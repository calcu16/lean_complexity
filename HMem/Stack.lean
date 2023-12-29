import HMem.Memory
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Basic

namespace HMem

namespace Instruction
inductive MemoryOperation
| COPY
| MOVE
| SWAP
end Instruction

def Memory.mop (m: Memory): Instruction.MemoryOperation → Source → Source → Memory
| .COPY, dst, _ => m.getms dst
| .MOVE, _, _ => 0
| .SWAP, _, src => m.getms src

inductive Instruction
| vop {N: ℕ} (op: (Fin N → Bool) → Bool) (dst: Source) (src: Fin N → Source)
| mop (op: Instruction.MemoryOperation) (dst src: Source)
| clear (dst: Source)
| branch {N: ℕ} (cond: (Fin N → Bool) → Bool) (src: Fin N → Source) (branch: List Instruction)
| call (dst src: Source) (func: List Instruction)
| recurse (dst src: Source)

instance: Inhabited Instruction where
  default := Instruction.mop Instruction.MemoryOperation.COPY Source.nil Source.nil

def Program: Type _ := List Instruction

namespace Instruction

inductive Step
| op (value: Memory)
| branch (cond: Option (Program))
| call (func: Option (Program)) (dst: List Bool) (arg: Memory)

def step: Instruction → Memory → Step
| .vop op dst src, m => .op (m.setvs dst (op (m.getvs ∘ src)))
| .mop op dst src, m => .op ((m.setms src (m.mop op src dst)).setms dst (m.getms src))
| .clear dst, m => .op (m.setms dst 0)
| .branch cond src is, m => .branch (ite (cond (m.getvs ∘ src)) (some is) none)
| .call dst src func, m => .call (some func) (dst.get m) (m.getms src)
| .recurse dst src, m => .call none (dst.get m) (m.getms src)

end Instruction

structure Thunk where
  state: Memory
  current: List Instruction
  function: Program

namespace Thunk

theorem congr {s₀ s₁: Memory} {c₀ c₁ f₀ f₁: Program}
    (hs: s₀ = s₁) (hc: c₀ = c₁) (hf: f₀ = f₁):
  Thunk.mk s₀ c₀ f₀ = ⟨s₁, c₁, f₁⟩ := hs ▸ hc ▸ hf ▸ rfl

def set_result: Thunk → List Bool → Memory → Thunk
| ⟨m, is, p⟩, as, m' => ⟨m.setmp as m', is, p⟩

end Thunk

def Program.call (p: Program) (m: Memory): Thunk := ⟨m, p, p⟩

inductive Stack
| result (value: Memory)
| execution (top: Thunk) (callers: List (Thunk × List Bool))

namespace Stack
def step: Stack → Stack
| execution ⟨m, i::is, p⟩ caller => match i.step m with
  | .op m' => execution ⟨m', is, p⟩ caller
  | .branch is' => execution ⟨m, is'.getD is, p⟩ caller
  | .call func dst arg =>
    execution ((func.getD p).call arg) ((⟨m.setmp dst 0, is, p⟩, dst)::caller)
| execution ⟨m, [], _⟩ (c::cs) => execution (c.fst.set_result c.snd m) cs
| execution ⟨m, [], _⟩ [] => result m
| result m => result m

theorem step_result: step (result m) = result m := rfl
theorem istep_result: step^[n] (result m) = result m := Function.iterate_fixed step_result _
theorem istep_result_le (hle: n₀ ≤ n₁) (hr: step^[n₀] thunk = result m): step^[n₁] thunk = result m :=
  Nat.sub_add_cancel hle ▸ Function.iterate_add_apply _ _ _ _ ▸ hr.symm ▸ istep_result
theorem return_of_step_result: step (execution ⟨m, is, p⟩ cs) = result r → m = r ∧ is = [] ∧ cs = [] := by
  cases is
  { cases cs <;> simp [step, Instruction.step] }
  case cons i is => cases i <;> simp [step, Instruction.step]

theorem return_of_step_result': {t: Thunk} → step (execution t cs) = result r → execution t cs = execution ⟨r, [], t.function⟩ []
| ⟨_, _, _⟩, h => congrArg₂ _
  (Thunk.congr
    (return_of_step_result h).left
    (return_of_step_result h).right.left
    rfl)
  (return_of_step_result h).right.right

theorem istep_return_exists_of_result: {n₀: ℕ} → {t₀: Thunk} → {cs: List (Thunk × List Bool)} →
    step^[n₀] (.execution t₀ cs) = result m →
    ∃ (n₁: ℕ) (p: Program) (_: n₁ < n₀),
      step^[n₁] (.execution t₀ cs) = .execution ⟨m, [], p⟩ []
| 0, _, _, h => absurd h Stack.noConfusion
| _+1, t₀, cs, h =>
  match hstep:(execution t₀ cs).step with
  | result _ => ⟨0, t₀.function, Nat.zero_lt_succ _,
    return_of_step_result' (hstep.trans
    ((istep_result_le (thunk := execution t₀ cs) (Nat.succ_le_succ (Nat.zero_le _)) hstep).symm.trans
    h))⟩
  | execution _ _ =>
    (istep_return_exists_of_result (hstep ▸ Function.iterate_succ_apply _ _ _ ▸ h)).elim
    λ _ ih ↦ ih.elim λ _ ih ↦ ih.elim λ hlt ih ↦
    ⟨_, _, Nat.succ_lt_succ hlt, (congrArg (step^[_]) hstep).trans ih⟩

theorem step_eq_execution: step s = .execution t cs → ∃ t' cs', s = .execution t' cs' := by
  cases s <;> simp [step]

theorem istep_eq_execution: (n: ℕ) → {s: Stack} → {t: Thunk} → {cs: List (Thunk × List Bool)} → step^[n] s = .execution t cs → ∃ t' cs', s = .execution t' cs'
| 0, _, _, _, h => ⟨_, _, h⟩
| n+1,  _, _, _, h => (istep_eq_execution n h).elim λ_ h ↦  h.elim λ _ ↦ step_eq_execution

theorem step_execution_append: step (.execution t₀ cs₀) = .execution t₁ cs₁ →
    step (.execution t₀ (cs₀ ++ cs)) = .execution t₁ (cs₁ ++ cs) := by
  cases t₀ with | _ m c p =>
  cases c; { cases cs₀ <;> simp [step, Instruction.step] }
  case cons hd _ =>
    cases t₁
    cases hd
    case call|recurse => simpa [step, Instruction.step, and_assoc]
      using λ hm hcs ↦ ⟨ hm, congrArg₂ List.append hcs rfl ⟩
    all_goals simp [step, Instruction.step, and_assoc]

theorem istep_execution_append:
    step^[n] (.execution t₀ cs₀) = .execution t₁ cs₁ →
    step^[n] (.execution t₀ (cs₀ ++ cs)) = .execution t₁ (cs₁ ++ cs) := by
  induction n generalizing t₀ t₁ cs₀ cs₁; { simp }
  case succ n ih =>
    exact λ h ↦ (istep_eq_execution n h).elim λ t hstep ↦ hstep.elim λ cs h' ↦
      (congrArg (step^[n]) (step_execution_append h')).trans
      (ih ((congrArg (step^[n]) h').symm.trans h))

theorem istep_recurse_return
    (h: step^[n] (.execution ⟨Memory.getms m src, p, p⟩ []) = .execution ⟨r, [], p'⟩ []):
    step^[n + 2] (.execution ⟨m, .recurse dst src ::is, p⟩ cs) = .execution ⟨m.setms dst r, is, p⟩ cs :=
  Function.iterate_succ_apply' _ _ _ ▸
    (congrArg _ (istep_execution_append h)).trans
    (congrArg₂ execution (Thunk.congr Memory.setmp_setmp rfl rfl) rfl)

theorem istep_call_return
    (h: step^[n] (.execution ⟨Memory.getms m src, func, func⟩ []) = .execution ⟨r, [], p'⟩ []):
    step^[n + 2] (.execution ⟨m, .call dst src func::is, p⟩ cs) = .execution ⟨m.setms dst r, is, p⟩ cs :=
  Function.iterate_succ_apply' _ _ _ ▸
    (congrArg _ (istep_execution_append h)).trans
    (congrArg₂ execution (Thunk.congr Memory.setmp_setmp rfl rfl) rfl)

theorem istep_recurse_result
    (hi: step^[n₀] (.execution ⟨Memory.getms m src, p, p⟩ []) = .result r₀)
    (ho: step^[n₁] (.execution ⟨m.setms dst r₀, is, p⟩ cs) = .result r₁):
    step^[n₁ + n₀ + 1] (.execution ⟨m, .recurse dst src ::is, p⟩ cs) = .result r₁ :=
  (istep_return_exists_of_result hi).elim λ _ hi ↦ hi.elim λ _ hi ↦ hi.elim λ hlt hi ↦
    istep_result_le
      (Nat.le_trans (Nat.add_le_add (le_refl _) (Nat.succ_le_succ (Nat.succ_le_of_lt hlt))) (le_of_eq (Nat.add_succ _ _)))
      ((Function.iterate_add_apply _ _ _ _).symm ▸
        (congrArg (step^[n₁]) (istep_recurse_return hi)).trans
        ho)

theorem istep_call_result
    (hi: step^[n₀] (.execution ⟨Memory.getms m src, func, func⟩ []) = .result r₀)
    (ho: step^[n₁] (.execution ⟨m.setms dst r₀, is, p⟩ cs) = .result r₁):
    step^[n₁ + n₀ + 1] (.execution ⟨m, .call dst src func::is, p⟩ cs) = .result r₁ :=
  (istep_return_exists_of_result hi).elim λ _ hi ↦ hi.elim λ _ hi ↦ hi.elim λ hlt hi ↦
    istep_result_le
      (Nat.le_trans (Nat.add_le_add (le_refl _) (Nat.succ_le_succ (Nat.succ_le_of_lt hlt))) (le_of_eq (Nat.add_succ _ _)))
      ((Function.iterate_add_apply _ _ _ _).symm ▸
        (congrArg (step^[n₁]) (istep_call_return hi)).trans
        ho)

theorem istep_of_result:
  {n: ℕ} → {t: Thunk} → {cs₀: List (Thunk × List Bool)} →
  (step^[n] (execution t (cs₀ ++ cs₁)) = result r₀) →
    ∃ r₁, step^[n] (execution t cs₀) = result r₁
| 0, _, _, h => absurd h Stack.noConfusion
| _+1, t, cs₀, h =>
    match hstep:(execution t cs₀).step with
    | result _ => ⟨_, istep_result_le (Nat.succ_le_succ (Nat.zero_le _)) hstep⟩
    | execution _ _ => Exists.imp
        (λ _ h ↦ (congrArg _ hstep).trans h)
        (istep_of_result ((congrArg _ (step_execution_append hstep)).symm.trans h))

theorem istep_of_recurse: {n: ℕ} →
  step^[n] (execution ⟨m, .recurse dst src::is, p⟩ cs) = result r₀ →
  ∃ r₁, step^[n] (execution ⟨m.getms src, p, p⟩ []) = result r₁
| 0 => flip absurd Stack.noConfusion
| _+1 => istep_of_result ∘ ((Function.iterate_succ_apply' _ _ _).trans ∘ (congrArg step))

theorem istep_of_call: {n: ℕ} →
  step^[n] (execution ⟨m, .call dst src func::is, p⟩ cs) = result r₀ →
  ∃ r₁, step^[n] (execution ⟨m.getms src, func, func⟩ []) = result r₁
| 0 => flip absurd Stack.noConfusion
| _+1 => istep_of_result ∘ ((Function.iterate_succ_apply' _ _ _).trans ∘ (congrArg step))

def hasResult (s: Stack) (m: Memory): Prop := ∃ n, Stack.step^[n] s = result m

theorem hasResult_inj {s: Stack} {m₀ m₁: Memory}
    (h₀: s.hasResult m₀) (h₁: s.hasResult m₁): m₀ = m₁ :=
  Stack.result.inj (h₀.elim (h₁.elim λ _ hn _ hm ↦ ((Nat.le_total _ _).elim
    (λ hle ↦ hm.symm.trans (Stack.istep_result_le hle hn))
    λ hle ↦ (Stack.istep_result_le hle hm).symm.trans hn)))

theorem step_hasResult (h: hasResult s r): hasResult (step s) r :=
  h.elim λ
  | 0, h => ⟨0, congr_arg step h⟩
  | _+1, h => ⟨_, h⟩

theorem istep_hasResult: {n: ℕ} → {s: Stack} →
    (hasResult s r) →
    hasResult (step^[n] s) r
| 0, _ => id
| n+1, _ => istep_hasResult (n := n) ∘ step_hasResult

theorem istep_hasResult'
    (h: hasResult s₀ r)
    (heq: step^[n] s₀ = s₁):
    hasResult s₁ r := heq ▸ istep_hasResult h

theorem hasResult_recurse
    (h₀: hasResult (execution ⟨m.getms src, p, p⟩ []) r₀)
    (h₁: hasResult (execution ⟨m.setms dst r₀, is, p⟩ cs) r₁):
    hasResult (execution ⟨m, .recurse dst src::is, p⟩ cs) r₁ :=
  h₀.elim λ _ h₀ ↦ h₁.elim λ _ h₁ ↦
    ⟨ _, istep_recurse_result h₀ h₁ ⟩

theorem hasResult_of_recurse
    (h₀: hasResult (execution ⟨m, .recurse dst src::is, p⟩ cs) r₀)
    (h₁: hasResult (execution ⟨m.getms src, p, p⟩ []) r₁):
    hasResult (execution ⟨m.setms dst r₁, is, p⟩ cs) r₀ :=
  h₁.elim λ _ h₁ ↦ (istep_return_exists_of_result h₁).elim
    λ _ h₁ ↦ h₁.elim λ _ h₁ ↦ h₁.elim λ _ h₁ ↦
    istep_hasResult' h₀ (istep_recurse_return h₁)

theorem hasResult_of_call
    (h₀: hasResult (execution ⟨m, .call dst src func::is, p⟩ cs) r₀)
    (h₁: hasResult (execution ⟨m.getms src, func, func⟩ []) r₁):
    hasResult (execution ⟨m.setms dst r₁, is, p⟩ cs) r₀ :=
  h₁.elim λ _ h₁ ↦ (istep_return_exists_of_result h₁).elim
    λ _ h₁ ↦ h₁.elim λ _ h₁ ↦ h₁.elim λ _ h₁ ↦
    istep_hasResult' h₀ (istep_call_return h₁)

@[simp] theorem hasResult_result: hasResult (.result m) = Eq m :=
  funext λ _ ↦ eq_iff_iff.mpr ⟨
    λ h ↦ h.elim λ _ ↦ result.inj ∘ istep_result.symm.trans,
    λ h ↦ h ▸ ⟨0, rfl⟩ ⟩

theorem hasResult_execution: hasResult (.execution t cs) = hasResult (.step (.execution t cs)) :=
  funext λ _ ↦
    eq_iff_iff.mpr ⟨
        λ h ↦ h.elim λ
        | 0 => flip absurd Stack.noConfusion
        | _+1 => λ h ↦ ⟨_, h⟩,
        λ h ↦ h.elim λ _ h ↦ ⟨_+1, h⟩
      ⟩

@[simp] theorem hasResult_nil: hasResult (.execution ⟨m, [], p⟩ []) = Eq m := hasResult_execution ▸ hasResult_result

@[simp] theorem hasResult_vop:
    hasResult (.execution ⟨m, .vop op dst src::is, p⟩ cs) =
    hasResult (.execution ⟨m.setvs dst (op (m.getvs ∘ src)), is, p⟩ cs) :=
  hasResult_execution

@[simp] theorem hasResult_mop:
    hasResult (.execution ⟨m, .mop op dst src::is, p⟩ cs) =
    hasResult (.execution ⟨(m.setms src (m.mop op src dst)).setms dst (m.getms src), is, p⟩ cs) :=
  hasResult_execution

@[simp] theorem hasResult_clear:
    hasResult (.execution ⟨m, .clear dst::is, p⟩ cs) =
    hasResult (.execution ⟨m.setms dst 0, is, p⟩ cs) :=
  hasResult_execution

@[simp] theorem hasResult_ite:
    hasResult (.execution ⟨m, .branch c src is'::is, p⟩ cs) =
    hasResult (.execution ⟨m, ite (c (m.getvs ∘ src)) is' is, p⟩ cs) :=
  hasResult_execution.trans (congrArg _ (flip (congrArg₂ execution) rfl
    (match c (Memory.getvs m ∘ src) with
    | true => rfl
    | false => rfl)))

def getResult: Stack → Memory
| result m => m
| _ => 0

end Stack

namespace Program

def haltsOn (p: Program) (inp: Memory): Prop :=
  ∃ n outp, Stack.step^[n] (.execution (p.call inp) []) = .result outp

def hasTimeCost (p: Program) (inp: Memory) (n: ℕ): Prop :=
  ∃ outp, Stack.step^[n] (.execution (p.call inp) []) = .result outp

def hasResult (p: Program) (inp: Memory) (outp: Memory): Prop :=
  ∃ n, Stack.step^[n] (.execution (p.call inp) []) = .result outp

@[simp] theorem hasResult_def: hasResult p inp = Stack.hasResult (.execution ⟨inp, p, p⟩ []) := rfl

theorem hasResult_injOut {p: Program} {inp: Memory} {o₀ o₁: Memory}:
  p.hasResult inp o₀ → p.hasResult inp o₁ → o₀ = o₁ := Stack.hasResult_inj

theorem haltsOnOfCost (p: Program) (inp: Memory) (n: ℕ) (h: p.hasTimeCost inp n):
   p.haltsOn inp := ⟨ n, h ⟩

instance (s: Stack) (n: ℕ): Decidable (∃ outp, Stack.step^[n] s = .result outp) :=
  match Stack.step^[n] s with
  | .execution _ _ => Decidable.isFalse (not_exists_of_forall_not λ _ ↦ Stack.noConfusion)
  | .result _ => Decidable.isTrue ⟨_, rfl⟩

def timeCost (p: Program) {inp: Memory} (h: p.haltsOn inp): ℕ := Nat.find h

def result {p: Program} {inp: Memory} (h: p.haltsOn inp): Memory :=
  (Stack.step^[p.timeCost h] (.execution (p.call inp) [])).getResult

theorem result_sound {p: Program} {inp: Memory} (h: p.haltsOn inp): p.hasResult inp (result h) :=
  ⟨_, (Nat.find_spec h).elim λ _ h ↦
    h.trans (congrArg Stack.result (Eq.symm (congrArg _ h)))⟩

@[simp] theorem hasResult_call:
    Stack.hasResult (.execution ⟨m, .call dst src func::is, p⟩ cs) outp =
    ∃ (h: Program.haltsOn func (m.getms src)), Stack.hasResult (.execution ⟨Memory.setms m dst (result h), is, p⟩ cs) outp :=
  eq_iff_iff.mpr ⟨
    λ h₀ ↦ ⟨(h₀.imp λ _ ↦ Stack.istep_of_call),
    Stack.hasResult_of_call h₀ ((h₀.imp λ _ ↦ Stack.istep_of_call).elim λ _ h₁ ↦ h₁.elim λ _ h₁ ↦
      Stack.hasResult_inj ⟨_, h₁⟩ (result_sound ⟨_, _, h₁⟩) ▸ ⟨_, h₁⟩)⟩,
  λ h ↦ h.elim λ h₁ h₀ ↦ h₁.elim λ_ h₁ ↦ h₁.elim λ _ h₁ ↦ h₀.elim λ n₀ h₀ ↦
    ⟨n₀ + _ + 1, Stack.istep_call_result h₁ ((Stack.hasResult_inj ⟨_, h₁⟩ (result_sound _)) ▸ h₀)⟩⟩

@[simp] theorem hasResult_recurse:
    Stack.hasResult (.execution ⟨m, .recurse dst src::is, p⟩ cs) outp =
    ∃ (h: p.haltsOn (m.getms src)), Stack.hasResult (.execution ⟨Memory.setms m dst (result h), is, p⟩ cs) outp :=
  eq_iff_iff.mpr ⟨
    λ h₀ ↦ ⟨(h₀.imp λ _ ↦ Stack.istep_of_recurse),
    Stack.hasResult_of_recurse h₀ ((h₀.imp λ _ ↦ Stack.istep_of_recurse).elim λ _ h₁ ↦ h₁.elim λ _ h₁ ↦
      Stack.hasResult_inj ⟨_, h₁⟩ (result_sound ⟨_, _, h₁⟩) ▸ ⟨_, h₁⟩)⟩,
  λ h ↦ h.elim λ h₁ h₀ ↦ h₁.elim λ_ h₁ ↦ h₁.elim λ _ h₁ ↦ h₀.elim λ n₀ h₀ ↦
    ⟨n₀ + _ + 1, Stack.istep_recurse_result h₁ ((Stack.hasResult_inj ⟨_, h₁⟩ (result_sound _)) ▸ h₀)⟩⟩

@[simp] theorem result_hasResult:
    (∃ (h: Program.haltsOn p inp), Program.result h = outp) = Program.hasResult p inp outp :=
  eq_iff_iff.mpr ⟨
    flip Exists.elim λ _ heq ↦ heq ▸ result_sound _,
    flip Exists.elim λ _ h ↦ ⟨⟨_, _, h⟩, hasResult_injOut (result_sound _) ⟨_, h⟩⟩⟩

end Program
end HMem
