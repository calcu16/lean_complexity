import HMem.Memory
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic

def Sum.reduce: α ⊕ α → α
| Sum.inl a => a
| Sum.inr a => a


@[simp] def List.append_eq_right {α: Type _} {x y: List α}: (x = y ++ x) ↔ ([] = y) :=
  ⟨ λ h ↦ (List.eq_nil_of_length_eq_zero
    (Nat.add_right_cancel (m := List.length x) (Nat.zero_add _ ▸ List.length_append _ _ ▸ congrArg List.length h)).symm).symm,
  λ h ↦ h ▸ rfl ⟩

@[simp] def List.cons_eq_append_inj {α: Type _} {a: α} {x z: List α}: (a :: x = z ++ x) ↔ ([a] = z) :=
  ⟨ λ h ↦ (List.append_left_inj _).mp h, λ h ↦ h ▸ rfl ⟩

@[simp] def List.cons_append_inj {α: Type _} {a: α} {x y z: List α}: (a :: (y ++ x) = z ++ x) ↔ (a :: y = z) := by
  simp [-List.cons_append, (List.cons_append _ _ _).symm]

@[simp] def List.cons₂_append_inj {α: Type _} {a b: α} {x y z: List α}: (a :: b :: (y ++ x) = z ++ x) ↔ (a :: b :: y = z) := by
  simp [-List.cons_append, (List.cons_append _ _ _).symm]

namespace HMem

namespace OpInstruction
inductive MemoryOperation
| COPY
| MOVE
| SWAP
end OpInstruction

@[simp] def Memory.mop (m: Memory): OpInstruction.MemoryOperation → Source → Source → Memory
| .COPY, _, src => m.getms src
| .MOVE, _, _ => 0
| .SWAP, dst, _ => m.getms dst

inductive OpInstruction
| vop {N: ℕ} (op: (Fin N → Bool) → Bool) (dst: Source) (src: Fin N → Source)
| mop (op: OpInstruction.MemoryOperation) (dst src: Source)
| const (dst: Source) (val: Memory)

@[simp] def OpInstruction.apply: OpInstruction → Memory → Memory
| vop op dst src, m => m.setvs dst (op (m.getvs ∘ src))
| mop op dst src, m => (m.setms src (m.mop op dst src)).setms dst (m.getms src)
| const dst val, m => m.setms dst val

inductive BranchInstruction
| ifTrue {N: ℕ} (cond: (Fin N → Bool) → Bool) (src: Fin N → Source)
| ifNull (src: Source)

def BranchInstruction.apply: BranchInstruction → Memory → Bool
| ifTrue cond src, m => (cond (m.getvs ∘ src))
| ifNull src, m => m.getms src = 0

@[simp] def BranchInstruction.apply_ifTrue_def: (ifTrue c src).apply m = (c (m.getvs ∘ src)) := rfl
@[simp] def BranchInstruction.apply_ifNull_def: (ifNull src).apply m = decide (m.getms src = 0) := rfl

inductive Program
| exit
| op (inst: OpInstruction) (next: Program)
| branch (inst: BranchInstruction) (pos: Program) (neg: Program)
| subroutine (dst src: Source) (func: Program) (next: Program)
| recurse (dst src: Source) (next: Program)

namespace Program
@[simp] def build: List (Program → Program) → Program
| [] => .exit
| p::ps => p (build ps)

@[match_pattern] def call (dst src: Source): Option Program → Program → Program
| some func, next => subroutine dst src func next
| none, next => recurse dst src next

@[simp] def setv (dst: Source) (b: Bool): Program → Program := op (.vop (λ _ ↦ b) dst finZeroElim)
@[simp] def setm (dst: Source) (src: Memory): Program → Program := op (.const dst src)
@[simp] def copyv (dst src: Source): Program → Program := op (.vop (λ f ↦ f 0) dst (λ (_: Fin 1) ↦ src))
@[simp] def copy (dst src: Source): Program → Program := op (.mop .COPY dst src)
@[simp] def move (dst src: Source): Program → Program := op (.mop .MOVE dst src)
@[simp] def swap (dst src: Source): Program → Program := op (.mop .SWAP dst src)
@[simp] def ifv (src: Source): List (Program → Program) → Program → Program := branch (.ifTrue (λ f ↦ f 0) (λ (_: Fin 1) ↦ src)) ∘ build

def subroutine_def: subroutine dst src func next = call dst src (some func) next := rfl
def recurse_def: recurse dst src next = call dst src none next := rfl

end Program

structure Thunk where
  state: Memory
  current: Program
  function: Program

namespace Thunk

theorem congr {s₀ s₁: Memory} {c₀ c₁ f₀ f₁: Program}
    (hs: s₀ = s₁) (hc: c₀ = c₁) (hf: f₀ = f₁):
  Thunk.mk s₀ c₀ f₀ = ⟨s₁, c₁, f₁⟩ := hs ▸ hc ▸ hf ▸ rfl

def setResult: Thunk → List Bool → Memory → Thunk
| ⟨m, is, p⟩, as, m' => ⟨m.setmp as m', is, p⟩

end Thunk

inductive Stack
| result (value: Memory)
| execution (top: Thunk) (callers: List (Thunk × List Bool))

namespace Stack
def step: Stack → Stack
| execution ⟨m, .op f next, p⟩ caller => execution ⟨f.apply m, next, p⟩ caller
| execution ⟨m, .branch f pos neg, p⟩ caller => execution ⟨m, ite (f.apply m) pos neg, p⟩ caller
| execution ⟨m, .recurse dst src next, p⟩ caller => execution ⟨m.getms src, p, p⟩ ((⟨m, next, p⟩, dst.get m)::caller)
| execution ⟨m, .subroutine dst src func next, p⟩ caller => execution ⟨m.getms src, func, func⟩ ((⟨m, next, p⟩, dst.get m)::caller)
| execution ⟨m, .exit, _⟩ (c::cs) => execution (c.fst.setResult c.snd m) cs
| execution ⟨m, .exit, _⟩ [] => result m
| result m => result m

theorem step_result: step (result m) = result m := rfl
theorem istep_result: step^[n] (result m) = result m := Function.iterate_fixed step_result _
theorem istep_result_le (hle: n₀ ≤ n₁) (hr: step^[n₀] s = result m): step^[n₁] s = result m :=
  Nat.sub_add_cancel hle ▸ Function.iterate_add_apply _ _ _ _ ▸ hr.symm ▸ istep_result
theorem istep_result_inj (h₀: step^[n₀] s = result m₀) (h₁: step^[n₁] s = result m₁): m₀ = m₁ :=
  result.inj ((le_total n₀ n₁).elim
    (λ h ↦ istep_result_le h h₀ ▸ h₁)
    λ h ↦ h₀ ▸ istep_result_le h h₁)
theorem stack_length_lt_istep_result: {n: ℕ} → {t: Thunk} → {cs: List _} →
  step^[n] (execution t cs) = result m → cs.length < n
| 0, _, _, h => absurd h Stack.noConfusion
| _+1, ⟨_, .op _ _, _⟩, _, h => Nat.lt_succ_of_lt (stack_length_lt_istep_result h)
| _+1, ⟨_, .branch _ _ _, _⟩, _, h => Nat.lt_succ_of_lt (stack_length_lt_istep_result h)
| _+1, ⟨_, .subroutine _ _ _ _, _⟩, _, h =>
  Nat.lt_of_succ_lt_succ (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt
    (List.length_cons  _ _ ▸ stack_length_lt_istep_result h)))
| _+1, ⟨_, .recurse _ _ _, _⟩, _, h =>
  Nat.lt_of_succ_lt_succ (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt
    (List.length_cons  _ _ ▸ stack_length_lt_istep_result h)))
| _+1, ⟨_, .exit, _⟩, [], _ => Nat.zero_lt_succ _
| n+1, ⟨_, .exit, _⟩, _::_, h => Nat.succ_lt_succ (stack_length_lt_istep_result (n := n) h)
theorem of_istep_result_le_stack_length (h: n ≤ cs.length): ∃ t' cs', step^[n] (execution t cs) = execution t' cs' :=
  match hstep:step^[n] (execution t cs) with
  | result _ => absurd (stack_length_lt_istep_result hstep) (not_lt_of_le h)
  | execution _ _ => ⟨_, _, rfl⟩


theorem istep_lt_result (he: step^[n₀] s = execution t cs) (hr: step^[n₁] s = result m): n₀ < n₁ :=
  lt_of_not_le λ h ↦ Stack.noConfusion (istep_result_le h hr ▸ he)
theorem istep_lt_result' (he: step^[n₀] s = execution t cs): step^[n₁] s = result m → cs.length + n₀ < n₁ :=
  (of_istep_result_le_stack_length (le_refl _)).elim λ _ hstep ↦ hstep.elim λ _ ↦
    istep_lt_result ∘
    ((Function.iterate_add_apply _ _ _ _).symm ▸ congrArg step^[cs.length] he).trans

theorem step_call: {func: Option Program} →
  step (execution ⟨m, .call dst src func next, p⟩ cs) =
    execution ⟨m.getms src, func.getD p, func.getD p⟩ ((⟨m, next, p⟩, dst.get m)::cs)
| some _ => rfl
| none => rfl

theorem istep_succ_call:
  step^[n+1] (execution ⟨m, .call dst src func next, p⟩ cs) =
    step^[n] (execution ⟨m.getms src, func.getD p, func.getD p⟩ ((⟨m, next, p⟩, dst.get m)::cs)) :=
  congrArg (step^[n]) step_call

theorem step_exit_nil: step (execution ⟨m, .exit, p⟩ []) = result m := rfl
theorem step_exit_cons: step (execution ⟨m, .exit, p⟩ []) = result m := rfl

section
attribute [local simp] step

theorem exit_of_step_result: step (execution ⟨m, is, p⟩ cs) = result r → m = r ∧ is = .exit ∧ cs = [] :=
by cases is <;> cases cs <;> simp

theorem exit_of_step_result': {t: Thunk} → step (execution t cs) = result r → execution t cs = execution ⟨r, .exit, t.function⟩ []
| ⟨_, _, _⟩, h => by simp [exit_of_step_result h]

theorem istep_exit_exists_of_result: {n₀: ℕ} → {t₀: Thunk} → {cs: List (Thunk × List Bool)} →
    step^[n₀] (.execution t₀ cs) = result m →
    ∃ (n₁: ℕ) (p: Program), step^[n₁] (.execution t₀ cs) = .execution ⟨m, .exit, p⟩ []
| 0, _, _, h => absurd h Stack.noConfusion
| n+1, t₀, cs, h =>
  match h':step^[n] (execution t₀ cs) with
  | result _ => Exists₂.imp (λ _ _ ↦ istep_result_inj h h' ▸ id) (istep_exit_exists_of_result h')
  | execution t _ => ⟨n, t.function,
    h' ▸ exit_of_step_result'
      (h' ▸ Function.iterate_succ_apply' step _ _ ▸ h)⟩

theorem istep_exit_exists_of_result' (h: step^[n₀] (.execution t₀ cs) = result m):
    ∃ (v : ℕ × Program), step^[v.fst] (.execution t₀ cs) = .execution ⟨m, .exit, v.snd⟩ [] :=
  (istep_exit_exists_of_result h).elim λ _ h ↦ h.elim λ _ h ↦ ⟨(_, _), h⟩

theorem step_eq_execution: step s = .execution t cs → ∃ t' cs', s = .execution t' cs' := by
  cases s <;> simp

theorem istep_eq_execution: (n: ℕ) → {s: Stack} → {t: Thunk} → {cs: List (Thunk × List Bool)} → step^[n] s = .execution t cs → ∃ t' cs', s = .execution t' cs'
| 0, _, _, _, h => ⟨_, _, h⟩
| n+1,  _, _, _, h => (istep_eq_execution n h).elim λ_ h ↦  h.elim λ _ ↦ step_eq_execution

theorem step_execution_append: step (.execution t₀ cs₀) = .execution t₁ cs₁ →
    step (.execution t₀ (cs₀ ++ cs)) = .execution t₁ (cs₁ ++ cs) := by
  cases t₀ with | _ m c p => cases c <;> cases cs₀ <;> simp [List.append_left_inj]

theorem istep_execution_append: {n: ℕ} → {t₀ t₁: Thunk} → {cs₀ cs₁: List (Thunk × List Bool)} →
    step^[n] (.execution t₀ cs₀) = .execution t₁ cs₁ →
    step^[n] (.execution t₀ (cs₀ ++ cs)) = .execution t₁ (cs₁ ++ cs)
| 0, _, _, _, _ => by simp
| n+1, _, _, _, _ =>
  λ h ↦ (istep_eq_execution n h).elim λ t hstep ↦ hstep.elim λ cs h' ↦
    (congrArg (step^[n]) (step_execution_append h')).trans
    (istep_execution_append ((congrArg (step^[n]) h').symm.trans h))
end

theorem istep_execution_stack_invariant: {n: ℕ} → {t₀ t₁: Thunk}  →
    step^[n] (.execution t₀ []) = .execution t₁ [] →
    step^[n] (.execution t₀ cs) = .execution t₁ cs := istep_execution_append

theorem istep_call_exit
    (h: step^[n] (.execution ⟨Memory.getms m src, func.getD p, func.getD p⟩ []) = .execution ⟨r, .exit, p'⟩ []):
    step^[n + 2] (.execution ⟨m, .call dst src func is, p⟩ cs) = .execution ⟨m.setms dst r, is, p⟩ cs :=
  Function.iterate_succ_apply' _ _ _ ▸
  istep_succ_call ▸
  istep_execution_stack_invariant h ▸
  rfl

theorem istep_recurse_exit
    (h: step^[n] (.execution ⟨Memory.getms m src, p, p⟩ []) = .execution ⟨r, .exit, p'⟩ []):
    step^[n + 2] (.execution ⟨m, .recurse dst src is, p⟩ cs) = .execution ⟨m.setms dst r, is, p⟩ cs :=
  Program.recurse_def ▸
  istep_call_exit (func := none) (Option.getD_none (a := p) ▸ h)

theorem istep_subroutine_exit
    (h: step^[n] (.execution ⟨Memory.getms m src, func, func⟩ []) = .execution ⟨r, .exit, p'⟩ []):
    step^[n + 2] (.execution ⟨m, .subroutine dst src func is, p⟩ cs) = .execution ⟨m.setms dst r, is, p⟩ cs :=
  Program.subroutine_def ▸
  istep_call_exit (func := some func) ((Option.getD_some (a := func)).symm ▸ h)

theorem istep_call_result
    (h₀: step^[n₀] (.execution ⟨Memory.getms m src, func.getD p, func.getD p⟩ []) = .result r₀)
    (h₁: step^[n₁] (.execution ⟨m.setms dst r₀, is, p⟩ cs) = .result r₁):
    step^[n₁ + n₀ + 1] (.execution ⟨m, .call dst src func is, p⟩ cs) = .result r₁ :=
  (istep_exit_exists_of_result' h₁).elim ((istep_exit_exists_of_result' h₀).elim λ _ h₀' _ h₁' ↦
    istep_succ_call ▸
    istep_result_le (Nat.add_le_add (istep_lt_result h₁' h₁) (istep_lt_result h₀' h₀))
    (Function.iterate_add_apply _ _ _ _ ▸
      Function.iterate_succ_apply' _ _ _ ▸
      Function.iterate_succ_apply' _ _ _ ▸
      istep_execution_stack_invariant h₀' (cs := (⟨m, is, p⟩, dst.get m)::cs) ▸
      congrArg step h₁'))

theorem istep_recurse_result
    (h₀: step^[n₀] (.execution ⟨Memory.getms m src, p, p⟩ []) = .result r₀)
    (h₁: step^[n₁] (.execution ⟨m.setms dst r₀, is, p⟩ cs) = .result r₁):
    step^[n₁ + n₀ + 1] (.execution ⟨m, .recurse dst src is, p⟩ cs) = .result r₁ :=
  Program.recurse_def ▸ istep_call_result (func := none) h₀ h₁

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

theorem istep_of_call: {n: ℕ} →
  step^[n] (execution ⟨m, .call dst src func is, p⟩ cs) = result r₀ →
  ∃ r₁, step^[n] (execution ⟨m.getms src, func.getD p, func.getD p⟩ []) = result r₁
| 0, h => absurd h Stack.noConfusion
| _+1, h => istep_of_result (r₀ := r₀) (cs₁ := (⟨m, is, p⟩, dst.get m)::cs)
  (Function.iterate_succ_apply' _ _ _ ▸ congrArg step (istep_succ_call.symm.trans h))

theorem istep_of_recurse
    (h: step^[n] (execution ⟨m, .recurse dst src is, p⟩ cs) = result r₀):
    ∃ r₁, step^[n] (execution ⟨m.getms src, p, p⟩ []) = result r₁ :=
  (istep_of_call (Program.recurse_def ▸ h)).imp (λ _ ↦ id)

theorem istep_of_subroutine
    (h: step^[n] (execution ⟨m, .subroutine dst src func is, p⟩ cs) = result r₀):
    ∃ r₁, step^[n] (execution ⟨m.getms src, func, func⟩ []) = result r₁ :=
  (istep_of_call (Program.subroutine_def ▸ h)).imp (λ _ ↦ id)

def hasResult (s: Stack) (m: Memory): Prop := ∃ n, Stack.step^[n] s = result m

theorem hasResult_inj (h₀: hasResult s m₀) (h₁: hasResult s m₁): m₀ = m₁ :=
  h₀.elim (h₁.elim λ _ hn _ hm ↦ istep_result_inj hm hn)

theorem hasResult_step (h: hasResult s r): hasResult (step s) r :=
  h.elim λ
  | 0, h => ⟨0, congr_arg step h⟩
  | _+1, h => ⟨_, h⟩

theorem hasResult_istep: {n: ℕ} → hasResult s r → hasResult (step^[n] s) r
| 0, h => h
| _+1, h =>
  Function.iterate_succ_apply' _ _ _ ▸
  hasResult_step ( hasResult_istep h)

theorem hasResult_istep'
    (h: hasResult s₀ r)
    (heq: step^[n] s₀ = s₁):
    hasResult s₁ r := heq ▸ hasResult_istep h

theorem hasResult_of_step (h: hasResult (step s) r): hasResult s r := h.elim λ _ h ↦ ⟨_ + 1, h⟩

theorem hasResult_call
    (h₀: hasResult (execution ⟨m.getms src, func.getD p, func.getD p⟩ []) r₀)
    (h₁: hasResult (execution ⟨m.setms dst r₀, is, p⟩ cs) r₁):
    hasResult (execution ⟨m, .call dst src func is, p⟩ cs) r₁ :=
  h₀.elim λ _ h₀ ↦ h₁.elim λ _ h₁ ↦ ⟨ _, istep_call_result h₀ h₁ ⟩

theorem hasResult_recurse
    (h₀: hasResult (execution ⟨m.getms src, p, p⟩ []) r₀)
    (h₁: hasResult (execution ⟨m.setms dst r₀, is, p⟩ cs) r₁):
    hasResult (execution ⟨m, .recurse dst src is, p⟩ cs) r₁ :=
  hasResult_call (func := none) h₀ h₁

theorem hasResult_subroutine
    (h₀: hasResult (execution ⟨m.getms src, func, func⟩ []) r₀)
    (h₁: hasResult (execution ⟨m.setms dst r₀, is, p⟩ cs) r₁):
    hasResult (execution ⟨m, .subroutine dst src func is, p⟩ cs) r₁ :=
  hasResult_call (func := some func) h₀ h₁

theorem hasResult_of_call
    (h₀: hasResult (execution ⟨m, .call dst src func is, p⟩ cs) r₀)
    (h₁: hasResult (execution ⟨m.getms src, func.getD p, func.getD p⟩ []) r₁):
    hasResult (execution ⟨m.setms dst r₁, is, p⟩ cs) r₀ :=
  h₁.elim λ _ h₁ ↦ (istep_exit_exists_of_result' h₁).elim
    λ _ h₁ ↦  hasResult_istep' h₀ (istep_call_exit h₁)

theorem hasResult_of_recurse
    (h₀: hasResult (execution ⟨m, .recurse dst src is, p⟩ cs) r₀)
    (h₁: hasResult (execution ⟨m.getms src, p, p⟩ []) r₁):
    hasResult (execution ⟨m.setms dst r₁, is, p⟩ cs) r₀ :=
  hasResult_of_call (Program.recurse_def ▸ h₀) h₁

theorem hasResult_of_subroutine
    (h₀: hasResult (execution ⟨m, .subroutine dst src func is, p⟩ cs) r₀)
    (h₁: hasResult (execution ⟨m.getms src, func, func⟩ []) r₁):
    hasResult (execution ⟨m.setms dst r₁, is, p⟩ cs) r₀ :=
  hasResult_of_call (Program.subroutine_def ▸ h₀) h₁

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

@[simp] theorem hasResult_nil: hasResult (.execution ⟨m, .exit, p⟩ []) = Eq m := hasResult_execution ▸ hasResult_result

@[simp] theorem hasResult_op:
    hasResult (.execution ⟨m, .op op is, p⟩ cs) =
    hasResult (.execution ⟨op.apply m, is, p⟩ cs) :=
  hasResult_execution

@[simp] theorem hasResult_branch:
    hasResult (.execution ⟨m, .branch c pos neg, p⟩ cs) =
    hasResult (.execution ⟨m, ite (c.apply m) pos neg, p⟩ cs) :=
  hasResult_execution

theorem hasResult_branch_pos (h: c.apply m):
    hasResult (.execution ⟨m, .branch c pos neg, p⟩ cs) =
    hasResult (.execution ⟨m, pos, p⟩ cs) := by simp [h]


theorem hasResult_branch_neg (h: c.apply m = false):
    hasResult (.execution ⟨m, .branch c pos neg, p⟩ cs) =
    hasResult (.execution ⟨m, neg, p⟩ cs) := by simp [h]

def halts (s: Stack): Prop := ∃ (v: ℕ × Memory), step^[v.fst] s = result v.snd


def getResult: Stack → Memory
| result m => m
| _ => 0

end Stack

namespace Program

def haltsOn (p: Program) (inp: Memory): Prop := Stack.halts (.execution ⟨inp, p, p⟩ [])

def hasResult (p: Program) (inp: Memory) (outp: Memory): Prop := Stack.hasResult (.execution ⟨inp, p, p⟩ []) outp

@[simp] theorem hasResult_def: hasResult p inp = Stack.hasResult (.execution ⟨inp, p, p⟩ []) := rfl

theorem hasResult_injOut {p: Program} {inp: Memory} {o₀ o₁: Memory}:
  p.hasResult inp o₀ → p.hasResult inp o₁ → o₀ = o₁ := Stack.hasResult_inj

instance (s: Stack) (n: ℕ): Decidable (∃ outp, Stack.step^[n] s = .result outp) :=
  match Stack.step^[n] s with
  | .execution _ _ => Decidable.isFalse (not_exists_of_forall_not λ _ ↦ Stack.noConfusion)
  | .result _ => Decidable.isTrue ⟨_, rfl⟩
end Program
end HMem
