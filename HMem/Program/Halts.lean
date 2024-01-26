import HMem.Program.Step


namespace HMem
namespace Stack
def halts (s: Stack): Prop := ∃ (v: ℕ × Memory), step^[v.fst] s = result v.snd
def hasResult (s: Stack) (m: Memory): Prop := ∃ n, Stack.step^[n] s = result m
def hasTimeCost (s: Stack) (n: ℕ): Prop := ∃ (m: Memory), step^[n] s = result m

def halts₂ (s: Stack): Prop := ∃ (n: ℕ) (m: Memory), step^[n] s = result m
theorem halts_iff_halts₂: halts s ↔ halts₂ s :=
  ⟨ λ h ↦ h.elim λ _ h ↦ ⟨_, _, h⟩,
    λ h ↦ h.elim λ _ h ↦ h.elim λ _ h ↦ ⟨(_, _), h⟩⟩

instance (s: Stack) (n: ℕ): Decidable (∃ outp, Stack.step^[n] s = .result outp) :=
  match Stack.step^[n] s with
  | .execution _ _ => Decidable.isFalse (not_exists_of_forall_not λ _ ↦ Stack.noConfusion)
  | .result _ => Decidable.isTrue ⟨_, rfl⟩

def timeCost (s: Stack) (h: s.halts): ℕ := Nat.find (halts_iff_halts₂.mp h)

def resultOf (s: Stack) (h: s.halts): Memory := getResult (step^[s.timeCost h] s)


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
    hasResult (.execution ⟨m, .branch c next, p⟩ cs) =
    hasResult (.execution ⟨m, next (c.apply m), p⟩ cs) :=
  hasResult_execution


theorem hasTimeCost_le (hle: n₀ ≤ n₁): hasTimeCost s n₀ → hasTimeCost s n₁ :=
  Exists.imp λ _ ↦ istep_result_le hle

theorem hasResult_hasTimeCost (hr: hasResult s r) (ht: hasTimeCost s n):
    step^[n] s = result r :=
  hr.elim (ht.elim λ _ hm _ hn ↦ istep_result_inj hn hm ▸ hm)

theorem hasTimeCost_step: {n: ℕ} → hasTimeCost s n → hasTimeCost (step s) (n - 1)
| 0 => Exists.imp λ _ ↦ congrArg step
| _+1 => id

theorem hasTimeCost_of_step: hasTimeCost (step s) n → hasTimeCost s (n + 1) := id

theorem hasTimeCost_of_step_le_succ: n₀ + 1 ≤ n₁ → hasTimeCost (step s) n₀ → hasTimeCost s n₁ := hasTimeCost_le

theorem hasTimeCost_of_step_le_succ': s' = step s → n₀ + 1 ≤ n₁ → hasTimeCost s' n₀ → hasTimeCost s n₁ :=
  λ heq ↦ heq ▸ hasTimeCost_of_step_le_succ

theorem hasTimeCost_call
    (hr: hasResult (execution ⟨m.getms src, func.getD p, func.getD p⟩ []) r)
    (h₀: hasTimeCost (execution ⟨m.getms src, func.getD p, func.getD p⟩ []) n₀)
    (h₁: hasTimeCost (execution ⟨m.setms dst r, is, p⟩ cs) n₁):
    hasTimeCost (execution ⟨m, .call dst src func is, p⟩ cs) (n₁ + n₀ + 1) :=
  h₁.imp (λ _ ↦ istep_call_result (hasResult_hasTimeCost hr h₀))

theorem hasTimeCost_recurse
    (hr: hasResult (execution ⟨m.getms src, p, p⟩ []) r)
    (h₀: hasTimeCost (execution ⟨m.getms src, p, p⟩ []) n₀)
    (h₁: hasTimeCost (execution ⟨m.setms dst r, is, p⟩ cs) n₁):
    hasTimeCost (execution ⟨m, .recurse dst src is, p⟩ cs) (n₁ + n₀ + 1) :=
  h₁.imp (λ _ ↦ istep_recurse_result (hasResult_hasTimeCost hr h₀))

theorem hasTimeCost_recurse_le
    (hle: n₁ + n₀ + 1 ≤ n)
    (hr: hasResult (execution ⟨m.getms src, p, p⟩ []) r)
    (h₀: hasTimeCost (execution ⟨m.getms src, p, p⟩ []) n₀)
    (h₁: hasTimeCost (execution ⟨m.setms dst r, is, p⟩ cs) n₁):
    hasTimeCost (execution ⟨m, .recurse dst src is, p⟩ cs) n :=
  hasTimeCost_le hle (hasTimeCost_recurse hr h₀ h₁)

theorem hasTimeCost_subroutine
    (hr: hasResult (execution ⟨m.getms src, func, func⟩ []) r)
    (h₀: hasTimeCost (execution ⟨m.getms src, func, func⟩ []) n₀)
    (h₁: hasTimeCost (execution ⟨m.setms dst r, is, p⟩ cs) n₁):
    hasTimeCost (execution ⟨m, .subroutine dst src func is, p⟩ cs) (n₁ + n₀ + 1) :=
  h₁.imp (λ _ ↦ istep_subroutine_result (hasResult_hasTimeCost hr h₀))

theorem hasTimeCost_subroutine_le
    (hle: n₁ + n₀ + 1 ≤ n)
    (hr: hasResult (execution ⟨m.getms src, func, func⟩ []) r)
    (h₀: hasTimeCost (execution ⟨m.getms src, func, func⟩ []) n₀)
    (h₁: hasTimeCost (execution ⟨m.setms dst r, is, p⟩ cs) n₁):
    hasTimeCost (execution ⟨m, .subroutine dst src func is, p⟩ cs) n :=
  hasTimeCost_le hle (hasTimeCost_subroutine hr h₀ h₁)

theorem resultOf_timeCost_sound (s: Stack) (h: s.halts): step^[timeCost _ h] s = .result (resultOf _ h) :=
  (Nat.find_spec (halts_iff_halts₂.mp h)).elim λ _ h ↦
    h.trans (congrArg _ (congrArg getResult h.symm))

theorem timeCost_le_iff (s: Stack) (h: s.halts) {n: ℕ}: s.hasTimeCost n ↔ s.timeCost h ≤ n :=
  ⟨ λ hn ↦ Nat.find_min' _ hn,
    λ hn ↦ ⟨_, istep_result_le hn
      (s.resultOf_timeCost_sound h)⟩⟩

theorem resultOf_sound (s: Stack) (h: s.halts): s.hasResult (s.resultOf h) :=
  ⟨_, resultOf_timeCost_sound _ h⟩

theorem timeCost_sound (s: Stack) (h: s.halts): s.hasTimeCost (s.timeCost h) :=
  ⟨_, resultOf_timeCost_sound _ h⟩


def halts_step {s: Stack} (h: s.halts): s.step.halts :=
  h.elim λ
  | ⟨0, _⟩, h => ⟨(0, _), congr_arg step h⟩
  | ⟨_+1, _⟩, h => ⟨(_, _), h⟩

theorem halts_call (h: halts (execution ⟨m, .call dst src func is, p⟩ cs)):
    halts (execution ⟨m.getms src, func.getD p, func.getD p⟩ []) :=
  h.elim λ
  | ⟨_, _⟩, h => (istep_of_call h).elim λ r h ↦ ⟨(_, r), h⟩

theorem halts_subroutine (h: halts (execution ⟨m, .subroutine dst src func is, p⟩ cs)):
    halts (execution ⟨m.getms src, func, func⟩ []) := halts_call (Program.subroutine_def ▸ h)

theorem halts_recurse (h: halts (execution ⟨m, .recurse dst src is, p⟩ cs)):
    halts (execution ⟨m.getms src, p, p⟩ []) := halts_call (Program.recurse_def ▸ h)

theorem halts_call' (h: halts (execution ⟨m, .call dst src func is, p⟩ cs)):
    halts (execution ⟨m.setms dst (resultOf _ (halts_call h)), is, p⟩ cs) :=
  h.elim λ
  | ⟨_, _⟩, h' =>
    (hasResult_of_call ⟨_, h'⟩ (resultOf_sound _ (halts_call h))).elim
      λ _ h' ↦ ⟨(_, _), h'⟩

theorem halts_subroutine' (h: halts (execution ⟨m, .subroutine dst src func is, p⟩ cs)):
    halts (execution ⟨m.setms dst (resultOf _ (halts_subroutine h)), is, p⟩ cs) :=
  halts_call' (Program.subroutine_def ▸ h)

theorem halts_recurse' (h: halts (execution ⟨m, .recurse dst src is, p⟩ cs)):
    halts (execution ⟨m.setms dst (resultOf _ (halts_recurse h)), is, p⟩ cs) :=
  halts_call' (Program.recurse_def ▸ h)

end Stack

namespace Program

def haltsOn (p: Program) (inp: Memory): Prop := Stack.halts (.execution ⟨inp, p, p⟩ [])

def hasResult (p: Program) (inp: Memory) (outp: Memory): Prop := Stack.hasResult (.execution ⟨inp, p, p⟩ []) outp

def hasTimeCost (p: Program) (inp: Memory) (n: ℕ): Prop := Stack.hasTimeCost (.execution ⟨inp, p, p⟩ []) n

@[simp] theorem hasResult_def: hasResult p inp = Stack.hasResult (.execution ⟨inp, p, p⟩ []) := rfl

theorem hasResult_injOut {p: Program} {inp: Memory} {o₀ o₁: Memory}:
  p.hasResult inp o₀ → p.hasResult inp o₁ → o₀ = o₁ := Stack.hasResult_inj

def timeCost (p: Program) {inp: Memory} (h: p.haltsOn inp): ℕ := Stack.timeCost _ h

def result (p: Program) {inp: Memory} (h: p.haltsOn inp): Memory := Stack.resultOf _ h

end HMem.Program
