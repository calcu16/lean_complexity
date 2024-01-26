import HMem.Program.Defs

namespace HMem

@[simp] def Memory.mop (m: Memory): OpInstruction.MemoryOperation → Source → Source → Memory
| .COPY, _, src => m.getms src
| .MOVE, _, _ => 0
| .SWAP, dst, _ => m.getms dst

@[simp] def OpInstruction.apply: OpInstruction → Memory → Memory
| vop op dst src, m => m.setvs dst (op (m.getvs ∘ src))
| mop op dst src, m => (m.setms src (m.mop op dst src)).setms dst (m.getms src)
| const dst val, m => m.setms dst val

def BranchInstruction.apply: BranchInstruction → Memory → Bool
| ifTrue cond src, m => (cond (m.getvs ∘ src))
| ifNull src, m => m.getms src = 0

@[simp] def BranchInstruction.apply_ifTrue_def: (ifTrue c src).apply m = (c (m.getvs ∘ src)) := rfl
@[simp] def BranchInstruction.apply_ifNull_def: (ifNull src).apply m = decide (m.getms src = 0) := rfl

namespace Stack

def step: Stack → Stack
| execution ⟨m, .op f next, p⟩ caller => execution ⟨f.apply m, next, p⟩ caller
| execution ⟨m, .branch f next, p⟩ caller => execution ⟨m, next (f.apply m), p⟩ caller
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
| _+1, ⟨_, .branch _ _, _⟩, _, h => Nat.lt_succ_of_lt (stack_length_lt_istep_result h)
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

theorem step_branch (h: inst.apply m = b):
    step (execution ⟨m, .branch inst next, p⟩ cs) = execution ⟨m, next b, p⟩ cs :=
  h ▸ rfl

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

theorem istep_subroutine_result
    (h₀: step^[n₀] (.execution ⟨Memory.getms m src, func, func⟩ []) = .result r₀)
    (h₁: step^[n₁] (.execution ⟨m.setms dst r₀, is, p⟩ cs) = .result r₁):
    step^[n₁ + n₀ + 1] (.execution ⟨m, .subroutine dst src func is, p⟩ cs) = .result r₁ :=
  Program.subroutine_def ▸ istep_call_result (func := some func) h₀ h₁

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
end Stack


end HMem
