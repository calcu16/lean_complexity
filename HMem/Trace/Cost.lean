import HMem.Trace.TracedProgram
import HMem.Trace.Sound

theorem Option.bind_of_none (h: o = none): Option.bind o f = none := h ▸ rfl

namespace HMem
variable {α: Type _} [Complexity.Encoding α Memory] {β: Type _} [Complexity.Encoding β Memory] {f: α → β} {tp: TracedProgram}
variable {γ: Type _} {δ: Type _} [Complexity.Encoding γ Memory] [Complexity.Encoding δ Memory] {fs: γ → δ} [Complexity.Computable Encoding.Model fs] [Complexity Encoding.Model fs]

namespace Trace
inductive CostedProgram
| exit
| op (inst: OpInstruction) (next: CostedProgram)
| branch (inst: BranchInstruction) (next: (b: Bool) → CostedProgram)
| subroutine (dst src: Source) {γ: Type _} {δ: Type _} [Complexity.Encoding γ Memory] [Complexity.Encoding δ Memory]
  (fs: γ → δ) [Complexity.Computable Encoding.Model fs] [Complexity Encoding.Model fs] (next: CostedProgram)
| recurse (dst src: Source) (next: CostedProgram)

namespace CostedProgram

@[match_pattern] def subroutine' (dst src: Source) {γ: Type _} (_hγ: Complexity.Encoding γ Memory) {δ: Type _} (_hδ: Complexity.Encoding δ Memory)
    (fs: γ → δ) (_h: Complexity.Computable Encoding.Model fs) (_h': Complexity Encoding.Model fs) (next: CostedProgram): CostedProgram :=
  subroutine dst src fs next

def toTracedProgram: CostedProgram → TracedProgram
| .exit => .exit
| .op inst next => .op inst next.toTracedProgram
| .branch inst next => .branch inst (λ b ↦ (next b).toTracedProgram)
| .subroutine' dst src _ _ fs _ _ next => .subroutine dst src fs next.toTracedProgram
| .recurse dst src next => .recurse dst src next.toTracedProgram

def toProgram: CostedProgram → Program := TracedProgram.toProgram ∘ toTracedProgram

def localTimeCost: {cp: CostedProgram} → {fm: α → Option Memory} →(h: cp.toTracedProgram.sound' f size fm) → Complexity.CostFunction α ℕ
| .exit, fm, _ => (1:Complexity.CostFunction Memory ℕ).flatMap fm
| .op _ _, fm, h => localTimeCost (TracedProgram.sound'_op_next h) + (1:Complexity.CostFunction Memory ℕ).flatMap fm
| .branch _ _, fm, h =>
  localTimeCost (TracedProgram.sound'_branch_next_true h) +
  localTimeCost (TracedProgram.sound'_branch_next_false h) + (1:Complexity.CostFunction Memory ℕ).flatMap fm
| .subroutine' _ _ _ _ _ _ _ _, fm, h => localTimeCost (TracedProgram.sound'_subroutine_next h) + (1:Complexity.CostFunction Memory ℕ).flatMap fm
| .recurse _ _ _, fm, h => localTimeCost (TracedProgram.sound'_recurse_next h) + (1:Complexity.CostFunction Memory ℕ).flatMap fm

def subroutineTimeCost: {cp: CostedProgram} → {fm: α → Option Memory} →(h: cp.toTracedProgram.sound' f size fm) → Complexity.CostFunction α ℕ
| .exit, _, _ => 0
| .op _ _, _, h => subroutineTimeCost (TracedProgram.sound'_op_next h)
| .branch _ _, _, h =>
  subroutineTimeCost (TracedProgram.sound'_branch_next_true h) +
  subroutineTimeCost (TracedProgram.sound'_branch_next_false h)
| .subroutine' _ _ _ _ _ _ hcost _, _, h =>
  subroutineTimeCost (TracedProgram.sound'_subroutine_next h) +
  hcost.cost.flatMap (TracedProgram.sound'_subroutine_arg h)
| .recurse _ _ _, _, h => subroutineTimeCost (TracedProgram.sound'_recurse_next h)

def recurseTimeCost {fcp: CostedProgram} (hf: fcp.toTracedProgram.toProgram.sound f size): {cp: CostedProgram} → {fm: α → Option Memory} →(h: cp.toTracedProgram.sound' f size fm) → Complexity.CostFunction α ℕ
| .exit, _, _ => 0
| .op _ _, _, h => recurseTimeCost hf (TracedProgram.sound'_op_next h)
| .branch _ _, _, h =>
  recurseTimeCost hf (TracedProgram.sound'_branch_next_true h) +
  recurseTimeCost hf (TracedProgram.sound'_branch_next_false h)
| .subroutine' _ _ _ _ _ _ _ _, _, h => recurseTimeCost hf (TracedProgram.sound'_subroutine_next h)
| .recurse _ _ _, _, h =>
  recurseTimeCost hf (TracedProgram.sound'_recurse_next h) +
  Complexity.CostFunction.flatMap (TracedProgram.sound'_recurse_arg h) λ arg ↦
    Program.timeCost _ (Program.halts_of_sound hf arg)

theorem localTimeCostInternal_le_size: {cp: CostedProgram} → (h: cp.toTracedProgram.sound' f size fm) →
  localTimeCost h ≤ cp.toProgram.size
| .exit, _, _ => Complexity.CostFunction.nat_flatMap_le_nat _ _ _
| .op _ _, _, _ => add_le_add
  (localTimeCostInternal_le_size _ _)
  (Complexity.CostFunction.nat_flatMap_le_nat _ _ _)
| .branch _ _, _, _ => add_le_add (add_le_add
  (localTimeCostInternal_le_size _ _)
  (localTimeCostInternal_le_size _ _))
  (Complexity.CostFunction.nat_flatMap_le_nat _ _ _)
| .subroutine' _ _ _ _ _ _ _ _, _, _ => add_le_add
  (le_add_left (localTimeCostInternal_le_size _ _))
  (Complexity.CostFunction.nat_flatMap_le_nat _ _ _)
| .recurse _ _ _, _, _ => add_le_add
  (localTimeCostInternal_le_size _ _)
  (Complexity.CostFunction.nat_flatMap_le_nat _ _ _)

theorem recurseTimeCost_leaf {fcp: CostedProgram} (hf: fcp.toTracedProgram.toProgram.sound f size):
    {cp: CostedProgram} → (h: cp.toTracedProgram.sound' f size fm) →
    {a : α} → size a = 0 → recurseTimeCost hc h a = 0
| .exit, _, _, _ => rfl
| .op _ next, _, _, hsize => recurseTimeCost_leaf (cp := next) hf _ hsize
| .branch _ _, _, _, hsize =>
  Nat.add_eq_zero_iff.mpr ⟨
      recurseTimeCost_leaf hf _ hsize,
      recurseTimeCost_leaf hf _ hsize ⟩
| .subroutine' _ _ _ _ _ _ _ next, _, _, hsize =>
  recurseTimeCost_leaf (cp := next) hf _ hsize
| .recurse _ _ _, h, _, hsize => Nat.add_eq_zero_iff.mpr ⟨
    recurseTimeCost_leaf hf _ hsize,
    Complexity.CostFunction.flatMap_none
      (Option.bind_of_none (Option.eq_none_iff_forall_not_mem.mpr λ _ hm ↦
        (h.right.left _ _ hm).elim λ _ harg ↦
          Nat.not_lt_zero _ (lt_of_lt_of_eq harg.right hsize)))
      _ ⟩

theorem splitTimeCost {fcp: CostedProgram} (hf: fcp.toTracedProgram.toProgram.sound f size):
    {cp: CostedProgram} → (h: cp.toTracedProgram.sound' f size fm) →
    ∀ a, ∀ m ∈ fm a, Stack.hasTimeCost
      (.execution ⟨m, cp.toProgram, fcp.toProgram⟩ [])
      ((subroutineTimeCost h + recurseTimeCost hf h + localTimeCost h) a)
| .exit, _, _, _, hm => ⟨_,
  Stack.istep_result_le
    (le_add_left (le_of_eq (Eq.symm (Complexity.CostFunction.flatMap_some hm _))))
    rfl⟩
| .op _ _, h, _, _, hm => Stack.hasTimeCost_of_step_le_succ
  (le_of_le_of_eq (add_le_add
      (le_refl _)
      (le_of_eq (Eq.symm (Complexity.CostFunction.flatMap_some hm _))))
    (Nat.add_assoc _ _ _))
  (splitTimeCost hf (TracedProgram.sound'_op_next h) _ _ (congrArg _ hm))
| .branch inst next, h, _, m, hm =>
  match hb:inst.apply m with
  | true => Stack.hasTimeCost_of_step_le_succ' (Stack.step_branch hb).symm
    (le_of_le_of_eq (add_le_add (add_le_add (add_le_add
      (Nat.le_add_right _ _)
      (Nat.le_add_right _ _))
      (Nat.le_add_right _ _))
      (le_of_eq (Eq.symm (Complexity.CostFunction.flatMap_some hm _))))
      (Nat.add_assoc _ _ _))
    (splitTimeCost hf
      (TracedProgram.sound'_branch_next_true h) _ _
      (Option.mem_filter_of_mem hm hb))
  | false => Stack.hasTimeCost_of_step_le_succ' (Stack.step_branch hb).symm
    (le_of_le_of_eq (add_le_add (add_le_add (add_le_add
      (Nat.le_add_left _ _)
      (Nat.le_add_left _ _))
      (Nat.le_add_left _ _))
      (le_of_eq (Eq.symm (Complexity.CostFunction.flatMap_some hm _))))
      (Nat.add_assoc _ _ _))
    (splitTimeCost hf
      (TracedProgram.sound'_branch_next_false h) _ _
      (Option.mem_filter_of_mem hm (congrArg Bool.not hb)))
| .subroutine' _ _ _ _ _ hcomp hcost next, h, a, m, hm => by
  apply Stack.hasTimeCost_subroutine_le _
  rw [TracedProgram.sound_subroutine_arg (TracedProgram.sound_of_sound' h _ _ hm)]
  apply hcomp.has_result
  rw [TracedProgram.sound_subroutine_arg (TracedProgram.sound_of_sound' h _ _ hm)]
  apply (Stack.timeCost_le_iff _ _).mpr
  apply hcost.cost_le
  exact (hcomp.has_result _).elim λ _ h ↦ ⟨(_, _), h⟩
  apply splitTimeCost hf (TracedProgram.sound'_subroutine_next h)
  apply Option.mem_bind_of_mem hm
  apply Option.mem_map_of_mem
  apply Option.get_mem
  apply le_of_le_of_eq _
  apply Nat.add_assoc
  apply add_le_add _
  apply (le_of_eq (Eq.symm (Complexity.CostFunction.flatMap_some hm _)))
  apply le_of_eq_of_le
  apply Eq.trans
  apply add_comm
  apply (Nat.add_assoc _ _ _).symm
  apply add_le_add _ (le_refl _)
  apply le_of_eq_of_le
  apply (Nat.add_assoc _ _ _).symm
  apply add_le_add _ (le_refl _)
  apply le_of_eq_of_le
  apply add_comm
  apply add_le_add (le_refl _)
  apply le_of_le_of_eq _
  apply Eq.symm
  apply Complexity.CostFunction.flatMap_some
  apply Option.mem_bind_of_mem
  apply hm
  apply Option.get_mem
  apply (h.left _ _ hm).elim λ hsome _ ↦ hsome
  apply le_refl
| .recurse _ _ _, h, _, _, hm => by
  apply Stack.hasTimeCost_recurse_le _
  rw [TracedProgram.sound_recurse_arg (TracedProgram.sound_of_sound' h _ _ hm)]
  apply Program.hasResult_of_sound hf
  rw [TracedProgram.sound_recurse_arg (TracedProgram.sound_of_sound' h _ _ hm)]
  apply Stack.timeCost_sound
  apply Program.halts_of_sound hf
  apply splitTimeCost hf (TracedProgram.sound'_recurse_next h)
  apply Option.mem_bind_of_mem hm
  apply Option.mem_map_of_mem
  apply Option.get_mem
  apply le_of_le_of_eq _
  apply Nat.add_assoc
  apply add_le_add _
  apply (le_of_eq (Eq.symm (Complexity.CostFunction.flatMap_some hm _)))
  apply le_of_eq_of_le
  apply Eq.trans
  apply add_comm
  apply (Nat.add_assoc _ _ _).symm
  apply add_le_add _ (le_refl _)
  apply le_of_eq_of_le
  apply Eq.trans
  apply add_comm
  apply Nat.add_assoc _ _ _
  apply add_le_add (le_refl _)
  apply add_le_add (le_refl _)
  apply le_of_le_of_eq _
  apply Eq.symm
  apply Complexity.CostFunction.flatMap_some
  apply Option.mem_bind_of_mem
  apply hm
  apply Option.get_mem
  apply (h.left _ _ hm).elim λ hsome _ ↦ hsome
  apply le_refl

end CostedProgram

class HasCostedProgram (p: Program) extends HasTracedProgram p where
  costedProgram: CostedProgram
  costedProgramMatches: costedProgram.toTracedProgram = tracedProgram

end Trace

class Program.HasCost (f: α → β) extends Program.HasTrace f where
  [hasCostedProgram: Trace.HasCostedProgram (Program.build program)]
  cost: Complexity.CostFunction α ℕ
  cost_le: (Program.build program).timeCost' sound ≲ cost

instance [h: Program.HasCost f]: Complexity Encoding.Model f where
  cost_le := h.cost_le.le_bound

end HMem
