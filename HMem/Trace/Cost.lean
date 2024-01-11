import HMem.Trace.TracedProgram
import HMem.Trace.Sound

namespace HMem.Trace.TracedProgram
variable {α: Type _} [Complexity.Encoding α Memory] {β: Type _} [Complexity.Encoding β Memory] {f: α → β}
variable {γ: Type _} {δ: Type _} [Complexity.Encoding γ Memory] [Complexity.Encoding δ Memory] {fs: γ → δ} [Complexity Encoding.Model fs]

def timeCost {tp: TracedProgram f} (h: sound tp size): Complexity.CostFunction α ℕ :=
  λ a ↦ Program.timeCost _ (halts h a)

def localTimeCostInternal: {tp: TracedProgram f} → (h: soundInternal' size tp fm) → Complexity.CostFunction α ℕ
| .exit, _ => 1
| .op _ _, h => localTimeCostInternal (soundInternal'_op_next h) + 1
| .branch _ _, h => localTimeCostInternal (soundInternal'_branch_next_true h) + localTimeCostInternal (soundInternal'_branch_next_false h) + 1
| .subroutine' _ _ _ _ _ _ _, h => localTimeCostInternal (soundInternal'_subroutine_next h) + 1
| .recurse _ _ _, h => localTimeCostInternal (soundInternal'_recurse_next h) + 1

def localTimeCost {tp: TracedProgram f} (h: tp.sound size): Complexity.CostFunction α ℕ := localTimeCostInternal (soundInternal'_of_sound (f := f) ▸ h)

def subroutineTimeCostInternal: {tp: TracedProgram f} → (h: soundInternal' size tp fm) → Complexity.CostFunction α ℕ
| .exit, _ => 0
| .op _ _, h => subroutineTimeCostInternal (soundInternal'_op_next h)
| .branch _ _, h => subroutineTimeCostInternal (soundInternal'_branch_next_true h) + subroutineTimeCostInternal (soundInternal'_branch_next_false h)
| .subroutine' _ _ _ _ _ hp _, h => subroutineTimeCostInternal (soundInternal'_subroutine_next h) + hp.cost.flatMap (soundInternal'_subroutine_arg h)
| .recurse _ _ _, h => subroutineTimeCostInternal (soundInternal'_recurse_next h)

def subroutineTimeCost {tp: TracedProgram f} (h: tp.sound size): Complexity.CostFunction α ℕ := subroutineTimeCostInternal (soundInternal'_of_sound (f := f) ▸ h)

def recurseTimeCostInternal {tp: TracedProgram f} (h: tp.sound size): {curr: TracedProgram f} → (hc: soundInternal' size curr fm) → Complexity.CostFunction α ℕ
| .exit, _ => 0
| .op _ _, hc => recurseTimeCostInternal h (soundInternal'_op_next hc)
| .branch _ _, hc => recurseTimeCostInternal h (soundInternal'_branch_next_true hc) + recurseTimeCostInternal h (soundInternal'_branch_next_false hc)
| .subroutine' _ _ _ _ _ _ _, hc => recurseTimeCostInternal h (soundInternal'_subroutine_next hc)
| .recurse _ _ _, hc => recurseTimeCostInternal h (soundInternal'_recurse_next hc) + (timeCost h).flatMap (soundInternal'_recurse_arg hc)

def recurseTimeCost {tp: TracedProgram f} (h: tp.sound size): Complexity.CostFunction α ℕ := recurseTimeCostInternal h (soundInternal'_of_sound (f := f) ▸ h)

-- theorem recurseTimeCostInternal_leaf {tp: TracedProgram f} (h: tp.sound size):
--     {curr: TracedProgram f} → (hc: soundInternal' size curr fm) →
--     {a : α} → size a = 0 → recurseTimeCostInternal h hc a = 0
-- | .exit, _, _, _ => rfl
-- | .op _ next, _, _, hsize => recurseTimeCostInternal_leaf (curr := next) h _ hsize
-- | .branch _ next, _, _, hsize =>
--   Nat.add_eq_zero_iff.mpr ⟨
--       recurseTimeCostInternal_leaf _ _ hsize,
--       recurseTimeCostInternal_leaf _ _ hsize ⟩
-- | .subroutine' _ _ _ _ _ _ next, _, _, hsize => recurseTimeCostInternal_leaf (curr := next) h _ hsize
-- | .recurse _ _ _, hc, a, hsize => by
--   apply Nat.add_eq_zero_iff.mpr
--   apply And.intro
--   exact recurseTimeCostInternal_leaf _ _ hsize
--   have hx := hc.right.left a





end HMem.Trace.TracedProgram
