import HMem.Trace.TracedProgram
import HMem.Trace.Sound

theorem Option.Forall_false: {o: Option α} → Option.Forall P o → (∀ a, ¬ P a ) → o = none
| some _, hP, h => (h _ hP).recOn
| none, _, _ => rfl

def Option.Exists_exists: {o: Option α} → Option.Exists P o → (∃ a, o = some a ∧ P a)
| some _, h => ⟨_, rfl, h⟩
| none, h => absurd h not_false

theorem Option.bind_of_none (h: o = none): Option.bind o f = none := h ▸ rfl

namespace HMem.Trace
variable {α: Type _} [Complexity.Encoding α Memory] {β: Type _} [Complexity.Encoding β Memory] {f: α → β} {tp: TracedProgram f}
variable {γ: Type _} {δ: Type _} [Complexity.Encoding γ Memory] [Complexity.Encoding δ Memory] {fs: γ → δ} [Complexity.Computable Encoding.Model fs] [Complexity Encoding.Model fs]

inductive CostedProgram: TracedProgram f → Type _
| exit: CostedProgram .exit
| op (inst: OpInstruction) {tp: TracedProgram f} (next: CostedProgram tp): CostedProgram (.op inst tp)
| branch (inst: BranchInstruction) {tp: Bool → TracedProgram f} (pos: (b: Bool) → CostedProgram (tp b)): CostedProgram (.branch inst tp)
| subroutine (dst src: Source) {γ: Type _} {δ: Type _} [Complexity.Encoding γ Memory] [Complexity.Encoding δ Memory]
  {fs: γ → δ} [Complexity.Computable Encoding.Model fs] [Complexity Encoding.Model fs] {tp: TracedProgram f} (next: CostedProgram tp): CostedProgram (.subroutine dst src fs tp)
| recurse (dst src: Source) {tp: TracedProgram f} (next: CostedProgram tp): CostedProgram (.recurse dst src tp)

class WithCost (tp: TracedProgram f) where
  cost: CostedProgram tp

instance: WithCost (f := f) .exit := ⟨ .exit ⟩
instance [next: WithCost tp]: WithCost (f := f) (.op inst tp) := ⟨ .op inst next.cost ⟩

def timeCost {tp: TracedProgram f} (h: tp.sound size): Complexity.CostFunction α ℕ :=
  λ a ↦ Program.timeCost _ (tp.halts h a)

def localTimeCostInternal: {tp: TracedProgram f} → {fm: α → Option Memory} → (h: tp.soundInternal' size fm) → Complexity.CostFunction α ℕ
| .exit, fm, _ => (1:Complexity.CostFunction Memory ℕ).flatMap fm
| .op _ _, fm, h => localTimeCostInternal (TracedProgram.soundInternal'_op_next h) + (1:Complexity.CostFunction Memory ℕ).flatMap fm
| .branch _ _, fm, h => localTimeCostInternal (TracedProgram.soundInternal'_branch_next_true h) + localTimeCostInternal (TracedProgram.soundInternal'_branch_next_false h) + (1:Complexity.CostFunction Memory ℕ).flatMap fm
| .subroutine' _ _ _ _ _ _ _, fm, h => localTimeCostInternal (TracedProgram.soundInternal'_subroutine_next h) + (1:Complexity.CostFunction Memory ℕ).flatMap fm
| .recurse _ _ _, fm, h => localTimeCostInternal (TracedProgram.soundInternal'_recurse_next h) + (1:Complexity.CostFunction Memory ℕ).flatMap fm

theorem localTimeCostInternal_le_size: {tp: TracedProgram f} → (h: tp.soundInternal' size fm) →
  ∀ a, localTimeCostInternal h a ≤ tp.toProgram.size
| .exit, _, _ => Complexity.CostFunction.nat_flatMap_le_nat _ _ _
| .op _ _, _, _ => add_le_add
  (localTimeCostInternal_le_size _ _)
  (Complexity.CostFunction.nat_flatMap_le_nat _ _ _)
| .branch _ _, _, _ => add_le_add (add_le_add
  (localTimeCostInternal_le_size _ _)
  (localTimeCostInternal_le_size _ _))
  (Complexity.CostFunction.nat_flatMap_le_nat _ _ _)
| .subroutine' _ _ _ _ _ _ _, _, _ => add_le_add
  (le_add_left (localTimeCostInternal_le_size _ _))
  (Complexity.CostFunction.nat_flatMap_le_nat _ _ _)
| .recurse _ _ _, _, _ => add_le_add
  (localTimeCostInternal_le_size _ _)
  (Complexity.CostFunction.nat_flatMap_le_nat _ _ _)

def localTimeCost (h: tp.sound size): Complexity.CostFunction α ℕ := localTimeCostInternal (TracedProgram.soundInternal'_of_sound h)

def localTimeCost_O1 (h: tp.sound size): Complexity.O (localTimeCost h) = Complexity.O (1) :=
  flip le_antisymm (Complexity.Asymptotic.o1_le _) ⟨_, le_add_left (localTimeCostInternal_le_size _)⟩

def subroutineTimeCostInternal: {tp: TracedProgram f} → CostedProgram tp → (h: tp.soundInternal' size fm) → Complexity.CostFunction α ℕ
| _, .exit, _ => 0
| _, .op _ next, h => subroutineTimeCostInternal next (TracedProgram.soundInternal'_op_next h)
| _, .branch _ next, h =>
  subroutineTimeCostInternal (next true) (TracedProgram.soundInternal'_branch_next_true h) +
  subroutineTimeCostInternal (next false) (TracedProgram.soundInternal'_branch_next_false h)
| _, @CostedProgram.subroutine _ _ _ _ _ _ _ _ _ _ _ _ _ hcost _ next, h =>
  subroutineTimeCostInternal next (TracedProgram.soundInternal'_subroutine_next h) +
  hcost.cost.flatMap (TracedProgram.soundInternal'_subroutine_arg h)
| _, .recurse _ _ next, h => subroutineTimeCostInternal next (TracedProgram.soundInternal'_recurse_next h)

def subroutineTimeCost {tp: TracedProgram f} [hc: WithCost tp] (h: tp.sound size): Complexity.CostFunction α ℕ :=
  subroutineTimeCostInternal hc.cost (TracedProgram.soundInternal'_of_sound h)

def recurseTimeCostInternal {tp: TracedProgram f} (h: tp.sound size): {curr: TracedProgram f} → (hc: TracedProgram.soundInternal' size curr fm) → Complexity.CostFunction α ℕ
| .exit, _ => 0
| .op _ _, hc => recurseTimeCostInternal h (TracedProgram.soundInternal'_op_next hc)
| .branch _ _, hc => recurseTimeCostInternal h (TracedProgram.soundInternal'_branch_next_true hc) + recurseTimeCostInternal h (TracedProgram.soundInternal'_branch_next_false hc)
| .subroutine' _ _ _ _ _ _ _, hc => recurseTimeCostInternal h (TracedProgram.soundInternal'_subroutine_next hc)
| .recurse _ _ _, hc => recurseTimeCostInternal h (TracedProgram.soundInternal'_recurse_next hc) + (timeCost h).flatMap (TracedProgram.soundInternal'_recurse_arg hc)

def recurseTimeCost (h: tp.sound size): Complexity.CostFunction α ℕ := recurseTimeCostInternal h (TracedProgram.soundInternal'_of_sound  h)

theorem recurseTimeCostInternal_leaf {tp: TracedProgram f} (h: tp.sound size):
    {curr: TracedProgram f} → (hc: TracedProgram.soundInternal' size curr fm) →
    {a : α} → size a = 0 → recurseTimeCostInternal h hc a = 0
| .exit, _, _, _ => rfl
| .op _ next, _, _, hsize => recurseTimeCostInternal_leaf (curr := next) h _ hsize
| .branch _ _, _, _, hsize =>
  Nat.add_eq_zero_iff.mpr ⟨
      recurseTimeCostInternal_leaf _ _ hsize,
      recurseTimeCostInternal_leaf _ _ hsize ⟩
| .subroutine' _ _ _ _ _ _ next, _, _, hsize => recurseTimeCostInternal_leaf (curr := next) h _ hsize
| .recurse _ _ _, hc, _, hsize => Nat.add_eq_zero_iff.mpr ⟨
    recurseTimeCostInternal_leaf _ _ hsize,
    Complexity.CostFunction.flatMap_none
      (Option.bind_of_none (Option.Forall_false (hc.right.left _) λ _ hm ↦
        (Option.Exists_exists hm).elim λ _ ha ↦
          Nat.not_lt_zero _ (Nat.lt_of_lt_of_eq ha.right hsize))) _ ⟩

theorem recurseTimeCostInternal_zero {tp: TracedProgram f} (h: tp.sound λ _ ↦ 0):
  recurseTimeCost h = 0 := funext λ _ ↦ recurseTimeCostInternal_leaf h _ rfl

theorem splitTimeCostInternal {tp: TracedProgram f} (hp: tp.sound size): {curr: TracedProgram f} → (hc: CostedProgram curr) → {fm: α → Option Memory} → (h: curr.soundInternal' size fm) →
    ∀ a, Option.Forall (λ m ↦ Stack.hasTimeCost
      (.execution ⟨m, curr.toProgram, tp.toProgram⟩ [])
      ((subroutineTimeCostInternal hc h + recurseTimeCostInternal hp h + localTimeCostInternal h) a)) (fm a)
| _, .exit, fm, h, a =>
  Option.Forall_forall λ _ hm ↦ ⟨_, Stack.istep_result_le (le_add_left (le_of_eq (Eq.symm (Complexity.CostFunction.flatMap_some hm _)))) rfl⟩
| _, .op inst next, fm, h, a => by
  apply Option.Forall_forall
  intro m hm
  -- apply Stack.hasTimeCost_step
  sorry
| _, _, _, _, _ => sorry


end HMem.Trace
