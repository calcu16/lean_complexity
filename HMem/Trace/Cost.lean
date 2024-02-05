import HMem.Trace.TracedProgram
import HMem.Trace.Sound
import Complexity.Asymptotic

theorem Option.bind_of_none (h: o = none): Option.bind o f = none := h ▸ rfl

namespace HMem
variable {α: Type _} [Complexity.Coding α Memory] {β: Type _} [Complexity.Encoding β Memory] {f: α → β} {tp: TracedProgram}
variable {γ: Type _} {δ: Type _} [Complexity.Coding γ Memory] [Complexity.Encoding δ Memory] {fs: γ → δ} {cs: Complexity.CostFunction γ ℕ} [Complexity.Computable Encoding.Model fs] [Complexity Encoding.Model fs cs]

namespace Trace
inductive CostedProgram
| exit
| op (inst: OpInstruction) (next: CostedProgram)
| branch (inst: BranchInstruction) (next: (b: Bool) → CostedProgram)
| subroutine (dst src: Source) {γ: Type _} {δ: Type _} [Complexity.Coding γ Memory] [Complexity.Encoding δ Memory]
  (fs: γ → δ) (cs: Complexity.CostFunction γ ℕ) [Complexity Encoding.Model fs cs] (next: CostedProgram)
| recurse (dst src: Source) (next: CostedProgram)

namespace CostedProgram

@[match_pattern] def subroutine' (dst src: Source) {γ: Type _} (_hγ: Complexity.Coding γ Memory) {δ: Type _} (_hδ: Complexity.Encoding δ Memory)
    (fs: γ → δ) (cs: Complexity.CostFunction γ ℕ) (_h': Complexity Encoding.Model fs cs) (next: CostedProgram): CostedProgram :=
  subroutine dst src fs cs next

@[simp] def toTracedProgram: CostedProgram → TracedProgram
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
  (localTimeCost (TracedProgram.sound'_branch_next_true h) +
   localTimeCost (TracedProgram.sound'_branch_next_false h)) +
  (1:Complexity.CostFunction Memory ℕ).flatMap fm
| .subroutine' _ _ _ _ _ _ _ _, fm, h =>
  localTimeCost (TracedProgram.sound'_subroutine_next h) +
  (1:Complexity.CostFunction Memory ℕ).flatMap fm
| .recurse _ _ _, fm, h => localTimeCost (TracedProgram.sound'_recurse_next h) + (1:Complexity.CostFunction Memory ℕ).flatMap fm

def subroutineTimeCost: {cp: CostedProgram} → {fm: α → Option Memory} →(h: cp.toTracedProgram.sound' f size fm) → Complexity.CostFunction α ℕ
| .exit, _, _ => 0
| .op _ _, _, h => subroutineTimeCost (TracedProgram.sound'_op_next h)
| .branch _ _, _, h =>
  subroutineTimeCost (TracedProgram.sound'_branch_next_true h) +
  subroutineTimeCost (TracedProgram.sound'_branch_next_false h)
| .subroutine' _ _ _ _ _ _ hcost _, _, h =>
  subroutineTimeCost (TracedProgram.sound'_subroutine_next h) +
  (Encoding.getBound hcost).flatMap (TracedProgram.sound'_subroutine_arg h)
| .recurse _ _ _, _, h => subroutineTimeCost (TracedProgram.sound'_recurse_next h)

def subroutineTimeCost_selfContained: {cp: CostedProgram} → cp.toProgram.selfContained → {fm: α → Option Memory} →(h: cp.toTracedProgram.sound' f size fm) → cp.subroutineTimeCost h = 0
| .exit, _, _, _ => rfl
| .op _ next, hs, _, h => subroutineTimeCost_selfContained (cp := next) hs (TracedProgram.sound'_op_next h)
| .branch _ _, hs, _, h =>
  funext λ _ ↦ add_eq_zero.mpr ⟨
    congrFun (subroutineTimeCost_selfContained (Bool.and_elim_left hs) (TracedProgram.sound'_branch_next_true h)) _,
    congrFun (subroutineTimeCost_selfContained (Bool.and_elim_right hs) (TracedProgram.sound'_branch_next_false h)) _ ⟩
| .subroutine' _ _ _ _ _ _ _ _, hs, _, _ => absurd hs Bool.noConfusion
| .recurse _ _ next, hs, _, h => subroutineTimeCost_selfContained (cp := next) hs (TracedProgram.sound'_recurse_next h)

def subroutineTimeComplexity: {cp: CostedProgram} → {fm: α → Option Memory} → (h: cp.toTracedProgram.sound' f size fm) → Complexity.CostFunction α ℕ
| .exit, _, _ => 0
| .op _ _, _, h => subroutineTimeComplexity (TracedProgram.sound'_op_next h)
| .branch _ _, _, h =>
  subroutineTimeComplexity (TracedProgram.sound'_branch_next_true h) +
  subroutineTimeComplexity (TracedProgram.sound'_branch_next_false h)
| .subroutine' _ _ _ _ _ cs _ _, _, h =>
  subroutineTimeComplexity (TracedProgram.sound'_subroutine_next h) +
  cs.flatMap (TracedProgram.sound'_subroutine_arg h)
| .recurse _ _ _, _, h => subroutineTimeComplexity (TracedProgram.sound'_recurse_next h)

def subroutineTimeComplexity': {cp: CostedProgram} → {m: Memory} → (h: cp.toTracedProgram.sound f sz a m) → ℕ
| .exit, _, _ => 0
| .op _ _, _, h => subroutineTimeComplexity' (TracedProgram.sound_op_next h)
| .branch _ _, _, h => subroutineTimeComplexity' (TracedProgram.sound_branch_next h)
| .subroutine' _ _ _ _ _ cs _ _, _, h =>
  subroutineTimeComplexity' (TracedProgram.sound_subroutine_next h) +
  cs (Option.get _ (TracedProgram.sound_subroutine_some h))
| .recurse _ _ _, _, h => subroutineTimeComplexity' (TracedProgram.sound_recurse_next h)

-- def subroutineTimeComplexity_eq: {cp: CostedProgram} → {fm: α → Option Memory} → ∀ arg ∈ fm a, (h: cp.toTracedProgram.sound f size a arg) → (h': cp.toTracedProgram.sound' f size fm) →
--   subroutineTimeComplexity' h = subroutineTimeComplexity h' a
-- | .exit, _, _, _, _, _ => rfl
-- | .op _ next, _, _, harg, _, _ => subroutineTimeComplexity_eq (cp := next) _ (Option.mem_map_of_mem _ harg) _ _
-- | .branch inst _, _, arg, harg, h, h' => by
--   match hi:inst.apply arg with
--   | true => sorry
--   | false => sorry
-- | _, _, _, _, _, _ => sorry



def subroutineTimeComplexity_elem: {cp: CostedProgram} → {fm: α → Option Memory} → (h: cp.toTracedProgram.sound' f size fm) →
    subroutineTimeCost h ∈ O(subroutineTimeComplexity h)
| .exit, _, _ => Complexity.ALE.refl
| .op _ _, _, h => subroutineTimeComplexity_elem (TracedProgram.sound'_op_next h)
| .branch _ _, _, _ => Complexity.ALE.add_ale_add
  (subroutineTimeComplexity_elem _)
  (subroutineTimeComplexity_elem _)
| .subroutine' _ _ _ _ _ _ _ _, _, h => Complexity.ALE.add_ale_add
    (subroutineTimeComplexity_elem (TracedProgram.sound'_subroutine_next h))
    (Complexity.ALE.flatMap_ale_flatMap (Complexity.ALE.bound_ale_self _) _)
| .recurse _ _ _, _, h =>
  subroutineTimeComplexity_elem (TracedProgram.sound'_recurse_next h)

def subroutineTimeComplexity_selfContained: {cp: CostedProgram} → cp.toProgram.selfContained → {fm: α → Option Memory} →(h: cp.toTracedProgram.sound' f size fm) → cp.subroutineTimeComplexity h = 0
| .exit, _, _, _ => rfl
| .op _ next, hs, _, h => subroutineTimeComplexity_selfContained (cp := next) hs (TracedProgram.sound'_op_next h)
| .branch _ _, hs, _, h =>
  funext λ _ ↦ add_eq_zero.mpr ⟨
    congrFun (subroutineTimeComplexity_selfContained (Bool.and_elim_left hs) (TracedProgram.sound'_branch_next_true h)) _,
    congrFun (subroutineTimeComplexity_selfContained (Bool.and_elim_right hs) (TracedProgram.sound'_branch_next_false h)) _ ⟩
| .subroutine' _ _ _ _ _ _ _ _, hs, _, _ => absurd hs Bool.noConfusion
| .recurse _ _ next, hs, _, h => subroutineTimeComplexity_selfContained (cp := next) hs (TracedProgram.sound'_recurse_next h)

def recurseTimeCost {fcp: CostedProgram} (hf: fcp.toTracedProgram.toProgram.sound f size): {cp: CostedProgram} → {fm: α → Option Memory} → (h: cp.toTracedProgram.sound' f size fm) → Complexity.CostFunction α ℕ
| .exit, _, _ => 0
| .op _ _, _, h => recurseTimeCost hf (TracedProgram.sound'_op_next h)
| .branch _ _, _, h =>
  recurseTimeCost hf (TracedProgram.sound'_branch_next_true h) +
  recurseTimeCost hf (TracedProgram.sound'_branch_next_false h)
| .subroutine' _ _ _ _ _ _ _ _, _, h =>
  recurseTimeCost hf (TracedProgram.sound'_subroutine_next h)
| .recurse _ _ _, _, h =>
  recurseTimeCost hf (TracedProgram.sound'_recurse_next h) +
  Complexity.CostFunction.flatMap (TracedProgram.sound'_recurse_arg h) λ arg ↦
    Program.timeCost _ (Program.halts_of_sound hf arg)

theorem recurseTimeCostNone {fcp: CostedProgram} (hf: fcp.toTracedProgram.toProgram.sound f size):
  {cp: CostedProgram} → {fm: α → Option Memory} → (h: cp.toTracedProgram.sound' f size fm) →
  fm a = none → recurseTimeCost hf h a = 0
| .exit, _, _, _ => rfl
| .op _ _, _, h, ha =>
  recurseTimeCostNone hf (TracedProgram.sound'_op_next h) (congrArg (Option.map _) ha)
| .branch _ _, _, h, ha => Nat.add_eq_zero_iff.mpr ⟨
    recurseTimeCostNone hf (TracedProgram.sound'_branch_next_true h) (congrArg (Option.filter _) ha),
    recurseTimeCostNone hf (TracedProgram.sound'_branch_next_false h) (congrArg (Option.filter _) ha) ⟩
| .subroutine'  _ _ _ _ _ _ _ _, _, h, ha =>
  recurseTimeCostNone hf (TracedProgram.sound'_subroutine_next h) (congrArg₂ Option.bind ha rfl)
| .recurse _ _ _, _, h, ha => Nat.add_eq_zero_iff.mpr
   ⟨ recurseTimeCostNone hf (TracedProgram.sound'_recurse_next h) (congrArg₂ Option.bind ha rfl),
     Complexity.CostFunction.flatMap_none (congrArg₂ Option.bind ha rfl) _⟩

def recurseSizeSum {a: α}: {cp: CostedProgram} → {m: Memory} → (h: cp.toTracedProgram.sound f sz a m) → ℕ
| .exit, _, _ => 0
| .op _ _, _, h => recurseSizeSum (TracedProgram.sound_op_next h)
| .branch _ _, _, h => recurseSizeSum (TracedProgram.sound_branch_next h)
| .subroutine' _ _ _ _ _ _ _ _, _, h => recurseSizeSum (TracedProgram.sound_subroutine_next h)
| .recurse _ _ _, _, h =>
  sz (Option.get _ (TracedProgram.sound_recurse_some h)) +
  recurseSizeSum (TracedProgram.sound_recurse_next h)

theorem recurseTimeCostBound {fcp: CostedProgram}
    (hf: fcp.toTracedProgram.toProgram.sound f sz)
    {a: α}
    (hsz: ∀ arg, sz arg < sz a → Program.timeCost _ (Program.halts_of_sound hf arg) ≤ x):
    {cp: CostedProgram} →
    {fm: α → Option Memory} →
    (hs: cp.toTracedProgram.sound' f sz fm) →
    recurseTimeCost hf hs a ≤ cp.toProgram.maxRecurse * x
| .exit, _, _ => zero_le _
| .op _ _, _, hs => recurseTimeCostBound hf hsz (TracedProgram.sound'_op_next hs)
| .branch inst _, fm, hs =>
  match hm:fm a with
  | some m => match hb:inst.apply m with
    | true => le_trans (le_of_eq_of_le
      ((congrArg₂ Nat.add rfl (recurseTimeCostNone hf _ (Option.filter_not_eq_none hm hb))).trans
      (add_zero _))
      (recurseTimeCostBound hf hsz (TracedProgram.sound'_branch_next_true hs)))
      (mul_le_mul (le_max_left _ _) (le_refl _) (zero_le _) (zero_le _))
    | false => le_trans (le_of_eq_of_le
      ((congrArg₂ Nat.add (recurseTimeCostNone hf _ (Option.filter_eq_none hm hb)) rfl).trans
      (zero_add _))
      (recurseTimeCostBound hf hsz (TracedProgram.sound'_branch_next_false hs)))
      (mul_le_mul (le_max_right _ _) (le_refl _) (zero_le _) (zero_le _))
  | none => le_of_eq_of_le (recurseTimeCostNone _ _ hm) (zero_le _)
| .subroutine' _ _ _ _ _ _ _ _, _, hs =>
  recurseTimeCostBound hf hsz (TracedProgram.sound'_subroutine_next hs)
| .recurse _ _ _, _, hs => le_of_le_of_eq (add_le_add
    (recurseTimeCostBound hf hsz (TracedProgram.sound'_recurse_next hs))
    (Complexity.CostFunction.flatMap_le_apply (g' := λ _ ↦ x) λ _ harg ↦ hsz _ (TracedProgram.sound'_recurse_arg_size hs _ harg)))
    (Nat.succ_mul _ _).symm

theorem localTimeCostInternal_le_size: {cp: CostedProgram} → (h: cp.toTracedProgram.sound' f size fm) →
  localTimeCost h ≤ λ _ ↦ cp.toProgram.size
| .exit, _, _ => Complexity.CostFunction.const_flatMap_le_const _ _ _
| .op _ _, _, _ => add_le_add
  (localTimeCostInternal_le_size _ _)
  (Complexity.CostFunction.const_flatMap_le_const _ _ _)
| .branch _ _, _, _ => add_le_add (add_le_add
  (localTimeCostInternal_le_size _ _)
  (localTimeCostInternal_le_size _ _))
  (Complexity.CostFunction.const_flatMap_le_const _ _ _)
| .subroutine' _ _ _ _ _ _ _ _, _, _ => add_le_add
  (le_add_left (localTimeCostInternal_le_size _ _))
  (Complexity.CostFunction.const_flatMap_le_const _ _ _)
| .recurse _ _ _, _, _ => add_le_add
  (localTimeCostInternal_le_size _ _)
  (Complexity.CostFunction.const_flatMap_le_const _ _ _)

theorem recurseTimeCost_leaf' {fcp: CostedProgram} (hf: fcp.toTracedProgram.toProgram.sound f size):
    {cp: CostedProgram} → (h: cp.toTracedProgram.sound' f size fm) →
    {a : α} → (∀ b, size a ≤ size b) → recurseTimeCost hc h a = 0
| .exit, _, _, _ => rfl
| .op _ next, _, _, hsize => recurseTimeCost_leaf' (cp := next) hf _ hsize
| .branch _ _, _, _, hsize =>
  Nat.add_eq_zero_iff.mpr ⟨
      recurseTimeCost_leaf' hf _ hsize,
      recurseTimeCost_leaf' hf _ hsize ⟩
| .subroutine' _ _ _ _ _ _ _ next, _, _, hsize =>
  recurseTimeCost_leaf' (cp := next) hf _ hsize
| .recurse _ _ _, h, _, hsize => Nat.add_eq_zero_iff.mpr ⟨
    recurseTimeCost_leaf' hf _ hsize,
    Complexity.CostFunction.flatMap_none
      (Option.bind_of_none (Option.eq_none_iff_forall_not_mem.mpr λ _ hm ↦
        (h.right.left _ _ hm).elim λ _ harg ↦
          (not_le_of_lt harg.right (hsize _))))
      _ ⟩

theorem recurseTimeCost_leaf {fcp: CostedProgram} (hf: fcp.toTracedProgram.toProgram.sound f size)
    {cp: CostedProgram} (h: cp.toTracedProgram.sound' f size fm)
    {a : α} (ha: size a = 0): recurseTimeCost hc h a = 0 :=
  recurseTimeCost_leaf' hf h (λ _ ↦ ha ▸ zero_le _)

theorem recurseTimeCost_maxRecurse_zero {fcp: CostedProgram} (hf: fcp.toTracedProgram.toProgram.sound f size):
    {cp: CostedProgram} → (h: cp.toTracedProgram.sound' f size fm) →
    (hr: cp.toProgram.maxRecurse = 0) → recurseTimeCost hc h = 0
| .exit, _, _ => rfl
| .op _ next, _, hr => recurseTimeCost_maxRecurse_zero hf (cp := next) _ hr
| .branch _ _, _, hr => add_eq_zero_iff.mpr ⟨
  recurseTimeCost_maxRecurse_zero hf _ (Nat.max_eq_zero_iff.mp hr).left,
  recurseTimeCost_maxRecurse_zero hf _ (Nat.max_eq_zero_iff.mp hr).right ⟩
| .subroutine' _ _ _ _ _ _ _ next, _, hr =>
  recurseTimeCost_maxRecurse_zero (cp := next) hf _ hr
| .recurse _ _ _, _, hr => absurd hr Nat.noConfusion

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
| .subroutine' _ _ _ _ _ _ hcost next, h, a, m, hm => by
  apply Stack.hasTimeCost_subroutine_le _
  rw [TracedProgram.sound_subroutine_arg (TracedProgram.sound_of_sound' h _ _ hm)]
  apply hcost.toComputable.has_result
  rw [TracedProgram.sound_subroutine_arg (TracedProgram.sound_of_sound' h _ _ hm)]
  apply (Stack.timeCost_le_iff _ _).mpr
  apply hcost.cost_ale.le_bound
  exact (hcost.toComputable.has_result _).elim λ _ h ↦ ⟨(_, _), h⟩
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

class HasCostedProgram (p: Program) where
  costedProgram: CostedProgram
  costedProgramMatches: costedProgram.toProgram = p

attribute [simp] HasCostedProgram.costedProgram

instance [h: HasCostedProgram p]: HasTracedProgram p where
  tracedProgram := h.costedProgram.toTracedProgram
  tracedProgramMatches := h.costedProgramMatches

end Trace

namespace Program
class HasCost (f: α → β) (fc: semiOutParam (Complexity.CostFunction α ℕ)) where
  program: List (Program → Program)
  [hasCostedProgram: Trace.HasCostedProgram (Program.build program)]
  size: α → ℕ
  sound: (Program.build program).sound f size
  cost_ale: (Program.build program).timeCost' sound ∈ O(fc)

instance [h: HasCost f c]: Trace.HasCostedProgram (Program.build h.program) := h.hasCostedProgram

instance[h: HasCost f c]: HasTrace f where
  program := h.program
  size := h.size
  sound := h.sound

def costed (p: Program) [h: Trace.HasCostedProgram p]: Trace.CostedProgram := h.costedProgram

@[simp] theorem costedMatches (p: Program) [h: Trace.HasCostedProgram p]:
    p.costed.toProgram = p := h.costedProgramMatches

@[simp] theorem costedMatches' (p: Program) [Trace.HasCostedProgram p]:
    p.costed.toTracedProgram.toProgram = p := p.tracedMatches

@[simp] theorem costedMatchesTraced (p: Program) [Trace.HasCostedProgram p]:
    p.costed.toTracedProgram = p.traced := rfl

theorem costed_sound {p: Program} [Trace.HasCostedProgram p] (h: p.sound f sz):
    (p.costed.toTracedProgram.toProgram).sound f sz := p.costedMatchesTraced ▸ h

theorem costed_sound' {p: Program} [Trace.HasCostedProgram p] (h: p.sound f sz):
    (p.costed.toTracedProgram).sound' f sz (some ∘ Complexity.encode) :=
  p.costedMatchesTraced ▸ Trace.TracedProgram.sound'_of_sound λ _ _ hm ↦
    (Option.some.inj (Option.mem_def.mp hm)) ▸ h _

def localTimeCost {p: Program} [Trace.HasCostedProgram p] (h: sound p f sz): Complexity.CostFunction α ℕ :=
  p.costed.localTimeCost (costed_sound' h)

def subroutineTimeCost {p: Program} [Trace.HasCostedProgram p] (h: sound p f sz): Complexity.CostFunction α ℕ :=
  p.costed.subroutineTimeCost (costed_sound' h)

def subroutineTimeCost_selfContained {p: Program} [Trace.HasCostedProgram p] (h: sound p f sz) (hs: p.selfContained): p.subroutineTimeCost h ∈ O(0):=
  ⟨0, 0, le_of_eq_of_le (p.costed.subroutineTimeCost_selfContained (p.costedMatches.symm ▸ hs) _) (zero_le _)⟩

def subroutineTimeComplexity {p: Program} [Trace.HasCostedProgram p] (h: sound p f sz): Complexity.CostFunction α ℕ :=
  p.costed.subroutineTimeComplexity (costed_sound' h)

def subroutineTimeComplexity_elem {p: Program} [Trace.HasCostedProgram p] (h: sound p f sz):
    p.subroutineTimeCost h ∈ O(p.subroutineTimeComplexity h) := p.costed.subroutineTimeComplexity_elem _

def subroutineTimeComplexity_selfContained {p: Program} [Trace.HasCostedProgram p] (h: sound p f sz) (hs: p.selfContained): p.subroutineTimeComplexity h ∈ O(0):=
  ⟨0, 0, le_of_eq_of_le (p.costed.subroutineTimeComplexity_selfContained (p.costedMatches.symm ▸ hs) _) (zero_le _)⟩

def recurseTimeCost {p: Program} [Trace.HasCostedProgram p] (h: sound p f sz): Complexity.CostFunction α ℕ :=
  p.costed.recurseTimeCost (costed_sound h) (costed_sound' h)

theorem recurseTimeCost_maxRecurse_zero {p: Program} [Trace.HasCostedProgram p] (h: sound p f sz) (hr: p.maxRecurse = 0):
    p.recurseTimeCost h = 0 :=
  Trace.CostedProgram.recurseTimeCost_maxRecurse_zero h (costed_sound' h) (p.costedMatches.symm ▸ hr)

def localTimeCost_const {p: Program} [Trace.HasCostedProgram p] (h: sound p f sz): localTimeCost h ∈ O(1) := ⟨
    p.size, 0,
    by
      apply le_of_le_of_eq _
      apply (mul_one _).symm
      apply le_of_le_of_eq
      apply Trace.CostedProgram.localTimeCostInternal_le_size (costed_sound' h)
      rw [costedMatches] ⟩

theorem splitTimeCost {p: Program} [Trace.HasCostedProgram p] (h: sound p f sz):
    p.timeCost' h ≤  p.subroutineTimeCost h + p.recurseTimeCost h + p.localTimeCost h := by
  intro a
  apply le_trans
  exact (Stack.timeCost_le_iff _ (Program.halts_of_sound h _)).mp (p.costedMatches ▸ p.costed.splitTimeCost (costed_sound h) (costed_sound' h) a _ (Option.mem_some_iff.mpr rfl))
  exact le_refl _
end Program

instance [h: Program.HasCost f c]: Complexity Encoding.Model f c where
  cost_ale := h.cost_ale

end HMem
