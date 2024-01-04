import Complexity.Basic
import HMem.Encoding.Basic

namespace HMem
namespace Complexity

inductive TracedProgram {α: Type _} [Complexity.Encoding α Memory] {β: Type _} [Complexity.Encoding β Memory] (f: α → β)
| exit
| op (inst: OpInstruction) (next: TracedProgram f)
| branch (inst: BranchInstruction) (pos: TracedProgram f) (neg: TracedProgram f)
| subroutine (dst src: Source) {γ: Type _} [Complexity.Encoding γ Memory] {δ: Type _} [Complexity.Encoding δ Memory]
  (func: γ → δ) [Computable Encoding.Model func] (next: TracedProgram f)
| recurse (dst src: Source) (next: TracedProgram f)

namespace TracedProgram
variable {α: Type _} [Complexity.Encoding α Memory] {β: Type _} [Complexity.Encoding β Memory] {f: α → β}

@[simp] def build: List (TracedProgram f → TracedProgram f) → TracedProgram f
| [] => .exit
| p::ps => p (build ps)

@[simp] def setv (dst: Source) (b: Bool): TracedProgram f → TracedProgram f := op (.vop (λ _ ↦ b) dst finZeroElim)
@[simp] def setm (dst: Source) (src: Memory): TracedProgram f  → TracedProgram f := op (.const dst src)
@[simp] def copyv (dst src: Source): TracedProgram f  → TracedProgram f := op (.vop (λ f ↦ f 0) dst (λ (_: Fin 1) ↦ src))
@[simp] def copy (dst src: Source): TracedProgram f  → TracedProgram f := op (.mop .COPY dst src)
@[simp] def move (dst src: Source): TracedProgram f  → TracedProgram f := op (.mop .MOVE dst src)
@[simp] def swap (dst src: Source): TracedProgram f  → TracedProgram f := op (.mop .SWAP dst src)
@[simp] def ifv (src: Source) (pos: List (TracedProgram f  → TracedProgram f)) (neg: List (TracedProgram f  → TracedProgram f)): TracedProgram f := branch (.ifTrue (λ f ↦ f 0) (λ (_: Fin 1) ↦ src)) (build pos) (build neg)

@[match_pattern] def subroutine' (dst src: Source) {γ: Type _} (_hγ: Complexity.Encoding γ Memory) {δ: Type _} (_hδ: Complexity.Encoding δ Memory)
    (func: γ → δ) (_h: Computable Encoding.Model func) (next: TracedProgram f): TracedProgram f :=
  subroutine dst src func next

def toProgram: TracedProgram f → Program
| exit => .exit
| op inst next => .op inst next.toProgram
| branch inst pos neg => .branch inst pos.toProgram neg.toProgram
| subroutine' dst src _ _ func _ next => .subroutine dst src (Encoding.getProgram func) next.toProgram
| recurse dst src next => .recurse dst src next.toProgram

inductive Step (α: Type _) [Complexity.Encoding α Memory]
| exit
| op (inst: OpInstruction)
| branch (inst: BranchInstruction)
| subroutine (dst src: Source) {γ: Type _} [Complexity.Encoding γ Memory] {δ: Type _} [Complexity.Encoding δ Memory]
  (func: γ → δ) [Computable Encoding.Model func] (arg: γ)
| recurse (dst src: Source) (arg: α)

def foldrInternal {θ: Type _} (tp: TracedProgram f) (m: Memory) (acc: θ) (g: Step α → Memory → θ → θ): Option θ :=
  match tp with
  | exit => some (g .exit m acc)
  | op inst next => (next.foldrInternal (inst.apply m) acc g).map (g (.op inst) m)
  | branch inst pos neg =>
    if (inst.apply m)
    then ((pos.foldrInternal m acc g).map (g (.branch inst) m))
    else ((neg.foldrInternal m acc g).map (g (.branch inst) m))
  | subroutine' dst src _ _ func _ next =>
    (Complexity.decode _ (m.getms src)).bind
    (λ arg ↦ ((next.foldrInternal (m.setms dst (Complexity.encode (func arg))) acc g).map (g (.subroutine dst src func arg) m)))
  | recurse dst src next =>
    (Complexity.decode _ (m.getms src)).bind
    (λ arg ↦ (next.foldrInternal (m.setms dst (Complexity.encode (f arg))) acc g).map (g (.recurse dst src arg) m))

@[simp] def foldr (tp: TracedProgram f) (a: α): θ → (Step α → Memory → θ → θ) → Option θ :=
  foldrInternal tp (Complexity.encode a)

def Forall (tp: TracedProgram f) (P: α → Step α → Memory → Prop): Prop :=
  ∀ a, foldr tp a True (λ s m b ↦ P a s m ∧ b) = some True

def descendsOp (size: α → ℕ) (a: α): Step α → Memory → Prop
| .recurse _ _ arg, _ => size arg < size a
| _, _ => True

def descends (tp: TracedProgram f): (α → ℕ) → Prop := tp.Forall ∘ descendsOp

def argsMatchOp (_: α): Step α → Memory → Prop
| @Step.subroutine _ _ _ src _ _ _ _ _ _ arg, m => Complexity.encode arg = m.getms src
| .recurse _ src arg, m => Complexity.encode arg = m.getms src
| _, _ => True

def argsMatch (tp: TracedProgram f): Prop := tp.Forall argsMatchOp

def resultOp: Step α → Memory → Memory → Memory
| .exit, m, _ => m
| _, _, m => m

@[simp] def result (tp: TracedProgram f) (a: α): Option Memory := tp.foldr a 0 resultOp

def resultMatches (tp: TracedProgram f): Prop := ∀ a, tp.result a = some (Complexity.encode (f a))

def sound (tp: TracedProgram f) (size: α → ℕ): Prop := ∀ a,
  foldr tp a True (λ s m b ↦ argsMatchOp a s m ∧ b) = some True ∧
  foldr tp a True (λ s m b ↦ descendsOp size a s m ∧ b) = some True ∧
  tp.result a = some (Complexity.encode (f a))

@[simp] theorem argsMatches_op:
    (foldrInternal (.op (f := f) inst next) m True (λ s m b ↦ argsMatchOp a s m ∧ b) = some True) =
    (foldrInternal next (inst.apply m) True (λ s m b ↦ argsMatchOp a s m ∧ b) = some True) :=
  iff_iff_eq.mp ⟨
    λ h ↦ (Option.map_eq_some'.mp h).elim λ _ h ↦
      h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right)),
    λ h ↦ Option.map_eq_some'.mpr ⟨_, h, true_and True⟩ ⟩

@[simp] theorem argsMatches_descend:
    (foldrInternal (.op (f := f) inst next) m True (λ s m b ↦ descendsOp size a s m ∧ b) = some True) =
    (foldrInternal next (inst.apply m) True (λ s m b ↦ descendsOp size a s m ∧ b) = some True) :=
  iff_iff_eq.mp ⟨
    λ h ↦ (Option.map_eq_some'.mp h).elim λ _ h ↦
      h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right)),
    λ h ↦ Option.map_eq_some'.mpr ⟨_, h, true_and True⟩ ⟩

@[simp] theorem resultMatches_descend:
    (foldrInternal (.op (f := f) inst next) m 0 (λ s m b ↦ resultOp s m b) = some res) =
    (foldrInternal next (inst.apply m) 0 (λ s m b ↦ resultOp s m b) = some res) :=
  iff_iff_eq.mp ⟨
    λ h ↦ (Option.map_eq_some'.mp h).elim λ _ h ↦
      h.left.trans (congrArg _ h.right),
    λ h ↦ Option.map_eq_some'.mpr ⟨_, h, rfl⟩ ⟩

@[simp] theorem argsMatches_exit:
    foldrInternal (.exit (f := f)) m True (λ s m b ↦ argsMatchOp a s m ∧ b) = some True :=
  congrArg some (true_and True)

@[simp] theorem descendsOp_exit:
    foldrInternal (.exit (f := f)) m True (λ s m b ↦ descendsOp size a s m ∧ b) = some True :=
  congrArg some (true_and True)

@[simp] theorem resultMatches_exit:
    (foldrInternal (.exit (f := f)) m 0 (λ s m b ↦ resultOp s m b) = some res) =
    (m = res) := iff_iff_eq.mp ⟨ Option.some.inj, congrArg _ ⟩

theorem matchesThunkResultBelow
    {size: α → ℕ}
    {a: α}
    {tp: TracedProgram f}:
    {current: TracedProgram f} →
    {m: Memory} →
    (hs: current.foldrInternal m True (λ s m b ↦ argsMatchOp a s m ∧ b) = some True) →
    (hd: current.foldrInternal m True (λ s m b ↦ descendsOp size a s m ∧ b) = some True) →
    (hr: current.foldrInternal m 0 resultOp = some (Complexity.encode (f a))) →
    (ih: ∀ arg, size arg < size a →
      tp.toProgram.hasResult (Complexity.encode arg) (Complexity.encode (f arg))) →
    Stack.hasResult (.execution ⟨m, current.toProgram, tp.toProgram⟩ []) (Complexity.encode (f a))
| .exit, _, _, _, hr, _ => ⟨1, congrArg Stack.result (Option.some.inj hr)⟩
| .op _ _, _, hs, hd, hr, ih => Stack.hasResult_of_step (matchesThunkResultBelow
    ((Option.map_eq_some'.mp hs).elim λ _ h ↦ h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right)))
    ((Option.map_eq_some'.mp hd).elim λ _ h ↦ h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right)))
    ((Option.map_eq_some'.mp hr).elim λ _ h ↦ h.left.trans (congrArg _ h.right))
    ih)
| .branch inst _ _, m, hs, hd, hr, ih =>
  dite (inst.apply m)
    (λ hb ↦ (eq_iff_iff.mp (congrFun (Stack.hasResult_branch_pos hb) _)).mpr
        (matchesThunkResultBelow
          ((Option.map_eq_some'.mp ((if_pos hb).symm.trans hs)).elim λ _ h ↦ h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right)))
          ((Option.map_eq_some'.mp ((if_pos hb).symm.trans hd)).elim λ _ h ↦ h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right)))
          ((Option.map_eq_some'.mp ((if_pos hb).symm.trans hr)).elim λ _ h ↦ h.left.trans (congrArg _ h.right))
          ih))
    (λ hb ↦ (eq_iff_iff.mp (congrFun (Stack.hasResult_branch_neg (Bool.eq_false_of_not_eq_true hb)) _)).mpr
        (matchesThunkResultBelow
          ((Option.map_eq_some'.mp ((if_neg hb).symm.trans hs)).elim λ _ h ↦ h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right)))
          ((Option.map_eq_some'.mp ((if_neg hb).symm.trans hd)).elim λ _ h ↦ h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right)))
          ((Option.map_eq_some'.mp ((if_neg hb).symm.trans hr)).elim λ _ h ↦ h.left.trans (congrArg _ h.right))
          ih))
| subroutine' _ _ _ _ _ comp _, _, hs, hd, hr, ih =>
    (Option.bind_eq_some'.mp hs).elim λ _ harg ↦
    (Option.map_eq_some'.mp harg.right).elim λ _ hs ↦
    Stack.hasResult_subroutine
      ((of_eq_true hs.right).left ▸ comp.has_result _)
      (matchesThunkResultBelow
        (hs.left.trans (congrArg _ (eq_true (of_eq_true hs.right).right)))
        ((Option.map_eq_some'.mp ((congrArg₂ Option.bind harg.left.symm rfl).trans hd)).elim λ _ h ↦ h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right)))
        ((Option.map_eq_some'.mp ((congrArg₂ Option.bind harg.left.symm rfl).trans hr)).elim λ _ h ↦ h.left.trans (congrArg _ h.right))
      ih)
| .recurse _ _ _, _, hs, hd, hr, ih =>
    (Option.bind_eq_some'.mp hs).elim λ _ harg ↦
    (Option.map_eq_some'.mp harg.right).elim λ _ hs ↦
    (Option.map_eq_some'.mp ((congrArg₂ Option.bind harg.left.symm rfl).trans hd)).elim λ _ hd ↦ (Stack.hasResult_recurse
      ((of_eq_true hs.right).left ▸ ih _ (of_eq_true hd.right).left)
      (matchesThunkResultBelow
        (hs.left.trans (congrArg _ (eq_true (of_eq_true hs.right).right)))
        (hd.left.trans (congrArg _ (eq_true (of_eq_true hd.right).right)))
        ((Option.map_eq_some'.mp ((congrArg₂ Option.bind harg.left.symm rfl).trans hr)).elim λ _ h ↦ h.left.trans (congrArg _ h.right))
        ih))

theorem hasResult (tp: TracedProgram f) {size: α → ℕ} (hs: tp.argsMatch) (hd: tp.descends size) (hr: tp.resultMatches) (n: ℕ):
    ∀ a, n = size a → tp.toProgram.hasResult (Complexity.encode a) (Complexity.encode (f a)) :=
  n.strong_induction_on λ _ ih _ ha ↦
    matchesThunkResultBelow (hs _) (hd _) (hr _)
      (λ _ hlt ↦ ih _ (ha ▸ hlt) _ rfl)

class HasTrace (f: α → β) where
  program: List (TracedProgram f → TracedProgram f)
  size: α → ℕ
  sound: (build program).sound size

instance [tr: HasTrace f]: Computable Encoding.Model f where
  program := (build tr.program).toProgram
  has_result _ := hasResult _ (λ _ ↦ (tr.sound _).left) (λ _ ↦ (tr.sound _).right.left) (λ _ ↦ (tr.sound _).right.right) _ _ rfl

end TracedProgram
end Complexity
end HMem
