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
@[simp] def ifv (src: Source): List (TracedProgram f  → TracedProgram f) → TracedProgram f → TracedProgram f := branch (.ifTrue (λ f ↦ f 0) (λ (_: Fin 1) ↦ src)) ∘ build

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

@[simp] theorem descend_op:
    (foldrInternal (.op (f := f) inst next) m True (λ s m b ↦ descendsOp size a s m ∧ b) = some True) =
    (foldrInternal next (inst.apply m) True (λ s m b ↦ descendsOp size a s m ∧ b) = some True) :=
  iff_iff_eq.mp ⟨
    λ h ↦ (Option.map_eq_some'.mp h).elim λ _ h ↦
      h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right)),
    λ h ↦ Option.map_eq_some'.mpr ⟨_, h, true_and True⟩ ⟩

@[simp] theorem resultMatches_op:
    (foldrInternal (.op (f := f) inst next) m 0 (λ s m b ↦ resultOp s m b) = some res) =
    (foldrInternal next (inst.apply m) 0 (λ s m b ↦ resultOp s m b) = some res) :=
  iff_iff_eq.mp ⟨
    λ h ↦ (Option.map_eq_some'.mp h).elim λ _ h ↦
      h.left.trans (congrArg _ h.right),
    λ h ↦ Option.map_eq_some'.mpr ⟨_, h, rfl⟩ ⟩

@[simp] theorem argsMatches_branch:
    (foldrInternal (.branch (f := f) inst pos neg) m True (λ s m b ↦ argsMatchOp a s m ∧ b) = some True) =
    ( inst.apply m = true ∧ foldrInternal pos m True (λ s m b ↦ argsMatchOp a s m ∧ b) = some True ∨
      inst.apply m = false ∧ foldrInternal neg m True (λ s m b ↦ argsMatchOp a s m ∧ b) = some True
    ) := iff_iff_eq.mp ⟨
    λ h ↦ (em (inst.apply m)).imp
      (λ hm ↦ ⟨hm, (Option.map_eq_some'.mp ((if_pos hm).symm.trans h)).elim λ _ h ↦
        h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right))⟩)
      λ hm ↦ ⟨(eq_false_of_ne_true hm), (Option.map_eq_some'.mp ((if_neg hm).symm.trans h)).elim λ _ h ↦
        h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right))⟩,
    λ h ↦ h.elim
      (λ h ↦ (if_pos h.left).trans
        (Option.map_eq_some'.mpr ⟨ _, h.right, and_true _ ⟩))
      (λ h ↦ (if_neg (ne_true_of_eq_false h.left)).trans
        (Option.map_eq_some'.mpr ⟨ _, h.right, and_true _ ⟩))⟩

@[simp] theorem resultMatches_branch:
    (foldrInternal (.branch (f := f) inst pos neg) m 0 (λ s m b ↦ resultOp s m b) = some res) =
    ( inst.apply m = true ∧ foldrInternal pos m 0 (λ s m b ↦ resultOp s m b) = some res ∨
      inst.apply m = false ∧ foldrInternal neg m 0 (λ s m b ↦ resultOp s m b) = some res
    ) := iff_iff_eq.mp ⟨
    λ h ↦ (em (inst.apply m)).imp
      (λ hm ↦ ⟨hm, (Option.map_eq_some'.mp ((if_pos hm).symm.trans h)).elim λ _ h ↦
        h.left.trans (congrArg _ h.right)⟩)
      λ hm ↦ ⟨(eq_false_of_ne_true hm), (Option.map_eq_some'.mp ((if_neg hm).symm.trans h)).elim λ _ h ↦
        h.left.trans (congrArg _ h.right)⟩,
    λ h ↦ h.elim
      (λ h ↦ (if_pos h.left).trans
        (Option.map_eq_some'.mpr ⟨ _, h.right, rfl ⟩))
      (λ h ↦ (if_neg (ne_true_of_eq_false h.left)).trans
        (Option.map_eq_some'.mpr ⟨ _, h.right, rfl ⟩))⟩

@[simp] theorem descendsMatches_branch:
    (foldrInternal (.branch (f := f) inst pos neg) m True (λ s m b ↦ descendsOp size a s m ∧ b) = some True) =
    ( inst.apply m = true ∧ foldrInternal pos m True (λ s m b ↦ descendsOp size a s m ∧ b) = some True ∨
      inst.apply m = false ∧ foldrInternal neg m True (λ s m b ↦ descendsOp size a s m ∧ b) = some True
    ) := iff_iff_eq.mp ⟨
    λ h ↦ (em (inst.apply m)).imp
      (λ hm ↦ ⟨hm, (Option.map_eq_some'.mp ((if_pos hm).symm.trans h)).elim λ _ h ↦
        h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right))⟩)
      λ hm ↦ ⟨(eq_false_of_ne_true hm), (Option.map_eq_some'.mp ((if_neg hm).symm.trans h)).elim λ _ h ↦
        h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right))⟩,
    λ h ↦ h.elim
      (λ h ↦ (if_pos h.left).trans
        (Option.map_eq_some'.mpr ⟨ _, h.right, and_true _ ⟩))
      (λ h ↦ (if_neg (ne_true_of_eq_false h.left)).trans
        (Option.map_eq_some'.mpr ⟨ _, h.right, and_true _ ⟩))⟩

@[simp] theorem argsMatches_subroutine
  {γ: Type _} [Complexity.Encoding γ Memory]
  {δ: Type _} [Complexity.Encoding δ Memory]
  {func: γ → δ} [Computable Encoding.Model func]:
    (foldrInternal (.subroutine (f := f) dst src func next) m True (λ s m b ↦ argsMatchOp a s m ∧ b) = some True) =
    (∃ arg,
      Complexity.decode γ (m.getms src) = some arg ∧
      Complexity.encode arg = (m.getms src) ∧
      foldrInternal next (m.setms dst (Complexity.encode (func arg))) True (λ s m b ↦ argsMatchOp a s m ∧ b) = some True) :=
    iff_iff_eq.mp ⟨
      λ h ↦ (Option.bind_eq_some'.mp h).imp λ _ h ↦ ⟨ h.left,
        (Option.map_eq_some'.mp h.right).elim λ _ h ↦ ⟨ (of_eq_true h.right).left,
        h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right)) ⟩ ⟩,
      λ h ↦ Option.bind_eq_some'.mpr (h.imp λ _ h ↦ ⟨h.left, Option.map_eq_some'.mpr ⟨_, h.right.right, eq_true ⟨h.right.left, trivial⟩⟩⟩)⟩

@[simp] theorem descends_subroutine
  {γ: Type _} [Complexity.Encoding γ Memory]
  {δ: Type _} [Complexity.Encoding δ Memory]
  {func: γ → δ} [Computable Encoding.Model func]:
    (foldrInternal (.subroutine (f := f) dst src func next) m True (λ s m b ↦ descendsOp size a s m ∧ b) = some True) =
    (∃ arg,
      Complexity.decode γ (m.getms src) = some arg ∧
      foldrInternal next (m.setms dst (Complexity.encode (func arg))) True (λ s m b ↦ descendsOp size a s m ∧ b) = some True) :=
    iff_iff_eq.mp ⟨
      λ h ↦ (Option.bind_eq_some'.mp h).imp λ _ h ↦ ⟨ h.left,
        (Option.map_eq_some'.mp h.right).elim λ _ h ↦ h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right))⟩,
      λ h ↦ Option.bind_eq_some'.mpr (h.imp λ _ h ↦ ⟨h.left, Option.map_eq_some'.mpr ⟨_, h.right, and_true _⟩⟩)⟩

@[simp] theorem resultMatches_subroutine
  {γ: Type _} [Complexity.Encoding γ Memory]
  {δ: Type _} [Complexity.Encoding δ Memory]
  {func: γ → δ} [Computable Encoding.Model func]:
    (foldrInternal (.subroutine (f := f) dst src func next) m 0 (λ s m b ↦ resultOp s m b) = some res) =
    (∃ arg,
      Complexity.decode γ (m.getms src) = some arg ∧
      foldrInternal next (m.setms dst (Complexity.encode (func arg))) 0 (λ s m b ↦ resultOp s m b) = some res) :=
    iff_iff_eq.mp ⟨
      λ h ↦ (Option.bind_eq_some'.mp h).imp λ _ h ↦ ⟨ h.left,
        (Option.map_eq_some'.mp h.right).elim λ _ h ↦ h.left.trans (congrArg _ h.right)⟩,
      λ h ↦ Option.bind_eq_some'.mpr (h.imp λ _ h ↦ ⟨h.left, Option.map_eq_some'.mpr ⟨_, h.right, rfl⟩⟩)⟩

@[simp] theorem descends_recurse:
    (foldrInternal (.recurse (f := f) dst src next) m True (λ s m b ↦ descendsOp size a s m ∧ b) = some True) =
    (∃ arg,
      Complexity.decode α (m.getms src) = some arg ∧
      size arg < size a ∧
      foldrInternal next (m.setms dst (Complexity.encode (f arg))) True (λ s m b ↦ descendsOp size a s m ∧ b) = some True) :=
    iff_iff_eq.mp ⟨
      λ h ↦ (Option.bind_eq_some'.mp h).imp λ _ h ↦ ⟨ h.left,
        (Option.map_eq_some'.mp h.right).elim λ _ h ↦ ⟨
          (of_eq_true h.right).left,
          h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right))⟩⟩,
      λ h ↦ Option.bind_eq_some'.mpr (h.imp λ _ h ↦ ⟨h.left, Option.map_eq_some'.mpr
        ⟨_, h.right.right, (and_true _).trans (eq_true h.right.left)⟩⟩)⟩

@[simp] theorem argsMatches_recurse:
    (foldrInternal (.recurse (f := f) dst src next) m True (λ s m b ↦ argsMatchOp a s m ∧ b) = some True) =
    (∃ arg,
      Complexity.decode α (m.getms src) = some arg ∧
      Complexity.encode arg = (m.getms src) ∧
      foldrInternal next (m.setms dst (Complexity.encode (f arg))) True (λ s m b ↦ argsMatchOp a s m ∧ b) = some True) :=
    iff_iff_eq.mp ⟨
      λ h ↦ (Option.bind_eq_some'.mp h).imp λ _ h ↦ ⟨ h.left,
        (Option.map_eq_some'.mp h.right).elim λ _ h ↦ ⟨ (of_eq_true h.right).left,
        h.left.trans (congrArg _ (eq_true (of_eq_true h.right).right)) ⟩ ⟩,
      λ h ↦ Option.bind_eq_some'.mpr (h.imp λ _ h ↦ ⟨h.left, Option.map_eq_some'.mpr ⟨_, h.right.right, eq_true ⟨h.right.left, trivial⟩⟩⟩)⟩

@[simp] theorem resultMatches_recurse:
    (foldrInternal (.recurse (f := f) dst src next) m 0 (λ s m b ↦ resultOp s m b) = some res) =
    (∃ arg,
      Complexity.decode α (m.getms src) = some arg ∧
      foldrInternal next (m.setms dst (Complexity.encode (f arg))) 0 (λ s m b ↦ resultOp s m b) = some res) :=
    iff_iff_eq.mp ⟨
      λ h ↦ (Option.bind_eq_some'.mp h).imp λ _ h ↦ ⟨ h.left,
        (Option.map_eq_some'.mp h.right).elim λ _ h ↦ h.left.trans (congrArg _ h.right)⟩,
      λ h ↦ Option.bind_eq_some'.mpr (h.imp λ _ h ↦ ⟨h.left, Option.map_eq_some'.mpr ⟨_, h.right, rfl⟩⟩)⟩

@[simp] theorem argsMatches_exit:
    foldrInternal (.exit (f := f)) m True (λ s m b ↦ argsMatchOp a s m ∧ b) = some True :=
  congrArg some (true_and True)

@[simp] theorem descends_exit:
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

-- def recursiveArgs: TracedProgram f → (α → Option Memory) → List (α → Option α)
-- | .exit, _ => []
-- | .op inst next, fm => recursiveArgs next (Option.map inst.apply ∘ fm)
-- | .branch inst pos neg, fm =>
--   recursiveArgs pos sorry ++ recursiveArgs neg sorry

end TracedProgram

class HasTrace {α: Type _} [Complexity.Encoding α Memory] {β: Type _} [Complexity.Encoding β Memory] (f: α → β) where
  program: List (TracedProgram f → TracedProgram f)
  size: α → ℕ
  sound: (TracedProgram.build program).sound size

instance {α: Type _} [Complexity.Encoding α Memory] {β: Type _} [Complexity.Encoding β Memory] {f: α → β} [tr: HasTrace f]: Computable Encoding.Model f where
  program := (TracedProgram.build tr.program).toProgram
  has_result _ := TracedProgram.hasResult _ (λ _ ↦ (tr.sound _).left) (λ _ ↦ (tr.sound _).right.left) (λ _ ↦ (tr.sound _).right.right) _ _ rfl

end Complexity
end HMem
