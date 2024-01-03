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
  (func: γ → δ) [Computable Encoding.Model func] (γ: arg)
| recurse (dst src: Source) (arg: α)

def foldlInternal {θ: Type _} (tp: TracedProgram f) (m: Memory) (g: θ → Step α → Memory → θ) (acc: θ): Option θ :=
  match tp with
  | exit => some (g acc .exit m)
  | op inst next => next.foldlInternal (inst.apply m) g (g acc (.op inst) m)
  | branch inst pos neg => match inst.apply m with
    | true => pos.foldlInternal m g (g acc (.branch inst) m)
    | false => neg.foldlInternal m g (g acc (.branch inst) m)
  | subroutine' dst src _ _ func _ next =>
    (Complexity.decode _ (m.getms src)).bind
    (λ arg ↦ next.foldlInternal (m.setms dst (Complexity.encode (func arg))) g (g acc (.subroutine dst src func arg) m))
  | recurse dst src next =>
    (Complexity.decode _ (m.getms src)).bind
    (λ arg ↦ next.foldlInternal (m.setms dst (Complexity.encode (f arg))) g (g acc (.recurse dst src arg) m))

def foldl (tp: TracedProgram f) (a: α): (θ → Step α → Memory → θ) → θ → Option θ :=
  foldlInternal tp (Complexity.encode a)

def Forall (tp: TracedProgram f) (P: α → Step α → Memory → Prop): Prop :=
  ∀ a, foldl tp a (λ b s m ↦ b ∧ P a s m) True = some True

def descends (tp: TracedProgram f) (size: α → ℕ): Prop := tp.Forall
  (λ | a, .recurse _ _ arg, _ => size arg < size a | _, _, _ => true)

def sound (tp: TracedProgram f): Prop := ∀ a, tp.foldl a (λ v _ _ ↦ v) () = some ()

-- theorem fold_sound (tp: TracedProgram f) (a: α) (g: θ → TracedProgram f → Memory → θ) (v: θ) (h: tp.sound):
--     Option.isSome (tp.foldl a g v) := by
--   unfold foldl



-- def soundInternal: TracedProgram f → (α → ℕ) → Memory → α → ℕ → Prop
-- | .exit, _, m, a, _ => m = Complexity.encode (f a)
-- | .op inst next, size, m, a, n => next.soundInternal size (inst.apply m) a n
-- | .branch inst pos neg, size, m, a, n =>
--   match inst.apply m with
--   | true => pos.soundInternal size m a n
--   | false => neg.soundInternal size m a n
-- | .subroutine' dst src _ _ func _ next, size, m, a, n =>
--   ∃ x, some x = Complexity.decode _ (m.getms src) ∧
--     next.soundInternal size (m.setms dst (Complexity.encode (func x))) a n
-- | .recurse dst src next, size, m, a, n =>
--   ∃ x, some x = Complexity.decode _ (m.getms src) ∧
--     next.soundInternal size (m.setms dst (Complexity.encode (f x))) a n

-- def sound (tp: TracedProgram f) (size: α → ℕ): Prop := ∀ a, tp.soundInternal size (Complexity.encode a) a (size a)




end TracedProgram

end Complexity
end HMem
