import Complexity.Basic
import Complexity.Cost

namespace Complexity
def Asymptotic (α: Type _): Type _ := Quotient (CostFunction.asymptotic α)

namespace Asymptotic

def O  (f: CostFunction α ℕ): Asymptotic α := ⟦f⟧

instance: PartialOrder (Asymptotic α) where
  le := Quotient.lift₂ (CostFunction.ALE) (λ _ _ _ _ ha hb ↦
    eq_iff_iff.mpr ⟨
      λ h ↦ Trans.trans ha.right (Trans.trans h hb.left),
      λ h ↦ Trans.trans  ha.left (Trans.trans h hb.right) ⟩)
  le_refl a := Quotient.out_eq a ▸ refl (r := CostFunction.ALE) _
  le_trans a b c := Quotient.out_eq a ▸ Quotient.out_eq b ▸ Quotient.out_eq c ▸ Trans.trans (r := CostFunction.ALE) (s := CostFunction.ALE)
  le_antisymm a b := by exact Quotient.out_eq a ▸ Quotient.out_eq b ▸ λ hab hbc ↦ Quotient.sound (s := CostFunction.asymptotic α) (And.intro hab hbc)

instance: Add (Asymptotic α) where
  add := Quotient.lift₂ (λ a b ↦ ⟦a + b⟧) (
    λ _ _ _ _ ha hb ↦ Quotient.sound ⟨
      CostFunction.add_ale_add ha.left hb.left,
      CostFunction.add_ale_add ha.right hb.right ⟩)

instance: Mul (Asymptotic α) where
  mul := Quotient.lift₂ (λ x y ↦ ⟦CostFunction.mul' x y⟧) (
    λ _ _ _ _ hx hy ↦ Quotient.sound ⟨
      CostFunction.mul'_ale_mul' hx.left hy.left,
      CostFunction.mul'_ale_mul' hx.right hy.right⟩)


def flatMap (f: α → Option β): Asymptotic β → Asymptotic α :=
  Quotient.lift (λ x ↦ ⟦ x.flatMap f ⟧) ( λ _ _ h ↦ Quotient.sound ⟨
      CostFunction.flatMap_ale_flatMap h.left _,
      CostFunction.flatMap_ale_flatMap h.right _⟩)
end Asymptotic
end Complexity

section
open Complexity.Asymptotic

structure AsymptoticComplexity {α: Type _} {β: Type _} (m: Complexity.Model) [Complexity.Encoding α m.Data] [Complexity.Encoding β m.Result] (f: α → β) (cost: Complexity.CostFunction α ℕ) where
  computable: Computable m f
  cost_le a: O computable.cost ≤ O (cost a)

end
