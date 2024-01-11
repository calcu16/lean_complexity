import Complexity.Cost

namespace Complexity
open CostFunction

def Asymptotic (α: Type _): Type _ := Quotient (CostFunction.asymptotic α)

instance: Membership (CostFunction α ℕ) (Asymptotic α) where
  mem cf o := ∃ (k: ℕ), cf ≤ k * o.out + k

def O  (f: CostFunction α ℕ): Asymptotic α := ⟦f⟧

namespace Asymptotic

def out_ale (f: CostFunction α ℕ): (O f).out ≤≤ f := (Quotient.exact ((Quotient.out_eq (O _)))).left
def ale_out (f: CostFunction α ℕ): f ≤≤ (O f).out := (Quotient.exact ((Quotient.out_eq (O _)))).right
theorem mem_self (f: CostFunction α ℕ): f ∈ O f :=
  And.right (Quotient.exact ((Quotient.out_eq (O _))))

def mem_def {f: CostFunction α ℕ} {g: Asymptotic α}: f ∈ g → f ≤≤ g.out := id
def mem_mk {f g: CostFunction α ℕ} (h: f ∈ O g): f ≤≤ g := Trans.trans (mem_def h) (out_ale _)

noncomputable def k_of_mem {f: CostFunction α ℕ} {g: Asymptotic α} (h: f ∈ g): ℕ := Classical.choose h
noncomputable def k_of_mk (f: CostFunction α ℕ): ℕ := Classical.choose (out_ale f)
noncomputable def k_of_mk' (f: CostFunction α ℕ): ℕ := Classical.choose (ale_out f)
noncomputable def k_of_mem_mk {f g: CostFunction α ℕ} (h: f ∈ O g): ℕ := Classical.choose (mem_mk h)

theorem k_of_mem_sound {f: CostFunction α ℕ} {g: Asymptotic α} (h: f ∈ g): f ≤ (k_of_mem h * g.out) + (k_of_mem h) := Classical.choose_spec h
theorem k_of_mk_sound (f: CostFunction α ℕ): (O f).out ≤ (k_of_mk f * f) + (k_of_mk f) :=
  Classical.choose_spec (out_ale f)
theorem k_of_mk'_sound (f: CostFunction α ℕ): f ≤ (k_of_mk' f * (O f).out) + (k_of_mk' f) :=
  Classical.choose_spec (ale_out f)
theorem k_of_mem_mk'_sound {f g: CostFunction α ℕ} (h: f ∈ O g): f ≤ (k_of_mem_mk h * g) + (k_of_mem_mk h) :=
  Classical.choose_spec (mem_mk h)

instance: PartialOrder (Asymptotic α) where
  le := Quotient.lift₂ (CostFunction.ALE) (λ _ _ _ _ ha hb ↦
    eq_iff_iff.mpr ⟨
      λ h ↦ Trans.trans ha.right (Trans.trans h hb.left),
      λ h ↦ Trans.trans  ha.left (Trans.trans h hb.right) ⟩)
  le_refl a := Quotient.out_eq a ▸ refl (r := CostFunction.ALE) _
  le_trans a b c := Quotient.out_eq a ▸ Quotient.out_eq b ▸ Quotient.out_eq c ▸ Trans.trans (r := CostFunction.ALE) (s := CostFunction.ALE)
  le_antisymm a b := by exact Quotient.out_eq a ▸ Quotient.out_eq b ▸ λ hab hbc ↦ Quotient.sound (s := CostFunction.asymptotic α) (And.intro hab hbc)

theorem o1_le (g: Asymptotic α): O 1 ≤ g := flip le_of_le_of_eq (Quotient.out_eq g) ⟨_, λ _ ↦ (Nat.le_add_left _ _)⟩

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
