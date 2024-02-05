import Lib
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Tactic

/-!
This file defines Complexity.CostFunction and various operations on it.

And represents the cost of some operation on α.
Ideally a CostFunction would have a [CanonicallyOrderedLatticeCommSemiring θ]
but that is not required in this file.

## TODO:

Consider filling in the path to CanonicallyOrderedLatticeCommSemiring more granularly.

Notions of powers and logs may be useful for calculations in the future.
-/

namespace Complexity
/--
A CostFunction is just a thin wrapper around a function from (α → θ).

We could consider making this a type, but its nice to be able to call it like a normal function.
-/
def CostFunction (α: Type _) (θ: Type _): Type _ := α → θ

namespace CostFunction

variable {α: Type _} {β: Type _} {θ: Type _}

/-- A convience Coe that represents a constant cost -/
instance: Coe θ (CostFunction α θ) where
  coe b _ := b

instance [Zero θ]: Zero (CostFunction α θ) := ⟨ ↑(0:θ) ⟩
instance [One θ]: One (CostFunction α θ) := ⟨ ↑(1:θ) ⟩

instance [Inhabited α] [Zero θ] [One θ] [NeZero (1:θ)]: NeZero (1:CostFunction α θ) where
  out h := one_ne_zero (congrFun h default)

/--
A cost function is ≤ if it is ≤ everywhere.

This has some implications:
- Total orders now becomes partial orders. F.x. ![1, 0] and ![0, 1] are incomparable despite 0 ≤ 1
- The implied < is ≤ everywhere and < somewhere, not < everywhere.
  In particular this means that even if [PosMulStrictMono θ] the cost function may not be becuase
  0 < ![1, 0] and 0 < ![0, 1] but the implied inner product is ![0, 0].
-/
instance [LE θ]: LE (CostFunction α θ) where
  le x y := ∀ a, x a ≤ y a

instance [Add θ]: Add (CostFunction α θ) where
  add x y a := x a + y a
theorem add_def [Add θ] {x y: CostFunction α θ}: (x + y) a = x a + y a := rfl
theorem const_add_const [Add θ](a b: θ): ((a + b:θ):CostFunction α θ) = (a:CostFunction α θ) + (b:CostFunction α θ) := funext λ _ ↦ rfl

instance [AddCommMonoid β]: AddCommMonoid (CostFunction α β) where
  zero_add _ := funext λ _ ↦ zero_add _
  add_zero _ := funext λ _ ↦ add_zero _
  add_comm _ _ := funext λ _ ↦ add_comm _ _
  add_assoc _ _ _ := funext λ _ ↦ add_assoc _ _ _

instance [Mul θ]: Mul (CostFunction α θ) where
  mul x y a := x a * y a
theorem const_mul_const [Mul θ] (a b: θ): ((a * b:θ):CostFunction α θ) = (a:CostFunction α θ) * (b:CostFunction α θ) := funext λ _ ↦ rfl
theorem mul_def [Mul θ] {x y: CostFunction α θ}: (x * y) a = x a * y a := rfl

instance [CommSemiring θ]: CommSemiring (CostFunction α θ) where
  one_mul _ := funext λ _ ↦ one_mul _
  mul_one _ := funext λ _ ↦ mul_one _
  mul_comm _ _ := funext λ _ ↦ mul_comm _ _
  mul_assoc _ _ _ := funext λ _ ↦ mul_assoc _ _ _
  mul_zero _ := funext λ _ ↦ mul_zero _
  zero_mul _ := funext λ _ ↦ zero_mul _
  left_distrib _ _ _ := funext λ _ ↦ left_distrib _ _ _
  right_distrib _ _ _  := funext λ _ ↦ right_distrib _ _ _

instance [CommSemiring θ]: NatCast (CostFunction α θ) where
  natCast n _ := n

instance [Preorder θ]: Preorder (CostFunction α θ) where
  le_refl _ _ := le_refl _
  le_trans _ _ _ hab hbc _ := le_trans (hab _) (hbc _)
class Monotone [Preorder α] [Preorder θ] (cf: CostFunction α θ) where
  mono {a b: α}: a ≤ b → cf a ≤ cf b
def monotone [Preorder α] [Preorder θ] (cf: CostFunction α θ) [h: Monotone cf] {a b: α}: a ≤ b → cf a ≤ cf b := h.mono

instance [PartialOrder θ]: PartialOrder (CostFunction α θ) where
  le_antisymm _ _ hab hba := funext λ _ ↦ le_antisymm (hab _) (hba _)

instance [LE θ] [OrderBot θ]: OrderBot (CostFunction α θ) where
  bot _ := ⊥
  bot_le _ _ := bot_le

instance [OrderedAddCommMonoid θ]: OrderedAddCommMonoid (CostFunction α θ) where
  add_le_add_left _ _ h _ _ := add_le_add_left (h _) _
/-- We can use use this instead of 0 < a if we need to show mul_pos. -/
class Positive [OrderedAddCommMonoid θ] (cf: CostFunction α θ) where
  positive a: 0 < cf a
def positive [OrderedAddCommMonoid θ] (cf: CostFunction α θ) [h: Positive cf]: (a: α) → 0 < cf a := h.positive

instance [CanonicallyOrderedAddCommMonoid θ]: CanonicallyOrderedAddCommMonoid (CostFunction α θ) where
  exists_add_of_le h := ⟨ _, funext λ _ ↦ Classical.choose_spec (exists_add_of_le (h _)) ⟩
  le_self_add _ _ _ := le_self_add
/-- If Monotone generalizes a positive first derivative,
then MonotoneConcaveUp generalizes a notion of a positive first and second derivative -/
class MonotoneConcaveUp [CanonicallyOrderedAddCommMonoid α] [CanonicallyOrderedAddCommMonoid θ] (cf: CostFunction α θ) extends Monotone cf where
  concave {a b c: α} (hab: a ≤ b) (hbc: b ≤ c) (hac: distance hab ≤ distance hbc):
    distance (monotone cf hab) ≤ distance (monotone cf hbc)
def monotoneConcaveUp [CanonicallyOrderedAddCommMonoid α] [CanonicallyOrderedAddCommMonoid θ] (cf: CostFunction α θ) [h: MonotoneConcaveUp cf]:
    {a b c: α} → (hab: a ≤ b) → (hbc: b ≤ c) → (hac: distance hab ≤ distance hbc) →
    distance (monotone cf hab) ≤ distance (monotone cf hbc) :=
  h.concave

instance [OrderedCommSemiring θ]: OrderedCommSemiring (CostFunction α θ) where
  zero_le_one _ := zero_le_one
  mul_comm _ _ := funext λ _ ↦ mul_comm _ _
  add_le_add_left _ _ h _ _ := add_le_add_left (h _) _
  mul_le_mul_of_nonneg_left _ _ _ hab hpos _ := mul_le_mul_of_nonneg_left (hab _) (hpos _)
  mul_le_mul_of_nonneg_right _ _ _ hab hpos _ := mul_le_mul_of_nonneg_right (hab _) (hpos _)

instance [OrderedCancelAddCommMonoid θ]: OrderedCancelAddCommMonoid (CostFunction α θ) where
  add_le_add_left _ _ h _ _ := add_le_add_left (h _) _
  le_of_add_le_add_left _ _ _ h _ := le_of_add_le_add_left (h _)

instance [Lattice θ]: Lattice (CostFunction α θ) where
  sup x y a := x a ⊔ y a
  inf x y a := x a ⊓ y a
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ hac hbc _ := sup_le (hac _) (hbc _)
  inf_le_left _ _ _ := inf_le_left
  inf_le_right _ _ _ := inf_le_right
  le_inf _ _ _ hab hac _ := le_inf (hab _) (hac _)

theorem sup_def [Lattice θ] {x y: CostFunction α θ}: (x ⊔ y) a = x a ⊔ y a := rfl
theorem inf_def [Lattice θ]  {x y: CostFunction α θ}: (x ⊓ y) a = x a ⊓ y a := rfl
theorem const_sup_const [Lattice θ] (a b: θ): ((a ⊔ b:θ):CostFunction α θ) = (a:CostFunction α θ) ⊔ (b:CostFunction α θ) := funext λ _ ↦ rfl
theorem const_inf_const [Lattice θ] (a b: θ): ((a ⊓ b:θ):CostFunction α θ) = (a:CostFunction α θ) ⊓ (b:CostFunction α θ) := funext λ _ ↦ rfl

def add_eq_sup [CanonicallyOrderedLatticeAddCommMonoid θ] {x y: CostFunction α θ} (h: ∀ a, x a = 0 ∨ y a = 0): x + y = x ⊔ y :=
  funext λ a ↦ (h a).elim
    (λ h ↦ ((congrArg₂ _ h rfl).trans (zero_add (y a))).trans ((congrArg₂ _ h rfl).trans (zero_sup (y a))).symm)
    (λ h ↦ ((congrArg₂ _ rfl h).trans (add_zero (x a))).trans ((congrArg₂ _ rfl h).trans (sup_zero (x a))).symm)

/-- Maps over a partial function sending None to 0 -/
def flatMap [Zero θ] (f: α → Option β) (g: CostFunction β θ): CostFunction α θ := λ a ↦
  match f a with
  | none => 0
  | some b => g b

theorem flatMap_none [Zero θ] {f: α → Option β} {a: α} (h: f a = none) (g: CostFunction β θ):
  (g.flatMap f) a = 0 := by simp[flatMap, h]

theorem flatMap_some [Zero θ] {f: α → Option β} {a: α} {b: β} (h: f a = some b) (g: CostFunction β θ):
  (g.flatMap f) a = g b := by simp[flatMap, h]


@[simp] theorem flatMap_some' [Zero θ] {g: CostFunction β θ}:
  flatMap Option.some g = g := rfl

@[simp] theorem flatMap_lambda_some [Zero θ] {f: α → β} {g: CostFunction β θ}:
  flatMap (λ a ↦ Option.some (f a)) g = g ∘ f := rfl

theorem flatMap_le_apply [CanonicallyOrderedAddCommMonoid θ] {f: α → Option β} {g: CostFunction β θ} {g': CostFunction α θ} {a: α}
    (h: ∀ b ∈ f a, g b ≤ g' a): (g.flatMap f) a ≤ g' a :=
  match ha: f a with
  | some _ => le_of_eq_of_le (flatMap_some ha _) (h _ ha)
  | none => le_of_eq_of_le (flatMap_none ha _) (zero_le _)

theorem flatMap_le_const [CanonicallyOrderedAddCommMonoid θ] {g: CostFunction β θ} (h: ∀ b, g b ≤ n) (f: α → Option β):
    g.flatMap f ≤ n := λ a ↦
  match ha:f a with
  | some _ => le_of_eq_of_le (flatMap_some ha _) (h _)
  | none => le_of_eq_of_le (flatMap_none ha _) (zero_le _)

theorem const_flatMap_le_const [CanonicallyOrderedAddCommMonoid θ] (n: θ) (f: α → Option β):
    flatMap f (n:CostFunction β θ) ≤ n := flatMap_le_const (λ _ ↦ le_refl _) _

theorem flatMap_le_flatMap [Zero θ] [Preorder θ] {x y: CostFunction β θ} (h: x ≤ y) (f: α → Option β):
    x.flatMap f ≤ y.flatMap f := λ a ↦
  match ha:f a with
  | none => flatMap_none ha x ▸ flatMap_none ha y ▸ le_refl _
  | some _ => flatMap_some ha x ▸ flatMap_some ha y ▸ h _


end CostFunction
end Complexity
