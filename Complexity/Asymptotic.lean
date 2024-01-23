import Complexity.Cost

/-!
Asymptotics on CostFunctions, defined in a computable manner.

This uses that offset constant multiple definition rather than the limit definition,
  f ∈ O(g) ↔ ∃ m k, ∀ a, f a ≤ m * g a + k
but instead of ∃ we keep around m and k.

By avoiding the limit/filter definition, we don't need to know anything about α.

Because these are intended to be computable, these are defined as Types and not Props.

## TODO

Flesh out θ(f) and o(f)
--/

namespace Complexity
/-
Asymptotically Less than or Equal (ALE)

A constant multiple and an offset of y that is always greater than x.
-/
structure ALE [CanonicallyOrderedLatticeCommSemiring θ] (x y: CostFunction α θ) where
  m: θ
  k: θ
  ale: x ≤ ↑m * y + ↑k

notation:50 f " ∈ O(" g ")" => ALE f g

namespace ALE
variable {α: Type _} {θ: Type _}
variable {x y z: CostFunction α θ} [CanonicallyOrderedLatticeCommSemiring θ]

def of_le {x y: CostFunction α θ} (h: x ≤ y): x ∈ O(y) := ⟨1, 0, le_of_le_of_eq h ((add_zero _).trans (one_mul _)).symm⟩

/- A bounding offset multiple of y that is greater than x -/
def bound (h: x ∈ O(y)): CostFunction α θ := ↑h.m * y + ↑h.k

theorem le_bound (h: x ∈ O(y)): x ≤ h.bound := h.ale

theorem le_zero_bound (h: x ∈ O(0)): x ≤ h.k :=
  le_of_le_of_eq h.le_bound ((congrArg₂ _ (mul_zero _) rfl).trans (zero_add _))

def refl: x ∈ O(x) := of_le (le_refl _)

def trans (hxy: x ∈ O(y)) (hyz: y ∈ O(z)): x ∈ O(z) where
  m := hxy.m * hyz.m
  k := hxy.m * hyz.k + hxy.k
  ale := le_trans hxy.le_bound
    (le_of_le_of_eq (add_le_add (le_of_le_of_eq
      (mul_le_mul (le_refl _) hyz.le_bound (zero_le _) (zero_le _))
      ((left_distrib _ _ _).trans
        (congrArg₂ _ (mul_assoc _ _ _).symm rfl)))
      (le_refl _))
      (add_assoc _ _ _))

def of_le_of_ale (hxy: x ≤ y) (hyz: y ∈ O(z)): x ∈ O(z) := trans (of_le hxy) hyz

def add_ale_sup: x + y ∈ O(x ⊔ y) where
  m := 2
  k := 0
  ale _ := le_of_le_of_eq
    (add_le_add le_sup_left le_sup_right)
    ((add_zero _).trans (two_mul _)).symm

def sup_ale_add: x ⊔ y ∈ O(x + y) where
  m := 1
  k := 0
  ale _ := le_of_le_of_eq
    (sup_le (le_add_right (le_refl _)) (le_add_left (le_refl _)))
    ((add_zero _).trans (one_mul _)).symm

def add_ale (hxz: x ∈ O(z)) (hyz: y ∈ O(z)): x + y ∈ O(z) where
  m := hxz.m + hyz.m
  k := hxz.k + hyz.k
  ale :=
    le_of_le_of_eq (add_le_add hxz.ale hyz.ale)
      (add_left_comm (↑hyz.m * z) _ _ ▸
      add_assoc (↑hxz.m * z) _ _ ▸
      add_assoc (↑hyz.m * z) _ _ ▸
      add_comm (↑hyz.m * z) _ ▸
      right_distrib _ _ z ▸
      CostFunction.const_add_const (hxz.k) (hyz.k) ▸
      rfl)

def ale_add_left (h: x ∈ O(z)): x ∈ O(y + z) where
  m := h.m
  k := h.k
  ale := le_trans
    h.ale
    (add_le_add_right
      (mul_le_mul
        (le_refl _)
        (le_add_left (le_refl _))
        (zero_le _)
        (zero_le _)) _)

def ale_add_right (h: x ∈ O(y)): x ∈ O(y + z) where
  m := h.m
  k := h.k
  ale := le_trans
    h.ale
    (add_le_add_right
      (mul_le_mul
        (le_refl _)
        (le_add_right (le_refl _))
        (zero_le _)
        (zero_le _)) _)

section -- TODO: tighten
def add_ale_add (h₀: a ∈ O(b)) (h₁: x ∈ O(y)): a + x ∈ O(b + y) :=
  add_ale (ale_add_right h₀) (ale_add_left h₁)

def sup_ale_sup (h₀: a ∈ O(b)) (h₁: x ∈ O(y)): a ⊔ x ∈ O(b ⊔ y) :=
  (sup_ale_add.trans (add_ale_add h₀ h₁)).trans add_ale_sup
end

def const_ale (n: θ) (f: CostFunction α θ): n ∈ O(f) where
  m := 0
  k := n
  ale := le_add_left (le_refl _)

def bound_ale_self (h: x ∈ O(y)): h.bound ∈ O(y) := ⟨_, _, le_refl _⟩

def bound_ale_trans (hy: x ∈ O(y)) (hz: y ∈ O(z)): hy.bound ∈ O(z) := trans (bound_ale_self _) hz

def flatMap_ale_flatMap {x y: CostFunction β θ} (h: x ∈ O(y)) (f: α → Option β):
    x.flatMap f ∈ O(y.flatMap f) where
  m := h.m
  k := h.k
  ale a :=
    match ha:f a with
    | none => CostFunction.flatMap_none ha x ▸ zero_le _
    | some _ => by simpa [CostFunction.add_def, CostFunction.mul_def, CostFunction.flatMap_some ha x, CostFunction.flatMap_some ha y] using h.ale _

end ALE

/-
Asymptotically EQual to (AEQ)

Arrived at by antisymmetry
-/
structure AEQ [CanonicallyOrderedLatticeCommSemiring θ] (x y: CostFunction α θ): Type _ where
  le: x ∈ O(y)
  ge: y ∈ O(x)

notation:50 f " ∈ θ(" g ")" => AEQ f g

/-
Asymptotically Less Than (ALT)

For all offset multipls of x, this computes an (a: α) such that (y a) is greater than the bound.
-/
structure ALT [CanonicallyOrderedLatticeCommSemiring θ] (x y: CostFunction α θ): Type _ where
  le: x ∈ O(y)
  a: θ → θ → α
  gt (m k: θ): y (a m k) > (↑m * x + ↑k) (a m k)

notation:50 f " ∈ o(" g ")" => ALT f g

end Complexity
