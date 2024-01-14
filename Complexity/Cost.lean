import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Tactic

namespace Complexity
def CostFunction (α: Type _) (β: Type): Type _ := α → β

-- instance (m: CostedModel): CanonicallyOrderedAddCommMonoid m.Cost := m.cost_add
-- instance (m: CostedModel): One m.Cost := m.cost_one

-- def Cost.scalar_mul (m: CostedModel): ℕ → m.Cost → m.Cost
-- | 0, _ => 0
-- | n+1, c => Cost.scalar_mul m n c + c

-- instance (m: CostedModel): HMul ℕ m.Cost m.Cost := ⟨ Cost.scalar_mul m ⟩
-- instance (m: CostedModel): Coe ℕ m.Cost := ⟨ λ n ↦ n * (One.one:m.Cost) ⟩

namespace CostFunction

variable {α: Type _}

instance {n: ℕ}: OfNat (CostFunction α ℕ) n where
  ofNat _ := n

instance: NatCast (CostFunction α ℕ) where
  natCast n := λ _ ↦ n

instance [Inhabited α]: NeZero (1:CostFunction α ℕ) where
  out h := one_ne_zero' ℕ (congrFun h default)

instance: LE (CostFunction α ℕ) where
  le x y := ∀ a, x a ≤ y a

instance: CanonicallyOrderedAddCommMonoid (CostFunction α ℕ) where
  le_refl _ _ := le_refl _
  le_antisymm _ _ hab hba := funext λ _ ↦ le_antisymm (hab _) (hba _)
  le_trans _ _ _ hab hbc _ := le_trans (hab _) (hbc _)
  bot := 0
  bot_le _ _ := bot_le
  add x y a := (x a) + (y a)
  zero_add _ := funext λ _ ↦ zero_add _
  add_zero _ := funext λ _ ↦ add_zero _
  add_comm _ _ := funext λ _ ↦ add_comm _ _
  add_assoc _ _ _ := funext λ _ ↦ add_assoc _ _ _
  add_le_add_left _ _ h _ _ := add_le_add_left (h _) _
  exists_add_of_le h := ⟨ _, funext λ _ ↦ (Nat.sub_add_cancel (h _)).symm.trans (Nat.add_comm _ _)  ⟩
  le_self_add _ _ _ := le_self_add

instance: OrderedCommSemiring (CostFunction α ℕ) where
  zero_le_one _ := zero_le_one
  mul x y a := (x a) * (y a)
  mul_zero _ := funext λ _ ↦ mul_zero _
  zero_mul _ := funext λ _ ↦ zero_mul _
  mul_one _ := funext λ _ ↦ mul_one _
  one_mul _ := funext λ _ ↦ one_mul _
  mul_comm _ _ := funext λ _ ↦ mul_comm _ _
  mul_assoc _ _ _ := funext λ _ ↦ mul_assoc _ _ _
  left_distrib _ _ _ := funext λ _ ↦ left_distrib _ _ _
  right_distrib _ _ _  := funext λ _ ↦ right_distrib _ _ _
  add_le_add_left _ _ h _ _ := add_le_add_left (h _) _
  mul_le_mul_of_nonneg_left _ _ _ hab hpos _ := mul_le_mul_of_nonneg_left (hab _) (hpos _)
  mul_le_mul_of_nonneg_right _ _ _ hab hpos _ := mul_le_mul_of_nonneg_right (hab _) (hpos _)

instance: OrderedCancelAddCommMonoid (CostFunction α ℕ) where
  le_of_add_le_add_left _ _ _ h _ := le_of_add_le_add_left (h _)

theorem add_def {x y: CostFunction α ℕ}: (x + y) a = x a + y a := rfl
theorem mul_def {x y: CostFunction α ℕ}: (x * y) a = x a * y a := rfl
theorem mul_pos {x y: CostFunction α ℕ} (hx: 1 ≤ x) (hy: 1 ≤ y): 1 ≤ x * y := λ _ ↦ Nat.mul_pos (hx _) (hy _)
theorem le_mul_of_pos_right {x y: CostFunction α ℕ} (hy: 1 ≤ y): x ≤ x * y := λ _ ↦ Nat.le_mul_of_pos_right (hy _)

theorem natZero_mul (x: CostFunction α ℕ): (0:ℕ) * x = 0 := funext λ _ ↦ zero_mul _
theorem natOne_mul (x: CostFunction α ℕ): (1:ℕ) * x = x := funext λ _ ↦ one_mul _
theorem const_add_const (a b: ℕ): ((a + b:ℕ):CostFunction α ℕ) = (a:CostFunction α ℕ) + b := funext λ _ ↦ rfl
theorem const_mul_const (a b: ℕ): ((a * b:ℕ):CostFunction α ℕ) = (a:CostFunction α ℕ) * b := funext λ _ ↦ rfl

def mul' (x y: CostFunction α ℕ): CostFunction α ℕ := (x + 1) * (y + 1)

theorem mul'_le_mul' {a x b y: CostFunction α ℕ} (hax: a ≤ x) (hby: b ≤ y): mul' a b ≤ mul' x y :=
  mul_le_mul (add_le_add_right hax _) (add_le_add_right hby _) (zero_le _) (zero_le _)

end CostFunction

structure ALE (x y: CostFunction α ℕ) where
  m: ℕ
  k: ℕ
  ale: x ≤ m * y + k

infix:50 " ≲ " => ALE

def ale_of_le {x y: CostFunction α ℕ} (h: x ≤ y): x ≲ y := ⟨1, 0, le_of_le_of_eq h (one_mul _).symm⟩

namespace ALE

variable {x y z: CostFunction α ℕ}

def bound (h: x ≲ y): CostFunction α ℕ := h.m * y + h.k

theorem le_bound (h: x ≲ y): x ≤ h.bound := h.ale

def refl: x ≲ x := ale_of_le (le_refl _)

def trans (hxy: x ≲ y) (hyz: y ≲ z): x ≲ z where
  m := hxy.m * hyz.m
  k := hxy.m * hyz.k + hxy.k
  ale := le_trans hxy.le_bound
    (le_of_le_of_eq (add_le_add (le_of_le_of_eq
      (mul_le_mul (le_refl _) hyz.le_bound (zero_le _) (zero_le _))
      ((left_distrib _ _ _).trans
        (congrArg₂ _ (mul_assoc _ _ _).symm rfl)))
      (le_refl _))
      (add_assoc _ _ _))

end ALE


-- instance : IsPreorder (CostFunction α ℕ) (. ≤≤ .) where
--   refl _ :=  ⟨_, le_add_right (le_of_eq (one_mul _).symm) ⟩
--   trans _ _ _ hab hbc := hab.elim (hbc.elim λ k₁ h₁ k₀ h₀ ↦
--     ⟨ k₀ * k₁ + k₀,
--       h₀.trans (const_add_const (α := α) (k₀ * k₁) k₀ ▸ add_assoc (G := CostFunction α ℕ) _ _ _ ▸
--         (add_le_add_right (const_mul_const (α := α) k₀ k₁ ▸
--         mul_add_one (α := CostFunction α ℕ) k₀ k₁ ▸
--         mul_assoc (G := CostFunction α ℕ) k₀ _ _ ▸
--         left_distrib (R := CostFunction α ℕ) k₀ _ k₁ ▸
--           mul_le_mul_of_nonneg_left
--             (h₁.trans (add_le_add_right
--               (mul_le_mul_of_nonneg_right (le_add_right (le_refl _))
--               (zero_le _)) _))
--             (zero_le _)) _))⟩)

-- theorem add_ale_add {a x b y: CostFunction α ℕ} (hax: a ≤≤ x) (hby: b ≤≤ y): a + b ≤≤ x + y := by
--   apply hax.elim
--   apply hby.elim
--   intro k₁ h₁ k₀ h₀
--   refine ⟨ k₀ + k₁, ?hha ⟩
--   refine const_add_const (α := α) k₀ k₁ ▸ ?hhb
--   refine add_assoc (G := CostFunction α ℕ) _ _ _ ▸ ?hhc
--   refine left_distrib (R := CostFunction α ℕ)  _ _ _ ▸ ?hhd
--   refine add_right_comm (G := CostFunction α ℕ) _ k₀ _ ▸ ?hhe
--   refine add_assoc (G := CostFunction α ℕ) _ _ _ ▸ ?hhf
--   apply add_le_add
--   apply le_trans h₀
--   apply add_le_add_right
--   apply mul_le_mul_of_nonneg_right
--   apply le_add_right
--   apply le_refl
--   apply zero_le
--   apply le_trans h₁
--   apply add_le_add_right
--   apply mul_le_mul_of_nonneg_right
--   apply le_add_left
--   apply le_refl
--   apply zero_le

-- theorem mul_le_mul' {a x: CostFunction α ℕ}: a * x ≤ mul' a x :=
--   mul_le_mul (le_add_right (le_refl _)) (le_add_right (le_refl _)) (zero_le _) (zero_le _)

-- theorem mul'_ale_mul' {a x b y: CostFunction α ℕ} (hax: a ≤≤ x) (hby: b ≤≤ y): mul' a b ≤≤ mul' x y := by
--   apply hax.elim
--   apply hby.elim
--   intro k₁ h₁ k₀ h₀
--   use (k₁ + 1) * (k₀ + 1)
--   apply le_trans
--   apply mul'_le_mul'
--   apply h₀
--   apply h₁
--   unfold mul'
--   simp [add_def, mul_def]
--   ring_nf
--   simp [add_assoc]
--   apply add_le_add
--   apply one_le_two
--   apply add_le_add
--   apply le_mul_of_pos_right
--   apply one_le_two
--   apply add_le_add_left
--   apply add_le_add_left
--   apply add_le_add_left
--   apply le_add_left
--   apply add_le_add
--   apply le_mul_of_pos_right
--   apply one_le_two
--   apply add_le_add_left
--   apply le_add_left
--   apply le_add_left
--   apply le_add_left
--   apply le_add_left
--   apply le_add_left
--   apply add_le_add
--   apply le_mul_of_pos_right
--   apply one_le_two
--   apply le_add_right
--   apply le_refl _

-- theorem mul_ale_mul_of_const_left {a b: CostFunction α ℕ} (h: a ≤≤ b): (n: ℕ) → (n:CostFunction α ℕ) * a ≤≤ (n:CostFunction α ℕ) * b
-- | 0 => natZero_mul a ▸ natZero_mul b ▸ refl _
-- | n+1 => by
--   apply h.elim
--   intro k h
--   refine ⟨ n * k + k, ?hha⟩
--   apply le_trans
--   apply mul_le_mul_of_nonneg_left h (zero_le _)
--   simp
--   ring_nf
--   apply add_le_add_right
--   apply add_le_add_right
--   apply le_add_right
--   apply add_le_add_left
--   intro
--   rw [mul_def (y := 2)]
--   apply Nat.le_mul_of_pos_right
--   apply Nat.zero_lt_succ

-- instance asymptotic (α: Type _): Setoid (CostFunction α ℕ) where
--   r x y := x ≤≤ y ∧ y ≤≤ x
--   iseqv.refl _ := ⟨ refl _, refl _ ⟩
--   iseqv.symm h := ⟨h.right, h.left⟩
--   iseqv.trans hxy hyz := ⟨ Trans.trans hxy.left hyz.left, Trans.trans hyz.right hxy.right ⟩

namespace CostFunction
def flatMap (f: α → Option β) (g: CostFunction β ℕ): CostFunction α ℕ := λ a ↦
  match f a with
  | none => 0
  | some b => g b

theorem flatMap_none {f: α → Option β} {a: α} (h: f a = none) (g: CostFunction β ℕ):
  (g.flatMap f) a = 0 := by simp[flatMap, h]

theorem flatMap_some {f: α → Option β} {a: α} {b: β} (h: f a = some b) (g: CostFunction β ℕ):
  (g.flatMap f) a = g b := by simp[flatMap, h]

theorem flatMap_le_const {g: CostFunction β ℕ} (h: ∀ b, g b ≤ n) (f: α → Option β):
    g.flatMap f ≤ n := λ a ↦
  match ha:f a with
  | some _ => le_of_eq_of_le (flatMap_some ha _) (h _)
  | none => le_of_eq_of_le (flatMap_none ha _) (zero_le _)

theorem nat_flatMap_le_nat (n: ℕ) (f: α → Option β):
    (n:CostFunction β ℕ).flatMap f ≤ n := flatMap_le_const (λ _ ↦ le_refl _) _

theorem flatMap_le_flatMap {x y: CostFunction β ℕ} (h: x ≤ y) (f: α → Option β):
    x.flatMap f ≤ y.flatMap f := λ a ↦
  match ha:f a with
  | none => flatMap_none ha x ▸ Nat.zero_le _
  | some _ => flatMap_some ha x ▸ flatMap_some ha y ▸ h _

-- theorem flatMap_ale_flatMap {x y: CostFunction β ℕ} (h: x ≤≤ y) (f: α → Option β):
--     x.flatMap f ≤≤ y.flatMap f := h.imp λ k hk a ↦
--   match ha:f a with
--   | none => flatMap_none ha x ▸ Nat.zero_le _
--   | some _ => by simpa [add_def, mul_def, flatMap_some ha x, flatMap_some ha y] using hk _
end CostFunction
end Complexity
