import Complexity.Cost

namespace Complexity
structure ALE (x y: CostFunction α ℕ) where
  m: ℕ
  k: ℕ
  ale: x ≤ m * y + k

notation:50 f " ∈ O(" g ")" => ALE f g

def ale_of_le {x y: CostFunction α ℕ} (h: x ≤ y): x ∈ O(y) := ⟨1, 0, le_of_le_of_eq h (one_mul _).symm⟩

namespace ALE

variable {x y z: CostFunction α ℕ}

def bound (h: x ∈ O(y)): CostFunction α ℕ := h.m * y + h.k

theorem le_bound (h: x ∈ O(y)): x ≤ h.bound := h.ale

def refl: x ∈ O(x) := ale_of_le (le_refl _)

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

def ale_of_le_of_ale (hxy: x ≤ y) (hyz: y ∈ O(z)): x ∈ O(z) := trans (ale_of_le hxy) hyz

def add_ale (hxz: x ∈ O(z)) (hyz: y ∈ O(z)): x + y ∈ O(z) where
  m := hxz.m + hyz.m
  k := hxz.k + hyz.k
  ale :=
    le_of_le_of_eq (add_le_add hxz.ale hyz.ale)
      (add_left_comm (hyz.m * z) _ _ ▸
      add_assoc (hxz.m * z) _ _ ▸
      add_assoc (hyz.m * z) _ _ ▸
      add_comm (hyz.m * z) _ ▸
      right_distrib _ _ z ▸
      CostFunction.const_add_const _ _ ▸
      rfl)

def const_ale (n: ℕ) (f: CostFunction α ℕ): n ∈ O(f) where
  m := 0
  k := n
  ale := le_add_left (le_refl _)


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

-- theorem flatMap_ale_flatMap {x y: CostFunction β ℕ} (h: x ≤≤ y) (f: α → Option β):
--     x.flatMap f ≤≤ y.flatMap f := h.imp λ k hk a ↦
--   match ha:f a with
--   | none => flatMap_none ha x ▸ Nat.zero_le _
--   | some _ => by simpa [add_def, mul_def, flatMap_some ha x, flatMap_some ha y] using hk _
end Complexity
