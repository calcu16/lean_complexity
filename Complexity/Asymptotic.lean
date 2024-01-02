-- import Complexity.Basic

-- namespace Complexity



-- structure CostedModel extends Model where
--   -- Cost: Type
--   -- [cost_add: CanonicallyOrderedAddCommMonoid Cost]
--   -- [cost_one: One Cost]
--   cost' {p: Program} {d: Data}: (∃ r, has_result p d r) → ℕ

-- def CostFunction (m: CostedModel) (α: Type _) [Encoding α m.Data]: Type _ := α → ℕ

-- def CostedModel.cost (m: CostedModel) (p: m.Program) (α: Type _) [Encoding α m.Data] (h: m.totalProgram p α): CostFunction m α :=
--   λ a ↦ m.cost' (h a)

-- -- instance (m: CostedModel): CanonicallyOrderedAddCommMonoid m.Cost := m.cost_add
-- -- instance (m: CostedModel): One m.Cost := m.cost_one

-- -- def Cost.scalar_mul (m: CostedModel): ℕ → m.Cost → m.Cost
-- -- | 0, _ => 0
-- -- | n+1, c => Cost.scalar_mul m n c + c

-- -- instance (m: CostedModel): HMul ℕ m.Cost m.Cost := ⟨ Cost.scalar_mul m ⟩
-- -- instance (m: CostedModel): Coe ℕ m.Cost := ⟨ λ n ↦ n * (One.one:m.Cost) ⟩

-- namespace CostFunction

-- variable {m: CostedModel} {α: Type _} [en: Encoding α m.Data]

-- instance {n: ℕ}: OfNat (CostFunction m α) n where
--   ofNat _ := n

-- instance: NatCast (CostFunction m α) where
--   natCast n := λ _ ↦ n

-- instance [Inhabited α]: NeZero (1:CostFunction m α) where
--   out h := one_ne_zero' ℕ (congrFun h default)

-- instance: LE (CostFunction m α) where
--   le x y := ∀ a, x a ≤ y a

-- instance: CanonicallyOrderedAddCommMonoid (CostFunction m α) where
--   le_refl _ _ := le_refl _
--   le_antisymm _ _ hab hba := funext λ _ ↦ le_antisymm (hab _) (hba _)
--   le_trans _ _ _ hab hbc _ := le_trans (hab _) (hbc _)
--   bot := 0
--   bot_le _ _ := bot_le
--   add x y a := (x a) + (y a)
--   zero_add _ := funext λ _ ↦ zero_add _
--   add_zero _ := funext λ _ ↦ add_zero _
--   add_comm _ _ := funext λ _ ↦ add_comm _ _
--   add_assoc _ _ _ := funext λ _ ↦ add_assoc _ _ _
--   add_le_add_left _ _ h _ _ := add_le_add_left (h _) _
--   exists_add_of_le h := ⟨ _, funext λ _ ↦ (Nat.sub_add_cancel (h _)).symm.trans (Nat.add_comm _ _)  ⟩
--   le_self_add _ _ _ := le_self_add

-- instance: OrderedCommSemiring (CostFunction m α) where
--   zero_le_one _ := zero_le_one
--   mul x y a := (x a) * (y a)
--   mul_zero _ := funext λ _ ↦ mul_zero _
--   zero_mul _ := funext λ _ ↦ zero_mul _
--   mul_one _ := funext λ _ ↦ mul_one _
--   one_mul _ := funext λ _ ↦ one_mul _
--   mul_comm _ _ := funext λ _ ↦ mul_comm _ _
--   mul_assoc _ _ _ := funext λ _ ↦ mul_assoc _ _ _
--   left_distrib _ _ _ := funext λ _ ↦ left_distrib _ _ _
--   right_distrib _ _ _  := funext λ _ ↦ right_distrib _ _ _
--   add_le_add_left _ _ h _ _ := add_le_add_left (h _) _
--   mul_le_mul_of_nonneg_left _ _ _ hab hpos _ := mul_le_mul_of_nonneg_left (hab _) (hpos _)
--   mul_le_mul_of_nonneg_right _ _ _ hab hpos _ := mul_le_mul_of_nonneg_right (hab _) (hpos _)

-- instance: OrderedCancelAddCommMonoid (CostFunction m α) where
--   le_of_add_le_add_left _ _ _ h _ := le_of_add_le_add_left (h _)

-- theorem add_def {x y: CostFunction m α}: (x + y) a = x a + y a := rfl
-- theorem mul_def {x y: CostFunction m α}: (x * y) a = x a * y a := rfl
-- theorem mul_pos {x y: CostFunction m α} (hx: 1 ≤ x) (hy: 1 ≤ y): 1 ≤ x * y := λ _ ↦ Nat.mul_pos (hx _) (hy _)
-- theorem le_mul_of_pos_right {x y: CostFunction m α} (hy: 1 ≤ y): x ≤ x * y := λ _ ↦ Nat.le_mul_of_pos_right (hy _)

-- theorem natZero_mul (x: CostFunction m α): (0:ℕ) * x = 0 := funext λ _ ↦ zero_mul _
-- theorem natOne_mul (x: CostFunction m α): (1:ℕ) * x = x := funext λ _ ↦ one_mul _
-- theorem const_add_const (a b: ℕ): ((a + b:ℕ):CostFunction m α) = (a:CostFunction m α) + b := funext λ _ ↦ rfl
-- theorem const_mul_const (a b: ℕ): ((a * b:ℕ):CostFunction m α) = (a:CostFunction m α) * b := funext λ _ ↦ rfl

-- def mul' (x y: CostFunction m α): CostFunction m α := (x + 1) * (y + 1)

-- theorem mul'_le_mul' {a x b y: CostFunction m α} (hax: a ≤ x) (hby: b ≤ y): mul' a b ≤ mul' x y :=
--   mul_le_mul (add_le_add_right hax _) (add_le_add_right hby _) (zero_le _) (zero_le _)

-- def ALE (x y: CostFunction m α): Prop := ∃ (k: ℕ), x ≤ k * y + k

-- local infix:50 " ≤≤ "  => ALE

-- theorem ale_of_le {x y: CostFunction m α} (h: x ≤ y): x ≤≤ y := ⟨_, le_add_right (le_of_le_of_eq h (one_mul _).symm)⟩

-- instance : IsPreorder (CostFunction m α) (. ≤≤ .) where
--   refl _ :=  ⟨_, le_add_right (le_of_eq (one_mul _).symm) ⟩
--   trans _ _ _ hab hbc := hab.elim (hbc.elim λ k₁ h₁ k₀ h₀ ↦
--     ⟨ k₀ * k₁ + k₀,
--       h₀.trans (const_add_const (m := m) (α := α) (k₀ * k₁) k₀ ▸ add_assoc (G := CostFunction m α) _ _ _ ▸
--         (add_le_add_right (const_mul_const (m := m) (α := α) k₀ k₁ ▸
--         mul_add_one (α := CostFunction m α) k₀ k₁ ▸
--         mul_assoc (G := CostFunction m α) k₀ _ _ ▸
--         left_distrib (R := CostFunction m α) k₀ _ k₁ ▸
--           mul_le_mul_of_nonneg_left
--             (h₁.trans (add_le_add_right
--               (mul_le_mul_of_nonneg_right (le_add_right (le_refl _))
--               (zero_le _)) _))
--             (zero_le _)) _))⟩)

-- theorem add_ale_add {a x b y: CostFunction m α} (hax: a ≤≤ x) (hby: b ≤≤ y): a + b ≤≤ x + y := by
--   apply hax.elim
--   apply hby.elim
--   intro k₁ h₁ k₀ h₀
--   refine ⟨ k₀ + k₁, ?hha ⟩
--   refine const_add_const (m := m) (α := α) k₀ k₁ ▸ ?hhb
--   refine add_assoc (G := CostFunction m α) _ _ _ ▸ ?hhc
--   refine left_distrib (R := CostFunction m α)  _ _ _ ▸ ?hhd
--   refine add_right_comm (G := CostFunction m α) _ k₀ _ ▸ ?hhe
--   refine add_assoc (G := CostFunction m α) _ _ _ ▸ ?hhf
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

-- theorem mul_le_mul' {a x: CostFunction m α}: a * x ≤ mul' a x :=
--   mul_le_mul (le_add_right (le_refl _)) (le_add_right (le_refl _)) (zero_le _) (zero_le _)

-- theorem mul'_ale_mul' {a x b y: CostFunction m α} (hax: a ≤≤ x) (hby: b ≤≤ y): mul' a b ≤≤ mul' x y := by
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

-- theorem mul_ale_mul_of_const_left {a b: CostFunction m α} (h: a ≤≤ b): (n: ℕ) → (n:CostFunction m α) * a ≤≤ (n:CostFunction m α) * b
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

-- instance asymptotic (m: CostedModel) (α: Type _) [Encoding α m.Data]: Setoid (CostFunction m α) where
--   r x y := x ≤≤ y ∧ y ≤≤ x
--   iseqv.refl _ := ⟨ refl _, refl _ ⟩
--   iseqv.symm h := ⟨h.right, h.left⟩
--   iseqv.trans hxy hyz := ⟨ Trans.trans hxy.left hyz.left, Trans.trans hyz.right hxy.right ⟩

-- def flatMap (f: α → Option β) [Encoding β m.Data] (g: CostFunction m β): CostFunction m α := λ a ↦
--   match f a with
--   | none => 0
--   | some b => g b

-- theorem flatMap_none {f: α → Option β} [Encoding β m.Data] {a: α} (h: f a = none) (g: CostFunction m β):
--   (g.flatMap f) a = 0 := by simp[flatMap, h]

-- theorem flatMap_some {f: α → Option β} [Encoding β m.Data] {a: α} {b: β} (h: f a = some b) (g: CostFunction m β):
--   (g.flatMap f) a = g b := by simp[flatMap, h]


-- theorem flatMap_le_flatMap [Encoding β m.Data] {x y: CostFunction m β} (h: x ≤ y) (f: α → Option β):
--     x.flatMap f ≤ y.flatMap f := λ a ↦
--   match ha:f a with
--   | none => flatMap_none ha x ▸ Nat.zero_le _
--   | some _ => flatMap_some ha x ▸ flatMap_some ha y ▸ h _

-- theorem flatMap_ale_flatMap [Encoding β m.Data] {x y: CostFunction m β} (h: x ≤≤ y) (f: α → Option β):
--     x.flatMap f ≤≤ y.flatMap f := h.imp λ k hk a ↦
--   match ha:f a with
--   | none => flatMap_none ha x ▸ Nat.zero_le _
--   | some _ => by simpa [add_def, mul_def, flatMap_some ha x, flatMap_some ha y] using hk _

-- end CostFunction

-- def Asymptotic (m: CostedModel) (α: Type _) [Encoding α m.Data]: Type _ := Quotient (CostFunction.asymptotic m α)

-- namespace Asymptotic

-- variable {m: CostedModel} {α: Type _} [en: Encoding α m.Data]

-- def O(f: CostFunction m α): Asymptotic m α := ⟦f⟧

-- instance: PartialOrder (Asymptotic m α) where
--   le := Quotient.lift₂ (CostFunction.ALE) (λ _ _ _ _ ha hb ↦
--     eq_iff_iff.mpr ⟨
--       λ h ↦ Trans.trans ha.right (Trans.trans h hb.left),
--       λ h ↦ Trans.trans  ha.left (Trans.trans h hb.right) ⟩)
--   le_refl a := Quotient.out_eq a ▸ refl (r := CostFunction.ALE) _
--   le_trans a b c := Quotient.out_eq a ▸ Quotient.out_eq b ▸ Quotient.out_eq c ▸ Trans.trans (r := CostFunction.ALE) (s := CostFunction.ALE)
--   le_antisymm a b := by exact Quotient.out_eq a ▸ Quotient.out_eq b ▸ λ hab hbc ↦ Quotient.sound (s := @CostFunction.asymptotic m α en) (And.intro hab hbc)

-- instance: Add (Asymptotic m α) where
--   add := Quotient.lift₂ (λ a b ↦ ⟦a + b⟧) (
--     λ _ _ _ _ ha hb ↦ Quotient.sound ⟨
--       CostFunction.add_ale_add ha.left hb.left,
--       CostFunction.add_ale_add ha.right hb.right ⟩)

-- instance: Mul (Asymptotic m α) where
--   mul := Quotient.lift₂ (λ x y ↦ ⟦CostFunction.mul' x y⟧) (
--     λ _ _ _ _ hx hy ↦ Quotient.sound ⟨
--       CostFunction.mul'_ale_mul' hx.left hy.left,
--       CostFunction.mul'_ale_mul' hx.right hy.right⟩)


-- def flatMap (f: α → Option β) [Encoding β m.Data]: Asymptotic m β → Asymptotic m α :=
--   Quotient.lift (λ x ↦ ⟦ x.flatMap f ⟧) ( λ _ _ h ↦ Quotient.sound ⟨
--       CostFunction.flatMap_ale_flatMap h.left _,
--       CostFunction.flatMap_ale_flatMap h.right _⟩)
-- end Asymptotic
-- end Complexity

-- section
-- open Complexity.Asymptotic

-- def Computable.cost {α: Type _} {β: Type _} (m: Complexity.CostedModel) [Complexity.Encoding α m.Data] [Complexity.Encoding β m.Result]
--     (f: α → β) [h: Computable m.toModel f]: Complexity.CostFunction m α :=
--   m.cost h.program α λ _ ↦ ⟨_, h.has_result _⟩

-- structure AsymptoticComplexity {α: Type _} {β: Type _} (m: Complexity.CostedModel) [Complexity.Encoding α m.Data] [Complexity.Encoding β m.Result] (f: α → β) (cost: Complexity.CostFunction m α) where
--   computable: Computable m.toModel f
--   cost_le a: O computable.cost ≤ O (cost a)

-- end
