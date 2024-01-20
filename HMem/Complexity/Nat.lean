import HMem.Complexity.Def

@[simp] theorem encode_zero: Complexity.encode (0:ℕ) = (0:HMem.Memory) := rfl
attribute [simp] bit0 bit1
@[simp] theorem one_div_two: 1 / 2 = 0 := rfl
@[simp] theorem size_bit1: Nat.size (2 * n + 1) = Nat.size n + 1 :=
  (congrArg _ (Nat.bit_val true _).symm).trans
  (Nat.binaryRec_eq' _ _ (Or.inr λ _ ↦ rfl))
@[simp] theorem add_one_add_one: n + 1 + 1 = n + 2 := rfl

theorem Nat.log_mul (hb: 1 < b) (hn: 1 ≤ n): Nat.log b (b * n) = Nat.log b n + 1 := by
  apply le_antisymm
  apply le_of_eq_of_le
  apply Nat.log_of_one_lt_of_le hb
  apply le_of_eq_of_le
  apply (mul_one _).symm
  apply mul_le_mul (le_refl _) hn (zero_le _) (zero_le _)
  apply Nat.succ_le_succ
  apply Nat.log_mono_right
  apply le_of_eq
  rw [Nat.mul_div_right _ (lt_trans zero_lt_one hb)]
  apply Nat.le_log_of_pow_le hb
  rw [Nat.pow_succ, mul_comm]
  apply mul_le_mul
  apply le_refl
  apply Nat.pow_log_le_self
  apply ne_of_lt' (Nat.lt_of_succ_le hn)
  apply zero_le
  apply zero_le

theorem Nat.log_mul_add (hb: 1 < b) (hn: 1 ≤ n) (hc: c < b): Nat.log b (b * n + c) = Nat.log b n + 1 := by
  apply le_antisymm
  apply le_of_eq_of_le
  apply Nat.log_of_one_lt_of_le hb
  apply add_le_add _ (zero_le _)
  apply le_of_eq_of_le
  apply (mul_one _).symm
  apply mul_le_mul (le_refl _) hn (zero_le _) (zero_le _)
  apply Nat.succ_le_succ
  apply Nat.log_mono_right
  apply le_of_eq
  apply Eq.trans
  apply Nat.mul_add_div (lt_trans zero_lt_one hb)
  apply congrArg _ (Nat.div_eq_of_lt hc)
  apply le_trans
  rw [← Nat.log_mul hb hn]
  apply Nat.log_mono_right
  apply le_add_right

theorem Nat.size_le_succ_log: size n ≤ (log 2 n) + 1 := by
  refine binaryRec' (n := n) ?hz ?hi
  exact zero_le _
  intro b n hb ih
  cases n
  cases b <;> simp
  rw [size_bit, bit_val, Nat.log_mul_add]
  apply Nat.succ_le_succ ih
  apply one_lt_two
  apply Nat.succ_le_succ (zero_le _)
  cases b <;> simp
  cases b <;> simp

namespace HMem.Complexity.Nat

instance: Program.HasCost (λ n ↦ n / 2) 1 where
  program := [ .move 0 2 ]
  size _ := 0
  sound n := by simp [Encoding.encode_nat_def (n := n)]
  cost_ale := Program.nonRecursiveComplexity (Complexity.ALE.const_ale _ _)

instance: Program.HasCost (λ n ↦ n % 2) 1 where
  program := [
    .copyv 0 1,
    .setm 2 0
  ]
  size _ := 0
  sound n := by simp [Encoding.encode_nat_def (n := n), (Encoding.encode_nat_def (n := n % 2))]
  cost_ale := Program.nonRecursiveComplexity (Complexity.ALE.const_ale _ _)

instance: Program.HasCost (λ n ↦ decide (n ≠ 0)) 1 where
  program := [
    .setm 1 0,
    .setm 2 0
  ]
  size _ := 0
  sound n := by simp [Encoding.encode_nat_def (n := n)]
  cost_ale := Program.nonRecursiveComplexity (Complexity.ALE.const_ale _ _)

instance: Program.HasCost Nat.succ (Nat.log 2) where
  program := [
    .ifv 1 [
      .setv 1 false,
      .recurse 2 2
    ],
    .setv 1 true,
    .setv 0 true
  ]
  size := Nat.size
  sound := Nat.binaryRec' rfl λ b ↦
      by cases b <;> simp [← Nat.two_mul, Nat.mul_add_mod, Nat.mul_add_div]
  cost_ale := Complexity.ALE.trans
    (Program.simpleLoopComplexity (Complexity.ALE.const_ale _ _) rfl)
    ⟨_, _, λ _ ↦ le_of_le_of_eq Nat.size_le_succ_log (congrArg₂ _ (one_mul _).symm rfl) ⟩

def Nat.AddWithCarry (x y: ℕ) (c: Bool): ℕ := x + y + Bool.toNat c

-- instance: Program.HasCost ↿Nat.AddWithCarry (λ | (x, y, _) => Nat.log 2 (x + y)) where
--   program := []
--   size | (x, y, _) => Nat.size x + Nat.size y
--   sound | (_, _, _) => sorry
--   cost_ale := sorry


end HMem.Complexity.Nat
