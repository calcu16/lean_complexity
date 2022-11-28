import binary_nat
import data.nat.pow
import tactic.linarith

open costed_binary_nat
open complexity

universe u
variables {α : Type u}

theorem zero_cost : Π (n), cost.cost_of (zero n) = n + 1
| 0 := by simp [zero, bit_zero]
| (n+1) := begin
  simp [zero, intro, zero_cost],
  ring,
end

theorem add_with_carry_cost : Π {n}, ∀ {x y : binary_nat n} {z : binary_nat 0},
  cost.cost_of (add_with_carry x y z) = 8 * 2^n - 3
| 0 := begin
  intros x y z,
  cases x,
  all_goals {cases y},
  all_goals {cases z},
  all_goals {simp [add_with_carry]},
end
| (n+1) := begin
  intros x y z,
  cases x with _ xu xl,
  cases y with _ yu yl,
  simp [add_with_carry, add_with_carry_cost, pow_succ],
  ring_nf,
  have g := nat.one_le_two_pow n,
  simp [@nat.succ_mul 1, nat.add_assoc],
  rw [nat.sub_add_cancel, ← nat.sub_add_comm],
  ring_nf,
  all_goals {linarith},
end

theorem add_cost {n : ℕ} : ∀ {x y : binary_nat n},
  cost.cost_of (add x y) = 8 * 2^n - 2 :=
begin
  intros x y,
  simp [add, add_with_carry_cost],
  rw ← nat.sub_add_comm,
  simp,
  have g := nat.one_le_two_pow n,
  apply le_mul_of_le_of_one_le,
  simp,
  apply nat.one_le_two_pow,
end

lemma tmul_dvd3 : ∀ n : ℕ, 3 ∣ 2 * 4 ^ n - 2
| 0 := by simp[pow_zero]
| (n+1) := begin
  rw [pow_succ,
      (show 4*4^n = (1+3)*4^n, by simp),
      add_mul, mul_add, one_mul, mul_left_comm,
      nat.sub_add_comm],
  apply dvd_add,
  apply tmul_dvd3,
  apply dvd_mul_right,
  have t : 1 ≤ 4 ^ n := nat.one_le_pow _ _ (by simp),
  linarith,  
end

lemma tmul_dvd3' : (∀ n : ℕ, 3 ∣ 8 * 4 ^ n - 2) :=
begin
  intro n,
  rw [(show 8 = (2+3*2), by ring), add_mul, nat.sub_add_comm],
  apply dvd_add,
  apply tmul_dvd3,
  rw [mul_assoc],
  apply dvd_mul_right,
  have t : 1 ≤ 4 ^ n := nat.one_le_pow _ _ (by simp),
  linarith,
end

lemma tmul_lt :  (∀ n : ℕ, n ≤ 2^n ∧ 2^n ≤ 4^n)
| 0 := by simp
| (n+1) := begin
  split,
  rw [pow_succ, nat.succ_mul, nat.one_mul],
  apply add_le_add (tmul_lt n).left,
  apply nat.one_le_pow,
  simp,
  rw [pow_succ, pow_succ],
  apply mul_le_mul _ (tmul_lt n).right,
  simp,
  simp,
  simp,
end

lemma tmul_lt' : (∀ {n c d : ℕ}, c ≤ 20 → 4 * n + (192 * 2 ^ n + c) ≤ 224 * 4 ^ n + d) :=
begin
  intros n c d p,
  apply le_add_right,
  rw [show 224 = 4 + (192 + 28), by simp, add_mul, add_mul],
  apply add_le_add,
  apply nat.mul_le_mul (le_refl _) (le_trans (tmul_lt _).left (tmul_lt _).right),
  apply add_le_add,
  apply nat.mul_le_mul (le_refl _) (tmul_lt _).right,
  rw [mul_comm],
  apply le_mul_of_one_le_of_le,
  apply nat.one_le_pow,
  simp,
  linarith,
end

lemma tmul_lt'' : (∀ {n c d : ℕ}, c ≤ 5 → n + (48 * 2 ^ (n + 1) + c) ≤ 56 * 4 ^ (n + 1) + d) :=
begin
  intros n c d p,
  apply le_add_right,
  rw [show 56 = 1 + (48 + 7), by simp, add_mul, add_mul, one_mul],
  apply add_le_add,
  rw [← @nat.add_le_add_iff_right 1],
  apply le_add_right,
  apply le_trans (tmul_lt _).left (tmul_lt _).right,
  apply add_le_add,
  apply nat.mul_le_mul (le_refl _) (tmul_lt _).right,
  rw [mul_comm],
  apply le_mul_of_one_le_of_le,
  apply nat.one_le_pow,
  simp,
  linarith,
end

-- f(n+1) = 4*f(n) + 24 * 2 ^(n+2) + 3*n + 10 
-- f(0) = 5
theorem traditional_multiply_cost : Π {n}, ∀ {x y : binary_nat n},
    cost.cost_of (traditional_multiply x y) = 56 * 4^n + (2*4^n-2)/3 - (48*2^n + n + 3)
| 0 := begin
  intros x y,
  cases x,
  all_goals {cases y},
  all_goals {simp[traditional_multiply]},
  all_goals {ring},
end
| (n+1) := begin
  have g : (∀ {a b c : ℕ}, a ≤ b → (b - a = c ↔ b = c + a)),
  { intros a b c p,
    split,
    intro q,
    rw[← q, nat.sub_add_cancel p],
    intro q,
    rw[q, nat.add_sub_cancel],
  },
  have g' : (∀ {a b c : ℕ}, a ≤ b → (c = b - a ↔ c + a = b)),
  {
    intros a b c p,
    split,
    intro q,
    apply eq.symm,
    rw [← g p],
    exact eq.symm q,
    intro q,
    apply eq.symm,
    rw [g p],
    exact eq.symm q,
  },
  intros x y,
  cases x with _ xu xl,
  cases y with _ yu yl,
  simp[traditional_multiply, zero_cost, add_cost],
  cases (cost.value_of (traditional_multiply xu yl)) with _ ulu ull,
  cases (cost.value_of (traditional_multiply xl yu)) with _ luu lul,
  simp [split, traditional_multiply_cost, nat.add_assoc],
  ring_nf,
  rw [g'],
  simp [nat.mul_sub_left_distrib],
  rw [@nat.add_comm (3*n)],
  repeat { rw [← nat.sub_add_comm] },
  rw [g],
  rw [@nat.add_comm (3 * (8 * 2 ^ (n + 2)))],
  repeat { rw [← nat.sub_add_comm] },
  rw [g],
  simp [pow_succ, mul_add, nat.add_assoc],
  ring_nf,
  rw [add_left_cancel_iff,
      nat.add_left_comm, add_left_cancel_iff,
      nat.add_left_comm, add_left_cancel_iff],
  rw [show 20 = 2 + 18, by simp],
  simp[← nat.add_assoc],
  apply nat.eq_of_mul_eq_mul_left (show 0 < 3, by simp),
  rw [nat.mul_div_cancel', mul_add, mul_left_comm, nat.mul_div_cancel'],
  simp [nat.mul_sub_left_distrib],
  rw [← nat.sub_add_comm],
  ring_nf,
  have t : 1 ≤ 4 ^ n := nat.one_le_pow _ _ (by simp),
  linarith,
  apply tmul_dvd3,
  apply tmul_dvd3',
  ring_nf,
  rw [nat.add_left_comm _ (224*4^n)],
  apply tmul_lt',
  simp,
  ring_nf,
  rw [nat.add_left_comm _ (224*4^n)],
  apply tmul_lt',
  simp,
  ring_nf,
  apply tmul_lt',
  simp,
  ring_nf,
  apply tmul_lt',
  simp,
  ring_nf,
  apply le_add_right,
  rw [mul_comm],
  apply le_mul_of_one_le_of_le,
  apply nat.one_le_pow,
  simp,
  simp,
  ring_nf,
  apply tmul_lt',
  simp,
  ring_nf,
  apply le_add_right,
  rw [mul_comm],
  apply le_mul_of_one_le_of_le,
  apply nat.one_le_pow,
  simp,
  simp,
  ring_nf,
  apply tmul_lt',
  simp,
  ring_nf,
  apply le_add_right,
  rw [mul_comm],
  apply le_mul_of_one_le_of_le,
  apply nat.one_le_pow,
  simp,
  simp,
  ring_nf,
  apply tmul_lt',
  simp,
  ring_nf,
  rw [mul_comm],
  apply le_mul_of_one_le_of_le,
  apply nat.one_le_pow,
  simp,
  simp,
  apply tmul_lt'',
  simp,
end
