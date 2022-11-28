import binary_nat
import data.nat.basic
import data.nat.pow
import tactic.suggest
import tactic.linarith

open binary_nat
open costed_binary_nat
open complexity

universe u
variables {α : Type u}

lemma zero_lt_two_pow {n : ℕ} : 0 < (2 ^ n) :=
nat.lt_of_lt_of_le (by simp) (nat.one_le_two_pow _)

lemma pow_two_pow_square {n m : ℕ} : n ^ 2 ^ (m + 1) = n ^ 2 ^ m * n ^ 2 ^ m :=
by  rw [pow_succ, mul_comm 2, pow_mul, pow_succ, pow_one] 

lemma one_lt_two_two_pow : ∀ n : ℕ, 1 < (2 ^ 2 ^ n)
| 0 := by simp
| (n+1) := begin
  rw [pow_two_pow_square],
  apply lt_mul_of_lt_of_one_le,
  apply one_lt_two_two_pow,
  apply le_of_lt,
  apply one_lt_two_two_pow,
end

lemma mod_cancel {x y: ℕ} (z : ℕ) (H: x = y): x % z = y % z := by simp[H]

theorem toNat_bound : Π {n}, ∀ x : binary_nat n, toNat x < 2 ^ 2 ^ n
| 0 := begin
  intro x,
  cases x,
  all_goals { simp[toNat] },
end
| (n+1) := begin
  intro x,
  cases x with _ xu xl,
  simp [toNat],
  apply @nat.lt_of_lt_of_le _ (2 ^ 2 ^ n * xu.toNat + 2 ^ 2 ^ n),
  apply add_lt_add_left,
  apply toNat_bound,
  rw [← nat.mul_succ, pow_two_pow_square],
  apply nat.mul_le_mul_left,
  apply nat.le_of_lt_succ,
  apply nat.succ_lt_succ,
  apply toNat_bound,
end

theorem toNat_cancel : Π {n}, ∀ x y : binary_nat n,
  toNat x = toNat y ↔ x = y 
| 0 := begin
  intros x y,
  cases x,
  all_goals {cases y},
  all_goals {simp [toNat]},
end
| (n+1) := begin
  intros x y,
  split,
  cases x with _ xu xl,
  cases y with _ yu yl,
  simp [toNat, nat.mul_comm (2^2^n)],
  intro p,
  have q := mod_cancel (2^2^n) p,
  simp [nat.mul_add_mod, nat.mod_eq_of_lt (toNat_bound _)] at q,
  rw [toNat_cancel] at q,
  simp [q, toNat_cancel] at p,
  exact ⟨p, q⟩,
  intro p,
  simp [p],
end

theorem zero_value : Π (n), toNat (cost.value_of (zero n)) = 0
| 0 := by simp [zero, toNat]
| (n+1) := begin
  simp [zero, zero_value, toNat],
end

lemma nat_mul_add_div_left (y z : ℕ) {x : ℕ} (H: 0 < x) : (x * y + z) / x = y + z / x :=
by simp [add_comm, nat.add_mul_div_left _ _ H]

lemma mod_absorb {x y z : ℕ} (H: 0 < x) : x * (y % x) + (z % x) = (x * y + (z % x)) % (x ^ 2) :=
begin
  have g := show (x * (y % x) + (z % x) < x ^ 2),
  begin
    apply @nat.lt_of_lt_of_le _ (x * (y % x) + x),
    apply add_lt_add_left,
    apply nat.mod_lt _ H,
    rw [← nat.mul_succ, pow_succ, pow_one],
    apply nat.mul_le_mul_left,
    apply nat.le_of_lt_succ,
    apply nat.succ_lt_succ,
    apply nat.mod_lt _ H,
  end,
  rw [← nat.mod_eq_of_lt g],
  rw [← nat.mul_mod_mul_left],
  rw [pow_succ, pow_one],
  rw [nat.mod_add_mod],
end

lemma mul_lt_div {a b c : ℕ} : a < c → b < c → a * b / c < c :=
begin
  intros p q,
  apply @lt_of_mul_lt_mul_left _ c,
  apply @nat.lt_of_add_lt_add_right _ (a*b%c),
  rw [nat.div_add_mod],
  apply nat.lt_add_right,
  cases a,
  simp,
  assumption,
  apply @nat.lt_trans _ (a.succ*c),
  apply nat.mul_lt_mul_of_pos_left,
  assumption,
  apply nat.zero_lt_succ,
  apply nat.mul_lt_mul_of_pos_right,
  assumption,
  apply pos_of_gt,
  assumption,
  apply nat.zero_le _,
end

lemma add_mul_lt_div {a b c d e : ℕ} : (a < b) → (c < b) → (d + b < e) → (d + a*c/b < e) :=
begin
  intros p q r,
  apply nat.lt_trans _ r,
  rw add_lt_add_iff_left,
  exact mul_lt_div p q,
end

theorem add_with_carry_value : Π {n}, ∀ x y : binary_nat n, ∀ z : binary_nat 0,
  (toNat (cost.value_of (add_with_carry x y z)).fst = (toNat x + toNat y + toNat z) / 2 ^ 2 ^ n) ∧
  (toNat (cost.value_of (add_with_carry x y z)).snd = (toNat x + toNat y + toNat z) % 2 ^ 2 ^ n)
| 0 := begin
  intros x y z,
  cases x,
  all_goals { cases y },
  all_goals { cases z },
  all_goals { simp [add_with_carry, toNat] },
  all_goals { ring },
end
| (n+1) := begin
  intros x y z,
  cases x with binary_nat.intro xu xl,
  cases y with binary_nat.intro yu yl,
  simp [add_with_carry, toNat,
      (add_with_carry_value _ _ _).left,
      (add_with_carry_value _ _ _).right],
  split,
  ring_nf,
  rw [pow_two_pow_square],
  rw [← nat.div_div_eq_div_mul,
      nat_mul_add_div_left _ _ zero_lt_two_pow,
      nat_mul_add_div_left _ _ zero_lt_two_pow],
  rw [mod_absorb zero_lt_two_pow],
  rw [← pow_mul, nat.mul_comm _ 2, ← pow_succ],
  apply mod_cancel,
  simp [mul_add, nat.add_assoc],
  rw [nat.div_add_mod],
  ring,
end

theorem add_value { n : ℕ } {x y : binary_nat n } :
    toNat (cost.value_of (add x y)) = (toNat x + toNat y) % 2 ^ 2 ^ n :=
by simp[add, toNat, add_with_carry_value x y bit_false]

theorem traditional_multiply_value : Π {n}, ∀ {x y : binary_nat n },
    toNat (cost.value_of (traditional_multiply x y)) = (toNat x * toNat y)
| 0 := begin
  intros x y,
  cases x,
  all_goals {cases y},
  all_goals {simp [traditional_multiply, toNat]},
end
| (n+1) := begin
  intros x y,
  cases x with binary_nat.intro xu xl,
  cases y with binary_nat.intro yu yl,
  simp [traditional_multiply, toNat,
      zero_value, add_value, traditional_multiply_value],
  cases h : (cost.value_of (traditional_multiply xu yl)) with _ ulu ull,
  cases g : (cost.value_of (traditional_multiply xl yu)) with _ luu lul,
  simp [split, toNat],
  rw [← toNat_cancel] at h,
  rw [← toNat_cancel] at g,
  have H : (∀ {n x y z : ℕ}, x = 2^2^n * y + z → 2^2^ n * x = 2^2^(n + 1) * y + 2^2^n * z),
  { intros n x y z p,
    rw [pow_two_pow_square, p],
    ring },
  simp [traditional_multiply_value, toNat] at h,
  simp [traditional_multiply_value, toNat] at g,
  rw [← H h, ← H g, nat.mod_eq_of_lt],
  simp [mul_add, add_mul, pow_two_pow_square],
  ring,
  simp [pow_two_pow_square],
  simp [← nat.add_assoc],
  have reduce : ∀ {a b c d e: ℕ }, a < c → b < c → e + c*c + 1 < d + 2*c → 
  e + a*b < d,
  { intros a b c d e p q r,
    rw [← add_lt_add_iff_right (2*c)],
    apply nat.lt_of_le_of_lt _ r,
    simp [nat.add_assoc],
    cases c,
    linarith,
    simp [nat.succ_eq_add_one, mul_add, add_mul],
    ring_nf,
    simp [← nat.add_assoc, add_mul],
    apply nat.mul_le_mul,
    apply nat.le_of_lt_succ q,
    apply nat.le_of_lt_succ p, },
  apply reduce (toNat_bound _) (toNat_bound _),
  apply @nat.lt_of_div_lt_div _ _ (2^2^n),
  simp [nat.add_assoc, nat.mul_assoc,
    nat_mul_add_div_left _ _ zero_lt_two_pow, nat.div_eq_zero (one_lt_two_two_pow _)],
  simp [← nat.add_assoc, nat.add_comm _ (2^2^n)],
  apply reduce (toNat_bound _) (toNat_bound _),
  simp [nat.add_right_comm _ (xu.toNat * yl.toNat)],
  apply reduce (toNat_bound _) (toNat_bound _),
  simp [← nat.add_assoc, nat.add_right_comm _ 1],
  apply @nat.lt_of_div_lt_div _ _ (2^2^n),
  simp [nat.add_assoc, nat.mul_assoc,
        nat_mul_add_div_left _ _ zero_lt_two_pow,
        nat.div_eq_zero (one_lt_two_two_pow _),
        nat.add_mul_div_right],
  rw [nat.add_comm, ← nat.succ_add, nat.succ_eq_add_one],
  apply reduce (toNat_bound _) (toNat_bound _),
  linarith,
end