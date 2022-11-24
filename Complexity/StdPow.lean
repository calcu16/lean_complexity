import Complexity.StdComp
import Complexity.StdAdd
import Complexity.StdMul

namespace Complexity
namespace Std

theorem one_pow (a b : Nat) : a = 1 → a ^ b = 1 := by
  induction b with
  | zero => simp [Nat.pow_zero]
  | succ b h =>
    intro p
    simp [p, Nat.pow_succ] at *
    assumption

theorem pow_two (a : Nat) : a ^ 2 = a * a := by simp [Nat.pow_succ, Nat.pow_zero]

theorem mul_pow (a b c : Nat) : (a * b) ^ c  = a ^ c * b ^ c := by
  induction c <;> simp [*, Nat.pow_zero, Nat.pow_succ]
  simp [Nat.mul_comm _ a, ← Nat.mul_assoc]

theorem two_mul {a : Nat} : 2 * a = a + a := by simp [Nat.succ_mul]

theorem pow_mul_pow (a b c : Nat) : (a ^ b) * (a ^ c) = a ^ (b + c) := by
  induction c <;> simp [*, Nat.pow_zero, Nat.add_zero, Nat.mul_one, Nat.pow_succ, Nat.add_succ, ← Nat.mul_assoc]
  
theorem pow_pow (a b c : Nat) : (a ^ b) ^ c = a ^ (b * c) := by
  induction c <;> simp [*, Nat.mul_zero, Nat.pow_zero, Nat.pow_succ, Nat.mul_succ, pow_mul_pow]

theorem pow_one_lt (a b : Nat) : 1 < a → 0 < b → 1 < a ^ b := by
  intros p q
  cases b with
  | zero => simp at q
  | succ b =>
    induction b with
    | zero => simp [Nat.pow_succ, Nat.pow_zero]; assumption
    | succ b r =>
      have r := r (Nat.zero_lt_succ b)
      have s := show a > 0 by
        apply Nat.gt_of_not_le
        intro t
        have t := Nat.lt_of_lt_of_le p t
        simp at t
      have s := Nat.mul_lt_mul_of_pos_right r s
      simp at s
      have s := Nat.lt_trans p s
      rw [← Nat.pow_succ] at s
      assumption

theorem pow_log_le {a b c : Nat} : 1 < c → c ^ a ≤ c ^ b → a ≤ b := by
  intros p q
  induction b generalizing a with
  | zero =>
    simp [Nat.pow_zero] at q
    simp
    cases a with
    | zero => rfl
    | succ a =>
      simp
      have r := pow_one_lt c (Nat.succ a) p (Nat.zero_lt_succ a)
      have r := Nat.lt_of_le_of_lt q r
      simp at r
  | succ b r =>
    cases a with
    | zero => simp
    | succ a =>
      apply Nat.succ_le_succ
      apply r
      apply @Nat.le_of_mul_le_mul_left (c ^ a) (c ^ b) c
      simp [Nat.mul_comm c, ← Nat.pow_succ]
      assumption
      apply (Nat.lt_trans Nat.zero_lt_one p)
      
theorem pow_log_eq {a b c : Nat} : 1 < c → (c ^ a = c ^ b ↔ a = b) := by
  intro p
  apply Iff.intro
  intro q
  rw [eq_of_le_of_le_iff]
  apply And.intro
  any_goals apply pow_log_le
  any_goals apply p
  any_goals rw [q]
  any_goals simp
  intro q
  simp [q]

theorem pow_log_ne (a b c : Nat) : c ^ a ≠ c ^ b → a ≠ b := by
  intros q r
  rw [r] at q
  contradiction


theorem pow_log_lt_mpr {a b c : Nat} : 1 < c → a < b → c ^ a < c ^ b := by
  intro p
  intro q
  apply lt_of_le_of_ne
  apply Nat.pow_le_pow_of_le_right
  apply gt_of_lt
  apply Nat.lt_trans
  apply Nat.zero_lt_one
  assumption
  apply Nat.le_of_lt
  assumption
  intro r
  rw [pow_log_eq p] at r
  simp [r] at q

theorem pow_log_lt {a b c : Nat} : 1 < c → c ^ a < c ^ b → a < b := by
  intro p
  intro q
  apply lt_of_le_of_ne
  apply pow_log_le
  repeat assumption
  apply Nat.le_of_lt_succ
  apply Nat.lt_trans
  apply Nat.lt_succ_self
  apply Nat.succ_lt_succ
  assumption
  intro p
  rw [p] at q
  have r := Nat.lt_irrefl (c ^ b) q
  contradiction

theorem pow_log_le_mpr {a b c : Nat} : 1 < c → a ≤ b → c ^ a ≤ c ^ b := by
  intro p
  intro q
  rw [le_iff_eq_or_lt] at q
  cases q with
  | inl q => simp [q]
  | inr q =>
    apply Nat.le_of_lt
    apply pow_log_lt_mpr
    repeat assumption

theorem pow_exp_eq_helper0 {a b : Nat} : a * a = b * b → a = b := by
  intro p
  cases nat_trich a b with
  | inl q =>
    have q := mul_lt_mul q q
    simp [p] at q
  | inr q =>
    cases q with
    | inl q => assumption
    | inr q =>
      have q := mul_lt_mul q q
      simp [p] at q

theorem pow_exp_lt {a b c : Nat} : a ^ c < b ^ c → a < b := by
  intro p
  apply Nat.gt_of_not_le
  intro q
  have q := lt_of_le_of_ne q
  have ne := show b ≠ a by
    intro eq 
    apply Nat.lt_irrefl (a ^ c)
    rw [eq] at p
    assumption
  have q := q ne
  have r := @Nat.pow_le_pow_of_le_left b a (Nat.le_of_lt q) c
  have r := Nat.lt_irrefl _ (Nat.lt_of_lt_of_le p r)
  assumption

theorem pow_exp_lt_mpr {a b c : Nat} : a < b → a ^ (Nat.succ c) < b ^ (Nat.succ c) := by
  intro p
  induction c with
  | zero =>
    simp [Nat.pow_succ, Nat.pow_zero]
    apply p
  | succ c h =>
    simp [Nat.pow_succ _ (Nat.succ c)]
    apply mul_lt_mul
    repeat assumption

theorem pow_exp_le_mpr {a b c : Nat} : a ≤ b → a ^ c ≤ b ^ c := by
  intro p
  induction c with
  | zero =>
    simp [Nat.pow_succ, Nat.pow_zero]
  | succ c h =>
    simp [Nat.pow_succ _ (Nat.succ c)]
    apply Nat.mul_le_mul
    repeat assumption

theorem le_succ_pow (a b : Nat) : a ^ (Nat.succ b) + (Nat.succ b) * a ^ b ≤ (Nat.succ a) ^ (Nat.succ b) := by
  induction b with
  | zero =>
    simp [Nat.pow_succ, Nat.pow_zero]
  | succ b h =>
    rw [Nat.succ_eq_add_one] at *
    have h := Nat.mul_le_mul h (Nat.le_refl (a + 1))
    simp [← Nat.pow_succ] at h
    simp [Nat.add_mul, Nat.mul_add] at h
    simp [← Nat.pow_succ, Nat.succ_eq_add_one, Nat.add_mul, ← Nat.add_assoc, Nat.mul_assoc] at *
    have g := Nat.le_add_right 0 (b * a ^ b + a ^ b)
    have h := Nat.add_le_add h g
    simp [← Nat.add_assoc] at h
    have h := Nat.le_of_add_le_add_right h
    have h := Nat.le_of_add_le_add_right h
    assumption

theorem succ_pow_le (a b : Nat) : (Nat.succ (Nat.succ a)) ^ b ≤ 2 ^ b * (Nat.succ a) ^ b := by
  induction b with
  | zero => simp [Nat.pow_zero]
  | succ n h =>
    simp [Nat.pow_succ, Nat.mul_assoc]
    rw [Nat.mul_comm 2, Nat.mul_assoc, Nat.mul_comm _ 2, ← Nat.mul_assoc]
    have g := show a + 1 + 1 ≤ 2 * (a + 1) by
      simp [Nat.mul_add, Nat.succ_mul]
      apply Nat.add_le_add
      apply Nat.le_refl
      apply Nat.succ_le_succ
      apply Nat.zero_le
    have f := Nat.mul_le_mul h g
    apply f

theorem pow2_squeeze_helper {a : Nat} : ∃ x, 2 ^ x ≤ (a + 1) ∧ (a + 1) < 2 ^ (x + 1) := by
  induction a with
  | zero => exists 0
  | succ a h =>
    cases h with | intro x h =>
    cases h with | intro lb ub =>
    have ub := Nat.add_lt_add_right ub 1
    have ub := Nat.le_of_lt_succ ub
    cases le_or_eq_or_lt ub with
    | inl ub =>
      exists Nat.succ x
      simp at ub
      apply And.intro
      simp [← ub, ← Nat.succ_eq_add_one]
      rw [Nat.succ_eq_add_one, ub, Nat.succ_add, Nat.pow_succ _ (x + 1), Nat.mul_succ, Nat.mul_one]
      rw [← Nat.add_zero (2 ^ (x + 1))]
      apply add_lt_of_le_of_lt
      repeat simp
      apply Nat.lt_trans
      apply Nat.zero_lt_one
      apply pow_one_lt
      simp
      apply Nat.zero_lt_succ
    | inr ub =>
      exists x
      simp at ub
      apply And.intro
      rw [Nat.succ_add]
      apply Nat.le_trans
      apply lb
      apply Nat.le_succ
      exact ub

theorem pow2_squeeze {a : Nat} : 0 < a → ∃ x, 2 ^ x ≤ a ∧ a < 2 ^ (x + 1) := by
  cases a
  simp
  intro _
  apply pow2_squeeze_helper

theorem lt_pow2_succ_exp2_helper (a : Nat) : 2 * a + 11 < 2 ^ (5 + a) := by
  induction a with
  | zero => simp
  | succ a h =>
    simp [Nat.mul_succ, Nat.add_succ 5, Nat.pow_succ, Nat.add_right_comm _ 2 11]
    apply Nat.add_lt_add
    assumption
    have g := Nat.pow_le_pow_of_le_right (show 2 > 0 by simp) (Nat.le_add_right 5 a)
    apply Nat.lt_of_lt_of_le _ g
    simp

theorem lt_pow2_lt_exp2 (a : Nat) : 5 ≤ a → a ^ 2 < 2 ^ a := by
  intro  q
  cases le_exists_sum.mp q with | intro x h =>
  rw [h]
  induction x generalizing a with
  | zero => simp
  | succ x g =>
      have g := g (5 + x) (Nat.le_add_right _ _) (Eq.refl _)
      have q := show (5 + Nat.succ x) ^ 2 = (5 + x) ^ 2 + (2 * x + 11) by
        simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_add, Nat.add_mul, Nat.mul_succ, Nat.succ_mul, Nat.succ_eq_add_one, Nat.add_assoc]
        simp [← Nat.add_left_comm x, ← add_left_cancel_iff]
        simp [← Nat.add_left_comm (x * x), ← add_left_cancel_iff]
      rw [q]
      rw [Nat.add_succ 5, Nat.pow_succ 2, Nat.mul_succ, Nat.mul_one]
      apply Nat.add_lt_add
      assumption
      apply lt_pow2_succ_exp2_helper

theorem lt_succ_pow2_exp2_helper (a : Nat) : 2 * a + 15 < 2 ^ (6 + a) := by
  induction a with
  | zero => simp
  | succ a h =>
    simp [Nat.mul_succ, Nat.add_succ 5, Nat.pow_succ, Nat.add_right_comm _ 2 15]
    apply Nat.add_lt_add
    simp
    assumption
    have g := Nat.pow_le_pow_of_le_right (show 2 > 0 by simp) (Nat.le_add_right 6 a)
    apply Nat.lt_of_lt_of_le _ g
    simp

theorem lt_succ_pow2_lt_exp2 (a : Nat) : 6 ≤ a → (a + 1) ^ 2 < 2 ^ a := by
  intro  q
  cases le_exists_sum.mp q with | intro x h =>
  rw [h]
  induction x generalizing a with
  | zero => simp
  | succ x g =>
      have g := g (6 + x) (Nat.le_add_right _ _) (Eq.refl _)
      have q := show (6 + Nat.succ x + 1) ^ 2 = (6 + x + 1) ^ 2 + (2 * x + 15) by
        simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_add, Nat.add_mul, Nat.mul_succ, Nat.succ_mul, Nat.succ_eq_add_one, Nat.add_assoc]
        simp [← Nat.add_left_comm x, ← add_left_cancel_iff]
        simp [← Nat.add_left_comm (x * x), ← add_left_cancel_iff]
      rw [q]
      rw [Nat.add_succ 6, Nat.pow_succ 2, Nat.mul_succ, Nat.mul_one]
      apply Nat.add_lt_add
      assumption
      apply lt_succ_pow2_exp2_helper


theorem lt_pow_lt_exp2_helper (a b : Nat) : 5 ≤ b → a = 2 ^ b → a ^ b < 2 ^ a := by
  intro p
  intro q
  simp [q, pow_pow]
  apply pow_log_lt_mpr
  simp
  rw [show b * b = b ^ 2 by simp [Nat.pow_succ, Nat.pow_zero]]
  apply lt_pow2_lt_exp2
  assumption

theorem lt_pow_lt_exp2 (a b : Nat) : 6 ≤ b → 2 ^ b ≤ a → a ^ b < 2 ^ a := by
  intro p
  intro q
  have r := Nat.pos_pow_of_pos b (show 0 < 2 by simp)
  have r := Nat.lt_of_lt_of_le r q
  cases pow2_squeeze r with | intro x h =>
  cases h with | intro lb ub =>
  have r := Nat.lt_of_le_of_lt q ub
  have r := pow_log_lt (show 1 < 2 by simp) r
  have s := show a ^ b < (2 ^ (x + 1)) ^ b by
    cases b
    simp at p
    apply pow_exp_lt_mpr
    assumption
  apply Nat.lt_of_lt_of_le
  apply s
  rw [pow_pow]
  apply pow_log_le_mpr
  simp
  have r2 := Nat.mul_lt_mul_of_pos_left r (gt_of_lt (Nat.zero_lt_succ x))
  rw [Nat.succ_eq_add_one] at r2
  apply Nat.le_of_lt
  apply Nat.lt_of_lt_of_le
  apply r2
  apply Nat.le_trans
  any_goals apply lb
  apply Nat.le_of_lt
  rw [show ((x +1) * (x + 1) = (x + 1) ^ 2) by simp [Nat.pow_succ, Nat.pow_zero]]
  apply lt_succ_pow2_lt_exp2
  apply Nat.le_trans
  apply p
  apply Nat.le_of_lt_succ
  apply r

theorem cmul_exponent_le (a b c : Nat) : b * a < c → b * a ^ c < (a + 1) ^ c := by
   intro p
   cases c with
  | zero => 
    have _ := Nat.not_eq_zero_of_lt p
    contradiction
  | succ c =>
    induction c with
    | zero =>
      simp [Nat.pow_succ, Nat.pow_zero]
      simp at p
      have p := Nat.le_of_lt_succ p
      rw [Nat.le_zero_eq] at p
      rw [p]
      apply Nat.zero_lt_succ
    | succ c h =>
      have p := Nat.le_of_lt_succ p
      cases Nat.le_or_eq_or_le_succ p with
      | inl p =>
        have p := Nat.lt_of_succ_le (Nat.add_le_add p (Nat.le_refl 1))
        have h := h (Nat.lt_of_succ_le p)
        have g := gt_of_lt (Nat.zero_lt_succ a)
        have h := Nat.mul_lt_mul_of_pos_right h g
        simp [Nat.mul_assoc, ← Nat.pow_succ] at h
        simp [Nat.mul_succ, ← Nat.pow_succ] at h
        simp [← Nat.mul_assoc, Nat.mul_add] at h
        have h := add_lt_of_lt_of_le h (Nat.zero_le (b * a ^ (c + 1)))
        have h := lt_of_add_lt_add_right h
        have h := lt_of_add_lt_add_right h
        apply h
      | inr p =>
        have h := le_succ_pow a (b * a)
        have g := Nat.le_add_left (Nat.succ (b * a) * a ^ (b * a)) (a ^ Nat.succ (b * a))
        have h := Nat.le_trans g h
        rw [Nat.succ_mul, Nat.mul_assoc, Nat.mul_comm a, ← Nat.pow_succ] at h
        cases a with
        | zero =>
          simp [Nat.mul_zero] at p
        | succ a =>
          have g := Nat.zero_lt_succ a
          have g := Nat.pos_pow_of_pos (b * Nat.succ a) g
          have h := add_lt_of_le_of_lt h g
          simp [← Nat.add_assoc] at h
          have h := lt_of_add_lt_add_right h
          rw [← p]
          assumption

theorem cmul_power_le (a b c x : Nat) : c < x → x ^ n ≤ c * x ^ m → n ≤ m := by
  intro p
  intro q
  cases c with
  | zero =>
    simp at q
    cases n with
    | zero => apply Nat.zero_le
    | succ n =>
      rw [Nat.pow_succ] at q
      have r := Nat.pos_pow_of_pos n p
      have p := Std.gt_of_lt p
      have r := Std.gt_of_lt r
      have t := Nat.mul_pos p r
      simp [Nat.mul_comm x, q] at t
  | succ c =>
    have r := Nat.zero_le c
    have r := Nat.add_le_add_right r 1
    simp [Nat.add_succ] at r
    have r := Nat.lt_of_le_of_lt r p
    simp [Nat.succ_eq_add_one] at r
    have r2 := Nat.lt_trans (Nat.zero_lt_one) r
    have r3 := Nat.pos_pow_of_pos m r2
    have s := Nat.mul_lt_mul_of_pos_left p (Std.gt_of_lt r3)
    rw [Nat.mul_comm] at s
    have q2 := Nat.lt_of_le_of_lt q s
    rw [← Nat.pow_succ] at q2
    apply Nat.le_of_lt_succ
    apply pow_log_lt
    apply r
    assumption

end Std
end Complexity