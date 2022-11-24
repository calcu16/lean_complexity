import Complexity.StdComp
import Complexity.StdAdd

namespace Complexity
namespace Std

theorem mul_lt_mul {a b c d : Nat} : a < b → c < d → a * c < b * d := by
  intro p
  intro q
  have r := show 0 < b by
    apply Nat.lt_of_le_of_lt
    apply Nat.zero_le
    apply p
  have s := Nat.mul_lt_mul_of_pos_left q r
  apply Nat.lt_of_le_of_lt _ s
  apply Nat.mul_le_mul_right
  apply Nat.le_of_lt
  assumption

theorem mul_eq_mul {a b c d : Nat} : a = b → c = d → a * c = b * d := by
  intros
  simp [*]

theorem lt_of_mul_lt_mul_left {a b c : Nat} (h : c * a < c * b) (hc : 0 < c) : a < b := by
  apply Nat.gt_of_not_le
  intro hlt
  have hlt := lt_of_le_of_ne hlt
  have neq := show b ≠ a by
    intro eq
    rw [eq] at h
    have h := Nat.lt_irrefl (c * a) 
    contradiction
  have hlt := hlt neq
  have h' := Nat.mul_lt_mul_of_pos_left hlt hc
  apply Nat.lt_irrefl (c * a)
  apply Nat.lt_trans
  exact h
  assumption

theorem lt_of_mul_lt_mul_right {a b c : Nat} (h : a * c < b * c) (hc : 0 < c) : a < b := by
  apply lt_of_mul_lt_mul_left
  simp [Nat.mul_comm _ c] at h
  repeat assumption

theorem lt_square {a b : Nat} : a < b → a < b * b := by
  cases b
  simp
  intro
  assumption
  intro p
  have p := Nat.le_of_lt_succ (Nat.succ_lt_succ p)
  apply Nat.lt_of_succ_le
  rw [← Nat.mul_one (Nat.succ a)]
  apply Nat.mul_le_mul
  assumption
  apply Nat.succ_le_succ
  apply Nat.zero_le

theorem mul_right_cancel {a b c : Nat} : 0 < c → a * c = b * c → a = b := by
  intros p q
  cases nat_trich a b with
  | inl h =>
    have h := Nat.mul_lt_mul_of_pos_right h p
    rw [q] at h
    have h := Nat.lt_irrefl (b * c) h
    contradiction
  | inr h =>
    cases h with
    | inl h => assumption
    | inr h =>
      have h := Nat.mul_lt_mul_of_pos_right h p
      rw [q] at h
      have h := Nat.lt_irrefl (b * c) h
      contradiction

end Std
end Complexity