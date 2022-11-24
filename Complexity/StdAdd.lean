import Complexity.StdComp

namespace Complexity
namespace Std

theorem add_left_cancel_iff (a b c : Nat) : a = b ↔ c + a = c + b := by
  apply Iff.intro
  intro p
  induction c
  simp [*]
  simp [Nat.add_succ, *]
  exact Nat.add_left_cancel

theorem add_right_cancel_iff (a b c : Nat) : a = b ↔ a + c = b + c := by
  simp [Nat.add_comm _ c]
  apply add_left_cancel_iff

theorem zero_add_left {a b : Nat} : 0 = a → b = b + a := by intro a; simp[← a]

theorem add_lt_of_lt_of_le {a b c d : Nat} : a < b → c ≤ d → a + c < b + d := by
  intros p q
  have p := Nat.le_of_lt_succ (Nat.succ_lt_succ p)
  have q := Nat.add_le_add p q
  rw [Nat.succ_add] at q
  apply Nat.lt_of_succ_le q

theorem add_lt_of_le_of_lt {a b c d : Nat} : a ≤ b → c < d → a + c < b + d := by
  intros p q
  have q := Nat.le_of_lt_succ (Nat.succ_lt_succ q)
  have q := Nat.add_le_add p q
  rw [Nat.add_succ] at q
  apply Nat.lt_of_succ_le q

theorem lt_of_add_lt_add_left {a b c : Nat} : a + b < a + c → b < c := by
  intro p
  have p := Nat.le_of_lt_succ (Nat.succ_lt_succ p)
  rw [← Nat.add_succ] at p
  have p := Nat.le_of_add_le_add_left p
  apply Nat.lt_of_succ_le
  assumption

theorem lt_of_add_lt_add_right {a b c : Nat} : a + b < c + b → a < c := by
  intro p
  have p := Nat.le_of_lt_succ (Nat.succ_lt_succ p)
  rw [← Nat.succ_add] at p
  have p := Nat.le_of_add_le_add_right p
  apply Nat.lt_of_succ_le
  assumption

end Std
end Complexity