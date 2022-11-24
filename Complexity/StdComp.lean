namespace Complexity
namespace Std

theorem eq_or_ne (a b : Nat) : (a = b) ∨ (a ≠ b) := by
  induction a generalizing b with
  | zero =>
    cases b <;> simp
  | succ a h =>
    cases b with
    | zero =>
      simp
    | succ b =>
      have h := h b
      cases h with
      | inl h =>
        simp [h]
      | inr h =>
        apply Or.inr
        simp
        assumption


theorem lt_add_left {a b : Nat} : a < b → ∀ c, a < c + b := by
  intros p c
  rw [← Nat.zero_add a]
  cases c
  simp
  any_goals apply Nat.add_lt_add
  repeat assumption
  apply Nat.zero_lt_succ
  assumption

theorem lt_add_right {a b : Nat} : a < b → ∀ c, a < b + c := by
  intros p c
  rw [← Nat.add_zero a]
  cases c
  simp
  any_goals apply Nat.add_lt_add
  repeat assumption
  apply Nat.zero_lt_succ

theorem le_exists_sum {a b : Nat} : (a ≤ b ↔ ∃ x, b = a + x) := by
  apply Iff.intro
  intro p
  induction p with
  | refl => exists 0
  | step p q =>
    cases q with | intro x  q =>
    exists Nat.succ x
    simp [Nat.add_succ]
    assumption
  intro p
  cases p with | intro x p =>
  rw [p]
  apply Nat.le_add_right

theorem eq_of_le_of_le_iff (a b : Nat) : a = b ↔ a ≤ b ∧ b ≤ a := by
  apply Iff.intro
  intro p
  simp [p]
  intro p
  cases p with | intro l r =>
  cases le_exists_sum.mp l with | intro x h =>
  simp [h] at r
  rw [← Nat.add_zero a] at r
  have r := Nat.le_of_add_le_add_left r
  rw [Nat.le_zero_eq] at r
  rw [r] at h
  simp [h]

theorem nat_trich (a b : Nat) : a < b ∨ a = b ∨ b < a := by
  cases Nat.le_total a b with
  | inl q =>
    cases le_exists_sum.mp q with | intro x h =>
    cases x with
    | zero =>
      apply Or.inr
      apply Or.inl
      simp [h]
    | succ x =>
      apply Or.inl
      apply Nat.lt_of_succ_le
      rw [le_exists_sum]
      exists x
      simp [h, Nat.add_succ, Nat.succ_add]
  | inr q =>
    cases le_exists_sum.mp q with | intro x h =>
    cases x with
    | zero =>
      apply Or.inr
      apply Or.inl
      simp [h]
    | succ x =>
      apply Or.inr
      apply Or.inr
      apply Nat.lt_of_succ_le
      rw [le_exists_sum]
      exists x
      simp [h, Nat.add_succ, Nat.succ_add]

theorem le_or_lt (a b : Nat) : a ≤ b ∨ b < a := by
  cases nat_trich a b
  apply Or.inl
  apply Nat.le_of_lt
  assumption
  case inr h =>
  cases h
  simp [*]
  apply Or.inr
  assumption

theorem gt_of_lt {a b : Nat} : a < b → b > a := by
  intro p
  apply Nat.gt_of_not_le
  intro q
  apply Nat.lt_irrefl b
  apply Nat.lt_of_le_of_lt
  repeat assumption

theorem one_le_succ (a : Nat) : 1 ≤ Nat.succ a := by
  apply Nat.succ_le_succ
  apply Nat.zero_le

theorem le_succ_or_eq_of_le {a b : Nat} : (a ≤ Nat.succ b → a = Nat.succ b ∨ a ≤ b) :=
  by intro p
     cases Std.le_exists_sum.mp p with | intro x p =>
     cases x with
     | zero => simp [p]
     | succ x =>
       apply Or.inr
       rw [Std.le_exists_sum]
       exists x
       simp [← Nat.add_succ, Nat.succ_eq_add_one, ← Nat.add_assoc, Nat.add_comm _ 1] at p
       simp [Nat.add_assoc] at p
       have p := Nat.add_left_cancel p
       assumption

theorem le_succ_ne_of_le {a b : Nat} : (a ≤ Nat.succ b → a ≠ Nat.succ b → a ≤ b) :=
  by intro p
     intro q
     cases Std.le_exists_sum.mp p with | intro x p =>
     cases x with
     | zero =>
       simp at p
       simp [p] at q
     | succ x =>
       rw [Std.le_exists_sum]
       exists x
       simp [← Nat.add_succ, Nat.succ_eq_add_one, ← Nat.add_assoc, Nat.add_comm _ 1] at p
       simp [Nat.add_assoc] at p
       have p := Nat.add_left_cancel p
       assumption

theorem succ_lt_succ_iff {a b : Nat} : a < b ↔ Nat.succ a < Nat.succ b := by
  apply Iff.intro
  apply Nat.succ_lt_succ
  intros
  apply Nat.lt_of_succ_le
  apply Nat.le_of_lt_succ
  assumption

theorem lt_of_le_of_ne {a b : Nat} : a ≤ b → a ≠ b → a < b := by
  intro p
  intro q
  cases b with
  | zero =>
    rw [Nat.le_zero_eq a] at p
    contradiction
  | succ b =>
    apply Nat.lt_of_succ_le
    apply Nat.succ_le_succ
    apply le_succ_ne_of_le
    repeat assumption

theorem add_lt_add_le {a b c d: Nat} : a < c → b ≤ d → a + b < c + d := by
  intros p q
  apply Nat.lt_of_succ_le
  rw [← Nat.succ_add]
  apply Nat.add_le_add
  apply Nat.le_of_lt_succ
  apply Nat.succ_lt_succ
  repeat assumption


theorem add_le_add_lt {a b c d: Nat} : a ≤ c → b < d → a + b < c + d := by
  intros
  rw [Nat.add_comm, Nat.add_comm c]
  apply add_lt_add_le
  repeat assumption

theorem le_or_eq_or_lt {a b : Nat} : a ≤ b → (a = b) ∨ a < b := by
  intro p
  cases le_exists_sum.mp p with | intro x h =>
  cases x with
  | zero => simp [h]
  | succ x =>
    simp [h, Nat.add_succ]
    apply Or.inr
    apply Nat.lt_of_succ_le
    apply Nat.succ_le_succ
    rw [← Nat.add_zero a]
    apply Nat.add_le_add
    simp
    simp

theorem le_iff_eq_or_lt {a b : Nat} : a ≤ b ↔ ((a = b) ∨ a < b) := by
  apply Iff.intro
  apply le_or_eq_or_lt
  intro p
  cases p
  apply Nat.le_of_eq
  any_goals apply Nat.le_of_lt
  all_goals assumption

theorem le_max (a b : Nat) : ∃ x : Nat, a ≤ x ∧ b ≤ x :=
  by cases Nat.le_total a b
     exists b
     simp [And.intro]
     assumption
     exists a
     simp [And.intro]
     assumption


theorem max_le (a b : Nat) : a ≤ Nat.max a b := by
  simp [Nat.max]
  rw [max]
  simp [Nat.instMaxNat, maxOfLe, ite, Nat.decLe, ite]
  cases nat_trich a b with
  | inl lab =>
    have x := show (a ≤ b) = true by
      simp[Nat.le_of_lt lab]
    simp [x]
  | inr geab =>
    cases geab with
    | inl ea =>
      have x := show (a ≤ b) = true by
        simp [ea]
      simp [x]
    | inr lb =>
      have x := show (a ≤ b) ↔ false by
        apply Iff.intro
        all_goals intro p
        any_goals contradiction
        simp
        apply Nat.lt_irrefl
        apply Nat.lt_of_le_of_lt
        repeat assumption
      simp [x]

theorem max_comm (a b : Nat) : Nat.max a b = Nat.max b a := by
  simp [Nat.max]
  rw [max]
  simp [Nat.instMaxNat, maxOfLe, ite, Nat.decLe, ite]
  cases nat_trich a b with
  | inl lab =>
    have x := show (a ≤ b) = true by
      simp[Nat.le_of_lt lab]
    have y := show (b ≤ a) ↔ false by
      apply Iff.intro
      all_goals intro p
      any_goals contradiction
      simp
      apply Nat.lt_irrefl
      apply Nat.lt_of_le_of_lt
      repeat assumption
    simp [x, y]
  | inr geab =>
    cases geab with
    | inl ea => simp[ea]
    | inr lba =>
      have x := show (a ≤ b) ↔ false by
        apply Iff.intro
        all_goals intro p
        any_goals contradiction
        simp
        apply Nat.lt_irrefl
        apply Nat.lt_of_le_of_lt
        repeat assumption
      have y := show (b ≤ a) = true by
        simp[Nat.le_of_lt lba]
      simp [x, y]

theorem zero_or_one_lt_two (a : Nat) : (a = 0 ∨ a = 1) ↔ (a < 2) := by
  apply Iff.intro
  all_goals intro h
  cases h
  repeat simp[*]
  cases a
  simp
  case succ a =>
  cases a
  simp
  simp [← succ_lt_succ_iff] at h
  contradiction

theorem zero_of_lt_two_ne_one (a : Nat) : a < 2 → a ≠ 1 → a = 0 := by
  intro p
  intro q
  rw [← zero_or_one_lt_two] at p
  cases p
  simp [*]
  contradiction

end Std
end Complexity