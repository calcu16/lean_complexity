import Complexity.StdComp
import Complexity.StdAdd
import Complexity.StdMul

namespace Complexity
namespace Std

theorem div_eq_div {a b : Nat} : a = b → ∀ c : Nat, a / c = b / c := by intro; simp[*]

theorem div_zero_of_lt {a b : Nat} : a < b → a / b = 0 := by
  intro p
  have q := show (¬ (0 < b ∧ b ≤ a)) by
    intro q
    apply Nat.lt_irrefl a
    apply Nat.lt_of_lt_of_le
    assumption
    apply q.right
  rw [Nat.div_eq]
  simp [q]

theorem div_exists {a b c : Nat} : 0 < b → (c = a / b ↔ ∃ x, x < b ∧ b * c + x = a) := by
  intro lb
  apply Iff.intro
  intros
  exists (a % b)
  simp [*]
  apply And.intro
  apply Nat.mod_lt
  assumption
  apply Nat.div_add_mod
  induction a, b using Nat.div.inductionOn generalizing c with
  | base a b h0 =>
    have h := show (a < b) by
      cases nat_trich a b with
      | inl => assumption
      | inr h => cases h with
        | inl h =>
          have _ := And.intro lb (Nat.le_of_eq h.symm)
          contradiction
        | inr h =>
          have _ := And.intro lb (Nat.le_of_lt h)
          contradiction
    intro g
    cases g with | intro x g =>
    cases c with
    | zero =>
      simp
      rw [Nat.div_eq]
      simp [h0]
    | succ c =>
      cases g with | intro f g =>
      simp [Nat.mul_succ] at g
      rw [← g] at h
      have h := Std.lt_of_add_lt_add_right (Std.lt_add_right h _)
      have h := Std.lt_of_add_lt_add_left (Std.lt_add_left h _)
      simp at h
  | ind a b g h =>
    intro f
    rw [Nat.div_eq]
    simp [g]
    cases c with
    | zero =>
      simp at f
      cases f with | intro x f =>
      cases f with | intro e f =>
      rw [f] at e
      have f := Nat.lt_of_le_of_lt g.right e
      have _ := Nat.lt_irrefl b f
      contradiction
    | succ c =>
      rw [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_comm _ 1, ← Std.add_left_cancel_iff]
      apply h
      assumption
      cases f with | intro x f =>
      exists x
      cases f with | intro _ f =>
      apply And.intro
      assumption
      simp [← f, Nat.mul_succ, Nat.add_right_comm _ b, Nat.add_sub_cancel]

theorem zero_div {a: Nat} : 0 / a = 0 := by
  cases a
  simp [Nat.div_eq]
  rw [div_zero_of_lt]
  apply Nat.zero_lt_succ

theorem self_div {a: Nat} : 0 < a → a / a = 1 := by
  intro
  rw [Nat.div_eq]
  simp [*]
  apply zero_div

theorem self_mul_div {a b c : Nat} : 0 < a → (a * b + c) / a = b + (c / a) := by
  let n := c / a
  have hn := show (n = c / a) by rfl
  intros
  apply Eq.symm
  cases (div_exists (show (0 < a) by assumption)).mp hn with | intro x h =>
  rw [div_exists]
  exists x
  apply And.intro
  exact h.left
  simp [← hn, Nat.mul_add, Nat.add_assoc, h.right]
  assumption

theorem self_mul_rem_div {a b c : Nat} (h: c < a) : (a * b + c) / a = b := by
  intros
  apply Eq.symm
  rw [div_exists]
  exists c
  apply Nat.lt_of_le_of_lt
  apply Nat.zero_le
  assumption

theorem le_mul_div {a b : Nat} : (a / b) * b ≤ a := by
  cases b
  simp
  case succ b =>
  let c := a / Nat.succ b
  have h := show c = a / Nat.succ b by rfl
  have g := h
  rw [div_exists] at g
  any_goals apply Nat.zero_lt_succ
  cases g with | intro x g =>
  cases g with | intro _ g =>
  rw [← g, self_mul_rem_div, Nat.mul_comm]
  apply Nat.le_add_right
  assumption

theorem div_lt_of_lt_mul {a b c : Nat} : 0 < c → a < b * c → a / c < b := by
  intros p q
  apply lt_of_mul_lt_mul_right _ p
  apply Nat.lt_of_le_of_lt _ q
  apply le_mul_div

theorem mod_eq_mod {a b : Nat} : a = b → ∀ c : Nat, a % c = b % c := by intro; simp[*]

theorem mod_exists {b : Nat} : 0 < b → ∀ a c : Nat, (c = a % b ↔ ∃ x, c < b ∧ b * x + c = a) := by
  intros lb a c
  apply Iff.intro
  intros
  exists (a / b)
  simp [*]
  apply And.intro
  apply Nat.mod_lt
  assumption
  apply Nat.div_add_mod
  induction a, b using Nat.mod.inductionOn with
  | base a b =>
    have h := show (a < b) by
      cases nat_trich a b with
      | inl => assumption
      | inr h => cases h with
        | inl h =>
          have _ := And.intro lb (Nat.le_of_eq h.symm)
          contradiction
        | inr h =>
          have _ := And.intro lb (Nat.le_of_lt h)
          contradiction
    intro g
    rw [Nat.mod_eq_of_lt h]
    cases g with | intro x g =>
    cases x with
    | zero =>
      simp at g
      exact g.right
    | succ x =>
      rw [← g.right, Nat.mul_succ] at h
      have h := Std.lt_of_add_lt_add_right (Std.lt_add_right h _)
      have h := Std.lt_of_add_lt_add_left (Std.lt_add_left h _)
      simp at h
  | ind a b g h =>
    intro f
    rw [Nat.mod_eq]
    simp [g]
    apply h
    repeat assumption
    cases f with | intro x f =>
    cases f with | intro lc f =>
    cases x with
    | zero =>
      simp at f
      simp [f] at lc
      have _ := Nat.lt_irrefl b (Nat.lt_of_le_of_lt g.right lc)
      contradiction
    | succ x =>
      exists x
      apply And.intro
      assumption
      simp [← f, Nat.mul_succ, Nat.add_right_comm _ b, Nat.add_sub_cancel]

theorem mod_mod_self {a b: Nat} : a % b = a % b % b := by
  cases b with
  | zero => repeat (rw [Nat.mod_eq]; simp)
  | succ b =>
    rw [mod_exists]
    exists 0
    apply And.intro
    apply Nat.mod_lt
    any_goals apply Nat.zero_lt_succ _
    simp

theorem mod_add_mod {a b c : Nat} : (a + b) % c = (a % c + b % c) % c := by
  cases c with
  | zero => repeat (rw [Nat.mod_eq]; simp)
  | succ c =>
    have h := mod_exists (Nat.zero_lt_succ c)
    let n := a % (Nat.succ c)
    let m := b % (Nat.succ c)
    have ha := h a n
    simp at ha
    have hb := h b m
    simp at hb
    cases ha with | intro xa ha =>
    cases hb with | intro xb hb =>
    cases le_or_lt (Nat.succ c) (a % (Nat.succ c) + b % (Nat.succ c)) with
    | inl g =>
      rw [Nat.mod_eq (a % (Nat.succ c) + b % (Nat.succ c))]
      simp [Nat.zero_lt_succ c, g]
      have f := show a % (Nat.succ c) + b % (Nat.succ c) - (Nat.succ c) < (Nat.succ c) by
        apply @Std.lt_of_add_lt_add_left (Nat.succ c)
        rw [← Nat.add_sub_assoc g, Nat.add_comm, Nat.add_sub_cancel]
        apply Nat.add_lt_add
        any_goals apply Nat.mod_lt
        any_goals apply Nat.zero_lt_succ
      rw [Nat.mod_eq_of_lt f]
      apply Eq.symm
      rw [mod_exists (Nat.zero_lt_succ c)]
      exists Nat.succ (xa + xb)
      apply And.intro
      assumption
      rw [
        Nat.mul_succ,
        Nat.mul_add,
        ← Nat.add_sub_assoc,
        ← Nat.add_assoc,
        Nat.add_right_comm _ (Nat.succ c),
        Nat.add_right_comm _ (Nat.succ c),
        Nat.add_sub_cancel,
        Nat.add_assoc,
        Nat.add_right_comm,
        ← Nat.add_assoc,
        ha.right,
        Nat.add_assoc,
        ← Std.add_left_cancel_iff,
        Nat.add_comm,
        hb.right
      ]
      assumption
    | inr g =>
      rw [Nat.mod_eq (a % (Nat.succ c) + b % (Nat.succ c))]
      have g := show ¬ (Nat.succ c ≤ a % Nat.succ c + b % Nat.succ c) by
        intro
        apply Nat.lt_irrefl (Nat.succ c)
        apply Nat.lt_of_le_of_lt
        repeat assumption
      simp [Nat.zero_lt_succ c, g]
      apply Eq.symm
      rw [h]
      exists (xa + xb)
      apply And.intro
      assumption
      rw [Nat.mul_add,
          Nat.add_right_comm,
          ← Nat.add_assoc,
          ha.right,
          Nat.add_assoc,
          ← Std.add_left_cancel_iff,
          Nat.add_comm,
          hb.right]

theorem self_mul_mod {a b : Nat} : a * b % a = 0 := by
  cases a
  simp
  case succ a =>
  apply Eq.symm
  rw [mod_exists]
  exists b
  simp
  repeat apply Nat.zero_lt_succ

theorem mul_self_mod {a b : Nat} : b * a % a = 0 := by
  rw [Nat.mul_comm]
  apply self_mul_mod

theorem self_mod {a : Nat} : a % a = 0 := by
  rw [show a % a = (1 * a) % a by simp [Nat.one_mul]]
  apply mul_self_mod

theorem self_mul_add_mod {a b c: Nat} : (a * b + c) % a = c % a := by
  simp [mod_add_mod, self_mul_mod, ← mod_mod_self]

theorem mod_mul {a b c : Nat} : 0 < b → 0 < c → a % (b * c) = (a / b % c) * b + (a % b) := by
  intros p q
  let m := a % b
  let n := (a / b) % c
  have mh := show m = a % b by rfl
  have nh := show n = (a / b) % c by rfl
  cases (mod_exists p _ _).mp mh with | intro x h =>
  cases (mod_exists q _ _).mp nh with | intro y g =>
  cases h with | intro lb h =>
  cases g with | intro lc g =>
  simp
  apply Eq.symm
  rw [mod_exists]
  exists y
  apply And.intro
  rw [← nh, ← mh]
  apply Nat.lt_of_succ_le
  rw [← Nat.add_succ]
  apply @Nat.le_of_add_le_add_right _ b _
  rw [Nat.add_right_comm, ← Nat.succ_mul]
  apply Nat.add_le_add
  rw [Nat.mul_comm]
  apply Nat.mul_le_mul_left
  apply Nat.le_of_lt_succ
  apply Nat.succ_lt_succ
  assumption
  apply Nat.le_of_lt_succ
  apply Nat.succ_lt_succ
  assumption
  rw [← nh, ← mh, ← Nat.add_assoc, Nat.mul_comm _ b, Nat.mul_assoc, ← Nat.mul_add b, g, mh]
  apply Nat.div_add_mod
  apply Nat.mul_pos
  repeat assumption

theorem mod_mul_mod {a b c: Nat} : a % (b * c) % b = a % b := by
  cases c
  all_goals cases b
  repeat (simp; rw [Nat.mod_eq _ 0]; simp)
  rw [mod_mul, mod_add_mod, mul_self_mod]
  simp
  repeat rw [← mod_mod_self]
  repeat apply Nat.zero_lt_succ

theorem mod_of_mul_mod_left {a b c d: Nat} : a % (c * d) = b % (c * d) → a % c = b % c := by
  intros
  rw [← mod_mul_mod, ← @mod_mul_mod b]
  apply mod_eq_mod
  assumption

theorem div_div_of_div_mul_pos {a b c : Nat} : 0 < b → 0 < c → a / b / c = a / (b * c) := by
  intros p q
  apply mul_right_cancel
  apply q
  rw [add_left_cancel_iff _ _ ((a / b) % c),
      Nat.add_comm,
      Nat.mul_comm,
      Nat.div_add_mod]
  apply mul_right_cancel
  apply p
  rw [add_left_cancel_iff _ _ (a % b),
      Nat.add_comm,
      Nat.mul_comm,
      Nat.div_add_mod,
      Nat.add_mul,
      ← Nat.add_assoc,
      Nat.add_comm,
      ← Nat.add_assoc,
      Nat.add_right_comm,
      Nat.add_assoc,
      ← mod_mul,
      Nat.mul_assoc,
      Nat.mul_comm,
      Nat.mul_comm c,
      Nat.div_add_mod]
  repeat assumption

theorem div_div_of_div_mul {a b c : Nat} : a / b / c = a / (b * c) := by
  cases b
  all_goals cases c
  all_goals simp
  any_goals rw [Nat.div_eq _ 0]
  any_goals simp
  any_goals rw [Nat.div_eq _ 0]
  any_goals rw [Nat.div_eq 0 _]
  any_goals simp
  apply div_div_of_div_mul_pos
  repeat apply Nat.zero_lt_succ 

theorem mod_mul_div_pos {a b c : Nat} :
    0 < c → 0 < b → a % (b * c) / c = (a / c) % b := by
  intros g h
  rw [Nat.mul_comm,
      mod_mul g h,
      Nat.mul_comm,
      self_mul_rem_div (Nat.mod_lt a g)]

theorem mod_mul_div {a b c : Nat} : a % (b * c) / c = (a / c) % b := by
  cases b
  simp
  repeat (rw [Nat.mod_eq _ 0]; simp)
  cases c
  simp
  repeat (rw [Nat.div_eq _ 0]; simp)
  apply mod_mul_div_pos
  repeat (apply Nat.zero_lt_succ _)

theorem mod_div_self {a b : Nat} : a % b / b = 0 := by
  apply show (a % (1 * b) / b = 0 → a % b / b = 0) by simp; intro; assumption
  rw [mod_mul_div, Nat.mod_one]

theorem mod_add_mod_self {a b c : Nat} : (a % b + c) % b = (a + c) % b := by
  rw [mod_add_mod, ← mod_mod_self, ← mod_add_mod]

end Std
end Complexity