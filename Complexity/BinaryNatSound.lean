import Complexity.Std
import Complexity.StdComp
import Complexity.StdDiv
import Complexity.BinaryNat

namespace Complexity
namespace BinaryNat

theorem toNat_bound (x : BinaryNat α) : toNat x < (bound x) := by
  induction x with
  | bit b => cases b <;> simp
  | intro y z hy hz =>
    have q := show (bound z = bound y) by simp[bound, bits, height]
    have r := show (bound (intro y z) = bound y ^ 2) by simp[bound, bits, height, Nat.pow_succ, ← Std.pow_pow, Nat.pow_zero]
    rw [q] at hz
    rw [toNat, q, r, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    apply Nat.lt_of_lt_of_le
    apply Nat.add_lt_add_left hz
    rw [← Nat.mul_succ]
    apply Nat.mul_le_mul
    simp
    apply Nat.le_of_lt_succ
    apply Nat.succ_lt_succ
    apply hy

theorem intro_bound {n a b : Nat} : (a < 2 ^ 2 ^ n) → (b < 2 ^ 2 ^ n) → (2 ^ 2 ^ n * a + b < 2 ^ 2 ^ Nat.succ n) := by
  intros
  apply Nat.lt_of_succ_le
  rw [Nat.succ_eq_add_one, Nat.add_assoc]
  simp [Nat.pow_succ, ← Std.pow_pow, Nat.pow_zero]
  apply @Nat.le_trans _ (2 ^ 2 ^ n * a + 2 ^ 2 ^ n)
  apply Nat.add_le_add
  apply Nat.le_refl
  apply Nat.le_of_lt_succ
  rw [← Nat.succ_eq_add_one]
  apply Nat.succ_lt_succ
  assumption
  rw [← Nat.mul_succ]
  apply Nat.mul_le_mul
  apply Nat.le_refl
  apply Nat.le_of_lt_succ
  apply Nat.succ_lt_succ
  assumption

theorem toNat_cancel {x y : BinaryNat n} : x = y ↔ toNat x = toNat y := by
  apply Iff.intro
  all_goals intro p
  simp [p]
  induction n with
  | zero =>
    cases x with | bit b =>
    cases y with | bit c =>
    cases b
    any_goals cases c
    any_goals simp
    any_goals simp [toNat] at p
  | succ n h  =>
    cases x with | intro ux lx =>
    cases y with | intro uy ly =>
    have r := show bound ly = bound lx by simp [bound, bits, height]
    simp [toNat] at p
    simp
    apply And.intro
    all_goals apply h
    have p := Std.div_eq_div p (bound lx)
    rw [Std.self_mul_rem_div,
        r,
        Std.self_mul_rem_div] at p
    assumption
    any_goals apply toNat_bound
    have p := Std.mod_eq_mod p (bound lx)
    rw [Std.mod_add_mod,
        Std.self_mul_mod,
        @Std.mod_add_mod _ (toNat ly),
        r,
        Std.self_mul_mod,
        Nat.mod_eq_of_lt,
        Nat.mod_eq_of_lt,
        Nat.mod_eq_of_lt,
        Nat.mod_eq_of_lt] at p
    simp at p
    any_goals simp
    any_goals apply toNat_bound
    any_goals apply Nat.mod_lt
    any_goals apply Nat.pos_pow_of_pos
    any_goals simp
    assumption

theorem toNat_exists {n a : Nat} : (a < 2 ^ 2 ^ n) → (∃ x : BinaryNat n, toNat x = a) := by
  induction n generalizing a with
  | zero =>
    simp [Nat.pow_zero, Nat.pow_succ]
    intro p
    rw [← Std.zero_or_one_lt_two] at p
    cases p
    exists BinaryNat.bit false
    simp [toNat, *]
    exists BinaryNat.bit true
    simp [toNat, bit_one, *]
  | succ n h =>
    cases h (show a % 2 ^ 2 ^ n < 2 ^ 2 ^ n by apply Nat.mod_lt; apply Nat.pos_pow_of_pos; simp) with | intro xl hl =>
    intro p
    have hu := show a / 2 ^ 2 ^ n < 2 ^ 2 ^ n by
      apply Std.div_lt_of_lt_mul
      apply Nat.pos_pow_of_pos
      simp
      simp [Nat.pow_succ, ← Std.pow_pow, Nat.pow_zero] at p
      assumption
    cases h hu with | intro xu hu =>
    exists BinaryNat.intro xu xl
    simp [toNat, hu, hl, bound, bits, height]
    apply Nat.div_add_mod

theorem ofNat_cancel {n a b : Nat} : (a % 2 ^ 2 ^ n = b % 2 ^ 2 ^ n ↔ ofNat n a = ofNat n b) := by
  induction n generalizing a b with
  | zero =>
    have q := show ((a % 2 == 1) = (b % 2 == 1) → a % 2 = b % 2) by
      have qa := Nat.mod_lt a (show 2 > 0 by simp)
      have qb := Nat.mod_lt b (show 2 > 0 by simp)
      rw [← Std.zero_or_one_lt_two] at *
      cases qa
      all_goals cases qb
      all_goals simp[*]
    apply Iff.intro
    all_goals intro p
    all_goals simp [ofNat, Nat.pow_zero, Nat.pow_succ] at p
    all_goals simp[ofNat, Nat.pow_zero, Nat.pow_succ, p]
    apply q
    assumption
  | succ n h =>
    simp [Nat.pow_succ, ← Std.pow_pow, Nat.pow_zero, ofNat, ← h, ← Std.mod_mul_div, ← Std.mod_mod_self]
    apply Iff.intro
    all_goals intro p
    simp [p]
    apply Std.mod_of_mul_mod_left
    assumption
    rw [Std.mod_mul, Std.mod_mul]
    simp [← Std.mod_mul_div, p]
    all_goals apply Nat.pos_pow_of_pos
    all_goals simp
    
theorem ofNat_exists {n : Nat} (x : BinaryNat n) : ∃ a : Nat, ofNat n a = x := by
  induction n with
  | zero =>
    cases x with | bit b =>
    cases b
    exists 0
    exists 1
  | succ n h =>
    cases x with | intro xu xl =>
    cases h xu with | intro au hu =>
    cases h xl with | intro al hl =>
    exists (bound xl) * au + al % (bound xl)
    simp [ofNat, ← hu, ← hl, bound, bits, height, ← ofNat_cancel]
    rw [Std.mod_add_mod, Std.self_mul_div]
    simp [Std.self_mul_mod, ← Std.mod_mod_self, Std.mod_div_self]
    all_goals apply Nat.pos_pow_of_pos
    all_goals simp

theorem ofNat_mul {n : Nat} (a b : Nat) : ofNat n (2 ^ 2 ^ n * a + b) = ofNat n b := by
  rw [← ofNat_cancel, Std.self_mul_add_mod]

theorem ofNat_toNat (x : BinaryNat n): ofNat n (toNat x) = x := by
  induction n with
  | zero =>
    cases x with | bit b =>
    cases b
    all_goals simp [toNat, ofNat]
  | succ n h =>
    cases x
    simp [ofNat, toNat, bound, bits, height]
    apply And.intro
    rw [Std.self_mul_rem_div]
    apply h
    apply toNat_bound
    simp [show ∀ n, ofNat (Nat.add n 0) = ofNat n by simp] at *
    rw [ofNat_mul, h]

theorem toNat_ofNat (n a : Nat) : toNat (ofNat n a) = a % 2 ^ 2 ^ n := by
  rw [← Nat.mod_eq_of_lt (toNat_bound _), bound, bits, height, ofNat_cancel, ofNat_toNat]


theorem ofNat_intro {n : Nat} (a b : Nat) :
    BinaryNat.intro (ofNat n a) (ofNat n b) = ofNat (n + 1) (2 ^ 2 ^ n * a + b % 2 ^ 2 ^ n) := by
  rw [toNat_cancel]
  simp [toNat, toNat_ofNat, bound, height, bits]
  rw [Std.self_mul_rem_div, Std.self_mul_add_mod, ← Std.mod_mod_self]
  apply Nat.mod_lt
  apply Nat.pos_pow_of_pos
  simp

theorem ite_true : ite (BinaryNat.bit true) (t : α) (f : α) = t := by simp [ite]
theorem ite_false : ite (BinaryNat.bit false) (t : α) (f : α) = f := by simp [ite]

theorem zero_toNat {n : Nat}: ∀ c : Cost, toNat (zero c n).snd = 0 := by
  induction n <;> simp [toNat, zero, *]

theorem extend_toNat {n m: Nat} (x : BinaryNat m): toNat (extend c n x).snd = toNat x := by
  induction n generalizing c m <;> simp [toNat, extend, @zero_toNat (m + _), *]

theorem add_with_carry_toNat (x y : BinaryNat n) (z : BinaryNat 0) :
    (add_with_carry c x y z).snd = (
      ofNat _ ((toNat x + toNat y + toNat z) / 2 ^ 2 ^ n),
      ofNat _ ((toNat x + toNat y + toNat z) % 2 ^ 2 ^ n)
    ) := by
    induction n generalizing c z with
    | zero =>
      cases x with | bit a =>
      cases y with | bit b =>
      cases z with | bit c =>
      cases a
      all_goals cases b
      all_goals cases c
      all_goals simp [add_with_carry, toNat, ofNat]
    | succ n h =>
      cases x with | intro xu xl =>
      cases y with | intro yu yl =>
      have bound_lt := show ∀ n : Nat, 0 < 2 ^ 2 ^ n by intros; apply Nat.pos_pow_of_pos; simp
      have sum_small := show (∀ n, ∀ (x y : BinaryNat n) (z : BinaryNat 0), (toNat x + toNat y + toNat z) / 2 ^ 2 ^ n < 2) by
        intros n x y z
        apply Std.div_lt_of_lt_mul (bound_lt _)
        rw [Nat.succ_mul, Nat.one_mul, Nat.add_assoc]
        apply Std.add_lt_add_le
        apply toNat_bound
        apply Nat.le_of_lt_succ
        rw [Nat.succ_eq_add_one]
        apply Std.add_lt_add_le
        apply toNat_bound
        apply Nat.le_of_lt_succ
        apply toNat_bound
      have ifMod2 := show (∀ a, a % 2 = (if a % 2 = 1 then 1 else 0)) by
        intro a
        split
        assumption
        apply Std.zero_of_lt_two_ne_one
        apply Nat.mod_lt
        simp
        assumption
      have reorder := show ∀ n : Nat, n * toNat xu + toNat xl + (n * toNat yu + toNat yl) + toNat z
          = n * (toNat xu + toNat yu) + (toNat xl + toNat yl + toNat z) by
        intro n
        simp [← Std.add_left_cancel_iff, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm]
      simp [add_with_carry, h,
          ← ofNat_cancel, ofNat_intro, toNat_ofNat, toNat,
          ← ifMod2, reorder, bound, bits, height,
          Nat.pow_succ, Nat.pow_zero, ← Std.pow_pow,
          ← Std.div_div_of_div_mul, Std.self_mul_div (bound_lt _),
          Std.self_mul_add_mod, ← Std.mod_mod_self]
      simp [Nat.mod_eq_of_lt (sum_small _ xl _ _),
            Std.mod_mul (bound_lt _) (bound_lt _),
            Std.self_mul_div (bound_lt _), Std.mod_div_self,
            Std.self_mul_add_mod, ← Std.mod_mod_self]

theorem add_toNat {x y : BinaryNat n}: (add c x y).snd = ofNat _ (toNat x + toNat y) := by
  simp [add, add_with_carry_toNat, ← ofNat_cancel, zero_toNat, ← Std.mod_mod_self]

theorem toNat_add {x y : BinaryNat n}: toNat (add c x y).snd = (toNat x + toNat y) % 2 ^ 2 ^ n := by
  rw [← @Nat.mod_eq_of_lt (toNat (add c x y).snd), ofNat_cancel, ofNat_toNat]
  apply add_toNat
  apply toNat_bound

theorem add_complement (x : BinaryNat n) :
    (add_with_carry c0 x (complement c1 x).snd (bit_one c2).snd).snd = ((bit_one c3).snd, (zero c3 _).snd)  := by
  have lemma := show (∀ n : Nat, ∀ x : BinaryNat n,
      (∀ c0 c1 c2 c3, (add_with_carry c0 x (complement c1 x).snd (bit_one c2).snd).snd.fst = (bit_one c3).snd)
      ∧ (∀ c3 c0 c1 c2, (add_with_carry c0 x (complement c1 x).snd (bit_one c2).snd).snd.snd = (zero c3 _).snd)) by
    intro n
    induction n with
    | zero =>
      intro x
      cases x with | bit b =>
      cases b
      all_goals simp [add_with_carry, bit_one, bit_zero, complement, zero]
    | succ n h =>
      intro x
      cases x with | intro xu xl =>
      simp [add_with_carry, complement]
      apply And.intro
      intros c0 c1 c2 c3
      rw [(h xl).left, (h xu).left]
      apply Cost.init
      intros c0 c1 c2 c3
      rw [(h xl).left, (h xl).right c0, (h xu).right c0]
      simp [zero]
      apply Cost.init
  rw [<- (lemma n x).left c0 c1 c2 c3, <- (lemma n x).right c3 c0 c1 c2]

theorem complement_toNat (x: BinaryNat n) : toNat (complement c x).snd = (bound x) - (toNat x) - 1 := by
  rw [← Nat.sub_add_eq,
      @Std.add_left_cancel_iff _ _ (toNat x + 1),
      Nat.add_comm _ (bound x - (toNat x + 1)),
      Nat.sub_add_cancel,
      Nat.add_right_comm]
  apply show (∀ a b : Nat,
      (ofNat 0 (a / 2 ^ 2 ^ n), ofNat n (a % 2 ^ 2 ^ n)) = (ofNat 0 (b / 2 ^ 2 ^ n), ofNat n (b % 2 ^ 2 ^ n))
      → (a < 2 ^ 2 ^ n + 2 ^ 2 ^ n)
      → (b < 2 ^ 2 ^ n + 2 ^ 2 ^ n)
      -> a = b) by
    have power_two_pos := show 0 < 2 ^ 2 ^ n by apply Nat.pos_pow_of_pos; simp
    simp [← ofNat_cancel, show 2 ^ 2 ^ n + 2 ^ 2 ^ n = 2 ^ 2 ^ n * 2 by simp[Nat.mul_succ], ← Std.mod_mod_self]
    intros a b p q r
    cases p with | intro pl pr =>
    rw [← Nat.mod_eq_of_lt q, ← Nat.mod_eq_of_lt r]
    simp [Std.mod_mul power_two_pos]
    apply show (∀ a b c d, a = b → c = d → a + c = b + d) by intros; simp[*]
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at pl
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    apply Std.mul_eq_mul
    any_goals rfl
    any_goals apply Std.div_lt_of_lt_mul power_two_pos
    any_goals rw[Nat.mul_comm]
    any_goals assumption
    all_goals apply Nat.lt_of_lt_of_le _ n_zero
  rw [show 1 = toNat (bit_one Cost.init).snd by simp[toNat],
      ← add_with_carry_toNat, add_complement,
      bound, bits, height,
      Nat.div_eq, Nat.mod_eq]
  simp [show 0 < 2 ^ 2 ^ n by apply Nat.pos_pow_of_pos; simp, Std.self_div, Std.self_mod,
      toNat_cancel, zero_toNat, toNat, bit_one, toNat_ofNat,
      Std.zero_div]
  repeat apply Cost.init
  rw [Nat.add_assoc]
  apply Std.add_lt_add_le
  any_goals (
    apply Nat.le_of_lt_succ;
    rw [← Nat.succ_eq_add_one];
    apply Nat.succ_lt_succ)
  any_goals rw [bound, bits, height]
  any_goals apply toNat_bound
  rw [← Nat.add_zero (2 ^ 2 ^ n)]
  apply Std.add_le_add_lt
  simp
  simp
  apply Nat.pos_pow_of_pos
  simp

theorem sub_iff_add (x y z : BinaryNat n) : (add c0 x y).snd = z ↔ x = (sub c1 z y).snd := by
  apply Iff.intro
  all_goals intro p
  have p := p.symm
  all_goals simp [p, sub, add,
      add_with_carry_toNat, complement_toNat, toNat_ofNat,
      ← Std.mod_mod_self, zero_toNat, toNat, Nat.add_assoc, Std.mod_add_mod_self]
  rw [Nat.add_left_comm (toNat y)]
  any_goals rw [Nat.add_comm 1]
  all_goals rw [← Nat.sub_add_eq, Nat.sub_add_cancel]
  any_goals rw [Nat.add_comm, ← Nat.mul_one (bound y), bound, bits, height,
                Std.self_mul_add_mod, Nat.mod_eq_of_lt, ofNat_toNat]
  any_goals rw [← Nat.succ_eq_add_one, bound, bits, height]
  any_goals apply Nat.le_of_lt_succ
  any_goals apply Nat.succ_lt_succ
  all_goals apply toNat_bound

end BinaryNat
end Complexity