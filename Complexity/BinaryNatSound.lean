import Complexity.Std
import Complexity.StdComp
import Complexity.StdMul
import Complexity.StdDiv
import Complexity.StdPow
import Complexity.Cost
import Complexity.BinaryNat

namespace Complexity
namespace BinaryNat

open CostedBinaryNat

theorem toNat_bound (x : BinaryNat n) : toNat x < 2^2^n := by
  induction x with
  | bit_false => simp
  | bit_true => simp
  | intro y z hy hz =>
    have r := show (bound (intro y z) = bound y ^ 2) by simp[bound, bits, height, Nat.pow_succ, ← Std.pow_pow, Nat.pow_zero]
    simp at r
    rw [toNat, r, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    simp
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
    cases x
    any_goals cases y
    any_goals simp
    any_goals simp [toNat] at p
  | succ n h  =>
    cases x with | intro ux lx =>
    cases y with | intro uy ly =>
    simp [toNat] at p
    simp
    apply And.intro
    all_goals apply h
    have p := Std.div_eq_div p (bound lx)
    simp at p
    rw [Std.self_mul_rem_div,
        Std.self_mul_rem_div] at p
    assumption
    any_goals apply toNat_bound
    have p := Std.mod_eq_mod p (bound lx)
    simp at p
    rw [Std.mod_add_mod,
        Std.self_mul_mod,
        @Std.mod_add_mod _ (toNat ly),
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
    exists BinaryNat.bit_false
    simp [toNat, *]
    exists BinaryNat.bit_true
    simp [toNat, *]
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
    apply Iff.intro
    all_goals intro p
    all_goals simp [ofNat, Nat.pow_zero, Nat.pow_succ] at p
    all_goals simp[ofNat, Nat.pow_zero, Nat.pow_succ, p]
    cases (Std.zero_or_one_lt_two (a%2)).mpr (@Nat.mod_lt a 2 (by simp))
    all_goals cases (Std.zero_or_one_lt_two (b%2)).mpr (@Nat.mod_lt b 2 (by simp))
    all_goals simp[*] at *
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
    cases x
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
    cases x
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
  rw [← Nat.mod_eq_of_lt (toNat_bound _), ofNat_cancel, ofNat_toNat]

theorem ofNat_intro {n : Nat} {a b : Nat} :
    BinaryNat.intro (ofNat n a) (ofNat n b) = ofNat (n + 1) (2 ^ 2 ^ n * a + b % 2 ^ 2 ^ n) := by
  rw [toNat_cancel]
  simp [toNat, toNat_ofNat, bound, height, bits]
  rw [Std.self_mul_rem_div, Std.self_mul_add_mod, ← Std.mod_mod_self]
  apply Nat.mod_lt
  apply Nat.pos_pow_of_pos
  simp

@[simp]
def UncostedToNat {n : Nat} (x : BinaryNat n) : Costed Nat := do return toNat x

theorem ite_true : CostedBinaryNat.ite (BinaryNat.bit_true) (t : Costed α) (f : Costed α) ≈ t := by simp [CostedBinaryNat.ite]

theorem ite_false : CostedBinaryNat.ite (BinaryNat.bit_false) (t : Costed α) (f : Costed α) ≈ f := by simp [CostedBinaryNat.ite]

theorem zero_ofNat {n : Nat}: (zero n) ≈ Cost.pure (ofNat n 0) := by
   induction n with
   | zero => simp[zero, ofNat, bit_zero]
   | succ n h =>
     simp [zero, ofNat, Bind.bind, CostedBinaryNat.intro, Std.zero_div, h]
     rw [h]
     simp

theorem extend_ofNat {n m: Nat} (x : BinaryNat m) : (extend n x) ≈ Cost.pure (ofNat (m + n) (toNat x)) := by
  induction n generalizing m with
  | zero =>
    simp [extend, ofNat_toNat]
  | succ n h =>
    simp [extend, ofNat_toNat, Bind.bind, CostedBinaryNat.intro, ofNat_toNat]
    rw [h, zero_ofNat]
    simp
    intro
    rw [@ofNat_intro (m + n)]
    rw [show ofNat (m + n + 1) = ofNat (m + Nat.succ n) by simp[← Nat.succ_eq_add_one, Nat.add_succ]]
    simp
    rw [Nat.mod_eq_of_lt]
    apply Nat.lt_of_lt_of_le
    apply toNat_bound
    simp
    apply Nat.pow_le_pow_of_le_right
    any_goals apply Nat.pow_le_pow_of_le_right
    repeat simp
    apply Nat.le_add_right

theorem add_with_carry_ofNat (x y : BinaryNat n) (z : BinaryNat 0) :
    (add_with_carry x y z) ≈ Cost.pure
      (ofNat _ ((toNat x + toNat y + toNat z) / 2 ^ 2 ^ n),
       ofNat _ ((toNat x + toNat y + toNat z) % 2 ^ 2 ^ n)) := by
  induction n generalizing z with
  | zero =>
    cases x <;> cases y <;> cases z <;>
    simp [Bind.bind,
      add_with_carry, bit_zero, bit_one, CostedBinaryNat.ite, ofNat_toNat, toNat, ofNat,
      Std.zero_div]
  | succ n h =>
    rw [add_with_carry]
    simp
    repeat rw [Bind.bind]
    rw [Monad.toBind, Cost.instMonadCosted]
    cases x with | intro xu xl =>
    cases y with | intro yu yl =>
    repeat rw [split]
    simp
    rw [CostedBinaryNat.intro]
    repeat rw[h]
    simp [toNat_ofNat, ← ofNat_cancel, toNat, ofNat_intro]
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
    repeat rw [reorder]
    rw [Nat.pow_zero, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul,
      ← Std.pow_pow, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    rw [Nat.mod_eq_of_lt (sum_small _ xl _ _), ← Std.div_div_of_div_mul, Std.self_mul_div (bound_lt _)]
    intro
    apply And.intro
    rfl
    rw [← Std.mod_mod_self, ← Std.mod_mod_self]
    rw [← Std.mod_add_mod_self]
    rw [Std.mul_mod_mod_mul_pos (bound_lt _) (bound_lt _)]
    rw [Std.mod_add_mod_self]
    rw [Nat.mul_add]
    simp [Nat.add_assoc]
    rw [Nat.div_add_mod]
    





    -- (bound * ((U + L / bound) % bound) + L % bound) % (bound * bound)
    -- (bound * U + bound * (L / bound) + L % bound)









-- theorem add_with_carry_toNat (x y : BinaryNat n) (z : BinaryNat 0) :
--     (add_with_carry c x y z).snd = (
--       ofNat _ ((toNat x + toNat y + toNat z) / 2 ^ 2 ^ n),
--       ofNat _ ((toNat x + toNat y + toNat z) % 2 ^ 2 ^ n)
--     ) := by
--     induction n generalizing c z with
--     | zero =>
--       cases x with | bit a =>
--       cases y with | bit b =>
--       cases z with | bit c =>
--       cases a
--       all_goals cases b
--       all_goals cases c
--       all_goals simp [add_with_carry, toNat, ofNat]
--     | succ n h =>
--       cases x with | intro xu xl =>
--       cases y with | intro yu yl =>
--       have bound_lt := show ∀ n : Nat, 0 < 2 ^ 2 ^ n by intros; apply Nat.pos_pow_of_pos; simp
--       have sum_small := show (∀ n, ∀ (x y : BinaryNat n) (z : BinaryNat 0), (toNat x + toNat y + toNat z) / 2 ^ 2 ^ n < 2) by
--         intros n x y z
--         apply Std.div_lt_of_lt_mul (bound_lt _)
--         rw [Nat.succ_mul, Nat.one_mul, Nat.add_assoc]
--         apply Std.add_lt_add_le
--         apply toNat_bound
--         apply Nat.le_of_lt_succ
--         rw [Nat.succ_eq_add_one]
--         apply Std.add_lt_add_le
--         apply toNat_bound
--         apply Nat.le_of_lt_succ
--         apply toNat_bound
--       have ifMod2 := show (∀ a, a % 2 = (if a % 2 = 1 then 1 else 0)) by
--         intro a
--         split
--         assumption
--         apply Std.zero_of_lt_two_ne_one
--         apply Nat.mod_lt
--         simp
--         assumption
--       have reorder := show ∀ n : Nat, n * toNat xu + toNat xl + (n * toNat yu + toNat yl) + toNat z
--           = n * (toNat xu + toNat yu) + (toNat xl + toNat yl + toNat z) by
--         intro n
--         simp [← Std.add_left_cancel_iff, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm]
--       simp [add_with_carry, h,
--           ← ofNat_cancel, ofNat_intro, toNat_ofNat, toNat,
--           ← ifMod2, reorder, bound, bits, height,
--           Nat.pow_succ, Nat.pow_zero, ← Std.pow_pow,
--           ← Std.div_div_of_div_mul, Std.self_mul_div (bound_lt _),
--           Std.self_mul_add_mod, ← Std.mod_mod_self]
--       simp [Nat.mod_eq_of_lt (sum_small _ xl _ _),
--             Std.mod_mul (bound_lt _) (bound_lt _),
--             Std.self_mul_div (bound_lt _), Std.mod_div_self,
--             Std.self_mul_add_mod, ← Std.mod_mod_self]

-- theorem add_toNat {x y : BinaryNat n}: (add c x y).snd = ofNat _ (toNat x + toNat y) := by
--   simp [add, add_with_carry_toNat, ← ofNat_cancel, zero_toNat, ← Std.mod_mod_self]

-- theorem toNat_add {x y : BinaryNat n}: toNat (add c x y).snd = (toNat x + toNat y) % 2 ^ 2 ^ n := by
--   rw [← @Nat.mod_eq_of_lt (toNat (add c x y).snd), ofNat_cancel, ofNat_toNat]
--   apply add_toNat
--   apply toNat_bound

-- theorem add_complement (x : BinaryNat n) :
--     (add_with_carry c0 x (complement c1 x).snd (bit_one c2).snd).snd = ((bit_one c3).snd, (zero c3 _).snd)  := by
--   have lemma := show (∀ n : Nat, ∀ x : BinaryNat n,
--       (∀ c0 c1 c2 c3, (add_with_carry c0 x (complement c1 x).snd (bit_one c2).snd).snd.fst = (bit_one c3).snd)
--       ∧ (∀ c3 c0 c1 c2, (add_with_carry c0 x (complement c1 x).snd (bit_one c2).snd).snd.snd = (zero c3 _).snd)) by
--     intro n
--     induction n with
--     | zero =>
--       intro x
--       cases x with | bit b =>
--       cases b
--       all_goals simp [add_with_carry, bit_one, bit_zero, complement, zero]
--     | succ n h =>
--       intro x
--       cases x with | intro xu xl =>
--       simp [add_with_carry, complement]
--       apply And.intro
--       intros c0 c1 c2 c3
--       rw [(h xl).left, (h xu).left]
--       apply Cost.init
--       intros c0 c1 c2 c3
--       rw [(h xl).left, (h xl).right c0, (h xu).right c0]
--       simp [zero]
--       apply Cost.init
--   rw [<- (lemma n x).left c0 c1 c2 c3, <- (lemma n x).right c3 c0 c1 c2]

-- theorem complement_toNat (x: BinaryNat n) : toNat (complement c x).snd = (bound x) - (toNat x) - 1 := by
--   rw [← Nat.sub_add_eq,
--       @Std.add_left_cancel_iff _ _ (toNat x + 1),
--       Nat.add_comm _ (bound x - (toNat x + 1)),
--       Nat.sub_add_cancel,
--       Nat.add_right_comm]
--   apply show (∀ a b : Nat,
--       (ofNat 0 (a / 2 ^ 2 ^ n), ofNat n (a % 2 ^ 2 ^ n)) = (ofNat 0 (b / 2 ^ 2 ^ n), ofNat n (b % 2 ^ 2 ^ n))
--       → (a < 2 ^ 2 ^ n + 2 ^ 2 ^ n)
--       → (b < 2 ^ 2 ^ n + 2 ^ 2 ^ n)
--       -> a = b) by
--     have power_two_pos := show 0 < 2 ^ 2 ^ n by apply Nat.pos_pow_of_pos; simp
--     simp [← ofNat_cancel, show 2 ^ 2 ^ n + 2 ^ 2 ^ n = 2 ^ 2 ^ n * 2 by simp[Nat.mul_succ], ← Std.mod_mod_self]
--     intros a b p q r
--     cases p with | intro pl pr =>
--     rw [← Nat.mod_eq_of_lt q, ← Nat.mod_eq_of_lt r]
--     simp [Std.mod_mul power_two_pos]
--     apply show (∀ a b c d, a = b → c = d → a + c = b + d) by intros; simp[*]
--     rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at pl
--     rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
--     apply Std.mul_eq_mul
--     any_goals rfl
--     any_goals apply Std.div_lt_of_lt_mul power_two_pos
--     any_goals rw[Nat.mul_comm]
--     any_goals assumption
--     all_goals apply Nat.lt_of_lt_of_le _ n_zero
--   rw [show 1 = toNat (bit_one Cost.init).snd by simp[toNat],
--       ← add_with_carry_toNat, add_complement,
--       bound, bits, height,
--       Nat.div_eq, Nat.mod_eq]
--   simp [show 0 < 2 ^ 2 ^ n by apply Nat.pos_pow_of_pos; simp, Std.self_div, Std.self_mod,
--       toNat_cancel, zero_toNat, toNat, bit_one, toNat_ofNat,
--       Std.zero_div]
--   repeat apply Cost.init
--   rw [Nat.add_assoc]
--   apply Std.add_lt_add_le
--   any_goals (
--     apply Nat.le_of_lt_succ;
--     rw [← Nat.succ_eq_add_one];
--     apply Nat.succ_lt_succ)
--   any_goals rw [bound, bits, height]
--   any_goals apply toNat_bound
--   rw [← Nat.add_zero (2 ^ 2 ^ n)]
--   apply Std.add_le_add_lt
--   simp
--   simp
--   apply Nat.pos_pow_of_pos
--   simp

-- theorem sub_iff_add (x y z : BinaryNat n) : (add c0 x y).snd = z ↔ x = (sub c1 z y).snd := by
--   apply Iff.intro
--   all_goals intro p
--   have p := p.symm
--   all_goals simp [p, sub, add,
--       add_with_carry_toNat, complement_toNat, toNat_ofNat,
--       ← Std.mod_mod_self, zero_toNat, toNat, Nat.add_assoc, Std.mod_add_mod_self]
--   rw [Nat.add_left_comm (toNat y)]
--   any_goals rw [Nat.add_comm 1]
--   all_goals rw [← Nat.sub_add_eq, Nat.sub_add_cancel]
--   any_goals rw [Nat.add_comm, ← Nat.mul_one (bound y), bound, bits, height,
--                 Std.self_mul_add_mod, Nat.mod_eq_of_lt, ofNat_toNat]
--   any_goals rw [← Nat.succ_eq_add_one, bound, bits, height]
--   any_goals apply Nat.le_of_lt_succ
--   any_goals apply Nat.succ_lt_succ
--   all_goals apply toNat_bound

end BinaryNat
end Complexity