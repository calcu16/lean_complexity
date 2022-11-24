import Complexity.Std
import Std.Data.Nat.Lemmas

namespace Complexity

def le_big_o (a b : Nat → Nat) :=
  ∃ x0 c : Nat,
    ∀ x : Nat,
      ((x0 ≤ x) → (a x ≤ c * (b x)))

theorem le_big_o_refl (a : Nat → Nat) : (le_big_o a a) :=
  by exists 0
     exists 1
     intros
     simp

theorem le_big_o_trans (a b c : Nat → Nat) : (le_big_o a b → le_big_o b c → le_big_o a c) :=
  by intro p q
     cases p with | intro xp p =>
     cases p with | intro cp p =>
     cases q with | intro xq q =>
     cases q with | intro cq q =>
     cases Std.le_max xp xq with | intro x0 bounds =>
     exists x0
     exists cp * cq
     intro x
     cases bounds with | intro lxp lxq =>
     intro lx0
     have lxp := Nat.le_trans lxp lx0
     have lxq := Nat.le_trans lxq lx0
     have hp := p x lxp
     have hq := Nat.mul_le_mul_left cp (q x lxq)
     have goal := Nat.le_trans hp hq
     rw [Nat.mul_assoc]
     assumption

theorem le_big_o_add (a1 b1 a2 b2 : Nat → Nat) : (le_big_o a1 a2 → le_big_o b1 b2 → le_big_o (Std.fadd a1 b1) (Std.fadd a2 b2)) :=
  by intros la lb
     cases la with | intro xa la =>
     cases la with | intro ca la =>
     cases lb with | intro xb lb =>
     cases lb with | intro cb lb =>
     cases Std.le_max xa xb with | intro x0 bounds =>
     cases bounds with | intro lxa lxb =>
     cases Std.le_max ca cb with | intro c bounds =>
     cases bounds with | intro lca lcb =>
     exists x0
     exists c
     intro x
     intro lx0
     repeat rw [Std.fadd]
     rw [Nat.mul_add]
     apply Nat.add_le_add
     have lca := Nat.mul_le_mul lca (Nat.le_refl (a2 x))
     have la := la x (Nat.le_trans lxa lx0)
     apply Nat.le_trans la lca
     have lcb := Nat.mul_le_mul lcb (Nat.le_refl (b2 x))
     have lb := lb x (Nat.le_trans lxb lx0)
     apply Nat.le_trans lb lcb

theorem le_big_o_mul (a1 b1 a2 b2 : Nat → Nat): (le_big_o a1 a2 → le_big_o b1 b2 → le_big_o (Std.fmul a1 b1) (Std.fmul a2 b2)) :=
  by intros la lb    
     cases la with | intro xa la =>
     cases la with | intro ca la =>
     cases lb with | intro xb lb =>
     cases lb with | intro cb lb =>
     cases Std.le_max xa xb with | intro x0 bounds =>
     cases bounds with | intro lxa lxb =>
     exists x0
     exists ca * cb
     intro x
     intro lx0
     repeat rw [Std.fmul]
     rw [Nat.mul_assoc ca]
     rw [Nat.mul_left_comm cb]
     rw [← Nat.mul_assoc ca]
     apply Nat.mul_le_mul
     apply la
     apply Nat.le_trans lxa lx0
     apply lb
     apply Nat.le_trans lxb lx0    

def cong_big_o (a b : Nat → Nat) :=
  le_big_o a b ∧ le_big_o b a

theorem le_of_cong_big_o (a b : Nat → Nat) : cong_big_o a b → le_big_o a b := by
  intro p
  cases p
  assumption

theorem cong_big_o_refl (a : Nat → Nat) : (cong_big_o a a) :=
  by apply And.intro
     repeat (apply le_big_o_refl)
     
theorem cong_big_o_sym {a b : Nat → Nat} : (cong_big_o a b → cong_big_o b a) :=
  by intro q
     apply And.intro
     apply And.right
     apply q
     apply And.left
     apply q

theorem cong_big_o_trans {a b c : Nat → Nat} : (cong_big_o a b → cong_big_o b c → cong_big_o a c) :=
  by intro p q
     cases p
     cases q
     apply And.intro
     apply le_big_o_trans a b c
     assumption
     assumption
     apply le_big_o_trans c b a
     assumption
     assumption

theorem cong_big_o_equivalence : Equivalence cong_big_o :=
  .mk cong_big_o_refl cong_big_o_sym cong_big_o_trans

theorem cong_big_o_add (a1 b1 a2 b2 : Nat → Nat) : (cong_big_o a1 a2 → cong_big_o b1 b2 → cong_big_o (Std.fadd a1 b1) (Std.fadd a2 b2)) :=
  by intro p
     intro q
     cases p
     cases q
     apply And.intro
     apply le_big_o_add
     repeat assumption
     apply le_big_o_add
     repeat assumption

theorem cong_big_o_mul (a1 b1 a2 b2 : Nat → Nat) : (cong_big_o a1 a2 → cong_big_o b1 b2 → cong_big_o (Std.fmul a1 b1) (Std.fmul a2 b2)) :=
  by intro p
     intro q
     cases p
     cases q
     apply And.intro
     apply le_big_o_mul
     repeat assumption
     apply le_big_o_mul
     repeat assumption

instance : Setoid (Nat → Nat) := .mk cong_big_o cong_big_o_equivalence

def BigO := Quotient (Setoid.mk cong_big_o cong_big_o_equivalence)
def O : (Nat → Nat) → BigO := Quotient.mk (Setoid.mk cong_big_o cong_big_o_equivalence)

theorem big_o_add (a1 b1 a2 b2 : Nat → Nat) :
    cong_big_o a1 a2 →
    cong_big_o b1 b2 →
    O (Std.fadd a1 b1) = O (Std.fadd a2 b2) := by
  intros p q
  apply Quotient.sound
  apply cong_big_o_add a1 b1 a2 b2
  repeat assumption

theorem big_o_mul (a1 b1 a2 b2 : Nat → Nat) : 
    cong_big_o a1 a2 →
    cong_big_o b1 b2 →
    O (Std.fmul a1 b1) = O (Std.fmul a2 b2) := by
  intros p q
  apply Quotient.sound
  apply cong_big_o_mul a1 b1 a2 b2
  repeat assumption

theorem big_o_le (a1 b1 a2 b2 : Nat → Nat) :
    cong_big_o a1 a2 →
    cong_big_o b1 b2 →
    le_big_o a1 b1 = le_big_o a2 b2 := by
  intros p q
  cases p
  cases q
  have h := show le_big_o a1 b1 ↔ le_big_o a2 b2 by
    apply Iff.intro
    all_goals intros
    apply le_big_o_trans a2 b1 b2
    apply le_big_o_trans a2 a1 b1
    repeat assumption
    any_goals apply le_big_o_trans a1 b2 b1
    any_goals apply le_big_o_trans a1 a2 b2
    repeat assumption
  simp [h]

theorem big_o_eq (a1 b1 a2 b2 : Nat → Nat) :
    cong_big_o a1 a2 →
    cong_big_o b1 b2 →
    cong_big_o a1 b1 = cong_big_o a2 b2 := by
  intros p q
  have h := show cong_big_o a1 b1 ↔ cong_big_o a2 b2 by
    apply Iff.intro
    all_goals intro r
    apply cong_big_o_sym
    all_goals apply cong_big_o_trans
    any_goals apply p
    all_goals apply cong_big_o_sym
    all_goals apply cong_big_o_trans
    any_goals apply q
    apply r
    apply cong_big_o_sym r
  simp [h]

def O_zero : BigO := O (λ _ => 0)
def O_one : BigO := O (λ _ => 1)

def o_cong_fun := Quotient.lift₂ cong_big_o big_o_eq

instance : Add BigO where add := Quotient.lift₂ (λ a b => O (Std.fadd a b)) big_o_add

instance : Mul BigO where mul := Quotient.lift₂ (λ a b => O (Std.fmul a b)) big_o_mul

instance : LE BigO where le := Quotient.lift₂ le_big_o big_o_le

instance : LT BigO where lt := λ a b : BigO => a ≤ b ∧ ¬ (a = b)

theorem o_add_eq (a b : Nat → Nat) : O (λ n => a n + b n) = O a + O b := by rfl

theorem o_mul_eq (a b : Nat → Nat) : O (λ n => a n * b n) =  O a * O b := by rfl

theorem o_cong (a b : Nat → Nat) : o_cong_fun (O a) (O b) ↔ cong_big_o a b := by rfl

theorem o_eq_inner (a b : Nat → Nat ) : O a = O b ↔ o_cong_fun (O a) (O b) := by
  apply Iff.intro
  intro p
  rw [p, o_cong]
  apply cong_big_o_refl
  intro p
  apply Quotient.sound
  rw [o_cong] at p
  assumption

theorem o_eq (a b : Nat → Nat) : O a = O b ↔ cong_big_o a b := by
  rw [← o_cong]
  apply o_eq_inner

theorem o_le (a b : Nat → Nat) : O a ≤ O b ↔ le_big_o a b := by  
  apply Iff.intro <;> (intro; assumption)

theorem o_le_of_eq {a b : Nat → Nat} : O a = O b → O a ≤ O b := by
  intro p
  rw [o_le]
  rw [o_eq] at p
  cases p
  assumption

theorem o_eq_of_le {a b : Nat → Nat} : O a ≤ O b → O b ≤ O a → O a = O b := by
  intro p
  intro q
  rw [o_le] at *
  rw [o_eq]
  apply And.intro
  repeat assumption

theorem o_ne_of_lt {a b : Nat → Nat} : O a < O b → O a ≠ O b := by
  intro p
  cases p
  assumption

theorem o_le_refl (a : BigO) : a ≤ a := by
  cases Quotient.exists_rep a with | intro f h =>
  rw [← h, ← O, o_le]
  apply le_big_o_refl

theorem o_le_trans {a b c : BigO} : a ≤ b → b ≤ c → a ≤ c := by
  cases Quotient.exists_rep a with | intro f x =>
  cases Quotient.exists_rep b with | intro g y =>
  cases Quotient.exists_rep c with | intro h z =>
  rw [← x, ← y, ← z, ← O, o_le, o_le, o_le]
  apply le_big_o_trans

theorem o_lt_of_le_of_lt {a b c : Nat → Nat} : O a ≤ O b → O b < O c → O a < O c := by
  intro p
  intro q
  cases q with | intro ql qr =>
  apply And.intro
  apply o_le_trans
  repeat assumption
  intro r
  apply qr
  apply o_eq_of_le
  assumption
  rw [← r]
  assumption

theorem o_lt_of_lt_of_le {a b c : Nat → Nat} : O a < O b → O b ≤ O c → O a < O c := by
  intro p
  intro q
  cases p with | intro pl pr =>
  apply And.intro
  apply o_le_trans
  repeat assumption
  intro r
  apply pr
  apply o_eq_of_le
  assumption
  rw [r]
  assumption

theorem o_mul_identity (a : BigO) : a = a * O_one := by
  cases Quotient.exists_rep a with | intro f h =>
  rw [← h, O_one, ← O, ← o_mul_eq]
  apply Quotient.sound
  apply And.intro <;> (exists 0, 1; simp)

theorem o_add_identity (a : BigO) : a = a + O_zero := by
  cases Quotient.exists_rep a with | intro f h =>
  rw [← h, O_zero, ← O, ← o_add_eq]
  apply Quotient.sound
  apply And.intro <;> (exists 0, 1; simp)

example : O_one + O_zero = O_one :=
  by apply o_add_identity

theorem o_power_le_power {n m : Nat} : (n ≤ m) ↔ O (λ x => x ^ n) ≤ O (λ x => x ^ m) := by
  apply Iff.intro
  intro p
  rw [o_le]
  exists 1
  exists 1
  simp
  intro x
  intro b
  have r := show x > 0 by
    apply Nat.gt_of_not_le
    intro h
    have g := Nat.le_trans b h
    simp at g
  have s := Nat.pow_le_pow_of_le_right r p
  assumption
  intro p
  rw [o_le] at p
  cases p with | intro x0 p =>
  cases p with | intro c p =>
  cases Std.le_max x0 (c + 1) with | intro x h =>
  cases h with | intro lb rb =>
  have p := p x
  simp at p
  apply @Std.cmul_power_le n m c x
  apply rb
  apply p lb

theorem o_power_lt_power {n m : Nat} : (n < m) ↔ O (λ x => x ^ n) < O (λ x => x ^ m) := by
  apply Iff.intro
  all_goals intro p
  apply And.intro
  rw [← o_power_le_power]
  apply Nat.le_of_lt
  assumption
  intro q
  apply Nat.lt_irrefl n
  apply Nat.lt_of_lt_of_le
  apply p
  rw [o_power_le_power]
  apply o_le_of_eq
  simp [q]
  apply Nat.lt_of_le_of_ne
  rw [o_power_le_power]
  cases p
  assumption
  intro q
  cases p with | intro pl pr =>
  simp [q] at pr

theorem o_exponent_le_exponent (n m : Nat) : (n ≤ m) ↔ O (λ x => n ^ x) ≤ O (λ x => m ^ x) := by
  apply Iff.intro
  intro p
  rw [o_le]
  exists 1
  exists 1
  intros _ _
  simp
  apply Nat.pow_le_pow_of_le_left
  assumption
  intro p
  rw [o_le] at p
  cases p with | intro x0 p =>
  cases p with | intro c p =>
  cases Std.le_max x0 (c * m + 1) with | intro x bounds =>
  have rb := Nat.lt_of_succ_le bounds.right
  have p := p x bounds.left
  simp at p
  apply Nat.ge_of_not_lt
  intro q
  have h := Std.cmul_exponent_le m c x rb
  have h := Nat.lt_of_le_of_lt p h
  have q := Nat.le_of_lt_succ (Std.add_lt_of_lt_of_le q (Nat.le_refl 1))
  have h := Std.pow_exp_lt h
  have h := Nat.lt_of_le_of_lt q h
  apply Nat.lt_irrefl
  apply h

theorem o_power_le_exponent_helper {n : Nat} : 6 ≤ n → O (λ x => x ^ n) ≤ O (λ x => 2 ^ x) := by
  intro p
  rw [o_le]
  exists 2 ^ n
  exists 1
  intro x
  intro xb
  simp
  apply Nat.le_of_lt
  apply Std.lt_pow_lt_exp2
  repeat assumption

theorem o_power_le_exponent {n m : Nat} : (1 < m) → O (λ x => x ^ n) ≤ O (λ x => m ^ x) := by
  intro p
  cases Std.le_max 6 n with | intro n2 nb =>
  cases nb with | intro l r =>
  rw [o_power_le_power] at r
  have s := o_power_le_exponent_helper l
  have p := Nat.succ_le_of_lt p
  rw [o_exponent_le_exponent] at p
  apply o_le_trans
  apply r
  apply o_le_trans
  apply s
  apply p

theorem o_power_lt_exponent (n m : Nat) : (1 < m) → O (λ x => x ^ n) < O (λ x => m ^ x) := by
  intro p
  apply o_lt_of_lt_of_le
  rw [← o_power_lt_power]
  apply Nat.lt_succ_self
  apply o_power_le_exponent
  assumption

end Complexity