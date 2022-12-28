import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.properties
import lambda_calculus.utlc.normal
import lambda_calculus.utlc.beta_trans

namespace utlc  

-- local attribute [simp] mk_β_normal_form β_normal_iteration reduced β_normal_step substitution shift
local attribute [simp] β_normal_iteration β_normal_step substitution β_step shift reduced closed closed_below

namespace church
def false : utlc := Λ Λ ↓0
def true : utlc := Λ Λ ↓1 
def ite : utlc := Λ Λ Λ ↓2·↓1·↓0
def and : utlc := Λ Λ ↓1·↓0·(Λ Λ ↓0)
def or : utlc := Λ Λ ↓1·(Λ Λ ↓1)·↓0
-- #eval mk_β_normal_form (Λ ite·↓0) 1 (by simp[ite])
def not : utlc := Λ Λ Λ ↓2·↓1·↓0
-- #eval mk_β_normal_form (Λ Λ ↓1·(not·↓0)·↓0) 2 (by simp[not, ite])
def xor : utlc := Λ Λ ↓1·(Λ Λ ↓2·↓1·↓0)·↓0


def pair : utlc := Λ Λ Λ ↓0·↓1·↓2
def fst : utlc := Λ ↓0·(Λ Λ ↓0)
def snd : utlc := Λ ↓0·(Λ Λ ↓1)

-- #eval mk_β_normal_form (Λ pair·true·↓0) 2 (by simp[pair, true])
def leaf : utlc := Λ Λ ↓0·↓1·(Λ Λ ↓1)
-- #eval mk_β_normal_form (leaf·true) 2 (by simp[leaf, pair, true])
def nil : utlc := Λ ↓0·(Λ Λ ↓1)·(Λ Λ ↓1)
-- #eval mk_β_normal_form (Λ Λ pair·false·(pair·↓1·↓0)) 4 (by {simp[leaf, pair, false], norm_num})
def cons : utlc := Λ Λ Λ ↓0·(Λ ↓0·↓2·↓3)·(Λ Λ ↓0)

-- #eval mk_β_normal_form (Λ fst·↓0) 1 (by simp[fst])
def isleaf : utlc := Λ ↓0·(Λ Λ ↓0)
def isnil : utlc := Λ ↓0·(Λ Λ ↓0) 

def ycomb : utlc := Λ (Λ ↓1·(↓0·↓0))·(Λ ↓1·(↓0·↓0))
def zcomb : utlc := Λ (Λ ↓1·(Λ ↓1·↓1·↓0))·(Λ ↓1·(Λ ↓1·↓1·↓0))

def zero : utlc := Λ Λ ↓0
def succ : utlc := Λ Λ Λ ↓1·(↓2·↓1·↓0)

def lift_helper : ℕ → utlc
| 0 := ↓ 0
| (n+1) := ↓1·lift_helper n

def lift : ℕ → utlc := λ n, Λ Λ lift_helper n

theorem lift_helper_closed_below (n : ℕ) : (lift_helper n).closed_below 2 :=
begin
  induction n with _ h,
  all_goals { simp [lift_helper, closed_below] },
  apply h,
end

theorem inc_lift_helper (n : ℕ): ↓1·(lift_helper n) = lift_helper (n+1) := by refl

theorem lift_closed (n : ℕ): (lift n).closed :=
begin
  simp [lift, closed_below],
  norm_num,
  apply lift_helper_closed_below
end

theorem lift_β_reduced (n : ℕ): (lift n).β_reduced :=
begin
  simp [lift, reduced],
  induction n,
  all_goals { simp [lift_helper] },
  assumption,
end

theorem lift_identity (n: ℕ): (lift n)·↓1·↓0 ≈ᵦ lift_helper n :=
begin
  unfold lift,
  apply β_equiv_of_β_normal_iteration 2,
  simp,
  rw [substitution_shift_index', @substitution_shift_index_zero],
  refl,
  apply lift_helper_closed_below,
end

theorem succ_lift (n : ℕ): succ·(lift n) ≈ᵦ lift (n + 1) :=
begin
  simp [succ, lift],
  simp [lift_helper],
  induction n,
  apply β_equiv_of_β_normal_iteration 3,
  simp,
  refl,
  simp [lift_helper],
  apply β_equiv_of_β_normal_iteration 3,
  simp,
  norm_num,
  rw [shift_closed_below (lift_helper_closed_below _) (nat.le_refl _)],
  apply β_equiv_lambda,
  apply β_equiv_lambda,
  apply β_equiv_application_right,
  apply β_equiv_application_right,
  rw [substitution_shift_index', @substitution_shift_index_zero],
  apply lift_helper_closed_below,
end

theorem inc_lift (n : ℕ): (Λ Λ ↓1·(lift n·↓1·↓0)) ≈ᵦ lift (n+1) :=
begin
  simp [lift],
  simp [lift_helper],
  apply β_equiv_of_β_normal_iteration 2,
  simp,
  rw [substitution_shift_index', @substitution_shift_index_zero],
  refl,
  apply lift_helper_closed_below,
end

theorem lift_inc (n : ℕ): (Λ Λ lift n·↓1·(↓1· ↓ 0)) ≈ᵦ lift (n+1) :=
begin
  simp [lift],
  simp [lift_helper],
  apply β_equiv_of_β_normal_iteration 2,
  simp,
  apply β_equiv_lambda,
  apply β_equiv_lambda,
  induction n,
  simp [lift_helper, substitution],
  refl,
  simp [lift_helper],
  apply β_equiv_application_right,
  apply n_ih,
end

theorem lift_helper_substitution (n m : ℕ): ((lift_helper n).substitution 1 ↓1).substitution 0 (lift_helper m) = lift_helper (n+m) :=
begin
  induction m generalizing n, -- do I need this?
  simp [lift_helper],
  rw [substitution_shift_index', @substitution_shift_index_zero],
  apply lift_helper_closed_below,
  induction n,
  simp [lift_helper],
  rw [shift_zero],
  rw [nat.succ_eq_add_one],
  rw [lift_helper],
  simp [substitution],
  rw n_ih,
  rw inc_lift_helper,
  ring_nf,
end

def add : utlc := Λ Λ Λ Λ ↓3·↓1·(↓2·↓1·↓0)

theorem add_zero {n : ℕ}: add·(lift n)·zero ≈ᵦ (lift n) :=
begin
  simp[add, zero],
  apply β_equiv_of_β_normal_iteration 2,
  simp [shift_closed (lift_closed _), substitution_closed (lift_closed _)],
  apply β_equiv_trans (β_equiv_of_β_step' [bool.tt] _),
  apply β_equiv_trans (β_equiv_of_β_step' [bool.tt] _),
  simp,
  apply β_equiv_of_β_normal_iteration 2,
  unfold lift,
  simp,
  rw [substitution_shift_index', @substitution_shift_index_zero],
  refl,
  apply lift_helper_closed_below,
end

theorem zero_add {n : ℕ}: add·zero·(lift n) ≈ᵦ (lift n) :=
begin
  simp[add, zero],
  apply β_equiv_of_β_normal_iteration 2,
  simp [shift_closed (lift_closed _), substitution_closed (lift_closed _)],
  apply β_equiv_trans (β_equiv_of_β_step' [bool.tt] _),
  apply β_equiv_trans (β_equiv_of_β_step' [bool.tt] _),
  simp,
  apply β_equiv_of_β_normal_iteration 2,
  unfold lift,
  simp,
  rw [substitution_shift_index', @substitution_shift_index_zero],
  rw [shift_zero],
  refl,
  apply lift_helper_closed_below,
end

theorem add_one {n: ℕ}: lift (n+1) ≈ᵦ add·(lift n)·(lift 1) :=
begin
  rw [show lift 1 = Λ Λ lift_helper 1, by simp[lift]],
  unfold add lift_helper,
  apply β_equiv_symm,
  apply β_equiv_of_β_normal_iteration 2,
  simp [shift_closed (lift_closed _), substitution_closed (lift_closed _)],
  apply β_equiv_trans (β_equiv_of_β_step' [bool.tt] _),
  apply β_equiv_trans (β_equiv_of_β_step' [bool.tt] _),
  simp,
  apply β_equiv_trans (lift_inc _),
  refl,
end

theorem one_add {n : ℕ}: lift (n+1) ≈ᵦ add·(lift 1)·(lift n) :=
begin
  rw [show lift 1 = Λ Λ lift_helper 1, by simp[lift]],
  unfold add lift_helper,
  apply β_equiv_symm,
  apply β_equiv_of_β_normal_iteration 4,
  simp [shift_closed (lift_closed _), substitution_closed (lift_closed _)],
  apply β_equiv_trans (inc_lift _),
  refl,
end

theorem add_sound {n m : ℕ}: add·(lift n)·(lift m) ≈ᵦ lift (n + m) :=
begin
  induction n with n hn generalizing m,
  simp,
  apply zero_add,
  unfold add,
  apply β_equiv_of_β_normal_iteration 2,
  simp [shift_closed (lift_closed _), substitution_closed (lift_closed _)],
  apply β_equiv_trans,
  apply β_equiv_lambda,
  apply β_equiv_lambda,
  apply β_equiv_application_right,
  apply lift_identity,
  rw [nat.succ_eq_add_one, lift],
  apply β_equiv_of_β_normal_iteration 2,
  simp,
  rw [lift_helper_substitution],
  refl,
  nat.add
end

def mul : utlc := Λ Λ Λ Λ ↓3·(↓2·↓1)·↓0   
def exp : utlc := Λ Λ ↓0·↓1

-- #eval mk_β_normal_form (Λ fst·(↓0·(Λ pair·((Λ ↓0·(succ·↓0))·(snd·↓0))))·(pair·zero·zero)) 8 (by {simp[fst,pair,succ,snd,zero], norm_num})
def pred : utlc := Λ ↓0·(Λ Λ Λ ↓0·↓1·(↓2·(Λ Λ ↓1)·(Λ Λ ↓1·(↓4·(Λ Λ ↓1)·↓1·↓0))))·(Λ Λ ↓0)·(Λ ↓0·(Λ Λ ↓0)·(Λ Λ ↓0))
-- #eval mk_β_normal_form (Λ Λ (↓0·pred)·↓1) 1 (by simp[pred])
def sub : utlc := Λ Λ ↓0·(Λ ↓0·(Λ Λ Λ ↓0·↓1·(↓2·(Λ Λ ↓1)·(Λ Λ ↓1·(↓4·(Λ Λ ↓1)·↓1·↓0))))·(Λ Λ ↓0)·(Λ ↓0·(Λ Λ ↓0)·(Λ Λ ↓0)))·↓1


def eq_zero : utlc := Λ ↓0·(Λ Λ Λ ↓0)·(Λ Λ ↓1)
-- #eval mk_β_normal_form (Λ Λ eq_zero·(sub·↓1·↓0)) 3 (by { simp[eq_zero, sub], norm_num} )
def leq : utlc := Λ Λ ↓0·(Λ ↓0·(Λ Λ Λ ↓0·↓1·(↓2·(Λ Λ ↓1)·(Λ Λ ↓1·(↓4·(Λ Λ ↓1)·↓1·↓0))))·(Λ Λ ↓0)·(Λ ↓0·(Λ Λ ↓0)·(Λ Λ ↓0)))·↓1·(Λ Λ Λ ↓0)·(Λ Λ ↓1)
-- #eval mk_β_normal_form (Λ Λ and·(leq·↓0·↓1)·(leq·↓1·↓0)) 6 (by {simp[and, leq], norm_num})
def eq : utlc := Λ Λ ↓1·(Λ ↓0·(Λ Λ Λ ↓0·↓1·(↓2·(Λ Λ ↓1)·(Λ Λ ↓1·(↓4·(Λ Λ ↓1)·↓1·↓0))))·(Λ Λ ↓0)·(Λ ↓0·(Λ Λ ↓0)·(Λ Λ ↓0)))·↓0·(Λ Λ Λ ↓0)·(Λ Λ ↓1)·(↓0·(Λ ↓0·(Λ Λ Λ ↓0·↓1·(↓2·(Λ Λ ↓1)·(Λ Λ ↓1·(↓4·(Λ Λ ↓1)·↓1·↓0))))·(Λ Λ ↓0)·(Λ ↓0·(Λ Λ ↓0)·(Λ Λ ↓0)))·↓1·(Λ Λ Λ ↓0)·(Λ Λ ↓1))·(Λ Λ ↓0)

-- #eval mk_β_normal_form (lead·false) 1 (by simp[leaf, false])
def bit_zero : utlc := Λ ↓0·(Λ Λ ↓0)·(Λ Λ ↓1)
-- #eval mk_β_normal_form (leaf·true) 2 (by simp[leaf, true])
def bit_one : utlc := Λ ↓0·(Λ Λ ↓1)·(Λ Λ ↓1)

end church



end utlc