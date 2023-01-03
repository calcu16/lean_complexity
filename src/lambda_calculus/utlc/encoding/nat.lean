import lambda_calculus.utlc.basic
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.beta.distance
import lambda_calculus.utlc.encoding.basic

namespace lambda_calculus
namespace utlc
namespace encoding
namespace nat

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

def lift(n :ℕ): utlc := Λ Λ iterate n ↓1 ↓0

def succ: utlc := Λ Λ Λ ↓1·(↓2·↓1·↓0)

def add: utlc := Λ Λ Λ Λ ↓3·↓1·(↓2·↓1·↓0)

def pred: utlc := Λ Λ Λ ↓2·(Λ Λ ↓0·(↓1·↓3))·(Λ ↓1)·(Λ ↓0)

def sub: utlc := Λ Λ ↓0·pred·↓1 

def is_zero: utlc := Λ ↓0·(Λ false)·true

def apply_iterate: utlc := (Λ Λ Λ ↓0·↓2·↓1)

local attribute [simp] closed closed_below
local attribute [simp] β.normal_iteration β.strategic_reduction_step
local attribute [simp] reduced substitution shift shift_substitution_index

section
local attribute [simp] iterate lift

theorem iterate_closed_below {n: ℕ} {f g: utlc} (m: ℕ):
  f.closed_below n → g.closed_below n → (iterate m f g).closed_below n :=
begin
  induction m,
  all_goals { simp },
  intros p q,
  refine ⟨p, m_ih p q⟩
end

@[simp] theorem iterate_substitution {n m: ℕ} {f g x: utlc}:
  (iterate n f g)[m:=x] = (iterate n (f[m:=x]) (g[m:=x])) :=
begin
  induction n,
  all_goals { simp },
  apply n_ih
end

@[simp] theorem iterate_shift {n m: ℕ} {f g: utlc}:
  (iterate n f g) ↑¹ m = (iterate n (f ↑¹ m) (g ↑¹ m)) :=
begin
  induction n,
  all_goals { simp },
  apply n_ih
end

theorem lift_closed (n: ℕ): (lift n).closed :=
begin
  simp,
  apply iterate_closed_below,
  all_goals { simp }
end

theorem lift_reduced (n: ℕ): β.reduced (lift n) :=
begin
  simp [reduced],
  induction n,
  all_goals { simp },
  assumption
end

theorem lift_inj {n m: ℕ}: (lift n) = (lift m) → n = m :=
begin
  simp [lift],
  induction n generalizing m,
  all_goals { cases m },
  all_goals { simp[iterate] },
  apply n_ih
end

instance : has_encoding ℕ := ⟨ ⟨ lift, begin
    intro a,
    refine ⟨lift_closed a, lift_reduced a, _⟩,
    apply lift_inj
  end  ⟩ ⟩


theorem lift_zero_distance_le (f g: utlc): β.distance_le 2 (lift 0·f·g) g :=
begin
  apply β.distance_le_of_normal_iteration 2,
  simp [lift],
end

theorem lift_succ_distance_le (n: ℕ) (f g: utlc): β.distance_le 4 ((lift (n+1))·f·g) (f·(lift n·f·g)) :=
begin
 apply distance_le_trans',
 apply β.distance_le_of_normal_iteration 2,
 simp,
 apply distance_le_symm,
 apply β.dot_distance_le_dot_right,
 apply β.distance_le_of_normal_iteration 2,
 simp 
end

theorem succ_distance_le (n: ℕ): β.distance_le 3 (succ·(lift n)) (lift (n+1)) :=
begin
  simp [succ],
  apply β.distance_le_of_normal_iteration 3,
  simp
end


theorem is_zero_distance_le (n: ℕ): β.distance_le 4 (is_zero·(lift n)) (encode (nat.decidable_eq n 0)) :=
begin
  cases n,
  all_goals { simp [is_zero, nat.decidable_eq, encode, has_encoding.value] },
  { apply distance_le_mono,
    apply β.distance_le_of_normal_iteration 3,
    simp,
    apply substitution_identity_of_closed,
    simp [true],
    simp },
  { apply β.distance_le_of_normal_iteration 4,
    simp,
    rw [substitution_identity_of_closed],
    rw [substitution_identity_of_closed],
    simp [false, closed],
    rw [substitution_identity_of_closed],
    all_goals { simp [false, closed] },
  }
end

theorem add_distance_le (n m: ℕ): β.distance_le 6 (add·(lift n)·(lift m)) (lift (n + m)) :=
begin
  simp [add],
  apply distance_le_trans' 4 2,
  apply β.distance_le_of_normal_iteration 4,
  simp,
  apply β.lambda_distance_le_lambda,
  apply β.lambda_distance_le_lambda,
  induction n generalizing m,
  simp,
  { cases m,
    all_goals { apply β.distance_le_of_normal_iteration 2, simp } },
  simp [nat.succ_add],
  apply β.dot_distance_le_dot_right,
  apply n_ih,
  simp
end

theorem pred_distance_le (n: ℕ): β.distance_le (2*n+5) (pred·(lift n)) (lift n.pred) :=
begin
  simp [pred],
  apply distance_le_trans' 3 (2*n+2),
  apply β.distance_le_of_normal_iteration 3,
  simp,
  norm_num,
  apply β.lambda_distance_le_lambda,
  apply β.lambda_distance_le_lambda,
  cases n,
  { apply distance_le_succ,
    apply β.distance_le_of_normal_iteration 1,
    simp },
  apply distance_le_trans' 3 (2*n+1),
  apply β.distance_le_of_normal_iteration 3,
  simp, norm_num,
  induction n,
  { apply β.distance_le_of_normal_iteration 1,
    simp },
  { apply distance_le_trans',
    apply β.distance_le_of_normal_iteration 2,
    simp, norm_num,
    apply β.dot_distance_le_dot_right,
    apply n_ih,
    ring },
  all_goals { ring }
end
end

theorem apply_iterate_zero_distance_le {f g: utlc}: β.distance_le 5 (apply_iterate·f·g·(encode 0)) g :=
begin
  simp [apply_iterate, encode, has_encoding.value],
  apply distance_le_trans',
  apply β.distance_le_of_normal_iteration 3,
  simp,
  rw [← shift_comm],
  simp [shift_substitution_index],
  apply lift_zero_distance_le,
  simp,
end

theorem apply_iterate_succ_distance_le {f g: utlc}: ∀ n, β.distance_le 10 (apply_iterate·f·g·(encode (n+1))) (f·(apply_iterate·f·g·encode n)) :=
begin
  intros n,
  simp [apply_iterate, encode, has_encoding.value],
  apply distance_le_trans',
  apply β.distance_le_of_normal_iteration 3,
  simp,
  rw [← shift_comm],
  simp [shift_substitution_index],
  apply distance_le_trans',
  apply lift_succ_distance_le,
  apply distance_le_symm,
  apply β.dot_distance_le_dot_right,
  apply β.distance_le_of_normal_iteration 3,
  simp,
  rw [← shift_comm],
  simp [shift_substitution_index],
  all_goals { refl },
end

theorem sub_distance_le (n m: ℕ): β.distance_le ((2 * n + 9) * m + 4) (sub·(lift n)·(lift m)) (lift (n - m)) :=
begin
  have pred_sub := substitution_identity_of_closed (show pred.closed, by { simp[pred], norm_num }),
  simp only [sub],
  apply distance_le_trans' 2 ((2*n + 9)*m + 2),
  apply β.distance_le_of_normal_iteration 2,
  simp [pred_sub],
  induction m,
  { simp,
    apply distance_le_mono,
    apply lift_zero_distance_le,
    nlinarith },
  { simp [nat.succ_eq_add_one],
    apply distance_le_mono,
    apply distance_le_trans',
    apply lift_succ_distance_le,
    apply distance_le_trans',
    apply β.dot_distance_le_dot_right,
    apply m_ih,
    apply pred_distance_le,
    refl,
    refl,
    ring_nf,
    simp [add_mul],
    ring_nf,
    simp,
  },
  ring,
end

end nat
end encoding
end utlc
end lambda_calculus