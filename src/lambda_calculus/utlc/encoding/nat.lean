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

instance : has_encoding ℕ := ⟨ lift ⟩

def succ: utlc := Λ Λ Λ ↓1·(↓2·↓1·↓0)

def add: utlc := Λ Λ Λ Λ ↓3·↓1·(↓2·↓1·↓0)

local attribute [simp] closed closed_below iterate lift
local attribute [simp] β.normal_iteration β.strategic_reduction_step
local attribute [simp] reduced substitution shift

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

theorem succ_distance_le (n: ℕ): β.distance_le 3 (succ·(lift n)) (lift (n+1)) :=
begin
  have iterate_cb: ∀ n, (iterate n ↓1 ↓0).closed_below 2,
  { intro n,
    apply iterate_closed_below,
    all_goals { simp } },
  have iterate_shift_cancel: ∀ n, (iterate n ↓1 ↓0) ↑¹ 2 = (iterate n ↓1 ↓0),
  { intro n,
    apply shift_of_closed_below,
    apply iterate_cb },
  simp [succ],
  apply β.distance_le_of_normal_iteration 3,
  simp [iterate_shift_cancel]
end

theorem add_distance_le (n m: ℕ): β.distance_le 6 (add·(lift n)·(lift m)) (lift (n + m)) :=
begin
  have iterate_cb: ∀ n, (iterate n ↓1 ↓0).closed_below 2,
  { intro n,
    apply iterate_closed_below,
    all_goals { simp } },
  have iterate_shift_cancel: ∀ n, (iterate n ↓1 ↓0) ↑¹ 2 = (iterate n ↓1 ↓0),
  { intro n,
    apply shift_of_closed_below,
    apply iterate_cb },
  simp [add],
  apply distance_le_trans' 4 2,
  apply β.distance_le_of_normal_iteration 4,
  simp [iterate_shift_cancel],
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


end nat
end encoding
end utlc
end lambda_calculus