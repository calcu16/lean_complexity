import lambda_calculus.complexity.basic
import lambda_calculus.distance
import lambda_calculus.utlc.basic
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.beta.distance
import lambda_calculus.utlc.encoding.basic
import lambda_calculus.utlc.encoding.nat

namespace lambda_calculus
namespace complexity

open utlc

theorem add_complexity: complexity_le nat.add (λ n m, (6:ℕ)) :=
begin
  use encoding.nat.add,
  split,
  simp [utlc.encoding.nat.add],
  norm_num,
  intros x y,
  apply utlc.encoding.nat.add_distance_le
end

theorem pred_complexity: complexity_le nat.pred (λ n, (2*n + 5:ℕ)) :=
begin
  use encoding.nat.pred,
  split,
  simp [utlc.encoding.nat.pred],
  norm_num,
  intros x,
  apply utlc.encoding.nat.pred_distance_le
end

theorem sub_complexity: complexity_le nat.sub
  (cast (by simp) (λ n m, (2 * n + 15) * m + 5)) :=
begin
  have hsub : nat.sub = (λ n m, nat.pred^[m] n),
  { ext1 n, ext1 m,
    induction m generalizing n,
    { simp [nat.sub] },
    simp [nat.sub],
    rw [m_ih, iteration_complexity_le.f_iterate nat.pred],
    simp },
  rw [hsub],
  apply iteration_complexity_le pred_complexity,
  intros n m,
  induction m,
  { simp },
  simp at *,
  rw [show (nat.pred^[m_n] n) = (λ a b, nat.pred^[b] a) n m_n, by simp,
      ← hsub,
      show n.sub m_n = n - m_n, by simp[has_sub.sub],
      nat.succ_eq_add_one],
  apply le_trans,
  { repeat { apply add_le_add },
    apply mul_le_mul,
    any_goals { apply nat.sub_le },
    any_goals { apply m_ih },
    any_goals { apply nat.zero_le },
    any_goals { apply le_refl } },
  ring_nf,
end

end complexity
end lambda_calculus