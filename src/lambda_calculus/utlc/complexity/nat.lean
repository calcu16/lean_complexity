import lambda_calculus.utlc.complexity.basic
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
    rw [function.iterate_succ_apply', ← m_ih],
    simp [nat.sub] },
  rw [hsub],
  apply iteration_complexity_le' pred_complexity,
  refl,
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

theorem mul_complexity: complexity_le nat.mul
  (cast (by simp) (λ n m, 27 * m + 39)) :=
begin
  -- n → m → n*m
  apply compose_complexity_le (ℕ×ℕ),
  { -- n → (0, n) =>
    apply to_fst_complexity_le,
    -- n → 0
    apply const_complexity_le,
    apply value_complexity_le (0:ℕ),
    { intro, refl },
    { intro, apply le_of_eq, refl },
    { simp },
    { intro, apply le_of_eq, refl } },
  -- => (0, n) → m → n*m
  apply curry_complexity_le,
  -- (0, n, m) → n*m
  apply compose_complexity_le (ℕ×ℕ),
  { -- => (0, n, m) → (n*m, m)
    apply uncurry_complexity_le,
    -- (0, n) → m → (n*m, m)
    apply flip_complexity_le,
    -- m → (0, n) → (n*m, m)
    apply iteration_complexity_le,
    -- (a, n) → (n+a, n)
    apply fork_complexity_le,
    { -- => (a, n) → n+a
      apply uncurry_complexity_le,
      -- a → n → n+a
      apply add_complexity,
      refl,
      intros a n, simp,
      apply show 6 + 3 ≤ (λ an, 9) (a, n), by simp },
    -- <= (a, n) → n
    apply snd_complexity_le,
    refl,
    { intros a,
      apply show 3 + (9 + 5) ≤ (λ a, 17) a, by simp },
    refl,
    { intros m an,
      simp },
    refl,
    { intros an m,
      induction m,
      { simp,
        apply show 5 + 13 ≤ (λ an m, 27*m + 18) an 0, by simp },
      { simp [nat.mul_succ],
        linarith } },
    refl,
    { intros ab n,
      simp, ring_nf,
      apply show 27 * n + 21 ≤ (λ abn: ((ℕ×ℕ)×ℕ), 27 * abn.snd + 21) (ab, n), by simp } },
  -- <= (n*m,n) → n*m
  apply fst_complexity_le,
  refl,
  { intro a, simp },
  { simp },
  { intros a b, simp },
  { ext1 n, ext1 m,
    simp [function.swap],
    have h: ((n* m, n) = ((λ (a : ℕ × ℕ), (a.fst + a.snd, a.snd))^[m] (0, n))) := by
    { induction m,
      { simp },
      rw [function.iterate_succ_apply', ← m_ih],
      simp [nat.mul_succ] },
    rw [←h] },
  { intro n,
    simp,
    intro m,
    ring_nf }
end

end complexity
end lambda_calculus