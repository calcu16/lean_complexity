import hmem.split_cost

universe u
variables {α: Type u} [has_zero α] [decidable_eq α]

namespace hmem
namespace program

-- sum (mrc^i) fc(n-i)
-- mrc^n*fc(0)
-- fc(n)
-- crtical := n * mrc
def divide_and_conquer_cost (p: program α) (fc: ℕ → ℕ): ℕ → ℕ
| 0 := p.max_internal_cost + fc 0
| (n+1) := p.max_internal_cost + fc (n + 1) + divide_and_conquer_cost n * p.max_recurse_count

theorem divide_and_conquer_cost_def {p: program α} {fc: ℕ → ℕ} {n: ℕ}:
  divide_and_conquer_cost p fc n = p.max_internal_cost + fc n + ite (n = 0) 0 (divide_and_conquer_cost p fc (n - 1) * p.max_recurse_count) :=
by cases n; simp [divide_and_conquer_cost]

theorem divide_and_conquer_cost_mono {p: program α} {fc: ℕ → ℕ} {m n: ℕ}:
  0 < p.max_recurse_count → m ≤ n → divide_and_conquer_cost p fc m ≤ divide_and_conquer_cost p fc n :=
begin
  intros hr hmn,
  induction n,
  { rw [nat.eq_zero_of_le_zero hmn] },
  cases eq_or_lt_of_le hmn,
  { rw [h] },
  exact trans (n_ih (nat.le_of_lt_succ h)) (le_add_left (nat.le_mul_of_pos_right hr)),
end

theorem divide_and_conquer_cost_sound {p: program α}
  (fr: memory α → ℕ → Prop) (hfr: ∀ inp n arg, p.recurse_arg inp arg → fr inp n → ∃ m < n, fr arg m)
  {fc: ℕ → ℕ} (hfc: ∀ inp n, fr inp n → p.call_cost inp (fc n)):
  ∀ inp n, fr inp n → p.has_time_cost inp (divide_and_conquer_cost p fc n) :=
begin
  intros inp n hn,
  cases hrc:p.max_recurse_count,
  { apply thunk.time_cost_of_split',
    apply split_cost_of_components,
    { rcases hfc _ _ hn with ⟨i, r, h⟩,
      exact internal_cost_bound ⟨fc n, r, h⟩ },
    { exact hfc _ _ hn },
    apply recurse_cost_mono,
    apply max_recurse_cost_zero,
    { rcases hfc _ _ hn with ⟨i, r, h⟩,
      exact ⟨_, thunk.time_cost_of_split h⟩ },
    exact hrc,
    apply nat.zero_le 0,
    cases n,
    { refl },
    { unfold divide_and_conquer_cost,
      rw [hrc, mul_zero] } },
  induction n using nat.strong_induction_on with n ih generalizing inp,
  cases n,
  { apply thunk.time_cost_of_split',
    { apply split_cost_of_components,
      { rcases hfc _ _ hn with ⟨i, r, h⟩,
        exact internal_cost_bound ⟨fc 0, r, h⟩ },
      { exact hfc _ _ hn },
      apply max_recurse_cost_zero',
      { rcases hfc _ _ hn with ⟨i, r, h⟩,
        exact ⟨_, thunk.time_cost_of_split h⟩ },
      intros arg harg,
      rcases hfr _ _ _ harg hn with ⟨m, hm, _⟩,
      exact absurd hm (nat.not_lt_zero _),
    },
    refl },
  { apply thunk.time_cost_of_split',
    { apply split_cost_of_components,
      { rcases hfc _ _ hn with ⟨i, r, h⟩,
        exact internal_cost_bound ⟨fc (n + 1), r, h⟩ },
      { exact hfc _ _ hn },
      apply max_recurse_cost,
      { rcases hfc _ _ hn with ⟨i, r, h⟩,
        exact ⟨_, thunk.time_cost_of_split h⟩ },
      intros arg hrec,
      rcases hfr _ (n + 1) arg hrec hn with ⟨n', hn', hfr⟩,
      apply time_cost_mono,
      specialize ih _ hn' _ hfr,
      apply ih,
      apply divide_and_conquer_cost_mono,
      rw [hrc],
      apply nat.zero_lt_succ,
      apply nat.le_of_lt_succ hn' },
    rw [mul_comm],
    refl },
end

end program
end hmem