import lambda_calculus.utlc.basic

namespace lambda_calculus
namespace utlc

variables {n m : ℕ}
variables {f g: utlc}
local attribute [simp] down_shift

theorem size_pos (f: utlc): 0 < f.size := by
{ cases f, all_goals { simp}  }

theorem size_pos' (f: utlc): 1 ≤ f.size := nat.one_le_of_lt (size_pos f)

@[simp] theorem shift_inj_helper (x y n: ℕ): ite (x < n) x (x + 1) = ite (y < n) y (y + 1) ↔ x = y :=
begin
  split_ifs;
  try { exact id };
  try { exact add_right_cancel };
  split;
  intro _;
  linarith
end 

@[simp] theorem shift_inj_iff {f: utlc} (n: nat) {g: utlc}: f ↑¹ n = g ↑¹ n ↔ f = g :=
begin
  induction f using lambda_calculus.utlc.notation_induction_on generalizing n g;
  induction g using lambda_calculus.utlc.notation_cases_on,
  { simp }, { simp }, { simp },
  { simp }, { simp [f_ih] }, { simp },
  { simp }, { simp }, { simp [f_ih_f, f_ih_g] },
end

theorem shift_comm (h: n ≤ m) (f: utlc): f ↑¹ n ↑¹ (m+1) = f ↑¹ m ↑¹ n :=
begin
  induction f using lambda_calculus.utlc.notation_induction_on generalizing n m,
  { simp only [down_shift],
    split_ifs;
    try { { refl } };
    exfalso;
    linarith },
  { simp [f_ih (nat.succ_le_succ h)] },
  { simp [f_ih_f h, f_ih_g h] }
end

@[simp] theorem shift_comm_zero (f: utlc): f ↑¹ n ↑¹ 0 = f ↑¹ 0 ↑¹ (n + 1) :=
 (shift_comm (nat.zero_le _) _).symm

theorem shift_comm' (h: n < m) (f: utlc) : f ↑¹ n ↑¹ m = f ↑¹ (m-1) ↑¹ n :=
begin
  cases m,
  { revert h, simp },
  { exact shift_comm (nat.le_of_lt_succ h) _ }, 
end

@[simp] theorem size_shift (f: utlc) (n: ℕ): (f ↑¹ n).size = f.size :=
begin
  induction f using lambda_calculus.utlc.notation_induction_on generalizing n,
  { simp },
  { simp [f_ih] },
  { simp[f_ih_f, f_ih_g] }
end

lemma down_shift_uses_lt {n m: ℕ}: n < m → ∀ (x: ℕ), (↓x ↑¹ n:utlc).uses m = (↓x:utlc).uses (m - 1) :=
begin
  cases m,
  { simp },
  rw [nat.succ_eq_add_one, nat.add_sub_cancel],
  intros hnm x,
  obtain hxm|hxm|hxm := nat.lt_trichotomy x m,
  { simp [hxm, ne_of_lt hxm, ite_eq_iff, show (x < n → ¬ x = m + 1) ↔ true, by rw [iff_true]; intro; linarith] },
  { simp [hxm, not_lt_of_ge (nat.le_of_lt_succ hnm)] },
  { simp [hxm, ne_of_gt hxm, show ¬ x < n, by linarith] }
end

lemma down_shift_uses_eq (n x: ℕ): (↓x ↑¹ n:utlc).uses n = 0 :=
by simp [down_shift, uses, ite_eq_iff,
  show ¬ (x < n ∧ x = n), by intro; linarith,
  show (n ≤ x → ¬ x + 1 = n) ↔ true , by rw [iff_true]; intros _ _; linarith ]

lemma down_shift_uses_gt {n m: ℕ}: m < n → ∀ (x: ℕ), (↓x ↑¹ n:utlc).uses m = (↓x:utlc).uses m :=
begin
  intros hnm x,
  by_cases x = m,
  { simp [h, not_le_of_lt hnm] },
  simp [h, ite_eq_iff,
    show (n ≤ x → ¬ x + 1 = m) ↔ true , by rw [iff_true]; intros _ _; linarith]
end

theorem shift_uses (f: utlc) (n m: ℕ):
  (f ↑¹ n).uses m =
  if n < m then f.uses (m - 1)
  else if n = m then 0
  else f.uses m :=
begin
  induction f using lambda_calculus.utlc.notation_induction_on generalizing n m,
  { obtain h|h|h := nat.lt_trichotomy n m,
    { simp only [h, if_true],
      exact down_shift_uses_lt h _ },
    { rw [h],
      simp only [lt_self_iff_false, if_false, eq_self_iff_true m, if_true],
      exact down_shift_uses_eq _ _ },
    { simp only [not_lt_of_gt h, ne_of_gt h, if_false],
      exact down_shift_uses_gt h _ } },
  { simp only [f_ih, lambda_shift, lambda_uses,
    add_right_cancel_iff, add_lt_add_iff_right],
    split_ifs;
    try { { refl } },
    rw [nat.sub_add_comm (nat.one_le_of_lt h)] },
  { simp only [ f_ih_f, f_ih_g, dot_shift, dot_uses],
    split_ifs;
    refl }
end

theorem shift_uses_lt {n m: ℕ} (h: n < m): ∀ (f: utlc), (f ↑¹ n).uses m = f.uses (m - 1) :=
by simp [shift_uses, h]


@[simp]
theorem shift_uses_zero_succ (f: utlc) (n: ℕ): (f ↑¹ 0).uses (n+1) = f.uses n := shift_uses_lt (nat.zero_lt_succ n) f

@[simp]
theorem shift_uses_self (f: utlc) (n: ℕ) : (f ↑¹ n).uses n = 0 :=
by simp [shift_uses]

theorem shift_of_uses_zero {f: utlc} {n: ℕ}: f.uses n = 0 → ∃ g, f = g ↑¹ n :=
begin
  induction f using lambda_calculus.utlc.notation_induction_on generalizing n,
  { intro p,
    obtain h|h|h := nat.lt_trichotomy f n,
    { use f, simp [h] },
    { revert p, simp [h] },
    cases f,
    { revert h, simp },
    use f,
    rw [nat.succ_eq_add_one] at *,
    simp [show ¬ f < n, by linarith] },
  { intro p,
    cases f_ih p with g ih,
    use Λ g,
    simp [ih] },
  { rw [dot_uses, add_eq_zero_iff, and_imp],
    intros p q,
    cases f_ih_f p with x ihx,
    cases f_ih_g q with y ihy,
    use x·y,
    simp [ihx, ihy], }
end

theorem shift_succ_of_uses_zero: f.uses n = 0 → f ↑¹ (n+1) = f ↑¹ n :=
begin
  induction f generalizing n,
  { have h_iff : ∀ {α: Type*} (p q: Prop) (a b: α)
      [dp: decidable p] [dq: decidable q],
      (@ite _ _ dp a b = @ite _ _ dq a b) ↔ ((p ↔ q) ∨ a = b),
    { intros _ p q a b _ _,
      split_ifs;
      simp[h, h_1, @comm _ eq] },
    simpa [
      show f < n + 1 ↔ f ≤ n, by exact ⟨ nat.le_of_lt_succ, nat.succ_le_succ ⟩,
      h_iff (f ≤ n) (f < n) f (f+1), iff_def,
      eq_true_intro (le_of_lt)] using flip (@lt_of_le_of_ne _ _ f n) },
  { simpa using f_ih },
  { simpa using λ x y, and.intro (f_ih_f x) (f_ih_g y) }
end

theorem closed_below_iff_uses_zero (f: utlc) (n : ℕ) : f.closed_below n ↔ ∀ m, n ≤ m → f.uses m = 0 :=
begin
  induction f using lambda_calculus.utlc.notation_induction_on
    with _ _ fh _ _ fh gh generalizing n,
  { have hlt: ∀ x y : ℕ, (∀ z, x ≤ z → y = z → false) ↔ y < x,
    { intros x y,
      split,
      { intro h,
        contrapose! h,
        exact ⟨y, h, rfl, not_false⟩ },
      intros hyx z hxz,
      exact ne_of_lt (lt_of_lt_of_le hyx hxz) },
    simp [closed_below, hlt] },
  { rw [closed_below, fh (n + 1)],
    split,
    { intros h m hnm,
      rw [lambda_uses, h _ (nat.succ_le_succ hnm)] },
    intros h m,
    cases m,
    { simp },
    rw [nat.succ_eq_add_one, add_le_add_iff_right, ← lambda_uses],
    exact h _ },
  { simp [down_closed_below, fh, gh, forall_and_distrib] }
end

theorem closed_below_mono: n ≤ m → f.closed_below n → f.closed_below m :=
begin
  induction f generalizing n m,
  { simpa [closed_below] using flip lt_of_lt_of_le },
  { simpa [← @nat.succ_le_succ_iff n m, ← nat.succ_eq_add_one] 
      using @f_ih n.succ m.succ },
  { intro h,
    simpa using λ x y, and.intro (f_ih_f h x) (f_ih_g h y) }
end

theorem closed_below_mono': f.closed_below n → n ≤ m → f.closed_below m := flip closed_below_mono

theorem shift_of_closed_below:
  f.closed_below n → f ↑¹ n = f :=
begin
  induction f generalizing n,
  { simpa [closed_below] using not_le_of_gt },
  { simpa using f_ih },
  { simpa using λ x y, and.intro (f_ih_f x) (f_ih_g y) }
end

theorem shift_of_closed {f: utlc}:
  f.closed → ∀ n, f ↑¹ n = f := λ p n, shift_of_closed_below (closed_below_mono (nat.zero_le _) p) 

theorem shift_closed_below (m: ℕ):
  f.closed_below n → (f ↑¹ m).closed_below (n+1) :=
begin
  simp only [closed_below_iff_uses_zero, shift_uses],
  intros h m,
  cases m,
  { simp },
  rw [nat.succ_eq_add_one, nat.add_sub_cancel, nat.add_le_add_iff_right],
  intro hnm,
  split_ifs,
  { exact h _ hnm },
  { refl },
  apply h,
  linarith,
end

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

theorem substitution_uses_le {n m: ℕ} (hnm: n ≤ m) (f g: utlc):
  f[n:=g].uses m = f.uses (m + 1) + f.uses n * g.uses m :=
begin
  induction f generalizing n m g,
  { obtain hfn|hfn|hfn := nat.lt_trichotomy f n,
    { simp[hfn, ne_of_lt hfn,
        show f ≠ m, by linarith,
        show f ≠ m + 1, by linarith] },
    { simp [hfn, ne_of_lt (nat.lt_succ_of_le hnm)] },
    simp [lt_asymm hfn, ne_of_gt hfn,
      nat.sub_eq_iff_eq_add (nat.one_le_of_lt hfn)] },
  { simp [f_ih _ (nat.succ_le_succ hnm)] },
  { simp [f_ih_f _ hnm, f_ih_g _ hnm,
      add_mul, ← nat.add_assoc,
      nat.add_right_comm (f_f.uses (m + 1)) _ (f_g.uses (m + 1))] }
end

theorem substitution_uses_gt {n m: ℕ} (hnm: m < n) (f g: utlc):
  f[n:=g].uses m = f.uses m + f.uses n * g.uses m :=
begin
  induction f generalizing n m g,
  { obtain hfn|hfn|hfn := nat.lt_trichotomy f n,
    { simp[hfn, ne_of_lt hfn] },
    { simp[hfn, ne_of_gt hnm] },
    simp [lt_asymm hfn, ne_of_gt hfn, ne_of_gt (trans hnm hfn),
      show f - 1 ≠ m, begin
        cases f,
        { revert hfn, simp },
        rw [nat.succ_eq_add_one, nat.add_sub_cancel],
        intro hfm,
        rw [hfm] at hfn,
        apply not_lt_of_ge (nat.le_of_lt_succ hfn) hnm
      end] },
  { simp[f_ih _ (nat.succ_lt_succ hnm)] },
  { simp [f_ih_f _ hnm, f_ih_g _ hnm,
      add_mul, ← nat.add_assoc,
      nat.add_right_comm (f_f.uses m) _ (f_g.uses m)] }
end

theorem substitution_uses (f: utlc) (n: ℕ) (g: utlc) (m: ℕ):
  f[n:=g].uses m = f.uses (ite (n ≤ m) (m + 1) m) + f.uses n * g.uses m :=
begin
  by_cases n ≤ m,
  { simp [substitution_uses_le h, h] },
  { simp [substitution_uses_gt (lt_of_not_ge h), h] }
end

@[simp]
theorem down_substitution_self (n:ℕ) (f:utlc): (↓n)[n:=f] = f := by simp

@[simp]
theorem shift_succ_substitiution_down (n:ℕ) (f:utlc): (f ↑¹ (n+1))[n:=↓n] = f := begin
  induction f generalizing n,
  { obtain h|h|h := nat.lt_trichotomy f n,
    { simp [trans h (nat.lt_succ_self _), ne_of_lt h, not_le_of_gt h] },
    { simp[h] },
    simp [
      show ¬ f < n + 1, by linarith,
      show ¬ f + 1 < n, by linarith,
      show ¬ f + 1 = n, by linarith] },
  { simp[f_ih] },
  { simp [f_ih_f, f_ih_g] }
end

@[simp] theorem substitution_of_shift (f: utlc) (n: ℕ) (g: utlc): (f ↑¹ n)[n:=g] = f :=
begin
  induction f generalizing n g,
  { obtain h|h|h := nat.lt_trichotomy f n,
    { simp[h] },
    { simp [h]},
    simp [lt_asymm h,
      show ¬ f + 1 < n, by linarith,
      show ¬ f + 1 = n, by linarith] },
  { simp[f_ih] },
  { simp[f_ih_f, f_ih_g] }
end

theorem substitution_of_unused: f.uses n = 0 → ∀ g, (f ↑¹ (n + 1)) [n:=g] = f :=
by intros h g; rw [shift_succ_of_uses_zero h, substitution_of_shift]

theorem substitution_of_closed_below:
  f.closed_below n → ∀ g, f[n:=g] = f :=
begin
  intros h g,
  conv_lhs { rw [← shift_of_closed_below h] },
  exact substitution_of_shift _ _ _
end

theorem substitution_of_closed: f.closed → ∀ n g, f[n:=g] = f :=
  λ p n, substitution_of_closed_below (closed_below_mono (nat.zero_le _) p)

theorem substitution_of_closed_below_gt: f.closed_below (n+1) → g.closed_below n → m ≤ n → f[m:=g].closed_below n :=
begin
  rw [closed_below_iff_uses_zero, closed_below_iff_uses_zero, closed_below_iff_uses_zero],
  intros hf hg hmn x hnx,
  simp [substitution_uses, trans hmn hnx,
    hf _ (nat.succ_le_succ hnx), hg _ hnx],
end

theorem substitution_zero_closed: f.closed_below 1 → g.closed → f[0:=g].closed :=
  λ hf hg, substitution_of_closed_below_gt hf hg (le_refl _)

theorem size_substitution (f: utlc) (n: ℕ) (g: utlc): f[n:=g].size = f.size + (f.uses n) * (g.size - 1) :=
begin
  induction f generalizing n g,
  { obtain h|h|h := nat.lt_trichotomy f n,
    simp [h, ne_of_lt h],
    simp [h, nat.add_comm 1, nat.sub_add_cancel (size_pos' g)],
    simp [lt_asymm h, ne_of_gt h] },
  { simp[f_ih, nat.add_right_comm _ 1 _] },
  { simp[f_ih_f, f_ih_g, ← nat.add_assoc, add_mul,
      nat.add_right_comm _ _ f_g.size,
      nat.add_right_comm _ 1 _] }
end

theorem shift_substitution_comm (f: utlc) (n: ℕ) (g: utlc): (f ↑¹ n)[n+1:=g] = (f ↑¹ (n+1))[n:=g] :=
begin
  induction f generalizing n g,
  { obtain h₀|h₀|h₀ := nat.lt_trichotomy f n,
    { simp[h₀, trans h₀ (nat.lt_succ_self _)] },
    { simp[h₀] },
    cases nat.eq_or_lt_of_le (nat.succ_le_of_lt h₀) with h₁ h₁;
    rw [nat.succ_eq_add_one] at h₁,
    { simp [←h₁, nat.add_assoc] },
    { simp [lt_asymm h₀, ne_of_gt h₀, lt_asymm h₁,
        show ¬ f + 1 < n, by linarith,
        show ¬ f + 1 = n, by linarith] } },
  { simp[f_ih] },
  { simp[f_ih_f, f_ih_g] }
end

theorem substitution_shift_lt {n m: ℕ} (hnm: n < m) (f g: utlc): (f ↑¹ (m+1))[n:=(g ↑¹ m)] = f[n:=g] ↑¹ m  :=
begin
  induction f generalizing n m g,
  { obtain hfn|hfn|hfn := nat.lt_trichotomy f n,
    { simp[hfn, trans hfn hnm, trans hfn (trans hnm (nat.lt_succ_self _))] },
    { simp[hfn, trans hnm (nat.lt_succ_self _)] },
    cases f,
    { revert hfn; simp },
    rw [nat.succ_eq_add_one] at *,
    by_cases f < m,
    { simp[h, lt_asymm hfn, ne_of_gt hfn, nat.sub_lt, @eq_comm _ (f - 1)] },
    { simp[h, lt_asymm hfn, ne_of_gt hfn,
        show ¬ f + 1 + 1 < n, by linarith,
        show f + 1 + 1 ≠ n, by linarith] } },
  { simp [f_ih _ (nat.succ_lt_succ hnm)] },
  { simp [f_ih_f _ hnm, f_ih_g _ hnm] }
end

theorem substitution_shift_ge {n m: ℕ} (hmn: m ≤ n) (f g: utlc): (f ↑¹ m)[n+1:=(g ↑¹ m)] = f[n:=g] ↑¹ m :=
begin
  induction f generalizing n m g,
  { obtain hfm|hfm|hfm := nat.lt_trichotomy f m,
    { simp [hfm, lt_of_lt_of_le hfm hmn, trans (lt_of_lt_of_le hfm hmn) (nat.lt_succ_self _)] },
    { cases lt_or_eq_of_le hmn with hmn hmn;
      { simp[hfm, hmn] } },
    obtain hfn|hfn|hfn := nat.lt_trichotomy f n,
    { simp[lt_asymm hfm, hfn] },
    { simp [lt_asymm hfm, ← hfn] },
    { cases f,
      { revert hfm, simp },
      rw [nat.succ_eq_add_one] at *,
      simp [lt_asymm hfm, ne_of_gt hfm, lt_asymm hfn, ne_of_gt hfn,
        show ¬ f < m, by linarith] } },
  { simp [f_ih _ (nat.succ_le_succ hmn)] },
  { simp [f_ih_f _ hmn, f_ih_g _ hmn] }
end

theorem substitution_shift_zero (f: utlc) (n: ℕ) (g: utlc): (f ↑¹ (n+1))[0:=(g ↑¹ n)] = f[0:=g] ↑¹ n :=
begin
  cases n,
  { rw [← substitution_shift_ge (nat.zero_le _)],
    simp [shift_substitution_comm] },
  apply substitution_shift_lt (nat.zero_lt_succ _)
end

theorem substitution_dist_lt {n m: ℕ} (hnm: n < m) (f g g': utlc):
  f[n:=g][m:=g'] = f[m+1:=g' ↑¹ n][n:=g[m:=g']] :=
begin
  induction f generalizing n m g g',
  { obtain hfn|hfn|hfn := nat.lt_trichotomy f n,
    { simp [hfn, trans hfn hnm, trans (trans hfn hnm) (nat.lt_succ_self _)] },
    { simp [hfn, trans hnm (nat.lt_succ_self _)] },
    cases f,
    { revert hfn, simp },
    rw [nat.succ_eq_add_one] at *,
    obtain hfm|hfm|hfm := nat.lt_trichotomy f m,
    { simp [lt_asymm hfn, ne_of_gt hfn, hfm] },
    { simp [lt_asymm hfn, ne_of_gt hfn, ← hfm] },
    { simp [lt_asymm hfn, ne_of_gt hfn, lt_asymm hfm, ne_of_gt hfm,
        show ¬ f < n, by linarith, show f ≠ n, by linarith ] } },
  { simp[f_ih _ _ (nat.succ_lt_succ hnm),
         substitution_shift_ge (nat.zero_le _)] },
  { simp[f_ih_f _ _ hnm, f_ih_g _ _ hnm] }
end

theorem substitution_dist_eq (f: utlc) (n: ℕ) (g g': utlc):
  f[n:=g][n:=g'] = f[n+1:=g' ↑¹ n][n:=g[n:=g']] :=
begin
  induction f generalizing n g g',
  {
    obtain hfn|hfn|hfn := nat.lt_trichotomy f n,
    { simp [hfn, trans hfn (nat.lt_succ_self _)] },
    { simp [hfn] },
    cases f,
    { revert hfn; simp },
    rw [nat.succ_eq_add_one] at *,
    cases eq_or_lt_of_le (nat.le_of_lt_succ hfn) with hfn₁ hfn₁,
    { simp [hfn₁] },
    { simp [lt_asymm hfn, ne_of_gt hfn, lt_asymm hfn₁, ne_of_gt hfn₁] } },
  { simp [f_ih, substitution_shift_ge (nat.zero_le _)] },
  { simp [f_ih_f, f_ih_g] }
end

end utlc
end lambda_calculus