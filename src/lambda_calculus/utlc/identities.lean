import lambda_calculus.utlc.basic

namespace lambda_calculus
namespace utlc

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

variables {n m : ℕ}
variables {f g: utlc}

theorem size_pos (f: utlc): 0 < f.size := by
{ cases f, all_goals { simp}  }

@[simp] theorem shift_inj_iff {f: utlc} (n: nat) {g: utlc}: f ↑¹ n = g ↑¹ n ↔ f = g :=
begin
  split,
  induction f generalizing n g,
  { cases g;
    simp,
    split_ifs;
    try { { simp } };
    intro;
    linarith },
  { cases g;
    simp,
    apply f_ih },
  { cases g;
    simp,
    intros hf hg,
    exact ⟨ f_ih_f _ hf, f_ih_g _ hg ⟩ },
  intro p,
  rw [p],
end

theorem shift_comm (f: utlc): n ≤ m → f ↑¹ n ↑¹ (m+1) = f ↑¹ m ↑¹ n :=
begin
  induction f generalizing n m;
  simp;
  intro nm,
  { split_ifs; try { simp }; linarith },
  { apply f_ih, linarith },
  { exact ⟨f_ih_f nm, f_ih_g nm⟩ }
end

theorem shift_comm' (f: utlc) : n < m → f ↑¹ n ↑¹ m = f ↑¹ (m-1) ↑¹ n :=
begin
  cases m,
  { simp },
  { simp [nat.succ_eq_add_one],
    intro,
    apply shift_comm,
    linarith }
end

@[simp] theorem size_shift (f: utlc) (n: ℕ): (f ↑¹ n).size = f.size :=
begin
  induction f generalizing n;
  simp,
  { apply f_ih },
  { rw[f_ih_f, f_ih_g] }
end

theorem shift_uses (f: utlc) (n m: ℕ):
  (f ↑¹ n).uses m =
  if n < m then f.uses (m - 1)
  else if n = m then 0
  else f.uses m :=
begin
  induction f generalizing n m,
  all_goals { simp[uses] },
  { split_ifs;
    simp only [nat.zero_ne_one, nat.one_ne_zero, eq_self_iff_true];
    try { linarith };
    cases m;
    simp [
      add_left_inj,
      not_lt_zero',
      nat.succ_eq_add_one,
      zero_tsub,
      nat.add_sub_cancel] at *;
    try { contradiction };
    try { linarith },
    { apply h_3,
      apply nat.eq_zero_of_le_zero,
      rw [← h_4],
      assumption, },
    rw [h_4] at h,
    apply h_3,
    apply antisymm h h_2 },
  { rw [f_ih],
    simp,
    split_ifs,
    rw [nat.sub_add_cancel (nat.one_le_of_lt h)],
    all_goals { refl } },
  { rw[f_ih_f, f_ih_g],
    split_ifs,
    all_goals { refl } }
end

theorem shift_uses_lt {n m: ℕ}: n < m → ∀ (f: utlc), (f ↑¹ n).uses m = f.uses (m - 1) :=
begin
  intros p f,
  have h := shift_uses f n m,
  simp [p] at h,
  assumption
end

theorem shift_uses_zero (f: utlc): (f ↑¹ 0).uses 0 = 0 :=
begin
  have h := shift_uses f 0 0,
  simp at h,
  assumption
end

theorem shift_uses_zero' (f: utlc) (n: ℕ) : (f ↑¹ n).uses n = 0 :=
begin
  have h := shift_uses f n n,
  simp at h,
  assumption
end

theorem shift_of_uses {f: utlc} {n: ℕ}: f.uses n = 0 → ∃ g, f = g ↑¹ n :=
begin
  induction f generalizing n,
  all_goals { simp },
  { intro p,
    obtain h|h|h := nat.lt_trichotomy f n,
    { use f, simp [h] },
    { contradiction },
    cases f,
    { simp at h, contradiction },
    simp [nat.succ_eq_add_one] at *,
    use f,
    simp [show ¬ f < n, by linarith] },
  { intro p,
    cases f_ih p with g ih,
    use Λ g,
    simp,
    exact ih },
  { intros p q,
    cases f_ih_f p with x ihx,
    cases f_ih_g q with y ihy,
    use x·y,
    simp,
    exact ⟨ ihx, ihy ⟩ }
end

theorem closed_below_iff_uses_zero (f: utlc) (n : ℕ) : f.closed_below n ↔ ∀ m, n ≤ m → f.uses m = 0 :=
begin
  induction f with _ _ fh _ _ fh gh generalizing n,
  { simp [closed_below, uses],
    split,
    intros fn x nm fx,
    linarith,
    intro p,
    contrapose! p,
    use f,
    simp [p] },
  { simp[closed_below, uses],
    rw [fh (n + 1)],
    split,
    intros h m nm,
    specialize h (m + 1) (by linarith),
    assumption,
    intros h m,
    cases m,
    simp,
    simp [nat.succ_eq_add_one],
    apply h },
  { simp[closed_below, uses],
    split,
    intros pq m nm,
    exact ⟨(fh n).mp pq.left m nm, (gh n).mp pq.right m nm⟩,
    rw [fh, gh],
    intros pq,
    split,
    intros m nm,
    exact (pq m nm).left,
    intros m nm,
    exact (pq m nm).right }
end

theorem closed_below_mono: f.closed_below n → n ≤ m → f.closed_below m :=
begin
  induction f generalizing n m,
  all_goals { simp },
  { exact lt_of_lt_of_le },
  { intros _ _,
    apply f_ih,
    assumption,
    linarith },
  { intros hf hg nm,
    exact ⟨f_ih_f hf nm, f_ih_g hg nm⟩ }
end

theorem shift_of_closed_below:
  f.closed_below n → f ↑¹ n = f :=
begin
  induction f generalizing n,
  all_goals { simp [closed_below, shift] },
  { intros _ _, linarith },
  { apply f_ih },
  { intros hf hg, exact ⟨ f_ih_f hf, f_ih_g hg ⟩ }
end

theorem shift_of_closed {f: utlc}:
  f.closed → ∀ n, f ↑¹ n = f :=
begin
  unfold closed,
  intros p n,
  exact shift_of_closed_below (closed_below_mono p (nat.zero_le _))
end

theorem shift_closed_below (m: ℕ):
  f.closed_below n → (f ↑¹ m).closed_below (n+1) :=
begin
  induction f generalizing n m;
  simp,
  { split_ifs;
    { intro, linarith } },
  { apply f_ih },
  { intros hf hg,
    exact ⟨f_ih_f _ hf, f_ih_g _ hg⟩ }
end

@[simp] theorem index_substitution_zero : (↓n)[n:=f] = f := by simp

theorem shift_succ_substitiution_down: (f ↑¹ (n+1))[n:=↓n] = f := begin
  induction f generalizing n;
  simp,
  { split_ifs;
    try { refl };
    try { { rw [h_2] } };
    try {
      exfalso,
      apply h_2 (nat.eq_of_lt_succ_of_not_lt h h_1) };
    { exfalso, linarith } },
  { apply f_ih },
  { exact ⟨ f_ih_f, f_ih_g ⟩ }
end

@[simp] theorem substitution_of_shift (f: utlc) (n: ℕ) (g: utlc): (f ↑¹ n)[n:=g] = f :=
begin
  induction f generalizing n g,
  all_goals { simp[nat.add_assoc] },
  { split_ifs,
    refl,
    repeat { exfalso, linarith },
    rw [nat.add_sub_cancel] },
  { exact f_ih _ _ },
  { exact⟨ f_ih_f _ _, f_ih_g _ _⟩ }
end

theorem substitution_identity_of_closed_below (g: utlc): f.closed_below n → f[n:=g] = f :=
begin
  induction f generalizing n g,
  all_goals { simp },
  { intros fn nf,
    exfalso,
    linarith },
  { apply f_ih },
  { intros hf hg,
    exact ⟨f_ih_f _ hf, f_ih_g _ hg⟩ }
end

theorem substitution_identity_of_closed: f.closed → ∀ n g, f[n:=g] = f :=
  λ p n g, substitution_identity_of_closed_below _ (closed_below_mono p (nat.zero_le _))

theorem substitution_of_closed_below_gt: f.closed_below (n+1) → g.closed_below n → m ≤ n → f[m:=g].closed_below n :=
begin
  induction f generalizing n m g,
  all_goals { simp },
  { intros _ _ _,
    split_ifs,
    any_goals { simp },
    { linarith },
    { assumption },
    cases f,
    { simp,
      exfalso,
      exact h (zero_lt_iff.mpr (ne.symm h_1)) },
    { simp[nat.succ_eq_add_one] at *, linarith } },
  { intros hf hg _,
    apply f_ih hf (shift_closed_below _ hg),
    linarith },
  { intros hff hfg hg nm,
    exact ⟨f_ih_f hff hg nm, f_ih_g hfg hg nm⟩ }
end

theorem substitution_zero_closed: f.closed_below 1 → g.closed → f[0:=g].closed :=
  λ hf hg, substitution_of_closed_below_gt hf hg (le_refl _)

theorem size_substitution (f: utlc) (n: ℕ) (g: utlc): f[n:=g].size = f.size + (f.uses n) * (g.size - 1) :=
begin
  induction f generalizing n g,
  all_goals { simp },
  { split_ifs,
    any_goals { simp },
    { exfalso, linarith },
    rw [nat.add_comm, nat.sub_add_cancel],
    linarith [size_pos g] },
  { rw [f_ih],
    simp,
    ring },
  {
    rw [f_ih_f, f_ih_g],
    ring }
end

theorem shift_substitution_comm (f: utlc) (n: ℕ) (g: utlc): (f ↑¹ n)[n+1:=g] = (f ↑¹ (n+1))[n:=g] :=
begin
  induction f generalizing n g,
  all_goals { simp },
  { split_ifs,
    any_goals { refl },
    any_goals { exfalso, linarith },
    any_goals { simp at h_2, contradiction },
    simp at *,
    exfalso,
    exact h_2 (nat.eq_of_le_of_lt_succ h h_3) },
  { apply f_ih },
  { exact ⟨f_ih_f _ _, f_ih_g _ _⟩ }
end

theorem substitution_shift_lt (f: utlc) {n m: ℕ} (g: utlc): n < m → f[n:=g] ↑¹ m = (f ↑¹ (m+1))[n:=(g ↑¹ m)] :=
begin
  induction f generalizing n m g,
  all_goals { simp },
  { intro nm,
    split_ifs,
    any_goals { have x1 := lt_of_le_of_ne (le_of_not_lt h) (ne.symm h_1) },
    any_goals { exfalso, linarith },
    all_goals { simp[*] },
    { intro, linarith },
    all_goals { cases f },
    any_goals { exfalso, exact nat.not_lt_zero n x1 },
    all_goals { simp [nat.succ_eq_add_one] at * },
    { intro, linarith },
    { simp [show ¬ f < m, by linarith,
            show ¬ f + 1 + 1 < n, by linarith,
            show f + 1 + 1 ≠ n, by linarith] } },
  { simp [nat.add_assoc, ← shift_comm _ (nat.zero_le m)],
    intro,
    apply f_ih,
    linarith },
  { intro mn, exact ⟨f_ih_f _ mn, f_ih_g _ mn⟩ }
end

theorem substitution_shift_ge (f: utlc) {n m: ℕ} (g: utlc): m ≤ n → f[n:=g] ↑¹ m = (f ↑¹ m)[n+1:=(g ↑¹ m)] :=
begin
  induction f generalizing n m g,
  all_goals { simp },
  { intro mn,
    split_ifs;
    try { exfalso, linarith };
    simp[*];
    simp at *;
    try { contradiction },
    cases f;
    simp;
    intro,
    { apply h_4,
      apply eq.symm,
      apply nat.eq_zero_of_le_zero,
      assumption },
    simp [nat.succ_eq_add_one] at *,
    have h_5:= lt_of_le_of_ne' h h_1,
    linarith },
  { simp [nat.add_assoc, ← shift_comm _ (nat.zero_le m)],
    intro,
    apply f_ih,
    linarith },
  { intro mn, exact ⟨f_ih_f _ mn, f_ih_g _ mn⟩ }
end

theorem substitution_shift_zero (f: utlc) (n: ℕ) (g: utlc): f[0:=g] ↑¹ n = (f ↑¹ (n+1))[0:=(g ↑¹ n)] :=
begin
  cases n,
  { rw [substitution_shift_ge _ _ (nat.zero_le _)],
    simp [shift_substitution_comm] },
  apply substitution_shift_lt _ _ (nat.zero_lt_succ _),
end

theorem shift_substitution_index (f: utlc) (n: ℕ) (g: utlc): (f ↑¹ n)[n:=g] = f :=
begin
  induction f generalizing n g,
  all_goals { simp },
  { split_ifs,
    simp [h],
    simp [show ¬ (f + 1 < n), by linarith],
    linarith, exfalso,
    linarith,
    simp },
end

theorem substitution_uses_zero {n m: ℕ} {f g: utlc}: n ≤ m → f[n:=g].uses m = f.uses (m + 1) + f.uses n * g.uses m := 
begin
  induction f generalizing n m g;
  simp,
  { split_ifs;
    try { intro, exfalso, linarith };
    simp;
    repeat { intro };
    cases f;
    simp [nat.succ_eq_add_one] at *;
    try { contradiction };
    try { linarith },
    apply h_1 h.symm },
  { intro,
    rw [f_ih],
    simp [shift_uses],
    linarith },
  { intro p,
    rw [f_ih_f p, f_ih_g p],
    ring }
end

theorem substitution_index_succ: f.closed_below (n + 1) → f[n:=↓(n+1)] = f ↑¹ n :=
begin
  induction f generalizing n,
  all_goals { simp[nat.add_assoc] },
  { intro p,
    split_ifs,
    { refl },
    { rw [h_1] },
    { exfalso,
      exact h_1 (nat.eq_of_lt_succ_of_not_lt p h) } },
  { apply f_ih },
  { intros hf hg,
    exact ⟨f_ih_f hf, f_ih_g hg⟩ }
end

theorem substitution_dist_lt (f: utlc) {n: ℕ} {g: utlc} {m: ℕ} (g': utlc):
  n < m → g'.uses n = 0 →
  f[n:=g][m:=g'] = f[m+1:=g' ↑¹ n][n:=g[m:=g']] :=
begin
  induction f generalizing n m g g',
  { intros hm hg,
    simp,
    split_ifs,
    any_goals { simp },
    simp [h, h_1],
    any_goals { intro },
    any_goals { exfalso, linarith},
    simp [h_1],
    all_goals { cases f },
    any_goals { simp[nat.succ_eq_add_one] at * },
    any_goals { exfalso, apply h_1 (h.symm) },
    simp [show ¬ f + 1 < n, by linarith,
          h_1,
          show f < m + 1, by linarith],
    intro, exfalso, linarith,
    simp [h_3],
    simp [show ¬ f < m, by linarith, h_2, h_3,
          show ¬ f < n, by linarith],
    split_ifs,
    exfalso,
    simp [h_4] at h_3 h_2,
    linarith,
    refl },
  { intros hm hg,
    simp,
    rw [f_ih],
    rw [shift_comm],
    rw [substitution_shift_ge],
    any_goals { apply nat.zero_le _ },
    linarith,
    rw [shift_uses_lt],
    simp [hg],
    apply nat.zero_lt_succ },
  { intros hm hg,
    simp,
    split,
    apply f_ih_f,
    apply hm,
    apply hg,
    apply f_ih_g,
    apply hm,
    apply hg }
end

theorem substitution_dist_eq (f: utlc) {n: ℕ} (g: utlc) {g': utlc}:
  (g' ↑¹ n).uses n = 0 →
  f[n:=g][n:=g'] = f[n+1:=g' ↑¹ n][n:=g[n:=g']] :=
begin
  induction f generalizing n g g',
  all_goals { simp },
  { intro h,
    split_ifs,
    any_goals { simp [*] },
    any_goals { exfalso, linarith },
    { exfalso,
      exact h_2 (eq_of_le_of_not_lt (nat.le_of_lt_succ h_3) h_1) },
    cases f,
    { exfalso, linarith },
    simp [nat.succ_eq_add_one] at *,
    simp [show ¬ f < n, by linarith, h_4] },
  { intro h,
    rw [← shift_comm, substitution_shift_ge],
    apply f_ih,
    simp [shift_uses],
    all_goals { exact nat.zero_le _ } },
  { intro h,
    refine ⟨f_ih_f _ h, f_ih_g _ h⟩ }
end

theorem substitution_dist_zero (f g g': utlc):
  f[0:=g][0:=g'] = f[1:=g' ↑¹ 0][0:=g[0:=g']] := substitution_dist_eq _ _ (shift_uses_zero _)

end utlc
end lambda_calculus