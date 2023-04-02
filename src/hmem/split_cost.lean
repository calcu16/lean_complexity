import hmem.stack

universe u
variables {α: Type u} [has_zero α] [decidable_eq α]

def rel_iterate {α: Type u} (r: α → α → Prop): ℕ → α → α → Prop
| 0 a a' := a = a'
| (n+1) a a' := ∃ x, r a x ∧ rel_iterate n x a'


notation f`^~[`n`]` := rel_iterate f n

theorem rel_iterate_zero {α: Type u} (r: α → α → Prop) (a: α):
  r^~[0] a a := eq.refl _

theorem rel_iterate_zero_iff {α: Type u} (r: α → α → Prop) (a b: α):
  r^~[0] a b ↔ a = b := by refl

theorem rel_iterate_one_iff {α: Type u} (r: α → α → Prop) (a b: α):
  r^~[1] a b ↔ r a b :=
begin
  split,
  { intro h,
    rcases h with ⟨x, hr, h⟩,
    rw [rel_iterate_zero_iff] at h,
    rwa [← h] },
  { intro h,
    refine ⟨ b, h, rel_iterate_zero _ _⟩ },
end

theorem rel_iterate_succ_iff {α: Type u} (r: α → α → Prop) (a b: α) (n: ℕ):
  r^~[n+1] a b ↔ ∃ x, r a x ∧ (r^~[n]) x b := by refl

theorem rel_iterate_succ_iff' {α: Type u} (r: α → α → Prop) (a b: α) (n: ℕ):
  r^~[n+1] a b ↔ ∃ x, r^~[n] a x ∧ r x b :=
begin
  induction n generalizing a b,
  { simp only [rel_iterate_succ_iff, rel_iterate_zero_iff, exists_eq_left', exists_eq_right] },
  { simp only [nat.succ_add, rel_iterate_succ_iff _ a, n_ih _ b, ← exists_and_distrib_left, ← exists_and_distrib_right, and_assoc],
    rw [exists_comm] },
end

theorem rel_iterate_sum_iff {α: Type u} (r: α → α → Prop) (a b: α) (n m: ℕ):
  r^~[n+m] a b ↔ ∃ x, r^~[n] a x ∧ (r^~[m]) x b :=
begin
  induction n generalizing a b,
  { simp only [zero_add, rel_iterate_zero_iff, exists_eq_left'] },
  { simp only [nat.succ_add, rel_iterate_succ_iff, n_ih, ← exists_and_distrib_left, ← exists_and_distrib_right, and_assoc],
    rw [exists_comm] }
end


namespace hmem

def program.max_internal_cost: program α → ℕ
| [] := 1
| ((@instruction.ite _ _ _ is')::is) := max (program.max_internal_cost is) (program.max_internal_cost is') + 1
| (i::is) := program.max_internal_cost is + 1


namespace thunk

def step_over (t r: thunk α): Prop :=
  match t.step with
  | (sum.inl t') := t' = r
  | (sum.inr (sum.inl m)) := false
  | (sum.inr (sum.inr (p, m, t'))) :=
    (p.get_or_else t.function).has_result m (r.state.getm 0)
    ∧ r = t'.set_result (r.state.getm 0) 
  end

theorem step_over_unique {t r r': thunk α}:
  step_over t r → step_over t r' → r = r' :=
begin
  cases hstep:t.step,
  { simp only [step_over, hstep],
    intros hr hr',
    rw [← hr, ← hr'] },
  rcases val with _|⟨_, _, _⟩,
  { simp only [step_over, hstep, false_implies_iff] },
  simp only [step_over, hstep, and_imp],
  intros hres hr hres' hr',
  rw [hr, hr', program.unique_result hres hres']
end

theorem step_over_decreasing {t r: thunk α}:
  step_over t r → r.current.max_internal_cost < t.current.max_internal_cost :=
begin
  cases t,
  cases t_current,
  { simp only [step_over, stack.step, step, false_implies_iff] },
  cases t_current_hd;
  try { simp only [step_over, stack.step, step, program.max_internal_cost],
    intro hr,
    simpa only [← hr] using nat.lt_succ_self _ };
  try { simp only [step_over, stack.step, step, program.max_internal_cost, and_imp],
    intros _ hr,
    rw [hr],
    exact nat.lt_succ_self _ },
  { simp only [step_over, stack.step, step, program.max_internal_cost],
    intro hr,
    simp only [← hr],
    apply lt_of_le_of_lt _ (nat.lt_succ_self _),
    by_cases t_current_hd_cond t_state.getv,
    { simp only [h, if_true, le_max_right] },
    { simp only [h, if_false, le_max_left] } },
end

theorem step_over_irrefl (t: thunk α):
  ¬ step_over t t := λ h, lt_irrefl _ (step_over_decreasing h)
  
def external_time_cost_step (t: thunk α) (c r: ℕ): Prop :=
  match t.step with
  | (sum.inl _) := true
  | (sum.inr (sum.inl _)) := true
  | (sum.inr (sum.inr (p, m, _))) :=
      (option.map (λ p : program α, p.has_time_cost m c) p).get_or_else
        (t.function.has_time_cost m r)
  end

theorem external_time_cost_step_mono {t: thunk α} {c₀ r₀ c₁ r₁: ℕ}:
  external_time_cost_step t c₀ r₀ → c₀ ≤ c₁ → r₀ ≤ r₁ → external_time_cost_step t c₁ r₁ :=
begin
  cases hstep:t.step,
  { simp only [external_time_cost_step, hstep, imp_true_iff] },
  cases val,
  { simp only [external_time_cost_step, hstep, imp_true_iff] },
  rcases val with ⟨_ | _, _, _⟩;
  simp only [external_time_cost_step, hstep, option.map_none', option.map_some', option.get_or_else];
  intros h hc hr,
  { exact program.time_cost_mono h hr },
  { exact program.time_cost_mono h hc }
end

theorem external_time_cost_step_independent {t: thunk α} {c₀ r₀ c₁ r₁: ℕ}:
  external_time_cost_step t c₀ r₀ → external_time_cost_step t c₁ r₁ → external_time_cost_step t c₀ r₁ :=
begin
  cases hstep:t.step,
  { simp only [external_time_cost_step, hstep, imp_true_iff] },
  cases val,
  { simp only [external_time_cost_step, hstep, imp_true_iff] },
  rcases val with ⟨_ | _, _, _⟩;
  simp only [external_time_cost_step, hstep],
  { exact λ _ h, h },
  { exact λ h _, h }
end

def split_time_cost: thunk α → ℕ → ℕ → ℕ → Prop
| _ 0 _ _ := false
| t (i+1) c r := t.current = [] ∨ ∃ t' c₀ c₁ r₀ r₁, external_time_cost_step t c₀ r₀ ∧ step_over t t' ∧ split_time_cost t' i c₁ r₁ ∧ c = c₀ + c₁ ∧ r = r₀ + r₁ 

theorem split_cost_independent {t: thunk α} {i₀ c₀ r₀ i₁ c₁ r₁ i₂ c₂ r₂: ℕ}:
  split_time_cost t i₀ c₀ r₀ → split_time_cost t i₁ c₁ r₁ → split_time_cost t i₂ c₂ r₂ →
  split_time_cost t i₀ c₁ r₂ :=
begin
  induction i₀ generalizing t c₀ r₀ i₁ c₁ r₁ i₂ c₂ r₂,
  { exact false.rec_on _ },
  intro h₀, rcases h₀ with _|⟨t', c₀₀, c₀₁, r₀₀, r₀₁, hex₀, hstep₀, hsplit₀, hc₀, hr₀⟩, { exact λ _ _, or.inl h₀ },
  cases i₁, { exact false.rec_on _ },
  intro h₁, rcases h₁ with _|⟨t₁, c₁₀, c₁₁, r₁₀, r₁₁, hex₁, hstep₁, hsplit₁, hc₁, hr₁⟩, { exact λ _, or.inl h₁ },
  cases i₂, { exact false.rec_on _ },
  intro h₂, rcases h₂ with _|⟨t₂, c₂₀, c₂₁, r₂₀, r₂₁, hex₂, hstep₂, hsplit₂, hc₂, hr₂⟩, { exact or.inl h₂ },
  rw [step_over_unique hstep₁ hstep₀] at hsplit₁,
  rw [step_over_unique hstep₂ hstep₀] at hsplit₂,
  exact or.inr ⟨t', _, _, _, _, external_time_cost_step_independent hex₁ hex₂, hstep₀, i₀_ih hsplit₀ hsplit₁ hsplit₂, hc₁, hr₂⟩
end

theorem split_cost_mono {t: thunk α} {i c r i' c' r': ℕ}:
  split_time_cost t i c r → i ≤ i' → c ≤ c' → r ≤ r' →
  split_time_cost t i' c' r' :=
begin
  induction i generalizing t c r i' c' r',
  { exact false.rec_on _ },
  intros h hi' hc' hr',
  cases i', { exact (nat.not_succ_le_zero _) hi' },
  rcases h with _|⟨t', c₀, c₁, r₀, r₁, hex, hstep, hsplit, hc, hr⟩,
  { exact or.inl h },
  refine or.inr ⟨t', c₀, c' - c₀, r₀, r' - r₀, hex, hstep, i_ih hsplit _ _ _, _, _⟩,
  { exact nat.succ_le_succ_iff.mp hi' },
  { apply le_trans',
    apply nat.sub_le_sub_right hc',
    rw [hc, nat.add_sub_cancel_left] },
  { apply le_trans',
    apply nat.sub_le_sub_right hr',
    rw [hr, nat.add_sub_cancel_left] },
  { rw [add_comm, nat.sub_add_cancel],
    apply le_trans' hc',
    rw [hc],
    exact le_add_right (le_refl _) },
  { rw [add_comm, nat.sub_add_cancel],
    apply le_trans' hr',
    rw [hr],
    exact le_add_right (le_refl _) },
end

theorem not_split_time_cost_zero (t: thunk α) (c r: ℕ):
  ¬ split_time_cost t 0 c r := by cases t; cases t_current; exact not_false


theorem split_time_cost_one (t: thunk α) (c r: ℕ):
  split_time_cost t 1 c r → t.current = [] :=
begin
  intro h,
  cases h,
  { assumption },
  rcases h with ⟨_, _, _, _, _, _, _, hso, _⟩,
  exact absurd hso (not_split_time_cost_zero _ _ _),
end

theorem iterate_step_of_step_over {t r: thunk α}:
  t.step_over r → ∃ n, (stack.step)^[n] (stack.execution t []) = stack.execution r [] :=
begin
  cases hstep:t.step,
  { simp only [thunk.step_over, hstep],
    intro h,
    use 1,
    simp only [function.iterate_one, stack.step, hstep, h, eq_self_iff_true, and_true] },
  cases val,
  { simp only [thunk.step_over, hstep],
    trivial },
  rcases val with ⟨_, _, _⟩,
  simp only [thunk.step_over, hstep, and_imp],
  intros hres hr,
  cases hres with n hres,
  rcases stack.step_iterate_return hres _ [] with ⟨m, hm, hres⟩,
  use m + 1,
  rw [list.nil_append] at hres,
  simp only [function.iterate_succ_apply, stack.step, program.call, hstep],
  rw [hres, ← hr]
end

theorem iterate_step_of_iterate_step_over {t: thunk α} {n: ℕ} {r: thunk α}:
  step_over^~[n] t r → ∃ n', (stack.step)^[n'] (stack.execution t []) = stack.execution r [] :=
begin
  induction n generalizing t,
  { rw [rel_iterate_zero_iff],
    exact λ h, ⟨0, h ▸ rfl⟩ },
  { simp only [rel_iterate_succ_iff, exists_imp_distrib, and_imp],
    intros x h_hd h_tl,
    cases iterate_step_of_step_over h_hd with n_hd h_hd,
    cases n_ih h_tl with n_tl h_tl,
    use n_tl + n_hd,
    rw [function.iterate_add_apply, h_hd, h_tl] }
end

theorem iterate_step_of_iterate_step_over' {t: thunk α} {n: ℕ} {p: program α} {m: memory α}:
  step_over^~[n] t ⟨p, [], m⟩ → ∃ n', (stack.step)^[n'] (stack.execution t []) = stack.result m :=
begin
  intro h,
  cases iterate_step_of_iterate_step_over h with n h,
  refine ⟨n + 1, _⟩,
  rw [function.iterate_succ_apply', h],
  refl
end

theorem step_over_function {t t': thunk α}:
  step_over t t' → t.function = t'.function :=
begin
  intro h,
  cases iterate_step_of_step_over h with n h,
  exact stack.nstep_function' h,
end

theorem step_over_function' {p p' is is': program α} {m m': memory α}:
  step_over ⟨p, is, m⟩ ⟨p', is', m'⟩ → p = p' := step_over_function

theorem step_over_succ {p inp: program α} {n: ℕ} {m m': memory α}:
  step_over^~[n + 1] ⟨p, inp, m⟩ ⟨p, [], m'⟩ →
  ∃ x y, step_over ⟨p, inp, m⟩ ⟨p, x, y⟩ ∧ (step_over^~[n]) ⟨p, x, y⟩ ⟨p, [], m'⟩ :=
begin
  simp only [rel_iterate_succ_iff, exists_imp_distrib, and_imp],
  intros x hstep hnstep,
  cases x,
  have h := (step_over_function' hstep).symm,
  rw [h] at *,
  exact ⟨_, _, hstep, hnstep⟩
end

theorem exists_external_cost {t t': thunk α}:
  t.step_over t' →
  ∃ c r, t.external_time_cost_step c r :=
begin
  cases hstep:t.step,
  { refine λ _, ⟨0, 0, _⟩,
    simp only [external_time_cost_step, hstep] },
  cases val,
  { simp only [step_over, hstep, false_implies_iff] },
  rcases val with ⟨_|_, _, _⟩;
  simp only [step_over, hstep, external_time_cost_step, option.map_none', option.map_some', option.get_or_else, and_imp];
  intros h _;
  cases h with n h,
  { exact ⟨0, n, _, h⟩ },
  { exact ⟨n, 0, _, h⟩ }
end

theorem time_cost_of_external_cost {t: thunk α} {c r: ℕ} {t': thunk α}:
  t.step_over t' → t.external_time_cost_step c r →
  ∃ m ≤ (c + r), (stack.step)^[m + 1] (stack.execution t []) = stack.execution t' [] :=
begin
  cases hstep:t.step,
  { simp only [step_over, hstep],
    intros ht _,
    refine ⟨0, le_add_self, _⟩,
    simp only [function.iterate_one, stack.step, hstep, ht, eq_self_iff_true, and_true] },
  cases val,
  { simp only [step_over, hstep, false_implies_iff] },
  rcases val with ⟨_, _, _⟩,
  cases val_fst;
  { simp only [step_over, external_time_cost_step, hstep, and_imp, option.get_or_else_none, option.map_none', option.get_or_else_some, option.map_some'],
    intros hres ht hcost,
    cases hcost with m hcost,
    rcases stack.step_iterate_return' hcost val_snd_snd with ⟨r', hr', hcost'⟩,
    refine ⟨r', by linarith, _⟩,
    simp only [function.iterate_succ_apply, option.get_or_else_none, option.get_or_else_some, program.call, stack.step, hstep, hcost', eq_self_iff_true, and_true],
    rw [ht],
    exact congr_arg _ (program.unique_result ⟨_, hcost⟩ hres) },
end

theorem external_cost_of_time_cost {t: thunk α} {n: ℕ} {t': thunk α}:
  t.step_over t' →
  ((stack.step)^[n] (stack.execution t [])) = stack.execution t' [] →
  ∃ c r, c + r < n ∧ t.external_time_cost_step c r :=
begin
  induction n using nat.strong_induction_on with n ih generalizing t t',
  cases n,
  { rw [function.iterate_zero_apply, stack.execution.inj_eq, eq_self_iff_true, and_true],
    intros hso ht,
    rw [ht] at hso,
    exact absurd hso (step_over_irrefl _) },
  cases hstep:t.step,
  { exact λ _ _, ⟨0, 0, nat.zero_lt_succ _, by simp only [external_time_cost_step, hstep] ⟩ },
  cases val,
  { simp only [step_over, hstep, false_implies_iff] },
  rcases val with ⟨_ | _, _, _⟩;
  simp only [function.iterate_succ_apply, stack.step, step_over, external_time_cost_step, hstep,
    and_imp, option.get_or_else, option.map_none', option.map_some', program.call];
  intros hres ht hcost;
  rcases stack.result_of_step_iterate hcost with ⟨m, n', hn, hcost⟩,
  exact ⟨0, n', nat.lt_succ_of_le ((nat.zero_add n').symm ▸ hn), ⟨_, hcost⟩⟩,
  exact ⟨n', 0, nat.lt_succ_of_le ((nat.add_zero n').symm ▸ hn), ⟨_, hcost⟩⟩,
end

theorem iterate_step_over_of_iterate_step {t: thunk α} {n:ℕ} {t': thunk α}:
  stack.step^[n] (stack.execution t []) = stack.execution t' [] →
  ∃ n', thunk.step_over^~[n'] t t' :=
begin
  induction n using nat.strong_induction_on with n ih generalizing t t',
  cases n,
  { rw [function.iterate_zero_apply, stack.execution.inj_eq, and_imp],
    exact λ h _, ⟨0, h⟩ },
  rw [function.iterate_succ_apply],
  cases hstep:t.step,
  { simp only [stack.step, hstep],
    intro h,
    cases ih n (nat.lt_succ_self _) h with n' ih,
    use n'+1,
    rw [rel_iterate_succ_iff],
    refine ⟨_, _, ih⟩,
    simp only [thunk.step_over, hstep] },
  cases val,
  { simp [stack.step, hstep, stack.result_halt] },
  { rcases val with ⟨_, _, c'⟩,
    simp only [stack.step, hstep],
    intro h,
    rcases stack.result_of_step_iterate h with ⟨m, n₁, hn₁, h₁⟩,
    rcases stack.step_iterate_return h₁ c' [] with ⟨n₂, hn₂, h₂⟩,
    rw [list.nil_append] at h₂,
    cases nat.exists_eq_add_of_le (trans hn₂ hn₁) with x hx,
    rw [hx, nat.add_comm, function.iterate_add_apply, h₂] at h,
    cases ih _ _ h with y hy,
    { refine ⟨y + 1, _, _, hy⟩,
      cases c',
      simp only [step_over, hstep, program.has_result,
        thunk.set_result, memory.getm_setm,
        eq_self_iff_true, and_true],
      exact ⟨_, h₁⟩ },
    apply nat.lt_succ_of_le,
    rw [hx, add_comm],
    exact le_self_add },
end

theorem iterate_step_over_iff_iterate_step {t: thunk α} {m: memory α}:
  (∃ n, stack.step^[n] (stack.execution t []) = stack.result m) ↔
  (∃ n, step_over^~[n] t ⟨t.function, [], m⟩) :=
begin
  split,
  { intro h,
    cases h with n h,
    rw stack.result_nprev' at h,
    rcases h with ⟨n', hn, h⟩,
    exact iterate_step_over_of_iterate_step h },
  { intro h,
    cases h with _ h,
    exact iterate_step_of_iterate_step_over' h }
end 

theorem time_cost_of_split {t: thunk α} {i c r: ℕ}:
  split_time_cost t i c r →
  ∃ m, (stack.step)^[i + c + r] (stack.execution t []) = stack.result m :=
begin
  induction i generalizing t c r,
  { exact flip absurd (not_split_time_cost_zero _ _ _) },
  simp only [nat.succ_add, split_time_cost, or_imp_distrib, exists_imp_distrib, and_imp, step_nil_iff],
  split,
  { intros _ h,
    simp only [function.iterate_succ_apply, stack.step, h, stack.result_halt, exists_eq'] },
  intros t' c₀ c₁ r₀ r₁ hex hso hcost hc hr,
  rcases time_cost_of_external_cost hso hex with ⟨n, hn, h⟩,
  rw [← @nat.sub_add_cancel (i_n + c + r) n, ← nat.add_succ, function.iterate_add_apply, h],
  { apply stack.result_mono (i_ih hcost),
    rw [show i_n + c + r = i_n + c₁ + r₁ + (c₀ + r₀), by rw [hc, hr]; ring,
      nat.add_sub_assoc hn],
    exact le_self_add },
  rw [show i_n + c + r = i_n + c₁ + r₁ + (c₀ + r₀), by rw [hc, hr]; ring],
  exact le_add_left hn,
end

theorem time_cost_of_split' {t: thunk α} {n: ℕ} {i c r: ℕ}:
  split_time_cost t i c r →
  n = i + c + r →
  ∃ m, (stack.step)^[n] (stack.execution t []) = stack.result m :=
λ h hn, hn.symm ▸ time_cost_of_split h

theorem result_or_step_over {t: thunk α} {m: memory α} {n: ℕ}:
  (stack.step)^[n] (stack.execution t []) = stack.result m →
  (stack.execution t []).step = stack.result m ∨
  ∃ t' n', thunk.step_over t t' ∧ (stack.step^[n'] (stack.execution t' [])) = stack.result m :=
begin
  intro h,
  cases iterate_step_over_iff_iterate_step.mp ⟨_, h⟩ with n₁ h₁,
  cases n₁,
  { left,
    rw [rel_iterate_zero_iff] at h₁,
    rw [h₁],
    refl },
  right,
  rw [rel_iterate_succ_iff] at h₁,
  rcases h₁ with ⟨t', ht, h₂⟩,
  cases iterate_step_of_iterate_step_over' h₂ with n₃ h₃,
  exact ⟨t', n₃, ht, h₃⟩
end

theorem result_or_external_cost {t: thunk α} {m: memory α} {n: ℕ}:
  (stack.step)^[n] (stack.execution t []) = stack.result m →
  (stack.execution t []).step = stack.result m ∨ 
  ∃ t' n₀ n₁ c r, external_time_cost_step t c r ∧ thunk.step_over t t' ∧ (stack.step^[n₁]) (stack.execution t' []) = stack.result m ∧ c + r < n₀ ∧ n₀ + n₁ = n :=
begin
  intro h₀,
  rcases result_or_step_over h₀ with h₁|⟨t', n₁, hso, h₁⟩,
  { exact or.inl h₁ },
  right,
  rcases exists_external_cost hso with ⟨c₀, r₀, hex₀⟩,
  rcases time_cost_of_external_cost hso hex₀ with ⟨n₂, hn₂, h₂⟩,
  rcases external_cost_of_time_cost hso h₂ with ⟨c₁, r₁, hcr, hex₁⟩,
  refine ⟨t', n₂ + 1, n - (n₂ + 1), c₁, r₁, hex₁, hso, stack.nstep_result_sub h₂ h₀, hcr, _⟩,
  rw [nat.add_comm, nat.sub_add_cancel],
  by_contradiction,
  rw [not_le] at h,
  cases nat.exists_eq_add_of_lt h with x hx,
  simpa only [hx, add_assoc n x 1, add_comm n (x + 1), function.iterate_add_apply _ (x + 1) n, h₀, stack.result_halt] using h₂
end

theorem split_cost_of_time_cost {t: thunk α} {m: memory α} {n: ℕ}:
  (stack.step)^[n] (stack.execution t []) = stack.result m →
  ∃ i c r, i + c + r ≤ n ∧ split_time_cost t i c r :=
begin
  induction n using nat.strong_induction_on with n ih generalizing t m,
  cases n,
  { simp only [function.iterate_zero_apply, false_implies_iff] },
  intro h,
  rcases result_or_external_cost h with h|⟨t', n₀, n₁, c₁, r₁, hex, hso, hs, hn₀, hn⟩,
  { refine ⟨1, 0, 0, nat.succ_le_succ (nat.zero_le _), or.inl _⟩,
    cases hstep:t.step,
    { simpa only [stack.step, hstep] using h },
    cases val,
    { simp only [step_nil_iff, hstep, exists_eq'] },
    rcases val with ⟨_|_,_,_⟩;
    { simpa only [stack.step, hstep] using h } },
  rcases ih _ _ hs with ⟨i₁, c₂, r₂, hn₁, ih⟩,
  { refine ⟨i₁ + 1, c₁ + c₂, r₁ + r₂, _, _⟩,
    { rw [← hn],
      linarith },
    exact or.inr ⟨_, _, _, _, _, hex, hso, ih, rfl, rfl⟩ },
  rw [← hn],
  exact lt_add_of_pos_left _ (pos_of_gt hn₀),
end

theorem apply_step_over {t t': thunk α} {m: memory α}:
  thunk.step_over t t' →
  (∃ n, (stack.step^[n]) (stack.execution t' []) = (stack.result m)) →
  ∃ n, (stack.step^[n]) (stack.execution t []) = (stack.result m) :=
begin
  intros hso hs,
  cases iterate_step_of_step_over hso with _ h,
  cases hs with _ h',
  exact ⟨_ + _, by rw[function.iterate_add_apply, h, h'] ⟩,
end

theorem apply_step_over_call {p: program α} {s: source α} {func is: program α} {m m' r: memory α}:
  func.has_result (m.getms s) m' →
  (∃ n, (stack.step^[n]) (stack.execution ⟨p, is, m.setm 0 m'⟩ []) = stack.result r) →
  (∃ n, (stack.step^[n]) (stack.execution ⟨p, (instruction.call func s)::is, m⟩ []) = stack.result r) :=
begin
  intro h,
  apply apply_step_over,
  simp only [thunk.step_over, thunk.step, set_result, 
    option.get_or_else, option.map_some',
    memory.getm_setm, memory.setm_setm, h,
    true_and, eq_self_iff_true],
end

theorem apply_step_over_recurse {p: program α} {s: source α} {is: program α} {m m' r: memory α}:
  p.has_result (m.getms s) m' →
  (∃ n, (stack.step^[n]) (stack.execution ⟨p, is, m.setm 0 m'⟩ []) = stack.result r) →
  (∃ n, (stack.step^[n]) (stack.execution ⟨p, (instruction.recurse s)::is, m⟩ []) = stack.result r) :=
begin
  intro h,
  apply apply_step_over,
  simp only [thunk.step_over, thunk.step, set_result, 
    option.get_or_else, option.map_none',
    memory.getm_setm, memory.setm_setm, h,
    true_and, eq_self_iff_true],
end

theorem apply_step_over' {p is₀ is₁ is₂: program α} {m₀ m₁ m₂: memory α}:
  is₀ = is₁ →
  thunk.step_over ⟨p, is₁, m₀⟩ ⟨p, is₂, m₁⟩ →
  (∃ n, (stack.step^[n]) (stack.execution ⟨p, is₂, m₁⟩ []) = (stack.result m₂)) →
  ∃ n, (stack.step^[n]) (stack.execution ⟨p, is₀, m₀⟩ []) = (stack.result m₂) :=
λ his, his ▸ apply_step_over
end thunk

namespace program

def internal_cost (p: program α) (inp: memory α) (i: ℕ): Prop :=
  ∃ c r, (p.call inp).split_time_cost i c r

def call_cost (p: program α) (inp: memory α) (c: ℕ): Prop :=
  ∃ i r, (p.call inp).split_time_cost i c r

def recurse_cost (p: program α) (inp: memory α) (r: ℕ): Prop :=
  ∃ i c, (p.call inp).split_time_cost i c r

theorem recurse_cost_mono {p: program α} {inp: memory α} {r r': ℕ}:
  p.recurse_cost inp r → r ≤ r' → p.recurse_cost inp r' :=
begin
  intros h hr,
  rcases h with ⟨i, c, h⟩,
  exact ⟨i, c, thunk.split_cost_mono h (le_refl _) (le_refl _) hr⟩,
end

theorem split_cost_of_components {p: program α} {inp: memory α} {i c r: ℕ}:
  internal_cost p inp i → call_cost p inp c → recurse_cost p inp r →
  (p.call inp).split_time_cost i c r :=
begin
  intros hi hc hr,
  rcases hi with ⟨_, _, hi⟩,
  rcases hc with ⟨_, _, hc⟩,
  rcases hr with ⟨_, _, hr⟩,
  exact thunk.split_cost_independent hi hc hr
end

theorem internal_cost_bound_helper_step {t: thunk α} {t': thunk α}:
  thunk.step_over t t' → t'.current.max_internal_cost < t.current.max_internal_cost :=
begin
  cases t,
  cases t_current,
  { simp only [thunk.step_over, thunk.step, false_implies_iff] },
  cases t_current_hd;
  try { simp only [thunk.step_over, thunk.step],
    intro h,
    rw [← h],
    simpa only [program.max_internal_cost] using nat.lt_succ_self _ };
  try { simp only [thunk.step_over, thunk.step, and_imp],
    intros _ h,
    rw [h],
    simpa only [program.max_internal_cost] using nat.lt_succ_self _ },
  simp only [thunk.step_over, thunk.step],
  by_cases (t_current_hd_cond t_state.getv);
  simp only [h, if_true];
  intro h;
  rw [← h],
  simpa only [program.max_internal_cost] using nat.lt_succ_of_le (le_max_right _ _),
  simpa only [program.max_internal_cost] using nat.lt_succ_of_le (le_max_left _ _)
end

theorem internal_cost_bound_helper {t: thunk α} {n: ℕ} {m: memory α}:
  thunk.step_over^~[n] t ⟨t.function, [], m⟩ → n < t.current.max_internal_cost :=
begin
  induction n generalizing t,
  {  rw [rel_iterate_zero_iff],
    intro h,
    rw [h],
    cases t,
    unfold max_internal_cost,
    exact nat.zero_lt_one },
  simp only [rel_iterate_succ_iff, exists_imp_distrib, and_imp],
  intros t' hd tl,
  rw [thunk.step_over_function hd] at tl,
  exact nat.succ_le_of_lt (nat.lt_of_le_of_lt (n_ih tl) (internal_cost_bound_helper_step hd))
end

theorem internal_cost_bound_helper' {p: program α} {n: ℕ} {m m': memory α}:
  thunk.step_over^~[n] (p.call m) ⟨p, [], m'⟩ → n < p.max_internal_cost :=
internal_cost_bound_helper

theorem internal_cost_of_step_over_helper {t: thunk α} {n: ℕ} {m: memory α}:
  (thunk.step_over^~[n]) t ⟨t.function, [], m⟩ → ∃ c r, t.split_time_cost (n + 1) c r :=
begin
  induction n generalizing t,
  { rw [rel_iterate_zero_iff],
    exact λ h, ⟨0, 0, h.symm ▸ or.inl rfl⟩ },
  simp only [rel_iterate_succ_iff, exists_imp_distrib, and_imp],
  intros t' hd tl,
  rcases thunk.exists_external_cost hd with ⟨c₀, r₀, hex⟩,
  rw [thunk.step_over_function hd] at tl,
  rcases n_ih tl with ⟨c₁, r₁, ih⟩,
  exact ⟨_, _, or.inr ⟨_, _, _, _, _, hex, hd, ih, rfl, rfl⟩⟩,
end

theorem internal_cost_of_step_over_helper' {t: thunk α} {i c r: ℕ}:
  t.split_time_cost i c r → ∃ (n < i) m, (thunk.step_over^~[n]) t ⟨t.function, [], m⟩:=
begin
  induction i generalizing t c r,
  { exact flip absurd (thunk.not_split_time_cost_zero _ _ _) },
  intro h,
  cases h,
  { cases t,
    refine ⟨_, nat.zero_lt_succ _, t_state, _⟩,
    rw [rel_iterate_zero_iff, ← h] },
  rcases h with ⟨t', _, _, _, _, _, hd, hsplit, _⟩,
  rcases i_ih hsplit with ⟨n, hn, m, tl⟩,
  rw [← thunk.step_over_function hd] at tl,
  exact ⟨_, nat.succ_le_succ hn, _, ⟨_, hd, tl⟩⟩
end

theorem internal_cost_bound {p: program α} {n: ℕ} {m: memory α}:
  p.internal_cost m n → p.internal_cost m p.max_internal_cost :=
begin
  intro h,
  rcases h with ⟨c, r, h⟩,
  rcases internal_cost_of_step_over_helper' h with ⟨_, _, _, h⟩,
  rw [program.call_function] at h,
  rcases internal_cost_of_step_over_helper h with ⟨c, r, h'⟩,
  exact ⟨c, r, thunk.split_cost_mono h' (nat.succ_le_of_lt ( internal_cost_bound_helper' h)) (le_refl _) (le_refl _)⟩
end

def recurse_arg (p: program α) (inp arg: memory α): Prop :=
  ∃ n t t', (thunk.step_over^~[n] (p.call inp) t) ∧ t.step = sum.inr (sum.inr (option.none, arg, t'))

def max_recurse_count: program α → ℕ
| ((instruction.recurse _)::is) := max_recurse_count is + 1
| ((@instruction.ite _ _ _ is')::is) := max (max_recurse_count is) (max_recurse_count is')
| (i::is) := max_recurse_count is
| [] := 0

def has_call: program α → Prop
| ((instruction.call _ _):: is) := true
| ((@instruction.ite _ _ _ is')::is) := has_call is ∨ has_call is'
| (i::is) := has_call is
| [] := false

theorem has_call_of_step {t: thunk α} {p: program α} {m: memory α} {t': thunk α}:
  t.step = sum.inr (sum.inr (option.some p, m, t')) → t.current.has_call :=
begin
  cases t,
  cases t_current,
  { simp only [thunk.step, false_implies_iff] },
  cases t_current_hd;
  try { { simp only [thunk.step, false_implies_iff] } },
  simp only [has_call, implies_true_iff],
  simp only [thunk.step, prod.mk.inj_iff, false_and, false_implies_iff],
end

theorem has_call_of_step_over {t: thunk α} {t': thunk α}:
  t.step_over t' → t'.current.has_call → t.current.has_call :=
begin
  cases t,
  cases t_current,
  { simp only [thunk.step_over, thunk.step, false_implies_iff] },
  cases t_current_hd;
  try { { simp only [thunk.step_over, thunk.step, has_call],
    intro h,
    rw [← h],
    simpa only [has_call] using id } },
  { simp only [thunk.step_over, thunk.step, has_call],
    intro h,
    rw [← h],
    split_ifs,
    exact or.inr,
    exact or.inl },
  { simp only [has_call, implies_true_iff] },
  { simp only [thunk.step_over, thunk.step, has_call, and_imp],
    intros _ h,
    rw [h],
    simp [thunk.set_result, has_call] }
end

theorem max_recurse_count_step_inl {t t': thunk α}:
  t.step = sum.inl t' →  t'.current.max_recurse_count ≤ t.current.max_recurse_count :=
begin
  rcases t with ⟨p, is, inp⟩,
  cases is,
  { simp only [thunk.step, false_implies_iff] },
  cases is_hd;
  try { { simp only [thunk.step],
    intro h,
    simp only [← h, max_recurse_count] } };
  try { { simp only [thunk.step, false_implies_iff] } },
  simp only [thunk.step],
  by_cases is_hd_cond inp.getv;
  { simp only [h, if_true, if_false],
    intro ht,
    simp only [← ht, max_recurse_count, le_max_right, le_max_left] }
end

theorem max_recurse_count_step_inr_inr_none {t: thunk α} {m: memory α} {t': thunk α}:
  t.step = sum.inr (sum.inr (none, m, t')) →  t.current.max_recurse_count = t'.current.max_recurse_count + 1 :=
begin
  rcases t with ⟨p, is, inp⟩,
  cases is,
  { simp only [thunk.step, false_implies_iff] },
  cases is_hd;
  try { { simp only [thunk.step, prod.mk.inj_iff, false_and, false_implies_iff] } },
  simp only [thunk.step, prod.mk.inj_iff, max_recurse_count, and_imp],
  intros _ _ h,
  rw [← h]
end

theorem max_recurse_count_step_inr_inr_some {t: thunk α} {p: program α} {m: memory α} {t': thunk α}:
  t.step = sum.inr (sum.inr (some p, m, t')) →  t.current.max_recurse_count = t'.current.max_recurse_count :=
begin
  rcases t with ⟨p, is, inp⟩,
  cases is,
  { simp only [thunk.step, false_implies_iff] },
  cases is_hd;
  try { { simp only [thunk.step, prod.mk.inj_iff, false_and, false_implies_iff] } },
  simp only [thunk.step, prod.mk.inj_iff, max_recurse_count, and_imp],
  intros _ _ h,
  rw [← h]
end

theorem max_recurse_helper_zero {t: thunk α} {i c r: ℕ}:
  thunk.split_time_cost t i c r →
  max_recurse_count t.current = 0 →
  thunk.split_time_cost t i c 0 :=
begin
  induction i generalizing t c r,
  { exact flip absurd (thunk.not_split_time_cost_zero _ _ _) },
  intros h hrec,
  cases h,
  { exact or.inl h },
  rcases h with ⟨t', c₀, c₁, r₀, r₁, hex, hso, hsplit, hc, hr⟩, 
  refine or.inr ⟨t', c₀, c₁, 0, 0, _, hso, i_ih hsplit _, hc, (nat.add_zero _).symm⟩,
  { cases hstep:t.step,
    { simp only [thunk.external_time_cost_step, hstep] },
    cases val,
    { simpa only [thunk.step_over, hstep] using hso },
    rcases val with ⟨_|_,_,_⟩,
    { simpa only [max_recurse_count_step_inr_inr_none hstep, nat.succ_ne_zero] using hrec },
    { simpa only [thunk.external_time_cost_step, hstep] using hex } },
  { cases hstep:t.step,
    { apply nat.eq_zero_of_le_zero,
      rw [← hrec],
      apply max_recurse_count_step_inl,
      simpa only [sum.inl.inj_eq, thunk.step_over, hstep] using hso },
    cases val,
    { simpa only [thunk.step_over, hstep] using hso },
    rcases val with ⟨_|_,_,_⟩,
    { simpa only [max_recurse_count_step_inr_inr_none hstep, nat.succ_ne_zero] using hrec },
    rw [← hrec, max_recurse_count_step_inr_inr_some hstep],
    simp only [thunk.step_over, option.get_or_else, hstep] at hso,
    apply congr_arg,
    apply (thunk.set_result_current hso.right.symm).symm,
  }
end

theorem max_recurse_helper_zero' {t: thunk α} {i c r: ℕ}:
  thunk.split_time_cost t i c r →
  (∀ n t₁, thunk.step_over^~[n] t t₁ → ∀ m t₂, t₁.step ≠ sum.inr (sum.inr (none, m, t₂)))  →
  thunk.split_time_cost t i c 0 :=
begin
  induction i generalizing t c r,
  { exact flip absurd (thunk.not_split_time_cost_zero _ _ _) },
  intros h hrec,
  cases h,
  { exact or.inl h },
  rcases h with ⟨t', c₀, c₁, r₀, r₁, hex, hso, hsplit, hc, hr⟩, 
  refine or.inr ⟨t', c₀, c₁, 0, 0, _, hso, i_ih hsplit _, hc, (nat.add_zero _).symm⟩,
  { cases hstep:t.step,
    { simp only [thunk.external_time_cost_step, hstep] },
    cases val,
    { simpa only [thunk.step_over, hstep] using hso },
    rcases val with ⟨_|_,_,_⟩,
    { exact absurd hstep (hrec _ _ (rel_iterate_zero _ _) _ _) },
    { simpa only [thunk.external_time_cost_step, hstep] using hex } },
  { intros n t₁ ht m t₂ hstep,
    apply hrec (n+1) t₁ _ _ _ hstep,
    { rw [rel_iterate_succ_iff],
      exact ⟨_, hso, ht⟩ } }
end

theorem max_recurse_helper {t: thunk α} {i c r n: ℕ}:
  thunk.split_time_cost t i c r →
  (∀ arg, (∃ n t' t'', (thunk.step_over^~[n]) t t' ∧ t'.step = sum.inr (sum.inr (option.none, arg, t''))) → t.function.has_time_cost arg n) →
  thunk.split_time_cost t i c (max_recurse_count t.current * n) :=
begin
  induction i generalizing t c r,
  { simp only [thunk.split_time_cost, false_implies_iff] },
  intros h hrec,
  cases h,
  { exact or.inl h },
  rcases h with ⟨t', c₀, c₁, r₀, r₁, hex, hso, hsplit, hc, hr⟩,
  cases hstep:t.step,
  { apply thunk.split_cost_mono _ (le_refl _) (le_refl _) (nat.mul_le_mul_right _ (max_recurse_count_step_inl hstep)),
    refine or.inr ⟨t', c₀, c₁, 0, _, _, hso, i_ih hsplit _, hc, _⟩,
    { simp only [thunk.external_time_cost_step, hstep] },
    { simp only [exists_imp_distrib, and_imp],
      exact λ arg n x _ hx hxstep, (thunk.step_over_function hso) ▸ hrec _ ⟨n+1, _, _, ⟨t', hso, hx⟩, hxstep⟩ },
      simp only [thunk.step_over, hstep] at hso,
      simp only [hso, nat.zero_add] },
  cases val,
  { exact or.inl (thunk.step_return_nil hstep) },
  rcases val with ⟨_|_, _, _⟩,
  { refine or.inr ⟨t', c₀, c₁, n, max_recurse_count t'.current * n, _, hso, i_ih hsplit _, hc, _⟩,
    { simp only [thunk.external_time_cost_step, hstep, option.map_none', option.get_or_else_none],
      exact hrec _ ⟨0, _, _, rel_iterate_zero _ _, hstep⟩ },
    { simp only [exists_imp_distrib, and_imp],
      exact λ arg n x _ hx hxstep, (thunk.step_over_function hso) ▸ hrec _ ⟨n+1, _, _, ⟨t', hso, hx⟩, hxstep⟩ },
    simp only [thunk.step_over, hstep] at hso,
    rw [max_recurse_count_step_inr_inr_none hstep, thunk.set_result_current hso.right.symm],
    ring },
  { refine or.inr ⟨t', c₀, c₁, 0, _, _, hso, i_ih hsplit _, hc, _⟩,
    { simpa only [thunk.external_time_cost_step, hstep, option.map_some', option.get_or_else] using hex },
    { simp only [exists_imp_distrib, and_imp],
      exact λ arg n x _ hx hxstep, (thunk.step_over_function hso) ▸ hrec _ ⟨n+1, _, _, ⟨t', hso, hx⟩, hxstep⟩ },
    simp only [thunk.step_over, hstep] at hso,
    rw [max_recurse_count_step_inr_inr_some hstep, thunk.set_result_current hso.right.symm],
    exact (nat.zero_add _).symm }
end
  
theorem max_recurse_cost {p: program α} {inp: memory α} {n: ℕ}:
  p.halts_on inp → (∀ arg, p.recurse_arg inp arg → p.has_time_cost arg n) → recurse_cost p inp (max_recurse_count p * n) :=
begin
  intros halt hrec,
  rcases halt with ⟨n, m, h⟩,
  rcases thunk.split_cost_of_time_cost h with ⟨i, c, r, hn, h⟩,
  exact ⟨i, c, max_recurse_helper h hrec⟩,
end

theorem max_recurse_cost_zero' {p: program α} {inp: memory α}:
  p.halts_on inp → (∀ arg, ¬ p.recurse_arg inp arg) → p.recurse_cost inp 0 :=
begin
  intros halt hrec,
  rcases halt with ⟨n, m, h⟩,
  rcases thunk.split_cost_of_time_cost h with ⟨i, c, r, hn, h⟩,
  refine ⟨i, c, max_recurse_helper_zero' h (λ _ _ ht _ _ hstep, hrec _ ⟨_, _, _, ht, hstep⟩)⟩,
end

theorem max_recurse_cost_zero {p: program α} {inp: memory α}:
  p.halts_on inp → p.max_recurse_count = 0 → p.recurse_cost inp 0 :=
begin
  intros halt hrec,
  rcases halt with ⟨n, m, h⟩,
  rcases thunk.split_cost_of_time_cost h with ⟨i, c, r, hn, h⟩,
  exact ⟨i, c, max_recurse_helper_zero h hrec⟩,
end

theorem call_cost_zero_help {t: thunk α} {i c r: ℕ}:
  t.split_time_cost i c r → ¬ t.current.has_call → t.split_time_cost i 0 r :=
begin
  intros h hcall,
  induction i generalizing t c r,
  { simpa only [thunk.split_time_cost] using h },
  cases h,
  { exact or.inl h },
  rcases h with ⟨t', c₀, c₁, r₀, r₁, hex, hso, hsplit, hc, hr⟩,
  refine or.inr ⟨t', 0, 0, r₀, r₁, _, hso, i_ih hsplit _, (nat.add_zero _).symm, hr⟩,
  { cases hstep:t.step,
    { simp only [thunk.external_time_cost_step, hstep] },
    cases val,
    { simpa only [thunk.step_over, hstep] using hso },
    rcases val with ⟨_|_,_,_⟩,
    { simpa only [thunk.external_time_cost_step, hstep] using hex },
    { exact absurd (has_call_of_step hstep) hcall } },
  { contrapose! hcall,
    exact has_call_of_step_over hso hcall }
end

theorem call_cost_zero {p: program α} {inp: memory α}:
  p.halts_on inp → ¬ p.has_call → p.call_cost inp 0 :=
begin
  intros halt hcall,
  rcases halt with ⟨n, m, h⟩,
  rcases thunk.split_cost_of_time_cost h with ⟨i, c, r, hn, h⟩,
  exact ⟨i, r, call_cost_zero_help h hcall⟩
end

end program


end hmem