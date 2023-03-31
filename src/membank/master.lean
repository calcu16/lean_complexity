import data.pnat.basic
import data.vector.basic
import membank.basic
import tactic.linarith
import algebra.big_operators.fin
import data.nat.choose.central
import algebra.big_operators.fin
import algebra.char_zero
import tactic.field_simp
import tactic.linear_combination

namespace membank
universe u

variables {α: Type u} [has_zero α] [decidable_eq α]

def external_cost_le (p: program α): instruction α → bank α → ℕ → ℕ → Prop
| (instruction.call (f::fs) arg) m c r := program.cost_le (f::fs) (m.getm (arg.getv m)) c
| (instruction.recurse arg) m c r := program.cost_le p (m.getm (arg.getv m)) r
| _ _ _ _ := true

def internal_step: frame α → frame α → Prop
| ⟨_, [], m ⟩ f' := f' = ⟨[], [], m⟩
| ⟨p, i::is, m⟩ f' :=
  match i with
  | (instruction.call (f::fs) arg) := ∃ m', f' = ⟨p, is, m.setm 0 m'⟩ ∧ program.has_result (f::fs) (m.getm (arg.getv m)) m'
  | (instruction.recurse arg) := ∃ m', f' = ⟨p, is, m.setm 0 m'⟩ ∧ program.has_result p (m.getm (arg.getv m)) m'
  | _ := [f'] = stack.step_helper  [⟨p, i::is, m⟩]
  end

theorem internal_step_nil {f f': frame α}:
  f.current = [] → internal_step f f' → f' = ⟨[], [], f.register⟩ :=
begin
  cases f,
  intros h,
  cases h,
  unfold internal_step,
  exact id,
end

theorem internal_step_cons_current {f f': frame α}:
  f.current = [] → internal_step f f' → f'.current = [] :=
begin
  cases f,
  intros hf,
  cases hf,
  simpa [internal_step] using congr_arg frame.current,
end

theorem internal_step_cons_current' {f f': frame α}:
  f'.current ≠ [] → internal_step f f' → f.current ≠ [] :=
λ hf' hin hf, hf' (internal_step_cons_current hf hin)


theorem internal_step_cons_function {f f': frame α}:
  f'.current ≠ [] → internal_step f f' → f'.function = f.function :=
begin
  cases f,
  intros h,
  cases f_current,
  { unfold internal_step,
    intro h',
    rw [h'] at h,
    revert h,
    simp },
  { cases f_current_hd;
    try { cases f_current_hd_func };
    try { simpa [internal_step, stack.step_helper] using congr_arg frame.function },
    simp [internal_step, stack.step_helper],
    exact λ _ h _, congr_arg frame.function h,
    simp [internal_step, stack.step_helper],
    exact λ _ h _, congr_arg frame.function h }
end

def internal_step_at: ℕ → frame α → frame α → Prop
| 0 := eq
| (n+1) := λ f g, ∃ f', internal_step f f' ∧  internal_step_at n f' g

theorem internal_step_at_nil {m: bank α}:
  ∀ {n f}, internal_step_at n ⟨[], [], m⟩ f → f = ⟨[], [], m⟩ :=
begin
  intros n f,
  induction n generalizing f,
  { exact eq.symm },
  simp only [internal_step_at, exists_imp_distrib, and_imp],
  intros x hin,
  rw [internal_step_nil _ hin],
  apply n_ih,
  refl,
end

theorem internal_step_at_succ (n: ℕ) (f g: frame α):
  internal_step_at (n+1) f g ↔ ∃ f', internal_step f f' ∧ internal_step_at n f' g := by refl

theorem internal_step_at_succ' (n: ℕ) (f g: frame α):
  internal_step_at (n+1) f g ↔ ∃ f', internal_step f' g ∧ internal_step_at n f f' :=
begin
  induction n generalizing f g,
  { simp [internal_step_at] },
  conv {
    congr, rw [internal_step_at_succ],
    congr, funext, rw [n_ih],
    rw [← exists_and_distrib_left], skip,
    congr, funext, rw[internal_step_at_succ],
    rw [← exists_and_distrib_left] },
  rw [exists_comm],
  apply exists₂_congr,
  intros a b,
  rw [and.left_comm],
end


theorem internal_step_at_cons_current {n: ℕ} {f f': frame α}:
  f.current = [] → internal_step_at n f f' → f'.current = [] :=
begin
  cases f,
  intro hf,
  simp at hf,
  rw [hf],
  induction n generalizing f',
  { exact λ h, congr_arg frame.current h.symm },
  { rw [internal_step_at_succ', exists_imp_distrib],
    intros x hx,
    exact internal_step_cons_current (n_ih hx.right) hx.left }
end

theorem internal_step_at_cons_current' {n: ℕ} {f f': frame α}:
  f'.current ≠ [] → internal_step_at n f f' → f.current ≠ [] :=
λ hf' hin hf, hf' (internal_step_at_cons_current hf hin)

theorem internal_step_at_cons_function {n: ℕ} {f f': frame α}:
  f'.current ≠ [] → internal_step_at n f f' → f'.function = f.function :=
begin
  induction n generalizing f,
  exact λ _ h, congr_arg frame.function h.symm,
  simp only [internal_step_at, exists_imp_distrib, and_imp],
  intros hnil x hfx hxf',
  rw [n_ih hnil hxf'],
  exact internal_step_cons_function (internal_step_at_cons_current' hnil hxf') hfx,
end

theorem internal_step_unique {f g g': frame α}:
  internal_step f g → internal_step f g' → g = g' :=
begin
  cases f,
  cases f_current;
  try { cases f_current_hd };
  try { cases f_current_hd_func };
  unfold internal_step;
  intros h h';
  try { { rw [h, h'] } };
  try {
    rw ← list.singleton_inj,
    rw [h, h'] };
rcases h with ⟨_, h, hr⟩;
rcases h' with ⟨_, h', hr'⟩;
rw [h, h'];
apply congr_arg;
apply congr_arg;
apply program.has_result_unique hr hr',
end

theorem step_of_internal_step {p: program α} {i: instruction α} {is: list (instruction α)} {m: bank α} {c r: ℕ} (hp: p ≠ []):
  external_cost_le p i m c r → ∃ n ≤ (1 + c + r), ∀ f pf, internal_step ⟨p, i::is, m⟩ f → (stack.step^[n]) ⟨[⟨p, i::is, m⟩], by simpa [stack.well_formed] using hp⟩ = ⟨[f], pf⟩ :=
begin
  cases i;
  try { cases i_func };
  try { {
    intro,
    refine ⟨1, by linarith, λ f pf, _⟩,
    { rw [function.iterate_one],
      unfold internal_step stack.step,
      simpa using eq.symm } } },
  { simp only [external_cost_le, program.cost_le, program.costed_result, exists_imp_distrib, internal_step, and_imp],
    intros x hx,
    rcases stack.step_return _ hx ⟨⟨_, _, _⟩, hp⟩ with ⟨m, hm, pf, h⟩,
    refine ⟨1 + m, by linarith, λ f' pf' y hf' h', _⟩,
    rw [eq_comm] at hf',
    induction hf',
    rw [add_comm 1, ← nat.succ_eq_add_one, function.iterate_succ_apply, stack.step_call, h],
    cases h' with m' hm',
    unfold program.costed_result at hm',
    simp [frame.setm, bank.setm_setm_self, stack.step_halt_unique hx hm'],
    exact list.cons_ne_nil _ _,
    simp [program.apply, stack.result] },
  { simp only [external_cost_le, program.cost_le, program.costed_result, exists_imp_distrib, internal_step, and_imp],
    intros x hx,
    rcases stack.step_return _ hx ⟨⟨_, _, _⟩, hp⟩ with ⟨m, hm, pf, h⟩,
    refine ⟨1 + m, by linarith, λ f' pf' y hf' h', _⟩,
    rw [eq_comm] at hf',
    induction hf',
    rw [add_comm 1, ← nat.succ_eq_add_one, function.iterate_succ_apply, stack.step_recurse, h],
    cases h' with m' hm',
    unfold program.costed_result at hm',
    simp [frame.setm, bank.setm_setm_self, stack.step_halt_unique hx hm'],
    simp [program.apply, stack.result, hp], },
end

theorem external_cost_of_internal_step {p: program α} {i: instruction α} {is: list (instruction α)} {m: bank α} {f: frame α}:
  internal_step ⟨p, i::is, m⟩ f → ∃ c r, external_cost_le p i m c r :=
begin
  cases i;
  try { cases i_func };
  try { exact λ _, ⟨0, 0, by unfold external_cost_le⟩ },
  { unfold internal_step external_cost_le program.has_result program.cost_le,
    intro h,
    rcases h with ⟨m', hf, n, h⟩,
    refine ⟨n, 0, m', h⟩ },
  { unfold internal_step external_cost_le program.has_result program.cost_le,
    intro h,
    rcases h with ⟨m', hf, n, h⟩,
    refine ⟨0, n, m', h⟩ },
end

theorem internal_step_has_result {f g: frame α} {m: bank α} (hf: f.function ≠ []):
   internal_step f g → (∃ n pf, stack.step^[n] ⟨[g], pf⟩ = stack.result m) → (∃ n pf, stack.step^[n] ⟨[f], pf⟩= stack.result m) :=
begin
  intros hstep hg,
  rcases hg with ⟨n, gpf, hg⟩,
  cases f,
  cases f_function,
  { contradiction },
  cases f_current,
  { unfold internal_step at hstep,
    refine ⟨1, by simp [stack.well_formed], _⟩,
    rw [function.iterate_one, stack.step_halt'', ← hg],
    simp only [hstep, ← stack.result_def', stack.step_halt] },
  rcases (external_cost_of_internal_step hstep) with ⟨c, r, hcost⟩,
  rcases (step_of_internal_step (list.cons_ne_nil _ _) hcost) with ⟨n', _, hn'⟩,
  exact ⟨n' + n, by simp[stack.well_formed], stack.step_trans n' n ( hn' _ _ hstep) hg rfl⟩,
end

theorem internal_step_has_result' {p: instruction α} {ps is is': program α} {m m' mr: bank α}:
  internal_step ⟨p :: ps, is, m⟩ ⟨p :: ps, is', m'⟩ →
  (∃ n, stack.step^[n] ⟨[⟨p :: ps, is', m'⟩], by simp[stack.well_formed]⟩ = stack.result mr) →
  (∃ n, stack.step^[n] ⟨[⟨p :: ps, is, m⟩], by simp[stack.well_formed]⟩ = stack.result mr) :=
begin
  intros hstep h,
  rcases h with ⟨n, h⟩,
  rcases internal_step_has_result _ hstep ⟨n, by simp[stack.well_formed], h⟩ with ⟨n', _, h'⟩,
  exact ⟨n', h'⟩,
  exact list.cons_ne_nil _ _,
end

theorem internal_step_has_result'' {p: program α} {i: instruction α} {is is': program α} {m m' mr: bank α} (hp: p ≠ []):
  internal_step ⟨p, i::is, m⟩ ⟨p, is', m'⟩ →
  (∃ n, stack.step^[n] ⟨[⟨p, is', m'⟩], by simp[hp, stack.well_formed]⟩ = stack.result mr) →
  (∃ n, stack.step^[n] ⟨[⟨p, i::is, m⟩], by simp[hp, stack.well_formed]⟩ = stack.result mr) :=
begin
  intros hstep h,
  rcases h with ⟨n, h⟩,
  rcases internal_step_has_result _ hstep ⟨n, by simp[hp, stack.well_formed], h⟩ with ⟨n', _, h'⟩,
  exact ⟨n', h'⟩,
  exact hp,
end


def split_cost_le: ℕ → ℕ → ℕ → frame α → Prop
| (n+1) _ _ ⟨_, [], _⟩ := true
| (n+1) c r ⟨p, i::is, m⟩ :=
  ∃ is' m' c₀ r₀ c₁ r₁, external_cost_le p i m c₀ r₀
    ∧ internal_step ⟨p, i::is, m⟩ ⟨p, is', m'⟩
    ∧ split_cost_le n c₁ r₁ ⟨p, is', m'⟩
    ∧ c = c₀ + c₁
    ∧ r = r₀ + r₁
| 0 _ _ ⟨[], [], _⟩ := true
| _ _ _ _ := false

theorem split_cost_instruction_pos (c r: ℕ) (p: list (instruction α)) (i: instruction α) (is: list (instruction α)) (m: bank α):
  ¬ split_cost_le 0 c r ⟨p, i::is, m⟩ :=
by cases p; exact not_false

theorem split_cost_le_mono {i c r i' c' r': ℕ} {f: frame α}:
  split_cost_le i c r f → i ≤ i' →  c ≤ c' → r ≤ r' → split_cost_le i' c' r' f :=
begin
  intros h hi hc hr,
  cases f with p is m,
  induction i' with i' ih generalizing i c r c' r' p is m,
  { rw [nonpos_iff_eq_zero] at hi,
    rw [hi] at h,
    revert h,
    cases p;
    cases is;
    exact id },
  { cases is,
    { cases p; trivial },
    cases i,
    { revert h,
      cases p;
      exact false.rec_on _ },
    rcases h with ⟨is', m', c₀, r₀, c₁, r₁, hex, hin, h, hc', hr'⟩,
    refine ⟨is', m', c₀, r₀, c' - c₀, r' - r₀, hex, hin, _, _⟩,
    refine ih p _ _ (nat.succ_le_succ_iff.mp hi) _ _ h,
    { exact le_tsub_of_add_le_left (hc' ▸ hc) },
    { exact le_tsub_of_add_le_left (hr' ▸ hr) },
    rw [nat.add_comm, nat.sub_add_cancel, nat.add_comm, nat.sub_add_cancel],
    exact ⟨ rfl, rfl ⟩,
    exact flip trans hr (hr'.symm ▸ le_self_add),
    exact flip trans hc (hc'.symm ▸ le_self_add) }
end

def internal_cost_le (f: frame α) (i: ℕ) := ∃ c r, split_cost_le i c r f

def call_cost_le (f: frame α) (c: ℕ) := ∃ i r, split_cost_le i c r f

def recursive_cost_le (f: frame α) (r: ℕ) := ∃ i c, split_cost_le i c r f

theorem split_cost_of_components {f: frame α} {i c r: ℕ}
  (hi: internal_cost_le f i) (hc: call_cost_le f c) (hr: recursive_cost_le f r):
   split_cost_le i c r f :=
begin
  induction i generalizing f c r,
  { cases f,
    cases f_current;
    cases f_function;
    revert hi;
    simp [internal_cost_le, split_cost_le] },
  { cases f,
    rcases hi with ⟨ic, ir, hi⟩,
    rcases hc with ⟨ci, cr, hc⟩,
    rcases hr with ⟨ri, rc, hr⟩,
    cases f_current,
    { trivial },
    cases ci,
    { exact absurd hc (split_cost_instruction_pos _ _ _ _ _ _) },
    cases ri,
    { exact absurd hr (split_cost_instruction_pos _ _ _ _ _ _) },
    unfold split_cost_le at *,
    rcases hi with ⟨iis, im, ic₀, ir₀, ic₁, ir₁, iex, iin, hi, hic, hir⟩,
    rcases hc with ⟨cis, cm, cc₀, cr₀, cc₁, cr₁, cex, cin, hc, hcc, hcr⟩,
    rcases hr with ⟨ris, rm, rc₀, rr₀, rc₁, rr₁, rex, rin, hr, hrc, hrr⟩,
    refine ⟨iis, im, cc₀, rr₀, cc₁, rr₁, _, _, _ , hcc, hrr⟩,
    { cases f_current_hd;
      try { cases f_current_hd_func };
      unfold external_cost_le,
      { unfold external_cost_le at cex,
        exact cex },
      { unfold external_cost_le at rex,
        exact rex } },
    { exact iin },
    { apply i_ih ⟨_, _, hi⟩,
      { rw [internal_step_unique iin cin],
        exact ⟨_, _, hc⟩ },
      { rw [internal_step_unique iin rin],
        exact ⟨_, _, hr⟩ } } }
end
  

theorem cost_of_split_cost_helper {p: program α} {is: program α} {inp: bank α} {i c r: ℕ} (hp: p ≠ []):
  split_cost_le i c r ⟨p, is, inp⟩ → ∃ m, (stack.step^[(i + c + r)]) ⟨[⟨p, is, inp⟩], by simp[stack.well_formed, hp]⟩ = stack.result m :=
begin
  cases p,
  { contradiction },
  induction hn:(i+c+r) using nat.strong_induction_on with n ih generalizing i c r is inp,
  cases i,
  { simp only [nat.nat_zero_eq_zero, add_eq_zero_iff] at hn,
    cases is;
    { simp [split_cost_le, hn] } },
  { cases is,
    { simp [← hn, nat.succ_add, stack.step_halt'', stack.step_halt] },
    intro h,
    rcases h with ⟨is', m', c₀, r₀, c₁, r₁, hex, hin, h, hc', hr'⟩,
    rw [← hn],
    simp only [nat.succ_add] at hn,
    cases ih _ _ rfl h with m ih,
    { refine ⟨m, _⟩,
      rcases step_of_internal_step _ hex with ⟨m', hm', h'⟩,
      specialize h' _ _ hin,
      { simp [stack.well_formed] },
      apply stack.step_halt_le,
      apply stack.step_trans m' _ h' ih rfl,
      exact list.cons_ne_nil _ _,
      rw [hc', hr', nat.succ_eq_add_one],
      linarith,
    },
    { apply nat.lt_of_succ_le,
      rw [← hn, hc', hr'],
      rw [nat.succ_le_succ_iff],
      apply add_le_add,
      apply add_le_add (le_refl _),
      apply le_add_self,
      apply_instance,
      apply_instance,
      apply le_add_self },
  }
end

theorem cost_of_split_cost {p: program α} {inp: bank α} {i c r: ℕ} (hp: p ≠ []):
  split_cost_le i c r ⟨p, p, inp⟩ → p.cost_le inp (i+c+r) :=
begin
  unfold program.cost_le program.costed_result program.apply,
  exact cost_of_split_cost_helper hp,
end

def internal_cost_bound: program α → ℕ
| [] := 1
| ((@instruction.ite _ cond _ is')::is) := max (internal_cost_bound is') (internal_cost_bound is) + 1
| (i::is) := internal_cost_bound is + 1

theorem internal_cost_bound_le {p: program α} {is: program α} {inp: bank α} {i c r: ℕ}:
  split_cost_le i c r ⟨p, is, inp⟩ → split_cost_le (internal_cost_bound is) c r ⟨p, is, inp⟩ :=
begin
  induction h:(internal_cost_bound is) using nat.strong_induction_on with n ih generalizing is inp i c r,
  cases is,
  { unfold internal_cost_bound at h,
    rw ← h,
    simp [internal_cost_le, split_cost_le] },
  cases i,
  { simp [internal_cost_le, split_cost_instruction_pos] },
  cases is_hd;
  try { cases is_hd_func };
  try { unfold internal_cost_bound at h,
    rw ← h,
    refine Exists₃.imp (λ is m c₀, _),
    refine Exists₃.imp (λ r₀ c₁ r₁, _),
    simp only [and_imp],
    refine λ hex hin hs hc hr, ⟨hex, hin, _, hc, hr⟩,
    simp only [internal_step, stack.step_helper, frame.mk.inj_eq, and.assoc, eq_self_iff_true, true_and] at hin,
    rw [← hin.left],
    rw [← hin.left] at h,
    apply ih _ (nat.lt_of_succ_le (nat.le_of_eq h)) rfl hs };
  try { unfold internal_cost_bound at h,
    rw ← h,
    refine Exists₃.imp (λ is m c₀, _),
    refine Exists₃.imp (λ r₀ c₁ r₁, _),
    simp only [and_imp],
    refine λ hex hin hs hc hr, ⟨hex, hin, _, hc, hr⟩,
    simp only [internal_step, stack.step_helper, frame.mk.inj_eq, and.assoc, eq_self_iff_true, true_and] at hin,
    cases hin with m hin,
    rw [← hin.left],
    rw [← hin.left] at h,
    apply ih _ (nat.lt_of_succ_le (nat.le_of_eq h)) rfl hs },
  { unfold internal_cost_bound at h,
    by_cases hcond:(is_hd_cond inp.getv);
    { rw ← h,
      refine Exists₃.imp (λ is m c₀, _),
      refine Exists₃.imp (λ r₀ c₁ r₁, _),
      simp only [and_imp],
      refine λ hex hin hs hc hr, ⟨hex, hin, _, hc, hr⟩,
      simp only [internal_step, stack.step_helper, frame.mk.inj_eq, and.assoc, eq_self_iff_true, true_and, hcond,
        ite_eq_iff, not_true, not_false_iff, and_true, false_and, or_false, false_or, @eq_comm _ is] at hin,
      rw [hin.left],
      rw [hin.left] at h,
      apply split_cost_le_mono,
      apply ih _ _ rfl hs,
      rw [← h],
      apply nat.lt_succ_of_le,
      try { exact le_max_left _ _},
      try { exact le_max_right _ _},
      try { exact le_max_left _ _},
      try { exact le_max_right _ _},
      exact le_refl _,
      exact le_refl _ } },
end

theorem internal_cost_bound_le' {p: program α} {is: program α} {inp: bank α} {i: ℕ}:
  internal_cost_le ⟨p, is, inp⟩  i → internal_cost_le ⟨p, is, inp⟩ (internal_cost_bound is) :=
Exists₂.imp (λ c r, internal_cost_bound_le)

def recurse_arg' (f: frame α) (m: bank α): Prop :=
  ∃ n p is arg m', internal_step_at n f ⟨p, (instruction.recurse arg)::is, m'⟩ ∧ m = m'.getm (arg.getv m')

theorem recurse_arg_zero (p:program α) (arg: source α) (is:program α) (m: bank α):
  recurse_arg' ⟨p, (instruction.recurse arg)::is, m⟩ (m.getm (arg.getv m)) :=
   ⟨0, p, is, arg, m, by unfold internal_step_at, rfl ⟩

theorem recurse_cost_zero {f: frame α}:
  (∀ m, ¬ recurse_arg' f m) → ∀ {i c r}, split_cost_le i c r f → split_cost_le i c 0 f :=
begin
  intros h i c r,
  induction i generalizing c r f,
  { cases f,
    cases f_function,
    cases f_current,
    exact id,
    exact false.rec_on _,
    exact false.rec_on _ },
  cases f,
  cases f_current,
  { cases f_function; exact id },
  intro hsplit,
  rcases hsplit with ⟨p, m, c₀, r₀, c₁, r₁, hex, hin, hsplit, hc, hr⟩,
  refine ⟨p, m, c₀, 0, c₁, 0, _, hin, _, hc, (zero_add _).symm⟩,
  { cases f_current_hd;
    try { cases f_current_hd_func };
    try { unfold external_cost_le },
    { revert hex,
      unfold external_cost_le,
      exact id },
    { exfalso,
      apply (h _) ⟨0, _, _, _, _, rfl, rfl⟩ } },
  { apply i_ih,
    { contrapose! h,
      rcases h with ⟨m', n, p', is', arg, m'', hstep, hm⟩,
      exact ⟨m', n+1, p', is', arg, m'', ⟨_, hin, hstep⟩, hm⟩,
    },
    exact hsplit }
end  

def recurse_arg (p: program α) (inp arg: bank α) := recurse_arg' ⟨p, p, inp⟩ arg
  
def recurse_count: program α → ℕ
| [] := 0
| ((instruction.recurse arg)::is) := 1 + recurse_count is
| ((@instruction.ite _ cond _ is')::is) := max (recurse_count is) (recurse_count is')
| (_::is) := recurse_count is

theorem recurse_count_mono {f f': frame α}:
  internal_step f f' → recurse_count f'.current ≤ recurse_count f.current :=
begin
  cases f,
  cases f_current,
  { exact λ h, h.symm ▸ le_refl _ },
  cases f_current_hd;
  try { cases f_current_hd_func };
  try { simp only [list.cons.inj_eq, internal_step, stack.step_helper, eq_self_iff_true, and_true, recurse_count],
    intro h,
    rw [h] },
  { cases @ite_eq_or_eq _  (f_current_hd_cond f_register.getv) f_current_hd__inst_1 f_current_hd_branch f_current_tl,
    simpa only [h_1, frame.current] using le_max_right _ _,
    simpa only [h_1, frame.current] using le_max_left _ _ },
  { simp only [list.cons.inj_eq, internal_step, stack.step_helper, eq_self_iff_true, and_true, recurse_count, exists_imp_distrib, and_imp],
    intros _ h _,
    rw [h] },
  { simp only [list.cons.inj_eq, internal_step, stack.step_helper, eq_self_iff_true, and_true, recurse_count, exists_imp_distrib, and_imp],
    intros _ h _,
    rw [h],
    exact le_add_self },
end

theorem recurse_count_zero_step {is: program α}:
  recurse_count is = 0 → ∀ {n f f'}, internal_step_at n f f' → f.current = is → ∀ is' arg m, f' ≠ ⟨ f.function, (instruction.recurse arg)::is', m⟩ :=
begin
  intros h n,
  induction n generalizing is,
  { intros f f' hin hc is' arg m hf,
    unfold internal_step_at at hin,
    revert h,
    rw [← hc, hin, hf],
    simp [recurse_count] },
  intros f f' hin hc is' arg m hf,
  unfold internal_step_at at hin,
  rcases hin with ⟨f'', hin, hin'⟩,
  rw [hf] at hin',
  cases is,
  { rw [internal_step_nil hc hin] at hin',
    have g := internal_step_at_nil hin',
    revert g,
    simp },
  { have g := flip internal_step_at_cons_function hin' (list.cons_ne_nil _ _),
    unfold frame.function at g,
    rw [g] at hin',
    apply n_ih _ hin' rfl _ _ _ rfl,
    apply nat.eq_zero_of_le_zero,
    rw [← h, ← hc],
    apply recurse_count_mono hin,
  },
end

theorem recurse_count_zero_arg' {is: program α}:
  recurse_count is = 0 → ∀ p m m', ¬ recurse_arg' ⟨p, is, m⟩ m' :=
begin
  intros h p m mx,
  unfold recurse_arg',
  simp only [not_exists, not_and],
  intros n p' is' arg m' hin meq,
  apply recurse_count_zero_step h,
  apply hin,
  refl,
  rw [← internal_step_at_cons_function _ hin],
  exact list.cons_ne_nil _ _,
end

theorem recurse_cost_bound_le {p: program α} {is: program α} {inp: bank α} {i c r: ℕ}
{rn: ℕ} (hr: ∀ arg, recurse_arg' ⟨p, is, inp⟩ arg → program.cost_le p arg rn):
  split_cost_le i c r ⟨p, is, inp⟩ → split_cost_le i c (rn * recurse_count is) ⟨p, is, inp⟩ :=
begin
  induction i generalizing is inp c r,
  { cases is;
    cases p,
    { exact id },
    all_goals { exact false.rec_on _ } },
  { cases is,
    { exact id },
    simp only [split_cost_le, exists_imp_distrib, and_imp],
    intros is' m c₀ r₀ c₁ r₁ hex hin hsplit hc hr,
    cases is_hd;
    try { cases is_hd_func };
    try { refine ⟨is', m, _, 0, _, _, _, hin, _, hc, (nat.zero_add _).symm ⟩,
      unfold external_cost_le,
      unfold recurse_count,
      simp only [internal_step, stack.step_helper, frame.mk.inj_eq, and.assoc, eq_self_iff_true, true_and,
        ite_eq_iff, not_true, not_false_iff, and_true, false_and, or_false, false_or] at hin,
      rw [hin.left],
      apply i_ih,
      { intros arg harg,
        apply hr,
        rcases harg with ⟨n, p, is, arg, m, hstep, heq⟩,
        refine ⟨n+1, p, is, arg, _, ⟨_, _, hstep⟩, heq⟩,
        unfold internal_step stack.step_helper,
        rw [hin.right] },
      rw [hin.left] at hsplit,
      apply hsplit },
    { refine ⟨is', m, _, 0, _, _, _, hin, _, hc, (nat.zero_add _).symm ⟩,
      { unfold external_cost_le },
      unfold recurse_count,
      by_cases hcond: (is_hd_cond inp.getv),
      { simp only [internal_step, stack.step_helper, frame.mk.inj_eq, and.assoc, eq_self_iff_true, true_and,
          if_pos trivial, not_true, not_false_iff, and_true, false_and, or_false, false_or, hcond] at hin,
        
        rw [hin.left],
        apply split_cost_le_mono _ (le_refl _) (le_refl _) (nat.mul_le_mul_left _ (le_max_right _ _)),
        apply i_ih,
        { intros arg harg,
          apply hr,
          rcases harg with ⟨n, p, is, arg, m, hstep, heq⟩,
          refine ⟨n+1, p, is, arg, _, ⟨_, _, hstep⟩, heq⟩,
          unfold internal_step stack.step_helper,
          simp [hin.right, hcond, if_pos trivial] },
        rw [hin.left] at hsplit,
        apply hsplit },
      { simp only [internal_step, stack.step_helper, frame.mk.inj_eq, and.assoc, eq_self_iff_true, true_and,
          if_neg _, not_true, not_false_iff, and_true, false_and, or_false, false_or, hcond] at hin,
        rw [hin.left],
        apply split_cost_le_mono _ (le_refl _) (le_refl _) (nat.mul_le_mul_left _ (le_max_left _ _)),
        apply i_ih,
        { intros arg harg,
          apply hr,
          rcases harg with ⟨n, p, is, arg, m, hstep, heq⟩,
          refine ⟨n+1, p, is, arg, _, ⟨_, _, hstep⟩, heq⟩,
          unfold internal_step stack.step_helper,
          simp [hin.right, hcond, if_pos trivial] },
        rw [hin.left] at hsplit,
        apply hsplit } },
    { refine ⟨is', m, _, 0, _, _, _, hin, _, hc, (nat.zero_add _).symm ⟩,
      { unfold external_cost_le,
        unfold external_cost_le at hex,
        exact hex,
      },
      unfold recurse_count,
      simp only [internal_step, stack.step_helper, frame.mk.inj_eq, and.assoc, eq_self_iff_true, true_and,
        ite_eq_iff, not_true, not_false_iff, and_true, false_and, or_false, false_or] at hin,
      cases hin with m hin,
      rw [hin.left],
      apply i_ih,
      { intros arg harg,
        apply hr,
        rcases harg with ⟨n, p, is, arg, m, hstep, heq⟩,
        refine ⟨n+1, p, is, arg, _, ⟨_, _, hstep⟩, heq⟩,
        unfold internal_step stack.step_helper,
        rw [hin.right.left],
        refine ⟨_, rfl, hin.right.right⟩, },
      rw [hin.left] at hsplit,
      apply hsplit },
    { refine ⟨is', m, _, rn, _, _, hr _ ⟨0, _, _, _, _, rfl, rfl⟩, hin, _, hc, by unfold recurse_count; rw [mul_add, mul_one] ⟩,
      simp only [internal_step, stack.step_helper, frame.mk.inj_eq, and.assoc, eq_self_iff_true, true_and,
        ite_eq_iff, not_true, not_false_iff, and_true, false_and, or_false, false_or] at hin,
      cases hin with m hin,
      rw [hin.left],
      apply i_ih,
      { intros arg harg,
        apply hr,
        rcases harg with ⟨n, p, is, arg, m, hstep, heq⟩,
        refine ⟨n+1, p, is, arg, _, ⟨_, _, hstep⟩, heq⟩,
        unfold internal_step stack.step_helper,
        rw [hin.right.left],
        refine ⟨_, rfl, hin.right.right⟩, },
      rw [hin.left] at hsplit,
      apply hsplit },

    }
end

def divide_and_conquer_cost (p: program α) (fc: ℕ → ℕ): ℕ → ℕ
| 0 := internal_cost_bound p + fc 0
| (n+1) := internal_cost_bound p + fc (n + 1) + divide_and_conquer_cost n * recurse_count p

theorem divide_and_conquer_cost_def {p: program α} {fc: ℕ → ℕ} {n: ℕ}:
  divide_and_conquer_cost p fc n = internal_cost_bound p + fc n + ite (n = 0) 0 (divide_and_conquer_cost p fc (n - 1) * recurse_count p) :=
by cases n; simp [divide_and_conquer_cost]

theorem divide_and_conquer_cost_pos (fc: ℕ → ℕ) (n: ℕ):
  1 ≤ divide_and_conquer_cost ([]:program α) fc n :=
begin
  cases n;
  unfold divide_and_conquer_cost internal_cost_bound,
  exact le_self_add,
  rw add_assoc,
  exact le_self_add,
end

theorem divide_and_conquer_cost_mono {p: program α} {fc: ℕ → ℕ} {m n: ℕ}:
  0 < recurse_count p → m ≤ n → divide_and_conquer_cost p fc m ≤ divide_and_conquer_cost p fc n :=
begin
  intros hr hmn,
  induction n,
  { rw [nat.eq_zero_of_le_zero hmn] },
  cases eq_or_lt_of_le hmn,
  { rw [h] },
  exact trans (n_ih (nat.le_of_lt_succ h)) (le_add_left (nat.le_mul_of_pos_right hr)),
end

theorem divide_and_conquer_cost_sound {p: program α}
  (fr: bank α → ℕ → Prop) (hfr: ∀ inp n arg, recurse_arg p inp arg → fr inp n → ∃ m < n, fr arg m)
  {fc: ℕ → ℕ} (hfc: ∀ inp n, fr inp n → call_cost_le ⟨p, p, inp⟩ (fc n)):
  ∀ inp n, fr inp n → p.cost_le inp (divide_and_conquer_cost p fc n) :=
begin
  cases p,
  { exact λ _ _ _, program.cost_le_mono (divide_and_conquer_cost_pos _ _) ⟨_, rfl⟩ },
  intros inp n hn,
  induction n using nat.strong_induction_on with n ih generalizing inp,
  cases n,
  { unfold divide_and_conquer_cost,
    rw [← nat.add_zero (_ + fc 0)],
    apply cost_of_split_cost (list.cons_ne_nil _ _),
    specialize hfc inp _ hn,
    rcases hfc with ⟨i, r, hfc⟩,
    apply recurse_cost_zero _ (internal_cost_bound_le hfc),
    { intro m,
      specialize hfr inp 0 m,
      simp only [hn, nat.not_lt_zero, imp_false, exists_prop, false_and, exists_false, not_true] at hfr,
      exact hfr } },
  unfold divide_and_conquer_cost,
  apply cost_of_split_cost (list.cons_ne_nil _ _),
  rcases hfc _ _ hn with ⟨i, r, hfc⟩,
  cases hpos:(recurse_count (p_hd::p_tl)),
  { rw [mul_zero],
    apply recurse_cost_zero,
    apply recurse_count_zero_arg' hpos,
    apply internal_cost_bound_le,
    apply recurse_cost_zero,
    apply recurse_count_zero_arg' hpos,
    apply hfc },
  rw [← hpos],
  have g := nat.zero_lt_succ n_1,
    rw [← hpos] at g,
  apply recurse_cost_bound_le _ (internal_cost_bound_le hfc),
  intros arg harg,
  rcases hfr inp _ arg harg hn with ⟨m, hm, hfr⟩,
  apply program.cost_le_mono,
  exact divide_and_conquer_cost_mono g (nat.le_of_lt_succ hm),
  exact ih _ hm _ hfr,
end

-- master theorem
-- S(m) ≤ Σ₀ᵐ a^i * f(m - i)
-- f(m) ≤ Θ(a^(m-ε)) → S(m) ≤ Θ(a^m)
-- f(m) ≈ Θ(a^m) → S(m) = Θ(m * f(m))
--  this might be limited to f(m) = Θ(m^k a^m) → S(m) = Θ(m^(k+1) * a^m)
-- f(m) ≥ Θ(a^(m+ε)) → S(m) ≤ Θ(f(m)) -- regularity constraint?


end membank