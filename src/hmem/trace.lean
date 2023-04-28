import hmem.memory
import hmem.split_cost
import hmem.stack

universe u
variables {α: Type u} [has_zero α] [decidable_eq α]

namespace hmem

structure trace (α: Type*) [has_zero α] [decidable_eq α] :=
  (result: memory α)
  (branch: list bool)
  (steps: ℕ)
  (calls: list (memory α))
  (recurses: list (memory α))

def program.calls_on_branch {α: Type*} [has_zero α] [decidable_eq α]:
  program α → list bool → list (program α)
| [] _ := []
| (@instruction.ite _ _ _ _ _ is'::is) (tt::br) := program.calls_on_branch is' br
| (@instruction.ite _ _ _ _ _ _::is) (ff::br) := program.calls_on_branch is br
| (instruction.call func _ _::is) br := func :: program.calls_on_branch is br
| (i::is) br := program.calls_on_branch is br

def trace.prog_calls (t: trace α) (p: program α): list (program α × memory α) :=
  list.zip (p.calls_on_branch t.branch) t.calls

def trace.has_call_cost (t: trace α) (p: program α) (c: ℕ): Prop :=
  (t.prog_calls p).sum_le (λ pm, pm.fst.has_time_cost pm.snd) c
  
def trace.has_recurse_cost (t: trace α) (p: program α) (r: ℕ): Prop :=
  t.recurses.sum_le (λ m, p.has_time_cost m) r

def thunk.extend_branch (tr: thunk α) (br: list bool): list bool :=
  match tr.takes_branch with
  | (some b) := b::br
  | none := br
  end

def thunk.extend_trace (t: thunk α): trace α → trace α
| ⟨m, br, i, cs, rs⟩ := match t.step with
  | (sum.inr (sum.inr (option.some p, m', _))) := ⟨m, br, i + 1, m'::cs, rs⟩
  | (sum.inr (sum.inr (option.none, m', _))) := ⟨m, br, i + 1, cs, m'::rs⟩
  | _ := ⟨m, t.extend_branch br, i + 1, cs, rs⟩
end

def thunk.extend_trace₀ {t t': thunk α} {tr: trace α} {m: memory α} {br: list bool} {n: ℕ} {cs: list (memory α)} {rs: list (memory α)}:
  t.step = sum.inl t' → tr = ⟨m, br, n, cs, rs⟩ → t.takes_branch = none → t.extend_trace tr = ⟨m, br, n+1, cs, rs⟩ :=
begin
  intros hstep heq,
  simp only [heq, thunk.extend_trace, thunk.extend_branch, hstep, eq_self_iff_true, and_true, true_and],
  intro h,
  rw [h],
  trivial,
end


def thunk.extend_trace_if {t t': thunk α} {tr: trace α} {m: memory α} {b: bool} {br: list bool} {n: ℕ} {cs: list (memory α)} {rs: list (memory α)}:
  t.step = sum.inl t' → tr = ⟨m, br, n, cs, rs⟩ → t.takes_branch = some b → t.extend_trace tr = ⟨m, b::br, n+1, cs, rs⟩ :=
begin
  intros hstep heq,
  simp only [heq, thunk.extend_trace, thunk.extend_branch, hstep, eq_self_iff_true, and_true, true_and],
  intro h,
  rw [h],
  trivial,
end

theorem thunk.extend_trace_result (t : thunk α) (tr: trace α):
  (t.extend_trace tr).result = tr.result :=
begin
  cases tr,
  unfold thunk.extend_trace,
  cases t.step,
  { refl },
  cases val,
  { refl },
  rcases val with ⟨_|_, _, _⟩;
  refl,
end

theorem thunk.extend_trace_steps (t : thunk α) (tr: trace α):
  (t.extend_trace tr).steps = tr.steps + 1 :=
begin
  cases tr,
  unfold thunk.extend_trace,
  cases t.step,
  { refl },
  cases val,
  { refl },
  rcases val with ⟨_|_, _, _⟩;
  refl,
end

theorem thunk.extend_trace_calls_cons {t: thunk α} {tr: trace α} {p: program α} {t': thunk α × list α} {m: memory α}:
  t.step = sum.inr (sum.inr (some p, m, t')) → (t.extend_trace tr).calls = m::tr.calls :=
begin
  cases tr,
  intro hstep,
  simp only [thunk.extend_trace, hstep, eq_self_iff_true, and_true],
end

theorem thunk.extend_trace_calls_eq {t: thunk α} {tr: trace α}:
  (∀ {p m t'}, t.step ≠ sum.inr (sum.inr (some p, m, t'))) → (t.extend_trace tr).calls = tr.calls :=
begin
  cases tr,
  cases hstep: t.step,
  { simp only [thunk.extend_trace, hstep, eq_self_iff_true, imp_true_iff] },
  cases val,
  { simp only [thunk.extend_trace, hstep, eq_self_iff_true, imp_true_iff] },
  rcases val with ⟨_|_,_,_,_⟩,
  { simp only [thunk.extend_trace, hstep, eq_self_iff_true, imp_true_iff] },
  contrapose!,
  simp,
end

theorem thunk.extend_trace_calls_eq₀ {t: thunk α} {tr: trace α} {t': thunk α}:
  t.step = sum.inl t' → (t.extend_trace tr).calls = tr.calls :=
begin
  intro hstep,
  apply thunk.extend_trace_calls_eq,
  simp [hstep]
end

theorem thunk.extend_trace_calls_eq₁ {t: thunk α} {tr: trace α} {m: memory α}:
  t.step = sum.inr (sum.inl m) → (t.extend_trace tr).calls = tr.calls :=
begin
  intro hstep,
  apply thunk.extend_trace_calls_eq,
  simp [hstep]
end

theorem thunk.extend_trace_calls_eq₂ {t: thunk α} {tr: trace α} {m: memory α} {t': thunk α × list α}:
  t.step = sum.inr (sum.inr (none, m, t')) → (t.extend_trace tr).calls = tr.calls :=
begin
  intro hstep,
  apply thunk.extend_trace_calls_eq,
  simp [hstep]
end

theorem thunk.extend_trace_recurses_cons {t: thunk α} {tr: trace α} {t': thunk α × list α} {m: memory α}:
  t.step = sum.inr (sum.inr (none, m, t')) → (t.extend_trace tr).recurses = m::tr.recurses :=
begin
  cases tr,
  intro hstep,
  simp only [thunk.extend_trace, hstep, eq_self_iff_true, and_true]
end

theorem thunk.extend_trace_recurses_eq {t: thunk α} {tr: trace α}:
  (∀ {m t'}, t.step ≠ sum.inr (sum.inr (none, m, t'))) → (t.extend_trace tr).recurses = tr.recurses :=
begin
  cases tr,
  cases hstep: t.step,
  { simp only [thunk.extend_trace, hstep, eq_self_iff_true, imp_true_iff] },
  cases val,
  { simp only [thunk.extend_trace, hstep, eq_self_iff_true, imp_true_iff] },
  rcases val with ⟨_|_,_,_,_⟩,
  {contrapose!, simp },
  { simp only [thunk.extend_trace, hstep, eq_self_iff_true, imp_true_iff] },
end

theorem thunk.extend_trace_recurses_eq₀ {t: thunk α} {tr: trace α} {t': thunk α}:
  t.step = sum.inl t' → (t.extend_trace tr).recurses = tr.recurses :=
begin
  intro hstep,
  apply thunk.extend_trace_recurses_eq,
  simp [hstep]
end

theorem thunk.extend_trace_recurses_eq₁ {t: thunk α} {tr: trace α} {m: memory α}:
  t.step = sum.inr (sum.inl m) → (t.extend_trace tr).recurses = tr.recurses :=
begin
  intro hstep,
  apply thunk.extend_trace_recurses_eq,
  simp [hstep]
end

theorem thunk.extend_trace_recurses_eq₂ {t: thunk α} {tr: trace α} {p: program α} {m: memory α} {t': thunk α × list α}:
  t.step = sum.inr (sum.inr (some p, m, t')) → (t.extend_trace tr).recurses = tr.recurses :=
begin
  intro hstep,
  apply thunk.extend_trace_recurses_eq,
  simp [hstep]
end

inductive thunk.has_trace: thunk α → trace α → Prop
| result (p: program α) (m: memory α): thunk.has_trace ⟨p, [], m⟩ ⟨m, [],  0, [], []⟩
| step {t t': thunk α} {tr: trace α} (ht: t.step_over t') (htr: thunk.has_trace t' tr):
  thunk.has_trace t (thunk.extend_trace t tr)

theorem thunk.has_trace_nil (t: thunk α) {tr: trace α}:
  t.has_trace tr → t.current = [] → tr = ⟨t.state, [], 0, [], []⟩ :=
begin
  intros htr ht,
  cases htr,
  { refl },
  cases t,
  simp only [] at ht,
  simpa [ht, thunk.step_over, thunk.step] using htr_ht,
end
theorem thunk.has_trace_result {t: thunk α} {tr: trace α}:
  t.has_trace tr → (thunk.step_over^~[tr.steps]) t ⟨t.function, [], tr.result⟩ :=
begin
  intro htr,
  induction htr,
  { exact rel_iterate_zero _ _ },
  rw [thunk.extend_trace_steps, thunk.extend_trace_result, rel_iterate_succ_iff, thunk.step_over_function htr_ht],
  exact ⟨_, htr_ht, htr_ih⟩
end


theorem trace.extend_prog_calls_eq {t t': thunk α} (tr: trace α) (htr: t'.has_trace tr):
  (∀ {p x}, t.step ≠ sum.inr (sum.inr (some p, x))) →
  t.step_over t' →
  (t.extend_trace tr).prog_calls t.current = tr.prog_calls t'.current :=
begin
  intros hstep hso,
  cases tr,
  cases t,
  cases t_current,
  { simpa only [thunk.step_over, thunk.step] using hso },
  cases t_current_hd;
  try {
    simp only [thunk.step_over, thunk.step] at hso,
    simp only [thunk.step, program.calls_on_branch, thunk.takes_branch, trace.prog_calls, trace.calls, thunk.extend_trace, thunk.extend_branch, ← hso] },
  { split_ifs;
    simp only [thunk.extend_branch, program.calls_on_branch] },
  { contrapose! hstep,
    simp only [thunk.step, sum.inr.inj_iff, prod.mk.inj_iff, exists_eq_right', exists_eq'] },
  rw [hso.right],
  refl,
end

theorem trace.extend_prog_calls_eq₀ {t t': thunk α} (tr: trace α) (htr: t'.has_trace tr):
  t.step = sum.inl t' →
  (t.extend_trace tr).prog_calls t.current = tr.prog_calls t'.current :=
begin
  intro h,
  apply trace.extend_prog_calls_eq,
  exact htr,
  exact λ _ _, h.symm ▸ sum.inl_ne_inr,
  simp only [thunk.step_over, h],
end

theorem trace.extend_prog_calls_eq₁ {t: thunk α} (tr: trace α) (m: memory α) (htr: t.has_trace tr):
  t.step = sum.inr (sum.inl m) →
  (t.extend_trace tr).prog_calls t.current = tr.prog_calls t.current :=
begin
  intro hstep,
  cases tr,
  cases t,
  cases t_current,
  { simp only [thunk.extend_trace, hstep, trace.prog_calls, thunk.extend_branch, thunk.takes_branch] },
  cases t_current_hd;
  simpa [thunk.step] using hstep,
end

theorem trace.extend_prog_calls_eq₂ {t t' t'': thunk α} (tr: trace α) (r) (m: memory α) (htr: t'.has_trace tr):
  t.step = sum.inr (sum.inr (none, m, t'', r)) →
  t.step_over t' →
  (t.extend_trace tr).prog_calls t.current = tr.prog_calls t'.current :=
begin
  intros hstep hso,
  apply trace.extend_prog_calls_eq,
  exact htr,
  { intros _ _,
    simpa only [hstep, ← push_neg.not_eq, prod.mk.inj_iff, false_and] using not_false },
  exact hso
end

theorem trace.extend_prog_calls_cons {t t': thunk α} (tr: trace α) {p: program α} {m: memory α} (htr: t'.has_trace tr) {r: list α}:
  t.step = sum.inr (sum.inr (some p, m, t', r)) →
  (t.extend_trace tr).prog_calls t.current = (p, m) :: tr.prog_calls t'.current :=
begin
  intro hstep,
  cases tr,
  simp only [hstep, thunk.extend_trace, trace.prog_calls,
    program.calls_on_branch],
  cases t,
  cases t_current,
  simpa only [thunk.step] using hstep,
  cases t_current_hd;
  try { simpa only [thunk.step, prod.mk.inj_iff, false_and] using hstep };
  simp only [thunk.step, prod.mk.inj_iff] at hstep,
  simpa only [program.calls_on_branch, thunk.takes_branch, thunk.extend_branch, ← hstep]
    using list.zip_cons_cons _ _ _ _,
end

theorem trace.extend_prog_calls_cons' {t t' t'': thunk α} (tr: trace α) {p: program α} {m: memory α} (htr: t''.has_trace tr) {r: list α}:
  t.step = sum.inr (sum.inr (some p, m, t', r)) →
  t'.current = t''.current →
  (t.extend_trace tr).prog_calls t.current = (p, m) :: tr.prog_calls t''.current :=
begin
  intros hstep heq,
  cases tr,
  simp only [hstep, thunk.extend_trace, trace.prog_calls,
    program.calls_on_branch],
  cases t,
  cases t_current,
  simpa only [thunk.step] using hstep,
  cases t_current_hd;
  try { simpa only [thunk.step, prod.mk.inj_iff, false_and] using hstep };
  simp only [thunk.step, prod.mk.inj_iff] at hstep,
  simpa only [program.calls_on_branch, thunk.takes_branch, thunk.extend_branch, ← hstep, ← heq]
    using list.zip_cons_cons _ _ _ _,
end

theorem thunk.has_trace.exists_calls_sum {t: thunk α} {tr: trace α}:
  t.has_trace tr → ∃ c, tr.has_call_cost t.current c :=
begin
  unfold trace.has_call_cost,
  intro htr,
  induction htr,
  { refine ⟨0, _⟩,
    unfold trace.prog_calls trace.calls,
    rw [list.zip_nil_right],
    trivial },
  cases hstep:htr_t.step,
  { simp only [thunk.step_over, hstep] at htr_ht,
    rwa [trace.extend_prog_calls_eq₀ _ _ hstep, htr_ht],
    rwa [htr_ht], },
  cases val,
  { simpa only [thunk.step_over, hstep] using htr_ht },
  rcases val with ⟨_|_, _, _, _⟩,
  { rwa [trace.extend_prog_calls_eq₂ _ _ _ _ hstep],
    exact htr_ht,
    exact htr_htr },
  { simp only [thunk.step_over, option.get_or_else, option.map_some', hstep] at htr_ht,
    cases htr_ht.left with c₀ hc₀,
    cases htr_ih with c₁ hc₁,
    rw [trace.extend_prog_calls_cons' _ _ hstep],
    refine ⟨_, c₀, c₁, ⟨_, hc₀⟩, hc₁, rfl⟩,
    apply thunk.set_result_current htr_ht.right.symm,
    apply htr_htr,
  }
end

theorem thunk.has_trace.exists_recurses_sum {t: thunk α} {tr: trace α}:
  t.has_trace tr → ∃ r, tr.has_recurse_cost t.function r :=
begin
  unfold trace.has_recurse_cost,
  intro htr,
  induction htr,
  { exact ⟨0, trivial⟩ },
  cases hstep:htr_t.step,
  { rwa [thunk.extend_trace_recurses_eq₀ hstep, thunk.step_over_function htr_ht] },
  cases val,
  { rwa [thunk.extend_trace_recurses_eq₁ hstep, thunk.step_over_function htr_ht] },
  rcases val with ⟨_|_, _, _⟩,
  { have hfunc := thunk.step_over_function htr_ht,
    simp only [thunk.step_over, option.get_or_else, option.map_none', hstep] at htr_ht,
    cases htr_ht.left with r₀ hr₀,
    cases htr_ih with r₁ hr₁,
    rw [thunk.extend_trace_recurses_cons hstep],
    exact ⟨r₀ + r₁, r₀, r₁, ⟨_, hr₀⟩, hfunc.symm ▸ hr₁, rfl⟩ },
  { rwa [thunk.extend_trace_recurses_eq₂ hstep, thunk.step_over_function htr_ht] },
end

theorem thunk.has_trace.split_cost {t: thunk α} {tr: trace α} {c r: ℕ}:
  t.has_trace tr →
  tr.has_call_cost t.current c →
  tr.has_recurse_cost t.function r →
  t.split_time_cost (tr.steps + 1) c r :=
begin
  unfold trace.has_call_cost trace.has_recurse_cost,
  intro htr,
  induction htr generalizing c r,
  { exact λ _ _, or.inl rfl },
  cases hstep:htr_t.step,
  { rw [trace.extend_prog_calls_eq₀ _ _ hstep, thunk.extend_trace_recurses_eq₀ hstep, thunk.extend_trace_steps, thunk.step_over_function htr_ht],
    intros hcs hrs,
    refine or.inr ⟨_, _, _, _, _, _, htr_ht, _, (zero_add _).symm, (zero_add _).symm⟩,
    { simp only [thunk.external_time_cost_step, hstep] },
    simp only [thunk.step_over, hstep] at htr_ht,
    rw [htr_ht] at hcs,
    exact htr_ih hcs hrs,
    simp only [thunk.step_over, hstep] at htr_ht,
    rw [htr_ht],
    apply htr_htr },
  cases val,
  { simpa only [thunk.step_over, thunk.step, hstep] using htr_ht },
  rcases val with ⟨_ | _, _, _, _⟩,
  { rw [trace.extend_prog_calls_eq₂ _ _ _ _ hstep, thunk.extend_trace_recurses_cons hstep, thunk.extend_trace_steps, thunk.step_over_function htr_ht],
    intros hcs hrs,
    rcases hrs with ⟨r₀, r₁, hrcost, hrs, hr⟩,
    refine or.inr ⟨_, _, _, _, _, _, htr_ht, _, (zero_add _).symm, hr⟩,
    { simpa only [thunk.external_time_cost_step, hstep, option.map_none', option.get_or_else, thunk.step_over_function htr_ht] using hrcost },
    exact htr_ih hcs hrs,
    exact htr_ht,
    exact htr_htr, },
  { rw [trace.extend_prog_calls_cons' _ _ hstep, thunk.extend_trace_recurses_eq₂ hstep, thunk.extend_trace_steps, thunk.step_over_function htr_ht],
    intros hcs hrs,
    rcases hcs with ⟨c₀, c₁, hccost, hcs, hc⟩,
    refine or.inr ⟨_, _, _, _, _, _, htr_ht, _, hc, (zero_add _).symm⟩,
    { simpa only [thunk.external_time_cost_step, hstep, option.map_some', option.get_or_else] using hccost },
    exact htr_ih hcs hrs,
    simp only [thunk.step_over, hstep] at htr_ht,
    apply thunk.set_result_current htr_ht.right.symm,
    apply htr_htr },
end

def program.has_trace (p: program α) (m: memory α) (t: trace α): Prop := thunk.has_trace ⟨p, p, m⟩ t

theorem program.has_trace.result {p: program α} {m: memory α} {t: trace α}:
  p.has_trace m t → p.has_result m t.result :=
λ h, thunk.iterate_step_of_iterate_step_over' (thunk.has_trace_result h)

theorem program.has_trace.result' {p: program α} {m r: memory α} {t: trace α}:
  p.has_trace m t → t.result = r → p.has_result m r :=
λ htr hr, hr ▸ program.has_trace.result htr

theorem program.has_trace.internal_cost {p: program α} {m: memory α} {tr: trace α}:
  p.has_trace m tr → p.internal_cost m (tr.steps + 1) :=
begin
  intros htr,
  cases htr.exists_calls_sum with c hc,
  cases htr.exists_recurses_sum with r hr,
  exact ⟨_, _, htr.split_cost hc hr⟩
end

theorem program.has_trace.call_cost {p: program α} {m: memory α} {tr: trace α} {c: ℕ}:
  p.has_trace m tr →
  tr.has_call_cost p c →
  p.call_cost m c :=
begin
  intros htr hc,
  cases htr.exists_recurses_sum with r hr,
  exact ⟨_, _, htr.split_cost hc hr⟩
end

theorem program.has_trace.recurse_cost {p: program α} {m: memory α} {tr: trace α} {r: ℕ}:
  p.has_trace m tr →
  tr.has_recurse_cost p r →
  p.recurse_cost m r :=
begin
  intros htr hr,
  cases htr.exists_calls_sum with c hc,
  exact ⟨_, _, htr.split_cost hc hr⟩
end

theorem start_trace {p is: program α} {inp: memory α} {tr: trace α}:
  is = p →
  thunk.has_trace ⟨p, is, inp⟩ tr →
  p.has_trace inp tr :=
λ h, h ▸ id

theorem step_trace {t t': thunk α} {tr tr': trace α}:
  t.step_over t' →
  t.extend_trace tr' = tr →
  t'.has_trace tr' →
  t.has_trace tr :=
λ hso hex htr, hex ▸ thunk.has_trace.step hso htr

theorem if_true_trace {r: memory α} {p: program α} {m: memory α} {n cn: ℕ} {cond: vector α cn → Prop} [Π {v}, decidable (cond v)] {src: vector (source α) cn} {br: list bool} {is is': program α} {cs rs: list (memory α)}:
  cond (src.map (λ s, m.getvs s)) →
  thunk.has_trace ⟨p, is', m⟩ ⟨r, br, n, cs, rs⟩ →
  thunk.has_trace ⟨p, (instruction.ite cond src is')::is, m⟩ ⟨r, tt::br, n+1, cs, rs⟩ :=
begin
  intros hcond htr,
  apply step_trace _ _ htr,
  { simp only [thunk.step_over, thunk.step, hcond, if_true, eq_self_iff_true, and_true] },
  simp only [thunk.extend_trace, thunk.step, thunk.extend_branch, thunk.takes_branch, hcond, if_true, eq_self_iff_true, and_true, true_and],
end

theorem if_false_trace {r: memory α} {p: program α} {m: memory α} {n cn: ℕ} {cond: vector α cn → Prop} [Π {v}, decidable (cond v)] {src: vector (source α) cn} {br: list bool} {is is': program α} {cs rs: list (memory α)}:
  ¬ cond (src.map (λ s, m.getvs s)) →
  thunk.has_trace ⟨p, is, m⟩ ⟨r, br, n, cs, rs⟩ →
  thunk.has_trace ⟨p, (instruction.ite cond src is')::is, m⟩ ⟨r, ff::br, n+1, cs, rs⟩ :=
begin
  intros hcond htr,
  apply step_trace _ _ htr,
  { simp only [thunk.step_over, thunk.step, hcond, if_false, eq_self_iff_true, and_true] },
  simp only [thunk.extend_trace, thunk.step, thunk.extend_branch, thunk.takes_branch, hcond, if_false, eq_self_iff_true, and_true, true_and],
end

theorem call_trace {pc: program α} {d s: source α} {p is: program α} {m m' mr r: memory α} {br: list bool} {n: ℕ} {cs rs: list (memory α)}:
  m.getms s = m' →
  pc.has_result m' mr →
  thunk.has_trace ⟨p, is, m.setmp (d.get m) mr⟩ ⟨r, br, n, cs, rs⟩ →
  thunk.has_trace ⟨p, (instruction.call pc d s)::is, m⟩ ⟨r, br, n+1, m'::cs, rs⟩ :=
begin
  intros hm hres htr,
  apply step_trace _ _ htr,
  { simpa only [thunk.step_over, thunk.step,
      option.get_or_else, option.map_none',
      hm, memory.getmp_setmp, thunk.set_result,
      eq_self_iff_true, and_true] using hres },
  { unfold thunk.extend_trace thunk.step,
    rw [hm] }
end

theorem recurse_trace {p: program α} {d s: source α} {is: program α} {m m' mr r: memory α} {br: list bool} {n: ℕ} {cs rs: list (memory α)}:
  m.getms s = m' →
  p.has_result m' mr →
  thunk.has_trace ⟨p, is, m.setmp (d.get m) mr⟩ ⟨r, br, n, cs, rs⟩ →
  thunk.has_trace ⟨p, (instruction.recurse d s)::is, m⟩ ⟨r, br, n+1, cs, m'::rs⟩ :=
begin
  intros hm hres htr,
  apply step_trace _ _ htr,
  { simpa only [thunk.step_over, thunk.step,
      option.get_or_else, option.map_none',
      hm, memory.getmp_setmp, thunk.set_result,
      eq_self_iff_true, and_true] using hres },
  { unfold thunk.extend_trace thunk.step,
    rw [hm] }
end

theorem end_trace {p: program α} {m m': memory α}:
  m = m' → thunk.has_trace ⟨p, [], m⟩ ⟨m', [], 0, [], []⟩ := λ h, h ▸ thunk.has_trace.result p m

end hmem