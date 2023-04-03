import hmem.memory
import hmem.split_cost
import hmem.stack

namespace hmem

structure trace (α: Type*) [has_zero α] [decidable_eq α] :=
  (result: memory α)
  (steps: ℕ)
  (calls: list (program α × memory α))
  (recurses: list (memory α)) 

universe u
variables {α: Type u} [has_zero α] [decidable_eq α]

def trace.has_call_cost (t: trace α) (c: ℕ): Prop :=
  t.calls.sum_le (λ pm, pm.fst.has_time_cost pm.snd) c
  
def trace.has_recurse_cost (t: trace α) (p: program α) (r: ℕ): Prop :=
  t.recurses.sum_le (λ m, p.has_time_cost m) r

def thunk.extend_trace (t: thunk α): trace α → trace α
| ⟨m, i, cs, rs⟩ := match t.step with
  | (sum.inr (sum.inr (option.some p, m', _))) := ⟨m, i + 1, (p, m')::cs, rs⟩
  | (sum.inr (sum.inr (option.none, m', _))) := ⟨m, i + 1, cs, m'::rs⟩
  | _ := ⟨m, i + 1, cs, rs⟩
end

def thunk.extend_trace₀ {t t': thunk α} {tr: trace α} {m: memory α} {n: ℕ} {cs: list (program α × memory α)} {rs: list (memory α)}:
  t.step = sum.inl t' → tr = ⟨m, n, cs, rs⟩ → t.extend_trace tr = ⟨m, n+1, cs, rs⟩ :=
begin
  intros hstep heq,
  simp only [heq, thunk.extend_trace, hstep, eq_self_iff_true, and_true],
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
  t.step = sum.inr (sum.inr (some p, m, t')) → (t.extend_trace tr).calls = (p, m)::tr.calls :=
begin
  cases tr,
  intro hstep,
  simp only [thunk.extend_trace, hstep, eq_self_iff_true, and_true]
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
| result (p: program α) (m: memory α): thunk.has_trace ⟨p, [], m⟩ ⟨m, 0, [], []⟩
| step {t t': thunk α} {tr: trace α} (ht: t.step_over t') (htr: thunk.has_trace t' tr):
  thunk.has_trace t (thunk.extend_trace t tr)

theorem thunk.has_trace_nil (t: thunk α) {tr: trace α}:
  t.has_trace tr → t.current = [] → tr = ⟨t.state, 0, [], []⟩ :=
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

theorem thunk.has_trace.exists_calls_sum {t: thunk α} {tr: trace α}:
  t.has_trace tr → ∃ c, tr.has_call_cost c :=
begin
  unfold trace.has_call_cost,
  intro htr,
  induction htr,
  { exact ⟨0, trivial⟩ },
  cases hstep:htr_t.step,
  { rwa [thunk.extend_trace_calls_eq₀ hstep] },
  cases val,
  { rwa [thunk.extend_trace_calls_eq₁ hstep] },
  rcases val with ⟨_|_, _, _⟩,
  { rwa [thunk.extend_trace_calls_eq₂ hstep] },
  { simp only [thunk.step_over, option.get_or_else, option.map_some', hstep] at htr_ht,
    cases htr_ht.left with c₀ hc₀,
    cases htr_ih with c₁ hc₁,rw [thunk.extend_trace_calls_cons hstep],
    exact ⟨_, _, _, ⟨_, hc₀⟩, hc₁, rfl⟩ }
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
  tr.has_call_cost c →
  tr.has_recurse_cost t.function r →
  t.split_time_cost (tr.steps + 1) c r :=
begin
  unfold trace.has_call_cost trace.has_recurse_cost,
  intro htr,
  induction htr generalizing c r,
  { exact λ _ _, or.inl rfl },
  cases hstep:htr_t.step,
  { rw [thunk.extend_trace_calls_eq₀ hstep, thunk.extend_trace_recurses_eq₀ hstep, thunk.extend_trace_steps, thunk.step_over_function htr_ht],
    intros hcs hrs,
    refine or.inr ⟨_, _, _, _, _, _, htr_ht, _, (zero_add _).symm, (zero_add _).symm⟩,
    { simp only [thunk.external_time_cost_step, hstep] },
    exact htr_ih hcs hrs },
  cases val,
  { simpa only [thunk.step_over, thunk.step, hstep] using htr_ht },
  rcases val with ⟨_ | _, _, _⟩,
  { rw [thunk.extend_trace_calls_eq₂ hstep, thunk.extend_trace_recurses_cons hstep, thunk.extend_trace_steps, thunk.step_over_function htr_ht],
    intros hcs hrs,
    rcases hrs with ⟨r₀, r₁, hrcost, hrs, hr⟩,
    refine or.inr ⟨_, _, _, _, _, _, htr_ht, _, (zero_add _).symm, hr⟩,
    { simpa only [thunk.external_time_cost_step, hstep, option.map_none', option.get_or_else, thunk.step_over_function htr_ht] using hrcost },
    exact htr_ih hcs hrs },
  { rw [thunk.extend_trace_calls_cons hstep, thunk.extend_trace_recurses_eq₂ hstep, thunk.extend_trace_steps, thunk.step_over_function htr_ht],
    intros hcs hrs,
    rcases hcs with ⟨c₀, c₁, hccost, hcs, hc⟩,
    refine or.inr ⟨_, _, _, _, _, _, htr_ht, _, hc, (zero_add _).symm⟩,
    { simpa only [thunk.external_time_cost_step, hstep, option.map_some', option.get_or_else] using hccost },
    exact htr_ih hcs hrs },
end

def program.has_trace (p: program α) (m: memory α) (t: trace α): Prop := thunk.has_trace ⟨p, p, m⟩ t

theorem program.has_trace.result {p: program α} {m: memory α} {t: trace α}:
  p.has_trace m t → p.has_result m t.result :=
λ h, thunk.iterate_step_of_iterate_step_over' (thunk.has_trace_result h)

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
  tr.has_call_cost c →
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


theorem call_trace {pc: program α} {d s: source α} {p is: program α} {m m' mr r: memory α} {n: ℕ} {cs: list (program α × memory α)} {rs: list (memory α)}:
  m.getms s = m' →
  pc.has_result m' mr →
  thunk.has_trace ⟨p, is, m.setmp (d.get m) mr⟩ ⟨r, n, cs, rs⟩ →
  thunk.has_trace ⟨p, (instruction.call pc d s)::is, m⟩ ⟨r, n+1, (pc,m')::cs, rs⟩ :=
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

theorem recurse_trace {p: program α} {d s: source α} {is: program α} {m m' mr r: memory α} {n: ℕ} {cs: list (program α × memory α)} {rs: list (memory α)}:
  m.getms s = m' →
  p.has_result m' mr →
  thunk.has_trace ⟨p, is, m.setmp (d.get m) mr⟩ ⟨r, n, cs, rs⟩ →
  thunk.has_trace ⟨p, (instruction.recurse d s)::is, m⟩ ⟨r, n+1, cs, m'::rs⟩ :=
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
  m = m' → thunk.has_trace ⟨p, [], m⟩ ⟨m', 0, [], []⟩ := λ h, h ▸ thunk.has_trace.result p m

end hmem