import hmem.memory

universe u
variables {α: Type u} [has_zero α] [decidable_eq α]

def list.sum_le {α: Type u}: list α → (α → ℕ → Prop) → ℕ → Prop
| [] _ _ := true
| (a::as) p n := ∃ m m', p a m ∧ as.sum_le p m' ∧ n = m + m'

theorem list.sum_le_nil {α: Type u} {p: α → ℕ → Prop}:
  list.sum_le [] p 0 :=
begin
  trivial
end

theorem list.sum_le_nil' {α: Type u} {p: α → ℕ → Prop} {l: list α}:
  l = [] → list.sum_le l p 0 := λ h, h.symm ▸ list.sum_le_nil

theorem list.sum_le_cons {α: Type u} {hd: α} {tl: list α} {p: α → ℕ → Prop} {m m': ℕ}:
  p hd m →
  tl.sum_le p m' →
  list.sum_le (hd::tl) p (m + m') := λ h_hd h_tl, ⟨m, m', h_hd, h_tl, rfl⟩ 

theorem list.cons_append_tail {α: Type u} (x: α) (xs: list α):
  ∃ ys y, x::xs = ys ++ [y] :=
begin
  induction xs generalizing x,
  { exact ⟨[], x, rfl⟩ },
  rcases xs_ih (xs_hd) with ⟨ys, y, ih⟩,
  refine ⟨x::ys, y, _⟩,
  rw [ih, list.cons_append],
end

theorem list.append_self_iff {α: Type u} (xs ys: list α):
  xs ++ ys = ys ↔ xs = [] :=
begin
  cases xs,
  { rw [list.nil_append],
    exact ⟨ λ _, rfl, λ _, rfl ⟩ },
  { simp only [list.cons_append, list.cons_ne_nil, iff_false],
    intro h,
    have h := congr_arg list.length h,
    simp only [list.length_cons, list.length_append] at h,
    linarith },
end

theorem list.sum_le_mono {α: Type u} {as: list α} {p: α → ℕ → Prop} {n n': ℕ}:
  as.sum_le p n → n ≤ n' → as.sum_le p n' :=
begin
  intros h hn,
  induction as generalizing n n',
  { trivial },
  cases nat.exists_eq_add_of_le hn with x hn,
  rcases h with ⟨m, m', hp, has, hm⟩,
  rw [hn],
  exact ⟨m, m' + x, hp, as_ih has le_self_add, hm.symm ▸ nat.add_assoc _ _ _⟩
end

namespace hmem

namespace instruction
inductive memory_operation
| COPY
| MOVE
| SWAP
end instruction

inductive instruction (α: Type u)
| vop {n: ℕ} (op: vector α n → α) (dst: source α) (src: vector (source α) n): instruction
| mop (op: hmem.instruction.memory_operation) (dst src: source α): instruction
| clear (dst: source α): instruction
| ite {n: ℕ} (cond: vector α n → Prop) [Π {v}, decidable (cond v)] (src: vector (source α) n) (branch: list instruction): instruction
| call (func: list instruction) (dst src: source α): instruction
| recurse (dst src: source α): instruction

instance {α: Type u}: inhabited (instruction α) :=
  ⟨ instruction.mop instruction.memory_operation.COPY source.nil source.nil ⟩ 

namespace instruction

def const (dst: source α) (v: α): instruction α := vop (λ _, v) dst (vector.nil)
def uop (op: α → α) (dst src: source α): instruction α := vop (λ s: vector α 1, op (s.nth ⟨0, zero_lt_one⟩)) dst (vector.cons src vector.nil)
def bop (op: α → α → α) (dst lhs rhs: source α): instruction α := vop (λ s: vector α 2, op (s.nth ⟨0, zero_lt_two⟩) (s.nth ⟨1, one_lt_two⟩)) dst (vector.cons lhs (vector.cons rhs vector.nil))
def ifz (src: source α): list (instruction α) → instruction α := ite (λ s: vector α 1, (s.nth ⟨0, zero_lt_one⟩) = 0) (vector.cons src vector.nil)

@[pattern] def copy: source α → source α → instruction α := instruction.mop instruction.memory_operation.COPY
@[pattern] def move: source α → source α → instruction α := instruction.mop instruction.memory_operation.MOVE
@[pattern] def swap: source α → source α → instruction α := instruction.mop instruction.memory_operation.SWAP

end instruction

@[reducible]
def program (α: Type u):= list (instruction α)

structure thunk (α: Type u) [has_zero α] [decidable_eq α] :=
  (function: program α)
  (current: program α)
  (state: memory α)

def program.call (p: program α) (m: memory α): thunk α := ⟨p, p, m⟩

theorem program.call_function (p: program α) (m: memory α): (p.call m).function = p := rfl

inductive stack (α: Type u) [has_zero α] [decidable_eq α]
| result (value: memory α): stack
| execution (top: thunk α) (callers: list (thunk α × list α)): stack

def memory.mop: memory α → instruction.memory_operation → source α → source α → memory α
| m instruction.memory_operation.COPY dst _ := m.getms dst
| m instruction.memory_operation.MOVE _ _ := memory.null _
| m instruction.memory_operation.SWAP _ src := m.getms src

namespace thunk

def set_result: (thunk α × list α) → memory α → thunk α
| (⟨p, is, m⟩, as) m' := ⟨p, is, m.setmp as m'⟩

def set_result': (thunk α × list α) → memory α → (thunk α × list α)
| (t, as) m := (thunk.set_result (t, as) m, as)

theorem set_result_function {t : thunk α × list α} {m: memory α} {t': thunk α}:
  thunk.set_result t m = t' → t.fst.function = t'.function :=
begin
  intro h,
  rw [← h],
  cases t,
  cases t_fst,
  refl,
end

theorem set_result_function' {t : thunk α × list α} {m: memory α}:
  (thunk.set_result t m).function = t.fst.function :=
begin
  cases t,
  cases t_fst,
  refl,
end

theorem set_result_current {t : thunk α × list α} {m: memory α} {t': thunk α}:
  thunk.set_result t m = t' → t.fst.current = t'.current :=
begin
  intro h,
  rw [← h],
  cases t,
  cases t_fst,
  refl,
end

theorem set_result_current' {t : thunk α × list α} {m: memory α}:
  (thunk.set_result t m).current = t.fst.current :=
eq.symm (set_result_current rfl)

theorem set_result_set_result' {t : thunk α × list α} {m m': memory α}:
  set_result (set_result' t m) m' = set_result t m' :=
begin
  cases t,
  cases t_fst,
  simp only [set_result, set_result', memory.setmp_setmp, eq_self_iff_true, and_true]
end

def step: thunk α → (thunk α ⊕ memory α ⊕ (option (program α) × memory α × thunk α × list α))
| ⟨_, [], m⟩ := sum.inr (sum.inl m)
| ⟨p, (instruction.vop op dst src)::is, m⟩ := sum.inl ⟨p, is, m.setvs dst (op (src.map (λ s, m.getvs s)))⟩
| ⟨p, (instruction.mop op dst src)::is, m⟩ := sum.inl ⟨p, is, (m.setms src (m.mop op src dst)).setms dst (m.getms src)⟩
| ⟨p, (instruction.clear dst)::is, m⟩ := sum.inl ⟨p, is, m.setms dst (memory.null _)⟩
| ⟨p, (@instruction.ite _ _ cond dcond src is')::is, m⟩ := sum.inl ⟨p, @ite _ (cond (src.map (λ s, m.getvs s))) (@dcond _) is' is, m⟩
| ⟨p, (instruction.call func dst src)::is, m⟩ := sum.inr (sum.inr (some func, m.getms src, ⟨p, is, m⟩, dst.get m))
| ⟨p, (instruction.recurse dst src)::is, m⟩ := sum.inr (sum.inr (none, m.getms src,  ⟨p, is, m⟩, dst.get m))

def takes_branch: thunk α → option bool
| ⟨p, (@instruction.ite _ _ cond dcond src is')::is, m⟩ :=
  @ite _ (cond (src.map (λ s, m.getvs s))) (@dcond _) (some tt) (some ff)
| _ := none

theorem step_nil_iff (t: thunk α):
  t.current = [] ↔ ∃ m, t.step = sum.inr (sum.inl m) :=
begin
  cases t,
  cases t_current;
  try { cases t_current_hd };
  simp [step]
end

theorem step_return_nil {t: thunk α} {m: memory α}:
  t.step = sum.inr (sum.inl m) → t.current = [] :=
λ x, (step_nil_iff _).mpr ⟨_, x⟩

theorem step_return_nil' {p is: program α} {m: memory α} {m': memory α}:
  thunk.step ⟨p, is, m⟩ = sum.inr (sum.inl m') → is = [] := step_return_nil

theorem step_function₀ {t t': thunk α}:
  t.step = sum.inl t' → t.function = t'.function :=
begin
  cases t,
  cases t_current;
  try { cases t_current_hd };
  simp only [step, false_implies_iff];
  intro h;
  rw [← h]
end

theorem step_function₂ {t: thunk α} {p: option (program α)} {m: memory α} {as: list α} {t': thunk α}:
  t.step = sum.inr (sum.inr (p, m, t', as)) → t.function = t'.function :=
begin
  cases t,
  cases t_current;
  try { cases t_current_hd };
  simp only [step, false_implies_iff, prod.mk.inj_iff, and_imp];
  intros _ _ h _;
  rw [← h]
end

end thunk

namespace stack
def step: stack α → stack α
| (execution f caller) := match f.step with
  | (sum.inl f') := execution f' caller
  | (sum.inr (sum.inl v)) := match caller with
    | [] := result v
    | (c::cs) := execution (thunk.set_result c v) cs
    end
  | (sum.inr (sum.inr (p, m, ret))) := execution ((p.get_or_else f.function).call m) ((thunk.set_result' ret (memory.null _))::caller)
  end
| r := r

theorem step_function {c : thunk α} {cs: list (thunk α × list α)} {c': thunk α} {cs': list (thunk α × list α)}:
  (execution c cs).step = (execution c' cs') → (list.last ((c, [])::cs) (list.cons_ne_nil _ _)).fst.function = (list.last ((c', [])::cs') (list.cons_ne_nil _ _)).fst.function :=
begin
  cases hstep:c.step,
  { simp only [step, hstep, and_imp],
    cases cs,
    { intros hc hcs,
      rw [← hcs, list.last_singleton, list.last_singleton, ← hc],
      exact thunk.step_function₀ hstep },
    intros hc hcs,
    rw [← hcs, list.last_cons_cons, list.last_cons_cons] },
  cases val,
  { cases cs,
    { simp only [step, hstep, false_implies_iff] },
    simp only [step, hstep, and_imp],
    cases cs_tl,
    { intros hc hcs,
      rw [← hcs, list.last_cons_cons, list.last_singleton, list.last_singleton],
      exact thunk.set_result_function hc },
    intros hc hcs,
    rw [← hcs, list.last_cons_cons, list.last_cons_cons, list.last_cons_cons] },
  rcases val with ⟨_, _, _, _⟩,
  simp only [step, hstep, and_imp],
  cases cs,
  { intros hc hcs,
    rw [← hcs, list.last_cons_cons, list.last_singleton, list.last_singleton],
    unfold thunk.set_result',
    rw [thunk.step_function₂ hstep, thunk.set_result_function'] },
  intros hc hcs,
  rw [← hcs, list.last_cons_cons, list.last_cons_cons, list.last_cons_cons]
end

def result_halt (m: memory α) (n: ℕ):
  step^[n] (result m) = result m :=
begin
  induction n,
  { refl },
  { rw [function.iterate_succ_apply', n_ih],
    refl }
end

def result_mono {s: stack α} {n n': ℕ}:
  (∃ m, step^[n] s = result m) → n ≤ n' → ∃ m, step^[n'] s = result m :=
begin
  intros h hn,
  cases nat.exists_eq_add_of_le hn with x hx,
  cases h with m h,
  simp only [hx, add_comm n x, function.iterate_add_apply, h, result_halt, result.inj_eq, exists_eq'],
end

theorem nstep_function {c : thunk α} {cs: list (thunk α × list α)} {n: ℕ} {c': thunk α} {cs': list (thunk α × list α)}:
  step^[n] (execution c cs) = (execution c' cs') → (list.last ((c, [])::cs) (list.cons_ne_nil _ _)).fst.function = (list.last ((c', [])::cs') (list.cons_ne_nil _ _)).fst.function :=
begin
  induction n generalizing c cs,
  { rw [function.iterate_zero_apply, execution.inj_eq, and_imp],
    intros hc hcs,
    rw [hc, hcs] },
  rw [function.iterate_succ_apply],
  cases hstep:(execution c cs).step,
  { simp only [result_halt, false_implies_iff] },
  exact λ h, eq.trans (step_function hstep) (n_ih h)
end

theorem nstep_function' {c : thunk α} {n: ℕ} {c': thunk α}:
  step^[n] (execution c []) = (execution c' []) → c.function = c'.function := nstep_function

theorem step_result_iff {t: thunk α} {cs: list (thunk α × list α)} {m: memory α}:
  step (execution t cs) = result m ↔ cs = [] ∧ ∃ p, t = ⟨p, [], m⟩ :=
begin
  split,
  { cases t,
    cases t_current,
    { cases cs,
      { unfold step thunk.step,
        intro h,
        refine ⟨ rfl, t_function, _ ⟩,
        rw [thunk.mk.inj_eq],
        exact ⟨ rfl, rfl, result.inj h ⟩ },
      trivial },
    cases t_current_hd;
    unfold step thunk.step;
    trivial },
  rw [and_imp, exists_imp_distrib],
  intros hcs _ ht,
  rw [ht, hcs],
  refl
end

def result_prev {c: thunk α} {cs: list (thunk α × list α)} {m: memory α}:
  (execution c cs).step = result m ↔
  c = ⟨ c.function, [], m ⟩ ∧ cs = [] :=
begin
  cases c,
  cases c_current;
  cases cs;
  try { cases c_current_hd };
  simp only [step, thunk.step, eq_self_iff_true, and_true, true_and, iff_self, and_false, false_and],
end

def result_nprev {c: thunk α} {cs: list (thunk α × list α)} {n: ℕ} {m: memory α}:
  step^[n] (execution c cs) = result m ↔
  ∃ t (n' < n), step^[n'] (execution c cs) = execution ⟨t, [], m⟩ [] :=
begin
  split,
  { induction n generalizing c cs,
    { simp only [function.iterate_zero_apply, false_implies_iff] },
    rw [function.iterate_succ_apply],
    cases hstep:(execution c cs).step,
    { refine λ h, ⟨ c.function, 0, (nat.zero_lt_succ _), _⟩,
      simp only [function.iterate_zero_apply, execution.inj_eq, and_assoc],
      rw [result_halt, result.inj_eq] at h,
      rwa [← result_prev, ← h] },
    intro h,
    rcases n_ih h with ⟨t, n', hn, ih⟩,
    refine ⟨t, n'+1, nat.succ_lt_succ hn, _⟩,
    rwa [function.iterate_succ_apply, hstep] },
  { intro h,
    rcases h with ⟨t, n', hn', h⟩,
    cases nat.exists_eq_add_of_lt hn' with x hx,
    rw [hx, nat.add_assoc, nat.add_comm, function.iterate_add_apply, h, function.iterate_succ_apply],
    unfold stack.step thunk.step,
    exact result_halt _ _ }
end

def result_nprev' {c: thunk α} {n: ℕ} {m: memory α}:
  step^[n] (execution c []) = result m ↔
  ∃ (n' < n), step^[n'] (execution c []) = execution ⟨c.function, [], m⟩ [] :=
begin
  rw [result_nprev],
  split,
  { intro h,
    rcases h with ⟨p, n', hn, h⟩,
    refine ⟨n', hn, _⟩,
    rw [h, nstep_function' h] },
  { intro h,
    rcases h with ⟨n', hn, h⟩,
    exact ⟨_, n', hn, h⟩ }
end

theorem step_return {t: thunk α} {cs: list (thunk α × list α)} {m: memory α}:
  step (execution t cs) = result m → ∀ c css, step (execution t (cs ++ ((thunk.set_result' c (memory.null _))::css))) = execution (thunk.set_result c m) css :=
begin
  rw [step_result_iff, and_imp, exists_imp_distrib],
  intros hcs _ ht _ _,
  rw [hcs, ht],
  cases c,
  cases c_fst,
  unfold stack.step thunk.step,
  rw [list.nil_append],
  unfold stack.step,
  rw [thunk.set_result_set_result'],
end

theorem step_append {t: thunk α} {t': thunk α} {cs cs': list (thunk α × list α)} :
  step (execution t cs) = (execution t' cs') → ∀ css, step (execution t (cs ++ css)) = (execution t' (cs' ++ css)) :=
begin
  cases t,
  cases t_current,
  { cases cs,
    { trivial },
    unfold step thunk.step,
    rw [execution.inj_eq, and_imp],
    intros ht hcs _,
    rw [← ht, ← hcs, list.cons_append],
    refl },
  cases t_current_hd;
  unfold step thunk.step;
  rw [execution.inj_eq, and_imp];
  intros ht hcs _;
  rw [← ht, ← hcs];
  try { rw [list.nil_append] };
  try { rw [list.cons_append] },
end

theorem step_iterate_append {t: thunk α} {n: ℕ} {t': thunk α} {cs cs': list (thunk α × list α)}:
  step^[n] (execution t cs) = execution t' cs' → ∀ css,  step^[n] (execution t (cs ++ css)) = execution t' (cs' ++ css) :=
begin
  induction n generalizing t t' cs cs',
  { rw [function.iterate_zero_apply, execution.inj_eq, and_imp],
    intros ht hcs _,
    rw [function.iterate_zero_apply, ← ht, ← hcs] },
  rw [function.iterate_succ_apply],
  cases h:(execution t cs).step,
  { rw [result_halt],
    trivial },
  intros hn _,
  rw [function.iterate_succ_apply, step_append h, n_ih hn]
end

theorem step_iterate_return {t: thunk α} {cs: list (thunk α × list α)} {n: ℕ} {m: memory α}:
  step^[n] (execution t cs) = result m →
  ∀ c css, ∃ n' ≤ n, step^[n'] (execution t (cs ++ ((thunk.set_result' c (memory.null _))::css))) = execution (thunk.set_result c m) css :=
begin
  induction n generalizing t cs m,
  { trivial },
  rw [function.iterate_succ_apply],
  cases hex:(step (execution t cs)),
  { rw [result_halt, result.inj_eq],
    intros hm _ _,
    refine ⟨1, nat.succ_le_succ (nat.zero_le _), _⟩,
    apply step_return,
    rwa [← hm] },
  { intros hstep _ _,
    rcases n_ih hstep _ _ with ⟨n', hn, h⟩,
    refine ⟨n'.succ, nat.succ_le_succ hn, _ ⟩,
    rwa [function.iterate_succ_apply, step_append hex] }
end

theorem step_iterate_return' {t: thunk α} {n: ℕ} {m: memory α}:
  step^[n] (execution t []) = result m →
  ∀ c, ∃ n' ≤ n, step^[n'] (execution t [thunk.set_result' c (memory.null _)]) = execution (thunk.set_result c m) [] :=
λ h c, step_iterate_return h c []

theorem return_of_step_iterate {t: thunk α } {c: thunk α × list α} {cs css: list (thunk α × list α)} {n: ℕ} {t': thunk α}:
  step^[n] (execution t (cs ++ c::css)) = execution t' css → ∃ (p: memory α) m ≤ n, step^[m] (execution t cs) = result p :=
begin
  induction n using nat.strong_induction_on with n ih generalizing t c cs t',
  cases n,
  { simp only [← @list.singleton_append _ c css, ← list.append_assoc,
      function.iterate_zero_apply, list.append_self_iff, list.append_ne_nil_of_ne_nil_right _ [c] (list.cons_ne_nil _ _),
      and_false, false_implies_iff] },
  rw [function.iterate_succ_apply],
  cases hstep:(t.step),
  { simp only [stack.step, hstep],
    intro h,
    rcases ih _ (nat.lt_succ_self _) h with ⟨p, m, hm, ih⟩,
    refine ⟨p, _, nat.succ_le_succ hm, _⟩,
    simpa only [function.iterate_succ_apply, stack.step, hstep] using ih },
  cases val,
  { cases cs,
    { refine λ _, ⟨val, 1, nat.succ_le_succ (nat.zero_le _), _⟩,
      simp only [function.iterate_one, stack.step, hstep] },
    simp only [function.iterate_succ_apply, stack.step, hstep, list.cons_append],
    intro h,
    rcases ih _ (nat.lt_succ_self _) h with ⟨p, n', hn', ih⟩,
    refine ⟨p, n' + 1, (nat.succ_le_succ hn'), _⟩,
    simpa only [function.iterate_succ_apply, stack.step, hstep] using ih },
  rcases val with ⟨_, _, c'⟩,
  simp only[stack.step, hstep, ← list.cons_append],
  intro h,
  rcases ih _ (nat.lt_succ_self _) h with ⟨p₁, n₁, hn₁, ih₁⟩,
  rcases step_iterate_return ih₁ c css with ⟨n₂, hn₂, ih₂⟩,
  rcases ih _ (nat.lt_succ_of_le (trans hn₂ hn₁)) ih₂ with ⟨p₃, n₃, hn₃, ih₃⟩,
  refine ⟨p₃, n₃ + 1, nat.succ_le_succ (le_trans (le_trans hn₃ hn₂) hn₁), _⟩,
  simpa only [function.iterate_succ_apply, stack.step, hstep, ih₂] using ih₃,
end

theorem result_of_step_iterate {t: thunk α} {c: thunk α × list α} {cs: list (thunk α × list α)} {n: ℕ} {t': thunk α}:
  step^[n] (execution t (c::cs)) = execution t' cs →
  ∃ (p: memory α) m ≤ n, step^[m] (execution t []) = result p :=
list.nil_append (c::cs) ▸ return_of_step_iterate

theorem nstep_result_sub {s s': stack α} {n n': ℕ} {m: memory α}:
  step^[n] s = s' → (step^[n']) s = result m → (step^[n' - n]) s' = result m :=
begin
  cases s,
  { intros hs hm,
    rw [← hs, ← hm, result_halt, result_halt, result_halt] },
  cases le_total n n';
  cases nat.exists_eq_add_of_le h with x h;
  rw [h, add_comm, function.iterate_add_apply],
  { intro hs,
    rw [hs, nat.add_sub_cancel],
    exact id },
  { intros hs hm,
    rw [← hs, hm, result_halt, result_halt] }
end

def memory_usage_le: stack α → ℕ → Prop
| (result m) n := m.usage_le n
| (execution f fs) n := ((f::fs.map prod.fst).map thunk.state).sum_le memory.usage_le n

def memory_usage_mono {s: stack α} {n m: ℕ}:
  s.memory_usage_le n → n ≤ m → s.memory_usage_le m :=
begin
  cases s,
  { apply set.size_le_mono },
  { apply list.sum_le_mono }
end

def get_result: stack α → memory α
| (result m) := m
| _ := memory.null α

theorem get_result_value_of_exists {s: stack α}: (∃ m, s = stack.result m) → s = result s.get_result :=
by cases s; simpa only [get_result, exists_eq', exists_false, eq_self_iff_true] using id

end stack

namespace program
def halts_on (p: program α) (inp: memory α) :=
  ∃ n outp, stack.step^[n] (stack.execution ⟨p, p, inp⟩ []) = stack.result outp

instance decidable_stack_result (s: stack α): decidable_pred (λ n, ∃ outp,(stack.step^[n]) s = stack.result outp) :=
begin
  intro n,
  cases h:((stack.step^[n]) s) with m,
  exact decidable.is_true ⟨m, h⟩,
  refine decidable.is_false _,
  simpa only [h, exists_false] using not_false,
end

def result (p: program α) (inp: memory α) (h: halts_on p inp): memory α :=
stack.get_result ((stack.step^[nat.find h]) (stack.execution ⟨p, p, inp⟩ []))

def has_result (p: program α) (inp outp: memory α) :=
  ∃ n, stack.step^[n] (stack.execution ⟨p, p, inp⟩ []) = stack.result outp

theorem result_sound (p: program α) (inp: memory α) (h: halts_on p inp):
  has_result p inp (result p inp h) :=
⟨_, stack.get_result_value_of_exists (nat.find_spec h)⟩


def has_time_cost (p: program α) (inp: memory α) (n: ℕ) :=
  ∃ outp, stack.step^[n] (stack.execution ⟨p, p, inp⟩ []) = stack.result outp

def has_memory_cost (p: program α) (inp: memory α) (m: ℕ) :=
  ∀ n, ((stack.step^[n]) (stack.execution ⟨p, p, inp⟩ [])).memory_usage_le m

theorem unique_result {p: program α} {inp outp outp': memory α}:
  p.has_result inp outp → p.has_result inp outp' → outp = outp' :=
begin
  intros h h',
  cases h with n h,
  cases h' with n' h',
  cases le_total n n' with hn hn,
  { cases nat.exists_eq_add_of_le hn with x hn,
    apply stack.result.inj,
    rwa [← stack.result_halt _ x, ← h, ← function.iterate_add_apply, add_comm, ← hn] },
  { cases nat.exists_eq_add_of_le hn with x hn,
    apply stack.result.inj,
    rwa [← stack.result_halt outp' x, ← h', ← function.iterate_add_apply, add_comm, ← hn, eq_comm] }
end

theorem unique_result' (p: program α) (inp outp: memory α) (h: halts_on p inp):
  has_result p inp outp → result p inp h = outp :=
unique_result (result_sound _ _ _)

theorem time_cost_mono {p: program α} {inp: memory α} {n m: ℕ}:
  p.has_time_cost inp n → n ≤ m → p.has_time_cost inp m :=
begin
  intros h hnm,
  cases nat.exists_eq_add_of_le hnm with x hnm,
  cases h with outp h,
  refine ⟨outp, _⟩,
  rw [hnm, add_comm, function.iterate_add_apply, h, stack.result_halt]
end

theorem memory_cost_mono {p: program α} {inp: memory α} {n m: ℕ}:
  p.has_memory_cost inp n → n ≤ m → p.has_memory_cost inp m :=
λ h hnm _,  stack.memory_usage_mono (h _) hnm

end program

end hmem