import tactic

def set.size_le {α: Type*}: set α → ℕ → Prop
| s 0 := s = ∅
| s (n+1) := s = ∅ ∨ ∃ a s', s = insert a s' ∧ set.size_le s' n

theorem set.size_le_mono {α: Type*} {s: set α} {n m: ℕ}:
  s.size_le n → n ≤ m → s.size_le m :=
begin
  intros h hnm,
  induction m generalizing s n,
  { rw [nat.eq_zero_of_le_zero hnm] at h,
    assumption },
  cases n,
  { exact or.inl h },
  cases h,
  { exact or.inl h },
  rcases h with ⟨a, s', hs, h⟩,
  exact or.inr ⟨a, s', hs, m_ih h (nat.succ_le_succ_iff.mp hnm)⟩,
end

namespace hmem

universe u

namespace hidden

inductive memory (α: Type u)
| leaf: memory
| node (value: α) (children: α → memory): memory

variables {α: Type u} [has_zero α] [decidable_eq α]

def getvp: memory α → list α → α
| (memory.leaf) _ := 0
| (memory.node v _) [] := v
| (memory.node _ vs) (a::as) := getvp (vs a) as

def setv: memory α → α → memory α
| (memory.leaf) a := (memory.node a (λ _, memory.leaf))
| (memory.node v vs) a := (memory.node a vs)

def getm: memory α → α → memory α
| (memory.leaf) _ := memory.leaf
| (memory.node _ vs) a := (vs a)

def setm: memory α → α → memory α → memory α
| (memory.leaf) a m := (memory.node 0 (λ x, ite (x = a) m memory.leaf))
| (memory.node v vs) a m := (memory.node v (λ x, ite (x = a) m (vs x))) 

theorem getvp_setv_nil (m: memory α) (a: α): getvp (setv m a) [] = a :=
by cases m; refl

theorem getvp_setv_cons (m: memory α) (a p: α) (ps: list α): getvp (setv m a) (p::ps) = getvp m (p::ps) :=
by cases m; refl

theorem getvp_getm (m: memory α) (a: α) (p: list α): getvp (getm m a) p = getvp m (a :: p) :=
by cases m; refl

theorem getvp_setm_nil (m: memory α) (a: α) (ma: memory α): getvp (setm m a ma) [] = getvp m [] :=
by cases m; refl

theorem getvp_setm_cons (m: memory α) (a: α) (ma: memory α) (p: list α): getvp (setm m a ma) (a::p) = getvp ma p :=
by cases m; simp only [setm, getvp, if_true, eq_self_iff_true]

theorem getvp_setm_cons_ne (m: memory α) (a: α) (ma: memory α) (b: α) (p: list α) (h: b ≠ a): getvp (setm m a ma) (b::p) = getvp m (b::p) :=
by cases m; simp only [setm, getvp, if_false, h]

theorem getm_setm (m: memory α) (a: α) (ma: memory α): getm (setm m a ma) a = ma :=
by cases m; simp only [setm, getm, if_true, eq_self_iff_true]


theorem getm_setv (m: memory α) (v a: α): getm (setv m v) a = getm m a :=
by cases m; simp only [setv, getm, if_true, eq_self_iff_true]

theorem getm_setm_ne (m: memory α) (a: α) (ma: memory α) (b: α) (h: b ≠ a): getm (setm m a ma) b = getm m b :=
by cases m; simp only [setm, getm, if_false, h]

theorem setm_setm (m: memory α) (a: α) (ma ma': memory α): setm (setm m a ma) a ma' = setm m a ma' :=
begin
  cases m;
  simp only [setm, if_true, eq_self_iff_true, true_and];
  funext;
  split_ifs;
  refl
end

theorem setm_setm_ne (m: memory α) (a a': α) (ma ma': memory α) (h: a ≠ a'): setm (setm m a ma) a' ma' = setm (setm m a' ma') a ma :=
begin
  cases m;
  simp only [setm, eq_self_iff_true, true_and];
  funext;
  split_ifs;
  try { refl };
  exfalso;
  apply h;
  rw [← h_1, ← h_2],
end

def equiv (α: Type*) [has_zero α] [decidable_eq α] (a b: memory α): Prop := ∀ p, getvp a p = getvp b p

instance (α: Type*) [has_zero α] [deq: decidable_eq α] [ft: fintype α]: decidable_rel (equiv α) :=
begin
  intros x y,
  induction x generalizing y,
  { induction y,
    { exact decidable.is_true (λ _, rfl) },
    cases deq 0 y_value with heq heq,
    { exact decidable.is_false (λ h, absurd (h []) heq) },
    cases @fintype.decidable_forall_fintype _ _ y_ih _ with hft hft,
    { apply decidable.is_false,
      contrapose! hft,
      exact λ a as, hft (a::as) },
    apply decidable.is_true,
    intro p,
    cases p,
    exact heq,
    exact hft p_hd p_tl },
  cases y,
  { cases deq x_value 0 with heq heq,
    { exact decidable.is_false (λ h, absurd (h []) heq) },
    cases @fintype.decidable_forall_fintype _ _ (λ a, x_ih a memory.leaf) _ with hft hft,
    { apply decidable.is_false,
      contrapose! hft,
      exact λ a as, hft (a::as) },
    apply decidable.is_true,
    intro p,
    cases p,
    exact heq,
    exact hft p_hd p_tl },
  cases deq x_value y_value with heq heq,
  { exact decidable.is_false (λ h, absurd (h []) heq) },
  cases @fintype.decidable_forall_fintype _ _ (λ a, x_ih a (y_children a)) _ with hft hft,
  { apply decidable.is_false,
    contrapose! hft,
    exact λ a as, hft (a::as) },
  apply decidable.is_true,
  intro p,
  cases p,
  exact heq,
  exact hft p_hd p_tl
end

@[refl]
theorem equiv_refl (m: memory α): equiv α m m := λ _, rfl

@[symm]
theorem equiv_symm (m n: memory α): equiv α m n → equiv α n m := λ h p, symm (h p)

@[trans]
theorem equiv_trans (a b c: memory α): equiv α a b → equiv α b c → equiv α a c := λ hab hbc p, trans (hab p) (hbc p) 

end hidden

instance (α: Type u) [has_zero α] [decidable_eq α]: setoid (hidden.memory α) := ⟨ hidden.equiv α, ⟨ hidden.equiv_refl, hidden.equiv_symm, hidden.equiv_trans ⟩ ⟩

def memory (α: Type u) [has_zero α] [decidable_eq α]: Type* := @quotient (hidden.memory α) infer_instance

variables {α: Type*} [has_zero α] [decidable_eq α]

namespace memory
section -- accessing hidden

def null (α: Type*) [has_zero α] [decidable_eq α]: memory α := quotient.mk hidden.memory.leaf

noncomputable def mk (value: α) (children: α → memory α): memory α :=
quotient.mk (hidden.memory.node value (quotient.out ∘ children))

def getv (m: memory α): α :=
begin
  apply quotient.lift_on m (flip hidden.getvp []),
  { intros _ _ h,
    funext,
    exact h _ },
end

def setv (m: memory α) (v: α): memory α :=
begin
  apply quotient.lift_on m (λ x, quotient.mk (hidden.setv x v)),
  intros _ _ h,
  apply quotient.sound,
  funext,
  intro p,
  cases p,
  { rw [hidden.getvp_setv_nil, hidden.getvp_setv_nil] },
  { rw [hidden.getvp_setv_cons, hidden.getvp_setv_cons],
    exact h _ },
end

def getm (m: memory α) (a: α): memory α :=
begin
  apply quotient.lift_on m (λ x, quotient.mk (hidden.getm x a)),
  intros _ _ h,
  apply quotient.sound,
  funext,
  intro p,
  rw [hidden.getvp_getm, hidden.getvp_getm],
  exact h _
end

def setm (m: memory α) (a: α) (ma: memory α): memory α :=
begin
  apply quotient.lift_on₂ m ma (λ x y, quotient.mk (hidden.setm x a y)),
  intros _ _ _ _ h₁ h₂,
  apply quotient.sound,
  funext,
  intro p,
  cases p,
  { rw [hidden.getvp_setm_nil, hidden.getvp_setm_nil],
    exact h₁ _ },
  by_cases p_hd = a,
  { rw [h, hidden.getvp_setm_cons, hidden.getvp_setm_cons],
    exact h₂ _ },
  { rw [hidden.getvp_setm_cons_ne, hidden.getvp_setm_cons_ne],
    exact h₁ _,
    repeat { exact h }, }
end

theorem getv_mk (m: hidden.memory α): getv ⟦m⟧ = hidden.getvp m [] := rfl

theorem getm_mk (m: hidden.memory α) (a: α): getm ⟦m⟧ a = ⟦hidden.getm m a⟧ := rfl

theorem setv_mk (m: hidden.memory α) (a: α): setv ⟦m⟧ a = ⟦hidden.setv m a⟧ := rfl

theorem setm_mk (m: hidden.memory α) (a: α) (ma: hidden.memory α): setm ⟦m⟧ a ⟦ma⟧= ⟦hidden.setm m a ma⟧ := rfl

theorem getv_null: (null α).getv = 0 := rfl

theorem getv_setv (m: memory α) (a: α): (m.setv a).getv = a :=
begin
  cases quotient.exists_rep m with wm hm,
  rw [← hm, setv_mk, getv_mk, hidden.getvp_setv_nil],
end


theorem setv_setv (m: memory α) (a b: α): (m.setv a).setv b= m.setv b :=
begin
  cases quotient.exists_rep m with wm hm,
  rw [← hm, setv_mk, setv_mk, setv_mk],
  apply quotient.sound,
  funext,
  intro p,
  cases p,
  { rw [hidden.getvp_setv_nil, hidden.getvp_setv_nil] },
  { rw [hidden.getvp_setv_cons, hidden.getvp_setv_cons, hidden.getvp_setv_cons] }
end


theorem getv_setm (m: memory α) (a: α) (ma: memory α): (m.setm a ma).getv = m.getv :=
begin
  cases quotient.exists_rep m with wm hm,
  cases quotient.exists_rep ma with wma hma,
  rw [← hm, ← hma, setm_mk, getv_mk, getv_mk, hidden.getvp_setm_nil],
end

theorem setv_getv (m: memory α): m.setv m.getv = m :=
begin
  cases quotient.exists_rep m with wm hm,
  rw [← hm, getv_mk, setv_mk],
  apply quotient.sound,
  funext,
  intro p,
  cases p,
  { rw [hidden.getvp_setv_nil] },
  { rw [hidden.getvp_setv_cons] }
end

theorem setv_setm (m: memory α) (v a: α) (ma: memory α): (m.setv v).setm a ma = (m.setm a ma).setv v :=
begin
  cases quotient.exists_rep m with wm hm,
  cases quotient.exists_rep ma with wma hma,
  rw [← hm, ← hma, setv_mk, setm_mk, setm_mk, setv_mk],
  apply quotient.sound,
  funext,
  intro p,
  cases p,
  { rw [hidden.getvp_setv_nil, hidden.getvp_setm_nil, hidden.getvp_setv_nil] },
  by_cases p_hd = a,
  { rw [h, hidden.getvp_setv_cons, hidden.getvp_setm_cons, hidden.getvp_setm_cons] },
  { rw [hidden.getvp_setv_cons, hidden.getvp_setm_cons_ne _ _ _ _ _ h, hidden.getvp_setm_cons_ne _ _ _ _ _ h, hidden.getvp_setv_cons] }
end

theorem setm_setv (m: memory α) (v a: α) (ma: memory α): (m.setm a ma).setv v = (m.setv v).setm a ma :=
(setv_setm _ _ _ _).symm
theorem getm_null (a: α): (null _).getm a = null _ := rfl

theorem getm_setm (m: memory α) (a: α) (ma: memory α): (m.setm a ma).getm a = ma :=
begin
  cases quotient.exists_rep m with wm hm,
  cases quotient.exists_rep ma with wma hma,
  rw [← hm, ← hma, setm_mk, getm_mk, hidden.getm_setm],
end

theorem getm_setv (m: memory α) (v a: α): (m.setv v).getm a = m.getm a :=
begin
  cases quotient.exists_rep m with wm hm,
  rw [← hm, setv_mk, getm_mk, getm_mk, hidden.getm_setv],
end

theorem getm_setm_ne (m: memory α) (a: α) (ma: memory α) (b: α) (h: b ≠ a): (m.setm a ma).getm b = m.getm b :=
begin
  cases quotient.exists_rep m with wm hm,
  cases quotient.exists_rep ma with wma hma,
  rw [← hm, ← hma, setm_mk, getm_mk, getm_mk, hidden.getm_setm_ne],
  exact h
end

theorem getm_setm_nz (m: memory α) (a: α) (ma: memory α) [ne_zero a]: (m.setm a ma).getm 0 = m.getm 0 :=
begin
  cases quotient.exists_rep m with wm hm,
  cases quotient.exists_rep ma with wma hma,
  rw [← hm, ← hma, setm_mk, getm_mk, getm_mk, hidden.getm_setm_ne],
  apply ne.symm,
  rw ← ne_zero_iff,
  apply_instance
end

theorem getm_setm_nz' (m: memory α) (a: α) (ma: memory α) [ne_zero a]: (m.setm 0 ma).getm a = m.getm a :=
begin
  cases quotient.exists_rep m with wm hm,
  cases quotient.exists_rep ma with wma hma,
  rw [← hm, ← hma, setm_mk, getm_mk, getm_mk, hidden.getm_setm_ne],
  rw ← ne_zero_iff,
  apply_instance
end

theorem setm_getm (m: memory α) (a: α): m.setm a (m.getm a) = m :=
begin
  cases quotient.exists_rep m with wm hm,
  rw [← hm, getm_mk, setm_mk],
  apply quotient.sound,
  funext,
  intro p,
  cases p,
  { rw [hidden.getvp_setm_nil] },
  by_cases p_hd = a,
  { rw [h, hidden.getvp_setm_cons, hidden.getvp_getm] },
  { rw [hidden.getvp_setm_cons_ne],
    exact h }
end

theorem setm_setm (m: memory α) (a: α) (ma ma': memory α): (m.setm a ma).setm a ma' = m.setm a ma' :=
begin
  cases quotient.exists_rep m with wm hm,
  cases quotient.exists_rep ma with wma hma,
  cases quotient.exists_rep ma' with wma' hma',
  rw [← hm, ← hma, ← hma', setm_mk, setm_mk, setm_mk, hidden.setm_setm],
end

theorem setm_setm_ne (m: memory α) (a a': α) (ma ma': memory α) (h: a ≠ a'): (m.setm a ma).setm a' ma' = (m.setm a' ma').setm a ma :=
begin
  cases quotient.exists_rep m with wm hm,
  cases quotient.exists_rep ma with wma hma,
  cases quotient.exists_rep ma' with wma' hma',
  rw [← hm, ← hma, ← hma', setm_mk, setm_mk, setm_mk, hidden.setm_setm_ne, setm_mk],
  exact h
end

theorem setm_setm_nz (m: memory α) (a: α) (ma ma': memory α) [ne_zero a]: (m.setm a ma).setm 0 ma' = (m.setm 0 ma').setm a ma :=
begin
  cases quotient.exists_rep m with wm hm,
  cases quotient.exists_rep ma with wma hma,
  cases quotient.exists_rep ma' with wma' hma',
  rw [← hm, ← hma, ← hma', setm_mk, setm_mk, setm_mk, hidden.setm_setm_ne, setm_mk],
  rw ← ne_zero_iff,
  apply_instance
end
end -- no more need for hidden

theorem getv_congr {m m': memory α} {v v': α}:
  m = m' → m.getv = v → m'.getv = v' → v = v' :=
begin
  intros hm hma hma',
  rw [← hma, ← hma', hm],
end

theorem getm_congr (a: α) {m m' ma ma':memory α}:
  m = m' → m.getm a = ma → m'.getm a = ma' → ma = ma' :=
begin
  intros hm hma hma',
  rw [← hma, ← hma', hm],
end

theorem null_setv_zero:
  (memory.null α).setv 0 = memory.null α :=
begin
  rw [← getv_null, setv_getv],
end

theorem null_setm_null (a: α):
  (memory.null α).setm a (memory.null _) = memory.null α :=
begin
  conv_lhs {
    congr, skip, skip,
    rw [← getm_null a] },
  rw [setm_getm],
end

theorem null_setv_setm_null (v a: α):
  ((memory.null α).setv v).setm a (memory.null _) = (memory.null α).setv v :=
begin
  rw [setv_setm, null_setm_null],
end

theorem setv_inj_iff (m: memory α) (v v': α):
  m.setv v = m.setv v' ↔ v = v' :=
⟨ λ h, getv_congr h (getv_setv _ _) (getv_setv _ _), λ h, h ▸ rfl ⟩

def getmp: memory α → list α → memory α
| m [] := m
| m (a::as) := (m.getm a).getmp as

theorem getmp_nil (m: memory α): m.getmp [] = m := rfl
theorem getmp_cons (m: memory α) (a: α) (as: list α): m.getmp (a::as) = (m.getm a).getmp as := rfl
theorem getmp_null (as: list α): (null _).getmp as = null _ :=
begin
  induction as,
  { exact getmp_nil _ },
  { rwa [getmp_cons] },
end

def setmp: memory α → list α → memory α → memory α
| m [] ma := ma
| m (a::as) ma := m.setm a ((m.getm a).setmp as ma)

theorem setmp_nil (m: memory α) (ma: memory α): m.setmp [] ma = ma := rfl
theorem setmp_cons (m: memory α) (a: α) (as: list α) (ma: memory α): m.setmp (a::as) ma = m.setm a ((m.getm a).setmp as ma) := rfl
theorem setmp_getmp (m: memory α) (as: list α): m.setmp as (m.getmp as) = m :=
begin
  induction as generalizing m,
  { refl },
  rw [setmp_cons, getmp_cons, as_ih, setm_getm],
end
theorem getmp_setmp (m: memory α) (as: list α) (ma: memory α): (m.setmp as ma).getmp as = ma :=
begin
  induction as generalizing m,
  { refl },
  rw [setmp_cons, getmp_cons, getm_setm, as_ih],
end

theorem setmp_setmp (m: memory α) (as: list α) (ma ma': memory α):
  (m.setmp as ma).setmp as ma' = m.setmp as ma' :=
begin
  induction as generalizing m,
  { rw [setmp_nil, setmp_nil] },
  { simp only [setmp_cons, setmp_nil, getm_setm, setm_setm, as_ih] }
end

def getvp (m: memory α) (as: list α): α := getv (getmp m as)

theorem getvp_nil (m: memory α): m.getvp [] = m.getv := rfl
theorem getvp_cons (m: memory α) (a: α) (as: list α): m.getvp (a::as) = (m.getm a).getvp as := rfl
theorem getvp_null (as: list α): (null _).getvp as = 0 :=
begin
  induction as,
  { rw [getvp_nil, getv_null] },
  { rwa [getvp_cons, getm_null] }
end

def setvp (m: memory α) (as: list α) (v: α): memory α := m.setmp as ((m.getmp as).setv v)

theorem setvp_nil (m: memory α) (v: α): m.setvp [] v = m.setv v := rfl
theorem setvp_cons (m: memory α) (a: α) (as: list α) (v: α): m.setvp (a::as) v = m.setm a ((m.getm a).setvp as v) := rfl
theorem setvp_getvp (m: memory α) (as: list α): m.setvp as (m.getvp as) = m :=
begin
  unfold setvp getvp,
  rw [setv_getv, setmp_getmp]
end

def usage_le (m: memory α) (n: ℕ): Prop :=
  set.size_le { p: list α | m.getmp p ≠ null _ } n

def unique_usage_le (m: memory α) (n: ℕ): Prop :=
  set.size_le { m': memory α | ∃ p, m.getmp p = m } n

section

theorem equiv_def (m m': hidden.memory α): hidden.getvp m = hidden.getvp m' → m ≈ m' :=
by intros h p; apply congr_fun h

theorem equiv_def' (m m': hidden.memory α): m ≈ m' → hidden.getvp m = hidden.getvp m' :=
by intro h; ext1 p; exact h p

theorem out_getvp (m: memory α): hidden.getvp (quotient.out m) = m.getvp :=
begin
  ext1 p,
  induction p generalizing m,
  exact getv_congr (quotient.out_eq m) rfl rfl,
  { rw [getvp_cons, ← hidden.getvp_getm, ← p_ih (m.getm p_hd)],
    apply congr_fun,
    apply equiv_def',
    apply quotient.exact _,
    rw [← getm_mk, quotient.out_eq, quotient.out_eq] }
end

theorem mk_getvp (m: hidden.memory α): hidden.getvp m = getvp ⟦m⟧ :=
begin
  rw [← out_getvp],
  apply equiv_def',
  apply quotient.exact _,
  rw [quotient.out_eq],
end

def has_height: memory α → ℕ → Prop
| m 0 := m = null α
| m (n+1) := ∀ a, has_height (m.getm a) n

theorem has_height_null (n: ℕ): (null α).has_height n :=
begin
  induction n,
  exact rfl,
  exact λ a, (getm_null a).symm ▸ n_ih,
end

theorem has_height_mono {m: memory α} {n n': ℕ}: m.has_height n → n ≤ n' → m.has_height n' :=
begin
  induction n' with n' ih generalizing n m,
  { intros hm hn,
    rwa [nat.eq_zero_of_le_zero hn] at hm },
  cases n,
  { exact λ hm _ a, hm.symm ▸ (getm_null a).symm ▸ has_height_null n' },
  exact λ hm hn a, ih (hm a) (nat.succ_le_succ_iff.mp hn)
end

instance [fintype α] (m: memory α) (n: ℕ): decidable (has_height m n) :=
begin
  induction n generalizing m,
  { unfold has_height, apply_instance },
  unfold has_height,
  haveI: decidable_pred (λ a, (m.getm a).has_height n_n) := (λ a, n_ih (m.getm a)),
  apply_instance,
end

theorem has_height_exists [ft: fintype α] (m: memory α):
  ∃ n, m.has_height n :=
begin
  rw [← quotient.out_eq m],
  induction quotient.out m generalizing,
  { exact ⟨0, rfl⟩ },
  by_cases finset.nonempty ft.elems,
  { refine ⟨finset.max' _ (finset.nonempty.image h (λ a, classical.some (ih a))) + 1, _⟩,
    intro a,
    rw [getm_mk, hidden.getm],
    apply has_height_mono,
    apply classical.some_spec (ih a),
    apply finset.le_max',
    apply finset.mem_image_of_mem,
    apply fintype.complete },
  refine ⟨1, _⟩,
  intro a,
  exfalso,
  apply h,
  use a,
  apply fintype.complete,
end

def out_helper: memory α → ℕ → hidden.memory α
| m 0 := hidden.memory.leaf
| m (n+1) := hidden.memory.node m.getv (λ a, out_helper (m.getm a) n)

theorem out_helper_eq {m: memory α} {n: ℕ}: m.has_height n → ⟦m.out_helper n⟧ = m :=
begin
  induction n generalizing m,
  { unfold has_height out_helper,
    intro h,
    rw [h],
    refl },
  unfold has_height out_helper,
  intro h,
  refine eq.trans _ (quotient.out_eq m),
  apply quotient.sound,
  intro p,
  rw [out_getvp],
  cases p,
  { refl },
  unfold hidden.getvp,
  rw [getvp_cons, mk_getvp],
  apply congr_arg2 _ (n_ih (h _)) rfl,
end

def out [fintype α] (m: memory α): hidden.memory α := out_helper m (nat.find (has_height_exists m))

theorem out_eq [fintype α] (m: memory α): ⟦m.out⟧ = m :=
out_helper_eq (nat.find_spec _)
end
end memory

inductive source (α: Type u)
| nil: source
| imm (hd: α) (tl: source): source
| idx (hd: source) (tl: source): source

def source.get: source α → memory α → list α
| (source.nil) m := []
| (source.imm hd tl) m := hd::(source.get tl m)
| (source.idx hd tl) m := (m.getvp (hd.get m))::(source.get tl m)

def memory.getvs (m: memory α) (s: source α) := m.getvp (s.get m)

def memory.setvs (m: memory α) (s: source α) := m.setvp (s.get m)

def memory.getms (m: memory α) (s: source α) := m.getmp (s.get m)

def memory.setms (m: memory α) (s: source α) := m.setmp (s.get m)


end hmem