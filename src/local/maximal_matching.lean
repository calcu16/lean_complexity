import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.matching
import combinatorics.simple_graph.coloring
import data.finset.basic
import set_theory.cardinal.basic
import set_theory.cardinal.finite
import set_theory.cardinal.ordinal
import local.cardinal
import local.set
import local.subgraph
import local.matching
import local.connectivity
universe univ

variables {V : Type univ} {α : Type*} {G : simple_graph V} {M : G.subgraph}
variables {u v : V}
variables {p: G.path u v}

lemma sym2.mem_exists: ∀ xy: sym2 V, ∃ x : V, x ∈ xy :=
begin
  rw sym2.forall,
  exact λ x y, ⟨x, sym2.mem_mk_left _ _⟩,
end

noncomputable
def sym2.left (xy: sym2 V): V := classical.some (sym2.mem_exists xy)

theorem sym2.left.mem (xy: sym2 V): sym2.left xy ∈ xy := classical.some_spec (sym2.mem_exists xy)

theorem sym2.left.mem_of_eq {xy: sym2 V}: sym2.left xy = v → v ∈ xy :=
begin
  intro h,
  rw [← h],
  exact sym2.left.mem _
end

theorem sym2.or_of_left (x y: V): x = sym2.left ⟦(x, y)⟧ ∨ y = sym2.left ⟦(x, y)⟧ :=
begin
  cases sym2.mem_iff.mp (sym2.left.mem ⟦(x, y)⟧); rw [h],
  exact or.inl rfl,
  exact or.inr rfl,
end

theorem sym2.or_of_left_eq {x y z: V}: sym2.left ⟦(x, y)⟧ = z → x = z ∨ y = z :=
begin
  cases sym2.mem_iff.mp (sym2.left.mem ⟦(x, y)⟧); rw [h],
  exact or.inl,
  exact or.inr
end

namespace simple_graph
namespace subgraph

def is_matching.left (hM: M.is_matching): set V := set.image sym2.left M.edge_set

def is_matching.right (hM: M.is_matching): set V := set.image hM.other hM.left

theorem is_matching.right_of_left (hM: M.is_matching): hM.right = set.image hM.other hM.left := rfl

theorem is_matching.left_of_right (hM: M.is_matching):
  hM.left = set.image hM.other hM.right :=
by ext1; simp [is_matching.right, set.mem_image, is_matching.other_inverse]

theorem is_matching.left_def (hM: M.is_matching) {e: sym2 V}: e ∈ M.edge_set → e.left ∈ hM.left := set.mem_image_of_mem _

theorem is_matching.left_mem (hM: M.is_matching) {v: V}: v ∈ hM.left → v ∈ M.verts :=
begin
  simp only [is_matching.left, set.mem_image, forall_exists_index, and_imp, sym2.forall],
  exact λ x y hxy hv, (hv.symm ▸ mem_verts_if_mem_edge) hxy (sym2.left.mem _),
end

theorem is_matching.left_subset (hM: M.is_matching): hM.left ⊆ M.verts := λ _, hM.left_mem

theorem is_matching.left_mem_of_right (hM: M.is_matching) {v: V}: v ∈ hM.right → hM.other v ∈ hM.left :=
by simp [hM.left_of_right, hM.other_inj_iff]

theorem is_matching.left_mem_of_right' (hM: M.is_matching) {v: V}: hM.other v ∈ hM.right → v ∈ hM.left :=
by simp [hM.left_of_right, hM.other_inj_iff']


theorem is_matching.right_mem_of_left (hM: M.is_matching) {v: V}: v ∈ hM.left → hM.other v ∈ hM.right :=
by simp [is_matching.right, hM.other_inj_iff]

theorem is_matching.right_mem_of_left' (hM: M.is_matching) {v: V}: hM.other v ∈ hM.left → v ∈ hM.right :=
by simp [is_matching.right, hM.other_inj_iff']

theorem is_matching.right_mem (hM: M.is_matching) {v: V}: v ∈ hM.right → v ∈ M.verts :=
begin
  simp only [is_matching.right, set.mem_image, forall_exists_index, and_imp, sym2.forall],
  exact λ x hxM hxv, hxv ▸ hM.other_mem_verts (hM.left_mem hxM)
end

theorem is_matching.left_unique_edge  (hM: M.is_matching) {v: V}: v ∈ hM.left → ∃! u : sym2 V, u ∈ M.edge_set ∧ u.left = v :=
begin
  unfold is_matching.left,
  rw [set.mem_image],
  intro h,
  rcases h with ⟨x, hxM, hxv⟩,
  refine exists_unique_of_exists_of_unique ⟨x, hxM, hxv⟩ _,
  simp only [and_imp],
  intros y z hyM hyv hzM hzv,
  exact hM.unique_edge hyM hzM (sym2.left.mem_of_eq hyv) (sym2.left.mem_of_eq hzv),
end

theorem is_matching.left_unique_edge' (hM: M.is_matching) {v: V}: v ∈ hM.left → ∃! u : sym2 V, u ∈ M.edge_set ∧ v ∈ u :=
begin
  unfold is_matching.left,
  rw [set.mem_image],
  intro h,
  rcases h with ⟨x, hxM, hxv⟩,
  refine exists_unique_of_exists_of_unique ⟨x, hxM, sym2.left.mem_of_eq hxv⟩ _,
  simp only [and_imp],
  intros y z hyM hyv hzM hzv,
  exact hM.unique_edge hyM hzM hyv hzv,
end

theorem is_matching.left_of_edge (hM: M.is_matching) {v: V} {e: sym2 V}: v ∈ hM.left → v ∈ e → e ∈ M.edge_set → e.left = v :=
begin
  intros hvM hve heM,
  rcases exists_unique.exists (hM.left_unique_edge hvM) with ⟨x, hxM, hxv⟩,
  rwa exists_unique.unique (hM.left_unique_edge' hvM) (and.intro heM hve) (and.intro hxM (sym2.left.mem_of_eq hxv)),
end

theorem is_matching.left_other (hM: M.is_matching) {v: V}: v ∈ hM.left → hM.other v ∉ hM.left :=
begin
  intros hv hv',
  rcases hM.left_unique_edge' hv with ⟨e, ⟨hm, hve⟩, hu ⟩,
  rcases exists_unique.exists (hM.left_unique_edge' hv') with ⟨e', hm', hve'⟩,
  apply hM.ne_of_mem (hM.left_mem hv),
  rw [← hM.left_of_edge hv' hve' hm', ← hM.left_of_edge hv hve hm, hu e' (and.intro hm' (hM.edge_of_other hve' hm'))],
end

theorem is_matching.left_other' (hM: M.is_matching) {v: V}: hM.other v ∈ hM.left → v ∉ hM.left :=
   λ h, hM.other_inverse v ▸ (hM.left_other h)
  
theorem is_matching.right_other (hM: M.is_matching) {v: V}: v ∈ hM.right → hM.other v ∉ hM.right :=
λ hl hr, hM.left_other (hM.left_mem_of_right hl) (hM.left_mem_of_right hr)


theorem is_matching.right_other' (hM: M.is_matching) {v: V}: hM.other v ∈ hM.right → v ∉ hM.right :=
  λ h, hM.other_inverse v ▸ (hM.right_other h)

theorem is_matching.left_independent (hM: M.is_matching) (x y: V): x ∈ hM.left → y ∈ hM.left → ¬ M.adj x y :=
begin
  intros hx hy he,
  rw [hM.other_of_adj_iff (hM.left_mem hy)] at he,
  apply hM.left_other hy,
  rwa [← he]
end

theorem is_matching.left_is_antichain (hM: M.is_matching): is_antichain M.adj hM.left :=
begin
  intros x hx y hy _,
  unfold has_compl.compl,
  rw [hM.other_of_adj_iff (hM.left_mem hy)],
  intro heq,
  apply hM.left_other hy,
  rwa [← heq],
end

theorem is_matching.left_edge_cover (hM: M.is_matching) {x y: V}:
  M.adj x y → x ∈ hM.left ∨ y ∈ hM.left :=
begin
  rw [← mem_edge_set],
  intro p,
  cases sym2.or_of_left x y with h h;
  rw [h],
  exact or.inl (hM.left_def p),
  exact or.inr (hM.left_def p),
end

theorem is_matching.left_other_cover (hM: M.is_matching) {x: V}:
  x ∈ M.verts → x ∈ hM.left ∨ hM.other x ∈ hM.left := hM.left_edge_cover ∘ hM.other_adj

theorem is_matching.other_card (hM: M.is_matching) {s: set V}:
  cardinal.mk s = cardinal.mk (s.image hM.other) :=
begin
  rw cardinal.eq,
  refine ⟨⟨
    λ x, ⟨hM.other x, (set.mem_image _ _ _).mpr ⟨x, x.property, rfl⟩⟩,
    λ x, ⟨hM.other x, _, ⟩,
      _, _⟩⟩,
    { rcases x.property with ⟨y, hys, hyx⟩,
      unfold_coes,
      rwa [← hyx, hM.other_inverse] },
  all_goals { intro; simp [hM.other_inverse] },
end

theorem is_matching.left_right_card (hM: M.is_matching):
  cardinal.mk hM.left = cardinal.mk hM.right :=
begin
  rw cardinal.eq,
  refine ⟨⟨
    λ x, ⟨hM.other x, (set.mem_image _ _ _).mpr ⟨x, x.property, rfl⟩⟩,
    λ x, ⟨hM.other x, hM.left_of_right.symm ▸ (set.mem_image _ _ _).mpr ⟨x, x.property, rfl⟩⟩,
    _, _ ⟩⟩,
    all_goals { intro; simp [hM.other_inverse] },
end

theorem is_matching.left_right_total (hM: M.is_matching):
  M.verts = hM.left ∪ hM.right :=
set.ext (λ x, ⟨
    λ hx, or.elim (hM.left_other_cover hx)
      (λ h, or.inl h)
      (λ h, or.inr ((set.mem_image _ _ _).mpr ⟨hM.other x, h, hM.other_inverse _⟩)),
    λ h, or.elim h hM.left_mem hM.right_mem ⟩)

theorem is_matching.left_right_disjoint (hM: M.is_matching):
  disjoint hM.left hM.right :=
begin
  rw [set.disjoint_left],
  exact λ _ h, hM.right_other' (hM.right_mem_of_left h)
end

theorem is_matching.other_disjoint (hM: M.is_matching) {s: set V}:
  s ⊆ M.verts → is_antichain M.adj s → disjoint s (s.image hM.other) :=
begin
  intros hsub hanti,
  rw [set.disjoint_left],
  intros x hx hx',
  have hxM := set.mem_of_subset_of_mem hsub hx,
  exact is_antichain.not_mem hanti hx (hM.ne_of_mem hxM) (hM.other_adj hxM) (hM.other_image hx'),
end

theorem is_matching.delete_pair (hM: M.is_matching) (v: M.verts):
  (M.delete_verts {v, hM.other v}).is_matching :=
begin
  intros u hu,
  have hv : u ≠ v,
  by contrapose! hu; simp [hu],
  have hv' : u ≠ hM.other v,
  by contrapose! hu; simp [hu],
  have hMu := set.mem_of_mem_diff hu,
  rw [exists_unique_congr],
  apply hM hMu,
  simp [hv, hv', hMu,
    set.mem_diff, set.mem_insert_iff, set.mem_singleton_iff,
    induce_verts, induce_adj, delete_verts, hM.other_of_adj_iff',
    hM.other_inverse, hM.other_mem_verts, hM.other_inj_iff, hM.other_inj_iff',
    not_or_distrib]
end

theorem is_matching.is_matching_induce (hM: M.is_matching) {s: set V} (hs: s ⊆ M.verts):
  (∀ {v}, v ∈ s → ∃ u, u ∈ s ∧ M.adj v u) → (M.induce s).is_matching :=
begin
  intros h v hv,
  have hv' := set.mem_of_subset_of_mem hs hv,
  rw [exists_unique_congr],
  { exact hM hv' },
  refine λ x, ⟨ and.right ∘ and.right, λ hadj, ⟨ hv, _, hadj ⟩ ⟩,
  rcases h hv with ⟨u, hu, hadj'⟩,
  rwa [exists_unique.unique (hM hv') hadj hadj'],
end

theorem is_matching.exists_smaller (hM: M.is_matching) {c: cardinal} (hc: c ≤ cardinal.mk M.verts) (hc': even c):
  ∃ M': G.subgraph, M'.verts ⊆ M.verts ∧ cardinal.mk M'.verts = c ∧ M'.is_matching :=
begin
  cases hc' with d hd,
  rcases @set.cardinal_embedding _ hM.left d  _ with ⟨s, hcard, hsub⟩,
  refine ⟨M.induce (s ⊔ set.image hM.other s), _, _, _⟩,
  { simp only [set.union_subset_iff, set.image_subset_iff, set.sup_eq_union, simple_graph.subgraph.induce_verts],
    exact ⟨ set.subset.trans hsub hM.left_subset, λ x hx, hM.other_mem_verts (hM.left_mem (hsub hx)) ⟩ },
  { rwa [set.sup_eq_union, simple_graph.subgraph.induce_verts, cardinal.mk_union_of_disjoint, ← hM.other_card, hcard, @eq_comm _ _ c],
    exact hM.other_disjoint (subset_trans hsub hM.left_subset) (is_antichain.subset hM.left_is_antichain hsub) },
  { refine hM.is_matching_induce _ _,
    { exact λ v  hv, or.elim hv
        (set.mem_of_subset_of_mem (trans hsub hM.left_subset))
        (λ h, hM.other_mem_verts' (hM.other_image (set.mem_of_subset_of_mem
          (trans (set.image_subset hM.other hsub)
          (set.image_subset hM.other hM.left_subset)) h))),
    },
    { exact λ v hv, or.elim hv
      (λ hv, ⟨hM.other v, or.inr ((set.mem_image _ _ _).mpr ⟨_, hv, rfl⟩),
        hM.other_adj (set.mem_of_subset_of_mem (trans hsub hM.left_subset) hv) ⟩)
      (λ hv, ⟨hM.other v, or.inl (hM.other_image' hv),
        hM.other_adj (hM.other_mem_verts' (set.mem_of_subset_of_mem
          (trans hsub hM.left_subset) (hM.other_image' hv))) ⟩) },
  },
  { apply cardinal.nat_cast_left_mul_le_mul _ _ (show 0 < 2, by simp),
    simp only [algebra_map.coe_one, one_mul, coe_is_add_hom.coe_add, ← hd, add_mul, (show 2 = 1 + 1, by refl)],
    conv {
      to_rhs,
      congr,
      skip,
      rw [hM.other_card, ← hM.right_of_left],
    },
    rwa [← cardinal.mk_union_of_disjoint hM.left_right_disjoint, ← hM.left_right_total],
  },
end

structure alternating_path (p: path G u v) (M: G.subgraph): Prop :=
  (start_inv: u ∉ M.verts)
  (alt_inv: ∀ {x y z}, y ≠ z → (p:G.subgraph).adj x y → (p:G.subgraph).adj x z →
    (xor (M.adj x y) (M.adj x z)))

namespace alternating_path

theorem mem_verts (ap: alternating_path p M) {x: V}:
  x ∈ (p: G.subgraph).verts → u = x ∨ v = x ∨ x ∈ M.verts :=
begin
  simp only [p.coe_verts_iff_get_vert, exists_imp_distrib],
  intros n hn h,
  induction h,
  cases eq_or_lt_of_le hn with hn hn,
  { simp [hn] },
  cases n,
  { simp },
  right, right,
  cases ap.alt_inv _(walk.adj_get_vert_succ' _ hn) (walk.adj_get_vert_pred' _ (nat.zero_lt_succ _) (le_of_lt hn)),
  exact M.edge_vert h.left,
  exact M.edge_vert h.left,
  apply p.get_vert_inj_ne (nat.succ_le_of_lt hn) (trans (nat.sub_le _ _) (le_of_lt hn)),
  rw [nat.succ_sub_one, nat.succ_eq_add_one, nat.succ_eq_add_one],
  linarith,
end

-- theorem maintains_is_matching (ap: alternating_path p M):
--   M.is_matching → (M ∆ p).is_matching :=
-- begin
--   intro hM,
--   intro x,
--   intro hx,
--   by_cases x ∈ (p:G.subgraph).verts,
--   { rw [p.coe_verts_iff_get_vert] at h,
--     rcases h with ⟨n, hn, h⟩,
--     rw [← h],
--     cases eq_or_lt_of_le hn with hn hn,
--     { rw [hn, walk.get_vert_length],
--       exact subgraph.symm_diff_adj_unique_right' _ _ _ (λ _, not_imp_not.mpr M.edge_vert ap.end_inv) (p.end_unique_adj ap.not_nil) },
--     cases n,
--     { rw [walk.get_vert_zero],
--       exact subgraph.symm_diff_adj_unique_right' _ _ _ (λ _, not_imp_not.mpr M.edge_vert ap.start_inv) (p.start_unique_adj ap.not_nil) },
--     cases ap.alt_inv _ (walk.adj_get_vert_succ' _ hn) (walk.adj_get_vert_pred' _ (nat.zero_lt_succ _) (le_of_lt hn)),
--     { apply hM.unique_symm_diff
--       h_1.left h_1.right
--       (walk.adj_get_vert_succ' _ hn)
--       (walk.adj_get_vert_pred' _ (nat.zero_lt_succ _) (le_of_lt hn))
--       (λ _, p.neighbors' (le_of_lt hn)) },
--     { apply hM.unique_symm_diff
--         h_1.left h_1.right
--         (walk.adj_get_vert_pred' _ (nat.zero_lt_succ _) (le_of_lt hn))
--         (walk.adj_get_vert_succ' _ hn),
--       intro y,
--       simpa [or.comm] using p.neighbors' (le_of_lt hn) },
--     apply p.get_vert_inj_ne (nat.succ_le_of_lt hn) (trans (nat.sub_le _ _) (le_of_lt hn)),
--     rw [nat.succ_sub_one, nat.succ_eq_add_one, nat.succ_eq_add_one],
--     linarith },
--   { apply M.symm_diff_adj_unique_left' _ _ _ (hM (M.symm_diff_verts_not_right _ h hx)),
--     intro y,
--     contrapose! h,
--     exact subgraph.edge_vert _ h }
-- end

end alternating_path

structure augmenting_path (p: path G u v) (M: G.subgraph) extends alternating_path p M: Prop :=
  (not_nil: u ≠ v)
  (end_inv: v ∉ M.verts)

namespace augmenting_path

theorem mem_verts (ap: augmenting_path p M) {x: V}:
  x ∈ (p: G.subgraph).verts → u = x ∨ v = x ∨ x ∈ M.verts :=
begin
  simp only [p.coe_verts_iff_get_vert, exists_imp_distrib],
  intros n hn h,
  induction h,
  cases eq_or_lt_of_le hn with hn hn,
  { simp [hn] },
  cases n,
  { simp },
  right, right,
  cases ap.alt_inv _(walk.adj_get_vert_succ' _ hn) (walk.adj_get_vert_pred' _ (nat.zero_lt_succ _) (le_of_lt hn)),
  exact M.edge_vert h.left,
  exact M.edge_vert h.left,
  apply p.get_vert_inj_ne (nat.succ_le_of_lt hn) (trans (nat.sub_le _ _) (le_of_lt hn)),
  rw [nat.succ_sub_one, nat.succ_eq_add_one, nat.succ_eq_add_one],
  linarith,
end

theorem maintains_is_matching (ap: augmenting_path p M):
  M.is_matching → (M ∆ p).is_matching :=
begin
  intro hM,
  intro x,
  intro hx,
  by_cases x ∈ (p:G.subgraph).verts,
  { rw [p.coe_verts_iff_get_vert] at h,
    rcases h with ⟨n, hn, h⟩,
    rw [← h],
    cases eq_or_lt_of_le hn with hn hn,
    { rw [hn, walk.get_vert_length],
      exact subgraph.symm_diff_adj_unique_right' _ _ _ (λ _, not_imp_not.mpr M.edge_vert ap.end_inv) (p.end_unique_adj ap.not_nil) },
    cases n,
    { rw [walk.get_vert_zero],
      exact subgraph.symm_diff_adj_unique_right' _ _ _ (λ _, not_imp_not.mpr M.edge_vert ap.start_inv) (p.start_unique_adj ap.not_nil) },
    cases ap.alt_inv _ (walk.adj_get_vert_succ' _ hn) (walk.adj_get_vert_pred' _ (nat.zero_lt_succ _) (le_of_lt hn)),
    { apply hM.unique_symm_diff
      h_1.left h_1.right
      (walk.adj_get_vert_succ' _ hn)
      (walk.adj_get_vert_pred' _ (nat.zero_lt_succ _) (le_of_lt hn))
      (λ _, p.neighbors' (le_of_lt hn)) },
    { apply hM.unique_symm_diff
        h_1.left h_1.right
        (walk.adj_get_vert_pred' _ (nat.zero_lt_succ _) (le_of_lt hn))
        (walk.adj_get_vert_succ' _ hn),
      intro y,
      simpa [or.comm] using p.neighbors' (le_of_lt hn) },
    apply p.get_vert_inj_ne (nat.succ_le_of_lt hn) (trans (nat.sub_le _ _) (le_of_lt hn)),
    rw [nat.succ_sub_one, nat.succ_eq_add_one, nat.succ_eq_add_one],
    linarith },
  { apply M.symm_diff_adj_unique_left' _ _ _ (hM (M.symm_diff_verts_not_right _ h hx)),
    intro y,
    contrapose! h,
    exact subgraph.edge_vert _ h }
end

theorem or_of_not_and {p q: Prop}: (¬ p ∧ q) → p ∨ q := by tauto

theorem augmented_verts (ap: augmenting_path p M):
  (M ∆ p).verts = insert u (insert v M.verts) :=
begin
  simp only [symm_diff_verts, set.ext_iff, coe_coe, set.mem_insert_iff],
  intro x,
  split; intro h,
  { cases h,
    { exact or.inr (or.inr h) },
    { simpa only [@eq_comm _ x] using ap.mem_verts h } },
  obtain h|h|h := h;
  { simp [h] },
end

theorem augmented_cardinality (ap: augmenting_path p M):
  cardinal.mk (M ∆ p).verts = (cardinal.mk M.verts) + 2 :=
begin
  rw [ap.augmented_verts, cardinal.mk_insert, cardinal.mk_insert ap.end_inv],
  { ring },
  rw [set.mem_insert_iff, not_or_distrib],
  exact ⟨ap.not_nil, ap.start_inv⟩,
end
end augmenting_path

-- theorem bergs_lemma_helper
--   (M: G.subgraph) [finset M.verts]


-- theorem is_matching.bergs_lemma_helper
--     (hM: is_matching M) (n: ℕ) (hn: cardinal.mk M.verts = 2 * n) {N: subgraph G} (hN: is_matching N):
--     ∀ (u: V), u ∉ M.verts → u ∈ N.verts → ∃ (v: V) (p: path G u v), augmenting_path p M :=
-- begin
--   induction n generalizing M N,
--   { simp only [algebra_map.coe_zero, nat.nat_zero_eq_zero, mul_zero, cardinal.mk_emptyc_iff] at hn,
--     intros u huM huN,
--     refine ⟨ hN.other u, path.singleton (N.adj_sub (hN.other_adj huN)), hN.ne_of_mem huN, huM, _, _⟩,
--     { simp only [hn, set.mem_empty_iff_false, not_false_iff] },
--     intros x y z hyz,
--     unfold_coes,
--     unfold walk.to_subgraph,
--     simp,
--     intros hxy hxz,
--     exfalso,
--     cases hxy;
--     simp only [hxy, hN.ne_of_mem huN, (hN.ne_of_mem huN).symm,
--       false_and, or_false, false_or, eq_self_iff_true, true_and] at hxz;
--     apply hyz;
--     rw [hxy.right, hxz] },
--   intros u huM huN,
--   by_cases huM': hN.other u ∈ M.verts,
--   { specialize n_ih (hM.delete_pair ⟨_, huM'⟩) _ (hN.delete_pair ⟨_, huN⟩) (hM.other (hN.other)),
    

--   },
--   { refine ⟨ hN.other u, path.singleton (N.adj_sub (hN.other_adj huN)), hN.ne_of_mem huN, huM, huM', _⟩,
--     intros x y z hyz,
--     unfold_coes,
--     unfold walk.to_subgraph,
--     simp,
--     intros hxy hxz,
--     exfalso,
--     cases hxy;
--     simp only [hxy, hN.ne_of_mem huN, (hN.ne_of_mem huN).symm,
--       false_and, or_false, false_or, eq_self_iff_true, true_and] at hxz;
--     apply hyz;
--     rw [hxy.right, hxz]
--   },
-- end

-- theorem is_matching.bergs_lemma (hM: is_matching M) (hf: cardinal.mk M.verts < cardinal.aleph_0):
--   (∃ {u v: V} (p: path G u v), augmenting_path p M) ↔ ¬ hM.is_maximal :=
-- begin
--   simp only [is_matching.is_maximal, not_forall, not_le],
--   split,
--   { intro h,
--     rcases h with ⟨u, v, p, ap⟩,
--     use ap.augmented_subgraph,
--     refine ⟨ ap.maintains_is_matching hM, _⟩,
--     rw [augmenting_path.augmented_cardinality],
--     cases cardinal.lt_aleph_0.mp hf with n hn,
--     rw [eq_comm] at hn,
--     induction hn,
--     rw [← nat.cast_two, ← cardinal.nat_cast_add, cardinal.nat_cast_lt],
--     simp },
--   { rw[cardinal.lt_aleph_0] at hf,
--     intro h,
--     rcases h with ⟨N, hN, h⟩,
--     cases hf with n hn,
--     have hn' := hN.exists_smaller _ _,


--   }
-- end

end subgraph
end simple_graph