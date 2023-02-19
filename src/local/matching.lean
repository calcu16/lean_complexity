import set_theory.cardinal.basic
import local.cardinal
import local.subgraph
universe univ

namespace simple_graph
namespace subgraph
variables {V : Type univ} {G : simple_graph V} {M : G.subgraph}
variables {u v : V}
variables {p: path G u v}


lemma is_matching_iff_forall_degree' {M : G.subgraph}:
  M.is_matching ↔ ∀ (v : V), v ∈ M.verts → cardinal.mk (M.neighbor_set v) = 1 :=
by simpa [degree_eq_one_iff_unique_adj']

theorem is_matching.of_adj (huv: G.adj u v): (G.subgraph_of_adj huv).is_matching :=
by simp [is_matching, G.ne_of_adj huv, (G.ne_of_adj huv).symm]

theorem is_matching.unique_edge {M: subgraph G} (hM: M.is_matching) {v: V}:
  ∀ {e₁ e₂}, e₁ ∈ M.edge_set → e₂ ∈ M.edge_set → v ∈ e₁ → v ∈ e₂ → e₁ = e₂ :=
begin
  simp only [sym2.forall, mem_edge_set],
  intros x₁ y₁,
  simp only [sym2.forall, mem_edge_set, sym2.mem_iff],
  intros x₂ y₂ hxy₁ hxy₂ hv₁ hv₂,
  cases hv₁ with hv₁ hv₁;
  cases hv₂ with hv₂ hv₂;
  induction hv₁;
  induction hv₂;
  simp only [
    M.ne_of_adj hxy₁, (M.ne_of_adj hxy₁).symm,
    M.ne_of_adj hxy₂, (M.ne_of_adj hxy₂).symm,
    true_and, and_true, and_false, or_false, false_or,
    eq_self_iff_true,
    sym2.rel_iff, quotient.eq],
  exact exists_unique.unique (hM (M.edge_vert hxy₁)) hxy₁ hxy₂,
  exact exists_unique.unique (hM (M.edge_vert hxy₁)) hxy₁ (M.adj_symm hxy₂),
  exact exists_unique.unique (hM (M.edge_vert (M.adj_symm hxy₁))) (M.adj_symm hxy₁) hxy₂,
  exact exists_unique.unique (hM (M.edge_vert (M.adj_symm hxy₁))) (M.adj_symm hxy₁) (M.adj_symm hxy₂),
end

noncomputable def is_matching.other {M : subgraph G} (hM : M.is_matching)
  (v: V): V := begin
  classical,
  exact dite (v ∈ M.verts) (λ h, (hM h).some) (λ _, v),
end

theorem is_matching.other_adj {M: subgraph G} (hM: M.is_matching) {v: V} (hv: v ∈ M.verts):
  M.adj v (hM.other v) :=
by simpa [is_matching.other, hv] using (hM hv).some_spec.1


theorem is_matching.other_adj' {M: subgraph G} (hM: M.is_matching) {v: V} (hv: v ∈ M.verts):
  M.adj (hM.other v) v := M.adj_symm (hM.other_adj hv)

theorem is_matching.other_of_adj {M: subgraph G} (hM: M.is_matching) {u v: V} (h: M.adj u v):
  hM.other u = v := exists_unique.unique (hM (M.edge_vert h)) (hM.other_adj (M.edge_vert h)) h

theorem is_matching.other_of_adj' {M: subgraph G} (hM: M.is_matching) {u v: V} (h: M.adj u v):
  u = hM.other v := eq.symm (hM.other_of_adj (M.adj_symm h))

theorem is_matching.ne_of_mem {M: subgraph G} (hM: M.is_matching) {v: V} (hv: v ∈ M.verts):
  v ≠ (hM.other v) := M.ne_of_adj (hM.other_adj hv)

theorem is_matching.other_id {M: subgraph G} (hM: M.is_matching) {v: V} (hv: v ∉ M.verts):
  hM.other v = v :=
by simp [is_matching.other, hv]

theorem is_matching.other_adj_iff {M: subgraph G} (hM: M.is_matching) {v: V}:
  (v ∈ M.verts) ↔ M.adj v (hM.other v) :=
begin
  refine ⟨ hM.other_adj, _ ⟩,
  contrapose!,
  intro h,
  rw [hM.other_id h],
  exact M.loopless _,
end

theorem is_matching.other_of_adj_iff {M: subgraph G} (hM: M.is_matching) {v u: V} (hv: v ∈ M.verts):
  M.adj u v ↔ u = (hM.other v) := ⟨ λ h, hM.other_of_adj'  h, λ h, h.symm ▸ (hM.other_adj' hv) ⟩

theorem is_matching.other_of_adj_iff' {M: subgraph G} (hM: M.is_matching) {v u: V} (hv: v ∈ M.verts):
  M.adj v u ↔ u = (hM.other v) := (eq_iff_iff.mpr (M.adj_comm u v)) ▸ hM.other_of_adj_iff hv

theorem is_matching.other_id_iff {M: subgraph G} (hM: M.is_matching) (v: V):
  (v ∉ M.verts) ↔ hM.other v = v :=
begin
  refine ⟨ hM.other_id, _ ⟩,
  contrapose!,
  intros hmem heq,
  apply M.loopless v,
  conv { congr, skip, skip, rw [← heq] },
  exact hM.other_adj hmem
end

theorem is_matching.other_id_iff' {M: subgraph G} (hM: M.is_matching) (v: V):
  (v ∉ M.verts) ↔ v = hM.other v:= by rw[hM.other_id_iff v, eq_comm]

@[simp]
theorem is_matching.other_subtype_ne {M: subgraph G} (hM: M.is_matching) {v: V} (hv: v ∈ M.verts):
  v ≠ (hM.other v) := by simpa [← is_matching.other_id_iff'] using hv

@[simp]
theorem is_matching.other_subtype_ne' {M: subgraph G} (hM: M.is_matching) {v: V} (hv: v ∈ M.verts):
  (hM.other v) ≠ v := ne.symm (hM.other_subtype_ne hv)

theorem is_matching.other_mem_verts {M: subgraph G} (hM: M.is_matching) {v: V} (hv: v ∈ M.verts):
  (hM.other v) ∈ M.verts := M.edge_vert (M.adj_symm (hM.other_adj hv))


theorem is_matching.other_inverse {M: subgraph G} (hM: M.is_matching) (v: V):
  hM.other (hM.other v) = v :=
begin
  by_cases v ∈ M.verts,
  { exact exists_unique.unique
      (hM (hM.other_mem_verts h))
      (hM.other_adj (hM.other_mem_verts h))
      (M.adj_symm (hM.other_adj h)) },
  { rw [hM.other_id h, hM.other_id h] }
end

theorem is_matching.other_mem_verts' {M: subgraph G} (hM: M.is_matching) {v: V} (hv: hM.other v ∈ M.verts):
  v ∈ M.verts := hM.other_inverse v ▸ M.edge_vert (hM.other_adj' hv)

theorem is_matching.other_inj_iff {M: subgraph G} (hM: M.is_matching) (u v: V):
  hM.other u = hM.other v ↔ u = v := ⟨ λ p, by rw [← hM.other_inverse u, p, hM.other_inverse v], congr_arg _ ⟩

theorem is_matching.other_inj_iff' {M: subgraph G} (hM: M.is_matching) (u v: V):
  hM.other u = v ↔ u = hM.other v :=
by conv_lhs { rw [← hM.other_inj_iff, hM.other_inverse] }

theorem is_matching.other_image {M: subgraph G} (hM: M.is_matching) {v: V} {s: set V}:
  v ∈ s.image hM.other → hM.other v ∈ s :=
by simp [set.mem_image, hM.other_inj_iff']  

theorem is_matching.other_image' {M: subgraph G} (hM: M.is_matching) {v: V} {s: set V}:
  v ∈ s.image hM.other → hM.other v ∈ s :=
by simp [set.mem_image, hM.other_inj_iff']  

theorem is_matching.edge_of_other {M: subgraph G} (hM: M.is_matching) {v: V} {e: sym2 V} (hv: hM.other v ∈ e) (he: e ∈ M.edge_set):
  v ∈ e :=
begin
  revert e,
  simp only [sym2.forall, sym2.mem_iff, mem_edge_set],
  intros x y hv hxy,
  cases hv;
  induction hv;
  rw [← hM.other_inverse v],
  exact or.inr (hM.other_of_adj hxy),
  exact or.inl (hM.other_of_adj' hxy).symm,
end

theorem is_matching.other_unique_edge {M: subgraph G} (hM: M.is_matching) {v: V}:
  ∀ {e₁ e₂}, e₁ ∈ M.edge_set → e₂ ∈ M.edge_set → v ∈ e₁ → hM.other v ∈ e₂ → e₁ = e₂ :=
begin
  simp only [sym2.forall, mem_edge_set],
  intros x₁ y₁,
  simp only [sym2.forall, mem_edge_set, sym2.mem_iff],
  intros x₂ y₂ hxy₁ hxy₂ hv₁ hv₂,
  have hxy₁' := hM.other_of_adj hxy₁,
  have hxy₂' := hM.other_of_adj hxy₂,
  cases hv₁ with hv₁ hv₁;
  cases hv₂ with hv₂ hv₂;
  induction hv₁;
  induction hv₂;
  simp only [hM.other_inj_iff, hM.other_inverse, hM.other_inj_iff', @eq_comm _ v] at hxy₁' hxy₂';
  induction hxy₁';
  induction hxy₂';
  try { refl };
  exact sym2.eq_swap,
end


theorem is_matching.unique_symm_diff (hM: M.is_matching) {N: G.subgraph} {x y z: V}:
  (M.adj x y) → (¬ M.adj x z) → N.adj x y → N.adj x z → (∀ {v}, N.adj x v → y = v ∨ z = v) →
  ∃! v, (M ∆ N).adj x v :=
begin
  intros hmxy hmxz hnxy hnxz hn,
  apply symm_diff_adj_unique_right,
  { simp only [subgraph.sdiff_adj_iff, not_and, not_not],
    intros u hu,
    rwa [(hM (M.edge_vert hmxy)).unique hu hmxy] },
  refine ⟨z, ⟨hnxz, hmxz⟩, _,⟩,
  simp only [subgraph.sdiff_adj_iff, not_and, not_not, and_imp],
  intros u hnu hmu,
  cases hn hnu,
  { induction h,
    contradiction },
  { rw [h] }
end

def is_matching.is_maximum (m: M.is_matching) :=
  ∀ M': G.subgraph, M'.is_matching → cardinal.mk M'.verts ≤ cardinal.mk M.verts

end subgraph
end simple_graph