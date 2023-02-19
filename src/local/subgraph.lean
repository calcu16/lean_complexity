import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.matching
import set_theory.cardinal.basic
import set_theory.cardinal.finite
import set_theory.cardinal.ordinal
import local.cardinal
import local.set
universe univ

namespace simple_graph
namespace subgraph
variables {V : Type univ} {G : simple_graph V} {M : G.subgraph}

noncomputable
theorem to_simple_graph (M: G.subgraph): simple_graph V :=
 { adj := M.adj, symm := @adj_symm _ _ M, loopless := M.loopless }
 

theorem ne_of_adj (M: G.subgraph) {u v: V}: M.adj u v → u ≠ v :=
begin
  intros hadj heq,
  rw [heq] at hadj,
  exact M.loopless _ hadj,
end

@[simp]
theorem sup_verts (M N: G.subgraph):
  (M ⊔ N).verts =  M.verts ⊔ N.verts := by refl

@[simp]
theorem sup_adj_iff (M N: G.subgraph) (u v: V):
  (M ⊔ N).adj u v ↔ M.adj u v ∨ N.adj u v := by refl

theorem sub_adj_unique_iff_not_left (M N: G.subgraph) {u: V} (hu: u ∉ M.verts):
  (∃! v, (M ⊔ N).adj u v) ↔ ∃! v, N.adj u v :=
by simp [(not_imp_not.mpr M.edge_vert) hu]

theorem sub_adj_unique_iff_not_right (M N: G.subgraph) {u: V} (hu: u ∉ N.verts):
  (∃! v, (M ⊔ N).adj u v) ↔ ∃! v, M.adj u v :=
by simp [(not_imp_not.mpr N.edge_vert) hu]

def sdiff (s t: G.subgraph): G.subgraph := s.delete_edges t.edge_set

instance: has_sdiff (G.subgraph) := ⟨ sdiff ⟩
  
@[simp]
theorem sdiff_verts (M N: G.subgraph):
  (M \ N).verts = M.verts :=
by simp [has_sdiff.sdiff, sdiff]

@[simp]
theorem sdiff_adj_iff (M N: G.subgraph) (u v: V):
  (M \ N).adj u v ↔ M.adj u v ∧ ¬ N.adj u v := by refl

@[simp]
theorem symm_diff_verts (M N: G.subgraph):
  (M ∆ N).verts = M.verts ⊔ N.verts := begin
  simp [symm_diff, sdiff]
end

theorem symm_diff_verts_not_left (M N: G.subgraph) {v: V} (h: v ∉ M.verts):
  v ∈ (M ∆ N).verts → v ∈ N.verts := by simp[h]

theorem symm_diff_verts_not_right (M N: G.subgraph) {v: V} (h: v ∉ N.verts):
  v ∈ (M ∆ N).verts → v ∈ M.verts := by simp[h]

@[simp]
theorem symm_diff_adj_iff (M N: G.subgraph) (u v: V):
  (M ∆ N).adj u v ↔ xor (M.adj u v) (N.adj u v) := by simp [symm_diff, xor]

theorem symm_diff_adj_unique_left (M N: G.subgraph) (u: V) (hN: ∀ v, ¬ (N \ M).adj u v):
  (∃! v, (M \ N).adj u v) → ∃! v, (M ∆ N).adj u v := by simp [symm_diff, hN]

theorem symm_diff_adj_unique_left' (M N: G.subgraph) (u: V) (hN: ∀ v, ¬ N.adj u v):
  (∃! v, M.adj u v) → ∃! v, (M ∆ N).adj u v := by simp [symm_diff, hN]

theorem symm_diff_adj_unique_right (M N: G.subgraph) (u: V) (hM: ∀ v, ¬ (M \ N).adj u v):
  (∃! v, (N \ M).adj u v) → ∃! v, (M ∆ N).adj u v := by simp [symm_diff, hM]

theorem symm_diff_adj_unique_right' (M N: G.subgraph) (u: V) (hM: ∀ v, ¬ M.adj u v):
  (∃! v, N.adj u v) → ∃! v, (M ∆ N).adj u v := by simp [hM]

lemma degree_eq_one_iff_unique_adj' {G' : G.subgraph} {v : V}:
  cardinal.mk (G'.neighbor_set v) = 1 ↔ ∃! (w : V), G'.adj v w :=
by simp [cardinal.eq_one_iff_exists_unique, set_coe.exists_unique, mem_neighbor_set]

end subgraph
end simple_graph