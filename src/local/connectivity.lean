import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.matching
import local.set
import local.subgraph

namespace simple_graph
variables {V : Type*} {G : simple_graph V} {M : G.subgraph}
variables {u v : V}
variables {p: path G u v}

def walk.to_subgraph (w: walk G u v): G.subgraph :=
 { verts := {v |  v ∈ w.support},
   adj := (λ x y, ⟦(x, y)⟧ ∈ w.edges),
   adj_sub := λ x y, walk.adj_of_mem_edges w,
   edge_vert := λ x y, w.fst_mem_support_of_mem_edges,
   symm := by simp [symmetric, sym2.eq_swap] }

instance : has_coe (walk G u v) (G.subgraph) := ⟨ walk.to_subgraph ⟩

theorem walk.length_pos_of_ne (w: walk G u v): u ≠ v → 0 < w.length :=
by cases w; simp

theorem walk.nth_le_support_iff_get_vert (w: walk G u v) {n: ℕ} (hn: n < w.support.length):
  w.support.nth_le n hn = w.get_vert n :=
begin
  induction w generalizing n,
  { simp [walk.get_vert] },
  cases n,
  { simp [walk.get_vert] },
  simpa [walk.get_vert] using w_ih _
end

theorem walk.nth_le_edge (w: walk G u v) {n : ℕ} (hn: n < w.edges.length):
  w.edges.nth_le n hn = ⟦ (w.get_vert n, w.get_vert (n + 1)) ⟧ :=
begin
  induction w generalizing n,
  { cases hn },
  cases n,
  { simp [walk.get_vert] },
  simpa [walk.get_vert] using w_ih _
end

theorem walk.mem_support_iff_coe_verts (w: walk G u v) (x: V):
  x ∈ w.support ↔ x ∈ (w:G.subgraph).verts := by refl

theorem walk.coe_verts_iff_get_vert (w: walk G u v) (x: V):
  x ∈ (w:G.subgraph).verts ↔ ∃ n ≤ w.length, w.get_vert n = x :=
by simp only [← walk.mem_support_iff_coe_verts, list.mem_iff_nth_le,
    walk.nth_le_support_iff_get_vert, walk.length_support, nat.lt_succ_iff]

@[simp]
theorem walk.start_mem_coe_verts (w: walk G u v):
  u ∈ (w:G.subgraph).verts := by simp [← w.mem_support_iff_coe_verts]

@[simp]
theorem walk.end_mem_coe_verts (w: walk G u v):
  v ∈ (w:G.subgraph).verts := by simp [← w.mem_support_iff_coe_verts]

theorem walk.mem_edges_iff_coe_adj (w: walk G u v) (x y: V):
  ⟦(x, y)⟧ ∈ w.edges ↔ (w:G.subgraph).adj x y := by refl

theorem walk.adj_get_vert_succ' (w: walk G u v) {n: ℕ} (hn: n < w.length):
  (w:G.subgraph).adj (w.get_vert n) (w.get_vert (n+1)) :=
begin
  induction w generalizing n,
  { cases hn },
  cases n,
  { simp [walk.get_vert, walk.get_vert_zero, ← walk.mem_edges_iff_coe_adj] },
  simpa [walk.get_vert, walk.get_vert_zero, ← walk.mem_edges_iff_coe_adj]
    using or.inr (w_ih (nat.succ_lt_succ_iff.mp hn))
end

theorem walk.adj_succ_get_vert' (w: walk G u v) {n: ℕ} (hn: n < w.length):
  (w:G.subgraph).adj (w.get_vert (n+1)) (w.get_vert n) :=
  (w:G.subgraph).adj_symm (w.adj_get_vert_succ' hn)


theorem walk.adj_get_vert_pred' (w: walk G u v) {n: ℕ} (hn₀: 0 < n) (hn₁: n ≤ w.length):
  (w:G.subgraph).adj (w.get_vert n) (w.get_vert (n-1)) :=
begin
  cases n,
  { cases hn₀ },
  simpa [nat.succ_eq_add_one] using w.adj_succ_get_vert' (nat.lt_of_succ_le hn₁)
end

lemma walk.coe_fst_mem_verts_of_adj (w : G.walk u v) {x y: V}:
  (w:G.subgraph).adj x y → x ∈ (w:G.subgraph).verts :=
begin
  rw [← w.mem_support_iff_coe_verts, ← w.mem_edges_iff_coe_adj],
  exact w.fst_mem_support_of_mem_edges
end

theorem path.get_vert_inj (p: path G u v) {n m: ℕ} (hn: n ≤ (p:walk G u v).length) (hm: m ≤ (p:walk G u v).length):
  (p:walk G u v).get_vert n = (p:walk G u v).get_vert m → n = m :=
begin
  rw [← nat.lt_succ_iff, nat.succ_eq_add_one, ← walk.length_support] at hn hm,
  simp [← (p:walk G u v).nth_le_support_iff_get_vert hn,
    ← (p:walk G u v).nth_le_support_iff_get_vert hm,
    list.nodup.nth_le_inj_iff p.nodup_support]
end

theorem path.get_vert_inj_ne (p: path G u v) {n m: ℕ} (hn: n ≤ (p:walk G u v).length) (hm: m ≤ (p:walk G u v).length):
  n ≠ m → (p:walk G u v).get_vert n ≠ (p:walk G u v).get_vert m :=
by simpa [not_imp_not] using p.get_vert_inj hn hm

theorem path.get_vert_inj_iff (p: path G u v) {n m: ℕ} (hn: n ≤ (p:walk G u v).length) (hm: m ≤ (p:walk G u v).length):
  (p:walk G u v).get_vert n = (p:walk G u v).get_vert m ↔ n = m :=
  ⟨ p.get_vert_inj hn hm, congr_arg _ ⟩

theorem path.coe_verts_iff_get_vert (p: path G u v) (x: V):
  x ∈ (p:G.subgraph).verts ↔ ∃ n ≤ (p:walk G u v).length, (p:walk G u v).get_vert n = x :=
  walk.coe_verts_iff_get_vert (p:walk G u v) x

theorem path.mem_edges_iff_coe_adj (p: path G u v) (x y: V):
  ⟦(x, y)⟧ ∈ (p:walk G u v).edges ↔ (p:G.subgraph).adj x y := by refl

theorem path.neighbors (p: path G u v) {n: ℕ} (hn: n ≤ (p:walk G u v).length) {x: V}:
  (p:G.subgraph).adj ((p:walk G u v).get_vert n) x →
    n < (p:walk G u v).length ∧ ((p:walk G u v).get_vert (n + 1)) = x ∨
    0 < n  ∧ ((p:walk G u v).get_vert (n - 1)) = x :=
begin
  simp only [← p.mem_edges_iff_coe_adj, walk.length_edges, walk.nth_le_edge,
    list.mem_iff_nth_le, sym2.rel_iff, quotient.eq],
  intros h,
  rcases h with ⟨m, hm, h⟩,
  cases h,
  { rw [← p.get_vert_inj (le_of_lt hm) hn h.left],
    exact or.inl ⟨hm, h.right⟩ },
  { rw [← p.get_vert_inj (nat.succ_le_of_lt hm) hn h.right, nat.succ_sub_one],
    exact or.inr ⟨nat.zero_lt_succ _, h.left⟩ }
end

theorem path.neighbors' (p: path G u v) {n: ℕ} (hn: n ≤ (p:walk G u v).length) {x: V}:
  (p:G.subgraph).adj ((p:walk G u v).get_vert n) x →
    ((p:walk G u v).get_vert (n + 1)) = x ∨
    ((p:walk G u v).get_vert (n - 1)) = x :=
begin
  intro hadj,
  cases p.neighbors hn hadj,
  exact or.inl h.right,
  exact or.inr h.right
end

theorem path.start_unique_adj (p: path G u v) (hne: u ≠ v):
  ∃! x, (p:G.subgraph).adj u x :=
begin
  simp only [← (p:walk G u v).get_vert_zero],
  refine ⟨(p:walk G u v).get_vert 1, walk.adj_get_vert_succ' _ (walk.length_pos_of_ne _ hne), _⟩,
  intros y hy,
  cases p.neighbors (nat.zero_le _) hy,
  { exact h.right.symm },
  { cases h.left }
end

theorem path.end_unique_adj (p: path G u v) (hne: u ≠ v):
  ∃! x, (p:G.subgraph).adj v x :=
begin
  simp only [← (p:walk G u v).get_vert_length],
  refine ⟨(p:walk G u v).get_vert ((p:walk G u v).length -1),
    walk.adj_get_vert_pred' _ (walk.length_pos_of_ne _ hne) (le_refl _),
    _⟩,
  intros y hy,
  cases p.neighbors (le_refl _) hy,
  { exact absurd h.left (lt_irrefl _) },
  { exact h.right.symm }
end

end simple_graph