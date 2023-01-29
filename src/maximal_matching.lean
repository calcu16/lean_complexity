
import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.matching
universe u

namespace simple_graph
variables {V : Type u} {G : simple_graph V} {M : subgraph G}
variables {u v : V}

namespace subgraph

def is_maximal_matching (M: subgraph G) (m: M.is_matching) :=
  ∀ M' : subgraph G, M'.is_matching → ∃ f : M'.verts → M.verts, f.injective

def alternating_path (p: path G u v) (M: subgraph G) :=
  u ∉ M.verts ∧ ∀ x y z : V,
    ⟦(x, y)⟧ ∈ (p:walk G u v).edges → ⟦(x, z)⟧ ∈ (p:walk G u v).edges → y ≠ z →
    (M.adj x y ↔ ¬ M.adj x z)

def augmenting_path (p: path G u v) (M: subgraph G) :=
  v ∉ M.verts ∧ alternating_path p M 


end subgraph

-- lemma walk.support_get_vert (w: walk G u v) {n: ℕ} (hn: n < w.support.length):
--   w.support.nth_le n hn = w.get_vert n :=
-- begin
--   induction w generalizing n,
--   { simp [walk.get_vert] },
--   cases n,
--   { simp [walk.get_vert] },
--   { simpa [walk.get_vert] using w_ih _ }
-- end

-- lemma walk.edge_vertex_iff (w: walk G u v) {n: ℕ} (hn: n < w.edges.length) (x y: V):
--   w.edges.nth_le n hn = ⟦(x, y)⟧ ↔
--     w.get_vert n = x ∧ w.get_vert (n+1) = y ∨
--     w.get_vert n = y ∧ w.get_vert (n+1) = x :=
-- begin
--   induction w generalizing n,
--   { revert hn, simp },
--   cases n,
--   { simp [walk.get_vert] },
--   { simpa [walk.get_vert, nat.succ_eq_add_one] using w_ih _ }
-- end

-- lemma walk.edge_mem_iff (w: walk G u v) (x y: V):
--   ⟦(x, y)⟧ ∈ w.edges ↔ ∃ (n < w.length),
--     w.get_vert n = x ∧ w.get_vert (n+1) = y ∨
--     w.get_vert n = y ∧ w.get_vert (n+1) = x :=
-- by simp only [list.mem_iff_nth_le, walk.edge_vertex_iff, w.length_edges]

-- lemma path.nil_of_zero_length (p: path G u v): (p:walk G u v).length = 0 → u = v :=
-- by cases p; cases p_val; simp

-- lemma path.pos_length_of_ne (p: path G u v): u ≠ v → 0 < (p:walk G u v).length :=
-- by cases p; cases p_val; simp

-- lemma path.get_vert_inj_iff (p: path G u v) {n m: ℕ} (hn: n ≤ (p:walk G u v).length) (hm: m ≤ (p:walk G u v).length):
--   (p:walk G u v).get_vert n = (p:walk G u v).get_vert m ↔ n = m :=
-- begin
--   have hn := nat.lt_succ_of_le hn,
--   have hm := nat.lt_succ_of_le hm,
--   rw [nat.succ_eq_add_one, ← walk.length_support] at hn hm,
--   rw [← (p:walk G u v).support_get_vert hn, ← (p:walk G u v).support_get_vert hm],
--   exact list.nodup.nth_le_inj_iff p.nodup_support _ _
-- end


-- lemma path.get_vert_inj (p: path G u v) {n m: ℕ} (hn: n ≤ (p:walk G u v).length) (hm: m ≤ (p:walk G u v).length):
--   (p:walk G u v).get_vert n = (p:walk G u v).get_vert m → n = m := (p.get_vert_inj_iff hn hm).mp

-- lemma path.get_vert_inj_left_iff (p: path G u v) {n: ℕ} (hn: n < (p:walk G u v).length) (m: ℕ):
--   (p:walk G u v).get_vert n = (p:walk G u v).get_vert m ↔ n = m :=
-- begin
--   by_cases hm: m < (p:walk G u v).length,
--   exact p.get_vert_inj_iff (le_of_lt hn) (le_of_lt hm),
--   simp only [(p:walk G u v).get_vert_of_length_le (le_of_not_lt hm),
--     ← (p:walk G u v).get_vert_length,
--     p.get_vert_inj_iff (le_of_lt hn) (le_refl _),
--     ne_of_lt hn, false_iff],
--   linarith,
-- end

-- lemma path.get_vert_inj_right_iff (p: path G u v) (n: ℕ) {m: ℕ} (hm: m < (p:walk G u v).length):
--   (p:walk G u v).get_vert n = (p:walk G u v).get_vert m ↔ n = m :=
-- begin
--   rw [eq_comm, @eq_comm ℕ],
--   exact p.get_vert_inj_left_iff hm _
-- end

-- lemma path.edge_mem_iff (p: path G u v) (x y: V):
--   ⟦(x, y)⟧ ∈ (p:walk G u v).edges ↔ ∃! (n < (p:walk G u v).length),
--     (p:walk G u v).get_vert n = x ∧ (p:walk G u v).get_vert (n+1) = y ∨
--     (p:walk G u v).get_vert n = y ∧ (p:walk G u v).get_vert (n+1) = x :=
-- begin
--   split,
--   { simp only [(p:walk G u v).edge_mem_iff, exists_unique_iff_exists],
--     intro h,
--     rcases h with ⟨n, hn, h⟩,
--     refine ⟨n, ⟨hn, h⟩, _⟩,
--     intros z hz,
--     cases hz with hz h',
--     cases h; cases h';
--     try { exfalso,
--       rw [← h.left, ← h.right, p.get_vert_inj_left_iff hz, p.get_vert_inj_right_iff _ hn] at h',
--       apply (show n ≠ n + 1 + 1, by linarith),
--       rw [← h'.left, h'.right] };
--     simp [← p.get_vert_inj_iff (le_of_lt hz) (le_of_lt hn), h, h'] },
--   simpa [(p:walk G u v).edge_mem_iff] using exists_of_exists_unique,
-- end

-- lemma path.edge_mem_vertex_iff (p: path G u v) (x y: V) (hne: u ≠ v):
--   ⟦(x, y)⟧ ∈ (↑p:walk G u v).edges → ∃! (n ≤ (↑p:walk G u v).length), (↑p:walk G u v).get_vert n = x :=
-- begin
--   intro h,




  
-- end


-- lemma path.edge_mem_vertex_iff (p: path G u v) (x y: V):
--   u ≠ v → ⟦(x, y)⟧ ∈ (↑p:walk G u v).edges ↔ ∃! n, (↑p:walk G u v).get_vert n = x :=
-- begin
  
-- end

-- lemma path.head_unique_edge (p: path G u v): u ≠ v →  ∃! (w : V), ⟦(u, w)⟧ ∈ p.val.edges :=
-- begin
--   cases p with w hp,
--   cases w with u _ x _ hux hxv,
--   { simp },
--   simp only [simple_graph.walk.cons_is_path_iff] at hp,
--   have huv: u ≠ v,
--   { cases hp with _ hp,
--     contrapose! hp,
--     rw [hp],
--     apply hxv.end_mem_support },
--   have hux': u ≠ x,
--   { by_contra,
--     rw [h] at hux,
--     exact G.loopless _ hux,
--   },
--   simp [huv, hux', not_imp_not.mpr hxv.fst_mem_support_of_mem_edges hp.right],
-- end

-- lemma path.get_vert_inj_iff (p: path G u v) (n m: ℕ) (hn: n ≤ p.val.length) (hm: m ≤ p.val.length):
--   p.val.get_vert n = p.val.get_vert m ↔ n = m :=
-- begin
--   simpa only [← p.val.support_get_vert (p.val.lt_length_support hn), ← p.val.support_get_vert (p.val.lt_length_support hm)]
--     using list.nodup.nth_le_inj_iff p.property.support_nodup _ _
-- end

-- lemma path.get_vert_inj_iff_left (p: path G u v) (n m: ℕ) (hn: n < p.val.length):
--   p.val.get_vert n = p.val.get_vert m ↔ n = m :=
-- begin
--   by_cases hm: m ≤ p.val.length,
--   exact p.get_vert_inj_iff n m (le_of_lt hn) hm,
--   simp only [p.val.get_vert_of_length_le (le_of_not_le hm), ← p.val.get_vert_length,
--     p.get_vert_inj_iff n p.val.length (le_of_lt hn) (le_refl _),
--     show n ≠ p.val.length, by linarith,
--     show n ≠ m, by linarith],
-- end

-- lemma path.get_vert_inj_iff_right (p: path G u v) (n m: ℕ) (hm: m < p.val.length):
--   p.val.get_vert n = p.val.get_vert m ↔ n = m :=
-- begin
--   rw [eq_comm, @eq_comm _ n],
--   exact p.get_vert_inj_iff_left m n hm
-- end

-- lemma path.mem_neighbor_cases (p: path G u v) {n: ℕ} (pos: 0 < n) (hn: n < p.val.length) (x: V):
--   ⟦(p.val.get_vert n, x)⟧ ∈ p.val.edges ↔ p.val.get_vert (n + 1) = x ∨ p.val.get_vert (n - 1) = x :=
-- begin
--   cases n,
--   { revert pos, simp },
--   rw [nat.succ_eq_add_one] at hn,
--   simp only [list.mem_iff_nth_le, p.val.length_edges,
--     p.val.edge_vertex_iff, exists_or_distrib, nat.succ_eq_add_one,
--     nat.add_sub_cancel, p.get_vert_inj_iff_right, add_right_cancel_iff,
--     hn, trans (nat.lt_succ_self _) hn,
--     and_comm _ (_ = n), exists_and_distrib_left, exists_eq_left, exists_const],
-- end

-- lemma path.start_unique_edge_iff (p: path G u v) (hne: u ≠ v) (x: V):
--   ⟦(u, x)⟧ ∈ p.val.edges ↔ p.val.get_vert 1 = x :=
-- by simp only [← p.val.get_vert_zero, list.mem_iff_nth_le, p.val.edge_vertex_iff,
--     p.pos_length_of_ne hne, p.get_vert_inj_iff_right,
--     nat.succ_ne_zero, and_false, or_false, exists_and_distrib_left,
--     exists_eq_left, zero_add, walk.length_edges, eq_self_iff_true,
--     exists_const]

-- lemma path.tail_unique_edge (p: path G u v): u ≠ v →  ∃! (w : V), ⟦(v, w)⟧ ∈ p.val.edges :=
-- begin
--   cases p with w hp,
--   induction w with _ u x v hux hxv,
--   { simp },
--   intro huv,
--   simp only [simple_graph.walk.cons_is_path_iff] at hp,
--   cases hp with hp _,
--   specialize w_ih hp,
--   cases hxv with x _ y _ hxy hyv,
--   { simp [huv.symm] },
--   simp only [simple_graph.walk.cons_is_path_iff] at hp,
--   cases hp with _ hp,
--   have hxv: x ≠ v,
--   { contrapose! hp,
--     rw [hp],
--     apply hyv.end_mem_support },
--   simpa [huv.symm, hxv, hxv.symm] using w_ih,
-- end

-- lemma path.end_unique_edge_iff (p: path G u v) (hne: u ≠ v) (x: V):
--   ⟦(v, x)⟧ ∈ p.val.edges ↔ p.val.get_vert (p.val.length - 1) = x :=
-- begin
--   split,
--   {
--     apply exists_unique.unique (p.tail_unique_edge hne),
--     conv in v {
--       rw [← p.val.get_vert_length, ← nat.sub_add_cancel (nat.succ_le_of_lt (p.pos_length_of_ne hne))],
--     },
--     rw [sym2.eq_swap, ← p.val.edge_vertex' (nat.sub_lt (p.pos_length_of_ne hne) zero_lt_one)],
--     exact list.nth_le_mem _ _ _,
--   },
--   { intro h,
--     rw [← h],
--     conv in v {
--       rw [← p.val.get_vert_length, ← nat.sub_add_cancel (nat.succ_le_of_lt (p.pos_length_of_ne hne))],
--     },
--     rw [sym2.eq_swap, ← p.val.edge_vertex' (nat.sub_lt (p.pos_length_of_ne hne) zero_lt_one)],
--     exact list.nth_le_mem _ _ _,
--   }
-- end
-- -- by simp only [← p.val.get_vert_zero, list.mem_iff_nth_le, p.val.edge_vertex_iff,
-- --     p.pos_length_of_ne hne, p.get_vert_inj_iff_right,
-- --     nat.succ_ne_zero, and_false, or_false, exists_and_distrib_left,
-- --     exists_eq_left, zero_add, walk.length_edges, eq_self_iff_true,
-- --     exists_const]

-- lemma exists_le_of_self_or_succ {u: ℕ} (hu: 0 < u) (p: ℕ → Prop):
--   (∃ (x : ℕ) (h : x < u), p x ∨ p (x + 1)) ↔ ∃ (x: ℕ) (h: x ≤ u), p x :=
-- begin
--   split,
--   { intro q,
--     rcases q with ⟨n, h, q⟩,
--     cases q,
--     { exact ⟨n, le_of_lt h, q⟩ },
--     { exact ⟨n+1, nat.succ_le_of_lt h, q⟩ } },
--   { intro q,
--     rcases q with ⟨n, h, q⟩,
--     cases n,
--     { exact ⟨0, hu, or.inl q⟩ },
--     { exact ⟨n, nat.lt_of_succ_le h, or.inr q⟩ } }
-- end

-- lemma path.edges_iff_vertex (p: path G u v) (hne: u ≠ v) (x: V):
--   (∃ (w : V), ⟦(x, w)⟧ ∈ p.val.edges) ↔ ∃ (n : ℕ) (h : n ≤ p.val.edges.length), p.val.get_vert n = x :=
-- by simpa [list.mem_iff_nth_le, walk.edge_vertex_iff,
--       and_or_distrib_left, @exists_or_distrib V, @exists_comm V _]
--       using exists_le_of_self_or_succ (p.pos_length_of_ne hne) (λ y, p.val.get_vert y = x)


-- namespace subgraph

-- noncomputable
-- instance [h: fintype V]: fintype M.verts :=
--    fintype.of_finite ↥(M.verts)

-- def is_maximal_matching (M: subgraph G) (m: M.is_matching) [fintype V] :=
--   ∀ M' : subgraph G, M'.is_matching →
--     M'.verts.to_finset.card ≤ M.verts.to_finset.card

-- def augmenting_path (M: subgraph G) (p: path G u v) :=
--   u ≠ v ∧ u ∉ M.verts ∧ v ∉ M.verts ∧
--     ∀ (n :ℕ) (hn: n < p.val.edges.length), (odd n ↔ (list.nth_le _ _ hn) ∈ M.edge_set)

-- namespace augmenting_path
-- variables {p: path G u v}

-- lemma augmenting_path_odd (ap: augmenting_path M p): odd p.val.length :=
-- begin
--   rcases ap with ⟨hne, hu, hv, hap⟩,
--   cases hn: p.val.length,
--   { exfalso,
--     exact hne (path.nil_of_zero_length _ hn) },
--   { rw [nat.odd_iff_not_even, nat.even_add_one, ← nat.odd_iff_not_even,
--       hap n (by rw [walk.length_edges, hn]; exact nat.lt_succ_self _ )],
--     rw [walk.edge_vertex, ← nat.succ_eq_add_one, ← hn, p.val.get_vert_of_length_le (le_refl _)],
--     contrapose! hv,
--     exact subgraph.mem_verts_if_mem_edge hv (sym2.mem_mk_right (p.val.get_vert n) v) }
-- end

-- def augment_adj (ap: augmenting_path M p) (x y: V) :=
--   xor (M.adj x y) (⟦(x, y)⟧ ∈ p.val.edges)

-- theorem augment_adj_sub (ap: augmenting_path M p):
--   ∀ (x y: V), ap.augment_adj x y → G.adj x y :=
-- begin
--   intros x y,
--   unfold augment_adj xor,
--   intro h,
--   cases h,
--   exact M.adj_sub h.left,
--   exact walk.adj_of_mem_edges _ h.left,
-- end

-- theorem augment_edge_vert (ap: augmenting_path M p):
--   ∀ (x y: V), ap.augment_adj x y → x ∈ (insert u (insert v M.verts)) :=
-- begin
--   intros x y,
--   unfold augment_adj xor,
--   intro h,
--   cases h,
--   { exact set.mem_insert_of_mem _ (set.mem_insert_of_mem _ (M.edge_vert h.left)) },
--   rcases ap with ⟨hnu, hu, hv, hap⟩,
--   cases h with hp hm,
--   rcases list.nth_le_of_mem hp with ⟨n, hn, hp⟩,
--   have hap₁ := hap n hn,
--   rw [hp, mem_edge_set] at hap₁,
--   simp only [hm, iff_false, ← nat.even_iff_not_odd] at hap₁,
--   obtain hp|hp|hp|hp := walk.edge_neighbor_cases hp,
--   { rw[hp], exact set.mem_insert _ _ },
--   all_goals { refine set.mem_insert_of_mem _ _ },
--   { rw[hp], exact set.mem_insert _ _ },
--   all_goals {
--     refine set.mem_insert_of_mem _ _,
--     rcases hp with ⟨z, hn', hz⟩,
--   },
--   { cases n, { revert hn', simp },
--     simp only [nat.succ_eq_add_one, nat.add_sub_cancel] at *,
--     apply subgraph.mem_verts_if_mem_edge,
--     rwa [← hap n (trans (nat.lt_succ_self _) hn), nat.odd_iff_not_even, ← nat.even_add_one],
--     rw [hz],
--     exact sym2.mem_mk_left _ _ },
--   { apply subgraph.mem_verts_if_mem_edge,
--     rwa [← hap (n+1) hn', nat.odd_iff_not_even, nat.even_add_one, not_not],
--     rw [hz],
--     exact sym2.mem_mk_left _ _ }
-- end

-- theorem augment_symm (ap: augmenting_path M p):
--   symmetric ap.augment_adj :=
-- begin
--   intros x y h,
--   cases h; cases h with h_pos h_neg,
--   { left, exact ⟨M.symm h_pos, by rwa [sym2.eq_swap] ⟩ },
--   { right,
--     refine ⟨ by rwa [sym2.eq_swap], _ ⟩,
--     contrapose! h_neg,
--     apply M.symm h_neg },
-- end

-- def augment_subgraph (ap: augmenting_path M p):
--   subgraph G := ⟨ insert u (insert v M.verts), ap.augment_adj, ap.augment_adj_sub, ap.augment_edge_vert, ap.augment_symm ⟩ 


-- instance (ap: augmenting_path M p) [decidable_eq V] [h: fintype M.verts]: fintype ap.augment_subgraph.verts :=
-- begin
--   simp only [augment_subgraph],
--   apply_instance,
-- end

-- lemma augment_is_matching_elem_odd (ap: augmenting_path M p) (hM: M.is_matching) (n: ℕ) (hn: n < p.val.length) (hn': odd n) (x: V):
--    ⟦(p.val.get_vert n, x)⟧ ∈ M.edge_set ↔ x = p.val.get_vert (n + 1) :=
-- begin
--   rcases ap with ⟨hne, hu, hv, hap⟩,
--   split,
--   { rw [mem_edge_set],
--     intro h,
--     apply exists_unique.unique (hM (M.edge_vert h)) h,
--     rwa [← mem_edge_set, ← p.val.edge_vertex, ← hap _ (p.val.lt_length_edges hn)] },
--   { intro h,
--     rwa [h, ← p.val.edge_vertex, ← hap _ (p.val.lt_length_edges hn)] },
-- end

-- lemma augment_is_matching_elem_even (ap: augmenting_path M p) (hM: M.is_matching) (n: ℕ) (hn: n < p.val.edges.length) (hn': odd n) (x: V):
--    ⟦(p.val.get_vert (n + 1), x)⟧ ∈ M.edge_set ↔ x = p.val.get_vert n :=
-- begin
--   rcases ap with ⟨hne, hu, hv, hap⟩,
--   split,
--   { rw [mem_edge_set],
--     intro h,
--     apply exists_unique.unique (hM (M.edge_vert h)) h,
--     apply M.adj_symm,
--     rwa [← mem_edge_set, ← p.val.edge_vertex, ← hap _ hn] },
--   { intro h,
--     rwa [sym2.eq_swap, h, ← p.val.edge_vertex, ← hap _ hn] },
-- end

-- lemma xor_or_self_iff (p q: Prop):
--   xor p (q ∨ p) ↔ ¬ p ∧ q :=
-- by by_cases p; simp[h]

-- lemma xor_self_or_iff (p q: Prop):
--   xor p (p ∨ q) ↔ ¬ p ∧ q :=
-- by by_cases p; simp[h]

-- lemma augment_is_matching_helper_even (ap: augmenting_path M p) (hM: M.is_matching) (n: ℕ) (hn: n ≤ p.val.length) (hn': even n) (x: V):
--   (augment_subgraph ap).adj (p.val.get_vert n) x ↔ x = p.val.get_vert (n + 1) :=
-- begin
--   cases eq_or_lt_of_le hn with hn hn,
--   { exfalso,
--     revert hn',
--     simpa only [hn, nat.even_iff_not_odd, ap.augmenting_path_odd, not_true] using id },
--   split,
--   { cases n,
--     { simpa only [augment_subgraph, augment_adj, walk.get_vert_zero,
--         ← mem_edge_set, (not_imp_not.mpr M.edge_vert) ap.right.left, xor_false, id,
--         p.start_unique_edge_iff ap.left, zero_add] using eq.symm },
--     simp only [augment_subgraph, augment_adj,  ← mem_edge_set, list.mem_iff_nth_le, p.val.edge_vertex_iff],
--     have hn₁ := lt_of_lt_of_le (nat.lt_succ_self _) hn,
--     rw [nat.even_add_one, ←nat.odd_iff_not_even] at hn',
--     rw [nat.succ_eq_add_one] at hn,
--     simp only [p.get_vert_inj_iff_right _ _ (nat.lt_of_succ_le hn),
--       nat.succ_eq_add_one,
--       exists_or_distrib, @and.left_comm _ (_ = n + 1), @and.left_comm _ (_ = n), @and.comm _ (_ = n),
--       exists_prop, and_assoc,
--       and_or_distrib_left, true_and,
--       exists_eq_left, add_right_cancel_iff,
--       p.val.length_edges,
--       hn, trans (nat.lt_succ_self _) hn,
--       ap.augment_is_matching_elem_even hM _ (trans (nat.lt_succ_self _) (p.val.lt_length_edges hn)) hn'],
--     simp [@eq_comm _ x, xor_or_self_iff, and_imp] },
--   { intro h,
--     right,
--     simp only [h, ← p.val.edge_vertex (p.val.lt_length_edges hn), list.nth_le_mem, true_and, ← mem_edge_set, ←ap.right.right.right, ← nat.even_iff_not_odd, hn'] }
-- end


-- lemma augment_is_matching_helper_odd (ap: augmenting_path M p) (hM: M.is_matching) (n: ℕ) (hn: n < p.val.length) (hn': even n) (x: V):
--   (augment_subgraph ap).adj (p.val.get_vert (n + 1)) x ↔ x = p.val.get_vert n :=
-- begin
--   split,
--   { cases eq_or_lt_of_le (nat.succ_le_of_lt hn),
--     { simp only [augment_subgraph, augment_adj, ← nat.succ_eq_add_one, h,
--         p.val.get_vert_length, (not_imp_not.mpr M.edge_vert) ap.right.right.left, xor_false, id,
--         list.mem_iff_nth_le, p.end_unique_edge_iff ap.left],
--       simpa only [← h, nat.succ_eq_add_one, nat.add_sub_cancel] using eq.symm },
--     simp only [augment_subgraph, augment_adj, ← mem_edge_set,
--       p.mem_neighbor_cases (nat.zero_lt_succ _) h,
--       ap.augment_is_matching_elem_odd hM _ h (by rwa [nat.odd_iff_not_even, nat.even_add_one, not_not]),
--       nat.succ_eq_add_one, @eq_comm _ x, xor_self_or_iff,
--       nat.add_sub_cancel, and_imp],
--     simp },
--   { intro h,
--     rw [h],
--     apply ap.augment_subgraph.adj_symm,
--     rw [ap.augment_is_matching_helper_even hM _ (le_of_lt hn) hn'] }
-- end

-- theorem augment_is_matching (ap: augmenting_path M p):
--   M.is_matching → ap.augment_subgraph.is_matching :=
-- begin
--   intros hM x hx,
--   simp only [set.mem_insert_iff, augment_subgraph] at hx,
--   obtain hxu|hxv|hx := hx,
--   { simpa [augment_subgraph, augment_adj, xor, hxu,
--           (not_imp_not.mpr M.edge_vert) ap.right.left] using p.head_unique_edge ap.left },
--   { simpa [augment_subgraph, augment_adj, xor, hxv,
--           (not_imp_not.mpr M.edge_vert) ap.right.right.left] using p.tail_unique_edge ap.left },
--   by_cases ∃ w, ⟦(x, w)⟧ ∈ p.val.edges,
--   { rw [p.edges_iff_vertex ap.left] at h,
--     rcases h with ⟨n, hn, hnx⟩,
--     rw [← hnx],
--     by_cases (even n),
--     cases eq_or_lt_of_le hn with hn hn,
--     { contrapose! h,
--       simpa only [hn, ← nat.odd_iff_not_even, p.val.length_edges] using ap.augmenting_path_odd },
--     conv { congr, funext, rw [ap.augment_is_matching_helper_even hM n (le_of_lt (p.val.lt_of_length_edges hn)) h], skip },
--     { simp },
--     cases n,
--     { revert h, simp },
--     simp only [nat.even_add_one, not_not] at h,
--     conv { congr, funext, rw [nat.succ_eq_add_one, ap.augment_is_matching_helper_odd hM _ (p.val.lt_of_length_edges (nat.lt_of_succ_le hn)) h], skip },
--     { simp } },
--   { simp only [not_exists] at h,
--     simp only [augment_subgraph, augment_adj, xor, h, not_false_iff, and_true, false_and, or_false],
--     exact hM hx },
-- end

-- theorem augment_card (ap: augmenting_path M p) [decidable_eq V] [fintype M.verts]:
--   M.verts.to_finset.card + 2 = ap.augment_subgraph.verts.to_finset.card :=
-- begin
--   rcases ap with ⟨hne, hu, hv, _⟩,
--   simp only [augment_subgraph, set.to_finset_insert],
--   rw [finset.card_insert_of_not_mem, finset.card_insert_of_not_mem],
--   rw [set.mem_to_finset],
--   exact hv,
--   simp only [finset.mem_insert, hne, false_or, set.mem_to_finset],
--   exact hu,
-- end

-- theorem berges_mp (ap: augmenting_path M p) (hM: M.is_matching) [decidable_eq V] [fintype V]:
--   ¬ M.is_maximal_matching hM :=
-- begin
--   simp only [is_maximal_matching, not_forall],
--   refine ⟨ ap.augment_subgraph, ap.augment_is_matching hM, _ ⟩,
--   apply not_le_of_lt,
--   rw [← add_lt_add_iff_right 2, ap.augment_card],
--   simp [augment_subgraph],
-- end

-- end augmenting_path
-- end subgraph
end simple_graph