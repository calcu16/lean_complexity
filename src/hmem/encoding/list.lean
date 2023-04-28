import hmem.stack
import hmem.encoding.basic
import hmem.split_cost
import hmem.trace
import complexity.basic

variables {μ: Type*} [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]

namespace hmem
namespace encoding

def encode_list {α: Type*} [α_en: has_encoding α μ]: list α → memory μ
| [] := memory.null _
| (x::xs) := (((memory.null _).setv 1).setm 0 (encode x)).setm 1 (encode_list xs)

instance list_encoding (α: Type*) [α_en: has_encoding α μ]: has_encoding (list α) μ :=
⟨ encode_list,
begin
  intros x y,
  rw [memory_equiv_eq_iff],
  induction x generalizing y;
  cases y,
  { simp only [has_equiv.equiv, eq_self_iff_true, imp_true_iff] },
  { simp only [has_equiv.equiv, (list.cons_ne_nil _ _).symm, iff_false, encode_list],
    intro h,
    apply @zero_ne_one μ,
    apply memory.getv_congr h,
    refl,
    rw [memory.getv_setm, memory.getv_setm, memory.getv_setv] },
  { simp only [has_equiv.equiv, (list.cons_ne_nil _ _), iff_false, encode_list],
    intro h,
    apply (@zero_ne_one μ _ _ _).symm,
    apply memory.getv_congr h,
    rw [memory.getv_setm, memory.getv_setm, memory.getv_setv],
    refl },
  simp only [has_equiv.equiv, encode_list, encode],
  intro h,
  split,
  { apply encode_inj' μ,
    apply memory.getm_congr 0 h;
    rw [memory.getm_setm_nz, memory.getm_setm] },
  apply x_ih,
  apply memory.getm_congr 1 h;
  rw [memory.getm_setm]
end ⟩

theorem encode_nil {α: Type*} [has_encoding α μ]: encode (@list.nil α) = memory.null μ := rfl

theorem encode_cons {α: Type*} [has_encoding α μ] (x: α) (xs: list α): encode (x::xs) = (((memory.null μ).setv 1).setm 0 (encode x)).setm 1 (encode xs) := rfl

def split (μ: Type*) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]: program μ :=
[ -- xs
  instruction.ifz source.nil [
    -- list.nil
    instruction.const source.nil 1
    -- 1 list.nil list.nil
  ],
  -- 1 x xs
  instruction.swap (source.imm 0 source.nil) (source.imm 1 source.nil),
  -- 1 xs x
  instruction.recurse (source.imm 0 source.nil) (source.imm 0 source.nil),
  -- 1 [ 1 fst snd ] x
  instruction.swap (source.imm 0 (source.imm 0 source.nil)) (source.imm 1 source.nil)
  -- 1 (x::snd) fst
]

def split_trace
  (μ: Type*) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]
  {α: Type*} [has_encoding α μ]: list α → hmem.trace μ
| [] := ⟨ encode (@list.nil α, @list.nil α), [tt], 2, [], [] ⟩
| (x::xs) := ⟨ encode (list.split (x::xs)), [ff], 4, [], [encode xs] ⟩

theorem split_trace_result
  (μ: Type*) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]
  {α: Type*} [has_encoding α μ] (l: list α):
  (split_trace μ l).result = encode l.split :=
by cases l; refl

theorem split_has_trace {α: Type*} [has_encoding α μ] (l : list α):
  (split μ).has_trace (encode l) (split_trace μ l) :=
begin
  induction l,
  { unfold split_trace,
    apply start_trace,
    { unfold split instruction.ifz instruction.const },
    apply if_true_trace,
    { refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step, },
    { apply thunk.extend_trace₀, unfold thunk.step, refl, refl },
    apply end_trace,
    simp only [encode_pair, encode_nil, memory.setvs, source.get, memory.setvp_nil, memory.null_setv_setm_null] },
  { unfold split_trace,
    apply start_trace,
    { unfold split instruction.swap instruction.ifz },
    apply if_false_trace,
    { simpa only [encode_cons, memory.getv_setm, memory.getv_setv, 
        memory.getvs, source.get, memory.getvp_nil,
        vector.map_cons, vector.nth_cons_zero, fin.mk_zero, one_ne_zero, if_false] using not_false },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl, refl },
    apply recurse_trace,
    { simp only [encode_cons, memory.mop, memory.setms, memory.getms, source.get,
        memory.setmp_nil, memory.setmp_cons, memory.setm_setm,
        memory.getmp_nil, memory.getmp_cons,
        memory.getm_setm, memory.getm_setm_nz,
        memory.setm_setm_nz] },
    { have h := l_ih.result,
      rw [split_trace_result] at h,
      exact h },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl, refl },
    apply end_trace,
    { cases hsplit:l_tl.split,
      simp only [list.split, hsplit, encode_pair, encode_cons,
        memory.mop, memory.setms, memory.getms, source.get,
        memory.setmp_nil, memory.setmp_cons, memory.setm_setm,
        memory.getmp_nil, memory.getmp_cons,
        memory.getm_setm, memory.getm_setm_nz,
        memory.setm_setm_nz] } }
end

def merge {μ: Type*} [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)] (cmp: program μ): program μ :=
[ -- 1 as bs
  instruction.ifz (source.imm 0 source.nil) [
    -- 1 [] bs
    instruction.move source.nil (source.imm 1 source.nil)
    -- bs
  ],
  -- 1 [1 a as] bs
  instruction.ifz (source.imm 1 source.nil) [
    -- 1 [1 a as] []
    instruction.move source.nil (source.imm 0 source.nil)
    -- 1 a as
  ],
  instruction.copy (source.imm 1 (source.nil)) source.nil,
  -- 1 [1 a as] [1 [1 a as] [1 b bs]]
  instruction.copy (source.imm 0 (source.imm 1 source.nil)) (source.imm 1 (source.imm 1 (source.imm 0 source.nil))),
  -- 1 [1 a b] [1 [1 a as] [1 b bs]]
  instruction.call cmp (source.imm 0 source.nil) (source.imm 0 source.nil),
  -- 1 [(a ≼ b) ? ?] [1 [1 a b] [1 as bs]]
  instruction.ifz (source.imm 0 source.nil) [
    -- ¬ a ≼ b
    -- 1 [1 null null] [1 [1 a as] [1 b bs]]
    instruction.move (source.imm 0 source.nil) (source.imm 1 (source.imm 1 (source.imm 0 source.nil))),
    -- 1 b [1 [1 a as] bs]
    instruction.move (source.imm 1 (source.imm 1 source.nil)) (source.imm 1 (source.imm 1 (source.imm 1 source.nil))),
    -- 1 b [1 [1 a as] bs]
    instruction.recurse (source.imm 1 source.nil) (source.imm 1 source.nil)
    -- 1 b xs
  ],
  -- a ≼ b
  -- 1 [0 null null] [1 [1 a as] [1 b bs]]
  instruction.move (source.imm 0 source.nil) (source.imm 1 (source.imm 0 (source.imm 0 source.nil))),
  -- 1 [1 a null] [1 [1 null as] [1 b bs]]
  instruction.move (source.imm 1 (source.imm 0 source.nil)) (source.imm 1 (source.imm 0 (source.imm 1 source.nil))),
  -- 1 a [1 as [1 b bs]]
  instruction.recurse (source.imm 1 source.nil) (source.imm 1 source.nil)
  -- 1 a xs
]

def merge_trace {α: Type*} [has_encoding α μ] (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp] (pcmp: program μ):
  list α → list α → trace μ
| [] b := ⟨ encode b, [tt], 2, [], [] ⟩
| (a::as) [] := ⟨ encode (a::as), [ff, tt], 3, [], [] ⟩
| (a::as) (b::bs) := 
  ⟨ encode (list.merge fcmp (a::as) (b::bs)), [ff, ff, ¬ fcmp a b], 9,
    [encode (a, b)],
    [encode (if fcmp a b then (as, b::bs) else (a::as, bs))] ⟩

theorem merge_trace_result {α: Type*} [has_encoding α μ] (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp] (pcmp: program μ)
  (as bs: list α): (merge_trace fcmp pcmp as bs).result = encode (list.merge fcmp as bs) :=
by cases as; cases bs; unfold merge_trace list.merge; split_ifs; refl

theorem merge_has_trace {α: Type*} [has_encoding α μ]
  (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp]
  {pcmp: program μ} (hcmp: ∀ (a b: α), pcmp.has_result (encode (a, b)) (encode (dcmp a b)))
  (as bs: list α):
  (merge pcmp).has_trace (encode (as, bs)) (merge_trace fcmp pcmp as bs) :=
begin
  induction h:(as.length + bs.length) using nat.strong_induction_on with n ih generalizing as bs,
  cases as with a as,
  { unfold merge_trace,
    apply start_trace,
    { unfold merge instruction.ifz instruction.move },
    apply if_true_trace,
    { simp only [encode_pair, encode_nil,
        fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
        source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
        memory.getm_setm, memory.getm_setm_nz, memory.getv_null,
        eq_self_iff_true, if_true] },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl, refl },
    apply end_trace,
    simp only [encode_pair, encode_nil, source.get, memory.getms, memory.setms,
      memory.setmp_cons, memory.setmp_nil,
      memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm] },
  cases bs with b bs,
  { unfold merge_trace,
    apply start_trace,
    { unfold merge instruction.ifz instruction.move },
    apply if_false_trace,
    { simpa only [encode_pair, encode_cons,
        fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
        source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
        memory.getm_setm, memory.getm_setm_nz,
        memory.getv_setm, memory.getv_setv,
        one_ne_zero' μ, if_false] using not_false },
    apply if_true_trace,
    { simp only [encode_pair, encode_nil,
        fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
        source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
        memory.getm_setm, memory.getm_setm_nz, memory.getv_null,
        eq_self_iff_true, if_true] }, 
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl, refl },
    apply end_trace,
    simp only [encode_pair, source.get, memory.getms, memory.setms,
      memory.setmp_cons, memory.setmp_nil,
      memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm, memory.getm_setm_nz] },
  unfold merge_trace,
  apply start_trace,
  { unfold merge instruction.ifz instruction.copy instruction.move },
  apply if_false_trace,
  { simpa only [encode_pair, encode_cons,
      fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
      source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
      memory.getm_setm, memory.getm_setm_nz,
      memory.getv_setm, memory.getv_setv,
      one_ne_zero' μ, if_false] using not_false },
  apply if_false_trace,
  { simpa only [encode_pair, encode_cons, fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
      source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
      memory.getm_setm, memory.getm_setm_nz,
      memory.getv_setm, memory.getv_setv,
      one_ne_zero' μ, if_false] using not_false },
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl, refl },
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl, refl },
  simp only [encode_pair, encode_cons, source.get, memory.getms, memory.setms,
    memory.setmp_cons, memory.setmp_nil,
    memory.getmp_cons, memory.getmp_nil,
    memory.setm_setm, memory.setm_setm_nz,
    memory.getm_setm, memory.getm_setm_nz,
    memory.mop],
  apply call_trace,
  { simp only [memory.setms, memory.getms, source.get,
      memory.setmp_cons, memory.setmp_nil,
      memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm, memory.getm_setm_nz,
      memory.setm_setm, memory.setm_setm_nz,
      memory.mop] },
  { apply hcmp },
  cases hdcmp:dcmp a b;
  simp only [
    vector.map_cons, fin.mk_zero, vector.nth_cons_zero, vector.cons_head,
    source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
    memory.setmp_cons, memory.setmp_nil, memory.getv_null,
    memory.setm_setm_nz,
    memory.getm_setm, h_1];
  try { simp [encode_is_true (decidable.is_true h_1)],
    apply if_false_trace,
    { simpa only [
        vector.map_cons, fin.mk_zero, vector.nth_cons_zero, vector.cons_head,
        source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
        memory.getv_setv, memory.getm_setm_nz, memory.getm_setm,
        one_ne_zero' μ] using not_false } };
  try { simp only [encode_is_false (decidable.is_false h_1)],
    apply if_true_trace,
    { simp only [
        vector.map_cons, fin.mk_zero, vector.nth_cons_zero, vector.cons_head,
        source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
        memory.getv_null, memory.getm_setm_nz, memory.getm_setm,
        eq_self_iff_true] } };
  { apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl, refl },
    apply recurse_trace,
    { simp only [encode_pair, encode_cons, if_false,
        source.get, memory.setms, memory.getms,
        memory.setmp_cons, memory.setmp_nil,
        memory.getmp_cons, memory.getmp_nil,
        memory.getm_setm, memory.getm_setm_nz,
        memory.setm_setm, memory.setm_setm_nz] },
    try { have hres := (ih _ _ (a::as) bs rfl).result,
      rw [merge_trace_result] at hres,
      apply hres,
      rw [← h, list.length_cons, list.length_cons],
      apply nat.lt_succ_self },
    try { have hres := (ih _ _ as (b::bs) rfl).result,
      rw [merge_trace_result] at hres,
      apply hres,
      simpa only [← h, list.length_cons, add_lt_add_iff_right] using nat.lt_succ_self _  },
    apply end_trace,
    simp only [encode_pair, encode_cons,
      source.get, memory.setms, memory.getms,
      memory.setmp_cons, memory.setmp_nil,
      memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm, memory.getm_setm_nz,
      memory.setm_setm, memory.setm_setm_nz,
      list.merge, h_1, if_true, if_false] },
end

def merge_sort {μ: Type*} [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)] (cmp: program μ): program μ :=
[ -- l
  instruction.ifz (source.imm 1 source.nil) [
    -- list.nil ∨ [a]
  ],
  -- 1 [1 a [1 b l]]
  instruction.call (split μ) source.nil source.nil,
  -- 1 l₀ l₁
  instruction.recurse (source.imm 0 source.nil) (source.imm 0 source.nil),
  -- 1 (ms l₀) l₁
  instruction.recurse (source.imm 1 source.nil) (source.imm 1 source.nil),
  -- 1 (ms l₀) (ms l₁),
  instruction.call (merge cmp) source.nil source.nil
  -- ms l
]

def merge_sort_trace {α: Type*} [has_encoding α μ] (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp] (pcmp: program μ):
  list α → trace μ
| [] := ⟨encode (@list.nil α), [tt], 1, [], []⟩
| [a] := ⟨encode [a], [tt], 1, [], []⟩
| l := match list.split l with
  | (as, bs) :=
    ⟨encode (list.merge_sort fcmp l), [ff], 5,
     [encode l,
      encode (list.merge_sort fcmp as, list.merge_sort fcmp bs)],
     [encode as, encode bs]⟩
  end

theorem merge_sort_result {α: Type*} [has_encoding α μ] (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp] (pcmp: program μ) (l: list α):
  (merge_sort_trace fcmp pcmp l).result = encode (list.merge_sort fcmp l) :=
begin
  cases l with a l,
  { unfold merge_sort_trace list.merge_sort },
  cases l with b l,
  { unfold merge_sort_trace list.merge_sort },
  cases hsplit:(a::b::l).split,
  simp only [merge_sort_trace, hsplit]
end

theorem merge_sort_has_trace
  {α: Type*} [has_encoding α μ]
  (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp]
  {pcmp: program μ} (hcmp: ∀ (a b: α), pcmp.has_result (encode (a, b)) (encode (dcmp a b)))
  (l: list α):
  (merge_sort pcmp).has_trace (encode l) (merge_sort_trace fcmp pcmp l) :=
begin
  induction hn:l.length using nat.strong_induction_on with n ih generalizing l,
  cases l with a l,
  { apply start_trace,
    { unfold merge_sort instruction.ifz },
    apply if_true_trace,
    { simp only [encode_nil, fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
        source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
        memory.getv_null, memory.getm_null, eq_self_iff_true, if_true] },
    apply end_trace rfl },
  cases l with b l,
  { apply start_trace,
    { unfold merge_sort instruction.ifz },
    apply if_true_trace,
    { simp only [encode_nil, encode_cons, fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
        source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
        memory.getv_null, memory.getm_setm, eq_self_iff_true, if_true] },
    apply end_trace rfl },
  cases hsplit:(a::b::l).split,
  simp only [merge_sort_trace, hsplit],
  apply start_trace,
  { unfold merge_sort instruction.ifz },
  apply if_false_trace,
  { simpa only [encode_cons, fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
      source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
      memory.getm_setm, memory.getv_setm, memory.getv_setv, one_ne_zero' μ, if_false] using not_false },
  apply call_trace,
  { simp only [source.get, memory.getms, memory.getmp_nil] },
  { apply program.has_trace.result,
    apply split_has_trace },
  simp only [source.get, memory.setms, memory.setmp_nil, split_trace_result, hsplit, encode_pair],
  apply recurse_trace,
  { simp only [source.get, memory.getms, memory.getmp_cons, memory.getmp_nil,
    memory.getm_setm_nz, memory.getm_setm] },
  { have hres := (ih _ _ fst rfl).result,
    rw [merge_sort_result] at hres,
    exact hres,
    rw [← hn],
    exact (list.length_split_lt hsplit).left },
  apply recurse_trace,
  { simp only [source.get, memory.getms,
    memory.getmp_cons, memory.getmp_nil, memory.setmp_cons, memory.setmp_nil,
    memory.setm_setm_nz, memory.getm_setm_nz, memory.getm_setm] },
  { have hres := (ih _ _ snd rfl).result,
    rw [merge_sort_result] at hres,
    exact hres,
    rw [← hn],
    exact (list.length_split_lt hsplit).right },
  simp only [source.get, memory.getms,
    memory.getmp_cons, memory.getmp_nil, memory.setmp_cons, memory.setmp_nil,
    memory.setm_setm_nz, memory.setm_setm, memory.getm_setm_nz, memory.getm_setm],
  apply call_trace,
  { simp only [source.get, memory.getms, memory.getmp_nil] },
  { rw [← encode_pair],
    apply program.has_trace.result,
    apply merge_has_trace fcmp,
    exact hcmp },
  apply end_trace,
  simp only [source.get, memory.setms, memory.setmp_nil,
    merge_trace_result, list.merge_sort_cons_cons fcmp hsplit],
end

end encoding
end hmem

-- open tactic
-- run_cmd do
--   d ← get_decl `list.split._main,
--   trace format!"{d.value.to_raw_fmt}"

/-
λ [sort uu+1] [list ↑0],
  list.brec_on ↑1
    (λ: [list ↑1], prod (list ↑2) (list ↑2))


(lam α implicit (sort uu+1)
 (lam ᾰ default (app (const list [uu]) (var 0))
  (app
   (app
    (app (app (const list.brec_on [uu+1, uu]) (var 1))
     (lam ᾰ default (app (const list [uu]) (var 1))
      (app (app (const prod [uu, uu]) (app (const list [uu]) (var 2))) (app (const list [uu]) (var 2)))))
    (var 0))
   (lam ᾰ default (app (const list [uu]) (var 1))
    (lam _F default
     (app
      (app (app (const list.below [uu+1, uu]) (var 2))
       (lam ᾰ default (app (const list [uu]) (var 2))
        (app (app (const prod [uu, uu]) (app (const list [uu]) (var 3))) (app (const list [uu]) (var 3)))))
      (var 0))
     (app
      (app
       (lam ᾰ default (app (const list [uu]) (var 3))
        (lam _F default
         (app
          (app (app (const list.below [uu+1, uu]) (var 4))
           (lam ᾰ default (app (const list [uu]) (var 4))
            (app (app (const prod [uu, uu]) (app (const list [uu]) (var 5))) (app (const list [uu]) (var 5)))))
          (var 0))
         (app
          (app
           (app
            (app
             (app (app (const list.cases_on [max 1 (uu+1), uu]) (var 5))
              (lam ᾰ default (app (const list [uu]) (var 5))
               (pi _F default
                (app
                 (app (app (const list.below [uu+1, uu]) (var 6))
                  (lam ᾰ default (app (const list [uu]) (var 6))
                   (app (app (const prod [uu, uu]) (app (const list [uu]) (var 7))) (app (const list [uu]) (var 7)))))
                 (var 0))
                (app (app (const prod [uu, uu]) (app (const list [uu]) (var 7))) (app (const list [uu]) (var 7))))))
             (var 1))
            (lam _F default
             (app
              (app (app (const list.below [uu+1, uu]) (var 5))
               (lam ᾰ default (app (const list [uu]) (var 5))
                (app (app (const prod [uu, uu]) (app (const list [uu]) (var 6))) (app (const list [uu]) (var 6)))))
              (app (const list.nil [uu]) (var 5)))
             (app
              (app (const id_rhs [uu+1])
               (app (app (const prod [uu, uu]) (app (const list [uu]) (var 6))) (app (const list [uu]) (var 6))))
              (app
               (app (app (app (const prod.mk [uu, uu]) (app (const list [uu]) (var 6))) (app (const list [uu]) (var 6)))
                (app (const list.nil [uu]) (var 6)))
               (app (const list.nil [uu]) (var 6))))))
           (lam ᾰ_hd default (var 5)
            (lam ᾰ_tl default (app (const list [uu]) (var 6))
             (lam _F default
              (app
               (app (app (const list.below [uu+1, uu]) (var 7))
                (lam ᾰ default (app (const list [uu]) (var 7))
                 (app (app (const prod [uu, uu]) (app (const list [uu]) (var 8))) (app (const list [uu]) (var 8)))))
               (app (app (app (const list.cons [uu]) (var 7)) (var 1)) (var 0)))
              (app
               (app (const id_rhs [uu+1])
                (app (app (const prod [uu, uu]) (app (const list [uu]) (var 8))) (app (const list [uu]) (var 8))))
               (app (app (app (const list.split._match_1 [uu]) (var 8)) (var 2))
                (app
                 (app
                  (app (const pprod.fst [uu+1, max 1 (uu+1)])
                   (app
                    (lam ᾰ default (app (const list [uu]) (var 8))
                     (app (app (const prod [uu, uu]) (app (const list [uu]) (var 9))) (app (const list [uu]) (var 9))))
                    (var 1)))
                  (app
                   (app
                    (app
                     (app (app (const list.rec [(max 1 (uu+1))+1, uu]) (var 8))
                      (lam n default (app (const list [uu]) (var 8)) (sort max 1 (uu+1))))
                     (const punit [max 1 (uu+1)]))
                    (lam hd default (var 8)
                     (lam tl default (app (const list [uu]) (var 9))
                      (lam ih default (sort max 1 (uu+1))
                       (app
                        (app (const pprod [max 1 (uu+1), max 1 (uu+1)])
                         (app
                          (app (const pprod [uu+1, max 1 (uu+1)])
                           (app
                            (lam ᾰ default (app (const list [uu]) (var 11))
                             (app (app (const prod [uu, uu]) (app (const list [uu]) (var 12)))
                              (app (const list [uu]) (var 12))))
                            (var 1)))
                          (var 0)))
                        (const punit [max 1 (uu+1)]))))))
                   (var 1)))
                 (app
                  (app
                   (app (const pprod.fst [max 1 (uu+1), max 1 (uu+1)])
                    (app
                     (app (const pprod [uu+1, max 1 (uu+1)])
                      (app
                       (lam ᾰ default (app (const list [uu]) (var 8))
                        (app (app (const prod [uu, uu]) (app (const list [uu]) (var 9)))
                         (app (const list [uu]) (var 9))))
                       (var 1)))
                     (app
                      (app
                       (app
                        (app (app (const list.rec [(max 1 (uu+1))+1, uu]) (var 8))
                         (lam n default (app (const list [uu]) (var 8)) (sort max 1 (uu+1))))
                        (const punit [max 1 (uu+1)]))
                       (lam hd default (var 8)
                        (lam tl default (app (const list [uu]) (var 9))
                         (lam ih default (sort max 1 (uu+1))
                          (app
                           (app (const pprod [max 1 (uu+1), max 1 (uu+1)])
                            (app
                             (app (const pprod [uu+1, max 1 (uu+1)])
                              (app
                               (lam ᾰ default (app (const list [uu]) (var 11))
                                (app (app (const prod [uu, uu]) (app (const list [uu]) (var 12)))
                                 (app (const list [uu]) (var 12))))
                               (var 1)))
                             (var 0)))
                           (const punit [max 1 (uu+1)]))))))
                      (var 1))))
                   (const punit [max 1 (uu+1)]))
                  (var 0)))))))))
          (var 0))))
       (var 1))
      (var 0)))))))

-/


