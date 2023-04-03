import hmem.stack
import hmem.encoding.basic
import hmem.split_cost
import hmem.trace
import complexity.basic

variables {μ: Type*} [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]

namespace hmem
namespace encoding


def encode_list {α: Type*} [α_en: complexity.has_encoding (runtime_model μ) α]: list α → memory μ
| [] := memory.null _
| (x::xs) := (((memory.null _).setv 1).setm 0 (encode x)).setm 1 (encode_list xs)

instance (α: Type*) [α_en: complexity.has_encoding (runtime_model μ) α]: complexity.has_encoding (runtime_model μ) (list α) :=
⟨ ⟨ encode_list,
begin
  intros x y,
  split,
  {  induction x generalizing y;
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
    { 
      rw ← complexity.encoding.encode_inj α_en.value,
      apply memory.getm_congr 0 h;
      { rw [memory.getm_setm_ne, memory.getm_setm],
        refl,
        apply zero_ne_one } },
    apply x_ih,
    apply memory.getm_congr 1 h;
    { rw [memory.getm_setm] } },
  intro h,
  rw [h],
  unfold has_equiv.equiv,
end ⟩ ⟩ 

theorem encode_nil {α: Type*} [complexity.has_encoding (runtime_model μ) α]: encode (@list.nil α) = memory.null μ := rfl

theorem encode_cons {α: Type*} [complexity.has_encoding (runtime_model μ) α] (x: α) (xs: list α): encode (x::xs) = (((memory.null μ).setv 1).setm 0 (encode x)).setm 1 (encode xs) := rfl

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
  {α: Type*} [complexity.has_encoding (runtime_model μ) α]: list α → hmem.trace μ
| [] := ⟨ encode (@list.nil α, @list.nil α), 2, [], [] ⟩
| (x::xs) := ⟨ encode (list.split (x::xs)), 4, [], [encode xs] ⟩

theorem split_trace_result
  (μ: Type*) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]
  {α: Type*} [complexity.has_encoding (runtime_model μ) α] (l: list α):
  (split_trace μ l).result = encode l.split :=
by cases l; refl

theorem split_has_trace {α: Type*} [complexity.has_encoding (runtime_model μ) α] (l : list α):
  (split μ).has_trace (encode l) (split_trace μ l) :=
begin
  induction l,
  { unfold split_trace,
    apply start_trace,
    { unfold split instruction.ifz instruction.const },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_nil, memory.getv_null, eq_self_iff_true, if_true,
      memory.getvs, source.get, memory.getvp_nil,
      vector.map_cons, vector.nth_cons_zero, fin.mk_zero],
    apply step_trace,
    { unfold thunk.step_over thunk.step, },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply end_trace,
    simp only [encode_pair, encode_nil, memory.setvs, source.get, memory.setvp_nil, memory.null_setv_setm_null] },
  { unfold split_trace,
    apply start_trace,
    { unfold split instruction.swap instruction.ifz },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_cons, memory.getv_setm, memory.getv_setv, 
      memory.getvs, source.get, memory.getvp_nil,
      vector.map_cons, vector.nth_cons_zero, fin.mk_zero, one_ne_zero, if_false],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply recurse_trace,
    { simp only [memory.mop, memory.setms, memory.getms, source.get,
        memory.setmp_nil, memory.setmp_cons, memory.setm_setm,
        memory.getmp_nil, memory.getmp_cons,
        memory.getm_setm, memory.getm_setm_nz,
        memory.setm_setm_nz] },
    { have h := l_ih.result,
      rw [split_trace_result] at h,
      exact h },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
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

def merge_trace {α: Type*} [complexity.has_encoding (runtime_model μ) α] (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp] (pcmp: program μ):
  list α → list α → trace μ
| [] b := ⟨ encode b, 2, [], [] ⟩
| (a::as) [] := ⟨ encode (a::as), 3, [], [] ⟩
| (a::as) (b::bs) := 
  ⟨ encode (list.merge fcmp (a::as) (b::bs)), 9,
    [(pcmp, (encode (a, b)))],
    [encode (if fcmp a b then (as, b::bs) else (a::as, bs))] ⟩

theorem merge_trace_result {α: Type*} [complexity.has_encoding (runtime_model μ) α] (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp] (pcmp: program μ)
  (as bs: list α): (merge_trace fcmp pcmp as bs).result = encode (list.merge fcmp as bs) :=
by cases as; cases bs; unfold merge_trace list.merge; split_ifs; refl

theorem merge_has_trace {α: Type*} [complexity.has_encoding (runtime_model μ) α]
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
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_pair, encode_nil,
      fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
      source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
      memory.getm_setm, memory.getm_setm_nz, memory.getv_null,
      eq_self_iff_true, if_true],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply end_trace,
    simp only [source.get, memory.getms, memory.setms,
      memory.setmp_cons, memory.setmp_nil,
      memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm] },
  cases bs with b bs,
  { unfold merge_trace,
    apply start_trace,
    { unfold merge instruction.ifz instruction.move },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_pair, encode_cons,
      fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
      source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
      memory.getm_setm, memory.getm_setm_nz,
      memory.getv_setm, memory.getv_setv,
      one_ne_zero' μ, if_false],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_pair, encode_nil,
      fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
      source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
      memory.getm_setm, memory.getm_setm_nz, memory.getv_null,
      eq_self_iff_true, if_true],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply end_trace,
    simp only [source.get, memory.getms, memory.setms,
      memory.setmp_cons, memory.setmp_nil,
      memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm, memory.getm_setm_nz] },
  unfold merge_trace,
  apply start_trace,
  { unfold merge instruction.ifz instruction.copy instruction.move },
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  simp only [encode_pair, encode_cons,
    fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
    source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
    memory.getm_setm, memory.getm_setm_nz,
    memory.getv_setm, memory.getv_setv,
    one_ne_zero' μ, if_false],
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  simp only [fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
    source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
    memory.getm_setm, memory.getm_setm_nz,
    memory.getv_setm, memory.getv_setv,
    one_ne_zero' μ, if_false],
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  simp only [source.get, memory.getms, memory.setms,
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
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  cases hdcmp:dcmp a b;
  try { simp [encode_is_false (decidable.is_false h_1)] };
  try { simp [encode_is_true (decidable.is_true h_1)] };
  { simp only [h_1, if_false, if_true, one_ne_zero' μ, eq_self_iff_true,
      vector.map_cons, fin.mk_zero, vector.nth_cons_zero,
      source.get, memory.getvs,
      memory.getmp_cons, memory.getmp_nil,
      memory.getvp_cons, memory.getvp_nil,
      memory.setmp_cons, memory.setmp_nil,
      memory.getm_setm, memory.getm_setm_nz,
      memory.setm_setm, memory.setm_setm_nz,
      memory.getv_setm, memory.getv_setv, memory.getv_null],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply recurse_trace,
    { simp only [encode_pair, encode_cons,
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
      list.merge, h_1, if_true, if_false] }
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

def merge_sort_trace {α: Type*} [complexity.has_encoding (runtime_model μ) α] (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp] (pcmp: program μ):
  list α → trace μ
| [] := ⟨encode (@list.nil α), 1, [], []⟩
| [a] := ⟨encode [a], 1, [], []⟩
| l := match list.split l with
  | (as, bs) :=
    ⟨encode (list.merge_sort fcmp l), 5,
     [(split μ, encode l),
      (merge pcmp, encode (list.merge_sort fcmp as, list.merge_sort fcmp bs))],
     [encode as, encode bs]⟩
  end

theorem merge_sort_result {α: Type*} [complexity.has_encoding (runtime_model μ) α] (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp] (pcmp: program μ) (l: list α):
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
  {α: Type*} [complexity.has_encoding (runtime_model μ) α]
  (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp]
  {pcmp: program μ} (hcmp: ∀ (a b: α), pcmp.has_result (encode (a, b)) (encode (dcmp a b)))
  (l: list α):
  (merge_sort pcmp).has_trace (encode l) (merge_sort_trace fcmp pcmp l) :=
begin
  induction hn:l.length using nat.strong_induction_on with n ih generalizing l,
  cases l with a l,
  { apply start_trace,
    { unfold merge_sort instruction.ifz },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_nil, fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
      source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
      memory.getv_null, memory.getm_null, eq_self_iff_true, if_true],
    apply end_trace rfl },
  cases l with b l,
  { apply start_trace,
    { unfold merge_sort instruction.ifz },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_nil, encode_cons, fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
      source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
      memory.getv_null, memory.getm_setm, eq_self_iff_true, if_true],
    apply end_trace rfl },
  cases hsplit:(a::b::l).split,
  simp only [merge_sort_trace, hsplit],
  apply start_trace,
  { unfold merge_sort instruction.ifz },
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  simp only [encode_cons, fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
    source.get, memory.getvs, memory.getvp_cons, memory.getvp_nil,
    memory.getm_setm, memory.getv_setm, memory.getv_setv, one_ne_zero' μ, if_false],
  apply call_trace,
  { simp only [source.get, memory.getms, memory.getmp_nil] },
  { rw [← encode_cons, ← encode_cons],
    apply program.has_trace.result,
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