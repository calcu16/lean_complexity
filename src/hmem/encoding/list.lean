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
  instruction.ite (λ a, a = 0) [
    -- list.nil
    instruction.const source.nil 1
    -- 1 list.nil list.nil
  ],
  -- 1 x xs
  instruction.swap (source.imm 0 source.nil) (source.imm 1 source.nil),
  -- 1 xs x
  instruction.recurse (source.imm 0 source.nil),
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
    { unfold split instruction.const },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_nil, memory.getv_null, eq_self_iff_true, if_true],
    apply step_trace,
    { unfold thunk.step_over thunk.step, },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply end_trace,
    simp only [encode_pair, encode_nil, memory.setvs, source.get, memory.setvp_nil, memory.null_setv_setm_null] },
  { unfold split_trace,
    apply start_trace,
    { unfold split instruction.swap },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_cons, memory.getv_setm, memory.getv_setv, one_ne_zero, if_false],
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
  instruction.uop id source.nil (source.imm 0 source.nil),
  -- (as_nil) as bs
  instruction.ite (λ a, a = 0) [
    -- 0 [] bs
    instruction.move source.nil (source.imm 1 source.nil)
    -- bs
  ],
  instruction.uop id source.nil (source.imm 1 source.nil),
  -- (bs_nil) [1 a as] bs
  instruction.ite (λ a, a = 0) [
    -- 0 [1 a as] []
    instruction.move source.nil (source.imm 0 source.nil)
    -- 1 a as
  ],
  -- 0 [1 a as] [1 b bs]
  instruction.swap (source.imm 0 (source.imm 1 source.nil)) (source.imm 1 (source.imm 0 source.nil)),
  -- 0 [1 a b] [1 as bs]
  instruction.copy (source.imm 1 source.nil) source.nil,
  -- 0 [1 a b] [0 [1 a b] [1 as bs]]
  instruction.call cmp (source.imm 0 source.nil),
  -- 0 [(a ≼ b) ? ?] [0 [1 a b] [1 as bs]]
  instruction.uop id source.nil (source.imm 0 source.nil),
  -- (a ≼ b) [(a ≼ b) ? ?] [0 [1 a b] [1 as bs]]
  instruction.ite (λ a, a = 1) [
    -- a ≼ b
    -- 1 [1 null null] [0 [1 a b] [1 as bs]]
    instruction.move (source.imm 0 (source.imm 0 source.nil)) (source.imm 1 (source.imm 1 (source.imm 0 source.nil))),
    -- 1 [1 as null] [0 [1 a b] [1 null bs]]
    instruction.const (source.imm 0 (source.imm 1 source.nil)) 1,
    -- 1 [1 as [1 null null]]] [0 [1 a b] [1 null bs]]
    instruction.move (source.imm 0 (source.imm 1 (source.imm 0 source.nil))) (source.imm 1 (source.imm 0 (source.imm 1 source.nil))),
    -- 1 [1 as [1 b null]]] [0 [1 a null] [1 null bs]]
    instruction.move (source.imm 0 (source.imm 1 (source.imm 1 source.nil))) (source.imm 1 (source.imm 1 (source.imm 1 source.nil))),
    -- 1 [1 as [1 b bs]]] [0 [1 a null] [1 null null]]
    instruction.recurse (source.imm 0 source.nil),
    -- 1 xs [0 [1 a null] [1 null null]]
    instruction.move (source.imm 1 (source.imm 0 (source.imm 1 source.nil))) (source.imm 0 source.nil),
    -- 1 null [0 [1 a xs] [1 null null]]
    instruction.move source.nil (source.imm 1 (source.imm 0 source.nil))
    -- 1 a xs
  ],
  -- ¬ a ≼ b
  -- 0 [0 null null] [0 [1 a b] [1 as bs]]
  instruction.const (source.imm 0 source.nil) 1,
  -- 0 [1 null null] [0 [1 a b] [1 as bs]]
  instruction.move (source.imm 0 (source.imm 1 source.nil)) (source.imm 1 (source.imm 1 (source.imm 1 source.nil))),
  -- 0 [1 null bs] [0 [1 a b] [1 as null]]
  instruction.const (source.imm 0 (source.imm 0 source.nil)) 1,
  -- 0 [1 [1 null null] bs] [0 [1 a b] [1 as null]]
  instruction.move (source.imm 0 (source.imm 0 (source.imm 0 source.nil))) (source.imm 1 (source.imm 0 (source.imm 0 source.nil))),
  -- 0 [1 [1 a null] bs] [0 [1 null b] [1 as null]]
  instruction.move (source.imm 0 (source.imm 0 (source.imm 1 source.nil))) (source.imm 1 (source.imm 1 (source.imm 0 source.nil))),
  -- 0 [1 [1 a as] b]] [0 [1 null b] [1 null null]]
  instruction.recurse (source.imm 0 source.nil),
  -- 0 xs [0 [1 null b] [1 null null]]
  instruction.move (source.imm 1 (source.imm 0 (source.imm 0 source.nil))) (source.imm 1 (source.imm 0 (source.imm 1 source.nil))),
  -- 0 xs [0 [1 b null] [1 null null]]
  instruction.move (source.imm 1 (source.imm 0 (source.imm 1 source.nil))) (source.imm 0 source.nil),
  -- 0 null [0 [1 b xs] [1 null null]]
  instruction.move source.nil (source.imm 1 (source.imm 0 source.nil))
  -- 1 b xs
]

def merge_trace {α: Type*} [complexity.has_encoding (runtime_model μ) α] (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp] (pcmp: program μ):
  list α → list α → trace μ
| [] b := ⟨ encode b, 3, [], [] ⟩
| (a::as) [] := ⟨ encode (a::as), 5, [], [] ⟩
| (a::as) (b::bs) := if (fcmp a b)
  then ⟨ encode (list.merge fcmp (a::as) (b::bs)), 16, [(pcmp, (encode (a, b)))], [encode (as, b::bs)] ⟩
  else ⟨ encode (list.merge fcmp (a::as) (b::bs)), 18, [(pcmp, (encode (a, b)))], [encode (a::as, bs)] ⟩

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
    { unfold merge instruction.uop instruction.move },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_pair, encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      memory.setm_setv, memory.setv_setv, memory.getv_null,
      memory.getm_setm, memory.getm_setm_nz,
      memory.getv_setm, memory.getv_setv, eq_self_iff_true, if_true],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply end_trace,
    cases bs;
    simp only [memory.setms, memory.getms, source.get,
      memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm, list.merge] },
  cases bs with b bs,
  { unfold merge_trace,
    apply start_trace,
    { unfold merge instruction.uop instruction.move },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_pair, encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      ← memory.setv_setm, memory.setv_setv, memory.getv_null,
      memory.getm_setm, memory.getm_setm_nz,
      memory.getv_setm, memory.getv_setv, encode_cons, one_ne_zero' μ, if_false],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      memory.setm_setv, memory.setv_setv, memory.getv_null,
      memory.getm_setm, memory.getm_setm_nz,
      memory.getv_setm, memory.getv_setv, eq_self_iff_true, if_true],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply end_trace,
    simp only [memory.setms, memory.getms, source.get,
      memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
      list.merge, ← encode_cons] },
  unfold merge_trace,
  cases hdcmp:dcmp a b,
  { simp only [h_1, if_true],
    apply start_trace,
    { unfold merge instruction.uop instruction.move instruction.swap instruction.copy instruction.const },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_pair, encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      ← memory.setv_setm, memory.setv_setv, memory.getv_null,
      memory.getm_setm, memory.getm_setm_nz,
      memory.getv_setm, memory.getv_setv, encode_cons, one_ne_zero' μ, if_false],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_pair, encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      ← memory.setv_setm, memory.setv_setv, memory.getv_null,
      memory.getm_setm, memory.getm_setm_nz,
      memory.getv_setm, memory.getv_setv, encode_cons, one_ne_zero' μ, if_false],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
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
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      hdcmp, encode_is_false (decidable.is_false h_1),
      memory.setvs, memory.getvs, memory.setms, memory.getms, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      memory.getmp_cons, memory.getmp_nil,
      memory.setmp_cons, memory.setmp_nil,
      memory.setm_setv, memory.setv_setv, memory.getv_null,
      memory.getv_setm, memory.getv_setv,
      memory.getm_setm, memory.getm_setm_nz,
      memory.setm_setm, memory.setm_setm_nz,
      memory.mop,
      zero_ne_one' μ, if_false],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply recurse_trace,
    { simp only [encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
        memory.setvs, memory.getvs, memory.setms, memory.getms, source.get,
        memory.setvp_nil, memory.setvp_cons, memory.getvp_cons, memory.getvp_nil,
        memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil,
        memory.setm_setv, memory.setv_setv, memory.getv_null,
        memory.getv_setm, memory.getv_setv,
        memory.getm_setm, memory.getm_setm_nz,
        memory.getm_setv, memory.getm_null,
        memory.setm_setm, memory.setm_setm_nz,
        memory.mop] },
    { have hres := (ih _ _ (a::as) bs rfl).result,
      rw [merge_trace_result] at hres,
      apply hres,
      rw [← h, list.length_cons, list.length_cons],
      apply nat.lt_succ_self },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply end_trace,
    simp only [encode_nil, encode_cons, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
        memory.setvs, memory.getvs, memory.setms, memory.getms, source.get,
        memory.setvp_nil, memory.setvp_cons, memory.getvp_cons, memory.getvp_nil,
        memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil,
        memory.setm_setv, memory.setv_setv, memory.getv_null,
        memory.getv_setm, memory.getv_setv,
        memory.getm_setm, memory.getm_setm_nz,
        memory.getm_setv, memory.getm_null,
        memory.setm_setm, memory.setm_setm_nz,
        memory.mop, list.merge, h_1, if_false] },
  { simp only [h_1, if_true],
    apply start_trace,
    { unfold merge instruction.uop instruction.move instruction.swap instruction.copy instruction.const },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_pair, encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      ← memory.setv_setm, memory.setv_setv, memory.getv_null,
      memory.getm_setm, memory.getm_setm_nz,
      memory.getv_setm, memory.getv_setv, encode_cons, one_ne_zero' μ, if_false],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_pair, encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      ← memory.setv_setm, memory.setv_setv, memory.getv_null,
      memory.getm_setm, memory.getm_setm_nz,
      memory.getv_setm, memory.getv_setv, encode_cons, one_ne_zero' μ, if_false],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
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
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      hdcmp, encode_is_true (decidable.is_true h_1),
      memory.setvs, memory.getvs, memory.setms, memory.getms, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      memory.getmp_cons, memory.getmp_nil,
      memory.setmp_cons, memory.setmp_nil,
      memory.setm_setv, memory.setv_setv, memory.getv_null,
      memory.getv_setm, memory.getv_setv,
      memory.getm_setm, memory.getm_setm_nz,
      memory.setm_setm, memory.setm_setm_nz,
      memory.mop,
      eq_self_iff_true, if_true],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply recurse_trace,
    { simp only [encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
        memory.setvs, memory.getvs, memory.setms, memory.getms, source.get,
        memory.setvp_nil, memory.setvp_cons, memory.getvp_cons, memory.getvp_nil,
        memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil,
        memory.setm_setv, memory.setv_setv, memory.getv_null,
        memory.getv_setm, memory.getv_setv, memory.null_setv_setm_null,
        memory.getm_setm, memory.getm_setm_nz, memory.getm_setm_nz',
        memory.getm_setv, memory.getm_null, memory.getm_setv,
        memory.setm_setm, memory.setm_setm_nz,
        memory.mop] },
    { have hres := (ih _ _ as (b::bs) rfl).result,
      rw [merge_trace_result] at hres,
      apply hres,
      simpa only [← h, list.length_cons, add_lt_add_iff_right] using nat.lt_succ_self _  },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply end_trace,
    simp only [encode_nil, encode_cons, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
        memory.setvs, memory.getvs, memory.setms, memory.getms, source.get,
        memory.setvp_nil, memory.setvp_cons, memory.getvp_cons, memory.getvp_nil,
        memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil,
        memory.setm_setv, memory.setv_setv, memory.getv_null,
        memory.getv_setm, memory.getv_setv,
        memory.getm_setm, memory.getm_setm_nz,
        memory.getm_setv, memory.getm_null,
        memory.setm_setm, memory.setm_setm_nz,
        memory.mop, list.merge, h_1, if_true] },
end

def merge_sort {μ: Type*} [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)] (cmp: program μ): program μ :=
[ -- l
  instruction.ite (λ a, a = 0) [
    -- list.nil
  ],
  -- 1 a l
  instruction.uop id source.nil (source.imm 1 source.nil),
  -- (l.nil) a l
  instruction.ite (λ a, a = 0) [
    -- 0 a list.nil
    instruction.const source.nil 1
    -- 1 a list.nil
  ],
  -- 1 a [1 b l]
  instruction.move (source.imm 0 source.nil) source.nil,
  -- 0 [1 a [1 b l]] null
  instruction.call (split μ) (source.imm 0 source.nil),
  -- 0 [1 l₁ l₂]
  instruction.move source.nil (source.imm 0 source.nil),
  -- 1 l₁ l₂
  instruction.recurse (source.imm 0 source.nil),
  -- 1 ms₁ l₂
  instruction.swap (source.imm 0 source.nil) (source.imm 1 source.nil),
  -- 1 l₂ ms₁
  instruction.recurse (source.imm 0 source.nil),
  -- 1 ms₂ ms₁
  instruction.swap (source.imm 0 source.nil) (source.imm 1 source.nil),
  -- 1 ms₁ ms₂
  instruction.move (source.imm 0 source.nil) source.nil,
  -- 0 [1 ms₁ ms₂] null
  instruction.call (merge cmp) (source.imm 0 source.nil),
  -- 0 m null
  instruction.move source.nil (source.imm 0 source.nil)
  -- m
]

def merge_sort_trace {α: Type*} [complexity.has_encoding (runtime_model μ) α] (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp] (pcmp: program μ):
  list α → trace μ
| [] := ⟨encode (@list.nil α), 1, [], []⟩
| [a] := ⟨encode [a], 4, [], []⟩
| l := match list.split l with
  | (as, bs) :=
    ⟨encode (list.merge_sort fcmp l), 13,
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
    { unfold merge_sort },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_nil, memory.getv_null, eq_self_iff_true, if_true],
    apply end_trace rfl },
  cases l with b l,
  { apply start_trace,
    { unfold merge_sort instruction.uop instruction.const },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [encode_cons, memory.getv_setm, memory.getv_setv, one_ne_zero' μ, if_false],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    simp only [id, encode_nil, memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      memory.getv_setm, memory.getm_setm, memory.getv_null,
      memory.getv_setv, ← memory.setv_setm, memory.setv_setv,
      fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
      eq_self_iff_true, if_true],
    apply step_trace,
    { unfold thunk.step_over thunk.step },
    { apply thunk.extend_trace₀, unfold thunk.step, refl },
    apply end_trace,
    simp only [memory.setvs, source.get,
      memory.setvp_cons, memory.setvp_nil,
      memory.setv_setm, memory.setv_setv] },
  cases hsplit:(a::b::l).split,
  simp only [merge_sort_trace, hsplit],
  apply start_trace,
  { unfold merge_sort instruction.uop instruction.const instruction.move instruction.swap },
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  simp only [encode_cons, memory.getv_setm, memory.getv_setv, one_ne_zero' μ, if_false],
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  simp only [id, encode_nil, memory.setvs, memory.getvs, source.get,
    memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
    memory.getv_setm, memory.getm_setm, memory.getv_null,
    memory.getv_setv, ← memory.setv_setm, memory.setv_setv,
    fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
    one_ne_zero' μ, if_false],
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  apply call_trace,
  { simp only [source.get, memory.setms, memory.getms,
      memory.getmp_cons, memory.getmp_nil,
      memory.setmp_cons, memory.setmp_nil,
      memory.getm_setm,
      memory.mop] },
  { rw [← encode_cons, ← encode_cons],
    apply program.has_trace.result,
    apply split_has_trace },
  simp only [source.get, memory.setms, memory.getms,
      memory.getmp_cons, memory.getmp_nil,
      memory.setmp_cons, memory.setmp_nil,
      memory.getm_setm, memory.setm_setm,
      memory.mop, split_trace_result, hsplit, encode_pair],
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  apply recurse_trace,
  { simp only [source.get, memory.setms, memory.getms,
        memory.getmp_cons, memory.getmp_nil,
        memory.setmp_cons, memory.setmp_nil,
        memory.getm_setm, memory.setm_setm,
        memory.getm_setm_nz,
        memory.mop] },
  { have hres := (ih _ _ fst rfl).result,
    rw [merge_sort_result] at hres,
    exact hres,
    rw [← hn],
    exact (list.length_split_lt hsplit).left },
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  apply recurse_trace,
  { simp only [source.get, memory.setms, memory.getms,
        memory.getmp_cons, memory.getmp_nil,
        memory.setmp_cons, memory.setmp_nil,
        memory.getm_setm, memory.setm_setm,
        memory.getm_setm_nz',
        memory.mop] },
  { have hres := (ih _ _ snd rfl).result,
    rw [merge_sort_result] at hres,
    exact hres,
    rw [← hn],
    exact (list.length_split_lt hsplit).right },
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  simp only [source.get, memory.setms, memory.getms,
        memory.getmp_cons, memory.getmp_nil,
        memory.setmp_cons, memory.setmp_nil,
        memory.getm_setm, memory.setm_setm,
        memory.getm_setm_nz, memory.getm_setm_nz',
        memory.setm_setm_nz, memory.setm_setm,
        memory.mop],
  apply call_trace,
  { simp only [source.get, memory.setms, memory.getms,
      memory.getmp_cons, memory.getmp_nil,
      memory.setmp_cons, memory.setmp_nil,
      memory.getm_setm,
      memory.mop] },
  { rw [← encode_pair],
    apply program.has_trace.result,
    apply merge_has_trace fcmp,
    exact hcmp },
  apply step_trace,
  { unfold thunk.step_over thunk.step },
  { apply thunk.extend_trace₀, unfold thunk.step, refl },
  apply end_trace,
  simp only [source.get, memory.setms, memory.getms,
      memory.getmp_cons, memory.getmp_nil,
      memory.setmp_cons, memory.setmp_nil,
      memory.getm_setm,
      memory.mop, merge_trace_result,
      list.merge_sort_cons_cons fcmp hsplit],
end

end encoding
end hmem