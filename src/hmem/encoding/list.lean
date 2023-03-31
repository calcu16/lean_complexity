import hmem.stack
import hmem.encoding.basic
import hmem.split_cost
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

theorem split_result {α: Type*} [complexity.has_encoding (runtime_model μ) α] (l : list α):
  (split μ).has_result (encode l) (encode (list.split l)) :=
begin
  induction l,
  { apply thunk.apply_step_over',
    { unfold split },
    { unfold thunk.step_over thunk.step },
    simp only [encode_nil, memory.getv_null, eq_self_iff_true, if_true],
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step instruction.const },
    simp only [memory.setvs, source.get, memory.setvp_nil],
    simp only [list.split, encode_pair, encode_nil, memory.null_setv_setm_null],
    exact ⟨1, rfl⟩, },
  { apply thunk.apply_step_over',
    { unfold split },
    { unfold thunk.step_over thunk.step },
    simp only [encode_cons, memory.getv_setm, memory.getv_setv, one_ne_zero, if_false],
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step instruction.swap },
    simp only [memory.mop, memory.setms, memory.getms, source.get,
      memory.setmp_nil, memory.setmp_cons, memory.setm_setm,
      memory.getmp_nil, memory.getmp_cons,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
      memory.setm_setm_ne _ 1 0 _ _ (one_ne_zero' μ)],
    apply thunk.apply_step_over_recurse,
    { simp only [memory.getms, source.get, memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ)],
      exact l_ih },
    simp only [memory.setm_setm, memory.setm_setm_ne _ 1 0 _ _ (one_ne_zero' μ)],
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step instruction.swap },
    cases hs:l_tl.split,
    simp only [memory.mop, memory.setms, memory.getms, source.get,
      list.split, hs, encode_pair, encode_cons,
      memory.setmp_nil, memory.setmp_cons, memory.setm_setm,
      memory.getmp_nil, memory.getmp_cons,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
      memory.setm_setm, memory.setm_setm_ne _ 1 0 _ _ (one_ne_zero' μ)],
    exact ⟨1, rfl⟩ }
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

theorem merge_result {α: Type*} [complexity.has_encoding (runtime_model μ) α]
  (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp]
  (pcmp: program μ) (hcmp: ∀ (a b: α), pcmp.has_result (encode (a, b)) (encode (dcmp a b))):
  ∀ (as bs: list α), (merge pcmp).has_result (encode (as, bs)) (encode (list.merge fcmp as bs)) :=
begin
  intros as bs,
  simp only [encode_pair],
  induction h:(as.length + bs.length) using nat.strong_induction_on with n ih generalizing as bs,
  cases as,
  { apply thunk.apply_step_over',
    { unfold merge },
    { unfold thunk.step_over thunk.step instruction.uop },
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step },
    simp only [encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      ← memory.setv_setm, memory.setv_setv, memory.getv_null,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
      memory.getv_setm, memory.getv_setv, eq_self_iff_true, if_true],
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step instruction.move },
    cases bs;
    simp only [memory.setms, memory.getms, source.get,
      memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm, list.merge];
    exact ⟨1, rfl⟩ },
  cases bs,
  { apply thunk.apply_step_over',
    { unfold merge },
    { unfold thunk.step_over thunk.step instruction.uop },
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step },
    simp only [encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      ← memory.setv_setm, memory.setv_setv, memory.getv_null,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
      memory.getv_setm, memory.getv_setv, encode_cons, one_ne_zero' μ, if_false],
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step },
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step },
    simp only [encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      ← memory.setv_setm, memory.setv_setv, memory.getv_null,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
      memory.getv_setm, memory.getv_setv, eq_self_iff_true, if_true],
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step instruction.move },
    simp only [memory.setms, memory.getms, source.get,
      memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
      list.merge, ← encode_cons],
    exact ⟨1, rfl⟩ },
  { apply thunk.apply_step_over',
    { unfold merge },
    { unfold thunk.step_over thunk.step instruction.uop },
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step },
    simp only [encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      ← memory.setv_setm, memory.setv_setv, memory.getv_null,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
      memory.getv_setm, memory.getv_setv, encode_cons, one_ne_zero' μ, if_false],
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step },
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step },
    simp only [encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      ← memory.setv_setm, memory.setv_setv, memory.getv_null,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
      memory.getv_setm, memory.getv_setv, encode_cons, one_ne_zero' μ, if_false],
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step instruction.swap },
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step instruction.copy },
    simp only [memory.setms, memory.getms, source.get,
      memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
      memory.setm_setm, memory.setm_setm_ne _ 1 0 _ _ (one_ne_zero' μ),
      memory.mop],
    apply thunk.apply_step_over_call,
    { simp only [memory.getms, source.get,
        memory.getmp_cons, memory.getmp_nil,
        memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ)],
      rw [← encode_pair],
      apply hcmp },
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step },
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step },
    simp only [encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
      memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      ← memory.setv_setm, memory.setv_setv, memory.getv_null,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
      memory.setm_setm, memory.setm_setm_ne _ 1 0 _ _ (one_ne_zero' μ)],
    cases hcmp:dcmp as_hd bs_hd,
    { rw[encode_is_false (decidable.is_false h_1)],
      simp [memory.getv_setm, memory.getv_setv, memory.getv_null],
      apply thunk.apply_step_over,
      { unfold thunk.step_over thunk.step instruction.const },
      apply thunk.apply_step_over,
      { unfold thunk.step_over thunk.step instruction.move },
      apply thunk.apply_step_over,
      { unfold thunk.step_over thunk.step },
      apply thunk.apply_step_over,
      { unfold thunk.step_over thunk.step },
      apply thunk.apply_step_over,
      { unfold thunk.step_over thunk.step },
      simp only [encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
        memory.setvs, memory.setms, memory.getvs, memory.getms, source.get,
        memory.setvp_cons, memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
        memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil, memory.mop,
        ← memory.setv_setm, memory.setv_setv, memory.getv_null,
        memory.getm_setv, memory.getm_null, memory.null_setv_setm_null,
        memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
        memory.setm_setm, memory.setm_setm_ne _ 1 0 _ _ (one_ne_zero' μ)],
      apply thunk.apply_step_over_recurse,
      { simp only [memory.getms, source.get, memory.getmp_cons, memory.getmp_nil,
           memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ)],
        rw [← encode_cons, ← encode_pair],
        apply ih _ _ _ _ rfl,
        simpa only [← h, list.length_cons, ← nat.add_assoc] using nat.lt_succ_self _ },
      apply thunk.apply_step_over,
      { unfold thunk.step_over thunk.step },
      apply thunk.apply_step_over,
      { unfold thunk.step_over thunk.step },
      apply thunk.apply_step_over,
      { unfold thunk.step_over thunk.step },
      simp only [
        list.merge, h_1, if_false,
        memory.setms, memory.getms, source.get,
        memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil, memory.mop,
        memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
        memory.setm_setm, memory.setm_setm_ne _ 1 0 _ _ (one_ne_zero' μ)],
      exact ⟨1, rfl⟩ },
    { rw[encode_is_true (decidable.is_true h_1)],
      simp [memory.getv_setm, memory.getv_setv, memory.getv_null],
      apply thunk.apply_step_over,
      { unfold thunk.step_over thunk.step instruction.move },
      apply thunk.apply_step_over,
      { unfold thunk.step_over thunk.step instruction.const },
      apply thunk.apply_step_over,
      { unfold thunk.step_over thunk.step },
      apply thunk.apply_step_over,
      { unfold thunk.step_over thunk.step },
      simp only [encode_nil, id, vector.map_cons, vector.map_nil, vector.nth_cons_zero, fin.mk_zero,
        memory.setvs, memory.setms, memory.getvs, memory.getms, source.get,
        memory.setvp_cons, memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
        memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil, memory.mop,
        ← memory.setv_setm, memory.setv_setv, memory.getv_null,
        memory.getm_setv, memory.getm_null, memory.null_setv_setm_null,
        memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
        memory.setm_setm, memory.setm_setm_ne _ 1 0 _ _ (one_ne_zero' μ)],
      apply thunk.apply_step_over_recurse,
      { simp only [memory.getms, source.get, memory.getmp_cons, memory.getmp_nil,
           memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
           memory.getm_setm_ne _ 0 _ 1 (one_ne_zero' μ),
           memory.getm_setv, memory.getm_null],
        rw [← encode_cons, ← encode_pair],
        apply ih _ _ _ _ rfl,
        simpa only [← h, list.length_cons, add_lt_add_iff_right] using nat.lt_succ_self _ },
      apply thunk.apply_step_over,
      { unfold thunk.step_over thunk.step },
      apply thunk.apply_step_over,
      { unfold thunk.step_over thunk.step },
      simp only [
        list.merge, h_1, if_true,
        memory.setms, memory.getms, source.get,
        memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil, memory.mop,
        memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
        memory.setm_setm, memory.setm_setm_ne _ 1 0 _ _ (one_ne_zero' μ)],
      exact ⟨1, rfl⟩ } }
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

theorem merge_sort_result
  {α: Type*} [complexity.has_encoding (runtime_model μ) α]
  (fcmp: α → α → Prop) [dcmp: decidable_rel fcmp]
  (pcmp: program μ) (hcmp: ∀ (a b: α), pcmp.has_result (encode (a, b)) (encode (dcmp a b))):
  ∀ (l: list α), (merge_sort pcmp).has_result (encode l) (encode (list.merge_sort fcmp l)) :=
begin
  intros l,
  induction hn:l.length using nat.strong_induction_on with n ih generalizing l,
  cases l with a l,
  { apply thunk.apply_step_over',
    unfold merge_sort,
    { unfold thunk.step_over thunk.step },
    simp only [encode_nil, memory.getv_null, eq_self_iff_true, if_true, list.merge_sort],
    exact ⟨1, rfl⟩ },
  apply thunk.apply_step_over',
  unfold merge_sort,
  { unfold thunk.step_over thunk.step },
  simp only [encode_cons, memory.getv_setm, memory.getv_setv, (one_ne_zero' μ), if_false],
  apply thunk.apply_step_over,
  { unfold thunk.step_over thunk.step instruction.uop },
  cases l with b l,
  { apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step },
    simp only [id, encode_nil, memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      memory.getv_setm, memory.getm_setm, memory.getv_null,
      memory.getv_setv, ← memory.setv_setm, memory.setv_setv,
      fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
      eq_self_iff_true, if_true],
    apply thunk.apply_step_over,
    { unfold thunk.step_over thunk.step instruction.const },
    simp only [id, encode_nil, memory.setvs, memory.getvs, source.get,
      memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
      memory.getv_setm, memory.getm_setm, memory.getv_null,
      memory.getv_setv, ← memory.setv_setm, memory.setv_setv,
      eq_self_iff_true, if_true],
    unfold list.merge_sort,
    rw [encode_cons],
    exact ⟨1, rfl⟩ },
  apply thunk.apply_step_over,
  { unfold thunk.step_over thunk.step },
  simp only [id, encode_cons, memory.setvs, memory.getvs, source.get,
    memory.setvp_nil, memory.getvp_cons, memory.getvp_nil,
    memory.getv_setm, memory.getm_setm, memory.getv_null,
    memory.getv_setv, ← memory.setv_setm, memory.setv_setv,
    fin.mk_zero, vector.map_cons, vector.nth_cons_zero,
    (one_ne_zero' μ), if_false],
  apply thunk.apply_step_over,
  { unfold thunk.step_over thunk.step instruction.move },
  simp only [memory.setms, memory.getms, source.get,
    memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil,
    memory.mop],
  apply thunk.apply_step_over_call,
  { simp only [memory.getms, source.get,
      memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ)],
    rw [← encode_cons, ← encode_cons],
    apply split_result },
  apply thunk.apply_step_over,
  { unfold thunk.step_over thunk.step },
  simp only [memory.getms, memory.setms, source.get,
    memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil,
    memory.setm_setm, memory.getm_setm ],
  cases e : list.split (a::b::l) with l₁ l₂,
  simp only [e, encode_pair],
  apply thunk.apply_step_over_recurse,
  { simp only [memory.getms, source.get,
      memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ)],
    apply ih _ _ _ rfl,
    exact hn ▸ (list.length_split_lt e).left },
  apply thunk.apply_step_over,
  { unfold thunk.step_over thunk.step instruction.swap },
  simp only [memory.getms, memory.setms, source.get,
    memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil,
    memory.setm_setm, memory.getm_setm,
    memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
    memory.setm_setm, memory.setm_setm_ne _ 1 0 _ _ (one_ne_zero' μ),
    memory.mop ],
  apply thunk.apply_step_over_recurse,
  { simp only [memory.getms, source.get,
      memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm, memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ)],
    apply ih _ _ _ rfl,
    exact hn ▸ (list.length_split_lt e).right },
  apply thunk.apply_step_over,
  { unfold thunk.step_over thunk.step },
  apply thunk.apply_step_over,
  { unfold thunk.step_over thunk.step },
  simp only [memory.getms, memory.setms, source.get,
    memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil,
    memory.setm_setm, memory.getm_setm,
    memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
    memory.setm_setm, memory.setm_setm_ne _ 1 0 _ _ (one_ne_zero' μ),
    memory.mop ],
  rw [← encode_pair],
  apply thunk.apply_step_over_call,
  { simp only [memory.getms, source.get,
      memory.getmp_cons, memory.getmp_nil,
      memory.getm_setm],
      apply merge_result fcmp,
      apply hcmp },
  apply thunk.apply_step_over,
  { unfold thunk.step_over thunk.step },
  simp only [memory.getms, memory.setms, source.get,
    memory.setmp_cons, memory.setmp_nil, memory.getmp_cons, memory.getmp_nil,
    memory.setm_setm, memory.getm_setm,
    memory.getm_setm_ne _ 1 _ 0 (zero_ne_one' μ),
    memory.setm_setm, memory.setm_setm_ne _ 1 0 _ _ (one_ne_zero' μ),
    memory.mop],
  rw [list.merge_sort_cons_cons],
  exact ⟨1, rfl⟩,
  exact e,
end


end encoding
end hmem