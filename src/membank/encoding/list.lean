import tactic
import membank.basic
import complexity.basic
import complexity.core
import membank.encoding.basic
import membank.master

namespace membank
namespace encoding

universe u

variables {μ: Type u} [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]
local attribute [simp] application_def' program.apply stack.step stack.step_helper stack.result source.getv frame.setm
local attribute [simp] bank.getmp bank.setmp bank.getvp bank.setvp
local attribute [simp]  getv_mpair getm_mpair₀ getm_mpair₁ setv_mpair setm_mpair₀ setm_mpair₁ push_arg


def encode_decidable (p: Prop) [decidable p] : bank μ := ite p (bank.null.setv 1) bank.null

instance (p: Prop): complexity.has_encoding (runtime_model μ) (decidable p) :=
begin
  fconstructor,
  fconstructor,
  exact λ d, @encode_decidable _ _ _ _ _ p d,
  refine λ x y, ⟨λ _, _, λ h, _⟩,
  rw eq_iff_true_of_subsingleton,
  trivial,
  apply bank.equiv_refl',
  apply congr_arg,
  exact h,
end

def encode_list {α: Type*} [complexity.has_encoding (runtime_model μ) α]: list α → bank μ
| [] := bank.null
| (x::xs) := mpair 1 (complexity.encode (runtime_model μ) x) (encode_list xs)

instance (α: Type*) [α_en: complexity.has_encoding (runtime_model μ) α]: complexity.has_encoding (runtime_model μ) (list α) :=
⟨ ⟨ encode_list,
begin
  intros x y,
  induction x generalizing y,
  { cases y,
    exact ⟨λ _, rfl, λ _, by refl⟩,
    split,
    { intro h,
      specialize h [],
      revert h,
      simp [encode_list, bank.getvp, bank.getv] },
    exact flip absurd (list.cons_ne_nil _ _).symm },
  cases y,
  { split,
    { intro h,
      specialize h [],
      revert h,
      simp [encode_list, bank.getvp, bank.getv] },
    exact flip absurd (list.cons_ne_nil _ _) },
  split,
  { intro p,
    rw [list.cons.inj_eq, ← complexity.encoding.inj_iff α_en.value, ← x_ih y_tl],
    refine ⟨_, _⟩,
    { unfold encode_list at p,
      have hp := bank.equiv_getm 0 p,
      simp at hp,
      apply hp },
    { unfold encode_list at p,
      have hp := bank.equiv_getm 1 p,
      simp at hp,
      apply hp } },
  { simp,
    intros p q,
    rw [p, q] },
end ⟩ ⟩

@[simp]
theorem mpair_eq (n m: μ) (a b c d: bank μ):
  mpair n a b ≈ mpair m c d ↔ n = m ∧ a ≈ c ∧ b ≈ d :=
begin
  refine ⟨ λ h, ⟨bank.equiv_getv h, _, _⟩, λ h, _ ⟩,
  { apply bank.equiv_getm' 0 h;
    simp [mpair, bank.getm] },
  { apply bank.equiv_getm' 1 h;
    simp [mpair, bank.getm] },
  rw [bank.equiv_iff, h.left],
  refine ⟨ rfl, λ a, _⟩,
  unfold mpair bank.getm,
  split_ifs,
  { exact h.right.left },
  { exact h.right.right },
  exact bank.equiv_refl _,
end

def encode (μ: Type u) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]
  {δ: Type} [complexity.has_encoding (runtime_model μ) δ]: δ → bank μ :=
  complexity.encode (runtime_model μ)

theorem encode_inj {δ: Type} [en: complexity.has_encoding (runtime_model μ) δ] (a b: δ):
  (encode μ a) ≈ (encode μ b) ↔ a = b :=
begin
  unfold encode complexity.encode,
  apply en.value.encode_inj,
end

instance (α β: Type*)  [α_en: complexity.has_encoding (runtime_model μ) α] [β_en: complexity.has_encoding (runtime_model μ) β]:
  complexity.has_encoding (runtime_model μ) (α × β) :=
  ⟨ ⟨ λ ab : (α × β), push_arg (encode μ ab.fst) (encode μ ab.snd),
  begin
    intros a b,
    cases a,
    cases b,
    simp [push_arg, mpair_eq, encode_inj],
  end ⟩ ⟩


notation `<[` l:(foldr ` , ` (h t, push_arg (encode _ h) t) bank.null) `]>` := l

-- splits a list into 2 lists of almost equal length
def split (μ: Type u) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]: program μ :=
[ -- 1 a null
  instruction.binary_op (λ a b, a) [] [source.imm 0] [],
  -- (a.nonnil) a null
  instruction.ite (λ a, a = 0) [
    -- 0 list.nil null
    instruction.move [source.imm 1] [source.imm 0],
    -- 0 list.nil list.nil
    instruction.binary_op (λ a b, 1) [] [] []
    -- 1 list.nil list.nil
  ],
  -- 1 [1 a_hd a_tl] null
  instruction.move [source.imm 1] [source.imm 0, source.imm 0],
  -- 1 [1 a_hd a_tl] a_hd
  instruction.move [source.imm 0, source.imm 0] [source.imm 0, source.imm 1],
  -- 1 [1 a_tl a_tl] a_hd
  instruction.clear [source.imm 0, source.imm 1],
  -- 1 [1 a_tl null] a_hd
  instruction.recurse (source.imm 0),
  -- 1 [1 lhs rhs] a_hd
  instruction.move [source.imm 1] [],
  -- 1 [1 lhs rhs] [1 [1 lhs rhs] a_hd]
  instruction.move [source.imm 0, source.imm 0] [source.imm 1, source.imm 1],
  -- 1 [1 a_hd rhs] [1 [1 lhs rhs] a_hd]
  instruction.move [source.imm 1] [source.imm 1, source.imm 0, source.imm 0]
  -- 1 [1 a_hd rhs] lhs
]

@[simp]
theorem getv_null: (@bank.null μ).getv = 0 := rfl

@[simp]
theorem setv_null: (@bank.null μ).setv 1 = mpair 1 bank.null bank.null := by simp [mpair, bank.setv]

@[simp]
theorem getm_null (a: μ): (@bank.null μ).getm a = bank.null := rfl

theorem split_result {α: Type*} [complexity.has_encoding (runtime_model μ) α] (l : list α):
  program.has_result (split μ) <[l]> (encode μ (list.split l)) :=
begin
  induction l,
  unfold program.has_result,
  apply internal_step_has_result'',
  -- simp only [split, push_arg, complexity.encode, complexity.has_encoding.value],
  -- induction l,
  -- {
  --   simp only [split, list.split, complexity.encode, complexity.has_encoding.value, encode_list, push_arg],
  --   unfold program.has_result program.costed_result program.apply,
  --   repeat {
  --     apply internal_step_has_result',
  --     { unfold internal_step, unfold stack.step_helper },
  --     simp },
  --   refine ⟨1, stack.step_halt'' _ _ _⟩ },
  -- simp only [split, list.split, complexity.encode, complexity.has_encoding.value, encode_list, push_arg],
  -- unfold program.has_result program.costed_result program.apply,
  -- repeat {
  --   apply internal_step_has_result',
  --   { unfold internal_step, unfold stack.step_helper },
  --   simp },
  -- apply internal_step_has_result',
  -- {
  --   unfold internal_step,
  --   simp,
  --   refine ⟨_, ⟨rfl, rfl⟩, l_ih⟩,
  -- },
  -- repeat {
  --   apply internal_step_has_result',
  --   { unfold internal_step, unfold stack.step_helper },
  --   simp },
  -- use 1,
  -- cases list.split l_tl,
  -- simp [encode_list, complexity.encode, complexity.has_encoding.value],
end

-- compare returns 0 if a < b and 1 otherwise 
def merge (p_cmp: program μ): program μ :=
[ -- 1 a [1 b null]]
  instruction.move [source.imm 1] [source.imm 1, source.imm 0],
  -- 1 a b
  instruction.binary_op (λ a b, a) [] [source.imm 0] [],
  -- (a.nonnil) a b
  instruction.ite (λ a, a = 0) [
    -- 0 list.nil b
    instruction.move [] [source.imm 1]
    -- b
  ],
  -- 1 [1 a_hd a_tl] b
  instruction.binary_op (λ a b, a) [] [source.imm 1] [],
  -- (b.nonnil) [1 a_hd a_tl] b
  instruction.ite (λ a, a = 0) [
    -- 0 [1 a_hd a_tl] list.nil
    instruction.move [] [source.imm 0]
    -- [1 a_hd a_tl]
  ],
  -- 1 [1 a_hd a_tl] [1 b_hd b_tl]
  instruction.move [source.imm 1] [],
  -- 1 [1 a_hd a_tl] [1 [1 a_hd a_tl] [1 b_hd b_tl]]
  instruction.clear [source.imm 0, source.imm 1],
  -- 1 [1 a_hd null] [1 [1 a_hd a_tl] [1 b_hd b_tl]]
  instruction.binary_op (λ _ _, 1) [source.imm 0, source.imm 1] [] [],
  -- 1 [1 a_hd [1 null null]] [1 [1 a_hd a_tl] [1 b_hd b_tl]]
  instruction.move [source.imm 0, source.imm 1, source.imm 0] [source.imm 1, source.imm 1, source.imm 0],
  -- 1 [1 a_hd [1 b_hd null]] [1 [1 a_hd a_tl] [1 b_hd b_tl]]
  instruction.call p_cmp (source.imm 0),
  -- 1 [(a_hd ≥ b_hd) null null] [1 [1 a_hd a_tl] [1 b_hd b_tl]]
  instruction.binary_op (λ a _, a) [] [source.imm 0] [],
  -- (a_hd ≥ b_hd) [(a_hd ≥ b_hd) null null] [1 [1 a_hd a_tl] [1 b_hd b_tl]]
  instruction.binary_op (λ _ _, 1) [source.imm 0] [] [],
  -- (a_hd ≥ b_hd) [1 null null] [1 [1 a_hd a_tl] [1 b_hd b_tl]]
  instruction.move [source.imm 0, source.imm 0] [source.imm 1, source.acc, source.imm 1],
  -- (a_hd ≥ b_hd) [1 (a_tl|b_tl) null] [1 [1 a_hd a_tl] [1 b_hd b_tl]]
  instruction.binary_op (λ a _, if a = 0 then 1 else 0) [] [] [],
  -- (a_hd < b_hd) [1 (a_tl|b_tl) null] [1 [1 a_hd a_tl] [1 b_hd b_tl]]
  instruction.binary_op (λ _ _, 1) [source.imm 0, source.imm 1] [] [],
  -- (a_hd < b_hd) [1 (a_tl|b_tl) [1 null null]] [1 [1 a_hd a_tl] [1 b_hd b_tl]]
  instruction.move [source.imm 0, source.imm 1, source.imm 0] [source.imm 1, source.acc],
  -- (a_hd < b_hd) [1 (a_tl|b_tl) [1 (b|a) null]] [1 [1 a_hd a_tl] [1 b_hd b_tl]]
  instruction.recurse (source.imm 0),
  -- (a_hd < b_hd) c_tl [1 [1 a_hd a_tl] [1 b_hd b_tl]]
  instruction.move [source.imm 1, source.acc] [source.imm 0],
  -- (a_hd < b_hd) c_tl [1 c_tl|[1 a_hd a_tl] [1 b_hd b_tl]|c_tl],
  instruction.binary_op (λ a _, if a = 0 then 1 else 0) [] [] [],
  -- (a_hd ≥ b_hd) c_tl [1 c_tl|[1 a_hd a_tl] [1 b_hd b_tl]|c_tl],
  instruction.move [source.imm 0] [source.imm 1, source.acc, source.imm 0],
  -- (a_hd ≥ b_hd) a_hd|b_hd [1 c_tl|[1 a_hd a_tl] [1 b_hd b_tl]|c_tl],
  instruction.binary_op (λ a _, if a = 0 then 1 else 0) [] [] [],
  -- (a_hd < b_hd) c_hd [1 c_tl|[1 a_hd a_tl] [1 b_hd b_tl]|c_tl],
  instruction.move [source.imm 1] [source.imm 1, source.acc],
  -- (a_hd < b_hd) c_hd c_tl
  instruction.binary_op (λ a b, 1) [] [] []
  -- 1 c_hd c_tl
]

-- theorem merge_result {α: Type*} [complexity.has_encoding (runtime_model μ) α] (l₁ l₂: list α) (p_cmp: program μ) (r: α → α → Prop) [decidable_rel r] (hp: p_cmp ≠ []):
--   (∀ a b : α, program.has_result p_cmp (push_arg (complexity.encode (runtime_model μ) b) (push_arg (complexity.encode (runtime_model μ) a) bank.null)) (encode_decidable (r a b))) →
--   program.has_result (merge p_cmp) (push_arg (complexity.encode (runtime_model μ) l₁) (push_arg (complexity.encode (runtime_model μ) l₂) bank.null)) (complexity.encode (runtime_model μ) (@list.merge _ r _ l₁ l₂ )) :=
-- begin
--   intro hcmp,
--   induction hn:(l₁.length + l₂.length) generalizing l₁ l₂,
--   { cases l₁,
--     cases l₂,
--     { simp only [merge, push_arg, encode_list, complexity.encode, complexity.has_encoding.value],
--       unfold program.has_result program.costed_result program.apply,
--       repeat {
--         apply internal_step_has_result',
--         { unfold internal_step, unfold stack.step_helper },
--         simp },
--       refine ⟨1, _⟩,
--       rw [function.iterate_one, stack.step_halt''],
--       simp [list.merge, encode_list] },
--     all_goals {
--       exfalso,
--       revert hn,
--       simp } },
--   cases l₁,
--   { simp only [merge, push_arg, encode_list, complexity.encode, complexity.has_encoding.value],
--     unfold program.has_result program.costed_result program.apply,
--     repeat {
--       apply internal_step_has_result',
--       { unfold internal_step, unfold stack.step_helper },
--       simp },
--     refine ⟨1, _⟩,
--     rw [function.iterate_one, stack.step_halt''],
--     simp [list.merge, encode_list],
--     cases l₂;
--     simp [list.merge] },
--   cases l₂,
--   { simp only [merge, push_arg, encode_list, complexity.encode, complexity.has_encoding.value],
--     unfold program.has_result program.costed_result program.apply,
--     repeat {
--       apply internal_step_has_result',
--       { unfold internal_step, unfold stack.step_helper },
--       simp },
--     refine ⟨1, _⟩,
--     rw [function.iterate_one, stack.step_halt''],
--     simp only [stack.result, encode_list, list.merge],
--     refl },
--   simp only [merge, push_arg, encode_list, complexity.encode, complexity.has_encoding.value],
--   unfold program.has_result program.costed_result program.apply,
--   repeat {
--     apply internal_step_has_result',
--     { unfold internal_step, unfold stack.step_helper },
--     simp },
--   by_cases r l₂_hd l₁_hd,
--   { cases p_cmp,
--     { contradiction },
--     apply internal_step_has_result',
--     { unfold internal_step,
--       simp,
--       refine ⟨_, ⟨rfl, rfl⟩, hcmp _ _⟩ },
--     repeat {
--       apply internal_step_has_result',
--       { unfold internal_step, unfold stack.step_helper },
--       simp },
--     clear hcmp,
--     simp [h, encode_decidable],
--     repeat {
--       apply internal_step_has_result',
--       { unfold internal_step, unfold stack.step_helper },
--       simp },
--     specialize ih l₂_tl (l₁_hd::l₁_tl),
--     simp only [merge, push_arg, encode_list, complexity.encode, complexity.has_encoding.value] at ih,
--     apply internal_step_has_result',
--     { unfold internal_step,
--       simp,
--       refine ⟨_, ⟨rfl, rfl⟩, ih _⟩,
--       clear ih,
--       simp [← nat.add_assoc, nat.succ_eq_add_one] at hn,
--       simp [← hn, ← nat.succ_eq_add_one, nat.succ_add, nat.add_succ],
--       exact nat.add_comm _ _ },
    
    
    




--   },
  
  
  

-- end

def merge_sort (p_cmp: program μ): program μ :=
[ -- 1 a null
  instruction.binary_op (λ a b, a) [] [source.imm 0, source.imm 1] [],
  -- (a.tail.nonnil) a null
  instruction.ite (λ a, a = 0) [
    -- 0 a null
    instruction.move [] [source.imm 0]
    -- a
  ],
  -- 1 [1 a_hd a_tl] null
  instruction.move [source.imm 0] [],
  -- 1 [1 [1 a_hd a_tl] null] null
  instruction.call (split μ) (source.imm 0),
  -- 1 [1 lhs rhs] null
  instruction.move [source.imm 1, source.imm 0] [source.imm 0, source.imm 1],
  -- 1 [1 lhs rhs] [0 rhs null]
  instruction.clear [source.imm 0, source.imm 1],
  -- 1 [1 lhs null] [0 rhs null]
  instruction.recurse (source.imm 0),
  -- 1 sorted_lhs [0 rhs null]
  instruction.move [source.imm 1, source.imm 1] [source.imm 0],
  -- 1 sorted_lhs [0 rhs sorted_lhs]
  instruction.clear [source.imm 0],
  -- 1 null [0 rhs sorted_lhs]
  instruction.move [source.imm 0, source.imm 0] [source.imm 1, source.imm 0],
  -- 1 [0 rhs null] [0 rhs sorted_lhs]
  instruction.binary_op (λ _ _, 1) [source.imm 0] [] [],
  -- 1 [1 rhs null] [0 rhs sorted_lhs]
  instruction.recurse (source.imm 0),
  -- 1 sorted_rhs [0 rhs sorted_lhs]
  instruction.binary_op (λ _ _, 1) [source.imm 1] [] [],
  -- 1 sorted_rhs [1 rhs sorted_lhs]
  instruction.move [source.imm 1, source.imm 0] [source.imm 1, source.imm 1],
  -- 1 sorted_rhs [1 sorted_lhs sorted_lhs]
  instruction.clear [source.imm 1, source.imm 1],
  -- 1 sorted_rhs [1 sorted_lhs null]
  instruction.move [source.imm 0] [],
  -- 1 [1 sorted_rhs [1 sorted_lhs null]] [1 sorted_lhs null]
  instruction.call (merge p_cmp) (source.imm 0),
  -- 1 sorted_a rhs
  instruction.move [] [source.imm 0]
]


end encoding
end membank