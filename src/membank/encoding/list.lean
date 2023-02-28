import tactic
import membank.basic
import complexity.basic
import complexity.core
import membank.encoding.basic

namespace membank
namespace encoding

universe u

variables {μ: Type u} [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]
local attribute [simp] application_def' program.apply stack.step bank.getmp bank.getm bank.getv bank.setmp source.getv get_push_arg_0 get_push_arg_1 set_push_arg_0 set_push_arg_1 frame.setm
local attribute [simp] stack.step_helper get_push_arg_v

def encode_list {α: Type*} [complexity.has_encoding (runtime_model μ) α]: list α → bank μ
| [] := bank.null
| (x::xs) := bank.mem 1 (λ n, ite (n = 0) (complexity.encode (runtime_model μ) x) (ite (n = 1) (encode_list xs) bank.null))

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

  -- theorem split_sound {α: Type*} [complexity.has_encoding (runtime_model μ) α] (a: list α):
  --   (split μ).costed_result (push_arg (encode_list a) bank.null) (8 * a.length + 2) (push_arg (encode_list (list.split a).fst) (encode_list (list.split a).snd)) :=
  -- begin
  --   induction a,
  --   simp [program.costed_result, split],


    
  -- end

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

example : ∀ n, Σ x : fin n, 

end encoding
end membank