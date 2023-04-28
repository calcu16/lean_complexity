import hmem.stack
import hmem.encoding.basic
import hmem.split_cost
import hmem.trace
import complexity.basic

variables {μ: Type*} [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]

namespace hmem
namespace encoding


instance memory_encoding : has_encoding (memory μ) μ :=
⟨ id, λ a b, (memory_equiv_eq_iff _ _ _).mp ⟩

noncomputable instance funencoding {α: Type*} [has_encoding α μ]:
  has_encoding (μ → α) μ :=
begin
  fconstructor,
  exact λ f, quotient.mk (hidden.memory.node (0:μ) (λ u, quotient.out (encode (f u)))),
  intros x y p,
  rw [memory_equiv_eq_iff],
  intro p,
  funext u,
  have h := congr_fun (congr_arg memory.getm p) u,
  rw [memory.getm_mk, memory.getm_mk] at h,
  unfold hidden.getm at h,
  rw [quotient.out_eq, quotient.out_eq] at h,
  apply encode_inj h,
end

instance fin_memory_fun_encoding {α: Type*} [fintype μ] [has_encoding α μ]:
  has_encoding (μ → α) μ :=
begin
  fconstructor,
  exact λ f, quotient.mk (hidden.memory.node (0:μ) (λ u, memory.out (encode (f u)))),
  intros x y,
  rw [memory_equiv_eq_iff],
  intro p,
  funext u,
  have h := congr_fun (congr_arg memory.getm p) u,
  rw [memory.getm_mk, memory.getm_mk] at h,
  unfold hidden.getm at h,
  rw [memory.out_eq, memory.out_eq] at h,
  apply encode_inj h,
end

-- def encode_vector_function {α: Type*} [complexity.has_encoding (runtime_model μ) α] [∀ {β: Type*} [complexity.has_encoding (runtime_model μ) β], complexity.has_encoding (runtime_model μ) (μ → β)]:
--   Π (n: ℕ), (vector μ n → α) → memory μ
-- | 0 f := encode (f vector.nil)
-- | (n+1) f := encode (λ u, encode_vector_function 

-- end


-- def encode_instruction: instruction μ → memory μ
-- | vop {n: ℕ} (op: vector α n → α) (dst: source α) (src: vector (source α) n): instruction
-- | mop (op: hmem.instruction.memory_operation) (dst src: source α): instruction
-- | clear (dst: source α): instruction
-- | ite {n: ℕ} (cond: vector α n → Prop) [Π {v}, decidable (cond v)] (src: vector (source α) n) (branch: list instruction): instruction
-- | call (func: list instruction) (dst src: source α): instruction
-- | recurse (dst src: source α): instruction

end encoding
end hmem