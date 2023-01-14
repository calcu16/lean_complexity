import lambda_calculus.utlc.beta.distance
import complexity.basic

namespace lambda_calculus
namespace utlc
namespace β
namespace encoding

structure encoded_program :=
mk :: (value: utlc) (proof: value.closed)

structure encoded_data :=
mk :: (value: utlc) (proof: value.closed ∧ β.reduced value)

instance : has_equiv encoded_data := ⟨ λ a b : encoded_data, a.value = b.value ⟩

local attribute [reducible] closed

def distance_model : complexity.model encoded_program encoded_data ℕ :=
 ⟨ λ prog data cost, distance_le cost prog.value data.value,
   λ prog data, ⟨ prog.value·data.value, by simp [closed, prog.proof, data.proof.left] ⟩,
   λ prog data c₀ c₁, distance_le_mono' ⟩

  
@[simp] theorem data_is_closed_below (a: encoded_data):
  ∀ n, a.value.closed_below n :=
  λ n, closed_below_mono a.proof.left (nat.zero_le _)

@[simp] theorem data_is_closed_below' {α: Type}
  [f: complexity.has_encoding distance_model α]
  (a: α) : ∀ n, (f.value.encode a).value.closed_below n :=
  λ n, closed_below_mono (f.value.encode a).proof.left (nat.zero_le _)

@[simp] theorem data_is_reduced (a: encoded_data):
   reduced_of head_reduced a.value := a.proof.right

@[simp] theorem data_is_reduced' {α: Type}
  [f: complexity.has_encoding distance_model α]
  (a: α) : reduced_of head_reduced (f.value.encode a).value :=
  (f.value.encode a).proof.right

@[simp] theorem value_inj (a b: encoded_data):
  a ≈ b ↔ a.value = b.value := by refl

@[simp] theorem data_value_inj {α: Type}
  [f: complexity.has_encoding distance_model α] (a b: α):
  (f.value.encode a).value = (f.value.encode b).value ↔ a = b :=
by rw [← value_inj, complexity.encoding.inj_iff]

end encoding
end β
end utlc
end lambda_calculus