import lambda_calculus.utlc.beta.distance
import complexity.basic

/-
 - Define complexity in terms of the number of β reductions
 - Programs and data need to be closed,
 -  additionally data needs to be fully reduced such that equivalence implies equality
 -/

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
   λ prog x y cx cy hx hy, reduced_equiv_inj x.proof.right y.proof.right (equiv_trans (equiv_symm (equiv_of_distance_le hx)) (equiv_of_distance_le hy)),
   λ prog data c₀ c₁, distance_le_mono' ⟩

@[simp] theorem program_is_closed (a: encoded_program):
  a.value.closed := a.proof

@[simp] theorem program_is_closed_below (a: encoded_program):
  ∀ n, a.value.closed_below n :=
  λ n, closed_below_mono' a.proof (nat.zero_le _)

@[simp] theorem program_ignores_shift (a: encoded_program) (n: ℕ):
  a.value ↑¹ n = a.value := by rw [shift_of_closed a.proof]

@[simp] theorem program_ignores_substitution (a: encoded_program) (n: ℕ) (g: utlc):
  has_substitution.substitution a.value n g = a.value := by rw [substitution_of_closed a.proof]
  

@[simp] theorem data_is_closed (a: encoded_data):
  a.value.closed := a.proof.left

@[simp] theorem data_is_closed_below (a: encoded_data):
  ∀ n, a.value.closed_below n :=
  λ n, closed_below_mono' a.proof.left (nat.zero_le _)

@[simp] theorem data_is_closed_below' {α: Type}
  [f: complexity.has_encoding distance_model α]
  (a: α) : ∀ n, (f.value.encode a).value.closed_below n :=
  λ n, closed_below_mono' (f.value.encode a).proof.left (nat.zero_le _)

@[simp] theorem data_is_reduced (a: encoded_data):
   reduced a.value := a.proof.right

@[simp] theorem data_is_reduced' {α: Type}
  [f: complexity.has_encoding distance_model α]
  (a: α) : reduced (f.value.encode a).value :=
  (f.value.encode a).proof.right

@[simp] theorem value_inj (a b: encoded_data):
  a ≈ b ↔ a.value = b.value := by refl

@[simp] theorem data_value_inj {α: Type}
  [f: complexity.has_encoding distance_model α] (a b: α):
  (f.value.encode a).value = (f.value.encode b).value ↔ a = b :=
by rw [← value_inj, complexity.encoding.inj_iff]

@[simp] theorem data_ignores_shift (a: encoded_data) (n: ℕ):
  a.value ↑¹ n = a.value := by rw [shift_of_closed a.proof.left]

@[simp] theorem data_ignores_substitution (a: encoded_data) (n: ℕ) (g: utlc):
  has_substitution.substitution a.value n g = a.value := by rw [substitution_of_closed a.proof.left]

end encoding
end β
end utlc
end lambda_calculus