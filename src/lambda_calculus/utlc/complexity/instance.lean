import lambda_calculus.utlc.complexity.basic

namespace lambda_calculus
namespace complexity

open complexity.complexity_le
open utlc

structure is_complexity {α: Type} [has_encodable_function α] (f: α):=
mk :: (cost : cost_function' α) (inv : complexity_le f cost)

class has_complexity {α: Type} [has_encodable_function α] (f: α) :=
  (value: is_complexity f)

def complexity {α: Type} [has_encodable_function α]  (f: α) [cf: has_complexity f] := 
  cf.value.1

instance value_complexity (α: Type) [has_encoding α] (a: α): has_complexity a :=
  ⟨ ⟨ (0:ℕ), (value_complexity_le _) ⟩ ⟩

instance compose_complexity (α β γ: Type) [α_en: has_encoding α] [β_en: has_encoding β] [γ_en: has_encodable_function γ]
  (f: α → β) (g: β → γ) [cf: has_complexity f] [cg: has_complexity g] : has_complexity (g∘f) :=
begin
  fconstructor,
  fconstructor,
  swap,
  apply compose_complexity_le β _ cf.value.2 cg.value.2,
  refl,
  { intro a, refl },
end

instance iteration_complexity (α: Type) [α_en: has_encoding α]
  (f: α → α) [cf: has_complexity f]: has_complexity (nat.iterate f) :=
begin
  fconstructor,
  fconstructor,
  swap,
  apply iteration_complexity_le,
  apply cf.value.2,
  refl,
  { intros a b, refl },
end

instance flip_complexity (α β γ: Type) [α_en: has_encoding α] [β_en: has_encoding β] [γ_en: has_encoding γ]
  (f: α → β → γ) [cf: has_complexity f]: has_complexity (flip f) :=
begin
  fconstructor,
  fconstructor,
  swap,
  apply flip_complexity_le,
  apply cf.value.2,
  refl,
  { intros a b, refl },
end

end complexity
end lambda_calculus