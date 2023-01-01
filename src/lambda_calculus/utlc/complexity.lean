import lambda_calculus.distance
import lambda_calculus.utlc.basic
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.beta.distance
import lambda_calculus.utlc.encoding.basic
import lambda_calculus.utlc.encoding.nat

namespace lambda_calculus
namespace complexity

open utlc

namespace hidden

inductive encodable_function: Type 1
| result: Π {α: Type}, has_encoding α → encodable_function
| application: Π {α: Type}, has_encoding α → encodable_function → encodable_function

def unwrap: encodable_function → Type
| (@encodable_function.result α _) := α
| (@encodable_function.application α _ b) := α → unwrap b

def is_encoded_function (α: Type) :=  { value: encodable_function // unwrap value = α }

class has_encodable_function (α: Type) := (value: is_encoded_function α)

instance encodable_result (α: Type) [f: has_encoding α]:
    has_encodable_function α :=
  ⟨ ⟨ encodable_function.result f, by simp [unwrap] ⟩ ⟩

instance encodable_application (α: Type) [f: has_encoding α] (β: Type) [g: has_encodable_function β]:
    has_encodable_function (α → β) :=
  ⟨ ⟨ encodable_function.application f g.value.1,
    begin
      simp [unwrap],
      apply show ∀ x y z: Type, y = z → (x → y) = (x → z), by {intros _ _ _ p, rw[p]},
      exact g.value.2,
    end ⟩ ⟩

def nat_complexity: encodable_function → Type
| (encodable_function.result _) := ℕ
| (@encodable_function.application α _ b) := α → (nat_complexity b)

def nat_complexity' (α : Type) [f: has_encodable_function α] := nat_complexity f.value.1

theorem unwrap_has_encodable {α: Type} (a: has_encodable_function α): α = unwrap a.value.1 := a.value.2.symm

def witness_complexity: Π (a : encodable_function), (unwrap a) → utlc → (nat_complexity a) → Prop
| (encodable_function.result e) := λ f g n, utlc.β.distance_le n g (@encode _ e f)
| (@encodable_function.application α e b) := λ f g n, ∀ a : α, witness_complexity b (f a) (g·(@encode α e a)) (n a)

end hidden

def complexity_le {α: Type} [a: hidden.has_encodable_function α] (f: α) (n: (hidden.nat_complexity' α)): Prop :=
  ∃ g: utlc, hidden.witness_complexity a.value.1 (cast (hidden.unwrap_has_encodable a) f) g n

example : complexity_le nat.add (λ n m, (6:ℕ)) :=
begin
  use encoding.nat.add,
  intros x y,
  apply utlc.encoding.nat.add_distance_le
end

end complexity
end lambda_calculus