import lambda_calculus.distance
import lambda_calculus.utlc.basic
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.beta.distance
import lambda_calculus.utlc.encoding.basic
import lambda_calculus.utlc.encoding.nat

namespace lambda_calculus
namespace complexity

open utlc

lemma ftype_right (α: Type) {β β': Type}: β = β' → (α → β) = (α → β') :=
by { intro p, rw [p] }

namespace hidden

inductive encodable_function: Type 1
| result: Π {α: Type}, has_encoding α → encodable_function
| application: Π {α: Type}, has_encoding α → encodable_function → encodable_function

def unwrap: encodable_function → Type
| (@encodable_function.result α _) := α
| (@encodable_function.application α _ b) := α → unwrap b

def result_type : encodable_function → Type
| (@encodable_function.result α _) := α
| (encodable_function.application _ b) := result_type b

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
      apply ftype_right,
      exact g.value.2,
    end ⟩ ⟩

@[simp] def nat_complexity: encodable_function → Type
| (encodable_function.result _) := ℕ
| (@encodable_function.application α _ b) := α → (nat_complexity b)

@[simp] def nat_complexity' (α : Type) [f: has_encodable_function α] := nat_complexity f.value.1

theorem unwrap_has_encodable {α: Type} (a: has_encodable_function α): α = unwrap a.value.1 := a.value.2.symm

def witness_complexity: Π (a : encodable_function), (unwrap a) → utlc → (nat_complexity a) → Prop
| (encodable_function.result e) := λ f g n, utlc.β.distance_le n g (@encode _ e f)
| (@encodable_function.application α e b) := λ f g n, ∀ a : α, witness_complexity b (f a) (g·(@encode α e a)) (n a)

end hidden

def complexity_le {α: Type} [a: hidden.has_encodable_function α] (f: α) (n: (hidden.nat_complexity' α)): Prop :=
  ∃ g: utlc, g.closed ∧ hidden.witness_complexity a.value.1 (cast (hidden.unwrap_has_encodable a) f) g n

@[simp] def iteration1_complexity_le_combine {α: Type}
  (fz: α) (nz: ℕ)
  (fi: α → α) (ni: α → ℕ): ℕ → ℕ
| 0 := nz + 4
| (n+1) := (ni (fi^[n] fz)) + (iteration1_complexity_le_combine n) + 8

@[simp] def iteration1_complexity_le_combine' {α: Type}
  (fi: α → α) (ni: α → ℕ): α → ℕ → ℕ := λ a, iteration1_complexity_le_combine a 0 fi ni

lemma f_iterate: ∀ {α : Type} (f: α → α) (n : ℕ) (a : α), (f (f^[n] a)) = (f^[n+1] a) :=
begin
  intros α f n a,
  induction n generalizing a,
  simp,
  simp,
  rw [n_ih],
  simp,
end

theorem iteration_complexity_le {α : Type} [has_encoding α]
  {fi: α → α} {ni: α → ℕ} (hi: complexity_le fi ni)
  {niz : α → ℕ → ℕ} (hiz: ∀ a n, iteration1_complexity_le_combine' fi ni a n ≤ niz a n):
    complexity_le (λ (a : α) (n: ℕ), fi^[n] a) niz :=
begin
  rcases hi with ⟨lc, hlc, hi⟩,
  use utlc.encoding.nat.apply_iterate lc,
  split,
  simp [utlc.encoding.nat.apply_iterate, closed],
  exact closed_below_mono hlc (nat.zero_le _),
  intro a,
  intro n,
  apply distance_le_mono _ (hiz a n),
  induction n,
  { simp,
    apply utlc.encoding.nat.apply_iterate_zero_distance_le hlc,
    apply encoding.is_closed },
  { simp,
    apply distance_le_trans',
    apply utlc.encoding.nat.apply_iterate_succ_distance_le hlc,
    apply encoding.is_closed,
    apply distance_le_trans',
    apply utlc.β.dot_distance_le_dot_right,
    apply n_ih,
    specialize hi (fi^[n_n] a),
    simp at hi,
    rw [f_iterate fi] at hi,
    apply hi,
    refl,
    simp,
    ring }
end


end complexity
end lambda_calculus