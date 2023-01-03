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

namespace complexity_le

inductive encodable_function: Type 1
| result: Π {α: Type}, has_encoding α → encodable_function
| application: Π {α: Type}, has_encoding α → encodable_function → encodable_function

@[simp] def unwrap: encodable_function → Type
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

@[simp] def cost_function: encodable_function → Type
| (encodable_function.result _) := ℕ
| (@encodable_function.application α _ b) := α → (cost_function b)

@[simp] def cost_function' (α : Type) [f: has_encodable_function α] := cost_function f.value.1

theorem unwrap_has_encodable {α: Type} (a: has_encodable_function α): α = unwrap a.value.1 := a.value.2.symm

def witness: Π (a : encodable_function), (unwrap a) → utlc → (cost_function a) → Prop
| (encodable_function.result e) := λ f g n, utlc.β.distance_le n g (@encode _ e f)
| (@encodable_function.application α e b) := λ f g n, ∀ a : α, witness b (f a) (g·(@encode α e a)) (n a)

end complexity_le

def complexity_le {α: Type} [a: complexity_le.has_encodable_function α] (f: α) (n: (complexity_le.cost_function' α)): Prop :=
  ∃ g: utlc, g.closed ∧ complexity_le.witness a.value.1 (cast (complexity_le.unwrap_has_encodable a) f) g n

theorem partial_complexity_le {α β: Type} [has_encoding α] [complexity_le.has_encodable_function β]
  {f: α → β} {n: α → (complexity_le.cost_function' β)} (h: complexity_le f n)
  (a: α):
  complexity_le (f a) (n a) :=
begin
  rcases h with ⟨lc, hl, h⟩,
  use lc·(encode a),
  simp [closed],
  refine ⟨ hl , _ ⟩,
  specialize h a,
   have fcast: ∀ {α β γ: Type} (f: α → β) (a: α) (h: (β = γ)), (cast h (f a)) = (cast (ftype_right α h) f) a,
  { intros α β γ f a h,
    finish },
  rw [fcast],
  apply h
end

namespace uncurry_complexity_le
@[simp] def cost_function {α β: Type} [has_encoding α] [has_encoding β]
  (f: α → β → ℕ): ((α × β) → ℕ) :=
  λ ab, 3 + f ab.fst ab.snd

end uncurry_complexity_le

theorem uncurry_complexity_le {α β γ: Type} [has_encoding α] [has_encoding β] [has_encoding γ]
  {f: α → β → γ} {n: α → β → ℕ} (h: complexity_le f n):
  complexity_le (λ ab : (α × β), f ab.fst ab.snd) (uncurry_complexity_le.cost_function n) :=
begin
  rcases h with ⟨lc, hl, h⟩,
  use utlc.encoding.uncurry·lc,
  simp,
  refine ⟨closed_below_mono hl (nat.zero_le _), _⟩,
  intro ab,
  cases ab with a b,
  simp,
  specialize h a b,
  apply distance_le_trans',
  apply utlc.encoding.uncurry_distance_le,
  apply h,
  refl
end

namespace iteration_complexity_le
@[simp] def cost_function {α: Type}
  (fz: α) (nz: ℕ)
  (fi: α → α) (ni: α → ℕ): ℕ → ℕ
| 0 := nz + 5
| (n+1) := (ni (fi^[n] fz)) + (cost_function n) + 10

@[simp] def cost_function' {α: Type}
  (fi: α → α) (ni: α → ℕ): α → ℕ → ℕ := λ a, cost_function a 0 fi ni

lemma f_iterate: ∀ {α : Type} (f: α → α) (n : ℕ) (a : α), (f (f^[n] a)) = (f^[n+1] a) :=
begin
  intros α f n a,
  induction n generalizing a,
  simp,
  simp,
  rw [n_ih],
  simp,
end
end iteration_complexity_le

theorem iteration_complexity_le {α : Type} [has_encoding α]
  {fi: α → α} {ni: α → ℕ} (hi: complexity_le fi ni)
  {niz : α → ℕ → ℕ} (hiz: ∀ a n, iteration_complexity_le.cost_function' fi ni a n ≤ niz a n):
    complexity_le (λ (a : α) (n: ℕ), fi^[n] a) niz :=
begin
  rcases hi with ⟨lc, hlc, hi⟩,
  use utlc.encoding.nat.apply_iterate·lc,
  split,
  simp [utlc.encoding.nat.apply_iterate, closed],
  exact closed_below_mono hlc (nat.zero_le _),
  intro a,
  intro n,
  apply distance_le_mono _ (hiz a n),
  induction n,
  { simp,
    apply utlc.encoding.nat.apply_iterate_zero_distance_le },
  { simp,
    apply distance_le_trans',
    apply utlc.encoding.nat.apply_iterate_succ_distance_le,
    apply distance_le_trans',
    apply utlc.β.dot_distance_le_dot_right,
    apply n_ih,
    specialize hi (fi^[n_n] a),
    simp at hi,
    rw [iteration_complexity_le.f_iterate fi] at hi,
    apply hi,
    refl,
    simp,
    ring }
end

end complexity
end lambda_calculus