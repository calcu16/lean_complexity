import Complexity.Asymptotic
import Complexity.Cost
import Mathlib.Tactic

/-!
This file defines a Complexity class which matches a lean function with its complexity
for a given computational model.
-/

namespace Complexity

/--
A computation model.

Consists of a Program type, a Data type (for input) and Result type (for output),
and an Cost type. The Data and Result types can be different, but it is more
convienent if they are the same.

The Data and Result types are allowed to have a more general notion of equals via Setoids.
For convience the Cost type should be
- CanonicallyOrdered (can't have negative costs)
- Lattice (given two costs we should be able to find a cost ≤ and ≥ both)
- Semiring, we should be able to add and multiple costs together

Given a Program and input Data we should be able to get a Result.
Since not all Programs halt, and given an arbitrary (Program, Data) pair
on a turing complete model its impossible to prove whether it halts this
is provided in Prop form instead instead with a functional requirement on the Prop.

Finally, given a proof that the program halts on data, what was the cost of that computation.

## TODO
Does it make more sense to have Cost be a semiring, or to HMul with ℕ

-/
structure Model where
  Program: Type _
  Data: Type _
  Result: Type _
  Cost: Type _
  [data_equiv: Setoid Data]
  [result_equiv: Setoid Result]
  [colcs: CanonicallyOrderedLatticeCommSemiring Cost]
  has_result: Program → Data → Result → Prop
  has_result_isFunc {p: Program} {d₀ d₁: Data} {r₀ r₁: Result}:
    d₀ ≈ d₁ → has_result p d₀ r₀ → has_result p d₁ r₁ → r₀ ≈ r₁
  cost': (p: Program) → (d: Data) → (∃ r, has_result p d r) → Cost

instance (m: Model): Setoid m.Data := m.data_equiv
instance (m: Model): Setoid m.Result := m.result_equiv
instance (m: Model): CanonicallyOrderedLatticeCommSemiring m.Cost := m.colcs

/--
In order to prove stuff about lean functions, we need to be able
to encode lean types into the data type. The Encoding should be injective relative
to the Model's equivalence relation.

For conviencience we also require a (presumably computable) decode operator
to be able to go the other direction.
-/
class Encoding (α: Type _) (Data: Type _) [Setoid Data] where
  encode: α → Data
  encode_inj a b: encode a ≈ encode b → a = b

theorem Encoding.inj' {α: Type _} {Data: Type _} [s: Setoid Data] [en: Encoding α Data] {a b: α}:
  (⟦en.encode a⟧:Quotient s) = ⟦en.encode b⟧ → a = b :=
en.encode_inj _ _ ∘ Quotient.eq.mp

theorem Encoding.inj_iff' {α: Type _} {Data: Type _} [s: Setoid Data] [en: Encoding α Data] {a b: α}:
  (⟦en.encode a⟧:Quotient s) = ⟦en.encode b⟧ ↔ a = b :=
⟨ Encoding.inj', λ h ↦ h ▸ rfl ⟩

def encode {α: Type _} {Data: Type _} [Setoid Data] [en: Encoding α Data]: α → Data := en.encode

class Coding (α: Type _) (Data: Type _) [Setoid Data] extends Encoding α Data where
  decode (d: Data): Option α
  decode_inv: ∀ (a: α), decode (Complexity.encode a) = some a

def decode (α: Type _) {Data: Type _} [Setoid Data] [en: Coding α Data] (d: Data): Option α := en.decode d

@[simp] theorem decode_inv {α: Type _} {Data: Type _} [Setoid Data] [en: Coding α Data] (a: α):
  decode _ (encode a:Data) = some a := en.decode_inv _

@[simp] theorem decode_comp_encode
    {α: Type _} [Setoid Data] [Coding α Data]:
    Complexity.decode α (Data := Data) ∘ Complexity.encode (α := α) (Data := Data) = some :=
  funext λ _ ↦ decode_inv _

noncomputable instance (α: Type _) (Data: Type _) [Setoid Data] [Encoding α Data]: Coding α Data where
  decode m :=
    open Classical in
    if h:∃ (a: α), encode a = m
    then some (Classical.choose h)
    else none
  decode_inv _ :=
    (dif_pos ⟨_, rfl⟩).trans
    (congrArg some (Encoding.inj'
      (congrArg _ (Classical.choose_spec (⟨_, rfl⟩:∃ _, _ = encode _)))))

instance [Setoid Data] [h: Coding α Data]: Encoding α Data := h.toEncoding

/-- Given a type, this program always halts on all encodings of the type -/
def Model.totalProgram (m: Model) (p: m.Program) (α: Type _) [Encoding α m.Data]: Prop := ∀ (a: α), ∃ r, m.has_result p (encode a) r

/-- Given a total program, get the cost in a CostFunction form -/
def Model.cost (m: Model) {p: m.Program} {α: Type} [Encoding α m.Data] (h: m.totalProgram p α): CostFunction α m.Cost := λ a ↦ m.cost' _ _ (h a)

/-- Proof that a lean function can be computed by a model -/
class Computable {α: Type _} {β: Type} (m: Complexity.Model) [Complexity.Encoding α m.Data] [Complexity.Encoding β m.Result]
    (f: α → β) where
  program: m.Program
  has_result (a: α): m.has_result program (Complexity.encode a) (Complexity.encode (f a))

def Computable.cost {m: Complexity.Model} [Complexity.Encoding α m.Data] [Complexity.Encoding β m.Result] {f: α → β} [computable: Computable m f]: Complexity.CostFunction α m.Cost := m.cost λ _ ↦ ⟨_, computable.has_result _⟩

end Complexity

/-- Proof that a computable lean function can be computed with a given asymptotic cost

Note: Becuase the asymptotics are proved under Type, this also provides a non-asymptotic upper bound as well.
-/
class Complexity {α: Type _} {β: Type _} (m: Complexity.Model)
    [Complexity.Encoding α m.Data] [Complexity.Encoding β m.Result] (f: α → β)
    (complexity: semiOutParam (Complexity.CostFunction α m.Cost)) extends Complexity.Computable m f where
  cost_ale: toComputable.cost ∈ O(complexity)
