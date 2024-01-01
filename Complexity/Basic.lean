import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Tactic

namespace Complexity

structure Model where
  Program: Type _
  Data: Type _
  Result: Type _
  [data_equiv: Setoid Data]
  [result_equiv: Setoid Result]
  has_result: Program → Data → Result → Prop
  has_result_inj {p: Program} {d₀ d₁: Data} {r₀ r₁: Result}:
    d₀ ≈ d₁ → has_result p d₀ r₀ → has_result p d₁ r₁ → r₀ ≈ r₁

instance (m: Model): Setoid m.Data := m.data_equiv
instance (m: Model): Setoid m.Result := m.result_equiv

class Encoding (α: Type _) (Data: Type _) [Setoid Data] where
  encode: α → Data
  inj (a b): encode a ≈ encode b → a = b

theorem Encoding.inj' {α: Type _} {Data: Type _} [s: Setoid Data] [en: Encoding α Data] {a b: α}:
  (⟦en.encode a⟧:Quotient s) = ⟦en.encode b⟧ → a = b :=
en.inj _ _ ∘ Quotient.eq.mp

theorem Encoding.inj_iff' {α: Type _} {Data: Type _} [s: Setoid Data] [en: Encoding α Data] {a b: α}:
  (⟦en.encode a⟧:Quotient s) = ⟦en.encode b⟧ ↔ a = b :=
⟨ Encoding.inj', λ h ↦ h ▸ rfl ⟩

def encode {α: Type _} {Data: Type _} [Setoid Data] [en: Encoding α Data]: α → Data := en.encode

def Model.totalProgram (m: Model) (p: m.Program) (α: Type _) [Encoding α m.Data]: Prop := ∀ (a: α), ∃ r, m.has_result p (encode a) r

end Complexity

class Computable {α: Type _} {β: Type} (m: Complexity.Model) [Complexity.Encoding α m.Data] [Complexity.Encoding β m.Result]
    (f: α → β) where
  program: m.Program
  has_result (a: α): m.has_result program (Complexity.encode a) (Complexity.encode (f a))

-- structure Complexity {α: Type _} {β: Type _} (m: Complexity.CostedModel) [Complexity.Encoding α m.Data] [Complexity.Encoding β m.Result] (f: α → β) (cost: α → m.Cost) where
--   computable: Computable m.toModel f
--   cost_le a: m.cost ⟨_, computable.has_result a⟩ ≤ cost a
