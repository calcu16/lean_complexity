import Complexity.Cost
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
  cost': (p: Program) → (d: Data) → (∃ r, has_result p d r) → ℕ

instance (m: Model): Setoid m.Data := m.data_equiv
instance (m: Model): Setoid m.Result := m.result_equiv

class Encoding (α: Type _) (Data: Type _) [Setoid Data] where
  encode: α → Data
  encode_inj a b: encode a ≈ encode b → a = b
  decode: Data → Option α
  decode_inv a: decode (encode a) = some a

theorem Encoding.inj' {α: Type _} {Data: Type _} [s: Setoid Data] [en: Encoding α Data] {a b: α}:
  (⟦en.encode a⟧:Quotient s) = ⟦en.encode b⟧ → a = b :=
en.encode_inj _ _ ∘ Quotient.eq.mp

theorem Encoding.inj_iff' {α: Type _} {Data: Type _} [s: Setoid Data] [en: Encoding α Data] {a b: α}:
  (⟦en.encode a⟧:Quotient s) = ⟦en.encode b⟧ ↔ a = b :=
⟨ Encoding.inj', λ h ↦ h ▸ rfl ⟩

def encode {α: Type _} {Data: Type _} [Setoid Data] [en: Encoding α Data]: α → Data := en.encode

def decode (α: Type _) {Data: Type _} [Setoid Data] [en: Encoding α Data]: Data → Option α := en.decode

@[simp] theorem decode_inv {α: Type _} {Data: Type _} [Setoid Data] [en: Encoding α Data] (a: α):
  decode α (encode a:Data) = some a := en.decode_inv _

def Model.totalProgram (m: Model) (p: m.Program) (α: Type _) [Encoding α m.Data]: Prop := ∀ (a: α), ∃ r, m.has_result p (encode a) r

def Model.cost (m: Model) {p: m.Program} {α: Type} [Encoding α m.Data] (h: m.totalProgram p α): CostFunction α ℕ := λ a ↦ m.cost' _ _ (h a)

end Complexity

class Computable {α: Type _} {β: Type} (m: Complexity.Model) [Complexity.Encoding α m.Data] [Complexity.Encoding β m.Result]
    (f: α → β) where
  program: m.Program
  has_result (a: α): m.has_result program (Complexity.encode a) (Complexity.encode (f a))

def Computable.cost {m: Complexity.Model} [Complexity.Encoding α m.Data] [Complexity.Encoding β m.Result] {f: α → β} [computable: Computable m f]: Complexity.CostFunction α ℕ := m.cost λ _ ↦ ⟨_, computable.has_result _⟩

structure Complexity {α: Type _} {β: Type _} (m: Complexity.Model) [Complexity.Encoding α m.Data] [Complexity.Encoding β m.Result] (f: α → β) (cost: Complexity.CostFunction α ℕ) where
  computable: Computable m f
  cost_le: computable.cost ≤ cost
