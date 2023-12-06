import Mathlib.Init.Algebra.Order
import Mathlib.Tactic

namespace Complexity

structure Model where
  Program: Type
  Data: Type
  Result: Type
  Cost: Type
  data_equiv: Setoid Data
  result_equiv: Setoid Result
  cost_preorder: Preorder Cost
  cost_add: AddCommMonoid Cost
  apply: Program → Data → Program
  has_cost: Program → Cost → Prop
  result: {p: Program} → {c: Cost} → (h: has_cost p c) → Result
  cost_pos: ∀ (c₀ c₁: Cost), c₀ ≤ c₀ + c₁
  has_cost_mono: ∀ p c₀ c₁, has_cost p c₀ → c₀ ≤ c₁ → has_cost p c₁

instance (m: Model): Setoid m.Data := m.data_equiv
instance (m: Model): Setoid m.Result := m.result_equiv
instance (m: Model): Preorder m.Cost := m.cost_preorder
instance (m: Model): AddCommMonoid m.Cost := m.cost_add

def Cost.scalar_mul (m: Model): ℕ → m.Cost → m.Cost
| 0, _ => 0
| n+1, c => Cost.scalar_mul m n c + c

instance (m: Model): HMul ℕ m.Cost m.Cost := ⟨ Cost.scalar_mul m ⟩

class Encoding (α: Type _) (Data: Type _) [Setoid Data] where
  encode: α → Data
  inj: ∀ {a b}, encode a ≈ encode b → a = b

theorem Encoding.inj' {α: Type _} {Data: Type _} [s: Setoid Data] [en: Encoding α Data] {a b: α}:
  (⟦en.encode a⟧:Quotient s) = ⟦en.encode b⟧ → a = b :=
en.inj ∘ Quotient.eq.mp

theorem Encoding.inj_iff' {α: Type _} {Data: Type _} [s: Setoid Data] [en: Encoding α Data] {a b: α}:
  (⟦en.encode a⟧:Quotient s) = ⟦en.encode b⟧ ↔ a = b :=
⟨ Encoding.inj', λ h ↦ h ▸ rfl ⟩

inductive Witness (m: Model): {φ: Type _} → {θ: Type _} → m.Program → φ → θ → Prop
| result {α: Type _} [en: Encoding α m.Result] (p: m.Program) (c: m.Cost) (ret: α)
  (hc: m.has_cost p c) (hr: (m.result hc) = en.encode ret): Witness m p ret c
| apply {α: Type _} {β: Type _} {γ: Type _} [en: Encoding α m.Data] (p: m.Program) (f: α → β) (fc: α → γ)
  (harg: (a: α) → Witness m (m.apply p (en.encode a)) (f a) (fc a)): Witness m p f fc

end Complexity

def Complexity {φ: Type _} {θ: Type _} (m: Complexity.Model) (f: φ) (cost: θ): Prop :=
  ∃ program, Complexity.Witness m program f cost