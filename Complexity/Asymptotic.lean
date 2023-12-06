import Complexity.Basic
namespace Complexity

inductive ConstantWitness (m: Model) (c₀: m.Cost): {φ: Type _} → m.Program → φ → Prop
| result {α: Type _} [en: Encoding α m.Result] (p: m.Program) (ret: α)
  (hc: m.has_cost p c₀) (hr: (m.result hc) = en.encode ret): ConstantWitness m c₀ p ret
| apply {α: Type u} {β: Type u} [en: Encoding α m.Data] (p: m.Program) (f: α → β)
  (harg: (a: α) → ConstantWitness m c₀ (m.apply p (en.encode a)) (f a)): ConstantWitness m c₀ p f

def Constant {α: Type _} (m: Complexity.Model) (f: α): Prop :=
  ∃ c₀ p, ConstantWitness m c₀ p f

inductive AsymptoticWitness (m: Model) (n: ℕ) (c₀: m.Cost): {φ: Type _} → {θ: Type _} → m.Program → φ → θ → Prop
| result {α: Type _} [en: Encoding α m.Result] (p: m.Program) (c: m.Cost) (ret: α)
  (hc: m.has_cost p (n * c + c₀)) (hr: (m.result hc) = en.encode ret): AsymptoticWitness m n c₀ p ret c
| apply {α: Type _} {β: Type _} {γ: Type _} [en: Encoding α m.Data] (p: m.Program) (f: α → β) (fc: α → γ)
  (harg: (a: α) → AsymptoticWitness m n c₀ (m.apply p (en.encode a)) (f a) (fc a)): AsymptoticWitness m n c₀ p f fc

def Asymptotically {α: Type _} {β: Type _} (m: Complexity.Model) (f: α) (cost: β): Prop :=
  ∃ n c p, AsymptoticWitness m n c p f cost

end Complexity
