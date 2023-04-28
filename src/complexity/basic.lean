import tactic

namespace complexity

structure model :=
  (Program: Type)
  (Data: Type)
  (Result: Type)
  (Cost: Type)
  (data_equiv: setoid Data)
  (result_equiv: setoid Result)
  (cost_lt: preorder Cost)
  (cost_add: has_add Cost)
  (apply: Program → Data → Program)
  (has_cost: Program → Cost → Prop)
  (result: Π {p c}, (has_cost p c) → Result)
  (cost_pos: ∀ (c₀ c₁: Cost), c₀ ≤ c₀ + c₁)
  (has_cost_mono: ∀ p c₀ c₁, has_cost p c₀ → c₀ ≤ c₁ → has_cost p c₁)

instance (m: model): setoid m.Data := m.data_equiv
instance (m: model): setoid m.Result := m.result_equiv
instance (m: model): preorder m.Cost := m.cost_lt
instance (m: model): has_add m.Cost := m.cost_add

class has_encoding (α: Type*) (Data: Type*) [setoid Data] :=
  (encode: α → Data)
  (inj: ∀ {a b}, ⟦encode a⟧ = ⟦encode b⟧ → a = b)

def encode {α: Type*} {Data: Type*} [setoid Data] [has_encoding α Data]: α → Data := has_encoding.encode

theorem encode_inj {α: Type*} {Data: Type*} [setoid Data] [has_encoding α Data]
  {a b: α}: ⟦(encode a:Data)⟧ = ⟦encode b⟧ → a = b := has_encoding.inj

theorem encode_inj_iff {α: Type*} {Data: Type*} [setoid Data] [has_encoding α Data]
  {a b: α}: ⟦(encode a:Data)⟧ = ⟦encode b⟧ ↔ a = b := ⟨ encode_inj, λ h, h ▸ rfl ⟩

inductive witness
  (m: complexity.model): Π {α: Type*} {β: Type*}, m.Program → α → β → Prop
| result {α: Type*} [complexity.has_encoding α m.Result] (p: m.Program) (c: m.Cost) (ret: α)
  (hc: m.has_cost p c) (hr: (m.result hc) = complexity.encode ret): witness p ret c
| apply {α: Type*} {β: Type*} {γ: Type*} [complexity.has_encoding α m.Data] (p: m.Program) (f: α → β) (fc: α → γ)
  (harg: Π (a: α), witness (m.apply p (complexity.encode a)) (f a) (fc a)): witness p f fc

end complexity

def complexity {α: Type*} {β: Type*} (m: complexity.model) (f: α) (cost: β): Prop :=
  ∃ (program: m.Program), complexity.witness m program f cost