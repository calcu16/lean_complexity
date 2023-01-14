import tactic.basic

lemma ftype {α α': Type} {β β': Type}: α = α' → β = β' → (α → β) = (α' → β') :=
by { intros p q, rw [p, q] }

lemma ftype_right (α: Type) {β β': Type}: β = β' → (α → β) = (α → β') :=
by { intro p, rw [p] }

lemma fcast: ∀ {α β γ: Type} (f: α → β) (a: α) (h: (β = γ)), (cast h (f a)) = (cast (ftype_right α h) f) a :=
 by { intros α β γ f a h, finish }

 lemma fcast': ∀ {α β γ: Type} (f: α → β) (a: α) (h: (β = γ)) (h': ((α → β) = (α → γ))), (cast h (f a)) = (cast h' f) a :=
 by { intros α β γ f a h, finish }

namespace complexity

-- a model is a relation between a program type and a datatype
structure model (α β γ: Type) [has_equiv β]  [preorder γ]  [has_add γ] :=
mk ::
  (accepts_with_cost : α → β → γ → Prop)
  (application : α → β → α)
  (cost_mono : ∀ {a : α} {b : β} {c₀ c₁ : γ}, c₀ ≤ c₁ → accepts_with_cost a b c₀ → accepts_with_cost a b c₁)

variables {α β γ: Type} [has_equiv β] [preorder γ] [has_add γ]

namespace model
@[simp] def program_type: model α β γ → Type := λ _, α
@[simp] def data_type: model α β γ → Type := λ _, β
@[simp] def cost_type: model α β γ → Type := λ _, γ
end model

structure encoding (m: model α β γ) (δ: Type) :=
mk ::
  (encode: δ → β)
  (encode_inj: ∀ x y: δ, encode x ≈ encode y ↔ x = y)

variables {m: model α β γ}

namespace encoding
variables {δ: Type}

@[simp] def model : encoding m δ → model α β γ := λ _,  m
@[simp] def type : encoding m δ → Type := λ _, δ

@[simp] def application (en: encoding m δ) (prog: α) (arg: δ): α :=
  en.model.application prog (en.encode arg)

@[simp] theorem inj_iff (en: encoding m δ) (a b: δ):
  en.encode a ≈ en.encode b ↔ a = b := en.encode_inj _ _
end encoding

class has_encoding (m: model α β γ) (δ: Type):= (value: encoding m δ)

def encode (m: model α β γ) {δ: Type} [f: has_encoding m δ] := f.value.encode

inductive encodable_function (m: model α β γ): Type 1
| result: Π {δ: Type}, encoding m δ → encodable_function
| application: Π {δ: Type}, encoding m δ → encodable_function → encodable_function

namespace encodable_function
@[simp] def model : encodable_function m → model α β γ := λ _, m

@[simp] def unwrap: encodable_function m → Type
| (result en) := en.type
| (application en b) := en.type → b.unwrap
end encodable_function
variables {enf: encodable_function m}

structure is_encoded_function (m: model α β γ) (δ: Type):=
mk ::
  (value: encodable_function m)
  (sound: value.unwrap = δ)

class has_encodable_function (m: model α β γ) (δ: Type) := (value: is_encoded_function m δ)

variables {δ: Type} [has_encodable_function m δ]

@[simp] theorem unwrap_has_encodable (a: has_encodable_function m δ): a.value.value.unwrap = δ := a.value.sound
theorem unwrap_has_encodable' (a: has_encodable_function m δ): δ = a.value.value.unwrap := a.value.sound.symm

@[simp] theorem unwrap_is_encoded_function (a: is_encoded_function m δ): a.value.unwrap = δ := a.sound

def cast_unwrap [a: has_encodable_function m δ] (f: δ): a.value.value.unwrap :=
  cast (unwrap_has_encodable' a) f

instance encodable_result (δ: Type) [f: has_encoding m δ]:
    has_encodable_function m δ :=
  ⟨ ⟨ encodable_function.result f.value, rfl ⟩ ⟩

instance encodable_application (δ: Type) [f: has_encoding m δ] (ε: Type) [g: has_encodable_function m ε]:
    has_encodable_function m (δ → ε) :=
  ⟨ ⟨ encodable_function.application f.value g.value.value, ftype rfl g.value.sound ⟩ ⟩

def cost_function: encodable_function m → Type
| (encodable_function.result _) := γ
| (encodable_function.application en c) := en.type → cost_function c

@[simp] def cost_function' (m: model α β γ) (δ : Type) [f: has_encodable_function m δ] := cost_function f.value.value

namespace cost_function
variables {cf₀ cf₁ : cost_function enf}

def less_than_or_equal: Π {enf: encodable_function m}, cost_function enf → cost_function enf → Prop
| (encodable_function.result _) := λ n m: γ, n ≤ m
| (encodable_function.application _ _) := λ f g, ∀ a, less_than_or_equal (f a) (g a)

instance: preorder (cost_function enf) := begin
  fconstructor,
  exact cost_function.less_than_or_equal,
  induction enf,
  { intro cf, refl },
  { intros cf x, exact enf_ih _ },
  induction enf,
  { intros a b c,
    apply preorder.le_trans},
  { intros a b c hab hac x,
    exact enf_ih _ _ _ (hab x) (hac x) },
end

def add: Π {enf: encodable_function m}, cost_function enf → cost_function enf → cost_function enf
| (encodable_function.result _) := λ n m: γ, (n + m: γ)
| (encodable_function.application _ _) := λ f g a, add (f a) (g a)

instance: has_add (cost_function enf) := ⟨ add ⟩

def lift: Π (enf: encodable_function m), γ → cost_function enf
| (encodable_function.result _) := λ c, c
| (encodable_function.application _ enf) := λ c _, lift enf c

instance: has_lift γ (cost_function enf) := ⟨ lift enf ⟩

end cost_function

def witness: Π (a : encodable_function m), α → a.unwrap → (cost_function a) → Prop
| (encodable_function.result en) := λ prog data, en.model.1 prog (en.encode data)
| (encodable_function.application en b) := λ prog f cost, ∀ arg : en.type,
  witness b (encoding.application en prog arg) (f arg) (cost arg)

def complexity_le [enf: has_encodable_function m δ] (f: δ) (cf: cost_function enf.value.value) :=
  ∃ prog: α, witness enf.value.value prog (cast_unwrap f) cf

structure is_complexity (m: model α β γ) {δ: Type} [has_encodable_function m δ] (f: δ) :=
mk ::
  (cost : cost_function' m δ)
  (proof : complexity_le f cost)

class has_complexity (m: model α β γ) {δ: Type} [has_encodable_function m δ] (f: δ) :=
  (value: is_complexity m f)

theorem omega_equiv  {m: model α β γ} {δ: Type} [enf: has_encodable_function m δ] {f: δ} {cf: cost_function enf.value.value}:
  complexity_le f cf → ∀ g, f = g → complexity_le g cf :=
begin
  intros hf g hfg,
  rw [← hfg],
  exact hf,
end

end complexity

def complexity {α β γ: Type} [has_equiv β] [preorder γ] [has_add γ]
  (m: complexity.model α β γ) {δ: Type} [complexity.has_encodable_function m δ]
  (f: δ) [c: complexity.has_complexity m f]:
  complexity.cost_function' m δ := c.value.cost

instance {α β γ: Type} [has_equiv β] [preorder γ] [has_add γ] (m: complexity.model α β γ)
  (δ: Type) [complexity.has_encodable_function m δ]:
  has_le (complexity.cost_function' m δ) :=
  ⟨ complexity.cost_function.less_than_or_equal ⟩