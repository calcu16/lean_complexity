import hmem.stack
import complexity.basic
import hmem.trace

universe u
variables {μ: Type} [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]

namespace hmem
namespace encoding

instance: has_equiv (memory μ) := ⟨ eq ⟩

def push_arg (lhs rhs: memory μ): memory μ :=
  (((memory.null μ).setv 1).setm 0 lhs).setm 1 rhs

def build_arg: list (memory μ) → memory μ
| [] := memory.null _
| [m] := m
| (x::xs) := push_arg (build_arg xs) x

def runtime_model (μ: Type) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]: complexity.model :=
⟨ (program μ × list (memory μ)),
  memory μ,
  memory μ,
  ℕ,
  ⟨ (=), eq.refl, @eq.symm _, @eq.trans _ ⟩,
  ⟨ (=), eq.refl, @eq.symm _, @eq.trans _ ⟩,
  infer_instance,
  infer_instance,
  λ p_a a, (p_a.fst, a::p_a.snd),
  λ p_a, (prod.fst p_a).has_time_cost (build_arg p_a.snd),
  λ p_a _ h, program.result p_a.fst (build_arg p_a.snd) ⟨_, h⟩,
  λ _ _, le_self_add,
  λ _ _ _ hrc₀ hc, program.time_cost_mono hrc₀ hc ⟩

theorem runtime_model_apply (p: program μ) (ms: list (memory μ)) (m: memory μ):
  (runtime_model μ).apply (p, ms) m = (p, m::ms) := rfl
  
theorem runtime_model_has_cost (p: program μ) (ms: list (memory μ)) (n: ℕ):
  (runtime_model μ).has_cost (p, ms) n ↔ p.has_time_cost (build_arg ms) n := ⟨ id, id ⟩

theorem memory_equiv_eq_iff (μ: Type*) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)] (m m': (runtime_model μ).Data):
  ⟦m⟧ = ⟦m'⟧ ↔ m = m' := ⟨quotient.exact, λ h, h ▸ rfl⟩

@[reducible]
def encode {α: Type*} [complexity.has_encoding α (runtime_model μ).Data]: α → memory μ := @complexity.encode _ _ (runtime_model μ).data_equiv _

@[reducible]
def has_encoding (α: Type*) (μ: Type*) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)] := complexity.has_encoding α (runtime_model μ).Data

instance (α: Type*) [en: has_encoding α μ]: complexity.has_encoding α (runtime_model μ).Result := en

theorem encode_inj {α: Type*} [has_encoding α μ] {a b: α}: (encode a:memory μ) = encode b → a = b :=
begin
  rw [← memory_equiv_eq_iff],
  exact complexity.encode_inj,
end

theorem encode_inj' {α: Type*} (μ: Type*) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]  [has_encoding α μ] {a b: α}: (encode a:memory μ) = encode b → a = b :=
begin
  rw [← memory_equiv_eq_iff],
  exact complexity.encode_inj,
end

instance prod_encoding (α β: Type*) [α_en: has_encoding α μ] [β_en: has_encoding β μ]:
  has_encoding (α × β) μ :=
begin
  fconstructor,
  exact λ ab, push_arg (encode ab.fst) (encode ab.snd),
  intros x y,
  cases x,
  cases y,
  rw [memory_equiv_eq_iff, prod.eq_iff_fst_eq_snd_eq],
  unfold push_arg,
  intro h;
  split,
  { apply encode_inj' μ,
    apply memory.getm_congr 0 h;
    rw [memory.getm_setm_nz, memory.getm_setm] },
  { apply encode_inj' μ,
    apply memory.getm_congr 1 h;
    rw [memory.getm_setm] }
end

theorem encode_pair  {α β: Type*}  [α_en: has_encoding α μ] [β_en: has_encoding β μ] (a: α) (b: β):
  encode (a, b) = (((memory.null μ).setv 1).setm 0 (encode a)).setm 1 (encode b) := rfl

instance decidable_encoding (p: Prop):
  has_encoding (decidable p) μ :=
begin
  fconstructor,
  exact λ d,  (memory.null _).setv (d.cases_on (λ _, 0) (λ _, 1)),
  intros x y,
  cases x;
  cases y;
  simp [memory_equiv_eq_iff, memory.setv_inj_iff],
end

theorem encode_is_false {p: Prop} {hp: ¬ p} (d: decidable p):
  (encode (is_false hp)) = memory.null μ := memory.null_setv_zero

theorem encode_is_true {p: Prop} {hp: p} (d: decidable p):
  (encode (is_true hp)) = (memory.null μ).setv 1 := rfl

instance bool_encoding: has_encoding bool μ :=
begin
  fconstructor,
  exact λ b,  (memory.null _).setv (ite b 1 0),
  intros x y,
  cases x;
  cases y;
  simp [memory_equiv_eq_iff, memory.setv_inj_iff],
end

-- structure encodable_function (μ: Type*) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)] :=
--   {α: Type} (α_en: complexity.encoding (runtime_model μ) α)
--   {β: Type} (β_en: complexity.encoding (runtime_model μ) β)
--   (f: α → β)

-- structure encodable_application (μ: Type*) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)] :=
--   {α: Type} (α_en: complexity.encoding (runtime_model μ) α)
--   {β: Type} (β_en: complexity.encoding (runtime_model μ) β)
--   (f: α → β)
--   (a: α)

-- structure encoded_function (μ: Type*) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)] :=
--   {α: Type} (α_en: complexity.encoding (runtime_model μ) α)
--   {β: Type} (β_en: complexity.encoding (runtime_model μ) β)
--   (f: α → β)
--   (p: program μ)
--   (pf: ∀ a : α, p.has_result (α_en.encode a) (β_en.encode (f a)))

-- def program.call_structure_helper: program μ → ℕ → tree ℕ
-- | [] n := tree.node n tree.nil tree.nil 
-- | (@instruction.ite _ _ _ _ _ is'::is) n := tree.node n (program.call_structure_helper is 0) (program.call_structure_helper is' 0)
-- | (instruction.call _ _ _::is) n := program.call_structure_helper is (n+1)
-- | (i::is) n := program.call_structure_helper is n

-- def program.call_structure: program μ → tree ℕ := flip program.call_structure_helper 0

-- def tree.all₂ {α β: Type*} (f: α → β → Prop): tree α → tree β → Prop
-- | tree.nil tree.nil := true
-- | (tree.node a la ra) (tree.node b lb rb) := f a b ∧ tree.all₂ la lb ∧ tree.all₂ ra rb
-- | _ _ := false

-- instance {α β: Type*} (f: α → β → Prop) [fd: Π {a b}, decidable (f a b)] (as: tree α) (bs: tree β):
--   decidable (tree.all₂ f as bs) :=
-- begin
--   induction as with _ _ _ lhs_ih rhs_ih generalizing bs,
--   { cases bs,
--     exact decidable.is_true trivial,
--     exact decidable.is_false not_false },
--   { cases bs,
--     exact decidable.is_false not_false,
--     cases fd,
--     exact decidable.is_false (not_and_of_not_left _ h),
--     cases lhs_ih _,
--     exact decidable.is_false (not_and_of_not_right _ (not_and_of_not_left _ h_1)),
--     cases rhs_ih _,
--     exact decidable.is_false (not_and_of_not_right _ (not_and_of_not_right _ h_2)),
--     exact decidable.is_true ⟨h, h_1, h_2⟩}
-- end

-- def tree.path {α: Type*}: tree α → list bool → list α
-- | (tree.nil) _ := []
-- | (tree.node a lhs rhs) [] := [a]
-- | (tree.node a lhs rhs) (ff::p) := a :: tree.path lhs p
-- | (tree.node a lhs rhs) (tt::p) := a :: tree.path rhs p

-- def makes_calls (μ: Type*) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]
--   {α: Type} [complexity.has_encoding (runtime_model μ) α]
--   {β: Type} [complexity.has_encoding (runtime_model μ) β]
--   (f: α → β)
--   (i: ℕ) (c: α → list (encodable_application μ)) 
--   (r: α → list α) :=
--   ∃ (p: program μ) (t: tree (list (encodable_function μ))),
--     tree.all₂ (λ l n, list.length l = n) t (program.call_structure p) ∧
--     ∀ (a : α), ∃ (tr: trace μ), 
--       p.has_trace (encode a) tr ∧
--       list.forall₂
--         (λ (ef: encoded_function μ) (pm: program μ × memory μ),
--           ∃ 
--       (list.join (t.path tr.branch)) 




end encoding
end hmem