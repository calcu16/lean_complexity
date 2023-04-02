import hmem.stack
import complexity.basic

variables {μ: Type*} [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]

namespace hmem
namespace encoding

instance: has_equiv (memory μ) := ⟨ eq ⟩

def push_arg (lhs rhs: memory μ): memory μ :=
  (((memory.null μ).setv 1).setm 0 lhs).setm 1 rhs

def build_arg: list (memory μ) → memory μ
| [] := memory.null _
| [m] := m
| (x::xs) := push_arg (build_arg xs) x

def runtime_model (μ: Type*) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]: complexity.model (program μ × list (memory μ)) (memory μ) ℕ :=
 ⟨  λ p_a r c, p_a.fst.has_result (build_arg p_a.snd) r ∧ p_a.fst.has_time_cost (build_arg p_a.snd) c,
    λ p_a a', (p_a.fst, a'::p_a.snd),
    λ _ _ _ _ _ hrc₁ hrc₂, program.unique_result hrc₁.left hrc₂.left,
    λ _ _ _ _ hc hrc₀, ⟨hrc₀.left, program.time_cost_mono hrc₀.right hc⟩ ⟩

def encode {δ: Type} [complexity.has_encoding (runtime_model μ) δ]: δ → memory μ := complexity.encode (runtime_model μ)

instance (α β: Type*)  [α_en: complexity.has_encoding (runtime_model μ) α] [β_en: complexity.has_encoding (runtime_model μ) β]:
  complexity.has_encoding (runtime_model μ) (α × β) :=
begin
  fconstructor,
  fconstructor,
  exact λ ab, push_arg (encode ab.fst) (encode ab.snd),
  intros x y,
  cases x,
  cases y,
  simp [push_arg, has_equiv.equiv, encode],
  split,
  { intro h,
    split,
    { rw ← complexity.encoding.encode_inj α_en.value,
      apply memory.getm_congr 0 h,
      { rw [memory.getm_setm_ne _ _ _ _ zero_ne_one, memory.getm_setm],
        refl,
        apply_instance},
      { rw [memory.getm_setm_ne _ _ _ _ zero_ne_one, memory.getm_setm],
        refl,
        apply_instance} },
    { rw ← complexity.encoding.encode_inj β_en.value,
      apply memory.getm_congr 1 h,
      { rw [memory.getm_setm],
        refl },
      { rw [memory.getm_setm],
        refl } } },
  { intro h,
    rw [h.left, h.right] }
end

theorem encode_pair  {α β: Type*}  [α_en: complexity.has_encoding (runtime_model μ) α] [β_en: complexity.has_encoding (runtime_model μ) β] (a: α) (b: β):
  encode (a, b) = (((memory.null μ).setv 1).setm 0 (encode a)).setm 1 (encode b) := rfl

instance (p: Prop):
  complexity.has_encoding (runtime_model μ) (decidable p) :=
begin
  fconstructor,
  fconstructor,
  exact λ d,  (memory.null _).setv (d.cases_on (λ _, 0) (λ _, 1)),
  intros x y,
  cases x;
  cases y;
  simp [has_equiv.equiv, memory.setv_inj_iff],
end

theorem encode_is_false {p: Prop} {hp: ¬ p} (d: decidable p):
  (encode (is_false hp)) = memory.null μ := memory.null_setv_zero

theorem encode_is_true {p: Prop} {hp: p} (d: decidable p):
  (encode (is_true hp)) = (memory.null μ).setv 1 := rfl

end encoding
end hmem