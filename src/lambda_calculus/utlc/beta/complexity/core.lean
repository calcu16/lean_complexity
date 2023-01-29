import lambda_calculus.utlc.beta.distance
import lambda_calculus.utlc.beta.encoding.basic
import lambda_calculus.utlc.beta.encoding.core
import lambda_calculus.utlc.beta.complexity.basic
import complexity.basic
import complexity.core

namespace lambda_calculus
namespace utlc
namespace β
namespace complexity

open complexity
open lambda_calculus.utlc.β.encoding

local attribute [simp] closed closed_below
local attribute [simp] β.normal_iteration β.strategic_reduction_step
local attribute [simp] substitution shift head_reduced

def fork_prog: encoded_program := ⟨ Λ Λ Λ Λ ↓0·(↓3·↓1)·(↓2·↓1), by simp [←one_add_one_eq_two] ⟩

instance fork_complexity_le {α β γ: Type} (et: encoding_type)
  [complexity.has_encoding (distance_model et) α] [complexity.has_encoding (distance_model et) β] [complexity.has_encoding (distance_model et) γ]
  {f: α → β} [cf: complexity.has_complexity (distance_model et) f]
  {g: α → γ} [cg: complexity.has_complexity (distance_model et) g]:
  complexity.has_complexity (distance_model et) (fork f g) :=
⟨ ⟨ (λ a, (3:ℕ) + (cf.value.cost a + cg.value.cost a)),
begin
  rcases cf.value with ⟨cfc, fp, cfp⟩,
  rcases cg.value with ⟨cgc, gp, cgp⟩,
  fconstructor,
  fconstructor,
  exact fork_prog.value·fp.value·gp.value,
  { simp },
  intro a,
  apply distance_le_trans',
  apply distance_le_of_normal_iteration 3,
  simp [fork_prog, complexity.cast_unwrap, distance_model,
    complexity.has_encoding.value],
  apply lambda_distance_le_lambda,
  apply distance_le_trans',
  apply dot_distance_le_dot_left,
  apply dot_distance_le_dot_right,
  apply cfp,
  apply dot_distance_le_dot_right,
  apply cgp,
  refl,
  simp,
end
⟩ ⟩

def curry_prog: encoded_program := ⟨ Λ Λ Λ ↓2·(Λ ↓0·↓2·↓1), by simp[← one_add_one_eq_two] ⟩

instance curry_complexity_le {α β γ: Type} (et: encoding_type)
  [α_en: complexity.has_encoding (distance_model et) α] [β_en: complexity.has_encoding (distance_model et) β] [complexity.has_encodable_function (distance_model et) γ]
  {f: (α × β) → γ} [cf: complexity.has_complexity (distance_model et) f]:
  complexity.has_complexity (distance_model et) (curry f) :=
⟨ ⟨ (λ a b, (cf.value.cost (a, b) + ↑(3:ℕ))),
begin
  rcases cf.value with ⟨cfc, fp, cfp⟩,
  fconstructor,
  fconstructor,
  exact curry_prog.value·fp.value,
  { simp },
  intros a b,
  apply of_distance_le begin
    fconstructor,
    refine fp.value·_,
    apply encoding.encoded_data.value,
    apply complexity.encode (distance_model et),
    apply (a, b),
    apply @encoding.prod_encoding α β et α_en β_en,
    simp,
  end,
  apply distance_le_of_normal_iteration 3,
  simp [curry_prog, complexity.cast_unwrap, distance_model, complexity.has_encoding.value],
  refl,
  apply cfp,
  simp [complexity.cast_unwrap, ← fcast', curry],
end
⟩ ⟩

def uncurry_prog: encoded_program := ⟨ Λ Λ ↓0·↓1, by simp ⟩

instance uncurry_complexity_le {α β γ: Type} (et: encoding_type)
  [α_en: complexity.has_encoding (distance_model et) α] [β_en: complexity.has_encoding (distance_model et) β] [complexity.has_encodable_function (distance_model et) γ]
  {f: α → β → γ} [cf: complexity.has_complexity (distance_model et) f]:
  complexity.has_complexity (distance_model et) (uncurry f) :=
⟨ ⟨ (λ ab, (cf.value.cost ab.fst ab.snd + ↑(3:ℕ))),
begin
  rcases cf.value with ⟨cfc, fp, cfp⟩,
  fconstructor,
  fconstructor,
  exact uncurry_prog.value·fp.value,
  { simp },
  intros ab,
  cases ab with a b,
  apply of_distance_le begin
    fconstructor,
    refine fp.value·_·_,
    apply encoding.encoded_data.value,
    apply complexity.encode (distance_model et),
    apply a,
    apply α_en,
    apply encoding.encoded_data.value,
    apply complexity.encode (distance_model et),
    apply b,
    apply β_en,
    simp,
  end,
  apply distance_le_of_normal_iteration 3,
  simp [uncurry_prog, pair, complexity.cast_unwrap, distance_model, complexity.has_encoding.value],
  simp [complexity.encode],
  apply cfp,
  simp [complexity.cast_unwrap, ← fcast', uncurry],
end ⟩ ⟩

end complexity
end β
end utlc
end lambda_calculus