import lambda_calculus.utlc.beta.distance
import lambda_calculus.utlc.beta.encoding.basic
import complexity.basic
import complexity.core

namespace lambda_calculus
namespace utlc
namespace β
namespace complexity

open lambda_calculus.utlc.β.encoding

local attribute [simp] β.normal_iteration β.strategic_reduction_step head_reduced

variables {et: encoding_type}

theorem of_distance_le
  {a: complexity.encodable_function (distance_model et)} {f f': a.unwrap} (g : encoded_program) {g': encoded_program} (fc fc': complexity.cost_function a) (n: ℕ):
  distance_le n g'.value g.value → complexity.witness a g f fc → f = f' → (fc + ↑n) ≤ fc' →
  complexity.witness a g' f' fc' :=
begin
  induction a with _ _ _ en _ generalizing f f' g g' fc fc',
  { intros hg hw hf hfc,
    rw [← hf],
    apply distance_le_mono,
    apply distance_le_trans',
    apply hg,
    apply hw,
    refl,
    rw  [nat.cast_id, nat.add_comm] at hfc,
    assumption },
  { intros hg hw hf hfc a,
    apply a_ih (en.application g a),
    simp [distance_model],
    apply utlc.β.dot_distance_le_dot_left,
    apply hg,
    apply hw,
    rw [hf],
    apply hfc,
  }
end

instance value_complexity (α: Type) (et: encoding_type) [en: complexity.has_encoding (distance_model et) α] (a: α):
  complexity.has_complexity (distance_model et) a :=
  ⟨ ⟨ (0:ℕ),
    ⟨ ⟨ (en.value.encode a).value, (en.value.encode a).proof.left ⟩,
      @distance_le_refl _ has_β_reduction.step _ ⟩ ⟩ ⟩

def id_prog: encoded_program := ⟨ Λ ↓0, by simp ⟩

instance id_complexity (α: Type) (et: encoding_type) [en: complexity.has_encoding (distance_model et) α] (a: α):
  complexity.has_complexity (distance_model et) (@id α) :=
  ⟨ ⟨ λ _, (1:ℕ), ⟨ id_prog,
begin
  intro a,
  apply distance_le_of_normal_iteration,
  simp [id_prog, complexity.cast_unwrap, distance_model],
end ⟩ ⟩ ⟩

def const_prog: encoded_program := ⟨ Λ Λ ↓1, by simp ⟩

instance const_complexity (α β: Type) (et: encoding_type)
  [en: complexity.has_encoding (distance_model et) α] [en: complexity.has_encoding (distance_model et) β]:
  complexity.has_complexity (distance_model et) (@const α β) :=
  ⟨ ⟨ λ _ _, (2:ℕ), ⟨ const_prog,
begin
  intros a b,
  apply distance_le_of_normal_iteration,
  simp [const_prog, const, complexity.cast_unwrap, distance_model],
end ⟩ ⟩ ⟩

instance partial_complexity
  (α β: Type) (et: encoding_type)
  [en: complexity.has_encoding (distance_model et) α]
  [complexity.has_encodable_function (distance_model et) β]
  (a: α) {f: α → β} [h: complexity.has_complexity (distance_model et) f] :
  complexity.has_complexity (distance_model et) (f a) :=
  ⟨ ⟨ (complexity (distance_model et) f) a,
  by {
  cases h.value.proof with prog h,
  exact ⟨ ⟨ prog.value·(en.value.encode a).value, by {
    simp only [ bool.to_bool_coe, and_true,
      data_is_closed_below', closed_below, closed], apply prog.proof } ⟩,
  by { rw [complexity.cast_unwrap, fcast], exact h a } ⟩ } ⟩ ⟩

def compose_prog: encoded_program := ⟨ Λ Λ Λ ↓2·(↓1·↓0), by simp ⟩

instance compose_complexity
  (α β γ: Type) (et: encoding_type)
  [α_en: complexity.has_encoding (distance_model et) α] [β_en: complexity.has_encoding (distance_model et) β] [γ_en: complexity.has_encodable_function (distance_model et) γ]
  (f: α → β) (g: β → γ) [cf: complexity.has_complexity (distance_model et) f] [cg: complexity.has_complexity (distance_model et) g]:
  complexity.has_complexity (distance_model et) (compose g f) :=
⟨ ⟨ λ a, cg.value.cost (f a) + ↑(3 + (cf.value.cost a):ℕ),
begin
  rcases cf.value with ⟨cfc, fp, cfp⟩,
  rcases cg.value with ⟨cgc, gp, cgp⟩,
  fconstructor,
  { exact ⟨ compose_prog.value·gp.value·fp.value,
    by simp; exact ⟨compose_prog.proof, gp.proof, fp.proof⟩ ⟩ },
  intro a,
  apply of_distance_le begin
    fconstructor,
    { exact gp.value·((β_en.value.encode (f a)).value) },
    simp,
  end,
  { simp [distance_model, compose_prog],
    apply distance_le_trans,
    { apply distance_le_of_normal_iteration 3,
      simp [normal_iteration, distance_model, compose_prog] },
    apply utlc.β.dot_distance_le_dot_right,
    apply cfp a },
  apply cgp (f a),
  unfold complexity.cast_unwrap,
  rw [← fcast', ← fcast'],
  all_goals { simp [compose] },
end ⟩ ⟩

def flip_prog: encoded_program := ⟨ Λ Λ Λ ↓2·↓0·↓1, by simp ⟩

instance flip_complexity
  (α β γ: Type) (et: encoding_type)
  [α_en: complexity.has_encoding (distance_model et) α] [β_en: complexity.has_encoding (distance_model et) β] [γ_en: complexity.has_encoding (distance_model et) γ]
  (f: α → β → γ) [cf: complexity.has_complexity (distance_model et) f]:
  complexity.has_complexity (distance_model et) (flip f) :=
⟨ ⟨ λ b a, (cf.value.cost a b) + ↑3,
begin
  rcases cf.value with ⟨cfc, fp, cfp⟩,
  fconstructor,
  { exact ⟨ flip_prog.value·fp.value,
    by simp; exact ⟨ flip_prog.proof, fp.proof ⟩ ⟩ },
  intros a b,
  apply distance_le_trans',
  { apply distance_le_of_normal_iteration 3,
    refl },
  simp [distance_model, flip_prog],
  apply cfp,
  simp [add_comm 3],
end ⟩ ⟩

def ycomb: utlc := Λ (Λ ↓1·(↓0·↓0))·(Λ ↓1·(↓0·↓0))
def yrec (f: utlc): utlc := ycomb·f

theorem yrec_apply {f: utlc}: distance_le 3 (yrec f) (f·yrec f) :=
begin
  rw [yrec, ycomb],
  apply distance_le_trans',
  apply distance_le_of_normal_iteration 2,
  simp,
  apply dot_distance_le_dot_right,
  apply distance_le_symm,
  apply distance_le_of_normal_iteration 1,
  simp,
end

end complexity
end β
end utlc
end lambda_calculus