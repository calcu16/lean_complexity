import lambda_calculus.utlc.beta.distance
import lambda_calculus.utlc.beta.encoding.basic
import lambda_calculus.utlc.beta.encoding.core
import lambda_calculus.utlc.beta.encoding.nat
import lambda_calculus.utlc.beta.encoding.utlc
import lambda_calculus.utlc.beta.complexity.core
import lambda_calculus.utlc.beta.complexity.nat
import complexity.basic
import complexity.nat

open complexity
open lambda_calculus.utlc.β.encoding

namespace lambda_calculus
namespace utlc
namespace β
namespace complexity
namespace utlc

namespace rec_complexity

def cost {α: Type}
  (rf: Π (f: utlc), (λ _: utlc, α) f)
  (c_down: ℕ → ℕ) (c_lambda: utlc → α → ℕ)
  (c_dot: utlc → utlc → α → α → ℕ): utlc → ℕ
| (↓n) := c_down n + 8
| (Λ f) := c_lambda f (rf f) + cost f + 9
| (f·g) := c_dot f g (rf f) (rf g) + cost f + cost g + 10

end rec_complexity

local attribute [simp] closed closed_below
local attribute [simp] β.normal_iteration β.strategic_reduction_step
local attribute [simp] substitution down_shift head_reduced
local attribute [simp] complexity.cast_unwrap distance_model
local attribute [simp] encoding.utlc.encode_utlc

def handle_down (f y: utlc): utlc := f
def handle_lambda (f y: utlc): utlc := Λ (f ↑¹ 0)·↓0·((y ↑¹ 0)·↓0)
def handle_dot (f y: utlc): utlc := Λ Λ (f ↑¹ 0 ↑¹ 1)·↓1·↓0·((y ↑¹ 0 ↑¹ 1)·↓1)·((y ↑¹ 0 ↑¹ 1)·↓0)
def rec_utlc (y g f₀ f₁ f₂: utlc): utlc := g·handle_down f₀ y·handle_lambda f₁ y·handle_dot f₂ y

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

theorem rec_utlc_sub {y g f₀ f₁ f₂: utlc} (n: ℕ) (x: utlc):
  (rec_utlc y g f₀ f₁ f₂)[n:=x] = (rec_utlc (y[n:=x]) (g[n:=x]) (f₀[n:=x]) (f₁[n:=x]) (f₂[n:=x])) :=
begin
  simp [rec_utlc, handle_down, handle_lambda, handle_dot, substitution_shift_ge],
  repeat { rw [substitution_shift_ge] },
  all_goals { linarith },
end

theorem rec_utlc_down (et: encoding_type) [ℕ_en: has_encoding (distance_model et) ℕ] (y: utlc) (n: ℕ) (f₀ f₁ f₂: utlc):
  distance_le 3
    (rec_utlc y (encoding.utlc.encode_utlc et (↓n)).value f₀ f₁ f₂)
    (f₀·(complexity.encode (distance_model et) n).value) :=
begin
  rw [rec_utlc, utlc.encode_utlc, β.encoding.alternative],
  simp,
  apply distance_le_of_normal_iteration,
  simp [handle_down],
end

theorem rec_utlc_lambda (et: encoding_type) [ℕ_en: has_encoding (distance_model et) ℕ] (y g f₀ f₁ f₂: utlc):
  distance_le 4
    (rec_utlc y (encoding.utlc.encode_utlc et (Λ g)).value f₀ f₁ f₂)
    (f₁·(complexity.encode (distance_model et) g).value·(y·(complexity.encode (distance_model et) g).value)) :=
begin
  rw [rec_utlc, utlc.encode_utlc, β.encoding.alternative],
  simp,
  apply distance_le_of_normal_iteration 4,
  simp [handle_lambda, utlc.encode_utlc, encode],
  refl,
end

theorem rec_utlc_dot (et: encoding_type) [ℕ_en: has_encoding (distance_model et) ℕ] (y g₀ g₁ f₀ f₁ f₂: utlc):
  distance_le 5
    (rec_utlc y (encoding.utlc.encode_utlc et (g₀·g₁)).value f₀ f₁ f₂)
    (f₂·(complexity.encode (distance_model et) g₀).value·(complexity.encode (distance_model et) g₁).value·(y·(complexity.encode (distance_model et) g₀).value)·(y·(complexity.encode (distance_model et) g₁).value)) :=
begin
  rw [rec_utlc, utlc.encode_utlc, β.encoding.alternative],
  simp,
  apply distance_le_of_normal_iteration 5,
  simp [handle_dot, and_assoc],
  refine ⟨ rfl, rfl, rfl, rfl ⟩,
end

instance rec_complexity
  (α: Type) (et: encoding_type) [α_en: has_encoding (distance_model et) α]
  [ℕ_en: has_encoding (distance_model et) ℕ]
  (f₀: ℕ → α) [cf₀: has_complexity (distance_model et) f₀]
  (f₁: utlc → α → α) [cf₁: has_complexity (distance_model et) f₁]
  (f₂: utlc → utlc → α → α → α) [cf₂: has_complexity (distance_model et) f₂]:
  has_complexity (distance_model et) (simp_rec f₀ f₁ f₂) :=
begin
  fconstructor,
  fconstructor,
  exact rec_complexity.cost (simp_rec f₀ f₁ f₂) cf₀.value.cost cf₁.value.cost cf₂.value.cost,
  rcases cf₀.value with ⟨ cfc₀, fp₀, cfp₀ ⟩,
  rcases cf₁.value with ⟨ cfc₁, fp₁, cfp₁ ⟩,
  rcases cf₂.value with ⟨ cfc₂, fp₂, cfp₂ ⟩,
  fconstructor,
  fconstructor,
  exact yrec (Λ Λ rec_utlc (↓1:utlc) (↓0:utlc) fp₀.value fp₁.value fp₂.value),
  simp [ycomb, yrec, rec_utlc, handle_down, handle_lambda, handle_dot],
  simp [cast_unwrap],
  intro a,
  simp [has_encoding.value, distance_model, complexity.encode],
  induction a,
  all_goals { apply distance_le_trans',
    apply dot_distance_le_dot_left,
    apply yrec_apply,
    apply distance_le_trans',
    apply distance_le_of_normal_iteration 2,
    simp [rec_utlc_sub] },
  { apply distance_le_trans',
    apply rec_utlc_down,
    simp,
    apply cfp₀,
    refl },
  refl,
  simp [rec_complexity.cost],
  ring,
  { apply distance_le_trans',
    apply rec_utlc_lambda,
    apply distance_le_trans',
    apply dot_distance_le_dot_right,
    apply a_ih,
    simp,
    apply cfp₁,
    refl,
    refl },
  refl,
  simp [rec_complexity.cost],
  ring,
  { apply distance_le_trans',
    apply rec_utlc_dot,
    apply distance_le_trans',
    apply dot_distance_le_dot_right,
    apply a_ih_g,
    apply distance_le_trans',
    apply dot_distance_le_dot_left,
    apply dot_distance_le_dot_right,
    apply a_ih_f,
    apply cfp₂,
    refl,
    refl,
    refl },
  refl,
  simp [rec_complexity.cost],
  ring_nf,
end

instance size_complexity:
  has_complexity church_model utlc.size :=
begin
  fconstructor,
  fconstructor,
  exact (λ f, 67 * f.size: utlc → ℕ),
  apply omega_equiv,
  rotate 2,
  exact (simp_rec
    (@const ℕ ℕ 1)
    (curry (compose (nat.add (1:ℕ)) prod.snd))
    (curry (curry (curry (compose (uncurry nat.add) (fork (compose prod.snd prod.fst) (compose (nat.add 1) prod.snd))))))),
  apply complexity_of_instance,
  intro f,
  simp [complexity, has_complexity.value],
  norm_num,
  unfold_coes,
  unfold has_add.add,
  unfold cost_function.add,
  unfold cost_function.less_than_or_equal,
  conv {
    to_lhs,
    congr,
    skip,
    skip,
    skip,
    funext,
    whnf,
    simp [nat.succ_eq_add_one],
    ring_nf,
    rw [nat.add_comm],
    whnf,
    simp [nat.succ_eq_add_one],
    norm_num },
  induction f,
  { simp [rec_complexity.cost],
    linarith },
  { simp [rec_complexity.cost, add_mul],
    ring_nf,
    apply add_le_add,
    apply f_ih,
    linarith },
  { simp [rec_complexity.cost, add_mul],
    ring_nf,
    apply add_le_add,
    apply f_ih_f,
    apply add_le_add,
    apply f_ih_g,
    refl },
  ext1,
  simp [const, curry, compose, uncurry, fork],
  induction x,
  { simp },
  { simp [x_ih, nat.add_comm _ 1] },
  { simp [x_ih_f, x_ih_g, add_comm 1 x_g.size, add_assoc x_f.size] }
end

end utlc
end complexity
end β
end utlc
end lambda_calculus
