import lambda_calculus.utlc.beta.distance
import lambda_calculus.utlc.beta.encoding.basic
import lambda_calculus.utlc.beta.encoding.core
import lambda_calculus.utlc.beta.encoding.nat
import lambda_calculus.utlc.beta.complexity.core
import complexity.basic
import complexity.nat

open complexity
open lambda_calculus.utlc.β.encoding

namespace lambda_calculus
namespace utlc
namespace β
namespace complexity
namespace nat


local attribute [simp] distance_model closed
local attribute [simp] β.normal_iteration β.strategic_reduction_step head_reduced substitution down_shift

def succ_prog: encoded_program := ⟨ Λ Λ Λ ↓1·(↓2·↓1·↓0), by simp ⟩

instance succ_complexity: has_complexity church_model nat.succ :=
  ⟨ ⟨ λ _, (3:ℕ), ⟨ succ_prog,
begin
  simp only [cast_unwrap, cast_eq],
  intros n,
  apply β.distance_le_of_normal_iteration 3,
  simp [succ_prog, has_encoding.value, encoding.nat.iterate, function.iterate_succ']
end ⟩ ⟩ ⟩

def add_prog: encoded_program := ⟨ Λ Λ Λ Λ ↓3·↓1·(↓2·↓1·↓0), by simp [← one_add_one_eq_two] ⟩

instance add_complexity: has_complexity church_model nat.add :=
  ⟨ ⟨ λ _ _, (6:ℕ), ⟨ add_prog,
begin
  simp only [cast_unwrap, cast_eq],
  intros n m,
  apply distance_le_trans' 4 2,
  apply β.distance_le_of_normal_iteration,
  simp [add_prog, has_encoding.value, function.iterate_succ'],
  apply β.lambda_distance_le_lambda,
  apply β.lambda_distance_le_lambda,
  induction n generalizing m,
  { cases m;
    apply β.distance_le_of_normal_iteration;
    simp [function.iterate_succ', function.iterate_zero, encoding.nat.iterate] },
  simp [function.iterate_succ', function.iterate_zero, encoding.nat.iterate, nat.succ_add],
  apply β.dot_distance_le_dot_right,
  apply n_ih,
  simp,
end ⟩ ⟩ ⟩  

def iterate_prog: encoded_program := ⟨ Λ Λ Λ ↓1·↓2·↓0, by simp ⟩

namespace iteration_complexity

lemma iterate_distance_le {n: ℕ} {f g: utlc}: distance_le n f g → ∀ (a: utlc) (m: ℕ), distance_le n ((has_dot.dot a)^[m] f) ((has_dot.dot a)^[m] g) :=
begin
  intros hfg a m,
  induction m generalizing f g,
  simp [hfg],
  simp,
  apply m_ih,
  apply dot_distance_le_dot_right hfg,
end

def cost {α: Type}
  (fi: α → α) (ni: α → ℕ): ℕ → α → ℕ
| 0 := λ fz, 5
| (n+1) := λ fz, (ni fz) + (cost n (fi fz)) + 10

theorem cost_zero {α: Type} (fi: α → α) (ni: α → ℕ) (a: α): cost fi ni 0 a = 5 := rfl

theorem cost_succ {α: Type} (fi: α → α) (ni: α → ℕ) (n: ℕ) (a: α): cost fi ni (n + 1) a = (ni a) + cost fi ni n (fi a) + 10 := rfl

theorem cost_succ' {α: Type} (fi: α → α) (ni: α → ℕ) (n: ℕ) (a: α): cost fi ni (n + 1) a = (ni (fi^[n] a)) + cost fi ni n a + 10 :=
begin
  rw [cost_succ],
  induction n generalizing a,
  simp [cost_zero],
  rw [cost_succ, n_ih, cost_succ, function.iterate_succ],
  simp [nat.add_assoc, nat.add_left_comm _ (ni a)],
end

@[simp] def cost' {α: Type} [α_en: has_encoding church_model α]
  (fi: α → α) (ni: complexity.cost_function' church_model (α → ℕ)): complexity.cost_function' church_model (ℕ → α → α) := cost fi ni
end iteration_complexity

instance iteration_complexity (α: Type) [α_en: has_encoding church_model α]
  (f: α → α) [cf: has_complexity church_model f]: has_complexity church_model (nat.iterate f) :=
⟨ ⟨ iteration_complexity.cost' f cf.value.cost,
begin
  rcases cf.value with ⟨cfc, fp, cfp⟩,
  fconstructor,
  use iterate_prog.value·fp.value,
  { simp },
  simp only [cast_unwrap, cast_eq, iterate_prog],
  intros n a,
  induction n generalizing a,
  { apply β.distance_le_of_normal_iteration,
    simp [has_encoding.value, encoding.nat.iterate, iteration_complexity.cost_zero] },
  { apply distance_le_trans',
    apply β.distance_le_of_normal_iteration 5,
    refl,
    simp [has_encoding.value, encoding.nat.iterate],
    apply distance_le_trans' (5 + (cfc a)) _ _ (n_ih (f a)),
    all_goals { clear n_ih },
    refl,
    simp [has_encoding.value, encoding.nat.iterate],
    apply distance_le_symm,
    apply distance_le_trans',
    apply β.distance_le_of_normal_iteration 5,
    simp,
    apply distance_le_symm,
    simp [encoding.nat.iterate],
    apply iteration_complexity.iterate_distance_le,
    apply cfp,
    refl,
    simp [iteration_complexity.cost_succ],
    ring }
end ⟩ ⟩

example:  (complexity church_model nat.mul) ≤ (λ (x y: ℕ), ((30*y + 43):ℕ)) :=
begin
  intros n m,
  simp only [complexity, complexity.cost_function.less_than_or_equal, has_complexity.value, fork, const, uncurry],
  ring_nf,
  norm_num,
  induction m,
  { simp only [iteration_complexity.cost_zero],
    ring_nf },
  simp only [iteration_complexity.cost_succ', function.iterate_succ', nat.mul_succ, add_mul, nat.add_assoc],
  nlinarith,
end

end nat
end complexity
end β
end utlc
end lambda_calculus