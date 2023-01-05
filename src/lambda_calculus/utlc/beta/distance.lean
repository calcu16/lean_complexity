import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.beta.church_rosser
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.beta.normal
import lambda_calculus.distance

namespace lambda_calculus
namespace utlc
namespace β

def distance_le (n: ℕ) (a b: utlc) := distance_le has_β_reduction.step n a b

variables {a b c: utlc}
variables {n m nm: ℕ}

theorem distance_le_of_reduction: a ↠β b → ∃ n, distance_le n a b :=
begin
  intro h,
  induction h with _ _ _ hab,
  { exact ⟨0, distance_le_refl _⟩ },
  cases h_ih with n h_ih,
  exact ⟨n+1, distance_le_trans h_ih (distance_le_single hab)⟩
end

theorem distance_le_of_equiv: a ≡β b → ∃ n, distance_le n a b :=
begin
  intro h,
  rcases h with ⟨x, hax, hbx⟩,
  cases distance_le_of_reduction hax with n hax,
  cases distance_le_of_reduction hbx with m hbx,
  exact ⟨n+m, distance_le_trans hax (distance_le_symm hbx)⟩
end

theorem equiv_of_distance_le: distance_le n a b → a ≡β b :=
begin
  induction n generalizing a b,
  { intro p,
    rw [distance_le, distance_le_zero] at p,
    rw [p] },
  intro p,
  rcases distance_le_head p with ⟨x, hax, hxb⟩,
  apply equiv_trans _ (n_ih hxb),
  rw [distance_le_one] at hax,
  obtain h|h|h := hax,
  rw [h],
  refine ⟨x, relation.refl_trans_gen.single h, by refl⟩,
  refine ⟨a, by refl, relation.refl_trans_gen.single h⟩
end

theorem distance_le_of_normal_iteration (n: ℕ): normal_iteration n a = b → distance_le n a b :=
begin
  induction n generalizing a b,
  { simp [normal_iteration, distance_le, distance_le_zero] },
  simp [normal_iteration],
  rw [nat.succ_eq_add_one, nat.add_comm],
  intro p,
  apply distance_le_trans _ (n_ih p),
  rw distance_le_one,
  cases strategic_reduction_step_eq_or_reduction_step a _,
  exact or.inl h,
  exact or.inr (or.inl h)
end

theorem lambda_distance_le_lambda: distance_le n a b → distance_le n (Λ a) (Λ b) :=
begin
  apply distance_le_cong,
  simp,
end

theorem dot_distance_le_dot_left: distance_le n a b → distance_le n (a·c) (b·c) :=
begin
  simp [show ∀ x, x·c = (λ y, y·c) x, by simp],
  apply distance_le_cong,
  intros x y,
  simp,
  apply dot_step_dot_left
end

theorem dot_distance_le_dot_right: distance_le n a b → distance_le n (c·a) (c·b) :=
begin
  simp [show ∀ x, c·x = (λ y, c·y) x, by simp],
  apply distance_le_cong,
  intros x y,
  simp,
  apply dot_step_dot_right
end

end β
end utlc
end lambda_calculus