import lambda_calculus.utlc.basic
import lambda_calculus.utlc.identities
import lambda_calculus.utlc.reduction

namespace lambda_calculus
namespace utlc
namespace β

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

variables {f g f' g' x y z: utlc}

@[simp]
def head_step : utlc → utlc → Prop
| (↓ _) := λ g, false
| (Λ _) := λ g, false
| (f1 · f2) := match f1 with
  | (↓ _) := λ g, false
  | (Λ f1) := λ g, substitution f1 0 f2 = g
  | (_ · _) := λ g, false
  end

instance head_step.decidable_rel : decidable_rel head_step :=
begin
  intros f _,
  cases f,
  any_goals { simp [head_step], apply_instance },
  cases f_f,
  all_goals { simp [head_step], apply_instance },
end

@[simp] theorem lambda_head_step:
  head_step (Λ f) (Λ g) → head_step f g := by simp[head_step]

instance : has_β_reduction utlc := ⟨ reduction_step_of head_step ⟩

@[simp] theorem lambda_step_iff:
  (Λ f) →β (Λ g) ↔ f →β g :=
begin
  simp [has_β_reduction.step, reduction_step],
end

theorem dot_step_dot_left (g: utlc): f →β f' → f·g →β f'·g :=
begin
  intro p,
  simp [has_β_reduction.step, reduction_step],
  exact or.inr (or.inl p),
end

theorem dot_step_dot_right (f: utlc): g →β g' → f·g →β f·g' :=
begin
  intro p,
  simp [has_β_reduction.step, reduction_step],
  exact or.inr (or.inr p),
end

theorem lambda_dot_step_substitution (f g: utlc):  (Λ f)·g →β f[0:=g] :=
by simp [has_β_reduction.step, reduction_step]

theorem dot_dot_step_dot:
  (x·y·z) →β (f·g) → (x·y →β f ∧ z = g ∨ x·y=f ∧ z →β g) :=
begin
  intro a,
  simp [has_β_reduction.step] at *,
  rw [reduction_step] at a,
  cases a,
  { simp at a, contradiction },
  any_goals { assumption },
end

@[simp] theorem lambda_reduction_lambda:
  f ↠β g → (Λ f) ↠β (Λ g) :=
begin
  intro _,
  apply relation.refl_trans_gen.lift,
  simp,
  intros _ _ _,
  assumption,
  assumption
end

@[simp] theorem dot_reduction_dot:
  f ↠β g → f' ↠β g' → (f·f') ↠β (g·g') :=
begin
  intros _ _,
  apply @trans _ _ _ _ (f·g'),
  simp [show ∀ g, f·g = (λg, f·g) g, by simp],
  apply relation.refl_trans_gen.lift,
  intros _ _ _,
  simp [has_β_reduction.step, reduction_step],
  right,
  right,
  assumption,
  assumption,
  simp [show ∀ f, f·g' = (λf, f·g') f, by simp],
  apply relation.refl_trans_gen.lift,
  intros _ _ _,
  simp [has_β_reduction.step, reduction_step],
  right,
  left,
  assumption,
  assumption,
  apply_instance,
end

@[simp] theorem dot_reduction_substitution:
  f ↠β (Λ g) → f' ↠β g' → (f·f') ↠β g[0:=g'] :=
begin
  intros _ _,
  apply @trans _ _  _ _ (f·g'),
  apply dot_reduction_dot,
  refl,
  assumption,
  apply @trans _ _ _ _ ((Λ g)·g'),
  apply dot_reduction_dot,
  assumption,
  refl,
  apply relation.refl_trans_gen.single,
  simp [has_β_reduction.step, reduction_step],
  apply_instance,
  apply_instance,
end

@[simp]
def head_reduced : utlc → bool
| (↓ _) := true
| (Λ _) := true
| (f·g) := match f with
  | (↓ _) := true
  | (Λ _) := false
  | (f·g) := true
  end

@[simp]
def reduced := λ f, lambda_calculus.utlc.reduced f head_reduced

@[simp] theorem lambda_reduced_iff:
  reduced (Λ f) ↔ reduced f := by simp [lambda_calculus.utlc.reduced]

theorem lambda_of_reduced_and_closed: reduced f → f.closed → ∃ g, f = Λ g :=
begin
  induction f with _ f _ f g fh,
  { simp [closed, closed_below] },
  { intros _ _,
    use f,
    refl },
  simp [lambda_calculus.utlc.reduced, closed_below],
  cases f with _ _ f f',
  any_goals { { simp [lambda_calculus.utlc.reduced, closed_below] } },
  intros _ p _ q _,
  specialize fh p q,
  simp at fh,
  contradiction
end


def not_reduction_of_reduced {f: utlc}: reduced f → ∀ g, ¬ f →β g :=
begin
  induction f,
  all_goals { simp [has_β_reduction.step, reduction_step, lambda_calculus.utlc.reduced] },
  { intros p g,
    cases g,
    all_goals { simp [has_β_reduction.step, reduction_step] },
    exact f_ih p _ },
  { intros p q r g,
    cases g,
    all_goals { simp [has_β_reduction.step, reduction_step] },
    any_goals { intro h, cases h, revert h },
    any_goals {
      cases f_f,
      any_goals { simp },
      simp [lambda_calculus.utlc.reduced] at p,
      contradiction },
    { cases h,
      all_goals { cases h },
      specialize f_ih_f q g_f,
      contradiction,
      specialize f_ih_g r g_g,
      contradiction } }
end

end β
end utlc
end lambda_calculus