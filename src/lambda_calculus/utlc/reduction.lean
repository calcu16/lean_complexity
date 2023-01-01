import lambda_calculus.utlc.basic

namespace lambda_calculus
namespace utlc

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

def reduction_step : utlc → utlc → (utlc → utlc → Prop) → Prop
| (↓ n) := λ g r, r (↓ n) g
| (Λ f) := λ g r, r (Λ f) g ∨ match g with
  | (↓ _) := false
  | (Λ g) := reduction_step f g r
  | (_·_) := false
  end
| (f1 · f2) := λ g r, r (f1 · f2) g ∨ match g with
  | (↓_) := false
  | (Λ _) := false
  | (g1 · g2) :=
    ((reduction_step f1 g1 r) ∧ f2 = g2) ∨ (f1 = g1 ∧ (reduction_step f2 g2 r))
  end

theorem reduction_step_irrefl {head_step : utlc → utlc → Prop} :
  (∀ f, ¬ head_step f f) → (∀ f, ¬ reduction_step f f head_step) :=
begin
  intros pf f,
  induction f with _ f fh f g fh gh,
  all_goals { simp[reduction_step, pf] },
  exact fh,
  exact not_or fh gh,
end

@[simp]
def reduction_step_of := λ r f g, reduction_step f g r

theorem reduction_step_lambda {f f' : utlc} {head_step : utlc → utlc → Prop}:
  reduction_step f f' head_step → reduction_step (Λ f) (Λ f') head_step := or.inr

theorem application_reduction_step_left {f f' g : utlc} {head_step : utlc → utlc → Prop}:
  reduction_step f f' head_step → reduction_step (f·g) (f'·g) head_step :=
begin
  intro n,
  exact or.inr (or.inl ⟨n, rfl⟩)
end

theorem application_reduction_step_right {f g g': utlc} {head_step : utlc → utlc → Prop}:
  reduction_step g g' head_step → reduction_step (f·g) (f·g') head_step :=
begin
  intro n,
  exact or.inr (or.inr ⟨rfl, n⟩)
end

def reduced : utlc → (utlc → bool) → bool
| (↓ n) := λ p, p (↓ n)
| (Λ f) := λ p, p (Λ f) ∧ reduced f p
| (f · g) := λ p, p (f · g) ∧ reduced f p ∧ reduced g p

end utlc
end lambda_calculus