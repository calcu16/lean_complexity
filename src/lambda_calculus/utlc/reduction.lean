import lambda_calculus.utlc.basic

namespace utlc

def reducible_step : utlc → utlc → (utlc → utlc → Prop) → Prop
| (↓ n) := λ g r, r (↓ n) g
| (Λ f) := λ g r, r (Λ f) g ∨ match g with
  | (↓ _) := false
  | (Λ g) := reducible_step f g r
  | (_·_) := false
  end
| (f1 · f2) := λ g r, r (f1 · f2) g ∨ match g with
  | (↓_) := false
  | (Λ _) := false
  | (g1 · g2) :=
    ((reducible_step f1 g1 r) ∧ f2 = g2) ∨ (f1 = g1 ∧ (reducible_step f2 g2 r))
  end

theorem reducible_step_irrefl {step : utlc → utlc → Prop} :
  (∀ f, ¬ step f f) → (∀ f, ¬ reducible_step f f step) :=
begin
  intros pf f,
  induction f with _ f fh f g fh gh,
  all_goals { simp[reducible_step, pf] },
  exact fh,
  exact not_or fh gh,
end

@[simp]
def reducible_step_of := λ r f g, reducible_step f g r

theorem lambda_reducible_step {f f' : utlc} {step : utlc → utlc → Prop}:
  reducible_step f f' step → reducible_step (Λ f) (Λ f') step := or.inr

theorem application_reducible_step_left {f f' g : utlc} {step : utlc → utlc → Prop}:
  reducible_step f f' step → reducible_step (f·g) (f'·g) step :=
begin
  intro n,
  exact or.inr (or.inl ⟨n, rfl⟩)
end

theorem application_reducible_step_right {f g g': utlc} {step : utlc → utlc → Prop}:
  reducible_step g g' step → reducible_step (f·g) (f·g') step :=
begin
  intro n,
  exact or.inr (or.inr ⟨rfl, n⟩)
end

def reduced : utlc → (utlc → bool) → bool
| (↓ n) := λ p, p (↓ n)
| (Λ f) := λ p, p (Λ f) ∧ reduced f p
| (f · g) := λ p, p (f · g) ∧ reduced f p ∧ reduced g p

end utlc