import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.properties

namespace utlc

def extension : utlc → ℕ → utlc
| (↓m) := λ n, if m < n then ↓m else ↓(m + 1)
| (Λ f) := λ n, Λ f.extension (n + 1)
| (f·g) := λ n, (f.extension n)·(g.extension n)

theorem size_extension (f: utlc) (n : ℕ) : (f.extension n).size = f.size :=
begin
  induction f with _ f fh f g fh gh generalizing n,
  all_goals { simp[size, extension, apply_ite size] },
  rw [fh],
  rw [fh, gh]
end

@[simp]
def η_reduction (f g : utlc) := f = Λ (g.extension 0)·↓0

instance η_reduction.decidable_rel : decidable_rel η_reduction :=
begin
  intros f _,
  cases f,
  all_goals { dsimp [η_reduction], apply_instance },
end

theorem η_irrefl (f : utlc) : ¬ f.η_reduction f :=
begin
  induction f with _ f fh,
  all_goals { simp[extension] },
  intro h,
  have h2 := (show ∀ a b : utlc, a = b → a.size = b.size, by { intros a b h, simp[h] }),
  specialize h2 _ _ h,
  simp [size, size_extension] at h2,
  ring_nf at h2,
  norm_num at h2,
end

@[simp]
def η_reducible_step := reducible_step_of η_reduction

theorem η_reducible_step_irrefl (f : utlc) : ¬ f.η_reducible_step f :=
begin
  apply reducible_step_irrefl,
  apply η_irrefl,
end

theorem application_η_reducible_step_left_iff {f f' g : utlc}:
  η_reducible_step (f·g) (f'·g) ↔ η_reducible_step f f' :=
begin
  simp[reducible_step],
  intro,
  contrapose!,
  intro,
  apply η_reducible_step_irrefl
end

theorem application_η_reducible_step_right_iff {f g g': utlc}:
  η_reducible_step (f·g) (f·g') ↔ η_reducible_step g g' :=
begin
  simp[reducible_step],
  contrapose!,
  intro,
  apply η_reducible_step_irrefl
end

@[simp]
def η_reduced_step : utlc → bool
| (↓_) := true
| (Λ f) := match f with
  | (↓_) := true
  | (Λ _) := true
  | (f·g) := g ≠ ↓0 ∨ ¬ f.unused 0
  end
| (_·_) := true

@[simp]
def η_reduced (f : utlc) := reduced f η_reduced_step

theorem application_η_reduced {f g: utlc} :
  f.η_reduced ∧ g.η_reduced ↔ η_reduced (f·g) := by simp[reduced]

end utlc