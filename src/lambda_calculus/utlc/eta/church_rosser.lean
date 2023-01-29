import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.eta.basic
import logic.relation

namespace lambda_calculus
namespace utlc
namespace η

theorem step_church_rosser {a b c :utlc}: a →η b → a →η c →
  ∃ d, relation.refl_gen has_η_reduction.step b d
    ∧ c ↠η d :=
begin
  induction a generalizing b c,
  all_goals { simp },
  { intros hab hac,
    cases lambda_step_cases hab with x hab,
    cases hab with hab hab,
    all_goals { cases lambda_step_cases hac with y hac },
    all_goals { cases hac with hac hac },
    { cases a_ih hab.right hac.right with z ih,
      use Λ z,
      rw [hab.left, hac.left],
      refine ⟨ lambda_refl_reduction_step_lambda ih.left, lambda_reduction_lambda ih.right ⟩ },
    { rw [hab.left, hac.left],
      rw [hac.right] at hab,
      cases x,
      all_goals { simp [has_η_reduction.step, and_assoc] at hab },
      any_goals { contradiction },
      simp,
      have h: x_f.uses 0 = 0,
      { rw [← reduction_step_uses hab.right.right, shift_uses_self] },
      cases shift_of_uses_zero h with x' hx,
      use x',
      rw [hab.right.left, hx],
      split,
      apply relation.refl_gen.single,
      apply lambda_step_head,
      apply relation.refl_trans_gen.single,
      apply reduction_step_shift 0,
      rw [← hx],
      apply hab.right.right },
    { rw [hab.left, hac.left],
      rw [hab.right] at hac,
      cases y,
      all_goals { simp [has_η_reduction.step, and_assoc] at hac },
      any_goals { contradiction },
      simp,
      have h: y_f.uses 0 = 0,
      { rw [← reduction_step_uses hac.right.right, shift_uses_self] },
      cases shift_of_uses_zero h with y' hy,
      use y',
      rw [hac.right.left, hy],
      split,
      apply relation.refl_gen.single,
      apply reduction_step_shift 0,
      rw [← hy],
      apply hac.right.right,
      apply relation.refl_trans_gen.single,
      apply lambda_step_head },
    { simp [hac.right, ← hac.left] at hab,
      use x,
      simp [hab],
      exact ⟨ by refl, by refl ⟩ } },
  { intros hab hac,
    rcases dot_step_cases hab with ⟨x, y, bxy, hab⟩,
    cases hab with hab hab,
    all_goals { rcases dot_step_cases hac with ⟨x', y', cxy, hac⟩ },
    all_goals { cases hac with hac hac },
    { cases a_ih_f hab.right hac.right with d ih,
      use d·y,
      rw [bxy, cxy, hac.left, ← hab.left],
      refine ⟨ dot_refl_reduction_step_dot_left ih.left _, dot_reduction_dot_left ih.right ⟩
    },
    { use x·y',
      rw [bxy, cxy, hab.left, hac.left],
      refine ⟨ dot_refl_reduction_step_dot_right _ _, dot_reduction_dot_left _ ⟩,
      apply relation.refl_gen.single,
      apply hac.right,
      apply relation.refl_trans_gen.single,
      apply hab.right },
    { use x'·y,
      rw [bxy, cxy, hab.left, hac.left],
      refine ⟨ dot_refl_reduction_step_dot_left _ _, dot_reduction_dot_right _ ⟩,
      apply relation.refl_gen.single,
      apply hac.right,
      apply relation.refl_trans_gen.single,
      apply hab.right },
    { cases a_ih_g hab.right hac.right with d ih,
      use x·d,
      rw [bxy, cxy, hac.left, hab.left],
      refine ⟨ dot_refl_reduction_step_dot_right ih.left _, dot_reduction_dot_right ih.right ⟩
    }
  }
end

theorem church_rosser {a b c :utlc}: a ↠η b → a ↠η c → b ≡η c :=
  relation.church_rosser @step_church_rosser

@[refl]
theorem equiv_refl (f : utlc): f ≡η f :=
  ⟨f, relation.refl_trans_gen.refl, relation.refl_trans_gen.refl⟩

@[symm]
theorem equiv_symm {a b: utlc}: a ≡η b → b ≡η a :=
begin
  apply relation.symmetric_join
end

@[trans]
theorem equiv_trans {a b c : utlc}: a ≡η b → b ≡η c → a ≡η c :=
begin
  apply relation.transitive_join,
  apply relation.refl_trans_gen.trans,
  apply @church_rosser,
end

theorem reduced_reduction_inj {f g: utlc}: reduced f → f ↠η g → f = g :=
begin
  intros hf p,
  induction p with x y hx hy fx,
  { refl },
  rw [←fx] at *,
  exfalso,
  apply (reduced_iff_not_reduction _).mp hf _ hy
end

theorem reduced_equiv_inj {f g: utlc}: reduced f → reduced g → f ≡η g → f = g :=
begin
  intros hf hg p,
  cases p with x p,
  rw [reduced_reduction_inj hf p.left, reduced_reduction_inj hg p.right]
end

end η
end utlc
end lambda_calculus