import lambda_calculus.utlc.basic
import lambda_calculus.utlc.identities
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.eta.basic


namespace lambda_calculus
namespace utlc
namespace βη

def head_step (f g: utlc) := β.head_step f g ∨ η.head_step f g

instance : has_βη_reduction utlc := ⟨ reduction_step_of head_step ⟩

theorem step_iff (f g: utlc): f →βη g ↔ f →β g ∨ f →η g :=
begin
  induction f generalizing g;
  simp only [lambda_notation, dot_notation, has_βη_reduction.step] at *,
  { simp [head_step] },
  { simp [lambda_reduction_step_iff, head_step, η.lambda_step_iff, β.lambda_step_iff, f_ih,
      and_or_distrib_left, exists_or_distrib,
      @or.left_comm _ (f_f = g ↑¹ 0 · ↓0)] },
  { simp [dot_reduction_step_iff, head_step, η.dot_step_iff', β.dot_step_iff, f_ih_f, f_ih_g,
      and_or_distrib_left, exists_or_distrib, and.assoc, or.assoc],
    itauto }
end

theorem reduction_of_beta {f g: utlc}: f ↠β g → f ↠βη g :=
begin
  intro p,
  induction p with x g hfx hxg ih,
  refl,
  apply trans ih (relation.refl_trans_gen.single _),
  rw [step_iff],
  exact or.inl hxg,
end

theorem reduction_of_eta {f g: utlc}: f ↠η g → f ↠βη g :=
begin
  intro p,
  induction p with x g hfx hxg ih,
  refl,
  apply trans ih (relation.refl_trans_gen.single _),
  rw [step_iff],
  exact or.inr hxg,
end

def head_reduced (f: utlc): bool := β.head_reduced f ∧ η.head_reduced f

def reduced := reduced_of head_reduced

theorem reduced_iff_no_reduction {f: utlc}: reduced f ↔ ∀ g, ¬ f →βη g :=
begin
  apply reduced_iff_not_reduction_step,
  intro f,
  simp [head_reduced, head_step, β.not_head_step_iff_head_reduced, η.head_reduced_iff_not_head_step,
    forall_and_distrib, not_or_distrib],
end 

end βη
end utlc
end lambda_calculus