import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.beta.parallel
import logic.relation

namespace lambda_calculus
namespace utlc
namespace β

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

theorem β_of_parallel {f g : utlc}: f →∥ g → f ↠β g :=
begin
  intro pfg,
  induction f generalizing g,
  { simp at pfg, simp [← pfg] },
  { cases g,
    all_goals { simp at pfg },
    any_goals { contradiction },
    apply lambda_reduction_lambda,
    apply f_ih pfg },
  { cases parallel.dot_step_cases pfg with h h,
    all_goals { rcases h with ⟨x, y, hfx, hfy, hgxy⟩ },
    { rw [hgxy],
      apply dot_reduction_dot (f_ih_f hfx) (f_ih_g hfy) },
    rw [hgxy],
    simp,
    apply dot_reduction_substitution,
    apply f_ih_f hfx,
    apply f_ih_g hfy }
end

theorem parallel_of_β {f g : utlc}: f →β g → f →∥ g :=
begin
  induction f using lambda_calculus.utlc.notation_induction_on generalizing g,
  { simp },
  { intro hfg,
    rcases lambda_step_exists hfg with ⟨x, hgx, hfx⟩,
    rw [hgx],
    exact parallel.lambda_step_lambda (f_ih hfx) },
  { intro hfg,
    obtain hfg|hfg|hfg := dot_step_cases hfg;
    rcases hfg with ⟨x, hgx, hfx⟩;
    rw [hgx],
    { exact parallel.dot_step_substitution _ (parallel.step_refl _) (parallel.step_refl _) hfx },
    all_goals { apply parallel.dot_step_dot },
    apply f_ih_f hfx,
    refl,
    refl,
    apply f_ih_g hfx }
end

theorem parallel_iff_β {f g : utlc}: f ↠∥ g ↔ f ↠β g :=
begin
  split;
  intro p;
  induction p with b c pb pbc fb,
  { refl },
  { exact trans fb (β_of_parallel pbc) },
  { refl },
  { exact trans fb (relation.refl_trans_gen.single (parallel_of_β pbc)) }
end

theorem church_rosser {a b c : utlc} (hab : a ↠β b) (hac : a ↠β c): b ≡β c :=
begin
  unfold relation.join,
  rw [← parallel_iff_β] at hab hac,
  cases parallel.church_rosser hab hac with d hd,
  use d,
  simp only [parallel_iff_β] at hd,
  apply hd,
end

@[refl]
theorem equiv_refl (f : utlc): f ≡β f :=
  ⟨f, relation.refl_trans_gen.refl, relation.refl_trans_gen.refl⟩

@[symm]
theorem equiv_symm {a b: utlc}: a ≡β b → b ≡β a :=
by apply relation.symmetric_join

@[trans]
theorem equiv_trans {a b c : utlc}: a ≡β b → b ≡β c → a ≡β c :=
by apply relation.transitive_join (@relation.refl_trans_gen.trans _ _) @church_rosser

theorem lambda_equiv_lambda {f g : utlc}: f ≡β g → Λ f ≡β Λ g :=
begin
  intro p,
  cases p with c p,
  exact ⟨Λ c, lambda_reduction_lambda p.left, lambda_reduction_lambda p.right⟩
end

theorem dot_equiv_dot {f f' g g': utlc}: f ≡β f' → g ≡β g' → f·g ≡β f'·g' :=
begin
  intros p q,
  cases p with c p,
  cases q with d q,
  exact ⟨c·d, dot_reduction_dot p.left q.left, dot_reduction_dot p.right q.right⟩
end

theorem dot_equiv_dot_left {f f' g: utlc}: f ≡β f' → f·g ≡β f'·g :=
  λ p, dot_equiv_dot p (by refl)

theorem dot_equiv_dot_right {f g g': utlc}: g ≡β g' → f·g ≡β f·g' :=
  dot_equiv_dot (by refl)

theorem reduced_reduction_inj {f g: utlc}: reduced f → f ↠β g → f = g :=
begin
  intros hf p,
  induction p with x y hx hy fx,
  { refl },
  rw [←fx] at *,
  exfalso,
  apply (reduced_of_not_reduction _).mp hf _ hy
end

theorem reduced_equiv_inj {f g: utlc}: reduced f → reduced g → f ≡β g → f = g :=
begin
  intros hf hg p,
  cases p with x p,
  rw [reduced_reduction_inj hf p.left, reduced_reduction_inj hg p.right]
end

end β
end utlc
end lambda_calculus