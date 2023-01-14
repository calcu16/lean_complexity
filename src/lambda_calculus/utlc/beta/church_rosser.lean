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
  { cases parallel.dot_step pfg with h h,
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
  intro hfg,
  induction f using lambda_calculus.utlc.substitution_induction_on generalizing g,
  all_goals { cases g, all_goals { simp } },
  any_goals { simp [lambda_step_iff, dot_step_iff] at hfg, contradiction },
  { simp at hfg,
    apply f_hx hfg },
  { simp [dot_step_cases, and.assoc] at hfg, exact ⟨f_hx hfg.right, hfg.left⟩ },
  any_goals { simp [dot_step_iff, and.assoc] at hfg,
    rw [← hfg],
    apply parallel.dot_step_substitution,
    all_goals { refl }  },
  { simp [dot_step_iff, lambda_step_iff, and.assoc] at hfg,
    obtain hfg|hfg|hfg := hfg,
    { rw [←hfg],
      apply parallel.dot_step_substitution,
      all_goals { refl }, },
    { rcases hfg with ⟨hfg, x, hgx, hfx⟩,
      apply parallel.dot_step_dot,
      rw [hgx],
      rw parallel.lambda_step_lambda,
      apply f_hx,
      apply hfx,
      rw [hfg] },
    { apply parallel.dot_step_dot,
      rw [hfg.left],
      apply f_hy,
      apply hfg.right } },
  { rw [dot_step_iff] at hfg,
    simp [and.assoc] at hfg,
    cases hfg;
    apply parallel.dot_step_dot;
    try { rw [hfg.left] };
    try { apply f_hxy };
    try { apply f_hz };
    apply hfg.right,
  }
end

theorem parallel_iff_β {f g : utlc}: f ↠∥ g ↔ f ↠β g :=
begin
  split,
  intro p,
  induction p with b c pb pbc fb,
  refl,
  apply trans,
  apply fb,
  apply β_of_parallel,
  apply pbc,
  intro p,
  induction p with b c pb pbc fb,
  refl,
  apply trans,
  apply fb,
  apply relation.refl_trans_gen.single,
  apply parallel_of_β,
  apply pbc,
end

theorem church_rosser {a b c : utlc} (hab : a ↠β b) (hac : a ↠β c): b ≡β c :=
begin
  unfold relation.join,
  rw [← parallel_iff_β] at hab hac,
  cases parallel.church_rosser hab hac with d hd,
  use d,
  simp [parallel_iff_β] at hd,
  apply hd,
end

@[refl]
theorem equiv_refl (f : utlc): f ≡β f :=
  ⟨f, relation.refl_trans_gen.refl, relation.refl_trans_gen.refl⟩

@[symm]
theorem equiv_symm {a b: utlc}: a ≡β b → b ≡β a :=
begin
  apply relation.symmetric_join
end

@[trans]
theorem equiv_trans {a b c : utlc}: a ≡β b → b ≡β c → a ≡β c :=
begin
  apply relation.transitive_join,
  apply relation.refl_trans_gen.trans,
  apply church_rosser,
end

theorem lambda_equiv_lambda {f g : utlc}: f ≡β g → Λ f ≡β Λ g :=
begin
  intro p,
  cases p with c p,
  use Λ c,
  exact ⟨lambda_reduction_lambda p.left, lambda_reduction_lambda p.right⟩
end

theorem dot_equiv_dot {f f' g g': utlc}: f ≡β f' → g ≡β g' → f·g ≡β f'·g' :=
begin
  intros p q,
  cases p with c p,
  cases q with d q,
  use c·d,
  exact ⟨dot_reduction_dot p.left q.left, dot_reduction_dot p.right q.right⟩
end

theorem dot_equiv_dot_left {f f' g: utlc}: f ≡β f' → f·g ≡β f'·g :=
begin
  intro p,
  apply dot_equiv_dot p,
  refl,
end


theorem dot_equiv_dot_right {f g g': utlc}: g ≡β g' → f·g ≡β f·g' :=
begin
  apply dot_equiv_dot,
  refl
end

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