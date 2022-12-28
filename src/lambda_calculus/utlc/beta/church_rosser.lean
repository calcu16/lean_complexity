import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.beta.basic
import logic.relation

namespace utlc

mutual def parallel_reduction_step_helper, parallel_reduction_step
with parallel_reduction_step_helper : utlc → utlc → Prop
| (↓_) := λ _, false
| (Λ f) := λ g, parallel_reduction_step f g
| (_·_) := λ _, false
with parallel_reduction_step : utlc → utlc → Prop
| (↓n) := λ x, x = (↓n)
| (Λ f) := λ x, ∃ g, parallel_reduction_step f g ∧ x = Λ g 
| (f·f') := λ x,
  (∃ g g', parallel_reduction_step f g ∧ parallel_reduction_step f' g' ∧ x = g·g') ∨
  ∃ g g', parallel_reduction_step_helper f g ∧  parallel_reduction_step f' g' ∧ x = g.substitution 0 g'

attribute [simp] parallel_reduction_step_helper

@[refl]
theorem parallel_reduction_step_refl (f : utlc): parallel_reduction_step f f :=
begin
  induction f with _ _ _ f f' hf hf',
  all_goals { simp [parallel_reduction_step] },
  { assumption },
  exact or.inl ⟨hf, hf'⟩
end

theorem lambda_parallel_reduction {f g : utlc}: parallel_reduction_step f g → parallel_reduction_step (Λ f) (Λ g) :=
by simp [parallel_reduction_step]

theorem application_parallel_reduction {f f' g g': utlc}: parallel_reduction_step f f' → parallel_reduction_step g g' → parallel_reduction_step (f·g) (f'·g') :=
begin
  simp [parallel_reduction_step],
  intros p q,
  exact or.inl ⟨p, q⟩,
end

theorem application_substitution_parallel_reduction {f f' g g': utlc}: parallel_reduction_step f f' → parallel_reduction_step g g' → parallel_reduction_step ((Λ f)·g) (f'.substitution 0 g') :=
begin
  simp [parallel_reduction_step],
  intros p q,
  exact or.inr ⟨f', p, g', q, rfl⟩,
end

theorem shift_parallel_reduction {f x: utlc} (n m : ℕ):
    parallel_reduction_step f x → parallel_reduction_step (f.shift n m) (x.shift n m) :=
begin
  induction f using utlc.apply_induction_on generalizing x n m,
  { simp [parallel_reduction_step],
    intro xf,
    rw [xf] },
  { simp [parallel_reduction_step],
    intros g fg xg,
    rw xg,
    simp [shift],
    apply lambda_parallel_reduction,
    apply f_hx,
    apply fg },
  { simp [parallel_reduction_step],
    intros g g' xfg,
    rw [xfg],
    apply application_parallel_reduction,
    refl,
    apply f_hx,
    apply g' },
  { unfold parallel_reduction_step,
    intro h,
    cases h,
    all_goals { rcases h with ⟨g, g', hfg, hfg', xgg'⟩, rw [xgg'] },
    rcases hfg with ⟨y, hfy, gy⟩,
    rw [gy],
    exact application_parallel_reduction (f_hx' _ _ (lambda_parallel_reduction hfy)) (f_hy _ _ hfg'),
    { simp at hfg,
      simp [shift, shift_substitution],
      exact application_substitution_parallel_reduction (f_hx _ _ hfg) (f_hy _ _ hfg') } },
  { intro h,
    rw [parallel_reduction_step] at h,
    simp at h,
    rcases h with ⟨g, hfg, g', hfg', xgg'⟩,
    rw [xgg', shift, show (g·g').shift n m = (g.shift n m)·(g'.shift n m), by simp[shift]],
    simp,
    exact application_parallel_reduction (f_hxy _ _ hfg) (f_hz _ _ hfg')
  }
end

theorem substitution_parallel_reduction {f f' g g': utlc} (n : ℕ): parallel_reduction_step f f' → parallel_reduction_step g g' → parallel_reduction_step (f.substitution n g) (f'.substitution n g') :=
begin
  induction f using utlc.apply_induction_on generalizing f' g g' n,
  all_goals { intros hf hg },
  all_goals { rw [parallel_reduction_step] at hf },
  { rw hf,
    simp [substitution],
    split_ifs,
    refl,
    apply shift_parallel_reduction,
    assumption,
    refl },
  { rcases hf with ⟨x, hfx, fx'⟩,
    rw [fx'],
    simp [substitution],
    apply lambda_parallel_reduction,
    apply f_hx,
    assumption,
    assumption },
  { simp at hf,
    rcases hf with ⟨x, hfx, y, hfy, fxy⟩,
    rw [fxy],
    rw [substitution, show (x·y).substitution n g' = (x.substitution n g')·(y.substitution n g'), by simp[substitution]],
    simp,
    apply application_parallel_reduction,
    apply f_hn,
    assumption,
    assumption,
    apply f_hx,
    assumption,
    assumption },
  { simp at hf,
    cases hf,
    rcases hf with ⟨x, hfx, y, hfy, fxy⟩,
    rw [fxy],
    rw [substitution, show (x·y).substitution n g' = (x.substitution n g')·(y.substitution n g'), by simp[substitution]],
    simp,
    apply application_parallel_reduction,
    apply f_hx',
    assumption,
    assumption,
    apply f_hy,
    assumption,
    assumption,
    rcases hf with ⟨x, hfx, y, hfy, fxy⟩,
    rw [fxy],
    simp [substitution, substitution_substitution'],
    apply application_substitution_parallel_reduction,
    apply f_hx,
    assumption,
    assumption,
    apply f_hy,
    assumption,
    assumption,

    -- apply application_substitution_parallel_reduction,
    -- fx -> x, g -> g, fy -> y
    -- (x.substitution (n+1) g').substitution 0 (y.substitution n g')
    -- = (x.substitution 0 y).substitution n g'
    -- (Λ x).substitution y
    -- 



  },
  { simp at hf,
    rcases hf with ⟨x, hfx, y, hfy, fxy⟩,
    rw [fxy],
    rw [substitution, show (x·y).substitution n g' = (x.substitution n g')·(y.substitution n g'), by simp[substitution]],
    simp,
    apply application_parallel_reduction,
    apply f_hxy,
    assumption,
    assumption,
    apply f_hz,
    assumption,
    assumption }
end

theorem parallel_reduction_church_rosser: ∀ {a b c}, parallel_reduction_step a b → parallel_reduction_step a c → ∃ d, parallel_reduction_step b d ∧ parallel_reduction_step c d :=
begin
  intro a,
  induction a using utlc.apply_induction_on,
  all_goals { intros b c },
  { simp [parallel_reduction_step],
    intros ba ca,
    use ↓a,
    rw [ba, ca],
    exact ⟨by refl, by refl⟩ },
  { simp [parallel_reduction_step],
    intros x ax bx y ay cy,
    rcases a_hx ax ay with ⟨d, xd, yd⟩,
    use (Λ d),
    rw [bx, cy],
    exact ⟨lambda_parallel_reduction xd, lambda_parallel_reduction yd⟩ },
  { simp [parallel_reduction_step],
    intros x hax bax y hay cay,
    rcases a_hx hax hay with ⟨d, xd, yd⟩,
    rw [bax, cay],
    use (↓a_n·d),
    exact ⟨application_parallel_reduction (by refl) xd,  application_parallel_reduction (by refl) yd⟩ },
  { intros h h',
    rw [parallel_reduction_step] at h h',
    cases h,
    all_goals { cases h' },
    all_goals { rcases h with ⟨f, f', haf, haf', bff'⟩ },
    any_goals { unfold parallel_reduction_step_helper at haf },
    all_goals { rcases h' with ⟨g, g', hag, hag', cgg'⟩ },
    any_goals { unfold parallel_reduction_step_helper at hag },
    any_goals { simp[parallel_reduction_step] at haf },
    any_goals { simp[parallel_reduction_step] at hag },
    any_goals { rcases haf with ⟨ lf, haf, ef⟩ },
    any_goals { rcases hag with ⟨ lg, hag, eg⟩ },
    any_goals { specialize a_hx haf hag },
    any_goals { rcases a_hx with ⟨d, hfd, hgd⟩ },
    any_goals { rcases a_hy haf' hag' with ⟨d', hfd', hgd'⟩ },
    any_goals { rw [bff', cgg'] },
    any_goals { rw [ef] },
    any_goals { rw [eg] },
    { use (Λ d)·d',
      split,
      apply application_parallel_reduction (lambda_parallel_reduction hfd) hfd',
      apply application_parallel_reduction (lambda_parallel_reduction hgd) hgd'
    },
    { 
      use (d.substitution 0 d'),
      split,
      apply application_substitution_parallel_reduction,
      apply hfd,
      apply hfd',
      apply substitution_parallel_reduction,
      assumption, assumption,
    },
    { use (d.substitution 0 d'),
      split,
      apply substitution_parallel_reduction,
      assumption, assumption,
      apply application_substitution_parallel_reduction,
      assumption,
      assumption,
    },
    { use (d.substitution 0 d'),
      split,
      apply substitution_parallel_reduction,
      assumption, assumption,
      apply substitution_parallel_reduction,
      assumption,
      assumption,
    },
  },
  { intros hab hac,
    rw [parallel_reduction_step] at hab hac,
    simp at hab hac,
    rcases hab with ⟨xy, haxy, z, haz, bxyz⟩,
    rcases hac with ⟨xy', haxy', z', haz', cxyz'⟩,
    rcases a_hxy haxy haxy' with ⟨d, xyd, xyd'⟩,
    rcases a_hz haz haz' with ⟨d', zd', zd''⟩,
    use (d·d'),
    rw [bxyz, cxyz'],
    exact ⟨application_parallel_reduction xyd zd', application_parallel_reduction xyd' zd''⟩ }
end

theorem parallel_reduction_church_rosser' {a b c : utlc} (hab : relation.refl_trans_gen parallel_reduction_step a b) (hac : relation.refl_trans_gen parallel_reduction_step a c)
  : relation.join (relation.refl_trans_gen parallel_reduction_step) b c :=
begin
  refine relation.church_rosser _ hab hac,
  intros x y z xy xz,
  rcases parallel_reduction_church_rosser xy xz with ⟨d, yd, zd⟩,
  exact ⟨d, relation.refl_gen.single yd, relation.refl_trans_gen.single zd⟩
end

theorem β_trans_lambda {f g : utlc}: relation.refl_trans_gen β_reducible_step f g → relation.refl_trans_gen β_reducible_step Λ f Λ g :=
begin
  intro p,
  apply relation.refl_trans_gen.lift,
  intros f g,
  apply @lambda_reducible_step f g,
  exact p
end

theorem β_trans_application {f f' g g': utlc}: relation.refl_trans_gen β_reducible_step f f' → relation.refl_trans_gen β_reducible_step g g' → relation.refl_trans_gen β_reducible_step (f·g) (f'·g') :=
begin
  intros p q,
  apply @trans _ _ _ _ (f·g'),
  simp [show ∀ g, f·g = (λg, f·g) g, by simp],
  apply relation.refl_trans_gen.lift,
  intros g g',
  apply @application_reducible_step_right f g g',
  exact q,
  simp [show ∀ f, f·g' = (λf, f·g') f, by simp],
  apply relation.refl_trans_gen.lift,
  intros f f',
  apply @application_reducible_step_left f f' g',
  exact p,
  apply_instance
end

theorem β_of_parallel {f g : utlc}: parallel_reduction_step f g → relation.refl_trans_gen β_reducible_step f g :=
begin
  intro pfg,
  induction f using utlc.apply_induction_on generalizing g,
  { simp[parallel_reduction_step] at pfg,
    rw [pfg] },
  { simp[parallel_reduction_step] at pfg,
    cases pfg with g' pfg,
    rw [pfg.right],
    exact β_trans_lambda (f_hx pfg.left) },
  all_goals { rw [parallel_reduction_step] at pfg, simp at pfg },
  { rcases pfg with ⟨x, hfx, y, hfy, gxy⟩,
    rw [gxy],
    apply β_trans_application,
    apply f_hn,
    apply hfx,
    apply f_hx,
    apply hfy },
  { cases pfg,
    rcases pfg with ⟨x, hfx, y, hfy, gxy⟩,
    rw [gxy],
    apply β_trans_application,
    apply f_hx',
    apply hfx,
    apply f_hy,
    apply hfy,
    rcases pfg with ⟨x, hfx, y, hfy, gxy⟩,
    specialize f_hx hfx,
    specialize f_hy hfy,
    apply relation.refl_trans_gen.trans,
    apply β_trans_application,
    apply β_trans_lambda,
    apply f_hx,
    apply f_hy,
    apply relation.refl_trans_gen.single,
    simp [reducible_step],
    left,
    rw [gxy] },
  { rcases pfg with ⟨x, hfx, y, hfy, gxy⟩,
    rw [gxy],
    apply β_trans_application,
    apply f_hxy,
    apply hfx,
    apply f_hz,
    apply hfy },
end

theorem parallel_of_β {f g : utlc}: β_reducible_step f g → parallel_reduction_step f g :=
begin
  intro hfg,
  induction f using utlc.apply_induction_on generalizing g,
  all_goals { cases g, all_goals { simp } },
  all_goals { simp [reducible_step] at hfg },
  any_goals { contradiction },
  { apply lambda_parallel_reduction,
    apply f_hx,
    apply hfg },
  { cases hfg with hg hfg,
    apply application_parallel_reduction,
    rw [hg],
    apply f_hx,
    apply hfg },
  { simp[parallel_reduction_step],
    use f_x,
    split,
    refl,
    use f_y,
    split,
    refl,
    rw [hfg] },
  { simp[parallel_reduction_step],
    use f_x,
    split,
    refl,
    use f_y,
    split,
    refl,
    rw [hfg], },
  { cases hfg,
    rw [← hfg],
    apply application_substitution_parallel_reduction,
    refl,
    refl,
    cases hfg,
    cases g_f,
    any_goals { simp[reducible_step] at hfg },
    any_goals { contradiction },
    simp,
    apply application_parallel_reduction,
    apply lambda_parallel_reduction,
    apply f_hx,
    apply hfg.left,
    rw [hfg.right],
    apply application_parallel_reduction,
    rw [hfg.left],
    apply f_hy,
    apply hfg.right },
  { cases hfg,
    all_goals { apply application_parallel_reduction },
    apply f_hxy,
    apply hfg.left,
    rw [hfg.right],
    rw [hfg.left],
    apply f_hz,
    apply hfg.right }
end

theorem parallel_iff_β {f g : utlc}: relation.refl_trans_gen parallel_reduction_step f g ↔ relation.refl_trans_gen β_reducible_step f g :=
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

theorem β_church_rosser {a b c : utlc} (hab : relation.refl_trans_gen β_reducible_step a b) (hac : relation.refl_trans_gen β_reducible_step a c): relation.join (relation.refl_trans_gen β_reducible_step) b c :=
begin
  unfold relation.join,
  rw [← parallel_iff_β] at hab hac,
  cases parallel_reduction_church_rosser' hab hac with d hd,
  use d,
  simp [parallel_iff_β] at hd,
  apply hd,
end

end utlc
