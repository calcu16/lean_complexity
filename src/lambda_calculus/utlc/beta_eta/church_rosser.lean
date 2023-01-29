import lambda_calculus.utlc.basic
import lambda_calculus.utlc.identities
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.beta.church_rosser
import lambda_calculus.utlc.eta.basic
import lambda_calculus.utlc.eta.normal
import lambda_calculus.utlc.eta.church_rosser
import lambda_calculus.utlc.beta_eta.basic
import logic.relation


namespace lambda_calculus
namespace utlc
namespace βη

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

theorem βη_diamond_step {a b c: utlc}:
   a →β b → a →η c →
   ∃ x, b ↠η x ∧ (c = x ∨ c →β x) :=
begin
  induction a generalizing b c;
  simp;
  intros hab hac,
  { rcases β.lambda_step_exists hab with ⟨b₁, hb₁, hab⟩,
    cases η.lambda_step_cases' hac with hac hac;
    rcases hac with ⟨c₁, hc₁, hac⟩;
     rw [hb₁, hc₁],
    { rcases a_ih hab hac with ⟨x, hbx, hcx⟩,
      use Λ x,
      refine ⟨ η.lambda_reduction_lambda hbx, _ ⟩,
      simp [hcx] },
    rw [hac] at hab,
    obtain hab|hab|hab := β.dot_step_cases hab;
    rcases hab with ⟨b₂, hb₂, hab⟩,
    { 
      cases shift_of_uses_zero (show b₂.uses 1 = 0, begin
        rw [← lambda_uses, ← hab],
        exact shift_uses_self _ _,
      end) with b₃ hb₃,
      rw [hb₃, ← lambda_shift, shift_inj_iff] at hab,
      rw [hab, hb₂, hb₃, shift_succ_substitiution_down],
      use Λ b₃,
      exact ⟨ by refl, or.inl rfl⟩ },
    { rw [hb₂],
      cases shift_of_uses_zero (β.uses_zero_step hab (shift_uses_self _ _)) with b₃ hb₃,
      rw [hb₃],
      rw [hb₃] at hab,
      use b₃,
      split,
      apply relation.refl_trans_gen.single,
      apply η.lambda_step_head,
      right,
      apply (shift_reduction_step_shift_iff _).mp,
      apply hab,
      apply β.shift_head_step_shift },
    { simp at hab, contradiction } },
  { obtain hab|hab|hab := β.dot_step_cases hab;
    cases η.dot_step_cases' hac with hac hac;
    rcases hab with ⟨x, hax, hxb⟩;
    rcases hac with ⟨y, z, hza, hcyz, hay⟩,
    { rw [hax, ←hza, hcyz],
      rw [hxb] at hay,
      cases η.lambda_step_cases' hay with hay hay;
      rcases hay with ⟨y₁, hy₁, hxy₁⟩,
      { rw [hy₁],
        use y₁[0:=z],
        split,
        apply substitution_reduction_step_left,
        apply η.head_step_substitution,
        apply hxy₁,
        right,
        apply β.lambda_dot_step_substitution },
      { simp [hxy₁, hy₁],
        use y₁·z,
        exact ⟨by refl, or.inl rfl⟩ } },
    { rw [hax, hcyz, hza, hxb],
      use x[0:=z],
      split,
      apply substitution_reduction_step_right,
      apply η.shift_head_step_shift,
      apply hay,
      right,
      apply β.lambda_dot_step_substitution, },
    { rw [hax, ← hza, hcyz],
      rcases a_ih_f hxb hay with ⟨m, hxm, hym⟩,
      use m·z,
      split,
      apply η.dot_reduction_dot_left hxm,
      cases hym,
      { simp [hym] },
      right,
      apply β.dot_step_dot_left hym },
    { rw [hax, hcyz, hza],
      use x·z,
      split,
      apply η.dot_reduction_dot_right,
      apply relation.refl_trans_gen.single hay,
      right,
      apply β.dot_step_dot_left hxb },
    { rw [hax, hcyz, hza],
      use y·x,
      split,
      apply η.dot_reduction_dot_left,
      apply relation.refl_trans_gen.single hay,
      right,
      apply β.dot_step_dot_right hxb },
    { rw [hax, ← hza, hcyz],
      rcases a_ih_g hxb hay with ⟨m, hxm, hym⟩,
      use y·m,
      split,
      apply η.dot_reduction_dot_right hxm,
      cases hym,
      { simp [hym] },
      right,
      apply β.dot_step_dot_right hym },
  }
end

theorem βη_diamond_step_reduction {a b c: utlc}: a →β b → a ↠η c →
  ∃ x, b ↠η x ∧ c ↠β x :=
begin
  intros hab hac,
  induction hac using relation.refl_trans_gen.head_induction_on with a f haf hfc ih generalizing b hab,
  exact ⟨b, by refl, relation.refl_trans_gen.single hab ⟩,
  rcases βη_diamond_step hab haf with ⟨g, hbg, hfg⟩,
  cases hfg,
  { refine ⟨ c, trans hbg _, by refl ⟩,
    rw [← hfg],
    exact hfc },
  rcases ih hfg with ⟨x, hgx, hcx⟩,
  refine ⟨x, trans hbg hgx, hcx⟩,
end

theorem βη_diamond_reduction {a b c: utlc}: a ↠β b → a ↠η c →
  ∃ x, b ↠η x ∧ c ↠β x :=
begin
  intros hab hac,
  induction hab using relation.refl_trans_gen.head_induction_on with a f haf hfb ih generalizing c hac,
  exact ⟨c, hac, by refl⟩,
  rcases βη_diamond_step_reduction haf hac with ⟨g, hfg, hcg⟩,
  rcases ih hfg with ⟨x, hbx, hgx⟩,
  refine ⟨x, hbx, trans hcg hgx⟩,
end

theorem β_diamond_reduction {a b c: utlc}: a ↠β b → a ↠βη c →
  ∃ x, b ↠βη x ∧ c ↠β x :=
begin
  intros hab hac,
  induction hac using relation.refl_trans_gen.head_induction_on with a f haf hfc ih generalizing b hab,
  exact ⟨b, by refl, hab⟩,
  rw [step_iff] at haf,
  cases haf,
  { rcases β.church_rosser hab (relation.refl_trans_gen.single haf) with ⟨x, hbx, hfx⟩,
    rcases ih hfx with ⟨y, hxy, hcy⟩,
    refine ⟨y, trans (reduction_of_beta hbx) hxy, hcy⟩ },
  { rcases βη_diamond_reduction hab (relation.refl_trans_gen.single haf) with ⟨x, hbx, hfx⟩,
    rcases ih hfx with ⟨y, hxy, hcy⟩,
    refine ⟨y, trans (reduction_of_eta hbx) hxy, hcy⟩ },
end

theorem η_diamond_reduction {a b c: utlc}: a ↠η b → a ↠βη c →
  ∃ x, b ↠βη x ∧ c ↠η x :=
begin
  intros hab hac,
  induction hac using relation.refl_trans_gen.head_induction_on with a f haf hfc ih generalizing b hab,
  exact ⟨b, by refl, hab⟩,
  rw [step_iff] at haf,
  cases haf,
  { rcases βη_diamond_reduction (relation.refl_trans_gen.single haf) hab with ⟨x, hfx, hbx⟩,
    rcases ih hfx with ⟨y, hxy, hcy⟩,
    refine ⟨y, trans (reduction_of_beta hbx) hxy, hcy⟩ },
  { rcases η.church_rosser hab (relation.refl_trans_gen.single haf) with ⟨x, hbx, hfx⟩,
    rcases ih hfx with ⟨y, hxy, hcy⟩,
    refine ⟨y, trans (reduction_of_eta hbx) hxy, hcy⟩ }
end

theorem church_rosser {a b c : utlc}:
  a ↠βη b → a ↠βη c → b ≡βη c :=
begin
  intros hab hac,
  induction hab using relation.refl_trans_gen.head_induction_on with a f haf hfb ih generalizing c hac,
  { use c,
    exact ⟨ hac, by refl⟩, },
  rw [step_iff] at haf,
  cases haf,
  { rcases β_diamond_reduction (relation.refl_trans_gen.single haf) hac with ⟨x, hfx, hcx⟩,
    rcases ih hfx with ⟨y, hby, hxy⟩,
    refine ⟨y, hby, trans (reduction_of_beta hcx) hxy ⟩ },
  { rcases η_diamond_reduction (relation.refl_trans_gen.single haf) hac with ⟨x, hfx, hcx⟩,
    rcases ih hfx with ⟨y, hby, hxy⟩,
    refine ⟨y, hby, trans (reduction_of_eta hcx) hxy ⟩ }
end


@[refl]
theorem equiv_refl (f : utlc): f ≡βη f :=
  ⟨f, relation.refl_trans_gen.refl, relation.refl_trans_gen.refl⟩

@[symm]
theorem equiv_symm {a b: utlc}: a ≡βη b → b ≡βη a :=
begin
  apply relation.symmetric_join
end

@[trans]
theorem equiv_trans {a b c : utlc}: a ≡βη b → b ≡βη c → a ≡βη c :=
begin
  apply relation.transitive_join,
  apply relation.refl_trans_gen.trans,
  apply @church_rosser,
end

theorem reduced_reduction_inj {f g: utlc}: reduced f → f ↠βη g → f = g :=
begin
  intros hf p,
  induction p with x y hx hy fx,
  { refl },
  rw [←fx] at *,
  exfalso,
  apply reduced_iff_no_reduction.mp hf _ hy
end

theorem reduced_equiv_inj {f g: utlc}: reduced f → reduced g → f ≡βη g → f = g :=
begin
  intros hf hg p,
  cases p with x p,
  rw [reduced_reduction_inj hf p.left, reduced_reduction_inj hg p.right]
end

end βη
end utlc
end lambda_calculus