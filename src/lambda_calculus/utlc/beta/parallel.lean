import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.beta.basic
import logic.relation

namespace lambda_calculus
namespace utlc
namespace β
namespace parallel

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

section
def step : utlc → utlc → Prop
| (↓n) := λ x, x = (↓n)
| (Λ f) := λ x, ∃ g, step f g ∧ x = Λ g 
| (f·f') := λ x,
  (∃ g g', step f g ∧ step f' g' ∧ x = g·g') ∨
  ∃ g g', step f (Λ g) ∧  step f' g' ∧ x = g[0:=g']

instance : has_parallel_reduction utlc := ⟨ step ⟩

@[simp] theorem down_step_down_iff {n m: ℕ}: (↓n:utlc) →∥ ↓m ↔ n = m :=
by simp [has_parallel_reduction.step, step, eq_comm]

@[simp] theorem not_down_step_lambda (n: ℕ) (f: utlc): ¬ (↓n:utlc) →∥ Λ f :=
by simp [has_parallel_reduction.step, step]

@[simp] theorem not_down_step_dot (n: ℕ) (f g: utlc): ¬ (↓n:utlc) →∥ f·g :=
by simp [has_parallel_reduction.step, step]

@[simp] theorem lambda_step_lambda_iff {f g: utlc}: (Λ f) →∥ (Λ g) ↔ f →∥ g :=
by simp [has_parallel_reduction.step, step]

@[simp] theorem not_lambda_step_down (f: utlc) (n: ℕ): ¬ Λ f →∥ ↓n :=
by simp [has_parallel_reduction.step, step]

@[simp] theorem not_lambda_step_dot (f g g': utlc): ¬ Λ f →∥ g·g' :=
by simp [has_parallel_reduction.step, step]

theorem dot_step_dot {f f' g g': utlc}: f →∥ f' → g →∥ g' → (f·g) →∥ (f'·g') :=
begin
  simp only [has_parallel_reduction.step, step],
  exact λ p q, or.inl ⟨f', g', p, q, rfl⟩,
end

theorem dot_step_substitution {f f' g g': utlc} (x: utlc): f →∥ f' → g →∥ g' → f' = Λ x → f·g →∥ x[0:=g'] :=
begin
  simp only [has_parallel_reduction.step, step],
  intros p q fx,
  rw [fx] at p,
  refine or.inr ⟨x, g', p, q, rfl⟩
end

theorem dot_step_substitution' {f f' g g' y: utlc} (x: utlc): f →∥ f' → g →∥ g' → f' = Λ x → y = x[0:=g'] → f·g →∥ y :=
begin
  simp only [has_parallel_reduction.step, step],
  intros p q fx fy,
  rw [fx] at p,
  rw [fy],
  refine or.inr ⟨x, g', p, q, rfl⟩
end

theorem lambda_dot_step_substitution {f f' g g': utlc}: f →∥ f' → g →∥ g' → (Λ f)·g →∥ f'[0:=g'] :=
begin
  simp only [has_parallel_reduction.step, step],
  intros p q,
  exact or.inr ⟨f', g', ⟨f', p, rfl⟩, q, rfl⟩,
end

theorem dot_step_iff {f f' g: utlc}: f·f' →∥ g ↔
  (∃ x y, f →∥ x ∧ f' →∥ y ∧ g = x·y ) ∨ (∃ x y,  f →∥ (Λ x) ∧ f' →∥ y ∧ g = x[0:=y]) :=
by  simp [has_parallel_reduction.step, step]

@[simp]
theorem step_notation {f g: utlc}: step f g ↔ f →∥ g := by refl
end -- shouldn't need to use has_parallel_reduction.step below here

@[simp] theorem down_step_down {n m: ℕ}: n = m → (↓n:utlc) →∥ ↓m :=
by simp

theorem lambda_step_lambda {f g: utlc}: f →∥ g → (Λ f) →∥ (Λ g) :=
by simp

theorem dot_step_cases {f f' g: utlc}: f·f' →∥ g →
  (∃ x y, f →∥ x ∧ f' →∥ y ∧ g = x·y ) ∨ (∃ x y,  f →∥ (Λ x) ∧ f' →∥ y ∧ g = x[0:=y]) :=
  dot_step_iff.mp

@[refl]
theorem step_refl (f : utlc): f →∥ f :=
begin
  induction f using lambda_calculus.utlc.notation_induction_on,
  { exact down_step_down rfl },
  { exact lambda_step_lambda f_ih },
  { exact dot_step_dot f_ih_f f_ih_g }
end

@[simp] theorem down_step_iff {n: ℕ} {g: utlc}: (↓n:utlc) →∥ g ↔ ↓n = g :=
by cases g; simp

@[simp] theorem down_dot_step (n: ℕ) {f g: utlc}: (↓n·f) →∥ g ↔
  (∃ x, f →∥ x ∧ g = ↓n·x ) :=
by simp [dot_step_iff]

theorem dot_dot_step {a b c g: utlc}: (a·b·c) →∥ g →
  (∃ x y, (a·b) →∥ x ∧ c →∥ y ∧ x·y →∥ g ) :=
begin
  intro h,
  have h := dot_step_cases h,
  cases h with h h,
  { rcases h with ⟨x, y, habx, hcy, hgxy⟩,
    refine ⟨x, y, habx, hcy, _⟩,
    rw [hgxy] },
  rcases h with ⟨x, y, habx, hcy, hgxy⟩,
  refine ⟨Λ x, y, habx, hcy, _⟩,
  rw [hgxy],
  apply lambda_dot_step_substitution (step_refl _) (step_refl _),
end

theorem dot_dot_step' {a b c g: utlc}: (a·b·c) →∥ g →
  (∃ x, (a·b) →∥ x ∧ x·c →∥ g ) :=
begin
  intro h,
  have h := dot_step_cases h,
  cases h with h h,
  { rcases h with ⟨x, y, habx, hcy, hgxy⟩,
    rw [hgxy],
    refine ⟨x, habx, dot_step_dot (step_refl _) hcy⟩ },
  rcases h with ⟨x, y, habx, hcy, hgxy⟩,
  rw [hgxy],
  refine ⟨ Λ x, habx, lambda_dot_step_substitution (step_refl _) hcy⟩,
end

theorem shift_step_shift {f g: utlc} (n: ℕ): f →∥ g → f ↑¹ n →∥ g ↑¹ n :=
begin
  induction f using lambda_calculus.utlc.notation_induction_on generalizing g n,
  { cases g; simp [down_shift] },
  { cases g,
    { simp },
    { simpa using f_ih (n+1) },
    { simp } },
  { rw [dot_step_iff, dot_shift],
    intro h,
    cases h;
    rcases h with ⟨x, y, hf, hg, h⟩; rw [h],
    { rw [dot_shift x],
      apply dot_step_dot (f_ih_f _ hf) (f_ih_g _ hg) },
    { rw [← substitution_shift_zero],
      apply dot_step_substitution _ (f_ih_f _ hf) (f_ih_g _ hg),
      simp }
  }
end

theorem substitution_step_substitution_succ {f f' g g': utlc} {n : ℕ}: f →∥ f' → g →∥ g' → g'.uses 0 = 0 → f[n+1:=g] →∥ f'[n+1:=g'] :=
begin
  induction f generalizing f' g g' n,
  { intros hf hg _,
    simp at hf,
    rw [← hf],
    simp,
    split_ifs,
    any_goals { refl },
    assumption },
  { simp,
    cases f',
    all_goals { simp },
    intros hf hg ug',
    apply f_ih hf (shift_step_shift _ hg) (shift_uses_self _ _) },
  simp,
  intros hf hg ug',
  cases dot_step_cases hf with h h,
  all_goals { rcases h with ⟨x, y, hfx, hfy, hfxy⟩,  rw [hfxy] },
  any_goals {
    rw [dot_substitution],
    apply dot_step_dot },
  any_goals {
    rw [substitution_dist_lt (nat.zero_lt_succ _)],
    apply dot_step_substitution },
  any_goals { apply f_ih_f },
  any_goals { apply f_ih_g },
  any_goals { apply hfx },
  any_goals { apply hfy },
  any_goals { apply hg },
  any_goals { apply ug' },
  simp,
end

theorem substitution_step_substitution {f f' g g': utlc}: f →∥ f' → g →∥ g' → f[0:=g] →∥ f'[0:=g'] :=
begin
  induction f generalizing f' g g',
  all_goals { simp },
  { intro hf,
    simp [← hf],
    split_ifs,
    all_goals { simp } },
  { cases f',
    all_goals { simp },
    intros hf hg,
    exact substitution_step_substitution_succ hf (shift_step_shift _ hg) (shift_uses_self _ _) },
  intros hf hg,
  cases dot_step_cases hf with h h,
  all_goals { rcases h with ⟨x, y, hfx, hfy, hfxy⟩,  rw [hfxy] },
  rw [dot_substitution],
  apply dot_step_dot,
  any_goals {
    rw [substitution_dist_eq],
    apply dot_step_substitution },
  any_goals { apply f_ih_f hfx hg },
  any_goals { apply f_ih_g hfy hg },
  simp,
end

theorem step_church_rosser {a b c :utlc}: a →∥ b → a →∥ c → ∃ d, b →∥ d ∧ c →∥ d :=
begin
  induction a generalizing b c,
  all_goals { simp },
  { intros hab hac,
    use ↓a,
    rw [←hab, ←hac],
    exact ⟨by refl, by refl⟩},
  { cases b,
    all_goals { simp },
    cases c,
    all_goals { simp },
    intros hab hac,
    cases a_ih hab hac with d ih,
    use Λ d,
    simp [ih] },
  { intros hab hac,
    cases dot_step_cases hab with hab hab,
    all_goals { cases dot_step_cases hac with hac hac },
    all_goals { rcases hab with ⟨f, g, haf, hag, hbfg⟩ },
    all_goals { rcases hac with ⟨m, n, ham, han, hcmn⟩ },
    all_goals {
      rcases a_ih_f haf ham with ⟨x, hfx, hmx⟩,
      rcases a_ih_g hag han with ⟨y, hgy, hny⟩ },
    all_goals { rw [hbfg, hcmn] },
    { use x·y,
      refine ⟨dot_step_dot hfx hgy, dot_step_dot hmx hny⟩ },
    all_goals {
      cases x,
      all_goals { simp at hfx hmx },
      any_goals { contradiction },
      use x[0:=y] },
    { refine ⟨dot_step_substitution _ hfx hgy rfl, substitution_step_substitution hmx hny⟩ },
    { refine ⟨substitution_step_substitution hfx hgy, dot_step_substitution _ hmx hny rfl⟩ },
    { refine ⟨substitution_step_substitution hfx hgy, substitution_step_substitution hmx hny⟩ } }
end

theorem church_rosser {a b c : utlc} (hab : a ↠∥ b) (hac : a ↠∥ c)
  : b ≡∥ c :=
begin
  refine relation.church_rosser _ hab hac,
  intros x y z xy xz,
  rcases step_church_rosser xy xz with ⟨d, yd, zd⟩,
  exact ⟨d, relation.refl_gen.single yd, relation.refl_trans_gen.single zd⟩
end
end parallel

end β
end utlc
end lambda_calculus
