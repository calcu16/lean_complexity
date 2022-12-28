import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.beta
import lambda_calculus.utlc.beta_trans

namespace utlc

@[simp] def β_step : utlc → list bool → utlc
| (↓n) := λ path, ↓n
| (Λ f) := λ path, Λ f.β_step path
| (f·g) := λ path, match path with
  | [] := match f with
    | (↓_) := f·g.β_step []
    | (Λ f) := substitution f 0 g
    | (_·_) := if f.β_reduced then f·g.β_step [] else f.β_step []·g
    end
  | (bool.ff :: path') := f.β_step path'·g
  | (bool.tt :: path') := f·g.β_step path'
  end

def β_normal_step : utlc → utlc := λ f, β_step f []

theorem β_step_eq_or_reducible (f: utlc): ∀ path, f.β_step path = f ∨  f.β_reducible_step (f.β_step path) :=
begin
  induction f with _ _ fh f g fh gh,
  all_goals { intro path, simp [reducible_step] at * },
  { apply fh },
  { all_goals { cases path with b path },
    cases f with _ _ f f',
    { simp,
      cases gh [],
      { left, assumption },
      cases g,
      all_goals{
        simp only [reducible_step],
        right,
        right,
        refine ⟨rfl, _⟩,
        apply h } },
    { simp },
    { simp,
      split_ifs,
      cases gh [] with gh gh,
      { simp [gh] },
      swap,
      cases fh [] with fh fh,
      { simp at fh, simp [reducible_step, ← fh] },
      all_goals { cases g },
      repeat {
        right,
        right,
        refine ⟨rfl, _⟩,
        apply gh },
      repeat {
        right,
        left,
        refine ⟨_, rfl⟩,
        apply fh }
    },
    cases b,
    cases fh path with fh fh,
    { simp [fh] },
    { cases g,
      all_goals { simp [reducible_step, fh] }
    },
    cases gh path with gh gh,
    simp [gh],
    cases g,
    all_goals {
      simp [reducible_step] at gh,
      simp [reducible_step, gh] }
  }
end

theorem β_trans_of_β_step (f : utlc) (path: list bool) : f ↠ᵦ f.β_step path :=
begin
  cases β_step_eq_or_reducible f path,
  rw [h],
  exact relation.refl_trans_gen.single h
end

theorem β_equiv_of_β_step (path: list bool) (f : utlc): f.β_step path ≈ᵦ f :=
begin
  use f.β_step path,
  exact ⟨by refl, β_trans_of_β_step f path⟩
end

theorem β_equiv_of_β_step' (path: list bool) (f : utlc): f ≈ᵦ f.β_step path :=
begin
  use f.β_step path,
  exact ⟨β_trans_of_β_step f path, by refl⟩
end

theorem β_normal_step_eq_or_reducible (f: utlc): β_normal_step f = f ∨ f.β_reducible_step f.β_normal_step :=
  β_step_eq_or_reducible f []

def β_normal_iteration : ℕ → utlc → utlc
| 0 := λ f, f
| (n+1) := λ f, (β_normal_iteration n (β_normal_step f))

theorem β_trans_of_β_normal_iteration {f : utlc} (n : ℕ) : f ↠ᵦ β_normal_iteration n f :=
begin
  induction n with n hn generalizing f,
  all_goals { simp [β_normal_iteration] },
  cases f.β_normal_step_eq_or_reducible,
  { rw [h], apply hn },
  exact relation.refl_trans_gen.head h hn,
end

theorem β_equiv_of_β_normal_iteration {f g : utlc} (n : ℕ) : β_normal_iteration n f ≈ᵦ g → f ≈ᵦ g :=
begin
  intros q,
  cases q with c q,
  use c,
  refine ⟨_, q.right⟩,
  apply trans _ q.left,
  apply β_trans_of_β_normal_iteration
end

theorem β_equiv_of_β_normal_iteration' {f g: utlc} (n : ℕ) : f ≈ᵦ β_normal_iteration n g → f ≈ᵦ g :=
begin
  intros _,
  apply relation.symmetric_join,
  apply β_equiv_of_β_normal_iteration,
  apply relation.symmetric_join,
  assumption
end

def β_normal_form (f g : utlc) := β_reduced g ∧ ∃ n, β_normal_iteration n f = g

def mk_β_normal_form (f : utlc) (x : ℕ) (pf: β_reduced (β_normal_iteration x f)) := β_normal_iteration x f
end utlc