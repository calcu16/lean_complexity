import lambda_calculus.utlc.basic
import lambda_calculus.utlc.identities

namespace lambda_calculus
namespace utlc

def reduction_step : utlc → utlc → (utlc → utlc → Prop) → Prop
| (↓ n) := λ g r, r (↓ n) g
| (Λ f) := λ g r, r (Λ f) g ∨ match g with
  | (↓ _) := false
  | (Λ g) := reduction_step f g r
  | (_·_) := false
  end
| (f1 · f2) := λ g r, r (f1 · f2) g ∨ match g with
  | (↓_) := false
  | (Λ _) := false
  | (g1 · g2) :=
    (g2 = f2 ∧ (reduction_step f1 g1 r)) ∨ (g1 = f1 ∧ (reduction_step f2 g2 r))
  end

def reduction_step_of := λ r f g, reduction_step f g r

section
variables (head_step: utlc → utlc → Prop)
variables (n : ℕ)
variables (f f' g g': utlc)
variables (m : ℕ)

local attribute [simp] reduction_step reduction_step_of

instance reduction_step.decidable_rel [h: decidable_rel head_step]: decidable_rel (reduction_step_of head_step) :=
begin
  have dor : ∀ (p q : Prop), decidable p → decidable q → decidable (p ∨ q),
  { intros p q hp hq,
    cases hp;
    cases hq;
    simp [hp, hq];
    apply_instance },
  have dand : ∀ (p q : Prop), decidable p → decidable q → decidable (p ∧ q),
  { intros p q hp hq,
    cases hp;
    cases hq;
    simp [hp, hq];
    apply_instance },
  intro f,
  induction f;
  intro g;
  cases g;
  simp;
  repeat { apply dor };
  repeat { apply dand };
  try { apply_instance },
  apply f_ih g,
  apply f_ih_f g_f,
  apply f_ih_g g_g
end

theorem down_reduction_step_iff: reduction_step_of head_step (↓n) g ↔ head_step (↓n) g :=
by cases g; simp

theorem lambda_reduction_step_iff: reduction_step_of head_step (Λ f) g ↔
  head_step (Λ f) g ∨ ∃ x, g = Λ x ∧ reduction_step_of head_step f x :=
by cases g; simp

theorem dot_reduction_step_iff: reduction_step_of head_step (f·f') g ↔
  head_step (f·f') g ∨
    (∃ x, g = x·f' ∧ reduction_step_of head_step f x) ∨
    ∃ x, g = f·x ∧ reduction_step_of head_step f' x :=
by cases g; simp [and.assoc]
end

attribute [irreducible] reduction_step_of
attribute [simp] down_reduction_step_iff lambda_reduction_step_iff dot_reduction_step_iff

variables {head_step: utlc → utlc → Prop}
variables {f f': utlc}
variables {n: ℕ}
variables {g g': utlc}
variables {m: ℕ}

@[simp] theorem reduction_step_down_iff:
  reduction_step_of head_step f ↓m ↔ head_step f ↓m :=
by cases f; simp

theorem down_of_refl_trans_reduction_step:
  (∀ n g, ¬ head_step (↓n:utlc) g) →
  relation.refl_trans_gen (reduction_step_of head_step) (↓n:utlc) g →
  g = ↓n :=
begin
  intros h p,
  induction p with x g hfx hxg,
  { refl },
  rw [p_ih, down_reduction_step_iff] at hxg,
  exfalso,
  apply h _ _ hxg,
end

theorem reduction_step_lambda_iff:
  reduction_step_of head_step f Λ g ↔
  head_step f (Λ g) ∨ ∃ x, f = Λ x ∧ reduction_step_of head_step x g :=
by cases f ; simp

theorem reduction_step_dot_iff:
  reduction_step_of head_step f (g·g') ↔
  head_step f (g·g') ∨
    (∃ x, x·g' = f ∧ reduction_step_of head_step x g) ∨
    ∃ x, g·x = f ∧ reduction_step_of head_step x g' :=
by cases f; simp [and.assoc]

theorem lambda_reduction_step_lambda:
  reduction_step_of head_step f g → reduction_step_of head_step (Λ f) (Λ g) :=
by simp; exact or.inr

theorem lambda_refl_reduction_step_lambda:
  relation.refl_gen (reduction_step_of head_step) f g →
  relation.refl_gen (reduction_step_of head_step) Λ f Λ g :=
begin
  intro p,
  cases p,
  { refl },
  exact relation.refl_gen.single (lambda_reduction_step_lambda (by assumption)),
end

theorem lambda_refl_trans_reduction_step_lambda:
  relation.refl_trans_gen (reduction_step_of head_step) f g →
  relation.refl_trans_gen (reduction_step_of head_step) Λ f Λ g :=
relation.refl_trans_gen.lift _ (@lambda_reduction_step_lambda _)

theorem lambda_of_refl_trans_reduction_step:
  (∀ f g, ¬ head_step (Λ f) g) →
  relation.refl_trans_gen (reduction_step_of head_step) (Λ f) g →
  ∃ x, g = Λ x :=
begin
  intros h p,
  induction p with x g hfx hxg,
  { use f },
  cases p_ih with y hy,
  rw [hy, lambda_reduction_step_iff] at hxg,
  cases hxg,
  { exfalso, apply h _ _ hxg },
  rcases hxg with ⟨z, _, _⟩,
  use z,
  assumption,
end

theorem dot_reduction_step_dot_left:
  reduction_step_of head_step f f' → reduction_step_of head_step (f·g) (f'·g) :=
by intro p; simp [p]

theorem dot_reduction_step_dot_right:
  reduction_step_of head_step g g' → reduction_step_of head_step (f·g) (f·g') :=
by intro p; simp [p]

theorem dot_refl_reduction_step_dot_left:
  relation.refl_gen (reduction_step_of head_step) f f' →
  ∀ g, relation.refl_gen (reduction_step_of head_step) (f·g) (f'·g) :=
begin
  intros p _,
  cases p,
  { refl },
  exact relation.refl_gen.single (dot_reduction_step_dot_left (by assumption))
end

theorem dot_refl_reduction_step_dot_right:
  relation.refl_gen (reduction_step_of head_step) f f' →
  ∀ g, relation.refl_gen (reduction_step_of head_step) (g·f) (g·f') :=
begin
  intros p _,
  cases p,
  { refl },
  exact relation.refl_gen.single (dot_reduction_step_dot_right (by assumption))
end

theorem dot_refl_trans_reduction_step_dot_left:
  relation.refl_trans_gen (reduction_step_of head_step) f f' →
  ∀ g, relation.refl_trans_gen (reduction_step_of head_step) (f·g) (f'·g) :=
begin
  intros _ g,
  simp only [show ∀ f, f·g = (λ x, x·g) f, by simp],
  apply relation.refl_trans_gen.lift,
  intros _ _ _,
  apply dot_reduction_step_dot_left,
  assumption'
end

theorem dot_refl_trans_reduction_step_dot_right:
  relation.refl_trans_gen (reduction_step_of head_step) f f' →
  ∀ g, relation.refl_trans_gen (reduction_step_of head_step) (g·f) (g·f') :=
begin
  intros _ g,
  simp only [show ∀ f, g·f = (λ x, g·x) f, by simp],
  apply relation.refl_trans_gen.lift,
  intros _ _ _,
  apply dot_reduction_step_dot_right,
  assumption'
end

theorem dot_refl_trans_reduction_step_dot:
  relation.refl_trans_gen (reduction_step_of head_step) f f' →
  relation.refl_trans_gen (reduction_step_of head_step) g g' →
  relation.refl_trans_gen (reduction_step_of head_step) (f·g) (f'·g') :=
begin
  intros p q,
  apply trans,
  exact dot_refl_trans_reduction_step_dot_left p _,
  exact dot_refl_trans_reduction_step_dot_right q _
end

theorem  dot_of_refl_trans_reduction_step:
  (∀ f f' g, ¬ head_step (f·f') g) →
  relation.refl_trans_gen (reduction_step_of head_step) (f·f') g →
  ∃ x x', g = x·x' :=
begin
  intros h p,
  induction p with x g hfx hxg,
  { exact ⟨f, f', rfl⟩ },
  rcases p_ih with ⟨y, y', hy⟩,
  rw [hy, dot_reduction_step_iff] at hxg,
  obtain hxg|hxg|hxg := hxg;
  try { exfalso, apply h _ _ _ hxg };
  rcases hxg with ⟨z, hg, _⟩,
  exact ⟨z, y', hg⟩,
  exact ⟨y, z, hg⟩
end

theorem uses_zero_reduction_step  (h: ∀ {f g}, head_step f g → ∀ {n}, f.uses n = 0 → g.uses n = 0):
  (reduction_step_of head_step f g) → ∀ {n}, f.uses n = 0 → g.uses n = 0 :=
begin
  induction f generalizing g;
  simp only [down_notation, lambda_notation, dot_notation];
  intro p;
  try { rw [down_reduction_step_iff] at p };
  try { rw [lambda_reduction_step_iff] at p, obtain p|p := p };
  try { rw [dot_reduction_step_iff] at p, obtain p|p|p := p };
  try { { apply @h _ _ p } };
  rcases p with ⟨x, hg, hf⟩;
  simp [hg];
  intro n,
  { apply f_ih hf },
  { intros p q, exact ⟨ f_ih_f hf p, q ⟩ },
  { intros p q, exact ⟨ p, f_ih_g hf q ⟩ }
end

theorem uses_reduction_step_uses (h: ∀ {f} {g}, head_step f g → ∀ n, f.uses n = g.uses n):
  (reduction_step_of head_step f g) → ∀ n, f.uses n = g.uses n :=
begin
  induction f generalizing g;
  simp only [down_notation, lambda_notation, dot_notation];
  intro p;
  try { rw [down_reduction_step_iff] at p };
  try { rw [lambda_reduction_step_iff] at p, obtain p|p := p };
  try { rw [dot_reduction_step_iff] at p, obtain p|p|p := p };
  try { { apply h p } };
  rcases p with ⟨x, hg, hf⟩;
  simp [hg],
  { intro n, apply f_ih hf },
  { apply f_ih_f hf },
  { apply f_ih_g hf }
end

theorem uses_refl_trans_reduction_step_uses (h: ∀ {f g}, head_step f g → ∀ n, f.uses n = g.uses n):
  (relation.refl_trans_gen (reduction_step_of head_step) f g) → ∀ n, f.uses n = g.uses n :=
begin
  intro p,
  induction p with x g hfx hxg,
  { intro, refl },
  intro n,
  apply trans (p_ih _),
  apply uses_reduction_step_uses @h hxg,
end

theorem shift_reduction_step_shift_iff: (∀ f g n, head_step (f ↑¹ n) (g ↑¹ n) ↔ head_step f g) → 
  (reduction_step_of head_step (f ↑¹ n) (g ↑¹ n) ↔ reduction_step_of head_step f g) :=
begin
  intro p,
  induction f generalizing n g;
  simp;
  conv_rhs { rw [← p _ _ n] };
  simp,
  { apply or_congr,
    { refl },
    split;
    intro p,
    { cases p with x p,
      cases @shift_of_uses x (n+1) (by rw [← lambda_uses, ←p.left]; simp [shift_uses]) with y q,
      use y,
      rw [q] at p,
      rw [← shift_inj_iff n, ← @f_ih (n + 1)],
      simp [p] },
    { cases p with x p,
      use x ↑¹ (n + 1),
      simp [p, f_ih] } },
  { apply or_congr,
    refl,
    apply or_congr;
    split;
    intro p;
    cases p with x p;
    try { { use x ↑¹ n, simp [p, f_ih_f, f_ih_g] } },
    { cases @shift_of_uses x n begin
        conv_lhs { rw [← add_zero (x.uses n), ← shift_uses_zero' f_g n, ← dot_uses, ←p.left] };
        apply shift_uses_zero'
      end with y q,
      use y,
      rw [← shift_inj_iff n, ← @f_ih_f n],
      simp [← q, p] },
    { cases @shift_of_uses x n begin
        conv_lhs { rw [← zero_add (x.uses n), ← shift_uses_zero' f_f n, ← dot_uses, ←p.left] };
        apply shift_uses_zero'
      end with y q,
      use y,
      rw [← shift_inj_iff n, ← @f_ih_g n],
      simp [← q, p] } },
end

theorem shift_refl_trans_reduction_shift: (∀ f g n, head_step (f ↑¹ n) (g ↑¹ n) ↔ head_step f g) → 
  (relation.refl_trans_gen (reduction_step_of head_step) f g → relation.refl_trans_gen (reduction_step_of head_step) (f ↑¹ n) (g ↑¹ n)) :=
begin
 intro p,
 apply relation.refl_trans_gen.lift,
 intros a b,
 apply (shift_reduction_step_shift_iff p).mpr
end

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

theorem substitution_reduction_step_left (f: utlc) (hf: ∀ {f f'}, head_step f f' → ∀ n g, relation.refl_trans_gen (reduction_step_of head_step) (f[n:=g]) (f'[n:=g])): reduction_step_of head_step f f' →
  ∀ n g, relation.refl_trans_gen (reduction_step_of head_step) (f[n:=g]) (f'[n:=g]) :=
begin
  induction f generalizing f';
  simp;
  intros p n g,
  { apply hf p },
  { cases p,
    { apply hf p },
    rcases p with ⟨x, hfx', hfx⟩,
    rw [hfx'],
    exact lambda_refl_trans_reduction_step_lambda (f_ih hfx _ _) },
  { obtain p|p|p := p,
    { apply hf p },
    { rcases p with ⟨x, hfx', hfx⟩,
      rw [hfx'],
      exact dot_refl_trans_reduction_step_dot_left (f_ih_f hfx _ _) _ },
    { rcases p with ⟨x, hfx', hfx⟩,
      rw [hfx'],
      exact dot_refl_trans_reduction_step_dot_right (f_ih_g hfx _ _) _ } }
end

theorem substitution_reduction_step_right (f: utlc) (hf: ∀ f g n, head_step (f ↑¹ n) (g ↑¹ n) ↔ head_step f g): reduction_step_of head_step g g' →
  ∀ n, relation.refl_trans_gen (reduction_step_of head_step) (f[n:=g]) (f[n:=g']) :=
begin
  induction f generalizing g g';
  simp;
  intros p n,
  { split_ifs,
    refl,
    apply relation.refl_trans_gen.single,
    apply p,
    refl },
  { apply lambda_refl_trans_reduction_step_lambda,
    apply f_ih,
    rw shift_reduction_step_shift_iff,
    assumption,
    assumption },
  { apply dot_refl_trans_reduction_step_dot,
    apply f_ih_f,
    assumption,
    apply f_ih_g,
    assumption }
end

def reduced : utlc → (utlc → bool) → bool
| (↓ n) := λ p, p (↓ n)
| (Λ f) := λ p, p (Λ f) ∧ reduced f p
| (f · g) := λ p, p (f · g) ∧ reduced f p ∧ reduced g p

def reduced_of : (utlc → bool) → utlc → bool := λ h f, reduced f h

section
local attribute [simp] reduced reduced_of
variables (head_pred: utlc → bool)

theorem down_reduced: reduced_of head_pred ↓n ↔ head_pred ↓n :=
by simp

theorem lambda_reduced: reduced_of head_pred Λ f ↔ head_pred Λ f ∧ reduced_of head_pred f :=
by simp

theorem dot_reduced: reduced_of head_pred (f·g) ↔ head_pred (f·g) ∧ reduced_of head_pred f ∧ reduced_of head_pred g :=
by simp
end
attribute [irreducible] reduced_of
attribute [simp] down_reduced lambda_reduced dot_reduced

variables {head_pred: utlc → bool}

theorem head_reduced_of_reduced: reduced_of head_pred f → head_pred f :=
by { cases f; simp; repeat {intro }; assumption}

theorem reduced_iff_not_reduction_step: (∀ f, head_pred f ↔ ∀ g, ¬ head_step f g) → (∀ f, reduced_of head_pred f ↔ ∀ g, ¬ reduction_step_of head_step f g) :=
begin
  intros p f,
  induction f;
  simp [p];
  try { simp [f_ih] };
  try { simp [f_ih_f, f_ih_g] };
  split;
  try { { intros q g, simp [q] } };
  intro q;
  split;
  try { split };
  intros g s;
  try {
  { apply q g, simp [s] } },
  { apply q (Λ g), simp [s] },
  { apply q (g·f_g), simp [s] },
  { apply q (f_f·g), simp [s] }
end

end utlc
end lambda_calculus