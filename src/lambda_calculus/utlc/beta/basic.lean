import lambda_calculus.utlc.basic
import lambda_calculus.utlc.identities
import lambda_calculus.utlc.reduction

namespace lambda_calculus
namespace utlc
namespace β

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

variables {f g f' g' x y z: utlc}

def head_step : utlc → utlc → Prop
| (↓ _) := λ g, false
| (Λ _) := λ g, false
| (f1 · f2) := match f1 with
  | (↓ _) := λ g, false
  | (Λ f1) := λ g, substitution f1 0 f2 = g
  | (_ · _) := λ g, false
  end

section
local attribute [simp] head_step

instance head_step.decidable_rel : decidable_rel head_step :=
begin
  intros f _,
  cases f;
  try { cases f_f };
  { simp, apply_instance }
end

theorem head_step_exists (f g: utlc): head_step f g ↔
  ∃ x y, f = (Λ x)·y ∧ x[0:=y] = g :=
by cases f; try { cases f_f }; simp [and.assoc]
end
attribute [simp] head_step_exists
attribute [irreducible] head_step

instance : has_β_reduction utlc := ⟨ reduction_step_of head_step ⟩

section
@[simp] theorem not_index_step (n: ℕ) (g: utlc): ¬ ↓n →β g := by simp [has_β_reduction.step]

theorem lambda_step_iff (f g: utlc): Λ f →β g ↔ ∃ x, g = Λ x ∧ f →β x := by simp [has_β_reduction.step]

theorem dot_step_iff (f f' g: utlc): f·f' →β g ↔
  (∃ x, f = Λ x ∧ x[0:=f'] = g) ∨
  (∃ x, g = x·f' ∧ f →β x) ∨
  (∃ x, g = f·x ∧ f' →β x) := by simp [and.assoc, has_β_reduction.step]
end

theorem lambda_step_exists {f g: utlc}: Λ f →β g → ∃ x, g = Λ x ∧ f →β x := (lambda_step_iff _ _).mp

theorem lambda_step_lambda {f g: utlc}: f →β g → Λ f →β Λ g :=
by rw [lambda_step_iff]; intro p; exact ⟨g, rfl, p⟩

@[simp] theorem lambda_step_lambda_iff {f g: utlc}: Λ f →β Λ g ↔ f →β g :=
by simp [lambda_step_iff]

@[simp] theorem step_index_iff (n: ℕ):
  f →β ↓n ↔ f = (Λ ↓0)·↓n ∨ ∃ g, f = (Λ ↓(n+1))·g :=
begin
  cases f;
  try { cases f_f };
  try { cases f_f };
  try { cases f_f };
  simp [and.assoc, lambda_step_iff, dot_step_iff, show 0 ≠ n + 1, by linarith, nat.succ_eq_add_one],
end

theorem dot_step_dot_left: f →β f' → ∀ g, f·g →β f'·g :=
by intro p; simp [dot_step_iff]; exact λ _, or.inr (or.inl p)

theorem dot_step_dot_right: g →β g' → ∀ f, f·g →β f·g' :=
by intro p; simp [dot_step_iff]; exact λ _, or.inr (or.inr p)

theorem dot_step_cases: f·f' →β g →
  (∃ x, f = Λ x ∧ x[0:=f'] = g) ∨
  (∃ x, g = x·f' ∧ f →β x) ∨
  (∃ x, g = f·x ∧ f' →β x) := (dot_step_iff f f' g).mp


theorem lambda_dot_step_substitution (f g: utlc):  (Λ f)·g →β f[0:=g] :=
by simp [dot_step_iff]

theorem down_dot_step_dot {n: ℕ}:
  (↓n·x) →β (↓n·g) ↔ (x →β g) :=
by simp [dot_step_iff]

@[simp] theorem down_dot_step_dot' {n: ℕ}:
  (↓n·x) →β (f·g) ↔ (f = ↓n) ∧ (x →β g) :=
by simp [dot_step_iff, and.assoc]

theorem dot_dot_step_dot:
  (x·y·z) →β (f·g) → (x·y →β f ∧ z = g ∨ x·y = f ∧ z →β g) :=
begin
  intro h,
  obtain h|h|h := dot_step_cases h;
  try { { simp at h, contradiction } };
  rcases h with ⟨w, hw, h⟩;
  simp at hw;
  rw [hw.left, hw.right],
  exact or.inl ⟨h, rfl⟩,
  exact or.inr ⟨rfl, h⟩
end

theorem lambda_reduction_lambda:
  f ↠β g → (Λ f) ↠β (Λ g) := lambda_refl_trans_reduction_step_lambda

theorem dot_reduction_dot:
  f ↠β g → f' ↠β g' → (f·f') ↠β (g·g') := dot_refl_trans_reduction_step_dot

theorem dot_reduction_dot_left:
  f ↠β g → (f·f') ↠β (g·f') :=
by intros p; apply dot_reduction_dot p; refl 

theorem dot_reduction_dot_right:
  f' ↠β g' → (f·f') ↠β (f·g') :=
by apply dot_reduction_dot; refl

theorem dot_reduction_substitution:
  f ↠β (Λ g) → f' ↠β g' → (f·f') ↠β g[0:=g'] :=
begin
  intros _ _,
  apply @trans _ _  _ _ (f·g'),
  apply dot_reduction_dot,
  refl,
  assumption,
  apply @trans _ _ _ _ ((Λ g)·g'),
  apply dot_reduction_dot,
  assumption,
  refl,
  apply relation.refl_trans_gen.single,
  simp [dot_step_iff],
  repeat { apply_instance }
end

theorem uses_zero_head_step: head_step f g → ∀ {n}, f.uses n = 0 → g.uses n = 0 :=
begin
  cases f;
  simp,
  intros x p q n hfx hxg,
  simp [hxg, hfx, ← p, ← q, 
    substitution_uses_zero (nat.zero_le n),
    ← lambda_uses],
end

theorem uses_zero_step: f →β g → ∀ {n}, f.uses n = 0 → g.uses n = 0 := uses_zero_reduction_step @uses_zero_head_step

theorem shift_head_step_shift {n: ℕ}: head_step (f ↑¹ n) (g ↑¹ n) ↔ head_step f g :=
begin
  cases f;
  cases g;
  try { { simp } };
  cases f_f;
  simp [and.assoc];
  simp only [← down_shift, ← lambda_shift, ← dot_shift, ← substitution_shift_zero];
  rw [shift_inj_iff],
end

theorem shift_head_step_shift' {n: ℕ}: head_step f g ↔ head_step (f ↑¹ n) (g ↑¹ n)  :=
by rw [shift_head_step_shift]


theorem shift_step_shift: f →β g → ∀ n, (f ↑¹ n) →β (g ↑¹ n) :=
begin
  simp [has_β_reduction.step],
  intros p n,
  rw [shift_reduction_step_shift_iff],
  apply p,
  apply shift_head_step_shift,
end

theorem shift_reduction_shift: f ↠β g → ∀ n, (f ↑¹ n) ↠β (g ↑¹ n) :=
begin
  simp [has_β_reduction.step],
  intros p n,
  apply shift_refl_trans_reduction_shift (@shift_head_step_shift) p
end

@[simp] def head_reduced : utlc → bool
| (↓ _) := true
| (Λ _) := true
| (f·g) := match f with
  | (↓ _) := true
  | (Λ _) := false
  | (f·g) := true
  end

@[simp] def reduced := λ f, lambda_calculus.utlc.reduced_of head_reduced f

theorem not_head_step_iff_head_reduced: head_reduced f ↔ ∀ g, ¬ head_step f g :=
by cases f; try { cases f_f }; simp

@[simp] theorem lambda_reduced_iff:
  reduced (Λ f) ↔ reduced f := by simp [lambda_reduced]

theorem lambda_of_reduced_and_closed: reduced f → f.closed → ∃ g, f = Λ g :=
begin
  induction f with _ f _ f g fh,
  { simp [closed, closed_below] },
  { intros _ _, use f, refl },
  simp [closed_below],
  cases f with _ _ f f',
  any_goals { { simp [closed_below] } },
  intros _ p _ q _,
  specialize fh p q,
  simp at fh,
  contradiction
end

def reduced_of_not_reduction (f: utlc): reduced f ↔ ∀ g, ¬ f →β g :=
  reduced_iff_not_reduction_step @not_head_step_iff_head_reduced _

-- inductive hypothesis useful when dealing with β reductions
-- splits f·g up to handle the (Λ f)·g ⇔ f[0:=g] case
theorem β_induction_on (p: utlc → Prop): Π (f: utlc)
  (down: Π n, p ↓n)
  (lambda: Π x (hx: p x), p (Λ x))
  (dot : Π x y (hx: p x) (hnx: ¬ ∃ x', Λ x' = x) (hy: p y), p (x·y))
  (lambda_dot: Π x y (hx: p (Λ x)) (hx': p x) (hy: p y), p ((Λ x)·y)),
  (p f)
| (↓n) := λ hn hx hdx hlx, hn n
| (Λ x) := λ hn hx hdx hlx, hx x (β_induction_on x hn hx hdx hlx)
| (↓n·y) := λ hn hx hdx hlx, hdx (↓n) y (hn n) (by simp) (β_induction_on y hn hx hdx hlx)
| ((Λ x)·y) := λ hn hx hdx hlx, hlx x y (β_induction_on (Λ x) hn hx hdx hlx) (β_induction_on x hn hx hdx hlx) (β_induction_on y hn hx hdx hlx)
| (x·x'·y) := λ hn hx hdx hlx, hdx (x·x') y (β_induction_on (x·x') hn hx hdx hlx) (by simp) (β_induction_on y hn hx hdx hlx)

end β
end utlc
end lambda_calculus