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
  | (Λ f1) := λ g, g = f1[0:=f2]
  | (_ · _) := λ g, false
  end

section
local attribute [simp] head_step

instance head_step.decidable_rel : decidable_rel head_step :=
begin
  intros f _,
  induction f using lambda_calculus.utlc.notation_cases_on,
  repeat { unfold head_step, apply_instance },
  induction f_f using lambda_calculus.utlc.notation_cases_on,
  repeat { unfold head_step, apply_instance }
end

theorem head_step_exists (f g: utlc): head_step f g ↔
  ∃ x y, f = (Λ x)·y ∧ g = x[0:=y] :=
by cases f; try { cases f_f }; simp [and.assoc]
end
attribute [simp] head_step_exists
attribute [irreducible] head_step

instance : has_β_reduction utlc := ⟨ reduction_step_of head_step ⟩

section
@[simp] theorem not_index_step (n: ℕ) (g: utlc): ¬ ↓n →β g := by simp [has_β_reduction.step]

theorem lambda_step_iff (f g: utlc): Λ f →β g ↔ ∃ x, g = Λ x ∧ f →β x := by simp [has_β_reduction.step]

theorem dot_step_iff (f f' g: utlc): f·f' →β g ↔
  (∃ x, g = x[0:=f'] ∧ f = Λ x) ∨
  (∃ x, g = x·f' ∧ f →β x) ∨
  (∃ x, g = f·x ∧ f' →β x) :=
by simp [and.assoc, has_β_reduction.step, @and.comm (g = _[0:=f'])]
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
  simp [and.assoc, lambda_step_iff, dot_step_iff, show 0 ≠ n + 1, by linarith, nat.succ_eq_add_one, @eq_comm _ ↓n],
end

theorem dot_step_dot_left: f →β f' → ∀ g, f·g →β f'·g :=
by intro p; simpa [dot_step_iff] using λ _, or.inr (or.inl p)

theorem dot_step_dot_right: g →β g' → ∀ f, f·g →β f·g' :=
by intro p; simpa [dot_step_iff] using λ _, or.inr (or.inr p)

theorem dot_step_cases: f·f' →β g →
  (∃ x, g = x[0:=f'] ∧ f = Λ x) ∨
  (∃ x, g = x·f' ∧ f →β x) ∨
  (∃ x, g = f·x ∧ f' →β x) := (dot_step_iff f f' g).mp

theorem dot_step_cases': (∀ x, f ≠ Λ x) → f·f' →β g →
  (∃ x, g = x·f' ∧ f →β x) ∨
  (∃ x, g = f·x ∧ f' →β x) :=
begin
  intros p q,
  cases dot_step_cases q with q q,
  { rcases q with ⟨x, q, _⟩,
    specialize p x,
    contradiction },
  assumption
end

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
  obtain h|h|h := dot_step_cases h,
  { revert h, simp },
  all_goals {
    rcases h with ⟨w, hw, h⟩,
    rw [dot_eq_dot_iff] at hw,
    rw [hw.left, hw.right] },
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
  λ p q, trans (dot_reduction_dot relation.refl_trans_gen.refl q) $
         trans (dot_reduction_dot p relation.refl_trans_gen.refl) $
         relation.refl_trans_gen.single $
         lambda_dot_step_substitution _ _

theorem uses_zero_head_step: head_step f g → ∀ {n}, f.uses n = 0 → g.uses n = 0 :=
begin
  induction f using lambda_calculus.utlc.notation_cases_on,
  { simp },
  { simp },
  simp only [head_step_exists, dot_uses, add_eq_zero_iff, forall_exists_index, and_imp],
  intros x y p q n hf hg,
  rw [dot_eq_dot_iff] at p,
  rw [q, ← p.right, substitution_uses_le (nat.zero_le _),
    ← lambda_uses, ← p.left, hf, hg, zero_add, mul_zero]
end

theorem uses_zero_step: f →β g → ∀ {n}, f.uses n = 0 → g.uses n = 0 := uses_zero_reduction_step @uses_zero_head_step

theorem shift_head_step_shift {n: ℕ}: head_step (f ↑¹ n) (g ↑¹ n) ↔ head_step f g :=
by induction f; simp [down_shift, and.assoc, shift_eq_lambda_iff, substitution_shift_zero]

theorem shift_head_step_shift' {n: ℕ}: head_step f g ↔ head_step (f ↑¹ n) (g ↑¹ n)  :=
by rw [shift_head_step_shift]


theorem shift_step_shift: f →β g → ∀ n, (f ↑¹ n) →β (g ↑¹ n) :=
by simp [has_β_reduction.step, shift_reduction_step_shift_iff @shift_head_step_shift]

theorem shift_reduction_shift: f ↠β g → ∀ n, (f ↑¹ n) ↠β (g ↑¹ n) :=
  λ p n, shift_refl_trans_reduction_shift (@shift_head_step_shift) p

def head_reduced : utlc → bool
| (↓ _) := true
| (Λ _) := true
| (f·g) := match f with
  | (↓ _) := true
  | (Λ _) := false
  | (f·g) := true
  end

def reduced := λ f, lambda_calculus.utlc.reduced_of head_reduced f

theorem head_reduced_iff_not_head_step: head_reduced f ↔ ∀ g, ¬ head_step f g :=
by cases f; try { cases f_f }; simp[reduced, head_reduced]

@[simp] theorem down_reduced (n: ℕ): reduced (↓n:utlc) := by simp [reduced, head_reduced]

@[simp] theorem lambda_reduced:
  reduced (Λ f) = reduced f := by simp [reduced, head_reduced, reduced_of, utlc.reduced]

@[simp] theorem dot_reduced:
  reduced (f·g) = ((¬ f.is_lambda) ∧ reduced f ∧ reduced g) :=
by cases f; simp [reduced, head_reduced, ← not_exists, reduced_of, utlc.reduced]

def reduced_of_not_reduction (f: utlc): reduced f ↔ ∀ g, ¬ f →β g :=
  reduced_iff_not_reduction_step @head_reduced_iff_not_head_step _

-- inductive hypothesis useful when dealing with β reductions
-- splits f·g up to handle the (Λ f)·g ⇔ f[0:=g] case
theorem induction_on (p: utlc → Prop): Π (f: utlc)
  (down: Π n, p ↓n)
  (lambda: Π x (hx: p x), p (Λ x))
  (dot : Π x y (hx: p x) (hnx: ∀ x', x ≠ Λ x') (hy: p y), p (x·y))
  (lambda_dot: Π x y (hx: p (Λ x)) (hx': p x) (hy: p y), p ((Λ x)·y)),
  (p f)
| (↓n) := λ hn hx hdx hlx, hn n
| (Λ x) := λ hn hx hdx hlx, hx x (induction_on x hn hx hdx hlx)
| (↓n·y) := λ hn hx hdx hlx, hdx (↓n) y (hn n) (by simp) (induction_on y hn hx hdx hlx)
| ((Λ x)·y) := λ hn hx hdx hlx, hlx x y (induction_on (Λ x) hn hx hdx hlx) (induction_on x hn hx hdx hlx) (induction_on y hn hx hdx hlx)
| (x·x'·y) := λ hn hx hdx hlx, hdx (x·x') y (induction_on (x·x') hn hx hdx hlx) (by simp) (induction_on y hn hx hdx hlx)


theorem lambda_of_reduced_and_closed: reduced f → f.closed → ∃ g, f = Λ g :=
begin
  induction f using lambda_calculus.utlc.β.induction_on,
  { simp },
  { simp },
  { simp only [dot_reduced, dot_closed, and_imp, bool.coe_to_bool],
    intros f_hnx hxr hyr hxc hyc,
    cases f_hx hxr hxc with g f_hx,
    revert f_hnx,
    simp [f_hx] },
  { simp [← not_exists] }
end

end β
end utlc
end lambda_calculus