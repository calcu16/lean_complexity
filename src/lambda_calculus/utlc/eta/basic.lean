import lambda_calculus.notation
import lambda_calculus.utlc.basic
import lambda_calculus.utlc.identities
import lambda_calculus.utlc.reduction
import logic.relation

namespace lambda_calculus
namespace utlc
namespace η

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

variables {f g f' g' x y z: utlc}

@[simp]
def head_step : utlc → utlc → Prop := λ f g, f = Λ (g ↑¹ 0)·↓0

instance : has_η_reduction utlc := ⟨ reduction_step_of head_step ⟩

@[simp] theorem down_step {n: ℕ}: ¬ ↓n →η g :=
begin
  simp [has_η_reduction.step, reduction_step],
end

theorem lambda_step_lambda : f →η g → (Λ f) →η (Λ g) :=
begin
  intro p,
  simp [has_η_reduction.step, reduction_step],
  exact or.inr p
end

theorem lambda_step_head (f: utlc): Λ (f ↑¹ 0)·↓0 →η f :=
by simp [has_η_reduction.step, reduction_step]

theorem lambda_step_head': f = (g ↑¹ 0)·↓0 → Λ f →η g :=
by { intro p, rw[p], exact lambda_step_head _ }

theorem lambda_step_iff: Λ f →η g ↔ (∃ x, g = x ∧ f = (x ↑¹ 0)·↓0) ∨ (∃ x, g = Λ x ∧ f →η x) :=
by simp [has_η_reduction.step, reduction_step]

theorem lambda_step_cases : Λ f →η g → (∃ x, g = Λ x ∧ f →η x ∨ g = x ∧ f = (x ↑¹ 0)·↓0) :=
begin
  simp [has_η_reduction.step, reduction_step],
  intro p,
  cases p,
  use g,
  exact or.inr ⟨rfl, p⟩,
  cases g,
  all_goals { simp [has_η_reduction.step, reduction_step] at * },
  any_goals { contradiction },
  use g,
  exact or.inl ⟨rfl, p⟩,  
end

theorem lambda_step_cases': Λ f →η g → (∃ x, g = Λ x ∧ f →η x) ∨ ∃ x, g = x ∧ f = (x ↑¹ 0)·↓0 :=
begin
  intro p,
  cases lambda_step_cases p,
  cases h,
  left,
  use w,
  assumption,
  right,
  use w,
  assumption,
end

theorem dot_step_dot_left : f →η f' → (f·g) →η (f'·g) :=
begin
  intro p,
  simp [has_η_reduction.step, reduction_step],
  exact or.inl p,
end

theorem dot_step_dot_right : g →η g' → (f·g) →η (f·g') :=
begin
  intro p,
  simp [has_η_reduction.step, reduction_step],
  exact or.inr p,
end

theorem dot_step_iff: (f·f') →η g ↔ ∃ x x', g = x·x' ∧ (x' = f' ∧ f →η x ∨ x = f ∧ f' →η x') :=
begin
  cases g,
  all_goals { simp [has_η_reduction.step, and_assoc] },
end

theorem dot_step_iff': (f·f') →η g ↔ (∃ x x', x' = f' ∧ g = x·x' ∧ f →η x) ∨ (∃ x x', x = f ∧ g = x·x' ∧ f' →η x') :=
begin
  cases g,
  all_goals { simp [has_η_reduction.step, and_assoc] },
end

theorem dot_step_cases: (f·f') →η g → ∃ x x', g = x·x' ∧ (x' = f' ∧ f →η x ∨ x = f ∧ f' →η x') :=
begin
  cases g,
  all_goals { simp [has_η_reduction.step, and_assoc] },
end

theorem dot_step_cases': (f·f') →η g → (∃ x x', x' = f' ∧ g = x·x' ∧ f →η x) ∨ (∃ x x', x = f ∧ g = x·x' ∧ f' →η x') :=
begin
  cases g,
  all_goals { simp [has_η_reduction.step, and_assoc] },
end

theorem reduction_step_shift (n: ℕ): f ↑¹ n →η g ↑¹ n → f →η g :=
begin
  induction f generalizing g n,
  { simp[down_shift] },
  { simp,
    intro p,
    cases lambda_step_cases p with x p,
    cases p with p p,
    { cases p with hgx hfx,
      have h: (g ↑¹ n).uses n = x.uses (n + 1),
      { simp [hgx, uses] },
      have h: ∃ y, x = y ↑¹ (n+1),
      { apply shift_of_uses_zero,
        rw [← h],
        simp [shift_uses] },
      cases h with y hy,
      rw [hy,
          ← show (Λ y) ↑¹ n = Λ y ↑¹ (n+1), by simp,
          shift_inj_iff] at hgx,
      rw [hgx],
      apply lambda_step_lambda,
      apply f_ih,
      rw [← hy],
      apply hfx },
    { cases p with hgx hfx,
      -- rw [← hgx, ← shift_comm] at hfx,
      apply lambda_step_head',
      rw [← shift_inj_iff (n + 1), hfx],
      simp [down_shift],
      rw [← shift_comm_zero, hgx] } },
  { simp,
    intro p,
    cases g;
    try { simp[has_η_reduction.step, reduction_step, dot_step_iff, down_shift] at p,
      contradiction },
    rcases dot_step_cases p with ⟨x, y, hgxy, p⟩,
    simp at hgxy,
    simp,
    cases p with p p,
    cases p with hfy hfx,
    simp [hfy] at hgxy,
    rw [hgxy.right],
    rw [← hgxy.left] at hfx,
    exact dot_step_dot_left (f_ih_f _ hfx),
    cases p with hfx hfy,
    simp [hfx] at hgxy,
    rw [hgxy.left],
    rw [← hgxy.right] at hfy,
    exact dot_step_dot_right (f_ih_g _ hfy)
     }
end

theorem reduction_step_uses: f →η g → ∀ n, f.uses n = g.uses n :=
begin
  induction f generalizing g,
  { all_goals { simp } },
  { intros p n,
    cases lambda_step_cases p with x p,
    cases p with p p,
    { simp [uses, p.left], exact f_ih p.right _},
    { simp [uses, p, show 0 ≠ n + 1, by linarith] } },
  {
    intros p m,
    rcases dot_step_cases p with ⟨x, y, hg, p⟩,
    cases p with p p,
    { simp [p.left, hg, uses],
      apply f_ih_f p.right },
    { simp [p.left, hg, uses],
      apply f_ih_g p.right } }
end

theorem reduction_step_size: f →η g → f.size = g.size + 3 :=
begin
  induction f generalizing g;
  simp,
  simp [lambda_step_iff],
  intro p,
  cases p,
  { rw [p], simp },
  { rcases p with ⟨x, hgx, hfx⟩,
    simp [f_ih hfx, hgx] },
  { intro p,
    rcases dot_step_cases p with ⟨x, y, hgxy, p⟩,
    cases p with p p;
    rcases p with ⟨heq, hstep⟩,
    simp [f_ih_f hstep, hgxy, ← heq],
    ring,
    simp [f_ih_g hstep, hgxy, ← heq],
    ring,
  }
end

theorem reduction_step_size_mono: f →η g → g.size < f.size :=
by intro p; simp [reduction_step_size p]

@[simp] theorem down_reduction_iff {n: ℕ}: ↓n ↠η g ↔ g = ↓n :=
begin
  split;
  intro p,
  cases relation.refl_trans_gen.cases_head p,
  { apply h.symm },
  { simp at h, contradiction },
  rw [p],
end

theorem lambda_reduction_lambda: f ↠η f' → Λ f ↠η Λ f' :=
begin
  intro p,
  induction p,
  { refl },
  apply relation.refl_trans_gen.tail,
  assumption,
  apply lambda_step_lambda,
  assumption,
end

theorem dot_reduction_dot_left: f ↠η f' → f·g ↠η f'·g :=
begin
  intro p,
  induction p,
  { refl },
  apply relation.refl_trans_gen.tail,
  assumption,
  apply dot_step_dot_left,
  assumption,
end

theorem dot_reduction_dot_right: g ↠η g' → f·g ↠η f·g' :=
begin
  intro p,
  induction p,
  { refl },
  apply relation.refl_trans_gen.tail,
  assumption,
  apply dot_step_dot_right,
  assumption,
end

theorem dot_reduction_dot: f ↠η f' → g ↠η g' → f·g ↠η f'·g' :=
begin
  intros p q,
  apply trans,
  apply dot_reduction_dot_left,
  assumption,
  apply dot_reduction_dot_right,
  assumption,
end

theorem dot_exists_reduction (h: f ↠η g): ∀ {m n}, f = m·n → ∃ x y, g = x·y ∧ m ↠η x ∧ n ↠η y :=
begin
  induction h using relation.refl_trans_gen.head_induction_on with f f' hf hfg ih,
  { intros m n p,
    refine ⟨ m, n, p, by refl, by refl⟩ },
  { intros m n p,
    rw [p] at hf,
    rcases dot_step_cases hf with ⟨a, b, hab, h⟩,
    rcases ih hab with ⟨i, j, ih⟩,
    refine ⟨i, j, ih.left, trans _ ih.right.left, trans _ ih.right.right⟩;
    cases h;
    try { simp[h] };
    cases h;
    try { apply relation.refl_trans_gen.single, assumption } }
end

theorem dot_reduction_cases (h: f·f' ↠η g): ∃ x y, g = x·y ∧ f ↠η x ∧ f' ↠η y := dot_exists_reduction h rfl

theorem dot_reduction_dot_iff: f·g ↠η f'·g' ↔ f ↠η f' ∧ g ↠η g' :=
begin
  split,
  { intro p,
    have h := dot_exists_reduction p rfl,
    simp [and.assoc] at h,
    assumption },
  intro p,
  apply dot_reduction_dot p.left p.right,
end

theorem shift_head_step_shift {n: ℕ}: head_step (f ↑¹ n) (g ↑¹ n) ↔ head_step f g :=
begin
  cases f;
  cases g;
  try { simp };
  cases f;
  try { simp[down_shift] };
  cases f_f;
  cases f_g;
  simp [down_shift];
  split_ifs;
  simp;
  try { simp [← @shift_comm 1 (n + 1) _ (by linarith)] };
  try { simp [← @shift_comm 0 n _ (by linarith)] };
  repeat { intro };
  try { linarith };
  split;
  intro;
  try { linarith },
  rw [← @shift_inj_iff _ (n + 1 + 1), shift_comm],
  assumption,
  linarith,
  rw [← shift_comm, shift_inj_iff],
  assumption,
  linarith,
end

theorem head_step_substitution: head_step f f' → ∀ n g, f[n:=g] ↠η f'[n:=g]  :=
begin
  simp only [head_step],
  intros p n g,
  simp [p],
  apply relation.refl_trans_gen.single,
  apply lambda_step_head',
  simp,
  apply substitution_shift_ge,
  apply nat.zero_le _,
end

def head_reduced : utlc → bool
| (↓ _):= true
| (Λ f) := match f with
  | (↓ _) := true
  | (Λ _) := true
  | (f·g) := f.uses 0 > 0 ∨ g ≠ ↓0
  end
| (_·_) := true

def reduced := reduced_of head_reduced

theorem head_reduced_iff_not_head_step: head_reduced f ↔ ∀ g, ¬ head_step f g :=
begin
  cases f;
  try { cases f };
  simp[head_reduced],
  split,
  { intros p g q,
    cases p,
    exfalso,
    apply (ne_of_lt p).symm,
    rw [q],
    apply shift_uses_self,
    assumption },
  intros p,
  obtain h|h|h := nat.lt_trichotomy (f_f.uses 0) 0,
  { simp at h, contradiction },
  { cases shift_of_uses_zero h with g h,
    right,
    apply p g h },
  { left, apply h },
end

theorem reduced_iff_not_reduction (f: utlc): reduced f ↔ ∀ g, ¬ f →η g :=
  reduced_iff_not_reduction_step @head_reduced_iff_not_head_step _


@[simp] theorem down_reduced (n: ℕ): reduced ↓n := by simp [reduced, head_reduced, down_reduced]

theorem lambda_reduced (f: utlc): reduced (Λ f) ↔ head_reduced (Λ f) ∧ reduced f :=
by simp [reduced, head_reduced, lambda_reduced]

@[simp] theorem dot_reduced (f g: utlc): reduced (f·g) ↔ reduced f ∧ reduced g := by simp [reduced, head_reduced, dot_reduced]

-- inductive hypothesis useful when dealing with η reductions
-- splits (Λ f·↓0) up to handle the (Λ f)·g ⇔ f[0:=g] case
-- theorem η_induction_on (p: utlc → Prop): Π (f: utlc)
--   (down: Π n, p ↓n)
--   (dot_lambda: Π x (hx: p x) (h: x.uses 0 = 0), p (Λ x·↓0))
--   (lambda: Π x (hx: p x) (h: head_reduced x), p (Λ x))
--   (dot : Π x y (hx: p x) (hy: p y), p (x·y)),
--   (p f)
-- | (↓n) := λ hn hx hdx hlx, hn n
-- | (Λ x) := λ hn hx hdx hlx, hx x (β_induction_on x hn hx hdx hlx)

end η
end utlc
end lambda_calculus