import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction

namespace utlc


namespace cost

def has := ℕ → Prop

def min (c : has) (x : ℕ) := c x ∧ ∀ m < x, ¬ c m

variables { x y : ℕ }
variable { c: has }

theorem min_exists : Π {x : ℕ}, c x → ∃ y, min c y
| 0 := begin
  intros cx,
  use 0,
  simp [min, cx]
end
| (x+1) := begin
  intros cx,
  by_contradiction,
  apply h,
  use (x+1),
  simp [min, cx],
  intros _ _ q,
  have h := min_exists q,
  contradiction
end

theorem min_unique: min c x → min c y → x = y :=
begin
  intros p q,
  simp [min] at p q,
  obtain _ | _ | _ := nat.lt_trichotomy x y,
  { exfalso,
    apply q.right x,
    assumption,
    apply p.left },
  { assumption },
  { exfalso,
    apply p.right y,
    assumption,
    apply q.left }
end

noncomputable def get (pf: ∃ x, c x) : ℕ := classical.some (min_exists (classical.some_spec pf))

lemma get_iff {pf: ∃ x, c x} : y = get pf ↔ min c y :=
begin
  split,
  all_goals { intro h },
  rw [h],
  any_goals { apply min_unique h },
  all_goals { apply classical.some_spec }
end

lemma get_iff' {pf: ∃ x, c x} : get pf = y ↔ min c y := by simp [eq_comm, get_iff]

lemma get_lt (pf: c x) : get (exists.intro x pf) ≤ x :=
begin
  let y := get (exists.intro x pf),
  have hy : get (exists.intro x pf) = y, by refl,
  rw [hy],
  rw [get_iff', min] at hy,
  contrapose! hy,
  intro,
  exact ⟨x, hy, pf⟩
end
  
end cost

def reducible_step_has_cost : utlc → utlc → (utlc → utlc → cost.has) → cost.has
| (index n) := λ g cr c, c > 0 ∧ cr (index n) g c
| (lambda f) := λ g cr c, (c > 0 ∧ cr (lambda f) g c) ∨ match g with
  | (lambda g) := reducible_step_has_cost f g cr c
  | _ := false
  end
| (application f1 f2) := λ g cr c, (c > 0 ∧ cr (application f1 f2) g c) ∨ match g with
  | (application g1 g2) :=
    ((reducible_step_has_cost f1 g1 cr c) ∧ f2 = g2) ∨ (f1 = g1 ∧ (reducible_step_has_cost f2 g2 cr c))
  | _ := false
  end

variables { f f' g : utlc } { r : utlc → utlc → Prop }

def reducible_cost_of (r : utlc → utlc → Prop) (cr : utlc → utlc → cost.has) :=
  ∀ {x y}, r x y ↔ ∃ c, c > 0 ∧ cr x y c

variables { cr : utlc → utlc → cost.has }

theorem reducible_step_cost_nzero : ¬ reducible_step_has_cost f g cr 0 :=
begin
  induction f with x f fh f f' fh fh' generalizing g,
  all_goals { cases g },
  all_goals { simp [reducible_step_has_cost] },
  apply fh,
  simp [fh, fh'],
end

theorem reducible_step_cost_pos (x : ℕ): reducible_step_has_cost f g cr x → 0 < x :=
begin
  cases x,
  simp [reducible_step_cost_nzero],
  simp [nat.zero_lt_succ _],
end

theorem reducible_step_cost_exists (cpf : reducible_cost_of r cr) : reducible_step f g r ↔ ∃ n, reducible_step_has_cost f g cr n :=
begin
  have iff_or : ∀ {a b c d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d),
  { intros a b c d h g, rw [h, g] },
  induction f with _ f fh f f' fh fh' generalizing g,
  { apply cpf },
  all_goals { cases g },
  all_goals { simp [reducible_step, reducible_step_has_cost, exists_or_distrib, iff_or, cpf] },
  rw [fh],
  rw [fh, fh']
end
 
noncomputable def reducible_step_cost (hab : (∃ x, reducible_step_has_cost f g cr x)) : ℕ := cost.get hab

def reducible_has_cost_helper : Π (n : ℕ) (cr: (utlc → utlc → cost.has)), utlc → utlc → Prop
| 0 := λ cr f g, (f = g)
| (x+1) := λ cr f g, ∃ (f' : utlc) (y < x + 1), reducible_step_has_cost f f' cr (x + 1 - y) ∧ reducible_has_cost_helper y cr f' g

def reducible_has_cost (f g : utlc) (cr): cost.has :=
  λ n, reducible_has_cost_helper n cr f g

theorem reducible_has_cost_of_step {f g : utlc} {x : ℕ}: reducible_step_has_cost f g cr x → reducible_has_cost f g cr x :=
begin
  cases x,
  { simp [reducible_has_cost, reducible_has_cost_helper],
    intro h,
    exfalso,
    apply reducible_step_cost_nzero h },
  simp [reducible_has_cost, reducible_has_cost_helper],
  intro n,
  use g,
  use 0,
  simp [n, reducible_has_cost_helper]
end

theorem reducible_has_cost_of_step' {f g : utlc} : (∃ x, reducible_step_has_cost f g cr x) → ∃ x, reducible_has_cost f g cr x :=
begin
  intro h,
  cases h with x h,
  exact ⟨x, reducible_has_cost_of_step h⟩
end

theorem reducible_has_cost_trans : Π {n m: ℕ} {cr : utlc → utlc → cost.has} {a b c : utlc},
  (reducible_has_cost a b cr n) → (reducible_has_cost b c cr m)  → (reducible_has_cost a c cr (n + m))
| 0 := begin
  intros m cr a b c hab hac,
  simp [reducible_has_cost, reducible_has_cost_helper] at hab,
  simp [hab, hac],
end
| (n+1) := begin
  intros m cr a b c hab hac,
  simp [reducible_has_cost, reducible_has_cost_helper] at hab,
  rcases hab with ⟨a', y, hab⟩,
  rw [← nat.succ_eq_add_one, nat.succ_add],
  unfold reducible_has_cost reducible_has_cost_helper,
  use a',
  use y + m,
  split,
  linarith [hab.left],
  split,
  apply (show ∀ x y, reducible_step_has_cost a a' cr x → x = y → reducible_step_has_cost a a' cr y, by { intros x y p h, simp[← h, p]}),
  apply hab.right.left,
  rw [nat.add_right_comm, nat.add_sub_add_right],
  cases hab,
  apply reducible_has_cost_trans,
  apply hab_right.right,
  assumption
end

theorem reducible_has_cost_pos {cr : utlc → utlc → cost.has} {a b : utlc} {y : ℕ}: a ≠ b → reducible_has_cost a b cr y → 0 < y :=
begin
  cases y,
  simp [reducible_has_cost, reducible_has_cost_helper],
  intros _ _,
  contradiction,
  simp [nat.zero_lt_succ y]
end

theorem reducible_has_cost_ne_iff {cr : utlc → utlc → cost.has} {a b : utlc} {x : ℕ} :
  a ≠ b → (reducible_has_cost a b cr x ↔ ∃ (f : utlc) (y < x), reducible_step_has_cost a f cr (x - y) ∧ reducible_has_cost_helper y cr f b) :=
begin
  intro nab,
  split,
  intro hab,
  cases x with x hx,
  exfalso,
  apply nab,
  simp [cost.get_iff', cost.min, reducible_has_cost, reducible_has_cost_helper] at hab,
  assumption,
  simp [reducible_has_cost, reducible_has_cost_helper] at hab,
  rcases hab with ⟨c, y, hc⟩,
  use c,
  use y,
  simp [nat.succ_eq_add_one],
  exact hc,
  intro h,
  cases x with x hx,
  simp at h,
  contradiction,
  simp [reducible_has_cost, reducible_has_cost_helper],
  rw [nat.succ_eq_add_one] at h,
  rcases h with ⟨c, y, p, hc⟩,
  use c,
  use y,
  exact ⟨p, hc⟩
end
  
section

variables {a b c : utlc}


noncomputable def reducible_cost (hab : (∃ x, (reducible_has_cost a b cr) x)) := cost.get hab

theorem reducible_cost_zero_iff {hab : (∃ x, (reducible_has_cost a b cr) x)} : reducible_cost hab = 0 ↔ a = b :=
by simp [reducible_cost, cost.get_iff', cost.min, reducible_has_cost, reducible_has_cost_helper]

theorem reducible_cost_zero {ha : (∃ x, (reducible_has_cost a a cr) x)} : reducible_cost ha = 0 :=
by simp [reducible_cost, cost.get_iff', cost.min, reducible_has_cost, reducible_has_cost_helper]

theorem reducible_cost_zero' {hab : (∃ x, (reducible_has_cost a b cr) x)} : a = b → reducible_cost hab = 0 :=
by simp [reducible_cost, cost.get_iff', cost.min, reducible_has_cost, reducible_has_cost_helper]

theorem reducible_cost_triangle
  {hab : (∃ x, (reducible_has_cost a b cr) x)}
  {hbc : (∃ x, (reducible_has_cost b c cr) x)}
  {hac : (∃ x, (reducible_has_cost a c cr) x)} : reducible_cost hac ≤ reducible_cost hab + reducible_cost hbc :=
begin
  simp [reducible_cost],
  let x := cost.get hab,
  let y := cost.get hbc,
  let z := cost.get hac,
  have hx : cost.get hab = x, by refl,
  have hy : cost.get hbc = y, by refl,
  have hz : cost.get hac = z, by refl,
  rw [hx, hy, hz],
  rw [cost.get_iff', cost.min] at hx hy hz,
  contrapose! hz with xyz,
  intro hac',
  use (x + y),
  refine ⟨xyz, _ ⟩,
  apply reducible_has_cost_trans hx.left hy.left,
end

theorem reducible_cost_single_lt {hab : (∃ x, reducible_step_has_cost a b cr x)}:
    reducible_cost (reducible_has_cost_of_step' hab) ≤ reducible_step_cost hab :=
begin
  by_cases (a=b),
  { rw [reducible_cost_zero'],
    apply nat.zero_le,
    apply h },
  simp [reducible_cost, reducible_step_cost],
  let x := cost.get (reducible_has_cost_of_step' hab),
  let y := cost.get hab,
  have hx : cost.get (reducible_has_cost_of_step' hab) = x, by refl,
  have hy : cost.get hab = y, by refl,
  rw [hx, hy],
  rw [cost.get_iff', cost.min] at hx hy,
  contrapose! hx with yx,
  intro habx,
  use y,
  refine ⟨yx, _⟩,
  rw [reducible_has_cost_ne_iff h],
  use b,
  use 0,
  simp [hy.left, reducible_has_cost_helper],
  apply reducible_step_cost_pos,
  apply hy.left,
end
end

end utlc