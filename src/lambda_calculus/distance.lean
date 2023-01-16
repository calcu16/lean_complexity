import tactic.basic
import tactic.linarith
import tactic.suggest

namespace lambda_calculus

variables {α: Type*}
variables {a b c: α}
variables {n m nm: ℕ}
variables {r: α → α → Prop}

def distance_le (r: α → α → Prop): ℕ → α → α → Prop
| 0 := λ f g, f = g
| (n+1) := λ f g, distance_le n f g ∨ ∃ x, (r f x ∨ r x f) ∧ distance_le n x g

theorem distance_le_zero (r: α → α → Prop): distance_le r 0 a b ↔ a = b := by simp[distance_le]

theorem distance_le_refl (a: α): distance_le r 0 a a := by rw[distance_le_zero]

theorem distance_le_one: distance_le r 1 a b ↔ (a = b ∨ r a b ∨ r b a) :=
by simp[distance_le]

theorem distance_le_single: r a b → distance_le r 1 a b :=
by { intro p, simp[distance_le_one, p] }

theorem distance_le_single': r b a → distance_le r 1 a b :=
by { intro p, simp[distance_le_one, p] }

theorem distance_le_succ: distance_le r n a b → distance_le r (n+1) a b :=
by { intro p, simp [distance_le, p] }

theorem distance_le_mono: distance_le r n a b → n ≤ m → distance_le r m a b :=
begin
  induction m generalizing n,
  { simp,
    intros _ hn,
    rw [← hn],
    assumption },
  { intros p hnm,
    cases eq_or_lt_of_le hnm,
    { rw [← h], assumption },
    exact distance_le_succ (m_ih p (nat.le_of_lt_succ h)) }
end

theorem distance_le_mono': n ≤ m → distance_le r n a b → distance_le r m a b :=
  λ p q, distance_le_mono q p

theorem distance_le_head: distance_le r (n+1) a b → ∃ f, distance_le r 1 a f ∧ distance_le r n f b :=
begin
  simp [distance_le],
  intro hx,
  cases hx,
  { exact ⟨a, or.inl rfl, hx⟩ },
  cases hx with x hx,
  exact ⟨x, or.inr hx.left, hx.right ⟩,
end

theorem distance_le_trans: distance_le r n a b → distance_le r m b c → distance_le r (n+m) a c :=
begin
  induction n generalizing m a b c,
  all_goals { simp [distance_le, nat.succ_add] },
  { intro ab, simp [ab, nat.zero_add] },
  intros hx hbc,
  cases hx,
  { exact or.inl (n_ih hx hbc) },
  right,
  cases hx with x hx,
  exact ⟨x, hx.left, n_ih hx.right hbc⟩
end

theorem distance_le_trans' (n m: ℕ): distance_le r n a b → distance_le r m b c → n + m = nm → distance_le r nm a c :=
begin
  intros hab hbc hnm,
  rw ←hnm,
  apply distance_le_trans hab hbc
end

theorem distance_le_trans_sub (n m: ℕ):
  distance_le r n a b → distance_le r (m - n) b c → n ≤ m → distance_le r m a c :=
begin
  intros hab hbc hnm,
  apply distance_le_trans' _ _ hab hbc,
  rw [nat.add_comm],
  apply nat.sub_add_cancel hnm,
end

theorem distance_le_symm: distance_le r n a b → distance_le r n b a :=
begin
  induction n generalizing a b,
  { simp [distance_le],
    apply eq.symm },
  { intro p,
    cases distance_le_head p with x hfx,
    apply distance_le_trans' _ 1,
    apply n_ih hfx.right,
    simp [distance_le] at *,
    cases hfx.left with h,
    { simp [h] },
    cases h with h,
    repeat { simp[h] },
    simp },
end

theorem distance_le_cong (f: α → α):
  (∀ {x y}, r x y → r (f x) (f y)) → distance_le r n a b →
  distance_le r n (f a) (f b) :=
begin
  intro p,
  induction n generalizing a b,
  { simp [distance_le_zero],
    intro h,
    rw [h] },
  { intro h,
    rcases distance_le_head h with ⟨c, hac, hcb⟩,
    rw [nat.succ_eq_add_one, nat.add_comm],
    apply distance_le_trans _ (n_ih hcb),
    rw [distance_le_one] at hac,
    rw [distance_le_one],
    obtain hac|hac|hac := hac,
    { simp [hac] },
    repeat { simp [p hac] } }
end

end lambda_calculus