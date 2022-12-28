import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction

namespace utlc

variables {n m k d : ℕ}
variables {f f' g: utlc}

def shift : utlc → ℕ → ℕ → utlc
| (↓ m) := λ Δ n, if m < n then ↓ m else ↓ (m + Δ)
| (Λ f) := λ Δ n, Λ (shift f Δ (n + 1))
| (f · g) := λ Δ n, (shift f Δ n) · (shift g Δ n)

theorem shift_zero : shift f 0 n = f :=
begin
  induction f generalizing n,
  all_goals { simp [shift, *] },
end

theorem shift_shift_comm : (f.shift k n).shift d (m+k+n) = (f.shift d (m + n)).shift k n :=
begin
  induction f with _ f hf f f' hf hf' generalizing k n m d,
  all_goals { simp [shift] },
  { split_ifs,
    all_goals { simp [shift] },
    all_goals { split_ifs },
    all_goals { simp },
    any_goals { { exfalso, linarith } },
    ring },
  { simp [nat.add_assoc _ n _],
    rw [hf] },
  { simp [hf, hf'] }
end

theorem shift_shift_comm' : k ≤ m → (f.shift k 0).shift n m = (f.shift n (m - k)).shift k 0 :=
begin
  intro p,
  have g := @shift_shift_comm 0 (m - k) k n f,
  simp[nat.sub_add_cancel p] at g,
  assumption
end

theorem shift_shift_add : (f.shift (d + k) n).shift m (k + n) = f.shift (d + k + m) n :=
begin
  induction f with _ f fh f g fh gh generalizing n,
  all_goals { simp[shift] },
  { split_ifs,
    all_goals { simp[shift] },
    intro p,
    exfalso, linarith,
    split_ifs,
    exfalso, linarith,
    simp [nat.add_assoc] },
  { simp [nat.add_assoc, fh] },
  { simp [fh, gh] }
end

theorem shift_shift_add' : (f.shift (d + k) 0).shift m k = f.shift (d + k + m) 0 :=
begin
  have g := @shift_shift_add 0 m k d f,
  simp at g,
  assumption
end

theorem size_shift : size (shift f n m) = size f :=
begin
  induction f with _ f fh f g fh gh generalizing m,
  all_goals { simp[size, shift, apply_ite size] },
  apply fh,
  rw [fh, gh]
end

theorem uses_shift_lt : n < k → uses (shift f m k) n = uses f n :=
begin
  revert n k,
  induction f with x f fh f g fh gh,
  all_goals { intros n k nk, simp [shift, uses] },
  { split_ifs,
    all_goals { simp [uses], intro },
    any_goals { contradiction },
    all_goals { linarith } },
  rw [@fh (n + 1) (k + 1) (by linarith)],
  rw [fh nk, gh nk],
end

theorem uses_shift_zero : k ≤ n → n < k + m → uses (shift f m k) n = 0 :=
begin
  revert n k,
  induction f with x f fh f g fh gh,
  all_goals { intros n k kn nkm, simp [shift, uses] },
  { split_ifs,
    all_goals { simp [uses] },
    { intro, linarith },
    contrapose! h,
    simp at h,
    linarith },
  { apply fh, repeat { linarith } },
  split,
  apply fh,
  repeat { assumption },
  apply gh,
  repeat { assumption },
end

theorem uses_shift_ge : k ≤ n → (f.shift m k).uses (n + m) = f.uses n :=
begin
  revert n k,
  induction f with x f fh f g fh gh,
  all_goals { intros n k kn, simp [shift, uses] },
  {
    split_ifs,
    all_goals { simp [uses, h_1] },
    linarith,
    contrapose! h_1,
    simp at h_1,
    linarith,
  },
  { rw [nat.add_right_comm], apply fh, repeat { linarith } },
  apply show ∀ a b c d : ℕ, a = c → b = d → a + b = c + d, by
  { intros _ _ _ _ p q,
    rw [p, q] },
  apply fh,
  repeat { assumption },
  apply gh,
  repeat { assumption },
end

theorem uses_shift_ge' : m ≤ n → k + m ≤ n → (f.shift m k).uses n = f.uses (n - m) :=
begin
  intros mn kn,
  let x := n - m,
  have g : n = x + m, by rw [
    show x = n - m, by refl,
    nat.add_comm,
    ← nat.add_sub_assoc mn,
    nat.add_sub_cancel_left],
  rw [show n - m = x, by refl, g],
  apply uses_shift_ge,
  linarith,
end

def unused : utlc → ℕ → bool
| (↓m) := λ n, n ≠ m
| (Λ f) := λ n, f.unused (n+1)
| (f·g) := λ n, f.unused n ∧ g.unused n

def closed_below : utlc → ℕ → bool
| (↓m) := λ n, m < n
| (Λ f) := λ n, f.closed_below (n+1)
| (f·g) := λ n, f.closed_below n ∧ g.closed_below n

@[simp] def closed (f : utlc) := closed_below f 0

theorem uses_closed_below (f: utlc) (n : ℕ) : f.closed_below n ↔ ∀ m, n ≤ m → f.uses m = 0 :=
begin
  induction f with _ _ fh _ _ fh gh generalizing n,
  { simp [closed_below, uses],
    split,
    intros fn x nm fx,
    linarith,
    intro p,
    contrapose! p,
    use f,
    simp [p] },
  { simp[closed_below, uses],
    rw [fh (n + 1)],
    split,
    intros h m nm,
    specialize h (m + 1) (by linarith),
    assumption,
    intros h m,
    cases m,
    simp,
    simp [nat.succ_eq_add_one],
    apply h },
  { simp[closed_below, uses],
    split,
    intros pq m nm,
    exact ⟨(fh n).mp pq.left m nm, (gh n).mp pq.right m nm⟩,
    rw [fh, gh],
    intros pq,
    split,
    intros m nm,
    exact (pq m nm).left,
    intros m nm,
    exact (pq m nm).right }
end

theorem shift_closed_below {f: utlc} {n m k: ℕ} :
  f.closed_below n → n ≤ k → f.shift m k = f :=
begin
  induction f with _ f fh f g fh gh generalizing n k,
  all_goals { simp [closed_below, shift] },
  { intros p q r,
    exfalso,
    linarith },
  { intros p q,
    apply fh p,
    linarith },
  intros p q r,
  exact ⟨ fh p r, gh q r ⟩
end

theorem shift_closed {f: utlc}:
  f.closed → ∀ n m, f.shift n m = f :=
begin
  unfold closed,
  intros p n m,
  exact shift_closed_below p (nat.zero_le m)
end

end utlc