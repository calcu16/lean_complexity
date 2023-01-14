import lambda_calculus.notation
import tactic.linarith

namespace lambda_calculus
/- Inductive definition of untyped lambda calculus using De Bruijn indexing
 - (https://en.wikipedia.org/wiki/De_Bruijn_index)
 -/
@[derive decidable_eq]
inductive utlc : Type
| index (n: ℕ): utlc
| abstraction (f: utlc) : utlc
| application (f g: utlc) : utlc

namespace utlc

@[pattern] instance : has_down utlc := ⟨ index ⟩
@[pattern] instance : has_lambda utlc := ⟨ abstraction ⟩
@[pattern] instance : has_dot utlc := ⟨ application ⟩
attribute [pattern] has_down.down has_lambda.lambda has_dot.dot

instance : inhabited utlc := ⟨ ↓0 ⟩

section -- Theorems so that we can use the notation instead of the raw names

@[simp] theorem ne_down_lambda (n : ℕ) (f: utlc) : ↓n ≠ Λ f :=
by apply utlc.no_confusion
@[simp] theorem ne_down_dot (n : ℕ) (f g : utlc) : ↓n ≠ f·g:=
by apply utlc.no_confusion
@[simp] theorem ne_lambda_down (f : utlc) (n : ℕ) : Λ f ≠ ↓n :=
by apply utlc.no_confusion
@[simp] theorem ne_lambda_dot (f g h: utlc): Λ f ≠ g·h :=
by apply utlc.no_confusion
@[simp] theorem ne_dot_down (f g: utlc) (n : ℕ) : f·g ≠ ↓n :=
by apply utlc.no_confusion
@[simp] theorem ne_dot_lambda (f g h: utlc) : f·g ≠ Λ h :=
by apply utlc.no_confusion

@[simp] theorem down_eq_down_iff {n m : ℕ}: (↓n : utlc) = ↓m ↔ n = m :=
begin
  split,
  intro p,
  exact utlc.no_confusion p (assume neq, neq),
  intro p,
  rw [p]
end

@[simp] theorem lambda_eq_lambda_iff {f g : utlc}: Λ f = Λ g ↔ f = g :=
begin
  split,
  intro p,
  exact utlc.no_confusion p (assume neq, neq),
  intro p,
  rw [p]
end

@[simp] theorem dot_eq_dot_iff {f f' g g': utlc}: f·g = f'·g' ↔ f = f' ∧ g = g' :=
begin
  split,
  intros p,
  exact utlc.no_confusion p (assume feq geq, and.intro feq geq),
  intro p,
  simp [p]
end

@[simp] theorem below_down (n: ℕ): (↓n:utlc).sizeof = 1 + n :=
begin
  unfold has_down.down,
  unfold_wf,
end

@[simp] theorem below_lambda (f: utlc): (Λ f).sizeof = 1 + f.sizeof :=
begin
  unfold has_lambda.lambda,
  unfold_wf,
end

@[simp] theorem below_dot (f g: utlc): (f·g).sizeof = 1 + f.sizeof + g.sizeof :=
begin
  unfold has_dot.dot,
  unfold_wf,
end

def repr: utlc → bool → string
| (↓n) := λ parens, "↓" ++ nat.repr n
| (Λ f) := λ parens, (ite parens "(" "") ++ "Λ " ++ (repr f false) ++ (ite parens ")" "")
| (f·g) := λ parens, (ite parens "(" "") ++ (repr f false) ++ "·" ++ (repr g true) ++ (ite parens ")" "")

instance : has_repr utlc := ⟨ λ f, repr f false ⟩

@[simp] theorem down_notation (n: ℕ): index n = ↓ n := rfl
@[simp] theorem lambda_notation (f: utlc): f.abstraction = Λ f  := rfl
@[simp] theorem dot_notation (f g: utlc): f.application g = f · g := rfl
end

@[simp] def size : utlc → ℕ
| (↓ _) := 1
| (Λ f) := f.size + 1
| (f · g) := f.size + g.size + 1

@[simp] def uses : utlc → ℕ → ℕ
| (↓ m) := λ n, if m = n then 1 else 0
| (Λ f) := λ n, uses f (n + 1)
| (f · g) := λ n, uses f n + uses g n

theorem lambda_uses (f: utlc) (n: ℕ): (Λ f).uses n = f.uses (n+1) :=
by simp

theorem dot_uses (f g: utlc) (n: ℕ): (f·g).uses n = f.uses n + g.uses n :=
by simp

@[simp] def closed_below : utlc → ℕ → bool
| (↓m) := λ n, m < n
| (Λ f) := λ n, f.closed_below (n+1)
| (f·g) := λ n, f.closed_below n ∧ g.closed_below n

@[simp] def closed (f : utlc) := closed_below f 0

def shift : utlc → ℕ → utlc
| (↓ m) := λ n, if m < n then ↓ m else ↓(m + 1)
| (Λ f) := λ n, Λ (shift f (n + 1))
| (f · g) := λ n, (shift f n) · (shift g n)

instance : has_shift utlc := ⟨ shift ⟩

@[simp] theorem down_shift (m n: ℕ): (↓m)↑¹n = (↓(if m < n then m else m + 1):utlc) :=
begin
  split_ifs;
  unfold has_shift.shift;
  simp [shift, h],
end

@[simp] theorem lambda_shift (f: utlc) (n: ℕ):  (Λ f) ↑¹ n = Λ(f ↑¹ (n+1)) :=
begin
  unfold has_shift.shift,
  simp [shift]
end

@[simp] theorem dot_shift (f f': utlc) (n: ℕ):  (f·f') ↑¹ n = (f ↑¹ n)·(f' ↑¹ n) :=
begin
  unfold has_shift.shift,
  simp [shift]
end

@[simp] theorem shift_notation (f: utlc) (n: ℕ): f.shift n = f ↑¹ n := rfl

def substitution : utlc → ℕ → utlc → utlc
| (↓m) := λ n x, if m < n then ↓ m else if m = n then x else ↓ (m-1)
| (Λ f) := λ n x, Λ (substitution f (n + 1) (x ↑¹ 0))
| (f · g) := λ n x, (substitution f n x) · (substitution g n x)

instance : has_substitution utlc := ⟨ substitution ⟩

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

@[simp] theorem down_substitution (m n: ℕ) (g: utlc): (↓m)[n:=g] = if m < n then ↓m else if m = n then g else ↓(m-1) :=
by simp[has_substitution.substitution, substitution]

@[simp] theorem lambda_substitution (f: utlc) (n: ℕ) (g: utlc): (Λ f)[n:=g] = Λ f[n+1:=g ↑¹ 0] :=
by simp[has_substitution.substitution, substitution]

@[simp] theorem dot_substitution (f f': utlc) (n: ℕ) (g: utlc): (f·f')[n:=g] = f[n:=g]·f'[n:=g] :=
by simp[has_substitution.substitution, substitution]

@[simp] theorem substitution_notation (f: utlc) (n: ℕ) (g: utlc): f.substitution n g = f[n:=g] := rfl

-- inductive hypothesis useful when dealing with substitutions
-- splits f·g up to handle the (Λ f)·g ⇔ f[0:=g] case
theorem substitution_induction_on (p: utlc → Prop): Π (f: utlc)
  (down: Π n, p ↓n)
  (lambda: Π x (hx: p x), p (Λ x))
  (down_dot : Π n x (hn: p ↓n) (hx: p x), p (↓n·x))
  (lambda_dot: Π x y (hx: p x) (hx': p (Λ x)) (hy: p y), p ((Λ x)·y))
  (dot_dot: Π x y z (hx: p x) (hy: p y) (hxy: p (x·y)) (hz: p z), p ((x·y)·z)),
  (p f)
| (↓n) := λ hn _ _ _ _, hn n
| (Λ x) := λ hn hx hnx hxy hxyz, hx x (substitution_induction_on x hn hx hnx hxy hxyz)
| (↓n·x) := λ hn hx hnx hxy hxyz, hnx n x (hn n) (substitution_induction_on x hn hx hnx hxy hxyz)
| ((Λ x)·y) := λ hn hx hnx hxy hxyz, hxy x y
  (substitution_induction_on x hn hx hnx hxy hxyz)
  (substitution_induction_on (Λ x) hn hx hnx hxy hxyz)
  (substitution_induction_on y hn hx hnx hxy hxyz)
| ((x·y)·z) := λ hn hx hnx hxy hxyz, hxyz x y z
  (substitution_induction_on x hn hx hnx hxy hxyz)
  (substitution_induction_on y hn hx hnx hxy hxyz)
  (substitution_induction_on (x·y) hn hx hnx hxy hxyz)
  (substitution_induction_on z hn hx hnx hxy hxyz)

end utlc
end lambda_calculus