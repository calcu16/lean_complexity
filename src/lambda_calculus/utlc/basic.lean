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

@[simp] def is_down: utlc → Prop
| (↓_) := true
| (Λ _) := false
| (_·_) := false

@[simp] def is_lambda: utlc → Prop
| (↓_) := false
| (Λ _) := true
| (_·_) := false

@[simp] def is_dot: utlc → Prop
| (↓_) := false
| (Λ _) := false
| (_·_) := true

@[simp] def size : utlc → ℕ
| (↓ _) := 1
| (Λ f) := f.size + 1
| (f · g) := f.size + g.size + 1

@[simp] def uses : utlc → ℕ → ℕ
| (↓ m) := λ n, if m = n then 1 else 0
| (Λ f) := λ n, uses f (n + 1)
| (f · g) := λ n, uses f n + uses g n

theorem lambda_uses (f: utlc) (n: ℕ): (Λ f).uses n = f.uses (n+1) := rfl

theorem dot_uses (f g: utlc) (n: ℕ): (f·g).uses n = f.uses n + g.uses n := rfl

section

def closed_below : utlc → ℕ → bool
| (↓m) := λ n, m < n
| (Λ f) := λ n, f.closed_below (n+1)
| (f·g) := λ n, f.closed_below n ∧ g.closed_below n

local attribute [simp] closed_below

@[simp] theorem down_closed_below (n m: ℕ): closed_below (↓n) m ↔ n < m := by simp

@[simp] theorem lambda_closed_below (f: utlc) (n: ℕ): closed_below (Λ f) n = closed_below f (n + 1) := rfl

@[simp] theorem dot_closed_below (f g: utlc) (n: ℕ): closed_below (f·g) n = (closed_below f n ∧ closed_below g n) := rfl

def closed (f : utlc) := closed_below f 0

local attribute [simp] closed

@[simp] theorem down_not_closed (n: ℕ): ¬ closed (↓n) := by simp

@[simp] theorem lambda_closed (f: utlc): closed (Λ f) = closed_below f 1 := rfl

@[simp] theorem dot_closed (f g: utlc): closed (f·g) = (closed f ∧ closed g) := rfl
end

section
def shift : utlc → ℕ → utlc
| (↓ m) := λ n, if m < n then ↓ m else ↓(m + 1)
| (Λ f) := λ n, Λ (shift f (n + 1))
| (f · g) := λ n, (shift f n) · (shift g n)

local attribute [simp] shift

instance : has_shift utlc := ⟨ shift ⟩

theorem down_shift (m n: ℕ): (↓m)↑¹n = (↓(if m < n then m else m + 1):utlc) :=
by split_ifs; simp [h, has_shift.shift]

@[simp] theorem lambda_shift (f: utlc) (n: ℕ):  (Λ f) ↑¹ n = Λ(f ↑¹ (n+1)) :=
by simp [has_shift.shift]

@[simp] theorem dot_shift (f f': utlc) (n: ℕ):  (f·f') ↑¹ n = (f ↑¹ n)·(f' ↑¹ n) :=
by simp [has_shift.shift]

theorem shift_eq_lambda_iff (f: utlc) (n: ℕ) (g: utlc): f ↑¹ n = Λ g ↔ ∃ x, f = Λ x ∧ x ↑¹ (n + 1) = g :=
by cases f; simp[down_shift]

theorem shift_eq_dot_iff (f: utlc) (n: ℕ) (g g': utlc): f ↑¹ n = g·g' ↔ ∃ x x', f = x·x' ∧ x ↑¹ n = g ∧ x' ↑¹ n = g' :=
by cases f; simp[and.assoc, down_shift]

@[simp] theorem shift_notation (f: utlc) (n: ℕ): f.shift n = f ↑¹ n := rfl
end

section
def substitution : utlc → ℕ → utlc → utlc
| (↓m) := λ n x, if m < n then ↓ m else if m = n then x else ↓ (m-1)
| (Λ f) := λ n x, Λ (substitution f (n + 1) (x ↑¹ 0))
| (f · g) := λ n x, (substitution f n x) · (substitution g n x)

instance : has_substitution utlc := ⟨ substitution ⟩
local attribute [simp] substitution

local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

@[simp] theorem down_substitution (m n: ℕ) (g: utlc): (↓m)[n:=g] = if m < n then ↓m else if m = n then g else ↓(m-1) :=
by simp[has_substitution.substitution]

@[simp] theorem lambda_substitution (f: utlc) (n: ℕ) (g: utlc): (Λ f)[n:=g] = Λ f[n+1:=g ↑¹ 0] :=
by simp[has_substitution.substitution]

@[simp] theorem dot_substitution (f f': utlc) (n: ℕ) (g: utlc): (f·f')[n:=g] = f[n:=g]·f'[n:=g] :=
by simp[has_substitution.substitution]

@[simp] theorem substitution_notation (f: utlc) (n: ℕ) (g: utlc): f.substitution n g = f[n:=g] := rfl
end

theorem notation_induction_on (p: utlc → Prop): Π (f: utlc)
  (down: Π n, p ↓n)
  (lambda: Π f (ih: p f), p (Λ f))
  (dot: Π f g (ih_f: p f) (ih_g: p g), p (f·g)),
  (p f)
| (↓n) := λ hn _ _, hn n
| (Λ f) := λ hn hl hd, hl f (notation_induction_on f hn hl hd)
| (f·g) := λ hn hl hd, hd f g (notation_induction_on f hn hl hd) (notation_induction_on g hn hl hd)

def notation_cases_on (p: utlc → Sort*): Π (f: utlc)
  (down: Π n, p ↓n)
  (lambda: Π f, p (Λ f))
  (dot: Π f g, p (f·g)),
  (p f)
| (↓n) := λ hn _ _, hn n
| (Λ f) := λ _ hl _, hl f
| (f·g) := λ _ _ hd, hd f g


def simp_rec {α: Type} (down: ℕ → α) (lambda: utlc → α → α) (dot: utlc → utlc → α → α → α): utlc → α
| (↓n) := down n
| (Λ f) := lambda f (simp_rec f)
| (f·g) := dot f g (simp_rec f) (simp_rec g)

@[simp] theorem simp_rec_down {α: Type} (down: ℕ → α) (lambda: utlc → α → α) (dot: utlc → utlc → α → α → α) (n: ℕ):
  simp_rec down lambda dot (↓n) = down n := by simp[simp_rec]

@[simp] theorem simp_rec_lambda {α: Type} (down: ℕ → α) (lambda: utlc → α → α) (dot: utlc → utlc → α → α → α) (f: utlc):
  simp_rec down lambda dot (Λ f) = lambda f (simp_rec down lambda dot f) := by simp[simp_rec]
  
@[simp] theorem simp_rec_dot {α: Type} (down: ℕ → α) (lambda: utlc → α → α) (dot: utlc → utlc → α → α → α) (f g: utlc):
  simp_rec down lambda dot (f·g) =  dot f g (simp_rec down lambda dot f) (simp_rec down lambda dot g) := by simp[simp_rec]

instance is_lambda_decidable (f: utlc): decidable (is_lambda f) :=
begin
  induction f using lambda_calculus.utlc.notation_cases_on;
  unfold is_lambda;
  apply_instance
end

end utlc
end lambda_calculus