import lambda_calculus.notation
import tactic.linarith

universes u

@[derive decidable_eq]
inductive utlc : Type
| index : ℕ → utlc
| lambda : utlc → utlc
| application (f g : utlc) : utlc

@[pattern] instance : has_index utlc := ⟨ utlc.index ⟩
@[pattern] instance : has_lambda utlc := ⟨ utlc.lambda ⟩
@[pattern] instance : has_apply utlc := ⟨ utlc.application ⟩
attribute [pattern] has_index.index has_apply.apply has_lambda.lambda

instance : inhabited utlc := ⟨ utlc.index 0 ⟩

namespace utlc

@[simp] theorem ne_index_lambda (n : ℕ) (f: utlc) : ↓n ≠ Λ f :=
by apply utlc.no_confusion
@[simp] theorem ne_index_application (n : ℕ) (f g : utlc) : ↓n ≠ f·g:=
by apply utlc.no_confusion
@[simp] theorem ne_lambda_index (f : utlc) (n : ℕ) : Λ f ≠ ↓n :=
by apply utlc.no_confusion
@[simp] theorem ne_lambda_application (f g h: utlc): Λ f ≠ g·h :=
by apply utlc.no_confusion
@[simp] theorem ne_application_index (f g: utlc) (n : ℕ) : f·g ≠ ↓n :=
by apply utlc.no_confusion
@[simp] theorem ne_application_lambda (f g h: utlc) : f·g ≠ Λ h :=
by apply utlc.no_confusion

@[simp] theorem index_eq_index {n m : ℕ}: (↓n : utlc) = ↓m ↔ n = m :=
begin
  split,
  intro p,
  exact utlc.no_confusion p (assume neq, neq),
  intro p,
  rw [p]
end
@[simp] theorem lambda_eq_lambda {f g : utlc}: Λ f = Λ g ↔ f = g :=
begin
  split,
  intro p,
  exact utlc.no_confusion p (assume neq, neq),
  intro p,
  rw [p]
end
@[simp] theorem application_eq_application {f f' g g': utlc}: f·g = f'·g' ↔ f = f' ∧ g = g' :=
begin
  split,
  intros p,
  exact utlc.no_confusion p (assume feq geq, and.intro feq geq),
  intro p,
  simp [p]
end

def repr: utlc → bool → string
| (↓n) := λ parens, "↓" ++ nat.repr n
| (Λ f) := λ parens, (ite parens "(" "") ++ "Λ " ++ (repr f false) ++ (ite parens ")" "")
| (f·g) := λ parens, (ite parens "(" "") ++ (repr f false) ++ "·" ++ (repr g true) ++ (ite parens ")" "")

instance : has_repr utlc := ⟨ λ f, repr f false ⟩

@[simp] theorem down_notation {n : ℕ}: index n = ↓ n := by refl
@[simp] theorem lambda_notation {f : utlc}: f.lambda = Λ f  := by refl
@[simp] theorem dot_notation {f g : utlc}: f.application g = f · g := by refl

@[simp] theorem below_lambda (f: utlc): (Λ f).sizeof = 1 + f.sizeof :=
begin
  rw [← lambda_notation],
  unfold_wf,
end

@[simp] theorem below_application (f g: utlc): (f·g).sizeof = 1 + f.sizeof + g.sizeof :=
begin
  rw [← dot_notation],
  unfold_wf,
end

def size : utlc → ℕ
| (↓ _) := 1
| (Λ f) := f.size + 1
| (f · g) := f.size + g.size + 1

theorem size_pos ( f : utlc ): 0 < size f := by
{ cases f, all_goals { simp[size] }  }

def uses : utlc → ℕ → ℕ
| (↓ m) := λ n, if m = n then 1 else 0
| (Λ f) := λ n, uses f (n + 1)
| (f · g) := λ n, uses f n + uses g n

theorem apply_induction_on (p: utlc → Prop): Π (f: utlc)
  (index: Π n, p ↓n)
  (lambda: Π x (hx: p x), p (Λ x))
  (index_apply : Π n x (hn: p ↓n) (hx: p x), p (↓n·x))
  (lambda_apply: Π x y (hx: p x) (hx': p (Λ x)) (hy: p y), p ((Λ x)·y))
  (apply_apply: Π x y z (hx: p x) (hy: p y) (hxy: p (x·y)) (hz: p z), p ((x·y)·z)),
  (p f)
| (↓n) := begin
  intros hn hx hnx hxy hxyz,
  apply hn,
end
| (Λ x) := begin
  intros hn hx hnx hxy hxyz,
  apply hx,
  apply apply_induction_on x hn hx hnx hxy hxyz,
end
| (↓n·x) := begin
  intros hn hx hnx hxy hxyz,
  apply hnx,
  apply hn,
  apply apply_induction_on x hn hx hnx hxy hxyz,
end
| ((Λ x)·y) := begin
  intros hn hx hnx hxy hxyz,
  apply hxy,
  apply apply_induction_on x hn hx hnx hxy hxyz,
  apply apply_induction_on (Λ x) hn hx hnx hxy hxyz,
  apply apply_induction_on y hn hx hnx hxy hxyz,
end
| ((x·y)·z) := begin
  intros hn hx hnx hxy hxyz,
  apply hxyz,
  apply apply_induction_on x hn hx hnx hxy hxyz,
  apply apply_induction_on y hn hx hnx hxy hxyz,
  apply apply_induction_on (x·y) hn hx hnx hxy hxyz,
  apply apply_induction_on z hn hx hnx hxy hxyz,
end

end utlc
