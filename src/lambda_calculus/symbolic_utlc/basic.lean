import lambda_calculus.notation
import lambda_calculus.utlc.basic

universe u

namespace hidden

inductive symbolic_utlc: ℕ → Type
| symbol : symbolic_utlc 0 → symbolic_utlc 0
| index : Π n, symbolic_utlc (n+1)
| lambda : Π {n}, symbolic_utlc n → symbolic_utlc n.pred
| application : Π {n m}, symbolic_utlc n → symbolic_utlc m → symbolic_utlc (max n m)

namespace symbolic_utlc
@[simp]
def closed_below: Π{n}, symbolic_utlc n → ℕ := λ n _, n

@[simp]
def type_index: Π{n}, symbolic_utlc n → ℕ
| _ (symbol _) := 0
| _ (index _) := 1
| _ (lambda _) := 2
| _ (application _ _) := 3

end symbolic_utlc
end hidden 

inductive symbolic_utlc: Type
| value : Π{n}, hidden.symbolic_utlc n → symbolic_utlc

namespace symbolic_utlc

def closed_below: symbolic_utlc → ℕ
| (value va) := va.closed_below

def combinator :=
  { value : symbolic_utlc // closed_below value = 0 }

namespace combinator

def mk (v: symbolic_utlc) (pf: v.closed_below = 0) : combinator := ⟨v, pf⟩

def mk' (v: hidden.symbolic_utlc 0): combinator := ⟨⟨v⟩, by simp[closed_below]⟩

def value:combinator → symbolic_utlc
| ⟨f, pf⟩ := f

def hidden_value: combinator → hidden.symbolic_utlc 0 :=
begin
  intro ca,
  cases ca with a pf,
  cases a with na va,
  unfold closed_below at pf,
  unfold hidden.symbolic_utlc.closed_below at pf,
  rw ←pf,
  apply va,
end

end combinator

def symbol: combinator → symbolic_utlc :=
begin
  intro ca,
  cases ca with a pf,
  cases a with na va,
  apply symbolic_utlc.value,
  apply hidden.symbolic_utlc.symbol,
  simp [closed_below, hidden.symbolic_utlc.closed_below] at pf,
  apply cast (show hidden.symbolic_utlc na = hidden.symbolic_utlc 0, by rw[pf]) va,
end

def index (n : ℕ): symbolic_utlc := symbolic_utlc.value (hidden.symbolic_utlc.index n)

def lambda: symbolic_utlc → symbolic_utlc
| (value va) := symbolic_utlc.value (hidden.symbolic_utlc.lambda va)

def application: symbolic_utlc → symbolic_utlc → symbolic_utlc
| (value va) (value vb) := symbolic_utlc.value (hidden.symbolic_utlc.application va vb)

def type_index: symbolic_utlc → ℕ
| (value va) := hidden.symbolic_utlc.type_index va

def strip: symbolic_utlc → (option symbolic_utlc × option symbolic_utlc)
| (value va) := begin
  cases va with va _ _ va _ _ va vb,
  exact ⟨option.some (symbolic_utlc.value va), option.none⟩,
  exact ⟨option.none, option.none⟩,
  exact ⟨option.some (symbolic_utlc.value va), option.none⟩,
  exact ⟨option.some (symbolic_utlc.value va), option.some (symbolic_utlc.value vb)⟩,
end

lemma strip_application {f g : symbolic_utlc}: (application f g).strip = (option.some f, option.some g) :=
begin
  cases f with nf vf,
  cases g with ng vg,
  simp [application, strip],
  refl,
end 
  
end symbolic_utlc

instance : has_index symbolic_utlc := ⟨ symbolic_utlc.index ⟩
instance : has_lambda symbolic_utlc := ⟨ symbolic_utlc.lambda ⟩
instance : has_apply symbolic_utlc := ⟨ symbolic_utlc.application ⟩
instance : has_symbol symbolic_utlc.combinator symbolic_utlc := ⟨ symbolic_utlc.symbol ⟩

instance : inhabited symbolic_utlc := ⟨ symbolic_utlc.index 0 ⟩

namespace symbolic_utlc

theorem down_notation {n : ℕ}: index n = ↓ n := by refl
theorem lambda_notation {f : symbolic_utlc}: f.lambda = Λ f  := by refl
theorem dot_notation {f g : symbolic_utlc}: f.application g = f · g := by refl 
theorem square_notation {fc : symbolic_utlc.combinator}: symbol fc = ◾fc := by refl

@[simp] theorem ne_symbol_index (fc: combinator) (n : ℕ) : (◾fc:symbolic_utlc) ≠ ↓n :=
begin
  intro p,
  have p := congr_arg type_index p,
  rw [← down_notation, ← square_notation, index, symbol] at p,
  cases fc with f pf,
  cases f with nf vf,
  simp only [type_index] at p,
  simp at p,
  contradiction
end

@[simp] theorem ne_symbol_lambda (fc: combinator) (g : symbolic_utlc) : ◾fc ≠ Λ g :=
begin
  intro p,
  have p := congr_arg type_index p,
  rw [← lambda_notation, ← square_notation, symbol] at p,
  cases fc with f pf,
  cases f with nf vf,
  cases g with ng vg,
  simp only [type_index, lambda] at p,
  simp at p,
  contradiction
end

@[simp] theorem ne_symbol_application (fc: combinator) (g g': symbolic_utlc) : ◾fc ≠ g·g' :=
begin
  intro p,
  have p := congr_arg type_index p,
  rw [← dot_notation, ← square_notation, symbol] at p,
  cases fc with f pf,
  cases f with nf vf,
  cases g with ng vg,
  cases g' with ng' vg',
  simp only [type_index, application] at p,
  simp at p,
  contradiction
end

@[simp] theorem ne_index_symbol (n : ℕ) (fc: combinator): (↓n:symbolic_utlc) ≠ ◾fc := ne.symm (ne_symbol_index _ _)
@[simp] theorem ne_index_lambda (n : ℕ) (f: symbolic_utlc) : ↓n ≠ Λ f :=
begin
  intro p,
  have p := congr_arg type_index p,
  rw [← down_notation, ← lambda_notation, index] at p,
  cases f with nf vf,
  simp only [type_index, lambda] at p,
  simp at p,
  contradiction
end

@[simp] theorem ne_index_application (n : ℕ) (g g': symbolic_utlc) : ↓n ≠ g·g' :=
begin
  intro p,
  have p := congr_arg type_index p,
  rw [← down_notation, ← dot_notation, index] at p,
  cases g,
  cases g',
  simp only [type_index, application] at p,
  simp at p,
  contradiction
end

@[simp] theorem ne_lambda_symbol (g : symbolic_utlc) (fc: combinator): Λ g ≠ ◾fc := ne.symm (ne_symbol_lambda _ _)
@[simp] theorem ne_lambda_index (f: symbolic_utlc) (n : ℕ)  : Λ f ≠ ↓n := ne.symm (ne_index_lambda _ _)

@[simp] theorem ne_lambda_application (f g g': symbolic_utlc) : Λ f ≠ g·g' :=
begin
  intro p,
  have p := congr_arg type_index p,
  rw [← lambda_notation, ← dot_notation] at p,
  cases f,
  cases g,
  cases g',
  simp only [type_index, lambda, application] at p,
  simp at p,
  contradiction
end

@[simp] theorem ne_application_symbol (g g': symbolic_utlc) (fc: combinator): g·g' ≠ ◾fc := ne.symm (ne_symbol_application _ _ _)
@[simp] theorem ne_application_index (g g': symbolic_utlc) (n : ℕ) : g·g' ≠ ↓n := ne.symm (ne_index_application _ _ _)
@[simp] theorem ne_application_lambda (g g' f: symbolic_utlc) :  g·g' ≠ Λ f := ne.symm (ne_lambda_application _ _ _)

lemma symbol_inj {f g : symbolic_utlc} {pf : closed_below f = 0} {pg : closed_below g = 0}:
  (symbol ⟨f, pf⟩ = symbol ⟨g, pg⟩) → f = g :=
begin
  intro p,
  cases hf: f with nf vf,
  cases hg: g with ng vg,
  have p := congr_arg strip p,
  simp only [hf, hg, symbol] at p,
  simp only [hf, hg, closed_below] at pf pg,
  simp only [strip] at p,
  simp at p,
  have p := congr_arg value p,
  have ef : ∀ c, value (cast c vf) = value vf,
  { simp, intro, simp [closed_below] at pf, apply pf.symm },
  rw [ef] at p,
  have eg : ∀ c, value (cast c vg) = value vg,
  { simp, intro, simp [closed_below] at pg, apply pg.symm },
  rw [eg] at p,
  assumption,
end

theorem symbol_cancel {fc gc: combinator}:
  (◾fc:symbolic_utlc) = ◾gc ↔ fc = gc :=
begin
  split,
  cases fc,
  cases gc,
  simp [←square_notation],
  apply symbol_inj,
  intro p,
  rw [p],
end

@[simp] theorem index_cancel {n m : ℕ}: (↓n:symbolic_utlc) = ↓m ↔ n = m :=
begin
  split,
  intro p,
  simp [← down_notation, index] at p,
  apply p.left,
  intro p,
  rw [p]
end

@[simp] theorem lambda_cancel {f g : symbolic_utlc}: Λ f = Λ g ↔ f = g :=
begin
  split,
  intro p,
  have p := congr_arg strip p,
  simp only [← lambda_notation] at p,
  cases hf: f,
  cases hg: g,
  simp only [hf, hg, lambda, strip] at p,
  rw [←hf, ←hg] at p,
  rw [←hf, ←hg],
  simp at p,
  assumption,
  intro p,
  rw [p],
end

@[simp] theorem application_cancel {f f' g g': symbolic_utlc}: (f·f') = (g·g') ↔ f=g ∧ f'=g' :=
begin
  split,
  swap,
  intro p,
  cases p with pf pg,
  rw [pf, pg],
  intro p,
  have p := congr_arg strip p,
  simp [← dot_notation, strip_application] at p,
  assumption
end

def underlying_rec_on {p: symbolic_utlc → Sort u}: ∀ (f: symbolic_utlc),
  (∀ (fc: combinator), p (symbolic_utlc.combinator.value fc) → (p ◾fc)) → 
   (∀ n, p ↓n) → 
  (∀ x, p x → p (Λ x)) →
  (∀ x y, p x → p y → p (x·y)) →
  p f
| (value (hidden.symbolic_utlc.symbol f)) := begin
  intros ps pi pl pa,
  have x := ps,
  specialize x (combinator.mk' f),
  rw [← square_notation, combinator.mk', combinator.value, symbol] at x,
  dsimp at x,
  apply x,
  apply underlying_rec_on ⟨f⟩ ps pi pl pa,
end
| (value (hidden.symbolic_utlc.index n)) := λ ps pi pl pa, pi n
| (value (hidden.symbolic_utlc.lambda f)) := begin
  intros ps pi pl pa,
  apply pl ⟨f⟩,
  apply underlying_rec_on ⟨f⟩ ps pi pl pa
end
| (value (hidden.symbolic_utlc.application f g)) := begin
  intros ps pi pl pa,
  apply pa ⟨f⟩ ⟨g⟩,
  apply underlying_rec_on ⟨f⟩ ps pi pl pa,
  apply underlying_rec_on ⟨g⟩ ps pi pl pa
end

-- theorem underlying_rec_on_symbol {p: symbolic_utlc → Sort u}
--   (fc: combinator)
--   (ps: Π (fc: combinator) (hx: p (symbolic_utlc.combinator.value fc)), (p ◾fc))
--   (pi: Π n, p ↓n)
--   (pl: Π x (hx: p x), p (Λ x))
--   (pa: Π x y (hx: p x) (hy: p y), p (x·y)):
--   underlying_rec_on (symbol fc) ps pi pl pa = ps fc (underlying_rec_on fc.value ps pi pl pa) :=
-- begin
-- -- end
-- set_option trace.check true

-- theorem underlying_rec_on_lambda {p: symbolic_utlc → Sort u}
--   (f: symbolic_utlc)
--   (ps: ∀ (fc: combinator), (p (symbolic_utlc.combinator.value fc)) → (p ◾fc))
--   (pi: ∀ n, p ↓n)
--   (pl: ∀ x, p x → p (Λ x))
--   (pa: ∀ x y, p x → p y → p (x·y)):
--   @underlying_rec_on p (Λ f) ps pi pl pa = pl f (@underlying_rec_on p f ps pi pl pa) :=
-- begin
--   rw [←lambda_notation],

-- end


lemma underlying_induction_on {p: symbolic_utlc → Prop}: Π (f: symbolic_utlc)
  (symbol: Π (fc: combinator) (hx: p (symbolic_utlc.combinator.value fc)), (p ◾fc))
  (index: Π n, p ↓n)
  (lambda: Π x (hx: p x), p (Λ x))
  (apply: Π x y (hx: p x) (hy: p y), p (x·y)),
  p f := λ f ps pi pl pa, underlying_rec_on f ps pi pl pa

@[simp]
theorem closed_below_index_le {n: ℕ}: (↓n : symbolic_utlc).closed_below = (n+1) :=
begin
  rw [show ↓n = index n, by refl],
  simp [index, closed_below, hidden.symbolic_utlc.closed_below],
end

@[simp]
theorem closed_below_lambda_le {a: symbolic_utlc} {n: ℕ}: a.closed_below ≤ n + 1 → (Λ a).closed_below ≤ n :=
begin
  rw [show Λ a = lambda a, by refl],
  cases a with na,
  simp [lambda, closed_below],
  cases na,
  simp,
  simp [nat.pred_succ, nat.succ_eq_add_one],
end

@[simp]
theorem closed_below_application_le {a b: symbolic_utlc} {n: ℕ}: a.closed_below ≤ n → b.closed_below ≤ n → (a·b).closed_below ≤ n :=
begin
  rw [show a·b = application a b, by refl],
  cases a,
  cases b,
  simp [application, closed_below],
  exact and.intro,
end

attribute [simp] dot_notation square_notation lambda_notation down_notation

end symbolic_utlc