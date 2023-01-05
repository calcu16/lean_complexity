import lambda_calculus.utlc.basic
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.beta.distance
import lambda_calculus.utlc.beta.church_rosser

namespace lambda_calculus
namespace utlc

local attribute [simp] closed closed_below
local attribute [simp] β.normal_iteration β.strategic_reduction_step
local attribute [simp] reduced substitution shift shift_substitution_index

@[simp] def encoding_invariant {α: Type} (f: α → utlc) :=
  ∀ {a : α}, closed (f a) ∧ β.reduced (f a) ∧ ∀ {b: α}, (f a) = (f b) → a = b

def encoding (α: Type) := { encode: α → utlc //  encoding_invariant encode }

class has_encoding (α: Type) := (value: encoding α)

def encode {α: Type*} [f: has_encoding α]: α → utlc := has_encoding.value.1

namespace encoding
section
@[simp] theorem is_closed {α: Type*} [f: has_encoding α] (a :α): (encode a).closed := f.value.2.left

@[simp]  theorem is_closed_below {α: Type*} [f: has_encoding α] (a: α) (n: ℕ): (encode a).closed_below n := closed_below_mono f.value.2.left (nat.zero_le _)

@[simp]  theorem is_β_reduced {α: Type*} [f: has_encoding α] (a :α): β.reduced (encode a) := f.value.2.right.left

theorem is_inj {α: Type*} [f: has_encoding α] {a b: α}: (encode a) = (encode b) → a = b := f.value.2.right.right

@[simp]  theorem is_inj_iff {α: Type*} [f: has_encoding α] {a b: α}: (encode a) = (encode b) ↔ a = b :=
  ⟨ is_inj, by finish ⟩

theorem is_equiv_inj {α: Type*} [f: has_encoding α] {a b: α}: (encode a) ≡β (encode b) → a = b :=
  λ p, is_inj (β.reduced_equiv_inj (is_β_reduced _) (is_β_reduced _) p)

@[simp] theorem is_equiv_inj_iff {α: Type*} [f: has_encoding α] {a b: α}: (encode a) ≡β (encode b) ↔ a = b :=
  ⟨ is_equiv_inj, by finish ⟩

@[simp] theorem shift_identity {α: Type*} [has_encoding α] {a : α}: ∀ {n}, (encode a) ↑¹ n = (encode a) :=
  shift_of_closed (is_closed _)

section
local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

@[simp] theorem substitution_identtiy {α: Type*} [ha: has_encoding α] {a : α}: ∀ {n g}, (encode a)[n:=g] = (encode a) :=
  substitution_identity_of_closed (is_closed _)
end
end -- usefule theorems

def identity: utlc := Λ ↓0

def pipe: utlc := Λ Λ ↓0·↓1

def compose: utlc := Λ Λ Λ ↓2·(↓1·↓0)

theorem identity_distance_le (f: utlc): β.distance_le 1 (identity·f) f :=
by { apply β.distance_le_of_normal_iteration 1, simp [identity] }

theorem pipe_distance_le {f x: utlc}:
  β.distance_le 2 (pipe·x·f) (f·x) :=
begin
  apply β.distance_le_of_normal_iteration,
  simp [pipe],
end

theorem compose_distance_le (f g x: utlc):
  β.distance_le 3 (compose·f·g·x) (f·(g·x)) :=
begin
  apply β.distance_le_of_normal_iteration,
  simp [compose],
  rw [← shift_comm],
  simp [shift_substitution_index],
end

def false : utlc := Λ Λ ↓0
def true : utlc := Λ Λ ↓1

theorem false_distance_le (f g: utlc): β.distance_le 2 (false·f·g) g :=
by { apply β.distance_le_of_normal_iteration 2, simp [false] }

theorem true_distance_le (f g: utlc): β.distance_le 2 (true·f·g) f :=
by { apply β.distance_le_of_normal_iteration 2, simp [true] }

instance bool_encoding: has_encoding bool := ⟨ ⟨ λ b, if b then true else false, by simp [reduced, true, false] ⟩ ⟩

theorem bool_distance_le (b: bool) (f g: utlc): β.distance_le 2 ((encode b)·f·g) (if b then f else g) :=
begin
  simp [encode, has_encoding.value],
  split_ifs,
  apply true_distance_le,
  apply false_distance_le,
end

instance decidable_encoding (p: Prop): has_encoding (decidable p) := ⟨ ⟨ λ dp, @ite _ p dp true false, by
  { intro, split_ifs, all_goals { simp [reduced, true, false] } } ⟩ ⟩

theorem decidable_distance_le {p: Prop} (dp: decidable p) (f g: utlc): β.distance_le 2 ((encode dp)·f·g) (@ite _ p dp f g) :=
begin
  simp [encode, has_encoding.value],
  split_ifs,
  apply true_distance_le,
  apply false_distance_le,
end

namespace tuple
@[simp] def build: list utlc → utlc → utlc
| [] := λ f, f
| (x :: xs) := λ f, build xs (f·(x ↑¹ 0))
end tuple

def tuple: list utlc → utlc := λ xs, Λ tuple.build xs ↓0

def pair (f g: utlc): utlc := tuple [f, g]

def curry: utlc := Λ Λ Λ ↓2·(pair ↓1 ↓0)
@[simp] theorem curry_closed : curry.closed := by simp [curry, pair, tuple]
@[simp] theorem curry_closed_below {n: ℕ}: curry.closed_below n := closed_below_mono curry_closed (nat.zero_le _)

def uncurry: utlc := Λ Λ ↓0·↓1
@[simp] theorem uncurry_closed : uncurry.closed := by simp [uncurry]
@[simp] theorem uncurry_closed_below {n: ℕ}: uncurry.closed_below n := closed_below_mono uncurry_closed (nat.zero_le _)

def swap: utlc := Λ ↓0·(Λ Λ Λ ↓0·↓1·↓2)
def fork: utlc := Λ Λ Λ pair (↓2·↓0) (↓1·↓0)
def to_fst: utlc := Λ Λ pair (↓1·↓0) ↓0
def to_snd: utlc := Λ Λ pair (↓0) (↓1·↓0)

instance prod_encoding {α β: Type*} [f: has_encoding α] [g: has_encoding β]:
  has_encoding (α × β) := ⟨ ⟨ λ a, pair (encode a.fst) (encode a.snd),
    begin
      simp [pair, tuple, reduced, is_closed_below],
      intros a b,
      refine ⟨ ⟨is_β_reduced a, is_β_reduced b ⟩, _⟩,
      intros c d hac hbd,
      exact ⟨ hac, hbd ⟩,
    end ⟩ ⟩

theorem uncurry_distance_le {α β: Type*} (f: utlc) (a : α) (b: β) [ha: has_encoding α] [hb: has_encoding β]:
  utlc.β.distance_le 3 (uncurry·f·encode (a, b)) (f·encode a·encode b) :=
begin
  simp [encode, uncurry, pair, tuple, has_encoding.value],
  simp,
  apply utlc.β.distance_le_of_normal_iteration,
  simp,
end

theorem curry_distance_le {α β: Type*} (f: utlc) (a : α) (b: β) [ha: has_encoding α] [hb: has_encoding β]:
  utlc.β.distance_le 3 (curry·f·encode a·encode b) (f·encode (a, b)) :=
begin
  simp [curry, pair, tuple],
  simp,
  apply utlc.β.distance_le_of_normal_iteration,
  simp [encode, has_encoding.value, pair, tuple],
  rw [← shift_comm _ (nat.zero_le _), ← shift_comm _ (nat.zero_le _)],
  simp [shift_substitution_index],
end

theorem swap_distance_le (f g: utlc):
  utlc.β.distance_le 4 (swap·pair f g) (pair g f) :=
begin
  simp [curry, pair, tuple],
  simp,
  apply utlc.β.distance_le_of_normal_iteration,
  simp [encode, has_encoding.value, pair, tuple, swap],
  rw [← shift_comm],
  simp [shift_substitution_index],
end

theorem fork_distance_le (f g x: utlc):
  utlc.β.distance_le 3 (fork·f·g·x) (pair (f·x) (g·x)) :=
begin
  simp [curry, pair, tuple],
  simp,
  apply utlc.β.distance_le_of_normal_iteration,
  simp [encode, has_encoding.value, pair, tuple, fork],
  rw [← shift_comm],
  simp [shift_substitution_index],
  norm_num,
  rw [← shift_comm f],
  rw [← shift_comm (f ↑¹ 0)],
  simp [shift_substitution_index],
  rw [← shift_comm],
  simp [shift_substitution_index],
  all_goals { refl },
end

theorem to_fst_distance_le (f g: utlc):
  utlc.β.distance_le 2 (to_fst·f·g) (pair (f·g) g) :=
begin
  simp [curry, pair, tuple],
  simp,
  apply utlc.β.distance_le_of_normal_iteration,
  simp [encode, has_encoding.value, pair, tuple, to_fst],
  rw [← shift_comm],
  simp [shift_substitution_index],
end

theorem to_snd_distance_le (f g: utlc):
  utlc.β.distance_le 2 (to_snd·f·g) (pair g (f·g)) :=
begin
  simp [curry, pair, tuple],
  simp,
  apply utlc.β.distance_le_of_normal_iteration,
  simp [encode, has_encoding.value, pair, tuple, to_snd],
  rw [← shift_comm],
  simp [shift_substitution_index],
end

theorem fst_distance_le (f g: utlc):
  utlc.β.distance_le 3 (pair f g·true) f  :=
begin
  simp [curry, pair, tuple],
  simp,
  apply utlc.β.distance_le_of_normal_iteration 3,
  simp [encode, has_encoding.value, pair, tuple, true],
end

theorem snd_distance_le (f g: utlc):
  utlc.β.distance_le 3 (pair f g·false) g  :=
begin
  simp [curry, pair, tuple],
  simp,
  apply utlc.β.distance_le_of_normal_iteration 3,
  simp [encode, has_encoding.value, pair, tuple, false],
end

@[simp] def n_abstract: ℕ → utlc → utlc
| 0 := λ x, x
| (n+1) := λ x, Λ n_abstract n x

@[simp] def iterate: ℕ → utlc → utlc → utlc
| 0 := λ f x, x 
| (n+1) := λ f x, f·iterate n f x

def alternative (n m: ℕ) (f: utlc) : utlc := n_abstract m (↓n·f)

namespace either
@[simp] def left: utlc → utlc := alternative 0 2
@[simp] def right: utlc → utlc := alternative 1 2
end either

instance sum_encoding {α β: Type*} [f: has_encoding α] [g: has_encoding β]:
  has_encoding (α ⊕ β) := ⟨ ⟨ λ a,
    sum.elim (either.left ∘ encode) (either.right ∘ encode) a,
    begin
      intros a,
      cases a,
      all_goals {
        simp [sum.elim, alternative, reduced, is_closed_below],
        exact is_β_reduced _,
      }
    end ⟩ ⟩

end encoding
end utlc
end lambda_calculus