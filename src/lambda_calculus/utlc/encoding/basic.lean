import lambda_calculus.utlc.basic
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.beta.church_rosser

namespace lambda_calculus
namespace utlc

@[simp] def encoding_invariant {α: Type} (f: α → utlc) :=
  ∀ {a : α}, closed (f a) ∧ β.reduced (f a) ∧ ∀ {b: α}, (f a) = (f b) → a = b

def encoding (α: Type) := { encode: α → utlc //  encoding_invariant encode }

class has_encoding (α: Type) := (value: encoding α)

def encode {α: Type*} [f: has_encoding α]: α → utlc := has_encoding.value.1

namespace encoding
theorem is_closed {α: Type*} [f: has_encoding α] (a :α): (encode a).closed := f.value.2.left

theorem is_closed_below {α: Type*} [f: has_encoding α] (a: α) (n: ℕ): (encode a).closed_below n := closed_below_mono f.value.2.left (nat.zero_le _)

theorem is_β_reduced {α: Type*} [f: has_encoding α] (a :α): β.reduced (encode a) := f.value.2.right.left

theorem is_inj {α: Type*} [f: has_encoding α] {a b: α}: (encode a) = (encode b) → a = b := f.value.2.right.right

theorem is_inj_iff {α: Type*} [f: has_encoding α] {a b: α}: (encode a) = (encode b) ↔ a = b :=
  ⟨ is_inj, by finish ⟩

theorem is_equiv_inj {α: Type*} [f: has_encoding α] {a b: α}: (encode a) ≡β (encode b) → a = b :=
  λ p, is_inj (β.reduced_equiv_inj (is_β_reduced _) (is_β_reduced _) p)

@[simp] theorem is_equiv_inj_iff {α: Type*} [f: has_encoding α] {a b: α}: (encode a) ≡β (encode b) ↔ a = b :=
  ⟨ is_equiv_inj, by finish ⟩

def true : utlc := Λ Λ ↓0
def false : utlc := Λ Λ ↓1   

instance bool_encoding: has_encoding bool := ⟨ ⟨ λ b, if b then true else false, by simp [reduced, true, false] ⟩ ⟩

instance decidable_encoding (p: Prop): has_encoding (decidable p) := ⟨ ⟨ λ dp, @ite _ p dp true false, by
  { intro, split_ifs, all_goals { simp [reduced, true, false] } } ⟩ ⟩

@[simp] def curry: list utlc → utlc → utlc
| [] := λ f, f
| (x :: xs) := λ f, curry xs (f·x)

def tuple: list utlc → utlc := λ xs, Λ curry xs ↓0

@[simp] def pair (f g: utlc): utlc := tuple [f, g]

instance prod_encoding {α β: Type*} [f: has_encoding α] [g: has_encoding β]:
  has_encoding (α × β) := ⟨ ⟨ λ a, pair (encode a.fst) (encode a.snd),
    begin
      simp [tuple, reduced, is_closed_below],
      intros a b,
      refine ⟨ ⟨is_β_reduced a, is_β_reduced b ⟩, _⟩,
      intros c d hac hbd,
      exact ⟨ is_inj hac, is_inj hbd ⟩,
    end ⟩ ⟩

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
        refine ⟨ is_β_reduced _, _ ⟩,
        intro b,
        exact is_inj,
      }
    end ⟩ ⟩

end encoding
end utlc
end lambda_calculus