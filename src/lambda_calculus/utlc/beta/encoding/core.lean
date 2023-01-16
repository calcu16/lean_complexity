import lambda_calculus.utlc.beta.distance
import complexity.basic
import lambda_calculus.utlc.beta.encoding.basic

namespace lambda_calculus
namespace utlc
namespace β
namespace encoding

def false : utlc := Λ Λ ↓0
def true : utlc := Λ Λ ↓1

instance bool_encoding: complexity.has_encoding distance_model bool :=
  ⟨ ⟨ λ b, ⟨ ite b true false,
     by cases b; simp[true, false, closed_below] ⟩,
     by intros x y; cases x; cases y; simp [false, true]  ⟩ ⟩

instance decidable_encoding (p: Prop): complexity.has_encoding distance_model (decidable p) :=
  ⟨ ⟨ λ dp, ⟨ @ite _ p dp true false,
    by split_ifs; simp[true, false, closed] ⟩,
    by finish ⟩ ⟩

def pair (f g: encoded_data): encoded_data :=
  ⟨ Λ ↓0·f.value·g.value, by simp ⟩

instance prod_encoding {α β: Type*}
  [f: complexity.has_encoding distance_model α]
  [g: complexity.has_encoding distance_model β]:
  complexity.has_encoding distance_model (α × β) :=
  ⟨ ⟨ λ ab, pair (f.value.encode ab.fst) (g.value.encode ab.snd),
      by intros x y; cases x; cases y; simp [pair, and_imp] ⟩ ⟩


def alternative (n m: ℕ) (f: encoded_data): encoded_data := ⟨
  ( λ x, Λ x)^[(m - 1) + 1] (↓(m - 1 - n)·f.value),
begin
  cases m,
  { simp },
  simp,
  split,
  apply show ∀ n (f: utlc), f.closed_below n → ((λ x :utlc, Λ x)^[n] f).closed,
  begin
    intro n,
    induction n,
    { simp },
    intros f hf,
    simp only [function.iterate_succ, function.comp_app,
      n_ih (Λ f) (by simp [hf])],
  end,
  simp,
  apply lt_of_le_of_lt (nat.sub_le _ _) (nat.lt_succ_self _),
  apply show ∀ n (f: utlc), β.reduced f → β.reduced ((λ x :utlc, Λ x)^[n] f),
  begin
    intro n,
    induction n,
    { simp },
    intros f hf,
    simp only [function.iterate_succ, function.comp_app],
    apply n_ih,
    simp,
    apply hf,
  end,
  simp,
end ⟩

namespace either
@[simp] def left: encoded_data → encoded_data := alternative 0 2
@[simp] def right: encoded_data → encoded_data := alternative 1 2
end either

instance sum_encoding {α β: Type*} [f: complexity.has_encoding distance_model α] [g: complexity.has_encoding distance_model β]:
  complexity.has_encoding distance_model (α ⊕ β) := ⟨ ⟨ λ ab,
    sum.elim (either.left ∘ f.value.encode) (either.right ∘ g.value.encode) ab,
    by intros a b; cases a; cases b; simp [alternative] ⟩ ⟩

end encoding
end β
end utlc
end lambda_calculus