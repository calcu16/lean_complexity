import lambda_calculus.utlc.beta.distance
import complexity.basic
import lambda_calculus.utlc.beta.encoding.basic

namespace lambda_calculus
namespace utlc
namespace β
namespace encoding

variable {et: encoding_type}

def false : utlc := Λ Λ ↓0
def true : utlc := Λ Λ ↓1

instance bool_encoding (et: encoding_type): complexity.has_encoding (distance_model et) bool :=
  ⟨ ⟨ λ b, ⟨ ite b true false,
     by cases b; simp[true, false, closed_below] ⟩,
     by intros x y; cases x; cases y; simp [false, true]  ⟩ ⟩

instance decidable_encoding (p: Prop) (et: encoding_type): complexity.has_encoding (distance_model et) (decidable p) :=
  ⟨ ⟨ λ dp, ⟨ @ite _ p dp true false,
    by split_ifs; simp[true, false, closed] ⟩,
    by finish ⟩ ⟩

def pair (f g: encoded_data et): encoded_data et :=
  ⟨ Λ ↓0·f.value·g.value, by simp ⟩

instance prod_encoding {α β: Type*} (et: encoding_type)
  [f: complexity.has_encoding (distance_model et) α]
  [g: complexity.has_encoding (distance_model et) β]:
  complexity.has_encoding (distance_model et) (α × β) :=
  ⟨ ⟨ λ ab, pair (f.value.encode ab.fst) (g.value.encode ab.snd),
      by intros x y; cases x; cases y; simp [pair, and_imp] ⟩ ⟩

@[simp]
def alternative (n m: ℕ) (args: list (encoded_data et)): (encoded_data et) := ⟨
  ( λ x, Λ x)^[m + 1] (list.foldl (λ x (y: encoded_data et), x · y.value) (↓(m - n)) args),
begin
  simp,
  split,
  apply show ∀ n (f: utlc), f.closed_below n → ((λ x :utlc, Λ x)^[n] f).closed,
  begin
    intro n,
    induction n,
    { simp [closed] },
    intros f hf,
    simp only [function.iterate_succ, function.comp_app,
      n_ih (Λ f) (by simp [hf])],
  end,
  simp,
  apply show ∀ n (f: utlc) xs, f.closed_below n → closed_below (list.foldl (λ x (y: encoded_data et), x·y.value) f xs) n,
  begin
    intros n f xs,
    induction xs generalizing f,
    { simp [closed] },
    simp,
    intro h,
    apply xs_ih,
    simp [h],
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
  apply show ∀ (f: utlc) xs, β.reduced f → ¬ f.is_lambda → β.reduced (list.foldl (λ x (y: encoded_data et), x·y.value) f xs),
  begin
    intros f xs,
    induction xs generalizing f,
    { simp, apply function.const },
    simp,
    intros p q,
    apply xs_ih,
    simp,
    exact ⟨ q, p ⟩,
    simp,
  end,
  simp,
  simp,
end
  ⟩

namespace either
@[simp] def left: encoded_data et → encoded_data et := λ x, alternative 0 2 [x]
@[simp] def right: encoded_data et → encoded_data et := λ x, alternative 1 2 [x]
end either

instance sum_encoding {α β: Type*} [f: complexity.has_encoding (distance_model et) α] [g: complexity.has_encoding (distance_model et) β]:
  complexity.has_encoding (distance_model et) (α ⊕ β) := ⟨ ⟨ λ ab,
    sum.elim (either.left ∘ f.value.encode) (either.right ∘ g.value.encode) ab,
    by intros a b; cases a; cases b; simp [alternative] ⟩ ⟩

end encoding
end β
end utlc
end lambda_calculus