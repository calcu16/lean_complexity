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

def alternative {n m: ℕ} (h: n < m) (f: encoded_data): encoded_data := ⟨
  ( λ x, Λ x)^[m] (↓n·f.value),
    begin
      split,
      { cases nat.exists_eq_add_of_le (nat.succ_le_of_lt h) with y h,
        rw [h, add_comm, function.iterate_add_apply],
        clear h h,
        apply show ∀ y (f: utlc), f.closed → ((λ x :utlc, Λ x)^[y] f).closed,
        begin
          intro y,
          induction y,
          { simp },
          intros f hf,
          simp [function.iterate_succ', function.comp_app,
            lambda_reduced_iff, closed, closed_below, add_zero,
            closed_below_mono (y_ih f hf)],
        end,
        apply show ∀ n (f: utlc), f.closed_below n → ((λ x :utlc, Λ x)^[n] f).closed,
        begin
          intro n,
          induction n,
          { simp },
          intros f hf,
          simp only [function.iterate_succ, function.comp_app,
            n_ih (Λ f) (by simp [hf])],
        end,
        simp [nat.lt_succ_self],
      },
      clear h,
      induction m,
      { simp },
      simp only [function.iterate_succ', function.comp_app, lambda_reduced_iff, m_ih]
    end ⟩

namespace either
@[simp] def left: encoded_data → encoded_data := alternative (show 0 < 2, by simp)
@[simp] def right: encoded_data → encoded_data := alternative (show 1 < 2, by simp)
end either

instance sum_encoding {α β: Type*} [f: complexity.has_encoding distance_model α] [g: complexity.has_encoding distance_model β]:
  complexity.has_encoding distance_model (α ⊕ β) := ⟨ ⟨ λ ab,
    sum.elim (either.left ∘ f.value.encode) (either.right ∘ g.value.encode) ab,
    by intros a b; cases a; cases b; simp [alternative] ⟩ ⟩

end encoding
end β
end utlc
end lambda_calculus