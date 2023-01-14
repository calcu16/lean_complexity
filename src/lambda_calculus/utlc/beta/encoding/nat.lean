import lambda_calculus.utlc.beta.distance
import complexity.basic
import lambda_calculus.utlc.beta.encoding.basic

namespace lambda_calculus
namespace utlc
namespace β
namespace encoding
namespace nat

@[reducible] def iterate (f: utlc) (n: ℕ) (g: utlc): utlc := (λ x, f·x)^[n] g

section
local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

@[simp] theorem iterate_substitution {n m: ℕ} {f g x: utlc}:
  (iterate f n g)[m:=x] = (iterate (f[m:=x]) n (g[m:=x])) :=
begin
  induction n;
  simp[iterate, function.iterate_succ'],
  apply n_ih
end

@[simp] theorem iterate_shift {n m: ℕ} {f g: utlc}:
  (iterate f n g) ↑¹ m = (iterate (f ↑¹ m) n (g ↑¹ m)) :=
begin
  induction n,
  all_goals { simp[iterate, function.iterate_succ'] },
  apply n_ih
end
end

instance nat_encoding:
  complexity.has_encoding distance_model ℕ := ⟨ ⟨ λ n,
    ⟨ (Λ Λ iterate (↓1:utlc) n ↓0: utlc),
      begin
        induction n,
        { simp [iterate] },
        simp only [iterate, reduced, lambda_reduced, closed, closed_below,
          zero_add, one_add_one_eq_two] at n_ih,
        simp [function.iterate_succ', iterate, n_ih],
      end
    ⟩,
    begin
      intros x y,
      cases le_total x y;
      cases nat.exists_eq_add_of_le h with z h;
      rw [h];
      clear h;
      simp only [iterate, value_inj, lambda_eq_lambda_iff, self_eq_add_right];
      cases z;
      try { { simp } };
      clear h,
      { induction x,
        { simp [function.iterate_succ'] },
        simp [function.iterate_succ', nat.succ_add, x_ih] },
      { induction y,
        { simp [function.iterate_succ'] },
        simp [function.iterate_succ', nat.succ_add, y_ih], }
    end ⟩ ⟩

end nat
end encoding
end β
end utlc
end lambda_calculus