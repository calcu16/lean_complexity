import lambda_calculus.notation
import lambda_calculus.symbolic_utlc.basic

namespace symbolic_utlc


def false : symbolic_utlc.combinator :=
begin
  unfold combinator,
  refine ⟨Λ Λ ↓0, _⟩,
  apply nat.eq_zero_of_le_zero,
  simp,
end

def true : symbolic_utlc.combinator :=
begin
  unfold combinator,
  refine ⟨Λ Λ ↓1, _⟩,
  apply nat.eq_zero_of_le_zero,
  simp,
end

end symbolic_utlc