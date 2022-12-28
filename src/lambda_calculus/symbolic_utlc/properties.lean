import lambda_calculus.symbolic_utlc.basic

namespace symbolic_utlc

def shift : symbolic_utlc → ℕ → ℕ → symbolic_utlc :=
begin
  intros f Δ n,
  apply underlying_rec_on f,
  exact (λfc c, ◾fc),
  exact (λm, if m < n then ↓m else ↓(m + Δ)),
  exact (λf pf, Λ pf),
  exact (λf g pf pg, pf·pg),
end

-- theorem shift_below (f : symbolic_utlc) (Δ n : ℕ): f.closed_below ≤ n → f.shift Δ n = f :=
-- begin
--   induction f using symbolic_utlc.underlying_induction_on generalizing n,
--   simp [shift, symbolic_utlc.underlying_induction_on],
  
-- end

end symbolic_utlc