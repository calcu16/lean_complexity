import lambda_calculus.utlc.basic
import lambda_calculus.notation
import lambda_calculus.symbolic_utlc.basic

namespace symbolic_utlc

def to_utlc (f: symbolic_utlc): utlc :=
begin
  apply underlying_rec_on f,
  { intros fc v, apply v },
  { intro n, exact ↓n },
  { intros f v, exact Λ v },
  { intros f g fv gv, exact fv·gv }
end

def of_utlc: utlc → symbolic_utlc
| (↓n) := ↓n
| (Λ f) := Λ(of_utlc f)
| (f·g) := (of_utlc f)·(of_utlc g)


end symbolic_utlc