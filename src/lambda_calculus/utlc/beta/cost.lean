import lambda_calculus.utlc.basic
import lambda_calculus.utlc.reduction
import lambda_calculus.utlc.beta.basic

namespace utlc

def costed_substitution (f : utlc) (n : ℕ) (g : utlc ) :=
  (substitution f n g, f.size + f.uses n * g.size)

@[simp]
def costed_β_reduction : utlc → utlc → ℕ → Prop
| (application (lambda f1) f2) := λ g c, costed_substitution f1 0 f2 = (g, c)
| _ := λ g c, false

end utlc