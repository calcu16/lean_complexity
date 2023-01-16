import lambda_calculus.utlc.basic
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.beta.encoding.core
import lambda_calculus.utlc.beta.encoding.nat

namespace lambda_calculus
namespace utlc
namespace β
namespace encoding
namespace utlc

def encode_utlc: utlc → encoded_data
| (↓n) := alternative 0 3 (complexity.encode distance_model n)
| (Λ f) := alternative 1 3 (encode_utlc f)
| (f·g) := alternative 2 3 (pair (encode_utlc f) (encode_utlc g))

instance: complexity.has_encoding distance_model utlc := ⟨ ⟨ encode_utlc,
  begin
    intros x y,
    simp only [value_inj],
    induction x generalizing y;
    cases y;
    try { { simp [encode_utlc, alternative, pair, complexity.encode, show 0 ≠ 2, by norm_num] } },
    simp [encode_utlc, alternative, pair, complexity.encode, x_ih],
    simp [encode_utlc, alternative, pair, complexity.encode, x_ih_f, x_ih_g],
  end ⟩ ⟩

end utlc
end encoding
end β
end utlc
end lambda_calculus