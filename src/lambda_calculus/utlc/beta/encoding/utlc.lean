import lambda_calculus.utlc.basic
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.beta.encoding.core
import lambda_calculus.utlc.beta.encoding.nat

namespace lambda_calculus
namespace utlc
namespace β
namespace encoding
namespace utlc

def encode_utlc (et: encoding_type) [complexity.has_encoding (distance_model et) ℕ]:
    utlc → encoded_data et
| (↓n) := alternative 0 2 [complexity.encode (distance_model et) n]
| (Λ f) := alternative 1 2 [encode_utlc f]
| (f·g) := alternative 2 2 [encode_utlc f, encode_utlc g]

instance (et: encoding_type) [complexity.has_encoding (distance_model et) ℕ]: complexity.has_encoding (distance_model et) utlc :=
⟨ ⟨ encode_utlc et,
begin
  intros x y,
  simp only [value_inj],
  induction x generalizing y;
  cases y;
  try { { simp [encode_utlc, complexity.encode, show 0 ≠ 2, by norm_num] } },
  simp [encode_utlc, complexity.encode, x_ih],
  simp [encode_utlc, complexity.encode, x_ih_f, x_ih_g],
end ⟩ ⟩

end utlc
end encoding
end β
end utlc
end lambda_calculus