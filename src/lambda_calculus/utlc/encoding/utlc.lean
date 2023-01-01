import lambda_calculus.utlc.basic
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.encoding.basic
import lambda_calculus.utlc.encoding.nat

namespace lambda_calculus
namespace utlc
namespace encoding

def encode_utlc: utlc → utlc
| (↓n) := alternative bool.ff (lift n)
| (Λ f) := alternative bool.tt (alternative bool.ff (encode_utlc f))
| (f·g) := alternative bool.tt (alternative bool.tt (pair (encode_utlc f) (encode_utlc g)))

instance : has_encoding utlc := ⟨ encode_utlc ⟩

end encoding
end utlc
end lambda_calculus