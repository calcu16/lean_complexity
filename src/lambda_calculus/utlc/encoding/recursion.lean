import lambda_calculus.utlc.basic
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.beta.distance
import lambda_calculus.utlc.encoding.basic

namespace lambda_calculus
namespace utlc
namespace encoding

def YCombinator : utlc := Λ (Λ ↓1·(↓0·↓0))·(Λ ↓1·(↓0·↓0))

def ZCombinator : utlc := Λ (Λ ↓1·(Λ ↓1·↓1·↓0))·(Λ ↓1·(Λ ↓1·↓1·↓0))

end encoding
end utlc
end lambda_calculus

