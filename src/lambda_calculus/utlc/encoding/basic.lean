import lambda_calculus.utlc.basic

namespace lambda_calculus
namespace utlc
class has_encoding (α: Type) := (encode: α → utlc)

def encode {α: Type*} [f: has_encoding α]: α → utlc := has_encoding.encode

namespace encoding
def pair (f g: utlc): utlc := Λ ↓0·f·g

instance prod_encoding {α β: Type*} [f: has_encoding α] [g: has_encoding β]:
  has_encoding (α × β) := ⟨ λ a, pair (encode a.fst) (encode a.snd) ⟩

def alternative (b: bool) (f: utlc): utlc :=
  if b then Λ Λ ↓0·f
  else Λ Λ ↓1·f

instance sum_encoding {α β: Type*} [f: has_encoding α] [g: has_encoding β]:
  has_encoding (α ⊕ β) := ⟨ λ a,
    sum.elim ((alternative bool.ff) ∘ encode) ((alternative bool.tt) ∘ encode) a ⟩

def iterate: ℕ → utlc → utlc → utlc
| 0 := λ f x, x 
| (n+1) := λ f x, f·iterate n f x

end encoding
end utlc
end lambda_calculus