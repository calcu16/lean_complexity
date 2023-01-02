import lambda_calculus.utlc.basic
import lambda_calculus.utlc.beta.basic
import lambda_calculus.utlc.encoding.basic
import lambda_calculus.utlc.encoding.nat

namespace lambda_calculus
namespace utlc
namespace encoding

def encode_utlc: utlc → utlc
| (↓n) := alternative 0 3 (encode n)
| (Λ f) := alternative 1 3 (encode_utlc f)
| (f·g) := alternative 2 3 (pair (encode_utlc f) (encode_utlc g))

instance : has_encoding utlc := ⟨ ⟨ encode_utlc,
  begin
    intro a,
    induction a,
    all_goals { simp [encode_utlc, alternative, tuple, reduced] },
    { refine ⟨ is_closed_below _ _, is_β_reduced _, _ ⟩,
      intro b,
      cases b,
      any_goals { simp [encode_utlc, alternative] },
      exact is_inj,
      norm_num },
    { refine ⟨ closed_below_mono a_ih.left (nat.zero_le _), a_ih.right.left, _⟩,
      intro b,
      cases b,
      any_goals { simp [encode_utlc, alternative] },
      exact a_ih.right.right },
    { refine ⟨ ⟨ closed_below_mono a_ih_f.left (nat.zero_le _),
                closed_below_mono a_ih_g.left (nat.zero_le _), ⟩,
              ⟨ a_ih_f.right.left,
                a_ih_g.right.left ⟩,
              _ ⟩,
      intro b,
      cases b,
      any_goals { simp [encode_utlc, alternative, tuple] },
      intros p q,
      exact ⟨ a_ih_f.right.right p, a_ih_g.right.right q ⟩ }
  end  ⟩ ⟩

end encoding
end utlc
end lambda_calculus