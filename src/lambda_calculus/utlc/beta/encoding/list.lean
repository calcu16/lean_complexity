import lambda_calculus.utlc.beta.distance
import complexity.basic
import lambda_calculus.utlc.beta.encoding.basic
import lambda_calculus.utlc.beta.encoding.core

namespace lambda_calculus
namespace utlc
namespace β
namespace encoding
namespace list

-- def encode_list {α : Type} [complexity.has_encoding distance_model α]: list α → encoded_data
-- | [] := alternative 0 1 []
-- | (x::xs) := alternative 1 1 [complexity.encode distance_model x, encode_list xs] 

-- instance list_encoding (α: Type) [α_en: complexity.has_encoding distance_model α]:
--   complexity.has_encoding distance_model (list α) :=
--   ⟨ ⟨ encode_list,
-- begin
--   intros x y,
--   induction x generalizing y;
--   cases y,
--   { simp },
--   { simp [encode_list] },
--   { simp [encode_list] },
--   simp at x_ih,
--   simp [encode_list, x_ih],
--   intro,
--   apply α_en.1.2 x_hd y_hd,
-- end ⟩ ⟩ 

end list
end encoding
end β
end utlc
end lambda_calculus