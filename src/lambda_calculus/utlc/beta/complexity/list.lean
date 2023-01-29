import lambda_calculus.utlc.beta.distance
import lambda_calculus.utlc.beta.encoding.basic
import lambda_calculus.utlc.beta.encoding.core
import lambda_calculus.utlc.beta.encoding.list
import lambda_calculus.utlc.beta.complexity.core
import complexity.basic
import complexity.nat

open complexity
open lambda_calculus.utlc.β.encoding

namespace lambda_calculus
namespace utlc
namespace β
namespace complexity
namespace list
local attribute [simp] β.normal_iteration β.strategic_reduction_step
local attribute [simp] down_shift head_reduced
local attribute [simp] complexity.cast_unwrap distance_model


-- def cons_prog: encoded_program := ⟨ (Λ Λ Λ Λ ↓0·↓3·↓2), by simp[← one_add_one_eq_two] ⟩

-- instance cons_complexity
--   (α: Type) [complexity.has_encoding distance_model α]:
--   complexity.has_complexity distance_model (@list.cons α) :=
--   ⟨ ⟨ (λ _ _, (2:ℕ)), ⟨ cons_prog, λ x xs, distance_le_of_normal_iteration _
--     (by simp [cons_prog, has_encoding.value, encoding.list.encode_list, encode]) ⟩ ⟩ ⟩

-- def handle_nil (f y: utlc): utlc := f
-- def handle_cons (f y: utlc): utlc := Λ Λ (f ↑¹ 0 ↑¹ 1)·↓1·↓0·((y ↑¹ 0 ↑¹ 1)·↓0)
-- def fold_cons (f y: utlc): utlc := Λ Λ ((y ↑¹ 0 ↑¹ 1)·((f ↑¹ 0 ↑¹ 1)·↓1·↓0)·↓0)
-- def rec_list (y g f₀ f₁: utlc): utlc := g·handle_nil f₀ y·handle_cons f₁ y

-- section
-- local notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c

-- theorem rec_list_sub {y g f₀ f₁: utlc} (n: ℕ) (x: utlc):
--   (rec_list y g f₀ f₁)[n:=x] = (rec_list (y[n:=x]) (g[n:=x]) (f₀[n:=x]) (f₁[n:=x])) :=
-- begin
--   simp [rec_list, handle_nil, handle_cons, substitution_shift_ge],
--   repeat { rw [substitution_shift_ge] },
--   all_goals { linarith },
-- end

-- theorem rec_list_nil {α: Type} [α_en: complexity.has_encoding distance_model α]
--   (y: utlc) (f₀ f₁: utlc):
--   distance_le 2
--     (rec_list y (encoding.list.encode_list (@list.nil α)).value f₀ f₁)
--     f₀ :=
-- begin
--   rw [rec_list, list.encode_list, β.encoding.alternative],
--   simp,
--   apply distance_le_of_normal_iteration,
--   simp [handle_nil],
-- end

-- theorem rec_list_cons {α: Type} [α_en: complexity.has_encoding distance_model α]
--   (y: utlc) (x: α) (xs: list α) (f₀ f₁: utlc):
--   distance_le 4
--     (rec_list y (encoding.list.encode_list (x :: xs)).value f₀ f₁)
--     (f₁·(complexity.encode distance_model x).value·(complexity.encode distance_model xs).value·(y·(complexity.encode distance_model xs).value)) :=
-- begin
--   rw [rec_list, list.encode_list, β.encoding.alternative],
--   apply distance_le_of_normal_iteration,
--   simp [handle_cons, complexity.encode, has_encoding.value],
-- end
-- end


-- namespace foldl_complexity

-- def cost {α: Type} {β: Type}
--   (rf: α → β → α)
--   (c_nil: ℕ) (c_cons: α → β → ℕ):
--   α → list β → ℕ :=
--   λ a xs, (list.foldl (λ (ca: ℕ × α) b, (ca.fst + c_cons ca.snd b, rf ca.snd b)) ((0:ℕ), a) xs).fst

-- | ([]) a := c_nil
-- | (x :: xs) a := c_cons a x + cost xs (rf a x)
-- end foldl_complexity

-- instance foldl_complexity
--   (α β: Type) [has_encoding distance_model α] [has_encoding distance_model β]
--   (f: α → β → α) [cf: has_complexity distance_model f]:
--   has_complexity distance_model (list.foldl f) :=
-- begin
--   fconstructor,
--   fconstructor,
--   exact (foldl_complexity.cost f 0 cf.value.cost),
--   rcases cf.value with ⟨cfc, fp, cfp⟩,
--   fconstructor,
--   fconstructor,
--   exact (yrec 

-- end




end list
end complexity
end β
end utlc
end lambda_calculus
