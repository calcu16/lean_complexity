import logic.relation

namespace lambda_calculus
/-
 - Notation for lambda calculus
 -
 - `↓` converts an integer into a lambda calculus representing
 -     the index of the corresponding abstraction as in De Bruijn indexing
 -     (https://en.wikipedia.org/wiki/De_Bruijn_index)
 - `Λ` is a unary operator that adds an abstraction level to an existing lambda calculus
 - `·` composes to lambda calculi together
 - M←[x:=N] represents a substitution of x with N within M
 - ↑¹ represents a shift of indices with a cutoff
 -/
class has_down (α : Type*) := (down : ℕ → α)
class has_lambda (α: Type*) := (lambda : α → α)
class has_dot (α : Type*) := (dot : α → α → α)
class has_substitution (α : Type*) := (substitution : α → ℕ → α → α)
class has_shift (α : Type*) := (shift : α → ℕ → α)

prefix ` ↓ `: 75 := has_down.down
infixl ` · `: 65 := has_dot.dot
prefix ` Λ `: 60 := has_lambda.lambda
-- substitution notation can cause problems for the parser, so only using it locally
-- notation a `[` b `:=` c  `]` : 70 := has_substitution.substitution a b c
infixl ` ↑¹ ` : 71 := has_shift.shift

class has_β_reduction (α : Type*) := (step : α → α → Prop)

-- should use subscript beta (e.g. ↠ᵦ) but unicode does not have subscript support for η
infix ` →β `: 50 := has_β_reduction.step
infix ` ↠β `: 50 := relation.refl_trans_gen has_β_reduction.step
infix ` ≡β `: 50 := relation.join (relation.refl_trans_gen has_β_reduction.step)

-- transitive parallel reduction is an equivalent to transitive beta reduction
--  and used to prove the church-rosser property of β reductions
class has_parallel_reduction (α : Type*) := (step : α → α → Prop)

infix ` →∥ `: 50 := has_parallel_reduction.step
infix ` ↠∥ `: 50 := relation.refl_trans_gen has_parallel_reduction.step
infix ` ≡∥ `: 50 := relation.join (relation.refl_trans_gen has_parallel_reduction.step)

class has_η_reduction (α : Type*) := (step : α → α → Prop)

infix ` →η `: 50 := has_η_reduction.step
infix ` ↠η `: 50 := relation.refl_trans_gen has_η_reduction.step
infix ` ≡η `: 50 := relation.join (relation.refl_trans_gen has_η_reduction.step)

class has_βη_reduction (α : Type*) := (step : α → α → Prop)

infix ` →βη `: 50 := has_βη_reduction.step
infix ` ↠βη `: 50 := relation.refl_trans_gen has_βη_reduction.step
infix ` ≡βη `: 50 := relation.join (relation.refl_trans_gen has_βη_reduction.step)

end lambda_calculus