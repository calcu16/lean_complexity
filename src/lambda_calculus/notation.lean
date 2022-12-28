universes u v w

class has_index (α : Type*) := (index : ℕ → α)
class has_lambda (α: Type*) := (lambda : α → α)
class has_apply (α : Type*) := (apply : α → α → α)
class has_symbol (α: Type u) (β: Type v) := (symbol : α → β)

prefix ` ↓ `: 70 := has_index.index
infixl ` · `: 65 := has_apply.apply
prefix ` Λ `: 60 := has_lambda.lambda
prefix ` ◾ `: 70 := has_symbol.symbol
