namespace HMem

inductive Memory (α: Type _)
| leaf : Memory α
| node (value: α) (children: α → Memory α): Memory α

namespace Memory

variable {α: Type u} [OfNat α 0] [DecidableEq α]

def Getvp: Memory α → List α → α
| leaf, _ => 0
| node v _, [] => v
| node _ vs, (a::as) => Getvp (vs a) as

def Setv: Memory α → α → Memory α
| leaf, a => node a (λ _ ↦ leaf)
| node _ vs, a => node a vs

def Getm: Memory α → α → Memory α
| leaf, _ => leaf
| node _ vs, a => vs a

def Setm: Memory α → α → Memory α → Memory α
| leaf, a, m => node 0 (λ x ↦ ite (x = a) m leaf)
| node v vs, a, m => node v (λ x ↦ ite (x = a) m (vs x))

theorem Getvp_Setv_nil (m: Memory α) (a: α): Getvp (Setv m a) [] = a :=
by cases m <;> rfl

end Memory

end HMem