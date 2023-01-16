namespace data
namespace binary_nat

inductive bin_nat_tree : Type
| false : bin_nat_tree
| true : bin_nat_tree
| intro : bin_nat_tree → bin_nat_tree → bin_nat_tree

def height_if_balanced: bin_nat_tree → option ℕ
| (bin_nat_tree.false) := some 0
| (bin_nat_tree.true) := some 0
| (bin_nat_tree.intro lhs rhs) := if height_if_balanced lhs = height_if_balanced rhs
  then height_if_balanced lhs
  else none

def balanced (b: bin_nat_tree): bool := (height_if_balanced b).is_some

def positive: bin_nat_tree → bool
| (bin_nat_tree.false) := ff
| (bin_nat_tree.true) := tt
| (bin_nat_tree.intro lhs rhs) := positive lhs ∨ positive rhs

def minimal_height: bin_nat_tree → bool
| (bin_nat_tree.false) := tt
| (bin_nat_tree.true) := tt
| (bin_nat_tree.intro lhs _) := positive lhs

structure bin_nat :=
mk ::
  (data: bin_nat_tree)
  (proof: balanced data ∧ minimal_height data)


end binary_nat
end data