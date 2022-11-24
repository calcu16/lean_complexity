import Complexity.Std
import Complexity.StdComp
import Complexity.StdDiv
import Complexity.BinaryNat
import Complexity.BigO

namespace Complexity
namespace BinaryNat

def zero_cost (n : Nat) : Nat :=
  let (c, _) := zero Cost.init n
  match c with | Cost.intro v => v

theorem zero_linear : O (zero_cost) = O (λ n => n) :=  by
  have g := show (∀ n : Nat, zero_cost n = n + 1) by
    intro n
    induction n with
    |  zero => simp[zero_cost]
    | succ n h =>
      simp [zero_cost] at h
      simp[zero_cost, zero, h, Cost.inc]
  rw [o_eq]
  apply And.intro
  exists 1
  exists 2
  intros x xb
  simp [g, Nat.succ_mul]
  apply Nat.add_le_add
  apply Nat.le_refl
  assumption
  exists 0
  exists 1
  intros x _
  simp [g, ← Nat.succ_eq_add_one]
  apply Nat.le_of_lt
  apply Nat.lt_succ_self

end BinaryNat
end Complexity