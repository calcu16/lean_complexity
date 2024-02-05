import HMem.Complexity.Def
import HMem.Complexity.Basic

namespace HMem.Complexity.Nat

instance: Program.HasCost (λ n ↦ n / 2) 1 where
  program := [ .move 0 2 ]
  size _ := 0
  sound n := by simp [Encoding.encode_nat_def (n := n)]
  cost_ale := Program.nonRecursiveComplexity (Complexity.ALE.const_ale _ _)

instance: Program.HasCost (λ n ↦ n % 2) 1 where
  program := [
    .copyv 0 1,
    .setm 2 0
  ]
  size _ := 0
  sound n := by simp [Encoding.encode_nat_def (n := n), (Encoding.encode_nat_def (n := n % 2))]
  cost_ale := Program.nonRecursiveComplexity (Complexity.ALE.const_ale _ _)

instance: Program.HasCost (λ n ↦ decide (n ≠ 0)) 1 where
  program := [
    .setm 1 0,
    .setm 2 0
  ]
  size _ := 0
  sound n := by simp [Encoding.encode_nat_def (n := n)]
  cost_ale := Program.nonRecursiveComplexity (Complexity.ALE.const_ale _ _)

instance: Program.HasCost Nat.succ (Nat.log 2) where
  program := [
    .ifv 1 [
      .setv 1 false,
      .recurse 2 2
    ],
    .setv 1 true,
    .setv 0 true
  ]
  size := Nat.size
  sound := Nat.binaryRec' rfl λ b ↦
    by
      cases b <;>
      simp [← Nat.two_mul, Nat.mul_add_mod, Nat.mul_add_div]



  cost_ale := Complexity.ALE.trans
    (Program.simpleLoopComplexity (Complexity.ALE.const_ale _ _) rfl)
    ⟨_, _, λ _ ↦ le_of_le_of_eq Nat.size_le_succ_log (congrArg₂ _ (one_mul _).symm rfl) ⟩

def Nat.AddWithCarry (x y: ℕ) (c: Bool): ℕ := x + y + Bool.toNat c

set_option maxHeartbeats 2000000
instance: Program.HasCost ↿Nat.AddWithCarry (λ | (x, y, _) => Nat.log 2 (x + y)) where
  program := [
    .ifOp₂ Bool.or 1 5 [
      .op₃ Bool.majoritySelect 14 3 11 6,
      .op₃ Bool.xor₃ 1 3 11 6,
      .move 13 12,
      .move 5 4,
      .setv 0 true,
      .setv 3 false,
      .setv 6 false,
      .recurse 2 2
    ],
    .move 0 6,
    .copy 1 0
  ]
  size | (x, y, _) => Nat.size x + Nat.size y
  sound
  | (x, y, c) => by
    cases x using Nat.parityZeroCases <;>
    cases y using Nat.parityZeroCases <;>
    cases c <;>
    simp [Nat.AddWithCarry, Function.HasUncurry.apply₃, Bool.xor₃, Bool.majoritySelect,
      Nat.succ_eq_add_one, ← Nat.add_assoc, Nat.add_right_comm _ 1, Nat.mul_add_div, Nat.ofBits,
      ← Nat.two_mul, Nat.div_add_mod, ← left_distrib (a := 2)]
  cost_ale := by
    apply Complexity.ALE.trans
    exact Program.simpleLoopComplexity' rfl rfl
    apply Complexity.ALE.mk 2 2
    intro arg
    match arg with
    | (x, y, _) =>
      apply le_trans
      apply Nat.add_size_le
      apply mul_le_mul (le_refl _) (Nat.size_le_succ_log) (zero_le _) (zero_le _)

instance: Program.HasCost ↿Nat.add (λ | (x, y) => Nat.log 2 (x + y)) where
  program := [
    .move 5 2,
    .costedSubroutine 0 0 ↿Nat.AddWithCarry (λ | (x, y, _) => Nat.log 2 (x + y))
  ]
  size := 0
  sound _ := by simp [Nat.AddWithCarry]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.of_le
    intro arg
    match arg with
    | (x, y) =>
      apply le_of_eq
      apply Eq.trans
      apply Nat.zero_add
      simp [flip, Complexity.CostFunction.flatMap]

end HMem.Complexity.Nat


instance : Complexity HMem.Encoding.Model ↿Nat.add (λ | (x, y) => Nat.log 2 (x + y)) := inferInstance
