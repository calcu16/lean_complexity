import HMem.Encoding.Basic
import HMem.Encoding.Emulator
import HMem.Complexity.Basic
import Complexity.Basic

@[simp] theorem Option.bind_comp_some:
    (λ a ↦ Option.bind a f) ∘ (some ∘ g) = f ∘ g :=
  funext λ _ ↦ rfl

@[simp] theorem id_def: (λ (a: α) ↦ a) = id := rfl

theorem lambda_comp {f: α → β}: (λ a ↦ f a) ∘ g = λ a ↦ (f (g a)) := funext λ _ ↦ rfl

@[simp] theorem Complexity.decode_comp_encode
    {α: Type _} [Setoid Data] [Encoding α Data]:
    Complexity.decode α (Data := Data) ∘ Complexity.encode (α := α) (Data := Data) = some :=
  funext λ _ ↦ decode_inv _

@[simp] theorem Complexity.CostFunction.flatMap_some':
  Complexity.CostFunction.flatMap Option.some g = g := rfl

@[simp] theorem Complexity.CostFunction.flatMap_lambda_some {f: α → β}:
  Complexity.CostFunction.flatMap (λ a ↦ Option.some (f a)) g = g ∘ f := rfl

/-
case y
h₀ : Complexity Encoding.Model (↿Memory.getmp) (List.length ∘ Prod.snd)
h₁ : Complexity Encoding.Model Memory.getv 1
⊢ (fun a => Complexity.ALE.bound Complexity.cost_ale (Memory.getmp a.1 a.2)) ∈ O(fun a => List.length a.2)
-/



namespace HMem.Complexity
instance: Program.HasCost Memory.getv 1 where
  program := [
    .setm 1 0,
    .setm 2 0
  ]
  size _ := 0
  sound _ := by simp
  cost_ale := Program.nonRecursiveCompexity (Complexity.ALE.const_ale _ _)

instance [h₀: Complexity Encoding.Model ↿Memory.getmp (List.length ∘ Prod.snd)] [h₁: Complexity Encoding.Model Memory.getv 1]:
    Program.HasCost ↿Memory.getvp (List.length ∘ Prod.snd) where
  program := [
    .costedSubroutine 0 0 ↿Memory.getmp (List.length ∘ Prod.snd),
    .costedSubroutine 0 0 Memory.getv 1
  ]
  size _ := 0
  sound
  | (_, _) => by simp
  cost_ale := by
    refine Program.nonRecursiveCompexity (Complexity.ALE.add_ale (Complexity.ALE.add_ale
      (Complexity.ALE.const_ale _ _)
      ?y)
      ?z) <;>
    simp [Complexity.CostFunction.flatMap, flip, lambda_comp]
    apply Complexity.ALE.const_ale
    apply Complexity.ALE.refl

instance: Program.HasCost ↿Memory.getm 1 where
  program := [ .move .nil (.imm false (.idx 2 0)) ]
  size _ := 0
  sound | (_, _) => by simp
  cost_ale := Program.nonRecursiveCompexity (Complexity.ALE.const_ale _ _)

instance: Program.HasCost ↿Memory.getmp (List.length ∘ Prod.snd) where
  program := [
    .ifv 2 [
      .move 1 (.imm false (.idx 5 0)),
      .move 2 6,
      .recurse 0 0
    ],
    .move 0 1
  ]
  size | (_, as) => as.length
  sound
  | (_, as) => by cases as <;> simp
  cost_ale := Program.simpleLoopComplexity (Complexity.ALE.const_ale _ _) rfl

instance [Complexity.Computable Encoding.Model ↿Memory.getvp] [Complexity.Computable Encoding.Model ↿(@List.cons Bool)]:
  Program.HasTrace ↿Source.get where
  program := [
    .ifv 1 [
      .move 6 2,
      .move 5 4,
      .copy 4 6,
      .recurse 2 2,
      .ifv 3 [
        .copy 8 4,
        .setv 3 false,
        .recurse 3 3,
        .swap 3 4,
        .setv 1 false,
        .subroutine' 1 1 ↿Memory.getvp,
        .subroutine' 0 0 ↿(@List.cons Bool)
      ],
      .move 1 7,
      .subroutine' 0 0 ↿(@List.cons Bool)
    ],
    .setm 0 0
  ]
  size | (s, _) => s.size
  sound | (s, _) => by cases s <;> simp
end HMem.Complexity
