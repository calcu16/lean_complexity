import HMem.Complexity.BitTree

@[simp] theorem Function.HasUncurry.apply₄ (f: α → β → γ → δ → η) (arg: α × β × γ × δ):
    (↿f) arg = f arg.fst arg.snd.fst arg.snd.snd.fst arg.snd.snd.snd := rfl

@[simp] theorem HMem.Encoding.decode_bitTree_node:
    Complexity.decode BitTree (Memory.mk true lhs rhs) =
    Option.map₂ BitTree.node (Complexity.decode _ lhs) (Complexity.decode _ rhs) := by
  simp [Complexity.decode, Complexity.Coding.decode, decodeBitTree]

@[simp] theorem HMem.Encoding.decode_bitTree_bit0:
    Complexity.decode BitTree (0:Memory) =
    Option.map BitTree.bit (0:Fin 2) := by
  simp [Complexity.decode, Complexity.Coding.decode, decodeBitTree]

@[simp] theorem HMem.Encoding.decode_bitTree_bit1:
    Complexity.decode BitTree (Memory.mk false 1 0) =
    Option.map BitTree.bit (1:Fin 2) := by
  simp [Complexity.decode, Complexity.Coding.decode, decodeBitTree]

@[simp] theorem BitTree.add_def (x y: BitTree): Add.add x y = x + y := rfl
@[simp] theorem BitTree.sub_def (x y: BitTree): Sub.sub x y = x - y := rfl

@[simp] theorem BitTree.height_node: BitTree.height (node x y) = max x.height y.height + 1 := rfl
@[simp] theorem BitTree.height_zero: BitTree.height (zero H) = H.length := perfect_height _ _
@[simp] theorem BitTree.height_mulBit: BitTree.height (mulBit H x y) = H.length := perfect_height _ _
@[simp] theorem BitTree.height_addWithCarry: {x y: BitTree} → BitTree.height (BitTree.addWithCarry x y c).snd = x.height
| .bit _, .bit _ => rfl
| .bit _, .node _ _ => rfl
| .node _ _, .bit _ => rfl
| .node _ _, .node _ _ => congrArg Nat.succ (congrArg₂ _ height_addWithCarry height_addWithCarry)

@[simp] theorem BitTree.height_add {x y: BitTree}: (x + y).height = x.height := height_addWithCarry

@[simp] theorem Nat.two_pow_max_commute: 2 ^ (max y z) = max (2 ^ y) (2 ^ z) :=
  Monotone.map_max λ _ _ ↦ Nat.pow_le_pow_right zero_lt_two



attribute [simp] Complexity.CostFunction.inf_def Complexity.CostFunction.add_def Complexity.CostFunction.mul_def

namespace HMem.Complexity.Karatsuba

instance: Program.HasCost ↿BitTree.karatsubaHelper₃ (
    Nat.pow 2 ∘ List.length ∘ Prod.fst +
    Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ∘ Prod.snd) where
  program := [
    .move 16 1,
    .setv 7 true,
    .copy 17 27,
    .copy 18 29,
    .copy 9 7,
    .costedSubroutine 7 3 ↿BitTree.mulBit (List.length ∘ Prod.fst),
    .move 8 5,
    .copy 21 20,
    .move 45 27,
    .move 46 30,
    .costedSubroutine 21 10 ↿BitTree.mulBit' (List.length ∘ Prod.fst),
    .copy 5 20,
    .move 13 28,
    .move 14 29,
    .swap 13 14,
    .costedSubroutine 13 2 ↿BitTree.mulBit' (List.length ∘ Prod.fst),
    .costedSubroutine 9 9 BitTree.zero List.length,
    .costedSubroutine 22 5 BitTree.zero List.length,
    .copy 5 9,
    .copy 14 22,
    .setv 2 true,
    .setv 3 true,
    .setv 4 true,
    .setv 6 true,
    .setv 10 true,
    .costedSubroutine 1 1 ↿(Add.add (α := BitTree)) (Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ⊓ Nat.pow 2 ∘ BitTree.height ∘ Prod.snd),
    .costedSubroutine 0 0 ↿(Add.add (α := BitTree)) (Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ⊓ Nat.pow 2 ∘ BitTree.height ∘ Prod.snd)
  ]
  size := 0
  sound | (H, xy, (xc, x), (yc, y)) => by simp [BitTree.karatsubaHelper₃, ← Fin.val_eq_val]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    simp only [Program.subroutineTimeComplexity, Trace.CostedProgram.subroutineTimeComplexity,
      Trace.TracedProgram.sound'_subroutine_arg, Source.ofNatZero, Function.flip_def,
      Memory.getms_def, Source.get_nil, Memory.getmp_nil, id_def, Function.comp_def, id_eq,
      Encoding.decode_prod, Source.ofNatSucc, Source.succ, Source.succ', Memory.setms_def,
      Source.get_imm, Function.HasUncurry.apply₂, BitTree.add_def, Memory.setmp_cons,
      Memory.setmp_nil, Memory.setm_f_def, Memory.getmp_cons, Memory.setm_t_def,
      Function.HasUncurry.apply₃, Encode.decode_fin2, Option.map₂_coe_left, Option.map₂_coe_right,
      Option.map_some', Option.map_map, Encoding.encode_prod, Encode.encode_fin2,
      OpInstruction.apply, Memory.mop, Memory.getm_mk_f, Memory.getv_mk, Memory.getm_mk_t,
      Memory.zero_getm, Memory.zero_getv, Memory.setvs_def, Memory.setvp_cons, Memory.setvp_nil,
      Memory.setv_def, Option.some_bind, Encoding.decode_cons, Encode.decode_uni,
      Complexity.decode_inv, Memory.zero_def', Memory.getm_mk, Encoding.decode_bitTree_node,
      Nat.pow_eq, Complexity.CostFunction.flatMap_lambda_some, Complexity.CostFunction.inf_def,
      BitTree.height_add, BitTree.height_node, BitTree.height_mulBit, List.length_cons,
      BitTree.height_zero, zero_add]
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.mk (2*2) 0 λ
      | (H, xy, (xc, x), (yc, y)) => by
        simp [flip, Function.comp, ← Fin.val_eq_val, Nat.pow_succ', mul_assoc]
        simp [HAdd.hAdd, Add.add]
        apply Or.inl
        apply le_trans
        apply Nat.le_mul_of_pos_left zero_lt_two
        apply Nat.mul_le_mul_left
        apply Nat.le_add_left
    apply Complexity.ALE.mk (2*2) 0 λ
      | (H, xy, (xc, x), (yc, y)) => by
        simp [flip, Function.comp, ← Fin.val_eq_val, Nat.pow_succ', mul_assoc]
        simp [HAdd.hAdd, Add.add]
        apply Or.inl
        apply le_trans
        apply Nat.le_mul_of_pos_left zero_lt_two
        apply Nat.mul_le_mul_left
        apply Nat.le_add_left
    apply Complexity.ALE.ale_add_right
    apply Complexity.ALE.of_le λ
      | (H, xy, (xc, x), (yc, y)) => by
        simpa [flip, Function.comp, ← Fin.val_eq_val, Nat.pow_succ'] using le_of_lt (Nat.lt_pow_self one_lt_two _)
    apply Complexity.ALE.ale_add_right
    apply Complexity.ALE.of_le λ
      | (H, xy, (xc, x), (yc, y)) => by
        simpa [flip, Function.comp, ← Fin.val_eq_val, Nat.pow_succ'] using Nat.lt_of_succ_le (Nat.lt_pow_self one_lt_two _)
    apply Complexity.ALE.ale_add_right
    apply Complexity.ALE.of_le λ
      | (H, xy, (xc, x), (yc, y)) => by
        simpa [flip, Function.comp, ← Fin.val_eq_val, Nat.pow_succ'] using le_of_lt (Nat.lt_pow_self one_lt_two _)
    apply Complexity.ALE.ale_add_right
    apply Complexity.ALE.of_le λ
      | (H, xy, (xc, x), (yc, y)) => by
        simpa [flip, Function.comp, ← Fin.val_eq_val, Nat.pow_succ'] using le_of_lt (Nat.lt_pow_self one_lt_two _)
    apply Complexity.ALE.ale_add_right
    apply Complexity.ALE.of_le λ
      | (H, xy, (xc, x), (yc, y)) => by
        simpa [flip, Function.comp, ← Fin.val_eq_val, Nat.pow_succ'] using Nat.lt_of_succ_le (Nat.lt_pow_self one_lt_two _)



instance: Program.HasCost ↿BitTree.karatsubaHelper₁ (
    Nat.pow 2 ∘ List.length ∘ Prod.fst +
    Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ∘ Prod.snd +
    Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ∘ Prod.snd ∘ Prod.snd) where
  program := [
    .costedSubroutine 9 1 BitTree.zero List.length,
    .move 10 13,
    .move 3 14,
    .move 6 5,
    .copy 5 9,
    .setv 1 false,
    .setv 4 true,
    .setv 2 true,
    .costedSubroutine 1 1 ↿(Sub.sub (α := BitTree)) (Nat.pow 2 ∘ BitTree.height ∘ Prod.snd),
    .costedSubroutine 0 0 ↿(Sub.sub (α := BitTree)) (Nat.pow 2 ∘ BitTree.height ∘ Prod.snd)
  ]
  size := 0
  sound | (H, z₀, z₂, z₃) => by simp [BitTree.karatsubaHelper₁]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    simp [Program.subroutineTimeComplexity, Trace.CostedProgram.subroutineTimeComplexity,
      flip, Function.comp]
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.mk 2 0 λ
      | (_, _, _, _) => by
        simp [Nat.pow_succ']
        apply And.intro
        apply le_add_right
        apply le_add_right
        apply le_refl _
        apply le_add_right
        apply le_add_left
        apply le_refl _
    apply Complexity.ALE.mk 2 0 λ
      | (_, _, _, _) => by
        simp [Nat.pow_succ']
        apply And.intro
        apply le_add_right
        apply le_add_right
        apply le_refl _
        apply le_add_left
        apply le_refl _
    apply Complexity.ALE.ale_add_right
    apply Complexity.ALE.ale_add_right
    apply Complexity.ALE.of_le λ
      | (_, _, _, _) => by
        simpa [flip, Function.comp, ← Fin.val_eq_val, Nat.pow_succ'] using le_of_lt (Nat.lt_pow_self one_lt_two _)

end HMem.Complexity.Karatsuba

@[simp] theorem BitTree.length_getHeight: {n: ℕ} → List.length (BitTree.getHeight n) = n.size.size := List.length_replicate _ _
attribute [simp] Unary.length_max

namespace HMem.Complexity.Karatsuba

instance [Program.HasCost ↿BitTree.karatsuba (Nat.pow 3 ∘ List.length ∘ Prod.fst)]:
  Program.HasCost ↿Nat.mul (Nat.pow 3 ∘ Nat.log 2 ∘ Nat.log 2 ∘ Prod.fst + Nat.pow 3 ∘ Nat.log 2 ∘ Nat.log 2 ∘ Prod.snd) where
  program := [
      .move 1 0,
      .costedSubroutine 5 3 BitTree.getHeight (Nat.log 2),
      .costedSubroutine 6 4 BitTree.getHeight (Nat.log 2),
      .costedSubroutine 2 2 ↿Unary.max (List.length ∘ Prod.fst ⊓ List.length ∘ Prod.snd),
      .move 22 4,
      .copy 21 2,
      .move 20 3,
      .copy 19 2,
      .costedSubroutine 9 9 ↿BitTree.ofNat (Nat.pow 2 ∘ List.length ∘ Prod.fst),
      .costedSubroutine 10 10 ↿BitTree.ofNat (Nat.pow 2 ∘ List.length ∘ Prod.fst),
      .copy 3 2,
      .costedSubroutine 1 1 ↿BitTree.karatsuba (Nat.pow 3 ∘ List.length ∘ Prod.fst),
      .swap 1 2,
      .move 4 1,
      .setv 1 true,
      .costedSubroutine 0 0 ↿BitTree.toNat (Nat.pow 2 ∘ List.length ∘ Prod.fst)
  ]
  size := 0
  sound | (x, y) => by simp [← Nat.karatsuba_eq_mul, Nat.karatsuba]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    sorry
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.const_ale
    -- apply Complexity.ALE.trans (y := Nat.pow 2 ∘ Nat.size ∘ Nat.size ∘ Prod.fst + Nat.pow 2 ∘ Nat.size ∘ Nat.size ∘ Prod.snd)
    -- apply Complexity.ALE.mk 2 0 λ
    --   | (_, _) => by
    --     simp [Function.comp, flip, Nat.pow_succ']
    --     apply And.intro
    --     apply Nat.le_add_right
    --     apply Nat.le_add_left
    -- apply Complexity.ALE.add_ale_add

instance: Program.HasCost ↿BitTree.karatsuba (Nat.pow 3 ∘ List.length ∘ Prod.fst) where
  program := [
    .ifv [false] [
      .move [false, false, false, false] [false],
      .copy [false, false, false, true, false] [false, false, false, false],
      .move [false, false, false, true, true] [true, false],
      .costedSubroutine [false, false, false, true] [false, false, false, true] ↿BitTree.mkPerfect (Nat.pow 2 ∘ List.length ∘ Prod.fst),
      .costedSubroutine 17 [false, false, false, true] BitTree.lo 1,
      .costedSubroutine [false, false, false, true] [false, false, false, true] BitTree.hi 1,
      .copy [false, false, true, true, false] 15,
      .move [false, false, true, true, true] 6,
      .costedSubroutine 18 18 ↿BitTree.mkPerfect (Nat.pow 2 ∘ List.length ∘ Prod.fst),
      .costedSubroutine 19 18 BitTree.lo 1,
      .costedSubroutine 18 18 BitTree.hi 1,
      .copy [false, true, true, false, false] 16,
      .copy [false, true, true, false, true, false] 17,
      .costedSubroutine 21 21 ↿BitTree.addWithCarry (Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ⊓ Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ∘ Prod.snd),
      .copy [false, true, true, true, false] 18,
      .copy [false, true, true, true, true, false] 19,
      .costedSubroutine 22 22 ↿BitTree.addWithCarry (Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ⊓ Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ∘ Prod.snd),
      .copy 23 [false, false, false, false, true],
      .copy [true, false, false, true, false] [false, true, true, false, true],
      .copy [true, false, false, true, true] [false, true, true, true, true],
      .recurse 11 11,
      .move [true, false, true, false] 11,
      .copy 11 [false, false, false, false, true],
      .move [true, false, true, true] 10,
      .costedSubroutine 5 5 ↿BitTree.karatsubaHelper₃ (Nat.pow 2 ∘ List.length ∘ Prod.fst + Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ∘ Prod.snd),
      .copy 13 [false, false, false, false, true],
      .move [true, true, true, false] 17,
      .move [true, true, true, true] 19,
      .recurse 6 6,
      .copy 9 [false, false, false, false, true],
      .move 21 16,
      .move 22 18,
      .recurse 4 4,
      .move [true, false, true, true, true] 5,
      .copy 11 15,
      .copy [true, false, true, false] 6,
      .copy [true, false, true, true, false] 4,
      .costedSubroutine 5 5 ↿BitTree.karatsubaHelper₁
        (Nat.pow 2 ∘ List.length ∘ Prod.fst + Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ∘ Prod.snd + Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ∘ Prod.snd ∘ Prod.snd),
      .move 12 5,
      .copy 11 [false, false, false, false, true],
      .costedSubroutine 5 5 ↿BitTree.lshift2 (List.length ∘ Prod.fst),
      .costedSubroutine 8 15 BitTree.zero List.length,
      .move 7 4,
      .move 4 5,
      .copy 5 8,
      .setv 3 true,
      .setv 2 true,
      .costedSubroutine 1 1 ↿(Add.add (α := BitTree)) (Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ⊓ Nat.pow 2 ∘ BitTree.height ∘ Prod.snd),
      .costedSubroutine 0 0 ↿(Add.add (α := BitTree)) (Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ⊓ Nat.pow 2 ∘ BitTree.height ∘ Prod.snd),
    ],
    .setv 1 true,
    .costedSubroutine 5 5 BitTree.getBit 1,
    .costedSubroutine 6 6 BitTree.getBit 1,
    .costedSubroutine 0 0 ↿BitTree.mulBit (List.length ∘ Prod.fst)
  ]
  size := List.length ∘ Prod.fst
  sound
  | ([], x, y) => by simp [BitTree.karatsuba, ← Fin.val_eq_val]
  | (()::H, x, y) => by
    simp [BitTree.karatsuba, ← Fin.val_eq_val]
  cost_ale := by
    apply Program.divideAndConquerComplexityLeafHeavy
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    -- apply Complexity.ALE.add_ale
    sorry


end HMem.Complexity.Karatsuba
