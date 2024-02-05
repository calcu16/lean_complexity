import HMem.Complexity.Def
import HMem.Complexity.Basic
import Lib

@[simp] theorem HMem.Encoding.encode_unit: (Complexity.encode ():Memory) = 0 := rfl

@[simp] theorem HMem.Encoding.encode_bit: {b: Fin 2} → (Complexity.encode (BitTree.bit b):Memory) = .mk false (.mk (b = 1) 0 0) 0
| 0 => Memory.zero_def'.symm.trans (congrArg₂ _ Memory.zero_def'.symm rfl)
| 1 => rfl

@[simp] theorem HMem.Encode.encode_node: (Complexity.encode (BitTree.node lhs rhs):Memory) = .mk true (Complexity.encode lhs) (Complexity.encode rhs) := rfl

@[simp] theorem HMem.Encode.encode_fin2: {b: Fin 2} → (Complexity.encode (b: Fin 2):Memory) = .mk (b = 1) 0 0
| 0 => Memory.zero_def'.symm
| 1 => rfl

@[simp] theorem Bool.toNat_fin: {v: Fin 2} → Bool.toNat (decide ((Fin.val v) = 1)) = v.val
| 0 => rfl
| 1 => rfl

@[simp] theorem BitTree.negate_height: (x: BitTree) → x.negate.height = x.height
| .bit _ => rfl
| .node _ _ => congrArg₂ _ (congrArg₂ _ (negate_height _) (negate_height _)) rfl

@[simp] theorem HMem.Encode.decode_uni (m: Memory): (Complexity.decode Unit m) = some () := rfl
@[simp] theorem HMem.Encode.decode_fin2: (Complexity.decode (Fin 2) m) = some ⟨Bool.toNat (Memory.getv m), match m.getv with | false => zero_lt_two | true => one_lt_two ⟩ := rfl

theorem Complexity.CostFunction.flatmap_bind [Zero θ] {x: CostFunction α θ} {f: β → Option α} {g: γ → Option β}:
    x.flatMap (flip Option.bind f ∘ g) = (x.flatMap f).flatMap g :=
  funext λ c ↦ by cases hg:g c <;> simp [flatMap, flip, Option.bind, hg]

def List.split': List α → (Option α × List α × List α)
| [] => (none, [], [])
| a::[] => (some a, [], [])
| a::b::tl =>
  have s := split' tl
  (s.fst, a::s.snd.fst, b::s.snd.snd)

@[simp] theorem List.split'_nil: List.split' (α := α) [] = (none, [], []) := rfl
@[simp] theorem List.split'_singletone: List.split' [a] = (some a, [], []) := rfl
@[simp] theorem List.split'_cons_cons_fst: (List.split' (a::b::tl)).fst = (List.split' tl).fst := rfl
@[simp] theorem List.split'_cons_cons_left: (List.split' (a::b::tl)).snd.fst = a::(List.split' tl).snd.fst := rfl
@[simp] theorem List.split'_cons_cons_right: (List.split' (a::b::tl)).snd.snd = b::(List.split' tl).snd.snd := rfl

@[simp] theorem List.split'_isSome:
    (xs: List α) → (List.split' xs).fst.isSome = decide (xs.length % 2 = 1)
| [] => rfl
| _::[] => rfl
| _::_::tl => by simpa using List.split'_isSome tl

@[simp] theorem List.split'_length_left:
    (xs: List α) → (List.split' xs).snd.fst.length = xs.length / 2
| [] => rfl
| _::[] => rfl
| _::_::tl => by simpa using List.split'_length_left tl

@[simp] theorem List.split'_length_right:
    (xs: List α) → (List.split' xs).snd.snd.length = xs.length / 2
| [] => rfl
| _::[] => rfl
| _::_::tl => by simpa using List.split'_length_right tl

@[simp] theorem HMem.Encoding.encode_option_getv [Complexity.Encoding α Memory]: (o: Option α) →
  Memory.getv (Complexity.encode o) = o.isSome
| none => rfl
| some _ => rfl


@[simp] theorem HMem.Encoding.encode_option_getm_t [Complexity.Encoding α Memory]: (o: Option α) →
  Memory.getm (Complexity.encode o) true = 0
| none => rfl
| some _ => rfl

namespace HMem.Complexity.Karatsuba

instance: Program.HasCost (λ n ↦ List.replicate (Nat.size n) ()) (Nat.log 2) where
  program := [
    .ifv 0 [
      .setm 1 0,
      .recurse 2 2
    ] ]
  size := Nat.size
  sound n := by
    induction n using Nat.parityZeroCases <;>
    simp [-List.replicate, Nat.div_add_mod]
  cost_ale := Complexity.ALE.trans (Program.simpleLoopComplexity' rfl rfl) Nat.size_ale_log

instance [Complexity.Coding α Memory]: Program.HasCost (List.split' (α := α)) List.length where
  program := [
    .ifv 0 [
      .setv 0 false,
      .ifv 2 [
        .setv 2 false,
        .recurse 6 6,
        .swap 1 13,
        .move 11 5,
        .swap 11 13,
        .move 12 29,
        .move 14 30,
        .setv 5 true,
        .setv 6 true
      ],
      .move 3 1,
      .setv 1 true
    ]
  ]
  size := List.length
  sound
  | [] => by simp
  | _::[] => by simp
  | _::_::_ => by simp [λ n ↦ lt_trans (Nat.lt_succ_self n) (Nat.lt_succ_self _)]
  cost_ale := Program.simpleLoopComplexity' rfl rfl

instance [Complexity.Coding α Memory]: Program.HasCost (List.length (α := α)) List.length where
  program := [
    .ifv 0 [
      .costedSubroutine 0 0 (List.split' (α := α)) List.length,
      .setv 0 true,
      .recurse 2 5,
      .setm 3 0
    ]
  ]
  size := Nat.size ∘ List.length
  sound
  | [] => by simp
  | _::[] => by simp [List.split']
  | _::_::_ => by simp [List.split']
  cost_ale := by
    apply Complexity.ALE.trans _ Nat.pow_size_ale_self
    apply Program.sizeLoopComplexity _ _
    rfl
    apply Complexity.ALE.trans _ Nat.ale_pow_size
    apply Complexity.ALE.of_le
    intro xs
    cases xs <;>
    simp [Program.subroutineTimeComplexity,
      Trace.CostedProgram.subroutineTimeComplexity,
      Complexity.CostFunction.flatMap,
      flip, Option.filter]

instance: Program.HasCost Nat.size (Nat.log 2) where
  program := [
    .costedSubroutine 0 0 (λ n ↦ List.replicate (Nat.size n) ()) (Nat.log 2),
    .costedSubroutine 0 0 (List.length (α := Unit)) List.length
  ]
  size := 0
  sound _ := by simp
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.const_ale _ _
    simpa [flip, Function.comp] using Nat.size_ale_log
    simpa [flip, Function.comp] using Complexity.ALE.refl

instance: Program.HasCost BitTree.getHeight (Nat.log 2) where
  program := [
    .costedSubroutine 0 0 Nat.size (Nat.log 2),
    .costedSubroutine 0 0 (λ n ↦ List.replicate (Nat.size n) ()) (Nat.log 2)
  ]
  size := 0
  sound _ := by simp [BitTree.getHeight]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.const_ale _ _
    simp [flip, Function.comp]
    apply Complexity.ALE.of_le
    intro a
    apply Nat.log_mono_right
    apply Nat.size_le_self
    simpa [flip, Function.comp] using Complexity.ALE.refl

instance: Program.HasCost ↿Unary.max (List.length ∘ Prod.fst ⊓ List.length ∘ Prod.snd) where
  program := [
    .ifv 1 [
      .ifv 2 [
        .move 5 4,
        .setv 2 false,
        .recurse 2 2,
        .setm 1 0,
        .setv 0 true
      ],
      .move 0 1
    ],
    .move 0 2
  ]
  size args := min args.fst.length args.snd.length
  sound
  | ([], _) => by simp [Unary.max]
  | (()::_, []) => by simp [Unary.max]
  | (()::_, ()::_) => by simp [Unary.max]
  cost_ale := Program.simpleLoopComplexity' rfl rfl

instance: Program.HasCost BitTree.zero List.length where
  program := [
    .ifv 0 [
      .recurse 2 2,
      .copy 1 2,
      .setv 0 true
    ]
  ]
  size := List.length
  sound H := by cases H <;> simp [BitTree.zero]
  cost_ale := Program.simpleLoopComplexity' rfl rfl

instance: Program.HasCost BitTree.setLowestBit BitTree.rightHeight where
  program := [
    .ifv 0 [ .recurse 2 2 ],
    .setv 1 true
  ]
  size := BitTree.rightHeight
  sound t := by
    cases t <;>
    simp [BitTree.setLowestBit, BitTree.rightHeight]
  cost_ale := Program.simpleLoopComplexity' rfl rfl

instance: Program.HasCost BitTree.one List.length where
  program := [
    .costedSubroutine 0 0 BitTree.zero List.length,
    .costedSubroutine 0 0 BitTree.setLowestBit BitTree.rightHeight
  ]
  size := 0
  sound H := by cases H <;> simp [BitTree.zero, BitTree.one]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.const_ale _ _
    apply Complexity.ALE.of_le (λ a ↦ by simp [flip, Function.comp, BitTree.rightHeight_zero])
    apply Complexity.ALE.of_le (λ a ↦ by simp [flip, Function.comp])

instance: Program.HasCost ↿Unary.append_pow₂ (Nat.pow 2 ∘ List.length ∘ Prod.fst) where
  program := [
    .ifv 1 [
      .move 1 4,
      .recurse 2 0,
      .recurse 0 0
    ],
    .setv 0 true
  ]
  size := List.length ∘ Prod.fst
  sound | (H, _) => by cases H <;> simp [Unary.append_pow₂]
  cost_ale := Program.simpleDivideAndConquerComplexity' _ rfl (le_refl _)

instance: Program.HasCost ↿Unary.div_pow₂ (List.length ∘ Prod.snd) where
  program := [
    .ifv 2 [
      .move 1 4,
      .move 2 6,
      .recurse 0 0
    ],
    .move 0 1
  ]
  size := List.length ∘ Prod.snd
  sound | (_, H) => by cases H <;> simp[-Unary.div_pow₂_eq, Unary.div_pow₂]
  cost_ale := Program.simpleLoopComplexity' (by rfl) (by rfl)

theorem eq_decide [Decidable P]: (b = decide P) = (decide b ↔ P) := by
  cases b <;> simp

instance: Program.HasCost ↿Unary.mod_pow₂ (List.length ∘ Prod.snd) where
  program := [
    .ifv 2 [
      .move 5 4,
      .setv 2 false,
      .recurse 4 2,
      .move 0 1,
      .op₂ Bool.or 0 1 2
    ],
    .setm 0 0
  ]
  size := List.length ∘ Prod.snd
  sound | (_, H) => by
          cases H <;>
          simp [
            -Unary.mod_pow₂_eq, Unary.mod_pow₂,
            Nat.mul_add_mod, Nat.mul_add_div,
            eq_decide, imp_iff_or_not]
  cost_ale := Program.simpleLoopComplexity' (by rfl) (by rfl)

instance: Program.HasCost ↿Unary.mul_pow₂ (List.length ∘ Prod.snd) where
  program := [
    .ifv 2 [
      .move 2 6,
      .recurse 2 0,
      .setm 1 0,
      .copyv 0 2
    ],
    .move 0 1
  ]
  size := List.length ∘ Prod.snd
  sound | (_, H) => by cases H <;> simp [-Unary.mul_pow₂_eq, Unary.mul_pow₂]
  cost_ale := Program.simpleLoopComplexity' (by rfl) (by rfl)

instance: Program.HasCost ↿BitTree.divBound (Nat.pow 2 ∘ List.length ∘ Prod.snd) where
  program := [
    .move 5 2,
    .costedSubroutine 2 2 (↿Unary.append_pow₂) (Nat.pow 2 ∘ List.length ∘ Prod.fst),
    .costedSubroutine 0 0 (↿Unary.div_pow₂) (List.length ∘ Prod.snd)
  ]
  size := 0
  sound
  | (_, _) => by
    simp[BitTree.divBound, Unary.append_pow₂_length, BitTree.bound, BitTree.width, BitTree.heightOf]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.const_ale
    apply Complexity.ALE.of_le λ | (_, _) => by simp [flip, Function.comp, Unary.append_pow₂_length]
    apply Complexity.ALE.of_le λ | (_, _) => by simp [flip, Function.comp]

instance: Program.HasCost ↿BitTree.modBound (Nat.pow 2 ∘ List.length ∘ Prod.snd) where
  program := [
    .move 5 2,
    .costedSubroutine 2 2 (↿Unary.append_pow₂) (Nat.pow 2 ∘ List.length ∘ Prod.fst),
    .costedSubroutine 0 0 (↿Unary.mod_pow₂) (List.length ∘ Prod.snd)
  ]
  size := 0
  sound
  | (_, _) => by
    simp[BitTree.modBound, Unary.append_pow₂_length, BitTree.bound, BitTree.width, BitTree.heightOf]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.const_ale
    apply Complexity.ALE.of_le λ | (_, _) => by simp [flip, Function.comp, Unary.append_pow₂_length]
    apply Complexity.ALE.of_le λ | (_, _) => by simp [flip, Function.comp]

instance: Program.HasCost ↿BitTree.mulBound (Nat.pow 2 ∘ List.length ∘ Prod.snd) where
  program := [
    .move 5 2,
    .costedSubroutine 2 2 (↿Unary.append_pow₂) (Nat.pow 2 ∘ List.length ∘ Prod.fst),
    .costedSubroutine 0 0 (↿Unary.mul_pow₂) (List.length ∘ Prod.snd)
  ]
  size := 0
  sound
  | (_, _) => by
    simpa [BitTree.mulBound, Unary.append_pow₂_length, BitTree.bound, BitTree.width, BitTree.heightOf]
      using Nat.mul_comm _ _
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.const_ale
    apply Complexity.ALE.of_le λ | (_, _) => by simp [flip, Function.comp, Unary.append_pow₂_length]
    apply Complexity.ALE.of_le λ | (_, _) => by simp [flip, Function.comp]

instance: Program.HasCost ↿BitTree.ofNatHelper (Nat.pow 2 ∘ List.length ∘ Prod.fst) where
  program := [
    .ifv 1 [
      .move 1 4,
      .recurse 2 0,
      .move 3 1,
      .move 4 5,
      .recurse 1 1,
      .move 5 4,
      .move 1 3,
      .setv 2 true
    ],
    .move 1 6,
    .setv 2 false
  ]
  size := List.length ∘ Prod.fst
  sound | (H, _) => by cases H <;> simp [BitTree.ofNatHelper, ← Fin.val_eq_val]
  cost_ale := Program.simpleDivideAndConquerComplexity' _ rfl (le_refl _)

instance: Program.HasCost ↿BitTree.ofNat (Nat.pow 2 ∘ List.length ∘ Prod.fst) where
  program := [
    .costedSubroutine 0 0 ↿BitTree.ofNatHelper (Nat.pow 2 ∘ List.length ∘ Prod.fst),
    .move 0 2
  ]
  size := 0
  sound | (_, _) => by simp[BitTree.ofNat]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.const_ale
    apply Complexity.ALE.of_le λ | (_, _) => by simp [flip, Function.comp]

theorem Fin₂.not_decide_eq_zero: {v: Fin 2} → (!(decide (v.val = 0))) = (decide (v.val = 1))
| 0 => rfl
| 1 => rfl

@[simp] theorem Fin.mod_eq (v: Fin N): v.val % N = v := Nat.mod_eq_of_lt v.isLt
@[simp] theorem Fin.div_eq_zero (v: Fin N): v.val / N = 0 := Nat.div_eq_of_lt v.isLt

instance: Program.HasCost ↿BitTree.toNatHelper (Nat.pow 2 ∘ List.length ∘ Prod.fst) where
  program := [
    .ifv 5 [
      .ifv 1 [
        .move 3 4,
        .move 9 11,
        .move 10 6,
        .setv 1 false,
        .recurse 6 1,
        .move 5 12,
        .move 1 3,
        .recurse 0 0
      ],
      .setm 0 0
    ],
    .move 1 11,
    .move 2 6,
    .op₂ Bool.or 0 1 2
  ]
  size := List.length ∘ Prod.fst
  sound
  | (H, t, _) => by
    cases H <;>
    cases t <;>
    simp [BitTree.toNatHelper, Nat.mul_add_mod, Nat.mul_add_div, eq_decide, imp_iff_or_not,
      Fin₂.not_decide_eq_zero, ← Fin.val_eq_val, add_comm _ (2 * _)]
  cost_ale := Program.simpleDivideAndConquerComplexity' _ rfl (le_refl _)

instance: Program.HasCost ↿BitTree.toNat (Nat.pow 2 ∘ List.length ∘ Prod.fst) where
  program := [
    .move 5 2,
    .costedSubroutine 0 0 ↿BitTree.toNatHelper (Nat.pow 2 ∘ List.length ∘ Prod.fst)
  ]
  size := 0
  sound | (_, _) => by simp [BitTree.toNat]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.const_ale
    apply Complexity.ALE.of_le λ | (_, _) => by simp [flip, Function.comp]

instance: Program.HasCost ↿BitTree.addWithCarry (Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ⊓ Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ∘ Prod.snd) where
  program := [
    .ifOp₂ Bool.xor 1 5 [ -- unreachable under "normal" arguments
      .swap 1 6,
      .move 2 6
    ],
    .ifOp₂ Bool.and 1 5 [
      .swap 4 5,
      .move 14 6,
      .move 13 10,
      .recurse 2 2,
      .setv 1 false,
      .setv 4 false,
      .move 10 5,
      .recurse 1 1,
      .move 5 4,
      .setv 2 true,
      .move 1 3
    ],
    .op₃ Bool.xor₃ 5 3 11 6,
    .op₃ Bool.majoritySelect 1 3 11 6,
    .setv 3 false,
    .setv 11 false,
    .setv 6 false
  ]
  size args := min args.fst.height args.snd.fst.height
  sound
  | (.bit x, .bit y, c) => by simp [BitTree.addWithCarry, ← Fin.val_eq_val]
  | (.bit _, .node _ _, _) => by simp[BitTree.addWithCarry]
  | (.node _ _, .bit _, _) => by simp[BitTree.addWithCarry]
  | (.node xhi xlo, .node yhi ylo, _) => by
    simp [BitTree.addWithCarry, ← Fin.val_eq_val]
  cost_ale := by
    apply Complexity.ALE.trans
    apply Program.simpleDivideAndConquerComplexity'
    rfl
    exact le_refl _
    apply Complexity.ALE.of_le
    intro
    apply le_inf
    apply Nat.pow_le_pow_right
    exact zero_lt_two
    apply min_le_left
    apply Nat.pow_le_pow_right
    exact zero_lt_two
    apply min_le_right

instance: Program.HasCost BitTree.negate (Nat.pow 2 ∘ BitTree.height) where
  program := [
    .ifv 0 [
      .recurse 1 1,
      .recurse 2 2
    ],
    .ifv 1 [ .setv 1 false ],
    .setv 1 true
  ]
  size := BitTree.height
  sound
  | .bit 0 => by simp [BitTree.negate]
  | .bit 1 => by simp [BitTree.negate]
  | .node _ _ => by simp [BitTree.negate]
  cost_ale := Program.simpleDivideAndConquerComplexity' _ rfl (le_refl _)

instance: Program.HasCost ↿(Add.add (α := BitTree)) (Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ⊓ Nat.pow 2 ∘ BitTree.height ∘ Prod.snd) where
  program := [
    .move 5 2,
    .costedSubroutine 0 0 ↿BitTree.addWithCarry (Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ⊓ Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ∘ Prod.snd),
    .move 0 2
  ]
  size := 0
  sound _ := by simp [Add.add]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.const_ale
    apply Complexity.ALE.of_le λ
      | (_, _) => by
        simpa [flip, Function.comp] using le_inf inf_le_left inf_le_right


instance: Program.HasCost ↿(Sub.sub (α := BitTree)) (Nat.pow 2 ∘ BitTree.height ∘ Prod.snd) where
  program := [
    .costedSubroutine 2 2 BitTree.negate (Nat.pow 2 ∘ BitTree.height),
    .move 5 2,
    .setv 6 true,
    .costedSubroutine 0 0 ↿BitTree.addWithCarry (Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ⊓ Nat.pow 2 ∘ BitTree.height ∘ Prod.fst ∘ Prod.snd),
    .move 0 2
  ]
  size := 0
  sound _ := by simp [Sub.sub]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.const_ale
    apply Complexity.ALE.of_le λ
      | (_, _) => by
        simp [flip, Function.comp]
        exact le_of_le_of_eq inf_le_right (congrArg (Nat.pow 2) (BitTree.negate_height _))
    apply Complexity.ALE.of_le λ | (_, _) => by simp [flip, Function.comp]

instance: Program.HasCost ↿(BitTree.mulBit) (List.length ∘ Prod.fst) where
  program := [
    .ifOp₂ Bool.and 5 6 [
      .costedSubroutine 0 1 BitTree.one List.length
    ],
    .costedSubroutine 0 1 BitTree.zero List.length
  ]
  size := 0
  sound
  | (_, ⟨0, _⟩, _) => by simp[BitTree.mulBit]
  | (_, ⟨1, _⟩, ⟨0, _⟩) => by simp[BitTree.mulBit]
  | (_, ⟨1, _⟩, ⟨1, _⟩) => by simp[BitTree.mulBit]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.const_ale
    apply Complexity.ALE.of_le λ
      | (_, ⟨0, _⟩, _) => by simp [flip, Function.comp, Complexity.CostFunction.flatMap, Option.filter]
      | (_, ⟨1, _⟩, ⟨0, _⟩) => by simp [flip, Function.comp, Complexity.CostFunction.flatMap, Option.filter]
      | (_, ⟨1, _⟩, ⟨1, _⟩) => by simp [flip, Function.comp, Complexity.CostFunction.flatMap, Option.filter]
    apply Complexity.ALE.of_le λ
      | (_, ⟨0, _⟩, _) => by
        simp [flip, Function.comp, Complexity.CostFunction.flatMap, Option.filter, Trace.CostedProgram.subroutineTimeComplexity]
      | (_, ⟨1, _⟩, ⟨0, _⟩) => by simp [flip, Function.comp, Complexity.CostFunction.flatMap, Option.filter, Trace.CostedProgram.subroutineTimeComplexity]
      | (_, ⟨1, _⟩, ⟨1, _⟩) => by simp [flip, Function.comp, Complexity.CostFunction.flatMap, Option.filter, Trace.CostedProgram.subroutineTimeComplexity]

instance: Program.HasCost ↿(BitTree.mulBit') (List.length ∘ Prod.fst) where
  program := [
    .ifv 5 [
      .move 0 6
    ],
    .costedSubroutine 0 1 BitTree.zero List.length
  ]
  size := 0
  sound
  | (_, ⟨0, _⟩, _) => by simp[BitTree.mulBit']
  | (_, ⟨1, _⟩, _) => by simp[BitTree.mulBit']
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.const_ale
    apply Complexity.ALE.of_le λ
      | (_, ⟨0, _⟩, _) => by simp [flip, Function.comp, Complexity.CostFunction.flatMap, Option.filter, Trace.CostedProgram.subroutineTimeComplexity]
      | (_, ⟨1, _⟩, _)=> by simp [flip, Function.comp, Complexity.CostFunction.flatMap, Option.filter, Trace.CostedProgram.subroutineTimeComplexity]

instance: Program.HasCost BitTree.getBit 1 where
  program := [
    .ifv 0 [ .setm 0 0 ],
    .move 0 1
  ]
  size := 0
  sound x := by cases x <;> simp [BitTree.getBit]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.const_ale

instance: Program.HasCost BitTree.hi 1 where
  program := [
    .ifv 0 [
      .move 0 1
    ],
    .setv 1 false
  ]
  size := 0
  sound x := by cases x <;> simp [BitTree.hi]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.const_ale

instance: Program.HasCost BitTree.lo 1 where
  program := [
    .ifv 0 [
      .move 0 2
    ]
  ]
  size := 0
  sound x := by cases x <;> simp [BitTree.lo]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.const_ale


instance: Program.HasCost ↿BitTree.lshift2 (List.length ∘ Prod.fst) where
  program := [
    .costedSubroutine 4 1 BitTree.zero List.length,
    .costedSubroutine 3 2 BitTree.hi 1,
    .costedSubroutine 3 3 BitTree.lo 1,
    .costedSubroutine 5 2 BitTree.lo 1,
    .costedSubroutine 6 5 BitTree.hi 1,
    .swap 6 4,
    .costedSubroutine 5 5 BitTree.lo 1,
    .setv 2 true,
    .setv 1 true,
    .setv 0 true
  ]
  size := 0
  sound | (_, _) => by simp [BitTree.lshift2]
  cost_ale := by
    apply Program.nonRecursiveComplexity
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.const_ale
    apply Complexity.ALE.const_flatMap_ale
    apply Complexity.ALE.const_flatMap_ale
    apply Complexity.ALE.const_flatMap_ale
    apply Complexity.ALE.const_flatMap_ale
    apply Complexity.ALE.const_flatMap_ale
    apply Complexity.ALE.of_le λ
      | (_, _) => by simp [flip, Function.comp]

instance: Program.HasCost ↿BitTree.mkPerfect (Nat.pow 2 ∘ List.length ∘ Prod.fst) where
  program := [
    .ifv 1 [
      .move 3 4,
      .costedSubroutine 4 2 BitTree.hi 1,
      .setv 1 false,
      .costedSubroutine 6 2 BitTree.lo 1,
      .copy 5 3,
      .setv 2 false,
      .recurse 1 1,
      .recurse 2 2,
      .setv 0 true
    ],
    .costedSubroutine 1 2 BitTree.getBit 1,
    .setm 2 0
  ]
  size := List.length ∘ Prod.fst
  sound | (H, x) => by cases H <;> simp [BitTree.mkPerfect]
  cost_ale := by
    apply Program.simpleDivideAndConquerComplexity
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.add_ale
    apply Complexity.ALE.const_ale
    apply Complexity.ALE.const_flatMap_ale
    apply Complexity.ALE.const_flatMap_ale
    apply Complexity.ALE.of_le λ
      | ([], _) => by
        simp [Trace.CostedProgram.subroutineTimeComplexity, Complexity.CostFunction.flatMap, flip, Function.comp, Option.filter]
        exact le_refl _
      | (_::_, _) => by
        simpa [Trace.CostedProgram.subroutineTimeComplexity] using zero_le _
    exact le_refl _

end HMem.Complexity.Karatsuba
