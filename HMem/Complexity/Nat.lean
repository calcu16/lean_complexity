import HMem.Complexity.Def
import HMem.Complexity.Basic

attribute [simp] bit0 bit1

-- @[simp] theorem decode_zero: Complexity.decode ℕ (0:HMem.Memory) = some 0 := rfl
theorem decode_nat: Complexity.decode ℕ (m:HMem.Memory) = Option.map Nat.ofBits (Complexity.decode (List Bool) m) := rfl
@[simp] theorem decode_nil [Complexity.Encoding α HMem.Memory]: Complexity.decode (List α) (0:HMem.Memory) = some [] := rfl
@[simp] theorem decode_cons [Complexity.Encoding α HMem.Memory]: Complexity.decode (List α) (HMem.Memory.mk true hd tl) =
  Option.map₂ List.cons (Complexity.decode α hd) (Complexity.decode _ tl) :=
    congrArg₂ (Option.map₂ List.cons)
      (congrArg _ (HMem.Memory.canonical_out.symm ▸ HMem.Memory.out_sound))
      (HMem.Memory.canonical_out.symm ▸ rfl)

@[simp] theorem decode_zero: Complexity.decode ℕ (0:HMem.Memory) = some 0 := rfl
@[simp] theorem decode_succ: Complexity.decode ℕ (HMem.Memory.mk true hd tl) = Option.map (λ n ↦ 2 * n + Bool.toNat hd.getv) (Complexity.decode ℕ tl) := by
  simp [decode_nat]
  apply congrArg₂ Option.map _ rfl
  apply funext
  intro xs
  simp [Nat.ofBits]
  match HMem.Memory.getv hd with
  | true => simp [← Nat.two_mul]
  | false => simp [← Nat.two_mul]

@[simp] theorem encode_zero: Complexity.encode (0:ℕ) = (0:HMem.Memory) := rfl
@[simp] theorem one_div_two: 1 / 2 = 0 := rfl
@[simp] theorem size_bit1: Nat.size (2 * n + 1) = Nat.size n + 1 :=
  (congrArg _ (Nat.bit_val true _).symm).trans
  (Nat.binaryRec_eq' _ _ (Or.inr λ _ ↦ rfl))
@[simp] theorem add_one_add_one: n + 1 + 1 = n + 2 := rfl
@[simp] theorem pred_lt_iff: n - 1 < n ↔ n ≠ 0 := by cases n <;> simp

@[simp] theorem Nat.size_div2: size (n / 2) = size n - 1 := by
  induction n using Nat.binaryRec' with
  | z => rfl
  | _ _ _ h =>
    rw [bit_div_2, size_bit]
    apply Eq.symm
    apply Nat.pred_succ
    apply bit_ne_zero_iff.mpr h


@[simp] theorem Nat.size_ne_zero: (¬ size n = 0) ↔ ¬ n = 0 :=
  ⟨ mt Nat.size_eq_zero.mpr, mt Nat.size_eq_zero.mp ⟩

@[simp] theorem div2_succ_succ: (n + 1 + 1) / 2 = n / 2 + 1 := Nat.add_div_right _ zero_lt_two

theorem Nat.add_size_le: size x + size y ≤ 2 * size (x + y) :=
  Nat.two_mul _ ▸ add_le_add
    (size_le_size (le_add_right _ _))
    (size_le_size (le_add_left _ _))


-- @[simp] theorem Nat.mul_div_self {n m: ℕ}: m * (n / m) = n - (n % m) :=
--   Nat.add_right_cancel_iff.mp ((div_add_mod n m).trans (Nat.sub_add_cancel (mod_le n m)).symm)

def Bool.majoritySelect (a b c: Bool): Bool := a ∧ b ∨ a ∧ c ∨ b ∧ c
def Bool.xor₃ (a b c: Bool): Bool := xor a (xor b c)

@[simp] theorem Nat.not_mod2_eq_zero: (¬ (n % 2 = 0)) ↔ (n % 2 = 1) := by
  cases n using binaryRec with
  | z => simp
  | f b _ _ => cases b <;> simp [← Nat.two_mul, Nat.mul_add_mod]


theorem Nat.log_mul (hb: 1 < b) (hn: 1 ≤ n): Nat.log b (b * n) = Nat.log b n + 1 := by
  apply le_antisymm
  apply le_of_eq_of_le
  apply Nat.log_of_one_lt_of_le hb
  apply le_of_eq_of_le
  apply (mul_one _).symm
  apply mul_le_mul (le_refl _) hn (zero_le _) (zero_le _)
  apply Nat.succ_le_succ
  apply Nat.log_mono_right
  apply le_of_eq
  rw [Nat.mul_div_right _ (lt_trans zero_lt_one hb)]
  apply Nat.le_log_of_pow_le hb
  rw [Nat.pow_succ, mul_comm]
  apply mul_le_mul
  apply le_refl
  apply Nat.pow_log_le_self
  apply ne_of_lt' (Nat.lt_of_succ_le hn)
  apply zero_le
  apply zero_le

theorem Nat.log_mul_add (hb: 1 < b) (hn: 1 ≤ n) (hc: c < b): Nat.log b (b * n + c) = Nat.log b n + 1 := by
  apply le_antisymm
  apply le_of_eq_of_le
  apply Nat.log_of_one_lt_of_le hb
  apply add_le_add _ (zero_le _)
  apply le_of_eq_of_le
  apply (mul_one _).symm
  apply mul_le_mul (le_refl _) hn (zero_le _) (zero_le _)
  apply Nat.succ_le_succ
  apply Nat.log_mono_right
  apply le_of_eq
  apply Eq.trans
  apply Nat.mul_add_div (lt_trans zero_lt_one hb)
  apply congrArg _ (Nat.div_eq_of_lt hc)
  apply le_trans
  rw [← Nat.log_mul hb hn]
  apply Nat.log_mono_right
  apply le_add_right

theorem Nat.size_le_succ_log: size n ≤ (log 2 n) + 1 := by
  refine binaryRec' (n := n) ?hz ?hi
  exact zero_le _
  intro b n hb ih
  cases n
  cases b <;> simp
  rw [size_bit, bit_val, Nat.log_mul_add]
  apply Nat.succ_le_succ ih
  apply one_lt_two
  apply Nat.succ_le_succ (zero_le _)
  cases b <;> simp
  cases b <;> simp

@[simp] theorem Nat.mod2_succ_eq_one: (n + 1) % 2 = 1 ↔ n % 2 = 0 := by
  cases n using binaryRec with
  | z => simp
  | f b _ _ => cases b <;> simp [← Nat.two_mul, Nat.mul_add_mod]

@[simp] theorem Nat.mod2_succ_eq_zero: (n + 1) % 2 = 0 ↔ n % 2 = 1 := by
  cases n using binaryRec with
  | z => simp
  | f b _ _ => cases b <;> simp [← Nat.two_mul, Nat.mul_add_mod]

@[simp] theorem Nat.bnot_mod2_eq_zero: (!decide (n % 2 = 0)) = decide (n % 2 = 1) := by
  cases n using binaryRec with
  | z => simp
  | f b _ _ => cases b <;> simp [← Nat.two_mul, Nat.mul_add_mod]

@[simp] theorem Nat.toNat_decide_mod2: Bool.toNat (decide (n % 2 = 0)) = (n + 1) % 2 := by
  cases n using binaryRec with
  | z => simp
  | f b _ _ => cases b <;> simp [← Nat.two_mul, Nat.mul_add_mod]

@[simp] theorem Nat.xor_mod2₀₀: Bool.xor (decide (n % 2 = 0)) (decide (m % 2 = 0)) = decide ((n + m) % 2 = 1) := by
  cases n using binaryRec with
  | z => simp
  | f b _ _ =>
    cases m using binaryRec with
    | z => cases b <;> simp [← Nat.two_mul]
    | f c _ _ =>
      cases b <;> cases c <;> simp [← Nat.two_mul, Nat.mul_add_mod, ← Nat.add_assoc]

@[simp] theorem Nat.xor_mod2₀₁: Bool.xor (decide (n % 2 = 0)) (decide (m % 2 = 1)) = decide ((n + m) % 2 = 0) := by
  cases m using binaryRec with
  | z => simp
  | f b _ _ =>
    cases n using binaryRec with
    | z => cases b <;> simp [← Nat.two_mul]
    | f c _ _ =>
      cases b <;> cases c <;> simp [← Nat.two_mul, Nat.mul_add_mod, ← Nat.add_assoc]

@[simp] theorem Nat.div_mod2: n / 2 + n % 2 = (n + 1) / 2 := by
  induction n using Nat.binaryRec' with
  | z => rfl
  | f b _ _ _ => cases b <;> simp [bit_val, mul_add_div, mul_add_mod]

@[elab_as_elim]
theorem Nat.parityZeroCases {C : Nat → Sort u} (z : C 0) (o : ∀ n, C (2 * n + 1)) (e : ∀ n, C (2 * n + 2)): ∀ n, C n := by
  intro n
  cases n using Nat.binaryRec' with
  | z => exact z
  | f b n hb =>
    cases b with
    | true => simpa [← Nat.two_mul] using o _
    | false =>
      match n with
      | 0 => exact absurd (hb rfl) Bool.noConfusion
      | n+1 => simpa [← Nat.add_assoc, Nat.add_right_comm _ 1, ← Nat.two_mul] using e _


theorem Nat.size_mul2_lt (h: n ≠ 0): Nat.size (2 * n) = Nat.size n + 1 :=
  ((congrArg _ (two_mul _)).trans (size_bit0 h))

@[simp] theorem Nat.size_mul2_lt': Nat.size (2 * n + 2) = Nat.size (n + 1) + 1:=
  (congrArg _ (Nat.mul_succ _ _).symm).trans (Nat.size_mul2_lt (Nat.succ_ne_zero _))

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
      by cases b <;> simp [← Nat.two_mul, Nat.mul_add_mod, Nat.mul_add_div]
  cost_ale := Complexity.ALE.trans
    (Program.simpleLoopComplexity (Complexity.ALE.const_ale _ _) rfl)
    ⟨_, _, λ _ ↦ le_of_le_of_eq Nat.size_le_succ_log (congrArg₂ _ (one_mul _).symm rfl) ⟩

def Nat.AddWithCarry (x y: ℕ) (c: Bool): ℕ := x + y + Bool.toNat c

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
    apply Complexity.ale_of_le
    intro arg
    match arg with
    | (x, y) =>
      apply le_of_eq
      apply Eq.trans
      apply Nat.zero_add
      simp [flip, Complexity.CostFunction.flatMap]

end HMem.Complexity.Nat
