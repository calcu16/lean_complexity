import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Tree
import Mathlib.Logic.Basic

-- Things that maybe should be put into Mathlib4 (or already exists I didn't find them)
class CanonicallyOrderedLatticeAddCommMonoid (α: Type _) extends Lattice α, CanonicallyOrderedAddCommMonoid α
instance [h: CanonicallyOrderedLatticeAddCommMonoid α]: Lattice α := h.toLattice
instance [h: CanonicallyOrderedLatticeAddCommMonoid α]: CanonicallyOrderedAddCommMonoid α := h.toCanonicallyOrderedAddCommMonoid

instance: CanonicallyOrderedLatticeAddCommMonoid ℕ :=
  { (inferInstance : Lattice ℕ),
    (inferInstance : CanonicallyOrderedAddCommMonoid ℕ) with }

theorem zero_sup [CanonicallyOrderedLatticeAddCommMonoid α] (a : α):
    0 ⊔ a = a := sup_of_le_right (zero_le a)

theorem sup_zero [CanonicallyOrderedLatticeAddCommMonoid α] (a : α):
    a ⊔ 0 = a := sup_of_le_left (zero_le a)

theorem sup_le_add [CanonicallyOrderedLatticeAddCommMonoid α] (a b: α):
    a ⊔ b ≤ a + b := sup_le (le_add_right (le_refl _)) (le_add_left (le_refl _))

noncomputable def distance [CanonicallyOrderedAddCommMonoid α] {a b: α} (h: a ≤ b): α :=
    Classical.choose (exists_add_of_le h)

theorem eq_add_distance [CanonicallyOrderedAddCommMonoid α] {a b: α} (h: a ≤ b):
    b = a + distance h := Classical.choose_spec (exists_add_of_le h)

class CanonicallyOrderedLatticeCommSemiring (α: Type _) extends CanonicallyOrderedLatticeAddCommMonoid α, OrderedCommSemiring α
instance [h: CanonicallyOrderedLatticeCommSemiring α]: CanonicallyOrderedLatticeAddCommMonoid α := h.toCanonicallyOrderedLatticeAddCommMonoid
instance [h: CanonicallyOrderedLatticeCommSemiring α]: OrderedCommSemiring α := h.toOrderedCommSemiring

instance: CanonicallyOrderedLatticeCommSemiring ℕ :=
  { (inferInstance : CanonicallyOrderedLatticeAddCommMonoid ℕ),
    (inferInstance : OrderedCommSemiring ℕ) with }

def Sum.reduce: α ⊕ α → α
| Sum.inl a => a
| Sum.inr a => a

@[simp] theorem List.append_eq_right {α: Type _} {x y: List α}: (x = y ++ x) ↔ ([] = y) :=
  ⟨ λ h ↦ (List.eq_nil_of_length_eq_zero
    (Nat.add_right_cancel (m := List.length x) (Nat.zero_add _ ▸ List.length_append _ _ ▸ congrArg List.length h)).symm).symm,
  λ h ↦ h ▸ rfl ⟩

@[simp] theorem List.cons_eq_append_inj {α: Type _} {a: α} {x z: List α}: (a :: x = z ++ x) ↔ ([a] = z) :=
  ⟨ λ h ↦ (List.append_left_inj _).mp h, λ h ↦ h ▸ rfl ⟩

@[simp] theorem List.cons_append_inj {α: Type _} {a: α} {x y z: List α}: (a :: (y ++ x) = z ++ x) ↔ (a :: y = z) := by
  simp [-List.cons_append, (List.cons_append _ _ _).symm]

@[simp] theorem List.cons₂_append_inj {α: Type _} {a b: α} {x y z: List α}: (a :: b :: (y ++ x) = z ++ x) ↔ (a :: b :: y = z) := by
  simp [-List.cons_append, (List.cons_append _ _ _).symm]

@[simp] theorem Tree.getOrElse_nil: {p: PosNum} → Tree.getOrElse p .nil a = a
| .one => rfl
| .bit0 _ => rfl
| .bit1 _ => rfl

@[simp] theorem Tree.getOrElse_node_one: Tree.getOrElse 1 (.node v lhs rhs) a = v := rfl

def Nat.ofBits: List Bool → ℕ
| [] => 0
| b::bs => bit b (ofBits bs)

@[simp] theorem Nat.ofBits_inverse: (n: ℕ) → ofBits n.bits = n :=
  Nat.binaryRec' rfl λ _ _ h ih ↦
    Nat.bits_append_bit _ _ h ▸ congrArg₂ bit rfl ih

@[simp] theorem Nat.bits_injEq: (Nat.bits n = Nat.bits m) = (n = m) :=
  eq_iff_iff.mpr ⟨
    λ h ↦ Nat.ofBits_inverse n ▸ Nat.ofBits_inverse m ▸ congrArg Nat.ofBits h,
    λ h ↦ h ▸ rfl ⟩

theorem Nat.bit_div_2: (Nat.bit b n) / 2 = n := by
  set_option linter.deprecated false in
  cases b <;> dsimp [bit, bit0, bit1] <;> omega

def List.getN (N: ℕ) (as: List α): Option (Fin N → α) :=
  if h: N ≤ as.length
  then some (λ n ↦ as.get ⟨n.val, lt_of_lt_of_le n.isLt h⟩)
  else none

@[simp] theorem List.getN_ofFn {f: Fin N → α}: List.getN N (List.ofFn f) = f :=
  (dif_pos (List.length_ofFn _ ▸ le_refl _)).trans
  (congrArg some (funext λ _ ↦ get_ofFn _ _))

@[simp] theorem Option.bind_comp_some:
    (λ a ↦ Option.bind a f) ∘ (some ∘ g) = f ∘ g :=
  funext λ _ ↦ rfl

@[simp] theorem id_def: (λ (a: α) ↦ a) = id := rfl

theorem lambda_comp {f: α → β}: (λ a ↦ f a) ∘ g = λ a ↦ (f (g a)) := funext λ _ ↦ rfl

@[simp] theorem Function.HasUncurry.apply₂ (f: α → β → γ) (arg: α × β):
    (↿f) arg = f arg.fst arg.snd := rfl

@[simp] theorem Function.HasUncurry.apply₃ (f: α → β → γ → δ) (arg: α × β × γ):
    (↿f) arg = f arg.fst arg.snd.fst arg.snd.snd := rfl

@[simp] theorem Nat.one_div_two: 1 / 2 = 0 := rfl
@[simp] theorem Nat.add_one_add_one: n + 1 + 1 = n + 2 := rfl
@[simp] theorem Nat.pred_lt_iff: n - 1 < n ↔ n ≠ 0 := by cases n <;> simp

attribute [simp] bit0 bit1
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

@[simp] theorem Nat.div2_succ_succ: (n + 1 + 1) / 2 = n / 2 + 1 := Nat.add_div_right _ zero_lt_two

theorem Nat.mod_mul {a b c: ℕ}: a % (b * c) = b * ((a / b) % c) + a % b := by
  match b with
  | 0 => simp
  | b + 1 =>
    match c with
    | 0 => simp[Nat.div_add_mod]
    | c + 1 =>
      apply Eq.trans
      apply congrArg₂ _ (Nat.div_add_mod a (b + 1)).symm rfl
      apply Eq.trans
      apply Nat.add_mod
      apply Eq.trans
      exact congrArg₂ _ (congrArg₂ _ (Nat.mul_mod_mul_left _ _ _) (Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.zero_lt_succ _)) (Nat.le_mul_of_pos_right (Nat.zero_lt_succ _))))) rfl
      apply Nat.mod_eq_of_lt
      apply Nat.lt_of_succ_le
      apply le_trans
      apply Nat.succ_le_succ
      apply add_le_add
      apply Nat.mul_le_mul_left
      apply Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.zero_lt_succ _))
      apply Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.zero_lt_succ _))
      simp [Nat.succ_eq_add_one, left_distrib, right_distrib, ← add_assoc]

theorem Nat.add_size_le: size x + size y ≤ 2 * size (x + y) :=
  Nat.two_mul _ ▸ add_le_add
    (size_le_size (le_add_right _ _))
    (size_le_size (le_add_left _ _))

def Bool.majoritySelect (a b c: Bool): Bool := a ∧ b ∨ a ∧ c ∨ b ∧ c
def Bool.xor₃ (a b c: Bool): Bool := xor a (xor b c)

@[simp] theorem Bool.majoritySelect_fin: (a b c: Fin 2) → majoritySelect (a.val = 1) (b.val = 1) (c.val = 1) = (decide ((a.val + b.val + c.val) / 2 = 1))
| 0, 0, 0 => by decide
| 0, 0, 1 => by decide
| 0, 1, 0 => by decide
| 0, 1, 1 => by decide
| 1, 0, 0 => by decide
| 1, 0, 1 => by decide
| 1, 1, 0 => by decide
| 1, 1, 1 => by decide

@[simp] theorem Bool.xor₃_fin: (a b c: Fin 2) → xor₃ (a.val = 1) (b.val = 1) (c.val = 1) = (decide ((a.val + b.val + c.val) % 2 = 1))
| 0, 0, 0 => by decide
| 0, 0, 1 => by decide
| 0, 1, 0 => by decide
| 0, 1, 1 => by decide
| 1, 0, 0 => by decide
| 1, 0, 1 => by decide
| 1, 1, 0 => by decide
| 1, 1, 1 => by decide


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

theorem Nat.pred_size_eq_log: size n - 1 = log 2 n := by
  refine binaryRec' (n := n) rfl ?hi
  intro b n hb ih
  cases n
  cases b <;> rfl
  rw [size_bit, bit_val, Nat.log_mul_add, Nat.succ_eq_add_one, Nat.add_sub_cancel, ← ih, Nat.sub_add_cancel]
  exact tsub_add_cancel_iff_le.mp rfl
  exact one_lt_two
  exact Nat.succ_le_succ (Nat.zero_le _)
  { cases b <;> simp }
  { simp }

theorem Nat.size_succ_eq_succ_log_succ: size (n + 1) = log 2 (n + 1) + 1 := by
  rw [← Nat.pred_size_eq_log, Nat.sub_add_cancel]
  exact tsub_add_cancel_iff_le.mp rfl

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

@[simp] theorem Nat.size_bit1': Nat.size (2 * n + 1) = Nat.size n + 1 :=
  (congrArg _ (Nat.bit_val true _).symm).trans
  (Nat.binaryRec_eq' _ _ (Or.inr λ _ ↦ rfl))

theorem Nat.size_le_self: Nat.size n ≤ n := by
  induction n using Nat.binaryRec' with
  | z => exact le_refl _
  | f b n hb ih =>
    rw [size_bit]
    cases b
    simp
    apply Nat.add_le_add (c := 1) ih
    { cases n
      exact absurd (hb rfl) Bool.noConfusion
      exact Nat.succ_le_succ (Nat.zero_le _) }
    simp
    apply Nat.succ_le_succ
    apply le_trans
    apply ih
    apply le_add_left
    cases b
    simpa using λ h ↦ absurd (hb h) Bool.noConfusion
    simp
