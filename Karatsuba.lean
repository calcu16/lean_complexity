import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

theorem Nat.mul_lt_mul_for_real {a b x y: ℕ} (hax: a < x) (hby: b < y): a * b < x * y :=
  Nat.lt_of_succ_le (le_trans
    (Nat.succ_le_of_lt (lt_of_lt_of_eq
      (Nat.lt_add_of_pos_right (Nat.lt_add_left _ (Nat.zero_lt_succ _)))
    ((Nat.mul_succ _ _).trans
      ((congrArg₂ _ (Nat.succ_mul _ _) rfl).trans
      (Nat.add_assoc _ _ _))).symm))
    (Nat.mul_le_mul
      (Nat.le_of_lt_succ (Nat.succ_lt_succ hax))
      (Nat.le_of_lt_succ (Nat.succ_lt_succ hby))))

def Unary.max: List Unit → List Unit → List Unit
| [], ys => ys
| ()::xs, [] => ()::xs
| ()::xs, ()::ys => ()::(max xs ys)

theorem Unary.length_max: (xs ys: List Unit) → (Unary.max xs ys).length = Nat.max xs.length ys.length
| [], _ => Eq.symm (Nat.zero_max _)
| ()::_, [] => Eq.symm (Nat.max_zero _)
| ()::_, ()::_ => (congrArg Nat.succ (Unary.length_max _ _)).trans (Nat.succ_max_succ _ _).symm

inductive BitTree: List Unit → Type _ where
| bit (b: Fin 2): BitTree []
| node {H: List Unit} (hi lo: BitTree H): BitTree (()::H)
deriving Repr

namespace BitTree

def getHeight (n: ℕ): List Unit := List.replicate n.size.size ()

def hi: BitTree (()::H) → BitTree H
| node hi _ => hi

def lo: BitTree (()::H) → BitTree H
| node _ lo => lo

def height: List Unit → ℕ := List.length
def width: List Unit → ℕ := Nat.pow 2 ∘ height
def bound: List Unit → ℕ := Nat.pow 2 ∘ width

theorem bound_pos (H: List Unit): 0 < bound H := Nat.pow_two_pos _
theorem two_le_bound (H: List Unit): 2 ≤ bound H :=
  (Nat.pow_le_pow_right zero_lt_two (Nat.pow_le_pow_right zero_lt_two (Nat.zero_le _)))

theorem bound_le_bound {H G: List Unit} (h: H.length ≤ G.length): bound H ≤ bound G :=
  Nat.pow_le_pow_right zero_lt_two (Nat.pow_le_pow_right zero_lt_two h)
theorem bound_le_cons (H: List Unit): bound H ≤ bound (()::H) :=
  bound_le_bound (Nat.le_succ _)

theorem bound_cons (H: List Unit): bound (()::H) = bound H * bound H :=
  (((congrArg _ (Nat.pow_succ _ _)).trans (Nat.pow_mul _ _ _)).trans (Nat.pow_two _))


theorem lt_bound_getHeight: n < bound (getHeight n) :=
  lt_of_lt_of_eq (lt_of_lt_of_le
    (Nat.lt_size_self _)
    (Nat.pow_le_pow_right (zero_lt_two) (le_of_lt (Nat.lt_size_self _))))
    (congrArg (λ n ↦ 2 ^ 2 ^ n) (List.length_replicate _ _).symm)

theorem add_lt_mul_bound (ha: a ≤ x) (hb: b < x): a + b < x * bound H :=
  lt_of_lt_of_le (add_lt_add_of_le_of_lt ha hb) (le_of_eq_of_le
    (mul_two _).symm
    (Nat.mul_le_mul (le_refl _) (two_le_bound _)))

theorem add_le_mul_bound (ha: a ≤ x) (hb: b ≤ x): a + b ≤ x * bound H :=
  le_trans (add_le_add ha hb) (le_of_eq_of_le
    (mul_two _).symm
    (Nat.mul_le_mul (le_refl _) (two_le_bound _)))

def zero: (H: List Unit) → BitTree H
| [] => bit 0
| _::H => node (zero H) (zero H)

def one: (H: List Unit) → BitTree H
| [] => bit 1
| _::H => node (zero H) (one H)

instance: Zero (BitTree H) := ⟨ zero _ ⟩
instance: One (BitTree H) := ⟨ one _ ⟩

def ofNat: (H: List Unit) → ℕ → BitTree H
| [], n => bit ⟨ n % 2, Nat.mod_lt _ zero_lt_two⟩
| _::H, n => node (ofNat H (n / bound H)) (ofNat H (n % bound H))

def toNat: {H: List Unit} → BitTree H → ℕ
| _, bit b => b.val
| _, @node H hi lo => bound H * (toNat hi)  + toNat lo

def toNat_node {H: List Unit} (x y: BitTree H): toNat (node x y) = bound H * (toNat x)  + toNat y := rfl

theorem toNat_zero: {H: List Unit} → @toNat H 0 = 0
| [] => rfl
| _::_ => congrArg₂ _ (congrArg _ toNat_zero) toNat_zero

theorem toNat_one: {H: List Unit} → @toNat H 1 = 1
| [] => rfl
| _::_ => congrArg₂ _ (congrArg _ toNat_zero) toNat_one

theorem ofNat_zero: {H: List Unit} → ofNat H 0 = 0
| [] => rfl
| _::_ => congrArg₂ _
  ((congrArg _ (Nat.zero_div _)).trans ofNat_zero)
  ((congrArg _ (Nat.zero_mod _)).trans ofNat_zero)

theorem ofNat_one: {H: List Unit} → @ofNat H 1 = 1
| [] => rfl
| _::_ => congrArg₂ node
    ((congrArg _ ((Nat.div_eq_zero_iff (bound_pos _)).mpr (Nat.lt_of_succ_le (two_le_bound _)))).trans ofNat_zero)
    ((congrArg _ (Nat.mod_eq_of_lt (Nat.lt_of_succ_le (two_le_bound _)))).trans ofNat_one)

theorem toNat_lt: {H: List Unit} → (x: BitTree H) → x.toNat < bound H
| _, bit b => b.isLt
| _, node _ _ => Nat.lt_of_succ_le (le_of_le_of_eq (add_le_add (add_le_add
      (mul_le_mul
        (le_refl _)
        (Nat.le_of_lt_succ (lt_of_lt_of_le
          (toNat_lt _)
          (le_of_eq (Nat.succ_pred (Nat.not_eq_zero_of_lt (bound_pos _))).symm)))
         (zero_le _) (zero_le _))
    (Nat.le_of_lt_succ (lt_of_lt_of_le
      (toNat_lt _)
      (le_of_eq (Nat.succ_pred (Nat.not_eq_zero_of_lt (bound_pos _))).symm))))
    (le_refl 1))
    ((Nat.add_assoc _ _ _).trans
        ((congrArg₂ _ ((Nat.mul_sub_left_distrib _ _ 1).trans (congrArg _ (mul_one _))) (Nat.sub_add_cancel (Nat.pow_two_pos _))).trans
        ((Nat.sub_add_cancel (Nat.le_mul_self _)).trans
        (bound_cons _).symm))))

theorem toNat_le_pred (x: BitTree H): x.toNat ≤ bound H - 1 := Nat.le_sub_of_add_le (Nat.succ_le_of_lt (toNat_lt _))

theorem toNat_hi (hi lo: BitTree H): toNat (node hi lo) / bound H = toNat hi :=
  (Nat.mul_add_div (bound_pos _) _ _).trans
  (congrArg₂ _ rfl (Nat.div_eq_of_lt (toNat_lt _)))

theorem toNat_hi': (x: BitTree (()::H)) → toNat (hi x) = toNat x / bound H
| node _ _ => (toNat_hi _ _).symm

theorem toNat_lo (hi lo: BitTree H): toNat (node hi lo) % bound H = toNat lo :=
  (Nat.mul_add_mod _ _ _).trans (Nat.mod_eq_of_lt (toNat_lt _))

theorem toNat_lo': (x: BitTree (()::H)) → toNat (lo x) = toNat x % bound H
| node _ _ => (toNat_lo _ _).symm

theorem ofNat_toNat: {H: List Unit} → (x: BitTree H) → ofNat H (toNat x) = x
| _, bit 0 => rfl
| _, bit 1 => rfl
| _, node _ _ => congrArg₂ _
  ((congrArg _ (toNat_hi _ _)).trans (ofNat_toNat _))
  ((congrArg _ (toNat_lo _ _)).trans (ofNat_toNat _))

theorem toNat_inj {x y: BitTree H} (h: toNat x = toNat y): x = y :=
  ofNat_toNat x ▸ h ▸ ofNat_toNat y

theorem ofNat_mul_add {H: List Unit} (n: ℕ) {m: ℕ} (hm: m < bound H): ofNat _ (bound H * n + m) = node (ofNat H n) (ofNat H m) :=
  congrArg₂ _
    (congrArg _ (
      (Nat.mul_add_div (bound_pos _) _ _).trans
      (congrArg _ (Nat.div_eq_of_lt hm))))
    (congrArg _ (
      (Nat.mul_add_mod _ _ _).trans
      (Nat.mod_eq_of_lt hm)))

theorem ofNat_mod (n: ℕ): (H: List Unit) → ofNat H (n % bound H) = ofNat H n
| [] => congrArg bit (Fin.eq_of_val_eq ((congrArg₂ _ (congrArg _ (pow_one _)) rfl).trans (Nat.mod_mod _ _)))
| _::_ => congrArg₂ node
  ((congrArg _ ((congrArg₂ _ (congrArg _ (bound_cons _)) rfl).trans
    (Nat.div_mod_eq_mod_mul_div _ _ _).symm)).trans (ofNat_mod _ _))
    (congrArg _ ((congrArg₂ _ (congrArg _ (bound_cons _)) rfl).trans
      (Nat.mod_mul_left_mod _ _ _)))

theorem ofNat_mul_add_mod (H: List Unit) (n m: ℕ): ofNat _ (bound H * n + m % bound H) = node (ofNat H n) (ofNat H m) :=
  (ofNat_mul_add _ (Nat.mod_lt _ (bound_pos _))).trans (congrArg _ (ofNat_mod _ _))

theorem ofNat_modInj (h: n % bound H = m % bound H): ofNat H n = ofNat H m :=
  ((ofNat_mod _ _).symm.trans (congrArg _ h)).trans (ofNat_mod _ _)

theorem toNat_ofNat: (H: List Unit) → (n: ℕ) → toNat (ofNat H n) = n % (bound H)
| [], _ => rfl
| _::_, _ =>
  ((Nat.mod_eq_of_lt (toNat_lt _)).symm.trans
  ((congrArg₂ _ (congrArg₂ _
    (congrArg _ ((toNat_ofNat _ _)))
    ((toNat_ofNat _ _).trans (Nat.mod_mod _ _))) rfl).trans
  (((Nat.add_mod _ _ _).trans (congrArg₂ _
    (congrArg₂ _
      ((congrArg _ (bound_cons _)).trans (Nat.mul_mod_mul_left _ _ _))
      (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
        (Nat.mod_lt _ (bound_pos _))
        (bound_le_cons _))))
      rfl)).symm.trans
  (congrArg₂ _ (Nat.div_add_mod _ _) rfl))))

theorem ofNat_modCongr (h: ofNat H n = ofNat H m): n % bound H = m % bound H :=
  ((toNat_ofNat _ _).symm.trans (congrArg toNat h)).trans (toNat_ofNat _ _)

def addWithCarry: {H: List Unit} → BitTree H → BitTree H → Fin 2 → Fin 2 × BitTree H
| _, .bit x, bit y, c => (⟨
    (x.val + y.val + c.val) / 2,
      Nat.div_lt_of_lt_mul (Nat.lt_succ_of_le (Nat.add_le_add (d := 1) (Nat.add_le_add (b := 1) (d := 1)
        (Nat.le_of_lt_succ x.isLt)
        (Nat.le_of_lt_succ y.isLt))
        (Nat.le_of_lt_succ c.isLt)))⟩,
    .bit ⟨(x.val + y.val + c.val) % 2,
      Nat.mod_lt _ zero_lt_two⟩)
| _, .node xhi xlo, .node yhi ylo, c =>
  have rlo := addWithCarry xlo ylo c
  have rhi := addWithCarry xhi yhi rlo.fst
  (rhi.fst, .node rhi.snd rlo.snd)


theorem addWithCarry_eq_ofNat_add: {H: List Unit} → (x y: BitTree H) → (c: Fin 2) →
  addWithCarry x y c = (
    ⟨(x.toNat + y.toNat + c.val) / bound H,
      Nat.div_lt_of_lt_mul (lt_of_le_of_lt (le_of_le_of_eq
        (add_le_add (add_le_add (toNat_le_pred _) (toNat_le_pred _)) (Nat.le_of_lt_succ c.isLt))
        ((add_assoc _ _ _).trans
          ((congrArg _ (Nat.sub_add_cancel (bound_pos _))).trans
          ((congrArg₂ _ (mul_two _) rfl).trans (Nat.sub_add_comm (bound_pos _))).symm)))
        (Nat.sub_lt (Nat.mul_pos (bound_pos _) zero_lt_two) zero_lt_one))⟩,
    ofNat H (x.toNat + y.toNat + c.val)
  )
| _, .bit _, .bit _, _ => rfl
| _, .node _ _, .node _ _, _ =>
  have rearrange: ∀ {m xh xl yh yl c},
    m * xh + xl + (m * yh + yl) + c =
    m * (xh + yh) + (xl + yl + c) := by intro _ _ _ _ _ _; ring
  congrArg₂ Prod.mk
    ((congrArg _ ((congrArg _ (congrArg _ (addWithCarry_eq_ofNat_add _ _ _))).trans
      (addWithCarry_eq_ofNat_add _ _ _))).trans
      (Fin.eq_of_val_eq (((congrArg₂ _ ((congrArg₂ _ rearrange rfl).trans
      (Nat.mul_add_div (bound_pos _) _ _)).symm rfl).trans
      (Nat.div_div_eq_div_mul _ _ _)).trans
      (congrArg _ (bound_cons _).symm))))
    (congrArg₂ node
      ((congrArg _ ((congrArg _ (congrArg _ (addWithCarry_eq_ofNat_add _ _ _))).trans
        (addWithCarry_eq_ofNat_add _ _ _))).trans
        (congrArg (ofNat _) ((congrArg₂ _ rearrange rfl).trans
        (Nat.mul_add_div (bound_pos _) _ _)).symm))
      ((congrArg _ (addWithCarry_eq_ofNat_add _ _ _)).trans
        (((congrArg _ ((Nat.add_mod _ _ _).trans
          ((congrArg₂ _ (congrArg₂ _ ((Nat.add_mod _ _ _).trans
            (congrArg₂ _ (congrArg₂ _ (toNat_lo _ _) (toNat_lo _ _)) rfl)) rfl) rfl).trans
              (Nat.add_mod _ _ _).symm))).trans (ofNat_mod _ _)).symm)))

theorem addWithCarry_eq_add {H: List Unit} (x y: BitTree H) (c: Fin 2):
    bound H * (addWithCarry x y c).fst.val + (addWithCarry x y c).snd.toNat = x.toNat + y.toNat + c.val :=
    (congrArg₂ _
      (congrArg _ (Fin.val_eq_of_eq
        (Prod.mk.inj (addWithCarry_eq_ofNat_add x y c)).left))
      ((congrArg _ (Prod.mk.inj
        (addWithCarry_eq_ofNat_add x y c)).right).trans
        (toNat_ofNat _ _))).trans
    (Nat.div_add_mod _ (bound H))

def negate: {H: List Unit} → BitTree H → BitTree H
| _, bit b => bit ⟨ 1 - b.val, Nat.sub_lt_left_of_lt_add (Nat.le_of_lt_succ (Fin.isLt _)) (Nat.lt_add_left _ (Nat.succ_lt_succ zero_lt_one)) ⟩
| _, node hi lo => node (negate hi) (negate lo)

theorem addWithCarry_negate: {H: List Unit} → (x: BitTree H) → addWithCarry x (negate x) 1 = (1, ofNat H 0)
| _, bit 0 => rfl
| _, bit 1 => rfl
| _, node _ _ => congrArg₂ Prod.mk
  ((congrArg _ ((congrArg _ (congrArg Prod.fst (addWithCarry_negate _))).trans (addWithCarry_negate _))))
  (congrArg₂ _
    ((congrArg _ ((congrArg _ (congrArg Prod.fst (addWithCarry_negate _))).trans
      (addWithCarry_negate _))).trans
      (congrArg (ofNat _) (Nat.zero_div _).symm))
    ((congrArg _ (addWithCarry_negate _)).trans
      (congrArg (ofNat _) (Nat.zero_mod _).symm)))

theorem add_toNat_negate: {H: List Unit} → (x: BitTree H) → x.toNat + (negate x).toNat + 1 = bound H
| _, bit 0 => rfl
| _, bit 1 => rfl
| _, node _ _ =>
  have rearrange : ∀ {m a b c d e: ℕ},
    m * a + b + (m * c + d) + e = m * (a + c) + (b + d + e) := by
    intro _ _ _ _ _ _; ring
  rearrange.trans
  ((congrArg _ (add_toNat_negate _)).trans
  ((Nat.mul_succ _ _).symm.trans
  ((congrArg _ (add_toNat_negate _)).trans
  (bound_cons _).symm)))

def mulBit (H: List Unit): Fin 2 → Fin 2 → BitTree H
| 0, _ => 0
| 1, 0 => 0
| 1, 1 => 1

theorem mulBit_ofNat: (H: List Unit) → (x y: Fin 2) → mulBit H x y = ofNat _ (x.val * y.val)
| _, 0, 0 => ofNat_zero.symm
| _, 0, 1 => ofNat_zero.symm
| _, 1, 0 => ofNat_zero.symm
| _, 1, 1 => ofNat_one.symm

def mulBit': Fin 2 → BitTree H → BitTree H
| 0, _ => 0
| 1, x => x

theorem mulBit'_ofNat {H: List Unit}: {x: Fin 2} → (y: BitTree H) → mulBit' x y = ofNat _ (x.val * toNat y)
| 0, _ => ((congrArg _ (zero_mul _)).trans ofNat_zero).symm
| 1, _ => ((congrArg _ (one_mul _)).trans (ofNat_toNat _)).symm

instance: Add (BitTree H) := ⟨ λ x y ↦ (addWithCarry x y 0).snd ⟩
instance: Sub (BitTree H) := ⟨ λ x y ↦ (addWithCarry x (negate y) 1).snd ⟩

theorem add_toNat (x y: BitTree H): x + y = ofNat _ (x.toNat + y.toNat) :=
  congrArg Prod.snd (addWithCarry_eq_ofNat_add _ _ _)

theorem sub_toNat (x y: BitTree H): x - y = ofNat _ (x.toNat + bound H - y.toNat) :=
  have rearrange: ∀ {a b c d: ℕ}, a + b + c + d = a + (d + b + c) := by intro _ _ _ _; ring
  (congrArg Prod.snd (addWithCarry_eq_ofNat_add _ _ _)).trans
  (congrArg (ofNat H) (Nat.sub_eq_of_eq_add
    (rearrange.trans (congrArg _ (add_toNat_negate _))).symm).symm)

def lshift2 {H: List Unit}: BitTree (()::()::H) → BitTree (()::()::H)
| node (node _ hi) (node md lo) => node (node hi md) (node lo 0)

theorem lshift2_toNat: (x: BitTree (()::()::H)) → x.lshift2.toNat = (x.toNat * bound H) % (bound (()::()::H))
| node (node _ _) (node _ _) => (Nat.mod_eq_of_lt (toNat_lt _)).symm.trans
  (by simp only [
    toNat, lshift2, bound_cons,
    left_distrib, right_distrib, ← mul_assoc,
    mul_right_comm _ _ (bound H), mul_comm (toNat _) (bound H),
    Nat.add_assoc, Nat.mul_add_mod,
    toNat_zero, add_zero])

def karatsubaHelper₃ (xy: BitTree (()::H)):
  (Fin 2 × BitTree H) →  (Fin 2 × BitTree H) → BitTree (()::()::H)
| (xc, x), (yc, y) =>
  node (mulBit _ xc yc) xy +
  node 0 (node (mulBit' xc y) 0) +
  node 0 (node (mulBit' yc x) 0)

theorem karatsubaHelper₃_toNat: (xy: BitTree (()::H)) → (x: Fin 2 × BitTree H) →  (y: Fin 2 × BitTree H) →
  xy.toNat = x.snd.toNat * y.snd.toNat → (karatsubaHelper₃ xy x y).toNat = (bound H * x.fst.val + x.snd.toNat) * (bound H * y.fst.val + y.snd.toNat)
| xy, (xc, x), (yc, y), h => by
  have h₀: ∀ {x y: Fin 2} {H: List Unit}, x.val * y.val % (bound H * bound H) = x.val * y.val :=
    Nat.mod_eq_of_lt (Nat.mul_lt_mul_for_real
      (lt_of_lt_of_le (Fin.isLt _) (two_le_bound _))
      (lt_of_lt_of_le (Fin.isLt _) (two_le_bound _)))
  have h₁: ∀ {x: Fin 2} {H: List Unit} {y: BitTree H}, x.val * y.toNat % bound H = x.val * y.toNat
    | 0, _, _ => Nat.mod_eq_of_lt (lt_of_eq_of_lt (zero_mul _) (bound_pos _))
    | 1, _, _ => Nat.mod_eq_of_lt (lt_of_eq_of_lt (one_mul _) (toNat_lt _))
  simpa only [karatsubaHelper₃,
    add_toNat, mulBit_ofNat, mulBit'_ofNat,
    bound_cons, ← mul_assoc, mul_zero,
    mul_right_comm _ _ (bound H),
    mul_right_comm _ (toNat _) (Fin.val _),
    mul_comm (toNat _) (bound H),
    Nat.add_right_comm _ (_ * toNat y) (_ * toNat x),
    Nat.add_right_comm _ (toNat _ * toNat _),
    left_distrib, right_distrib,
    toNat_ofNat, toNat_node, h, toNat_zero,
    add_zero, zero_add, Nat.mod_add_mod, ← Nat.add_assoc,
    h₀, h₁] using Nat.mod_eq_of_lt (lt_of_eq_of_lt
    (Nat.add_assoc _ _ _)
    (add_lt_mul_bound
      (add_le_mul_bound
        (le_trans
          (mul_le_of_le_one_right' (Nat.le_of_lt_succ (Fin.isLt _)))
          (mul_le_of_le_one_right' (Nat.le_of_lt_succ (Fin.isLt _))))
        (Nat.mul_le_mul
          (mul_le_of_le_one_right' (Nat.le_of_lt_succ (Fin.isLt _)))
          (le_of_lt (toNat_lt _))))
      (add_lt_mul_bound
        (Nat.mul_le_mul (mul_le_of_le_one_right' (Nat.le_of_lt_succ (Fin.isLt _))) (le_of_lt (toNat_lt _)))
        (Nat.mul_lt_mul_for_real (toNat_lt _) (toNat_lt _)))))

-- theorem karatsubaHelper₃_toNat_ofNat

def karatsubaHelper₁ (z₀ z₂: BitTree H) (z₃: BitTree (()::H)): BitTree (()::H) := z₃ - (node 0 z₂) - (node 0 z₀)

theorem karatsubaHelper₁_toNat
    (xhi xlo yhi ylo: BitTree H)
    (z₀ z₂: BitTree (()::H)) (z₃: BitTree (()::()::H)):
    z₀.toNat = xlo.toNat * ylo.toNat →
    z₂.toNat = xhi.toNat * yhi.toNat →
    z₃.toNat = (xhi.toNat + xlo.toNat) * (yhi.toNat + ylo.toNat) →
    (karatsubaHelper₁ z₀ z₂ z₃).toNat = xhi.toNat * ylo.toNat + xlo.toNat * yhi.toNat := by
  intro h₀ h₂ h₃
  have h: ∀ {H: List Unit} {a b c d e f: BitTree H},
      (a.toNat * b.toNat + c.toNat * d.toNat + e.toNat * f.toNat) % (bound H * bound H * bound H *bound H) =
      a.toNat * b.toNat + c.toNat * d.toNat + e.toNat * f.toNat :=
    Nat.mod_eq_of_lt (add_lt_mul_bound
      (add_le_mul_bound
        (Nat.mul_le_mul
          (le_of_lt (toNat_lt _))
          (le_of_lt (toNat_lt _)))
        (Nat.mul_le_mul
          (le_of_lt (toNat_lt _))
          (le_of_lt (toNat_lt _))))
       (add_lt_mul_bound
        (Nat.mul_le_mul
          (le_of_lt (toNat_lt _))
          (le_of_lt (toNat_lt _)))
        (Nat.mul_lt_mul_for_real
          (bound_pos _)
          (bound_pos _))))
  have h': ∀ {H: List Unit} {a b c d: BitTree H},
      (a.toNat * b.toNat + c.toNat * d.toNat) % (bound H * bound H * bound H * bound H) =
      a.toNat * b.toNat + c.toNat * d.toNat :=
    (congrArg₂ _ (congrArg _ (congrArg₂ _
      toNat_zero.symm toNat_zero.symm)) rfl).trans
    (h.trans (congrArg _ (congrArg₂ _
      toNat_zero toNat_zero)))
  have hs: ∀ {a b c: ℕ}, a + b + c - b = a + c :=
    (congrArg₂ _ (Nat.add_right_comm _ _ _) rfl).trans (Nat.add_sub_cancel _ _)
  simpa only [karatsubaHelper₁,
    sub_toNat, h₃, left_distrib, right_distrib, add_comm (xhi.toNat * yhi.toNat), ←
    add_assoc, add_right_comm _ (xhi.toNat * yhi.toNat), bound_cons, ← mul_assoc, toNat_node,
    toNat_zero, mul_zero, h₂, zero_add, add_tsub_cancel_right, toNat_ofNat, Nat.add_mod_right, h,
    h₀, hs, h'] using Nat.add_comm _ _


def karatsuba: {H: List Unit} → (x y: BitTree H) → BitTree (()::H)
| _, bit x, bit y => mulBit _ x y
| _, node xhi xlo, node yhi ylo =>
  have z₂ := karatsuba xhi yhi
  have z₀ := karatsuba xlo ylo
  have zx := addWithCarry xhi xlo 0
  have zy := addWithCarry yhi ylo 0
  have z₃ := karatsubaHelper₃ (karatsuba zx.snd zy.snd) zx zy
  have z₁ := karatsubaHelper₁ z₀ z₂ z₃
  (node z₂ 0) + lshift2 z₁  + (node 0 z₀)

theorem karatsuba_eq_mul: {H: List Unit} → (x y: BitTree H) → karatsuba x y = ofNat _ (toNat x * toNat y)
| _, bit _, bit _ => mulBit_ofNat _ _ _
| _::H, node xhi xlo, node yhi ylo => by
  have h: ∀ {H: List Unit} {x y: BitTree H}, x.toNat * y.toNat % (bound H * bound H) = x.toNat * y.toNat :=
    Nat.mod_eq_of_lt (Nat.mul_lt_mul_for_real (toNat_lt _) (toNat_lt _))
  apply toNat_inj
  simp [karatsuba,
    @karatsuba_eq_mul H, toNat_node,
    toNat_ofNat, add_toNat, ← add_assoc,
    bound_cons, ← mul_assoc, left_distrib, right_distrib, mul_right_comm _ _ (bound H), mul_comm (toNat _) (bound H),
    toNat_zero, addWithCarry_eq_ofNat_add, h]
  rw [lshift2_toNat, karatsubaHelper₁_toNat xhi xlo yhi ylo]
  apply congrArg₂ _ _ rfl
  apply congrArg₂
  apply Eq.trans _ (Nat.add_assoc _ _ _).symm
  apply congrArg
  apply Eq.trans
  apply Nat.mod_eq_of_lt
  simp only [bound_cons, ← Nat.mul_assoc]
  apply Nat.mul_lt_mul _ (le_refl _) (bound_pos _)
  apply add_lt_mul_bound
  apply Nat.le_of_lt
  apply Nat.mul_lt_mul_for_real (toNat_lt _) (toNat_lt _)
  apply Nat.mul_lt_mul_for_real (toNat_lt _) (toNat_lt _)
  ring
  rfl
  simp [toNat_ofNat, bound_cons, h]
  simp [toNat_ofNat, bound_cons, h]
  rw [karatsubaHelper₃_toNat]
  simp [toNat_ofNat, Nat.div_add_mod]
  simp [toNat_ofNat, bound_cons]
  apply Nat.mod_eq_of_lt
  apply Nat.mul_lt_mul_for_real
  apply Nat.mod_lt _ (bound_pos _)
  apply Nat.mod_lt _ (bound_pos _)

end BitTree


def Nat.karatsuba (n m: ℕ): ℕ :=
  have H := Unary.max (BitTree.getHeight n) (BitTree.getHeight m)
  BitTree.toNat (BitTree.karatsuba (BitTree.ofNat H n) (BitTree.ofNat H m))

theorem Nat.karatsuba_eq_mul (n m: ℕ): karatsuba n m = n * m :=
  have hn : n < BitTree.bound (Unary.max (BitTree.getHeight n) (BitTree.getHeight m)) :=
    lt_of_lt_of_le BitTree.lt_bound_getHeight (BitTree.bound_le_bound (le_of_le_of_eq (le_max_left _ _) (Unary.length_max _ _).symm))
  have hm : m < BitTree.bound (Unary.max (BitTree.getHeight n) (BitTree.getHeight m)) :=
    lt_of_lt_of_le BitTree.lt_bound_getHeight (BitTree.bound_le_bound (le_of_le_of_eq (le_max_right _ _) (Unary.length_max _ _).symm))
  (congrArg BitTree.toNat (BitTree.karatsuba_eq_mul _ _)).trans
    ((congrArg _ (congrArg _ (congrArg₂ _
      ((BitTree.toNat_ofNat _ _).trans
        (Nat.mod_eq_of_lt hn))
      ((BitTree.toNat_ofNat _ _).trans
        (Nat.mod_eq_of_lt hm))))).trans
      ((BitTree.toNat_ofNat _ _).trans
      (Nat.mod_eq_of_lt (lt_of_lt_of_eq
        (Nat.mul_lt_mul_for_real hn hm)
        (BitTree.bound_cons _).symm))))
