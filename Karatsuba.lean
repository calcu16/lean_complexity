import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
import Lib

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

def Unary.div_mod2: List Unit → (List Unit × Bool)
| [] => ([], false)
| _::[] => ([], true)
| _::_::us => (()::(div_mod2 us).fst, (div_mod2 us).snd)

def Unary.append_pow₂: List Unit → List Unit → List Unit
| [] => List.cons ()
| _::H => append_pow₂ H ∘ append_pow₂ H

theorem Unary.append_pow₂_length: (H acc: List Unit) → (append_pow₂ H acc).length = acc.length + 2 ^ H.length
| [], _ => rfl
| _::H, _ =>
  (Unary.append_pow₂_length H _).trans
  ((congrArg₂ _ (Unary.append_pow₂_length H _) rfl).trans
  ((Nat.add_assoc _ _ _).trans
  (congrArg _ ((Nat.pow_succ _ _).trans (Nat.mul_two _)).symm)))

def Unary.max: List Unit → List Unit → List Unit
| [], ys => ys
| _::xs, [] => ()::xs
| _::xs, _::ys => ()::(max xs ys)

theorem Unary.length_max: (xs ys: List Unit) → (Unary.max xs ys).length = Nat.max xs.length ys.length
| [], _ => Eq.symm (Nat.zero_max _)
| _::_, [] => Eq.symm (Nat.max_zero _)
| _::_, _::_ => (congrArg Nat.succ (Unary.length_max _ _)).trans (Nat.succ_max_succ _ _).symm

def Unary.div_pow₂: ℕ → List Unit → ℕ
| n, [] => n
| n, _::H => div_pow₂ (n / 2) H

@[simp] theorem Unary.div_pow₂_eq (n: ℕ): (H: List Unit) → div_pow₂ n H = n / 2 ^ H.length
| [] => (Nat.div_one _).symm
| _::H =>
    (div_pow₂_eq _ H).trans
    ((Nat.div_div_eq_div_mul _ _ _).trans
    (congrArg _ Nat.pow_succ'.symm))

def Unary.mod_pow₂: ℕ → List Unit → ℕ
| _, [] => 0
| n, _::H => 2 * (mod_pow₂ (n / 2) H) + (n % 2)

@[simp] theorem Unary.mod_pow₂_eq (n: ℕ): (H: List Unit) → mod_pow₂ n H = n % 2 ^ H.length
| [] => (Nat.mod_one _).symm
| _::_ =>
  (congrArg₂ Nat.add (congrArg (Nat.mul _) (Unary.mod_pow₂_eq _ _)) rfl).trans
  (Nat.mod_mul.symm.trans (congrArg _ Nat.pow_succ'.symm))

def Unary.mul_pow₂: ℕ → List Unit → ℕ
| n, [] => n
| n, _::H => 2 * (mul_pow₂ n H)

@[simp] theorem Unary.mul_pow₂_eq (n: ℕ): (H: List Unit) → mul_pow₂ n H = n * 2 ^ H.length
| [] => (Nat.mul_one _).symm
| _::_ =>
  (congrArg (Nat.mul _) (mul_pow₂_eq _ _)).trans
  ((mul_left_comm _ _ _).trans
  (congrArg _ Nat.pow_succ'.symm))

inductive BitTree: Type _ where
| bit (val: Fin 2)
| node (left right: BitTree)


namespace BitTree


class inductive Perfect: List Unit → BitTree → Prop
| bit (val: Fin 2): Perfect [] (.bit val)
| node {H: List Unit} {l r: BitTree} (lhs: Perfect H l) (rhs: Perfect H r):
  Perfect (()::H) (.node l r)

instance: Perfect [] (.bit b) := .bit b
instance [hx: Perfect H x] [hy: Perfect H y]: Perfect (()::H) (.node x y) := .node hx hy

def getHeight (n: ℕ): List Unit := List.replicate n.size.size ()

def getBit: BitTree → Fin 2
| .bit v => v
| .node _ _ => 0 -- garbage

def hi: BitTree → BitTree
| .bit _ => .bit 0 -- garbage
| .node hi _ => hi

instance [h: Perfect (()::H) t]: Perfect H (hi t) :=
  match h with | .node lhs _ => lhs

def lo: BitTree → BitTree
| .bit v => .bit v -- garbage
| .node _ lo => lo

instance [h: Perfect (()::H) t]: Perfect H (lo t) :=
  match h with | .node _ rhs => rhs

def heightOf: List Unit → ℕ := List.length
def width: List Unit → ℕ := Nat.pow 2 ∘ heightOf
def bound: List Unit → ℕ := Nat.pow 2 ∘ width


theorem bound_pos (H: List Unit): 0 < bound H := Nat.pow_two_pos _
theorem two_le_bound (H: List Unit): 2 ≤ bound H :=
  (Nat.pow_le_pow_right zero_lt_two (Nat.pow_le_pow_right zero_lt_two (Nat.zero_le _)))

theorem bound_le_bound {H G: List Unit} (h: H.length ≤ G.length): bound H ≤ bound G :=
  Nat.pow_le_pow_right zero_lt_two (Nat.pow_le_pow_right zero_lt_two h)
theorem bound_le_cons (H: List Unit): bound H ≤ bound (()::H) :=
  bound_le_bound (Nat.le_succ _)

theorem bound_zero: bound [] = 2 := rfl
theorem bound_one: bound (()::[]) = 4 := rfl

theorem bound_cons (H: List Unit): bound (()::H) = bound H * bound H :=
  (((congrArg _ (Nat.pow_succ _ _)).trans (Nat.pow_mul _ _ _)).trans (Nat.pow_two _))


theorem lt_bound_getHeight: n < bound (getHeight n) :=
  lt_of_lt_of_eq (lt_of_lt_of_le
    (Nat.lt_size_self _)
    (Nat.pow_le_pow_right (zero_lt_two) (le_of_lt (Nat.lt_size_self _))))
    (congrArg (λ n ↦ 2 ^ 2 ^ n) (List.length_replicate _ _).symm)

theorem mul_lt_bound_cons (ha: a < bound H) (hb: b < bound H): a * b < bound (()::H) :=
  lt_of_lt_of_eq (Nat.mul_lt_mul_for_real ha hb) (bound_cons _).symm

theorem add_lt_mul_bound (ha: a ≤ x) (hb: b < x): a + b < x * bound H :=
  lt_of_lt_of_le (add_lt_add_of_le_of_lt ha hb) (le_of_eq_of_le
    (mul_two _).symm
    (Nat.mul_le_mul (le_refl _) (two_le_bound _)))

theorem add_lt_bound_cons (ha: a < bound H) (hb: b < bound H): a + b < bound (()::H) :=
  lt_of_lt_of_eq (add_lt_mul_bound (le_of_lt ha) hb) (bound_cons _).symm

theorem add_le_mul_bound (ha: a ≤ x) (hb: b ≤ x): a + b ≤ x * bound H :=
  le_trans (add_le_add ha hb) (le_of_eq_of_le
    (mul_two _).symm
    (Nat.mul_le_mul (le_refl _) (two_le_bound _)))

def zero: (H: List Unit) → BitTree
| [] => bit 0
| _::H => node (zero H) (zero H)

instance: Perfect H (zero H) := H.recOn (.bit 0) (λ _ _ ih ↦ .node ih ih)

def size: BitTree → ℕ
| .bit _ => 0
| .node lhs rhs => size lhs + size rhs + 1

@[simp] theorem BitTree.lt_size_lo: size xlo < size (node xhi xlo) :=
  Nat.lt_succ_of_le (Nat.le_add_left _ _)

@[simp] theorem BitTree.lt_size_hi: size xhi < size (node xhi xlo) :=
  Nat.lt_succ_of_le (Nat.le_add_right _ _)

def height: BitTree → ℕ
| .bit _ => 0
| .node lhs rhs => max (height lhs) (height rhs) + 1

@[simp] theorem perfect_height: (H: outParam (List Unit)) → (x: BitTree) → [Perfect H x] → x.height = H.length
| _, _, .bit _ => rfl
| _::_, _, .node _ _ =>
  congrArg Nat.succ ((congrArg₂ _ (perfect_height _ _) (perfect_height _ _)).trans (Nat.max_self _))

@[simp] theorem BitTree.lt_height: (x < height (node xhi xlo)) = (x ≤ height xhi ∨ x ≤ height xlo) :=
  iff_iff_eq.mp ⟨ le_max_iff.mp ∘ Nat.le_of_lt_succ, Nat.lt_succ_of_le ∘ le_max_iff.mpr ⟩

def rightHeight: BitTree → ℕ
| .bit _ => 0
| .node _ rhs => rightHeight rhs + 1

theorem rightHeight_zero: {H: List Unit} → rightHeight (zero H) = List.length H
| [] => rfl
| _::_ => congrArg Nat.succ rightHeight_zero

def setLowestBit: BitTree → BitTree
| .bit _ => bit 1
| .node lhs rhs => .node lhs (setLowestBit rhs)

instance [h: Perfect H x]: Perfect H (setLowestBit x) :=
  h.recOn (λ _ ↦ .bit 1) λ lhs _ _ rhs ↦ .node lhs rhs

def one: (H: List Unit) → BitTree := setLowestBit ∘ zero

instance: Perfect H (one H) := H.recOn (.bit 1) (λ _ _ ih ↦ .node inferInstance ih)

def divBound (n: ℕ) (H: List Unit): ℕ := n / bound H
def modBound (n: ℕ) (H: List Unit): ℕ := n % bound H
def mulBound (n: ℕ) (H: List Unit): ℕ := bound H * n
@[simp] theorem divBound_zero: divBound 0 H = 0 := Nat.zero_div _


def ofNatHelper: List Unit → ℕ → (ℕ × BitTree)
| [], n => ( n / 2, .bit ⟨ n % 2, Nat.mod_lt _ zero_lt_two ⟩ )
| _::H, n =>
  have lo := ofNatHelper H n
  have hi := ofNatHelper H lo.fst
  (hi.fst, node hi.snd lo.snd)

theorem ofNatHelper_fst: (H: List Unit) → (n: ℕ) →
    (ofNatHelper H n).fst = divBound n H
| [], _ => rfl
| _::_, _ =>
  (congrArg (Prod.fst ∘ ofNatHelper _) (ofNatHelper_fst _ _)).trans
  ((ofNatHelper_fst _ _).trans
  ((Nat.div_div_eq_div_mul _ _ _).trans
  ((congrArg (Nat.div _) (bound_cons _)).symm)))

def ofNat (H: List Unit) (n: ℕ): BitTree := (ofNatHelper H n).snd


@[simp] theorem ofNat_nil (n: ℕ): ofNat [] n = .bit ⟨ n % 2, Nat.mod_lt _ zero_lt_two ⟩ := rfl
@[simp] theorem ofNat_cons: (H: List Unit) → (n: ℕ) →
    ofNat (()::H) n = node (ofNat H (divBound n H)) (ofNat H n)
| [], _ => rfl
| _::_, _ => congrArg₂ node (congrArg (ofNat _) (ofNatHelper_fst _ _)) rfl

theorem ofNat_mod: (H: List Unit) → (n: ℕ) → ofNat H (modBound n H) = ofNat H n
| [], _ => congrArg bit (Fin.eq_of_val_eq (Nat.mod_eq_of_lt (Nat.mod_lt _ zero_lt_two)))
| _::_, x => ofNat_cons _ (modBound _ _) ▸ ofNat_cons _ x ▸ congrArg₂ _
    ((congrArg _ ((congrArg₂ Nat.div (congrArg (Nat.mod _) (bound_cons _)) rfl).trans (Nat.mod_mul_right_div_self _ _ _))).trans (ofNat_mod _ _))
    (((ofNat_mod _ _).symm.trans (congrArg _ ((congrArg₂ _ (congrArg (Nat.mod _) (bound_cons _)) rfl).trans (Nat.mod_mul_left_mod _ _ _)))).trans (ofNat_mod _ _))

theorem ofNat_cons' (H: List Unit) (n: ℕ):
    ofNat (()::H) n = node (ofNat H (divBound n H)) (ofNat H (modBound n H)) :=
  ofNat_mod H n ▸ ofNat_cons H n

instance: Perfect H (ofNat H n) := by
  induction H generalizing n with
  | nil => exact .bit _
  | cons _ _ ih => exact .node ih ih

def toNatHelper: List Unit → BitTree → ℕ → ℕ
| _, bit b, n => b.val + 2 * n
| [], node _ _, _ => 0
| _::H, node hi lo, n => toNatHelper H lo (toNatHelper H hi n)

theorem toNatHelper_acc: (H: List Unit) → (x: BitTree) → [Perfect H x] → (n: ℕ) → toNatHelper H x n = bound H * n + (toNatHelper H x 0)
| _, _, .bit _, _ => by simpa [toNatHelper, bound_zero] using Nat.add_comm _ _
| _::H, .node _ _, .node _ _, x => by
  simp [bound_cons, toNatHelper, toNatHelper_acc H _ x, toNatHelper_acc H _ (_ + _),
    toNatHelper_acc H _ (toNatHelper _ _ _),
    left_distrib, right_distrib, ← mul_assoc, ← add_assoc]

def toNat (H: List Unit) (x: BitTree): ℕ := toNatHelper H x 0

theorem toNat_node (H: List Unit) (x y: BitTree) [Perfect H x] [Perfect H y]: toNat (()::H) (node x y) = bound H * (toNat H x)  + toNat H y :=
  toNatHelper_acc H _ _

theorem toNat_zero: {H: List Unit} → toNat H (zero H) = 0
| [] => rfl
| _::_ => (toNat_node _ _ _).trans (congrArg₂ _ (congrArg _ toNat_zero) toNat_zero)

theorem toNat_one: (H: List Unit) → toNat H (one H) = 1
| [] => rfl
| _::_ => (toNat_node _ _ _).trans (congrArg₂ _ (congrArg _ toNat_zero) (toNat_one _))

theorem ofNat_zero: {H: List Unit} → ofNat H 0 = (zero H)
| [] => rfl
| _::_ => (ofNat_cons _ _).trans
  (congrArg₂ _
    ((congrArg _ (Nat.zero_div _)).trans ofNat_zero)
    ofNat_zero)

theorem ofNat_one: {H: List Unit} → @ofNat H 1 = (one H)
| [] => rfl
| _::_ => (ofNat_cons _ _).trans (congrArg₂ node
    ((congrArg _ ((Nat.div_eq_zero_iff (bound_pos _)).mpr (Nat.lt_of_succ_le (two_le_bound _)))).trans ofNat_zero)
    ofNat_one)

theorem toNat_lt: {H: List Unit} → (x: BitTree) → [Perfect H x] → x.toNat H < bound H
| _, _, .bit b => b.isLt
| _, _, .node _ _ => lt_of_eq_of_lt (toNat_node _ _ _) (
  Nat.lt_of_succ_le (le_of_le_of_eq (add_le_add (add_le_add
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
        (bound_cons _).symm)))))

theorem toNat_le_pred (x: BitTree) [Perfect H x]: x.toNat H ≤ bound H - 1 := Nat.le_sub_of_add_le (Nat.succ_le_of_lt (toNat_lt _))

theorem toNat_hi (hi lo: BitTree) [Perfect H hi] [Perfect H lo]: toNat (()::H) (node hi lo) / bound H = toNat H hi :=
  (congrArg₂ _ (toNat_node _ _ _) rfl).trans
  ((Nat.mul_add_div (bound_pos _) _ _).trans
  (congrArg₂ _ rfl (Nat.div_eq_of_lt (toNat_lt _))))

theorem toNat_hi': (x: BitTree) → [Perfect (()::H) x] → toNat H (hi x) = toNat (()::H) x / bound H
| _, .node _ _ => (toNat_hi _ _).symm

theorem toNat_lo (hi lo: BitTree) [Perfect H hi] [Perfect H lo]: toNat (()::H) (node hi lo) % bound H = toNat H lo :=
  (congrArg₂ _ (toNat_node _ _ _) rfl).trans
  ((Nat.mul_add_mod _ _ _).trans
  (Nat.mod_eq_of_lt (toNat_lt _)))

theorem toNat_lo': (x: BitTree) → [Perfect (()::H) x] → toNat H (lo x) = toNat (()::H) x % bound H
| _, .node _ _ => (toNat_lo _ _).symm

theorem ofNat_toNat: (H: List Unit) → (x: BitTree) → [Perfect H x] → ofNat H (toNat H x) = x
| _, _, .bit 0 => rfl
| _, _, .bit 1 => rfl
| _, _, .node _ _ => (ofNat_cons' _ _).trans (congrArg₂ _
  ((congrArg _ (toNat_hi _ _)).trans (ofNat_toNat _ _))
  ((congrArg _ (toNat_lo _ _)).trans (ofNat_toNat _ _)))

theorem toNat_inj {x y: BitTree} [Perfect H x] [Perfect H y] (h: toNat H x = toNat H y): x = y :=
  ofNat_toNat H x ▸ h ▸ ofNat_toNat H y

theorem ofNat_mul_add {H: List Unit} (n: ℕ) {m: ℕ} (hm: m < bound H): ofNat (()::H) (bound H * n + m) = node (ofNat H n) (ofNat H m) :=
  (ofNat_cons' _ _).trans
  (congrArg₂ _
    (congrArg _ (
      (Nat.mul_add_div (bound_pos _) _ _).trans
      (congrArg _ (Nat.div_eq_of_lt hm))))
    (congrArg _ (
      (Nat.mul_add_mod _ _ _).trans
      (Nat.mod_eq_of_lt hm))))

@[simp] theorem ofNat_mul_add_mod (H: List Unit) (n m: ℕ): ofNat H (bound H * n + m) = ofNat H m :=
  (ofNat_mod _ _).symm.trans ((congrArg _ (Nat.mul_add_mod _ _ _)).trans (ofNat_mod _ _))

theorem ofNat_mul_add_mod' (H: List Unit) (n m: ℕ): ofNat (()::H) (bound H * n + m % bound H) = node (ofNat H n) (ofNat H m) :=
  (ofNat_mul_add _ (Nat.mod_lt _ (bound_pos _))).trans (congrArg _ (ofNat_mod _ _))

theorem ofNat_modInj (h: n % bound H = m % bound H): ofNat H n = ofNat H m :=
  ((ofNat_mod _ _).symm.trans (congrArg _ h)).trans (ofNat_mod _ _)

theorem toNat_ofNat_lt: {H: List Unit} → {n: ℕ} → n < bound H → toNat H (ofNat H n) = n
| [], _, h => Nat.mod_eq_of_lt h
| _::_, _, h =>
  (congrArg _ (ofNat_cons' _ _)).trans
  ((toNat_node _ _ _).trans
  ((congrArg₂ _
    (congrArg _ (toNat_ofNat_lt (Nat.div_lt_of_lt_mul (lt_of_lt_of_eq h (bound_cons _)))))
    (toNat_ofNat_lt (Nat.mod_lt _ (bound_pos _)))).trans
  (Nat.div_add_mod _ _)))


theorem toNat_ofNat (H: List Unit) (n: ℕ): toNat H (ofNat H n) = n % bound H :=
  (congrArg _ (ofNat_mod _ _).symm).trans
  (toNat_ofNat_lt (Nat.mod_lt _ (bound_pos _)))

theorem ofNat_modCongr (h: ofNat H n = ofNat H m): n % bound H = m % bound H :=
  ((toNat_ofNat _ _).symm.trans (congrArg (toNat _) h)).trans (toNat_ofNat _ _)

theorem ofNat_congr (h: ofNat H n = ofNat H m) (hn: n < bound H) (hm: m < bound H): n = m :=
  (Nat.mod_eq_of_lt hn).symm.trans ((ofNat_modCongr h).trans (Nat.mod_eq_of_lt hm))

def addWithCarry: BitTree → BitTree → Fin 2 → Fin 2 × BitTree
| .bit x, .bit y, c => (⟨
    (x.val + y.val + c.val) / 2,
      Nat.div_lt_of_lt_mul (Nat.lt_succ_of_le (Nat.add_le_add (d := 1) (Nat.add_le_add (b := 1) (d := 1)
        (Nat.le_of_lt_succ x.isLt)
        (Nat.le_of_lt_succ y.isLt))
        (Nat.le_of_lt_succ c.isLt)))⟩,
    .bit ⟨(x.val + y.val + c.val) % 2,
      Nat.mod_lt _ zero_lt_two⟩)
| .node xhi xlo, .node yhi ylo, c =>
  have rlo := addWithCarry xlo ylo c
  have rhi := addWithCarry xhi yhi rlo.fst
  (rhi.fst, .node rhi.snd rlo.snd)
| x, _, c => (c, x) -- garbage

instance instPerfectAddWithCarry [hx: Perfect H x] [hy: Perfect H y]: Perfect H (addWithCarry x y c).snd :=
  match hx, hy with
  | .bit x, .bit y => .bit ⟨(x.val + y.val + _) % _, _⟩
  | .node _ _, .node _ _ =>
    Perfect.node instPerfectAddWithCarry instPerfectAddWithCarry

theorem addWithCarry_eq_ofNat_add: {H: List Unit} → (x y: BitTree) → [Perfect H x] → [Perfect H y] → (c: Fin 2) →
  addWithCarry x y c = (
    ⟨(x.toNat H + y.toNat H + c.val) / bound H,
      Nat.div_lt_of_lt_mul (lt_of_le_of_lt (le_of_le_of_eq
        (add_le_add (add_le_add (toNat_le_pred _) (toNat_le_pred _)) (Nat.le_of_lt_succ c.isLt))
        ((add_assoc _ _ _).trans
          ((congrArg _ (Nat.sub_add_cancel (bound_pos _))).trans
          ((congrArg₂ _ (mul_two _) rfl).trans (Nat.sub_add_comm (bound_pos _))).symm)))
        (Nat.sub_lt (Nat.mul_pos (bound_pos _) zero_lt_two) zero_lt_one))⟩,
    ofNat H (x.toNat H + y.toNat H + c.val)
  )
| _, _, _, .bit _, .bit _, _ => by simp [addWithCarry, toNat, toNatHelper, bound_zero]
| _::H, _, _, .node _ _, .node _ _, _ =>
  have rearrange: ∀ {m xh xl yh yl c: ℕ},
    m * xh + xl + (m * yh + yl) + c =
    m * (xh + yh) + (xl + yl + c) := by intro _ _ _ _ _ _; ring
  by
  simp [addWithCarry, @addWithCarry_eq_ofNat_add H, rearrange, toNat_node, bound_cons,
    ← Nat.div_div_eq_div_mul, Nat.mul_add_div (bound_pos _),  divBound]

theorem addWithCarry_eq_add {H: List Unit} (x y: BitTree) [Perfect H x] [Perfect H y] (c: Fin 2):
    bound H * (addWithCarry x y c).fst.val + (addWithCarry x y c).snd.toNat H = x.toNat H + y.toNat H + c.val :=
    (congrArg₂ _
      (congrArg _ (Fin.val_eq_of_eq
        (Prod.mk.inj (addWithCarry_eq_ofNat_add x y c)).left))
      ((congrArg _ (Prod.mk.inj
        (addWithCarry_eq_ofNat_add x y c)).right).trans
        (toNat_ofNat _ _))).trans
    (Nat.div_add_mod _ (bound H))


theorem addWithCarry_eq_add₀ {H: List Unit} (x y: BitTree) [Perfect H x] [Perfect H y]:
    bound H * (addWithCarry x y 0).fst.val + (addWithCarry x y 0).snd.toNat H = x.toNat H + y.toNat H :=
  addWithCarry_eq_add _ _ _

def negate: BitTree → BitTree
| bit b => bit ⟨ 1 - b.val, Nat.sub_lt_left_of_lt_add (Nat.le_of_lt_succ (Fin.isLt _)) (Nat.lt_add_left _ (Nat.succ_lt_succ zero_lt_one)) ⟩
| node hi lo => node (negate hi) (negate lo)

instance [h: Perfect H x]: Perfect H (negate x) :=
  h.recOn (λ _ ↦ .bit _) λ _ _ lhs rhs ↦ .node lhs rhs

theorem addWithCarry_negate: {H: List Unit} → (x: BitTree) → [Perfect H x] → addWithCarry x (negate x) 1 = (1, ofNat H 0)
| _, _, .bit 0 => rfl
| _, _, .bit 1 => rfl
| ()::H, _, .node _ _ => by simp [addWithCarry, addWithCarry_negate (H := H)]

theorem add_toNat_negate: {H: List Unit} → (x: BitTree) → [Perfect H x] → x.toNat H + (negate x).toNat H + 1 = bound H
| _, _, .bit 0 => rfl
| _, _, .bit 1 => rfl
| _, _, .node _ _ =>
  have rearrange : ∀ {m a b c d e: ℕ},
    m * a + b + (m * c + d) + e = m * (a + c) + (b + d + e) := by
    intro _ _ _ _ _ _; ring
  by simp [toNat_node, rearrange, negate, add_toNat_negate _, ← Nat.mul_succ, Nat.succ_eq_add_one, bound_cons]

def mulBit (H: List Unit): Fin 2 → Fin 2 → BitTree
| 0, _ => zero H
| 1, 0 => zero H
| 1, 1 => one H

instance: Perfect H (mulBit H x y) :=
  match x, y with
  | 0, _ => instPerfectZero
  | 1, 0 => instPerfectZero
  | 1, 1 => instPerfectOne

theorem mulBit_ofNat: (H: List Unit) → (x y: Fin 2) → mulBit H x y = ofNat H (x.val * y.val)
| _, 0, 0 => ofNat_zero.symm
| _, 0, 1 => ofNat_zero.symm
| _, 1, 0 => ofNat_zero.symm
| _, 1, 1 => ofNat_one.symm

def mulBit': List Unit → Fin 2 → BitTree → BitTree
| H, 0, _ => zero H
| _, 1, x => x

instance [h: Perfect H x]: Perfect H (mulBit' H b x) :=
  match b with
  | 0 => instPerfectZero
  | 1 => h

theorem mulBit'_ofNat {H: List Unit}: {x: Fin 2} → (y: BitTree) → [Perfect H y] → mulBit' H x y = ofNat H (x.val * toNat H y)
| 0, _, _ => ((congrArg _ (zero_mul _)).trans ofNat_zero).symm
| 1, _, _ => ((congrArg _ (one_mul _)).trans (ofNat_toNat _ _)).symm

instance: Add (BitTree) := ⟨ λ x y ↦ (addWithCarry x y 0).snd ⟩
instance: Sub (BitTree) := ⟨ λ x y ↦ (addWithCarry x (negate y) 1).snd ⟩

instance instPerfectAdd [Perfect H x] [Perfect H y]: Perfect H (x + y) := instPerfectAddWithCarry
instance instPerfectSub [Perfect H x] [Perfect H y]: Perfect H (x - y) := instPerfectAddWithCarry

theorem add_toNat (H: List Unit) (x y: BitTree) [Perfect H x] [Perfect H y]: x + y = ofNat H (x.toNat H + y.toNat H) :=
  congrArg Prod.snd (addWithCarry_eq_ofNat_add _ _ _)

theorem add_toNat_mod (H: List Unit) (x y: BitTree) [Perfect H x] [Perfect H y]: toNat H (x + y) = (x.toNat H + y.toNat H) % bound H :=
  (Nat.mod_eq_of_lt (toNat_lt _)).symm.trans (ofNat_modCongr ((ofNat_toNat _ _).trans (add_toNat _ _ _)))

theorem sub_toNat (H: List Unit) (x y: BitTree) [Perfect H x] [Perfect H y]: x - y = ofNat H (x.toNat H + bound H - y.toNat H) :=
  have rearrange: ∀ {a b c d: ℕ}, a + b + c + d = a + (d + b + c) := by intro _ _ _ _; ring
  (congrArg Prod.snd (addWithCarry_eq_ofNat_add _ _ _)).trans
  (congrArg (ofNat H) (Nat.sub_eq_of_eq_add
    (rearrange.trans (congrArg _ (add_toNat_negate _))).symm).symm)

def lshift2 (H: List Unit) (x: BitTree): BitTree :=
  node
    (node (lo (hi x)) (hi (lo x)))
    (node (lo (lo x)) (zero H))

instance [Perfect (()::()::H) x]: Perfect (()::()::H) (lshift2 H x) :=
  Perfect.node inferInstance inferInstance

theorem lshift2_toNat: (H: List Unit) → (x: BitTree) → [Perfect (()::()::H) x] → (x.lshift2 H).toNat (()::()::H) = (x.toNat (()::()::H) * bound H) % (bound (()::()::H))
| H, _, .node (.node _ _) (.node _ _) => (Nat.mod_eq_of_lt (toNat_lt _)).symm.trans
  (by simp only [
    toNat_node, lo, hi, lshift2, bound_cons,
    left_distrib, right_distrib, ← mul_assoc,
    mul_right_comm _ _ (bound H), mul_comm (toNat _ _) (bound H),
    Nat.add_assoc, Nat.mul_add_mod,
    toNat_zero, add_zero])

def karatsubaHelper₃ (H: List Unit) (xy: BitTree):
  (Fin 2 × BitTree) →  (Fin 2 × BitTree) → BitTree
| (xc, x), (yc, y) =>
  node (mulBit (()::H) xc yc) xy +
  node (zero (()::H)) (node (mulBit' H xc y) (zero H)) +
  node (zero (()::H)) (node (mulBit' H yc x) (zero H))

instance [Perfect (()::H) xy] [Perfect H (Prod.snd x)] [Perfect H (Prod.snd y)]: Perfect (()::()::H) (karatsubaHelper₃ H xy x y) := instPerfectAdd

theorem karatsubaHelper₃_toNat: (xy: BitTree) → (x: Fin 2 × BitTree) →  (y: Fin 2 × BitTree) → [Perfect (()::H) xy] → [Perfect H x.snd] → [Perfect H y.snd] →
  xy.toNat (()::H) = x.snd.toNat H * y.snd.toNat H → (karatsubaHelper₃ H xy x y).toNat (()::()::H) = (bound H * x.fst.val + x.snd.toNat H) * (bound H * y.fst.val + y.snd.toNat H)
| xy, (xc, x), (yc, y), _, _, _, h => by
  have h₀: ∀ {x y: Fin 2} {H: List Unit}, x.val * y.val % (bound H * bound H) = x.val * y.val :=
    Nat.mod_eq_of_lt (Nat.mul_lt_mul_for_real
      (lt_of_lt_of_le (Fin.isLt _) (two_le_bound _))
      (lt_of_lt_of_le (Fin.isLt _) (two_le_bound _)))
  have h₁: ∀ {x: Fin 2} {H: List Unit} {y: BitTree} [Perfect H y], x.val * y.toNat H % bound H = x.val * y.toNat H
    | 0, _, _, _ => Nat.mod_eq_of_lt (lt_of_eq_of_lt (zero_mul _) (bound_pos _))
    | 1, _, _, _ => Nat.mod_eq_of_lt (lt_of_eq_of_lt (one_mul _) (toNat_lt _))
  simpa only [karatsubaHelper₃,
    add_toNat (()::()::H), mulBit_ofNat, mulBit'_ofNat,
    bound_cons, ← mul_assoc, mul_zero,
    mul_right_comm _ _ (bound H),
    mul_right_comm _ (toNat _ _) (Fin.val _),
    mul_comm (toNat _ _) (bound H),
    Nat.add_right_comm _ (_ * toNat H y) (_ * toNat H x),
    Nat.add_right_comm _ (toNat _ _ * toNat _ _),
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

def karatsubaHelper₁ (H: List Unit) (z₀ z₂: BitTree) (z₃: BitTree): BitTree := z₃ - (node (zero H) z₂) - (node (zero H) z₀)

instance [Perfect H z₀] [Perfect H z₂] [Perfect (()::H) z₃]: Perfect (()::H) (karatsubaHelper₁ H z₀ z₂ z₃) := instPerfectSub

theorem karatsubaHelper₁_toNat
    (xhi xlo yhi ylo: BitTree)
    [Perfect H xhi]
    [Perfect H xlo]
    [Perfect H yhi]
    [Perfect H ylo]
    (z₀ z₂: BitTree) (z₃: BitTree)
    [Perfect (()::H) z₀]
    [Perfect (()::H) z₂]
    [Perfect (()::()::H) z₃]:
    z₀.toNat (()::H) = xlo.toNat H * ylo.toNat H →
    z₂.toNat (()::H) = xhi.toNat H * yhi.toNat H →
    z₃.toNat (()::()::H) = (xhi.toNat H + xlo.toNat H) * (yhi.toNat H + ylo.toNat H) →
    (karatsubaHelper₁ (()::H) z₀ z₂ z₃).toNat (()::()::H) = xhi.toNat H * ylo.toNat H + xlo.toNat H * yhi.toNat H := by
  intro h₀ h₂ h₃
  have h: ∀ {H: List Unit} {a b c d e f: BitTree} [Perfect H a] [Perfect H a] [Perfect H b] [Perfect H c] [Perfect H d] [Perfect H e] [Perfect H f],
      (a.toNat H * b.toNat H + c.toNat H * d.toNat H + e.toNat H * f.toNat H) % (bound H * bound H * bound H * bound H) =
      a.toNat H * b.toNat H + c.toNat H * d.toNat H + e.toNat H * f.toNat H :=
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
  have h': ∀ {H: List Unit} {a b c d: BitTree} [Perfect H a] [Perfect H b] [Perfect H c] [Perfect H d],
      (a.toNat H * b.toNat H + c.toNat H * d.toNat H) % (bound H * bound H * bound H * bound H) =
      a.toNat H * b.toNat H + c.toNat H * d.toNat H :=
    (congrArg₂ _ (congrArg _ (congrArg₂ _
      toNat_zero.symm toNat_zero.symm)) rfl).trans
    (h.trans (congrArg _ (congrArg₂ _
      toNat_zero toNat_zero)))
  have hs: ∀ {a b c: ℕ}, a + b + c - b = a + c :=
    (congrArg₂ _ (Nat.add_right_comm _ _ _) rfl).trans (Nat.add_sub_cancel _ _)
  simpa only [karatsubaHelper₁,
    sub_toNat (()::()::H), h₃, left_distrib, right_distrib, add_comm (xhi.toNat _ * yhi.toNat _), ←
    add_assoc, add_right_comm _ (xhi.toNat _ * yhi.toNat _), bound_cons, ← mul_assoc, toNat_node,
    toNat_zero, mul_zero, h₂, zero_add, add_tsub_cancel_right, toNat_ofNat, Nat.add_mod_right, h,
    h₀, hs, h'] using Nat.add_comm _ _


-- Just for complexity purposes - consider weaving height through addWithCarry instead
def mkPerfect: List Unit → BitTree → BitTree
| [], t => .bit (getBit t)
| _::H, t => .node (mkPerfect H (hi t)) (mkPerfect H (lo t))

instance (H: List Unit) {x: BitTree}: Perfect H (mkPerfect H x) :=
  match H with
  | [] => .bit _
  | _::H => .node (instPerfectMkPerfect H) (instPerfectMkPerfect H)

theorem mkPerfect_id: (H: List Unit) → (x: BitTree) → [Perfect H x] → mkPerfect H x = x
| _, _, .bit _ => rfl
| _, _, .node _ _ => congrArg₂ node (mkPerfect_id _ _) (mkPerfect_id _ _)

def karatsuba: (H: List Unit) → (x y: BitTree) → BitTree
| [], x, y => mulBit [()] (getBit x) (getBit y)
| _::H, x, y =>
  have x' := mkPerfect (()::H) x
  have y' := mkPerfect (()::H) y
  have xhi := hi x'
  have xlo := lo x'
  have yhi := hi y'
  have ylo := lo y'
  have z₂ := karatsuba H xhi yhi
  have z₀ := karatsuba H xlo ylo
  have zx := addWithCarry xhi xlo 0
  have zy := addWithCarry yhi ylo 0
  have z₃ := karatsubaHelper₃ H (karatsuba H zx.snd zy.snd) zx zy
  have z₁ := karatsubaHelper₁ (()::H) z₀ z₂ z₃
  (node z₂ (zero (()::H))) + lshift2 H z₁  + (node (zero (()::H)) z₀)

instance instPerfectKaratsuba
 [hx: Perfect H x] [hy: Perfect H y]: Perfect (()::H) (karatsuba H x y) := by
  match H, hx, hy with
  | _, .bit _, .bit _ => unfold karatsuba; infer_instance
  | _::H, .node _ _, .node yhi ylo =>
    haveI: ∀ {x y}, [Perfect H x] → [Perfect H y] → Perfect (()::H) (karatsuba H x y) := instPerfectKaratsuba
    unfold karatsuba; infer_instance

theorem karatsuba_eq_mul: (H: List Unit) → (x y: BitTree) → [Perfect H x] → [Perfect H y] → karatsuba H x y = ofNat (()::H) (toNat H x * toNat H y)
| _, _, _, .bit x, .bit y => mulBit_ofNat _ _ _
| _::H, .node xhi xlo, .node yhi ylo, .node _ _, .node _ _ => by
  have h: ∀ {H: List Unit} {x y: BitTree} [Perfect H x] [Perfect H y], x.toNat H * y.toNat H % (bound (()::H)) = x.toNat H * y.toNat H :=
    Nat.mod_eq_of_lt (lt_of_lt_of_eq (Nat.mul_lt_mul_for_real (toNat_lt _) (toNat_lt _)) (bound_cons _).symm)
  have karatsuba_toNat: ∀ {x y} [Perfect H x] [Perfect H y], toNat (()::H) (karatsuba H x y) = x.toNat H * y.toNat H :=
    (congrArg _ (karatsuba_eq_mul _ _ _)).trans ((toNat_ofNat _ _).trans h)
  have h₃:
      (karatsubaHelper₃ H
        (karatsuba H
          (addWithCarry xhi xlo 0).2
          (addWithCarry yhi ylo 0).2)
        (addWithCarry xhi xlo 0)
        (addWithCarry yhi ylo 0)) =
      ofNat (()::()::H) ((xhi.toNat H + xlo.toNat H) * (yhi.toNat H + ylo.toNat H)) :=
    toNat_inj (H := (()::()::H))
      (((karatsubaHelper₃_toNat _ _ _  karatsuba_toNat).trans
        (congrArg₂ _
          (addWithCarry_eq_add₀ _ _)
          (addWithCarry_eq_add₀ _ _))).trans
        (toNat_ofNat_lt (mul_lt_bound_cons
          (add_lt_bound_cons (toNat_lt _) (toNat_lt _))
           (add_lt_bound_cons (toNat_lt _) (toNat_lt _)))).symm)
  have h₁:
        (karatsubaHelper₁ (() :: H) (karatsuba H xlo ylo) (karatsuba H xhi yhi)
            (ofNat (() :: () :: H) ((toNat H xhi + toNat H xlo) * (toNat H yhi + toNat H ylo)))) =
        ofNat (()::()::H) (xlo.toNat H * yhi.toNat H + xhi.toNat H * ylo.toNat H) :=
      toNat_inj (H := (()::()::H))
        (((karatsubaHelper₁_toNat xhi xlo yhi ylo _ _ _ karatsuba_toNat karatsuba_toNat
          (toNat_ofNat_lt (mul_lt_bound_cons
            (add_lt_bound_cons (toNat_lt _) (toNat_lt _))
            (add_lt_bound_cons (toNat_lt _) (toNat_lt _))))).trans
          (add_comm _ _)).trans
          (toNat_ofNat_lt (add_lt_bound_cons
            (mul_lt_bound_cons (toNat_lt _) (toNat_lt _))
            (mul_lt_bound_cons (toNat_lt _) (toNat_lt _)))).symm)
  simp only [karatsuba, h₃, h₁, mkPerfect_id, hi, lo]
  apply Eq.trans
  apply add_toNat (()::()::H)
  apply congrArg
  apply Eq.trans
  apply congrArg₂
  apply congrArg
  apply Eq.trans
  apply add_toNat (()::()::H)
  apply congrArg
  apply congrArg
  apply lshift2_toNat
  rfl
  simp only [toNat_ofNat, toNat_node, toNat_zero, add_zero, karatsuba_toNat,
    mul_zero, zero_add, left_distrib, right_distrib,
    bound_cons, ← mul_assoc, ← add_assoc,
    mul_right_comm _ _ (bound H), mul_comm (toNat _ _) (bound H), mul_comm (_ % _) (bound H),
    Nat.add_mod_mod, add_left_inj]
  apply Eq.trans
  apply congrArg₂
  apply congrArg
  apply congrArg
  apply Nat.mod_eq_of_lt
  apply add_lt_mul_bound
  apply le_trans _
  apply Nat.le_mul_of_pos_right (bound_pos _)
  apply le_of_lt
  apply Nat.mul_lt_mul_for_real
  apply toNat_lt _
  apply toNat_lt _
  apply lt_of_lt_of_le _
  apply Nat.le_mul_of_pos_right (bound_pos _)
  apply Nat.mul_lt_mul_for_real
  apply toNat_lt _
  apply toNat_lt _
  rfl
  simp only [left_distrib, ← add_assoc, ← mul_assoc]
  apply Nat.mod_eq_of_lt
  apply lt_of_le_of_lt (b := (node xhi xlo).toNat (()::H) * (node yhi ylo).toNat (()::H))
  { simp [toNat_node, left_distrib, right_distrib, add_assoc, ← mul_assoc, mul_right_comm _ (toNat _ _) (bound _), mul_comm (toNat _ _) (bound _)] }
  apply lt_of_lt_of_eq _ (mul_assoc _ _ _).symm
  apply Nat.mul_lt_mul_for_real
  apply lt_of_lt_of_eq (toNat_lt _) (bound_cons _)
  apply lt_of_lt_of_eq (toNat_lt _) (bound_cons _)
end BitTree

def Nat.karatsuba (n m: ℕ): ℕ :=
  have H := Unary.max (BitTree.getHeight n) (BitTree.getHeight m)
  BitTree.toNat (()::H) (BitTree.karatsuba H (BitTree.ofNat H n) (BitTree.ofNat H m))

theorem Nat.karatsuba_eq_mul: karatsuba = Nat.mul := funext λ n ↦ funext λ m ↦
  have hn : n < BitTree.bound (Unary.max (BitTree.getHeight n) (BitTree.getHeight m)) :=
    lt_of_lt_of_le BitTree.lt_bound_getHeight (BitTree.bound_le_bound (le_of_le_of_eq (le_max_left _ _) (Unary.length_max _ _).symm))
  have hm : m < BitTree.bound (Unary.max (BitTree.getHeight n) (BitTree.getHeight m)) :=
    lt_of_lt_of_le BitTree.lt_bound_getHeight (BitTree.bound_le_bound (le_of_le_of_eq (le_max_right _ _) (Unary.length_max _ _).symm))
  (congrArg (BitTree.toNat _) (BitTree.karatsuba_eq_mul _ _ _)).trans
    ((congrArg _ (congrArg _ (congrArg₂ _
      (BitTree.toNat_ofNat_lt hn)
      (BitTree.toNat_ofNat_lt hm)))).trans
      (BitTree.toNat_ofNat_lt (BitTree.mul_lt_bound_cons hn hm)))
