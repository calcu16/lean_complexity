import Mathlib.Init.ZeroOne
import Mathlib.Algebra.NeZero
import Mathlib.Data.Quot
import Mathlib.Data.Nat.Bits

namespace HMem

inductive _Memory
| leaf
| node (value: Bool) (t f: _Memory)
deriving DecidableEq, Inhabited, Repr

namespace _Memory
def size: _Memory → ℕ
| leaf => 0
| node _ t f => size t + size f + 1

def getv: _Memory → Bool
| leaf => false
| node v _ _ => v

def getm: _Memory → Bool → _Memory
| leaf, _ => leaf
| node _ f _, false => f
| node _ _ t, true => t

@[simp] theorem getv_node: (node v f t).getv = v := rfl
theorem getm_node_false: (node v f t).getm false = f := rfl
theorem getm_node_true: (node v f t).getm true = t := rfl

def canonical: _Memory → _Memory
| leaf => leaf
| node v f t =>
  match v, f.canonical, t.canonical with
  | false, leaf, leaf => leaf
  | v', f', t' => node v' f' t'

instance setoid: Setoid _Memory where
  r lhs rhs := lhs.canonical = rhs.canonical
  iseqv := ⟨ λ _ ↦ Eq.refl _, Eq.symm, Eq.trans ⟩

@[simp] theorem canonical_leaf_def: leaf.canonical = leaf := rfl

theorem canonical_node_def {v: Bool} {f t: _Memory}:
  (node v f t).canonical =
    match v, f.canonical, t.canonical with
    | false, leaf, leaf => leaf
    | v', f', t' => node v' f' t' := rfl

theorem canonical_getv: {m: _Memory} →
  m.canonical.getv = m.getv
| leaf => rfl
| node v f t => canonical_node_def ▸
  match v, hf:f.canonical, ht:t.canonical with
  | false, leaf, leaf => rfl
  | false, leaf, node _ _ _ => rfl
  | false, node _ _ _, _ => rfl
  | true, _, _ => rfl

theorem canonical_getm: {m: _Memory} → {b: Bool} →
  (m.getm b).canonical = m.canonical.getm b
| leaf, _ => rfl
| node v f t, b => canonical_node_def ▸
  match b, v, hf:f.canonical, ht:t.canonical with
  | false, false, leaf, leaf => hf
  | true, false, leaf, leaf => ht
  | false, false, leaf, node _ _ _ => hf
  | true, false, leaf, node _ _ _ => ht
  | false, false, node _ _ _, _ => hf
  | true, false, node _ _ _, _ => ht
  | false, true, _, _ => hf
  | true, true, _, _ => ht

theorem canonical_leaf: {m: _Memory} →
    m.getv = false →
    (∀ b, (m.getm b).canonical = leaf) →
    m.canonical = leaf
| leaf, _, _ => rfl
| node _ _ _, rfl, hm => canonical_node_def ▸
    (hm false).symm.trans (congrArg _ getm_node_false) ▸
    (hm true).symm.trans (congrArg _ getm_node_true) ▸
    rfl

theorem canonical_cases (m: _Memory):
  m.canonical = leaf ∨
  m.canonical = node m.getv (m.getm false).canonical (m.getm true).canonical :=
match h:m.canonical with
| leaf => Or.inl rfl
| node _ _ _ => Or.inr (congr (congrArg₂ _
    ((congrArg getv h).symm.trans canonical_getv)
    (canonical_getm.trans (congrArg₂ _ h (Eq.refl false))).symm)
    (canonical_getm.trans (congrArg₂ _ h (Eq.refl true))).symm)

theorem canonical_node {m: _Memory} (h: m.canonical ≠ leaf):
    m.canonical = node m.getv (m.getm false).canonical (m.getm true).canonical :=
  m.canonical_cases.elim (flip absurd h) id

theorem canonical_congr: {m₀ m₁: _Memory} →
  m₀.getv = m₁.getv →
  (∀ b, (m₀.getm b).canonical = (m₁.getm b).canonical) →
  m₀.canonical = m₁.canonical
| leaf, leaf, _, _ => rfl
| leaf, node _ _ _, hv, hm => (canonical_leaf hv.symm λ _ ↦ (hm _).symm).symm
| node v₀ f₀ t₀, m₁, hv, hm =>
  match canonical_cases (node v₀ f₀ t₀), canonical_cases m₁ with
  | Or.inl h₀, Or.inl h₁ => h₀ ▸ h₁ ▸ rfl
  | Or.inl h₀, Or.inr h₁ =>
    absurd (h₁.symm.trans (canonical_leaf
        (hv.symm.trans (canonical_getv.symm.trans (congrArg _ h₀)))
        λ _ ↦ (hm _).symm.trans (canonical_getm.trans (congrArg₂ _ h₀ rfl))))
      _Memory.noConfusion
  | Or.inr h₀, Or.inl h₁ =>
    absurd (h₀.symm.trans (canonical_leaf
        (hv.trans (canonical_getv.symm.trans (congrArg _ h₁)))
        λ _ ↦ (hm _).trans (canonical_getm.trans (congrArg₂ _ h₁ rfl))))
      _Memory.noConfusion
  | Or.inr h₀, Or.inr h₁ => h₀ ▸ h₁ ▸ congr (congrArg₂ _ hv (hm false)) (hm true)

@[simp] theorem canonical_idempotent: {m: _Memory} → m.canonical.canonical = m.canonical
| leaf => rfl
| node _ _ _ => canonical_congr canonical_getv λ
  | false => (congrArg _ canonical_getm.symm).trans canonical_idempotent
  | true => (congrArg _ canonical_getm.symm).trans canonical_idempotent

theorem canonical_le_height: (m: _Memory) → m.canonical.size ≤ m.size
| .leaf => Nat.zero_le _
| .node v f t =>
  match canonical_cases (node v f t) with
  | Or.inl h => h ▸ Nat.zero_le _
  | Or.inr h => h ▸  Nat.succ_le_succ (Nat.add_le_add
    (canonical_le_height f)
    (canonical_le_height t))

end _Memory

def Memory: Type _ := Quotient _Memory.setoid

namespace Memory
def out: Memory → _Memory := Quotient.lift _Memory.canonical (λ _ _ ↦ id)
theorem out_exact {m: _Memory}: out ⟦m⟧ = m.canonical :=
  Quotient.lift_mk (s := _Memory.setoid) _ (λ _ _ ↦ id) _

@[simp] theorem out_sound {m: Memory}: ⟦m.out⟧ = m :=
  (Quotient.exists_rep m).elim λ _ h ↦ h ▸
    Quotient.sound (_Memory.canonical_idempotent.trans out_exact)

theorem out_inj {m₀ m₁: Memory} (h: out m₀ = out m₁): m₀ = m₁ :=
  @out_sound m₀ ▸ @out_sound m₁ ▸ congrArg Quotient.mk' h

@[simp] theorem canonical_out {m: Memory}: m.out.canonical = m.out :=
  out_sound (m := m) ▸ out_exact ▸ _Memory.canonical_idempotent

instance: Repr Memory := ⟨ Repr.reprPrec ∘ Memory.out ⟩

def mk (v: Bool) (f t: Memory): Memory := ⟦.node v f.out t.out⟧

instance: Zero Memory where
  zero := ⟦.leaf⟧

instance: One Memory where
  one := ⟦.node true .leaf .leaf⟧

instance: NeZero (1:Memory) where
  out h := Bool.noConfusion (congrArg _Memory.getv (Quotient.exact h))

instance: DecidableEq Memory := λ a b ↦
  if h:a.out = b.out
  then Decidable.isTrue (out_inj h)
  else Decidable.isFalse (h ∘ congrArg _)

instance: Coe Memory Bool where
  coe x := x ≠ 0

@[simp] theorem eq_zero_symm {m: Memory}: (0 = m) = (m = 0) := iff_iff_eq.mp ⟨ Eq.symm, Eq.symm ⟩

def size (m: Memory): ℕ := m.out.size

theorem size_zero_iff {m: Memory}: m.size = 0 ↔ m = 0 := ⟨
    λ hm ↦ match h:out m with
    | .leaf => out_inj h
    | .node _ _ _ => absurd
      (hm.symm.trans (congr_arg _Memory.size h))
      Nat.noConfusion,
    λ hm ↦ hm ▸ rfl ⟩

theorem size_zero (m: Memory): (m.size = 0) = (m = 0) :=
  iff_iff_eq.mp size_zero_iff

def getv (m: Memory): Bool := m.out.getv
def getm (m: Memory) (b: Bool): Memory := ⟦m.out.getm b⟧

theorem getm_size (m: Memory) (b: Bool): (m.getm b).size ≤ m.size.pred :=
  match h:m.out, b with
  | .leaf, _ => le_of_eq_of_le
    (congrArg size (congrArg Quotient.mk' (congrArg₂ _ h rfl)))
    (Nat.zero_le _)
  | .node _ _ _, false => le_of_eq_of_le
    (congrArg size (congrArg Quotient.mk' (congrArg₂ _ h rfl)))
    (le_of_le_of_eq (le_trans
      (_Memory.canonical_le_height _)
      (Nat.le_add_right _ _))
      (congrArg Nat.pred (congrArg _Memory.size h.symm)))
  | .node _ _ _, true => le_of_eq_of_le
    (congrArg size (congrArg Quotient.mk' (congrArg₂ _ h rfl)))
    (le_of_le_of_eq (le_trans
      (_Memory.canonical_le_height _)
      (Nat.le_add_left _ _))
      (congrArg Nat.pred (congrArg _Memory.size h.symm)))

theorem getv_eq (m: _Memory): getv ⟦m⟧ = m.getv := _Memory.canonical_getv
theorem getm_eq (m: _Memory) (b: Bool): getm ⟦m⟧ b = ⟦m.getm b⟧ :=
  Quotient.sound (out_exact ▸ _Memory.canonical_getm.symm ▸ _Memory.canonical_idempotent)

@[simp] theorem getv_mk: (mk v f t).getv = v := getv_eq _
@[simp] theorem getm_mk_f: (mk v f t).getm false = f := (getm_eq _ _).trans out_sound
@[simp] theorem getm_mk_t: (mk v f t).getm true = t := (getm_eq _ _).trans out_sound
@[simp] theorem getm_mk: {b: Bool} → (mk v m m).getm b = m
| false => getm_mk_f
| true => getm_mk_t

theorem inj {m₀ m₁: Memory}: m₀.getv = m₁.getv → m₀.getm = m₁.getm → m₀ = m₁ :=
  λ hv hm ↦
    @out_sound m₀ ▸
    @out_sound m₁ ▸
    Quotient.sound (_Memory.canonical_congr hv λ _ ↦
      Quotient.exact (congrFun hm _))

theorem mk_eq (m: Memory): mk m.getv (m.getm false) (m.getm true) = m :=
  inj (getv_eq _) (funext λ
  | false => getm_mk_f
  | true => getm_mk_t)

theorem zero_def: (0:Memory) = ⟦.leaf⟧ := rfl
@[simp] theorem zero_out: (0:Memory).out = .leaf := rfl
@[simp] theorem zero_def': mk false 0 0 = 0 := inj rfl rfl
@[simp] theorem zero_getv: getv 0 = false := rfl
@[simp] theorem zero_getm: getm 0 b = 0 := rfl
@[simp] theorem one_def: 1 = mk true 0 0 := rfl

@[simp] theorem mk_inj: (mk v₀ f₀ t₀ = mk v₁ f₁ t₁) ↔ (v₀ = v₁ ∧ f₀ = f₁ ∧ t₀ = t₁) :=
  ⟨
    λ h ↦ ⟨
      getv_mk (v := v₀) ▸ getv_mk (v := v₁) ▸ congrArg getv h,
      getm_mk_f (f := f₀) ▸ getm_mk_f (f := f₁) ▸ congrArg₂ getm h (Eq.refl false),
      getm_mk_t (t := t₀) ▸ getm_mk_t (t := t₁) ▸ congrArg₂ getm h (Eq.refl true) ⟩,
    λ h ↦ inj (getv_mk ▸ getv_mk ▸ h.left) (funext λ
    | false => getm_mk_f ▸ getm_mk_f ▸ h.right.left
    | true => getm_mk_t ▸ getm_mk_t ▸ h.right.right)⟩

@[simp] theorem mk_injEq: (mk v₀ f₀ t₀ = mk v₁ f₁ t₁) = (v₀ = v₁ ∧ f₀ = f₁ ∧ t₀ = t₁) :=
  eq_iff_iff.mpr mk_inj

@[simp] theorem mk_zero_injEq: (mk v f t = 0) = (v = false ∧ f = 0 ∧ t = 0) := zero_def' ▸ mk_injEq

def setv (m: Memory) (v: Bool): Memory := mk v (m.getm false) (m.getm true)
def setm (m: Memory): Bool → Memory → Memory
| false => flip (mk m.getv) (m.getm true)
| true => mk m.getv (m.getm false)

@[simp] theorem setv_def: setv m v = mk v (m.getm false) (m.getm true) := rfl
@[simp] theorem setm_f_def: setm m false ma = mk m.getv ma (m.getm true) := rfl
@[simp] theorem setm_t_def: setm m true ma = mk m.getv (m.getm false) ma := rfl
@[simp] theorem setm_setm: (setm m b ma₀).setm b ma₁ = m.setm b ma₁ := by cases b <;> simp

theorem getv_setv: (setv m v).getv = v := by simp
@[simp] theorem getm_setv: (setv m v).getm = m.getm := by funext b; cases b <;> simp
@[simp] theorem getv_setm: (setm m b ma).getv = m.getv := by cases b <;> simp
@[simp] theorem getm_setm_eq: (setm m b ma).getm b = ma := by cases b <;> simp

def getmp (m: Memory): List Bool → Memory
| [] => m
| b::bs => (m.getm b).getmp bs

@[simp] theorem getmp_nil: getmp m [] = m := rfl
@[simp] theorem getmp_cons: getmp m (b::bs) = (m.getm b).getmp bs := rfl
@[simp] theorem zero_getmp: {bs: List Bool} → getmp 0 bs = 0
| [] => rfl
| _::tl => @zero_getmp tl

def setmp (m: Memory): List Bool → Memory → Memory
| [] => id
| b::bs => m.setm b ∘ (m.getm b).setmp bs

@[simp] theorem setmp_nil: setmp m [] ma = ma := rfl
@[simp] theorem setmp_cons: setmp m (b::bs) ma = m.setm b ((m.getm b).setmp bs ma) := rfl
@[simp] theorem setmp_setmp: {m: Memory} → {bs: List Bool} → setmp (setmp m bs ma₀) bs ma₁ = setmp m bs ma₁
| _, [] => rfl
| m, (b::bs) => by simp [setmp_setmp (bs := bs)]

def getvp (m: Memory): List Bool → Bool := getv ∘ getmp m
def setvp (m: Memory) (bs: List Bool): Bool → Memory := m.setmp bs ∘ (m.getmp bs).setv

@[simp] theorem getvp_nil: getvp m [] = m.getv := rfl
@[simp] theorem getvp_cons: getvp m (b::bs) = (m.getm b).getvp bs := rfl
@[simp] theorem zero_getvp: getvp 0 bs = false := congrArg getv zero_getmp
@[simp] theorem setvp_nil: setvp m [] v = m.setv v := rfl
@[simp] theorem setvp_cons: setvp m (b::bs) v = m.setm b ((m.getm b).setvp bs v) := rfl

@[simp] theorem getv_getmp: getv (getmp m bs) = getvp m bs := rfl

@[elab_as_elim] def recOn.{u} {motive: Memory → Sort u} (m: Memory) (base: motive 0) (ind: ∀ (b: Bool) (f t: Memory), Memory.size (.mk b f t) > 0 → motive f → motive t → motive (.mk b f t)): motive m :=
  match h:m.size with
  | 0 => size_zero_iff.mp h ▸ base
  | (n+1) =>
    have: (getm m false).size < m.size := lt_of_le_of_lt (getm_size _ _) (h ▸ Nat.lt_succ_self _)
    have: (getm m true).size < m.size := lt_of_le_of_lt (getm_size _ _) (h ▸ Nat.lt_succ_self _)
    mk_eq m ▸ ind _ _ _
      (lt_of_lt_of_eq (Nat.zero_lt_succ n) ((congrArg _ (mk_eq _)).trans h).symm)
      (recOn _ base ind)
      (recOn _ base ind)
termination_by _ m _ _ => m.size

end Memory

inductive Source
| nil
| imm (hd: Bool) (tl: Source)
| idx (hd tl: Source)
deriving Repr

namespace Source
def height: Source → ℕ
| nil => 0
| imm _ tl => height tl + 1
| idx hd tl => max (height hd) (height tl) + 1
@[simp] theorem height_imm_tl: tl.height < (imm hd tl).height := Nat.lt_succ_self _
@[simp] theorem height_idx_hd: hd.height < (idx hd tl).height := Nat.lt_succ_of_le (le_max_left _ _)
@[simp] theorem height_idx_tl: tl.height < (idx hd tl).height := Nat.lt_succ_of_le (le_max_right _ _)

def size: Source → ℕ
| nil => 0
| imm _ tl => size tl + 1
| idx hd tl => size hd + size tl + 1
@[simp] theorem size_imm_tl: tl.size < (imm hd tl).size := Nat.lt_succ_self _
@[simp] theorem size_idx_hd: hd.size < (idx hd tl).size := Nat.lt_succ_of_le (Nat.le_add_right _ _)
@[simp] theorem size_idx_tl: tl.size < (idx hd tl).size := Nat.lt_succ_of_le (Nat.le_add_left _ _)


def get: Source → Memory → List Bool
| nil, _ => []
| imm hd tl, m => hd::(tl.get m)
| idx hd tl, m => m.getvp (hd.get m)::tl.get m

@[simp] theorem get_nil: nil.get m = [] := rfl
@[simp] theorem get_imm: (imm hd tl).get m = hd::(tl.get m) := rfl
@[simp] theorem get_idx: (idx hd tl).get m = m.getvp (hd.get m)::(tl.get m) := rfl

def convert (f: Memory → List Bool → β) (m: Memory) (s: Source): β := f m (s.get m)

@[simp] def succ': Source → (Bool × Source)
| nil => (true, nil)
| idx hd tl => (true, idx hd tl)
| imm hd tl => match succ' tl, hd with
  | (false, tl), hd => (false, imm hd tl)
  | (true, tl), false => (false, imm true tl)
  | (true, tl), true =>  (true, imm false tl)

@[simp] def succ (s: Source): Source :=
  match s.succ' with
  | (false, s) => s
  | (true, tl) => .imm false tl

def fromNat: ℕ → Source
| 0 => .nil
| (n+1) => (fromNat n).succ

instance: OfNat Source n := ⟨ fromNat n ⟩
@[simp] theorem ofNatZero: (OfNat.ofNat 0:Source) = .nil := rfl
@[simp] theorem ofNatSucc: (OfNat.ofNat (n+1):Source) = succ (OfNat.ofNat n) := rfl

end Source

namespace Memory
def getvs: Memory → Source → Bool := Source.convert getvp
def getms: Memory → Source → Memory := Source.convert getmp
def setvs: Memory → Source → Bool → Memory := Source.convert setvp
def setms: Memory → Source → Memory → Memory := Source.convert setmp

@[simp] theorem getvs_def: getvs m s = m.getvp (s.get m) := rfl
@[simp] theorem getms_def: getms m s = m.getmp (s.get m) := rfl
@[simp] theorem setvs_def: setvs m s = m.setvp (s.get m) := rfl
@[simp] theorem setms_def: setms m s = m.setmp (s.get m) := rfl

end Memory
end HMem
