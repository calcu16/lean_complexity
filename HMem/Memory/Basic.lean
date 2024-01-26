import HMem.Memory.Canonical

/-!
This file defines the Memory data structure.

This Memory structure is equivalent to an infinite binary tree with all nodes starting at zero.
This is implemented by a quotient over Tree Bool that recursively treats
  .nil as (.node false .nil nil)
-/

namespace HMem
local instance Memory.setoid: Setoid (Tree Bool) where
  r lhs rhs := canonical lhs = canonical rhs
  iseqv := ⟨ λ _ ↦ Eq.refl _, Eq.symm, Eq.trans ⟩


def Memory: Type _ := Quotient Memory.setoid

namespace Memory
def out: Memory → Tree Bool := Quotient.lift Memory.canonical (λ _ _ ↦ id)
theorem out_exact {m: Tree Bool}: out ⟦m⟧ = canonical m :=
  Quotient.lift_mk (s := Memory.setoid) _ (λ _ _ ↦ id) _

@[simp] theorem out_sound {m: Memory}: ⟦m.out⟧ = m :=
  (Quotient.exists_rep m).elim λ _ h ↦ h ▸
    Quotient.sound (canonical_idempotent.trans out_exact)


theorem out_inj {m₀ m₁: Memory} (h: out m₀ = out m₁): m₀ = m₁ :=
  @out_sound m₀ ▸ @out_sound m₁ ▸ congrArg (Quotient.mk setoid) h

@[simp] theorem canonical_out {m: Memory}: canonical m.out = m.out :=
  out_sound (m := m) ▸ out_exact ▸ canonical_idempotent

instance: Repr Memory := ⟨ Repr.reprPrec ∘ Memory.out ⟩

def mk (v: Bool) (lhs rhs: Memory): Memory := ⟦.node v lhs.out rhs.out⟧

instance: Zero Memory where
  zero := ⟦.nil⟧

instance: One Memory where
  one := ⟦.node true .nil .nil⟧

instance: NeZero (1:Memory) where
  out h := Tree.noConfusion (Quotient.exact h)

instance: DecidableEq Memory := λ a b ↦
  if h:a.out = b.out
  then Decidable.isTrue (out_inj h)
  else Decidable.isFalse (h ∘ congrArg _)

instance: Coe Memory Bool where
  coe x := x ≠ 0

@[simp] theorem eq_zero_symm {m: Memory}: (0 = m) = (m = 0) := iff_iff_eq.mp ⟨ Eq.symm, Eq.symm ⟩

def size (m: Memory): ℕ := m.out.numNodes

def height (m: Memory): ℕ := m.out.height

theorem size_zero_iff {m: Memory}: m.size = 0 ↔ m = 0 := ⟨
    λ hm ↦ match h:out m with
    | .nil => out_inj h
    | .node _ _ _ => absurd
      (hm.symm.trans (congr_arg Tree.numNodes h))
      Nat.noConfusion,
    λ hm ↦ hm ▸ rfl ⟩

@[simp] theorem size_zero (m: Memory): (m.size = 0) = (m = 0) :=
  iff_iff_eq.mp size_zero_iff

def getv (m: Memory): Bool := m.out.getOrElse 1 false
def getm (m: Memory): Bool → Memory
| false => ⟦m.out.left⟧
| true => ⟦m.out.right⟧

@[simp] theorem getv_mk: (mk v f t).getv = v := canonical_getOrElse
@[simp] theorem getm_mk_f: (mk v f t).getm false = f :=
  (congrArg (Quotient.mk setoid) canonical_left.symm).trans
  ((congrArg (Quotient.mk setoid) canonical_out).trans
  out_sound)
@[simp] theorem getm_mk_t: (mk v f t).getm true = t :=
  (congrArg (Quotient.mk setoid) canonical_right.symm).trans
  ((congrArg (Quotient.mk setoid) canonical_out).trans
  out_sound)
@[simp] theorem getm_mk: {b: Bool} → (mk v m m).getm b = m
| false => getm_mk_f
| true => getm_mk_t
theorem inj {m₀ m₁: Memory}: m₀.getv = m₁.getv → m₀.getm = m₁.getm → m₀ = m₁ :=
  λ hv hm ↦
    @out_sound m₀ ▸
    @out_sound m₁ ▸
    Quotient.sound (canonical_congr hv
      (Quotient.exact (congrFun hm false))
      (Quotient.exact (congrFun hm true)))

theorem mk_eq (m: Memory): mk m.getv (m.getm false) (m.getm true) = m :=
  inj getv_mk (funext λ | false => getm_mk_f | true => getm_mk_t)

theorem zero_def: (0:Memory) = ⟦.nil⟧ := rfl
@[simp] theorem zero_out: (0:Memory).out = .nil := rfl
@[simp] theorem zero_def': mk false 0 0 = 0 := inj rfl rfl
@[simp] theorem zero_getv: getv 0 = false := rfl
@[simp] theorem zero_getm: {b: Bool} → getm 0 b = 0
| false => rfl
| true => rfl
@[simp] theorem one_def: 1 = mk true 0 0 := rfl

theorem mk_inj_iff: mk v₀ f₀ t₀ = mk v₁ f₁ t₁ ↔ v₀ = v₁ ∧ f₀ = f₁ ∧ t₀ = t₁ :=
  ⟨ λ h ↦ ⟨
      getv_mk (v := v₀) ▸ getv_mk (v := v₁) ▸ congrArg getv h,
      getm_mk_f (f := f₀) ▸ getm_mk_f (f := f₁) ▸ congrArg₂ getm h (Eq.refl false),
      getm_mk_t (t := t₀) ▸ getm_mk_t (t := t₁) ▸ congrArg₂ getm h (Eq.refl true) ⟩,
    λ h ↦ inj (getv_mk ▸ getv_mk ▸ h.left) (funext λ
    | false => getm_mk_f ▸ getm_mk_f ▸ h.right.left
    | true => getm_mk_t ▸ getm_mk_t ▸ h.right.right)⟩

@[simp] theorem mk_eq_inj: (mk v f t = m) = (v = m.getv ∧ f = m.getm false ∧ t = m.getm true) :=
  eq_iff_iff.mpr ⟨ λ h ↦ mk_inj_iff.mp (h.trans (mk_eq m).symm), λ h ↦ (mk_inj_iff.mpr h).trans (mk_eq m) ⟩

@[simp] theorem eq_mk_inj: (m = mk v f t) = (m.getv = v ∧ m.getm false = f ∧ m.getm true = t) :=
  eq_iff_iff.mpr ⟨ λ h ↦ mk_inj_iff.mp ((mk_eq m).trans h), λ h ↦  (mk_eq m).symm.trans (mk_inj_iff.mpr h) ⟩

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
| _::tl => (congrArg (λ m ↦ getmp m tl) zero_getm).trans zero_getmp

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

end HMem.Memory
