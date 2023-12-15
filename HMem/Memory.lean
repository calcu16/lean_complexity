import Mathlib.Init.ZeroOne
import Mathlib.Algebra.NeZero
import Mathlib.Data.Quot

namespace HMem

inductive _Memory
| leaf
| node (value: Bool) (t f: _Memory)
deriving DecidableEq, Inhabited

namespace _Memory
def getv: _Memory → Bool
| leaf => false
| node v _ _ => v

def getm: _Memory → Bool → _Memory
| leaf, _ => leaf
| node _ f _, false => f
| node _ _ t, true => t

theorem getm_node_false: (node v f t).getm false = f := rfl
theorem  getm_node_true: (node v f t).getm true = t := rfl

def setv (m₀: _Memory) (b: Bool): _Memory := node b (m₀.getm false) (m₀.getm true)

def setm: _Memory → Bool → _Memory → _Memory
| m, false, ma => node m.getv ma (m.getm true)
| m, true, ma => node m.getv (m.getm false) ma

def getmp: _Memory → List Bool → _Memory
| m, [] => m
| m, a::as => (m.getm a).getmp as

theorem getmp_leaf: (p: List Bool) → leaf.getmp p = leaf
| [] => rfl
| _::as => getmp_leaf as

theorem getmp_append (m: _Memory): (lhs rhs: List Bool) → m.getmp (lhs ++ rhs) = (m.getmp lhs).getmp rhs
| [], _ => rfl
| _::ls, _ => getmp_append _ ls _

def setmp: _Memory → List Bool → _Memory → _Memory
| _, [], ma => ma
| m, a::as, ma => m.setm a ((m.getm a).setmp as ma)

def getvp (m: _Memory) (as: List Bool): Bool := (m.getmp as).getv

theorem getvp_leaf (as: List Bool): leaf.getvp as = false := congrArg _ (getmp_leaf _)

theorem getvp_append (m: _Memory) (lhs rhs: List Bool): m.getvp (lhs ++ rhs) = (m.getmp lhs).getvp rhs := congr_arg _ (getmp_append _ _ _)

def setvp (m: _Memory) (as: List Bool) (v: Bool): _Memory :=
  m.setmp as ((m.getmp as).setv v)

instance setoid: Setoid _Memory where
  r lhs rhs := ∀ as, lhs.getvp as = rhs.getvp as
  iseqv := ⟨ λ _ _ ↦ rfl, λ h _ ↦ (h _).symm, λ hxy hyz _ ↦ (hxy _).trans (hyz _) ⟩

theorem equiv_of_eq: {m₀ m₁: _Memory} → m₀ = m₁ → m₀ ≈ m₁
| _, _, rfl => Setoid.refl _

def getvp_congr {m₀ m₁: _Memory} (p: List Bool) (h: m₀ ≈ m₁):
    m₀.getmp p ≈ m₁.getmp p :=
  λ _ ↦ getvp_append m₀ p _ ▸ getvp_append m₁ p _ ▸ h _

def getvp_congr' {m₀ m₁ mp₀ mp₁: _Memory} (p: List Bool)
    (h: m₀ ≈ m₁)
    (h₀: m₀.getmp p = mp₀)
    (h₁: m₁.getmp p = mp₁):
    mp₀ ≈ mp₁ :=
  h₁ ▸ h₀ ▸ getvp_congr p h

def getvp_inj {m₀ m₁: _Memory} (hv: m₀.getv = m₁.getv) (hm: ∀ b, m₀.getm b ≈ m₁.getm b): m₀ ≈ m₁
| [] => hv
| _::_ => hm _ _

def getvp_inj' {m₀ m₁: _Memory}
    (hv: m₀.getv = m₁.getv)
    (hf: m₀.getm false ≈ m₁.getm false)
    (ht: m₀.getm true ≈ m₁.getm true):
    m₀ ≈ m₁ :=
  getvp_inj hv λ
  | false => hf
  | true => ht

def canonical: _Memory → _Memory
| leaf => leaf
| node v f t =>
  match v, f.canonical, t.canonical with
  | false, leaf, leaf => leaf
  | v', f', t' => node v' f' t'

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
    (m.getm false).canonical = leaf →
    (m.getm true).canonical = leaf →
    m.canonical = leaf
| leaf, _, _, _ => rfl
| node _ _ _, rfl, hf, ht => canonical_node_def ▸
    hf.symm.trans (congrArg _ getm_node_false) ▸
    ht.symm.trans (congrArg _ getm_node_true) ▸
    rfl

theorem canonical_cases (m: _Memory): m.canonical = leaf ∨ m.canonical = node m.getv (m.getm false).canonical (m.getm true).canonical :=
match h:m.canonical with
| leaf => Or.inl rfl
| node _ _ _ => Or.inr (congr (congrArg₂ _
    ((congrArg getv h).symm.trans canonical_getv)
    (canonical_getm.trans (congrArg₂ _ h (Eq.refl false))).symm)
    (canonical_getm.trans (congrArg₂ _ h (Eq.refl true))).symm)

theorem canonical_equiv: {m: _Memory} → m.canonical ≈ m
| leaf, _ => rfl
| node _ _ _, [] => canonical_getv
| node _ _ _, false::_ =>
  (congrArg (flip getvp _) canonical_getm.symm).trans (canonical_equiv _)
| node _ _ _, true::_ =>
  (congrArg (flip getvp _) canonical_getm.symm).trans (canonical_equiv _)

theorem canonical_equiv' {m₀ m₁ m₂: _Memory}: m₀ ≈ m₁ → m₁.canonical = m₂ → m₀ ≈ m₂ :=
  λ h₀ h₁ ↦ h₁ ▸ Setoid.trans h₀ (Setoid.symm (canonical_equiv (m := m₁)))

theorem canonical_of_equiv_leaf: {m: _Memory} → m ≈ leaf → m.canonical = leaf
| leaf, _ => rfl
| node _ _ _, h => canonical_leaf (h [])
    (canonical_of_equiv_leaf (getvp_congr [false] h))
    (canonical_of_equiv_leaf (getvp_congr [true] h))

theorem canonical_of_equiv: {m₀ m₁: _Memory} → m₀ ≈ m₁ → m₀.canonical = m₁.canonical
| leaf, leaf, _ => rfl
| leaf, _, h => (canonical_of_equiv_leaf (Setoid.symm h)).symm
| _, leaf, h => canonical_of_equiv_leaf h
| node v₀ f₀ t₀, node v₁ f₁ t₁, h =>
  (canonical_cases (node v₀ f₀ t₀)).elim
    (λ h₀ ↦ h₀.trans (canonical_of_equiv_leaf (canonical_equiv' (Setoid.symm h) h₀)).symm)
    λ h₀ ↦ (canonical_cases (node v₁ f₁ t₁)).elim
      (λ h₁ ↦ absurd (h₀.symm.trans (canonical_of_equiv_leaf (canonical_equiv' h h₁))) _Memory.noConfusion)
      λ h₁ ↦ h₀ ▸ h₁ ▸ congr
        (congrArg₂ _ (h []) (canonical_of_equiv (getvp_congr [false] h)))
        (canonical_of_equiv (getvp_congr [true] h))

theorem canonical_equiv_iff {m₀ m₁: _Memory}: m₀.canonical = m₁.canonical ↔ m₀ ≈ m₁ :=
⟨ flip Setoid.trans canonical_equiv ∘ canonical_equiv' (Setoid.refl _),
  canonical_of_equiv ⟩


theorem canonical_iff_equiv {m₀ m₁: _Memory}: (m₀.canonical = m₁.canonical) = (m₀ ≈ m₁) := eq_iff_iff.mpr canonical_equiv_iff

instance (m₀ m₁: _Memory): Decidable (m₀ ≈ m₁) := canonical_iff_equiv ▸ inferInstance

end _Memory

def Memory: Type _ := Quotient _Memory.setoid

namespace Memory

instance: Zero Memory where
  zero := ⟦.leaf⟧

instance: One Memory where
  one := ⟦.node true .leaf .leaf⟧

instance: NeZero (1:Memory) where
  out h := Bool.ff_ne_tt.symm (Quotient.exact h [])

def out: Memory → _Memory := Quotient.lift _Memory.canonical @_Memory.canonical_of_equiv
theorem out_eq (m: Memory): ⟦m.out⟧ = m :=
  (Quotient.exists_rep m).elim λ _ h ↦
    ((congrArg (Quotient.mk' ∘ Memory.out) h.symm).trans
    (Quotient.sound _Memory.canonical_equiv)).trans
    h

def getv (m: Memory): Bool := m.out.getv
def getm (m: Memory) (b: Bool): Memory := ⟦m.out.getm b⟧
def setv (m: Memory) (b: Bool): Memory := ⟦m.out.setv b⟧
def setm (m: Memory) (b: Bool) (ma: Memory): Memory := ⟦m.out.setm b ma.out⟧

def getvp (m: Memory) (bs: List Bool): Bool :=  m.out.getvp bs
def setvp (m: Memory) (bs: List Bool) (b: Bool): Memory := ⟦m.out.setvp bs b⟧
def getmp (m: Memory) (bs: List Bool): Memory := ⟦m.out.getmp bs⟧
def setmp (m: Memory) (bs: List Bool) (ma: Memory): Memory := ⟦m.out.setmp bs ma.out⟧

theorem node_eq (m: Memory):
  ⟦.node
    m.getv
    (m.getm false).out
    (m.getm true).out⟧ = m :=
  flip Eq.trans (out_eq _) (Quotient.sound λ
  | [] => rfl
  | false::_ => _Memory.canonical_equiv _
  | true::_ => _Memory.canonical_equiv _)

@[simp] theorem getv_sound (m: _Memory): getv ⟦m⟧ = m.getv := _Memory.canonical_getv
@[simp] theorem getm_sound (m: _Memory) (b: Bool): getm ⟦m⟧ b = m.getm b := _Memory.canonical_getm

@[simp] theorem getv_zero: (0:Memory).getv = false := rfl
@[simp] theorem getv_one: (1:Memory).getv = true := rfl
@[simp] theorem getm_zero (b: Bool): (0:Memory).getm b = 0 := rfl
@[simp] theorem getm_one: (b: Bool) → (1:Memory).getm b = 0
| false => rfl
| true => rfl

-- @[simp] theorem getm_setm {m ma: Memory}: {b: Bool} → (m.setm b ma).getm b = ma
-- | false => by
--   apply sound'
--   intro bs
--   match bs with
--   | [] =>
--     rw [← node_eq m, ← node_eq ma]


--   | false::_ => sorry
--   | true::_ => sorry

-- | true => sorry


-- theorem setv_inj_iff {m₀ m₁: Memory} {v₀ v₁: Bool}:
--     (m₀.setv v₀ = m₁.setv v₁) ↔ (v₀ = v₁ ∧ m₀.getm false = m₁.getm false ∧ m₀.getm true = m₁.getm true) :=
-- ⟨ λ h ↦ ⟨
--     Quotient.exact h [],
--     Quotient.sound (_Memory.getvp_congr' [false] (Quotient.exact h) rfl rfl),
--     Quotient.sound (_Memory.getvp_congr' [true] (Quotient.exact h) rfl rfl) ⟩,
--   λ h ↦ Quotient.sound λ
--     | [] => h.left
--     | false::_ => Quotient.exact h.right.left _
--     | true::_ => Quotient.exact h.right.right _ ⟩

-- @[simp] theorem setv_inj_eq {m₀ m₁: Memory} {v₀ v₁: Bool}:
--     (m₀.setv v₀ = m₁.setv v₁) = (v₀ = v₁ ∧ m₀.getm false = m₁.getm false ∧ m₀.getm true = m₁.getm true) :=
-- eq_iff_iff.mpr setv_inj_iff

-- theorem setm_inj_iff {m₀ ma₀ m₁ ma₁: Memory}: (b: Bool) →
--   m₀.setm b ma₀ = m₁.setm b ma₁ ↔ m₀.getv = m₁.getv ∧ ma₀ = ma₁ ∧ m₀.getm (!b) = m₁.getm !b := by
--   intro b
--   apply Iff.intro
--   intro h
--   apply And.intro
--   exact Quotient.exact h []


end Memory


inductive Source
| nil
| imm (hd: Bool) (tl: Source)
| idx (hd tl: Source)

def Source.get: Source → Memory → List Bool
| nil, _ => []
| imm hd tl, m => hd::(tl.get m)
| idx hd tl, m => m.getvp (hd.get m)::tl.get m

def Source.convert (f: Memory → List Bool → β) (m: Memory) (s: Source): β := f m (s.get m)

def Memory.getvs: Memory → Source → Bool := Source.convert getvp
def Memory.setvs: Memory → Source → Bool → Memory := Source.convert setvp
def Memory.getms: Memory → Source → Memory := Source.convert getmp
def Memory.setms: Memory → Source → Memory → Memory := Source.convert setmp

end HMem
