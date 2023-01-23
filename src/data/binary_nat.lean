import tactic.basic
import tactic.linarith
import tactic.hint
import data.vector.basic

namespace data
namespace binary_nat

inductive node : Type
| bit (b: bool): node
| intro (u l: node): node

namespace node
def height: node → ℕ
| (bit _) := 0
| (intro u l) := (height u) + 1
end node

inductive well_formed: ℕ → node → Prop
| wf_bit (b: bool): well_formed 0 (node.bit b)
| wf_intro {n m: node} (wn: well_formed n.height n) (wm: well_formed m.height m) (hp: n.height = m.height): well_formed ((n.intro m).height) (n.intro m)

namespace well_formed

theorem intro_pos {n m: node} {h: ℕ} (w: well_formed h (n.intro m)): h ≠ 0 :=
begin
  cases w,
  exact nat.succ_ne_zero _
end

-- theorem elim_intro {n m: node} {h: ℕ} (w: well_formed (h + 1) (n.intro m)): well_formed h n ∧ well_formed h m :=
-- begin
--   cases w,
--   exact ⟨ by assumption, by assumption ⟩
-- end

-- theorem intro_height' {n m: node} (hw: is_well_formed (n.intro m)): n.height = m.height :=
-- begin
--   cases hw with h w,
--   cases w,
--   assumption
-- end

-- theorem elim_intro' {n m: node} (hw: is_well_formed (n.intro m)): is_well_formed n ∧ is_well_formed m :=
-- begin
--   cases hw with h w,
--   cases h,
--   { exfalso, exact intro_pos w rfl },
--   exact ⟨ ⟨h, (elim_intro w).left⟩, ⟨h, (elim_intro w).right⟩ ⟩,
-- end

-- theorem skolem {n: node}: is_well_formed n → well_formed n.height n :=
-- begin
--   induction n,
--   { exact λ _, wf_bit _ },
--   { intro p,
--     apply wf_intro (n_ih_u (elim_intro' p).left) _ (intro_height' p),
--     rw [intro_height' p],
--     apply n_ih_l (elim_intro' p).right },
-- end

-- theorem skolem_iff (n: node): is_well_formed n ↔ well_formed n.height n := ⟨ skolem,  λ p, ⟨ _, p ⟩ ⟩

theorem eq_height {n: node} {h₀ h₁: ℕ} (h: h₀ = h₁): well_formed h₀ n → well_formed h₁ n :=
by rw [h]; exact id

theorem eq_height' {n: node} {h₀ h₁: ℕ} (h: h₁ = h₀): well_formed h₀ n → well_formed h₁ n :=
by rw [h]; exact id

end well_formed

end binary_nat

def binary_nat := { n: binary_nat.node // binary_nat.well_formed n.height n }

namespace binary_nat

@[reducible]
def proof (x: binary_nat) := x.2

@[reducible]
def height (x: binary_nat): ℕ := x.val.height

@[pattern]
def bit (b: bool): binary_nat := ⟨ node.bit b, well_formed.wf_bit b⟩

@[pattern]
def intro: Π (x y: binary_nat), x.val.height = y.val.height → binary_nat
| ⟨ xval, xproof⟩ ⟨ yval, yproof ⟩ h := ⟨ node.intro xval yval, well_formed.wf_intro xproof yproof h ⟩

-- @[elab_as_eliminator] def elim {α} {C : Π {n}, vector α n → Sort u} (H : ∀l : list α, C ⟨l, rfl⟩)
--   {n : nat} : Π (v : vector α n), C v
-- | ⟨l, h⟩ := match n, h with ._, rfl := H l end

-- universe u
-- @[elab_as_eliminator] def elim {C: binary_nat → Sort u}
--   (bit: Π (b: bool), C (bit b))
--   (intro: Π (x y: binary_nat) (h: is_well_formed (x.val.intro y.val)), C (intro x y h)):
--   Π (x: binary_nat), C x
-- | ⟨ (node.bit b), _ ⟩ := bit b
-- | ⟨ (node.intro n m), pf ⟩ := intro
--   ⟨ n, (well_formed.elim_intro' pf).left ⟩
--   ⟨ m, (well_formed.elim_intro' pf).right ⟩
--   pf


@[simp] theorem sizeof_leaf (b: bool): (bit b).sizeof = 2 :=
begin
  unfold bit,
  unfold_wf,
end

@[simp] theorem sizeof_intro (x y: binary_nat) (h: x.val.height = y.val.height): (intro x y h).sizeof = 1 + x.sizeof + y.sizeof :=
begin
  cases x,
  cases y,
  unfold intro,
  unfold_wf,
end

def is_zero: binary_nat → Prop
| (bit b) := false
| (intro u l _) := is_zero u ∧ is_zero l



end binary_nat
end data