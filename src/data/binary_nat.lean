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

theorem intro_height {n m: node} {h: ℕ} (hw: well_formed h (n.intro m)): n.height = m.height :=
begin
  cases hw with h w,
  assumption
end

theorem elim_intro {n m: node} {h: ℕ} (w: well_formed (h + 1) (n.intro m)): well_formed h n ∧ well_formed h m :=
begin
  cases w,
  refine ⟨ by assumption, _ ⟩,
  rw [w_hp],
  assumption,
end

theorem elim_intro' {n m: node} (w: well_formed (n.intro m).height (n.intro m)): well_formed n.height n ∧ well_formed m.height m :=
begin
  rw [← intro_height w],
  exact elim_intro w,
end

theorem eq_height {n: node} {h₀ h₁: ℕ} (h: h₀ = h₁): well_formed h₀ n → well_formed h₁ n :=
by rw [h]; exact id

theorem eq_height' {n: node} {h₀ h₁: ℕ} (h: h₁ = h₀): well_formed h₀ n → well_formed h₁ n :=
by rw [h]; exact id

end well_formed

end binary_nat

def binary_nat := { n: binary_nat.node // binary_nat.well_formed n.height n }

namespace binary_nat

def height (x: binary_nat): ℕ := x.val.height

@[pattern]
def bit (b: bool): binary_nat := ⟨ node.bit b, well_formed.wf_bit b⟩

@[pattern]
def intro: Π (high low: binary_nat), high.height = low.height → binary_nat
| ⟨ high_val, high_proof⟩ ⟨ low_val, low_proof ⟩ h := ⟨ node.intro high_val low_val, well_formed.wf_intro high_proof low_proof h ⟩

theorem height_intro (x y: binary_nat): ∀  (h: x.height = y.height), (x.intro y h).height = x.height + 1 :=
begin
  cases x,
  cases y,
  simp [intro, height, node.height],
end

theorem height_intro' (x y: binary_nat): ∀  (h: x.height = y.height), (x.intro y h).height = y.height + 1 :=
begin
  cases x,
  cases y,
  simp [intro, height, node.height],
end

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

universe u
@[elab_as_eliminator] def elim {C: binary_nat → Sort u}
  (bit: Π (b: bool), C (bit b))
  (intro: Π (high low: binary_nat) (h: high.height = low.height), C (intro high low h)):
  Π (x: binary_nat), C x
| ⟨ (node.bit b), _ ⟩ := bit b
| ⟨ (node.intro n m), pf ⟩ := intro
  ⟨ n, (well_formed.elim_intro' pf).left ⟩
  ⟨ m, (well_formed.elim_intro' pf).right ⟩
  (well_formed.intro_height pf)

@[elab_as_eliminator]
def rec_on {C: binary_nat → Sort u}:
  Π (x: binary_nat)
  (handle_bit: Π (b: bool), C (bit b))
  (handle_intro: Π (high low: binary_nat) (h: high.height = low.height) (ih_high: C high) (ih_low: C low), C (intro high low h)),
  C x := λ x hb hi,
begin
  cases x,
  induction x_val,
  { apply hb },
  refine hi ⟨ x_val_u, _ ⟩ ⟨ x_val_l, _⟩ _ _ _,
  exact (well_formed.elim_intro' x_property).left,
  exact (well_formed.elim_intro' x_property).right,
  exact (well_formed.intro_height x_property),
  apply x_val_ih_u,
  apply x_val_ih_l,
end

@[elab_as_eliminator]
def rec {C: binary_nat → Sort u}
  (handle_bit: Π (b: bool), C (bit b))
  (handle_intro: Π (high low: binary_nat) (h: high.height = low.height) (ih_high: C high) (ih_low: C low), C (intro high low h)):
  Π (x: binary_nat), C x := λ x, rec_on x handle_bit handle_intro

def simp_rec {α: Type*}
  (handle_bit: Π (b: bool), α)
  (handle_intro: Π (high low: binary_nat) (ih_high ih_low: α), α):
  Π (x: binary_nat), α := λ x, rec_on x handle_bit (λ high low _ ih_high ih_low, handle_intro high low ih_high ih_low)

def zero: ℕ → binary_nat
| 0 := bit ff
| (n+1) := intro (zero n) (zero n) rfl

theorem zero_height (n: ℕ): (zero n).height = n :=
begin
  induction n,
  refl,
  rw [nat.succ_eq_add_one, ← n_ih],
  unfold zero,
  conv_lhs {
    congr,
    congr,
    rw n_ih,
    skip,
    rw n_ih,
  },
  apply height_intro,
end

def zero_extend (x: binary_nat): ℕ → binary_nat
| 0 := x
| (n+1) := intro (zero (zero_extend n).height) (zero_extend n) (by rw [zero_height])

theorem zero_extend_height (x: binary_nat) (n: ℕ): (zero_extend x n).height = x.height + n :=
begin
  induction n,
  refl,
  rw [nat.succ_eq_add_one, ← add_assoc, ← n_ih],
  unfold zero_extend,
  conv_lhs {
    congr,
    congr,
    rw n_ih,
    skip },
  apply height_intro',
end

def intro' (x y: binary_nat): binary_nat :=
  intro (zero_extend x (y.height - x.height)) (zero_extend y (x.height - y.height))
begin
  rw [zero_extend_height, zero_extend_height],
  cases @nat.le_total x.height y.height;
  rw [nat.add_sub_of_le h, nat.sub_eq_zero_of_le h, add_zero],
end

def is_zero: binary_nat → Prop := simp_rec
  (λ b, b = ff)
  (λ _ _ high_ih low_ih, high_ih ∧ low_ih)

instance is_zero.decidable (x: binary_nat): decidable (is_zero x) :=
begin
  induction x using data.binary_nat.rec_on,
  unfold is_zero,
  unfold bit,
  unfold simp_rec,
  unfold rec_on,
  apply_instance,
  cases x_high,
  cases x_low,
  apply @and.decidable _ _ x_ih_high x_ih_low,
end

def minimize: binary_nat → binary_nat := simp_rec
  (λ b, bit b)
  (λ high low high_ih low_ih,
    ite (is_zero high) low_ih (intro' high low))

def to_nat (x: binary_nat): binary_nat → ℕ := simp_rec (λ b, ite b 1 0) (λ high _ high_ih low_ih, 2 ^ 2 ^ high.height * high_ih + low_ih)

def inc_helper: binary_nat → (bool × binary_nat) := simp_rec
  (λ b: bool, ite b (tt, bit ff) (ff, bit tt))
  (λ high _ (high_ih low_ih: (bool × binary_nat)), ite low_ih.fst
    (high_ih.fst, (intro' high_ih.snd low_ih.snd))
    (ff, (intro' high low_ih.snd)))

def inc (x: binary_nat): binary_nat := minimize (intro' (bit (inc_helper x).fst) (inc_helper x).snd)

def of_nat (n: ℕ) := inc^[n] (zero 0)


end binary_nat
end data