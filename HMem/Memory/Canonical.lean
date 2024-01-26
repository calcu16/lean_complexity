import Mathlib.Data.Tree
import Lib

/-!
This file defines a canonical representation of a Tree Bool where
leafs are considered to hold a false value.

Therefore (.node false .nil .nil) -> .nil, and this is handled recursively.
This allows us to define a tree-like memory that starts at all false.
-/

namespace HMem.Memory

def canonical: Tree Bool → Tree Bool
| .nil => .nil
| .node v lhs rhs =>
  match v, canonical lhs, canonical rhs with
  | false, .nil, .nil => .nil
  | v', lhs', rhs' => .node v' lhs' rhs'

@[simp] theorem canonical_nil_def: canonical .nil = .nil := rfl

theorem canonical_node_def:
  canonical (.node v lhs rhs) =
    match v, canonical lhs, canonical rhs with
    | false, .nil, .nil => .nil
    | v', lhs', rhs' => .node v' lhs' rhs' := rfl

theorem canonical_getOrElse: {t: Tree Bool} →
  (canonical t).getOrElse 1 false = t.getOrElse 1 false
| .nil => rfl
| .node v lhs rhs => canonical_node_def ▸
  match v, canonical lhs, canonical rhs with
  | false, .nil, .nil => rfl
  | false, .nil, .node _ _ _ => rfl
  | false, .node _ _ _, _ => rfl
  | true, _, _ => rfl

theorem canonical_left: {t: Tree Bool} →
  canonical t.left = (canonical t).left
| .nil => rfl
| .node v lhs rhs => canonical_node_def ▸
  match v, canonical lhs, canonical rhs with
  | false, .nil, .nil => rfl
  | false, .nil, .node _ _ _ => rfl
  | false, .node _ _ _, _ => rfl
  | true, _, _ => rfl

theorem canonical_right: {t: Tree Bool} →
  canonical t.right = (canonical t).right
| .nil => rfl
| .node v lhs rhs => canonical_node_def ▸
  match v, canonical lhs, canonical rhs with
  | false, .nil, .nil => rfl
  | false, .nil, .node _ _ _ => rfl
  | false, .node _ _ _, _ => rfl
  | true, _, _ => rfl

theorem canonical_nil: {t: Tree Bool} →
    t.getOrElse 1 false = false →
    canonical t.left = .nil →
    canonical t.right = .nil →
    canonical t = .nil
| .nil, _, _, _ => rfl
| .node _ lhs rhs, hv, hl, hr =>
    canonical_node_def ▸
    (Tree.getOrElse_node_one ▸ hv) ▸
    (hl: canonical lhs = .nil).symm ▸
    (hr: canonical rhs = .nil).symm ▸ rfl

theorem canonical_cases (t: Tree Bool):
  canonical t = .nil ∨
  canonical t = .node (t.getOrElse 1 false) (canonical t.left) (canonical t.right) :=
match h:canonical t with
| .nil => Or.inl rfl
| .node _ _ _ =>
  Or.inr (congr (congrArg₂ _
    ((congrArg (λ t ↦ Tree.getOrElse 1 t false) h).symm.trans canonical_getOrElse)
    (canonical_left.trans (congrArg _ h)).symm)
    (canonical_right.trans (congrArg _ h)).symm)

theorem canonical_node (h: canonical t ≠ .nil):
    canonical t = .node (t.getOrElse 1 false) (canonical t.left) (canonical t.right) :=
  (canonical_cases t).elim (flip absurd h) id


theorem canonical_congr: {t₀ t₁: Tree Bool} →
  t₀.getOrElse 1 false = t₁.getOrElse 1 false →
  canonical t₀.left = canonical t₁.left →
  canonical t₀.right = canonical t₁.right →
  canonical t₀ = canonical t₁
| .nil, .nil, _, _, _ => rfl
| .nil, .node _ _ _, hv, hl, hr => (canonical_nil hv.symm hl.symm hr.symm).symm
| .node v₀ lhs₀ rhs₀, t₁, hv, hl, hr =>
  match canonical_cases (.node v₀ lhs₀ rhs₀), canonical_cases t₁ with
  | Or.inl h₀, Or.inl h₁ => h₀ ▸ h₁ ▸ rfl
  | Or.inl h₀, Or.inr h₁ => by
    apply absurd (h₁.symm.trans (canonical_nil
        (hv.symm.trans (canonical_getOrElse.symm.trans (congrArg (λ t ↦ Tree.getOrElse 1 t false) h₀)))
        (hl.symm.trans (canonical_left.trans (congrArg _ h₀)))
        (hr.symm.trans (canonical_right.trans (congrArg _ h₀)))))
      Tree.noConfusion
  | Or.inr h₀, Or.inl h₁ =>
    absurd (h₀.symm.trans (canonical_nil
        (hv.trans (canonical_getOrElse.symm.trans (congrArg (λ t ↦ Tree.getOrElse 1 t false) h₁)))
        (hl.trans (canonical_left.trans (congrArg _ h₁)))
        (hr.trans (canonical_right.trans (congrArg _ h₁)))))
      Tree.noConfusion
  | Or.inr h₀, Or.inr h₁ => h₀ ▸ h₁ ▸ congr (congrArg₂ _ hv hl) hr

@[simp] theorem canonical_idempotent: {t: Tree Bool} → canonical (canonical t) = canonical t
| .nil => rfl
| .node _ _ _ => canonical_congr canonical_getOrElse
  ((congrArg _ canonical_left.symm).trans canonical_idempotent)
  ((congrArg _ canonical_right.symm).trans canonical_idempotent)

theorem canonical_le_numNodes: (t: Tree Bool) → (canonical t).numNodes ≤ t.numNodes
| .nil => Nat.zero_le _
| .node v lhs rhs =>
  match canonical_cases (.node v lhs rhs) with
  | Or.inl h => h ▸ Nat.zero_le _
  | Or.inr h => h ▸  Nat.succ_le_succ (Nat.add_le_add
    (canonical_le_numNodes lhs)
    (canonical_le_numNodes rhs))

end HMem.Memory
