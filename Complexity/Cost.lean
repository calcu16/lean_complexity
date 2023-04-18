import Complexity.StdComp
import Complexity.StdAdd

namespace Complexity

structure Costed (α : Type u) where
  of : Nat → (Nat × α)
  cost_inv : ∀ c₀ c₁ : Nat, (of c₀).fst + c₁ = (of c₁).fst + c₀
  value_inv : ∀ c₀ c₁ : Nat, (of c₀).snd = (of c₁).snd
  cost_inc : ∀ c₀ : Nat, c₀ ≤ (of c₀).fst

namespace Cost

@[simp]
def pure (a : α) : Costed α := {
  of := λ c: Nat => (c, a),
  cost_inv := by simp [Nat.add_comm]
  value_inv := by simp
  cost_inc := by simp
}

@[simp]
def succ (a : α) : Costed α := {
  of := λ c: Nat => (Nat.succ c, a)
  cost_inv := by simp [Nat.add_comm, Nat.add_succ]
  value_inv := by simp
  cost_inc := by simp [Std.le_succ_self]
}

@[simp]
def bind : Costed α → (α → Costed β) → Costed β :=
  λ ca cb => {
    of := λ c₀ : Nat =>
      let (c₁, a) := ca.of c₀
      (cb a).of c₁
    cost_inv := by
      intros c₀ c₁
      simp
      rw [Std.add_right_cancel_iff _ _ (ca.of c₀).fst,
          Nat.add_assoc,
          Nat.add_assoc,
          Nat.add_comm c₁,
          Nat.add_comm c₀,
          ca.cost_inv,
          ← Nat.add_assoc,
          ← Nat.add_assoc,
          ← Std.add_right_cancel_iff,
          (cb _).cost_inv,
          ← Std.add_right_cancel_iff,
          ca.value_inv _ c₁]
    value_inv := by
      intros c₀ c₁ 
      simp
      rw [ca.value_inv _ c₁, (cb _).value_inv]
    cost_inc := by
      intros c₀
      simp
      apply Nat.le_trans
      apply ca.cost_inc
      apply (cb _).cost_inc
  }
  
instance : Monad Costed where
  pure := pure
  bind := bind

@[simp]
def cross (ca: Costed α) (cb: Costed β) : Costed (α × β) :=
  do
    let a ← ca
    let b ← cb
    return (a, b)

instance : HasEquiv (Costed α) where Equiv := λ ca cb => ∀ c : Nat, (ca.of c).snd = (cb.of c).snd

@[simp]
theorem equiv (ca cb : Costed α) : ca ≈ cb ↔ ∀ c : Nat, (ca.of c).snd = (cb.of c).snd := by apply Iff.intro <;> (intro; assumption)
  
theorem equiv_refl (ca : Costed α) : ca ≈ ca := by simp[equiv]

theorem equiv_symm {ca cb : Costed α} : ca ≈ cb → cb ≈ ca := by
  simp[equiv]
  intros
  apply Eq.symm
  simp[*]

theorem equiv_trans {ca cb cc : Costed α} : ca ≈ cb → cb ≈ cc → ca ≈ cc := by
  simp [equiv]
  intros p q c
  rw [p c, q c]

theorem equivalence (α : Type u): Equivalence (λ ca cb : Costed α => ca ≈ cb) := .mk equiv_refl equiv_symm equiv_trans

@[simp]
theorem value_elim {ca : Costed α} {c : Nat} : (ca.of c).snd = (ca.of 0).snd := by rw [ca.value_inv]

@[simp]
theorem pure_elim {a : α} : (Costed.of (Pure.pure a) 0).snd = a := by simp[Pure.pure]

end Cost


end Complexity