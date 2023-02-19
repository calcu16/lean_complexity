import data.set.basic
import data.set.lattice
import order.antichain

lemma set_coe.exists_unique {α : Type*} (s: set α) (p: s → Prop):
  (∃! a : s, p a) ↔ ∃! a (h: a ∈ s), p ⟨a, h⟩ :=
by simp [set_coe.exists, exists_unique, and_assoc]

lemma set.sep_mem {α: Type*} (s: set α):
  {v : α | v ∈ s} = s := rfl

theorem set.disjoint_diff' {α: Type*} (a b : set α): disjoint (a \ b) b :=
begin
  apply disjoint.symm _,
  apply set.disjoint_diff,
end

theorem set.mem_image' {α β: Type*} (f : α → β) (s : set α) (y : β) :
  y ∈ f '' s ↔ ∃ x, f x = y ∧ x ∈ s := begin
  rw [set.mem_image f s y],
  conv_lhs { congr, funext, rw and_comm },
end

section

variables {α β : Type*} {r r₁ r₂ : α → α → Prop} {r' : β → β → Prop} {s t : set α} {a : α}

lemma is_antichain.not_mem (hs : is_antichain r s) {a b : α} (ha : a ∈ s) (hab: a ≠ b) (h : r a b) :
  b ∉ s := λ hb, hab (is_antichain.eq hs ha hb h)

end