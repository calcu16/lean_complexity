
import set_theory.cardinal.basic
import set_theory.cardinal.finite
import set_theory.cardinal.ordinal

universe u

namespace cardinal
lemma eq_one_iff_exists_unique {α : Type*}:
  cardinal.mk α = 1 ↔ ∃! (a: α), true :=
begin
  rw [eq_one_iff_unique],
  exact ⟨ 
      λ h, h.right.elim (λ a, ⟨a, trivial, λ _ _, @subsingleton.elim _ h.left _ _ ⟩) ,
      λ h, exists_unique.elim h (λ a _ ha, and.intro
        (subsingleton.intro (λ x y, trans (ha x trivial) (ha y trivial).symm))
        (nonempty.intro a)) ⟩,
end

theorem lt_aleph_0' {c : cardinal} (hc: c < aleph_0): ∃ n : ℕ, (n: cardinal) = c :=
  exists.elim (cardinal.lt_aleph_0.mp hc) (λ n hn, ⟨n, hn.symm⟩)

lemma le_mk_diff_add_mk_of_lt_aleph_0 {α: Type*} {c: cardinal} {s t: set α} (ht: cardinal.mk t < cardinal.aleph_0): c + cardinal.mk t ≤ cardinal.mk s → c ≤ cardinal.mk (s \ t : set α) :=
λ h, (cardinal.add_le_add_iff_of_lt_aleph_0 ht).mp (trans h (le_mk_diff_add_mk _ _))

lemma to_nat_inj {a b: cardinal} (ha: a < aleph_0) (hb: b < aleph_0) (h: a.to_nat = b.to_nat):
   a = b := le_antisymm
      ((cardinal.to_nat_le_iff_le_of_lt_aleph_0 ha hb).mp (le_of_eq h))
      ((cardinal.to_nat_le_iff_le_of_lt_aleph_0 hb ha).mp (ge_of_eq h))

lemma to_nat_inj_iff {a b: cardinal} (ha: a < aleph_0) (hb: b < aleph_0):
  a.to_nat = b.to_nat ↔ a = b :=
    ⟨ λ h, to_nat_inj ha hb h, congr_arg _ ⟩

lemma nat_cast_add (n m: ℕ): ((n + m:ℕ): cardinal) = n + m :=
  to_nat_inj (nat_lt_aleph_0 _) (add_lt_aleph_0 (nat_lt_aleph_0 _) (nat_lt_aleph_0 _)) (by simp)

theorem to_nat_even_iff (c: cardinal): even c ↔ even c.to_nat :=
begin
  split;
  intro h;
  cases h with x h,
  { rw [h],
    use to_nat x,
    rw [← two_mul, ← two_mul, to_nat_mul, ← nat.cast_two, to_nat_cast] },
  cases lt_or_ge c aleph_0 with hfin hinf,
  { cases cardinal.lt_aleph_0' hfin with n hn,
    induction hn,
    rw [to_nat_cast] at h,
    exact ⟨ x, by rw [h, nat_cast_add] ⟩ },
  { exact ⟨c, (add_eq_left hinf (le_refl _)).symm⟩ },
end

theorem nat_mul_lt_aleph_0 (c: cardinal) {n: ℕ}: c < aleph_0 → (n:cardinal)*c < aleph_0 :=
begin
  simp only [lt_aleph_0, forall_exists_index],
  exact λ m hm, ⟨n * m, hm.symm ▸ (nat.cast_mul _ _).symm⟩
end


theorem nat_mul_ge_aleph_0 (c: cardinal) {n: ℕ}: aleph_0 ≤ c → n ≠ 0 → (n:cardinal)*c = c :=
begin
  intros hc hn,
  rwa [mul_eq_max_of_aleph_0_le_right _ hc, max_eq_right_iff.mpr _],
  exact trans (le_of_lt (nat_lt_aleph_0 _)) hc,
  rwa nat.cast_ne_zero,
end

theorem nat_cast_left_mul_le_mul (c d: cardinal) {n: ℕ} (hn: 0 < n): (n:cardinal) * c ≤ n * d → c ≤ d :=
begin
  by_cases hc: c < aleph_0;
  by_cases hd: d < aleph_0,
  { cases lt_aleph_0' hc with nc hc,
    cases lt_aleph_0' hd with nd hd,
    induction hc,
    induction hd,
    simpa only [← nat.cast_mul, nat.cast_le, mul_le_mul_left hn] using id },
  { exact λ _,  trans (le_of_lt hc) (le_of_not_gt hd) },
  { intro h,
    exfalso,
    apply not_lt_of_ge h,
    apply lt_of_lt_of_le (nat_mul_lt_aleph_0 _ hd),
    rw [nat_mul_ge_aleph_0],
    repeat { exact le_of_not_gt hc },
    apply ne_of_gt hn },
  { rw [nat_mul_ge_aleph_0, nat_mul_ge_aleph_0],
    exact id,
    any_goals { exact ne_of_gt hn },
    { exact le_of_not_gt hd },
    { exact le_of_not_gt hc },
  },
end
end cardinal


lemma set.cardinal_embedding {α: Type u} {s: set α} {c: cardinal.{u}}:
  c ≤ cardinal.mk s → ∃ t: set α, cardinal.mk t = c ∧ t ⊆ s :=
begin
  intro hlt,
  rw [← cardinal.mk_out c, cardinal.le_def] at hlt,
  cases hlt,
  use { v | ∃ (hv : v ∈ s) c, hlt.to_fun c = ⟨v, hv⟩ },
  refine ⟨_, λ hp, by simpa using λ hp _ _, hp ⟩,
  conv_rhs { rw [← cardinal.mk_out c] },
  apply eq.symm,
  rw [cardinal.eq],
  fconstructor,
  refine equiv.of_bijective _ ⟨_, _⟩,
  { exact (λ x, ⟨ (hlt.to_fun x).val, by simp ⟩) },
  { intros c₁ c₂, simp [subtype.coe_inj] },
  intros ha,
  rcases ha with ⟨a, ha, c', hc⟩,
  use c',
  revert hc,
  simpa using congr_arg coe,
end

lemma set.cardinal_union_ge {α: Type*} (s t: set α):
  cardinal.mk s ≤ cardinal.mk (s ∪ t: set α) :=
 ⟨ ⟨  λ a, ⟨ a.val, or.inl a.property ⟩, λ a b, by simp [subtype.coe_inj] ⟩ ⟩

lemma set.cardinal_union_of_aleph_0_le {α: Type*} (s t: set α):
  cardinal.mk t ≤ cardinal.mk s → cardinal.aleph_0 ≤ cardinal.mk s → cardinal.mk (s ∪ t: set α) = cardinal.mk s :=
  λ h₁ h₂, le_antisymm
    (trans (cardinal.mk_union_le _ _) (cardinal.add_le_of_le h₂ (le_refl _) h₁))
    (cardinal.mk_le_mk_of_subset (set.subset_union_left _ _))