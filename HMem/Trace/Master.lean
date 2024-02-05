import HMem.Trace.Cost
import Complexity.Asymptotic

theorem blah {a x: ℕ}: (x + 1) ^ a + x ^ (a + 1)  ≤ (x + 1) ^ (a + 1) + x ^ a := by
  ring_nf
  apply add_le_add_right
  apply le_add_right
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  apply Nat.le_add_left

theorem blah2 {a x: ℕ}: (x + 1) ^ a - x ^ a  ≤ (x + 1) ^ (a + 1) - x ^ (a + 1) := by
  apply Nat.sub_le_of_le_add
  rw [← Nat.sub_add_comm]
  apply Nat.le_sub_of_add_le
  apply blah
  apply Nat.pow_le_pow_left
  apply Nat.le_add_right

theorem blah3 {a x: ℕ}: {b: ℕ} → (x + 1) ^ a - x ^ a  ≤ (x + 1) ^ (a + b) - x ^ (a + b)
| 0 => le_refl _
| _+1 => le_trans blah3 blah2

theorem blah4 {a b: ℕ}: {x: ℕ} → x ^ (a + b) - x ^ a  ≤ (x + 1) ^ (a + b) - (x + 1) ^ a
| 0 => by cases a <;> cases b <;> simp
| x+1 => by
  apply Nat.le_sub_of_add_le
  rw [← Nat.sub_add_comm, add_comm, Nat.sub_add_comm]
  apply Nat.add_le_of_le_sub _ blah3
  apply Nat.pow_le_pow_left (Nat.le_succ _)
  apply Nat.pow_le_pow_left (Nat.le_succ _)
  apply Nat.pow_le_pow_right (Nat.zero_lt_succ _)
  apply Nat.le_add_right

theorem blah5 {a b x: ℕ}: {y: ℕ} → x ^ (a + b) - x ^ a  ≤ (x + y) ^ (a + b) - (x + y) ^ a
| 0 => by simp
| _+1 => le_trans blah5 blah4

theorem blah6 {a b y: ℕ}: {x: ℕ} → (x + y) ^ a - x ^ a ≤ (x + y) ^ (a + b) - x ^ (a + b)
| 0 => by
  cases a <;> cases b <;> cases y <;>
  simp [Nat.pow_add]
  exact le_trans (Nat.pow_le_pow_right (Nat.zero_lt_succ 0) (Nat.succ_le_succ (Nat.zero_le _))) (Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.zero_le _)) _)
| x+1 => by
  apply Nat.le_sub_of_add_le
  rw [← Nat.sub_add_comm, add_comm (_ ^ _), Nat.sub_add_comm]
  apply Nat.add_le_of_le_sub _ blah5
  apply Nat.pow_le_pow_right
  apply Nat.lt_add_right _ (Nat.zero_lt_succ _)
  apply Nat.le_add_right
  apply Nat.pow_le_pow_right
  apply Nat.zero_lt_succ _
  apply Nat.le_add_right
  apply Nat.pow_le_pow_left
  apply Nat.le_add_right

theorem blah7 {a b x y: ℕ} (hab: a ≤ b) (hxy: x ≤ y): y ^ a - x ^ a ≤ y ^ b - x ^ b := by
  apply (Nat.exists_eq_add_of_le hab).elim
  apply (Nat.exists_eq_add_of_le hxy).elim
  intro _ hxy _ hab
  rw [hxy, hab]
  exact blah6

def Nat.size_ale_log: Nat.size ∈ O(Nat.log 2) where
  ale := λ _ ↦ le_of_le_of_eq Nat.size_le_succ_log (congrArg₂ _ (one_mul _).symm rfl)

def Nat.pow_size_ale_self: Nat.pow 2 ∘ Nat.size ∘ cf ∈ O(cf) where
  m := 2
  k := 1
  ale := by
    intro n
    dsimp [Complexity.CostFunction.add_def, Complexity.CostFunction.mul_def]
    cases cf n
    exact le_refl _
    rw [Nat.size_succ_eq_succ_log_succ, Nat.pow_succ']
    apply le_trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_log_le_self _ Nat.noConfusion
    apply Nat.le_add_right

def Nat.ale_pow_size: cf ∈ O(Nat.pow 2 ∘ Nat.size ∘ cf) := by
  apply Complexity.ALE.of_le
  intro n
  dsimp
  cases cf n
  apply zero_le
  simp [Nat.size_succ_eq_succ_log_succ]
  apply Nat.succ_le_of_lt
  apply lt_of_le_of_lt _
  apply Nat.lt_pow_succ_log_self
  exact one_lt_two
  apply Nat.le_succ

def Nat.sub_add_le {k m n: ℕ} (hk: m ≤ k) (hn: n ≤ m):
    k - m + n ≤ k :=
  (Nat.exists_eq_add_of_le hk).elim λ _ hx ↦
    hx ▸
    Nat.add_sub_cancel_left _ _ ▸
    add_comm _ n ▸
    add_le_add_right hn _

namespace HMem.Program
variable {α: Type _} [Complexity.Coding α Memory] {β: Type _} [Complexity.Encoding β Memory] {f: α → β} {tp: TracedProgram}

def nonRecursiveComplexity {p: Program} [Trace.HasCostedProgram p] {h: sound p f (λ _ ↦ 0)}
    {cf: Complexity.CostFunction α ℕ} (hs: p.subroutineTimeComplexity h ∈ O(cf)):
    p.timeCost' h ∈ O(cf) := Complexity.ALE.of_le_of_ale
    (splitTimeCost h)
    ((Complexity.ALE.add_ale (Complexity.ALE.add_ale (Complexity.ALE.trans
      (subroutineTimeComplexity_elem _)
      hs)
      (Complexity.ALE.of_le_of_ale (le_of_eq (funext λ _ ↦ (Trace.CostedProgram.recurseTimeCost_leaf (costed_sound h) _ rfl))) (Complexity.ALE.const_ale 0 _)))
      (Complexity.ALE.trans (localTimeCost_const h) (Complexity.ALE.const_ale _ _))))


def maxRecurseCost {p: Program} [Trace.HasCostedProgram p] {h: sound p f sz}
    {csi cr: Complexity.CostFunction α ℕ}
    (hsi: p.subroutineTimeCost h + p.localTimeCost h ≤ csi)
    (hz: ∀ a, csi a ≤ cr a)
    (hi: ∀ {a b}, sz a < sz b →  p.maxRecurse * (cr a) + csi b ≤ cr b)
    (a: α):
    p.timeCost' h a ≤ cr a :=
  le_trans (le_trans (le_of_le_of_eq
    (p.splitTimeCost _ _)
    (Nat.add_right_comm _ _ _)) (add_le_add_right (hsi _) _))
    (match hp:p.maxRecurse with
    | 0 => le_of_eq_of_le (congrArg _ (congrFun (p.recurseTimeCost_maxRecurse_zero _ hp) _)) (hz _)
    | _+1 =>
      haveI: {P: Prop} → Decidable P := Classical.dec _
      have hpos: 0 < p.maxRecurse := lt_of_lt_of_eq (Nat.zero_lt_succ _) hp.symm
      have hmax: ∀ a, ∃ m, ∀ b, sz b < sz a → cr b ≤ m :=
        λ _ ↦ ⟨ _, λ _ hb ↦ le_trans (le_add_left (le_mul_of_one_le_left' (Nat.succ_le_of_lt hpos))) (le_of_eq_of_le (add_comm _ _) (hi hb)) ⟩
      let boundOf: α → ℕ := λ a ↦ Nat.find (hmax a)
      have boundOf_le: ∀ a m, (∀ b, sz b < sz a → cr b ≤ m) → boundOf a ≤ m := λ _ _ hle ↦ Nat.find_le hle
      have le_boundOf: ∀ a b, sz b < sz a → cr b ≤ boundOf a :=
        λ _ ↦ Nat.find_spec (hmax _)
      have boundOf_exists_le: ∀ a, (∃ b, sz b < sz a) → ∃ b, sz b < sz a ∧ boundOf a ≤ cr b :=
        λ a hlt ↦
        match hb: boundOf a with
        | 0 => hlt.imp λ _ ha ↦ ⟨ha, zero_le _⟩
        | m+1 => not_forall_not.mp λ hx ↦ Nat.not_succ_le_self _
          (le_of_eq_of_le hb.symm (boundOf_le a m  λ _ ha ↦
            le_of_not_lt (not_and.mp (hx _) ha ∘ Nat.succ_le_of_lt)))
      have boundOf_exists_eq: ∀ a, (∃ b, sz b < sz a) → ∃ b, sz b < sz a ∧ boundOf a = cr b :=
        λ a hlt ↦
          (boundOf_exists_le a hlt).imp λ
          | a, ⟨ha, hb⟩ => ⟨ ha, le_antisymm hb (le_boundOf _ _ ha) ⟩
      let boundOf': {a: α} → (∃ b, sz b < sz a) → α :=
        λ hlt ↦ Classical.choose (boundOf_exists_eq _ hlt)
      have boundOf'_sz: ∀ {a: α} (hlt: ∃ b, sz b < sz a), sz (boundOf' hlt) < sz a :=
          λ hlt ↦ (Classical.choose_spec (boundOf_exists_eq _ hlt)).left
      have boundOf'_cr: ∀ {a b: α} (h: sz b < sz a), cr b ≤ cr (boundOf' ⟨_, h⟩) := λ hlt ↦
        le_of_le_of_eq (le_boundOf _ _ hlt) (Classical.choose_spec (boundOf_exists_eq _ ⟨_, hlt⟩)).right
      by
      apply (em (∃ arg, sz arg < sz a)).elim _
      exact λ ha ↦ le_of_eq_of_le (congrArg _ (Trace.CostedProgram.recurseTimeCost_leaf' (costed_sound h) _ (λ _ ↦ le_of_not_lt (forall_not_of_not_exists ha _)))) (hz _)
      intro ha
      apply flip le_trans (le_of_eq_of_le (Nat.add_comm _ _) (hi (boundOf'_sz ha)))
      apply add_le_add_left
      apply le_trans
      apply Trace.CostedProgram.recurseTimeCostBound
      intro arg harg
      simp only [p.costedMatches']
      apply le_trans (maxRecurseCost hsi hz hi _)
      rotate_right
      apply Nat.mul_le_mul_right _ (p.costedMatches.symm ▸ le_refl _)
      apply boundOf'_cr harg)
termination_by _ _ _ _ a => sz a

theorem simpleLoopCost {p: Program} [Trace.HasCostedProgram p] {h: sound p f sz}
    {x: ℕ}
    (hsi: p.subroutineTimeCost h + p.localTimeCost h ≤ λ _ ↦ x)
    (hr: p.maxRecurse = 1)
    (n: ℕ):
  ∀ a, sz a = n → p.timeCost' h a ≤ x * n + x := by
  induction n using Nat.case_strong_induction_on with
  | hi n₀ ih =>
    intro a hsz
    apply le_trans (splitTimeCost _ _)
    apply le_of_eq_of_le
    apply Eq.trans
    apply Nat.add_right_comm _ _ _
    apply Nat.add_comm
    apply add_le_add _
    apply hsi
    apply le_trans
    apply Trace.CostedProgram.recurseTimeCostBound (x := x * n₀ + x)
    intro arg harg
    apply le_trans _ (add_le_add_right (mul_le_mul (le_refl _ ) _ (zero_le _) (zero_le _)) _)
    use sz arg
    specialize ih (sz arg) _
    apply Nat.succ_le_succ_iff.mp
    apply le_of_le_of_eq _ hsz
    apply Nat.succ_le_of_lt harg
    specialize ih _ rfl
    simp only [p.costedMatches']
    apply ih
    apply Nat.succ_le_succ_iff.mp
    apply le_of_le_of_eq _ hsz
    apply Nat.succ_le_of_lt harg
    simp only [p.costedMatches, hr, one_mul, Nat.mul_succ]
    apply le_refl
  | hz =>
    intro a hsz
    apply le_trans (splitTimeCost _ _)
    apply le_of_eq_of_le
    apply Eq.trans
    apply Nat.add_right_comm _ _ _
    apply Nat.add_comm
    apply add_le_add _
    apply hsi
    apply le_of_eq_of_le _ (zero_le _)
    apply Trace.CostedProgram.recurseTimeCost_leaf (costed_sound h) _ hsz

def simpleLoopComplexity {p: Program} [Trace.HasCostedProgram p] {h: sound p f sz}
    (hs: p.subroutineTimeComplexity h ∈ O(1))
    (hr: p.maxRecurse = 1):
  p.timeCost' h ∈ O(sz) :=
    have hsi: subroutineTimeCost h + localTimeCost h ∈ O(0) :=
      Complexity.ALE.add_ale
        (((subroutineTimeComplexity_elem _).trans hs).trans (Complexity.ALE.const_ale _ 0))
        ((p.localTimeCost_const h).trans (Complexity.ALE.const_ale _ 0))
    ⟨ _, _, λ _ ↦ simpleLoopCost (le_trans hsi.le_bound (le_of_eq ((congrArg₂ Add.add (mul_zero _) rfl).trans (zero_add _)))) hr _ _ rfl ⟩

def simpleLoopComplexity' {p: Program} [Trace.HasCostedProgram p] {h: sound p f sz}
    (hs: p.selfContained)
    (hr: p.maxRecurse = 1):
  p.timeCost' h ∈ O(sz) :=
    have hsi: subroutineTimeCost h + localTimeCost h ∈ O(0) :=
      Complexity.ALE.add_ale
        ((p.subroutineTimeCost_selfContained h hs).trans (Complexity.ALE.const_ale _ 0))
        ((p.localTimeCost_const h).trans (Complexity.ALE.const_ale _ 0))
    ⟨ _, _, λ _ ↦ simpleLoopCost (le_trans hsi.le_bound (le_of_eq ((congrArg₂ Add.add (mul_zero _) rfl).trans (zero_add _)))) hr _ _ rfl ⟩

def sizeLoopComplexity {p: Program} [Trace.HasCostedProgram p]
    (sz: Complexity.CostFunction α ℕ)
    {h: sound p f sz}
    (hs: p.subroutineTimeComplexity h ∈ O(Nat.pow 2 ∘ sz))
    (hr: p.maxRecurse = 1):
  p.timeCost' h ∈ O(Nat.pow 2 ∘ sz) :=
    have hsi: subroutineTimeCost h + localTimeCost h ∈ O(Nat.pow 2 ∘ sz) :=
      ((subroutineTimeComplexity_elem _).trans hs).add_ale
        ((p.localTimeCost_const h).trans (Complexity.ALE.const_ale _ _))
      by
    apply Complexity.ALE.mk (2 * hsi.m + hsi.k) hsi.k
    intro a
    apply maxRecurseCost (h := h) hsi.le_bound
    intro a
    apply (λ a ↦ add_le_add_right (Nat.mul_le_mul_right _ (le_add_right (Nat.le_mul_of_pos_left zero_lt_two))))
    intro a b hab
    simp only [Complexity.ALE.bound, Complexity.CostFunction.add_def, Function.comp,
      Complexity.CostFunction.mul_def, two_mul, left_distrib, right_distrib,
      ← add_assoc, ← mul_assoc, hr, one_mul,
      add_le_add_iff_right]
    rw [add_right_comm _ (hsi.m * Nat.pow 2 (sz b)) (hsi.k * Nat.pow 2 (sz b)),
      add_le_add_iff_right]
    have hab₂ : 2 * Nat.pow 2 (sz a) ≤ Nat.pow 2 (sz b) :=
      le_of_eq_of_le
        ((Nat.mul_comm _ _).trans (Nat.pow_succ _ _).symm)
        (Nat.pow_le_pow_right zero_lt_two (Nat.succ_le_of_lt hab))
    apply le_trans _
    apply add_le_add
    apply Nat.mul_le_mul_left _ hab₂
    apply Nat.mul_le_mul_left _ hab₂
    simp only [two_mul, left_distrib, ← add_assoc]
    apply add_le_add_left
    apply Nat.le_mul_of_pos_right (Nat.pow_two_pos _)


def simpleDivideAndConquerComplexity {p: Program} [Trace.HasCostedProgram p]
    {sz: Complexity.CostFunction α ℕ}
    {h: sound p f sz}
    (hs: p.subroutineTimeComplexity h ∈ O(1)) -- can be extended to any power < p.maxRecurse
    (hr: 2 ≤ p.maxRecurse):
  p.timeCost' h ∈ O(Nat.pow p.maxRecurse ∘ sz) := by
  have hsi: subroutineTimeCost h + localTimeCost h ∈ O(0) :=
      Complexity.ALE.add_ale
        (((subroutineTimeComplexity_elem _).trans hs).trans (Complexity.ALE.const_ale _ 0))
        ((p.localTimeCost_const h).trans (Complexity.ALE.const_ale _ 0))
  apply Complexity.ALE.trans (y := λ n ↦ p.maxRecurse ^ (sz n + 1) - 1)
  apply Complexity.ALE.mk hsi.k 0
  intro a
  apply maxRecurseCost (h := h) hsi.le_bound _
  -- exact λ _ ↦ le_of_eq_of_le
  --   (((congrArg₂ Nat.add (Nat.mul_zero _) rfl).trans (Nat.zero_add _)).trans
  --   ((congrArg _ (Nat.pow_zero _)).trans (Nat.mul_one _)).symm)
  --   (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (lt_of_lt_of_le zero_lt_two hr) (zero_le _)))
  { intro a b h
    simp [flip, Function.comp, Complexity.CostFunction.add_def, Complexity.CostFunction.mul_def,
      left_distrib, right_distrib, ← add_assoc, ← mul_assoc, Complexity.ALE.bound, OfNat.ofNat, Zero.zero]
    rw [mul_comm _ hsi.k, mul_assoc, ← Nat.mul_succ]
    apply Nat.mul_le_mul_left
    apply Nat.le_sub_of_add_le
    apply le_trans _
    apply Nat.pow_le_pow_right (lt_of_lt_of_le zero_lt_two hr) (Nat.succ_le_succ (Nat.succ_le_of_lt h))
    simp [Nat.succ_eq_add_one, Nat.mul_sub_left_distrib]
    apply le_trans
    apply Nat.sub_add_le _ hr
    apply Nat.le_mul_of_pos_right
    apply Nat.lt_of_lt_of_le _
    apply Nat.pow_le_pow_right (lt_of_lt_of_le zero_lt_two hr) (zero_le _)
    apply Nat.lt_of_lt_of_eq zero_lt_one (Nat.pow_zero _).symm
    apply le_of_eq
    apply Eq.trans
    apply mul_comm
    apply Eq.symm
    apply Nat.pow_succ}
  intro a
  simp [Complexity.ALE.bound, Complexity.CostFunction.add_def, Complexity.CostFunction.mul_def, OfNat.ofNat, Zero.zero]
  apply Nat.le_mul_of_pos_right
  apply Nat.lt_of_succ_le
  apply Nat.le_sub_of_add_le
  apply le_trans _
  apply Nat.pow_le_pow_left hr
  apply Nat.pow_le_pow_right zero_lt_two (Nat.succ_le_succ (zero_le _))
  apply Complexity.ALE.trans
  apply Complexity.ALE.of_le
  intro
  apply Nat.sub_le
  apply Complexity.ALE.mk (maxRecurse p) 0
  intro
  apply le_of_eq
  apply Eq.trans
  apply Nat.pow_succ
  apply mul_comm

def simpleDivideAndConquerComplexity' {p: Program} [Trace.HasCostedProgram p]
    {sz: Complexity.CostFunction α ℕ}
    (h: sound p f sz)
    (hs: p.selfContained) -- can be extended to any power < p.maxRecurse
    (hr: 2 ≤ p.maxRecurse):
    p.timeCost' h ∈ O(Nat.pow p.maxRecurse ∘ sz) :=
  simpleDivideAndConquerComplexity
    ((Program.subroutineTimeComplexity_selfContained _ hs).trans
      (Complexity.ALE.const_ale _ _))
    hr

def divideAndConquerComplexityLeafHeavy {p: Program} [Trace.HasCostedProgram p]
    {sz: Complexity.CostFunction α ℕ}
    {h: sound p f sz}
    (hs: p.subroutineTimeComplexity h ∈ O(Nat.pow (p.maxRecurse - 1) ∘ sz))
    (hr: 3 ≤ p.maxRecurse):
    p.timeCost' h ∈ O(Nat.pow p.maxRecurse ∘ sz) := by
  have hsi: subroutineTimeCost h + localTimeCost h ∈ O(Nat.pow (p.maxRecurse - 1) ∘ sz) :=
      Complexity.ALE.add_ale ((subroutineTimeComplexity_elem _).trans hs) ((p.localTimeCost_const h).trans (Complexity.ALE.const_ale _ _))
  apply Complexity.ALE.trans (y := λ n ↦ p.maxRecurse ^ (sz n + 1) - (p.maxRecurse - 1) ^ (sz n + 1))
  apply Complexity.ALE.mk (hsi.m + hsi.k) 0
  apply maxRecurseCost (h := h) hsi.le_bound _
  intro a b hsz
  simp only [Complexity.CostFunction.add_def, Complexity.CostFunction.mul_def, add_zero, ← mul_assoc]
  apply le_trans
  apply add_le_add_right
  apply Nat.mul_le_mul_left
  apply blah7
  apply Nat.succ_le_of_lt
  apply hsz
  apply Nat.sub_le
  rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
  apply Nat.le_sub_of_add_le
  rw [Nat.add_assoc, ← Nat.sub_add_comm]
  apply Nat.sub_le_of_le_add
  apply add_le_add
  rw [Nat.pow_succ', Nat.mul_left_comm, Nat.mul_assoc]
  rw [Nat.pow_succ, ← mul_assoc, Nat.mul_sub_left_distrib, add_comm, mul_one, ← Nat.sub_add_comm]
  apply Nat.sub_le_of_le_add
  apply add_le_add
  rw [mul_right_comm, mul_comm (_ + _)]
  rw [right_distrib]
  apply add_le_add
  apply le_refl
  apply Nat.le_mul_of_pos_right
  apply Nat.pos_pow_of_pos
  apply Nat.lt_sub_of_add_lt
  apply lt_of_lt_of_le (Nat.succ_lt_succ (Nat.zero_lt_succ _)) hr
  apply Nat.le_mul_of_pos_right
  apply Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hr
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  apply Nat.sub_le
  intro a
  simp [Complexity.ALE.bound, Complexity.CostFunction.add_def, Complexity.CostFunction.mul_def, right_distrib]
  apply add_le_add
  rw [Nat.mul_sub_left_distrib]
  apply Nat.le_sub_of_add_le
  rw [← left_distrib]
  apply Nat.mul_le_mul_left
  rw [Nat.pow_succ', add_comm, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel, Nat.pow_succ']
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  apply Nat.sub_le
  apply le_trans (Nat.succ_le_succ (Nat.zero_le _)) hr
  apply Nat.le_mul_of_pos_right
  apply Nat.lt_sub_of_add_lt
  rw [zero_add]
  apply Nat.pow_lt_pow_left
  apply Nat.sub_lt
  apply lt_of_lt_of_le (Nat.zero_lt_succ _) hr
  apply zero_lt_one
  apply Nat.noConfusion
  apply Complexity.ALE.mk (maxRecurse p) 0
  intro
  apply le_trans
  apply Nat.sub_le
  apply le_of_eq
  apply Nat.pow_succ'



end HMem.Program
