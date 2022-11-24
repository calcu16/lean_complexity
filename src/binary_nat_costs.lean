import binary_nat

open costed_binary_nat

universe u
variables {α : Type u}

def cost_of (c: cost): costed α → ℕ := λ f, ((f c).fst.value - c.value)

def cost_zero (c: cost) (n: ℕ) := cost_of c (costed_zero n)

theorem cost_zero_exact (n : ℕ) : ∀ c : cost, cost_zero c n = n + 1 :=
begin
  induction n with n h,
  unfold cost_zero,
  unfold cost_of,
  unfold costed_zero,
  unfold costed_bit_zero,
  unfold cost_inc,
  simp,
  unfold cost_zero,
  unfold cost_of,
  unfold costed_zero,
  unfold cost_zero at h,
  unfold cost_of at h,
  intro c,
  specialize h c,
  








  
  










  




end
