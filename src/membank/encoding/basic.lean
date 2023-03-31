import tactic
import membank.basic
import membank.master
import complexity.basic
import complexity.core
import algebra.big_operators.fin

namespace membank
namespace encoding

variables {μ: Type*} [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]

def mpair (v: μ) (m₀ m₁: bank μ) := bank.mem v (λ n, if 0 = n then m₀ else if 1 = n then m₁ else bank.null)

def push_arg: bank μ → bank μ → bank μ := mpair 1

def runtime_model (μ: Type*) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]: complexity.model (program μ × bank μ) (bank μ) ℕ :=
 ⟨  λ p_a r c, stack.step^[c] (function.uncurry program.apply p_a) = (stack.result r),
    λ p_a a', (p_a.fst, mpair 1 p_a.snd a'),
    λ _ _ _ c₀ c₁ h₀ h₁,
      bank.equiv_refl' (stack.result.inj (or.elim (le_total c₀ c₁)
        (λ h, h₁ ▸ (stack.step_halt_le h₀ h).symm)
        (h₀ ▸ stack.step_halt_le h₁))),
    λ _ _ _ _, flip stack.step_halt_le ⟩

theorem application_def (p: program μ) (arg₀ arg₁: bank μ):
 complexity.model.application (runtime_model μ) (p, arg₀) arg₁ = (p, mpair 1 arg₀ arg₁) := rfl

theorem application_def' (p: program μ × bank μ) (arg: bank μ):
 complexity.model.application (runtime_model μ) p arg = (p.fst, mpair 1 p.snd arg) := rfl

theorem getv_mpair (v: μ) (m₀ m₁: bank μ): (mpair v m₀ m₁).getv = v := rfl

theorem getm_mpair₀ (v: μ) (m₀ m₁: bank μ): (mpair v m₀ m₁).getm 0 = m₀ :=
by simp [mpair, bank.getm]

theorem getm_mpair₁ (v: μ) (m₀ m₁: bank μ): (mpair v m₀ m₁).getm 1 = m₁ :=
by simp [mpair, bank.getm]

theorem ite_ite_self (p: Prop) [decidable p] {α: Sort*} (a b c: α): ite p (ite p a b) c = ite p a c :=
by split_ifs; refl

theorem ite_ite_self' (p: Prop) [decidable p] {α: Sort*} (a b c: α): ite p a (ite p b c) = ite p a c :=
by split_ifs; refl

theorem setv_mpair (v v': μ) (m₀ m₁: bank μ): (mpair v m₀ m₁).setv v' = (mpair v' m₀ m₁) := rfl

theorem setm_mpair₀ (v: μ) (m₀ m₁ m₀': bank μ): (mpair v m₀ m₁).setm 0 m₀' = (mpair v m₀' m₁) :=
by simp [mpair, bank.setm, @eq_comm μ 0, ite_ite_self']

theorem setm_mpair₁ (v: μ) (m₀ m₁ m₁': bank μ): (mpair v m₀ m₁).setm 1 m₁' = (mpair v m₀ m₁') :=
begin
  simp [mpair, bank.setm, @eq_comm μ 0, ite_ite_self'],
  ext1,
  split_ifs;
  try { refl },
  rw [h_1] at h,
  exact absurd h.symm zero_ne_one,
end

variables {α: Type} [complexity.has_encoding (runtime_model μ) α]
variables {β: Type} [complexity.has_encoding (runtime_model μ) β]

open complexity

-- protected lemma strong_induction_on {p : nat → Prop} (n : nat) (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
-- nat.strong_rec_on n h

def complexity (p: program μ) (f: α → β) (cost: α → ℕ) :=
  ∀ a, complexity.witness' (runtime_model μ) (p, push_arg (encode (runtime_model μ) a) bank.null) (f a) (cost a)

-- theorem recursive_complexity
--   (p: program μ) (f: α → β)
--   (size: α → ℕ) (call_cost: ℕ → ℕ) (total_cost: α → ℕ)
--   (hsize: ∀ {a m}, recurse_arg p (push_arg (encode (runtime_model μ) a) bank.null) m → ∃ a', m = (push_arg (encode (runtime_model μ) a') bank.null) ∧ size a' < size a)
--   (hrec: ∀ a₁,
--     (∀ a₀, size a₀ < size a₁ → p.has_result (push_arg (encode (runtime_model μ) a₀) bank.null) (encode (runtime_model μ) (f a₀))) →
--     call_cost_le ⟨p, p, (push_arg (encode (runtime_model μ) a₁) bank.null)⟩ (call_cost (size a₁)) ∧
--     p.has_result (push_arg (encode (runtime_model μ) a₁) bank.null) (push_arg (encode (runtime_model μ) (f a₁)) bank.null))
--   (hc: ∀ a, divide_and_conquer_cost p call_cost (size a) ≤ total_cost a):
--   complexity p f total_cost :=
-- begin
--   intro a,
--   induction hn:(size a) using nat.strong_induction_on with n ih,
--   unfold witness',
--   rw [cast_unwrap, fcast],
--   apply program.costed_result_of_cost_of_result,
--   {
--     simp only [],
--     apply program.cost_le_mono (hc _),
--     apply divide_and_conquer_cost_sound (λ m n, ∃ x : α, m = (push_arg (encode (runtime_model μ) x) bank.null) ∧ n = size x),
--     { intros inp n arg harg hinp,
--       rcases hinp with ⟨m_inp, hinp, inp_size⟩,
--       rw [hinp] at harg,
--       rcases hsize harg with ⟨m_arg, harg, hsize⟩,
--       rw [inp_size],
--       exact ⟨_, hsize, _, harg, rfl⟩ },
--     { intros inp n' hinp,
--       rcases hinp with ⟨m_inp, hinp, inp_size⟩,
--       rw [hinp, inp_size],
--       apply (hrec _ _).left,
--       intros ax hax,
--       rw [← inp_size] at hax,
--       specialize ih (size ax),
      

      

--     },
--   },
--   -- apply stack.step_halt_le _ (hc _),
  




-- end

-- local attribute [simp] application_def' program.apply stack.step bank.getmp bank.getm bank.getv bank.setmp source.getv get_push_arg_0 get_push_arg_1 set_push_arg_0 set_push_arg_1 frame.setm


-- instance compose_complexity
--   (α β γ: Type)
--   [α_en: complexity.has_encoding (runtime_model μ) α] [β_en: complexity.has_encoding (runtime_model μ) β] [γ_en: complexity.has_encoding (runtime_model μ) γ]
--   (f: α → β) (g: β → γ) [cf: complexity.has_complexity (runtime_model μ) f] [cg: complexity.has_complexity (runtime_model μ) g]:
--   complexity.has_complexity (runtime_model μ) (compose g f) :=
-- ⟨ ⟨ λ a, ((cg.value.cost (f a) + 1:ℕ) + (cf.value.cost a+1:ℕ) + 9:ℕ),
-- begin
--   rcases cf.value with ⟨cfc, fp, cfp⟩,
--   rcases cg.value with ⟨cgc, gp, cgp⟩,
--   fconstructor,
--   fconstructor,
--   refine [_, _, _, _, _, _, _, _],
--   exact instruction.move [(source.imm 0)] [],
--   exact instruction.move [(source.imm 1)] [],
--   exact instruction.move [(source.imm 1), (source.imm 0)] [(source.imm 0), (source.imm 0), (source.imm 1)],
--   exact instruction.move [(source.imm 0), (source.imm 0)] [(source.imm 0), (source.imm 0), (source.imm 0)],
--   exact instruction.call fp.fst (source.imm 0),
--   exact instruction.move [(source.imm 1), (source.imm 1)] [(source.imm 0)],
--   exact instruction.call gp.fst (source.imm 1),
--   exact instruction.move [] [(source.imm 0)],
--   exact push_arg fp.snd gp.snd,
--   intros a,
--   simp,
--   -- TODO
-- end ⟩ ⟩

-- open_locale big_operators
-- def cost (n: ℕ) (f: ℕ → ℕ): ℕ := (∑ i : fin n.succ, f (n - i) * 2 ^ (i:ℕ))
-- #eval cost 5 (λ n, 24*2^n + 35) -- 6813

-- theorem master_theorem_leaf_heavy (f: ℕ → ℕ) (a n: ℕ) (ha_pos: 0 < a):
--   (∃ (c < a) k, ∀ i, f i ≤ k * c ^ i) → ∃ k, (∑ i : fin n.succ, f (n - i) * a ^ (i:ℕ)) ≤ k * a ^ n := sorry

end encoding
end membank