import tactic
import membank.basic
import complexity.basic
import complexity.core

namespace membank
namespace encoding

variables {μ: Type*} [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]

def push_arg: bank μ → bank μ → bank μ := λ l r,
  (bank.mem 1 (λ n, if n = 0 then l else if n = 1 then r else bank.null))

def runtime_model (μ: Type*) [decidable_eq μ] [has_zero μ] [has_one μ] [ne_zero (1:μ)]: complexity.model (program μ × bank μ) (bank μ) ℕ :=
 ⟨  λ p_a r c, stack.step^[c] (function.uncurry program.apply p_a) = (stack.result r),
    λ p_a a', (p_a.fst, push_arg p_a.snd a'),
    λ _ _ _ c₀ c₁ h₀ h₁,
      bank.equiv_refl' (stack.result.inj (or.elim (le_total c₀ c₁)
        (λ h, h₁ ▸ (stack.step_halt_le h₀ h).symm)
        (h₀ ▸ stack.step_halt_le h₁))),
    λ _ _ _ _, flip stack.step_halt_le ⟩

theorem application_def (p: program μ) (arg₀ arg₁: bank μ):
 complexity.model.application (runtime_model μ) (p, arg₀) arg₁ = (p, push_arg arg₀ arg₁) := rfl

theorem application_def' (p: program μ × bank μ) (arg: bank μ):
 complexity.model.application (runtime_model μ) p arg = (p.fst, push_arg p.snd arg) := rfl

theorem get_push_arg_v (arg₀ arg₁: bank μ): (push_arg arg₀ arg₁).getv = 1 :=
by simp [push_arg, bank.get]

theorem get_push_arg_0 (arg₀ arg₁: bank μ): (push_arg arg₀ arg₁).getm 0 = arg₀ :=
by simp [push_arg, bank.getm]

theorem get_push_arg_1 (arg₀ arg₁: bank μ): (push_arg arg₀ arg₁).getm 1 = arg₁ :=
by simp [push_arg, bank.getm]

theorem ite_ite_self (p: Prop) [decidable p] {α: Sort*} (a b c: α): ite p (ite p a b) c = ite p a c :=
by split_ifs; refl

theorem ite_ite_self' (p: Prop) [decidable p] {α: Sort*} (a b c: α): ite p a (ite p b c) = ite p a c :=
by split_ifs; refl

theorem set_push_arg_0 (arg₀ arg₁ arg₂: bank μ): (push_arg arg₀ arg₁).setm 0 arg₂ = (push_arg arg₂ arg₁) :=
by simp [push_arg, bank.setm, @eq_comm μ 0, ite_ite_self']

theorem set_push_arg_1 (arg₀ arg₁ arg₂: bank μ): (push_arg arg₀ arg₁).setm 1 arg₂ = (push_arg arg₀ arg₂) :=
begin
  simp only [push_arg, bank.setm, @eq_comm μ 1, eq_self_iff_true, true_and],
  ext1,
  split_ifs;
  try { refl },
  rw [h_1] at h,
  exact absurd h zero_ne_one,
end

local attribute [simp] application_def' program.apply stack.step bank.getmp bank.getm bank.getv bank.setmp source.getv get_push_arg_0 get_push_arg_1 set_push_arg_0 set_push_arg_1 frame.setm


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

end encoding
end membank