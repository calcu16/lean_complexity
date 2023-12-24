import HMem.Encoding.Basic
import HMem.Encoding.Emulator
import HMem.Computability.Basic
import Complexity.Basic


namespace HMem.Computability

instance: Computable Encoding.Model Memory.getv where
  program := [
    .clear (.imm false .nil),
    .clear (.imm true .nil)]
  has_result a := by simp


instance: Computable Encoding.Model (Function.uncurry Memory.getm) where
  program := [ .mop .MOVE .nil (.imm false (.idx (.imm true .nil) .nil)) ]
  has_result | (m, b) => by simp

instance: Computable Encoding.Model (Function.uncurry Memory.getmp) where
  program := [
    .ite (λ (op:Fin 1 → Bool) ↦ op 0) (λ _ ↦ .imm true .nil) [
      .mop .MOVE (.imm false .nil) (.imm false (.idx (.imm true (.imm false .nil)) .nil)),
      .mop .MOVE (.imm true .nil) (.imm true (.imm true .nil)),
      .recurse .nil .nil
    ],
    .mop .MOVE .nil (.imm false .nil)
  ]
  has_result
  | (m, bs) => by
    induction bs generalizing m with
    | nil => simp
    | cons hd tl ih => simpa using ih (m.getm hd)


-- instance: Computable Encoding.Model (Function.uncurry Memory.getvp) where
--   program := [
--     .call .nil .nil (getProgram (Function.uncurry Memory.getmp)),
--     .call .nil .nil (getProgram Memory.getv)
--   ]
--   has_result
--   | (m, bs) => by
--     simp

end HMem.Computability
