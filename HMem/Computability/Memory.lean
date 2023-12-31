import HMem.Encoding.Basic
import HMem.Encoding.Emulator
import HMem.Computability.Basic
import Complexity.Basic


namespace HMem.Computability

instance: HasTrace Memory.getv where
  program := .build [
    .op (.const (.imm false .nil) 0),
    .op (.const (.imm true .nil) 0)]
  trace _ := []
  sound.correct | _ => by simp
  sound.consistent | _, _ => by simp
  sound.wellFounded := ⟨ λ | _ => Acc.intro _ λ | _ => by simp ⟩

instance: HasTrace (Function.uncurry Memory.getm) where
  program := .build [ .op (.mop .MOVE .nil (.imm false (.idx (.imm true .nil) .nil))) ]
  trace _ := []
  sound.correct | (_, _) => by simp
  sound.consistent | _, _ => by simp
  sound.wellFounded := ⟨ λ | _ => Acc.intro _ λ | _ => by simp ⟩

instance [Computable Encoding.Model (Function.uncurry Memory.getmp)] [Computable Encoding.Model Memory.getv]: HasTrace (Function.uncurry Memory.getvp) where
  program := .build [
    .subroutine .nil .nil (Encoding.getProgram (Function.uncurry Memory.getmp)),
    .subroutine .nil .nil (Encoding.getProgram Memory.getv)
  ]
  trace | (m, as) => [
    .subroutine (Function.uncurry Memory.getmp) (m, as),
    .subroutine Memory.getv (m.getmp as),
   ]
  sound.correct | (_, as) => by simp
  sound.consistent | (_, as), (_, bs) => by simp
  sound.wellFounded := ⟨ λ | _ => Acc.intro _ λ | _ => by simp ⟩

instance: HasTrace (Function.uncurry Memory.getmp) where
  program := .build [
    .branch (.ifTrue (λ (op:Fin 1 → Bool) ↦ op 0) (λ _ ↦ .imm true .nil)) (.build [
      .op (.mop .MOVE (.imm false .nil) (.imm false (.idx (.imm true (.imm false .nil)) .nil))),
      .op (.mop .MOVE (.imm true .nil) (.imm true (.imm true .nil))),
      .recurse .nil .nil
    ]),
    .op (.mop .MOVE .nil (.imm false .nil))
  ]
  trace
  | (_, []) => [ .branch false]
  | (m, a::as) => [ .branch true, .recurse (m.getm a, as)]
  sound.correct | (_, as) => by cases as <;> simp
  sound.consistent | (_, as), (_, bs) => by cases as <;> cases bs <;> simp
  sound.wellFounded := sorry

end HMem.Computability
