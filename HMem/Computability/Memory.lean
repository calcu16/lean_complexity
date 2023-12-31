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
  prop.correct | _ => by simp
  prop.consistent | _, _ => by simp
  prop.wellFounded := ⟨ λ | _ => Acc.intro _ λ | _ => by simp ⟩

instance: HasTrace (Function.uncurry Memory.getm) where
  program := .build [ .op (.mop .MOVE .nil (.imm false (.idx (.imm true .nil) .nil))) ]
  trace _ := []
  prop.correct | (_, _) => by simp
  prop.consistent | _, _ => by simp
  prop.wellFounded := ⟨ λ | _ => Acc.intro _ λ | _ => by simp ⟩

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
  prop.correct
  | (_, as) => by
    cases as <;> simp [TraceElem.matchesThunk, TraceElem.matchesProgram, BranchInstruction.apply]
  prop.consistent
  | (_, as), (_, bs) => by
    cases as <;> cases bs <;> simp
  prop.wellFounded := sorry

end HMem.Computability
