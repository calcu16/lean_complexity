import HMem.Trace
import HMem.Encoding.Basic
import Complexity.Basic


@[simp] def HMem.Program.build: List (Program → Program) → Program
| [] => .exit
| p::ps => p (build ps)

namespace HMem.Computability

instance (f: α → β) [Complexity.Encoding α Memory] [Complexity.Encoding β Memory] [htr: HasTrace f]: Computable Encoding.Model f where
  program := htr.program
  has_result := htr.sound.hasResult

instance [Complexity.Encoding α Memory]: HasTrace (Function.uncurry (@List.cons α)) where
  program := .build [ .op (.vop (λ _ ↦ true) .nil finZeroElim) ]
  trace _ := []
  sound.correct | (_, _) => by simp
  sound.consistent | _, _ => by simp
  sound.wellFounded := ⟨ λ | (_, _) => Acc.intro _ λ | (_, _) => by simp ⟩


end HMem.Computability
