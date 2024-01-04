import HMem.Trace
import HMem.Encoding.Basic
import HMem.Computability.TracedProgram
import Complexity.Basic

@[simp] theorem Function.HasUncurry.apply₂ (f: α → β → γ) (arg: α × β):
    (↿f) arg = f arg.fst arg.snd := rfl

namespace HMem.Computability

instance (f: α → β) [Complexity.Encoding α Memory] [Complexity.Encoding β Memory] [htr: HasTrace f]:
    Computable Encoding.Model f where
  program := htr.program
  has_result := htr.sound.hasResult

instance [Complexity.Encoding α Memory]: HasTrace ↿(@List.cons α) where
  program := .build [ .setv 0 true ]
  trace _ := []
  height _ := 0
  sound.correct | (_, _) => by simp
  sound.consistent | _, _ => by simp
  sound.wellFounded | _ => by simp

instance [Complexity.Encoding α Memory]: Complexity.TracedProgram.HasTrace ↿(@List.cons α) where
  program := [ .setv 0 true ]
  size _ := 0
  sound | (_, _) => by simp

end HMem.Computability
