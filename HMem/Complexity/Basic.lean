import HMem.Encoding.Basic
import HMem.Trace.TracedProgram
import HMem.Trace.Sound
import Complexity.Basic

@[simp] theorem Function.HasUncurry.apply₂ (f: α → β → γ) (arg: α × β):
    (↿f) arg = f arg.fst arg.snd := rfl

namespace HMem.Complexity

instance [Complexity.Encoding α Memory]: Trace.HasTrace ↿(@List.cons α) where
  program := [ .setv 0 true ]
  size _ := 0
  sound | (_, _) => by simp

end HMem.Complexity
