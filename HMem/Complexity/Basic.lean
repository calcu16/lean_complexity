import HMem.Encoding.Basic
import HMem.Trace.Cost
import Complexity.Basic
import HMem.Complexity.Def

@[simp] theorem Function.HasUncurry.apply₂ (f: α → β → γ) (arg: α × β):
    (↿f) arg = f arg.fst arg.snd := rfl

namespace HMem.Complexity

instance [Complexity.Encoding α Memory]: Program.HasCost ↿(@List.cons α) where
  program := [ .setv 0 true ]
  size _ := 0
  sound | (_, _) => by simp
  cost := 1
  cost_le := Complexity.ALE.ale_of_le_of_ale
    (Program.splitTimeCost _)
    (Complexity.ALE.add_ale
      (Complexity.ALE.const_ale _ _)
      (Program.localTimeCost_const _))

end HMem.Complexity
