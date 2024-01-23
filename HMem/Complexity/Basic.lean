import HMem.Encoding.Basic
import HMem.Trace.Cost
import Complexity.Basic
import HMem.Complexity.Def

namespace HMem.Complexity

instance [Complexity.Coding α Memory]: Program.HasCost ↿(@List.cons α) 1 where
  program := [ .setv 0 true ]
  size _ := 0
  sound | (_, _) => by simp
  cost_ale := Program.nonRecursiveComplexity (Complexity.ALE.const_ale _ _)

end HMem.Complexity
