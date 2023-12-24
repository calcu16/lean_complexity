import HMem.Encoding.Basic
import Complexity.Basic


namespace HMem.Computability

@[simp] theorem data_def: Encoding.Model.Data = Memory := rfl
@[simp] theorem result_def: Encoding.Model.Result = Memory := rfl
@[simp] theorem model_has_result: Encoding.Model.has_result = Program.hasResult := rfl


instance [h: Complexity.Encoding α Memory]: Complexity.Encoding α Encoding.Model.Data := h
instance [h: Complexity.Encoding α Memory]: Complexity.Encoding α Encoding.Model.Result := h

def getProgram [Complexity.Encoding α Memory] [Complexity.Encoding β Memory] (f: α → β) [h: Computable Encoding.Model f]: Program :=
  h.program

instance [Complexity.Encoding α Memory]: Computable Encoding.Model (Function.uncurry (@List.cons α)) where
  program := [ .vop (λ _ ↦ true) .nil finZeroElim ]
  has_result
  | (a, as) => by simp

end HMem.Computability
