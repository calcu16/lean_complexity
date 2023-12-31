import HMem.Trace
import HMem.Encoding.Basic
import Complexity.Basic


@[simp] def HMem.Program.build: List (Program → Program) → Program
| [] => .exit
| p::ps => p (build ps)

namespace HMem.Computability

@[simp] theorem data_def: Encoding.Model.Data = Memory := rfl
@[simp] theorem result_def: Encoding.Model.Result = Memory := rfl
@[simp] theorem model_has_result: Encoding.Model.has_result = Program.hasResult := rfl


instance [h: Complexity.Encoding α Memory]: Complexity.Encoding α Encoding.Model.Data := h
instance [h: Complexity.Encoding α Memory]: Complexity.Encoding α Encoding.Model.Result := h

instance (f: α → β) [Complexity.Encoding α Memory] [Complexity.Encoding β Memory] [htr: HasTrace f]: Computable Encoding.Model f where
  program := htr.program
  has_result := htr.prop.hasResult

def getProgram [Complexity.Encoding α Memory] [Complexity.Encoding β Memory] (f: α → β) [h: Computable Encoding.Model f]: Program :=
  h.program

instance [Complexity.Encoding α Memory]: HasTrace (Function.uncurry (@List.cons α)) where
  program := .build [ .op (.vop (λ _ ↦ true) .nil finZeroElim) ]
  trace _ := []
  prop.correct | (_, _) => by simp
  prop.consistent | _, _ => by simp
  prop.wellFounded := ⟨ λ | (_, _) => Acc.intro _ λ | (_, _) => by simp ⟩


end HMem.Computability
