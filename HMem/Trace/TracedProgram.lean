import Complexity.Basic
import HMem.Encoding.Basic

namespace HMem
namespace Trace

inductive TracedProgram
| exit
| op (inst: OpInstruction) (next: TracedProgram)
| branch (inst: BranchInstruction) (next: Bool → TracedProgram)
| subroutine (dst src: Source) {γ: Type _} [enγ: Complexity.Encoding γ Memory] {δ: Type _} [enδ: Complexity.Encoding δ Memory]
  (fs: γ → δ) [h: Complexity.Computable Encoding.Model fs] (next: TracedProgram)
| recurse (dst src: Source) (next: TracedProgram)

namespace TracedProgram
variable {α: Type _} [Complexity.Encoding α Memory] {β: Type _} [Complexity.Encoding β Memory] {f: α → β}

@[simp] def build: List (TracedProgram → TracedProgram) → TracedProgram
| [] => .exit
| p::ps => p (build ps)

@[match_pattern] def subroutine' (dst src: Source) {γ: Type _} (_hγ: Complexity.Encoding γ Memory) {δ: Type _} (_hδ: Complexity.Encoding δ Memory)
    (fs: γ → δ) (_h: Complexity.Computable Encoding.Model fs) (next: TracedProgram): TracedProgram :=
  subroutine dst src fs next

def toProgram: TracedProgram → Program
| exit => .exit
| op inst next => .op inst next.toProgram
| branch inst next => .branch inst (λ b ↦ toProgram (next b))
| subroutine dst src fs next => .subroutine dst src (Encoding.getProgram fs) next.toProgram
| recurse dst src next => .recurse dst src next.toProgram

end TracedProgram

class HasTracedProgram (p: Program) where
  tracedProgram: TracedProgram
  tracedProgramMatches: tracedProgram.toProgram = p

instance (tp: TracedProgram): HasTracedProgram tp.toProgram := ⟨ _, rfl ⟩

attribute [simp] HasTracedProgram.tracedProgram
end Trace

@[simp] def Program.traced (p: Program) [htp: Trace.HasTracedProgram p]: Trace.TracedProgram := htp.tracedProgram

@[simp] theorem Program.tracedMatches (p: Program) [Trace.HasTracedProgram p]:
    p.traced.toProgram = p := Trace.HasTracedProgram.tracedProgramMatches

end HMem
