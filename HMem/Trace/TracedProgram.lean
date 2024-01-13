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

@[simp] def setv (dst: Source) (b: Bool): TracedProgram → TracedProgram := op (.vop (λ _ ↦ b) dst finZeroElim)
@[simp] def setm (dst: Source) (src: Memory): TracedProgram  → TracedProgram := op (.const dst src)
@[simp] def copyv (dst src: Source): TracedProgram  → TracedProgram := op (.vop (λ f ↦ f 0) dst (λ (_: Fin 1) ↦ src))
@[simp] def copy (dst src: Source): TracedProgram  → TracedProgram := op (.mop .COPY dst src)
@[simp] def move (dst src: Source): TracedProgram  → TracedProgram := op (.mop .MOVE dst src)
@[simp] def swap (dst src: Source): TracedProgram  → TracedProgram := op (.mop .SWAP dst src)
@[simp] def ifv (src: Source) (pos: List (TracedProgram  → TracedProgram)) (neg: TracedProgram): TracedProgram := branch (.ifTrue (λ f ↦ f 0) (λ (_: Fin 1) ↦ src)) (λ | true => build pos | false => neg)

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

end Trace

def Program.traced (p: Program) [htp: Trace.HasTracedProgram p]: Trace.TracedProgram := htp.tracedProgram

@[simp] theorem Program.tracedMatches (p: Program) [Trace.HasTracedProgram p]:
    p.traced.toProgram = p := Trace.HasTracedProgram.tracedProgramMatches

end HMem
