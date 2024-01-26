import HMem.Memory

/-!
Defines the data structures used for executing Programs that manipulate memory.
-/
namespace HMem
inductive OpInstruction.MemoryOperation
| COPY
| MOVE
| SWAP

inductive OpInstruction
| vop {N: ℕ} (op: (Fin N → Bool) → Bool) (dst: Source) (src: Fin N → Source)
| mop (op: OpInstruction.MemoryOperation) (dst src: Source)
| const (dst: Source) (val: Memory)

inductive BranchInstruction
| ifTrue {N: ℕ} (cond: (Fin N → Bool) → Bool) (src: Fin N → Source)
| ifNull (src: Source)

inductive Program
| exit
| op (inst: OpInstruction) (next: Program)
| branch (inst: BranchInstruction) (next: Bool → Program)
| subroutine (dst src: Source) (func: Program) (next: Program)
| recurse (dst src: Source) (next: Program)

namespace Program

def build: List (Program → Program) → Program
| [] => .exit
| p::ps => p (build ps)

def size: Program → ℕ
| exit => 1
| op _ next => size next + 1
| branch _ next => size (next true) + size (next false) + 1
| subroutine _ _ func next => size func + size next + 1
| recurse _ _ next => size next + 1

def maxRecurse: Program → ℕ
| exit => 0
| op _ next => maxRecurse next
| branch _ next => max (maxRecurse (next true)) (maxRecurse (next false))
| subroutine _ _ _ next => maxRecurse next
| recurse _ _ next => maxRecurse next + 1

def selfContained: Program → Bool
| exit => true
| op _ next => selfContained next
| branch _ next => (selfContained (next true)) && (selfContained (next false))
| subroutine _ _ _ _ => false
| recurse _ _ next => selfContained next

@[match_pattern] def call (dst src: Source): Option Program → Program → Program
| some func, next => subroutine dst src func next
| none, next => recurse dst src next

def subroutine_def: subroutine dst src func next = call dst src (some func) next := rfl
def recurse_def: recurse dst src next = call dst src none next := rfl

end Program

structure Thunk where
  state: Memory
  current: Program
  function: Program

theorem Thunk.congr {s₀ s₁: Memory} {c₀ c₁ f₀ f₁: Program}
    (hs: s₀ = s₁) (hc: c₀ = c₁) (hf: f₀ = f₁):
  Thunk.mk s₀ c₀ f₀ = ⟨s₁, c₁, f₁⟩ := hs ▸ hc ▸ hf ▸ rfl

def Thunk.setResult: Thunk → List Bool → Memory → Thunk
| ⟨m, is, p⟩, as, m' => ⟨m.setmp as m', is, p⟩

inductive Stack
| result (value: Memory)
| execution (top: Thunk) (callers: List (Thunk × List Bool))


def Stack.getResult: Stack → Memory
| result m => m
| _ => 0
end HMem
