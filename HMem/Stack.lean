import HMem.Memory
import Mathlib.Logic.Function.Iterate

namespace HMem

namespace Instruction
inductive MemoryOperation
| COPY
| MOVE
| SWAP
end Instruction

def Memory.mop (m: Memory): Instruction.MemoryOperation → Source → Source → Memory
| .COPY, dst, _ => m.getms dst
| .MOVE, _, _ => 0
| .SWAP, _, src => m.getms src

inductive Instruction
| vop {N: ℕ} (op: (Fin N → Bool) → Bool) (dst: Source) (src: Fin N → Source)
| mop (op: Instruction.MemoryOperation) (dst src: Source)
| clear (dst: Source)
| ite {N: ℕ} (cond: (Fin N → Bool) → Bool) (src: Fin N → Source) (branch: List Instruction)
| call (func: List Instruction) (dst src: Source)
| recurse (dst src: Source)

instance: Inhabited Instruction where
  default := Instruction.mop Instruction.MemoryOperation.COPY Source.nil Source.nil

def Program: Type _ := List Instruction

structure Thunk where
  function: Program
  current: Program
  state: Memory

namespace Thunk

inductive Step
| thunk (value: Thunk)
| result (value: Memory)
| call (func: Option (Program)) (arg: Memory) (caller: Thunk) (as: List Bool)

def step: Thunk → Step
| ⟨_, [], m⟩ => .result m
| ⟨p, .vop op dst src::is, m⟩ => .thunk ⟨p, is, m.setvs dst (op (m.getvs ∘ src))⟩
| ⟨p, .mop op dst src::is, m⟩ => .thunk ⟨p, is, (m.setms src (m.mop op src dst)).setms dst (m.getms src)⟩
| ⟨p, .clear dst::is, m⟩ => .thunk ⟨p, is, m.setms dst 0⟩
| ⟨p, .ite cond src is'::is, m⟩ => .thunk ⟨p, ite (cond (m.getvs ∘ src)) is' is, m⟩
| ⟨p, .call func dst src::is, m⟩ => .call (some func) (m.getms src) ⟨p, is, m⟩ (dst.get m)
| ⟨p, .recurse  dst src::is, m⟩ => .call none (m.getms src) ⟨p, is, m⟩ (dst.get m)

def set_result: Thunk → List Bool → Memory → Thunk
| ⟨p, is, m⟩, as, m' => ⟨p, is, m.setmp as m'⟩

end Thunk

def Program.call (p: Program) (m: Memory): Thunk := ⟨p, p, m⟩

inductive Stack
| result (value: Memory)
| execution (top: Thunk) (callers: List (Thunk × List Bool))

namespace Stack
def step: Stack → Stack
| execution f caller => match f.step with
  | .thunk t => execution t caller
  | .result m => match caller with
    | [] => result m
    | c::cs => execution (c.fst.set_result c.snd m) cs
  | .call func arg ret as =>
    execution ((func.getD f.function).call arg) ((ret.set_result as 0, as)::caller)
| result m => result m

def getResult: Stack → Memory
| result m => m
| _ => 0

end Stack

namespace Program

def haltsOn (p: Program) (inp: Memory): Prop :=
  ∃ n outp, Stack.step^[n] (.execution (p.call inp) []) = .result outp

instance (s: Stack) (n: ℕ): Decidable (∃ outp, Stack.step^[n] s = .result outp) :=
  match Stack.step^[n] s with
  | .execution _ _ => Decidable.isFalse (not_exists_of_forall_not λ _ ↦ Stack.noConfusion)
  | .result _ => Decidable.isTrue ⟨_, rfl⟩

def timeCost (p: Program) {inp: Memory} (h: p.haltsOn inp): ℕ := Nat.find h

def result (p: Program) {inp: Memory} (h: p.haltsOn inp): Memory :=
  (Stack.step^[p.timeCost h] (.execution (p.call inp) [])).getResult

end Program
end HMem
