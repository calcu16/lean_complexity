import HMem.Encoding.Basic
import HMem.Encoding.Emulator
import HMem.Complexity.Basic
import Complexity.Basic

namespace HMem.Complexity
instance: Program.HasTrace Memory.getv where
  program := [
    .setm 1 0,
    .setm 2 0
  ]
  size _ := 0
  sound _ := by simp

instance: Program.HasTrace ↿Memory.getm where
  program := [ .move .nil (.imm false (.idx 2 0)) ]
  size _ := 0
  sound | (_, _) => by simp

instance [Complexity.Computable Encoding.Model ↿Memory.getmp] [Complexity.Computable Encoding.Model Memory.getv]:
    Program.HasTrace ↿Memory.getvp where
  program := [
    .subroutine' 0 0 ↿Memory.getmp,
    .subroutine' 0 0 Memory.getv
  ]
  size _ := 0
  sound | (_, _) => by simp [and_assoc]

instance: Program.HasTrace ↿Memory.getmp where
  program := [
    .ifv 2 [
      .move 1 (.imm false (.idx 5 0)),
      .move 2 6,
      .recurse 0 0
    ],
    .move 0 1
  ]
  size | (_, as) => as.length
  sound
  | (_, as) => by cases as <;> simp

instance [Complexity.Computable Encoding.Model ↿Memory.getvp] [Complexity.Computable Encoding.Model ↿(@List.cons Bool)]:
  Program.HasTrace ↿Source.get where
  program := [
    .ifv 1 [
      .move 6 2,
      .move 5 4,
      .copy 4 6,
      .recurse 2 2,
      .ifv 3 [
        .copy 8 4,
        .setv 3 false,
        .recurse 3 3,
        .swap 3 4,
        .setv 1 false,
        .subroutine' 1 1 ↿Memory.getvp,
        .subroutine' 0 0 ↿(@List.cons Bool)
      ],
      .move 1 7,
      .subroutine' 0 0 ↿(@List.cons Bool)
    ],
    .setm 0 0
  ]
  size | (s, _) => s.size
  sound | (s, _) => by cases s <;> simp
end HMem.Complexity
