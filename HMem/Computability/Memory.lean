import HMem.Encoding.Basic
import HMem.Encoding.Emulator
import HMem.Computability.Basic
import Complexity.Basic


namespace HMem.Computability

instance: HasTrace Memory.getv where
  program := .build [
    .setm 1 0,
    .setm 2 0
  ]
  trace _ := []
  height _ := 0
  sound.correct _ := by simp
  sound.consistent _ _ := by simp
  sound.wellFounded _ := by simp

instance: HasTrace ↿Memory.getm where
  program := .build [ .move .nil (.imm false (.idx 2 0)) ]
  trace _ := []
  height := 0
  sound.correct | (_, _) => by simp
  sound.consistent _ _ := by simp
  sound.wellFounded _ := by simp

instance [Computable Encoding.Model ↿Memory.getmp] [Computable Encoding.Model Memory.getv]: HasTrace ↿Memory.getvp where
  program := .build [
    .subroutine' 0 0 ↿Memory.getmp,
    .subroutine' 0 0 Memory.getv
  ]
  trace | (m, as) => [
    .subroutine ↿Memory.getmp (m, as),
    .subroutine Memory.getv (m.getmp as),
   ]
  height := 0
  sound.correct
    | (_, as) => by simp
  sound.consistent | (_, as), (_, bs) => by simp
  sound.wellFounded | (_, as) => by simp

instance: HasTrace ↿Memory.getmp where
  program := .build [
    .ifv 2 [
      .move 1 (.imm false (.idx 5 0)),
      .move 2 6,
      .recurse 0 0
    ],
    .move 0 1
  ]
  trace
  | (_, []) => [ .branch false]
  | (m, a::as) => [ .branch true, .recurse (m.getm a, as)]
  height | (_, as) => as.length
  sound.correct | (_, as) => by cases as <;> simp
  sound.consistent | (_, as), (_, bs) => by cases as <;> cases bs <;> simp
  sound.wellFounded
  | (_, []) => by simp
  | (_, _::_) => by simp

instance  [Computable Encoding.Model ↿Memory.getvp] [Computable Encoding.Model ↿(@List.cons Bool)]: HasTrace ↿Source.get where
  program := .build [
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
  trace
  | (.nil, _) => [.branch false]
  | (.imm hd tl, m) => [
      .branch true,
      .recurse (tl, m),
      .branch false,
      .subroutine (↿(@List.cons Bool)) (hd, tl.get m)
    ]
  | (.idx hd tl, m) => [
    .branch true,
    .recurse (tl, m),
    .branch true,
    .recurse (hd, m),
    .subroutine ↿Memory.getvp (m, hd.get m),
    .subroutine ↿(@List.cons Bool) (m.getvp (hd.get m), tl.get m)
  ]
  height | (s, _) => s.height
  sound.correct | (s, _) => by cases s <;> simp
  sound.consistent | (s₀, _), (s₁, _) => by cases s₀ <;> cases s₁ <;> simp
  sound.wellFounded
  | (.nil, _ ) => by simp
  | (.imm _ _, _ ) => by simp
  | (.idx _ _, _ ) => by simp

end HMem.Computability
