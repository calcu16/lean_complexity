import HMem.Memory
import HMem.Stack
import HMem.Encoding.Basic
import Complexity.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Fin.Tuple.Basic

namespace HMem
namespace Encoding
open Complexity

def encodeSource: Source → Memory
| .nil => 0
| .imm hd tl => .mk true (.mk false (encode hd) 0) (encodeSource tl)
| .idx hd tl => .mk true (.mk true (encodeSource hd) 0) (encodeSource tl)

theorem encodeSource_inj {s₀ s₁: Source}: encodeSource s₀ = encodeSource s₁ → s₀ = s₁ := by
  cases h₀:s₀ <;> cases h₁:s₁
  case imm.imm => simpa [encodeSource] using λ hhd htl ↦ ⟨hhd, encodeSource_inj htl⟩
  case idx.idx => simpa [encodeSource] using λ hhd htl ↦ ⟨encodeSource_inj hhd, encodeSource_inj htl⟩
  all_goals { simp [encodeSource] }

instance: Encoding Source Memory where
  encode := encodeSource
  inj _ _ := encodeSource_inj

instance: Encoding Instruction.MemoryOperation Memory where
  encode
  | .COPY => 0
  | .MOVE => 1
  | .SWAP => .mk true 1 0
  inj a b := by cases a <;> cases b <;> simp

def encodeProgram: List Instruction → Memory
| [] => 0
| i::is => (Memory.mk true) (match i with
  | .clear src => .mk false (.mk false (encode src) 0) 0
  | .vop op dst src => .mk false (.mk false (encode op) 0) (.mk true (encode dst) (encode src))
  | .mop op dst src => .mk false (.mk true (encode op) 0) (.mk false (encode dst) (encode src))
  | .recurse dst src => .mk true (.mk false (encode dst) (encode src)) 0
  | .call dst src func => .mk true (.mk false (encode dst) (encode src)) (.mk true (encodeProgram func) 0)
  | .branch cond src branch => .mk true (.mk true (encode cond) 0) (.mk true (encode src) (encodeProgram branch))
) (encodeProgram is)

def encodeProgram_inj {is₀ is₁: List Instruction}: encodeProgram is₀ = encodeProgram is₁ → is₀ = is₁ := by
  cases is₀ <;> cases is₁
  case cons.cons hd₀ tl₀ hd₁ tl₁ =>
    cases hd₀ <;> cases hd₁
    case vop.vop =>
      simpa [
        encodeProgram, and_assoc,
        Iff.intro (@encodeProgram_inj tl₀ tl₁) (λ h ↦ h ▸ rfl)]
        using λ hN hopt hdst _ hsrc htl ↦ ⟨ hN, hopt, hdst, hsrc, htl ⟩
    case branch.branch _ _ _ branch₀ _ _ _ branch₁ =>
      simpa [
        encodeProgram, and_assoc,
        Iff.intro (@encodeProgram_inj tl₀ tl₁) (λ h ↦ h ▸ rfl),
        Iff.intro (@encodeProgram_inj branch₀ branch₁) (λ h ↦ h ▸ rfl)]
        using  λ hN hcond _ hsrc hbranch htl ↦ ⟨ hN, hcond, hsrc, hbranch, htl ⟩
    case call.call _ _ func₀ _ _ func₁ =>
      simp [
        encodeProgram, and_assoc,
        Iff.intro (@encodeProgram_inj tl₀ tl₁) (λ h ↦ h ▸ rfl),
        Iff.intro (@encodeProgram_inj func₀ func₁) (λ h ↦ h ▸ rfl)]
    all_goals simp [encodeProgram, and_assoc,
      Iff.intro (@encodeProgram_inj tl₀ tl₁) (λ h ↦ h ▸ rfl)]
  all_goals unfold encodeProgram; simp

instance: Encoding Instruction Memory where
  encode := encodeProgram ∘ flip List.cons []
  inj _ _ := List.head_eq_of_cons_eq ∘ encodeProgram_inj

instance: Encoding Program Memory where
  encode := encode (α := List Instruction)
  inj := Encoding.inj (α := List Instruction)

instance: Encoding Instruction.Step Memory where
  encode
  | .op value => .mk false (encode value) 0
  | .branch value => .mk false (encode value) 1
  | .call func dst arg => .mk true (.mk false (encode func)  (encode dst)) (encode arg)
  inj a b := by
    cases a <;> cases b
    case call.call => simpa using λ hf hd ha => ⟨hf, hd, ha⟩
    all_goals simp

instance: Encoding Thunk Memory where
  encode
  | .mk f c s => .mk false (.mk false (encode f) (encode c)) (encode s)
  inj
  | .mk _ _ _, .mk _ _ _ => by
    simpa using λ hf hc hs ↦ ⟨ hf, hc, hs ⟩


end Encoding
end HMem
