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
  all_goals simp[encodeSource]

instance: Encoding Source Memory where
  encode := encodeSource
  encode_inj _ _ := encodeSource_inj

@[simp] theorem encodeSource_nil: (encode Source.nil:Memory) = 0 := rfl
@[simp] theorem encodeSource_imm: (encode (Source.imm hd tl):Memory) = .mk true (.mk false (encode hd) 0) (encode tl) := rfl
@[simp] theorem encodeSource_idx: (encode (Source.idx hd tl):Memory) = .mk true (.mk true (encode hd) 0) (encode tl) := rfl

instance: Encoding OpInstruction.MemoryOperation Memory where
  encode
  | .COPY => 0
  | .MOVE => 1
  | .SWAP => .mk true 1 0
  encode_inj a b := by cases a <;> cases b <;> simp

instance: Encoding OpInstruction Memory where
  encode
  | .const dst val => .mk false (encode dst) (encode val)
  | .vop op dst src => .mk true (encode op) (.mk false (encode dst) (encode src))
  | .mop op dst src => .mk true (encode op) (.mk true (encode dst) (encode src))
  encode_inj a b := by
    cases a <;> cases b
    case vop.vop => simpa using λ hN hop hdst _ hsrc ↦ ⟨hN, hop, hdst, hsrc⟩
    all_goals simp

instance: Encoding BranchInstruction Memory where
  encode
  | .ifNull src => .mk false (encode src) 0
  | .ifTrue op src => .mk true (encode op) (encode src)
  encode_inj a b := by
    cases a <;> cases b
    case ifTrue.ifTrue => simpa using λ hN hcond _ hsrc ↦ ⟨hN, hcond, hsrc⟩
    all_goals simp

def encodeProgram: Program → Memory
| .exit => 0
| .op op is => .mk true (.mk false (encode op) (encodeProgram is)) 0
| .branch cond next => .mk true (.mk false (encode cond) 0) (.mk true (encodeProgram (next false)) (encodeProgram (next true)))
| .recurse dst src is => .mk true (.mk true (encode dst) (encode src)) (.mk false 0 (encodeProgram is))
| .subroutine dst src func is => .mk true (.mk true (encode dst) (encode src)) (.mk true (encodeProgram func) (encodeProgram is))

theorem encodeProgram_inj {p₀ p₁: Program}: encodeProgram p₀ = encodeProgram p₁ → p₀ = p₁ := by
  induction p₀ generalizing p₁ <;> cases p₁
  case op.op ih _ _ => simpa [encodeProgram] using λ x y ↦ ⟨x, ih y⟩
  case branch.branch nih _ _ =>
    simpa [encodeProgram] using λ hop hf ht ↦
      ⟨ hop, funext λ | false => nih _ hf | true => nih _ ht ⟩
  case subroutine.subroutine fih nih _ _ _ _ =>
    simpa [encodeProgram] using λ hdst hsrc hfunc hnext ↦ ⟨ hdst, hsrc, fih hfunc, nih hnext ⟩
  case recurse.recurse ih _ _ _ =>
    simpa [encodeProgram] using λ hdst hsrc hnext ↦ ⟨hdst, hsrc, ih hnext⟩
  all_goals simp [encodeProgram]

instance: Encoding Program Memory where
  encode := encodeProgram
  encode_inj _ _ := encodeProgram_inj

instance: Encoding Thunk Memory where
  encode
  | .mk f c s => .mk false (.mk false (encode f) (encode c)) (encode s)
  encode_inj
  | .mk _ _ _, .mk _ _ _ => by
    simpa using λ hf hc hs ↦ ⟨ hf, hc, hs ⟩

instance: Encoding Stack Memory where
  encode
  | .result m => .mk false (encode m) 0
  | .execution t cs => .mk true (encode t) (encode cs)
  encode_inj a b := by cases a <;> cases b <;> simp

end Encoding
end HMem
