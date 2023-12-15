import HMem.Memory
import Complexity.Basic
import Mathlib.Logic.Basic

namespace HMem
open Complexity

instance: Setoid Memory where
  r := Eq
  iseqv := eq_equivalence

instance:
    Complexity.Encoding Bool Memory where
  encode := Memory.setv 0
  inj _ _ := And.left ∘  Memory.setv_inj_iff.mp

def pathInj {v₀ v₁: θ} [Encoding θ Memory] {m₀ m₁: Memory} (p: List Bool)
    (hm: m₀ ≈ m₁) (h₀: m₀.getmp p = Encoding.encode v₀) (h₁: m₁.getmp p = Encoding.encode v₁): v₀ = v₁ :=
  Encoding.inj (Data := Memory) _ _ (h₀ ▸ h₁ ▸ congrArg₂ _ hm rfl)

-- instance [Encoding θ Memory] [Encoding φ Memory]: Encoding (θ × φ) Memory where
--   encode
--   | (a, b) => .node False (encode a) (encode b)
--   inj
--   | (_, _), (_, _), h => congrArg₂ _ (pathInj [False] h rfl rfl) (pathInj [True] h rfl rfl)

-- instance [Encoding θ Memory] [Encoding φ Memory]: Encoding (θ ⊕ φ) Memory where
--   encode
--   | Sum.inl v => .node False (encode v) .leaf
--   | Sum.inr v => .node True (encode v) .leaf
--   inj
--   | Sum.inl _, Sum.inl _, h => congrArg _ (pathInj [False] h rfl rfl)
--   | Sum.inl _, Sum.inr _, h => absurd (h []) Bool.noConfusion
--   | Sum.inr _, Sum.inl _, h => absurd (h []) Bool.noConfusion
--   | Sum.inr _, Sum.inr _, h => congrArg _ (pathInj [False] h rfl rfl)

-- def encodeList [Encoding θ Memory]: List θ → Memory
-- | [] => .leaf
-- | a::as => .node True (encode a) (encodeList as)

-- theorem encodeList_inj [Encoding θ Memory]: {lhs rhs: List θ} → encodeList lhs ≈ encodeList rhs → lhs = rhs
-- | [], [], _ => rfl
-- | [], _::_, h => absurd (h []) Bool.noConfusion
-- | _::_, [], h => absurd (h []) Bool.noConfusion
-- | _::_, _::_, h => congrArg₂ _
--   (pathInj [False] h rfl rfl)
--   (encodeList_inj (Memory.getvp_congr' [True] h rfl rfl))

-- instance [Encoding θ Memory]: Encoding (List θ) Memory where
--   encode := encodeList
--   inj _ _ := encodeList_inj

-- instance: Encoding Memory Memory where
--   encode := Memory.canonical
--   inj _ _ := by
--     intro h


end HMem
