import HMem.Memory
import HMem.Stack
import Complexity.Basic
import Complexity.Asymptotic
import Mathlib.Logic.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Init.Data.Nat.Bitwise

def Nat.ofBits: List Bool → ℕ
| [] => 0
| b::bs => bit b (ofBits bs)

@[simp] theorem Nat.ofBits_inverse: (n: ℕ) → ofBits n.bits = n :=
  Nat.binaryRec' rfl λ _ _ h ih ↦
    Nat.bits_append_bit _ _ h ▸ congrArg₂ bit rfl ih

@[simp] theorem Nat.bits_injEq: (Nat.bits n = Nat.bits m) = (n = m) :=
  eq_iff_iff.mpr ⟨
    λ h ↦ Nat.ofBits_inverse n ▸ Nat.ofBits_inverse m ▸ congrArg Nat.ofBits h,
    λ h ↦ h ▸ rfl ⟩

def List.getN (N: ℕ) (as: List α): Option (Fin N → α) :=
  if h: N ≤ as.length
  then some (λ n ↦ as.get ⟨n.val, lt_of_lt_of_le n.isLt h⟩)
  else none

@[simp] theorem List.getN_ofFn {f: Fin N → α}: List.getN N (List.ofFn f) = f :=
  (dif_pos (List.length_ofFn _ ▸ le_refl _)).trans
  (congrArg some (funext λ _ ↦ get_ofFn _ _))

namespace HMem
namespace Encoding
open Complexity

instance eq_setoid: Setoid Memory where
  r := Eq
  iseqv := eq_equivalence

@[simp] theorem eq_equiv (m₀ m₁: Memory): (m₀ ≈ m₁) = (m₀ = m₁) := rfl

@[simp] theorem encodeInjEq {v₀ v₁: α} [h: Encoding α Memory]:
    ((encode v₀:Memory) = encode v₁) = (v₀ = v₁) :=
  eq_iff_iff.mpr ⟨ h.encode_inj _ _, congrArg _ ⟩

theorem pathInj {v₀ v₁: α} [Encoding α Memory] {m₀ m₁: Memory} (p: List Bool)
    (hm: m₀ ≈ m₁) (h₀: m₀.getmp p = Encoding.encode v₀) (h₁: m₁.getmp p = Encoding.encode v₁): v₀ = v₁ :=
  Encoding.encode_inj (Data := Memory) _ _ (h₀ ▸ h₁ ▸ congrArg₂ _ hm rfl)

instance: Complexity.Encoding Bool Memory where
  encode b := .mk b 0 0
  encode_inj _ _ := by simp
  decode m := m.getv
  decode_inv := by simp

@[simp] theorem encodeBool {b: Bool}: (encode b:Memory) = .mk b 0 0 := rfl
@[simp] theorem decodeBool {m: Memory}: (decode Bool m) = some m.getv := rfl

instance [Encoding α Memory] [Encoding β Memory]: Encoding (α × β) Memory where
  encode | (a, b) => .mk false (encode a) (encode b)
  encode_inj | (_, _), (_, _) => by simp
  decode m := Option.map₂ Prod.mk (decode α (m.getm false)) (decode β (m.getm true))
  decode_inv
  | (_, _) => by simp

@[simp] theorem encode_prod [Encoding α Memory] [Encoding β Memory]: {v: α × β} →
    (encode v:Memory) = .mk false (encode v.fst) (encode v.snd)
| (_, _) => rfl

@[simp] theorem decode_prod [Encoding α Memory] [Encoding β Memory] {m: Memory}:
  decode (α × β) m = Option.map₂ Prod.mk (decode α (m.getm false)) (decode β (m.getm true)) := rfl

instance [Encoding α Memory] [Encoding β Memory]: Encoding (α ⊕ β) Memory where
  encode
  | Sum.inl v => .mk false (encode v) 0
  | Sum.inr v => .mk true (encode v) 0
  encode_inj x y := by cases x <;> cases y <;> simp
  decode m := match m.getv with
    | false => (decode α (m.getm false)).map Sum.inl
    | true => (decode β (m.getm false)).map Sum.inr
  decode_inv
  | Sum.inl _ => by simp
  | Sum.inr _ => by simp

@[simp] theorem encode_sum_inl [Encoding α Memory] [Encoding β Memory]:
    (encode (Sum.inl a:α ⊕ β):Memory) = .mk false (encode a) 0 := rfl
@[simp] theorem encode_sum_inr [Encoding α Memory] [Encoding β Memory]:
    (encode (Sum.inr b:α ⊕ β):Memory) = .mk true (encode b) 0 := rfl
@[simp] theorem encode_sum_getm_t [Encoding α Memory] [Encoding β Memory] (v: α ⊕ β):
    Memory.getm (encode v) true = 0 := by cases v <;> simp

def encodeList [Encoding α Memory]: List α → Memory
| [] => 0
| a::as => .mk true (encode a) (encodeList as)

theorem encodeList_inj [Encoding α Memory]: (lhs rhs: List α) → encodeList lhs = encodeList rhs → lhs = rhs
| [], [] => λ _ ↦ rfl
| [], _::_ => by simp[encodeList]
| _::_, [] => by simp[encodeList]
| _::lhs, _::rhs => by simp[encodeList, Iff.intro (encodeList_inj lhs rhs) λ h ↦ h ▸ rfl]

def rawDecodeList [Encoding α Memory]: _Memory → Option (List α)
| .leaf => some []
| .node false _ _ => some []
| .node true f t => Option.map₂ List.cons (decode α (Data := Memory) ⟦f⟧) (rawDecodeList t)

def decodeList [Encoding α Memory]: Memory → Option (List α) := rawDecodeList ∘ Memory.out

theorem rawDecodeList_inv [Encoding α Memory]: (as: List α) → decodeList (encodeList as) = some as
| [] => rfl
| _::tl => by simpa [encodeList, decodeList, rawDecodeList] using rawDecodeList_inv tl

instance [Encoding α Memory]: Encoding (List α) Memory where
  encode := encodeList
  encode_inj := encodeList_inj
  decode := decodeList
  decode_inv := rawDecodeList_inv

@[simp] theorem encode_list_nil [Encoding α Memory]: (encode ([]: List α):Memory) = 0 := rfl
@[simp] theorem encode_list_cons [Encoding α Memory] {a :α}: (encode (a::as):Memory) = .mk true (encode a) (encode as) := rfl

instance [Encoding α Memory]: Encoding (Option α) Memory where
  encode
  | .none => 0
  | .some a => .mk true (encode a) 0
  encode_inj a b := by cases a <;> cases b <;> simp
  decode m := match m.getv with
  | false => some none
  | true => Option.map some (decode α (m.getm false))
  decode_inv
  | .none => rfl
  | .some _ => by simp

instance [Encoding α Memory]: Encoding (Fin N → α) Memory where
  encode := encode ∘ List.ofFn
  encode_inj _ _ := by simp
  decode m := Option.join ((decode (List α) m).map (List.getN N))
  decode_inv := by
    simp


theorem encodeFinTuple_def [Encoding α Memory] (f: Fin N → α): (encode f:Memory) = encode (List.ofFn f) := rfl

@[simp] theorem tupleInj_eq [Encoding α Memory] {N₀ N₁: ℕ} (f₀: Fin N₀ → α) (f₁: Fin N₁ → α):
    ((encode f₀:Memory) = encode f₁) = (N₀ = N₁ ∧ HEq f₀ f₁) := by
  simp [encodeFinTuple_def, List.ofFn_inj']

instance: Encoding Memory Memory where
  encode := id
  encode_inj _ _ := id
  decode := some ∘ id
  decode_inv _ := rfl

@[simp] theorem encode_memory (m: Memory): encode m = m := rfl
@[simp] theorem decode_memory (m: Memory): decode Memory m = some m := rfl

def encodeOp [Encoding α Memory]: {N: ℕ} → ((Fin N → Bool) → α) → Memory
| 0, f => Memory.mk false (encode (f finZeroElim)) 0
| _+1, f => Memory.mk true
  (encodeOp (f ∘ (Fin.cons (α := λ _ ↦ Bool) false)))
  (encodeOp (f ∘ (Fin.cons (α := λ _ ↦ Bool) true)))

theorem encodeOp_inj [Encoding α Memory]: {N: ℕ} → (f₀ f₁: ((Fin N) → Bool) → α) → encodeOp f₀ = encodeOp f₁ → f₀ = f₁
| 0, f₀, f₁ => by simpa [encodeOp] using λ h ↦ funext λ x ↦ Subsingleton.elim _ x ▸ h
| N+1, f₀, f₁ => by
  simpa [encodeOp,
    λ b ↦ Iff.intro
      (encodeOp_inj
        (f₀ ∘ (Fin.cons (α := λ _ ↦ Bool) b))
        (f₁ ∘ (Fin.cons (α := λ _ ↦ Bool) b)))
      (λ h ↦ h ▸ rfl)]
    using λ hf ht ↦ funext λ y ↦ Fin.cons_self_tail y ▸
      match y 0 with
      | false => congrFun hf (Fin.tail y)
      | true => congrFun ht (Fin.tail y)

def decodeOp [Encoding α Memory]: {N: ℕ} → Memory → Option ((Fin N → Bool) → α)
| 0, m => Option.map (λ x _ ↦ x) (decode α (m.getm false))
| N+1, m => Option.map₂ (λ f t g ↦
    match g ⟨0, Nat.zero_lt_succ _⟩ with
    | false => f (Fin.tail g)
    | true => t (Fin.tail g))
    (decodeOp (α := α) (N:=N) (m.getm false))
    (decodeOp (α := α) (N:=N) (m.getm true))

theorem decodeOp_inv [Encoding α Memory]: {N: ℕ} → (x: (Fin N → Bool) → α) →
    decodeOp (N := N) (encodeOp x) = some x
| 0, _ => by simpa [decodeOp, encodeOp]
  using funext λ _ ↦ congrArg _ (funext finZeroElim)
| N+1, g => by
  simp [decodeOp, encodeOp, decodeOp_inv (N := N)]
  apply funext
  intro x
  match h:x 0 with
  | true =>
    apply congrArg g
    exact h ▸ Fin.cons_self_tail _
  | false =>
    apply congrArg g
    exact h ▸ Fin.cons_self_tail _


instance {N: ℕ} [Encoding α Memory]: Encoding ((Fin N → Bool) → α) Memory where
  encode := encodeOp
  encode_inj := encodeOp_inj
  decode := decodeOp
  decode_inv := decodeOp_inv

theorem encodeOp_zeroDef [Encoding α Memory] (f: (Fin 0 → Bool) → α): (encode f:Memory) = .mk false (encode (f finZeroElim)) 0 := rfl
theorem encodeOp_succDef [Encoding α Memory] (f: (Fin (N + 1) → Bool) → α): (encode f:Memory) =
  Memory.mk true
  (encode (f ∘ (Fin.cons (α := λ _ ↦ Bool) false)))
  (encode (f ∘ (Fin.cons (α := λ _ ↦ Bool) true))) := rfl

theorem encodeOp_injN [Encoding α Memory]: {N₀ N₁: ℕ} → {f₀: ((Fin N₀) → Bool) → α} → {f₁: ((Fin N₁) → Bool) → α} →
    (encode f₀: Memory) = encode f₁ → N₀ = N₁
| 0, N₁, _, _ => by cases N₁ <;> simp [encodeOp_zeroDef, encodeOp_succDef]
| N₀+1, 0, _, _ => by simp [encodeOp_zeroDef, encodeOp_succDef]
| N₀+1, N₁+1, f₀, f₁ => by
  simpa [encodeOp_succDef] using λ _ ↦ encodeOp_injN

@[simp] theorem encodeOp_injEq [Encoding α Memory] {N₀ N₁: ℕ} {f₀: ((Fin N₀) → Bool) → α} {f₁: ((Fin N₁) → Bool) → α}:
    ((encode f₀: Memory) = encode f₁) = (N₀ = N₁ ∧ HEq f₀ f₁) :=
  eq_iff_iff.mpr ⟨
    λ h ↦ by cases (encodeOp_injN h); simp [h, ← encodeInjEq],
    λ h ↦ by cases h.left; cases h.right; rfl ⟩

instance: Encoding ℕ Memory where
  encode := encode ∘ Nat.bits
  encode_inj := by simp
  decode m := Option.map Nat.ofBits (decode (List Bool) m)
  decode_inv := by simp

def Model: Complexity.Model where
  Program := Program
  Data := Memory
  Result := Memory
  has_result := Program.hasResult
  has_result_inj h := h ▸ Program.hasResult_injOut
  cost' p _ h := p.timeCost (h.elim λ _ h ↦ h.elim λ _ h ↦ ⟨(_, _), h⟩)

@[simp] theorem data_def: Encoding.Model.Data = Memory := rfl
@[simp] theorem result_def: Encoding.Model.Result = Memory := rfl
@[simp] theorem model_has_result: Encoding.Model.has_result = Program.hasResult := rfl

instance [h: Complexity.Encoding α Memory]: Complexity.Encoding α Encoding.Model.Data := h
instance [h: Complexity.Encoding α Memory]: Complexity.Encoding α Encoding.Model.Result := h
def getProgram [Complexity.Encoding α Memory] [Complexity.Encoding β Memory] (f: α → β) [h: Computable Encoding.Model f]: Program :=
  h.program

@[simp] theorem getProgram_hasResult [Complexity.Encoding α Memory] [Complexity.Encoding β Memory] (f: α → β) [h: Complexity.Computable Encoding.Model f] (a: α):
    (getProgram f).hasResult (encode a) (encode (f a)) := h.has_result a

end Encoding

@[simp] def Program.subroutine' (dst src: Source) [Complexity.Encoding α Memory] [Complexity.Encoding β Memory] (f: α → β) [Complexity.Computable Encoding.Model f]: Program → Program :=
  subroutine dst src (Encoding.getProgram f)

end HMem
