import HMem.Memory
import HMem.Program
import Complexity.Basic
import Complexity.Asymptotic
import Mathlib.Logic.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Init.Data.Nat.Bitwise
import Lib

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
@[simp] theorem encodeBool {b: Bool}: (encode b:Memory) = .mk b 0 0 := rfl

instance: Complexity.Coding Bool Memory where
  decode m := m.getv
  decode_inv := by simp

@[simp] theorem decodeBool {m: Memory}: (decode Bool m) = some m.getv := rfl

instance [Encoding α Memory] [Encoding β Memory]: Encoding (α × β) Memory where
  encode | (a, b) => .mk false (encode a) (encode b)
  encode_inj | (_, _), (_, _) => by simp

@[simp] theorem encode_prod [Encoding α Memory] [Encoding β Memory]: {v: α × β} →
    (encode v:Memory) = .mk false (encode v.fst) (encode v.snd)
| (_, _) => rfl

instance [Coding α Memory] [Coding β Memory]: Coding (α × β) Memory where
  decode m := Option.map₂ Prod.mk (decode α (m.getm false)) (decode β (m.getm true))
  decode_inv
  | (_, _) => by simp

@[simp] theorem decode_prod [Encoding α Memory] [Encoding β Memory] {m: Memory}:
  decode (α × β) m = Option.map₂ Prod.mk (decode α (m.getm false)) (decode β (m.getm true)) := rfl

instance [Encoding α Memory] [Encoding β Memory]: Encoding (α ⊕ β) Memory where
  encode
  | Sum.inl v => .mk false (encode v) 0
  | Sum.inr v => .mk true (encode v) 0
  encode_inj x y := by cases x <;> cases y <;> simp
@[simp] theorem encode_sum_inl [Encoding α Memory] [Encoding β Memory]:
    (encode (Sum.inl a:α ⊕ β):Memory) = .mk false (encode a) 0 := rfl
@[simp] theorem encode_sum_inr [Encoding α Memory] [Encoding β Memory]:
    (encode (Sum.inr b:α ⊕ β):Memory) = .mk true (encode b) 0 := rfl
@[simp] theorem encode_sum_getm_t [Encoding α Memory] [Encoding β Memory] (v: α ⊕ β):
    Memory.getm (encode v) true = 0 := by cases v <;> simp

instance [Coding α Memory] [Coding β Memory]: Coding (α ⊕ β) Memory where
  decode m := match m.getv with
    | false => (decode α (m.getm false)).map Sum.inl
    | true => (decode β (m.getm false)).map Sum.inr
  decode_inv
  | Sum.inl _ => by simp
  | Sum.inr _ => by simp

def encodeList [Encoding α Memory]: List α → Memory
| [] => 0
| a::as => .mk true (encode a) (encodeList as)

theorem encodeList_inj [Encoding α Memory]: (lhs rhs: List α) → encodeList lhs = encodeList rhs → lhs = rhs
| [], [] => λ _ ↦ rfl
| [], _::_ => by simp[encodeList]
| _::_, [] => by simp[encodeList]
| _::lhs, _::rhs => by simp[encodeList, Iff.intro (encodeList_inj lhs rhs) λ h ↦ h ▸ rfl]

def rawDecodeList [Coding α Memory]: Tree Bool → Option (List α)
| .nil => some []
| .node false _ _ => some []
| .node true f t => Option.map₂ List.cons (decode α (Data := Memory) ⟦f⟧) (rawDecodeList t)

def decodeList [Coding α Memory]: Memory → Option (List α) := rawDecodeList ∘ Memory.out

theorem rawDecodeList_inv [Coding α Memory]: (as: List α) → decodeList (encodeList as) = some as
| [] => rfl
| _::tl => by simpa [encodeList, decodeList, rawDecodeList] using rawDecodeList_inv tl

instance [Encoding α Memory]: Encoding (List α) Memory where
  encode := encodeList
  encode_inj := encodeList_inj

instance [Coding α Memory]: Coding (List α) Memory where
  decode := decodeList
  decode_inv := rawDecodeList_inv

@[simp] theorem encode_list_nil [Encoding α Memory]: (encode ([]: List α):Memory) = 0 := rfl
@[simp] theorem encode_list_cons [Encoding α Memory] {a: α}: (encode (a::as):Memory) = .mk true (encode a) (encode as) := rfl

instance [Encoding α Memory]: Encoding (Option α) Memory where
  encode
  | .none => 0
  | .some a => .mk true (encode a) 0
  encode_inj a b := by cases a <;> cases b <;> simp

@[simp] theorem encode_option_none [Encoding α Memory]: (encode (none:Option α):Memory) = 0 := rfl
@[simp] theorem encode_option_some [Encoding α Memory] {a: α}: (encode (some a):Memory) = .mk true (encode a) 0 := rfl

instance [Coding α Memory]: Coding (Option α) Memory where
  decode m := match m.getv with
  | false => some none
  | true => Option.map some (decode α (m.getm false))
  decode_inv
  | .none => rfl
  | .some _ => by simp

instance [Encoding α Memory]: Encoding (Fin N → α) Memory where
  encode := encode ∘ List.ofFn
  encode_inj _ _ := by simp

theorem encodeFinTuple_def [Encoding α Memory] (f: Fin N → α): (encode f:Memory) = encode (List.ofFn f) := rfl
@[simp] theorem tupleInj_eq [Encoding α Memory] {N₀ N₁: ℕ} (f₀: Fin N₀ → α) (f₁: Fin N₁ → α):
    ((encode f₀:Memory) = encode f₁) = (N₀ = N₁ ∧ HEq f₀ f₁) := by
  simp [encodeFinTuple_def, List.ofFn_inj']

instance [Coding α Memory]: Coding (Fin N → α) Memory where
  decode m := Option.join ((decode (List α) m).map (List.getN N))
  decode_inv := by simp [encodeFinTuple_def]

instance: Coding Memory Memory where
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

instance {N: ℕ} [Encoding α Memory]: Encoding ((Fin N → Bool) → α) Memory where
  encode := encodeOp
  encode_inj := encodeOp_inj

def decodeOp [Coding α Memory]: {N: ℕ} → Memory → Option ((Fin N → Bool) → α)
| 0, m => Option.map (λ x _ ↦ x) (decode α (m.getm false))
| N+1, m => Option.map₂ (λ f t g ↦
    match g ⟨0, Nat.zero_lt_succ _⟩ with
    | false => f (Fin.tail g)
    | true => t (Fin.tail g))
    (decodeOp (α := α) (N:=N) (m.getm false))
    (decodeOp (α := α) (N:=N) (m.getm true))

theorem decodeOp_inv [Coding α Memory]: {N: ℕ} → (x: (Fin N → Bool) → α) →
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

instance {N: ℕ} [Coding α Memory]: Coding ((Fin N → Bool) → α) Memory where
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

theorem encode_nat_as_list: encode (α := ℕ) (Data := Memory) = encode ∘ Nat.bits := rfl

instance: Coding ℕ Memory where
  decode m := Option.map Nat.ofBits (decode (List Bool) m)
  decode_inv := by simp [encode_nat_as_list]

theorem encode_nat_def {n: ℕ}: (encode n) = Memory.mk (decide (n ≠ 0)) (encode (decide (n % 2 = 1))) (encode (n / 2)) := by
  refine Nat.binaryRec' (n := n) Memory.zero_def'.symm ?hi
  intro b n hn _
  apply Eq.trans
  apply congrArg (encode (α := List Bool))
  apply Nat.bits_append_bit _ _ hn
  apply Memory.mk_inj_iff.mpr
  apply And.intro
  exact Eq.symm (decide_eq_true λ h ↦ absurd ((Nat.bit_eq_zero.mp h).right.symm.trans (hn (Nat.bit_eq_zero.mp h).left)) Bool.noConfusion)
  cases b <;> simp [-Nat.bit_false, -Nat.bit_true, Nat.bit_mod_two, Nat.bit_div_2]
  rfl
  rfl

@[simp] theorem encode_zero: encode (0: ℕ) = (0: Memory) := rfl
@[simp] theorem encode_succ: encode ((Nat.succ n):ℕ) = Memory.mk true (encode (decide ((n + 1) % 2 = 1))) (encode ((n + 1) / 2)) :=
  encode_nat_def
@[simp] theorem encode_getm_false {n: ℕ}: Memory.getm (encode n) false = encode (decide (n % 2 = 1)) :=
  (congrArg₂ Memory.getm encode_nat_def rfl).trans Memory.getm_mk_f
@[simp] theorem encode_getm_true {n: ℕ}: Memory.getm (encode n) true = encode (n / 2) :=
  (congrArg₂ Memory.getm encode_nat_def rfl).trans Memory.getm_mk_t
@[simp] theorem encode_getv {n: ℕ}: Memory.getv (encode n) = decide (n ≠ 0) :=
  (congrArg Memory.getv encode_nat_def).trans Memory.getv_mk


def Model: Complexity.Model where
  Program := Program
  Data := Memory
  Result := Memory
  Cost := ℕ
  has_result := Program.hasResult
  has_result_isFunc h := h ▸ Program.hasResult_injOut
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

def getBound [Complexity.Encoding α Memory] [Complexity.Encoding β Memory] {f: α → β} {cf: CostFunction α ℕ} (h: Complexity Encoding.Model f cf): CostFunction α ℕ := h.cost_ale.bound
end Encoding
end HMem
