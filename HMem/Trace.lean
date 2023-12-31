import HMem.Stack
import HMem.Encoding.Basic

namespace HMem
open Complexity

variable {α: Type _} [Encoding α Memory] {β: Type _} [Encoding β Memory]
variable {f: α → β}

inductive TraceElem (f: α → β) where
| branch (b: Bool)
| subroutine {γ: Type _} [Encoding γ Memory] {δ: Type _} [Encoding δ Memory] (fc: γ → δ) (arg: γ)
| recurse (arg: α)

namespace TraceElem

def matchesProgram: Program → List (TraceElem f) → Memory → Program → α → Prop
| .exit, [], m, _, a => m = (encode (f a))
| .op op is, ts, m, p, a =>
  matchesProgram is ts (op.apply m) p a
| .branch op pos _, TraceElem.branch true :: ts, m, p, a =>
  op.apply m ∧
  matchesProgram pos ts m p a
| .branch op _ neg, TraceElem.branch false :: ts, m, p, a =>
  op.apply m = false ∧
  matchesProgram neg ts m p a
| .recurse dst src is, TraceElem.recurse arg :: ts, m, p, a =>
  m.getms src = encode arg ∧ matchesProgram is ts (m.setms dst (encode (f arg))) p a
| .subroutine dst src func is, TraceElem.subroutine fc arg :: ts, m, p, a =>
  m.getms src = encode arg ∧
  func.hasResult (encode arg) (encode (fc arg)) ∧
  matchesProgram is ts (m.setms dst (encode (fc arg))) p a
| _, _, _, _, _ => False

def matchesThunk (tr: List (TraceElem f)) (t: Thunk): α → Prop :=
  matchesProgram t.current tr t.state t.function

@[simp] theorem matchesThunk_exit:
    matchesThunk (f := f) [] ⟨m, .exit, p⟩ a = (m = encode (f a)) := rfl

@[simp] theorem matchesThunk_vop {tr: List (TraceElem f)}:
    matchesThunk tr ⟨m, .op op is, p⟩ =
    matchesThunk tr ⟨op.apply m, is, p⟩ := rfl

@[simp] theorem matchesThunk_branch_pos {tr: List (TraceElem f)}:
    matchesThunk (.branch true::tr) ⟨m, .branch op pos neg, p⟩ a =
    (op.apply m = true ∧ matchesThunk tr ⟨m, pos, p⟩ a) := rfl

@[simp] theorem matchesThunk_branch_neg {tr: List (TraceElem f)}:
    matchesThunk (.branch false::tr) ⟨m, .branch op pos neg, p⟩ a =
    (op.apply m = false ∧ matchesThunk tr ⟨m, neg, p⟩ a) := rfl

@[simp] theorem matchesThunk_recurse {tr: List (TraceElem f)}:
    matchesThunk (.recurse arg::tr) ⟨m, .recurse dst src is, p⟩ a =
    (m.getms src = encode arg ∧ matchesThunk tr ⟨m.setms dst (encode (f arg)), is, p⟩ a) := by
  simp [matchesThunk, matchesProgram]

@[simp] theorem matchesThunk_subroutine {tr: List (TraceElem f)} [Encoding γ Memory] [Encoding δ Memory] {fc: γ → δ} [hc: Computable Encoding.Model fc]:
    matchesThunk (.subroutine fc arg::tr) ⟨m, .subroutine dst src (Encoding.getProgram fc) is, p⟩ a =
    (m.getms src = encode arg ∧ matchesThunk tr ⟨m.setms dst (encode (fc arg)), is, p⟩ a) := by
  simp [matchesThunk, matchesProgram]

inductive Consistent: List (TraceElem f) → List (TraceElem f) → Prop
| nil : Consistent [] []
| branch_ne {b₀ b₁: Bool} (h: b₀ ≠ b₁) (tr₀ tr₁: List (TraceElem f)):
  Consistent (branch b₀::tr₀) (branch b₁::tr₁)
| branch_eq (b: Bool) {tr₀ tr₁: List (TraceElem f)} (h: Consistent tr₀ tr₁):
  Consistent (branch b::tr₀) (branch b::tr₁)
| subroutine {γ: Type _} [Encoding γ Memory] {δ: Type _} [Encoding δ Memory]
  (fc: γ → δ) (arg₀ arg₁: γ)
  {tr₀ tr₁: List (TraceElem f)} (h: Consistent tr₀ tr₁):
  Consistent (subroutine fc arg₀::tr₀) (subroutine fc arg₁::tr₁)
| recurse (arg₀ arg₁: α) {tr₀ tr₁: List (TraceElem f)} (h: Consistent tr₀ tr₁):
  Consistent (recurse arg₀::tr₀) (recurse arg₁::tr₁)

@[simp] theorem Consistent.nil_def: Consistent (f := f) [] [] := Consistent.nil
@[simp] theorem Consistent.branch_def:
    Consistent (f := f) (.branch b₀::tr₀) (.branch b₁::tr₁) =
    (b₀ ≠ b₁ ∨ Consistent tr₀ tr₁) := eq_iff_iff.mpr ⟨ λ
      | branch_ne h _ _ => Or.inl h
      | branch_eq _ h => Or.inr h,
      (em (b₀ = b₁)).elim ( λ
        | heq, Or.inl h => absurd heq h
        | rfl, Or.inr h => branch_eq _ h
      ) ( λ h _ ↦ Consistent.branch_ne h tr₀ tr₁) ⟩
@[simp] theorem Consistent.recurse_def:
    Consistent (f := f) (.recurse arg₀::tr₀) (.recurse arg₁::tr₁) = Consistent tr₀ tr₁ := eq_iff_iff.mpr ⟨
      λ | recurse _ _ h => h,
      Consistent.recurse _ _ ⟩
@[simp] theorem Consistent.subroutine_def {γ: Type _} [Encoding γ Memory] {δ: Type _} [Encoding δ Memory] {fc: γ → δ} {arg₀ arg₁: γ}:
    Consistent (.subroutine fc arg₀::tr₀) (.subroutine fc arg₁::tr₁) = Consistent tr₀ tr₁ := eq_iff_iff.mpr ⟨
      λ | subroutine _ _ _ h => h,
      Consistent.subroutine _ _ _ ⟩

@[simp] def hasRecursiveArg: TraceElem f → α → Prop
| recurse arg, a => arg = a
| _, _ => false

attribute [local simp] matchesThunk matchesProgram

theorem matchesThunk_hasResult
    {ts: List (TraceElem f)}
    (hm: matchesThunk ts t a)
    (hrec: ∀ {arg te}, te ∈ ts → hasRecursiveArg te arg →
      Program.hasResult (Thunk.function t) (encode arg) (encode (f arg))):
    Stack.hasResult (.execution t []) (encode (f a)) := by
  cases t with | mk tstate tcurr tfunc =>
  induction tcurr generalizing tstate ts with
  | exit =>
    cases ts
    . simpa using hm
    . simp at hm
  | op _ _ ih => exact Stack.hasResult_of_step (ih _ hm hrec)
  | branch c pos neg pih nih =>
    cases ts with
    | nil => exact absurd hm not_false
    | cons te tr =>
      cases te
      case branch c =>
        cases c with
        | true => exact
          Stack.hasResult_branch_pos hm.left (pos := pos) ▸ pih _ (hm.right) (hrec ∘ List.mem_cons_of_mem _)
        | false => exact
          Stack.hasResult_branch_neg hm.left (neg := neg) ▸ nih _ (hm.right) (hrec ∘ List.mem_cons_of_mem _)
      all_goals simp at hm
  | subroutine _ _ _ _ _ ih =>
    cases ts with
    | nil => exact absurd hm not_false
    | cons te tr =>
      cases te
      case subroutine fc arg =>
        apply Stack.hasResult_subroutine
        rw [hm.left]
        apply hm.right.left
        apply ih
        apply hm.right.right
        exact (hrec ∘ List.mem_cons_of_mem _)
      all_goals simp at hm
  | recurse _ _ _ ih =>
    cases ts with
    | nil => exact absurd hm not_false
    | cons te tr =>
      cases te
      case recurse =>
        apply Stack.hasResult_recurse
        rw [hm.left]
        apply hrec
        apply List.mem_cons_self
        rfl
        apply ih
        apply hm.right
        exact (hrec ∘ List.mem_cons_of_mem _)
      all_goals simp at hm

end TraceElem

def Trace {α: Type _} {β: Type _} [Encoding α Memory] [Encoding β Memory] (f: α → β): Type _ := α → List (TraceElem f)

namespace Trace
variable {f: α → β}

@[simp] def recursiveArgOf (tr: Trace f) (a₀ a₁: α): Prop :=
  ∃ te ∈ (tr a₁), te.hasRecursiveArg a₀

structure MatchesProgram (tr: Trace f) (p: Program): Prop where
  correct: ∀ a, TraceElem.matchesThunk (tr a) ⟨encode a, p, p⟩ a
  consistent: ∀ a b, TraceElem.Consistent (tr a) (tr b)
  wellFounded: WellFounded tr.recursiveArgOf

namespace MatchesProgram

variable {tr: Trace f} {p: Program}

@[simp] theorem MatchesProgram_def:
  tr.MatchesProgram p =
  ((∀ a, TraceElem.matchesThunk (tr a) ⟨encode a, p, p⟩ a) ∧
  (∀ a b, TraceElem.Consistent (tr a) (tr b)) ∧
  WellFounded tr.recursiveArgOf) :=
  eq_iff_iff.mpr
  ⟨ λ h ↦ ⟨h.correct, h.consistent, h.wellFounded⟩,
    λ h ↦ ⟨h.left, h.right.left, h.right.right⟩ ⟩

theorem hasResult (h: MatchesProgram tr p) (a: α): p.hasResult (encode a) (encode (f a)) :=
  h.wellFounded.induction a λ _ ih ↦
    TraceElem.matchesThunk_hasResult (h.correct _)
      λ hmem hrec ↦ ih _ ⟨_, hmem, hrec⟩

end MatchesProgram

end Trace

class HasTrace (f: α → β) [Encoding α Memory] [Encoding β Memory] where
  program: Program
  trace: Trace f
  sound: trace.MatchesProgram program

end HMem
