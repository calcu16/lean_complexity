import HMem.Stack
import HMem.Computability.Basic

namespace HMem
open Complexity

variable {α: Type _} [Encoding α Memory] {β: Type _} [Encoding β Memory]
variable {f: α → β}

inductive TraceElem (f: α → β) where
| branch (b: Bool)
| call {γ: Type _} [Encoding γ Memory] {δ: Type _} [Encoding δ Memory] (fc: γ → δ) (arg: γ)
| recurse (arg: α)

namespace TraceElem

def matchesThunk: List (TraceElem f) → Thunk → α → Prop
| [], ⟨m, [], _⟩, a => m = (encode (f a))
| TraceElem.recurse arg :: ts, ⟨m, .recurse dst src::is, p⟩, a =>
  m.getms src = encode arg ∧ matchesThunk ts ⟨m.setms dst (encode (f arg)), is, p⟩ a
| ts, ⟨m, .vop op dst src::is, p⟩, a =>
  matchesThunk ts ⟨m.setvs dst (op (m.getvs ∘ src)), is, p⟩ a
| ts, ⟨m, .mop op dst src::is, p⟩, a =>
  matchesThunk ts ⟨(m.setms src (m.mop op src dst)).setms dst (m.getms src), is, p⟩ a
| ts, ⟨m, .clear dst::is, p⟩, a =>
  matchesThunk ts ⟨m.setms dst 0, is, p⟩ a
| TraceElem.call fc arg :: ts, ⟨m, .call dst src func::is, p⟩, a =>
  m.getms src = encode arg ∧
  Program.hasResult func (encode arg) (encode (fc arg)) ∧
  matchesThunk ts ⟨m.setms dst (encode (fc arg)), is, p⟩ a
| TraceElem.branch b :: ts, ⟨m, .branch cond src is'::is, p⟩, a =>
  cond (m.getvs ∘ src) = b ∧ matchesThunk ts ⟨m, ite b is' is , p⟩ a
| _, _, _ => False
termination_by _ ts t _ => (ts.length, List.length t.current)

def consistent: List (TraceElem f) → List (TraceElem f) → Prop
| [], [] => True
| branch b₀::tr₀, branch b₁::tr₁ => b₀ ≠ b₁ ∨ consistent tr₀ tr₁
| te₀::tr₀, te₁::tr₁ => te₀ = te₁ ∧ consistent tr₀ tr₁
| _, _ => False

def hasRecursiveArg: TraceElem f → α → Prop
| recurse arg, a => arg = a
| _, _ => false

theorem matchesThunk_hasResult
    {ts: List (TraceElem f)}
    (hm: matchesThunk ts t a)
    (hrec: ∀ {arg te}, te ∈ ts → hasRecursiveArg te arg →
      Program.hasResult (Thunk.function t) (encode arg) (encode (f arg))):
    Stack.hasResult (.execution t []) (encode (f a)) := by
  cases t with | mk tstate tcurr tfunc =>
  induction tcurr generalizing tstate ts with
  | nil => cases ts with
    | nil => simpa using hm
    | cons => simp [matchesThunk] at hm
  | cons i is ih =>
    cases i
    case recurse =>
      cases ts with
      | nil => exact absurd hm not_false
      | cons te tr =>
        cases te
        case recurse =>
          apply Stack.hasResult_recurse
          simp only [hm.left]
          apply hrec (List.mem_cons_self _ _) rfl
          apply ih
          apply hm.right
          intro arg te hte htea
          apply hrec
          exact List.mem_cons_of_mem _ hte
          apply htea
        exact absurd hm not_false
        exact absurd hm not_false
    case call =>
      cases ts with
      | nil => exact absurd hm not_false
      | cons te tr =>
        cases te
        case call =>
          unfold matchesThunk at hm
          apply Stack.hasResult_call
        exact absurd hm not_false
        exact absurd hm not_false
    case branch =>
      cases ts with
      | nil => exact absurd hm not_false
      | cons te tr =>
        cases te
        case branch => sorry
        exact absurd hm not_false
        exact absurd hm not_false
    sorry
    sorry
    sorry

end TraceElem

def Trace {α: Type _} {β: Type _} [Encoding α Memory] [Encoding β Memory] (f: α → β): Type _ := α → List (TraceElem f)

namespace Trace
variable {f: α → β}

def recursiveArgOf (tr: Trace f) (a₀ a₁: α): Prop :=
  ∃ te ∈ (tr a₁), te.hasRecursiveArg a₀

structure MatchesProgram (tr: Trace f) (p: Program) where
  correct: ∀ a, TraceElem.matchesThunk (tr a) ⟨encode a, p, p⟩ a
  consistent: ∀ a b, TraceElem.consistent (tr a) (tr b)
  wellFounded: WellFounded tr.recursiveArgOf

namespace MatchesProgram

variable {tr: Trace f} {p: Program}

theorem halts (h: MatchesProgram tr p) (a: α): p.haltsOn (encode a) := by
  apply h.wellFounded.induction a
  intro x h




end MatchesProgram
end Trace

end HMem
