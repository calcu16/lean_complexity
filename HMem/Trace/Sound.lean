import HMem.Trace.TracedProgram

@[simp] theorem Option.filter_none : Option.filter f none = none := rfl

@[simp] theorem Option.filter_eq_some': {x: Option α} → x.filter f = some b ↔ x = some b ∧ f b
| .none => ⟨ flip absurd Option.noConfusion, And.left ⟩
| .some b => by simpa [Option.filter, And.comm (a := Eq b _)] using λ heq ↦ heq ▸ ⟨id, id⟩

theorem Option.forall_mem_filter {f : α → Bool} {o : Option α} {p : α → Prop} :
  (∀ y ∈ o.filter f, p y) ↔ ∀ x ∈ o, f x → p x := by simp

theorem Option.mem_filter_of_mem {f : α → Bool} {o : Option α}
    (hmem: x ∈ o) (hf: f x): x ∈ o.filter f := Option.filter_eq_some'.mpr ⟨hmem, hf⟩

theorem Option.forall_mem_bind {f : α → Option β} {o : Option α} {p : β → Prop}:
  (∀ y ∈ Option.bind o f, p y) ↔ ∀ x ∈ o, ∀ y ∈ f x, p y := by
    simpa using ⟨ λ h _ hx _ ↦ h _ _ hx, λ h _ _ hx ↦ h _ hx _ ⟩

theorem Option.mem_bind_of_mem {f : α → Option β} {o : Option α}
    (ha: a ∈ o) (hf: b ∈ f a): b ∈ o.bind f := (congrArg₂ _ ha rfl).trans hf

namespace HMem
variable {α: Type _} [Complexity.Encoding α Memory] {β: Type _} [Complexity.Encoding β Memory] {f: α → β}

namespace Trace.TracedProgram

section
variable {γ: Type _} {δ: Type _} [enγ: Complexity.Encoding γ Memory] [enδ: Complexity.Encoding δ Memory] {fs: γ → δ} [hc: Complexity.Computable Encoding.Model fs]

def sound (f: α → β) (size: α → ℕ) (a: α): TracedProgram → Memory → Prop
| exit, m => m = Complexity.encode (f a)
| op inst next, m => next.sound f size a (inst.apply m)
| branch inst next, m => (next (inst.apply m)).sound f size a m
| subroutine dst src func next, m =>
  ∃ arg,
    m.getms src = Complexity.encode arg ∧
    next.sound f size a (m.setms dst (Complexity.encode (func arg)))
| recurse dst src next, m =>
  ∃ arg,
    m.getms src = Complexity.encode arg ∧
    size arg < size a ∧
    next.sound f size a (m.setms dst (Complexity.encode (f arg)))

def sound' (f: α → β) (size: α → ℕ): TracedProgram → (α → Option Memory) → Prop
| exit, fm => ∀ a, ∀ m ∈ (fm a), m = Complexity.encode (f a)
| op inst next, fm => next.sound' f size (Option.map inst.apply ∘ fm)
| branch inst next, fm =>
  (next true).sound' f size (Option.filter inst.apply ∘ fm) ∧
  (next false).sound' f size (Option.filter (Bool.not ∘ inst.apply) ∘ fm)
| subroutine' dst src enγ _ fs _ next, fm =>
  (∀ a, ∀ m ∈ (fm a), ∃ (hm: Option.isSome (Complexity.decode (en := enγ) (m.getms src))), m.getms src = Complexity.encode (Option.get _ hm)) ∧
  next.sound' f size (flip Option.bind
    (λ m ↦ (Complexity.decode _ (m.getms src)).map
      (m.setms dst ∘ Complexity.encode ∘ fs)) ∘
    fm)
| recurse dst src next, fm =>
  (∀ a, ∀ m ∈ (fm a), ∃ (hm: Option.isSome (Complexity.decode α (m.getms src))), m.getms src = Complexity.encode (Option.get _ hm)) ∧
  (∀ a, ∀ m ∈ (fm a), ∃ arg ∈ Complexity.decode α (m.getms src), size arg < size a) ∧
  next.sound' f size (flip Option.bind
    (λ m ↦ (Complexity.decode α (m.getms src)).map
      (m.setms dst ∘ Complexity.encode ∘ f)) ∘
    fm)
end

variable {γ: Type _} {δ: Type _} [enγ: Complexity.Encoding γ Memory] [enδ: Complexity.Encoding δ Memory] {fs: γ → δ} {hc: Complexity.Computable Encoding.Model fs}

theorem sound_branch_eq (h: inst.apply m = b):
    sound f size a (branch inst next) m = sound f size a (next b) m := h ▸ rfl

theorem sound_subroutine_some (h: sound f size a (subroutine dst src fs next) m):
    Option.isSome (Complexity.decode γ (m.getms src)) :=
  h.elim λ | arg, ⟨h, _⟩ => h ▸ Complexity.decode_inv arg (Data := Memory) ▸ rfl

theorem sound_recurse_some (h: sound f size a (recurse dst src next) m):
    Option.isSome (Complexity.decode α (m.getms src)) :=
  h.elim λ | arg, ⟨h, _, _⟩ => h ▸ Complexity.decode_inv arg (Data := Memory) ▸ rfl

@[simp] theorem sound_exit: (sound f size a exit m) = (m = Complexity.encode (f a)) := rfl
@[simp] theorem sound_op: (sound f size a (op inst next) m) = (next.sound f size a (inst.apply m)) := rfl
theorem sound_op_next: sound f size a (op inst next) m → next.sound f size a (inst.apply m) := id
@[simp] theorem sound_branch: (sound f size a (branch inst next) m) = ((next (inst.apply m)).sound f size a m) := rfl
theorem sound_branch_next: sound f size a (branch inst next) m → (next (inst.apply m)).sound f size a m := id
@[simp] theorem sound_subroutine: (sound f size a (subroutine dst src fs next) m) = (∃ arg,
    Complexity.decode γ (m.getms src) = some arg ∧
    m.getms src = Complexity.encode arg ∧
    next.sound f size a (m.setms dst (Complexity.encode (fs arg)))) :=
  iff_iff_eq.mp (exists_congr λ _ ↦ ⟨ λ h ↦ ⟨ h.left ▸ Complexity.decode_inv _, h ⟩, And.right ⟩)
theorem sound_subroutine_arg (h: sound f size a (subroutine dst src fs next) m):
    m.getms src = Complexity.encode (Option.get _ (sound_subroutine_some h)) :=
  h.elim λ | _, ⟨hm, _⟩ => by simp only [hm, Complexity.decode_inv, Option.get_some]
theorem sound_subroutine_next (h: sound f size a (subroutine dst src fs next) m):
    next.sound f size a (m.setms dst (Complexity.encode (fs (Option.get _ (sound_subroutine_some h))))) :=
  h.elim λ | _, ⟨hm, h⟩ => by simpa only [hm, Complexity.decode_inv, Option.get_some] using h

@[simp] theorem sound_recurse: (sound f size a (recurse dst src next) m) = (∃ arg,
    Complexity.decode α (m.getms src) = some arg ∧
    m.getms src = Complexity.encode arg ∧
    size arg < size a ∧
    next.sound f size a (m.setms dst (Complexity.encode (f arg)))) :=
  iff_iff_eq.mp (exists_congr λ _ ↦ ⟨ λ h ↦ ⟨ h.left ▸ Complexity.decode_inv _, h ⟩, And.right ⟩)
theorem sound_recurse_arg (h: sound f size a (recurse dst src next) m):
    m.getms src = Complexity.encode (Option.get _ (sound_recurse_some h)) :=
  h.elim λ | _, ⟨hm, _, _⟩ => by simp only [hm, Complexity.decode_inv, Option.get_some]
theorem sound_recurse_size (h: sound f size a (recurse dst src next) m):
    size (Option.get _ (sound_recurse_some h)) < size a :=
  h.elim λ | _, ⟨hm, hs, _⟩ => by simpa only [hm, Complexity.decode_inv, Option.get_some] using hs
theorem sound_recurse_next (h: sound f size a (recurse dst src next) m):
    next.sound f size a (m.setms dst (Complexity.encode (f (Option.get _ (sound_recurse_some h))))) :=
  h.elim λ | _, ⟨hm, _, h⟩ => by simpa only [hm, Complexity.decode_inv, Option.get_some] using h

theorem hasResultInternal
    {size: α → ℕ}
    {a: α}
    {tp: TracedProgram}
    (ih: ∀ arg, size arg < size a →
      tp.toProgram.hasResult (Complexity.encode arg) (Complexity.encode (f arg))):
    {current: TracedProgram} →
    {m: Memory} →
    (h: sound f size a current m) →
    Stack.hasResult (.execution ⟨m, current.toProgram, tp.toProgram⟩ []) (Complexity.encode (f a))
| .exit, _, h => ⟨1, congrArg Stack.result h⟩
| .op _ _, _, h => Stack.hasResult_of_step (hasResultInternal ih h)
| .branch _ _, _, h => Stack.hasResult_of_step (hasResultInternal ih h)
| .subroutine' _ _ _ _ _ hc _, _, h => h.elim λ
  | _, ⟨hm, h⟩ => Stack.hasResult_subroutine
    (hm.symm ▸ hc.has_result _)
    (hasResultInternal ih h)
| .recurse _ _ _, _, h => h.elim λ
  | _, ⟨hm, hsize, h⟩ => Stack.hasResult_recurse
    (hm.symm ▸ ih _ hsize)
    (hasResultInternal ih h)

theorem sound'_op_next:
    sound' f size (.op inst next) fm → sound' f size next (Option.map inst.apply ∘ fm) := id

theorem sound'_branch_next_true:
    sound' f size (.branch inst next) fm →
      (next true).sound' f size (Option.filter inst.apply ∘ fm) := And.left

theorem sound'_branch_next_false:
    sound' f size (.branch inst next) fm →
  (next false).sound' f size (Option.filter (Bool.not ∘ inst.apply) ∘ fm) := And.right

theorem sound'_branch_next_true':
    {b: Bool} → b = true → sound' f size (.branch inst next) fm →
  (next b).sound' f size (Option.filter inst.apply ∘ fm)
| _, rfl => sound'_branch_next_true

theorem sound'_branch_next_false':
    {b: Bool} → b = false → sound' f size (.branch inst next) fm →
  (next b).sound' f size (Option.filter (Bool.not ∘ inst.apply) ∘ fm)
| _, rfl => sound'_branch_next_false

@[simp] def sound'_subroutine_arg (_: sound' f size (.subroutine dst src fs next) fm): α → Option γ :=
  flip Option.bind (Complexity.decode _ ∘ flip Memory.getms src) ∘ fm

theorem sound_subroutine_mem_arg (h: sound' f size (subroutine dst src fs next) fm):
    ∀ a, ∀ m ∈ fm a, m.getms src ∈ Option.map Complexity.encode (sound'_subroutine_arg h a) :=
  λ _ _ hm ↦ (h.left _ _ hm).elim λ _ heq ↦
    heq ▸ Option.mem_map_of_mem _
      (Option.mem_bind_of_mem hm (Option.get_mem _))

theorem sound'_subroutine_next:
    sound' f size (.subroutine dst src fs next) fm →
    sound' f size next (flip Option.bind
      (λ m ↦ (Complexity.decode _ (m.getms src)).map
        (m.setms dst ∘ Complexity.encode ∘ fs)) ∘
      fm) := And.right

@[simp] def sound'_recurse_arg (_: sound' f size (.recurse dst src next) fm): α → Option α :=
    flip Option.bind (Complexity.decode _ ∘ flip Memory.getms src) ∘ fm

theorem sound'_recurse_next:
    sound' f size (.recurse dst src next) fm →
    sound' f size next (flip Option.bind
      (λ m ↦ (Complexity.decode _ (m.getms src)).map
        (m.setms dst ∘ Complexity.encode ∘ f)) ∘
      fm) := And.right ∘ And.right

theorem sound'_of_sound: {tp: TracedProgram} → {fm: α → Option Memory} →
    (∀ a, ∀ m ∈ (fm a), sound f size a tp m) → sound' f size tp fm
| .exit, _, h => h
| .op _ next, _, h => sound'_of_sound (tp := next) (λ _ ↦ Option.forall_mem_map.mpr (h _))
| .branch _ _, _, h => ⟨
    sound'_of_sound λ _ ↦
      Option.forall_mem_filter.mpr λ _ hm ht ↦
        ht ▸ h _ _ hm,
    sound'_of_sound λ _ ↦
      Option.forall_mem_filter.mpr λ _ hm hf ↦
        (Bool.not_not _).symm.trans ((congrArg Bool.not hf).trans Bool.not_true) ▸
          h _ _ hm⟩
| .subroutine' _ _ _ _ _ _ _, _, h =>
  ⟨ λ _ _ hm ↦ ⟨_, sound_subroutine_arg (h _ _ hm)⟩,
    sound'_of_sound λ _ ↦
      Option.forall_mem_bind.mpr λ _ hm ↦
        Option.forall_mem_map.mpr λ _ hc ↦
          Option.get_of_mem _ hc ▸
          sound_subroutine_next (h _ _ hm) ⟩
| .recurse _ _ _, _, h =>
  ⟨ λ _ _ hm ↦ ⟨_, sound_recurse_arg (h _ _ hm)⟩,
    λ _ _ hm ↦ ⟨_, Option.get_mem _, sound_recurse_size (h _ _ hm)⟩,
    sound'_of_sound λ _ ↦
      Option.forall_mem_bind.mpr λ _ hm ↦
        Option.forall_mem_map.mpr λ _ hc ↦
          Option.get_of_mem _ hc ▸
          sound_recurse_next (h _ _ hm) ⟩

theorem sound_of_sound': {tp: TracedProgram} → {fm: α → Option Memory} →
    sound' f size tp fm → ∀ a, ∀ m ∈ (fm a), sound f size a tp m
| .exit, _, h, _, _, hm => h _ _ hm
| .op _ next, _, h, _, _, hm =>
  sound_of_sound' (tp := next) h _ _
    (Option.mem_map_of_mem _ hm)
| .branch inst _, _, h, _, m, hm =>
  match hb:inst.apply m with
  | true => sound_branch_eq (f := f) hb ▸
    sound_of_sound' h.left _ _
      (Option.mem_filter_of_mem hm hb)
  | false => sound_branch_eq (f := f) hb ▸
    sound_of_sound' h.right _ _
      (Option.mem_filter_of_mem hm (congrArg Bool.not hb))
| .subroutine' _ _ _ _ _ _ _, _, h, a, m, hm =>
  (h.left a m hm).elim λ _ harg ↦
    ⟨_, harg,
      sound_of_sound' h.right _ _
        (Option.mem_bind_of_mem hm
          (Option.mem_map_of_mem _ (Option.get_mem _)))⟩
| .recurse _ _ _, _, h, a, m, hm =>
  (h.left a m hm).elim λ _ harg ↦
    ⟨_, harg,
      (h.right.left a m hm).elim λ _ hr ↦
        lt_of_eq_of_lt (congrArg _ (Option.get_of_mem _ hr.left)) hr.right,
      sound_of_sound' h.right.right _ _
        (Option.mem_bind_of_mem hm
          (Option.mem_map_of_mem _ (Option.get_mem _)))⟩

end Trace.TracedProgram

namespace Program

def sound (p: Program) [Trace.HasTracedProgram p] (f: α → β) (size: α → ℕ): Prop := ∀ a, p.traced.sound f size a (Complexity.encode a)

theorem hasResult_of_soundHelper {p: Program} [Trace.HasTracedProgram p] {size: α → ℕ} (h: p.sound f size) (n: ℕ):
    ∀ a, n = size a → p.hasResult (Complexity.encode a) (Complexity.encode (f a)) :=
  p.tracedMatches ▸ n.strong_induction_on λ _ ih _ ha ↦
    p.traced.hasResultInternal
      (λ _ harg ↦ p.tracedMatches.symm ▸ ih _ (ha ▸ harg) _ rfl)
      (h _)

theorem hasResult_of_sound {p: Program} [Trace.HasTracedProgram p] {size: α → ℕ} (h: p.sound f size) (a: α):
    p.hasResult (Complexity.encode a) (Complexity.encode (f a)) :=
  p.hasResult_of_soundHelper h _ a rfl


theorem halts_of_sound {p: Program} [Trace.HasTracedProgram p] {size: α → ℕ} (h: p.sound f size) (a: α):
    p.haltsOn (Complexity.encode a) :=
  (p.hasResult_of_sound h a).elim λ _ hm => ⟨(_, _), hm⟩


def timeCost' (p: Program) [Trace.HasTracedProgram p] (h: p.sound f sz): Complexity.CostFunction α ℕ :=
  λ a ↦ p.timeCost (p.halts_of_sound h a)

class HasTrace (f: α → β) where
  program: List (Program → Program)
  [hasTracedProgram: Trace.HasTracedProgram (Program.build program)]
  size: α → ℕ
  sound: (Program.build program).sound f size

instance [tr: HasTrace f]: Trace.HasTracedProgram (Program.build tr.program) := tr.hasTracedProgram

instance {α: Type _} [Complexity.Encoding α Memory] {β: Type _} [Complexity.Encoding β Memory] {f: α → β} [tr: HasTrace f]: Complexity.Computable Encoding.Model f where
  program := .build tr.program
  has_result := Program.hasResult_of_sound tr.sound

end Program
end HMem
