import HMem.Trace.TracedProgram

def Option.Forall (P: α → Prop): Option α → Prop
| some a => P a
| none => True

theorem Option.Forall_imp: {o: Option α} → Option.Forall P o → (∀ a, P a → Q a) → Option.Forall Q o
| some _, hP, h => h _ hP
| none, _, _ => trivial

theorem Option.Forall_forall: {o: Option α} → (∀ a, o = some a → P a) → Option.Forall P o
| some _, h => h _ rfl
| none, _ => trivial

theorem Option.Forall_map: {o: Option α} → Option.Forall P (Option.map f o) = Option.Forall (P ∘ f) o
| some _ => rfl
| none => rfl

theorem Option.Forall_bind: {o: Option α} → Option.Forall P (Option.bind o f) = Option.Forall (Option.Forall P ∘ f) o
| some _ => rfl
| none => rfl

theorem Option.Forall_filter: {o: Option α} → Option.Forall P (Option.filter f o) = Option.Forall (λ a ↦ f a → P a) o
| some a => if h:f a
  then (congrArg (Forall P) (if_pos h)).trans (iff_iff_eq.mp ⟨ λ hf _ ↦ hf, λ hf ↦ hf h ⟩)
  else (congrArg (Forall P) (if_neg h)).trans (eq_true (flip absurd h)).symm
| none => rfl

theorem Option.Forall_some_eq (h: o = Option.some a): Option.Forall P o = P a := h ▸ rfl
theorem Option.Forall_of_some (h: o = Option.some a): Option.Forall P o → P a := Forall_some_eq h ▸ id
theorem Option.Forall_some (h: o = Option.some a): P a → Option.Forall P o := Forall_some_eq h ▸ id
theorem Option.Forall_isSome: {o: Option α} → (h: Option.isSome o) → P (o.get h) → Option.Forall P o
| some _, _ => id
| none, h => absurd h Bool.noConfusion

theorem Option.Forall_none (h: o = none): Option.Forall P o := h ▸ trivial

def Option.Exists (P: α → Prop): Option α → Prop
| some a => P a
| none => False


def Option.Exists_of_isSome: {o: Option α} → (hs: o.isSome) → P (o.get hs) → Option.Exists P o
| some _, _, hP => hP
| none, hs, _ => absurd hs Bool.noConfusion

def Option.Exists_isSome: {o: Option α} → (hs: o.isSome) → Option.Exists P o → P (o.get hs)
| some _, _, hP => hP
| none, hs, _ => absurd hs Bool.noConfusion

namespace HMem.Trace

namespace TracedProgram
variable {α: Type _} [Complexity.Encoding α Memory] {β: Type _} [Complexity.Encoding β Memory] {f: α → β}
variable {γ: Type _} {δ: Type _} [enγ: Complexity.Encoding γ Memory] [enδ: Complexity.Encoding δ Memory] {fs: γ → δ} [hc: Complexity Encoding.Model fs]
def soundInternal (size: α → ℕ) (a: α): TracedProgram f → Memory → Prop
| exit, m => m = Complexity.encode (f a)
| op inst next, m => next.soundInternal size a (inst.apply m)
| branch inst next, m => (next (inst.apply m)).soundInternal size a m
| subroutine dst src func next, m =>
  ∃ arg,
    m.getms src = Complexity.encode arg ∧
    next.soundInternal size a (m.setms dst (Complexity.encode (func arg)))
| recurse dst src next, m =>
  ∃ arg,
    m.getms src = Complexity.encode arg ∧
    size arg < size a ∧
    next.soundInternal size a (m.setms dst (Complexity.encode (f arg)))

@[simp] def sound (tp: TracedProgram f) (size: α → ℕ): Prop := ∀ a, tp.soundInternal size a (Complexity.encode a)

theorem soundInternal_branch_eq (h: inst.apply m = b):
    soundInternal size a (branch (f := f) inst next) m = soundInternal size a (next b) m := h ▸ rfl

theorem soundInternal_subroutine_some (h: soundInternal size a (subroutine (f := f) dst src fs next) m):
    Option.isSome (Complexity.decode γ (m.getms src)) :=
  h.elim λ | arg, ⟨h, _⟩ => h ▸ Complexity.decode_inv arg (Data := Memory) ▸ rfl

theorem soundInternal_recurse_some (h: soundInternal size a (recurse (f := f) dst src next) m):
    Option.isSome (Complexity.decode α (m.getms src)) :=
  h.elim λ | arg, ⟨h, _, _⟩ => h ▸ Complexity.decode_inv arg (Data := Memory) ▸ rfl

@[simp] theorem soundInternal_exit: (soundInternal size a (exit (f := f)) m) = (m = Complexity.encode (f a)) := rfl
@[simp] theorem soundInternal_op: (soundInternal size a (op (f := f) inst next) m) = (next.soundInternal size a (inst.apply m)) := rfl
theorem soundInternal_op_next: soundInternal size a (op (f := f) inst next) m → next.soundInternal size a (inst.apply m) := id
@[simp] theorem soundInternal_branch: (soundInternal size a (branch (f := f) inst next) m) = ((next (inst.apply m)).soundInternal size a m) := rfl
theorem soundInternal_branch_next: soundInternal size a (branch (f := f) inst next) m → (next (inst.apply m)).soundInternal size a m := id
@[simp] theorem soundInternal_subroutine: (soundInternal size a (subroutine (f := f) dst src fs next) m) = (∃ arg,
    Complexity.decode γ (m.getms src) = some arg ∧
    m.getms src = Complexity.encode arg ∧
    next.soundInternal size a (m.setms dst (Complexity.encode (fs arg)))) :=
  iff_iff_eq.mp (exists_congr λ _ ↦ ⟨ λ h ↦ ⟨ h.left ▸ Complexity.decode_inv _, h ⟩, And.right ⟩)
theorem soundInternal_subroutine_arg (h: soundInternal size a (subroutine (f := f) dst src fs next) m):
    m.getms src = Complexity.encode (Option.get _ (soundInternal_subroutine_some h)) :=
  h.elim λ | _, ⟨hm, _⟩ => by simp only [hm, Complexity.decode_inv, Option.get_some]
theorem soundInternal_subroutine_next (h: soundInternal size a (subroutine (f := f) dst src fs next) m):
    next.soundInternal size a (m.setms dst (Complexity.encode (fs (Option.get _ (soundInternal_subroutine_some h))))) :=
  h.elim λ | _, ⟨hm, h⟩ => by simpa only [hm, Complexity.decode_inv, Option.get_some] using h

@[simp] theorem soundInternal_recurse: (soundInternal size a (recurse (f := f) dst src next) m) = (∃ arg,
    Complexity.decode α (m.getms src) = some arg ∧
    m.getms src = Complexity.encode arg ∧
    size arg < size a ∧
    next.soundInternal size a (m.setms dst (Complexity.encode (f arg)))) :=
  iff_iff_eq.mp (exists_congr λ _ ↦ ⟨ λ h ↦ ⟨ h.left ▸ Complexity.decode_inv _, h ⟩, And.right ⟩)
theorem soundInternal_recurse_arg (h: soundInternal size a (recurse (f := f) dst src next) m):
    m.getms src = Complexity.encode (Option.get _ (soundInternal_recurse_some h)) :=
  h.elim λ | _, ⟨hm, _, _⟩ => by simp only [hm, Complexity.decode_inv, Option.get_some]
theorem soundInternal_recurse_size (h: soundInternal size a (recurse (f := f) dst src next) m):
    size (Option.get _ (soundInternal_recurse_some h)) < size a :=
  h.elim λ | _, ⟨hm, hs, _⟩ => by simpa only [hm, Complexity.decode_inv, Option.get_some] using hs
theorem soundInternal_recurse_next (h: soundInternal size a (recurse (f := f) dst src next) m):
    next.soundInternal size a (m.setms dst (Complexity.encode (f (Option.get _ (soundInternal_recurse_some h))))) :=
  h.elim λ | _, ⟨hm, _, h⟩ => by simpa only [hm, Complexity.decode_inv, Option.get_some] using h

theorem hasResultInternal
    {size: α → ℕ}
    {a: α}
    {tp: TracedProgram f}
    (ih: ∀ arg, size arg < size a →
      tp.toProgram.hasResult (Complexity.encode arg) (Complexity.encode (f arg))):
    {current: TracedProgram f} →
    {m: Memory} →
    (h: soundInternal size a current m) →
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

theorem hasResultHelper
    {tp: TracedProgram f} {size: α → ℕ} (h: tp.sound size) (n: ℕ):
    ∀ a, n = size a → tp.toProgram.hasResult (Complexity.encode a) (Complexity.encode (f a)) :=
  n.strong_induction_on λ _ ih _ ha ↦
    hasResultInternal
      (λ _ harg ↦ ih _ (ha ▸ harg) _ rfl)
      (h _)

theorem hasResult {tp: TracedProgram f} {size: α → ℕ} (h: tp.sound size) (a: α):
    tp.toProgram.hasResult (Complexity.encode a) (Complexity.encode (f a)) :=
  hasResultHelper h _ a rfl

theorem halts {tp: TracedProgram f} {size: α → ℕ} (h: tp.sound size) (a: α):
    tp.toProgram.haltsOn (Complexity.encode a) :=
  (hasResult h a).elim λ _ hm => ⟨(_, _), hm⟩

def soundInternal' (size: α → ℕ): TracedProgram f → (α → Option Memory) → Prop
| exit, fm => ∀ a, (fm a).Forall (λ m ↦ m = Complexity.encode (f a))
| op inst next, fm => next.soundInternal' size (Option.map inst.apply ∘ fm)
| branch inst next, fm =>
  (next true).soundInternal' size (Option.filter inst.apply ∘ fm) ∧
  (next false).soundInternal' size (Option.filter (Bool.not ∘ inst.apply) ∘ fm)
| subroutine' dst src enγ _ fs _ next, fm =>
  (∀ a, (fm a).Forall (λ m ↦ ∃ (hm: Option.isSome (Complexity.decode (en := enγ) (m.getms src))), m.getms src = Complexity.encode (Option.get _ hm))) ∧
  next.soundInternal' size (flip Option.bind
    (λ m ↦ (Complexity.decode _ (m.getms src)).map
      (m.setms dst ∘ Complexity.encode ∘ fs)) ∘
    fm)
| recurse dst src next, fm =>
  (∀ a, (fm a).Forall (λ m ↦ ∃ (hm: Option.isSome (Complexity.decode α (m.getms src))), m.getms src = Complexity.encode (Option.get _ hm))) ∧
  (∀ a, (fm a).Forall (λ m ↦ (Complexity.decode α (m.getms src)).Exists (λ arg ↦ size arg < size a))) ∧
  next.soundInternal' size (flip Option.bind
    (λ m ↦ (Complexity.decode α (m.getms src)).map
      (m.setms dst ∘ Complexity.encode ∘ f)) ∘
    fm)

theorem soundInternal'_op_next:
    soundInternal' size (.op (f := f) inst next) fm → soundInternal' size next (Option.map inst.apply ∘ fm) := id

theorem soundInternal'_branch_next_true:
    soundInternal' size (.branch (f := f) inst next) fm →
      (next true).soundInternal' size (Option.filter inst.apply ∘ fm) := And.left

theorem soundInternal'_branch_next_false:
    soundInternal' size (.branch (f := f) inst next) fm →
  (next false).soundInternal' size (Option.filter (Bool.not ∘ inst.apply) ∘ fm) := And.right

@[simp] def soundInternal'_subroutine_arg (_: soundInternal' size (.subroutine (f := f) dst src fs next) fm): α → Option γ :=
  flip Option.bind (Complexity.decode _ ∘ flip Memory.getms src) ∘ fm

theorem soundInternal'_subroutine_next:
    soundInternal' size (.subroutine (f := f) dst src fs next) fm →
    soundInternal' size next (flip Option.bind
      (λ m ↦ (Complexity.decode _ (m.getms src)).map
        (m.setms dst ∘ Complexity.encode ∘ fs)) ∘
      fm) := And.right

@[simp] def soundInternal'_recurse_arg (_: soundInternal' size (.recurse (f := f) dst src next) fm): α → Option α :=
    flip Option.bind (Complexity.decode _ ∘ flip Memory.getms src) ∘ fm

theorem soundInternal'_recurse_next:
    soundInternal' size (.recurse (f := f) dst src next) fm →
    soundInternal' size next (flip Option.bind
      (λ m ↦ (Complexity.decode _ (m.getms src)).map
        (m.setms dst ∘ Complexity.encode ∘ f)) ∘
      fm) := And.right ∘ And.right

theorem soundInternal'_of_soundInternal: {tp: TracedProgram f} → {fm: α → Option Memory} →
    (∀ a, (fm a).Forall (soundInternal size a tp)) → soundInternal' size tp fm
| .exit, _, h => h
| .op _ next, _, h =>
  soundInternal'_of_soundInternal (tp := next)
    λ _ ↦ Option.Forall_map.symm ▸ h _
| .branch _ _, _, h => ⟨
    soundInternal'_of_soundInternal λ _ ↦
      Option.Forall_filter ▸
      Option.Forall_imp (h _) ( λ _ h heq ↦ heq ▸ h),
    soundInternal'_of_soundInternal λ _ ↦
      Option.Forall_filter ▸
      Option.Forall_imp (h _) (λ _ h heq ↦
        (((Bool.not_not _).symm.trans (congrArg Bool.not heq)).trans Bool.not_true)
          ▸ h)⟩
| .subroutine' _ _ _ _ _ _ _, _, h => ⟨
  λ _ ↦ Option.Forall_forall λ _ hm ↦
    ⟨_, soundInternal_subroutine_arg (Option.Forall_of_some hm (h _))⟩,
  soundInternal'_of_soundInternal λ _ ↦
    Option.Forall_bind ▸
    Option.Forall_imp (h _) (λ _ hm ↦
      Function.comp_apply ▸
      Option.Forall_map.symm ▸
      Option.Forall_isSome
        (soundInternal_subroutine_some hm)
        (soundInternal_subroutine_next hm))⟩
| .recurse _ _ _, _, h => ⟨
  λ _ ↦ Option.Forall_forall λ _ hm ↦
    ⟨_, soundInternal_recurse_arg (Option.Forall_of_some hm (h _))⟩,
  λ _ ↦ Option.Forall_forall λ _ hm ↦
    Option.Exists_of_isSome _ (soundInternal_recurse_size (Option.Forall_of_some hm (h _))),
  soundInternal'_of_soundInternal λ _ ↦
    Option.Forall_bind ▸
    Option.Forall_imp (h _) (λ _ hm ↦
      Function.comp_apply ▸
      Option.Forall_map.symm ▸
      Option.Forall_isSome
        (soundInternal_recurse_some hm)
        (soundInternal_recurse_next hm))⟩

theorem soundInternal_of_soundInternal': {tp: TracedProgram f} → {fm: α → Option Memory} →
    soundInternal' size tp fm → ∀ a, (fm a).Forall (soundInternal size a tp)
| .exit, _, h, _ => h _
| .op _ next, _, h, _ => Option.Forall_map ▸ soundInternal_of_soundInternal' (tp := next) h _
| .branch inst _, _, h, _ => Option.Forall_forall λ m hm ↦ match hb: inst.apply m with
  | true => soundInternal_branch_eq (f := f) hb ▸
    (Option.Forall_of_some hm
      (Option.Forall_filter ▸ soundInternal_of_soundInternal' h.left _))
      hb
  | false => soundInternal_branch_eq (f := f) hb ▸
    (Option.Forall_of_some hm
      (Option.Forall_filter ▸ soundInternal_of_soundInternal' h.right _))
      (congrArg Bool.not hb)
| .subroutine' _ _ _ _ _ _ _, _, h, _ =>
  Option.Forall_forall λ _ hm ↦
    (Option.Forall_of_some hm (h.left _)).elim λ hSome heq ↦
    ⟨ _, heq, Option.Forall_of_some
        ((congrArg₂ _ hm rfl).trans
        (congrArg₂ Option.map rfl (Option.some_get hSome).symm))
      (soundInternal_of_soundInternal' h.right _) ⟩
| .recurse _ _ _, _, h, a =>
  Option.Forall_forall λ _ hm ↦
    (Option.Forall_of_some hm (h.left _)).elim λ hSome heq ↦ ⟨
        Option.get _ hSome,
        heq,
        Option.Exists_isSome hSome (hm ▸ h.right.left a),
        Option.Forall_of_some
            ((congrArg₂ _ hm rfl).trans
            (congrArg₂ Option.map rfl (Option.some_get hSome).symm))
          (soundInternal_of_soundInternal' h.right.right _)
      ⟩

theorem soundInternal_iff_soundInternal': soundInternal' (f := f) size tp fm ↔ ∀ a, (fm a).Forall (soundInternal size a tp) :=
  ⟨ soundInternal_of_soundInternal', soundInternal'_of_soundInternal ⟩

theorem soundInternal'_def: soundInternal' (f := f) size tp fm = ∀ a, (fm a).Forall (soundInternal size a tp) :=
  eq_iff_iff.mpr soundInternal_iff_soundInternal'

theorem soundInternal'_of_sound: sound (f := f) tp size = soundInternal' size tp (some ∘ Complexity.encode) :=
  soundInternal'_def (f := f) ▸ rfl

end TracedProgram

class HasTrace {α: Type _} [Complexity.Encoding α Memory] {β: Type _} [Complexity.Encoding β Memory] (f: α → β) where
  program: List (TracedProgram f → TracedProgram f)
  size: α → ℕ
  sound: (TracedProgram.build program).sound size

instance {α: Type _} [Complexity.Encoding α Memory] {β: Type _} [Complexity.Encoding β Memory] {f: α → β} [tr: HasTrace f]: Complexity.Computable Encoding.Model f where
  program := (TracedProgram.build tr.program).toProgram
  has_result := TracedProgram.hasResult tr.sound

end HMem.Trace
