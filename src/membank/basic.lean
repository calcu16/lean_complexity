import data.pnat.basic
import data.vector.basic

namespace membank
universe u

inductive source (α: Type u)
| acc: source
| imm (value: α): source

inductive instruction (α: Type u): Type u
| binary_op (op: α → α → α) (dst lhs rhs: list (source α)): instruction -- [dst...] := bin_op [lhs...] [rhs...]
| move (dst src: list (source α)): instruction -- [dst...] := [src...]
| clear (dst: list (source α)): instruction -- [dst...] := null
| ite (cond: α → Prop) [Π {a}, decidable (cond a)] (branch: list instruction): instruction -- if cond acc then (execute is) else continue
| call (func: list instruction) (arg: source α): instruction -- [0] := func [arg]
| recurse (arg: source α): instruction -- [0] := this.func [arg]

@[reducible]
def program (α: Type u) := list (instruction α)

inductive bank (α: Type u)
| null: bank
| mem (value: α) (memory: α → bank): bank

namespace bank
variables {α: Type u}

def getv [has_zero α]: bank α → α
| (null) := 0
| (mem v _) := v

def setv: bank α → α → bank α
| (null) v := mem v (function.const _ null)
| (mem _ b) v := mem v b

def getm: bank α → α → bank α
| (null) _ := null
| (mem _ b) v := b v

def setm [has_zero α] [decidable_eq α]: bank α → α → bank α → bank α
| (null) i v := mem 0 (λ j, if i = j then v else null)
| (mem x b) i v := mem x (λ j, if i = j then v else b j)


theorem setm_setm_self [has_zero α] [decidable_eq α] (m: bank α) (a: α) (v₀ v₁: bank α):
  (m.setm a v₀).setm a v₁ = m.setm a v₁ :=
begin
  cases m;
  unfold setm;
  simp;
  ext1;
  split_ifs;
  refl
end


def setvp [has_zero α] [decidable_eq α]: bank α → (list α) → α → bank α
| m [] v := m.setv v 
| m (a::as) v := m.setm a ((m.getm a).setvp as v)

def setmp [has_zero α] [decidable_eq α]: bank α → (list α) → bank α → bank α
| _ [] m' := m'
| m (a::as) m' := m.setm a ((m.getm a).setmp as m')

def getvp [has_zero α]: bank α → list α → α
| m [] := m.getv
| m (a::as) := (m.getm a).getvp as

def getmp: bank α → list α → bank α
| m [] := m
| m (a::as) := (m.getm a).getmp as

instance [has_zero α]: has_equiv (bank α) :=
 ⟨ λ a b, ∀ p, a.getvp p = b.getvp p ⟩

@[refl]
theorem equiv_refl [has_zero α] (m: bank α): m ≈ m := λ _, rfl

theorem equiv_refl' [has_zero α] {m n: bank α}: m = n → m ≈ n := flip eq.subst (equiv_refl _)

@[symm]
theorem equiv_symm [has_zero α] {m n: bank α}: m ≈ n → n ≈ m := λ h p, symm (h p)

@[trans]
theorem equiv_trans [has_zero α] {a b c: bank α}: a ≈ b → b ≈ c → a ≈ c := λ hab hbc p, trans (hab p) (hbc p)

theorem equiv_getv [has_zero α] {m n: bank α}:
  m ≈ n → m.getv = n.getv := λ h, h []

theorem equiv_getm [has_zero α] {m n: bank α} (a: α):
  m ≈ n → m.getm a ≈ n.getm a := λ h p, h (a::p)

theorem equiv_mk [has_zero α] {m n: bank α}:
  m.getv = n.getv → (∀ a, m.getm a ≈ n.getm a) → m ≈ n :=
λ hv hm p, list.cases_on p hv hm

theorem equiv_iff [has_zero α] {m n: bank α}:
  m ≈ n ↔ m.getv = n.getv ∧ (∀ a, m.getm a ≈ n.getm a) :=
⟨ λ h, ⟨equiv_getv h, λ _, equiv_getm _ h ⟩, λ h, equiv_mk h.left h.right ⟩

end bank

namespace source
variables {α: Type u} [has_zero α]
def getv: (source α) → (bank α) → α
| acc := bank.getv
| (imm v) := λ _, v
end source

variables {α: Type u} [has_zero α] [decidable_eq α]

structure frame (α: Type u) :=
  (function: program α)
  (current: program α)
  (register: bank α)

namespace frame

def setm [has_zero α]: frame α → α → bank α → frame α
| (mk f c r) i v := mk f c (r.setm i v)

theorem setm_function [has_zero α] (f: frame α) (a: α) (b: bank α):
  (f.setm a b).function = f.function :=
by cases f; trivial

end frame

namespace stack

def well_formed {α: Type u} (s: list (frame α)) :=
  (s ≠ [] ∧ (∀ f ∈ s, (frame.function f) ≠ [])) ∨ ∃ m, s = [⟨[], [], m⟩]

theorem well_formed_of_frame {α: Type u} {f: frame α}:
  f.function ≠ [] → well_formed [f] := λ h, or.inl begin
    rw list.ball_cons _ _ _,
    exact ⟨ by simp, h, list.ball_nil _⟩,
  end

theorem not_well_formed_nil {α: Type u}: ¬ @well_formed α [] := by simp [well_formed]

theorem well_formed_cons {α: Type u} {f: frame α} {s: list (frame α)}:
  f.function ≠ [] → well_formed s → (∀ m, s ≠ [⟨[], [], m⟩]) → well_formed (f::s) :=
begin
  intros fp sp hs,
  cases s,
  { exact absurd sp not_well_formed_nil },
  rcases sp with ⟨_, h⟩ | ⟨m, h⟩,
  { simp at h,
    simpa [well_formed, h.left] using and.intro fp h.right },
  exfalso,
  exact hs m (h.symm ▸ rfl),
end 

theorem well_formed_head {α: Type u} {f f': frame α} {fs: list (frame α)}:
  well_formed (f :: f' :: fs) → f.function ≠ [] :=
by simpa [well_formed] using λ h _ _, h

theorem not_well_formed_singleton_function {α: Type u} {i: instruction α} {is: program α} {m: bank α}:
  ¬ well_formed [⟨[], i::is, m⟩] :=
by simp [well_formed]

theorem well_formed_singleton_function {α: Type u} {p: program α} {i: instruction α} {is: program α} {m: bank α}:
  well_formed [⟨p, i::is, m⟩] → ∀ m', well_formed [⟨p, is, m'⟩] :=
by cases p; simp [well_formed]

theorem well_formed_singleton_function' {α: Type u} {p: program α} {i: instruction α} {is: program α} {m: bank α}:
  well_formed [⟨p, i::is, m⟩] → ∀ m' is', well_formed [⟨p, is', m'⟩] :=
by cases p; simp [well_formed]

theorem well_formed_pair {α: Type u} {p: program α} {i: instruction α} {is: program α} {m: bank α}:
  well_formed [⟨p, i::is, m⟩] → ∀ m' p' ps' is' m'', well_formed [⟨p, is, m'⟩, ⟨p'::ps', is', m''⟩] :=
by { cases p; simp [well_formed],
 rw [imp_true_iff, imp_true_iff, imp_true_iff, imp_true_iff, imp_true_iff],
 trivial }


theorem well_formed_pair' {α: Type u} {p: program α} {i: instruction α} {is: program α} {m: bank α}:
  well_formed [⟨p, i::is, m⟩] → ∀ m' is' m'', well_formed [⟨p, is, m'⟩, ⟨p, is', m''⟩] :=
by { cases p; simp [well_formed] }

theorem not_well_formed_stack {α: Type u} {is: program α} {m: bank α} {f: frame α} {s: list (frame α)}:
 ¬ well_formed (⟨[], is, m⟩::f::s) :=
by cases is; simp [well_formed]

end stack

def stack (α: Type u) := { s : list (frame α) // stack.well_formed s }

namespace stack

theorem irrel {α: Type u} {f f': list (frame α)}: f = f' →
  ∀ {pf pf'}, (⟨f, pf⟩:stack α) = ⟨f', pf'⟩ := λ h, h ▸ (λ _ _, rfl)

def item (α: Type u) := { f: frame α // f.function ≠ [] }

def result (r: bank α): stack α := ⟨[⟨[], [], r⟩], or.inr ⟨r, rfl⟩⟩

theorem result_def (r: bank α): (result r).val = [⟨[], [], r⟩] := rfl

theorem result.inj {r₀ r₁: bank α}: result r₀ = result r₁ → r₀ = r₁ :=
by simp[result, list.singleton_inj, frame.mk.inj_eq]

theorem result.inj_iff {r₀ r₁: bank α}: result r₀ = result r₁ ↔ r₀ = r₁ := ⟨ result.inj, congr_arg _ ⟩

def cons: item α → stack α → stack α
| f ⟨[], pf⟩ := absurd pf not_well_formed_nil
| f ⟨[⟨[], [], m⟩], pf⟩ := ⟨[f.val.setm 0 m], or.inl ⟨ list.cons_ne_nil _ _, by simpa [frame.setm_function] using f.property⟩⟩
| f ⟨[⟨[], _::_, _⟩], pf⟩ := absurd pf not_well_formed_singleton_function
| f ⟨[⟨p::ps, is, m⟩], pf⟩ := ⟨ [f.val, ⟨p::ps, is, m⟩], or.inl ⟨ list.cons_ne_nil _ _, by simpa using f.property ⟩ ⟩
| f ⟨f'::f''::s, pf⟩ := ⟨ f.val :: f' :: f'' :: s , begin
  cases pf,
  { refine or.inl ⟨_, _⟩,
    exact list.cons_ne_nil _ _,
    exact (list.ball_cons _ _ _).mpr ⟨f.property, pf.right⟩ },
  revert pf, simp,
end ⟩

theorem cons_result (fp: item α) (m: bank α):
  cons fp (result m) = ⟨[fp.val.setm 0 m], by simpa [well_formed, frame.setm_function] using or.inl fp.property ⟩ := rfl

theorem cons_not_result (fp: item α) {s: stack α} (hs: ∀ m, s ≠ result m):
   cons fp s = ⟨fp.val::s.val, well_formed_cons fp.property s.property (begin cases s, simp, contrapose! hs, cases hs with m hs, refine ⟨m, _⟩, simp[hs, result],
    end)
   ⟩ :=
begin
  cases s with s sp,
  cases s with f' s,
  { exact absurd sp not_well_formed_nil },
  cases f' with p is m,
  cases p;
  cases is;
  cases s with f'' s;
  try { refl },
  { exfalso,
    exact hs m rfl },
  exact absurd sp not_well_formed_singleton_function,
end

def step_helper: list (frame α) → list (frame α)
| [] := []
| [⟨_, [], m⟩] := [⟨[], [], m⟩] -- halting condition
| [f, ⟨_, [], m⟩] := [f.setm 0 m] -- return
| [⟨p, (i::is), m⟩] :=
  match i with
  | (instruction.binary_op op d l r) := [⟨p, is, m.setvp (d.map (λ x, x.getv m)) (op (m.getvp (l.map (λ x, x.getv m))) (m.getvp (r.map (λ x, x.getv m))))⟩]
  | (instruction.move d s) := [⟨p, is, m.setmp (d.map (λ x, x.getv m)) (m.getmp (s.map (λ x, x.getv m)))⟩]
  | (instruction.clear d) := [⟨p, is, m.setmp (d.map (λ x, x.getv m)) bank.null⟩]
  | (@instruction.ite _ cond dec is') := [⟨p, @ite _ (cond m.getv) dec is' is, m⟩]
  | (instruction.call [] arg) := [⟨p, is, m.setm 0 (m.getm (arg.getv m))⟩]
  | (instruction.call (p'::ps') arg) := [⟨p, is, m.setm 0 bank.null⟩, ⟨p'::ps', p'::ps', m.getm (arg.getv m)⟩]
  | (instruction.recurse arg) := [⟨p, is, m.setm 0 bank.null⟩, ⟨p, p, m.getm (arg.getv m)⟩]
  end
| (f :: fs) := f :: (step_helper fs)

theorem step_helper_instruction_cases (p: program α) (i: instruction α) (is: program α) (m: bank α):
  ∃ is' m' s, step_helper [⟨p, i::is, m⟩] = ⟨p, is', m'⟩::s ∧
    (s = [] ∨
    (∃ i' is' m'', s = [⟨i'::is', i'::is', m''⟩]) ∨
    (∃ m'', s = [⟨p, p, m''⟩])) :=
by cases i; try { cases i_func }; simp [step_helper, and_assoc]

theorem step_helper_cons_cases (f f':frame α) (p: list (frame α)):
  step_helper (f::f'::p) = f::step_helper (f'::p) ∨ step_helper (f::f'::p) = [f.setm 0 f'.register] :=
begin
  cases f;
  cases f_current;
  cases p;
  cases f';
  cases f'_current;
  try { exact or.inl rfl  };
  try { exact or.inr rfl  },
end

theorem step_helper_nil (s: list (frame α)):
  step_helper s = [] ↔ s = [] :=
begin
  cases s with f s,
  { exact ⟨ λ _, rfl, λ _, rfl ⟩ },
  cases s with f' s,
  { cases f with p is m,
    cases is with i is,
    { simp [step_helper] },
    rcases step_helper_instruction_cases p i is m with ⟨is', m', s', h, _⟩,
    simp [h] },
  { cases step_helper_cons_cases f f' s;
    simp [h] },
end

theorem step_helper_ne_nil (s: list (frame α)):
  step_helper s ≠ [] ↔ s ≠ [] := by simp [step_helper_nil]

theorem step_helper_cons (f: frame α) (p: program α) (i: instruction α) (is: program α) (m: bank α) (s: list (frame α)):
  step_helper (f :: ⟨p, i::is, m⟩ :: s) = f :: step_helper  (⟨p, i::is, m⟩ :: s) :=
begin
  cases s;
  cases p;
  cases f;
  cases f_function;
  cases f_current;
  refl,
end

theorem step_helper_cons_cons (f₀ f₁ f₂: frame α) (s: list (frame α)):
  step_helper (f₀ :: f₁ :: f₂ :: s) = f₀ :: step_helper (f₁ :: f₂ :: s) :=
begin
  cases f₀,
  cases f₀_function;
  cases f₀_current;
  cases f₁;
  cases f₁_function;
  cases f₁_current;
  refl
end

theorem step_helper_cons_result (f: frame α) (p: program α) (m: bank α):
  step_helper [f, ⟨p, [], m⟩] = [f.setm 0 m] :=
begin
  cases f;
  cases f_current;
  refl,
end

theorem step_helper_result (p: program α) (m: bank α):
  step_helper [⟨p, [], m⟩] = [⟨[], [], m⟩] := rfl

theorem step_helper_result_cases {s: list (frame α)} {m: bank α}:
  well_formed s → step_helper s = [⟨[], [], m⟩] → ∃ p, s = [⟨p, [], m⟩] :=
begin
  cases s with f s,
  { exact flip absurd not_well_formed_nil },
  cases f with p is m,
  cases s with f' s,
  { cases is with i is,
    { intro,
      simpa only [step_helper, implies_true_iff, and_assoc, exists_eq_left', eq_self_iff_true, true_and] using id },
    cases p with p ps,
    { exact flip absurd not_well_formed_singleton_function },
    rcases step_helper_instruction_cases (p::ps) i is m with ⟨is', m', s', h, _⟩,
    simp [h] },
  { cases p with p ps,
    { exact flip absurd not_well_formed_stack },
    cases step_helper_cons_cases ⟨ p::ps, is, m ⟩ f' s,
    { simp [h] },
    simp [h, frame.setm] }
end

theorem step_helper.well_formed_helper (s: list (frame α)):
  (∀ f ∈ s, frame.function f ≠ []) → (∀ f ∈ (step_helper s), frame.function f ≠ []) ∨ ∃ m, (step_helper s) = [⟨[], [], m⟩] :=
begin
  induction s with f s,
  { exact or.inl },
  cases s with f' s,
  { clear s_ih,
    cases f with p is m,
    cases is with i is,
    { simp [step_helper] },
    rcases step_helper_instruction_cases p i is m with ⟨m, is, s, h, h'|⟨i, is, m, h'⟩|⟨m, h'⟩⟩,
    { simpa [h, h'] using or.inl },
    simp [h, h'],
    simp [h, h'] },
  cases step_helper_cons_cases f f' s,
  { rw [list.ball_cons, and_imp],
    intros hf hwf,
    rcases s_ih hwf with s_ih | ⟨m, s_ih⟩,
    { left,
      simpa [h, hf] using s_ih },
    { cases flip step_helper_result_cases s_ih (or.inl ⟨by simp, hwf⟩),
      simp [h_1, step_helper_cons_result, frame.setm_function, hf] } },
  intro hwf,
  left,
  rw [h],
  simp at hwf,
  simp [frame.setm_function, hwf],
end

def step (s: stack α) : stack α := ⟨ step_helper s.val, begin
  rcases s.property with ⟨ hs, h ⟩ | ⟨m, h⟩,
  rcases step_helper.well_formed_helper s.val h with h|⟨m, h⟩,
  { left,
    rw [step_helper_ne_nil],
    exact ⟨ hs, h ⟩ },
  exact or.inr ⟨ m, h ⟩,
  exact or.inr ⟨ m, h.symm ▸ rfl ⟩,
end ⟩

theorem step_cons {f f': frame α} {s: list (frame α)}:
∀ pf pf' pf'', step ⟨f::f'::s, pf⟩ = cons ⟨f, pf'⟩ (step ⟨(f'::s), pf''⟩) :=
begin
  intros _ _ _,
  unfold step,
  cases s with f'' s,
  { cases f' with p is m,
    cases is with i is,
    { simp [cons, step_helper_cons_result, step_helper] },
    cases p with p ps,
    { exact absurd pf'' not_well_formed_singleton_function },
    rcases step_helper_instruction_cases (p::ps) i is m with ⟨is', m', s, h, _⟩,
    cases is';
    cases s;
    simp [cons, step_helper_cons, h] },
  cases step_helper_cons_cases f' f'' s,
  { cases f' with p is m,
    cases p with p ps,
    { revert pf'', simp[well_formed] },
    cases is;
    cases step_helper (f'' :: s);
    simp [cons, step_helper_cons_cons, h] },
  cases f' with p is m,
  cases p with p ps,
  { revert pf'', simp[well_formed] },
  simp [cons, step_helper_cons_cons, h, frame.setm],
end

theorem step_cons' (fp: item α) (s: stack α):
  (∀ m, s ≠ result m) → step (cons fp s) = cons fp (step s) :=
begin
  intro h,
  rw [cons_not_result _ h],
  cases s with s sp,
  cases s with f' s,
  { exact absurd sp not_well_formed_nil },
  rw [step_cons _ fp.property sp],
  simp,
end

theorem step_halt (r: bank α) (n: ℕ): step^[n] (result r) = (result r) :=
begin
  induction n,
  exact function.iterate_zero_apply _ _,
  rw [function.iterate_succ_apply', n_ih],
  refl,
end

theorem step_halt' {r₀ r₁: bank α} {n: ℕ}: step^[n] (result r₁) = result r₀ → r₁ = r₀ :=
  (step_halt r₁ n).symm ▸ result.inj

theorem step_halt'' (p: program α) (r: bank α) (pf: well_formed [⟨p, [], r⟩]): step ⟨[⟨p, [], r⟩], pf⟩ = result r := rfl

theorem step_halt_le {s: stack α} {r: bank α} {n: ℕ} {m: ℕ}:
  step^[n] s = (result r) → n ≤ m → (step^[m] s) = (result r) :=
begin
  intros hn h,
  cases nat.exists_eq_add_of_le h with x h,
  rw [h, add_comm, function.iterate_add_apply, hn, step_halt],
end

theorem step_halt_unique {s: stack α} {r₀ r₁: bank α} {n: ℕ} {m: ℕ}:
  step^[n] s = result r₀ → (step^[m]) s = result r₁ → r₀ = r₁ :=
begin
  intros h₀ h₁,
  cases le_total n m,
  { rw [step_halt_le h₀ h] at h₁,
    exact result.inj h₁ },
  { rw [step_halt_le h₁ h] at h₀,
    exact result.inj h₀.symm }
end

theorem step_return {s: stack α} {r: bank α} {n: ℕ}:
  (s ≠ result r) → (step^[n]) s = (result r) → ∀ (fp : item α), ∃ (m ≤ n) pf', (step^[m]) (stack.cons fp s) = ⟨ [fp.val.setm 0 r], pf' ⟩:=
begin
  induction n generalizing s r,
  { rw [function.iterate_zero_apply],
    intros _ hs fp,
    rw [hs],
    simpa [well_formed, cons_result, frame.setm_function] using or.inl fp.property },
  { intros hns hs fp,
    cases s with s pfs,
    cases s with f' s,
    { exact absurd pfs not_well_formed_nil },
    by_cases step ⟨f'::s, pfs⟩ = result r,
    { refine ⟨1, nat.succ_le_succ (nat.zero_le _), _, _⟩,
      { simpa [well_formed, frame.setm_function] using or.inl fp.property },
      rw [function.iterate_one, step_cons', h, cons_result],
      intros m hm,
      rw [hm, step_halt] at hs,
      rw [hs] at hm,
      exact hns hm },
    { rw[function.iterate_succ_apply] at hs,
      rcases n_ih h hs _ with ⟨m, hm, pf', ih⟩,
      refine ⟨m.succ, nat.succ_le_succ hm, pf', _⟩,
      rwa [function.iterate_succ_apply, step_cons'],
      intros m h',
      rw [h', ← function.iterate_succ_apply, step_halt] at hs,
      apply h,
      rw [h', hs, ← function.iterate_one step],
      exact step_halt _ _ } }
end

theorem step_trans {s t u: stack α} (n m: ℕ) {nm: ℕ}:
  (step^[n]) s = t → (step^[m]) t = u → n + m = nm → (step^[nm]) s = u :=
begin
  intros hst htu hnm,
  rwa [← hnm, add_comm, function.iterate_add_apply, hst],
end

end stack

namespace program

def apply (p: program α) (inp: bank α): stack α :=
  ⟨ [⟨ p, p, inp ⟩], begin
    cases p,
    exact or.inr ⟨inp, rfl⟩,
    exact or.inl ⟨list.cons_ne_nil _ _, (list.ball_cons _ _ _).mpr ⟨list.cons_ne_nil _ _, list.ball_nil _⟩⟩,
  end ⟩

def costed_result (p: program α) (inp: bank α) (n: ℕ) (outp: bank α) :=
  stack.step^[n] (p.apply inp) = stack.result outp

def has_result (p: program α) (inp: bank α) (outp: bank α) :=
  ∃ n, costed_result p inp n outp

theorem has_result_unique {p: program α} {inp outp₀ outp₁: bank α}:
  p.has_result inp outp₀ → p.has_result inp outp₁ → outp₀ = outp₁ :=
begin
  unfold has_result costed_result,
  simp only [exists_imp_distrib],
  intros x hx y hy,
  exact stack.step_halt_unique hx hy,
end

def cost_le (p: program α) (inp: bank α) (n: ℕ) :=
  ∃ outp, costed_result p inp n outp

theorem cost_le_mono {p: program α} {inp: bank α} {n m: ℕ}:
  n ≤ m → cost_le p inp n → cost_le p inp m :=
begin
  intros hnm h,
  rcases h with ⟨outp, h⟩,
  exact ⟨outp, stack.step_halt_le h hnm ⟩,
end

def halts (p: program α) (inp: bank α) :=
  ∃ n outp, costed_result p inp n outp

end program

theorem stack.step_call (p: program α) (arg: source α) (func: program α) (is: program α) (m: bank α) (hfunc: func ≠ []) (hp: p ≠ []):
  stack.step ⟨[⟨p, (instruction.call func arg)::is, m⟩], by simpa [stack.well_formed] using hp⟩ = stack.cons ⟨⟨p, is, m.setm 0 bank.null⟩, hp⟩ (program.apply func (m.getm (arg.getv m))) :=
begin
  cases p, { contradiction },
  cases func, { contradiction },
  unfold stack.step stack.step_helper stack.cons program.apply,
  refl,
end

theorem stack.step_recurse (p: program α) (arg: source α) (is: program α) (m: bank α) (hp: p ≠ []):
  stack.step ⟨[⟨p, (instruction.recurse arg)::is, m⟩], by simpa [stack.well_formed] using hp⟩ = stack.cons ⟨⟨p, is, m.setm 0 bank.null⟩, hp⟩ (program.apply p (m.getm (arg.getv m))) :=
begin
  cases p, { contradiction },
  unfold stack.step stack.step_helper stack.cons program.apply,
  refl,
end
end membank