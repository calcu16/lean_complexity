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
| ite (cond: α → Prop) [Π {a}, decidable (cond a)] (branch: list instruction): instruction -- if cond acc then (execute is) else continue
| call (func: list instruction) (arg: source α): instruction -- [0] := func [arg]
| recurse (arg: source α): instruction -- [0] := this.func [arg]

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

end frame

def stack (α: Type u) := list (frame α)

namespace stack

def step: stack α → stack α
| [] := []
| [⟨_, [], m⟩] := [⟨[], [], m⟩] -- halting condition
| [f, ⟨[], [], m⟩] := [f.setm 0 m] -- return
| [⟨p, (i::is), m⟩] :=
  match i with
  | (instruction.binary_op op d l r) := [⟨p, is, m.setvp (d.map (λ x, x.getv m)) (op (m.getvp (l.map (λ x, x.getv m))) (m.getvp (r.map (λ x, x.getv m))))⟩]
  | (instruction.move d s) := [⟨p, is, m.setmp (d.map (λ x, x.getv m)) (m.getmp (s.map (λ x, x.getv m)))⟩]
  | (@instruction.ite _ cond dec is') := [⟨p, @ite _ (cond m.getv) dec is' is, m⟩]
  | (instruction.call p' arg) := [⟨p, is, m⟩, ⟨p', p', m.getm (arg.getv m)⟩]
  | (instruction.recurse arg) := [⟨p, is, m⟩, ⟨p, p, m.getm (arg.getv m)⟩]
  end
| (f :: fs) := f :: (step fs)

def result (r: bank α): stack α := [⟨[], [], r⟩]

theorem result_def (r: bank α): result r = [⟨[], [], r⟩] := rfl

theorem result.inj {r₀ r₁: bank α}: result r₀ = result r₁ → r₀ = r₁ :=
by simp[result, list.singleton_inj, frame.mk.inj_eq]


theorem result.inj_iff {r₀ r₁: bank α}: result r₀ = result r₁ ↔ r₀ = r₁ := ⟨ result.inj, congr_arg _ ⟩

theorem step_nil (n: ℕ): step^[n] (@list.nil (frame α)) = list.nil :=
begin
  induction n,
  { refl },
  { rwa [function.iterate_succ_apply] },
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

theorem step_halt'' (p: program α) (r: bank α): step [⟨p, [], r⟩] = result r := rfl

theorem step_halt_le {s: stack α} {r: bank α} {n: ℕ} {m: ℕ}:
  step^[n] s = (result r) → n ≤ m → (step^[m] s) = (result r) :=
begin
  intros hn h,
  cases nat.exists_eq_add_of_le h with x h,
  rw [h, add_comm, function.iterate_add_apply, hn, step_halt],
end

theorem step_stack (f: frame α) (p: program α) (i: instruction α) (is: program α) (m: bank α) (s: stack α):
  step (f :: ⟨p, i::is, m⟩ :: s) = f :: step  (⟨p, i::is, m⟩ :: s) :=
begin
  cases s;
  cases p;
  cases f;
  cases f_function;
  cases f_current;
  refl,
end

theorem step_stack' (f₀ f₁ f₂: frame α) (s: stack α):
  step (f₀ :: f₁ :: f₂ :: s) = f₀ :: step (f₁ :: f₂ :: s) :=
begin
  cases f₀,
  cases f₀_function;
  cases f₀_current;
  cases f₁;
  cases f₁_function;
  cases f₁_current;
  refl
end

theorem step_stack'' (f: frame α) (pi: instruction α)  (p: program α) (is: program α) (m: bank α) (s: stack α):
  step (f :: ⟨pi :: p, is, m⟩ :: s) = f :: step  (⟨pi::p, is, m⟩ :: s) :=
begin
  cases s;
  cases p;
  cases f;
  cases f_function;
  cases f_current;
  refl,
end

theorem step_result (f: frame α) (m: bank α):
  step (f :: result m) = [f.setm 0 m] :=
begin
  cases f;
  cases f_function;
  cases f_current;
  refl,
end

theorem step_return {s: stack α} {r: bank α} {n: ℕ}:
  (step^[n]) s = (result r) → ∀ f : frame α, ∃ m ≤ n + 1, (step^[m]) (f :: s) = [f.setm 0 r] :=
begin
  induction n generalizing s r,
  { rw [function.iterate_zero_apply],
    intros hs f,
    refine ⟨1, le_refl _, _⟩,
    rw [function.iterate_one, hs, step_result] },
  { cases s with f' fs,
    { simp only [step_nil, result, is_empty.forall_iff] },
    intros hs f,
    cases fs,
    { cases f',
      cases f'_current;
      cases f'_function,
      { refine ⟨1, le_add_self, _⟩,
        rw [← result_def, step_halt, result.inj_iff] at hs,
        rw [hs, ← result_def, function.iterate_one],
        exact step_result _ _ },
      { refine ⟨2, _, _⟩,
        { simp [nat.succ_eq_add_one, ← one_add_one_eq_two] },
        rw [function.iterate_succ_apply, step_halt'', step_halt, result.inj_iff] at hs,
        rw [function.iterate_succ_apply, function.iterate_one, step_stack'', step_halt'', step_result, hs] },
      repeat { rw [function.iterate_succ_apply] at hs,
        cases f'_current_hd;
        rcases n_ih hs f with ⟨m, hm, _⟩;
        refine ⟨m+1, nat.succ_le_succ hm, _⟩;
        rwa [function.iterate_succ_apply, step_stack] } },
    rw [function.iterate_succ_apply] at hs,
    rcases n_ih hs f with ⟨m, hm, _⟩,
    refine ⟨m+1, nat.succ_le_succ hm, _⟩,
    rwa [function.iterate_succ_apply, step_stack'] },
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
  [⟨ p, p, inp ⟩]

end program

end membank