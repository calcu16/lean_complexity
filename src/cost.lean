import data.nat.basic
import algebra.group.pi
import tactic.ring

universes u v
variables {α : Type u}
variables {β : Type v}

namespace complexity
namespace cost

@[simp]
def raw_cost_independent (f : ℕ → (ℕ × α)) :=
  ∀ c₀ c₁ : ℕ, (f c₀).fst + c₁ = (f c₁).fst + c₀

@[simp]
def raw_value_independent (f : ℕ → (ℕ × α)) :=
  ∀ c₀ c₁ : ℕ, (f c₀).snd = (f c₁).snd

@[simp]
def invariant (f : ℕ → (ℕ × α)) :=
  raw_cost_independent f ∧ raw_value_independent f


def costed (α : Type u) :=
  { val : ℕ → (ℕ × α) // invariant val }

theorem cost_independent {ca : costed α} : ∀ c₀, (ca.val c₀).fst = (ca.val 0).fst + c₀ :=
begin
  intro c₀,
  exact ca.2.left c₀ 0,
end

theorem value_independent {ca : costed α} : ∀ c₀, (ca.val c₀).snd = (ca.val 0).snd :=
begin
  intro c₀,
  exact ca.2.right c₀ 0,
end

@[simp]
def raw_pure (a : α) := λ c : ℕ, (c, a)

theorem raw_pure_invariant (a : α) : invariant (raw_pure a) :=
begin
  split,
  intros c₀ c₁,
  simp [nat.add_comm],
  intros c₀ c₁,
  simp,
end

def pure (a : α) : costed α := ⟨ raw_pure a, raw_pure_invariant a ⟩

@[simp]
def raw_succ (a : α) := λ c : ℕ, (nat.succ c, a)

theorem raw_succ_invariant (a : α) : invariant (raw_succ a) :=
begin
  split,
  intros c₀ c₁,
  unfold raw_succ,
  simp [nat.succ_add],
  rw  [nat.add_comm],
  intros c₀ c₁,
  simp,
end

def succ (a : α) : costed α := ⟨ raw_succ a, raw_succ_invariant a ⟩

@[simp]
def raw_bind (ca : costed α) (cba : α → costed β) : (ℕ → (ℕ × β)) :=
  λ c : ℕ, (cba (ca.1 c).snd).1 (ca.1 c).fst

theorem raw_bind_invariant (ca : costed α) (cba : α → costed β) : invariant (raw_bind ca cba) :=
begin
  split,
  intros c₀ c₁,
  unfold raw_bind,
  rw [@cost_independent α],
  rw [@cost_independent β],
  rw [value_independent],
  conv begin
    to_rhs,
    rw [@cost_independent α],
    rw [@cost_independent β],
    rw [value_independent],
  end,
  ring,
  intros c₀ c₁,
  unfold raw_bind,
  rw [@value_independent α],
  rw [@value_independent β],
  conv begin
    to_rhs,
    rw [@value_independent α],
    rw [@value_independent β],
  end,
end

def bind (ca : costed α) (cba : α → costed β) : costed β := ⟨ raw_bind ca cba, raw_bind_invariant ca cba ⟩

instance : monad costed := {pure := @complexity.cost.pure, bind := @complexity.cost.bind}

@[simp]
def cross (ca : costed α) (cb : costed β) : costed (α × β) :=
  do
    a ← ca,
    b ← cb,
    return (a, b)

def cost_of (ca : costed α) : ℕ := (ca.val 0).fst

def value_of (ca : costed α) : α := (ca.val 0).snd

@[simp]
theorem cost_of_pure {a : α} : cost_of (pure a) = 0 := by simp [cost_of, pure]
@[simp]
theorem value_of_pure {a : α} : value_of (pure a) = a := by simp[value_of, pure]

@[simp]
theorem cost_of_return {a : α} : cost_of (return a) = 0 := by simp [return, has_pure.pure]

@[simp]
theorem value_of_return {a : α} : value_of (return a) = a := by simp [return, has_pure.pure]

@[simp]
theorem cost_of_succ {a : α} : cost_of (succ a) = 1 := by simp[cost_of, succ]
@[simp]
theorem value_of_succ {a : α} : value_of (succ a) = a := by simp[value_of, succ]

@[simp]
theorem cost_of_bind {ca : costed α} {cab : α → costed β} :
    cost_of (bind ca cab) =  cost_of (cab (value_of ca)) + (cost_of ca) :=
begin
  simp [bind, cost_of, value_of],
  have g := @cost_independent β (cab (ca.val 0).snd) (ca.val 0).fst,
  simp at g,
  rw [← g],
end

@[simp]
theorem cost_of_bind_infix {α β : Type u} {ca : costed α} {cab : α → costed β} :
  cost_of (ca >>= cab) = cost_of (cab (value_of ca))+ cost_of ca := cost_of_bind

@[simp]
theorem value_of_bind {ca : costed α} {cab : α → costed β} :
    value_of (bind ca cab) = value_of (cab (value_of ca)) :=
begin
  simp [bind, value_of],
  have g := value_independent,
  simp at g,
  rw [g],
end

@[simp]
theorem value_of_bind_infix {α β : Type u} {ca : costed α} {cab : α → costed β} :
  value_of (ca >>= cab) = value_of (cab (value_of ca))  := value_of_bind

end cost
end complexity