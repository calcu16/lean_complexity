import data.nat.pow
import data.vector.basic
import cost

inductive binary_nat : ℕ → Type
| bit_false : binary_nat 0
| bit_true : binary_nat 0
| intro : Π {n}, binary_nat n → binary_nat n → binary_nat (n+1)

namespace binary_nat

def toNat : Π {n}, binary_nat n → ℕ
| 0 bit_false := 0
| 0 bit_true := 1
| (n+1) (intro x y) := 2^2^n * toNat x + toNat y

def ofNat : Π {n}, ℕ → binary_nat n
| 0 := λ a, if a % 2 = 1 then bit_true else bit_false
| (n+1) := λ a, intro (ofNat (a/2^2^n)) (ofNat a)
  
end binary_nat

namespace costed_binary_nat
open complexity
universe u
variables {α : Type u}

@[simp]
def bit_zero := cost.succ binary_nat.bit_false

@[simp]
def bit_one := cost.succ binary_nat.bit_true

@[simp]
def intro {n : ℕ} (x y : binary_nat n) :=
  cost.succ (binary_nat.intro x y)

@[simp]
def split {n : ℕ} (x : binary_nat (n+1)) :=
  match x with | (binary_nat.intro y z) :=
    cost.succ (y, z)
  end

@[simp]
def ite (x : binary_nat 0) (ct cf : cost.costed α) : cost.costed α :=
  match x with
  | binary_nat.bit_true := ct
  | binary_nat.bit_false := cf
  end >>= cost.succ

def zero : Π (n), cost.costed (binary_nat n)
| 0 := bit_zero
| (n+1) := do
  z ← zero n,
  intro z z

def add_with_carry : Π {n}, binary_nat n → binary_nat n → binary_nat 0 →
    cost.costed (binary_nat 0 × binary_nat n)
| 0 := λ x y z,
  ite x
    (ite y
      (ite z
        (cost.cross bit_one bit_one)
        (cost.cross bit_one bit_zero))
      (ite z
        (cost.cross bit_one bit_zero)
        (cost.cross bit_zero bit_one)))
    (ite y
      (ite z
        (cost.cross bit_one bit_zero)
        (cost.cross bit_zero bit_one))
      (ite z
       (cost.cross bit_zero bit_one)
       (cost.cross bit_zero bit_zero)))
| (n+1) := λ x y z, do
  (xu, xl) ← split x,
  (yu, yl) ← split y,
  zl ← add_with_carry xl yl z,
  zu ← add_with_carry xu yu zl.fst,
  cost.cross (pure zu.fst) (intro zu.snd zl.snd)

def add {n : ℕ}: binary_nat n → binary_nat n → cost.costed (binary_nat n) :=
  λ x y, do
    z0 ← bit_zero,
    z ← add_with_carry x y z0,
    return z.snd

def traditional_multiply : Π {n}, binary_nat n → binary_nat n →
    cost.costed (binary_nat (n + 1))
| 0 := λ x y, do
  z0 ← ite x (ite y bit_one bit_zero) (ite y bit_zero bit_zero),
  z1 ← bit_zero,
  intro z1 z0
| (n+1) :=
  have shift_n : (binary_nat (n + 1) → cost.costed (binary_nat (n + 2))) :=
    (λ x, do
      zn ← zero n,
      x ← split x,
      xu ← intro zn x.fst,
      xl ← intro x.snd zn,
      intro xu xl),
  λ x y, do
    (xu, xl) ← split x,
    (yu, yl) ← split y,
    ll ← traditional_multiply xl yl,
    lu ← traditional_multiply xl yu,
    ul ← traditional_multiply xu yl,
    uu ← traditional_multiply xu yu,
    zn1 ← zero (n + 1),
    ll ← intro zn1 ll,
    lu ← shift_n lu,
    ul ← shift_n ul,
    uu ← intro uu zn1,
    l ← add lu ll,
    u ← add uu ul,
    add u l

end costed_binary_nat