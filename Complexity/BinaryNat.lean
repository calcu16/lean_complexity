import Complexity.Std
import Complexity.StdComp
import Complexity.StdDiv
import Complexity.Cost

namespace Complexity

inductive BinaryNat : Nat → Type _ where
  | bit_false : BinaryNat 0
  | bit_true : BinaryNat 0
  | intro : BinaryNat n → BinaryNat n → BinaryNat (n + 1)

namespace BinaryNat
@[simp]
def height (_ : BinaryNat n) : Nat := n

@[simp]
def bits (x : BinaryNat α) : Nat := 2 ^ (height x)

@[simp]
def bound (x : BinaryNat α) : Nat := 2 ^ (bits x)

def toNat : (x : BinaryNat α) → Nat
  | BinaryNat.bit_false => 0
  | BinaryNat.bit_true => 1
  | BinaryNat.intro y z => bound z * toNat y + toNat z

def ofNat (n a : Nat) : BinaryNat n :=
  match n with
  | 0 => if a % 2 == 1 then BinaryNat.bit_true else BinaryNat.bit_false
  | n + 1 => BinaryNat.intro (ofNat _ (a / 2 ^ 2 ^ n)) (ofNat _ a)
end BinaryNat

namespace CostedBinaryNat

def bit_zero := Cost.succ BinaryNat.bit_false

def bit_one := Cost.succ BinaryNat.bit_true

def split (x : BinaryNat (n + 1)) :=
  match x with | BinaryNat.intro x y => Cost.succ (x, y)

def intro (x y: BinaryNat n) := Cost.succ (BinaryNat.intro x y)

def ite : BinaryNat 0 → Costed α → Costed α → Costed α := λ x p q =>
  Cost.bind (Cost.succ 0) λ _ =>
  match x with
  | BinaryNat.bit_true => p
  | BinaryNat.bit_false => q

def zero  (n : Nat) : Costed (BinaryNat n) :=
  match n with
  | 0 => bit_zero
  | n + 1 => do
    let z ← zero n
    intro z z

def extend (n : Nat) : BinaryNat m → Costed (BinaryNat (m + n)) :=
  match n with
  | 0 => λ x => Cost.pure x
  | n + 1 => λ x => do
    let z ← zero (m + n)
    let e ← extend n x
    intro z e

def add_with_carry {n : Nat} : BinaryNat n → BinaryNat n → BinaryNat 0 → Costed (BinaryNat 0 × BinaryNat n) :=
  match n with
  | 0 => λ x y z =>
    ite x
      (ite y
        (ite z (Cost.cross bit_one bit_one) (Cost.cross bit_one bit_zero))
        (ite z (Cost.cross bit_one bit_zero) (Cost.cross bit_zero bit_one))
      )
      (ite y 
        (ite z (Cost.cross bit_one bit_zero) (Cost.cross bit_zero bit_one))
        (ite z (Cost.cross bit_zero bit_one) (Cost.cross bit_zero bit_zero))
      )
  | _ + 1 =>  λ x y zc => do
    let (xu, xl) ← split x
    let (yu, yl) ← split y
    let (zc, zl) ← add_with_carry xl yl zc
    let (zc, zu) ← add_with_carry xu yu zc
    let z ← intro zu zl
    return (zc, z)

def add {n : Nat} : BinaryNat n → BinaryNat n → Costed (BinaryNat n) :=
  λ x y => do
  let zc ← bit_zero
  let (_, z) ← add_with_carry x y zc
  return z

def complement {n : Nat} : BinaryNat n → Costed (BinaryNat n) :=
  match n with
  | 0 => λ x => ite x bit_zero bit_one
  | _ + 1 => λ x => do
    let (xu, xl) ← split x
    let cxu ← complement xu
    let cxl ← complement xl
    intro cxu cxl

def sub {n : Nat} : BinaryNat n → BinaryNat n → Costed (BinaryNat n) :=
  λ x y => do
    let cy ← complement y
    let o ← bit_one
    let (_, r) ← add_with_carry x cy o
    return r

def traditional_multiply {n : Nat} : BinaryNat n → BinaryNat n -> Costed (BinaryNat (n + 1)) :=
  match n with
  | 0 => λ x y => do
    let z ←  ite x (ite y bit_one bit_zero) bit_zero
    extend 1 z
  | n + 1 => λ x y =>
    let shift_n := λ zn w => do
      let (wu, wl) ← split w
      let wu ← intro zn wu
      let wl ← intro wl zn
      intro wu wl
  do
    let (xu, xl) ← split x
    let (yu, yl) ← split y
    let zn1 ← zero (n + 1)
    let zn ← zero n
    let ll ← traditional_multiply xl yl
    let ll ← intro zn1 ll
    let lu ← traditional_multiply xl yu
    let lu ← shift_n zn lu
    let ul ← traditional_multiply xu yl
    let ul ← shift_n zn ul
    let uu ← traditional_multiply xu yu
    let uu ← intro uu zn1
    let zu ← add uu lu
    let zl ← add ul ll
    add zu zl

end CostedBinaryNat
end Complexity