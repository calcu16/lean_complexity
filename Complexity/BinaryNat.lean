import Complexity.Std
import Complexity.StdComp
import Complexity.StdDiv

namespace Complexity
inductive BinaryNat : Nat → Type _ where
  | bit : Bool → BinaryNat 0
  | intro : BinaryNat n → BinaryNat n → BinaryNat (n + 1)

namespace BinaryNat

inductive Cost : Type 0 where
  | intro : Nat → Cost

namespace Cost
def init : Cost := Cost.intro Nat.zero
def inc : Cost → Cost | intro value => intro (value + 1)
def add : Cost → Nat → Cost | intro value => λ n => intro (value + n)
end Cost

def bit_zero (c: Cost) := (Cost.inc c, BinaryNat.bit false)

def bit_one (c: Cost ):= (Cost.inc c, BinaryNat.bit true)  

def height (_ : BinaryNat n) : Nat := n

def bits (x : BinaryNat α) : Nat := 2 ^ (height x)

def bound (x : BinaryNat α) : Nat := 2 ^ (bits x)

def toNat : (x : BinaryNat α) → Nat
  | bit b => if b then 1 else 0
  | intro y z =>
    bound z * toNat y + toNat z

def ofNat (n a : Nat) : BinaryNat n :=
  match n with
  | 0 => BinaryNat.bit (a % 2 == 1)
  | n + 1 => BinaryNat.intro (ofNat _ (a / 2 ^ 2 ^ n)) (ofNat _ a)

def ite : BinaryNat 0 → α → α → α := by
  intro x
  intro p
  intro q
  cases x with | bit b =>
  apply (if b then p else q)

def zero (c: Cost) (n : Nat) : (Cost × BinaryNat n) :=
  match n with
  | 0 => bit_zero c
  | n + 1 =>
    let (c, z) := zero c n
    (Cost.inc c, BinaryNat.intro z z)

def extend (c : Cost) (n : Nat) : BinaryNat m → (Cost × BinaryNat (m + n)) :=
  match n with
  | 0 => λ x => (c, x)
  | n + 1 => λ x =>
    let (c, z) := zero c (m + n)
    let (c, e) := extend c n x
    (Cost.inc c, BinaryNat.intro z e)

def add_with_carry (c: Cost) {n : Nat} : BinaryNat n → BinaryNat n → BinaryNat 0 → (Cost × BinaryNat 0 × BinaryNat n) :=
  match n with
  | 0 => λ x y z =>
    match x with
    | bit xb =>
      match y with
      | bit yb => 
        match z with 
        | bit zb => (Cost.add c 7, (BinaryNat.bit (xb && yb || xb && zb || yb && zb)), (BinaryNat.bit ((xb ≠ yb) ≠ zb)))
  | _ + 1 =>  λ x y z =>
    match x with
    | intro xu xl =>
      match y with
      | intro yu yl =>
         let (c, z2, l) := add_with_carry c xl yl z
         let (c, z3, u) := add_with_carry c xu yu z2
         (Cost.inc c, z3, BinaryNat.intro u l)

def add (c: Cost) {n : Nat} : BinaryNat n → BinaryNat n → (Cost × BinaryNat n) :=
  λ x y =>
    let (c, z) := zero c 0
    let (c, _, r) := add_with_carry c x y z
    (c, r)

def complement (c: Cost) {n : Nat} : BinaryNat n → (Cost × BinaryNat n) :=
  match n with
  | 0 => λ x =>
    match x with | bit a => (Cost.inc c, BinaryNat.bit (!a))
  | _ + 1 => λ x =>
    match x with
    | intro xu xl =>
      let (c, cxu) := complement c xu
      let (c, cxl) := complement c xl
      (Cost.inc c, BinaryNat.intro cxu cxl)

def sub (c: Cost) {n : Nat} : BinaryNat n → BinaryNat n → (Cost × BinaryNat n) :=
  λ x y =>
    let (c, cy) := complement c y
    let (c, o) := bit_one c
    let (c, _, r) := add_with_carry c x cy o
    (c, r)

def traditional_multiply (c: Cost) {n : Nat} : BinaryNat n → BinaryNat n -> (Cost × BinaryNat (n + 1)) :=
  match n with
  | 0 => λ x y =>
    match x with
    | bit a =>
      match y with
      | bit b => extend (Cost.inc c) _ (BinaryNat.bit (a && b))
  | _ + 1 => λ x y =>
    match x with
    | intro xu xl =>
      match y with
      | intro yu yl =>
        let n := height yl
        let (c, zn1) := zero c (n + 1)
        let (c, zn) := zero c n
        let (c, ll) := traditional_multiply c xl yl
        let (c, lu) := traditional_multiply c xl yu
        let (c, ul) := traditional_multiply c xu yl
        let (c, uu) := traditional_multiply c xu yu
        let ll := BinaryNat.intro zn1 ll
        let lu := match lu with
          | intro luu lul => BinaryNat.intro (BinaryNat.intro zn luu) (BinaryNat.intro lul zn)
        let ul := match ul with
          | intro ulu ull => BinaryNat.intro (BinaryNat.intro zn ulu) (BinaryNat.intro ull zn)
        let uu := BinaryNat.intro uu zn1
        let (c, zu) := add c uu lu
        let (c, zl) := add c ul ll
        add c zu zl

end BinaryNat
end Complexity