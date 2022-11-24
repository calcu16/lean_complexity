import data.nat.pow
import data.vector.basic

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

universe u
variables {α : Type u}

structure cost : Type := (value : ℕ)

def costed (a : Type _) := cost → (cost × a)

def cost_inc (a : α) (c: cost):= (cost.mk (c.value + 1), a)

def costed_bit_zero := cost_inc binary_nat.bit_false

def costed_bit_one := cost_inc binary_nat.bit_true

def costed_intro {n : ℕ} (x y : binary_nat n) :=
  cost_inc (binary_nat.intro x y)

def costed_split {n : ℕ} (x : binary_nat (n+1)) :=
  match x with | (binary_nat.intro y z) :=
    cost_inc (y, z)
  end

def costed_bit_and (x y : binary_nat 0) :=
  match x, y with
  | binary_nat.bit_true, binary_nat.bit_true := cost_inc binary_nat.bit_true
  | _, _ := cost_inc binary_nat.bit_false
  end

def costed_bit_or (x y : binary_nat 0) :=
  match x, y with
  | binary_nat.bit_false, binary_nat.bit_false := cost_inc binary_nat.bit_false
  | _, _ := cost_inc binary_nat.bit_true
  end

def costed_bit_xor (x y : binary_nat 0) :=
  match x, y with
  | binary_nat.bit_true, binary_nat.bit_true := cost_inc binary_nat.bit_false
  | binary_nat.bit_false, binary_nat.bit_false := cost_inc binary_nat.bit_false
  | _, _ := cost_inc binary_nat.bit_true
  end

def costed_zero : Π (n), costed (binary_nat n)
| 0 := costed_bit_zero
| (n+1) := λ c₀,
  match costed_zero n c₀ with
  | (c, x) := costed_intro x x c
  end

def costed_add_with_carry : Π {n}, binary_nat n → binary_nat n → binary_nat 0 →
    costed (binary_nat 0 × binary_nat n)
| 0 := λ x y zc c,
  match costed_bit_xor x y c with | (c, z) :=
  match costed_bit_xor z zc c with | (c, z) :=
  match costed_bit_and x y c with | (c, xy) :=
  match costed_bit_and x zc c with | (c, xz) :=
  match costed_bit_and y zc c with | (c, yz) :=
  match costed_bit_or xy xz c with | (c, xy_xz) :=
  match costed_bit_or xy_xz yz c with | (c, zc) :=
    (c, zc, z)
  end end end end end end end
| (n+1) := λ x y zc c,
  match costed_split x c with | (c, xu, xl) :=
  match costed_split y c with | (c, yu, yl) :=
  match costed_add_with_carry xl yl zc c with | (c, zc, zl) :=
  match costed_add_with_carry xu yu zc c with | (c, zc, zu) :=
  match costed_intro zu zl c with | (c, z) :=
    (c, zc, z)
  end end end end end

end costed_binary_nat