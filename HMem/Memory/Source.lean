import HMem.Memory.Basic

/-!
This file defines the Source data structure which allows for indirect indexing into Memory
in addition static indexing.
-/
namespace HMem
inductive Source
| nil -- indexes at the current location
| imm (hd: Bool) (tl: Source) -- goes left or right depending on hd
| idx (hd tl: Source) -- goes left or right depending on the value of Memory at hd
deriving Repr

namespace Source
def height: Source → ℕ
| nil => 0
| imm _ tl => height tl + 1
| idx hd tl => max (height hd) (height tl) + 1
@[simp] theorem height_imm_tl: tl.height < (imm hd tl).height := Nat.lt_succ_self _
@[simp] theorem height_idx_hd: hd.height < (idx hd tl).height := Nat.lt_succ_of_le (le_max_left _ _)
@[simp] theorem height_idx_tl: tl.height < (idx hd tl).height := Nat.lt_succ_of_le (le_max_right _ _)

def size: Source → ℕ
| nil => 0
| imm _ tl => size tl + 1
| idx hd tl => size hd + size tl + 1
@[simp] theorem size_imm_tl: tl.size < (imm hd tl).size := Nat.lt_succ_self _
@[simp] theorem size_idx_hd: hd.size < (idx hd tl).size := Nat.lt_succ_of_le (Nat.le_add_right _ _)
@[simp] theorem size_idx_tl: tl.size < (idx hd tl).size := Nat.lt_succ_of_le (Nat.le_add_left _ _)


def get: Source → Memory → List Bool
| nil, _ => []
| imm hd tl, m => hd::(tl.get m)
| idx hd tl, m => m.getvp (hd.get m)::tl.get m

@[simp] theorem get_nil: nil.get m = [] := rfl
@[simp] theorem get_imm: (imm hd tl).get m = hd::(tl.get m) := rfl
@[simp] theorem get_idx: (idx hd tl).get m = m.getvp (hd.get m)::(tl.get m) := rfl

def convert (f: Memory → List Bool → β) (m: Memory) (s: Source): β := f m (s.get m)

@[simp] def succ': Source → (Bool × Source)
| nil => (true, nil)
| idx hd tl => (true, idx hd tl)
| imm hd tl => match succ' tl, hd with
  | (false, tl), hd => (false, imm hd tl)
  | (true, tl), false => (false, imm true tl)
  | (true, tl), true =>  (true, imm false tl)

@[simp] def succ (s: Source): Source :=
  match s.succ' with
  | (false, s) => s
  | (true, tl) => .imm false tl

def fromNat: ℕ → Source
| 0 => .nil
| (n+1) => (fromNat n).succ

/-
Level order accessing into Memory
     0
    / \
  1     2
 / \   / \
3   4 5   6
-/
instance: OfNat Source n := ⟨ fromNat n ⟩
@[simp] theorem ofNatZero: (OfNat.ofNat 0:Source) = .nil := rfl
@[simp] theorem ofNatSucc: (OfNat.ofNat (n+1):Source) = succ (OfNat.ofNat n) := rfl

end Source

namespace Memory
def getvs: Memory → Source → Bool := Source.convert getvp
def getms: Memory → Source → Memory := Source.convert getmp
def setvs: Memory → Source → Bool → Memory := Source.convert setvp
def setms: Memory → Source → Memory → Memory := Source.convert setmp

@[simp] theorem getvs_def: getvs m s = m.getvp (s.get m) := rfl
@[simp] theorem getms_def: getms m s = m.getmp (s.get m) := rfl
@[simp] theorem setvs_def: setvs m s = m.setvp (s.get m) := rfl
@[simp] theorem setms_def: setms m s = m.setmp (s.get m) := rfl

end Memory
end HMem
