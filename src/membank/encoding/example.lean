import tactic
import membank.basic
import complexity.basic
import complexity.core
import membank.encoding.basic
import membank.encoding.list

namespace membank
namespace encoding

def nat_cmp: program ℕ :=
[ -- 1 a [1 b _]
  instruction.binary_op (λ a b, ite (a < b) 0 1) [] [source.imm 0] [source.imm 1, source.imm 0],
  -- (a≥b) null [1 b _]
  instruction.clear [source.imm 0],
  -- (a≥b) null null
  instruction.clear [source.imm 1]
]

instance : complexity.has_encoding (runtime_model ℕ) ℕ := ⟨ ⟨ bank.null.setv, begin
  intros x y,
  rw [bank.equiv_iff],
  simp [bank.setv, bank.getv],
  intros h a,
  rw [h],
end ⟩ ⟩

instance (α: Type*): inhabited (frame α) := ⟨ ⟨ [], [], bank.null ⟩ ⟩

def decode_list: bank ℕ → list ℕ
| bank.null := []
| (bank.mem 1 f) := (f 0).getv :: (decode_list (f 1))
| (bank.mem _ _) := []
def mk_list: list ℕ → bank ℕ := complexity.encode (runtime_model ℕ)
def push_list: list ℕ → bank ℕ → bank ℕ := λ xs, push_arg (mk_list xs)

def test: list (frame ℕ) := ((stack.step^[1000]) ((merge_sort nat_cmp).apply (push_list [9, 3, 6, 5, 2] bank.null))).val

#eval 1

#eval (list.length test) -- 1
#eval list.length (frame.current (list.ilast test)) -- 0
#eval decode_list (frame.register (list.ilast test)) -- [2, 3, 5, 6, 9]


def test2: (stack ℕ × ℕ) := stack.step_count ((merge_sort nat_cmp).apply (push_list [9, 3, 6, 5, 2] bank.null)) 1000

#eval decode_list test2.snd
#eval decode_list (frame.register (list.ilast test2.fst.val))

end encoding
end membank