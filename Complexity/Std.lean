import Complexity.StdComp
import Complexity.StdAdd
import Complexity.StdMul
import Complexity.StdPow

namespace Complexity
namespace Std

def fadd (a b : Nat → Nat) := λ n : Nat => a n + b n
def fmul (a b : Nat → Nat) := λ n : Nat => a n * b n

end Std
end Complexity