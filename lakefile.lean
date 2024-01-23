import Lake
open Lake DSL

package complexity

@[default_target]
lean_lib Lib
@[default_target]
lean_lib HMem
@[default_target]
lean_lib Complexity

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
