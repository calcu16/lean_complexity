import Lake
open Lake DSL

package complexity

@[default_target]
lean_lib Complexity

@[default_target]
lean_lib HMem

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
