import Lake

open Lake DSL

package complexity

@[default_target]
lean_lib Complexity

@[default_target]
lean_exe complexity where
  root := `Main

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require std from git "https://github.com/leanprover/std4" @ "main"