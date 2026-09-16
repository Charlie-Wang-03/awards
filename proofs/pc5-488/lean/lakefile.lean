import Lake
open Lake DSL

package pc5_488

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

@[default_target]
lean_lib PC5488
