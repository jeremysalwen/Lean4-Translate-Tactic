import Lake
open Lake DSL

package «translate» {
  -- add package configuration options here
}

lean_lib «Translate» {
  -- add library configuration options here
}

require std from git "https://github.com/leanprover/std4" @ "main"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
