import Lake
open Lake DSL

package hyperbook {
  -- add package configuration options here
}

lean_lib Hyperbook {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe hyperbook {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"