import Lake
open Lake DSL

package «grid_ham» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «GridHam» where
