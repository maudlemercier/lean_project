import Lake
open Lake DSL

package «lean_project»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.20.0"

@[default_target]
lean_lib «LeanProject» where
  -- add any library configuration options here
