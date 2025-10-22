import Lake
open Lake DSL

package «lean_project»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "29dcec074de168ac2bf835a77ef68bbe069194c5"

@[default_target]
lean_lib «LeanProject» where
  -- add any library configuration options here
