import Lake
open Lake DSL

package «truthmaker» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «Core» where
  -- add library configuration options here

lean_lib «Extensions» where
  -- add library configuration options here

lean_lib «Problems» where
  -- add library configuration options here

lean_lib «Experiments» where
  -- add library configuration options here

@[default_target]
lean_lib «TruthmakerProject» where
  -- add library configuration options here
