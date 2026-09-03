import Lake
open Lake DSL

-- Historical EGPT proof tree (canonical chain, sorry-free P=NP, Lean v4.21.0-rc3).
-- Live work has moved to Lean/EGPT/ (the standalone InformationTheory project).
package Archive where

@[default_target]
lean_lib Archive

lean_lib PPNP

-- Pull in mathlib4 from GitHub
require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"master"
