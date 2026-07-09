import Lake
open Lake DSL

package «egpt» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib InformationTheory where
  srcDir := "."

require mathlib from "../../../../../Lean/mathlib4"
