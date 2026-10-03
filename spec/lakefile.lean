import Lake
open Lake DSL

require "leanprover-community" / "mathlib"

package "flexbox" where
  version := v!"0.1.0"

@[default_target]
lean_lib «Layout» where
  -- add library configuration options here

@[default_target]
lean_exe «Harness» where
