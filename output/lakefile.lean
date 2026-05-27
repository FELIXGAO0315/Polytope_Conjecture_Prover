import Lake
open Lake DSL

package «output» where
  name := "output"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Output where
  roots := #[`Output]
