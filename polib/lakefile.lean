import Lake
open Lake DSL

package "polib" where
  name := "polib"

require "leanprover-community" / "mathlib" @ git "v4.30.0"

lean_lib Inventory where
  roots := #[`Inventory]

lean_lib Polib where
  roots := #[`Polib]
