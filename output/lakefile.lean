import Lake
open Lake DSL

package «output» where
  name := "output"

-- All deps are PATH deps into polib's already-built package set, so this
-- viewing workspace shares polib's mathlib rev (v4.30.0) and its .olean
-- artifacts — nothing is downloaded or rebuilt, and `import Inventory`
-- resolves for the proof artifacts under conjecture_without_ce/.
require mathlib from "../polib/.lake/packages/mathlib"
require batteries from "../polib/.lake/packages/batteries"
require aesop from "../polib/.lake/packages/aesop"
require Qq from "../polib/.lake/packages/Qq"
require Cli from "../polib/.lake/packages/Cli"
require importGraph from "../polib/.lake/packages/importGraph"
require LeanSearchClient from "../polib/.lake/packages/LeanSearchClient"
require plausible from "../polib/.lake/packages/plausible"
require proofwidgets from "../polib/.lake/packages/proofwidgets"
require polib from "../polib"

@[default_target]
lean_lib Output where
  roots := #[`Output]
