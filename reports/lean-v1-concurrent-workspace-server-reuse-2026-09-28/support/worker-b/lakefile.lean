
import Lake
open Lake DSL

-- Aeneas rev: 42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4
require aeneas from "../../toolchain/anneal/toolchain/f44ae6414b534f9610dc52f7356cf8ddd4d173d555fcdb99a33d43bce5cf3e9e/aeneas/backends/lean"

package anneal_verification

@[default_target]
lean_lib «Generated» where
  srcDir := "generated"
  roots := #[`Generated, `RelocateProbeRelocateProbe93d79f43b0c543cb.Funs, `RelocateProbeRelocateProbe93d79f43b0c543cb.Types]

@[default_target]
lean_lib «Anneal» where
  srcDir := "anneal"
  roots := #[`Config, `Anneal]

lean_lib «User» where
  srcDir := "user"
