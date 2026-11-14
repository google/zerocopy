import Lake
open Lake DSL

package «two_phase_thinlto_pruning» where

@[default_target]
lean_lib «TwoPhaseThinLtoPruning» where
  roots := #[`TwoPhaseThinLtoPruning]
