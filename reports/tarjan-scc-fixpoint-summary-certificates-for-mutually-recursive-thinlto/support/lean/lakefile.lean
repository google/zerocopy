import Lake
open Lake DSL

package «thinlto_scc_fixpoint» where

@[default_target]
lean_lib «ThinLtoSccFixpointProofs» where
  roots := #[`ThinLtoSccFixpointProofs]
