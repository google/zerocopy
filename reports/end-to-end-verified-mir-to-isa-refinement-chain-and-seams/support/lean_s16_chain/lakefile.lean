import Lake
open Lake DSL

package «s16_chain» where

@[default_target]
lean_lib «S16Chain» where
  roots := #[`S16Chain]
