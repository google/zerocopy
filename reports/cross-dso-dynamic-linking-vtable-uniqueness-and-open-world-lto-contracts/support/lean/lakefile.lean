import Lake
open Lake DSL

package «cross_dso_link_world» where

@[default_target]
lean_lib «CrossDsoLinkWorldContract» where
  roots := #[`CrossDsoLinkWorldContract]
