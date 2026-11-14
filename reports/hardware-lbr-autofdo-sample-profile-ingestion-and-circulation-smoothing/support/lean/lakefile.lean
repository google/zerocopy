import Lake
open Lake DSL

package «autofdo_circulation» where

@[default_target]
lean_lib «AutoFdoCirculationAndPolarity» where
  roots := #[`AutoFdoCirculationAndPolarity]
