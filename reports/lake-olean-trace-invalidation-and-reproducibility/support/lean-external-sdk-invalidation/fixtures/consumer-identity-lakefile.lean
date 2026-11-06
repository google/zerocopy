import Lake
open Lake DSL
package probe_consumer
@[default_target] lean_lib Client where
  roots := #[`Client, `SdkIdentity]
