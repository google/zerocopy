import Lake
open Lake DSL
package probe_dep where
  version := v!"1.0.0"
@[default_target]
lean_lib Dep
