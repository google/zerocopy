import Lake
open Lake DSL
package probe_dep where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]
@[default_target]
lean_lib Dep
