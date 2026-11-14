import Lake
open Lake DSL

package «regalloc_cert» where
  moreLeancArgs := #["-O3"]

@[default_target]
lean_lib «RegAllocCert» where
  roots := #[`RegAllocCert]
