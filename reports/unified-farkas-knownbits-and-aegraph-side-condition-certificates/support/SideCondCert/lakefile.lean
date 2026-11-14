import Lake
open Lake DSL

package «side_cond_cert» where
  moreLeancArgs := #["-O3"]

@[default_target]
lean_lib «SideCondCert» where
  roots := #[`SideCondCert]
