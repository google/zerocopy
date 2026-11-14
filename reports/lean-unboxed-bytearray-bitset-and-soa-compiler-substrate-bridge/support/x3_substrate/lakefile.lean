import Lake
open Lake DSL

package «x3_substrate» where
  moreLeancArgs := #["-O3"]

lean_lib «BitSet64» where
  roots := #[`BitSet64]

@[default_target]
lean_exe «x3_bench» where
  root := `X3Bench
