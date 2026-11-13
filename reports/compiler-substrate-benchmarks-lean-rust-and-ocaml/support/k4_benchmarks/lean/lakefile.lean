import Lake
open Lake DSL

package k4_bench_lean where
  moreLeancArgs := #["-O3"]

@[default_target]
lean_exe k4_bench_lean where
  root := `K4Bench
