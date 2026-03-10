// We define these codegen benchmarks in a dedicated `#![no_std]` crate rather
// than treating them as standard `[dev-dependencies]` of the main `zerocopy`
// crate. This isolation allows us to compile instruction set architecture
// targets like `thumbv7m` or `riscv32imc` without accidentally pulling in
// `std`-dependent test harness crates which causes hard cross-compilation
// failures.
#![no_std]
include!(concat!(env!("OUT_DIR"), "/benches.rs"));
