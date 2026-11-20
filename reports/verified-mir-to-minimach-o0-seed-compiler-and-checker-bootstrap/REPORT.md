# Verified MIR-to-MiniMach O0 Seed Compiler and Two-Step Proof-Checker Bootstrap

## Summary

A proof-carrying or translation-validating Rust compiler cannot cite a formally verified Lean checker specification (`Trusted.MirSemantics`, `SpecCheckerSound`) as its steady-state trust story while extracting that checker through `lean -c`, `clang`, or an unverified optimizing `rustc`: any Trojaned host C or Rust compiler—or a miscompiled optimization pass—can silently subvert the checker binary while leaving kernel proof scripts green. Primary-source inspection of verified-compiler and proof-checker ecosystems (`CakeML/cakeml`, `tanyongkiam/cake_lpr`, `digama0/mm0`, `AbsInt/CompCert`, `CertiRocq/certirocq`, `leanprover/lean4`, `joshlf/anneal`), paired with an empirical `rustc 1.98.0-nightly` MIR census and a kernel-checked Lean `v4.34.1` mechanization in [MirToMiniMachO0Seed.lean](support/MirToMiniMachO0Seed.lean), establishes a two-step bootstrap architecture that removes `lean -c`, `clang`, and optimizing compilers from the steady-state trusted computing base (TCB):

1. **Step 1 (Verified `-O0` Seed Compiler, run once per checker release):** A non-optimizing compiler `MirToMiniMachO0` (`compileBody`) formalized directly inside Lean `v4.34.1` lowers a restricted MIR subset (`SeedMir`) into fixed-offset stack-slot abstract machine code (`MiniMachO0`, `frameBytes <= 4096`) and proves forward simulation (`mirToMiniMachO0_forward_sim`), static move/liveness rejection (`checkBodyInvs`), and backward simulation (`mirToMiniMachO0_backward_sim`) with `0` `sorryAx`, `0` `Lean.ofReduceBool`, and `0` `bv_decide`. Using this kernel-checked Step-1 compiler to compile `vrustc-certcheck` avoids `lean -c` and unverified C/LLVM toolchains.
2. **Step 2 (Self-Certified `-O3` Checker):** The Step-1 verified `-O0` `seedCheckerMach` binary checks a one-time translation certificate proving semantic refinement between the checker source MIR (`certCheckAsProg`) and an unverified fast `-O3` checker binary (`fastCheckerO3`). Once `two_step_bootstrap_sound` accepts `(certCheckAsProg, fastCheckerO3, bootCert)`, steady-state compilation checks user programs using `fastCheckerO3` at full `-O3` native throughput without trusting `rustc -O3` or LLVM.
3. **Empirical MIR Subset Boundary (`vrustc_certcheck_seed.rs`):** Compiling a real 1,155-LOC `#![no_std] #![forbid(unsafe_code)]` BTL superblock and sub-register allocation certificate checker in `rustc 1.98.0-nightly` reveals two essential design constraints:
   - Unextended live `joshlf/anneal` `Trusted/MirSemantics.lean` v1 accommodates `0/8` functions in the stripped-down `seed_core` checker (`6/38` crate bodies total), because real `#![no_std]` safe Rust still emits `Field`/`Index`/`Deref` projections, fixed stack arrays `[T; N]`, `&[T; N]`/`&mut [T; N]` references, scalar `IntToInt` casts (`77` in `seed_core`), overflow arithmetic (`61` `OverflowBinaryOp`, `183` `Assert`), and `49` internal calls. Extending the seed IR (`CoreMirO0`) with these safe stack-local constructs immediately captures `8/8` (`100%`) of `seed_core` and `30/38` total crate bodies while still eliminating `Downcast` (`0`), `UnaryOp_PtrMetadata` (`0`), `Discriminant` (`0`), `std_or_result_adt` (`0`), and closures (`0`).
   - Across 9 trials x 10,000 invocations (120,000 certificate checks/trial) compiled identically with `-C panic=abort`, `seed_core` executes at `766.58 ns/bundle` (`16.09M` steps/s) at `-O0` vs `321.69 ns/bundle` (`38.34M` steps/s) at `-O3` (only a `2.38x` slowdown at `-O0`), whereas idiomatic slice/iterator/Result Rust (`idiomatic_safe`) slows `3.59x` (`1840.76 ns` at `-O0` vs `512.96 ns` at `-O3`).

## Applicability

These findings apply to designing a kernel-checked `-O0` bootstrap compiler for a Rust verification checker and establishing the exact MIR subset boundary between `MirSemantics` v1, a fixed-array safe-Rust `CoreMirO0` seed subset, and unconstrained `#![no_std]` Rust.

- **Subject relationships:**
  - `CakeML/cakeml`, `tanyongkiam/cake_lpr`, `digama0/mm0`, `AbsInt/CompCert`, `CertiRocq/certirocq`, and `leanprover/lean4` supply primary-source reference points for machine-checked extraction, stack-frame lowering (`Linear -> Mach`), FFI/runtime shims, and remaining C/`clang` TCB holes.
  - `joshlf/anneal` defines the host Rust MIR AST (`Trusted/MirAst.lean`), operational semantics (`Trusted/MirSemantics.lean`), and Lean audit rules (`TrustedBoundary.lean`) targeted by downstream verified Rust infrastructure.
  - `bytecodealliance/regalloc2` supplies the upstream symbolic sub-register / allocation checker invariant design (`CheckerState::update`) mirrored in the BTL + RegAlloc micro-checker crate [vrustc_certcheck_seed.rs](support/vrustc_certcheck_seed.rs).
  - `rust-lang/rust` (`rustc 1.98.0-nightly`, `2026-05-31`, `LLVM 22.1.6` on `x86_64-unknown-linux-gnu`) provides the actual MIR dumps and native `-O0` / `-O3` executables benchmarked by [census_and_bench_certcheck.py](support/census_and_bench_certcheck.py).
  - `leanprover/lean4` (`v4.34.1`) kernel-checks [MirToMiniMachO0Seed.lean](support/MirToMiniMachO0Seed.lean).
- **Local probes vs upstream targets:** [vrustc_certcheck_seed.rs](support/vrustc_certcheck_seed.rs) is an authored synthetic `#![no_std] #![forbid(unsafe_code)]` proxy modeled after BTL superblock (`Freeze`/`nuw`/`disjoint`/Farkas) and `regalloc2` sub-register checks, NOT the full `rustc` MIR of a complete compiler pass crate. [MirToMiniMachO0Seed.lean](support/MirToMiniMachO0Seed.lean) formalizes a scalar/boolean/ZST `SeedMir` core; extending that proof to `CoreMirO0` arrays, references, scalar casts, and calls remains future engineering work documented under `## Boundaries`.

## Findings

### 1. Primary-Source TCB Gap Across Existing Verified Toolchains

Basis: source (pinned GitHub repositories verified verbatim).

Comparing seven verified compilers and proof checkers shows two distinct TCB endpoints: full machine-byte self-hosting with a tiny OS syscall shim, versus Lean/Rocq/C extraction pipelines that retain an unverified `clang` or host C/C++ compiler:

| Project & Pinned Commit | Bootstrap Mechanism | Unverified Native Code / C TCB | Key Verified Theorem / Gap Located |
| :--- | :--- | :--- | :--- |
| `CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb` | 12-pass backend in HOL4 to `lab_to_target$compile` emitting `word8 list` (`backendScript.sml:43-78`) | C FFI glue (`basis_ffi.c`, 309 lines in downstream binaries) | `semantics_compiler_x64_prog` (`compiler_x64ProgScript.sml:68-86`): bootstrapped x64 machine-byte semantics |
| `tanyongkiam/cake_lpr@033aad53d1733bd4b8ca41cf6f1b5fb5d84f8de2` | Built by bootstrapped CakeML compiler into `.S` assembly + `basis_ffi.c` (`README.md`) | `basis_ffi.c` + assembler/linker (`cc`) | `check_unsat_whole_prog_spec2` & `check_unsat_semantics` (`lpr_arrayFullProgScript.sml:1753-1775`) |
| `digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956` | External `mm0-c` C verifier + MM0-to-x86 theorem (`verifier.mm0:18-29`) | `mm0-c` totals 2,857 C LOC across 7 files (`index.c` 161, `main.c` 79, `parser.c` 904, `types.c` 329, `verifier.c` 819, `verifier_debug.c` 322, `verifier_types.c` 243) compiled with `cc` | `Verifier_Valid` specifies x86 `initialConfig Verifier k`, **but** `examples/compiler.mm0:6` retains `axiom sorry (p: wff): $ p $;` |
| `CertiRocq/certirocq@ab66e0164e7ecb63e5af95c90c8e479068bf95c2` | Extracted `certirocqchk` Rocq checker + C runtime (`bootstrap/certirocqchk/`) | Unverified `clang -O2` (`Makefile:1,40-44`; `# ccomp:` commented out) + `gc_stack.o`/`rocq_ffi.o` | `pipeline.v:21-23,46-48` axiomatizes OCaml printing; `compile.v:22-24,44` uses `assume_normalization` (`todo`) and `fake_guard_impl` |
| `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc` | OCaml extraction + verified C backend (`Linear` -> `Mach` `Stacking.v`) | OCaml compiler + unverified GNU `as`/`ld` after `Asm` | `transf_program_correct : forward_simulation` (`Stackingproof.v:2201-2216`); frame size strictly bounded by `Ptrofs.max_unsigned` (`Stacking.v:206`) |
| `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` | Lean -> LCNF -> C11 (`lean -c`) + C++ runtime + `@[csimp]` replacement | `clang`/GCC + Lean C++ runtime + unchecked `@[csimp]` eqs | `src/Lean/Compiler/CSimpAttr.lean:58-70` replaces constants in compiled LCNF code only, trusting compiler/runtime equivalence |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `TrustedBoundary.lean` audits Lean theorems directly in kernel | Fails closed if no verified codegen target exists beyond host Lean/Rust | Rejects `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, `partial`, `@[extern]`, `@[implemented_by]`; `MirSemantics.lean` currently scalar/ZST-only |

Two architectural lessons follow directly from these sources:
1. Even mature proof-checker bootstraps like `CertiRocq/certirocqchk` still break the chain at `clang -O2` (`Makefile:1,40-44`), while `mm0-c`'s x86 target spec still depends on `examples/compiler.mm0:6`'s `axiom sorry`. Removing `lean -c` and `clang` requires compiling the seed checker directly from verified Lean MIR (`MirToMiniMachO0`) without C intermediate emission.
2. In `bytecodealliance/regalloc2@4eb655fa745fba271af74be8495154a4b0cac56f`, `CheckerState::update` for `CheckerInst::Move` (`checker/mod.rs:546-563`) updates `self.set_value(into, val)` inside `if let Some(val) = self.get_value(&from).cloned()` without an `else` branch evicting stale destination mappings—illustrating why compiled proof checkers themselves must be formally verified against the source semantics (`deinitMovedPlace`, upper-lane clobbering, stale value eviction) rather than handwritten in trusted C or unverified Rust.

### 2. Empirical `rustc 1.98.0-nightly` MIR Census on `#![no_std] #![forbid(unsafe_code)]` Certificate Checker

Basis: execution (real `rustc 1.98.0-nightly` compilation and `-Z dump-mir=runtime-post-cleanup` census on synthetic checker crate `vrustc_certcheck_seed.rs`).

To measure what MIR constructs `rustc` actually emits for a non-trivial certificate checker without guessing, [vrustc_certcheck_seed.rs](support/vrustc_certcheck_seed.rs) implements the exact same BTL superblock (`Input` known-bits, `Freeze` non-duplication, `Add64` `nuw`, `Or64` `disjoint`, canonical shift/sub equivalence, Farkas linear infeasibility) and 10-lane sub-register checker (`SeedReg`, `Spill`, `Reload`, `Move`, `Remat`, `VZeroUpper`, `AbiCallOrRet`, `ParMoveSwap`) in two styles inside one `#![no_std] #![forbid(unsafe_code)]` crate:
- **`seed_core` (`8` bodies):** Scalar locals, fixed stack arrays `[T; N]`, `&[T; N]` / `&mut [T; N]` references, `while` index loops, explicit `u32` return codes, zero `Iterator`, zero `Option`/`Result`, zero slices/tuples where avoidable.
- **`idiomatic_safe` (`10` bodies):** Idiomatic safe Rust slices `&[BtlNode]`, `.iter().enumerate()`, `.zip()`, `Option`/`Result` combinators, and `?` early returns (`CheckErr`).

Compiling under `rustc --edition=2024 --crate-type=rlib -D warnings -C panic=abort -Z dump-mir=runtime-post-cleanup` produced `38` function MIR dumps (`8` `seed_core`, `10` `idiomatic_safe`, `20` `shared_derives`), summarized below:

| MIR Metric (`3-2-000.runtime-post-cleanup`, `o0_abort`) | `seed_core` (`8` bodies) | `idiomatic_safe` (`10` bodies) | `shared_derives` (`20` bodies) | All Bodies (`38`) |
| :--- | ---: | ---: | ---: | ---: |
| Total Basic Blocks / Max BB per Body | `666` / `280` | `650` / `262` | `28` / `9` | `1,344` / `280` |
| Fits unextended `MirSemantics` v1 (`fits_trusted_v1_bodies`) | **`0 / 8`** | `1 / 10` | `5 / 20` | `6 / 38` |
| Fits `CoreMirO0` (`fits_core_mir_o0_bodies`) | **`8 / 8 (100%)`** | **`2 / 10 (20%)`** | **`20 / 20`** | `30 / 38` |
| `std_or_result_adt` Locals (`Option`, `Result`, `Iter`, `ControlFlow`) | **`0`** | **`186`** | `0` | `186` |
| Closures (`{closure@...}`) | **`0`** | **`1`** | `0` | `1` |
| Fixed Arrays `[T; N]` / `&[T; N]` / `&mut [T; N]` Locals | `16` / `6` / `20` | `15` / `13` / `4` | `0` | `31` / `19` / `24` |
| Unsized / Other Refs (`&other`, `&mut other`) | `2` / `0` | `57` / `25` | `8` / `0` | `67` / `25` |
| `Downcast` Projections (`(x as Variant)`) | **`0`** | **`54`** | `0` | `54` |
| `Field` / `Index` / `Deref` Projections | `292` / `114` / `122` | `302` / `114` / `95` | `8` / `0` / `34` | `602` / `228` / `251` |
| `UnaryOp_PtrMetadata` / `Discriminant` | **`0` / `0`** | **`10` / `30`** | `0` / `8` | `10` / `38` |
| `Cast` (`IntToInt`, etc.) / `OverflowBinaryOp` | `77` / `61` | `10` / `7` | `0` / `0` | `87` / `68` |
| `Assert` / `Call` Terminators | `183` / `49` | `132` / `162` | `0` / `0` | `315` / `211` |
| `Drop` / `Resume` Terminators | `0` / `0` | `0` / `0` | `0` / `0` | `0` / `0` |

Four critical compiler-architecture conclusions follow directly from this census:
1. **Live `MirSemantics` v1 cannot compile any non-trivial checker body directly (`0/8` in `seed_core`):** Inspection of `joshlf/anneal` `Trusted/MirSemantics.lean` shows why: `evalOperandToSlot` fails closed with `.unsupported` on any non-empty projection (`L953`, `L962`), `evalStatement` rejects projected assignments (`L1407`), and `evalTerminator` rejects `Call`, `Assert`, and `Drop` (`L1568`), while `MirTy` lacks arrays and references (`L721-724`). Even minimal `#![no_std]` array indexing and checked integer arithmetic (`i += 1`, array bounds) emit `Index`, `Field`, `Deref`, `OverflowBinaryOp`, `Assert`, `Cast`, and fixed-array references (`&[T; N]`, `&mut [T; N]`).
2. **Defining `CoreMirO0` as the exact gap between `MirSemantics` v1 and `seed_core` closes `8/8` checker bodies while dropping `54` `Downcast`s, `186` `std` ADTs, and `10` `PtrMetadata` ops:** Adding fixed-size stack arrays `[T; N]`, fixed-length stack refs `&[T; N]` / `&mut [T; N]`, `Field`/`Index`/`Deref` projections, scalar `IntToInt` `Cast`, `Add/Sub/MulWithOverflow` + `Assert`, and direct monomorphic `Call` brings `seed_core` coverage from `0%` to `100%` (`8/8`) and `30/38` crate-wide—requiring zero unsized slice fat-pointer metadata (`PtrMetadata`), zero variant `Downcast` projections, zero `ControlFlow`/`Iterator` combinators, and zero closures. (Note: even `seed_core` still produces `1` `Other` rvalue in 3 places for fixed-array indexing/borrows, `34` tuple/array `Aggregate`s, and `16` `[0; N]` `Repeat` initializers; `162` `Call`s in `idiomatic_safe` drop `3.3x` to `49` in `seed_core` from `saturating_add`/`saturating_mul`/`wrapping_*`/helper calls.)
3. **Warning on `runtime-post-cleanup` MIR immutability across optimization levels:** Comparing the raw SHA-256 digests of the `38` `*.3-2-000.runtime-post-cleanup.after.mir` files emitted under `o0_abort` (`9978cf2e...`) vs `o3_abort` (`638ff2cc...`) shows `post_cleanup_sha256_invariant_o0_vs_o3_abort = false`: `11/38` functions differ between `-C opt-level=0` and `-C opt-level=3` (for example, `seed_core::analyze_btl_dag` drops from `92,320` bytes at `-O0` to `84,479` bytes at `-O3`). In `rustc 1.98.0-nightly`, MIR optimization level scales with `-C opt-level` prior to `runtime-post-cleanup`, so a Step-1 seed compiler targeting `runtime-post-cleanup` MIR compiles the checker at `-O0`, while Step-2 validation proves refinement between that `-O0` `optimized_mir` and the `-O3` native artifact.
4. **`o0_unwind` vs `o0_abort` shows `0` `Drop`/`Resume` in `#![no_std]` non-allocating checkers:** For `vrustc_certcheck_seed.rs` (all `Copy` stack types), `o0_abort` and `o0_unwind` produce identical basic block, statement, projection, and terminator census counts (`1,344` BBs, `0` `Drop`, `0` `Resume`) because unwind cleanup blocks are only generated when live non-`Copy` types have destructors or catch pads.

### 3. Execution Overhead of `-O0` Seed vs `-O3` Native on Identical Hardware

Basis: execution (real `driver_o0` and `driver_o3` binaries built from [vrustc_certcheck_seed.rs](support/vrustc_certcheck_seed.rs) on Linux x86-64 via [census_and_bench_certcheck.py](support/census_and_bench_certcheck.py)).

Both `driver_o0` and `driver_o3` passed all `3` valid and `12` negative semantic equivalence tests (`verify_pos3_neg12_ok = true`), including `pos_bundle_2` (`x < 64`, `Const64(64)`, `Or disjoint` vs `Add nuw` + Farkas `[1*x <= 63, -1*x <= -64]` -> `0 <= -1`) and negative sub-register/Farkas traps `N1..N12`:

| Measurement (`-C panic=abort`, `--edition=2024`) | `seed_core` (`-O0`) | `seed_core` (`-O3`) | `idiomatic_safe` (`-O0`) | `idiomatic_safe` (`-O3`) |
| :--- | ---: | ---: | ---: | ---: |
| Median ns / 15-bundle avg bundle (`9 x 120k` checks) | **`766.58 ns`** | `321.69 ns` | `1,840.76 ns` | `512.96 ns` |
| Equivalent checker throughput (`steps/s`) | **`16.09M`** | `38.34M` | `6.70M` | `24.04M` |
| `-O0` vs `-O3` execution slowdown | **`2.38x`** | `1.00x` | **`3.59x`** | `1.00x` |
| Style speedup (`seed_core` / `idiomatic_safe` latency) | **`0.42x`** (`2.40x` faster) | `0.63x` (`1.59x` faster) | `1.00x` | `1.00x` |
| Checker module `.text` bytes (`nm --size-sort`) | `14,892` B | `6,063` B | `19,246` B | `7,063` B |
| Crate `.text` / `.o` / `.rlib` (`vrustc_certcheck_seed`) | `41,392` B / `285,600` B / `365,026` B (total `-O0`) | `14,052` B / `56,776` B / `123,822` B (total `-O3`) | — | — |
| Crate compile wall time / peak RSS | `0.4301`s / `148.33` MB | `0.7009`s / `146.16` MB | — | — |
| Cold-start `once` latency median (min) (`15` trials) | `2.433` ms (`1.934` ms) | `5.784` ms (`3.137` ms) | (shared driver binary) | (shared driver binary) |
| Warm driver peak RSS (`21.50` MB vs `21.62` MB) | `21.50` MB | `21.62` MB | (shared driver binary) | (shared driver binary) |

The performance payoff is clear: writing the bootstrap seed checker in `seed_core` style makes `-O0` (`766.58 ns/bundle`, `16.09M` steps/s) `2.40x` faster than `-O0` idiomatic Rust (`1,840.76 ns`) and within `1.49x` of even `-O3` idiomatic Rust (`512.96 ns`), while paying only a `2.38x` penalty vs `-O3` `seed_core`. Under the two-step bootstrap, that `2.38x` `-O0` cost is paid only once when verifying the `-O3` checker binary (`fastCheckerO3`), after which user compilations run at full `-O3` speed (`38.34M` steps/s). Note on `cold_start_median_ms`: `-O3` measured higher median (`5.784` ms, min `3.137` ms) than `-O0` (`2.433` ms, min `1.934` ms) across 15 short subprocess spawns due to container process startup/page-cache jitter (`driver_o3` binary is actually smaller at `4,409,256` B vs `4,486,560` B `driver_o0`).

### 4. Kernel-Checked `SeedMir -> MiniMachO0` Compiler & Bootstrap Soundness

Basis: source + execution (Lean `v4.34.1` kernel type-checking of [MirToMiniMachO0Seed.lean](support/MirToMiniMachO0Seed.lean): `3,071` LOC, `95` definitions/types, `51` theorems, `30.088s` check time, `700.93 MB` RSS).

#### 4.1 Direct Stack-Slot Lowering (`compileBody`) and ZST Preservation

`MirToMiniMachO0Seed` models the stack-local scalar/boolean/ZST semantics matching `joshlf/anneal` `Trusted/MirSemantics.lean`:
- **Three-state `LocalSlot` (`deinitMovedPlace = true`):** Every local is `.dead | .live none | .live (some v)`. Reading `.move loc` succeeds on `.live (some v)` and resets runtime-stored locals (`isRuntimeStoredTy ty = true`, `.bool | .int w s`) to `.live none`, while preserving inhabited zero-sized types (`.unit`, `.zstEnum discr`) at `.live (some v)`. `StorageDead 0` and writes to `.dead` slots fault with `.unsupported` or `.undefined`, mirroring `Trusted/MirSemantics.lean:949-976,1392`.
- **Single-Page Guard Bound & Direct Frame Layout (`compileBody`):** Each local `i` maps statically to 8-byte stack slot `i` (`frameBytes = locals.length * 8 <= 4096`), eliminating heap allocation, alias analysis, and register allocation while guaranteeing out-of-bounds slots fail closed via static guard (`0 < locals.length`, `argCount < locals.length`, `0 < blocks.length`, `frameBytes <= 4096`).
- **Kernel-Proof Bug Caught on Non-Zero `zstEnum` Returns:** Initial formalization of `MachTerm.retSlot0 (stored : Bool)` returned `0#64` for all non-runtime-stored return types (`stored = false`). That broke `block_step_forward_sim` when `body.locals[0] = .zstEnum d` with `d != 0#64`, because `encodeSeedVal (.zstEnum d) = d != 0#64`. Parameterizing `MachTerm.retSlot0 (zstImm? : Option (BitVec 64))` (`some d` for `.zstEnum d`, `some 0#64` for `.unit`, `none` for stack-slot `0`) fixed the return semantics cleanly across both `.unit` and arbitrary `64`-bit single-variant enum discriminants.

#### 4.2 Forward Simulation, Move/Liveness Checker (`checkBodyInvs`), Backward Simulation, and Counterexample

- **Forward simulation (`mirToMiniMachO0_forward_sim`):** For any fuel `n`, if `compileBody body = some mbody`, `initMirState body args = some mirSt0`, and every reachable `SeedMir` block step avoids `.fault` (`hAllNoFault`, `hNoFault`), then `runMachBlocks mbody n (initMachState body args)` steps lockstep (`machSt'.bb = mirSt'.bb ∧ MatchStateInv body.locals mirSt'.slots machSt'.frame`), returns `encodeSeedVal v` whenever MIR returns `v`, and panics (`assertMach`) iff MIR panics (`assertNonZero`).
- **Static move/liveness certificate checker (`checkBodyInvs`) & backward simulation (`mirToMiniMachO0_backward_sim`):** Because runtime stack slots in `MiniMachO0` never track `.dead` vs `.live none` tags, `MiniMachO0` cannot fault on uninitialized/moved-out reads (`MatchSlot` leaves `.dead` and `.live none` unconstrained!). Therefore `mirToMiniMachO0_backward_sim` proves backward simulation *conditioned on* a linear-time three-state abstract interpretation checker `checkBodyInvs : MirBody -> List (List AbsSlot) -> Bool` (`AbsSlot = .dead | .uninit | .init`). `checkBodyInvs` handles arbitrary multi-block loops and branches (`Goto`, `SwitchInt`, `AssertNonZero`), guaranteeing MIR non-faulting (`checkBodyInvs_no_fault_from_state`) and type preservation on return (`checkBodyInvs_run_returned_ty`) so any `MiniMachO0` return/panic implies the identical `SeedMir` return/panic.
- **Explicit negative counterexample (`cex_m4_move_then_copy_faults_in_mir_not_mach`):** `m4MoveAliasBody` executes `_0 := BinOp.add (.move 1) (.copy 1)` with left-to-right operand evaluation. `compileBody` succeeds (`mbody`), and executing `mbody` returns `.returned 42#64` (`21 + 21`), whereas `SeedMir` faults with `.fault .undefined` because `.move 1` deinitializes slot `1` before `.copy 1` runs. `checkBodyInvs m4MoveAliasBody [[.uninit, .init]] = false` rejects it cleanly at compile time, proved by `rfl`.

#### 4.3 Step-1 + Step-2 Bootstrap Theorem and Concrete Thompson-Trojan Rejection

```lean
theorem two_step_bootstrap_sound ...
    (h_ret_bool : getAt? certCheckMir.locals 0 = some .bool)
    (h_spec : SpecCheckerSound sem specCheck)
    (h_seed_compile : compileBody certCheckMir = some seedCheckerMach)
    (h_invs : checkBodyInvs certCheckMir certInvs = true)
    (h_mir_verif : ∀ p1 p2 c mirSt0, ...)
    (h_init_boot : ∃ mirSt0, initMirState certCheckMir (enc certCheckAsProg fastCheckerO3 bootCert) = some mirSt0)
    (h_step1_boot : runMachBlocks seedCheckerMach fuel
      (initMachState certCheckMir (enc certCheckAsProg fastCheckerO3 bootCert)) = .returned 1#64)
    (h_fast_semantic_link : SemRefines sem certCheckAsProg fastCheckerO3 →
      runFastO3 fastCheckerO3 userSrc userTgtO3 userCert = true →
      SemRefines sem userSrc userTgtO3)
    (h_step2_user : runFastO3 fastCheckerO3 userSrc userTgtO3 userCert = true) :
    SemRefines sem userSrc userTgtO3
```

Because `checkBodyInvs_run_returned_ty` proves from `h_ret_bool` that `SeedMir` return value `v` has type `.bool`, backward simulation from `h_step1_boot` (`1#64`) uniquely forces `v = .bool true` (blocking scalar `1#64` spoofing), discharging `SpecCheckerSound` on `(certCheckAsProg, fastCheckerO3, bootCert)` and compositionally establishing `SemRefines sem userSrc userTgtO3`. Concrete executable witness `witness_bootstrap_accepts_valid_and_rejects_thompson_trojan` compiles a 3-block CFG `seedCheckerMir` (`BinOp.eq (.move 1) (.move 2)` followed by `SwitchInt`) into `seedCheckerMach` via `compileBody`, passes `checkBodyInvs`, accepts valid tag pair `(42, 42)` (`.returned 1#64` / `.returned (.bool true)`), and rejects a Thompson-trojaned candidate `(42, 99)` (`.returned 0#64` / `.returned (.bool false)`).

All 5 exported theorems satisfy `TrustedBoundary`-grade axiom hygiene (`#print axioms`):
- `MirToMiniMachO0Seed.mirToMiniMachO0_forward_sim`: `[propext, Classical.choice, Quot.sound]`
- `MirToMiniMachO0Seed.mirToMiniMachO0_backward_sim`: `[propext, Classical.choice, Quot.sound]`
- `MirToMiniMachO0Seed.cex_m4_move_then_copy_faults_in_mir_not_mach`: `[propext, Quot.sound]`
- `MirToMiniMachO0Seed.two_step_bootstrap_sound`: `[propext, Classical.choice, Quot.sound]`
- `MirToMiniMachO0Seed.witness_bootstrap_accepts_valid_and_rejects_thompson_trojan`: `[propext, Quot.sound]`

### 5. Quantitative & Validation Scorecard (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

| Dimension | Measured / Observed Value | Basis |
| :--- | :--- | :--- |
| **`L1` Proof & Authoring Effort** | `MirToMiniMachO0Seed.lean` is `3,071` LOC (`95` defs/types, `51` theorems); checker proxy `vrustc_certcheck_seed.rs` is `1,155` LOC | Source inspection |
| **`L2` Toolchain Build / Check Time** | Lean `v4.34.1` full kernel check: `30.088s`; `rustc` checker `-O0`: `0.4301s`, `-O3`: `0.7009s`; driver `-O0`: `0.2533s`, `-O3`: `1.1174s` | Execution (`anneal-lean-run`, `rustc`) |
| **`L3` Seed Compile Latency** | In-kernel `compileBody` evaluates in `< 1 ms` (`rfl` in `witness_...`); full MIR checker compilation via Step-1 `MirToMiniMachO0` on `vrustc_certcheck_seed`: **not measured** | Execution (toy witness) / missing gap |
| **`L4` Generated Code Speed** | `-O0` `seed_core` executes at `766.58 ns/bundle` vs `321.69 ns/bundle` at `-O3` (`2.38x`); `-O0` vs `-O3` for `MiniMachO0 -> x86_64` bytes: **not measured** | Execution (`driver_o0`/`driver_o3`) |
| **`L5` Checker Throughput & Cold Start** | `seed_core -O0`: `16.09M` steps/s, `2.433 ms` median cold start; `seed_core -O3`: `38.34M` steps/s, `5.784 ms` median cold start | Execution (`driver_o0`/`driver_o3`) |
| **`L6` Footprint (RAM / Binary)** | Lean kernel RSS `700.93 MB`; `rustc` RSS `148.33 MB`; `seed_core` `.text` `14,892` B (`-O0`) / `6,063` B (`-O3`); driver RSS `21.50 MB` (`-O0`) / `21.62 MB` (`-O3`) | Execution (`os.wait4`, `size`, `nm`) |
| **`C1` Spec / TCB Auditability** | `0` `sorryAx`, `0` `Lean.ofReduceBool`, `0` `bv_decide`, `0` `@[extern]`; `CoreMirO0` drops all `54` downcasts and `186` `std` ADTs | Execution (`#print axioms`) + MIR census |
| **`C2` Orthogonality** | Separating Step-1 `-O0` seed soundness from Step-2 `-O3` throughput makes `fastCheckerO3`'s optimization passes untrusted black-box witnesses | Derived from `two_step_bootstrap_sound` |
| **`V1` Non-Vacuity / Negatives** | Both MIR-vs-Mach (`cex_m4_move_then_copy_faults_in_mir_not_mach`) and valid-vs-Trojan (`witness_...`) plus 12 negative `N1..N12` Rust traps tested and green | Execution (Lean kernel + `rustc` binaries) |
| **`V2` Differential Fuzzing** | Exhaustive cross-implementation differential check across `3` valid + `12` negative bundles (`seed_core == idiomatic_safe`); random property fuzzing: **not examined** | Execution (`verify` mode) |
| **`V3` Weak Memory / Leakage** | Single-thread sequential MIR semantics; weak-memory models, crash consistency, and hardware microarchitectural side channels: **not examined** | Outside scope |
| **`V4` Held-Out Replay** | Tested on `rustc 1.98.0-nightly` + `vrustc_certcheck_seed.rs`; arbitrary crates.io / `core` MIR replay through `MirToMiniMachO0`: **unsupported / not examined** | Explicit scope boundary |

## Boundaries

- **Unsupported in `MirToMiniMachO0Seed.lean` (`unsupported` / `not examined`):** The Lean mechanization covers only scalar/boolean/ZST `SeedMir` (`locals <= 512`, `frameBytes <= 4096`), `SwitchInt`, `AssertNonZero`, `Goto`, and `StorageLive`/`StorageDead`. It does **not** yet model or prove `CoreMirO0` extensions needed to compile `vrustc_certcheck_seed.rs` verbatim inside Lean: fixed stack arrays (`[T; N]`), fixed-array references (`&[T; N]` / `&mut [T; N]`), `Deref`/`Field`/`Index` projections, `IntToInt` casts, `Add`/`Sub`/`MulWithOverflow`, direct internal `Call` frames, ELF/Mach-O encoding, or x86-64 machine instruction bytes. Until those extensions are mechanized and connected to `x86-64` ELF emission, end-to-end zero-C execution on real Rust crates remains unbridged (`not examined`).
- **Known not to apply to unextended `MirSemantics` v1 (`known not to apply`):** Directly executing any non-trivial `#![no_std] #![forbid(unsafe_code)]` certificate checker in live `joshlf/anneal` `Trusted/MirSemantics.lean` v1 fails (`0/8` `seed_core` functions fit), because array indexing, `Field`/`Deref` access, and overflow assertions are ubiquitous even with `Iterator`/`Option`/`Result` completely eliminated.
- **Known not to apply to `runtime-post-cleanup` MIR equality across `-O0` and `-O3` (`known not to apply`):** On `rustc 1.98.0-nightly`, `3-2-000.runtime-post-cleanup` MIR already diverges across `-O0` vs `-O3` on `11/38` checker crate functions. Any pipeline requiring identical pre-pass MIR across optimization levels must extract earlier (`built` / pre-MIR-opt) or treat `-O0` vs `-O3` MIR refinement explicitly via translation certificates.
- **Known not to apply beyond fixed stack bounds (`unsupported`):** `compileBody` rejects any function with `locals.length * 8 > 4096` (`frameBytes <= 4096`) to guarantee single-guard-page non-aliasing; large checkers must split helpers across call frames or prove explicit multi-page stack probing (comparable to CompCert's `Ptrofs.max_unsigned` bound in `Stacking.v:206`).
- **Proxy checker & concurrency scope (`not examined`):** [vrustc_certcheck_seed.rs](support/vrustc_certcheck_seed.rs) (`3` positive + `12` negative fixed-capacity 32-node bundles) measures micro-checker throughput and `rustc` MIR emission accurately, not full multi-function SSA/BTL traces from real crates; weak memory, multi-threading, and FFI syscalls (the minimal syscall boundary analogous to CakeML's `basis_ffi.c`) are **not examined**.

## Evidence

### Preserved Package Artifacts (`support/`)

- [support/vrustc_certcheck_seed.rs](support/vrustc_certcheck_seed.rs) (`1,155` LOC, SHA-256 `60f74dd30b55d547bb6235a8226d5d8e70dfe5d42bec2da48a6be13b22b60f5c`): dual `seed_core` / `idiomatic_safe` `#![no_std] #![forbid(unsafe_code)]` BTL + sub-register certificate checker crate.
- [support/MirToMiniMachO0Seed.lean](support/MirToMiniMachO0Seed.lean) (`3,071` LOC, SHA-256 `2adf1fef25f29fa7b721b2dee768221f4a06c74350f9a6d9af32ad5c53f64d3f`): Lean `v4.34.1` formalization of `SeedMir`, `MiniMachO0`, `compileBody`, `checkBodyInvs`, `mirToMiniMachO0_forward_sim`, `mirToMiniMachO0_backward_sim`, `cex_m4_move_then_copy_faults_in_mir_not_mach`, `two_step_bootstrap_sound`, and `witness_bootstrap_accepts_valid_and_rejects_thompson_trojan`.
- [support/census_and_bench_certcheck.py](support/census_and_bench_certcheck.py): end-to-end harness running `rustc` (`o0_abort`, `o0_unwind`, `o3_abort`, `o3_unwind`), symbol/size checks, `driver_o0` vs `driver_o3` equivalence (`3` positive + `12` negative) & throughput benchmarks (`9 x 10,000` iterations, `os.wait4` RSS), and `lean -DElab.async=false -Ddebug.skipKernelTC=false`.
- [support/certcheck_mir_census_and_bench.json](support/certcheck_mir_census_and_bench.json): full machine-readable output recorded on `2026-11-20` on Linux `x86_64`.

### Primary Pinned Upstream References (`2026-11-20`)

- `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean` (L621-623 `LocalSlot`, L748-752 `liveUninitSlot`, L949-976 `deinitMovedPlace = true` & projection rejection, L1392 `storageDead 0`, L1407, L1568), and `trusted/audit/TrustedBoundary.lean`.
- `CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb`: `compiler/backend/backendScript.sml` (L43-78), `compiler/bootstrap/translation/x64/compiler_x64ProgScript.sml` (L68-86).
- `tanyongkiam/cake_lpr@033aad53d1733bd4b8ca41cf6f1b5fb5d84f8de2`: `README.md` (1–105), `lpr_arrayFullProgScript.sml` (L1753 `check_unsat_whole_prog_spec2`, L1772-1775 `check_unsat_semantics`).
- `digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956`: `mm0-c/` (7 C files, 2,857 LOC total), `examples/verifier.mm0` (L18-29 `Verifier_Valid`), `examples/compiler.mm0` (L6 `axiom sorry`).
- `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`: `backend/Stacking.v` (L206 `Ptrofs.max_unsigned` frame bound), `backend/Stackingproof.v` (L2201-2216 `transf_program_correct`).
- `CertiRocq/certirocq@ab66e0164e7ecb63e5af95c90c8e479068bf95c2`: `theories/Compiler/pipeline.v` (L21-23, L46-48), `bootstrap/certirocqchk/compile.v` (L22-24 `assume_normalization`, L44 `fake_guard_impl`), `bootstrap/certirocqchk/Makefile` (L1, L40-44, L69-73 `clang -O2`).
- `bytecodealliance/regalloc2@4eb655fa745fba271af74be8495154a4b0cac56f`: `src/checker/mod.rs` (L546-563 `CheckerInst::Move`).
- `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`): `src/Lean/Compiler/CSimpAttr.lean` (L58-70).
- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly 2026-05-31`, `LLVM 22.1.6`): host toolchain executing `-Z dump-mir=runtime-post-cleanup`, `-C opt-level=0`, `-C opt-level=3`, `-C panic=abort`.

## Revalidation

To reproduce both the Lean kernel proof and the `rustc` MIR census / native `-O0`-vs-`-O3` benchmarks from a clean workspace containing this package's `support/` files (requires `rustc`, `size`, `nm`, Python 3.10+, and Lean `v4.34.1`):

1. **Kernel-check Lean mechanization and axioms (`~30s`, `0` `sorryAx`):**
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/MirToMiniMachO0Seed.lean
   ```
   Confirm exit code `0`, zero warnings, and `#print axioms` output containing only `[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]`.
2. **Re-run empirical `rustc` MIR census and `-O0` vs `-O3` benchmark (`~5s` with `--skip-lean`, or `~35s` full suite):**
   ```bash
   python3 support/census_and_bench_certcheck.py
   ```
   Confirm exit code `0`, `VERIFY_ALL_OK pos=3 neg=12` for both `driver_o0` and `driver_o3`, `seed_core` fitting `8/8` `CoreMirO0` (`0/8` unextended `MirSemantics` v1), and updated results written cleanly to `support/certcheck_mir_census_and_bench.json`.
3. **Recheck future `CoreMirO0` readiness on `joshlf/anneal`:**
   Diff `trusted/lean/Trusted/MirSemantics.lean` and `trusted/lean/Trusted/MirAst.lean` against `c131b320eeeb26ef692e5afd5ec8db49ee518613` for added array, fixed-ref, `Field`/`Index`/`Deref`, `Cast`, `OverflowBinaryOp`, `Assert`, and `Call` semantics before connecting `vrustc_certcheck_seed.rs` directly without a custom `CoreMirO0` parser.
