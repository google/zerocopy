# Supporting Rust for Linux (`torvalds/linux`) with Anneal: Minimal-TCB Verification Architecture

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

This report records the pre-implementation minimal-TCB architecture (`google/zerocopy#4207`) for verifying unmodified Rust-for-Linux (`torvalds/linux@b6a9fa34ce4187cb69d3c588a4bbffc31ce5db8f`, Linux `7.4-rc4`) targets out-of-tree in Anneal (`google/zerocopy@ccf9caacb6abc54b8b2cfd6db114f02cb87276e5`):

1. **Concentrated `unsafe` Authority (`[real measurement]`):** Across `357` non-vendored `.rs` files (`2,208` `unsafe` blocks), **`1,989 / 2,208` (`90.1%`)** sit inside two crates—`rust/kernel/` (`1,870` blocks across `169` files) and `rust/pin-init/` (`119` blocks across `17` files)—while mainline Linux vendors `zerocopy` `0.8.62` (`rust/zerocopy/` `125` files, `rust/zerocopy-derive/` `11` files, `305` `unsafe` blocks).
2. **Authoritative Kbuild `.o.cmd` Capture (Zero Kernel Forks):** An out-of-tree untrusted extractor (`kbuild-extract`, with zero Linux-specific logic in `anneal/trusted/`) parses `.<target>.o.cmd` (`savedcmd_$@`, `source_$@`, `deps_$@`) and `@include/generated/rustc_cfg`, resolves transitive `--extern` DAGs, forwards normalized `RUST_MODFILE`, stages `srctree`/`objtree`/`exttree` cleanly (`OBJTREE` path-prefix rewriting), and preserves Kbuild's `--sysroot=/dev/null`, host proc-macro `.so` digests, and `-Copt-level`/`-Coverflow-checks`/`-Cdebug-assertions` flags without altering `.o`/`.ko` artifacts (`scripts/generate_rust_analyzer.py` / `rust-project.json` is disqualified).
3. **Three Kernel Soundness Seams:** (i) `build_assert!` / `rust_build_error()` lowers to `Terminator::BuildError` (`FaultKind.buildAssert` when `CONFIG_RUST_BUILD_ASSERT_ALLOW=n`, `TerminalOut.aborted` when `=y`) with separate `buildPre` on declared `#[inline(always)]` helpers so safe-`fn` unconditional UB-freedom (`NoUbAndSupported`) stays intact; (ii) `bindings::*` and `439` `rust_helper_*` C shims (`70` `.c` files) verify modularly via out-of-tree `FnContract` stubs, compile-time `_Static_assert` `bindgen` layout checks, `Opaque<T>` (`ByteRole.unionData` + `hasUnsafeCellAt = true` + Ghost ownership tokens), `#[vtable]` `ExternAbi::C` handles, and `PinInit`/`DropGuard` slot contracts; (iii) `rust/kernel/sync/{atomic,rcu}` uses a segregated `Trusted.MirSemantics.Lkmm` axiom interface (differentially validated against `herd7` `tools/memory-model/linux-kernel.cat`, never C11/RC11) plus `{ preemptDepth, irqDisabled, rcuDepth }` `ExecCtx` tokens (`klint` lattice + Clang `-Wthread-safety`) and zero-TCB `AnnealAeneasBridge` safe-driver composition.
4. **Phased Milestones (`M0`–`M2`) & Settled Policy (`D1`–`D6`):** Policy choices `D1`–`D6` settle on out-of-tree `kbuild-extract` + reusable split-action flags (`D1`), `buildPre` (`D2-A`), pinned `rustc 1.98` for M0–M1 (`D3-A`), out-of-tree FFI stubs + `bindgen` `_Static_assert` (`D4-A`), segregated LKMM + generic `InvariantEnv` context tokens (`D5-A`), and an out-of-tree `linux-kernel-anneal` companion repo (`D6-A`).

## Applicability

- **Kernel Target:** Unmodified `torvalds/linux@b6a9fa34ce4187cb69d3c588a4bbffc31ce5db8f` (`Linux 7.4-rc4`, matching `Rust-for-Linux/linux` `rust-next`), specifically `rust/{build_error,compiler_builtins,ffi,bindings/lib,uapi/lib,kernel/*,pin-init/src/lib,macros/{lib,module,vtable},helpers/*,zerocopy/*}`, `drivers/*`, and `tools/memory-model/linux-kernel.cat`.
- **Anneal Platform & Toolchains:** `google/zerocopy@ccf9caacb6abc54b8b2cfd6db114f02cb87276e5` (`anneal/trusted/`, `anneal/docs/`, `exocrate/src/lib.rs`), `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`rustc 1.98.0-nightly`, `CONFIG_RUSTC_VERSION=109800`), `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), `Rust-for-Linux/klint@2fb6a267bde4ce595e384cd9b9b34a5995c0419f`, `AeneasVerif/aeneas@fb44cb400eb6bfe7dce97422ebe8fa748b7e4f9b`, and `AeneasVerif/charon@0490c09eb6218e905fec38ec8ebebc9f796d4b04`.
- **Execution scope:** `64`-bit little-endian targets (`x86_64`, `arm64`, `riscv64`, `loongarch64`) under `-Cpanic=abort` and `CONFIG_KASAN=n`; `32`-bit and big-endian (`s390x`) kernel execution depends on `TargetProfile`/`Program.targetEndian` (`google/zerocopy#4188`).

## Findings

### Outcome Contract `(C+, C-)` & Eliminated Alternatives

Basis: `source` inspection + `derived` constraints.

- **Positive Obligations (`C+1`–`C+6`):**
  - `C+1`: Verify unmodified `torvalds/linux` crates (`rust/zerocopy/`, `rust/pin-init/`, `rust/kernel/`, drivers) out-of-tree from authoritative `.o.cmd` records without altering production `.o`/`.ko` artifacts.
  - `C+2`: Preserve fail-closed default third-party `cargo-anneal verify` restrictions; admit kernel capabilities strictly behind explicit split-action capability flags bound in `CaptureManifest` and Receipt v3 `target_bindings`/`tcb_shims[]`.
  - `C+3`: Keep `-Zmir-opt-level=0 -Zmir-preserve-ub` `Runtime(PostCleanup)` capture while modeling `-Copt-level=2/s`, `-Cdebug-assertions`, and `-Coverflow-checks=y` explicitly via `TerminatorKind::Assert` and `TerminalOut.aborted`; never waive UB via `safetyPre` on safe `fn`s (`isUnsafe = false`) or ignore reachable `rust_build_error()` paths under `CONFIG_RUST_BUILD_ASSERT_ALLOW=n`.
  - `C+4`: Verify `rust/kernel/` and `rust/pin-init/` modularly across `bindings::*` and `439` `rust_helper_*` C shims via auditable `FnContract` stubs, `Opaque<T>`, `#[vtable]`, `PinInit`/`DropGuard`, and compile-time `bindgen` `_Static_assert` checks.
  - `C+5`: Isolate `tools/memory-model/linux-kernel.cat` (LKMM) from C11/RC11 (`MiriWeak`), track preemption/IRQ/RCU `ExecCtx` tokens, and compose safe driver proofs via zero-TCB `AnnealAeneasBridge`.
  - `C+6`: Maintain all `TrustedBoundary.lean` invariants (`Type 0` `levelParams.isEmpty`, `foundation-lock.json`, `<= 3` axioms, Pass-2 `M_ref` independence) across `M0`–`M2`.
- **Exclusions (`C-1`–`C-5`):** No `rust-project.json` authority (`E1`: `generate_rust_analyzer.py:345` scans only `("samples", "drivers")`, injects dummy `RUST_MODFILE` at `:106`, hardcodes `[core, kernel, pin_init, zerocopy, zerocopy_derive]` at `:364`, and drops `--target`/`-Coverflow-checks`/`-Zsanitizer`/`@rustc_cfg`); no `Runtime(Optimized)` primary capture (`E3`); no `safetyPre` UB waivers on safe `fn`s (`E4`); no `rustc_public` migration (`E5`: loses `32.8%` of `PlaceMention` checks on `zerocopy`); no C11/RC11 modeling of `kernel/sync/{atomic,rcu}` or trusting `CONFIG_RUST_INLINE_HELPERS=y` bitcode internalization as verified Rust MIR (`E6`); no whole-C-kernel prerequisite or in-tree `verus!{}` forks (`E8`); no `Aeneas`/`mathlib4`/`herd7`/Make inside `anneal/trusted/lean/` (`E9`).

### Authoritative Kbuild Capture Architecture

Basis: `source` (`Makefile:648, 939-951`, `rust/Makefile:9-98, 597-821`, `scripts/{Kbuild.include:199-214, Makefile.build:347-382, generate_rust_target.rs:199-208}`, `anneal/trusted/`) + `execution` (`google/zerocopy:reference@a723bbfcfeba`).

1. **Out-of-Tree `.o.cmd` Extraction & Three-Domain Staging:**
   - Kbuild writes `savedcmd_<target>`, `source_<target>`, and `deps_<target>` (`fixdep` closure) into `.<target>.o.cmd`. An out-of-tree untrusted `kbuild-extract` CLI parses these records, expands `@$(objtree)/include/generated/rustc_cfg` (logging its SHA-256), resolves omitted transitive `-L $(objtree)/rust/` crates from `deps_<target>` and upstream `rust/.*.o.cmd` records, and emits explicit `--extern <name>=<path>` arguments.
   - `srctree`, `objtree`, and optional `exttree` (`M=...`) stage into disjoint `rust/{src,out_dir,ext}/` directories (`0` `..` escapes). `OBJTREE` is rewritten to staged `rust/out_dir` and normalized in `CaptureManifest.json` (`env_depinfo`); any unnormalized host `OBJTREE` leaking into a runtime `&str` MIR constant fails closed. `RecordingLoader` pairs lexical allowlisting with open-FD `fstat()` `(st_dev, st_ino)` regular-file validation and streaming SHA-256 verification.
2. **Two-Graph Crate DAG, `--sysroot=/dev/null`, Proc-Macros & `PanicImpl`:**
   - Reusable split-action capability flags (`--allow-empty-sysroot`, `--allow-lib-panic-handler`, `--path-prefix-env OBJTREE`, zero Linux-specific code inside `anneal/trusted/`) admit `--sysroot=/dev/null` with `0` ambient `-L` probing, forward normalized `RUST_MODFILE` (`rust/macros/module.rs:471-472`) to child env, authenticate host proc-macros (`lib{macros,zerocopy_derive,pin_init_internal}.so`) via Two-Pass `(st_dev, st_ino)` `/proc/self/maps` checks logged in `proc_macros[]` / `tcb_shims[]`, consume Kbuild's prebuilt `libcore.rmeta`/`libcompiler_builtins.rmeta` (failing closed on floats and redirected 128-bit mul/div/shift libcalls under `rust/Makefile:701-706, 744`), and admit `LangItem::PanicImpl` on `CrateType::Lib` (`rust/kernel/lib.rs:181-187`) strictly when returning `!`.
3. **Target Profiles, `TerminatorKind::Assert`, Hardening Flags & Compiler Floor:**
   - `TargetProfile` + `Program.targetEndian` (`.little` | `.big`) + hashed `scripts/target.json` (`"rustc-abi": "softfloat"`) fail closed on floating-point `MirTy` or FP intrinsics.
   - Admitting `-Copt-level=2/s`, `-Cdebug-assertions`, `-Coverflow-checks=y` (`Makefile:939-951`), `-Cpanic=abort` binds `{ optLevel, debugAssertions, overflowChecks }` into `Trusted.MirSemantics.Config` while still extracting `-Zmir-opt-level=0 -Zmir-preserve-ub --emit=metadata` + `tcx.items_of_instance` BFS. `TerminatorKind::Assert` lowers to `MirAst` (`AssertKind`), stepping failed runtime checks to `TerminalOut.aborted (callerMem)` distinct from `FaultKind.undefined`.
   - `TargetKernelCodegen` allowlists `-Cno-redzone=y`, `-Ccode-model=kernel`, `-Cjump-tables=n`, `-Zsanitizer={kcfi,shadow-call-stack}`, `-Zbranch-protection=bti,pac-ret`, `-Zpatchable-function-entry=*`, etc. as Receipt v3 `tcb_shims[]` (`kind: "below_mir_kernel_codegen_hardening"`); `module!` `global_asm!` (`module.rs:592`) and `static mut __MOD` emit module-lifecycle `tcb_shims[]`; `CONFIG_KASAN=n` is required.
   - M0–M1 target pinned `rustc 1.98` (`CONFIG_RUSTC_VERSION=109800`); older kernel MSRV compilers (`1.85`–`1.97`) route through isolated `#4098`/`#4017` capture containers (`D3-A`).

### Kernel Soundness Seams & Verification Composition

Basis: `source` (`rust/kernel/{build_assert,types,io,uaccess,dma,bug,jump_label,sync/*}.rs`, `rust/build_error.rs`, `rust/pin-init/src/lib.rs`, `rust/macros/vtable.rs`, `tools/memory-model/linux-kernel.cat`, `anneal/docs/aeneas-interop-bridge.md`) + `derived`.

1. **Trap 1 — `build_assert!` / `rust_build_error()` (`D2-A`):**
   - `static_assert!` / `const_assert!` resolve via `required_consts` CTFE; `const`-generic `DmaMask::new::<N>` resolves via `--instantiate` / `ConstMirMachine`.
   - Runtime-argument `#[inline(always)]` wrappers (`Bounded::from_expr`, `Io::io_view_assert`) lower diverging `build_error::build_error` calls to `Terminator::BuildError`: stepping to `FaultKind.buildAssert` when `CONFIG_RUST_BUILD_ASSERT_ALLOW=n` (link-time rejection) and `.aborted` when `=y` (`BUG()`).
   - `Contract` keeps `NoUbAndSupported` unconditional on safe `fn`s (`safetyPre` never waives UB) and adds `buildPre : Query → Prop` solely on declared `#[inline(always)]` helpers (`CrateTheorem` exempts them while exporting Receipt v3 `link_time_build_assert_obligations[]`; callers discharge `callee.buildPre` at call sites).
2. **Trap 2 — Minimal-TCB C-ABI, `Opaque<T>`, `#[vtable]`, `pin-init` (`D4-A`):**
   - `bindings::*` and `439` `rust_helper_*` shims (`helpers.c` + `69` leaf `.c` files = `70` `.c` files) lower to `BodyRole::assumedStub` (`AbiKind::cNoUnwind`, `noUnwind = true`, `AssumedContractRealizable`) in out-of-tree `linux-kernel-anneal-specs`, logged in `tcb_shims[]` (`kind: "unverified_c_ffi_stub"`) and invariant under `CONFIG_RUST_INLINE_HELPERS=y` (`helpers.bc` LTO happens post-MIR).
   - Because `rust/Makefile:526` passes `--no-layout-tests` to `bindgen`, `kbuild-extract` emits a C compile-time `_Static_assert` cross-check on `sizeof`/`alignof`/`offsetof` (`BindingsLayoutCert`).
   - `Opaque<T>` (`UnsafeCell<MaybeUninit<T>>`, `types.rs:331-419`) uses `ByteRole.unionData`, `FreezeProfile.hasUnsafeCellAt := true`, and Ghost `InvariantEnv` ownership/init states (`uninit -> c_initialized(state) -> destroyed`).
   - `#[vtable]` (`macros/vtable.rs:27-158`) admits non-variadic `ExternAbi::C` with opaque `FnPtrVal (Option DefId)` handles proving `noUnwind`, errno `[-4095, -1]`, and `ForeignOwnable` alignment.
   - `rust/pin-init/` (`17` files, `119` `unsafe` blocks) specifies `PinInit<T, E>` as slot-footprint `FnContract`s proving field initialization + pinning on `Ok(())` and reverse-order `DropGuard` cleanup without double-drop on `Err(e)`.
3. **Trap 3 — Segregated LKMM, `ExecCtx`, Tier-3 Boundaries, & `Anneal ↔ Aeneas` (`D5-A`):**
   - `rust/kernel/sync/atomic/` (`Relaxed | Acquire | Release | Full`, no `SeqCst`) delegates to `rust_helper_atomic_*` governed by `tools/memory-model/linux-kernel.cat` (syntactic `ppo` dependencies, `smp_mb__*`, and RCU `rb` grace-period irreflexivity). `Trusted.MirSemantics.Lkmm` provides a segregated axiom interface differentially tested offline against `herd7` `linux-kernel.cat`.
   - Generic `InvariantEnv` ghost tokens instantiate `ExecCtx := { preemptDepth : Nat, irqDisabled : Bool, rcuDepth : Nat }` (`SpinLock` increments `preemptDepth`, `rcu::Guard` independently increments `rcuDepth` for `CONFIG_PREEMPT_RCU`, `GFP_KERNEL`/`Mutex::lock`/`synchronize_rcu`/`UserSliceReader::read_raw` require all three zero; C stubs seed annotations from Clang `-Wthread-safety`).
   - Localized Tier-3 bounds: `6` `asm!`/`asm_goto` sites in `rust/kernel/` (`bug.rs`, `jump_label.rs`, `lib.rs`, `sync/`) get `Terminator::InlineAsm` contracts; `io` (`46` `unsafe`) checks `offset_valid`; `uaccess` (`14` `unsafe`) models demonic `Ok(())`/`Err(EFAULT)` single-fetch TOCTOU; `dma` (`21` `unsafe`) models volatile device-coherent access.
   - Planned zero-TCB `anneal/interop/aeneas-bridge/` (once Anneal's Lean pin aligns from `v4.34.1` to `v4.36.0` for `aeneas@fb44cb400eb6`) composes pure Aeneas driver proofs (`rnull`, `pwm_th1520`, `binder/range_alloc/array.rs`, `nova-core` GSP parsers) with Anneal-verified `kernel::*` primitives.

### Phased Milestones (`M0`–`M2`) & TCB Budget

Basis: `source` baseline (`google/zerocopy@ccf9caacb6`, `[real measurement]`) + `derived` estimates (`[engineering estimate]`).

- **Live Clean `HEAD` Baseline (`ccf9caacb6`):** `rustc-capture/src/` `10,460` `.rs` (`14,573` total); `cargo-anneal/src/` `25,583` `.rs` (`39,065` total); `audit/` `5,189` `.rs` `src/` (`17,841` incl. tests) + `6,212` `TrustedBoundary.lean` + `68` `positive.lean` (`24,121` `.rs+.lean`, `24,143` incl. `Cargo.toml`); `lean/Trusted/` `5,437` non-canary (`6,224` total); `correspondence/Trusted/` `4,103` non-canary (`4,264` total).
- **Milestones (`[engineering estimate]`):**
  - **M0 (Immediate In-Tree Dividend):** Untainted Receipt v3 verification of vendored `rust/zerocopy/` (`0.8.62`, `305` `unsafe` blocks) + Tier-0 `rust/kernel/` (`bits`, `bitfield`, `Bounded<T, N>`, `page_align`, `DmaMask`, `ArrayLayout`, `Error`). Est. `+400–600` Rust TCB, `+280–450` Lean TCB, `+250–400` Ring-2.
  - **M1 (`pin-init` + `kernel::list` + Core FFI):** `kernel::list` (`73` `unsafe`, `0` C calls), `kernel::str` (`18` `unsafe`), `Opaque<T>`, `rust/pin-init/` (`17` files, `119` `unsafe`), `rbtree.rs` (`64` `unsafe`), `kernel::alloc/` (`89` `unsafe`), `nova-core` (`113` `zerocopy` uses across `86` files), `drm` (`9` `unsafe`), `binder/range_alloc/`. Est. `+700–1,000` Rust TCB, `+2,200–3,400` Lean TCB, `+1,400–2,200` Ring-2.
  - **M2 (LKMM, Drivers & Subsystems):** `kernel::sync/{atomic,rcu,lock,arc}`, full `nova-core` (`37` `unsafe`), `drm`, `binder` (`152` `unsafe`), and `0`-`unsafe` drivers composed via `AnnealAeneasBridge` (`90.1%` non-vendored kernel `unsafe` surface). Est. `+400–650` Rust TCB, `+1,100–1,800` Lean TCB, `+600–950` Ring-2.

## Boundaries

- **Pre-implementation specification (`not examined` in live full-kernel `make`):** Full `torvalds/linux` compilation (`make LLVM=1` generating `objtree/` `.o.cmd` files), QEMU boot tests, `klint` runs, `herd7` LKMM execution, and `Charon`/`Aeneas` driver extraction were not executed in the planning workspace; Kbuild rules, `arch/*/Makefile`, `klint`, and `linux-kernel.cat` are grounded via `[source inspection]`.
- **Architecture limits (`not examined` / `unsupported`):** `32`-bit (`arm`/`x86_32` UML) and big-endian (`s390x`) kernel builds are unverified in live execution pending `#4188` target layout generalization; `CONFIG_KASAN=y` builds are excluded (`unsupported`); `CONFIG_RUST_INLINE_HELPERS=y` bitcode internalization is not verified as Rust MIR (`known not to apply`).
- **Unlanded dependencies (`not yet implemented`):** `AnnealAeneasBridge` (`anneal/docs/aeneas-interop-bridge.md`) and Profile v2 (`#4188`–`#4192`, `#4197`) are not yet landed on `google/zerocopy@ccf9caacb6`; Anneal's Lean pin (`v4.34.1`) must also align to `AeneasVerif/aeneas@fb44cb400eb6`'s Lean `v4.36.0` `.olean` format for `Anneal ↔ Aeneas` composition.

## Evidence

- **Kernel source inspection (`2026-11-23`):** `torvalds/linux@b6a9fa34ce4187cb69d3c588a4bbffc31ce5db8f` (`Makefile:648, 939-951`, `rust/Makefile`, `scripts/{Makefile.build,Makefile.lib,Makefile.context-analysis,generate_rust_target.rs,generate_rust_analyzer.py,min-tool-version.sh,Kbuild.include}`, `arch/{x86,arm64}/Makefile`, `rust/{build_error,compiler_builtins,bindings/lib,uapi/lib,kernel/*,pin-init/src/lib,macros/{lib,module,vtable},helpers/*,zerocopy/*}`, `tools/memory-model/linux-kernel.cat`).
- **Anneal baseline & census (`[real measurement]`):** `google/zerocopy@ccf9caacb6abc54b8b2cfd6db114f02cb87276e5` LOC measurements (`anneal/trusted/`), `568`-file `.rs` / `70`-file `rust/helpers/` census (`2,208` non-vendored `unsafe` blocks), and `google/zerocopy:reference@a723bbfcfeba34509c2035e27bc0fded43681755` (`12`-row `anneal-rustc-capture` matrix, `22.0 ms` raw driver pass-through, and Receipt v3 `v4.34.1` checks on `<usize as PointerMetadata>` and `rust_build_error()`/`MAX_DMA_BITS = 32` mutant).

## Revalidation

1. Run a dry-run `.o.cmd` extractor against real `make LLVM=1` outputs (`rust/.kernel.o.cmd`, `rust/.zerocopy.o.cmd`) on `torvalds/linux@b6a9fa34ce41` (or newer) to confirm `savedcmd_$@`, `@include/generated/rustc_cfg`, `deps_$@`, and `RUST_MODFILE` extraction parity.
2. Diff `rust/Makefile`, `scripts/generate_rust_target.rs`, and `rust/kernel/{build_assert,types,sync/atomic/*}.rs` when advancing `torvalds/linux` beyond `7.4-rc4` to check for changes in `objcopy --redefine-sym`, `softfloat` target JSON keys, or `klint`/`-Wthread-safety` annotations.
3. Check `anneal/trusted/` on `google/zerocopy` for landing of `#4188`–`#4192`, `#4197`, and `anneal/interop/aeneas-bridge/`.
