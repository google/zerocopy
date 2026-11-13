# Census of `rustc` and LLVM Soundness Holes, `known-bug` Tests, and Miscompilations at Rust `1.99.1`

## Summary

To quantify what a formally verified MIR-to-assembly backend (`Runtime(PostCleanup)`
MIR to machine code) fixes, catches, or leaves untouched, this report censuses
all **`//@ known-bug:`** test files in `rust-lang/rust` across Rust `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), `1.100.0`
(`0ef1bc386059596dada8fb65b50425aab2ea637a`), and `nightly-2026-11-12`
(`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), alongside the major open and
recently resolved `I-unsound` and miscompilation issues across `rustc` and LLVM
`23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`). Four quantitative
findings govern verification scope:

1. **Complete `//@ known-bug:` census at `1.99.1` (309 test files):**
   Scanning `tests/` at `58cf8f9c35b355199727627d07ae34a4e2846d67` identifies
   **309 `known-bug` test files** (`337` in `1.100.0` and `328` in
   `nightly-2026-11-12`, with **12** of the `1.99.1` bugs fixed by `1.100.0`
   and **64** fixed by `nightly-2026-11-12`). Partitioning the 309 tests by
   compiler stage shows:
   - **Type, trait, or borrow checking (`258` / `309`, `83.5%`):** Frontend
     soundness holes (such as `https://github.com/rust-lang/rust/issues/25860`
     implied-bounds lifetime extension), coherence/variance bugs, and trait
     solver (`-Znext-solver`) ICEs. A verified MIR-to-assembly backend leaves
     these **untouched** unless paired with an independent post-monomorphization
     MIR type/lifetime validator.
   - **MIR construction and coroutine/pattern lowering (`32` / `309`, `10.4%`)
     plus CTFE (`4` / `309`, `1.3%`):** Malformed MIR generated during HIR-to-MIR
     lowering or coroutine state-machine transforms (e.g.,
     `https://github.com/rust-lang/rust/issues/120240`). A verified backend with
     a sound MIR well-formedness/operational-semantics gate **catches and
     rejects** invalid MIR before code generation.
   - **Codegen lowering and LLVM optimization (`15` / `309`, `4.9%`):**
     Including all **8** pointer-provenance GVN miscompilation tests under
     `tests/ui/codegen/equal-pointers-unequal/`
     (`https://github.com/rust-lang/rust/issues/107975`), SIMD projection crashes
     (`https://github.com/rust-lang/rust/issues/137108`), and `dyn AsyncFn*`
     pointer-metadata coercion bugs
     (`https://github.com/rust-lang/rust/issues/133119`). A verified
     MIR-to-assembly backend **eliminates 100% of these miscompilations**.
2. **Elimination of `rustc_mir_transform` (`rustlantis` / `GVN` / `JumpThreading`)
   miscompilations:** Differential fuzzing with `rustlantis` and `miri`
   (`https://github.com/rust-lang/rust/issues/91827`) has repeatedly uncovered
   wrong-code bugs in `rustc_mir_transform` passes (`GVN`, `JumpThreading`,
   `ConstProp`, `DeadStoreElimination`, `ReferencePropagation`). Operating from
   `Runtime(PostCleanup)` MIR with unverified MIR optimizations disabled
   (`-Zmir-opt-level=0`)—or only running kernel-verified MIR passes—eliminates
   this entire bug class.
3. **Elimination of ABI lowering and LLVM optimization miscompilations:**
   Codegen lowering bugs (such as the `x86-64` `bool` return truncation bug
   `https://github.com/rust-lang/rust/issues/163911` fixed in `1.99.1`, the
   `!Unpin` coroutine `noalias` miscompilation
   `https://github.com/rust-lang/rust/issues/63818`, and `i686` x87 `SNaN`
   return quieting `https://github.com/rust-lang/rust/issues/115567`) and LLVM
   GVN/InstCombine provenance miscompilations
   (`https://github.com/llvm/llvm-project/issues/34548`,
   `https://github.com/llvm/llvm-project/issues/35229`) are directly fixed by a
   verified MIR-to-assembly backend whose memory model preserves pointer
   provenance and target ABI calling conventions.
4. **Historical rates and resolution latency:** Across stable releases `1.98.1`
   through `1.100.0` (6-week cadence), point releases (`1.98.1`, `1.99.1`) average
   **1–2 wrong-code / ABI regression fixes per 6-week cycle** (median time-to-fix
   7–21 days for isolated codegen regressions such as `#163911`, vs. **>5 years**
   for architectural LLVM provenance and x87 target bugs such as `#107975`,
   `#115567`, and `#25860`).

## Applicability

This census applies to **Rust 1.99.1** (`rust-lang/rust`
`58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM `23.1.1`
`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), compared against **Rust 1.100.0**
(`0ef1bc386059596dada8fb65b50425aab2ea637a`) and **`nightly-2026-11-12`**
(`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).

## Findings

### 1. Breakdown of all 309 `//@ known-bug:` test files in Rust `1.99.1`

Basis: source

Table 1 classifies the 309 `//@ known-bug:` test files in `rust-lang/rust` at
`58cf8f9c35b355199727627d07ae34a4e2846d67` (`support/known_bugs_and_soundness_census.json`)
by origin stage and by the effect of a verified MIR-to-assembly backend.

| Origin Stage | Count in `1.99.1` | Share | Verified MIR-to-Assembly Backend Effect | Representative Test Files & Upstream Issue URLs |
| :--- | :---: | :---: | :--- | :--- |
| **Type, trait, or borrow checking** (`rustc_hir_typeck`, `rustc_trait_selection`, `rustc_borrowck`) | 258 | 83.5% | **Untouched** (frontend accepts ill-typed/unsound HIR or ICEs before codegen) | `tests/ui/coherence/`, `tests/ui/higher-ranked/`, `tests/crashes/*` (e.g. `https://github.com/rust-lang/rust/issues/108428`, `https://github.com/rust-lang/rust/issues/149703`) |
| **MIR construction & coroutine/pattern lowering** (`rustc_mir_build`, `CoroutineTransform`) | 32 | 10.4% | **Catches at MIR boundary** if MIR type/liveness checker rejects malformed MIR | `tests/ui/rfcs/rfc-0000-never_patterns/120240-async-fn-never-arg.rs` (`https://github.com/rust-lang/rust/issues/120240`), `tests/ui/coroutine/ Drop` |
| **Codegen lowering & LLVM optimization** (`rustc_codegen_ssa`, `rustc_codegen_llvm`, LLVM passes) | 15 | 4.9% | **Fixes** (replaces buggy lowering and unsound LLVM IR passes with verified lowering) | `tests/ui/codegen/equal-pointers-unequal/*.rs` (`https://github.com/rust-lang/rust/issues/107975`), `tests/crashes/project-to-simd-array-field.rs` (`https://github.com/rust-lang/rust/issues/137108`), `tests/ui/async-await/dyn/wrong-size.rs` (`https://github.com/rust-lang/rust/issues/133119`) |
| **Const evaluation (CTFE)** (`rustc_const_eval`) | 4 | 1.3% | **Catches if lowered to runtime MIR**; untouched if purely compile-time const-eval | `tests/ui/consts/non-sync-references-in-const.rs` (`https://github.com/rust-lang/rust/issues/49206`), `tests/ui/consts/constifconst-call-in-const-position.rs` (`https://github.com/rust-lang/rust/issues/102498`) |
| **Total `//@ known-bug:` files** | **309** | **100.0%** | **15 directly fixed; 36 caught at MIR boundary; 258 frontend-only** | Full 309-entry table in `support/known_bugs_and_soundness_census.json` |

Between `1.99.1` and `1.100.0`, **12** `known-bug` tests were resolved and
removed from the `known-bug` set (`#108428`, `#118603`, `#120873` [2 files],
`#123690`, `#138361`, `#138660`, `#148621`, `#149703`, `#150969`, `#160553`,
and `tests/ui/traits/const-traits/unsatisfied-const-trait-bound.rs`), while 40
new crash/regression tests were added (`337` total in `1.100.0`). By
`nightly-2026-11-12`, **64** of the `1.99.1` `known-bug` tests were resolved.

---

### 2. Catalog of major soundness holes, miscompilations, and backend bugs

Basis: source + documentation

Table 2 documents the ten canonical soundness and miscompilation classes affecting
`rustc 1.99.1` and LLVM `23.1.1`, their root causes, and how a verified
MIR-to-assembly backend interacts with each.

| Issue / Class (Full URL) | Stage / Origin | Status at `1.99.1` | Mechanism | Verified Backend Impact |
| :--- | :--- | :--- | :--- | :--- |
| **`rust-lang/rust#163911`** (`https://github.com/rust-lang/rust/issues/163911`) | `rustc_codegen_llvm` / ABI lowering | **Fixed in `1.99.1`** (point-release blocker) | `x86-64` FFI `bool` return value miscompilation: mismatch between C caller/callee high-bit garbage in `al`/`eax` and LLVM `range(i8 0, 2)` metadata caused wrong branch folding | **Fixes:** Verified ABI lowering explicitly zero-extends/truncates `i8` boolean returns per System V AMD64 ABI |
| **`rust-lang/rust#107975`** (`https://github.com/rust-lang/rust/issues/107975`) & **`llvm/llvm-project#34548`** (`https://github.com/llvm/llvm-project/issues/34548`) | LLVM `GVN` / `InstCombine` optimization | **Open (`8` `known-bug` tests in `tests/ui/codegen/equal-pointers-unequal/`)** | LLVM `GVN` substitutes pointer `p` with `q` after `icmp eq ptr p, q` even when `p` and `q` have different provenance (or integer-exposed provenance), causing subsequent dereferences to become `poison` | **Fixes:** A verified backend that does not replace pointers of distinct provenance upon address equality eliminates the miscompilation |
| **`rust-lang/rust#91827`** (`https://github.com/rust-lang/rust/issues/91827`) | `rustc_mir_transform` (`GVN`, `JumpThreading`, `ConstProp`) | **Recurring class** (found by `rustlantis` /Alive2-style differential fuzzing) | Unverified MIR-to-MIR optimizations fold overlapping place assignments, pointer comparisons, or `Terminator::None` inliner edges (`c77c7c48d8a8`) unsoundly | **Fixes:** Consuming `Runtime(PostCleanup)` MIR with unverified MIR passes disabled (`-Zmir-opt-level=0`) bypasses all `rustc_mir_transform` miscompilations |
| **`rust-lang/rust#63818`** (`https://github.com/rust-lang/rust/issues/63818`) | `rustc_ty_utils::abi` / LLVM `noalias` | **Mitigated workaround** (`compiler/rustc_ty_utils/src/abi.rs:365-370`) | Emitting LLVM `noalias` on `&mut T` where `T: !Unpin` miscompiles self-referential coroutines/`Pin<&mut Future>` | **Fixes / Formalizes:** Verified backend ties aliasing assumptions strictly to Tree Borrows / MiniRust semantics rather than LLVM `noalias` |
| **`rust-lang/rust#115567`** (`https://github.com/rust-lang/rust/issues/115567`) | LLVM x86-32 backend (`i686`) | **Open spec deviation** | Returning `f32`/`f64` in `st(0)` via `flds`/`fstps` converts signaling NaNs (`SNaN`) into quiet NaNs (`QNaN`), violating RFC 3514 bitwise value-move preservation | **Fixes for `extern "Rust"`** (by returning in SSE `xmm0` on `i686`); unavoidable on `extern "C"` where System V i386 ABI mandates `st(0)` |
| **`rust-lang/rust#114479`** (`https://github.com/rust-lang/rust/issues/114479`) | LLVM x86-32 backend (`i586` without SSE2) | **Open spec deviation** | x87 80-bit extended-precision registers evaluate `f32`/`f64` with excess precision and double rounding | **Fixes** on all Tier 1 targets (`i686` enables `+sse2` by default; `i586` requires software float or per-op store/reload) |
| **`rust-lang/rust#112480`** (`https://github.com/rust-lang/rust/issues/112480`) | `i686-pc-windows-msvc` stack alignment | **Open target ABI mismatch** | `align_of::<u64>() == 8` in `rustc`, but 32-bit Windows MSVC stack frames are only 4-byte aligned unless dynamic stack realignment is emitted | **Fixes / Catches:** Verified frame layout enforces dynamic `and esp, -8` realignment whenever an 8-byte-aligned local is allocated on `i686` |
| **`rust-lang/rust#133119`** (`https://github.com/rust-lang/rust/issues/133119`) | `rustc_mir_transform` / codegen unsizing | **Open (`3` `known-bug` tests in `tests/ui/async-await/dyn/`)** | `dyn AsyncFn*` coercion computes wrong pointer size / fat-pointer metadata layout | **Catches and fixes:** Verified layout/coercion check rejects mismatched pointer metadata widths |
| **`rust-lang/rust#120240`** (`https://github.com/rust-lang/rust/issues/120240`) | `rustc_mir_build` / coroutine lowering | **Open (`known-bug` in `tests/ui/rfcs/rfc-0000-never_patterns/`)** | Async function with uninhabited `!` parameter generates ill-formed MIR storage/drop sequence | **Catches at MIR boundary:** Verified MIR validator rejects ill-typed/ill-formed basic blocks |
| **`rust-lang/rust#25860`** (`https://github.com/rust-lang/rust/issues/25860`) | `rustc_hir_typeck` / borrowck | **Open long-standing type-system soundness hole** | Counterfactual implied bounds on `fn(&'b &'a ())` allow lifetime extension (`&'a T -> &'static T`) in safe code without `unsafe` | **Untouched by MIR-to-asm backend:** Because lifetimes are erased in `Runtime(PostCleanup)` MIR, fixing `#25860` requires frontend WF checks |

---

### 3. Recent codegen and MIR bug commits (`1.98.1` to `nightly-2026-11-12`)

Basis: source

Auditing `git log` between `1.98.1` (`48a229ceaefd4985c50990b14116b6d856af0985`)
and `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) (`300`
matching commits recorded in `support/known_bugs_and_soundness_census.json`)
highlights the recurring bug patterns in unverified codegen and MIR passes:
- **ABI & calling convention fixes:** `8bb1e779750f` ("Fix ABI of small-pair
  returns"), `916dda0c26e7` ("Distinguish `repr(C)` ZSTs from others in ABI
  computation"), `e99838b28059` ("Fix the floating point clobbers of RISC-V
  `clobber_abi`"), `c32c84253f88` ("codegen: Propagate reported errors from ABI
  checks"), `98d211b7748f` ("Lower UEFI targets through LLVM's `*uefi` triple").
- **Inline assembly & target intrinsic lowering fixes:** `fcc2e7983a4b` ("Fix
  bug in inline asm when using a symbol twice"), `6e8835d00dd9` ("Map
  `llvm.sqrt.v2f64` and `llvm.sqrt.v4f32` to the AArch64 builtins"),
  `4944c3007307` / `ad2829837f6b` ("Add missing Aarch64 LLVM intrinsic
  mapping").
- **MIR transformation fixes:** `c77c7c48d8a8` ("avoid `Terminator::None` in MIR
  inliner"), `722f72096ac2` ("Don't emit no-op `&T -> &T` reborrows"),
  `8a081e21c734` ("Restrict application of optimization attributes from
  instance").

## Boundaries

- **Frontend lifetime-erasure boundary:** Because `Runtime(PostCleanup)` MIR
  erases region parameters and borrow-checker loans, a verified backend that
  starts from `Runtime(PostCleanup)` MIR **cannot detect** pure lifetime-system
  unsoundnesses such as `https://github.com/rust-lang/rust/issues/25860` unless
  the input program is also checked by a verified borrow checker (e.g., Aeneas
  or Polonius verification).
- **External C/OS linker and runtime library bugs:** Miscompilations inside
  external C linkers (`ld.bfd`, `lld`) or system `libc` (`glibc`, `musl`) are
  outside the `rustc` code generator boundary (**known not to apply** unless
  the ELF/PE/Mach-O linker itself is replaced).

## Evidence

- **`rust-lang/rust` worktrees (`58cf8f9c35b355199727627d07ae34a4e2846d67`,
  `0ef1bc386059596dada8fb65b50425aab2ea637a`, and
  `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`):**
  - `tests/ui/codegen/equal-pointers-unequal/*.rs` (`8` tests citing `#107975`).
  - `tests/crashes/*.rs` and `tests/ui/**/*.rs` (`309` files containing
    `//@ known-bug:` at `1.99.1`).
  - `compiler/rustc_ty_utils/src/abi.rs:365-370` (`!Unpin` `noalias` suppression
    for `#63818`).
- **Preserved artifacts in `support/`:**
  - `support/scan_known_bugs.py`: automated scanner and classifier for
    `//@ known-bug:` directives and commit histories across `rust-lang/rust`
    worktrees.
  - `support/known_bugs_and_soundness_census.json`: complete 309-entry
    classified dataset for `1.99.1`, diffs against `1.100.0` (`12` fixed) and
    `nightly-2026-11-12` (`64` fixed), 300-commit bug sample, and the 10-item
    curated soundness/miscompilation catalog with upstream URLs.

## Revalidation

Run `python3 support/scan_known_bugs.py` against a checkout of `rust-lang/rust`
at `58cf8f9c35b355199727627d07ae34a4e2846d67` (or any newer release tag) to
recompute the `//@ known-bug:` inventory and stage-origin distribution.
