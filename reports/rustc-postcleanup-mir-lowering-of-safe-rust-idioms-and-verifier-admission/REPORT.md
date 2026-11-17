# `Runtime(PostCleanup)` MIR Lowering of Safe Rust Idioms, Verifier Admission Boundaries, and `-O0` `thread_local!` Stack Exhaustion

## Summary

Auditing unoptimized `Runtime(PostCleanup)` MIR (`SimplifyCfg-pre-optimizations`)
across `rustc 1.98.0-nightly` (`f8a08b688cbe`) and `rustc 1.102.0-nightly`
(`3ef0c22cdb86`) reveals four non-obvious lowering and runtime behaviors affecting
Rust formal verifiers, MIR censuses, and baseline `miniz_oxide 0.9.1` builds:

1. **Compiler-version drift inside `Box` dereference lowering:** Coercing `&Box<[u8;
   N]>` during `b[i]` emits `((_5.0: Unique<[u8; 32]>).0: NonNull<[u8; 32]>) as
   *const [u8; 32] (Transmute)` in `1.98.0-nightly` (`f8a08b688cbe`), whereas
   `1.102.0-nightly` (`3ef0c22cdb86`) emits `(_5.0: std::boxed::BoxRaw<[u8; 32]>)
   as *const [u8; 32] (BoxDerefTransmute)`. Any MIR extractor pattern-matching
   `Unique`/`NonNull` field chains breaks across this toolchain bump unless it
   handles `BoxRaw` + `CastKind::BoxDerefTransmute`.
2. **Dense-slice, closure, and unary/unchecked admission gaps in MIR extraction:**
   Safe slice idioms expand into MIR primitives rejected by narrow scalar
   extractors (`joshlf/anneal@31b91b61b84e`): `slice::len()` and `split_at_mut`
   lower to `Rvalue::UnaryOp(UnOp::PtrMetadata, ...)`; `Cell::from_mut(out).as_slice_of_cells()`
   creates `&[Cell<u8>]` indexing checked by `PtrMetadata`; capturing closures
   construct anonymous `AggregateKind::Closure` structs dispatched through
   `<closure as Fn>::call`; fieldless enum constructors (`MiniStatus::Failed`)
   lower via empty `AggregateKind::Adt` rvalues rather than scalar literals; and
   bit-twiddling uses `UnOp::{Not, Neg}` and `BinOp::{Div, Rem}` (plus unchecked
   ops in bit-packing).
3. **Full `miniz_oxide 0.9.1` & `adler2 2.0.1` MIR census + latent upstream bitmask bugs:**
   Dumping `SimplifyCfg-pre-optimizations.after.mir` under `1.98.0-nightly`
   (`f8a08b688cbe`, `-C opt-level=0 -C debug-assertions=no -C overflow-checks=no`)
   yields `367` MIR files (`344` functions, `8,032` locals, `3,510` basic blocks,
   `22,487` statements, `317` bounds/panic asserts) for `miniz_oxide 0.9.1` (top
   body `inflate::core::decompress_with_limit`: `998` locals, `466` BBs, `23`
   asserts) and `17` MIR files (`290` locals, `124` BBs, `36` asserts) for
   `adler2 2.0.1`. Upstream `miniz_oxide 0.9.1` also contains three dormant
   defects: an identically-false flag conjunction `(flags &
   TDEFL_FORCE_ALL_RAW_BLOCKS & TDEFL_RLE_MATCHES) != 0` (`0x0008_0000 &
   0x0001_0000 == 0`) in `window_bits_from_flags`, missing `TDEFL_RLE_MATCHES`
   in `compress_inner`'s fast-compressor filter, a `LEVEL1_HASH_SIZE_MASK = 4095`
   mask leaving `87.5%` of the `32,768`-slot hash array unused, and a redundant
   `256`-byte self-match loop when `cur_match_dist == 0` at position `0`.
4. **Unoptimized `-O0` `thread_local!` eager array overflow on 2 MiB stacks:**
   In `-C opt-level=0` (such as verification capture builds or debug tests),
   initializing a `1.8 MB` buffer inside `thread_local!` via `RefCell::new([1u8;
   1_800_000])` materializes an eager stack temporary before moving into TLS,
   triggering a deterministic 2 MiB thread stack overflow (`SIGABRT` / return
   `-6`), whereas `const { RefCell::new([0u8; 1_800_000]) }` or lazy
   `Box<[u8; N]>` initialization succeeds on 2 MiB stacks across both `-O0` and
   `-O3`.

---

## Applicability

These findings govern:

- **`rustc_middle::mir` consumers and verifiers:** Applies to tools ingesting
  `Runtime(PostCleanup)` (`SimplifyCfg-pre-optimizations`) MIR on Rust `1.98.0`
  through `1.102.0-nightly`, specifically `joshlf/anneal@31b91b61b84e`
  (`trusted/rustc-capture/src/{extract,ir,lean,capture}.rs`).
- **Baseline crate comparison (`miniz_oxide` & `adler2`):** Exact crate revisions
  `Frommi/miniz_oxide@4e582392df3a739d2b0dfd2c537dc33e8942be38` (`0.9.1`) and
  `oyvindln/adler2@89a031a0f42eeff31c70dc598cbf31f1680f` (`2.0.1`).
- **Debug/verification memory layout:** Applies to Linux `x86_64` threads using
  Rust's default `2 MiB` stack (`std::thread::Builder::stack_size(2 * 1024 * 1024)`)
  when compiling with `-C opt-level=0`.

---

## Findings

### 1. Golden `Runtime(PostCleanup)` MIR Lowerings Across `1.98` and `1.102`

`Basis: execution`

Compiling [`support/mir_idioms_probe.rs`](support/mir_idioms_probe.rs) with
`rustc --edition 2021 --crate-type rlib -Copt-level=0 -Cdebug-assertions=no
-Coverflow-checks=no -Zdump-mir=SimplifyCfg-pre-optimizations` establishes how
common safe Rust constructs materialize in unoptimized MIR:

| Safe Rust Idiom (`mir_idioms_probe.rs`) | Observed MIR Representation (`SimplifyCfg-pre-optimizations.after.mir`) | Toolchain Delta (`1.98` vs. `1.102`) | Impact on Minimal Extractors (`31b91b61b`) |
| :--- | :--- | :--- | :--- |
| `&Box<[u8; 32]>` indexing (`read_box_array`) | `_5 = no_retag copy (*_1); _6 = copy ... as *const [u8; 32] (...); _0 = copy (*_6)[_3];` | `1.98`: `(_5.0: Unique<[u8; 32]>).0: NonNull<...>` `(Transmute)`; `1.102`: `(_5.0: BoxRaw<[u8; 32]>)` `(BoxDerefTransmute)` | Extractors traversing `Box`'s internal fields break across `BoxRaw` without handling `BoxDerefTransmute` |
| `Cell::from_mut(out).as_slice_of_cells()` (`cell_apply`) | `Terminator::Call` to `Cell::<[u8]>::from_mut` + `as_slice_of_cells`; bounds check uses `PtrMetadata(copy _4)` before `&(*_4)[_10]` | Identical shape | Requires `PtrMetadata` support and `Cell` intrinsic/method contracts |
| `&mut dyn FnMut(&[u8]) -> bool` (`dyn_cb`) | Trait-method `Terminator::Call` (`<dyn FnMut as FnMut>::call_mut`) on fat `&mut dyn` object | Identical shape (`dump` item present) | Requires vtable/dynamic dispatch modeling outside static `DefId` lookup |
| Capturing closure `\|x\| x.wrapping_add(bias)` (`closure_map`) | `_3 = {closure@...} { bias: move _4 };` followed by `<{closure@...} as Fn<(u8,)>>::call(move _5, move _6)` | Identical `{closure@...}` ADT aggregate syntax | Rejected unless `AggregateKind::Closure` and generated closure `DefId`s are admitted |
| Iterator chain `.chunks_exact(4).zip(...).map(...).sum()` (`iter_zip_dot`) | Lowered to multiple `Terminator::Call` state-machine steps (`next`/`sum`) with branch terminators | Identical (`>= 2` return edges) | Monomorphized iterator helpers must either be inlined or contracted |
| Fieldless enum construction (`MiniStatus::from_flag`) | Pretty-printed as `_0 = MiniStatus::Failed;` (`Rvalue::Aggregate(AggregateKind::Adt(..., []), [])`) | Identical | Rejected by `31b91b61b:extract.rs:384-418` unless zero-arg `AggregateKind::Adt` is lowered to `ConstLit` for `evalConstLit` |
| Bitwise / signed arithmetic (`scalar_ops`) | Emits `Not(_)`, `Neg(_)`, `Div(_, _)`, `Rem(_, _)` with zero-divide / overflow `assert`s | Identical (`Div`, `Rem`, `Not`, `Neg` observed) | `31b91b61b:extract.rs:254-277` explicitly rejects `UnOp` and `Div`/`Rem`/unchecked `BinOp`s (`MirAst.lean` already models them) |

*Note on `joshlf/anneal@31b91b61b84e` compatibility:* `trusted/lean/Trusted/MirAst.lean:370-416`
and `MirSemantics.lean:942-1101` already define `UnOp::{not, neg}` and
`BinOp::{div, rem, *Unchecked}`, plus `evalConstLit (.enum ety) (.scalar bits)`.
Extending `rustc-capture` (`extract.rs`, `ir.rs`, `lean.rs`) solely to lower
`UnOp::{Not, Neg}`, those seven `BinOp`s, and zero-field `AggregateKind::Adt`
enum constants lets pure scalar/enum kernels pass capture without altering
`trusted/lean/`.

### 2. Reproducible MIR Census of Upstream `miniz_oxide 0.9.1` and `adler2 2.0.1`

`Basis: source + execution`

Full crate MIR dumps (`-Zdump-mir=SimplifyCfg-pre-optimizations` under `-C
opt-level=0 -C debug-assertions=no -C overflow-checks=no`) establish the exact
structural footprint of the upstream baseline:

| Crate & Revision | Toolchain | MIR Units / Functions | Total Locals | Basic Blocks | MIR Statements / Storage | Bounds / Panic `assert`s | Largest Function Footprint |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :--- |
| `miniz_oxide 0.9.1` (`4e582392`) | `1.98.0` (`f8a08b688`) | `367` / `344` | `8,032` | `3,510` | `22,487` | `317` | `decompress_with_limit`: `998` locals, `466` BBs, `23` asserts |
| `miniz_oxide 0.9.1` (`4e582392`) | `1.102.0` (`3ef0c22cd`) | `357` / `334` | `7,906` | `3,476` | `22,135` | `317` | `decompress_with_limit`: `972` locals, `442` BBs, `23` asserts (`compress_normal`: `436` locals, `158` BBs; `compress_fast`: `426` locals, `157` BBs) |
| `adler2 2.0.1` (`89a031a0`) | `1.98.0` (`f8a08b688`) | `17` / `17` | `290` | `124` | `749` | `36` | `algo::{impl#0}-compute`: `167` locals, `68` BBs, `11` asserts |
| `adler2 2.0.1` (`89a031a0`) | `1.102.0` (`3ef0c22cd`) | `17` / `17` | `286` | `124` | `737` | `36` | `algo::{impl#0}-compute`: `167` locals, `68` BBs, `11` asserts |

Across `miniz_oxide 0.9.1`, `317` explicit runtime `assert(...)` terminators sit
inside MIR bodies even with `-C debug-assertions=no -C overflow-checks=no`,
dominated by dynamic slice/array bounds checks in `decompress_with_limit`,
`compress_normal`, and `compress_fast`.

### 3. Dormant Upstream `miniz_oxide 0.9.1` Bitmask, Hash-Mask, and Self-Match Bugs

`Basis: source + derived`

Inspecting `Frommi/miniz_oxide@4e582392df3a:miniz_oxide/src/deflate/{core,buffer}.rs`
explains four baseline anomalies:

1. **Always-false bitmask conjunction in `window_bits_from_flags` (`core.rs:2586-2596`):**
   Line `2587` tests `(flags & TDEFL_FORCE_ALL_RAW_BLOCKS & TDEFL_RLE_MATCHES) != 0`.
   Because `TDEFL_RLE_MATCHES = 0x0001_0000` (`core.rs:196`) and
   `TDEFL_FORCE_ALL_RAW_BLOCKS = 0x0008_0000` (`core.rs:203`) are disjoint
   single-bit flags (`0x0008_0000 & 0x0001_0000 == 0`, verified in
   `verify_mir_and_tls.py`), this conjunction evaluates to `false` for all
   `flags: u32`, preventing `CompressionStrategy::RLE` alone from clamping the
   zlib header `CMINFO` to `window_bits = 8`.
2. **Dead raw flag & ignored RLE filter in `compress_inner` (`core.rs:2471-2481`):**
   `let filter_or_rle = d.params.flags & (TDEFL_FILTER_MATCHES | TDEFL_FORCE_ALL_RAW_BLOCKS) != 0;`
   tests `TDEFL_FORCE_ALL_RAW_BLOCKS` (already handled two lines later by `if raw`)
   instead of `TDEFL_RLE_MATCHES`. When level `1` is combined with
   `CompressionStrategy::RLE` (such as `limit_level_by_window_bits` clamping
   `window_bits < 12`), execution falls into `compress_fast` (`core.rs:2158-2320`),
   which ignores `TDEFL_RLE_MATCHES` and emits non-RLE distances up to `32,768`.
3. **87.5% wasted `HashBuffers.hash` allocation at Level 1 (`core.rs:333, 2211-2215`):**
   `HashBuffers` zero-initializes `hash: Box<[u16; 32768]>` (`64 KiB`, `buffer.rs:30, 52`)
   and `next: Box<[u16; 32768]>` (`64 KiB`), yet `compress_fast` masks trigram
   hashes with `const LEVEL1_HASH_SIZE_MASK: u32 = 4095;` (`8 KiB` read/written,
   leaving `28,672 / 32,768 = 87.5%` of `hash` and all `64 KiB` of `next` unused).
4. **Zero-slot `cur_match_dist == 0` self-comparison (`core.rs:2214-2246`):**
   Because `hash` is zero-initialized, at `lookahead_pos = 0`, `probe_pos = 0`
   yields `cur_match_dist = 0 <= d.dict.size` (`0 <= 0`). `compress_fast` compares
   `dict[0..]` against itself across all `32` 8-byte `u64` iterations (`256` B)
   before discarding the match post-hoc with `if cur_match_dist == 0 { 0 }` at
   line `2241`; unvisited `0` buckets at positions `1..=32768` also probe offset `0`.

### 4. `-O0` `thread_local!` Eager Stack Temporary Overflow on 2 MiB Stacks

`Basis: execution`

When a crate stores a large workspace (`1.8 MB` `[u8; 1_800_000]`) inside
`thread_local!`, initialization semantics diverge sharply at `-C opt-level=0` vs.
`-O3` (`support/tls_stack_overflow_probe.rs`):

| `thread_local!` Declaration (`1,800,000` B) | `-C opt-level=0` (2 MiB Thread Stack) | `-C opt-level=3` (2 MiB Thread Stack) | Underlying Codegen Mechanism |
| :--- | :---: | :---: | :--- |
| `RefCell::new([1u8; 1_800_000])` (eager non-`const` expr) | **Stack overflow (`SIGABRT`, `-6` / exit `134`)** | Passes (`Ok(1)`) | At `-O0`, LLVM does not RVO/promote the `[1u8; 1_800_000]` rvalue, allocating a `1.8 MB` stack frame inside the TLS init closure on top of caller frames (`> 2 MiB`) |
| `const { RefCell::new([0u8; 1_800_000]) }` | Passes (`Ok(42)`) | Passes (`Ok(42)`) | `const { ... }` places the zero-initialized value in static `.tbss` / TLS template mapped outside the 2 MiB call stack |
| `const { RefCell::new(None::<Box<[u8; 1_800_000]>>) }` | Passes (`Ok(42)`) | Passes (`Ok(42)`) | `Box` allocates lazily on the heap (`1.8 MB` never touches either `.tdata`/`.tbss` or stack) |

*(Caveat observed from test design: very large `.tbss` static TLS segments can
still interact with dynamic linker TLS reservation overhead when spawning many
threads; lazy `Option<Box<[u8; N]>>` avoids both stack pressure and static TLS
size inflation.)*

---

## Boundaries

- **Upstream `miniz_oxide` MIR census dumps:** The full `367`-file `miniz_oxide
  0.9.1` and `17`-file `adler2 2.0.1` counts were measured in `/tmp/rr_probes/`
  from upstream source trees compiled standalone without network fetch;
  [`support/verify_mir_and_tls.py`](support/verify_mir_and_tls.py) checks
  reproducibility offline on the standalone
  [`support/mir_idioms_probe.rs`](support/mir_idioms_probe.rs) idioms and
  [`support/tls_stack_overflow_probe.rs`](support/tls_stack_overflow_probe.rs)
  without requiring external Cargo registries.
- **Unmodified `31b91b61b84e` MIR pipeline execution:** This package audits
  `extract.rs`/`MirAst.lean` admission boundaries directly via `-Zdump-mir`
  inspection rather than building the `Anneal` binary and Lean `.olean` closure.

---

## Evidence

### 1. Primary Upstream Sources Examined

- **`rust-lang/rust` (`f8a08b688cbe` `1.98.0-nightly` and `3ef0c22cdb86` `1.102.0-nightly`):**
  Direct `SimplifyCfg-pre-optimizations.after.mir` output produced by `-Zdump-mir`.
- **`joshlf/anneal` (`31b91b61b84e0058db44cacbd6d189a90433c2d1`):**
  `trusted/rustc-capture/src/{extract,ir,lean,capture}.rs` and `trusted/lean/Trusted/{MirAst,MirSemantics}.lean`.
- **`Frommi/miniz_oxide` (`4e582392df3a739d2b0dfd2c537dc33e8942be38`, `0.9.1`):**
  `miniz_oxide/src/deflate/core.rs:163, 184-204, 333, 392-398, 2158-2320, 2471-2481, 2586-2596`
  and `miniz_oxide/src/deflate/buffer.rs:13-67`.
- **`oyvindln/adler2` (`89a031a0f42eeff31c70dc598cbf31f1680f`, `2.0.1`):**
  Full crate MIR dump (`17` items, `36` asserts).

### 2. Preserved Package Support Artifacts

- [`support/mir_idioms_probe.rs`](support/mir_idioms_probe.rs): Safe Rust crate
  exercising `&Box<[u8; 32]>`, `Cell::as_slice_of_cells`, `&mut dyn FnMut`,
  capturing closures, `chunks_exact`/`zip` iterators, fieldless enum
  construction, and `Not`/`Neg`/`Div`/`Rem`.
- [`support/tls_stack_overflow_probe.rs`](support/tls_stack_overflow_probe.rs):
  `2 MiB` thread-stack reproducer comparing non-`const` vs. `const { ... }` vs.
  `Box` initialization across `-O0` and `-O3`.
- [`support/verify_mir_and_tls.py`](support/verify_mir_and_tls.py): Automated
  verification script validating MIR lowering differences across `1.98.0` and
  `1.102.0`, `-O0` `SIGABRT` overflow (`-6`), and `TDEFL_FORCE_ALL_RAW_BLOCKS &
  TDEFL_RLE_MATCHES == 0`.

---

## Revalidation

Run the standalone verification script from the repository root:

```console
python3 reports/rustc-postcleanup-mir-lowering-of-safe-rust-idioms-and-verifier-admission/support/verify_mir_and_tls.py
```

The command must exit `0` with `"status": "PASS"`, observing
`BoxDerefTransmute` (`1.102.0`) vs. `Unique/NonNull (Transmute)` (`1.98.0` when
installed), `"tls_o0_eager_rc": -6` (`SIGABRT` on the `2 MiB` stack), `"tls_o3_eager_out":
"eager_fn_1.8MB: 1"`, and `"tdefl_rle_raw_and_zero": true`.
