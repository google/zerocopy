# Cross-Crate `.rmeta` / `.rlib` Provenance, MIR Inlining, and Foreign Call Boundaries

## Summary

In `rustc` (`49d734536222bf28bb6d07d885b3a81d145981da` source;
`19833af7224424e8b53e288097d56b6af43d5bcf` / `1.101.0-nightly` execution), calls
to `core` and upstream crate functions never inline or lower in
`Runtime(PostCleanup)` (`tcx.mir_drops_elaborated_and_const_checked`) because
`LowerIntrinsics` only rewrites direct calls to a fixed allowlist of 25
`#[rustc_intrinsic]` symbols, while `LowerSliceLenCalls`, `InstSimplify`,
`ForceInline`, and `Inline` execute exclusively inside `optimized_mir`
(`run_optimization_passes`). When a `rustc_driver` verifier queries foreign MIR
via `tcx.instance_mir(InstanceKind::Item(def_id))`, `rustc` unconditionally
dispatches to `tcx.optimized_mir(def_id)`—which succeeds only when
`should_encode_mir` set `encode_opt = true` (`-Z always-encode-mir=yes`, or
codegen-emitting builds where the item is reachable and either generic or
`cross_crate_inlinable`) and panics on `--emit=metadata` builds or non-inlined
`pub const fn` items even when `mir_for_ctfe` is present in `.rmeta`.
Furthermore, bodyless `#[rustc_intrinsic]` items in `libcore` (`bswap`, `ctlz`,
`cttz`, `ctpop`, `saturating_add`, `saturating_sub`) have
`is_mir_available == true` and return a synthetic 1-block
`TerminatorKind::Unreachable` body from
`tcx.instance_mir(InstanceKind::Item(def_id))`, requiring verifiers to gate
foreign body retrieval on `tcx.intrinsic(def_id)` and `Instance::try_resolve`.

On the provenance boundary, `CStore` loads `.rmeta` and `.rlib` artifacts via
`std::fs::File::open` and `Mmap::map` (`MAP_PRIVATE`), completely bypassing
`Session::source_map().file_loader` (`FileLoader`). Neither `StableCrateId`
(which hashes only crate name, `-C metadata`, crate type, and compiler version)
nor `Svh` (`tcx.crate_hash(cnum)`, a 128-bit `Fingerprint` stored as an
unverified 16-byte little-endian header field in `CrateHeader.hash`)
cryptographically authenticates an external crate: overwriting those 16 bytes in
a trojan `.rlib` defeats `rustc`'s transitive diamond `Svh` check (`E0460`)
while keeping `StableCrateId` and `DefPathHash` identical. Sound compositional
multi-crate verification requires (1) staging or pre/post `(st_dev, st_ino,
st_size, st_mtime_nsec, sha256)` verification of every path reported in
`tcx.used_crate_source(cnum)` across `tcx.crates(())`, (2) explicitly calling
`tcx.import_source_files(cnum)` before inspecting
`tcx.sess.source_map().files()` (because `SpecializedDecoder<Span>` imports
upstream `SourceFile`s lazily on span decode, leaving transitive dependencies
with zero imported files by default), and (3) verifying `sf.src_hash` /
`sf.checksum_hash` for all imported `.rs` and `include!()` files while
accounting for the omission of `include_str!()` / `include_bytes!()` assets from
`.rmeta`.

## Applicability

- **Compiler and standard library source tree**: `rust-lang/rust` at commit
  `49d734536222bf28bb6d07d885b3a81d145981da` (`compiler/rustc_mir_transform`,
  `compiler/rustc_mir_build`, `compiler/rustc_middle`,
  `compiler/rustc_metadata`, `compiler/rustc_codegen_ssa`,
  `compiler/rustc_span`, `compiler/rustc_data_structures`, and `library/core`).
- **Compiler execution and empirical probes**: `rustc 1.101.0-nightly
  (19833af72 2026-10-20)`, commit `19833af7224424e8b53e288097d56b6af43d5bcf` on
  `x86_64-unknown-linux-gnu` (LLVM `23.1.4`).
- **Target workload reference**: Fuchsia Starnix `ebpf_core` crate
  (`fuchsia/fuchsia` at commit `823a15538f191b9dbd9ebafaa6ba23220b87d2e1`,
  `src/starnix/lib/ebpf`), comprising 1,052 local MIR bodies and 1,265 external
  call sites across 69 distinct `core` (65) and `alloc` (4) callees.

## Findings

### 1. Foreign Calls, MIR Inlining, and Intrinsic Lowering Across MIR Phases

#### 1.1 Why `core` Calls Survive in `Runtime(PostCleanup)`

In `compiler/rustc_mir_transform/src/lib.rs:647-684`, the query provider
`mir_drops_elaborated_and_const_checked` constructs the final `Runtime(PostCleanup)`
body by running `run_post_borrowck_cleanup_passes` followed by only three
late passes (`LowerIntrinsics`, `RemovePlaceMention`, and
`SimplifyCfg::PreOptimizations`) and clearing local variable debug info
(`decl.local_info = ClearCrossCrate::Clear`):

```rust
// compiler/rustc_mir_transform/src/lib.rs:670-683
run_passes(
    tcx,
    &mut body,
    &[
        &lower_intrinsics::LowerIntrinsics,
        &remove_place_mention::RemovePlaceMention,
        &simplify::SimplifyCfg::PreOptimizations,
    ],
    Some(MirPhase::Runtime(RuntimePhase::PostCleanup)),
);
for decl in &mut body.local_decls {
    decl.local_info = ClearCrossCrate::Clear;
}
```

None of `LowerSliceLenCalls`, `InstSimplify`, `ForceInline`, or `Inline` run in
`mir_drops_elaborated_and_const_checked`; those passes run only inside
`run_optimization_passes` (`compiler/rustc_mir_transform/src/lib.rs:686-773`)
when constructing `optimized_mir` (`MirPhase::Runtime(RuntimePhase::Optimized)`).

Furthermore, `LowerIntrinsics`
(`compiler/rustc_mir_transform/src/lower_intrinsics.rs:12-340`) only inspects
`TerminatorKind::Call` instructions whose direct callee `DefId` is itself a
`#[rustc_intrinsic]` (`tcx.intrinsic(def_id).is_some()`) matching a fixed
25-symbol allowlist:

| Intrinsic symbol (`sym::*`) in `LowerIntrinsics` | Lowered MIR construct (`lower_intrinsics.rs:27-336`) |
| :--- | :--- |
| `unreachable` | `TerminatorKind::Unreachable` |
| `ub_checks`, `overflow_checks`, `contract_checks` | `Rvalue::Use(Operand::RuntimeChecks(RuntimeChecks::*), WithRetag::No)` |
| `forget` | `StatementKind::Assign(*destination = Const::zero_sized(tcx.types.unit))` + `Goto` |
| `copy_nonoverlapping` | `StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(..))` + `Goto` |
| `assume` | `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(..))` + `Goto` |
| `wrapping_add`, `wrapping_sub`, `wrapping_mul` | `Rvalue::BinaryOp(BinOp::{Add, Sub, Mul}, ..)` |
| `three_way_compare` | `Rvalue::BinaryOp(BinOp::Cmp, ..)` |
| `unchecked_add`, `unchecked_sub`, `unchecked_mul` | `Rvalue::BinaryOp(BinOp::{AddUnchecked, SubUnchecked, MulUnchecked}, ..)` |
| `unchecked_div`, `unchecked_rem` | `Rvalue::BinaryOp(BinOp::{Div, Rem}, ..)` (in `assign_binop`) |
| `unchecked_shl`, `unchecked_shr` | `Rvalue::BinaryOp(BinOp::{ShlUnchecked, ShrUnchecked}, ..)` |
| `add_with_overflow`, `sub_with_overflow`, `mul_with_overflow` | `Rvalue::BinaryOp(BinOp::{AddWithOverflow, SubWithOverflow, MulWithOverflow}, ..)` |
| `read_via_copy` | `Rvalue::Use(Operand::Copy(*arg), WithRetag::Yes)` |
| `discriminant_value` | `Rvalue::Discriminant(*arg)` |
| `offset` | `Rvalue::BinaryOp(BinOp::Offset, ..)` |
| `slice_get_unchecked` | `Rvalue::{RawPtr, Ref}` projecting `(*ptrish)[index]` |
| `transmute`, `transmute_unchecked` | `Rvalue::Cast(CastKind::Transmute, arg, dst_ty)` |
| `aggregate_raw_ptr` | `Rvalue::Aggregate(AggregateKind::RawPtr(ty, mutbl), [data, meta])` |
| `ptr_metadata` | `Rvalue::UnaryOp(UnOp::PtrMetadata, ptr)` |

Every other `#[rustc_intrinsic]` hits `_ => {}` at `lower_intrinsics.rs:336` and
remains a `TerminatorKind::Call`. Standard library methods such as
`u64::from_be`, `u64::swap_bytes`, `u64::overflowing_add`, `u64::wrapping_add`,
`u64::checked_add`, `u64::saturating_add`, `u64::leading_zeros`,
`u64::wrapping_shl`, `Option::unwrap_or`, `cmp::min`, and `<[T]>::len` are
ordinary Rust functions in `core` (not `#[rustc_intrinsic]` declarations).
Consequently, in a caller's `Runtime(PostCleanup)` MIR, 100% of calls to those
functions remain `TerminatorKind::Call` to `core::*`. (In the Starnix
`ebpf_core` 10-file bundle, `api::apply_endianness` has zero calls only because
its source implementation uses explicit bitmask and shift operators rather than
calling `u16::from_be`, `u32::from_be`, or `u64::from_be`.)

#### 1.2 Caller `Runtime(PostCleanup)` vs. `Runtime(Optimized)` Under `-C opt-level=0`, `-Z inline-mir=yes`, and `-C opt-level=2`

Inside `run_optimization_passes` (`compiler/rustc_mir_transform/src/lib.rs:686-773`):

1. `LowerSliceLenCalls` (`compiler/rustc_mir_transform/src/lower_slice_len.rs:21-65`)
   has `is_enabled(&self) -> true` unconditionally; even at `-C opt-level=0`, it
   rewrites calls to `#[rustc_nounwind]` item `sym::slice_len_fn`
   (`core::slice::<impl [T]>::len`) into
   `Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(slice_ptr))`.
2. `ForceInline` (`compiler/rustc_mir_transform/src/inline.rs:146-172`) runs
   unconditionally even at `-C opt-level=0`, but only inlines callees annotated
   with `#[rustc_force_inline]` (`InlineAttr::Force`). Standard `core` methods
   use `#[inline]` (`InlineAttr::Hint`) or `#[inline(always)]`
   (`InlineAttr::Always`), so `ForceInline` leaves them untouched.
3. `Inline` (`compiler/rustc_mir_transform/src/inline.rs:47-61`) is enabled only
   when `sess.opts.unstable_opts.inline_mir` (`-Z inline-mir=yes`) is set, or by
   default when `sess.mir_opt_level() >= 2` (which holds when
   `-C opt-level` is `2`, `3`, `s`, or `z`).

Probing 28 representative `core` calls (`support/foreign_mir_and_inlining_probes.py`)
across `-C opt-level=0`, `-C opt-level=0 -Z inline-mir=yes`, and `-C opt-level=2`
establishes four distinct lowering regimes in caller `optimized_mir`:

| Caller function (`u64` / `Option<u64>` / `&[u8]`) | `Runtime(PostCleanup)` calls | `Optimized` (`-C opt-level=0`) calls | `Optimized` (`-C opt-level=0 -Z inline-mir=yes`) calls | `Optimized` (`-C opt-level=2`) calls & terminal MIR ops |
| :--- | :--- | :--- | :--- | :--- |
| `call_slice_len` | `core::slice::<impl [T]>::len` | `[]` (`UnOp::PtrMetadata`) | `[]` (`UnOp::PtrMetadata`) | `[]` (`UnOp::PtrMetadata`) |
| `call_wrapping_{add,sub,mul}` | `core::num::<impl u64>::wrapping_*` | `core::num::<impl u64>::wrapping_*` | `[]` | `[]` (`BinOp::{Add, Sub, Mul}`) |
| `call_overflowing_{add,sub,mul}` | `core::num::<impl u64>::overflowing_*` | `core::num::<impl u64>::overflowing_*` | `[]` | `[]` (`BinOp::{AddWithOverflow, SubWithOverflow, MulWithOverflow}`) |
| `call_checked_sub` | `core::num::<impl u64>::checked_sub` | `core::num::<impl u64>::checked_sub` | `[]` | `[]` (`BinOp::Lt`, `BinOp::SubUnchecked`) |
| `call_option_{is_some,is_none,unwrap_or}` | `core::option::Option::<T>::*` | `core::option::Option::<T>::*` | `[]` | `[]` (`Discriminant`, `BinOp::Eq`, `UnOp::Not`, `SwitchInt`) |
| `call_partial_eq` (`&u64 == &u64`) | `core::cmp::PartialEq::eq` | `core::cmp::PartialEq::eq` | `[]` | `[]` (`BinOp::Eq`) |
| `call_wrapping_{shl,shr}` | `core::num::<impl u64>::wrapping_{shl,shr}` | `core::num::<impl u64>::wrapping_{shl,shr}` | `unchecked_{shl,shr}::precondition_check` | `[]` (`BinOp::BitAnd`, `BinOp::{ShlUnchecked, ShrUnchecked}`) |
| `call_unchecked_add` | `core::num::<impl u64>::unchecked_add` | `core::num::<impl u64>::unchecked_add` | `unchecked_add::precondition_check` | `[]` (`BinOp::AddUnchecked`) |
| `call_checked_{add,mul}` | `core::num::<impl u64>::checked_{add,mul}` | `core::num::<impl u64>::checked_{add,mul}` | `core::intrinsics::cold_path` | `core::intrinsics::cold_path` (`BinOp::{AddWithOverflow, MulWithOverflow}`) |
| `call_{from_be,to_be,swap_bytes}` | `core::num::<impl u64>::{from_be,to_be,swap_bytes}` | `core::num::<impl u64>::{from_be,to_be,swap_bytes}` | `core::intrinsics::bswap` | `core::intrinsics::bswap` |
| `call_{leading_zeros,trailing_zeros,count_ones}` | `core::num::<impl u64>::*` | `core::num::<impl u64>::*` | `core::intrinsics::{ctlz,cttz,ctpop}` | `core::intrinsics::{ctlz,cttz,ctpop}` |
| `call_rotate_left` | `core::num::<impl u64>::rotate_left` | `core::num::<impl u64>::rotate_left` | `core::intrinsics::rotate_left` | `core::intrinsics::rotate_left` |
| `call_saturating_{add,sub}` | `core::num::<impl u64>::saturating_*` | `core::num::<impl u64>::saturating_*` | `core::intrinsics::saturating_{add,sub}` | `core::intrinsics::saturating_{add,sub}` |
| `call_cmp_{min,max}` | `core::cmp::{min,max}` | `core::cmp::{min,max}` | `core::intrinsics::integer_{min,max}` | `core::intrinsics::integer_{min,max}` |

Note the difference between `-C opt-level=0 -Z inline-mir=yes` and
`-C opt-level=2` on `wrapping_shl`, `wrapping_shr`, and `unchecked_add`:
`libcore`'s encoded `optimized_mir` for `u64::wrapping_shl` (which delegates to
`unchecked_shl(b & 63)`) guards a call to
`unchecked_shl::precondition_check` behind `Operand::RuntimeChecks(UbChecks)`.
At `-C opt-level=2` (where `ub_checks` is disabled by default), `SimplifyConstCondition`
folds `UbChecks` to `false` and eliminates the `precondition_check` branch; at
`-C opt-level=0 -Z inline-mir=yes` (where `ub_checks` defaults to `true`), the
call to `unchecked_shl::precondition_check` (and its transitive call to
`core::panicking::panic_nounwind_fmt`) survives in the inlined caller body.

#### 1.3 Foreign MIR Retrieval (`tcx.instance_mir` vs. `tcx.mir_for_ctfe`) and the Bodyless Intrinsic `Unreachable` Trap

When a tool queries `tcx.instance_mir(InstanceKind::Item(def_id))`
(`compiler/rustc_middle/src/ty/mod.rs:1832-1871`), `TyCtxt::instance_mir`
branches on `tcx.def_kind(def)` (`ty/mod.rs:1849-1858`):

- For `DefKind::Const | DefKind::AssocConst | DefKind::AnonConst |
  DefKind::InlineConst | DefKind::GlobalAsm`, it calls `tcx.mir_for_ctfe(def)`.
- For all other item kinds (`DefKind::Fn | DefKind::AssocFn | DefKind::Closure`),
  it **unconditionally** calls `tcx.optimized_mir(def)`—even when `def` is a
  `const fn`!
- For `InstanceKind::Intrinsic(..)` or `InstanceKind::Virtual(..)`,
  `tcx.instance_mir` panics with `bug!("cannot provide Mir for {instance:?}")`
  (`ty/mod.rs:1860-1869`).

Inspecting the foreign MIR bodies encoded in sysroot `libcore` (`support/foreign_mir_and_inlining_out.json`) reveals three critical structural properties for verifiers:

1. **Pre-Lowered `Runtime(Optimized)` Bodies in `libcore`**: Because the rustup
   sysroot `libcore` is compiled with optimizations enabled (`-C opt-level=3` /
   `mir-opt-level >= 2`), `tcx.instance_mir(InstanceKind::Item(def_id))` on
   `core::num::<impl u64>::{overflowing_add, overflowing_sub, overflowing_mul,
   wrapping_add, wrapping_sub, wrapping_mul}` and `core::slice::<impl [T]>::len`
   returns a **1-basic-block, 1-statement, 0-call** `Runtime(Optimized)` body
   where `LowerIntrinsics` and `Inline` have already collapsed the body to a
   single primitive `Rvalue` (`BinOp::AddWithOverflow`, `BinOp::Add`,
   `UnOp::PtrMetadata`) with `StorageLive`/`StorageDead` markers stripped
   (`storage_markers == 0`). By contrast, `tcx.mir_for_ctfe(def_id)` on the same
   `u64::overflowing_add` `DefId` returns the uninlined `Runtime(PostCleanup)`
   body (`1` basic block, `22` statements, `14` storage markers).
2. **The Bodyless `#[rustc_intrinsic]` `TerminatorKind::Unreachable` Trap**:
   In `library/core/src/intrinsics/mod.rs`, intrinsics without a Rust fallback
   body (`bswap`, `ctlz`, `cttz`, `ctpop`, `saturating_add`, `saturating_sub`,
   etc.) are declared without a `{ ... }` block. During AST-to-HIR lowering,
   `compiler/rustc_ast_lowering/src/item.rs:1426-1443` synthesizes a dummy body
   and records `has_body: false`, which `intrinsic_raw`
   (`compiler/rustc_middle/src/ty/util.rs:1714-1719`) maps to
   `IntrinsicDef { must_be_overridden: true, .. }`. During MIR construction,
   `compiler/rustc_mir_build/src/builder/mod.rs:1044-1049` checks
   `self.tcx.intrinsic(self.def_id).is_some_and(|i| i.must_be_overridden)` and
   terminates `START_BLOCK` (`bb0`) with **`TerminatorKind::Unreachable`**.
   Then, in `inner_optimized_mir`
   (`compiler/rustc_mir_transform/src/lib.rs:813-817`):
   ```rust
   if let TerminatorKind::Unreachable = body.basic_blocks[START_BLOCK].terminator().kind
       && body.basic_blocks[START_BLOCK].statements.is_empty()
   {
       return body;
   }
   ```
   `optimized_mir` short-circuits before `run_optimization_passes` (leaving
   `body.phase == MirPhase::Runtime(RuntimePhase::PostCleanup)`), and
   `should_encode_mir` serializes that dummy body into `libcore`'s
   `tables.optimized_mir` because `cross_crate_inlinable`
   (`compiler/rustc_mir_transform/src/cross_crate_inline.rs:38-44`) returns
   `true` for every `#[rustc_intrinsic]`. Consequently, for
   `core::intrinsics::{bswap, ctlz, cttz, ctpop, saturating_add, saturating_sub}`:
   - `tcx.is_mir_available(def_id)` returns **`true`**.
   - `tcx.instance_mir(InstanceKind::Item(def_id))` succeeds and returns a
     1-block body whose `bb0` has `0` statements and
     **`TerminatorKind::Unreachable`**.
   - `rustc`'s own inliner (`compiler/rustc_mir_transform/src/inline.rs:555-572`)
     avoids inlining this dummy body because `Instance::try_resolve` resolves the
     call to `InstanceKind::Intrinsic(def_id)` and `inline.rs:563` aborts when
     `intrinsic.must_be_overridden` is `true` (or when
     `!tcx.sess.fallback_intrinsics.contains(&intrinsic.name)` for intrinsics
     like `rotate_left` that have a fallback body).
   - **Soundness requirement for MIR verifiers**: A verifier MUST check
     `tcx.intrinsic(def_id)` (or resolve the call via `Instance::try_resolve` and
     match `InstanceKind::Intrinsic`) *before* calling `tcx.is_mir_available` /
     `tcx.instance_mir(InstanceKind::Item(def_id))`. Stepping into
     `InstanceKind::Item(def_id)` on a `must_be_overridden` intrinsic treats a
     pure total operation like `u64::from_be` / `bswap` as `Unreachable`!
3. **Trait Method Declarations vs. `Instance::try_resolve` Impl Methods**:
   In `Runtime(PostCleanup)` MIR, a trait method call such as `a == b` on `&u64`
   encodes `TyKind::FnDef(trait_item_def_id, [ReErased, ReErased, u64, u64])`
   where `trait_item_def_id` is the trait declaration `core::cmp::PartialEq::eq`
   (`is_mir_available == false`, because defaultless trait declarations have no
   body). Passing the unmonomorphized `trait_item_def_id` to
   `tcx.instance_mir(InstanceKind::Item(trait_item_def_id))` panics. Resolving
   via `Instance::try_resolve(tcx, typing_env, callee_def_id, args)` resolves
   `core::cmp::PartialEq::eq` on `&u64` to
   `core::cmp::impls::<impl PartialEq<&B> for &A>::eq` (`is_mir_available == true`),
   and after substituting `args = [u64, u64]`, resolves the inner call to
   `core::cmp::impls::<impl PartialEq for u64>::eq` (`1` basic block, `BinOp::Eq`).

#### 1.4 Cross-Crate MIR Encoding Matrix (`should_encode_mir` and `-Z always-encode-mir=yes`)

In `compiler/rustc_metadata/src/rmeta/encoder.rs:1108-1138`, `should_encode_mir`
computes `(encode_const, encode_opt)` independently for each local `DefId`:

- **`encode_const` (`tables.mir_for_ctfe` / `tables.trivial_const`)**: `true` for
  all `Const`, `AssocConst`, `AnonConst`, `Ctor`, and all `const fn` items
  (`tcx.is_const_fn(def_id)`), regardless of reachability, optimization level, or
  `--emit=metadata`.
- **`encode_opt` (`tables.optimized_mir`, queried by `tcx.is_mir_available` and
  `tcx.instance_mir`)**: `true` for `Fn | AssocFn | Closure` if and only if
  (when not `Const { always: true }`):
  ```rust
  let generics = tcx.generics_of(def_id);
  let needs_inline = (generics.requires_monomorphization(tcx)
      || tcx.cross_crate_inlinable(def_id))
      && tcx.sess.opts.output_types.should_codegen();
  let always_encode_mir = tcx.sess.opts.unstable_opts.always_encode_mir;
  reachable_set.contains(&def_id) && needs_inline || always_encode_mir
  ```
- In `compiler/rustc_mir_transform/src/cross_crate_inline.rs:18-111`,
  `cross_crate_inlinable` returns `true` for `Ctor`/`Closure`,
  `#[rustc_intrinsic]`, explicit `#[inline]` / `#[inline(always)]` /
  `#[rustc_force_inline]`, or—when `tcx.sess.opts.optimize != OptLevel::No ||
  tcx.sess.opts.unstable_opts.inline_mir` and incremental compilation is disabled—small
  leaf bodies with `calls == 0` (ignoring intrinsics), `resumes == 0`,
  `landing_pads == 0`, and `statements <= threshold` (default `100`).

Testing 6 function categories across 5 upstream build modes
(`support/foreign_mir_and_inlining_probes.py`, Section 3 of
`support/foreign_mir_and_inlining_out.json`) confirms the exact matrix of
`(is_mir_available / instance_mir_ok, mir_for_ctfe_ok)`:

| Upstream `ext_lib` item | `--crate-type=rlib -C opt-level=0` | `--crate-type=rlib -C opt-level=2` | `--crate-type=rlib --emit=metadata -C opt-level=2` | `--crate-type=rlib -C opt-level=0 -Z always-encode-mir=yes` | `--crate-type=rlib --emit=metadata -C opt-level=0 -Z always-encode-mir=yes` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `plain_non_generic` (has non-intrinsic call, no `#[inline]`) | `(false, false)` | `(false, false)` | `(false, false)` | **`(true, false)`** | **`(true, false)`** |
| `small_leaf_non_generic` (`0` calls, no `#[inline]`) | `(false, false)` | **`(true, false)`** | `(false, false)` | **`(true, false)`** | **`(true, false)`** |
| `inline_non_generic` (`#[inline]`) | **`(true, false)`** | **`(true, false)`** | `(false, false)` | **`(true, false)`** | **`(true, false)`** |
| `const_non_inlined` (`pub const fn`, calls helper, no `#[inline]`) | **`(false, true)`** | **`(true, true)`** | **`(false, true)`** | **`(true, true)`** | **`(true, true)`** |
| `const_inlined` (`#[inline] pub const fn`) | **`(true, true)`** | **`(true, true)`** | **`(false, true)`** | **`(true, true)`** | **`(true, true)`** |
| `generic_fn<T: Copy>` (`requires_monomorphization == true`) | **`(true, false)`** | **`(true, false)`** | `(false, false)` | **`(true, false)`** | **`(true, false)`** |

Two failure modes stand out:

1. **The `--emit=metadata` (`cargo check`) Trap**: When an upstream crate is
   compiled with `--emit=metadata` only (`!output_types.should_codegen()`) and
   without `-Z always-encode-mir=yes`, `encode_opt` is **`false` for every
   function in the crate**—including generic functions and `#[inline(always)]`
   functions! Only `mir_for_ctfe` on `const fn` items is encoded.
2. **The Non-Inlined `pub const fn` Asymmetry**: At `-C opt-level=0` (or under
   `--emit=metadata`), a `pub const fn` without `#[inline]` (`const_non_inlined`)
   has `is_mir_available == false`, so `tcx.instance_mir(InstanceKind::Item(def_id))`
   panics with `"does not have a \"optimized_mir\""` even though
   `tcx.mir_for_ctfe(def_id)` is encoded in `.rmeta` and succeeds! Passing
   `-Z always-encode-mir=yes` when building upstream workspace crates guarantees
   `is_mir_available == true` across all 6 categories even under `--emit=metadata`
   and `-C opt-level=0`.

---

### 2. Cryptographic Provenance of `.rmeta` / `.rlib` Artifacts (`rustc_metadata`)

#### 2.1 Binary Layout of `.rmeta` and `.rlib` Metadata Blobs

In `compiler/rustc_metadata/src/rmeta/mod.rs:39-599` and
`compiler/rustc_metadata/src/rmeta/encoder.rs:647-789`, a `.rmeta` blob
(serialized either as a standalone `lib<name>.rmeta` file or inside an `.rlib`
`ar` archive member named `METADATA_FILENAME = "lib.rmeta"`, extracted by
`DefaultMetadataLoader::get_rlib_metadata` in
`compiler/rustc_codegen_ssa/src/back/metadata.rs:56-80`) has the following layout:

1. **`METADATA_HEADER` (`&[u8; 8] = b"rust\0\0\0\x0b"`, `rmeta/mod.rs:46`)**:
   4-byte magic prefix plus 4-byte big-endian `METADATA_VERSION` (`11`).
2. **`rustc_version(cfg_version)` (`String`, `encoder.rs:655`)**: Compiler
   version string checked for exact equality by
   `MetadataBlob::check_compatibility` (`decoder.rs:206-226`).
3. **`LazyValue<CrateRoot>` offset (`usize` relative to position, `encoder.rs:664-685`)**:
   Points to the `CrateRoot` record at the end of the file.
4. **Immediately following `LazyValue<CrateRoot>` at fixed prefix offset:
   `CrateHeader` (`rmeta/mod.rs:248-262`, `encoder.rs:687-693`)**:
   - `triple: TargetTuple`
   - `hash: Svh` (128-bit `Fingerprint` serialized as **16 raw little-endian
     bytes** via `Fingerprint::encode` in
     `compiler/rustc_data_structures/src/fingerprint.rs:170-182`)
   - `name: Symbol`
   - `is_proc_macro_crate: bool`
   - `is_stub: bool`
5. **Lazy Tables and Payload Sections (`encoder.rs:696-788`)**:
   - `source_map: LazyTable<u32, Option<SourceFile>>` (`encode_source_map`,
     `encoder.rs:542-608`)
   - `raw_crates: LazyArray<CrateDep>` (`encode_crate_deps`,
     `encoder.rs:1822-1850`), where each `CrateDep` records
     `(name: Symbol, hash: Svh, host_hash: Option<Svh>, kind: CrateDepKind,
     extra_filename: String, is_private: bool)`
   - `tables: LazyTables` (`rmeta/mod.rs:124-213`), mapping `DefIndex` to
     `LazyValue` offsets for `optimized_mir`, `mir_for_ctfe`, `promoted_mir`,
     `fn_sig`, `type_of`, `generics_of`, `predicates_of`, `def_span`,
     `def_keys`, etc.
   - `def_path_hash_map: LazyValue<DefPathHashMapRef<'static>>` (sorted array of
     64-bit local `DefPathHash` halves for binary search in
     `def_path_hash_to_def_index`).
   - `CrateRoot` header (`rmeta/mod.rs:271-372`), including `header: CrateHeader`
      and `stable_crate_id: StableCrateId`.

#### 2.2 What `StableCrateId` and `Svh` (`tcx.crate_hash`) Commit To—and How `CrateHeader.hash` Can Be Forged

- **`StableCrateId` (`compiler/rustc_span/src/def_id.rs:147-195`)**: A 64-bit
  `Hash64` over **only** `(crate_name, sorted -C metadata args, is_exe,
  cfg_version)`. It incorporates **zero** source file hashes, HIR hashes, or
  dependency hashes. Likewise, `DefPathHash` (`def_id.rs:116`) pairs
  `(StableCrateId, local_def_path_hash: Hash64)`. Two completely different
  implementations of a crate compiled with the same `--crate-name`,
  `-C metadata`, crate type, and `rustc` version produce **bit-for-bit identical
  `StableCrateId` and `DefPathHash` values** (`support/rmeta_provenance_and_tamper_out.json`,
  Experiment 3: both benign `v1` returning `x + 1` and trojan `v2` returning
  `x + 999` have `StableCrateId(3265860412234866286)` and
  `DefPathHash(Fingerprint(3265860412234866286, 8118457988314067129))` for
  `upstream::compute`).
- **`Svh` (`tcx.crate_hash(LOCAL_CRATE)`, `compiler/rustc_middle/src/hir/map.rs:1165-1254`)**:
  A 128-bit `Fingerprint` (`SipHash-2-4`) computed during compilation of the
  upstream crate over:
  1. Every local HIR owner's `OwnerInfo` (`tcx.lower_to_hir(owner.def_id)`),
  2. `upstream_crates`: sorted `Vec<(StableCrateId, Svh)>` of all loaded upstream
     crates (`tcx.crates(())`), forming a transitive Merkle DAG of `Svh` values,
  3. `source_file_names`: sorted `Vec<StableSourceFileId>` of local `SourceFile`s
     (hashing only remapped file *names*, not `src_hash`),
  4. `debugger_visualizers`, `[TRACKED]` session options
     (`dep_tracking_hash(true)`), `StableCrateId`, visibility table, and macro
     metavar spans.
- **Why `Svh` Alone Is Not a Cryptographic Authenticator for Loaded `.rmeta` /
  `.rlib` Files**:
  1. **Direct `--extern` dependencies skip `Svh` matching**: In
     `CrateLocator::new` (`compiler/rustc_metadata/src/locator.rs:324-337`),
     direct dependencies of `LOCAL_CRATE` have `hash: None`, so `--extern
     upstream=path/to/libupstream.rlib` accepts any `.rlib` regardless of its
     `Svh`.
  2. **`rustc` never recomputes `Svh` when loading metadata**: For transitive
     dependencies (`CStore::resolve_crate_deps`, `creader.rs:899-926`),
     `CrateLocator::crate_matches` (`locator.rs:727-736`) compares the expected
     `CrateDep.hash` against `metadata.get_header().hash`—which simply reads the
     16-byte little-endian `Fingerprint` stored in `CrateHeader.hash` inside the
     `.rmeta` blob!
  3. **Empirical SVH Forgery Counterexample (Experiment 3C in
     `support/rmeta_provenance_and_tamper_probes.py`)**: In a diamond dependency
     `down3_diamond -> mid -> upstream` where `mid` was compiled against benign
     `upstream` `v1` (`svh = 864fa52dd30a7051a1b2f20e5b8bb31f`), swapping in
     unmodified trojan `v2` (`svh = 35b8a5987fb98031769c5826370ef053`) fails
     with `error[E0460]: found possibly newer version of crate upstream`.
     However, overwriting the single 16-byte little-endian occurrence of `v2`'s
     `Svh` inside `v2`'s `libupstream.rlib` with `v1`'s 16-byte `Svh` causes:
     - `rustc` to compile the diamond dependency with **0 errors**,
     - `tcx.crate_hash(cnum)` to report `v1`'s exact `Svh`
       (`864fa52dd30a7051a1b2f20e5b8bb31f`),
     - `tcx.stable_crate_id(cnum)` and `tcx.def_path_hash(did)` to match `v1`
       identically, while
     - `tcx.instance_mir` decodes the trojan `v2` body (`x.wrapping_add(999)`).
     Only hashing the actual `.rmeta`/`.rlib` artifact bytes (`sha256` of `v1`
     `3841accde4...` vs. forged `v2` `4dcb7105c2...`) and checking
     `ImportedSourceFile.src_hash` (`md5=01f0b01af0...` vs. `md5=42864f04a2...`)
     detects the forgery.

#### 2.3 Two Blind Spots in `.rmeta` `SourceMap` Provenance (`tcx.import_source_files` and `include_str!`)

When an upstream crate is encoded, `EncodeContext::encode_source_map`
(`compiler/rustc_metadata/src/rmeta/encoder.rs:542-608`) serializes only those
local `SourceFile`s whose index was marked in `self.required_source_files` by
`Span` encoding (`encoder.rs:546`), stripping `src: None` (`encoder.rs:577`) and
preserving `name`, `src_hash` (`SourceFileHash`, defaulting to `Md5`),
`checksum_hash` (`Option<SourceFileHash>`, populated when compiled with
`-Z checksum-hash-algorithm=blake3|sha256`), `byte_length`, and line tables.

Experiment 1 (`support/rmeta_provenance_and_tamper_probes.py`) reveals two
critical blind spots when a downstream verifier inspects
`tcx.sess.source_map().files()`:

1. **Lazy On-Demand Import into `tcx.sess.source_map().files()`**:
   Constructing `CrateMetadata` (`decoder.rs:618-642`) initializes
   `source_map_import_info` as an empty lock of `OnceLock` slots without
   importing any `SourceFile` into `tcx.sess.source_map()`. Individual files are
   imported lazily by `cdata.imported_source_file(tcx, file_index)`
   (`decoder.rs:1702-1909`) **only** when `SpecializedDecoder<Span>` decodes a
   `Span` referencing `file_index`.
   - In Experiment 1, `upstream_mod` contains `src/lib.rs`, `src/submodule.rs`,
     and `src/included_fragment.rs` (via `include!()`). When `downstream` calls
     only `upstream_mod::used_in_downstream` (in `src/lib.rs`), inspecting
     `tcx.sess.source_map().files()` in `after_analysis` **before** calling
     `tcx.import_source_files(cnum)` returns **only `src/lib.rs` (1 of 3 encoded
     files)**; `src/submodule.rs` and `src/included_fragment.rs` are completely
     invisible!
   - Even worse, in Experiment 3C (`down3_diamond -> mid -> upstream`), because
     `upstream` is a transitive dependency and `down3_diamond` only calls
     `mid::mid_call`, `tcx.sess.source_map().files()` contains **zero files
     (`[]`)** from `upstream` before `tcx.import_source_files(cnum)` is called!
   - Calling `tcx.import_source_files(cnum)` (`cstore_impl.rs:790-796`) iterates
     `0..cdata.root.source_map.size()` and forces `imported_source_file` for
     every encoded `SourceFile` in crate `cnum`, immediately populating
     `src/lib.rs`, `src/submodule.rs`, and `src/included_fragment.rs` in
     `tcx.sess.source_map().files()`.
2. **Complete Omission of `include_str!()` / `include_bytes!()` Assets from
   `.rmeta`**:
   In Experiment 1, `src/submodule.rs` embeds `include_str!("data.txt")`. Even
   after calling `tcx.import_source_files(cnum)`, `data.txt` is **absent from
   `.rmeta`** (`include_str_data_txt_encoded_in_rmeta == false`). Unlike
   `include!("included_fragment.rs")`, which parses the included file into the
   `SourceMap` as a `SourceFile` with AST/HIR spans, `include_str!` and
   `include_bytes!` call `SourceMap::load_binary_file`
   (`compiler/rustc_span/src/source_map.rs:344-354`), which records the path only
   in `file_depinfo` (for `--emit=dep-info` during the upstream build) without
   creating a `SourceFile`. Thus, `include_str!` / `include_bytes!` inputs must
   be bound when the upstream crate itself is compiled/verified via
   `FileLoader::read_binary_file`.

#### 2.4 `.rmeta` vs. `.rlib` Candidate Priority and `Mmap` Unlinked-Inode TOCTOU

1. ** Bypassing `FileLoader` via Direct `Mmap`**:
   Neither `get_rmeta_metadata_section` (`locator.rs:936-953`) nor
   `DefaultMetadataLoader::get_rlib_metadata` (`metadata.rs:44-80`) consults
   `Session::source_map().file_loader` (`FileLoader`). Both call
   `std::fs::File::open(path)` and `unsafe { Mmap::map(file) }` directly,
   retaining the `Mmap` inside `MetadataBlob(OwnedSlice)` for the duration of the
   compilation session.
2. **`.rmeta` Takes Priority Over `.rlib` When `only_needs_metadata` Is `true`**:
   Contrary to the stale module comment in `locator.rs:48-49`,
   `CrateLocator::extract_lib` (`locator.rs:536-540`) extracts `CrateFlavor::Rmeta`
   **before** `CrateFlavor::Rlib`. When `only_needs_metadata` is `true`
   (`is_rlib || !sess.opts.output_types.should_codegen()`, `locator.rs:313-317`),
   `needs_crate_flavor(CrateFlavor::Rlib)` returns `false` (`locator.rs:555-556`),
   so `extract_one` for `.rlib` returns `Ok(None)` immediately (`locator.rs:589-592`)
   once an `.rmeta` has been loaded!
   - Experiment 4A (`support/rmeta_provenance_and_tamper_out.json`) confirms that
     when both `libupstream.rmeta` and `libupstream.rlib` exist in `-L`,
     compiling with `--crate-type=rlib` sets
     `tcx.used_crate_source(cnum) = CrateSource { rmeta: Some(".../libupstream.rmeta"), rlib: None, dylib: None }`
     (and even for sysroot `core`, loads `libcore-<hash>.rmeta` with
     `rlib: None`), whereas compiling with `--crate-type=bin` populates both
     `rmeta: Some(...)` and `rlib: Some(...)`.
   - Therefore, a verifier MUST inspect **all** path fields of
     `tcx.used_crate_source(cnum)` (`rmeta`, `rlib`, `dylib`,
     `sdylib_interface`), never assuming that `.rlib` was the file opened.
3. **`Mmap` Unlinked-Inode `rename(2)` TOCTOU Split-Brain Race**:
   Experiment 4B demonstrates that if `libupstream.rmeta` (`v1`, inode
   `45055393`, `sha256 = 4fce513d...`) is atomically replaced via `rename(2)`
   with `v2` (inode `45055402`, `sha256 = fece00f6...`) after `CStore` maps the
   file but before `after_analysis` finishes:
   - `CStore` continues decoding `v1` from the unlinked `Mmap` inode (`svh =
     113b152c...`, `src_hash = md5=01f0b01a...`, `wrapping_add(x, 1)`), while
   - Any post-compilation check that opens `tcx.used_crate_source(cnum).rmeta` by
     path reads the new inode `45055402` (`v2`, `sha256 = fece00f6...`).
   - Worse still, because `Mmap::map` uses `MAP_PRIVATE` over the file descriptor
     and `.rmeta` tables (`tables.optimized_mir`, `tables.fn_sig`, etc.) are
     decoded lazily throughout compilation, an **in-place overwrite** (`write(2)`
     to the same inode without `rename(2)`) can cause early queries (e.g.
     `fn_sig`) to read `v1` pages while later queries in `after_analysis` (e.g.
     `optimized_mir`) fault in modified `v2` pages.

#### 2.5 End-to-End Compositional Multi-Crate Provenance Protocol

To achieve sound compositional verification across `LOCAL_CRATE`, upstream
workspace crates, and sysroot crates (`core`, `alloc`, `compiler_builtins`):

1. **Private Staging or Pre/Post Inode + Digest Pinning of All `--extern` / `-L`
   Artifacts**:
   - For workspace/external `.rmeta` and `.rlib` inputs, copy or hard-link each
     expected artifact into a verifier-owned private staging directory (or record
     `(st_dev, st_ino, st_size, st_mtime_nsec, sha256)` *before* invoking
     `rustc_driver` and re-verify the exact same tuple *after* `after_analysis`
     completes).
2. **Exhaustive `tcx.crates(())` and `tcx.used_crate_source(cnum)` Audit in
   `after_analysis`**:
   - Iterate over every `&cnum in tcx.crates(())`.
   - Call `tcx.used_crate_source(cnum)` and verify that every populated path in
     `CrateSource { rmeta, rlib, dylib, sdylib_interface }` belongs either to the
     pinned toolchain `--sysroot` (with expected SHA-256) or to the pinned
     manifest's staged artifact set, and that its `(st_dev, st_ino, st_size,
     st_mtime_nsec)` and SHA-256 match the pre-compilation snapshot.
   - Verify `tcx.stable_crate_id(cnum)` and `tcx.crate_hash(cnum)` (`Svh`)
     against the upstream crate's verification receipt.
3. **Mandatory Eager `tcx.import_source_files(cnum)` + Source Digest Verification**:
   - Before reading `tcx.sess.source_map().files()`, call
     `tcx.import_source_files(cnum)` for every `&cnum in tcx.crates(())`.
   - For every `SourceFile` in `tcx.sess.source_map().files()`, partition by
     `sf.cnum`:
     - For `sf.cnum == LOCAL_CRATE`: verify via `VirtualFileLoader` /
       `RecordingFileLoader` as established in
       [`compiler-concurrent-source-modification-and-hermetic-input-binding`](../compiler-concurrent-source-modification-and-hermetic-input-binding/REPORT.md).
     - For `sf.cnum != LOCAL_CRATE`: verify `(sf.name, sf.src_hash,
       sf.checksum_hash)` against the upstream crate's pinned `source.json`
       manifest (compiled with `-Z checksum-hash-algorithm=blake3` or `sha256` so
       every `ImportedSourceFile` carries a cryptographic `checksum_hash` in
       addition to 128-bit MD5 `src_hash`).
4. **Foreign Call Dispatch Discipline**:
   - When verifying a `TerminatorKind::Call` to a foreign `DefId`, first resolve
     the call via `Instance::try_resolve(tcx, typing_env, callee_def_id, args)`.
   - If the callee is an intrinsic (`InstanceKind::Intrinsic` or
     `tcx.intrinsic(resolved_def_id).is_some()`), dispatch to the verifier's
     primitive intrinsic semantics—**never** call
     `tcx.instance_mir(InstanceKind::Item(resolved_def_id))` on a bodyless
     (`must_be_overridden == true`) intrinsic.
   - Otherwise, either discharge the call compositionally against the upstream
     crate's verified contract for `(tcx.stable_crate_id(cnum),
     tcx.crate_hash(cnum), tcx.def_path_hash(resolved_def_id))` (authenticated by
     the `.rmeta`/`.rlib` SHA-256 above), or—for transparent inlining of
     `core`/upstream helpers—require upstream compilation with
     `-Z always-encode-mir=yes` and fetch `tcx.instance_mir(InstanceKind::Item(resolved_def_id))`
     (falling back to `tcx.mir_for_ctfe(resolved_def_id)` when
     `!tcx.is_mir_available(resolved_def_id) && tcx.is_const_fn(resolved_def_id)`).

## Boundaries

- **Target architecture and object container**: The `.rlib` archive extraction
  behavior (`DefaultMetadataLoader::get_rlib_metadata` reading the `lib.rmeta`
  archive member) and `Mmap::map` (`MAP_PRIVATE`) semantics are evaluated on
  Linux (`x86_64-unknown-linux-gnu`); AIX XCOFF metadata sections and Windows
  file-locking semantics under `CreateFileMappingW` differ in OS-level page
  protection and rename behavior.
- **Proc-macro dynamic libraries**: This report covers `.rmeta` and `.rlib`
  metadata blobs and MIR tables (`tables.optimized_mir` and
  `tables.mir_for_ctfe`). Host proc-macro `.so` loading via `dlopen`/`dlsym`
  (`rustc_metadata::host_dylib::dlsym_proc_macros`) executes arbitrary native
  code inside the compiler process and is outside pure metadata provenance.
- **Polymorphic post-monomorphization errors (PMEs)**: Instantiating generic
  foreign `optimized_mir` bodies with concrete type arguments is covered here
  for call resolution (`Instance::try_resolve`), while `const` evaluation of
  post-monomorphization assertions is covered in
  [`rustc-const-evaluation-monomorphization-and-pme-capture`](../rustc-const-evaluation-monomorphization-and-pme-capture/REPORT.md).

## Evidence

- **Primary `rust-lang/rust` source locations (`49d734536222bf28bb6d07d885b3a81d145981da`)**:
  - `compiler/rustc_mir_transform/src/lib.rs:647-822` (`mir_drops_elaborated_and_const_checked`, `run_optimization_passes`, `inner_optimized_mir` lone-`Unreachable` short-circuit)
  - `compiler/rustc_mir_transform/src/lower_intrinsics.rs:12-340` (`LowerIntrinsics` 25-symbol allowlist)
  - `compiler/rustc_mir_transform/src/lower_slice_len.rs:21-65` (`LowerSliceLenCalls`)
  - `compiler/rustc_mir_transform/src/inline.rs:47-172, 550-585` (`Inline`, `ForceInline`, `InstanceKind::Intrinsic` `must_be_overridden` check)
  - `compiler/rustc_mir_transform/src/cross_crate_inline.rs:18-196` (`cross_crate_inlinable`)
  - `compiler/rustc_mir_build/src/builder/mod.rs:1044-1049` (synthesis of `TerminatorKind::Unreachable` for `must_be_overridden` intrinsics)
  - `compiler/rustc_middle/src/ty/mod.rs:1832-1871` (`TyCtxt::instance_mir`)
  - `compiler/rustc_middle/src/ty/util.rs:1712-1728` (`intrinsic_raw`)
  - `compiler/rustc_middle/src/hir/map.rs:1165-1254` (`crate_hash` / `Svh` computation)
  - `compiler/rustc_span/src/def_id.rs:116-195` (`DefPathHash`, `StableCrateId::new`)
  - `compiler/rustc_data_structures/src/fingerprint.rs:170-182` (`Fingerprint` 16-byte little-endian `Encodable` / `Decodable`)
  - `compiler/rustc_metadata/src/rmeta/mod.rs:39-599` (`METADATA_HEADER`, `CrateHeader`, `CrateRoot`, `LazyTables`)
  - `compiler/rustc_metadata/src/rmeta/encoder.rs:542-854, 1108-1138, 1822-1850` (`encode_source_map`, `EncodeContext::encode`, `should_encode_mir`, `encode_crate_deps`)
  - `compiler/rustc_metadata/src/rmeta/decoder.rs:195-248, 595-652, 1371-1431, 1702-1909` (`MetadataBlob`, `CrateMetadata::new`, `is_item_mir_available`, `imported_source_file`)
  - `compiler/rustc_metadata/src/rmeta/decoder/cstore_impl.rs:248-334, 380-423, 599-614, 746-796` (`provide_extern`, `used_crate_source`, `crate_hash`, `crates`, `import_source_files`)
  - `compiler/rustc_metadata/src/creader.rs:572-652, 729-930` (`register_crate`, `resolve_crate_deps`)
  - `compiler/rustc_metadata/src/locator.rs:304-345, 522-799, 817-953` (`CrateLocator::new`, `extract_lib`, `extract_one`, `crate_matches`, `get_rmeta_metadata_section` `Mmap::map`)
  - `compiler/rustc_codegen_ssa/src/back/metadata.rs:44-127` (`DefaultMetadataLoader::get_rlib_metadata` `Mmap::map`)
- **Reproducible probe suites and captured outputs**:
  - [`support/foreign_mir_and_inlining_probes.py`](support/foreign_mir_and_inlining_probes.py) and [`support/foreign_mir_and_inlining_out.json`](support/foreign_mir_and_inlining_out.json)
  - [`support/rmeta_provenance_and_tamper_probes.py`](support/rmeta_provenance_and_tamper_probes.py) and [`support/rmeta_provenance_and_tamper_out.json`](support/rmeta_provenance_and_tamper_out.json)

## Revalidation

Run both self-contained `rustc_driver` probe suites with a nightly `rustc` toolchain that includes `rustc-dev` (`rustc_private`):

```bash
python3 reports/rustc-cross-crate-rmeta-provenance-and-foreign-mir-inlining/support/foreign_mir_and_inlining_probes.py \
  foreign_mir_and_inlining_out.json
python3 reports/rustc-cross-crate-rmeta-provenance-and-foreign-mir-inlining/support/rmeta_provenance_and_tamper_probes.py \
  rmeta_provenance_and_tamper_out.json
```

Verify that:
1. In `foreign_mir_and_inlining_out.json`, all 28 `core` calls remain `TerminatorKind::Call` in `postcleanup`; `call_slice_len` lowers to `PtrMetadata` even at `opt0`; `bswap`/`ctlz`/`cttz`/`ctpop`/`saturating_add` have `is_mir_available: true`, `must_be_overridden: true`, and `has_unreachable_term: true`; and `ext_lib_encoding_matrix` matches the 6 $\times$ 5 `(is_mir_available, mir_for_ctfe_ok)` table.
2. In `rmeta_provenance_and_tamper_out.json`, `files_in_source_map_before_explicit_import` has 1 file while `files_in_source_map_after_explicit_import` has 3 files (and `include_str_data_txt_encoded_in_rmeta` is `false`); `forged_svh_in_v2_rlib.diamond_compile_with_forged_svh_succeeded` is `true`; and `mmap_rename_toctou` shows differing pre-run and post-run `(ino, sha256)` on the `.rmeta` path while `CStore` decodes the original unlinked inode.
