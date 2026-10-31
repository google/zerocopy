# `anneal-rustc-capture` MIR/Layout Extraction and Unified Byte-Addressed Provenance Semantics in Lean 4.34.1

## Summary

Scaling Anneal's MIR-to-x86-64 prototype (`joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`)
from scalar `u64`/`bool` slots to multi-field structs, enums, raw pointers,
wide slices (`&[T]`), polymorphic `Src`/`Dst` types, and `zerocopy`'s unsafe
primitives requires resolving two coupled problems: what compiler facts
`anneal-rustc-capture` must extract beyond textual `rustc --emit=mir`, and how
`Trusted/X86Semantics.lean` models byte-addressed memory, spatial provenance,
and per-byte initialization without breaking kernel `rfl`/`whnf` reduction. Our
`rustc_driver` probes (`support/layout_mir_driver.rs`,
`support/monomorph_mir_driver.rs` on `support/probe_6cat.rs`) and our
`prelude`-only Lean 4.34.1 mechanizations in
`support/ByteMemoryProvenanceProbe.lean` (2,625 lines, 0 `sorry`) and
`support/Phase3SemanticsProbe.lean` (4,862 lines, 0 `sorry`) establish six core
results:

1. **`rustc` Flag Mechanics (`-Z mir-opt-level=0 -C debug-assertions=off -C panic=abort`):**
   In `compiler/rustc_session/src/session.rs:945-951`, `-C debug-assertions=off`
   sets both `sess.overflow_checks()` and `sess.ub_checks()` to `false` (passing
   `-Z ub-checks=no` produces a 0-byte diff in `--emit=mir`). Arithmetic `+`,
   `-`, `*`, `<<`, `>>` overflow checks and pointer alignment/null/enum UB
   checks (`CheckAlignment`, `CheckNull`, `CheckEnums`) are suppressed, whereas
   array/slice bounds checks (`Builder::bounds_check` at
   `compiler/rustc_mir_build/src/builder/expr/as_place.rs:728-757`) and
   division/remainder-by-zero checks (`as_rvalue.rs:530-591`) are emitted
   unconditionally.
2. **Why `DefId` Call Interception at `-Z mir-opt-level=0` Beats `-Z mir-enable-passes=+Inline`:**
   At `-Z mir-opt-level=0`, `LowerIntrinsics` lowers `core::mem::transmute` in
   place to `CastKind::Transmute`, but the other 11 `zerocopy` wrappers
   (`size_of`, `align_of`, `transmute_copy`, `ptr::read`, `ptr::write`,
   `ptr::copy`, `ptr::copy_nonoverlapping`, `ptr::write_bytes`,
   `hint::unreachable_unchecked`, `MaybeUninit::{uninit,assume_init}`,
   `UnsafeCell::get`) are `#[inline]`/`#[inline(always)]` (not
   `#[rustc_force_inline]`) and remain `TerminatorKind::Call`. Enabling `-Z
   mir-enable-passes=+Inline,+InstSimplify-after-simplifycfg,+SimplifyConstCondition-after-inst-simplify`
   (note that literal `+InstSimplify` is ignored with a warning because `rustc`
   registers `InstSimplify-before-inline` and `InstSimplify-after-simplifycfg`)
   destroys local per-function modular verification boundaries by inlining all
   generic functions (`inline.rs:834-837`) and small leaf callees
   (`cross_crate_inline.rs:80-105`), leaves unreachable `precondition_check`
   basic blocks in `body.basic_blocks`, fails to inline `transmute_copy` (whose
   cost exceeds `inline_mir_hint_threshold = 100`), leaves `intrinsics::copy`
   and `intrinsics::write_bytes` as calls, and explodes `MaybeUninit` into
   internal `MaybeDangling`/`ManuallyDrop` union projections. Intercepting
   `TerminatorKind::Call` by `FnDef(def_id, args)` (`classify_call` in
   `support/monomorph_mir_driver.rs`) at `-Z mir-opt-level=0` handles all 12
   `zerocopy` operations and `core` pointer/slice helpers in 1 basic block per
   call while keeping every local function boundary intact.
3. **12 Concrete Semantic & ABI Gaps in Textual `--emit=mir` Bridged by `rustc_driver`:**
   Auditing `compiler/rustc_middle/src/mir/pretty.rs` against
   `support/layout_mir_driver.rs` and `support/monomorph_mir_driver.rs`
   identifies 12 facts omitted by `--emit=mir`: (1) ADT declarations and
   `#[repr(Rust)]` field reordering (`Pair { a: u32, b: u64 }` places `b` at
   offset `0` and `a` at offset `8`), (2) `#[repr(C, packed)]` alignment (`1B`),
   (3) `TagEncoding::Direct` (`Option<usize>`, `16B`) vs `TagEncoding::Niche`
   (`Option<NonZeroUsize>`, `8B`, `untagged_variant = 1`, `niche_start = 0`),
   (4) per-variant field offsets (`Result<usize, u32>` places `Ok.0` at `8` and
   `Err.0` at `4`), (5) dropped `VariantIdx` in `ProjectionElem::Downcast`, (6)
   `FnAbi` `PassMode` (`[u32; 2]` uses `PassMode::Cast` in `rax`; `Pair` uses
   `PassMode::Pair` in `rdi:rsi` / `rax:rdx`; `ReorderRust` uses
   `PassMode::Indirect` hidden `sret` pointer in `rdi`), (7) hidden
   `#[track_caller]` implicit `&Location` argument (`CodegenFnAttrFlags::TRACK_CALLER`
   on `ptr::read`, `ptr::write`, `transmute_copy`, `unreachable_unchecked`,
   `MaybeUninit::assume_init`), (8) omitted `pub`/`unsafe`/`extern`/predicates,
   (9) omitted `CastKind::IntToInt` source type, (10) omitted `TraitRef` on impl
   headers, (11) omitted monomorphized bodies (`tcx.collect_and_partition_mono_items(())`
   + `instance.instantiate_mir_and_normalize_erasing_regions`), and (12) omitted
   `body.required_consts()` and `body.mentioned_items()` side-tables.
4. **Allocation-Indexed Byte Memory (`mem : Nat → AllocBlock` + `Ptr alloc offset`) vs. Flat 64-Bit Address Space:**
   In `support/ByteMemoryProvenanceProbe.lean`, indexing memory by logical
   allocation (`AllocBlock` with `size : Nat`, `perm : BytePerm`, `written :
   Bool`, `bytes : List (Option UInt8)`, and `ptr : Option Ptr`) gives
   definitional cross-slot framing (`rfl`) even when an adjacent slot has
   symbolic polymorphic byte size `tySizes idx`, and catches 100% of out-of-bounds
   pointer offsets (`Nat.ble (width + p.offset) (mem p.alloc.index).size`),
   whereas a flat `UInt64 → Byte` map requires $O(W_1 \cdot W_2)$ interval
   disjointness proofs and cannot frame symbolic-size polymorphic slots.
5. **Three Essential `prelude`-Only Lean 4.34.1 Kernel Idioms for Symbolic Byte Slices:**
   - **First-argument `Nat` structural recursion:** Defining `dropBytes (count :
     Nat) (xs : List α)`, `takeBytes (count : Nat) (xs : List α)`, and
     `writeSliceAt (offset : Nat) (xs : List α) (patch : List α)` with the `Nat`
     argument first compiles via `Nat.rec` rather than `List.rec`, so at `offset
     = 0`, `extractSlice bs 0 sz` and `writeSlice (replicateBytes sz none) 0 bs`
     reduce definitionally (`rfl`) even when `bs` has symbolic length `sz =
     tySizes idx`. Writing `width + p.offset` (with `p.offset` on the right of
     `+`) likewise reduces `width + 0` to `width` by `rfl`.
   - **`Bool.casesOn` (`match ... with | true => ...`) + `Nat.ble`/`Nat.beq` instead of `@ite` + `decide`:**
     Eliminates dependent `Decidable` instance motives that block `rw` and
     `dsimp` on symbolic memories.
   - **Avoiding open symbolic `Nat.div`/`Nat.mod` in `whnf_core`:** Lean 4.34.1's
     C++ kernel accelerates `Nat.div`/`Nat.mod` only on closed literals
     (`is_nat_lit`); decomposing multi-byte struct fields into symbolic `UInt8`
     bytes (`a0, c0, c1, c2, c3 : UInt8`) and comparing symbolic type sizes via
     `Nat.beq` in `cmpSizeEqJmp` avoids unfolding 7 nested levels of Peano
     `WellFounded.fix` division by 256.
6. **End-to-End Byte-Level Mechanization of Struct Padding, Niche Enums, Wide Slices, `copy_nonoverlapping`, Casts, and `wpByteX86`:**
   Across `support/ByteMemoryProvenanceProbe.lean` and
   `support/Phase3SemanticsProbe.lean`, we prove positive `CrateTheorem`s and
   negative `¬ CrateTheorem` adequacy canaries for multi-field padded structs
   (`Padded { a: u8, b: u32 }`), cross-slot OOB pointer arithmetic, polymorphic
   `transmute_checked<Src, Dst>` with PME `sizeEqConst`, multi-field and enum
   `AdmissibleLibInv`, niche-encoded `Option<NonZeroUsize>` vs direct-tagged
   `Option<usize>`, wide slice pointers (`&[u32]`, `PtrMetadata`,
   `SliceArgValid`), `copy_nonoverlapping` spatial disjointness UB, `.leaSlot`
   on uninitialized `StorageLive` destinations, signed/unsigned width casts
   (`movzx`, `movsx`, `truncate`), and syntax-directed `wpByteX86` (reducing
   byte-machine proofs by 89–95% with `dsimp only` projection collapsing after
   `wp_jcc_split`).

## Applicability

These findings apply to:

- **Anneal (`joshlf/anneal`):** Commit
  `4f45f0a391a921ced9c9dc773b9a040dbc215d14` (`mir-to-x86`), specifically
  `trusted/rustc-capture/src/lib.rs`, `trusted/lean/Trusted/X86Ast.lean`,
  `trusted/lean/Trusted/X86Semantics.lean`, and `theory/Anneal/`.
- **Rust Compiler (`rust-lang/rust`):** Both the pinned source baseline
  `58cf8f9c35b355199727627d07ae34a4e2846d67` and the bundled Anneal nightly
  compiler `1.98.0-nightly (f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1
  2026-05-30)` (`x86_64-unknown-linux-gnu`).
- **Rust Reference (`rust-lang/reference`):** Commit
  `82da570bafd9efed421bdbae0f8603ede8dd308b` (`r[layout.repr.rust]`,
  `r[layout.repr.c]`, `r[validity.struct]`, `r[validity.enum]`,
  `r[validity.undef]`).
- **Lean 4 (`leanprover/lean4`):** Version `v4.34.1` at commit
  `5045d0056413266e57c625dcd7c365b10e377c52` (`prelude`-only mode with `import
  Init.NotationExtra`).

## Findings

### 1. Six-Category Empirical `rustc` Matrix and the 12 Gaps in Textual `--emit=mir`

Running `rustc --emit=mir -Z mir-opt-level=0 -C debug-assertions=off -C
panic=abort` and `support/layout_mir_driver.rs` /
`support/monomorph_mir_driver.rs` on `support/probe_6cat.rs` establishes the
following correspondence between textual `--emit=mir` and internal `TyCtxt`
queries:

| Category | Representative Constructs in `probe_6cat.rs` | Textual `--emit=mir` Representation (`-Z mir-opt-level=0 -C debug-assertions=off`) | Hidden Layout / ABI Facts Exposed by `TyCtxt` (`layout_mir_driver.rs` & `monomorph_mir_driver.rs`) |
| :--- | :--- | :--- | :--- |
| **1. Aggregates, Arrays, Slices, Enums** | `Pair { a: u32, b: u64 }`, `ReorderRust { a: u8, b: u64, c: u16 }`, `#[repr(C)] PairC`, `#[repr(C, packed)] PackedPair`, `[u32; 4]`, `&[u8]`, `Option<usize>`, `Option<NonZeroUsize>`, `Result<usize, u32>`, `#[repr(u8)] CLike`, `DataEnum` | Aggregate Rvalues `Pair { a: move _3, b: move _4 }`, `Option::<usize>::Some(move _4)`, `Option::<NonZero<usize>>::Some(move _4)`, `[move _3, ...]`, `[const 0_u8; 16]`. | `Pair` (`16B`, `ScalarPair(I64, I32)`) reorders `FieldIdx(1)` (`b`) to offset `0` and `FieldIdx(0)` (`a`) to offset `8`. `ReorderRust` (`16B`, `Memory`) reorders `[1, 2, 0]` to offsets `[10, 0, 8]`. `Option<usize>` is `16B` (`TagEncoding::Direct`, tag at `0`, payload at `8`), whereas `Option<NonZeroUsize>` is `8B` (`TagEncoding::Niche { untagged_variant: 1, niche_variants: 0..=0, niche_start: 0 }`) with identical MIR. |
| **2. Nested Projections & Raw Pointers** | `t.0.1`, `(*p).b`, `arr[idx]`, `slice[idx]`, `*ptr`, `&raw const (*ptr).b`, `&raw mut (*ptr).b`, packed `&raw const (*ptr).b` | `_0 = copy ((_1.0: (u32, u64)).1: u64);`, `_0 = copy ((*_1).1: u64);`, `_0 = &raw const ((*_1).1: u64);`. Indexing emits `PtrMetadata` + `Lt` + `assert(...)` before `(*_1)[_3]`. | In `PackedPair`, `(&raw const ((*_1).1: u64))` is at byte offset `1` (`align = 1B`). Bounds-check `Assert` terminators are emitted unconditionally (`as_place.rs:728-757`). |
| **3. Casts, Provenance, Wide Metadata** | `u8 as u64`, `i32 as i64`, `u64 as u32`, `i32 as u32`, `ptr as usize`, `ptr.addr()`, `with_exposed_provenance`, `without_provenance`, `arr as &[u32]`, `slice.len()`, `intrinsics::ptr_metadata` | `IntToInt`, `PointerExposeProvenance`, `PointerWithExposedProvenance`, `&raw const (*_1)`, `PtrToPtr`, `PointerCoercion(Unsize, AsCast)`, `PtrMetadata(move _2)`. | `CastKind::IntToInt` omits the source operand's type inline; distinguishing `movzx` from `movsxd` requires `body.local_decls[src].ty`. `Unsize` constructs a `16B` `ScalarPair(ptr, const 4_usize)`. |
| **4. Loops & Control Flow** | `while`, `loop` with `break`/`continue`, `for i in 0..n`, `match` on `u32`, `CLike`, `DataEnum`, `Option<usize>`, `Option<NonZeroUsize>` | `goto -> bb_header` back-edges; `_2 = discriminant(_1); switchInt(move _2)`. | `Rvalue::Discriminant(_1)` returns logical discriminant (`0` for `None`, `1` for `Some`) for both `Option<usize>` and `Option<NonZeroUsize>`, and `1, 2, 255` for `CLike`. Lowering `discriminant` requires `Variants::Multiple` (`TagEncoding`) from `tcx.layout_of`. |
| **5. Calls & Generics** | `callee_0..7`, `cat5_generic_id<T: Copy>`, `<T as ComputeTrait>::compute`, `#[track_caller] cat5_tracked_callee` | `_0 = callee(...) -> [return: bb1, unwind unreachable];` | `#[track_caller]` callees (`cat5_tracked_callee`, `ptr::read`, `ptr::write`, `transmute_copy`, `unreachable_unchecked`, `MaybeUninit::assume_init`) append an implicit `&Location` parameter in `FnAbi::args` (`arg_count = N + 1`) absent from MIR `args`. |
| **6. `zerocopy` Intrinsics** | `size_of`, `align_of`, `transmute`, `transmute_copy`, `ptr::{read,write,copy,copy_nonoverlapping,write_bytes}`, `unreachable_unchecked`, `MaybeUninit::{uninit,assume_init}`, `UnsafeCell::get` | Only `mem::transmute` lowers inline (`as Dst (Transmute)`) at `mir-opt-level=0`; the other 11 remain `TerminatorKind::Call` unless intercepted by `DefId`. | `cat6_transmute` returning `[u32; 2]` (`8B`, `BackendRepr::Memory`) uses `PassMode::Cast` in `rax`; `Pair` (`16B`) uses `PassMode::Pair` in `rax:rdx`; `ReorderRust` (`16B`) uses `PassMode::Indirect` (`sret` in `rdi`). |

In `support/monomorph_mir_driver.rs`, `tcx.collect_and_partition_mono_items(())`
discovers all 70 reachable local `MonoItem::Fn(instance)` items (including
`cat5_generic_id::<Pair>`, `cat5_trait_generic::<u64>`, and `<u64 as
ComputeTrait>::compute`), and
`instance.instantiate_mir_and_normalize_erasing_regions(tcx,
TypingEnv::fully_monomorphized(), EarlyBinder::bind(raw_body.clone()))`
substitutes `instance.args`, erases regions, and normalizes associated types
(whereas raw `EarlyBinder::instantiate` returns `ty::Unnormalized` without
normalizing associated types). In polymorphic mode
(`TypingEnv::post_analysis(tcx, def_id)`), `body.required_consts()` exposes the
symbolic `<Src as SizedTypeProperties>::SIZE` and `<Dst as
SizedTypeProperties>::SIZE` obligations on `core::mem::transmute_copy<Src,
Dst>`.

Basis: **source** (`compiler/rustc_session/src/session.rs:945-951`,
`compiler/rustc_mir_build/src/builder/expr/{as_place,as_rvalue}.rs`,
`compiler/rustc_mir_transform/src/{lib,lower_intrinsics,instsimplify,simplify_branches,inline,cross_crate_inline}.rs`,
`compiler/rustc_middle/src/mir/pretty.rs`) + **execution**
(`support/probe_6cat.rs`, `support/layout_mir_driver.rs`,
`support/monomorph_mir_driver.rs`, `support/driver_extracted_metadata.txt`,
`support/monomorph_driver_output.txt`).

### 2. Unified Byte-Addressed Provenance Machine (`AllocBlock`) and `prelude`-Only Kernel Design Idioms

In `support/ByteMemoryProvenanceProbe.lean` and
`support/Phase3SemanticsProbe.lean`, replacing the prototype's disjoint
`X86Val` sum (`.word64`, `.boolVal`, `.unit`, `.adt`, `.bytes`) with
`ByteVec := List (Option UInt8)` inside `AllocBlock` unifies concrete scalars,
multi-field padded structs, enums, wide slices, and polymorphic `Src`/`Dst`
values:

```lean
structure Ptr where
  alloc : Reg
  offset : Nat
  deriving DecidableEq

structure AllocBlock where
  size : Nat
  perm : BytePerm
  written : Bool
  bytes : List (Option UInt8)
  ptr : Option Ptr := none
```

Three `prelude`-only Lean 4.34.1 design choices are critical so that symbolic
byte-slice operations reduce by `rfl` and `dsimp`:

1. **First-argument `Nat` recursion (`dropBytes`, `takeBytes`, `writeSliceAt`) and right-hand offset addition (`width + p.offset`):**
   Putting the `Nat` count/offset parameter first compiles recursion via
   `Nat.rec` rather than `List.rec`. At `offset = 0`, `extractSlice bs 0 sz` and
   `writeSlice (replicateBytes sz none) 0 bs` reduce definitionally (`rfl`) even
   when `bs` has symbolic length `sz = tySizes idx`. Likewise, writing `width +
   p.offset` in `readSlice` and `writeSliceMem` reduces `width + 0` to `width`
   by `rfl` (`Nat.add_zero` is definitional in Lean 4, whereas `0 + width` is
   not).
2. **`Bool.casesOn` (`match ... with | true => ...`) + `Nat.ble`/`Nat.beq` instead of `@ite` + `decide`:**
   `@ite` (`if c then ... else ...`) embeds `s.mem k` inside dependent
   `Decidable` proof terms, causing `rw [hmem]` to fail with `motive is not type
   correct` and preventing `dsimp` from reducing `updateAlloc mem 3 blk 1` on
   symbolic `mem`. Using `Bool` pattern matching and `Nat.ble`/`Nat.beq` makes
   disjoint slot lookups reduce automatically under `dsimp`.
3. **`leaSlot` on uninitialized `StorageLive` destinations:**
   Taking `&raw mut dst` via `.leaSlot` before `copy_nonoverlapping` or
   `repMovsbJmp` writes into `dst` must check `targetBlk.perm.canRead &&
   Nat.ble offset targetBlk.size` without requiring `targetBlk.written = true`,
   because `allocSlotTyped` initializes fresh `StorageLive` stack allocations
   with `written = false`.

Basis: **normative** (`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`
`r[validity.undef]`, `r[validity.struct]`) + **execution**
(`support/ByteMemoryProvenanceProbe.lean` Sections 1–5,
`support/Phase3SemanticsProbe.lean` Sections 1–6).

### 3. Summary of Verified Byte-Level `CrateTheorem`s and Negative Adequacy Canaries

Across `support/ByteMemoryProvenanceProbe.lean` and
`support/Phase3SemanticsProbe.lean`, every semantic feature is paired with both
positive `CrateTheorem` verification (via syntax-directed `wpByteX86` +
`dsimp only` projection collapsing after `wp_jcc_split`) and negative `¬
CrateTheorem` adequacy canaries:

| Feature Area | Positive Verified `CrateTheorem`s & Specs | Negative Adequacy Canaries (`¬ CrateTheorem`) |
| :--- | :--- | :--- |
| **Multi-Field Padded Structs (`Padded { a: u8, /* 3 pad */ b: u32 }`) & `rep movsb`** | `prove_padded_subfield_crate`, `paddedSubfieldAndCopyBody_verified_vcgen` (12 lines via `wpByteX86`), `defaultLibInv_admissible`, `nonZeroAndPaddedLibInv_admissible` | `canary_alu_on_uninit_padding_rejected` (8B ALU `.add` spanning `none` padding bytes), `canary_pubSafe_padded_rejects_field_restriction`, `canary_pubSafe_padded_rejects_padding_init_requirement` |
| **Spatial Provenance (`Ptr alloc offset`)** | `prove_inbounds_ptr_field_load_crate` (`Ptr ⟨1⟩ 0` + `4` $\mapsto$ `Ptr ⟨1⟩ 4` loading 4B `u32` field `b`) | `canary_oob_ptr_load_rejected` & `canary_oob_ptr_store_rejected` (`Ptr ⟨1⟩ 0` + `8` $\mapsto$ `Ptr ⟨1⟩ 8` rejected even when slot `2` is allocated) |
| **Polymorphic `transmute_checked<Src, Dst>` & PME `sizeEqConst`** | `prove_pme_transmute_single_crate`, `constSucceeds_sizeEqConstBody_vcgen` (2 lines), `transmuteCheckedBody_verified_vcgen` (6 lines) | `canary_transmuteUnchecked_rejected` (omitting `sizeEqConstBody` allows `tySizes 0 ≠ tySizes 1` UB in `repMovsbJmp`) |
| **Niche-Encoded (`Option<NonZeroUsize>`) vs Direct-Tagged (`Option<usize>`) Enums** | `prove_unwrap_or_zero_niche_crate`, `prove_map_nonzero_to_opt_crate` (`mapNonZeroToOptBody_ensures_some_discr`), `prove_unwrap_or_zero_direct_crate`, `enumCrateLibInv_admissible` | `canary_direct_option_uninit_payload_rejected` (reading `none` payload of `Option::<usize>::None`), `canary_niche_forged_zero_nonzero_rejected` (downcasting `0` into `NonZeroUsize`) |
| **Wide Slice Pointers (`&[u32]`), `PtrMetadata`, & Bounds-Checked Indexing** | `prove_slice_get_checked_crate` (under `SliceArgValid`), `prove_slice_make_and_get_crate`, `sliceMakeAndGetBody_ensures_200` | `canary_forged_slice_len_oob_rejected` (wide slice with forged `len = 4` over 2-element buffer faults at `idx = 2`) |
| **`copy_nonoverlapping` Spatial Disjointness** | `prove_copy_nonoverlapping_distinct_slots_crate`, `prove_copy_nonoverlapping_subslices_crate` (`0..4` to `4..8` in same 8B buffer) | `canary_copy_nonoverlapping_overlapping_rejected` (copying 4B from `0..4` to overlapping `2..6` in same 8B allocation) |
| **Signed/Unsigned Width Casts (`movzx`, `movsx`, `truncate`)** | `prove_cast_u8_to_u64_zero_extend_crate`, `prove_cast_i8_to_i64_sign_extend_crate`, `prove_cast_u64_to_u8_truncate_crate`, `movsx_vs_movzx_neg1_and_pos42` | `canary_movsx_uninit_rejected` (`movsx` reading uninitialized `none` byte) |

Basis: **execution** (`support/ByteMemoryProvenanceProbe.lean` Sections 6–10,
`support/Phase3SemanticsProbe.lean` Sections 7–12).

## Boundaries

- **Known not to apply:** Textual `rustc --emit=mir` and `-Z print-type-sizes`
  cannot substitute for `TyCtxt` extraction in `anneal-rustc-capture`, because
  neither emits `FnAbi` `PassMode`s, `#[track_caller]` implicit `&Location`
  arguments, `TagEncoding::Niche` parameters (`untagged_variant`,
  `niche_variants`, `niche_start`), tuple field offsets, or `body.required_consts()`.
- **Known not to apply:** Passing `-Z mir-enable-passes=+InstSimplify` to
  `rustc 1.98.0-nightly` is a no-op with an unknown-pass warning; the pass is
  registered as `InstSimplify-before-inline` and
  `InstSimplify-after-simplifycfg`.
- **Not examined:** Stacked Borrows or Tree Borrows aliasing state machines for
  simultaneous mutable/shared reference retagging beyond spatial allocation
  provenance (`Ptr alloc offset`) and `copy_nonoverlapping` interval
  disjointness.

## Evidence

- **Rust compiler source (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` and `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):**
  - `compiler/rustc_session/src/session.rs:945-951` (`overflow_checks`, `ub_checks`).
  - `compiler/rustc_mir_build/src/builder/expr/as_place.rs:728-757` (`Builder::bounds_check`).
  - `compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs:456-591` (binary overflow, shift, and division/remainder checks).
  - `compiler/rustc_mir_transform/src/lower_intrinsics.rs:21-346` (`LowerIntrinsics`).
  - `compiler/rustc_mir_transform/src/instsimplify.rs:20-38, 450-471` (`InstSimplify-after-simplifycfg` `UbChecks` folding).
  - `compiler/rustc_mir_transform/src/inline.rs:45-98, 834-837` and `cross_crate_inline.rs:80-105`.
  - `compiler/rustc_middle/src/mir/pretty.rs:316-419, 681-744, 1382-1393` (`write_mir_pretty` omissions).
- **Preserved package artifacts (`reports/anneal-mir-to-x86-rustc-capture-and-byte-provenance-semantics/support/`):**
  - `support/ByteMemoryProvenanceProbe.lean` (`sha256: d584229501aa70396798f81fe77666cc09bdc1c0d1ca6ccb05f95045389a336b`, 2,625 lines, 0 `sorry`).
  - `support/Phase3SemanticsProbe.lean` (`sha256: 348282b85d13eb49c685e639adfac4e0627e6dd4d7f9ea9e289d8755e4b89379`, 4,862 lines, 0 `sorry`).
  - `support/probe_6cat.rs` (`sha256: 8d4f9acf88995a4e354635a8fba058b17a26f8e82ae8d24c097c39c6379a8c50`).
  - `support/layout_mir_driver.rs` (`sha256: e79065ef77adf4a879e0278e1deabe1d94e62f34d4e3fd4ebc75152c8921d0a9`).
  - `support/monomorph_mir_driver.rs` (`sha256: 76a5061bd910780d1a55169f63ee2dea293f1b78848a52a7857483a19ebd7e60`).
  - `support/driver_extracted_metadata.txt` (`sha256: 87c1d3647146d498a7018001a96d37d3fffda0894825c7abe120e01ac3743641`).
  - `support/monomorph_driver_output.txt` (`sha256: a4c4018d664ef0c3f197e5977b1b2bfa225c9265c689ffcd54641fc93a10c7c0`).

## Revalidation

Run the two standalone `prelude`-only Lean 4.34.1 probes and the two
`rustc_driver` extractors:

```bash
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/ByteMemoryProvenanceProbe.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/Phase3SemanticsProbe.lean

rustc --edition=2021 support/layout_mir_driver.rs -o /tmp/layout_mir_driver
/tmp/layout_mir_driver support/probe_6cat.rs --crate-type=lib --edition=2021 \
  -C panic=abort -C debug-assertions=off -Z mir-opt-level=0

rustc --edition=2021 support/monomorph_mir_driver.rs -o /tmp/monomorph_mir_driver
/tmp/monomorph_mir_driver support/probe_6cat.rs --crate-type=lib --edition=2021 \
  -C panic=abort -C debug-assertions=off -Z mir-opt-level=0
```
