# Catalog of `rustc` 1.99.1 LLVM IR Attributes, Instruction Flags, Metadata, Globals, and Cross-Path Obligations

## Summary

When `rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) lowers
`Runtime(PostCleanup)` MIR to LLVM 23.1.1 IR (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`)
in `compiler/rustc_codegen_llvm`, it communicates semantic guarantees to the
LLVM optimizer across six channels:

1. **50 enum attributes (`AttributeKind` in `llvm/ffi.rs:272-322`) and 39 string
   attributes (`attributes.rs`, `abi.rs`, `builder.rs`)** placed on functions,
   parameters (`AttributePlace::Argument(i)`), return values
   (`AttributePlace::ReturnValue`), and call sites (`apply_to_callsite`).
2. **Instruction-level poison-producing flags**: integer arithmetic (`nuw`,
   `nsw`, `exact` in `builder.rs:270-480`), bitwise/conversion flags (`disjoint`
   on `or`, `nneg` on `zext`, `samesign` on `icmp`), `getelementptr inbounds`
   (`nuw` / `inbounds`), and `fast-math` flags (`afn`, `reassoc`, `nnan`,
   `ninf`, `nsz`, `arcp`, `contract` on algebraic intrinsics).
3. **42 fixed instruction/global metadata kinds (`MetadataKindId` in
   `llvm/metadata_kind.rs:28-71`)**, of which `rustc` actively emits `!range`,
   `!noundef`, `!nonnull`, `!align`, `!alias.scope`, `!noalias`,
   `!invariant.load`, `!nontemporal`, `!dbg`, `!DIAssignID`, `!type`,
   `!kcfi_type`, `!vcall_visibility`, `!associated`, `!prof`, `!unpredictable`,
   and `!nosanitize` (while never emitting C/C++ `!tbaa` or `!tbaa.struct`).
4. **Global variable and function symbol properties (`consts.rs`,
   `mono_item.rs`, `declare.rs`)**: `Linkage` (17 variants), `Visibility`
   (`Default`, `Hidden`, `Protected`), `UnnamedAddr` (`No`, `Local`, `Global`),
   `dso_local`, `DllStorageClass`, `Comdat`, `ThreadLocalMode`, `constant` vs.
   `global`, `section`, and `@llvm.used` / `@llvm.compiler.used`.
5. **19 module flags (`llvm.module.flags` in `context.rs:260-540`)**: `PIC
   Level`, `PIE Level`, `Code Model`, `RtLibUseGOT`, `uwtable`,
   `frame-pointer`, `cfguard`, `ehcontguard`, `cf-protection-branch`,
   `cf-protection-return`, `function_return_thunk_extern`,
   `indirect_branch_cs_prefix`, `branch-target-enforcement`,
   `sign-return-address`, `sign-return-address-all`,
   `sign-return-address-with-bkey`, `branch-protection-pauth-lr`,
   `guarded-control-stack`, `kcfi`, `kcfi-offset`, `kcfi-arity`, `CFI Canonical
   Jump Tables`, `cfi-normalize-integers`, `EnableSplitLTOUnit`, and `Virtual
   Function Elim`.
6. **Target-CPU and target-feature attributes (`target-cpu`, `tune-cpu`,
   `target-features`)**, attached to every emitted function (`attributes.rs:638-684`)
   to govern subtarget instruction selection and gate cross-function ThinLTO
   inlining.

For a composite or verified compiler that interoperates with LLVM-compiled
crates or CGUs, every attribute or metadata node emitted at a call boundary
creates a **bidirectional semantic obligation**:

- **Caller-to-callee obligation (when calling an LLVM-compiled function)**: The
  alternative backend must satisfy every parameter precondition LLVM assumes at
  function entry (`noundef`, `nonnull`, `align N`, `dereferenceable(N)`,
  `noalias`, `zext`/`sext` high-bit extension, `inreg`, `sret`, `byval`, and
  valid scalar niche ranges).
- **Callee-to-caller obligation (when called by an LLVM-compiled function)**:
  The alternative backend must honor every postcondition and effect bound LLVM
  attaches to the call site (`noundef` and `!range` on return values, `readonly`
  + `captures(none)` deduced by `deduce_param_attrs.rs` on indirect `Freeze`
  arguments, `nounwind` on `extern "C"` / `panic=abort` functions, and
  callee-saved register/frame-pointer/unwind conventions).

## Applicability

- **Primary baseline**: `rust-lang/rust` `1.99.1`
  (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `rust-lang/llvm-project`
  `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), verified unchanged in
  structure across `1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`) and
  `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).
- **Scope**: Complete inventory of attributes, flags, metadata, globals, and
  module flags emitted by `rustc_codegen_llvm`, their origin in Rust type/MIR
  analysis, their LLVM 23.1.1 LangRef semantics (UB vs. poison), and the exact
  obligations imposed on foreign/verified compilation paths.

## Findings

### 1. Parameter, Return-Value, and Call-Site Attributes (`ArgAttributes` & `FnAbi`)

`Basis: source + normative + execution`

`compiler/rustc_ty_utils/src/abi.rs:420-690` populates `ArgAttributes` on each
`ArgAbi` in `FnAbi`, and `compiler/rustc_codegen_llvm/src/abi.rs:38-136` lowers
them to LLVM parameter, return, and call-site attributes:

| LLVM Attribute | `AttributeKind` / Constructor (`abi.rs`) | When `rustc` Emits It (`rustc_ty_utils/src/abi.rs`) | LLVM 23.1.1 LangRef Semantics (Poison vs. Immediate UB) | Justification in Rust Semantics & Cross-Path Obligation |
| :--- | :--- | :--- | :--- | :--- |
| `noundef` | `AttributeKind::NoUndef` (33) | At `-Copt-level >= 1` (or with MSan at `-O0`) on scalar/pair arguments and returns whose layout has no uninitialized bits (`abi.rs:80-110`, `ty_utils/abi.rs:512-555`), and on all indirect pointer arguments (`&T`, `&mut T`, `Box<T>`, `PassMode::Indirect`). | **Immediate UB** if any bit of the argument or return value is `undef` or `poison` at the call/return boundary. | Rust scalar values (`bool`, integers, floats, references, raw pointers) cannot hold uninitialized bytes; passing uninitialized padding in a direct register or returning uninitialized bits from another backend triggers immediate UB in LLVM callers/callees. |
| `nonnull` | `AttributeKind::NonNull` (9) | On `&T`, `&mut T`, `Box<T>`, `NonNull<T>` (when `pointee_size == 0` or `NoFree` is absent; absorbed into `dereferenceable(N)` when `N > 0` and `NoFree` holds, `abi.rs:84-91`) and `PassMode::Indirect` pointers. | **Poison value** if the pointer is null; combined with `noundef`, passing null is **immediate UB**. | References, boxes, and indirect ABI pointers are non-null by Rust validity. Foreign/verified code must never pass a null pointer for a reference or `PassMode::Indirect` slot. |
| `align N` | `CreateAlignmentAttr(llcx, N)` | Always (even at `-O0`, `abi.rs:70-72`) on `&T`, `&mut T`, `Box<T>`, and `PassMode::Indirect` (including `sret` and `byval`), where `N = pointee_align.unwrap_or(layout.align.abi)`. | **Poison value** if pointer low bits `(ptr & (N - 1)) != 0`; combined with `noundef`, passing an unaligned pointer is **immediate UB**. | References and indirect ABI slots must be aligned to `layout.align.abi`. Another backend allocating a caller stack slot for `PassMode::Indirect` or `sret` must align that stack slot to at least `N` bytes! |
| `dereferenceable(N)` / `dereferenceable_or_null(N)` | `CreateDereferenceableAttr` / `CreateDereferenceableOrNullAttr` | At `-Copt-level >= 1` when `pointee_size == N > 0` and `ArgAttribute::NoFree` is set (`&T`, `&mut T`, `Box<T>`, `PassMode::Indirect`, `abi.rs:81-91`). | **Immediate UB** if `[ptr, ptr + N)` is not dereferenceable (readable, and not freed during the call because LLVM `dereferenceable` on arguments currently implies `nofree` for the call duration). | Backed by Rust reference validity and `Box` ownership (`-Zbox-noalias`, default `true`). Callees must not deallocate a `dereferenceable(N) nofree` argument before returning. |
| `noalias` | `AttributeKind::NoAlias` (6) | At `-Copt-level >= 1` on `&mut T`, `&T` where `T: Freeze` (`!T.has_unsafe_cell()`), `Box<T>` (`-Zbox-noalias=yes`), `PassMode::Indirect` (`sret` and by-value indirect args), and allocator return values (`attributes.rs:596, 612`). | Pointer provenance rule (C99 `restrict`): **immediate UB** on conflicting memory access if any memory modified through this pointer (or through another pointer for a `readonly noalias` shared reference) is accessed via a pointer not based on this parameter during the call. | Justified by Stacked Borrows / Tree Borrows uniqueness (`&mut T`, `Box<T>`) and immutability of shared `Freeze` references (`&T`). Another backend must not mutate memory reachable through a `&T` (`T: Freeze`) or alias a `&mut T` / `sret` pointer. |
| `readonly` | `AttributeKind::ReadOnly` (14) | At `-Copt-level >= 1` on `&T` when `T: Freeze`, and on `PassMode::Indirect { on_stack: false }` parameters when either `T: Freeze` is deduced `ReadOnly` by `deduce_param_attrs.rs` or in `FnAbi` when not mutated. | **Immediate UB** if the callee writes to memory through this pointer (even writing the same value back!). | **Critical cross-path hazard**: Because `deduce_param_attrs.rs:174-239` marks a by-value `PassMode::Indirect` parameter `ReadOnly` whenever the MIR body does not mutate it, a verified/alternative backend **must treat incoming `PassMode::Indirect` caller pointers as read-only unless the MIR body explicitly mutates the parameter local** (it must copy to a local stack slot before any backend-inserted scratch write). |
| `writable` | `AttributeKind::Writable` (42) | At `-Copt-level >= 1` on `sret` return pointers and `&mut T` (when `T: Freeze` and not pinned/uninitialized hazard, `ty_utils/abi.rs:475-495`). | Tells LLVM DSE/memcpyopt that `[ptr, ptr + N)` may be spuriously written (provided no concurrent reader exists) before being overwritten. | Callees/callers must never place a `writable` argument in read-only `.rodata` memory. |
| `dead_on_unwind` | `AttributeKind::DeadOnUnwind` (43) | On `sret` return pointers and indirect by-value arguments owned by the call frame (`ty_utils/abi.rs:480-510`). | Memory pointed to by the argument is dead if the function exits via unwinding; LLVM DSE may eliminate stores to `sret` along unwind paths. | Callers must not read from an `sret` destination slot if the call unwinds (`UnwindAction::Cleanup`). |
| `dead_on_return` | `AttributeKind::DeadOnReturn` (44) | On by-value `PassMode::Indirect` parameter slots whose lifetime ends when the callee returns (`ty_utils/abi.rs:500-510`). | Callee-owned indirect argument slot is dead after normal return; allows LLVM tail-call and stack-slot reuse optimizations. | Callers must treat the temporary stack copy passed to `PassMode::Indirect` as clobbered/dead after the call returns! |
| `captures(none)` / `captures(address)` / `captures(read_only)` | `CapturesNone` (46), `CapturesAddress` (7), `CapturesReadOnly` (45) | `CapturesNone` on `sret`, by-value `PassMode::Indirect` (when deduced by `deduce_param_attrs.rs`), and drop-in-place; `CapturesAddress` on deallocator arg 0 (`attributes.rs:622`). | `captures(none)`: callee does not retain any bit derived from the pointer or its provenance after returning. `captures(address)`: callee may compare/stash the integer address, but **accessing memory through the stashed pointer after return is UB**. | Any backend compiling a function whose MIR does not escape a `PassMode::Indirect` parameter must not stash that pointer in a global or return it. |
| `zext` / `sext` | `AttributeKind::ZExt` (18) / `SExt` (15) | Always (ABI-affecting, `abi.rs:73-77`) on narrow integers (`bool`, `u8`, `i8`, `u16`, `i16`) when target ABI requires caller/callee sign/zero extension (e.g., x86_64 Apple Darwin, i686, s390x, RISC-V). | Caller must zero/sign-extend sub-register integer arguments to 32/64 bits; callee must extend return values. Violation causes high-bit garbage (**immediate UB** if `noundef`). | Mandatory ABI requirement across all backends regardless of optimization level (`abi.rs:73`). |
| `inreg` | `AttributeKind::InReg` (19) | Always (ABI-affecting, `abi.rs:38-40`) on `i686` fastcall/regparm and AVR/MSP430/x86_64 Windows vectorcall. | Forces register assignment rather than stack passing. | Mandatory ABI requirement (`ABI_AFFECTING_ATTRIBUTES`). |
| `sret(T)` / `byval(T)` | `CreateStructRetAttr` / `CreateByValAttr` | Always on `PassMode::Indirect` return slot (`sret`) and `PassMode::Indirect { on_stack: true }` (`byval`, e.g., x86_64 SysV `MEMORY` class structs > 16B in `extern "C"`). | `sret`: hidden pointer in ABI return register (`%rdi`/`%x8`) returned in `%rax` on x86_64. `byval([N x i8])`: passed at a fixed stack offset in the caller's outgoing argument area. | Mandatory ABI requirement. Both `sret` and `byval` in `rustc` use `[N x i8]` byte-array types to preserve exact padding (`callconv/mod.rs:66-71`). |

---

### 2. Function-Level Attributes (`attributes.rs`, `declare.rs`, `mono_item.rs`)

`Basis: source + normative`

| Attribute | Source in `rustc_codegen_llvm` | Condition & Meaning | Cross-Path Obligation |
| :--- | :--- | :--- | :--- |
| `uwtable(sync \| async)` | `attributes.rs:190-198, 501-503` | Emitted whenever `sess.must_emit_unwind_tables()` is true (default `async` on all Tier 1 targets). | Every function on the call stack between a panic and `catch_unwind` must emit valid `.eh_frame` (or `.pdata`/`.xdata`) unwind tables. |
| `nounwind` | `AttributeKind::NoUnwind` (12) (`abi.rs:580-610`) | Emitted when `!fn_abi.can_unwind` (`extern "C"`, `panic=abort`, or intrinsics). | Unwinding out of a `nounwind` function into an LLVM caller is **immediate UB** (`rustc` wraps potentially panicking bodies in an abort landing pad when `!can_unwind`). |
| `noreturn` | `AttributeKind::NoReturn` (11) (`abi.rs:575`) | Emitted when return type is uninhabited (`!` / `abi.ret.layout.is_uninhabited()`). | Returning normally from a `noreturn` function executes `unreachable` in the caller (**immediate UB**). |
| `willreturn` | `AttributeKind::WillReturn` (29) | Emitted on pure intrinsics and allocator functions that are guaranteed to terminate. | Must not loop infinitely or abort when `willreturn` is attached. |
| ` inlinehint` / `alwaysinline` / `noinline` / `optnone` / `optsize` / `minsize` / `cold` | `attributes.rs:49-81, 448-527` | Controlled by `#[inline]`, `#[optimize]`, `-Copt-level=s/z`, and `#[cold]`. | Heuristic/pass controls; `#[optimize(none)]` emits `optnone` + `noinline`. |
| `memory(none)` / `memory(read)` | `MemoryEffects::None` / `ReadOnly` (`attributes.rs:528-533`) | Emitted for `#[ffi_const]` and `#[ffi_pure]` foreign functions. | Violation (reading/writing memory in `#[ffi_const]`, or writing in `#[ffi_pure]`) causes LLVM CSE/DCE miscompilation (**UB**). |
| `alloc-family="__rust_alloc"`, `allockind(...)`, `allocsize(N)`, `allocalign`, `allocatedptr` | `attributes.rs:568-625` | Emitted on `#[rustc_allocator]`, `#[rustc_deallocator]`, `#[rustc_reallocator]`, `#[rustc_allocator_zeroed]`. | Allows LLVM `InstCombine`/`Attributor` to elide unused heap allocations (`malloc`/`free` pairs) across `__rust_alloc` and `__rust_dealloc`! Any custom allocator shim must preserve exact `size`/`align` semantics. |
| `probe-stack="inline-asm"` or `"__rust_probestack"` | `attributes.rs:338-369` | Emitted when `sess.target.stack_probes != StackProbeType::None` (disabled under ASan/TSan or `-Cprofile-generate`). | Prevents stack-clash guard-page jumping on frames > 4096 bytes. |
| `stack-protector` (`ssp`, `sspstrong`, `sspreq`) | `attributes.rs:371-380` | Emitted when `-Zstack-protector=basic\|strong\|all`. | Requires `__stack_chk_guard` TLS/global and `__stack_chk_fail` symbol. |
| `frame-pointer="all" \| "non-leaf"` | `attributes.rs:212-223` | Emitted when `sess.target.frame_pointer != MayOmit` or `-Cforce-frame-pointers=yes`. | Preserves `%rbp`/`x29` frame chain for profilers and frame-pointer unwinders. |
| `nonlazybind` | `AttributeKind::NonLazyBind` (23) (`attributes.rs:438-444`) | Emitted when `!sess.needs_plt()` (`-Zplt=no`, default on Tier 1 x86_64). | Calls use GOT-indirect `call *[foo@GOTPCREL(%rip)]` instead of PLT stubs. |
| `target-cpu`, `tune-cpu`, `target-features` | `attributes.rs:412-434, 638-684` | Attached to every function; `#[target_feature(enable = "...")]` appends `+<feat>`. | An unverified/verified caller must not call a `#[target_feature]` function unless the CPU feature is dynamically detected or statically enabled. |

---

### 3. Instruction Flags and Metadata Kinds (`builder.rs`, `metadata_kind.rs`)

`Basis: source + normative + execution`

#### 3.1 Instruction-Level Poison and Fast-Math Flags

In `compiler/rustc_codegen_llvm/src/builder.rs`, `rustc` attaches the following
instruction flags:

- **`nuw` / `nsw` (`unchecked_add`, `unchecked_sub`, `unchecked_mul`,
  `unchecked_shl`, `unchecked_shr`, `neg`)**: Lowered from
  `BinOp::{AddUnchecked, SubUnchecked, MulUnchecked}` and enum discriminant
  arithmetic (`builder.rs:275-345`). Signed or unsigned wrap produces **poison**.
- **`exact` (`udiv exact`, `sdiv exact`, `ashr exact`, `lshr exact`)**: Lowered
  from `Intrinsic::exact_div` and pointer `offset_from_unsigned` / `offset_from`
  (`builder.rs:348-385`, `intrinsic.rs`). Non-zero remainder produces **poison**.
- **`disjoint` (`or disjoint`) and `nneg` (`zext nneg`)**: Emitted by LLVM or
  `rustc` when combining non-overlapping bitfields or zero-extending known
  non-negative signed integers; violating disjointness or non-negativity
  produces **poison**.
- **`inbounds` (and `nuw`) on `getelementptr`**: Emitted by `Builder::inbounds_gep`
  (`builder.rs:845-875`) for struct field projections, slice indexing, and
  `ptr::offset` / `ArithOffset`. Out-of-bounds address calculation outside the
  allocated object's bounds `[base, base + size]` (or wrapping the address
  space) produces a **poison pointer**.
- **Fast-Math Flags (`FastMathFlags` in `builder.rs:400-465`)**: Normal Rust
  `+`, `-`, `*`, `/`, `%` on `f16`/`f32`/`f64`/`f128` emit **no fast-math
  flags** (strict IEEE 754 semantics). Only `fadd_fast`, `fsub_fast`,
  `fmul_fast`, `fdiv_fast`, `frem_fast` (`core::intrinsics::f*_fast`) and
  `fadd_algebraic` (`reassoc nsz contract afn`) set LLVM fast-math flags (`nnan`,
  `ninf`, `nsz`, `arcp`, `contract`, `afn`, `reassoc`).

#### 3.2 Instruction and Global Metadata (`MetadataKindId` in `llvm/metadata_kind.rs`)

Of the 42 fixed metadata IDs (`MD_dbg = 0` through `MD_noalias_addrspace = 41`
in `compiler/rustc_codegen_llvm/src/llvm/metadata_kind.rs:28-71`), `rustc` 1.99.1
emits 18 and leaves 24 unused (including `MD_tbaa = 1` and `MD_tbaa_struct = 5`,
because Rust aliasing is type-agnostic and relies on `noalias` / `!alias.scope`
rather than C/C++ type-based alias analysis!):

| Metadata Kind | ID | Where Emitted (`rustc_codegen_llvm`) | Meaning & Violation Consequence |
| :--- | :--- | :--- | :--- |
| `!range ![lo, hi)` | `MD_range` (4) | `builder.rs:1410-1475` (`load_from_place` / scalar `valid_range` on `bool`, `char`, `NonZero*`, niche enums) and call return sites | Loaded/returned integer is in `[lo, hi)` (wrapping). Out-of-range value produces **immediate UB** if paired with `!noundef`, or **poison** otherwise. |
| `!noundef !{}` | `MD_noundef` (29) | `builder.rs:1420-1485` on loads of initialized scalar/pointer values (`!uninit` valid layout) | Loaded value contains no `undef` or `poison` bits; violation is **immediate UB** at the `load` instruction. |
| `!nonnull !{}` | `MD_nonnull` (11) | `builder.rs:1445-1460` on loads of non-null pointers (`&T`, `&mut T`, `Box<T>`, `NonNull<T>`, `fn` pointers) | Loaded pointer is non-null; loading null produces **poison** (or **immediate UB** with `!noundef`). |
| `!align !{i64 N}` | `MD_align` (17) | `builder.rs:1462-1474` on loads of references/boxes (`pointee_align`) | Loaded pointer is aligned to `N` bytes; unaligned pointer value is **poison** (**UB** with `!noundef`). |
| `!alias.scope` & `!noalias` | `MD_alias_scope` (7), `MD_noalias` (8) | `builder.rs` / `mir/block.rs` during `memcpy` and inlined functions | Scoped `noalias` metadata preserved across LLVM inlining (`ScopedNoAliasAA`). |
| `!invariant.load !{}` | `MD_invariant_load` (6) | `builder.rs:1395-1408` (`MemFlags::INVARIANT` on vtable loads and immutable static/promoted loads) | Memory location holds the same value for all time once dereferenceable; mutating a vtable or immutable static is **immediate UB**. |
| `!nontemporal !{i32 1}` | `MD_nontemporal` (9) | `builder.rs:1388, 1520` (`MemFlags::NONTEMPORAL` from `nontemporal_store`) | Cache-bypass hint (`movntdq` / `stnp`). |
| `!unpredictable !{}` | `MD_unpredictable` (15) | `intrinsic.rs` (`select_unpredictable`) | Tells LLVM backend to lower branch/select to conditional move (`cmov` / `csel`) rather than a predictable branch. |
| `!prof !{"branch_weights", ...}` | `MD_prof` (2) | `builder.rs` (`likely`, `unlikely`, cold panic branches, PGO) | Branch probability weights for block placement and inlining. |
| `!type` & `!vcall_visibility` & `!kcfi_type` | `MD_type` (19), `MD_vcall_visibility` (28), `MD_kcfi_type` (36) | `type_membership.rs` / `abi.rs` (when `-Zsanitizer=cfi` or `-Zsanitizer=kcfi` or `-Zvirtual-function-elimination` is enabled) | Type-test metadata for LLVM LTO CFI, KCFI indirect call hash checks, and virtual function elimination. |
| `!associated !{ptr @...}` | `MD_associated` (22) | `consts.rs` / `coverageinfo` | Ties metadata sections (`SHF_LINK_ORDER`) to their associated function/global for linker `--gc-sections`. |
| `!dbg` & `!DIAssignID` | `MD_dbg` (0), `MD_DIAssignID` (38) | `debuginfo/` | DWARF/CodeView source locations and assignment tracking (`experimental-assignment-tracking`). |

**Sample emitted LLVM IR (`support/llvm_ir_catalog.json`)**:
```llvm
define noundef i64 @ref_and_niche(
    ptr noalias noundef nonnull align 8 dereferenceable(8) %r,
    ptr noalias noundef readonly align 8 dereferenceable(72) captures(none) %shared,
    i64 noundef range(i64 1, 0) %nz,
    i1 noundef zeroext %b
) unnamed_addr #0
```
Notice how `rustc` 1.99.1 simultaneously attaches `noalias noundef readonly
align 8 dereferenceable(72) captures(none)` to `&BigPair`, `noundef range(i64 1,
0)` (i.e., $[1, 2^{64})$) to `NonZeroU64` and `Option<NonZeroU64>` return value,
and `noundef zeroext` to `bool`!

---

### 4. Global Properties and Module Flags (`mono_item.rs`, `consts.rs`, `context.rs`)

`Basis: source + execution`

- **`unnamed_addr` vs `local_unnamed_addr` (`mono_item.rs:160-210`, `consts.rs`)**:
  All non-exported functions and immutable promoted/anonymous allocations
  receive `unnamed_addr` (`UnnamedAddr::Global`), allowing LLVM `GlobalMerge` and
  linker `--icf=safe` to merge identical bodies because their address is not
  significant. Exported or `#[no_mangle]` globals receive `No` (`UnnamedAddr::No`).
- **`dso_local` (`mono_item.rs:215-260`, `consts.rs:533`)**: Set on hidden/internal
  definitions and non-interposable symbols (`should_assume_dso_local`), allowing
  direct RIP-relative `lea`/`call` instead of GOT indirection.
- **Module Flags (`context.rs:260-540`)**: All 19 module flags (cataloged in
  `support/llvm_ir_catalog.json`) carry explicit `ModuleFlagMergeBehavior`
  (`Error`, `Warning`, `Override`, `Max`, `Min`) enforced by the LLVM linker
  during LTO. In particular, `Code Model` and `NumRegisterParameters` use
  `Error`, `uwtable` and `frame-pointer` use `Max`, and AArch64 branch-protection
  flags (`branch-target-enforcement`, `sign-return-address`, etc.) use `Min` (so
  linking one unprotected module into an LTO unit downgrades the module-wide
  flag unless all modules carry it!).

## Boundaries

- **Target-specific intrinsics (`not examined` exhaustively)**:
  `compiler/rustc_codegen_llvm/src/intrinsic.rs` maps architecture-specific
  `std::arch` vendor intrinsics directly to `@llvm.<arch>.*` intrinsics; their
  per-instruction semantics are governed by the target ISA specification rather
  than general MIR-to-LLVM attribute lowering.
- **Enzyme autodiff and GPU offload metadata (`unsupported` on stable)**:
  `enzyme_ffi.rs` and `gpu_offload.rs` emit experimental `!enzyme_*` and offload
  annotations only under unstable `-Zautodiff` and `-Zoffload` flags.

## Evidence

- **Primary source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `compiler/rustc_codegen_llvm/src/llvm/ffi.rs:186-322` (`Linkage`,
    `Visibility`, `UnnamedAddr`, `DLLStorageClass`, `UWTableKind`,
    `FramePointerKind`, and all 50 `AttributeKind` variants).
  - `compiler/rustc_codegen_llvm/src/llvm/metadata_kind.rs:1-71` (all 42
    `MetadataKindId` constants).
  - `compiler/rustc_codegen_llvm/src/abi.rs:38-136, 540-762` (`ArgAttributesExt`,
    `ABI_AFFECTING_ATTRIBUTES`, `OPTIMIZATION_ATTRIBUTES`,
    `CAPTURES_ATTRIBUTES`, `FnAbiLlvmExt`).
  - `compiler/rustc_codegen_llvm/src/attributes.rs:1-690` (`llfn_attrs_from_instance`,
    allocator attributes at lines 568-625, branch protection at lines 543-566,
    target-cpu/features at lines 638-685).
  - `compiler/rustc_codegen_llvm/src/context.rs:250-545` (module flags).
  - `compiler/rustc_codegen_llvm/src/builder.rs:270-480, 845-875, 1380-1525`
    (instruction flags and load/store metadata).
  - `compiler/rustc_ty_utils/src/abi.rs:420-690` and
    `compiler/rustc_mir_transform/src/deduce_param_attrs.rs:1-239`.
- **Support artifacts**:
  - `support/llvm_ir_catalog.json`: Complete machine-readable catalog of all 50
    `AttributeKind` discriminants, 42 `MetadataKindId` constants, 39 string
    attributes, 19 module flags, and emitted LLVM IR specimen from `rustc`
    1.99.1.

## Revalidation

Run the following check against a newer `rustc` checkout to detect any added or
modified LLVM attributes, metadata kinds, or module flags:

```console
git -C <rust-checkout> diff 58cf8f9c35b355199727627d07ae34a4e2846d67 -- \
  compiler/rustc_codegen_llvm/src/llvm/ffi.rs \
  compiler/rustc_codegen_llvm/src/llvm/metadata_kind.rs \
  compiler/rustc_codegen_llvm/src/abi.rs \
  compiler/rustc_codegen_llvm/src/attributes.rs \
  compiler/rustc_codegen_llvm/src/context.rs \
  compiler/rustc_mir_transform/src/deduce_param_attrs.rs
```
