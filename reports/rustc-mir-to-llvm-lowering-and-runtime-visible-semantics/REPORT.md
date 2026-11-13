# MIR-to-LLVM-IR Lowering and Runtime-Visible Semantics in rustc 1.99.1

## Summary

`rustc_codegen_ssa::mir` (`9.6K` lines across 14 modules) lowers monomorphic
`Runtime(Optimized)` MIR to backend IR through `BuilderMethods` (`139` methods),
and `rustc_codegen_llvm` (`31.1K` lines) materializes those calls as LLVM
`23.1.1` IR:
1. **Local and operand partitioning (`analyze.rs`, `locals.rs`, `operand.rs`):**
   Before instruction emission, `analyze::non_ssa_locals` scans the MIR body.
   Locals whose address is never taken, that are never projected into in memory,
   and whose `BackendRepr` is `Scalar`, `ScalarPair`, `SimdVector`, or ZST become
   **SSA `LocalRef::Operand` / `PendingOperand`** values (`OperandValue::Immediate(V)`,
   `Pair(V, V)`, or `ZeroSized`), completely bypassing stack `alloca`s even at
   `-Copt-level=0`. All other locals become `LocalRef::Place(PlaceRef)` backed by
   entry-block `alloca`s (`OperandValue::Ref(PlaceValue)`). Notably, `bool` has
   immediate type `i1` in SSA `OperandValue::Immediate`, but memory type `i8`
   when stored to or loaded from a `PlaceRef`.
2. **Construct-by-construct lowering (`statement.rs`, `rvalue.rs`, `block.rs`, `place.rs`):**
   Every `StatementKind` (13 variants), `Rvalue` (13 variants), `CastKind` (12
   variants), `ProjectionElem` (8 variants), and `TerminatorKind` (15 variants)
   maps deterministically to `BuilderMethods` calls (preserved in
   `support/per_construct_lowering_table.json` and `support/golden_o0.{mir,ll}`).
   Experimental Miri-style pointer retagging (`-Zcodegen-emit-retag`) traverses a
   per-layout `RetagPlan` (`retag.rs:30-100`) to emit runtime retag calls on
   function entry, return, and `StatementKind::Assign`.
3. **Runtime-visible lowering choices (`block.rs`, `base.rs`, `PassWrapper.cpp`):**
   - **Asserts and panics:** `TerminatorKind::Assert` lowers to a conditional
     branch weighted `2000:1` (`!prof`) toward the normal target and a `cold`
     block that calls `core::panicking::panic_const::panic_const_*` (for overflow,
     div-by-zero,rem-by-zero, coroutine resumption), `panic_bounds_check`, or
     `panic_misaligned_pointer_dereference`, passing an implicit `&core::panic::Location`
     as the final argument (`#[track_caller]`).
   - **`unreachable` vs `abort`:** `core::intrinsics::abort()` emits `@llvm.trap()`
     followed by `unreachable`, whereas `std::process::abort()` invokes `libc::abort()`.
     Crucially, `TerminatorKind::Unreachable` (including `core::hint::unreachable_unchecked()`)
     emits LLVM's `unreachable` terminator, **and `rustc` sets
     `Options.TrapUnreachable = true` (plus `Options.NoTrapAfterNoreturn = true`
     on non-Wasm, non-Windows targets) in
     `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:390-410`**, instructing
     LLVM's machine backend to emit a hardware trap instruction (`ud2` on x86,
     `brk #0x1` on AArch64) instead of falling through into adjacent code when an
     `unreachable` block is not eliminated by control-flow optimization.
   - **Generated `main` shim (`base.rs:500-635`):** `maybe_create_entry_wrapper`
     emits the C ABI `main(int argc, char **argv) -> int` (or `efi_main` on UEFI),
     which passes `rust_main`, `argc`, `argv`, and `sigpipe` to the `#[lang = "start"]`
     entry item (`std::rt::lang_start`).

## Applicability

These findings apply to `rust-lang/rust` `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) and LLVM `23.1.1`
(`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`). All golden IR observations in
`support/golden_o0.{mir,ll}` were produced on `x86_64-unknown-linux-gnu` at
`-Copt-level=0 -Zmir-opt-level=0`.

## Findings

### 1. Local Storage Classification (`LocalRef`) and `OperandValue` Invariants

`Basis: source (compiler/rustc_codegen_ssa/src/mir/mod.rs:107-198, analyze.rs, operand.rs:28-140, place.rs:70-160)`

1. **`LocalRef` partitioning (`mir/mod.rs:146-162`, `analyze.rs`):**
   - `LocalRef::Operand(OperandRef)` / `LocalRef::PendingOperand`: used whenever a
     local's `TyAndLayout` is SSA-standalone (`BackendRepr::Scalar`, `ScalarPair`,
     `SimdVector`, `SimdScalableVector`, or zero-sized `Memory`) and `non_ssa_locals`
     confirms the local is never borrowed (`Rvalue::Ref` / `RawPtr`), never has a
     partial field written in place, and is assigned only by rvalues that produce
     `OperandRef`.
   - `LocalRef::Place(PlaceRef)`: allocates stack memory in the LLVM function's
     entry block via `PlaceRef::alloca(bx, layout)` with `layout.align.abi`.
   - `LocalRef::UnsizedPlace(PlaceRef)`: holds an indirect thin pointer `alloca`
     pointing to an unsized by-value parameter (`unsized_fn_params`).
2. **`OperandValue<V>` four-variant representation (`operand.rs:28-138`):**

| `OperandValue<V>` Variant | Required `BackendRepr` (`is_expected_variant_for_type`) | LLVM Value Representation |
| :--- | :--- | :--- |
| `Immediate(V)` | `BackendRepr::Scalar(..)`, `SimdVector`, `SimdScalableVector` | Single SSA value (`immediate_backend_type`). Note: `Scalar` `bool` is `i1` in `Immediate`, converted via `zext i1 to i8` (`from_immediate`) on store and `trunc i8 to i1` (`to_immediate_scalar`) on load (`!range !{i8 0, i8 2}`) |
| `Pair(V, V)` | `BackendRepr::ScalarPair(a, b)` | Two SSA immediate values `(a, b)` where `a` is at byte offset `0` and `b` is at its aligned offset (used for `&[T]`, `&dyn Trait`, `(u64, u64)`, `Result<u32, u32>`, and `*WithOverflow` results) |
| `Ref(PlaceValue<V>)` | `BackendRepr::Memory { sized }` with `!layout.is_zst()` | Pointer `llval` (plus optional wide metadata `llextra` and `align: Align`) pointing to stack/global memory; `load_operand` does not copy bytes until `store_with_annotation` emits `llvm.memcpy` |
| `ZeroSized` | `BackendRepr::Memory { .. }` with `layout.is_zst()` | Zero runtime bytes; no LLVM value emitted (or `poison` if an FFI signature requires a dummy value) |

### 2. Construct-by-Construct MIR-to-LLVM-IR Lowering Specification

`Basis: source + execution (compiler/rustc_codegen_ssa/src/mir/{statement,rvalue,block,place,intrinsic,debuginfo,retag}.rs, support/per_construct_lowering_table.json, support/golden_o0.ll)`

| MIR Construct | `rustc_codegen_ssa` / `rustc_codegen_llvm` Lowering Rule |
| :--- | :--- |
| **Projections (`place.rs`)** | `ProjectionElem::Deref` loads `OperandRef` and calls `.deref(align)` to unpack `(llptr, llextra)`. `Field(idx, ty)` emits `struct_gep` or byte-offset `gep` and updates `PlaceValue::align = min(place.align, field_offset_align)`. `Index(local)` / `ConstantIndex` / `Subslice` emit `inbounds gep` on the element type and update slice length metadata in `llextra`. `Downcast(_, variant_idx)` narrows `PlaceRef::layout` to `layout.for_variant(cx, variant_idx)`. `OpaqueCast` and `UnwrapUnsafeBinder` re-layout the same `PlaceValue` at the target monomorphized type. |
| **Statements (`statement.rs:15-122`)** | `Assign(place, rvalue)` dispatches to `codegen_rvalue_operand` (for `PendingOperand`) or `codegen_rvalue` (for `PlaceRef`). `SetDiscriminant` writes the variant tag (`codegen_set_discr`). `StorageLive`/`StorageDead` emit `@llvm.lifetime.start.p0` / `@llvm.lifetime.end.p0` on `LocalRef::Place` allocas. `Intrinsic(Assume(op))` emits `@llvm.assume(i1)`. `Intrinsic(CopyNonOverlapping)` emits `unchecked_sumul(count, sizeof(T))` followed by `@llvm.memcpy.p0.p0.i64`. `FakeRead`, `AscribeUserType`, `ConstEvalCounter`, `PlaceMention`, `BackwardIncompatibleDropHint`, and `Nop` emit zero instructions. |
| **Rvalue::Use & Repeat (`rvalue.rs:107-250`)** | `Use(op, with_retag)` elides the store completely if `op` is an all-uninit constant; otherwise stores `op` into `dest` (attaching `!captures` read-only metadata when storing `&Freeze` with `WithRetag::Yes`). `Repeat(elem, count)` emits `@llvm.memset` with `undef` for uninit consts, `@llvm.memset` for single-byte scalars, or a 3-block counter loop for general types. |
| **Rvalue::Aggregate (`rvalue.rs:21-92, 254-335, 810-847`)** | When targeting a `PlaceRef`, `try_codegen_const_aggregate_as_immediate` packs all-constant single-variant structs/tuples of size `1, 2, 4, 8, 16` bytes into a single `i8..i128` store (`rvalue.rs:21-92`, visible in `golden_o0.ll` where ` [4u32, 5]` and `Pair { a: 3, b: 9 }` constants fold). Otherwise fields are stored in offset order and `codegen_set_discr` writes the enum tag. |
| **Rvalue::BinaryOp & UnaryOp (`rvalue.rs:656-746`)** | Checked `BinOp::*WithOverflow` calls `@llvm.{u,s}{add,sub,mul}.with.overflow.iN` and returns `OperandValue::Pair(val, oflow_i1)`. `BinOp::*Unchecked` emits `add/sub/mul/shl/lshr/ashr` with `nuw`/`nsw` flags. Wide-pointer `Eq`/`Ne`/`Lt`/etc. compare data pointers (`ptrtoint` when needed) and metadata (`llextra`) sequentially. `UnOp::PtrMetadata` extracts `llextra` from `Pair(ptr, meta)` (or `0` for thin pointers). |
| **Rvalue::Discriminant (`rvalue.rs:747-757`, `place.rs`)** | For `Variants::Single { index }`, returns constant discr for `index`. For `Variants::Multiple { TagEncoding::Direct }`, loads the tag scalar with `!range` metadata. For `TagEncoding::Niche { untagged_variant, niche_variants, niche_start }`, loads the niche scalar, wrapping-subtracts `niche_start`, checks `icmp ule` against the niche range width, and `select`s between the computed niche variant and `untagged_variant`. |
| **Rvalue::Cast (`rvalue.rs:137-192, 501-628`)** | `PointerCoercion::Unsize` constructs `OperandValue::Pair(thin_ptr, vtable_or_len)` (or coerces custom smart-pointer structs field-by-field via `coerce_unsized_into`). `IntToInt` emits `trunc`/`zext`/`sext`. `FloatToInt` emits `@llvm.fptosi.sat` / `@llvm.fptoui.sat` (safe saturating cast!). `PointerExposeProvenance` emits `ptrtoint`; `PointerWithExposedProvenance` emits `inttoptr`; `Transmute` / `Subtype` bitcasts scalars/pairs or round-trips through an `alloca`. |
| **TerminatorKind::SwitchInt (`block.rs:1330-1410`)** | Single-arm `SwitchInt` (such as `bool` branch) emits `icmp eq` + `br i1 %cond, label %t, label %f` (attaching `!prof !{!"branch_weights", i32 1, i32 2000}` when one target is in `cold_blocks`). Multi-arm `SwitchInt` emits LLVM `switch iN %discr, label %otherwise [ ... ]`. |
| **TerminatorKind::Call & TailCall (`block.rs:985-1325`)** | Resolves callee (`InstanceKind::Virtual(def_id, idx)` loads slot `idx` from the receiver `Pair`'s vtable pointer via `meth::VirtualIndex::from_index(idx).get_fn`). Marshals arguments according to `FnAbi::args`: `PassMode::Ignore` (skipped), `PassMode::Direct(attrs)` (passed as single value with `noalias`/`nonnull`/`noundef`/`align`/`zext`/`sext`), `PassMode::Pair(a, b)` (passed as two arguments), `PassMode::Cast(target, pad)` (stored to temp/cast via integer/register tuple `CastTarget`), `PassMode::Indirect { attrs, meta_attrs, on_stack }` (copied to caller stack temporary `alloca` and passed by pointer with `byval` or `sret` for `FnAbi::ret`). If the callee has `#[track_caller]`, appends the caller's `Location` pointer. Emits `call` (if `UnwindAction::Unreachable` or `nounwind`) or `invoke ... to label %normal unwind label %landing_pad`. `TailCall` (`become`) emits `musttail call` followed immediately by `ret`. |
| **Cleanups, Landing Pads & Funclets (`block.rs:60-165, 1490-1645`)** | On Itanium ABI targets (`x86_64-unknown-linux-gnu`), each cleanup entry block gets a `landingpad { ptr, i32 } cleanup` instruction that stores `{ exc_ptr, selector }` into `FunctionCx::personality_slot`, and `UnwindResume` reloads `personality_slot` and executes `resume { ptr, i32 }`. On Windows MSVC SEH / Wasm EH (`wants_new_eh_instructions`), cleanup blocks use `cleanuppad within none []` funclets and `cleanupret from %funclet unwind to caller`. |
| **Naked Functions (`naked_asm.rs`)** | Functions with `#[unsafe(naked)]` skip `FunctionCx` MIR statement lowering entirely; `naked_asm.rs` emits a module-level raw assembly block or a single `call void asm` + `unreachable` in a `naked` attribute LLVM function. |
| **Experimental Retag Emission (`retag.rs:1-536`)** | When `-Zcodegen-emit-retag` is active, `RetagPlan::build` recursively inspects `TyAndLayout` for `&T`, `&mut T`, and `Box<T>` (skipping `MaybeDangling<T>` and types smaller than `pointer_size`) and emits external retag hook calls on function entry, assignment rvalues, and returns. |

### 3. Runtime-Visible Lowering: Panics, Asserts, `#[track_caller]`, Aborts, UB Checks, and `main`

`Basis: source + execution (compiler/rustc_codegen_ssa/src/mir/block.rs:850-980, compiler/rustc_codegen_ssa/src/base.rs:500-635, compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:390-410, support/golden_o0.{mir,ll})`

1. **Assert lowering and panic lang items (`block.rs:850-980`, `support/golden_o0.ll`):**
   Every `TerminatorKind::Assert { cond, expected, msg, target, unwind }` lowers to:
   - An `icmp eq i1 %cond, expected` (with `@llvm.expect.i1` and `!prof` branch
     weights `2000` for `target` vs `1` for the failure block);
   - A failure basic block marked `cold` that calls the `AssertKind`-specific
     `#[lang = "..."]` function in `core::panicking`:
     - `AssertKind::Overflow(BinOp::Add, l, r)` $\rightarrow$ `core::panicking::panic_const::panic_const_add_overflow(&Location)`
     - `AssertKind::Overflow(BinOp::Sub / Mul / Shl / Shr, ..)` $\rightarrow$ `panic_const_{sub,mul,shl,shr}_overflow(&Location)`
     - `AssertKind::OverflowNeg(_)` $\rightarrow$ `panic_const_neg_overflow(&Location)`
     - `AssertKind::DivisionByZero(_)` / `RemainderByZero(_)` $\rightarrow$ `panic_const_{div,rem}_by_zero(&Location)`
     - `AssertKind::BoundsCheck { len, index }` $\rightarrow$ `core::panicking::panic_bounds_check(index, len, &Location)`
     - `AssertKind::MisalignedPointerDereference { required, found }` $\rightarrow$ `core::panicking::panic_misaligned_pointer_dereference(required, found, &Location)`
     - `AssertKind::NullPointerDereference` $\rightarrow$ `core::panicking::panic_null_pointer_dereference(&Location)`
     - `AssertKind::InvalidEnumConstruction(tag)` $\rightarrow$ `core::panicking::panic_invalid_enum_construction(tag, &Location)`
2. **`#[track_caller]` and `Location::caller()` (`mir/mod.rs:128-130`, `block.rs:1050-1085`):**
   - When a function is annotated with `#[track_caller]` (such as
     `checked_add_and_assert` in `support/golden_o0.ll`), `FnAbi` appends an
     extra implicit parameter `ptr noalias noundef readonly align 8 dereferenceable(24) %0`
     (`&'static core::panic::Location<'static>`) to its signature (`fn(i32, i32, ptr) -> i32`).
   - Inside a `#[track_caller]` function, `FunctionCx::caller_location` holds that
     implicit parameter, so any nested `Assert` or call to another `#[track_caller]`
     function (including `core::panic::Location::caller()`) forwards `%0` instead
     of materializing a static `Location` constant for the interior span!
   - When a `#[track_caller]` function is coerced to a `fn` pointer, `ShimKind::Reify`
     generates a wrapper with standard ABI `(i32, i32) -> i32` that supplies the
     function definition's own static `&Location` as the third argument.
3. **`intrinsics::abort`, `process::abort`, and `TrapUnreachable` (`PassWrapper.cpp:390-410`):**
   - `core::intrinsics::abort()` lowers via `bx.abort(); bx.unreachable();` to
     `call void @llvm.trap()` followed by `unreachable` (emitted as `ud2` on
     x86-64, terminating with `SIGILL`).
   - `std::process::abort()` calls the C library `abort()` function (terminating
     with `SIGABRT`) or `fastfail` on Windows.
   - `TerminatorKind::Unreachable` (produced by `core::hint::unreachable_unchecked()`,
     uninhabited match arms, and infinite loops without side effects) emits LLVM
     `unreachable`. Because `PassWrapper.cpp:390-410` configures LLVM's
     `TargetOptions` with `Options.TrapUnreachable = true` (and
     `Options.NoTrapAfterNoreturn = true` on non-Wasm, non-Windows targets), any
     `unreachable` block that survives LLVM's IR optimizer is emitted as a
     hardware trap instruction (`ud2` / `brk #0x1`) rather than falling off the
     end of the function.
4. **Differences under `-Cpanic=abort` vs `-Cpanic=unwind`:**
   - At the MIR level (`AbortUnwindingCalls`), calls that can unwind inside a
     `panic=abort` session (or inside an `extern "C"` nounwind function) have
     their unwind edges rewritten to `UnwindAction::Terminate` (or `Unreachable`
     when `-Cpanic=abort` makes all Rust calls `nounwind`).
   - At the LLVM IR level, `FnAbi::can_unwind` returns `false` for Rust functions
     under `-Cpanic=abort` (except `extern "C-unwind"`), so `rustc_codegen_llvm`
     marks functions `nounwind`, emits `call` instead of `invoke`, and omits
     `.gcc_except_table` LSDA unwinding tables.
   - If an `extern "C-unwind"` call unwinds into a cannot-unwind frame, the
     landing pad branches to `FunctionCx::terminate_blocks`, which calls
     `core::panicking::panic_cannot_unwind()` (`UnwindTerminateReason::Abi`) or
     `core::panicking::panic_in_cleanup()` (`UnwindTerminateReason::InCleanup`).
5. **The generated `main` entry point (`compiler/rustc_codegen_ssa/src/base.rs:500-635`, `support/golden_o0.ll`):**
   In the CGU containing the user's `fn main()`, `maybe_create_entry_wrapper`
   synthesizes the C symbol `@main(i32 %0, ptr %1) -> i32`:
   ```llvm
   define noundef i32 @main(i32 %0, ptr %1) unnamed_addr #6 {
   top:
     %_7 = sext i32 %0 to i64
     %2 = call i64 @std::rt::lang_start::<()>(ptr @golden_probe::main, i64 %_7, ptr %1, i8 0)
     %3 = trunc i64 %2 to i32
     ret i32 %3
   }
   ```
   Here `i8 0` is the `#[unix_sigpipe]` disposition passed to `std::rt::lang_start`.

## Boundaries

- **Target-specific ABI `PassMode::Cast` classification:** The exact register vs
  stack classification rules for aggregates (`PassMode::Cast` vs `Indirect`) are
  computed per architecture in `compiler/rustc_target/src/callconv/*.rs` (26
  modules); `rustc_codegen_ssa` consumes the resulting `FnAbi` uniformly across
  architectures.

## Evidence

- **Support artifacts:**
  - `support/generate_golden_lowering.py`
  - `support/per_construct_lowering_table.json`
  - `support/golden_o0.mir`
  - `support/golden_o0.ll`
- **Primary source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_codegen_ssa/src/mir/mod.rs:51-198` (`FunctionCx`, `LocalRef`)
  - `compiler/rustc_codegen_ssa/src/mir/operand.rs:28-175` (`OperandValue`, `OperandRef`)
  - `compiler/rustc_codegen_ssa/src/mir/place.rs:70-534` (`PlaceRef`, projections, discriminants)
  - `compiler/rustc_codegen_ssa/src/mir/statement.rs:11-123` (`codegen_statement`)
  - `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:21-874` (`codegen_rvalue`, `codegen_rvalue_operand`)
  - `compiler/rustc_codegen_ssa/src/mir/block.rs:60-1760` (`codegen_terminator`, calls, asserts, switches, cleanups)
  - `compiler/rustc_codegen_ssa/src/mir/retag.rs:1-100` (`RetagPlan`)
  - `compiler/rustc_codegen_ssa/src/base.rs:500-635` (`maybe_create_entry_wrapper`)
  - `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:390-410` (`Options.TrapUnreachable`, `Options.NoTrapAfterNoreturn`)

## Revalidation

Run `support/generate_golden_lowering.py`:

```bash
python3 reports/rustc-mir-to-llvm-lowering-and-runtime-visible-semantics/support/generate_golden_lowering.py \
  --toolchain 1.99.1-x86_64-unknown-linux-gnu \
  --out-dir /tmp/golden_lowering
```

Diff `/tmp/golden_lowering/golden_o0.mir` and `/tmp/golden_lowering/golden_o0.ll`
against `support/golden_o0.mir` and `support/golden_o0.ll`.
