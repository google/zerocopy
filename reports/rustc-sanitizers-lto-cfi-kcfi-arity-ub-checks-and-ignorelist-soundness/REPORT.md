# Rustc Runtime UB-Check MIR Passes, LTO CFI vs. KCFI Arity, Sanitizer Instrumentation, and Ignorelist Blame Soundness

## Summary

This report establishes primary-source, empirical, and mechanized ground truth for four interacting runtime-checking and instrumentation subsystems in `rustc` and their boundary with formal MIR verification in Anneal:

1. **MIR Runtime UB-Check Passes (`CheckAlignment`, `CheckNull`, `CheckEnums`, shared helper `check_pointers`):** All three passes execute as the first three passes of `run_optimization_passes` immediately after `MirPhase::Runtime(RuntimePhase::PostCleanup)`, bail out if `LangItem::PanicImpl` is absent, and emit non-unwinding `TerminatorKind::Assert` checks (`UnwindAction::Unreachable`, lowering to `#[rustc_nounwind]` lang items in `core::panicking`). They are **sound with respect to false positives** over well-defined non-packed executions, yet **strictly incomplete** relative to Miri:
   - `CheckAlignment` excludes `[bool, i8, u8]` (notably *not* `()`, which receives a trivially satisfied `addr & 0 == 0` check at `-O0` that `-O2` folds away), follows field projections on borrows (`BorrowedFieldProjectionMode::FollowProjections`), and clamps the alignment mask by `target.max_reliable_alignment()`. Consequently, `&(*misaligned_p).u8_field` succeeds under both `-Z ub-checks=yes` and Miri.
   - `CheckNull` excludes no types and does *not* follow field projections (`BorrowedFieldProjectionMode::NoFollowProjections`), checking the raw base pointer before any field offset is added. It distinguishes reference formation (`SharedBorrow`/`Borrow`, checked unconditionally even for zero-sized types) from non-borrow dereference reads/writes (guarded by `size_of::<T>() != 0`). Thus `*null::<()>()` succeeds while `&*null::<()>()` and `&(*null::<AlignedStruct>()).tail` abort. Between `rust-lang/rust@14210df0e` (`1.98.0-nightly`) and `rust-lang/rust@342d74463`, `CheckNull` split its failure kind from a unified `AssertKind::NullPointerDereference` into `AssertKind::NullReferenceConstructed` for borrows versus `AssertKind::NullPointerDereference` for dereferences.
   - `CheckEnums` inspects *only* `Rvalue::Cast(CastKind::Transmute, op, ty)` where `ty` is an enum ADT, covering `Variants::Empty` (when the source operand is inhabited), `Variants::Multiple { TagEncoding::Direct }` (`SwitchInt` over masked discriminants), and `Variants::Multiple { TagEncoding::Niche }` (`[MaybeUninit<u8>; N]` subslice offset extraction when `discr.size < op_size`, followed by `WrappingRange` modular subtraction). It deliberately skips `Variants::Single` (e.g., `enum SingleWrapBool { Only(bool) }`), `ty::Bool`, and pointer dereference reads (`*(ptr as *const DirectEnum)`), all three of which pass `-Z ub-checks=yes` silently while Miri rejects them as Undefined Behavior.

2. **LTO CFI (`@llvm.type.test` / `LowerTypeTests`) vs. KCFI Arity (`-Z sanitizer-kcfi-arity`):**
   - Under `-Z sanitizer=cfi`, `rustc` attaches a 4-point lattice of Itanium C++ ABI `!type` metadata identifiers to every function declaration—the powerset of `{GENERALIZE_POINTERS, NORMALIZE_INTEGERS}` (`raw`, `.normalized`, `.generalized`, `.normalized.generalized`, plus `USE_CONCRETE_SELF` for monomorphized instances)—and emits `@llvm.type.test(ptr %f, metadata !"...")` before indirect calls. During LTO, LLVM's `LowerTypeTests` replaces `@llvm.type.test` with a canonical 8-byte-stride jump-table membership check: a single `icmp eq ptr %f, @.cfi.jumptable.1` for singleton equivalence classes versus a rotate-right-by-3 range test (`@llvm.fshl.i64(diff, diff, 61) < n`) for multi-slot classes. Enabling `-Z sanitizer-cfi-generalize-pointers=yes` erases pointee types to `PKv` (`*const ()`), collapsing `fn(*const i32) -> i32` and `fn(*const u8) -> i32` into the same 2-slot jump table and empirically permitting cross-pointee indirect-call type confusion (`rc = 0`) while still preserving non-ZST parameter arity (`arity_mismatch` traps with `SIGILL`, `rc = -4`).
   - Under `-Z sanitizer=kcfi` (which mandates `-C panic=abort`), each function receives a single 32-bit `!kcfi_type` tag (lower 32 bits of `xxHash64` over the CFI type string) and indirect calls carry `[ "kcfi"(i32 <hash>) ]` operand bundles without requiring LTO or jump tables. Adding `-Z sanitizer-kcfi-arity=yes` emits module flag `!"kcfi-arity", i32 1`, shifting the x86-64 `__cfi_<fn>` preamble register from a constant `%eax` for all functions to an arity-encoded register (`0 -> %eax`, `1 -> %ecx`, `2 -> %edx`, `3 -> %ebx`).

3. **Sanitizer IR/Runtime Matrix, `#[sanitize(...)]`, and `SanitizerIgnoreList` Blame Algebra:**
   - LLVM sanitizer instrumentation passes (`AddressSanitizerPass`, `ThreadSanitizerPass`, `MemorySanitizerPass`, etc.) run only in the pre-link optimization pipeline (`!is_lto`) via `OptimizerLastEPCallbacks`, while `-Z sanitizer=leak` (LSan) injects zero IR instrumentation and links only `librustc-nightly_rt.lsan.a` (unless ASan or HWASan is also active). Crate-level ABI mismatch checking rejects mixing uninstrumented `std` with `-Z sanitizer={thread,memory,cfi,kcfi}` unless `-Z build-std` or `-C unsafe-allow-abi-mismatch=sanitizer` is supplied, whereas `address` and `leak` link without that override.
   - `SanitizerIgnoreList` (added in `rust-lang/rust@c0e55d66c` on `2026-09-03`, present at `342d74463` and absent at `14210df0e`) resolves per-function sanitizer suppression via lexicographic `(file_idx, line_no)` blame pairs: `is_blame_ignored(no_san, san) = no_san.is_some() && (san.is_none() || no_san > san)`, taking the componentwise maximum across four query axes (`fun` mangled, `fun` demangled, `src`, `mainfile`). Because `sanitize_attrs` computes `enabled = tcx.sess.sanitizers() - sanitizer_fn_attr.disabled` *before* calling `filter_instance_sanitizers`, `#[sanitize(s = "off")]` strictly dominates any ignorelist `=sanitize` re-enable rule. A documented `FIXME` in `filter_instance_sanitizers` leaves `SAFESTACK`, `SHADOWCALLSTACK`, `MEMTAG`, and `REALTIME` unfiltered by ignorelists.

4. **Anneal Trusted-Boundary Implications & Mechanized Lean 4 Proof:**
   - In `joshlf/anneal@c131b320e`, `Trusted.MirAst.AssertKind` models `.misalignedPtrDeref` and `.nullPtrDeref` but folds `NullReferenceConstructed` and `InvalidEnumConstruction` into `.unsupported`, and `Trusted.MirSemantics.evalTerminator` faults closed (`.fault .unsupported`) on all `.assert` terminators. Capturing MIR at `Runtime(PostCleanup)` avoids these injected asserts cleanly; verifying post-UB-check `optimized_mir` requires extending both `AssertKind` and `evalTerminator`.
   - `support/SanitizerUbChecksAndCfiSoundness.lean` (1,185 lines, Lean `v4.34.1`, zero warnings under `-DwarningAsError=true`, axioms strictly within `[propext, Quot.sound]`, zero `Classical.choice` or external decision-procedure axioms) mechanizes all three main soundness/algebra theorems and three constructive counterexamples (`ce1`, `ce2`, `ce3`).

## Applicability

### Subjects and Relationships

This report combines four pinned, independently resolvable upstream subjects:

| Subject | Repository & Immutable Revision | Role in Report |
| :--- | :--- | :--- |
| Upstream `rustc` source | `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | Primary-source audit of MIR UB-check passes (`PassPolicy::optional`), `AssertKind::NullReferenceConstructed`, LTO CFI / KCFI lowering, LLVM sanitizer pass registration, and `SanitizerIgnoreList` (introduced in `c0e55d66cca54bd3ad8b78e152d8d07fc976da0a`). |
| Executed `rustc` + `Miri` toolchain | `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`, `LLVM 22.1.6`, `miri 0.1.0 (14210df0e2 2026-05-31)`) | Direct local execution of all empirical probes (`support/probe_sanitizers_cfi_ub_checks.py` -> `support/probe_results.json`) on `x86_64-unknown-linux-gnu`, plus direct source diffing against `342d74463`. |
| Anneal trusted MIR boundary | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Primary-source audit of `Trusted.MirAst.AssertKind` and `Trusted.MirSemantics.evalTerminator` to determine how `rustc` UB-check injection interacts with MIR capture. |
| Lean 4 proof kernel | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Direct kernel verification of `support/SanitizerUbChecksAndCfiSoundness.lean` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`. |

### Cross-Revision Comparison (`14210df0e` vs. `342d74463`)

Because empirical execution ran on `14210df0e` (`1.98.0-nightly`) while upstream source auditing also covered `342d74463`, every behavior difference between the two revisions was checked by direct `diff -u` of the compiler sources (`source` + `execution`):

| Mechanism | `rust-lang/rust@14210df0e` (`1.98.0-nightly`, executed) | `rust-lang/rust@342d74463` (upstream audited) | Semantic Impact |
| :--- | :--- | :--- | :--- |
| MIR UB-check pass policy (`CheckAlignment`, `CheckNull`, `CheckEnums`) | `is_enabled(sess) = sess.ub_checks()` and `is_required() = true` (cannot be overridden with `-Z mir-enable-passes`) | `policy(ctx) = PassPolicy::optional(ctx.ub_checks())` (`pass_manager.rs:88-107, 256-285`) | Default behavior identical at all `-O` levels (`-O0`..`-O3`) since none is wrapped in `WithMinOptLevel`; `342d74463` additionally allows explicit `-Z mir-enable-passes=-CheckNull` overrides. |
| `CheckNull` failure `AssertKind` on borrows (`&*null`, `&(*null).tail`) | Emits `AssertKind::NullPointerDereference` unconditionally on borrows -> runtime message `"null pointer dereference occurred"` | Splits into `AssertKind::NullReferenceConstructed` on `SharedBorrow`/`Borrow` -> runtime message `"null reference produced"`, vs. `AssertKind::NullPointerDereference` on non-borrow derefs | Same abort/allow predicate on every input; only the diagnostic `AssertKind` and panicking lang item (`panic_null_reference_constructed`) changed. |
| `CheckAlignment` & `CheckEnums` predicates | Identical `excluded_pointees = [bool, i8, u8]`, `FollowProjections`, `max_reliable_alignment()`, `Uninhabited`/`Direct`/`WithNiche` visitor and `[MaybeUninit<u8>; N]` subslice extraction | Identical predicates and visitor; refactored `BasicBlockData` split helper only | Identical runtime and MIR-assertion semantics across both revisions. |
| LTO CFI 4-ID lattice, `LowerTypeTests`, KCFI, and `-Z sanitizer-kcfi-arity` | Present and empirically executed (`LLVM 22.1.6`); `declare.rs`, `cfi/typeid/mod.rs`, `kcfi/typeid/mod.rs` identical except `InstanceKind::ReifyShim` moved to `InstanceKind::Shim(ShimKind::Reify(..))` | Present with identical `!type` lattice, `!kcfi_type` xxHash64-low32 encoding, and `!"kcfi-arity", i32 1` module flag | Identical IR, assembly preamble, and runtime behavior on `x86_64-unknown-linux-gnu`. |
| `#[sanitize(address = "off")]` | Present (`#![feature(sanitize)]`) and empirically executed (`attributes.rs:110-122`) | Present (`attributes.rs:150-170`) and composed ahead of `SanitizerIgnoreList` | Identical attribute semantics when no ignorelist is supplied. |
| `-Z sanitizer-ignorelist` & `compiler/rustc_sanitizers/src/ignorelist/` | **Absent / unsupported** (`error: unknown unstable option: sanitizer-ignorelist`) | **Present** (landed in `c0e55d66cca54bd3ad8b78e152d8d07fc976da0a`, `2026-09-03`) | Blame resolution and `filter_instance_sanitizers` findings for `342d74463` are established by `source` + `derived` Lean proof, not live execution on `14210df0e`. |

### Configuration and Target Constraints

- All empirical compilation, IR/MIR/assembly extraction, and native execution ran on `x86_64-unknown-linux-gnu`.
- Standalone single-file compilation against precompiled sysroot `std` requires `-C unsafe-allow-abi-mismatch=sanitizer` for `-Z sanitizer={cfi,kcfi,thread,memory}` (whereas `address` and `leak` do not trigger the ABI mismatch gate), and `-Z sanitizer=kcfi` additionally mandates `-C panic=abort`.
- Live ASan execution used `ASAN_OPTIONS=detect_leaks=0:abort_on_error=0` to isolate heap-buffer-overflow reporting from leak-detector `ptrace` attachment restrictions, and live TSan execution used `TSAN_OPTIONS=halt_on_error=0:exitcode=66`.
- Live Miri execution used `MIRIFLAGS=-Zmiri-disable-isolation` via `cargo miri run` on a minimal Cargo crate containing the exact 13-case probe source.

## Findings

### 1. MIR Runtime UB-Check Passes (`check_pointers`, `CheckAlignment`, `CheckNull`, `CheckEnums`)

#### 1.1 Pipeline Placement, Gating, and Non-Unwinding Panic Contract

Basis: `source` + `execution`

In `rust-lang/rust@342d74463`, `run_runtime_cleanup_passes` (`compiler/rustc_mir_transform/src/lib.rs:684-698`) finishes by advancing the MIR body to `MirPhase::Runtime(RuntimePhase::PostCleanup)` (`lib.rs:691`). Immediately afterward, `run_optimization_passes` (`lib.rs:700-765`) schedules the three UB-check passes as its **very first three passes** before any inlining, ZST removal, unreachable-enum pruning, or constant propagation:

```rust
// compiler/rustc_mir_transform/src/lib.rs:706-714 (342d74463)
pm::run_passes(
    tcx,
    body,
    &[
        // Add some UB checks before any UB gets optimized away.
        &check_alignment::CheckAlignment,
        &check_null::CheckNull,
        &check_enums::CheckEnums,
        ...
```

Because `miri` interprets pre-optimization MIR (`mir_drops_elaborated_and_const_checked` / `mir_for_ctfe`), Miri executes bodies **before** `CheckAlignment`, `CheckNull`, and `CheckEnums` run and instead enforces its own full machine-level validity checks.

Every pass is gated by two conditions:
1. **Flag / Policy Gating:** `Session::ub_checks` (`compiler/rustc_session/src/session.rs:1095-1097`) returns `self.opts.unstable_opts.ub_checks.unwrap_or(self.opts.debug_assertions)`. In `342d74463`, each of `CheckAlignment`, `CheckNull`, and `CheckEnums` returns `PassPolicy::optional(ctx.ub_checks())` (`pass_manager.rs:88-107, 167-173`), which is **not** wrapped in `WithMinOptLevel` so the passes run identically at `-C opt-level=0` and `-C opt-level=2` unless explicitly toggled via `-Z ub-checks=no` or `-Z mir-enable-passes`. In `14210df0e`, the passes returned `is_enabled(sess) = sess.ub_checks()` and `is_required() = true`.
2. **`LangItem::PanicImpl` Bail-Out:** Both `check_pointers` (`compiler/rustc_mir_transform/src/check_pointers.rs:62-64`) and `CheckEnums::run_pass` (`compiler/rustc_mir_transform/src/check_enums.rs:27-29`) immediately return without modifying the body if `tcx.lang_items().get(LangItem::PanicImpl).is_none()`. This prevents `#![no_std]` library crates compiled without a panic handler from failing to link due to compiler-injected panic calls.

Both `check_pointers` (`check_pointers.rs:74-144`) and `CheckEnums` (`check_enums.rs:39-110`) iterate blocks and statement indices **in reverse** (`indices().rev()`, `(0..len).rev()`), splitting the current basic block at `location.statement_index` so that inserted blocks only affect already-visited locations. Every inserted `TerminatorKind::Assert` sets `unwind: UnwindAction::Unreachable` (`check_pointers.rs:117`, `check_enums.rs:370, 461, 538`). In `compiler/rustc_codegen_ssa/src/mir/block.rs:815-831`, the four UB-check `AssertKind` variants lower to four `#[rustc_nounwind]` lang items in `library/core/src/panicking.rs:277-334`:

| `AssertKind` Variant (`rustc_middle/src/mir/syntax.rs:1052-1055`) | Lowered Lang Item (`core::panicking`) | Unwind Behavior | Runtime Message |
| :--- | :--- | :--- | :--- |
| `MisalignedPointerDereference { required, found }` | `panic_misaligned_pointer_dereference` | `#[rustc_nounwind]` -> abort (`SIGABRT`, `rc = -6`) | `"misaligned pointer dereference: address must be a multiple of ..."` |
| `NullPointerDereference` | `panic_null_pointer_dereference` | `#[rustc_nounwind]` -> abort (`SIGABRT`, `rc = -6`) | `"null pointer dereference occurred"` |
| `NullReferenceConstructed` (added post-`14210df0e`, present at `342d74463`) | `panic_null_reference_constructed` | `#[rustc_nounwind]` -> abort (`SIGABRT`, `rc = -6`) | `"null reference produced"` |
| `InvalidEnumConstruction(source)` | `panic_invalid_enum_construction` | `#[rustc_nounwind]` -> abort (`SIGABRT`, `rc = -6`) | `"trying to construct an enum from an invalid value 0x..."` |

The `#[rustc_nounwind]` contract is load-bearing for soundness: as documented in `check_pointers.rs:113-117`, allowing an injected UB check to unwind into unsafe code could violate panic-safety invariants and trigger worse UB during stack unwinding.

#### 1.2 `check_pointers` Visitor Scope and the `CheckAlignment` vs. `CheckNull` Asymmetry

Basis: `source` + `execution`

`PointerFinder` (`compiler/rustc_mir_transform/src/check_pointers.rs:182-250`) filters MIR place uses through five sequential gates:
1. **Context filter (`should_visit_place`, lines 182-198):** Visits `MutatingUse(Store | Call | Yield | Drop | Borrow)` and `NonMutatingUse(Copy | Move | SharedBorrow)`. Raw address-of (`&raw const (*p).f` -> `RawBorrow`) and `PlaceMention` are *not* visited.
2. **Indirect raw-pointer filter (lines 203-215):** Requires `place.is_indirect()` and that the base local `Place::from(place.local)` has type `ty::RawPtr(pointee_ty, _)`. Dereferences of safe references (`&T`/`&mut T`) or `Box<T>` are not checked.
3. **Field-projection type selection (lines 219-228):** If `field_projection_mode` is `BorrowedFieldProjectionMode::FollowProjections` **and** the context is `SharedBorrow` or `Borrow`, `pointee_ty` is replaced by `place.ty(self.local_decls, self.tcx).ty` (the projected field's type); under `NoFollowProjections`, `pointee_ty` stays the base pointer's pointee type. Notice that in *both* modes, the checked pointer operand passed to `on_finding` is always `pointer = Place::from(place.local)` (the base pointer local, line 208).
4. **Sizedness gate (lines 231-234):** Unsized pointees (`!pointee_ty.is_sized(tcx, typing_env)`) are skipped completely.
5. **Excluded element type filter (lines 237-245):** Unwraps `ty::Array(elem, _)` to `elem` and skips any type in `excluded_pointees`.

`CheckAlignment` and `CheckNull` instantiate `check_pointers` with deliberately asymmetric parameters:

- **`CheckAlignment` (`compiler/rustc_mir_transform/src/check_alignment.rs:20-148`):**
  - `excluded_pointees = [tcx.types.bool, tcx.types.i8, tcx.types.u8]` (line 22). **Subtle empirical finding:** `tcx.types.unit` (`()`) and 1-byte `#[repr(u8)]` enums are *not* in `excluded_pointees`! Consequently, MIR dumps at `-O0 -Z ub-checks=yes` confirm that `CheckAlignment` emits 1 alignment `Assert` in `deref_zst_null`, `borrow_zst_null`, and `ptr_read_direct_enum` (`align_of::<()>() = 1`, `mask = 1 - 1 = 0`, `addr & 0 == 0`), which LLVM `-O2` folds away completely (reducing `deref_zst_null` from 27 IR lines / 2 panic calls at `-O0` to 4 IR lines / 0 calls at `-O2`).
  - `BorrowedFieldProjectionMode::FollowProjections` (line 32): For `&(*p).tail` where `p: *const AlignedStruct` (align 4) is offset by `+1` byte and `.tail: u8` (align 1) is at offset `+4`, `pointee_ty` becomes `u8`, which is excluded by `excluded_pointees`. `CheckAlignment` inserts **0 asserts** in `borrow_field_u8`, avoiding a false positive on code that Miri confirms is well-defined (`BYTE=85`, `rc = 0`).
  - **Target alignment clamping (lines 86-108):** Computes `alignment_mask = align_of::<T>() - 1`, and whenever `tcx.sess.target.max_reliable_alignment() < Align::MAX`, bitwise-ANDs `alignment_mask` with `max_align.bytes() - 1` so targets that cannot reliably enforce over-aligned allocations never trigger false-positive alignment aborts. Finally checks `(addr & alignment_mask) == 0`.
  - **Implicit layout precondition for `FollowProjections` (`derived`):** Because `CheckAlignment` checks `baseAddr & (fieldAlign - 1) == 0` using `Place::from(place.local)` rather than the projected address `(baseAddr + fieldOffset)`, checking `baseAddr` against `fieldAlign` agrees with `(baseAddr + fieldOffset) % fieldAlign == 0` if and only if `fieldAlign ∣ fieldOffset` (which holds for all non-packed Rust structs; unaligned borrows of `#[repr(packed)]` fields are rejected separately by safe/unsafe packed-reference rules).

- **`CheckNull` (`compiler/rustc_mir_transform/src/check_null.rs:18-128`):**
  - `excluded_pointees = []` (line 22) and `BorrowedFieldProjectionMode::NoFollowProjections` (line 24).
  - **Why `NoFollowProjections` is essential:** For `&(*null::<AlignedStruct>()).tail`, the projected field address would be `0x0 + 0x4 = 0x4` (non-null!). Indeed, at `-Z ub-checks=no`, `borrow_u8_null_struct` prints `PTR=0x4` and exits `0`. Because `CheckNull` uses `NoFollowProjections` and tests `Place::from(place.local)` (`0x0`), it catches the null base pointer before the `+4` field offset is applied (`rc = -6`), agreeing with Miri (`attempting to offset pointer by 4 bytes, but got null pointer`).
  - **Borrow vs. Dereference ZST asymmetry (lines 55-123):**
    - For `SharedBorrow` or `Borrow`, `pointee_should_be_checked = true` unconditionally and (at `342d74463`) `assert_kind = AssertKind::NullReferenceConstructed` (at `14210df0e`, `AssertKind::NullPointerDereference`). Thus `&*null::<()>()` aborts (`rc = -6`), matching Miri (`encountered a null reference`).
    - For all other visited contexts (`Copy`, `Move`, `Store`, `Call`, `Yield`, `Drop`), `pointee_should_be_checked = (size_of::<pointee_ty>() != 0)` and `assert_kind = AssertKind::NullPointerDereference`. The final condition is `!(is_null & pointee_should_be_checked)`. Thus `*null::<()>()` succeeds (`ZST_DEREF_OK`, `rc = 0`), matching Miri (`rc = 0`), and at `-O2` LLVM completely deletes the null check from `deref_zst_null`.

#### 1.3 `CheckEnums` Visitor Scope, Multi-Byte Niche Extraction, and Deliberate Incompleteness

Basis: `source` + `execution`

`EnumFinder::visit_rvalue` (`compiler/rustc_mir_transform/src/check_enums.rs:166-238`) matches **only** `Rvalue::Cast(CastKind::Transmute, op, ty)` where `ty.kind()` is `ty::Adt(adt_def, _)` with `adt_def.is_enum()`. It dispatches on `enum_layout.variants`:

1. **`Variants::Empty` (lines 187-194):** If `op_layout.is_uninhabited()`, returns without inserting a check (avoiding spurious instrumentation in unreachable code). Otherwise emits `EnumCheckType::Uninhabited` -> unconditional `Assert { cond: false, msg: InvalidEnumConstruction(0) }` (lines 421-464).
2. **`Variants::Single { .. }` (line 196):** Explicitly does nothing (`{}`), commenting *"Construction of Single value enums is always fine."* This is false whenever the single variant wraps a type with invalid bit patterns (e.g., `enum SingleWrapBool { Only(bool) }`), because `CheckEnums` inspects only the outer enum discriminant, not field validity.
3. **`Variants::Multiple { tag_encoding: TagEncoding::Direct, tag: Scalar::Initialized { value, .. }, .. }` (lines 198-214):** Collects `adt_def.discriminants(tcx)`, casts the source operand to `u128` via `insert_discr_cast_to_u128`, masks with `discr.size.unsigned_int_max()`, and branches with `TerminatorKind::SwitchInt` to `new_block` for every valid truncated discriminant and to `invalid_discr_block` (`Assert { cond: false, msg: InvalidEnumConstruction(discr_masked) }`) otherwise (lines 338-419).
4. **`Variants::Multiple { tag_encoding: TagEncoding::Niche { .. }, tag: Scalar::Initialized { value, valid_range, .. }, tag_field, .. }` (lines 216-231):** Extracts the tag at byte offset `offset = enum_layout.fields.offset(tag_field.as_usize())`. Whenever `discr.size.bytes() < op_size.bytes()` (`insert_discr_cast_to_u128`, lines 278-303), `CheckEnums` transmutes the source operand to `[MaybeUninit<u8>; op_size]`, projects a `ProjectionElem::Subslice { from: offset, to: offset + discr.size, from_end: false }` (using `MaybeUninit<u8>` so uninitialized padding bytes in the surrounding aggregate do not trigger UB during extraction!), and transmutes the subslice to the tag integer type before widening to `u128`. It then verifies `WrappingRange` membership via `(discr - valid_range.start) <= valid_range.end.wrapping_sub(valid_range.start)` (lines 489-540). Our live MIR dump of `transmute_multibyte_niche` (`[u8; 8] -> Option<(u32, bool)>`) directly confirmed `has_maybe_uninit_subslice = true` and a single `CheckEnums` assert lowering to `panic_invalid_enum_construction`.
5. **Deliberate non-covered paths (incompleteness):** Because `EnumFinder` checks only `Rvalue::Cast(CastKind::Transmute, ...)` on multi-variant or empty enums:
   - `transmute::<u8, SingleWrapBool>(2)` emits **0** asserts (`Variants::Single` skipped).
   - `transmute::<u8, bool>(2)` emits **0** asserts (`ty::Bool` is not an `Adt` enum).
   - `*(ptr as *const DirectEnum)` reading byte `2` emits **0** `CheckEnums` asserts (only `CheckAlignment` + `CheckNull` on the pointer), because reading through a raw pointer is `Rvalue::Use(Operand::Copy(*p))`, not `CastKind::Transmute`.

#### 1.4 Library `assert_unsafe_precondition!` and Precompiled `libcore` Interaction

Basis: `source` + `execution`

Standard-library preconditions (`slice::from_raw_parts`, `hint::unreachable_unchecked`) are checked not by MIR passes, but by `core::ub_checks::assert_unsafe_precondition!` (`library/core/src/ub_checks.rs:58-87`), which expands to `if ::core::ub_checks::$kind() { precondition_check(args); }` where `precondition_check` carries `#[rustc_no_mir_inline]`, `#[inline]`, `#[rustc_nounwind]`, and `#[track_caller]`. For language UB (`check_language_ub`, lines 96-108), `const_eval_select!` returns `false` in `const` evaluation and `!cfg!(miri) && intrinsics::ub_checks()` at runtime so Miri reports its native UB diagnostics instead of a library panic.

**Empirical `-O0` nuance observed on `rustc 1.98.0-nightly (14210df0e)`:** In `probe_1_ub_checks`, `call_unreachable_unchecked` (`unreachable_bad`) still aborted (`rc = -6`, `"unsafe precondition(s) violated: hint::unreachable_unchecked must never be reached"`) under `-C opt-level=0 -Z ub-checks=no`, whereas `slice_null_bad` returned `SLICE_LEN=0` (`rc = 0`) and at `-C opt-level=2 -Z ub-checks=no` `call_unreachable_unchecked` lowered to bare `unreachable` (4 IR lines, 0 calls). In `ub_no_O0`, `call_unreachable_unchecked` retained 22 IR lines calling `panic_cannot_unwind` because at `-O0` the `intrinsics::ub_checks()` guard branch inside the non-inlined `unreachable_unchecked` precondition path was not folded before lowering, whereas `make_slice_raw` evaluated the `false` branch dynamically and skipped the check.

#### 1.5 Complete 13-Case Empirical Matrix (`rustc 1.98.0-nightly` @ `14210df0e` + `Miri`)

Basis: `execution` (`support/probe_results.json`)

| Case | Function | MIR Asserts (`ub=yes -O0`: Align / +Null / +Enum) | `ub=yes -O0` | `ub=yes -O2` | `ub=no -O0` | `ub=no -O2` | Live `Miri` Oracle | Classification |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: | :--- |
| `misaligned_u32` | `deref_read_u32` | 1 / 2 / 2 | `-6` (misaligned) | `-6` (misaligned) | `0` (`VAL=119`) | `0` (`VAL=119`) | **UB** (`align 1, req 4`) | Caught by `CheckAlignment` |
| `borrow_u8_misaligned_struct` | `borrow_field_u8` | 0 / 1 / 1 | `0` (`BYTE=85`) | `0` (`BYTE=85`) | `0` (`BYTE=85`) | `0` (`BYTE=85`) | **OK** (`BYTE=85`) | No false positive (`FollowProjections` + `u8` excluded) |
| `borrow_u8_null_struct` | `borrow_field_u8` | 0 / 1 / 1 | `-6` (null) | `-6` (null) | `0` (`PTR=0x4`) | `0` (`PTR=0x4`) | **UB** (null +4 offset) | Caught by `CheckNull` (`NoFollowProjections`) |
| `deref_zst_null` | `deref_zst_null` | 1 / 2 / 2 | `0` (`ZST_DEREF_OK`) | `0` (`ZST_DEREF_OK`) | `0` (`ZST_DEREF_OK`) | `0` (`ZST_DEREF_OK`) | **OK** (`ZST_DEREF_OK`) | No false positive (`size_of == 0` guard) |
| `borrow_zst_null` | `borrow_zst_null` | 1 / 2 / 2 | `-6` (null) | `-6` (null) | `0` (`ZST_BORROW=0x0`) | `0` (`ZST_BORROW=0x0`) | **UB** (null `&()`) | Caught by `CheckNull` (unconditional on borrow) |
| `direct_enum_bad` | `transmute_direct_enum` | 0 / 0 / 1 | `-6` (`0x2`) | `-6` (`0x2`) | `0` (`ENUM=0`) | `0` (`ENUM=0`) | **UB** (`tag 0x02`) | Caught by `CheckEnums` (`Direct`) |
| `niche_opt_bool_bad` | `transmute_niche_opt_bool` | 0 / 0 / 1 | `-6` (`0x3`) | `-6` (`0x3`) | `0` (`OPT=Some(true)`) | `0` (`OPT=Some(true)`) | **UB** (`tag 0x03`) | Caught by `CheckEnums` (`WithNiche`) |
| `uninhabited_bad` | `transmute_uninhabited` | 0 / 0 / 1 | `-6` (`0x0`) | `-6` (`0x0`) | `-4` (`SIGILL`) | *(skipped: UB)* | **UB** (zero-variant) | Caught by `CheckEnums` (`Uninhabited`) |
| `single_wrap_bool_bad` | `transmute_single_wrap_bool` | 0 / 0 / 0 | **`0`** (`RAW=0`) | **`0`** (`RAW=0`) | `0` (`RAW=0`) | `0` (`RAW=0`) | **UB** (`bool 0x02`) | **Missed** (`Variants::Single` skipped) |
| `raw_bool_bad` | `transmute_raw_bool` | 0 / 0 / 0 | **`0`** (`RAW_BOOL=0`) | **`0`** (`RAW_BOOL=0`) | `0` (`RAW_BOOL=0`) | `0` (`RAW_BOOL=0`) | **UB** (`bool 0x02`) | **Missed** (`ty::Bool` not enum ADT) |
| `ptr_read_enum_bad` | `ptr_read_direct_enum` | 1 / 2 / 2 | **`0`** (`ENUM=0`) | **`0`** (`ENUM=2`) | `0` (`ENUM=0`) | `0` (`ENUM=2`) | **UB** (`tag 0x02`) | **Missed** (`*ptr` not `Transmute`) |
| `slice_null_bad` | `make_slice_raw` | 0 / 0 / 0 | `-6` (precond) | `-6` (precond) | `0` (`LEN=0`) | `0` (`LEN=0`) | **UB** (null `&[u8]`) | Caught by `core` `assert_unsafe_precondition!` |
| `unreachable_bad` | `call_unreachable_unchecked` | 0 / 0 / 0 | `-6` (precond) | `-6` (precond) | `-6` (precond) | *(skipped: UB)* | **UB** (unreachable) | Caught by `core` `assert_unsafe_precondition!` |

*(In addition, `transmute_multibyte_niche` emitted `0 / 0 / 1` MIR asserts with `has_maybe_uninit_subslice = true` and called `panic_invalid_enum_construction` in LLVM IR at both `-O0` and `-O2` under `-Z ub-checks=yes`, and `0` asserts / `0` panic calls under `-Z ub-checks=no`.)*

---

### 2. LTO CFI (`@llvm.type.test` / `LowerTypeTests`) vs. KCFI Arity (`-Z sanitizer-kcfi-arity`)

#### 2.1 The 4-Point LTO CFI `!type` Metadata Lattice

Basis: `source` + `execution`

When `-Z sanitizer=cfi` is enabled, `CodegenCx::declare_fn` (`compiler/rustc_codegen_llvm/src/declare.rs:198-228`) attaches every unique type metadata identifier generated by iterating over the powerset of `TypeIdOptions`:
- For bare `FnAbi` declarations (`declare.rs:216-226`): powerset of `{GENERALIZE_POINTERS, NORMALIZE_INTEGERS}` (`2^2 = 4` lattice points).
- For monomorphized `Instance` definitions (`declare.rs:199-214`): powerset of `{GENERALIZE_POINTERS, NORMALIZE_INTEGERS, USE_CONCRETE_SELF}` deduplicated via `FxIndexSet` (which yields 4 distinct `!type` attachments for ordinary free functions and up to 8 when `Self` erasure for vtable-callable trait methods differs from concrete `Self`).

Each identifier is constructed by `itanium_cxx_abi::typeid_for_fnabi` (`compiler/rustc_sanitizers/src/cfi/typeid/itanium_cxx_abi/mod.rs:25-106`):
1. Prefixes `_ZTSF`, encodes the transformed return type, encodes every argument with `arg.mode != PassMode::Ignore` (erasing zero-sized ignored arguments, line 71; emitting `v` if none remain, line 79), and closes with `E`.
2. Applies `TransformTy::fold_ty` (`compiler/rustc_sanitizers/src/cfi/typeid/itanium_cxx_abi/transform.rs:50-220`):
   - `NORMALIZE_INTEGERS` (`transform.rs:76-115`): maps `bool -> u8`, `char -> u32`, and `isize`/`usize` to fixed-width integers matching C ABI width (`i64`/`u64` on 64-bit targets).
   - `GENERALIZE_POINTERS` (`transform.rs:189-219`): replaces `*const T -> *const ()` (`PKv`), `*mut T -> *mut ()` (`Pv`), `&T -> &'static ()`, `&mut T -> &'static mut ()`, and `fn(...) -> *const ()` (`PKv`), short-circuiting recursion on the erased pointee.
3. Appends deterministic mode suffixes in fixed order (`itanium_cxx_abi/mod.rs:97-103`): `.normalized` if `NORMALIZE_INTEGERS`, then `.generalized` if `GENERALIZE_POINTERS`.

Direct pre-LTO IR inspection (`lto_cfi_pre_lto_lib`, `--crate-type=lib -C linker-plugin-lto -Z sanitizer=cfi`) confirmed this exact 4-ID lattice on `target_i32_ptr` and `target_u8_ptr`:
- `target_i32_ptr` carries `!type !18 !type !19 !type !20 !type !21` (`_ZTSFu3i32PKS_E`, `_ZTSFu3i32PKvE.generalized`, `_ZTSFu3i32PKS_E.normalized`, `_ZTSFu3i32PKvE.normalized.generalized`).
- `target_u8_ptr` carries `!type !31 !type !19 !type !32 !type !21` (`_ZTSFu3i32PKu2u8E`, `_ZTSFu3i32PKvE.generalized`, `_ZTSFu3i32PKu2u8E.normalized`, `_ZTSFu3i32PKvE.normalized.generalized`).
- Crucially, `!19` and `!21` are literally identical metadata nodes shared by both functions, whereas `!18`/`!31` and `!20`/`!32` remain disjoint.

#### 2.2 `@llvm.type.test` Insertion and `LowerTypeTests` Jump-Table Lowering

Basis: `source` + `execution`

At every indirect call (`LLVMRustIsNonGVFunctionPointerTy(llfn)`), `Builder::cfi_type_test` (`compiler/rustc_codegen_llvm/src/builder.rs:1969-2102`) checks whether CFI is disabled on the caller (via `#[sanitize(cfi = "off")]` or `"no-sanitize-cfi"` from an ignorelist) or on the callee signature type (`is_sanitizer_type_ignored(c"cfi", fn_abi)`). Otherwise it computes the single call-site type ID for the active session options (`GENERALIZE_POINTERS`, `NORMALIZE_INTEGERS`), emits:

```llvm
%0 = tail call i1 @llvm.type.test(ptr nonnull %f, metadata !"_ZTSFu3i32PKS_E")
br i1 %0, label %type_test.pass, label %type_test.fail

type_test.pass:
  %_0 = tail call noundef i32 %f(ptr noundef %p) #5
  ret i32 %_0

type_test.fail:
  tail call void @llvm.trap()
  unreachable
```

(When `-Z sanitizer-cfi-diag` or `-Z sanitizer-cfi-recover` is set, `type_test.fail` calls `__ubsan_handle_cfi_check_fail*` instead of `abort_immediate()`, `builder.rs:2024-2095`.)

In `compiler/rustc_codegen_llvm/src/context.rs:292-322`, `rustc` also attaches module flags `"EnableSplitLTOUnit" = 1` (whenever CFI or split-LTO is enabled), `"CFI Canonical Jump Tables" = 1` (default yes, disabled by `-Z sanitizer-cfi-canonical-jump-tables=no`), and `"cfi-normalize-integers" = 1` (when integer normalization is enabled). During full LTO (`!IsLinkerPluginLTO`, `PassWrapper.cpp:843-851`), `LowerTypeTestsPass` lowers `@llvm.type.test` into jump tables (8-byte stride on x86-64) and concrete address checks:

- **Default CFI (`lto_cfi_default`, singleton class for `_ZTSFu3i32PKS_E`):** Only `target_i32_ptr` belongs to the equivalence class (`target_i32_ptr = .L.cfi.jumptable.1`). `LowerTypeTests` collapses the membership test to an exact pointer equality check and devirtualizes the call target:
  ```llvm
  %0 = icmp eq ptr %f, @.cfi.jumptable.1
  br i1 %0, label %type_test.pass, label %type_test.fail
  type_test.pass:
    %_0 = tail call noundef i32 @.cfi.jumptable.1(ptr noundef %p) #64
    ret i32 %_0
  ```
- **Generalized Pointers (`lto_cfi_generalize_ptrs`, 2-slot class for `_ZTSFu3i32PKvE.generalized`):** Both `target_i32_ptr = .L.cfi.jumptable.1` (slot 0) and `target_u8_ptr = .L.cfi.jumptable.1+8` (slot 1) inhabit the jump table. `LowerTypeTests` lowers the check to an 8-byte-stride rotate-right-by-3 (`fshl` by 61) range test:
  ```llvm
  %0 = ptrtoint ptr %f to i64
  %1 = sub i64 ptrtoint (ptr getelementptr (i8, ptr @.cfi.jumptable.1, i64 8) to i64), %0
  %2 = tail call i64 @llvm.fshl.i64(i64 %1, i64 %1, i64 61)
  %3 = icmp ult i64 %2, 2
  br i1 %3, label %type_test.pass, label %type_test.fail
  ```
  Mathematically, for `d = (base - f) mod 2^64` (or `(f - jtBase) mod 2^64`), `ror3_64(d) = (d / 8) + (d % 8) * 2^61 < n` holds for `n <= 2^61` if and only if `d % 8 == 0` (rejecting misaligned mid-slot jumps into jump-table bytes) and `d / 8 < n` (bounds checking the slot index).

#### 2.3 KCFI Single-ID Encoding and `-Z sanitizer-kcfi-arity=yes` Register Assignment

Basis: `source` + `execution`

Unlike LTO CFI, KCFI (`-Z sanitizer=kcfi`) operates without LTO or jump tables, requires `-C panic=abort`, and is subject to LLVM's constraint that each function carries **at most one** `!kcfi_type` metadata node (`compiler/rustc_codegen_llvm/src/declare.rs:230-246`, `compiler/rustc_sanitizers/src/kcfi/typeid/mod.rs:34-57`):
- `kcfi::typeid_for_fnabi` / `kcfi::typeid_for_instance` hashes the single selected Itanium C++ ABI type string with `XxHash64` and truncates to the lower 32 bits (`hash.finish() as u32`). Because a function can have only one `!kcfi_type`, KCFI inserts reification shims (`ShimKind::Reify(_, Some(ReifyReason::FnPtr))` with `USE_CONCRETE_SELF`) for casts between function items, closures, trait methods, and function pointers.
- At indirect calls, `Builder::kcfi_operand_bundle` (`builder.rs:2105-2149`) attaches `[ "kcfi"(i32 <hash>) ]` directly to the `call`/`invoke`/`callbr` instruction rather than emitting `@llvm.type.test`, and codegen emits `.kcfi_traps` sections alongside inline `ud2` traps.
- In `context.rs:344-369`, `rustc` emits module flag `"kcfi" = 1`, optionally `"kcfi-offset"` when `-Z patchable-function-entry` adds prefix NOPs, and `"kcfi-arity" = 1` when `-Z sanitizer-kcfi-arity=yes` is active.

Empirical x86-64 assembly from `kcfi_default` vs. `kcfi_arity` directly measures the exact preamble transformation immediately preceding each function entry point (`11` padding `nop`s + 5-byte `movl $imm32, %reg` = 16-byte `__cfi_<fn>` preamble):

| Function | Non-ZST Register Arity | 32-bit KCFI Hash (`u32` / signed `i32`) | `kcfi_default` Preamble | `kcfi_arity` Preamble (`!"kcfi-arity", i32 1`) |
| :--- | :---: | :---: | :--- | :--- |
| `target_zero_args()` | 0 | `3525342048` (`0xd2203760`) | `movl $3525342048, %eax` | `movl $3525342048, %eax` |
| `target_i32_ptr(*const i32)` | 1 | `124123658` (`0x0765fa0a`) | `movl $124123658, %eax` | `movl $124123658, %ecx` |
| `target_two_args(i32, i32)` | 2 | `2505940310` (`-1789026986`) | `movl $2505940310, %eax` | `movl $2505940310, %edx` |
| `target_three_args(i32, i32, i32)` | 3 | `1248878270` (`0x4a705ebe`) | `movl $1248878270, %eax` | `movl $1248878270, %ebx` |

Thus `-Z sanitizer-kcfi-arity=yes` encodes the callee's register-parameter arity directly into the x86-64 opcode/ModRM byte of the `__cfi_<fn>` preamble (`0 -> %eax`, `1 -> %ecx`, `2 -> %edx`, `3 -> %ebx`) so kernel hypervisor/trap handlers or FineIBT/hardware callers can recover arity directly from the instruction preceding the entry symbol without altering the 32-bit type hash.

#### 2.4 Complete 6-Mode LTO CFI vs. KCFI Empirical Matrix

Basis: `execution` (`support/probe_results.json`, `rustc 1.98.0-nightly`, `LLVM 22.1.6`)

| Mode | Module Flags (`CanonJT` / `SplitLTO` / `kcfi-arity`) | `@llvm.type.test` Count | `!type` Unique IDs / `!kcfi_type` Refs | Lowered Check in `call_indirect_i32_ptr` | Runtime `valid` / `valid_two_args` | Runtime `ptr_mismatch` | Runtime `arity_mismatch` |
| :--- | :---: | :---: | :---: | :--- | :---: | :---: | :---: |
| `lto_cfi_pre_lto_lib` | `T / T / F` | `4` | `30` / `0` | `@llvm.type.test(ptr %f, !"_ZTSFu3i32PKS_E")` | *(lib)* | *(lib)* | *(lib)* |
| `lto_cfi_default` | `T / T / F` | `0` *(lowered)* | `48` / `0` | `icmp eq ptr %f, @.cfi.jumptable.1` | `0` (`OK=42`) / `0` (`TWO=42`) | **`-4`** (`SIGILL`) | **`-4`** (`SIGILL`) |
| `lto_cfi_generalize_ptrs` | `T / T / F` | `0` *(lowered)* | `48` / `0` | `@llvm.fshl.i64(diff, diff, 61)` + `icmp ult %2, 2` | `0` (`OK=42`) / `0` (`TWO=42`) | **`0` (`PTR_MISMATCH=27`)** | **`-4`** (`SIGILL`) |
| `lto_cfi_no_canon_jt` | `F / T / F` | `0` *(lowered)* | `48` / `0` | `icmp eq ptr %f, @.cfi.jumptable.1` | `0` (`OK=42`) / `0` (`TWO=42`) | **`-4`** (`SIGILL`) | **`-4`** (`SIGILL`) |
| `kcfi_default` | `F / F / F` | `0` | `0` / `8` | `[ "kcfi"(i32 124123658) ]`, all preambles `%eax` | *(lib)* | *(lib)* | *(lib)* |
| `kcfi_arity` | `F / F / T` | `0` | `0` / `8` | `[ "kcfi"(i32 124123658) ]`, `%eax`/`%ecx`/`%edx`/`%ebx` | *(lib)* | *(lib)* | *(lib)* |

---

### 3. Sanitizer IR/Runtime Matrix, `#[sanitize(...)]`, and `SanitizerIgnoreList` Blame Algebra

#### 3.1 Pass Pipeline, Pre-Link Insertion, and Runtime Library Matrix

Basis: `source` + `execution`

In `compiler/rustc_codegen_llvm/src/back/write.rs:631-645`, `rustc` constructs `llvm::SanitizerOptions` **only when `!is_lto`** (`// Sanitizer instrumentation is only inserted during the pre-link optimization stage.`). Inside `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:882-959`, each enabled sanitizer appends its instrumentation pass to `OptimizerLastEPCallbacks`:
- **ASan (`SanitizeAddress` / `SanitizeKernelAddress`, lines 917-938):** Adds `AddressSanitizerPass` with `UseAfterScope = true`, `AsanDetectStackUseAfterReturnMode::Runtime`, `UseGlobalGC = true`, and `UseOdrIndicator = !isOSWindows()`. Functions receive LLVM attribute `sanitize_address` (`attributes.rs:172-174`). Also disables stack probes (`probestack_attr`, `attributes.rs:374`).
- **TSan (`SanitizeThread`, lines 908-915):** Adds `ModuleThreadSanitizerPass` + function-level `ThreadSanitizerPass`. Functions receive `sanitize_thread` (`attributes.rs:178-180`) and stack probes are disabled (`attributes.rs:374`).
- **MSan (`SanitizeMemory`, lines 895-906):** Adds `MemorySanitizerPass` with `EagerChecks = true` and `SanitizeMemoryTrackOrigins` (from `-Z sanitizer-memory-track-origins={0,1,2}`). Functions receive `sanitize_memory` (`attributes.rs:175-177`). During LTO (`back/lto.rs:61-72`), `rustc` explicitly preserves weak symbols `__msan_keep_going` and `__msan_track_origins`.
- **LSan (`SanitizerSet::LEAK`):** **Zero LLVM IR pass and zero function attribute.** `link.rs:1779-1784` links `librustc-nightly_rt.lsan.a` solely when `LEAK` is enabled and neither `ADDRESS` nor `HWADDRESS` is enabled (since ASan already embeds LSan).

Live compilation and execution on `rustc 1.98.0-nightly (14210df0e)` empirically verified all four entries:

| Sanitizer | Flags Tested | Requires `-C unsafe-allow-abi-mismatch=sanitizer` Against Stock `std`? | Function Attribute in IR | Observed Instrumentation Symbols in IR | Live Runtime Verification |
| :--- | :--- | :---: | :--- | :--- | :--- |
| **ASan** | `-Z sanitizer=address -C opt-level=1` | No | `sanitize_address` | `@__asan_init`, `@__asan_report_{load4,load8,store4,store8}` | In-bounds: `rc = 0` (`VAL=30`); OOB `idx = 8` on 4-elem `Box<[i32; 4]>`: **`rc = 1`**, `ERROR: AddressSanitizer: heap-buffer-overflow` |
| **TSan** | `-Z sanitizer=thread -C opt-level=1` | **Yes** | `sanitize_thread` | Non-atomic `bump_nonatomic`: `@__tsan_func_entry`, `@__tsan_func_exit`, `@__tsan_write4`; Atomic `bump_atomic`: `@__tsan_atomic32_fetch_add`, `@__tsan_func_{entry,exit}` | Atomic path: `rc = 0` (`ATOMIC=0`); 2-thread race on `NONATOMIC_CTR`: **`rc = 66`**, `WARNING: ThreadSanitizer: data race` in `bump_nonatomic` |
| **MSan** | `-Z sanitizer=memory -Z sanitizer-memory-track-origins=2 -C opt-level=1` | **Yes** | `sanitize_memory` | `@__msan_init`, `@__msan_track_origins`, `@__msan_warning_with_origin_noreturn` | *(lib IR verified; full MSan execution requires instrumented `std`/libc)* |
| **LSan** | `-Z sanitizer=leak -C opt-level=1` | No | *(none)* | *(empty: 0 IR sanitizer attributes, 0 `@__asan_init`, 0 `@__lsan_*`)* | Confirms link-time-only runtime (`link.rs:1779-1784`) |

#### 3.2 `#[sanitize(... = "off")]` and `SanitizerIgnoreList` Blame Algebra

Basis: `source` + `execution` (`#[sanitize(address = "off")]` executed on `14210df0e`; `SanitizerIgnoreList` audited in `342d74463`)

Function-level sanitizer suppression combines two mechanisms in `compiler/rustc_codegen_llvm/src/attributes.rs:150-170` (`342d74463`):

```rust
// compiler/rustc_codegen_llvm/src/attributes.rs:158-170 (342d74463)
let mut enabled = tcx.sess.sanitizers() - sanitizer_fn_attr.disabled;
if let Some(ignorelist) = sanitizer_ignorelist {
    if let Some(instance) = instance {
        let result = ignorelist.filter_instance_sanitizers(tcx, instance, enabled);
        enabled = result.enabled;
        if result.ignore_cfi {
            attrs.push(llvm::CreateAttrString(cx.llcx, "no-sanitize-cfi"));
        }
        if result.ignore_kcfi {
            attrs.push(llvm::CreateAttrString(cx.llcx, "no-sanitize-kcfi"));
        }
    }
}
```

On `rustc 1.98.0-nightly (14210df0e)`, `probe_4_sanitize_attr_and_ignorelist` empirically verified the attribute layer: under `-Z sanitizer=address`, `normal_fn` emitted attribute group `#1` containing `sanitize_address` and an `@__asan_report_load4` call, whereas `#[sanitize(address = "off")] attr_off_fn` emitted attribute group `#0` with `has_sanitize_address = false` and `has_asan_report_call = false`. Passing `-Z sanitizer-ignorelist=<file>` on `14210df0e` exited with `rc = 1` (`error: unknown unstable option: sanitizer-ignorelist`), confirming the feature landed later (`c0e55d66cca54bd3ad8b78e152d8d07fc976da0a`, `2026-09-03`).

In `rust-lang/rust@342d74463`, the exact ignorelist blame algebra lives across `compiler/rustc_sanitizers/src/ignorelist/{mod.rs,ffi.rs}` and `compiler/rustc_llvm/llvm-wrapper/RustWrapper.cpp:1786-1941`:

1. **Blame Representation (`ignorelist/ffi.rs:8-27`):** `Blame { file_idx: u32, line_no: u32 }` derives lexicographic `Ord` (`file_idx` primary, `line_no` secondary), with `Blame::NONE = { file_idx: 0, line_no: 0 }`, `is_none() := (line_no == 0)`, and `is_some() := (line_no != 0)`.
2. **Last-Match-Wins Predicate (`ignorelist/mod.rs:8-10`):**
   ```rust
   pub fn is_blame_ignored(no_san: Blame, san: Blame) -> bool {
       no_san.is_some() && (san.is_none() || no_san > san)
   }
   ```
   A function is ignored if and only if at least one plain (disable) rule matches it (`no_san.is_some()`) and either no `=sanitize` rule matches (`san.is_none()`) or the latest matching disable rule strictly follows the latest matching `=sanitize` rule (`no_san > san`). Ties (`no_san == san`) resolve in favor of sanitizing (`false`).
3. **Section Bitmask and Reverse Scan (`RustWrapper.cpp:1786-1898`, `sanitizer_set.rs:11-26`):** `RustSanitizerSpecialCaseList` precomputes a `uint32_t Mask` for each section (`[all]` -> `~0u`, `[address]` -> `1 << 0`, ..., `[realtime]` -> `1 << 13`), matching `SanitizerSet`'s bitflags 1-to-1 (`sanitizer_set.rs:12-25`). `inSectionBlame` iterates sections in **reverse** (`rbegin()` to `rend()`) and calls LLVM's `Section::getLastMatch(Prefix, Query, Category)` twice—first with empty category (`OutNoSan`), then with `"sanitize"` (`OutSan`) (`RustWrapper.cpp:1932-1940`).
4. **Four-Axis Componentwise Maximum (`ignorelist/mod.rs:65-99`):** `instance_blame` evaluates `in_section_blame` across four queries in order:
   - `fun:<mangled symbol_name>`
   - `fun:<demangled def_path_str (no trimmed paths)>`
   - `src:<source filename (prefer_local_unconditionally)>`
   - `mainfile:<local_crate_source_file>` (when non-empty)
   updating `no_san = no_san.max(ns)` and `san = san.max(s)` across all four axes before invoking `is_blame_ignored(no_san, san)`. Consequently, a later `=sanitize` rule on any axis (for instance `fun:*ignorelist_reenabled_fn*=sanitize` on line 4 after `fun:*ignorelist_reenabled_fn*` on line 3 or a `src:` wildcard on line 2) supersedes the earlier disable rule.
5. **Monotonic Attribute Dominance (`attributes.rs:158-170`):** Because `enabled = tcx.sess.sanitizers() - sanitizer_fn_attr.disabled` runs *before* `filter_instance_sanitizers`, and `filter_instance_sanitizers` only ever calls `enabled.remove(...)` (never `enabled.insert(...)`), a function marked `#[sanitize(address = "off")]` **cannot** be re-enabled by a `=sanitize` entry in `-Z sanitizer-ignorelist`.
6. **CFI/KCFI Type-Prefix Ignorelist Queries (`context.rs:874-883`, `builder.rs:1998, 2134`, `ignorelist/mod.rs:180-192`):** In addition to per-caller `"no-sanitize-cfi"` / `"no-sanitize-kcfi"` attributes, CFI and KCFI indirect call sites query `contains_prefix(c"cfi"|c"kcfi", c"type", &typename_for_ignore_list(tcx, fn_abi))`, formatting the callee signature as a safe `fn(...) -> ...` string with no trimmed paths.
7. **Documented Unfiltered-Sanitizer Gap (`ignorelist/mod.rs:151-153`):** Although `section_to_sanitizer_set` (`mod.rs:194-212`) and `RustWrapper.cpp:1868-1894` parse sections for `safestack`, `shadow-call-stack`, `memtag`, and `realtime`, `filter_instance_sanitizers` explicitly omits filtering them:
   ```rust
   // FIXME: Add support for filtering SAFESTACK, SHADOWCALLSTACK, MEMTAG, and REALTIME.
   // Note: For REALTIME, `rustc_codegen_llvm::attributes::sanitize_attrs` will also
   // need to check the filtered `enabled` set rather than `tcx.sess.sanitizers()`.
   ```
   Indeed, `attributes.rs:202` reads `tcx.sess.sanitizers().contains(SanitizerSet::REALTIME)` directly rather than the filtered `enabled` set, confirming both parts of that `FIXME`. Furthermore, `context.rs:694-708` parses the ignorelist files redundantly once per codegen unit (CGU) (`// FIXME: This parses the ignorelist files for each CGU, which adds a performance overhead.`). Note also that `naked` functions skip `sanitize_attrs` entirely (`attributes.rs:568-574`).

---

### 4. Anneal Trusted-Boundary Implications (`joshlf/anneal@c131b320e`)

Basis: `source` + `derived`

Auditing `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` alongside `rustc`'s MIR pipeline exposes three concrete architectural boundaries for verified-MIR capture and semantics:

1. **Exact Capture Seam (`Runtime(PostCleanup)` vs. `optimized_mir`):** Because `CheckAlignment`, `CheckNull`, and `CheckEnums` execute as passes 1–3 of `run_optimization_passes` (`compiler/rustc_mir_transform/src/lib.rs:711-713`) immediately *after* `MirPhase::Runtime(RuntimePhase::PostCleanup)` (`lib.rs:691`), MIR captured at `Runtime(PostCleanup)` is completely invariant to `-Z ub-checks=yes|no` and matches the pre-optimization MIR interpreted by Miri. Conversely, capturing `optimized_mir` with `-Z ub-checks=yes` injects `TerminatorKind::Assert` blocks (and `SwitchInt` + `[MaybeUninit<u8>; N]` subslice transmutations from `CheckEnums`) into every raw-pointer access and enum transmute.
2. **Current Fail-Closed Gap in `Trusted.MirAst` and `Trusted.MirSemantics`:**
   - In `trusted/lean/Trusted/MirAst.lean:699-740`, `inductive AssertKind` includes `.misalignedPtrDeref` and `.nullPtrDeref`, but explicitly maps `AssertKind::NullReferenceConstructed` and `AssertKind::InvalidEnumConstruction` to `.unsupported` (lines 727-731).
   - In `trusted/lean/Trusted/MirSemantics.lean:1568-1569`, `evalTerminator` faults closed on **every** `.assert` terminator:
     ```lean
     | .unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .unsupported =>
       .fault .unsupported
     ```
   - Therefore, any `optimized_mir` body instrumented by `CheckAlignment`, `CheckNull`, or `CheckEnums` is currently rejected fail-closed by `Trusted.MirSemantics.evalTerminator`. Extending Anneal to accept or discharge UB-check-instrumented MIR requires (a) adding `.nullRefConstructed` and `.invalidEnumConstruction` to `Trusted.MirAst.AssertKind`, (b) giving `.assert` deterministic non-unwinding abort semantics on condition failure (matching `UnwindAction::Unreachable` and `#[rustc_nounwind]`), and (c) handling `[MaybeUninit<u8>; N]` subslice transmutations emitted by `CheckEnums::insert_discr_cast_to_u128`.
3. **Never Confuse UB-Check Survival with Value-Validity Verification:** Because `CheckAlignment` skips unsized raw pointers and `CheckEnums` skips `Variants::Single`, `ty::Bool`, and pointer-dereference enum reads (`ce1`), observing zero panics under `-Z ub-checks=yes` provides **zero guarantee** of freedom from validity UB. Conversely, because all three passes satisfy no-false-positive soundness (`ubChecks_never_reject_well_defined_execution`), proving full Miri-level operational well-definedness at `Runtime(PostCleanup)` implies that compiling the verified crate with `-Z ub-checks=yes` will never introduce spurious runtime aborts (provided non-packed layout alignment `fieldAlign ∣ fieldOffset` holds).

---

### 5. Kernel-Checked Lean 4 Formalization (`support/SanitizerUbChecksAndCfiSoundness.lean`)

Basis: `derived` + `execution` (`leanprover/lean4` `v4.34.1`)

`support/SanitizerUbChecksAndCfiSoundness.lean` (1,185 lines) mechanizes all three subsystems in constructive Lean 4 with **zero** `sorry`, **zero** `Classical.choice`, **zero** `omega`, **zero** `bv_decide`, **zero** `native_decide`, **zero** `partial def`, **zero** `._unsafe_rec`, and **zero** warnings under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

| Theorem / Counterexample | Formal Property Proved | Kernel Axiom Set (`#print axioms`) |
| :--- | :--- | :--- |
| `ubChecks_never_reject_well_defined_execution` | For any target `cfg` with clamping `effectiveAlign t ∣ t.align` and any operation `op` satisfying `layoutAlignedOffset op` and `miriWellDefined op`, `runUbChecks cfg op = .ok`. | `[propext, Quot.sound]` |
| `ubChecks_sound_no_false_positives` | Bundles universal no-false-positive soundness with concrete verified witnesses for `&(*misaligned_p).tail` (allowed), `*null::<()>()` (allowed), `&*null::<()>()` (`abort .nullRefConstructed`), `&(*null::<AlignedStruct>()).tail` (`abort .nullRefConstructed` via `NoFollowProjections`), and offset-4 multi-byte niche rejection (`abort .invalidEnumConstruction`). | `[propext, Quot.sound]` |
| `cfi_jump_table_accepts_iff_matching_type_id` | For any 8-byte-stride jump table (`0 < slotCount ≤ 2^61`, `jtBase + 8 * slotCount ≤ 2^64`), `lowerTypeTestsCheck jtBase slotCount addr = true` iff `∃ k < slotCount, addr = jtBase + 8 * k`, covering both singleton `icmp eq` and general `ror3_64(diff) < slotCount` (`@llvm.fshl.i64(..., 61)`). | `[propext, Quot.sound]` |
| `cfi_generalize_strictly_coarser_and_arity_preserving` | Proves 4-point CFI lattice coarsening monotonicity (`m1 ≤ m2 → cfiTypeId m1 s1 = cfiTypeId m1 s2 → cfiTypeId m2 s1 = cfiTypeId m2 s2`), non-ZST arity preservation across all 4 modes, strictness on `target_i32_ptr` vs. `target_u8_ptr`, and x86-64 KCFI arity register separation (`%eax`, `%ecx`, `%edx`, `%ebx`) vs. default `%eax` collapse. | `[propext]` |
| `ignorelist_blame_and_attr_composition` | Proves `#[sanitize(s = "off")]` dominance over any ignorelist `=sanitize` rule, same-file last-match-wins resolution (`lSan ≥ lNo → isBlameIgnored = false`; `lNo > lSan → isBlameIgnored = true`), invariance of the 4 unfiltered `FIXME` sanitizers (`SAFESTACK`, `SHADOWCALLSTACK`, `MEMTAG`, `REALTIME`), and exact agreement with the 4-function `[address]` matrix. | `[propext, Quot.sound]` |
| `ce1_ub_checks_miss_single_variant_bool_and_ptr_read_enum_ub` | Constructive 3-way counterexample proving `transmute::<u8, SingleWrapBool>(2)`, `transmute::<u8, bool>(2)`, and `*(ptr as *const DirectEnum)` (byte `2`) all satisfy `¬ miriWellDefined` yet `runUbChecks x86HostUbCfg = .ok`. | `[propext, Quot.sound]` |
| `ce2_cfi_generalize_pointers_admits_cross_pointee_type_confusion` | Constructive counterexample proving `target_i32_ptr` and `target_u8_ptr` have distinct raw CFI type IDs (and `target_u8_ptr` fails the 1-slot jump-table check), identical generalized CFI type IDs, and both pass the 2-slot `ror3_64` check while misaligned mid-slot address `jtBase + 1` fails. | `[propext]` |
| `ce3_forgetting_blame_ordering_drops_later_sanitize_reenable_rule` | Constructive counterexample proving an order-insensitive ignorelist (`naiveSetIgnored`) misclassifies `ignorelist_reenabled_fn` (matched at line 3 plain + line 4 `=sanitize` across 4-axis aggregation) as ignored, whereas `isBlameIgnored` preserves ASan instrumentation. | `[]` *(no axioms)* |

## Boundaries

### Unsupported
- **`-Z sanitizer-ignorelist` on `rustc 1.98.0-nightly (14210df0e)`:** Explicitly unsupported (`error: unknown unstable option: sanitizer-ignorelist`); support landed in `rust-lang/rust@c0e55d66cca54bd3ad8b78e152d8d07fc976da0a` (`2026-09-03`). All ignorelist blame-algebra findings for `342d74463` therefore rest on direct primary-source inspection (`source`) and Lean mechanization (`derived`), whereas `#[sanitize(address = "off")]` was directly executed on `14210df0e` (`execution`).
- **Ignorelist filtering for `SAFESTACK`, `SHADOWCALLSTACK`, `MEMTAG`, and `REALTIME` at `rust-lang/rust@342d74463`:** Explicitly unimplemented in `SanitizerIgnoreList::filter_instance_sanitizers` (`ignorelist/mod.rs:151-153`), and `REALTIME` attribute generation (`attributes.rs:202`) bypasses the filtered `enabled` set completely.
- **KCFI with `-C panic=unwind`:** Explicitly rejected by `rustc` (`error: -Z sanitizer=kcfi requires -C panic=abort`).
- **Multiple `!kcfi_type` attachments per function:** Unsupported by LLVM KCFI (`declare.rs:231`, `kcfi/typeid/mod.rs:39`), motivating `rustc`'s `ReifyReason::FnPtr` shim synthesis.

### Known Not to Apply
- **`check_pointers` on unsized raw pointers, safe references, `Box<T>`, and `&raw const`:** Explicitly excluded by `PointerFinder::visit_place` (`check_pointers.rs:182-234`); neither `CheckAlignment` nor `CheckNull` instruments these accesses.
- **`CheckEnums` on `Variants::Single`, `ty::Bool`, structs, and pointer reads:** Known not to apply (`check_enums.rs:168-196`); confirmed both in MIR dumps (`0` enum asserts) and live runtime runs (`rc = 0` on UB inputs caught by Miri).
- **LLVM sanitizer IR passes on `-Z sanitizer=leak` and during post-link LTO:** Known not to apply (`PassWrapper.cpp:882-959`, `write.rs:631-632`, `link.rs:1779-1784`).
- **Non-packed alignment assumption for `CheckAlignment` `FollowProjections`:** Theorem `checkAlignment_sound` requires `fieldTy.align ∣ fieldOffset` (`layoutAlignedOffset`); it does not claim soundness for unaligned field offsets in `#[repr(packed)]` structs (which Rust forbids taking references to without unsafe workarounds that are themselves UB).
- **`#[sanitize(... = "off")]` override by ignorelist `=sanitize`:** Known not to apply (`attributes.rs:158-170`); an attribute disabling a sanitizer cannot be undone by an ignorelist file.

### Not Examined
- **Cross-DSO / shared-object CFI (`-Z sanitizer=cfi` across `cdylib` boundaries, `-Z sanitizer-cfi-canonical-jump-tables=no` impact on cross-DSO function-pointer equality):** Only single-binary LTO execution was probed; in single-binary LTO, `-Z sanitizer-cfi-canonical-jump-tables=no` removed the `"CFI Canonical Jump Tables"` module flag while still emitting `.cfi.jumptable` for the single translation unit.
- **Non-x86-64 architectures (`aarch64`, `riscv64`, `i686`):** Jump-table entry strides, KCFI preamble instructions and arity registers (`-Z sanitizer-kcfi-arity` on AArch64), and targets with `max_reliable_alignment() < Align::MAX` (e.g., 32-bit targets with restricted stack/malloc alignment) were not executed locally.
- **Full `-Z build-std` sanitizer runs, MSan/LSan runtime detection, and kernel/hardware sanitizers:** Live MSan runtime uninitialized-memory detection (which requires an MSan-instrumented `std`/libc), live LSan leak-reporting exit behavior under `ptrace`, and HWASan / KASAN / KHWASan / MemTag / SafeStack / ShadowCallStack / DFSan / RTSan were not executed.
- **Multi-file `-Z sanitizer-ignorelist` CLI precedence and `type:` ignorelist runtime suppression:** Verified in source (`RustWrapper.cpp:1800-1819`, `context.rs:874-883`, `builder.rs:1998, 2134`) but not executed on a `>= 2026-09-03` toolchain.
- **Direct Lean refinement linking `SanitizerUbChecksAndCfiSoundness.lean` to `joshlf/anneal`'s `Trusted.MirSemantics` or to LLVM's C++ `LowerTypeTests` implementation:** The Lean module is a self-contained standalone model faithfully mirroring the audited algorithms; it does not import `Trusted.MirSemantics` or verify LLVM's C++ pass implementation.

### Unknown
- **Exact `rustc` commit range where `unreachable_unchecked` at `-O0 -Z ub-checks=no` still fires `precondition_check`:** Observed empirically on `14210df0e` (`ub_no_O0` returned `rc = -6` while `ub_no_O2` eliminated the call completely); whether newer `rustc` nightlies (`342d74463`) fold `intrinsics::ub_checks()` earlier at `-O0` was not executed on `342d74463`.

### Attractive Stronger Conclusions Not Established
- Passing `-Z ub-checks=yes` does **not** establish absence of Rust Undefined Behavior (even for enum discriminants or pointers), because `CheckEnums` misses single-variant wrappers, `bool`, and pointer reads, `check_pointers` misses unsized pointers, and neither checks provenance, aliasing (Stacked/Tree Borrows), or uninitialized memory.
- Passing `-Z sanitizer-cfi-generalize-pointers=yes` does **not** preserve pointee type safety across indirect calls; it preserves only non-ZST arity and non-pointer parameter/return types while collapsing all immutable pointers (`*const T`, `fn(...)`) to `PKv`.
- Enabling `-Z sanitizer-ignorelist` at `rust-lang/rust@342d74463` does **not** filter `SAFESTACK`, `SHADOWCALLSTACK`, `MEMTAG`, or `REALTIME`.

## Evidence

### 1. Primary-Source Git References (All Commit SHAs Resolved Live on `2026-11-22`)

#### `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`
- `compiler/rustc_mir_transform/src/check_pointers.rs`: lines 10–22 (`PointerCheck`, `BorrowedFieldProjectionMode`), 43–145 (`check_pointers`, `LangItem::PanicImpl` guard at 62–64, reverse iteration at 74–75, `UnwindAction::Unreachable` at 117), 182–250 (`PointerFinder::should_visit_place`, `visit_place`, `FollowProjections` at 219–228, `is_sized` at 231–234, `excluded_pointees` at 237–245).
- `compiler/rustc_mir_transform/src/check_alignment.rs`: lines 14–35 (`PassPolicy::optional(ctx.ub_checks())`, `excluded_pointees = [bool, i8, u8]`, `FollowProjections`), 39–148 (`insert_alignment_check`, `max_reliable_alignment()` clamping at 86–108, `AssertKind::MisalignedPointerDereference` at 143–146).
- `compiler/rustc_mir_transform/src/check_null.rs`: lines 12–27 (`PassPolicy::optional(ctx.ub_checks())`, `excluded_pointees = []`, `NoFollowProjections`), 29–128 (`insert_null_check`, `SharedBorrow`/`Borrow` -> unconditional `AssertKind::NullReferenceConstructed` at 55–68, non-borrow `size_of != 0` -> `AssertKind::NullPointerDereference` at 70–88).
- `compiler/rustc_mir_transform/src/check_enums.rs`: lines 18–112 (`CheckEnums`, `PassPolicy::optional(ctx.ub_checks())`, `LangItem::PanicImpl` guard at 27–29), 166–238 (`EnumFinder::visit_rvalue`: `CastKind::Transmute` + `adt_def.is_enum()`, `Variants::Empty`, `Variants::Single {}` at 196, `TagEncoding::Direct`, `TagEncoding::Niche`), 257–336 (`insert_discr_cast_to_u128`, `[MaybeUninit<u8>; N]` subslice at 278–303), 338–541 (`insert_direct_enum_check`, `insert_uninhabited_enum_check`, `insert_niche_check` with `WrappingRange` at 489–540).
- `compiler/rustc_mir_transform/src/lib.rs`: lines 684–714 (`run_runtime_cleanup_passes` -> `Runtime(PostCleanup)` at 691; `run_optimization_passes` scheduling `CheckAlignment`, `CheckNull`, `CheckEnums` at 711–713).
- `compiler/rustc_mir_transform/src/pass_manager.rs`: lines 88–107 (`PassPolicy`), 167–173 (`Deref<Target = Session>` for `PassCtx`), 256–285 (`should_run_pass`).
- `compiler/rustc_session/src/session.rs`: lines 1095–1097 (`Session::ub_checks`).
- `compiler/rustc_middle/src/mir/syntax.rs`: lines 1052–1055 (`AssertKind` UB-check variants).
- `compiler/rustc_codegen_ssa/src/mir/block.rs`: lines 815–831 (`AssertKind` lowering to panicking lang items).
- `library/core/src/panicking.rs`: lines 277–334 (`#[rustc_nounwind]` on all four UB-check panic lang items).
- `library/core/src/ub_checks.rs`: lines 58–108 (`assert_unsafe_precondition!`, `check_library_ub`, `check_language_ub` via `const_eval_select!`).
- `compiler/rustc_sanitizers/src/cfi/typeid/mod.rs`: lines 11–55 (`TypeIdOptions`).
- `compiler/rustc_sanitizers/src/cfi/typeid/itanium_cxx_abi/mod.rs`: lines 25–128 (`typeid_for_fnabi`, `PassMode::Ignore` skip at 71, `.normalized`/`.generalized` suffixes at 97–103).
- `compiler/rustc_sanitizers/src/cfi/typeid/itanium_cxx_abi/transform.rs`: lines 76–219 (`NORMALIZE_INTEGERS` and `GENERALIZE_POINTERS` folding rules).
- `compiler/rustc_sanitizers/src/kcfi/typeid/mod.rs`: lines 16–57 (`XxHash64` lower 32 bits, `ShimKind::Reify(_, Some(ReifyReason::FnPtr))`).
- `compiler/rustc_codegen_llvm/src/declare.rs`: lines 198–246 (CFI powerset `!type` metadata loop; KCFI single `!kcfi_type`).
- `compiler/rustc_codegen_llvm/src/type_.rs`: lines 327–349 (`add_type_metadata`, `set_kcfi_type_metadata`).
- `compiler/rustc_codegen_llvm/src/context.rs`: lines 292–369 (module flags `"CFI Canonical Jump Tables"`, `"cfi-normalize-integers"`, `"EnableSplitLTOUnit"`, `"kcfi"`, `"kcfi-offset"`, `"kcfi-arity"`), 694–708 (per-CGU ignorelist parse), 874–883 (`is_sanitizer_type_ignored`).
- `compiler/rustc_codegen_llvm/src/builder.rs`: lines 1969–2149 (`cfi_type_test` emitting `@llvm.type.test` + `abort_immediate()`/`__ubsan_handle_cfi_check_fail*`; `kcfi_operand_bundle` emitting `[ "kcfi"(i32 ...) ]`).
- `compiler/rustc_codegen_llvm/src/attributes.rs`: lines 150–210 (`sanitize_attrs`, attribute subtraction before `filter_instance_sanitizers`, `REALTIME` bypass at 202), 370–376 (probestack disabled for ASan/TSan), 568–574 (naked functions skip `sanitize_attrs`).
- `compiler/rustc_codegen_llvm/src/back/write.rs`: lines 631–645 (pre-link `!is_lto` `SanitizerOptions`).
- `compiler/rustc_codegen_llvm/src/back/lto.rs`: lines 61–72 (MSan weak symbols preserved across LTO).
- `compiler/rustc_codegen_ssa/src/back/link.rs`: lines 1774–1790 (sanitizer runtime archives, LSan link-only condition at 1779–1784).
- `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp`: lines 843–959 (`LowerTypeTestsPass`, `DataFlowSanitizerPass`, `MemorySanitizerPass`, `ModuleThreadSanitizerPass`/`ThreadSanitizerPass`, `AddressSanitizerPass`, `HWAddressSanitizerPass`, `RealtimeSanitizerPass`).
- `compiler/rustc_structures/src/sanitizer_set.rs`: lines 10–27 (`SanitizerSet` bit positions `1 << 0` .. `1 << 13`).
- `compiler/rustc_sanitizers/src/ignorelist/mod.rs`: lines 8–10 (`is_blame_ignored`), 65–99 (`instance_blame`), 111–159 (`filter_instance_sanitizers`, `FIXME` at 151–153), 180–212 (`typename_for_ignore_list`, `section_to_sanitizer_set`). (Introduced in `rust-lang/rust@c0e55d66cca54bd3ad8b78e152d8d07fc976da0a`, `2026-09-03`.)
- `compiler/rustc_sanitizers/src/ignorelist/ffi.rs`: lines 8–52 (`Blame`, FFI declarations).
- `compiler/rustc_llvm/llvm-wrapper/RustWrapper.cpp`: lines 1786–1941 (`RustSanitizerSpecialCaseList`, reverse-section `inSectionBlame`, bitmask mapping matching `SanitizerSet`).

#### `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
- Direct `diff -u` against `342d74463` on `check_pointers.rs`, `check_alignment.rs`, `check_null.rs`, `check_enums.rs`, `cfi/typeid/mod.rs`, `kcfi/typeid/mod.rs`, `attributes.rs` established: `is_enabled`/`is_required` (pre-`PassPolicy`), unified `AssertKind::NullPointerDereference` in `check_null.rs:58-126`, and absence of `compiler/rustc_sanitizers/src/ignorelist/mod.rs` (HTTP 404).

#### `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`
- `trusted/lean/Trusted/MirAst.lean`: lines 699–740 (`AssertKind` constructor correspondence; `NullReferenceConstructed` and `InvalidEnumConstruction` mapped to `.unsupported`).
- `trusted/lean/Trusted/MirSemantics.lean`: lines 1568–1569 (`evalTerminator` failing closed with `.fault .unsupported` on `.assert`).

### 2. Preserved Empirical Probe and Results (`2026-11-22`)

- **Probe script:** `support/probe_sanitizers_cfi_ub_checks.py`
- **Recorded live output (paths/PIDs/ASLR addresses scrubbed):** `support/probe_results.json`
- **Executed toolchain:** `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`LLVM version: 22.1.6`), `miri 0.1.0 (14210df0e2 2026-05-31)`, host `x86_64-unknown-linux-gnu`.
- **Invocation:**
  ```bash
  python3 support/probe_sanitizers_cfi_ub_checks.py --out support/probe_results.json
  ```
  Exit code `0`; ran all 13 UB-check cases across 4 `rustc` configurations (`ub_yes_O0`, `ub_yes_O2`, `ub_no_O0`, `ub_no_O2`) + MIR pass dumps (`-Z dump-mir=all`) + 13 live `cargo miri run` invocations, all 6 LTO CFI / KCFI modes (including live execution of `valid`, `valid_two_args`, `ptr_mismatch`, `arity_mismatch`), all 4 sanitizer modes (including live ASan heap-buffer-overflow `rc = 1` and live TSan data-race `rc = 66`), and `#[sanitize(address = "off")]` + `-Z sanitizer-ignorelist` feature detection.

### 3. Preserved Lean 4 Proof Artifact and Kernel Verification (`2026-11-22`)

- **Proof file:** `support/SanitizerUbChecksAndCfiSoundness.lean` (1,185 lines, 50,427 bytes).
- **Executed verifier:** `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
- **Invocation:**
  ```bash
  lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    support/SanitizerUbChecksAndCfiSoundness.lean
  ```
- **Verbatim `#print axioms` output (exit code `0`, zero warnings, zero forbidden tokens):**
  ```text
  'SanitizerUbChecksAndCfiSoundness.ubChecks_never_reject_well_defined_execution' depends on axioms: [propext, Quot.sound]
  'SanitizerUbChecksAndCfiSoundness.ubChecks_sound_no_false_positives' depends on axioms: [propext, Quot.sound]
  'SanitizerUbChecksAndCfiSoundness.cfi_jump_table_accepts_iff_matching_type_id' depends on axioms: [propext, Quot.sound]
  'SanitizerUbChecksAndCfiSoundness.cfi_generalize_strictly_coarser_and_arity_preserving' depends on axioms: [propext]
  'SanitizerUbChecksAndCfiSoundness.ignorelist_blame_and_attr_composition' depends on axioms: [propext, Quot.sound]
  'SanitizerUbChecksAndCfiSoundness.ce1_ub_checks_miss_single_variant_bool_and_ptr_read_enum_ub' depends on axioms: [propext, Quot.sound]
  'SanitizerUbChecksAndCfiSoundness.ce2_cfi_generalize_pointers_admits_cross_pointee_type_confusion' depends on axioms: [propext]
  'SanitizerUbChecksAndCfiSoundness.ce3_forgetting_blame_ordering_drops_later_sanitize_reenable_rule' does not depend on any axioms
  ```

## Revalidation

To revalidate these findings against a newer `rustc` nightly (including a toolchain at or after `rust-lang/rust@c0e55d66c` that supports `-Z sanitizer-ignorelist`) or a newer `joshlf/anneal` revision:

1. **Re-run the standalone empirical probe (`~45s` including Miri):**
   ```bash
   python3 support/probe_sanitizers_cfi_ub_checks.py --out /tmp/reval_probe_results.json
   ```
   Check the key discriminators in `/tmp/reval_probe_results.json`:
   - `probe_1_ub_checks.ub_yes_O0.runtime`: confirm `borrow_u8_misaligned_struct` (`rc = 0`) and `deref_zst_null` (`rc = 0`) remain false-positive-free; check whether `borrow_zst_null` / `borrow_u8_null_struct` print `"null reference produced"` (post-`NullReferenceConstructed` split) and whether `single_wrap_bool_bad`, `raw_bool_bad`, or `ptr_read_enum_bad` remain `rc = 0` (if any starts returning `-6`, `CheckEnums` or a new MIR validity pass expanded coverage).
   - `probe_2_lto_cfi_vs_kcfi`: confirm `lto_cfi_default.runtime.ptr_mismatch.rc == -4`, `lto_cfi_generalize_ptrs.runtime.ptr_mismatch.rc == 0`, `lto_cfi_generalize_ptrs.runtime.arity_mismatch.rc == -4`, and `kcfi_arity.asm_signals.kcfi_preambles` maps `0/1/2/3` args to `%eax`/`%ecx`/`%edx`/`%ebx`.
   - `probe_3_asan_tsan_msan_lsan`: confirm ASan `run_oob.rc == 1` (`detected_heap_overflow == true`), TSan `run_race.rc == 66` (`detected_data_race == true`), MSan emits `@__msan_track_origins`, and LSan emits zero IR instrumentation.
   - `probe_4_sanitize_attr_and_ignorelist`: on a toolchain with `supports_z_sanitizer_ignorelist == true`, verify `ignorelist_mode.compile_rc == 0` and exact per-function ASan flags: `normal_fn = true`, `attr_off_fn = false`, `ignorelist_excluded_fn = false`, `ignorelist_reenabled_fn = true`.

2. **Targeted upstream source diffs (fastest check for policy or `FIXME` changes):**
   - Diff `compiler/rustc_mir_transform/src/{check_pointers,check_alignment,check_null,check_enums,lib}.rs` against `342d74463` for changes to `excluded_pointees`, `BorrowedFieldProjectionMode`, `EnumFinder::visit_rvalue` (`Variants::Single` / `ty::Bool`), or pass ordering relative to `Runtime(PostCleanup)`.
   - Diff `compiler/rustc_sanitizers/src/ignorelist/mod.rs` and `compiler/rustc_codegen_llvm/src/attributes.rs` against `342d74463` to see whether the `FIXME` omitting `SAFESTACK`, `SHADOWCALLSTACK`, `MEMTAG`, and `REALTIME` has been resolved.
   - Diff `trusted/lean/Trusted/MirAst.lean` (`inductive AssertKind`) and `trusted/lean/Trusted/MirSemantics.lean` (`evalTerminator`) in `joshlf/anneal` against `c131b320e` to check whether `.nullRefConstructed`, `.invalidEnumConstruction`, and `.assert` evaluation have been added.

3. **Re-verify the Lean 4 mechanization (`~6s`):**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/SanitizerUbChecksAndCfiSoundness.lean
   ```
   Confirm exit code `0`, zero diagnostics, and that `#print axioms` reports no axioms outside `[propext, Quot.sound]`.
