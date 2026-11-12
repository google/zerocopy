# Anneal Prefix-Safety Scalar MIR Differential Execution, `DefKind::AnonConst` Taxonomy, and Capture-vs-`bodyWF` Admission Alignment

## Summary

This report synthesizes a four-way differential execution challenge (`Native rustc`, `Miri`, `Lean 4.34.1` kernel `rfl`, and end-to-end `cargo-anneal verify`), a `rustc_driver` `DefKind::AnonConst` / `InlineConst` taxonomy, and a capture-vs-`bodyWF` alignment study for Anneal's prefix-safety scalar MIR verification pipeline (`joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b`, `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):

1. **Zero Semantic Mismatches Across 38 Admitted Scalar, Signed-Shift, Storage-Lifecycle, and Enum Functions (`159` Boundary Vectors) plus `35` Extended `UnaryOp` / Constant Vectors**:
   - Across all `38` baseline admitted functions (`159` boundary input vectors) and `6` Phase 1/Phase 2 extended functions (`35` boundary input vectors), **Native `rustc` (`1.98.0-nightly`, `-C opt-level=0 -C overflow-checks=no`)**, **Miri (`-Zmiri-disable-Stacked-Borrows` / default Tree/Stacked Borrows)**, **Lean 4.34.1 kernel `rfl` over `Trusted.Mvp.run fuel body args`**, and **end-to-end `cargo-anneal verify`** achieved **100% agreement (`0` semantic mismatches)**:
     - Signed two's-complement wrapping arithmetic (`i8`, `i16`, `i32`, `i64`, `isize`) at `MIN`, `-1`, `0`, `1`, and `MAX` (including `i8::MIN.wrapping_sub(1) == 127` and `i8::MIN.wrapping_mul(-1) == -128`);
     - Signed arithmetic right shift (`evalShift` via `signExtend bits value >>> shift` followed by `truncate bits`) across mixed shift-count widths (`i8 >> u8`, `i8 >> u32`, `i16 >> i8`, `i32 >> u64`, `i64 >> u8`) at `0`, `1`, `bits - 2`, and `bits - 1`;
     - Signed relational comparisons (`lt`, `le`, `gt`, `ge`, `eq`, `ne`) via `toSigned bits lhs < toSigned bits rhs` on `i8` (`-128 < 127`), `i16`, `i32`, `i64`, and `isize`;
     - Fieldless enum discriminants with negative (`-128`, `-1`), zero, sparse (`1000`), and `i64::MIN` (`0x8000000000000000`) / `i64::MAX` (`0x7fffffffffffffff`) `#[repr(i8/i16/i64/u64)]` tags, verifying the model's separation between logical `0`-based variant indices in `Slot.val` and `isize` bit-patterns produced by `Rvalue.discriminant`; and
     - Multi-cycle `StorageLive` -> `Assign` -> `Move` -> `StorageDead` -> `StorageLive` slot re-initialization.

2. **Controlled `#[custom_mir]` Invalid-State Probes and Deliberate Conservative Refusals (`11` Cases)**:
   - Using `#![feature(custom_mir, core_intrinsics)]` (`dialect = "runtime", phase = "post-cleanup"`), we constructed MIR bodies unreachable from safe Rust surface syntax and compared Lean kernel evaluation against Miri:
     - **Reading uninitialized (`Slot.uninit`) or dead (`StorageDead`) locals**: Miri raises UB (`using uninitialized data`) and Lean evaluates `run` to `.fault .uninitializedLocal` (`rfl`).
     - **Reading a moved `Copy` local (`Operand.move` followed by `Operand.copy` without re-initialization)**: Miri permits the second read because `Runtime(PostCleanup)` treats `Operand::Move` and `Operand::Copy` identically for `Copy` types (`rust-lang/rust` `compiler/rustc_mir_transform/src/elaborate_drops.rs`), whereas Anneal's `evalOperand` transition overwrites the source slot with `.uninit` on `.move`, fault-stopping with `.fault .uninitializedLocal`. Because `Verified` guarantees fault-freedom (`noFault`), any program verified by Anneal is strictly free of post-move reads; thus this is a **sound conservative over-approximation** (`Anneal Verified => Rust/Miri UB-free`).
     - **Shift count `>= bit_width` (`x << 8` on `u8`, negative shift count `-1i8` with unsigned bit-pattern `255 >= 8`) and `INT_MIN / -1` or `/ 0` under `-C overflow-checks=no`**: Lean's `evalShift` (`shift >= bits -> .error .shiftOverflow`) and `evalBinary` (`rhs == 0 -> .error .divisionByZero`; signed `lhs == MIN && rhs == -1 -> .error .signedDivisionOverflow`) match Rust and Miri UB rules exactly.

3. **`DefKind::AnonConst` vs. `DefKind::InlineConst` Taxonomy and Dead-Branch CTFE under `--emit=metadata`**:
   - Inspecting `tcx.iter_local_def_id()` in `rustc 1.98.0-nightly` (`support/anon_const_and_capture_probe.rs`) establishes that:
     - Explicit enum variant discriminants (`Variant = expr`) create a body-owning `DefKind::AnonConst` (`parent = DefKind::Variant`, `grandparent = DefKind::Enum`, `generics_count = 0`) whose `DefId` matches `v.discr == ty::VariantDiscr::Explicit(def.to_def_id())`. Implicit variants (`Relative(1)`) create no child `AnonConst`. Array lengths inside enum variant fields have `parent = DefKind::Field` (not `DefKind::Variant`), array lengths in functions have `parent = DefKind::Fn`, generic `const` defaults have `parent = DefKind::Struct`, and inline `const { ... }` blocks use a separate `DefKind::InlineConst` constructor (`generics_count = 1`, `ConstContext::Const { inline: true }`).
     - Every enum variant discriminant is evaluated by `rustc_hir_analysis::check_crate` (`check_well_formed`) **before** `Callbacks::after_analysis` runs (`pub enum Bad { X = 1 / 0 }` and `pub enum BadPanic { X = { panic!(...) } }` fail with `E0080` and never enter `after_analysis`), and `adt.discriminants(tcx)` re-evaluates all variant discriminants when building `Ty.enum id discriminants`.
     - By contrast, under `--emit=metadata` (used by `anneal-rustc-capture`), a dead-branch inline constant `pub fn dead_inline_const_div_zero(x: i32) -> i32 { if false { const { 1 / 0 } } else { x + 7 } }` reaches and finishes `after_analysis` with **zero compiler errors** (`has_errors_at_after_analysis_entry = false`, `driver_result_ok = true`) unless `body.required_consts` is explicitly evaluated via `tcx.const_eval_resolve(ty::TypingEnv::fully_monomorphized(), uv, req.span)`.

4. **Capture-vs-`bodyWF` Alignment and Resolving All `10` Unexpected Refusals + Starnix `verifier::saturating_inc_u32`**:
   - **Phase 1 (Adapter-only changes in `trusted/rustc-capture/src/{capture.rs,extract.rs}`; zero changes to `Syntax.lean` or `Semantics.lean`)** resolves **7 of the 10 Task 2 refusals plus Starnix's `verifier::saturating_inc_u32`**:
     1. Admitting variant-discriminant `DefKind::AnonConst` and scalar `DefKind::Const` / `DefKind::InlineConst` in `whole_crate_item` (`--scope crate`);
     2. Resolving `mir::Const::Unevaluated(uv, _)` via `tcx.const_eval_resolve(ty::TypingEnv::fully_monomorphized(), uv, span)` across both `body.required_consts` and `Operand::Constant` (at `-C opt-level=0`, associated constants like `i8::MIN` and `u32::MAX` and `const` items remain `Const::Unevaluated` in `Runtime(PostCleanup)` MIR), which admits `i8::MIN`, `u32::MAX`, `const MODULE_CONST: i32 = -42`, `const { -42 }`, and Starnix's `verifier::saturating_inc_u32` while rejecting dead-branch `if false { const { 1 / 0 } }` and `if false { const { panic!() } }`;
     3. Lowering zero-field `Rvalue::Aggregate(AggregateKind::Adt(adt_did, variant_idx, ..), [])` to existing `Rvalue.use (Operand.constant (.enum id ds) variant_idx) false` (already supported by unmodified `Semantics.lean`);
     4. Lowering identity `Rvalue::Cast(CastKind::IntToInt)` (`e as isize` after `_2 = discriminant(_1)`) to `Rvalue.use operand false`; and
     5. Rejecting non-enum `Rvalue::Discriminant(place)` (`!place.ty(&body.local_decls, tcx).ty.is_enum()`) at capture (`status: "unsupported"`), eliminating the `status: "captured"` / `bodyWF = false` mismatch.
   - **Phase 2 (Minimal `Trusted.Mvp` model refinement)** resolves the remaining 3 items:
     1. Removing `!ds.isEmpty` from `Ty.admitted` in `Semantics.lean` makes uninhabited `EmptyEnum` (`Ty.enum id []`) admitted with `validValue (.enum id []) _ = false` (identical in inhabitant set to `Ty.never`), preserving all existing theorems in `Anneal/Mvp/Execution.lean` and verifying `pub fn match_empty(e: EmptyEnum) -> u64 { match e {} }` end-to-end (`status: "crate_verified"`).
     2. Adding `UnaryOp` (`neg`, `not`) and `Rvalue.unary` to `Syntax.lean` and `Semantics.lean` verifies `-x` and `!x` across signed integers (`i8`, `i64`), unsigned integers (`u8`), and `bool` in 100% agreement with Native `rustc` and Miri (`35` Lean kernel `rfl` theorems).

## Applicability

These findings apply to:

- **Anneal Prefix-Safety Scalar MIR Pipeline**: `joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b` (`trusted/lean/Trusted/Mvp/{Syntax,Semantics,Theorem}.lean`, `trusted/rustc-capture/src/{capture.rs,extract.rs,ir.rs,lean.rs}`, `theory/Anneal/Mvp/{Execution,Step}.lean`), with the self-contained scalar MIR semantics and Phase 1/2 deltas inlined in Section 1 below.
- **Rust Nightly Compiler and Miri**: `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`rustc 1.98.0-nightly (f8a08b688 2026-05-30)`, `miri 0.1.0 (f8a08b688 2026-05-30)`), compiled under the pinned capture profile (`--edition=2021 -C opt-level=0 -C debug-assertions=off -C overflow-checks=no`).
- **The Rust Reference**: `rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` (`expressions/operator-expr.md`, `items/enumerations.md`, `behavior-considered-undefined.md`).
- **Lean 4 Kernel**: `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).
- **Fuchsia Starnix `ebpf_core`**: `fuchsia/fuchsia@823a15538f191b9dbd9ebafaa6ba23220b87d2e1` (`src/starnix/lib/ebpf/core/src/verifier.rs`, `saturating_inc_u32`).

## Findings

### 1. Inlined Prefix-Safety Scalar MIR Semantics and Four-Way Differential Harness

#### 1.1 Scalar word representation, arithmetic, shifts, comparisons, and enum discriminants
In Anneal's prefix-safety scalar MIR model (`Trusted/Mvp/Syntax.lean` and `Trusted/Mvp/Semantics.lean`), runtime values are represented uniformly as 64-bit machine words (`abbrev Word := BitVec 64`) paired with a static type descriptor (`Ty.bool`, `Ty.unit`, `Ty.never`, `Ty.int bits signed` for `bits ∈ {8, 16, 32, 64}`, or `Ty.enum id discriminants`):
- **Bit truncation, sign extension, and signed interpretation**:
  ```lean
  def maskBits (bits : Nat) : Nat := Nat.pow 2 bits - 1
  def truncate (bits : Nat) (value : Word) : Word :=
    BitVec.ofNat 64 (value.toNat &&& maskBits bits)
  def signBit (bits : Nat) : Nat := Nat.pow 2 (bits - 1)
  def signExtend (bits : Nat) (value : Word) : Word :=
    let raw := (truncate bits value).toNat
    if (raw &&& signBit bits) == 0 then BitVec.ofNat 64 raw
    else BitVec.ofNat 64 (raw ||| (maskBits 64 - maskBits bits))
  def toSigned (bits : Nat) (value : Word) : Int :=
    let raw := (truncate bits value).toNat
    if raw < signBit bits then Int.ofNat raw else Int.ofNat raw - Int.ofNat (Nat.pow 2 bits)
  ```
- **Validity invariant (`validValue`)**:
  - `validValue .bool v := v == 0 || v == 1`
  - `validValue .unit v := v == 0`
  - `validValue .never _ := false`
  - `validValue (.int bits _) v := decide (v.toNat < Nat.pow 2 bits)`
  - `validValue (.enum _ ds) v := decide (v.toNat < ds.length)`
- **Arithmetic, division/remainder, shifts, and casts**:
  - Under `-C overflow-checks=no`, `add`, `sub`, and `mul` evaluate `(lhs + rhs)`, `(lhs - rhs)`, and `(lhs * rhs)` modulo $2^{\text{bits}}$ via `truncate bits`.
  - `div` and `rem` fault with `.divisionByZero` when `rhs == 0`, and signed `div`/`rem` fault with `.signedDivisionOverflow` when `toSigned bits lhs == -Int.ofNat (signBit bits)` and `toSigned bits rhs == -1`; otherwise they compute truncated integer quotient (`Int.tdiv`) and remainder (`Int.tmod`).
  - `shl` and `shr` (`evalShift`) accept any admitted integer shift-count type `rhsTy = .int rhsBits rhsSigned`, extract `shift := (truncate rhsBits rhs).toNat`, and fault with `.shiftOverflow` whenever `shift ≥ bits` (including negative signed shift counts whose two's-complement bit-pattern satisfies `truncate rhsBits rhs ≥ bits`). When `shift < bits`, unsigned `shr` evaluates `truncate bits ((truncate bits lhs) >>> BitVec.ofNat 64 shift)` and signed `shr` evaluates `truncate bits ((signExtend bits lhs) >>> BitVec.ofNat 64 shift)`.
  - `Rvalue.discriminant place` reads a local of type `.enum id ds` holding logical variant index $v < |ds|$ and looks up `ds[v.toNat]?` (`isize` bit-pattern in `.int 64 true`). `Terminator.switchInt` branches directly on `ds[v.toNat]?` when the scrutinee has type `.enum id ds`.

#### 1.2 Four-way differential execution and seeded-error detection (`support/run_differential_harness.py`)
We executed `59` test cases (`159` boundary input vectors across `38` admitted functions, `10` unexpected refusals, `5` `#[custom_mir]` / UB cases, and `6` seeded error mutations) in [`support/run_differential_harness.py`](support/run_differential_harness.py) ([`support/differential_results.json`](support/differential_results.json)):

| Taxonomic Category | Cases | Input Vectors | Outcome |
| :--- | :---: | :---: | :--- |
| **1. Agreement (`Admitted & Equal`)** | `38` | `159` | **100% 4-way agreement** across Native `rustc`, Miri, Lean `rfl` (`Trusted.Mvp.run`), and `cargo-anneal verify`: signed wrapping `i8`/`i16`/`i32`/`i64` arithmetic, signed `div`/`rem`, mixed-width signed/unsigned shifts (`i8 >> u8`, `i8 >> u32`, `i16 >> i8`, `i32 >> u64`, `i64 >> u8`), signed relational comparisons, narrow-to-wide and wide-to-narrow integer casts, `#[repr(i8/i16/i64/u64)]` enum switches (`i64::MIN`, `-1`, `0`, `1000`, `i64::MAX`), and multi-cycle `StorageLive`/`StorageDead`/`Move` transitions. |
| **2. Deliberate Conservative Refusal / Fault** | `11` | `11` | **100% sound**: `5` source-level unsupported constructs (`checked_add` tuple, `&x` reference, struct, loop, `as` enum cast) refused at capture/model; `5` `#[custom_mir]` / runtime-fault cases (`shl 8` on `u8`, `shr -1i8` on `i8`, `i8::MIN / -1`, uninit read, dead-local read) fault in both Miri and Lean (`rfl`); `1` `#[custom_mir]` move-then-copy of `i32` faults conservatively in Lean (`.fault .uninitializedLocal`) while Miri allows it. |
| **3. Unexpected Refusal / Capture-vs-`bodyWF` Gap** | `10` | — | Diagnosed to root cause and **resolved 10/10** in Track B (Sections 2 and 3 below). |
| **4. Semantic Mismatch** | **`0`** | **`0`** | Zero silent semantic discrepancies between Anneal's Lean model and Rust/Miri execution. |
| **5. Seeded Error Detection Controls** | `6` | `6` | **6/6 caught (`100%`)**: logical `>>>` vs. arithmetic `>>` on `-128i8 >> 4` (`8` vs. `248`), unsigned vs. signed `<` on `-1i8 < 0i8` (`false` vs. `true`), zero-extension vs. sign-extension on `-1i8 as i32` (`255` vs. `4294967295`), variant index `0` vs. discriminant `255` (`-1i8`), masked shift `shift & 7` vs. fault on `1u8 << 8`, and wrong post-`StorageLive` value (`99` vs. `42`). |

Basis: **source**, **documentation**, and **execution** ([`support/run_differential_harness.py`](support/run_differential_harness.py), [`support/differential_results.json`](support/differential_results.json)).

---

### 2. `DefKind::AnonConst` vs. `DefKind::InlineConst` Taxonomy and `--emit=metadata` CTFE Semantics

#### 2.1 Complete `tcx.iter_local_def_id()` taxonomy across constant contexts
In `trusted/rustc-capture/src/capture.rs`, `--scope crate` iterates over `tcx.iter_local_def_id()`. Because `required(kind, has_body)` returns `true` for every body-owning HIR definition (`has_body == true`), any `DefKind::AnonConst` or `DefKind::InlineConst` inside a crate must be explicitly classified in `whole_crate_item`. Running [`support/anon_const_and_capture_probe.rs`](support/anon_const_and_capture_probe.rs) ([`support/anon_const_taxonomy_results.json`](support/anon_const_taxonomy_results.json)) under `rustc 1.98.0-nightly` established the exact structural invariants distinguishing the five constant contexts:

| Constant Construct | Example | `tcx.def_kind(def)` | `parent_kind` | `grandparent_kind` | `hir_body_const_context` | `generics_count` | `v.discr == Explicit(def)` | `mir_stolen_by_ctfe` at `after_analysis` |
| :--- | :--- | :--- | :--- | :--- | :--- | :---: | :---: | :---: |
| Explicit enum variant discriminant (literal) | `ExplicitEnum::Neg = -1` | `DefKind::AnonConst` | `DefKind::Variant` | `DefKind::Enum` | `Some(Const { inline: false })` | `0` | `true` | `false` |
| Explicit enum variant discriminant (compound expr) | `ExplicitEnum::Pos = 1 + 2` | `DefKind::AnonConst` | `DefKind::Variant` | `DefKind::Enum` | `Some(Const { inline: false })` | `0` | `true` | **`true`** (stolen during `check_crate` CTFE) |
| Implicit enum variant discriminant | `ExplicitEnum::ImplicitZero` | *(no child `AnonConst`)* | — | — | — | — | `false` (`Relative(1)`) | — |
| Array length inside enum variant payload | `PayloadArrayEnum::Arr([u8; 4])` | `DefKind::AnonConst` | **`DefKind::Field`** | `DefKind::Variant` | `Some(Const { inline: false })` | `0` | `false` | `false` |
| Array length / repeat count in function | `fn f() -> [u8; 4] { [0u8; 1 + 1] }` | `DefKind::AnonConst` | `DefKind::Fn` | `DefKind::Mod` | `Some(Const { inline: false })` | `0` | `false` | `true` (for `1 + 1`) |
| Inline `const { ... }` block | `const { 40 + 2 }`, `if false { const { 1 / 0 } }` | **`DefKind::InlineConst`** | `DefKind::Fn` | `DefKind::Mod` | `Some(Const { inline: true })` | **`1`** | `false` | `false` (under `--emit=metadata`) |
| Generic `const` parameter default | `struct S<const N: usize = 8>` (`8`) | `DefKind::AnonConst` | `DefKind::Struct` | `DefKind::Mod` | `Some(Const { inline: false })` | `0` | `false` | `false` |

#### 2.2 Soundness of variant-discriminant `AnonConst` admission vs. dead-branch `InlineConst` hazard under `--emit=metadata`
Our `rustc_driver` probes (`Probes 2–4` in [`support/anon_const_taxonomy_results.json`](support/anon_const_taxonomy_results.json)) proved a sharp distinction between enum variant discriminants and inline `const { ... }` blocks when `anneal-rustc-capture` runs with `--emit=metadata`:
1. **Enum variant discriminants are unconditionally evaluated by `check_crate` before `after_analysis`**:
   - Both `pub enum Bad { X = 1 / 0 }` and `pub enum BadPanic { X = { panic!("discriminant boom") } }` fail with `E0080` inside `rustc_hir_analysis::check_crate` (`check_well_formed`) and **never reach `Callbacks::after_analysis`** (`reached_after_analysis: false`, `driver_result_ok: false`).
   - Furthermore, for compound discriminant expressions (`Pos = 1 + 2`), `mir_for_ctfe` steals `mir_drops_elaborated_and_const_checked(def)` during `check_crate` (`mir_stolen_by_ctfe: true`), so attempting to run `capture_body` on the `AnonConst`'s runtime MIR would panic or read a stolen `Steal<Body>`. Instead, checking in `whole_crate_item` that `parent_kind == DefKind::Variant`, `grandparent_kind == DefKind::Enum`, `v.discr == ty::VariantDiscr::Explicit(def.to_def_id())`, and `extract::ty(tcx, enum_ty).is_ok()` (which evaluates `adt.discriminants(tcx)`) soundly admits explicit discriminants of supported fieldless enums while rejecting array-length `AnonConst`s on payload enums (`parent_kind == DefKind::Field`).
2. **Dead-branch `DefKind::InlineConst` reaches `after_analysis` without errors under `--emit=metadata` unless `body.required_consts` is evaluated**:
   - Compiling `pub fn dead_inline_const_div_zero(x: i32) -> i32 { if false { const { 1 / 0 } } else { x + 7 } }` with `--emit=metadata -C opt-level=0` reaches and exits `Callbacks::after_analysis` with **zero compiler errors** (`has_errors_at_after_analysis_entry: false`, `driver_result_ok: true`), because monomorphization/codegen (which normally forces evaluation of `body.required_consts`) does not run under `--emit=metadata`.
   - Evaluating every entry `req` in `body.required_consts` via `tcx.const_eval_resolve(ty::TypingEnv::fully_monomorphized(), uv, req.span)` inside `extract::body` triggers CTFE on `dead_inline_const_div_zero::{constant#0}`, catches the division by zero (`Err(ErrorHandled)`), and rejects the function as `status: "unsupported"` (`"required constant evaluation failed in the scalar model"`).

Basis: **source** and **execution** ([`support/anon_const_and_capture_probe.rs`](support/anon_const_and_capture_probe.rs), [`support/anon_const_taxonomy_results.json`](support/anon_const_taxonomy_results.json)).

---

### 3. Capture-vs-`bodyWF` Alignment and Phase 1 / Phase 2 Verification (`support/run_track_b_experiments.py`)

We implemented and tested two isolated stages in [`support/run_track_b_experiments.py`](support/run_track_b_experiments.py) ([`support/track_b_verification_receipts.json`](support/track_b_verification_receipts.json)):

#### 3.1 Phase 1: Resolving 7 of 10 Task 2 refusals + Starnix `verifier::saturating_inc_u32` with zero Lean changes
1. **Evaluating `mir::Const::Unevaluated` across `body.required_consts` and `Operand::Constant`**:
   At `-C opt-level=0` (`Runtime(PostCleanup)` MIR), associated constants (`i8::MIN`, `u32::MAX`) and `const` items (`const MODULE_CONST: i32 = -42`) appear both in `body.required_consts` and in `Operand::Constant` as `mir::Const::Unevaluated(uv, ty)`. Resolving `mir::Const::Unevaluated` via `tcx.const_eval_resolve(ty::TypingEnv::fully_monomorphized(), uv, span)` folds them to `ConstValue::Scalar(Scalar::Int(...))` at capture time, admitting `i8::MIN`, `u32::MAX`, `MODULE_CONST`, `const { -42 }`, and Starnix's `verifier::saturating_inc_u32` (which passes `bodyWF = true` and all 5 boundary execution vectors `0, 1, 41, u32::MAX - 1, u32::MAX` by `rfl` in unmodified `Semantics.lean`).
2. **Lowering zero-field enum `Rvalue::Aggregate` and identity `e as isize` casts to existing `Trusted.Mvp` forms**:
   Unmodified `Semantics.lean` already types and evaluates `(Operand.constant (.enum id ds) variant_idx)` (`operandTy = some (.enum id ds)`, `evalOperand = .ok (ty, BitVec.ofNat 64 variant_idx, locals)`). Lowering zero-field `Rvalue::Aggregate(AggregateKind::Adt(adt_did, variant_idx, ..), [])` to `Rvalue.use (Operand.constant enum_ty variant_idx) false` and lowering identity `Rvalue::Cast(CastKind::IntToInt)` (`src_ty == dst_ty`, emitted after `_2 = discriminant(_1)` for `e as isize`) to `Rvalue.use operand false` admits fieldless enum construction and `e as isize` with **zero changes to `Syntax.lean` or `Semantics.lean`**.
3. **Rejecting non-enum `Rvalue::Discriminant(place)` at capture**:
   Adding `if !place.ty(&body.local_decls, tcx).ty.is_enum()` in `extract::rvalue` rejects `#[custom_mir]` `Discriminant(x)` on `x: i32` with `status: "unsupported"` (`"bb0 statement 0: discriminant on non-enum type is unsupported: i32"`), closing the `status: "captured"` / `bodyWF = false` mismatch.

#### 3.2 Phase 2: Empty enum `Ty.admitted` (Option A vs. Option B) and `UnaryOp.neg` / `UnaryOp.not`
1. **Uninhabited `EmptyEnum` (`pub enum EmptyEnum {}`)**:
   - **Option A (Relax `Ty.admitted` in `Semantics.lean` by removing `!ds.isEmpty`)**: With `!ds.isEmpty` removed, `Ty.admitted (.enum id []) = true` while `validValue (.enum id []) value = decide (value.toNat < 0) = false` for all `value : Word`. Thus `Ty.enum id []` is an uninhabited type with the exact same inhabitant set (`∅`) as `Ty.never`. All existing theorems in `Anneal/Mvp/Execution.lean` and `Anneal/Mvp/Canaries.lean` compile unmodified, and `empty_enum_crate` (`pub fn match_empty(e: EmptyEnum) -> u64 { match e {} }`) passes full end-to-end `cargo-anneal verify` (`status: "crate_verified"`, `exactType: true`, `axioms: ["propext", "Quot.sound"]`).
   - **Option B (Reject `adt.variants().is_empty()` in `extract.rs`)**: Rejects `EmptyEnum` at capture with `status: "unsupported"`. Option A is strictly more general and eliminates a special case from `Semantics.lean`.
2. **`UnaryOp.neg` and `UnaryOp.not` (`Syntax.lean` + `Semantics.lean`)**:
   Adding `inductive UnaryOp | neg | not` and `Rvalue.unary op operand` with `evalUnary` (`truncate bits (0 - value)` for `.neg` on `.int bits true`, `boolWord (value == 0)` for `.not` on `.bool`, and `truncate bits (BitVec.not value)` for `.not` on `.int bits signed`) verified all `35` boundary vectors across `neg_i8`, `neg_i64`, `not_i8`, `not_u8`, and `not_bool` by `rfl` in 100% agreement with Native `rustc` and Miri.

| Case ID | Construct | Baseline (`f2bc17e9be`) | Phase 1 (`0` Lean Changes) | Phase 2 (Relaxed `Ty.admitted` + `UnaryOp`) | Verified Boundary Vectors (`Native == Miri == Lean rfl`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `c07_enum_match_i8` | `SimpleEnum { Neg = -1, Zero = 0, Pos = 1 }` (`--scope crate`) | Refused (`AnonConst`) | **Captured & Verified (`rfl`)** | **Captured & Verified (`rfl`)** | `[-10 (246), 0, 10]` |
| `c08_enum_discriminant_isize` | `e as isize` on `SimpleEnum` | Refused (`IntToInt` cast) | **Captured & Verified (`rfl`)** | **Captured & Verified (`rfl`)** | `[2^64 - 1, 0, 1]` |
| `c10_empty_enum_unreachable` | `pub enum EmptyEnum {}` + `match e {}` | Mismatch (`captured`, `bodyWF = false`) | **Option B: `status: "unsupported"`** | **Option A: `status: "crate_verified"`** | Uninhabited (`validValue = false`) |
| `c11_i8_min_const` / `c12_u32_max_const` | `i8::MIN`, `u32::MAX` (`Const::Unevaluated`) | Refused (`required_consts`) | **Captured & Verified (`rfl`)** | **Captured & Verified (`rfl`)** | `128` (`-128i8`), `4294967295` (`0xffffffff`) |
| `c13_const_item_neg` | `const MODULE_CONST: i32 = -42; x + MODULE_CONST` | Refused (`required_consts`) | **Captured & Verified (`rfl`)** | **Captured & Verified (`rfl`)** | `[4294967254, 0, 8]` |
| `c14_unary_neg` | `-x` on `i8` & `i64` (`-C overflow-checks=no`) | Refused (`UnOp::Neg`) | Refused (`UnOp::Neg`) | **Captured & Verified (`rfl`)** | `i8`: `[128, 1, 0, 255, 129]`; `i64`: `[2^63, 1, 0, 2^64-1]` |
| `c15_unary_not` | `!x` on `i8`, `u8`, and `bool` | Refused (`UnOp::Not`) | Refused (`UnOp::Not`) | **Captured & Verified (`rfl`)** | `i8`: `[127, 0, 255, 128]`; `u8`: `[255, 254, 127, 0]`; `bool`: `[1, 0]` |
| `c16_enum_variant_construct` | Constructing `SimpleEnum::{Neg,Zero,Pos}` | Refused (`AggregateKind::Adt`) | **Captured & Verified (`rfl`)** | **Captured & Verified (`rfl`)** | `[2^64 - 1, 0, 1]` |
| `c17_custom_mir_non_enum_discr` | `#[custom_mir]` `Discriminant(x)` on `x: i32` | Mismatch (`captured`, `bodyWF = false`) | **Rejected at capture (`unsupported`)** | **Rejected at capture (`unsupported`)** | Soundly refused at capture |
| `verifier::saturating_inc_u32` | Starnix `ebpf_core` `u32::MAX` saturating increment | Refused (`required_consts`) | **Captured & Verified (`rfl`)** | **Captured & Verified (`rfl`)** | `0->1, 1->2, 41->42, MAX-1->MAX, MAX->MAX` |
| Dead-branch `const { 1 / 0 }` | `if false { const { 1 / 0 } }` under `--emit=metadata` | Refused (`required_consts`) | **Rejected at capture (`unsupported`, CTFE error)** | **Rejected at capture (`unsupported`, CTFE error)** | Soundly refused via `const_eval_resolve` |

Basis: **source** and **execution** ([`support/run_track_b_experiments.py`](support/run_track_b_experiments.py), [`support/track_b_verification_receipts.json`](support/track_b_verification_receipts.json)).

## Boundaries

- **Known not to apply (`-C overflow-checks=yes` vs. `-C overflow-checks=no`)**: Anneal's capture pipeline pins `-C debug-assertions=off -C overflow-checks=no`, under which `rustc` lowers `+`, `-`, `*`, and unary `-` on integers to non-checked `BinaryOp` / `UnOp::Neg` in `Runtime(PostCleanup)` MIR. Under `-C overflow-checks=yes` (or explicit `checked_add`), `rustc` emits `CheckedBinaryOp` returning `(T, bool)` and an `Assert` terminator.
- **Known not to apply (bidirectional equivalence for `#[custom_mir]` post-move reads of `Copy` types)**: While `Anneal Verified` implies `Rust/Miri UB-free`, the converse does not hold for hand-written `#[custom_mir]` bodies that read a `Copy` local after `Operand::Move` without re-initialization (`c19_custom_mir_move_copy_reuse`), because Anneal's `evalOperand` conservatively deinitializes the source slot on `.move`.
- **Not examined (128-bit integers `i128`/`u128`, floats, and payload-bearing enums)**: `Word := BitVec 64` bounds scalar widths to `bits ∈ {8, 16, 32, 64}`; `i128`/`u128`, IEEE-754 floats, and payload-bearing ADTs require multi-word or aggregate slot representations beyond the 64-bit scalar word model.

## Evidence

All reproducible harnesses, `rustc_driver` probes, and machine-readable JSON receipts are preserved under `support/`:

1. **Four-Way Differential Execution Harness and Results**:
   - [`support/run_differential_harness.py`](support/run_differential_harness.py) and [`support/differential_results.json`](support/differential_results.json).
2. **`DefKind::AnonConst` / `DefKind::InlineConst` Taxonomy and `--emit=metadata` CTFE Probe**:
   - [`support/anon_const_and_capture_probe.rs`](support/anon_const_and_capture_probe.rs) and [`support/anon_const_taxonomy_results.json`](support/anon_const_taxonomy_results.json).
3. **Phase 1 & Phase 2 Capture-vs-`bodyWF` Alignment and `UnaryOp` Verification Harness**:
   - [`support/run_track_b_experiments.py`](support/run_track_b_experiments.py) and [`support/track_b_verification_receipts.json`](support/track_b_verification_receipts.json).

## Revalidation

1. **Four-Way Differential Execution**:
   - Run `python3 support/run_differential_harness.py` against the pinned Anneal toolchain (`rustc 1.98.0-nightly`, `miri`, `lean 4.34.1`, and `cargo-anneal`) and verify `0` semantic mismatches across all admitted vectors and `6/6` seeded-error detections in `support/differential_results.json`.
2. **`AnonConst` Taxonomy and Dead-Branch `InlineConst` CTFE Check**:
   - Compile `support/anon_const_and_capture_probe.rs` against `librustc_driver` and verify that panicking/div-by-zero enum discriminants fail before `Callbacks::after_analysis` while dead-branch `if false { const { 1 / 0 } }` is caught by `tcx.const_eval_resolve` over `body.required_consts`.
3. **Phase 1 and Phase 2 Capture Alignment**:
   - Run `python3 support/run_track_b_experiments.py` and verify that all 10 former refusals plus Starnix's `verifier::saturating_inc_u32` match `support/track_b_verification_receipts.json`.
