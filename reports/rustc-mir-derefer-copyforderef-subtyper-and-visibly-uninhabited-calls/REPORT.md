# `rustc` Phase-Transition Required MIR Desugarings: `Derefer`, `EraseDerefTemps`, `Subtyper`, and `LintAndRemoveUninhabited`

## Summary

Four mandatory `rustc` MIR transformation passes (`PassPolicy::Required`) establish load-bearing structural, aliasing, typing, and control-flow invariants across the `Built -> Analysis(Initial) -> Analysis(PostCleanup) -> Runtime(Initial) -> Runtime(PostCleanup)` phase transitions:

1. **`Derefer` + `EraseDerefTemps` (`CopyForDeref` -> `Rvalue::Use(Operand::Copy(_), WithRetag::No)`):**
   - `Derefer` (`compiler/rustc_mir_transform/src/deref_separator.rs:1-109`), running at the end of `run_analysis_cleanup_passes` (`MirPhase::Analysis(AnalysisPhase::PostCleanup)`), rewrites every non-`VarDebugInfo` place containing `ProjectionElem::Deref` at index `>= 1` (`place.projection[1..].contains(&ProjectionElem::Deref)`) into a chain of synthetic temporaries marked `LocalInfo::DerefTemp` and assigned via `Rvalue::CopyForDeref(deref_place)`. After `Derefer`, `ProjectionElem::Deref` appears only as `projection[0]` outside `VarDebugInfo`.
   - `LocalInfo::DerefTemp` and `Rvalue::CopyForDeref` exist solely as an intermediate handoff across `ElaborateDrops`: `rustc_mir_dataflow`'s `move_paths::builder` (`move_paths/builder.rs:33-35, 388-397, 408-411`) excludes `DerefTemp` locals from `MovePath` allocation and records an `un_derefer` reverse map so drop elaboration sees through the split projection chain.
   - `EraseDerefTemps` (`compiler/rustc_mir_transform/src/erase_deref_temps.rs:1-46`), running after `ElaborateDrops` and `AddMovesForPackedDrops` immediately before `MirPhase::Runtime(RuntimePhase::Initial)`, resets `LocalInfo::DerefTemp` to `LocalInfo::Boring` and lowers `Rvalue::CopyForDeref(place)` to `Rvalue::Use(Operand::Copy(place), WithRetag::No)` (pretty-printed as `no_retag copy`).
   - Emitting `WithRetag::No` (`RetagMode::None` in `rustc_const_eval/src/interpret/step.rs:179-184`, returning `None` in both `sb_retag_ptr_value` and `tb_retag_ptr_value`) is **aliasing-critical**. Live Miri differential execution and kernel-checked Lean 4 proofs establish that replacing `WithRetag::No` with `WithRetag::Yes` on split-field `&mut &mut (u32, u32)` raw-pointer accesses (`p0 = &raw mut (*(*pp)).0; *p0 = 11; p1 = &raw mut (*(*pp)).1; *p1 = 22; *p0 = *p0 + *p1`) causes immediate Undefined Behavior under **both** aliasing models, at different statements: **Stacked Borrows** aborts on the read `*p0` (the second `Unique` retag over `[0x0..0x8]` pops `p0`'s `SharedReadWrite` tag on `[0x0..0x4]`), whereas **Tree Borrows** allows the read and aborts on the write `*p0 = v0 + v1` (the second reborrow acts as a foreign read over `[0x0..0x8]`, transitioning the first tag from `Unique`/`Active` to `Frozen`).

2. **`Subtyper` (`CastKind::Subtype` Region-Erased HRTB Projection Normal Form):**
   - `Subtyper` (`compiler/rustc_mir_transform/src/add_subtyping_projections.rs:1-73`), running immediately after `PostAnalysisNormalize` (and `CriticalCallEdges`) at the `Analysis(PostCleanup) -> Runtime(Initial)` boundary, inspects every `StatementKind::Assign((place, rvalue))` except `rvalue.is_generic_reborrow()` (`Rvalue::Reborrow`) and `DerefTemp` destinations.
   - It computes `place_ty = tcx.erase_and_anonymize_regions(place.ty(...))` and `rval_ty = tcx.erase_and_anonymize_regions(rvalue.ty(...))`. Ordinary free-region variance (`&'static u8` assigned to `&'a u8`) becomes structurally equal after region erasure (`&u8 == &u8`) and receives **zero** casts. Whenever higher-ranked binder structure differs after region erasure (for example, `(for<'a> fn(&'a u8) -> &'a u8, u32)` coerced to `(fn(&'static u8) -> &'static u8, u32)` or `for<'a, 'b> fn(&'a u8, &'b u8) -> &'a u8` coerced to `for<'c> fn(&'c u8, &'c u8) -> &'c u8`), `Subtyper` inserts `temp = rval; place = move temp as place_ty (CastKind::Subtype)`.
   - Operationally, `CastKind::Subtype` is a layout-size-checked, representation-preserving value identity (`rustc_const_eval/src/interpret/cast.rs:192-200`) that makes higher-ranked type changes explicit so downstream optimizations (`CopyProp`, `GVN`), trait selection, and `TypeId::of` do not conflate distinct higher-ranked types (`TypeId::of::<for<'a> fn(&'a u8) -> &'a u8>() != TypeId::of::<fn(&'static u8) -> &'static u8>()`).
   - **Important validator subtlety uncovered by source inspection and live execution:** Although `validate.rs:609-617` switches `mir_assign_valid_types` from `Variance::Covariant` to `Variance::Invariant` at `MirPhase::Runtime(RuntimePhase::Initial)`, `rustc_const_eval/src/util/compare_types.rs:34` constructs its `InferCtxt` with `.ignoring_regions()` and never runs a leak check or region-constraint solver (`validate.rs:592`: *"This is not precise, it will accept some incorrect assignments"*). Consequently, disabling `Subtyper` (`-Zvalidate-mir -Zmir-enable-passes=-Subtyper` on `1.98.0-nightly`) does **not** trigger a `validate.rs` ICE on higher-ranked function-pointer assignments (even though disabling `Derefer` or `EraseDerefTemps` immediately ICEs `validate.rs`), while `CopyProp` propagates the uncast local into debuginfo (`debug g => _1`). Verified MIR consumers that enforce strict structural type equality on `Assign` therefore depend directly on `Subtyper`, not on `validate.rs` alone.

3. **`LintAndRemoveUninhabited` (Module-Scoped `is_inhabited_from` Call-Return Pruning & Definite-Init `E0381` Gate):**
   - `LintAndRemoveUninhabited` (`compiler/rustc_mir_transform/src/lint_and_remove_uninhabited.rs:1-139`), running first in `mir_built` **before** `mir_borrowck` (and inlined inside `rustc_mir_build::builder::Builder::lint_and_remove_uninhabited` in `1.98.0-nightly`), removes the normal return edge `TerminatorKind::Call { target: Some(bb) -> None }` if and only if `!ty.is_inhabited_from(tcx, parent_module, typing_env)`.
   - `rustc` maintains a strict three-tier inhabitedness hierarchy (`compiler/rustc_middle/src/ty/inhabitedness/mod.rs:1-408`):
     `!is_inhabited_from(ty, M)` $\implies$ `is_privately_uninhabited(ty)` $\implies$ `!is_opsem_inhabited(ty)`.
     - Publicly uninhabited types (`pub enum PublicVoid {}`, `!`) satisfy `!is_inhabited_from`, so `target` becomes `None`; borrowck sees the post-call block as unreachable and accepts `let x: u32; make_pub_void(); x` (`rc = 0`, emitting `UNREACHABLE_CODE` / `UnreachableDueToUninhabited` unless the enclosing function's own return type is visibly uninhabited, per rust-lang/rust#149571).
     - Privately uninhabited structs (`pub struct OpaqueUninhabited(PrivateVoid)`) wrap private fields in `InhabitedPredicate::NotInModule(def_mod).or(pred)` (`inhabitedness/mod.rs:124`). From outside `def_mod`, `is_inhabited_from` returns `true`, `target` remains `Some(bb)`, and borrowck rejects `let x: u32; m::make_priv_void(); x` with `error[E0381]: used binding 'x' isn't initialized` (`rc = 1`). Inside `def_mod` and its child submodules (`m::child`), `NotInModule(def_mod)` is `false`, so `target` is pruned (`rc = 0`). This enforces **SemVer monotonicity**: evolving a private uninhabited field into an inhabited type (e.g., `u32`) cannot break downstream crates' definite initialization.
     - Operational-semantics uninhabited references (`&'static PublicVoid`, `&'static !`) strictly separate Tier 1 from Tier 3: `inhabitedness/mod.rs:166` maps references to `InhabitedPredicate::True` (`is_inhabited_from == true`, keeping `target = Some(bb)` and triggering `E0381`), even though `is_opsem_inhabited` recurses through references (`mod.rs:300-308`) and returns `false`.
   - Because `!is_inhabited_from` implies `!is_opsem_inhabited`, no valid return value of the callee's type can exist; pruning `target` to `None` (which raises `throw_ub!(Unreachable)` in `eval_context.rs:525-531` if a callee ever returned) never introduces UB on valid executions.

4. **Downstream Verification Boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`) & Mechanization:**
   - `joshlf/anneal` targets `Runtime(PostCleanup)` MIR in `Trusted.MirAst`: it relies on `Derefer` + `EraseDerefTemps` having eliminated `CopyForDeref` (even using `.CopyForDeref ⟨0, Array.empty⟩` in `Trusted/Correspondence.lean:1505` as a fail-closed sentinel for `.unsupported`), admits `.use` only when retagging is a no-op (`WithRetag::No` or ref/box-free scalars/enums), rejects `WithRetag::Yes` on references/boxes and all `Rvalue::Cast` (including `CastKind::Subtype`) fail-closed to `.unsupported`, and models `TerminatorKind::Call` with `target : Option BasicBlockId` (currently fail-closed `.fault .unsupported` in `MirSemantics.lean:1568`).
   - All three desugarings are mechanized in a standalone, kernel-checked Lean `v4.34.1` module (`support/DereferCopyForDerefSubtyperAndVisiblyUninhabitedSoundness.lean`, `1,769` lines, `19` core theorems + capstone, `0` errors/warnings under `-DwarningAsError=true -DElab.async=false -Ddebug.skipKernelTC=false`, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, and `0` `._unsafe_rec` constants).

---

## Applicability

### Studied Subjects and Their Relationships

This report combines primary-source inspection across three revisions of `rust-lang/rust`, normative rules from `rust-lang/reference`, live compiler and Miri execution, downstream trusted-boundary inspection of `joshlf/anneal`, and standalone kernel-checked mechanization in `Lean 4`:

| Subject | Repository & Immutable Revision | Role in Report |
| :--- | :--- | :--- |
| **`rustc` (HEAD)** | `rust-lang/rust` @ `ce66487ebbd7541212d22d01c39a808057d69f1f` | Primary upstream source authority for `deref_separator.rs`, `erase_deref_temps.rs`, `add_subtyping_projections.rs`, `lint_and_remove_uninhabited.rs`, `lib.rs`, `pass_manager.rs`, `validate.rs`, `syntax.rs`, `inhabitedness/mod.rs`, `inhabited_predicate.rs`, `rustc_const_eval/src/interpret/{step,cast,eval_context}.rs`, `compare_types.rs`, `move_paths/builder.rs`, and `src/tools/miri/src/borrow_tracker/{mod,stacked_borrows/mod,tree_borrows/mod}.rs`. |
| **`rustc` (`1.102.0-nightly`)** | `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | Cross-checked against HEAD (`ce66487e`): byte-for-byte identical in all four pass files and `syntax.rs`; differs in `lib.rs` on `PostAnalysisNormalize` phase placement (`run_runtime_lowering_passes` vs end of `run_analysis_cleanup_passes`). |
| **`rustc` & `Miri` (`1.98.0-nightly`)** | `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `miri 0.1.0 (14210df0e2 2026-05-31)`) | Live execution subject (`x86_64-unknown-linux-gnu`, Edition 2024) for all MIR dumps, `-Zvalidate-mir` checks, Miri Stacked Borrows and Tree Borrows runs, `custom_mir` `WithRetag::Yes` UB counterexamples, and `E0381` definite-init probes. |
| **The Rust Reference** | `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Normative rules for subtyping (`r[subtype.kinds]`, `r[subtype.higher-ranked]`, `r[subtyping.variance]`), never type (`r[type.never]`), and enumerated types (`r[type.enum]`). |
| **Anneal** | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Downstream formal-verification consumer of `Runtime(PostCleanup)` MIR (`trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/correspondence/Trusted/Correspondence.lean`, `trusted/rustc-capture/src/driver.rs`). |
| **Lean 4** | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Proof kernel checking `support/DereferCopyForDerefSubtyperAndVisiblyUninhabitedSoundness.lean`. |

### Cross-Revision Equivalence vs. Version-Specific Differences (`14210df0e` vs. `3ef0c22cd` vs. `ce66487eb`)

Direct byte-level diffs across all three `rust-lang/rust` commits establish exactly which behaviors are shared and which changed:

| Component | `14210df0e` (`1.98.0-nightly`) | `3ef0c22cd` (`1.102.0-nightly`) | `ce66487eb` (HEAD) |
| :--- | :--- | :--- | :--- |
| **`Derefer` algorithm (`deref_separator.rs`)** | Identical splitting logic (`DerefTemp` + `CopyForDeref`; `WithRetag::No` when `add_deref_metadata == false`); `fn is_required(&self) -> bool { true }` | Byte-for-byte identical to HEAD (`109` lines); `PassPolicy::Required` | `109` lines; `PassPolicy::Required` |
| **`EraseDerefTemps` algorithm (`erase_deref_temps.rs`)** | Identical lowering (`CopyForDeref(place)` -> `Rvalue::Use(Operand::Copy(place), WithRetag::No)`, `DerefTemp` -> `Boring`); `is_required() -> true` | Byte-for-byte identical to HEAD (`46` lines); `PassPolicy::Required` | `46` lines; `PassPolicy::Required` |
| **`Subtyper` algorithm (`add_subtyping_projections.rs`)** | Identical (`erase_and_anonymize_regions`, skips `is_generic_reborrow` & `is_deref_temp`, inserts temp + `CastKind::Subtype`); `is_required() -> true` | Byte-for-byte identical to HEAD (`73` lines); `PassPolicy::Required` | `73` lines; `PassPolicy::Required` |
| **Pass override enforcement (`pass_manager.rs`)** | `should_run_pass` (L214–240) checks `-Zmir-enable-passes` override **before** `is_required()`, so `-Zmir-enable-passes=-Derefer` disables `Derefer` and triggers `validate.rs` ICEs. | `should_run_pass` (L256–285) matches `PassPolicy::Required => true` **before** consulting `-Zmir-enable-passes`, making required passes un-disableable. | Identical `PassPolicy::Required => true` enforcement. |
| **`PostAnalysisNormalize` placement (`lib.rs`)** | Start of `run_runtime_lowering_passes` (L631), right before `Subtyper` (L633). | Start of `run_runtime_lowering_passes` (L660), right before `Subtyper` (L664). | End of `run_analysis_cleanup_passes` (L655), right after transitioning to `Analysis(PostCleanup)` and still immediately preceding `CriticalCallEdges` + `Subtyper` (L662–664). |
| **Uninhabited call-return pruning** | Inline inside `rustc_mir_build::builder::Builder::lint_and_remove_uninhabited` (`compiler/rustc_mir_build/src/builder/mod.rs:825-936`), using the exact same `ty.is_inhabited_from(...)`, `*target = None`, and issue #149571 enclosing-return guard. | Extracted into dedicated pass `compiler/rustc_mir_transform/src/lint_and_remove_uninhabited.rs` (`139` lines), run first in `mir_built` (`lib.rs:418`) with `PassPolicy::Required`. | Byte-for-byte identical to `3ef0c22cd` (`139` lines). |

### Configuration and Scope Boundaries

- All live executions use `--edition=2024` on `x86_64-unknown-linux-gnu` with default panic strategy (`unwind`), default MIR validation (`-Zvalidate-mir` explicitly enabled where noted), and Miri under both default Stacked Borrows and `MIRIFLAGS="-Zmiri-tree-borrows"`.
- Findings for `Derefer`, `EraseDerefTemps`, `Subtyper`, and `LintAndRemoveUninhabited` apply to non-trivial-const MIR bodies processed through `mir_built` and `mir_drops_elaborated_and_const_checked` (`lib.rs:395-698`). Trivial consts (`lib.rs:403-408`) and synthetic ADT constructors (`lib.rs:507-513`) bypass these pipelines.
- The standalone Lean 4 mechanization models the abstract phase-transition algorithms, Tree Borrows / Stacked Borrows transitions, region-erased HRTB types, and module-parametric `InhabitedPredicate` lattice; it does **not** import `joshlf/anneal`'s `Trusted.MirSemantics` or `vendor/lean-miri` (see **Boundaries**).

---

## Findings

### 1. Required Phase-Transition Pipeline Architecture (`PassPolicy::Required`)

Basis: `source` (`rust-lang/rust@ce66487eb`, `3ef0c22cd`, `14210df0e`: `compiler/rustc_mir_transform/src/{lib.rs,pass_manager.rs}`) + `execution` (`support/probe_derefer_subtyper_and_visibly_uninhabited.py`)

In `rust-lang/rust` (`ce66487eb`, `compiler/rustc_mir_transform/src/pass_manager.rs:88-100, 256-285`), MIR passes declare their enablement contract through `PassPolicy`:

```rust
pub(crate) enum PassPolicy {
    /// This pass implements a mandatory lowering step, either to implement parts of the MIR semantics
    /// or to bring MIR into a shape that is easier to deal with for later passes/codegen.
    /// Passes using this cannot be disabled via any means. They must not remove any UB, as they will
    /// run in Miri. They must also come with a comment justifying why they must always run.
    Required,
    Optional { enabled_by_default: bool },
}
```

In `should_run_pass` (`pass_manager.rs:270-284`), `PassPolicy::Required => true` short-circuits **before** reading `-Zmir-enable-passes`, fixing the earlier `1.98.0-nightly` (`14210df0e`, `pass_manager.rs:228-240`) loophole where `overridden.unwrap_or_else(...)` evaluated `-Zmir-enable-passes` before `pass.is_required()`.

The four audited `PassPolicy::Required` passes occupy fixed positions across the five MIR phases (`lib.rs:412-698`):

```text
mir_built (MirPhase::Built)
  ├─ [1] LintAndRemoveUninhabited   (PassPolicy::Required, lib.rs:418)  <-- BEFORE mir_borrowck!
  ├─ MIR lints + SimplifyCfg::Initial + SanityCheck
  ▼
mir_promoted -> MirPhase::Analysis(AnalysisPhase::Initial)               (lib.rs:485)
  ├─ mir_borrowck (runs on Analysis(Initial) MIR; definite-init E0381 sees pruned Call targets!)
  ▼
run_analysis_cleanup_passes -> MirPhase::Analysis(AnalysisPhase::PostCleanup) (lib.rs:642-656)
  ├─ ImpossibleClauses -> CleanupPostBorrowck -> RemoveNoopLandingPads -> SimplifyCfg::PostAnalysis
  ├─ [2] Derefer                    (PassPolicy::Required, lib.rs:648)  <-- splits projection[1..].Deref
  ├─ phase change -> Analysis(PostCleanup)                              (lib.rs:651)
  ├─ PostAnalysisNormalize          (PassPolicy::Required, lib.rs:655)  <-- reveals opaques
  ▼
run_runtime_lowering_passes -> MirPhase::Runtime(RuntimePhase::Initial)  (lib.rs:659-681, no_validate)
  ├─ CriticalCallEdges
  ├─ [3] Subtyper                   (PassPolicy::Required, lib.rs:664)  <-- explicit CastKind::Subtype
  ├─ ElaborateDrops                 (uses LocalInfo::DerefTemp + CopyForDeref via un_derefer!)
  ├─ CheckDropRecursion -> AbortUnwindingCalls -> AddMovesForPackedDrops
  ├─ [4] EraseDerefTemps            (PassPolicy::Required, lib.rs:675)  <-- CopyForDeref -> WithRetag::No
  ├─ ElaborateBoxDerefs -> coroutine::StateTransform (calls deref_finder(_, _, false) at L977)
  ├─ phase change -> Runtime(Initial)                                   (lib.rs:680)
  ▼
run_runtime_cleanup_passes -> MirPhase::Runtime(RuntimePhase::PostCleanup) (lib.rs:684-698)
  ├─ LowerIntrinsics -> RemovePlaceMention -> SimplifyCfg::PreOptimizations
  ├─ phase change -> Runtime(PostCleanup) + validate_body               (lib.rs:691)
  └─ clear all local_decl.local_info = ClearCrossCrate::Clear           (lib.rs:695-697)
```

Notice two architectural constraints visible directly from this sequence:
1. **`run_runtime_lowering_passes` uses `pm::run_passes_no_validate` (`lib.rs:680`)** because intermediate steps between `Analysis(PostCleanup)` and `Runtime(Initial)` temporarily violate invariants of both dialects (for example, `Subtyper` inserts `CastKind::Subtype` while `DerefTemp`/`CopyForDeref` are still live for `ElaborateDrops`, and `EraseDerefTemps` removes `CopyForDeref` before `ElaborateBoxDerefs` and `Runtime(Initial)` validation).
2. **All `PassPolicy::Required` passes run inside Miri** (`pass_manager.rs:91-92`: *"They must not remove any UB, as they will run in Miri"*), which means every transformation here is part of the **operational semantics boundary** of Rust MIR — not an optional backend optimization.

---

### 2. `Derefer` + `EraseDerefTemps`: Projection Normalization and `WithRetag::No` Aliasing Preservation

Basis: `source` (`deref_separator.rs:1-109`, `erase_deref_temps.rs:1-46`, `move_paths/builder.rs:29-42, 388-412`, `validate.rs:653, 956-995, 1028-1032, 1501-1507, 1669-1679`, `syntax.rs:308-340, 490-505, 1456-1466`, `mir/pretty.rs:1153-1156, 1205`, `interpret/step.rs:179-186`, `miri/src/borrow_tracker/{mod.rs:281-294, stacked_borrows/mod.rs:858-886, tree_borrows/mod.rs:126-135, 474-504}`, `coroutine/mod.rs:977`) + `execution` (`support/probe_derefer_subtyper_and_visibly_uninhabited.{py,json}`) + `derived` (Lean Theorems 1–7)

#### 2.1 Exact `Derefer` Algorithm and `VarDebugInfo` Exclusion

In `compiler/rustc_mir_transform/src/deref_separator.rs:23-81`, `DerefChecker::visit_place` triggers if and only if all three conditions hold:

```rust
if !place.projection.is_empty()
    && cntxt != PlaceContext::NonUse(VarDebugInfo)
    && place.projection[1..].contains(&ProjectionElem::Deref)
```

When triggered:
1. It locates `last_deref_idx` — the rightmost index `idx` in `place.projection` where `*elem == ProjectionElem::Deref` (`deref_separator.rs:32-36`).
2. It walks `(idx, (p_ref, p_elem))` over `place.iter_projections().enumerate()` (`deref_separator.rs:38-79`). Whenever `!p_ref.projection.is_empty() && p_elem == ProjectionElem::Deref`:
   - It computes `ty = p_ref.ty(self.local_decls, self.tcx).ty` and allocates a fresh local `temp` via `patcher.new_local_with_info(ty, span, LocalInfo::DerefTemp)` (when `add_deref_metadata == true`; `LocalInfo::Boring` when `false`).
   - It constructs `deref_place = Place::from(place_local).project_deeper(&p_ref.projection[last_len..], self.tcx)`. Because `last_len` starts at `0` and advances to `p_ref.projection.len()` at each non-leading deref, `p_ref.projection[last_len..]` begins with at most one leading `Deref` followed exclusively by non-`Deref` projections (`Field`, `Downcast`, `Index`, etc.).
   - It inserts before `loc`:
     - `temp = Rvalue::CopyForDeref(deref_place)` when `add_deref_metadata == true` (`Derefer::run_pass`, line 102); or
     - `temp = Rvalue::Use(Operand::Copy(deref_place), WithRetag::No)` when `add_deref_metadata == false` (invoked by `coroutine/mod.rs:977` inside `StateTransform`, after `EraseDerefTemps` has already run).
   - It advances `place_local = temp; last_len = p_ref.projection.len()`.
   - When `idx == last_deref_idx`, it overwrites `*place = Place::from(temp).project_deeper(&place.projection[idx..], self.tcx)`, whose leading element is `place.projection[last_deref_idx] == ProjectionElem::Deref` and whose tail `place.projection[last_deref_idx + 1..]` contains **zero** `Deref` elements.

**Why `VarDebugInfo` is excluded (`deref_separator.rs:25` & `validate.rs:958`):** Debuginfo mappings (`debug var => (*(*_1)).0`) are metadata, not runtime operations. Inserting runtime `CopyForDeref` temporaries for debuginfo would alter runtime control/dataflow and diverge debug vs. non-debug builds; therefore both `Derefer` and `validate.rs:956-965` explicitly exempt `PlaceContext::NonUse(NonUseContext::VarDebugInfo)`.

#### 2.2 Why `CopyForDeref` + `LocalInfo::DerefTemp` Must Bridge `Derefer` to `EraseDerefTemps`

Between `Derefer` (`lib.rs:648`) and `EraseDerefTemps` (`lib.rs:675`), `ElaborateDrops` (`lib.rs:665`) computes initialization and drop-flag dataflow via `rustc_mir_dataflow::move_paths::builder`:

- **`move_paths/builder.rs:33-35`:** Skips creating any `MovePath` for locals where `l.is_deref_temp()` returns `true`.
- **`move_paths/builder.rs:388-397`:** On `StatementKind::Assign((place, Rvalue::CopyForDeref(reffed)))`, asserts `self.body.local_decls[local].is_deref_temp()`, inserts `(local, reffed.as_ref())` into `rev_lookup.un_derefer`, and aliases `rev_lookup.locals[local] = rev_lookup.locals[base_local]` so move/init/drop tracking resolves through the synthetic temporary back to the original nested projection path.
- **`move_paths/builder.rs:407-412`:** On `StorageDead(local)`, skips `gather_move` if `is_deref_temp()`, because `DerefTemp` locals do not own or move the borrowed value.

Until `Runtime(Initial)`, `validate.rs` enforces four tight structural contracts on `DerefTemp` and `CopyForDeref`:
- `validate.rs:982-994`: Any use of a `DerefTemp` local must either dereference it as the first projection (`place.is_indirect_first_projection()`) or be a direct `MutatingUseContext::Store` to the bare local (`place.as_local().is_some()`).
- `validate.rs:1501-1507`: Any assignment targeting a `DerefTemp` local must use `Rvalue::CopyForDeref(_)`.
- `validate.rs:1675-1679`: Before `Runtime(Initial)`, a `DerefTemp` local's type must satisfy `ty.builtin_deref(true).is_some()`.
- `validate.rs:1028-1032, 1669-1674`: Once `phase >= MirPhase::Runtime(RuntimePhase::Initial)`, BOTH `Rvalue::CopyForDeref` and `LocalInfo::DerefTemp` are forbidden (ICE: `` "`CopyForDeref` should have been removed in runtime MIR" `` and `` "`DerefTemp` should have been removed in runtime MIR" ``).

#### 2.3 `EraseDerefTemps` and the `WithRetag::No` Aliasing Necessity

`EraseDerefTemps` (`compiler/rustc_mir_transform/src/erase_deref_temps.rs:19-33`) performs two surgical mutations:

```rust
fn visit_rvalue(&mut self, rvalue: &mut Rvalue<'tcx>, _: Location) {
    if let &mut Rvalue::CopyForDeref(place) = rvalue {
        // We do *NOT* want a retag here! This assignment might copy a mutable reference we
        // can't actually copy, we just need it temporarily to create another pointer.
        *rvalue = Rvalue::Use(Operand::Copy(place), WithRetag::No)
    }
}

fn visit_local_decl(&mut self, _: Local, local_decl: &mut LocalDecl<'tcx>) {
    if local_decl.is_deref_temp() {
        let info = local_decl.local_info.as_mut().unwrap_crate_local();
        **info = LocalInfo::Boring;
    }
}
```

Two non-obvious invariants interact here:
1. **`Operand::Copy` on non-`Copy` `&mut T` / `Box<T>`:** Notice that `deref_place` frequently has type `&mut T` (which does **not** implement `Copy`!). In `Analysis` phases, `validate.rs:652-661` rejects `Operand::Copy(place)` for non-`Copy` types (`if !self.tcx.type_is_copy_modulo_regions(...)`). Crucially, that check is gated by `self.body.phase < MirPhase::Runtime(RuntimePhase::Initial)` (`validate.rs:653`). Because `EraseDerefTemps` runs inside `run_runtime_lowering_passes` (`run_passes_no_validate`) right before transitioning to `Runtime(Initial)`, `Rvalue::Use(Operand::Copy(place), WithRetag::No)` on `&mut T` is valid in `Runtime` MIR.
2. **Operational meaning of `WithRetag::No` vs. `WithRetag::Yes`:**
   - In `compiler/rustc_middle/src/mir/syntax.rs:314-316`, `StatementKind::Assign` documents that ordinary assignments *"implicitly 'retag' all references and boxes that it copies, meaning that the resulting value is not an exact duplicate for all intents and purposes of the original value."*
   - `compiler/rustc_middle/src/mir/pretty.rs:1153-1156` prints `Rvalue::Use(op, WithRetag::No)` with the prefix `no_retag ` (`_7 = no_retag copy (*_1);`) and omits any prefix for `WithRetag::Yes` (`_2 = copy (*_1);`).
   - In `compiler/rustc_const_eval/src/interpret/step.rs:179-186`:
     ```rust
     Use(ref operand, with_retag) => {
         let op = self.eval_operand(operand, Some(dest.layout))?;
         let mode = if with_retag.yes() { RetagMode::Default } else { RetagMode::None };
         M::with_retag_mode(self, mode, |ecx| ecx.copy_op(&op, &dest))?;
     }
     CopyForDeref(_) => bug!("`CopyForDeref` in runtime MIR"),
     ```
   - In Miri's borrow trackers:
     - **Stacked Borrows** (`src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs:869`): `RetagMode::None => return interp_ok(None)` — skips `sb_retag_place` completely, preserving the copied pointer's exact `BorTag` and leaving every borrow stack untouched. Under `RetagMode::Default`, `sb_retag_place` performs a **`Unique` retag across the full pointee size**, popping incompatible tags above the parent!
     - **Tree Borrows** (`src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:132-134`): `if mode == RetagMode::None { return None; }` inside `NewPermission::new` — skips `tb_retag_place` completely, creating no child node and performing no foreign read. Under `RetagMode::Default`, `tb_retag_place` creates a fresh child tag in `Reserved` and executes a **foreign read across the full pointee size**, transitioning any active sibling tag from `Unique` (`Active`) to `Frozen`!

#### 2.4 Live `rustc` MIR Dumps and Miri SB/TB Counterexample (`WithRetag::No` vs. `WithRetag::Yes`)

Executing `support/probe_derefer_subtyper_and_visibly_uninhabited.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `miri 0.1.0 (14210df0e2 2026-05-31)` yields exact empirical confirmation across both 2-level (`nested_mut_raw_split`) and 3-level (`nested_mut_triple_deref`) nested `&mut` dereferences, plus a direct `custom_mir` aliasing discriminator:

1. **Multi-level `Derefer` -> `EraseDerefTemps` counts (`support/probe_derefer_subtyper_and_visibly_uninhabited.json`):**
   - `nested_mut_raw_split(&mut &mut (u32, u32))`:
     - Before `Derefer`: `2` nested `(*(*` statements (`&raw mut (*(*pp)).0` and `&raw mut (*(*pp)).1`).
     - After `Derefer`: `0` nested `(*(*` statements, `2` `deref_copy` assignments (`_7 = deref_copy (*_1);`, `_8 = deref_copy (*_1);`).
     - After `EraseDerefTemps` and in `Runtime(PostCleanup)`: `0` `deref_copy` assignments, `2` `no_retag copy` assignments (`_7 = no_retag copy (*_1);`, `_8 = no_retag copy (*_1);`).
   - `nested_mut_triple_deref(&mut &mut &mut (u32, u32))`:
     - Before `Derefer`: `8` nested `(*(*(*` places across `+= 5`, `+= 7`, and `+`.
     - After `Derefer`: `0` nested derefs, `16` chained `deref_copy` assignments (`_7 = deref_copy (*_1); _8 = deref_copy (*_7); ... _21 = deref_copy (*_1); _22 = deref_copy (*_21);` — 2 temporaries per 3-level place).
     - After `EraseDerefTemps`: `0` `deref_copy`, `16` chained `no_retag copy` assignments (`_7 = no_retag copy (*_1); _8 = no_retag copy (*_7); ...`).
   - Native binary and Miri under **both** Stacked Borrows and Tree Borrows exit `0` with stdout `NESTED_MUT_DEREF=33 TRIPLE_DEREF=42`.

2. **Live Miri Counterexample Contrasting `WithRetag::No` vs. `WithRetag::Yes`:**
   Compare the compiler-lowered `nested_mut_raw_split` (`_7 = no_retag copy (*_1); ... _8 = no_retag copy (*_1);`) against `custom_with_retag_yes` (`#[custom_mir(dialect = "runtime", phase = "post-cleanup")]`) which has the **exact same control flow and operations** except using `WithRetag::Yes` (`_2 = copy (*_1); ... _3 = copy (*_1);`):

   ```text
   // Compiler output (WithRetag::No)           // Counterexample (WithRetag::Yes)
   _7 = no_retag copy (*_1);                    _2 = copy (*_1);
   _2 = &raw mut ((*_7).0: u32);                _4 = &raw mut ((*_2).0: u32);
   (*_2) = const 11_u32;                        (*_4) = const 11_u32;
   _8 = no_retag copy (*_1);                    _3 = copy (*_1);          <-- RETAG OVER [0x0..0x8]!
   _3 = &raw mut ((*_8).1: u32);                _5 = &raw mut ((*_3).1: u32);
   (*_3) = const 22_u32;                        (*_5) = const 22_u32;
   v0 = copy (*_2); v1 = copy (*_3);            _6 = copy (*_4);          <-- SB UB HERE!
   (*_2) = v0 + v1;                             (*_4) = Add(copy _6, copy _7);  <-- TB UB HERE!
   ```

   | Variant | Miri Stacked Borrows (`rc`) | Miri Tree Borrows (`-Zmiri-tree-borrows`, `rc`) | Exact Failure Mechanism |
   | :--- | :---: | :---: | :--- |
   | `nested_mut_raw_split` (`WithRetag::No`) | `0` (`NESTED_MUT_DEREF=33`) | `0` (`NESTED_MUT_DEREF=33`) | Copies `*pp`'s tag directly (`RetagMode::None`); zero stack pops or foreign reads. |
   | `custom_with_retag_yes` (`WithRetag::Yes`) | **`1` (UB on read `v0 = *p0`)** | **`1` (UB on write `(*p0) = v0 + v1`)** | **SB:** `<1579>` (`SharedReadWrite` at `[0x0..0x4]`) is popped by `Unique` retag over `[0x0..0x8]` at `t2 = *pp`.<br>**TB:** `<1537>` (`Reserved` -> `Unique` on `*p0 = 11`) transitions to `Frozen` due to foreign read over `[0x0..0x8]` at `t2 = *pp`; read `v0 = *p0` still succeeds, then write `(*p0) = v0 + v1` violates `Frozen`. |

3. **Live `-Zvalidate-mir` Pass-Disable Verification (on `1.98.0-nightly` `14210df0e`):**
   - `-Zvalidate-mir -Zmir-enable-passes=-Derefer` aborts with `rc = 101`: `broken MIR ... (after pass LowerIntrinsics): place (*(_24.0: &u8)) has deref as a later projection (it is only permitted as the first projection)`.
   - `-Zvalidate-mir -Zmir-enable-passes=-EraseDerefTemps` aborts with `rc = 101`: `broken MIR ... (after pass LowerIntrinsics): 'CopyForDeref' should have been removed in runtime MIR`.

4. **Mechanized Proofs (`support/DereferCopyForDerefSubtyperAndVisiblyUninhabitedSoundness.lean`, Part I):**
   - `dereferPlace_normalForm` (Theorem 1): Structural induction over arbitrary-depth projection lists proving all emitted temporaries and rewritten places satisfy `derefOnlyFirst = true` (and `LocalInfo.derefTemp` + `Rvalue.copyForDeref` when `addMeta = true`).
   - `dereferPlace_skips_varDebugInfo` (Theorem 2): `VarDebugInfo` places are preserved untouched.
   - `eraseDerefTemps_eliminates_and_preserves` (Theorem 3): Eliminates every `CopyForDeref` and `DerefTemp` while preserving `derefOnlyFirst`.
   - `derefer_then_eraseNoRetag_preserves_tree_borrows` (Theorems 4–5): Proves by structural induction on arbitrary projection depth that `Derefer` followed by `EraseDerefTemps(WithRetag::No)` resolves to the exact same value/pointer/provenance tag and leaves `heap`, `perms` (the entire Tree Borrows map), `parentOf`, and `nextTag` strictly identical.
   - `withRetagNo_succeeds_and_withRetagYes_causes_tree_borrows_ub` (Theorem 6) & `withRetagNo_succeeds_and_withRetagYes_causes_stacked_borrows_ub` (Theorem 7): Mechanize the exact SB-read-UB vs. TB-write-UB split (`runSplitRawTB .no = .ok (33, 22)`, `runSplitRawTB .yes = .ub (.frozenWriteForbidden 1 0)`, `runSplitRawSB .no = .ok (33, 22)`, `runSplitRawSB .yes = .ub (.tagMissingFromStack 2 0)`).

---

### 3. `Subtyper`: Region-Erased Higher-Ranked Subtyping Coercions and Validator Precision

Basis: `normative` (`rust-lang/reference@c9cc32825`: `src/subtyping.md`, `r[subtype.kinds]`, `r[subtype.higher-ranked]`, `r[subtyping.variance]`) + `source` (`add_subtyping_projections.rs:1-73`, `syntax.rs:1530-1540`, `mir/statement.rs:812-816`, `validate.rs:591-618, 1446-1453, 1484-1508`, `compare_types.rs:1-43`, `type_relating.rs:220-255, 275-345`, `interpret/cast.rs:37-43, 192-200`, `gvn.rs:724-732`) + `execution` (`support/probe_derefer_subtyper_and_visibly_uninhabited.{py,json}`) + `derived` (Lean Theorems 8–12)

#### 3.1 Normative Subtyping Basis and Why Region Erasure Leaves Residual Subtyping

Per *The Rust Reference* (`rust-lang/reference@c9cc32825`, `src/subtyping.md:7-36`):
- `r[subtype.kinds]`: *"Subtyping is restricted to two cases: variance with respect to lifetimes and between types with higher ranked lifetimes. If we were to erase lifetimes from types, then the only subtyping would be due to type equality."*
- `r[subtype.higher-ranked]`: *"Higher-ranked function pointers and trait objects have another subtype relation. They are subtypes of types that are given by substitutions of the higher-ranked lifetimes."* Examples include `for<'a> fn(&'a i32) -> &'a i32 <: fn(&'static i32) -> &'static i32` and `for<'a, 'b> fn(&'a i32, &'b i32) <: for<'c> fn(&'c i32, &'c i32)`.

In `rustc`'s type representation (`Ty<'tcx>`), erasing free regions (`tcx.erase_and_anonymize_regions`) collapses free lifetime parameters (`'a`, `'static`) into `ReErased`, making `&'static u8` and `&'a u8` **structurally equal** (`&u8 == &u8`). However, higher-ranked `Binder` quantifiers and their De Bruijn `ReBound` variables are **not** erased by `erase_and_anonymize_regions` — they remain structurally distinct:
- `for<'a> fn(&'a u8) -> &'a u8` has 1 bound region variable (`^0`), whereas `fn(&'static u8) -> &'static u8` erases to `fn(&'{erased} u8) -> &'{erased} u8` with 0 bound region variables.
- `for<'a, 'b> fn(&'a u8, &'b u8) -> &'a u8` has 2 bound region variables (`^0`, `^1`), whereas `for<'c> fn(&'c u8, &'c u8) -> &'c u8` has 1 bound region variable (`^0`).
- These types have **distinct `TypeId`s** and can match distinct trait implementations (which is why `syntax.rs:1537-1539` explicitly remarks: *"we only care about subtyping that can affect trait selection and `TypeId`"*).

#### 3.2 Exact `Subtyper` Algorithm (`add_subtyping_projections.rs:21-49`)

`SubTypeChecker::visit_assign` executes immediately after `PostAnalysisNormalize` (which reveals opaque types so `Subtyper` never confronts unrevealed `Opaque` aliases, `lib.rs:655, 663-664`):

```rust
fn visit_assign(
    &mut self,
    place: &mut Place<'tcx>,
    rvalue: &mut Rvalue<'tcx>,
    location: Location,
) {
    if rvalue.is_generic_reborrow() {
        return;
    }
    // We don't need to do anything for deref temps as they are
    // not part of the source code, but used for desugaring purposes.
    if self.local_decls[place.local].is_deref_temp() {
        return;
    }
    let mut place_ty = place.ty(self.local_decls, self.tcx).ty;
    let mut rval_ty = rvalue.ty(self.local_decls, self.tcx);
    // Not erasing this causes `Free Regions` errors in validator,
    // when rval is `ReStatic`.
    rval_ty = self.tcx.erase_and_anonymize_regions(rval_ty);
    place_ty = self.tcx.erase_and_anonymize_regions(place_ty);
    if place_ty != rval_ty {
        let temp = self
            .patcher
            .new_temp(rval_ty, self.local_decls[place.as_ref().local].source_info.span);
        let new_place = Place::from(temp);
        self.patcher.add_assign(location, new_place, rvalue.clone());
        *rvalue = Rvalue::Cast(CastKind::Subtype, Operand::Move(new_place), place_ty);
    }
}
```

Four implementation details are load-bearing:
1. **Two explicit skips (`lines 27-34`):**
   - `rvalue.is_generic_reborrow()` (`compiler/rustc_middle/src/mir/statement.rs:814-816`: `matches!(self, Self::Reborrow(..))`), used for generic `Reborrow`/`CoerceShared` trait coercions.
   - `self.local_decls[place.local].is_deref_temp()`, because `DerefTemp` locals are synthetic temporaries produced by `Derefer` whose assignments must remain `Rvalue::CopyForDeref` until `EraseDerefTemps` (`validate.rs:1501-1507` would ICE if `Subtyper` replaced a `DerefTemp`'s `CopyForDeref` with `Rvalue::Cast(CastKind::Subtype, ...)`!).
2. **Region erasure before comparison (`lines 39-40`):** Calling `erase_and_anonymize_regions` prevents two bugs simultaneously: (a) avoids inserting spurious `CastKind::Subtype` casts on ordinary `&'static T -> &'a T` assignments, and (b) prevents placing unerased `ReStatic` into `temp`'s `LocalDecl.ty` or the `CastKind::Subtype` target type, which would trigger `Free Regions` errors in `validate.rs`.
3. **Operational semantics of `CastKind::Subtype` (`interpret/cast.rs:37-43, 192-200`, `gvn.rs:724-732`, `syntax.rs:1530-1540`):**
   - In `rustc_const_eval/src/interpret/cast.rs:192-200`, `CastKind::Subtype` shares the same arm as `CastKind::Transmute` and `CastKind::BoxDerefTransmute`: it asserts `src.layout.is_sized()`, `dest.layout.is_sized()`, `cast_ty == dest.layout.ty`, checks `src.layout.size == dest.layout.size`, and copies the value representation unchanged while updating type metadata.
   - Because `CastKind::Subtype` is explicitly marked in the rvalue, MIR optimizations such as `CopyProp` and `GVN` cannot blindly treat `place` and `temp` as having identical `Ty<'tcx>` without traversing the cast (`gvn.rs:724`).
4. **Live execution confirmation (`support/probe_derefer_subtyper_and_visibly_uninhabited.json`):**
   - `hrtb_tuple_coerce`: `0` `(Subtype)` casts in `analysis-post-cleanup.after.mir` -> **`1`** in `Subtyper.after.mir` and `runtime-post-cleanup.after.mir`:
     ```text
     _10 = (move _4, const 7_u32);
     _3 = move _10 as (fn(&u8) -> &u8, u32) (Subtype);
     ```
   - `hrtb_binder_collapse`: `0` -> **`1`** in `Subtyper.after.mir` and `runtime-post-cleanup.after.mir`:
     ```text
     _9 = copy _3;
     _4 = move _9 as for<'a> fn(&'a u8, &'a u8) -> &'a u8 (Subtype);
     ```
   - `hrtb_typeid_split`: `0` -> **`1`** in `Subtyper.after.mir` and `runtime-post-cleanup.after.mir`:
     ```text
     _9 = copy _1;
     _2 = move _9 as fn(&u8) -> &u8 (Subtype);
     ```
     and executes natively and under Miri (`rc = 0`) printing `SUBTYPER=99 K=7 COLLAPSE=99 TYPEID_DIFF=true VAR=99`.
   - `plain_region_variance<'a>(x: &'static u8) -> &'a u8` (negative control): **`0`** `(Subtype)` casts in `analysis-post-cleanup.after.mir`, `Subtyper.after.mir`, and `runtime-post-cleanup.after.mir`.

#### 3.3 Discovered `validate.rs` vs. `compare_types.rs` Imprecision Gap

Basis: `source` (`validate.rs:591-618, 1446-1453`, `compare_types.rs:11-43`, `type_relating.rs:220-255, 322-345`) + `execution` (`support/probe_derefer_subtyper_and_visibly_uninhabited.json`)

A subtle discrepancy exists between `validate.rs`'s documented intent and its actual check when validating `StatementKind::Assign` in `MirPhase::Runtime`:
- `validate.rs:609-617` states:
  ```rust
  // After borrowck subtyping should be fully explicit via
  // `Subtype` projections.
  let variance = if self.body.phase >= MirPhase::Runtime(RuntimePhase::Initial) {
      Variance::Invariant
  } else {
      Variance::Covariant
  };
  crate::util::relate_types(self.tcx, self.typing_env, variance, src, dest)
  ```
- Under `ty::Invariant`, `compiler/rustc_infer/src/infer/relate/type_relating.rs:332-345` relates higher-ranked binders by running `enter_forall` in both directions (`exists<..> A == for<..> B` and `exists<..> B == for<..> A`), recording `make_eqregion(..., VisibleForLeakCheck::Yes)` constraints in `type_relating.rs:246-253`.
- **However**, `compiler/rustc_const_eval/src/util/compare_types.rs:34` constructs `infcx` via:
  ```rust
  let (infcx, param_env) = tcx.infer_ctxt().ignoring_regions().build_with_typing_env(typing_env);
  ```
  and returns `ocx.evaluate_obligations_error_on_ambiguity().no_errors()` without running a region solver or leak check (`validate.rs:592` explicitly caveats: *"This is not precise, it will accept some incorrect assignments"*).
- **Empirical confirmation:** Running `rustc --edition=2024 -Zvalidate-mir -Zmir-enable-passes=-Subtyper` on `1.98.0-nightly (14210df0e)` compiles `hrtb_tuple_coerce`, `hrtb_binder_collapse`, and `hrtb_typeid_split` with **`rc = 0`** (even with `-Zmir-opt-level=4`!), leaving raw uncast assignments `_3 = (move _4, const 7_u32);` and `_2 = copy _1;` in `runtime-post-cleanup.after.mir`, and allowing `CopyProp` to propagate `debug g => _1` across distinct higher-ranked types (`for<'a> fn(&'a u8) -> &'a u8` vs. `fn(&u8) -> &u8`). By contrast, disabling `Derefer` or `EraseDerefTemps` under the exact same `-Zvalidate-mir` command immediately ICEs with `rc = 101`.
- **Consequence for verified MIR consumers:** `Subtyper` (`PassPolicy::Required` in `3ef0c22cd`/`ce66487eb`), NOT `validate.rs`, is what actually guarantees exact structural `erase_and_anonymize_regions(place_ty) == erase_and_anonymize_regions(rval_ty)` on `Runtime` MIR assignments.

#### 3.4 Mechanized Soundness (`support/DereferCopyForDerefSubtyperAndVisiblyUninhabitedSoundness.lean`, Part II)

- `eraseAndAnonymize_idempotent` (Theorem 8): Idempotence of region erasure preserving De Bruijn binders.
- `isSubtype_eraseAndAnonymize` (Theorem 9): Declarative Rust subtyping (`IsSubtype`) is preserved under `eraseAndAnonymize`.
- `subtyper_explicit_cast_typing_and_eval_equiv` (Theorem 10): For any analysis-well-typed assignment (`AnalysisAssignWellTyped`, respecting `validate.rs:1501-1507` for `DerefTemp`) and fresh temporary `tmp`, `subtyperAssign` emits statements ALL satisfying strict `RuntimeAssignWellTyped` (exact structural erased-type equality on every `Assign`, plus `IsSubtype` on every `CastKind::Subtype`) AND preserving exact runtime store values at every local `k ≠ tmp`.
- `subtyper_plain_region_variance_no_cast` (Theorem 11) & `subtyper_hrtb_tuple_and_binder_collapse_insert_casts` (Theorem 12): Constructively witness `0` casts for `&'static u8 -> &'a u8`, explicit `CastKind::Subtype` insertion for both `(for<'a> fn(&'a u8) -> &'a u8, u32) -> (fn(&'static u8) -> &'static u8, u32)` and `for<'a, 'b> -> for<'c>` binder collapse, and strict erased-type inequality (`eraseAndAnonymize hrtbFn ≠ eraseAndAnonymize staticFn`).

---

### 4. `LintAndRemoveUninhabited`: Module-Scoped Inhabitedness, Call-Return Pruning, and Definite-Init SemVer Monotonicity

Basis: `normative` (`rust-lang/reference@c9cc32825`: `src/types/never.md`, `src/types/enum.md`) + `source` (`lint_and_remove_uninhabited.rs:1-139`, `lib.rs:412-432, 546-556`, `compiler/rustc_mir_build/src/builder/mod.rs:825-936` [at `14210df0e`], `inhabitedness/mod.rs:1-408`, `inhabited_predicate.rs:39-110`, `interpret/eval_context.rs:521-532`) + `execution` (`support/probe_derefer_subtyper_and_visibly_uninhabited.{py,json}`) + `derived` (Lean Theorems 13–19)

#### 4.1 Three-Tier Inhabitedness Hierarchy in `rustc_middle`

`compiler/rustc_middle/src/ty/inhabitedness/mod.rs` defines three distinct inhabitedness predicates that form a strict implication chain for normalized monomorphic types:

| Tier | Method & Location | Visibility-Scoped? | Recurses Through `&T` / `&mut T`? | Handles `#[non_exhaustive]` Foreign ADTs? | Primary Consumers |
| :--- | :--- | :---: | :---: | :---: | :--- |
| **Tier 1 (Visibly uninhabited)** | `Ty::is_inhabited_from(tcx, module, typing_env)` (`mod.rs:209-216`, `inhabited_predicate.rs:39-98`) | **Yes** (`Visibility::Restricted(from)` -> `NotInModule(from).or(pred)`, `mod.rs:124`) | **No** (`mod.rs:166`: references return `InhabitedPredicate::True`) | Treated as inhabited (`mod.rs:138-140`) | `LintAndRemoveUninhabited` (`lint_and_remove_uninhabited.rs:36`), pattern exhaustiveness |
| **Tier 2 (Privately uninhabited)** | `Ty::is_privately_uninhabited(tcx, typing_env)` (`mod.rs:222-228`, `inhabited_predicate.rs:74-80`) | **No** (`in_module = \|_\| Ok(true)`) | **No** (same `InhabitedPredicate`) | Treated as inhabited (`mod.rs:138-140`) | Internal type/layout checks ignoring local privacy |
| **Tier 3 (Opsem uninhabited)** | `Ty::is_opsem_inhabited(tcx, typing_env)` (`mod.rs:238-398`) | **No** | **Yes** (`mod.rs:300-308`, stopping at refs on cycles) | Inspects actual variants (`mod.rs:378-389`); unions always inhabited (`mod.rs:358-361`) | Layout ABI (`BackendRepr::Uninhabited`), Miri/CTFE validity, backend dead-code assumptions |

Key structural details directly from `inhabitedness/mod.rs`:
1. **Structs vs. Enums (`mod.rs:119-125`):** Inside `variant_inhabited_predicate`, `if adt.is_enum() { return pred; }` skips `Visibility` wrapping because enum variant fields inherit the enum's visibility. Only `struct` fields carry per-field `Visibility::Restricted(from)`, which wraps the field's predicate in `InhabitedPredicate::NotInModule(from).or(tcx, pred)`.
2. **Module containment (`inhabited_predicate.rs:58-70, 98`):** `NotInModule(from)` evaluates to `!in_module(from)`, where `in_module(from)` is `true` whenever `caller_mod` is equal to `from` or is a descendant submodule of `from`. Outside `from`, `NotInModule(from)` evaluates to `true`, short-circuiting the disjunction `NotInModule(from) || pred` to `true` (visibly inhabited) **regardless of what `pred` is**.
3. **Strict implication chain:** Because `apply_ignore_module` forces every `NotInModule(_)` atom to `false` (monotonic reduction of a positive Boolean formula of `And`/`Or`), and `is_opsem_inhabited` additionally recurses into references and ignores `#[non_exhaustive]`:
   $$
   \neg \text{is\_inhabited\_from}(\tau, M) \implies \text{is\_privately\_uninhabited}(\tau) \implies \neg \text{is\_opsem\_inhabited}(\tau).
   $$
   The reverse implications are **strictly false**:
   - `pub struct OpaqueUninhabited(PrivateVoid)` outside its defining module is privately (and opsem) uninhabited, yet `is_inhabited_from == true`.
   - `&'static PublicVoid` and `&'static !` are opsem-uninhabited (`is_opsem_inhabited == false`), yet `is_inhabited_from == true` in **every** module (and `is_privately_uninhabited == false`).

#### 4.2 Exact `LintAndRemoveUninhabited` Algorithm and Control-Flow / Borrowck Gate

In `compiler/rustc_mir_transform/src/lint_and_remove_uninhabited.rs:13-91` (run first in `mir_built` at `lib.rs:418`, before `SimplifyCfg::Initial` and before `mir_borrowck` at `lib.rs:553`):
1. Resolves `parent_module = tcx.parent_module_from_def_id(def_id)` and `typing_env = body.typing_env(tcx)`.
2. Computes the rust-lang/rust#149571 regression guard (`lines 21-25`):
   ```rust
   let return_ty_is_inhabited = matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
       && body.local_decls[RETURN_PLACE].ty.is_inhabited_from(tcx, parent_module, typing_env);
   ```
3. Iterates over every basic block terminator matching `TerminatorKind::Call { ref mut target, destination, .. }` with `Some(target_bb) = *target` (`lines 28-57`):
   - Computes `ty = destination.ty(&body.local_decls, tcx).ty` and `ty_is_inhabited = ty.is_inhabited_from(tcx, parent_module, typing_env)`.
   - If `!ty_is_inhabited`:
     - If `!ty.is_never() && return_ty_is_inhabited` (`line 47`; `!` is already linted during typeck), queues `(target_bb, ty, term.source_info.span)` for the `UNREACHABLE_CODE` (`UnreachableDueToUninhabited`) lint, skipping external macros (`line 60`) and skipping compiler-generated `()` / `RETURN_PLACE` / `StorageLive` / `StorageDead` / `BackwardIncompatibleDropHint` plumbing via `find_unreachable_code_from` (`lines 95-139`).
     - Unconditionally sets **`*target = None`** (`line 55`).

**Why `*target = None` gates `E0381` and why it is operationally sound:**
- **Compile-time borrowck definite-init gate:** `mir_borrowck` (`lib.rs:553`) executes on `Analysis(Initial)` MIR *after* `mir_built`. When `*target` is pruned to `None`, the post-call block `bb1` has zero reachable predecessors; borrowck's `MaybeUninitializedPlaces` analysis never reaches the use of uninitialized `x` in `bb1`, so `let x: u32; make_pub_void(); x` compiles (`rc = 0`). When `*target` remains `Some(bb1)`, `bb1` is reachable from `bb0` without initializing `x`, so borrowck emits `error[E0381]: used binding 'x' isn't initialized` (`rc = 1`).
- **SemVer monotonicity:** Because `NotInModule(def_mod)` short-circuits `is_inhabited_from` to `true` for every external module, changing `struct OpaqueUninhabited(PrivateVoid)` to `struct OpaqueUninhabited(u32)` cannot change `is_inhabited_from`, cannot restore a previously pruned CFG edge in any downstream crate, and therefore cannot turn previously compiling downstream code into an `E0381` error.
- **Operational soundness (`lint_and_remove_uninhabited.rs:88`, `eval_context.rs:525-531`):** In `rustc_const_eval/src/interpret/eval_context.rs:525-531`, `return_to_block(None)` executes `throw_ub!(Unreachable)`. As `lint_and_remove_uninhabited.rs:88` observes, *"removing the return edge would \*introduce\* UB if the call actually returned."* Because `!ty.is_inhabited_from(...)` implies `!ty.is_opsem_inhabited(...)`, no valid execution of the callee can ever construct and return a valid value of `ty` (any attempt to produce a value of `ty` is already UB by value validity). Thus pruning `target` to `None` never introduces new UB on valid executions.

#### 4.3 Live 5-Case Empirical Verification Matrix (`support/probe_derefer_subtyper_and_visibly_uninhabited.json`)

| Case | Callee Return Type & Call Site | `rustc` Exit Code | `built.after.mir` Call Terminator | `call_has_return_target` | Diagnostics |
| :--- | :--- | :---: | :--- | :---: | :--- |
| **1. `visibly_uninhabited_pub_void`** | `m::PublicVoid` called from crate root | **`0`** | `_2 = make_pub_void() -> bb2;` | **`false`** | `warning: unreachable expression` (note: `PublicVoid` is uninhabited) + `warning: unused variable: x` |
| **2. `privately_uninhabited_outside_mod`** | `m::OpaqueUninhabited(PrivateVoid)` called from crate root | **`1`** | `_2 = make_priv_void() -> [return: bb1, unwind: bb2];` | **`true`** | `error[E0381]: used binding 'x' isn't initialized` |
| **3. `privately_uninhabited_inside_mod_and_child`** | `m::OpaqueUninhabited(PrivateVoid)` called inside `m` AND inside `m::child` | **`0`** | `_2 = make_priv_void() -> bb2;` (both fns) | **`false`** | `warning: unreachable expression` + `warning: unused variable: x` (for both fns) |
| **4. `opsem_uninhabited_but_visibility_inhabited_ref`** | `&'static PublicVoid` called from crate root | **`1`** | `_2 = make_ref_void() -> [return: bb1, unwind: bb2];` | **`true`** | `error[E0381]: used binding 'x' isn't initialized` (confirms Tier 1 vs. Tier 3 separation!) |
| **5. `enclosing_uninhabited_return_lint_suppression`** | `PublicVoid` called inside `fn outer_uninh() -> PublicVoid` (issue #149571) | **`0`** | `_2 = make_pub_void() -> bb7;` | **`false`** | `warning: unused variable: x` ONLY (`unreachable expression` suppressed while pruning still runs!) |

#### 4.4 Mechanized Proofs (`support/DereferCopyForDerefSubtyperAndVisiblyUninhabitedSoundness.lean`, Part III)

- `evalPred_false_implies_ignoreMod_false` (Theorem 13), `privatelyUninhabited_implies_opsemUninhabited` (Theorem 14), and `visiblyUninhabited_implies_opsemUninhabited` (Theorem 15): Constructive proof of the full three-tier inhabitedness implication chain.
- `refNever_opsemUninhab_but_visiblyInhab` (Theorem 16): Strict separation witness for `&'static !` and `&'static PublicVoid`.
- `visiblyUninhabited_call_prune_opsem_sound` (Theorem 17): Operational equivalence (`evalCallCont pruned.target out = evalCallCont orig.target out`) over all valid callee outcomes (`CalleeOutcome` carrying `ValidVal`), proving zero introduced `ubUnreachable`.
- `visiblyUninhabited_call_prune_sound_and_semver_monotone` (Theorem 18): Jointly proves the `PublicVoid` / `OpaqueUninhabited` outside-vs.-inside/child definite-init split AND SemVer invariance under arbitrary private-field evolution (`oldField -> newField`).
- `enclosingUninhabited_suppresses_lint_preserves_pruning` (Theorem 19): Mechanizes the issue #149571 lint-suppression guard while retaining `target := none` pruning.

---

### 5. Downstream Verification Trusted Boundary Audit (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

Basis: `source` (`joshlf/anneal@c131b320e`: `trusted/lean/Trusted/MirAst.lean:53, 450-491, 557-629, 742-796`, `trusted/lean/Trusted/MirSemantics.lean:1542-1570`, `trusted/correspondence/Trusted/Correspondence.lean:1317, 1480-1506`, `trusted/rustc-capture/src/driver.rs:25, 75-84`)

Inspecting `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes the exact contract between these `rustc` phase-transition passes and Anneal's trusted MIR boundary:

1. **Capture Phase (`Runtime(PostCleanup)`):** Both `Trusted/MirAst.lean:53` and `Trusted/Correspondence.lean:1317` (`phase := .Runtime .PostCleanup`) target `Runtime(PostCleanup)` MIR — strictly **after** `LintAndRemoveUninhabited`, `Derefer`, `PostAnalysisNormalize`, `Subtyper`, and `EraseDerefTemps` have all executed. Note that `trusted/rustc-capture/src/driver.rs:25, 79` is currently pinned to `1.98.0-nightly (f8a08b688 2026-05-30)` and only confirms `after_analysis` without extracting MIR bodies yet.
2. **`Derefer` & `EraseDerefTemps` (`WithRetag::No` vs. `WithRetag::Yes`):**
   - `Trusted/MirAst.lean:562-619` explicitly documents `Rvalue::Use(Operand<'tcx>, WithRetag)` and `Rvalue::CopyForDeref(Place<'tcx>)`.
   - `MirAst.Rvalue.use` admits `Rvalue::Use(op, withRetag)` **only** when retagging is an operational no-op (`WithRetag::No` or ref/box-free scalar/enum types); any `Use(_, WithRetag::Yes)` on a type containing references or boxes MUST lower fail-closed to `.unsupported` until stacked/tree-borrows retagging is formalized (`MirAst.lean:593-597, 617-618`).
   - `CopyForDeref` is lowered fail-closed to `.unsupported` (`MirAst.lean:616`), and `Trusted/Correspondence.lean:1489-1505` explicitly maps `RefRvalue.unsupported` to `Miri.MIR.Rvalue.CopyForDeref ⟨0, Array.empty⟩` as a fail-closed sentinel that `vendor/lean-miri`'s `evalRvalueIntoPlace` rejects directly with `.invalidProgram` (matching `interpret/step.rs:186` `bug!("CopyForDeref in runtime MIR")`).
   - When Anneal extends `MirAst`/`MirSemantics` to `&T` / `&mut T` dereferencing, its MIR extractor **must** preserve the `WithRetag` bit on `Rvalue::Use` (`WithRetag::No` vs. `WithRetag::Yes`) — conflating `no_retag copy` with a retagging `copy` would inject spurious Tree Borrows / Stacked Borrows UB into valid Rust programs with nested `&mut &mut T` dereferences (as demonstrated by Theorems 6–7 and our live Miri counterexample).
3. **`Subtyper` (`CastKind::Subtype`):**
   - `Trusted/MirAst.lean:612-618` currently lowers all `Rvalue::Cast` variants (including `CastKind::Subtype`) fail-closed to `.unsupported`.
   - Once Anneal extends capture to function pointers or trait objects, admitting `CastKind::Subtype` is operationally a same-size bit-preserving value identity (`interpret/cast.rs:192-200`), while preserving `Subtyper`'s explicit cast node prevents downstream verification/lifting layers from conflating distinct higher-ranked types (`TypeId` / trait resolution).
4. **`LintAndRemoveUninhabited` (`TerminatorKind::Call { target: Option BasicBlockId }`):**
   - `Trusted/MirAst.lean:793-794` already represents `.call` with `target : Option BasicBlockId`.
   - `Trusted/MirSemantics.lean:1568-1569` currently evaluates `.call` fail-closed to `.fault .unsupported`. When interprocedural `.call` semantics is added, returning from a callee into `target = none` must fault with `.fault .undefined` (matching `eval_context.rs:530` `throw_ub!(Unreachable)`), and soundness of `rustc`'s pre-borrowck pruning relies directly on Theorem 17 (`!is_inhabited_from` $\implies$ `!is_opsem_inhabited` $\implies$ no valid return value exists).

---

### 6. Kernel-Checked Lean `v4.34.1` Mechanization Architecture and Purity Audit

Basis: `source` + `execution` (`support/DereferCopyForDerefSubtyperAndVisiblyUninhabitedSoundness.lean`, `Lean v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`)

The companion formalization `support/DereferCopyForDerefSubtyperAndVisiblyUninhabitedSoundness.lean` (`1,769` total lines, `1,615` non-blank LOC, `77,878` bytes) compiles cleanly with `exit 0` under:

```bash
LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
  lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/DereferCopyForDerefSubtyperAndVisiblyUninhabitedSoundness.lean
```

**Strict Kernel Purity Audit:**
- **Zero `sorry` / `sorryAx`**, **zero `Classical.choice`**, **zero `omega`**, **zero `bv_decide`**, **zero `native_decide` / `Lean.ofReduceBool` / `Lean.trustCompiler`**, **zero `partial def`**, and **zero `._unsafe_rec` constants (`UNSAFE_REC_COUNT=0`)** verified programmatically over `env.constants.map₂`.
- **Zero-`_unsafe_rec` engineering note:** In Lean `v4.34.1`, writing recursive `def`s via equation-compiler pattern matching causes the code generator to emit auxiliary `foo._unsafe_rec` declarations (`isPartial` helpers rejected by strict boundary audits). All 7 list-recursive functions (`projHasNoDeref`, `splitAfterFirstAux`, `evalProjChain`, `execNoRetagStmts`, `sbHasTag`, `sbPopAbove`, `execAssignList`) are therefore written using `List.foldr` (computable, `0` `_unsafe_rec`), and all 6 inductive-tree evaluators (`Ty.beq`, `eraseAndAnonymize`, `evalPred`, `evalPredIgnoreMod`, `inhabPred`, `isOpsemInhabited`) are written directly via explicit structural recursors (`@Ty.rec`, `@InhabPred.rec`, `@AdtTy.rec`, `0` `_unsafe_rec`), paired with `rfl` unfolding lemmas.
- **Axiom footprints (`#print axioms` on all 17 audited theorems):**
  - **Zero axioms (`[]`):** `dereferPlace_skips_varDebugInfo`, `withRetagNo_succeeds_and_withRetagYes_causes_stacked_borrows_ub`, `eraseAndAnonymize_idempotent`, `isSubtype_eraseAndAnonymize`, `refNever_opsemUninhab_but_visiblyInhab`.
  - **`[propext]` only:** `dereferPlace_normalForm`, `eraseDerefTemps_eliminates_and_preserves`, `withRetagNo_succeeds_and_withRetagYes_causes_tree_borrows_ub`, `subtyper_plain_region_variance_no_cast`, `subtyper_hrtb_tuple_and_binder_collapse_insert_casts`, `visiblyUninhabited_implies_opsemUninhabited`, `visiblyUninhabited_call_prune_opsem_sound`, `visiblyUninhabited_call_prune_sound_and_semver_monotone`, `enclosingUninhabited_suppresses_lint_preserves_pruning`, `phase_transition_required_desugarings_capstone`.
  - **`[propext, Quot.sound]` only:** `derefer_then_eraseNoRetag_preserves_tree_borrows`, `subtyper_explicit_cast_typing_and_eval_equiv`.

---

## Boundaries

### Explicitly Classified Negative Space

1. **Direct Mechanized Bridge into `joshlf/anneal`'s `Trusted.MirSemantics` — `not examined` / `unsupported` (at `c131b320e`):**
   - `support/DereferCopyForDerefSubtyperAndVisiblyUninhabitedSoundness.lean` is a standalone single-file Lean `v4.34.1` module over faithful abstract models of `Derefer`, `EraseDerefTemps`, `Subtyper`, and `LintAndRemoveUninhabited`; it does **not** import `Trusted.MirAst` or `Trusted.MirSemantics`.
   - At `joshlf/anneal@c131b320e`, `Trusted.MirSemantics` does not yet model reference dereferencing, Tree Borrows / Stacked Borrows tags, function-pointer HRTBs, `Rvalue::Cast`, or `.call` execution (`MirSemantics.lean:1568` faults `.unsupported` on `.call`; `MirAst.lean:612-618` lowers `Cast` and `Use(_, WithRetag::Yes)` on references to `.unsupported`). Thus a direct mechanized refinement against `Trusted.MirSemantics` is currently `unsupported` by the Day-1 `MirSemantics` scope.

2. **`deref_finder(tcx, body, false)` inside `coroutine::StateTransform` (`deref_separator.rs:62-67`, `coroutine/mod.rs:977`) — `unknown` (upstream `FIXME`):**
   - `deref_separator.rs:62-66` carries an explicit upstream `FIXME` noting that `add_deref_metadata = false` is undocumented and tentatively emits `Rvalue::Use(Operand::Copy(deref_place), WithRetag::No)` by analogy with `EraseDerefTemps`. We confirmed the sole caller (`coroutine/mod.rs:977`) and confirmed it runs after `EraseDerefTemps`, but we did **not** empirically stress-test `StateTransform`-generated `add_deref_metadata = false` nested coroutine dereferences under Miri Tree Borrows (`not examined`).

3. **`Box<T>` Derefs, `ElaborateBoxDerefs`, and Custom-Allocator Boxes — `not examined`:**
   - `ElaborateBoxDerefs` (`lib.rs:676`, running immediately after `EraseDerefTemps`) lowers `ProjectionElem::Deref` on `Box<T>` using `CastKind::BoxDerefTransmute`. While `miri/src/borrow_tracker/{stacked_borrows,tree_borrows}/mod.rs` shows that `Box<T, Global>` undergoes retagging under `RetagMode::Default` (and boxes with custom allocators do not, `stacked_borrows/mod.rs:875`, `tree_borrows/mod.rs:495`), our live probe and Lean counterexample examined `&mut &mut (u32, u32)` and `&mut &mut &mut (u32, u32)` rather than nested `Box<Box<T>>`.

4. **`Subtyper` on `Rvalue::Reborrow` (`is_generic_reborrow`), Trait-Object (`dyn for<'a> Trait<'a>`) `Unsize` Coercions, and `-Znext-solver` — `known not to apply` / `not examined`:**
   - `Subtyper` explicitly skips `rvalue.is_generic_reborrow()` (`add_subtyping_projections.rs:27-29`); soundness of generic `Reborrow`/`CoerceShared` trait coercions is `known not to apply` to `Subtyper`'s `CastKind::Subtype` insertion.
   - Our live probe verified that `&dyn for<'b> Fn(&'b u8) -> &'b u8` coerced to `&dyn Fn(&'a u8) -> &'a u8` in `1.98.0-nightly` is lowered earlier during MIR building into `CastKind::PointerCoercion(Unsize, Implicit)` rather than reaching `Subtyper` as an uncast assignment (`known not to apply` to `Subtyper` when already wrapped in `Unsize`).
   - Behavior under `-Znext-solver` (`next_trait_solver_globally() == true`) and `PostAnalysisNormalize`'s `OpaqueCast` removal (`post_analysis_normalize.rs:34-48`) was `not examined` empirically.

5. **`InhabitedPredicate` Generics (`GenericType`), Local Opaque Types (`OpaqueType`), Constant-Length Arrays (`[!; N]` / `[!; 0]`), and `#[non_exhaustive]` Cross-Crate Enums — `not examined` (empirically):**
   - We inspected `inhabitedness/mod.rs:136-167, 255-259` and `inhabited_predicate.rs:91-110` in source, establishing that `[T; 0]` is `True`, unknown-length `[T; N]` yields `pred.or(ConstIsZero(N))`, unions and foreign `#[non_exhaustive]` ADTs yield `True`, and unnormalized generic projections yield `True` conservatively. Our live `rustc` probe and Lean `AdtTy` algebra directly tested `!`, `PublicVoid`, `OpaqueUninhabited(PrivateVoid)` (external, same-module, child-module), `&'static PublicVoid`, and enclosing-uninhabited lint suppression; generic/array/cross-crate `#[non_exhaustive]` cases were `not examined` empirically.

6. **Live Execution Version Gap (`14210df0e` vs. `3ef0c22cd` / `ce66487eb`) — `not examined` (live binary at `ce66487eb`):**
   - All live `rustc` and `Miri` executions in `support/probe_derefer_subtyper_and_visibly_uninhabited.json` ran on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `miri 0.1.0 (14210df0e2 2026-05-31)`. We verified by direct source diff that `deref_separator.rs`, `erase_deref_temps.rs`, `add_subtyping_projections.rs`, and `lint_and_remove_uninhabited.rs` (extracted verbatim from `14210df0e`'s `rustc_mir_build::builder::mod.rs:825-936`) have identical algorithms at `3ef0c22cd` and `ce66487eb`, except that `PassPolicy::Required` in `3ef0c22cd`/`ce66487eb` closes the `-Zmir-enable-passes=-<Pass>` disable loophole observed on `14210df0e`. Executing a live `ce66487eb` binary to confirm `-Zmir-enable-passes=-Derefer` is silently ignored under `PassPolicy::Required` was `not examined` on this host.

### Stronger Conclusions Not Established

- **Does NOT establish that `-Zvalidate-mir` rejects omitted `CastKind::Subtype` coercions:** To the contrary, our source audit (`compare_types.rs:34` `.ignoring_regions()`) and live `-Zvalidate-mir -Zmir-enable-passes=-Subtyper` execution (`rc = 0`) establish that `validate.rs` does **not** catch missing higher-ranked `Subtype` casts.
- **Does NOT establish full Stacked Borrows / Tree Borrows soundness for all MIR rvalues:** Theorems 4–7 prove equivalence of `Derefer` + `EraseDerefTemps(WithRetag::No)` over projection-chain resolution and concrete split-field `&mut &mut (u32, u32)` aliasing counterexamples; they do not formalize protectors (`RetagMode::FnEntry`), `UnsafeCell` interior mutability, or two-phase borrows (`RetagMode::TwoPhase`).
- **Does NOT establish that `is_opsem_inhabited == false` allows pruning in `LintAndRemoveUninhabited`:** Pruning `&'static !` or `OpaqueUninhabited(PrivateVoid)` from outside its defining module would violate Rust's privacy and SemVer stability guarantees (`Case 2` and `Case 4` both prove `rustc` deliberately keeps `target = Some(bb)` and rejects with `E0381`).

---

## Evidence

### 1. Upstream Primary Source Anchors (Immutable Revisions)

All GitHub commit SHAs were resolved live via GitHub API on `2026-11-22`:

| Repository | Full 40-Hex Commit SHA | File Path & Symbol / Line Range | Verified Fact |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` | `compiler/rustc_mir_transform/src/deref_separator.rs:1-109` (`Derefer`, `DerefChecker::visit_place`, `deref_finder`) | Splits `projection[1..].contains(&Deref)` outside `VarDebugInfo` into `LocalInfo::DerefTemp` + `Rvalue::CopyForDeref` (or `Boring` + `Use(Copy, WithRetag::No)` when `add_deref_metadata == false`); `PassPolicy::Required` (`L105-108`). Byte-identical at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`. |
| `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` | `compiler/rustc_mir_transform/src/erase_deref_temps.rs:1-46` (`EraseDerefTemps`, `EraseDerefTempsVisitor`) | Rewrites `CopyForDeref(place)` -> `Rvalue::Use(Operand::Copy(place), WithRetag::No)` (`L20-24`) and `LocalInfo::DerefTemp` -> `LocalInfo::Boring` (`L28-31`); `PassPolicy::Required` (`L42-45`). Byte-identical at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`. |
| `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` | `compiler/rustc_mir_transform/src/add_subtyping_projections.rs:1-73` (`Subtyper`, `SubTypeChecker::visit_assign`) | Skips `is_generic_reborrow()` (`L27`) and `is_deref_temp()` (`L32`), calls `tcx.erase_and_anonymize_regions` (`L39-40`), inserts `temp = rvalue; place = Move(temp) as place_ty (CastKind::Subtype)` when `place_ty != rval_ty` (`L41-48`); `PassPolicy::Required` (`L69-72`). Byte-identical at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`. |
| `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` | `compiler/rustc_mir_transform/src/lint_and_remove_uninhabited.rs:1-139` (`LintAndRemoveUninhabited`, `find_unreachable_code_from`) | Checks `ty.is_inhabited_from(tcx, parent_module, typing_env)` (`L36`), prunes `*target = None` (`L55`), gates `UnreachableDueToUninhabited` lint on `!ty.is_never() && return_ty_is_inhabited` (`L24-25, L47`, issue #149571); `PassPolicy::Required` (`L86-90`). Byte-identical at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`. |
| `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` | `compiler/rustc_mir_transform/src/lib.rs:412-432, 546-698` | Schedules `LintAndRemoveUninhabited` (`L418`), `mir_borrowck` (`L553`), `Derefer` (`L648`), `PostAnalysisNormalize` (`L655`; was `L660` in `3ef0c22cdb`), `Subtyper` (`L664`), `ElaborateDrops` (`L665`), `EraseDerefTemps` (`L675`), `ElaborateBoxDerefs` (`L676`), `StateTransform` (`L677`). |
| `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` | `compiler/rustc_mir_transform/src/pass_manager.rs:88-100, 256-285` | `PassPolicy::Required => true` short-circuits before `-Zmir-enable-passes` overrides (closing the `14210df0e` `pass_manager.rs:214-240` override path). |
| `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` | `compiler/rustc_mir_transform/src/validate.rs:591-618, 653, 956-995, 1028-1032, 1446-1453, 1484-1508, 1669-1679` | Enforces `Deref` only at `projection[0]` (excluding `VarDebugInfo`), forbids `CopyForDeref`/`DerefTemp` in `Runtime(Initial)+`, gates `Operand::Copy` non-`Copy` check on `< Runtime(Initial)`, validates `CastKind::Subtype` via `sub_types`, and sets `Variance::Invariant` on `Assign` in `Runtime(Initial)+` (subject to `compare_types.rs:34` `.ignoring_regions()`). |
| `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` | `compiler/rustc_const_eval/src/util/compare_types.rs:11-43` & `compiler/rustc_infer/src/infer/relate/type_relating.rs:220-255, 322-345` | `relate_types` uses `tcx.infer_ctxt().ignoring_regions()` (`L34`), explaining why `validate.rs` does not reject omitted higher-ranked `Subtype` casts. |
| `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` | `compiler/rustc_middle/src/mir/{syntax.rs:308-340, 490-505, 1456-1466, 1530-1540; pretty.rs:1153-1156, 1205; statement.rs:812-816}` | Defines `WithRetag::{Yes, No}`, `no_retag ` / `deref_copy ` pretty-printing, `CopyForDeref`, `CastKind::Subtype`, and `is_generic_reborrow`. |
| `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` | `compiler/rustc_const_eval/src/interpret/{step.rs:179-186, cast.rs:37-43, 192-200, eval_context.rs:521-532}` | Maps `WithRetag::No -> RetagMode::None`, `CopyForDeref -> bug!`, `CastKind::Subtype -> size-checked value identity`, and `return_to_block(None) -> throw_ub!(Unreachable)`. |
| `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` | `src/tools/miri/src/borrow_tracker/{mod.rs:281-294, stacked_borrows/mod.rs:858-886, tree_borrows/mod.rs:126-135, 474-504}` | Confirms `RetagMode::None` returns `None` (complete retag no-op) in both Stacked Borrows and Tree Borrows. |
| `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` | `compiler/rustc_mir_dataflow/src/move_paths/builder.rs:29-42, 388-412` | Skips `MovePath` allocation for `is_deref_temp()` and maintains `rev_lookup.un_derefer` across `CopyForDeref`. |
| `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` | `compiler/rustc_middle/src/ty/inhabitedness/{mod.rs:72-408, inhabited_predicate.rs:39-110}` | Defines `InhabitedPredicate::NotInModule`, `is_inhabited_from`, `is_privately_uninhabited`, and `is_opsem_inhabited` (including `mod.rs:166` vs. `mod.rs:300-308` reference separation). |
| `rust-lang/rust` | `ce66487ebbd7541212d22d01c39a808057d69f1f` | `compiler/rustc_mir_transform/src/coroutine/mod.rs:977` | Sole `deref_finder(tcx, body, false)` call site (post-`EraseDerefTemps`). |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_mir_build/src/builder/mod.rs:825-936` & `compiler/rustc_mir_transform/src/pass_manager.rs:214-240` | Pre-extraction location of `lint_and_remove_uninhabited` inside MIR building and pre-`PassPolicy` flag-overridable `is_required()` in `1.98.0-nightly`. |
| `rust-lang/reference` | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | `src/subtyping.md:1-113`, `src/types/never.md:1-61`, `src/types/enum.md:1-22` | Normative subtyping (`r[subtype.kinds]`, `r[subtype.higher-ranked]`) and uninhabited/never rules (`r[type.never]`). |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean:53, 450-491, 557-629, 742-796`, `trusted/lean/Trusted/MirSemantics.lean:1542-1570`, `trusted/correspondence/Trusted/Correspondence.lean:1317, 1480-1506`, `trusted/rustc-capture/src/driver.rs:25, 75-84` | Trusted MIR dialect (`Runtime(PostCleanup)`), `WithRetag::No` / `CopyForDeref` / `Cast` / `.call` fail-closed capture rules, and `.CopyForDeref` sentinel in `Correspondence.lean`. |

### 2. Preserved Package Support Artifacts

All empirical and mechanized evidence is self-contained inside this report's `support/` directory (observed `2026-11-22`):

1. **[support/probe_derefer_subtyper_and_visibly_uninhabited.py](support/probe_derefer_subtyper_and_visibly_uninhabited.py):**
   Standalone Python 3.10+ probe (stdlib only, zero hardcoded measurements) compiling and executing all three pass testbeds via live `rustc` and `cargo miri` (both Stacked Borrows and `-Zmiri-tree-borrows`), inspecting MIR phase dumps (`Derefer.before/after`, `EraseDerefTemps.after`, `analysis-post-cleanup.after`, `Subtyper.after`, `runtime-post-cleanup.after`, `built.after`), testing `-Zvalidate-mir -Zmir-enable-passes=-<Pass>`, and sanitizing host paths before serializing JSON.
2. **[support/probe_derefer_subtyper_and_visibly_uninhabited.json](support/probe_derefer_subtyper_and_visibly_uninhabited.json):**
   Recorded output produced by running `python3 support/probe_derefer_subtyper_and_visibly_uninhabited.py support/probe_derefer_subtyper_and_visibly_uninhabited.json` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `miri 0.1.0 (14210df0e2 2026-05-31)` (`x86_64-unknown-linux-gnu`), capturing every exit code, stdout line, MIR assignment/terminator excerpt, and live Miri SB/TB UB diagnostic quoted in **Findings**.
3. **[support/DereferCopyForDerefSubtyperAndVisiblyUninhabitedSoundness.lean](support/DereferCopyForDerefSubtyperAndVisiblyUninhabitedSoundness.lean):**
   `1,769`-line (`1,615` non-blank LOC) standalone Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) mechanization verifying 19 named theorems + capstone with `exit 0` under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, `0` `sorry`/`sorryAx`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`/`Lean.ofReduceBool`, `0` `partial def`, and `UNSAFE_REC_COUNT=0`.

---

## Revalidation

Each claim in this report can be revalidated cheaply with narrow, self-contained checks against any newer `rustc`, `Miri`, `joshlf/anneal`, or `Lean` release:

1. **Rerun the Live `rustc` + `Miri` Differential Probe (~7 seconds):**
   ```bash
   python3 support/probe_derefer_subtyper_and_visibly_uninhabited.py /tmp/reval_probe.json
   ```
   Verify in `/tmp/reval_probe.json`:
   - `nested_mut_raw_split`: `nested_deref_before_derefer == 2`, `nested_deref_after_derefer == 0`, `deref_copy_after_derefer == 2`, `deref_copy_after_erase == 0`, `no_retag_copy_after_erase == 2`, `no_retag_copy_in_runtime_post_cleanup == 2`.
   - `nested_mut_triple_deref`: `nested_deref_before_derefer == 8`, `nested_deref_after_derefer == 0`, `deref_copy_after_derefer == 16`, `no_retag_copy_after_erase == 16`.
   - `miri_with_retag_no`: `stacked_borrows_rc == 0`, `tree_borrows_rc == 0`, stdout `NESTED_MUT_DEREF=33 TRIPLE_DEREF=42`.
   - `miri_with_retag_yes_counterexample`: `stacked_borrows_rc == 1` (read UB / `Unique` retag pop), `tree_borrows_rc == 1` (write UB / `Frozen` transition from foreign read).
   - `subtyper_hrtb_cast`: `hrtb_tuple_coerce`, `hrtb_binder_collapse`, and `hrtb_typeid_split` each transition `0 -> 1` `(Subtype);` casts across `Subtyper`, while `plain_region_variance` remains `0 -> 0`; stdout `SUBTYPER=99 K=7 COLLAPSE=99 TYPEID_DIFF=true VAR=99`.
   - `disable_pass_under_validate_mir`: On `rustc >= 1.102.0-nightly` (with `PassPolicy::Required`), expect all three `disable_*` probes to return `rc == 0` because `-Zmir-enable-passes` can no longer disable `PassPolicy::Required` passes (verify by inspecting that `Derefer.after.mir`, `EraseDerefTemps.after.mir`, and `Subtyper.after.mir` are still emitted!). On pre-`PassPolicy` nightlies (`1.98.0-nightly`), `disable_Derefer` and `disable_EraseDerefTemps` ICE with `rc == 101` while `disable_Subtyper` returns `rc == 0` due to `compare_types.rs:34` `.ignoring_regions()`.
   - `lint_and_remove_uninhabited_visibility_split`: `visibly_uninhabited_pub_void`, `privately_uninhabited_inside_mod_and_child`, and `enclosing_uninhabited_return_lint_suppression` all return `rc == 0` with `call_has_return_target == false` (and the third emits zero `unreachable expression` warnings); `privately_uninhabited_outside_mod` and `opsem_uninhabited_but_visibility_inhabited_ref` both return `rc == 1` with `error[E0381]` and `call_has_return_target == true`.

2. **Rerun Lean `v4.34.1` Kernel Verification & `_unsafe_rec` Audit (~8 seconds):**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/DereferCopyForDerefSubtyperAndVisiblyUninhabitedSoundness.lean
   ```
   Confirm `exit 0`, zero occurrences of `sorryAx`, `Classical.choice`, or `Lean.ofReduceBool` in `#print axioms` output, and zero `._unsafe_rec` constants in `env.constants.map₂`.

3. **Targeted Upstream Source Diffs (When Tracking Newer `rust-lang/rust` or `joshlf/anneal` Commits):**
   Diff the following narrow regions against `ce66487ebbd7541212d22d01c39a808057d69f1f` (`rust-lang/rust`) and `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`joshlf/anneal`):
   - `compiler/rustc_mir_transform/src/{deref_separator.rs,erase_deref_temps.rs,add_subtyping_projections.rs,lint_and_remove_uninhabited.rs,lib.rs,pass_manager.rs,validate.rs}`
   - `compiler/rustc_const_eval/src/util/compare_types.rs` (specifically whether `.ignoring_regions()` is ever tightened to run a higher-ranked leak check)
   - `compiler/rustc_middle/src/ty/inhabitedness/{mod.rs,inhabited_predicate.rs}` (specifically whether `Ty::inhabited_predicate` ever changes `ty::Ref` from `InhabitedPredicate::True`)
   - `joshlf/anneal`: `trusted/lean/Trusted/{MirAst.lean,MirSemantics.lean}` and `trusted/rustc-capture/src/` (specifically when `WithRetag`, `CastKind::Subtype`, and `.call` execution transition from fail-closed `.unsupported` to modeled semantics).
