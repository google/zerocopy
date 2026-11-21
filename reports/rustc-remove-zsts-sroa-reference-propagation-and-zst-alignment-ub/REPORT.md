# `RemoveZsts`, Over-Aligned ZST UB Erasure Under `miri -Zmir-opt-level=1`, `ReferencePropagation`, and `ScalarReplacementOfAggregates`

## Summary

`Basis: normative + source + execution + derived`

This reference report establishes primary-source, empirical (`rustc`, Miri, MIR pass dumps, and full-crate `zerocopy`), and kernel-checked Lean 4 (`v4.34.1`) ground truth for `RemoveZsts` (`remove_zsts.rs`), `CheckAlignment` (`check_alignment.rs`) under `MIRI_DEFAULT_ARGS`, `ReferencePropagation` (`ref_prop.rs`), and `ScalarReplacementOfAggregates` (`sroa.rs`) across `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, and `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`), `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`), `google/zerocopy` (`907b9175fee081872ec883ca4709e6ad922f8ed0`, `v0.8.64`), and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`).

1. **Zero-sized pointer validity decouples allocation liveness from alignment (`size == 0` vs. `addr % align == 0`):** Under the Rust Reference (`src/behavior-considered-undefined.md:18-19, 79-89, 103-110`) and Miri's operational memory model (`compiler/rustc_const_eval/src/interpret/memory.rs:519-566, 579-635`; `place.rs:480-572`), a zero-byte access (`size == 0`) cannot be *dangling* because `check_and_deref_ptr` immediately returns `interp_ok(None)` when `size.bytes() == 0` (`memory.rs:532`). Consequently, reading or writing `()` at `core::ptr::null()` (`size = 0, align = 1, addr = 0`), reading `#[repr(align(64))] struct Aligned64Zst` at `core::ptr::null()` (`0 % 64 == 0`), and reading `Aligned64Zst` at `NonNull::<Aligned64Zst>::dangling().as_ptr()` (`addr = 64`, `64 % 64 == 0`) are all **well-defined (`rc = 0`)** in Rust and Miri at `-Zmir-opt-level=0`. However, `size == 0` **never** exempts loads or stores from pointer alignment (`addr % align == 0`) or from requiring the pointer operand itself to be initialized: `get_place_alloc` and `get_place_alloc_mut` invoke `check_misalign` unconditionally before inspecting `size == 0` (`place.rs:551-552, 568-570`). By contrast, `deref_pointer` on a raw pointer merely caches `mplace.misaligned = is_ptr_misaligned(ptr, align)` (`place.rs:512-515`), so a pure place expression without load/store or safe reborrow (`unsafe { let _ = *misaligned; }`, lowered to `PlaceMention(*misaligned)`) is valid (`rc = 0`) even at `-Zmir-opt-level=0`.
2. **Plain-surface-Rust UB erasure in `miri -Zmir-opt-level=1` (even under `-Zmir-preserve-ub=yes` and `-Zub-checks=yes`):** On plain stable surface Rust (`#[repr(align(64))] struct Aligned64Zst; unsafe { *misaligned = Aligned64Zst; }` and `let v: Aligned64Zst = unsafe { *misaligned };` at `addr % 64 == 1`), `miri -Zmir-opt-level=0` deterministically catches `Undefined Behavior: accessing memory based on pointer with alignment 1, but alignment 64 is required` (`rc = 1`). Passing **`-Zmir-opt-level=1` to Miri—even together with explicit `-Zmir-preserve-ub=yes` and `-Zub-checks=yes`—causes Miri to exit `0` with zero UB diagnostics**. Primary-source inspection and controlled flag ablations prove a three-part mechanism:
   - *(a) `RemoveZsts` ignores `mir_preserve_ub`:* Unlike `RemovePlaceMention` (`remove_place_mention.rs:13`: `PassPolicy::optional(!ctx.opts.unstable_opts.mir_preserve_ub)`) and `CfgSimplifier` (`simplify.rs:132-133`), `RemoveZsts` enables itself at `ctx.mir_opt_level() >= 1` (`remove_zsts.rs:12-14` in `c7d5ba59d`; `is_enabled` at `L10-12` plus `is_required() = true` at `L31-33` in `14210df0e`), unconditionally rewriting `Operand::Copy(*p)` / `Move(*p)` of any known ZST to `ConstValue::ZeroSized` (`remove_zsts.rs:108-116`) and indirect ZST `Assign((*p, rval))` / `PlaceMention(*p)` / `SetDiscriminant(*p)` to `StatementKind::Nop` (`remove_zsts.rs:143-149`) without checking `align == 1` or pointer initialization.
   - *(b) `MIRI_DEFAULT_ARGS` omits `-RemoveZsts`:* In `src/tools/miri/src/lib.rs:200-218` (`14210df0e:183-200`), Miri explicitly disables `-ReferencePropagation` and `-GVN` when users raise `-Zmir-opt-level`, noting they may hide UB, but **does not disable `-RemoveZsts`**.
   - *(c) `-Zmir-enable-passes=-CheckAlignment` overrides `-Zub-checks=yes`:* `MIRI_DEFAULT_ARGS` splices `-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums` right after `argv[0]` (`src/tools/miri/src/bin/miri.rs:468`). Inside `should_run_pass` (`compiler/rustc_mir_transform/src/pass_manager.rs:256-285` in `c7d5ba59d`; `L214-240` in `14210df0e`), `mir_enable_passes` overrides `CheckAlignment`'s default policy (`ctx.ub_checks()`). Thus `-Zub-checks=yes` remains a no-op inside Miri unless `-Zmir-enable-passes=+CheckAlignment` is explicitly appended afterward (`miri_opt1_force_enable_CheckAlignment`, which restores `CheckAlignment` prior to `RemoveZsts` and aborts with `rc = 1`, matching standalone `rustc -Zmir-opt-level=1 -Zub-checks=yes` `rc = -6`).
3. **Cross-version `RemoveZsts` evolution (`14210df0e` vs. `3ef0c22cd` / `c7d5ba59d`):** Between `14210df0e` (2026-05-31) and `3ef0c22cd` (2026-11-11) / `c7d5ba59d` (2026-11-20), `RemoveZsts` underwent two concrete changes that preserve the indirect ZST UB erasure: (i) `is_required() -> true` (`14210df0e:31-33`, which bypassed `#[optimize(none)]` once `mir_opt_level >= 1`) became `PassPolicy::optional(ctx.mir_opt_level() >= 1)` (`c7d5ba59d:12-14`), and (ii) `visit_statement` gained `&& place_for_ty.is_indirect()` (`c7d5ba59d:145`), keeping direct local ZST assignments `_x = const ZeroSized` alive for later move-elimination address stability while still erasing every indirect `(*p) = Aligned64Zst` to `nop`. Meanwhile, reading an *uninitialized* pointer local in `*uninit_ptr = ()` depends on whether `uninit_ptr` itself becomes unused after `*uninit_ptr = ()` turns into `nop`: in `MaybeUninit::<*mut ()>::uninit().assume_init()`, `p = move tmp` still reads uninitialized `tmp` (`rc = 1` in Miri at `opt1`), whereas if an uninitialized `*mut ()` local is never copied before `*p = ()`, `RemoveZsts` erases its sole read as well.
4. **`ReferencePropagation` (`ref_prop.rs`) invariants and the `VarDebugInfo` SROA-blocking gap:** Enabled at `mir_opt_level >= 2` (`ref_prop.rs:76-78`), `ReferencePropagation` first normalizes pointer/reference `Move` operands to `Copy` (`move_to_copy_pointers`, `L93-118`) and then runs a fixed-point `while propagate_ssa` loop (`L84, 120-136`) enforcing three soundness invariants: (1) **Place stability** (`is_constant_place`, `L193-203`: `(*ssa_local).stable_offsets` or `storage_live.has_single_storage(local)` with `PlaceElem::is_stable_offset`), (2) **Target liveness** (`MaybeStorageDead` dataflow, `L161-163, 205-217`, plus `storage_to_remove` stripping intermediate reborrow storage markers at `L455-463`), and (3) **All-or-nothing `&mut` uniqueness** (`fully_replaceable_locals`, `L234-240, 345-348, 361-375`: `ssa.num_direct_uses(local) == 0` closed under `ssa.meet_copy_equivalence` so direct target accesses never interleave with surviving `&mut` aliases). Immediately after `ReferencePropagation` (`lib.rs:751`), `simplify::remove_unused_definitions` (`ref_prop.rs:132`; `simplify.rs:514-565`) marks every local referenced by `VarDebugInfo` (`debug r => _6`) as `always_used` (`simplify.rs:529, 554`), and `StripDebugInfo` does not run until 19 passes later (`lib.rs:773`)—even under default `-C debuginfo=0`! Consequently, an anonymous borrow `(&p).0.wrapping_add((&p).1)` deletes `&p` immediately and **unlocks `ScalarReplacementOfAggregates` (`0` projections)**, whereas binding `let r = &p; r.0.wrapping_add(r.1)` leaves `_6 = &_3` alive entering `ScalarReplacementOfAggregates` (`lib.rs:754`, two passes before `DeadStoreElimination::Initial` at `lib.rs:756`), causing `excluded_locals` (`value_analysis.rs:1044`) to **block SROA on `p` completely**.
5. **`ScalarReplacementOfAggregates` (`sroa.rs`) and full-crate `zerocopy` (`v0.8.64`) MIR normalization:** Enabled at `mir_opt_level >= 2` on non-coroutine bodies (`sroa.rs:18-29`), `ScalarReplacementOfAggregates` precomputes address-taken `excluded_locals(body)` (`sroa.rs:31`) and iterates `loop { escaping_locals ... replace_Input }` (`sroa.rs:33-45`) until fixed point, excluding `_0..=arg_count`, unions, enums, `MaybeDangling` (`is_like_maybe_dangling`, preserving relaxed dangling-reference validity!), `!def.can_project_fields(tcx)`, and whole-value uses outside `StorageLive`/`StorageDead`/`VarDebugInfo`/unprojected LHS `Aggregate`|`Use`. Across all `4,476` MIR bodies of `google/zerocopy@907b9175fee0` (`v0.8.64`) on `rustc 1.98.0-nightly (14210df0e)` (`4,302` bodies on `rustc 1.102.0-nightly (3ef0c22cd)`), `RemoveZsts` modifies `3,199` bodies (`71.47%`), `ReferencePropagation` modifies `825` bodies (`18.43%`, cutting deref projections by `-645` from `2,452` to `1,807`, `-26.3%`; `-535` on `3ef0c22cd`), and `ScalarReplacementOfAggregates` modifies `837` bodies (`18.70%`), cutting direct-local field projections by `-620` (`3,050 -> 2,430`) while temporarily expanding `Ptr` fields onto dead `PhantomData` locals that `SimplifyLocals::BeforeConstProp` + `DeadStoreElimination::Initial` immediately prune (`field_projections: 5,206 -> 4,013`, `direct_local_field_projections: 2,430 -> 1,699`, and `1,637` by `SimplifyLocals::Final`), leaving **`2,742 / 4,476` (`61.26%`)** of `zerocopy` bodies 100% projection-free and borrow-free (`2,644 / 4,302 = 61.46%` on `3ef0c22cd`).
6. **Constructive Lean 4 mechanization and Anneal trusted-boundary requirements:** `support/RemoveZstsSroaAndRefPropSoundness.lean` (4,330 lines, Lean `v4.34.1`, `0` `sorry`, `0` `Classical.choice`, `0` `omega`/`bv_decide`/`native_decide`/`partial def`/`._unsafe_rec`, axioms strictly within `[propext, Quot.sound]`) mechanizes `Layout`, indirect ZST pointer validity, `PassPolicy` override precedence, `RemoveZsts`, `sroaFlatten`, and `refProp` (both `&T` and copy-equivalence-closed `&mut T`), proving: (1) forward codegen refinement of unconditional `removeZstsStmt` across all alignments (`removeZstsStmt_forward_codegen_refinement`) vs. exact bidirectional UB-preserving equivalence for initialized `align == 1` indirect ZST accesses (`removeZsts_indirect_align_one_bidirectional_iff`) and alignment/preserve-UB-guarded `removeZstsCertifiedStmt` (`removeZstsCertifiedStmt_bidirectional_equivalence`); (2) exact single-statement and trace bisimulations of `sroaFlatten` (`sroaFlattenStmt_exact_bisimulation`, `sroaFlattenProg_exact_bisimulation`), parametric in `deinitOnMove : Bool` so the proof covers both Miri (`false`) and Anneal `Trusted.MirSemantics` (`deinitMovedPlace = true`), plus `MaybeDangling` exclusion necessity (`sroa_maybeDangling_exclusion_necessary`); (3) exact bisimulations of shared and all-or-nothing `&mut` `ReferencePropagation` (`refProp_shared_exact_bisimulation`, `refProp_mut_all_or_nothing_exact_bisimulation`); and (4) three constructive sharpness counterexamples (`ce1_remove_zsts_erases_misaligned_align64_zst_ub`, `ce2_refprop_into_storage_dead_target_dangling_ub`, `ce3_partial_mut_refprop_interleaving_aliasing_unsound`—the last demonstrating **forward UB introduction** into a defined program when `&mut` replacement is partial!). Because `joshlf/anneal@c131b320` captures post-cleanup MIR prior to `RemoveZsts`/`ReferencePropagation`/`SROA` and fails closed on non-empty projections and borrows, any verified pre-pass normalizing projections/borrows for Anneal VC generation must enforce these exact certified side conditions—and differential Miri testing of Anneal specs must never pass `-Zmir-opt-level >= 1` without accounting for `RemoveZsts` UB erasure.

---

## Applicability

`Basis: source + execution`

This report characterizes seven durable upstream subjects and their exact technical relationships:

1. **Primary executed compiler and interpreter (`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly 2026-05-31`, `miri 0.1.0`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`):** All live runs in `support/probe_remove_zsts_sroa_refprop.py` -> `support/probe_results.json` (Part A 8-specimen × 6-mode Miri/native ZST matrix, Part B 7-function `ReferencePropagation` + `ScalarReplacementOfAggregates` MIR litmus suite, and Part C `4,476`-body `zerocopy` pass census across 6 pass checkpoints) were executed directly on this toolchain, with every compiler file line-pinned to this exact commit.
2. **Cross-version executed comparison toolchain (`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `rustc 1.102.0-nightly 2026-11-11`, LLVM `23.1.5`, `x86_64-unknown-linux-gnu`):** Provides cross-version execution comparison for both the Miri `-Zmir-opt-level=1` over-aligned ZST UB erasure matrix and the `4,302`-body `zerocopy` pass census after `RemoveZsts` switched from unconditional ZST statement erasure to `place_for_ty.is_indirect()`.
3. **Upstream continuity revision (`rust-lang/rust` @ `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, 2026-11-20 `HEAD`):** Every relevant upstream source file (`remove_zsts.rs`, `remove_place_mention.rs`, `check_alignment.rs`, `check_null.rs`, `check_pointers.rs`, `pass_manager.rs`, `ref_prop.rs`, `sroa.rs`, `ssa.rs`, `value_analysis.rs`, `simplify.rs`, `lib.rs`, `options.rs`, `session.rs`, `place.rs`, `operand.rs`, `memory.rs`, `step.rs`, `src/tools/miri/src/lib.rs`, `src/tools/miri/src/bin/miri.rs`) was audited directly at this commit.
   - **Shared across `14210df0e`, `3ef0c22cd`, and `c7d5ba59d`:**
     - Miri's `check_and_deref_ptr` early `interp_ok(None)` return when `size == 0`, combined with `get_place_alloc`/`get_place_alloc_mut` unconditional `check_misalign` and `deref_pointer` deferred raw-pointer `mplace.misaligned` caching;
     - `RemoveZsts` enabling at `mir_opt_level >= 1` without consulting `mir_preserve_ub`, rewriting indirect ZST `Copy(*p)`/`Move(*p)` operands to `ConstValue::ZeroSized` and indirect ZST `Assign((*p, _))`/`PlaceMention(*p)`/`SetDiscriminant(*p)` statements to `StatementKind::Nop`;
     - `MIRI_DEFAULT_ARGS` splicing `-Zmir-preserve-ub`, `-Zmir-opt-level=0`, `-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums`, and `-Zmir-enable-passes=-ReferencePropagation,-GVN` after `argv[0]` while omitting `-RemoveZsts`, and `should_run_pass` giving `mir_enable_passes` strict precedence over `CheckAlignment`'s `ctx.ub_checks()` default;
     - `CheckAlignment` running near the top of `run_optimization_passes` (`lib.rs:695` in `14210df0e`; `L711` in `c7d5ba59d`) well before `RemoveZsts` (`lib.rs:722` in `14210df0e`; `L738` in `c7d5ba59d`);
     - `ReferencePropagation` (`mir_opt_level >= 2`: `move_to_copy_pointers`, `has_single_storage`, `MaybeStorageDead`, `fully_replaceable_locals` + `ssa.meet_copy_equivalence`, `remove_unused_definitions` preserving `VarDebugInfo` locals) running 3 passes before `ScalarReplacementOfAggregates`, while `DeadStoreElimination::Initial` runs 2 passes *after* `ScalarReplacementOfAggregates` and `StripDebugInfo` runs 19 passes *after* `ScalarReplacementOfAggregates`;
     - `ScalarReplacementOfAggregates` (`mir_opt_level >= 2`: `excluded_locals`, iterative `escaping_locals` excluding `_0..=arg_count`, unions, enums, `MaybeDangling`, `!can_project_fields`, and non-`Field` whole-local uses).
   - **Version-specific differences between `14210df0e` and `3ef0c22cd` / `c7d5ba59d`:**
     - *`RemoveZsts` `is_required` vs. `PassPolicy::optional`:* In `14210df0e` (`remove_zsts.rs:10-12, 31-33`), `RemoveZsts` implemented `is_enabled() = mir_opt_level >= 1` **and** `is_required() = true`, meaning `#[optimize(none)]` on an individual function could not suppress `RemoveZsts` when crate `-Zmir-opt-level >= 1` (and `-Zmir-enable-passes=-RemoveZsts` was ignored by `should_run_pass` at `pass_manager.rs:215-217` because `pass.is_required()` returned early before checking `mir_enable_passes`!). By `c7d5ba59d` (`remove_zsts.rs:12-14`; `pass_manager.rs:257-268`), `RemoveZsts` uses `PassPolicy::optional(ctx.mir_opt_level() >= 1)`, so both `#[optimize(none)]` (`PassCtx::mir_opt_level` at `pass_manager.rs:144-150`) and `-Zmir-enable-passes=-RemoveZsts` suppress `RemoveZsts`.
     - *`RemoveZsts` direct vs. indirect statement `nop`:* In `14210df0e` (`remove_zsts.rs:139-145`), `visit_statement` rewrote *both* direct (`_x = Aligned64Zst`) and indirect (`(*_p) = Aligned64Zst`) ZST `Assign`/`PlaceMention`/`SetDiscriminant` statements to `StatementKind::Nop` (causing `zst_const_ops` across `zerocopy` to *drop* from `3,721` to `1,001`). In `3ef0c22cd` and `c7d5ba59d` (`remove_zsts.rs:143-149`), `visit_statement` guards statement erasure with `&& place_for_ty.is_indirect()`, leaving direct `_x = const ZeroSized` assignments intact so move-elimination / local-address reasoning sees explicit writes (causing `zst_const_ops` across `zerocopy` to *rise* from `3,648` to `4,384`, `+736`), while **identically erasing all indirect ZST writes `(*_p) = ...` and indirect `PlaceMention(*_p)` to `nop`**.
     - *`PointerFinder` unsized raw-pointer handling:* In `14210df0e` (`check_pointers.rs:209-212`), `PointerFinder` skips unsized pointees via `pointee_ty.is_sized(self.tcx, self.typing_env)`. In `c7d5ba59d` (`check_pointers.rs:212-215`), `PointerFinder` passes `pointee_ty` directly to `check_fn` and computes dynamic slice/Metadata alignment via `InsertAlignmentCheck::compute_align` (`check_alignment.rs:78-115`) when `layout.is_unsized()`, still ignoring `extern type` metadata (`DynStar`/`Foreign` -> `Align::ONE`).
4. **Normative language specification (`rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):** Supplies the normative rules for pointer dereference, alignment, dangling vs. zero-sized spans, uninitialized memory, and type layout (`src/behavior-considered-undefined.md`, `src/type-layout.md`).
5. **Real-world systems workload (`google/zerocopy` @ `907b9175fee081872ec883ca4709e6ad922f8ed0`, `v0.8.64`):** Supplies a `4,476`-body (`14210df0e`) / `4,302`-body (`3ef0c22cd`) systems Rust crate dense in `PhantomData<T>` ZST markers, `Ptr<'a, T, I>` nested wrapper structs, and zero-cost reference/pointer conversions.
6. **Anneal verification trusted boundary (`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Evaluated at `trusted/lean/Trusted/{MirAst.lean,MirSemantics.lean}`, `trusted/correspondence/Trusted/Correspondence.lean`, and `vendor/lean-miri/Miri/{Interpreter/Place.lean,Memory/Access.lean,Memory/AllocationAccess.lean}` to determine exact pre-pass certification obligations and Miri differential-oracle constraints.
7. **Lean 4 kernel (`leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Verifies `support/RemoveZstsSroaAndRefPropSoundness.lean` standalone with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

---

## Findings

### 1. Normative and Miri Operational Semantics of Indirect ZST Pointer Accesses

`Basis: normative + source + execution`

#### 1.1 Why `*(null as *const ())` and `*NonNull::<Aligned64Zst>::dangling().as_ptr()` Are Valid While `*misaligned_align64_zst` Is UB

A frequent source of compiler and verification bugs is conflating **allocation dereferenceability** (`size` bytes must lie within a live allocation when `size > 0`) with **pointer alignment validity** (`addr % align == 0`, required even when `size == 0`) and **place evaluation vs. value load/store**. Both the Rust Reference (`rust-lang/reference@c9cc32825b03`, `src/behavior-considered-undefined.md`) and Miri (`compiler/rustc_const_eval/src/interpret/`) separate these checks sharply:

1. **Dangling pointers exempt `size == 0` (`r[undefined.dangling.def]`, `behavior-considered-undefined.md:103-110`):**
   > *"A reference or pointer is 'dangling' if it is null or not all of the bytes it points to are part of the same live allocation (so in particular they all have to be part of some allocation). The span of bytes it points to is determined by the pointer value and the size of the pointee type (using `size_of_val`). As a consequence, if the span is empty, 'dangling' is the same as 'non-null'. Note that dynamically sized types (such as slices and strings) point to their entire range, so it is important that the length metadata is never too large. If the size is 0, then a pointer is never considered 'dangling' for memory accesses (even if it is null), because it points to no bytes."*

   Note the crucial distinction inside that paragraph: for **references/Boxes** (`&T`, `&mut T`, `Box<T>`), null is always invalid via the type validity invariant (`non-null` + `aligned`, even when `size == 0`), whereas for **raw-pointer memory accesses** (`*p` load/store), `size == 0` points to zero bytes and is **never dangling, even when `p` is `null` or `NonNull::dangling()`**!
2. **Misalignment does NOT exempt `size == 0` on loads or stores, but DOES exempt pure raw-pointer place expressions (`r[undefined.misaligned]`, `behavior-considered-undefined.md:79-89`):**
   - `r[undefined.misaligned.load-store]` (`L88`): *"Performing a load or store from a place that is misaligned, based on the alignment of the accessed place's type."* There is **no** `size > 0` guard: loading or storing a zero-sized `#[repr(align(64))] struct Aligned64Zst` at address `1` (`1 % 64 != 0`) is immediate Undefined Behavior.
   - By contrast, evaluating a raw-pointer place expression `*raw_ptr` *without* loading, storing, creating a safe reference, or projecting (`let _ = *misaligned;` -> `StatementKind::PlaceMention(*misaligned)`) does **not** perform a load or store and is well-defined (`rc = 0`).

Miri's interpreter (`compiler/rustc_const_eval/src/interpret/`) implements these exact three steps:

- **Step 1 — Reading the pointer operand (`eval_operand` -> `deref_pointer`, `place.rs:480-517` in `c7d5ba59d`; `L466-503` in `14210df0e`):**
  `deref_pointer` first evaluates the pointer local `op = self.read_immediate(&val)?`. If the pointer local itself holds `MaybeUninit::uninit()`, `read_immediate` immediately faults with uninitialized-memory UB (`alloc[0x0..0x8] is uninitialized`), regardless of whether the pointee is a ZST. Next, `deref_pointer` checks `check_and_deref_ptr` (`memory.rs:519-566`), which immediately short-circuits on `size == 0`:
  ```rust
  // compiler/rustc_const_eval/src/interpret/memory.rs:531-533 (c7d5ba59d)
  if size.bytes() == 0 {
      // Nothing to check, not even non-nullness!
      return interp_ok(None);
  }
  ```
  Finally, `deref_pointer` checks alignment via `let misaligned = self.is_ptr_misaligned(val.to_scalar_ptr(), layout.align);`: if `!ref_tracking` (a raw pointer `*const T` / `*mut T` when `-Zmiri-check-raw-ptr` is not active), `deref_pointer` does **not** fault yet—it stores `misaligned: Option<Misalignment>` inside `MPlaceTy` (`place.rs:512-515`)! Consequently, `StatementKind::PlaceMention(*misaligned)` (`step.rs:146-162`, calling `eval_place(place)?` without `get_place_alloc`) succeeds with `rc = 0`!
- **Step 2 — Performing a ZST load or ZST store (`get_place_alloc` / `get_place_alloc_mut`, `place.rs:541-572` in `c7d5ba59d`; `L505-516` in `14210df0e`):**
  When MIR executes `_v = copy (*_p)` (`eval_place_to_op` -> `read_from_mplace`) or `(*_p) = Aligned64Zst` (`write_constant_to_mplace` / `copy_op`), Miri calls `get_place_alloc` or `get_place_alloc_mut`:
  ```rust
  // compiler/rustc_const_eval/src/interpret/place.rs:549-555 (c7d5ba59d)
  pub fn get_place_alloc(&self, mplace: &MPlaceTy<'tcx, M::Provenance>) -> InterpResult<'tcx, Option<AllocRef<'_, 'tcx, M::Provenance, M::AllocExtra, M::Bytes>>> {
      let size = mplace.layout.size;
      self.check_misalign(mplace.misaligned)?;
      if size == Size::ZERO {
          return interp_ok(None);
      }
      ...
  ```
  `self.check_misalign(mplace.misaligned)?` runs **strictly before** `if size == Size::ZERO { return interp_ok(None); }`! Inside `is_ptr_misaligned` -> `is_offset_misaligned` (`memory.rs:589-597`), Miri computes `offset.bytes() % align.bytes() != 0` on the concrete integer address (`0 % 1 == 0`, `0 % 64 == 0`, `64 % 64 == 0`, whereas `(base + 1) % 64 != 0` faults with `AlignmentCheckFailed`!). Notice that `joshlf/anneal@c131b320`'s vendored `lean-miri` (`vendor/lean-miri/Miri/Interpreter/Place.lean:455-510`, `Miri/Memory/Access.lean:160-245`) mirrors this exact ordering: `getPlaceAlloc` and `getPlaceAllocMut` call `checkMisalign` before returning `none` on `size == 0`.

---

### 2. Plain-Surface-Rust Over-Aligned ZST UB Erasure Under `miri -Zmir-opt-level=1`

`Basis: source + execution + derived`

#### 2.1 `RemoveZsts` Implementation and Missing `mir_preserve_ub` Guard (`remove_zsts.rs`)

`RemoveZsts` (`compiler/rustc_mir_transform/src/remove_zsts.rs`) eliminates reads, indirect writes, and local storage markers of statically known zero-sized types (`ty_and_layout.is_zst()`, i.e. `!layout.is_unsized() && layout.size.bytes() == 0` after rejecting coroutines/closures with uncomputed layouts via `known_zst` at `remove_zsts.rs:76-94`).

Compare the pass-gating policies of `RemovePlaceMention`, `CfgSimplifier`, and `RemoveZsts` in `rust-lang/rust@c7d5ba59d`:

```rust
// compiler/rustc_mir_transform/src/remove_place_mention.rs:12-14 (c7d5ba59d)
fn policy(&self, ctx: &PassCtx<'_>) -> PassPolicy {
    PassPolicy::optional(!ctx.opts.unstable_opts.mir_preserve_ub)
}

// compiler/rustc_mir_transform/src/remove_zsts.rs:12-14 (c7d5ba59d)
fn policy(&self, ctx: &PassCtx<'_>) -> PassPolicy {
    PassPolicy::optional(ctx.mir_opt_level() >= 1)
}
```

And in `rust-lang/rust@14210df0e` (`compiler/rustc_mir_transform/src/remove_zsts.rs:10-12, 31-33`):

```rust
fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
    sess.mir_opt_level() >= 1
}
fn is_required(&self) -> bool {
    true
}
```

`RemoveZsts` **never consults `mir_preserve_ub`**, nor does it check `ty_and_layout.align.bytes() == 1` or pointer local initialization when folding an indirect dereference `*p`:

1. **Operand visitor (`Replacer::visit_operand`, `remove_zsts.rs:108-116` in `c7d5ba59d`; `L104-112` in `14210df0e`):**
   ```rust
   fn visit_operand(&mut self, operand: &mut Operand<'tcx>, _: Location) {
       let Some(place) = operand.place() else { return };
       let place_ty = place.ty(self.local_decls, self.tcx).ty;
       if self.known_zst(place_ty) {
           *operand = self.make_zst(place_ty);
       }
   }
   ```
   Whenever `place` is `(*_2)` of type `Aligned64Zst` (`size = 0, align = 64`), `operand.place()` returns `Some((*_2))`, `known_zst(Aligned64Zst)` is `true`, and `Copy(*_2)` / `Move(*_2)` is overwritten in-place with `Operand::Constant(ConstOperand { const_: Const::Val(ConstValue::ZeroSized, Aligned64Zst) })`. The dereference of `_2` vanishes from the RHS before any interpreter or backend sees it.
2. **Statement visitor (`Replacer::visit_statement`, `remove_zsts.rs:118-152` in `c7d5ba59d`; `L114-147` in `14210df0e`):**
   ```rust
   // compiler/rustc_mir_transform/src/remove_zsts.rs:135-150 (c7d5ba59d)
   let place_for_ty = match statement.kind {
       StatementKind::Assign(box (place, ref rvalue)) => {
           rvalue.is_safe_to_remove().then_some(place)
       }
       StatementKind::StorageDead(local) | StatementKind::StorageLive(local) => {
           if self.known_zst(self.local_decls[local].ty) {
               statement.make_nop(true);
           }
           return;
       }
       StatementKind::Deinit(box place)
       | StatementKind::SetDiscriminant { box place, variant_index: _ }
       | StatementKind::PlaceMention(box place) => Some(place),
       ...
   };
   if let Some(place_for_ty) = place_for_ty
       && place_for_ty.is_indirect()
       && let ty = place_for_ty.ty(self.local_decls, self.tcx).ty
       && self.known_zst(ty)
   {
       statement.make_nop(true);
   } else {
       self.super_statement(statement, location);
   }
   ```
   (In `14210df0e:139-145`, the `&& place_for_ty.is_indirect()` guard was absent, so both direct `_x = Aligned64Zst` and indirect `(*_2) = Aligned64Zst` became `nop`; in `3ef0c22cd` and `c7d5ba59d`, `place_for_ty.is_indirect()` preserves direct local ZST writes while **specifically targeting indirect `(*_2) = ...` for `nop` erasure**!)

#### 2.2 The Three-Way Pass-Manager Vacuum Under `MIRI_DEFAULT_ARGS`

Why does Miri fail to catch `*misaligned = Aligned64Zst` at `-Zmir-opt-level=1` even when the user explicitly passes `-Zmir-preserve-ub=yes` **and** `-Zub-checks=yes`? Direct inspection of `src/tools/miri/src/lib.rs`, `src/tools/miri/src/bin/miri.rs`, and `compiler/rustc_mir_transform/src/pass_manager.rs` reveals three interlocking design choices:

1. **`MIRI_DEFAULT_ARGS` disables `-ReferencePropagation` and `-GVN`, but forgets `-RemoveZsts`:**
   ```rust
   // src/tools/miri/src/lib.rs:200-218 (c7d5ba59d; L183-200 in 14210df0e)
   pub const MIRI_DEFAULT_ARGS: &[&str] = &[
       "--cfg=miri",
       "-Zalways-encode-mir",
       "-Zextra-const-ub-checks",
       "-Zmir-preserve-ub",
       "-Zmir-opt-level=0",
       // Weaken protection against layout randomization, so Miri can test it better.
       "-Zrandomize-layout",
       // CheckAlignment, CheckNull and CheckEnums insert checks that Miri already does itself.
       "-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums",
       // Some optimizations are known to hide UB, so disable them even if the user
       // explicitly selects a higher mir-opt-level.
       "-Zmir-enable-passes=-ReferencePropagation,-GVN",
   ];
   ```
   And in `src/tools/miri/src/bin/miri.rs:466-469`, Miri constructs `rustc_args` by splicing `MIRI_DEFAULT_ARGS` immediately after `argv[0]`, followed by user `RUSTFLAGS` / CLI flags. Notably, Miri prints a warning (`warning: You have explicitly enabled MIR optimizations, overriding Miri's default which is to completely disable them. Any optimizations may hide UB that Miri would otherwise detect...`), confirming that Miri's authors knew higher MIR opt levels risk hiding UB and tried to block known UB-erasing passes via `-ReferencePropagation,-GVN`, yet left `RemoveZsts` enabled at `mir_opt_level >= 1`!
2. **`should_run_pass` gives `MIRI_DEFAULT_ARGS`'s `-CheckAlignment` strict precedence over `-Zub-checks=yes`:**
   In `compiler/rustc_mir_transform/src/pass_manager.rs:256-285` (`c7d5ba59d`; `L214-240` in `14210df0e`):
   ```rust
   pub fn should_run_pass<'tcx, P: MirPass<'tcx> + ?Sized>(
       tcx: TyCtxt<'tcx>,
       pass: &P,
       def_id: DefId,
   ) -> bool {
       let name = pass.name();
       let ctx = PassCtx { tcx, def_id, opts: tcx.sess.opts };
       let enabled_by_default = match pass.policy(&ctx) {
           PassPolicy::Required => return true,
           PassPolicy::Optional { enabled_by_default } => enabled_by_default,
       };
       let overridden = tcx
           .sess
           .opts
           .unstable_opts
           .mir_enable_passes
           .iter()
           .rev()
           .find_map(|(s, polarity)| (s == name).then_some(*polarity));
       overridden.unwrap_or(enabled_by_default)
   }
   ```
   `CheckAlignment` has `PassPolicy::optional(ctx.ub_checks())` (`check_alignment.rs:15-18`), so `-Zub-checks=yes` sets `enabled_by_default = true`. However, `MIRI_DEFAULT_ARGS` already pushed `("CheckAlignment", false)` into `mir_enable_passes`! Thus `overridden` evaluates to `Some(false)`, and `overridden.unwrap_or(true)` returns **`false`**! Only when the user explicitly passes `-Zmir-enable-passes=+CheckAlignment` *after* `MIRI_DEFAULT_ARGS` does `.iter().rev().find_map(...)` encounter `("CheckAlignment", true)` first and run `CheckAlignment`.
3. **Pass ordering between `CheckAlignment` and `RemoveZsts` (`lib.rs:694-739`):**
   In `run_optimization_passes` (`compiler/rustc_mir_transform/src/lib.rs:695` vs `L722` in `14210df0e`; `L711` vs `L738` in `c7d5ba59d`), `CheckAlignment` is the **very first pass** in the optimization pipeline, running **27 slots before `RemoveZsts`**. Furthermore, `PointerFinder` (`check_pointers.rs:190-215`) visits `(*misaligned)` on both `(*_2) = Aligned64Zst` and `_3 = copy (*_2)` because `_2: *mut Aligned64Zst` / `*const Aligned64Zst` has type `ty::RawPtr` and `Aligned64Zst` is `Sized`, inserting `AssertKind::MisalignedPointerDereference { required: const 64_usize, found: ... }` before `RemoveZsts` erases `(*_2)`!
   - Under standalone `rustc -Zmir-opt-level=1 -Zub-checks=yes` (where `MIRI_DEFAULT_ARGS` is absent), `CheckAlignment` runs before `RemoveZsts`, so native execution aborts (`rc = -6`, `SIGABRT`) on both misaligned ZST read and misaligned ZST write!
   - Under `miri -Zmir-opt-level=1 -Zmir-preserve-ub=yes -Zub-checks=yes`, `MIRI_DEFAULT_ARGS` suppresses `CheckAlignment`, `RemoveZsts` erases `(*_2)` before Miri's interpreter ever executes a single instruction, and Miri exits `0`!
   - Under `miri -Zmir-opt-level=1 -Zmir-preserve-ub=yes -Zub-checks=yes -Zmir-enable-passes=+CheckAlignment`, `+CheckAlignment` overrides `-CheckAlignment`, inserts the MIR alignment assertion before `RemoveZsts`, and Miri panics cleanly (`rc = 1`)!

#### 2.3 Empirical 8-Specimen × 6-Mode ZST Verification Matrix (Part A)

Executing `support/probe_remove_zsts_sroa_refprop.py` (`support/probe_results.json`) on `rustc 1.98.0-nightly (14210df0e)` + `miri 0.1.0` (with matching 4-mode results verified on `rustc 1.102.0-nightly (3ef0c22cd)`) establishes the complete 8 × 6 behavioral table:

| Specimen (Plain Stable Surface Rust) | Pointee Layout & Address | `miri -Zmir-opt-level=0 -Zmir-preserve-ub=yes` | `miri -Zmir-opt-level=0 -Zmir-preserve-ub=yes -Zmir-enable-passes=+RemoveZsts` | `miri -Zmir-opt-level=1 -Zmir-preserve-ub=yes` | `miri -Zmir-opt-level=1 -Zmir-preserve-ub=yes -Zub-checks=yes` | `miri -Zmir-opt-level=1 -Zmir-preserve-ub=yes -Zub-checks=yes -Zmir-enable-passes=+CheckAlignment` | Native `rustc -Copt-level=0 -Zmir-opt-level=1 -Zub-checks=yes` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `surface_null_unit_read_black_box` (`let v: () = unsafe { *null() };`) | `(0, 1)`, `addr = 0` | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) |
| `surface_null_unit_write` (`unsafe { *null_mut::<()>() = (); }`) | `(0, 1)`, `addr = 0` | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) |
| `surface_null_align64_zst_read` (`let v: Aligned64Zst = unsafe { *null() };`) | `(0, 64)`, `addr = 0` (`0 % 64 == 0`) | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) |
| `surface_dangling_align64_zst_read` (`*NonNull::<Aligned64Zst>::dangling().as_ptr()`) | `(0, 64)`, `addr = 64` (`64 % 64 == 0`) | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) | `rc = 0` (Valid) |
| **`surface_misaligned_align64_zst_write`** (`*misaligned = Aligned64Zst`) | `(0, 64)`, `addr % 64 == 1` | **`rc = 1` (UB: align 1 < 64)** | **`rc = 0` (UB ERASED!)** | **`rc = 0` (UB ERASED!)** | **`rc = 0` (UB ERASED!)** | `rc = 1` (`CheckAlignment` panic) | `rc = -6` (`CheckAlignment` `SIGABRT`) |
| **`surface_misaligned_align64_zst_read`** (`let v = *misaligned; black_box(v)`) | `(0, 64)`, `addr % 64 == 1` | **`rc = 1` (UB: align 1 < 64)** | **`rc = 0` (UB ERASED!)** | **`rc = 0` (UB ERASED!)** | **`rc = 0` (UB ERASED!)** | `rc = 1` (`CheckAlignment` panic) | `rc = -6` (`CheckAlignment` `SIGABRT`) |
| `surface_misaligned_align64_zst_place_mention` (`unsafe { let _ = *misaligned; }`) | `(0, 64)`, `addr % 64 == 1` (no load/store) | `rc = 0` (Valid!) | `rc = 0` (Valid!) | `rc = 0` (Valid!) | `rc = 0` (Valid!) | `rc = 0` (Valid!) | `rc = 0` (Valid!) |
| `surface_uninit_ptr_to_zst_write` (`let p = uninit_ptr.assume_init(); *p = ();`) | `(0, 1)`, `p` uninitialized | `rc = 1` (UB: uninit 8B ptr) | `rc = 1` (UB at `assume_init` copy) | `rc = 1` (UB at `assume_init` copy) | `rc = 1` (UB at `assume_init` copy) | `rc = 1` (UB at `assume_init` copy) | **`rc = 0` (Silent!)** |

Observe four decisive discriminators in this matrix:
1. Column 4 (`miri -Zmir-opt-level=0 -Zmir-preserve-ub=yes -Zmir-enable-passes=+RemoveZsts`) isolates `RemoveZsts` with **zero other optimization passes active**: enabling `RemoveZsts` alone flips `surface_misaligned_align64_zst_write` and `surface_misaligned_align64_zst_read` from `rc = 1` (UB caught) to `rc = 0` (`0` diagnostics), proving `RemoveZsts` is the **sole and sufficient** cause of the UB erasure.
2. In `surface_misaligned_align64_zst_write`, the exact MIR diff captured in `support/probe_results.json` (`before_RemoveZsts_mir` vs. `after_RemoveZsts_mir` at `-Zmir-opt-level=1 -Zmir-preserve-ub=yes -Zub-checks=no`) is:
   ```text
   // BEFORE RemoveZsts (bb3):
   _2 = ptr::mut_ptr::<impl *mut u8>::cast::<Aligned64Zst>(move _3) -> [return: bb4, unwind continue];
   bb4: {
       (*_2) = Aligned64Zst;
       _0 = const ();
       return;
   }

   // AFTER RemoveZsts (bb4):
   bb4: {
       nop;
       nop;          // (on 3ef0c22cd / c7d5ba59d: `_0 = const ();` preserved because _0 is direct)
       return;
   }
   ```
   And in `surface_misaligned_align64_zst_read`, `_3 = copy (*_2);` in `bb4` becomes `_3 = const Aligned64Zst;` (`const ZeroSized: Aligned64Zst`).
3. Look at row 7 (`surface_misaligned_align64_zst_place_mention`: `unsafe { let _ = *misaligned; }`): even `CheckAlignment` (`+CheckAlignment` in Miri and native `-Zub-checks=yes`) exits `0`! Why? Inspecting `compiler/rustc_mir_transform/src/check_pointers.rs:190-206` shows that `PointerFinder::visit_place` skips `PlaceContext::NonUse(NonUseContext::PlaceMention)` (`!context.is_use()`, `check_pointers.rs:193`), matching `r[undefined.misaligned.load-store]` (`PlaceMention` does not load or store)!
4. Look at row 8 (`surface_uninit_ptr_to_zst_write`): Miri catches the uninitialized 8-byte pointer read inside `MaybeUninit::assume_init()` (`_1 = move (_2.0: *mut ())`) at both `opt0` and `opt1` (`rc = 1`), whereas native `-Zub-checks=yes` exits `0` because `-Zub-checks` has no shadow-memory initialization tracking (moreover, at raw MIR level without `MaybeUninit::assume_init()`, `StorageLive(_1); (*_1) = ();` has its sole read of `_1` inside `(*_1) = ()` erased to `nop` by `RemoveZsts`, as mechanized in `PtrInitSound` in Section 5).

---

### 3. `ReferencePropagation` (`ref_prop.rs`): Soundness Pillars and the `VarDebugInfo` SROA-Blocking Asymmetry

`Basis: source + execution + derived`

#### 3.1 Pass Pipeline, `move_to_copy_pointers`, and Fixed-Point `propagate_ssa`

`ReferencePropagation` (`compiler/rustc_mir_transform/src/ref_prop.rs`) is enabled at `ctx.mir_opt_level() >= 2` (`ref_prop.rs:76-78` in `c7d5ba59d`; `L62-64` in `14210df0e`). Its `run_pass` entry point executes two sequential steps:

1. **Pointer move-to-copy normalization (`move_to_copy_pointers`, `ref_prop.rs:93-118`):**
   Scans every basic block and rewrites `Operand::Move(place)` to `Operand::Copy(place)` whenever `place.ty(local_decls, tcx).ty.is_any_ptr()` (`&T`, `&mut T`, `*const T`, `*mut T`, `Box<T>`? Note `Ty::is_any_ptr` matches `Ref` and `RawPtr`, which are `Copy`—yes, even `&mut T` is trivially bitwise copyable in post-borrowck runtime MIR once borrow checking is complete, provided aliasing rules are respected!). Why is this required? Because `SsaLocals` (`compiler/rustc_mir_transform/src/ssa.rs:212-220`) treats `MutatingUseContext::Move` as a *mutation* of the moved-from local (disqualifying it from SSA!), whereas `NonMutatingUseContext::Copy` is a pure SSA read.
2. **Iterative SSA reference substitution (`while propagate_ssa`, `ref_prop.rs:84, 120-136`):**
   ```rust
   // compiler/rustc_mir_transform/src/ref_prop.rs:120-135 (c7d5ba59d)
   let ssa = SsaLocals::new(tcx, body, typing_env);
   let storage_live = StorageLiveLocals::new(body, &ssa);
   let replacements = compute_replacement(tcx, body, typing_env, &ssa, &storage_live);
   if replacements.is_empty() {
       return false;
   }
   let mut replacer = Replacer { tcx, body, replacements, storage_to_remove: BitSet::new_empty(body.local_decls.len()), any_replacement: false };
   replacer.visit_body_preserves_cfg(body);
   if replacer.any_replacement {
       simplify::remove_unused_definitions(body);
   }
   replacer.any_replacement
   ```
   The `while` loop iterates so chains of borrows (`r2 = &(*r1).field` after `r1 = &base`) collapse transitively once outer layers become direct SSA borrows.

#### 3.2 The Three Soundness Pillars of `compute_replacement`

`compute_replacement` (`ref_prop.rs:146-358`) inspects SSA locals satisfying `ty.is_any_ptr()` (`&T`, `&mut T`, `*const T`, `*mut T` at `ref_prop.rs:228`) whose unique SSA definition is `Rvalue::Ref(_, _, place)`, `Rvalue::RawPtr(_, place)`, or a copy/move `Rvalue::Use(Operand::Copy(place) | Operand::Move(place))` from another SSA local (`ref_prop.rs:243-282`), flagging `needs_unique = ty.is_mutable_ptr()` (`&mut T` and `*mut T` at `ref_prop.rs:234`):

1. **Pillar 1 — Place Offset & Allocation-Generation Stability (`is_constant_place`, `ref_prop.rs:193-203`):**
   Every projection element in `place` must satisfy `PlaceElem::is_stable_offset` (ruling out `ProjectionElem::Index(idx)` whose index local `idx` could mutate between borrow creation and dereference use!), **and** the base `place.local` must either be a dereference of an immutable SSA pointer (`(*ssa_ptr)...` where `ssa.is_ssa(place.local)`) or have **at most one `StorageLive` execution** (`storage_live.has_single_storage(place.local)` in `ssa.rs:479-520`, ruling out loops where `StorageDead(x); StorageLive(x)` allocates a fresh stack generation `gen + 1` while an old reference `r = &x` still points to generation `gen`, as proved necessary by Counterexample 2 `ce2_refprop_into_storage_dead_target_dangling_ub`!).
2. **Pillar 2 — Target Liveness Across `StorageDead` (`MaybeStorageDead`, `ref_prop.rs:161-163, 205-217, 455-463`):**
   - If `place` is a **direct local projection** (`!place.is_indirect()`, e.g., `r = &x.0`), `compute_replacement` runs `MaybeStorageDead` dataflow (`rustc_mir_dataflow::storage::MaybeStorageDead`) lazily and checks whether `x` can possibly be `StorageDead` at **any** reachable statement where `r` is used (`ref_prop.rs:297-315`). If `maybe_dead.contains(target_local)` holds at any use of `r`, `r` is rejected (`Value::Unknown`). Without this check, rewriting `*r` to `x` after `StorageDead(x)` would replace a dangling-pointer dereference in Miri with an illegal MIR access to a dead local (or worse, if `StorageLive(x)` ran again without `has_single_storage`, silently read the new generation!).
   - If `place` is a **reborrow** (`place.is_indirect()`, i.e., `r = &(*y).0`), `y` is a reference/pointer local (say `&T` or `*const T`). Substituting `*r -> (*y).0` extends uses of `y` past `StorageDead(y)`! To preserve MIR well-formedness without invalidating the pointee allocation (which belongs to `*y`, not to the stack slot holding pointer `y`!), `Replacer` inserts `y` into `storage_to_remove` (`ref_prop.rs:420-425`) and rewrites all `StorageLive(y)` and `StorageDead(y)` statements to `nop` (`ref_prop.rs:455-463`), keeping pointer local `y` permanently live for the entire function body (`StorageLive` at function entry for arguments or implicit permanent slot for non-`StorageLive` locals).
3. **Pillar 3 — All-or-Nothing `&mut` Uniqueness Closed Under `ssa.meet_copy_equivalence` (`fully_replaceable_locals`, `ref_prop.rs:234-240, 345-348, 361-375`):**
   Why can `ReferencePropagation` replace *some* uses of a shared reference `r: &T` while leaving `r = &x` alive (e.g., when `r` is also passed to `sink(r)`), yet **refuses** to perform any replacement through `r: &mut T` unless **every single use** of `r` AND **every copy-equivalent alias** `r2 = copy r` can be completely eliminated (`fully_replaceable_locals.contains(local)`)?
   ```rust
   // compiler/rustc_mir_transform/src/ref_prop.rs:361-375 (c7d5ba59d)
   fn fully_replaceable_locals(ssa: &SsaLocals) -> BitSet<Local> {
       let mut replaceable = BitSet::new_empty(ssa.num_locals());
       for local in ssa.locals() {
           if ssa.num_direct_uses(local) == 0 {
               replaceable.insert(local);
           }
       }
       ssa.meet_copy_equivalence(&mut replaceable);
       replaceable
   }
   ```
   Here `ssa.num_direct_uses(local)` (`ssa.rs:341-370`) counts uses of `local` *other than* `Deref` projections (`*local`) and SSA copy-class edges (`r2 = copy local`). `ssa.meet_copy_equivalence(&mut replaceable)` (`ssa.rs:383-397`) intersects `replaceable` across every connected component of `copy_classes`!
   - **Soundness reason (proved constructively in Counterexample 3 `ce3_partial_mut_refprop_interleaving_aliasing_unsound`):** Under Stacked Borrows and Tree Borrows, creating `r1 = &mut target` grants `r1` (and its bitwise copy `r2 = copy r1`) an exclusive child borrow tag `bid` (`Unique` / `Active`). If `ReferencePropagation` rewrote `*r1 = 42` to a direct parent write `target = 42` while `r2` survived (because `r2` was passed to `sink(r2)` or read via `*r2`), executing the direct write `target = 42` accesses the parent tag and **invalidates `bid`**, causing the subsequent read/call on `r2` to trigger **immediate Undefined Behavior in a 100%-defined source program**! Only when the entire copy-equivalence class `{r1, r2, ...}` has zero escaping/direct uses can `remove_unused_definitions` delete `r1 = &mut target` and `r2 = copy r1` altogether, eliminating `bid` completely.

#### 3.3 Live Pass-Ordering Discovery: Why `let r = &p; r.0 + r.1` Blocks SROA Even at `-C debuginfo=0`

In `compiler/rustc_mir_transform/src/lib.rs:750-775` (`c7d5ba59d`; `L734-759` in `14210df0e`), the `@mir_opt_level >= 2` pipeline runs in this exact sequence:
1. `ReferencePropagation` (`lib.rs:751`), calling `simplify::remove_unused_definitions(body)` at the end of each `propagate_ssa` iteration (`ref_prop.rs:132`);
2. `SingleUseConsts` (`lib.rs:752`);
3. `ScalarReplacementOfAggregates` (`lib.rs:754`);
4. `SimplifyLocals::BeforeConstProp` (`lib.rs:755`);
5. `DeadStoreElimination::Initial` (`lib.rs:756`);
6. ... (16 passes) ...
7. `StripDebugInfo` (`lib.rs:773`).

Look inside `simplify::remove_unused_definitions` (`compiler/rustc_mir_transform/src/simplify.rs:526-556` in `c7d5ba59d`):
```rust
// We don't handle debugging information here, these are in DSE.
let always_used_locals = debuginfo_locals(body);
```
Even when `rustc` is invoked with `-C opt-level=2` and **no `-g` (`debuginfo = 0`)**, `rustc_mir_build` unconditionally populates `body.var_debug_info` (`debug r => _6;`) for every named user variable binding so borrowck diagnostics and MIR dumps have variable names, and `StripDebugInfo` only strips `var_debug_info` at `lib.rs:773`—**19 passes after `ScalarReplacementOfAggregates`**!
- In `refprop_anon_borrow_unlocks_sroa` (`let p = Pair(x, y); (&p).0.wrapping_add((&p).1)`), the two `&p` borrows live in compiler temporaries with **no** `VarDebugInfo` entry. After `ReferencePropagation` rewrites `(*_4).0 -> _3.0` and `(*_6).1 -> _3.1`, `remove_unused_definitions` immediately deletes `_4 = &_3` and `_6 = &_3`. Entering `ScalarReplacementOfAggregates`, `_3` (`p`) is no longer address-taken, so `SROA` flattens `_3` into scalars and reduces field projections to **`0`**!
- In `refprop_named_borrow_blocked_by_debuginfo` (`let p = Pair(x, y); let r = &p; r.0.wrapping_add(r.1)`), `ReferencePropagation` identically rewrites `(*_4).0 -> _3.0` and `(*_4).1 -> _3.1`, leaving `_4` (`r`) with zero statement uses—**but `debug r => _4` keeps `_4` in `always_used_locals`**, so `remove_unused_definitions` leaves `_4 = &_3;` in `bb0`! Entering `ScalarReplacementOfAggregates` two passes later, `excluded_locals(body)` (`value_analysis.rs:1044`) sees `_4 = &_3`, marks `_3` (`p`) as address-taken, and **`ScalarReplacementOfAggregates` completely skips `p` (`sroa_changed_mir = false`, `2` field projections survive)**—only two passes *later* does `DeadStoreElimination::Initial` finally delete `_4 = &_3`, after `ScalarReplacementOfAggregates` has already finished for the entire compilation!

---

### 4. `ScalarReplacementOfAggregates` (`sroa.rs`), Controlled Litmus Suite (Part B), and Full-Crate `zerocopy` Pass Census (Part C)

`Basis: source + execution + derived`

#### 4.1 `ScalarReplacementOfAggregates` Eligibility, Exclusions, and Iterative Fixed Point (`sroa.rs`)

`ScalarReplacementOfAggregates` (`compiler/rustc_mir_transform/src/sroa.rs`) runs at `ctx.mir_opt_level() >= 2` (`sroa.rs:18-20` in `c7d5ba59d`; `L14-16` in `14210df0e`), immediately returning without modifying coroutine bodies (`if body.coroutine.is_some() { return; }`, `sroa.rs:27-29`, avoiding state-machine local explosion across `Yield` suspension points).

1. **Address-taken exclusion (`excluded_locals`, `sroa.rs:31`; `value_analysis.rs:1037-1055`):**
   Before entering the flattening loop, `sroa` computes `let excluded = excluded_locals(body);`, marking every local visited under `PlaceContext::is_address_of()` (`Rvalue::RawPtr`, i.e., `&raw const` / `&raw mut`) or `PlaceContext::is_borrow()` (`Rvalue::Ref`, i.e., `&` / `&mut`). Because `ReferencePropagation` runs three slots earlier (`lib.rs:751` -> `754`), any local whose borrows were completely eliminated—*and* deleted by `simplify::remove_unused_definitions`—becomes eligible for SROA!
2. **Per-iteration escape and type-category exclusions (`escaping_locals`, `sroa.rs:56-137`):**
   Inside `loop` (`sroa.rs:33-45`), `escaping_locals(tcx, typing_env, body, &excluded)` initializes a `DenseBitSet` containing:
   - `Local::ZERO..=Local::from_usize(body.arg_count)` (`sroa.rs:58`: return place `_0` and ABI parameters `_1..=_arg_count` cannot have their ABI signature split);
   - Address-taken `excluded` locals (`sroa.rs:59`);
   - Any local whose type fails structural single-variant field decomposition (`sroa.rs:61-76`):
     ```rust
     // compiler/rustc_mir_transform/src/sroa.rs:63-75 (c7d5ba59d)
     ty::Adt(def, _)
         if def.is_union()
             || def.is_enum()
             || def.is_like_maybe_dangling()
             || !def.can_project_fields(tcx) =>
     {
         escaping.insert(local);
     }
     ```
     Notice each of those four ADT exclusions carries a concrete soundness invariant:
     - **`def.is_union()`:** Union fields overlap in storage; splitting fields into independent locals destroys cross-field aliasing!
     - **`def.is_enum()`:** Multi-variant enums have variant-dependent layouts and discriminants (`Downcast` + `SetDiscriminant`).
     - **`def.is_like_maybe_dangling()` (`#[rustc_LayoutScalarValidRange...]` / `MaybeDangling<T>`):** `MaybeDangling<&u64>` intentionally suppresses live-allocation dereferenceability/aliasing validity checks on its inner `&u64` during whole-wrapper moves/copies; flattening `MaybeDangling<&u64>` into a bare `&u64` local re-imposes live-reference validity on every assignment and **introduces fresh UB into valid programs** (proved constructively in `sroa_maybeDangling_exclusion_necessary`, `RemoveZstsSroaAndRefPropSoundness.lean:3434-3437`)!
     - **`!def.can_project_fields(tcx)`:** Blocks `#[repr(simd)]` ADTs whose fields are vector lanes rather than independently addressable MIR projections.
     - Only `ty::Tuple(_)` and single-variant struct `ty::Adt`s passing those checks remain eligible; arrays (`[T; N]`), slices, and scalars are marked `escaping` (`sroa.rs:74`).
   - Finally, `EscapeVisitor` (`sroa.rs:91-137`) marks a local `escaping` whenever it has any projection **other** than `PlaceElem::Field(..)` at the root (`[PlaceElem::Field(..), ..]`), EXCEPT for four benign whole-local contexts where `ReplacementVisitor` knows how to expand all fields simultaneously:
     1. `NonUseContext::StorageLive` (`StorageLive(agg)` -> `StorageLive(l_0); ...; StorageLive(l_k)`),
     2. `NonUseContext::StorageDead` (`StorageDead(agg)` -> `StorageDead(l_0); ...; StorageDead(l_k)`),
     3. `NonUseContext::VarDebugInfo` (rewritten to composite `VarDebugInfoContents::Composite` fragment mappings at `sroa.rs:235-299`),
     4. Unprojected `MutatingUseContext::Store` on the LHS of `StatementKind::Assign(lhs, rvalue)` (`lhs.as_local()`) when `rvalue` is **either** `Rvalue::Aggregate(AggregateKind::Adt(..) | Tuple, fields)` **or** `Rvalue::Use(Operand::Copy(rhs) | Move(rhs))` (`sroa.rs:344-396`, lowered to field-by-field `l_i = op_i` or `l_i = copy/move (rhs.i)`!).
3. **Why the fixed-point `loop` (`sroa.rs:33-45`) runs multiple iterations:**
   - *Forward nested flattening:* Flattening `outer: Outer` (`Outer { inner: Inner, z: u64 }`) creates a fresh local `_inner: Inner`, which is itself flattened into `_x: u64` and `_y: u64` on the next iteration.
   - *Backward move/copy-chain unlocking:* In `let a = Outer { ... }; let b = a; b.inner.x + ...`, during Iteration 1 `a` appears on the RHS of `b = move a` (`NonMutatingUse`/`Move` unprojected -> `a` initially escapes!), while `b` only appears as LHS of `b = move a` and in `b.inner.x` (`b` does NOT escape!). Iteration 1 flattens `b`, rewriting `b = move a` into `_b_inner = move (a.0); _b_z = move (a.1)`—turning `a`'s whole-value move into pure `Field` projections! On Iteration 2, `a` no longer escapes and flattens completely as well!
   - Dead original locals have `local_decls` replaced with unit `()` (`tcx.types.unit`) by `all_dead_locals` (`sroa.rs:43, 425-441`).

#### 4.2 Controlled Litmus Suite Results (Part B)

Executing Part B of `support/probe_remove_zsts_sroa_refprop.py` (`rustc 1.98.0-nightly 14210df0e`, `-Copt-level=2 -Zmir-opt-level=2`) confirms every `ReferencePropagation` and `ScalarReplacementOfAggregates` interaction across 7 targeted litmus functions:

| Litmus Function | Pre-`ReferencePropagation` (`deref`, `field`) | Post-`ReferencePropagation` (`deref`, `field`) | Post-`ScalarReplacementOfAggregates` (`deref`, `field`, `other`) | Exact Pass Behavior Verified |
| :--- | :--- | :--- | :--- | :--- |
| `refprop_anon_borrow_unlocks_sroa` (`(&p).0 + (&p).1`) | `(2, 2)` | `(0, 2)` (`RP_changed = true`) | **`(0, 0, 0)` (`SROA_changed = true`, 100% pure!)** | Anonymous borrows `_7 = &_3`, `_9 = &_3` lack `VarDebugInfo`, so `remove_unused_definitions` deletes them immediately and unlocks `SROA` on `p` (`_3 -> _10, _11`) |
| `refprop_named_borrow_blocked_by_debuginfo` (`let r = &p; r.0 + r.1`) | `(2, 2)` | `(0, 2)` (`RP_changed = true`) | **`(0, 2, 0)` (`SROA_changed = false`!)** | `debug r => _6` keeps `_6 = &_3` alive past `remove_unused_definitions`, causing `excluded_locals` to block `SROA` on `p` (`_3.0` and `_3.1` survive) |
| `refprop_mut_fully_replaced` (`let r = &mut slot; ... let r2 = r; ...`) | `(4, 0)` | `(0, 0)` (`RP_changed = true`) | **`(0, 0, 0)` (`0` derefs!)** | Copy-equivalence class `{_3, _6}` (`r`, `r2`) has `num_direct_uses == 0`, so `fully_replaceable_locals` admits both and rewrites all 4 `*r`/`*r2` derefs to direct `_2` (`slot`) |
| `refprop_mut_escaped_blocks_partial` (`let r = &mut slot; *r += 1; let raw: *mut u64 = r; sink(raw);`) | `(3, 0)` | `(0, 0)` (`RP_changed = true`) | `(0, 0, 0)` (`_3` address-taken via `&raw mut _3`) | `rustc_mir_build` lowers `let raw: *mut u64 = r` as implicit reborrow `_7 = &raw mut (*_4)`, giving `_4` (`r`) `num_direct_uses == 0` so `(*_4)` rewrites cleanly to `_3` (`_7 = &raw mut _3`) |
| `sroa_multi_iter_nested_and_move` (`let a = Outer { inner: Inner { x, y }, z }; let b = a; ...`) | `(0, 5)` | `(0, 5)` (`RP_changed = false`) | **`(0, 0, 0)` (`SROA_changed = true`, 100% pure!)** | Multi-iteration `loop` flattens `b`, unlocks `a`, and flattens nested `Inner` into pure scalar locals (`_15, _17, _18, _19, _20, _21`) |
| `sroa_excluded_union_and_enum` (`WordOrBytes` union + `TagOrVal` enum) | `(0, 2)` + `1` downcast | `(0, 2)` + `1` downcast | `(0, 2, 1)` (`SROA_changed = false`) | `def.is_union()` and `def.is_enum()` both excluded by `escaping_locals` |
| `sroa_excluded_address_taken` (`let raw_first = &raw const p.0; *raw_first + p.1`) | `(1, 2)` | `(0, 3)` (`RP_changed = true`) | `(0, 3, 0)` (`SROA_changed = false`) | `ReferencePropagation` propagates `(*_6)` through `Rvalue::RawPtr` (`_6 = &raw const (_3.0)` -> `_7 = copy (_3.0)`), while `debug raw_first => _6` retains `_6 = &raw const (_3.0)` and blocks `SROA` on `p` |

Notice three subtle MIR-level behaviors directly visible in the preserved post-`ScalarReplacementOfAggregates` dumps (`support/probe_results.json`, `part_b_refprop_and_sroa_mir_litmus.*.final_sroa_after_mir`):
- **Anonymous vs. `VarDebugInfo`-pinned borrows:** In `refprop_anon_borrow_unlocks_sroa`, `p` (`_3: Pair`) is completely flattened into `_10: u64` and `_11: u64` with composite debuginfo `debug ((p: Pair).0: u64) => _10; debug ((p: Pair).1: u64) => _11;`, whereas in `refprop_named_borrow_blocked_by_debuginfo`, `debug r => _6` keeps `_6 = &_3;` in `bb0` right across `ScalarReplacementOfAggregates`, leaving `_3 = Pair(move _4, move _5); _7 = copy (_3.0: u64); _8 = copy (_3.1: u64);` unflattened.
- **Why surviving `_3 = &mut _2` in `refprop_mut_fully_replaced` prior to `DSE` is sound:** In `refprop_mut_fully_replaced`, `debug r => _3` and `debug r2 => _3` temporarily keep the dead statement `_3 = &mut _2;` in `bb0` until `DeadStoreElimination::Initial` (`lib.rs:756`). Unlike partial `&mut` replacement (where a surviving operational read/call on `r2` faults after direct mutation of `_2`), an unused dead borrow `_3 = &mut _2` followed by direct accesses to `_2` is 100% sound under both Stacked Borrows and Tree Borrows: the first direct read `_5 = copy _2` simply pops/disables `_3`'s tag, and `_3` is never dereferenced or passed anywhere again (`VarDebugInfo` is non-operational metadata).
- **Implicit reborrow on `&mut T -> *mut T` coercion vs. direct call escape:** In `refprop_mut_escaped_blocks_partial` (`let raw: *mut u64 = r; sink(raw);`), `rustc_mir_build` lowers the `&mut u64 -> *mut u64` coercion as `_7 = &raw mut (*_4);` rather than `Move(_4)`. Because `_4` (`r`) is only ever used under `ProjectionElem::Deref` (`*r += 1` and `&raw mut (*_4)`), `ssa.num_direct_uses(_4) == 0`, allowing `ReferencePropagation` to rewrite `&raw mut (*_4)` into `_7 = &raw mut _3` so `_7` borrows directly from `slot` (`_3`) *after* `_3` was incremented! By contrast, passing `r: &mut u64` directly to a callee `sink_mut(r: &mut u64)` without `*r` produces `ssa.num_direct_uses(r) == 1 > 0`, where `fully_replaceable_locals` blocks replacement (`ce3_partial_mut_refprop_interleaving_aliasing_unsound`).

#### 4.3 Full-Crate `google/zerocopy` (`v0.8.64`) MIR Pass Census Across Two `rustc` Versions (Part C)

`google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0` (`v0.8.64`) is an ideal real-world benchmark for `RemoveZsts`, `ReferencePropagation`, and `ScalarReplacementOfAggregates` because its core pointer abstraction `Ptr<'a, T, I>` wraps `PtrInner<'a, T>` (`NonNull<T>` + `PhantomData<&'a mut T>`) paired with zero-sized invariant phantom markers `(I::Aliasing, I::Alignment, I::Validity)`.

Table 4.3a records the live 6-pass trajectory across all **`4,476` MIR bodies** of `zerocopy` on `rustc 1.98.0-nightly (14210df0e)` (`support/probe_results.json`, `part_c_zerocopy_mir_pass_census`), and Table 4.3b compares the 3-pass census across all **`4,302` MIR bodies** on `rustc 1.102.0-nightly (3ef0c22cd)`:

**Table 4.3a — `google/zerocopy@907b9175fee0` (`4,476` MIR bodies) on `rustc 1.98.0-nightly (14210df0e)`:**

| Pass Checkpoint (`-Copt-level=2 -Zmir-opt-level=2`) | Bodies Modified by Pass | Pure Projection-Free & Ref-Free Bodies | Total `Field` Projections | Direct-Local `Field` (`_x.f`) | `Deref` Projections (`*_x`) | Other Projections (`Index`/`Downcast`) | Borrow/RawPtr Rvalues | ZST Const Ops |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Before `RemoveZsts`** | — | `2,718` (`60.72%`) | `5,290` | `2,707` | `2,477` | `769` | `1,013` | `3,721` |
| **After `RemoveZsts`** | `3,199` (`71.47%`) | `2,731` (`61.01%`, `+13`) | `4,749` (`-541`) | `2,607` (`-100`) | `2,380` (`-97`) | `769` (`0`) | `988` (`-25`) | `1,001` (`-2,720`) |
| **Before `ReferencePropagation`** | — | `2,729` (`60.97%`) | `4,637` | `2,609` | `2,452` | `751` | `988` | `1,001` |
| **After `ReferencePropagation`** | `825` (`18.43%`) | `2,731` (`61.01%`, `+2`) | `4,696` (`+59`) | `3,050` (`+441`) | **`1,807` (`-645`, `-26.3%`)** | `751` (`0`) | `965` (`-23`) | `1,000` (`-1`) |
| **After `ScalarReplacementOfAggregates`** | `837` (`18.70%`) | `2,732` (`61.04%`, `+1`) | `5,206` (`+510`) | **`2,430` (`-620`, `-20.3%`)** | `1,975` (`+168`) | `951` (`+200`) | `965` (`0`) | `1,000` (`0`) |
| **After `SimplifyLocals::BeforeConstProp`** | `1,569` (`35.05%`) | **`2,742` (`61.26%`, `+10`)** | **`4,024` (`-1,182`)** | **`1,701` (`-729`)** | `1,795` (`-180`) | `899` (`-52`) | `965` (`0`) | `955` (`-45`) |
| **After `DeadStoreElimination::Initial`** | `249` (`5.56%`) | **`2,742` (`61.26%`)** | `4,013` (`-11`) | `1,699` (`-2`) | `1,793` (`-2`) | `896` (`-3`) | `965` (`0`) | `955` (`0`) |
| **After `SimplifyLocals::Final`** | `760` (`16.98%`) | **`2,742` (`61.26%`)** | **`3,691` (`-1,599` net)** | **`1,637` (`-1,070` net)** | **`1,771` (`-706` net)** | `822` | `964` | `805` |

**Table 4.3b — Cross-Version Comparison on `rustc 1.102.0-nightly (3ef0c22cd)` (`4,302` MIR bodies):**

| Pass Checkpoint (`3ef0c22cd`) | Pure Projection-Free & Ref-Free Bodies | Total `Field` Projections | `Deref` Projections (`*_x`) | ZST Const Ops | Cross-Version Explanation |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Before -> After `RemoveZsts`** | `2,615 -> 2,621` (`+6`, `60.93%`) | `3,676 -> 3,671` (`-5`) | `2,296 -> 2,285` (`-11`) | `3,648 -> 4,384` (**`+736`**) | `3ef0c22cd` added `&& place_for_ty.is_indirect()`, converting ZST operands to `const ZeroSized` (`+736`) instead of erasing direct `_x = ZST` assignments to `nop` (`-2,720` on `14210df0e`) |
| **Before -> After `ReferencePropagation`** | `2,621 -> 2,621` (`60.93%`) | `3,671 -> 3,724` (`+53`) | `2,357 -> 1,822` (**`-535`, `-22.7%`**) | `4,021 -> 3,766` (`-255`) | Eliminates `-535` derefs by turning `(*_ref).field` into direct `_base.field` (`+53` direct field projections) |
| **Before -> After `ScalarReplacementOfAggregates`** | `2,621 -> 2,644` (**`+23`, `61.46%`**) | `3,724 -> 3,637` (**`-87`**) | `1,822 -> 1,976` (`+154`) | `3,766 -> 3,766` (`0`) | Flattens local structs (`-87` net field projections immediately; `+23` completely projection-free & borrow-free bodies, `61.46%`) |

Notice the striking two-step synergy visible in Table 4.3a between `ScalarReplacementOfAggregates` and `SimplifyLocals::BeforeConstProp`:
- When `ScalarReplacementOfAggregates` flattens a `Ptr<'a, T, I>` local assigned from a function parameter `_1: Ptr<'a, T, I>` (`_local = move _1`), `ReplacementVisitor` (`sroa.rs:372-395`) expands that single assignment into separate assignments for every field of `Ptr`, including dead `PhantomData` marker fields (`_phantom = move ((_1.0).1: PhantomData<&mut T>)`), temporarily spiking total nested `Field` projections from `4,696` to `5,206` (`+510`) while immediately cutting direct-local `_local.field` projections by `-620` (`3,050 -> 2,430`).
- On the **very next pass** (`SimplifyLocals::BeforeConstProp`, `lib.rs:755`), `rustc` deletes every unused scalar/ZST fragment local created by `SROA`, collapsing `field_projections` by **`-1,182` in a single pass** (`5,206 -> 4,024`) and cutting `direct_local_field_projections` down to `1,701` (`-44.2%` below post-`ReferencePropagation`'s `3,050`!).

---

### 5. Constructive Lean 4 Mechanization (`support/RemoveZstsSroaAndRefPropSoundness.lean`)

`Basis: source + derived`

`support/RemoveZstsSroaAndRefPropSoundness.lean` (4,330 lines, 196,548 bytes, kernel-checked under Lean `v4.34.1` commit `5045d0056413266e57c625dcd7c365b10e377c52`) mechanizes the exact operational semantics, side conditions, refinement/bisimulation theorems, and sharpness counterexamples for all three passes without external libraries (`0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec` constants in the compiled `Environment`).

#### 5.1 Theorem-to-Upstream-Source Correspondence Inventory

| Lean 4 Declaration (`RemoveZstsSroaAndRefPropSoundness.*`) | Lines | Axioms (`#print axioms`) | Upstream `rustc` / Miri Counterpart & Mechanized Guarantee |
| :--- | :--- | :--- | :--- |
| `shouldRunPass`, `miri_default_args_suppress_checkAlignment_and_run_removeZsts`, `miri_force_enable_checkAlignment_restores_pass` | `L152–L214` | `[]` (pure kernel reduction) | `pass_manager.rs:256-285` + `src/tools/miri/src/lib.rs:200-218`: proves `MIRI_DEFAULT_ARGS` suppresses `CheckAlignment` for every `ubChecks : Bool` (`-Zub-checks=yes` included), suppresses `RemovePlaceMention` via `mirPreserveUb = true`, runs `RemoveZsts` at `mirOptLevel = 1`, and restores `CheckAlignment` when `+CheckAlignment` is appended afterward. |
| `checkDerefAlloc`, `checkIndirectLoadStore`, `null_unit_load_and_store_valid`, `dangling_aligned64_zst_load_and_store_valid`, `any_init_ptr_zst_align_one_valid` | `L349–L405` | `[]` / `[propext]` | `memory.rs:519-566` + `place.rs:549-572`: `size == 0` skips allocation lookup while enforcing `isAligned addr align`; proves `*(null as *const ())`, `*NonNull::<Aligned64Zst>::dangling()`, and **every** initialized pointer at layout `(0, 1)` succeed without UB (constructive `addr % 1 = 0` via `Nat.mod_lt`, zero `omega`). |
| **`removeZstsStmt_forward_codegen_refinement`** (Main Theorem 1a) | `L957–L1229` | `[propext]` | `remove_zsts.rs:108-152`: proves unconditional `removeZstsStmt` is a **sound forward UB-refining optimization** across ALL alignments (`align == 1` and `align > 1`) and both `deinitOnMove ∈ {false, true}`: whenever `execZstStmt` succeeds on `src`, `removeZstsStmt` succeeds on `tgt` and preserves `ZstObsRel` (exact `memVars` and non-ZST `locals`). |
| **`removeZsts_indirect_align_one_bidirectional_iff`** (Main Theorem 1b) | `L1232–L1261` | `[propext]` | Exact `align == 1` boundary: whenever `env p = .rawPtr (.zst 1)` and `p` holds an initialized `PtrVal` `pv` (arbitrary address/provenance), `removeZstsStmt` satisfies **exact bidirectional outcome equality** (`execZstStmt` before == after) for both `*p = ()` and `dst = copy (*p)`. |
| **`removeZstsCertifiedStmt_bidirectional_equivalence`** (Main Theorem 1c) | `L1391–L1469` | `[propext]` | Certified UB-preserving `RemoveZsts` design (`preserveUb = true` keeps indirect ops; `preserveUb = false` requires `align == 1 && ptrConfirmedInit p` under `PtrInitSound`): proves **exact bidirectional state and UB identity** across all layouts and alignments. |
| **`ce1_remove_zsts_erases_misaligned_align64_zst_ub`** (Counterexample 1) | `L1499–L1515` | `[propext]` | Constructive witness (`Aligned64Zst` at `addr = 1`): pre-`RemoveZsts` write `*p = Aligned64Zst` and read `v = *p` both fault with `.ub (.misalignedAccess 1 64)`; upstream `removeZstsStmt` erases both to `.ok`, while `removeZstsCertifiedStmt` preserves `.ub (.misalignedAccess 1 64)`. |
| **`sroaFlattenStmt_exact_bisimulation`** & **`sroaFlattenProg_exact_bisimulation`** (Main Theorems 2a & 2b) | `L2483–L3423` | `[propext, Quot.sound]` | `sroa.rs:56-154, 302-422`: proves exact step and multi-statement trace bisimulation (`SroaBisimRel` on `.ok` AND bidirectional `.ub` equivalence) across `StorageLive`, `StorageDead`, scalar/field writes, `Rvalue::Aggregate`, and unprojected `Copy`/`Move` pair assignments, parametric in `deinitOnMove : Bool`. |
| `sroa_maybeDangling_exclusion_necessary` | `L3434–L3437` | `[]` | `sroa.rs:66`: proves why flattening `MaybeDangling<&T>` over a dead allocation (`allocLive = false`) turns a valid wrapper copy (`true`) into an invalid bare reference assignment (`false`). |
| **`refProp_shared_exact_bisimulation`** (Main Theorem 3a) | `L3629–L3687` | `[propext, Quot.sound]` | `ref_prop.rs:71-72, 193-217`: proves exact outcome equality (`execRefStmt` before == after) for `&target` substitution when `target` is live (`!maybeStorageDead`), at matching `StorageLive` generation `gen` (`has_single_storage`), with `activeMutBorrow = none`. |
| **`refProp_mut_step_bisimulation`** & **`refProp_mut_all_or_nothing_exact_bisimulation`** (Main Theorem 3b) | `L3774–L4232` | `[propext, Quot.sound]` | `ref_prop.rs:234-240, 361-375` + `ssa.rs:383-397`: proves exact bidirectional state bisimulation (`MutRefBisimRel`) and exact UB identity (`execRefProg = .ub err ↔ ...`) when an entire copy-equivalence class `inClass` of `&mut target` locals is replaced all-or-nothing. |
| **`ce2_refprop_into_storage_dead_target_dangling_ub`** (Counterexample 2) | `L4275–L4284` | `[]` | Constructive necessity of `MaybeStorageDead` (`ref_prop.rs:205`) and `has_single_storage` (`ref_prop.rs:196`): across `StorageDead(2)`, liveness-blind substitution turns `.danglingAfterStorageDead 2` into `.deadLocal 2`; across `StorageDead(2); StorageLive(2); _2 = 99`, generation-blind substitution **erases dangling-reference UB** and silently reads `99`! |
| **`ce3_partial_mut_refprop_interleaving_aliasing_unsound`** (Counterexample 3) | `L4321–L4328` | `[]` | Constructive necessity of `fully_replaceable_locals` + `ssa.meet_copy_equivalence`: on defined trace `_1 = &mut _0; _2 = copy _1; *_1 = 42; _3 = *_2` (`.ok`, `_3 = 42`), partial replacement (`_0 = 42` while `_2` survives) invalidates borrow capability `bid = 0` and **introduces fresh UB** `.ub (.mutBorrowAliasingViolation 0 0)`! |

#### 5.2 Forward Refinement vs. Backward UB Preservation vs. Forward Unsoundness

A subtle theoretical distinction—captured cleanly across Theorems 1a–3b and Counterexamples 1–3—governs how a verified compiler backend vs. a UB-detecting interpreter/verifier must treat these three passes:

1. **Forward UB-refining optimization (`src ≠ .ub ⟹ tgt ≈ src`, allowed in codegen, forbidden in UB checkers):**
   `RemoveZsts` on over-aligned `align > 1` indirect accesses (`ce1`) and generation-blind `ReferencePropagation` across `StorageDead; StorageLive` (`ce2` part 2) **strictly reduce** the set of executions that trigger UB (`src = .ub`, `tgt = .ok`). Under standard compiler correctness (`CompCert` / `Alive2` forward refinement, mechanized in `removeZstsStmt_forward_codegen_refinement`), turning a source-UB execution into a defined `nop` is 100% sound for machine-code generation because a valid source program never relied on the UB branch. However, for **Miri** (`-Zmir-preserve-ub`) and **Anneal verification condition (VC) generation** (which must prove the user's Rust code *never* triggers UB!), erasing UB before checking VCs is **unsound** (false-positive safety proof of buggy unsafe Rust!).
2. **Exact bidirectional bisimulation (`src = .ub ↔ tgt = .ub` and `src = .ok s₁ ↔ tgt = .ok s₂` with `R s₁ s₂`, sound for BOTH codegen AND VC generation):**
   `removeZstsCertifiedStmt` (`align == 1` + `PtrInitSound`), `sroaFlattenProg` (under `!addressTaken && !isUnionOrEnum && !isMaybeDangling && local > argCount`), `refPropSharedStmt` (under `has_single_storage && !maybeStorageDead`), and all-or-nothing `refPropMutProg` (under `fully_replaceable_locals` closed under `meet_copy_equivalence`) preserve **both** defined states **and** exact UB faults! Therefore, a verified MIR pre-pass enforcing these side conditions can safely normalize MIR *before* Anneal VC generation without masking a single source UB!
3. **Forward UB-introducing bug (`src = .ok` and `tgt = .ub`, unsound EVERYWHERE):**
   Flattening `MaybeDangling<&T>` (`sroa_maybeDangling_exclusion_necessary`) or partially replacing `&mut T` across an unclosed copy-equivalence class (`ce3_partial_mut_refprop_interleaving_aliasing_unsound`) **introduces fresh UB into a 100%-defined source program**, which would allow downstream LLVM optimizations or runtime checks to miscompile valid safe Rust!

---

### 6. Anneal Trusted-Boundary Implications (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

`Basis: source + derived`

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/correspondence/Trusted/Correspondence.lean`) connects every finding above directly to Anneal's soundness boundary:

1. **Current fail-closed MIR intake and ZST/move semantics in `Trusted.MirSemantics`:**
   - Anneal extracts post-cleanup runtime MIR prior to `run_optimization_passes` (i.e., **before** `RemoveZsts`, `ReferencePropagation`, and `ScalarReplacementOfAggregates`).
   - `Trusted.MirSemantics` currently rejects non-empty place projections fail-closed (`.error .unsupported` whenever `!place.projection.isEmpty` at `MirSemantics.lean:953, 962, 1270, 1407`) and rejects `Rvalue.ref`, `Rvalue.addressOf`, and `Rvalue.aggregateTuple` fail-closed (`MirSemantics.lean:1245-1315`).
   - On moves of direct locals, `Trusted.MirSemantics` sets `deinitMovedPlace := true` (`MirSemantics.lean:949-972`), updating the moved-from slot via `liveUninitSlot ty`: for zero-sized types (`ty.isZeroSized`), `liveUninitSlot` returns `.live (some .zstVal)` (`MirSemantics.lean:150-163`), whereas for non-ZST types it deinitializes the slot to `.live none` (more conservative than Miri's `deinitOnMove = false` runtime behavior, where unprojected scalar moves leave bytes intact until overwritten or `StorageDead`). Because `RemoveZstsSroaAndRefPropSoundness.lean` parameterizes both Section 1 (`execZstStmt`) and Section 2 (`execSroaStmt` / `sroaFlattenProg_exact_bisimulation`) over arbitrary `deinitOnMove : Bool`, our bisimulations hold **simultaneously** for upstream Miri (`deinitOnMove = false`) and Anneal `Trusted.MirSemantics` (`deinitOnMove = true`)!
2. **Quantified leverage of a certified SROA + RefProp + ZST pre-pass for Anneal:**
   As demonstrated in Part C (Table 4.3a/b), `61.26%` (`2,742 / 4,476` on `14210df0e`) to `61.46%` (`2,644 / 4,302` on `3ef0c22cd`) of all MIR bodies in `google/zerocopy` (`v0.8.64`) become **100% projection-free and borrow-free** once `RemoveZsts` + `ReferencePropagation` + `ScalarReplacementOfAggregates` + `SimplifyLocals` run—meaning a certified MIR-to-MIR normalization pre-pass can unlock verification of over three-fifths of `zerocopy`'s functions *without* expanding `Trusted.MirSemantics`'s core memory model! Furthermore, stripping dead `VarDebugInfo` references *before* `ScalarReplacementOfAggregates` (closing the `let r = &p` blocker documented in Section 3.3) unlocks even more bodies!
3. **Mandatory certification gates if Anneal runs or verifies MIR normalization pre-passes:**
   - **Never run upstream unguarded `RemoveZsts` prior to Anneal VC extraction:** Running `rustc`'s stock `RemoveZsts` (`-Zmir-opt-level >= 1`) before Anneal extracts MIR would silently erase misaligned `#[repr(align(N))]` ($N > 1$) indirect ZST reads/writes (`ce1`) and uninitialized ZST-pointer dereferences, allowing an unsafe Rust function with real UB to pass Anneal verification! Any pre-VC ZST pass in Anneal MUST enforce `removeZstsCertifiedStmt`'s exact guard (`align == 1 && ptrConfirmedInit`, Theorem 1c), or emit an explicit alignment/init proof obligation `isAligned pv.addr align` before folding `*p`.
   - **Never run Miri differential tests with `-Zmir-opt-level >= 1` (unless `+CheckAlignment` and `-RemoveZsts` are accounted for):** Any differential testing harness comparing Anneal's semantics against Miri must keep Miri's default `-Zmir-opt-level=0`.
   - **Enforce all three `ReferencePropagation` and four `SROA` side conditions:** Any verified borrow/aggregate normalizer targeting Anneal must check `has_single_storage`, `!maybeStorageDead`, copy-equivalence-closed `fully_replaceable_locals` for `&mut`, and `!isUnion && !isEnum && !isMaybeDangling && canProjectFields && !addressTaken && local > argCount`.

---

## Boundaries

`Basis: source + execution + derived`

1. **Unsized ZSTs (`[(); n]` slices, `str` slices of length 0, and `dyn Trait` backed by ZST implementors) (`known not to apply` to `RemoveZsts`):** `RemoveZsts::known_zst` (`remove_zsts.rs:76-94`) explicitly requires `!ty_and_layout.is_unsized() && ty_and_layout.is_zst()`. Fat pointers `*const [Aligned64Zst]` (`&[Aligned64Zst]`) have `is_unsized() == true`, so `RemoveZsts` leaves unsized slice dereferences untouched even though every element has size `0`; consequently, Miri continues to check slice pointer alignment at `-Zmir-opt-level=1` for unsized `[Aligned64Zst]`! Note that in `c7d5ba59d`, `CheckAlignment` (`check_alignment.rs:78-115`) also computes dynamic alignment for unsized slice/trait pointers via ptr-metadata, whereas in `14210df0e` (`check_pointers.rs:209-212`) `PointerFinder` restricted `-Zub-checks` to `pointee_ty.is_sized(...)`.
2. **`-Zmiri-check-raw-ptr` / strict raw-pointer alignment mode on `PlaceMention(*misaligned)` (`known not to apply` to default Miri):** Under default Miri flags (matching the Rust Reference `r[undefined.misaligned.load-store]`), `unsafe { let _ = *misaligned; }` (`PlaceMention(*misaligned)`) exits `0` at `-Zmir-opt-level=0` because `deref_pointer` defers `check_misalign` on raw pointers until load/store (`place.rs:512-515`). If a user passes experimental `-Zmiri-check-raw-ptr` (which sets `ref_tracking = true` on raw pointers), `deref_pointer` checks alignment eagerly during place evaluation; that non-default experimental Miri dialect was `not examined` in the empirical matrix.
3. **GVN (`gvn.rs`) and `InstSimplify` (`instsimplify.rs`) ZST interactions at `-Zmir-opt-level >= 2` (`not examined` in isolation):** While `MIRI_DEFAULT_ARGS` explicitly disables `-GVN` and `-ReferencePropagation`, `GVN` and `InstSimplify` also fold certain zero-sized constants and aggregate projections in standard `-O2` codegen. Their standalone behavior with `-RemoveZsts` disabled on `c7d5ba59d` was `not examined` empirically beyond the full `-Zmir-opt-level=2` pipeline in Parts B and C.
4. **Tree Borrows (`-Zmiri-tree-borrows`) vs. Stacked Borrows on partial `&mut` `ReferencePropagation` (`known not to apply` to `Foreign Write` survival on `Active` `&mut`):** Counterexample 3 (`ce3_partial_mut_refprop_interleaving_aliasing_unsound`) models an already-written (`Active` / `Unique`) `&mut target` capability `bid` (`*_1 = 42`) followed by an interleaved parent write and child read (`_3 = *_2`). Under **both** Stacked Borrows (`Unique` popped by parent write) and Tree Borrows (`Active` transitioned to `Disabled` by foreign parent write!), a subsequent child read `*_2` is immediate UB. (Under Tree Borrows alone, a *never-written* `Reserved` `&mut` survives foreign reads—and when `!Unpin`, foreign writes prior to activation—whereas `ce3` performs `*_1 = 42` first, activating the borrow under both models; `Reserved`-only Tree Borrows corner cases were `not examined` separately in Lean.)
5. **Arbitrary $N$-field and multi-block CFG loops in the Lean 4 `SROA` / `RefProp` models (`known not to apply` beyond finite unrolling / structural induction):** Section 2 of `support/RemoveZstsSroaAndRefPropSoundness.lean` mechanizes 2-field structs (`Field2 = {f0, f1}`) over arbitrary sequential statement lists (`List SroaStmt`), and Section 3 mechanizes arbitrary sequential traces (`List RefStmt`) within a single `StorageLive` epoch where `MaybeStorageDead` and `has_single_storage` hold. Generalizing `Field2` to `Fin n` is purely structural, while lifting `MutProgAdmittedAndDominated` from finite traces to cyclic CFG dataflow fixpoints requires composing standard monotone dataflow soundness for `MaybeStorageDead` and `SsaLocals` (`not examined` in `RemoveZstsSroaAndRefPropSoundness.lean`).
6. **Coroutine MIR bodies in `ScalarReplacementOfAggregates` (`unsupported` by `rustc` `SROA`):** As verified in `compiler/rustc_mir_transform/src/sroa.rs:27-29`, `ScalarReplacementOfAggregates` explicitly bails out on all coroutine/async state-machine bodies (`if body.coroutine.is_some() { return; }`).
7. **Whether upstream `rustc` / Miri will gate `RemoveZsts` on `!mir_preserve_ub` vs. adding `-RemoveZsts` to `MIRI_DEFAULT_ARGS` (`unknown`):** Primary-source evidence establishes that `RemoveZsts` omits `!ctx.opts.unstable_opts.mir_preserve_ub` (`remove_zsts.rs:12-14`) and `MIRI_DEFAULT_ARGS` omits `-RemoveZsts` (`src/tools/miri/src/lib.rs:200-218`). Whether upstream maintainers prefer adding `-RemoveZsts` to `MIRI_DEFAULT_ARGS`, guarding indirect ZST folding in `remove_zsts.rs` on `!mir_preserve_ub || align == 1`, or treating `-Zmir-opt-level >= 1` UB hiding in Miri as covered by Miri's general optimization warning is an upstream policy choice `unknown` from current repository sources.

---

## Evidence

All primary-source inspections, live compiler/Miri executions, and Lean 4 kernel verifications were acquired and validated on **2026-11-21** on `x86_64-unknown-linux-gnu` against immutable 40-hex Git revisions verified via the GitHub commits API.

### Primary Source Citations

1. **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (2026-05-31, `rustc 1.98.0-nightly`, `miri 0.1.0`, LLVM `22.1.6`):**
   - `compiler/rustc_mir_transform/src/remove_zsts.rs:10-12` (`is_enabled`: `sess.mir_opt_level() >= 1`), `L31-33` (`is_required`: `true`), `L76-94` (`known_zst`), `L104-112` (`visit_operand` folding ZST `Copy`/`Move` to `ConstValue::ZeroSized`), `L114-147` (`visit_statement` erasing ZST `StorageLive`/`StorageDead`/`Assign`/`PlaceMention`/`SetDiscriminant` to `nop`).
   - `compiler/rustc_mir_transform/src/check_alignment.rs:15-37, 74-147` (`CheckAlignment`, `insert_alignment_check`).
   - `compiler/rustc_mir_transform/src/check_pointers.rs:43-245` (`PointerFinder`: `ty::RawPtr` filter at `L190`, `!context.is_use()` skipping `PlaceMention` at `L193`, `is_sized` filter at `L209-212`).
   - `compiler/rustc_mir_transform/src/pass_manager.rs:214-240` (`should_run_pass`: `is_required()` short-circuit + reverse `mir_enable_passes` override).
   - `compiler/rustc_mir_transform/src/ref_prop.rs:62-64` (`mir_opt_level >= 2`), `L79-122` (`move_to_copy_pointers`, `while propagate_ssa`, `simplify::remove_unused_definitions`), `L132-344` (`compute_replacement`, `is_constant_place`, `has_single_storage`, `MaybeStorageDead`), `L347-361` (`fully_replaceable_locals` + `ssa.meet_copy_equivalence`), `L405-450` (`Replacer`, `storage_to_remove`).
   - `compiler/rustc_mir_transform/src/sroa.rs:14-41` (`mir_opt_level >= 2`, coroutine bailout, `excluded_locals`, fixed-point `loop`), `L52-133` (`escaping_locals`: `_0..=arg_count`, `is_union`, `is_enum`, `is_like_maybe_dangling`, `!can_project_fields`, `EscapeVisitor`), `L135-437` (`ReplacementMap`, `VarDebugInfoContents::Composite`, `ReplacementVisitor`, `all_dead_locals`).
   - `compiler/rustc_mir_transform/src/ssa.rs:212-220, 341-397, 479-520` (`SsaLocals`, `num_direct_uses`, `meet_copy_equivalence`, `StorageLiveLocals::has_single_storage`).
   - `compiler/rustc_mir_transform/src/value_analysis.rs:1037-1055` (`excluded_locals`).
   - `compiler/rustc_mir_transform/src/lib.rs:695` (`CheckAlignment`), `L722` (`RemoveZsts`), `L735` (`ReferencePropagation`), `L738` (`ScalarReplacementOfAggregates`), `L739` (`SimplifyLocals::BeforeConstProp`), `L740` (`DeadStoreElimination::Initial`), `L757` (`StripDebugInfo`).
   - `compiler/rustc_const_eval/src/interpret/memory.rs:519-566, 579-635` (`check_and_deref_ptr` `size == 0` early `Ok(None)`, `is_ptr_misaligned`, `is_offset_misaligned`).
   - `compiler/rustc_const_eval/src/interpret/place.rs:466-516` (`deref_pointer` caching `mplace.misaligned`, `get_place_alloc` / `get_place_alloc_mut` calling `check_misalign` before `size == Size::ZERO`).
   - `src/tools/miri/src/lib.rs:183-200` (`MIRI_DEFAULT_ARGS`) and `src/tools/miri/src/bin/miri.rs:460-485` (`MIRI_DEFAULT_ARGS` spliced before user args + optimization warning).
2. **`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (2026-11-11, `rustc 1.102.0-nightly`, LLVM `23.1.5`) & `rust-lang/rust` @ `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (2026-11-20 `HEAD`):**
   - `compiler/rustc_mir_transform/src/remove_zsts.rs:12-14` (`PassPolicy::optional(ctx.mir_opt_level() >= 1)`), `L108-116` (`visit_operand`), `L135-150` (`visit_statement` with `&& place_for_ty.is_indirect()` at `L145`).
   - `compiler/rustc_mir_transform/src/remove_place_mention.rs:12-14` (`PassPolicy::optional(!ctx.opts.unstable_opts.mir_preserve_ub)`).
   - `compiler/rustc_mir_transform/src/simplify.rs:132-133` (`CfgSimplifier` checking `mir_preserve_ub`), `L514-565` (`remove_unused_definitions` keeping `debuginfo_locals(body)` in `always_used_locals` at `L529, 554`).
   - `compiler/rustc_mir_transform/src/pass_manager.rs:88-100, 132-165, 256-285` (`PassPolicy`, `PassCtx`, `should_run_pass`).
   - `compiler/rustc_mir_transform/src/check_alignment.rs:15-18, 78-148` & `check_pointers.rs:43-251` (`PointerFinder` unsized metadata alignment).
   - `compiler/rustc_mir_transform/src/ref_prop.rs:76-465` & `sroa.rs:18-441` & `lib.rs:711, 738, 751, 754, 755, 756, 773`.
   - `compiler/rustc_const_eval/src/interpret/memory.rs:519-635`, `place.rs:480-572`, `step.rs:146-162`, `src/tools/miri/src/lib.rs:200-218`, `src/tools/miri/src/bin/miri.rs:466-490`.
3. **`rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:**
   - `src/behavior-considered-undefined.md:18-23` (`r[undefined.pointer-access]`), `L79-98` (`r[undefined.misaligned]`, `r[undefined.misaligned.load-store]`), `L103-112` (`r[undefined.dangling.def]` `size == 0` exemption).
   - `src/type-layout.md:1-65, 595-638` (zero-sized layouts and `#[repr(align(N))]`).
4. **`google/zerocopy` @ `907b9175fee081872ec883ca4709e6ad922f8ed0` (`v0.8.64`):**
   - `src/lib.rs` and `src/pointer/{ptr.rs,inner.rs}` (`4,476` MIR bodies on `14210df0e`; `4,302` MIR bodies on `3ef0c22cd`).
5. **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
   - `trusted/lean/Trusted/MirAst.lean:308-321, 455-490, 620-628, 732-740`.
   - `trusted/lean/Trusted/MirSemantics.lean:150-163` (`liveUninitSlot` ZST inhabitant preservation), `L949-972` (`deinitMovedPlace = true`), `L953, 962, 1245-1315, 1407` (fail-closed projection and borrow handling).
   - `trusted/correspondence/Trusted/Correspondence.lean:781-801`.
   - `vendor/lean-miri/Miri/Interpreter/Place.lean:455-510` & `vendor/lean-miri/Miri/Memory/Access.lean:160-245` (`checkAndDerefPtr`, `getPlaceAlloc`, `getPlaceAllocMut`).
6. **`leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):**
   - Official Lean 4 kernel toolchain verifying `support/RemoveZstsSroaAndRefPropSoundness.lean`.

### Preserved Package Support Artifacts

All executable probes, path-scrubbed JSON receipts, and Lean 4 formalization files are preserved self-contained under `support/`:

- `support/probe_remove_zsts_sroa_refprop.py` — Standalone Python 3.10+ empirical harness (743 lines, 24,677 bytes, SHA-256 `7c3a7c72e676150c1cb6c172dcfd6f420860aca27936e6ad2dd71ba4267f116f`) running Part A (8-specimen × 6-mode Miri + native `-Zub-checks` ZST matrix and `RemoveZsts` MIR diffs), Part B (7-function `ReferencePropagation` + `ScalarReplacementOfAggregates` litmus suite), and Part C (full-crate `zerocopy` MIR pass census across 6 pass checkpoints; supports `--zerocopy-lib-rs <path>` and `--skip-zerocopy`).
- `support/probe_results.json` — Complete path-scrubbed execution receipt (919 lines, 55,256 bytes, SHA-256 `5b6a3cd19062e3310b963913d90a3a51a3d4fcaacbe36a62eb23f832a8525596`).
- `support/RemoveZstsSroaAndRefPropSoundness.lean` — Standalone constructive Lean 4 (`v4.34.1`) mechanization (4,330 lines, 196,548 bytes, SHA-256 `9442846936aa6df76e9e55fb98cd00af08c9493a3574bbae2a9785b34d346558`).
- `support/check_lean.py` — Reproducible Lean 4 kernel & axiom audit script (201 lines, 7,970 bytes, SHA-256 `951274e6ecffbe48f33c3cace9d1e85910938f264b3fa44154a0c6399d8fab0a`) running `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, scanning stripped source for 11 forbidden tactic/construct patterns, auditing `#print axioms` on all 17 theorems/counterexamples, and inspecting `Lean.Environment.constants` for `0` `isUnsafe` / `._unsafe_rec` declarations.
- `support/lean_check_receipt.json` — Kernel verification receipt (76 lines, 2,698 bytes, SHA-256 `97203ee73a424c1c009db74060fb843ec10ceaee9ad1e8e46c617cada17b6753`; `all_checks_passed = true`, `main_exit_code = 0`, `axiom_audit_exit_code = 0`, `env_unsafe_decl_count = 0`, `forbidden_axioms_found = []`).

---

## Revalidation

`Basis: source + execution`

To cheaply determine whether these findings continue to hold on a newer `rustc` / Miri nightly, a newer `google/zerocopy` release, or an updated `joshlf/anneal` commit:

1. **Fastest Miri ZST UB-erasure & RefProp/SROA litmus probe (~8–12 seconds, no external checkout needed):**
   From the package directory, run:
   ```console
   python3 support/probe_remove_zsts_sroa_refprop.py --skip-zerocopy --out /tmp/rz_sroa_reval.json
   ```
   Inspect three sharp discriminators in `/tmp/rz_sroa_reval.json`:
   - **Discriminator 1 (Over-aligned ZST UB erasure in Miri `opt1`):** Compare `part_a_miri_zst_ub_erasure_matrix.surface_misaligned_align64_zst_write.modes`:
     - `miri_opt0_preserve_ub.rc == 1` vs. `miri_opt1_default_preserve_ub.rc == 0` and `miri_opt1_with_ub_checks_yes.rc == 0`. If `miri_opt1_default_preserve_ub.rc` flips from `0` to `1`, upstream either added `-RemoveZsts` to `MIRI_DEFAULT_ARGS` (`src/tools/miri/src/lib.rs`) or gated indirect ZST folding in `compiler/rustc_mir_transform/src/remove_zsts.rs` on `!mir_preserve_ub` / `align == 1`!
     - Confirm `surface_null_unit_read_black_box` and `surface_dangling_align64_zst_read` remain `rc == 0` at `miri_opt0_preserve_ub`, and `miri_opt1_force_enable_CheckAlignment.rc == 1` on `surface_misaligned_align64_zst_write`.
   - **Discriminator 2 (`VarDebugInfo` SROA blocker):** Compare `part_b_refprop_and_sroa_mir_litmus.refprop_anon_borrow_unlocks_sroa.sroa_changed_mir` (`true`, `field_projections == 0`) against `refprop_named_borrow_blocked_by_debuginfo.sroa_changed_mir` (`false`, `field_projections == 2`). If the latter flips to `true` (`0` projections), check whether `simplify::remove_unused_definitions` (`simplify.rs`) began stripping `VarDebugInfo` or whether `StripDebugInfo` / `DeadStoreElimination` moved ahead of `ScalarReplacementOfAggregates` in `compiler/rustc_mir_transform/src/lib.rs`.
   - **Discriminator 3 (Full `zerocopy` census, ~35–50 seconds when a `zerocopy` checkout is available):**
     ```console
     python3 support/probe_remove_zsts_sroa_refprop.py --zerocopy-lib-rs /path/to/zerocopy/src/lib.rs --out /tmp/rz_sroa_full_reval.json
     ```
     Check `part_c_zerocopy_mir_pass_census` to verify `RemoveZsts`, `ReferencePropagation`, `ScalarReplacementOfAggregates`, and `SimplifyLocals_before_const_prop` projection deltas and `after_pure_unprojected_noref_pct` (~`61%`).

2. **Targeted upstream source diff (~5 seconds when inspecting a `rust-lang/rust` tree without running Miri):**
   Diff these five regions against `rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`:
   - `compiler/rustc_mir_transform/src/remove_zsts.rs` (`policy`, `visit_operand`, `visit_statement`);
   - `src/tools/miri/src/lib.rs` (`MIRI_DEFAULT_ARGS`) and `compiler/rustc_mir_transform/src/pass_manager.rs` (`should_run_pass`);
   - `compiler/rustc_const_eval/src/interpret/{memory.rs,place.rs}` (`check_and_deref_ptr`, `deref_pointer`, `get_place_alloc`);
   - `compiler/rustc_mir_transform/src/{ref_prop.rs,ssa.rs,simplify.rs}` (`compute_replacement`, `fully_replaceable_locals`, `remove_unused_definitions`);
   - `compiler/rustc_mir_transform/src/{sroa.rs,lib.rs}` (`escaping_locals`, pass ordering among `ReferencePropagation`, `ScalarReplacementOfAggregates`, `SimplifyLocals::BeforeConstProp`, `DeadStoreElimination::Initial`, and `StripDebugInfo`).

3. **Revalidate the Lean 4 mechanization (~10–15 seconds):**
   ```console
   python3 support/check_lean.py --out /tmp/lean_reval_receipt.json
   ```
   Verify `all_checks_passed == true`, `main_exit_code == 0`, `axiom_audit_exit_code == 0`, `env_unsafe_decl_count == 0`, all `forbidden_token_counts == 0`, and `forbidden_axioms_found == []`.

4. **Revalidate Anneal trusted-boundary assumptions:**
   Inspect `trusted/lean/Trusted/MirSemantics.lean` and `cargo-anneal` MIR extraction in `joshlf/anneal` to confirm MIR continues to be captured prior to `RemoveZsts`, and verify that any newly introduced MIR projection/borrow normalizer enforces the side conditions mechanized in `support/RemoveZstsSroaAndRefPropSoundness.lean`.
