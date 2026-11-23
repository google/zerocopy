# Rustc CTFE Constant Interning, Mutability Enforcement, Dangling Rejection, and Cross-AllocId Provenance

## Summary

Compile-Time Function Evaluation (CTFE) in `rustc` allows arbitrary local stack mutation inside `const fn` and constant blocks, yet enforces a strict boundary when a constant finishes evaluating and its result memory graph is promoted into compiler-global immutable or static allocations. This boundary operates across four coordinated layers—MIR static safety checks (`rustc_const_eval::check_consts`), interpreter memory hooks (`CompileTimeMachine` in `rustc_const_eval::const_eval::machine`), recursive interning (`intern_const_alloc_recursive` in `rustc_const_eval::interpret::intern`), and recursive value validation (`const_validate_mplace` / `const_validate_place` in `rustc_const_eval::interpret::validity`):

1. **Three `InternKind` variants govern a two-tier `(base_mutability, inner_mutability)` lattice**: `InternKind` (`compiler/rustc_const_eval/src/interpret/intern.rs`) defines `Static(hir::Mutability)`, `Constant`, and `Promoted` (there is no separate `StaticMut` variant). `Constant` and `Promoted` freeze both root and inner allocations `(Not, Not)`. `Static(Mutability::Not)` freezes inner allocations while setting the root to `Mutability::Mut` iff `!ty.is_freeze(...)` (interior-mutable statics such as `static ATOMIC: AtomicU32`). Only `Static(Mutability::Mut)` (`static mut`) keeps both root and inner allocations `Mutability::Mut`.
2. **Interleaved ordering in `intern_and_validate` produces different diagnostics for dangling references vs. dangling raw pointers**: `eval_queries.rs` calls `intern_const_alloc_recursive` *before* `const_validate_mplace`, but matches `intern_result` *after* `const_validate_mplace` returns. Because `RawPtr` skips allocation liveness checks during validation, a dangling raw pointer (`const DANGLE_RAW: *const u32`) reaches `intern_result` and fails with `"encountered dangling pointer in final value of constant"` (no `E0080` error code), whereas a dangling shared reference (`const DANGLE_REF: &u32`) fails inside `check_safe_pointer` with `E0080` (`"encountered a dangling reference (use-after-free)"`). Conversely, an integer-cast pointer (`0x1000usize as *const u32`) carries `provenance = None`, introduces zero `ProvenanceMap` edges, and interns cleanly.
3. **`const OWNED_CELL: Cell<u32>` succeeds while inner `&UnsafeCell` and `&mut` fail via dual defenses**: For `const` items, `const_validate_mplace` initializes `CtfeValidationMode::Const { allow_immutable_unsafe_cell: true }` for `inner = false` (root value, which is copied at each use site) and flips `allow_immutable_unsafe_cell` to `false` at every dereference (`inner = true`). Safe escaping `&mut` and `&UnsafeCell` borrows are blocked statically by `check_consts` (`E0764` and `E0492`), while `unsafe` transmutes and `union` type puns into read-only memory are caught by CTFE validation (`E0080`, `"encountered \`UnsafeCell\` in read-only memory"` and `"encountered mutable reference or box pointing to read-only memory"`). Zero-sized allocations (`size == 0`) are explicitly exempted from CTFE validation's read-only mutability/cell checks (`ZST` exemption) and `Promoted` `&mut []` interning checks, even though MIR `check_consts` still rejects `&UnsafeCell::new(())` with `E0492`.
4. **The `const &AtomicU32` exception rests on `skip_recursive_check` preserving `.rodata` / `.data` separation**: In `CtfeValidationMode::Const`, `check_safe_pointer` sets `skip_recursive_check = true` when a reference targets `GlobalAlloc::Static(did)` with `alloc_actual_mutbl.is_mut() || tcx.is_foreign_item(did)`. This lets `const REF: &AtomicU32 = &ATOMIC` point to a mutable/interior-mutable static allocation without either mutating `.rodata` or tripping constant validation, while transmuting an *immutable* static (`static IMM: u32`) into `&UnsafeCell<u32>` fails `skip_recursive_check` (`alloc_actual_mutbl == Mutability::Not`) and is rejected (`E0080`). Meanwhile, `CompileTimeMachine::before_access_global` rejects *reading* mutable or interior-mutable statics during `const` evaluation (`ConstAccessesMutGlobal`, `E0080`).
5. **Cross-`AllocId` provenance (`CtfeProvenance`) guarantees linker relocation invariance**: With `CtfeProvenance::OFFSET_IS_ADDR = false`, `pointer.rs` packs `(alloc_id, immutable, shared_ref)` with invariant `immutable => shared_ref` and withholds concrete base addresses. MIR `check_consts` rejects raw pointer comparisons and pointer-to-integer casts upfront; interpreter intrinsics/operators enforce single-allocation bounds on non-zero `ptr.add` (`memory.rs` early-returns `Ok(None)` when `size == 0`, allowing `(0x1000usize as *const u8).add(0)`), single-`AllocId` provenance on `ptr_offset_from`, and dereference bounds on `wrapping_add`; and `CompileTimeMachine::binary_ptr_op` unconditionally rejects runtime-style pointer comparison even under `-Z unleash-the-miri-inside-of-you`.
6. **Empirical and kernel-checked confirmation**: All 30 compiled probes in `support/probe_ctfe_interning_provenance.py` matched observed compiler behavior on `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), and the 2,442-line Lean `v4.34.1` formalization (`support/CtfeInterningMutabilityAndProvenanceSoundness.lean`) kernel-checks 57 theorems (including 4 core soundness theorems and 10 exact differential witnesses) using only `[propext]`, with zero `sorryAx`, `Classical.choice`, `Lean.ofReduceBool`, `partial def`, `omega`, `bv_decide`, or `._unsafe_rec` definitions.

## Applicability

This report establishes primary-source compiler behavior, empirical execution behavior, normative specification alignment, formal soundness guarantees, and downstream verification boundaries across five pinned subjects:

1. **Upstream compiler source (`rust-lang/rust`, HEAD `277240238554297f93fa9ee3c7643dfa03ccbbb4`)**: Primary source analysis covers `compiler/rustc_const_eval/src/interpret/{intern.rs, validity.rs, memory.rs, operator.rs, intrinsics.rs}`, `compiler/rustc_const_eval/src/const_eval/{eval_queries.rs, machine.rs}`, `compiler/rustc_const_eval/src/check_consts/{check.rs, ops.rs, qualifs.rs}`, `compiler/rustc_const_eval/src/diagnostics.rs`, and `compiler/rustc_middle/src/mir/interpret/pointer.rs`.
2. **Executed toolchain (`rust-lang/rust`, `1.98.0-nightly`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`)**: All 30 compiler/binary probes in `support/probe_ctfe_interning_provenance.py` (`support/probe_results.json`) were compiled with `--edition=2024` (plus `-Z unleash-the-miri-inside-of-you` on the unleashed pointer-comparison probe) and executed natively where compilation succeeded.
3. **Version delta between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `277240238554297f93fa9ee3c7643dfa03ccbbb4`**: Direct diffs across both trees show that the core interning, mutability, `skip_recursive_check`, `CtfeProvenance` bit-packing, `before_access_global`, and provenance-checking logic are semantically identical, while refactorings shifted module paths, symbol names, and line numbers:
   - **Diagnostics module move**: `crate::errors` in `14210df0e` was renamed to `crate::diagnostics` on `277240238` (`interpret_intern.rs`, `const_eval_eval_queries.rs`, `const_eval_machine.rs`, `check_consts_check.rs`, with diagnostics structures residing in `diagnostics.rs`), plus `diag.span_context(...)` loops in `report_eval_error`.
   - **Method renames & ghost mode**: `const_validate_operand` (`14210df0e`, `eval_queries.rs:451`) was renamed to `const_validate_place` (`277240238`, `eval_queries.rs:497`); `Memory::validation_in_progress` (`14210df0e`, `interpret_memory.rs:141`) was generalized to `Memory::ghost_mode` (`277240238`, `interpret_memory.rs:141`).
   - **Query entry guards**: `277240238` adds `retry_codegen_mode_with_postanalysis` (`eval_queries.rs:26-52`, `381-385`, `427-431`), `ensure_monomorphic_enough(ty)?` (`eval_queries.rs:101`), and a `#[track_caller]` caller-location guard (`eval_queries.rs:118-123`); `DefKind::Const` / `DefKind::AssocConst` dropped brace struct fields (`eval_queries.rs:64-68`), and `Qualif` in `check_consts/qualifs.rs` removed default values for `IS_CLEARED_ON_MOVE` and `ALLOW_PROMOTED` while adding `PhantomDeref` to place projections (`qualifs.rs:301`).
   - **Line-number shifts**: `InternKind` is at `intern.rs:181` on `277240238` (`180` on `14210df0e`), `intern_const_alloc_recursive` at `204` (`203`), `span_bug!` at `350` (`349`), `intern_and_validate` at `eval_queries.rs:161` (`119`), `const_validate_mplace` at `478` (`432`), `allow_immutable_unsafe_cell` at `494` (`448`), `skip_recursive_check` at `validity.rs:730` (`752`), `"mutable reference or box pointing to read-only memory"` at `820` (`842`), `visit_value` at `1363` (`1367`), `guaranteed_cmp` at `machine.rs:280` (`278`), `binary_ptr_op` at `573` (`790`), and `before_access_global` at `676` (`897`).
4. **Normative specification (`rust-lang/reference`, `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`)**: Audited `src/const_eval.md` (`r[const-eval.const-expr.path-static]`, `r[const-eval.const-expr.borrows]`) and `src/items/static-items.md` (`r[items.static.intro]`, `r[items.static.storage-disjointness]`, `r[items.static.read-only]`) to identify where compiler behavior implements vs. sharpens Reference rules (notably ZST exceptions and `unsafe` transmute backstops).
5. **Downstream verifier TCB (`joshlf/anneal`, `c131b320eeeb26ef692e5afd5ec8db49ee518613`) & Lean mechanization (`leanprover/lean4`, `v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`)**: `trusted/lean/Trusted/MirAst.lean` (`490-550`) and `trusted/lean/Trusted/MirSemantics.lean` (`570-625`, `838-905`) establish that Anneal's verified MIR lowering currently admits only `.scalar` and `.zeroSized` `ConstLit` constants and rejects pointer/reference/static constants to `.unsupported`. The Lean `v4.34.1` model formalizes the compiler guarantees required if Anneal expands CTFE constant admission beyond scalars and ZSTs.

## Findings

### 1. CTFE Finality Pipeline: `eval_in_interpreter`, `intern_and_validate`, and the `InternKind` Mutability Lattice

Basis: source + execution + derived

Every constant or static evaluated in the MIR interpreter runs through `eval_in_interpreter` (`compiler/rustc_const_eval/src/const_eval/eval_queries.rs:450-475` on `277240238`), which initializes `CompileTimeMachine::new(CanAccessMutGlobal::from(is_static), CheckAlignment::Error)`. During body interpretation, stack locals live as mutable `MemoryKind::Stack` allocations inside `ecx.memory.alloc_map`, permitting full in-place writes through local `&mut` references (verified by `stack_mut_owned_cell_and_static_atomic_ok`: `sum_via_mut(8) + 6` evaluates to `X=42`).

At return, `eval_body_using_ecx` invokes `intern_and_validate` (`eval_queries.rs:161-210` on `277240238`, `119-168` on `14210df0e`), whose execution and diagnostic sequence is subtle and security-critical:

```rust
fn intern_and_validate<'tcx, R: InterpretationResult<'tcx>>(
    ecx: &mut CompileTimeInterpCx<'tcx>,
    cid: GlobalId<'tcx>,
    intern_kind: InternKind,
    ret: MPlaceTy<'tcx>,
) -> InterpResult<'tcx, R> {
    let intern_result = intern_const_alloc_recursive(ecx, intern_kind, &ret);
    const_validate_mplace(ecx, &ret, cid)?;
    match intern_result {
        Ok(()) => {}
        Err(InternError::DanglingPointer) => { /* emits DanglingPtrInFinal */ }
        Err(InternError::BadMutablePointer) => { /* emits MutablePtrInFinal */ }
        Err(InternError::ConstAllocNotGlobal) => { /* emits ConstHeapPtrInFinal */ }
        Err(InternError::PartialPointer) => { /* emits PartialPtrInFinal */ }
    }
    interp_ok(R::make_result(ret, ecx))
}
```

Three consequences follow directly from this control flow:

1. **Interning executes first (`eval_queries.rs:168`)**, moving reachable local allocations out of `ecx.memory.alloc_map` into global `tcx` memory (`set_alloc_id_memory` for `const`/`promoted`, or `intern_as_new_static` with `PerParentDisambiguatorState` for nested allocations of a `static` at `interpret/intern.rs:124-137`). Validation (`validity.rs:736`, `1078`) relies on this invariant: every live reachable allocation must already be present in `tcx.try_get_global_alloc(alloc_id)` by the time `const_validate_mplace` inspects it.
2. **Validation errors preempt `InternError` reporting (`eval_queries.rs:171-176`)**: Because `const_validate_mplace` uses `?` before `match intern_result`, any invalid reference, `UnsafeCell`, or `&mut` pointing to read-only memory emits rich `E0080` validation diagnostics with type paths and byte dumps before `intern_result` is inspected.
3. **`intern_result` acts as the backstop for allocations invisible to type-directed validation (`interpret/intern.rs:269-274`)**: Raw pointers (`*const T` / `*mut T`) and `union` fields containing provenance bypass recursive type validation, yet `alloc.provenance().ptrs()` exposes every relocation edge to `intern_const_alloc_recursive`, so a dangling raw pointer fails at `match intern_result` (`eval_queries.rs:178-185`) unless validation already failed first.

`InternKind` (`interpret/intern.rs:181-187`) has **exactly three variants** (no separate `StaticMut` variant exists):

| `InternKind` variant | Source context | `base_mutability` (root alloc) | `inner_mutability` (nested allocs) | `is_static` | Mutable-pointer safety check (`intern.rs:302-355`) | Observed probe behavior |
| --- | --- | --- | --- | --- | --- | --- |
| `InternKind::Constant` | `const` / `const { ... }` / anon const | `Mutability::Not` | `Mutability::Not` | `false` | Enforced on all newly interned non-dangling pointers (`!prov.shared_ref()`) | `const OWNED_CELL` ok (`X=42 CELL=12`); inner `&UnsafeCell`/`&mut` rejected |
| `InternKind::Promoted` | Promoted rvalue expression | `Mutability::Not` | `Mutability::Not` | `false` | **Skipped** (`intern_kind != InternKind::Promoted`, allows `&mut []`) | `ZST_MUT_PROMOTED_OK` ok (`ZST_MUT_LEN=0`) |
| `InternKind::Static(Mutability::Not)` | `static` item (`!mut`) | `Mutability::Not` if `ret.layout.ty.is_freeze(...)`, else `Mutability::Mut` | `Mutability::Not` | `true` | Enforced on nested allocations (`inner_mutability == Not`); root `DefKind::Static` handled by caller (`eval_static_initializer`), inner edges become nested `static` items | `static ATOMIC: AtomicU32` root `Mut` (`ATOMIC_PREV=77 ATOMIC_NOW=80`), inner tail exprs frozen |
| `InternKind::Static(Mutability::Mut)` | `static mut` item | `Mutability::Mut` | `Mutability::Mut` | `true` | Disabled (`inner_mutability == Mut`); nested allocs stay `Mut` | `static_mut_nested_mut_alloc_ok` mutates `&mut [10, 20]` to `[99, 20]` (`S_MUT_0=99 S_MUT_1=20`) |

In `prepare_alloc` (`interpret/intern.rs:58-95`), setting `mutability == Mutability::Not` freezes `alloc.mutability = Mutability::Not`, whereas setting `Mutability::Mut` asserts `alloc.mutability == Mutability::Mut` (`"we won't 'un-freeze' allocations ever"`). Additionally, for `InternKind::Static`, `base_alloc_id == alloc_id && is_static` short-circuits recursive worklist traversal (`intern.rs:279-285`) to tolerate self-referential statics (`recursive_interior_mut`), leaving validity checks to `const_validate_mplace`.

### 2. Why `const OWNED_CELL` Passes While Escaping `&UnsafeCell` and `&mut` Fail (`E0492`, `E0764`, `E0080`)

Basis: normative + source + execution + derived

Rust permits `const OWNED_CELL: Cell<u32> = Cell::new(10);` because every use of a `const` copies its value into the caller's own stack slot or destination (`c.set(c.get() + 2)` yields independent `CELL=12` per evaluation), whereas borrowing into interior-mutable or `&mut` memory across program-lifetime extension would forge shared global mutable state or alias LLVM `.rodata`. Compiler enforcement spans two independent layers plus a ZST carveout:

1. **Layer 1 — MIR static `check_consts` (`check_consts/check.rs:308-336`, `549-581`)**:
   - `place_may_escape` returns `false` inside `ConstContext::ConstFn` (`is_transient = true`, enabling `&mut` local borrows inside `const fn` as verified by `sum_via_mut`) and otherwise returns `!(place.is_indirect() || self.local_is_transient(place.local))`.
   - When `Rvalue::Ref(_, BorrowKind::Mut { .. }, place)` or `Rvalue::RawPtr(RawPtrKind::Mut, place)` may escape outside `ConstContext::Static(Mutability::Mut)`, `check_op(ops::EscapingMutBorrow)` emits `E0764` (`diagnostics.rs:202-216`): `"mutable borrows of temporaries that have their lifetime extended until the end of the program are not allowed"` (verified by `mut_ref_escaping_const_rejected`, `rc=1`). Inside `static mut`, `is_allowed = true` permits `&mut [10, 20]` (`static_mut_nested_mut_alloc_ok`, `S_MUT_0=99 S_MUT_1=20`).
   - When `Rvalue::Ref(_, BorrowKind::Shared | BorrowKind::Fake(_), place)` or `Rvalue::RawPtr(RawPtrKind::Const, place)` targets a place whose `HasMutInterior` qualifier (`qualifs.rs:84-137`, checking `!Freeze` structural containment) is true and `place_may_escape(place)` holds, `check_op(ops::EscapingCellBorrow)` emits `E0492` (`diagnostics.rs:266-280`): `"interior mutable shared borrows of temporaries that have their lifetime extended until the end of the program are not allowed"` (verified by `unsafe_cell_ref_in_const_rejected`, `rc=1`).

2. **Layer 2 — CTFE Value Validation (`const_validate_mplace` & `interpret/validity.rs`)**:
   If `unsafe` code (such as `transmute`, `*const T`, or a `union`) bypasses `check_consts` (note `CastKind::Transmute` and `*const T` casts are explicitly allowed operations in `check_consts/check.rs:598-620`, and `&u32` -> `&mut u32` directly trips the HIR lint `mutable_transmutes`, whereas routing `&1u32 -> *const u32 -> &mut u32` reaches CTFE!), `const_validate_mplace` (`eval_queries.rs:478-506`) tracks `inner: bool`:
   - Root value (`inner = false`): `CtfeValidationMode::Const { allow_immutable_unsafe_cell: true }`. Both `visit_value` (`validity.rs:1376`) and `visit_union` (`validity.rs:1316`) skip the `UnsafeCell`-in-read-only-memory error when `c.allow_immutable_unsafe_cell()` is `true`. Hence `const OWNED_CELL: Cell<u32> = Cell::new(10)` passes (`stack_mut_owned_cell_and_static_atomic_ok`).
   - After root validation, `inner` is set to `true` (`eval_queries.rs:502`) for every reference/box target queued in `ref_tracking` (`validity.rs:837-844`), setting `allow_immutable_unsafe_cell = false`. Any non-ZST `UnsafeCell` inside `visit_value` (`validity.rs:1376-1391`) or non-`Freeze` `union` inside `visit_union` (`validity.rs:1316-1328`) checks `self.in_mutable_memory(val)` (`validity.rs:1072-1091`, reading `tcx.global_alloc(alloc_id).mutability(...)`). Because `intern_const_alloc_recursive` already froze `Constant` allocations to `Mutability::Not`, `in_mutable_memory` returns `false` and raises `E0080`: `"at .<deref>, encountered \`UnsafeCell\` in read-only memory"`. Both direct type transmute (`unsafe_cell_transmute_in_const_rejected`) and `union CellOrInt` transmute (`unsafe_cell_union_transmute_in_const_rejected`) failed with that exact `E0080` diagnostic.
   - Independently of `UnsafeCell`, `check_safe_pointer` (`validity.rs:800-824`) checks non-zero-sized `PtrKind::Box` or `PtrKind::Ref(Mutability::Mut)` against `alloc_actual_mutbl == Mutability::Not` and fails with `E0080`: `"encountered mutable reference or box pointing to read-only memory"` (verified by `mut_ref_transmute_to_readonly_rejected`: `alloc3<imm>`).

3. **Layer 3 — Interning Safety Net (`intern.rs:302-355`)**:
   During worklist traversal in `intern_const_alloc_recursive`, whenever `intern_kind != InternKind::Promoted` and `inner_mutability == Mutability::Not`, every relocation edge to a newly interned (non-dangling, non-preexisting-global) allocation must satisfy `prov.shared_ref()`. Otherwise `found_bad_mutable_ptr` triggers a compiler ICE (`span_bug!` at `intern.rs:350`: `"the static const safety checks accepted a mutable pointer they should not have accepted"`), or `Err(InternError::BadMutablePointer)` under `-Z unleash-the-miri-inside-of-you`. Crucially, pointers to *already-global* allocations from other constants are skipped (`is_already_global && !just_interned.contains(&alloc_id)` at `intern.rs:307-316`) because global-mutability safety is governed by the target allocation's own interning.

4. **ZST Validation vs. Static Check Asymmetry**:
   `rust-lang/reference` (`r[const-eval.const-expr.borrows]`) states the lifetime-extension rule categorically without distinguishing zero-sized types, whereas the compiler exhibits an intentional split observed in probes `zst_promoted_mut_and_zst_cell_exceptions_ok` (`rc=0`) vs. `zst_unsafecell_direct_borrow_still_e0492_rejected` (`rc=1`):
   - **CTFE validation and promoted interning exempt ZSTs**: `check_safe_pointer` guards `&mut`/box mutability with `if size != Size::ZERO` (`validity.rs:800`), `visit_value` and `visit_union` guard the `UnsafeCell` read-only check with `if !zst` (`validity.rs:1380`, `1320`), and `intern.rs:302` exempts `InternKind::Promoted` specifically for promoted `&mut []`. Thus `const ZST_MUT_PROMOTED_OK: &[u8] = { let x: &mut [u8] = &mut []; x };`, `const ZST_CELL_TRANSMUTE_OK: &UnsafeCell<()> = unsafe { transmute(&()) };`, and `const ZST_MUT_TRANSMUTE_OK: &mut [u8; 0] = unsafe { transmute::<*const [u8; 0], _>(&[]) };` all compile and run (`ZST_MUT_LEN=0 ZST_CELL_SIZE=0 ZST_MUT_ARR_LEN=0`).
   - **MIR `check_consts` does NOT exempt ZSTs**: `const ZST_CELL_BORROW: &UnsafeCell<()> = &UnsafeCell::new(());` still triggers `HasMutInterior` (`!&UnsafeCell<()> : Freeze`), failing compilation with `E0492`.

### 3. The `const &AtomicU32` Boundary: `skip_recursive_check` vs. `ConstAccessesMutGlobal`

Basis: normative + source + execution + derived

Even though `const` evaluation must generally produce frozen read-only data (`ConstAccessesMutGlobal` forbids reading mutable globals during evaluation), Rust explicitly supports `static ATOMIC: AtomicU32 = AtomicU32::new(77); const STATIC_ATOMIC: &AtomicU32 = &ATOMIC;` as a compile-time handle to runtime-mutable global storage. Primary-source inspection explains both why this compiles safely and why reading through that pointer inside a `const` fails:

1. **Identity-only reference escape via `skip_recursive_check` (`validity.rs:761-795`)**:
   In `check_safe_pointer`, when `place.ptr()` resolves to `GlobalAlloc::Static(did)` (`assert!(!tcx.is_thread_local_static(did))`):
   - In `CtfeValidationMode::Const { .. }` (`validity.rs:785-794`):
     ```rust
     if alloc_actual_mutbl.is_mut() || self.ecx.tcx.is_foreign_item(did) {
         skip_recursive_check = true;
     }
     ```
     Because `static ATOMIC: AtomicU32` is `!Freeze`, its own `intern_const_alloc_recursive` ran under `InternKind::Static(Mutability::Not)` (`intern.rs:224-229`) and gave it `alloc_actual_mutbl == Mutability::Mut`. Validation of `const STATIC_ATOMIC: &AtomicU32` therefore validates the outer pointer non-null/aligned/liveness properties, sees `alloc_actual_mutbl.is_mut() == true`, skips descending into `ATOMIC`'s bytes (`skip_recursive_check = true`), and interns only the pointer-holding `const` allocation (`constEntry`) as immutable (`Mutability::Not`), leaving `ATOMIC` untouched in mutable static memory (`.data`/`.bss`). Meanwhile in `MIR` `check_consts`, taking `&ATOMIC` (`Static` `Place` in MIR or `Rvalue::Ref` over an existing static place / promoted) is permitted, unlike borrowing a newly created temporary `&AtomicU32::new(...)`.
   - In `CtfeValidationMode::Static` and `Promoted` (`validity.rs:769-784`): `skip_recursive_check = !nested`, skipping independent non-nested statics to avoid cyclic query evaluation while walking nested allocations (`DefKind::Static { nested: true, .. }`).

2. **Immutable `static` does NOT trigger `skip_recursive_check`**:
   When a `static IMM_STATIC: u32 = 99` is `Freeze` (`alloc_actual_mutbl == Mutability::Not`), `alloc_actual_mutbl.is_mut()` is `false`. Attempting `const BAD_CELL_TO_IMM_STATIC: &UnsafeCell<u32> = unsafe { transmute(&IMM_STATIC) };` skips neither the outer check nor recursive descent, hits `visit_value`, sees `in_mutable_memory == false`, and fails with `E0080: at .<deref>, encountered UnsafeCell in read-only memory` (`const_transmute_imm_static_to_unsafecell_rejected`, `rc=1`). Thus, an immutable `.rodata` static can never acquire mutable `UnsafeCell` aliasing via `const`.

3. **Raw `*mut` to `static mut` inside a `const` succeeds without reading, while any CTFE *read* of mutable globals fails (`E0080`)**:
   As demonstrated in `const_ref_to_static_atomic_and_ptr_to_static_mut_ok` (`rc=0`, stdout `REF_TO_STATIC=99 READ_IMM_STATIC=99 ATOMIC_PREV=5 ATOMIC_NOW=7 PTR_TO_MUT_STATIC_AFTER=456`), a `const` can bind `&IMM_STATIC`, copy `IMM_STATIC`'s value (`99`), bind `&ATOMIC_STATIC`, and bind `PTR_TO_MUT_STATIC: *mut u32 = &raw mut MUT_STATIC` (which `RawPtr` does not dereference during validation and `intern_const_alloc_recursive` accepts because `ATOMIC_STATIC`/`MUT_STATIC` already exist in `tcx` global allocations, hitting `is_already_global && !just_interned.contains(&alloc_id)` -> `continue` at `intern.rs:307-316`).
   By contrast, *reading* the contents of either `ATOMIC_STATIC` (via unsafe `*(&raw const ATOMIC_STATIC as *const u32)` in `const_read_atomic_static_rejected`) or `MUT_STATIC` (`unsafe { MUT_STATIC }` in `const_reading_mut_static_rejected`) fails during CTFE execution inside `CompileTimeMachine::before_access_global` (`const_eval_machine.rs:676-706`):
   - `is_write == true` unconditionally fails (`WriteToReadOnly` or `ModifiedGlobal`).
   - `is_write == false` succeeds only if `machine.can_access_mut_global == CanAccessMutGlobal::Yes` (inside a `static` initializer per `eval_queries.rs:465`) OR `alloc.mutability == Mutability::Not` (immutable `IMM_STATIC`); otherwise it fails with `Err(ConstEvalErrKind::ConstAccessesMutGlobal)` (`error[E0080]: constant accesses mutable global memory`).

### 4. Dangling Pointers vs. Integer-Backed Pointers at the Interning Boundary

Basis: source + execution + derived

During CTFE, freed locals are removed from `ecx.memory.alloc_map`, while pointer scalars carry `Option<CtfeProvenance>` (`pointer.rs:90-164` defines `CtfeProvenance(NonZero<u64>)` packing `ALLOC_ID_MASK` (`bits 0..61`), `SHARED_REF_MASK = 1 << 62`, and `IMMUTABLE_MASK = 1 << 63`, maintaining `immutable() => shared_ref()` via `as_immutable()`). Comparing four dangling/integer pointer shapes reveals an exact multi-layer boundary:

1. **Dangling local `*const u32` stored in a `const` (`dangling_alloc_raw_ptr_in_final_const_rejected`, `rc=1`)**:
   `let p = { let x = 42u32; &raw const x };` drops `x` (`StorageDead` frees `alloc_id` from `alloc_map`), leaving `p` with `prov = Some(alloc_id)`. Validation of `ty::RawPtr` (`validity.rs:917-934`) reads the pointer immediate and checks wide-pointer metadata if unsized, but deliberately does **not** verify that `alloc_id` is live. `const_validate_mplace` returns `Ok(())`. Execution reaches `match intern_result` (`eval_queries.rs:176-185`): earlier, `intern_const_alloc_recursive` pushed `prov` onto `todo` from `alloc.provenance().ptrs()` (`intern.rs:255`) and called `intern_shallow`, whose `alloc_map.swap_remove(&alloc_id)` returned `None` -> `Err(InternError::DanglingPointer)` (`intern.rs:113-114`). `rustc` emits `"error: encountered dangling pointer in final value of constant"` (specifically **without** an `E0080` code because `DanglingPtrInFinal` is a `NonConstEvalError`, not a validation `InterpError`).

2. **Dangling `&u32` stored in a `const` (`dangling_ref_rejected`, `rc=1`)**:
   Here `ty::Ref` calls `check_safe_pointer` (`validity.rs:732-755`). After `ptr_try_get_alloc_id` extracts `alloc_id`, `try_get_global_alloc(alloc_id)` returns `None` and `alloc_map.contains_key(&alloc_id)` is `false` (already freed). Validation aborts with `E0080: constructing invalid value of type &u32: encountered a dangling reference (use-after-free)`, preempting `intern_result` (which had already failed and returned `Err(DanglingPointer)`, as documented by `eval_queries.rs:173`: `"Only report this after validation, as validation produces much better diagnostics."`).

3. **Dereferencing a dangling local `*const u32` during CTFE (`dangling_raw_deref_rejected`, `rc=1`)**:
   Before interning even begins, `unsafe { *p }` executes `check_ptr_access` -> `get_live_alloc_size_and_align` (`interpret/memory.rs:481-566`, `967-977`), which detects that `alloc2` is dead and fails with `E0080: memory access failed: alloc2 has been freed, so this pointer is dangling`.

4. **Integer-cast pointer (`0x1000usize as *const u32`) stored in a `const` (`int_raw_ptr_stored_ok`, `rc=0`, `INT_PTR_ADDR=0x1000`)**:
   Casting `0x1000usize as *const u32` creates a scalar pointer with `prov = None` (`CastKind::PointerWithExposedProvenance`, allowed by `check_consts/check.rs:625-627`). Because `alloc.provenance()` stores only `(Offset, CtfeProvenance)` pairs for provenance-carrying pointers, no provenance edge is recorded in the serialized constant allocation, so `intern_const_alloc_recursive` sees zero edges and succeeds, and `ty::RawPtr` validation succeeds. Only dereferencing `*(0x1000usize as *const u8)` (`int_to_ptr_deref_rejected`, `rc=1`) fails inside `check_and_deref_ptr` (`memory.rs:537-539`) when `ptr_try_get_alloc_id` returns `Err(addr)` -> `throw_ub!(DanglingIntPointer)` -> `E0080: memory access failed: attempting to access 1 byte, but got 0x1000[noalloc] which is a dangling pointer (it has no provenance)`.

### 5. Cross-`AllocId` Provenance Enforcement, OOB Pointer Arithmetic, Pointer Comparisons, and Relocation Invariance

Basis: normative + source + execution + derived

Because CTFE runs before linking and relocation (`CtfeProvenance::OFFSET_IS_ADDR = false`, `pointer.rs:169`), constant evaluation cannot observe concrete ASLR or linker base addresses of allocations. Across the 13 probes in Category B, `rustc` enforces relocation invariance through five distinct mechanisms:

| Operation / Edge Case | Enforcing Layer & Source Location | Concrete Probe Behavior (`rustc 1.98.0-nightly`) | Soundness Rationale |
| --- | --- | --- | --- |
| In-bounds `ptr.add(2)` + deref on local array | `BinOp::Offset` (`interpret/operator.rs:326-357`), `check_and_deref_ptr` (`memory.rs:519-566`) | `provenance_valid_inbounds` (`rc=0`): `INBOUNDS_VAL=30` | Relative offset `8 < 16` stays inside single `AllocId` |
| `(0x1000usize as *const u8).add(0)` | `check_and_deref_ptr` **zero-size early exit** (`memory.rs:532-534`: `if size == 0 { return interp_ok(None); }`) | `int_to_ptr_zero_add_ok` (`rc=0`): `INT_PTR_ZERO_ADD=0x1000` | `0`-byte offset needs no provenance and preserves address (`0x1000 + 0`) |
| `(0x1000usize as *const u8).add(1)` | `check_and_deref_ptr` (`memory.rs:536-540`, `DanglingIntPointer`) | `int_to_ptr_nonzero_add_rejected` (`rc=1`): `E0080` `"0x1000[noalloc] which is a dangling pointer (it has no provenance)"` | Non-zero inbounds offset requires live provenanced allocation |
| OOB `arr.as_ptr().add(10)` on `[u8; 2]` | `check_and_deref_ptr` (`memory.rs:552-561`, `PointerOutOfBounds`) | `oob_ptr_add_rejected` (`rc=1`): `E0080` `"attempting to offset pointer by 10 bytes, but got alloc2 which is only 2 bytes from the end of the allocation"` | `inbounds` GEP semantics forbid stepping past `[0, alloc_size]` |
| OOB `ARR.as_ptr().wrapping_add(10)` stored vs. deref'd | `arith_offset` (`interpret/intrinsics.rs:426-435`) calls `wrapping_signed_offset`; deref hits `check_and_deref_ptr` (`memory.rs:552`) | `oob_wrapping_add_static_stored_ok` (`rc=0`, `OOB_WRAP_OFFSET=10`); `oob_wrapping_add_deref_rejected` (`rc=1`, `E0080`: `alloc2+0xa` out of 2-byte bounds) | LLVM allows non-`inbounds` offset computation within pointer width as long as memory is not accessed |
| `ptr.offset_from(origin)` same `AllocId` vs. different `AllocId` | `ptr_offset_from` (`interpret/intrinsics.rs:446-469`) checks `Err/Err` (two ints) or `Ok(a_id) == Ok(b_id)` | `offset_from_same_static_ok` (`rc=0`, `SAME_DIFF=2`); `offset_from_diff_alloc_rejected` (`rc=1`, `E0080`: `"not both derived from the same allocation"`) | Only intra-allocation distance is independent of linker base addresses |
| `ptr1 == ptr2` (distinct allocs or integer ptrs) | MIR `check_consts` (`check.rs:658-670`: `ops::RawPtrComparison`) | `ptr_cmp_different_allocs_rejected` & `ptr_cmp_int_ptrs_rejected` (`rc=1`: `"pointers cannot be reliably compared during const eval"`) | General pointer equality depends on linker/dedup addresses |
| `ptr1 == ptr2` under `-Z unleash-the-miri-inside-of-you` | `CompileTimeMachine::binary_ptr_op` (`machine.rs:573-580`) | `ptr_cmp_unleashed_runtime_binary_ptr_op_rejected` (`rc=1`, `E0080`: `"pointer arithmetic or comparison is not supported at compile-time"`) | Machine runtime fallback refuses pointer comparisons unconditionally |
| `ptr as usize` cast | MIR `check_consts` (`check.rs:622-624`: `CastKind::PointerExposeProvenance` -> `ops::RawPtrToIntCast`); runtime machine hook `expose_provenance` (`machine.rs:641-647`) | `ptr_to_int_cast_rejected` (`rc=1`: `"pointers cannot be cast to integers during const eval"`) | Exposing `alloc_id` addresses breaks compile-time determinism |

A subtle internal distinction exists in `const_eval_machine.rs:280-389` (`guaranteed_cmp`): although user `==` / `<` raw-pointer expressions are blocked by `check_consts` and `CompileTimeMachine::binary_ptr_op`, internal CTFE helper `guaranteed_cmp` can still decide equality in narrow linker-guaranteed cases: (a) pointer vs. integer when alignment or non-nullability prevents equality, (b) distinct alignment residues modulo `min(a.align, b.align)`, (c) two pointers into the *same* `GlobalAlloc::Static` (returning `(a_offset == b_offset) as u8` per `r[items.static.intro]` non-deduplication), and (d) two *strictly in-bounds* pointers into *different* `GlobalAlloc::Static` allocations (returning `0` / unequal per `r[items.static.storage-disjointness]`), while returning `2` ("unknown") for one-past-the-end static pointers, `GlobalAlloc::Memory` (which may overlap immutable statics or be deduplicated), functions/vtables, and `TypeId`. Note that the `check_ptr_access` `size == 0` early return in `interpret/memory.rs:532-534` explains why `(0x1000usize as *const u8).add(0)` passes while `.add(1)` fails `DanglingIntPointer`.

### 6. Kernel-Checked Lean `v4.34.1` Formalization (`CtfeInterningMutabilityAndProvenanceSoundness.lean`)

Basis: source + derived

`support/CtfeInterningMutabilityAndProvenanceSoundness.lean` (`2,442` lines, `102,954` bytes) mechanizes the `rustc` CTFE allocation graph (`MemState` splitting `locals` and `globals` with `MemWF` no-duplicate invariants), recursive worklist interning (`internShallow`, `internWorklist`, `internAllocRec`), type-directed validation (`validationModeFor`, `skipRecursiveCheck`, `validateVal`, `internAndValidate`), `check_consts` guards (`checkConstsBorrow`), global access gating (`canAccessMutGlobal`), provenance-checked pointer operations (`ptrInboundsAdd`, `ptrWrappingAdd`, `ptrDerefRead`, `ptrOffsetFrom`, `ptrRawCmp`), and concrete physical relocation layouts (`RelocLayout`, `ValidRelocLayout`, `evalCtfeSteps`, `evalCtfeAtLayout`).

Every `def` in the module is `noncomputable def` (`49` `noncomputable def`s, zero `partial def`, zero `deriving` clauses on recursive inductives, zero `omega`/`bv_decide`/`native_decide`/`Classical.choice`/`sorryAx`), verified directly by the Lean `v4.34.1` kernel (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) and audited via Lean MetaM (`distinct_axioms_used = [propext]`, `unsafe_recs = 0`, `theorems = 221` in environment, `57` file-level theorems).

Four core soundness theorems establish the mechanized invariants:

1. **Read-Only Immutability Soundness (`readonly_immutability_soundness`, L1698)**, supported by `internAllocRec_const_or_promoted_freezes` (L1504), `validateVal_inner_unsafeCell_requires_mut` (L1595), `validateVal_inner_unionCell_requires_mut` (L1622), and `validateVal_mutRef_target_mutable` (L1647):
   For any well-formed state `MemWF m`, if `internAndValidate fuel m kind rootTy rootVal baseId = .ok (m', justList)` with `kind = .constant ∨ kind = .promoted`, then `MemWF m'` holds, **every newly interned global allocation `q` is strictly immutable (`g.mutbl = .imm`)**, no non-ZST `UnsafeCell` succeeds validation behind `inner = true` on `q`, and no non-ZST `&mut` targeting `q` succeeds validation.

2. **Zero-Dangling-Local Interning Guarantee (`zero_dangling_local_interning_guarantee`, L1861)**, supported by `internShallow_rejects_missing_or_freed` (L1769), `internWorklist_head_rejects_dangling` (L1784), and `validateVal_rejects_dangling_ref` (L1823):
   Under `kind = .constant ∨ kind = .promoted` and `MemWF m`, a succeeding `internAndValidate` guarantees that every newly interned global allocation has `lifecycle = .live`, the root allocation `baseId` is `.live` in `globals`, and any root shared reference's target `pr.allocId` resolves in `lookupAny m'` to a `.live` entry.

3. **Mutable-Static Pointer Escape Separation Safety (`mutable_static_escape_separation_safety`, L1959)**:
   Given a live interior-mutable static allocation (`origin = .globalStatic false false`, `mutbl = .mutbl`, `size >= 4`, `alreadyGlobal = true`) and a distinct `localConst` root pointing to it as `&UnsafeCell<u32>`, `internAndValidate` **succeeds** (`ok (m', jList)`) via `skip_recursive_check`, preserving `atomicEntry` as mutable in `globals`, freezing `gConst.mutbl = .imm`, and proving `ptrDerefRead m' .constant ptrToAtomic 4 = .err .constAccessesMutGlobal`. Thus `.rodata` constant allocations and `.data`/`.bss` mutable static allocations remain strictly partitioned.

4. **Cross-`AllocId` Relocation Invariance (`cross_allocid_relocation_invariance`, L2107) and Physical Address Displacement / Disjointness (`physical_address_displacement_and_disjointness`, L2117)**:
   `evalCtfeAtLayout L₁ m kind regs prog = evalCtfeAtLayout L₂ m kind regs prog` (`rfl` — CTFE evaluation over `CtfeProvenance` depends strictly on `(AllocId, offset)`, never concrete addresses). Whenever `ValidRelocLayout m L` holds (disjoint non-empty address intervals assigned to distinct allocations), `physical_address_displacement_and_disjointness` proves that any successful `ptrInboundsAdd m p n = .ok p'` induces exact physical displacement `concreteAddr L p' = concreteAddr L p + n` (`ptrOffsetFrom m p' p = .ok n`), and any two strictly in-bounds pointers into distinct live non-ZST allocations `pr₁.allocId ≠ pr₂.allocId` satisfy `concreteAddr L p₁ ≠ concreteAddr L p₂`.

Ten kernel-checked differential witnesses (`L2220-2440`) verify exact agreement with the observed `rustc` probe suite across: `witness_owned_cell_const_accepted`, `witness_unsafe_cell_transmute_rejected`, `witness_unsafe_cell_union_transmute_rejected`, `witness_mut_ref_to_readonly_rejected`, `witness_dangling_raw_ptr_rejected`, `witness_dangling_ref_rejected`, `witness_int_ptr_boundary` (`.add(0)` ok vs `.add(1)`/`deref` `danglingIntPointer`), `witness_transmute_imm_static_to_cell_rejected`, `witness_zst_validation_vs_static_e0492`, `witness_offset_from_same_vs_cross_alloc`, and `witness_static_const_checks`.

### 7. Implications for `joshlf/anneal` Verified MIR Semantics

Basis: source + derived

Inspecting `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) at `trusted/lean/Trusted/MirAst.lean` (`lines 490-550`) and `trusted/lean/Trusted/MirSemantics.lean` (`lines 570-625`, `838-905`) shows that Anneal's trusted MIR semantics currently restricts `ConstLit` to `.scalar` and `.zeroSized`, lowering all pointer, reference, slice, and indirect static constants to `.unsupported`. This restriction keeps Anneal sound with respect to constant allocation aliasing and global mutability today, because no `.unsupported` constant can enter proof obligations as a valid value.

However, if Anneal extends `ConstLit` to verify functions referencing `const &'static [u8]`, `const &str`, `static` items, or `const &AtomicU32` handles, its `Trusted` memory and constant model must mirror four `rustc` guarantees proven here:
1. Promoted/constant aggregate allocations backing `ConstLit` references must carry immutable memory attributes (no interior writes, no escaping `&mut`), unless backed by a distinct non-aliasing `static` item (`GlobalAlloc::Static`) whose reads in CTFE/specification are explicitly modeled.
2. Any constant ZST reference (`&[]`, `&UnsafeCell<()>`) permitted past `rustc` validation must have zero-byte read/write footprint in `MirSemantics` so zero-sized aliasing cannot violate separation invariants.
3. No `AllocId` in a lowered constant graph may be freed (`zero_dangling_local_interning_guarantee`), and integer-derived non-provenance pointers (`0x1000 as *const T`) must remain unusable for `deref` or non-zero `offset` proofs.
4. Relational pointer reasoning across distinct constant/static allocations must preserve `cross_allocid_relocation_invariance`: distinct allocations must remain disjoint when strictly in bounds (`physical_address_displacement_and_disjointness`), without exposing concrete pointer-to-integer numerical equality across allocations.

## Boundaries

Per the report format taxonomy, the following boundaries delimit what this evidence establishes and does not establish:

- **Known not to apply**:
  - **Runtime borrowing and LLVM/Miri aliasing semantics**: CTFE validation uses `CtfeValidationMode` with `compiletime` machine hooks (`RetagMode::None`/`Raw`), whereas runtime unsafe execution (and Miri's Stacked Borrows / Tree Borrows) governs post-startup stack/heap borrows and allows interior mutation inside heap/stack `UnsafeCell`s where CTFE read-only `.rodata` forbids it.
  - **Zero-sized types (ZSTs) under CTFE validation and promoted `&mut []`**: ZSTs (`&mut []`, `transmute::<&(), &UnsafeCell<()>>`, `transmute::<*const [u8; 0], &mut [u8; 0]>`) are explicitly exempted from CTFE read-only mutability/cell checks (`validity.rs:800, 1320, 1380`) and `Promoted` interning checks (`intern.rs:302`), and `ptr.add(0)` on an integer-cast pointer succeeds (`memory.rs:532-534`). Do not apply non-ZST `E0080` claims to ZST targets without checking MIR `check_consts` (`E0492` still fires for direct `&UnsafeCell::new(())`).
  - **Dynamic `const_allocate` / `const_make_global` heap lifetime rules**: Covered in this report only at the `prepare_alloc` `MemoryKind::Machine(Heap { was_made_global })` gate (`intern.rs:65-71`); full `const_heap` ICEs and deallocation contracts belong to dedicated `const_heap` analyses.
  - **Formalized `CtfeInterningMutabilityAndProvenanceSoundness.lean` abstraction scope**: The Lean model mechanizes CTFE's allocation graph, mutability flags, provenance rules, and validation decisions cleanly at an abstract block/type/value level (`ConstVal`/`ConstTy`); it does *not* extract or symbolically execute `rustc`'s full MIR bytecode interpreter or LLVM IR lowering, so soundness theorems establish properties of the formalized transition model shown faithfully to match all 30 live `rustc` probes rather than a verified extraction of `rustc_const_eval`'s Rust crate binary.

- **Not examined**:
  - Function pointers (`GlobalAlloc::Function`), trait-object vtable pointers (`GlobalAlloc::VTable`), `GlobalAlloc::TypeId` pointers, `extern static` FFI symbols (`is_foreign_item`), and `#[thread_local]` statics (`NestedStaticInThreadLocal` error in `intern.rs:162-165`).
  - Partial/sub-byte provenance merging (`provenance_merge_bytes` and `InternError::PartialPointer` in `intern.rs:76-80`) and `reset_provenance_and_padding` byte masking (`validity.rs:911-923`, `1329-1338`).
  - Target pointer widths other than 64-bit `x86_64-unknown-linux-gnu` (`usize` overflow/sign-extension edge cases on 16-bit or 32-bit targets in `memory.rs:557` and `intrinsics.rs:431`), and codegen-level linker section placement / merge-constants deduplication behavior (`immutable static` vs `const` physical overlap allowed by `r[items.static.storage-disjointness]`).

- **Unknown**:
  - Whether or when upstream `rust-lang/rust` will convert `InternError::DanglingPointer` (`DanglingPtrInFinal`) from `NonConstEvalError` into a validation error (`const_validate_mplace` FIXME at `eval_queries.rs:173-174`: `"FIXME: ensure validation always reports this and stop making interning care about it."`) or resolve tracking issue `#53020` for reliable pointer comparison during const evaluation (`guaranteed_cmp` exposure).

- **Unsupported**:
  - Pointer-to-integer casts (`ptr as usize`) and raw-pointer equality/relational comparisons (`==`, `!=`, `<`, `<=`, `>`, `>=`) in const evaluation contexts (`check_consts/check.rs:622-624, 658-670` and `machine.rs:573-580, 641-647`).
  - Lowering pointer-valued, slice-valued, reference-valued, or static-backed constants inside `joshlf/anneal` (`trusted/lean/Trusted/MirAst.lean:490-550`, `.unsupported`).

## Evidence

### Primary Sources Audited

| Subject | Exact Commit SHA | Audited Paths & Key Symbols / Line Ranges |
| --- | --- | --- |
| `rust-lang/rust` (HEAD `2026-11-23`) | `277240238554297f93fa9ee3c7643dfa03ccbbb4` | `compiler/rustc_const_eval/src/interpret/intern.rs` (`prepare_alloc` `58-95`, `intern_shallow` `104-138`, `intern_as_new_static` `142-177`, `InternKind` `181-187`, `InternError` `190-195`, `intern_const_alloc_recursive` `204-357`, `span_bug!` `350`); `compiler/rustc_const_eval/src/const_eval/eval_queries.rs` (`retry_codegen_mode_with_postanalysis` `26-52`, `intern_and_validate` `161-210`, `eval_in_interpreter` `450-475`, `const_validate_mplace` `478-506` with `allow_immutable_unsafe_cell: !inner` at `494`); `compiler/rustc_const_eval/src/interpret/validity.rs` (`CtfeValidationMode` `264-286`, `check_safe_pointer` `729-844` with `skip_recursive_check` at `730`/`785-792` and `size != Size::ZERO` at `800-824`, `try_visit_primitive` `RawPtr` `917-934`, `in_mutable_memory` `1072-1091`, `visit_union` `1310-1340`, `visit_value` `1363-1391`); `compiler/rustc_const_eval/src/interpret/memory.rs` (`check_ptr_access` / `check_and_deref_ptr` `481-566` with `size == 0` at `532-534`, `get_live_alloc_size_and_align` `967-977`); `compiler/rustc_const_eval/src/interpret/operator.rs` (`binary_ptr_op` `316-362`); `compiler/rustc_const_eval/src/interpret/intrinsics.rs` (`arith_offset` `426-435`, `ptr_offset_from` `436-489`); `compiler/rustc_const_eval/src/const_eval/machine.rs` (`guaranteed_cmp` `280-389`, `binary_ptr_op` `573-580`, `expose_provenance` `641-647`, `before_access_global` `676-706`); `compiler/rustc_const_eval/src/check_consts/check.rs` (`place_may_escape` `308-336`, `Mut`/`UnsafeCell` borrow checks `549-581`, casts `598-630`, `RawPtrComparison` `652-679`); `compiler/rustc_const_eval/src/check_consts/{ops.rs,qualifs.rs}` (`HasMutInterior`, `ProjectionElem::PhantomDeref`); `compiler/rustc_const_eval/src/diagnostics.rs` (`E0764` `202-216`, `E0492` `266-280`); `compiler/rustc_middle/src/mir/interpret/pointer.rs` (`CtfeProvenance` `82-169`). |
| `rust-lang/rust` (`1.98.0-nightly`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Direct line-level comparison across the same core files: `intern.rs` (`InternKind` `180`, `intern_const_alloc_recursive` `203`, `span_bug!` `349`), `eval_queries.rs` (`intern_and_validate` `119`, `const_validate_mplace` `432`, `allow_immutable_unsafe_cell` `448`, `const_validate_operand`), `validity.rs` (`skip_recursive_check` `752`, `mutable reference or box` `842`, `visit_value` `1367`), `machine.rs` (`guaranteed_cmp` `278`, `binary_ptr_op` `790`, `before_access_global` `897`). Executed live for all 30 probes (`support/probe_results.json`). |
| `rust-lang/reference` | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | `src/const_eval.md` (`1-100`: `r[const-eval.const-expr.path-static]`, `r[const-eval.const-expr.borrows]`); `src/items/static-items.md` (`1-100`: `r[items.static.intro]`, `r[items.static.storage-disjointness]`, `r[items.static.read-only]`). |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean` (`490-550`, `ConstLit` restricted to `.scalar` and `.zeroSized`, pointer/slice/indirect lowering to `.unsupported`); `trusted/lean/Trusted/MirSemantics.lean` (`570-625`, `838-905`). |
| `leanprover/lean4` (`v4.34.1`) | `5045d0056413266e57c625dcd7c365b10e377c52` | Kernel type-checking and MetaM axiom/purity audit of `support/CtfeInterningMutabilityAndProvenanceSoundness.lean`. |

### Live `rustc` Execution Matrix (`support/probe_results.json`, `rustc 1.98.0-nightly`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `--edition=2024`)

All 30 probes executed cleanly inside isolated temporary directories (`support/probe_ctfe_interning_provenance.py`, recorded in `support/probe_results.json` on `2026-11-23`):

| Group | Probe ID | Compile RC | Run RC | Key Compiler Diagnostic or Program Output |
| --- | --- | --- | --- | --- |
| A | `stack_mut_owned_cell_and_static_atomic_ok` | `0` | `0` | `X=42 CELL=12 ATOMIC_PREV=77 ATOMIC_NOW=80` |
| A | `dangling_alloc_raw_ptr_in_final_const_rejected` | `1` | — | `error: encountered dangling pointer in final value of constant` (no `E0080`) |
| A | `int_raw_ptr_stored_ok` | `0` | `0` | `INT_PTR_ADDR=0x1000` |
| A | `dangling_raw_deref_rejected` | `1` | — | `error[E0080]: memory access failed: alloc2 has been freed, so this pointer is dangling` |
| A | `dangling_ref_rejected` | `1` | — | `error[E0080]: constructing invalid value of type &u32: encountered a dangling reference (use-after-free)` |
| A | `unsafe_cell_ref_in_const_rejected` | `1` | — | `error[E0492]: interior mutable shared borrows of temporaries that have their lifetime extended until the end of the program are not allowed` |
| A | `unsafe_cell_transmute_in_const_rejected` | `1` | — | `error[E0080]: constructing invalid value of type &UnsafeCell<u32>: at .<deref>, encountered \`UnsafeCell\` in read-only memory` |
| A | `unsafe_cell_union_transmute_in_const_rejected` | `1` | — | `error[E0080]: constructing invalid value of type &CellOrInt: at .<deref>, encountered \`UnsafeCell\` in read-only memory` |
| A | `mut_ref_escaping_const_rejected` | `1` | — | `error[E0764]: mutable borrows of temporaries that have their lifetime extended until the end of the program are not allowed` |
| A | `mut_ref_transmute_to_readonly_rejected` | `1` | — | `error[E0080]: constructing invalid value of type &mut u32: encountered mutable reference or box pointing to read-only memory` |
| A | `zst_promoted_mut_and_zst_cell_exceptions_ok` | `0` | `0` | `ZST_MUT_LEN=0 ZST_CELL_SIZE=0 ZST_MUT_ARR_LEN=0` |
| A | `zst_unsafecell_direct_borrow_still_e0492_rejected` | `1` | — | `error[E0492]: interior mutable shared borrows of temporaries that have their lifetime extended until the end of the program are not allowed` |
| A | `static_mut_nested_mut_alloc_ok` | `0` | `0` | `S_MUT_0=99 S_MUT_1=20` |
| B | `provenance_valid_inbounds` | `0` | `0` | `INBOUNDS_VAL=30` |
| B | `int_to_ptr_deref_rejected` | `1` | — | `error[E0080]: memory access failed: attempting to access 1 byte, but got 0x1000[noalloc] which is a dangling pointer (it has no provenance)` |
| B | `int_to_ptr_zero_add_ok` | `0` | `0` | `INT_PTR_ZERO_ADD=0x1000` |
| B | `int_to_ptr_nonzero_add_rejected` | `1` | — | `error[E0080]: in-bounds pointer arithmetic failed: attempting to offset pointer by 1 byte, but got 0x1000[noalloc] which is a dangling pointer (it has no provenance)` |
| B | `oob_ptr_add_rejected` | `1` | — | `error[E0080]: in-bounds pointer arithmetic failed: attempting to offset pointer by 10 bytes, but got alloc2 which is only 2 bytes from the end of the allocation` |
| B | `oob_wrapping_add_static_stored_ok` | `0` | `0` | `OOB_WRAP_OFFSET=10` |
| B | `oob_wrapping_add_deref_rejected` | `1` | — | `error[E0080]: memory access failed: attempting to access 1 byte, but got alloc2+0xa which is at or beyond the end of the allocation of size 2 bytes` |
| B | `ptr_cmp_different_allocs_rejected` | `1` | — | `error: pointers cannot be reliably compared during const eval` |
| B | `ptr_cmp_int_ptrs_rejected` | `1` | — | `error: pointers cannot be reliably compared during const eval` |
| B | `ptr_to_int_cast_rejected` | `1` | — | `error: pointers cannot be cast to integers during const eval` |
| B | `offset_from_same_static_ok` | `0` | `0` | `SAME_DIFF=2` |
| B | `offset_from_diff_alloc_rejected` | `1` | — | `error[E0080]: \`ptr_offset_from\` called on two different pointers that are not both derived from the same allocation` |
| B | `ptr_cmp_unleashed_runtime_binary_ptr_op_rejected` | `1` | — | `error[E0080]: pointer arithmetic or comparison is not supported at compile-time` (`-Z unleash-the-miri-inside-of-you`) |
| C | `const_ref_to_static_atomic_and_ptr_to_static_mut_ok` | `0` | `0` | `REF_TO_STATIC=99 READ_IMM_STATIC=99 ATOMIC_PREV=5 ATOMIC_NOW=7 PTR_TO_MUT_STATIC_AFTER=456` |
| C | `const_read_atomic_static_rejected` | `1` | — | `error[E0080]: constant accesses mutable global memory` |
| C | `const_reading_mut_static_rejected` | `1` | — | `error[E0080]: constant accesses mutable global memory` |
| C | `const_transmute_imm_static_to_unsafecell_rejected` | `1` | — | `error[E0080]: constructing invalid value of type &UnsafeCell<u32>: at .<deref>, encountered \`UnsafeCell\` in read-only memory` |

### Mechanized Lean `v4.34.1` Formalization (`support/CtfeInterningMutabilityAndProvenanceSoundness.lean`)

- **Size & Structure**: `2,442` lines (`102,954` bytes), `57` file-level `theorem` declarations, `49` `noncomputable def` definitions, `0` `partial def`, `0` `sorry`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`.
- **Kernel & Purity Verification**: Compiled under Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (exit `0`, zero warnings), followed by a Lean MetaM environment inspection across all `221` environment theorems and `242` definitions reporting `unsafe_recs=0`, `forbidden_axiom_items=0`, and `distinct_axioms_used=[propext]` (`0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`).

## Revalidation

To cheaply revalidate all empirical, formal, and structural claims from the corpus repository root:

1. **Re-run all 30 live `rustc` probes** (compares every exit code against expected pass/fail outcomes in temporary directories and writes updated JSON):
   ```bash
   python3 reports/rustc-ctfe-const-interning-mutability-dangling-and-provenance-soundness/support/probe_ctfe_interning_provenance.py /tmp/ctfe_interning_reval.json
   ```
   A passing run confirms all 30 probes still yield identical pass/fail classifications; inspecting `compile_stderr` in `/tmp/ctfe_interning_reval.json` detects any diagnostic text changes (`E0492`/`E0764`/`E0080` or `DanglingPtrInFinal`).

2. **Re-verify the Lean `v4.34.1` formalization with full kernel checking and strict warnings**:
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true reports/rustc-ctfe-const-interning-mutability-dangling-and-provenance-soundness/support/CtfeInterningMutabilityAndProvenanceSoundness.lean
   ```

3. **Check upstream `rust-lang/rust` drift** since `277240238554297f93fa9ee3c7643dfa03ccbbb4`: diff `compiler/rustc_const_eval/src/interpret/{intern.rs,validity.rs,memory.rs,intrinsics.rs}`, `compiler/rustc_const_eval/src/const_eval/{eval_queries.rs,machine.rs}`, `compiler/rustc_const_eval/src/check_consts/check.rs`, and `compiler/rustc_middle/src/mir/interpret/pointer.rs` targeting changes to `InternKind`, `intern_and_validate`, `skip_recursive_check`, `allow_immutable_unsafe_cell`, `before_access_global`, or `check_and_deref_ptr` (`size == 0`), plus `trusted/lean/Trusted/MirAst.lean` in `joshlf/anneal` for any relaxation of `.unsupported` constant lowering.

4. **Validate corpus metadata and index consistency**:
   ```bash
   python3 tools/reference.py catalog && python3 tools/reference.py check && python3 -m unittest discover -s tests -v
   ```
