# `rustc` `#![feature(const_heap)]`: Two Live Interning ICEs (`intern.rs:91` & `intern.rs:350`), `const_deallocate` `# Safety` Contract Falsehoods, CTFE-vs-Runtime/Miri Fallback Divergence, and Kernel-Checked Repaired Interning Soundness

## Summary

Direct source inspection across three pinned `rust-lang/rust` revisions (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` / `rustc 1.98.0-nightly`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` / `rustc 1.102.0-nightly`, and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` / `2026-11-22` HEAD), empirical execution of a 30-case `rustc` matrix plus native and Miri (Stacked Borrows and Tree Borrows) dual-mode probes, and a kernel-checked Lean `v4.34.1` formalization (`support/ConstHeapInterningAndMakeGlobalSoundness.lean`, 40 theorems, 0 `sorry`, 0 `Classical.choice`, 0 `._unsafe_rec`) establish four durable defects and semantic boundaries in `rustc`'s `#![feature(const_heap)]` (`const_allocate`, `const_deallocate`, `const_make_global`) subsystem:

1. **Live Compiler Crash — ICE #1 (`intern.rs:350:13` on `1.102.0-nightly`/HEAD; `intern.rs:349:13` on `1.98.0-nightly`, exit code `101`):** `sym::const_make_global` calls `make_const_heap_ptr_global(ptr)` (which sets `was_made_global = true` and `alloc.mutability = Mutability::Not`) and then writes `ptr` back to `dest` **unmodified**, preserving `CtfeProvenance { immutable: false, shared_ref: false }`. Returning `*const u8` directly from `const_make_global(p)` inside a `const` or immutable `static` passes static const-checking (`check_consts/check.rs`) and would pass raw-pointer validation (`validity.rs:917-934`), but hits `!prov.shared_ref()` during `intern_const_alloc_recursive` (`intern.rs:302-304`) and panics with `span_bug!: the static const safety checks accepted a mutable pointer they should not have accepted`. Reborrowing `(&*const_make_global(p)) as *const T` runs `CompileTimeMachine::retag_ptr_value` (`machine.rs:1125-1158`), setting `SHARED_REF_MASK` (for both `Freeze` and `!Freeze` pointees) and compiling cleanly (`rc = 0`). Passing `-Z unleash-the-miri-inside-of-you` downgrades ICE #1 to a regular error (`diagnostics::MutablePtrInFinal`, `rc = 1`).
2. **Live Compiler Crash — ICE #2 (`intern.rs:91:13` across all three revisions, exit code `101`) and `static mut` Catch-22:** For `InternKind::Static(Mutability::Mut)` (`static mut`), `intern_const_alloc_recursive` sets `inner_mutability = Mutability::Mut` (`intern.rs:236-240`) and invokes `prepare_alloc`, which unconditionally asserts `assert_eq!(alloc.mutability, Mutability::Mut)` (`intern.rs:91`). Because `make_const_heap_ptr_global` already froze the allocation to `Mutability::Not` (`memory.rs:374`), **every** `static mut` initializer referencing a same-evaluation `const_make_global` allocation panics (`left: Not, right: Mut`) regardless of whether the value is `&'static u8`, `*const u8`, or compiled with `-Z unleash-the-miri-inside-of-you`. Omitting `const_make_global` instead fails earlier at `intern.rs:66-71` (`ConstHeapPtrInFinal`, `rc = 1`), creating a complete deadlock for same-evaluation `const_heap` inside `static mut`. Referencing an allocation already pre-interned by a separate `const` item (`GlobalAlloc::Memory`) bypasses `prepare_alloc` at `intern.rs:324` and compiles (`rc = 0`).
3. **`core::intrinsics::const_deallocate` `# Safety` Contract Falsehood and CTFE-vs-Runtime/Miri Divergence:** `library/core/src/intrinsics/mod.rs` documents under `# Safety` that `"If the ptr is pointing to a local variable, this intrinsic doesn't deallocate it"`. In reality, CTFE `sym::const_deallocate` checks `Align::from_bytes(align)` **first**, then skips deallocation **only** for `Some(GlobalAlloc::Memory(_))` (allocations interned by *another* `const`, ignoring size mismatches once alignment is a power of two). Calling `const_deallocate` on a stack local (`MemoryKind::Stack`), a `static` item (`GlobalAlloc::Static`), or a same-`const` `const_make_global` allocation immediately raises `E0080` UB (`deallocating allocN, which is stack variable memory`, `static memory`, or `immutable allocation`). Conversely, at runtime **and under Miri** (both default Stacked Borrows and `-Zmiri-tree-borrows`) all three intrinsics execute their `#[miri::intrinsic_fallback_is_spec]` fallback bodies (`const_allocate` returns `null_mut()`, `const_deallocate` is an unchecked NOP, `const_make_global` is the identity function), silently accepting non-power-of-two alignments (`align = 3`), bogus sizes (`size = 999`), and stack-local pointers while producing observable CTFE-vs-runtime value divergence (`CTFE=(true, 88)` vs. `RUNTIME=(true, 77)`) on the exact same `const fn`.
4. **Repaired Semantics & Verified Trusted-Boundary Requirements:** Updating `const_make_global`'s returned pointer provenance via `CtfeProvenance::as_immutable` (`immutable = true, shared_ref = true`) and exempting `MemoryKind::Heap { was_made_global: true }` in `prepare_alloc` (preserving `Mutability::Not` without un-freezing even when `inner_mutability == Mutability::Mut`) eliminates both ICEs across `const`, `promoted`, immutable `static`, and `static mut` while mechanically guaranteeing that every interned `const_heap` allocation is strictly immutable and no transient `was_made_global = false` allocation escapes. A subtle boundary remains for pre-call aliases (`let _g = const_make_global(p); p as *const u8`), whose provenance retains `shared_ref = false` unless `intern_const_alloc_recursive` also checks `was_made_global` or emits a non-ICE diagnostic.

## Applicability

This report applies to `rustc`'s compile-time function evaluation (CTFE) interpreter (`rustc_const_eval`), its standard-library intrinsic definitions (`library/core/src/intrinsics/mod.rs`), Miri's fallback-body dispatch (`src/tools/miri/src/intrinsics/mod.rs`), and formal verification boundaries that ingest `rustc` MIR constants (specifically `joshlf/anneal`).

### Relationship Among Examined Subjects

The six subjects in `REPORT.json` relate as follows:

| Subject | Immutable Revision | Role in This Report |
| :--- | :--- | :--- |
| `rust-lang/rust` (`1.102.0-nightly`, `2026-11-11`) | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | Primary-source baseline (`const_eval/machine.rs`, `interpret/memory.rs`, `interpret/intern.rs`, `const_eval/eval_queries.rs`, `interpret/validity.rs`, `check_consts/check.rs`, `diagnostics.rs`, `library/core/src/intrinsics/mod.rs`, `src/tools/miri/src/intrinsics/mod.rs`) paired with the preserved 15-case + dual-execution record (`support/probe_results_1_102_nightly.json`). |
| `rust-lang/rust` (HEAD, `2026-11-22`) | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | Source-drift verification confirming that CTFE intrinsic dispatch moved from `const_eval/machine.rs` into `const_eval/intrinsics.rs` (`call_ctfe_intrinsic`), while `memory.rs`, `intern.rs`, `const_eval/error.rs`, and the `# Safety` contract falsehood in `library/core/src/intrinsics/mod.rs` remained semantically identical (with `memory.rs` and `intern.rs` byte-for-byte identical to `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`). |
| `rust-lang/rust` (`1.98.0-nightly` + `Miri 0.1.0`, `2026-05-31`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Live execution environment for the full 30-case `rustc` compiler matrix (15 core + 15 extended boundary discriminators), native `x86_64-unknown-linux-gnu` binary execution, and offline Miri execution under both default Stacked Borrows and `-Zmiri-tree-borrows` (`support/probe_results_1_98_nightly.json`). |
| `rust-lang/reference` (`2026-11-17`) | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Normative language-level rules for constant evaluation (`src/const_eval.md`) and static item immutability/disjointness (`src/items/static-items.md`), confirming that unstable `const_heap` intrinsics sit outside the Reference while relying on Reference-level read-only `static`/`const` guarantees. |
| `joshlf/anneal` (`2026-11-19`) | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Target verification trusted computing base (`trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`) analyzed for how `ConstLit`, `Rvalue`, `TerminatorKind::Call`, and `BodyStaticAdmitted` currently fail closed on pointer constants and `const_heap` intrinsics. |
| `leanprover/lean4` (`v4.34.1`) | `5045d0056413266e57c625dcd7c365b10e377c52` | Proof kernel checking `support/ConstHeapInterningAndMakeGlobalSoundness.lean` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`. |

### Version-Specific Differences Across Examined `rust-lang/rust` Revisions

1. **Feature-gate attribution on `const_deallocate`:**
   - At `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`), `library/core/src/intrinsics/mod.rs:2653-2658` carried `#[rustc_const_unstable(feature = "const_heap", issue = "79597")]` alongside `#[unstable(feature = "core_intrinsics", issue = "none")]`.
   - At `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, L2731-2735) and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (HEAD, L2735-2739), `const_deallocate` carries `#[rustc_const_unstable(feature = "core_intrinsics", issue = "none")]`, while `const_allocate` and `const_make_global` retain `#[rustc_const_unstable(feature = "const_heap", issue = "79597")]`. Calling any of the three via `core::intrinsics::*` requires `#![feature(const_heap, core_intrinsics)]` in all three revisions.
2. **Source file location of CTFE intrinsic handlers:**
   - At `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`), handlers live in `compiler/rustc_const_eval/src/const_eval/machine.rs:489-542`.
   - At `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`), handlers live in `compiler/rustc_const_eval/src/const_eval/machine.rs:503-556`.
   - At `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (HEAD), `CompileTimeMachine::call_intrinsic` (`machine.rs:514`) delegates to `InterpCx::call_ctfe_intrinsic` in the newly extracted `compiler/rustc_const_eval/src/const_eval/intrinsics.rs:34-87`. The match-arm logic for `const_allocate`, `const_deallocate`, and `const_make_global` is unchanged.
3. **Diagnostic line number of ICE #1:**
   - At `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`), `span_bug!` in `intern_const_alloc_recursive` is at `compiler/rustc_const_eval/src/interpret/intern.rs:349:13` (1 line earlier because line 163 in `intern_as_new_static` was a single line referencing `errors::NestedStaticInThreadLocal`).
   - At `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`) and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (HEAD), `diagnostics::NestedStaticInThreadLocal` wrapped onto two lines (`intern.rs:163-164`), shifting the exact same `span_bug!` to `intern.rs:350:13`. ICE #2 (`assert_eq!(alloc.mutability, Mutability::Mut)`) is at `intern.rs:91:13` in all three revisions.

### Scope Conditions

- **Target / Host:** Empirical runs executed on `x86_64-unknown-linux-gnu` with Rust 2024 edition (`--edition=2024`). Because all defects reside in target-independent `rustc_const_eval` / `core::intrinsics` logic, the compiler behavior is architecture-independent (derived from source), though only `x86_64-unknown-linux-gnu` was directly executed.
- **Unstable Feature Flags:** All probes enable `#![feature(const_heap, core_intrinsics)]` (plus `#![feature(thread_local)]` for the thread-local nested-static case). None of `const_allocate`, `const_deallocate`, or `const_make_global` are stabilized in any examined revision.

## Findings

### 1. CTFE Heap Allocation State Machine and Packed Provenance Architecture

Basis: source + execution + derived

During constant evaluation, `CompileTimeMachine` stores session-local allocations in `ecx.memory.alloc_map : FxIndexMap<AllocId, (MemoryKind<const_eval::MemoryKind>, Allocation)>` (`compiler/rustc_const_eval/src/interpret/intern.rs:43` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`). Machine-specific memory kinds in CTFE contain a single variant carrying a boolean promotion flag (`compiler/rustc_const_eval/src/const_eval/machine.rs:177-203`):

```rust
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum MemoryKind {
    Heap {
        /// Indicates whether `make_global` was called on this allocation.
        /// If this is `true`, the allocation must be immutable.
        was_made_global: bool,
    },
}

impl interpret::MayLeak for MemoryKind {
    #[inline(always)]
    fn may_leak(self) -> bool {
        match self {
            MemoryKind::Heap { was_made_global } => was_made_global,
        }
    }
}
```

Separately, pointer provenance during CTFE is packed into a single `NonZero<u64>` (`compiler/rustc_middle/src/mir/interpret/pointer.rs:82-164`):

```rust
/// Packed representation of:
/// - an `AllocId` (non-zero)
/// - an `immutable: bool`
/// - a `shared_ref: bool`
/// with the extra invariant that if `immutable` is `true`, then so is `shared_ref`.
pub struct CtfeProvenance(NonZero<u64>);

const IMMUTABLE_MASK: u64 = 1 << 63; // the highest bit
const SHARED_REF_MASK: u64 = 1 << 62;
const ALLOC_ID_MASK: u64 = u64::MAX & !IMMUTABLE_MASK & !SHARED_REF_MASK;
```

Key provenance constructors and bit-level invariants (`pointer.rs:93-164`):
- `CtfeProvenance::from(alloc_id)` sets **both** `immutable = false` and `shared_ref = false`. Every pointer returned by `ecx.allocate_ptr(...)` — including `sym::const_allocate` — starts with `(immutable = false, shared_ref = false)`.
- `CtfeProvenance::as_shared_ref(self)` sets `SHARED_REF_MASK` (`1 << 62`) only (`immutable` unchanged).
- `CtfeProvenance::as_immutable(self)` sets `IMMUTABLE_MASK | SHARED_REF_MASK` (preserving the representation invariant `immutable => shared_ref`).

The **only** place in `CompileTimeMachine` that transitions a pointer's provenance to `shared_ref = true` (or `immutable = true`) during MIR execution is `CompileTimeMachine::retag_ptr_value` (`const_eval/machine.rs:1125-1158`), which runs exclusively on shared references (`ty::Ref(_, ty, Mutability::Not)`), **never** on raw pointers (`*const T` / `*mut T`) or `RetagMode::Raw`:

```rust
if let ty::Ref(_, ty, mutbl) = val.layout.ty.kind()
    && *mutbl == Mutability::Not
    && val.to_scalar_and_meta().0.to_pointer(ecx).provenance.is_some_and(|p| !p.immutable())
{
    let is_immutable = ty.is_freeze(*ecx.tcx, ecx.typing_env());
    let place = ecx.imm_ptr_to_mplace(val)?;
    let new_place = if is_immutable {
        place.map_provenance(CtfeProvenance::as_immutable)
    } else {
        place.map_provenance(CtfeProvenance::as_shared_ref)
    };
    interp_ok(Some(ImmTy::from_immediate(new_place.to_ref(ecx), val.layout)))
}
```

#### Lifecycle State Transitions of a `const_heap` Allocation

Every allocation created by `sym::const_allocate` follows a strict five-state lifecycle across `ecx.memory.alloc_map`, `ecx.memory.dead_alloc_map`, and `tcx` global memory:

| State | Location & Metadata | Allowed Operations | Rejected Operations (Exact Diagnostic) |
| :--- | :--- | :--- | :--- |
| **S0: Transient Heap** | `alloc_map[id] = (Heap { was_made_global: false }, mutbl: Mut)` | Read, write, `const_deallocate(p, size, align)` -> **S1**, `const_make_global(p)` (at offset `0`) -> **S2**, unreachable drop at end of CTFE -> silently discarded (`rc = 0`). | Reachable at interning (`prepare_alloc`, `intern.rs:66-71`) -> `ConstHeapPtrInFinal` (`encountered const_allocate pointer in final value that was not made global`). `const_make_global` at non-zero offset -> `ConstMakeGlobalWithOffset`. |
| **S1: Deallocated (Dead)** | Removed from `alloc_map`; `(size, align)` inserted into `dead_alloc_map[id]`. | None (dangling pointer). | Read/write -> `PointerUseAfterFree`. `const_deallocate` -> `PointerUseAfterFree`. `const_make_global` -> `ConstMakeGlobalWithDanglingPtr` (`pointer passed to const_make_global is dangling: allocN`). Reachable at interning -> `DanglingPtrInFinal`. |
| **S2: Frozen Local Heap (Made Global, Pre-Intern)** | `alloc_map[id] = (Heap { was_made_global: true }, mutbl: Not)` | Read; interning via `intern_const_alloc_recursive` -> **S3** (for `const`/`promoted`) or **S4** (for non-TLS immutable `static`) — **only** if every pointing provenance has `shared_ref = true` (else ICE #1) and `intern_kind != Static(Mut)` (else ICE #2). | Write (`*p = v`) -> `E0080: writing to allocN which is read-only`. `const_make_global(p)` again -> `ConstMakeGlobalPtrAlreadyMadeGlobal` (`attempting to call const_make_global twice on the same allocation allocN`). `const_deallocate(p, ...)` -> `E0080: deallocating immutable allocation allocN`. |
| **S3: Interned `GlobalAlloc::Memory`** | Removed from `alloc_map`; inserted into `tcx` via `set_alloc_id_memory(id, alloc)` with `mutbl: Not`. | Read by any subsequent `const` or `static` (including `static mut`, bypassing `prepare_alloc` at `intern.rs:324`). `const_deallocate` in *another* `const` -> **no-op** (after power-of-two `align` check). | `const_make_global` -> `ConstMakeGlobalPtrIsNonHeap` (`memory.rs:347-350`). Write -> `WriteToReadOnly`. |
| **S4: Interned Nested `GlobalAlloc::Static`** | Removed from `alloc_map`; synthesized `DefPathData::NestedStatic` via `intern_as_new_static` (`intern.rs:142-177`) with `mutability: alloc.0.mutability`. | Read in other `static` initializers (or `const` if immutable). | If parent static is `#[thread_local]` -> `NestedStaticInThreadLocal` (`intern.rs:162-165`). `const_deallocate` in another `const` -> `E0080: deallocating allocN, which is static memory` (because `GlobalAlloc::Static`, unlike `GlobalAlloc::Memory`, is NOT exempted by `is_allocated_in_another_const`). |

Two subtle properties of this state machine were confirmed by both source reading (`const_eval/eval_queries.rs:94-210`) and live execution (`support/probe_results_1_98_nightly.json`):
1. **Unreachable transient heap allocations are NOT checked for leaks during CTFE:** `eval_body_using_ecx` (`eval_queries.rs:135-143`) runs `while ecx.step()? {}` and then immediately calls `intern_and_validate(ecx, cid, intern_kind, ret)`. It never invokes `ecx.take_leaked_allocations(...)` (which exists in `interpret/memory.rs:1155` for Miri). Thus `pub const UNREACHABLE_LEAK_OK: u8 = unsafe { let p = const_allocate(1, 1); *p = 55; *p };` compiles with `rc = 0` (`transient_alloc_unreachable_leak_silently_dropped`), silently discarding the leaked CTFE allocation when `ecx` drops, even though `MemoryKind::Heap { was_made_global: false }.may_leak()` returns `false` (`machine.rs:196-203`).
2. **Interning executes BEFORE value validation (`eval_queries.rs:161-210`):**
   ```rust
   fn intern_and_validate<'tcx, R: InterpretationResult<'tcx>>(
       ecx: &mut CompileTimeInterpCx<'tcx>,
       cid: GlobalId<'tcx>,
       intern_kind: InternKind,
       ret: MPlaceTy<'tcx>,
   ) -> InterpResult<'tcx, R> {
       // Intern the result
       let intern_result = intern_const_alloc_recursive(ecx, intern_kind, &ret);

       // Since evaluation had no errors, validate the resulting constant.
       const_validate_mplace(ecx, &ret, cid)?;
       ...
   ```
   Because `intern_const_alloc_recursive` runs *first*, any panic (`span_bug!` at `intern.rs:350` or `assert_eq!` at `intern.rs:91`) aborts compilation before `const_validate_mplace` ever runs. Normal `Err(InternError::*)` returns are deferred until after `const_validate_mplace` so validation can emit more specific type-guided diagnostics when possible.

---

### 2. Live ICE #1: Stale Provenance After `const_make_global` Triggers `intern.rs:350` `span_bug!`

Basis: source + execution + derived

#### Exact Mechanism Across Compiler Passes

1. **Intrinsic handler drops provenance upgrade:**
   At `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`compiler/rustc_const_eval/src/const_eval/machine.rs:552-556`) and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`compiler/rustc_const_eval/src/const_eval/intrinsics.rs:83-87`), `sym::const_make_global` executes:
   ```rust
   sym::const_make_global => {
       let ptr = self.read_pointer(&args[0])?;
       self.make_const_heap_ptr_global(ptr)?;
       self.write_pointer(ptr, dest)?;
   }
   ```
   Inside `make_const_heap_ptr_global` (`compiler/rustc_const_eval/src/interpret/memory.rs:335-377`), `rustc` verifies `offset == 0`, checks `try_get_global_alloc(alloc_id).is_none()`, looks up `(kind, alloc)` in `alloc_map`, verifies `kind == Heap { was_made_global: false }`, sets `*was_made_global = true` (L369), and freezes `alloc.mutability = Mutability::Not` (L374). Crucially, it **does not** modify `ptr`'s `CtfeProvenance`, and the intrinsic handler writes the original `ptr` — whose provenance still has `immutable = false, shared_ref = false` from `const_allocate` — directly into `dest` (`*const u8`).

2. **Static const safety checking permits raw `*const u8` return:**
   `check_consts/check.rs:549-561` rejects escaping mutable borrows (`Rvalue::Ref(_, BorrowKind::Mut { .. }, place) | Rvalue::RawPtr(RawPtrKind::Mut, place)`). A call to `const_allocate` followed by `const_make_global` returns `*const u8` via an intrinsic call, never constructing an escaping `Rvalue::Ref` or `Rvalue::RawPtr(Mut, ...)` to a local place, so static const-checking accepts the body without error.

3. **Validation ignores raw-pointer provenance flags:**
   Even if validation ran first, `ValidityVisitor::try_visit_primitive` (`compiler/rustc_const_eval/src/interpret/validity.rs:917-934`) only reads a `ty::RawPtr` immediate and checks unsized metadata if `!pointee.is_sized(...)`; it never inspects `CtfeProvenance::shared_ref` or dereferences raw pointers.

4. **Interning detects `!prov.shared_ref()` and panics via `span_bug!`:**
   In `intern_const_alloc_recursive` (`compiler/rustc_const_eval/src/interpret/intern.rs:215-241`), both `InternKind::Constant` and `InternKind::Static(Mutability::Not)` set `inner_mutability = Mutability::Not`. When the worklist pops `prov` from the root allocation (`intern.rs:302-355`):
   ```rust
   if intern_kind != InternKind::Promoted
       && inner_mutability == Mutability::Not
       && !prov.shared_ref()
   {
       let is_already_global = ecx.tcx.try_get_global_alloc(alloc_id).is_some();
       if is_already_global && !just_interned.contains(&alloc_id) {
           continue;
       }
       let dangling = !is_already_global && !ecx.memory.alloc_map.contains_key(&alloc_id);
       if !dangling {
           found_bad_mutable_ptr = true;
       }
   }
   ```
   Here `intern_kind != Promoted`, `inner_mutability == Mutability::Not`, `!prov.shared_ref()` is `true`, `is_already_global` is `false`, and `alloc_map.contains_key(&alloc_id)` is `true` (so `dangling == false`). Therefore `found_bad_mutable_ptr` becomes `true`. The allocation is still moved into global memory at L340 (`intern_shallow`), and after the loop terminates, L343-355 fires:
   ```rust
   if found_bad_mutable_ptr {
       if ecx.tcx.sess.opts.unstable_opts.unleash_the_miri_inside_of_you {
           return Err(InternError::BadMutablePointer);
       } else {
           span_bug!(
               ecx.tcx.span,
               "the static const safety checks accepted a mutable pointer they should not have accepted"
           );
       }
   }
   ```

#### Minimal Reproducers and Empirical Outcomes

- **`ice1a` (`const` item):**
  ```rust
  #![feature(const_heap, core_intrinsics)]
  pub const RAW_FROM_MAKE_GLOBAL: *const u8 = unsafe {
      let p = core::intrinsics::const_allocate(1, 1);
      *p = 42;
      core::intrinsics::const_make_global(p)
  };
  ```
  - `rustc 1.102.0-nightly (3ef0c22cd)`: `rc = 101`, `error: internal compiler error: <RUSTC_SRC>/compiler/rustc_const_eval/src/interpret/intern.rs:350:13: the static const safety checks accepted a mutable pointer they should not have accepted`.
  - `rustc 1.98.0-nightly (14210df0e)`: `rc = 101`, identical ICE at `intern.rs:349:13`.
  - `rustc 1.98.0-nightly -Z unleash-the-miri-inside-of-you`: `rc = 1` (non-ICE), `error: encountered mutable pointer in final value of constant` (`diagnostics::MutablePtrInFinal`).
- **`ice1b` (immutable `static` item via `Sync` newtype `SyncPtr(*const u8)`):**
  - Identical `rc = 101` ICE at `intern.rs:350:13` (`1.102.0-nightly`) and `intern.rs:349:13` (`1.98.0-nightly`).
- **Workaround via shared reborrow (`reborrow_to_raw_ptr_avoids_ice1` and `reborrow_cell_nonfreeze_to_raw_ptr_avoids_ice1`):**
  Writing `(&*core::intrinsics::const_make_global(p)) as *const u8` (or `(&*(core::intrinsics::const_make_global(p) as *const Cell<u8>)) as *const Cell<u8>` for `!Freeze` pointees) emits a MIR shared borrow (`ty::Ref(_, T, Mutability::Not)`), invoking `retag_ptr_value` (`machine.rs:1125-1158`), which calls `CtfeProvenance::as_immutable` (for `Freeze` `u8`) or `CtfeProvenance::as_shared_ref` (for `!Freeze` `Cell<u8>`). In both cases `SHARED_REF_MASK` is set, and the subsequent cast `&T as *const T` preserves that provenance, compiling cleanly with `rc = 0`.
- **Pre-call alias hazard (`pre_call_alias_after_make_global_still_triggers_ice1`):**
  Writing `let _g = core::intrinsics::const_make_global(p); p as *const u8` also triggers ICE #1 (`rc = 101`, `intern.rs:349:13` on `1.98.0-nightly`). Crucially, even if `const_make_global` is patched to return `ptr.map_provenance(as_immutable)`, a pre-call copy `p` retained in another local still carries `shared_ref = false` (proven formally in Theorem 11 of `ConstHeapInterningAndMakeGlobalSoundness.lean`).

---

### 3. Live ICE #2: Unconditional Mutability Assertion in `prepare_alloc` (`intern.rs:91`) and the `static mut` Catch-22

Basis: source + execution + derived

#### Exact Mechanism

In `intern_const_alloc_recursive` (`compiler/rustc_const_eval/src/interpret/intern.rs:236-240`), `InternKind::Static(Mutability::Mut)` selects:

```rust
InternKind::Static(Mutability::Mut) => {
    // Just make everything mutable. We accept code like
    // `static mut X = &mut [42]`, so even inner allocations need to be mutable.
    (Mutability::Mut, Mutability::Mut, true)
}
```

Because `inner_mutability == Mutability::Mut`, the `!prov.shared_ref()` guard at `intern.rs:302-305` is **skipped** entirely (so ICE #1 cannot fire for `static mut`). Instead, for any inner allocation not yet in `tcx` global memory, L340 invokes `intern_shallow(ecx, alloc_id, Mutability::Mut, disambiguator)` -> `prepare_alloc(*ecx.tcx, kind, &mut alloc, Mutability::Mut)` (`intern.rs:58-95`):

```rust
fn prepare_alloc<'tcx, Prov: Provenance, Extra, Bytes: AllocBytes>(
    tcx: TyCtxt<'tcx>,
    kind: MemoryKind<const_eval::MemoryKind>,
    alloc: &mut Allocation<Prov, Extra, Bytes>,
    mutability: Mutability,
) -> Result<(), InternError> {
    match kind {
        MemoryKind::Machine(const_eval::MemoryKind::Heap { was_made_global }) => {
            if !was_made_global {
                tcx.dcx().delayed_bug("non-global heap allocation in const value");
                return Err(InternError::ConstAllocNotGlobal);
            }
        }
        MemoryKind::Stack | MemoryKind::CallerLocation => {}
    }
    ...
    match mutability {
        Mutability::Not => {
            alloc.mutability = Mutability::Not;
        }
        Mutability::Mut => {
            // This must be already mutable, we won't "un-freeze" allocations ever.
            assert_eq!(alloc.mutability, Mutability::Mut);
        }
    }
    Ok(())
}
```

This creates an **unconditional catch-22 deadlock** for any `static mut` initializer that allocates via `const_allocate` and retains a pointer to that allocation:
- **Branch A (`const_make_global` NOT called):** `kind` is `Heap { was_made_global: false }`. Lines 65-71 execute **before** line 91, returning `Err(InternError::ConstAllocNotGlobal)` -> normal compile error `error: encountered const_allocate pointer in final value that was not made global` (`static_mut_uninterned_transient_rejected_not_ice`, `rc = 1`).
- **Branch B (`const_make_global` IS called):** `make_const_heap_ptr_global` (`memory.rs:369, 374`) sets `was_made_global = true` AND `alloc.mutability = Mutability::Not`. Lines 65-72 pass, execution reaches line 91 (`assert_eq!(alloc.mutability, Mutability::Mut)`), and `rustc` unconditionally panics (`rc = 101`):
  ```text
  thread 'rustc' (<PID>) panicked at <RUSTC_SRC>/compiler/rustc_const_eval/src/interpret/intern.rs:91:13:
  assertion `left == right` failed
    left: Not
   right: Mut
  ```
- **Invariance across pointer types and flags:** Unlike ICE #1, ICE #2 is **not** mitigated by reborrowing (`ice2a_static_mut_reborrowed_ref` with `&'static u8` crashes identically to `ice2b_static_mut_raw_ptr` with `*const u8`) and is **not** downgraded by `-Z unleash-the-miri-inside-of-you` (`ice2a_with_unleash_miri_still_ices`, `rc = 101`), because `assert_eq!` at line 91 is unconditional.

#### Empirical Pre-Interned Workaround (`intern.rs:324`)

When the `const_allocate` + `const_make_global` evaluation is factored out into a separate `const` item first:

```rust
const PRE: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    &*core::intrinsics::const_make_global(p)
};
pub static mut SM_PRE: &'static u8 = PRE;
```

`PRE` interns the heap allocation into `tcx` as an immutable `GlobalAlloc::Memory`. When `SM_PRE` is later interned, `intern.rs:324` (`if ecx.tcx.try_get_global_alloc(alloc_id).is_some() { continue; }`) skips `intern_shallow` and `prepare_alloc` completely. Both `static_mut_preinterned_const_avoids_ice2` (`&'static u8`) and `static_mut_raw_ptr_via_preinterned_const_avoids_both_ices` (`*const u8`, combined with the reborrow workaround inside `PRE_RAW`) compile cleanly with `rc = 0` while preserving immutability of the underlying global allocation.

#### Interaction with `#[thread_local]` Statics (`intern.rs:162-165`)

For `#[thread_local] pub static TLS_REF: &'static u8 = unsafe { ... const_make_global(p) ... };`, `intern_shallow` calls `intern_as_new_static` (`intern.rs:142-177`) because `ecx.machine.static_def_id()` is `Some(static_id)`. Lines 162-165 check `if tcx.is_thread_local_static(static_id.into())` and emit `diagnostics::NestedStaticInThreadLocal`:
`error: #[thread_local] does not support implicit nested statics, please create explicit static items and refer to them instead` (`thread_local_nested_static_rejected`, `rc = 1` on both `1.98.0-nightly` and `1.102.0-nightly`).

---

### 4. Specification Falsehoods in `core::intrinsics::const_deallocate` and CTFE-vs-Runtime/Miri Fallback Divergence

Basis: documentation + source + execution + derived

#### 4.1 Direct Contradiction Between `core` `# Safety` Docstring and CTFE Implementation

In `library/core/src/intrinsics/mod.rs` (L2721-2737 at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`; L2725-2741 at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`; L2643-2660 at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `const_deallocate` states:

```rust
/// Deallocates a memory which allocated by `intrinsics::const_allocate` at compile time.
/// At runtime, it does nothing.
///
/// # Safety
///
/// - The `align` argument must be a power of two.
///    - At compile time, a compile error occurs if this constraint is violated.
///    - At runtime, it is not checked.
/// - If the `ptr` is created in an another const, this intrinsic doesn't deallocate it.
/// - If the `ptr` is pointing to a local variable, this intrinsic doesn't deallocate it.
#[rustc_const_unstable(feature = "core_intrinsics", issue = "none")]
#[rustc_nounwind]
#[rustc_intrinsic]
#[miri::intrinsic_fallback_is_spec]
pub const unsafe fn const_deallocate(_ptr: *mut u8, _size: usize, _align: usize) {
    // Runtime NOP
}
```

Compare the third `# Safety` bullet (`"If the ptr is pointing to a local variable, this intrinsic doesn't deallocate it"`) against the actual CTFE handler (`const_eval/machine.rs:522-550` at `3ef0c22cd`; `const_eval/intrinsics.rs:53-81` at `342d74463`):

```rust
sym::const_deallocate => {
    let ptr = self.read_pointer(&args[0])?;
    let size = self.read_scalar(&args[1])?.to_target_usize(self)?;
    let align = self.read_scalar(&args[2])?.to_target_usize(self)?;

    let size = Size::from_bytes(size);
    let align = match Align::from_bytes(align) {
        Ok(a) => a,
        Err(err) => {
            throw_ub_format!("invalid align passed to `const_deallocate`: {err}")
        }
    };

    // If an allocation is created in an another const,
    // we don't deallocate it.
    let (alloc_id, _, _) = self.ptr_get_alloc_id(ptr, 0)?;
    let is_allocated_in_another_const = matches!(
        self.tcx.try_get_global_alloc(alloc_id),
        Some(interpret::GlobalAlloc::Memory(_))
    );

    if !is_allocated_in_another_const {
        self.deallocate_ptr(
            ptr,
            Some((size, align)),
            interpret::MemoryKind::Machine(MemoryKind::Heap { was_made_global: false }),
        )?;
    }
}
```

The implementation **never** checks for `MemoryKind::Stack`. Instead, it forwards stack-local pointers directly to `deallocate_ptr` (`interpret/memory.rs:380-434`), where `alloc_kind` (`MemoryKind::Stack`) fails `if alloc_kind != kind` (L418-422) against `MemoryKind::Machine(Heap { was_made_global: false })`, immediately throwing `E0080` UB:

```text
error[E0080]: deallocating alloc2, which is stack variable memory, using heap allocation deallocation operation
```

#### 4.2 Complete CTFE vs. Runtime/Miri Dispatch Matrix for `const_deallocate`

| Pointer / Allocation Class | `align` Valid (`2^k`)? | `core` Docstring Claim | Observed CTFE Behavior (`1.98` & `1.102`) | Observed Runtime & Miri Behavior (`1.98` SB/TB & `1.102`) |
| :--- | :--- | :--- | :--- | :--- |
| Same-const transient `const_allocate` (`Heap { was_made_global: false }`), exact `(size, align)`, offset `0` | Yes | Deallocates | **Deallocates** (`rc = 0`, moves `alloc_id` to `dead_alloc_map`) | **NOP** (`rc = 0`) |
| Same-const stack local (`let mut x: u8 = 7; &raw mut x`) | Yes | *"doesn't deallocate it"* (implies NOP) | **`E0080` UB** (`rc = 1`): `deallocating alloc2, which is stack variable memory, using heap allocation deallocation operation` | **NOP** (`rc = 0`) |
| Other `const` interned memory (`GlobalAlloc::Memory`), exact or **wrong** `size` (`999`) | Yes | *"doesn't deallocate it"* | **NOP** (`rc = 0`): skips `deallocate_ptr`, bypassing offset and size checks (`dealloc_other_const_wrong_size_is_noop`) | **NOP** (`rc = 0`) |
| Other `const` interned memory (`GlobalAlloc::Memory`) | **No (`align = 3`)** | *"compile error occurs"* | **`E0080` UB** (`rc = 1`): `invalid align passed to const_deallocate: 3 is not a power of 2` (checked **before** `is_allocated_in_another_const`) | **NOP** (`rc = 0`, unchecked!) |
| `static` item (`GlobalAlloc::Static`) | Yes | Undocumented | **`E0080` UB** (`rc = 1`): `deallocating alloc1, which is static memory` (`memory.rs:407-409`) | **NOP** (`rc = 0`) |
| Same-const `const_make_global` allocation (`Heap { was_made_global: true }`, `mutbl = Not`) | Yes | Undocumented | **`E0080` UB** (`rc = 1`): `deallocating immutable allocation alloc2` (`memory.rs:415-417`, checked **before** `alloc_kind != kind`!) | **NOP** (`rc = 0`) |

Notice the subtle check ordering inside `deallocate_ptr` (`memory.rs:386-433`):
1. `Align::from_bytes(align)` in `sym::const_deallocate` (throws `invalid align` even for cross-`const` `GlobalAlloc::Memory`),
2. `ptr_get_alloc_id(ptr, 0)` (throws on integer/dangling-prov pointer without provenance),
3. `matches!(try_get_global_alloc(alloc_id), Some(GlobalAlloc::Memory(_)))` (returns `Ok(())` immediately, skipping steps 4-8!),
4. `offset.bytes() != 0` check (`memory.rs:389-393`),
5. `alloc_map.remove(&alloc_id)` (`memory.rs:395-413`, failing with `static memory` on `GlobalAlloc::Static` or `PointerUseAfterFree` on dangling pointers),
6. `alloc.mutability.is_not()` check (`memory.rs:415-417`, firing on same-const `const_make_global` allocations **before** the kind mismatch check),
7. `alloc_kind != kind` check (`memory.rs:418-422`, firing on `MemoryKind::Stack` and `MemoryKind::CallerLocation`),
8. `(size, align)` equality check (`memory.rs:423-433`).

#### 4.3 Miri `#[miri::intrinsic_fallback_is_spec]` Violation and Observable CTFE-vs-Runtime Value Divergence

In `src/tools/miri/src/intrinsics/mod.rs:62-78` (at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), Miri refuses to execute any intrinsic's Rust fallback body unless that intrinsic carries `#[miri::intrinsic_fallback_is_spec]`, and explicitly documents the soundness precondition for that attribute in its diagnostic message:

> `"Miri can only use intrinsic fallback bodies that exactly reflect the specification: they fully check for UB and are as non-deterministic as possible. After verifying that `{intrinsic_name}` does so, add the `#[miri::intrinsic_fallback_is_spec]` attribute to it"`

All three `const_heap` intrinsics carry `#[miri::intrinsic_fallback_is_spec]` (`library/core/src/intrinsics/mod.rs:2714, 2734, 2745` at `3ef0c22cd`), yet their fallback bodies are:
- `const_allocate(_size, _align) -> *mut u8 { crate::ptr::null_mut() }` — does **not** check that `_align` is a power of two (even though `# Safety` states `"The align argument must be a power of two"` and notes `"At runtime, it is not checked"`!).
- `const_deallocate(_ptr, _size, _align) {}` — checks **nothing** (`_ptr`, `_size`, `_align`).
- `const_make_global(ptr) -> *const u8 { ptr }` — returns `ptr` unchanged for **any** pointer (stack, non-zero offset, dangling, or already global), even though the docstring states `"The pointer must point to the beginning of a heap allocation"`.

Consequently, Miri executes the fallback bodies with zero UB detection, matching native runtime behavior while diverging starkly from CTFE on the exact same `const fn`:

```rust
const unsafe fn probe_dual() -> (bool, u8) {
    unsafe {
        let p = core::intrinsics::const_allocate(1, 1);
        if !p.is_null() {
            *p = 88;
            let gp = core::intrinsics::const_make_global(p);
            (true, *gp)
        } else {
            let mut x: u8 = 77;
            core::intrinsics::const_deallocate(&raw mut x, 999, 3);
            let bad_alloc = core::intrinsics::const_allocate(1, 3);
            let gp = core::intrinsics::const_make_global(&raw mut x);
            (bad_alloc.is_null() && !gp.is_null(), *gp)
        }
    }
}
```

Executing `probe_dual()` as both `const CTFE_VAL = unsafe { probe_dual() };` and a runtime call in `main()` produces:
- Native `rustc 1.98.0-nightly (14210df0e)`: `compile_rc = 0`, `run_rc = 0`, `stdout = "CTFE=(true, 88) RUNTIME=(true, 77)"`.
- Miri `0.1.0 (14210df0e)` default (Stacked Borrows): `rc = 0`, `stdout = "CTFE=(true, 88) RUNTIME=(true, 77)"`, `stderr = ""`.
- Miri `0.1.0 (14210df0e)` with `-Zmiri-tree-borrows`: `rc = 0`, `stdout = "CTFE=(true, 88) RUNTIME=(true, 77)"`, `stderr = ""`.
- Preserved `rustc 1.102.0-nightly (3ef0c22cd)` native + Miri runs: identical `CTFE=(true, 88) RUNTIME=(true, 77)` with `rc = 0`.

This directly refutes any assumption that a `const fn` using `const_heap` satisfies CTFE-to-runtime behavioral refinement (`eval_ctfe(f) == eval_runtime(f)`) or that Miri enforces `const_heap`'s `# Safety` preconditions at runtime.

---

### 5. Repaired Semantics and Kernel-Checked Lean `v4.34.1` Formalization

Basis: derived + execution (Lean `v4.34.1` kernel check)

To eliminate both ICEs without weakening Rust's read-only global memory invariants, two minimal, orthogonal repairs suffice:

1. **Repair #1 (`const_make_global` provenance upgrade — fixes ICE #1 for returned pointers):**
   In `sym::const_make_global` (`const_eval/intrinsics.rs:83-87` at HEAD; `machine.rs:552-556` at `3ef0c22cd`), update the written pointer's provenance after `make_const_heap_ptr_global(ptr)?`:
   ```rust
   sym::const_make_global => {
       let ptr = self.read_pointer(&args[0])?;
       self.make_const_heap_ptr_global(ptr)?;
       let ptr = ptr.map_provenance(|p| p.map(CtfeProvenance::as_immutable));
       self.write_pointer(ptr, dest)?;
   }
   ```
   Using `CtfeProvenance::as_immutable` sets both `IMMUTABLE_MASK` and `SHARED_REF_MASK`, preserving `CtfeProvenance`'s invariant (`immutable => shared_ref`), immediately blocking subsequent writes through the returned pointer in `before_memory_write` (`machine.rs:1184`), and satisfying `prov.shared_ref() == true` in `intern_const_alloc_recursive` (`intern.rs:304`).
   *Pre-call alias caveat:* Because `CtfeProvenance` lives per-pointer value (not per-allocation), a caller that saves `let alias = p; let _ = const_make_global(p); alias as *const u8` still passes `alias` with `shared_ref = false`. Eliminating ICE #1 for pre-call aliases as well requires either (a) treating `MemoryKind::Heap { was_made_global: true }` as exempt from `found_bad_mutable_ptr` in `intern.rs:302-323` (sound because `make_const_heap_ptr_global` already froze the entire allocation to `Mutability::Not`), or (b) emitting a clean non-ICE error (`InternError::BadMutablePointer`) rather than `span_bug!`.

2. **Repair #2 (`prepare_alloc` made-global heap exemption — fixes ICE #2 without un-freezing):**
   In `prepare_alloc` (`interpret/intern.rs:64-94`), preserve `Mutability::Not` for `Heap { was_made_global: true }` regardless of `mutability` (`reqMutbl`):
   ```rust
   match kind {
       MemoryKind::Machine(const_eval::MemoryKind::Heap { was_made_global }) => {
           if !was_made_global {
               tcx.dcx().delayed_bug("non-global heap allocation in const value");
               return Err(InternError::ConstAllocNotGlobal);
           }
           // Already frozen immutable by `make_const_heap_ptr_global`; never un-freeze
           // even when reachable from a `static mut` initializer.
           assert_eq!(alloc.mutability, Mutability::Not);
       }
       MemoryKind::Stack | MemoryKind::CallerLocation => {
           match mutability {
               Mutability::Not => alloc.mutability = Mutability::Not,
               Mutability::Mut => assert_eq!(alloc.mutability, Mutability::Mut),
           }
       }
   }
   ```
   Downstream `intern_as_new_static` (`intern.rs:156`) **already** reads `mutability: alloc.0.mutability` from the prepared allocation (not from `inner_mutability`), so the synthesized nested static automatically receives `Mutability::Not` (placed in read-only memory). Furthermore, if user code attempts to place a `&mut u8` pointing to that frozen `const_make_global` allocation inside `static mut`, `const_validate_mplace` (`validity.rs:813-823`) catches `ptr_expected_mutbl == Mutability::Mut && alloc_actual_mutbl == Mutability::Not` and rejects it cleanly with `"encountered mutable reference or box pointing to read-only memory"`, while legitimately permitting `static mut CUR: &'static u8` or `static mut PTR: *const u8` to point at immutable compile-time heap buffers.

#### Mechanized Formalization (`support/ConstHeapInterningAndMakeGlobalSoundness.lean`)

The standalone Lean `v4.34.1` module (`1,664` lines, `70,337` bytes, `40` explicit `theorem` declarations, `454` kernel constants, `106` kernel theorem/equation-lemma entries) formalizes the full `CtfeProvenance`, `LocalAllocKind`, `constAllocate`, `constDeallocate`, `deallocatePtr`, `makeConstHeapPtrGlobal`, `constMakeGlobalBuggy`, `constMakeGlobalFixed`, `retagSharedRef`, `ctfeWriteCheck`, `prepareAllocBuggy`, `prepareAllocFixed`, `internShallow`, `internLoop`, `internConstAllocRecursive`, and runtime/Miri fallback semantics. All 40 theorems were kernel-checked under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` with zero warnings, zero `sorry`, zero `Classical.choice` (only `[propext]` or `[propext, Quot.sound]`), zero `omega`, zero `bv_decide`, zero `native_decide`, zero `partial def`, and zero `._unsafe_rec` constants across both `env.constants.map₁` and `env.constants.map₂`.

| Theorem Group | Lean Theorem Identifier(s) | Quantified Property Proven | Kernel Axioms |
| :--- | :--- | :--- | :--- |
| **Provenance & Retagging** | `CtfeProvenance.fromAllocId_wf`, `asSharedRef_wf`, `asImmutable_wf`, `retagSharedRef_sets_sharedRef` | `fromAllocId`, `asSharedRef`, `asImmutable`, and `retagSharedRef` preserve `immutable = true -> sharedRef = true`, and `retagSharedRef` guarantees `sharedRef = true` for both `Freeze` and `!Freeze`. | `[propext]` |
| **ICE #1 Reproduction & Mitigations** | `buggy_constMakeGlobal_raw_ptr_triggers_intern_ice1_const`, `buggy_constMakeGlobal_raw_ptr_triggers_intern_ice1_static`, `buggy_constMakeGlobal_raw_ptr_unleash_miri_not_ice1`, `reborrow_shared_ref_avoids_ice1_const` | `constAllocate` + `constMakeGlobalBuggy` raw pointer triggers `.fail .ice1BadMutablePtrSpanBug` for `const` and `static` (`rootIsFreeze ∈ {true, false}`); `unleashMiri = true` yields `.fail .errBadMutablePointer`; `retagSharedRef` yields `.ok st'` for `isFreeze ∈ {true, false}`. | `[propext]` |
| **ICE #2 & `static mut` Catch-22** | `buggy_prepareAlloc_static_mut_triggers_ice2`, `static_mut_catch22_deadlock_in_buggy_rustc`, `thread_local_static_nested_const_heap_rejected`, `static_mut_preinterned_const_avoids_ice2_in_buggy_rustc` | For all `(immutable, sharedRef, unleashMiri : Bool)`, `static mut` + same-eval `const_make_global` unconditionally hits `.fail .ice2PrepareAllocMutAssertFailed`, while omitting `const_make_global` hits `.fail .errConstAllocNotGlobal`; pre-interned `GlobalAlloc::Memory` compiles `.ok st'` with `g.mutbl = .not`; `#[thread_local]` hits `.fail .errNestedStaticInThreadLocal`. | `[propext]` |
| **`const_deallocate` Contract Contradictions** | `constDeallocate_stack_local_contradicts_core_docstring`, `constDeallocate_cross_const_memory_noop_and_align_order`, `constDeallocate_static_item_throws_ub`, `constDeallocate_same_const_after_make_global_throws_ub` | Universally over arbitrary states `st`, stack locals throw `.error .deallocWrongKind`; cross-const `GlobalAlloc::Memory` ignores arbitrary `wrongSize` on power-of-two `align` but throws `.error .invalidAlign` on non-power-of-two `align` first; `GlobalAlloc::Static` throws `.error .deallocStaticMemory`; same-const frozen heap throws `.error .deallocImmutable`. | `[propext]` |
| **CTFE vs. Runtime/Miri Divergence** | `ctfe_vs_runtime_fallback_divergence` | Universally over any state `st` with fresh `nextId`, `evalDualProbeCtfe st = .ok (true, 88)` while `evalDualProbeRuntime stackPtr = (true, 77)`, and `constAllocate st 1 3 = .error .invalidAlign` while `runtimeConstAllocate 1 3 = nullPtr`. | `[propext, Quot.sound]` |
| **Repaired Post-Freeze Safety** | `constMakeGlobalFixed_correct_and_blocks_post_freeze_ops` | Universally over any `st`, `size`, power-of-two `align`, `constMakeGlobalFixed` returns `{ allocId := st.nextId, immutable := true, sharedRef := true }`, freezes `alloc.mutbl = .not`, and causes subsequent `constMakeGlobalFixed`, `constDeallocate`, and `ctfeWriteCheck` (via both new and pre-call pointers) to fail cleanly. | `[propext, Quot.sound]` |
| **Universal Repaired Immutability & No-Transient-Escape Soundness** | `prepareAllocFixed_sound`, `internShallow_fixed_preserves_invariants`, `internLoop_fixed_immutability_and_no_transient_escape`, `repaired_interning_immutability_soundness` | By structural induction over arbitrary worklist `fuel` and all `InternKind` variants: whenever `internConstAllocRecursive .fixed st kind baseId fuel = .ok st'`, `GlobalHeapImmutable st'` holds (every heap-origin entry in `st'.globalMap` has `mutbl = .not`, even for `static mut`), and every newly interned allocation had `orig.kind ≠ .heap false` (zero transient escape). | `[propext, Quot.sound]` |
| **Universal ICE-Freedom & Completeness** | `prepareAllocFixed_complete`, `removeLocal_preserves_ready`, `internLoop_fixed_ice_free`, `repaired_constMakeGlobal_and_prepareAlloc_succeeds_all_four_contexts` | For arbitrary well-formed heaps (`HeapInvariants st ∧ AllLocalReadyForIntern st`), `isThreadLocal = false`, and `sharedRef = true` worklists, `internLoop .fixed` **never** raises ICE #1, ICE #2, `errBadMutablePointer`, or `errConstAllocNotGlobal`; end-to-end raw `*const u8` succeeds across all four contexts (`const`, `promoted`, `static`, `static mut`) with `g.mutbl = .not`. | `[propext, Quot.sound]` |
| **Pre-Call Alias Boundary** | `repaired_constMakeGlobalFixed_precall_alias_boundary` | Proves that fixing only `const_make_global`'s return value leaves a pre-call alias `p` with `sharedRef = false`, still triggering `.fail .ice1BadMutablePtrSpanBug` under strict `internLoop`. | `[propext]` |

---

### 6. Implications for Verified Compilers and the `joshlf/anneal` Trusted Boundary

Basis: source + derived

Direct inspection of `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean`) establishes how Anneal's current trusted boundary interacts with `const_heap` and interned global allocations, and what invariants future extensions must enforce:

1. **Current Fail-Closed Status in `joshlf/anneal@c131b320e`:**
   - `Trusted.MirAst.ConstLit` (`MirAst.lean:492-505`) models only `.scalar (bits : BitVec 128)` (`ConstValue::Scalar(Scalar::Int)`) and `.zeroSized` (`ConstValue::ZeroSized`); pointer, slice, and `ConstValue::Indirect` constants lower fail-closed to `.unsupported`.
   - `Trusted.MirAst.TerminatorKind.call` (`MirSemantics.lean:1691-1694`) steps to `.fault .unsupported`, and `BodyStaticAdmitted` (`MirSemantics.lean:1730-1737`) requires `body.locals.all isSupportedScalarOrUnitTy` (excluding raw pointer/reference locals and `const_heap` intrinsics).
   - Therefore, at `c131b320e`, no crate using `const_heap` or interned pointer constants can bypass `BodyVerified` / `ProgramVerified` soundness: all such bodies are rejected fail-closed.
2. **Mandatory Invariants for Future Verified-`rustc` / Anneal CTFE Ingestion:**
   - **Never identify CTFE and runtime semantics for `const_heap` intrinsics:** Because `const_allocate`, `const_deallocate`, and `const_make_global` execute completely different specifications at CTFE vs. runtime/Miri (`CTFE=(true, 88)` vs. `RUNTIME=(true, 77)`), a verified compiler or MIR verifier must model them as **mode-indexed** operations (or reject runtime calls to `const_heap` intrinsics unless their fallback behavior is explicitly specified), never assuming CTFE evaluation refines runtime execution.
   - **Do not rely on Miri to detect `const_heap` `# Safety` violations at runtime:** Because `#[miri::intrinsic_fallback_is_spec]` bypasses UB checks in Miri for all three intrinsics, differential testing against Miri will **silently pass** invalid alignments (`align = 3`), bogus sizes, and stack-local `const_deallocate` / `const_make_global` calls that are `E0080` UB in CTFE.
   - **Distinguish `GlobalAlloc::Memory` vs. `GlobalAlloc::Static` and `Mutability` at the global-table boundary:** Any future `Trusted.MirSemantics` extension ingesting `tcx` global allocations must carry an explicit `originKind` / `mutability` tag per `AllocId` and enforce `GlobalHeapImmutable`: every interned `const_make_global` allocation MUST enter the global store as read-only (`Mutability::Not`), even when its root referrer is a `static mut`.
   - **Never trust `library/core` `# Safety` comments as normative over `rustc_const_eval` source:** The `const_deallocate` stack-local bullet demonstrates live documentation-vs-implementation divergence inside `rust-lang/rust`'s own `libcore`. Every intrinsic modeled in a trusted boundary must be audited directly against `compiler/rustc_const_eval/src/const_eval/{machine,intrinsics}.rs`, `interpret/memory.rs`, and `src/tools/miri/src/intrinsics/mod.rs`.

## Boundaries

- **Other `rustc` channels and releases — `not examined`:** Stable and beta `rustc` toolchains do not expose `#![feature(const_heap)]` without `RUSTC_BOOTSTRAP=1`, and nightlies outside `1.98.0-nightly (14210df0e)`, `1.102.0-nightly (3ef0c22cd)`, and `2026-11-22` HEAD (`342d74463`) were not executed or inspected.
- **Direct binary execution of `rust-lang/rust` HEAD (`342d74463`) — `not examined`:** HEAD (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`) was verified by primary-source inspection and exact file diff against `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`memory.rs` and `intern.rs` are byte-for-byte identical; `intrinsics.rs:34-87` is line-for-line equivalent to `machine.rs:503-556`). No compiler binary built from `342d74463` was executed directly.
- **Non-`x86_64-unknown-linux-gnu` host/target triples — `not examined`:** All empirical runs targeted `x86_64-unknown-linux-gnu`. Architecture independence of the CTFE/interning bugs is derived from target-independent `rustc_const_eval` source rather than multi-target execution.
- **Miri execution with full `std` under `cargo miri` — `not examined` (on `1.98.0-nightly`):** Offline `1.98.0-nightly` Miri execution compiled a MIR-encoded `libcore` + `compiler_builtins` sysroot and executed `#![no_std]` `#![no_main]` `miri_start` directly under `miri` (both Stacked Borrows and `-Zmiri-tree-borrows`). Full-`std` `cargo miri` execution was recorded on `1.102.0-nightly (3ef0c22cd)` (`support/probe_results_1_102_nightly.json`).
- **Promoted temporaries (`InternKind::Promoted`) containing `const_make_global` — `unknown`:** Although `intern.rs:302` explicitly exempts `InternKind::Promoted` from the `!prov.shared_ref()` check, promotion analysis (`promote_consts.rs`) generally refuses to promote calls to unsafe/unstable intrinsics like `const_allocate`/`const_make_global`; whether any unsafe promotion path can trigger `const_make_global` inside `InternKind::Promoted` was not tested empirically.
- **`const_make_global` on zero-sized allocations (`const_allocate(0, 1)`) and partial-pointer provenance (`alloc.provenance_merge_bytes == false`) — `not examined` empirically:** `prepare_alloc` checks `provenance_merge_bytes` at `intern.rs:76-80` (modeled in Lean via `hasPartialPtr` -> `.errPartialPointer`), but concrete Rust reproducers constructing partial pointers inside `const_allocate` buffers or testing zero-sized `const_allocate(0, 1)` were not included in the 30-case matrix.
- **Formal model scope vs. full `rustc` MIR semantics — `known not to apply`:** `support/ConstHeapInterningAndMakeGlobalSoundness.lean` is a standalone, self-contained formalization of the CTFE allocation/provenance/interning state machine (`IMPORTS: []` of `joshlf/anneal`). It does **not** import `Trusted.MirSemantics`, does not model MIR control-flow evaluation, byte-level memory reads/writes, `RefTracking` in `const_validate_mplace`, or LLVM codegen placement in `.rodata`/`.data`. Its universal theorems establish properties of the modeled `const_allocate`/`const_deallocate`/`const_make_global`/`intern_const_alloc_recursive` transition system, not full end-to-end `rustc` compiler soundness.
- **Stabilization timeline / upstream fix PRs — `unknown`:** Whether upstream `rust-lang/rust` intends to fix ICE #1 via `CtfeProvenance::as_immutable` in `const_make_global`, via an interner exemption for `was_made_global`, or by redesigning `#![feature(const_heap)]` (`issue #79597`) is an open design question outside the examined revisions.
- **Stabilized Rust usage — `unsupported`:** `#![feature(const_heap)]` and `#![feature(core_intrinsics)]` are nightly-only unstable features; none of the reproducers compile on stable Rust without `RUSTC_BOOTSTRAP=1`.

## Evidence

### 1. Pinned Primary-Source Locations

All commit SHAs below were resolved live via GitHub API on `2026-11-22`:

- **`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, `2026-11-11`):**
  - `compiler/rustc_const_eval/src/const_eval/machine.rs`: `MemoryKind::Heap { was_made_global }` and `MayLeak` (L177-203); `sym::const_allocate` (L503-521); `sym::const_deallocate` (L522-550); `sym::const_make_global` (L552-556); `CompileTimeMachine::retag_ptr_value` (L1125-1158); `before_memory_write` (L1171-1189).
  - `compiler/rustc_const_eval/src/interpret/memory.rs`: `InterpCx::make_const_heap_ptr_global` (L335-377, setting `*was_made_global = true` at L369 and `alloc.mutability = Mutability::Not` at L374); `InterpCx::deallocate_ptr` (L380-450, checking `GlobalAlloc::Static | GlobalAlloc::Memory` at L407-409, `alloc.mutability.is_not()` at L415-417, `alloc_kind != kind` at L418-422, layout match at L423-433); `take_leaked_allocations` (L1155-1178).
  - `compiler/rustc_const_eval/src/interpret/intern.rs`: `prepare_alloc` (L58-95, `!was_made_global` at L66-71, `provenance_merge_bytes` at L76-80, `assert_eq!(alloc.mutability, Mutability::Mut)` at L91); `intern_shallow` (L104-138); `intern_as_new_static` (L142-177, `mutability: alloc.0.mutability` at L156, `NestedStaticInThreadLocal` at L162-165); `intern_const_alloc_recursive` (L204-357, `Static(Mut)` at L236-240, `!prov.shared_ref()` at L302-323, `try_get_global_alloc` skip at L324-328, `unleash_the_miri_inside_of_you` vs. `span_bug!` at L343-355).
  - `compiler/rustc_const_eval/src/const_eval/eval_queries.rs`: `eval_body_using_ecx` (L94-143); `intern_and_validate` (L161-210); `const_validate_mplace` (L478-506).
  - `compiler/rustc_const_eval/src/const_eval/error.rs`: `ConstMakeGlobalPtrAlreadyMadeGlobal`, `ConstMakeGlobalPtrIsNonHeap`, `ConstMakeGlobalWithDanglingPtr`, `ConstMakeGlobalWithOffset` (L35-43, L66-84).
  - `compiler/rustc_const_eval/src/diagnostics.rs`: `DanglingPtrInFinal`, `NestedStaticInThreadLocal`, `MutablePtrInFinal`, `ConstHeapPtrInFinal`, `PartialPtrInFinal` (L13-80; `ConstHeapPtrInFinal` at L55-63).
  - `compiler/rustc_const_eval/src/interpret/validity.rs`: mutable-ref-to-read-only-memory check (L800-824); `ty::RawPtr` handling skipping provenance `shared_ref` checks (L917-934).
  - `compiler/rustc_const_eval/src/check_consts/check.rs`: `Rvalue::Ref(_, BorrowKind::Mut, _) | Rvalue::RawPtr(RawPtrKind::Mut, _)` check (L549-561).
  - `compiler/rustc_middle/src/mir/interpret/pointer.rs`: `CtfeProvenance` bit masks and `as_immutable`/`as_shared_ref` (L82-164).
  - `library/core/src/intrinsics/mod.rs`: `const_allocate` (L2703-2719), `const_deallocate` (L2721-2737, false local-variable `# Safety` claim at L2730), `const_make_global` (L2739-2749), all carrying `#[miri::intrinsic_fallback_is_spec]`.
  - `src/tools/miri/src/intrinsics/mod.rs`: `#[miri::intrinsic_fallback_is_spec]` dispatch and UB-specification invariant message (L62-78).
- **`rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (HEAD, `2026-11-22`):**
  - `compiler/rustc_const_eval/src/const_eval/machine.rs:514` delegates to `compiler/rustc_const_eval/src/const_eval/intrinsics.rs:34-87` (`const_allocate` L34-52, `const_deallocate` L53-81, `const_make_global` L83-87).
  - `compiler/rustc_const_eval/src/interpret/memory.rs` and `compiler/rustc_const_eval/src/interpret/intern.rs` are byte-for-byte identical to `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`.
  - `library/core/src/intrinsics/mod.rs:2725-2753` retains the identical false local-variable bullet (L2734) and `#[miri::intrinsic_fallback_is_spec]` annotations.
- **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`):**
  - `compiler/rustc_const_eval/src/const_eval/machine.rs:489-542`, `interpret/memory.rs:335-434`, `interpret/intern.rs:91` (ICE #2) and `intern.rs:349` (ICE #1), `library/core/src/intrinsics/mod.rs:2643-2672` (false local-variable bullet at L2652).
- **`rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`2026-11-17`):**
  - `src/const_eval.md` (constant expressions, static access restrictions, escaping mutable temporary borrows `E0764`).
  - `src/items/static-items.md` (`items.static.intro`, `items.static.storage-disjointness`, `items.static.read-only`, `items.static.mut.safety`).
- **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`):**
  - `trusted/lean/Trusted/MirAst.lean`: `ConstLit` (L492-505), `Operand` / `Rvalue` (L506-628), `StatementKind` (L630-662), `TerminatorKind` (L742-795).
  - `trusted/lean/Trusted/MirSemantics.lean`: `BodyStaticAdmitted` (L1730-1737), `BodyVerified` (L1751-1758), `ProgramVerified` (L1786-1795).

### 2. Empirical Compiler & Miri Execution Records

All preserved probe artifacts live inside this package's `support/` directory:
- `support/probe_const_heap_make_global_ices_and_interning.py`: Standalone Python 3.10+ script (stdlib only) that compiles all 15 core cases and 15 extended boundary cases with `rustc --crate-type=lib --edition=2024`, compiles and runs the native dual CTFE/runtime binary, builds an offline MIR-encoded `libcore` + `compiler_builtins` sysroot, and executes the dual probe under `miri` in both Stacked Borrows and `-Zmiri-tree-borrows` modes.
- `support/probe_results_1_98_nightly.json` (captured `2026-11-22` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `miri 0.1.0 (14210df0e 2026-05-31)`).
- `support/probe_results_1_102_nightly.json` (preserved scrubbed capture from `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` + `miri`, matching all 15 core cases and dual-execution stdout).

#### Complete 30-Case Empirical Matrix (`rustc 1.98.0-nightly` + `rustc 1.102.0-nightly` Comparison)

| # | Case ID | `1.98` `rc` | `1.102` `rc` | ICE? | Observed Outcome / Exact Diagnostic Summary |
| ---: | :--- | ---: | ---: | :---: | :--- |
| 1 | `valid_const_reborrowed_shared_ref` | `0` | `0` | No | Clean compile (`&*const_make_global(p)` sets `as_immutable` / `shared_ref = true`). |
| 2 | `valid_static_reborrowed_shared_ref` | `0` | `0` | No | Clean compile (creates immutable `NestedStatic`). |
| 3 | `ice1a_const_raw_ptr_from_const_make_global` | `101` | `101` | **Yes** | **ICE #1:** `intern.rs:349:13` (`1.98`) / `350:13` (`1.102`): `the static const safety checks accepted a mutable pointer they should not have accepted`. |
| 4 | `ice1b_static_raw_ptr_from_const_make_global` | `101` | `101` | **Yes** | **ICE #1:** identical `span_bug!` on immutable `static SyncPtr(*const u8)`. |
| 5 | `reborrow_to_raw_ptr_avoids_ice1` | `0` | `0` | No | Clean compile (`(&*const_make_global(p)) as *const u8` retags via `retag_ptr_value`). |
| 6 | `ice2a_static_mut_reborrowed_ref` | `101` | `101` | **Yes** | **ICE #2:** `intern.rs:91:13`: `assertion left == right failed` (`left: Not`, `right: Mut`). |
| 7 | `ice2b_static_mut_raw_ptr` | `101` | `101` | **Yes** | **ICE #2:** identical `intern.rs:91:13` panic on `static mut SM_RAW: *const u8`. |
| 8 | `doc_contradiction_dealloc_stack_local` | `1` | `1` | No | `E0080: deallocating alloc2, which is stack variable memory, using heap allocation deallocation operation` (contradicts `core` `# Safety`). |
| 9 | `dealloc_other_const_memory_is_noop` | `0` | `0` | No | Clean compile (`GlobalAlloc::Memory` skipped by `is_allocated_in_another_const`). |
| 10 | `dealloc_static_item_throws_ub` | `1` | `1` | No | `E0080: deallocating alloc1, which is static memory`. |
| 11 | `dealloc_same_const_after_make_global_throws_ub` | `1` | `1` | No | `E0080: deallocating immutable allocation alloc2`. |
| 12 | `uninterned_transient_const_allocate_rejected` | `1` | `1` | No | `error: encountered const_allocate pointer in final value that was not made global`. |
| 13 | `make_global_nonzero_offset_rejected` | `1` | `1` | No | `E0080: making alloc2+0x1 global which does not point to the beginning of an object`. |
| 14 | `make_global_twice_rejected` | `1` | `1` | No | `E0080: attempting to call const_make_global twice on the same allocation alloc2`. |
| 15 | `thread_local_nested_static_rejected` | `1` | `1` | No | `error: #[thread_local] does not support implicit nested statics, please create explicit static items and refer to them instead`. |
| 16 | `ice1a_with_unleash_miri_downgrades_to_normal_error` | `1` | — | No | `-Z unleash-the-miri-inside-of-you` -> `error: encountered mutable pointer in final value of constant`. |
| 17 | `ice2a_with_unleash_miri_still_ices` | `101` | — | **Yes** | `-Z unleash-the-miri-inside-of-you` still panics at `intern.rs:91:13` (`left: Not, right: Mut`). |
| 18 | `static_mut_preinterned_const_avoids_ice2` | `0` | — | No | Pre-interned `const PRE: &'static u8` referenced by `static mut SM_PRE` compiles cleanly. |
| 19 | `static_mut_uninterned_transient_rejected_not_ice` | `1` | — | No | `ConstHeapPtrInFinal` fires at `intern.rs:66-71` before `assert_eq!` at L91. |
| 20 | `static_mut_raw_ptr_via_preinterned_const_avoids_both_ices` | `0` | — | No | Pre-interned reborrowed `*const u8` in `static mut` compiles cleanly. |
| 21 | `reborrow_cell_nonfreeze_to_raw_ptr_avoids_ice1` | `0` | — | No | `!Freeze` `Cell<u8>` reborrow sets `SHARED_REF_MASK` via `as_shared_ref`, avoiding ICE #1. |
| 22 | `pre_call_alias_after_make_global_still_triggers_ice1` | `101` | — | **Yes** | Discarding `const_make_global(p)`'s return and returning pre-call `p as *const u8` hits ICE #1. |
| 23 | `dealloc_other_const_wrong_size_is_noop` | `0` | — | No | Cross-const `const_deallocate(..., 999, 1)` silently ignores bogus size `999`. |
| 24 | `dealloc_other_const_bad_align_throws_ub_before_skip` | `1` | — | No | Cross-const `const_deallocate(..., 1, 3)` throws `E0080: invalid align` before `GlobalAlloc::Memory` check. |
| 25 | `make_global_on_stack_local_rejected` | `1` | — | No | `E0080: pointer passed to const_make_global does not point to a heap allocation: alloc2`. |
| 26 | `make_global_on_dangling_heap_rejected` | `1` | — | No | `E0080: pointer passed to const_make_global is dangling: alloc2`. |
| 27 | `write_after_make_global_throws_ub` | `1` | — | No | `E0080: writing to alloc2 which is read-only`. |
| 28 | `transient_alloc_write_read_dealloc_succeeds` | `0` | — | No | Balanced transient `const_allocate` / write / read / `const_deallocate` compiles cleanly. |
| 29 | `transient_alloc_unreachable_leak_silently_dropped` | `0` | — | No | Unreachable transient `const_allocate` never deallocated is silently dropped at end of CTFE. |
| 30 | `const_allocate_bad_align_throws_ub_in_ctfe` | `1` | — | No | `E0080: invalid align passed to const_allocate: 3 is not a power of 2` (vs. unchecked `null_mut()` at runtime/Miri). |

### 3. Lean `v4.34.1` Kernel Verification Record

Executed `2026-11-22` with `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`):

1. **Strict standalone kernel check:**
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/ConstHeapInterningAndMakeGlobalSoundness.lean
   ```
   Result: exit code `0`, zero errors, zero warnings.
2. **MetaM environment & axiom audit across `env.constants.map₁ ++ env.constants.map₂`:**
   - `AUDIT_CONST_COUNT = 454` (`ConstHeapInterning.*` declarations, recursors, projections, equation lemmas)
   - `AUDIT_THEOREM_COUNT = 106` (including all `40` explicit `theorem` declarations)
   - `AUDIT_UNSAFE_REC_COUNT = 0`
   - `AUDIT_BAD_AXIOM_COUNT = 0` (every theorem uses only subsets of `{propext, Quot.sound}`; zero `Classical.choice`, zero `sorryAx`, zero `Lean.ofReduceBool`, zero `Lean.trustCompiler`)
3. **Source hygiene scan (excluding comments):** `sorry: 0`, `Classical.choice: 0`, `omega: 0`, `bv_decide: 0`, `native_decide: 0`, `partial def: 0`, `axiom: 0`, `unsafe: 0`, `_unsafe_rec: 0`, `deriving: 0`.

## Revalidation

To cheaply determine whether these findings still hold on a newer `rust-lang/rust` nightly or after an upstream PR modifying `rustc_const_eval` or `core::intrinsics`:

1. **Fastest compiler & Miri check (~15 seconds):** Run the preserved standalone probe script against the target nightly `rustc` (with `miri` and `rust-src` components installed):
   ```console
   python3 support/probe_const_heap_make_global_ices_and_interning.py
   ```
   Inspect five discriminating outputs:
   - `matrix.ice1a_const_raw_ptr_from_const_make_global`: if `rc` changes from `101` to `0`, ICE #1 is fixed for returned raw pointers; check `extended_matrix.pre_call_alias_after_make_global_still_triggers_ice1` to see whether pre-call aliases were also fixed or downgraded to a non-ICE error.
   - `matrix.ice2a_static_mut_reborrowed_ref` and `matrix.ice2b_static_mut_raw_ptr`: if `rc` changes from `101` to `0`, ICE #2 in `prepare_alloc` is fixed; verify whether the nested static remains read-only (e.g., by checking that placing `&mut *const_make_global(p)` into `static mut` still fails validation).
   - `matrix.doc_contradiction_dealloc_stack_local`: if `rc` remains `1` (`stack variable memory`) while `library/core/src/intrinsics/mod.rs` still states `"If the ptr is pointing to a local variable, this intrinsic doesn't deallocate it"`, the specification contradiction remains live.
   - `runtime_execution.stdout`, `miri_execution.stdout`, and `miri_tree_borrows_execution.stdout`: if all three remain `CTFE=(true, 88) RUNTIME=(true, 77)` with `rc = 0`, CTFE-vs-runtime/Miri fallback divergence and unchecked `align = 3` acceptance under `#[miri::intrinsic_fallback_is_spec]` remain live.
2. **Targeted upstream source diff (zero compilation):** Diff four narrow file regions against `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`:
   - `compiler/rustc_const_eval/src/const_eval/intrinsics.rs` (`sym::const_allocate`, `sym::const_deallocate`, `sym::const_make_global`),
   - `compiler/rustc_const_eval/src/interpret/memory.rs` (`make_const_heap_ptr_global`, `deallocate_ptr`),
   - `compiler/rustc_const_eval/src/interpret/intern.rs` (`prepare_alloc`, `intern_const_alloc_recursive`),
   - `library/core/src/intrinsics/mod.rs` (`const_allocate`, `const_deallocate`, `const_make_global` doc comments and `#[miri::intrinsic_fallback_is_spec]`).
3. **Lean formalization re-check (~5 seconds):** Re-run Lean `v4.34.1` (or newer) with kernel checking forced on:
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/ConstHeapInterningAndMakeGlobalSoundness.lean
   ```
   A passing Lean run revalidates only the internal consistency of the formal model and theorems; matching the model to a newer `rustc` revision still requires checking the source regions in step 2.
