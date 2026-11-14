# CTFE, `GlobalAlloc` Provenance Graphs, `GlobalAlloc::TypeId` Lowering, Promoted Constants, and Runtime `Runtime(PostCleanup)` MIR Equivalence

## Summary

At `Runtime(PostCleanup)` MIR (`tcx.mir_drops_elaborated_and_const_checked`) in
`rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), compile-time
function evaluation (`CTFE`, `rustc_const_eval::interpret::InterpCx<CompileTimeMachine>`)
surfaces through `mir::Const` operands (`Const::Val`, `Const::Unevaluated`, and
`Const::Ty`) and the global allocation table `tcx.global_alloc(alloc_id)`.
Combining compiler source inspection, a zero-axiom Lean `v4.34.1` mechanization
([`support/CtfeRuntimeRefinementProbe.lean`](support/CtfeRuntimeRefinementProbe.lean)),
and a 30-case CTFE vs. native runtime and Miri (`0.1.0`, `3ef0c22cdb`)
differential suite and `GlobalAlloc` census
([`support/globalalloc_census.json`](support/globalalloc_census.json))
establishes four foundational contracts for `.anneal-mir` export, Anneal
verification, and `MiniSSA` codegen:

1. **Complete Taxonomy and Graph Topology of the Five `GlobalAlloc` Variants
   (`interpret/mod.rs:254-350`):**
   Every `AllocId` in a monomorphized `.anneal-mir` artifact resolves via
   `tcx.global_alloc(alloc_id)` to one of five variants:
   - `GlobalAlloc::Memory(ConstAllocation)`: byte buffer with an explicit
     `InitMask` bitset (preserving uninitialized struct/enum padding chunks up
     to `uninit_const_chunk_threshold`, lowered to `[N x i8] undef` in
     `rustc_codegen_llvm/src/consts.rs:69-97`), a `ProvenanceMap` of
     `(Size, CtfeProvenance)` relocations (supporting arbitrary interior byte
     offsets `offset >= 0`, `C17`–`C19`), and `Mutability` (`Not` -> `.rodata`
     `constant`, `Mut` -> writable `.data` `global`);
   - `GlobalAlloc::Static(DefId)`: indirection node for `static` items whose
     `GlobalAlloc::mutability` (`interpret/mod.rs:315-345`) upgrades
     `Mutability::Not` to `Mutability::Mut` whenever `!ty.is_freeze(tcx,
     typing_env)` (such as `SyncCellU64(UnsafeCell<u64>)` in `C04`, placing the
     symbol in writable `.data` rather than `.rodata`);
   - `GlobalAlloc::Function { instance }`: monomorphic function-pointer target
     (`C07`, `C08`);
   - `GlobalAlloc::VTable(Ty, List<PolyExistentialPredicate>)`: symbolic vtable
     resolved via `tcx.vtable_allocation((ty, principal))` to a synthesized
     `GlobalAlloc::Memory` allocation (`common.rs:217-226`, `C06`);
   - `GlobalAlloc::TypeId { ty }`: symbolic provenance carrier for
     `core::any::TypeId::of::<T>()` (`C09`–`C12`).
2. **Where Cycles Can and Cannot Exist in `GlobalAlloc` Provenance Graphs
   (`interpret/mod.rs:191-202`, `machine.rs:1078-1102`):**
   - **Acyclic `GlobalAlloc::Memory` DAG:** Direct `Memory -> Memory` cycles and
     mutual `const A -> const B -> const A` cycles are **impossible** in valid
     Rust crates because `const` evaluation triggers a `tcx` query-cycle error
     (`interpret/mod.rs:194-202`).
   - **Cyclic `GlobalAlloc::Static` Graphs (`C01`–`C03`):** Both self-cycles
     (`static C01: SelfRefStatic = SelfRefStatic { self_ptr: &C01 }`) and
     mutual static cycles (`C02 -> C03 -> C02`) are **valid and supported**!
     Taking `&C01` inside `C01`'s initializer creates a pointer to
     `GlobalAlloc::Static(C01_def_id)` without calling `before_alloc_access`;
     when the initializer finishes and copies its result at `machine.stack.is_empty()`,
     `CompileTimeMachine::before_alloc_access` (`machine.rs:1083-1086`) bypasses
     the `RecursiveStatic` check (`if machine.stack.is_empty() { return
     interp_ok(()); }`). By contrast, *reading* from `C01` while `C01`'s frame is
     still on the CTFE stack (`!machine.stack.is_empty()`) fails with
     `ConstEvalErrKind::RecursiveStatic` (`machine.rs:1088-1090`).
3. **Dual Compile-Time vs. Codegen Representation of `GlobalAlloc::TypeId { ty }`
   (`intrinsics.rs:86-215`, `common.rs:201-205`):**
   - `core::any::TypeId` is represented as a 16-byte wrapper around a pointer
     array (`[*const (); 2]` on 64-bit targets). In CTFE (`write_type_id`,
     `intrinsics.rs:86-120`), `rustc` writes the 128-bit SipHash-1-3
     `tcx.type_id_hash(ty).as_u128()` as the two 64-bit integer offsets and
     attaches `GlobalAlloc::TypeId { ty }` provenance to both pointer words.
   - During CTFE, `sym::type_id_eq` (`intrinsics.rs:211-215`) calls
     `read_type_id` (`intrinsics.rs:123-166`), which verifies that both pointer
     chunks carry the **exact same `GlobalAlloc::TypeId { ty }`** and matching
     hash fragments (rejecting integer-forged `TypeId`s with UB,
     `forgedIntegerTypeId_rejected_in_ctfe`), and compares `a_ty == b_ty`
     directly so a hypothetical 128-bit hash collision can never unsoundly
     equate distinct types in the type system.
   - At codegen time (`CodegenCx::alloc_to_backend` in
     `rustc_codegen_llvm/src/common.rs:201-205`), `GlobalAlloc::TypeId { .. }`
     returns `Err(0)` (dropping provenance and using base address `0`), so the
     two pointers become raw 64-bit integer constants `(hash_lo, hash_hi)` and
     runtime `TypeId` equality compares the 128-bit hashes directly. Theorem
     `typeIdEq_ctfe_runtime_agreement`
     ([`support/CtfeRuntimeRefinementProbe.lean:119-146`](support/CtfeRuntimeRefinementProbe.lean#L119-L146))
     proves that once the `.anneal-mir` exporter checks pairwise hash
     distinctness across the finite set of `GlobalAlloc::TypeId` types in the
     crate graph, CTFE `type_id_eq` and runtime 128-bit equality are
     definitionally identical.
4. **Refinement Between CTFE and Runtime `Runtime(PostCleanup)` MIR Execution
   (`ctfePure_refines_runtime`, `30 / 30` Differential Pass):**
   - Across all 5 divergence points between `CompileTimeMachine` and runtime
     execution—(i) unconditional `runtime_checks() == true` (`machine.rs:863-870`),
     (ii) rejected `expose_provenance` / `binary_ptr_op` (`machine.rs:872-879,943-949`),
     (iii) conservative `ptr_guaranteed_cmp` (`machine.rs:279-388`, returning `2`
     when unknown), (iv) deterministic canonical quiet NaN payloads vs. RFC 3514
     runtime NaN set (`C30`), and (v) `const_eval_select` (`C29`)—every
     successful CTFE evaluation of a pure `Runtime(PostCleanup)` MIR body (with
     matching `const_eval_select` arms) refines a valid runtime execution of that
     body (`ctfePure_refines_runtime`,
     [`support/CtfeRuntimeRefinementProbe.lean:206-226`](support/CtfeRuntimeRefinementProbe.lean#L206-L226)).

## Applicability

This report applies to `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), Miri `0.1.0`
(`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), and `Lean 4 v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`) when exporting, decoding,
verifying, and lowering `mir::Const` operands, promoted bodies (`promoted[N]`),
and `GlobalAlloc` graphs in `.anneal-mir`, Anneal, and `MiniSSA`.

It extends three corpus reports:
- `rustc-postcleanup-mir-const-placement-layout-folding-and-ub-checks`
- `rustc-postcleanup-mir-unevaluated-consts-promoted-bodies-and-alloc-decoding`
- `rustc-monomorphization-vtables-statics-symbols-and-cgu-partitioning`

Created: 2026-11-14 · Updated: 2026-11-14

## Findings

### 1. `.anneal-mir` Serialization and Codegen Lowering of All Five `GlobalAlloc` Variants

Basis: source + execution

When `.anneal-mir` exports a monomorphized crate graph at `Runtime(PostCleanup)`
MIR, it walks every reachable `mir::Const` (evaluating any surviving
`Const::Unevaluated` and `body.required_consts()` entry via
`tcx.const_eval_resolve(typing_env, uv, span)` and failing compilation if any
returns `Err(ErrorHandled::Reported(..))`) and transitively visits every
`AllocId` referenced in `ConstValue` or `Allocation::provenance()`:

| `GlobalAlloc` Variant | `rustc` Source Definition | Mutability & ELF/Mach-O/COFF Section | `.anneal-mir` Serialization & Lowering Contract |
| :--- | :--- | :--- | :--- |
| `GlobalAlloc::Memory(ConstAllocation)` | `interpret/mod.rs:266`, `consts.rs:40-157` | `Mutability::Not` -> `.rodata` (`constant`); `Mutability::Mut` -> `.data` (`global`) | Serialize `(size, align, mutability, bytes, init_mask_ranges, relocations: Vec<(offset, target_alloc_id, target_offset)>)`. Acyclic over `Memory -> Memory` edges; may point to `Static`, `Function`, `VTable`, or `TypeId`. |
| `GlobalAlloc::Static(DefId)` | `interpret/mod.rs:264,315-345`, `consts.rs:159-179` | `.rodata` iff `mutability == Not && ty.is_freeze()`; otherwise `.data` (or `.tdata`/`.tbss` if `#[thread_local]`) | Serialize `(def_id, symbol_name, is_thread_local, is_foreign, mutability, root_memory_alloc_id)`. **Breaking cycles:** Pre-register `AllocId -> Static(DefId)` in the symbol table before recursively serializing `tcx.eval_static_initializer(def_id)`. |
| `GlobalAlloc::Function { instance }` | `interpret/mod.rs:256`, `common.rs:185-187` | `.text` (`AddressSpace::INSTRUCTION`) | Serialize canonical monomorphic `Instance` key (`def_id`, `args`). Lowers to symbol address of compiled function. |
| `GlobalAlloc::VTable(Ty, PolyExistentialPredicates)` | `interpret/mod.rs:261`, `common.rs:217-226` | `.rodata` (`Mutability::Not`, `unnamed_addr constant`) | Resolve eagerly via `tcx.vtable_allocation((ty, principal))` to its underlying `GlobalAlloc::Memory` allocation plus structured vtable metadata `(size, align, drop_in_place, method_entries)`. |
| `GlobalAlloc::TypeId { ty }` | `interpret/mod.rs:269`, `intrinsics.rs:86-166`, `common.rs:201-205` | No runtime memory allocation (`base_addr = 0`) | Serialize `(canonical_ty, hash_u128 = tcx.type_id_hash(ty).as_u128())`. Verify pairwise hash distinctness across all `TypeId` allocations in the crate graph; lower at codegen to base address `0` (`offset = hash_fragment`). |

### 2. Uninitialized Padding (`InitMask`) and Cyclic `Static` Provenance Graphs in the 30-Case Census

Basis: source + execution

In `compiler/rustc_codegen_llvm/src/consts.rs:63-98`,
`append_chunks_of_init_and_uninit_bytes` inspects `alloc.init_mask().range_as_init_chunks(range)`.
Each `InitChunk::Init(r)` lowers to `cx.const_bytes(bytes)`, while each
`InitChunk::Uninit(r)` (such as the 3-byte and 2-byte alignment gaps in
`PaddedStruct`, `C13`–`C14`, or the uninitialized payload tail of
`NicheTaggedEnum::Small(7)`, `C15`) lowers to `cx.const_undef(cx.type_array(cx.type_i8(), len))`
(`undef` in LLVM IR), provided the total chunk count does not exceed
`uninit_const_chunk_threshold`.

Running [`support/run_globalalloc_and_ctfe_probe.py`](support/run_globalalloc_and_ctfe_probe.py)
across the 30-case suite (`C01`–`C30`,
[`support/globalalloc_census.json`](support/globalalloc_census.json)) confirms:
- **100% (`30 / 30`) agreement** between compile-time `CTFE` constants, native
  `rustc 1.99.1` runtime execution (`-Zmir-opt-level=0`), and Miri
  (`-Zmiri-tree-borrows`);
- **`116` read-only `.rodata` `constant` allocations** vs. **`1` writable `.data`
  `global` allocation** (`C04_INTERIOR_MUT_STATIC`, automatically placed in
  writable `.data` because `SyncCellU64` contains `UnsafeCell<u64>` and is
  `!Freeze`, whereas `C05_FROZEN_STATIC` is placed in `.rodata`);
- **`11` explicit `[N x i8] undef` padding chunks** preserved in LLVM IR across
  the padded struct and niche-enum constants (`C13`–`C16`);
- **Self-referential (`C01_SELF_CYCLE`) and mutually recursive (`C02_MUTUAL_A <->
  C03_MUTUAL_B`) statics** compile cleanly and satisfy `ptr::eq(C01_SELF_CYCLE.self_ptr,
  &C01_SELF_CYCLE)` and `ptr::eq(C02_MUTUAL_A.peer.peer, &C02_MUTUAL_A)` in both
  native execution and Miri.

### 3. Five Exact Divergence Axes Between `CTFE` and Runtime Execution (`CompileTimeMachine`)

Basis: source + execution + derived

Auditing `compiler/rustc_const_eval/src/const_eval/machine.rs` and
`compiler/rustc_const_eval/src/interpret/intrinsics.rs` identifies the exact five
operations where `CTFE` differs from runtime `Runtime(PostCleanup)` MIR:

| Divergence Axis | `CTFE` Behavior (`CompileTimeMachine`) | Runtime Behavior (`MiniSSA` / Native / Miri) | Refinement & Verification Contract |
| :--- | :--- | :--- | :--- |
| 1. `mir::RuntimeChecks` (`OverflowChecks`, `UbChecks`) | `machine.rs:863-870`: **Always returns `true`** (ignores `-Coverflow-checks=off` so `const` evaluation is crate-flag independent) | Controlled by session flag (`-Coverflow-checks`); checked `BinOp::AddWithOverflow` always traps on `Assert` | **Strict subset (`ctfePure_refines_runtime`):** Any `const fn` that succeeds in CTFE without overflow also succeeds at runtime under both `-Coverflow-checks=on` and `off`. |
| 2. Pointer-to-Integer Casts (`expose_provenance`) & Raw Pointer `<`/`==` (`binary_ptr_op`) | `machine.rs:872-879,943-949`: **Unsupported error** (`"exposing pointers is not possible at compile-time"`) | Valid at runtime (exposes concrete integer address) | **Strict subset:** CTFE rejects before producing a `ConstValue`, so no `ConstValue` ever depends on compile-time `ptrtoint`. |
| 3. `sym::ptr_guaranteed_cmp` (`<*const T>::guaranteed_eq`, `C26`–`C28`) | `machine.rs:279-388`: Returns `1` (definitely equal, e.g. both null or same `Static` + same offset), `0` (definitely unequal, e.g. null vs non-null or in-bounds of distinct `Static`s), or **`2` (unknown)** | Lowers at codegen to `0` or `1` (`(a == b) as u8`) | Standard library `guaranteed_eq` maps `2 -> None`, `1 -> Some(true)`, `0 -> Some(false)`. Whenever CTFE returns `0` or `1`, runtime pointer equality is guaranteed to evaluate to the identical boolean. |
| 4. Floating-Point NaN Payloads (`generate_nan`, `C30`) |Deterministic canonical quiet NaN (`0x7ff8_0000_0000_0000` for `f64`) | RFC 3514 non-deterministic choice from `{±canonical_qNaN, input_NaN_with_quiet_bit}` | **Refinement holds (`ctfePure_refines_runtime`):** CTFE's canonical quiet NaN is a member of the runtime RFC 3514 permitted set. |
| 5. `core::intrinsics::const_eval_select((args..), ctfe_fn, rt_fn)` (`C29`) | Calls `ctfe_fn(args..)` | Calls `rt_fn(args..)` | **Requires explicit equivalence obligation:** Because `const_eval_select` is `unsafe`, Anneal generates a verification obligation requiring `ctfe_fn` and `rt_fn` to satisfy the same functional postcondition `ens`. |

## Boundaries

1. **User `const_eval_select` With Intentionally Divergent Closures:**
   - **Known not to apply without a proof obligation:** If unsafe code invokes
     `core::intrinsics::const_eval_select((x,), ctfe_fn, rt_fn)` where `ctfe_fn`
     and `rt_fn` return different values (violating the standard library safety
     precondition of `const_eval_select`), CTFE and runtime execution will
     diverge. Anneal must treat `const_eval_select` as an unsafe intrinsic whose
     verification condition requires proving observational equivalence of
     `ctfe_fn` and `rt_fn` (or verifying both branches against the caller's
     specification).
2. **`GlobalAlloc::Memory` Deduplication and Pointer Equality (`ptr_guaranteed_cmp`
   Return `2`):**
   - **Known not to apply to `GlobalAlloc::Memory`:** Unlike `GlobalAlloc::Static`
     (which has a unique address per `DefId`), unnamed `GlobalAlloc::Memory`
     allocations (promoted temporaries and `const` references) may be merged or
     duplicated across codegen units (`unnamed_addr`). `CompileTimeMachine::guaranteed_cmp`
     therefore always returns `2` (`None`) when comparing pointers into
     `GlobalAlloc::Memory`, `GlobalAlloc::Function`, `GlobalAlloc::VTable`, or
     `GlobalAlloc::TypeId` (`machine.rs:370-385`).

## Evidence

1. **Lean `v4.34.1` Mechanization (`0` `sorryAx`, `0` `Lean.ofReduceBool`):**
   - File:
     [`support/CtfeRuntimeRefinementProbe.lean`](support/CtfeRuntimeRefinementProbe.lean)
   - Verified theorems: `read_writeTypeIdCtfe_roundtrip`,
     `forgedIntegerTypeId_rejected_in_ctfe`, `typeIdEq_ctfe_runtime_agreement`,
     and `ctfePure_refines_runtime`.
2. **30-Case CTFE vs. Runtime/Miri Differential Suite and `GlobalAlloc` Census:**
   - Script:
     [`support/run_globalalloc_and_ctfe_probe.py`](support/run_globalalloc_and_ctfe_probe.py)
   - Dataset:
     [`support/globalalloc_census.json`](support/globalalloc_census.json)
3. **`rustc 1.99.1` Source Coordinates (`58cf8f9c35b355199727627d07ae34a4e2846d67`):**
   - `compiler/rustc_middle/src/mir/interpret/mod.rs:174-350`
     (`AllocDecodingSession::decode_alloc_id`, `GlobalAlloc`, `mutability`)
   - `compiler/rustc_const_eval/src/interpret/intrinsics.rs:86-215`
     (`write_type_id`, `read_type_id`, `sym::type_id`, `sym::type_id_eq`)
   - `compiler/rustc_codegen_llvm/src/common.rs:178-262` (`alloc_to_backend`,
     `GlobalAlloc::TypeId -> Err(0)`)
   - `compiler/rustc_codegen_llvm/src/consts.rs:40-179` (`const_alloc_to_llvm`,
     `append_chunks_of_init_and_uninit_bytes`)
   - `compiler/rustc_const_eval/src/const_eval/machine.rs:279-388,863-1102`
     (`guaranteed_cmp`, `runtime_checks`, `binary_ptr_op`, `expose_provenance`,
     `before_access_global`, `before_alloc_access`)

## Revalidation

1. **Re-verify the Lean `v4.34.1` Mechanization:**
   ```bash
   anneal-lean-run --mode file --concurrency 4 -- \
     ~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
     reports/rustc-ctfe-globalalloc-promoted-constants-and-runtime-mir-equivalence/support/CtfeRuntimeRefinementProbe.lean
   ```
2. **Re-run the 30-Case CTFE Differential Suite and `GlobalAlloc` Census:**
   ```bash
   python3 reports/rustc-ctfe-globalalloc-promoted-constants-and-runtime-mir-equivalence/support/run_globalalloc_and_ctfe_probe.py
   ```
