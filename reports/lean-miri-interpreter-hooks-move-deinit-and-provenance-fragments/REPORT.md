# `lean-miri`, `rust-lang/miri`, and `rustc_const_eval` Interpreter Hooks, Move Deinitialization, Provenance Fragments, and Frame-Exit Protector Ordering

## Summary

In `proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`), `rust-lang/miri` (`7fa591d7d4dd9af8154becbc8332f8096f8323b1`), and `rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`), four operational invariants govern how a mechanized Rust verifier can soundly instantiate or refine the Miri interpreter:

1. **`Operand::Move` Deinitialization vs. `InitSubsumes` Refinement**: Neither `rustc_const_eval` (`InterpCx::eval_operand`) nor `lean-miri` (`Miri.Interpreter.evalOperand`, theorem `copy_move_same`) deinitializes the source place or performs a Tree Borrows write access when evaluating `Operand::Move(place)` inside `Rvalue::Use`, `Rvalue::BinaryOp`, `Rvalue::UnaryOp`, `Rvalue::Aggregate`, or `Rvalue::Cast`. Only `TerminatorKind::Call` and `TailCall` argument evaluation (`evalFnCallArgumentAt` / `passArgument`) distinguishes `Operand::Move(place)`, routing memory-backed or potentially overlapping moved arguments through `FnArg.inPlace` and `protectInPlaceFunctionArgument` (which retags the place as `.Mutable` with an `.FnEntry` protector and calls `writeUninit`). A stricter verification machine $M_{\text{strict}}$ that also deinitializes moved-from places on rvalue `Operand::Move` (`deinitOnMove = true`) forward-simulates the permissive machine $M_{\text{perm}}$ (`deinitOnMove = false`) under pointwise byte subsumption (`InitSubsumes`) across scalar reads (`.Initialized` and `.Union`), scalar writes, memory-to-memory copies, `Retag`, and `deallocate` **if and only if** move-deinitialization resets `initMask` and `provenance` (`deinitRange` / `Allocation.writeUninit`) **without** performing a Tree Borrows `.Write` access. Performing a Tree Borrows `.Write` access on move prematurely activates `ReservedFrz false → Unique` and breaks `BorrowTree` equivalence under a subsequent foreign read and child write.
2. **Sub-Pointer Byte Copies, `PointerFrag` Reassembly, and `offsetIsAddr`**: Because `u8` has `BackendRepr::Scalar(Scalar::Initialized { value: Int(I8, false), .. })` whereas `MaybeUninit<u8>` has `BackendRepr::Scalar(Scalar::Union { value: Int(I8, false) })`, `read_immediate_from_mplace_raw` (`MemoryOperand.readPlan`) takes the immediate scalar fast path (`Allocation.readScalar` with `readProvenance = false`) for `u8`—stripping pointer provenance under `offsetIsAddr = true`—but returns `.notImmediate` (`None`) for `MaybeUninit<u8>`, routing even a 1-byte `MaybeUninit<u8>` loop through memory-to-memory `Allocation.copyRepeatedly`. Each sub-pointer copy creates per-byte `PointerFrag { idx : UInt8, prov : Prov, bytes : Vector UInt8 8 }` entries in `ProvenanceMap.byteFragments`, where `bytes` snapshots the full 8-byte address of the original pointer rather than its storage offset in the allocation. Consequently, copying all 8 bytes of a pointer via `MaybeUninit<u8>` to a shifted (even unaligned) destination offset preserves provenance on reload, whereas chimeric splicing of bytes `0..4` of `p1` and bytes `4..8` of `p2` that share the **exact same `(allocId, tag)` at different offsets** (`p1.addr() != p2.addr()`) fails `frag1.bytes == frag2.bytes` in `inspectFragments` and strips provenance. Across the entire `lean-miri` codebase, exactly 10 functions in 9 files branch on `PointerProvenance.offsetIsAddr`.
3. **Five-Step `Return` and `UnwindResume` Ordering vs. Two-Stage Tree Borrows Protector Release**: Both `TerminatorKind::Return` (`unwinding = false`) and `TerminatorKind::UnwindResume` (`unwinding = true`) execute `returnFromCurrentFrame` in five ordered steps: (1) `returnOperand` (`_0`), (2) `popFrame` (`beforeStackPopWithEnsure`, which first runs `BorrowTree.releaseProtector` emitting `AccessCause.FnExit` for every `(allocId, tag)` in `frame.protectedTags` while all frame tags remain registered in `global.protectedTags`, and only then runs `global.endCall`), (3) `copyReturn` (executed only when `unwinding = false`), (4) `cleanupFrame` (`deallocateLocal` on every live `.indirect` local in `frame.locals`, invoking `BorrowTree.deallocateBorrowRange`, followed by `afterPop`), and (5) branching to the caller's `ret` or `unwind` block. Because Stage 2a runs on `UnwindResume` before `endCall`, unwinding out of a frame emits `FnExit(Write)` on every location accessed through a protected `Unique` tag (disabling sibling tags on those locations). Because Stage 2b (`endCall`) runs before Step 4 (`cleanupFrame`), a popping callee's own `FnEntry` protectors are unregistered before its stack locals are deallocated and never trigger `.ProtectedDealloc` during normal return or unwinding.
4. **Fail-Closed Verification Over `TerminationInfo`, `StepError`, Import Closures, and Open Interpreter Hooks**: In `lean-miri`, `Miri.Concurrency.TerminationInfo` has 13 constructors (only 3 satisfy `isUbReport = true`: `.stackedBorrowsUb`, `.treeBorrowsUb`, `.dataRace`) and `Miri.Interpreter.StepError` has 9 constructors (only `.undefinedBehavior`, `.retagWriteToReadOnly`, and `.termination info` with `info.isUbReport = true` satisfy `RunLoop.reportsUB = true`). Notably, reading or writing a `.dead` local produces `.error (.stack .localExpectedLive)` and executing `StorageDead(_0)` produces `.error (.stack .cannotMakeReturnPlaceDead)`, both of which have `RunLoop.reportsUB = false` and classify as `.blocked` rather than `.undefinedBehavior` in `Miri/OperationalSafety.lean` (unlike `rustc_const_eval`, which raises `UbInfo::LocalUseAfterFree`). Any sound verifier must therefore enforce `System.Safe` (`∀ outcome, ReachesOutcome sys start outcome → outcome.isReturn`) rather than `NoUndefinedBehavior`, and must instantiate all 8 open interpreter hook structures (112 distinct hook fields across `StepHooks`, `PlaceHooks`, `RvalueHooks`, `ScalarOpsHooks`, `CastHooks`, `ControlHooks`, `TerminatorHooks`, and `LocalStorageHooks`).

## Applicability

The findings in this report apply to the following concrete revisions and toolchains:

- **`proofs-rs/lean-miri`** at commit `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (whose `Miri/` directory has Git tree SHA-1 `ef473f04eed9bbfed474a7b5f6f91a2f6350c41b`, comprising `Miri.lean` and 607 `.lean` files under `Miri/`).
- **`rust-lang/miri`** at commit `7fa591d7d4dd9af8154becbc8332f8096f8323b1`, the upstream Miri revision mechanized by `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`.
- **`rust-lang/rust`** at commit `8144389c895da997dbdecaa635e41d6a50be6ffd`, the upstream `rustc` revision (`rustc_const_eval`, `rustc_middle`, `rustc_abi`) pinned by `rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1` and `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`.
- **`rust-lang/rust` / `miri` nightly toolchain** at commit `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly (3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1 2026-11-11)`, `miri 0.1.0 (3ef0c22cdb 2026-11-11)` on `x86_64-unknown-linux-gnu`), used to execute the preserved Tree Borrows (`MIRIFLAGS="-Zmiri-tree-borrows"`) and `#[custom_mir]` probes in [`support/miri_probe/src/lib.rs`](support/miri_probe/src/lib.rs). All code paths exercised by the probe (`eval_operand`, `eval_fn_call_argument`, `pass_argument`, `protect_in_place_function_argument`, `read_immediate_from_mplace_raw`, `ProvenanceMap`, `return_from_current_stack_frame`, `on_stack_pop`, and `release_protector`) match the source at `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` and `rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1`.
- **Lean 4** at commit `3b0f2862196c6a8af9eb0025ee650252694013dd` (`v4.28.0-rc1`) and commit `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), both of which kernel-check the standalone formalization in [`support/LeanMiriInitSubsumesAndFragProbe.lean`](support/LeanMiriInitSubsumesAndFragProbe.lean) with zero `sorryAx` and zero `Lean.ofReduceBool`.

Pointer-fragment (`PointerFrag`) creation and reassembly in `ProvenanceMap` (`Miri/Memory/ProvenanceMap.lean:185`, `provenance_map.rs:230`) requires a 64-bit target pointer size (`pointerSize == Size.ofBytes 8`); on 32-bit targets (`pointerSize != 8`), `ptrFragments` returns `#[]` and sub-pointer copies drop provenance immediately.

## Findings

### 1. `Operand::Move` Deinitialization Semantics and `InitSubsumes` Forward Simulation

#### 1.1 Operational Behavior of `Operand::Move` in Rvalues vs. Function Calls

`Basis: documentation + source + execution`

1. **Runtime MIR Documentation vs. `eval_operand` Implementation**:
   In `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`, the doc comment on `rustc_middle::mir::Operand::Move` (`compiler/rustc_middle/src/mir/syntax.rs:1731-1740`) states that in runtime MIR, `Move(Place)` marks the place as deinitialized (writes `uninit` to all bytes of the place). However, `InterpCx::eval_operand` (`compiler/rustc_const_eval/src/interpret/operand.rs:837-853`) takes an immutable `&self` receiver, contains an explicit `FIXME`, and evaluates `Operand::Copy(place)` and `Operand::Move(place)` identically:
   ```rust
   pub fn eval_operand(
       &self,
       mir_op: &mir::Operand<'tcx>,
       layout: Option<TyAndLayout<'tcx>>,
   ) -> InterpResult<'tcx, OpTy<'tcx, M::Provenance>> {
       use rustc_middle::mir::Operand::*;
       let op = match mir_op {
           // FIXME: do some more logic on move to invalidate the old location
           &Copy(place) | &Move(place) => self.eval_place_to_op(place, layout)?,
           Constant(constant) => self.eval_mir_constant(&constant.const_, constant.span, layout)?,
           RuntimeChecks(checks) => { ... }
       };
       interp_ok(op)
   }
   ```
   Because `eval_rvalue_into_place` (`compiler/rustc_const_eval/src/interpret/step.rs:179-213`) evaluates `Rvalue::Use(ref operand, with_retag)` by calling `let op = self.eval_operand(operand, Some(dest.layout))?; M::with_retag_mode(self, mode, |ecx| ecx.copy_op(&op, &dest))?;` without subsequently inspecting whether `operand` was `Operand::Move(place)`, **neither `rustc_const_eval` nor `rust-lang/miri` deinitializes the moved-from local or memory allocation—or performs a Tree Borrows write access—when `Operand::Move(place)` appears in `Rvalue::Use`, `Rvalue::BinaryOp`, `Rvalue::UnaryOp`, `Rvalue::Aggregate`, `Rvalue::Repeat`, `Rvalue::Cast`, or `Rvalue::WrapUnsafeBinder`**.

2. **Exact Transcription in `proofs-rs/lean-miri`**:
   In `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, `Miri.Interpreter.evalOperand` (`Miri/Interpreter/LocalAccess.lean:120-128`) and `OperandMachine.evalOperand` (`Miri/Interpreter/OperandMachine.lean:98-106`) match `.Copy place | .Move place => evalPlaceToOp place layout`, and `Miri/Interpreter/LocalAccess.lean:333-337` proves definitional equality:
   ```lean
   theorem copy_move_same
       (evalPlaceToOp : Place → Option Layout → Except LocalAccessError (OpTy Prov Layout))
       (evalConst : ConstOperand → Option Layout → Except LocalAccessError (OpTy Prov Layout))
       (evalRuntimeChecks : RuntimeChecksKind → Option Layout →
         Except LocalAccessError (OpTy Prov Layout))
       (place : Place) (layout : Option Layout) :
       evalOperand evalPlaceToOp evalConst evalRuntimeChecks (.Copy place) layout =
         evalOperand evalPlaceToOp evalConst evalRuntimeChecks (.Move place) layout := rfl
   ```
   `Miri/Interpreter/ExecutionMachine.lean:119-125, 164-235` wires `OperandMachine.evalOperand` directly into `RvalueHooks.evalOperand`.

3. **Where `Operand::Move` *Does* Deinitialize and Perform a Tree Borrows Write (`TerminatorKind::Call` and `TailCall`)**:
   The sole place in `rustc_const_eval`, `rust-lang/miri`, and `proofs-rs/lean-miri` that distinguishes `Operand::Move(place)` from `Operand::Copy(place)` is function-call argument passing (`compiler/rustc_const_eval/src/interpret/step.rs:369-480`, `call.rs:412-454`; `Miri/Interpreter/Call.lean:153-225`):
   - `moveDefinitelyDisjoint` (`Miri/Interpreter/Call.lean:153-162`, `step.rs:369-388`) returns `true` iff no `Operand::Move(place)` argument and no `returnPlace` contains a `.Deref` projection and all their base `LocalId`s are pairwise distinct.
   - `evalFnCallArgumentAt` (`Miri/Interpreter/Call.lean:169-203`, `step.rs:429-480`) evaluates `Operand::Copy` to `FnArg.copy op`, and evaluates `Operand::Move place` as follows:
     - When `moveDefinitelyDisjoint == true`: calls `evalPlaceToOp`. If the local is memory-backed (`.indirect mplace`), it returns `FnArg.inPlace mplace`. **If the local is an immediate register value (`.immediate imm`), it returns `FnArg.copy (.immediate imm)` and does not deinitialize the caller's immediate local.**
     - When `moveDefinitelyDisjoint == false` (for example, `Move(*p)` through a pointer dereference, or overlapping move arguments): calls `evalPlace` and `forceAllocation` to materialize an `MPlaceTy`, returning `FnArg.inPlace mplace`.
   - `passArgument` (`Miri/Interpreter/Call.lean:206-225`, `call.rs:412-454`) copies the argument into the callee's parameter place via `copyOpAllowTransmute` and then, for `FnArg.inPlace mplace`, invokes `hooks.protectInPlaceArgument choice mplace`.
   - `protectInPlaceFunctionArgument` (`Miri/Interpreter/MachineHooks.lean:365-387`, wired in `Miri/Interpreter/PlaceMachine.lean:305-311`, matching `EvalContextExt::protect_in_place_function_argument` in `rust-lang/miri/src/machine.rs:1857-1876`):
     1. When `size > 0`, retags `mplace` using `RetagPolicy.protectionPolicy` (`.Mutable` access + `.FnEntry` protector, which assigns `ReservedFrz false` even inside `UnsafeCell` and registers a `StrongProtector` in the callee frame); and
     2. Calls `hooks.writeUninit choice protectedPlace` (`write_uninit(&protected_place)`), which performs a **Tree Borrows `.Write` access through the newly created `FnEntry`-protected tag** (transitioning it to `Unique, accessed = true` and disabling foreign aliases) and clears `initMask` and `provenance` over the argument's byte range.
   - Confirmed by execution in [`support/miri_probe/src/lib.rs`](support/miri_probe/src/lib.rs): `test_rvalue_move_does_not_deinit_or_tb_write` executes custom MIR `y = Move(x)` after `p = &raw const x` and reads `*p == 42` without UB, whereas `test_ub_call_move_local_deinits_in_place_arg` passes `Move(x)` to `Call(RET = sink_non_copy(Move(x)), ...)` after `p = &raw const x` and triggers uninitialized-memory UB (`memory is uninitialized at [0x0..0x8]`) when `*p` is read after the call returns.

#### 1.2 `InitSubsumes` Refinement and Why `deinitOnMove` Must Omit Tree Borrows `.Write`

`Basis: source + derived + execution`

When a verification harness over `lean-miri` enforces strict move semantics (`deinitOnMove = true`, deinitializing moved-from places on rvalue `Operand::Move`) while upstream `lean-miri` / `rustc_const_eval` leaves moved-from rvalue places initialized (`deinitOnMove = false`), the relationship between the strict machine $M_{\text{strict}}$ and the permissive machine $M_{\text{perm}}$ is captured by the formal model in [`support/LeanMiriInitSubsumesAndFragProbe.lean`](support/LeanMiriInitSubsumesAndFragProbe.lean):

1. **Definitions of `AbsByte`, `ByteSubsumes`, `InitSubsumes`, and `StateSubsumes`**:
   ```lean
   structure ByteProvFrag where
     prov : Provenance
     origAddr : Nat
     byteIdx : Nat
     deriving DecidableEq, Repr, Inhabited

   inductive AbsByte where
     | uninit
     | init (val : UInt8) (frag : Option ByteProvFrag)
     deriving DecidableEq, Repr, Inhabited

   def ByteSubsumes (b_strict b_perm : AbsByte) : Prop :=
     b_strict = .uninit ∨ b_strict = b_perm

   inductive InitSubsumes : List AbsByte → List AbsByte → Prop where
     | nil : InitSubsumes [] []
     | cons {b_s b_p : AbsByte} {rest_s rest_p : List AbsByte} :
         ByteSubsumes b_s b_p → InitSubsumes rest_s rest_p →
         InitSubsumes (b_s :: rest_s) (b_p :: rest_p)

   structure MachineState where
     mem : List AbsByte
     tbTree : List (Provenance × TBPerm)
     nextTag : Nat

   def StateSubsumes (s_strict s_perm : MachineState) : Prop :=
     InitSubsumes s_strict.mem s_perm.mem ∧
     s_strict.tbTree = s_perm.tbTree ∧
     s_strict.nextTag = s_perm.nextTag
   ```

2. **Why `deinitOnMove = true` Must Deinitialize Without a Tree Borrows `.Write` Access (`tb_write_on_move_breaks_borrow_tree_equiv`)**:
   In `rustc_const_eval`, `StorageDead` (`make_local_dead` in `stack.rs:490-519`, `Miri/Interpreter/Stack.lean:269-286`) deallocates or clears a local without performing a reference write access, and `Allocation.writeUninit` (`Miri/Memory/Allocation.lean:596-604`) clears `initMask` and `provenance` without calling `beforeMemoryWrite`.
   If $M_{\text{strict}}$ (`deinitOnMove = true`) instead performed a Tree Borrows `.Write` access when moving from `*r` in `Rvalue::Use(Operand::Move(*r))` (where `r` has permission `ReservedFrz false` and `isProt = false`) while $M_{\text{perm}}$ (`deinitOnMove = false`) performed only the `.Read` access of `copyOp`:
   - $M_{\text{strict}}$ transitions `r` from `ReservedFrz false` to `Unique` (`Miri/TreeBorrows/Permissions.lean:87, 363-365`);
   - $M_{\text{perm}}$ keeps `r` at `ReservedFrz false` (`Permissions.lean:62-65`);
   - After a subsequent foreign `.Read` and a local `.Write` through `r`, $M_{\text{strict}}$ transitions `Unique → Frozen` (`Permissions.lean:78-80`) and **rejects** the local `.Write` (`none`), whereas $M_{\text{perm}}$ preserves `ReservedFrz false` across the foreign `.Read` (`Permissions.lean:72-74`) and **accepts** the local `.Write` (`some .Unique`).
   Conversely, if $M_{\text{strict}}$ deinitializes moved-from memory purely via `deinitRange` (`Allocation.writeUninit` / `LocalValue.uninit`) without invoking a Tree Borrows `.Write` transition, `s_strict.tbTree = s_perm.tbTree` holds identically (`moveDeinit_preserves_StateSubsumes`).

3. **Kernel-Checked Forward Simulation Across Memory and Tree Borrows Operations**:
   In [`support/LeanMiriInitSubsumesAndFragProbe.lean`](support/LeanMiriInitSubsumesAndFragProbe.lean), `InitSubsumes` and `StateSubsumes` are proved to be forward simulations across:
   - **Typed scalar reads (`readScalarInitializedAt_simulation`)**: `Allocation.readScalar` (`Miri/Memory/Allocation.lean:376-411`) first checks `checkInit range` (`decodeInitBytes`). If $M_{\text{strict}}$ succeeds (`= some v`), no byte in `slice_s` is `.uninit`; by `decodeInitBytes_eq_of_subsumes`, `slice_s = slice_p` byte-for-byte and fragment-for-fragment, so $M_{\text{perm}}$ succeeds and returns the exact same `ScalarVal` `v`.
   - **Union / `MaybeUninit` reads (`readScalarUnionAt_simulation`, `readScalarAt_simulation`)**: Returns raw byte slices of equal length related by `InitSubsumes`.
   - **Scalar writes (`writeScalarAt_simulation`)**: Overwrites the target range with identical `.init` bytes in both machines, preserving `InitSubsumes` on the surrounding prefix and suffix (`spliceAt_subsumes`). Even if `writeScalar` in $M_{\text{perm}}$ partially overwrites an 8-byte pointer whose remaining bytes were already deinitialized to `.uninit` in $M_{\text{strict}}$—causing `ProvenanceMap.clear` (`Miri/Memory/ProvenanceMap.lean:241-265`) in $M_{\text{perm}}$ to demote those remaining bytes to `PointerFrag` entries—`.uninit` in $M_{\text{strict}}$ subsumes every `AbsByte` in $M_{\text{perm}}$, so `InitSubsumes` is preserved.
   - **Memory-to-memory copies (`copyBytes_simulation`)**: `Allocation.copyRepeatedly` (`Miri/Memory/Allocation.lean:629-692`) splices an `InitSubsumes`-related source slice into an `InitSubsumes`-related destination allocation, preserving `InitSubsumes`.
   - **Retagging (`retagPlace_simulation`)**: `FreezeVisitor.visitFreezeSensitive` (`Miri/TreeBorrows/FreezeVisitor.lean:74-135`) inspects only static and dynamic type layouts (`isUnsafeCell`, `typeIsFreeze`, `FieldsShape`, `Variants`) and never inspects pointee `initMask` or `rawBytes`. `RetagPipeline.retagPointerValue` (`Miri/TreeBorrows/RetagPipeline.lean:199-300`) reads only the 8-byte pointer scalar being retagged (which is identical in both machines by `readScalarInitializedAt_simulation`), updates `BorrowTree` identically, and writes the retagged pointer scalar back.
   - **Deallocation (`deallocateAlloc_simulation`)**: `BorrowTree.deallocateBorrowRange` (`Miri/TreeBorrows/TreeState.lean:1076-1156`) checks only `protectedTags` and `tree` permissions (`protectedTags.get node.tag == some .StrongProtector && !permission.permission.isCell && permission.accessed`), never `Allocation.initMask`.

---

### 2. Sub-Pointer Byte Copies, `PointerFrag` Reassembly, and `offsetIsAddr` Mode Switching

#### 2.1 `u8` (`Scalar::Initialized`) vs. `MaybeUninit<u8>` (`Scalar::Union`) in `readPlan` and `copy_op`

`Basis: source + execution + derived`

1. **ABI Representation Distinction (`Miri/ABI/Layout.lean:62-78`)**:
   - `u8` has `BackendRepr.Scalar (.Initialized (.Int .I8 false) (0..=255))`.
   - `MaybeUninit<u8>` is a `#[repr(transparent)] union` with `BackendRepr.Scalar (.Union (.Int .I8 false))`.
   - `[u8; 8]` and `[MaybeUninit<u8>; 8]` have `BackendRepr.Memory (sized := true)`.

2. **Immediate Fast Path vs. Memory-Copy Fallback (`operand.rs:591-632`, `Miri/Interpreter/MemoryOperand.lean:173-190`)**:
   In `rustc_const_eval` (`InterpCx::read_immediate_from_mplace_raw`) and `lean-miri` (`MemoryOperand.readPlan`), only `BackendRepr.Scalar (.Initialized value _)` and `BackendRepr.ScalarPair (.Initialized a _) (.Initialized b _)` take the immediate scalar load path:
   ```lean
   match mplace.layout.layout.backendRepr with
   | .Scalar (.Initialized value _) =>
       let size := value.size ptrSize
       .ok (.scalar (allocRange offset size) value.isPointer)
   | .ScalarPair (.Initialized a _) (.Initialized b _) => ...
   | _ => .ok .notImmediate
   ```
   Consequently, during `copy_op` (`compiler/rustc_const_eval/src/interpret/place.rs:970-1052`, `Miri/Interpreter/Place.lean:347-376`):
   - **Copying a pointer byte-by-byte via `u8` (`test_ub_u8_copy_strips_provenance`, `u8_copy_strips_prov`)**: Each 1-byte load of `u8` matches `.Scalar (.Initialized (.Int .I8 false) _)` with `value.isPointer == false`, calling `Allocation.readScalar range (readProvenance := false)` (`Miri/Memory/Allocation.lean:376-411`). Under `offsetIsAddr = true`, `readScalar` checks `isRangeInitialized` and returns `Scalar.fromUInt bits 1` without provenance. Writing the 8 `u8` values into destination memory produces 8 initialized integer bytes with empty `ProvenanceMap`; dereferencing the transmuted pointer fails with dangling-pointer (no-provenance) UB (`0x...[noalloc]`).
   - **Copying a pointer byte-by-byte via `MaybeUninit<u8>` (`test_pointer_copy_maybe_uninit_vs_u8`, `byte_by_byte_maybe_uninit_copy_preserves_prov`)**: Because `MaybeUninit<u8>` has `.Scalar (.Union (.Int .I8 false))`, `readPlan` returns `.notImmediate` (`read_immediate_from_mplace_raw` returns `None`). For any memory-backed `MaybeUninit<u8>` (such as `arr[i]` in `[MaybeUninit<u8>; 8]`), `copy_op_no_validate` (`place.rs:1023-1048`) takes the 1-byte memory-to-memory `Allocation.copyRepeatedly` path, preserving `initMask` and copying 1-byte `PointerFrag` entries in `ProvenanceMap.byteFragments`.

#### 2.2 `PointerFrag` Snapshot Semantics, Shifted Reassembly, and Chimeric Splice Rejection

`Basis: source + execution + derived`

In `Miri/Memory/ProvenanceMap.lean:15-316` (transcribing `compiler/rustc_middle/src/mir/interpret/allocation/provenance_map.rs:15-450`):

1. **Fragment Creation (`ptrFragments` and `prepareCopy`, `Miri/Memory/ProvenanceMap.lean:183-198, 267-316`)**:
   ```lean
   structure PointerFrag (Prov : Type) where
     idx : UInt8
     prov : Prov
     bytes : Vector UInt8 8
     deriving DecidableEq, Repr
   ```
   When a sub-pointer copy (`Allocation.copyRepeatedly` of `< 8` bytes) or a partial overwrite/deinit (`ProvenanceMap.clear`, lines 241–265) splits a whole pointer `(pos, prov)` in `ProvenanceMap.ptrs`, `ptrFragments` reads the 8 raw bytes of the pointer at `[pos .. pos + 8)` into `bytes : Vector UInt8 8` and emits `(pos + i, { idx := UInt8.ofNat i, prov, bytes })` for each byte `i ∈ 0..7`.

2. **Fragment Reassembly (`inspectFragments` and `Allocation.readPtrAt`, `Miri/Memory/ProvenanceMap.lean:117-149`, `Miri/Memory/Allocation.lean:314-346`)**:
   When an 8-byte pointer is read at `offset`, if `self.getPtr offset` is `none` and no unaligned whole pointer overlaps `[offset .. offset + 8)`, `readPtr` invokes `inspectFragments offset pointerSize`:
   - For each `idx ∈ 0..7`, looks up `frag := self.getByte (offset + idx) pointerSize` (returning `none` if any byte has no fragment).
   - Verifies `frag.idx.toNat == idx` and that all 8 non-wildcard fragments have identical `(frag.prov, frag.bytes)`.
   - In `Allocation.readPtrAt` (`Allocation.lean:328-345`), if `readPtr` recovered `some prov` from `byteFragments`, `readPtrAt` additionally checks that the 8 current raw bytes in `self.rawBytes[offset .. offset + 8)` equal `(self.provenance.getByte offset pointerSize).get!.bytes`.

3. **Shifting vs. Chimeric Splicing**:
   - **Shifting a pointer's bytes to an arbitrary (even unaligned) offset (`byte_by_byte_maybe_uninit_copy_preserves_prov`, `test_pointer_copy_maybe_uninit_vs_u8` Case C)**: Because `PointerFrag` stores the relative byte index `idx ∈ 0..7` and the 8-byte value snapshot `bytes`—not the source allocation offset `pos`—copying all 8 bytes of a pointer via `MaybeUninit<u8>` to offset `+3` in a destination buffer and loading via `read_unaligned()` satisfies `frag.idx == idx` and `(frag.prov, frag.bytes) == expected` for all 8 bytes, preserving `prov`.
   - **Chimeric splicing of two pointers `p1, p2` sharing `(allocId, tag)` at different offsets (`chimeric_splice_strips_prov`, `chimeric_splice_general_strips_prov`, `test_ub_chimeric_splice_same_tag_diff_offset_strips_prov`)**: Suppose `p1 = base` and `p2 = base.wrapping_add(1)` point into the same allocation with the **exact same provenance `(allocId, tag)`**. Even though the upper 4 address bytes (`idx = 4..7`) of `p1` and `p2` are numerically identical, `ptrFragments` snapshotted all 8 bytes of `p1` into `frag1.bytes` and all 8 bytes of `p2` into `frag2.bytes`. Because `frag1.bytes[0] != frag2.bytes[0]`, `frag1.bytes != frag2.bytes`; at `idx = 4`, `inspectFragments` sees `(frag.prov, frag.bytes) != current` and returns `none`, stripping provenance.
   - **Splicing two copies of the identical pointer value (`test_chimeric_splice_same_tag_same_vs_diff_offset` Splice 1)**: If `p1` and `p1_clone` have both the same `prov` and the same 8-byte address `bytes`, splicing bytes `0..4` from `p1` and bytes `4..8` from `p1_clone` satisfies `(frag.prov, frag.bytes) == current` across all 8 bytes and preserves provenance.

#### 2.3 Exhaustive Catalog of Functions Branching on `PointerProvenance.offsetIsAddr`

`Basis: source`

`PointerProvenance.offsetIsAddr` (`Miri/Memory/Identity.lean:87-100`) is `true` for runtime Miri provenance (`Provenance`, where `Pointer.offset` is an absolute virtual address) and `false` for relative CTFE provenance (`AllocId` at `Identity.lean:97-100` and `CtfeProvenance` at `Miri/Memory/CtfeProvenance.lean:118-121`). Across all 608 `.lean` files in `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, exactly **10 functions in 9 files** branch on `PointerProvenance.offsetIsAddr`:

| # | Function | File and Line Range | Behavior when `offsetIsAddr = true` (Runtime Miri) | Behavior when `offsetIsAddr = false` (Pure CTFE) |
| :--- | :--- | :--- | :--- | :--- |
| 1 | `Miri.Memory.Pointer.addr` | `Miri/Memory/Pointer.lean:98-100` | Returns `.ok self.offset` (absolute address) | Returns `.error .relativeProvenanceHasNoAbsoluteAddress` |
| 2 | `Miri.Memory.Scalar.tryToScalarInt` | `Miri/Memory/Scalar.lean:118-132` | Converts `.pointer pointer` to `.integer (ScalarInt.fromUInt pointer.offset.bytes self.scalarSize)`, stripping provenance so pointer-to-int operations succeed | Returns `.erasedPointer ⟨pointer.offset, id⟩ self.scalarSize`, causing `Scalar.toScalarInt` / `toBits` / `clearProvenance` to fail with `.readPointerAsInt` |
| 3 | `Miri.Memory.ProvenanceMap.readPtr` | `Miri/Memory/ProvenanceMap.lean:138-149` | When partial or chimeric pointer fragments fail to reassemble (`prov.isNone`), returns `.ok none` (stripping provenance and reading integer address bytes) | When `prov.isNone` and the range contains provenance/fragments, returns `.error (.readPartialPointer offset)` |
| 4 | `Miri.Memory.Allocation.getBytesStripProvenance` | `Miri/Memory/Allocation.lean:349-370` | Checks `checkInit` and returns `rawSlice range`, ignoring any provenance in `range` | If `!self.provenance.rangeEmpty range pointerSize`, returns `.error (.readPointerAsInt none)` |
| 5 | `Miri.Memory.Allocation.readScalar` | `Miri/Memory/Allocation.lean:376-411` | When `readProvenance = false`, ignores provenance and returns `Scalar.fromUInt bits range.size` | When `readProvenance = false` and `!self.provenance.rangeEmpty range pointerSize`, returns `.error (.readPointerAsInt none)` |
| 6 | `Miri.Memory.isPtrMisaligned` | `Miri/Memory/Access.lean:196-221` | Checks `offsetMisalignment ptr.offset required` directly on the absolute address `ptr.offset` | Checks `resolved.allocationAlignBytes < requiredBytes` and `offsetMisalignment resolved.offset required` |
| 7 | `Miri.Memory.Validity.checkSafePointer` | `Miri/Memory/Validity.lean:1096-1098` | On a null pointer with `nullable = true`, sets `maybe := false` in `.nullSafePointer kind false` | On a pointer with `offset = 0` and `nullable = true`, sets `maybe := target.pointer.isPointer` in `.nullSafePointer kind maybe` (rejecting relative offset-0 pointers as "maybe null") |
| 8 | `Miri.Memory.Validity.visitPrimitive` | `Miri/Memory/Validity.lean:1339-1341` | On `.functionPointer` with `nullable = true`, sets `maybe := false` in `.nullFunctionPointer false` | Sets `maybe := scalar.isPointer` in `.nullFunctionPointer maybe` |
| 9 | `Miri.Interpreter.ExecutionScalar.pointerBinary` & `Miri.Interpreter.IntrinsicAtomic.pointerBinary` | `Miri/Interpreter/ExecutionScalar.lean:85-97`, `Miri/Interpreter/IntrinsicAtomic.lean:260-271` | Executes atomic pointer `.Add`, `.Sub`, `.BitOr`, `.BitAnd`, `.BitXor` on the address bits while preserving left-hand provenance | Returns `.error (.unsupported "Miri atomic pointer arithmetic requires address provenance")` |
| 10 | `Miri.Interpreter.Intrinsics.pointerOffsetFrom` | `Miri/Interpreter/Intrinsics.lean:217-233` | Uses `a.offset.bytes` and `b.offset.bytes` directly as absolute addresses before checking inbounds and same-allocation requirements | Resolves `tryAllocId` on both pointers upfront and requires `aId == bId` (returning `.pointerOffsetFromDifferentAllocations` if different) |

---

### 3. `Return` and `UnwindResume` Frame-Exit Ordering vs. Two-Stage Tree Borrows Protector Release

#### 3.1 Five-Step Frame-Exit Pipeline in `returnFromCurrentFrame`

`Basis: source + execution`

In `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` (`compiler/rustc_const_eval/src/interpret/call.rs:1134-1210`, `stack.rs:447-488`), `rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1` (`src/machine.rs:1971-2020`, `src/borrow_tracker/mod.rs:359-398`, `src/borrow_tracker/tree_borrows/mod.rs:92-105`), and `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (`Miri/Interpreter/Step.lean:105-110`, `Miri/Interpreter/ControlFlow.lean:64-113`, `Miri/Interpreter/Stack.lean:385-425`, `Miri/Interpreter/MachineHooks.lean:392-429`), both `TerminatorKind::Return` (`unwinding = false`) and `TerminatorKind::UnwindResume` (`unwinding = true`) execute `returnFromCurrentFrame`:

```lean
def returnFromCurrentFrame
    (hooks : ControlHooks P L E M C Op) (choice : C) (unwinding : Bool)
    (state : StepState P L E M) : StepResult (StepState P L E M) Unit :=
  match hooks.returnOperand choice state with
  | (state, .error err) => (state, .error err)
  | (state, .ok returnOp) =>
      match hooks.popFrame choice state with
      | (state, .error err) => (state, .error err)
      | (state, .ok popping) =>
          let afterCopy :=
            if !unwinding then
              hooks.copyReturn choice returnOp popping.returnPlace state
            else
              (state, .ok ())
          match afterCopy with
          | (state, .error err) => (state, .error err)
          | (state, .ok ()) =>
              match hooks.cleanupFrame choice unwinding popping state with
              | (state, .error err) => (state, .error err)
              | (state, .ok action) => ...
```

The five steps execute in the following strict order:

1. **Step 1 (`returnOperand` / `local_to_op(RETURN_PLACE)`, before popping)**:
   Evaluates `_0` of the current frame to an `OpTy` (`Operand.immediate` or `Operand.indirect`). This runs even when `unwinding == true` (`call.rs:1142-1145`), because `local_to_op` on an `.uninit` or `.indirect` `_0` does not read memory bytes (`Miri/Interpreter/Stack.lean:180-198`); only `.dead` fails with `.localExpectedLive`, and `StorageDead(_0)` is forbidden (`Stack.lean:273`).
2. **Step 2 (`popFrame` / `pop_stack_frame_raw`: Two-Stage Tree Borrows Protector Release + Frame Removal)**:
   While the callee frame is still at the top of `stack.frames`, `popStackFrameRaw` (`Miri/Interpreter/Stack.lean:385-396`, `stack.rs:447-461`) calls `beforePop` (`beforeStackPopWithEnsure` at `Miri/Interpreter/MachineHooks.lean:392-429`, `on_stack_pop` at `borrow_tracker/mod.rs:359-398`). `beforeStackPopWithEnsure` does not take `unwinding : Bool` and executes identically on `Return` and `UnwindResume` in two sub-stages:
   - **Stage 2a (Per-Tag Implicit `FnExit` Access + Exposure Propagation while All Frame Tags Remain Protected)**:
     Iterates in insertion order over `(allocId, tag)` in `frame.extra.borrowTracker.protectedTags`. If `getAllocInfo(allocId).kind == .liveData`, calls `BorrowTree.releaseProtector tag currentTracker.global.protectedTags` (`Miri/TreeBorrows/TreeState.lean:1036-1069`, `tree_borrows/tree.rs:671-738`):
     - For every location segment in `tree.locations` where `tag` has an entry with `state.accessed == true` and `state.permission.associatedAccess == some kind` (`Write` for `Unique`; `Read` for `ReservedFrz`, `ReservedIM`, and `Frozen`; `none` for `Cell` and `Disabled`, per `Miri/TreeBorrows/Permissions.lean:268-271`), performs a synthetic tree access `performTreeAccessAt segment.data (some source) kind protectedTags .SkipChildrenOfAccessed` (`AccessCause::FnExit(kind)`) **while all tags in `frame.protectedTags` remain registered in `global.protectedTags`**.
     - Calls `updateExposureForProtectorRelease tag` (`TreeState.lean:1012-1033`).
   - **Stage 2b (Global Protector Unregistration)**:
     Only after Stage 2a completes for all `(allocId, tag)` in `frame.protectedTags`, calls `tracker.global.endCall borrowFrame` (`MachineHooks.lean:420`, `borrow_tracker/mod.rs:394`), removing the popping frame's tags from `global.protectedTags`.
   - Removes `frame` from `stack.frames`.
3. **Step 3 (`copyReturn` / `copy_op_allow_transmute(&return_op, frame.return_place)`, skipped when `unwinding == true`)**:
   - When `unwinding == false`: copies `returnOp` into the caller's `returnPlace`. Because Step 2 already released the callee's protectors (including any `FnEntry` protector placed on `returnPlace` by `protectInPlaceFunctionArgument` at call entry, `Miri/Interpreter/Call.lean:241`), writing the return value into `returnPlace` does not conflict with the callee's own protector on `returnPlace`.
   - When `unwinding == true`: skipped (`ControlFlow.lean:77`, `call.rs:1165`).
4. **Step 4 (`cleanupFrame` / `cleanup_stack_frame`: Deallocating `frame.locals` + `after_stack_pop`)**:
   `cleanupStackFrame` (`Miri/Interpreter/Stack.lean:398-425`, `stack.rs:464-488`) iterates over every `slot` in `frame.locals` and calls `deallocateLocal slot.value`, deallocating every live `.indirect` stack allocation owned by the popped frame (invoking `BorrowTree.deallocateBorrowRange` at `Miri/TreeBorrows/TreeState.lean:1076-1156`), then calls `deallocateVarargs` and `afterPop` (`M::after_stack_pop(self, frame, unwinding)`).
5. **Step 5 (`returnToBlock` vs. `unwindToBlock`)**:
   Branches to `frame.returnContinuation.ret` (`unwinding == false`) or `frame.returnContinuation.unwind` (`unwinding == true`).

#### 3.2 Interaction Between Frame-Exit Ordering and `StrongProtector`

`Basis: source + execution`

1. **`UnwindResume` Still Emits `FnExit` Protector-End Accesses (`test_unwind_with_valid_fn_entry_protector` and `test_ub_unwind_protector_end_access_disables_sibling`)**:
   As noted in `rust-lang/miri/src/borrow_tracker/tree_borrows/diagnostics.rs:29-33`, the synthetic `FnExit` access itself never faults directly (`unreachable!("protector accesses can never be the source of UB")`), because any foreign access that would conflict with an active protector already faults immediately when that foreign access occurs. However, on both `Return` and `UnwindResume`, Step 2a's `FnExit(Write)` access on every location where an `FnEntry`-protected tag reached `Unique, accessed = true` transitions sibling tags at those locations to `Disabled`. In `test_ub_unwind_protector_end_access_disables_sibling`, a callee receives `x: &mut u64` protecting bytes `[8..16)` of a `(u64, u64)` pair, writes `*x = 555` (`Unique, accessed = true` at `[8..16)`), reborrows a sibling `z_ref = &mut (*root_ptr).0` at `[0..8)` (which accesses only `[0..8)` and initializes `z_ref` with lazy outside permission `ReservedFrz false, accessed = false` at `[8..16)`), and panics. During `UnwindResume`, Step 2a emits `FnExit(Write)` on `x` at `[8..16)`, leaving `z_ref` valid at `[0..8)` (`test_unwind_with_valid_fn_entry_protector`) while transitioning `z_ref` at `[8..16)` to `Disabled`.
2. **Deallocating a Protected Allocation Before vs. During Frame Exit (`test_ub_dealloc_local_with_active_strong_protector`)**:
   - **Before frame exit (`StorageDead` or `dealloc` while the protecting frame is still active)**: `BorrowTree.deallocateBorrowRange` (`Miri/TreeBorrows/TreeState.lean:1106-1108`) checks `if protectedTags.get node.tag == some .StrongProtector && !permission.permission.isCell && permission.accessed then return .Error tree (.ProtectedDealloc)`. Deallocating an allocation while an active frame holds an accessed non-`Cell` `StrongProtector` on it immediately faults with `.ProtectedDealloc` UB (`test_ub_dealloc_local_with_active_strong_protector`).
   - **During frame exit (Step 4 `cleanupStackFrame`)**: Because Step 2b (`global.endCall`) removes all `frame.protectedTags` of the popping frame from `global.protectedTags` **before** Step 4 (`cleanupStackFrame`) deallocates the popping frame's live `.indirect` locals (`deallocateLocal` → `deallocateBorrowRange`), a callee's own `FnEntry` protectors are already unregistered by Step 4 and never trigger `.ProtectedDealloc` on its own stack allocations.

---

### 4. Exhaustive Classification of `TerminationInfo`, `StepError`, Import Closures, Open Hooks, and Value-Validity Retagging

#### 4.1 Exhaustive Classification of `TerminationInfo` (`Miri/Concurrency/Termination.lean:19-66`)

`Basis: source`

`Miri.Concurrency.TerminationInfo` has **13 constructors**, classified by `TerminationInfo.report : TerminationInfo → TerminationReport` (lines 45–58) and `TerminationInfo.isUbReport : TerminationInfo → Bool` (`self.report == .undefinedBehavior`, lines 64–65):

| # | `TerminationInfo` Constructor | `TerminationInfo.report` | `isUbReport` | Meaning and Fail-Closed Verifier Treatment |
| :--- | :--- | :--- | :--- | :--- |
| 1 | `.stackedBorrowsUb (message : String)` | `.undefinedBehavior` | **`true`** | Stacked Borrows aliasing UB → **Reject (UB)** |
| 2 | `.treeBorrowsUb (title : String)` | `.undefinedBehavior` | **`true`** | Tree Borrows aliasing or protector UB → **Reject (UB)** |
| 3 | `.dataRace (involvesNonAtomic : Bool)` | `.undefinedBehavior` | **`true`** | Concurrency data race UB → **Reject (UB)** |
| 4 | `.exit (exitCode : Int) (leakCheck : Bool)` | `.regularExit exitCode leakCheck` | `false` | Whole-program exit (`0` on normal root termination; non-zero on `std::process::exit(code)`) → **Accept only on root frame normal return; reject premature exit unless specified** |
| 5 | `.abort (message : String)` | `.abnormalTermination` | `false` | Explicit abort (`intrinsics::abort`, panic-in-drop abort, `UnwindTerminate`) → **Reject under `System.Safe` / postcondition verification** |
| 6 | `.interrupted` | `.interrupted` | `false` | Host interrupt signal / timeout → **Reject (Blocked / Incomplete)** |
| 7 | `.unsupportedInIsolation (message : String)` | `.unsupportedOperation` | `false` | Host OS operation blocked by isolation → **Reject Fail-Closed (Unsupported)** |
| 8 | `.int2PtrWithStrictProvenance` | `.unsupportedOperation` | `false` | Integer-to-pointer cast under `-Zmiri-strict-provenance` → **Reject Fail-Closed (Unsupported)** |
| 9 | `.unsupportedForeignItem (item : String)` | `.unsupportedOperation` | `false` | Call to unmodeled extern / FFI symbol → **Reject Fail-Closed (Unsupported)** |
| 10 | `.globalDeadlock` | `.globalDeadlock` | `false` | All threads blocked on locks/condvars/joins → **Reject under `System.Safe` (Deadlock)** |
| 11 | `.localDeadlock` | `.localDeadlock` | `false` | Single-thread self-deadlock → **Reject under `System.Safe` (Deadlock)** |
| 12 | `.multipleSymbolDefinitions (linkName : String)` | `.otherMachineStop` | `false` | Linker symbol collision → **Reject Fail-Closed (Blocked / Invalid Program)** |
| 13 | `.symbolShimClashing (linkName : String)` | `.otherMachineStop` | `false` | User symbol clashes with Miri shim → **Reject Fail-Closed (Blocked / Invalid Program)** |

#### 4.2 Exhaustive Classification of `StepError` (`Miri/Interpreter/Step.lean:9-21`) and `RunLoop.reportsUB` (`Miri/Interpreter/RunLoop.lean:87-91`)

`Basis: source + derived`

`Miri.Interpreter.StepError` has **9 constructors**, and `RunLoop.reportsUB : StepError → Bool` (`Miri/Interpreter/RunLoop.lean:87-91`) returns `true` for only 2.5 of them:

```lean
def reportsUB : StepError → Bool
  | .undefinedBehavior _ => true
  | .retagWriteToReadOnly => true
  | .termination info => info.isUbReport
  | _ => false
```

| # | `StepError` Constructor | `RunLoop.reportsUB` | `OperationalSafety.classifyError` | Where Emitted and Fail-Closed Verifier Requirement |
| :--- | :--- | :--- | :--- | :--- |
| 1 | `.undefinedBehavior (reason : String)` | **`true`** | `.undefinedBehavior` | Arithmetic UB (`Div`/`Rem` by zero, `INT_MIN / -1`, `Unchecked` overflow, OOB shifts), memory UB (`invalidUninitBytes`, OOB/misaligned/dangling pointer access, overlapping `copy_nonoverlapping`, invalid scalar/enum/bool/ref validity, `Unreachable` terminator) → **Reject (UB)** |
| 2 | `.retagWriteToReadOnly` | **`true`** | `.undefinedBehavior` | `Miri/TreeBorrows/RetagPipeline.lean:211` / `Miri/Interpreter/TypedRetag.lean`: mutable `Unique` retag of read-only allocation → **Reject (UB)** |
| 3 | `.termination (info : TerminationInfo)` | `info.isUbReport` (`true` for 3; `false` for 10) | `.undefinedBehavior` (3), `.unsupported` (2), `.blocked` (8) | Tree Borrows UB (`.termination (.treeBorrowsUb ...)`), Stacked Borrows UB, data races, `abort`, deadlocks, unsupported FFI, `int2PtrWithStrictProvenance`, `exit` → **Reject all non-return outcomes fail-closed** |
| 4 | `.unsupported (feature : String)` | `false` | `.unsupported` | Unimplemented or unsupported MIR features, intrinsics, target shims, or layout queries → **Reject Fail-Closed (Unsupported)** |
| 5 | `.invalidProgram (reason : String)` | `false` | `.blocked` | Malformed MIR, missing basic block / local / layout / ABI mismatch, `CopyForDeref in runtime MIR` → **Reject Fail-Closed (Blocked)** |
| 6 | `.resourceExhaustion (reason : String)` | `false` | `.blocked` | Stack overflow (`Stack.pushFrame` exceeding `maxStackDepth`), fuel exhaustion, OOM → **Reject Fail-Closed (Blocked)** |
| 7 | `.machineStop (reason : String)` | `false` | `.blocked` | Non-UB machine halt (`TerminationMachine`) → **Reject Fail-Closed (Blocked)** |
| 8 | `.stack (error : StackError)` | `false` | `.blocked` | **Critical divergence from `rustc_const_eval`**: `StackError` (`Miri/Interpreter/Stack.lean:31-38`) has 4 constructors: `.emptyStack`, `.invalidLocal`, `.localExpectedLive`, `.cannotMakeReturnPlaceDead`. In `rustc_const_eval` (`stack.rs:284`), reading or writing `LocalValue::Dead` raises `InterpErrorKind::UndefinedBehavior(UbInfo::LocalUseAfterFree)`. In `lean-miri`, reading a `.dead` local (`LocalAccess.lean:28`, `OperandMachine.lean:33`) or writing to a `.dead` local (`Stack.lean:154`) returns **`.error (.stack .localExpectedLive)`**, and `StorageDead(_0)` (`Stack.lean:273`) returns **`.error (.stack .cannotMakeReturnPlaceDead)`**—both of which have `reportsUB = false` and classify as `.blocked`! A verifier that checked only `NoUndefinedBehavior` (`¬ ReachesOutcome sys start (.undefinedBehavior _)`) instead of `System.Safe` (`∀ outcome, ReachesOutcome sys start outcome → outcome.isReturn`, `Miri/OperationalSafety.lean:83-85`) would **unsoundly accept dead-local use-after-free and `StorageDead(_0)`** |
| 9 | `.callback (reason : String)` | `false` | `.blocked` | Unresolved stack-empty or frame callback error → **Reject Fail-Closed (Blocked)** |

#### 4.3 Module Import Closures in `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`

`Basis: source`

1. **Full Repository (`608` `.lean` files)**:
   The repository contains `Miri.lean` plus `607` `.lean` files under `Miri/` (`Miri/Interpreter/`: 307 + `Miri/Interpreter.lean`; `Miri/Input/`: 216 + `Miri/Input.lean`; `Miri/Concurrency/`: 25 + `Miri/Concurrency.lean`; `Miri/Memory/`: 22 + `Miri/Memory.lean`; `Miri/TreeBorrows/`: 15 + `Miri/TreeBorrows.lean`; `Miri/ABI/`: 9 + `Miri/ABI.lean`; `Miri/DataStructures/`: 2 + `Miri/DataStructures.lean`; `Miri/MIR/`: 2; `Miri/Frontend/`: 1; `Miri/OperationalSafety.lean`: 1). `Miri.lean` transitively imports `605` files (leaving `Miri/Frontend/ImportMIR.lean`, `Miri/Input/ExecutionChoicePolicy.lean`, and `Miri/Interpreter/TlsCallbacks.lean` unimported by `Miri.lean`).
2. **67-File Pure Core Closure**:
   - The first 21 imports of `Miri/Interpreter.lean` (lines 1–21: `IntegerOps`, `Immediate`, `Operand`, `PointerOffset`, `IntegerCast`, `MemoryOperand`, `Stack`, `Step`, `ControlFlow`, `Projection`, `Rvalue`, `ScalarOps`, `LocalAccess`, `RunLoop`, `Aggregate`, `Discriminant`, `Call`, `Place`, `VTable`, `DynamicLayout`, `MachineHooks`—stopping immediately before `import Miri.Interpreter.Constant` at line 22) have a transitive closure of **67 `.lean` files** with zero `Miri/Input/*` JSON decoder files.
   - Equivalently, `Miri.TreeBorrows` (`57` files) together with `Miri.Interpreter.Constant` (`+10` files: `AllocationImage`, `Decoder`, `DecoderValues`, `JsonTraversalCache`, `LowerMIR`, `Model`, `Model.Types`, `RuntimeMetadata`, `SharedPayloads`, `Constant`) also spans **67 `.lean` files**.
3. **131-File Single-Threaded Verification Core Closure**:
   Including the full single-threaded interpreter core—lines 1–38 of `Miri/Interpreter.lean` (`IntegerOps` through `PointerMachineBindings`, adding `Constant`, `PlaceDynamic`, `ExecutionSafety`, `FloatOps`, `Cast`, `PlaceMachine`, `ThreadLocal`, `Scheduling`, `LayoutCompat`, `Intrinsics`, `ValidityVisitor`, `ValidityMemory`, `ThreadExit`, `PlaceTypes`, `TypedMachineBindings`, `ThreadStacks`, `PointerMachineBindings`) plus `Miri.TreeBorrows`, `Miri.Memory`, `Miri.ABI`, `Miri.MIR.Syntax`, and `Miri.OperationalSafety`—yields a transitive closure of **131 `.lean` files**.

#### 4.4 Exhaustive Catalog of the 8 Open Interpreter Hook Structures and Value-Validity Retagging

`Basis: source`

1. **The 8 Open Interpreter Hook Structures (112 Distinct Fields)**:
   `proofs-rs/lean-miri` parameterizes its core step, place, rvalue, scalar, cast, control-flow, terminator, and local-storage evaluators by 8 open record types:

   | # | Hook Structure | File and Line Range | Type Parameters | Field Count and Complete Field List |
   | :--- | :--- | :--- | :--- | :--- |
   | 1 | `StepHooks` | `Miri/Interpreter/Step.lean:34-54` | `(Prov Layout Extra Machine Choice PlaceValue : Type)` | **10 fields**: `assign`, `evalPlace`, `writeDiscriminant`, `storageLive`, `storageDead`, `intrinsic`, `incrementConstEvalCounter`, `returnFromCurrentFrame`, `beforeTerminator`, `terminator` |
   | 2 | `PlaceHooks` | `Miri/Interpreter/Place.lean:10-31` | `(P S C E : Type)` | **16 fields**: `getFrame`, `setFrame`, `debugAssertions`, `frameIndex`, `resolveLayout`, `localToOp`, `projection`, `deref`, `checkPlaceType`, `allocateStack`, `writeMemoryNoValidate`, `afterLocalMovedToMemory`, `memoryOffset`, `writeLocalImmediate`, `enforceValidity`, `validate` |
   | 3 | `RvalueHooks` | `Miri/Interpreter/Rvalue.lean:19-44` | `(Prov S C V : Type)` | **25 fields**: `placeLayout`, `evalPlace`, `evalOperand`, `evalOperandAt` (defaulted to `evalOperand`), `evalPlaceToOp`, `readImmediate`, `writeImmediate`, `writePointer`, `threadLocalPointer`, `withRetagMode`, `copyOp`, `copyOpAllowTransmute`, `binaryOp`, `unaryOp`, `writeAggregate`, `writeRepeat`, `forceAllocation`, `toRef`, `enforceValidity`, `retagPtrValue`, `placeBaseRaw`, `normalize`, `cast`, `readDiscriminant`, `discriminantForVariant` |
   | 4 | `ScalarOpsHooks` | `Miri/Interpreter/ScalarOps.lean:14-24` | `(Prov S C : Type)` | **10 fields**: `classify`, `boolLayout`, `orderingLayout`, `overflowLayout`, `metadataLayout`, `unitLayout`, `floatBinary`, `pointerBinary`, `floatUnary`, `derefValidity` |
   | 5 | `CastHooks` | `Miri/Interpreter/Cast.lean:29-66` | `(P S C V : Type)` | **37 fields**: `target`, `typeInfo`, `layoutOf`, `destLayout`, `readImmediate`, `writeImmediate`, `writePointer`, `enforceValidity`, `enforceValidityRecursively`, `validatePlace`, `derefPointer`, `checkFunctionPointer`, `exposeProvenance`, `pointerFromExposedAddress`, `usizeLayout`, `floatOps` (`FloatOpsHooks`), `ensureMonomorphic`, `requireNoBoundVars`, `resolveFunction`, `resolveClosureFnOnce`, `functionPointer`, `builtinDeref`, `boxLayout`, `validateImmediateABI`, `copyAllowTransmute`, `copyNoValidate`, `projectRead`, `projectWrite`, `fieldLayout`, `lockstepTails`, `vtableType`, `vtablePointer`, `principal`, `vtableEntries`, `supertraitSlot`, `eraseSelfTraitRef`, `normalizePrincipal` |
   | 6 | `ControlHooks` | `Miri/Interpreter/ControlFlow.lean:9-19` | `(P L E M C Op : Type)` | **6 fields**: `bodySpan`, `returnOperand`, `popFrame`, `copyReturn`, `cleanupFrame`, `unwindTerminate` |
   | 7 | `TerminatorHooks` | `Miri/Interpreter/ControlFlow.lean:116-131` | `(P L E M C Op Imm : Type) extends ControlHooks P L E M C Op` | **8 own fields (+ 6 inherited from `ControlHooks` = 14 total)**: `evalDiscriminant`, `compareSwitchCase`, `call`, `tailCall`, `drop`, `ignoreOptionalOverflowChecks`, `readAssertCondition`, `assertPanic` |
   | 8 | `LocalStorageHooks` | `Miri/Interpreter/Stack.lean:239-245` | `(Prov Layout Extra State : Type)` | **6 fields**: `veryTriviallySized`, `layout`, `isSized`, `afterLocalWrite`, `allocateDyn`, `deallocateStack` |

2. **Why `Miri.MIR.StatementKind` and `Miri.Interpreter.StatementKind` Have No Standalone `.Retag` Constructor**:
   In `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` (`compiler/rustc_middle/src/mir/syntax.rs:146-214`), standalone `StatementKind::Retag` was removed from `rustc_middle::mir::StatementKind` and replaced by value-validity retagging:
   - `Rvalue::Use(Operand<'tcx>, WithRetag)` (`syntax.rs:1174`, `Miri/MIR/Syntax.lean:426`) carries a `WithRetag` flag (`.None` or `.Yes`). In `eval_rvalue_into_place` (`step.rs:179-184`, `Miri/Interpreter/Rvalue.lean:59-62`), `Rvalue.Use operand retag` executes `h.withRetagMode choice (if retag == .Yes then .Default else .None) (h.copyOp choice op dest)`.
   - `Rvalue::Ref` (`step.rs:214-239`, `Rvalue.lean:80-90`) runs under `RetagMode.TwoPhase` (for two-phase borrows) or `RetagMode.Default`, and `Rvalue::RawPtr` (`Rvalue.lean:95-104`) runs under `RetagMode.Raw`.
   - Function entry (`init_stack_frame` in `call.rs:456-515`, `Miri/Interpreter/Call.lean:227-269`) validates arguments under `RetagMode.FnEntry`.
   - During `copyOp` validation (`PlaceHooks.validate` → `Validity.checkSafePointer`), whenever `RetagMode != .None`, safe references and `Box` values invoke `retag_ptr_value` in place as part of value-validity checking. Accordingly, `Miri.MIR.StatementKind` (`Miri/MIR/Syntax.lean:441-454`) has 12 constructors and `Miri.Interpreter.StatementKind` (`Miri/Interpreter/Step.lean:23-32`) has 7 runtime constructors (`.Assign`, `.SetDiscriminant`, `.StorageLive`, `.StorageDead`, `.Intrinsic`, `.ConstEvalCounter`, `.Nop`), neither of which includes `.Retag`.

## Boundaries

1. **Rvalue `Operand::Move` vs. `Call` `Operand::Move` Asymmetry (`known not to apply`)**:
   The finding that `eval_operand` treats `Operand::Move` identically to `Operand::Copy` applies to rvalue operand evaluation (`Rvalue::Use`, `Rvalue::BinaryOp`, `Rvalue::UnaryOp`, `Rvalue::Aggregate`, `Rvalue::Repeat`, `Rvalue::Cast`, `Rvalue::WrapUnsafeBinder`), **not** to `TerminatorKind::Call` or `TailCall` argument evaluation when the moved argument is memory-backed (`.indirect`) or `moveDefinitelyDisjoint` is `false`. In those call-argument cases, `evalFnCallArgumentAt` and `passArgument` invoke `protectInPlaceFunctionArgument` + `writeUninit`, which both retags the place as `.Mutable` + `.FnEntry` and performs a Tree Borrows `.Write` access that deinitializes `initMask`.
2. **Immediate Locals Passed by `Operand::Move` to `Call` (`known not to apply`)**:
   Even in `TerminatorKind::Call`, when `moveDefinitelyDisjoint` is `true` and the moved local is stored as `LocalValue.immediate` (not forced into a memory allocation), `evalFnCallArgumentAt` (`Miri/Interpreter/Call.lean:183-191`, `step.rs:444-456`) returns `FnArg.copy (.immediate imm)` rather than `FnArg.inPlace`, so `protectInPlaceFunctionArgument` is not called and the immediate local remains initialized in the caller frame until overwritten or `StorageDead`.
3. **32-Bit Target Pointer Fragmentation (`unsupported`)**:
   In `Miri/Memory/ProvenanceMap.lean:185` (`if pointerSize != Size.ofBytes 8 then return #[]`) and `compiler/rustc_middle/src/mir/interpret/allocation/provenance_map.rs:230`, `PointerFrag` creation is implemented only for 8-byte pointers (`pointerSize == 8`). On 32-bit targets, sub-pointer copies via `MaybeUninit<u8>` do not record `PointerFrag` entries and strip provenance.
4. **Concurrency and Stacked Borrows (`not examined`)**:
   The forward-simulation proofs in [`support/LeanMiriInitSubsumesAndFragProbe.lean`](support/LeanMiriInitSubsumesAndFragProbe.lean) cover single-threaded execution with Tree Borrows (`BorrowTree`); Stacked Borrows and multi-threaded weak-memory / data-race states in `Miri/Concurrency/` were not examined beyond `TerminationInfo` classification.

## Evidence

### 1. Upstream Repository Revisions and Source Coordinates

- **`proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, `Miri/` tree `ef473f04eed9bbfed474a7b5f6f91a2f6350c41b`)**:
  - `Miri/Interpreter/LocalAccess.lean:120-128, 333-337`: `evalOperand` and theorem `copy_move_same`.
  - `Miri/Interpreter/OperandMachine.lean:31-35, 98-106`: `OperandMachine.localToOp` (throwing `.stack .localExpectedLive`) and `OperandMachine.evalOperand`.
  - `Miri/Interpreter/ExecutionMachine.lean:119-125, 164-235`: `RvalueHooks.evalOperand` wiring to `OperandMachine.evalOperand`.
  - `Miri/Interpreter/Call.lean:153-269`: `moveDefinitelyDisjoint`, `evalFnCallArgumentAt`, `passArgument`, and `initStackFrame`.
  - `Miri/Interpreter/MachineHooks.lean:365-429`: `protectInPlaceFunctionArgument` and `beforeStackPopWithEnsure`.
  - `Miri/Interpreter/MemoryOperand.lean:173-190`: `readPlan` branching on `.Scalar (.Initialized ...)` vs. `.notImmediate`.
  - `Miri/Memory/ProvenanceMap.lean:15-316`: `PointerFrag`, `ProvenanceMap`, `inspectFragments`, `readPtr`, `ptrFragments`, `clear`, and `prepareCopy`.
  - `Miri/Memory/Allocation.lean:314-411, 571-692`: `readPtrAt`, `getBytesStripProvenance`, `readScalar`, `writeScalar`, `writeUninit`, and `copyRepeatedly`.
  - `Miri/Memory/Identity.lean:87-100` and `Miri/Memory/CtfeProvenance.lean:118-121`: `PointerProvenance.offsetIsAddr` instances.
  - `Miri/Interpreter/ControlFlow.lean:9-131`: `ControlHooks`, `returnFromCurrentFrame`, and `TerminatorHooks`.
  - `Miri/Interpreter/Stack.lean:31-38, 150-286, 385-425`: `StackError`, `localToOp`, `storageDead`, `LocalStorageHooks`, `popStackFrameRaw`, and `cleanupStackFrame`.
  - `Miri/TreeBorrows/Permissions.lean:55-115, 268-271, 355-405`: `performAccess` and `associatedAccess`.
  - `Miri/TreeBorrows/TreeState.lean:1012-1156`: `updateExposureForProtectorRelease`, `releaseProtector`, and `deallocateBorrowRange`.
  - `Miri/TreeBorrows/FreezeVisitor.lean:74-135` and `Miri/TreeBorrows/RetagPipeline.lean:178-300`: `visitFreezeSensitive` and `retagPointerValue`.
  - `Miri/Concurrency/Termination.lean:19-66`: `TerminationInfo`, `TerminationReport`, `report`, and `isUbReport`.
  - `Miri/Interpreter/Step.lean:9-54`: `StepError`, `StatementKind`, and `StepHooks`.
  - `Miri/Interpreter/RunLoop.lean:87-91`: `RunLoop.reportsUB`.
  - `Miri/OperationalSafety.lean:19-90`: `Outcome`, `classifyError`, `NoUndefinedBehavior`, and `System.Safe`.
  - `Miri/MIR/Syntax.lean:396-454`: `Miri.MIR.Operand`, `Miri.MIR.Rvalue` (`Use (operand : Operand) (retag : WithRetag)`), and `Miri.MIR.StatementKind`.
  - `Miri/Interpreter/Place.lean:10-31, 347-376`, `Miri/Interpreter/Rvalue.lean:19-105`, `Miri/Interpreter/ScalarOps.lean:14-24`, `Miri/Interpreter/Cast.lean:29-66`: `PlaceHooks`, `copyRuntimePlaceNoValidate`, `copyRuntimePlace`, `RvalueHooks`, `ScalarOpsHooks`, and `CastHooks`.
- **`rust-lang/miri` (`7fa591d7d4dd9af8154becbc8332f8096f8323b1`)**:
  - `src/machine.rs:1857-1876, 1971-2020`: `protect_in_place_function_argument`, `before_stack_pop`, and `after_stack_pop`.
  - `src/borrow_tracker/mod.rs:359-398`: `FrameState::on_stack_pop`.
  - `src/borrow_tracker/tree_borrows/mod.rs:92-105, 212-358`: `release_protector` and `retag_ptr_value`.
  - `src/borrow_tracker/tree_borrows/tree.rs:671-738`: `Tree::release_protector`.
  - `src/borrow_tracker/tree_borrows/diagnostics.rs:29-33`: `AccessCause::FnExit` unreachable UB comment.
- **`rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`)**:
  - `compiler/rustc_middle/src/mir/syntax.rs:146-214, 1170-1210, 1731-1740`: `StatementKind`, `Rvalue::Use(Operand<'tcx>, WithRetag)`, and `Operand::Move`.
  - `compiler/rustc_middle/src/mir/interpret/allocation/provenance_map.rs:15-450`: `PointerFrag` and `ProvenanceMap`.
  - `compiler/rustc_const_eval/src/interpret/operand.rs:591-632, 837-853`: `read_immediate_from_mplace_raw` and `eval_operand`.
  - `compiler/rustc_const_eval/src/interpret/place.rs:970-1052`: `copy_op` and `copy_op_no_validate`.
  - `compiler/rustc_const_eval/src/interpret/step.rs:115-240, 369-480`: `eval_rvalue_into_place`, `move_definitely_disjoint`, and `eval_fn_call_argument`.
  - `compiler/rustc_const_eval/src/interpret/call.rs:412-515, 1134-1210`: `pass_argument`, `init_stack_frame`, and `return_from_current_stack_frame`.
  - `compiler/rustc_const_eval/src/interpret/stack.rs:280-290, 447-519`: `local_to_op` (`UbInfo::LocalUseAfterFree`), `pop_stack_frame_raw`, `cleanup_stack_frame`, and `make_local_dead`.

### 2. Preserved Standalone Lean 4 Formalization (`support/LeanMiriInitSubsumesAndFragProbe.lean`)

The self-contained Lean 4 file [`support/LeanMiriInitSubsumesAndFragProbe.lean`](support/LeanMiriInitSubsumesAndFragProbe.lean) formalizes `AbsByte`, `ByteProvFrag`, `readScalarAt`, `writeScalarAt`, `copyBytes`, `deinitRange`, `InitSubsumes`, `StateSubsumes`, `tbPerformAccess`, `retagPlace`, and `deallocateAlloc`, and proves 14 theorems checked by both Lean `v4.28.0-rc1` (`3b0f2862196c6a8af9eb0025ee650252694013dd`) and Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with zero `sorryAx` and zero `Lean.ofReduceBool`:

```text
'LeanMiriInitSubsumesAndFragProbe.byte_by_byte_maybe_uninit_copy_preserves_prov' depends on axioms: [propext]
'LeanMiriInitSubsumesAndFragProbe.u8_copy_strips_prov' depends on axioms: [propext]
'LeanMiriInitSubsumesAndFragProbe.chimeric_splice_strips_prov' depends on axioms: [propext]
'LeanMiriInitSubsumesAndFragProbe.chimeric_splice_general_strips_prov' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanMiriInitSubsumesAndFragProbe.readScalarInitializedAt_simulation' depends on axioms: [propext, Quot.sound]
'LeanMiriInitSubsumesAndFragProbe.readScalarUnionAt_simulation' depends on axioms: [propext]
'LeanMiriInitSubsumesAndFragProbe.readScalarAt_simulation' depends on axioms: [propext, Quot.sound]
'LeanMiriInitSubsumesAndFragProbe.writeScalarAt_simulation' depends on axioms: [propext]
'LeanMiriInitSubsumesAndFragProbe.copyBytes_simulation' depends on axioms: [propext, Quot.sound]
'LeanMiriInitSubsumesAndFragProbe.deinitRange_preserves_InitSubsumes' depends on axioms: [propext, Quot.sound]
'LeanMiriInitSubsumesAndFragProbe.tb_write_on_move_breaks_borrow_tree_equiv' depends on axioms: [propext]
'LeanMiriInitSubsumesAndFragProbe.moveDeinit_preserves_StateSubsumes' depends on axioms: [propext, Quot.sound]
'LeanMiriInitSubsumesAndFragProbe.retagPlace_simulation' depends on axioms: [propext, Quot.sound]
'LeanMiriInitSubsumesAndFragProbe.deallocateAlloc_simulation' does not depend on any axioms
```

### 3. Preserved Rust and Miri Execution Probe (`support/miri_probe/`)

The crate in [`support/miri_probe/Cargo.toml`](support/miri_probe/Cargo.toml) and [`support/miri_probe/src/lib.rs`](support/miri_probe/src/lib.rs) contains 4 positive tests and 5 negative `#[ignore]` UB witness tests executed under `MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test` (`rustc 1.102.0-nightly (3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1 2026-11-11)`):

- Positive suite (`MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test`):
  ```text
  running 9 tests
  test tests::test_chimeric_splice_same_tag_same_vs_diff_offset ... ok
  test tests::test_pointer_copy_maybe_uninit_vs_u8 ... ok
  test tests::test_rvalue_move_does_not_deinit_or_tb_write ... ok
  test tests::test_ub_call_move_local_deinits_in_place_arg ... ignored
  test tests::test_ub_chimeric_splice_same_tag_diff_offset_strips_prov ... ignored
  test tests::test_ub_dealloc_local_with_active_strong_protector ... ignored
  test tests::test_ub_u8_copy_strips_provenance ... ignored
  test tests::test_ub_unwind_protector_end_access_disables_sibling ... ignored
  test tests::test_unwind_with_valid_fn_entry_protector ... ok

  test result: ok. 4 passed; 0 failed; 5 ignored; 0 measured; 0 filtered out
  ```
- Negative UB witnesses (`MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test -- --ignored <test_name>`):
  1. `test_ub_call_move_local_deinits_in_place_arg`: fails with `Undefined Behavior: reading memory at alloc...[0x0..0x8], but memory is uninitialized at [0x0..0x8]`.
  2. `test_ub_u8_copy_strips_provenance`: fails with `Undefined Behavior: memory access failed: attempting to access 8 bytes, but got 0x...[noalloc] which is a dangling pointer (it has no provenance)`.
  3. `test_ub_chimeric_splice_same_tag_diff_offset_strips_prov`: fails with `Undefined Behavior: memory access failed: attempting to access 8 bytes, but got 0x...[noalloc] which is a dangling pointer (it has no provenance)`.
  4. `test_ub_dealloc_local_with_active_strong_protector`: fails with `Undefined Behavior: deallocation through <...> (root of the allocation) at alloc...[0x0] is forbidden ... this deallocation (acting as a foreign write access) would cause the protected tag <...> (currently Unique) to become Disabled`.
  5. `test_ub_unwind_protector_end_access_disables_sibling`: fails with `Undefined Behavior: write access through <...> at alloc...[0x8] is forbidden ... help: the accessed tag <...> later transitioned to Disabled due to a protector release (acting as a foreign write access) on every location previously accessed by this tag`.

## Revalidation

1. **Re-check the Lean 4 Formalization**:
   Run the Lean 4 kernel over [`support/LeanMiriInitSubsumesAndFragProbe.lean`](support/LeanMiriInitSubsumesAndFragProbe.lean) and verify that all 14 `#print axioms` lines report only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) with zero `sorryAx` and zero `Lean.ofReduceBool`:
   ```bash
   lean reports/lean-miri-interpreter-hooks-move-deinit-and-provenance-fragments/support/LeanMiriInitSubsumesAndFragProbe.lean
   ```
2. **Re-run the Miri Positive and Negative Execution Probes**:
   Copy `support/miri_probe` to a temporary directory (so build artifacts do not dirty the corpus tree) and run `cargo +nightly miri test`:
   ```bash
   tmpdir="$(mktemp -d)"
   cp -r reports/lean-miri-interpreter-hooks-move-deinit-and-provenance-fragments/support/miri_probe "$tmpdir/"
   (
     cd "$tmpdir/miri_probe"
     MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test
     for t in \
       test_ub_call_move_local_deinits_in_place_arg \
       test_ub_u8_copy_strips_provenance \
       test_ub_chimeric_splice_same_tag_diff_offset_strips_prov \
       test_ub_dealloc_local_with_active_strong_protector \
       test_ub_unwind_protector_end_access_disables_sibling; do
       ! MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test -- --ignored "$t"
     done
   )
   rm -rf "$tmpdir"
   ```
3. **Check Upstream Source Invariants on Newer Revisions**:
   - In `rustc_const_eval`, inspect `InterpCx::eval_operand` (`compiler/rustc_const_eval/src/interpret/operand.rs`), `InterpCx::read_immediate_from_mplace_raw` (`operand.rs`), `eval_fn_call_argument` (`step.rs`), `pass_argument` (`call.rs`), and `return_from_current_stack_frame` (`call.rs`) to see whether `&Copy(place) | &Move(place)` has been split or whether `Scalar::Union` handling in `read_immediate_from_mplace_raw` has changed.
   - In `proofs-rs/lean-miri`, check `Miri/Interpreter/LocalAccess.lean` (`evalOperand`), `Miri/Memory/ProvenanceMap.lean` (`inspectFragments` and `ptrFragments`), `Miri/Interpreter/ControlFlow.lean` (`returnFromCurrentFrame`), and `Miri/Interpreter/RunLoop.lean` (`reportsUB`).
