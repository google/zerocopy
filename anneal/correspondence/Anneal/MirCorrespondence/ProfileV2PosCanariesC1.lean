-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.Correspondence
import Anneal.MirWp
import Anneal.MirCorrespondence.ByteCodec
import Anneal.MirCorrespondence.LayoutAndAlign
import Anneal.MirCorrespondence.MiriMemoryBridge
import Anneal.MirCorrespondence.ProfileV2RefMachine
import Anneal.MirCorrespondence.ProfileV2Correspondence
import Anneal.MirCorrespondence.ProfileV2Witnesses
import Anneal.MirCorrespondence.ProfileV2EdgeWitnesses
import Anneal.MirCorrespondence.ProfileV2Canaries
import Anneal.MirCorrespondence.ProfileV2PosCanaries
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.SimHelpers

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Anneal.MirWp

/-!
# Profile v2 Positive Canary `V2_C1` (`ProfileV2PosCanariesC1`)

Proves end-to-end lockstep agreement between Anneal Profile v2 (`evalStepV2` /
`CallerMemory`) and `ProfileV2RefMachine` on `V2_C1` (slice split via
`RangeTo`/`RangeFrom` aggregates and `slice::len`).
-/

/-! ## Section 1: `V2_C1` (slice split) shared state definitions -/

/-- Encoded `V2_C1` program. -/
noncomputable abbrev c1Rp : RefProg := encodeProg progV2_C1_splitAt
/-- Entry body of the encoded `V2_C1` program. -/
noncomputable abbrev c1Body : RefBody :=
  @GetElem.getElem _ Nat _ _ _ c1Rp.bodies 0 (by decide)

/-- Slice reference type `&[u8]`. -/
noncomputable abbrev c1SliceTy : MirTy := .ref .shared (.slice u8Ty)
/-- Unsigned pointer-sized integer type `usize`. -/
noncomputable abbrev c1UsizeTy : MirTy := .int .isize false
/-- Return tuple type `(&[u8], usize)` of `V2_C1`. -/
noncomputable abbrev c1TupTy : MirTy := .tuple [c1SliceTy, c1UsizeTy]

/-- Local layout of `(&[u8], usize)` in `V2_C1`. -/
noncomputable abbrev c1Tup := refLocalLayoutForTyV2 c1Rp.types c1TupTy
/-- Local layout of `&[u8]` in `V2_C1`. -/
noncomputable abbrev c1Sl := refLocalLayoutForTyV2 c1Rp.types c1SliceTy
/-- Local layout of `usize` in `V2_C1`. -/
noncomputable abbrev c1Us := refLocalLayoutForTyV2 c1Rp.types c1UsizeTy
/-- Local layout of `RangeTo<usize>` in `V2_C1`. -/
noncomputable abbrev c1RTo :=
  refLocalLayoutForTyV2 c1Rp.types (.rangeTo c1UsizeTy)
/-- Local layout of `RangeFrom<usize>` in `V2_C1`. -/
noncomputable abbrev c1RFrom :=
  refLocalLayoutForTyV2 c1Rp.types (.rangeFrom c1UsizeTy)

/-- Concrete read-only caller allocation `alloc2` of `V2_C1`. -/
noncomputable def c1A2 : Miri.Memory.Allocation Miri.Memory.Provenance Unit :=
  exceptOkGet (Miri.Memory.Allocation.fromBytes
    (Array.mk [10, 20, 30, 40, 50]) ⟨0⟩ .Not) rfl

/-- Root frame of `V2_C1` at statement `idx` of block `bb`. -/
noncomputable def c1Frame (bb idx : Nat) (locals : List RefLocalState) :=
  mkRefMiriFrameV2 c1Rp.types 0 c1Body bb idx locals ⟨retMemPlaceV2, c1Tup⟩

/-- `V2_C1` reference state at statement `idx` of block `bb` with terminator
control `ctrl`. -/
noncomputable def c1St (bb idx : Nat) (locals : List RefLocalState)
    (mem : RefMiriMem)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) : RefMiriState :=
  mkRefMiriState (c1Frame bb idx locals) mem ctrl callerMemV2_C1

/-- Lowered basic block `bb` of `V2_C1`. -/
noncomputable abbrev c1Block (bb : Nat) (h : bb < 4 := by decide) :
    Miri.MIR.BasicBlock :=
  toMiriBasicBlockV2 c1Rp.types
    (@GetElem.getElem _ Nat _ _ _ c1Body.basicBlocks bb h)

/-! ## Section 2: `V2_C1` concrete reference states -/

/-- Fresh Tree Borrows tree (root tag `BorTag.one`) over `n` bytes. -/
noncomputable def c1Tree (n : UInt64) : Miri.TreeBorrows.BorrowTree :=
  Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
    (Miri.ABI.Size.ofBytes n)

/-- Concrete image of the 24-byte return buffer made by `tryNew`. -/
noncomputable def c1Ret : Miri.Memory.Allocation Miri.Memory.Provenance Unit :=
  estateOkGet (Miri.Memory.Allocation.writeUninit
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 24))
    (Miri.ABI.Size.ofBytes 8)
    (exceptOkGet (Miri.Memory.Allocation.fromBytes
      (Array.replicate 24 0) Miri.ABI.Align.EIGHT .Mut) rfl)) rfl

/-- Concrete image of a fresh 8-byte stack buffer made by `tryNew`. -/
noncomputable def c1Blank8 :
    Miri.Memory.Allocation Miri.Memory.Provenance Unit :=
  estateOkGet (Miri.Memory.Allocation.writeUninit
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
    (Miri.ABI.Size.ofBytes 8)
    (exceptOkGet (Miri.Memory.Allocation.fromBytes
      (Array.replicate 8 0) Miri.ABI.Align.EIGHT .Mut) rfl)) rfl

/-- 8-byte stack buffer of `_4` / `_6` after writing `2usize`. -/
noncomputable def c1A8 : Miri.Memory.Allocation Miri.Memory.Provenance Unit :=
  exceptOkGet (Miri.Memory.Allocation.fromBytes
    (Array.mk [2, 0, 0, 0, 0, 0, 0, 0]) Miri.ABI.Align.EIGHT .Mut) rfl

/-- One row of the reference memory's `live` table. -/
abbrev C1Row := Miri.Memory.AllocId ×
  Miri.Memory.LocalAllocation Miri.Memory.Provenance
    Miri.TreeBorrows.BorrowTree Unit

/-- `V2_C1` reference memory with live rows `live`, next id `next` and issued
ids `issued`. -/
noncomputable def c1Mem (next : UInt64) (live : Array C1Row)
    (issued : Array Miri.Memory.AllocId) : RefMiriMem :=
  ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
      nextAllocId := next, live := live }).setIssuedIds issued

/-- Live row of caller read-only allocation `alloc2`. -/
noncomputable def c1Row2 : C1Row :=
  (alloc2IdV2, ⟨.machine (), c1A2.withExtra (c1Tree 5)⟩)

/-- Live row of the 24-byte return buffer `retAllocIdV2`. -/
noncomputable def c1RowRet : C1Row :=
  (retAllocIdV2, ⟨.stack, c1Ret.withExtra (c1Tree 24)⟩)

/-- `usize` scalar `n`. -/
noncomputable def c1Usize (n : Nat) :
    Miri.Memory.Scalar Miri.Memory.Provenance :=
  .fromScalarInt (miriScalar .isize (BitVec.ofNat 128 n))

/-- Pointer scalar into caller `alloc2` at byte offset `off`. -/
noncomputable def c1PtrSc (off : UInt64) :
    Miri.Memory.Scalar Miri.Memory.Provenance :=
  .fromPointer refRuntimeLayoutV2.base
    ⟨Miri.ABI.Size.ofBytes off, .concrete alloc2IdV2 Miri.Memory.BorTag.one⟩

/-- Wide `&[u8]` immediate: `len` bytes of `alloc2` starting at `off`. -/
noncomputable def c1Slice (off : UInt64) (len : Nat) :
    Miri.Interpreter.Immediate Miri.Memory.Provenance :=
  .scalarPair (c1PtrSc off) (c1Usize len)

/-- Uninitialized immediate local value. -/
noncomputable abbrev c1U :
    Miri.Interpreter.LocalValue Miri.Memory.Provenance :=
  .live (.immediate .uninit)

/-- Initialized immediate local value holding `i`. -/
noncomputable abbrev c1I
    (i : Miri.Interpreter.Immediate Miri.Memory.Provenance) :
    Miri.Interpreter.LocalValue Miri.Memory.Provenance :=
  .live (.immediate i)

/-- `V2_C1` locals with `_2`..`_7` holding the given local values. -/
noncomputable def c1Locals
    (v2 v3 v4 v5 v6 v7 : Miri.Interpreter.LocalValue Miri.Memory.Provenance) :
    List RefLocalState :=
  [⟨c1U, some c1Tup⟩, ⟨c1I (c1Slice 0 5), some c1Sl⟩,
   ⟨v2, some c1Us⟩, ⟨v3, some c1Sl⟩, ⟨v4, some c1RTo⟩, ⟨v5, some c1Sl⟩,
   ⟨v6, some c1RFrom⟩, ⟨v7, some c1Us⟩]

/-- Initial `V2_C1` reference memory containing caller `alloc2` and the return
buffer. -/
noncomputable def c1Mem0 : RefMiriMem :=
  c1Mem 3 (Array.mk [c1Row2, c1RowRet]) (Array.mk [alloc2IdV2, retAllocIdV2])

/-- Entry state (bb0, stmt 0). -/
noncomputable def c1S_entry : RefMiriState :=
  c1St 0 0 (c1Locals (c1I (.scalar (c1Usize 2))) c1U c1U c1U c1U c1U)
    c1Mem0 refInitControl

/-- Stack place of the force-allocated local living in allocation `id`. -/
noncomputable def c1Mp (id : Miri.Memory.AllocId) :
    Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
  ⟨⟨Miri.ABI.Size.ZERO, some (.concrete id Miri.Memory.BorTag.one)⟩,
    .none, none⟩

/-- Indirect local value backed by stack allocation `id`. -/
noncomputable abbrev c1M (id : Miri.Memory.AllocId) :
    Miri.Interpreter.LocalValue Miri.Memory.Provenance :=
  .live (.indirect (c1Mp id))

/-- Live row of the 8-byte stack buffer `id` holding `2usize`. -/
noncomputable def c1Row8 (id : Miri.Memory.AllocId) : C1Row :=
  (id, ⟨.stack, c1A8.withExtra (c1Tree 8)⟩)

/-- Memory after force-allocating `_4` into `alloc3`. -/
noncomputable def c1Mem1 : RefMiriMem :=
  c1Mem 4 (Array.mk [c1Row2, c1RowRet, c1Row8 alloc3IdV2])
    (Array.mk [alloc2IdV2, retAllocIdV2, alloc3IdV2])

/-- Memory after force-allocating `_6` into `alloc4`. -/
noncomputable def c1Mem2 : RefMiriMem :=
  c1Mem 5
    (Array.mk [c1Row2, c1RowRet, c1Row8 alloc3IdV2, c1Row8 alloc4IdV2])
    (Array.mk [alloc2IdV2, retAllocIdV2, alloc3IdV2, alloc4IdV2])

/-- Immediate `2usize` local value. -/
noncomputable abbrev c1Two :
    Miri.Interpreter.LocalValue Miri.Memory.Provenance :=
  c1I (.scalar (c1Usize 2))

/-- Terminator control state after `n` terminators. -/
noncomputable def c1Ctrl : Nat → Miri.Interpreter.TerminatorMachine.Control Unit
  | 0 => refInitControl
  | n + 1 => advanceRefControl (c1Ctrl n)

/-- Allocation-span entry in `MachineState.allocationSpans`. -/
abbrev C1Span := Miri.Memory.AllocId × Miri.MIR.SpanRef ×
  Option Miri.MIR.SpanRef

/-- Allocation-span row recorded when local storage moves to memory. -/
noncomputable def c1Sp (id : Miri.Memory.AllocId) : C1Span := (id, ⟨0⟩, none)

/-- `c1St` with explicit `allocationSpans`. -/
noncomputable def c1StS (bb idx : Nat) (locals : List RefLocalState)
    (mem : RefMiriMem) (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (spans : Array C1Span) : RefMiriState :=
  { stack := (c1St bb idx locals mem ctrl).stack
    machine := { (c1St bb idx locals mem ctrl).machine with
      allocationSpans := spans } }

/-- Allocation spans after force-allocating `_4`. -/
noncomputable abbrev c1Spans1 : Array C1Span := Array.mk [c1Sp alloc3IdV2]

/-- Allocation spans after force-allocating `_4` and `_6`. -/
noncomputable abbrev c1Spans2 : Array C1Span :=
  Array.mk [c1Sp alloc3IdV2, c1Sp alloc4IdV2]

/-- State at (bb0, stmt 1), after `_4 = RangeTo(copy _2)`. -/
noncomputable def c1S_bb0_1 : RefMiriState :=
  c1StS 0 1 (c1Locals c1Two c1U (c1M alloc3IdV2) c1U c1U c1U) c1Mem1
    (c1Ctrl 0) c1Spans1

/-- State at (bb1, stmt 0), after `_3 = get_unchecked(_1, ..2)`. -/
noncomputable def c1S_bb1_0 : RefMiriState :=
  c1StS 1 0 (c1Locals c1Two (c1I (c1Slice 0 2)) (c1M alloc3IdV2) c1U c1U c1U)
    c1Mem1 (c1Ctrl 1) c1Spans1

/-- State at (bb1, stmt 1), after `_6 = RangeFrom(move _2)`. -/
noncomputable def c1S_bb1_1 : RefMiriState :=
  c1StS 1 1 (c1Locals c1U (c1I (c1Slice 0 2)) (c1M alloc3IdV2) c1U
      (c1M alloc4IdV2) c1U) c1Mem2 (c1Ctrl 1) c1Spans2

/-- State at (bb2, stmt 0), after `_5 = get_unchecked(_1, 2..)`. -/
noncomputable def c1S_bb2_0 : RefMiriState :=
  c1StS 2 0 (c1Locals c1U (c1I (c1Slice 0 2)) (c1M alloc3IdV2)
      (c1I (c1Slice 2 3)) (c1M alloc4IdV2) c1U) c1Mem2 (c1Ctrl 2) c1Spans2

/-- State at (bb3, stmt 0), after `_7 = len(move _3)`. -/
noncomputable def c1S_bb3 : RefMiriState :=
  c1StS 3 0 (c1Locals c1U c1U (c1M alloc3IdV2) (c1I (c1Slice 2 3))
      (c1M alloc4IdV2) c1Two) c1Mem2 (c1Ctrl 3) c1Spans2

/-! ## Section 3: `V2_C1` entry and core-call steps (`bb0`, `bb1`, `bb2`) -/

/-- `Allocation.tryNew` of the 24-byte return buffer equals `c1Ret`. -/
theorem c1_tryNew24 :
    Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (Miri.ABI.Size.ofBytes 24) ⟨3⟩ .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok c1Ret :=
  tryNew_eq_of_image_v2 _ _ 8 _ _ rfl rfl (by decide) rfl rfl

/-- Entry initialization of the `V2_C1` reference machine. -/
theorem c1_init (ms : Nat) :
    initRefStateV2 c1Rp queryV2_C1 ms =
      .ok { miri := c1S_entry, retTy := c1TupTy,
            retPlace := ⟨retMemPlaceV2, c1Tup⟩,
            stepsExecuted := 0, maxSteps := ms } := by
  have h_icm : refInitCallerMemoryV2 c1Rp.types callerMemV2_C1 c1TupTy =
      .ok (c1Mem0, ⟨retMemPlaceV2, c1Tup⟩) := by
    dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2,
      refTupleLayoutFitsU64V2, refTyLayoutFitsU64V2, refNatFitsU64V2,
      Bool.not_true, ite_false]
    rw [show c1Tup.layout.size = Miri.ABI.Size.ofBytes 24 from rfl,
      show c1Tup.layout.align.abi = (⟨3⟩ : Miri.ABI.Align) from rfl,
      c1_tryNew24]
    rfl
  exact initRefStateV2_ok_v2 c1Rp queryV2_C1 ms c1Body
    [c1TupTy, c1SliceTy, c1UsizeTy, c1SliceTy, .rangeTo c1UsizeTy, c1SliceTy,
      .rangeFrom c1UsizeTy, c1UsizeTy] c1TupTy c1Mem0 c1Mem0
    ⟨retMemPlaceV2, c1Tup⟩ _
    rfl rfl rfl rfl rfl rfl rfl rfl h_icm rfl rfl rfl

/-! ### Core-call dispatch helpers -/

/-- Call hooks of the Profile v2 reference machine for `V2_C1`. -/
noncomputable abbrev c1Calls :=
  Miri.Interpreter.ExecutionMachine.callHooks (refExecCfgV2 c1Rp) refLimitsV2

private theorem eStateM_bind_assoc {ε σ α β γ : Type}
    (x : EStateM ε σ α) (f : α → EStateM ε σ β) (g : β → EStateM ε σ γ) :
    EStateM.bind (EStateM.bind x f) g =
      EStateM.bind x (fun a => EStateM.bind (f a) g) := by
  funext s
  dsimp only [EStateM.bind]
  cases x s <;> rfl

private theorem eStateM_pure_bind {ε σ α β : Type} (a : α)
    (f : α → EStateM ε σ β) :
    EStateM.bind (EStateM.pure a) f = f a := rfl

private def c1ResMatch {S A : Type}
    (motive : EStateM.Result Miri.Interpreter.StepError S A → Type)
    (x : EStateM.Result Miri.Interpreter.StepError S A)
    (h1 : ∀ (val : A) (s' : S), motive (.ok val s'))
    (h2 : ∀ (err : Miri.Interpreter.StepError) (s' : S),
      motive (.error err s')) : motive x :=
  match x with
  | .ok val s' => h1 val s'
  | .error err s' => h2 err s'

/-- `ForeignItems.emulate` on a Profile v2 core-call symbol that finishes with
a normal block return. -/
theorem c1f_emulate (name : String) (abi : Miri.ABI.FnAbi Miri.MIR.TyId)
    (args : Array (Miri.Interpreter.OpTy Miri.Memory.Provenance))
    (dest : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance)
    (ret : Option Nat) (unwind : Miri.MIR.UnwindAction)
    (st st1 st2 : RefMiriState)
    (h_name : name = "__anneal_core_slice_get_unchecked_range_to" ∨
      name = "__anneal_core_slice_get_unchecked_range_from" ∨
      name = "__anneal_core_slice_len")
    (h : refExecCoreCallForeignV2 c1Rp.types name abi args dest st =
      .ok .NeedsReturn st1)
    (h_ret : (refForeignHooksV2 c1Rp.types).returnToBlock ret st1 =
      .ok () st2) :
    Miri.Interpreter.ForeignItems.emulate (refForeignHooksV2 c1Rp.types)
      name abi args dest ret unwind st = .ok none st2 := by
  have h' : (refForeignHooksV2 c1Rp.types).math name abi args dest st =
      .ok .NeedsReturn st1 := h
  change EStateM.bind (Miri.Interpreter.ForeignItems.inner
    (refForeignHooksV2 c1Rp.types) name abi args dest) _ st = _
  have h_in : Miri.Interpreter.ForeignItems.inner
      (refForeignHooksV2 c1Rp.types) name abi args dest st =
      .ok .NeedsReturn st1 := by
    unfold Miri.Interpreter.ForeignItems.inner
    simp only [← Array.contains_toList]
    cases h_name with
    | inl h_eq =>
      subst h_eq
      change EStateM.bind
        ((refForeignHooksV2 c1Rp.types).math _ abi args dest) _ st = _
      rw [eStateM_bind_ok h']; rfl
    | inr h_eq =>
      cases h_eq with
      | inl h_eq =>
        subst h_eq
        change EStateM.bind
          ((refForeignHooksV2 c1Rp.types).math _ abi args dest) _ st = _
        rw [eStateM_bind_ok h']; rfl
      | inr h_eq =>
        subst h_eq
        change EStateM.bind
          ((refForeignHooksV2 c1Rp.types).math _ abi args dest) _ st = _
        rw [eStateM_bind_ok h']; rfl
  rw [eStateM_bind_ok h_in]
  change EStateM.bind ((refForeignHooksV2 c1Rp.types).returnToBlock ret) _
    st1 = _
  rw [eStateM_bind_ok h_ret]
  rfl

/-- `findMirOrEvalFn` on a Profile v2 core-call instance. -/
theorem c1f_find (defId : Nat) (abi : Miri.ABI.FnAbi Miri.MIR.TyId)
    (args : Array (Miri.Interpreter.FnArg Miri.Memory.Provenance))
    (ops : Array (Miri.Interpreter.OpTy Miri.Memory.Provenance))
    (dest : Miri.Interpreter.RuntimeStackPlace Miri.Memory.Provenance)
    (ret : Option Nat) (unwind : Miri.MIR.UnwindAction)
    (st st1 st2 : RefMiriState)
    (h_id : defId = 0 ∨ defId = 1 ∨ defId = 2)
    (h_ops : args.map Miri.Interpreter.FnArg.copyFnArg = ops)
    (h : refExecCoreCallForeignV2 c1Rp.types
      (refCoreCallSymbolNameV2 c1Rp.types ⟨.Item defId, Array.empty⟩) abi ops
      dest.toRuntimePlace st = .ok .NeedsReturn st1)
    (h_ret : (refForeignHooksV2 c1Rp.types).returnToBlock ret st1 =
      .ok () st2) :
    c1Calls.findMirOrEvalFn 0 ⟨.Item defId, Array.empty⟩ abi args dest ret
      unwind st = .ok none st2 := by
  subst h_ops
  cases h_id with
  | inl h_id0 =>
    subst h_id0
    exact c1f_emulate _ abi _ _ ret unwind st st1 st2 (.inr (.inr rfl)) h h_ret
  | inr h_id12 =>
    cases h_id12 with
    | inl h_id1 =>
      subst h_id1
      exact c1f_emulate _ abi _ _ ret unwind st st1 st2 (.inl rfl) h h_ret
    | inr h_id2 =>
      subst h_id2
      exact c1f_emulate _ abi _ _ ret unwind st st1 st2
        (.inr (.inl rfl)) h h_ret

/-- Step over the first action inside a wrapper `W` that is the identity on
successful results (e.g. the private `Call.cleanupTempArgsOnError`). -/
theorem eStateM_wrap_bind_ok {ε σ α β γ : Type}
    (W : EStateM ε σ β → EStateM ε σ β)
    (hW : ∀ act s v s', act s = .ok v s' → W act s = .ok v s')
    {X : EStateM ε σ α} {K2 : α → EStateM ε σ β} {K : β → EStateM ε σ γ}
    {s s1 : σ} {x : α} (y : β) (s2 : σ) {R : EStateM.Result ε σ γ}
    (h : X s = .ok x s1) (h2 : K2 x s1 = .ok y s2) (h3 : K y s2 = R) :
    EStateM.bind (W (EStateM.bind X K2)) K s = R := by
  have h4 : EStateM.bind X K2 s = .ok y s2 := by
    dsimp only [EStateM.bind]; rw [h]; exact h2
  dsimp only [EStateM.bind]
  rw [hW _ _ _ _ h4]
  exact h3

/-- Dispatch of a Profile v2 core call with copied arguments. -/
theorem c1f_initFnCall (n defId : Nat) (abi : Miri.ABI.FnAbi Miri.MIR.TyId)
    (args : Array (Miri.Interpreter.FnArg Miri.Memory.Provenance))
    (a b : Miri.Interpreter.OpTy Miri.Memory.Provenance)
    (ops : Array (Miri.Interpreter.OpTy Miri.Memory.Provenance))
    (dest : Miri.Interpreter.RuntimeStackPlace Miri.Memory.Provenance)
    (ret : Option Nat) (unwind : Miri.MIR.UnwindAction)
    (st st1 st2 : RefMiriState)
    (h_id : defId = 0 ∨ defId = 1 ∨ defId = 2)
    (h_args : (args = Array.mk [.Copy a, .Copy b] ∧ ops = Array.mk [a, b]) ∨
      (args = Array.mk [.Copy a] ∧ ops = Array.mk [a]))
    (h : refExecCoreCallForeignV2 c1Rp.types
      (refCoreCallSymbolNameV2 c1Rp.types ⟨.Item defId, Array.empty⟩) abi ops
      dest.toRuntimePlace st = .ok .NeedsReturn st1)
    (h_ret : (refForeignHooksV2 c1Rp.types).returnToBlock ret st1 =
      .ok () st2) :
    Miri.Interpreter.Call.initFnCall c1Calls 0 (n + 1)
      ⟨.Instance ⟨.Item defId, Array.empty⟩, (), some abi, args, false, dest,
        ret, unwind, Array.empty⟩ st = .ok () st2 := by
  have h_ops : args.map Miri.Interpreter.FnArg.copyFnArg = ops := by
    cases h_args with
    | inl h =>
      let ⟨ha, hb⟩ := h
      subst ha; subst hb; rw [List.map_toArray]; rfl
    | inr h =>
      let ⟨ha, hb⟩ := h
      subst ha; subst hb; rw [List.map_toArray]; rfl
  let unwind' : Miri.MIR.UnwindAction :=
    if (some abi).any (fun x => !c1Calls.abiCanUnwind x) then .Unreachable
    else unwind
  have h_f := c1f_find defId abi args ops dest ret unwind' st st1 st2 h_id
    h_ops h h_ret
  have h_fi : c1Calls.isForeignItem ⟨.Item defId, Array.empty⟩ =
      EStateM.pure true := by
    funext st'
    cases h_id with
    | inl h_id0 => subst h_id0; rfl
    | inr h_id12 =>
      cases h_id12 with
      | inl h_id1 => subst h_id1; rfl
      | inr h_id2 => subst h_id2; rfl
  have h_mat : Miri.Interpreter.Call.materializeAndDeinitArgs c1Calls 0 args =
      EStateM.pure (args, Array.empty) := by
    funext st'
    unfold Miri.Interpreter.Call.materializeAndDeinitArgs
    simp only [← Array.any_toList]
    cases h_args with
    | inl h => let ⟨ha, _⟩ := h; subst ha; rfl
    | inr h => let ⟨ha, _⟩ := h; subst ha; rfl
  have h_step : Miri.Interpreter.Call.initFnCallStep c1Calls 0
      ⟨.Instance ⟨.Item defId, Array.empty⟩, (), some abi, args, false, dest,
        ret, unwind, Array.empty⟩ st = .ok none st2 := by
    unfold Miri.Interpreter.Call.initFnCallStep
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [eStateM_pure_bind, show c1Calls.deinitMovedPlace = true from rfl]
    simp only [ite_true]
    rw [h_fi, eStateM_pure_bind]
    simp only [ite_true]
    rw [h_mat]
    refine eStateM_apply_bind _ _ (args, Array.empty) st st ?_ ?_
    · rfl
    dsimp only
    refine eStateM_wrap_bind_ok _ (fun act s v s' hh => ?_) () st2 h_f ?_ rfl
    · change c1ResMatch
        (fun _ => EStateM.Result Miri.Interpreter.StepError RefMiriState Unit)
        (act s) (fun val s'' => EStateM.Result.ok val s'')
        (fun err s'' => _) = .ok v s'
      dsimp only [c1ResMatch]
      rw [hh]
    · cases h_args with
      | inl h => let ⟨ha, _⟩ := h; subst ha; rfl
      | inr h => let ⟨ha, _⟩ := h; subst ha; rfl
  change EStateM.bind (Miri.Interpreter.Call.initFnCallStep c1Calls 0 _) _
    st = _
  rw [eStateM_bind_ok h_step]
  rfl

/-- Raw memory read of an 8-byte integer scalar (cf.
`readImmediate_mem_u32_v2`). -/
theorem readImmediate_mem_u64_v2
    (lay : Miri.Interpreter.LocalLayout)
    (vr : Miri.ABI.WrappingRange)
    (mplace : Miri.Interpreter.MemPlace Miri.Memory.Provenance)
    (aid : Miri.Memory.AllocId) (alloc : RefMiriAlloc)
    (sc : Miri.Memory.Scalar Miri.Memory.Provenance)
    (st : RefMiriState) (mem1 : RefMiriMem)
    (off : Miri.ABI.Size) (ghost : Bool)
    (cfg : Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser)
    (h_lay : Miri.Interpreter.localMemoryLayout lay =
      ⟨Miri.ABI.Size.ofBytes 8, Miri.ABI.Align.EIGHT,
        .Scalar (.Initialized (value := .Int .I64 false) (validRange := vr)),
        some lay.ty⟩)
    (h_aln : mplace.misaligned = none)
    (h_ga :
      Miri.Memory.AllocationAccess.getPtrAlloc st.machine.memory
          ⟨st.machine, none⟩ ⟨Miri.ABI.Size.ofBytes 8⟩ mplace.ptr
          (Miri.ABI.Size.ofBytes 8) ghost none
          cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg) =
        ⟨mem1, ⟨st.machine, none⟩,
          some ⟨aid, Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 8),
            alloc⟩,
          .ok (some ⟨aid, Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 8),
            alloc⟩)⟩)
    (h_sub : (Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 8)).subrange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) =
      .ok (Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 8)))
    (h_rd : alloc.readScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 8)) false = .ok sc) :
    Miri.Interpreter.readImmediate st.machine.memory ⟨st.machine, none⟩
        (.indirect mplace) (Miri.Interpreter.localMemoryLayout lay)
        refRuntimeLayoutV2 ghost none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      ⟨mem1, ⟨st.machine, none⟩,
        some ⟨aid, Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 8), alloc⟩,
        .ok ⟨.scalar sc, Miri.Interpreter.localMemoryLayout lay⟩⟩ := by
  let rng := Miri.Memory.allocRange off (Miri.ABI.Size.ofBytes 8)
  let mplaceTy : Miri.Interpreter.MemoryOperandPlace Miri.Memory.Provenance :=
    ⟨mplace, ⟨Miri.ABI.Size.ofBytes 8, Miri.ABI.Align.EIGHT,
      .Scalar (.Initialized (value := .Int .I64 false) (validRange := vr)),
      some lay.ty⟩⟩
  have h_gpl := getPlaceAlloc_sized_of_access_v2' st.machine.memory mem1
    ⟨st.machine, none⟩ mplaceTy ghost none cfg.globalHooks
    (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout
    ⟨aid, rng, alloc⟩ rfl h_aln h_ga
  have h_raw_m :
      Miri.Interpreter.readImmediateFromMplaceRaw st.machine.memory
        ⟨st.machine, none⟩ mplaceTy refRuntimeLayoutV2 ghost none
        cfg.globalHooks (Miri.Interpreter.PlaceMachine.accessHooks cfg)
        cfg.dynamicLayout =
      ⟨mem1, ⟨st.machine, none⟩, some ⟨aid, rng, alloc⟩,
        .ok (some ⟨.scalar sc, mplaceTy.layout⟩)⟩ := by
    dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run,
      bind, Bind.bind, pure, Pure.pure]
    rw [h_gpl]
    dsimp only [mplaceTy, Miri.ABI.BackendRepr.isUnsized]
    simp only [Bool.false_eq_true, ite_false]
    change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
      (Except.bind
        (Except.mapError Miri.Interpreter.MemoryOperandError.memoryRange
          (rng.subrange (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (Miri.ABI.Size.ofBytes 8))))
        (fun range =>
          Except.mapError Miri.Interpreter.MemoryOperandError.allocation
            (alloc.readScalar refRuntimeLayoutV2.base range false))) _ _ = _
    rw [h_sub]
    dsimp only [Except.mapError, Except.bind]
    rw [h_rd]
  rw [h_lay]
  dsimp only [Miri.Interpreter.readImmediate, Miri.Interpreter.readImmediateRaw,
    Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [h_raw_m]
  rfl

/-- `PlaceMachine.readImmediate` of a memory operand from its raw result. -/
theorem placeReadImmediate_indirect_v2 (types : List MirTy)
    (mp : Miri.Interpreter.MemPlace Miri.Memory.Provenance)
    (lay : Miri.Interpreter.LocalLayout) (st : RefMiriState)
    (mem1 : RefMiriMem)
    (ref? : Option (Miri.Memory.AllocationAccessRef Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree))
    (imm : Miri.Interpreter.Immediate Miri.Memory.Provenance)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_res : Miri.Interpreter.readImmediate st.machine.memory
        ⟨st.machine, none⟩ (.indirect mp)
        (Miri.Interpreter.localMemoryLayout lay)
        (refAccessConfigV2 types).runtime (refAccessConfigV2 types).ghostMode
        (refAccessConfigV2 types).globalKind
        (refAccessConfigV2 types).globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 types))
        (refAccessConfigV2 types).dynamicLayout =
      ⟨mem1, ⟨st.machine, none⟩, ref?,
        .ok ⟨imm, Miri.Interpreter.localMemoryLayout lay⟩⟩) :
    Miri.Interpreter.PlaceMachine.readImmediate (refAccessConfigV2 types)
        ⟨.indirect mp, lay⟩ st =
      .ok ⟨imm, lay⟩
        { st with machine := { st.machine with memory := mem1 } } := by
  cases st with | mk sk mc => cases mc with | mk m b d t r a u pmd =>
  dsimp only at h_pmd h_res
  subst h_pmd
  unfold Miri.Interpreter.PlaceMachine.readImmediate
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
    EStateM.set, Miri.Interpreter.PlaceMachine.takePendingMoveDeinit,
    Miri.Interpreter.MachineHooks.takeLastPendingMoveDeinit]
  rw [h_res]
  rfl

section C1ValidityChild

open Miri.ABI Miri.Memory Miri.Memory.Validity Miri.Interpreter
open Miri.Interpreter.ValidityVisitor

variable {P S C E F A Pad : Type}

/-- Public mirror of one tracked-pointee visit of
`ValidityVisitor.validatePlace`. -/
def refValidateChildMirror [PointerProvenance P] [DecidableEq P]
    (h : Hooks P S C E F A Pad) (c : C) (fuel : Nat) (key : Key P)
    (path : ValidationPath) : M S Unit :=
  h.withGhostValidation
    (let child : RuntimePlace P := ⟨.memory key.mplace, key.layout⟩
     Bind.bind
       (visit h c fuel
         { path, flags := ⟨false, true⟩, ctfeMode := none,
           refTracking := none, dataBytes := none } child)
       (fun visited => refResetPaddingMirror h c visited child))

end C1ValidityChild

/-- The mirrored worklist with exactly one pending tracked pointee. -/
theorem refValidatePost_child_v2 (types : List MirTy)
    (sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (st st' : RefMiriState)
    (key : Miri.Interpreter.ValidityVisitor.Key Miri.Memory.Provenance)
    (path : Miri.Memory.ValidationPath)
    (tracking : Miri.Memory.Validity.RefTracking
      (Miri.Interpreter.ValidityVisitor.Key Miri.Memory.Provenance)
      Miri.Memory.ValidationPath)
    (h_next : sess.refTracking.bind Miri.Memory.Validity.RefTracking.next =
      some ((key, path), tracking))
    (h_child : refValidateChildMirror (refValHooksV2 types) 0 16 key path st =
      .ok () st')
    (h_next2 : (some tracking).bind Miri.Memory.Validity.RefTracking.next =
      none) :
    refValidatePostMirror (refValHooksV2 types) 0 16 true sess st =
      .ok () st' := by
  dsimp only [refValidatePostMirror, bind, Bind.bind, pure, Pure.pure]
  rw [ite_true_eq, eStateM_loop_forIn_eq st]
  dsimp only [bind, Bind.bind, pure, Pure.pure, ite_true_eq]
  rw [h_next]
  dsimp only
  rw [show (16 == 0) = false from rfl, ite_false_eq]
  change EStateM.bind (EStateM.bind (EStateM.bind
    (refValidateChildMirror (refValHooksV2 types) 0 16 key path) _) _) _ st = _
  rw [eStateM_bind3_ok h_child]
  rw [eStateM_bind2_ok (show (EStateM.pure _ :
      EStateM Miri.Interpreter.StepError RefMiriState _) st' = _ from rfl)]
  dsimp only
  rw [eStateM_loop_forIn_eq st']
  dsimp only [bind, Bind.bind, pure, Pure.pure, ite_true_eq]
  rw [h_next2]
  dsimp only
  rw [eStateM_bind_pure_fn]
  dsimp only
  rw [eStateM_loop_forIn_eq st', ite_false_eq]
  rfl

/-- Reading back `2usize` from an 8-byte range buffer. -/
theorem c1f_read8 :
    (c1A8.withExtra (c1Tree 8)).readScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
      false = .ok (c1Usize 2) :=
  (Miri.Memory.Allocation.readScalar_int_of_bytes (c1A8.withExtra (c1Tree 8))
    refRuntimeLayoutV2.base _ (Array.mk [2, 0, 0, 0, 0, 0, 0, 0]) rfl rfl
    (by decide) (.inr rfl)).trans rfl

/-- Runtime place of local `i` with layout `lay` in `V2_C1`. -/
noncomputable abbrev c1Local (i : Nat) (lay : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
  ⟨.local 0 i none (c1Frame 0 0 []).localsIdentity, lay⟩

/-- Immediate slice-argument operand `s` passed to `slice::get_unchecked`. -/
noncomputable abbrev c1OpS :
    Miri.Interpreter.OpTy Miri.Memory.Provenance :=
  ⟨.immediate (c1Slice 0 5), c1Sl⟩

/-- Indirect range-argument operand living in stack allocation `id`. -/
noncomputable abbrev c1OpM (id : Miri.Memory.AllocId)
    (lay : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.OpTy Miri.Memory.Provenance :=
  ⟨.indirect (c1Mp id), lay⟩

/-- Read `2usize` from the force-allocated range buffer `aid` in `st`. -/
theorem c1f_rdRange (aid : Miri.Memory.AllocId)
    (lay : Miri.Interpreter.LocalLayout) (st : RefMiriState)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_dr : st.machine.dataRace = none)
    (h_bt : st.machine.borrowTracker = none)
    (h_lay : Miri.Interpreter.localMemoryLayout lay =
      ⟨Miri.ABI.Size.ofBytes 8, Miri.ABI.Align.EIGHT,
        .Scalar (.Initialized (value := .Int .I64 false)
          (validRange := refFullWrappingRangeSize (Miri.ABI.Size.ofBytes 8))),
        some lay.ty⟩)
    (h_find : st.machine.memory.live.find? (fun e => e.1 == aid) =
      some (aid, ⟨.stack, c1A8.withExtra (c1Tree 8)⟩))
    (h_any : (st.machine.memory.live.any fun e => e.1 == aid) = true)
    (h_set : st.machine.memory.setLiveAllocation aid
      (c1A8.withExtra (c1Tree 8)) = .ok st.machine.memory) :
    Miri.Interpreter.PlaceMachine.readImmediate
        (refAccessConfigV2 c1Rp.types) (c1OpM aid lay) st =
      .ok ⟨.scalar (c1Usize 2), lay⟩ st :=
  have h_ga := getPtrAlloc_live_nonghost_v2 c1Rp.types (Miri.ABI.Size.ofBytes 8)
    8 st.machine.memory st.machine.memory .stack (c1A8.withExtra (c1Tree 8))
    st.machine aid Miri.ABI.Size.ZERO (c1Mp aid).ptr
    (.concrete Miri.Memory.BorTag.one) h_find h_any h_set rfl rfl rfl rfl
    h_dr h_bt
  placeReadImmediate_indirect_v2 c1Rp.types (c1Mp aid) lay st
    st.machine.memory _ _ h_pmd
    (readImmediate_mem_u64_v2 lay _ (c1Mp aid) aid _ (c1Usize 2) st
      st.machine.memory Miri.ABI.Size.ZERO false (refAccessConfigV2 c1Rp.types)
      h_lay rfl h_ga rfl c1f_read8)

/-- Validation key of the `[u8]` pointee `alloc2[off .. off + len]`. -/
noncomputable def c1Key (off : UInt64) (len : Nat) :
    Miri.Interpreter.ValidityVisitor.Key Miri.Memory.Provenance :=
  ⟨⟨⟨Miri.ABI.Size.ofBytes off,
      some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩,
      .metadata (c1Usize len), none⟩,
    refLocalLayoutForTyV2 c1Rp.types (.slice u8Ty)⟩

/-- Deref validation path used when checking `&[u8]` pointees. -/
noncomputable def c1Path : Miri.Memory.ValidationPath :=
  ⟨"", Array.mk [.deref]⟩

/-- Root validation session of a `&[u8]` immediate local. -/
noncomputable def c1Sess (off : UInt64) (len : Nat) :
    Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance :=
  { path := ⟨"", Array.empty⟩, flags := ⟨true, false⟩, ctfeMode := none
    refTracking := some (Miri.Memory.Validity.RefTracking.empty.track
      (c1Key off len) (fun _ => c1Path))
    dataBytes := none }

/-- Popping the singleton worklist produced by `RefTracking.track`. -/
theorem c1f_track_next
    (key : Miri.Interpreter.ValidityVisitor.Key Miri.Memory.Provenance)
    (path : Miri.Memory.ValidationPath) :
    (some (Miri.Memory.Validity.RefTracking.empty.track key
      (fun _ => path))).bind Miri.Memory.Validity.RefTracking.next =
      some ((key, path), ⟨Array.mk [key], Array.empty⟩) := by
  rw [Miri.Memory.Validity.RefTracking.track, ← Array.any_toList]
  rfl

/-- Validation of a place whose root visit tracks exactly one `[u8]` pointee
inside caller `alloc2`. -/
theorem c1f_validate_slice
    (dp : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance)
    (st : RefMiriState) (off : UInt64) (len : Nat)
    (h_pre : refValidatePreMirror (refValHooksV2 c1Rp.types) 0 16 dp true true
      st = .ok (c1Sess off len) st)
    (h_child : refValidateChildMirror (refValHooksV2 c1Rp.types) 0 16
      (c1Key off len) c1Path st = .ok () st) :
    Miri.Interpreter.ValidityVisitor.validatePlace (refValHooksV2 c1Rp.types)
      0 16 dp true true st = .ok () st := by
  rw [refValidatePlace_split_v2]
  exact eStateM_apply_bind _ _ (c1Sess off len) st st h_pre
    (refValidatePost_child_v2 c1Rp.types (c1Sess off len) st st
      (c1Key off len) c1Path _ (c1f_track_next _ _) h_child rfl)

/-- Write and validate a `&[u8]` wide reference into local `i`. -/
theorem c1f_wrSlice (i : Nat) (off : UInt64) (len : Nat)
    (stPre stPost : RefMiriState)
    (h_run : Miri.Interpreter.writePlaceImmediate
        (refPlaceProjectionHooksV2 c1Rp.types).place 0 (c1Slice off len)
        (c1Local i c1Sl) stPre =
      Miri.Interpreter.ValidityVisitor.validatePlace
        (refValHooksV2 c1Rp.types) 0 16 (c1Local i c1Sl) true true stPost)
    (h_pre : refValidatePreMirror (refValHooksV2 c1Rp.types) 0 16
      (c1Local i c1Sl) true true stPost = .ok (c1Sess off len) stPost)
    (h_child : refValidateChildMirror (refValHooksV2 c1Rp.types) 0 16
      (c1Key off len) c1Path stPost = .ok () stPost) :
    Miri.Interpreter.writePlaceImmediate
        (refPlaceProjectionHooksV2 c1Rp.types).place 0 (c1Slice off len)
        (c1Local i c1Sl) stPre = .ok () stPost := by
  rw [h_run]
  exact c1f_validate_slice (c1Local i c1Sl) stPost off len h_pre h_child

/-- The `terminator` step hook on a `Call` terminator, from the result of
`Call.evalCallTerminator`. -/
theorem c1f_term_ok (si : Miri.MIR.SourceInfo) (func : Miri.MIR.Operand)
    (args : Array Miri.MIR.SpannedOperand) (dest : Miri.MIR.Place)
    (target : Nat) (unwind : Miri.MIR.UnwindAction)
    (x : Miri.MIR.CallSource) (y : Miri.MIR.SpanRef)
    (st st' : RefMiriState)
    (h : Miri.Interpreter.Call.evalCallTerminator c1Calls 0
      refLimitsV2.callDispatch
      ⟨si, .Call func args dest (some target) unwind x y⟩ st = .ok () st')
    (h_prog : (st'.stack.frames.size == st.stack.frames.size &&
      st'.stack.currentFrame?.map Miri.Interpreter.Frame.location ==
        st.stack.currentFrame?.map Miri.Interpreter.Frame.location) =
      false) :
    (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfigV2 c1Rp)
      refLimitsV2).terminator 0
      ⟨si, .Call func args dest (some target) unwind x y⟩ st =
      (st', .ok ()) := by
  have h_run : Miri.Interpreter.MachineHooks.run
      (Miri.Interpreter.Call.evalCallTerminator c1Calls 0
        refLimitsV2.callDispatch
        ⟨si, .Call func args dest (some target) unwind x y⟩) st =
      (st', .ok ()) := by
    dsimp only [Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
    rw [h]
  change (match Miri.Interpreter.MachineHooks.run
      (Miri.Interpreter.Call.evalCallTerminator c1Calls 0
        refLimitsV2.callDispatch
        ⟨si, .Call func args dest (some target) unwind x y⟩) st with
    | (state, result) =>
      match result with
      | Except.error error => (state, Except.error error)
      | Except.ok () =>
        if ((some target).isSome &&
            state.stack.frames.size == st.stack.frames.size &&
            state.stack.currentFrame?.map Miri.Interpreter.Frame.location ==
              st.stack.currentFrame?.map Miri.Interpreter.Frame.location) =
            true then
          (state, Except.error (Miri.Interpreter.StepError.invalidProgram
            "evaluating this call made no progress"))
        else (state, Except.ok ())) = _
  rw [h_run]
  simp only [Option.isSome, Bool.true_and, h_prog, Bool.false_eq_true,
    ite_false]

/-! ### Call steps (`bb0`, `bb1`, `bb2`) -/

/-- Locals of `V2_C1` at `bb0` call before writing `_3`. -/
noncomputable def c1L1 := c1Locals c1Two c1U (c1M alloc3IdV2) c1U c1U c1U
/-- Locals of `V2_C1` after `_3 = get_unchecked(_1, ..2)`. -/
noncomputable def c1L2 := c1Locals c1Two (c1I (c1Slice 0 2)) (c1M alloc3IdV2)
  c1U c1U c1U
/-- Post-`beforeTerminator` state at `(bb0, 1)`. -/
noncomputable def c1T0 := c1StS 0 1 c1L1 c1Mem1 (c1Ctrl 1) c1Spans1
/-- Post-write intermediate state of Call 1 (`_3` updated, still at `bb0`). -/
noncomputable def c1W0 := c1StS 0 1 c1L2 c1Mem1 (c1Ctrl 1) c1Spans1

/-- Locals of `V2_C1` at `bb1` call before writing `_5`. -/
noncomputable def c1L3 := c1Locals c1U (c1I (c1Slice 0 2)) (c1M alloc3IdV2)
  c1U (c1M alloc4IdV2) c1U
/-- Locals of `V2_C1` after `_5 = get_unchecked(_1, 2..)`. -/
noncomputable def c1L4 := c1Locals c1U (c1I (c1Slice 0 2)) (c1M alloc3IdV2)
  (c1I (c1Slice 2 3)) (c1M alloc4IdV2) c1U
/-- Post-`beforeTerminator` state at `(bb1, 1)`. -/
noncomputable def c1T1 := c1StS 1 1 c1L3 c1Mem2 (c1Ctrl 2) c1Spans2
/-- Post-write intermediate state of Call 2 (`_5` updated, still at `bb1`). -/
noncomputable def c1W1 := c1StS 1 1 c1L4 c1Mem2 (c1Ctrl 2) c1Spans2

/-- Shared proof for Call 1 (`bb0`, `RangeTo`) and Call 2 (`bb1`, `RangeFrom`).
-/
theorem c1f_callRange (bb : Nat) (h_lt : bb < 4) (isRangeTo : Bool)
    (aid : Miri.Memory.AllocId) (rLay : Miri.Interpreter.LocalLayout)
    (dst : Nat) (off : UInt64) (len : Nat)
    (stMid stW st' : RefMiriState)
    (h_rd : Miri.Interpreter.PlaceMachine.readImmediate
        (refAccessConfigV2 c1Rp.types) (c1OpM aid rLay) stMid =
      .ok ⟨.scalar (c1Usize 2), rLay⟩ stMid)
    (h_wr : Miri.Interpreter.writePlaceImmediate
        (refPlaceProjectionHooksV2 c1Rp.types).place 0 (c1Slice off len)
        (c1Local dst c1Sl) stMid = .ok () stW)
    (h_case :
      (bb = 0 ∧ isRangeTo = true ∧ aid = alloc3IdV2 ∧ rLay = c1RTo ∧
        dst = 3 ∧ off = 0 ∧ len = 2 ∧ stMid = c1T0 ∧ stW = c1W0 ∧
        st' = c1S_bb1_0) ∨
      (bb = 1 ∧ isRangeTo = false ∧ aid = alloc4IdV2 ∧ rLay = c1RFrom ∧
        dst = 5 ∧ off = 2 ∧ len = 3 ∧ stMid = c1T1 ∧ stW = c1W1 ∧
        st' = c1S_bb2_0)) :
    Miri.Interpreter.Call.evalCallTerminator c1Calls 0
        refLimitsV2.callDispatch (c1Block bb h_lt).terminator stMid =
      .ok () st' := by
  have h_exec : refExecSliceGetUncheckedV2 c1Rp.types isRangeTo
      (Array.mk [c1OpS, c1OpM aid rLay]) (c1Local dst c1Sl) stMid =
      .ok .NeedsReturn stW := by
    cases h_case with
    | inl h0 =>
      let ⟨hbb, hrt, haid, hrl, hdst, hoff, hlen, hmid, hw, _⟩ := h0
      subst hbb; subst hrt; subst haid; subst hrl; subst hdst
      subst hoff; subst hlen; subst hmid; subst hw
      unfold refExecSliceGetUncheckedV2
      dsimp only
      change (match Miri.Interpreter.PlaceMachine.readImmediate
          (refAccessConfigV2 c1Rp.types) (c1OpM alloc3IdV2 c1RTo) c1T0 with
        | EStateM.Result.error e st1 => EStateM.Result.error e st1
        | EStateM.Result.ok imm1 st2 => _) = _
      rw [h_rd]
      dsimp only
      change (match Miri.Interpreter.writePlaceImmediate
          (refPlaceProjectionHooksV2 c1Rp.types).place 0 (c1Slice 0 2)
          (c1Local 3 c1Sl) c1T0 with
        | EStateM.Result.error e st3 => EStateM.Result.error e st3
        | EStateM.Result.ok () st3 =>
          EStateM.Result.ok Miri.Interpreter.ForeignItems.EmulateItemResult.NeedsReturn st3) = _
      rw [h_wr]
    | inr h1 =>
      let ⟨hbb, hrt, haid, hrl, hdst, hoff, hlen, hmid, hw, _⟩ := h1
      subst hbb; subst hrt; subst haid; subst hrl; subst hdst
      subst hoff; subst hlen; subst hmid; subst hw
      unfold refExecSliceGetUncheckedV2
      dsimp only
      change (match Miri.Interpreter.PlaceMachine.readImmediate
          (refAccessConfigV2 c1Rp.types) (c1OpM alloc4IdV2 c1RFrom) c1T1 with
        | EStateM.Result.error e st1 => EStateM.Result.error e st1
        | EStateM.Result.ok imm1 st2 => _) = _
      rw [h_rd]
      dsimp only
      change (match Miri.Interpreter.writePlaceImmediate
          (refPlaceProjectionHooksV2 c1Rp.types).place 0 (c1Slice 2 3)
          (c1Local 5 c1Sl) c1T1 with
        | EStateM.Result.error e st3 => EStateM.Result.error e st3
        | EStateM.Result.ok () st3 =>
          EStateM.Result.ok Miri.Interpreter.ForeignItems.EmulateItemResult.NeedsReturn st3) = _
      rw [h_wr]
  cases h_case with
  | inl h0 =>
    let ⟨hbb, hrt, haid, hrl, hdst, hoff, hlen, hmid, hw, hst⟩ := h0
    subst hbb; subst hrt; subst haid; subst hrl; subst hdst
    subst hoff; subst hlen; subst hmid; subst hw; subst hst
    change EStateM.bind (Miri.Interpreter.Call.evalCalleeAndArgs c1Calls 0
      _ _ _) _ _ = _
    unfold Miri.Interpreter.Call.evalCalleeAndArgs
    simp only [← Array.any_toList, Std.Legacy.Range.forIn_eq_forIn_range']
    change EStateM.bind (Miri.Interpreter.Call.initFnCall c1Calls 0 _ _) _ _ = _
    refine (eStateM_bind_ok (c1f_initFnCall _ 1 _ _ c1OpS
      (c1OpM alloc3IdV2 c1RTo) (Array.mk [c1OpS, c1OpM alloc3IdV2 c1RTo])
      _ _ _ c1T0 c1W0 c1S_bb1_0 (.inr (.inl rfl))
      (.inl ⟨rfl, rfl⟩) ?_ rfl)).trans rfl
    exact h_exec
  | inr h1 =>
    let ⟨hbb, hrt, haid, hrl, hdst, hoff, hlen, hmid, hw, hst⟩ := h1
    subst hbb; subst hrt; subst haid; subst hrl; subst hdst
    subst hoff; subst hlen; subst hmid; subst hw; subst hst
    change EStateM.bind (Miri.Interpreter.Call.evalCalleeAndArgs c1Calls 0
      _ _ _) _ _ = _
    unfold Miri.Interpreter.Call.evalCalleeAndArgs
    simp only [← Array.any_toList, Std.Legacy.Range.forIn_eq_forIn_range']
    change EStateM.bind (Miri.Interpreter.Call.initFnCall c1Calls 0 _ _) _ _ = _
    refine (eStateM_bind_ok (c1f_initFnCall _ 2 _ _ c1OpS
      (c1OpM alloc4IdV2 c1RFrom) (Array.mk [c1OpS, c1OpM alloc4IdV2 c1RFrom])
      _ _ _ c1T1 c1W1 c1S_bb2_0 (.inr (.inr rfl))
      (.inl ⟨rfl, rfl⟩) ?_ rfl)).trans rfl
    exact h_exec

/-- Step 1: `_3 = slice_get_unchecked_range_to(copy _1, copy _4)`. -/
theorem c1_step_1 :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 c1Rp)
        refLimitsV2 0 c1S_bb0_1 = (c1S_bb1_0, .ok true) :=
  execStep_term_ok c1Rp c1S_bb0_1 c1T0 c1S_bb1_0
    (c1Frame 0 1 c1L1) 0 1 (c1Block 0) rfl rfl rfl rfl rfl rfl
    (c1f_term_ok _ _ _ _ _ _ _ _ c1T0 c1S_bb1_0
      (c1f_callRange 0 (by decide) true alloc3IdV2 c1RTo 3 0 2 c1T0 c1W0
        c1S_bb1_0
        (c1f_rdRange alloc3IdV2 c1RTo c1T0 rfl rfl rfl rfl rfl
          (by rw [← Array.any_toList]; rfl) rfl)
        (c1f_wrSlice 3 0 2 c1T0 c1W0 rfl rfl rfl)
        (.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)) rfl)

/-- Step 3: `_5 = slice_get_unchecked_range_from(copy _1, copy _6)`. -/
theorem c1_step_3 :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 c1Rp)
        refLimitsV2 0 c1S_bb1_1 = (c1S_bb2_0, .ok true) :=
  execStep_term_ok c1Rp c1S_bb1_1 c1T1 c1S_bb2_0
    (c1Frame 1 1 c1L3) 1 1 (c1Block 1) rfl rfl rfl rfl rfl rfl
    (c1f_term_ok _ _ _ _ _ _ _ _ c1T1 c1S_bb2_0
      (c1f_callRange 1 (by decide) false alloc4IdV2 c1RFrom 5 2 3 c1T1 c1W1
        c1S_bb2_0
        (c1f_rdRange alloc4IdV2 c1RFrom c1T1 rfl rfl rfl rfl rfl
          (by rw [← Array.any_toList]; rfl) rfl)
        (c1f_wrSlice 5 2 3 c1T1 c1W1 rfl rfl rfl)
        (.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)) rfl)

/-! ### Call 3 (`bb2`): `_7 = slice_len(move _3)` -/

/-- Locals of `V2_C1` at `bb2` after moving `_3`. -/
noncomputable def c1L5 := c1Locals c1U c1U (c1M alloc3IdV2)
  (c1I (c1Slice 2 3)) (c1M alloc4IdV2) c1U
/-- Locals of `V2_C1` after writing `_7 = 2usize`. -/
noncomputable def c1L6 := c1Locals c1U c1U (c1M alloc3IdV2)
  (c1I (c1Slice 2 3)) (c1M alloc4IdV2) c1Two
/-- Post-`beforeTerminator` state at `(bb2, 0)`. -/
noncomputable def c1T2 := c1StS 2 0 c1L4 c1Mem2 (c1Ctrl 3) c1Spans2
/-- State at `(bb2, 0)` after `evalCalleeAndArgs` moves `_3`. -/
noncomputable def c1T2' := c1StS 2 0 c1L5 c1Mem2 (c1Ctrl 3) c1Spans2
/-- Post-write intermediate state of Call 3 (`_7` updated, still at `bb2`). -/
noncomputable def c1W2 := c1StS 2 0 c1L6 c1Mem2 (c1Ctrl 3) c1Spans2

/-- Step 4: `_7 = slice_len(move _3)`. -/
theorem c1_step_4 :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 c1Rp)
        refLimitsV2 0 c1S_bb2_0 = (c1S_bb3, .ok true) := by
  have h_wr : Miri.Interpreter.writePlaceImmediate
      (refPlaceProjectionHooksV2 c1Rp.types).place 0 (.scalar (c1Usize 2))
      (c1Local 7 c1Us) c1T2' = .ok () c1W2 := by
    have h_run : Miri.Interpreter.writePlaceImmediate
        (refPlaceProjectionHooksV2 c1Rp.types).place 0 (.scalar (c1Usize 2))
        (c1Local 7 c1Us) c1T2' =
      Miri.Interpreter.ValidityVisitor.validatePlace (refValHooksV2 c1Rp.types)
        0 16 (c1Local 7 c1Us) true true c1W2 := rfl
    rw [h_run]
    exact refValidatePlace_of_pre_v2 c1Rp.types (c1Local 7 c1Us) c1W2 c1W2
      { path := ⟨"", Array.empty⟩, flags := ⟨true, false⟩, ctfeMode := none,
        refTracking := some .empty, dataBytes := none } rfl rfl
  have h_exec : refExecSliceLenV2 c1Rp.types
      (Array.mk [⟨.immediate (c1Slice 0 2), c1Sl⟩]) (c1Local 7 c1Us) c1T2' =
      .ok .NeedsReturn c1W2 := by
    unfold refExecSliceLenV2
    dsimp only
    change (match Miri.Interpreter.writePlaceImmediate
        (refPlaceProjectionHooksV2 c1Rp.types).place 0
        (.scalar (c1Usize 2)) (c1Local 7 c1Us) c1T2' with
      | EStateM.Result.error e st2 => EStateM.Result.error e st2
      | EStateM.Result.ok () st2 =>
        EStateM.Result.ok
          Miri.Interpreter.ForeignItems.EmulateItemResult.NeedsReturn st2) = _
    rw [h_wr]
  have h_call : Miri.Interpreter.Call.evalCallTerminator c1Calls 0
      refLimitsV2.callDispatch (c1Block 2).terminator c1T2 =
      .ok () c1S_bb3 := by
    change EStateM.bind (Miri.Interpreter.Call.evalCalleeAndArgs c1Calls 0
      _ _ _) _ _ = _
    unfold Miri.Interpreter.Call.evalCalleeAndArgs
      Miri.Interpreter.Call.moveDefinitelyDisjoint
    simp only [← Array.any_toList, ← Array.contains_toList,
      Std.Legacy.Range.forIn_eq_forIn_range']
    change EStateM.bind (Miri.Interpreter.Call.initFnCall c1Calls 0 _ _) _ _ = _
    refine (eStateM_bind_ok (c1f_initFnCall _ 0 _ _
      ⟨.immediate (c1Slice 0 2), c1Sl⟩ ⟨.immediate (c1Slice 0 2), c1Sl⟩
      (Array.mk [⟨.immediate (c1Slice 0 2), c1Sl⟩]) _ _ _
      c1T2' c1W2 c1S_bb3 (.inl rfl) (.inr ⟨rfl, rfl⟩) ?_ rfl)).trans rfl
    exact h_exec
  exact execStep_term_ok c1Rp c1S_bb2_0 c1T2 c1S_bb3
    (c1Frame 2 0 c1L4) 2 0 (c1Block 2) rfl rfl rfl rfl rfl rfl
    (c1f_term_ok _ _ _ _ _ _ _ _ c1T2 c1S_bb3 h_call rfl)

/-! ## Section 4: `V2_C1` aggregate statements (`RangeTo` / `RangeFrom`) -/

/-- Projection place-hooks abbreviation for `V2_C1`. -/
noncomputable abbrev c1gPlace :=
  (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfgV2 c1Rp)).place
/-- Byte range `[0, 8)` for 8-byte stack range buffers. -/
noncomputable abbrev c1gRng8 : Miri.Memory.AllocRange :=
  Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
/-- Runtime operand carrying the immediate `2usize`. -/
noncomputable abbrev c1gOp2 : Miri.Interpreter.OpTy Miri.Memory.Provenance :=
  ⟨.immediate (.scalar (c1Usize 2)), c1Us⟩
/-- Initialized 8-byte stack allocation `c1A8` with fresh BorrowTree. -/
noncomputable abbrev c1gA8E := c1A8.withExtra (c1Tree 8)

/-- Keyed arrays with equal ordered rows are equal. -/
theorem c1g_keyedExt {K V : Type} [BEq K] [Hashable K] {f : V → K}
    (a b : Miri.Memory.KeyedArray K V f) (h : a.toArray = b.toArray) :
    a = b := by
  cases a with
  | _ ka ra ia ea aa ma =>
    cases b with
    | _ kb rb ib eb ab mb =>
      have h' : ra = rb := h
      subst h' ma mb ea eb
      rfl

/-- Exact `reserveAllocId` successor of a `c1Mem` state. -/
theorem c1g_reserve_exact (next : UInt64) (live : Array C1Row)
    (issued : Array Miri.Memory.AllocId) (mem1 : RefMiriMem)
    (aid : Miri.Memory.AllocId)
    (h_res : (c1Mem next live issued).reserveAllocId = (mem1, .ok aid)) :
    mem1 = c1Mem (next + 1) live (issued.push aid) := by
  dsimp only [Miri.Memory.MemoryState.reserveAllocId, Id.run, bind, Bind.bind,
    pure, Pure.pure] at h_res
  have h1 := ite_pair_error_eq_ok _ _ _ _ _ _ h_res
  have h2 := ite_pair_error_eq_ok _ _ _ _ _ _ h1
  cases h_al : Miri.Memory.AllocId.ofUInt64 (c1Mem next live issued).nextAllocId
  with
  | none => rw [h_al] at h2; cases h2
  | some id =>
    rw [h_al] at h2; have h3 := ite_pair_error_eq_ok _ _ _ _ _ _ h2
    simp only [show (c1Mem next live issued).sourceAllocIdWorldActive = false
      from rfl, Bool.false_eq_true, ite_false] at h3
    injection h3 with h_m h_ok; injection h_ok with h_id; rw [← h_m, ← h_id]
    dsimp only [c1Mem, Miri.Memory.MemoryState.setIssuedIds,
      Miri.Memory.MemoryState.empty]
    have h_k : ((Miri.Memory.KeyedArray.ofArray
        (fun (x : Miri.Memory.AllocId) => x.value) issued).push id) =
        Miri.Memory.KeyedArray.ofArray _ (issued.push id) :=
      c1g_keyedExt _ _ rfl
    rw [h_k]

/-- Concrete uninitialized 8-byte stack allocation created by `tryNew`. -/
theorem c1g_blank8 :
    Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
      (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok c1Blank8 :=
  tryNew_eq_of_image_v2 (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT 8 _ _
    rfl rfl (by decide) (exceptOkGet_eq _ rfl) rfl

/-- Live row of a fresh (uninitialized) 8-byte stack buffer `id`. -/
noncomputable def c1gBlank (id : Miri.Memory.AllocId) : C1Row :=
  (id, ⟨.stack, c1Blank8.withExtra (c1Tree 8)⟩)

/-- Stack allocation of an 8-byte range local on a `c1Mem`-shaped memory. -/
theorem c1g_allocStack8 (st : RefMiriState) (lay : Miri.Interpreter.LocalLayout)
    (next : UInt64) (live : Array C1Row) (issued : Array Miri.Memory.AllocId)
    (h_nz : next ≠ 0) (h_mem : st.machine.memory = c1Mem next live issued)
    (h_lay : lay.layout = refRangeUsizeLayoutDataV2)
    (h_bt : st.machine.borrowTracker = none) (h_dr : st.machine.dataRace = none)
    (h_iss : (issued.toList.all fun id =>
      decide (id.value.toNat < next.toNat)) = true)
    (h_lv : (live.toList.all fun r =>
      decide (r.1.value.toNat < next.toNat)) = true) :
    c1gPlace.allocateStack 0 lay st = .ok ⟨c1Mp ⟨next, h_nz⟩, lay⟩
      { st with machine := { st.machine with
          memory := c1Mem (next + 1) (live.push (c1gBlank ⟨next, h_nz⟩))
            (issued.push ⟨next, h_nz⟩) } } := by
  cases st with | mk sk mc => cases mc with | mk m b d t r a u pmd =>
    dsimp only at h_mem h_bt h_dr; subst h_mem h_bt h_dr
    let ⟨mem1, h_res, h_as⟩ := allocateStack_sized_v2 c1Rp
      ⟨sk, ⟨c1Mem next live issued, none, none, t, r, a, u, pmd⟩⟩ lay
      ⟨next, h_nz⟩ c1Blank8 (by rw [h_lay]; rfl) (by rw [h_lay]; decide)
      (by rw [h_lay]; exact c1g_blank8) (by rw [h_lay]; rfl) rfl rfl rfl h_nz
      (fun h => by cases h) (fun h => by cases h)
      (fun _ h => of_decide_eq_true (List.all_eq_true.mp h_iss _
        (Array.mem_def.mp h)))
      (fun _ h => of_decide_eq_true (List.all_eq_true.mp h_lv _
        (Array.mem_def.mp h)))
      (fun _ h => absurd h (Array.not_mem_empty _))
      (fun _ h => absurd h (Array.not_mem_empty _)) rfl
    rw [c1g_reserve_exact next live issued mem1 ⟨next, h_nz⟩ h_res] at h_as
    rw [h_as, show lay.layout.size = Miri.ABI.Size.ofBytes 8 from by
      rw [h_lay]; rfl]; rfl

/-- `afterLocalMovedToMemory` only records the allocation span of `aid`. -/
theorem c1g_afterMoved (st : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (localId : LocalId) (aid : Miri.Memory.AllocId)
    (lay : Miri.Interpreter.LocalLayout)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none)
    (h_in : (st.machine.memory.live.toList.any fun e => e.1 == aid) = true) :
    c1gPlace.afterLocalMovedToMemory 0 localId ⟨c1Mp aid, lay⟩ st =
      .ok () { st with machine := { st.machine with allocationSpans :=
        ((st.machine.allocationSpans.filter fun e => e.1 != aid).push
          (aid, ⟨0⟩, none)) } } := by
  rw [Array.any_toList] at h_in
  change Miri.Interpreter.MachineHooks.afterLocalMovedToMemory localId
    ⟨c1Mp aid, lay⟩ (refCompilerHooksV2 c1Rp.types).localSpan st = _
  dsimp only [Miri.Interpreter.MachineHooks.afterLocalMovedToMemory, c1Mp,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [currentFrame_single_v2 st frame h_fr]; dsimp only
  rw [show (refCompilerHooksV2 c1Rp.types).localSpan frame.body localId st =
      .ok ⟨0⟩ st from rfl]
  dsimp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [h_in]; simp only [h_dr]; rfl

/-- Writing `2usize` over a fresh 8-byte stack buffer yields `c1A8`. -/
theorem c1g_w8 :
    Miri.Memory.Allocation.writeScalar refRuntimeLayoutV2.base c1gRng8
      (c1Usize 2) (c1Blank8.withExtra (c1Tree 8)) = .ok () c1gA8E := by
  change (match targetUIntBytesMirror refRuntimeLayoutV2.base
      (Miri.ABI.Size.ofBytes 8) (BitVec.ofNat 128 2) with
    | .ok _ => _ | .error _ => _) = _
  rw [show targetUIntBytesMirror refRuntimeLayoutV2.base
      (Miri.ABI.Size.ofBytes 8) (BitVec.ofNat 128 2) =
      .ok (Array.mk [2, 0, 0, 0, 0, 0, 0, 0]) from by
    dsimp only [targetUIntBytesMirror]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']; rfl]; rfl

/-- Reading back `2usize` from the 8-byte range buffer `c1A8`. -/
theorem c1g_read8 :
    c1gA8E.readScalar refRuntimeLayoutV2.base c1gRng8 false = .ok (c1Usize 2) :=
  (Miri.Memory.Allocation.readScalar_int_of_bytes c1gA8E refRuntimeLayoutV2.base
    _ (Array.mk [2, 0, 0, 0, 0, 0, 0, 0]) rfl rfl (by decide) (.inr rfl)).trans rfl

/-- Memory write of `2usize` into the fresh 8-byte stack buffer `id`. -/
theorem c1g_write (st : RefMiriState) (id : Miri.Memory.AllocId)
    (mem' : RefMiriMem)
    (h_find : st.machine.memory.live.find? (fun e => e.1 == id) =
      some (c1gBlank id))
    (h_any : (st.machine.memory.live.toList.any fun e => e.1 == id) = true)
    (h_set : st.machine.memory.setLiveAllocation id
      (c1Blank8.withExtra (c1Tree 8)) = .ok st.machine.memory)
    (h_set' : st.machine.memory.setLiveAllocation id c1gA8E = .ok mem')
    (h_dr : st.machine.dataRace = none)
    (h_bt : st.machine.borrowTracker = none) :
    c1gPlace.writeMemoryNoValidate 0 (.scalar (c1Usize 2)) ⟨c1Mp id, c1Us⟩ st =
      .ok () { st with machine := { st.machine with memory := mem' } } := by
  rw [Array.any_toList] at h_any
  exact Miri.Interpreter.PlaceMachine.writeMemory_of_result
    (refAccessConfigV2 c1Rp.types) _ _ _ _ mem' (some ⟨id, c1gRng8, c1gA8E⟩)
    rfl (writeImmediate_scalar_u64_at_poly _ _ _ _ _ _ _ 2 _ _ _ _ _ _ _ c1gA8E
      (Miri.Interpreter.getPlaceAllocMut_sized_of_access _ _ _ _
        (Miri.ABI.Size.ofBytes 8) _ _ _ _ _ rfl rfl rfl
        (getPtrAllocMut_live_nonghost_v2 c1Rp.types (Miri.ABI.Size.ofBytes 8)
          8 _ _ .stack (c1Blank8.withExtra (c1Tree 8)) st.machine id
          Miri.ABI.Size.ZERO (c1Mp id).ptr (.concrete Miri.Memory.BorTag.one)
          h_find rfl h_any h_set rfl rfl rfl rfl h_dr h_bt))
      rfl c1g_w8 h_set')

/-- Ghost validity read of `2usize` from the 8-byte range buffer `aid`. -/
theorem c1g_readImm_u64 (st : RefMiriState) (aid : Miri.Memory.AllocId)
    (h_find : st.machine.memory.live.find? (fun e => e.1 == aid) =
      some (aid, ⟨.stack, c1gA8E⟩)) :
    Miri.Interpreter.ValidityMemory.readImmediate
        (refValidityMemoryEnvV2 c1Rp.types) ⟨.indirect (c1Mp aid), c1Us⟩
        .integer st = .ok ⟨.scalar (c1Usize 2), c1Us⟩ st := by
  let cfg := refAccessConfigV2 c1Rp.types
  let mp : Miri.Interpreter.MemoryOperandPlace Miri.Memory.Provenance :=
    ⟨c1Mp aid, Miri.Interpreter.localMemoryLayout c1Us⟩
  have h_raw : Miri.Interpreter.readImmediateFromMplaceRaw st.machine.memory
      ⟨st.machine, none⟩ mp refRuntimeLayoutV2 true none cfg.globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout =
      ⟨st.machine.memory, ⟨st.machine, none⟩, some ⟨aid, c1gRng8, c1gA8E⟩,
        .ok (some ⟨.scalar (c1Usize 2), mp.layout⟩)⟩ := by
    dsimp only [Miri.Interpreter.readImmediateFromMplaceRaw, Id.run, bind,
      Bind.bind, pure, Pure.pure]
    rw [getPlaceAlloc_sized_of_access_v2' st.machine.memory st.machine.memory
      ⟨st.machine, none⟩ mp true none cfg.globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks cfg) cfg.dynamicLayout
      ⟨aid, c1gRng8, c1gA8E⟩ rfl rfl
      (getPtrAlloc_live_ghost_v2 (Miri.ABI.Size.ofBytes 8) 8 st.machine.memory
        .stack c1gA8E st.machine aid Miri.ABI.Size.ZERO (c1Mp aid).ptr
        (.concrete Miri.Memory.BorTag.one) cfg.globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks cfg) rfl h_find
        rfl rfl rfl rfl)]
    change Miri.Interpreter.readImmediateFromMplaceRaw.match_3 _
      (Except.bind (Except.mapError
        Miri.Interpreter.MemoryOperandError.memoryRange
        (c1gRng8.subrange c1gRng8)) fun r => Except.mapError
          Miri.Interpreter.MemoryOperandError.allocation
          (c1gA8E.readScalar refRuntimeLayoutV2.base r false)) _ _ = _
    rw [show c1gRng8.subrange c1gRng8 = .ok c1gRng8 from rfl]
    dsimp only [Except.mapError, Except.bind]; rw [c1g_read8]
  dsimp only [Miri.Interpreter.ValidityMemory.readImmediate,
    refValidityMemoryEnvV2, refValidityMemoryEnv, get, getThe, MonadStateOf.get,
    EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    Miri.Interpreter.readImmediate, Miri.Interpreter.readImmediateRaw, Id.run]
  rw [show cfg.runtime = refRuntimeLayoutV2 from rfl, h_raw]
  cases st with | mk sk mc => cases mc; rfl

/-- Root validation session produced for an indirect 8-byte range local. -/
noncomputable def c1gRangeSess :
    Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance :=
  { path := ⟨"", Array.empty⟩, flags := ⟨true, false⟩, ctfeMode := none,
    refTracking := some .empty,
    dataBytes := some (exceptOkGet
      (Miri.Memory.Validity.DataRangeSet.empty.addRange
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) rfl) }

/-- Field `.0 : usize` of the range local `_i`. -/
noncomputable abbrev c1gF (i : Nat) :
    Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
  ⟨.local 0 i (some Miri.ABI.Size.ZERO) (c1Frame 0 0 []).localsIdentity, c1Us⟩

/-- Whole local `_i` with range layout `lay`. -/
noncomputable abbrev c1gDp (i : Nat) (lay : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
  ⟨.local 0 i none (c1Frame 0 0 []).localsIdentity, lay⟩

/-- Locals before step 0. -/
noncomputable abbrev c1gL0 := c1Locals c1Two c1U c1U c1U c1U c1U
/-- Locals after step 0 (`_4` in `alloc3`). -/
noncomputable abbrev c1gL0' := c1Locals c1Two c1U (c1M alloc3IdV2) c1U c1U c1U
/-- Memory after force-allocating `_4`. -/
noncomputable def c1gMemA0 : RefMiriMem :=
  c1Mem 4 (Array.mk [c1Row2, c1RowRet, c1gBlank alloc3IdV2])
    (Array.mk [alloc2IdV2, retAllocIdV2, alloc3IdV2])
/-- State after writing `_4` before statement advance. -/
noncomputable def c1gC0 : RefMiriState :=
  c1StS 0 0 c1gL0' c1Mem1 (c1Ctrl 0) c1Spans1

/-- Step 0 (`bb0`, stmt 0): `_4 = RangeTo(copy _2)`. -/
theorem c1_step_0 :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 c1Rp)
        refLimitsV2 0 c1S_entry = (c1S_bb0_1, .ok true) := by
  let rv : Miri.MIR.Rvalue :=
    .Aggregate .Tuple (Array.mk [.Copy ⟨2, Array.empty⟩])
  have h_cp : Miri.Interpreter.copyRuntimePlaceNoValidate c1gPlace
      (refExecCfgV2 c1Rp).copy 0 c1gOp2 (c1gF 4) false c1S_entry =
      .ok () c1gC0 := by
    change EStateM.bind (EStateM.bind (EStateM.bind
      (c1gPlace.allocateStack 0 c1RTo) _) _) _ c1S_entry = _
    rw [eStateM_bind3_ok (c1g_allocStack8 c1S_entry c1RTo 3 _ _
      (by decide) rfl rfl rfl rfl rfl rfl)]
    change EStateM.bind (EStateM.bind (EStateM.bind
      (c1gPlace.afterLocalMovedToMemory 0 4 ⟨c1Mp alloc3IdV2, c1RTo⟩) _) _) _
      (c1StS 0 0 c1gL0 c1gMemA0 (c1Ctrl 0) Array.empty) = _
    rw [eStateM_bind3_ok (c1g_afterMoved _ (c1Frame 0 0 c1gL0) 4 alloc3IdV2
      c1RTo rfl rfl rfl)]
    exact c1g_write (c1StS 0 0 c1gL0' c1gMemA0 (c1Ctrl 0) c1Spans1)
      alloc3IdV2 c1Mem1 rfl rfl rfl rfl rfl rfl
  exact execStep_assign_val_v2 c1Rp c1S_entry c1gC0 c1gC0 (c1Frame 0 0 c1gL0)
    (c1Frame 0 0 c1gL0') 0 0 (c1Block 0) _ ⟨4, Array.empty⟩ rv (c1gDp 4 c1RTo)
    c1gRangeSess rfl rfl rfl rfl rfl rfl
    (by
      change Miri.Interpreter.MachineHooks.run (EStateM.bind (forIn
        (m := Miri.Interpreter.MachineHooks.M Unit RefUser)
        ({ start := 0, stop := 1, step := 1, step_pos := Nat.zero_lt_one } :
          Std.Legacy.Range)
        _ _) _) c1S_entry = _
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      change Miri.Interpreter.MachineHooks.run (EStateM.bind (EStateM.bind
        (EStateM.bind (Miri.Interpreter.copyRuntimePlaceNoValidate c1gPlace
          (refExecCfgV2 c1Rp).copy 0 c1gOp2 (c1gF 4) false) _) _) _)
        c1S_entry = _
      rw [mhRun_bind3_ok h_cp]; rfl)
    (by
      change EStateM.bind (EStateM.bind (EStateM.bind (EStateM.bind
        (EStateM.bind (EStateM.bind ((refValHooksV2 c1Rp.types).readImmediate 0
          (c1gF 4) .integer) _) _) _) _) _) _ c1gC0 = _
      dsimp only [EStateM.bind]; rw [refValHooksV2_readImmediate]
      dsimp only [bind, Bind.bind, EStateM.bind]
      rw [show Miri.Interpreter.placeToOp
          (refBasePlaceProjectionHooksV2 c1Rp.types).place 0 (c1gF 4) c1gC0 =
          .ok ⟨.indirect (c1Mp alloc3IdV2), c1Us⟩ c1gC0 from rfl]
      dsimp only; rw [c1g_readImm_u64 c1gC0 alloc3IdV2 rfl]; rfl)
    rfl rfl rfl

/-- Locals after moving `_2` in step 2. -/
noncomputable abbrev c1gL2 :=
  c1Locals c1U (c1I (c1Slice 0 2)) (c1M alloc3IdV2) c1U c1U c1U
/-- Locals after step 2 (`_6` in `alloc4`). -/
noncomputable abbrev c1gL2' :=
  c1Locals c1U (c1I (c1Slice 0 2)) (c1M alloc3IdV2) c1U (c1M alloc4IdV2) c1U
/-- Memory after force-allocating `_6`. -/
noncomputable def c1gMemA2 : RefMiriMem :=
  c1Mem 5
    (Array.mk [c1Row2, c1RowRet, c1Row8 alloc3IdV2, c1gBlank alloc4IdV2])
    (Array.mk [alloc2IdV2, retAllocIdV2, alloc3IdV2, alloc4IdV2])
/-- State of step 2 after evaluating `move _2`. -/
noncomputable def c1gS2 : RefMiriState :=
  c1StS 1 0 c1gL2 c1Mem1 (c1Ctrl 1) c1Spans1
/-- State after writing `_6` before statement advance. -/
noncomputable def c1gC2 : RefMiriState :=
  c1StS 1 0 c1gL2' c1Mem2 (c1Ctrl 1) c1Spans2

/-- Step 2 (`bb1`, stmt 0): `_6 = RangeFrom(move _2)`. -/
theorem c1_step_2 :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 c1Rp)
        refLimitsV2 0 c1S_bb1_0 = (c1S_bb1_1, .ok true) := by
  let rv : Miri.MIR.Rvalue :=
    .Aggregate .Tuple (Array.mk [.Move ⟨2, Array.empty⟩])
  have h_cp : Miri.Interpreter.copyRuntimePlaceNoValidate c1gPlace
      (refExecCfgV2 c1Rp).copy 0 c1gOp2 (c1gF 6) false c1gS2 =
      .ok () c1gC2 := by
    change EStateM.bind (EStateM.bind (EStateM.bind
      (c1gPlace.allocateStack 0 c1RFrom) _) _) _ c1gS2 = _
    rw [eStateM_bind3_ok (c1g_allocStack8 c1gS2 c1RFrom 4 _ _
      (by decide) rfl rfl rfl rfl rfl rfl)]
    change EStateM.bind (EStateM.bind (EStateM.bind
      (c1gPlace.afterLocalMovedToMemory 0 6 ⟨c1Mp alloc4IdV2, c1RFrom⟩) _) _) _
      (c1StS 1 0 c1gL2 c1gMemA2 (c1Ctrl 1) c1Spans1) = _
    rw [eStateM_bind3_ok (c1g_afterMoved _ (c1Frame 1 0 c1gL2) 6 alloc4IdV2
      c1RFrom rfl rfl rfl)]
    exact c1g_write (c1StS 1 0 c1gL2' c1gMemA2 (c1Ctrl 1) c1Spans2)
      alloc4IdV2 c1Mem2 rfl rfl rfl rfl rfl rfl
  exact execStep_assign_val_v2 c1Rp c1S_bb1_0 c1gC2 c1gC2
    (c1Frame 1 0 (c1Locals c1Two (c1I (c1Slice 0 2)) (c1M alloc3IdV2) c1U c1U
      c1U))
    (c1Frame 1 0 c1gL2') 1 0 (c1Block 1) _ ⟨6, Array.empty⟩ rv
    (c1gDp 6 c1RFrom) c1gRangeSess rfl rfl rfl rfl rfl rfl
    (by
      change Miri.Interpreter.MachineHooks.run (EStateM.bind (forIn
        (m := Miri.Interpreter.MachineHooks.M Unit RefUser)
        ({ start := 0, stop := 1, step := 1, step_pos := Nat.zero_lt_one } :
          Std.Legacy.Range)
        _ _) _) c1S_bb1_0 = _
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      change Miri.Interpreter.MachineHooks.run (EStateM.bind (EStateM.bind
        (EStateM.bind (Miri.Interpreter.copyRuntimePlaceNoValidate c1gPlace
          (refExecCfgV2 c1Rp).copy 0 c1gOp2 (c1gF 6) false) _) _) _)
        c1gS2 = _
      rw [mhRun_bind3_ok h_cp]; rfl)
    (by
      change EStateM.bind (EStateM.bind (EStateM.bind (EStateM.bind
        (EStateM.bind (EStateM.bind ((refValHooksV2 c1Rp.types).readImmediate 0
          (c1gF 6) .integer) _) _) _) _) _) _ c1gC2 = _
      dsimp only [EStateM.bind]; rw [refValHooksV2_readImmediate]
      dsimp only [bind, Bind.bind, EStateM.bind]
      rw [show Miri.Interpreter.placeToOp
          (refBasePlaceProjectionHooksV2 c1Rp.types).place 0 (c1gF 6) c1gC2 =
          .ok ⟨.indirect (c1Mp alloc4IdV2), c1Us⟩ c1gC2 from rfl]
      dsimp only; rw [c1g_readImm_u64 c1gC2 alloc4IdV2 rfl]; rfl)
    rfl rfl rfl

section C1BackProof

open Miri.Memory Miri.ABI Miri.Interpreter

/-! ## Section 5: `V2_C1` block `bb3` and return/cleanup proof -/

/-- Two-operand tuple `writeAggregate` unrolls into two field writes. -/
theorem writeAggregate_tuple2_v2 {P S C V : Type}
    (h : AggregateHooks P S C V) (c : C) (o0 o1 : Miri.MIR.Operand)
    (dest : V) :
    writeAggregate h c .Tuple (Array.mk [o0, o1]) dest =
      Bind.bind (h.projectField c dest 0) (fun f0 =>
      Bind.bind (h.evalOperandAt c (.aggregate 0) o0 (some (h.placeLayout f0)))
        (fun v0 =>
      Bind.bind (h.copyOpNoValidate c v0 f0 false) (fun _ =>
      Bind.bind (h.projectField c dest 1) (fun f1 =>
      Bind.bind (h.evalOperandAt c (.aggregate 1) o1 (some (h.placeLayout f1)))
        (fun v1 =>
      Bind.bind (h.copyOpNoValidate c v1 f1 false) (fun _ =>
      Bind.bind (h.writeDiscriminant c 0 dest) (fun _ =>
      Bind.bind (h.enforceValidity c (h.placeLayout dest)) (fun enf =>
      if enf = true then h.validate c dest else pure ())))))))) := by
  unfold writeAggregate
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    show (Array.mk [o0, o1] : Array Miri.MIR.Operand).size = 2 from rfl,
    show ({ start := 0, stop := 2, step := 1, step_pos := Nat.zero_lt_one } :
      Std.Legacy.Range).size = 2 from rfl,
    show List.range' 0 2 = [0, 1] from rfl, List.forIn_cons, List.forIn_nil,
    pure_bind, bind_assoc, Option.isSome_none, Bool.false_and,
    show (Array.mk [o0, o1] : Array Miri.MIR.Operand)[0]? = some o0 from rfl,
    show (Array.mk [o0, o1] : Array Miri.MIR.Operand)[1]? = some o1 from rfl,
    Bool.false_eq_true, ite_false, Option.getD_none]

/-- Next `RefMiriMem` after reserving `id` without an active source world. -/
noncomputable def refBumpAllocIdV2 :
    RefMiriMem → Miri.Memory.AllocId → RefMiriMem
  | ⟨nai, idex, it, lv, dd, gt, igt, igr, fn, va, bk, bkr, sw, sn, se, sbr,
      rbs, os, sb⟩, id =>
    ⟨nai + 1, idex, it.push id, lv, dd, gt, igt, igr, fn, va, bk, bkr, sw, sn,
      se, sbr, rbs, os, sb⟩

/-- Exact characterization of `MemoryState.reserveAllocId` in v2 states. -/
theorem reserveAllocId_exact_v2 (mem0 mem1 : RefMiriMem)
    (aid : Miri.Memory.AllocId) (h_sw : mem0.sourceAllocIdWorldActive = false)
    (h_res : mem0.reserveAllocId = (mem1, .ok aid)) :
    mem1 = refBumpAllocIdV2 mem0 aid := by
  dsimp only [Miri.Memory.MemoryState.reserveAllocId, Id.run, bind, Bind.bind,
    pure, Pure.pure] at h_res
  have h1 := ite_pair_error_eq_ok _ _ _ _ _ _ h_res
  have h2 := ite_pair_error_eq_ok _ _ _ _ _ _ h1
  cases h_al : Miri.Memory.AllocId.ofUInt64 mem0.nextAllocId with
  | none => rw [h_al] at h2; cases h2
  | some id =>
    rw [h_al] at h2; have h3 := ite_pair_error_eq_ok _ _ _ _ _ _ h2
    rw [h_sw] at h3; simp only [Bool.false_eq_true, ite_false] at h3
    injection h3 with hm1 hok; injection hok with hid
    rw [← hm1, ← hid]; cases mem0; dsimp only at h_sw; subst h_sw; rfl

/-- `afterLocalMovedToMemory` records `localSpan` when data race is off. -/
theorem afterLocalMovedToMemory_ok_v2 (rp : RefProg) (st : RefMiriState)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (localId : LocalId) (aid : Miri.Memory.AllocId) (lay : LocalLayout)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none)
    (h_in : (st.machine.memory.live.any fun e => e.1 == aid) = true) :
    MachineHooks.afterLocalMovedToMemory localId
        ⟨⟨⟨Size.ZERO, some (.concrete aid BorTag.one)⟩, .none, none⟩, lay⟩
        (refCompilerHooksV2 rp.types).localSpan st =
      .ok () { st with
        machine := { st.machine with
          allocationSpans :=
            (st.machine.allocationSpans.filter fun e => e.1 != aid).push
              (aid, ⟨0⟩, none) } } := by
  dsimp only [MachineHooks.afterLocalMovedToMemory, bind, Bind.bind,
    EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [currentFrame_single_v2 st frame h_fr]; dsimp only
  rw [show (refCompilerHooksV2 rp.types).localSpan frame.body localId st =
      .ok ⟨0⟩ st from rfl]
  dsimp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [h_in]; simp only [h_dr]; rfl

/-- `V2_C1` locals at `bb3` with `_0`, `_5`, `_7` holding `v0`, `v5`, `v7`. -/
noncomputable def c1bLocals
    (v0 v5 v7 : LocalValue Provenance) : List RefLocalState :=
  [⟨v0, some c1Tup⟩, ⟨c1I (c1Slice 0 5), some c1Sl⟩, ⟨c1U, some c1Us⟩,
   ⟨c1U, some c1Sl⟩, ⟨c1M alloc3IdV2, some c1RTo⟩, ⟨v5, some c1Sl⟩,
   ⟨c1M alloc4IdV2, some c1RFrom⟩, ⟨v7, some c1Us⟩]

/-- `V2_C1` memory after reserving `alloc5`, with `live` and `dead` rows. -/
noncomputable def c1bMem (live : Array C1Row)
    (dead : Array DeadAllocation) : RefMiriMem :=
  { refBumpAllocIdV2 c1Mem2 alloc5IdV2 with live := live, dead := dead }

/-- Runtime place of local `_0` (`bb3`). -/
noncomputable abbrev c1bDest : RuntimePlace Provenance :=
  ⟨.local 0 0 none (c1Frame 3 0 []).localsIdentity, c1Tup⟩

/-- Runtime place of field `.0 : &[u8]` of local `_0`. -/
noncomputable abbrev c1bF0 : RuntimePlace Provenance :=
  ⟨.local 0 0 (some Size.ZERO) (c1Frame 3 0 []).localsIdentity, c1Sl⟩

/-- Runtime place of field `.1 : usize` of local `_0`. -/
noncomputable abbrev c1bF1 : RuntimePlace Provenance :=
  ⟨.local 0 0 (some (Size.ofBytes 16)) (c1Frame 3 0 []).localsIdentity, c1Us⟩

/-- Offset-16 `MemPlace` inside concrete stack/return allocation `id`. -/
noncomputable def c1bMp16' (id : Miri.Memory.AllocId) : MemPlace Provenance :=
  ⟨⟨Size.ofBytes 16, some (.concrete id BorTag.one)⟩, .none, none⟩

/-- Live rows once `_0` lives in `alloc5` with contents `a`. -/
noncomputable def c1bLive (a : RefMiriAlloc) : Array C1Row :=
  Array.mk [c1Row2, c1RowRet, c1Row8 alloc3IdV2, c1Row8 alloc4IdV2,
    (alloc5IdV2, ⟨.stack, a⟩)]

/-- Public builder mirroring the private `Allocation` constructor. -/
noncomputable def refMkAllocV2 {P E : Type} (raw : Array UInt8) (size : Size)
    (prov : ProvenanceMap P) (mask : InitMask) (align : Align)
    (mty : Miri.Memory.Mutability) (extra : E) :
    Miri.Memory.Allocation P E := by
  constructor; exact raw; exact size; exact prov; exact mask
  exact align; exact mty; exact extra; exact none

/-- Public builder mirroring the private `ProvenanceMap` constructor. -/
noncomputable def refMkProvV2 {P : Type} (ptrs : Array (Size × P)) :
    ProvenanceMap P := by constructor; exact ptrs; exact none

/-- 24-byte tuple allocation with bytes `raw`, provenance `ptrs`, mask `m`. -/
noncomputable def c1bBuf (raw : List UInt8) (ptrs : List (Size × Provenance))
    (mask : InitMaskBlocks) : RefMiriAlloc :=
  refMkAllocV2 (Array.mk raw) (Size.ofBytes 24) (refMkProvV2 (Array.mk ptrs))
    ⟨mask, Size.ofBytes 24⟩ Align.EIGHT .Mut (c1Tree 24)

/-- Little-endian 8-byte encoding of small byte `b`. -/
noncomputable abbrev c1bB8 (b : UInt8) : List UInt8 := [b, 0, 0, 0, 0, 0, 0, 0]

/-- Provenance entry of the slice pointer at offset `0`. -/
noncomputable abbrev c1bPtrs : List (Size × Provenance) :=
  [(Size.ZERO, .concrete alloc2IdV2 BorTag.one)]

/-- Fresh contents of `_0`'s stack buffer. -/
noncomputable def c1bA0 : RefMiriAlloc :=
  c1bBuf (c1bB8 0 ++ c1bB8 0 ++ c1bB8 0) [] (.Lazy false)

/-- `_0`'s buffer after writing the slice pointer at offset `0`. -/
noncomputable def c1bA1 : RefMiriAlloc :=
  c1bBuf (c1bB8 2 ++ c1bB8 0 ++ c1bB8 0) c1bPtrs
    (.Materialized ⟨Array.mk [0xFF]⟩)

/-- `_0`'s buffer after writing the slice length at offset `8`. -/
noncomputable def c1bA2 : RefMiriAlloc :=
  c1bBuf (c1bB8 2 ++ c1bB8 3 ++ c1bB8 0) c1bPtrs
    (.Materialized ⟨Array.mk [0xFFFF]⟩)

/-- Final tuple allocation parameterized by init-mask representation `m`. -/
noncomputable def c1bA3m (m : InitMaskBlocks) : RefMiriAlloc :=
  c1bBuf (c1bB8 2 ++ c1bB8 3 ++ c1bB8 2) c1bPtrs m

/-- Concrete `_0` buffer after writing `2usize` at offset `16`. -/
noncomputable abbrev c1bA3 : RefMiriAlloc :=
  c1bA3m (.Materialized ⟨Array.mk [0xFFFFFF]⟩)

/-- Concrete return buffer after `copyRepeatedly` from `c1bA3`. -/
noncomputable abbrev c1bR1 : RefMiriAlloc := c1bA3m (.Lazy true)

/-- Disjunction identifying the two concrete init masks `c1bA3` and `c1bR1`. -/
abbrev C1BMaskEq (m : InitMaskBlocks) : Prop :=
  m = .Materialized ⟨Array.mk [0xFFFFFF]⟩ ∨ m = .Lazy true

/-- Read slice pointer scalar from `c1bA3m m` at offset `0`. -/
theorem c1b_rd_ptr (m : InitMaskBlocks) (hm : C1BMaskEq m) :
    (c1bA3m m).readScalar refRuntimeLayoutV2.base
      (allocRange Size.ZERO (Size.ofBytes 8)) true = .ok (c1PtrSc 2) := by
  have hi : (⟨m, Size.ofBytes 24⟩ : InitMask).isRangeInitialized
      (allocRange Size.ZERO (Size.ofBytes 8)) = .ok (.ok ()) := by
    cases hm with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  exact Allocation.readScalar_ptr_roundtrip (c1bA3m m) refRuntimeLayoutV2.base
    (allocRange Size.ZERO (Size.ofBytes 8))
    ⟨Size.ofBytes 2, .concrete alloc2IdV2 BorTag.one⟩ hi rfl (by decide)
    (by decide) rfl rfl

/-- Read slice length `3usize` from `c1bA3m m` at offset `8`. -/
theorem c1b_rd_len (m : InitMaskBlocks) (hm : C1BMaskEq m) :
    (c1bA3m m).readScalar refRuntimeLayoutV2.base
      (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) false =
      .ok (c1Usize 3) := by
  have hi : (⟨m, Size.ofBytes 24⟩ : InitMask).isRangeInitialized
      (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) = .ok (.ok ()) := by
    cases hm with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  exact (Allocation.readScalar_int_of_bytes (c1bA3m m) refRuntimeLayoutV2.base
    (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) (Array.mk (c1bB8 3)) hi rfl
    (by decide) (.inr rfl)).trans rfl

/-- Read `2usize` scalar from `c1bA3m m` at offset `16`. -/
theorem c1b_rd_usize (m : InitMaskBlocks) (hm : C1BMaskEq m) :
    (c1bA3m m).readScalar refRuntimeLayoutV2.base
      (allocRange (Size.ofBytes 16) (Size.ofBytes 8)) false =
      .ok (c1Usize 2) := by
  have hi : (⟨m, Size.ofBytes 24⟩ : InitMask).isRangeInitialized
      (allocRange (Size.ofBytes 16) (Size.ofBytes 8)) = .ok (.ok ()) := by
    cases hm with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  exact (Allocation.readScalar_int_of_bytes (c1bA3m m) refRuntimeLayoutV2.base
    (allocRange (Size.ofBytes 16) (Size.ofBytes 8)) (Array.mk (c1bB8 2)) hi rfl
    (by decide) (.inr rfl)).trans rfl

/-- Little-endian 8-byte encoding performed by `Allocation.writeScalar`. -/
theorem targetUIntBytesMirror_le8_v2 (bits : BitVec 128) :
    targetUIntBytesMirror refRuntimeLayoutV2.base (Size.ofBytes 8) bits =
      .ok (Array.mk ((List.range' 0 8).map fun i =>
        UInt8.ofNat (Nat.mod (Nat.div bits.toNat (Nat.pow 2 (8 * i))) 256))) :=
  by
  dsimp only [targetUIntBytesMirror]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']; rfl

/-- Evaluate `ProvenanceMap.insertPtr` at offset `0` inside `writeScalar`. -/
private theorem c1b_insertPtr_zero (raw : List UInt8) (m : InitMaskBlocks)
    (aErr aOk : RefMiriAlloc)
    (h_ok : refMkAllocV2 (Array.mk raw) (Size.ofBytes 24)
      (refMkProvV2 (Array.mk c1bPtrs)) ⟨m, Size.ofBytes 24⟩ Align.EIGHT .Mut
      (c1Tree 24) = aOk) :
    (match ProvenanceMap.insertPtr Size.ZERO
        (Provenance.concrete alloc2IdV2 BorTag.one) (Size.ofBytes 8)
        ProvenanceMap.new with
      | .ok _ mp => EStateM.Result.ok () (refMkAllocV2 (Array.mk raw)
          (Size.ofBytes 24) mp ⟨m, Size.ofBytes 24⟩ Align.EIGHT .Mut
          (c1Tree 24))
      | .error _ _ => EStateM.Result.error AllocError.readOnlyAllocation
          aErr) = .ok () aOk := by
  rw [ProvenanceMap.insertPtr_new Size.ZERO (Size.ofBytes 8) (Size.ofBytes 8)
    _ (by decide) rfl]
  subst aOk; rfl

/-- Idempotent re-write of slice pointer at offset `0` on `c1bA3m m`. -/
theorem c1b_re_w0 (m : InitMaskBlocks) (hm : C1BMaskEq m) :
    Allocation.writeScalar refRuntimeLayoutV2.base
      (allocRange Size.ZERO (Size.ofBytes 8)) (c1PtrSc 2) (c1bA3m m) =
      .ok () (c1bA3m m) := by
  cases hm with
  | inl h =>
    subst h
    change (match targetUIntBytesMirror refRuntimeLayoutV2.base (Size.ofBytes 8)
        (BitVec.ofNat 128 2) with | .ok _ => _ | .error _ => _) = _
    rw [targetUIntBytesMirror_le8_v2]; dsimp only
    exact c1b_insertPtr_zero _ (.Materialized ⟨Array.mk [0xFFFFFF]⟩)
      c1bA3 c1bA3 rfl
  | inr h =>
    subst h
    change (match targetUIntBytesMirror refRuntimeLayoutV2.base (Size.ofBytes 8)
        (BitVec.ofNat 128 2) with | .ok _ => _ | .error _ => _) = _
    rw [targetUIntBytesMirror_le8_v2]; dsimp only
    exact c1b_insertPtr_zero _ (.Lazy true) c1bR1 c1bR1 rfl

/-- Idempotent re-write of slice length `3` at offset `8` on `c1bA3m m`. -/
theorem c1b_re_w1 (m : InitMaskBlocks) (hm : C1BMaskEq m) :
    Allocation.writeScalar refRuntimeLayoutV2.base
      (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) (c1Usize 3) (c1bA3m m) =
      .ok () (c1bA3m m) := by
  cases hm with
  | inl h =>
    subst h
    change (match targetUIntBytesMirror refRuntimeLayoutV2.base (Size.ofBytes 8)
        (BitVec.ofNat 128 3) with | .ok _ => _ | .error _ => _) = _
    rw [targetUIntBytesMirror_le8_v2]; rfl
  | inr h =>
    subst h
    change (match targetUIntBytesMirror refRuntimeLayoutV2.base (Size.ofBytes 8)
        (BitVec.ofNat 128 3) with | .ok _ => _ | .error _ => _) = _
    rw [targetUIntBytesMirror_le8_v2]; rfl

/-- State after evaluating `move _5` at `(bb3, 0)`. -/
noncomputable def c1bSa : RefMiriState :=
  c1StS 3 0 (c1bLocals c1U c1U c1Two) c1Mem2 (c1Ctrl 3) c1Spans2

/-- Allocation spans once `_0` has moved to memory. -/
noncomputable abbrev c1bSpans : Array C1Span :=
  Array.mk [c1Sp alloc3IdV2, c1Sp alloc4IdV2, c1Sp alloc5IdV2]

/-- State at statement `idx` of `bb3` with `_0` in `alloc5` holding `a`. -/
noncomputable def c1bSm (idx : Nat) (v5 v7 : LocalValue Provenance)
    (a : RefMiriAlloc) : RefMiriState :=
  c1StS 3 idx (c1bLocals (c1M alloc5IdV2) v5 v7)
    (c1bMem (c1bLive a) Array.empty) (c1Ctrl 3) c1bSpans

/-- Pre-validation state after both tuple field writes at `(bb3, 0)`. -/
noncomputable abbrev c1bS0 : RefMiriState := c1bSm 0 c1U c1U c1bA3

/-- Post-assign state at `(bb3, 1)` ready for `Terminator.Return`. -/
noncomputable def c1bS1 : RefMiriState := c1bSm 1 c1U c1U c1bA3

/-- Field `.0` copy allocates `_0` on stack, records span, and writes slice. -/
theorem c1b_copy0 :
    copyRuntimePlaceNoValidate
      (ExecutionMachine.projectionHooks (refExecCfgV2 c1Rp)).place
      (refExecCfgV2 c1Rp).copy 0 ⟨.immediate (c1Slice 2 3), c1Sl⟩ c1bF0 false
      c1bSa = .ok () (c1bSm 0 c1U c1Two c1bA2) := by
  let stB := c1StS 3 0 (c1bLocals c1U c1U c1Two)
    (c1bMem (c1bLive c1bA0) Array.empty) (c1Ctrl 3) c1Spans2
  let stC := c1StS 3 0 (c1bLocals c1U c1U c1Two)
    (c1bMem (c1bLive c1bA0) Array.empty) (c1Ctrl 3) c1bSpans
  let m0 := c1bMem (c1bLive c1bA0) Array.empty
  let m1 := c1bMem (c1bLive c1bA1) Array.empty
  let m2 := c1bMem (c1bLive c1bA2) Array.empty
  let hk : PlaceMachine.AccessState Unit RefUser :=
    ⟨(c1bSm 0 c1U c1Two c1bA0).machine, none⟩
  let cfg := refAccessConfigV2 c1Rp.types
  have hlt : ∀ z, z ∈ [alloc2IdV2, retAllocIdV2, alloc3IdV2, alloc4IdV2] →
      z.value.toNat < 5 := fun z hz => of_decide_eq_true
    (List.all_eq_true.mp (rfl : [alloc2IdV2, retAllocIdV2, alloc3IdV2,
      alloc4IdV2].all (fun z => decide (z.value.toNat < 5)) = true) z hz)
  let ⟨mem1, h_res, h_as⟩ := allocateStack_sized_v2 c1Rp c1bSa c1Tup
    alloc5IdV2 c1Ret rfl (by decide) (tryNew_eq_of_image_v2 (Size.ofBytes 24)
      Align.EIGHT 8 _ c1Ret rfl rfl (by decide) (exceptOkGet_eq _ rfl) rfl)
    rfl rfl rfl rfl (by decide) (fun h => by cases h) (fun h => by cases h)
    (fun id h => hlt id h.val)
    (fun row h => hlt row.1 (List.mem_map_of_mem (f := Prod.fst) h.val))
    (fun row h => by cases h with | mk hl => cases hl)
    (fun row h => by cases h with | mk hl => cases hl) rfl
  rw [reserveAllocId_exact_v2 _ _ _ rfl h_res] at h_as
  have h_am : MachineHooks.afterLocalMovedToMemory 0 ⟨c1Mp alloc5IdV2, c1Tup⟩
      (refCompilerHooksV2 c1Rp.types).localSpan stB = .ok () stC :=
    afterLocalMovedToMemory_ok_v2 c1Rp stB _ 0 alloc5IdV2 c1Tup rfl rfl
      (by rw [← Array.any_toList]; rfl)
  have h_ptr0 := getPtrAllocMut_live_nonghost_v2 c1Rp.types (Size.ofBytes 16) 16
    m0 m0 .stack c1bA0 (c1bSm 0 c1U c1Two c1bA0).machine alloc5IdV2 Size.ZERO
    (c1Mp alloc5IdV2).ptr (.concrete BorTag.one) rfl rfl
    (by rw [← Array.any_toList]; rfl) rfl rfl rfl rfl rfl rfl rfl
  have h_gpl := getPlaceAllocMut_sized_of_access m0 hk
    ⟨c1Mp alloc5IdV2, localMemoryLayout c1Sl⟩ refRuntimeLayoutV2
    (Size.ofBytes 8) none cfg.globalHooks (PlaceMachine.accessHooks cfg)
    cfg.dynamicLayout
    ⟨alloc5IdV2, allocRange Size.ZERO (Size.ofBytes 16), c1bA0⟩ rfl rfl rfl
    h_ptr0
  have h_w0 : Allocation.writeScalar refRuntimeLayoutV2.base
      (allocRange Size.ZERO (Size.ofBytes 8)) (c1PtrSc 2) c1bA0 =
      .ok () c1bA1 := by
    change (match targetUIntBytesMirror refRuntimeLayoutV2.base (Size.ofBytes 8)
        (BitVec.ofNat 128 2) with | .ok _ => _ | .error _ => _) = _
    rw [targetUIntBytesMirror_le8_v2]
    exact c1b_insertPtr_zero _ (.Materialized ⟨Array.mk [0xFF]⟩) c1bA0 c1bA1 rfl
  have h_w1 : Allocation.writeScalar refRuntimeLayoutV2.base
      (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) (c1Usize 3) c1bA1 =
      .ok () c1bA2 := by
    change (match targetUIntBytesMirror refRuntimeLayoutV2.base (Size.ofBytes 8)
        (BitVec.ofNat 128 3) with | .ok _ => _ | .error _ => _) = _
    rw [targetUIntBytesMirror_le8_v2]; rfl
  have h_wr0 := PlaceMachine.writeMemory_of_result cfg (fun _ => true)
    (c1Slice 2 3) ⟨c1Mp alloc5IdV2, c1Sl⟩ (c1bSm 0 c1U c1Two c1bA0) m2
    (some ⟨alloc5IdV2, allocRange Size.ZERO (Size.ofBytes 16), c1bA2⟩) rfl
    (writeImmediate_pair_of_access m0 m1 m2 hk
      ⟨c1Mp alloc5IdV2, localMemoryLayout c1Sl⟩ refRuntimeLayoutV2 none
      cfg.globalHooks (PlaceMachine.accessHooks cfg) cfg.dynamicLayout
      (c1PtrSc 2) (c1Usize 3) _ _ (Size.ofBytes 8) alloc5IdV2 c1bA0 c1bA1 c1bA2
      rfl rfl rfl trivial rfl (by decide) (by decide) (by decide) h_gpl
      h_w0 rfl h_w1 rfl)
  change EStateM.bind (EStateM.bind (EStateM.bind
    ((ExecutionMachine.projectionHooks
      (refExecCfgV2 c1Rp)).place.allocateStack 0 c1Tup) _) _) _ c1bSa = _
  rw [eStateM_bind3_ok h_as]
  change EStateM.bind (EStateM.bind (EStateM.bind
    (MachineHooks.afterLocalMovedToMemory 0 ⟨c1Mp alloc5IdV2, c1Tup⟩
      (refCompilerHooksV2 c1Rp.types).localSpan) _) _) _ stB = _
  rw [eStateM_bind3_ok h_am]; exact h_wr0

/-- Field `.1` copy into `_0.1` yields `c1bS0`. -/
theorem c1b_copy1 :
    copyRuntimePlaceNoValidate
      (ExecutionMachine.projectionHooks (refExecCfgV2 c1Rp)).place
      (refExecCfgV2 c1Rp).copy 0 ⟨.immediate (.scalar (c1Usize 2)), c1Us⟩
      c1bF1 false (c1bSm 0 c1U c1U c1bA2) = .ok () c1bS0 := by
  let cfg := refAccessConfigV2 c1Rp.types
  let m2 := c1bMem (c1bLive c1bA2) Array.empty
  let m3 := c1bMem (c1bLive c1bA3) Array.empty
  let hk : PlaceMachine.AccessState Unit RefUser :=
    ⟨(c1bSm 0 c1U c1U c1bA2).machine, none⟩
  have h_ptr1 := getPtrAllocMut_live_nonghost_v2 c1Rp.types (Size.ofBytes 8) 8
    m2 m2 .stack c1bA2 (c1bSm 0 c1U c1U c1bA2).machine alloc5IdV2
    (Size.ofBytes 16) (c1bMp16' alloc5IdV2).ptr (.concrete BorTag.one) rfl rfl
    (by rw [← Array.any_toList]; rfl) rfl rfl rfl rfl rfl rfl rfl
  have h_gpl := getPlaceAllocMut_sized_of_access m2 hk
    ⟨c1bMp16' alloc5IdV2, localMemoryLayout c1Us⟩ refRuntimeLayoutV2
    (Size.ofBytes 8) none cfg.globalHooks (PlaceMachine.accessHooks cfg)
    cfg.dynamicLayout
    ⟨alloc5IdV2, allocRange (Size.ofBytes 16) (Size.ofBytes 8), c1bA2⟩ rfl rfl
    rfl h_ptr1
  have h_w2 : Allocation.writeScalar refRuntimeLayoutV2.base
      (allocRange (Size.ofBytes 16) (Size.ofBytes 8)) (c1Usize 2) c1bA2 =
      .ok () c1bA3 := by
    change (match targetUIntBytesMirror refRuntimeLayoutV2.base (Size.ofBytes 8)
        (BitVec.ofNat 128 2) with | .ok _ => _ | .error _ => _) = _
    rw [targetUIntBytesMirror_le8_v2]; rfl
  exact PlaceMachine.writeMemory_of_result cfg (fun _ => true)
    (.scalar (c1Usize 2)) ⟨c1bMp16' alloc5IdV2, c1Us⟩
    (c1bSm 0 c1U c1U c1bA2) m3
    (some ⟨alloc5IdV2, allocRange (Size.ofBytes 16) (Size.ofBytes 8), c1bA3⟩)
    rfl
    (writeImmediate_scalar_u64_at_poly m2 m3 hk (c1bMp16' alloc5IdV2)
      (some c1Us.ty) false _ 2 none cfg.globalHooks
      (PlaceMachine.accessHooks cfg) cfg.dynamicLayout (fun _ => true)
      ⟨alloc5IdV2, allocRange (Size.ofBytes 16) (Size.ofBytes 8), c1bA2⟩
      _ c1bA3 h_gpl rfl h_w2 rfl)

/-- Validity `resolvePointer` bridge via `refResolvePointerPure`. -/
theorem c1b_val_rp (mem : RefMiriMem)
    (m : MachineHooks.MachineState Unit RefUser)
    (ptr : Pointer (Option Provenance)) (ss : Int) (id : Miri.Memory.AllocId)
    (off : Size)
    (h : refResolvePointerPure ptr ss = .ok ⟨id, off, .concrete BorTag.one⟩) :
    (refValidityMemoryEnvV2 c1Rp.types).context.accessHooks.resolvePointer mem
      ⟨m, none⟩ ptr ss =
      ⟨⟨m, none⟩, .ok (.ok ⟨id, off, .concrete BorTag.one⟩)⟩ := by
  dsimp only [refValidityMemoryEnvV2, PlaceMachine.accessHooks]
  exact PlaceMachine.resolvePointer_ok (refAccessConfigV2 c1Rp.types) mem m
    ptr ss _ (by
      dsimp only [refAccessConfigV2, refAccessConfig, refResolvePointer]
      rw [h])

/-- Ghost `getPtrAllocMut` succeeds on a live mutable allocation in `mem`. -/
theorem getPtrAllocMut_live_ghost_v2 (sz : Size) (signedSize : Int)
    (mem : RefMiriMem) (kind : MemoryKind Unit) (alloc : RefMiriAlloc)
    (machine : MachineHooks.MachineState Unit RefUser)
    (aid : Miri.Memory.AllocId) (off : Size)
    (ptr : Pointer (Option Provenance)) (prov : ProvenanceExtra)
    (globalHooks : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree
      Unit (PlaceMachine.AccessState Unit RefUser))
    (accessHooks : AllocationAccessHooks Provenance Miri.TreeBorrows.BorrowTree
      Unit (PlaceMachine.AccessState Unit RefUser) ProvenanceExtra)
    (h_gh : globalHooks = refGlobalAllocationHooks)
    (h_find : mem.live.find? (fun e => e.1 == aid) =
      some (aid, ⟨kind, alloc⟩))
    (h_mut : alloc.mutability = .Mut) (h_sz : sizeAsI64 sz = .ok signedSize)
    (h_nz : (signedSize != 0) = true)
    (h_cb : checkedBounds ⟨Size.ofBytes 8⟩ aid alloc.byteSize off signedSize
      .memoryAccess = .ok ())
    (h_rp : accessHooks.resolvePointer mem ⟨machine, none⟩ ptr signedSize =
      ⟨⟨machine, none⟩, .ok (.ok ⟨aid, off, prov⟩)⟩) :
    AllocationAccess.getPtrAllocMut mem ⟨machine, none⟩ ⟨Size.ofBytes 8⟩
        ptr sz true none globalHooks accessHooks =
      ⟨mem, ⟨machine, none⟩, some ⟨aid, allocRange off sz, alloc⟩,
        .ok (some ⟨aid, allocRange off sz, alloc⟩)⟩ := by
  have h_mut_f : (alloc.mutability == .Not) = false := by rw [h_mut]; rfl
  have h_raw : MemoryLifecycle.getAllocRawMut mem ⟨machine, none⟩ aid none
      globalHooks = ⟨mem, ⟨machine, none⟩, .ok alloc⟩ := by
    dsimp only [MemoryLifecycle.getAllocRawMut, MemoryLifecycle.getAllocRaw]
    rw [h_gh]; dsimp only [refGlobalAllocationHooks, Id.run, bind, Bind.bind,
      pure, Pure.pure]; rw [h_find]; dsimp only; rw [h_mut_f]; rfl
  dsimp only [AllocationAccess.getPtrAllocMut]
  change (match sizeAsI64 sz with | .ok _ => _ | .error _ => _) = _
  rw [h_sz]; change (if ((signedSize != 0) = true) then _ else _) = _
  rw [h_nz, ite_true_eq]; dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_rp]; dsimp only [pure, Pure.pure, bind, Bind.bind]; simp only [ite_true]
  rw [h_raw]; dsimp only [pure, Pure.pure, bind, Bind.bind]; rw [h_cb]; rfl

/-- `beforeMemoryWrite` succeeds trivially with borrow and race checks off. -/
theorem c1b_acc_write (m : MachineHooks.MachineState Unit RefUser)
    (hbt : m.borrowTracker = none) (hdr : m.dataRace = none)
    (tr : Miri.TreeBorrows.BorrowTree) (ptr : Pointer (Option Provenance))
    (id : Miri.Memory.AllocId) (rng : AllocRange) :
    (refValidityMemoryEnvV2 c1Rp.types).context.accessHooks.beforeMemoryWrite
      ⟨m, none⟩ tr ptr id (.concrete BorTag.one) rng =
      ⟨⟨m, none⟩, tr, .ok ()⟩ := by
  cases m; dsimp only at hbt hdr; subst hbt hdr; rfl

/-- Invariants of a concrete tuple place `place` backed by `c1bA3m m` at
stack/return allocation `id` inside state `st` (`mem = st.machine.memory`). -/
structure C1BValState (st : RefMiriState) (mem : RefMiriMem)
    (m : InitMaskBlocks) (id : Miri.Memory.AllocId)
    (place f0 f1 : RuntimePlace Provenance) : Prop where
  h_mem : st.machine.memory = mem
  h_bt : st.machine.borrowTracker = none
  h_dr : st.machine.dataRace = none
  h_find2 : mem.live.find? (fun e => e.1 == alloc2IdV2) = some c1Row2
  h_play : place.layout = c1Tup
  h_flay0 : f0.layout = c1Sl
  h_flay1 : f1.layout = c1Us
  h_toOpP : placeToOp (refBasePlaceProjectionHooksV2 c1Rp.types).place 0 place
    st = .ok ⟨.indirect (c1Mp id), c1Tup⟩ st
  h_fa : forceAllocation (refBasePlaceProjectionHooksV2 c1Rp.types).place 0
    place st = .ok ⟨c1Mp id, c1Tup⟩ st
  h_field0 : PlaceDynamic.field (refValHooksV2 c1Rp.types).projection 0
    place 0 st = .ok f0 st
  h_field1 : PlaceDynamic.field (refValHooksV2 c1Rp.types).projection 0
    place 1 st = .ok f1 st
  h_toOp0 : placeToOp (refBasePlaceProjectionHooksV2 c1Rp.types).place 0 f0
    st = .ok ⟨.indirect (c1Mp id), c1Sl⟩ st
  h_asMp0 : asMplaceOrMutableLocal
    (refBasePlaceProjectionHooksV2 c1Rp.types).place 0 f0 st =
    .ok (.memory ⟨c1Mp id, c1Sl⟩) st
  h_toOp1 : placeToOp (refBasePlaceProjectionHooksV2 c1Rp.types).place 0 f1
    st = .ok ⟨.indirect (c1bMp16' id), c1Us⟩ st
  h_clr1 : (refValHooksV2 c1Rp.types).clearProvenance 0 f1 st = .ok () st
  h_find : mem.live.find? (fun e => e.1 == id) =
    some (id, ⟨.stack, c1bA3m m⟩)
  h_live : { mem with live := ((mem.live.filter fun e => e.1 != id).push
    (id, ⟨.stack, c1bA3m m⟩)) } = mem
  hm : C1BMaskEq m

/-- Validity memory context abbreviation for `V2_C1`. -/
noncomputable abbrev c1bValAcc := (refValidityMemoryEnvV2 c1Rp.types).context

/-- Shared `ScalarPair` operand layout of field `.0 : &[u8]`. -/
noncomputable abbrev c1bPairOpLay : MemoryOperandLayout :=
  ⟨Size.ofBytes 16, Align.EIGHT, .ScalarPair
    (a := .Initialized (value := .Pointer AddressSpace.ZERO)
      (validRange := refFullWrappingRangeSize (Size.ofBytes 8)))
    (b := .Initialized (value := .Int .I64 false)
      (validRange := refFullWrappingRangeSize (Size.ofBytes 8)))
    (bOffset := Size.ofBytes 8), some c1Sl.ty⟩

/-- Shared `Scalar` operand layout of field `.1 : usize`. -/
noncomputable abbrev c1bU64OpLay : MemoryOperandLayout :=
  ⟨Size.ofBytes 8, Align.EIGHT, .Scalar (.Initialized (value := .Int .I64 false)
    (validRange := refFullWrappingRangeSize (Size.ofBytes 8))), some c1Us.ty⟩

/-- Non-ghost `writeImmediateToMplaceNoValidate` proof with opaque hooks. -/
theorem c1b_wr_pair_false (st : RefMiriState) (mem : RefMiriMem)
    (a : RefMiriAlloc) (id : Miri.Memory.AllocId)
    (global : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree
      Unit (PlaceMachine.AccessState Unit RefUser))
    (access : AllocationAccessHooks Provenance Miri.TreeBorrows.BorrowTree
      Unit (PlaceMachine.AccessState Unit RefUser) ProvenanceExtra)
    (dynamic : DynamicLayoutResolver Provenance Miri.TreeBorrows.BorrowTree
      Unit (PlaceMachine.AccessState Unit RefUser))
    (h_rp : access.resolvePointer mem ⟨st.machine, none⟩ (c1Mp id).ptr 16 =
      ⟨⟨st.machine, none⟩, .ok (.ok ⟨id, Size.ZERO, .concrete BorTag.one⟩)⟩)
    (h_find : mem.live.find? (fun e => e.1 == id) = some (id, ⟨.stack, a⟩))
    (h_live : { mem with live := ((mem.live.filter fun e => e.1 != id).push
      (id, ⟨.stack, a⟩)) } = mem)
    (h_mut : a.mutability = .Mut) (h_bs : a.byteSize = Size.ofBytes 24)
    (h_sync : global.synchronizeMemory mem ⟨st.machine, none⟩ =
      ⟨st.machine, none⟩)
    (h_bef : access.beforeAllocationAccess ⟨st.machine, none⟩ id =
      ⟨⟨st.machine, none⟩, .ok ()⟩)
    (h_wr : access.beforeMemoryWrite ⟨st.machine, none⟩ a.extra (c1Mp id).ptr id
      (.concrete BorTag.one) (allocRange Size.ZERO (Size.ofBytes 16)) =
      ⟨⟨st.machine, none⟩, a.extra, .ok ()⟩)
    (h_w0 : a.writeScalar refRuntimeLayoutV2.base
      (allocRange Size.ZERO (Size.ofBytes 8)) (c1PtrSc 2) = .ok () a)
    (h_w1 : a.writeScalar refRuntimeLayoutV2.base
      (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) (c1Usize 3) = .ok () a) :
    let lay : MemoryOperandLayout := ⟨Size.ofBytes 16, Align.EIGHT, .ScalarPair
      (a := .Initialized (value := .Pointer AddressSpace.ZERO)
        (validRange := refFullWrappingRangeSize (Size.ofBytes 8)))
      (b := .Initialized (value := .Int .I64 false)
        (validRange := refFullWrappingRangeSize (Size.ofBytes 8)))
      (bOffset := Size.ofBytes 8), some c1Sl.ty⟩
    let ref : AllocationAccessRef Provenance Miri.TreeBorrows.BorrowTree :=
      ⟨id, allocRange Size.ZERO (Size.ofBytes 16), a⟩
    getPlaceAllocMut mem ⟨st.machine, none⟩ ⟨c1Mp id, lay⟩ refRuntimeLayoutV2
        false none global access dynamic =
      ⟨mem, ⟨st.machine, none⟩, some ref, .ok (some ref)⟩ ∧
    writeImmediateToMplaceNoValidate mem ⟨st.machine, none⟩
        (.scalarPair (c1PtrSc 2) (c1Usize 3)) ⟨c1Mp id, lay⟩ refRuntimeLayoutV2
        false none global access dynamic (fun _ => true) =
      ⟨mem, ⟨st.machine, none⟩, some ref, .ok ()⟩ := by
  intro lay ref
  let abiA : Miri.ABI.Scalar :=
    .Initialized (value := .Pointer AddressSpace.ZERO)
      (validRange := refFullWrappingRangeSize (Size.ofBytes 8))
  let abiB : Miri.ABI.Scalar := .Initialized (value := .Int .I64 false)
    (validRange := refFullWrappingRangeSize (Size.ofBytes 8))
  have h_cb : checkedBounds ⟨Size.ofBytes 8⟩ id a.byteSize Size.ZERO 16
      .memoryAccess = .ok () := by rw [h_bs]; rfl
  have h_ga := AllocationAccess.live_mut_of_edges mem ⟨st.machine, none⟩
    ⟨Size.ofBytes 8⟩ (c1Mp id).ptr (Size.ofBytes 16) none global access id
    ⟨.stack, a⟩ (.concrete BorTag.one) 16 rfl (by decide) h_rp h_find h_mut
    h_sync h_cb h_bef h_wr (congrArg MemoryState.live h_live)
  have hf := getPlaceAllocMut_sized_of_access mem ⟨st.machine, none⟩
    ⟨c1Mp id, lay⟩ refRuntimeLayoutV2 (Size.ofBytes 8) none global access
    dynamic ref rfl rfl rfl h_ga
  have h_cache : mem.setLiveAllocation id a = .ok mem := by
    rw [MemoryState.setLiveAllocation_of_find mem id ⟨.stack, a⟩ a h_find]
    exact congrArg Except.ok h_live
  have h_wr_f := writeImmediate_pair_of_access mem mem mem ⟨st.machine, none⟩
    ⟨c1Mp id, lay⟩ refRuntimeLayoutV2 none global access dynamic (c1PtrSc 2)
    (c1Usize 3) abiA abiB (Size.ofBytes 8) id a a a rfl rfl rfl trivial rfl
    (by decide) (by decide) (by change 8 + 8 ≤ 16; decide) (by exact hf) h_w0 h_cache
    h_w1 h_cache
  exact ⟨hf, h_wr_f⟩

/-- Abstract ghost re-write of `c1Slice 2 3` at `c1Mp id` preserves `mem`. -/
theorem c1b_val_reset0_abs (st : RefMiriState) (mem : RefMiriMem)
    (a : RefMiriAlloc) (id : Miri.Memory.AllocId) (f0 : RuntimePlace Provenance)
    (h_mem : st.machine.memory = mem)
    (h_bt : st.machine.borrowTracker = none)
    (h_dr : st.machine.dataRace = none) (h_flay0 : f0.layout = c1Sl)
    (h_asMp0 : asMplaceOrMutableLocal
      (refBasePlaceProjectionHooksV2 c1Rp.types).place 0 f0 st =
      .ok (.memory ⟨c1Mp id, c1Sl⟩) st)
    (h_find : mem.live.find? (fun e => e.1 == id) = some (id, ⟨.stack, a⟩))
    (h_live : { mem with live := ((mem.live.filter fun e => e.1 != id).push
      (id, ⟨.stack, a⟩)) } = mem)
    (h_mut : a.mutability = .Mut) (h_bs : a.byteSize = Size.ofBytes 24)
    (h_w0 : a.writeScalar refRuntimeLayoutV2.base
      (allocRange Size.ZERO (Size.ofBytes 8)) (c1PtrSc 2) = .ok () a)
    (h_w1 : a.writeScalar refRuntimeLayoutV2.base
      (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) (c1Usize 3) = .ok () a) :
    (refValHooksV2 c1Rp.types).writeNoValidate 0 (c1Slice 2 3) f0 st =
      .ok () st := by
  let mp := c1Mp id
  let lay : MemoryOperandLayout := ⟨Size.ofBytes 16, Align.EIGHT, .ScalarPair
    (a := .Initialized (value := .Pointer AddressSpace.ZERO)
      (validRange := refFullWrappingRangeSize (Size.ofBytes 8)))
    (b := .Initialized (value := .Int .I64 false)
      (validRange := refFullWrappingRangeSize (Size.ofBytes 8)))
    (bOffset := Size.ofBytes 8), some c1Sl.ty⟩
  have h_rp := c1b_val_rp mem st.machine mp.ptr 16 id Size.ZERO rfl
  have h_cb : checkedBounds ⟨Size.ofBytes 8⟩ id a.byteSize Size.ZERO 16
      .memoryAccess = .ok () := by rw [h_bs]; rfl
  have h_ga_t := getPtrAllocMut_live_ghost_v2 (Size.ofBytes 16) 16 mem .stack a
    st.machine id Size.ZERO mp.ptr (.concrete BorTag.one)
    c1bValAcc.globalHooks c1bValAcc.accessHooks rfl h_find h_mut rfl (by decide)
    h_cb h_rp
  have ht := getPlaceAllocMut_sized_of_access_v2' mem mem ⟨st.machine, none⟩
    ⟨mp, lay⟩ true none c1bValAcc.globalHooks c1bValAcc.accessHooks
    c1bValAcc.dynamicLayout ⟨id, allocRange Size.ZERO (Size.ofBytes 16), a⟩
    rfl rfl h_ga_t
  let ⟨hf, h_wr_f⟩ := c1b_wr_pair_false st mem a id
    c1bValAcc.globalHooks c1bValAcc.accessHooks c1bValAcc.dynamicLayout
    h_rp h_find h_live h_mut h_bs rfl rfl
    (c1b_acc_write _ h_bt h_dr _ _ _ _) h_w0 h_w1
  have h_eq : writeImmediateToMplaceNoValidate mem ⟨st.machine, none⟩
      (c1Slice 2 3) ⟨mp, lay⟩ refRuntimeLayoutV2 true none
      c1bValAcc.globalHooks c1bValAcc.accessHooks c1bValAcc.dynamicLayout
      (fun _ => true) =
      writeImmediateToMplaceNoValidate mem ⟨st.machine, none⟩
      (c1Slice 2 3) ⟨mp, lay⟩ refRuntimeLayoutV2 false none
      c1bValAcc.globalHooks c1bValAcc.accessHooks c1bValAcc.dynamicLayout
      (fun _ => true) := by unfold writeImmediateToMplaceNoValidate; rw [ht, hf]
  have h_st : { st with machine := { st.machine with memory := mem } } = st :=
    by cases st; dsimp only at h_mem; subst h_mem; rfl
  dsimp only [refValHooksV2, TypedMachineBindings.bindValidity,
    refValidityHooksV2, ValidityMemory.bind, ValidityMemory.writeNoValidate,
    bind, Bind.bind, pure, Pure.pure]
  rw [h_flay0, show (!c1Sl.layout.isSized) = false from rfl]
  simp only [Bool.false_eq_true, ite_false]; rw [eStateM_bind_ok h_asMp0]
  dsimp only [get, getThe, MonadStateOf.get, EStateM.get,
    refValidityMemoryEnvV2, refValidityMemoryEnv, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [eStateM_bind_ok (show (EStateM.get :
      EStateM Miri.Interpreter.StepError RefMiriState RefMiriState) st =
      .ok st st from rfl)]
  rw [h_mem]; dsimp only [c1bValAcc, refValidityMemoryEnvV2] at h_eq h_wr_f
  rw [show (⟨mp, localMemoryLayout c1Sl⟩ : MemoryOperandPlace Provenance) =
      ⟨mp, lay⟩ from rfl,
    show (refAccessConfigV2 c1Rp.types).runtime = refRuntimeLayoutV2 from rfl,
    h_eq, show (c1Slice 2 3 : Immediate Provenance) =
      .scalarPair (c1PtrSc 2) (c1Usize 3) from rfl, h_wr_f]
  dsimp only
  refine eStateM_apply_bind _ _ () _ _ rfl ?_
  dsimp only [ValidityMemory.Environment.putTouched,
    ValidityMemory.Environment.putMemoryHooks]
  rw [h_st]
  rfl

/-- Pointee layout `[u8]` for `V2_C1` validity checking. -/
noncomputable abbrev c1bSliceLay : LocalLayout :=
  refLocalLayoutForTyV2 c1Rp.types (.slice u8Ty)

/-- Pointee `MemPlace` (`alloc2 + 2`, length `3`) of `&[u8]`. -/
noncomputable abbrev c1bSliceMp : MemPlace Provenance :=
  ⟨⟨Size.ofBytes 2, some (.concrete alloc2IdV2 BorTag.one)⟩,
    .metadata (c1Usize 3), none⟩

/-- Byte alignment `Align.ONE` succeeds for any pointer in `V2_C1`. -/
theorem c1b_misalign1 (ptr : Pointer (Option Provenance))
    (st : RefMiriState) :
    PointerPlaceMachine.misalignmentWith (refAccessConfigV2 c1Rp.types)
      refAlignCtxV2 ptr Align.ONE st = .ok none st := by
  cases st with | mk sk mc => cases mc with | mk m b d t r a u pmd =>
    dsimp only [PointerPlaceMachine.misalignmentWith, refAlignCtxV2]
    cases ptr with | mk off p => cases p <;> rfl

/-- Shared ghost `readImmediate` combiner from `getPlaceAlloc` and
`readImmediate`. -/
private theorem c1b_val_ri_step (st : RefMiriState) (mem : RefMiriMem)
    (a : RefMiriAlloc) (f : RuntimePlace Provenance) (exp : ExpectedValue)
    (mp : MemPlace Provenance) (lay : LocalLayout)
    (layOp : MemoryOperandLayout) (imm : Immediate Provenance)
    (id : Miri.Memory.AllocId) (off sz : Size) (ss : Int)
    (h_mem : st.machine.memory = mem)
    (h_toOp : placeToOp (refBasePlaceProjectionHooksV2 c1Rp.types).place 0 f
      st = .ok ⟨.indirect mp, lay⟩ st)
    (h_lml : localMemoryLayout lay = layOp) (h_sz : sizeAsI64 sz = .ok ss)
    (h_nz : (ss != 0) = true) (h_sz_eq : layOp.size = sz)
    (h_us : layOp.backendRepr.isUnsized = false) (h_aln : mp.misaligned = none)
    (h_find : mem.live.find? (fun e => e.1 == id) = some (id, ⟨.stack, a⟩))
    (h_cb : checkedBounds ⟨Size.ofBytes 8⟩ id a.byteSize off ss
      .memoryAccess = .ok ())
    (h_rp : refResolvePointerPure mp.ptr ss =
      .ok ⟨id, off, .concrete BorTag.one⟩)
    (h_ri : getPlaceAlloc st.machine.memory ⟨st.machine, none⟩ ⟨mp, layOp⟩
        refRuntimeLayoutV2 true none c1bValAcc.globalHooks c1bValAcc.accessHooks
        c1bValAcc.dynamicLayout =
      ⟨st.machine.memory, ⟨st.machine, none⟩, some ⟨id, allocRange off sz, a⟩,
        .ok (some ⟨id, allocRange off sz, a⟩)⟩ →
      Miri.Interpreter.readImmediate st.machine.memory ⟨st.machine, none⟩
        (.indirect mp) layOp refRuntimeLayoutV2 true none c1bValAcc.globalHooks
        c1bValAcc.accessHooks c1bValAcc.dynamicLayout =
      ⟨st.machine.memory, ⟨st.machine, none⟩, some ⟨id, allocRange off sz, a⟩,
        .ok ⟨imm, layOp⟩⟩) :
    (refValHooksV2 c1Rp.types).readImmediate 0 f exp st =
      .ok ⟨imm, lay⟩ st := by
  have h_ga : AllocationAccess.getPtrAlloc st.machine.memory ⟨st.machine, none⟩
      ⟨Size.ofBytes 8⟩ mp.ptr sz true none c1bValAcc.globalHooks
      c1bValAcc.accessHooks =
      ⟨st.machine.memory, ⟨st.machine, none⟩, some ⟨id, allocRange off sz, a⟩,
        .ok (some ⟨id, allocRange off sz, a⟩)⟩ := by
    rw [h_mem]
    exact getPtrAlloc_live_ghost_v2 sz ss mem .stack a st.machine id off mp.ptr
      (.concrete BorTag.one) c1bValAcc.globalHooks c1bValAcc.accessHooks rfl
      h_find h_sz h_nz h_cb (c1b_val_rp mem st.machine mp.ptr ss id off h_rp)
  rw [← h_sz_eq] at h_ga
  have h_gpl := getPlaceAlloc_sized_of_access_v2' st.machine.memory
    st.machine.memory ⟨st.machine, none⟩ ⟨mp, layOp⟩ true none
    c1bValAcc.globalHooks c1bValAcc.accessHooks c1bValAcc.dynamicLayout _
    h_us h_aln h_ga
  rw [h_sz_eq] at h_gpl
  have h_ir := h_ri h_gpl
  dsimp only [refValHooksV2, TypedMachineBindings.bindValidity,
    refValidityHooksV2, ValidityMemory.bind, bind, Bind.bind, pure, Pure.pure]
  change EStateM.bind
    (placeToOp (refBasePlaceProjectionHooksV2 c1Rp.types).place 0 f) _ st = _
  rw [eStateM_bind_ok h_toOp]
  dsimp only [ValidityMemory.readImmediate, get, getThe, MonadStateOf.get,
    EStateM.get, bind, Bind.bind, pure, Pure.pure,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    refValidityMemoryEnvV2, refValidityMemoryEnv]
  rw [eStateM_bind_ok (show (EStateM.get :
      EStateM Miri.Interpreter.StepError RefMiriState RefMiriState) st =
      .ok st st from rfl)]
  dsimp only [c1bValAcc, refValidityMemoryEnvV2] at h_ir
  rw [show (refAccessConfigV2 c1Rp.types).runtime = refRuntimeLayoutV2 from rfl,
    h_lml, h_ir]
  dsimp only
  cases st with
  | mk sk mc =>
    cases mc with
    | mk m b d t r a u pmd =>
      refine eStateM_apply_bind _ _ ()
        (⟨sk, ⟨m, b, d, t, r, a, u, pmd⟩⟩ : RefMiriState)
        (⟨sk, ⟨m, b, d, t, r, a, u, pmd⟩⟩ : RefMiriState) ?_ ?_
      · rfl
      · rfl

/-- Ghost `readImmediate` on slice field `f0` returns `c1Slice 2 3`. -/
theorem c1b_val_ri_sl (st : RefMiriState) (mem : RefMiriMem)
    (m : InitMaskBlocks) (id : Miri.Memory.AllocId)
    (place f0 f1 : RuntimePlace Provenance)
    (hs : C1BValState st mem m id place f0 f1) :
    (refValHooksV2 c1Rp.types).readImmediate 0 f0 .reference st =
      .ok ⟨c1Slice 2 3, c1Sl⟩ st := by
  let a := c1bA3m m; let rng := allocRange Size.ZERO (Size.ofBytes 16)
  refine c1b_val_ri_step st mem a f0 .reference (c1Mp id) c1Sl c1bPairOpLay
    (c1Slice 2 3) id Size.ZERO (Size.ofBytes 16) 16 hs.h_mem hs.h_toOp0 rfl rfl
    (by decide) rfl rfl rfl hs.h_find rfl rfl (fun h_gpl => by
      have h_raw : readImmediateFromMplaceRaw st.machine.memory
          ⟨st.machine, none⟩ ⟨c1Mp id, c1bPairOpLay⟩ refRuntimeLayoutV2 true
          none c1bValAcc.globalHooks c1bValAcc.accessHooks
          c1bValAcc.dynamicLayout =
          ⟨st.machine.memory, ⟨st.machine, none⟩, some ⟨id, rng, a⟩,
            .ok (some ⟨c1Slice 2 3, c1bPairOpLay⟩)⟩ := by
        dsimp only [readImmediateFromMplaceRaw, Id.run, bind, Bind.bind,
          pure, Pure.pure]
        rw [h_gpl]; dsimp only [c1bPairOpLay, BackendRepr.isUnsized]
        simp only [Bool.false_eq_true, ite_false]
        change readImmediateFromMplaceRaw.match_4 _ (Except.bind
          (Except.mapError MemoryOperandError.memoryRange
            (rng.subrange (allocRange Size.ZERO (Size.ofBytes 8))))
          (fun r => Except.mapError MemoryOperandError.allocation
            (a.readScalar refRuntimeLayoutV2.base r true))) _ _ = _
        rw [show rng.subrange (allocRange Size.ZERO (Size.ofBytes 8)) =
            .ok (allocRange Size.ZERO (Size.ofBytes 8)) from rfl]
        dsimp only [Except.mapError, Except.bind]
        rw [c1b_rd_ptr m hs.hm]; dsimp only
        change readImmediateFromMplaceRaw.match_4 _ (Except.bind
          (Except.mapError MemoryOperandError.memoryRange
            (rng.subrange (allocRange (Size.ofBytes 8) (Size.ofBytes 8))))
          (fun r => Except.mapError MemoryOperandError.allocation
            (a.readScalar refRuntimeLayoutV2.base r false))) _ _ = _
        rw [show rng.subrange (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) =
            .ok (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) from rfl]
        dsimp only [Except.mapError, Except.bind]
        rw [c1b_rd_len m hs.hm]; rfl
      dsimp only [Miri.Interpreter.readImmediate, readImmediateRaw, Id.run,
        bind, Bind.bind, pure, Pure.pure]
      rw [h_raw]; rfl)

/-- Ghost `readImmediate` on `usize` field `f1` returns `c1Usize 2`. -/
theorem c1b_val_ri_u64 (st : RefMiriState) (mem : RefMiriMem)
    (m : InitMaskBlocks) (id : Miri.Memory.AllocId)
    (place f0 f1 : RuntimePlace Provenance)
    (hs : C1BValState st mem m id place f0 f1) :
    (refValHooksV2 c1Rp.types).readImmediate 0 f1 .integer st =
      .ok ⟨.scalar (c1Usize 2), c1Us⟩ st := by
  let a := c1bA3m m; let rng := allocRange (Size.ofBytes 16) (Size.ofBytes 8)
  refine c1b_val_ri_step st mem a f1 .integer (c1bMp16' id) c1Us c1bU64OpLay
    (.scalar (c1Usize 2)) id (Size.ofBytes 16) (Size.ofBytes 8) 8 hs.h_mem
    hs.h_toOp1 rfl rfl (by decide) rfl rfl rfl hs.h_find rfl rfl
    (fun h_gpl => by
      have h_raw : readImmediateFromMplaceRaw st.machine.memory
          ⟨st.machine, none⟩ ⟨c1bMp16' id, c1bU64OpLay⟩ refRuntimeLayoutV2
          true none c1bValAcc.globalHooks c1bValAcc.accessHooks
          c1bValAcc.dynamicLayout =
          ⟨st.machine.memory, ⟨st.machine, none⟩, some ⟨id, rng, a⟩,
            .ok (some ⟨.scalar (c1Usize 2), c1bU64OpLay⟩)⟩ := by
        dsimp only [readImmediateFromMplaceRaw, Id.run, bind, Bind.bind,
          pure, Pure.pure]
        rw [h_gpl]; dsimp only [c1bU64OpLay, BackendRepr.isUnsized]
        simp only [Bool.false_eq_true, ite_false]
        change readImmediateFromMplaceRaw.match_3 _ (Except.bind
          (Except.mapError MemoryOperandError.memoryRange
            (rng.subrange (allocRange Size.ZERO (Size.ofBytes 8))))
          (fun r => Except.mapError MemoryOperandError.allocation
            (a.readScalar refRuntimeLayoutV2.base r false))) _ _ = _
        rw [show rng.subrange (allocRange Size.ZERO (Size.ofBytes 8)) =
            .ok rng from rfl]
        dsimp only [Except.mapError, Except.bind]
        rw [c1b_rd_usize m hs.hm]
      dsimp only [Miri.Interpreter.readImmediate, readImmediateRaw, Id.run,
        bind, Bind.bind, pure, Pure.pure]
      rw [h_raw]; rfl)

/-- `DataRangeSet` covering `[0, 16)` after field `.0`. -/
noncomputable abbrev c1bRange016 : Validity.DataRangeSet :=
  exceptOkGet (Validity.DataRangeSet.empty.addRange Size.ZERO
    (Size.ofBytes 16)) rfl

/-- `DataRangeSet` covering `[0, 24)` after both tuple fields. -/
noncomputable abbrev c1bRange024 : Validity.DataRangeSet :=
  exceptOkGet (Validity.DataRangeSet.addRange c1bRange016 (Size.ofBytes 16)
    (Size.ofBytes 8)) rfl

/-- `ValidityVisitor.visit` on slice field `f0`. -/
theorem c1b_visit_slice_field (st : RefMiriState) (mem : RefMiriMem)
    (m : InitMaskBlocks) (id : Miri.Memory.AllocId)
    (place f0 f1 : RuntimePlace Provenance) (p : ValidationPath)
    (hs : C1BValState st mem m id place f0 f1) :
    let sess : ValidityVisitor.Session Provenance :=
      ⟨p, ⟨true, false⟩, none, some .empty, some .empty⟩
    ValidityVisitor.visit (refValHooksV2 c1Rp.types) 0 15 sess f0 st =
      .ok { sess with
        dataBytes := some c1bRange016
        refTracking := some ((Validity.RefTracking.empty).track
          ⟨c1bSliceMp, c1bSliceLay⟩ (fun _ => p.push .deref)) } st := by
  intro sess
  have h_find2' : st.machine.memory.live.find? (fun e => e.1 == alloc2IdV2) =
      some c1Row2 := by rw [hs.h_mem]; exact hs.h_find2
  have h_p2p : (refValHooksV2 c1Rp.types).ptrToPlace 0 ⟨c1Slice 2 3, c1Sl⟩ st =
      .ok ⟨c1bSliceMp, c1bSliceLay⟩ st := by
    dsimp only [refValHooksV2, TypedMachineBindings.bindValidity,
      refValidityHooksV2, ValidityMemory.bind, refFromImmediatePtrV2]
    rw [show resolveTy c1Rp.types c1Sl.ty =
        some (.ref .shared (.slice u8Ty)) from rfl]; dsimp only
    rw [show (c1Slice 2 3).toScalarAndMeta =
        .ok (c1PtrSc 2, .metadata (c1Usize 3)) from rfl]; dsimp only
    rw [show (c1PtrSc 2).toPointer refRuntimeLayoutV2.base =
        .ok ⟨Size.ofBytes 2, some (.concrete alloc2IdV2 BorTag.one)⟩ from rfl]
    dsimp only
    rw [show refTyLayoutFitsU64V2 u8Ty.slice = true from rfl, Bool.not_true,
      ite_false_eq, show c1bSliceLay.layout.align.abi = Align.ONE from rfl,
      c1b_misalign1]
  have h_gai : st.machine.memory.getAllocInfo alloc2IdV2 =
      .ok ⟨Size.ofBytes 5, Align.ONE, .liveData, .Not⟩ := by
    dsimp only [MemoryState.getAllocInfo, bind, Bind.bind, Except.bind]
    rw [h_find2']
    rfl
  have h_chk : checkPtrAccess ⟨(refAccessConfigV2 c1Rp.types).runtime.pointerSize⟩
      c1bSliceMp.ptr (Size.ofBytes 3) (.dereferenceable "pointer")
      (fun _ _ => refResolvePointerPure c1bSliceMp.ptr 3)
      st.machine.memory.getAllocInfo = .ok () := by
    dsimp only [checkPtrAccess, checkAndDerefPtr, bind, Bind.bind,
      Except.bind, pure, Pure.pure, Except.pure]
    rw [show refResolvePointerPure c1bSliceMp.ptr 3 =
        .ok ⟨alloc2IdV2, Size.ofBytes 2, .concrete BorTag.one⟩ from rfl]
    dsimp only
    rw [h_gai]
    rfl
  have h_cpa : (refValHooksV2 c1Rp.types).checkPointerAccess 0 c1bSliceMp.ptr
      (Size.ofBytes 3) st = .ok (.ok ()) st := by
    dsimp only [refValHooksV2, TypedMachineBindings.bindValidity,
      refValidityHooksV2, ValidityMemory.bind, refCheckPointerAccessResultV2]
    rw [show sizeAsI64 (Size.ofBytes 3) = .ok 3 from rfl]
    dsimp only
    rw [show (3 == (0 : Int)) = false from rfl, ite_false_eq]
    change (match checkPtrAccess
        ⟨(refAccessConfigV2 c1Rp.types).runtime.pointerSize⟩ c1bSliceMp.ptr
        (Size.ofBytes 3) (.dereferenceable "pointer")
        (fun _ _ => refResolvePointerPure c1bSliceMp.ptr 3)
        st.machine.memory.getAllocInfo with
      | Except.ok () => EStateM.Result.ok (Except.ok ()) st
      | Except.error e => EStateM.Result.ok (Except.error e) st) = _
    rw [h_chk]
  have h_rtm : ValidityVisitor.retagSafePointer p (.reference false)
      (refValHooksV2 c1Rp.types).retagPointer 0 ⟨c1Slice 2 3, c1Sl⟩ c1Sl.ty
      st = .ok none st := by
    dsimp only [ValidityVisitor.retagSafePointer,
      ValidityVisitor.mapRetagOutcome]
    rw [refValHooksV2_retagPointer c1Rp.types 0 ⟨c1Slice 2 3, c1Sl⟩ c1Sl.ty st
      hs.h_bt]
  have h_ma : ValidityVisitor.mapPointerAlignmentOutcome p (.reference false)
      ((refValHooksV2 c1Rp.types).checkPointerAlignResult 0 c1bSliceMp.ptr
        Align.ONE) st = .ok () st := by
    dsimp only [ValidityVisitor.mapPointerAlignmentOutcome, refValHooksV2,
      TypedMachineBindings.bindValidity, refValidityHooksV2,
      ValidityMemory.bind, refCheckPointerAlignResultV2]
    rw [c1b_misalign1]
  have h_wr0 := c1b_val_reset0_abs st mem (c1bA3m m) id f0 hs.h_mem hs.h_bt
    hs.h_dr hs.h_flay0 hs.h_asMp0 hs.h_find hs.h_live rfl rfl
    (c1b_re_w0 m hs.hm) (c1b_re_w1 m hs.hm)
  rw [ValidityVisitor.visit.eq_2]
  refine eStateM_apply_bind _ _ (.reference false) st st
    (by rw [hs.h_flay0]; rfl) ?_
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  change EStateM.bind (EStateM.bind (EStateM.bind
    ((refValHooksV2 c1Rp.types).readImmediate 0 f0 .reference) _) _) _ st = _
  simp only [eStateM_bind_assoc]
  rw [eStateM_bind_ok (c1b_val_ri_sl st mem m id place f0 f1 hs)]
  dsimp only [sess]
  simp only [ite_true]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  simp only [eStateM_bind_assoc]
  refine eStateM_apply_bind _ _ { sess with dataBytes := some c1bRange016 }
    st st ?_ ?_
  · have h_off : (refValHooksV2 c1Rp.types).toOp 0 f0 st =
        .ok ⟨.indirect (c1Mp id), c1Sl⟩ st := by
      rw [refValHooksV2_toOp, hs.h_toOp0]
    change (if (!f0.layout.layout.isSized) = true then _
      else EStateM.bind
        (EStateM.bind ((refValHooksV2 c1Rp.types).toOp 0 f0) _) _) st =
      .ok { sess with dataBytes := some c1bRange016 } st
    rw [hs.h_flay0, show c1Sl.layout.isSized = true from rfl]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [eStateM_bind_assoc, eStateM_bind_ok h_off]
    rfl
  dsimp only
  rw [eStateM_bind_ok h_p2p]
  dsimp only
  rw [show c1bSliceLay.layout.isSized = false from rfl]
  simp only [Bool.false_eq_true, Bool.not_false, ite_true, eStateM_bind_assoc]
  refine eStateM_apply_bind _ _ () st st ?_ ?_
  · rfl
  rw [eStateM_bind_ok (show (refValHooksV2 c1Rp.types).sizeAndAlign 0
      ⟨c1bSliceMp, c1bSliceLay⟩ st =
      .ok (some (Size.ofBytes 3, Align.ONE)) st from rfl)]
  dsimp only [Option.getD, sess]
  simp only [Bool.false_eq_true, Bool.not_false, ite_true, eStateM_bind_assoc]
  rw [eStateM_bind_ok h_cpa,
    show f0.layout.ty = c1Sl.ty from by rw [hs.h_flay0]]
  dsimp only
  rw [eStateM_bind_assoc, eStateM_bind_ok h_rtm]
  dsimp only
  rw [eStateM_bind_assoc]
  refine eStateM_apply_bind _ _ () st st h_wr0 ?_
  rw [eStateM_bind_assoc]
  refine eStateM_apply_bind _ _ (Scalar.fromPointer refRuntimeLayoutV2.base
    ⟨Size.ofBytes 2, Provenance.concrete alloc2IdV2 BorTag.one⟩) st st ?_ ?_
  · rfl
  rw [eStateM_bind_assoc,
    eStateM_bind_ok (show (refValHooksV2 c1Rp.types).scalarMayBeNull 0
      (Scalar.fromPointer refRuntimeLayoutV2.base
        ⟨Size.ofBytes 2, Provenance.concrete alloc2IdV2 BorTag.one⟩) st =
      .ok false st from rfl)]
  simp only [Bool.false_eq_true, ite_false]
  rw [eStateM_bind_assoc,
    eStateM_bind_ok (show (refValHooksV2 c1Rp.types).opsemInhabited 0
      c1bSliceLay.ty st = .ok true st from rfl)]
  simp only [ite_true]
  rw [eStateM_bind_assoc, eStateM_bind_ok h_ma]
  rfl

/-- `ValidityVisitor.visit` on scalar field `f1`. -/
theorem c1b_visit_u64_field (st : RefMiriState) (mem : RefMiriMem)
    (m : InitMaskBlocks) (id : Miri.Memory.AllocId)
    (place f0 f1 : RuntimePlace Provenance) (p : ValidationPath)
    (rt : Option (Validity.RefTracking
      (ValidityVisitor.Key Provenance) ValidationPath))
    (hs : C1BValState st mem m id place f0 f1) :
    let sess : ValidityVisitor.Session Provenance :=
      ⟨p, ⟨true, false⟩, none, rt, some c1bRange016⟩
    ValidityVisitor.visit (refValHooksV2 c1Rp.types) 0 15 sess f1 st =
      .ok { sess with dataBytes := some c1bRange024 } st := by
  intro sess
  rw [ValidityVisitor.visit.eq_2]
  refine eStateM_apply_bind _ _ .integer st st (by rw [hs.h_flay1]; rfl) ?_
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  change EStateM.bind (EStateM.bind
    ((refValHooksV2 c1Rp.types).readImmediate 0 f1 .integer) _) _ st = _
  simp only [eStateM_bind_assoc]
  rw [eStateM_bind_ok (c1b_val_ri_u64 st mem m id place f0 f1 hs)]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  simp only [eStateM_bind_assoc]
  refine eStateM_apply_bind _ _ (c1Usize 2) st st ?_ ?_
  · rfl
  · rw [show (ValidityVisitor.TypeKind.integer == .boolean) = false from rfl,
      show (ValidityVisitor.TypeKind.integer == .character) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    dsimp only [sess]
    simp only [ite_true, eStateM_bind_assoc]
    rw [eStateM_bind_ok hs.h_clr1]
    refine eStateM_apply_bind _ _ { sess with dataBytes := some c1bRange024 }
      st st ?_ ?_
    · have h_off : (refValHooksV2 c1Rp.types).toOp 0 f1 st =
          .ok ⟨.indirect (c1bMp16' id), c1Us⟩ st := by
        rw [refValHooksV2_toOp, hs.h_toOp1]
      change (if (!f1.layout.layout.isSized) = true then _
        else EStateM.bind
          (EStateM.bind ((refValHooksV2 c1Rp.types).toOp 0 f1) _) _) st =
        .ok { sess with dataBytes := some c1bRange024 } st
      rw [hs.h_flay1, show c1Us.layout.isSized = true from rfl]
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      rw [eStateM_bind_assoc, eStateM_bind_ok h_off]
      rfl
    · rfl

/-- Mirror of one tracked-pointee child visit inside `validatePlace`. -/
def c1bValidateChildMirror {P S C E F A Pad : Type}
    [PointerProvenance P] [DecidableEq P]
    (h : ValidityVisitor.Hooks P S C E F A Pad) (c : C) (fuel : Nat)
    (key : ValidityVisitor.Key P) (path : ValidationPath) :
    ValidityVisitor.M S Unit :=
  h.withGhostValidation
    (let child : RuntimePlace P := ⟨.memory key.mplace, key.layout⟩
     Bind.bind
       (ValidityVisitor.visit h c fuel
         { path, flags := ⟨false, true⟩, ctfeMode := none,
           refTracking := none, dataBytes := none } child)
       (fun visited => refResetPaddingMirror h c visited child))

/-- Worklist runs one tracked child mirror and immediately terminates. -/
theorem c1b_validatePost_child (types : List MirTy)
    (sess : ValidityVisitor.Session Provenance) (st st' : RefMiriState)
    (key : ValidityVisitor.Key Provenance) (path : ValidationPath)
    (tracking : Validity.RefTracking
      (ValidityVisitor.Key Provenance) ValidationPath)
    (h_next : sess.refTracking.bind Validity.RefTracking.next =
      some ((key, path), tracking))
    (h_child : c1bValidateChildMirror (refValHooksV2 types) 0 16 key path st =
      .ok () st')
    (h_next2 : (some tracking).bind Validity.RefTracking.next = none) :
    refValidatePostMirror (refValHooksV2 types) 0 16 true sess st =
      .ok () st' := by
  dsimp only [refValidatePostMirror, bind, Bind.bind, pure, Pure.pure]
  rw [ite_true_eq, eStateM_loop_forIn_eq st]
  dsimp only [bind, Bind.bind, pure, Pure.pure, ite_true_eq]; rw [h_next]
  dsimp only; rw [show (16 == 0) = false from rfl, ite_false_eq]
  change EStateM.bind (EStateM.bind (EStateM.bind
    (c1bValidateChildMirror (refValHooksV2 types) 0 16 key path) _) _) _ st =
    _
  rw [eStateM_bind3_ok h_child,
    eStateM_bind2_ok (show (EStateM.pure _ :
      EStateM StepError RefMiriState _) st' = _ from rfl)]
  dsimp only; rw [eStateM_loop_forIn_eq st']
  dsimp only [bind, Bind.bind, pure, Pure.pure, ite_true_eq]; rw [h_next2]
  dsimp only; rw [eStateM_bind_pure_fn]
  dsimp only; rw [eStateM_loop_forIn_eq st', ite_false_eq]; rfl

/-- Whole `validatePlace` (root tuple + recursive slice child) succeeds. -/
theorem c1b_validate_tup (st : RefMiriState) (mem : RefMiriMem)
    (m : InitMaskBlocks) (id : Miri.Memory.AllocId)
    (place f0 f1 : RuntimePlace Provenance)
    (hs : C1BValState st mem m id place f0 f1)
    (h_child : c1bValidateChildMirror (refValHooksV2 c1Rp.types) 0 16
      ⟨c1bSliceMp, c1bSliceLay⟩
      ⟨"", Array.mk [.tupleElem 0, .deref]⟩ st = .ok () st) :
    ValidityVisitor.validatePlace (refValHooksV2 c1Rp.types) 0 16 place true
      true st = .ok () st := by
  let p0 : ValidationPath := ⟨"", Array.mk [.tupleElem 0]⟩
  let p1 : ValidationPath := ⟨"", Array.mk [.tupleElem 1]⟩
  let key0 : ValidityVisitor.Key Provenance := ⟨c1bSliceMp, c1bSliceLay⟩
  let rt1 : Validity.RefTracking (ValidityVisitor.Key Provenance)
      ValidationPath := Validity.RefTracking.empty.track key0
        (fun _ => p0.push .deref)
  let sess2 : ValidityVisitor.Session Provenance :=
    ⟨⟨"", Array.mk []⟩, ⟨true, false⟩, none, some rt1, some c1bRange024⟩
  have h_vis : ValidityVisitor.visit (refValHooksV2 c1Rp.types) 0 16
      ⟨⟨"", Array.mk []⟩, ⟨true, false⟩, none, some .empty, some .empty⟩
      place st = .ok sess2 st := by
    rw [ValidityVisitor.visit.eq_2]
    refine eStateM_apply_bind _ _ (.aggregate false false false) st st
      (by rw [hs.h_play]; rfl) ?_
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    refine eStateM_apply_bind _ _ none st st rfl ?_
    dsimp only
    rw [show (ValidityVisitor.TypeKind.aggregate false false false == .box) =
        false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [hs.h_play, show c1Tup.layout.fields =
        .Arbitrary (Array.mk [Size.ZERO, Size.ofBytes 16]) (Array.mk [0, 1])
        from rfl]
    dsimp only
    rw [← Array.forIn_toList,
      show (Array.mk [0, 1] : Array Nat).toList = [0, 1] from rfl,
      List.forIn_cons]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    simp only [eStateM_bind_assoc]
    rw [eStateM_bind_ok hs.h_field0]
    rw [eStateM_bind_ok (show (refValHooksV2 c1Rp.types).fieldPath 0 c1Tup 0
      f0.layout.ty st = .ok (.tupleElem 0) st from rfl)]
    simp only [Bool.false_or]
    rw [show ({ originalType := "" } : ValidationPath).push (.tupleElem 0) =
      p0 from rfl]
    rw [eStateM_bind_ok (c1b_visit_slice_field st mem m id place f0 f1 p0 hs)]
    dsimp only
    rw [eStateM_bind_pure]
    dsimp only
    rw [List.forIn_cons]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    simp only [eStateM_bind_assoc]
    rw [eStateM_bind_ok hs.h_field1]
    rw [eStateM_bind_ok (show (refValHooksV2 c1Rp.types).fieldPath 0 c1Tup 1
      f1.layout.ty st = .ok (.tupleElem 1) st from rfl)]
    rw [show ({ originalType := "" } : ValidationPath).push (.tupleElem 1) =
      p1 from rfl]
    rw [eStateM_bind_ok (c1b_visit_u64_field st mem m id place f0 f1 p1
      (some rt1) hs)]
    dsimp only
    rw [eStateM_bind_pure]
    dsimp only [List.forIn_nil, pure, Pure.pure]
    rw [eStateM_bind_pure]
    rw [show c1Tup.layout.variants = .Single 0 from rfl]
    dsimp only
    rw [eStateM_bind_ok (show (refValHooksV2 c1Rp.types).opsemInhabited 0
        c1Tup.ty st = .ok true st from rfl),
      show (refValHooksV2 c1Rp.types).debugAssertions = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rfl
  have h_pre : refValidatePreMirror (refValHooksV2 c1Rp.types) 0 16 place
      true true st = .ok sess2 st := by
    dsimp only [refValidatePreMirror, bind, Bind.bind, pure, Pure.pure]
    rw [eStateM_bind_ok (refValHooksV2_typeName c1Rp.types 0 _ st),
      refValHooksV2_withGhostValidation, ite_true_eq]
    dsimp only [EStateM.bind]; rw [refValHooksV2_toOp, hs.h_toOpP]
    dsimp only; rw [ite_true_eq]; dsimp only [EStateM.bind]; rw [h_vis]
    dsimp only [refResetPaddingMirror, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure, sess2]
    rw [show (refValHooksV2 c1Rp.types).projection.place =
        (refBasePlaceProjectionHooksV2 c1Rp.types).place from rfl, hs.h_fa]
    dsimp only
    rw [show (refValHooksV2 c1Rp.types).sizeAndAlign 0 ⟨c1Mp id, c1Tup⟩ st =
        .ok (some (c1Tup.layout.size, c1Tup.layout.align.abi)) st from rfl]
    dsimp only [Option.getD]
    rw [show (c1Mp id).ptr.offset = Size.ZERO from rfl,
      show c1Tup.layout.size = Size.ofBytes 24 from rfl]
    simp only [show (c1bRange024.toArray ==
        Array.mk [allocRange Size.ZERO (Size.ofBytes 24)]) = true from rfl,
      ite_true]
    rfl
  have h_nx : (some rt1).bind Validity.RefTracking.next =
      some ((key0, p0.push .deref), ⟨Array.mk [key0], Array.empty⟩) := by
    dsimp only [rt1]; rw [Validity.RefTracking.track, ← Array.any_toList]; rfl
  rw [refValidatePlace_split_v2]
  exact eStateM_apply_bind _ _ sess2 st st h_pre
    (c1b_validatePost_child c1Rp.types sess2 st st key0 (p0.push .deref) _
      h_nx h_child rfl)

/-- Step 5 (`(bb3, 0)`): `_0 = (move _5, move _7)` moves `_0` to stack
allocation `alloc5` and validates the pair + pointee slice. -/
theorem c1_step_5 :
    ExecutionMachine.step (refExecutionConfigV2 c1Rp) refLimitsV2 0 c1S_bb3 =
      (c1bS1, .ok true) := by
  have h_val := c1b_validate_tup c1bS0 (c1bMem (c1bLive c1bA3) Array.empty)
    (.Materialized ⟨Array.mk [0xFFFFFF]⟩) alloc5IdV2 c1bDest c1bF0 c1bF1
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, .inl rfl⟩ rfl
  have h_ass : (ExecutionMachine.stepHooks (refExecutionConfigV2 c1Rp)
      refLimitsV2).assign 0 ⟨0, Array.empty⟩
      (.Aggregate .Tuple
        (Array.mk [.Move ⟨5, Array.empty⟩, .Move ⟨7, Array.empty⟩]))
      c1S_bb3 = (c1bS0, .ok ()) := by
    dsimp only [MachineHooks.run, Call.run, ExecutionMachine.stepHooks]
    rw [show ExecutionMachine.withValidation (refExecutionConfigV2 c1Rp)
        refLimitsV2 = refExecCfgV2 c1Rp from rfl]
    dsimp only [ExecutionMachine.rvalueHooks, evalRvalueIntoPlace,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [refStepCfgV2_eq,
      show PlaceDynamic.evalPlace
        (ExecutionMachine.projectionHooks (refExecCfgV2 c1Rp)) 0
        ⟨0, Array.empty⟩ true c1S_bb3 = .ok c1bDest c1S_bb3 from rfl]
    dsimp only; rw [writeAggregate_tuple2_v2]
    dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [show PlaceDynamic.field
        (ExecutionMachine.projectionHooks (refExecCfgV2 c1Rp)) 0 c1bDest 0
        c1S_bb3 = .ok c1bF0 c1S_bb3 from rfl]; dsimp only
    rw [show OperandMachine.evalOperandAt
        (ExecutionMachine.operandHooks (refExecCfgV2 c1Rp)) 0
        (.aggregate 0) (.Move ⟨5, Array.empty⟩) (some c1Sl) c1S_bb3 =
        .ok ⟨.immediate (c1Slice 2 3), c1Sl⟩ c1bSa from rfl]
    dsimp only; rw [c1b_copy0]; dsimp only
    rw [show PlaceDynamic.field
        (ExecutionMachine.projectionHooks (refExecCfgV2 c1Rp)) 0 c1bDest 1
        (c1bSm 0 c1U c1Two c1bA2) =
        .ok c1bF1 (c1bSm 0 c1U c1Two c1bA2) from rfl]; dsimp only
    rw [show OperandMachine.evalOperandAt
        (ExecutionMachine.operandHooks (refExecCfgV2 c1Rp)) 0
        (.aggregate 1) (.Move ⟨7, Array.empty⟩) (some c1Us)
        (c1bSm 0 c1U c1Two c1bA2) =
        .ok ⟨.immediate (.scalar (c1Usize 2)), c1Us⟩
          (c1bSm 0 c1U c1U c1bA2) from rfl]
    dsimp only; rw [c1b_copy1]; dsimp only
    rw [show Discriminant.writeDiscriminant
        (ExecutionMachine.discriminantHooks (refExecCfgV2 c1Rp)) 0 0 c1bDest
        c1bS0 = .ok () c1bS0 from rfl]; dsimp only
    rw [show (refExecCfgV2 c1Rp).compiler.enforceValidity 0 c1Tup c1bS0 =
        .ok true c1bS0 from rfl]; dsimp only; simp only [ite_true]
    rw [show (refExecCfgV2 c1Rp).compiler.validate 0 c1bDest c1bS0 =
        ValidityVisitor.validatePlace (refValHooksV2 c1Rp.types) 0 16
          c1bDest true true c1bS0 from rfl, h_val]
  exact execStep_assign_ok c1Rp c1S_bb3 c1bS0 (c1Frame 3 0 _) (c1Frame 3 0 _)
    3 0 (c1Block 3) _ ⟨0, Array.empty⟩
    (.Aggregate .Tuple
      (Array.mk [.Move ⟨5, Array.empty⟩, .Move ⟨7, Array.empty⟩]))
    rfl rfl rfl rfl rfl rfl h_ass rfl rfl

/-- Uniform initialization copy descriptor of the 24-byte `c1bA3` buffer. -/
theorem c1b_init_prep :
    c1bA3.initializationMask.prepareCopy
      (allocRange Size.ZERO (Size.ofBytes 24)) =
      .ok ⟨true, Array.mk [24]⟩ := by
  have h_wf : InitMask.WriteProof.WellFormed c1bA3.initializationMask := by
    change (24 ≤ (Array.mk [0xFFFFFF]).size * 64); decide
  exact InitMask.WriteProof.prepareCopy_of_uniform c1bA3.initializationMask
    (allocRange Size.ZERO (Size.ofBytes 24)) (Size.ofBytes 24) true
    h_wf rfl (by decide) (by decide)
    ((InitMask.WriteProof.isRangeInitialized_nonempty_iff
      c1bA3.initializationMask (allocRange Size.ZERO (Size.ofBytes 24))
      (Size.ofBytes 24) h_wf rfl (by decide) (by decide)).1.mp rfl)

/-- Allocation-level 24-byte copy from `c1bA3` into `c1bA0` produces `c1bR1`. -/
theorem c1b_ret_copy_alloc :
    Allocation.copyRepeatedly c1bA3
      (allocRange Size.ZERO (Size.ofBytes 24)) Size.ZERO 1
      (Size.ofBytes 8) false true c1bA0 = .ok () c1bR1 := by
  let p := Provenance.concrete alloc2IdV2 BorTag.one
  let srcPm := refMkProvV2 (Array.mk c1bPtrs)
  have h_src : ProvenanceMap.insertPtr Size.ZERO p (Size.ofBytes 8)
      (ProvenanceMap.new : ProvenanceMap Provenance) = .ok () srcPm := by
    rw [ProvenanceMap.insertPtr_new Size.ZERO (Size.ofBytes 8) (Size.ofBytes 8)
      p (by decide) rfl]; rfl
  let ⟨prep, h_prep, _, h_app, _⟩ := c1_provMap_copy24 p srcPm
    (Array.mk (c1bB8 2 ++ c1bB8 3 ++ c1bB8 2))
    (Array.mk (c1bB8 0 ++ c1bB8 0 ++ c1bB8 0)) h_src
  have h_prep_eq : prep = ⟨Array.mk [(Size.ZERO, p)], Array.empty⟩ := by
    rw [show srcPm.prepareCopy (allocRange Size.ZERO (Size.ofBytes 24))
        (Array.mk (c1bB8 2 ++ c1bB8 3 ++ c1bB8 2)) (Size.ofBytes 8) =
        .ok ⟨Array.mk [(Size.ZERO, p)], Array.empty⟩ from rfl] at h_prep
    exact (Except.ok.inj h_prep).symm
  rw [h_prep_eq] at h_app
  have h_ip := c1b_init_prep
  rw [show c1bA3.initializationMask =
      ⟨.Materialized ⟨Array.mk [0xFFFFFF]⟩, Size.ofBytes 24⟩ from rfl] at h_ip
  unfold Allocation.copyRepeatedly
  dsimp only [bind, Bind.bind, pure, Pure.pure, Except.bind, Except.pure,
    Id.run]
  change (match InitMask.prepareCopy ⟨.Materialized ⟨Array.mk [0xFFFFFF]⟩,
      Size.ofBytes 24⟩ (allocRange Size.ZERO (Size.ofBytes 24)) with
    | .ok _ => _ | .error _ => _) = _
  rw [h_ip]; dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    show (1 : UInt64).toNat = 1 from rfl, Std.Legacy.Range.size,
    List.range', List.forIn_cons, List.forIn_nil]
  have h_ac := InitMask.WriteProof.applyCopy_singleton
    ⟨.Lazy true, Size.ofBytes 24⟩ Size.ZERO (Size.ofBytes 24) (Size.ofBytes 24)
    1 true (by decide) rfl
  rw [show (Size.ofBytes 24).bytes = 24 from rfl] at h_ac
  change (match (⟨.Lazy true, Size.ofBytes 24⟩ : InitMask).applyCopy
      ⟨true, Array.mk [24]⟩ (allocRange Size.ZERO (Size.ofBytes 24)) 1 with
    | .ok _ => _ | .error _ => _) = _
  rw [h_ac]; dsimp only
  rw [show (⟨.Lazy true, Size.ofBytes 24⟩ : InitMask).setRange
      (allocRange Size.ZERO (Size.ofBytes 24)) true =
      .ok ⟨.Lazy true, Size.ofBytes 24⟩ from rfl]
  dsimp only [pure, Pure.pure, Id.run]
  change Miri.Memory.Allocation.writeBytes.match_2 _
    (ProvenanceMap.applyCopy ⟨Array.mk [(Size.ZERO, p)], Array.empty⟩
      (allocRange Size.ZERO (Size.ofBytes 24)) 1
      (ProvenanceMap.new : ProvenanceMap Provenance)) _ _ = _
  rw [h_app]
  rfl

/-- State after `beforeTerminator` advances control to step `4`. -/
noncomputable def c1bStMid : RefMiriState :=
  c1StS 3 1 (c1bLocals (c1M alloc5IdV2) c1U c1U)
    (c1bMem (c1bLive c1bA3) Array.empty) (c1Ctrl 4) c1bSpans

/-- Live rows once the 24-byte return copy completes (`c1bR1`). -/
noncomputable def c1bLiveRetB : Array C1Row :=
  Array.mk [c1Row2, c1Row8 alloc3IdV2, c1Row8 alloc4IdV2,
    (alloc5IdV2, ⟨.stack, c1bA3⟩), (retAllocIdV2, ⟨.stack, c1bR1⟩)]

/-- Post-pop state before copying the return tuple. -/
noncomputable def c1bStE : RefMiriState := { c1bStMid with stack := ⟨Array.empty⟩ }

/-- Post-copy state before stack cleanup deallocates locals `_0`, `_4`, `_6`. -/
noncomputable def c1bStE' : RefMiriState :=
  { c1bStE with
    machine := { c1bStE.machine with
      memory := c1bMem c1bLiveRetB Array.empty } }

private noncomputable def c1bSnapChecks {K U : Type}
    (config : PlaceMachine.AccessConfig K U)
    (source : Allocation Provenance Miri.TreeBorrows.BorrowTree)
    (range : AllocRange) (pointerSize : Size) : MachineHooks.M K U Unit :=
  let __do_jp := fun bytes =>
    let __do_jp2 := fun (_ : Unit) =>
      match source.initializationMask.prepareCopy range with
      | .ok _ => EStateM.pure ()
      | .error error =>
        EStateM.throw (config.memoryError (.allocation (.memory error)))
    match source.provenanceMap.prepareCopy range bytes pointerSize with
    | .ok _ => __do_jp2 ()
    | .error error =>
      EStateM.bind
        (EStateM.throw (config.memoryError (.allocation (.provenance error))))
        __do_jp2
  match source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) with
  | .ok bytes => EStateM.bind (EStateM.pure bytes) __do_jp
  | .error error =>
    EStateM.bind (EStateM.throw (config.memoryError (.allocation error)))
      __do_jp

/-- `GlobalMemoryCopyMachine.typedCopy` copies `_0` (`alloc5`) into `ret`. -/
theorem c1b_ret_typedCopy :
    GlobalMemoryCopyMachine.typedCopy (refExecCfgV2 c1Rp).access
      (refExecCfgV2 c1Rp).addresses (refExecCfgV2 c1Rp).arithmetic
      (refExecCfgV2 c1Rp).projection.dynamic
      (refExecCfgV2 c1Rp).projection.dynamicFuel
      (refExecCfgV2 c1Rp).compiler.debugAssertions 0
      ⟨c1Mp alloc5IdV2, c1Tup⟩ ⟨retMemPlaceV2, c1Tup⟩ c1bStE =
      .ok () c1bStE' := by
  let gh := MemoryCopyMachine.genericHooks (refExecCfgV2 c1Rp).access
    (refExecCfgV2 c1Rp).addresses (refExecCfgV2 c1Rp).arithmetic
  have h_acc : ∀ (w : Bool) (id : Miri.Memory.AllocId) (off sz : Size)
      (tr : Miri.TreeBorrows.BorrowTree)
      (m : MachineHooks.MachineState Unit RefUser),
      m.borrowTracker = none → m.dataRace = none →
      PlaceMachine.memoryAccess (refExecCfgV2 c1Rp).access w ⟨m, none⟩
        tr id (.concrete BorTag.one) (allocRange off sz) =
      ⟨⟨m, none⟩, tr, .ok ()⟩ := by
    intro w id off sz tr m hbt hdr
    cases m; dsimp only at hbt hdr; subst hbt hdr; cases w <;> rfl
  let c1bStEA : RefMiriState :=
    { c1bStE with
      machine := { c1bStE.machine with
        memory := c1bMem
          (Array.mk [c1Row2, c1Row8 alloc3IdV2, c1Row8 alloc4IdV2,
            (alloc5IdV2, ⟨.stack, c1bA3⟩), (retAllocIdV2, ⟨.stack, c1bA0⟩)])
          Array.empty } }
  have h_gc : GlobalMemoryCopyMachine.genericCopy (refExecCfgV2 c1Rp).access
      (refExecCfgV2 c1Rp).addresses (refExecCfgV2 c1Rp).arithmetic
      (c1Mp alloc5IdV2).ptr retMemPlaceV2.ptr (Size.ofBytes 24) 1 true
      c1bStE = .ok () c1bStE' := by
    let cfg := refExecCfgV2 c1Rp
    dsimp only [GlobalMemoryCopyMachine.genericCopy, bind, Bind.bind,
      pure, Pure.pure, get, getThe, MonadStateOf.get, EStateM.get, set,
      MonadStateOf.set, EStateM.set]
    refine eStateM_apply_bind _ _
      (some (alloc5IdV2, Size.ZERO,
        Miri.Memory.ProvenanceExtra.concrete BorTag.one))
      c1bStE c1bStE ?_ ?_
    · rfl
    rw [show Size.mul (Size.ofBytes 24) 1 = .ok (Size.ofBytes 24) from rfl]
    dsimp only
    rw [eStateM_bind_pure]
    refine eStateM_apply_bind _ _
      (some (retAllocIdV2, Size.ZERO,
        Miri.Memory.ProvenanceExtra.concrete BorTag.one))
      c1bStE c1bStE ?_ ?_
    · rfl
    rw [eStateM_bind_ok (show (EStateM.get :
        MachineHooks.M Unit RefUser RefMiriState) c1bStE = .ok c1bStE c1bStE
      from rfl)]
    dsimp only
    rw [show gh.tryGetAllocId c1bStE.machine.memory ⟨c1bStE.machine, none⟩
        (c1Mp alloc5IdV2).ptr (Size.ofBytes 24).bytes = none from rfl]
    dsimp only
    refine eStateM_apply_bind _ _ c1bA3 c1bStE c1bStE ?_ ?_
    · rfl
    rw [show cfg.access.ghostMode = false from rfl, ite_false_eq]
    refine eStateM_apply_bind _ _ c1bA3 c1bStE c1bStE ?_ ?_
    · change (if ((PlaceMachine.memoryAccess cfg.access false
          ⟨c1bStE.machine, none⟩ c1bA3.extra alloc5IdV2
          (ProvenanceExtra.concrete BorTag.one)
          (allocRange Size.ZERO (Size.ofBytes 24))).state.machine.memory.live.any
          fun entry => entry.1 == alloc5IdV2) = true
        then (_ : MachineHooks.M Unit RefUser _) else _) c1bStE =
        .ok c1bA3 c1bStE
      rw [h_acc false alloc5IdV2 _ (Size.ofBytes 24) _ _ rfl rfl]
      dsimp only
      rw [show (c1bStE.machine.memory.live.any fun entry =>
          entry.1 == alloc5IdV2) = true from by rw [← Array.any_toList]; rfl]
      simp only [ite_true]
      rw [show c1bA3.setExtra c1bA3.extra = c1bA3 from rfl,
        show c1bStE.machine.memory.setLiveAllocation alloc5IdV2 c1bA3 =
          .ok c1bStE.machine.memory from rfl]
      rfl
    refine eStateM_apply_bind _ _ () c1bStE c1bStE ?_ ?_
    · have hget : c1bA3.getBytesUnchecked (allocRange Size.ZERO c1bA3.byteSize) =
          .ok ((Array.mk (c1bB8 2 ++ c1bB8 3 ++ c1bB8 2)).extract 0 24) := rfl
      have h1 : c1bA3.getBytesUnchecked (allocRange Size.ZERO c1bA3.byteSize) =
          .ok (Array.mk (c1bB8 2 ++ c1bB8 3 ++ c1bB8 2)) :=
        hget.trans (congrArg Except.ok
          (by apply Array.ext'; rw [Array.toList_extract]; rfl))
      have h2 : c1bA3.provenanceMap.prepareCopy
          (allocRange Size.ZERO (Size.ofBytes 24))
          (Array.mk (c1bB8 2 ++ c1bB8 3 ++ c1bB8 2)) (Size.ofBytes 8) =
          .ok ⟨Array.mk [(Size.ZERO,
            Provenance.concrete alloc2IdV2 BorTag.one)], Array.empty⟩ := by
        dsimp only [c1bA3, c1bA3m, c1bBuf, refMkAllocV2,
          Allocation.provenanceMap]
        rfl
      change c1bSnapChecks cfg.access c1bA3
        (allocRange Size.ZERO (Size.ofBytes 24))
        (refExecCfgV2 c1Rp).arithmetic.pointerSize c1bStE = .ok () c1bStE
      dsimp only [c1bSnapChecks]
      rw [h1]
      dsimp only [EStateM.pure, EStateM.bind]
      rw [show (refExecCfgV2 c1Rp).arithmetic.pointerSize = Size.ofBytes 8
          from rfl, h2]
      dsimp only
      rw [c1b_init_prep]
      rfl
    refine eStateM_apply_bind _ _ c1bA0 c1bStE c1bStE ?_ ?_
    · rfl
    refine eStateM_apply_bind _ _ () c1bStE c1bStE ?_ ?_
    · rfl
    refine eStateM_apply_bind _ _ c1bA0 c1bStE c1bStEA ?_ ?_
    · change (if ((PlaceMachine.memoryAccess cfg.access true
          ⟨c1bStE.machine, none⟩ c1bA0.extra retAllocIdV2
          (ProvenanceExtra.concrete BorTag.one)
          (allocRange Size.ZERO (Size.ofBytes 24))).state.machine.memory.live.any
          fun entry => entry.1 == retAllocIdV2) = true
        then (_ : MachineHooks.M Unit RefUser _) else _) c1bStE =
        .ok c1bA0 c1bStEA
      rw [h_acc true retAllocIdV2 _ (Size.ofBytes 24) _ _ rfl rfl]
      dsimp only
      rw [show (c1bStE.machine.memory.live.any fun entry =>
          entry.1 == retAllocIdV2) = true from by rw [← Array.any_toList]; rfl]
      simp only [ite_true]
      rw [show c1bA0.setExtra c1bA0.extra = c1bA0 from rfl,
        show c1bStE.machine.memory.setLiveAllocation retAllocIdV2 c1bA0 =
          .ok c1bStEA.machine.memory from rfl]
      rfl
    rw [show (alloc5IdV2 == retAllocIdV2) = false from rfl,
      show (refExecCfgV2 c1Rp).arithmetic.pointerSize = Size.ofBytes 8 from rfl,
      c1b_ret_copy_alloc]
    dsimp only
    rw [eStateM_bind_ok (show (EStateM.get :
        MachineHooks.M Unit RefUser RefMiriState) c1bStEA = .ok c1bStEA c1bStEA
      from rfl)]
    rw [show c1bStEA.machine.memory.setLiveAllocation retAllocIdV2 c1bR1 =
        .ok c1bStE'.machine.memory from rfl]
    rfl
  dsimp only [GlobalMemoryCopyMachine.typedCopy,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [show DynamicLayout.sizeAndAlignFromMeta
      (refExecCfgV2 c1Rp).projection.dynamic 0
      (refExecCfgV2 c1Rp).projection.dynamicFuel retMemPlaceV2.metadata c1Tup
      c1bStE = .ok (some (Size.ofBytes 24, Align.EIGHT)) c1bStE from rfl]
  dsimp only
  rw [show (refExecCfgV2 c1Rp).compiler.debugAssertions = false from rfl,
    ite_false_eq, bne_self_eq_false, ite_false_eq, eStateM_bind_ok h_gc]; rfl

/-- Full `copyRuntimePlace` of `_0` into `retMemPlaceV2` with validation. -/
theorem c1b_ret_copy :
    copyRuntimePlace
      (ExecutionMachine.projectionHooks (refExecCfgV2 c1Rp)).place
      (refExecCfgV2 c1Rp).copy 0 ⟨.indirect (c1Mp alloc5IdV2), c1Tup⟩
      ⟨.memory retMemPlaceV2, c1Tup⟩ true c1bStE = .ok () c1bStE' := by
  have h_val := c1b_validate_tup c1bStE'
    (c1bMem c1bLiveRetB Array.empty) (.Lazy true)
    retAllocIdV2 ⟨.memory retMemPlaceV2, c1Tup⟩ ⟨.memory retMemPlaceV2, c1Sl⟩
    ⟨.memory (c1bMp16' retAllocIdV2), c1Us⟩
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, .inr rfl⟩ rfl
  have h_mc : (refExecCfgV2 c1Rp).copy.memoryCopy 0
      ⟨c1Mp alloc5IdV2, c1Tup⟩ ⟨retMemPlaceV2, c1Tup⟩ c1bStE =
      .ok () c1bStE' := by
    dsimp only [refExecCfgV2, ExecutionMachine.withValidation]
    exact c1b_ret_typedCopy
  have h_nv : copyRuntimePlaceNoValidate
      (ExecutionMachine.projectionHooks (refExecCfgV2 c1Rp)).place
      (refExecCfgV2 c1Rp).copy 0 ⟨.indirect (c1Mp alloc5IdV2), c1Tup⟩
      ⟨.memory retMemPlaceV2, c1Tup⟩ true c1bStE = .ok () c1bStE' := by
    dsimp only [copyRuntimePlaceNoValidate, bind, Bind.bind, pure, Pure.pure]
    rw [show (refExecCfgV2 c1Rp).copy.compatible c1Tup c1Tup = .ok true
        from rfl, placeLift_ok]
    dsimp only [pure, Pure.pure]; rw [eStateM_bind_pure_fn]
    simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
    rw [show (refExecCfgV2 c1Rp).copy.hasPadding c1Tup = .ok true from rfl,
      placeLift_ok]
    dsimp only [pure, Pure.pure]
    rw [eStateM_bind_pure_fn,
      eStateM_bind_ok (show (ExecutionMachine.projectionHooks
        (refExecCfgV2 c1Rp)).place.takePendingMoveDeinit c1bStE =
        .ok false c1bStE from rfl), ite_true_eq, eStateM_bind_pure_fn]
    dsimp only
    rw [eStateM_bind_ok (show Miri.Interpreter.forceAllocation
        (ExecutionMachine.projectionHooks (refExecCfgV2 c1Rp)).place 0
        ⟨.memory retMemPlaceV2, c1Tup⟩ c1bStE =
        .ok ⟨retMemPlaceV2, c1Tup⟩ c1bStE from rfl),
      eStateM_bind_ok h_mc, ite_false_eq]; rfl
  dsimp only [copyRuntimePlace, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]
  rw [h_nv]; dsimp only
  rw [show (ExecutionMachine.projectionHooks
      (refExecCfgV2 c1Rp)).place.enforceValidity 0 c1Tup c1bStE' =
      .ok true c1bStE' from rfl]; dsimp only
  rw [ite_true_eq, bne_self_eq_false, ite_false_eq,
    show (ExecutionMachine.projectionHooks (refExecCfgV2 c1Rp)).place.validate
      0 ⟨.memory retMemPlaceV2, c1Tup⟩ c1bStE' =
      ValidityVisitor.validatePlace (refValHooksV2 c1Rp.types) 0 16
        ⟨.memory retMemPlaceV2, c1Tup⟩ true true c1bStE' from rfl]
  exact h_val

/-- Terminal reference memory for `V2_C1`. -/
noncomputable def c1bMemEnd : RefMiriMem :=
  c1bMem (Array.mk [c1Row2, (retAllocIdV2, ⟨.stack, c1bR1⟩)])
    (Array.mk [⟨alloc5IdV2, Size.ofBytes 24, Align.EIGHT⟩,
      ⟨alloc3IdV2, Size.ofBytes 8, Align.EIGHT⟩,
      ⟨alloc4IdV2, Size.ofBytes 8, Align.EIGHT⟩])

/-- Terminal reference machine state for `V2_C1`. -/
noncomputable def c1bSend : RefMiriState :=
  { c1bStE with machine := { c1bStE.machine with memory := c1bMemEnd } }

/-- Root frame cleanup deallocates `_0`, `_4`, and `_6` in local order. -/
theorem c1b_cleanup :
    CallMachine.cleanup
      { refLifecycle c1Rp.types with storage := refStorageHooksV2 c1Rp.types }
      0 false (c1Frame 3 1 (c1bLocals (c1M alloc5IdV2) c1U c1U)) c1bStE' =
      .ok .normal c1bSend := by
  let mkD : RefMiriMem → RefMiriState := fun m =>
    { c1bStE with machine := { c1bStE.machine with memory := m } }
  let stD0 := mkD (c1bMem
    (Array.mk [c1Row2, c1Row8 alloc3IdV2, c1Row8 alloc4IdV2,
      (retAllocIdV2, ⟨.stack, c1bR1⟩)])
    (Array.mk [⟨alloc5IdV2, Size.ofBytes 24, Align.EIGHT⟩]))
  let stD1 := mkD (c1bMem
    (Array.mk [c1Row2, c1Row8 alloc4IdV2, (retAllocIdV2, ⟨.stack, c1bR1⟩)])
    (Array.mk [⟨alloc5IdV2, Size.ofBytes 24, Align.EIGHT⟩,
      ⟨alloc3IdV2, Size.ofBytes 8, Align.EIGHT⟩]))
  have h_d0 : refDeallocateStackV2 (c1Mp alloc5IdV2).ptr c1bStE' =
      .ok () stD0 := by
    dsimp only [refDeallocateStackV2, MemoryLifecycle.deallocatePtrWith, Id.run,
      bind, Bind.bind, pure, Pure.pure]; simp only [← Array.any_toList]; rfl
  have h_d1 : refDeallocateStackV2 (c1Mp alloc3IdV2).ptr stD0 =
      .ok () stD1 := by
    dsimp only [refDeallocateStackV2, MemoryLifecycle.deallocatePtrWith, Id.run,
      bind, Bind.bind, pure, Pure.pure]; simp only [← Array.any_toList]; rfl
  have h_d2 : refDeallocateStackV2 (c1Mp alloc4IdV2).ptr stD1 =
      .ok () c1bSend := by
    dsimp only [refDeallocateStackV2, MemoryLifecycle.deallocatePtrWith, Id.run,
      bind, Bind.bind, pure, Pure.pure]; simp only [← Array.any_toList]; rfl
  dsimp only [CallMachine.cleanup, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]
  rw [show (c1Frame 3 1 (c1bLocals (c1M alloc5IdV2) c1U c1U)).returnContinuation
      = .stop true from rfl]
  dsimp only; simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [← Array.forIn_toList,
    show (c1Frame 3 1 (c1bLocals (c1M alloc5IdV2) c1U c1U)).locals.toList =
      [⟨c1M alloc5IdV2, some c1Tup⟩, ⟨c1I (c1Slice 0 5), some c1Sl⟩,
       ⟨c1U, some c1Us⟩, ⟨c1U, some c1Sl⟩, ⟨c1M alloc3IdV2, some c1RTo⟩,
       ⟨c1U, some c1Sl⟩, ⟨c1M alloc4IdV2, some c1RFrom⟩, ⟨c1U, some c1Us⟩]
      from rfl,
    show (refStorageHooksV2 c1Rp.types).deallocateStack =
      refDeallocateStackV2 from rfl]
  simp only [List.forIn_cons, List.forIn_nil, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, h_d0, h_d1, h_d2]; rfl

/-- Step 6 (`(bb3, 1)`): `Return` copies the tuple to `retPlace` and frees
local stack buffers `_0`, `_4`, and `_6`, ending with `c1bSend`. -/
theorem c1_step_6 :
    ExecutionMachine.step (refExecutionConfigV2 c1Rp) refLimitsV2 0 c1bS1 =
      (c1bSend, .ok true) := by
  have h_bt : (ExecutionMachine.stepHooks (refExecutionConfigV2 c1Rp)
      refLimitsV2).beforeTerminator 0 c1bS1 = (c1bStMid, .ok ()) := rfl
  have h_retOp : (ExecutionMachine.projectionHooks
      (refExecCfgV2 c1Rp)).place.localToOp 0 0 c1bStMid =
      .ok ⟨.indirect (c1Mp alloc5IdV2), c1Tup⟩ c1bStMid := rfl
  have h_rf := returnFromCurrentFrame_op_at_v2 c1Rp c1bStMid
    (.indirect (c1Mp alloc5IdV2)) c1TupTy ⟨retMemPlaceV2, c1Tup⟩
    (c1Frame 3 1 (c1bLocals (c1M alloc5IdV2) c1U c1U)) 3 1
    (Array.mk ((@GetElem.getElem _ Nat _ _ _ c1Body.basicBlocks 3
      (by decide)).statements.map (toMiriStatementV2 c1Rp.types)))
    (c1bMem c1bLiveRetB Array.empty) c1bMemEnd
    rfl rfl rfl rfl rfl rfl rfl h_retOp c1b_cleanup c1b_ret_copy
  exact execStep_term_ok c1Rp c1bS1 c1bStMid c1bSend
    (c1Frame 3 1 (c1bLocals (c1M alloc5IdV2) c1U c1U)) 3 1 (c1Block 3)
    rfl rfl rfl rfl rfl h_bt h_rf

/-- Return readback decodes `c1bR1` to `(&[30, 40, 50], 2usize)` and confirms
caller confinement and reference validity. -/
theorem c1_ret_val :
    refReadReturnValV2 c1bMemEnd callerMemV2_C1 c1TupTy
        ⟨retMemPlaceV2, c1Tup⟩ =
      .ok (.tuple [.slicePtr ⟨some 2, 2, .isize⟩ 3,
        .scalar ⟨.isize, false, BitVec.ofNat 128 2⟩]) := by
  dsimp only [refReadReturnValV2, retMemPlaceV2, retPtrV2,
    refTyLayoutFitsU64V2, refTupleLayoutFitsU64V2, refNatFitsU64V2,
    Bool.not_true, ite_false]
  rw [show c1bMemEnd.live.find? (fun entry => entry.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, c1bR1⟩) from rfl]
  dsimp only [refReadValFromAllocV2, refTupleLayoutFitsU64V2,
    refTyLayoutFitsU64V2, refNatFitsU64V2, Bool.not_true, ite_false]
  rw [show (refTupleFieldsLayoutV2 0 0 [c1SliceTy, c1UsizeTy]).1 =
      [Size.ZERO, Size.ofBytes 16] from rfl]
  dsimp only [refReadTupleFieldsFromAllocV2, refReadValFromAllocV2,
    refReadScalarIntFromAllocV2]
  rw [show Size.ofBytes (UInt64.ofNat (0 + Size.ZERO.bytes.toNat)) =
      Size.ZERO from rfl,
    show Size.ofBytes (UInt64.ofNat (0 + Size.ZERO.bytes.toNat + 8)) =
      Size.ofBytes 8 from rfl,
    show Size.ofBytes (UInt64.ofNat (0 + (Size.ofBytes 16).bytes.toNat)) =
      Size.ofBytes 16 from rfl,
    show toMiriSize .isize = Size.ofBytes 8 from rfl,
    c1b_rd_ptr (.Lazy true) (.inr rfl), c1b_rd_len (.Lazy true) (.inr rfl),
    c1b_rd_usize (.Lazy true) (.inr rfl)]; rfl

/-- Caller memory extraction at return matches `callerMemV2_C1`. -/
theorem c1_ret_mem :
    refExtractCallerMemoryV2 callerMemV2_C1 c1bMemEnd = callerMemV2_C1 := rfl

end C1BackProof

/-! ## Section 6: End-to-End Lockstep for `V2_C1` -/

/-- Seven reference-machine steps take the `V2_C1` entry state to `outV2_C1`. -/
theorem c1_exec :
    refCoreExecV2 c1Rp c1TupTy ⟨retMemPlaceV2, c1Tup⟩
      (fun o => o = outV2_C1) False False 7 c1S_entry := by
  rw [refCoreExecV2_step_ok_v2 c1_step_0 rfl,
    refCoreExecV2_step_ok_v2 c1_step_1 rfl,
    refCoreExecV2_step_ok_v2 c1_step_2 rfl,
    refCoreExecV2_step_ok_v2 c1_step_3 rfl,
    refCoreExecV2_step_ok_v2 c1_step_4 rfl,
    refCoreExecV2_step_ok_v2 c1_step_5 rfl,
    refCoreExecV2_return_ok_v2 c1_step_6 rfl c1_ret_val]
  exact congrArg
    (fun cm => TerminalOut.returned
      ⟨.tuple [.slicePtr ⟨some 2, 2, .isize⟩ 3,
        .scalar ⟨.isize, false, BitVec.ofNat 128 2⟩], cm⟩)
    c1_ret_mem

/-- `V2_C1` (slice split via `RangeTo`/`RangeFrom` aggregates and
`slice::len`): Anneal and the reference machine agree on the unique returned
output `outV2_C1`. -/
theorem V2_C1_splitAt_lockstep :
    WellFormedV2 progV2_C1_splitAt queryV2_C1 ∧
    BehaviorV2 progV2_C1_splitAt queryV2_C1 outV2_C1 ∧
    ¬ DivergesV2 progV2_C1_splitAt queryV2_C1 ∧
    RefWellFormedV2 (encodeProg progV2_C1_splitAt) queryV2_C1 ∧
    RefBehaviorV2 (encodeProg progV2_C1_splitAt) queryV2_C1 outV2_C1 ∧
    (∀ out', RefBehaviorV2 (encodeProg progV2_C1_splitAt) queryV2_C1
      out' → out' = outV2_C1) ∧
    ¬ RefDivergesV2 (encodeProg progV2_C1_splitAt) queryV2_C1 :=
  let ⟨h_wf, h_beh, h_nd, _⟩ := c1_m_anneal
  let ⟨h_rwf, h_rbeh, h_uniq, h_rnd⟩ := ref_ok_of_coreExec c1_init c1_exec
  ⟨h_wf, h_beh, h_nd, h_rwf, h_rbeh, h_uniq, h_rnd⟩

end Anneal.MirCorrespondence
