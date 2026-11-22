-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace ZirconHandleAndReactorInvariants

/-!
# Constructive Zircon Handle-Transfer, Multi-Process Quotient, and Reactor Invariants

Self-contained `Type 0` `prelude` formalization (`leanprover/lean4` `v4.34.1`,
zero axioms, zero `_unsafe_rec`, zero `noncomputable`, Pass-1 `TrustedBoundary`
syntax-clean) accompanying the reference report
`fuchsia-zircon-channel-handle-linearity-and-vdso-syscall-semantics`:

1. **All-handle error-path consumption (`sysChannelWriteReal_consumes_all_handles`):**
   Models Zircon's `prepare_write` `zr::defer` cleanup (`channel.rs:297-301`,
   `user_handles.rs:361-446`) and proves that for *every* handle list `hs` and
   every non-zero `h ∈ hs`, all six success and failure branches (including
   unreadable `bytes` and invalid `options`) remove `h` whenever the `handles`
   array is readable, while `ZX_HANDLE_OP_DUPLICATE` preserves source handles
   and invalid disposition opcodes (`op != ZX_HANDLE_OP_DUPLICATE`) consume them.
2. **Even/Odd `ObjId` quotient rebinding counterexample (`even_odd_quotient_rebinds_transferred_handle`):**
   Demonstrates how encoding Process 1 / Process 2 kernel object IDs via `2 * id` /
   `2 * id + 1` and projecting/writing back via `id / 2` silently rebinds an
   in-flight cross-channel handle `(objId = 2 * id)` onto the receiver's private
   object `(2 * id + 1)`.
3. **Reactive prefix-trace allowlist confinement, tight per-wakeup step bounds,
   shared-slot exhaustion counterexample, and quota-partitioned 2-run
   non-interference:** Contrastive proof that a shared `MAX_SLOTS` pool violates
   2-run tenant non-interference under slot-exhaustion attacks, whereas per-tenant
   slot quotas preserve exact sequence-ordered `obsB` equivalence across arbitrary
   adversarial Tenant-A schedules.
-/

/-! ## Part 1: Zircon Handle-Consuming Syscall Semantics -/

abbrev ZxHandle := Nat
abbrev ObjId := Nat
abbrev ZxRights := Nat

def ZX_HANDLE_INVALID : ZxHandle := 0
def ZX_RIGHT_TRANSFER : ZxRights := 1
def ZX_RIGHT_DUPLICATE : ZxRights := 2
def ZX_RIGHT_WRITE : ZxRights := 4

inductive ZxStatus : Type where
  | ok : ZxStatus
  | invalidArgs : ZxStatus
  | badHandle : ZxStatus
  | accessDenied : ZxStatus
  | peerClosed : ZxStatus
  | outOfRange : ZxStatus

inductive HandleOp : Type where
  | move : HandleOp
  | duplicate : HandleOp
  | invalid (raw : Nat) : HandleOp

structure HandleEntry : Type where
  handle : ZxHandle
  objId : ObjId
  rights : ZxRights

structure HandleDisposition : Type where
  op : HandleOp
  handle : ZxHandle

def hasWriteRight (rights : ZxRights) : Bool :=
  Nat.beq (Nat.mod (Nat.div rights 4) 2) 1

def lookupHandle (tbl : List HandleEntry) (h : ZxHandle) : Option HandleEntry :=
  List.foldr
    (fun e acc => match Nat.beq e.handle h with | true => some e | false => acc)
    none
    tbl

def removeHandle (tbl : List HandleEntry) (h : ZxHandle) : List HandleEntry :=
  match Nat.beq h ZX_HANDLE_INVALID with
  | true => tbl
  | false =>
    List.foldr
      (fun e acc => match Nat.beq e.handle h with | true => acc | false => e :: acc)
      []
      tbl

def removeHandles (tbl : List HandleEntry) (hs : List ZxHandle) : List HandleEntry :=
  List.foldr (fun h acc => removeHandle acc h) tbl hs

def containsHandle (hs : List ZxHandle) (target : ZxHandle) : Bool :=
  List.foldr
    (fun h acc => match Nat.beq h target with | true => true | false => acc)
    false
    hs

def removeNonDupDispositions (tbl : List HandleEntry) (ds : List HandleDisposition) :
    List HandleEntry :=
  List.foldr
    (fun d acc =>
      match d.op with
      | .duplicate => acc
      | .move => removeHandle acc d.handle
      | .invalid _ => removeHandle acc d.handle)
    tbl
    ds

def sysChannelWriteReal
    (tbl : List HandleEntry)
    (chanHandle : ZxHandle)
    (optionsZero : Bool)
    (withinMaxLimits : Bool)
    (bytesReadable : Bool)
    (handlesReadable : Bool)
    (peerOpen : Bool)
    (handles : List ZxHandle) : ZxStatus × List HandleEntry :=
  let consumedTbl := match handlesReadable with | true => removeHandles tbl handles | false => tbl
  match optionsZero with
  | false => (.invalidArgs, consumedTbl)
  | true =>
    match lookupHandle tbl chanHandle with
    | none => (.badHandle, consumedTbl)
    | some chEntry =>
      match hasWriteRight chEntry.rights with
      | false => (.accessDenied, consumedTbl)
      | true =>
        match withinMaxLimits with
        | false => (.outOfRange, consumedTbl)
        | true =>
          match bytesReadable with
          | false => (.invalidArgs, consumedTbl)
          | true =>
            match handlesReadable with
            | false => (.invalidArgs, tbl)
            | true =>
              match peerOpen with
              | false => (.peerClosed, consumedTbl)
              | true => (.ok, consumedTbl)

theorem nat_beq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change Nat.beq k k = true
    exact ih

theorem nat_beq_eq (a b : Nat) (h : Nat.beq a b = true) : a = b := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => cases h
  | succ a' ih =>
    intro b h
    cases b with
    | zero => cases h
    | succ b' =>
      have h' : Nat.beq a' b' = true := h
      rw [ih b' h']

theorem lookup_removeHandle_self (tbl : List HandleEntry) (h : ZxHandle)
    (hNonZero : Nat.beq h ZX_HANDLE_INVALID = false) :
    lookupHandle (removeHandle tbl h) h = none := by
  unfold removeHandle
  rw [hNonZero]
  dsimp only
  induction tbl with
  | nil => rfl
  | cons hd tl ih =>
    unfold List.foldr
    cases hEq : Nat.beq hd.handle h with
    | true =>
      dsimp only
      exact ih
    | false =>
      dsimp only
      unfold lookupHandle
      unfold List.foldr
      rw [hEq]
      dsimp only
      exact ih

theorem lookup_removeHandle_preserves_none (tbl : List HandleEntry) (x h : ZxHandle)
    (hNone : lookupHandle tbl h = none) :
    lookupHandle (removeHandle tbl x) h = none := by
  unfold removeHandle
  cases Nat.beq x ZX_HANDLE_INVALID with
  | true => exact hNone
  | false =>
    dsimp only
    induction tbl with
    | nil => rfl
    | cons hd tl ih =>
      unfold lookupHandle at hNone
      unfold List.foldr at hNone
      cases hHd : Nat.beq hd.handle h with
      | true =>
        rw [hHd] at hNone
        cases hNone
      | false =>
        rw [hHd] at hNone
        dsimp only at hNone
        unfold List.foldr
        cases Nat.beq hd.handle x with
        | true =>
          dsimp only
          exact ih hNone
        | false =>
          dsimp only
          unfold lookupHandle
          unfold List.foldr
          rw [hHd]
          dsimp only
          exact ih hNone

theorem removeHandles_consumes_member (tbl : List HandleEntry) (hs : List ZxHandle) (h : ZxHandle)
    (hMem : containsHandle hs h = true)
    (hNonZero : Nat.beq h ZX_HANDLE_INVALID = false) :
    lookupHandle (removeHandles tbl hs) h = none := by
  induction hs with
  | nil => cases hMem
  | cons x rest ih =>
    unfold containsHandle at hMem
    unfold List.foldr at hMem
    unfold removeHandles
    unfold List.foldr
    change lookupHandle (removeHandle (removeHandles tbl rest) x) h = none
    cases hEq : Nat.beq x h with
    | true =>
      rw [nat_beq_eq x h hEq]
      exact lookup_removeHandle_self (removeHandles tbl rest) h hNonZero
    | false =>
      rw [hEq] at hMem
      dsimp only at hMem
      exact lookup_removeHandle_preserves_none (removeHandles tbl rest) x h (ih hMem)

theorem sysChannelWriteReal_consumes_all_handles
    (tbl : List HandleEntry)
    (chanHandle h : ZxHandle)
    (hs : List ZxHandle)
    (optionsZero withinMaxLimits bytesReadable peerOpen : Bool)
    (hMem : containsHandle hs h = true)
    (hNonZero : Nat.beq h ZX_HANDLE_INVALID = false) :
    lookupHandle
      (sysChannelWriteReal tbl chanHandle optionsZero withinMaxLimits bytesReadable true peerOpen hs).2
      h = none := by
  unfold sysChannelWriteReal
  dsimp only
  have hRem : lookupHandle (removeHandles tbl hs) h = none :=
    removeHandles_consumes_member tbl hs h hMem hNonZero
  cases optionsZero with
  | false => exact hRem
  | true =>
    dsimp only
    cases lookupHandle tbl chanHandle with
    | none => exact hRem
    | some chEntry =>
      dsimp only
      cases hasWriteRight chEntry.rights with
      | false => exact hRem
      | true =>
        dsimp only
        cases withinMaxLimits with
        | false => exact hRem
        | true =>
          dsimp only
          cases bytesReadable with
          | false => exact hRem
          | true =>
            dsimp only
            cases peerOpen with
            | false => exact hRem
            | true => exact hRem

def sampleTable : List HandleEntry :=
  [ { handle := 3, objId := 10, rights := 4 }
  , { handle := 7, objId := 20, rights := 1 }
  , { handle := 11, objId := 30, rights := 1 } ]

theorem unreadable_handles_slice_preserves_table_control :
    lookupHandle (sysChannelWriteReal sampleTable 3 true true true false true [7, 11]).2 11
      = some { handle := 11, objId := 30, rights := 1 } :=
  rfl

theorem unreadable_bytes_still_consumes_all_handles :
    (sysChannelWriteReal sampleTable 3 true true false true true [7, 11]).1 = .invalidArgs ∧
    lookupHandle (sysChannelWriteReal sampleTable 3 true true false true true [7, 11]).2 7 = none ∧
    lookupHandle (sysChannelWriteReal sampleTable 3 true true false true true [7, 11]).2 11 = none :=
  ⟨rfl, rfl, rfl⟩

theorem invalid_disposition_opcode_consumes_unlike_duplicate :
    lookupHandle (removeNonDupDispositions sampleTable [{ op := .invalid 99, handle := 7 }]) 7 = none ∧
    lookupHandle (removeNonDupDispositions sampleTable [{ op := .duplicate, handle := 7 }]) 7
      = some { handle := 7, objId := 20, rights := 1 } :=
  ⟨rfl, rfl⟩

/-! ## Part 2: Even/Odd `ObjId` Quotient Rebinding Counterexample -/

def encodeProc1Obj (localId : ObjId) : ObjId := 2 * localId
def encodeProc2Obj (localId : ObjId) : ObjId := 2 * localId + 1
def decodeSharedObj (sharedId : ObjId) : ObjId := Nat.div sharedId 2

/-- When Process 1 transfers a handle to its local object `localId` (shared `2 * localId`)
    into Process 2's receive queue, projecting Process 2's view via `decodeSharedObj`
    and writing Process 2's slice back via `encodeProc2Obj` silently rewrites the queued
    handle's `ObjId` to `2 * localId + 1` (Process 2's own private object)! -/
theorem even_odd_quotient_rebinds_transferred_handle :
    encodeProc2Obj (decodeSharedObj (encodeProc1Obj 0)) = encodeProc2Obj 0 ∧
    Nat.beq (encodeProc2Obj (decodeSharedObj (encodeProc1Obj 0))) (encodeProc1Obj 0) = false :=
  ⟨rfl, rfl⟩

/-! ## Part 3: Chronological Reactor Prefix Safety, Step Bounds, & Slot-Quota Non-Interference -/

inductive Tenant : Type where
  | slotA : Tenant
  | slotB : Tenant

inductive PacketKind : Type where
  | openSubChannel : PacketKind
  | request (payloadValid : Bool) (payloadTag : Nat) : PacketKind

structure InboundPacket : Type where
  target : Tenant
  kind : PacketKind

structure OutboundEvent : Type where
  tenant : Tenant
  replyTag : Nat

structure TenantState : Type where
  activeSlots : Nat
  acceptedOpens : Nat
  requestCount : Nat

structure HandlerOutcome : Type where
  nextTenant : TenantState
  emitted : Option OutboundEvent
  steps : Nat

/-- Step-metered per-tenant handler with explicit `slotQuota` cap. -/
def stepTenant (t : Tenant) (slotQuota : Nat) (st : TenantState) (k : PacketKind) : HandlerOutcome :=
  match k with
  | .openSubChannel =>
    match Nat.blt st.activeSlots slotQuota with
    | true =>
      { nextTenant := { st with activeSlots := st.activeSlots + 1, acceptedOpens := st.acceptedOpens + 1 }
        emitted := none
        steps := 14 }
    | false =>
      { nextTenant := st, emitted := none, steps := 6 }
  | .request payloadValid payloadTag =>
    match Nat.blt 0 st.activeSlots with
    | false => { nextTenant := st, emitted := none, steps := 4 }
    | true =>
      match payloadValid with
      | false =>
        { nextTenant := { st with activeSlots := st.activeSlots - 1 }
          emitted := none
          steps := 12 }
      | true =>
        match Nat.blt payloadTag 26 with
        | true =>
          { nextTenant := { st with requestCount := st.requestCount + 1 }
            emitted := some { tenant := t, replyTag := payloadTag }
            steps := 19 }
        | false =>
          { nextTenant := { st with activeSlots := st.activeSlots - 1 }
            emitted := none
            steps := 15 }

/-- Counterexample: Unpartitioned shared slot pool (`totalCap`) allows Tenant A to
    exhaust all slots and alter Tenant B's observable `acceptedOpens`! -/
structure SharedPoolState : Type where
  usedTotal : Nat
  opensA : Nat
  opensB : Nat

def stepSharedOpen (totalCap : Nat) (s : SharedPoolState) (t : Tenant) : SharedPoolState :=
  match Nat.blt s.usedTotal totalCap with
  | false => s
  | true =>
    match t with
    | .slotA => { s with usedTotal := s.usedTotal + 1, opensA := s.opensA + 1 }
    | .slotB => { s with usedTotal := s.usedTotal + 1, opensB := s.opensB + 1 }

theorem shared_slot_pool_violates_noninterference :
    (stepSharedOpen 1 { usedTotal := 0, opensA := 0, opensB := 0 } .slotB).opensB = 1 ∧
    (stepSharedOpen 1 (stepSharedOpen 1 { usedTotal := 0, opensA := 0, opensB := 0 } .slotA) .slotB).opensB = 0 :=
  ⟨rfl, rfl⟩

/-- Quota-partitioned reactor state (`quotaA`, `quotaB`) with chronological trace append. -/
structure PartitionedReactor : Type where
  stateA : TenantState
  stateB : TenantState
  traceRev : List OutboundEvent

def pushEvent (ev? : Option OutboundEvent) (tr : List OutboundEvent) : List OutboundEvent :=
  match ev? with
  | none => tr
  | some e => e :: tr

def dispatchPartitioned (quotaA quotaB : Nat) (r : PartitionedReactor) (pkt : InboundPacket) :
    PartitionedReactor :=
  match pkt.target with
  | .slotA =>
    let out := stepTenant .slotA quotaA r.stateA pkt.kind
    { r with stateA := out.nextTenant, traceRev := pushEvent out.emitted r.traceRev }
  | .slotB =>
    let out := stepTenant .slotB quotaB r.stateB pkt.kind
    { r with stateB := out.nextTenant, traceRev := pushEvent out.emitted r.traceRev }

def wakeupSteps (quotaA quotaB : Nat) (r : PartitionedReactor) (pkt : InboundPacket) : Nat :=
  let hSteps :=
    match pkt.target with
    | .slotA => (stepTenant .slotA quotaA r.stateA pkt.kind).steps
    | .slotB => (stepTenant .slotB quotaB r.stateB pkt.kind).steps
  16 + hSteps + 25

/-- Chronological left-to-right execution (`pkt` executes first, then `rest`),
    implemented via `List.foldr` CPS without `_unsafe_rec`! -/
def runChronological (quotaA quotaB : Nat) (r0 : PartitionedReactor) (sched : List InboundPacket) :
    PartitionedReactor :=
  (List.foldr
    (fun pkt cont r => cont (dispatchPartitioned quotaA quotaB r pkt))
    (fun r => r)
    sched) r0

theorem runChronological_nil (qA qB : Nat) (r : PartitionedReactor) :
    runChronological qA qB r [] = r :=
  rfl

theorem runChronological_cons (qA qB : Nat) (r : PartitionedReactor)
    (pkt : InboundPacket) (rest : List InboundPacket) :
    runChronological qA qB r (pkt :: rest) =
      runChronological qA qB (dispatchPartitioned qA qB r pkt) rest :=
  rfl

def TraceAllowlistSafe (tr : List OutboundEvent) : Bool :=
  List.foldr (fun ev ok => Nat.blt ev.replyTag 26 && ok) true tr

theorem stepTenant_allowlist_safe (t : Tenant) (q : Nat) (st : TenantState) (k : PacketKind)
    (tr : List OutboundEvent) (hSafe : TraceAllowlistSafe tr = true) :
    TraceAllowlistSafe (pushEvent (stepTenant t q st k).emitted tr) = true := by
  unfold stepTenant
  cases k with
  | openSubChannel =>
    cases Nat.blt st.activeSlots q with
    | true => exact hSafe
    | false => exact hSafe
  | request payloadValid payloadTag =>
    dsimp only
    cases Nat.blt 0 st.activeSlots with
    | false => exact hSafe
    | true =>
      dsimp only
      cases payloadValid with
      | false => exact hSafe
      | true =>
        dsimp only
        cases hTag : Nat.blt payloadTag 26 with
        | false =>
          dsimp only
          exact hSafe
        | true =>
          dsimp only
          change (Nat.blt payloadTag 26 && TraceAllowlistSafe tr) = true
          rw [hTag]
          exact hSafe

theorem dispatchPartitioned_preserves_allowlist (qA qB : Nat) (r : PartitionedReactor)
    (pkt : InboundPacket) (hSafe : TraceAllowlistSafe r.traceRev = true) :
    TraceAllowlistSafe (dispatchPartitioned qA qB r pkt).traceRev = true := by
  unfold dispatchPartitioned
  cases pkt.target with
  | slotA => exact stepTenant_allowlist_safe .slotA qA r.stateA pkt.kind r.traceRev hSafe
  | slotB => exact stepTenant_allowlist_safe .slotB qB r.stateB pkt.kind r.traceRev hSafe

theorem runChronological_allowlist_safe (qA qB : Nat) (sched : List InboundPacket) :
    ∀ r : PartitionedReactor,
      TraceAllowlistSafe r.traceRev = true →
      TraceAllowlistSafe (runChronological qA qB r sched).traceRev = true := by
  induction sched with
  | nil =>
    intro r hSafe
    exact hSafe
  | cons pkt rest ih =>
    intro r hSafe
    rw [runChronological_cons]
    exact ih (dispatchPartitioned qA qB r pkt)
      (dispatchPartitioned_preserves_allowlist qA qB r pkt hSafe)

theorem wakeupSteps_dos_bound (qA qB : Nat) (r : PartitionedReactor) (pkt : InboundPacket) :
    Nat.ble (wakeupSteps qA qB r pkt) 60 = true := by
  unfold wakeupSteps
  dsimp only
  cases pkt.target with
  | slotA =>
    dsimp only
    unfold stepTenant
    cases pkt.kind with
    | openSubChannel =>
      dsimp only
      cases Nat.blt r.stateA.activeSlots qA with
      | true => rfl
      | false => rfl
    | request pv pt =>
      dsimp only
      cases Nat.blt 0 r.stateA.activeSlots with
      | false => rfl
      | true =>
        dsimp only
        cases pv with
        | false => rfl
        | true =>
          dsimp only
          cases Nat.blt pt 26 with
          | true => rfl
          | false => rfl
  | slotB =>
    dsimp only
    unfold stepTenant
    cases pkt.kind with
    | openSubChannel =>
      dsimp only
      cases Nat.blt r.stateB.activeSlots qB with
      | true => rfl
      | false => rfl
    | request pv pt =>
      dsimp only
      cases Nat.blt 0 r.stateB.activeSlots with
      | false => rfl
      | true =>
        dsimp only
        cases pv with
        | false => rfl
        | true =>
          dsimp only
          cases Nat.blt pt 26 with
          | true => rfl
          | false => rfl

def filterTraceB (tr : List OutboundEvent) : List OutboundEvent :=
  List.foldr
    (fun ev acc => match ev.tenant with | .slotA => acc | .slotB => ev :: acc)
    []
    tr

def obsB (r : PartitionedReactor) : TenantState × List OutboundEvent :=
  (r.stateB, filterTraceB r.traceRev)

def filterSchedB (sched : List InboundPacket) : List InboundPacket :=
  List.foldr
    (fun pkt acc => match pkt.target with | .slotA => acc | .slotB => pkt :: acc)
    []
    sched

theorem filterSchedB_cons_slotA (pkt : InboundPacket) (rest : List InboundPacket)
    (hT : pkt.target = .slotA) :
    filterSchedB (pkt :: rest) = filterSchedB rest := by
  change (match pkt.target with | .slotA => filterSchedB rest | .slotB => pkt :: filterSchedB rest) = filterSchedB rest
  rw [hT]

theorem filterSchedB_cons_slotB (pkt : InboundPacket) (rest : List InboundPacket)
    (hT : pkt.target = .slotB) :
    filterSchedB (pkt :: rest) = pkt :: filterSchedB rest := by
  change (match pkt.target with | .slotA => filterSchedB rest | .slotB => pkt :: filterSchedB rest) = pkt :: filterSchedB rest
  rw [hT]

theorem filterTraceB_push_slotA (q : Nat) (st : TenantState) (k : PacketKind) (tr : List OutboundEvent) :
    filterTraceB (pushEvent (stepTenant .slotA q st k).emitted tr) = filterTraceB tr := by
  unfold stepTenant
  cases k with
  | openSubChannel =>
    dsimp only
    cases Nat.blt st.activeSlots q with
    | true => rfl
    | false => rfl
  | request pv pt =>
    dsimp only
    cases Nat.blt 0 st.activeSlots with
    | false => rfl
    | true =>
      dsimp only
      cases pv with
      | false => rfl
      | true =>
        dsimp only
        cases Nat.blt pt 26 with
        | true => rfl
        | false => rfl

theorem filterTraceB_push_slotB (q : Nat) (st : TenantState) (k : PacketKind)
    (tr1 tr2 : List OutboundEvent) (hTr : filterTraceB tr1 = filterTraceB tr2) :
    filterTraceB (pushEvent (stepTenant .slotB q st k).emitted tr1) =
    filterTraceB (pushEvent (stepTenant .slotB q st k).emitted tr2) := by
  unfold stepTenant
  cases k with
  | openSubChannel =>
    dsimp only
    cases Nat.blt st.activeSlots q with
    | true => exact hTr
    | false => exact hTr
  | request pv pt =>
    dsimp only
    cases Nat.blt 0 st.activeSlots with
    | false => exact hTr
    | true =>
      dsimp only
      cases pv with
      | false => exact hTr
      | true =>
        dsimp only
        cases Nat.blt pt 26 with
        | false => exact hTr
        | true =>
          dsimp only [pushEvent]
          change OutboundEvent.mk .slotB pt :: filterTraceB tr1 =
                 OutboundEvent.mk .slotB pt :: filterTraceB tr2
          rw [hTr]

theorem dispatch_slotA_preserves_obsB (qA qB : Nat) (r : PartitionedReactor) (pkt : InboundPacket)
    (hT : pkt.target = .slotA) :
    obsB (dispatchPartitioned qA qB r pkt) = obsB r := by
  unfold dispatchPartitioned
  rw [hT]
  dsimp only
  unfold obsB
  dsimp only
  rw [filterTraceB_push_slotA]

theorem dispatch_slotB_commutes_obsB (qA qB : Nat) (r1 r2 : PartitionedReactor) (pkt : InboundPacket)
    (hT : pkt.target = .slotB) (hEq : obsB r1 = obsB r2) :
    obsB (dispatchPartitioned qA qB r1 pkt) = obsB (dispatchPartitioned qA qB r2 pkt) := by
  unfold obsB at hEq
  injection hEq with hStB hTrB
  unfold dispatchPartitioned
  rw [hT, hStB]
  dsimp only
  unfold obsB
  dsimp only
  rw [filterTraceB_push_slotB qB r2.stateB pkt.kind r1.traceRev r2.traceRev hTrB]

theorem runChronological_congr_obsB (qA qB : Nat) (sb : List InboundPacket) :
    ∀ r1 r2 : PartitionedReactor,
      obsB r1 = obsB r2 →
      obsB (runChronological qA qB r1 sb) = obsB (runChronological qA qB r2 sb) := by
  induction sb with
  | nil =>
    intro r1 r2 hEq
    exact hEq
  | cons pkt rest ih =>
    intro r1 r2 hEq
    rw [runChronological_cons, runChronological_cons]
    cases hT : pkt.target with
    | slotA =>
      apply ih
      rw [dispatch_slotA_preserves_obsB qA qB r1 pkt hT]
      rw [dispatch_slotA_preserves_obsB qA qB r2 pkt hT]
      exact hEq
    | slotB =>
      apply ih
      exact dispatch_slotB_commutes_obsB qA qB r1 r2 pkt hT hEq

theorem runChronological_eq_filtered (qA qB : Nat) (sched : List InboundPacket) :
    ∀ r : PartitionedReactor,
      obsB (runChronological qA qB r sched) =
      obsB (runChronological qA qB r (filterSchedB sched)) := by
  induction sched with
  | nil =>
    intro r
    rfl
  | cons pkt rest ih =>
    intro r
    cases hT : pkt.target with
    | slotA =>
      rw [runChronological_cons, filterSchedB_cons_slotA pkt rest hT]
      rw [ih (dispatchPartitioned qA qB r pkt)]
      exact runChronological_congr_obsB qA qB (filterSchedB rest)
        (dispatchPartitioned qA qB r pkt) r
        (dispatch_slotA_preserves_obsB qA qB r pkt hT)
    | slotB =>
      rw [runChronological_cons, filterSchedB_cons_slotB pkt rest hT, runChronological_cons]
      exact ih (dispatchPartitioned qA qB r pkt)

/-- Chronological Quota-Partitioned 2-Run Non-Interference:
    Unlike `SharedPoolState` above, partitioning slot quotas (`qA`, `qB`) guarantees
    that arbitrary Tenant-A subchannel opens, request floods, and malformed messages
    have zero effect on Tenant B's state or sequence-ordered reply stream. -/
theorem partitioned_two_run_noninterference
    (qA qB : Nat) (r1 r2 : PartitionedReactor) (sched1 sched2 : List InboundPacket)
    (hInit : obsB r1 = obsB r2)
    (hSched : filterSchedB sched1 = filterSchedB sched2) :
    obsB (runChronological qA qB r1 sched1) = obsB (runChronological qA qB r2 sched2) := by
  rw [runChronological_eq_filtered qA qB sched1 r1]
  rw [runChronological_eq_filtered qA qB sched2 r2]
  rw [hSched]
  exact runChronological_congr_obsB qA qB (filterSchedB sched2) r1 r2 hInit

end ZirconHandleAndReactorInvariants
