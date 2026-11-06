-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Historical Concurrency, Weak Memory, Kernel, Storage & Distributed Canaries

Standalone Lean 4.34.1 mechanization of historical failure witnesses
("canaries") and their architectural repairs in Anneal's four `trusted/lean/`
primitives:
1. `Language (SemObs : Type)` + `BehaviorCodec L₁ L₂`
2. `ProductiveOn` + `InhabitedPre`
3. Positive per-obligation `VerificationResult`
4. `SmallStepMachine` with `EventualBehaviorOf` + `StepResult.externalCall`
-/

namespace Anneal.ConcurrencySystemsFailures

/-! ## Section 1: Anneal's Four `trusted/lean/` Primitives -/

class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- Primitive 1A: `Language (SemObs : Type)` with observation spine `obs`. -/
structure Language (SemObs : Type) where
  Prog : Type
  Query : Type
  Out : Type
  obs : Out → SemObs
  sem : Prog → Behavior Query Out

/-- Primitive 1B: `BehaviorCodec L₁ L₂` with partial-bijection and `obs` laws. -/
structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  decode_encode_query : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  encodeOut : L₁.Out → L₂.Out
  decodeOut : L₂.Out → Option L₁.Out
  decode_encode_out : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  encode_decode_out : ∀ o₁ o₂, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂
  obs_decodeOut : ∀ o₁ o₂, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

def BehaviorCodec.toMorphism {SemObs : Type} {L₁ L₂ : Language SemObs}
    (codec : BehaviorCodec L₁ L₂)
    (b₁ : Behavior L₁.Query L₁.Out) : Behavior L₂.Query L₂.Out :=
  fun q₂ =>
    let q₁ := codec.decodeQuery q₂
    { defined := (b₁ q₁).defined
      val := fun h₁ o₂ =>
        ∃ o₁, codec.decodeOut o₂ = some o₁ ∧ (b₁ q₁).val h₁ o₁ }

abbrev Compiles {SemObs : Type} (L₁ L₂ : Language SemObs)
    (codec : BehaviorCodec L₁ L₂) (s : L₁.Prog) (t : L₂.Prog) : Prop :=
  L₂.sem t ≤ codec.toMorphism (L₁.sem s)

abbrev Abstracts {SemObs : Type} (L_v L_src : Language SemObs)
    (codec : BehaviorCodec L_v L_src) (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ codec.toMorphism (L_v.sem v)

/-- Primitive 2: `InhabitedPre` and `ProductiveOn`. -/
def InhabitedPre {Query : Type} (pre : Query → Prop) : Prop :=
  ∃ q, pre q

def Language.ProductiveOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q →
    ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Primitive 3: Positive Per-Obligation `VerificationResult`. -/
structure Obligation where
  id : String
  prop : Prop

structure TrustPolicy where
  isAllowed : String → Prop

def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

def VerificationResult (policy : TrustPolicy) (waived : List String)
    (obligations : List Obligation) : Prop :=
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))

/-- Primitive 4: `SmallStepMachine` with `EventualOut` and `externalCall`. -/
inductive FailureKind where
  | ub
  | error
  deriving DecidableEq, Repr

inductive ChoiceKind where
  | demonic
  | angelic
  deriving DecidableEq, Repr

inductive Terminal (Val : Type) where
  | normal (v : Val)
  | panic
  deriving DecidableEq, Repr

inductive EventualOut (Obs Val : Type) where
  | terminated (trace : List Obs) (term : Terminal Val)
  | diverges
  deriving DecidableEq, Repr

inductive StepResult (State Obs Val : Type) where
  | step (obs : Option Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : Terminal Val)
  | failed (kind : FailureKind)

def StepResult.externalCall {State Obs Val : Type}
    (boundaryInv : Bool) (branches : State → Prop) :
    StepResult State Obs Val :=
  if boundaryInv then .choice .demonic branches else .failed .ub

/-! ## Section 2: Weak-Memory Atomic Compilation & Promising 1.0/2.0 Canaries -/

/--
 Failure Canary 1A.1 (Manerkar et al. MICRO 2016; Lahav et al. PLDI 2017):
 Mixing Power/ARMv7 trailing-sync or leading-sync mappings with ARMv8
 `ldar`/`stlr` without a full `dmb ish` between `stlr` and subsequent `ldar`
 (or `LDAPR`) allows the `R` / `Z6.U` / `SB` weak-memory cycle where two
 threads both observe stale values `(r0 = 0, r1 = 0)` on `SeqCst` atomics if
 `stlr x, 1; ldar r0, y` is reordered by hardware store-forwarding/early-read
 before `stlr` propagates to other cores.
-/
structure SeqCstSBState where
  x : Nat
  y : Nat
  t1StoreBuffered : Bool
  t2StoreBuffered : Bool
  r0 : Nat
  r1 : Nat
  deriving DecidableEq, Repr

/-- Unrepaired naive ARMv8 `stlr` + `ldar` without `dmb ish` (or `stlr`
    early-read reorder) permits both loads to execute before the remote core
    observes `stlr`. -/
def buggyArmv8StlrLdarAllowsZeroZero (s : SeqCstSBState) : Prop :=
  s.x = 0 ∧ s.y = 0 ∧ s.t1StoreBuffered = true ∧ s.t2StoreBuffered = true ∧
  s.r0 = 0 ∧ s.r1 = 0

/-- Repaired `RC11` / ARMv8 mapping with `dmb ish` (or `stlr` + `dmb ish` /
    `ldapr` discipline) requires at least one thread's store buffer to drain to
    coherent memory (`x = 1 ∨ y = 1`) before the other thread's `SeqCst` load
    executes. -/
def rc11RepairedArmv8SeqCstSchedule (s : SeqCstSBState) : Prop :=
  (s.x = 1 ∧ s.r1 = 1) ∨ (s.y = 1 ∧ s.r0 = 1)

theorem canary_unrepaired_seqcst_mapping_allows_sb_zero_zero :
    ∃ s : SeqCstSBState, buggyArmv8StlrLdarAllowsZeroZero s ∧
      ¬ (s.r0 = 1 ∨ s.r1 = 1) := by
  refine ⟨⟨0, 0, true, true, 0, 0⟩, ?_, ?_⟩
  · unfold buggyArmv8StlrLdarAllowsZeroZero
    decide
  · decide

theorem repaired_rc11_seqcst_mapping_forbids_sb_zero_zero
    (s : SeqCstSBState) (h : rc11RepairedArmv8SeqCstSchedule s) :
    s.r0 = 1 ∨ s.r1 = 1 := by
  rcases h with ⟨_, hr1⟩ | ⟨_, hr0⟩
  · exact Or.inr hr1
  · exact Or.inl hr0

/--
 Failure Canary 1A.2 (Kang et al. POPL 2017 `Promising 1.0` vs. Lee et al.
 PLDI 2020 `Promising 2.0`):
 In `Promising 1.0`, a thread may speculatively promise a future write `x = 42`
 as long as it can certify that promise locally against current memory. If a
 compiler performs a global value-range optimization based on the invariant
 `x ≤ 1`, an uncapped promise in `Promising 1.0` can use a dead certification
 path that violates the global range bound, rendering global value-range
 optimization unsound. `Promising 2.0` caps certification against bounded/capped
 memory so promises cannot exceed the global invariant.
-/
def promising1UncappedCertifiable (promisedVal : Nat) : Prop :=
  promisedVal = 0 ∨ promisedVal = 42

def promising2CappedCertifiable (globalCap : Nat) (promisedVal : Nat) : Prop :=
  promising1UncappedCertifiable promisedVal ∧ promisedVal ≤ globalCap

theorem canary_promising1_uncapped_promise_breaks_global_range_opt :
    ∃ v, promising1UncappedCertifiable v ∧ ¬ (v ≤ 1) := by
  exact ⟨42, Or.inr rfl, by decide⟩

theorem promising2_capped_memory_preserves_global_range_opt
    (v : Nat) (h : promising2CappedCertifiable 1 v) :
    v ≤ 1 :=
  h.2

/-! ## Section 3: Rust Concurrent Data Structure & Reclamation Canaries -/

/--
 Failure Canary 1B.1 (`crossbeam-epoch` Missing `SeqCst` Fence / Premature
 Reclamation, `crossbeam-rs/crossbeam` issues #462 / #535):
 In Epoch-Based Reclamation (EBR), a reader thread pins the current global
 epoch `E` into its local `Participant` slot and then loads a shared atomic
 pointer `p`. A collector thread advances the global epoch `E` and reclaims
 garbage retired 3 epochs ago if it observes that no active thread is pinned to
 an old epoch.
 Without a `SeqCst` fence between storing `local_epoch := E` and loading
 `ptr := shared_ptr` (and between advancing `global_epoch` and scanning
 `local_epoch`), Store-Buffering allows:
 - Reader buffers `local_epoch := E` and reads the old pointer `alloc_0` before
   collector's unlink, while
 - Collector reads `local_epoch = unpinned` (before Reader's store flushes) and
   frees `alloc_0`!
-/
structure EpochReclamationTrace where
  readerPinnedVisibleToCollector : Bool
  collectorUnlinkVisibleToReader : Bool
  fenceSeqCstPresent : Bool
  deriving DecidableEq, Repr

def epochStepResult (t : EpochReclamationTrace) : StepResult Unit Unit Unit :=
  if !t.readerPinnedVisibleToCollector && !t.collectorUnlinkVisibleToReader then
    .failed .ub
  else
    .terminated (.normal ())

def validEpochHardwareTrace (t : EpochReclamationTrace) : Prop :=
  t.fenceSeqCstPresent = true →
    (t.readerPinnedVisibleToCollector = true ∨
      t.collectorUnlinkVisibleToReader = true)

theorem canary_epoch_pin_without_seqcst_allows_uaf :
    ∃ t : EpochReclamationTrace,
      t.fenceSeqCstPresent = false ∧
      validEpochHardwareTrace t ∧
      epochStepResult t = .failed .ub := by
  refine ⟨⟨false, false, false⟩, rfl, ?_, rfl⟩
  intro h
  contradiction

theorem repaired_epoch_pin_seqcst_prevents_uaf
    (t : EpochReclamationTrace)
    (hFence : t.fenceSeqCstPresent = true)
    (hHw : validEpochHardwareTrace t) :
    epochStepResult t = .terminated (.normal ()) := by
  have hVis := hHw hFence
  unfold epochStepResult
  rcases hVis with hR | hC
  · simp [hR]
  · simp [hC]

/--
 Failure Canary 1B.2 (`RwLockReadGuard` / `MutexGuard` Unsound `Sync` Bound,
 `rust-lang/rust#41622`, CVE-2018-1000810):
 `RwLockReadGuard<'a, T>` Derefs to `&T`. If `RwLockReadGuard<'a, T>` implements
 `Sync` whenever `T: Send` (without requiring `T: Sync`), then sharing
 `&RwLockReadGuard<'a, Cell<u64>>` across two threads gives both threads
 concurrent `&Cell<u64>` references, causing an immediate non-atomic data race.
-/
structure GuardTypeTraits where
  tIsSend : Bool
  tIsSync : Bool
  deriving DecidableEq, Repr

def buggyRwLockReadGuardIsSync (tr : GuardTypeTraits) : Bool :=
  tr.tIsSend

def repairedRwLockReadGuardIsSync (tr : GuardTypeTraits) : Bool :=
  tr.tIsSync

def concurrentSharedGuardAccessSafe (tr : GuardTypeTraits) : Bool :=
  tr.tIsSync

theorem canary_rwlock_read_guard_send_only_permits_data_race :
    ∃ tr : GuardTypeTraits,
      buggyRwLockReadGuardIsSync tr = true ∧
      concurrentSharedGuardAccessSafe tr = false := by
  exact ⟨⟨true, false⟩, rfl, rfl⟩

theorem repaired_rwlock_read_guard_requires_t_sync
    (tr : GuardTypeTraits)
    (hSync : repairedRwLockReadGuardIsSync tr = true) :
    concurrentSharedGuardAccessSafe tr = true :=
  hSync

/-! ## Section 4: Linux Kernel `VirtIO` Ring `EVENT_IDX` Weak-Memory Canary -/

/--
 Failure Canary 1C.1 (Linux Kernel / VirtIO `VIRTIO_RING_F_EVENT_IDX` Missing
 `smp_mb()`):
 In VirtIO split rings with `EVENT_IDX`, the guest driver writes `avail_idx = K`
 and reads `used_event` to decide whether to kick the host; concurrently, the
 host device writes `used_event = K` and reads `avail_idx` to decide whether to
 sleep.
 Without a full `smp_mb()` (`SeqCst` fence) on both sides, ARM64/RISC-V store
 buffering allows:
 - Driver writes `avail_idx = K`, reads stale `used_event != K`, and suppresses
   the kick;
 - Host writes `used_event = K`, reads stale `avail_idx < K`, and goes to sleep.
 Both sides block forever (lost-wakeup deadlock).
-/
structure VirtioEventIdxExchange where
  driverSeesUpdatedUsedEvent : Bool
  deviceSeesUpdatedAvailIdx : Bool
  driverExecutedSmpMb : Bool
  deviceExecutedSmpMb : Bool
  deriving DecidableEq, Repr

def virtioKickSent (e : VirtioEventIdxExchange) : Bool :=
  e.driverSeesUpdatedUsedEvent

def virtioDeviceAwake (e : VirtioEventIdxExchange) : Bool :=
  e.deviceSeesUpdatedAvailIdx || virtioKickSent e

theorem canary_virtio_event_idx_missing_mb_deadlocks :
    ∃ e : VirtioEventIdxExchange,
      (e.driverExecutedSmpMb = false ∨ e.deviceExecutedSmpMb = false) ∧
      virtioDeviceAwake e = false := by
  exact ⟨⟨false, false, false, true⟩, Or.inl rfl, rfl⟩

theorem repaired_virtio_event_idx_smp_mb_prevents_lost_wakeup
    (e : VirtioEventIdxExchange)
    (hBarrierOrder :
      e.driverExecutedSmpMb = true →
      e.deviceExecutedSmpMb = true →
      (e.driverSeesUpdatedUsedEvent = true ∨
        e.deviceSeesUpdatedAvailIdx = true))
    (hDrv : e.driverExecutedSmpMb = true)
    (hDev : e.deviceExecutedSmpMb = true) :
    virtioDeviceAwake e = true := by
  have hOrd := hBarrierOrder hDrv hDev
  unfold virtioDeviceAwake virtioKickSent
  rcases hOrd with h1 | h2
  · simp [h1]
  · simp [h2]

/-! ## Section 5: Verified OS Kernel & Storage Boundary Failure Canaries -/

/--
 Failure Canary 2.1 (`seL4` / `SeKVM` / `CertiKOS` Unmodeled DMA & ARMv8
 Break-Before-Make TLB Conflict Boundary):
 If a kernel verification model treats page-table updates as atomic RAM writes
 and omits `StepResult.externalCall` boundary checks for (a) ARMv8
 Break-Before-Make (`BBM`: old valid PTE must be invalidated and TLB-flushed via
 `dsb; tlbi; dsb` before writing a new block/page PTE) and (b) IOMMU DMA
 disjointness from active Rust CPU borrows, hardware raises a fatal
 `TLB Conflict Abort` or DMA clobbers live CPU references.
-/
structure MmuDmaBoundaryState where
  oldPteValidInTlb : Bool
  writingNewIncompatiblePte : Bool
  dmaRangeOverlapsActiveCpuBorrow : Bool
  deriving DecidableEq, Repr

def mmuDmaBoundaryInv (s : MmuDmaBoundaryState) : Bool :=
  !(s.oldPteValidInTlb && s.writingNewIncompatiblePte) &&
  !s.dmaRangeOverlapsActiveCpuBorrow

def executeHardwareMmuDmaStep (s : MmuDmaBoundaryState) :
    StepResult MmuDmaBoundaryState Unit Unit :=
  StepResult.externalCall (mmuDmaBoundaryInv s) (fun s' => s' = s)

theorem canary_bbm_violation_or_rogue_dma_triggers_ub :
    executeHardwareMmuDmaStep ⟨true, true, false⟩ = .failed .ub ∧
    executeHardwareMmuDmaStep ⟨false, false, true⟩ = .failed .ub := by
  exact ⟨rfl, rfl⟩

theorem repaired_external_call_boundary_inv_blocks_rogue_dma_and_bbm
    (s : MmuDmaBoundaryState)
    (hBbm : ¬ (s.oldPteValidInTlb = true ∧ s.writingNewIncompatiblePte = true))
    (hDma : s.dmaRangeOverlapsActiveCpuBorrow = false) :
    executeHardwareMmuDmaStep s = .choice .demonic (fun s' => s' = s) := by
  unfold executeHardwareMmuDmaStep StepResult.externalCall mmuDmaBoundaryInv
  cases h1 : s.oldPteValidInTlb <;> cases h2 : s.writingNewIncompatiblePte
  · simp [hDma]
  · simp [hDma]
  · simp [hDma]
  · exfalso
    exact hBbm ⟨h1, h2⟩

/--
 Failure Canary 2.2 (`FSCQ` / `Yggdrasil` Non-Idempotent Crash Recovery Under
 Nested Crashes):
 Suppose a write-ahead log (WAL) recovery procedure `buggyRecover` applies log
 record `L` to disk block `B` by `B := B + L` and *then* clears `L := 0`. If a
 single crash occurs and `buggyRecover` runs to completion, `B` has the right
 value. However, if a *second* power loss occurs after `B := B + L` is flushed
 to disk but before `L := 0` is persisted, running `buggyRecover` after the
 second reboot applies `L` a *second* time (`B + 2*L`), corrupting the
 filesystem! Idempotent recovery (`repairedIdempotentRecover`, overwriting
 `B := targetVal` or checking a persisted sequence number) is invariant under
 arbitrary $k \ge 1$ nested crashes.
-/
structure WalDiskState where
  dataBlock : Nat
  logDeltaOrTarget : Nat
  logValid : Bool
  deriving DecidableEq, Repr

def buggyRecoverInterruptedOnce (d : WalDiskState) : WalDiskState :=
  if d.logValid then
    { d with dataBlock := d.dataBlock + d.logDeltaOrTarget }
  else d

def buggyRecoverComplete (d : WalDiskState) : WalDiskState :=
  if d.logValid then
    { dataBlock := d.dataBlock + d.logDeltaOrTarget
      logDeltaOrTarget := 0
      logValid := false }
  else d

def repairedRecoverInterruptedOnce (d : WalDiskState) : WalDiskState :=
  if d.logValid then { d with dataBlock := d.logDeltaOrTarget } else d

def repairedRecoverComplete (d : WalDiskState) : WalDiskState :=
  if d.logValid then
    { dataBlock := d.logDeltaOrTarget
      logDeltaOrTarget := d.logDeltaOrTarget
      logValid := false }
  else d

theorem canary_nested_crash_during_non_idempotent_recovery_corrupts_disk :
    let init : WalDiskState := ⟨10, 5, true⟩
    (buggyRecoverComplete (buggyRecoverInterruptedOnce init)).dataBlock ≠
      (buggyRecoverComplete init).dataBlock := by
  decide

theorem repaired_idempotent_wal_recovery_survives_nested_crashes
    (d : WalDiskState) :
    repairedRecoverComplete (repairedRecoverInterruptedOnce d) =
      repairedRecoverComplete d := by
  cases h : d.logValid <;>
    simp [repairedRecoverInterruptedOnce, repairedRecoverComplete, h]

/-! ## Section 6: Distributed Protocol, Marshaling & SMT Isolation Canaries -/

/--
 Failure Canary 3.1 (Pamela Zave CCR 2012 / ToN 2017 Alloy Counterexample to
 `Chord`):
 In a 3-node identifier ring `{0, 1, 2}`, a valid global ring requires that
 iterating the primary `successor` pointer from `0` visits all 3 live nodes
 (cycle length 3). Under concurrent join + failure/churn without Zave's
 structured successor-list invariant, node `0` points to `0` (self-loop) while
 `1 ↔ 2` form a separate 2-cycle, partitioning the ring even though every node
 has a live successor and predecessor!
-/
structure Chord3Ring where
  succ0 : Fin 3
  succ1 : Fin 3
  succ2 : Fin 3
  deriving DecidableEq, Repr

def Chord3Ring.step (r : Chord3Ring) (n : Fin 3) : Fin 3 :=
  match n with
  | ⟨0, _⟩ => r.succ0
  | ⟨1, _⟩ => r.succ1
  | ⟨2, _⟩ => r.succ2

def Chord3Ring.everyNodeHasValidSucc (r : Chord3Ring) : Bool :=
  let s0 := r.succ0.val
  let s1 := r.succ1.val
  let s2 := r.succ2.val
  (s0 != s1) && (s1 != s2) && (s0 != s2)

def Chord3Ring.isConnectedSingleRing (r : Chord3Ring) : Bool :=
  let n1 := r.step ⟨0, by decide⟩
  let n2 := r.step n1
  (n1.val != 0) && (n2.val != 0) && (n2.val != n1.val)

theorem canary_chord_local_bijection_allows_partitioned_subrings :
    ∃ r : Chord3Ring,
      r.everyNodeHasValidSucc = true ∧
      r.isConnectedSingleRing = false := by
  refine ⟨⟨⟨0, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩⟩, ?_, ?_⟩
  · decide
  · decide

/--
 Failure Canary 3.2 (`Verdi` / `IronFleet` / `Cheerios` Non-Injective Packet
 Marshaling vs. `BehaviorCodec` Partial-Bijection Law):
 Suppose a distributed node serializes
 `Msg := (header : List UInt8) × (payload : List UInt8)` by naive concatenation
 `header ++ payload` without a length prefix. Then two distinct messages
 `m₁ = ([1], [2, 3])` and `m₂ = ([1, 2], [3])` produce the *exact same* wire
 packet `[1, 2, 3]`, violating `BehaviorCodec`'s bijection law
 `decodeOut (encodeOut o₁) = some o₁`! Prefixing the header length
 `header.length :: (header ++ payload)` makes serialization injective and
 invertible.
-/
structure SplitMsg where
  header : List Nat
  payload : List Nat
  deriving DecidableEq, Repr

def buggySerializeConcat (m : SplitMsg) : List Nat :=
  m.header ++ m.payload

def repairedSerializeLengthPrefixed (m : SplitMsg) : List Nat :=
  m.header.length :: (m.header ++ m.payload)

def repairedDeserializeLengthPrefixed (wire : List Nat) : Option SplitMsg :=
  match wire with
  | [] => none
  | len :: rest =>
    if rest.length < len then none
    else some ⟨rest.take len, rest.drop len⟩

theorem canary_non_injective_packet_serializer_collides :
    let m₁ : SplitMsg := ⟨[1], [2, 3]⟩
    let m₂ : SplitMsg := ⟨[1, 2], [3]⟩
    m₁ ≠ m₂ ∧ buggySerializeConcat m₁ = buggySerializeConcat m₂ := by
  decide

theorem take_append_exact : ∀ (xs ys : List Nat),
    (xs ++ ys).take xs.length = xs
  | [], _ => rfl
  | _ :: xs, ys => by simp [take_append_exact xs ys]

theorem drop_append_exact : ∀ (xs ys : List Nat),
    (xs ++ ys).drop xs.length = ys
  | [], _ => rfl
  | _ :: xs, ys => by simp [drop_append_exact xs ys]

theorem length_le_append (xs ys : List Nat) :
    ¬ ((xs ++ ys).length < xs.length) := by
  simp [List.length_append]

theorem repaired_length_prefixed_roundtrip (m : SplitMsg) :
    repairedDeserializeLengthPrefixed
      (repairedSerializeLengthPrefixed m) = some m := by
  rcases m with ⟨hdr, pay⟩
  dsimp [repairedSerializeLengthPrefixed, repairedDeserializeLengthPrefixed]
  have hNotLt : ¬ ((hdr ++ pay).length < hdr.length) :=
    length_le_append hdr pay
  rw [ite_eq_right_iff.mpr (fun h => False.elim (hNotLt h))]
  rw [take_append_exact, drop_append_exact]

/--
 Failure Canary 3.3 (`IronFleet` / `Mariposa` Z3 Quantifier Instability
 Isolation via Anneal's Positive Per-Obligation `VerificationResult`):
 In antecedent-based verification envelopes (`hAssumptions → AllVerified`), a
 single false or waived assumption makes the antecedent `False`, vacuously
 "proving" *every* obligation in the crate (Principle of Explosion). In
 Anneal's positive per-obligation `VerificationResult`, waiving an SMT-unstable
 obligation `"vc_raft_append_entries"` leaves every other obligation
 `"vc_wal_bounds_safe"` positively proven!
-/
def AntecedentVerificationResult (assumptionsHold : Prop)
    (obligations : List Obligation) : Prop :=
  assumptionsHold → AllHold (obligations.map (·.prop))

theorem canary_antecedent_verification_result_explodes_on_false_assumption
    (obligations : List Obligation) :
    AntecedentVerificationResult False obligations := by
  intro hFalse
  exact False.elim hFalse

theorem positive_verification_result_isolates_waived_obligation
    (policy : TrustPolicy)
    (obSafe obWaived : Obligation)
    (hDistinct : obSafe.id ≠ obWaived.id)
    (hVR : VerificationResult policy [obWaived.id] [obSafe, obWaived]) :
    obSafe.prop := by
  rcases hVR with ⟨_, hObs⟩
  rcases hObs with ⟨hFirst, _⟩
  rcases hFirst with hInWaived | hProp
  · simp at hInWaived
    exact False.elim (hDistinct hInWaived)
  · exact hProp

/--
 Failure Canary 3.4 (`ProductiveOn` + `InhabitedPre` Blocking Vacuous Domain &
 Empty-Outcome Miracles in Concurrent / Kernel Specs):
 Without `InhabitedPre pre`, an over-constrained fairness or hardware
 precondition `pre := fun _ => False` vacuously satisfies
 `ProductiveOn pre prog` even for a program with Undefined Behavior
 (`Partial.ub`). Pairing `InhabitedPre pre` with `L.ProductiveOn pre prog`
 guarantees at least one concrete defined execution outcome exists.
-/
theorem canary_uninhabited_pre_vacuously_satisfies_ub_prog
    {SemObs : Type} (L : Language SemObs) (prog : L.Prog) :
    L.ProductiveOn (fun _ => False) prog := by
  intro _ hFalse
  exact False.elim hFalse

theorem inhabited_pre_and_productive_on_guarantee_witness
    {SemObs : Type} (L : Language SemObs) (pre : L.Query → Prop) (prog : L.Prog)
    (hInh : InhabitedPre pre) (hProd : L.ProductiveOn pre prog) :
    ∃ (q : L.Query) (h : (L.sem prog q).defined) (o : L.Out),
      pre q ∧ (L.sem prog q).val h o := by
  rcases hInh with ⟨q, hq⟩
  rcases hProd q hq with ⟨hDef, o, hVal⟩
  exact ⟨q, hDef, o, hq, hVal⟩

end Anneal.ConcurrencySystemsFailures

/--
info: 'Anneal.ConcurrencySystemsFailures.canary_unrepaired_seqcst_mapping_allows_sb_zero_zero' does not depend on any axioms
-/
#guard_msgs in
#print axioms Anneal.ConcurrencySystemsFailures.canary_unrepaired_seqcst_mapping_allows_sb_zero_zero

/--
info: 'Anneal.ConcurrencySystemsFailures.repaired_rc11_seqcst_mapping_forbids_sb_zero_zero' does not depend on any axioms
-/
#guard_msgs in
#print axioms Anneal.ConcurrencySystemsFailures.repaired_rc11_seqcst_mapping_forbids_sb_zero_zero

/--
info: 'Anneal.ConcurrencySystemsFailures.repaired_epoch_pin_seqcst_prevents_uaf' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.ConcurrencySystemsFailures.repaired_epoch_pin_seqcst_prevents_uaf

/--
info: 'Anneal.ConcurrencySystemsFailures.repaired_external_call_boundary_inv_blocks_rogue_dma_and_bbm' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.ConcurrencySystemsFailures.repaired_external_call_boundary_inv_blocks_rogue_dma_and_bbm

/--
info: 'Anneal.ConcurrencySystemsFailures.repaired_idempotent_wal_recovery_survives_nested_crashes' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.ConcurrencySystemsFailures.repaired_idempotent_wal_recovery_survives_nested_crashes

/--
info: 'Anneal.ConcurrencySystemsFailures.repaired_length_prefixed_roundtrip' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.ConcurrencySystemsFailures.repaired_length_prefixed_roundtrip

/--
info: 'Anneal.ConcurrencySystemsFailures.positive_verification_result_isolates_waived_obligation' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Anneal.ConcurrencySystemsFailures.positive_verification_result_isolates_waived_obligation

/--
info: 'Anneal.ConcurrencySystemsFailures.inhabited_pre_and_productive_on_guarantee_witness' does not depend on any axioms
-/
#guard_msgs in
#print axioms Anneal.ConcurrencySystemsFailures.inhabited_pre_and_productive_on_guarantee_witness
