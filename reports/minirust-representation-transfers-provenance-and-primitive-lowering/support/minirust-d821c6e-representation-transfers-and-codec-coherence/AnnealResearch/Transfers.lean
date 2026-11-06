import AnnealResearch.Representation
import AnnealResearch.ByteMemory

/-!
Operational bridges for the owned byte representation. Decoding is pointer
formation, not permission to dereference. Allocation-address resolution below
is an explicitly admitted ordinary-allocation policy, not Rust provenance
adequacy. It excludes exposed-provenance recovery and external MMIO.

The underlying storage commands use byte-addressed access checks; they do not
enforce the wider alignment required by Rust's aligned typed operations. The
codec's conditional layout theorem alone cannot supply base-address alignment.
-/
namespace AnnealResearch.Transfers

variable {C : Type}

inductive CopyResult (C : Type) where
  | success (after : ByteMemory.State C)
  | failure (error : ByteMemory.Error) (after : ByteMemory.State C)

/-- The operational command retains state on failure. ByteMemory.rawCopy is
    only its state-erasing convenience projection. -/
def runRawCopy (policy : ByteMemory.Policy) (s : ByteMemory.State C)
    (src dst : ByteMemory.Ptr) (n : Nat) : CopyResult C :=
  match ByteMemory.readSnapshot policy s src n with
  | .error e => .failure e s
  | .ok (b, afterRead) =>
    match ByteMemory.writeBlock policy afterRead dst n b with
    | .error e => .failure e afterRead
    | .ok afterWrite => .success afterWrite

def CopyResult.forget : CopyResult C → Except ByteMemory.Error (ByteMemory.State C)
  | .success after => .ok after
  | .failure e _ => .error e

theorem runRawCopy_projection (policy : ByteMemory.Policy) (s : ByteMemory.State C)
    (src dst : ByteMemory.Ptr) (n : Nat) :
    (runRawCopy policy s src dst n).forget = ByteMemory.rawCopy policy s src dst n := by
  unfold runRawCopy ByteMemory.rawCopy
  cases ByteMemory.readSnapshot policy s src n with
  | error e => rfl
  | ok result =>
    rcases result with ⟨b, after⟩
    dsimp only
    cases hw : ByteMemory.writeBlock policy after dst n b <;>
      simp only [CopyResult.forget]

theorem runRawCopy_success (policy : ByteMemory.Policy) (s out : ByteMemory.State C)
    (src dst : ByteMemory.Ptr) (n : Nat)
    (copied : ByteMemory.rawCopy policy s src dst n = .ok out) :
    runRawCopy policy s src dst n = .success out := by
  unfold ByteMemory.rawCopy at copied
  unfold runRawCopy
  cases hr : ByteMemory.readSnapshot policy s src n with
  | error e => simp [hr] at copied
  | ok result =>
    rcases result with ⟨b, after⟩
    cases hw : ByteMemory.writeBlock policy after dst n b with
    | error e => simp [hr, hw] at copied
    | ok written =>
      have same : written = out := by simpa [hr, hw] using copied
      cases same
      simp only [hw]

theorem rawCopy_failure_retains_revoked_grant (value : C) :
    runRawCopy .siblingRevoking (ByteMemory.aliasInitial value)
      ByteMemory.sibling ByteMemory.owner 1 =
      .failure .authority
        (ByteMemory.afterRead .siblingRevoking (ByteMemory.aliasInitial value)
          ByteMemory.sibling 1) ∧
    (ByteMemory.afterRead .siblingRevoking (ByteMemory.aliasInitial value)
      ByteMemory.sibling 1).writeGrant ByteMemory.owner = false := by
  have hr : ByteMemory.ReadReady (ByteMemory.aliasInitial value) ByteMemory.sibling 1 := by
    refine ⟨?_, fun _ => rfl⟩
    simp [ByteMemory.Fits, ByteMemory.aliasInitial, ByteMemory.sibling]
  have denied : ¬ ByteMemory.WriteReady
      (ByteMemory.afterRead .siblingRevoking (ByteMemory.aliasInitial value)
        ByteMemory.sibling 1) ByteMemory.owner 1 := by
    intro ready
    have impossible := ready.2 ⟨0, by decide⟩
    simp [ByteMemory.afterRead, ByteMemory.revoke, ByteMemory.Span, ByteMemory.Ptr.shift,
      ByteMemory.Ptr.loc, ByteMemory.sibling, ByteMemory.owner] at impossible
  constructor
  · simp only [runRawCopy, ByteMemory.readSnapshot_ok _ _ _ _ hr]
    simp only [ByteMemory.writeBlock, denied, ite_eq_right, not_false_eq_true]
    rfl
  · rfl

def memoryRep (s : ByteMemory.State Representation.Cell) (p : ByteMemory.Ptr) :
    Representation.Representation := fun i => s.cells (p.locAt i)

def blockRep (b : ByteMemory.Block Representation.Cell n) :
    Representation.Representation :=
  fun i => if h : i < n then b ⟨i, h⟩ else .uninit

@[simp] theorem blockRep_cell (b : ByteMemory.Block Representation.Cell n) (i : Fin n) :
    blockRep b i.val = b i := by
  simp [blockRep, i.isLt]

/-- Any successful raw transfer preserves exactly the decoder's subject,
    regardless of whether that subject is supported by the decoder. -/
theorem rawCopy_pointer_reconstruction (t : Representation.Target)
    (policy : ByteMemory.Policy) (s : ByteMemory.State Representation.Cell)
    (src dst : ByteMemory.Ptr)
    (hr : ByteMemory.ReadReady s src t.width)
    (hw : ByteMemory.WriteReady (ByteMemory.afterRead policy s src t.width) dst t.width) :
    ∃ out, runRawCopy policy s src dst t.width = .success out ∧
      Representation.decodePtr t (memoryRep out dst) =
        Representation.decodePtr t (memoryRep s src) ∧
      (∀ l, ¬ ByteMemory.Span dst t.width l → out.cells l = s.cells l) := by
  obtain ⟨out, copied, cells, frame⟩ := ByteMemory.rawCopy_success policy s src dst t.width hr hw
  refine ⟨out, runRawCopy_success policy s out src dst t.width copied, ?_, frame⟩
  exact Representation.decodePtr_congr t _ _ cells

theorem rawCopy_aggregate_reconstruction (t : Representation.Target)
    (layout : Representation.Layout) (hl : Representation.Admissible t layout)
    (policy : ByteMemory.Policy) (s : ByteMemory.State Representation.Cell)
    (src dst : ByteMemory.Ptr)
    (hr : ByteMemory.ReadReady s src layout.extent)
    (hw : ByteMemory.WriteReady (ByteMemory.afterRead policy s src layout.extent) dst layout.extent) :
    ∃ out, runRawCopy policy s src dst layout.extent = .success out ∧
      Representation.decodeAggregate t layout (memoryRep out dst) =
        Representation.decodeAggregate t layout (memoryRep s src) ∧
      (∀ i : Fin layout.extent, memoryRep out dst i.val = memoryRep s src i.val) := by
  obtain ⟨out, copied, cells, _⟩ := ByteMemory.rawCopy_success policy s src dst layout.extent hr hw
  refine ⟨out, runRawCopy_success policy s out src dst layout.extent copied, ?_, cells⟩
  apply Representation.decodeAggregate_congr t layout hl
  intro i hi
  exact cells ⟨i, hi⟩

inductive TypedError where
  | access (error : ByteMemory.Error)
  | unsupportedRepresentation
  | unsupportedLayout
  deriving DecidableEq, Repr

/-- The post-read state is retained even when reconstruction is unsupported. -/
inductive LoadResult (t : Representation.Target) where
  | success (pointer : Representation.Ptr t) (after : ByteMemory.State Representation.Cell)
  | failure (error : TypedError) (after : ByteMemory.State Representation.Cell)

def loadPointer (t : Representation.Target) (policy : ByteMemory.Policy)
    (s : ByteMemory.State Representation.Cell) (src : ByteMemory.Ptr) : LoadResult t :=
  match ByteMemory.readSnapshot policy s src t.width with
  | .error e => .failure (.access e) s
  | .ok (b, after) =>
    match Representation.decodePtr t (blockRep b) with
    | none => .failure .unsupportedRepresentation after
    | some p => .success p after

theorem loadPointer_supported (t : Representation.Target) (policy : ByteMemory.Policy)
    (s : ByteMemory.State Representation.Cell) (src : ByteMemory.Ptr)
    (p : Representation.Ptr t) (hr : ByteMemory.ReadReady s src t.width)
    (hd : Representation.decodePtr t (memoryRep s src) = some p) :
    loadPointer t policy s src =
      .success p (ByteMemory.afterRead policy s src t.width) := by
  have same : Representation.decodePtr t (blockRep (ByteMemory.getWindow s src t.width)) =
      Representation.decodePtr t (memoryRep s src) := by
    apply Representation.decodePtr_congr
    intro i
    exact blockRep_cell _ i
  simp [loadPointer, ByteMemory.readSnapshot_ok policy s src t.width hr, same, hd]

theorem loadPointer_uninitialized (t : Representation.Target) (policy : ByteMemory.Policy)
    (s : ByteMemory.State Representation.Cell) (src : ByteMemory.Ptr)
    (hr : ByteMemory.ReadReady s src t.width) (i : Fin t.width)
    (hi : memoryRep s src i.val = .uninit) :
    loadPointer t policy s src =
      .failure .unsupportedRepresentation (ByteMemory.afterRead policy s src t.width) := by
  have hd : Representation.decodePtr t
      (blockRep (ByteMemory.getWindow s src t.width)) = none := by
    apply Representation.decodePtr_reject_uninit t _ i
    simpa only [blockRep_cell, memoryRep, ByteMemory.getWindow] using hi
  simp [loadPointer, ByteMemory.readSnapshot_ok policy s src t.width hr, hd]

inductive StoreResult where
  | success (after : ByteMemory.State Representation.Cell)
  | failure (error : TypedError) (after : ByteMemory.State Representation.Cell)

def aggregateBlock (t : Representation.Target) (layout : Representation.Layout)
    (policy : Representation.ProvenancePolicy) (v : Representation.Aggregate t) :
    ByteMemory.Block Representation.Cell layout.extent :=
  fun i => Representation.encodeAggregate t layout
    (Representation.reborrowAggregate policy v) i.val

/-- Raw-pointer payloads use identityPolicy. Other policies model an explicitly
    abstract reference-like operation; no Rust reference validity is inferred. -/
def storeAggregate (t : Representation.Target) (layout : Representation.Layout)
    (policy : ByteMemory.Policy) (provenance : Representation.ProvenancePolicy)
    (s : ByteMemory.State Representation.Cell) (dst : ByteMemory.Ptr)
    (v : Representation.Aggregate t) : StoreResult :=
  if Representation.Admissible t layout then
    match ByteMemory.writeBlock policy s dst layout.extent (aggregateBlock t layout provenance v) with
    | .error e => .failure (.access e) s
    | .ok after => .success after
  else .failure .unsupportedLayout s

theorem storeAggregate_supported (t : Representation.Target) (layout : Representation.Layout)
    (hl : Representation.Admissible t layout) (policy : ByteMemory.Policy)
    (provenance : Representation.ProvenancePolicy) (s : ByteMemory.State Representation.Cell)
    (dst : ByteMemory.Ptr) (v : Representation.Aggregate t)
    (hw : ByteMemory.WriteReady s dst layout.extent) :
    ∃ out, storeAggregate t layout policy provenance s dst v = .success out ∧
      Representation.decodeAggregate t layout (memoryRep out dst) =
        some (Representation.reborrowAggregate provenance v) ∧
      (∀ i, i < layout.extent → ¬ Representation.NonPadding t layout i →
        memoryRep out dst i = .uninit) ∧
      (∀ l, ¬ ByteMemory.Span dst layout.extent l → out.cells l = s.cells l) := by
  let out := ByteMemory.afterWrite policy s dst layout.extent (aggregateBlock t layout provenance v)
  have cells : ∀ i : Fin layout.extent, memoryRep out dst i.val =
      Representation.encodeAggregate t layout (Representation.reborrowAggregate provenance v) i.val :=
    ByteMemory.afterWrite_storage policy s dst layout.extent _
  refine ⟨out, ?_, ?_, ?_, ?_⟩
  · simp [storeAggregate, hl, ByteMemory.writeBlock_ok policy s dst layout.extent _ hw, out]
  · rw [Representation.decodeAggregate_congr t layout hl _
      (Representation.encodeAggregate t layout (Representation.reborrowAggregate provenance v))
      (fun i hi => cells ⟨i, hi⟩)]
    exact Representation.decodeAggregate_encodeAggregate t layout hl _
  · intro i hi padding
    rw [cells ⟨i, hi⟩]
    exact Representation.encodeAggregate_padding t layout _ i padding
  · exact ByteMemory.afterWrite_frame policy s dst layout.extent _

def typedCopyAggregate (t : Representation.Target) (layout : Representation.Layout)
    (policy : ByteMemory.Policy) (provenance : Representation.ProvenancePolicy)
    (s : ByteMemory.State Representation.Cell) (src dst : ByteMemory.Ptr) : StoreResult :=
  if Representation.Admissible t layout then
    match ByteMemory.readSnapshot policy s src layout.extent with
    | .error e => .failure (.access e) s
    | .ok (b, after) =>
      match Representation.decodeAggregate t layout (blockRep b) with
      | none => .failure .unsupportedRepresentation after
      | some v => storeAggregate t layout policy provenance after dst v
  else .failure .unsupportedLayout s

theorem typedCopyAggregate_supported (t : Representation.Target) (layout : Representation.Layout)
    (hl : Representation.Admissible t layout) (policy : ByteMemory.Policy)
    (provenance : Representation.ProvenancePolicy) (s : ByteMemory.State Representation.Cell)
    (src dst : ByteMemory.Ptr) (v : Representation.Aggregate t)
    (hr : ByteMemory.ReadReady s src layout.extent)
    (hw : ByteMemory.WriteReady (ByteMemory.afterRead policy s src layout.extent) dst layout.extent)
    (hd : Representation.decodeAggregate t layout (memoryRep s src) = some v) :
    ∃ out, typedCopyAggregate t layout policy provenance s src dst = .success out ∧
      Representation.decodeAggregate t layout (memoryRep out dst) =
        some (Representation.reborrowAggregate provenance v) ∧
      (∀ i, i < layout.extent → ¬ Representation.NonPadding t layout i →
        memoryRep out dst i = .uninit) ∧
      (∀ l, ¬ ByteMemory.Span dst layout.extent l → out.cells l = s.cells l) := by
  have hd' : Representation.decodeAggregate t layout
      (blockRep (ByteMemory.getWindow s src layout.extent)) = some v := by
    rw [Representation.decodeAggregate_congr t layout hl _ (memoryRep s src)
      (by intro i hi; exact blockRep_cell _ ⟨i, hi⟩)]
    exact hd
  obtain ⟨out, stored, decoded, padding, frame⟩ := storeAggregate_supported t layout hl policy
    provenance (ByteMemory.afterRead policy s src layout.extent) dst v hw
  refine ⟨out, ?_, decoded, padding, ?_⟩
  · simp [typedCopyAggregate, hl, ByteMemory.readSnapshot_ok _ _ _ _ hr, hd', stored]
  · exact frame

/-- The same admitted source produces equal abstract cells under raw copying,
    while this typed-transfer policy clears padding. -/
theorem raw_and_typed_padding (t : Representation.Target) (layout : Representation.Layout)
    (hl : Representation.Admissible t layout) (policy : ByteMemory.Policy)
    (s : ByteMemory.State Representation.Cell) (src dst : ByteMemory.Ptr)
    (v : Representation.Aggregate t) (hr : ByteMemory.ReadReady s src layout.extent)
    (hw : ByteMemory.WriteReady (ByteMemory.afterRead policy s src layout.extent) dst layout.extent)
    (hd : Representation.decodeAggregate t layout (memoryRep s src) = some v)
    (i : Fin layout.extent) (padding : ¬ Representation.NonPadding t layout i.val)
    (initialized : memoryRep s src i.val ≠ .uninit) :
    ∃ raw typed,
      runRawCopy policy s src dst layout.extent = .success raw ∧
      typedCopyAggregate t layout policy Representation.identityPolicy s src dst = .success typed ∧
      memoryRep raw dst i.val = memoryRep s src i.val ∧
      memoryRep typed dst i.val = .uninit ∧
      memoryRep raw dst i.val ≠ memoryRep typed dst i.val := by
  obtain ⟨raw, copied, _, cells⟩ := rawCopy_aggregate_reconstruction t layout hl policy s src dst hr hw
  obtain ⟨typed, moved, _, uninit, _⟩ := typedCopyAggregate_supported t layout hl policy
    Representation.identityPolicy s src dst v hr hw hd
  refine ⟨raw, typed, copied, moved, cells i, uninit i.val i.isLt padding, ?_⟩
  rw [cells i, uninit i.val i.isLt padding]
  exact initialized

def digitsValue : List Representation.Byte → Nat
  | [] => 0
  | b :: bs => b.val + 256 * digitsValue bs

theorem digitsValue_bound (bs : List Representation.Byte) : digitsValue bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [digitsValue]
  | cons b bs ih =>
    have hb := b.isLt
    simp only [digitsValue, List.length_cons, Nat.pow_succ]
    omega

/-- Significance order is little-endian internally; physical byte order is
    handled by Representation.significance for either target endianness. -/
def addressNumber (t : Representation.Target) (p : Representation.Ptr t) : Nat :=
  digitsValue (List.ofFn p.address)

theorem addressNumber_bound (t : Representation.Target) (p : Representation.Ptr t) :
    addressNumber t p < 256 ^ t.width := by
  simpa [addressNumber] using digitsValue_bound (List.ofFn p.address)

structure AddressSpace where
  base : Nat → Nat
  generation : Nat → Nat

/- This table has no global allocation-coherence theorem: disjoint live ranges,
   lifetime evolution and absolute alignment remain separate obligations. -/

def Resolvable (t : Representation.Target) (a : AddressSpace) (s : ByteMemory.State C)
    (p : Representation.Ptr t) (v : Representation.Provenance) (n : Nat) : Prop :=
  s.live v.allocation = true ∧ v.generation = a.generation v.allocation ∧
  a.base v.allocation ≤ addressNumber t p ∧
  addressNumber t p + n ≤ a.base v.allocation + s.size v.allocation ∧
  a.base v.allocation + s.size v.allocation ≤ 256 ^ t.width

instance (t : Representation.Target) (a : AddressSpace) (s : ByteMemory.State C)
    (p : Representation.Ptr t) (v : Representation.Provenance) (n : Nat) :
    Decidable (Resolvable t a s p v n) := by
  unfold Resolvable
  infer_instance

inductive ResolveError where
  | noProvenance
  | rejected
  deriving DecidableEq, Repr

def resolve (t : Representation.Target) (a : AddressSpace) (s : ByteMemory.State C)
    (p : Representation.Ptr t) (n : Nat) : Except ResolveError ByteMemory.Ptr :=
  -- Rejecting no-provenance even at n=0 is an extra restricted pilot policy.
  -- It is not a classification of Rust's zero-size or external-memory accesses.
  match p.provenance with
  | none => .error .noProvenance
  | some v =>
    if Resolvable t a s p v n then
      .ok ⟨v.allocation, addressNumber t p - a.base v.allocation, v.tag⟩
    else .error .rejected

theorem resolve_success (t : Representation.Target) (a : AddressSpace) (s : ByteMemory.State C)
    (p : Representation.Ptr t) (n : Nat) (q : ByteMemory.Ptr)
    (ok : resolve t a s p n = .ok q) :
    ∃ v, p.provenance = some v ∧ Resolvable t a s p v n ∧
      q.allocation = v.allocation ∧ q.tag = v.tag ∧
      a.base v.allocation + q.offset = addressNumber t p ∧
      q.offset + n ≤ s.size v.allocation := by
  cases hp : p.provenance with
  | none => simp [resolve, hp] at ok
  | some v =>
    by_cases h : Resolvable t a s p v n
    · have hq : q = ⟨v.allocation, addressNumber t p - a.base v.allocation, v.tag⟩ := by
        simpa [resolve, hp, h] using ok.symm
      subst q
      refine ⟨v, rfl, h, rfl, rfl, ?_, ?_⟩
      · change a.base v.allocation +
          (addressNumber t p - a.base v.allocation) = addressNumber t p
        have lower := h.2.2.1
        omega
      · change (addressNumber t p - a.base v.allocation) + n ≤ s.size v.allocation
        have lower := h.2.2.1
        have upper := h.2.2.2.1
        omega
    · simp [resolve, hp, h] at ok

theorem no_provenance_resolution (t : Representation.Target) (a : AddressSpace) (s : ByteMemory.State C)
    (p : Representation.Ptr t) (n : Nat) (none : p.provenance = none) :
    resolve t a s p n = .error .noProvenance := by
  simp [resolve, none]

theorem stale_generation_rejected (t : Representation.Target) (a : AddressSpace) (s : ByteMemory.State C)
    (p : Representation.Ptr t) (v : Representation.Provenance) (n : Nat)
    (prov : p.provenance = some v) (stale : v.generation ≠ a.generation v.allocation) :
    resolve t a s p n = .error .rejected := by
  have denied : ¬ Resolvable t a s p v n := by
    intro h
    exact stale h.2.1
  simp [resolve, prov, denied]

inductive AccessError where
  | resolution (error : ResolveError)
  | memory (error : ByteMemory.Error)
  | typed (error : TypedError)
  deriving DecidableEq, Repr

inductive AccessResult (C : Type) (n : Nat) where
  | success (data : ByteMemory.Block C n) (after : ByteMemory.State C)
  | failure (error : AccessError) (after : ByteMemory.State C)

def readThroughPointer (t : Representation.Target) (a : AddressSpace)
    (policy : ByteMemory.Policy) (s : ByteMemory.State C)
    (p : Representation.Ptr t) (n : Nat) : AccessResult C n :=
  match resolve t a s p n with
  | .error e => .failure (.resolution e) s
  | .ok q =>
    match ByteMemory.readSnapshot policy s q n with
    | .error e => .failure (.memory e) s
    | .ok (b, after) => .success b after

theorem readThroughPointer_supported (t : Representation.Target) (a : AddressSpace)
    (policy : ByteMemory.Policy) (s : ByteMemory.State C) (p : Representation.Ptr t)
    (v : Representation.Provenance) (n : Nat)
    (prov : p.provenance = some v) (admitted : Resolvable t a s p v n)
    (ready : ByteMemory.ReadReady s
      ⟨v.allocation, addressNumber t p - a.base v.allocation, v.tag⟩ n) :
    readThroughPointer t a policy s p n =
      .success (ByteMemory.getWindow s
        ⟨v.allocation, addressNumber t p - a.base v.allocation, v.tag⟩ n)
        (ByteMemory.afterRead policy s
          ⟨v.allocation, addressNumber t p - a.base v.allocation, v.tag⟩ n) := by
  simp [readThroughPointer, resolve, prov, admitted, ByteMemory.readSnapshot_ok _ _ _ _ ready]

/-- Reading pointer storage and reading through the resulting pointer are
    separate operations with separate permission effects and checks. -/
def loadAndRead (t : Representation.Target) (a : AddressSpace)
    (policy : ByteMemory.Policy) (s : ByteMemory.State Representation.Cell)
    (src : ByteMemory.Ptr) (n : Nat) : AccessResult Representation.Cell n :=
  match loadPointer t policy s src with
  | .failure e after => .failure (.typed e) after
  | .success p after => readThroughPointer t a policy after p n

theorem loadAndRead_supported (t : Representation.Target) (a : AddressSpace)
    (policy : ByteMemory.Policy) (s : ByteMemory.State Representation.Cell)
    (src : ByteMemory.Ptr) (p : Representation.Ptr t)
    (v : Representation.Provenance) (n : Nat)
    (hr : ByteMemory.ReadReady s src t.width)
    (decoded : Representation.decodePtr t (memoryRep s src) = some p)
    (prov : p.provenance = some v)
    (admitted : Resolvable t a (ByteMemory.afterRead policy s src t.width) p v n)
    (ready : ByteMemory.ReadReady (ByteMemory.afterRead policy s src t.width)
      ⟨v.allocation, addressNumber t p - a.base v.allocation, v.tag⟩ n) :
    loadAndRead t a policy s src n =
      .success (ByteMemory.getWindow (ByteMemory.afterRead policy s src t.width)
        ⟨v.allocation, addressNumber t p - a.base v.allocation, v.tag⟩ n)
        (ByteMemory.afterRead policy (ByteMemory.afterRead policy s src t.width)
          ⟨v.allocation, addressNumber t p - a.base v.allocation, v.tag⟩ n) := by
  rw [loadAndRead, loadPointer_supported t policy s src p hr decoded]
  exact readThroughPointer_supported t a policy _ p v n prov admitted ready

theorem decoded_stale_pointer_cannot_read (t : Representation.Target) (a : AddressSpace)
    (policy : ByteMemory.Policy) (s : ByteMemory.State Representation.Cell)
    (src : ByteMemory.Ptr) (p : Representation.Ptr t)
    (v : Representation.Provenance) (n : Nat)
    (hr : ByteMemory.ReadReady s src t.width)
    (decoded : Representation.decodePtr t (memoryRep s src) = some p)
    (prov : p.provenance = some v) (stale : v.generation ≠ a.generation v.allocation) :
    loadAndRead t a policy s src n =
      .failure (.resolution .rejected) (ByteMemory.afterRead policy s src t.width) := by
  rw [loadAndRead, loadPointer_supported t policy s src p hr decoded]
  simp only [readThroughPointer, stale_generation_rejected t a _ p v n prov stale]

#print axioms runRawCopy_projection
#print axioms runRawCopy_success
#print axioms rawCopy_failure_retains_revoked_grant
#print axioms rawCopy_pointer_reconstruction
#print axioms rawCopy_aggregate_reconstruction
#print axioms loadPointer_supported
#print axioms loadPointer_uninitialized
#print axioms storeAggregate_supported
#print axioms typedCopyAggregate_supported
#print axioms raw_and_typed_padding
#print axioms digitsValue_bound
#print axioms addressNumber_bound
#print axioms resolve_success
#print axioms no_provenance_resolution
#print axioms stale_generation_rejected
#print axioms readThroughPointer_supported
#print axioms loadAndRead_supported
#print axioms decoded_stale_pointer_cannot_read

end AnnealResearch.Transfers
