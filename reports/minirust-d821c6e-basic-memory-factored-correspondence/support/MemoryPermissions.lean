import AnnealResearch.MiniRustFactored
import AnnealResearch.BorrowFrame

/-!
Owned composition of the audited BasicMemory kernels with the selected flat
BorrowFrame table. The operations are positive-size ONE-BYTE raw read, initialized
u8 read, and raw write. Every permission key is derived from the actual memory
pointer's resolved allocation ID and byte offset; no separately supplied spatial
permission key is accepted. The caller supplies only pointer, tag, alignment,
and (for write) the raw byte value.

Basic alignment/provenance/lifetime/bounds checks run before the permission hook.
The pure underlying load/store may compute proposed bytes/state before the hook;
only successful permission checks expose bytes or commit a proposed write.
Initialized-value checking follows the read hook, and its failure retains the
hook's permission effects. Initialized numeric bytes accept any optional fragment.

This composition reuses the SAME explicit flat permission table/helper in both
implementations. The memory dispatches independently invoke their existing
coupled/factored kernels. It is not the full Tree Borrows graph, retag/protector
algorithm, a typed Rust validity model, or a Rust/MiniRust adequacy theorem.
No allocation/free operation is added here. noChoice remains a distinct result,
although the selected one-byte load/store kernels cannot generate allocator
noChoice. Unsupported representations and all failed operations remain results,
never filtered transitions. Residual state is present on every result.
-/

namespace AnnealResearch.MemoryPermissions


structure Coupled where
  memory : MiniRustReference.State
  permissions : BorrowFrame.Store

structure Factored where
  memory : MiniRustFactored.State
  permissions : BorrowFrame.Store

inductive Fault where
  | basic (reason : MiniRustReference.UB)
  | permission (reason : BorrowFrame.UB)
  | uninitialized
  deriving DecidableEq

inductive Result (Value State : Type) where
  | ok (value : Value) (state : State)
  | ub (fault : Fault) (state : State)
  | unsupported (state : State)
  | noChoice (state : State)

inductive Reply where
  | raw (bytes : List MiniRustReference.Byte)
  | number (value : Fin 256)
  | unit
  deriving DecidableEq

inductive Command where
  | readRaw (pointer : MiniRustReference.Ptr) (tag align : Nat)
  | readU8 (pointer : MiniRustReference.Ptr) (tag align : Nat)
  | writeRaw (pointer : MiniRustReference.Ptr) (tag align : Nat) (byte : MiniRustReference.Byte)
  deriving DecidableEq

def reify (state : Factored) : Coupled :=
  ⟨MiniRustFactored.reify state.memory, state.permissions⟩

def encode (state : Coupled) : Factored :=
  ⟨MiniRustFactored.encode state.memory, state.permissions⟩

def resultMap (f : S → T) : Result V S → Result V T
  | .ok value state => .ok value (f state)
  | .ub fault state => .ub fault (f state)
  | .unsupported state => .unsupported (f state)
  | .noChoice state => .noChoice (f state)

theorem reify_encode (state : Coupled) : reify (encode state) = state := by
  cases state
  simp [reify, encode, MiniRustFactored.reify_encode]

/-- Shared table operation. id/offset are supplied only by a successful actual
memory resolution below, rather than by the command or a separate permission. -/
def permissionStep (permissions : BorrowFrame.Store) (id offset tag : Nat) (kind : BorrowFrame.AccessKind) :
    Except BorrowFrame.UB BorrowFrame.Store :=
  BorrowFrame.perform permissions ⟨⟨id, offset⟩, tag, kind⟩

def readCoupled (state : Coupled) (pointer : MiniRustReference.Ptr) (tag align : Nat) :
    Result Reply Coupled :=
  match MiniRustReference.load state.memory pointer 1 align with
  | .ub reason => .ub (.basic reason) state
  | .unsupported => .unsupported state
  | .noChoice => .noChoice state
  | .ok (bytes, memory) =>
    match MiniRustReference.checkPtr state.memory pointer 1 with
    | .ub reason => .ub (.basic reason) state
    | .unsupported => .unsupported state
    | .noChoice => .noChoice state
    | .ok none => .unsupported state
    | .ok (some span) =>
      match permissionStep state.permissions span.id span.offset tag .read with
      | .error reason => .ub (.permission reason) state
      | .ok permissions => .ok (.raw bytes) ⟨memory, permissions⟩

def readFactored (state : Factored) (pointer : MiniRustReference.Ptr) (tag align : Nat) :
    Result Reply Factored :=
  match MiniRustFactored.load state.memory pointer 1 align with
  | .ub reason => .ub (.basic reason) state
  | .unsupported => .unsupported state
  | .noChoice => .noChoice state
  | .ok (bytes, memory) =>
    match MiniRustFactored.resolve state.memory pointer 1 with
    | .ub reason => .ub (.basic reason) state
    | .unsupported => .unsupported state
    | .noChoice => .noChoice state
    | .ok none => .unsupported state
    | .ok (some span) =>
      match permissionStep state.permissions span.id span.offset tag .read with
      | .error reason => .ub (.permission reason) state
      | .ok permissions => .ok (.raw bytes) ⟨memory, permissions⟩

def writeCoupled (state : Coupled) (pointer : MiniRustReference.Ptr) (tag align : Nat) (byte : MiniRustReference.Byte) :
    Result Reply Coupled :=
  match MiniRustReference.store state.memory pointer [byte] align with
  | .ub reason => .ub (.basic reason) state
  | .unsupported => .unsupported state
  | .noChoice => .noChoice state
  | .ok memory =>
    match MiniRustReference.checkPtr state.memory pointer 1 with
    | .ub reason => .ub (.basic reason) state
    | .unsupported => .unsupported state
    | .noChoice => .noChoice state
    | .ok none => .unsupported state
    | .ok (some span) =>
      match permissionStep state.permissions span.id span.offset tag .write with
      | .error reason => .ub (.permission reason) state
      | .ok permissions => .ok .unit ⟨memory, permissions⟩

def writeFactored (state : Factored) (pointer : MiniRustReference.Ptr) (tag align : Nat) (byte : MiniRustReference.Byte) :
    Result Reply Factored :=
  match MiniRustFactored.store state.memory pointer [byte] align with
  | .ub reason => .ub (.basic reason) state
  | .unsupported => .unsupported state
  | .noChoice => .noChoice state
  | .ok memory =>
    match MiniRustFactored.resolve state.memory pointer 1 with
    | .ub reason => .ub (.basic reason) state
    | .unsupported => .unsupported state
    | .noChoice => .noChoice state
    | .ok none => .unsupported state
    | .ok (some span) =>
      match permissionStep state.permissions span.id span.offset tag .write with
      | .error reason => .ub (.permission reason) state
      | .ok permissions => .ok .unit ⟨memory, permissions⟩

/-- This selected initialized-u8 decoder ignores optional provenance exactly as
the pinned integer decoder does. It runs AFTER the permission-producing read.
The other success shapes are unreachable from these one-byte read kernels but
remain explicit failure cases of this total classifier. -/
def decodeInitialized : Result Reply S → Result Reply S
  | .ok (.raw [.init value _]) state => .ok (.number value) state
  | .ok _ state => .ub .uninitialized state
  | .ub fault state => .ub fault state
  | .unsupported state => .unsupported state
  | .noChoice state => .noChoice state

def runCoupled (command : Command) (state : Coupled) : Result Reply Coupled :=
  match command with
  | .readRaw pointer tag align => readCoupled state pointer tag align
  | .readU8 pointer tag align => decodeInitialized (readCoupled state pointer tag align)
  | .writeRaw pointer tag align byte => writeCoupled state pointer tag align byte

def runFactored (command : Command) (state : Factored) : Result Reply Factored :=
  match command with
  | .readRaw pointer tag align => readFactored state pointer tag align
  | .readU8 pointer tag align => decodeInitialized (readFactored state pointer tag align)
  | .writeRaw pointer tag align byte => writeFactored state pointer tag align byte

theorem decodeInitialized_map (f : S → T) (result : Result Reply S) :
    decodeInitialized (resultMap f result) = resultMap f (decodeInitialized result) := by
  cases result with
  | ok reply state =>
    cases reply with
    | raw bytes =>
      cases bytes with
      | nil => rfl
      | cons first rest =>
        cases rest with
        | nil => cases first <;> rfl
        | cons next rest => cases first <;> rfl
    | number value => rfl
    | unit => rfl
  | ub fault state => rfl
  | unsupported state => rfl
  | noChoice state => rfl

/-- All-state equality includes Basic UB, permission UB, unsupported/noChoice,
and every success/failure residual state; no StateWF/safety premise is assumed. -/
theorem read_reify (state : Factored) (pointer : MiniRustReference.Ptr) (tag align : Nat) :
    readCoupled (reify state) pointer tag align =
      resultMap reify (readFactored state pointer tag align) := by
  unfold readCoupled readFactored
  simp only [reify]
  rw [MiniRustFactored.load_reify, MiniRustFactored.resolve_reify]
  cases loaded : MiniRustFactored.load state.memory pointer 1 align with
  | ub reason => rfl
  | unsupported => rfl
  | noChoice => rfl
  | ok value =>
    rcases value with ⟨bytes, memory⟩
    cases resolved : MiniRustFactored.resolve state.memory pointer 1 with
    | ub reason => rfl
    | unsupported => rfl
    | noChoice => rfl
    | ok optional =>
      cases optional with
      | none => rfl
      | some span =>
        simp only [MiniRustFactored.resultMap, Option.map, MiniRustFactored.reifySpan]
        cases permitted : permissionStep state.permissions span.id span.offset tag .read <;>
          simp [resultMap, reify]

theorem write_reify (state : Factored) (pointer : MiniRustReference.Ptr) (tag align : Nat) (byte : MiniRustReference.Byte) :
    writeCoupled (reify state) pointer tag align byte =
      resultMap reify (writeFactored state pointer tag align byte) := by
  unfold writeCoupled writeFactored
  simp only [reify]
  rw [MiniRustFactored.store_reify, MiniRustFactored.resolve_reify]
  cases stored : MiniRustFactored.store state.memory pointer [byte] align with
  | ub reason => rfl
  | unsupported => rfl
  | noChoice => rfl
  | ok memory =>
    cases resolved : MiniRustFactored.resolve state.memory pointer 1 with
    | ub reason => rfl
    | unsupported => rfl
    | noChoice => rfl
    | ok optional =>
      cases optional with
      | none => rfl
      | some span =>
        simp only [MiniRustFactored.resultMap, Option.map, MiniRustFactored.reifySpan]
        cases permitted : permissionStep state.permissions span.id span.offset tag .write <;>
          simp [resultMap, reify]

theorem run_reify (command : Command) (state : Factored) :
    runCoupled command (reify state) = resultMap reify (runFactored command state) := by
  cases command with
  | readRaw pointer tag align => exact read_reify state pointer tag align
  | readU8 pointer tag align =>
      simp only [runCoupled, runFactored, read_reify, decodeInitialized_map]
  | writeRaw pointer tag align byte => exact write_reify state pointer tag align byte

theorem encoded_run (command : Command) (state : Coupled) :
    runCoupled command state = resultMap reify (runFactored command (encode state)) := by
  simpa [reify_encode] using run_reify command (encode state)

namespace Fixtures

def byte (value : Fin 256) : MiniRustReference.Byte := .init value none

def block (first second : MiniRustReference.Byte) : MiniRustReference.Allocation :=
  { base := 16, size := 2, align := 1, kind := .heap, live := true
    data := fun offset => if offset = 0 then first else second }

def liveMemory (first second : MiniRustReference.Byte) : MiniRustReference.State :=
  { next := 1, allocations := fun id => if id = 0 then some (block first second) else none }

def pointer0 : MiniRustReference.Ptr := ⟨16, some 0⟩
def pointer1 : MiniRustReference.Ptr := ⟨17, some 0⟩

def access0 (tag : Nat) (kind : BorrowFrame.AccessKind) : BorrowFrame.Access := ⟨⟨0, 0⟩, tag, kind⟩
def allCell : BorrowFrame.Store := fun _ _ => .Cell
def aliasPermissions : BorrowFrame.Store := fun _ tag => if tag = 0 then .Cell else .Unique

def stable (value : Fin 256) : Coupled :=
  ⟨liveMemory (byte value) (byte value), allCell⟩
def stableRead0 (value : Fin 256) : Coupled :=
  { stable value with permissions := BorrowFrame.update allCell (access0 0 .read) .Cell }
def stableRead1 (value : Fin 256) : Coupled :=
  { stableRead0 value with
    permissions := BorrowFrame.update (stableRead0 value).permissions (access0 1 .read) .Cell }

def writtenMemory (value written : Fin 256) : MiniRustReference.State :=
  let bytes : List MiniRustReference.Byte := [byte written]
  let allocation := block (byte value) (byte value)
  let writtenData : Nat → MiniRustReference.Byte := fun index =>
    if 0 ≤ index ∧ index < 0 + bytes.length then
      List.getD bytes (index - 0) MiniRustReference.Byte.uninit
    else allocation.data index
  MiniRustReference.replace (liveMemory (byte value) (byte value)) 0
    { allocation with data := writtenData }

def stableWritten (value written : Fin 256) : Coupled :=
  ⟨writtenMemory value written,
    BorrowFrame.update (stableRead1 value).permissions (access0 1 .write) .Cell⟩

def aliasing (value : Fin 256) : Coupled :=
  ⟨liveMemory (byte value) (byte value), aliasPermissions⟩
def aliasRead0 (value : Fin 256) : Coupled :=
  { aliasing value with permissions := BorrowFrame.update aliasPermissions (access0 0 .read) .Cell }
def aliasRead1 (value : Fin 256) : Coupled :=
  { aliasRead0 value with
    permissions := BorrowFrame.update (aliasRead0 value).permissions (access0 1 .read) .Frozen }

def uninitState : Coupled := ⟨liveMemory .uninit .uninit, aliasPermissions⟩
def uninitAfterRead0 : Coupled :=
  { uninitState with permissions := BorrowFrame.update aliasPermissions (access0 0 .read) .Cell }
def disabledState : Coupled :=
  { uninitState with permissions := fun _ _ => .Disabled }

theorem stable_raw_read (value : Fin 256) :
    runCoupled (.readRaw pointer0 0 1) (stable value) =
      .ok (.raw [byte value]) (stableRead0 value) := rfl

theorem stable_typed_read (value : Fin 256) :
    runCoupled (.readU8 pointer0 1 1) (stableRead0 value) =
      .ok (.number value) (stableRead1 value) := rfl

theorem stable_write (value written : Fin 256) :
    runCoupled (.writeRaw pointer0 1 1 (byte written)) (stableRead1 value) =
      .ok .unit (stableWritten value written) := rfl

theorem alias_raw_read (value : Fin 256) :
    runCoupled (.readRaw pointer0 0 1) (aliasing value) =
      .ok (.raw [byte value]) (aliasRead0 value) := rfl

theorem alias_read_freezes (value : Fin 256) :
    (aliasing value).permissions ⟨0, 0⟩ 1 = .Unique ∧
    (aliasRead0 value).permissions ⟨0, 0⟩ 1 = .Frozen := ⟨rfl, rfl⟩

theorem alias_typed_read (value : Fin 256) :
    runCoupled (.readU8 pointer0 1 1) (aliasRead0 value) =
      .ok (.number value) (aliasRead1 value) := rfl

theorem alias_write_fails (value written : Fin 256) :
    runCoupled (.writeRaw pointer0 1 1 (byte written)) (aliasRead1 value) =
      .ub (.permission .localWriteFrozen) (aliasRead1 value) := rfl

theorem uninit_typed_read_retains_permissions :
    runCoupled (.readU8 pointer0 0 1) uninitState =
      .ub .uninitialized uninitAfterRead0 ∧
    uninitAfterRead0.permissions ⟨0, 0⟩ 1 = .Frozen := ⟨rfl, rfl⟩

theorem uninit_later_write_fails (written : Fin 256) :
    runCoupled (.writeRaw pointer0 1 1 (byte written)) uninitAfterRead0 =
      .ub (.permission .localWriteFrozen) uninitAfterRead0 := rfl

theorem basic_alignment_precedes_permission_and_decode :
    runCoupled (.readU8 pointer1 0 2) disabledState =
      .ub (.basic .misalignedLoad) disabledState := rfl

theorem permission_precedes_initialized_value_check :
    runCoupled (.readU8 pointer0 0 1) disabledState =
      .ub (.permission .localReadDisabled) disabledState := rfl

theorem unsupported_alignment_is_preserved :
    runCoupled (.readRaw pointer0 0 0) uninitState = .unsupported uninitState := rfl

theorem initialized_fragment_is_accepted (value : Fin 256) (fragment : MiniRustReference.Frag) :
    decodeInitialized (.ok (.raw [.init value (some fragment)]) uninitAfterRead0) =
      .ok (.number value) uninitAfterRead0 := rfl

theorem liveMemory_WF (first second : MiniRustReference.Byte)
    (firstWF : MiniRustReference.ByteWF (liveMemory first second) first)
    (secondWF : MiniRustReference.ByteWF (liveMemory first second) second) :
    MiniRustReference.StateWF (liveMemory first second) := by
  constructor
  · intro id
    by_cases same : id = 0
    · subst id
      simp [liveMemory]
    · simp [liveMemory, same] <;> omega
  · intro id actual found
    by_cases same : id = 0
    · subst id
      have equal : actual = block first second := by simpa [liveMemory] using found.symm
      subst actual
      change 0 < 16 ∧ MiniRustReference.AlignWF 1 ∧ 16 % 1 = 0 ∧
        2 < MiniRustReference.sizeLimit ∧ 16 + 2 < MiniRustReference.addressLimit
      exact ⟨by decide, ⟨0, rfl⟩, by decide, by decide, by decide⟩
    · simp [liveMemory, same] at found
  · intro id actual offset found bound
    by_cases same : id = 0
    · subst id
      have equal : actual = block first second := by simpa [liveMemory] using found.symm
      subst actual
      by_cases zero : offset = 0
      · simpa [block, zero] using firstWF
      · simpa [block, zero] using secondWF
    · simp [liveMemory, same] at found
  · intro id firstAllocation otherId secondAllocation firstFound secondFound different _ _
    have firstZero : id = 0 := by
      by_cases zero : id = 0
      · exact zero
      · simp [liveMemory, zero] at firstFound
    have secondZero : otherId = 0 := by
      by_cases zero : otherId = 0
      · exact zero
      · simp [liveMemory, zero] at secondFound
    exact False.elim (different (firstZero.trans secondZero.symm))

theorem pointer0_WF (first second : MiniRustReference.Byte) : MiniRustReference.PtrWF (liveMemory first second) pointer0 := by
  change 16 < MiniRustReference.addressLimit ∧ 0 < 1
  exact ⟨by decide, by decide⟩

theorem pointer1_WF (first second : MiniRustReference.Byte) : MiniRustReference.PtrWF (liveMemory first second) pointer1 := by
  change 17 < MiniRustReference.addressLimit ∧ 0 < 1
  exact ⟨by decide, by decide⟩

theorem stable_WF (value : Fin 256) : MiniRustReference.StateWF (stable value).memory :=
  liveMemory_WF _ _ True.intro True.intro

theorem aliasing_WF (value : Fin 256) : MiniRustReference.StateWF (aliasing value).memory :=
  liveMemory_WF _ _ True.intro True.intro

theorem uninit_WF : MiniRustReference.StateWF uninitState.memory :=
  liveMemory_WF _ _ True.intro True.intro

end Fixtures

#print axioms reify_encode
#print axioms decodeInitialized_map
#print axioms read_reify
#print axioms write_reify
#print axioms run_reify
#print axioms encoded_run
#print axioms Fixtures.stable_raw_read
#print axioms Fixtures.stable_typed_read
#print axioms Fixtures.stable_write
#print axioms Fixtures.alias_raw_read
#print axioms Fixtures.alias_read_freezes
#print axioms Fixtures.alias_typed_read
#print axioms Fixtures.alias_write_fails
#print axioms Fixtures.uninit_typed_read_retains_permissions
#print axioms Fixtures.uninit_later_write_fails
#print axioms Fixtures.basic_alignment_precedes_permission_and_decode
#print axioms Fixtures.permission_precedes_initialized_value_check
#print axioms Fixtures.unsupported_alignment_is_preserved
#print axioms Fixtures.initialized_fragment_is_accepted
#print axioms Fixtures.liveMemory_WF
#print axioms Fixtures.pointer0_WF
#print axioms Fixtures.pointer1_WF
#print axioms Fixtures.stable_WF
#print axioms Fixtures.aliasing_WF
#print axioms Fixtures.uninit_WF

end AnnealResearch.MemoryPermissions
