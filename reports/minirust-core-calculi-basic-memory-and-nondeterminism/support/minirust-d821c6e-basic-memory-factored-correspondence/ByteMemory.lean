import Std

/-!
Generic byte-addressed operational pilot. Each `C` is the complete data at one
byte position; commands never inspect it. Thus initialization markers and
provenance fragments supplied by a representation module survive verbatim.
Allocation identity and mathematical byte offset are distinct. There is no
absolute address or implied allocation alignment, allocation reuse, machine
overflow, Rust validity check, or Rust alias-model adequacy theorem here.

An accepted primitive snapshot is atomic at this model layer. In particular,
overlap uses the initial snapshot; this is neither a forward-loop simulation
nor a model of per-byte interleavings. Every error is a failed toy check, not
a proved classification of Rust undefined behavior.
-/
namespace AnnealResearch.ByteMemory

structure Loc where
  allocation : Nat
  offset : Nat
  deriving DecidableEq, Repr

structure Ptr where
  allocation : Nat
  offset : Nat
  tag : Nat
  deriving DecidableEq, Repr

def Ptr.loc (p : Ptr) : Loc := ⟨p.allocation, p.offset⟩
def Ptr.locAt (p : Ptr) (i : Nat) : Loc := ⟨p.allocation, p.offset + i⟩
def Ptr.shift (p : Ptr) (i : Nat) : Ptr := ⟨p.allocation, p.offset + i, p.tag⟩

abbrev Block (C : Type) (n : Nat) := Fin n → C

structure State (C : Type) where
  cells : Loc → C
  live : Nat → Bool
  size : Nat → Nat
  readGrant : Ptr → Bool
  writeGrant : Ptr → Bool

inductive Policy where
  | stable
  | siblingRevoking
  deriving DecidableEq, Repr

inductive Error where
  | dead
  | bounds
  | authority
  deriving DecidableEq, Repr

def Span (p : Ptr) (n : Nat) (l : Loc) : Prop :=
  l.allocation = p.allocation ∧ p.offset ≤ l.offset ∧ l.offset < p.offset + n

instance (p : Ptr) (n : Nat) (l : Loc) : Decidable (Span p n l) := by
  unfold Span
  infer_instance

def Fits (s : State C) (p : Ptr) (n : Nat) : Prop :=
  s.live p.allocation = true ∧ p.offset + n ≤ s.size p.allocation

def ReadReady (s : State C) (p : Ptr) (n : Nat) : Prop :=
  Fits s p n ∧ ∀ i : Fin n, s.readGrant (p.shift i.val) = true

def WriteReady (s : State C) (p : Ptr) (n : Nat) : Prop :=
  Fits s p n ∧ ∀ i : Fin n, s.writeGrant (p.shift i.val) = true

instance (s : State C) (p : Ptr) (n : Nat) : Decidable (ReadReady s p n) := by
  unfold ReadReady Fits
  infer_instance

instance (s : State C) (p : Ptr) (n : Nat) : Decidable (WriteReady s p n) := by
  unfold WriteReady Fits
  infer_instance

def getWindow (s : State C) (p : Ptr) (n : Nat) : Block C n :=
  fun i => s.cells (p.locAt i.val)

def accessError (s : State C) (p : Ptr) (n : Nat) : Error :=
  if s.live p.allocation = false then .dead
  else if ¬ p.offset + n ≤ s.size p.allocation then .bounds else .authority

def revoke (policy : Policy) (p : Ptr) (n : Nat)
    (grant : Ptr → Bool) (q : Ptr) : Bool :=
  if policy = .siblingRevoking ∧ Span p n q.loc ∧ q.tag ≠ p.tag
  then false else grant q

/-- Named post-read permission state; cell storage is unchanged. -/
def afterRead (policy : Policy) (s : State C) (p : Ptr) (n : Nat) : State C :=
  { s with
    readGrant := revoke policy p n s.readGrant
    writeGrant := revoke policy p n s.writeGrant }

def readSnapshot (policy : Policy) (s : State C) (p : Ptr) (n : Nat) :
    Except Error (Block C n × State C) :=
  if ReadReady s p n then .ok (getWindow s p n, afterRead policy s p n)
  else .error (accessError s p n)

def writeCells (s : State C) (p : Ptr) (n : Nat) (b : Block C n) (l : Loc) : C :=
  if h : Span p n l then b ⟨l.offset - p.offset, by
    have hlo := h.2.1
    have hhi := h.2.2
    omega⟩
  else s.cells l

def afterWrite (policy : Policy) (s : State C) (p : Ptr) (n : Nat)
    (b : Block C n) : State C :=
  { s with
    cells := writeCells s p n b
    readGrant := revoke policy p n s.readGrant
    writeGrant := revoke policy p n s.writeGrant }

def writeBlock (policy : Policy) (s : State C) (p : Ptr) (n : Nat)
    (b : Block C n) : Except Error (State C) :=
  if WriteReady s p n then .ok (afterWrite policy s p n b)
  else .error (accessError s p n)

/-- Errors propagate; no default value is supplied for a failed read. -/
def rawCopy (policy : Policy) (s : State C) (src dst : Ptr) (n : Nat) :
    Except Error (State C) :=
  match readSnapshot policy s src n with
  | .error e => .error e
  | .ok (b, r) => writeBlock policy r dst n b

theorem readSnapshot_ok (policy : Policy) (s : State C) (p : Ptr) (n : Nat)
    (h : ReadReady s p n) :
    readSnapshot policy s p n = .ok (getWindow s p n, afterRead policy s p n) := by
  simp [readSnapshot, h]

theorem readSnapshot_error (policy : Policy) (s : State C) (p : Ptr) (n : Nat)
    (h : ¬ ReadReady s p n) :
    readSnapshot policy s p n = .error (accessError s p n) := by
  simp [readSnapshot, h]

theorem readSnapshot_shape (policy : Policy) (s : State C) (p : Ptr) (n : Nat)
    (b : Block C n) (t : State C) (h : readSnapshot policy s p n = .ok (b, t)) :
    ReadReady s p n ∧ b = getWindow s p n ∧ t = afterRead policy s p n := by
  by_cases hr : ReadReady s p n
  · have he : (getWindow s p n, afterRead policy s p n) = (b, t) := by
      simpa [readSnapshot, hr] using h
    exact ⟨hr, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
  · simp [readSnapshot, hr] at h

theorem afterRead_storage (policy : Policy) (s : State C) (p : Ptr) (n : Nat)
    (l : Loc) : (afterRead policy s p n).cells l = s.cells l := rfl

/-- Every actual successful read returns exactly the full cell snapshot. -/
theorem readSnapshot_exact (policy : Policy) (s : State C) (p : Ptr) (n : Nat)
    (b : Block C n) (t : State C) (h : readSnapshot policy s p n = .ok (b, t)) :
    (∀ i, b i = s.cells (p.locAt i.val)) ∧ ∀ l, t.cells l = s.cells l := by
  obtain ⟨_, hb, ht⟩ := readSnapshot_shape policy s p n b t h
  subst b
  subst t
  exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem afterWrite_storage (policy : Policy) (s : State C) (p : Ptr) (n : Nat)
    (b : Block C n) (i : Fin n) :
    (afterWrite policy s p n b).cells (p.locAt i.val) = b i := by
  have hin : Span p n (p.locAt i.val) := by
    refine ⟨rfl, ?_, ?_⟩
    · change p.offset ≤ p.offset + i.val
      omega
    · change p.offset + i.val < p.offset + n
      exact Nat.add_lt_add_left i.isLt p.offset
  change writeCells s p n b (p.locAt i.val) = b i
  unfold writeCells
  rw [dite_eq_left hin]
  congr 1
  apply Fin.ext
  simp [Ptr.locAt]

theorem afterWrite_frame (policy : Policy) (s : State C) (p : Ptr) (n : Nat)
    (b : Block C n) (l : Loc) (h : ¬ Span p n l) :
    (afterWrite policy s p n b).cells l = s.cells l := by
  simp [afterWrite, writeCells, h]

theorem writeBlock_ok (policy : Policy) (s : State C) (p : Ptr) (n : Nat)
    (b : Block C n) (h : WriteReady s p n) :
    writeBlock policy s p n b = .ok (afterWrite policy s p n b) := by
  simp [writeBlock, h]

theorem writeBlock_shape (policy : Policy) (s : State C) (p : Ptr) (n : Nat)
    (b : Block C n) (t : State C) (h : writeBlock policy s p n b = .ok t) :
    WriteReady s p n ∧ t = afterWrite policy s p n b := by
  by_cases hw : WriteReady s p n
  · have he : afterWrite policy s p n b = t := by
      simpa [writeBlock, hw] using h
    exact ⟨hw, he.symm⟩
  · simp [writeBlock, hw] at h

theorem writeBlock_exact (policy : Policy) (s : State C) (p : Ptr) (n : Nat)
    (b : Block C n) (t : State C) (h : writeBlock policy s p n b = .ok t) :
    (∀ i, t.cells (p.locAt i.val) = b i) ∧
      ∀ l, ¬ Span p n l → t.cells l = s.cells l := by
  rw [(writeBlock_shape policy s p n b t h).2]
  exact ⟨afterWrite_storage policy s p n b, afterWrite_frame policy s p n b⟩

theorem rawCopy_eq_write (policy : Policy) (s : State C) (src dst : Ptr) (n : Nat)
    (hr : ReadReady s src n) :
    rawCopy policy s src dst n =
      writeBlock policy (afterRead policy s src n) dst n (getWindow s src n) := by
  simp [rawCopy, readSnapshot_ok policy s src n hr]

/-- The destination must be writable after the source read's permission effect.
    Arbitrary n and pointer offsets include partial fragments and overlapping spans. -/
theorem rawCopy_success (policy : Policy) (s : State C) (src dst : Ptr) (n : Nat)
    (hr : ReadReady s src n) (hw : WriteReady (afterRead policy s src n) dst n) :
    ∃ t, rawCopy policy s src dst n = .ok t ∧
      (∀ i : Fin n, t.cells (dst.locAt i.val) = s.cells (src.locAt i.val)) ∧
      (∀ l, ¬ Span dst n l → t.cells l = s.cells l) := by
  refine ⟨afterWrite policy (afterRead policy s src n) dst n (getWindow s src n), ?_, ?_, ?_⟩
  · rw [rawCopy_eq_write policy s src dst n hr]
    exact writeBlock_ok policy _ dst n _ hw
  · intro i
    exact afterWrite_storage policy _ dst n (getWindow s src n) i
  · intro l hl
    exact afterWrite_frame policy _ dst n (getWindow s src n) l hl

/-- Geometric separation preserves existing destination grants for this policy;
    it does not manufacture grants or establish a Rust framing principle. -/
theorem afterRead_writeReady_of_disjoint (policy : Policy) (s : State C)
    (src dst : Ptr) (n : Nat) (hw : WriteReady s dst n)
    (apart : ∀ i : Fin n, ¬ Span src n (dst.locAt i.val)) :
    WriteReady (afterRead policy s src n) dst n := by
  refine ⟨hw.1, ?_⟩
  intro i
  have hi : ¬ Span src n (dst.shift i.val).loc := by
    simpa [Ptr.shift, Ptr.loc, Ptr.locAt] using apart i
  simpa [afterRead, revoke, hi] using hw.2 i

def numericState : State Nat where
  cells := fun l => l.offset
  live := fun _ => true
  size := fun _ => 4
  readGrant := fun _ => true
  writeGrant := fun _ => true

def overlapSrc : Ptr := ⟨0, 0, 0⟩
def overlapDst : Ptr := ⟨0, 1, 0⟩
def overlapResult : State Nat :=
  afterWrite .stable (afterRead .stable numericState overlapSrc 2) overlapDst 2
    (getWindow numericState overlapSrc 2)

/-- Position two receives initial source position one, despite overwriting it. -/
theorem overlap_snapshot :
    rawCopy .stable numericState overlapSrc overlapDst 2 = .ok overlapResult ∧
      overlapResult.cells ⟨0, 1⟩ = 0 ∧ overlapResult.cells ⟨0, 2⟩ = 1 ∧
      overlapResult.cells ⟨0, 3⟩ = 3 := by
  have hr : ReadReady numericState overlapSrc 2 :=
    ⟨by simp [Fits, numericState, overlapSrc], fun _ => rfl⟩
  have hw : WriteReady (afterRead .stable numericState overlapSrc 2) overlapDst 2 := by
    refine ⟨by simp [Fits, afterRead, numericState, overlapDst], ?_⟩
    intro i
    simp [afterRead, revoke, numericState]
  refine ⟨?_, by decide, by decide, by decide⟩
  rw [rawCopy_eq_write .stable numericState overlapSrc overlapDst 2 hr]
  exact writeBlock_ok .stable _ overlapDst 2 _ hw

def partialResult : State Nat :=
  afterWrite .stable (afterRead .stable numericState ⟨0, 2, 0⟩ 1) ⟨1, 1, 0⟩ 1
    (getWindow numericState ⟨0, 2, 0⟩ 1)

theorem partial_range_overwrite :
    rawCopy .stable numericState ⟨0, 2, 0⟩ ⟨1, 1, 0⟩ 1 = .ok partialResult ∧
      partialResult.cells ⟨1, 1⟩ = 2 ∧ partialResult.cells ⟨1, 0⟩ = 0 ∧
      partialResult.cells ⟨1, 2⟩ = 2 := by
  have hr : ReadReady numericState ⟨0, 2, 0⟩ 1 :=
    ⟨by simp [Fits, numericState], fun _ => rfl⟩
  have hw : WriteReady (afterRead .stable numericState ⟨0, 2, 0⟩ 1) ⟨1, 1, 0⟩ 1 := by
    refine ⟨by simp [Fits, afterRead, numericState], ?_⟩
    intro i
    simp [afterRead, revoke, numericState]
  refine ⟨?_, by decide, by decide, by decide⟩
  rw [rawCopy_eq_write .stable numericState ⟨0, 2, 0⟩ ⟨1, 1, 0⟩ 1 hr]
  exact writeBlock_ok .stable _ ⟨1, 1, 0⟩ 1 _ hw

def owner : Ptr := ⟨0, 0, 0⟩
def sibling : Ptr := ⟨0, 0, 1⟩
def aliasInitial (value : C) : State C where
  cells := fun _ => value
  live := fun _ => true
  size := fun _ => 1
  readGrant := fun _ => true
  writeGrant := fun _ => true

/-- The same live, in-bounds copy succeeds or really fails its authority check. -/
theorem policies_distinct (value : C) :
    (∃ t, rawCopy .stable (aliasInitial value) sibling owner 1 = .ok t) ∧
      rawCopy .siblingRevoking (aliasInitial value) sibling owner 1 = .error .authority := by
  have hr : ReadReady (aliasInitial value) sibling 1 :=
    ⟨by simp [Fits, aliasInitial, sibling], fun _ => rfl⟩
  constructor
  · have hw : WriteReady (afterRead .stable (aliasInitial value) sibling 1) owner 1 := by
      refine ⟨by simp [Fits, afterRead, aliasInitial, owner], ?_⟩
      intro i
      simp [afterRead, revoke, aliasInitial]
    obtain ⟨t, ht, _⟩ := rawCopy_success .stable (aliasInitial value) sibling owner 1 hr hw
    exact ⟨t, ht⟩
  · rw [rawCopy_eq_write .siblingRevoking (aliasInitial value) sibling owner 1 hr]
    have noWrite : ¬ WriteReady (afterRead .siblingRevoking (aliasInitial value) sibling 1) owner 1 := by
      intro hw
      have bad := hw.2 ⟨0, by decide⟩
      simp [afterRead, revoke, Span, Ptr.shift, Ptr.loc, sibling, owner] at bad
    simp only [writeBlock, ite_eq_right noWrite]
    rfl

#print axioms readSnapshot_exact
#print axioms writeBlock_exact
#print axioms rawCopy_success
#print axioms afterRead_writeReady_of_disjoint
#print axioms overlap_snapshot
#print axioms partial_range_overwrite
#print axioms policies_distinct

end AnnealResearch.ByteMemory
