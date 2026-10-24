import Std

/-!
An owned, scoped memory-law pilot. These are abstract storage *slots*, not a
claim that a pointer has a one-byte physical representation. `Byte` slots are
the only slots read by the byte loop. No claim of Rust/97-clause adequacy is made.
Addresses and extents use unbounded mathematical naturals. Allocation reuse,
machine pointer overflow, Rust validity, references, and a full Rust alias model
are outside the owned scope. The admitted loop protocol has pairwise distinct
source/destination locations; explicit source bytes and access grants suffice.
-/
namespace AnnealResearch.Memory

abbrev Byte := Fin 256

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

inductive Cell where
  | uninit
  | byte (value : Byte)
  | pointer (value : Ptr)
  deriving DecidableEq, Repr

inductive Error where
  | dead
  | bounds
  | authority
  | uninitialized
  | representation
  deriving DecidableEq, Repr

structure Model where
  State : Type
  peek : State → Loc → Cell
  Readable : State → Ptr → Prop
  Writable : State → Ptr → Prop
  read : State → Ptr → Except Error (Byte × State)
  write : State → Ptr → Byte → Except Error State

/- The postconditions apply to actual successful commands. Authority is not
   inferred from initialized storage. All frame premises name locations. -/
structure Laws (m : Model) : Prop where
  read_success : ∀ s p b, m.Readable s p → m.peek s p.loc = .byte b →
    ∃ t, m.read s p = .ok (b, t)
  read_requires : ∀ s p b t, m.read s p = .ok (b, t) →
    m.Readable s p ∧ m.peek s p.loc = .byte b
  read_storage : ∀ s p b t, m.read s p = .ok (b, t) →
    ∀ l, m.peek t l = m.peek s l
  read_readable : ∀ s p b t, m.read s p = .ok (b, t) →
    ∀ q, q.loc ≠ p.loc → m.Readable s q → m.Readable t q
  read_writable : ∀ s p b t, m.read s p = .ok (b, t) →
    ∀ q, q.loc ≠ p.loc → m.Writable s q → m.Writable t q
  write_success : ∀ s p b, m.Writable s p → ∃ t, m.write s p b = .ok t
  write_requires : ∀ s p b t, m.write s p b = .ok t → m.Writable s p
  write_storage : ∀ s p b t, m.write s p b = .ok t → m.peek t p.loc = .byte b
  write_frame : ∀ s p b t, m.write s p b = .ok t →
    ∀ l, l ≠ p.loc → m.peek t l = m.peek s l
  write_readable : ∀ s p b t, m.write s p b = .ok t →
    ∀ q, q.loc ≠ p.loc → m.Readable s q → m.Readable t q
  write_writable : ∀ s p b t, m.write s p b = .ok t →
    ∀ q, q.loc ≠ p.loc → m.Writable s q → m.Writable t q

structure Job where
  src : Ptr
  dst : Ptr
  /-- Specification value: the command reads storage and does not consult it. -/
  value : Byte
  deriving DecidableEq, Repr

def Apart (a b : Job) : Prop :=
  a.src.loc ≠ b.src.loc ∧ a.src.loc ≠ b.dst.loc ∧
  a.dst.loc ≠ b.src.loc ∧ a.dst.loc ≠ b.dst.loc

def Separated : List Job → Prop
  | [] => True
  | j :: js => j.src.loc ≠ j.dst.loc ∧ (∀ k ∈ js, Apart j k) ∧ Separated js

def Ready (m : Model) (s : m.State) (js : List Job) : Prop :=
  ∀ j ∈ js, m.Readable s j.src ∧ m.Writable s j.dst ∧
    m.peek s j.src.loc = .byte j.value

def Finished (m : Model) (s : m.State) (js : List Job) : Prop :=
  ∀ j ∈ js, m.peek s j.dst.loc = .byte j.value

def Frame (m : Model) (before after : m.State) (js : List Job) : Prop :=
  ∀ l, (∀ j ∈ js, l ≠ j.dst.loc) → m.peek after l = m.peek before l

/-- A forward byte loop. Errors are propagated; there is no default read value. -/
def copy (m : Model) (s : m.State) : List Job → Except Error m.State
  | [] => .ok s
  | j :: js =>
    match m.read s j.src with
    | .error e => .error e
    | .ok (b, r) =>
      match m.write r j.dst b with
      | .error e => .error e
      | .ok w => copy m w js

/-- Universal in the model, length, byte contents, and admitted separated plan. -/
theorem copy_safe (m : Model) (laws : Laws m) (s : m.State) (js : List Job)
    (ready : Ready m s js) (sep : Separated js) :
    ∃ t, copy m s js = .ok t ∧ Finished m t js ∧ Frame m s t js := by
  induction js generalizing s with
  | nil =>
    exact ⟨s, rfl, by simp [Finished], by simp [Frame]⟩
  | cons j js ih =>
    have hj := ready j (by simp)
    obtain ⟨r, hr⟩ := laws.read_success s j.src j.value hj.1 hj.2.2
    obtain ⟨w, hw⟩ := laws.write_success r j.dst j.value
      (laws.read_writable s j.src j.value r hr j.dst (Ne.symm sep.1) hj.2.1)
    have tailReady : Ready m w js := by
      intro k hk
      have hkReady := ready k (by simp [hk])
      have apart := sep.2.1 k hk
      have rs : m.Readable r k.src := laws.read_readable s j.src j.value r hr
        k.src (Ne.symm apart.1) hkReady.1
      have wd : m.Writable r k.dst := laws.read_writable s j.src j.value r hr
        k.dst (Ne.symm apart.2.1) hkReady.2.1
      refine ⟨laws.write_readable r j.dst j.value w hw k.src
        (Ne.symm apart.2.2.1) rs,
        laws.write_writable r j.dst j.value w hw k.dst
        (Ne.symm apart.2.2.2) wd, ?_⟩
      rw [laws.write_frame r j.dst j.value w hw k.src.loc (Ne.symm apart.2.2.1),
        laws.read_storage s j.src j.value r hr k.src.loc]
      exact hkReady.2.2
    obtain ⟨t, ht, done, frame⟩ := ih w tailReady sep.2.2
    refine ⟨t, ?_, ?_, ?_⟩
    · simp [copy, hr, hw, ht]
    · intro k hk
      rcases List.mem_cons.mp hk with h | h
      · subst k
        rw [frame j.dst.loc (by
          intro k hk
          exact (sep.2.1 k hk).2.2.2)]
        exact laws.write_storage r j.dst j.value w hw
      · exact done k h
    · intro l hl
      rw [frame l (by intro k hk; exact hl k (by simp [hk])),
        laws.write_frame r j.dst j.value w hw l (hl j (by simp)),
        laws.read_storage s j.src j.value r hr l]

/- Dynamic allocation/access checks and storage are distinct fields. The second
   witness revokes sibling-tag authority at the accessed location. Its protocol
   here is the separated byte loop, not unrestricted Rust aliasing. -/
inductive Policy where
  | historyFree
  | siblingRevoking
  deriving DecidableEq, Repr

structure Store where
  cells : Loc → Cell
  live : Nat → Bool
  size : Nat → Nat
  readGrant : Ptr → Bool
  writeGrant : Ptr → Bool

def CanRead (s : Store) (p : Ptr) : Prop :=
  s.live p.allocation = true ∧ p.offset < s.size p.allocation ∧ s.readGrant p = true

def CanWrite (s : Store) (p : Ptr) : Prop :=
  s.live p.allocation = true ∧ p.offset < s.size p.allocation ∧ s.writeGrant p = true

instance (s : Store) (p : Ptr) : Decidable (CanRead s p) := by
  unfold CanRead
  infer_instance

instance (s : Store) (p : Ptr) : Decidable (CanWrite s p) := by
  unfold CanWrite
  infer_instance

def accessError (s : Store) (p : Ptr) : Error :=
  if s.live p.allocation = false then .dead
  else if ¬ p.offset < s.size p.allocation then .bounds else .authority

def revoke (policy : Policy) (p : Ptr) (grant : Ptr → Bool) (q : Ptr) : Bool :=
  if policy = .siblingRevoking ∧ q.loc = p.loc ∧ q.tag ≠ p.tag then false else grant q

def afterRead (policy : Policy) (s : Store) (p : Ptr) : Store :=
  { s with writeGrant := revoke policy p s.writeGrant }

def afterWrite (policy : Policy) (s : Store) (p : Ptr) (b : Byte) : Store :=
  { s with
    cells := fun l => if l = p.loc then .byte b else s.cells l
    readGrant := revoke policy p s.readGrant
    writeGrant := revoke policy p s.writeGrant }

def read (policy : Policy) (s : Store) (p : Ptr) : Except Error (Byte × Store) :=
  if CanRead s p then
    match s.cells p.loc with
    | .byte b => .ok (b, afterRead policy s p)
    | .uninit => .error .uninitialized
    | .pointer _ => .error .representation
  else .error (accessError s p)

def write (policy : Policy) (s : Store) (p : Ptr) (b : Byte) : Except Error Store :=
  if CanWrite s p then .ok (afterWrite policy s p b)
  else .error (accessError s p)

def concrete (policy : Policy) : Model where
  State := Store
  peek := Store.cells
  Readable := CanRead
  Writable := CanWrite
  read := read policy
  write := write policy

private theorem read_shape (policy : Policy) (s : Store) (p : Ptr) (b : Byte) (t : Store)
    (h : read policy s p = .ok (b, t)) :
    CanRead s p ∧ s.cells p.loc = .byte b ∧ t = afterRead policy s p := by
  by_cases ha : CanRead s p
  · cases hc : s.cells p.loc with
    | uninit => simp [read, ha, hc] at h
    | pointer ptr => simp [read, ha, hc] at h
    | byte v =>
      have he : (v, afterRead policy s p) = (b, t) := by
        simpa [read, ha, hc] using h
      have hv : v = b := congrArg Prod.fst he
      have ht : afterRead policy s p = t := congrArg Prod.snd he
      exact ⟨ha, congrArg Cell.byte hv, ht.symm⟩
  · simp [read, ha] at h

private theorem write_shape (policy : Policy) (s : Store) (p : Ptr) (b : Byte) (t : Store)
    (h : write policy s p b = .ok t) :
    CanWrite s p ∧ t = afterWrite policy s p b := by
  by_cases ha : CanWrite s p
  · have ht : afterWrite policy s p b = t := by
      simpa [write, ha] using h
    exact ⟨ha, ht.symm⟩
  · simp [write, ha] at h

private theorem revoke_other (policy : Policy) (p q : Ptr) (grant : Ptr → Bool)
    (h : q.loc ≠ p.loc) : revoke policy p grant q = grant q := by
  simp [revoke, h]

/-- Both policy choices satisfy every field of the same owned law record. -/
theorem concrete_laws (policy : Policy) : Laws (concrete policy) where
  read_success := by
    intro s p b ha hc
    change CanRead s p at ha
    change s.cells p.loc = .byte b at hc
    exact ⟨afterRead policy s p, by simp [concrete, read, ha, hc]⟩
  read_requires := by
    intro s p b t h
    exact ⟨(read_shape policy s p b t h).1, (read_shape policy s p b t h).2.1⟩
  read_storage := by
    intro s p b t h l
    rw [(read_shape policy s p b t h).2.2]
    rfl
  read_readable := by
    intro s p b t h q hq ha
    rw [(read_shape policy s p b t h).2.2]
    exact ha
  read_writable := by
    intro s p b t h q hq ha
    rw [(read_shape policy s p b t h).2.2]
    simpa only [concrete, CanWrite, afterRead, revoke_other policy p q s.writeGrant hq] using ha
  write_success := by
    intro s p b ha
    change CanWrite s p at ha
    exact ⟨afterWrite policy s p b, by simp [concrete, write, ha]⟩
  write_requires := by
    intro s p b t h
    exact (write_shape policy s p b t h).1
  write_storage := by
    intro s p b t h
    rw [(write_shape policy s p b t h).2]
    simp [concrete, afterWrite]
  write_frame := by
    intro s p b t h l hl
    rw [(write_shape policy s p b t h).2]
    simp [concrete, afterWrite, hl]
  write_readable := by
    intro s p b t h q hq ha
    rw [(write_shape policy s p b t h).2]
    simpa only [concrete, CanRead, afterWrite, revoke_other policy p q s.readGrant hq] using ha
  write_writable := by
    intro s p b t h q hq ha
    rw [(write_shape policy s p b t h).2]
    simpa only [concrete, CanWrite, afterWrite, revoke_other policy p q s.writeGrant hq] using ha

theorem laws_consistent : ∃ m : Model, Laws m :=
  ⟨concrete .historyFree, concrete_laws .historyFree⟩

theorem both_scoped_witnesses :
    Laws (concrete .historyFree) ∧ Laws (concrete .siblingRevoking) :=
  ⟨concrete_laws _, concrete_laws _⟩

def srcPtr (i : Nat) : Ptr := ⟨0, i, 0⟩
def dstPtr (i : Nat) : Ptr := ⟨1, i, 0⟩
def byteJob (i : Nat) (b : Byte) : Job := ⟨srcPtr i, dstPtr i, b⟩

def jobsFrom (start : Nat) : Nat → (Nat → Byte) → List Job
  | 0, _ => []
  | n + 1, values => byteJob start (values start) :: jobsFrom (start + 1) n values

theorem jobsFrom_length (start n : Nat) (values : Nat → Byte) :
    (jobsFrom start n values).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [jobsFrom, ih]

private theorem jobsFrom_mem (start n : Nat) (values : Nat → Byte) (j : Job)
    (h : j ∈ jobsFrom start n values) :
    ∃ i, start ≤ i ∧ i < start + n ∧ j = byteJob i (values i) := by
  induction n generalizing start with
  | zero => simp [jobsFrom] at h
  | succ n ih =>
    rcases List.mem_cons.mp h with hj | hj
    · exact ⟨start, Nat.le_refl _, by omega, hj⟩
    · obtain ⟨i, hi, hn, he⟩ := ih (start + 1) hj
      exact ⟨i, by omega, by omega, he⟩

private theorem mem_jobsFrom (start n : Nat) (values : Nat → Byte) (i : Nat)
    (lo : start ≤ i) (hi : i < start + n) :
    byteJob i (values i) ∈ jobsFrom start n values := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    by_cases he : i = start
    · subst i; exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      exact ih (start + 1) (by omega) (by omega)

theorem jobsFrom_separated (start n : Nat) (values : Nat → Byte) :
    Separated (jobsFrom start n values) := by
  induction n generalizing start with
  | zero => trivial
  | succ n ih =>
    refine ⟨by simp [byteJob, srcPtr, dstPtr, Ptr.loc], ?_, ih (start + 1)⟩
    intro j hj
    obtain ⟨i, hlo, hhi, rfl⟩ := jobsFrom_mem (start + 1) n values j hj
    have hne : start ≠ i := by omega
    simp [Apart, byteJob, srcPtr, dstPtr, Ptr.loc, hne]

/-- A nonempty family for every positive length, with wholly uninitialized dst. -/
def initial (n : Nat) (values : Nat → Byte) : Store where
  cells := fun l => if l.allocation = 0 ∧ l.offset < n then .byte (values l.offset) else .uninit
  live := fun a => decide (a = 0 ∨ a = 1)
  size := fun _ => n
  readGrant := fun p => decide (p.allocation = 0 ∧ p.tag = 0)
  writeGrant := fun p => decide (p.allocation = 1 ∧ p.tag = 0)

theorem initial_destination_uninitialized (n i : Nat) (values : Nat → Byte) :
    (initial n values).cells (dstPtr i).loc = .uninit := by
  simp [initial, dstPtr, Ptr.loc]

theorem initial_ready (policy : Policy) (n : Nat) (values : Nat → Byte) :
    Ready (concrete policy) (initial n values) (jobsFrom 0 n values) := by
  intro j hj
  obtain ⟨i, hlo, hi, rfl⟩ := jobsFrom_mem 0 n values j hj
  simp only [Nat.zero_add] at hi
  simp [concrete, CanRead, CanWrite, initial, byteJob, srcPtr, dstPtr, Ptr.loc, hi]

/-- Actual unbounded-length theorem, instantiated by each concrete witness.
    All lengths and all functions Nat → Byte are admitted; no validity premise
    assumes this program's success. Empty copies perform no access. -/
theorem copy_family (policy : Policy) (n : Nat) (values : Nat → Byte) :
    ∃ t, copy (concrete policy) (initial n values) (jobsFrom 0 n values) = .ok t ∧
      (∀ i, i < n → t.cells (dstPtr i).loc = .byte (values i)) ∧
      (∀ i, i < n → t.cells (srcPtr i).loc = .byte (values i)) := by
  obtain ⟨t, ht, done, frame⟩ := copy_safe (concrete policy) (concrete_laws policy)
    (initial n values) (jobsFrom 0 n values) (initial_ready policy n values)
    (jobsFrom_separated 0 n values)
  change Store at t
  have frame' : ∀ l, (∀ j ∈ jobsFrom 0 n values, l ≠ j.dst.loc) →
      t.cells l = (initial n values).cells l := frame
  refine ⟨t, ht, ?_, ?_⟩
  · intro i hi
    exact done (byteJob i (values i))
      (mem_jobsFrom 0 n values i (Nat.zero_le _) (by simpa using hi))
  · intro i hi
    rw [frame' (srcPtr i).loc (by
      intro j hj
      obtain ⟨k, hlo, hhi, rfl⟩ := jobsFrom_mem 0 n values j hj
      simp [byteJob, srcPtr, dstPtr, Ptr.loc])]
    simp [initial, srcPtr, Ptr.loc, hi]

def zeroByte : Byte := ⟨0, by decide⟩
def oneByte : Byte := ⟨1, by decide⟩

/-- Negative controls are failures of the owned toy commands. Relating any
    `Error` to Rust undefined behavior requires a separate adequacy theorem. -/
theorem uninitialized_read_error (policy : Policy) (s : Store) (p : Ptr)
    (authority : CanRead s p) (uninitialized : s.cells p.loc = .uninit) :
    read policy s p = .error .uninitialized := by
  simp [read, authority, uninitialized]

theorem pointer_slot_byte_read_error (policy : Policy) (s : Store) (p q : Ptr)
    (authority : CanRead s p) (symbolic : s.cells p.loc = .pointer q) :
    read policy s p = .error .representation := by
  simp [read, authority, symbolic]

theorem out_of_bounds_error (policy : Policy) (n : Nat) (values : Nat → Byte) :
    read policy (initial n values) (srcPtr n) = .error .bounds := by
  simp [read, CanRead, initial, srcPtr, accessError]

def blankSource : Store :=
  { initial 1 (fun _ => zeroByte) with cells := fun _ => .uninit }

theorem uninitialized_copy_error (policy : Policy) :
    copy (concrete policy) blankSource [byteJob 0 zeroByte] = .error .uninitialized := by
  simp [copy, concrete, read, CanRead, blankSource, initial, byteJob, srcPtr]

theorem missing_write_authority_error (policy : Policy) :
    write policy { initial 1 (fun _ => zeroByte) with writeGrant := fun _ => false }
      (dstPtr 0) oneByte = .error .authority := by
  simp [write, CanWrite, initial, dstPtr, accessError]

theorem dead_allocation_error (policy : Policy) :
    read policy { initial 1 (fun _ => zeroByte) with live := fun _ => false }
      (srcPtr 0) = .error .dead := by
  simp [read, CanRead, initial, srcPtr, accessError]

def owner : Ptr := ⟨0, 0, 0⟩
def sibling : Ptr := ⟨0, 0, 1⟩

def aliasInitial : Store where
  cells := fun _ => .byte zeroByte
  live := fun _ => true
  size := fun _ => 1
  readGrant := fun _ => true
  writeGrant := fun _ => true

def siblingProgram (policy : Policy) : Except Error Store :=
  match read policy aliasInitial sibling with
  | .error e => .error e
  | .ok (_, r) => write policy r owner oneByte

/-- A difference with an observable success/error consequence outside the copy
    protocol. This does not identify either policy with a Rust alias model. -/
theorem policies_distinct :
    (∃ t, siblingProgram .historyFree = .ok t) ∧
    siblingProgram .siblingRevoking = .error .authority := by
  constructor
  · refine ⟨afterWrite .historyFree (afterRead .historyFree aliasInitial sibling) owner oneByte, ?_⟩
    simp [siblingProgram, read, write, CanRead, CanWrite, aliasInitial,
      sibling, owner, afterRead, revoke, Ptr.loc]
  · simp [siblingProgram, read, write, CanRead, CanWrite, aliasInitial,
      sibling, owner, afterRead, revoke, Ptr.loc, accessError]

/- A separate static type/layout and codec example. Two abstract slots contain
   one payload and one padding slot; pointer payloads preserve the entire Ptr,
   including allocation and tag. No byte size is assigned to pointer payloads.
   This codec remains isolated from operational Model/Laws/copy: no theorem
   connects its transfers to command access checks or proves a combined
   representation refinement. It does not complete research-agenda item A1. -/
namespace PaddedCodec

inductive Ty where
  | byte
  | pointer
  deriving DecidableEq, Repr

def Value : Ty → Type
  | .byte => Byte
  | .pointer => Ptr

def payloadSlot : Ty → Bool
  | .byte => false
  | .pointer => true

structure Layout where
  extent : Nat
  payload : Bool
  deriving DecidableEq, Repr

def canonicalLayout (ty : Ty) : Layout := ⟨2, payloadSlot ty⟩

/-- A static coherence obligation, independent of dynamic access authority. -/
def Coherent (ty : Ty) (layout : Layout) : Prop :=
  layout.extent = 2 ∧ layout.payload = payloadSlot ty

abbrev Representation := Bool → Cell

def payloadCell : (ty : Ty) → Value ty → Cell
  | .byte, b => .byte b
  | .pointer, p => .pointer p

def encode (ty : Ty) (value : Value ty) : Representation :=
  fun slot => if slot = payloadSlot ty then payloadCell ty value else .uninit

def decode (ty : Ty) (layout : Layout) (repr : Representation) : Option (Value ty) :=
  if layout.extent = 2 then
    match ty with
    | .byte => match repr layout.payload with
      | .byte b => some b
      | _ => none
    | .pointer => match repr layout.payload with
      | .pointer p => some p
      | _ => none
  else none

structure CodecLaws : Prop where
  roundTrip : ∀ ty layout, Coherent ty layout → ∀ value : Value ty,
    decode ty layout (encode ty value) = some value
  padding : ∀ ty (value : Value ty), encode ty value (!payloadSlot ty) = .uninit

/-- A proved codec law record, rather than a postulated round-trip axiom. -/
theorem codec_laws : CodecLaws where
  roundTrip := by
    intro ty layout coherent value
    rcases coherent with ⟨he, hp⟩
    cases ty <;> simp_all [decode, encode, payloadSlot, payloadCell]
  padding := by
    intro ty value
    cases ty <;> simp [encode, payloadSlot]

theorem canonical_coherent (ty : Ty) : Coherent ty (canonicalLayout ty) := ⟨rfl, rfl⟩

theorem roundTrip (ty : Ty) (layout : Layout) (coherent : Coherent ty layout)
    (value : Value ty) : decode ty layout (encode ty value) = some value :=
  codec_laws.roundTrip ty layout coherent value

theorem padding_uninitialized (ty : Ty) (value : Value ty) :
    encode ty value (!payloadSlot ty) = .uninit := codec_laws.padding ty value

/-- Raw representation copying retains initialization and symbolic provenance. -/
def rawCopy (repr : Representation) : Representation :=
  fun slot => match repr slot with
    | .uninit => .uninit
    | .byte b => .byte b
    | .pointer p => .pointer p

theorem rawCopy_exact (repr : Representation) (slot : Bool) :
    rawCopy repr slot = repr slot := by
  unfold rawCopy
  cases repr slot <;> rfl

/-- Typed transfer decodes a value and encodes it, leaving padding uninitialized. -/
def typedTransfer (ty : Ty) (layout : Layout) (repr : Representation) :
    Option Representation := (decode ty layout repr).map (encode ty)

theorem typedTransfer_encoded (ty : Ty) (layout : Layout) (coherent : Coherent ty layout)
    (value : Value ty) :
    typedTransfer ty layout (encode ty value) = some (encode ty value) := by
  simp [typedTransfer, codec_laws.roundTrip ty layout coherent value]

def paddedByte (b : Byte) (padding : Cell) : Representation :=
  fun slot => if slot = false then .byte b else padding

theorem typed_transfer_discards_padding (b : Byte) (padding : Cell) :
    typedTransfer .byte (canonicalLayout .byte) (paddedByte b padding) =
      some (encode .byte b) := by
  have hd : decode .byte (canonicalLayout .byte) (paddedByte b padding) = some b := by
    rfl
  unfold typedTransfer
  rw [hd]
  rfl

theorem raw_copy_preserves_padding (b : Byte) (padding : Cell) :
    rawCopy (paddedByte b padding) true = padding := by
  rw [rawCopy_exact]
  simp [paddedByte]

theorem pointer_provenance_roundTrip (p : Ptr) :
    decode .pointer (canonicalLayout .pointer) (encode .pointer p) = some p :=
  codec_laws.roundTrip .pointer _ (canonical_coherent _) p

theorem raw_copy_preserves_pointer (p : Ptr) :
    rawCopy (encode .pointer p) true = .pointer p := by
  rw [rawCopy_exact]
  simp [encode, payloadSlot, payloadCell]

/-- Removing type/layout coherence breaks the actual codec law. -/
theorem incoherent_layout_counterexample :
    decode .byte ⟨2, true⟩ (encode .byte zeroByte) = none ∧
    decode .byte ⟨2, true⟩ (encode .byte zeroByte) ≠ some zeroByte := by
  constructor
  · rfl
  · intro h
    change (none : Option Byte) = some zeroByte at h
    cases h

theorem wrong_type_counterexample (b : Byte) :
    decode .pointer (canonicalLayout .pointer) (encode .byte b) = none := by
  rfl

theorem no_unconditional_roundTrip :
    ¬ (∀ layout (value : Value .byte), decode .byte layout (encode .byte value) = some value) := by
  intro h
  have bad := h ⟨2, true⟩ zeroByte
  simp [decode, encode, payloadSlot] at bad

end PaddedCodec

#print axioms copy_safe
#print axioms concrete_laws
#print axioms copy_family
#print axioms laws_consistent
#print axioms both_scoped_witnesses
#print axioms jobsFrom_length
#print axioms jobsFrom_separated
#print axioms initial_ready
#print axioms initial_destination_uninitialized
#print axioms uninitialized_read_error
#print axioms pointer_slot_byte_read_error
#print axioms out_of_bounds_error
#print axioms uninitialized_copy_error
#print axioms missing_write_authority_error
#print axioms dead_allocation_error
#print axioms policies_distinct
#print axioms PaddedCodec.codec_laws
#print axioms PaddedCodec.roundTrip
#print axioms PaddedCodec.padding_uninitialized
#print axioms PaddedCodec.rawCopy_exact
#print axioms PaddedCodec.typedTransfer_encoded
#print axioms PaddedCodec.typed_transfer_discards_padding
#print axioms PaddedCodec.raw_copy_preserves_padding
#print axioms PaddedCodec.pointer_provenance_roundTrip
#print axioms PaddedCodec.raw_copy_preserves_pointer
#print axioms PaddedCodec.incoherent_layout_counterexample
#print axioms PaddedCodec.wrong_type_counterexample
#print axioms PaddedCodec.no_unconditional_roundTrip

end AnnealResearch.Memory
