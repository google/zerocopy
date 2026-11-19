/-!
# `LoanFrame` lifecycle, shared-ring double fetch, and unified per-frame pin

Standalone Lean `v4.34.1` file (core library only; no `sorry`, no `axiom`, no
`native_decide`). Every universally quantified statement about the finite
models below is discharged by kernel evaluation (`decide +kernel`) over the
complete abstract state space, so the proofs are exhaustive rather than
sampled.

Part A models one frame loaned by a client address space `A` to a server
address space `B` for the duration of a `Call`, with page-table entries and
(possibly stale) address-translation-cache entries per address space, and a
`Design` record of seven independent kernel decisions. With all seven enabled
the safety predicate holds in every reachable state; disabling any single one
yields a concrete violating trace.

Part B models a kernel consuming a submission-queue entry from user-shared
memory, where every fetch may observe a different value.

Part C models a single per-frame pin shared by every kernel subsystem that
retains a frame beyond one system call.
-/

namespace LoanRingPin

/-! ## Part A — the `LoanFrame` lifecycle -/

inductive Perm where
  | ro | rw
  deriving DecidableEq, Repr

/-- Contents of the server's dedicated loan-slot virtual page. -/
inductive Slot where
  | empty
  | own                  -- a page of the server's own, mapped by the server
  | loaned (p : Perm)    -- the loaned frame, mapped by the kernel
  deriving DecidableEq, Repr

/-- Abstract kernel state for one frame, one client mapping, one third-party
mapping, one server loan slot, and one `Reply` object. `none` means "no
access". The two `tlb` fields are cached translations *to the loaned frame*;
hardware consults them before the page table. -/
structure LState where
  frameLive : Bool          -- the frame object exists (its memory is not retyped)
  replyLive : Bool          -- the `Reply` object bound by the client's `Call` exists
  loan      : Option Perm   -- loan token, linked from the frame and from the `Reply`
  savedA    : Option Perm   -- client's pre-loan permission, stashed in the token
  pteA      : Option Perm   -- client's leaf page-table entry for the frame
  tlbA      : Option Perm   -- cached translation in the client's ASID
  slot      : Slot          -- server's loan-slot page-table entry
  tlbB      : Option Perm   -- cached translation loan-slot → frame in the server's ASID
  pteC      : Option Perm   -- a mapping of the same frame through a second capability
  deriving DecidableEq, Repr

inductive Ev where
  | loan (p : Perm)     -- client: `Call` carrying `LoanFrame(frame, p)`
  | reply               -- server: reply on the bound `Reply` object
  | revokeFrame         -- frame object deleted (capability revoked, memory about to be retyped)
  | deleteReply         -- `Reply` object destroyed (server deleted, or reply capability dropped)
  | accessA (w : Bool)  -- any thread in the client's address space touches the page
  | accessB (w : Bool)  -- any thread in the server's address space touches the loan slot
  | bUnmapPT            -- server removes the page table that holds the loan slot
  | bMapOwn             -- server maps a page of its own at the loan-slot address
  | bUnmapOwn           -- server unmaps its own page from the loan-slot address
  | aUnmap              -- client unmaps the frame through its capability
  | aMap (p : Perm)     -- client maps the frame through its capability
  | cMap (p : Perm)     -- the frame is mapped through a second capability
  | cUnmap              -- the second capability's mapping is removed
  deriving DecidableEq, Repr

/-- Seven independent kernel decisions. -/
structure Design where
  flushOnLoan   : Bool  -- `sfence.vma` for the client's page after downgrading its entry
  flushOnEnd    : Bool  -- `sfence.vma` for the loan slot after clearing the server's entry
  endOnRevoke   : Bool  -- deleting the frame ends the loan through the token
  endOnReplyDel : Bool  -- destroying the `Reply` ends the loan through the token
  ppnCheck      : Bool  -- loan end clears the loan slot only if it still maps the loaned frame
  uniqueCheck   : Bool  -- a loan starts only if no second mapping of the frame exists
  mapGuard      : Bool  -- mapping a frame is refused while it is loaned

def good : Design := ⟨true, true, true, true, true, true, true⟩

/-- Does a translation with this permission allow a read (`w = false`) or a
write (`w = true`)? -/
def permits : Option Perm → Bool → Bool
  | some .rw, _ => true
  | some .ro, false => true
  | _, _ => false

def slotPerm : Slot → Option Perm
  | .loaned p => some p
  | _ => none

/-- Client-side permission while the frame is loaned with permission `p`: an
exclusive (`rw`) loan removes the client's access, a shared (`ro`) loan leaves
it read-only. -/
def downgrade : Perm → Option Perm → Option Perm
  | .rw, _ => none
  | .ro, some _ => some .ro
  | .ro, none => none

/-- End a loan using only the fields recorded in the token: restore the
client's entry, clear the server's loan slot, flush the server's translation.
No page table is searched. -/
def endLoan (d : Design) (s : LState) : LState :=
  { s with
    loan := none
    savedA := none
    pteA := if s.frameLive then s.savedA else none
    slot := match s.slot with
            | .loaned _ => .empty
            | .own => if d.ppnCheck then .own else .empty
            | .empty => .empty
    tlbB := if d.flushOnEnd then none else s.tlbB }

def step (d : Design) (s : LState) : Ev → LState
  | .loan p =>
    if s.frameLive && s.replyLive && s.loan.isNone && s.slot == .empty
        && (!d.uniqueCheck || s.pteC.isNone) then
      { s with
        loan := some p
        savedA := s.pteA
        pteA := downgrade p s.pteA
        tlbA := if d.flushOnLoan then none else s.tlbA
        slot := .loaned p }
    else s
  | .reply => if s.replyLive && s.loan.isSome then endLoan d s else s
  | .revokeFrame =>
    if s.frameLive then
      let s1 := { s with frameLive := false, pteA := none, tlbA := none, pteC := none,
                         savedA := none }
      if d.endOnRevoke && s.loan.isSome then endLoan d s1 else s1
    else s
  | .deleteReply =>
    if s.replyLive then
      let s1 := if d.endOnReplyDel && s.loan.isSome then endLoan d s else s
      { s1 with replyLive := false }
    else s
  | .accessA w =>
    if !permits s.tlbA w && permits s.pteA w then { s with tlbA := s.pteA } else s
  | .accessB w =>
    if !permits s.tlbB w && permits (slotPerm s.slot) w then { s with tlbB := slotPerm s.slot }
    else s
  | .bUnmapPT => { s with slot := .empty, tlbB := none }
  | .bMapOwn => if s.slot == .empty then { s with slot := .own } else s
  | .bUnmapOwn => if s.slot == .own then { s with slot := .empty } else s
  | .aUnmap => { s with pteA := none, tlbA := none, savedA := none }
  | .aMap p =>
    if s.frameLive && s.pteA.isNone && (!d.mapGuard || s.loan.isNone) then
      { s with pteA := some p }
    else s
  | .cMap p =>
    if s.frameLive && s.pteC.isNone && (!d.mapGuard || s.loan.isNone) then
      { s with pteC := some p }
    else s
  | .cUnmap => { s with pteC := none }

def run (d : Design) (s : LState) (tr : List Ev) : LState := tr.foldl (step d) s

/-- Can the client's address space reach the frame (through a cached or a
fresh translation)? -/
def canA (s : LState) (w : Bool) : Bool := permits s.tlbA w || permits s.pteA w
def canB (s : LState) (w : Bool) : Bool := permits s.tlbB w || permits (slotPerm s.slot) w
def canC (s : LState) (w : Bool) : Bool := permits s.pteC w

/-- The safety predicate.

1. Nobody reaches a deleted frame.
2. The server reaches the frame only under a live loan, and writes only under
   a `rw` loan.
3. While any loan is live, no translation outside the server permits a write
   (the server never observes a concurrent modification: no TOCTOU).
4. While an exclusive loan is live, nothing outside the server reaches the
   frame at all.
5. A live loan has a live `Reply` object and a live frame. -/
def safe (s : LState) : Bool :=
  (s.frameLive || !(canA s false || canB s false || canC s false)) &&
  (!canB s false || s.loan.isSome) && (!canB s true || s.loan == some .rw) &&
  (s.loan.isNone || !(canA s true || canC s true)) &&
  (s.loan != some .rw || !(canA s false || canC s false)) &&
  (s.loan.isNone || (s.replyLive && s.frameLive))

/-- Permission order `none ≤ ro ≤ rw`. -/
def le : Option Perm → Option Perm → Bool
  | none, _ => true
  | some .ro, some _ => true
  | some .rw, some .rw => true
  | _, _ => false

/-- Inductive strengthening of `safe`: cached translations never exceed the
page table, the loan slot maps the frame only under a matching token, the
client's entry is downgraded and no second mapping exists while loaned, and a
deleted frame has no mapping and no token. -/
def inv (s : LState) : Bool :=
  le s.tlbA s.pteA && le s.tlbB (slotPerm s.slot) &&
  (match s.slot with
   | .loaned p => s.loan == some p
   | _ => true) &&
  (match s.loan with
   | none => s.savedA.isNone
   | some .rw => s.pteA.isNone && s.pteC.isNone
   | some .ro => s.pteA != some .rw && s.pteC.isNone) &&
  (s.loan.isNone || le s.pteA s.savedA) &&
  (s.loan.isNone || (s.replyLive && s.frameLive)) &&
  (s.frameLive || (s.pteA.isNone && s.pteC.isNone && s.loan.isNone))

/-- Initial state: the client has the frame mapped read-write; nothing else. -/
def init : LState :=
  { frameLive := true, replyLive := true, loan := none, savedA := none, pteA := some .rw,
    tlbA := none, slot := .empty, tlbB := none, pteC := none }

/-! ### Exhaustive enumeration support -/

instance decForallPerm (p : Perm → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .ro ∧ p .rw)
    ⟨fun h x => by cases x <;> simp [h.1, h.2], fun h => ⟨h _, h _⟩⟩

instance decForallOptPerm (p : Option Perm → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p none ∧ p (some .ro) ∧ p (some .rw))
    ⟨fun h x => by
        cases x with
        | none => exact h.1
        | some v => cases v
                    · exact h.2.1
                    · exact h.2.2,
     fun h => ⟨h _, h _, h _⟩⟩

instance decForallSlot (p : Slot → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .empty ∧ p .own ∧ p (.loaned .ro) ∧ p (.loaned .rw))
    ⟨fun h x => by
        cases x with
        | empty => exact h.1
        | own => exact h.2.1
        | loaned v => cases v
                      · exact h.2.2.1
                      · exact h.2.2.2,
     fun h => ⟨h _, h _, h _, h _⟩⟩

instance decForallEv (p : Ev → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff
    ((∀ q, p (.loan q)) ∧ p .reply ∧ p .revokeFrame ∧ p .deleteReply ∧ (∀ w, p (.accessA w)) ∧
     (∀ w, p (.accessB w)) ∧ p .bUnmapPT ∧ p .bMapOwn ∧ p .bUnmapOwn ∧ p .aUnmap ∧
     (∀ q, p (.aMap q)) ∧ (∀ q, p (.cMap q)) ∧ p .cUnmap)
    ⟨fun h x => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
        cases x with
        | loan q => exact h1 q
        | reply => exact h2
        | revokeFrame => exact h3
        | deleteReply => exact h4
        | accessA w => exact h5 w
        | accessB w => exact h6 w
        | bUnmapPT => exact h7
        | bMapOwn => exact h8
        | bUnmapOwn => exact h9
        | aUnmap => exact h10
        | aMap q => exact h11 q
        | cMap q => exact h12 q
        | cUnmap => exact h13,
     fun h => ⟨fun _ => h _, h _, h _, h _, fun _ => h _, fun _ => h _, h _, h _, h _, h _,
               fun _ => h _, fun _ => h _, h _⟩⟩

/-! ### The good design is safe in every reachable state -/

theorem inv_init : inv init = true := by decide

/-- `inv` is preserved by every event from every abstract state (11,664
states × 18 events, checked exhaustively by the kernel). -/
theorem inv_step_fields :
    ∀ (fl rl : Bool) (loan savedA pteA tlbA : Option Perm) (slot : Slot)
      (tlbB pteC : Option Perm) (e : Ev),
      inv ⟨fl, rl, loan, savedA, pteA, tlbA, slot, tlbB, pteC⟩ = true →
      inv (step good ⟨fl, rl, loan, savedA, pteA, tlbA, slot, tlbB, pteC⟩ e) = true := by
  decide +kernel

theorem inv_step (s : LState) (e : Ev) (h : inv s = true) : inv (step good s e) = true := by
  cases s
  exact inv_step_fields _ _ _ _ _ _ _ _ _ e h

/-- `inv` implies `safe` in every abstract state. -/
theorem inv_safe_fields :
    ∀ (fl rl : Bool) (loan savedA pteA tlbA : Option Perm) (slot : Slot)
      (tlbB pteC : Option Perm),
      inv ⟨fl, rl, loan, savedA, pteA, tlbA, slot, tlbB, pteC⟩ = true →
      safe ⟨fl, rl, loan, savedA, pteA, tlbA, slot, tlbB, pteC⟩ = true := by
  decide +kernel

theorem inv_safe (s : LState) (h : inv s = true) : safe s = true := by
  cases s
  exact inv_safe_fields _ _ _ _ _ _ _ _ _ h

theorem inv_run (tr : List Ev) : ∀ s, inv s = true → inv (run good s tr) = true := by
  induction tr with
  | nil => intro s h; exact h
  | cons e tr ih => intro s h; exact ih (step good s e) (inv_step s e h)

/-- **Safety of the good design.** After any finite sequence of client,
server, third-party, and revocation events, the safety predicate holds. -/
theorem good_design_safe (tr : List Ev) : safe (run good init tr) = true :=
  inv_safe _ (inv_run tr init inv_init)

/-- Kernel-initiated loan teardown never removes a page the server mapped
itself at the loan-slot address. -/
theorem no_collateral_unmap :
    ∀ (fl rl : Bool) (loan savedA pteA tlbA tlbB pteC : Option Perm),
      (step good ⟨fl, rl, loan, savedA, pteA, tlbA, .own, tlbB, pteC⟩ .reply).slot = .own ∧
      (step good ⟨fl, rl, loan, savedA, pteA, tlbA, .own, tlbB, pteC⟩ .revokeFrame).slot = .own ∧
      (step good ⟨fl, rl, loan, savedA, pteA, tlbA, .own, tlbB, pteC⟩ .deleteReply).slot = .own := by
  decide +kernel

/-- After a loan ends by reply, the client's original mapping is back. -/
theorem reply_restores_owner (p : Perm) :
    (run good init [.loan p, .accessB false, .reply]).pteA = some .rw ∧
    (run good init [.loan p, .accessB false, .reply]).loan = none ∧
    (run good init [.loan p, .accessB false, .reply]).slot = .empty := by
  cases p <;> decide

/-! ### Each of the seven decisions is necessary -/

/-- Without the client-side `sfence.vma`, a translation cached before the loan
still permits a client write during an exclusive loan. -/
theorem need_flushOnLoan :
    safe (run { good with flushOnLoan := false } init [.accessA true, .loan .rw]) = false := by
  decide

/-- Without the server-side `sfence.vma`, the server still reaches the frame
after the reply. -/
theorem need_flushOnEnd :
    safe (run { good with flushOnEnd := false } init [.loan .rw, .accessB true, .reply])
      = false := by
  decide

/-- If deleting the frame does not end the loan, the server keeps a mapping of
memory that is about to be retyped. -/
theorem need_endOnRevoke :
    safe (run { good with endOnRevoke := false } init [.loan .rw, .revokeFrame]) = false := by
  decide

/-- If destroying the `Reply` does not end the loan, the loan outlives the only
object that could end it. -/
theorem need_endOnReplyDel :
    safe (run { good with endOnReplyDel := false } init [.loan .rw, .deleteReply]) = false := by
  decide

/-- Without the target check, loan teardown unmaps a page the server mapped
itself after discarding the loan mapping. -/
theorem need_ppnCheck :
    (run { good with ppnCheck := false } init [.loan .rw, .bUnmapPT, .bMapOwn, .reply]).slot
      = .empty ∧
    (run good init [.loan .rw, .bUnmapPT, .bMapOwn, .reply]).slot = .own := by
  decide

/-- If a second mapping may exist when the loan starts, it permits writes
during the loan. -/
theorem need_uniqueCheck :
    safe (run { good with uniqueCheck := false } init [.cMap .rw, .loan .rw]) = false := by
  decide

/-- If mapping is not refused while loaned, a second capability re-creates a
writable mapping during the loan. -/
theorem need_mapGuard :
    safe (run { good with mapGuard := false } init [.loan .rw, .cMap .rw]) = false := by
  decide

/-! ## Part B — fetching from user-shared memory -/

/-- A submission-queue entry: an operation code and a byte range inside a
registered buffer. -/
structure SqEntry where
  op  : Nat
  off : Nat
  len : Nat

/-- User-shared memory as seen by the kernel: the `i`-th fetch of the same
entry returns `sh i`, and nothing relates distinct fetches. -/
abbrev Shared := Nat → SqEntry

def entryValid (regionLen : Nat) (e : SqEntry) : Bool := decide (e.off + e.len ≤ regionLen)

/-- Validates one fetch and acts on a second fetch. -/
def consumeDoubleFetch (regionLen : Nat) (sh : Shared) : Option (Nat × Nat) :=
  if entryValid regionLen (sh 0) = true then some ((sh 1).off, (sh 1).len) else none

/-- Fetches once into a kernel-private value, then validates and acts on it. -/
def consumeCopyOnce (regionLen : Nat) (sh : Shared) : Option (Nat × Nat) :=
  let e := sh 0
  if entryValid regionLen e = true then some (e.off, e.len) else none

/-- Copy-once: whatever user space does to the shared entry, the range the
kernel acts on is the range it validated. -/
theorem copyOnce_in_bounds (regionLen : Nat) (sh : Shared) (off len : Nat)
    (h : consumeCopyOnce regionLen sh = some (off, len)) : off + len ≤ regionLen := by
  unfold consumeCopyOnce at h
  by_cases hv : entryValid regionLen (sh 0) = true
  · simp only [hv, if_true] at h
    have h1 : (sh 0).off = off := congrArg Prod.fst (Option.some.inj h)
    have h2 : (sh 0).len = len := congrArg Prod.snd (Option.some.inj h)
    have h3 : (sh 0).off + (sh 0).len ≤ regionLen := by
      simpa [entryValid] using hv
    omega
  · simp [hv] at h

/-- Double fetch: user space rewrites the entry between the two fetches and
the kernel acts on a range it never validated. -/
theorem doubleFetch_out_of_bounds :
    ∃ (sh : Shared) (off len : Nat),
      consumeDoubleFetch 4096 sh = some (off, len) ∧ 4096 < off + len :=
  ⟨fun i => if i = 0 then ⟨0, 0, 16⟩ else ⟨0, 0, 1048576⟩, 0, 1048576, by decide, by decide⟩

/-- Number of submissions consumed in one batch, computed from **one** fetch
of the user-written tail index and the kernel-private head index (both 32-bit,
wrapping), clamped to the ring size. -/
def batchLen (size headPriv tail : Nat) : Nat :=
  min ((tail % 4294967296 + 4294967296 - headPriv % 4294967296) % 4294967296) size

/-- Ring slot of the `i`-th submission of a batch. -/
def slotIdx (size headPriv i : Nat) : Nat := (headPriv + i) % size

/-- For every tail value user space can write, a batch is at most one ring
long and every slot it touches lies inside the ring. -/
theorem batch_bounded (size headPriv tail : Nat) (hs : 0 < size) :
    batchLen size headPriv tail ≤ size ∧ ∀ i, slotIdx size headPriv i < size :=
  ⟨Nat.min_le_right _ _, fun _ => Nat.mod_lt _ hs⟩

/-! ## Part C — one pin per frame for every long-lived kernel reference -/

/-- Kernel subsystems that keep a reference to a frame across system calls. -/
inductive Holder where
  | loan        -- a `LoanFrame` in progress (released by reply)
  | ring        -- backing memory of an asynchronous ring
  | modCode     -- executable slot of a loaded kernel module
  | modScratch  -- scratch region of a loaded kernel module
  deriving DecidableEq, Repr

/-- `pin` is the single authoritative per-frame field; each `ref*` is the
corresponding holder object's reference back to the frame. -/
structure PState where
  frameLive  : Bool
  pin        : Option Holder
  refLoan    : Bool
  refRing    : Bool
  refCode    : Bool
  refScratch : Bool
  deriving DecidableEq, Repr

def PState.ref (s : PState) : Holder → Bool
  | .loan => s.refLoan
  | .ring => s.refRing
  | .modCode => s.refCode
  | .modScratch => s.refScratch

def PState.setRef (s : PState) (h : Holder) (b : Bool) : PState :=
  match h with
  | .loan => { s with refLoan := b }
  | .ring => { s with refRing := b }
  | .modCode => { s with refCode := b }
  | .modScratch => { s with refScratch := b }

inductive PEv where
  | pin (h : Holder)       -- a subsystem takes the frame
  | release (h : Holder)   -- holder-side end: reply, ring destroyed, module unloaded
  | revoke                 -- frame-side end: the frame object is deleted
  deriving DecidableEq, Repr

/-- `notify = true`: deleting a pinned frame first detaches the holder named
by the pin. `notify = false`: deletion ignores the pin. -/
def pstep (notify : Bool) (s : PState) : PEv → PState
  | .pin h =>
    if s.frameLive && s.pin.isNone && !s.ref h then { s.setRef h true with pin := some h } else s
  | .release h =>
    if s.ref h then
      let s1 := s.setRef h false
      if s.pin == some h then { s1 with pin := none } else s1
    else s
  | .revoke =>
    if s.frameLive then
      match s.pin with
      | some h => if notify then { (s.setRef h false) with pin := none, frameLive := false }
                  else { s with frameLive := false }
      | none => { s with frameLive := false }
    else s

def prun (notify : Bool) (s : PState) (tr : List PEv) : PState := tr.foldl (pstep notify) s

/-- A holder that still believes it references the frame is the unique pin
holder of a live frame: the kernel never follows a holder's reference into
deleted (retyped) memory, and two subsystems never share a frame. -/
def psafe (s : PState) : Bool :=
  (!s.refLoan || (s.frameLive && s.pin == some .loan)) &&
  (!s.refRing || (s.frameLive && s.pin == some .ring)) &&
  (!s.refCode || (s.frameLive && s.pin == some .modCode)) &&
  (!s.refScratch || (s.frameLive && s.pin == some .modScratch)) &&
  (s.frameLive || s.pin.isNone)

def pinit : PState := ⟨true, none, false, false, false, false⟩

instance decForallHolder (p : Holder → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .loan ∧ p .ring ∧ p .modCode ∧ p .modScratch)
    ⟨fun h x => by
        cases x
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2,
     fun h => ⟨h _, h _, h _, h _⟩⟩

instance decForallOptHolder (p : Option Holder → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p none ∧ ∀ h, p (some h))
    ⟨fun h x => by
        cases x with
        | none => exact h.1
        | some v => exact h.2 v,
     fun h => ⟨h _, fun _ => h _⟩⟩

instance decForallPEv (p : PEv → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff ((∀ h, p (.pin h)) ∧ (∀ h, p (.release h)) ∧ p .revoke)
    ⟨fun h x => by
        cases x with
        | pin v => exact h.1 v
        | release v => exact h.2.1 v
        | revoke => exact h.2.2,
     fun h => ⟨fun _ => h _, fun _ => h _, h _⟩⟩

theorem psafe_step_fields :
    ∀ (fl : Bool) (pin : Option Holder) (a b c d : Bool) (e : PEv),
      psafe ⟨fl, pin, a, b, c, d⟩ = true →
      psafe (pstep true ⟨fl, pin, a, b, c, d⟩ e) = true := by
  decide +kernel

theorem psafe_step (s : PState) (e : PEv) (h : psafe s = true) :
    psafe (pstep true s e) = true := by
  cases s
  exact psafe_step_fields _ _ _ _ _ _ e h

/-- **One pin suffices.** With revocation routed through the pin, every
reachable state is safe for all four kinds of holder at once. -/
theorem pin_safe (tr : List PEv) : psafe (prun true pinit tr) = true := by
  have key : ∀ (tr : List PEv) (s : PState), psafe s = true → psafe (prun true s tr) = true := by
    intro tr
    induction tr with
    | nil => intro s h; exact h
    | cons e tr ih => intro s h; exact ih (pstep true s e) (psafe_step s e h)
  exact key tr pinit (by decide)

/-- If deleting a frame ignores the pin, a ring (or a loaded module) keeps a
reference into deleted memory. -/
theorem need_revoke_notification :
    psafe (prun false pinit [.pin .ring, .revoke]) = false ∧
    psafe (prun false pinit [.pin .modCode, .revoke]) = false := by
  decide

end LoanRingPin
