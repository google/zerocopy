import DoubleFetch.Basic

/-!
# Specs and parsers

Specs are pure functions of a byte vector. Parsers are decision trees (`Prog`). Instances:

* a length-prefixed record header (`lpParse`), checked against a copy buffer of capacity `cap`;
* a byte that later code reinterprets as a `bool` (`boolParse`);
* a two-field record with a checksum computed by addition modulo 256 (`ckParse`);
* a two-byte pair (`pairSpec`), the simplest value spanning two addresses;
* a seqlock-style versioned record (`seqSpec`);
* a tagged value whose payload must be a valid `bool` when the tag is `1` (`ValidE`, `viewSpec`).
-/

namespace Toy.DoubleFetch

section Generic

variable {n : Nat} {α : Type}

/-- Parse an atomic snapshot: copy the whole region in one access, then apply `spec`. -/
def snapParse (spec : Region n → α) : Prog n α := .snap fun s => .ret (spec s)

/-- Read the addresses in `l` one byte at a time, in order, storing each byte into the accumulator
`acc`; then continue with `k` applied to the filled accumulator. -/
def readSeq : List (Fin n) → Region n → (Region n → Prog n α) → Prog n α
  | [], acc, k => k acc
  | i :: is, acc, k => .read i fun b => readSeq is (fun j => if j = i then b else acc j) k

/-- Byte-by-byte copy: read addresses `0, 1, …, n-1` in that order (address `j` at time `j`),
then continue with the copied region. -/
def byteCopy (k : Region n → Prog n α) : Prog n α := readSeq (List.finRange n) (fun _ => 0) k

/-- Parse a byte-by-byte copy: copy one byte at a time, then apply `spec` to the copy. -/
def copyParse (spec : Region n → α) : Prog n α := byteCopy fun s => .ret (spec s)

/-- A check-then-use fragment: load the byte at `addr` into a local, test it with `check`; on
success run `use` on the local, otherwise run `onFail`. -/
structure CheckUse (n : Nat) (α : Type) where
  addr : Fin n
  check : Byte → Bool
  use : Byte → Prog n α
  onFail : Prog n α

/-- The check-then-use fragment as written: one read; the check and the later use both see the same
local. -/
def CheckUse.compile (c : CheckUse n α) : Prog n α :=
  .read c.addr fun b => if c.check b then c.use b else c.onFail

/-- Read rematerialization of the later use: the use no longer sees the local but a fresh read of
the same address, taken after the check. -/
def CheckUse.remat (c : CheckUse n α) : Prog n α :=
  .read c.addr fun b => if c.check b then .read c.addr c.use else c.onFail

/-- A check-then-use fragment whose use and failure continuation perform no further reads: on
success it returns `u b`, otherwise `e`. -/
def CheckUse.pure (addr : Fin n) (check : Byte → Bool) (u : Byte → α) (e : α) : CheckUse n α :=
  { addr := addr, check := check, use := fun b => .ret (u b), onFail := .ret e }

/-- Re-read with a fallback on a one-byte region: read the byte twice; if the two reads agree,
return `spec` of that byte, otherwise return `spec` of the zero byte. -/
def rereadFallback (spec : Region 1 → α) : Prog 1 α :=
  .read 0 fun b => .read 0 fun b' =>
    .ret (if b = b' then spec (fun _ => b) else spec (fun _ => 0))

end Generic

/-! ## Length-prefixed record header -/

/-- Spec of a length-prefixed record header: the length byte at address `0` is accepted iff it is
at most the buffer capacity `cap`, and the result is the length to copy. (The toy models the
destination bound `len ≤ cap`; the source-side bound, that `len` payload bytes are present, is
not modelled.) -/
def lpParse (cap : Nat) {m : Nat} (s : Region (m + 1)) : Option Nat :=
  if (s 0).val ≤ cap then some (s 0).val else none

/-- The action "copy `len` bytes into a buffer of capacity `cap`" is in bounds; an error result
performs no copy and is in bounds. -/
def CopyInBounds (cap : Nat) : Option Nat → Prop
  | some len => len ≤ cap
  | none => True

/-- The length check as a check-then-use fragment on an `(m+1)`-byte region: load the length byte,
check `len ≤ cap`, then copy `len` bytes. -/
def lenCheck (m cap : Nat) : CheckUse (m + 1) (Option Nat) :=
  CheckUse.pure 0 (fun b => decide (b.val ≤ cap)) (fun b => some b.val) none

/-- Single-read length parser: read the length once, check it, copy that same length. -/
def lenOnce (m cap : Nat) : Prog (m + 1) (Option Nat) := (lenCheck m cap).compile

/-- Double-fetch length parser: read the length, check it, then read the length again and copy
the re-read length. It is exactly the read rematerialization of `lenOnce`. -/
def lenReread (m cap : Nat) : Prog (m + 1) (Option Nat) := (lenCheck m cap).remat

/-- The writer that shows the length `cap` at time `0` and the length `cap + 1` at every later time
(both reduced modulo 256; for `cap < 255` no reduction happens). -/
def lenFlipAdv (m cap : Nat) : Adversary (m + 1) :=
  fun t _ => if t = 0 then Fin.ofNat 256 cap else Fin.ofNat 256 (cap + 1)

/-! ## A byte reinterpreted as `bool` -/

/-- Spec of a `bool` stored as one byte at address `0`: valid iff the byte is `0` or `1`. The
result is the validated byte, which later code reinterprets as a `bool` without checking. -/
def boolParse {m : Nat} (s : Region (m + 1)) : Option Byte :=
  if (s 0).val ≤ 1 then some (s 0) else none

/-- The result, if any, is a valid `bool` representation (`0` or `1`). -/
def ValidBoolOut : Option Byte → Prop
  | some b => b.val ≤ 1
  | none => True

/-- The tag check as a check-then-use fragment: validate that the byte is `0` or `1`, then hand the
byte on as a `bool`. -/
def tagCheck (m : Nat) : CheckUse (m + 1) (Option Byte) :=
  CheckUse.pure 0 (fun b => decide (b.val ≤ 1)) (fun b => some b) none

/-- Single-read `bool` parser. -/
def tagOnce (m : Nat) : Prog (m + 1) (Option Byte) := (tagCheck m).compile

/-- Double-fetch `bool` parser: validate the byte, then re-read it and hand on the re-read byte as
a `bool`. -/
def tagReread (m : Nat) : Prog (m + 1) (Option Byte) := (tagCheck m).remat

/-- The writer that shows the byte `1` at time `0` and the byte `2` at every later time. -/
def tagFlipAdv (m : Nat) : Adversary (m + 1) := fun t _ => if t = 0 then 1 else 2

/-- Re-read and compare on a one-byte region: read the byte twice; if the two reads differ, return
the error result, otherwise decode the byte as a `bool`. -/
def rereadCompare : Prog 1 (Option Byte) :=
  .read 0 fun b => .read 0 fun b' =>
    .ret (if b = b' then boolParse (m := 0) (fun _ => b) else none)

/-- A parser whose second address depends on the first byte read: read address `0`; if it holds
`0`, read and return address `1`, otherwise read and return address `2`. -/
def dataDepProg : Prog 3 Byte :=
  .read 0 fun b => if b.val = 0 then .read 1 .ret else .read 2 .ret

/-! ## Two-byte values and checksums -/

/-- The pair of bytes at addresses `0` and `1`. -/
def pairSpec (s : Region 2) : Byte × Byte := (s 0, s 1)

/-- Two-field record with a checksum: fields at addresses `0` and `1`, checksum at address `2`,
accepted iff the checksum equals the sum of the fields modulo 256 (wrapping `Fin 256`
addition). -/
def ckParse (s : Region 3) : Option (Byte × Byte) :=
  if s 2 = s 0 + s 1 then some (s 0, s 1) else none

/-- A writer going from `(0,0)` to `(1,1)` between times `0` and `1`. -/
def pairTornAdv : Adversary 2 := fun t => if t = 0 then reg2 0 0 else reg2 1 1

/-- A writer whose every state passes the checksum: `(0,0,0)` at time `0`, `(1,1,2)` at time `1`,
and `(2,255,1)` from time `2` on (`2 + 255 = 1` modulo 256). -/
def ckTornAdv : Adversary 3 :=
  fun t => if t = 0 then reg3 0 0 0 else if t = 1 then reg3 1 1 2 else reg3 2 255 1

/-- No single byte value determines the spec's output: for every address `i`, byte `v` and
candidate output `r`, some region with `v` at address `i` has a different output. -/
def NoByteDeterminesOutput {n : Nat} {α : Type} (spec : Region n → α) : Prop :=
  ∀ (i : Fin n) (v : Byte) (r : α), ∃ σ : Region n, σ i = v ∧ spec σ ≠ r

/-- Some region state `s0` has no byte that determines the spec's output, and the spec is not
constant: for every candidate output `r` some region has a different output, and for every
address `i` and candidate output `r` some region that agrees with `s0` at `i` has a different
output. -/
def HasUndeterminedState {n : Nat} {α : Type} (spec : Region n → α) : Prop :=
  ∃ s0 : Region n, (∀ r : α, ∃ σ : Region n, spec σ ≠ r) ∧
    ∀ (i : Fin n) (r : α), ∃ σ : Region n, σ i = s0 i ∧ spec σ ≠ r

/-- Two-byte boolean AND: `true` iff both bytes are `1`. -/
def andSpec (s : Region 2) : Bool := decide (s 0 = 1) && decide (s 1 = 1)

/-- A writer with one checksum-passing state `(0,0,0)` at time `0` and one failing state
`(1,1,1)` at every later time. -/
def ckMixAdv : Adversary 3 := fun t => if t = 0 then reg3 0 0 0 else reg3 1 1 1

/-! ## Seqlock-style version check -/

/-- A versioned record: version byte at address `0`, data at addresses `1` and `2`. An odd
version means "write in progress" (error result); an even version yields the data. -/
def seqSpec (s : Region 3) : Option (Byte × Byte) :=
  if (s 0).val % 2 = 0 then some (s 1, s 2) else none

/-- Seqlock-style reader: read the version; if odd, fail; otherwise read the data, read the version
again, and return the data iff both version reads agree. -/
def seqlockReader : Prog 3 (Option (Byte × Byte)) :=
  .read 0 fun v1 =>
    if v1.val % 2 = 0 then
      .read 1 fun d1 => .read 2 fun d2 => .read 0 fun v2 =>
        .ret (if v2 = v1 then some (d1, d2) else none)
    else .ret none

/-- One step of the version protocol (version increments are modulo 256): no change; begin a
write (even version to version + 1, data unchanged); change data while the version is odd; or end
a write (odd version to version + 1, data unchanged). -/
def VersionStep (s s' : Region 3) : Prop :=
  s' = s ∨
  ((s 0).val % 2 = 0 ∧ s' 0 = s 0 + 1 ∧ s' 1 = s 1 ∧ s' 2 = s 2) ∨
  ((s 0).val % 2 = 1 ∧ s' 0 = s 0) ∨
  ((s 0).val % 2 = 1 ∧ s' 0 = s 0 + 1 ∧ s' 1 = s 1 ∧ s' 2 = s 2)

/-- A writer that follows the version protocol and takes at most one protocol step between
consecutive memory accesses of the reader. -/
def OneStepVersionWriter (adv : Adversary 3) : Prop := ∀ t, VersionStep (adv t) (adv (t + 1))

/-- A writer that follows the version protocol and takes at most two protocol steps between
consecutive memory accesses of the reader. -/
def TwoStepVersionWriter (adv : Adversary 3) : Prop :=
  ∀ t, ∃ mid : Region 3, VersionStep (adv t) mid ∧ VersionStep mid (adv (t + 1))

/-- `VersionPath c s s'`: a finite sequence of protocol steps leads from `s` to `s'`, and exactly
`c` of these steps increment the version (modulo 256); the others leave it unchanged. -/
inductive VersionPath : Nat → Region 3 → Region 3 → Prop
  | refl (s : Region 3) : VersionPath 0 s s
  | stay {c : Nat} {s s' s'' : Region 3} :
      VersionStep s s' → s' 0 = s 0 → VersionPath c s' s'' → VersionPath c s s''
  | bump {c : Nat} {s s' s'' : Region 3} :
      VersionStep s s' → s' 0 = s 0 + 1 → VersionPath c s' s'' → VersionPath (c + 1) s s''

/-- A writer that follows the version protocol, with any number of protocol steps between
consecutive reader accesses, and increments the version fewer than `B` times in total from time
`0` (the reader's first access) to time `3` (its last possible access). -/
def IncrementBoundedWriter (B : Nat) (adv : Adversary 3) : Prop :=
  ∃ c0 c1 c2 : Nat, VersionPath c0 (adv 0) (adv 1) ∧ VersionPath c1 (adv 1) (adv 2) ∧
    VersionPath c2 (adv 2) (adv 3) ∧ c0 + c1 + c2 < B

/-- A writer that changes the data while the version stays `0` (it ignores the protocol). -/
def seqRogueAdv : Adversary 3 := fun t => reg3 0 (Fin.ofNat 256 t) (Fin.ofNat 256 t)

/-- A protocol writer that completes a whole write without changing the data (version `0` to
`1` to `2`) between the reader's first and second accesses: two protocol steps, no wraparound. -/
def seqTwoStepAdv : Adversary 3 := fun t => if t = 0 then reg3 0 0 0 else reg3 2 0 0

/-- A protocol writer that shows `(0,0,0)` at times `0` and `1` and `(0,1,1)` from time `2` on.
Between time `1` (the reader's read of the first data byte) and time `2` (its read of the second
data byte) it takes 257 protocol steps: it begins a write (version `0` to `1`), changes the data
from `(0,0)` to `(1,1)` under the odd version, and then increments the version 255 more times
until it wraps back to `0` (256 version increments and one data change in total). -/
def seqWrapAdv : Adversary 3 := fun t => if t < 2 then reg3 0 0 0 else reg3 0 1 1

/-! ## Validated typed views -/

/-- Validity of a tagged value laid out as (tag, payload): tag `0` (no payload; the payload byte is
ignored), or tag `1` with a payload that is a valid `bool` (`0` or `1`). -/
def ValidE (tag payload : Byte) : Prop := tag.val = 0 ∨ (tag.val = 1 ∧ payload.val ≤ 1)

instance (tag payload : Byte) : Decidable (ValidE tag payload) := by
  unfold ValidE; infer_instance

/-- Every decode in the result list is a valid tagged value. -/
def ViewOK : Option (List (Byte × Byte)) → Prop
  | some l => ∀ x ∈ l, ValidE x.1 x.2
  | none => True

/-- `k` further decodes through a view of the region: each re-reads tag and payload and records
them without re-validating (the view's type promises validity). The list is in reverse order. -/
def viewUses : Nat → List (Byte × Byte) → Prog 2 (Option (List (Byte × Byte)))
  | 0, acc => .ret (some acc)
  | k + 1, acc => .read 0 fun t => .read 1 fun p => viewUses k ((t, p) :: acc)

/-- Validate once, then hand out a view used for `k` later decodes. -/
def viewProg (k : Nat) : Prog 2 (Option (List (Byte × Byte))) :=
  .read 0 fun t => .read 1 fun p => if ValidE t p then viewUses k [] else .ret none

/-- Spec of the decodes served after validating a tagged value: `k` copies of (tag, payload) if
the value is valid, otherwise the error result. -/
def viewSpec (k : Nat) (s : Region 2) : Option (List (Byte × Byte)) :=
  if ValidE (s 0) (s 1) then some (List.replicate k (s 0, s 1)) else none

/-- Copy out, one byte at a time: copy tag and payload into private memory (address `0` at time
`0`, address `1` at time `1`; this is not an atomic snapshot), then validate the private copy and
serve all `k` later decodes from it. -/
def copyOutProg (k : Nat) : Prog 2 (Option (List (Byte × Byte))) := copyParse (viewSpec k)

/-- Single-read decoding into an owned value, validating while it reads: read the tag; if it is
neither `0` nor `1`, return the error result without reading the payload; otherwise read the
payload once, validate, and serve all `k` later decodes from the owned value. Unlike
`copyOutProg`, which reads both bytes before validating, which addresses it reads depends on the
tag. -/
def ownedProg (k : Nat) : Prog 2 (Option (List (Byte × Byte))) :=
  .read 0 fun t =>
    if 1 < t.val then .ret none
    else .read 1 fun p => if ValidE t p then .ret (some (List.replicate k (t, p))) else .ret none

/-- Tag flip after validation: `(0, 2)` (tag `0`, valid) at times `0` and `1`, then `(1, 2)` (tag
`1` with payload `2`, not a valid `bool`). -/
def viewFlipAdv : Adversary 2 := fun t => if t < 2 then reg2 0 2 else reg2 1 2

/-- A writer showing `(0, 2)` (tag `0`, valid) at time `0` and `(1, 1)` (tag `1` with payload
`1`, valid) at every later time. -/
def copyTornAdv : Adversary 2 := fun t => if t = 0 then reg2 0 2 else reg2 1 1

/-- A writer whose every state is a valid tagged value: `(1, 1)` (tag `1`, payload `1`) at times
`0`, `1` and `2`, then `(0, 2)` (tag `0`) from time `3` on; it switches once, atomically, between
two valid states. -/
def validSwitchAdv : Adversary 2 := fun t => if t < 3 then reg2 1 1 else reg2 0 2

end Toy.DoubleFetch
