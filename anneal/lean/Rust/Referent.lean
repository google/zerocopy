/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Rust.Storage
@[expose] public section

/-!
A referent state admits a domain of byte lists at an explicit width. `safe`
requires an admitted value; `initialized` requires only initialized bytes; and
`uninit` places no restriction on byte contents. Width remains a requirement in
all three states. These are pure facts about numeric bytes. A consumer must
separately justify any Rust memory, ownership, or pointer interpretation.

`Transfer` describes a directional inclusion of domains when widths agree. A
width mismatch makes that implication vacuous, so composition needs evidence
that the intermediate width agrees. `Safe` supplies a reusable domain from a
storage decoder and a mathematical decoder; neither must choose an encoding.
-/

namespace Rust.Referent

open Rust.Storage

/-- The byte-content promise attached to a referent. -/
inductive State where
  | uninit
  | initialized
  | safe
  deriving DecidableEq, Repr

/-- Both decoding stages must succeed on this particular representation.
The witnesses need not describe a canonical representation or an inhabited type. -/
def Safe [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (decodeModel : Raw → Option Model) (metadata : Metadata) (bytes : List AMByte) : Prop :=
  ∃ raw value, decoder.run metadata bytes = some raw ∧ decodeModel raw = some value

theorem safe_iff_runWith [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (decodeModel : Raw → Option Model) (metadata : Metadata) (bytes : List AMByte) :
    Safe decoder decodeModel metadata bytes ↔
      ∃ value, decoder.runWith decodeModel metadata bytes = some value := by
  simp only [StorageDecoder.runWith_eq_some_iff, Safe]
  constructor
  · rintro ⟨raw, value, language, model⟩
    exact ⟨value, raw, language, model⟩
  · rintro ⟨value, raw, language, model⟩
    exact ⟨raw, value, language, model⟩

theorem safe_length [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (decodeModel : Raw → Option Model) (metadata : Metadata) (bytes : List AMByte)
    (admitted : Safe decoder decodeModel metadata bytes) :
    bytes.length = decoder.byteSize metadata := by
  obtain ⟨raw, _, language, _⟩ := admitted
  exact decoder.run_length metadata bytes raw language

theorem safe_initialized [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (decodeModel : Raw → Option Model) (initialized : decoder.Initialized)
    (metadata : Metadata) (bytes : List AMByte)
    (admitted : Safe decoder decodeModel metadata bytes) : Initialized bytes := by
  obtain ⟨raw, _, language, _⟩ := admitted
  exact initialized metadata bytes raw language

/-- A state always describes exactly the requested number of bytes.
In particular, `uninit` permits initialized bytes as well as uninitialized bytes. -/
def Allowed (width : Nat) (safe : List AMByte → Prop) (state : State)
    (bytes : List AMByte) : Prop :=
  bytes.length = width ∧ match state with
    | .uninit => True
    | .initialized => Initialized bytes
    | .safe => safe bytes

/-- Transfer retains the bytes and changes only the promise they satisfy.
The width guard is conditional: this relation does not itself prove equal sizes. -/
def Transfer (sourceWidth : Nat) (sourceSafe : List AMByte → Prop) (sourceState : State)
    (destinationWidth : Nat) (destinationSafe : List AMByte → Prop)
    (destinationState : State) : Prop :=
  sourceWidth = destinationWidth → ∀ bytes,
    Allowed sourceWidth sourceSafe sourceState bytes →
    Allowed destinationWidth destinationSafe destinationState bytes

/-- A language decoder that requires initialization lets safe bytes be read as
initialized bytes. The mathematical decoder may still reject other bytes. -/
theorem safe_to_initialized [DecidableEq Metadata]
    (decoder : StorageDecoder Metadata Raw) (decodeModel : Raw → Option Model)
    (initialized : decoder.Initialized) (metadata : Metadata)
    (destinationWidth : Nat) (destinationSafe : List AMByte → Prop) :
    Transfer (decoder.byteSize metadata) (Safe decoder decodeModel metadata) .safe
      destinationWidth destinationSafe .initialized := by
  intro sameWidth bytes admitted
  exact ⟨admitted.1.trans sameWidth,
    safe_initialized decoder decodeModel initialized metadata bytes admitted.2⟩

/-- Initialization suffices for safe admission only when both decoding stages
are complete for every initialized representation of the requested width. -/
theorem initialized_to_safe [DecidableEq Metadata]
    (decoder : StorageDecoder Metadata Raw) (decodeModel : Raw → Option Model)
    (complete : decoder.CompleteWith decodeModel) (metadata : Metadata)
    (sourceWidth : Nat) (sourceSafe : List AMByte → Prop) :
    Transfer sourceWidth sourceSafe .initialized
      (decoder.byteSize metadata) (Safe decoder decodeModel metadata) .safe := by
  intro sameWidth bytes admitted
  have width := admitted.1.trans sameWidth
  exact ⟨width, (safe_iff_runWith decoder decodeModel metadata bytes).mpr
    (complete metadata bytes width admitted.2)⟩

theorem initialized_identity (sourceWidth destinationWidth : Nat)
    (sourceSafe destinationSafe : List AMByte → Prop) :
    Transfer sourceWidth sourceSafe .initialized destinationWidth destinationSafe .initialized := by
  intro sameWidth bytes admitted
  exact ⟨admitted.1.trans sameWidth, admitted.2⟩

/-- Forgetting a byte-content promise leaves only the width requirement. -/
theorem to_uninit (sourceWidth destinationWidth : Nat)
    (sourceSafe destinationSafe : List AMByte → Prop) (sourceState : State) :
    Transfer sourceWidth sourceSafe sourceState destinationWidth destinationSafe .uninit := by
  intro sameWidth bytes admitted
  exact ⟨admitted.1.trans sameWidth, trivial⟩

theorem transfer_refl (width : Nat) (safe : List AMByte → Prop) (state : State) :
    Transfer width safe state width safe state := by
  intro _ _ admitted
  exact admitted

/-- The intermediate width must agree with the source width. Otherwise either
input transfer can hold solely because its own width guard is false. -/
theorem transfer_trans
    (sourceWidth middleWidth destinationWidth : Nat)
    (sourceSafe middleSafe destinationSafe : List AMByte → Prop)
    (sourceState middleState destinationState : State)
    (first : Transfer sourceWidth sourceSafe sourceState middleWidth middleSafe middleState)
    (second : Transfer middleWidth middleSafe middleState
      destinationWidth destinationSafe destinationState)
    (middleWidthAgrees : sourceWidth = middleWidth) :
    Transfer sourceWidth sourceSafe sourceState destinationWidth destinationSafe destinationState := by
  intro sameWidth bytes admitted
  exact second (middleWidthAgrees.symm.trans sameWidth) bytes
    (first middleWidthAgrees bytes admitted)

/-- Replacing either safe predicate by an equivalent domain preserves transfer.
This supports transparent mathematical wrappers without a registry of wrappers. -/
theorem allowed_congr (width : Nat) (left right : List AMByte → Prop)
    (equivalent : ∀ bytes, left bytes ↔ right bytes) (state : State) (bytes : List AMByte) :
    Allowed width left state bytes ↔ Allowed width right state bytes := by
  cases state <;> simp only [Allowed]
  exact and_congr_right (fun _ => equivalent bytes)

/-- Safe domains transfer by predicate inclusion at the actual source width.
Wrappers can establish this premise directly from their decoding definitions. -/
theorem safe_transfer_of_implication (sourceWidth destinationWidth : Nat)
    (sourceSafe destinationSafe : List AMByte → Prop)
    (preserves : ∀ bytes, bytes.length = sourceWidth → sourceSafe bytes → destinationSafe bytes) :
    Transfer sourceWidth sourceSafe .safe destinationWidth destinationSafe .safe := by
  intro sameWidth bytes admitted
  exact ⟨admitted.1.trans sameWidth, preserves bytes admitted.1 admitted.2⟩

/-- Initialization is inherited by any sublist, including a contiguous range. -/
theorem initialized_sublist (bytes subrange : List AMByte)
    (initialized : Initialized bytes) (contained : subrange.Sublist bytes) : Initialized subrange := by
  intro byte member
  exact initialized byte (contained.subset member)

theorem initialized_take (bytes : List AMByte) (initialized : Initialized bytes) (count : Nat) :
    Initialized (bytes.take count) :=
  initialized_sublist bytes _ initialized (List.take_sublist count bytes)

theorem initialized_drop (bytes : List AMByte) (initialized : Initialized bytes) (count : Nat) :
    Initialized (bytes.drop count) :=
  initialized_sublist bytes _ initialized (List.drop_sublist count bytes)

/-- A range is the requested prefix after skipping its starting position. -/
theorem initialized_subrange (bytes : List AMByte) (initialized : Initialized bytes)
    (start count : Nat) : Initialized ((bytes.drop start).take count) :=
  initialized_take _ (initialized_drop bytes initialized start) count

/-- Splicing initialized bytes into initialized storage preserves initialization.
The separate length premise in `initialized_replace_length` preserves the width. -/
theorem initialized_replace (bytes replacement : List AMByte)
    (initialized : Initialized bytes) (replacementInitialized : Initialized replacement)
    (start count : Nat) :
    Initialized (bytes.take start ++ replacement ++ bytes.drop (start + count)) := by
  exact (initialized_append _ _).mpr
    ⟨(initialized_append _ _).mpr
      ⟨initialized_take bytes initialized start, replacementInitialized⟩,
      initialized_drop bytes initialized (start + count)⟩

theorem initialized_replace_length (bytes replacement : List AMByte) (start count : Nat)
    (within : start + count ≤ bytes.length) (sameLength : replacement.length = count) :
    (bytes.take start ++ replacement ++ bytes.drop (start + count)).length = bytes.length := by
  simp only [List.length_append, List.length_take, List.length_drop, sameLength]
  omega

end Rust.Referent
