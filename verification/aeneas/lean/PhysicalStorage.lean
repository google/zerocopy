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
A provider has one physical interpretation. Fixed storage is the Unit-metadata
case; indexed storage retains its own metadata and equality test. The fixed
accessor is deliberately partial: an owned-value primitive must not guess a
slice count, even when several counts have the same byte width.

Initialization and realizability range over the whole interpretation. The
fixed accessor supports existing owned-value primitives and fixed-layout laws;
it is a projection of this interpretation, never a second decoder to maintain.
-/

namespace AeneasSpecs
open Rust.Storage

inductive PhysicalStorage (Raw : Type u) where
  | fixed (decoder : BitDecoder Raw)
  | indexed (Metadata : Type) (equality : DecidableEq Metadata)
      (decoder : StorageDecoder Metadata Raw)

namespace PhysicalStorage

def fixed? : PhysicalStorage Raw → Option (BitDecoder Raw)
  | .fixed decoder => some decoder
  | .indexed .. => none

def Initialized : PhysicalStorage Raw → Prop
  | .fixed decoder => decoder.Initialized
  | .indexed _ equality decoder => @StorageDecoder.Initialized _ _ equality decoder

/-- Realizability uses the raw value's actual metadata, not a guessed count. -/
def Realizable (valid : Raw → Prop) : PhysicalStorage Raw → Prop
  | .fixed decoder => ∀ raw, valid raw → ∃ bytes, decoder.run bytes = some raw
  | .indexed _ equality decoder => ∀ raw, valid raw →
      ∃ bytes, @StorageDecoder.run _ _ equality decoder (decoder.metadata raw) bytes = some raw

/-- A storage wrapper keeps the child's metadata and byte interpretation.
The inverse law concerns only wrapping a child, not a mathematical encoder. -/
def map (physical : PhysicalStorage A) (wrap : A → B) (unwrap : B → A)
    (inverse : ∀ raw, unwrap (wrap raw) = raw) : PhysicalStorage B :=
  match physical with
  | .fixed decoder => .fixed (decoder.map wrap)
  | .indexed metadata equality decoder =>
    .indexed metadata equality (decoder.map wrap (fun raw => decoder.metadata (unwrap raw))
      (fun raw => congrArg decoder.metadata (inverse raw)))

@[simp] theorem fixed?_map (physical : PhysicalStorage A) (wrap : A → B) (unwrap : B → A)
    (inverse : ∀ raw, unwrap (wrap raw) = raw) :
    (physical.map wrap unwrap inverse).fixed? = physical.fixed?.map (·.map wrap) := by
  cases physical <;> rfl

theorem map_initialized (physical : PhysicalStorage A) (wrap : A → B) (unwrap : B → A)
    (inverse : ∀ raw, unwrap (wrap raw) = raw) (initialized : physical.Initialized) :
    (physical.map wrap unwrap inverse).Initialized := by
  cases physical with
  | fixed decoder => exact BitDecoder.map_initialized decoder wrap initialized
  | indexed metadata equality decoder =>
    letI := equality
    exact StorageDecoder.map_initialized decoder wrap (fun raw => decoder.metadata (unwrap raw))
      (fun raw => congrArg decoder.metadata (inverse raw)) initialized

theorem initialized_fixed {physical : PhysicalStorage Raw} {decoder : BitDecoder Raw}
    (available : physical.fixed? = some decoder) (initialized : physical.Initialized) :
    decoder.Initialized := by
  cases physical with
  | fixed selected => cases Option.some.inj available; exact initialized
  | indexed => contradiction

end PhysicalStorage
end AeneasSpecs

namespace Rust.Storage.StorageDecoder

/-- A sequence carrier may restrict its length (fixed arrays or bounded slices).
The original metadata and bytes are retained before checking that shape. -/
def restrict [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (valid : Raw → Prop) [DecidablePred valid] : StorageDecoder Metadata {raw // valid raw} where
  byteSize := decoder.byteSize
  metadata raw := decoder.metadata raw.val
  decode metadata bytes := (decoder.run metadata bytes).bind fun raw =>
    if h : valid raw then some ⟨raw, h⟩ else none

@[simp] theorem run_restrict [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (valid : Raw → Prop) [DecidablePred valid] (metadata : Metadata) (bytes : List AMByte) :
    (decoder.restrict valid).run metadata bytes =
      (decoder.run metadata bytes).bind (fun raw => if h : valid raw then some ⟨raw, h⟩ else none) := by
  by_cases width : bytes.length = decoder.byteSize metadata
  · cases language : decoder.decode metadata bytes with
    | none => simp [run, restrict, width, language]
    | some raw =>
      by_cases agrees : decoder.metadata raw = metadata
      · by_cases admitted : valid raw <;> simp [run, restrict, width, language, agrees, admitted]
      · simp [run, restrict, width, language, agrees]
  · simp [run, restrict, width]

theorem restrict_initialized [DecidableEq Metadata] (decoder : StorageDecoder Metadata Raw)
    (valid : Raw → Prop) [DecidablePred valid] (initialized : decoder.Initialized) :
    (decoder.restrict valid).Initialized := by
  intro metadata bytes raw accepted
  rw [run_restrict] at accepted
  cases language : decoder.run metadata bytes with
  | none => simp [language] at accepted
  | some output => exact initialized metadata bytes output language

end Rust.Storage.StorageDecoder
