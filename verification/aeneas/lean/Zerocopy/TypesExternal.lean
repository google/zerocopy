/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Aeneas
@[expose] public section
open Aeneas.Std

-- The extracted NonZero carrier deliberately admits a zero field. The
-- physical and mathematical decoders in ModelPrelude perform the nonzero
-- check; merely building this Lean record grants no Rust construction rights.
abbrev core.num.niche_types.NonZeroU8Inner := U8
abbrev core.num.niche_types.NonZeroI8Inner := I8
abbrev core.num.niche_types.NonZeroU16Inner := U16
abbrev core.num.niche_types.NonZeroI16Inner := I16
abbrev core.num.niche_types.NonZeroU32Inner := U32
abbrev core.num.niche_types.NonZeroI32Inner := I32
abbrev core.num.niche_types.NonZeroU64Inner := U64
abbrev core.num.niche_types.NonZeroI64Inner := I64
abbrev core.num.niche_types.NonZeroU128Inner := U128
abbrev core.num.niche_types.NonZeroI128Inner := I128
abbrev core.num.niche_types.NonZeroUsizeInner := Usize
abbrev core.num.niche_types.NonZeroIsizeInner := Isize

structure core.num.nonzero.NonZero (T : Type) (_Inner : Type) where
  val : T

-- These standard-library types are opaque at this extraction boundary. Their
-- documented byte representation is that of T. Retain nominal wrappers:
-- identical stored bytes do not make their APIs or invariants interchangeable.
-- This models only stored values, not Cell's access protocol or destruction.
structure core.mem.manually_drop.ManuallyDrop (T : Type) where
  value : T

structure core.cell.Cell (T : Type) where
  value : T

structure core.cell.UnsafeCell (T : Type) where
  value : T
