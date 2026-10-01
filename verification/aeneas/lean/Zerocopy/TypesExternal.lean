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

-- These types model stored values, not Rust's niche encoding or memory layout.
-- The generic wrapper admits zero; the alignment theorems explicitly require
-- positivity. This over-approximation includes every valid NonZeroUsize.
abbrev core.num.niche_types.NonZeroUsizeInner := Usize

structure core.num.nonzero.NonZero (T : Type) (_Inner : Type) where
  val : T
