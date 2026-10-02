/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs.Contracts
public import Proofs.Util
public import Proofs.NestedReference
@[expose] public section

/-!
This module proves contracts about the actual Aeneas function definitions.
The Raw namespace steps through extracted control flow and machine
arithmetic. Those lemmas deliberately retain useful representation domains,
even when an inline specification admits a smaller domain through automatic
decoding.

The canonical theorems outside Raw prove the generated Specs propositions.
They use the raw lemmas, decode accepted inputs, and establish that the
actual returned representation decodes and has the requested mathematical
properties. WP.spec_mono transfers a proved computation to a new
postcondition; it cannot replace that computation. Registered specifications
let later proofs reuse a callee's theorem instead of unfolding its
implementation each time.

Aeneas Result describes execution success, panic, or divergence. Rust Option
and Rust Result values may themselves be successful payloads. The proof must
keep these cases distinct.
-/
open Aeneas Aeneas.Std
