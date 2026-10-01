/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Nominal

open Aeneas Aeneas.Std NominalTuples

example : First = Second := rfl
example : NominalTuples.Empty = OtherEmpty := rfl
example : Generic Nat = OtherGeneric Nat := rfl
example : Pair Nat = OtherPair Nat := rfl
example : Nested Nat = OtherNested Nat := rfl
example (x : First) : Second := x
example (x : Std.U32) : First := x
