/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Nominal

open Aeneas Aeneas.Std Result NominalTuples

example : True := by
  fail_if_success have : First = Second := rfl
  fail_if_success have : NominalTuples.Empty = OtherEmpty := rfl
  fail_if_success have : Generic Nat = OtherGeneric Nat := rfl
  fail_if_success have : Pair Nat = OtherPair Nat := rfl
  fail_if_success have : Nested Nat = OtherNested Nat := rfl
  trivial

example (x : First) : x = x := by
  fail_if_success have : Second := x
  fail_if_success have : Std.U32 := x
  rfl

example (x : Std.U32) : construct x = ok (First.mk x, Second.mk x) := rfl
example (x y : Std.U32) : project (First.mk x) (Second.mk y) = ok (x, y) := rfl
example (x y : Std.U32) : pattern (First.mk x) (Second.mk y) = ok (x, y) := rfl
example : empty = ok (Empty.mk, OtherEmpty.mk) := rfl
example : empty_pattern Empty.mk OtherEmpty.mk = ok () := rfl
example {T : Type} (x : T) : generic x = ok (Generic.mk x) := rfl
example {T : Type} (x : T) : other_generic x = ok (OtherGeneric.mk x) := rfl
example {T : Type} (x : T) : generic_pattern (Generic.mk x) = ok x := rfl
example {T : Type} (x : T) (y : Std.U32) : pair x y = ok (Pair.mk x y) := rfl
example {T : Type} (x : T) (y : Std.U32) : pair_pattern (Pair.mk x y) = ok (x, y) := rfl
example {T : Type} (x : T) (y z : Std.U32) :
    update (Pair.mk x y) z = ok (Pair.mk x z) := rfl
example {T : Type} (x : T) (y : Std.U32) :
    nested x y = ok (Nested.mk (First.mk y) (Second.mk y) (Generic.mk x)) := rfl
example {T : Type} (x : T) (a b : Std.U32) :
    nested_pattern (Nested.mk (First.mk a) (Second.mk b) (Generic.mk x)) = ok (a, b, x) := rfl
example (x : Std.U32) (y : Std.U64) : ordinary x y = ok (x, y) := rfl
example (x : Std.U32) (y : Std.U64) : ordinary_pattern (x, y) = ok (y, x) := rfl
example : ordinary_unit () = ok () := rfl
example {T : Type} (x : T) (y : Std.U32) : other_pair x y = ok (OtherPair.mk x y) := rfl
example {T : Type} (x : T) (y : Std.U32) : other_pair_pattern (OtherPair.mk x y) = ok (x, y) := rfl
example {T : Type} (x : T) (y : Std.U32) :
    other_nested x y = ok (OtherNested.mk (First.mk y) (Second.mk y) (Generic.mk x)) := rfl
example {T : Type} (x : T) (a b : Std.U32) :
    other_nested_pattern (OtherNested.mk (First.mk a) (Second.mk b) (Generic.mk x)) = ok (a, b, x) := rfl
