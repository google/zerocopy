/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import DeriveModels
@[expose] public section

/-!
This module produces decoded models whose records contain automatically proved
constraints. A separate consumer module unfolds these definitions and uses the
generated decomposition theorems. Splitting producer from consumer catches
export bugs that a same-module proof could miss, particularly private proof
auxiliaries embedded in an exposed decoder.
-/

open AeneasSpecs Aeneas.Std
namespace ModelExportRegression
structure Raw where
  word : Usize
aeneas_model_shape Raw with 0 type parameters begin
 model Value where
   word : Nat
   fits : word ≤ Usize.max
end
derive_rust_model Raw with 0 type parameters decode self =>
  let word := self.word.value
  { word := word, .. }
check_model_binding Raw with 0 type parameters

structure Encoding where
  word : core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner
aeneas_model_shape Encoding with 0 type parameters begin
 model Value where
   align : Nat
   phase : Nat
   pow2 : align.isPowerOfTwo
   phase_lt : phase < align
   fits : align + phase ≤ Usize.max
end
derive_rust_model Encoding with 0 type parameters decode self =>
  let word := self.word.value
  let align := 2 ^ Nat.log2 word
  { align := align, phase := word - align, .. }
check_model_binding Encoding with 0 type parameters

structure Fallible where
  word : Usize
aeneas_model_shape Fallible with 0 type parameters begin
 model Value where
   word : Nat
   positive : 0 < word
   fits : word ≤ Usize.max
end
derive_rust_model Fallible with 0 type parameters decode? self =>
  if h : 1 < self.word.value then
    some { word := self.word.value - 1, .. }
  else none
check_model_binding Fallible with 0 type parameters

end ModelExportRegression
