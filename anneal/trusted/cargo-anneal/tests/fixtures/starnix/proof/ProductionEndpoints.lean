-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import ProductionSteps

namespace ProductionSteps

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Endianness
  ProductionReduction

/-!
The generated module proves the source's actual transitions and return values.
These fixed endpoints separately require those values to implement endianness
conversion. A mutated implementation can have valid execution witnesses while
failing this bridge to the unchanged specification.
-/

theorem le8 (value : Word) :
    Safe sourceBody (endianArgs false 0 value) ∧
      Returns sourceBody (endianArgs false 0 value) (u64Val (value &&& 255)) :=
  le8_actual value

theorem le16 (value : Word) :
    Safe sourceBody (endianArgs false 1 value) ∧
      Returns sourceBody (endianArgs false 1 value) (u64Val (value &&& 65535)) :=
  le16_actual value

theorem le32 (value : Word) :
    Safe sourceBody (endianArgs false 2 value) ∧
      Returns sourceBody (endianArgs false 2 value) (u64Val (value &&& 4294967295)) :=
  le32_actual value

theorem le64 (value : Word) :
    Safe sourceBody (endianArgs false 3 value) ∧
      Returns sourceBody (endianArgs false 3 value) (u64Val value) :=
  le64_actual value

theorem be8 (value : Word) :
    Safe sourceBody (endianArgs true 0 value) ∧
      Returns sourceBody (endianArgs true 0 value) (u64Val (swap8 value)) :=
  be8_actual value

theorem be16 (value : Word) :
    Safe sourceBody (endianArgs true 1 value) ∧
      Returns sourceBody (endianArgs true 1 value) (u64Val (swap16 value)) :=
  be16_actual value

theorem be32 (value : Word) :
    Safe sourceBody (endianArgs true 2 value) ∧
      Returns sourceBody (endianArgs true 2 value) (u64Val (swap32 value)) :=
  be32_actual value

theorem be64 (value : Word) :
    Safe sourceBody (endianArgs true 3 value) ∧
      Returns sourceBody (endianArgs true 3 value) (u64Val (swap64 value)) :=
  be64_actual value

end ProductionSteps
