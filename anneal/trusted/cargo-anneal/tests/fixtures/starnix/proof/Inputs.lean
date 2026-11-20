-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Data.BitVec.Lemmas
import Endianness

namespace Endianness

/-- Four concrete proofs cover every logical width index. -/
theorem fin4_cases {p : Fin 4 → Prop}
    (h0 : p 0) (h1 : p 1) (h2 : p 2) (h3 : p 3) : ∀ w, p w :=
  Fin.cases h0
    (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (fun i => Fin.elim0 i))))

/-- The fixed specification rejects the masked-identity mutation used by CI. -/
theorem maskedIdentity16_rejected :
    ¬ ByteReversal 16 (1#64) ((1#64) &&& 0xffff) := by
  intro h
  have bit := h 0 (by decide)
  simp [reverseByteIndex] at bit

/-- The fixed specification rejects the constant-zero mutation used by CI. -/
theorem constantZero16_rejected :
    ¬ ByteReversal 16 (1#64) (0#64) := by
  intro h
  have bit := h 8 (by decide)
  simp [reverseByteIndex] at bit

end Endianness
