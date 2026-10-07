/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
import Rust.Storage

namespace Rust.Storage.Tests

-- Nonempty arrays preserve element order and byte values.
example : (arrayDecoder boolDecoder 3).run
    [AMByte.init 0, AMByte.init 1, AMByte.init 0] =
    some ⟨[false, true, false], rfl⟩ := by decide

example : (arrayDecoder byteDecoder 3).run
    [AMByte.init 0, AMByte.init 2, AMByte.init 255] =
    some ⟨[0, 2, 255], rfl⟩ := by decide

-- Empty arrays accept no representation bytes, regardless of the element width.
example : (arrayDecoder boolDecoder 0).run [] = some ⟨[], rfl⟩ := by decide
example : (arrayDecoder byteDecoder 0).run [] = some ⟨[], rfl⟩ := by decide
example : (arrayDecoder unitDecoder 0).run [] = some ⟨[], rfl⟩ := by decide
example : (arrayDecoder boolDecoder 0).run [AMByte.init 0] = none := by decide

-- Positive counts of zero-sized elements decode empty chunks repeatedly.
example : (arrayDecoder unitDecoder 3).run [] = some ⟨[(), (), ()], rfl⟩ := by decide
example : (arrayDecoder unitDecoder 3).run [AMByte.init 0] = none := by decide
example : (arrayDecoder unitDecoder 3).decode [AMByte.init 0] = none := by decide

-- The outer width guard rejects both extra and short representations.
example : (arrayDecoder boolDecoder 2).run
    [AMByte.init 0, AMByte.init 1, AMByte.init 0] = none := by decide
example : (arrayDecoder boolDecoder 2).run [AMByte.init 0] = none := by decide

-- The recursive decoder also enforces the final remainder and each chunk's width.
example : (arrayDecoder boolDecoder 2).decode
    [AMByte.init 0, AMByte.init 1, AMByte.init 0] = none := by decide
example : (arrayDecoder boolDecoder 2).decode [AMByte.init 0] = none := by decide

-- A failure in a later element propagates despite earlier success.
example : (arrayDecoder boolDecoder 2).run [AMByte.init 0, AMByte.init 2] = none := by decide
example : (arrayDecoder boolDecoder 2).run [AMByte.init 1, AMByte.uninit] = none := by decide
example : (arrayDecoder byteDecoder 2).run [AMByte.init 255, AMByte.uninit] = none := by decide

-- Initialization is inherited only when an element law is supplied.
example : (arrayDecoder boolDecoder 3).Initialized :=
  arrayDecoder_initialized boolDecoder boolDecoder_initialized 3
example : (arrayDecoder byteDecoder 3).Initialized :=
  arrayDecoder_initialized byteDecoder byteDecoder_initialized 3
example : (arrayDecoder unitDecoder 3).Initialized :=
  arrayDecoder_initialized unitDecoder unitDecoder_initialized 3

-- A decoder may accept an uninitialized byte, but cannot claim the law.
def badDecoder : BitDecoder Unit where
  byteSize := 1
  decode _ := some ()

example : badDecoder.run [AMByte.uninit] = some () := by decide
example : ¬ badDecoder.Initialized := by
  intro h
  have impossible := h [AMByte.uninit] () (by decide)
  simp [Initialized] at impossible

-- The width guard remains effective for deliberately permissive decoders.
example : badDecoder.run [] = none := by decide
example : badDecoder.run [AMByte.uninit, AMByte.uninit] = none := by decide

-- Mapping values retains byte width and initialization for an adapter.
example : (byteDecoder.map (fun byte => byte.toNat)).run [AMByte.init 255] = some 255 := by decide
example : (byteDecoder.map (fun byte => byte.toNat)).Initialized :=
  BitDecoder.map_initialized byteDecoder _ byteDecoder_initialized

#print axioms arrayDecoder_initialized
#print axioms arrayDecoder_run_length
#print axioms arrayDecoder_output_length

end Rust.Storage.Tests
