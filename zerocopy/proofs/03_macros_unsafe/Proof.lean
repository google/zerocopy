-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import AutoScaffold

namespace Proof

open AutoScaffold

theorem verify : Expected.claim :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, all_bodies_safe,
    ⟨rfl, id_unsafe_macro, body_unsafe_macro,
      get_unsafe_macro, rfl, rfl, rfl, ok_unsafe_macro.2⟩⟩

end Proof
