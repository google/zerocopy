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
    ⟨rfl, id_unit_from_elem_count, body_unit_from_elem_count,
      id_unit_to_elem_count, body_unit_to_elem_count,
      get_unit_from_elem_count, rfl, rfl,
      get_unit_to_elem_count, rfl, rfl,
      ok_unit_from_elem_count.2, ok_unit_to_elem_count.2,
      ⟨ok_unit_to_elem_count.2, ok_unit_from_elem_count.2 0⟩,
      fun n => ⟨ok_unit_from_elem_count.2 n, ok_unit_to_elem_count.2⟩⟩⟩

end Proof
