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
    ⟨rfl,
      ⟨id_unsafe_macro, body_unsafe_macro, get_unsafe_macro,
        rfl, rfl, rfl, ok_unsafe_macro.2⟩,
      ⟨id_unit_from_elem_count, body_unit_from_elem_count,
        id_unit_to_elem_count, body_unit_to_elem_count,
        get_unit_from_elem_count, rfl, rfl,
        get_unit_to_elem_count, rfl, rfl,
        ok_unit_from_elem_count.2, ok_unit_to_elem_count.2⟩,
      ⟨id_usize_from_elem_count, body_usize_from_elem_count,
        id_usize_to_elem_count, body_usize_to_elem_count,
        get_usize_from_elem_count, rfl, rfl,
        get_usize_to_elem_count, rfl, rfl,
        ok_usize_from_elem_count.2, ok_usize_to_elem_count.2⟩,
      ⟨id_u8_Immutable_marker, body_u8_Immutable_marker,
        get_u8_Immutable_marker, rfl, rfl, rfl,
        ok_u8_Immutable_marker.2⟩,
      ⟨id_u8_TryFromBytes_marker, body_u8_TryFromBytes_marker,
        get_u8_TryFromBytes_marker, rfl, rfl, rfl,
        ok_u8_TryFromBytes_marker.2⟩,
      ⟨id_u8_FromZeros_marker, body_u8_FromZeros_marker,
        get_u8_FromZeros_marker, rfl, rfl, rfl,
        ok_u8_FromZeros_marker.2⟩,
      ⟨id_u8_FromBytes_marker, body_u8_FromBytes_marker,
        get_u8_FromBytes_marker, rfl, rfl, rfl,
        ok_u8_FromBytes_marker.2⟩⟩⟩

end Proof
