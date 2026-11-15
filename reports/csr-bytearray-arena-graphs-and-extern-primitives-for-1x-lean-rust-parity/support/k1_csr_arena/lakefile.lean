-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lake
open Lake DSL

package «k1_csr_arena» where
  moreLeancArgs := #["-O3", "-march=native", "-fno-strict-aliasing", "-include", "anneal_substrate_shim.h"]

lean_lib «ByteWordSlice» where

lean_lib «CSRGraph» where

@[default_target]
lean_exe «k1_bench» where
  root := `K1Bench
