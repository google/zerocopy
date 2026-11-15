-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lake
open Lake DSL

package «k2_daemon» where
  moreLeancArgs := #["-O3", "-march=native"]

lean_lib «DaemonSpec» where

@[default_target]
lean_exe «anneal_kernel_daemon» where
  root := `AnnealKernelDaemon
  supportInterpreter := true
