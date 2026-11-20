-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: vetted
prelude
import Init.NotationExtra

/-!
# Anneal Trusted Lean Foundation (`Trusted.lean`)

Root umbrella module for Anneal's trusted Lean 4 computing base (`trusted/lean/`).
Starts from `prelude` and imports only locked foundation modules from
`trusted/lean/foundation-lock.json` and `Trusted.*` submodules.
-/
