-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import LibcoreAudit.Common
import LibcoreAudit.Shard00
import LibcoreAudit.Shard01
import LibcoreAudit.Shard02
import LibcoreAudit.Shard03
import LibcoreAudit.Shard04
import LibcoreAudit.Shard05
import LibcoreAudit.Shard06
import LibcoreAudit.Shard07
import LibcoreAudit.Shard08
import LibcoreAudit.Shard09
import LibcoreAudit.Shard10
import LibcoreAudit.Shard11
import LibcoreAudit.Shard12
import LibcoreAudit.Shard13
import LibcoreAudit.Shard14
import LibcoreAudit.Shard15

namespace LibcoreAudit

/-- Whole-`libcore` 16-shard conjunction theorem (`1,745,344` `HybridTrace` steps). -/
theorem libcore_all_16_shards_verified :
    checkLibcoreShard 0 = true ∧ checkLibcoreShard 1000 = true ∧ checkLibcoreShard 2000 = true ∧ checkLibcoreShard 3000 = true ∧ checkLibcoreShard 4000 = true ∧ checkLibcoreShard 5000 = true ∧ checkLibcoreShard 6000 = true ∧ checkLibcoreShard 7000 = true ∧ checkLibcoreShard 8000 = true ∧ checkLibcoreShard 9000 = true ∧ checkLibcoreShard 10000 = true ∧ checkLibcoreShard 11000 = true ∧ checkLibcoreShard 12000 = true ∧ checkLibcoreShard 13000 = true ∧ checkLibcoreShard 14000 = true ∧ checkLibcoreShard 15000 = true :=
  And.intro shard_00_verified (And.intro shard_01_verified (And.intro shard_02_verified (And.intro shard_03_verified (And.intro shard_04_verified (And.intro shard_05_verified (And.intro shard_06_verified (And.intro shard_07_verified (And.intro shard_08_verified (And.intro shard_09_verified (And.intro shard_10_verified (And.intro shard_11_verified (And.intro shard_12_verified (And.intro shard_13_verified (And.intro shard_14_verified (shard_15_verified)))))))))))))))

end LibcoreAudit
