-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted
import Std.Internal.UV.TCP
import Std.Net.Addr

namespace EvilTheory

-- 1. Arbitrary file write outside output `.olean`
#eval IO.FS.writeFile "/tmp/pwned" "pwn"

-- 2a. Unauthorized host file read outside staged source/toolchain closure via `#eval`
#eval IO.FS.readFile "/etc/hostname"

-- 2b. Unauthorized host file read via `include_str` macro without `#eval`
def stolenHostname : String := include_str "../../../../../../../../../../../../etc/hostname"

-- 3. Process spawning (`sh -c id`)
#eval IO.Process.output { cmd := "sh", args := #["-c", "id"] }

-- 4. Overwriting upstream `Trusted.olean` during compilation
#eval IO.FS.writeFile "Trusted.olean" "corrupted"

-- 5. Network socket creation (`socket(AF_INET, SOCK_STREAM, 0)`)
#eval do
  let sock ← Std.Internal.UV.TCP.Socket.new
  let addr := Std.Net.SocketAddress.v4
    (Std.Net.SocketAddressV4.mk (Std.Net.IPv4Addr.ofParts 127 0 0 1) 0)
  sock.bind addr

theorem bogus : Trusted.targetSpec 0 = 42 := rfl

end EvilTheory
