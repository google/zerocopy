-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def specs : Specs :=
  { safety := fun _ args =>
      match args with
      | [.scalar ⟨.isize, false, bits⟩] => bits ≠ BitVec.ofNat 128 0
      | _ => False
    property := fun _ => True }

end Spec
