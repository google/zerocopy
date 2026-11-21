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

/--
The reviewed caller requirements are: `locked` may never be called, while
`open` has no extra caller requirements. The predicates follow source
identities regardless of body-list order. The additional property is trivial
so this regression isolates caller-contract binding from functional results.
-/
def specs : Specs :=
  { safety := fun identity _ =>
      if identity = "rust-path-v1::locked" then False else True
    property := fun _ => True }

end Spec
