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

noncomputable def specs : Trusted.MirSemantics.Specs :=
  ⟨fun _ _ => False, fun program =>
    ∀ args out,
      ¬Trusted.MirSemantics.Behavior
        (Trusted.MirSemantics.entryProgForBody program 0)
        { args := args } out⟩

end Spec
