/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Controls.Funs
open Aeneas Aeneas.Std Controls

-- Start with a successful generated call: a missing module, wrong namespace,
-- or broken interpretation cannot count as rejecting an invalid execution.
example : valid (1#u8) ⦃ out => out = some true ⦄ := by
  simp [valid, util.transmute_unchecked, UScalar.val]

-- These are real Aeneas-generated callers, not handwritten monadic witnesses.
-- The invalid call must survive filtering even when its result is unused.
example : ignored = Result.fail .undef := by
  simp [ignored, util.transmute_unchecked, Zerocopy.forbiddenExecution, UScalar.val]

example : before_divergence false = Result.fail .undef := by
  simp [before_divergence, util.transmute_unchecked, Zerocopy.forbiddenExecution, UScalar.val]

example : ¬ WP.spec ignored (fun _ => True) := by
  simp [ignored, util.transmute_unchecked, Zerocopy.forbiddenExecution, UScalar.val]

example : ¬ WP.dspec (before_divergence false) (fun _ => True) := by
  simp [before_divergence, util.transmute_unchecked, Zerocopy.forbiddenExecution, UScalar.val]
