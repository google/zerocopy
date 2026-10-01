/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs

/-!
This is the import root for the extracted program and its handwritten
external models. Aeneas supplies generated Types and Funs; the external
modules state the explicitly selected correspondence for operations outside
that translation. Specs and proofs import this root so their computation
names refer to the selected complete extraction, not to inline mathematical
definitions.
-/
