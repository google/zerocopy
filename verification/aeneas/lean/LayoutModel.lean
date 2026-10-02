/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import SpecPrelude
public import LayoutMath
@[expose] public section

/-!
Extracted trailing records contain machine words and compressed rounding
encodings. This module interprets those records as an unbounded complete-size
formula and a separately observed physical slice offset. Its definitions do
not call an extracted operation or assume that an operation is correct.

Keeping physical offset separate from normalized base and phase is essential:
inner padding can make them differ. Operation proofs use these observations
to connect extracted arithmetic with the independent layout mathematics.
-/
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs


end Zerocopy.Proofs
