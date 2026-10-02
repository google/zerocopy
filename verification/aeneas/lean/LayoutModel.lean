/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import LayoutMath
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs

abbrev NonZeroUsize := core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner


end Zerocopy.Proofs
