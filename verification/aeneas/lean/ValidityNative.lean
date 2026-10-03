/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.TypesExternal
public import Validity
@[expose] public section

open Aeneas.Std
namespace AeneasSpecs

-- The stored-value model deliberately admits zero. Conditional specifications
-- recover Rust's NonZeroUsize representation domain through this predicate.
@[validity_canonical] instance validNonZeroUsize : IsValid
    (core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner) :=
  ⟨fun x => 0 < x.val.val⟩

end AeneasSpecs
