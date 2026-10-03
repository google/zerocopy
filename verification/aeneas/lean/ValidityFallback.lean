/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Validity
@[expose] public section

namespace AeneasSpecs

-- Import only after structural instances have elaborated. A missing child
-- instance must fail during that phase rather than capture this predicate.
instance (priority := low) unrestricted (α : Type u) : IsValid α :=
  ⟨fun _ => True⟩

end AeneasSpecs
