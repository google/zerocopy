/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Aeneas
public section

/-!
Required-contract comparisons use a dedicated simplification set. Registering
it in this small module lets imported modules add normalizations before the
checker runs. The lemmas remain ordinary checked theorems; this attribute only
controls which rewrites the comparison's proof search attempts.
-/


namespace AeneasContracts

/-- Normalizations for independently authored required contracts. This
attribute is initialized before the importing checker registers its lemmas. -/
register_simp_attr' contractSimpExt contractSimprocExt contract_simps

end AeneasContracts
