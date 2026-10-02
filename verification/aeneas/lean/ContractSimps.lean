/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Aeneas
public section

namespace AeneasContracts

/-- Normalizations for independently authored required contracts. This
attribute is initialized before the importing checker registers its lemmas. -/
register_simp_attr' contractSimpExt contractSimprocExt contract_simps

end AeneasContracts
