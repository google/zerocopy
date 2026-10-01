/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

-- The corresponding TModel shape succeeds in ModelTests. This fixture must
-- fail at the authored shape because raw T and its dictionary are unavailable.
import DeriveModels
open AeneasSpecs
namespace TypeOnlyShapeNegative
structure RawDependent (T : Type) where
  value : T
aeneas_model_shape RawDependent with 1 type parameters begin
 model Value where
   value : T
end
end TypeOnlyShapeNegative
