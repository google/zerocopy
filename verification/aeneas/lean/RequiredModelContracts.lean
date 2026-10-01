/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RequiredModelContracts.Util
@[expose] public section

/-!
These adapters prove that mathematical inline promises retain independently
stated raw behavior and input coverage. Each receives provided, a proof about
an arbitrary run, and derives the matching Obligations proposition for that
same run. It never executes or independently proves the function to bypass a
weak authored spec.

Constructing mathematical input witnesses from raw premises checks the
promised domain. Recovering raw facts from the decoded result checks the
promised observations. The contract_simps attribute makes these ordinary
proved implications available to check_contract's bounded normalization.
-/
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

end Zerocopy.Proofs
