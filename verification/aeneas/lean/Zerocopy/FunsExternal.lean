/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Types
@[expose] public section
open Aeneas Aeneas.Std
open Zerocopy

-- External semantic models: Clone copies the value; NonZero::get returns its
-- stored integer without failure. Their correspondence to Rust is part of the
-- trusted boundary described in ../../README.md, not a theorem of this package.
def core.num.niche_types.NonZeroUsizeInner.Insts.CoreCloneClone.clone
    (x : core.num.niche_types.NonZeroUsizeInner) :
    Result core.num.niche_types.NonZeroUsizeInner := .ok x

@[simp] def core.num.nonzero.NonZero.get
    {T Inner : Type} (_inst : core.num.nonzero.ZeroablePrimitive T Inner)
    (x : core.num.nonzero.NonZero T Inner) : Result T := .ok x.val
