-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Captured
public import SourceInputs

@[expose] public section

namespace ProductionReduction

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Endianness

abbrev sourceBody : Body := Captured.program.bodies[0]'(by decide)

abbrev dataWidthVal (width : Nat) : Val :=
  bodyDataWidthVal sourceBody width

abbrev endianArgs (toBe : Bool) (width : Nat) (value : Word) : List Val :=
  bodyEndianArgs sourceBody toBe width value

end ProductionReduction

end
