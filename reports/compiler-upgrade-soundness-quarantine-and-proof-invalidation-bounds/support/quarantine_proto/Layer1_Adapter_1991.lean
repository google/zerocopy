-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Layer0_TrustedCore

namespace Anneal.QuarantineProto

inductive FrontendStmt1991 where
  | fakeRead
  | boxDerefTransmute (dst : RegId) (src : RegId)
  | core (s : CoreStmt)
  deriving Repr, DecidableEq

def evalFrontend1991 (fs : FrontendStmt1991) (st : MachState) : MachState :=
  match fs with
  | .fakeRead => st
  | .boxDerefTransmute dst src => st.write dst (st.read src)
  | .core s => evalStmt s st

def adapt1991 (fs : FrontendStmt1991) : CoreStmt :=
  match fs with
  | .fakeRead => .nop
  | .boxDerefTransmute dst src => .assign dst (.var src)
  | .core s => s

theorem adapt1991_sound (fs : FrontendStmt1991) (st : MachState) :
    evalStmt (adapt1991 fs) st = evalFrontend1991 fs st := by
  cases fs <;> rfl

end Anneal.QuarantineProto
