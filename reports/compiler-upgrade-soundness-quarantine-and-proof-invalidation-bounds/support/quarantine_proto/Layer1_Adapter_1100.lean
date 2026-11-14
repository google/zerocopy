-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Layer0_TrustedCore

namespace Anneal.QuarantineProto

inductive FrontendStmt1100 where
  | fakeRead
  | phantomDerefAssign (dst : RegId) (src : RegId)
  | boxDerefTransmute (dst : RegId) (src : RegId)
  | core (s : CoreStmt)
  deriving Repr, DecidableEq

def evalFrontend1100 (fs : FrontendStmt1100) (st : MachState) : MachState :=
  match fs with
  | .fakeRead => st
  | .phantomDerefAssign dst src => st.write dst (st.read src)
  | .boxDerefTransmute dst src => st.write dst (st.read src)
  | .core s => evalStmt s st

def adapt1100 (fs : FrontendStmt1100) : CoreStmt :=
  match fs with
  | .fakeRead => .nop
  | .phantomDerefAssign dst src => .assign dst (.var src)
  | .boxDerefTransmute dst src => .assign dst (.var src)
  | .core s => s

theorem adapt1100_sound (fs : FrontendStmt1100) (st : MachState) :
    evalStmt (adapt1100 fs) st = evalFrontend1100 fs st := by
  cases fs <;> rfl

end Anneal.QuarantineProto
