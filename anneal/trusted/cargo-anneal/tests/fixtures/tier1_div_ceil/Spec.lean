-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def usizeVal (n : Nat) : Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 n⟩

/-- `div_ceil_usize(a, b)` returns `0` for `a = 0`, unwinds cleanly on `a ≠ 0`
with `b = 0`, and returns `⌈a / b⌉ = (a + b - 1) / b` without overflowing for
all nonzero `a, b : usize`. -/
noncomputable def divCeilSpec (program : Program) : Prop :=
  ∀ a b : BitVec 64,
    (a.toNat = 0 →
      Behavior (entryProgForBody program 0)
        { args := [usizeVal a.toNat, usizeVal b.toNat] }
        (.returned ⟨usizeVal 0, ⟨[]⟩⟩)) ∧
    (a.toNat ≠ 0 → b.toNat = 0 →
      Behavior (entryProgForBody program 0)
        { args := [usizeVal a.toNat, usizeVal b.toNat] }
        (.unwound ⟨[]⟩)) ∧
    (a.toNat ≠ 0 → b.toNat ≠ 0 →
      Behavior (entryProgForBody program 0)
        { args := [usizeVal a.toNat, usizeVal b.toNat] }
        (.returned ⟨usizeVal ((a.toNat + b.toNat - 1) / b.toNat), ⟨[]⟩⟩))

noncomputable def specs : Specs := ⟨fun _ _ => False, divCeilSpec⟩

end Spec
