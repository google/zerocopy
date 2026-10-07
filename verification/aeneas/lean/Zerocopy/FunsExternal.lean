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

-- Rust's unchecked integer operations are defined only when their exact
-- arithmetic fits. Use the backend's checked operations on that domain. A
-- failed model run outside it establishes no Rust behavior: the corresponding
-- Rust operation has undefined behavior, rather than a promised panic.
def core.num.Usize.unchecked_add (left right : Usize) : Result Usize := left + right
def core.num.Usize.unchecked_mul (left right : Usize) : Result Usize := left * right

@[simp] def core.num.nonzero.NonZero.get
    {T Inner : Type} (_inst : core.num.nonzero.ZeroablePrimitive T Inner)
    (x : core.num.nonzero.NonZero T Inner) : Result T := .ok x.val

-- Aeneas erases Rust's ABI information from a generic Type parameter. These
-- two data parameters supply that information. They assert no propositions;
-- every consumer must prove its contract under explicit size/alignment inputs.
-- The axiom audit admits exactly these signatures, never arbitrary axioms.
axiom Zerocopy.RustLayout.size (T : Type) : Usize
axiom Zerocopy.RustLayout.align (T : Type) : Usize

@[simp] noncomputable def core.mem.size_of (T : Type) : Result Usize := by
  classical
  exact .ok (if T = Usize then
    { bv := BitVec.ofNat _ (System.Platform.numBits / 8) }
    else Zerocopy.RustLayout.size T)

@[simp] noncomputable def core.mem.align_of (T : Type) : Result Usize :=
  .ok (Zerocopy.RustLayout.align T)

-- The extracted call sites instantiate this primitive only at Usize.
@[simp] noncomputable def core.num.nonzero.NonZero.new
    {T Inner : Type} (_inst : core.num.nonzero.ZeroablePrimitive T Inner)
    (x : T) : Result (Option (core.num.nonzero.NonZero T Inner)) := by
  classical
  exact if h : T = Usize then
    if (cast h x : Usize) = 0#usize then .ok none else .ok (some ⟨x⟩)
  else .fail .panic
