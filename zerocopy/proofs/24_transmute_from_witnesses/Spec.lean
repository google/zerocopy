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

/-!
# `impl_for_transmute_from!` Witnesses

Specifies 60 monomorphizations of generic items in unmodified
`zerocopy/src/`, selected with `scope.instantiations`, all under Profile v1.

`impl_for_transmute_from!` (`util/macros.rs`) implements `$trait` for `$ty`
by transmutation from `$repr`. In the sealing marker of each impl it defines

```rust
fn is_trait<T, R>()
where
    T: TransmuteFrom<R, Safe, Safe> + ?Sized,
    R: TransmuteFrom<T, Safe, Safe> + ?Sized,
    R: $trait,
{}
```

and a function `f` that calls `is_trait::<$ty, $repr>()`, so the impl only
compiles when those bounds hold. This unit covers the `is_trait` of every
such impl in `impls.rs`: the atomics (`impls::atomics`) and
`Wrapping<T>`, `ManuallyDrop<T>`, `Cell<T>`, and `UnsafeCell<T>` (`impls`).
Each is instantiated at the pair `($ty, $repr)` that its `f` passes, with
`T` chosen as `u32`, `[u8]`, `u16`, and `i64` for the four wrappers and
`u8` for `AtomicPtr<T>`. (`f` itself calls a generic function, which
capture does not support.)

Each body is pinned to its identity, which records the impl and the pair,
and is proved to be a safe function with no parameters that terminates
returning `()`. The bodies are listed in capture order, which sorts them by
identity.
-/

/-- All 60 bodies are safe functions, so `BodyVerified` never consults the
safety precondition. -/
def safetyPre (_identity : String) (_args : List Val) : Prop := True

/-- Total-correctness MIR call outcome at `defId` with empty caller memory. -/
noncomputable def ReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

/-- Body `defId` is the safe, parameterless function `identity`, and it
terminates returning `()`. -/
noncomputable def returnsUnitPost (p : Program) (defId : DefId)
    (identity : String) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => False
  | some body =>
    body.identity = identity ∧ body.isUnsafe = false ∧
    body.argumentCount = 0 ∧ ReturnsTotal p defId [] .unit

/-- Identity of `is_trait::<ty, repr>` in the sealing marker of
`impl trait for implSelf` in module `module`. -/
def witnessId (module trait implSelf ty repr : String) : String :=
  stringAppend
    (stringAppend
      (stringAppend
        (stringAppend
          (stringAppend
            (stringAppend
              (stringAppend
                (stringAppend
                  (stringAppend
                    (stringAppend "rust-path-v1::" module)
                    "::_::<impl ")
                  trait)
                " for ")
              implSelf)
            ">::only_derive_is_allowed_to_implement_this_trait::is_trait::<")
          ty)
        ", ")
      repr)
    ">"

/-- `wrapper<arg>`. -/
def applyTy (wrapper arg : String) : String :=
  stringAppend (stringAppend (stringAppend wrapper "<") arg) ">"

/-- The witness of `impl trait for wrapper<T>` (`$ty = wrapper<T>`,
`$repr = T`), instantiated with `T = inner`. -/
def wrapperWitnessId (trait wrapper inner : String) : String :=
  witnessId "impls" trait (applyTy wrapper "T") (applyTy wrapper inner) inner

/-- `core::sync::atomic::Atomic<prim>`, which `AtomicU8` and the other
atomic types name. -/
def atomicTy (prim : String) : String :=
  applyTy "core::sync::atomic::Atomic" prim

/-- The witness of `impl trait for Atomic<prim>` in module
`impls::atomics::atomic_<width>` (`$ty = Atomic<prim>`, `$repr = prim`). -/
def atomicWitnessId (width trait prim : String) : String :=
  witnessId (stringAppend "impls::atomics::atomic_" width) trait
    (atomicTy prim) (atomicTy prim) prim

/-- The witness of `impl trait for AtomicPtr<T>` (`$ty = AtomicPtr<T>`,
`$repr = *mut T`), instantiated with `T = u8`. -/
def atomicPtrWitnessId (trait : String) : String :=
  witnessId "impls::atomics::atomic_ptr" trait (atomicTy "*mut T")
    (atomicTy "*mut u8") "*mut u8"

/-- The identities of bodies `0` through `59`, in capture order. -/
def witnessIds : List String :=
  [wrapperWitnessId "FromBytes" "core::cell::Cell" "u16",
   wrapperWitnessId "FromBytes" "core::cell::UnsafeCell" "i64",
   wrapperWitnessId "FromBytes" "core::mem::manually_drop::ManuallyDrop" "[u8]",
   wrapperWitnessId "FromBytes" "core::num::wrapping::Wrapping" "u32",
   wrapperWitnessId "FromZeros" "core::cell::Cell" "u16",
   wrapperWitnessId "FromZeros" "core::cell::UnsafeCell" "i64",
   wrapperWitnessId "FromZeros" "core::mem::manually_drop::ManuallyDrop" "[u8]",
   wrapperWitnessId "FromZeros" "core::num::wrapping::Wrapping" "u32",
   wrapperWitnessId "IntoBytes" "core::cell::Cell" "u16",
   wrapperWitnessId "IntoBytes" "core::cell::UnsafeCell" "i64",
   wrapperWitnessId "IntoBytes" "core::mem::manually_drop::ManuallyDrop" "[u8]",
   wrapperWitnessId "IntoBytes" "core::num::wrapping::Wrapping" "u32",
   wrapperWitnessId "TryFromBytes" "core::cell::Cell" "u16",
   wrapperWitnessId
     "TryFromBytes" "core::mem::manually_drop::ManuallyDrop" "[u8]",
   wrapperWitnessId "TryFromBytes" "core::num::wrapping::Wrapping" "u32",
   atomicWitnessId "16" "FromBytes" "i16",
   atomicWitnessId "16" "FromBytes" "u16",
   atomicWitnessId "16" "FromZeros" "i16",
   atomicWitnessId "16" "FromZeros" "u16",
   atomicWitnessId "16" "IntoBytes" "i16",
   atomicWitnessId "16" "IntoBytes" "u16",
   atomicWitnessId "16" "TryFromBytes" "i16",
   atomicWitnessId "16" "TryFromBytes" "u16",
   atomicWitnessId "32" "FromBytes" "i32",
   atomicWitnessId "32" "FromBytes" "u32",
   atomicWitnessId "32" "FromZeros" "i32",
   atomicWitnessId "32" "FromZeros" "u32",
   atomicWitnessId "32" "IntoBytes" "i32",
   atomicWitnessId "32" "IntoBytes" "u32",
   atomicWitnessId "32" "TryFromBytes" "i32",
   atomicWitnessId "32" "TryFromBytes" "u32",
   atomicWitnessId "64" "FromBytes" "i64",
   atomicWitnessId "64" "FromBytes" "u64",
   atomicWitnessId "64" "FromZeros" "i64",
   atomicWitnessId "64" "FromZeros" "u64",
   atomicWitnessId "64" "IntoBytes" "i64",
   atomicWitnessId "64" "IntoBytes" "u64",
   atomicWitnessId "64" "TryFromBytes" "i64",
   atomicWitnessId "64" "TryFromBytes" "u64",
   atomicWitnessId "8" "FromBytes" "i8",
   atomicWitnessId "8" "FromBytes" "u8",
   atomicWitnessId "8" "FromZeros" "bool",
   atomicWitnessId "8" "FromZeros" "i8",
   atomicWitnessId "8" "FromZeros" "u8",
   atomicWitnessId "8" "IntoBytes" "bool",
   atomicWitnessId "8" "IntoBytes" "i8",
   atomicWitnessId "8" "IntoBytes" "u8",
   atomicWitnessId "8" "TryFromBytes" "bool",
   atomicWitnessId "8" "TryFromBytes" "i8",
   atomicWitnessId "8" "TryFromBytes" "u8",
   atomicWitnessId "ptr" "FromBytes" "isize",
   atomicWitnessId "ptr" "FromBytes" "usize",
   atomicPtrWitnessId "FromZeros",
   atomicWitnessId "ptr" "FromZeros" "isize",
   atomicWitnessId "ptr" "FromZeros" "usize",
   atomicWitnessId "ptr" "IntoBytes" "isize",
   atomicWitnessId "ptr" "IntoBytes" "usize",
   atomicPtrWitnessId "TryFromBytes",
   atomicWitnessId "ptr" "TryFromBytes" "isize",
   atomicWitnessId "ptr" "TryFromBytes" "usize"]

/-- Bodies `defId, defId + 1, ...` are the witnesses `ids`. -/
noncomputable def witnessPosts (p : Program) : DefId → List String → Prop
  | _, [] => True
  | defId, identity :: rest =>
    returnsUnitPost p defId identity ∧ witnessPosts p (defId + 1) rest

noncomputable def property (p : Program) : Prop :=
  p.bodies.length = 60 ∧ witnessPosts p 0 witnessIds

noncomputable def specs : Specs := ⟨safetyPre, property⟩

end Spec
