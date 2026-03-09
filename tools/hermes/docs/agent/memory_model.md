# Hermes Memory Modeling Principles

This document prescribes the core principles that agents (and humans) must understand when writing proofs that interact with the Hermes memory model. 

For technical definitions, exact theorems, and the physical implementation of these principles, **you must consult `Hermes.lean` directly.**

## 1. The Mathematical vs. Physical Principle
*   **The Principle:** Never conflate mathematical sizing (`Nat`) with physical addressing (`Usize`).
*   **Guidance:** When writing purely logical bounds (like the abstract capacity of a sequence), use unbounded `Nat`s (`SpecLayout`). When writing bounds for pointer arithmetic, allocations, or validating the physical size of a generic type, you must use `Usize` (`Layout`). Crossing between them requires verifying a `FitsInUsize` property.

## 2. The Typeclass Automation Principle
*   **The Principle:** Lean’s typeclass resolution mechanically synthesizes memory layouts and constraints.
*   **Guidance:** Do not manually construct `Layout` or `SpecLayout` objects. Instead, rely on the `[HasStaticLayout T]` or `[HasSpecLayout T]` typeclasses provided in your theorem context. If Lean complains about missing derivations, the underlying Rust type is likely missing a bound (like `Sized`) or requires a mathematically bounded layout proof.

## 3. The Spatial Inclusion Principle
*   **The Principle:** Pointers point to mathematical *views* (`Referent`), which must be physically contained within allocated blocks (`Allocation`).
*   **Guidance:** You cannot guarantee pointer safety simply by proving `addr + size < MAX`. True safety strictly requires proving `FitsInAllocation r a`—meaning the requested `Referent` is a guaranteed sub-region bounds-checked within a parent `Allocation`. When dealing with raw pointers, your primary goal is manipulating and proving these inclusion relationships.

## 4. The Logical Reflection Principle
*   **The Principle:** Hermes applies layout specifications to Lean values, but the statements made *actually* apply to the source Rust program, not the Lean representation itself.
*   **Guidance:** When `HasLayout` returns a size of 8 bytes for an `x : Aeneas.Std.Usize`, it is mathematically claiming that the original Rust `usize` occupies 8 bytes in physical memory. It is *not* claiming that the Lean `x` (which is a structural inductive wrapper around a `Fin`) occupies 8 bytes in the Lean runtime. Always interpret Hermes memory theorems as logically reflecting the Rust application's physical reality, irrespective of Lean's internal memory management.
