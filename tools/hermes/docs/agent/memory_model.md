# Hermes Memory Modeling

This document provides a conceptual overview of how Hermes represents Rust memory limits, layouts, and pointers within Lean 4. While the `llms-full.txt` file contains the exact Lean definitions and axioms from `Hermes.lean`, this document explains *why* those abstractions exist and how they fit together to model programs correctly.

## 1. Mathematical vs. Physical Layouts

A core concept in Hermes is the distinction between unbounded mathematical sizes and physically constrained memory layouts.

*   **`SpecLayout` (Mathematical):** Represents the idealized layout of a type. Its size is represented as an unbounded Lean `Nat`. This allows for reasoning about the structure of a type without worrying about physical memory limits (e.g., calculating the theoretical size of a slice with a massive number of elements).
*   **`Layout` (Physical):** Represents a layout that has been proven to fit within physical memory space. Its size is constrained by `Usize` (which fundamentally maps back to the limits of physical addressing).

Hermes uses the "Has*" trait convention to provide these layouts to types:
*   `HasSpecLayout`: Indicates a type has a mathematical layout.
*   `HasStaticLayout`: Indicates a fixed-size type has a physical layout (usually bounded by Rust's `Sized` bounds).

## 2. Allocations and Referents

To reason about pointer safety and bounds, Hermes models physical memory regions and the views into them.

*   **`Allocation`**: The foundational unit of memory. It represents a contiguous block of physical bytes starting at a specific `base` address and extending for a specific `size` (both constrained by `Usize`). Crucially, Allocations are constrained by target limits (often `isize::MAX` in Rust) to prevent pointer arithmetic overflow.
*   **`Referent`**: A conceptual "view" or a slice of an `Allocation`. Pointers in Hermes point to Referents.
*   **`FitsInAllocation`**: A core predicate linking the two. It asserts that a specific `Referent` is bound entirely within the confines of a specific `Allocation`.

When writing proofs about pointer safety, you are often tasked with proving that the layout of the type you are casting to or accessing `FitsInAllocation` for the pointer's original allocation.

## 3. Validity (`IsValid`)

While layouts define the shape of memory, `IsValid` defines the constraints on the *values* inhabiting that memory. 

`IsValid` is a typeclass that asserts internal invariants for a custom type. For example, a struct definition might have a physical `Layout` of 8 bytes, but its `IsValid` predicate might stipulate that the first 4 bytes must always be non-zero. When Hermes verifies specifications, it uses `IsValid` to add assumptions about function inputs and enforce guarantees about function outputs.
