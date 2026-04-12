# Module 3: Memory Model

Hermes relies on pure functional translation for safe Rust, but safe Rust is ultimately just an abstraction over raw physical memory. When you write specifications for `unsafe` code—code that manipulates raw bytes and pointers—you must leave the functional world and reason spatially.

Hermes provides a mathematically rigorous model of physical memory for this exact purpose.

## 1. The "Lower Bound" Justification

Why does Hermes define its own memory model instead of using Aeneas's or Rust's?

Rust currently lacks a formalized "operational semantics"—an official, mathematically proven set of rules describing exactly what `rustc` is allowed to do with memory. Because this formal model doesn't exist, Hermes cannot assume *how* Rust structures its memory internally.

Instead, Hermes relies strictly on **minimal, universally guaranteed physical truths**. It models a "lower bound" of memory semantics—proving properties that must be physically true on any architecture, without making assumptions about compiler optimizations or undefined behavior flags that aren't strictly specified by Rust.

## 2. Core Abstractions Revealed

To reason about memory, you interact with several core Lean abstractions defined in `Anneal.lean`. While you don't always instantiate these directly, they form the basis of all spatial invariants.

### Layouts
Every type has a layout: a size and an alignment constraint. Hermes distinguishes between mathematical layouts (unbounded) and physical layouts (bounded by the address space).

```lean
/-- A mathematically idealized memory layout (size can exceed Usize::MAX) -/
structure SpecLayout where
  size : Nat
  align : Alignment
  sizeAligned : align.val.val ∣ size

/-- A valid physical memory layout (bounded by the machine's address space) -/
structure Layout where
  size : Usize
  align : Alignment
  sizeAligned : align.val.val ∣ size.val
```
Hermes provides typeclasses like `HasStaticLayout T` to automatically retrieve the `Layout` for any sized type `T`.

### Allocations and Referents
An **Allocation** represents a contiguous block of memory requested from the OS or allocator. A **Referent** represents the specific slice of memory that a pointer is allowed to address.

Crucially, Hermes represents the addressable space not just as a `base` and `size`, but as a mathematical `Set Nat`.

```lean
/-- Represents a Rust allocation (e.g. from Box, Vec, or static memory) -/
structure Allocation where
  base : Usize
  size : Usize
  addresses : Set Nat
  base_not_null : base.val ≠ 0
  size_le_isize_max : size.val ≤ Isize.max
  base_add_size_le_usize_max : base.val + size.val ≤ Usize.max
  bounds : ∀ a ∈ addresses, base.val ≤ a ∧ a < base.val + size.val

/-- The region of memory a specific pointer addresses -/
structure Referent where
  address : Usize
  size : Usize
  addresses : Set Nat
  addresses_are_usizes : ∀ a ∈ addresses, a ≤ Usize.max
  bounds : ∀ a ∈ addresses, address.val ≤ a ∧ a < address.val + size.val
```

## 3. The Four Principles of the Memory Model

When writing memory specifications (such as for a raw pointer wrapper), your proofs will rely on the following four principles:

### Principle 1: Mathematical vs Physical Separation
Hermes strictly separates mathematical models from physical representations.
*   Physical properties (like an address) are bounded (`Usize`, `Isize`).
*   Mathematical properties (like the `addresses : Set Nat`) use unbounded integers (`Nat`, `Int`) to prevent overflow reasoning during logical proofs. 

It is sometimes useful to convert bounded machine integers to `Nat` or `Int` using `.val` before doing arithmetic in your proofs.

> [!TIP]
> **Numerical Literal Suffixes (`#usize`):** Because memory modeling differentiates physical sizes from mathematical sizes, Lean will often raise ambiguity errors when you use bare numbers. You must often suffix numerical literals (e.g., `0#usize`) to explicitly specify their type class.

### Principle 2: Typeclass Automation
Instead of manually passing layout sizes and alignments, Hermes uses Lean's typeclass resolution (`[HasStaticLayout T]`) to implicitly carry physical bounds. You rarely construct a `Layout` manually; you lean on the generator to provide `HasStaticLayout T` and use `size_of T` or `align_of T`.

If you *must* manually instantiate typeclasses for a custom proof or lemma:
*   **Empty Typeclasses:** Some marker traits like `Sized` translate to empty typeclasses in Lean. You can legally instantiate them dynamically using the anonymous constructor `⟨⟩` (e.g., `have h_sized : Hermes.core.marker.Sized T := ⟨⟩`).
*   **Complex Layouts:** For complex typeclasses like `HasStaticLayout`, Lean's inference struggles with fully anonymous instantiations (e.g. `⟨_, _⟩`). If you need to manually construct one, you must alias it to a named `have` binding first before using it (e.g. `have h_layout : Hermes.HasStaticLayout T := { ... }`).

### Principle 3: Spatial Inclusion (The `FitsInAllocation` Axiom)
To prove that a pointer is safe to read or write, you must prove that its `Referent` (the memory it wants to touch) is physically contained within a valid `Allocation`.
Hermes formalizes this spatial relationship:
```lean
def FitsInAllocation (r : Referent) (a : Allocation) : Prop :=
  r.addresses ⊆ a.addresses ∧
  a.base.val ≤ r.address.val ∧ r.address.val + r.size.val ≤ a.base.val + a.size.val
```
If your `unsafe` code offsets a pointer, your specification must prove that the new `Referent` still satisfies `FitsInAllocation`.

### Principle 4: Logical Reflection (Contiguity)
Just because a pointer has a base address and a size does not mean the memory within that range is completely addressable (due to padding, uninitialized bytes, or fragmentation). To perform a bulk read/write, you must prove the memory is continuous:
```lean
def Referent.IsContiguous (r : Referent) : Prop :=
  ∀ a, r.address.val ≤ a ∧ a < r.address.val + r.size.val → a ∈ r.addresses
```
This is the heart of spatial reasoning in Hermes: mapping abstract types to their contiguous byte-level realities and ensuring they never violate the bounds of their parent `Allocation`.
