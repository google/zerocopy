# Module 2: Rust to Lean Mapping

Aeneas maps Rust concepts into pure mathematical models in Lean's standard library. Before writing specifications in Anneal, you must understand how your Rust variables mathematically exist inside Lean.

This module covers exactly how Rust code is structurally transformed.

## 1. Type Translation

When writing Lean specs, reference Aeneas types explicitly:

### Primitives
*   `u8`..`u128` → `Aeneas.Std.U8` .. `Aeneas.Std.U128`
*   `i8`..`i128` → `Aeneas.Std.I8` .. `Aeneas.Std.I128`
*   `usize` → `Aeneas.Std.Usize`
*   `isize` → `Aeneas.Std.Isize`
*   `bool` → `Bool`

### Strings and Text
*   `String` → `String`
*   `&str` → `str`
*   `char` → `char`

### Compound Types
*   `[T; N]` → `Aeneas.Array T N` (e.g., `[u32; 4]` → `Aeneas.Array Aeneas.Std.U32 4`)
*   `&[T]` → `Aeneas.Slice T` 
*   `(A, B)` → `A × B`

### Custom Types
*   **Structs**: Map to Lean `structure`.
*   **Enums**: Map to Lean `inductive`.
*   **Unions**: *Currently entirely unsupported by Aeneas.*

## 2. Pointers and References

Because Lean is purely functional, Aeneas must completely abstract memory away.

*   **Immutable References (`&T`, `&&T`)**: Flatten completely to the underlying value type `T`. Lean simply passes the value.
*   **Raw Pointers (`*const T`, `*mut T`)**: Map to `Anneal.ConstRawPtr T` and `Anneal.MutRawPtr T`. (See the Memory Model module for how to perform spatial reasoning on these).

### The Tuple Destructuring of Mutation (`&mut T`)
This is the most critical functional shift: **Aeneas models `&mut T` via state-updating transformations.** 

Because a pure function cannot mutate memory in-place, a Rust function taking or returning mutable borrows is structurally translated into a Lean function that returns a **tuple**. 
This tuple contains *both* the normal return value, and the new post-execution state of every mutated variable.

```rust
// Rust
fn add_one(x: &mut u32) -> bool { ... }

-- Translated Lean structure (Conceptual)
def add_one (x : U32) : Result (Bool × U32) := ...
```

When you write proofs, you do not need to manually parse this tuple! Anneal intercepts it automatically and binds it to two distinct variables:
*   The original input is available as `x`.
*   The modified output is available as `x'`.

## 3. The Monadic Environment (`Result T`)

All functions translated by Aeneas return a monadic `Result T`, even if they cannot organically fail or panic in Rust. 

This is to mathematically model potential divergence (like division by zero, out-of-bounds panics, or infinite loops).
*   Functions returning `()` (Unit) map to `Result Unit`.
*   Functions returning `!` (Never) map structurally to a `Result` that inherently diverges (meaning it never resolves to `Result.ok`).

### Proving Correctness means Proving Success
When you write an `ensures` postcondition, you are inherently attempting to prove that the Aeneas `Result T` strictly resolves to `Result.ok T`. If your proof gets stuck, it frequently means that Lean believes there is a branch where your function panics or loops forever.

## 4. Aeneas Quirks & Workarounds

As Aeneas scales Rust to Lean, Anneal applies several structural patches that you must know about to avoid debugging bizarre errors.

### The Crate Namespace Translation
Aeneas generates top-level Lean modules using your package's name converted to `snake_case`. Anneal strictly adheres to this, explicitly converting hyphens (`-`) to underscores (`_`). 

**What this means for you:** If you are verifying a complex crate and need to manually unfold a function or reference an external definition, you must root it in this namespace (e.g. `unfold my_crate_name.my_function`).

### The Discriminant `isize` Hardcoding
When Aeneas translates Rust enumerations, it tags them with a `@[discriminant]` attribute for Lean's code generator. Because Aeneas omits the underlying type parameter, Anneal forcibly text-replaces this with `@[discriminant isize]`. 

**What this means for you:** If you use `#[repr(u8)]` or similar specialized tags on an enum, the Lean generated model still logically assumes the discriminant occupies an `isize` block of memory. This can lead to unexpected failures in sizing or alignment proofs for tightly packed structures.

### Opaque Functions and `noncomputable section`
Because `unsafe(axiom)` functions are translated into opaque Lean axioms (stubs with no bodies), Lean's bytecode compiler will aggressively reject the entire generated file if you attempt to build it. To suppress these errors, Anneal wraps the entirety of the generated `Funs.lean` file inside a `noncomputable section`.

**What this means for you:** You cannot use Lean's `#eval` command to test the runtime behavior of your verified functions computationally. They are strictly mathematical models.
