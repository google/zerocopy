# Rust to Lean Mapping

## Type Translation

Aeneas maps Rust types to its own standard library wrappers in Lean. When writing Lean specs, reference these explicitly:

### Primitives
*   `u8`..`u128` → `Std.U8` .. `Std.U128`
*   `i8`..`i128` → `Std.I8` .. `Std.I128`
*   `usize` → `Std.Usize`
*   `isize` → `Std.Isize`
*   `bool` → `Bool`

### Strings and Text
*   `String` → `String`
*   `&str` → `str`
*   `char` → `char`

### Compound Types
*   `[T; N]` → `Array T N` (e.g., `[u32; 4]` → `Array Std.U32 4`)
*   `&[T]` → `Slice T` 
*   `(A, B)` → `A × B`

### Custom Types
*   `struct` → Lean `structure`
*   `enum` → Lean `inductive`  (e.g., variants map to constructors like `MyEnum.VariantA x`)
*   *Note: `union` is currently unsupported by Aeneas.*

## Pointers and References

### References
Aeneas models references via pure pass-by-value and return-by-value semantics:
*   `&T` and nested references (e.g., `&&T`) flatten to the underlying type `T` (passed by value).
*   `&mut T` splits into two implicit variables: an input `T` (before execution) and a returned `T` (the post-state after execution).

### Raw Pointers
*   `*const T` → `ConstRawPtr T`
*   `*mut T` → `MutRawPtr T`

## Result Types and Control Flow

All functions are translated to return a monadic `Result T` to mathematically model potential panics or divergence—even if they cannot fail in Rust.
*   Functions returning `!` (the never type) map structurally to a `Result` that diverges (never resolves to `Result.ok`).

## Mutable State and Tuples

Functions mutating state (`&mut T`) return structured tuples in Lean tracking both the return value and the post-state of all mutated references.

Hermes handles this transparently by destructuring the tuple into `ret` and `arg'` variables via the `h_returns` hypothesis. `h_returns` automatically bounds the execution to these destructured variables, eliminating the need for manual tuple traversal.
