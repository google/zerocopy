# Rust to Lean Mapping

## Lean Translation of Rust Types
- `*const T` reliably maps to `ConstRawPtr T` in Lean, which is often easier to reason about in proofs than `NonNull<T>` (which maps to a wrapped `core.ptr.non_null.NonNull Self` structure).
- Functions and methods returning `T` may be translated by Aeneas to return `Result T` (ie, accounting for panicking), even if they never fail in Rust.
- In Hermes `ensures` blocks, you can simply pattern match Results directly instead of worrying about implicit unwrapping:
  ```lean
  ensures match KnownLayoutInst.my_method val with
          | Result.ok m => ...
          | _ => False
  ```
- **Standard types:** Aeneas maps Rust primitive types to its own standard library wrappers in Lean. If you are writing Lean specs, you will often need to reference these explicitly instead of primitive Lean types (e.g., `usize` -> `Std.Usize`, `u32` -> `Std.U32`).

## Implicit Variables in Specs (`ret` and `x'`)
- `ret` is an implicit variable injected by Hermes representing the successful return value of a function.
- For any mutable reference parameter `x: &mut T`, `x` refers to the variable's state **before** the function executes, while `x'` refers to its state **after** execution.
