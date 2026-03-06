<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Hermes

## Basic commands

1. Run with `cargo run verify`.
2. Run unit tests with `cargo test --bin hermes`.
3. Run all tests (including integration tests) with `cargo test`.
4. Run a *specific* integration test fixture with `cargo test --test integration fixture_name`.

## Tips

1. Integration tests are expensive. Prefer `cargo test --bin hermes` for quick verification and iteration,
   and only run `cargo test --test integration` when you need to verify the integration tests.
2. To see the generated Lean code for a module, use `cargo run expand`. This will run Aeneas and Hermes but skip verification, outputting the generated `.lean` definitions to the terminal.
   ```bash
   cargo run expand --example abs
   ```
3. To see where intermediate artifacts are placed on disk, run with `RUST_LOG=hermes=trace` as a fallback:
  ```bash
  RUST_LOG=hermes=trace cargo run verify --example abs
  ```

## Integration Testing

1. **Updating Expected Output:** Hermes integration tests (stored in `tests/fixtures/<test_name>`) assert against an `expected.stderr` or `out.txt` file. When you intentionally change the behavior or output of a test, do not edit these files manually. Instead, run the integration test with `BLESS=1` to automatically overwrite the snapshot files:
   ```bash
   BLESS=1 cargo test --test integration fixture_name
   ```

2. **Allowing `sorry`:** While developing and ensuring Aeneas translates Rust correctly, you don't have to write the full Lean proof immediately. You can write `sorry` inside the `proof` block. However, you must pass `--allow-sorry` to Hermes so the verifier doesn't fail immediately on the unimplemented proof. For integration tests, this is done by adding `--allow-sorry` to the `args` array in the fixture's `hermes.toml`:
   ```toml
   args = ["verify", "--allow-sorry"]
   ```

## Debugging Tips

1. **Debugging Aeneas vs Hermes Mismatches**
   - If you encounter Lean type mismatches (e.g., `Application type mismatch`), it's often a mismatch between what Aeneas generated for the function and what Hermes assumed Aeneas generated in the theorem signature.
   - Standard integration tests (`cargo test --test integration`) delete their temporary output directory (`target/hermes-test-XXX`) upon completion.
   - If a test fails and you want to inspect the generated Lean code, use the `HERMES_KEEP_TEST_DIR=1` environment variable.
   - The test runner will preserve the directory and print its path to stderr:
     ```bash
     HERMES_KEEP_TEST_DIR=1 cargo test --test integration macro_edge_cases
     ```
   - Look at `Funs.lean` to see the actual Aeneas parameters, and `[TestName].lean` to see the Hermes theorem signature.

2. **Caches Need Busting**
   - Sometimes `cargo test` fails with bizarre syntax errors that persist despite fixing the code.
   - If this happens, clear the integration caches: `rm -rf target/hermes_integration_cache`.

4. **Lean Translation of Rust Types**
   - `*const T` reliably maps to `ConstRawPtr T` in Lean, which is often easier to reason about in proofs than `NonNull<T>` (which maps to a wrapped `core.ptr.non_null.NonNull Self` structure).
   - Trait methods that return primitive types (like returning `usize` from `fn my_method() -> usize`) are frequently translated by Aeneas to return `Result Std.Usize`, even if they never fail in Rust.
   - For structural properties without `Result` wrapping, prefer trait Associated Constants (`const FOO: Type`) over Methods, since Aeneas lowers constants cleanly into flat values.
   - In Hermes `ensures` blocks, you can simply pattern match Results directly instead of worrying about implicit unwrapping:
     ```lean
     ensures match KnownLayoutInst.my_method val with
             | Result.ok m => ...
             | _ => False
     ```
   - **Standard types:** Aeneas maps Rust primitive types to its own standard library wrappers in Lean. If you are writing Lean specs, you will often need to reference these explicitly instead of primitive Lean types (e.g., `usize` -> `Std.Usize`, `u32` -> `Std.U32`).

4. **Implicit Variables in Specs (`result` and `x'`)**
   - `result` is an implicit variable injected by Hermes representing the successful return value of a function.
   - For any mutable reference parameter `x: &mut T`, `x` refers to the variable's state **before** the function executes, while `x'` refers to its state **after** execution. 

5. **Beware "Context" Grepping**
   - You might see `/// context` lines in other Hermes tests. While `context` *is* a valid Hermes keyword, it is used to provide pure Lean setup (like `open Aeneas` or `let limit := 100`), **not** to explicitly bind or declare function parameters for the theorem signature. If you try to write `context val : Type` to force a parameter binding, you will get an `unexpected identifier` parsing error.

## Hermes Annotation Syntax

Hermes specifications are written in standard Rust docile comments using a fenced code block annotated with `hermes` (e.g. ````rust /// ```lean, hermes ````). The parser uses a **line-oriented, indentation-sensitive grammar**. 

### Grammar Rules
1. **Keywords**: Recognized keywords are `context`, `requires`, `ensures`, `proof`, `axiom`, `isValid`, and `isSafe`. They must be the first non-whitespace text on a line.
2. **Indentation (The Off-side Rule)**: When a keyword is encountered, its exact indentation level becomes the baseline. All subsequent lines in that clause *must* be indented strictly more than the baseline.

### Block Types

1. **Safe Verification (`spec` and `proof`)**
   - **Purpose**: Specify behavior for standard Rust functions Aeneas can translate.
   - **Syntax**: `/// ```lean, hermes, spec` (or just `hermes`).
   - **Notes**: You can use implicit variables like `result` (for the return value) and `x'` (for the post-state of a mutable reference `x: &mut T`).
   - **Example**:
     ````rust
     /// ```lean, hermes, spec
     /// requires x > 0
     /// ensures result = x + 1
     /// proof
     ///   simp [add_one]
     /// ```
     pub fn add_one(x: u32) -> u32 { x + 1 }
     ````

2. **Unsafe/Opaque Modeling (`unsafe(axiom)`)**
   - **Purpose**: Axiomatize leaf operations that Aeneas cannot currently translate (like raw pointer manipulation).
   - **Syntax**: `/// ```lean, hermes, unsafe(axiom)`
   - **Notes**: Treats the function as opaque. Aeneas won't generate a body, and Hermes generates a Lean `axiom` trusting the mathematical specification provided. **Buggy `unsafe(axiom)` annotations can lead to unsound programs.**
   - **Example**:
     ````rust
     /// ```lean, hermes, unsafe(axiom)
     /// requires b.val > 0
     /// ensures ret.val = a.val / b.val
     /// ```
     pub unsafe fn safe_div(a: u32, b: u32) -> u32 {
         unsafe { a / b }
     }
     ````

3. **Type Invariants**
   - **Purpose**: Specify internal field invariants for structs.
   - **Syntax**: `/// isValid self := ...`
   - **Notes**: Auto-implements `Hermes.IsValid` for the type. Adds validity requirements to function inputs and validity guarantees to function outputs.
   - **Example**:
     ````rust
     /// ```lean, hermes
     /// isValid self := 2 | self.x.val
     /// ```
     pub struct Even {
         x: usize,
     }
     ````

4. **Trait Invariants**
   - **Purpose**: Designate an `unsafe trait` as a marker/invariant.
   - **Syntax**: `/// isSafe : ...`
   - **Notes**: Requires implementors to prove `isSafe(Self)`, and allows generic functions bounding `<T: Trait>` to rely on `hSafe: isSafe T` in their proofs.
   - **Example**:
     ````rust
     /// ```lean, hermes
     /// isSafe : ...
     /// ```
     pub unsafe trait FromBytes {}
     ````