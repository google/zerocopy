# Hermes Annotation Syntax and Verification

Hermes specifications are written in standard Rust docile comments using a fenced code block annotated with `hermes` (e.g. ````rust /// ```hermes ````). The parser uses a **line-oriented, indentation-sensitive grammar**. 

## Grammar Rules
1. **Keywords**: Recognized keywords are `context`, `requires`, `ensures`, `proof`, `axiom`, `isValid`, and `isSafe`. They must be the first non-whitespace text on a line.
2. **Indentation (The Off-side Rule)**: When a keyword is encountered, its exact indentation level becomes the baseline. All subsequent lines in that clause *must* be indented strictly more than the baseline.

## Block Types

1. **Safe Verification (`spec` and `proof`)**
   - **Purpose**: Specify behavior for standard Rust functions Aeneas can translate.
   - **Syntax**: `/// ```hermes, spec` (or just `hermes`).
   - **Notes**: You can use implicit variables like `ret` (for the return value) and `x'` (for the post-state of a mutable reference `x: &mut T`).
   - **Example**:
     ````rust
     /// ```hermes, spec
     /// requires x > 0
     /// ensures ret = x + 1
     /// proof
     ///   simp [add_one]
     /// ```
     pub fn add_one(x: u32) -> u32 { x + 1 }
     ````

2. **Unsafe/Opaque Modeling (`unsafe(axiom)`)**
   - **Purpose**: Axiomatize leaf operations that Aeneas cannot currently translate (like raw pointer manipulation).
   - **Syntax**: `/// ```hermes, unsafe(axiom)`
   - **Notes**: Treats the function as opaque. Aeneas won't generate a body, and Hermes generates a Lean `axiom` trusting the mathematical specification provided. **Buggy `unsafe(axiom)` annotations can lead to unsound programs.**
   - **Example**:
     ````rust
     /// ```hermes, unsafe(axiom)
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
     /// ```hermes
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
     /// ```hermes
     /// isSafe : ...
     /// ```
     pub unsafe trait FromBytes {}
     ````
