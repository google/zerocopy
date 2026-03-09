# Hermes Syntax Reference

Hermes specifications are written inline in Rust doc comments using fenced code blocks: `/// ```hermes`.

## Syntax

Hermes annotations are a sequence of indentation-sensitive (Python-style) blocks:

````rust
/// ```hermes
/// requires: x > 0
/// ensures:
//     ret = x + 1
/// proof:
///   ...
/// ```
````

## Block Types

The full list of blocks is:
- `context`: Context used by all blocks
- `requires`: Pre-conditions
- `ensures`: Post-conditions
- `proof context`: Lemmas or other items used by multiple proofs
- `proof`: Proofs of post-conditions
- `isValid`: Type invariants
- `isSafe`: Trait invariants

## Named and Anonymous Bounds

`requires`, `ensures`, and `proof` define or discharge bounds. They can be anonymous or named:

````rust
/// ```hermes
/// requires (h_x_pos): x > 0
/// requires (h_even): x % 2 == 0
/// ensures: ret = x + 2
/// proof:
///   ...
/// ```
````

Bounds are namespaced to either pre-conditions or post-conditions. An anonymous proof is combined with an anonymous post-condition.

## `isValid` and `isSafe`

`isValid` defines invariants for a type. Its syntax is a (boolean) Lean function:

````rust
/// ```hermes
/// isValid self := self.x.val > 0
/// ```
````

`isSafe` defines invariants for an unsafe trait.

````rust
/// ```hermes
/// isSafe : 
///   ∀ (self : Self), True
/// ```
````

## Axioms

A specification can be axiomatic, in which case a proof is not given. Note the `unsafe(axiom)` token.

````rust
/// ```hermes, unsafe(axiom)
/// requires: b.val > 0
/// ensures: ret.val = a.val / b.val
/// ```
pub unsafe fn safe_div(a: u32, b: u32) -> u32 { unsafe { a / b } }
````

## Implicit Variables

**`ret`**: The return value of the function, assuming it returns (doesn't panic or loop forever).

**`arg'`**: The value of the referent of a mutable reference `arg: &mut T` after the function returns.

## Implicit Bounds & Hypotheses

Hermes automatically defines or injects the following structural names.

**`h_unnamed`**: The singleton name assigned to an anonymous `requires` or `ensures` block. These are namespaced to either pre-conditions or post-conditions, so they don't conflict.

````rust
/// ```hermes
/// requires: x > 0        -- Named `h_unnamed`
/// ensures: ret = x + 1   -- Named `h_unnamed`
/// proof:                 -- Proves `h_unnamed`
///   ...
/// ```
````

**`h_<arg>_is_valid`**: An auto-injected precondition asserting that the argument `arg` satisfies its type invariant (`isValid`).

````rust
/// ```hermes
/// requires (h_x_is_valid): isValid x -- Don't actually write this; it's implicit
/// ```
fn foo(x: MyType) {}
````

**`h_<arg>'_is_valid`**: An auto-injected postcondition asserting that a mutable reference `arg` satisfies its type invariant after the function returns.

````rust
/// ```hermes
/// ensures (h_x'_is_valid): isValid x' -- Don't actually write this; it's implicit
/// proof (h_x'_is_valid):
///   ... -- Prove the postcondition
/// ```
fn foo(x: &mut MyType) {}
````

**`h_ret_is_valid`**: An auto-injected postcondition asserting that the return value satisfies its type invariant.

````rust
/// ```hermes
/// proof (h_ret_is_valid):
///   ...
/// ```
fn foo() -> MyType {}
````

**`h_progress`**: The statement that the function terminates without panicking.

````rust
/// ```hermes
/// proof (h_progress):    -- Prove execution doesn't fail (e.g. divide by zero) or loop forever
///   ...
/// ```
fn safe_div(x: u32, y: u32) -> u32 {} 
````

**`h_returns`**: The hypothesis binding the successful evaluation of the function to the implicitly-available values `ret`, `arg'`, etc.

````rust
/// ```hermes
/// ensures (h_res): ret = x + y
/// proof (h_res):
///   -- `h_returns` is in scope here
///   ...
/// ```
pub fn add(x: u32, y: u32) -> u32 { x.wrapping_add(y) }
````

Because we prove progress and correctness separately, our correctness proof is *actually* a proof of correctness *conditional on progress*. `h_returns` is this condition: it asserts that the function call successfully evaluated to the values available in the proof context (`ret`, `x'`, etc.).

The values available in the proof context are automatically destructured for you:
*   `ret`: The final return value of the function.
*   `x'`, `y'`, etc.: The post-states of any mutable references passed to the function.
