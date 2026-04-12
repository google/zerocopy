# Module 5: Proof Architecture

The biggest conceptual hurdle in Anneal is understanding *how* your proofs are mathematically structured and evaluated. 

If you try to write proofs by blindly guessing tactics, you will fail. You must understand the engine. This module explains the "Orthogonal WP" architecture and the strict "Term Mode" hygiene rules that govern Anneal proofs.

## 1. Orthogonal WP Proofs

Aeneas generates verification goals using **Weakest Preconditions (WP)**. In a standard WP framework, you step through the execution of a function line-by-line. If the execution gets "stuck" (e.g., you can't prove a loop terminates or a division is safe), the entire proof halts. 

Anneal uses a custom architecture called **Orthogonal WP**.

Orthogonal WP mathematically decouples the proof into two completely independent goals:
1.  **Progress (`h_progress`):** Proving that the `Result T` successfully resolves to `.ok` (i.e., the function doesn't panic, loop forever, or violate Rust rules).
2.  **Correctness (`h_returns`):** Proving that the *returned values* satisfy your `ensures` bounds and `isValid` invariants.

**Why is this important?** 
Because they are orthogonal, *Anneal allows you to write the correctness proof even if the progress proof fails.* This means that missing termination proofs no longer block you from verifying your actual logical invariants.

## 2. The Verification Environment

When Anneal generates a theorem for your function, it sets up an incredibly convenient environment for you before your custom `proof context:` even begins. 

You do not start with a blank slate. Anneal automatically performs:

### State Setup (`Pre`)
Anneal aggregates all your `requires` bounds, `unsafe(axiom)` traits, and implicit type invariants into a `Pre` struct. It then automatically destructured this struct via an `rcases` tactic.
**Result:** Every named precondition (e.g., `h_x_positive`) is immediately available as a free variable in your local Lean context. You do not need to use `intro` to bring preconditions into scope.

### State Capture (`h_returns`)
Anneal intercepts the final execution tuple (which contains both the standard return value and the post-state of all mutated `&mut` borrows) and binds it.
**Result:** Mutated inputs are available as `var'` (e.g., `x'`), and the final return value is available as `ret`. 

> [!TIP]
> **Zero-Sized Return Optimization:** If your function returns `()` or `!`, Anneal completely eliminates `ret` from the environment. There is no `ret` variable to prove things about!

## 3. The `Post` Struct

When you provide a manual proof for a named bound, you write it in a block like this:
```rust
/// ```anneal, proof
/// proof (h_my_bound):
///   scalar_tac
/// ```
```

Internally, Anneal aggregates all your postconditions and invariants into a struct called `Post` containing proofs of all post-conditions. Your proof blocks are literally injected into the `exact { ... }` instantiation of this struct using `:= by`.

```lean
-- Conceptual Anneal internal structure
exact {
  h_ret_is_valid := by verify_is_valid ...
  h_my_bound := by <YOUR PROOF TEXT HERE>
}
```

Because Anneal separates *progress* and *correctness* proofs, **you cannot use `progress` or `eval_progress`** inside these fields.

## 4. Omitting Proofs

Anneal provides `autoParam` macros that automatically attempt to solve missing proofs (e.g., `verify_is_valid`, `verify_user_bound`). If you do not provide a `proof:` block for an `ensures` clause, Anneal uses these macros to try `simp_all` and `scalar_tac` for you.

### The `--allow-sorry` Trap

You can run Anneal with `--allow-sorry` to temporarily skip failing proofs. 

**Understand exactly what this does:** It simply configures the `autoParam` macros to degrade to a `sorry` axiom if they fail. 

**What it does NOT do:** It does *not* magically silence syntax errors or broken logic in your manual `proof:` blocks. If you write:
```rust
/// ```anneal, proof
/// proof (foo):
///   some_garbage_tactic_that_doesnt_exist
/// ```
```
This will *still fail to compile* even with `--allow-sorry`. 
