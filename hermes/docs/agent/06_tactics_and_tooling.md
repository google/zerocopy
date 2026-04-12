# Module 6: Tactics and Tooling

While Anneal completely abstracts the boilerplate of theorem generation, you still need to write the mathematical proofs for your `requires` and `ensures` bounds. 

This module serves as a survival dictionary for the most common Lean 4 tactics and Aeneas APIs you will encounter.

## 1. The Core Tactics

### `scalar_tac`
This is Aeneas's custom arithmetic solver, and arguably the most important tactic in Anneal. 
*   **What it does:** It automatically proves linear arithmetic inequalities and equalities involving bounded integers (e.g., `Usize.val ≤ Usize.max`). It natively understands the `.val` unwrapping of Aeneas primitives.
*   **When to use it:** Almost constantly. If a bound is purely arithmetic (e.g., proving an index is within a slice length, or an offset doesn't overflow `isize`), `scalar_tac` solves it.
*   **Limitations:** It only handles linear arithmetic (addition, subtraction, multiplication by constants). If your proof involves non-linear arithmetic (like `x * y > z` or modulo operations), `scalar_tac` will fail and you must manually apply algebraic theorems before calling it.

### `simp_all`
The "simplify all" tactic.
*   **What it does:** It aggressively applies all known `@[simp]` lemmas in the environment to simplify your goal and your hypotheses, and attempts to close trivial goals.
*   **When to use it:** When setting up a custom lemma or when you need to unroll complex structure definitions into simpler boolean propositions.

### `intro`
*   **What it does:** When your goal is a function or an implication (e.g., `A → B`), `intro x` takes `A` from the goal, assumes it is true, and adds it to your local context as hypothesis `x`, leaving `B` as the new goal.
*   **When to use it:** Primarily when writing custom lemmas or manual WP progress proofs that involve implications, or when unpacking the `Option`/`Result` matching logic. (Note: You do not need `intro` for your preconditions; Anneal natively destructured them into your context using `rcases`).

### `eval_progress` / `progress`
*   **What they do:** These tactics "step" through the Aeneas Weakest Precondition (WP) evaluator. If you have a sequence of statements in a function, `progress` handles the WP extraction to move execution to the next line of code.
*   **WARNING IN ANNEAL:** Due to Orthogonal WP (see Module 5), the progress goal evaluates entirely independently from your correctness `proof:` blocks, using the generated `eval_progress` tactic. You cannot use `progress` inside a Correctness proof because the WP state is already destructured. If `eval_progress` fails to automatically discharge the Progress goal, you must manually use `progress` inside an explicit `proof (h_progress):` block.

## 2. Tactic Combinators

### `<;>` (The "And Then" Combinator)
You will often see tactics chained together like `cases x <;> simp_all`.
*   **What it does:** `A <;> B` applies tactic `A` to the current goal. If `A` splits the goal into multiple subgoals (like branching on an `if` statement or an `enum`), it then immediately applies tactic `B` to **every single resulting subgoal**.
*   **Why it's powerful:** It instantly prunes impossible error states. If you split a `Result` into `.ok` and `.fail`, running `<;> simp_all` will usually instantly solve and close the impossible `.fail` branch, leaving you to focus solely on the `.ok` branch.

## 3. Essential Aeneas APIs

When writing specifications, you will inevitably interact with definitions from Aeneas's standard library.

### `Usize` Bounds for Slices
*   **What it is:** While purely mathematical arrays might be indexed with strictly bounded types (like `Fin n`), Aeneas models Rust slice and array indices natively using machine integers (e.g., `Usize`).
*   **Why it matters:** When indexing into a slice, Aeneas enforces the bounds logically via function preconditions (e.g., `0 <= i.val` and `i.val < slice.length`) rather than at the type level. You use `scalar_tac` to transparently discharge these bound assertions.

### `Aeneas.Std.bind_tc_ok`
*   **What it is:** A fundamental `@[simp]` theorem in Aeneas (`(do let y <- .ok x; f y) = f x`).
*   **Why it matters:** If you are forced to manually step through a monadic sequence, `bind_tc_ok` simplifies the bind operation downward *after* you have already proven that the preceding statement evaluated to `.ok`. It allows you to seamlessly "fast-forward" the simulated execution.

### `spec_imp_exists`
*   **What it is:** A foundational `theorem` (`Aeneas.Std.WP.spec_imp_exists`) for Weakest Preconditions.
*   **Why it matters:** When resolving the Orthogonal WP Progress goal, you must prove that there *exists* a valid return value `y` such that `test = ok y`. This theorem converts standard WP `spec` constraints into the existential proof required to close that goal.

## 4. Troubleshooting: Exhaustion vs Syntax

If a proof compilation fails, you must immediately diagnose whether it is a **solver exhaustion** or a **syntax error**.

**Solver Exhaustion (`autoParam` failure):**
*   **Symptom:** The error output complains about `autoParam` failing, or says something like *"Missing explicit proof for named bound... Lean cannot automatically prove that this value satisfies the `isValid` type invariant."*
*   **Cause:** The Anneal auto-solver (`verify_user_bound` or `verify_is_valid`) attempted to use `scalar_tac` and `simp_all`, but got stuck. 
*   **Fix:** You must provide a manual `proof (bound_name):` block to hold Lean's hand through the logic.

**Syntax / Tactic Errors:**
*   **Symptom:** The error points specifically at a line *inside* your `proof:` block and complains about "unknown identifier", "unexpected token", or "tactic failed".
*   **Cause:** You wrote invalid Lean syntax, you used a tactic that doesn't apply to the current goal state (like `progress` inside a correctness block), or your Python-string indentation is incorrect.
*   **Fix:** Fix the syntax. Remember that `--allow-sorry` will **not** save you from these errors. If you just want to skip the failing proof entirely, you must delete the entire `proof:` block.
