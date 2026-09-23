# Anneal: Named Preconditions and Postconditions

## Motivation

Verification tools are fundamentally in the business of composing logical requirements. A function might require that its input parameter `x` is greater than zero, and additionally require that `x` is a valid memory address. Similarly, it might ensure that its return value is bounded, and additionally ensure that any mutable references it borrowed remain valid post-execution.

A naive approach to this requirement – and the one taken by earlier versions of Anneal – is to model these composed requirements using implicit, anonymous logical conjunctions (`∧`). If a user wrote `requires: x > 0` and the system injected a type invariant `isValid x`, the resulting theorem signature would quietly bundle them: `h_req : (IsValid x) ∧ (x > 0)`.

While mathematically sound, this anonymous tuple design created unacceptable friction for developers:

1. **Opaque Invariants:** When an auto-injected constraint (like `isValid`) failed, the Lean compiler would emit a generic "unsolved goals" error pointing at a giant logical AND chain. Users were left guessing which invisible constraint actually broke the build.
2. **"Tuple" Combinatorics:** When a user needed to manually prove a specific clause, they had to mentally and syntactically destructure `A ∧ (B ∧ C)`.
3. **Clunky & Brittle Tactics:** To leverage a specific precondition in a proof, a user had to traverse a positional tree (e.g., `h_req.right.left`). If a new constraint was added (perhaps due to a struct gaining a new field), the entire tree shifted, breaking unrelated proof paths globally.

Named Bounds is the architectural redesign that solves this. By elevating every constraint — whether authored by the user or dynamically injected by Anneal — into explicitly named, structurally addressable propositions, we achieve a system that is transparent upon failure, resilient to change, and robust enough to support isolated subset evaluation.

## Design Criteria

The Named Bounds architecture was engineered to satisfy six criteria:

1. **The Anonymity Principle:** A user should *never* have to guess the name of an anonymous proposition. If a bound is unnamed, the system must either prove it invisibly or provide a stable, explicitly authored name. The only exception is obvious and predictable names for injected type bounds (e.g., `h_x_is_valid`).
2. **Independent Evaluation (The Subset Problem):** If a function has $N$ obligations (e.g., 3 postconditions and 1 `isValid` bound), and the user provides proofs for $N-1$ of them, the system *must* evaluate the $N-1$ proofs independently. It cannot fail the entire function's verification simply because one proof is missing. Users must get targeted feedback strictly on the unproven $N^{th}$ obligation.
3. **Graceful Degradation (`--allow-sorry`):** The system must support rapid prototyping by allowing unproven bounds to fall back to `sorry`. Crucially, this degradation must be *resilient*: it should not blindly `sorry` the entire function and mask genuine Lean syntax or semantic errors in the proofs the user *did* write.
4. **Structural Resilience (Order Independence):** Adding, removing, or reordering a `requires` or `ensures` clause must not break unrelated proof blocks due to positional shifting.
5. **Context Hygiene:** Shared setup logic (e.g., in a `proof context:` block) must be strictly isolated from the global goal state. Users must be able to define intermediate bindings without accidentally employing unhygienic tactics (like `simp_all` or `unfold`) that could unpredictably corrupt sibling proof branches.
6. **Orthogonality of Progress and Correctness:** "Progress" (the existential proof that the execution yields a valid result) and "Correctness" (the logical predicates constraining the output state) must be treated as independent obligations. A stuck execution step (WP) must not destroy the granular diagnostics of the postconditions.

## Technical Sandbox: How Named Bounds Work

To satisfy the criteria above, Anneal completely abandons logical conjunctions in favor of **Lean 4 Structures** combined with **Term-Mode Instantiation** and **`autoParam` macros**.

### 1. Surface Syntax (`.rs` blocks)
The Anneal grammar allows users to optionally name their `requires` and `ensures` statements.

```rust
/// ```anneal
/// requires (h_positive): x > 0
/// ensures (h_incremented): ret == x + 1
/// ```
```
*Note: All section headers (e.g., `requires`, `ensures`, `proof`) must be followed by a colon (`:`).*

### 2. Translating Preconditions (`structure Pre`)
To satisfy **Structural Resilience**, Anneal isolates all precondition requirements (both user-defined `requires` and injected `isValid` bounds) into a dedicated Lean structure named `Pre`.

```lean
namespace func
  structure Pre (x : Std.U32) : Prop where
    h_x_is_valid : Anneal.IsValid.isValid x
    h_positive   : x > 0
end func

theorem spec (x : Std.U32) (h_req : func.Pre x) : ...
```

**Implications:**
- **Order Independence for Callers:** When a developer calls this verified function inside a proof, they instantiate the requirements using a named record: `exact { h_positive := ..., h_x_is_valid := ... }`. They do not need to memorize positional ordering.
- **Ergonomics:** At the start of the generated proof block, Anneal automatically unpacks the struct (`rcases h_req with ⟨...⟩`), bringing every precondition (like `h_positive`) directly into the local tactic scope as a named hypothesis.

### 3. Translating Postconditions (`structure Post`)
Postconditions and output `isValid` bounds are equally encapsulated inside a generated `Post` structure.

```lean
namespace func
  structure Post (x ret x' : Std.U32) : Prop where
    h_x'_is_valid  : Anneal.IsValid.isValid x'
    h_ret_is_valid : Anneal.IsValid.isValid ret
    h_incremented  : ret = x + 1
end func
```

This ensures that if verification fails, the Lean compiler highlights the specific missing field (e.g., `h_ret_is_valid : IsValid ret`) rather than a giant logical tuple.

### 4. Independent Subset Evaluation via `exact {}`
A Weakest Precondition (WP) in Aeneas accepts a single, monolithic lambda to evaluate post-states: `(fun (ret, x') => Post x ret x')`. To satisfy the **Independent Evaluation** criterion, Anneal cannot simply build a tree of `constructor` tactics, because a failure in one branch halts execution of subsequent branches.

Instead, Anneal synthesizes a single `exact { ... }` block to instantiate the entire `Post` struct simultaneously.

```lean
-- ... inside the theorem ...
exact {
  h_incremented := by
    -- User's `proof (h_incremented)` block gets injected perfectly here!
    omega
  -- Notice that `h_ret_is_valid` is intentionally missing ...
}
```

**The Magic of `autoParam`:**
If the user provides a `proof (h_incremented):` block, Anneal drops it directly into the `h_incremented` field of the `exact` instantiation. If the user *omits* a proof for an injected bound (like `h_ret_is_valid`) or a user-defined bound, Anneal simply omits that field from the instantiation entirely.

Because the Lean `Post` structure defines these fields with a default `autoParam` macro (`verify_is_valid` for injected bounds, and `verify_user_bound` for user bounds), Lean will automatically attempt to execute a chain of tactics (`simp_all`, `subst_eqs`, `scalar_tac`, `omega`, etc.) behind the scenes to close the omitted field. If it succeeds, the user is completely shielded from trivial proofs. If it fails, Lean throws a custom error precisely at the missing field, prompting the user for an explicit `proof:` block.

### 5. Context Hygiene (`proof context:`)
Sometimes, users need to perform intermediate shared setup before branching off into their individual named proofs.

```rust
/// ensures (h_pos): ret > 0
/// ensures (h_even): ret % 2 == 0
/// proof context:
///   have h_shared : ret = 2 := by simp [foo]
/// proof (h_pos): ...
/// proof (h_even): ...
```

To satisfy **Context Hygiene**, Anneal injects `proof context:` directly into Lean's **Term Mode**, immediately before the `exact` struct initialization:

```lean
exact
  have h_shared : ret = 2 := by simp [foo]
  {
    h_pos := by ...
    h_even := by ...
  }
```

Because this evaluates in Term Mode (rather than as an open tactic block), unhygienic commands like `unfold` or `simp_all` are illegal. Users can only define localized bindings (`have`, `let`), guaranteeing that shared setup cannot accidentally manipulate or corrupt the global goal state of sibling branches.

### 6. The Orthogonal WP Architecture
The final major leap in the Named Bounds design solves the stuck WP problem.

Standard Aeneas Weakest Preconditions (`WP.spec m P`) evaluate two things simultaneously:
$$(\exists y, m = .ok\ y) \land (\forall y, m = .ok\ y \implies P\ y)$$

Previously, if "Progress" (the existential proof `∃ y, m = .ok y`) stalled due to an opaque execution step, it killed the entire WP compilation, completely destroying the granular evaluations of the `Post` struct fields.

To satisfy the **Orthogonality of Progress and Correctness**, Anneal completely divorces these two branches natively using the `wp_prove_orthogonal` theorem:

```lean
-- Generated by Anneal
apply wp_prove_orthogonal
· -- Goal 1: Progress
  eval_progress "Execution stalled..."
· -- Goal 2: Correctness
  intro y hy
  exact { ... } -- The Post struct evaluates safely here!
```

**Implications:**
1. **Targeted Failure:** If tracking execution stalls, `eval_progress` cleanly fails on Goal 1, completely isolating the failure.
2. **Correctness Survival:** Because Goal 2 binds the output `y` unconditionally into the local context, the type of the `Post` struct is mathematically rigorous and fully known by Lean. The `exact { ... }` block natively compiles and evaluates subset bounds (Goal 2) *even if Goal 1 is stuck*.
3. **Explicit Progress Proofs:** Because Progress is now an orthogonal property, users can explicitly resolve execution limits by providing a `proof (h_progress):` block (where unhygienic tactics like `progress` and `unfold` are allowed natively).

### 7. Resiliency and `--allow-sorry`
When running with the `--allow-sorry` flag, the `autoParam` macros (`verify_is_valid` and `verify_user_bound`) dynamically look up the `Anneal.allow_sorry` axiom, which Anneal defines only when `--allow-sorry` is passed.

If it exists, omitted bounds gracefully fallback to `sorry`, emitting localized warnings. However, because Anneal natively respects the **Independent Evaluation** constraint through struct fields, if a user *does* provide an explicit proof script for a field, that script completely overrides the default `autoParam`. As a result, genuine Lean syntax or semantic errors in the user's explicit proofs are *never* squashed or bypassed by the `--allow-sorry` safety net, and still cause verification to fail.

### 8. The Singleton Unnamed Proposition
To honor the **Anonymity Principle**, Anneal does not rely on auto-generated names (like `unnamed_1`) if a user writes an anonymous bounds clause.

Instead, the AST formally models anonymous user clauses as a **singleton proposition** via the reserved name `h_anon`. There can only ever be exactly one anonymous `requires` and one anonymous `ensures` per function.

If a user writes a lone `proof:` block, Anneal routes it directly to the `h_anon` field behind the scenes. Lean's diagnostic strippers then intercept any failures tagged with `h_anon` and present them back to the user plainly as "Your anonymous ensures clause failed to verify." Callers never guess names; they just map the single anonymous constraint natively.

## Future Work

1. **`h_anon` Diagnostic Stripping:** When a user provides exactly one unnamed constraint, Anneal encapsulates it as `h_anon`. If the user's unnamed `proof` fails to solve it, Lean outputs: `Unsolved goal for h_anon`. Seeing this internal implementation detail in an error confuses users. Future iterations of Anneal should intercept goals tagged with `h_anon` and strip the name from the diagnostic: *"Your anonymous ensures clause failed to verify"*.

## Appendix: Technical Implementation & Edge Cases

The following details the specific diagnostic mappings, AST validation checks, and advanced Orthogonal WP limitations implemented by the Named Bounds architecture.

### 1. Diagnostic Mapping & Error Attribution

To ensure users are never left deciphering cryptic Lean compiler errors resulting from Anneal's structural scaffolding, Lean's `exact {}` structural instantiation and Anneal' custom `autoParam` macros handle interceptive diagnostic mapping natively.

*   **Injected Bound Failures (`isValid`):** If a user returns `&mut T` but provides zero `ensures` clauses, Anneal omits the `h_arg'_is_valid` field inside the `exact {}` instantiation. Lean's `autoParam` triggers `verify_is_valid`. If this fails to find a trivial proof (via `simp_all`), Lean emits a primary error: `could not synthesize default value for field 'h_arg'_is_valid'`. The custom `verify_is_valid` macro intercepts this and surfaces a secondary error message indicating exactly which invariant failed, advising the user to provide a manual `proof ({name}):` for it.
*   **Missing Named Proofs & Automatic Fallbacks:** If a user writes `ensures (A)` but omits `proof (A)`, Anneal allows this to fall through to the Lean structural instantiation layer. Lean's `verify_user_bound` `autoParam` will actively attempt to solve the bound using a combination of `simp_all`, `scalar_tac`, and `omega`. If the goal is too complex and the auto-proving fails, the macro intercepts the failure and emits a custom diagnostic: `Missing explicit proof for named bound A.`.
*   **Mismatched Proof Names:** If a user writes `ensures (h_foo)` but later writes `proof (h_bar)`, Anneal catches this at the Rust AST stage before generating Lean, panicking statically: *"Validation Error: You provided a proof: for `h_bar` but no such constraint exists."*
*   **Duplicate Clause Naming:** Anneal statically asserts that all names provided across `requires` and `ensures` for a single function are strictly globally unique, panicking at the Rust level on collisions.

### 2. Dummy Field Leakage (The `h_anon` Singleton)

When a user provides exactly one unnamed constraint alongside an injected `isValid`, Anneal encapsulates it cleanly in the structures via the dummy field `h_anon`.

```lean
namespace func
  structure Post (x ret x' : Std.U32) : Prop where
    h_x'_is_valid  : Anneal.IsValid.isValid x'   -- Auto-injected &mut param
    h_anon      : ret > 0                        -- User's single anonymous clause
end func
```

### 3. Advanced Limitation: WP Spec Extraction under Orthogonal Progress

A highly specific side-effect of the Orthogonal Architecture is that **the Aeneas `progress` tactic cannot be used inside `proof context:` blocks.**

`proof context:` evaluates on the **Correctness** branch (Goal 2), *after* the WP has already been split. This means the target hypothesis `h_ret_` locally available in `proof context:` is not a Weakest Precondition (`WP.spec`); it is a direct equality (e.g., `test_func = ok ret_`).

Because `progress` specifically targets and evaluates WPs, using `progress` inside `proof context:` to extract sub-calls will fail.

```rust
// THIS FAILS because `progress` requires a WP target
/// proof context:
///   progress as ⟨ ret_val, h_valid ⟩
```

**Workaround (Relocate to `proof (h_progress)`):**
Users must relocate `progress` and other tactic operations to the strictly orthogonal `proof (h_progress):` block, which natively supports tactic mode evaluation for Weakest Preconditions, or to the specific `proof (field):` branch where the values are needed.

```rust
/// proof (h_progress):
///   unfold parent_func at *
///   progress as ⟨ ret_val, h_valid ⟩
///   unfold parent_func at h_ret_
///   simp_all [parent_func, sub_func]
```

### 4. Evaluation Order of `proof context` vs Preconditions

Because `proof context:` is evaluated directly within the structural instantiation (`exact`), it evaluates *after* the WPs are split, which critically means it evaluates *after* the preconditions (`Pre` struct) have been destructured (`rcases h_req with ⟨...⟩`) by the global theorem signature.

This means that `proof context:` logic has full access to the user-defined preconditions (like `h_positive`). Users can safely and ergonomically use their `requires` hypotheses to build shared setup logic for their `ensures` proofs.

### 5. Zero-Sized Returns (`Unit` and Diverging `!`)

Anneal employs a structural optimization when dealing with functions that return `()` (Unit) or `!` (diverging/Never). Because a `Unit` or `Never` return value contains no state worth bounding or evaluating, Anneal optimizes the `Post` struct by omitting the `ret` parameter entirely.

Instead of an `exact {}` assignment mapping to fields, Anneal emits `exact ⟨⟩` to instantly discharge the empty `Post` structure, preventing the proof context from being cluttered with `ret : Unit` or `ret : Never` bindings.

**Why Special-Casing Zero-Sized Returns is Required**

While it may seem architecturally cleaner to treat `Unit` and `!` symmetrically with all other return types (i.e., by always generating a `ret` parameter and forcing the user to supply `h_ret_is_valid` or allowing it to be inferred automatically), doing so creates catastrophic friction with Aeneas and Lean's type theory:

1. **Aggressive `Unit` Tuple Elision:** When a function returns `()` but mutates arguments (e.g., `fn foo(x: &mut u32)`), Aeneas's LLBC translation does *not* generate `Result (Unit × U32)`. It elides the mathematically useless `Unit` entirely, emitting just `Result U32`. If Anneal blindly generated `structure Post (ret: Unit)`, its structural destructuring (`let (ret, x') := ret_`) would instantly fail type-checking. Anneal would be forced to reverse-engineer Aeneas's tuple elision rules and synthesize `let ret := ()` out of thin air to satisfy the struct.
2. **Asymmetric Translation of `!`:** While Aeneas elides `Unit` from mutated tuples, it *preserves* `Never`. For `fn never_mut_ref(x: &mut u32) -> !`, Aeneas uniquely generates `Result (Never × U32)` because the presence of `Never` renders the entire tuple uninhabited. To be consistent with Aeneas's behavior for *both* `()` and `!`, Anneal would have to implement deep, fragile logic to track this asymmetry perfectly in sync with Aeneas.
3. **Loss of the `exact ⟨⟩` Optimization:** By formally dropping `ret: Unit` and its bound, standard `fn foo()` functions result in a completely empty `Post` struct. This unlocks the structural `exact ⟨⟩` shortcut, instantly proving the Correctness goal without bloating the proof context. Keeping `Unit` would force Anneal to bloat every void function in a project with useless `exact { ret := (), h_ret_is_valid := by verify_is_valid }` assignments.
