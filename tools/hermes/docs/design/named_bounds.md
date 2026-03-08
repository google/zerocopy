# Hermes: Named Preconditions and Postconditions

## Background & Motivation

Without named bounds, Hermes would have to rely on implicit, anonymous conjunctions (`∧`) to compose multiple requirements for a function (and in fact, it did prior to this design). This applies to explicit user specifications (`requires` and `ensures`) as well as auto-injected type invariants (e.g., `isValid`).

While mathematically sound, an anonymous design creates significant friction:
1. **OPAQUE INVARIANTS**: When a function accepts or returns types implementing `isValid`, the system invisibly bounds them via `∧`. When a proof fails due to an injected invariant, the Lean error (`unsolved goals`) is confusing, leaving users wondering where the extra constraint came from.
2. **"TUPLE" COMBINATORICS**: Lean's error messages present a giant logical `AND` chain. Users must mentally destructure `A ∧ (B ∧ C)` to understand which constraint actually failed.
3. **CLUNKY TACTICS**: To leverage a specific `requires` clause in a proof, a user might have to traverse a tree (e.g., `h_req.right.left`). If a new constraint is added, the structure shifts and breaks the brittle access path.

Hermes solves this by designing a system where invariants and constraints are explicitly named in the output Lean context, remaining **low-impact** for trivial cases while providing complete **transparency** when things go wrong.

### The Anonymity Principle

A core principle of this design is that **the user should never have to know or guess the names of anonymous predicates.** 
If a user writes an anonymous condition (or if Hermes injects one invisibly), the system must either:
1.  Allow the user to prove it without naming it (e.g., via a single unambiguous anonymous proof, or a monolithic `simp_all`).
2.  Provide a clear, stable name that the user explicitly authored themselves.

**Exception (`isValid` Invariants):** Auto-injected type bounds like `isValid` are exempt from this rule because they follow a strict, mathematically predictable naming scheme (e.g., `h_x_is_valid` for an input `x`, `h_x'_is_valid` for `&mut x`'s post-state, and `h_ret_is_valid` for the return value). Users *can* and *should* target these names in `proof` blocks when `simp_all` fails.
 
If there are *multiple* anonymous user-defined predicates in a context, we cannot simply auto-generate names (like `unnamed_1`, `unnamed_2`) and expect the user to guess them in a proof. If a user needs to write isolated, granular proofs for multiple conditions, they MUST name those conditions.

---

## Design: Named Conjuncts

### 1. Surface Syntax Changes (Rust `hermes` block)
The Hermes grammar supports optional names for `requires` and `ensures` statements. If a name is missing, an anonymous name is mapped internally.

**Syntax Pattern:**
`[keyword] [(name)]: [expression]`

**Examples:**
```rust
/// ```hermes
/// requires (h_positive): x > 0
/// requires (h_less_than): x < 100
/// ensures (h_incremented): ret == x + 1
/// ```
```
*Note: All section headers (e.g. `requires`, `ensures`, `proof`, `proof context`, `context`, `axiom`) MUST be followed by a colon (`:`). The only exceptions to this rule are the `isValid` and `isSafe` bounds.*

### 2. Translating Preconditions (`requires` & Input `isValid`)
Preconditions are incredibly straightforward to unbundle because Lean supports naming multiple hypotheses explicitly in the theorem signature.

**`structure Pre`**
To ensure that callers of a function have an ergonomic, order-independent way to prove preconditions without relying on giant logical tuples (`A ∧ (B ∧ C)`), Hermes generates a custom Lean `structure` that encapsulates the preconditions as named fields.

```lean
namespace func
  structure Pre (x : Std.U32) : Prop where
    h_x_is_valid : Hermes.IsValid.isValid x
    h_positive   : x > 0
    h_less_than  : x < 100
end func

theorem spec (x : Std.U32) (h_req : func.Pre x) : ...
```

**Note on Empty Structures:** 
If there are zero conditions to require or validate for a function (e.g., zero arguments, zero implicit `isValid` derivations, and zero user `requires` blocks), the `Pre` structure is entirely omitted, and the theorem signature skips the `pre` argument. In practice, because almost every function has inputs, and `isValid` is unconditionally generated for all inputs (even those with trivial `True` types), the `Pre` structure is almost always generated.

**Note on Zero Postconditions:**
If a function returns `()` (or `Unit`), has zero mutable reference inputs, and specifies zero user `ensures` clauses, an empty `Post` structure (without any fields) is emitted. Hermes uniformly instantiates it using `exact {}` for the Aeneas WP lambda predicate, establishing a highly consistent structural blueprint across all output.

**Usage by Callers (Lemma Applications):**
Because `Pre` is a standard Lean structure, a user calling a verified sub-function inside a proof context will need to construct it explicitly. 
For example: `have h_call := other_func_spec x { h_x_is_valid := ..., h_positive := ... }`. 
By relying on idiomatic Lean struct instantiation via `⟨h1, h2⟩` or named `{ field := val }`, we can make these applications robust without building complex macros.

**Benefits:**
- **Order Independence for Callers:** When a user calls this function and must prove its preconditions, they can construct the `Pre` structure explicitly (`exact { h_positive := ..., h_less_than := ... }`) or use the `constructor` tactic. They do not need to memorize the positional order of Hermes's auto-injected bounds versus user bounds.
- **Anonymity Principle Preserved (The Singleton Unnamed Proposition):** The system completely abandons positional, algorithmic unnamed fields (`unnamed_1`, `unnamed_2`). Instead, it formally models anonymous user clauses as a **singleton proposition** via the reserved name `h_unnamed`. There can only ever be exactly one anonymous `requires` and exactly one anonymous `ensures` per function. Callers never guess numeric identifiers; they just map the single anonymous constraint natively.

**Benefits:**
- **Instant Recognition:** If an input invariant fails statically, or the user is interacting with the Lean environment, their context cleanly spells out `h_x_is_valid : Hermes.IsValid.isValid x`. It prevents user requirements from being cluttered.
- **Ergonomics:** Hermes automatically destructures the `Pre` struct at the start of the generated proof block using `rcases h_req with ⟨...⟩`. This brings every precondition directly into the local tactic scope, allowing users to reference named preconditions cleanly (e.g., `h_positive`) in their proofs instead of performing manual field accesses (`h_req.h_positive`) or playing guessing games with anonymous tuple `.left` and `.right` accessors.

### 3. Translating Postconditions (`ensures` & Output `isValid`)
Postconditions are more difficult to unbundle. We depend on Aeneas' Weakest Precondition (WP) framework, which expects a single predicate function `(fun ret => ...)`. We cannot easily rewrite the signature of `Aeneas.Std.WP.spec` to accept multiple distinct ensure clauses.

We have a few options to make postconditions transparent.

#### Custom Generated Structures (Records)
We generate custom Lean `structures` for post-conditions.

For every function, Hermes generates a custom Lean `structure` that encapsulates the postconditions as named fields. To avoid polluting the global Lean namespace, these structures are emitted within a `namespace <func_name>` block.

```lean
namespace func
  structure Post (x ret x' : Std.U32) : Prop where
    h_x'_is_valid  : Hermes.IsValid.isValid x'
    h_incremented  : ret = x + 1
end func

```lean
-- Aeneas usage:
Aeneas.Std.WP.spec (func x) (fun (ret, x') =>
  func.Post x ret x'
) := by ...
```

**Destructuring the Return Tuple:**
Aeneas models state-updating transformations (like `&mut T` or returns) by yielding a tuple from the forward function containing the return value and updated mutable references. Hermes synthesizes a destructuring lambda `fun (ret, x') =>` for the WP spec, and introduces them via `intro (ret, x') h_ret_` on the second goal of `wp_prove_orthogonal`.

**Benefits:**
- The ultimate form of transparency. If Lean verification fails, the specific field (`h_ret_is_valid` or `h_incremented`) is highlighted as the core `unsolved goal`.
- Very idiomatic Lean. The user can construct the response elegantly: `exact { h_ret_is_valid := ..., h_incremented := ... }`. 
**Drawbacks:**
- High boilerplate generation output.
- May feel "heavy" for simple functions. However, `simp_all` can automatically construct these structures in trivial cases, keeping the impact invisible for basic functions.

### 4. Named Proofs
If we name our post-conditions, we unlock the ability to write granular, named proof blocks. 

**Syntax:**
```rust
/// ensures (h_positive): ret > 0
/// ensures (h_ret_is_valid): IsValid ret
/// proof (h_positive):
///   omega
/// proof (h_ret_is_valid):
///   simp_all
```

**Under the Hood (`exact {}` struct instantiation):**
Aeneas still strictly requires *one monolithic proof block* per function WP. Hermes automatically synthesizes the single block by emitting a `exact { ... }` tactic to instantiate the `Post` struct, directly assigning each user proof to its matched struct field.
```lean
:= by
  apply Hermes.wp_prove_orthogonal
  · eval_progress "Missing orthogonal progress proof..."
  · intro ret_ h_ret_
    unfold func at h_ret_
    try simp_all
    try subst h_ret_
    exact {
      h_positive := by
        omega
      h_ret_is_valid := by
        simp_all
    }
```

**Pros:**
- **Incredible Granularity:** The user proves exactly one postcondition at a time, completely isolating the local context for that specific goal without accidentally over-proving or getting mixed up.
- **Auto-Proof Injection (The Holy Grail):** If a user provides `proof (h_positive)` but omits the `proof (h_ret_is_valid)` block, Hermes simply omits the field from the `exact { ... }` block. Lean's `autoParam` elaboration then automatically evaluates the default `verify_is_valid` macro (which attempts `simp_all [Hermes.IsValid.isValid]`). The user is completely shielded from trivial `isValid` proofs!

**Cons:**
- **Shared Context Overhead:** If two post-conditions require computing the same expensive intermediate `have h_shared := ...`, named proofs explicitly isolate the branches within the struct instantiation `exact { ... }`, so they can't easily share setup. The user would have to duplicate the intermediate step or prove a standalone lemma.
  - **Resolution - `proof context`:** Hermes extends the existing `context` feature with a `proof context` block that evaluates *before* the structural instantiation to alleviate this exact issue.

**Example with `proof context`:**
```rust
/// ensures (h_pos): ret > 0
/// ensures (h_even): ret % 2 == 0
/// proof context:
///   have h_shared : ret = 2 := by simp [foo]
/// proof (h_pos):
///   omega
/// proof (h_even):
///   simp_all
```
This generates:
```lean
:= by
  apply Hermes.wp_prove_orthogonal
  · eval_progress "Missing orthogonal progress proof..."
  · intro ret_ h_ret_
    unfold func at h_ret_
    try simp_all
    try subst h_ret_
    exact
      have h_shared : ret = 2 := by simp [foo]
      {
        h_pos := by
          omega
        h_even := by
          simp_all
      }
```

**Hygienic Term-Mode Execution:**
Important: `proof context:` is evaluated directly within Lean's **Term Mode** (immediately following the `exact` keyword), *not* as an open tactic block. This means any state defined inside `proof context:` is perfectly hygienic. Users cannot accidentally manipulate the global goal state using unhygienic tactics like `unfold`, `simp_all`, or `subst` inside a `proof context:` block. They can only define localized bindings (e.g., `have`, `let`) that apply strictly to the `exact` structure initialization, ensuring robust proof composition without unintended side-effects on subsequent branch goals.

**Edge Cases & Resolution:**
- **Mixing Styles:** Users are entirely free to mix an unnamed `/// proof:` block with named `/// proof (X):` blocks. This is because the unnamed `proof:` block directly maps exclusively to the singleton `h_unnamed` field. This eliminates the need for arbitrary validation rejections.
- **Proving Complex Injected Invariants:** If a function has a complex `isValid` invariant that Lean cannot auto-prove via `simp_all`, the user can manually prove it by providing a named proof block targeting the auto-generated name (e.g., `proof (h_ret_is_valid):` or `proof (h_x'_is_valid):`). Hermes will directly assign the user's manual proof to that field in the struct instantiation, bypassing the `autoParam` default!

### 5. Development Fallbacks (`--allow-sorry`)
When verifying code iteratively, developers often want to run tests and ignore unproven bounds. Hermes supports an `--allow-sorry` flag. Instead of aggressively injecting `sorry` into the Rust struct instantiation—which would overwrite syntax errors and suppress complex tactic failures—Hermes implements this gracefully via Lean's macro environment:

1. **The `Config.lean` Injection:**
   If `--allow-sorry` is passed, `aeneas.rs` generates a `Config.lean` file containing the declaration `axiom Hermes.allow_sorry : True`.
2. **Environment-Aware Macros:**
   The `verify_is_valid` (for implicit boundaries) and `verify_user_bound` (for unproven user boundaries) macros are bound as default `autoParam` proofs in the `Post` structure. These macros invoke `eval_allow_sorry_or_fail`, which executes an `env.find?` lookup for the `Hermes.allow_sorry` axiom.
3. **Graceful Degradation:**
   - If the axiom exists, the macros successfully return ``(← `(tactic| sorry))``. If the `tactic` satisfies the proof, no warning is emitted. If it does not, `sorry` is used and a "declaration uses `sorry`" warning is emitted, pointing directly at the `Post` field.
   - If the axiom does not exist, the macro throws a hard compiler error complaining about the missing bound.
4. **Resiliency:**
   - Deliberate semantic errors (e.g. `proof: rfl` on `true == false`) completely bypass the `autoParam` default because an explicit proof replaces it. This natively surfaces Lean syntax and semantic errors, ensuring development feedback remains highly actionable even under `--allow-sorry`.
   - Precondition obligations (`requires`) are never accidentally `sorry`'d out if the user provides any explicit proof script, ensuring isolation between local post-state derivations and caller proof obligations.

---

## Addressing The Core Constraints

### Constraint 1: Low-impact on trivial cases
If a function requires no complex reasoning, the user writes nothing.
```rust
/// ```hermes
/// proof:
/// ```
// or just NO `hermes` block if we want to go full zero-boilerplate!
```
The unbundled structure combined with `simp_all` can automatically prove `h_ret_is_valid` and any other trivial bounds without user intervention. The user explicitly ignores the syntax until verification fails. 

### Constraint 2: Invisible bounds are transparent on failure
The Structure generation for Postconditions, combined with the Unbundled Preconditions, completely solve this issue. 

If verification fails, the Lean infoview points to `h_ret_is_valid : IsValid ret`, *not* `⊢ (x > 0) ∧ (IsValid ret)`. A newcomer looks at the screen, reads `h_ret_is_valid`, and intuitively understands exactly which constraint failed.

*Note: For a detailed breakdown of how Hermes augments and maps specific Lean errors to the user, see **Section 5: Diagnostic Mapping & Error Attribution**.*

### Constraint 3: Friendly to both newbies and experts
- **Newbie friendly**: Errors describe the exact assertion variable that failed (e.g. `h_ret_is_valid`, or the user's explicit name). The syntax `requires (h_name): x > 0` looks clean and aligns with Rust's explicit variable-binding ethos. The strict naming rule prevents users from ever having to guess an auto-generated variable name.
- **Expert friendly**: The `structure Pre` and `structure Post` APIs act effectively as keyword-argument structs, insulating users from brittle positional ordering or nested `AND` tuples.

---

## Known Gotchas and Edge Cases

### 1. Identifier Collisions
If Hermes auto-generates `h_x_is_valid`, but the user manually writes `requires (h_x_is_valid): ...` on another clause, Lean will throw a "duplicate identifier" compiling error. 
**Solution:** Hermes will statically validate names during parsing. If a user provides a name that conflicts with an auto-generated one (e.g., `h_<arg>_is_valid`) or provides a duplicate name, the `cargo run verify` invocation will fail cleanly with a Rust panic/error before Lean generation.

### 2. Breaking Existing Proofs
Shattering `h_req` into multiple distinct parameters fundamentally breaks the theorem signature. If an integration test manually applied `spec x ⟨h1, h2⟩`, it will fail because the function now expects `spec x h1 h2`.
**Solution:** This is a breaking change we *want* to make. It aligns the code directly with idiomatic Lean 4 proofs.

### 3. Strict Naming Enforcement vs. The Singleton Proposition
Hermes models unnamed bounds natively as a **singleton proposition** via the reserved Lean field name `h_unnamed`. This allows robust composition of both named and anonymous bounds.

- **True Compositionality**: Hermes AST cleanly handles `unnamed: Option<Clause>` and `named: HashMap<String, Clause>`. You are permitted to declare one `requires:` alongside one or more `requires (h_foo):`.
- **Lexical Reservation:** To guarantee absolute safety in Lean, Hermes `validate.rs` reserves the string `h_unnamed`. If a user attempts to manually name a bound `requires (h_unnamed): ...`, the parser will immediately reject it.
- **Auto-Routing:** When Lean compiles `exact { ... }`, the lone `proof:` block automatically populates the `h_unnamed` singleton. No guessing occurs.

### 4. Anonymous Arguments in Lean
When a user provides exactly one unnamed constraint, Hermes translates this into Lean without forcing arbitrary names into the *caller's* local context, instead encapsulating it cleanly in the Structures.

#### Unnamed `ensures`
If there is exactly one unnamed user `ensures: ret > 0` alongside auto-injected `isValid` output invariants, Hermes generates the standard encapsulated custom `structure` but internally maps the user's clause to a safe dummy field (`unnamed`).

```lean
namespace func
  structure Post (x ret x' : Std.U32) : Prop where
    h_x'_is_valid  : Hermes.IsValid.isValid x'   -- Auto-injected &mut param
    h_ret_is_valid : Hermes.IsValid.isValid ret  -- Auto-injected return
    h_unnamed      : ret > 0                     -- User's single anonymous clause
end func
```
**Why this is robust:** Unlike falling back to an `A ∧ (B ∧ C)` chain which requires tricky nested `constructor` tactics, a flat structure scales perfectly to *any* number of injected `isValid` bounds. Hermes cleanly isolates the user's single unnamed `proof` via the `exact {}` assignment behind the scenes:

```lean
:= by
  exact {
    -- 1. Hermes drops the user's Unnamed Proof block directly into the target field:
    h_unnamed := by 
      {raw_user_proof_block} 

    -- 2. Hermes omits `h_x'_is_valid` and `h_ret_is_valid` from the `exact {}` assignment,
    -- allowing Lean's `autoParam` elaboration to automatically prove them invisibly!
  }
```
The user never feels the presence of `isValid` nor the structural boilerplate. They simply write their unnamed `proof` and discharge their unnamed `ensures` target safely.

## 5. Diagnostic Mapping & Error Attribution
To ensure users are never left deciphering cryptic Lean compiler errors resulting from Hermes's structural scaffolding, Lean's `exact {}` structural instantiation and Hermes' custom `autoParam` macro handle interceptive diagnostic mapping natively.

The following edge cases must be caught and decorated with context-aware rust-centric errors:

### 1. Injected Bound Failures (`isValid`)
**Scenario:** A user returns `&mut T` but provides zero `ensures` clauses. Hermes omits the `h_arg'_is_valid` field inside the `exact {}` instantiation, letting the `autoParam` trigger `verify_is_valid`, which fails to find a trivial proof.
**Lean Output:** Lean emits a primary error stating `could not synthesize default value for field 'h_arg'_is_valid' ... using tactics`, pointing exactly to the `{` character.
**Resolution:** The `autoParam` elaboration correctly captures the missing proof. The custom `verify_is_valid` macro also surfaces a secondary error message to provide deeper context indicating exactly which invariant failed, and advising the user to provide a manual proof for it.

### 2. Missing Named Proofs & Partial Coverage
**Scenario:** A user writes `ensures (A)` and `ensures (B)`. They provide `proof (A)` but forget `proof (B)`.

**Lean Output:** Contrary to expectations for structural instantiation, Lean does *not* throw a "missing field" error at the `{`. This is because Hermes assigns a default `autoParam` of `verify_user_bound` to *all* user-defined `ensures` fields in the generated `Post` structure. If the user bound corresponds to a completely trivial arithmetic or logical condition (e.g., `x > 0` where `x` is `1`), Lean will automatically attempt to satisfy the `verify_user_bound` requirements transparently. 

The `verify_user_bound` macro automatically attempts to dispatch the goal using a robust default tactic chain:
1. `simp_all [Hermes.IsValid.isValid]`: To resolve basic logical equivalences, equalities, and unroll validity constraints.
2. `(try scalar_tac)`: An Aeneas-provided wrapper around `omega` that specializes in dispatching bounded integer arithmetic (e.g. `ret >= 1`), which runs as a fallback if `simp_all` leaves arithmetic goals open.

If any of these tactics successfully close the goal, the proof succeeds entirely silently. The user never even knows they missed a proof! 

If the tactics *fail* to close the goal, the macro falls back to its fail-safe: if `--allow-sorry` is enabled, it injects `sorry` and emits a `declaration uses sorry` warning. If `--allow-sorry` is disabled, the macro throws a custom error pointing exactly at the bound: `Missing explicit proof for named bound B`.
**Resolution:** The `autoParam` automatically dispatches trivial mathematical and logical bounds, gracefully degrades to `sorry` for rapid prototyping when `--allow-sorry` is enabled, and strictly halts verification with a localized, readable error identifying the exact missing user bound when disabled.
### 3. Mismatched Proof Names
**Scenario:** A user writes `ensures (h_foo)` but later writes `proof (h_bar)`.
**Lean Output:** If blindly passed to Lean inside `exact { h_bar := by ... }`, Lean would throw: "invalid field `h_bar` for structure `Post`...".
**Resolution:** Hermes catches this **at the Rust parsing/AST stage** before generating Lean. It panics statically: 
> *"Validation Error: You provided a proof for `h_bar` but no such constraint exists. Did you mean `h_foo`?"*

### 4. Duplicate Clause Naming
**Scenario:** A user names a requirement `requires (h_same)` and also names a postcondition `ensures (h_same)`.
**Lean Output:** "duplicate identifier `h_same`" or "duplicate field `h_same`".
**Resolution:** Hermes static validation must assert that all names provided by the user across `requires` and `ensures` for a single function are strictly globally unique, panicking at the Rust level if there is a collision.

### 5. `h_unnamed` Dummy Field Leakage
**Scenario:** A user has exactly one unnamed `ensures : x > 0` alongside an injected `isValid`. Hermes generates the dummy `h_unnamed` field in the structure. The user's unnamed `proof` fails to solve it.
**Lean Output:** "Unsolved goal for `h_unnamed`".
**Resolution:** Seeing `h_unnamed` in an error will confuse users who think they just wrote an anonymous clause. Hermes should intercept goals tagged with `h_unnamed` and strip the name from the diagnostic: 
> *"Your anonymous ensures clause failed to verify: `x > 0`"*

### 6. Line Number Attribution in `proof context`
**Scenario:** A user writes a faulty `have h : x = 0 := by omega` inside a `proof context` block.
**Lean Output:** Fails on the `have` binding, *before* the goals are split. 
**Resolution:** Because the generated Lean file abstracts the structure heavily, Hermes must map the line number of the failing tactic in the Lean file tightly back to the `proof context` block in the original `.rs` file so the user knows where their intermediate lemma failed.

---

## 6. Future Considerations

### `isValid` Opt-out
Because `isValid` injection will become robust and systemic, a future extension should provide an **opt-out mechanism**. 
If a function is intentionally designed to bypass invariants (e.g., an `unsafe(axiom)` manipulating raw memory layouts before initialization), Hermes should support a syntax like `requires !isValid(x)` or `#[hermes::raw_mut]` to suppress the auto-injection for a specific parameter or return type.

### WP Spec Extraction under Orthogonal Progress
Because the generated `WP.spec` for each function separates the progress goal from the correctness predicates (the Orthogonal WP Architecture), when users manually instantiate the specification of a sub-call (e.g., `have _h_call := other_func.spec ...`), the postconditions are wrapped in the WP evaluation and cannot be directly extracted without a complex specification elimination tactic (e.g., `have ⟨_, h_call_ens⟩ := _h_call.elim h_ret_`). A future extension should provide streamlined Lean 4 tactics or auto-generated macros to automatically unwrap and expose these postconditions into the local proof context, restoring the simple ergonomics of sub-call composition.

---

## 7. System Architecture

This section details how the named bounds design is architected across the Hermes pipeline: parsing, validation, and final Lean code generation.

### AST and Parser (`src/parse/attr.rs`)
The Hermes extraction parser evaluates named clauses and proof blocks mapping accurately to AST structures.

1. **Clause Struct**: 
   - `Clause<M>` holds an optional `name: Option<Ident>` mapping the explicit bound.
2. **Parser State Machine (`parse_hermes_block_common` & `RawHermesSpecBody::start_section`)**:
   - Keyword parsing logic for `requires` and `ensures` extracts the optional `(name)` from the argument string before the `:` separator.
   - Strict enforcement of `:` ensures predictable AST splits (e.g., `requires (name): expr`).
   - `proof` parsing accurately differentiates between `proof context`, `proof (name)`, and unnamed `proof` branches.
3. **AST Node Structure**:
   - `FunctionBlockInner::Proof` cleanly maps strings to `context: Vec<SpannedLine>` and maintains a `cases: Vec<Clause<M>>` isolating named proof segments.

### Static Validation (`src/validate.rs`)
Enforcing structural integrity and the strict Anonymity Principle happens before Lean generation.

1. **Naming Rules (checked during AST finalization)**:
   - For a given function, if there is > 1 user-defined `requires`, Hermes panics if they are not all named.
   - If there is > 1 user-defined `ensures`, Hermes panics if they are not all named.
   - If exactly one `requires` or `ensures` exists and is unnamed, it maps its internal name safely to `unnamed`.
2. **Collision and Coverage Checks (`validate.rs`)**:
   - It verifies that all names across `requires` and `ensures` within a single function are strictly globally unique, halting on naming collisions with reserved identifiers (`h_{arg}'_is_valid` or `h_ret_is_valid`).
   - For every named `proof (X)` block, Hermes asserts that `X` corresponds to a known, named `ensures` clause or an auto-injected `isValid` bound.
   - *Note: Missing proofs for `ensures` are not flagged at this stage; Lean's `autoParam` struct synthesis cleanly surfaces these errors natively during elaboration.*

### Translation Logic (`src/generate.rs`)
`generate_function` translates Rust functions into clean Lean representations, emphasizing elegant structs and isolated proof boundaries.

1. **Helper Mapping (`extract_args_metadata`)**:
   - All function arguments (including `self` mapping safely) resolve to Lean variable names and types to precisely map to `Pre` and `Post` fields.
2. **Precondition Structure (`structure Pre`)**:
   - Generates a localized `namespace <func_name>` and standardizes `structure Pre`.
   - Implements input preconditions: `h_{arg}_is_valid : Hermes.IsValid.isValid {arg}`.
   - Projects user `requires` bounds safely: `{name} : {expr}`.
   - Projects cleaner theorem signatures leveraging `pre : {func_name}.Pre args...`.
3. **Postcondition Structure (`structure Post`)**:
   - Emits `structure Post` encapsulating state variables.
   - Derives output arguments bridging inputs, outputs (`ret`), and mutable state transitions.
   - Enforces default bounds by utilizing Lean's `autoParam` feature natively mapping `h_{arg}'_is_valid` and `h_ret_is_valid` to `verify_is_valid` fallbacks.
4. **Proof Synthesis**:
   - Evaluates a `proof context` safely in **Term Mode**, preventing unhygienic tactic leakage prior to structural decomposition.
   - Initiates isolated verification boundaries cleanly mapped inside an `exact` tactic instantiation.
   - Translates matched user `proof ({name})` payloads tightly into structural fields, skipping unmatched fields dynamically so Lean's `autoParam` synthesis can prove implicit boundaries anonymously if they succeed.

### Lean Infrastructure Setup
1. **The `verify_is_valid` Macro (`src/Hermes.lean`)**:
   - Evaluates bounds natively via `simp_all [Hermes.IsValid.isValid]`. If `simp_all` cannot silently execute the boundary constraint, it surfaces an intuitive error alerting the user to manually verify the parameter.
2. **Diagnostic Mapping (`src/aeneas.rs`)**:
   - Extracts accurate line-reporting mapping unverified structures gracefully back onto the original `ensure` or `proof` blocks inside the Rust source file resolving the debug loop efficiently.

---

## 8. Development & Implementation Details

To ensure diagnostics remain isolated, Hermes employs several specific architectural tactics:

1. **`h_unnamed` Diagnostic Stripping**: Aeneas and Hermes intercept `h_unnamed` fields targeting anonymous user constraints, ensuring users see plain strings like "Your anonymous ensures clause failed to verify: `x > 0`" rather than the confusing structural `h_unnamed`.
2. **Auto-proving Trivial User Bounds**: `verify_user_bound` uses strict `simp_all; scalar_tac` chains. 
3. **`proof context` Safety**: `proof context:` boundaries are evaluated hygienically in **Term Mode** directly alongside the `exact` instantiation. This strictly restricts them to injecting bindings (e.g., `have`, `let`) or intermediate lemmas without allowing unhygienic tactics (`unfold`, `simp_all`) to leak into and corrupt the global goal state.
4. **Targeted `sorry` Warnings**: When `eval_allow_sorry_or_fail` invokes `sorry` dynamically via `--allow-sorry`, it emits a clear "declaration uses sorry" attached directly to the precise `Post` struct field or `Progress` goal that failed.

## 9. Solving Stuck WPs: The Decoupled (Orthogonal) WP Architecture

To elegantly solve stuck Weakest Preconditions (WPs) (often caused by opaque dependencies) without destroying the highly-targeted diagnostics of the `Post` struct fields, Hermes structurally decouples Progress from Correctness.

### Progress as an Orthogonal Property

**Progress and Correctness are mathematically strictly orthogonal.**

We can frame "the Weakest Precondition is stuck" as simply "the function failed to automatically prove Progress". 

By treating Progress exactly like any other bounded property (like `isValid` or a user `ensures` clause), Hermes naturally resolves subset evaluation and granular diagnostics uniformly:
- It gets its own named default tactic (`eval_progress`).
- It gets its own distinct `--allow-sorry` handling (emits a target warning if skipped).
- It can fail explicitly without `--allow-sorry`.
- **Crucially: The user can provide an explicit proof for it, which overrides the `--allow-sorry` fallback completely.**

Standard Aeneas Weakest Preconditions (`WP.spec m P`) are mathematically equivalent to:
$$(\exists y, m = .ok\ y) \land (\forall y, m = .ok\ y \implies P\ y)$$

We instituted a native Lean theorem `wp_prove_orthogonal` to unilaterally split the generated proof into two universally distinct subgoals:

```lean
theorem wp_prove_orthogonal {α} {m : Result α} {P : α → Prop} :
  (∃ y, m = .ok y) → (∀ y, m = .ok y → P y) → WP.spec m P := by
  intro ⟨y, hy⟩ hP
  rw [hy]
  exact hP y hy
```

Every single generated `WP.spec` is now structured manually in `generate.rs`:
```lean
theorem spec_function_name : WP.spec function_name (fun ret => Post ret) := by
  apply wp_prove_orthogonal
  · -- Goal 1: Progress (Strictly orthogonal)
    eval_progress "The function's progress evaluation stalled, likely due to an opaque dependency."
  · -- Goal 2: Correctness (Predicates)
    intro y hy
    exact { 
      predicate_easy := by ...
      predicate_hard := by ...
    } 
```

**Why this works perfectly:**
1. **Progress Isolation:** The `Progress` goal (`∃ y, m = .ok y`) executes the structural reduction of the expression evaluating the function. If it stalls, it hits `eval_progress` macro and safely degrades, acting exactly like an `autoParam` field failure but at the structural goal level. *(Note: `eval_progress` employs `exact ⟨_, rfl⟩` internally to universally support functions with non-`Unit` return types, ensuring robust existential witness inference.)*
2. **Predicate Survival:** The `Predicates` goal universally binds the output `y` (and any state variations like `hy : ... = .ok y`) into the local context. Thus, the `Post` struct type is *mathematically rigorous and fully known*. `exact { ... }` natively compiles on the second goal without ever hitting the structural instantiation bug. 
3. **Subset Granularity:** When `exact { ... }` runs on the second goal, every single field evaluates independently. Satisfiable fields succeed silently. Unsatisfiable fields trigger their own `autoParam` failures.

### Providing User Proofs for Progress

Because Progress is now treated as an orthogonal property, users must be able to explicitly name and satisfy it. 

To accomplish this, Hermes recognizes a special `proof progress:` block:

```rust
/// proof progress:
///   progress as ⟨ ret, h_ret_is_valid, ... ⟩
///   simp_all
```

Then `generate.rs` will inject the user's explicit proof strictly into the isolated Progress Goal:

```lean
theorem spec_function_name : WP.spec function_name (fun ret => Post ret) := by
  apply wp_prove_orthogonal
  · -- Goal 1: Extracted User Progress Proof 
    progress as ⟨ ret, h_ret_is_valid, ... ⟩
    simp_all
  · -- Goal 2: Correctness (Predicates)
    intro y hy
    exact { ... }
```

By formalizing Progress as a distinct, addressable obligation, the system elegantly escapes the structural instantiation crisis of `exact { ... }` while perfectly aligning the UX of Stuck WPs with the rest of the named bounds diagnostic philosophy.

### Advanced Limitation: WP Spec Extraction under Orthogonal Progress

Because the generated `WP.spec` for each function separates the progress goal from the correctness predicates, **the Aeneas `progress` tactic cannot be used inside `proof context:` blocks.**

`proof context:` evaluates on the **Correctness** branch (Goal 2), *after* the WP has already been split. This means the target hypothesis `h_ret_` locally available in `proof context:` is not a Weakest Precondition (`WP.spec`); it is a direct equality (e.g., `test_func = ok ret_`).

Because `progress` specifically targets and evaluates WPs, **using `progress` inside `proof context:` to extract sub-calls will fail.**

```rust
// THIS FAILS because `progress` requires a WP target
/// proof context:
///   progress as ⟨ ret_val, h_valid ⟩
```

**Workaround (Relocate to `proof (h_progress)`):**
Because `proof context:` is strictly evaluated in Term Mode on the Correctness branch, unhygienic tactic operations (`progress`, `unfold`, `simp_all`) are completely illegal inside it. Users must relocate these operations to the `proof (h_progress):` block, which natively supports tactic mode evaluation for Weakest Preconditions, or to the specific `proof (field):` branch where the values are needed.

```rust
/// proof (h_progress):
///   unfold parent_func at *
///   progress as ⟨ ret_val, h_valid ⟩
///   unfold parent_func at h_ret_
///   simp_all [parent_func, sub_func]
///   -- The equality is now successfully manually unwrapped!
```

A future extension should provide streamlined Lean 4 tactics or auto-generated macros (e.g., a `.elim` tactic or a specialized `extract_post` macro) to automatically unwrap and expose these postconditions into the local proof context from the evaluated equality, restoring the simple ergonomics of sub-call composition.
