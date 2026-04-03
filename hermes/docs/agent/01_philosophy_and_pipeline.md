# Module 1: Philosophy and Pipeline

Welcome to Hermes! Before you write your first specification or try to prove your first theorem, it's critical that you understand *what* Hermes is, *why* it exists, and *how* the mechanical pipeline works step-by-step. 

Without this mental model, you will struggle to debug issues, interpret errors, or understand why the tooling is structured the way it is.

## 1. The Functional Verification Gap 

### What are Charon and Aeneas?
Hermes does not translate Rust to Lean by itself. It delegates the heavy lifting of pure program verification to a pipeline consisting of two tools:
1. **Charon** parses your Rust code's Mid-level Intermediate Representation (MIR) and extracts it into an intermediate artifact called LLBC.
2. **Aeneas** reads that LLBC and performs a **purely functional translation**, emitting Lean 4 formal models.

Aeneas relies heavily on Rust's strict borrow-checker rules. Because safe Rust statically guarantees non-aliasing and immutability, Aeneas can structurally flatten your program into pure mathematical functions, entirely abstracting away raw physical memory, pointers, and manual spatial reasoning.

### The Unsafe Boundary
While Aeneas is incredibly powerful for *safe* Rust, its purely functional translation completely breaks down at the `unsafe` boundary. Aeneas cannot mathematically model a raw pointer (`*const T` or `*mut T`) or understand unsafe memory operations (like `ptr::read_unaligned()`), because these operations violate the functional abstraction of non-aliasing tree structures.

If Aeneas encounters an opaque external call or untranslatable unsafe operation, it emits it into Lean as an **opaque, uninterpreted axiom** (i.e. a function definition with no body).

### Why Hermes Exists
**This is exactly where Hermes comes in.** Hermes is designed specifically to bridge this functional verification gap. 

Hermes allows you to write inline mathematical specifications (preconditions and postconditions) for the safe wrappers around these unsafe operations. Hermes then acts as the glue:
1. It allows you to **axiomatize** the un-verifiable unsafe "leaf" operations that Aeneas cannot model functionally (using `unsafe(axiom)`).
2. It allows you to write the mathematical proofs that structurally define exactly what those opaque leaves do.
3. It relies on Aeneas to functionally verify the safe *glue code* and control flow that composes those leaves together.

In short, Hermes lets you enforce the mathematical safety of `unsafe` code at its boundary, enabling the rest of your crate to be verified using pure functional mathematics.

---

## 2. The Verification Pipeline

When you invoke Hermes via the CLI (e.g., `cargo run verify`), a complex pipeline executes behind the scenes. Understanding this pipeline is your most powerful tool for debugging.

1. **Extraction (Charon).** Hermes invokes Charon to parse your Rust codebase. 
   * **The `--start-from` Optimization:** Hermes tells Charon to only extract functions that actually carry `/// ```hermes` annotations and their transitive dependencies. You don't need to fear running Hermes on a massive crate—it automatically bounds the verification strictly to the dependency graph of the code you annotate.
2. **Translation (Aeneas).** Charon outputs an LLBC artifact. Hermes passes this artifact to Aeneas, which generates standard Lean 4 files modeling your Rust code functionally.
3. **Specification Generation (Hermes).** In parallel, Hermes's internal scanner reads your actual Rust source files, parses the mathematical specifications and proofs out of your `/// ```hermes` doc comments, and generates its own Lean file (usually called `<CrateName><Hash>.lean`).
4. **Compilation (Lake).** Hermes aggregates the Aeneas-generated functional models and its own Hermes-generated specifications, dropping them into isolated directories. It then invokes the Lean package manager (`lake`) to compile the proofs and check their mathematical correctness against the generated model.
