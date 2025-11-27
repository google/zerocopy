<!-- TODO: Delete this document before merging -->

# AGENTS.md Best Practices: A Comprehensive Guide

## Introduction

This document synthesizes extensive research on best practices for creating `AGENTS.md` files and similar agent-guiding documentation (such as `.cursorrules` and `llms.txt`). The goal is to provide a detailed, actionable blueprint for empowering AI coding agents to work effectively, correctly, and safely within a software repository.

## Core Principles

### 1. The "Operating Manual" Mindset
Treat `AGENTS.md` not as general documentation, but as a strict **Operating Manual** for a specific employee. It should answer:
*   "Who am I?" (Persona)
*   "What are my tools?" (Commands)
*   "What are the rules?" (Boundaries & Style)
*   "How do I verify my work?" (Testing & Validation)

### 2. Clarity Over Brevity
While human documentation often favors brevity, agent documentation favors **specificity**. Ambiguity is the enemy. If a procedure has edge cases, document them. If a command has specific flags that *must* be used, explicitly state them.

### 3. Show, Don't Just Tell
Agents perform significantly better with **few-shot prompting**. Instead of describing a coding style, provide a concrete example of "Good Code" vs. "Bad Code".
*   **Do:** "Use `Result<T, E>` for error handling."
*   **Better:** Provide a snippet showing a function returning `Result` and handling the error.

### 4. Context Optimization
LLMs have limited context windows.
*   **High Signal-to-Noise:** Exclude generic advice (e.g., "write clean code"). Focus on project-specific constraints.
*   **Selective Inclusion:** If the repo is massive, consider splitting instructions into smaller, scoped files (e.g., `frontend/AGENTS.md`, `backend/AGENTS.md`) or using a "map" file like `llms.txt` to point to relevant resources.

---

## Content Guidelines: What to Include

### 1. Agent Persona & Scope
Define the agent's role to prime its behavior.
*   **Role:** "You are an expert Rust systems programmer specializing in zero-copy parsing."
*   **Scope:** "You are responsible for the `src/` directory. You generally do not touch `tools/` unless explicitly asked."

### 2. The "Golden Commands"
List the exact commands the agent should use. Do not assume it knows your build system quirks.
*   **Build:** `cargo build --release` (or `npm run build`)
*   **Test:** `cargo test --workspace` (or specific flags like `-- --nocapture`)
*   **Lint:** `cargo clippy -- -D warnings`
*   **Format:** `cargo fmt -- --check`

> **Tip:** If you have wrapper scripts (e.g., `./cargo.sh`), explicitly instruct the agent to *always* use them and *never* use the raw tool.

### 3. Explicit Boundaries & Safety
Define what is strictly forbidden. This is crucial for safety.
*   **Secrets:** "NEVER output API keys or secrets."
*   **Files:** "NEVER edit `.lock` files manually."
*   **Behavior:** "NEVER remove `// SAFETY:` comments."
*   **Deps:** "Do not add new dependencies without user approval."

### 4. Coding Standards & Patterns
Go beyond standard linting.
*   **Idioms:** "Prefer `matches!` macro over `if let` for simple enum checks."
*   **Error Handling:** "Always propagate errors with `?`. Never use `unwrap()` in production code."
*   **Comments:** "All public APIs must have doc comments. All unsafe blocks must have `// SAFETY:` comments explaining why they are sound."
*   **Deprecated Patterns:** Explicitly list patterns to avoid (e.g., "Do not use `lazy_static`; use `OnceLock` instead.").

### 5. Testing Strategy
Explain *how* to test, not just *to* test.
*   **Unit vs. Integration:** "Unit tests go in the same file in a `mod tests`. Integration tests go in `tests/`."
*   **UI Tests:** "Run `./tools/update-ui-tests.sh` to update stderr files. Do not edit them manually."
*   **Mocking:** "Use the `mockall` crate for mocking traits."

### 6. Git & Workflow
*   **Commit Messages:** "Use Conventional Commits (e.g., `feat: add new parser`)."
*   **PRs:** "Keep PRs small and focused. One logical change per PR."
*   **Pre-push:** "Always run `./githooks/pre-push` before asking for review."

---

## Structural Best Practices

### 1. File Placement
*   **Root:** Place `AGENTS.md` in the root of the repository.
*   **Nested:** For monorepos, place specific `AGENTS.md` files in subdirectories. Agents should ideally look for the nearest instruction file.

### 2. Formatting
*   **Markdown:** Use standard Markdown headers (`#`, `##`) to structure the document. LLMs parse this structure well.
*   **Code Blocks:** Use fenced code blocks (```rust) for all examples.
*   **Alerts:** Use GitHub-style alerts (`> [!IMPORTANT]`) to highlight critical rules.

### 3. The "Chain of Thought" Trigger
Encourage the agent to think before acting.
*   "Before generating code, propose a plan in `<thinking>` tags."
*   "Review your changes against the `Safety Guidelines` section before submitting."

---

## Examples & Templates

### Example Section: "Critical Rules"
```markdown
## Critical Rules
> [!IMPORTANT]
> These rules are non-negotiable. Violation will result in rejected code.

1. **Wrapper Scripts:** ALWAYS use `./cargo.sh` instead of `cargo`.
2. **Safety Comments:** Every `unsafe` block MUST have a `// SAFETY:` comment citing the Rust Reference.
3. **No Unwraps:** `unwrap()` and `expect()` are banned in `src/`. Use `?` or handle errors explicitly.
```

### Example Section: "Testing"
```markdown
## Testing Strategy
*   **Unit Tests:** Colocate with code in `mod tests`.
    *   *Command:* `./cargo.sh test lib`
*   **UI Tests:** Located in `tests/ui`.
    *   *Update:* `./tools/update-ui.sh` (NEVER edit `.stderr` manually)
*   **Verification:**
    *   Run `cargo kani` for formal verification of unsafe code.
```

---

## Deep Dive: Chain of Thought (CoT) Triggers

### Theory
Chain of Thought (CoT) prompting is a technique that enables Large Language Models (LLMs) to solve complex problems by breaking them down into intermediate reasoning steps. Research shows that models forced to "show their work" before generating a final answer produce significantly more accurate, consistent, and safe code.

For coding agents, CoT is critical because:
1.  **Error Detection:** It allows the model to catch logic errors *before* committing them to code.
2.  **Context Management:** It forces the model to explicitly retrieve and organize relevant context from its memory.
3.  **Safety Verification:** It creates a dedicated space to check against safety guidelines (e.g., "Is this `unsafe` block sound?") before generating the block.

### The "Trigger" Mechanism
A "trigger" is a specific instruction in the system prompt that forces the model into a reasoning mode. The most effective triggers use **XML tags** to structure this reasoning, separating it from the final output.

### Best Practices for Implementation

#### 1. The `<thinking>` Protocol
Enforce a strict protocol where every significant action must be preceded by a `<thinking>` block.

**Example Instruction:**
> "Before generating any code or making any changes, you MUST first output a `<thinking>` block. In this block, you will:
> 1.  Restate the user's goal.
> 2.  List the files you need to modify.
> 3.  Identify potential risks or edge cases.
> 4.  Verify your plan against the `Safety Guidelines`.
>
> Only after closing the `</thinking>` tag may you output the code."

#### 2. Structured Reasoning Templates
For high-stakes tasks, provide a template within the trigger.

**Example for Unsafe Code:**
> "When writing `unsafe` code, your `<thinking>` block must include:
> - **Invariant Analysis:** What invariants does this type maintain?
> - **Safety Argument:** Why is this specific operation safe?
> - **Citation:** Which part of the Rust Reference justifies this?"

#### 3. Zero-Shot vs. Few-Shot Triggers
*   **Zero-Shot:** "Think step by step." (Good for general tasks)
*   **Few-Shot:** Provide an example of a `<thinking>` block followed by the correct code. (Better for specific, complex protocols like `zerocopy` safety).

#### 4. The "Refusal" Trigger
Instruct the agent to use the reasoning phase to *reject* unsafe requests.
> "If your analysis in `<thinking>` reveals that the user's request violates safety policy, you must STOP and explain why, instead of generating the code."

### Recommended Implementation for `AGENTS.md`
Add a top-level section called **"Interaction Protocol"**:

```markdown
## Interaction Protocol

To ensure correctness and safety, you must follow this thinking process for every coding task:

1.  **Analyze:** Open a `<thinking>` block.
2.  **Plan:** Break down the task into steps.
3.  **Verify:** Check each step against the **Critical Dos and Don'ts** and **Safety Guidelines**.
4.  **Execute:** improved code generation.

**Example:**
<thinking>
The user wants to cast a byte slice to `MyStruct`.
- Risk: `MyStruct` might not have valid alignment.
- Rule Check: I must use `Ref::new_from_prefix` instead of a raw cast.
- Safety: This handles alignment checks at runtime.
</thinking>
```

## Maintenance & Iteration

### 1. Treat as Code
`AGENTS.md` is part of the codebase. Version control it. Review changes to it just like code changes.

### 2. Iterative Refinement
*   **Feedback Loop:** When an agent makes a mistake, ask "Did the `AGENTS.md` cover this?"
*   **Fix the Root Cause:** If the agent used a forbidden pattern, add a specific rule against it in `AGENTS.md`. Don't just correct the code; correct the *instructions*.

### 3. Keep it Fresh
*   Update versions (e.g., "We are now on Rust 1.75").
*   Remove obsolete rules to keep the context window clean.

## Conclusion
A well-crafted `AGENTS.md` is a force multiplier. It turns a generic coding assistant into a specialized team member that knows your project's specific culture, constraints, and workflows. By investing time in this "meta-programming," you ensure consistent, high-quality contributions from AI agents.
