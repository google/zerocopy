<!-- TODO: Incorporate the advice in this document and delete it before merging. -->

# Evaluation of AGENTS.md

## Overview
This document evaluates the current `AGENTS.md` file against the best practices identified in `agents_md_best_practices.md`.

## Strengths
*   **Clear Persona:** The document establishes a clear role ("expert Rust systems programmer").
*   **Golden Commands:** The emphasis on `cargo.sh` is excellent and aligns with the "Golden Commands" principle.
*   **Explicit Boundaries:** The "Critical Dos and Don'ts" section effectively sets boundaries (e.g., `README.md` generation, `TODO` vs `FIXME`).
*   **Testing Strategy:** The recent updates to the testing strategy and Kani documentation are detailed and actionable.

## Gaps & Recommendations



### 2. Chain of Thought Trigger
*   **Current State:** There is no explicit instruction for the agent to "think" or plan before acting.
*   **Recommendation:** Add a "Workflow" or "Interaction Protocol" section requiring agents to use `<thinking>` tags or a specific planning format before making changes.



### 4. Specific Anti-Patterns
*   **Current State:** We list some "Don'ts", but we could be more specific about recurring issues.
*   **Recommendation:** Add a "Common Pitfalls" section.
    *   *Question:* Are there specific mistakes agents make repeatedly in this repo? (e.g., using `std` features in `no_std` contexts?)

### 5. Formatting & Readability
*   **Current State:** The "Critical Dos and Don'ts" section is a mix of high-level rules (workflow) and specific syntax (coding).
*   **Recommendation:** Group these into logical categories (e.g., "Workflow Rules", "Coding Rules") and remove redundancies (e.g., pointer casts are already in "Safety Guidelines").

## Completed Improvements
*   **"Show, Don't Tell":** Added detailed "Good vs. Bad" examples for pointer casts, safety comments, and macro lints.
*   **"Why" Context:** Added explanations for `cargo.sh`, strict linting, and version matching.
*   **Formatting:** Enforced 80-column wrapping throughout the file.

## Questions for User
1.  **Chain of Thought:** Do you want to enforce a specific "thinking" protocol (e.g., `<thinking>` tags) for every major task?
2.  **Anti-Patterns:** What are the most annoying/frequent mistakes agents make in this codebase?
3.  **Tone:** Is the current tone (authoritative but professional) working, or should it be stricter/more encouraging?
