---
name: comment-guidelines
description: >-
  Write or review explanatory code comments that preserve non-obvious rationale,
  invariants, assumptions, contracts, and behavior without becoming stale. Use
  when adding, revising, or reviewing explanatory inline comments or
  documentation comments. Not for standalone prose documentation,
  non-prose tool directives, or pure task-tracking markers unless
  explanatory comment editing is also part of the task.
---

# Comment guidelines

Write comments for the reader and interface they serve. Help that reader
understand information they should not have to reconstruct from elsewhere, and
keep that information accurate as the code evolves. Do not add an explanatory
comment merely because this skill is active; clear implementation code may need
no implementation comment.

## Content

### Match the comment to its audience

For implementation comments, prioritize information a source reader cannot
reliably infer from the surrounding code:

- why a design or implementation choice exists;
- invariants and constraints that must remain true;
- non-obvious semantics, contracts, side effects, edge cases, or safety
  considerations; and
- assumptions about external systems, data, or environments when they materially
  affect correctness, safety, compatibility, or interoperability.

Do not narrate syntax or obvious control flow. When the task permits a code
change and the code can express a fact more directly and durably, prefer making
the code clearer rather than using a comment to excuse avoidable obscurity.

Caller-facing documentation comments are part of the API. Document the
behavior, obligations, side effects, errors, safety conditions, and usage
context that callers need without reading the implementation, as relevant to
that API and the project's documentation conventions. Do not omit needed API
documentation merely because the implementation or type signature makes the
information discoverable. Do not expose mutable implementation details as API
contract.

### Describe the current code, not its chronology

State current facts and current reasons. Do not use explanatory comments as a
changelog or roadmap. Mention an ongoing transition, future condition, or prior
design only when it is needed to explain why the current code has its present
shape or to preserve a lesson that constrains the current design. Make the
present constraint understandable without requiring the reader to reconstruct
that history.

### Keep the relevant context local

A reader should not need unexplained knowledge of distant code to understand a
comment. At the same time, do not duplicate mutable implementation details from
elsewhere merely to make a comment self-contained; that creates another source
of truth that can become stale.

When a cross-code relationship is essential, name the stable concept or
identifier and explain the relationship that must remain true. Avoid claims
whose correctness silently depends on unrelated mutable details elsewhere in the
codebase.

### Document assumptions precisely

Explicitly comment a non-obvious external assumption when violating it would
change behavior or invalidate correctness, safety, compatibility, or
interoperability, unless nearby code, types, APIs, or checks already make the
assumption clear. State what must remain true and why it matters. A comment
records an assumption; it does not enforce it.

## Style

1. Write prose comments as full sentences with proper grammar, capitalization,
   and punctuation. Headings, table cells, diagrams, and code fragments need not
   be sentences.
2. Use straightforward, factual language. Avoid subjective or superlative claims
   such as "flawlessly", "seamlessly", or "beautifully".
3. Wrap comment prose at **80 columns** from the left margin, including
   indentation and any comment marker such as `//`, `///`, or `//!`.
   a. **Exceptions:** Markdown tables, ASCII diagrams, long URLs, code blocks,
      or other cases where wrapping would impair readability.
   b. In bulleted lists, indent continuation lines by 2 spaces.
   c. Do not wrap a link if doing so would break it.
4. Put a blank comment line between prose paragraphs and between a section
   header and the first line of that section. Do not write:

   ```
   // Lorem ipsum.
   // Dolor sit amet ...
   ```

   Instead, write:

   ```
   // Lorem ipsum.
   //
   // Dolor sit amet ...
   ```

## Self-check

- [ ] Is each explanatory comment appropriate for the reader and interface it
      serves?
- [ ] Does each implementation comment add information the surrounding code does
      not make clear on its own?
- [ ] Does each caller-facing documentation comment state the contract callers
      need without requiring them to read the implementation?
- [ ] Does the comment explain the current rationale, invariant, contract, or
      assumption instead of merely narrating the code or its history?
- [ ] Can a reader understand it without unstated knowledge of distant code, and
      does it avoid duplicating mutable details from elsewhere?
- [ ] Are material, non-obvious external assumptions documented?
- [ ] Are prose comments complete, grammatical sentences using factual language?
- [ ] Are prose lines wrapped at 80 columns, with the documented exceptions?
- [ ] Are paragraphs and section bodies separated as required?
