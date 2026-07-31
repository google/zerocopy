<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal

Anneal is a verification tool for Rust. It helps developers replace informal
reasoning about unsafe code with checked proofs, and it can also verify precise
application-specific promises about program behavior.

> **Status:** Anneal is under active construction and cannot yet verify
> applications. The checked-in executable currently provides only toolchain
> setup infrastructure. The example below illustrates the problem Anneal
> addresses, not a workflow which is currently available.

## Why Anneal exists

Rust's safe APIs promise that ordinary, type-checked use will not cause
undefined behavior—for example, an invalid memory access or a data race. We
call this guarantee soundness: every use which the safe API permits must remain
free from undefined behavior. Safe code can still panic, run forever, or
produce the wrong answer, but a safe API must remain sound even when it uses
unsafe code internally.

Unsafe Rust lets a programmer perform operations whose soundness the compiler
cannot verify. Each such operation comes with requirements: a pointer might
need to refer to live memory, an index might need to be in bounds, or a value
might need to be initialized. The compiler accepts the operation because the
programmer takes responsibility for meeting those requirements.

That reasoning is usually recorded in a comment:

```rust
pub fn get_byte(bytes: &[u8], index: usize) -> u8 {
    assert!(index < bytes.len());

    // SAFETY: `bytes` is a valid slice and `index` is in bounds, so this
    // pointer may be dereferenced.
    unsafe { *bytes.as_ptr().add(index) }
}
```

A reviewer can understand this argument, but Rust does not check that the
comment is correct or remains correct after a refactor. If the bounds check is
removed or moved too late, the unsafe operation's requirements may no longer
hold while the comment continues to look reassuring.

Because `get_byte` is a safe function, callers may pass any `usize`. An
out-of-bounds call may panic at the assertion, but it must never cause undefined
behavior. A safe API must not place a hidden safety requirement on its caller.

Anneal turns reasoning like the safety comment into proof obligations checked
by [Lean](https://lean-lang.org/), a language which mechanically checks
mathematical arguments. If Anneal cannot establish an obligation, it reports
the gap and identifies the operation which produced it instead of silently
treating the comment as proof. An undischarged obligation is a verification
failure and a useful diagnostic; by itself, it does not prove that the Rust
code is unsound.

This is intentionally a tiny example; ordinary Rust should simply use
`bytes[index]`. It stands in for implementations which cannot avoid unsafe
operations. It contains no Anneal-specific syntax because the specification
and proof-authoring interface is still being designed.

## What Anneal adds

Anneal lets a project describe:

- the requirements a caller must satisfy before using an unsafe API;
- the promises a function or type makes to its callers; and
- the reasoning which connects ordinary Rust code to those requirements and
  promises.

Anneal checks the Rust safety obligations within the claimed scope, including
the requirements of unsafe operations and the promises on which safe APIs
rely. It follows those promises through function calls, so a verified
implementation can be used through its API without every caller re-examining
its private unsafe code.

For a safe abstraction, the goal is straightforward: callers can use the safe
API according to the normal Rust type system, with no hidden rule whose
violation could cause undefined behavior. An unsafe API may explicitly give
part of that responsibility to its caller—for example, through a function
declared `unsafe` with documented requirements.

## What a verification result means

**Note:** The exact report format and command behavior are still being designed.

A successful Anneal result identifies the particular code and build it covers
and states which guarantees were checked. At a minimum, it establishes that:

- every safety-relevant operation within the named coverage satisfies Rust's
  requirements;
- the functions and types checked by Anneal keep the promises stated in their
  specifications; and
- anything Anneal could not prove, deliberately trusted, or did not cover is
  listed rather than silently included in an unconditional claim.

For example, a result might cover one Cargo target with a particular feature
set and dependency graph. It should say whether generated Rust, dependencies,
and calls into foreign code were checked, trusted, or outside its coverage.

When Anneal reports that a safe abstraction itself has been verified within a
stated semantic and build envelope, every type-correct safe use which the API
permits within that envelope should be safe—not only the calls which happened
to appear in one test or binary. Any assumptions on that claim must be listed
explicitly.

Verification does not mean that the program has no bugs. It applies only to
the guarantees and build configuration named in the result. Changing the
target, feature set, dependency, compiler configuration, or generated source
may require checking the program again.

For promises beyond Rust safety, Anneal checks whether the code satisfies the
specification it was given; it cannot decide whether that specification says
what its author truly wanted. A weak or mistaken specification can describe
the wrong behavior. It cannot, however, erase the Rust safety requirements
which Anneal is responsible for checking.

## Beyond Rust safety

Rust safety is only one part of program correctness. A memory-safe function can
still return the wrong answer or panic unexpectedly. Anneal also aims to check
additional promises, for example:

- a parser returns the value described by its input;
- an operation does not panic when its documented requirements hold;
- a data structure preserves the rules expected by its public API; or
- an implementation follows an application or network protocol.

Each promise must be stated precisely enough to prove. Anneal should make
common cases approachable while leaving Lean available for specifications and
proofs which need its full expressive power.

## Incremental adoption

Adopting formal verification across an existing codebase takes time. Anneal
lets teams begin with their highest-risk code and expand coverage gradually.

During that process, some unsafe operations may still rely on prose
`// SAFETY:` comments, unfinished proofs, or trusted external behavior. Anneal
reports those portions honestly rather than treating them as machine-checked
facts. This lets a team see what has been proved and what work or trust remains.

## Under the hood: Lean

Lean checks Anneal's mathematical arguments. Some specifications or advanced
proofs may be written directly in Lean, while Anneal connects them to the Rust
program and presents useful obligations and diagnostics to Rust developers.

Lean can check only the statement it receives. A meaningful result therefore
also depends on Anneal connecting that statement to the right Rust program and
reporting any external assumptions. Users should not need to understand the
translation machinery, but they must be able to see the assumptions and gaps
which qualify a result.

## Repository development

Coding agents working on Anneal must begin with [`AGENTS.md`](AGENTS.md). It
routes them into `agent_docs/`, an internal corpus written for agent
consumption. That corpus contains design context, current implementation facts,
and operating guidance which are intentionally omitted from this user-facing
introduction. Human maintainers may consult it, but it is not part of Anneal's
user documentation or a stable product interface.
