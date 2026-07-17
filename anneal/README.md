<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal V2

Anneal is being built to help Rust developers prove that unsafe implementations
uphold the guarantees expected of safe Rust.

> **Status:** Anneal V2 is under active construction and cannot yet verify
> applications. The checked-in executable currently has only `setup`
> infrastructure for installing its bundled compiler and proof tools. Its
> remote download metadata is placeholder data, so development currently uses
> a locally supplied archive. The Rust example below illustrates the problem
> Anneal is intended to solve, not a workflow available today.

## Why Anneal exists

Rust's safe APIs promise that ordinary, type-checked use will not cause
undefined behavior—for example, an invalid memory access or a data race. Safe
code can still panic, run forever, or produce the wrong answer, but a safe API
must uphold that safety promise even when it uses unsafe code internally.

Unsafe Rust lets a programmer perform operations that the compiler cannot
prove are valid. Each such operation comes with requirements: a pointer might
need to refer to live memory, an index might need to be in bounds, or a value
might need to be initialized. The compiler accepts the operation because the
programmer takes responsibility for those requirements.

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
removed or moved too late, the unsafe operation may become invalid while the
comment continues to look reassuring.

Because `get_byte` is a safe function, callers may pass any `usize`. An
out-of-bounds call may panic at the assertion, but it must never cause undefined
behavior. A safe API cannot place a hidden safety requirement on its caller.

Anneal is intended to check reasoning like this instead of trusting the comment
alone.

This is intentionally a tiny example; ordinary Rust should simply use
`bytes[index]`. It stands in for implementations which cannot avoid unsafe
operations. It contains no Anneal-specific syntax because V2's specification
and proof-authoring interface is still being designed.

## What Anneal is intended to add

Anneal V2 is intended to let a project describe:

- the requirements a caller must satisfy before using an unsafe API;
- the promises a function or type makes to its callers; and
- the reasoning which connects ordinary Rust code to those requirements and
  promises.

Anneal would then check every Rust safety obligation in the claimed scope,
including the requirements of unsafe operations and the promises on which safe
APIs rely. It would follow those promises through function calls, so a verified
implementation could be used through its API without every caller re-examining
its private unsafe code.

For a safe abstraction, the goal is straightforward: callers should be able to
use the safe API according to the normal Rust type system, with no hidden rule
whose violation could cause undefined behavior. An unsafe API may explicitly
give part of that responsibility to its caller—for example, through a function
declared `unsafe` with documented requirements.

## What a verification result should mean

The exact report format and command behavior are not yet finalized. At a
minimum, a successful Anneal result should tell you that, for the code and
build it names:

- every safety-relevant operation within the claimed coverage satisfies Rust's
  requirements;
- the functions and types checked by Anneal keep the promises stated in their
  specifications; and
- anything Anneal could not prove, deliberately trusted, or did not cover is
  clearly listed rather than silently included in an unconditional claim.

For example, a result might cover one Cargo target with a particular feature
set and dependency graph. It should say whether generated Rust, dependencies,
and calls into foreign code were checked, trusted, or outside its coverage.

When Anneal reports that a safe abstraction itself has been verified, every
type-correct use from safe client code allowed by its API within the named
configurations should be safe—not only the call sites which happened to appear
in a test or one binary, and subject to any assumptions the result explicitly
lists.

Verification is not a claim that the program has no bugs. It applies to the
specific guarantees and build configuration named in the result. Changing a
target, feature set, dependency, compiler configuration, or generated source
may require checking the program again.

For user-defined promises beyond Rust safety, Anneal can check whether code
keeps the promises written in its specification; it cannot decide whether
those promises express what the author truly wanted. A weak or mistaken
specification can still describe the wrong behavior. It cannot, however, erase
the Rust safety requirements that Anneal itself is responsible for checking.

## Beyond Rust safety

Rust safety is only one part of program correctness. A memory-safe function can
still return the wrong answer or panic unexpectedly. Anneal's long-term scope
includes checking additional promises, for example:

- a parser returns the value described by its input;
- an operation does not panic when its documented requirements hold;
- a data structure preserves the rules expected by its public API; or
- an implementation follows an application or network protocol.

Each promise still has to be stated precisely enough to prove. Anneal should
make common cases approachable, while leaving Lean available for specifications
and proofs which need its full expressive power.

## Incremental adoption

Adopting formal verification across an existing codebase takes time. Anneal is
intended to let teams begin with their highest-risk code and expand coverage
gradually.

During that process, some unsafe operations may still rely on prose
`// SAFETY:` comments, unfinished proofs, or trusted external behavior. Anneal
should report those portions honestly rather than silently treating them as
machine-checked facts. This lets a team see what has been proved and what work
or trust remains.

## Where Lean fits

Anneal's proofs will ultimately be checked by
[Lean](https://lean-lang.org/), a language which mechanically checks
mathematical arguments. Some specifications or advanced proofs may be written
directly in Lean. Anneal's role is to connect those proofs to the Rust program,
identify what must be proved, and present useful results and diagnostics to
Rust developers.

Lean can only check the mathematical statement it receives. A meaningful
result therefore also relies on Anneal correctly connecting that statement to
the Rust program and on any explicitly listed external assumptions. Users
should not need to understand the translation machinery, but the result must
make its remaining assumptions and gaps visible.

The exact proof-authoring experience is still being designed. Its internal
architecture is documented separately for contributors.

## Current state

V2 is not currently an application verifier at all. It cannot yet select a
Cargo target, generate or check application proofs, or produce a verification
report. No invocation of the checked-in V2 executable currently proves that an
application is safe or correct.

V2 is a ground-up redesign of the experimental V1 prototype. V1 remains in
[`v1/`](v1/README.md) as historical implementation and design evidence; its
interfaces and behavior should not be treated as promises about V2.
Neither version should currently be treated as a production verifier.

See the [current architecture](docs/reference/current-architecture.md) and
[current limitations](docs/reference/current-limitations.md) for an exact
account of what is implemented today.

## Developing Anneal

See [V2 development and CI](docs/reference/development-and-ci.md) for setup,
build, and test instructions.

Contributors and coding agents should also read [`AGENTS.md`](AGENTS.md) and
the [design documentation](docs/README.md). Those documents contain the
translation architecture, detailed trust model, and unresolved design
questions which are intentionally omitted from this introduction.
