<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Verification results

This document defines the semantic meaning of an Anneal verification result. It
derives from the project [principles](../PRINCIPLES.md) and
[design contract](../DESIGN.md); those documents remain authoritative if this
one conflicts with them.

The purpose here is to say what Anneal is asserting when it reports successful
verification. This document deliberately does not choose an atomic compilation
subject, a property taxonomy, a proof encoding, a result serialization, a
command-line policy, or a source/model adequacy construction.

## The semantic core

An ordinary successful Anneal verification result has two semantic parts:

1. an exact **claim** about program behavior; and
2. the claim-relative **trusted computing base (TCB)** on whose correctness that
   claim depends.

Its meaning is:

    if every dependency in the TCB is correct, then the claim is true.

For code in the TCB, “correct” means that the code behaves in the way the result
relies upon. For an assumption in the TCB, it means that the assumption is true.
This is the result-level form of Anneal's promise in
[PRINCIPLES.md](../PRINCIPLES.md).

Checked proofs, validations, and other evidence explain why Anneal is entitled
to issue this result with this claim and this TCB. They are not an additional
kind of promise. Likewise, an intermediate theorem about a generated model is
evidence toward a Rust-level result; successfully checking that theorem does not
by itself turn it into a claim about the Rust program.

## The claim

The claim is the complete proposition Anneal stands behind. It must identify
what program or behavior it concerns and state the promise precisely enough that
a reader cannot silently generalize it to something Anneal did not establish.

A claim may need to say which inputs or clients it quantifies over, which
behaviors it covers, which configuration it concerns, or which execution
semantics it talks about. These are examples of information a claim may need,
not a fixed list of independent “verification dimensions.” Future properties
should be expressible without changing the core result model merely because they
need a different shape of proposition.

Program-level conditions belong in the claim. For example, if Anneal establishes
“if a caller satisfies precondition A, then behavior P follows,” it is asserting
the implication; it is not asserting that A holds for every caller. This is
different from Anneal asserting P while relying on an unproved fact A. In the
latter case, A is a trusted dependency and belongs in the TCB.

This distinction prevents trust from disappearing through presentation. Moving
a premise into the wording of a claim is legitimate only when Anneal is actually
making a weaker or more conditional promise and that change is visible to the
consumer of the result.

For Rust-level verification, well-defined behavior remains foundational and
always on as required by the principles. Additional developer-defined
correctness properties add promises; they do not replace the well-definedness
basis needed to interpret them as claims about Rust.

For a developer-defined property, Anneal establishes the proposition that was
specified. It does not additionally establish that the proposition captures the
developer's real-world intent.

## The TCB

The TCB is relative to a particular claim. It contains the code, assumptions,
models, external semantics, tools, platforms, or other dependencies whose
correctness Anneal relies on without establishing that correctness in the
evidence supporting this result.

A component is therefore not intrinsically “trusted” in all contexts. A
dependency may matter to one claim and be irrelevant to another. The detailed
roles and categories of trusted dependencies can be designed later without
changing this definition.

Stronger evidence can shrink the TCB without changing the claim. For example, a
trusted semantic specification might later be replaced by a checked proof of the
same specification. The promise to the user can remain the same while the set of
things that must be trusted becomes smaller.

Moving an unchecked dependency into generated code, another tool, or an upstream
project does not shrink the TCB if the same result still depends on that
unchecked correctness.

Any user-facing audit representation must preserve which trusted dependencies
qualify which claims. This document does not choose the audit-log schema,
identity scheme, serialization, or presentation.

## Evidence, trust, and blockers

Anneal issues an ordinary verification result only when accepted machine-checked
evidence establishes the claim relative to its TCB.

Not every missing piece of evidence is therefore another kind of trust. An
unfinished proof, unsupported semantics, missing coverage, or a model or tool
failure does not automatically become a TCB entry. For the affected claim, such
a condition is a blocker unless one of two things happens explicitly:

- Anneal reports a different, genuinely narrower claim that the available
  evidence does establish; or
- an applicable trust policy deliberately permits a specific premise to be
  admitted into the TCB.

Either change must remain visible. An unresolved obligation must never turn into
an assumption merely because treating it that way lets verification continue.

This document does not decide which premises a production or incremental policy
may admit. That policy remains constrained by the higher-level principles. In
particular, a development-only bypass of Anneal's mandatory undefined-behavior
checks cannot masquerade as an ordinary successful verification result covered
by Anneal's promise.

A verifier or model failure is likewise not a behavior of the source program. It
can explain why Anneal failed to establish a claim, but it is not evidence that
the program satisfies or violates that claim.

## Broader command output

A verification invocation may produce more than ordinary successful verification
results. It may report incomplete obligations, unsupported constructs, failed
tools, development-mode information, or narrower claims that were established
even though a requested stronger claim was not.

Those outputs are useful, especially during incremental adoption, but they must
remain distinguishable from an ordinary successful result with the semantics
defined above. The exact command names, exit statuses, warning policies, and
machine-readable representation of partial information remain separate design
questions.

Likewise, the exact relation between requested properties and reported results
is not fixed here. Whatever policy is chosen must not let “no errors” communicate
a promise stronger than the results actually establish.

## What this document leaves open

This model intentionally does not decide:

- what the atomic subject of verification is or how build matrices are grouped;
- how generated source and other generated artifacts participate in that
  subject;
- a fixed decomposition of claims into property, behavior, client, coverage, or
  execution-endpoint axes;
- the taxonomy of trusted dependencies;
- which assumptions are admissible in production, incremental, or development
  modes;
- how proofs, validations, or other evidence are structured and composed;
- how Anneal proves source/model correspondence or complete obligation coverage;
- the contents and serialization of the TCB audit log;
- canonical result identity, hashing, provenance, or reproducibility rules; or
- command names, profiles, warnings, exit codes, and CI policy.

Those choices may add structure around a verification result. They must preserve
the semantic core: an exact claim and an explicit claim-relative TCB. Anneal
must have sufficient evidence to stand behind the implication from that TCB to
that claim.
