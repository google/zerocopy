# Rust undefined behavior and experimental operational models at the 2026-05-31 toolchain

## Summary

At the Rust toolchain revision relevant to Anneal's pinned 2026-05-31
toolchain, Rust has authoritative language rules about many forms of undefined
behavior, but it does **not** have a complete formal operational semantics for
unsafe Rust. The Rust Reference explicitly says both that its undefined-behavior
list is non-exhaustive and that there is no formal model deciding everything
unsafe code may do. Its memory-model chapter separately warns that Rust's memory
model is incomplete and not fully decided.

That distinction matters for Anneal. A verifier cannot equate "the cases listed
on the Reference UB page" with "a complete mathematical definition of Rust
behavior." The Reference is the primary language reference and is the right
source for established language requirements, but important regions remain
deliberately unsettled, especially exact aliasing rules, parts of pointer
provenance, union/reference validity details, and runtime assumptions.

Miri occupies a different role. In the same Rust source revision, Miri describes
itself as an undefined-behavior detection tool that uses its own approximation of
what is and is not UB. Its README directs users to the Reference for the official
definition, says Miri does not catch every violation, and makes no promise about
future compiler versions. Miri's aliasing checks are explicitly experimental:
Stacked Borrows is experimental, and Tree Borrows is an optional alternative
described as even more experimental.

Stacked Borrows and Tree Borrows therefore provide concrete, executable
candidate operational rules for important parts of Rust's aliasing semantics;
they are not interchangeable with the language definition. A Miri rejection
under one of these models is strong evidence about that model and often exposes
real bugs, but the model's experimental rules must not silently become an Anneal
axiom about Rust. Conversely, acceptance by Miri is not proof of soundness or
UB-freedom: Miri checks particular executions and explicitly documents missing
behaviors and unsupported operations.

The Unsafe Code Guidelines repository is likewise not a parallel specification.
At the examined UCG revision, its README says the repository is primarily a forum
for open operational-semantics questions, that most of the old UCG reference has
been archived, and that current consensus is documented in t-opsem FCPs and the
Rust Language Reference. Its surviving glossary is useful explanatory material,
but it repeatedly labels exact provenance and aliasing details as unresolved.

No fresh Miri or compiler execution was performed for this report. Its purpose is
to establish the authority boundary among the Reference, open operational-
semantics work, and executable experimental models.

## Applicability

The Rust source subject is
`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the Rust source
revision associated with the 2026-05-31 toolchain era used by Anneal/Charon.
That Rust tree pins the Rust Reference submodule to
`rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`; those exact
Reference files are the basis for the language-rule findings below.

Miri is examined as the source bundled under
`rust-lang/rust@14210df0e…/src/tools/miri`. This report does not infer
continuity to newer Miri releases merely because Miri normally tracks rustc
closely.

The Unsafe Code Guidelines repository is examined separately at
`rust-lang/unsafe-code-guidelines@d809f91e62968913d808e53397fbcf7cea762cce`.
That revision is not presented as part of the 2026-05-31 Rust distribution. It
is included to establish the role the UCG repository itself claims for current
unsafe-code semantics work.

This report uses **authoritative language rule** for rules stated by the Rust
Reference as requirements of Rust programs. It uses **experimental operational
model** for executable/modeling machinery such as Stacked Borrows and Tree
Borrows that explores or approximates unresolved semantics. This terminology
does not claim that the Rust Reference is a complete formal specification; the
Reference itself says it is incomplete in the relevant area.

## Findings

### The Rust Reference is primary language authority, but its UB account is intentionally incomplete

The pinned Reference introduces itself as "the primary reference for the Rust
programming language." It states that observable behavior of compiled programs
must conform to the Reference even though the Reference does not prescribe which
optimizations a compiler may perform.

The undefined-behavior chapter then states a stronger limitation that is central
for verification: its UB list is not exhaustive and may grow or shrink. It says
there is no formal model of Rust semantics that completely decides what unsafe
code may do.

Thus two claims must remain separate:

1. A behavior the Reference identifies as UB is a language-level prohibition for
   the subject revision.
2. Absence from the listed inventory does not establish that the behavior is
   defined.

Basis: **normative** Rust Reference language rules plus the Reference's own
explicit incompleteness warning.

### The Reference's explicit UB inventory covers broad classes, not a complete operational semantics

At the pinned Reference revision, the top-level UB inventory includes:

- data races;
- loading from or storing to dangling or sufficiently misaligned places;
- place projections that violate in-bounds pointer-arithmetic requirements;
- violation of pointer aliasing rules, while explicitly saying the exact rules
  are not yet determined;
- mutation of bytes that Rust requires to remain immutable;
- UB triggered through compiler intrinsics;
- executing code compiled for unsupported target features, absent a documented
  exception;
- calling a function with the wrong ABI or unwinding across a frame that forbids
  it;
- producing invalid typed values;
- incorrect inline-assembly use;
- violating Rust-runtime assumptions, most of which the Reference says are not
  yet explicitly documented.

The chapter further defines important pieces of danglingness, alignment and
validity. It says, for example, that references and `Box<T>` must be aligned,
non-null and non-dangling and point to valid values, but also records live debate
over some validity details. Union validity is expressly not fully decided.

This page is therefore both a set of enforceable language constraints and a map
of unresolved semantics. A verifier should preserve both aspects.

Basis: **normative** + explicit **documentation of uncertainty** in the Rust
Reference.

### Aliasing is a known semantic gap rather than an unspecified implementation detail Anneal can ignore

The Reference says breaking the pointer aliasing rules is UB, but immediately
states that the exact aliasing rules are not determined yet. It gives only an
outline: shared references generally prohibit mutation of their reachable
non-`UnsafeCell` data while live; mutable references require stronger
exclusivity; `Box<T>` is treated similarly to a long-lived mutable reference for
these purposes; and the exact liveness duration remains partially unspecified.

This is different from a behavior the language intentionally leaves arbitrary to
implementations. The Reference identifies aliasing as a UB boundary while
acknowledging that the exact boundary has not been fully specified.

For Anneal, a complete UB-freedom proof cannot simply omit aliasing because the
Reference lacks a final formal rule. A design must either rely on an explicitly
trusted assumption/model for this gap, restrict the supported behavior, or
eventually replace that trust with stronger evidence. Which mechanism Anneal
chooses is a design question; the external fact is that the language boundary is
real and incompletely formalized.

Basis: **normative** + **derived** implication for what a Rust-level proof must
account for.

### The Reference memory model contains some settled abstractions while explicitly remaining incomplete

The pinned `memory-model.md` begins with a warning that Rust's memory model is
incomplete and not fully decided. It nevertheless specifies useful abstract
structure: Rust memory uses abstract bytes that may be initialized or
uninitialized and may carry optional provenance. These distinctions need not be
present as hardware bits; they can still affect whether program behavior is
defined.

This illustrates the general shape of current Rust semantics: the language
already commits to abstract-machine state beyond raw machine bytes, while the
full rules governing that state are still under development.

Basis: **normative** Rust Reference.

### Pointer provenance is semantically relevant, but its exact model is not fully settled

The Reference UB chapter includes provenance-related requirements in const
evaluation and uses provenance-aware concepts in its memory model. The UCG
glossary gives the useful abstract-machine intuition that pointers can contain
state beyond their numerical address and that this state can distinguish two
pointers with the same address.

However, the UCG glossary explicitly says the exact form of provenance in Rust is
unclear. It also says the exact aliasing model has not yet been defined. The
glossary is explanatory and historical/current-research context, not a substitute
for the Reference or t-opsem decisions.

Therefore Anneal must not infer a complete pointer model merely from the word
"provenance" appearing in the Reference, nor elevate one particular UCG example
into a language guarantee without the corresponding accepted rule.

Basis: **normative** Reference + **documentation** from UCG.

### The current UCG repository points away from itself as normative authority

At `rust-lang/unsafe-code-guidelines@d809f91e…`, the README says the
repository's purpose is to collect and discuss questions arising in unsafe code
and that it is primarily used by the operational-semantics team to track open
questions. It describes the former UCG Reference book as a past effort, mostly
archived, and says current consensus is documented in t-opsem FCPs and the Rust
Language Reference.

This establishes a useful research hierarchy:

1. accepted/current language rules: Rust Reference and accepted t-opsem process
   outputs;
2. implementation/compiler evidence: rustc and associated source/tests;
3. experimental operational models: Miri and specific aliasing/provenance models;
4. UCG issues/glossary/history: research context and terminology, not independent
   language authority.

The exact authority of a particular t-opsem FCP must be assessed from that FCP;
this report does not attempt to inventory all FCPs.

Basis: **documentation** from the UCG repository.

### Miri is an executable UB detector, not the definition of Rust semantics

The pinned Miri README calls Miri an Undefined Behavior detection tool. It lists
checks for out-of-bounds/use-after-free, uninitialized data, intrinsic
preconditions, alignment, basic validity, data races and some weak-memory
effects, plus experimental aliasing checks.

The same README then gives explicit limits:

- Miri does not catch every violation of Rust's rules.
- There is no complete Rust specification for Miri to implement.
- Miri uses its own approximation of what is and is not UB.
- Users should consult the Reference for the official UB definition.
- Miri makes no promises about future rustc versions.
- One Miri execution explores only one of potentially many nondeterministic
  executions.
- Many platform APIs and most FFI are unsupported.
- Weak-memory emulation is incomplete.
- Miri cannot establish that a library is sound from passing tests.

This makes Miri valuable evidence but unsuitable as an unqualified
"Rust-semantics oracle."

Basis: **documentation** from the pinned Miri README.

### Miri distinguishes definite checks from experimental aliasing checks

Miri's README separates many checks from aliasing-model experiments. It labels
Stacked Borrows violations **Experimental** and Tree Borrows violations
**Experimental**, with Tree Borrows presented as an optional alternative.

The command-line interface reflects that status. Borrow tracking can be disabled,
and `-Zmiri-tree-borrows` switches from Stacked Borrows to Tree Borrows. The
README says Tree Borrows is even more experimental than Stacked Borrows. It also
says Tree Borrows is intended to catch aliasing violations exploited by current
compilers while likely being more permissive than the eventual final Rust model:
code accepted under Tree Borrows today may still become UB under a stricter final
model.

Thus:

- a Stacked/Tree Borrows rejection establishes a violation of the selected
  experimental model;
- it does not, by that fact alone, establish that the Rust Reference has already
  fixed that exact rule;
- acceptance does not establish future-defined behavior.

Basis: **documentation** + **source** presence of the two borrow-tracking modes.

### Stacked Borrows and Tree Borrows are candidate aliasing semantics with different purposes and permissiveness

The pinned Miri source contains separate borrow-tracking implementations and a
runtime choice between the models. Both enrich pointer/provenance state with
tracking needed to enforce aliasing restrictions that ordinary hardware does not
represent.

Stacked Borrows is the older and more established experimental model in Miri.
Tree Borrows is an alternative intended to model aliasing with a tree-shaped
permission structure and, at this revision, is deliberately more experimental.

For verification work, the important reusable fact is not which model Anneal
"should" choose. It is that Rust's final aliasing semantics are not yet fully
specified, while Miri provides executable candidate models that encode
substantially more structure than the current Reference prose.

Basis: **source** + **documentation**; no Anneal design conclusion is implied.

### Miri success and Miri failure have asymmetric evidentiary value

Miri's own documentation says that finding UB demonstrates a real problem under
the non-experimental checks, subject to tool bugs, while passing a test does not
prove a library sound. Miri evaluates concrete executions and can miss behaviors
that require other inputs, schedules, addresses or unsupported platform
operations.

For experimental aliasing rules, even a rejection must be qualified by the
chosen model's status. A practical evidence taxonomy is therefore:

- **Reference violation:** direct evidence that the source execution violates an
  established language rule, once correspondence from the program to that rule
  is justified.
- **Miri definite-model rejection:** executable evidence of a behavior Miri
  currently treats as UB; often strong bug evidence, but still mediated by Miri's
  implementation and coverage.
- **Stacked/Tree Borrows rejection:** executable evidence against that candidate
  aliasing model; not automatically a settled Rust rule.
- **Miri acceptance:** absence of a detected problem in the executions explored,
  not proof of UB-freedom or soundness.

This taxonomy is **derived** from the primary documentation and is useful for
keeping future Anneal evidence claims from collapsing unlike sources.

## Boundaries

- **The Rust UB list is not exhaustive.** The Reference says this directly.
  Therefore this report does not provide a closed enumeration that can be copied
  into a verifier and called complete.
- **No complete formal Rust operational semantics is identified.** The Reference
  explicitly says there is no formal model deciding all unsafe-code behavior, and
  the memory-model chapter says the model is incomplete.
- **Exact aliasing remains unsettled.** Stacked Borrows and Tree Borrows are
  experimental models. Their differences and full formal rules are not
  reproduced here.
- **Pointer provenance is only partially pinned down.** The report establishes
  that provenance is semantically relevant and that current explanatory material
  leaves its exact form open. It does not define Anneal's provenance logic.
- **The t-opsem FCP corpus was not exhaustively inventoried.** UCG's README points
  to t-opsem FCPs as a source of current consensus, but this report does not claim
  that every accepted operational-semantics decision is already mirrored in the
  Reference.
- **No fresh Miri execution was performed on this surface.** Claims about Miri
  behavior here come from pinned source/documentation, not newly observed runs.
- **Concurrency semantics are not exhaustively covered.** The Reference names
  data races as UB and Miri implements some weak-memory exploration, but this
  report does not specify Rust's complete atomic/concurrent memory model.
- **Library safety invariants are not the same as language validity.** The report
  focuses on language UB and operational models, not every library-level safety
  contract that safe APIs may assume.

## Evidence

**Normative — Rust Reference.**
`rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`:

- `src/introduction.md`: identifies the book as Rust's primary reference and
  explains its relationship to observable language behavior.
- `src/behavior-considered-undefined.md`: defines the explicit UB inventory,
  states that the inventory is non-exhaustive, records the lack of a formal
  unsafe-code semantics, and marks unresolved aliasing/validity/runtime details.
- `src/memory-model.md`: states that the memory model is incomplete and not
  fully decided while defining abstract initialized/uninitialized bytes and
  optional provenance.

**Source — Rust distribution linkage.**
`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` pins
`src/doc/reference` to
`rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

**Documentation/source — Miri.**
`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`,
`src/tools/miri/README.md`, especially the opening UB inventory and caveats,
the `-Zmiri-disable-stacked-borrows` and `-Zmiri-tree-borrows` flag
documentation, and the explicit classification of Stacked/Tree Borrows as
experimental.

The same tree's `src/tools/miri/src/borrow_tracker/` source contains the
borrow-tracking machinery, including Tree Borrows state/retagging logic. This is
implementation evidence that the experimental models are executable interpreter
semantics rather than merely prose proposals.

**Documentation — Unsafe Code Guidelines.**
`rust-lang/unsafe-code-guidelines@d809f91e62968913d808e53397fbcf7cea762cce`:

- `README.md`: describes UCG as a discussion/open-question repository, calls
  the old reference book a past effort, and directs current consensus to t-opsem
  FCPs and the Rust Reference.
- `reference/src/glossary.md`: explains abstract bytes, provenance, aliasing and
  UB while explicitly recording unresolved exact provenance and aliasing rules.

**Derived.**
The evidence hierarchy and asymmetric interpretation of Miri acceptance/rejection
follow from the sources above. Those derived statements are not themselves Rust
language rules.

## Revalidation

For a later Rust toolchain:

1. Resolve the exact `rust-lang/rust` revision and its
   `src/doc/reference` submodule revision.
2. Diff the Reference's
   `behavior-considered-undefined.md`, `memory-model.md`, and introduction.
   Pay special attention to whether the non-exhaustiveness warning, aliasing
   uncertainty, provenance rules, validity rules, runtime assumptions, or memory-
   model warning changed.
3. Diff the bundled Miri README's opening UB inventory and all borrow-tracking
   flags. Record whether Stacked Borrows or Tree Borrows changed default status,
   experimental status, or stated relationship to compiler behavior.
4. Diff the Miri borrow-tracker implementation enough to identify newly added or
   removed models and any major semantic switches.
5. Check current UCG/t-opsem documentation to see whether a formerly open
   question acquired an accepted FCP or Reference rule. Do not infer consensus
   merely from an issue or experiment.

On a surface capable of execution, a compact revalidation suite should run the
exact bundled Miri against preserved examples that distinguish:

- Reference-settled UB such as use-after-free, invalid `bool`, and misalignment;
- a Stacked-Borrows-specific aliasing rejection;
- a case accepted/rejected differently by Tree Borrows;
- nondeterministic concurrency under several Miri seeds.

Record the exact rustc/Miri revision and flags. Such runs would confirm the
executable behavior of that Miri revision. They would **not** convert experimental
aliasing rules into settled Rust semantics, and successful runs would not prove
soundness or exhaustively establish UB-freedom.
