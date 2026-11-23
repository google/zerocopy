<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# MIR Semantics and Reference Correspondence Strategy

> **Note:** Anneal is under active development. This document sets out the
> correspondence strategy and target Lean formalization design; the concrete
> MIR semantics, reference model, `cargo anneal verify`, Pass 2
> (`anneal-audit --require-correspondence`), and correspondence modules land
> incrementally across the MIR correspondence stack.

Anneal verifies Rust programs by stating its top-level whole-crate and
proof-unit verification obligations (`Trusted.CrateTheorem` and
`Trusted.UnitTheorem`) over an operational semantics for Rust's Mid-level
Intermediate Representation (MIR) inside the Lean 4 kernel. Because that MIR
semantics defines what it means for a program to be free of undefined behavior
(UB) and to satisfy a functional specification, any soundness bug in Anneal's
MIR semantics directly undermines Anneal's correctness promise.

This document describes the strategy for building Anneal's MIR semantics
incrementally while guarding against semantic bugs through a machine-checked
correspondence proof against an established reference model in continuous
integration (CI).

## 1. The core problem: verification ergonomics vs. semantic trust

A MIR operational semantics for Anneal must satisfy two competing requirements:

1. **Ergonomic symbolic reasoning in Lean 4:** Proving properties of real Rust
   functions requires a semantics structured for symbolic evaluation,
   compositional framing, and proof automation. As Anneal matures, this
   semantics ($M_{\text{anneal}}$) will be iteratively extended, refactored,
   and optimized for proof performance—often by AI coding agents.
2. **High confidence in Rust semantic fidelity:** Rust's operational semantics
   contains many subtle rules across integer and pointer arithmetic, niche and
   padding representations, place projections, borrow and aliasing state
   machines, drop elaboration, and unwinding. When contributors or AI agents
   implement or optimize $M_{\text{anneal}}$ under pressure to make verification
   proofs pass, both accidental oversights and optimization incentives push
   toward omitting inconvenient UB checks or oversimplifying corner cases.

Verifying user programs directly against an external reference interpreter or
specification (such as `lean-miri` or `MiniRust`) avoids writing a custom
semantics, but those models are structured as literal interpreters or reference
documents rather than compositional verification targets in Lean 4. Conversely,
writing $M_{\text{anneal}}$ from scratch and relying on human reviewers to
catch every missing UB check or behavioral divergence across tens of thousands
of lines of Lean definitions does not scale reliably.

Anneal resolves this tension by maintaining **both** models and connecting them
with locked correspondence and fault-equivalence theorems in CI:

- **Anneal's MIR semantics ($M_{\text{anneal}}$):** Designed and iteratively
  evolved for verification ergonomics in Lean 4, and treated as potentially
  buggy during development.
- **A reference MIR model ($M_{\text{ref}}$):** An existing external
  formalization (`lean-miri`, `MiniRust`, or a combination of reference models;
  Anneal's target architecture adopts a pinned `lean-miri` snapshot, see
  [`development/architecture.md`](architecture.md)) landed in the repository and
  audited once up front for both Rust semantic fidelity and faithful
  transcription/vendoring from upstream (with its small staged support gate
  widened under human review as coverage grows within $M_{\text{ref}}$'s
  supported features, or $M_{\text{ref}}$ itself extended under Section 4.2
  when moving beyond them).

## 2. The three-step development strategy

Rather than implementing a large portion of $M_{\text{anneal}}$ first and
attempting to retrofit correspondence proofs afterward, Anneal establishes the
reference model and the end-to-end correspondence claims **first**, before
iteratively implementing MIR features.

### Step 1: Land the reference model ($M_{\text{ref}}$)

First, we land a reference MIR semantics ($M_{\text{ref}}$)—the strategy is
agnostic among `lean-miri`, `MiniRust`, or a combination, and Anneal's target
architecture adopts `lean-miri`—in the repository. Because $M_{\text{ref}}$ is
transcribed or adapted from an existing external specification rather than
invented alongside Anneal's proof tactics, human reviewers can audit
$M_{\text{ref}}$'s underlying semantics once up front.

### Step 2: Define the core MIR representation and execution outcomes

Second, we define the core MIR representation and execution semantics for
$M_{\text{anneal}}$. In addition to normal progress and termination outcomes,
executions in $M_{\text{anneal}}$ distinguish at least two failure outcomes:

- **`undefined`:** The program executed a construct that $M_{\text{anneal}}$
  models and violated Rust's operational rules (exhibiting undefined behavior).
- **`unsupported`:** The program reached a construct, type, operation, or
  execution mode that $M_{\text{anneal}}$ does not model, or an execution that
  $M_{\text{anneal}}$ conservatively rejects because it enforces a simpler rule
  than full Rust.

For verification soundness, both `undefined` and `unsupported` act as failure
outcomes: a program verified by Anneal is not permitted to reach either outcome.
Splitting them into distinct outcomes serves developer experience and
engineering diagnostics:

- Reporting `undefined` tells the user that their program exhibits UB under the
  modeled semantics.
- Reporting `unsupported` tells the user (and Anneal developers) that the
  program may be valid Rust, but uses a feature that $M_{\text{anneal}}$ does
  not yet implement or falls outside a simplified rule that
  $M_{\text{anneal}}$ enforces.

### Step 3: Lock the correspondence claims in CI and grow $M_{\text{anneal}}$

Third, we state and lock the correspondence and fault-equivalence theorems in
CI before implementing the bulk of MIR, anchored by the core correspondence
property:

> **Correspondence Theorem (Informal):** For every program $p$ and every input
> query $q$, if $p$ is well-formed on $q$ according to $M_{\text{anneal}}$
> (meaning that no execution of $p$ from $q$ reaches `undefined` or
> `unsupported`), then $p$ is also well-formed on $q$ according to
> $M_{\text{ref}}$, and every observable behavior that $M_{\text{ref}}$ permits
> for $p$ on $q$ is also a behavior of $p$ on $q$ in $M_{\text{anneal}}$.

Two features of this statement carry its soundness.

First, both models execute the same program environment and input. Each program
$p$ carries its captured target environment (`CaptureManifest` in
[`development/architecture.md`](architecture.md): compiler version, target layout such
as pointer width, endianness, type sizes, alignments, and field offsets, and the
active semantic profile), which both models enforce and which any program
translation preserves identically. The theorem quantifies universally over all
programs $p$ (including that environment) and all input queries $q$ (function
arguments and initial caller-visible memory), sharing $q$ directly while either
sharing $p$'s representation or passing $p$ through a total,
structure-preserving, TCB-audited translation $\tau_{\text{prog}}$ (`encodeProg`
in Anneal's target design; see Section 4.3). Each model constructs its initial
state directly from the shared input—`initState` from $(p, q)$ for
$M_{\text{anneal}}$ and `initRefState` from $(\tau_{\text{prog}}(p), q)$ for
$M_{\text{ref}}$—so an unverified precondition or filtering conversion on $p$ or
$q$ cannot discard or sanitize the target layouts, profiles, or inputs that
trigger UB, leaving every remaining reference execution trivially safe.

Second, behavioral inclusion runs from $M_{\text{ref}}$ into
$M_{\text{anneal}}$. Writing $\mathsf{Behavior}_{\text{anneal}}(p, q)$ and
$\mathsf{Behavior}_{\text{ref}}(p, q)$ (abbreviating
$\mathsf{Behavior}_{\text{ref}}(\tau_{\text{prog}}(p), q)$ when
$\tau_{\text{prog}}$ translates $p$, and likewise
$\mathsf{WellFormed}_{\text{ref}}(p, q)$ for
$\mathsf{WellFormed}_{\text{ref}}(\tau_{\text{prog}}(p), q)$) for the sets of
observable behaviors (including divergence) that each model permits on
$(p, q)$, sound specification transfer requires behavioral refinement:

$$
\mathsf{Behavior}_{\text{ref}}(p, q) \subseteq
\mathsf{Behavior}_{\text{anneal}}(p, q)
$$

This is the backward-simulation direction of the `Abstracts` relation that
Anneal's verified lowering uses ([`development/architecture.md`](architecture.md)),
with $M_{\text{ref}}$ in the role of the concrete semantics and
$M_{\text{anneal}}$ in the role of its abstraction. Under
`CorrespondenceClaim` alone (which requires totality only in the
$M_{\text{ref}} \to M_{\text{anneal}}$ direction), a specification proved for
every behavior of $M_{\text{anneal}}$ holds for every behavior that
$M_{\text{ref}}$ permits, even if $M_{\text{anneal}}$ over-approximates
non-faulting outcomes. When both models are deterministic and productive under
the combined contract—or when nondeterministic models satisfy the unconditional
choice-coupled contract of Section 4.6 with reverse totality across all valid
executions—the relation strengthens to exact behavioral equivalence up to
$\sim_{\text{out}}$ on every $(p, q)$, under which each model permits a
behavior if and only if the other does:

$$
\mathsf{Behavior}_{\text{anneal}}(p, q) = \mathsf{Behavior}_{\text{ref}}(p, q)
$$

Even without reverse totality on non-faulting executions, imposing the
unconditional combined contract of Section 4.6 (including universal
bidirectional fault equivalence on coupled pairs, Case 1) rules out behavioral
over-approximation on any value or control-flow choice that a program inside
the gated fragment can inspect and turn into a fault; true behavioral
over-approximation—where
$\mathsf{Behavior}_{\text{ref}} \subsetneq \mathsf{Behavior}_{\text{abstract}}$
for a Stage 3 abstract semantics's behavior set
$\mathsf{Behavior}_{\text{abstract}}$—therefore belongs in Stage 3
(`StableAst` / `Abstracts` / `MirWp`), which is not subject to
`FaultEquivalenceClaim`.

The opposite inclusion alone,

$$
\mathsf{Behavior}_{\text{anneal}}(p, q) \subseteq
\mathsf{Behavior}_{\text{ref}}(p, q)
$$

would be unsound: if $M_{\text{ref}}$ admitted an extra nondeterministic
outcome, a postcondition proved over every behavior of $M_{\text{anneal}}$
would say nothing about that outcome.

In Anneal's target Lean formalization (`Trusted/MirSemantics.lean` and
`Trusted/Correspondence.lean`), this strategy is realized by two top-level
claims: `CorrespondenceClaim` states the core soundness implication—that
whenever a program and query are well-formed in $M_{\text{anneal}}$, they are
also well-formed in $M_{\text{ref}}$ and every finite terminal outcome and
diverging execution of $M_{\text{ref}}$ has a choice-coupled matching
execution in $M_{\text{anneal}}$ (strengthening to two-way outcome and
divergence agreement when both models are deterministic and productive)—and
`FaultEquivalenceClaim` anchors exact fault classification (`undefined` vs.
`unsupported`). Unconditionally across **every** program $p$ and input query
$q$ (without gating on $\mathsf{WellFormed}_{\text{anneal}}(p, q)$), the
combined locked correspondence and fault-equivalence contract requires a
faithful choice-coupled execution relation satisfying Cases 1–4 of
Section 4.6 with: (1) unconditional forward totality from $M_{\text{ref}}$ to
$M_{\text{anneal}}$ across **all** valid executions (faulting and
non-faulting alike), and (2) unconditional reverse totality on faulting
executions from $M_{\text{anneal}}$ to $M_{\text{ref}}$ (Section 4.6). In the
deterministic and productive setting, that unconditional contract reduces
cleanly to `CorrespondenceClaim` (gated on
$\mathsf{WellFormed}_{\text{anneal}}(p, q)$) plus unconditional bidirectional
fault-reachability equivalence across every $(p, q)$ (Section 4.6); under
nondeterminism, unconditional forward totality across all valid executions is
essential so $M_{\text{anneal}}$ cannot collapse a mixed succeeding/faulting
input into all-faulting executions while leaving `CorrespondenceClaim` vacuous.
Together, (1) and (2) suffice for verification soundness, exact fault
classification, and behavioral inclusion on every $(p, q)$; if nondeterminism
is introduced and exact behavioral equality on uninspectable entry-frame
boundary outcomes (such as uncaught unwind payloads or entry-frame returns) is
also desired, adding (3) reverse totality from $M_{\text{anneal}}$ to
$M_{\text{ref}}$ across all valid executions (not only faulting ones)
automatically yields exact behavioral equality across Cases 1–4 of Section 4.6
on every $(p, q)$.

Initially, both $M_{\text{anneal}}$ and $M_{\text{ref}}$'s staged support gate
(Section 4.6) can return `unsupported` for almost every MIR construct. Because
reaching `unsupported` falsifies $\mathsf{WellFormed}_{\text{anneal}}(p, q)$
and both models agree on `unsupported` outside the initial gate, both
correspondence claims are straightforward to prove on the initial skeleton.

Once these theorems are locked in CI, incremental development proceeds by
replacing `unsupported` branches in $M_{\text{anneal}}$ with concrete execution
rules (returning normal progress or `undefined`) and widening $M_{\text{ref}}$'s
small human-audited staged support gate one MIR feature at a time:

1. **The theorem statements stay fixed:** Adding support for a new MIR feature
   updates the execution rules of $M_{\text{anneal}}$, widens the staged
   support gate in $M_{\text{ref}}$'s correspondence wrapper (strictly replacing
   `unsupported` with delegation to the audited reference interpreter, never
   suppressing UB checks or narrowing existing coverage), adds positive and
   negative feature canaries whose exact theorem statements and concrete
   program, query, and expected-outcome fixture definitions live on the
   human-audited `Trusted.*` surface and are registered as required witness
   locks in `trusted/audit/` (Section 4.6, with only the canary proofs in
   untrusted `theory/` or `correspondence/`), and updates the correspondence
   and canary proofs—without changing `CorrespondenceClaim` or
   `FaultEquivalenceClaim` themselves. When a feature also adds a new
   `MirAst` constructor, outer boundary definition, or `encodeProg`/
   `evalRefStep` arm (see [`development/architecture.md`](architecture.md) and
   Section 4.3), those TCB additions receive the same human semantic review.
2. **CI polices soundness automatically:** Whenever a pull request changes a
   branch of $M_{\text{anneal}}$ from `unsupported` to an active execution
   rule, the Lean 4 kernel requires the pull request to prove that the new rule
   never succeeds on an execution where $M_{\text{ref}}$ faults, and never
   omits a behavior that $M_{\text{ref}}$ permits.

If implementing a new MIR feature in $M_{\text{anneal}}$ omits a UB check that
$M_{\text{ref}}$ enforces (for example, a division-by-zero, shift-overflow,
alignment, or aliasing guard), breaking the well-formedness implication, or
miscomputes a result so that $M_{\text{anneal}}$ omits a behavior that
$M_{\text{ref}}$ permits, breaking behavioral inclusion, the correspondence
proof fails to compile in CI.

The proof detects divergences between $M_{\text{anneal}}$ and
$M_{\text{ref}}$; it cannot detect an error that both share. If
$M_{\text{ref}}$ omits the same UB check or encodes the same mistaken rule, if
$M_{\text{ref}}$ was transcribed incorrectly, or if the trusted boundary
definitions that state the theorem are wrong, the two models can agree and the
proof still compiles. The upfront human TCB audit of $M_{\text{ref}}$ and of
those boundary definitions remains responsible for such shared errors.

## 3. Why order matters: avoiding the retrofit trap

Implementing a large semantics first and deferring correspondence proofs until
later fails in two ways:

1. **Compounding divergences:** Small differences in value representations,
   layout calculations, control-flow handling, and side-condition checks
   accumulate across thousands of lines of code before any mechanized check
   compares the two models.
2. **Pressure to weaken the theorem:** When an agent or contributor is asked to
   prove correspondence between two large, already-written models that disagree
   on edge cases, the path of least resistance is to weaken the theorem
   statement—for example, by gating the theorem behind an ad hoc syntactic
   fragment predicate, adding a hypothesis assuming that $M_{\text{ref}}$ does
   not fault, or proving isolated per-instruction lemmas rather than a single
   whole-program theorem.

Landing $M_{\text{ref}}$ and locking the whole-program correspondence and
fault-equivalence theorems on a minimal skeleton inverts these incentives. Human
reviewers inspect the reference semantics, the locked theorem statements, and
the outer boundary definitions once up front when the codebase is small; any
later change to $M_{\text{ref}}$, the correspondence wrapper (`encodeProg`,
`evalRefStep`, or the staged support gate), the locked theorem statements, or
the outer boundary definitions requires the same human review. Every subsequent
feature addition must satisfy those unchanged theorem statements, so when a PR
only activates an existing MIR construct, human review focuses on the staged
support gate update in $M_{\text{ref}}$'s wrapper (confirming it only widens
delegation without weakening UB checks), the new `Trusted.*` canary theorem
statements and fixtures together with their required witness locks in
`trusted/audit/` (Section 4.6), and confirming that no outer boundary definition
or `encodeProg`/`evalRefStep` rule changed silently.

## 4. Subtleties and formal failure modes

A machine-checked theorem is only as strong as its statement and its boundary
definitions. Even with the Lean 4 kernel checking every proof, a correspondence
theorem can be "technically true" while failing to establish what a human
intuitively expects.

**Human comprehension of the correspondence theorem statement and every
definition in its transitive dependency cone is therefore paramount.** It must
be crystal clear to a human reviewer that the correspondence theorem means in
mathematical terms what they intend it to mean in intuitive terms. Non-obvious
subtleties, clever encodings, or indirect formulations in the theorem statement
or its transitive boundary definitions are unacceptable: any complexity needed
to relate the two models belongs in the untrusted proof, while every definition
that controls the meaning of the theorem must be maximally direct, self-evident
to a human auditing the file, and documented so that every boundary condition is
explicit rather than subtle.

In particular, the design of $M_{\text{anneal}}$, $M_{\text{ref}}$, and the
correspondence theorem must guard against the following failure modes from the
beginning and across all future additions.

### 4.1 One-way soundness asymmetry

The correspondence implication runs from $M_{\text{anneal}}$ to
$M_{\text{ref}}$ for every program $p$ and input query $q$:

$$
\mathsf{WellFormed}_{\text{anneal}}(p, q) \implies
\mathsf{WellFormed}_{\text{ref}}(p, q) \;\land\;
\mathsf{Behavior}_{\text{ref}}(p, q) \subseteq
\mathsf{Behavior}_{\text{anneal}}(p, q)
$$

This asymmetry is deliberate:

- **$M_{\text{anneal}}$ may never be more permissive than $M_{\text{ref}}$:**
  If $M_{\text{ref}}$ exhibits UB on an execution, $M_{\text{anneal}}$ must
  report either `undefined` or `unsupported`. A theorem that instead assumed
  $\mathsf{WellFormed}_{\text{ref}}(p, q)$ as a hypothesis would pass
  vacuously on every input where $M_{\text{anneal}}$ omitted a UB guard
  enforced by $M_{\text{ref}}$.
- **The implication tolerates a more restrictive $M_{\text{anneal}}$:**
  $M_{\text{anneal}}$ may reject an execution that $M_{\text{ref}}$ accepts,
  either because a construct is not yet implemented or because
  $M_{\text{anneal}}$ conservatively enforces a simpler rule than full Rust.
  Soundness is preserved in both cases, and in both cases $M_{\text{anneal}}$
  must report `unsupported`, not `undefined`. `undefined` is reserved for
  executions that actually exhibit UB; reporting it for a valid program would
  falsely tell the user that the program has UB. The bidirectional fault
  equivalence of Section 4.6 narrows this latitude further: it permits
  $M_{\text{anneal}}$ to report `unsupported` only where $M_{\text{ref}}$'s
  gated correspondence wrapper also does—that is, outside the human-audited
  staged support gate of Section 4.6 (which mirrors unimplemented or
  conservatively rejected cases as `unsupported`) or on constructs that
  $M_{\text{ref}}$ itself rejects as `unsupported`.
- **Behaviors are included in the opposite direction:** Under
  `CorrespondenceClaim` (and unconditionally under Section 4.6's forward
  totality across all valid executions), every behavior that $M_{\text{ref}}$
  permits must also be a behavior of $M_{\text{anneal}}$—strengthening to exact
  behavioral equality
  $\mathsf{Behavior}_{\text{anneal}} = \mathsf{Behavior}_{\text{ref}}$ on every
  $(p, q)$ when both models are deterministic and productive under the combined
  contract, or when reverse totality is imposed across all valid executions in
  Section 4.6 under nondeterminism, leaving strict over-approximation to Stage 3
  lowering (see Step 3).

### 4.2 Requiring $M_{\text{ref}}$ to model everything in $M_{\text{anneal}}$

No existing reference model covers 100% of `rustc` MIR (for example, arbitrary
compiler intrinsics or inline assembly). Consequently, $M_{\text{ref}}$ also
distinguishes between well-defined executions and unmodeled or faulting
executions.

$\mathsf{WellFormed}_{\text{ref}}(p, q)$ requires that $p$ is completely
supported and UB-free in $M_{\text{ref}}$ on $q$. That means
$M_{\text{anneal}}$ is not allowed to treat a construct as well-formed unless
$M_{\text{ref}}$ also models it and agrees it is well-formed. This strict
requirement keeps the theorem statement simple and prevents an escape hatch
where $M_{\text{anneal}}$ could implement a construct with no reference oracle
checking its soundness.

The requirement does not lapse as coverage grows. To support a construct (such
as an additional compiler intrinsic) beyond $M_{\text{ref}}$'s initial
coverage, we extend $M_{\text{ref}}$ itself, through its extension hooks or an
audited extension suitable for upstreaming, or we compose a second, explicit
reference model for that construct. Either way, the extension joins the
human-audited TCB, and the theorem statement does not change. We never exempt
a construct from correspondence while presenting it as correspondence-checked:
an exemption would leave bugs in $M_{\text{anneal}}$'s rules for that
construct unchecked while CI still passes. If a construct is ever deliberately
left without a reference, it must be surfaced as trusted, human-audited
semantics rather than as correspondence-checked semantics.

### 4.3 Program representation and translation ($\tau_{\text{prog}}$)

To compare how $M_{\text{anneal}}$ and $M_{\text{ref}}$ execute "the same
program," the theorem must either:

1. **Share the exact same MIR syntax type** between $M_{\text{anneal}}$ and
   $M_{\text{ref}}$, or
2. **Translate programs** via a trusted translation function
   $\tau_{\text{prog}}$.

If $\tau_{\text{prog}}$ is buggy, the correspondence theorem can become useless:

- **Partiality fail-open:** If $\tau_{\text{prog}}(p)$ is partial (returning
  `Option Prog_ref`) and the theorem is conditioned on
  $\tau_{\text{prog}}(p) = \mathsf{some}\;p_{\text{ref}}$, then returning `none`
  on difficult constructs makes the theorem hold vacuously. Even guaranteeing
  translation only for $\mathsf{WellFormed}_{\text{anneal}}$ programs is
  insufficient, because fault correspondence (Section 4.6) must also compare
  faulting programs that reach `undefined` or `unsupported` (for which
  $\mathsf{WellFormed}_{\text{anneal}}$ is false). Accordingly,
  $\tau_{\text{prog}}$ must be total over the entire theorem-domain syntax (or
  successful translation must be proven unconditionally for every program $p$ in
  both the semantic and fault-correspondence theorems).
- **Collapsing or constant translation:** If $\tau_{\text{prog}}$ maps multiple
  programs to a trivial no-op program while a corresponding output map hides the
  difference, the theorem proves nothing about the original program.
- **Semantic laundering:** Even a one-to-one AST translation can silently
  rewrite an unsafe operation into a safe one (for example, translating an
  unchecked arithmetic operator in $M_{\text{anneal}}$ to a wrapping operator in
  $M_{\text{ref}}$, or synthesizing storage/cleanup instructions that were not
  present in the source MIR).

Round-trip invertibility, such as a decoder that recovers every source program
from its translation, rules out collapsing distinct programs onto a trivial
default. It does not by itself rule out semantic laundering. A translation that
permutes operators bijectively still round-trips: if the encoder maps `.add` to
the reference's `.addUnchecked` and `.addUnchecked` to `.add`, and the decoder
swaps them back, every program decodes exactly, yet the theorem now describes a
different reference program.

Anneal therefore keeps semantic content out of $\tau_{\text{prog}}$ and keeps
the evolving execution rules of $M_{\text{anneal}}$ out of the human-audited
semantic assumptions. In Anneal's target three-stage pipeline
([`development/architecture.md`](architecture.md)), Stage 1 emits the shared
unnormalized captured-MIR AST (`Trusted/MirAst.lean`), which serves directly as
the input syntax to both $M_{\text{anneal}}$ and Stage 3's program logics and
lowering passes. Within the Lean operational semantics (Stages 2–3), only the
three human-audited semantic surfaces detailed in
[`development/architecture.md`](architecture.md)—the reference model $M_{\text{ref}}$
(with its `Trusted/Correspondence.lean` wrapper, `RefProg` dispatch into
`vendor/lean-miri/`, and staged support gate), the correspondence interface in
`Trusted/Correspondence.lean` ($\tau_{\text{prog}}$, output and choice-coupling
relations, and the locked `CorrespondenceClaim` and `FaultEquivalenceClaim`
statements), and the outer theorem-stating boundary of $M_{\text{anneal}}$ in
`Trusted/MirAst.lean` and `Trusted/MirSemantics.lean` (excluding `initState`,
`evalStep`, and the helpers that only those rules use, once Pass 2 and the
corresponding `AGENTS.md`/`.gemini/styleguide.md`/`skills/trust-review/SKILL.md`
review-policy updates are active)—require human semantic
audit (alongside Stage 1's `trusted/rustc-capture/` and the non-semantic TCB
enforcement infrastructure). Per-crate verification (`cargo anneal verify`)
discharges `Trusted.CrateTheorem` or `Trusted.UnitTheorem` over
$M_{\text{anneal}}$ (via `Anneal.MirWp` or Stage 3's kernel-checked `Abstracts`
backward simulation from normalized `StableAst` to $M_{\text{anneal}}$), while
blocking repository CI (Pass 2, `anneal-audit --require-correspondence`) proves
`CorrespondenceClaim` and `FaultEquivalenceClaim` universally from
$M_{\text{anneal}}$ to $M_{\text{ref}}$ via $\tau_{\text{prog}}$. Adding or
refactoring an execution rule in $M_{\text{anneal}}$ (`initState` and
`evalStep`) is therefore certified by the Lean 4 kernel against $M_{\text{ref}}$
rather than adding new semantic trust assumptions. Because AST normalization happens in Stage 3 (`Theory/Rust/Passes/` $\to$
`StableAst`) above $M_{\text{anneal}}$, $\tau_{\text{prog}}$ (`encodeProg` in
`Trusted/Correspondence.lean`) translates Stage 2's captured-MIR AST
(`Trusted/MirAst.lean`) into the correspondence wrapper's intermediate
reference-program representation (`RefProg`), which reuses `MirAst`'s operator
enums and mirrors each statement and terminator constructor one-to-one while
confining $\tau_{\text{prog}}$ to structural bookkeeping such as type-table
indexing—audited as part of the TCB and checked by kernel-checked
constructor-preservation theorems on `encodeProg` (`MirAst` $\to$ `RefProg`).
Importantly, `lean-miri`'s input contract operates on concrete, monomorphized
function instances with substituted generic arguments, normalized types,
concrete layouts, and evaluated MIR constants rather than unnormalized generic
bodies. Accordingly, neither `encodeProg` nor `evalRefStep` performs hidden
monomorphization, type normalization, or constant evaluation: in the initial
correspondence phase, the theorem domain is restricted explicitly to concrete,
monomorphic captured MIR carrying the concrete instance, layout, and
evaluated-constant metadata extracted and audited by Stage 1
(`trusted/rustc-capture/`), while any unnormalized generic body, unevaluated
MIR constant, or missing compiler-query layout fails closed to `unsupported` in
both $M_{\text{anneal}}$ and $M_{\text{ref}}$. This initial phase still supports
modular library-centric verification of concrete library functions over all
caller inputs and states without a `fn main()`, while full polymorphic
verification of uninstantiated generic library bodies across arbitrary
downstream caller types and layouts (the long-term target in
[`DESIGN.md`](../DESIGN.md#library-centric-verification)) is phased in
separately by parameterizing $M_{\text{anneal}}$ over generic substitutions and
layout/trait constraints and connecting every valid concrete substitution to
$M_{\text{ref}}$ via a kernel-verified instantiation theorem (or formally
verifying the normalization pass itself)—never by adding unverified lowering to
`evalRefStep`.
Within that concrete domain, the cross-AST dispatch from `RefProg` into
`vendor/lean-miri/`'s internal syntax (`evalRefStep` inside $M_{\text{ref}}$'s
`Trusted/Correspondence.lean` wrapper) is the remaining semantic-laundering
surface, so `evalRefStep` is audited one-to-one as part of the $M_{\text{ref}}$
TCB and backed by end-to-end semantic canaries: for example, an unchecked
addition that overflows must exhibit UB, whereas a wrapping addition of the
same operands must not. (Unless their theorem statements and fixtures live on
`Trusted.*` and are registered in Pass 2's required witness list in
`trusted/audit/`, those constructor-preservation theorems and canaries serve as
supplementary CI checks rather than Pass 2 witness locks.) Both
$\tau_{\text{prog}}$ and the wrapper's dispatch remain minimal and audited as
part of the TCB.

### 4.4 Behavior representation and projection ($\pi$)

Similarly, to state that $p$ "has the same behavior" in $M_{\text{anneal}}$ and
$M_{\text{ref}}$, the theorem must either:

1. **Use the exact same representation of observable program behavior** in both
   semantics, or
2. **Project or translate behaviors** through a trusted function $\pi$.

A flawed $\pi$ function can silently hollow out the theorem in several ways:

- **Outcome erasure:** If $\pi$ projects outcomes to `Unit`, a constant, or an
  echo of the input arguments, then any two terminating runs trivially "have the
  same behavior" regardless of the values they compute.
- **Bijective value permutations:** Requiring $\pi$ to be bijective rules out
  many-to-one erasure, but a bijection on values alone can still permute
  distinct concrete results (for example, mapping $v \mapsto v \oplus 1$ or
  swapping two output fields) if the two sides compensate inside their
  respective evaluators.
- **Omitting caller-visible state:** If $\pi$ compares only a scalar return
  slot while projecting away caller-visible memory or mutable reference targets,
  a function that corrupts caller memory while returning the expected integer
  passes the behavioral check.
- **Over-constraining internal machine state:** Conversely, requiring a strict
  bijection between full *internal* execution states ($S_{\text{anneal}}$ and
  $S_{\text{ref}}$) is too rigid when the two models use different internal
  representations for local storage, allocation identifiers, or uninitialized
  padding bytes.

The clean separation is to keep internal machine states private to the
simulation proof while making the **observable behavior representation**
(covering termination vs. unwinding vs. divergence, return values, and
caller-visible memory effects) share the exact same type and leaf representation
between $M_{\text{anneal}}$ and $M_{\text{ref}}$ so that $\pi$ is the identity
on observable leaves. In this effect-free execution model (`Query` $\to$
`Behavior`, covering `TerminalOut` and divergence), constructs that produce
intermediate externally observable effects before terminating or during a
diverging run—such as I/O, volatile or MMIO accesses, inline assembly,
concurrency or atomic synchronization, and foreign/external calls—remain
outside the supported domain and evaluate to `unsupported`
(`FaultKind.unsupported`); admitting any such construct in a future phase
requires extending `Behavior` and the choice-coupled simulation relation with a
shared labeled event/prefix trace so neither terminating nor diverging
executions can disagree on effect ordering. If any projection $\pi$ is used
around composite or memory wrappers, it must be accompanied by a kernel-checked
theorem proving universally (for all values, not merely a finite test suite)
that $\pi$ preserves scalar bits, boolean flags, field identity, provenance
tags, and caller-visible memory contents; concrete input-output tests serve only
as supplementary non-vacuity canaries and cannot establish a trusted boundary
map.

### 4.5 All-prefix safety, productivity, and nondeterminism

The theorem's definition of well-formedness and behavior must also account for
non-terminating and nondeterministic executions:

- **All-prefix safety (not return-only safety):** If well-formedness only
  inspects completed returns, a program that faults with UB on step 3—or that
  triggers UB on one nondeterministic branch while diverging on another—has no
  completed returns on the faulting run and would be judged vacuously
  well-formed. Both $\mathsf{WellFormed}_{\text{anneal}}$ and
  $\mathsf{WellFormed}_{\text{ref}}$ must require that *every reachable finite
  execution prefix* avoids `undefined` and `unsupported`.
- **No silent stuck states (productivity):** If $M_{\text{ref}}$ represents
  steps relationally and an unmodeled or invalid state simply has no outgoing
  transitions (rather than stepping to an explicit fault outcome), universal
  claims over all executions in $M_{\text{ref}}$ hold vacuously. Every
  non-terminal state in both models must step productively to either a successor
  state or an explicit failure outcome.
- **Demonic nondeterminism:** When $M_{\text{ref}}$ models nondeterministic
  choices (such as memory allocator addresses),
  $\mathsf{WellFormed}_{\text{anneal}}(p, q)$ must imply that *all* permitted
  executions in $M_{\text{ref}}$ are well-formed and that each of their
  behaviors is a behavior of $M_{\text{anneal}}$. If $M_{\text{anneal}}$ is
  deterministic, it cannot arbitrarily pick one lucky choice when the
  program's branch or safety depends on that choice; the correspondence
  theorem automatically forces $M_{\text{anneal}}$ to either return
  `unsupported` on operations that observe the nondeterminism or model the
  nondeterministic choice itself.

### 4.6 Guarding against antecedent collapse and outcome misclassification

Because both `undefined` and `unsupported` falsify
$\mathsf{WellFormed}_{\text{anneal}}(p, q)$, the correspondence theorem by
itself does not prevent two bugs in $M_{\text{anneal}}$:

1. **Antecedent collapse (vacuous `unsupported` or `undefined`):** If a pull
   request claims to add support for a MIR construct, but a bug in
   $M_{\text{anneal}}$ causes every execution of that construct to return
   `unsupported` (or `undefined`), the correspondence theorem still holds
   vacuously.
2. **`undefined` vs. `unsupported` swaps:** If $M_{\text{anneal}}$ returns
   `unsupported` on a program that actually triggers UB (masking a real bug as
   "unmodeled"), or returns `undefined` on a valid program that uses an
   unimplemented construct (falsely reporting UB on safe code), the
   correspondence theorem still holds because both outcomes falsify the
   antecedent.

To close this gap and ensure future additions cannot regress into vacuity or
misclassification, incremental additions to $M_{\text{anneal}}$ must be paired
with concrete canary tests in CI. Each CI canary's exact theorem statement
**and** every concrete program, query, and expected-outcome fixture definition
it references must live on the human-audited `Trusted.*` surface—enforced by
Statement-Origin Separation in `trusted/audit/`, which forbids locked canary
theorem types from referencing untrusted `theory/` or `correspondence/`
definitions (whether fixtures are named `Trusted.*` definitions or complete
constructor values embedded directly in the locked `Trusted.*` type)—while only
the canary *proofs* live in untrusted `theory/` or `correspondence/`. Adding a
new feature canary includes registering its required Pass 1 or Pass 2 witness
lock in `trusted/audit/`, so an untrusted edit to `theory/` or
`correspondence/` can neither delete the canary nor weaken its statement, nor
swap a referenced fixture definition for a trivial program:

- **Positive execution canaries:** Concrete programs exercising each supported
  MIR construct and proving both that every execution from the canary query is
  fault-free ($\mathsf{WellFormed}_{\text{anneal}}(p, q)$ holds universally
  across all reachable prefixes) and that $M_{\text{anneal}}$ evaluates them to
  the expected `ok` outcome (witnessing that
  $\mathsf{WellFormed}_{\text{anneal}}$ is inhabited and non-vacuous for that
  feature).
- **Negative `undefined` canaries:** Concrete programs exercising each modeled
  UB condition and proving that $M_{\text{anneal}}$ evaluates them to
  `undefined` (not `ok` and not `unsupported`).
- **Negative `unsupported` canaries:** Concrete programs exercising unmodeled
  constructs and proving that $M_{\text{anneal}}$ evaluates them to
  `unsupported` (not `ok` and not `undefined`) until support for those
  constructs is intentionally added.

Canaries alone cannot cover a supported domain. For a construct parameterized
by operators, integer widths, signedness, or modes, one positive canary
witnesses a single execution: an implementation could special-case that
program and return `unsupported` for the rest of the claimed domain while the
correspondence theorem and every canary still pass. Anneal therefore pairs
concrete boundary-case canaries with a staged support gate in $M_{\text{ref}}$
and fault equivalence along corresponding executions.

Because an imported reference interpreter may already evaluate constructs that
$M_{\text{anneal}}$ has not yet enabled (or that $M_{\text{anneal}}$
conservatively rejects under Section 4.1), $M_{\text{ref}}$'s correspondence
wrapper applies an explicit, human-audited support gate that reports
`unsupported` outside the currently claimed support domain and delegates every
construct inside that domain to the reference interpreter. The execution
correspondence relation between $M_{\text{anneal}}$ and $M_{\text{ref}}$ must
be induced by a stepwise simulation coupled to a faithful choice-event relation
that preserves every shared external nondeterministic choice (such as allocator
addresses, provenance decisions, or scheduler choices) at each choice point—so
paired executions can never permute distinct external choice branches (allowing
many-to-one, one-to-many, or many-to-many coupling only over genuinely
unobservable internal machine choices or step-granularity stuttering, and
bijective when both models have identical nondeterminism).

Unconditionally across **every** program $p$ and input query $q$ (without gating
on $\mathsf{WellFormed}_{\text{anneal}}(p, q)$), the combined locked
correspondence and fault-equivalence contract requires this choice-coupled
execution relation to satisfy Cases 1–4 below on every coupled pair together
with the following totality conditions:

- **Unconditional forward totality ($M_{\text{ref}} \to M_{\text{anneal}}$
  across all valid executions, faulting and non-faulting):** Every valid
  execution of $M_{\text{ref}}(\tau_{\text{prog}}(p), q)$ has a choice-coupled
  valid execution of $M_{\text{anneal}}(p, q)$ satisfying Cases 1–4.
- **Unconditional reverse totality on faulting executions
  ($M_{\text{anneal}} \to M_{\text{ref}}$):** Every faulting execution of
  $M_{\text{anneal}}(p, q)$ has a choice-coupled faulting execution of
  $M_{\text{ref}}(\tau_{\text{prog}}(p), q)$ satisfying Case 1.
- **Optional reverse totality on non-faulting executions
  ($M_{\text{anneal}} \to M_{\text{ref}}$):** Holds automatically when both
  models are deterministic and productive. Under nondeterminism, omitting it
  permits non-faulting behavioral over-approximation in $M_{\text{anneal}}$;
  imposing reverse totality across *all* valid executions of
  $M_{\text{anneal}}$ (faulting and non-faulting alike) immediately upgrades
  Cases 2–4 to bidirectional equivalence (because productive executions
  partition into the four mutually exclusive outcome classes below) and yields
  exact behavioral equality
  $\mathsf{Behavior}_{\text{anneal}} = \mathsf{Behavior}_{\text{ref}}$ on
  $(p, q)$ vs. $(\tau_{\text{prog}}(p), q)$ up to $\sim_{\text{out}}$ on
  **every** $(p, q)$, including mixed-faulting inputs.

On every coupled pair of valid executions, the relation enforces four mutually
exclusive outcome cases over productive executions. When wrapping `lean-miri`,
additional non-success interpreter or operational-safety stop outcomes beyond
UB and explicit unsupported features—specifically `failed`, `pending`, and
`blocked` (unresolved obligations, pending interactions, or interpreter/host
failures)—must be classified explicitly and fail-closed inside the
human-audited `Trusted/Correspondence.lean` wrapper (mapping each such stop to
$\mathsf{unsupported}$, never silently dropping, retrying, or reclassifying it
as UB or normal termination, unless dedicated outcome cases are added to both
models and locked in the correspondence witness contract). Under that
fail-closed wrapper classification, every productive execution partitions into
four outcome cases:

1. **Faulting executions (universal and bidirectional across every coupled
   pair):** For every choice-coupled pair of valid executions, whenever either
   execution faults with classification
   $k \in \{\mathsf{undefined}, \mathsf{unsupported}\}$ (with `lean-miri`'s
   `failed`, `pending`, and `blocked` stops mapped fail-closed into
   $\mathsf{unsupported}$ by the locked wrapper), the other also faults with
   the exact same classification $k$. In particular, no non-faulting execution
   in either model may pair with a faulting execution in the other, and neither
   model may swap `undefined` with `unsupported`.
2. **Normally terminating executions (paired
   $M_{\text{ref}} \to M_{\text{anneal}}$; bidirectional whenever reverse
   totality holds):** For every choice-coupled pair of valid executions,
   whenever the $M_{\text{ref}}$ execution terminates normally (returns from
   the entry frame), the coupled $M_{\text{anneal}}$ execution also terminates
   normally in a state related under $\sim_{\text{out}}$ (preserving the return
   value and caller-visible memory effects). Whenever reverse totality holds
   across all valid executions (automatically when both models are deterministic
   and productive), the reverse $M_{\text{anneal}} \to M_{\text{ref}}$ direction
   follows directly from the partition of productive outcomes.
3. **Unwinding executions (paired $M_{\text{ref}} \to M_{\text{anneal}}$;
   bidirectional whenever reverse totality holds):** For every choice-coupled
   pair of valid executions, whenever the $M_{\text{ref}}$ execution terminates
   by unwinding out of the entry frame, the coupled $M_{\text{anneal}}$
   execution also terminates by unwinding in a state related under
   $\sim_{\text{out}}$ (preserving the unwind payload, drop and cleanup
   effects, and caller-visible memory effects); as in Case 2, the reverse
   direction follows automatically whenever reverse totality holds across all
   valid executions. Constructs capable of abnormal process termination without
   returning from or unwinding out of the entry frame (such as
   `UnwindAction::Terminate`, aborting panics, or abort intrinsics) remain
   `unsupported` (`FaultKind.unsupported`, covered by Case 1) unless an
   explicit `aborted` outcome is added to `TerminalOut`.
4. **Diverging executions (paired $M_{\text{ref}} \to M_{\text{anneal}}$;
   bidirectional whenever reverse totality holds):** For every choice-coupled
   pair of valid executions, whenever the $M_{\text{ref}}$ execution
   diverges—meaning that it produces an infinite productive step trace
   $t_0 \to t_1 \to t_2 \to \cdots$ without terminating, unwinding, or faulting
   (proven coinductively or over infinite step sequences, allowing finite
   stuttering between corresponding steps when step granularities differ,
   rather than treating finite fuel exhaustion as divergence)—the coupled
   $M_{\text{anneal}}$ execution also diverges, never conflating divergence
   with normal return, unwinding, or faulting; as in Cases 2–3, the reverse
   direction follows automatically whenever reverse totality holds across all
   valid executions.

Unconditional forward totality across all valid executions (not gated on
$\mathsf{WellFormed}_{\text{anneal}}(p, q)$) closes two subtle nondeterministic
failure modes together with unconditional reverse totality on faulting
executions and Case 1. First, every faulting execution of $M_{\text{ref}}$
(even on an input where $M_{\text{anneal}}$ faults on another branch) pairs
with a choice-coupled execution of $M_{\text{anneal}}$ that faults with the
exact same classification $k$, so $M_{\text{anneal}}$ can never mask or
misclassify a fault in $M_{\text{ref}}$; symmetrically, every faulting
execution of $M_{\text{anneal}}$ pairs with a choice-coupled execution of
$M_{\text{ref}}$ that faults with the exact same classification $k$. Second,
every *non-faulting* execution of $M_{\text{ref}}$—even on a mixed-faulting
nondeterministic input where $M_{\text{ref}}$ has both a succeeding branch and
a faulting branch—must still pair with a choice-coupled non-faulting execution
of $M_{\text{anneal}}$ satisfying Cases 2–4. Gating forward totality on
$\mathsf{WellFormed}_{\text{anneal}}(p, q)$ would leave such mixed-faulting
inputs unprotected: an $M_{\text{anneal}}$ that faulted on every branch would
falsify $\mathsf{WellFormed}_{\text{anneal}}(p, q)$ (making a gated forward
claim vacuous) while pairing every Anneal fault with $M_{\text{ref}}$'s
faulting branch. Unconditional forward totality rejects that failure mode,
implies `CorrespondenceClaim` directly whenever
$\mathsf{WellFormed}_{\text{anneal}}(p, q)$ holds, and establishes
$\mathsf{Behavior}_{\text{ref}} \subseteq \mathsf{Behavior}_{\text{anneal}}$ on
every $(p, q)$.

Under nondeterminism, imposing universal bidirectional Case 1 and reverse
totality on faulting executions across all programs $p$ (including programs
that branch on a computed value and trigger UB or `unsupported` on an
unexpected outcome) already rules out behavioral over-approximation on all
values and control flow inspectable and fault-convertible within the gated
fragment, whereas full behavioral equality
$\mathsf{Behavior}_{\text{anneal}} = \mathsf{Behavior}_{\text{ref}}$ up to
$\sim_{\text{out}}$ on every $(p, q)$—including uninspectable entry-frame
boundary outcomes and mixed-faulting inputs—follows immediately if reverse
totality is imposed across *all* valid executions of $M_{\text{anneal}}$ (not
only faulting ones). True behavioral over-approximation,
$\mathsf{Behavior}_{\text{ref}} \subsetneq \mathsf{Behavior}_{\text{abstract}}$,
belongs in Stage 3 (`StableAst` / `Abstracts` / `MirWp`), which is not subject
to `FaultEquivalenceClaim`.

When both models are globally deterministic and productive across all
$(p, q)$—including `unsupported` transitions—this unconditional relation
reduces cleanly to `CorrespondenceClaim` (gated on
$\mathsf{WellFormed}_{\text{anneal}}(p, q)$) plus unconditional bidirectional
fault-reachability equivalence for every program $p$ and input query $q$:

$$
\mathsf{Reaches}_{\text{anneal}}(p, q, \mathsf{fault}\;k) \iff
\mathsf{Reaches}_{\text{ref}}(\tau_{\text{prog}}(p), q, \mathsf{fault}\;k)
\quad \text{for } k \in \{\mathsf{undefined}, \mathsf{unsupported}\}
$$

Specifically, whenever $M_{\text{ref}}(\tau_{\text{prog}}(p), q)$ has a
non-faulting execution, determinism implies that $M_{\text{ref}}$ does not
fault on that input, so bidirectional fault-reachability equivalence implies
$\mathsf{WellFormed}_{\text{anneal}}(p, q)$; `CorrespondenceClaim` then fires
non-vacuously and yields exact behavioral equality
$\mathsf{Behavior}_{\text{anneal}} = \mathsf{Behavior}_{\text{ref}}$ up to
$\sim_{\text{out}}$ across every $(p, q)$.

When a model permits nondeterministic choices, requiring this unconditional
choice-coupled correspondence (covering **all** valid executions of
$M_{\text{ref}}$ and all faulting executions of $M_{\text{anneal}}$ across
every $(p, q)$, rather than merely existential reachability over $p$ and $q$, a
partial relation that omits faulting branches, or forward totality gated on
$\mathsf{WellFormed}_{\text{anneal}}(p, q)$) ensures that neither model can
leave a faulting branch unpaired, that $M_{\text{anneal}}$ cannot hide a
reference `undefined` fault behind an `unsupported` fault on a different
branch, that $M_{\text{anneal}}$ cannot fault on a branch where
$M_{\text{ref}}$ succeeds (even when another branch faults), that
$M_{\text{anneal}}$ cannot report `unsupported` on one branch merely because a
different nondeterministic branch of the same input triggers `unsupported`, and
that neither model can swap `undefined` and `unsupported` on any execution.

Because this unconditional contract quantifies over all inputs, all valid
executions of $M_{\text{ref}}$, and all faulting executions of
$M_{\text{anneal}}$ across $M_{\text{ref}}$'s gated semantics, it forbids
$M_{\text{anneal}}$ from returning `unsupported` (or `undefined`) on any
execution where $M_{\text{ref}}$ succeeds, from omitting a fault that
$M_{\text{ref}}$ triggers on any branch, and from reporting one failure outcome
where $M_{\text{ref}}$ reports the other. $M_{\text{ref}}$'s staged support
gate (together with any `unsupported` outcomes produced by $M_{\text{ref}}$
itself) thereby serves as the single audited support predicate:
$M_{\text{anneal}}$ reports `unsupported` if and only if $M_{\text{ref}}$'s
gated semantics does, so widening the supported domain means widening the
coverage that $M_{\text{ref}}$ exposes to the theorem, under human review. The
CI canaries—whose exact theorem statements and referenced program, query, and
expected-outcome fixture definitions live on the human-audited `Trusted.*`
surface and are locked as required Pass 1 and Pass 2 witnesses in
`trusted/audit/`—then guard that staged support predicate itself against
collapse. For each parameterized construct, they cover positive and boundary
cases across its parameters (such as each integer width and signedness, the
extremes of each operand range, a zero divisor, or a shift amount equal to the
bit width), proving that those sampled executions reach `ok` or `undefined`
(never `unsupported`) so that narrowing the staged gate or implementation across
any sampled case breaks the locked CI canaries.
