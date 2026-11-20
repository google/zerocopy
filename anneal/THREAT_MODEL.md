<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal Threat Model

[`PRINCIPLES.md`](PRINCIPLES.md) defines Anneal's central promise to its users:

> One of Anneal's outputs is a *TCB audit log*, a list of code and assumptions
> Anneal trusts (including itself) to compile your code and prove it correct.
> Anneal's promise is this:
>
> ***If** the code in your TCB audit log is correct, its assumptions are valid,
> **and** Anneal emits no errors, **then** your code is sound and satisfies any
> stated specifications.*

This document defines what Anneal does and does not aim to defend against—and
why—so that promise holds even when Rust code, specifications, and Lean proofs
are written by untrusted humans or reward-hacking AI coding agents. For the
invariant goals that govern this threat model, see
[`META_PRINCIPLES.md`](META_PRINCIPLES.md); for how Anneal's architecture
implements these defenses, see [`docs/trust-model.md`](docs/trust-model.md).

## 1. Adversarial contributions and bounded human review

Unlike testing, which checks that a program behaves as expected on specific
inputs, formal verification claims that a mathematical proof establishes a
property for *all* valid inputs. Because writing specifications and
machine-checked proofs requires significant effort, projects increasingly rely
on external contributors and AI coding agents to write Rust code,
specifications, proof automation, and Lean 4 proofs.

An honest developer uses `cargo anneal` to find genuine bugs in their code or
proofs. By contrast, a malicious contributor—or a reward-hacking AI coding agent
optimizing to make `cargo anneal` exit `0`—has an incentive to make verification
succeed *without* proving the property the maintainer expects:

- An agent stuck on a difficult proof may try to sneak `sorry`, a custom
  `axiom`, unverified native evaluation (`native_decide`), or a compiler
  override (`@[implemented_by]`, `@[extern]`) into a Lean proof.
- An agent unable to prove a function's specification may weaken the
  postcondition (`ensures(true)`), restrict the precondition to a trivial or
  empty case (`requires(x == 0)` or `requires(false)`), modify a helper
  definition that the specification depends on, or bypass verification with an
  explicit trust waiver (such as `#[anneal::trusted]`).
- An agent running on a developer's machine may bypass verification altogether
  by modifying or shadowing the `cargo-anneal` binary or its toolchain
  dependencies so the command exits `0` unconditionally.

Anneal's threat model therefore assumes that repository changes may be authored
by adversarial humans or reward-hacking AI coding agents rather than assuming
good-faith inputs.

### The end-to-end division of labor and the two senses of "trusted"

No automated tool can defend against a compromised host operating system or know
what specifications and assumptions exist only in a maintainer's head. Turning
[`PRINCIPLES.md`](PRINCIPLES.md)'s promise into an end-to-end guarantee that
code *behaves as the maintainer expects* therefore requires an explicit division
of labor:

- **If:**
  1. Verification runs in an **uncompromised execution environment** (such as an
     isolated CI runner),
  2. A human reviewer (or review agent) audits **only** two clearly bounded
     surfaces and agrees with their contents:
     - **The stated specifications**, and
     - **The TCB audit log**, and
  3. **Anneal emits no errors**,
- **Then:** The verified code is sound (UB-free) and behaves as the maintainer
  expects.

Here, an **uncompromised execution environment** ensures that `cargo-anneal`'s
"no errors" result and TCB audit log are genuine, while the two human-reviewed
surfaces are "trusted" in fundamentally different ways that must not be
conflated:

1. **The stated specifications — trusted to define *what the user intended to
   prove*:**
   - Baseline **soundness** (well-defined behavior / UB-freedom) is defined by
     Anneal itself and is always on, even when a crate contains no user-written
     specifications at all.
   - For properties beyond baseline soundness (as well as any stated
     preconditions or invariants under which code is verified, including caller
     safety preconditions on `unsafe` functions), the stated
     specifications—together with any helper functions, trait implementations,
     constants, types, or mathematical models that define their meaning—express
     *what the user is asking Anneal to verify*.
   - Calling specifications "trusted" does **not** mean Anneal assumes they hold
     without proof: Anneal proves that the Rust code satisfies its stated
     specifications, while relying on human review to confirm that those
     specifications state the intended property (bridging the gap from
     *"satisfies any stated specifications"* to *"behaves as the maintainer
     expects"*).
2. **The TCB audit log — trusted to be *true without proof*:**
   - Covers Anneal's own Trusted Computing Base (Anneal, `rustc`, the Lean 4
     kernel, and their semantic models) together with any unproved assumptions
     or trust waivers in the verified crate or its dependencies.
   - Unlike stated specifications, Anneal assumes every entry in the TCB audit
     log is valid without proving it, and relies on human review to confirm that
     the TCB's code and unproved assumptions are acceptable.

**Bounded human-review corollary:** Because Anneal makes these two surfaces
explicit and enforces total defenses (Section 3) over everything outside them, a
human reviewer knows which code and artifacts can define or affect the meaning
of **stated specifications** and which code and assumptions are trusted without
proof via the **TCB audit log**—and can **safely ignore everything outside those
two categories**, including all proofs, all proof-automation libraries, and all
verified Rust implementation bodies that do not define specifications or TCB
assumptions, no matter how large, complex, or adversarial they are.

To uphold this division of labor without **security theater**, Anneal classifies
every threat by whether an automated verification tool can prevent it
**totally** without rejecting legitimate code: threats that cannot in principle
be prevented totally by an automated tool are stated as **explicit assumptions**
(Section 2), whereas threats from untrusted repository contents outside the
human-reviewed surfaces are met with **mathematically or structurally total
defenses** (Section 3).

## 2. Explicit assumptions: threats outside automated verification

### 1. Compromised execution environments and the dev vs. CI boundary

The overarching operational threat that Anneal **does not** aim to defend
against is a **compromised execution environment**: an environment in which an
untrusted human, agent, or process can modify or interpose on `cargo-anneal`,
its binary dependencies (`cargo`, `rustc`, `lean`, or pre-compiled toolchain
files), its environment variables (`PATH`, `LD_PRELOAD`), its working files
during verification, or the channel reporting the verification result and TCB
audit log.

This includes host OS tampering executed during compilation or elaboration by
build-time code inside the repository—such as Cargo `build.rs` build scripts,
procedural macros, compiler plugins, or Lean 4 elaborator I/O (`#eval`,
`run_cmd`, `by_elab`, `initialize`). (By contrast, non-malicious Rust code
*generated* by a `build.rs` script or procedural macro is compiled by `rustc`
and verified by Anneal under the same soundness, specification, and TCB rules as
hand-written code in the crate.)

**There is no in-principle way for an un-sandboxed user-space tool to defend
against a compromised execution environment.** If an agent running under the
same OS user account as `cargo-anneal`—or a `build.rs` script, procedural macro,
or compiler process invoked during the build—has write access to the host's
binaries, working directory, or environment, it does not need to find a
soundness bug in Anneal or the Lean 4 kernel: it can replace `cargo-anneal` (or
`lean`) or overwrite build outputs on disk so verification reports a clean TCB
audit log and exits `0`. In-process checks inside `cargo-anneal` cannot defend
against an actor or child process that can modify the host environment in which
those checks run; preventing build-time code from tampering with the host
requires OS-level sandboxing of the build.

**Anneal's threat model therefore assumes an uncompromised execution
environment:** the operating system, filesystem, environment, and installed
Anneal toolchain binaries are intact and outside the untrusted actor's write or
process-control access when verification runs.

This assumption naturally aligns with the standard split between **local
development environments** and **Continuous Integration (CI)**:

- **Local development machines (outside the threat model when shared with an
  un-sandboxed agent):** When a developer runs an un-sandboxed AI agent under
  their own user account on a laptop or workstation, the execution environment
  is potentially compromised. Running `cargo anneal` locally remains useful as a
  fast feedback loop for catching ordinary mistakes and naive agent shortcuts,
  but a local pass is not a security guarantee. (A local run satisfies the
  threat model only when the agent is confined inside a separate OS sandbox,
  container, or VM while `cargo-anneal` runs outside that sandbox.)
- **Well-configured CI (within the threat model):** In CI, an untrusted
  contributor or AI agent cannot touch the runner's binaries or environment
  directly; their only interface is **proposing changes to repository files in a
  pull request**. Because software projects already rely on isolated CI runners
  (with OS-level build sandboxing where untrusted `build.rs`, macro, or
  elaborator execution is a concern) and human code review to gate merges to
  `main`, running `cargo anneal` in CI with protected workflow configurations
  and a pinned Anneal toolchain satisfies the uncompromised execution
  environment assumption.

### 2. Weak, vacuous, or unintended specifications and explicit TCB assumptions

Even in an uncompromised CI environment, Anneal **does not** aim to judge
automatically whether a stated specification or an assumption in the TCB audit
log matches the maintainers' intent. No automated tool can distinguish in
principle between "the maintainers decided to narrow this function's
specification" and "a reward-hacking agent weakened the specification to make
proofs pass."

In particular, **automated vacuity checks cannot defend against adversarial
specification weakening.** Suppose a reward-hacking agent cannot prove a
specification across all valid inputs of a function `parse(buf: &[u8])`. Even if
Anneal rejected contradictory preconditions such as `requires(false)` by
checking that at least one valid input satisfies the precondition, the agent
could trivially satisfy that check by restricting the precondition to a single
narrow case—such as `requires(buf.is_empty())` or `requires(x == 0)`—or by
weakening the postcondition to `ensures(true)`, leaving almost all executions or
behaviors unverified. Conversely, heuristically rejecting narrow preconditions
or weak postconditions would reject legitimate domain-specific contracts.

Anneal therefore does not treat heuristic or satisfiability-based vacuity checks
as a security defense. Because any weakening of a stated specification or
addition of a TCB waiver appears on the two human-reviewed surfaces, judging
that stated specifications are strong enough and that logged TCB assumptions are
acceptable is a **human-review responsibility**.

## 3. In-scope threats: total defenses over untrusted repository contents

Within an uncompromised execution environment, Anneal treats the repository's
proofs, specifications, and Rust source files as untrusted and aims to provide
**total, un-bypassable defenses** against the two ways untrusted repository
contents could subvert verification—without rejecting legitimate Rust crates,
Cargo workspaces, or Lean 4 specifications and proofs:

### 1. Subverting the proof without proving the theorem

An adversarial proof in the crate or in a proof-automation library can attempt
to make Lean accept a false claim without proving the theorem derived from
Anneal's soundness definition and the crate's stated specifications—for example,
by introducing `sorry` or a custom `axiom`, invoking unverified native
evaluation (`native_decide`), defining `partial` or `unsafe` constants,
attaching compiler overrides (`@[implemented_by]`, `@[extern]`, `@[csimp]`), or
proving a weakened, shadowed, or renamed theorem statement instead of the
generated verification obligation.

Anneal aims to prevent any untrusted proof or tactic library from altering the
theorem statement or causing a false claim to pass—without restricting
legitimate Lean 4 proofs, tactics, or macros—so that **proofs never need to be
trusted or reviewed by humans**.

### 2. Hidden specification dependencies or unlogged TCB assumptions

Even when every proof is mathematically sound in the Lean kernel, an adversarial
change outside a function's inline contract could attempt to alter what is
proved or assumed without appearing on the two surfaces a human reviewer audits:

- **Indirect specification tampering (hidden specification dependencies):**
  Leaving a function's inline specification unchanged in a pull request diff
  while modifying or shadowing a helper function, trait implementation,
  constant, type definition, or mathematical model that the specification's
  meaning transitively depends on—for example, modifying a helper predicate
  `is_sorted(result)` so it always returns `true`. Anneal aims to ensure that
  every definition capable of affecting the meaning of a stated specification is
  explicitly demarcated on (or surfaced in) the human-reviewed specification
  surface, and that no code outside that surface can shadow, redefine, or
  silently alter what a specification means.
- **Unlogged assumptions across crate items and compositional boundaries:**
  Bypassing verification of an obligation without recording an entry in the TCB
  audit log. Every obligation or assumption required for the crate's soundness
  or stated specifications must either be **discharged by proof** where it
  originates or be **recorded in the TCB audit log**—including across:
  - *Functions, call sites, trait implementations, and trust waivers:* Because
    baseline soundness is always on across the crate, skipping or waiving
    verification of any function, method, trait implementation, or other item in
    the crate (such as with `#[anneal::trusted]`)—even an uncalled entry
    point—or calling any waived, unverified, or external (`extern`) function
    must be recorded in the TCB audit log (surfacing the waived code or
    assumption so edits to waived code cannot pass silently). Likewise, every
    verified caller must prove a callee's stated preconditions—including
    `unsafe` function preconditions (which are part of the human-reviewed
    specification surface)—at the call site, and every trait implementation must
    prove the trait's stated specifications (and, for `unsafe` traits, its
    safety contract).
  - *Type invariants and encapsulation boundaries:* If verified code assumes a
    type invariant that relies on encapsulation, the type's visibility boundary
    must prevent unverified code from breaking it: *every* function within the
    visibility scope capable of constructing the type, mutating its
    invariant-bearing fields, or exposing mutable access to those fields must
    establish or preserve that invariant, and leaving any such function
    unverified or waived must be surfaced as an assumption in the TCB audit log.
  - *Crate and workspace dependencies:* Relying on an unverified dependency, or
    on a verified dependency that itself contains TCB waivers or assumptions,
    must surface those assumptions transitively in the TCB audit log so waivers
    cannot be hidden in upstream dependencies.

Because Anneal ensures that nothing outside the human-reviewed specification and
TCB audit log surfaces can silently alter a specification's meaning or introduce
an unproved assumption—without noise from ordinary implementation or proof
edits—**verified Rust implementation bodies that do not define specifications or
TCB assumptions never need to be reviewed by humans**.
