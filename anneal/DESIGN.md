<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal Design Overview

> [!NOTE]
> Anneal is an early alpha. Today it verifies a small, call-free scalar subset
> of Rust on x86-64 Linux and has not yet been audited against adversarial
> proofs or hostile crates. This document explains how Anneal is designed to
> work for Rust users and clearly separates what runs today from what is
> planned. For internal contributor and implementation details, see
> [`development/design.md`](development/design.md) and
> [`development/`](development/README.md).

Anneal is a formal verification framework for Rust libraries. It lets engineers
and AI coding agents prove that Rust code—including `unsafe` code—is free of
Rust undefined behavior (UB) and satisfies stated specifications, while keeping
the amount of code humans have to review small and bounded.

## How Anneal works

Rather than asking you to rewrite Rust in a separate verification language,
Anneal hooks into `rustc` to capture the typed Mid-level Intermediate
Representation (MIR) that the compiler produces after typechecking, borrow
checking, and drop elaboration. It then checks proofs about that captured MIR
using the Lean 4 theorem prover.

Anneal separates its own codebase—and your verification artifacts—along a strict
trust boundary:

- **Trusted core (`trusted/`):** The small set of components whose correctness
  must be audited by humans without a machine-checked proof: capturing MIR from
  `rustc`, stating the MIR semantics and verification theorem, orchestrating
  verification, and auditing the boundary. To reduce reliance on manual review
  of operational semantics, Anneal also certifies its MIR execution rules in CI
  against a pinned reference model (`lean-miri`).
- **Untrusted proofs and proof automation (`theory/` and user proofs):**
  Weakest-precondition libraries, tactics, and per-crate proofs live outside the
  Trusted Computing Base (TCB). Every proof is checked by a proof kernel against
  the trusted theorem statement, so a bug in a proof library or an adversarial
  proof script can cause verification to fail, never cause a false claim to
  pass.

## What Anneal guarantees—and what it assumes

When Anneal runs in an intact, isolated execution environment (including
isolation from untrusted compile-time Rust code such as `build.rs` scripts and
procedural macros) and emits an untainted passing verification receipt bound to
an exact captured source, specification set, target, `cfg` set, and compiler
profile, the guarantee holds at the **captured MIR boundary** whenever every
component in the **TCB audit log**—including Anneal's MIR semantics (its
definition of UB), capture and audit boundary, toolchain assumptions, external
calls, and any waived or unverified items—is correct and its assumptions are
jointly valid of the real system. Under those conditions:

1. **Safe Rust APIs are UB-free:** Every verified safe API is free of Rust UB
   across all execution prefixes (terminating, diverging, or panicking) for all
   type-correct calls satisfying applicable library invariants (each preserved by
   every constructor and mutator, even on unwind, as proved or logged in the
   TCB) in any safe calling context, including open-world callbacks and interior
   mutability. No user specification or scope clause can narrow this baseline.
2. **`unsafe` Rust APIs are UB-free under their formal `# Safety` contracts:**
   Every verified `unsafe` API is free of UB across all prefixes whenever
   callers discharge its formally stated `# Safety` preconditions (which never
   relax Rust language validity).
3. **Stated functional specifications hold as partial correctness:** Verified
   code satisfies its stated functional specifications. Because functional
   specifications default to partial correctness, a never-returning body (such
   as `loop {}`) satisfies any postcondition unless the specification explicitly
   requires termination.

Whole-crate receipts cover the crate's entire externally reachable surface under
the same conditions, while selected-unit receipts make no claim about unverified
siblings. Any run that enables a development relaxation flag (such as allowing
`sorry` or skipping sandboxing) is irrevocably marked tainted and is not a
verification result.

**What baseline UB-freedom does not claim:** Proofs are anchored at captured
MIR, so post-capture `rustc` optimizations, LLVM codegen, linking, and hardware
execution remain TCB assumptions (optional downstream translation validation is
planned; hardware remains in the TCB at every stage). Baseline UB-freedom makes
no claim about termination, panic-freedom, timing or microarchitectural side
channels, cryptographic randomness or general hyperproperties, stack overflow or
out-of-memory errors, physical hardware faults, or logic bugs outside stated
specifications.

## Bounded human review and rendered specification closures

Once Anneal completes its trust-boundary audit
([`#4012`](https://github.com/google/zerocopy/issues/4012)), human reviewers can
skip all proof files and every verified implementation body that defines no
specification or TCB assumption, inspecting two bounded surfaces instead:

1. **The TCB audit log** — trusted without proof, recording Anneal's toolchain,
   external calls, and any waived or unverified items.
2. **The rendered specification closure** — proved against the code and reviewed
   for human intent.

A common tension in verification is inline ergonomics versus audit isolation:
developers prefer writing contracts inline on Rust items, while reviewers want
one clear diff surface that cannot be silently altered by helper functions or
macros. Anneal resolves this by always deterministically rendering the
**complete transitive definition closure of stated specifications** regardless
of whether specs are authored inline in Rust or out-of-line in Lean. Each
rendered closure includes:

- every precondition, postcondition, invariant, helper predicate, constant,
  type, trait implementation, and verified Rust helper body that affects a
  specification's meaning; and
- each specification's **resolved canonical Rust item path** (rejecting
  positional or unresolved bindings) together with each bound item's **safe /
  `unsafe fn` signature**, so reordering items, renaming a function, or flipping
  `fn` to `unsafe fn` cannot silently change what is proved.

Teams can check this rendered specification closure into version control as a
golden file guarded by `CODEOWNERS` or `OWNERS`, so any change that alters what
is proved requires specification-owner review. Optional specification sanity
checks (such as checking that a precondition has at least one valid input or
that a mutated body fails its postcondition) are positioned strictly as
**non-adversarial reviewer aids** for catching accidental contradictions or
typos—never as security defenses, because a single witness can be satisfied by a
narrowed spec such as `requires(x == 0)`.

## Library-centric verification and incremental adoption

Systems Rust lives in libraries (`zerocopy`, allocators, synchronization
primitives, kernel and cryptographic routines) that have no `fn main()`
entrypoint and expose APIs to arbitrary callers. Anneal is library-centric by
default: each function is verified modularly against its contract for all valid
caller states, safe modules can encapsulate `unsafe` code behind type invariants
preserved across normal returns and unwinding, and downstream crates can reuse
upstream verified specifications while carrying upstream TCB assumptions
forward.

Teams can adopt Anneal incrementally along two axes:

- **Breadth:** Start by verifying a single high-risk `unsafe` function while
  logging unverified callees or siblings in the TCB audit log, then retire
  assumptions over time until a whole-crate receipt covers the crate's public
  surface.
- **Depth:** Start with baseline UB-freedom (mechanizing `# Safety` comments),
  add structural postconditions and type invariants, and connect functions to
  pure mathematical models or reference implementations where needed.

## What works today vs. what is planned

| Area | Available today (alpha) | Planned |
| :--- | :--- | :--- |
| **Rust coverage** | Dependency-free, call-free scalar library crates on x86-64 Linux (`bool`, integers, `char`, `Ordering`, overflowing-arithmetic intrinsics, unit/never, fieldless enums, scalar ops and casts). Unsupported constructs fail closed. | References, slices, raw pointers and aliasing semantics, general structs/enums, function calls, `Drop`/unwinding, generics, concurrency, FFI, and inline assembly ([`#4097`](https://github.com/google/zerocopy/issues/4097), [`#4101`](https://github.com/google/zerocopy/issues/4101)). |
| **Specifications & proofs** | External Lean 4 `Spec.lean` and `Proof.lean` modules (`--manifest-path`, `--request`, or `verify rustc`), pre-elaboration spec syntax checking, and bundled proof libraries. | Inline Rust contract syntax (`core::contracts`, `anodized`, thin attributes), always-rendered golden spec closures for `CODEOWNERS`/`OWNERS`, split safety vs. behavioral contracts with explicit effect masks ([`#4102`](https://github.com/google/zerocopy/issues/4102)), and an optional zero-TCB Aeneas interop bridge. |
| **Audit & containment** | Structured verification receipts, positive 3-axiom kernel allowlist, Linux elaboration sandboxing (`bwrap` or Landlock + seccomp), `lean-miri` correspondence checks in CI, and `-Zmir-preserve-ub` capture guards. | Audited adversarial trust boundary ([`#4012`](https://github.com/google/zerocopy/issues/4012)): isolated NDJSON proof export checked by independent external kernels (`nanoda_bin`, `con-ron`; [`#4016`](https://github.com/google/zerocopy/issues/4016)), complete crate census across all item kinds, and mandatory TCB guard-mutation CI. |
| **Build & scale** | Pinned single-version `rustc` + Lean 4 archive (`cargo anneal setup`). | Multi-version `rustc` and multi-crate capture ([`#4098`](https://github.com/google/zerocopy/issues/4098)), split-action Cargo/Bazel/GN/Buck2/Nix integration, parallel crate sharding, and IDE/LSP workflows ([`#4100`](https://github.com/google/zerocopy/issues/4100), [`#4103`](https://github.com/google/zerocopy/issues/4103)). |

## Where to go next

- [`README.md`](README.md) — Motivation, quickstart, and installing the alpha.
- [`PRINCIPLES.md`](PRINCIPLES.md) and [`THREAT_MODEL.md`](THREAT_MODEL.md) —
  Correctness promise, adversarial threat model, and review boundaries.
- [`META_PRINCIPLES.md`](META_PRINCIPLES.md) — Invariant goals governing
  Anneal's principles and threat model.
- [`development/`](development/README.md) — Internal contributor documentation
  (not user-facing), including the detailed developer design overview in
  [`development/design.md`](development/design.md),
  [`development/architecture.md`](development/architecture.md), and
  [`development/trust-model.md`](development/trust-model.md).
