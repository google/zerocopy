# Anneal

<img src="https://raw.githubusercontent.com/google/zerocopy/main/anneal/assets/logo.svg" alt="Anneal logo" width="100%">

<p align="center"><em>logo by <a href="https://www.instagram.com/tinyneonspark">tinyneonspark</a></em></p>

> [!WARNING]
> **Stage 0 alpha (`experimental: true`) — not yet production-audited.**
> Anneal currently verifies selected functions and dependency-free, call-free
> scalar library crates on `x86_64-unknown-linux-gnu` (Profile v1 scalar MIR).
> Both the verifier and its Receipt v3 TCB audit log are still under active
> development and have not yet completed the independent Stage 1 trust-boundary
> audit ([`#4012`](https://github.com/google/zerocopy/issues/4012)). Treat a
> Stage 0 pass as an early confidence-building tool rather than an audited
> soundness boundary, and expect frequent API changes.

## Anneal's Verification Promise

> **In one sentence:** If every entry in Anneal's TCB audit log is correct, an
> untainted receipt means verified safe APIs have no undefined behavior for any
> caller, verified `unsafe` APIs have none for callers meeting their formal
> safety preconditions, and verified code meets its stated specifications as
> partial correctness. All of this is proved at the captured MIR and, in
> today's Stage 0 alpha, not yet adversarially audited.

> **Anneal's Verification Promise *(currently Stage 0 alpha,
> `experimental: true` — pointer-free, call-free scalar/enum/unit MIR on
> `x86_64-unknown-linux-gnu`; adversarial trust boundary to be audited in Stage
> 1)*:** When Anneal runs in an intact, isolated execution environment
> (including isolation from untrusted compile-time Rust code such as `build.rs`
> and procedural macros) and emits an **untainted** passing verification
> receipt immutably bound to an exact captured source, specification set,
> target, `cfg` set, and compiler profile, the guarantee holds at the captured
> MIR boundary whenever every component in the **TCB audit log**—including
> Anneal's MIR semantics (its definition of UB), capture/audit boundary,
> toolchain assumptions, external calls, and every waived or unverified item in
> scope and transitive dependencies—is correct and its assumptions are
> **jointly valid** of the real system. Under those conditions:
>
> 1. **Safe Rust APIs:** Every verified **safe** Rust API is **free of Rust
>    Undefined Behavior (UB)** across all execution prefixes (terminating,
>    diverging, or panicking) for all type-correct calls satisfying applicable
>    library invariants (each preserved by every constructor and mutator, even
>    on unwind, as proved or logged in the TCB) in any safe calling
>    context—including open-world callbacks and interior mutability—and no user
>    specification or scope clause can narrow that baseline.
> 2. **`unsafe` Rust APIs:** Every verified **`unsafe`** API is **free of UB**
>    across all prefixes whenever callers discharge its formally stated
>    `# Safety` preconditions (which never relax Rust language validity).
> 3. **Stated functional specifications:** Verified code **satisfies its stated
>    functional specifications** (partial correctness: a never-returning body
>    meets any postcondition unless return is required).
>
> Under the same conditions, whole-crate receipts cover the crate's entire
> externally reachable surface (selected-unit receipts make no claim about
> unverified siblings). Once Stage 1 completes its adversarial trust-boundary
> audit (positive axiom allowlist, no untrusted compiled proof artifacts in the
> verdict process, complete crate census), reviewers can skip all proof files
> and every verified implementation body that defines no specification or TCB
> assumption, and inspect two bounded surfaces: the **TCB audit log** (assumed
> without proof) and the **complete, unambiguously rendered transitive
> definition closure of stated specifications, with the captured items each one
> binds to and their safe/`unsafe` status** (proved against the code, reviewed
> for human intent and non-vacuity). Tainted development runs are irrevocably
> labeled tainted and are not verification results; Anneal aims to support all
> Rust program behaviors and otherwise fails closed with structured failure
> receipts rather than failing open; and baseline UB-freedom makes no claim
> about post-capture `rustc`/LLVM/linker/hardware lowering (explicitly tracked
> in the TCB), termination, panic-freedom (nor do assumed contracts silently
> assume progress), timing or microarchitectural side channels, hyperproperties
> or randomness preservation, finite physical resource bounds, hardware faults,
> or logic bugs outside stated specifications.

### What Anneal Does Not Promise (Unless Separately Modeled & Specified)

- **Not production-audited at Stage 0:** Today's alpha (`experimental: true`)
  is not yet audited against adversarial proof files or hostile crates;
  skipping proof review requires the audited Stage 1 trust boundary
  ([`#4012`](https://github.com/google/zerocopy/issues/4012)).
- **Not end-to-end binary verification (yet):** Proofs are anchored at
  **captured MIR**. Post-capture `rustc` MIR optimizations, LLVM codegen, and
  linking sit explicitly in the TCB until optional downstream translation
  validation is added
  ([`#3867`](https://github.com/google/zerocopy/issues/3867)); hardware
  execution remains a TCB assumption at every stage.
- **Not human intent or external standards:** Anneal proves code satisfies its
  *stated* specifications; it cannot confirm that developer- or agent-authored
  functional specs match external RFCs or human intent, nor catch
  self-consistent spec-plus-code bugs. Optional kernel-checked
  anti-vacuity/realizability checks (proposed in
  [`#4112`](https://github.com/google/zerocopy/issues/4112)) are reviewer aids,
  not a substitute for reviewing stated specs.
- **Not progress, constant-time, or all security bugs:** Baseline UB-freedom is
  all-prefix safety, and functional specifications are partial correctness
  unless they require termination. Baseline UB-freedom makes no claim about
  termination, panic-freedom (nor do assumed contracts silently assume
  progress), timing or microarchitectural side channels, cryptographic
  randomness or general hyperproperties (which trace refinement does not
  preserve), finite physical resource bounds (stack overflow or OOM), physical
  hardware faults, or logic/security vulnerabilities outside stated specs (such
  as authorization bypasses or algorithmic DoS).
- **Not tainted dev outputs:** Any run enabling `--allow-sorry-in-proof`,
  `--allow-unpinned-lean`, or `--allow-unsandboxed-elaboration` is irrevocably
  marked `tainted_*` in both CLI banners and Receipt v3 and does not constitute
  a verification result.

## Current Alpha Scope vs. Roadmap

Anneal tracks maturity across three public milestones:
[Stage 0 — Alpha usability (`#4095`)][stage-0] →
[Stage 1 — Audited trust boundary & TCB accounting (`#4012`)][stage-1] →
[Stage 2 — Broad systems Rust & TCB reduction (`#4096`)][stage-2].

| Area | Shipped Today (Stage 0 Alpha — Profile v1) | Active Roadmap (Stage 1 & Stage 2) |
| :--- | :--- | :--- |
| **Rust MIR coverage** | Dependency-free, call-free scalar/enum/unit MIR on `x86_64-unknown-linux-gnu`: `bool`, 8–128-bit & pointer-sized integers, `char`, `Ordering`, `(T, bool)` overflowing-arithmetic intrinsics, unit/never, local fieldless enums, scalar ops & casts (`-Copt-level=0`, `-Cdebug-assertions=no`, `-Coverflow-checks=no`). Calls, runtime `Assert` terminators (incl. ordinary `/` and `%`), place projections, and aggregates fail closed. | References, slices, `unsafe` raw pointers & Tree Borrows, general ADTs/aggregates, function calls, `Drop`/unwinding, generics, concurrency, `asm!`/FFI ([`#4097`](https://github.com/google/zerocopy/issues/4097), [`#4101`](https://github.com/google/zerocopy/issues/4101)). |
| **Specifications & proofs** | External Lean 4 `Spec.lean` (with live `"spec-preflight"`) & `Proof.lean` modules (`--manifest-path`, `--request`, or `verify rustc`), plus bundled 3-axiom `Anneal.*` proof libraries. Functional specs are partial correctness (termination such as `¬ Diverges` must be stated when required). | Inline Rust contract syntax (`core::contracts`, `anodized`, thin attributes), always-rendered golden spec closure binding canonical item paths & safe/`unsafe` signatures for `CODEOWNERS`/`OWNERS` gating, `Spec Core v2` ([`#4102`](https://github.com/google/zerocopy/issues/4102)). |
| **Audit & containment** | Receipt Schema v3, positive 3-axiom allowlist, Linux `ExecSeal` (`bwrap` / Landlock + seccomp), Pass 2 correspondence against pinned `lean-miri`, and fail-closed `-Zmir-preserve-ub`, `PlaceMention`, and `CallSource::Use` capture guards (`#4114`, closing `#4042`/`#4083`). | Audited Stage 1 boundary ([`#4012`](https://github.com/google/zerocopy/issues/4012)): Universal NDJSON Comparator with independent external kernels (`nanoda_bin`, `con-ron`; [`#4016`](https://github.com/google/zerocopy/issues/4016)), complete crate census across every item kind (including body-less items), typed audit results, and mandatory guard-mutation CI. |
| **Toolchains & scale** | Pinned single-version `rustc` + Lean 4 toolchain archive (`cargo anneal setup`). | Multi-version `rustc` & multi-crate capture ([`#4098`](https://github.com/google/zerocopy/issues/4098)), split-action Cargo/Bazel/GN/Buck2/Nix integration, crate sharding, LSP/MCP workflows ([`#4100`](https://github.com/google/zerocopy/issues/4100), [`#4103`](https://github.com/google/zerocopy/issues/4103)). |

## Documentation Map

| Document | Audience | Contents |
| :--- | :--- | :--- |
| [`README.md`][readme-doc] | Users | Verification promise, Stage 0 alpha scope, quickstart, and conceptual motivation. |
| [`DESIGN.md`][design-doc] | Users & architects | End-to-end architecture (implemented vs. planned), golden spec closure, NDJSON comparator, build integration, and specification modes. |
| [`PRINCIPLES.md`][principles-doc] | Users & maintainers | Governing mission, conditional correctness promise, and decision priorities. |
| [`THREAT_MODEL.md`][threat-model-doc] | Security reviewers & users | Adversarial threat model, bounded two-surface human review, explicit assumptions, and total defenses. |
| [`META_PRINCIPLES.md`][meta-principles-doc] | Maintainers | Invariant goals governing `PRINCIPLES.md` and `THREAT_MODEL.md`. |

> [!NOTE]
> Internal contributor and developer documentation (architecture deep dives,
> trust-boundary enforcement details, build/test scaffolding, and review
> policy) lives under [`development/`][development-dir] and is **not**
> user-facing documentation.

## Why Anneal (Target Design Vision)

*This section motivates Anneal's target design; see [Current Alpha Scope vs.
Roadmap](#current-alpha-scope-vs-roadmap) and [Try the alpha](#try-the-alpha)
for what runs today.*

For safe code, Rust promises that "if it compiles, then it is memory-safe."
Anneal aims to provide the same assurance for `unsafe` code at the captured MIR
boundary.

Rust promises that safe Rust code is free of memory-safety bugs by encoding
memory-safety requirements in its type system—lifetimes prevent use-after-free,
ownership prevents double-free, and so on.[^1] By contrast, **type-checked
`unsafe` Rust programs can still exhibit undefined behavior.**

[^1]: Barring compiler, standard-library, and platform bugs, which do exist.

Consider [`usize::strict_div`](https://doc.rust-lang.org/std/primitive.usize.html#method.strict_div):

```rust
impl usize {
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    pub fn strict_div(self, rhs: usize) -> usize;
}
```

A safe implementation of `strict_div` must handle *all possible values* of
`self` and `rhs`—including `rhs == 0`—without triggering undefined behavior. By
contrast, consider the `unsafe` [`usize::unchecked_div_exact`](https://doc.rust-lang.org/std/primitive.usize.html#method.unchecked_div_exact):

```rust
impl usize {
    /// # Safety
    ///
    /// This results in undefined behavior when `rhs == 0` or `self % rhs != 0`.
    pub unsafe fn unchecked_div_exact(self, rhs: usize) -> usize;
}
```

Rust's type system has no way to express "a pair of `usize`s such that
`rhs != 0` and `self % rhs == 0`." Its type signature is therefore *too
permissive*: illegal values still compile and trigger undefined behavior at
runtime:

```rust
let res: usize = unsafe { 1usize.unchecked_div_exact(0) };
```

Anneal extends Rust's static checks with formal specifications checked in Lean
4. An `unsafe fn`'s `# Safety` preconditions become machine-checked obligations
that verified callers must discharge at every call site, while a safe `fn` must
prove UB-freedom unconditionally across all type-valid inputs (never narrowed by
user specifications).

```rust
// Target inline-contract vision (in development under #4102; syntax may change).
impl usize {
    /// # Safety
    ///
    /// Requires `rhs != 0` and `self % rhs == 0`.
    #[requires(rhs != 0)]
    #[requires(self % rhs == 0)]
    pub unsafe fn unchecked_div_exact(self, rhs: usize) -> usize;
}

let res: usize = unsafe { 1usize.unchecked_div_exact(0) }; // ERROR: Cannot prove `rhs != 0`
```

*Support for inline Rust contract syntax is under development
([`#4102`](https://github.com/google/zerocopy/issues/4102)). Today's Stage 0
alpha attaches specifications in external `Spec.lean` modules.*

Once Stage 1 closes the audited trust boundary, Anneal removes verified
`unsafe` Rust code from your
[trusted computing base](https://en.wikipedia.org/wiki/Trusted_computing_base)
(TCB):\*

| | Rust | Anneal (target, Stage 1+) |
| :--- | :--- | :--- |
| **Check** | `cargo check` | `cargo anneal verify` |
| **Contracts** | Rust types | Rust types + stated specifications |
| **Guarantee** | Safe code is UB-free | Safe and verified `unsafe` code is UB-free at captured MIR\* |
| **Caveat** | `unsafe` code is unchecked | Code outside the modeled Rust Abstract Machine (AM) is assumed\* |
| **TCB** | Rust toolchain, all `unsafe` code | Rust + Anneal toolchains, post-capture lowering, code outside the Rust AM\* |

\* *Anneal cannot verify code that executes outside the modeled Rust Abstract
Machine, such as C FFI or unmodeled inline assembly; its contract must be
stated as an explicit assumption recorded in the TCB audit log. Rust code that
**calls** those constructs can still be verified against their logged
contracts, removing the calling `unsafe` Rust code from the TCB.*

### Development Philosophy

Formal verification has historically been applied *post-hoc* to existing
codebases, which assumes separate specialist workflows, fights unverified code
structure, stretches feedback loops, and lets proofs drift from code. Anneal
treats specifications as an extension of Rust's type system:

1. Developers already hold informal justifications for why their `unsafe` code
   is sound; specifications make those justifications explicit and
   machine-checked.
2. Inner-loop verification nudges code organization toward clean abstraction
   boundaries and explicit invariants as code is written.
3. CI runs `cargo anneal verify` alongside `cargo test` so specifications,
   proofs, and code stay synchronized on every change.

### Human and Agentic Development

Anneal is built for both human engineers and AI coding agents. Writing formal
proofs is labor-intensive, whereas auditing a bounded set of contracts and
assumptions is tractable. Under Anneal's target Stage 1 threat model
([`THREAT_MODEL.md`][threat-model-doc]), untrusted contributors or AI coding
agents can author complex `unsafe` Rust implementations and Lean 4 proofs while
human reviewers skip all proof files and every verified implementation body
that defines no specification or TCB assumption—reviewing the **always-rendered
golden specification closure** (including each specification's bound Rust item
paths, safe/`unsafe` signatures, and any referenced Rust helper bodies,
optionally gated via `CODEOWNERS` / `OWNERS`) and the **TCB audit log** (for
assumed components and waivers).

## Try the alpha

The Stage 0 alpha verifies selected Rust functions or dependency-free scalar
library crates on x86-64 Linux with glibc. Follow the
[alpha guide][alpha-guide] to install it and check a runnable proof.

## Agent skill

Run `cargo anneal skill` to print the bundled `SKILL.md` without setting up
the Anneal toolchain.

To make the skill discoverable before an agent runs `cargo anneal`, install it
with [GitHub CLI][gh-skill]. Set `ANNEAL_REV` to the release tag or source
commit for your `cargo-anneal` build and run this from your project's Git
repository.

```sh
gh skill install google/zerocopy \
  anneal/trusted/cargo-anneal/skills/cargo-anneal/SKILL.md \
  --agent codex --scope project --pin "${ANNEAL_REV:?set the source revision}"
```

Choose the `--agent` value for your host. Commit the installed skill to share
it with teammates and agents working in fresh checkouts.

## Contributor checks and internal docs

Contributor build, audit, and review documentation lives in
[`development/`][development-dir] (internal developer docs, not user-facing):

- [Contributor guide][developing-anneal] to build the local toolchain archive
  and run repository trust-boundary audits.
- [Scaffold guide][scaffold-guide] to run installed smoke cases and reproduce
  retained failures.
- [Codex review guide][codex-review] for required merge gates.

Subsystem tracking umbrellas on `google/zerocopy`:
[MIR (`#4097`)](https://github.com/google/zerocopy/issues/4097),
[Capture (`#4098`)](https://github.com/google/zerocopy/issues/4098),
[Audit (`#4099`)](https://github.com/google/zerocopy/issues/4099),
[Theory (`#4100`)](https://github.com/google/zerocopy/issues/4100),
[FFI/ISA (`#4101`)](https://github.com/google/zerocopy/issues/4101),
[Specs (`#4102`)](https://github.com/google/zerocopy/issues/4102), and
[UX (`#4103`)](https://github.com/google/zerocopy/issues/4103).

## Acknowledgments

Anneal builds on decades of work and research in formal verification and the
study of programming languages, among other fields. It is only possible thanks
to the work of countless researchers and software engineers. Some of the most
significant influences are listed here, but this list is far from exhaustive.

- Son Ho and Jonathan Protzenko's [Aeneas] inspired PureLift's translation of
  Rust borrows and updates into pure computations. Early Anneal used Aeneas
  to translate Rust into Lean and [Charon] to extract Rust programs for
  analysis. Charon is by Son Ho, Guillaume Boisseau, Lucas Franceschino, Yoann
  Prak, Aymeric Fromherz, and Jonathan Protzenko. Son Ho, Aymeric Fromherz, and
  Jonathan Protzenko's [work on symbolic borrow checking][symbolic-borrows]
  informed Anneal's study of the semantics behind this translation.
- PureLift uses lawful bidirectional lenses. J. Nathan Foster, Michael B.
  Greenwald, Jonathan T. Moore, Benjamin C. Pierce, and Alan Schmitt developed
  these foundations in [Combinators for Bidirectional Tree
  Transformations][tree-lenses].
- Anneal's tristate-number (`tnum`) bitwise and carry-propagation transfer
  functions adapt the `tnum` abstract domain formalized by Harishankar
  Vishwanathan, Matan Shachnai, Srinivas Narayana, and Santosh Nagarakatte in
  [Sound, Precise, and Fast Abstract Interpretation with Tristate
  Numbers][tnum-paper] and used in the Linux kernel's eBPF verifier.
- Anneal's proof-lifting experiments drew on Magnus O. Myreen, Michael J. C.
  Gordon, and Konrad Slind's [decompilation into logic][decompilation] to
  reason about one basic block at a time. [Tree Borrows][tree-borrows] by
  Neven Villani, Johannes Hostert, Derek Dreyer, and Ralf Jung guided
  experiments on how to account for mutable borrow permissions.
- Anneal's MIR correspondence proofs use a pinned, patched copy of
  [lean-miri]. Yuichi Nishiwaki's port builds on the Rust compiler's MIR
  interpreter and the work of the [Miri developers and contributors][Miri].
  Ralf Jung's [MiniRust] and the Rust Unsafe Code
  Guidelines contributors' [discussion of moved values][ucg-moves] helped
  inform Anneal's treatment of moves. Xavier Leroy and the [CompCert]
  contributors' work on simulation proofs provided a comparison for how
  Anneal relates its model to its reference semantics.
- [Lean 4], by Leonardo de Moura, Sebastian Ullrich, and the Lean
  contributors, checks Anneal's proofs. Lean's
  [declaration replay][lean-replay], [environment importer][lean-env],
  compiler-attribute handling, and kernel reduction behavior guided Anneal's
  auditor and PureLift's combinators.
- Anneal's elaborator sandbox builds on [Bubblewrap], by Alexander Larsson,
  Colin Walters, and the Bubblewrap contributors, on Linux's [Landlock]
  security module, by Mickaël Salaün and the Linux kernel contributors, and on
  Linux's [seccomp-BPF] syscall filter, by Will Drewry and the Linux kernel
  contributors.
- The Rust contributors' [compiler source][rustc] (including
  [`rustc_const_eval`][rustc-const-eval] and [a padding-clearing
  issue][rust-148470]) and [Rust Reference] guided Anneal's MIR capture and
  model of Rust behavior. The earlier memory model also drew on the
  [standard library documentation][rust-std]. The LLVM contributors'
  [language reference][llvm-linkage] guided Anneal's treatment of Rust's
  linkage attributes.
- Early design work drew on
  [research into security risks in Rust][rust-security] by Xiaoye Zheng,
  Zhiyuan Wan, Yun Zhang, Rui Chang, and David Lo. Lars Bergstrom's
  [Rust Nation UK talk][rust-nation], Jeff Vander Stoep's
  [Android delivery data][android-rust], and Hongliang Tian's
  [account of the Asterinas kernel][asterinas] gave the early design concrete
  examples of Rust development and the work involved in writing unsafe code.
- The [Fuchsia] and [Starnix eBPF][starnix-ebpf] contributors' production Rust
  crates and build integration shaped Anneal's out-of-tree verification
  interface and end-to-end verification tests.

[stage-0]: https://github.com/google/zerocopy/issues/4095
[stage-1]: https://github.com/google/zerocopy/issues/4012
[stage-2]: https://github.com/google/zerocopy/issues/4096
[readme-doc]: https://github.com/google/zerocopy/blob/main/anneal/README.md
[design-doc]: https://github.com/google/zerocopy/blob/main/anneal/DESIGN.md
[principles-doc]: https://github.com/google/zerocopy/blob/main/anneal/PRINCIPLES.md
[threat-model-doc]: https://github.com/google/zerocopy/blob/main/anneal/THREAT_MODEL.md
[meta-principles-doc]: https://github.com/google/zerocopy/blob/main/anneal/META_PRINCIPLES.md
[development-dir]: https://github.com/google/zerocopy/tree/main/anneal/development
[alpha-guide]: https://github.com/google/zerocopy/blob/main/anneal/development/alpha.md
[developing-anneal]: https://github.com/google/zerocopy/blob/main/anneal/development/README.md
[scaffold-guide]: https://github.com/google/zerocopy/blob/main/anneal/development/scaffolding.md
[codex-review]: https://github.com/google/zerocopy/blob/main/anneal/development/codex-review.md
[gh-skill]: https://cli.github.com/manual/gh_skill_install
[Aeneas]: https://arxiv.org/abs/2206.07185
[Charon]: https://link.springer.com/chapter/10.1007/978-3-031-98685-7_18
[symbolic-borrows]: https://arxiv.org/abs/2404.02680
[tree-lenses]: https://doi.org/10.1145/1232420.1232424
[tnum-paper]: https://arxiv.org/abs/2105.05398
[decompilation]: https://www.cl.cam.ac.uk/~mom22/decompilation/fmcad12.pdf
[tree-borrows]: https://iris-project.org/pdfs/2025-pldi-treeborrows.pdf
[lean-miri]: https://github.com/proofs-rs/lean-miri
[Miri]: https://github.com/rust-lang/miri
[MiniRust]: https://github.com/minirust/minirust
[ucg-moves]: https://github.com/rust-lang/unsafe-code-guidelines/issues/188
[CompCert]: https://compcert.org/
[Lean 4]: https://lean-lang.org/papers/lean4.pdf
[lean-replay]: https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Replay.lean
[lean-env]: https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Environment.lean
[Bubblewrap]: https://github.com/containers/bubblewrap
[Landlock]: https://docs.kernel.org/userspace-api/landlock.html
[seccomp-BPF]: https://docs.kernel.org/userspace-api/seccomp_filter.html
[rustc]: https://github.com/rust-lang/rust/tree/main/compiler
[rustc-const-eval]: https://github.com/rust-lang/rust/tree/main/compiler/rustc_const_eval/src/interpret
[rust-148470]: https://github.com/rust-lang/rust/issues/148470
[Rust Reference]: https://doc.rust-lang.org/reference/
[rust-std]: https://doc.rust-lang.org/std/
[llvm-linkage]: https://llvm.org/docs/LangRef.html#linkage-types
[rust-security]: https://arxiv.org/abs/2308.15046
[rust-nation]: https://www.youtube.com/watch?v=QrrH2lcl9ew
[android-rust]: https://blog.google/security/rust-in-android-move-fast-fix-things/
[asterinas]: https://asterinas.github.io/2025/06/04/kernel-memory-safety-mission-accomplished.html
[Fuchsia]: https://fuchsia.dev/
[starnix-ebpf]: https://fuchsia.googlesource.com/fuchsia/+/823a15538f191b9dbd9ebafaa6ba23220b87d2e1/src/starnix/lib/ebpf/core/src
