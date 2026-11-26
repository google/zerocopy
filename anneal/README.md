<img src="https://raw.githubusercontent.com/google/zerocopy/main/anneal/docs/images/logo.svg" alt="Anneal logo" width="100%">

<p align="center"><em>logo by <a href="https://www.instagram.com/tinyneonspark">tinyneonspark</a></em></p>

> [!WARNING]
> **This is alpha software!** Anneal (`0.2.0-alpha`, Stage 0) is an
> experimental verifier under active development and has **not** yet
> completed an independent audit of its Trusted Computing Base (TCB). Today it
> verifies only a small, pointer-free scalar subset of Rust without returning
> calls (`x86_64-unknown-linux-gnu` Profile v1) across selected functions or
> monomorphizations (`UnitTheorem`) or single scalar library or binary crates
> with no required normal or build dependencies (`CrateTheorem`). Passing
> results depend on an intact build host (`rustc`—and any `build.rs` or
> proc-macro run to produce inputs—executes outside the Lean sandbox) as well
> as human review of stated specifications (the declared primary specification
> module, every `specification`-role module, and their transitive meaning
> dependencies), compilation and scope configuration (`request.json` or
> `verify rustc` flags), and TCB audit logs (complete review-surface reporting
> remains under active development). Do not rely on alpha runs as a production
> security or soundness guarantee, and expect frequent breaking changes. See
> the [alpha guide][alpha-guide] and [threat model][threat-model].

For safe code, Rust promises that "if it compiles, then it is memory-safe."
Anneal aims to provide the same compile-time guarantee for unsafe code via
formal specifications and Lean 4 proofs (at Stage 0 alpha today, verification
covers only a scalar, pointer-free subset).

Rust promises that all safe Rust code is free of memory safety bugs. It does this by encoding the requirements for memory safety in the type system, ensuring that if a program type checks, then it is free of memory safety bugs. The lifetime system prevents use-after-free bugs, the ownership system prevents double-free bugs, and so on. **There do not exist type-checked safe Rust programs with memory safety bugs.**[^1] The same is not true of unsafe Rust code. **There do exist type-checked unsafe Rust programs with memory safety bugs.**

[^1]: Barring compiler and platform bugs, which do exist.

One way to understand this distinction is that a safe Rust function must be free of memory safety bugs *no matter what value is passed in*. Consider [`usize::strict_div`](https://doc.rust-lang.org/std/primitive.usize.html#method.strict_div):

```rust
impl usize {
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    pub fn strict_div(self, rhs: usize) -> usize;
}
```

A safe implementation of `strict_div` would be forced to handle *all possible values* of `self` and `rhs`. `strict_div` must handle the case where `rhs == 0` (division by zero). It could choose to return an arbitrary `usize` or, as it does in practice, panic. But it cannot exhibit a memory safety bug – Rust would prevent such a program from compiling.

By contrast, consider the unsafe [`usize::unchecked_div_exact`](https://doc.rust-lang.org/std/primitive.usize.html#method.unchecked_div_exact):

```rust
impl usize {
    /// # Safety
    ///
    /// This results in undefined behavior when `rhs == 0` or `self % rhs != 0`.
    pub unsafe fn unchecked_div_exact(self, rhs: usize) -> usize;
}
```

Rust doesn't have any way to express "a pair of `usize`s such that `rhs != 0`
and `self % rhs == 0`". Thus, the type signature of `unchecked_div_exact` is
*too permissive*. While it prevents some illegal values statically (e.g.,
the type system will not permit you to pass `-1`), some illegal values will
compile just fine, and will result in memory safety bugs at runtime:

```rust
let res: usize = unsafe { 1usize.unchecked_div_exact(0) };
```

In this view, unsafe Rust differs from safe Rust in that **some type-safe values
are still illegal**, while in safe Rust, **all type-safe values are legal**
(where "illegal" means "will result in a memory safety bug").

As we saw before, Rust ensures that **no type-checked safe Rust programs contain
memory safety bugs.** Anneal's goal is to provide the same promise for unsafe
Rust code by making preconditions, invariants, and postconditions
machine-checked at verification time via the Lean 4 kernel. Anneal separates
proof authoring (such as `Proof.lean`, kept outside the trusted review surfaces)
from the two human-reviewed surfaces: stated specifications (the declared
primary specification module plus every `specification`-role module and its
transitive meaning dependencies) and the TCB audit log, which covers the
[trusted computing base](https://en.wikipedia.org/wiki/Trusted_computing_base)
(TCB) and compilation/scope configuration (`request.json`).

| | Rust | Anneal (target model; Stage 0 scalar subset today) |
| - | ---- | ------ |
| **Command** | `cargo check` | `cargo anneal verify` |
| **Contract surface** | Rust types | Rust types + formal specifications (declared primary and `specification`-role modules plus transitive dependencies today; inline Rust syntax planned) |
| **Guarantee** | Safe code is free of memory safety bugs | Verified Rust is free of Rust UB under stated specs and TCB log* |
| **Caveat** | `unsafe` code is unchecked | External code outside the Rust AM is unchecked; Stage 0 refuses constructs outside scalar Profile v1* |
| **TCB** | Rust toolchain, `unsafe` code | Rust + Anneal toolchains, compilation/scope configuration (`request.json`), code outside the Rust AM* |

\* *Anneal cannot verify code that lives outside the Rust Abstract Machine (AM),
such as FFI or inline assembly; callers must axiomatically specify its behavior
in the TCB. At Stage 0 alpha, Anneal supports only the pointer-free scalar MIR
fragment without returning calls (`Profile v1` on `x86_64-unknown-linux-gnu`)
and fails closed (`unsupported`) on references, raw pointers, structs, slices,
returning calls, and unsupported items; see the [alpha guide][alpha-guide] for
the exact boundary.*

### Development Philosophy

Anneal is a [formal verification][formal-verification] tool designed for
inner-loop developer and CI feedback rather than purely post-hoc verification:

1. Developers already hold mental justifications (preconditions and invariants)
   for why code is valid; Anneal turns those justifications into explicit formal
   contracts.
2. Verification shapes code toward modular, cleanly specified boundaries as code
   is written.
3. Short `cargo anneal verify` runs can execute locally alongside `cargo check`
   and continuously in CI so specifications and proofs never drift from code.

At Stage 0 alpha, specifications and proofs live out-of-line in Lean 4 (for
example, `Spec.lean` and `Proof.lean` via `request.json`, or explicit
`--spec-file` and `--proof-file` flags on `cargo anneal verify rustc`). Inline
Rust specification syntax is planned roadmap work.

### Human and agentic workflow

Anneal is built for both human engineers and AI coding agents. Lean's kernel
checks proof scripts automatically, keeping human review focused on the two
trusted review surfaces rather than reading every line of proof modules (see the
[threat model][threat-model]):

1. Stated specifications (the declared primary specification module plus every
   `specification`-role module and its transitive meaning dependencies—such as
   `Spec.lean` or custom `--spec-file` modules declaring caller preconditions in
   `safety` and behavior/postconditions in `property`); and
2. The TCB audit log (covering the pinned toolchains, the compilation and
   scope configuration in `request.json` or `verify rustc` flags—target triple,
   `cfg`, `env`, `crate_root`, `source_files`, `scope.roots`—and any host or
   axiomatic assumptions recorded in the Receipt v3 fields: `taint_reasons`,
   `elaboration_sandbox`, `assumptions`, `deferred`, and `audit`).

Automated reporting across the complete review surface (recorded in `deferred`
as `"complete review-surface reporting"`) remains under active development.

[formal-verification]: https://en.wikipedia.org/wiki/Formal_verification

## Try the alpha

The alpha verifies selected Rust functions or scalar library or binary crates
with no required normal or build dependencies (dev-dependencies and inactive
optional dependencies are ignored) on x86-64 Linux with glibc.

Install a published prerelease from [GitHub Releases][releases] (replacing
`<version>` with the version from the latest `anneal-v<version>` tag without the
`anneal-v` prefix), verify with `setup` / `init` / `verify`, and check
`cargo anneal skill` for agent guidance:

```sh
cargo install --locked cargo-anneal@<version>
cargo anneal setup
cargo anneal init --standalone --proof-dir hello
cd hello
cargo anneal verify --request request.json
```

When building from a source checkout whose `Cargo.toml` tracks `0.0.0-dev`
with an all-zero archive digest, or when testing local compiler or Lean edits,
either build and install a local archive via
`cargo anneal setup --local-archive target/omnibus-link` or pass `--capture`,
`--sysroot`, and `--lean` directly to `cargo anneal verify`; see the
[alpha guide][alpha-guide].

`cargo anneal init --standalone` writes four files into `hello/`:

- `lib.rs` — a minimal scalar library crate (`pub fn zero() -> u64 { 0 }`);
- `request.json` — binds `lib.rs`, `scope` (`selected_unit` root `zero`), and
  the Lean modules below;
- `Spec.lean` — defines `Spec.specs`, requiring `zero()` to terminate without
  diverging and return `0u64`; and
- `Proof.lean` — discharges `Expected.claim` against captured MIR using
  `Anneal.MirWp`.

```rust
pub fn zero() -> u64 {
    0
}
```

On success (`exit 0`), `cargo anneal verify --request request.json` prints a
human verification card to stdout (`[SCOPED]` for a selected function, `[OK]`
only for untainted whole-crate verification). Pass `--format json` to emit the
Receipt Schema v3 JSON object directly on stdout, or `--receipt-out <path>` to
write it atomically to disk alongside the human card (condensed below from a
Linux `ExecSeal` run: `audit`, `census`, `configuration`,
`correspondence_provenance`, `selected`, `sources`, `toolchain_identity`,
digests, and `timing_ms` fields are omitted for brevity; on Linux,
`elaboration_sandbox` is `linux_bwrap` or `linux_landlock_seccomp` by default):

```json
{
  "schema_version": 3,
  "status": "selected_unit_verified",
  "experimental": true,
  "elaboration_sandbox": "linux_bwrap",
  "taint_reasons": [],
  "spec_warnings": [],
  "scope": { "kind": "selected_unit", "roots": ["zero"] },
  "assumptions": [
    "faithful pinned compiler capture",
    "experimental pointer-free MIR semantics",
    "Lean kernel and admitted foundation",
    "intact compiler and verification environment"
  ],
  "deferred": [
    "complete review-surface reporting",
    "source-to-deployed-binary correspondence"
  ]
}
```

To verify that the check is live, edit `lib.rs` to return `1` and rerun
`cargo anneal verify --request request.json`: verification fails with exit code
`1`, a `[FAIL]` card (`"status": "proof_failed"` with `--format json`), and the
failing Lean diagnostic and file/line location in `Proof.lean`. To inspect
captured MIR (`Captured.lean`) and the proof obligation (`Expected.lean`)
directly, pass `--artifacts <new-directory>` (`verify` rejects a path that
already exists, or whose parent is not an existing directory, before starting
verification work). To rerun into the same path, add `--overwrite-artifacts`:
it replaces only an earlier artifact directory that `verify` wrote, or an empty
directory (see the [alpha guide][alpha-guide]).

[alpha-guide]: https://github.com/google/zerocopy/blob/main/anneal/docs/alpha.md
[releases]: https://github.com/google/zerocopy/releases
[threat-model]: https://github.com/google/zerocopy/blob/main/anneal/THREAT_MODEL.md

## Agent skill

Run `cargo anneal skill` to print the bundled `cargo-anneal` `SKILL.md`
without setting up the Anneal toolchain.

To make the skill discoverable before an agent runs `cargo anneal`, install it
with [GitHub CLI][gh-skill]. Set `ANNEAL_REV` to the release tag or source
commit for your `cargo-anneal` build and run this from your project's Git
repository.

```sh
gh skill install google/zerocopy \
  anneal/trusted/cargo-anneal/skills/cargo-anneal/SKILL.md \
  --agent codex --scope project --pin "${ANNEAL_REV:?set the source revision}"
```

For authoring formal specifications or scaling larger Lean proofs, see the
companion [spec-authoring][spec-authoring-skill] and
[proof-scaling][proof-scaling-skill] skills in the
[Anneal skills index][skills-index]. `cargo-anneal` bundles both: run
`cargo anneal skill list` to list the bundled skills, and
`cargo anneal skill spec-authoring` or `cargo anneal skill proof-scaling` to
print one.

Choose the `--agent` value for your host. Commit the installed skill to share
it with teammates and agents working in fresh checkouts.

[gh-skill]: https://cli.github.com/manual/gh_skill_install
[spec-authoring-skill]: https://github.com/google/zerocopy/blob/main/anneal/skills/spec-authoring/SKILL.md
[proof-scaling-skill]: https://github.com/google/zerocopy/blob/main/anneal/skills/proof-scaling/SKILL.md
[skills-index]: https://github.com/google/zerocopy/blob/main/anneal/skills/README.md

## Repository checks

See the [contributor guide][developing-anneal] to build the local toolchain
archive and audit the trust boundary, the [scaffold guide][scaffold-guide] to
run installed smoke cases and reproduce retained failures, and the
[Gate 2 review guide][codex-review] for required merge checks.

[developing-anneal]: https://github.com/google/zerocopy/blob/main/anneal/docs/README.md
[scaffold-guide]: https://github.com/google/zerocopy/blob/main/anneal/docs/scaffolding.md
[codex-review]: https://github.com/google/zerocopy/blob/main/anneal/docs/codex-review.md

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
  informed Anneal's study of the semantics behind this translation. Johannes
  Hostert's [Aeneas layout model][aeneas-layouts] informed `SpatialMem`'s
  byte-level aggregate codecs.
- PureLift uses lawful bidirectional lenses. J. Nathan Foster, Michael B.
  Greenwald, Jonathan T. Moore, Benjamin C. Pierce, and Alan Schmitt developed
  these foundations in [Combinators for Bidirectional Tree
  Transformations][tree-lenses].
- Anneal's tristate-number (`tnum`) bitwise and carry-propagation transfer
  functions adapt the `tnum` abstract domain formalized by Harishankar
  Vishwanathan, Matan Shachnai, Srinivas Narayana, and Santosh Nagarakatte in
  [Sound, Precise, and Fast Abstract Interpretation with Tristate
  Numbers][tnum-paper] and used in the Linux kernel's eBPF verifier. Anneal's
  reduced-product MIR abstract-interpretation checker (`Anneal.AiPcc`) combines
  `tnum` with [wrapped intervals][wrapped-intervals] by Jorge A. Navas, Peter
  Schachte, Harald Søndergaard, and Peter J. Stuckey, [arithmetical
  congruences][congruences] by Philippe Granger, and single-pass cutpoint
  post-fixpoint checking following François Bourdoncle's [weak topological
  orderings][bourdoncle-wto].
- Anneal's $\mathbb{F}_2$-linear and $\mathbb{F}_2$-bilinear SIMD and
  carryless-multiply certificate evaluators draw on Shay Gueron and Michael E.
  Kounavis's [carryless polynomial multiplication and reduction][clmul-gcm] and
  Wojciech Muła, Nathan Kurz, and Daniel Lemire's [split-nibble SIMD table
  lookups][mula-simd].
- Anneal's proof-lifting experiments drew on Magnus O. Myreen, Michael J. C.
  Gordon, and Konrad Slind's [decompilation into logic][decompilation] to
  reason about one basic block at a time. [Tree Borrows][tree-borrows] by
  Neven Villani, Johannes Hostert, Derek Dreyer, and Ralf Jung guided
  experiments on how to account for mutable borrow permissions. [Gillian-Rust]
  by Sacha-Élie Ayoun, Xavier Denis, Petar Maksimović, and Philippa Gardner,
  [CN] by Christopher Pulte, Dhruv C. Makwana, Thomas Sewell, Kayvan Memarian,
  Peter Sewell, and Neel Krishnaswami, and [Fulminate] by Rini Banerjee, Kayvan
  Memarian, Dhruv Makwana, Christopher Pulte, Neel Krishnaswami, and Peter
  Sewell informed `SpatialMem`'s hybrid pure-and-byte pinning and padding
  representation.
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
- Google DeepMind's [`code-verification`][code-verification] (`ProofLib`,
  Apache-2.0) inspired Anneal's balanced Braun-tree separation-logic AC
  reflection (`Anneal.Core.SepPCM`) and sparse linear bitvector offset
  normalizer (`Anneal.PureLift.BvLin`).
- Michael Sammler, Rodolphe Lepigre, Robbert Krebbers, Kayvan Memarian, Derek
  Dreyer, and Deepak Garg's [RefinedC][refinedc] and its Lithium
  separation-logic engine inspired `Anneal.SepAC.RangeSpan`'s deterministic
  non-backtracking `PTree.diffWith` framing rules.

[Aeneas]: https://arxiv.org/abs/2206.07185
[Charon]: https://link.springer.com/chapter/10.1007/978-3-031-98685-7_18
[symbolic-borrows]: https://arxiv.org/abs/2404.02680
[aeneas-layouts]: https://github.com/AeneasVerif/aeneas/pull/1447
[tree-lenses]: https://doi.org/10.1145/1232420.1232424
[tnum-paper]: https://arxiv.org/abs/2105.05398
[wrapped-intervals]: https://doi.org/10.1007/978-3-642-35182-2_9
[congruences]: https://doi.org/10.1080/00207168908803778
[bourdoncle-wto]: https://doi.org/10.1007/BFb0039704
[clmul-gcm]: https://doi.org/10.1016/j.ipl.2010.04.011
[mula-simd]: https://doi.org/10.1093/comjnl/bxx046
[decompilation]: https://www.cl.cam.ac.uk/~mom22/decompilation/fmcad12.pdf
[tree-borrows]: https://iris-project.org/pdfs/2025-pldi-treeborrows.pdf
[Gillian-Rust]: https://doi.org/10.1145/3729289
[CN]: https://doi.org/10.1145/3571194
[Fulminate]: https://doi.org/10.1145/3704879
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
[code-verification]: https://github.com/google-deepmind/code-verification
[refinedc]: https://doi.org/10.1145/3453483.3454036
