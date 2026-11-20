---
name: trust-review
description: >-
  Audit code changes, commits, and pull requests in joshlf/anneal to preserve
  Anneal's trust model and correctness promise. Use as a distinct review pass
  whenever reviewing changes or preparing modifications to verify both that code
  outside trusted/, ci/, and .github/ does not bypass trust auditing and that
  changes inside trusted/, ci/, .github/, and pinned root manifests preserve TCB
  soundness and enforcement completeness.
---

# Trust-boundary code review

Use this skill whenever reviewing code, commits, branches, or pull requests in
`joshlf/anneal`, or when auditing changes before committing.

Anneal's correctness promise in [`PRINCIPLES.md`](../../PRINCIPLES.md) depends
on a strict boundary documented in
[`docs/trust-model.md`](../../docs/trust-model.md): first-party trusted code
lives in [`trusted/`](../../trusted) (together with root manifests pinned by
hashes in `trusted/`), and all code in `theory/` is untrusted and verified in
repository CI by [`trusted/audit/`](../../trusted/audit) (`anneal-audit`) to be
pure, effect-free, and axiom-free.

Combine this skill with:

- [`comment-guidelines`](../comment-guidelines/SKILL.md) when reviewing or
  writing explanatory and citation comments in `trusted/`; and
- [`reader-oriented-explanation`](../reader-oriented-explanation/SKILL.md) and
  [`williams-style`](../williams-style/SKILL.md) when drafting review findings
  or documentation.

Reviewing changes under this skill does not authorize modifying repository
files, updating cryptographic lock manifests, weakening audit checks, or
approving, merging, or publishing a pull request.

## Run a distinct adversarial review pass

Do not fold trust-boundary review into a general code-review pass that checks
functionality, style, naming, or prose at the same time. In a combined pass,
high-frequency surface comments crowd out subtle cross-cutting boundary risks,
and reviewers default to a cooperative stance ("does this change do what the
author intended?") rather than an adversarial stance ("how could this change—or
an omission in it—subvert or bypass the trust model?").

Execute trust-boundary review as a dedicated pass:

1. **Inspect the complete change inventory:** Check all added, modified,
   renamed, and deleted paths, file modes, symlinks, and hidden dotfiles across
   the diff, not just isolated code hunks. Look both at what changed and at what
   companion updates (such as manifest hashes, pinned citations, or negative
   audit tests) are missing.
2. **Evaluate two distinct goals based on the affected paths:**
   - **Pass 1 (Enforcement-bypass audit outside `trusted/`, `ci/`, and
     `.github/`):** Run on every change that touches or adds files outside
     `trusted/`, `ci/`, and `.github/` to ensure untrusted code cannot
     intentionally or accidentally bypass `anneal-audit` or CI gates.
   - **Pass 2 (TCB and harness audit inside `trusted/`, `ci/`, `.github/`, and
     pinned root manifests):** Run whenever a change touches `trusted/`, `ci/`,
     `.github/`, or any root file pinned by
     [`trusted/root-manifest.sha256`](../../trusted/root-manifest.sha256)
     (`Cargo.toml`, `Cargo.lock`, `flake.nix`, `flake.lock`). If a diff touches
     none of these paths, skip Pass 2.
3. **In single-pass PR review environments:** When operating as a single-turn
   automated pull request reviewer that cannot spawn a separate pass, evaluate
   Pass 1 and (when triggered) Pass 2 first and emit a dedicated
   `### Trust-Boundary Assessment` section before general review comments
   whenever a change raises a boundary question or touches `trusted/`, `ci/`,
   `.github/`, or pinned root manifests.

## Pass 1: Audit changes outside `trusted/`, `ci/`, and `.github/` for bypasses

Code outside `trusted/`, `ci/`, and `.github/` (such as `theory/`, tests,
workspace configurations, or new directories) is untrusted. Although
`anneal-audit` and CI scripts are designed to enforce purity mechanically,
parts of the target architecture in
[`docs/trust-model.md`](../../docs/trust-model.md) are still evolving and any
static checker can have blind spots. Check every change outside the TCB for
intentional or accidental enforcement bypasses:

1. **Unchecked effectful code or build hooks outside `trusted/`:**
   - Reject any new Rust crate, `build.rs` script, procedural macro, Makefile,
     `lakefile.lean`, or shell/Python script outside `trusted/` that could
     execute arbitrary code during `cargo test`, `nix build`, `lake`, or
     developer workflows without being blocked by `anneal-audit`.
   - Reject ambient toolchain or compiler configuration files at the repository
     root or in subdirectories (such as `.cargo/config.toml`, `rust-toolchain`,
     `rust-toolchain.toml`, `.envrc`, or editor/plugin hooks) that could alter
     `rustc` flags, `RUSTC_WRAPPER`, linker behavior, or dependency sources.
2. **Filesystem, module-discovery, and artifact evasion:**
   - Check that no `.lean` files are placed in directories or naming layouts
     outside the trees scanned by `anneal-audit` (`trusted/lean/` and
     `theory/`), and that no symlinks, hardlinks, git submodules, or
     pre-compiled `.olean`, `.ilean`, or `.ir` artifacts are introduced into the
     source tree.
   - Watch for path-normalization tricks, case-collision filenames, or Unicode
     homoglyphs and bidirectional/invisible control characters in module or
     identifier names.
3. **Lean syntax, elaborator, or attribute blind spots in `theory/`:**
   - Verify that `.lean` files in `theory/` use only pure declarations and
     tactics (and that `trusted/lean/` remains tactic-free). Flag any construct
     that attempts to run metaprograms, read files or environment variables, or
     alter elaboration or compiler behavior—even if
     [`TrustedBoundary.lean`](../../trusted/audit/TrustedBoundary.lean)'s
     syntactic preflight (`allowedTrustedSyntaxKinds`,
     `allowedTheoryTacticKinds`, and `inspectNodeKind`) failed to reject that
     specific syntax shape.
   - Confirm that code outside `trusted/lean/` never declares constants in the
     `Trusted` root namespace, never includes `-- anneal-trust-tier:`
     directives, and never introduces `axiom`, `sorry`, `unsafe`, `partial`,
     `noncomputable`, `opaque`, `native_decide`, `decide!`, `bv_decide`,
     `rfl'`, `grind`, tactic `configItem` flags (`+native`, `+kernel`),
     `by_elab`, `#eval`, `set_option`, `initialize`, `@[implemented_by]`,
     `@[extern]`, or `@[csimp]`.
4. **Vacuous or misleading specifications at the `trusted/`–`theory/` seam:**
   - Check that lowering passes (`Abstracts`), weakest-precondition rules, and
     specification helpers in `theory/` do not discharge obligations via
     contradictory preconditions, tautological postconditions, or weakened
     intermediate predicates that make an unverified or trivial claim appear to
     test or prove a stronger property.

## Pass 2: Audit `trusted/`, `ci/`, `.github/`, and pinned root manifests

When a change touches `trusted/`, `ci/`, `.github/`, or any root file pinned by
[`trusted/root-manifest.sha256`](../../trusted/root-manifest.sha256), audit the
affected components against these requirements:

### 1. Semantic definitions and module tiers (`trusted/lean/`)

- **Rust semantic fidelity and fail-closed behavior:** Definitions in
  `trusted/lean/` must faithfully reflect Rust operational semantics and must
  never "fail open" by treating undefined behavior or unsupported constructs as
  no-ops or trivially valid states.
- **Mandatory pinned citations:** Every declaration or rule in `trusted/lean/`
  that claims to model Rust semantics must explain the correspondence in its
  comments and both quote and cite the applicable Rust Reference section
  (`rust-lang/reference`) or compiler source (`rust-lang/rust`) at a pinned
  commit hash.
- **Statement-Origin Separation:** Verify that `Trusted.CrateTheorem` and
  `VerificationResult` theorem statements (`ConstantInfo.type`) reference only
  `Init.*` and `Trusted.*` constants, never `theory/` (`Anneal.*`).
- **Module trust-tier discipline (`-- anneal-trust-tier:`):** Every `Trusted.*`
  module must carry an accurate `-- anneal-trust-tier: vetted` or
  `-- anneal-trust-tier: candidate:<feature>` directive. Ensure that new or
  unreviewed semantics use `candidate:<feature>` rather than `vetted`, and that
  `vetted` modules never import or reference `candidate:<feature>` modules.

### 2. Compiler fact extraction and proof emission (`trusted/rustc-capture/`)

- **1:1 capture without semantic normalization:** `rustc-capture` must translate
  `Runtime(PostCleanup)` MIR and compiler facts directly into `Trusted` AST
  structures. Control-flow restructuring, expression simplification, and
  semantic desugaring must live in `theory/` where their soundness is proven in
  Lean, not in unverified Rust capture code.
- **Fail-closed translation and late-error guards:** Unsupported MIR statements,
  terminators, types, intrinsics, or attributes must produce hard errors rather
  than fallback defaults or skipped obligations, and capture must abort whenever
  `tcx.dcx().has_errors()` indicates compiler diagnostics.
- **Emitted `Mir.lean` and `Proof.lean` integrity:** Generated Lean files must
  remain pure and deterministic, and must never allow crate names, identifiers,
  or annotation strings to inject raw Lean commands or alter the
  `Proof.verify_crate : Trusted.CrateTheorem Mir.crate` theorem statement.
- **Mandatory pinned `rustc` citations:** Code extracting `rustc` internal types
  (`TyCtxt`, `Body`, layouts, regions, ABI facts) must explain the
  correspondence and both quote and cite `rust-lang/rust` at a pinned commit
  hash.

### 3. Boundary auditor and lock manifests (`trusted/audit/`, lock files)

- **No silent weakening of `anneal-audit`:** Scrutinize any modification to
  [`trusted/audit/src/lib.rs`](../../trusted/audit/src/lib.rs) or
  [`TrustedBoundary.lean`](../../trusted/audit/TrustedBoundary.lean). Flag any
  change that:
  - expands `allowedCommandKinds`, `allowedDeclarationKinds`,
    `allowedAttributeNames`, `allowedTrustedSyntaxKinds`,
    `allowedTheoryTacticKinds`, or the foundation axiom allowlist without a
    sound justification;
  - relaxes structural node checks in `inspectNodeKind` or `inspectSyntax`;
  - relaxes Cargo workspace containment (`check_cargo_boundary`), source-tree
    regular-file checks (`scan_lean_tree`), or environment variable stripping;
  - weakens synchronous compilation flags (`-DElab.async=false`,
    `-Ddebug.skipKernelTC=false`), `.olean` loading (`trustLevel := 0`,
    `plugins := #[]`, `loadExts := false`), `checkTierReferences`, or fresh
    kernel replay (`base.toKernelEnv.replay`).
- **Negative regression tests:** Any change to `anneal-audit` admission rules,
  syntax filters, or tier checks must include negative tests in
  [`boundary_audit.rs`](../../trusted/audit/tests/boundary_audit.rs) verifying
  that prohibited inputs are rejected with policy exit code `1`.
- **Cryptographic lock synchronization:** When `Cargo.toml`, `Cargo.lock`,
  `flake.nix`, `flake.lock`, the Lean binary, or `Init.*` prelude files change,
  verify that
  [`trusted/root-manifest.sha256`](../../trusted/root-manifest.sha256) and
  [`foundation-lock.json`](../../trusted/lean/foundation-lock.json)
  (`trusted/lean/foundation-lock.json`) are updated in lockstep and that the
  underlying dependency or toolchain change is audited.

### 4. CLI orchestrator and dependencies (`trusted/cargo-anneal/`, `Cargo.*`)

- **Orchestration integrity:** Verify that `cargo-anneal` does not allow ambient
  environment variables, target-crate configuration files, or CLI flags to skip
  Lean kernel checking, substitute an unverified toolchain archive, or suppress
  verification errors.
- **Dependency discipline:** Check any added or updated crate in `Cargo.toml`
  and `Cargo.lock` against [`AGENTS.md`](../../AGENTS.md): prefer standard,
  well-audited crates over hand-rolled plumbing, keep transitive dependency
  trees conservative, and ensure all dependencies come from pinned `crates.io`
  checksums.

### 5. CI workflows and scripts (`ci/`, `.github/workflows/`)

- **Mandatory CI gates:** Verify that
  [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml) verifies
  `trusted/root-manifest.sha256` (`sha256sum --check --strict`), checks for
  forbidden `.cargo` and `rust-toolchain*` paths, runs
  `cargo run --locked -p anneal-audit`, and requires every job in the
  fail-closed `all-jobs-succeed` gate (enforced by
  [`ci/check_job_dependencies.sh`](../../ci/check_job_dependencies.sh)).
- **Privilege, action pinning, and cache isolation:** Ensure workflows keep
  `permissions: contents: read`, pin third-party GitHub Actions to full
  40-character commit SHAs, strip `ACTIONS_CACHE_URL`, `ACTIONS_RESULTS_URL`,
  and `ACTIONS_RUNTIME_TOKEN` in jobs running scripts outside `trusted/`, and
  never allow cached artifacts to bypass `anneal-audit` or shadow source
  changes.

## Report findings with clear evidence and scope

Treat any confirmed or plausible violation of Pass 1 (enforcement bypass) or
Pass 2 (TCB unsoundness or audit weakening) as a blocking review finding.

When reporting a finding:

1. **Cite the exact location and invariant:** Identify the file, line range or
   declaration, and the specific guarantee in
   [`PRINCIPLES.md`](../../PRINCIPLES.md),
   [`docs/trust-model.md`](../../docs/trust-model.md), or `anneal-audit` that is
   undermined or bypassed.
2. **Explain the concrete failure or bypass mechanism:** State how an untrusted
   input, `theory/` module, build step, or edge case could exploit or trigger
   the flaw.
3. **Distinguish confirmed defects from open verification questions:** When a
   finding depends on an unverified assumption (for example, whether a Lean
   parser production can be reached or how an external tool handles a path),
   state the hypothesis and what check or test would resolve it rather than
   asserting an unverified failure as fact.
