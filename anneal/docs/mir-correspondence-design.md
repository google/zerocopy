<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# MIR Correspondence Design

> **Note:** Anneal is under active development. The concrete vendored
> `lean-miri` snapshot, `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`,
> `Trusted/Correspondence.lean`, `correspondence/`, `theory/Anneal/MirWp.lean`,
> `anneal-audit` Pass 2 enforcement, and the packaged correspondence provenance
> record (planned alongside end-to-end packaging and `cargo anneal verify`
> integration) described below are target architecture landing incrementally
> across the MIR correspondence stack.

[`docs/mir-correspondence-strategy.md`](mir-correspondence-strategy.md) defines
how Anneal validates its Rust Mid-level Intermediate Representation (MIR)
operational semantics ($M_{\text{anneal}}$): we prove in the Lean 4 kernel that
$M_{\text{anneal}}$ refines an independently developed reference model
($M_{\text{ref}}$) and matches its fault classification unconditionally across
every program and input query.

This document specifies the architecture that implements that strategy:

1. **Reference model ($M_{\text{ref}}$):** Anneal vendors `lean-miri` under
   `vendor/lean-miri/` as part of its pinned, human-audited correspondence TCB
   and enables a surgical opt-in flag (`deinitMovedPlace : Bool`) so that
   moving a non-zero-sized MIR place deinitializes the source location at
   runtime—a deliberate conservative choice stricter than current Miri,
   codegen, and MiniRust (which removed destructive loads in
   `minirust@766d8d619a` and deinitializes only in-place call arguments),
   permitted by `rustc`'s post-cleanup MIR contract (`Move` *may* overwrite the
   moved-from place with `uninit`; Section 2.4).
2. **Anneal MIR syntax and semantics ($M_{\text{anneal}}$):**
   `Trusted.MirAst` represents MIR programs with structural types (`MirTy`)
   carried directly by value, and `Trusted.MirSemantics` defines a small-step
   operational semantics that shares its boundary input and output value types
   (`Query`, `Out`, `TerminalOut`) directly with the reference adapter.
3. **Canonical type codec and correspondence (`Trusted.Correspondence`):**
   A total encoder (`encodeProg`) interns structural `MirTy` values into a
   deduplicated type table (`RefProg.types`) indexed by `TyId := Nat`, and a
   total decoder (`decodeProg`) inverts `encodeProg` unconditionally (`∀ p,
   decodeProg (encodeProg p) = some p`). Unconditionally across every program
   and input query `(p, q)` (without gating on `WellFormed p q`), the combined
   locked contract requires a faithful choice-coupled execution relation with
   (a) unconditional forward totality ($M_{\text{ref}} \to M_{\text{anneal}}$)
   across all valid executions (faulting and non-faulting), (b) unconditional
   reverse totality on faulting executions
   ($M_{\text{anneal}} \to M_{\text{ref}}$) preserving fault classification
   (`.undefined` vs. `.ub` and `.unsupported` vs. `.blocked`), and (c) optional
   reverse totality on non-faulting executions. In the deterministic,
   productive Phase 1 setting, that unconditional contract reduces cleanly to
   `CorrespondenceClaim` (`correspondence_claim_holds`, exported from
   `anneal_corresponds_to_miri`, proved via the one-to-one simulation invariant
   `SimulationInv`) plus unconditional bidirectional fault-reachability
   equivalence `FaultEquivalenceClaim` (`fault_equivalence_claim_holds`,
   exported from `reachesResult_fault_iff_refReachesOutcome`), yielding exact
   two-way outcome, divergence, and fault agreement across every `(p, q)`.

---

## 1. Repository Layout, Two-Pass Audit, and Trust Boundary

Anneal separates the core semantics and theory (`trusted/lean/` and `theory/`,
audited in Pass 1 and packaged in the downstream verification archive once MIR
scaffolding lands) from the repository-only correspondence proof against
`vendor/lean-miri/` (`trusted/correspondence/` and `correspondence/`):

```text
trusted/lean/                   Core TCB (Pass 1; shipped in omnibus-archive)
  Trusted.lean                  Umbrella module
                                (-- anneal-trust-tier: vetted)
  Trusted/
    MirAst.lean                 Anneal MIR syntax
                                (-- anneal-trust-tier: candidate:mir_ast)
    MirSemantics.lean           Anneal small-step semantics
                                (-- anneal-trust-tier: candidate:mir_semantics)

theory/                         Core untrusted theory (Pass 1; shipped in
                                omnibus-archive once MIR scaffolding lands)
  Anneal.lean                   Umbrella module
  Anneal/
    MirWp.lean                  Fuel-bounded weakest precondition (wpProg,
                                wpFaultProg) and M_anneal non-vacuity canaries

vendor/lean-miri/               Vendored lean-miri reference model
                                (correspondence TCB; Pass 2)
  UPSTREAM_PIN.json             Pinned commit, 608 .lean SHA-256s (Miri.lean +
                                607 under Miri/), 8 auxiliary-file SHA-256s, 10
                                patched-file SHA-256s, and 160 ExecutionMachine
                                .olean SHA-256s
  Miri.lean                     Top-level vendored root module
  Miri/
    MIR/...                     Reference MIR syntax (TyId-indexed)
    Interpreter/
      MachineHooks.lean         MachineState + pendingMoveDeinit flag
      LocalAccess.lean          Pure local operand helpers + deinitMovedPlace
      OperandMachine.lean       Operand evaluation + immediate move deinit
      Place.lean                copyRuntimePlaceNoValidate + indirect move
                                deinit
      PlaceMachine.lean         readImmediate + takePendingMoveDeinit wiring
                                and CopyNonOverlapping move snapshots
      Cast.lean                 Cast.cast + atomic pendingMoveDeinit deinit
      ExecutionCast.lean        CastHooks wiring for takePendingMoveDeinit
      Call.lean                 Call argument move deinitialization
      ExecutionCalls.lean       CallHooks wiring for deinitMovedPlace
      ExecutionMachine.lean     Single-step interpreter facade (`step`,
                                `stepHooks`), `Config` flag, and
                                `CopyNonOverlapping` move sequencing

trusted/correspondence/Trusted/ Correspondence TCB specification (Pass 2)
  Correspondence.lean           Hub + locked *Claim constants (37 claims:
  Correspondence/               Codec, State, Config, Eval, Simulation,
                                CanaryFixtures;
                                -- anneal-trust-tier: candidate:mir_semantics)

correspondence/Anneal/          Untrusted correspondence proof (Pass 2)
  MirCorrespondence/            Modular proofs (Codec, SimHelpers, ScalarEquiv,
                                EnumEquiv, MemRoundTrip, RvalueStep,
                                StmtTermStep, InitAndSim, Canaries)
  MirCorrespondenceProof.lean   Public re-exports of all 37 locked witnesses

trusted/audit/                  anneal-audit CLI, auditor library, and inspector
  TrustedBoundary.lean          Syntactic preflight, namespace and
                                constant-cone checks, statement-origin
                                verification, and kernel replay
  src/                          Auditor implementation (`lib.rs`, plus
                                `miri_pin.rs` and `repo_audit.rs` once split):
                                Pass 1 (51-module core lock) and Pass 2
                                (UPSTREAM_PIN.json + correspondence closure)
```

### 1.1 Separating Pass 1 (Core Omnibus) from Pass 2 (Correspondence)

At this design document's commit, Anneal's Nix build (`omnibus-archive` in
`flake.nix`) copies `trusted/lean/` into `share/anneal/trusted/lean` inside
`anneal-exocrate.tar.zst`; once the MIR scaffolding lands, `flake.nix` also
packages `theory/` into `share/anneal/theory` (requiring
`share/anneal/theory/Anneal/MirWp.lean`) so per-crate proofs can invoke
`Anneal.MirWp`, while continuing to exclude `vendor/lean-miri/`,
`trusted/correspondence/`, and `correspondence/` from packaged user archives.
To preserve bounded human-review auditability without shipping
`vendor/lean-miri/` or `correspondence/` at runtime
([`docs/architecture.md`](architecture.md),
[`docs/trust-model.md`](trust-model.md)), once end-to-end packaging lands,
packaged user archives and `cargo-anneal` bundles will instead carry a compact,
CI-checked, digest-bound **correspondence provenance record** (pinned Anneal
revision, `trusted/lean/` source and `.olean` digests, `vendor/lean-miri/`
upstream commit, `UPSTREAM_PIN.json` SHA-256, `patched_files`
allowlist/digests, `Trusted/Correspondence.lean` digest, and Pass 2 attestation
metadata). Archive construction and `cargo anneal verify` will hash the actual
packaged `trusted/lean/` artifacts and fail closed unless those computed digests
exactly match the attested provenance record (as well as failing closed if
missing or malformed), and `cargo anneal verify` will surface the verified
record in every verification result's TCB audit log. Per
[`docs/mir-correspondence-strategy.md`](mir-correspondence-strategy.md), the
Phase 1 correspondence domain covers concrete, monomorphic captured MIR carrying
concrete instance/layout metadata (with polymorphic generic library verification
phased separately), and the `Trusted/Correspondence.lean` wrapper maps any
non-UB `lean-miri` stop outcome (`failed`, `pending`, `blocked`) fail-closed to
`RefOutcome.blocked` (corresponding to `FaultKind.unsupported`).
Meanwhile, `anneal-audit` Pass 1 (`Checker::run`) verifies that every module
under `trusted/lean/` and `theory/` starts with `prelude` and imports only the
51 locked `Init.*` modules in `trusted/lean/foundation-lock.json` and
role-permitted intra-repository `Trusted.*` / `Anneal.*` modules. By contrast,
`vendor/lean-miri/` (608 `.lean` files total: `Miri.lean` plus 607 files under
`Miri/`; 160 `Miri.*` modules in the transitive import closure of
`Miri.Interpreter.ExecutionMachine`) uses standard Lean 4 module headers
without `prelude`, transitively importing `Init.*`, `Std.*`, and `Lean.*`
modules from the Lean 4.34.1 toolchain sysroot (whose `.olean`,
`.olean.server`, and `.olean.private` artifacts are authenticated in memory
once the vendored snapshot lands—via
`AdmittedToolchain::ensure_sysroot_foundation` in `src/lib.rs` against
`LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256` in `trusted/audit/`, later
refactored to `Checker::ensure_sysroot_foundation` calling
`verify_sysroot_foundation` after the `src/{miri_pin,repo_audit}.rs` split).

Although `Trusted/MirSemantics.lean` resides in `trusted/lean/` so that
`Trusted.CrateTheorem` and `Anneal.MirWp` can state per-crate obligations in
Pass 1 without importing `vendor/lean-miri/`, only its outer theorem-stating
boundary—shared input/outcome types (`Query`, `Val`, `Out`, `TerminalOut`, and
`FaultKind`), execution predicates (`Step`, `Reaches`, `ReachesResult`,
`WellFormed`, `Behavior`, `Diverges`, and `SatisfiesPost`), verification
judgments (`BodyStaticAdmitted`, `ValidEntryArgs`, `BodyVerified`, `Specs`,
`Crate`, `ProgramVerified`, `CrateTheorem`, and `UnitTheorem`; Section 4.5),
and the helpers they reference—is a human-audited specification surface (with
`WpSoundnessClaim` and `WpFaultSoundnessClaim` additionally serving as the
Pass 1 weakest-precondition proof-interface checks). Its internal operational
execution rules (`initState` and `evalStep` of $M_{\text{anneal}}$) are
kernel-certified against $M_{\text{ref}}$ (`vendor/lean-miri/` together with
its `Trusted/Correspondence.lean` wrapper) in Pass 2 by `CorrespondenceClaim`
and `FaultEquivalenceClaim` (`correspondence/`), keeping evolving
$M_{\text{anneal}}$ execution rules out of the human-audited semantic TCB in
accordance with [`docs/architecture.md`](architecture.md) and
[`docs/mir-correspondence-strategy.md`](mir-correspondence-strategy.md). While
`evalStep` cross-checks against `vendor/lean-miri/`'s interpreter primitives,
entry validation in `initRefState` (matching `initState`) and the Day-1
`ExecutionMachine.Config` hooks in `Trusted/Correspondence/` (Section 2.2) are
authored in the correspondence wrapper and human-audited alongside
`vendor/lean-miri/` as part of the correspondence TCB (Section 1.3), while Miri
natively enforces uninitialized reads and shallow validity via
`ExecutionMachine.step` and `ValidityVisitor.validatePlace`.

Placing `Trusted.Correspondence*`, `Anneal.MirCorrespondence.*`, and
`Anneal.MirCorrespondenceProof` in `trusted/correspondence/` and
`correspondence/` preserves both invariants:

1. **Pass 1 (`Checker::run` on `trusted/lean/` and `theory/`):** Runs in a
   fresh, isolated staging directory, auditing `Trusted.MirAst`,
   `Trusted.MirSemantics`, and `Anneal.MirWp` against the unmodified 51-module
   `trusted/lean/foundation-lock.json` and unmodified
   `allowedTrustedSyntaxKinds` / `allowedTheorySyntaxKinds` allowlists in
   `TrustedBoundary.lean`, and source-preflighting, compiling from source, and
   kernel-replaying all `trusted/lean/` and `theory/` modules onto
   `foundation-lock.json`. Once MIR scaffolding lands, whenever
   `Anneal.PureLift`, `Trusted.MirAst`, `Trusted.MirSemantics`, or
   `Anneal.MirWp` is present (or `require_mir_wp` is enabled),
   `TrustedBoundary.lean` (`verifyMirWpCoreTheorems`) requires
   `Trusted.MirAst` and `Trusted.MirSemantics` in `trusted/` and `Anneal.MirWp`
   in `theory/`, and enforces Statement-Origin Separation: every Pass 1
   canary's exact `*Claim` theorem statement and every concrete program
   (`prog*`), query, and expected-outcome fixture definition it references live
   on the human-audited `Trusted.*` surface (`Trusted.MirSemantics`), while
   only the proofs (`wellFormed_and_spec_of_wp`,
   `reaches_fault_and_exclusive_of_wpFault`, and all 15 Day-1 scalar/bool/unit
   or 25 full canary theorems once fieldless enums, `!`, crate/unit scope,
   byte-level memory, `char`, `BinOp.cmp`, `BinOp.*WithOverflow`, and
   `CastKind.intToInt` land, including
   `CanaryCrateAndBodyVerifiedAnnealClaim` and
   `CanaryMemoryLifecycleAnnealClaim`) live in
   untrusted `Anneal.MirWp` and are verified against those exact trusted
   `*Claim` propositions. Packaged user archives (`omnibus-archive`) ship
   `trusted/lean/` and, once MIR scaffolding and end-to-end packaging land,
   will also ship `theory/` (with `Anneal/MirWp.lean`) and carry the compact
   correspondence provenance record surfaced in `cargo anneal verify`'s TCB
   audit log, while never packaging `vendor/lean-miri/`,
   `trusted/correspondence/`, or `correspondence/`, keeping downstream
   per-crate verification independent of `vendor/lean-miri/`. (In intermediate
   commits after `vendor/lean-miri/` lands and before
   `--require-correspondence` splits Pass 2 out, `Checker::run` verifies the
   vendored pin and 160-module closure unconditionally.)
2. **Pass 2 (`Checker::run_correspondence` on `vendor/lean-miri/`,
   `trusted/correspondence/`, and `correspondence/`):** Runs in blocking
   repository CI (`--require-correspondence`) as an extension of Pass 1's
   isolated staging run (never reusing unverified ambient `.olean` artifacts)
   to audit the correspondence claim against `vendor/lean-miri/`:
   - **Fail-closed `UPSTREAM_PIN.json` and sysroot authentication from
     `trusted/`:** Before using `vendor/lean-miri/UPSTREAM_PIN.json`,
     `trusted/audit/` (`verify_upstream_pin` in `src/lib.rs`, later
     `src/miri_pin.rs`) verifies that the manifest's own SHA-256 digest matches
     the TCB constant `LOCKED_UPSTREAM_PIN_SHA256`, that its `commit` equals
     `LOCKED_MIRI_COMMIT`, that its `build_lean_toolchain` matches Anneal's
     locked `leanprover/lean4:v4.34.1`, and that its patched-file map matches
     the closed TCB allowlist `LOCKED_PATCHED_MIRI_FILES` in the same module,
     so an untrusted change outside `trusted/` cannot alter `UPSTREAM_PIN.json`
     to admit modified `vendor/lean-miri/` sources or `.olean`s. It walks
     `vendor/lean-miri/` without following symlinks and rejects any unpinned
     extra file (`.lean` or auxiliary), missing pinned file, symlink,
     non-regular file, or pre-existing `.olean`/`.ilean`/`.ir` artifact,
     verifying that all 608 `.lean` files (`Miri.lean` plus 607 files under
     `Miri/`) and 8 auxiliary files match their pinned SHA-256 digests: 598
     `.lean` files match unmodified upstream `proofs-rs/lean-miri` at
     `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, and the 10 patched files match
     their pinned `patched_sha256` digests in `UPSTREAM_PIN.json`. Any future
     upstream pin update must expose and receive human semantic review of the
     resolved old-to-new reference-model diff (in addition to compile-time
     metaprograms and local patches), per [`docs/trust-model.md`](trust-model.md).
     Before any vendor module is compiled or replayed, `anneal-audit` also
     authenticates the pinned Lean toolchain's `Init`/`Std`/`Lean` `.olean`
     companions against `LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`.
   - **160-module `ExecutionMachine` slice build, `.olean` cache, and
     standalone vendor kernel replay:** Every closure source file is staged and
     re-hashed against its pinned SHA-256 digest before use. On a cache
     miss—or whenever `--miri-cache-dir` / `ANNEAL_MIRI_CACHE_DIR` is omitted
     to force a cold from-source rebuild—`anneal-audit` compiles all 160
     `Miri.*` modules in topological order from verified pinned source using
     the locked `lean` binary (`-j1 -M2048 -t0 -DElab.async=false
     -Ddebug.skipKernelTC=false`), checks each compiled `.olean` (and any
     pinned `.olean.server`/`.olean.private` sidecar, rejecting unexpected
     ones) against `UPSTREAM_PIN.json`'s `execution_machine_closure` SHA-256
     digests before writing it back to the cache (write-after-verify via
     `prepare_nosymlink_cache_path` / `write_cache_file`), and rejects any
     cache directory located inside (or resolving via symlinks inside) the
     repository checkout. In CI, the cache lives in
     `${{ runner.temp }}/anneal-miri-olean-cache` keyed on OS, architecture,
     `trusted/lean/lean-toolchain`, and `vendor/lean-miri/UPSTREAM_PIN.json`
     (so any pin or toolchain change misses and compiles cold), blocking
     merge-queue (`merge_group`), manual (`workflow_dispatch`), and
     non-`main`/fork `push` runs skip the cache action and omit
     `--miri-cache-dir`, and canonical `main`-branch (`push`) runs use
     `lookup-only: true` plus `rm -rf` before invoking `anneal-audit` so every
     landed revision and manual dispatch performs a cold from-source build as
     well as standalone kernel replay while canonical `main` still seeds a
     missing default-branch cache entry for pull requests. Per
     [`docs/trust-model.md`](trust-model.md), cold compilation and any
     metaprogram-executing Pass 2 step over unmerged candidate
     `vendor/lean-miri/` code must be confined to an OS-level isolated sandbox
     without credentials or writable access to the worktree, home directory, or
     auditor state (the initial `anneal-audit` staging implementation isolates
     private temporary build directories on ephemeral CI runners, with explicit
     OS-level process sandboxing for candidate vendor elaboration required by
     the governing trust model before admitting untrusted pin-update builds).
     Forging a pinned `.olean` digest would require
     modifying `UPSTREAM_PIN.json` (which changes `UPSTREAM_PIN.json`'s own
     SHA-256 and breaks `LOCKED_UPSTREAM_PIN_SHA256` inside `trusted/audit/`).
     Moreover, a digest-matching cache hit skips only re-elaborating the pinned
     `.lean` source—it does **not** skip kernel typechecking: on **every** run
     (cold compile and warm cache hit alike), `TrustedBoundary.lean`
     (`auditCorrespondence`) loads the verified `.olean` closure with
     `trustLevel := 0`, `plugins := #[]`, and `loadExts := false`, constructs a
     clean `baseEnv` containing strictly the authenticated `.foundation` and
     `.sysrootFoundation` modules from the pinned sysroot, and **replays all
     non-`isPartial` safe `.vendorMiri` constants across all 160 vendored
     closure modules (38,603 in the unpatched closure; 38,728 once the 10-file
     `deinitMovedPlace` patch lands) from scratch in the standalone Lean kernel
     (`baseEnv.toKernelEnv.replay`)**—omitting the 75 compiler-generated
     `isPartial` (`*._unsafe_rec`) codegen helpers so replay fails with
     `unknown constant` if any safe constant references a skipped `unsafe` or
     `partial` constant—while rejecting `isUnsafe`, `axiom`, `sorryAx`,
     compiler-reflection primitives (`Lean.ofReduceBool`, `Lean.ofReduceNat`,
     `Lean.trustCompiler`, `Lean.reduceBool`, `Lean.reduceNat`), and any
     `.vendorMiri` `isPartial` or `.opaqueInfo` (`partial def`) constant
     reachable in the 36-root `Miri.Interpreter.ExecutionMachine` cone or the
     full dependency cone of the locked correspondence claims (tested end-to-end
     by `rejects_vendor_miri_skip_kernel_tc_during_replay`). Neither a scoped
     `set_option debug.skipKernelTC true` inside a vendored `.lean` file nor a
     poisoned `.olean` cache can therefore admit an un-kernel-checked safe
     constant. **Syntactic-preflight boundary:** unlike `trusted/lean/`,
     `theory/`, `trusted/correspondence/`, and `correspondence/`, vendored
     `vendor/lean-miri/` sources are **not** passed through untrusted-`.theory`
     syntactic preflight, because upstream `Miri.Input.*` and proof helpers
     retain compile-time metaprograms (`run_cmd`), custom tactic `elab`s, 1
     `initialize` declaration (`Miri/Input/DecoderValues.lean:918`), and 24
     `partial def`s audited under the SHA-256 `UPSTREAM_PIN.json` pin and
     `LOCKED_PATCHED_MIRI_FILES` allowlist in `trusted/audit/`.
   - **Syntactic preflight and compilation of `Trusted.Correspondence*`,
     `Anneal.MirCorrespondence.*`, and `Anneal.MirCorrespondenceProof`:**
     Enforces the unmodified `allowedTrustedSyntaxKinds` and
     `allowedTheorySyntaxKinds` allowlists, `prelude`, and explicit
     root-identifier checks on every correspondence module (compiled fresh
     from source at `-M4096`), extending Pass 1's fresh isolated preflight,
     from-source compilation, and kernel replay of `trusted/lean/` and
     `theory/`.
   - **Root-namespace provenance for vendored and sysroot modules:**
     `verifyAndCollectCorrLocals` rejects every constant that a `.vendorMiri`
     or `.sysrootFoundation` module declares in the `Trusted` or `Anneal` root
     namespace (including `private` constants) and rejects any `axiom`,
     `unsafe` declaration, quotient primitive, missing body, direct `sorryAx`
     reference, or compiler-reflection primitive declared by a `.vendorMiri`
     module, so neither the vendored tree nor the toolchain sysroot can inject
     declarations or axioms into the audited namespaces.
   - **Reference-evaluator independence (`verifyRefEvaluatorIndependence`):**
     Enforces fail-closed transitive module-level import isolation on every
     isolated `Trusted.Correspondence.*` evaluator submodule (every
     `Trusted.Correspondence.*` module outside the umbrella
     `Trusted.Correspondence` and `{Simulation,CanaryFixtures}`)—rejecting any
     direct or transitive import of a disallowed `Trusted` module (including
     `Trusted`, `Trusted.MirSemantics*`, `Trusted.Correspondence`,
     `Trusted.Correspondence.Simulation`,
     `Trusted.Correspondence.CanaryFixtures`, or sibling `Trusted.*`
     modules)—and requires `evalRefStep`, `initRefState`, and `RefAllowedStep`
     to reside inside those isolated submodules in a modular layout. It then
     computes the transitive constant cone of
     `[Trusted.Correspondence.evalRefStep,
     Trusted.Correspondence.initRefState]` via `closureCorr`, requiring all 39
     live `ExecutionMachine` `Miri.Interpreter.*` / `Miri.Memory.ScalarInt.*`
     primitives listed in Section 1.3 to be reachable directly from the live
     evaluator (never masked by `RefAllowedStep`), separately requires
     `Miri.Interpreter.ExecutionMachine.AllowedStep` in the cone of
     `Trusted.Correspondence.RefAllowedStep`, and restricts every
     `.repo (.trusted _)` dependency across both cones to `Trusted.MirAst*`,
     `Trusted.MirModel`, or `Trusted.Correspondence*` (so
     `Trusted.MirSemantics`, `Trusted.MirSemantics.*`, and any other sibling
     `Trusted.*` module are rejected fail-closed; human review of
     `trusted/correspondence/` and `Trusted.MirModel` remains the semantic
     boundary).
   - **Constant-cone purity, statement-origin verification, and kernel replay:**
     `TrustedBoundary.lean` (`auditCorrespondence`, run under `-M8192`) splits
     Pass 2 inspection across `collectCorrEnv`, `replayCorrAndVendor`, and
     `verifyCorrConesAndClaims`. First, `collectCorrEnv` loads the full Pass 2
     environment in a dedicated scope (so `env` is released before importing
     `baseEnv` for replay), classifies all 5 module roles (`.foundation`,
     `.sysrootFoundation`, `.vendorMiri`, `.trusted tier`, and `.theory`), runs
     `verifyAndCollectCorrLocals` and `checkDeclarationEdges`, and collects the
     `.repo` and non-`isPartial` `.vendorMiri` inventories. Next,
     `replayCorrAndVendor` resets the search path strictly to the authenticated
     sysroot, replays all non-`isPartial` `.vendorMiri` constants (38,603 in
     the unpatched closure; 38,728 once the 10-file `deinitMovedPlace` patch
     lands) onto `baseEnv.toKernelEnv`, and—within the same isolated Pass 2
     staging run—replays every freshly compiled `.repo` declaration
     (`trusted/lean/`, `theory/`, `Trusted.Correspondence*`,
     `Anneal.MirCorrespondence.*`, and `Anneal.MirCorrespondenceProof`)
     directly onto that replayed vendor kernel environment, matching the
     end-to-end Pass 1 + Pass 2 isolated staging and kernel-replay architecture
     in [`docs/architecture.md`](architecture.md). Finally,
     `verifyCorrConesAndClaims` restores the Pass 2 search path and traverses
     the constant-level dependency graph (`declarationEdges`) across both the
     36-root `Miri.Interpreter.ExecutionMachine` cone and the full
     correspondence dependency cone, verifying that no reachable constant is
     `unsafe` or `isPartial`, that no reachable `.vendorMiri` constant is
     `.opaqueInfo` (guaranteeing that none of the 24 `partial def` JSON parser
     helpers in `Miri.Input.*` inside the 160-module closure—out of 27 across
     all of `Miri/Input/`—is reachable), and that the only reachable axioms
     belong to `{propext, Classical.choice, Quot.sound}`. Within
     `verifyCorrConesAndClaims`, `verifyCorrespondenceClaims` enforces
     Statement-Origin Separation by locking all 37 `(claim, proof)` pairs in
     `Anneal.MirCorrespondenceProof` against the exact `Prop` constants defined
     in `Trusted.Correspondence` (whose referenced program, query, and
     expected-outcome fixture definitions likewise live on `Trusted.*`, with
     only the proofs in untrusted `correspondence/`): `CorrespondenceClaim`
     (`correspondence_claim_holds`, re-exporting `anneal_corresponds_to_miri`),
     `FaultEquivalenceClaim` (`fault_equivalence_claim_holds`, re-exporting
     `reachesResult_fault_iff_refReachesOutcome`),
     `CorrespondenceAtChoicesClaim` (`correspondence_at_choices_claim_holds`),
     `FaultEquivalenceAtChoicesClaim`
     (`fault_equivalence_at_choices_claim_holds`),
     `MiriMoveDeinitWiringClaim` (`miri_move_deinit_wiring_claim_holds`), the 6
     codec claims (`DecodeProgEncodeProgClaim` through
     `EncodeStmtAssignIffClaim`), the 11 uniqueness and simulation claims
     (`StateUniqueOfSimulationInvClaim` through `DivergesIffRefDivergesClaim`),
     and the 11 `D6`–`D16` canary claims (`CanaryD6UseAfterMoveUbClaim` through
     `CanaryD16WithOverflowOkClaim`), plus non-empty required
     constant cones on every claim.
   - **Pass 2 negative audit tests:** `trusted/audit/tests/boundary_audit.rs`
     (and unit tests in `trusted/audit/src/lib.rs`) must exercise fail-closed
     rejection (policy exit code `1`) for: `UPSTREAM_PIN.json` tampering,
     missing, unlisted, or symlinked files under `vendor/lean-miri/`,
     unauthorized `patched_files`, and corrupted closure digests
     (`verifies_upstream_pin_and_rejects_tampering`); `.vendorMiri` constants
     in reserved `Trusted`/`Anneal` namespaces (including `private`) or
     declaring axioms/unsafe constants
     (`rejects_vendor_constants_in_reserved_namespaces`); digest-gated Miri
     `.olean` cache verification, in-checkout cache paths, and symlinked cache
     entries (`verifies_miri_cache_and_rejects_unverified_oleans`,
     `rejects_miri_cache_dir_inside_checkout`, and `src/lib.rs` unit tests
     `rejects_symlinks_in_miri_cache_dir` and
     `validates_correspondence_replay_fields_fail_closed`); standalone kernel
     replay rejection of scoped `set_option debug.skipKernelTC true` in a
     vendored module (`rejects_vendor_miri_skip_kernel_tc_during_replay`);
     correspondence-audit violations and sysroot foundation manifest digest
     mismatches
     (`rejects_correspondence_audit_violations_and_sysroot_mismatch`);
     compiled `Trusted` header imports of `theory/` and
     `Trusted.Correspondence` importing `theory/` in both Pass 2 preflight and
     compiled correspondence audit
     (`rejects_compiled_trusted_header_import_of_theory`,
     `rejects_trusted_correspondence_import_of_theory_in_pass2_preflight`, and
     `rejects_trusted_correspondence_import_of_theory_in_correspondence_audit`);
     and missing or weakened locked WP/correspondence claims, canaries, and
     `verifyRefEvaluatorIndependence` regressions
     (`enforces_mir_wp_non_backsliding`,
     `enforces_mir_wp_param_claim_proof_rules`,
     `enforces_mir_wp_canary_claim_proof_rules`, and
     `enforces_correspondence_non_backsliding`).

Landing the new Pass 2 Lean directories (`trusted/correspondence/`,
`vendor/lean-miri/`, and `correspondence/`)—and later treating Pass 2
correspondence certification as a substitute for human semantic audit of
`initState` and `evalStep` inside `trusted/lean/`—also requires lockstep
updates to [`AGENTS.md`](../AGENTS.md),
[`.gemini/styleguide.md`](../.gemini/styleguide.md),
[`docs/trust-model.md`](trust-model.md), and
[`skills/trust-review/SKILL.md`](../skills/trust-review/SKILL.md) so the
repository code-review rules, trust model, and human review checklist cover
Pass 2's directory roles, `UPSTREAM_PIN.json` and sysroot manifest pinning,
`trusted/correspondence/` TCB admission, and the exact boundary between
human-audited definitions and Pass 2-certified step rules.

### 1.2 Compliance with `TrustedBoundary.lean` and `TrustTier` Discipline

Every `Trusted.*` and `Anneal.*` module satisfies `TrustedBoundary.lean` with
zero changes to `trusted/lean/foundation-lock.json` or the syntax/tactic
allowlists:

- **Trust-tier headers (`-- anneal-trust-tier:`):** `Trusted/MirAst.lean`
  carries `-- anneal-trust-tier: candidate:mir_ast`; `Trusted/MirSemantics.lean`
  and `Trusted/Correspondence.lean` carry `-- anneal-trust-tier:
  candidate:mir_semantics`; and `Trusted.lean` carries `-- anneal-trust-tier:
  vetted`. Per [`AGENTS.md`](../AGENTS.md), `vetted` modules—including the
  `Trusted.lean` umbrella—must never import or reference `candidate:*` modules
  or constants: `theory/` and downstream `candidate:*` modules import
  `candidate:*` submodules (`Trusted.MirAst`, `Trusted.MirSemantics`) directly,
  and any `Trusted.lean` umbrella import requires promoting those modules from
  `candidate:*` to `vetted` first. `anneal-audit` discovers candidate modules
  by walking `trusted/lean/` directly and mechanically enforces tier isolation
  at the **declaration-edge level** (`checkDeclarationEdges` with
  `RepoOrigin.edgeViolation?` and `CorrOrigin.edgeViolation?` forbids any
  `vetted` *declaration* from referencing a `candidate:*` declaration); because
  module-level import isolation between `vetted` and `candidate:*` modules is
  currently a known temporary enforcement gap
  (`enforces_module_level_trust_tiers_and_namespace_hygiene` in
  `boundary_audit.rs` still allows a declaration-free `Trusted.lean` umbrella
  import), Pass 2 human review enforces module-level import isolation manually
  until `anneal-audit` and that test are hardened.
- **Tactic-free, `deriving`-free `Trusted.*` definitions:**
  `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, and
  `Trusted/Correspondence.lean` start with `prelude`, import locked modules
  from `foundation-lock.json` (`Init.NotationExtra`,
  `Init.Data.BitVec.BasicAux`, `Init.Data.Int.Basic`,
  `Init.Data.Nat.Div.Basic`, `Init.Data.Nat.Bitwise.Basic`, and
  `Init.Control.Except`), omit `deriving` clauses in favor of explicit
  structural `beq` functions, and mark recursive definitions `noncomputable def`
  so Lean 4.34.1 elaborates the identical pure kernel `.defnInfo` without
  emitting partial `._unsafe_rec` compiler helpers. Beyond locked modules and
  the `Trusted.*` modules they build on, only `Trusted/Correspondence.lean`
  imports anything else: `Miri.Interpreter.ExecutionMachine` and its
  sub-modules (`LocalAccess`, `Place`, `Rvalue`, `Step`, `ControlFlow`) from
  `vendor/lean-miri/`, which places the vendored tree inside the correspondence
  TCB (Section 1.3).
- **Allowlisted tactics in `theory/` and `correspondence/`:**
  `Anneal/MirWp.lean`, `Anneal/MirWp/*.lean`, `Anneal/MirCorrespondence/*.lean`,
  and `Anneal/MirCorrespondenceProof.lean` use only the tactics that
  `allowedTheorySyntaxKinds` admits (such as `let ⟨a, b⟩ := h`, `cases`,
  `induction`, `dsimp`, `simp`, `rw`, `exact`, `apply`, and `decide`, using
  allowlisted `locationHyp` locations including `at h` and `at h ⊢`) and unfold
  multi-arm `Trusted.*` definitions via `dsimp only [Trusted.foo]` rather than
  `simp [Trusted.foo]` or `unfold Trusted.foo` (preventing
  `Lean.Meta.getEqnsFor?` from lazily emitting `Trusted.foo.eq_N` theorems into
  `theory/` `.olean`s).

### 1.3 Human-Audited Correspondence TCB and Human-Comprehension Priority

The audit checks in Section 1.1 establish that the correspondence theorems are
kernel-checked proofs of the exact claims stated in `Trusted.Correspondence`.
They cannot establish that those claims mean what a reader expects, because a
claim is only as strong as the definitions it unfolds to. For example,
narrowing `WellFormed` or dropping caller-visible memory from `TerminalOut`
would weaken the locked theorems, yet the statement-origin checks would still
pass, because they inspect only which constants a claim names and where those
constants are defined.

**Human comprehension of the correspondence theorem statements
(`CorrespondenceClaim`, `FaultEquivalenceClaim`, and
`MiriMoveDeinitWiringClaim`) and every definition in their transitive dependency
cone is therefore the highest design priority in `Trusted.MirAst`,
`Trusted.MirSemantics`, and `Trusted.Correspondence`.** It must be immediately
clear to a human reviewer that each theorem statement means in mathematical
terms what they intend it to mean in intuitive terms. Clever encodings, indirect
formulations, or non-obvious subtleties in the theorem statements or their
transitive definitions are unacceptable: any proof-engineering complexity must
live in the untrusted proof (`correspondence/`), while every definition in the
theorem-statement dependency cone must be maximally direct, self-evident to a
human auditing the file, and documented so that every boundary condition is
explicit.

Human reviewers audit every definition that controls the meaning of the claims,
together with every later change to those definitions:

| Component | Theorem-controlling definitions |
| :--- | :--- |
| `Trusted.MirAst` | AST types (`MirTy`, `EnumTy`, `StatementKind`, |
| | `Rvalue`, `TerminatorKind`, `Body`), |
| | `VerificationScope`, `Program` (`pointerWidthBits`, |
| | `mirProfileVersion`, `scope`) |
| `Trusted.MirSemantics` | `Val`, `Query`, `Out`, `TerminalOut`, `FaultKind`, |
| | `StepResult`, `LocalSlot`, `FrameState`, `State` |
| | `ValidChoice`, `Step`, `Reaches`, `ReachesResult`, |
| | `WellFormed`, `Behavior`, `Diverges`, |
| | `SatisfiesPost` |
| | `BodyStaticAdmitted`, `ValidEntryArgs`, |
| | `BodyVerified`, `Specs`, `Crate`, `ProgramVerified`, |
| | `CrateTheorem`, `UnitTheorem`, `entryProgForBody`, |
| | `bodiesHaveUniqueIdentities` (Section 4.5) |
| | `WpSoundnessClaim`, `WpFaultSoundnessClaim`, |
| | `prog*`, `Canary*Claim` (15 Day-1; 25 with Phase 1, memory, and casts) |
| `Trusted.Correspondence` | Codec (`RefProg`, `encodeProg`, `decodeProg`), |
| | reference machine & staged support gate |
| | (`initRefState`, `refIsSupportedLocalTy`, |
| | `refEnumAdmitted`, `refDiscriminantTypesValid`, |
| | `refInitMemoryAndRetPlace`, `refExecutionConfig`, |
| | `refLimits`, `evalRefStep`, `RefAllowedStep`, |
| | `toMiriBinOp`, `toMiriUnOp`) |
| | Reference predicates (`RefWellFormed`, |
| | `RefBehavior`, `RefDiverges`, `RefReachesOutcome`, |
| | `*AtChoices`, `faultToRefOutcome`), `SimulationInv` |
| | Locked `*Claim` constants (37 locked Pass 2 |
| | claims: aggregate & choice-coupled top-level, |
| | wiring, `AllowedStep` soundness, codec, |
| | byte codec, simulation, and `CanaryD6–D16`) |
| `vendor/lean-miri/` | Pinned 160-module `ExecutionMachine` slice and |
| | 10-file `deinitMovedPlace` patch (`UPSTREAM_PIN.json`) |

- **`Trusted.MirAst` and `Trusted.MirSemantics` (`trusted/lean/`):** These
  modules define the programs, inputs, state/outcome types (`State`,
  `FrameState`, `LocalSlot`, `FaultKind`, `TerminalOut`), trace predicates
  (built from `Step` and `ValidChoice`) that turn `initState` and `evalStep`
  into the claims' hypotheses and conclusions, top-level verification judgments
  (`BodyStaticAdmitted`, `ValidEntryArgs`, `BodyVerified`, `Specs`, `Crate`,
  `ProgramVerified`, `CrateTheorem`, `UnitTheorem`, and helpers such as
  `entryProgForBody` and `bodiesHaveUniqueIdentities`; Section 4.5), and the
  concrete `prog*` fixtures and `*Claim` propositions enforced on
  `Anneal.MirWp` (15 Day-1 baseline; 20 once fieldless enums, `!`, crate/unit
  scope, and byte-level memory land, including
  `CanaryCrateAndBodyVerifiedAnnealClaim` and
  `CanaryMemoryLifecycleAnnealClaim`; 25 with `char`, `BinOp.cmp`,
  `BinOp.*WithOverflow`, and `CastKind.intToInt`).
  `SatisfiesPost` is the contract that per-function specifications discharge
  through `Anneal.MirWp`. The correspondence theorems cross-check the execution
  rules inside `initState` and `evalStep` against $M_{\text{ref}}$, but they
  assume, rather than check, the meaning of the predicates built on those rules.
- **`Trusted.Correspondence` (`trusted/correspondence/`):** This module defines
  the codec (`RefProg`, `encodeProg`, and `decodeProg`); the reference machine
  and staged support gate that the claims observe (`initRefState`,
  `refIsSupportedLocalTy`, `refEnumAdmitted`, `refDiscriminantTypesValid`,
  `refInitMemoryAndRetPlace`, `refExecutionConfig`, `refLimits`,
  `evalRefStep`, `RefAllowedStep`, `ValidRefChoice`, `RefStep`, `RefReaches`,
  and the operator tables `toMiriBinOp` and `toMiriUnOp`); the aggregate and
  choice-coupled reference predicates and simulation invariant
  (`RefReachesOutcome`, `RefWellFormed`, `RefBehavior`, `RefDiverges`,
  `RefReachesAtChoices`, `RefValidPrefixAtChoices`,
  `RefReachesOutcomeAtChoices`, `RefBehaviorAtChoices`,
  `RefDivergesAtChoices`, `faultToRefOutcome`, and `SimulationInv`); and the
  locked `*Claim` propositions (37 locked Pass 2 claims: `CorrespondenceClaim`,
  `FaultEquivalenceClaim`, `CorrespondenceAtChoicesClaim`,
  `FaultEquivalenceAtChoicesClaim`, `MiriMoveDeinitWiringClaim`,
  `RefStepSoundForAllowedStepClaim`, `BytesCodecMatchesMiriClaim`, the 6 codec
  claims, the 11 uniqueness and simulation claims, and
  `CanaryD6*Claim`–`CanaryD16*Claim`).
- **`vendor/lean-miri/`:** `Trusted.Correspondence` drives `evalRefStep`
  directly through `Miri.Interpreter.ExecutionMachine.step`, reaching all 39
  required live `ExecutionMachine` primitives (`ExecutionMachine.{step,
  withValidation,stepHooks,rvalueHooks,operandHooks,projectionHooks,
  discriminantHooks,scalarHooks}`, `Step.{step,evalStatement}`,
  `ControlFlow.{goToBlock,evalTerminator,returnFromCurrentFrame}`,
  `ExecutionControl.hooks`, `MachineHooks.{storageLiveDyn,storageDead}`,
  `OperandMachine.{evalOperand,evalPlaceToOp}`,
  `PlaceMachine.{readImmediate,writeMemory}`,
  `ValidityVisitor.validatePlace`, `ValidityMemory.bind`,
  `evalRvalueIntoPlace`, `TerminatorMachine.beforeTerminatorWithChoice`,
  `ScalarOps.{binary,unary}`, `IntegerOps.{binary,binaryBool,binaryChar,
  unary}`, `Cast.cast`, `IntegerCast.cast`,
  `Discriminant.{readDiscriminant,discriminantForVariant}`, and
  `ScalarInt.{truncateFromUInt,tryFromUInt,tryToBool,toChar,ofChar}`), while
  `RefAllowedStep` separately instantiates `ExecutionMachine.AllowedStep` and
  is tied to `RefStep` by `RefStepSoundForAllowedStepClaim` (all verified by
  `verifyRefEvaluatorIndependence` and `verifyCorrespondenceClaims`,
  Section 1.1), and states the wiring of `ExecutionMachine.step`,
  `OperandMachine.evalOperand`, and `LocalAccess.evalOperand` in
  `MiriMoveDeinitWiringClaim` (Section 5.2), so
  those definitions control the meaning of the reference machine. The vendored
  tree is therefore part of the pinned, human-audited correspondence TCB, not
  merely an input checked for forbidden axioms. `UPSTREAM_PIN.json` pins every
  file to its audited digest, any change to a pinned digest (including a new
  patch) requires the same human audit as a change to `trusted/`, and
  `verifyAndCollectCorrLocals` keeps vendored declarations out of the `Trusted`
  and `Anneal` namespaces.

---

## 2. Reference Model ($M_{\text{ref}}$) and Move Deinitialization

### 2.1 Vendored `lean-miri` Core

Anneal uses `lean-miri` (pinned at upstream `proofs-rs/lean-miri` commit
`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, which targets `miri` commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1` and `rustc` commit
`8144389c895da997dbdecaa635e41d6a50be6ffd`) as $M_{\text{ref}}$. Upstream
`c92d1d97` pins `leanprover/lean4:v4.35.0` in its `lean-toolchain` (recorded as
`upstream_lean_toolchain` in `UPSTREAM_PIN.json`), whereas Anneal builds and
audits the 160-module `ExecutionMachine` closure under Anneal's locked
`leanprover/lean4:v4.34.1` toolchain (`build_lean_toolchain`, verified by
`verify_upstream_pin`). The 160-module closure compiles cleanly under `v4.34.1`
with kernel typechecking enabled (`-t0 -DElab.async=false
-Ddebug.skipKernelTC=false`) and passes `anneal-audit`'s standalone kernel
replay. Compiling cleanly under `v4.34.1` establishes kernel well-typedness
under `v4.34.1`, not semantic equivalence with upstream `lean-miri`'s `v4.35.0`
test suite; correspondence proofs and canaries therefore validate
reference-model behavior directly under Anneal's locked `v4.34.1` toolchain,
and toolchain alignment to `v4.35.0` is planned once Anneal upgrades its locked
foundation. Because `anneal-rustc-capture` targets Stage 2
`Runtime(PostCleanup)` MIR from Anneal's pinned `rustc` toolchain
(`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), the correspondence TCB audits
that every enabled Stage 2 MIR construct in `Trusted.MirAst` has identical
post-cleanup operational rules across both `rustc` revisions, and stamps
captured programs with an explicit semantic profile version
(`mirProfileVersion : Nat`; Section 3.1) that both `initState` and
`initRefState` verify fail-closed. `lean-miri` is a mechanized Lean 4
interpreter modeled line-by-line on `rustc_const_eval::interpret`. Each
invocation of `evalRefStep` in `Trusted.Correspondence` executes one MIR
statement or terminator in a single deterministic step without an internal
substep fuel cutoff (and `ExecutionMachine.step` in `vendor/lean-miri` is
parameterized over `limits : ExecutionMachine.Limits`, which is universally
quantified in `MiriMoveDeinitWiringClaim`), taking a nondeterminism oracle
(`choice : Choice`) and a reference state and returning one of five outcomes:

- `.running nextState`: the statement or terminator stepped normally.
- `.returned out`: the root frame executed `TerminatorKind.Return`, copied `_0`
  into the caller-owned return allocation `retPlace`, and popped.
- `.exhaustedStepLimit`: the execution reached its configured step budget
  (`stepsExecuted ≥ maxSteps`).
- `.ub`: the execution triggered modeled Rust Undefined Behavior (such as
  reading uninitialized data, dividing by zero, overflowing an unchecked
  arithmetic operator, or accessing a dead local).
- `.blocked`: the execution encountered an unmodeled feature, missing hook, or
  malformed MIR invariant (such as an out-of-bounds basic-block index or an
  unsupported statement, rvalue, or terminator).

### 2.2 Single-Source Type Table and Layout Adapters

`lean-miri` names types by `TyId := Nat` and asks its hook records for
layouts. Rather than maintaining several tables that could disagree on a type's
size or signedness, `Trusted.Correspondence` keeps a single program-wide table:

```lean
structure RefProg where
  bodies : List RefBody
  entryDefId : DefId := 0
  types : List MirTy
  pointerWidthBits : Nat
  mirProfileVersion : Nat
  scope : VerificationScope
```

Every `TyId` in a reference program resolves through `rp.types[tyId]?`:
`initRefState` resolves the entry body's local declarations once
(`decodeLocalTys`) and pre-caches each local's `Miri.Interpreter.LocalLayout`
in the real `Miri.Interpreter.Frame`, while constant operands resolve their
`TyId` through `refExecutionConfig rp` (`evalConst`). An out-of-bounds `TyId`
makes the step `.blocked`.

The `ExecutionMachine.Config` adapters in
`Trusted/Correspondence/{State,Config}.lean` derive real `lean-miri` layouts
from `rp.types[tyId]?`:

- `refLocalLayoutForTy` gives `()` and admitted one-variant zero-sized enums
  their 0-byte `Layout` (`isZst = true`), scalar integers and `bool` their
  exact scalar byte widths and signedness (`refScalarLayoutData`), non-ZST
  admitted fieldless enums their `Variants.Multiple` scalar tag layout
  (`refEnumLayoutData`), and uninhabited `!` (`MirTy.never`) an uninhabited
  0-byte/non-ZST-marked layout (`refNeverLayoutData`) so moving a `!` local
  takes Miri's deinitialization branch and reading it faults with `.ub`.
- `refScalarLayoutData w signed` gives an integer or discriminant value the
  scalar layout of `toMiriSize w` bytes (`1`, `2`, `4`, `8`, or `16`) with
  signedness `signed`. Because `isize` and `usize` use 8 bytes, which is
  correct only on 64-bit targets, `initRefState` rejects every `RefProg` whose
  `pointerWidthBits` is not `64` (Section 3.1).
- `refEnumLayoutData ety` gives a fieldless enum the layout
  `Variants.Single 0` (0 bytes) when its tag is zero-sized and
  `Variants.Multiple tag .Direct 0 variants` over its scalar tag otherwise,
  which `Miri.Interpreter.Discriminant` decodes directly inside
  `ExecutionMachine.discriminantHooks`.

In `lean-miri`, `OperandMachine.localToOp` caches a local's layout in
`frame.locals` on its first read. Because `initRefState` pre-caches every
local's `LocalLayout` in `Miri.Interpreter.LocalState` (and uninitialized
non-ZST locals are stored directly as real `.live (.immediate .uninit)`),
read-only operand evaluations (`Operand.copy`) leave `frame.locals` unchanged
and Miri's own `.uninit` read and validity checks (`PlaceMachine.readImmediate`,
`ValidityVisitor.validatePlace`, and `Discriminant.readDiscriminant`) enforce
uninitialized-read and invalid-tag UB natively.

### 2.3 Real `ExecutionMachine` Return-Place Ownership

In `lean-miri`, the entry function's return place belongs to its caller:
`MainThread.callMain` (`vendor/lean-miri/Miri/Interpreter/MainThread.lean`)
allocates the return place in `Miri.Memory.MemoryState` before pushing the
entry frame, so that place outlives the entry frame. On
`TerminatorKind.Return`, `ControlFlow.returnFromCurrentFrame` reads `_0`,
validates and copies it into `frame.returnPlace`, pops the returning frame, and
observes `frame.returnContinuation = .stop false`.

`Trusted.Correspondence` mirrors this ownership directly in real
`Miri.Memory.MemoryState` (`refInitMemoryAndRetPlace` in
`Trusted/Correspondence/State.lean`):

- `initRefState` allocates a fresh caller-owned return allocation `retPlace :
  Miri.Interpreter.MPlaceTy Miri.Memory.Provenance` sized to the entry body's
  return type `retTy = localTys[0]` in `Miri.Memory.MemoryState` and starts the
  real `Miri.Interpreter.MachineHooks.State Unit RefUser` with the single entry
  frame (`returnPlace := .memory retPlace`, `returnContinuation := .stop
  false`).
- On `TerminatorKind.Return`, `ExecutionMachine.step` runs Miri's real
  `ControlFlow.returnFromCurrentFrame` (`copyRuntimePlace` into `retPlace`,
  `ValidityVisitor.validatePlace`, frame pop) and returns `(miri', .ok true)`
  with an empty stack (`miri'.stack.frames.isEmpty = true`), after which
  `evalRefStep` reads the validated return value back from `retPlace` in
  `miri'.machine.memory` (`refReadReturnVal`) to construct
  `.returned (.returned ⟨retVal, callerMem⟩)`.
- `SimulationInv` (Section 5.3) relates every running $M_{\text{anneal}}$ state
  to that single-frame `ExecutionMachine` state together with its unchanged
  caller-owned `retPlace` allocation in `miri.machine.memory`.

### 2.4 Runtime Move Deinitialization

Upstream `lean-miri` follows
`compiler/rustc_const_eval/src/interpret/operand.rs` (line 847 at `8144389c` /
line 842 at `f8a08b68`), which implements `Operand::Move(place)` identically to
`Operand::Copy(place)` (``// FIXME: do some more logic on `move` to invalidate
the old location``). While treating `move` as `copy` is benign for compile-time
constant evaluation of borrow-checked safe Rust, Anneal captures
`Runtime(PostCleanup)` MIR—after the elaborate-drops and drop-shim passes have
run—and verifies `unsafe` Rust code where raw pointer dereferences can alias
moved locals. In `rustc`'s own MIR syntax documentation
(`compiler/rustc_middle/src/mir/syntax.rs:1310-1327` at `f8a08b68`),
`Operand::Move` *may* overwrite the moved-from place with `uninit` (leaving the
exact boundary under discussion in Rust UCG#188 / marked "Needs clarification").
MiniRust removed destructive loads in `minirust@766d8d619a` (2023-07-28) and
deinitializes only in-place call arguments, so value loads on `Operand::Move`
only read the place. Anneal's rule deinitializing every non-zero-sized moved
place so that any subsequent read before reinitialization is Undefined Behavior
is therefore a deliberate conservative choice—stricter than current Miri,
codegen, and MiniRust, and permitted by `rustc`'s MIR contract. Rather than
deferring reads of moved places via a gated `.unsupported`/`.blocked` pair
under [`docs/mir-correspondence-strategy.md`](mir-correspondence-strategy.md)
Section 4.1, Anneal enables the matching rule in $M_{\text{ref}}$ via
`deinitMovedPlace = true` so both models classify moved-place reads identically
as `.undefined` / `.ub`, which is why canaries `D6`, `D7b`, and `D7c` record
`.undefined` / `.ub` under `FaultEquivalenceClaim` (even though those programs
are not UB under current Miri or MiniRust).

To make $M_{\text{ref}}$ enforce runtime move deinitialization without altering
the signatures or constructors used by upstream callers, we add an opt-in
configuration flag `deinitMovedPlace : Bool := false` across 10 files in
`vendor/lean-miri/Miri/`
(`MachineHooks.lean`, `LocalAccess.lean`, `OperandMachine.lean`, `Place.lean`,
`PlaceMachine.lean`, `Cast.lean`, `ExecutionCast.lean`, `Call.lean`,
`ExecutionCalls.lean`, and `ExecutionMachine.lean`). `Trusted.Correspondence`
sets `deinitMovedPlace := true` on `refExecutionConfig rp`, driving every
`copy` and `move` operand directly through `ExecutionMachine.step` ->
`ExecutionMachine.operandHooks` ->
`Miri.Interpreter.OperandMachine.evalOperand`.
`MiriMoveDeinitWiringClaim` (Section 5.2) kernel-proves
`ExecutionMachine.step`'s `pendingMoveDeinit` clearing, the `deinitMovedPlace`
flags on `ExecutionMachine.withValidation(...).access` and
`ExecutionMachine.operandHooks`, both `OperandMachine.evalOperand` (the live
operand path executed by `evalRefStep`) and `LocalAccess.evalOperand` for
unprojected immediate moves,
`recordPendingMoveDeinit`/`takeLastPendingMoveDeinit`,
and `FnArg.copyFnArg`/`Call.deinitInPlaceArg` (kernel-checking those wiring
entries in `ExecutionMachine`, `OperandMachine`, `LocalAccess`, `MachineHooks`,
and `Call`, while `ExecutionMachine`, `OperandMachine`, `PlaceMachine`, and
`Place` enter `correspondence_claim_holds` directly). The remaining call, cast,
indirect-move, and intrinsic propagation (`ExecutionCalls`, `ExecutionCast`,
`Cast`, `evalCopyNonOverlappingDeinit`, and the unverified arms of
`ExecutionMachine`, `MachineHooks`, and `Call`) is trusted by human audit and
pinned against drift by `UPSTREAM_PIN.json` digests rather than proved by a
kernel theorem.

In `lean-miri`, `OperandMachine.evalOperand` evaluates a `Place` via
`evalPlaceToOp` into an `OpTy` whose runtime payload is either:

- **`Operand.immediate imm`:** For an unprojected local
  (`place.projection.isEmpty`), the local variable's scalar or zero-sized value
  has already been copied by value out of `frame.locals[localId]` into `imm`.
  When `deinitMovedPlace` is `true` and `evalOperand` evaluates `.Move place`,
  it first runs `evalPlaceToOp` (so any out-of-bounds or dead-local error fires
  before mutation, and `pendingMoveDeinit` is cleared), then resets
  `frame.locals[place.localId]` to `.live (.immediate .uninit)` (unless the
  local's layout is zero-sized):
  - In `_1 = move _1` (self-move), `evalOperand` extracts the old value of `_1`
    and marks `_1` as `.uninit`, after which `writePlaceImmediate` overwrites
    `_1` with the extracted value.
  - In `BinOp(lhs, rhs)`, `Rvalue.BinaryOp` evaluates and reads `lhs` before
    evaluating `rhs`. Hence `BinOp(copy _1, move _1)` reads `_1` in `lhs` and
    moves `_1` in `rhs`, whereas `BinOp(move _1, copy _1)` and `BinOp(move _1,
    move _1)` deinitialize `_1` during `lhs` and fault with `.ub` when `rhs`
    reads `_1`.
  - When `_1` has a zero-sized layout (`()` or an admitted one-variant enum),
    `evalOperand` leaves its value in place: a 0-byte value has no bytes to
    invalidate, and `.immediate .uninit` is already its canonical valid
    representation in `lean-miri` (`Immediate.lean`, `ValidityVisitor.lean`).
    Moving such a local therefore leaves it valid and initialized, matching
    `liveUninitSlot` in $M_{\text{anneal}}$.
- **`Operand.indirect mplace`:** For memory-backed locals, projected fields in
  memory, and pointer dereferences (`*_1`) in Phase 2, `evalPlaceToOp` returns a
  lazy pointer (`MemPlace`) into `state.machine.memory` that consumers
  (`PlaceMachine.readImmediate`, `Place.copyRuntimePlaceNoValidate`,
  `Cast.cast`, and `Call.passArgument` / `Call.allocateVarargs`) read *after*
  `evalOperand` returns. (If `evalPlaceToOp` succeeds with `.immediate _` on a
  projected local `!place.projection.isEmpty`, meaning the local has no `.Deref`
  projection and every projection step is valid, `evalOperand` in both
  `OperandMachine.lean` and `LocalAccess.lean` materializes the base local via
  `forceAllocation` / `forceLocalAllocation` and re-runs `evalPlaceToOp` to
  obtain `.indirect mplace` for the projected sub-place.) Rather than adding a
  field to `OpTy` (which would break 2-argument `⟨op, layout⟩` constructors
  across 174 files in `vendor/lean-miri/Miri/`), `evalOperand (.Move place)`
  arms `pendingMoveDeinit` on `MachineHooks.MachineState`
  (`recordPendingMoveDeinit`), while `evalPlaceToOp` (and therefore every
  `Copy`) and the `Constant` and `RuntimeChecks` arms of `evalOperand` clear
  it:
  - Inside `PlaceMachine.readImmediate` (`BinaryOp`, `UnaryOp`, `SwitchInt`,
    `Assert`), the consumer atomically takes `pendingMoveDeinit`, runs
    upstream `Miri.Interpreter.readImmediate` (checking scalar layout, pointer
    alignment, borrow-tracker permissions, and `.uninit` bytes), and then writes
    `.uninit` to `⟨mplace, operand.layout⟩` via
    `writeImmediateToMplaceNoValidate`.
  - Inside `Place.copyRuntimePlaceNoValidate` (`Rvalue.Use`, `Aggregate`,
    `Repeat`, `WrapUnsafeBinder`), the consumer atomically takes
    `h.takePendingMoveDeinit` after `compatible` and `hasPadding` checks. In the
    `.immediate value` branch, it deinitializes `⟨mplace, source.layout⟩`
    via `h.writeMemoryNoValidate choice .uninit` *before* writing
    `value.value` to `dest` (preserving indirect self-moves
    `*_1 = move *_1`); in the `.place memory` branch (padded or memory-backed
    structs/arrays), it runs `copy.memoryCopy` (which enforces
    `nonoverlapping = true`, rejecting non-ZST overlapping `Assign` places as
    `overlapping copy_nonoverlapping` UB per Rust MIR's disjoint-`Assign` rule)
    and then, when `shouldDeinit` is `true`, deinitializes
    `⟨memory.mplace, source.layout⟩` via `h.writeMemoryNoValidate choice
    .uninit` (which is a no-op on zero-sized places because their byte length is
    `0`), before `copyRuntimePlace` runs destination validity checks
    (`h.validate choice dest`). On the zero-length `Repeat` (`[move x; 0]`) path
    where `writeRepeat` skips `copyOp`, `ExecutionMachine.rvalueHooks`
    explicitly consumes `takePendingMoveDeinit` and deinitializes `source`'s
    `mplace` after `getPlaceAllocMut` validates the destination.
  - Inside `Cast.cast` (`Rvalue.Cast`), `Cast.cast` atomically takes
    `shouldDeinit ← h.takePendingMoveDeinit` at entry before any intermediate
    helper read (`checkFunctionPointer`, `BoxDerefTransmute`, or per-field
    `copyNoValidate` inside `unsizeInto`) can consume the flag, then
    deinitializes the complete source operand via `h.deinitSource choice source`
    once the cast or unsizing copy completes.
  - Inside `Call.evalCalleeAndArgs`, `Call.evalFnCallArgumentAt`,
    `Call.passArgument`, `Call.allocateVarargs`,
    `Call.materializeAndDeinitArgs`, `Call.initFnCallStep`, `Call.initFnCall`,
    and `Call.initFnTailCall` (`TerminatorKind.Call` and `TailCall`), setting
    `h.deinitMovedPlace = false` leaves upstream behavior unchanged
    (`snapshotInPlaceArg` returns `.InPlace place none` with no snapshotting or
    unsized-move rejection, and no move deinitialization runs). When
    `h.deinitMovedPlace` is `true`, moving an unprojected `.immediate` argument
    deinitializes `frame.locals[place.localId]` (preserving valid ZST
    immediates when `layout.isZst`). In `evalCalleeAndArgs`, whenever `hasMove`
    is `true` (`isMoveFunc || args.any ...`) and `func` evaluates to an
    indirect `.indirect mplace`, a sized `func` is snapshotted into a temporary
    stack allocation (`tmpFunc` via `h.copyToMemory`, preserving Tree Borrows,
    race, alignment, and initialization checks) before argument evaluation can
    deinitialize an alias of `func`, and `⟨mplace, func.layout⟩` is
    deinitialized via `h.deinitInPlaceArgument` only when `isMoveFunc` is
    `true` (while `ExecutionCalls.make` clears `pendingMoveDeinit := false`
    after `evalOperand` / `evalOperandAt`); if `func` is an unsized `.indirect`
    callee (`!func.layout.layout.isSized`) while `hasMove` is `true`,
    `evalCalleeAndArgs` fails closed with `StepError.unsupported` (`.blocked`
    in $M_{\text{ref}}$) so a later aliased `.Move` cannot overwrite an
    un-snapshotted callee (and an unsized `.Move` callee cannot pass through
    un-deinitialized). When a `.Move` argument resolves to an `.InPlace` memory
    place during `evalCalleeAndArgs`, `evalFnCallArgumentAt` calls
    `snapshotInPlaceArg`: for a sized place (`place.layout.layout.isSized`),
    `snapshotInPlaceArg` snapshots the argument into a temporary stack
    allocation (`tempAllocs`) and marks the source `MPlaceTy`'s raw bytes
    `.uninit` (`h.markInPlaceMovedUninit`) immediately during argument
    evaluation so any later operand evaluation that aliases the moved place
    sees `.uninit` and reports UB; for an unsized `.Move` `.InPlace` place
    (`!place.layout.layout.isSized`), `snapshotInPlaceArg` fails closed with
    `StepError.unsupported` (`.blocked` in $M_{\text{ref}}$) rather than
    passing an un-deinitialized moved place through where a subsequent aliasing
    operand could still read stale initialized bytes. Indirect `.Copy`
    arguments in calls with `hasMove = true` are snapshotted into `tempAllocs`
    via `h.copyToMemory` when sized (preserving canonical read access checks),
    and fail closed with `StepError.unsupported` (`.blocked` in
    $M_{\text{ref}}$) when unsized so a later aliased `.Move` cannot overwrite
    an un-snapshotted `.Copy` argument; when `hasMove = false`, unsized `.Copy`
    arguments pass through unchanged. Inside `passArgument`, `allocateVarargs`,
    and `materializeAndDeinitArgs`, sized `.InPlace` arguments restore their
    snapshotted raw bytes (`h.restoreInPlaceMovedBytes`), copy from `srcPlace`
    via `h.copyAllowTransmute` / `h.copyToMemory` (so the copy runs with full
    Tree Borrows, data-race, alignment, and validity checks on `srcPlace`), and
    deinitialize `srcPlace` via `h.deinitInPlaceArgument` (followed by
    `h.protectArgument` in `passArgument`), while `materializeAndDeinitArgs`
    likewise fails closed with `StepError.unsupported` (`.blocked`) whenever
    `h.deinitMovedPlace = true` and `args.any (.InPlace ..)` on any unsized
    indirect `.Copy` or `.InPlace` argument. On non-copying call paths
    (`findMirOrEvalFn = none` and an empty `isRustCall` tuple),
    `deinitInPlaceArg` restores any snapshotted raw bytes and invokes
    `h.deinitInPlaceArgument` (`writeMemoryNoValidate .uninit`). A `.Virtual`
    call restores a snapshotted (sized) receiver's bytes before `resolveVirtual`
    reads the receiver (so its alignment, Tree Borrows, and data-race read
    checks apply to the original place) and deinitializes that sized receiver
    after dispatch (while an unsized `.Move` receiver—or any unsized indirect
    `.Copy` receiver when `hasMove = true`—was already rejected fail-closed
    with `.blocked`, and an unsized `.Copy` receiver when `hasMove = false`
    passes through intact across `resolveVirtual`). Every call path deallocates
    its temporary stack allocations via `deallocateStack`, including on error.
  - In `ExecutionMachine.stepHooks` (`intrinsic` hook), a
    `CopyNonOverlapping` statement with at least one `Move` operand routes
    evaluation through `evalCopyNonOverlappingDeinit` (which then delegates to
    `Intrinsics.copyWith`), because the intrinsic evaluates all three operands
    before it reads any of them, so a single pending flag cannot carry their
    moves. After evaluating each operand in `(src, dst, count)` order,
    `PlaceMachine.trySnapshotMPlace` checks read access (`getPlaceAlloc`)
    on a sized indirect operand: if backed by a live, in-bounds allocation, it
    copies the operand's evaluation-time bytes into a temporary stack allocation
    and, when the operand is a `Move` to an aligned, mutable place, immediately
    marks the source bytes raw `.uninit` so a later operand that reads an
    aliased place observes the move (leaving misaligned or immutable moved
    places unmodified until read time). Intermediate `dst` and `count`
    evaluations wrap prior snapshots in `cleanupTempStackAllocsOnError` so
    snapshots remain live across all three operand evaluations and are only
    deallocated early on error; `cleanupTempStackAllocs` then deallocates all
    snapshots once after `copyWith` finishes (on success or error). `copyWith`
    reads the operands in its upstream `(count, src, dst)` order through
    `PlaceMachine.readImmediateFromSnapshot`, which runs the original place's
    pointer, bounds, alignment, data-race, and Tree Borrows read checks, reads
    the value from the snapshot, and (when moved) writes `.uninit` to the
    original place via `PlaceMachine.writeMemory` (triggering the canonical
    `.readOnlyAllocation` error for a moved read-only allocation and the
    canonical alignment error for a misaligned place). An operand that cannot
    be snapshotted (immediate, unsized, dangling, or out of bounds) falls back
    to `PlaceMachine.readImmediate`, so `copyWith` reads immediates directly
    and reports the upstream error in upstream `(count, src, dst)` order.
  - Finally, `ExecutionMachine.step` clears `pendingMoveDeinit := false` before
    and after every statement or terminator step so no unconsumed flag can leak
    into a subsequent step.

### 2.5 Direct `ExecutionMachine.step` Protocol (`Config.lean` and `Eval.lean`)

Inside `Trusted.Correspondence`, `evalRefStep` drives every statement and
terminator directly through
`Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c
rs.miri` over real `Miri.Interpreter.MachineHooks.State Unit RefUser`, passing
a real translated `Miri.MIR.Body` (`toMiriBody`):

- **Body, operand, rvalue, and terminator translation (`toMiriBody`,
  `toMiriOperand`, `toMiriRvalue`, `toMiriTerminator`):** `toMiriOperand` maps
  `RefOperand` to `Miri.MIR.Operand`, encoding scalar constants with their real
  `RefProg.types` index `c.ty` and 128-bit payload carrier and zero-sized
  constants as `.ZeroSized`. `toMiriRvalue` maps `.use`, `.binaryOp`,
  `.unaryOp`, and `.discriminant` to their real `Miri.MIR.Rvalue` constructors
  (`Use`, `BinaryOp`, `UnaryOp`, `Discriminant`) with real translated operands
  and places, while unmodeled Day-1 rvalues (`.ref`, `.addressOf`,
  `.aggregateTuple`, `.unsupported`) route to `.CopyForDeref ⟨0, #[]⟩`, which
  `evalRvalueIntoPlace` rejects fail-closed with `.invalidProgram` (mapped to
  `.blocked`). Likewise, `.goto`, `.switchInt`, `.return_`, and `.unreachable`
  translate directly to their real `Miri.MIR.TerminatorKind` constructors,
  while unmodeled Day-1 terminators (`.unwindResume`, `.assert`, `.call`,
  `.unsupported`) route to `.CoroutineDrop`, which `ControlFlow.evalTerminator`
  rejects fail-closed with `.invalidProgram` (`.blocked`).
- **Real `ExecutionMachine.Config` (`refExecutionConfig rp`):** Sets
  `deinitMovedPlace := true`, `enforceValidity := true` (shallow validation via
  `ValidityMemory.bind` -> `ValidityVisitor.validatePlace`), disables Tree
  Borrows and data-race trackers (which are inactive on Day-1 register-only
  programs with no pointers), wires `layoutOf` / `evalConst` / `discriminant`
  leaves against `rp.types`, and leaves unmodeled Day-1 callbacks (`cast`,
  `call`, `drop`, `intrinsic`, `ref`) fail-closed with `.unsupported`.
- **Single-step execution and allowed-step predicate (`evalRefStep`,
  `RefAllowedStep`):** `evalRefStep` enforces `rs.stepsExecuted < rs.maxSteps`
  (returning `.exhaustedStepLimit` at the budget), runs
  `ExecutionMachine.step (refExecutionConfig rp) refLimits c rs.miri`, and
  classifies the result: `(_, .ok true)` with non-empty stack returns
  `.running` (incrementing `stepsExecuted`), `(_, .ok true)` with empty stack
  reads the validated return value from `rs.retPlace` in `miri'.machine.memory`
  (`refReadReturnVal`), `(_, .error (.undefinedBehavior _))` and
  `(_, .error (.stack (.localExpectedLive _)))` return `.ub`, and all other
  errors or `(_, .ok false)` return `.blocked`. `RefAllowedStep` instantiates
  `Miri.Interpreter.ExecutionMachine.AllowedStep` directly over
  `refExecutionConfig rp` and admissible choices `c = 0`, and
  `RefStepSoundForAllowedStepClaim` kernel-proves that every non-exhausted
  `RefStep` transition (`.running` or `.returned`) satisfies `RefAllowedStep`
  at `refLimits`.

---

## 3. MIR Representation (`Trusted.MirAst`) and Canonical Type Codec

### 3.1 Structural Types by Value in `Trusted.MirAst`

In `Trusted.MirAst`, MIR types (`MirTy`) are structural inductive values carried
directly inside AST nodes (`Body.locals : List MirTy`, `ConstOperand.ty :
MirTy`, and `ProjectionElem.field : FieldIdx → MirTy → ProjectionElem`):

```lean
inductive IntWidth where
  | i8 | i16 | i32 | i64 | i128 | isize

inductive Mutability where
  | shared | mut

inductive MirTy where
  | bool
  | int (width : IntWidth) (signed : Bool)
  | unit
  | never
  | char
  | ordering
  | enum (ty : EnumTy)
  | tuple (fields : List MirTy)
  | ref (mutability : Mutability) (pointee : MirTy)
  | rawPtr (mutability : Mutability) (pointee : MirTy)
  | unsupported
```

`MirTy.never` types the uninhabited `!`, `MirTy.char` types `char`,
`MirTy.ordering` types `core::cmp::Ordering`, and `MirTy.enum ety` types a
fieldless enum. `EnumTy` records the enum's nominal identity (`id`), its
discriminant type (`discrWidth`, `discrSigned`), its tag encoding (`tagRepr`:
`.zeroSized` for a one-variant enum, or `.scalar tagW tagS`), and its declared
`discriminants` in variant order. Both machines admit an enum only when its
discriminants are non-empty, pairwise distinct, representable in the
discriminant type, and recoverable from their truncated tags (`enumAdmitted` in
$M_{\text{anneal}}$ and the independent `refEnumAdmitted` in
$M_{\text{ref}}$). $M_{\text{ref}}$ decodes constant enum tags and evaluates
`Rvalue.discriminant` through `Miri.Interpreter.Discriminant`.

Carrying `MirTy` by value eliminates out-of-bounds type-table indices (`TyId`)
and duplicate-index aliasing from `Trusted.MirAst` and `Trusted.MirSemantics`:
two types in $M_{\text{anneal}}$ are equal if and only if they are structurally
equal (`t₁ = t₂`). To satisfy `TrustedBoundary.lean`'s `deriving`-free
syntax allowlist in `trusted/`, `Trusted.MirAst` defines structural equality
via pure pattern-matching functions (`IntWidth.beq`, `Mutability.beq`,
`MirTy.beq`).

Similarly, constant literals (`ConstLit`) represent only modeled constant shapes
(`.scalar (bits : BitVec 128)` and `.zeroSized`). In the target Stage 1
pipeline (landing incrementally once `anneal-rustc-capture` moves beyond its
initial stub), whenever `anneal-rustc-capture` encounters any unmodeled
constant, statement, rvalue, terminator, or type in Stage 2
`Runtime(PostCleanup)` MIR, it is required to fail closed with a hard capture
error and never rewrite unsupported MIR into generic `.unsupported` nodes. The
`.unsupported` constructors (`MirTy.unsupported`, `StatementKind.unsupported`,
`Rvalue.unsupported`, and `TerminatorKind.unsupported`) exist solely in
`Trusted.MirAst` as explicit AST sentinels for testing and verifying fail-closed
`.unsupported` / `.blocked` fault handling in `CorrespondenceClaim`,
`FaultEquivalenceClaim`, and negative canaries (such as
`canary_negative_unsupported_anneal`).

`Program` collects the function bodies and records the pointer width of the
captured target, the Stage 2 MIR semantic profile version, and the capture
scope:

```lean
structure Program where
  bodies : List Body
  entryDefId : DefId := 0
  pointerWidthBits : Nat
  mirProfileVersion : Nat
  scope : VerificationScope
```

`scope` distinguishes whole-crate capture (`.crate`, verified through
`CrateTheorem`) from a selected proof unit (`.unit`, verified through
`UnitTheorem`; see Section 4.5 for exact definitions of `VerificationScope` and
the crate/unit verification judgments). It changes which bodies the crate
theorems quantify over, not how a body executes, so neither machine consults it
during execution; the codec carries it, together with each body's `isUnsafe`
and `identity`, unchanged.

Once implemented, `anneal-rustc-capture` records the target layout,
compiler/MIR profile, and capture scope in the `CaptureManifest`
([`docs/architecture.md`](architecture.md)). `Program` and `RefProg`
deliberately omit Lean field defaults for `pointerWidthBits`,
`mirProfileVersion`, and `scope` so that any capture serializer omitting these
fields fails at Lean elaboration/compile time rather than silently defaulting
to accepted values (`64`, `1`, or `.unit`) and bypassing the initializer or
scope gates; hand-written test fixtures and canaries can use a separate
test-only helper constructor if concise defaults are desired:

- **Target pointer-width gating (`pointerWidthBits = 64`):** Both semantics
  model `isize` and `usize` as 8-byte integers (`IntWidth.byteSize .isize = 8`
  in $M_{\text{anneal}}$, and `toMiriSize .isize` is 8 bytes in
  $M_{\text{ref}}$), so both fail closed on every other target: `initState` and
  `initRefState` return `.error .unsupported` whenever `p.pointerWidthBits` is
  not `64` (`!Nat.beq p.pointerWidthBits 64`). Without this check, both models
  could share the 64-bit layout, agree with each other, and still accept
  overflow, shift, and layout behavior that differs from the compiled program on
  a 32-bit target.
- **Semantic revision and profile gating (`mirProfileVersion = 1`):** Because
  `anneal-rustc-capture` runs on Anneal's pinned `rustc` toolchain
  (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) while `vendor/lean-miri/` tracks
  upstream `miri`/`rustc` (`8144389c895da997dbdecaa635e41d6a50be6ffd`), the
  correspondence TCB audit verifies that every enabled Stage 2
  `Runtime(PostCleanup)` MIR construct has identical operational rules across
  both compiler revisions under profile version `1`. Both `initState` and
  `initRefState` check `Nat.beq p.mirProfileVersion 1` and return
  `.error .unsupported` on any other profile version, rejecting mismatched
  profile versions fail-closed at audit and verification time; bumping
  `mirProfileVersion` on incompatible capture-profile or target-ABI changes
  remains a human-review obligation coordinating updates across both models.

### 3.2 Canonical Type Interning (`encodeProg` and `decodeProg`)

Because `lean-miri` indexes types via `TyId := Nat`, `Trusted.Correspondence`
provides a pure, total codec between `Program` (with inline `MirTy`) and
`RefProg` (with `TyId` indices into `RefProg.types : List MirTy`):

1. **Unseeded initial type table (`collectProgTypes`):**
   `collectProgTypes p := p.bodies.foldl collectBody []` starts from the empty
   table `[]` and interns each `MirTy` in first-occurrence, bottom-up order via
   `insertTy`. Consequently, no `TyId` in `RefProg.types` has a fixed
   cross-program meaning: `RefProg.types` contains only types that appear
   syntactically in `p`, while `ExecutionMachine` built-in layout queries
   (`boolLayout`, `usizeLayout`, `unitLayout`, and enum discriminant layouts)
   resolve through `tyIdFor` / `auxTyCode` (`resolveTy` dispatches indices
   `< types.length` into `types` and synthetic codes `≥ types.length` to
   built-in primitive types without mutating `RefProg.types`).
2. **Recursive bottom-up sub-type interning (`collectTy`):**
   `collectTy` traverses every `MirTy` appearing in `Body.locals`,
   `ConstOperand.ty`, and `ProjectionElem.field`, recursively interning child
   types (`pointee` in `.ref`/`.rawPtr` and `fields` in `.tuple`) via
   `insertTy` before interning the enclosing composite type.
3. **Stateless-per-table encoding and decoding:**
   Once `collectProgTypes p` constructs the program's `types : List MirTy`
   table, `encodeProg p` replaces each `ty : MirTy` with `lookupTyId types ty`,
   and `decodeProg rp` resolves each `id : TyId` back to `rp.types[id]?`
   (returning `none` if any `TyId` is out of bounds). Both directions copy
   `entryDefId`, `pointerWidthBits`, `mirProfileVersion`, and `scope` (and
   each body's `argumentCount`, `isUnsafe`, and `identity`) unchanged, so the
   reference machine checks the exact target width and semantic profile version
   that the capture recorded.

### 3.3 Unconditional Anti-Laundering Guarantees

`Anneal.MirCorrespondence.Codec` proves the `*_base` codec lemmas and
`Anneal.MirCorrespondenceProof` exports the six canonical theorems below, each
locked by `TrustedBoundary.lean` (`verifyCorrespondenceClaims`) against its
exact `*Claim` constant in `Trusted.Correspondence`
(`DecodeProgEncodeProgClaim`, `EncodeProgTypesCanonicalClaim`,
`EncodeStmtNoDormantNoopsClaim`, `EncodeRvalueBinaryOpIffClaim`,
`EncodeRvalueUnaryOpIffClaim`, and `EncodeStmtAssignIffClaim`):

1. **Exact round-trip (`decodeProg_encodeProg`):**
   ```lean
   theorem decodeProg_encodeProg (p : Program) :
       decodeProg (encodeProg p) = some p
   ```
   Every `p : Program` round-trips through `encodeProg` and `decodeProg` with
   zero well-formedness preconditions. `encodeProg` is therefore injective and
   cannot collapse distinct `Program`s onto the same `RefProg`.
2. **Canonical type deduplication (`encodeProg_types_canonical`):**
   ```lean
   theorem encodeProg_types_canonical (p : Program) :
       typesAreCanonical (encodeProg p).types = true
   ```
   Every `MirTy` in `(encodeProg p).types` appears at a unique `TyId`. As a
   result, nominal `TyId` equality inside `lean-miri` (`assertSameType` in
   binary operations and `assertRvalueLayout` in assignments) is equivalent to
   structural `MirTy` equality in $M_{\text{anneal}}$.
3. **No dormant no-op laundering (`encodeStmt_no_dormant_noops`):**
   `encodeStmt` maps a statement to `RefStatementKind.nop` if and only if the
   source statement is `StatementKind.nop` (`encodeStmt ts s = .nop ↔ s =
   .nop`), ensuring that `encodeProg` never silences an active or unsupported
   MIR statement by turning it into a no-op.
4. **Operator, operand-order, and assignment preservation
   (`encodeRvalue_binaryOp_iff`, `encodeRvalue_unaryOp_iff`, and
   `encodeStmt_assign_iff`):**
   `encodeRvalue ts rv` is `RefRvalue.binaryOp op l' r'` if and only if `rv` is
   `Rvalue.binaryOp op l r` with the same operator `op`,
   `encodeOperand ts l = l'`, and `encodeOperand ts r = r'`, so the encoder
   neither changes the operator nor swaps the operands. The same holds for
   `RefRvalue.unaryOp` and for `RefStatementKind.assign` (with
   `encodePlace ts dst` and `encodeRvalue ts rv`). The remaining encoder arms
   (`encodePlace`, `encodeOperand`, `encodeTerminator`, `encodeBasicBlock`, and
   `encodeBody`) are one-line structural maps that copy their constructor and
   fields, which the human audit of `Trusted.Correspondence` checks directly.

Guarantees 1–3 alone would not rule out semantic permutation: an encoder that
exchanged `.add` and `.addUnchecked`, reversed `(lhs, rhs)` on `.sub`/`.div`, or
exchanged `.storageLive` and `.storageDead`, paired with a decoder that reversed
the permutation, would still satisfy round-trip (`decodeProg (encodeProg p) =
some p`). Guarantee 4 rules out operator, operand-order, and assignment
permutations by theorem, and the audited one-line encoder arms rule out the
rest.

Two further checks pin the meaning of the shared operators. Inside
`Trusted.Correspondence`, the reference machine maps each `BinOp` and `UnOp` to
its `lean-miri` counterpart through the audited tables `toMiriBinOp` and
`toMiriUnOp` (Section 1.3). The canary
`canary_negative_ub_add_unchecked_overflow_u32` (Section 5.4) evaluates an
unchecked `u32` addition whose mathematical sum exceeds `u32::MAX` and proves
that it reaches `.fault .undefined`, whereas wrapping `.add` on the same
operands wraps modulo $2^{32}$. Because `FaultEquivalenceClaim` transfers that
fault to `.ub` in $M_{\text{ref}}$, an encoder or operator table that mapped
`.addUnchecked` to wrapping addition, or an $M_{\text{anneal}}$ rule that
wrapped instead of faulting, would fail CI.

---

## 4. Anneal Operational Semantics (`Trusted.MirSemantics`)

### 4.1 Shared Boundary Value Domain

`Trusted.MirSemantics` and `Trusted.Correspondence` share the exact same
boundary value types (`ScalarVal`, `PtrVal`, `AllocByte`, `Val`, `Allocation`,
`CallerMemory`, `Query`, `Out`, and `TerminalOut`):

```lean
structure ScalarVal where
  width : IntWidth
  signed : Bool
  bits : BitVec 128

inductive OrderingVal where
  | less
  | equal
  | greater

inductive Val where
  | scalar (v : ScalarVal)
  | ptr (p : PtrVal)
  | bool (b : Bool)
  | char (c : Char)
  | ordering (ord : OrderingVal)
  | unit
  | enumVal (ty : EnumTy) (variant : Nat)
  | tuple (fields : List Val)
  | bytes (data : List AllocByte)

structure Query where
  args : List Val
  callerMem : CallerMemory := ⟨[]⟩

structure Out where
  ret : Val
  callerMem : CallerMemory := ⟨[]⟩

inductive TerminalOut where
  | returned (out : Out)
  | unwound (callerMem : CallerMemory := ⟨[]⟩)
```

In Day 1 / Phase 1, unwinding is disabled (outside the supported domain), so
every unwinding transition maps to `FaultKind.unsupported` / `.blocked` and
`TerminalOut.unwound` is never produced by either machine; when a future phase
enables unwinding, `TerminalOut.unwound` must also carry the canonical unwind
payload alongside `callerMem` so corresponding unwind outcomes preserve both
the payload and caller-visible memory.

Sharing `Query` and `TerminalOut` across both $M_{\text{anneal}}$ and
$M_{\text{ref}}$ eliminates any external input conversion or output projection
function $\pi : \text{Out}_{\text{anneal}} \to \text{Out}_{\text{ref}}$ from the
correspondence theorem statement, preventing a constant or lossy projection from
hiding disagreements in return values or memory state. Inside
`Trusted.Correspondence`, `initRefState` and `evalRefStep` bridge boundary
`Val`s (`Val.scalar ⟨w, s, bits⟩`, `Val.bool b`, `Val.char c`,
`Val.ordering ord`, `Val.unit`, `Val.enumVal ety v`, and overflow-pair
`Val.tuple [.scalar sv, .bool b]`) to and from `lean-miri`'s `Immediate` and
`MemoryState` representations: `checkRefVal` validates entry arguments with
`ScalarInt.tryFromUInt bits (toMiriSize w)` (rejecting any out-of-width bit
pattern rather than truncating) alongside Unicode scalar / ordering /
overflow-pair checks, `evalRefConstLit` decodes constants with
`ScalarInt.tryFromUInt`, `ScalarInt.tryToBool`, `ScalarInt.toChar`, and
`Discriminant.readDiscriminant`, `ExecutionMachine.scalarHooks` invokes
`Miri.Interpreter.ScalarOps.{binary,unary}`
(`IntegerOps.{binary,binaryBool,binaryChar,unary}`) directly on `Immediate`
operands, and `ExecutionMachine.castHooks` drives `Miri.Interpreter.Cast.cast`
(`Miri.Interpreter.IntegerCast.cast` for `CastKind.intToInt`).
`Anneal.MirCorrespondence.{ScalarEquiv,EnumEquiv,RvalueStep}` prove
unconditional agreement lemmas between these Miri operations and
$M_{\text{anneal}}$ (`checkRefVal_eq`, `checkRefArgsMatch_eq`,
`evalRefConstLit_eq`, `evalRefBinOp_eq`, `evalRefUnOp_eq`,
`scalarOps_binary_ref_eq`, `scalarOps_unary_ref_eq`,
`integerCast_u128_to_{int,char}`, `cast_intToInt_local_eq`, and
`match_tryFromUInt_eq`, which shows that a validated `ScalarInt` preserves
`sc.data = bits` with zero truncation or signedness mutation).

### 4.2 Factored Entry Initialization and Small-Step State Machine

Rather than embedding a synthetic `.entry q` state inside the running state type
(which would introduce a 1-step stuttering offset relative to `initRefState`),
`Trusted.MirSemantics` factors entry validation (`initState`) from the running
state machine (`State` and `evalStep`):

```lean
inductive LocalSlot where
  | dead
  | immediate (val : Option Val)
  | indirect (place : MemPlace)

structure FrameState where
  defId : DefId
  blockIdx : BasicBlockId
  stmtIdx : Nat
  locals : List LocalSlot

structure State where
  frames : List FrameState
  callerMem : CallerMemory := ⟨[]⟩
  mem : MemoryState
```

`LocalSlot` mirrors `rustc`'s `LocalValue` / `Operand` and
`Miri.Interpreter.LocalValue` one constructor to one constructor; Section 4.6
describes the byte-level `MemoryState` behind `.indirect` slots.

At function entry, `initState : Program → Query → Except FaultKind State`
checks that:

1. `p.pointerWidthBits` is `64` and `p.mirProfileVersion` is `1` (any other
   target width or semantic profile version returns `.error .unsupported`; see
   Section 3.1).
2. `q.callerMem.allocations` is empty on Day 1 (non-empty initial caller memory
   returns `.error .unsupported`).
3. `p.bodies[p.entryDefId]?` exists, has at least one basic block, satisfies
   `body.argumentCount < body.locals.length`, has all `.storageLive` and
   `.storageDead` indices in bounds (`< body.locals.length`, matching
   `CallMachine.alwaysLiveVarsAndTemps`), and declares only supported local
   types (`bool`, integers, `()`, `!`, and admitted fieldless enums).
4. `q.args` has length `body.argumentCount` and each argument `v` satisfies
   `v.ty? = some paramTy` (including `ScalarVal.wf`: `v.bits.toNat <
   2 ^ v.width.bitWidth`).

`initRefState` applies the same checks to `encodeProg p` and fails with the
same `.error .unsupported`, so the two machines reject exactly the same entry
inputs.

When validation succeeds, `initState` constructs the initial `FrameState` at
`blockIdx := 0, stmtIdx := 0`:

- Return place `_0` is initialized to `liveUninitSlot body.locals[0]`.
- Argument locals `1 .. body.argumentCount` are initialized to `.immediate
  (some q.args[idx - 1])`.
- Non-argument locals (`idx > body.argumentCount`) start as `.dead` if any
  basic block in `body` contains a `.storageLive idx` or `.storageDead idx`
  statement, and start as `liveUninitSlot body.locals[idx]` otherwise.
- The memory is `entryMemory`: no allocations, with allocation id `1` reserved
  for the caller-owned return place that `lean-miri`'s `callMain` allocates.

### 4.3 Three-Pole Outcome Partition, Well-Formedness, and Behavior

Each step of `evalStep : Program → Choice → State → StepResult State
TerminalOut` returns one of four outcomes (spanning progress, termination,
UB, and unsupported constructs):

- `.step next`: execution advances to `next : State`.
- `.done out`: execution terminates normally with `out : TerminalOut`.
- `.fault .undefined`: execution triggers modeled Rust Undefined Behavior.
- `.fault .unsupported`: execution reaches an unmodeled MIR construct or state.

Over `initState` and `evalStep`, `Trusted.MirSemantics` defines reachability,
all-prefix well-formedness, and observable behavior:

```lean
def Step (p : Program) (s : State)
    (res : StepResult State TerminalOut) : Prop :=
  ∃ c : Choice, ValidChoice p s c ∧ evalStep p c s = res

inductive Reaches (p : Program) : State → State → Prop where
  | refl (s : State) : Reaches p s s
  | tail : Reaches p s₁ s₂ → Step p s₂ (.step s₃) →
      Reaches p s₁ s₃

def ReachesResult (p : Program) (q : Query)
    (res : StepResult State TerminalOut) : Prop :=
  match initState p q with
  | .error k => res = .fault k
  | .ok s₀ => ∃ s : State, Reaches p s₀ s ∧ Step p s res

def WellFormed (p : Program) (q : Query) : Prop :=
  (∃ s₀ : State, initState p q = .ok s₀ ∧
    ∀ s : State, Reaches p s₀ s →
      ∃ c : Choice, ValidChoice p s c) ∧
  (∀ k : FaultKind, ¬ ReachesResult p q (.fault k))

def Behavior (p : Program) (q : Query) (out : TerminalOut) : Prop :=
  ReachesResult p q (.done out)

def Diverges (p : Program) (q : Query) : Prop :=
  ∃ s₀ : State, initState p q = .ok s₀ ∧
    ∃ trace : Nat → State,
      trace 0 = s₀ ∧ ∀ n : Nat, Step p (trace n) (.step (trace (n + 1)))

def SatisfiesPost (p : Program) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  WellFormed p q ∧ ∀ out : TerminalOut, Behavior p q out → post out
```

`WellFormed p q` requires both that `initState p q` succeeds and every
reachable state has at least one admissible choice
(`∃ c, ValidChoice p s c`, preventing a vacuous choice predicate from making
`WellFormed` hold on a stuck machine) and that no reachable transition faults
with either `.undefined` or `.unsupported`.

`Diverges p q` states that entry succeeds (`initState p q = .ok s₀`) and that
there exists a single coherent infinite execution trace `trace : Nat → State`
starting at `trace 0 = s₀` in which every state `trace n` steps to
`trace (n + 1)`. Defining divergence via a single state stream `trace : Nat →
State` (rather than `∀ n, ∃ s, ReachesN p n s₀ s`) ensures that even when
`ValidChoice` admits infinitely many nondeterministic branches (such as
allocator address choices), an infinitely branching tree of finite-only paths is
not misclassified as divergent. Termination versus divergence is observable
behavior under
[`docs/mir-correspondence-strategy.md`](mir-correspondence-strategy.md), and
Section 5.2 relates `Diverges` to its reference counterpart in both
directions. `SatisfiesPost` is a partial-correctness contract: it constrains
every terminal behavior but does not by itself require termination, so a
specification that must also rule out divergence can add `¬ Diverges p q`.

### 4.4 Core Operational Rules Matching `lean-miri`

To maintain a 1-to-1 step correspondence with `lean-miri` across all inputs
(both well-formed executions and faulting executions), `Trusted.MirSemantics`
aligns its operational checks with `lean-miri`'s evaluation order:

1. **Zero-sized initialization (`liveUninitSlot`):**
   ```lean
   def liveUninitSlot : MirTy → LocalSlot
     | .unit => .immediate (some .unit)
     | .enum ety =>
       if isZstEnumTy ety then .immediate (some (.enumVal ety 0))
       else .immediate none
     | _ => .immediate none
   ```
   In `lean-miri`, a 0-byte zero-sized type (`Size.ZERO`) has `.immediate
   .uninit` as its unique valid representation. Defining `liveUninitSlot .unit =
   .immediate (some .unit)` (and likewise for an admitted one-variant zero-sized
   enum) ensures that `fn empty() { return }` (which returns `_0 :
   ()` without an explicit `_0 = const ()` assignment) succeeds in both
   machines, and that `StorageLive` and `Operand.move` on a zero-sized local
   preserve state correspondence.
2. **Two-stage operand evaluation and move threading (`evalOperandToSlot` and
   `evalPrimitiveOperand`):**
   - **Stage 1 (`evalOperandToSlot`):** Resolves an `Operand` to `(ty : MirTy,
     optVal : Option Val, locals' : List LocalSlot, mem' : MemoryState)`
     without yet checking whether `optVal` is initialized (`some v`). If the
     operand is `.move place` on a live unprojected `.immediate` local,
     `evalOperandToSlot` updates `locals[place.localId]` to `liveUninitSlot
     ty` and returns the updated `locals'`. For an `.indirect` local (Section
     4.6), it first applies the caller's static type check (`tyOk`:
     `isPrimitiveReadableTy` for Stage 2A, `srcTy = dstTy` for Stage 2B) and
     only then reads the bytes (`loadIndirect`) and, for `.move`,
     deinitializes them (`deinitIndirect`), matching `lean-miri`, whose
     consumers check the type before touching memory.
   - **Stage 2A (`evalPrimitiveOperand`):** Used by `Rvalue.binaryOp`,
     `Rvalue.unaryOp`, and `TerminatorKind.switchInt`. Checks
     `isPrimitiveReadableTy ty` (`.bool`, `.int w s`, `.char`, or overflow pairs
     `.tuple [.int w s, .bool]`) *before* checking whether `optVal` is
     `some v`, matching `MemoryOperand.readImmediate` (which checks
     `BackendRepr.Scalar` / `BackendRepr.ScalarPair` on the static layout
     before inspecting the runtime `Immediate` for `.uninit`).
   - **Stage 2B (`Rvalue.use` inside `evalRvalue`):** Calls `evalOperandToSlot`,
     checks `srcTy = dstTy` first (matching `copyRuntimePlaceNoValidate`), and
     then checks `optVal = some v` (matching `h.validate`).
   - **Stage 2C (`Rvalue.cast .intToInt` inside `evalRvalue`):** Calls
     `evalOperandToSlot ... isIntLikeTy`, checks `isIntLikeTy srcTy` (`.bool`,
     `.int _ _`, or `.char`) first (matching `enforceValidity`'s `typeInfo`),
     then checks `optVal = some v` (matching `readImmediate` `.uninit` UB), and
     finally applies `evalIntToIntCast` (`intLikeBits` + target width
     truncation or `u8`-range `≤ 255` check for `.char`, matching `Cast.cast` /
     `IntegerCast.cast`), with `castTypesValid` enforcing `dstTy = castTy`
     statically on unprojected assignments.
   - In $M_{\text{ref}}$, the corresponding unified pipeline is
     `Miri.Interpreter.OperandMachine.evalOperand` (Stage 1) and
     `Miri.Interpreter.PlaceMachine.readImmediate` /
     `Miri.Interpreter.Place.copyRuntimePlace` (Stage 2A/2B), driven directly
     by `Miri.Interpreter.ExecutionMachine.step` (Section 2.5).
3. **Assignment evaluation order (`StatementKind.assign`):**
   `evalStatement` checks that `dst.projection` is empty and looks up `dstTy :=
   body.locals[dst.localId]?` first, then evaluates `evalRvalue` (producing
   `(val, localsAfterRval, memAfterRval)` with any source `.move`
   deinitializations applied), and finally calls `writePlace localsAfterRval
   memAfterRval dst.localId dstTy val` (which checks `checkVal val dstTy` and
   verifies that `dst` is not `.dead`). Because
   `writePlace` runs after `evalRvalue`, self-moves (`_1 = move _1`) first
   deinitialize `_1` during `evalRvalue` and then write the extracted value back
   into `_1`.
4. **Six-width integer, `bool`, `char`, `Ordering`, and overflow-pair
   operations (`evalBinOp`, `evalUnOp`, `evalIntToIntCast`):**
   - Non-shift integer binary operators require matching width and signedness
     (`l.width = r.width ∧ l.signed = r.signed`), faulting with `.unsupported`
     on mismatched types.
   - Wrapping `.add`, `.sub`, and `.mul` wrap modulo $2^{\text{bitWidth}}$;
     `.addUnchecked`, `.subUnchecked`, and `.mulUnchecked` fault with
     `.undefined` when the mathematical result falls outside the target signed
     or unsigned range; `.addWithOverflow`, `.subWithOverflow`, and
     `.mulWithOverflow` return `.tuple [.scalar wrapped, .bool overflowed]` of
     overflow-pair type `.tuple [.int w s, .bool]`.
   - `.cmp` compares equal-typed integers (signed or unsigned) and `char`
     values, returning `.ordering` (`OrderingVal.{less,equal,greater}`, `i8`
     tags `255 / 0 / 1` read via `Rvalue.discriminant`); `.cmp` on `bool`
     faults with `.unsupported`.
   - `.div` and `.rem` fault with `.undefined` on division/remainder by zero and
     on signed `INT_MIN / -1` and `INT_MIN % -1`.
   - Shift operators (`.shl`, `.shr`, `.shlUnchecked`, `.shrUnchecked`) accept
     any integer RHS width and signedness, mask the shift amount modulo
     `l.width.bitWidth`, perform arithmetic right shift on signed `l`, and fault
     with `.undefined` on `.shlUnchecked`/`.shrUnchecked` when `r.toInt < 0` or
     `r.toInt ≥ l.width.bitWidth`.
   - `char` comparisons (`Eq..Ge` and `Cmp`) compare Unicode scalar values; all
     unary operators on `.char` fault with `.unsupported`.
   - `UnOp.not` complements booleans and bitwise-inverts integers; `UnOp.neg`
     wraps signed integers (`-INT_MIN == INT_MIN`) and faults with
     `.unsupported` on unsigned integers or booleans.
   - `evalIntToIntCast` sign-extends signed sources, zero-extends unsigned
     sources, and maps `bool` / `char` to `128`-bit integers, truncating to
     integer targets or converting `≤ 255` values to `char` (`.unsupported`
     for larger values or non-int/non-char targets).
5. **Terminator evaluation and block-bounds checking (`evalTerminator`):**
   - `.goto target` and `.switchInt discr targets` update `frame.blockIdx :=
     target, stmtIdx := 0` (with `.switchInt` also storing the post-discriminant
     `localsAfterDiscr` into the frame). `evalCharSwitchBranches` checks each
     case bit pattern via `evalConstLit .char`, faulting `.unsupported` above 4
     bytes or `.undefined` on non-Unicode-scalar cases; overflow-pair
     discriminants succeed only on empty branch lists (`otherwise`). Target
     basic-block existence is checked once at the start of the next step in
     `evalStep` (faulting with `.unsupported` if
     `body.basicBlocks[frame.blockIdx]? = none`), matching
     `ControlFlow.goToBlock` and `Step.step` in `lean-miri`.
   - `.return_` faults with `.unsupported` if `bb.cleanup` is `true`, returns
     `.done (.returned ⟨retVal, callerMem⟩)` if `_0` holds `retVal`
     (`.immediate (some retVal)`, or an `.indirect` place whose bytes decode to
     `retVal`), and faults with `.undefined` if `_0` is `.dead` or
     uninitialized.
   - `.unreachable` faults with `.undefined`.

### 4.5 Multi-Body Program, Crate, and Proof-Unit Verification Judgments

To ensure that per-crate verification demonstrably covers **every** captured
body (whether or not a user wrote an explicit specification for it), enforces
distinct body identities, enforces structural admission unconditionally even on
uninhabited-parameter bodies, and fails closed on `.crate` vs. `.unit` scope
mismatches, `Trusted.MirAst` defines `VerificationScope` (with `Body` carrying
`isUnsafe : Bool := false` and `identity : String := ""`), and
`Trusted.MirSemantics` defines the exact top-level verification judgments below
(where `isSupportedScalarOrUnitTy` admits Phase 1 scalar integers, `bool`,
`char`, `Ordering`, overflow pairs `.tuple [.int w s, .bool]`, `()`, `!`, and
admitted fieldless enums, and `Trusted` re-exports `Trusted.Crate`,
`Trusted.CrateTheorem`, and `Trusted.UnitTheorem` as top-level `abbrev`s):

```lean
-- In Trusted.MirAst:
inductive VerificationScope where
  | unit
  | crate

-- In Trusted.MirSemantics:
noncomputable def entryProgForBody (p : Program) (defId : DefId) : Program :=
  { p with entryDefId := defId }

noncomputable def ValidEntryArgs (body : Body) (args : List Val) : Prop :=
  checkArgsMatch args ((body.locals.drop 1).take body.argumentCount) = true

noncomputable def bodiesHaveUniqueIdentities (bodies : List Body) : Bool :=
  bodies.all (fun b => !stringBeq b.identity "") &&
    stringListPairwiseNe (bodies.map (fun b => b.identity))

noncomputable def BodyStaticAdmitted (p : Program) (body : Body) : Bool :=
  Nat.beq p.pointerWidthBits 64 &&
    Nat.beq p.mirProfileVersion 1 &&
    !stringBeq body.identity "" &&
    !body.basicBlocks.isEmpty &&
    Nat.blt body.argumentCount body.locals.length &&
    storageAnnotationsInBounds body &&
    body.locals.all isSupportedScalarOrUnitTy

noncomputable def BodyVerified (p : Program) (defId : DefId) (body : Body)
    (safetyPre : List Val → Prop) : Prop :=
  getElem? p.bodies defId = some body ∧
  BodyStaticAdmitted p body = true ∧
  ∀ args : List Val,
    ValidEntryArgs body args →
    (body.isUnsafe = true → safetyPre args) →
    WellFormed (entryProgForBody p defId) { args := args }

structure Specs where
  safety : String → List Val → Prop := fun _ _ => True
  property : Program → Prop := fun _ => True

structure Crate where
  program : Program
  specs : Specs := ⟨fun _ _ => True, fun _ => True⟩

noncomputable def ProgramVerified (p : Program) (specs : Specs) : Prop :=
  Nat.beq p.pointerWidthBits 64 = true ∧
  Nat.beq p.mirProfileVersion 1 = true ∧
  !p.bodies.isEmpty = true ∧
  Nat.blt p.entryDefId p.bodies.length = true ∧
  bodiesHaveUniqueIdentities p.bodies = true ∧
  (∀ (defId : DefId) (body : Body),
    getElem? p.bodies defId = some body →
    BodyVerified p defId body (specs.safety body.identity)) ∧
  specs.property p

noncomputable def CrateTheorem (c : Crate) : Prop :=
  c.program.scope = .crate ∧ ProgramVerified c.program c.specs

noncomputable def UnitTheorem (c : Crate) : Prop :=
  c.program.scope = .unit ∧ ProgramVerified c.program c.specs
```

These definitions pin five properties directly in the trusted theorem surface:

1. **Unconditional coverage of every captured body:** `ProgramVerified`
   quantifies universally over every `(defId, body)` with `getElem? p.bodies
   defId = some body`, never filtering to bodies with user-authored specs.
   `Specs.safety` defaults to `fun _ _ => True` and `BodyVerified` gates
   `safetyPre args` on `body.isUnsafe = true`: every safe function
   (`body.isUnsafe = false`) must be `WellFormed` on all well-typed entry
   arguments regardless of `specs.safety`, and any `unsafe` function without a
   stronger user safety precondition must likewise be `WellFormed` on all
   well-typed entry arguments.
2. **Body-index binding and uninhabited-parameter non-vacuity:** `BodyVerified`
   binds `body` to `getElem? p.bodies defId = some body` (blocking callers from
   passing an unrelated `body` while executing `p.bodies[defId]`) and requires
   `BodyStaticAdmitted p body = true` unconditionally—even when `body` takes an
   uninhabited `!` (`MirTy.never`) parameter so `ValidEntryArgs body args` is
   empty.
3. **Non-emptiness, valid entry, and collision-free identities:**
   `ProgramVerified` enforces `p.pointerWidthBits = 64`, `p.mirProfileVersion =
   1`, `!p.bodies.isEmpty = true`, `p.entryDefId < p.bodies.length`,
   `bodiesHaveUniqueIdentities p.bodies = true` (using pure UTF-8 byte equality
   `stringBeq` and `stringListPairwiseNe` over `foundation-lock.json` so two
   bodies can never alias in `specs.safety` or carry an empty identity), and
   `specs.property p`.
4. **Fail-closed `.crate` vs. `.unit` scope gating and producer obligations:**
   `CrateTheorem` requires `c.program.scope = .crate` and `UnitTheorem`
   requires `c.program.scope = .unit` (`Program.scope` carries no Lean field
   default, so omitting the capture scope is a Lean elaboration/compile-time
   error per Section 3.1, while an explicitly mismatched scope fails the
   selected theorem). In Phase
   1, `BodyVerified` quantifies over value arguments with empty caller memory
   (`callerMem := ⟨[]⟩`), reachable `TerminatorKind.call` steps fail closed as
   `.fault .unsupported`, and `WellFormed` permits divergence unless
   `specs.property` rules it out. External obligations on the capture and driver
   TCB (`anneal-rustc-capture` and `cargo-anneal`) complete the boundary:
   - For `.crate` captures (`CrateTheorem`), `c.program.bodies` must include
     every executable body and reachable callee of the compiled Rust crate.
   - For `.unit` captures (`UnitTheorem`), out-of-scope crate items are omitted
     from `c.program.bodies` by design and MUST be surfaced in the TCB audit
     log so a proof-unit result can never be mistaken for whole-crate
     verification (see [THREAT_MODEL.md](../THREAT_MODEL.md) and
     [architecture.md](./architecture.md)).
   - For both scopes, `Body.isUnsafe` and `Body.identity` must be captured
     faithfully, and generated `specs.safety` maps must return `True` for any
     identity without a stated safety precondition (so an unannotated `unsafe`
     body is not vacuously skipped).
5. **Locked Pass 1 canary (`CanaryCrateAndBodyVerifiedAnnealClaim`):**
   Once fieldless enums, `!`, and crate/unit scope land (bringing Pass 1 from
   the 15 Day-1 baseline canaries to 19, before byte-level memory adds
   `CanaryMemoryLifecycleAnnealClaim` as the 20th), `TrustedBoundary.lean` locks
   `Anneal.MirWp.canary_crate_and_body_verified_anneal` against the exact
   proposition below in `Trusted.MirSemantics`, pairing positive `CrateTheorem`
   and `UnitTheorem` witnesses with 12 constructive negative refutations:

```lean
noncomputable def canarySafeUnitBody : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := false
  identity := "canary::safe_unit"
}

noncomputable def canaryUnsafeGuardedBody (isUnsafeFlag : Bool) : Body := {
  argumentCount := 1
  locals := [u32Ty, .bool]
  basicBlocks := [
    {
      statements := []
      terminator := .switchInt (.copy ⟨1, []⟩) {
        branches := [(BitVec.ofNat 128 1, 1)]
        otherwise := 2
      }
    },
    {
      statements := [
        .assign ⟨0, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩))
      ]
      terminator := .return_
    },
    {
      statements := []
      terminator := .unreachable
    }
  ]
  isUnsafe := isUnsafeFlag
  identity := "canary::unsafe_guarded"
}

noncomputable def canaryNeverParamBody (badStorage : Bool) : Body := {
  argumentCount := 1
  locals := [.unit, .never]
  basicBlocks := [{
    statements := if badStorage then [.storageLive 9] else []
    terminator := .unreachable
  }]
  isUnsafe := false
  identity := "canary::never_param"
}

noncomputable def canaryValidCrate : Crate := {
  program := {
    pointerWidthBits := 64
    mirProfileVersion := 1
    scope := .crate
    bodies := [
      canarySafeUnitBody,
      canaryUnsafeGuardedBody true,
      canaryNeverParamBody false
    ]
  }
  specs := {
    safety := fun id args =>
      if stringBeq id "canary::unsafe_guarded" then
        args = [.bool true]
      else
        False
    property := fun p => Nat.beq p.bodies.length 3 = true
  }
}

noncomputable def CanaryCrateAndBodyVerifiedAnnealClaim : Prop :=
  CrateTheorem canaryValidCrate ∧
  UnitTheorem {
      program := {
        pointerWidthBits := 64
        mirProfileVersion := 1
        scope := .unit
        bodies := [canarySafeUnitBody]
      }
      specs := {
        property := fun p => Nat.beq p.bodies.length 1 = true
      }
    } ∧
  ¬ BodyVerified
      { pointerWidthBits := 64, mirProfileVersion := 1, scope := .unit,
        bodies := [canaryUnsafeGuardedBody false] } 0
      (canaryUnsafeGuardedBody false) (fun _ => False) ∧
  ¬ BodyVerified
      { pointerWidthBits := 64, mirProfileVersion := 1, scope := .unit,
        bodies := [canaryNeverParamBody true] } 0
      (canaryNeverParamBody true) (fun _ => True) ∧
  ¬ BodyVerified
      { pointerWidthBits := 64, mirProfileVersion := 1, scope := .unit,
        bodies := [canarySafeUnitBody, canaryUnsafeGuardedBody false] } 0
      (canaryUnsafeGuardedBody false) (fun _ => True) ∧
  ¬ BodyVerified
      { pointerWidthBits := 64, mirProfileVersion := 1, scope := .unit,
        bodies := [canaryUnsafeGuardedBody false] } 0
      (canaryNeverParamBody false) (fun _ => True) ∧
  ¬ CrateTheorem {
      program := {
        pointerWidthBits := 64
        mirProfileVersion := 1
        scope := .crate
        bodies := []
      }
    } ∧
  ¬ UnitTheorem {
      program := {
        pointerWidthBits := 64
        mirProfileVersion := 1
        scope := .unit
        entryDefId := 5
        bodies := [canarySafeUnitBody]
      }
    } ∧
  ¬ CrateTheorem {
      program := {
        pointerWidthBits := 64
        mirProfileVersion := 1
        scope := .crate
        bodies := [canarySafeUnitBody, canarySafeUnitBody]
      }
    } ∧
  ¬ CrateTheorem {
      program := {
        pointerWidthBits := 64
        mirProfileVersion := 1
        scope := .crate
        bodies := [canarySafeUnitBody, canaryUnsafeGuardedBody false]
      }
    } ∧
  ¬ CrateTheorem {
      program := {
        pointerWidthBits := 64
        mirProfileVersion := 1
        scope := .crate
        bodies := [canarySafeUnitBody]
      }
      specs := {
        property := fun _ => False
      }
    } ∧
  ¬ UnitTheorem {
      program := {
        pointerWidthBits := 64
        mirProfileVersion := 1
        scope := .unit
        bodies := [canarySafeUnitBody]
      }
      specs := {
        property := fun _ => False
      }
    } ∧
  ¬ CrateTheorem {
      program := {
        pointerWidthBits := 64
        mirProfileVersion := 1
        scope := .unit
        bodies := [canarySafeUnitBody]
      }
    } ∧
  ¬ UnitTheorem canaryValidCrate
```

Specifically, the locked canary witnesses: (i) positive `CrateTheorem` on a
3-body crate (safe unit with `safety = False` ignored, `unsafe` guarded body,
and valid `!`-parameter body) and positive `UnitTheorem` on a `.unit` capture;
and constructive refutations of (ii) safe-marked faulty bodies despite
`safetyPre := fun _ => False`, (iii) invalid `!`-parameter bodies via
`BodyStaticAdmitted`, (iv) mismatched `p.bodies[defId]` bindings (including
substituting an admitted `!`-parameter body for a faulty `p.bodies[0]`), (v)
empty `bodies`, out-of-bounds `entryDefId`, and duplicate `identity` keys, (vi)
an unverified second body alongside a valid first body, (vii) false
`specs.property` under both `CrateTheorem` and `UnitTheorem`, and (viii)
`.unit`/`.crate` scope mismatches in both directions.

---

### 4.6 Byte-Level Memory, Layouts, and `forceAllocation` (Option 1A)

$M_{\text{anneal}}$ models memory at the byte level and represents a local
either as an immediate value or as a place in a stack allocation, following
Option 1A of Section 6.1:

- **Type layouts (`Trusted.MirSemantics.Layout`):** `LayoutData` records the
  size and alignment of a sized type, and `layoutOfTy` gives the layouts of the
  Day-1 local types (`bool`, the integers with natural alignment, `()`, `!`,
  and admitted fieldless enums, whose scalar-tagged layout is the tag
  integer's). `TargetEndian` and `profileTargetEndian` fix the byte order of
  MIR profile version 1 to big-endian, matching the data layout that
  $M_{\text{ref}}$ passes to `lean-miri` (`RuntimeTargetDataLayout.default`).
  These are $M_{\text{anneal}}$'s own choices, so they live outside
  `Trusted.MirAst*`, which `verifyRefEvaluatorIndependence` lets the
  reference evaluator import. $M_{\text{ref}}$ chooses alignments
  independently: `RuntimeTargetDataLayout.default` gives `i64` and `i128`
  4-byte alignment, and `Trusted.Correspondence` gives every local layout
  alignment 1 (`Align.ONE`), whereas $M_{\text{anneal}}$ uses natural
  alignment. Profile version 1 has no operation that reinterprets bytes or
  exposes an address, so neither byte order nor alignment can affect any
  `Behavior`.
- **Value representations (`Trusted.MirSemantics.Bytes`):** `encodeUInt` and
  `decodeUInt` follow `rustc`'s `write_target_uint` / `read_target_uint`.
  `encodeVal` stores a Day-1 value as initialized, provenance-free bytes, and
  `decodeVal` decodes bytes back through `evalConstLit`, so constant operands
  and memory reads share the same validity checks; any uninitialized byte of a
  non-zero-sized value decodes to `none`.
- **Memory (`Trusted.MirSemantics.Memory`):** `MemoryState` holds a monotonic
  allocation-id counter and a list of `Allocation`s, each with its own bytes,
  alignment, mutability, and liveness. Allocation ids start at `1` and are
  never reused; `entryMemory` reserves id `1` for the caller-owned return
  place so later stack-allocation ids agree with `lean-miri`'s.
  `allocateStack`, `deallocateStack`, `readBytes`, `writeBytes`, and
  `writeUninit` follow `rustc`'s `allocate`, `deallocate_ptr`, and
  `check_and_deref_ptr` (liveness, bounds, and alignment checks, with
  zero-sized accesses always allowed).
- **Indirect locals:** `LocalSlot.indirect place` reads and writes go through
  `loadIndirect` and `storeIndirect`; `Operand.move` marks an indirect local's
  bytes uninitialized; and `StorageLive` and `StorageDead` deallocate an
  indirect local's allocation (`deallocateLocal`, matching `rustc`'s
  `deallocate_local`).
- **`forceAllocation`:** Moves an immediate local into a fresh stack
  allocation, storing an initialized value without validation, exactly like
  `rustc`'s `force_allocation` and `lean-miri`'s `Place.forceAllocation`.

`rustc` forces an allocation only when a place expression needs the local's
address (projections, references, raw pointers, or in-memory call arguments).
Profile version 1 rejects all of these, so no profile-version-1 step creates an
indirect local in either machine. `CanaryMemoryLifecycleAnnealClaim` therefore
applies `forceAllocation` between steps of concrete programs and pins, by
kernel evaluation, the allocation id, the stored big-endian bytes, the read
back through `.indirect`, the deallocation at `StorageDead` (a later read
through the stale place faults with `.undefined`), a write through an
uninitialized indirect local, the `.undefined` fault on reading uninitialized
indirect bytes, a move out of an indirect local (which deinitializes its
bytes), `StorageLive` deallocating an indirect local, `discriminant` and
`Return` reading indirect locals, and the precedence of static type checks
over memory reads (an ill-typed use of an indirect local whose allocation is
gone faults with `.unsupported`, as in `lean-miri`, rather than `.undefined`).
`BytesCodecMatchesMiriClaim` (Pass 2) first shows that its fresh
`lean-miri` allocation exists and then cross-checks `encodeVal` and
`decodeVal` against `lean-miri`'s
`Allocation.{writeScalar,getBytesUnchecked,readScalar,writeUninit}` for every
integer width and bit pattern.

## 5. Correspondence Theorem, Step Budgets, and Verification Layer

### 5.1 Step-Budget Quantification (`maxSteps`)

In `lean-miri`, `ExecutionMachine.step` executes a single interpreter step (via
`Step.step (stepHooks cfg limits) c`, clearing `pendingMoveDeinit` before and
after the step, where `limits : ExecutionMachine.Limits` bounds internal
recursion budgets for `callDispatch`, `casts`, `retag`, and `validation`). In
`Trusted.Correspondence`, `RefState` carries an explicit outer step budget
(`stepsExecuted` and `maxSteps`) enforced by `evalRefStep`: at the start of
each step it checks `rs.stepsExecuted < rs.maxSteps`, returning
`.exhaustedStepLimit` if the budget is reached and otherwise executing one
statement or terminator through `Miri.Interpreter.Step.step` and incrementing
`stepsExecuted := rs.stepsExecuted + 1`.

To keep `Trusted.Correspondence` maximally auditable without resetting step
counters between transitions, `initRefState` takes `maxSteps : Nat` as an
explicit parameter (`stepsExecuted := 0, maxSteps := maxSteps`), and
`RefReaches` chains `RefStep` transitions completely unmodified:

```lean
inductive RefReaches (rp : RefProg) : RefState → RefState → Prop where
  | refl (rs : RefState) : RefReaches rp rs rs
  | tail : RefReaches rp rs₁ rs₂ →
      RefStep rp rs₂ (.running rs₃) →
      RefReaches rp rs₁ rs₃

def RefReachesOutcome (rp : RefProg) (q : Query) (maxSteps : Nat)
    (out : RefOutcome) : Prop :=
  match initRefState rp q maxSteps with
  | .error k => out = faultToRefOutcome k
  | .ok rs₀ => ∃ rs : RefState, RefReaches rp rs₀ rs ∧ RefStep rp rs out
```

`RefWellFormed`, `RefBehavior`, and `RefDiverges` then quantify over
`maxSteps : Nat` according to their polarity:

```lean
def RefWellFormed (rp : RefProg) (q : Query) : Prop :=
  ∀ maxSteps : Nat,
    (∃ rs₀ : RefState, initRefState rp q maxSteps = .ok rs₀ ∧
      ∀ rs : RefState, RefReaches rp rs₀ rs →
        ∃ c : Choice, ValidRefChoice rp rs c) ∧
    ¬ RefReachesOutcome rp q maxSteps .ub ∧
    ¬ RefReachesOutcome rp q maxSteps .blocked

def RefBehavior (rp : RefProg) (q : Query) (out : TerminalOut) : Prop :=
  ∃ maxSteps : Nat, RefReachesOutcome rp q maxSteps (.returned out)

def RefDiverges (rp : RefProg) (q : Query) : Prop :=
  ∃ rs₀ : RefState, initRefState rp q 0 = .ok rs₀ ∧
    ∃ trace : Nat → RefState,
      trace 0 = rs₀ ∧
      ∀ n : Nat,
        RefStep rp
          { trace n with stepsExecuted := n, maxSteps := n + 1 }
          (.running
            { trace (n + 1) with
              stepsExecuted := n + 1, maxSteps := n + 1 })
```

- In `RefWellFormed rp q`, quantifying universally over `∀ maxSteps : Nat`
  asserts that no finite execution prefix of any length ever reaches `.ub` or
  `.blocked` (treating `.exhaustedStepLimit` as the step-budget horizon rather
  than a program fault).
- In `RefBehavior rp q out`, quantifying existentially over `∃ maxSteps : Nat`
  asserts that there exists a finite step budget large enough (specifically
  `maxSteps := n + 1` for an $n$-step trace in $M_{\text{anneal}}$) for
  `lean-miri` to run from `stepsExecuted = 0` to `.returned out`.
- In `RefDiverges rp q`, a single coherent infinite state stream `trace : Nat →
  RefState` starts at `trace 0 = rs₀` (`initRefState rp q 0 = .ok rs₀`), and at
  every step `n`, `trace n` (with step budget `maxSteps := n + 1` so the step
  limit does not fire at step `n`) transitions via `RefStep` to `trace (n + 1)`.
  Quantifying `∃ trace : Nat → RefState` outside `∀ n : Nat` forces a single
  connected infinite execution path rather than allowing different finite
  branches at different horizons `n`.

### 5.2 Correspondence, Fault-Equivalence, and Move-Deinit Wiring Theorems

`Trusted.Correspondence` states five top-level locked claims: aggregate
correspondence for well-formed programs (`CorrespondenceClaim`), unconditional
bidirectional fault equivalence (`FaultEquivalenceClaim`), choice-coupled
correspondence (`CorrespondenceAtChoicesClaim`), choice-coupled bidirectional
fault equivalence (`FaultEquivalenceAtChoicesClaim`), and the vendored
`ExecutionMachine` move-deinitialization wiring contract
(`MiriMoveDeinitWiringClaim`, covering `ExecutionMachine.step`,
`ExecutionMachine.{withValidation,operandHooks}`, both live
`OperandMachine.evalOperand` and `LocalAccess.evalOperand`, `MachineHooks`, and
`Call.deinitInPlaceArg`). All five top-level claims (together with
`RefStepSoundForAllowedStepClaim`, `BytesCodecMatchesMiriClaim`, the 6 codec
claims, 11 uniqueness and simulation claims, and 11 `D6`–`D16` canary claims—37
locked Pass 2 claims in total) are proved with zero `sorry` in
`Anneal.MirCorrespondenceProof` and enforced by `TrustedBoundary.lean`
(`verifyCorrespondenceClaims`).

```lean
def CorrespondenceClaim : Prop :=
  ∀ (p : Program) (q : Query),
    WellFormed p q →
      RefWellFormed (encodeProg p) q ∧
      (∀ out : TerminalOut,
        Behavior p q out ↔ RefBehavior (encodeProg p) q out) ∧
      (Diverges p q ↔ RefDiverges (encodeProg p) q)

def FaultEquivalenceClaim : Prop :=
  ∀ (p : Program) (q : Query) (k : FaultKind),
    ReachesResult p q (.fault k) ↔
      ∃ maxSteps : Nat,
        RefReachesOutcome (encodeProg p) q maxSteps (faultToRefOutcome k)
```

where `faultToRefOutcome .undefined = .ub` and
`faultToRefOutcome .unsupported = .blocked`, and `MiriMoveDeinitWiringClaim`
in `trusted/correspondence/Trusted/Correspondence.lean` adds the two
`OperandMachine.evalOperand` move-deinitialization conjuncts alongside
`ExecutionMachine.step`, `ExecutionMachine.{withValidation,operandHooks}`,
`LocalAccess.evalOperand`,
`MachineHooks.{recordPendingMoveDeinit,takeLastPendingMoveDeinit}`, and
`FnArg.copyFnArg`/`Call.deinitInPlaceArg`.

On Day 1, both $M_{\text{anneal}}$ and $M_{\text{ref}}$ are deterministic
(`ValidChoice _ _ c := c = 0` and `ValidRefChoice _ _ c := c = 0`), so there is
at most one execution path from `(p, q)` and the unconditional contract below
reduces cleanly to `CorrespondenceClaim` (gated on `WellFormed p q`) plus
unconditional bidirectional fault-reachability equivalence
`FaultEquivalenceClaim`. As Phase 2 introduces nondeterministic choices (such
as base-address allocation draws `c : Choice` along a choice trace
`choices : List Choice`), comparing aggregate behavior sets, existential
divergence predicates, or existential fault sets across unrelated branches—or
gating forward totality on `WellFormed p q`—would allow one machine to permute
outcomes across $c_1$ and $c_2$ or collapse a mixed-faulting input into
all-faulting branches while leaving a gated claim vacuous. Consistent with
[`docs/mir-correspondence-strategy.md`](mir-correspondence-strategy.md) Section
4.6, unconditionally across every `(p, q)` (without gating on `WellFormed p q`),
the combined locked contract requires a faithful choice-coupled execution
relation with (a) unconditional forward totality
($M_{\text{ref}} \to M_{\text{anneal}}$) across **all** valid executions
(faulting and non-faulting), (b) unconditional reverse totality on faulting
executions ($M_{\text{anneal}} \to M_{\text{ref}}$), and (c) optional reverse
totality on non-faulting executions. To enforce unconditional forward totality
across **every** valid execution prefix (not only completed returns,
divergences, or faults), `Trusted.MirSemantics.Boundary` and
`Trusted.Correspondence` define and lock `ValidPrefixAtChoices`,
`RefValidPrefixAtChoices`, `CorrespondenceAtChoicesClaim`, and
`FaultEquivalenceAtChoicesClaim`:

```lean
inductive ReachesAtChoices (p : Program) :
    State → List Choice → State → Prop where
  | nil (s : State) : ReachesAtChoices p s [] s
  | cons {s₁ s₂ s₃ : State} {c : Choice} {cs : List Choice} :
      ValidChoice p s₁ c →
      evalStep p c s₁ = .step s₂ →
      ReachesAtChoices p s₂ cs s₃ →
      ReachesAtChoices p s₁ (c :: cs) s₃

def ValidPrefixAtChoices (p : Program) (q : Query)
    (choices : List Choice) : Prop :=
  ∃ s₀ s : State,
    initState p q = .ok s₀ ∧ ReachesAtChoices p s₀ choices s

inductive RefReachesAtChoices (rp : RefProg) :
    RefState → List Choice → RefState → Prop where
  | nil (rs : RefState) : RefReachesAtChoices rp rs [] rs
  | cons {rs₁ rs₂ rs₃ : RefState} {c : Choice} {cs : List Choice} :
      ValidRefChoice rp rs₁ c →
      evalRefStep rp c rs₁ = .running rs₂ →
      RefReachesAtChoices rp rs₂ cs rs₃ →
      RefReachesAtChoices rp rs₁ (c :: cs) rs₃

def RefValidPrefixAtChoices (rp : RefProg) (q : Query)
    (choices : List Choice) : Prop :=
  ∃ maxSteps : Nat, ∃ rs₀ rs : RefState,
    initRefState rp q maxSteps = .ok rs₀ ∧
    RefReachesAtChoices rp rs₀ choices rs

def CorrespondenceAtChoicesClaim : Prop :=
  ∀ (p : Program) (q : Query),
    (WellFormed p q → RefWellFormed (encodeProg p) q) ∧
    (∀ (choices : List Choice),
      RefValidPrefixAtChoices (encodeProg p) q choices →
        ValidPrefixAtChoices p q choices) ∧
    (∀ (choices : List Choice) (out : TerminalOut),
      RefBehaviorAtChoices (encodeProg p) q choices out →
        BehaviorAtChoices p q choices out) ∧
    (∀ (choiceStream : Nat → Choice),
      RefDivergesAtChoices (encodeProg p) q choiceStream →
        DivergesAtChoices p q choiceStream)

def FaultEquivalenceAtChoicesClaim : Prop :=
  ∀ (p : Program) (q : Query) (choices : List Choice) (k : FaultKind),
    ReachesResultAtChoices p q choices (.fault k) ↔
      ∃ maxSteps : Nat,
        RefReachesOutcomeAtChoices (encodeProg p) q choices maxSteps
          (faultToRefOutcome k)
```

`ValidPrefixAtChoices p q choices` and `RefValidPrefixAtChoices rp q choices`
hold iff `choices` is an admissible finite choice prefix from the initial state
in $M_{\text{anneal}}$ / $M_{\text{ref}}$, including prefixes ending before
termination or faulting and prefixes ending at a dead-end state with no
admissible next choice. Without the explicit `RefValidPrefixAtChoices →
ValidPrefixAtChoices` conjunct, an input with `¬ WellFormed p q` on which
$M_{\text{ref}}$ reaches a valid finite prefix ending at a state with no
admissible next choice would witness none of `RefBehaviorAtChoices`,
`RefDivergesAtChoices`, or `RefReachesOutcomeAtChoices`, allowing all displayed
outcome implications to hold vacuously even if $M_{\text{anneal}}$ had no
coupled execution prefix at all. Using one-way reference-to-Anneal implications
(`RefBehaviorAtChoices → BehaviorAtChoices` and `RefDivergesAtChoices →
DivergesAtChoices`) in `CorrespondenceAtChoicesClaim` keeps reverse totality on
non-faulting executions genuinely optional as specified above, while
`FaultEquivalenceAtChoicesClaim` enforces bidirectional fault equivalence
unconditionally. Under shared exact choice traces where reverse totality also
holds across all valid executions (no non-faulting over-approximation), those
three conjuncts (`ValidPrefixAtChoices`, `BehaviorAtChoices`, and
`DivergesAtChoices`) strengthen directly from `→` to `↔`, coupling every
nondeterministic execution prefix and branch unconditionally across every `(p,
q)` (including mixed-faulting inputs) for prefixes, normal returns, unwinds,
divergence, and fault classifications.

Each conjunct of `CorrespondenceClaim` closes a distinct gap:

- **`RefWellFormed (encodeProg p) q`** transfers UB-freedom: no finite
  execution prefix in $M_{\text{ref}}$ reaches `.ub` or `.blocked`.
- **Forward simulation** (the `→` direction of the behavior equivalence)
  shows that every terminal behavior of $M_{\text{anneal}}$ is one that
  $M_{\text{ref}}$ permits.
- **Backward simulation** (the `←` direction) shows that $M_{\text{ref}}$
  has no terminal behavior that $M_{\text{anneal}}$ lacks. This is the
  direction that sound specification transfer requires: without it, once a
  valid choice (such as an allocation address) can affect a returned value or
  a branch, `SatisfiesPost` could prove a postcondition over
  $M_{\text{anneal}}$'s behaviors while another permitted reference execution
  violates it.
- **Divergence equivalence** (`Diverges p q ↔ RefDiverges (encodeProg p) q`)
  makes termination versus divergence observable. Terminal behaviors and
  faults alone cannot distinguish two machines that agree on every finite
  outcome while only one of them also permits an infinite execution.

### 5.3 One-to-One Simulation Invariant (`SimulationInv`)

Because both $M_{\text{anneal}}$ and $M_{\text{ref}}$ deinitialize moved locals
in lockstep (`liveUninitSlot` / `OperandMachine.evalOperand` with
`deinitMovedPlace := true`) and pre-cache local layouts via `liftLocals`, the
simulation relation `SimulationInv rp p s rs`—defined in
`Trusted.Correspondence.Simulation` so the 11 locked uniqueness and simulation
claims (`StateUniqueOfSimulationInvClaim`,
`RefStateUniqueOfSimulationInvClaim`, `InitRefStateSimClaim`,
`EvalRefStepEqClaim`, `SimOfRefStepClaim`, `SimOfRefReachesClaim`,
`RefWellFormedOfWellFormedClaim`, `RefBehaviorOfBehaviorClaim`,
`BehaviorOfRefBehaviorClaim`, `BehaviorIffRefBehaviorClaim`, and
`DivergesIffRefDivergesClaim`, all checked by `verifyCorrespondenceClaims`) can
name it—pins every semantic field of `s` and the real `ExecutionMachine` state
`rs` (up to `stepsExecuted`, `maxSteps`, and `miri.machine.user.control`):

```lean
def FrameSimInv (rp : RefProg) (p : Program) (f : FrameState)
    (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (rf : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra) : Prop :=
  ∃ (body : Body) (rbody : RefBody),
    MirSemantics.getElem? p.bodies f.defId = some body ∧
    MirSemantics.getElem? rp.bodies f.defId = some rbody ∧
    decodeBody rp.types rbody = some body ∧
    Nat.blt body.argumentCount body.locals.length = true ∧
    storageAnnotationsInBounds body = true ∧
    discriminantTypesValid body = true ∧
    body.locals.all isSupportedScalarOrUnitTy = true ∧
    SlotsMatchTys body.locals f.locals ∧
    FramePcInBounds body f ∧
    rf = mkRefMiriFrame rp.types f.defId rbody f.blockIdx f.stmtIdx
      (liftLocals rp.types body.locals f.locals) retPlace

def SimulationInv (rp : RefProg) (p : Program) (s : State) (rs : RefState) :
    Prop :=
  ∃ (f : FrameState)
    (rf : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (retTy : MirTy)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit),
    decodeProg rp = some p ∧
    s.frames = [f] ∧
    s.mem = entryMemory ∧
    f.defId = p.entryDefId ∧
    entryRetTy? p = some retTy ∧
    rs.retTy = retTy ∧
    refInitMemoryAndRetPlace rp.types retTy = .ok (mem, rs.retPlace) ∧
    RefControlValid ctrl ∧
    rs.miri = mkRefMiriState rf mem ctrl s.callerMem ∧
    FrameSimInv rp p f rs.retPlace rf
```

Memory corresponds one to one: `lean-miri`'s memory holds exactly the
caller-owned return allocation (id `1`), and $M_{\text{anneal}}$'s memory is
`entryMemory` (no allocations, id `1` reserved for the same place).
`slotToMiriLocalValue` lifts every `LocalSlot` constructor to its
`Miri.Interpreter.LocalValue` counterpart (`.indirect place` to
`.live (.indirect (memPlaceToMiri place))`), but `SlotMatchesTy` excludes
`.indirect` slots: no profile-version-1 step creates one in either machine
(Section 4.6), so neither machine allocates, writes, or deallocates memory
before `Return`. The lockstep proof for indirect locals against `lean-miri`'s
`readScalar` / `writeScalar` belongs to the profile that makes them reachable;
`BytesCodecMatchesMiriClaim` already pins the byte codec it will rely on.

`SimulationInv` constrains every semantic field of `s` and `rs` (the single
active `Miri.Interpreter.Frame`, the fresh caller-owned return allocation
`retPlace` in `miri.machine.memory`, disabled borrow/race trackers,
`pendingMoveDeinit = false`, `callerMem`, and `RefControlValid`). Binding
`f.defId = p.entryDefId` in the single-frame Phase 1 model (before multi-frame
`TerminatorKind.call` support generalizes `SimulationInv` to a frame-stack
invariant) guarantees that the executing frame's return place `_0` always has
the entry body's return type `retTy`, matching `rs.retPlace` even on multi-body
programs and keeping `SimulationInv` unique in both directions on related
running states at fixed `(stepsExecuted, maxSteps, control)` (proved in
`Anneal.MirCorrespondence.SimHelpers` and exported in
`Anneal.MirCorrespondenceProof` against `StateUniqueOfSimulationInvClaim` and
`RefStateUniqueOfSimulationInvClaim`):

```lean
theorem state_unique_of_simulationInv
    (h₁ : SimulationInv p s₁ rs) (h₂ : SimulationInv p s₂ rs) :
    s₁ = s₂

theorem refState_unique_of_simulationInv
    (h₁ : SimulationInv p s rs₁) (h₂ : SimulationInv p s rs₂)
    (h_steps : rs₁.stepsExecuted = rs₂.stepsExecuted)
    (h_max : rs₁.maxSteps = rs₂.maxSteps) : rs₁ = rs₂
```

### 5.4 Fuel-Bounded Verification Layer (`Anneal.MirWp`) and Canaries

To let per-function proofs in `theory/` and generated crate obligations
discharge `WellFormed`, `Behavior`, and `SatisfiesPost` by symbolic
computation, `Anneal.MirWp` defines a single fuel-bounded weakest-precondition
recursor (`wpOutcomeState`) over `evalStep`, written directly with `@Nat.rec`
rather than pattern-matching recursion so Lean does not emit compiler-generated
`_unsafe_rec` helpers that `TrustedBoundary.lean` rejects as `partial`:

```lean
def wpOutcomeState (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => False)
    (fun _ ih st =>
      (∃ c₀ : Choice, ValidChoice p st c₀) ∧
      ∀ c : Choice, ValidChoice p st c →
        match evalStep p c st with
        | .step st' => ih st'
        | .done out => onDone out
        | .fault k => onFault k)
    fuel s
```

Instantiating `wpOutcomeState` with `onFault := fun _ => False` yields `wpProg`
(for proving `SatisfiesPost p q post` and
`∃ out, Behavior p q out ∧ post out` via `wellFormed_and_spec_of_wp`), and
instantiating it with `onDone := fun _ => False` and
`onFault := (· = expected)` yields `wpFaultProg` (for proving negative fault
canaries via `reaches_fault_and_exclusive_of_wpFault`). Both core soundness
theorems discharge exact parameterized propositions defined in
`Trusted.MirSemantics`:

```lean
def WpSoundnessClaim
    (wpProgFn : Program → Nat → Query → (TerminalOut → Prop) → Prop) : Prop :=
  ∀ (p : Program) (q : Query) (fuel : Nat) (post : TerminalOut → Prop),
    wpProgFn p fuel q post →
      SatisfiesPost p q post ∧
      ¬ Diverges p q ∧
      ∃ out : TerminalOut, Behavior p q out ∧ post out

def WpFaultSoundnessClaim
    (wpFaultProgFn : Program → Nat → Query → FaultKind → Prop) : Prop :=
  ∀ (p : Program) (q : Query) (fuel : Nat) (expected : FaultKind),
    wpFaultProgFn p fuel q expected →
      ReachesResult p q (.fault expected) ∧
      (∀ k : FaultKind, k ≠ expected →
        ¬ ReachesResult p q (.fault k)) ∧
      (∀ out : TerminalOut, ¬ ReachesResult p q (.done out)) ∧
      ¬ Diverges p q ∧
      ¬ WellFormed p q
```

`Anneal.MirWp` (Pass 1) and `Anneal.MirCorrespondenceProof` (Pass 2) include
kernel-checked non-vacuity and parameter-boundary canary theorems that exercise
all three outcome poles, every supported Day 1 MIR statement, rvalue,
terminator, unary and binary operator, all six integer widths (`i8`, `i16`,
`i32`, `i64`, `i128`, `isize`) in signed and unsigned modes, and runtime move
semantics across both $M_{\text{anneal}}$ and $M_{\text{ref}}$. Each CI
canary's exact `*Claim : Prop` theorem statement **and** every concrete program
(`prog*`), query, and expected-outcome fixture definition it references live on
the human-audited `Trusted.*` surface (`Trusted.MirSemantics` in
`trusted/lean/` and `Trusted.Correspondence` in `trusted/correspondence/`)—
enforced by Statement-Origin Separation in `TrustedBoundary.lean`, which
forbids locked `Trusted.*` theorem types and their transitive constant cones
from referencing any untrusted `Anneal.*` declaration—while only the canary
*proofs* live in untrusted `theory/` (`Anneal.MirWp`) or `correspondence/`
(`Anneal.MirCorrespondenceProof`). `TrustedBoundary.lean`
(`verifyMirWpCoreTheorems` and `verifyCorrespondenceClaims`) verifies that each
exported theorem in `Anneal.MirWp` and `Anneal.MirCorrespondenceProof` has a
type matching the corresponding `Trusted.*Claim` constant—syntactically equal
(`Expr.const claimName []`) for every nullary claim and canary, and direct
application (`Expr.app (.const claimName []) (.const argName [])`) to
`Anneal.MirWp.wpProg` or `Anneal.MirWp.wpFaultProg` for the two parameterized
Pass 1 WP soundness claims. Thus an untrusted edit to `theory/` or
`correspondence/` cannot delete or weaken any nullary correspondence claim,
canary statement, referenced fixture, or expected outcome; for the two
parameterized WP claims, `wpProg` and `wpFaultProg` themselves live in
untrusted `theory/`, so making them vacuous (for instance
`fun _ _ _ _ => False`) would break downstream proofs and canaries without
breaking per-crate soundness, because per-crate verification checks `Trusted.*`
target theorem statements (`CrateTheorem`/`UnitTheorem`) directly in the Lean
kernel.

The Pass 1 canaries in `Anneal.MirWp` (15 in the Day-1 scalar/bool/unit
baseline, growing to 19 once fieldless enums, `!`, and crate/unit scope land,
to 20 with byte-level memory's `canary_memory_lifecycle_anneal`, Section
4.6, and to 25 with `char`, `BinOp.cmp`, `BinOp.*WithOverflow`, and
`CastKind.intToInt`) check $M_{\text{anneal}}$ directly:

- **`canary_positive_add_anneal`:** `_0 = copy _1 + copy _2; return`
  (`30u32 + 12u32`) is `WellFormed` and returns `42u32`.
- **`canary_positive_empty_unit_fn`:** `fn empty() { return }` (`_0 : ()`) is
  `WellFormed` and returns `()`.
- **`canary_positive_stmts_and_cf_anneal`:** Exercises `StatementKind.nop`,
  `StatementKind.storageLive`, `StatementKind.storageDead` (followed by
  re-allocating with `storageLive` and initializing), `TerminatorKind.goto`,
  and `TerminatorKind.switchInt` across both a matched branch arm and the
  `otherwise` fallback arm, proving `WellFormed` and expected return values.
- **`canary_positive_unop_anneal`:** Exercises `UnOp.not` on `bool` (`!true =
  false`, `!false = true`), `UnOp.not` on `u8` (`!0x0fu8 = 0xf0u8`), and
  `UnOp.neg` on signed `i8` (`-42i8` as `214`, and wrapping `-INT_MIN ==
  INT_MIN` on `-128i8`).
- **`canary_positive_all_binops_anneal`:** Exercises every supported `BinOp`
  variant at boundary values: wrapping `.add`, `.sub`, `.mul` on `u8`
  (including overflow wrapping modulo $2^8$), in-bounds `.addUnchecked`,
  `.subUnchecked`, `.mulUnchecked` on `u8`, signed `.div` and `.rem` on `i8`,
  bitwise `.bitXor`, `.bitAnd`, `.bitOr` on `u8` plus `.bitXor` on `bool`,
  shifts `.shl` and `.shr` (including shift amounts $\ge W$ masked modulo $W$
  and arithmetic right shift on negative signed integers), `.shlUnchecked` and
  `.shrUnchecked` at maximum valid shift (`W - 1`), all six comparisons
  (`.eq`, `.ne`, `.lt`, `.le`, `.gt`, `.ge`) on signed `i8`, and `.lt` on
  unsigned `u8` (high-bit distinction) and `bool`.
- **`canary_positive_all_int_widths_anneal`:** Exercises all six `IntWidth`
  variants (`i8`, `i16`, `i32`, `i64`, `i128`, `isize`) in both signed and
  unsigned modes at their respective width boundaries (`MAX` wrapping to `0` on
  unsigned `.add` and `INT_MAX` wrapping to `INT_MIN` on signed `.add`).
- **`canary_negative_ub_div_zero_anneal`:**
  `_0 = copy _1 / const 0u32; return` reaches `.fault .undefined` (not
  `.unsupported`) and is not `WellFormed`.
- **`canary_negative_ub_signed_rem_overflow_i8`:**
  `_0 = copy _1 % copy _2; return` (`-128i8 % -1i8`) reaches
  `.fault .undefined` (not `.unsupported`) and is not `WellFormed`.
- **`canary_negative_ub_add_unchecked_overflow_u32`:** an unchecked `u32`
  addition (`BinOp.addUnchecked`) whose mathematical sum exceeds `u32::MAX`
  reaches `.fault .undefined` (not `.unsupported`) and is not `WellFormed`,
  whereas wrapping `.add` on the same operands wraps modulo $2^{32}$.
- **`canary_negative_ub_shift_unchecked_at_bitwidth_anneal`:**
  `BinOp.shlUnchecked` with shift amount equal to the bit width (`32` on `u32`)
  and `BinOp.shrUnchecked` with a negative signed shift amount (`-1i8`) each
  reach `.fault .undefined` (not `.unsupported`).
- **`canary_negative_ub_storage_dead_read_anneal`:** Reading an in-bounds local
  after `StatementKind.storageDead` reaches `.fault .undefined` (not
  `.unsupported`).
- **`canary_negative_ub_unreachable_anneal`:** Executing
  `TerminatorKind.unreachable` reaches `.fault .undefined` (not
  `.unsupported`).
- **`canary_negative_unsupported_anneal`,
  `canary_negative_unsupported_unsigned_neg_anneal`, and
  `canary_negative_ub_storage_dead_return_place_anneal`:**
  `StatementKind.unsupported`, `UnOp.neg` on an unsigned integer (`u32`), and
  `StatementKind.storageDead 0` on return place `_0` (matching
  `StackError.cannotMakeReturnPlaceDead` in `Miri/Interpreter/Stack.lean:41,
  266`) reach `.fault .unsupported` (not `.undefined`) and are not
  `WellFormed`. (The locked constant name
  `CanaryNegativeUbStorageDeadReturnPlaceAnnealClaim` /
  `canary_negative_ub_storage_dead_return_place_anneal` retains the `ub` token
  for historical grouping with the storage-lifetime canaries, while its
  proposition explicitly asserts `.fault .unsupported` and rules out
  `.fault .undefined`.)
- **`canary_positive_enum_explicit_repr_anneal`,
  `canary_positive_zst_single_enum_anneal`, and
  `canary_negative_ub_enum_invalid_tag_and_uninit_anneal`:**
  Exercise fieldless enum encoded-tag constant decoding (`#[repr(u8)]` and
  signed `i8` -> `isize`), explicit-width `Rvalue.discriminant`, inhabited
  1-variant zero-sized enums (`EnumTagRepr.zeroSized`, `ConstLit.zeroSized`),
  invalid scalar enum tag UB, and uninitialized enum discriminant read UB.
- **`canary_crate_and_body_verified_anneal`
  (`CanaryCrateAndBodyVerifiedAnnealClaim`, Section 4.5):**
  Exercises `CrateTheorem` and `UnitTheorem` positively and constructively
  refutes `BodyVerified`, `CrateTheorem`, and `UnitTheorem` on safe-marked
  faulty bodies, invalid uninhabited-`!` bodies (`BodyStaticAdmitted`),
  mismatched `p.bodies[defId]` bindings, empty `bodies`, out-of-bounds
  `entryDefId`, duplicate `identity` keys, an unverified second body, false
  `specs.property`, and `.unit`/`.crate` scope mismatches.
- **`canary_positive_char_and_cmp_anneal` and
  `canary_negative_char_and_cmp_anneal`:** `char` comparisons compare Unicode
  scalar values; `BinOp.cmp` returns `core::cmp::Ordering` (`Val.ordering`)
  on `char` and on signed and unsigned integers (`-1i8.cmp(1i8)` is `Less`
  although its bits `255` exceed `1`); `Rvalue.discriminant` of `Less` is
  `-1i8`; and `switchInt` on a `char` takes the matching case or falls
  through. A surrogate `char` constant (`0xD800`) and a surrogate `char`
  switch case reach `.fault .undefined`, while `BinOp.cmp` on `bool` (as in
  `IntegerOps.binaryBool`) and `UnOp.not` on `char` reach `.fault
  .unsupported`.
- **`canary_positive_overflow_ops_anneal`:**
  `BinOp.{addWithOverflow,subWithOverflow,mulWithOverflow}` return the wrapped
  result and overflow flag as a `(T, bool)` tuple on `u8`, `i8`, `u32`, and
  `i128` (including signed `i128` multiplication overflow).
- **`canary_positive_int_to_int_cast_anneal` and
  `canary_negative_int_to_int_cast_anneal`:** `CastKind.intToInt` sign-extends
  signed sources, zero-extends unsigned sources, truncates to the target width,
  converts `bool` and `char` to integers, and converts `u8` to `char`; casting
  any other integer value to `char` (`300u32`, or `-1i8` whose sign-extended
  intermediate exceeds `255`) or casting to `bool` reaches `.fault
  .unsupported`, and casting an uninitialized local reaches `.fault
  .undefined`.

The Pass 2 canaries in `Anneal.MirCorrespondenceProof` check both models:

- **`canary_D6_use_after_move_ub`:** `_2 = move _1; _0 = copy _1; return`
  reaches `.fault .undefined` and `.ub` in $M_{\text{ref}}$.
- **`canary_D7a_binop_copy_then_move_ok`:** `_0 = copy _1 + move _1; return`
  (`42u32`) is `WellFormed` and `RefWellFormed` and returns `84u32` in both.
- **`canary_D7b_binop_move_then_copy_ub`:** `_0 = move _1 + copy _1; return`
  reaches `.fault .undefined` and `.ub` in $M_{\text{ref}}$.
- **`canary_D7c_binop_move_then_move_ub`:** `_0 = move _1 + move _1; return`
  reaches `.fault .undefined` and `.ub` in $M_{\text{ref}}$.
- **`canary_D8_self_move_ok`:** `_1 = move _1; _0 = copy _1; return`
  (`42u32`) is `WellFormed` and `RefWellFormed` and returns `42u32` in both.
- **`canary_D9_move_unit_zst_ok`:** `_2 = move _1; _0 = copy _1; return`
  (`_1 : ()`) is `WellFormed` and `RefWellFormed` and returns `()` in both.
- **`canary_D10_add_unchecked_overflow_ub`:** on `(u32::MAX, 1)`,
  `_0 = AddUnchecked(_1, _2)` reaches `.fault .undefined` in $M_{\text{anneal}}$
  and `.ub` in $M_{\text{ref}}$, while wrapping `_0 = Add(_1, _2)` returns `0`
  in both.
- **`canary_D11_enum_discriminant_and_const_ok`,
  `canary_D12_zst_enum_move_and_discr_ok`, and
  `canary_D13_enum_invalid_tag_and_uninit_ub`:**
  Verify agreement between $M_{\text{anneal}}$ and $M_{\text{ref}}$
  (`Miri.Interpreter.Discriminant`) across explicit-repr and signed-tag
  fieldless enums, 1-variant zero-sized enums, invalid scalar enum tags, and
  uninitialized enum discriminant reads.
- **`canary_D14_char_cmp_and_switch_ok`:** `'b'.cmp('a')` returns
  `Ordering::Greater` (`IntegerOps.binaryChar` in $M_{\text{ref}}$),
  `Rvalue.discriminant` of `(-1i8).cmp(1i8)` returns `-1i8`, and `switchInt`
  on the `char` `'a'` takes its matching case and returns `1u32`, in both
  models.
- **`canary_D15_int_to_int_cast`:** `-1i8 as u32` returns `0xFFFF_FFFF` and
  `200u8 as char` returns `'\u{c8}'` in both models (`Cast.cast` and
  `IntegerCast.cast` in $M_{\text{ref}}$), while `300u32 as char` reaches
  `.fault .unsupported` in $M_{\text{anneal}}$ and `.blocked` in
  $M_{\text{ref}}$.
- **`canary_D16_with_overflow_ok`:** `BinOp.addWithOverflow` on
  `(255u8, 1u8)` returns `(0, true)` and `BinOp.subWithOverflow` on
  `(-128i8, 1i8)` returns `(127, true)` through the return place in both
  models.

---

## 6. Phase 2 Roadmap and Deferred Design Decisions

### 6.1 Crossing the `forceAllocation` Boundary for Aggregates and Pointers

On Day 1, `Rvalue.aggregateTuple`, `Rvalue.ref`, `Rvalue.addressOf`, and
non-empty place projections (`place.projection ≠ []`) step to `.fault
.unsupported` in $M_{\text{anneal}}$ and `.blocked` in $M_{\text{ref}}$.

When Phase 2 adds support for tuples, field projections, and references/raw
pointers, it must address how `lean-miri` represents compound and address-taken
locals (line numbers below refer to pinned upstream commit `c92d1d97`):

- In `lean-miri`, evaluating `Rvalue.Ref` (`Rvalue.lean:80-90`) or
  `Rvalue.RawPtr` (`Rvalue.lean:95-104`, `MIR/Syntax.lean:428-430`) on a local
  held as `LocalValue.live (.immediate imm)` invokes `Place.forceAllocation`
  (`Place.lean:135-160`), which dynamically allocates a fresh `AllocId` in
  `state.machine.memory`, serializes `imm` into bytes, and mutates the local
  slot in `frame.locals` from `.immediate imm` to `.indirect mplace`.
- Furthermore, `Rvalue.Aggregate` (`Rvalue.lean:78`, implemented by
  `writeAggregate` in `Aggregate.lean:42-74` and wired in
  `ExecutionMachine.lean:174-196, 230`) projects each field of the destination
  and writes it via `copyOpNoValidate` (forcing allocation via
  `asMplaceOrMutableLocal` in `Place.lean:165-179` whenever a projected local
  carries a field offset), whereas `ProjectionElem.Field`
  (`Projection.lean:63-90, 132-150`) can project over `.immediate (.scalar ..)`
  or `.immediate .uninit` without allocation only for uninhabited/ZST fields,
  offset-0 equal-size wrappers, or `ScalarPair` components.

Two candidate representations remain open for Phase 2 adjudication:

1. **Option 1A (Mirror `forceAllocation` in $M_{\text{anneal}}$):**
   Equip $M_{\text{anneal}}$'s `LocalSlot` with both immediate values and
   in-memory stack allocations (`LocalSlot.indirect mplace`), allocating a block
   in `Memory` whenever a tuple is constructed or a local's address is taken.
   Option 1A keeps `SimulationInv` a near-identity one-to-one correspondence
   over `LocalSlot` and `Memory`, at the cost of routing tuple accesses in
   `wpProg` proofs through byte-level memory reads and writes.
2. **Option 1B (Pure value trees in $M_{\text{anneal}}$ until address-taken):**
   Keep non-address-taken tuples as pure `Val.tuple` trees inside `LocalSlot` in
   $M_{\text{anneal}}$ (allocating in `Memory` only upon `Rvalue.ref` or
   `Rvalue.addressOf`), while `SimulationInv` relates each pure `Val.tuple`
   local in $M_{\text{anneal}}$ to its `forceAllocation`-backed stack block in
   `lean-miri`'s `Memory` via an explicit disjointness and byte-decoding
   invariant. Option 1B keeps `wpProg` proofs over non-address-taken tuples
   purely structural, at the cost of a relational local-to-memory injection in
   `SimulationInv`.

**Adjudication:** $M_{\text{anneal}}$ adopts Option 1A. `LocalSlot` now has
`.immediate` and `.indirect` constructors, `State` carries a byte-level
`MemoryState`, and `forceAllocation` mirrors `lean-miri`'s (Section 4.6).
Indirect locals stay unreachable until the first Phase 2 PR that enables
`ProjectionElem.field`, `Rvalue.aggregateTuple`, or `Rvalue.ref` /
`Rvalue.addressOf`; that PR must extend `SimulationInv` to `.indirect` slots
and allocated memory (Section 5.3).

### 6.2 Supporting Constructs Unmodeled by `lean-miri`

On Day 1, `anneal_corresponds_to_miri` requires that the reference adapter in
`Trusted.Correspondence` models
every construct that $M_{\text{anneal}}$ models
(`WellFormed p q → RefWellFormed (encodeProg p) q`), ensuring that
`RefWellFormed` cannot vacuously excuse bugs via `.blocked`. This requirement
does not lapse as coverage grows. Supporting a Rust feature (such as a
compiler intrinsic or inline assembly construct) that upstream `lean-miri`
leaves unimplemented means extending the reference model, never exempting the
feature from correspondence while presenting it as correspondence-checked.
Two paths extend the reference model:

1. **Preferred path (implement the `lean-miri` hook):** `lean-miri` already
   routes intrinsics, foreign calls, place projections, and casts through hook
   records (`StepHooks`, `CallHooks`, `PlaceProjectionHooks`, and
   `CastHooks`). Implementing the corresponding hook in the adapters of
   `Trusted.Correspondence` preserves `anneal_corresponds_to_miri` without
   changing its statement.
2. **Fallback path (audited extension or second reference model):** If a
   construct hits a hardcoded `.blocked` branch inside `lean-miri` that cannot
   be routed through a hook, we either extend `vendor/lean-miri/` with
   an audited patch suitable for upstreaming, pinned in `UPSTREAM_PIN.json`
   like the `deinitMovedPlace` patch, or compose a second, explicit reference
   model for that construct inside the correspondence TCB (Section 1.3).
   `CorrespondenceClaim` keeps its statement in either case.

---

## Appendix: Alternatives Considered and Rejected

### A.1 Reference Model and Move-Semantics Alternatives

#### MiniRust as a Standalone Reference Model

We considered formalizing [MiniRust](https://github.com/minirust/minirust) from
scratch as $M_{\text{ref}}$. MiniRust specifies runtime operational semantics
directly (though since `minirust@766d8d619a` it removed destructive loads and
deinitializes only in-place call arguments, not arbitrary `Operand::Move`
places), but it is written in prose and `specr` (a Rust-like pseudocode DSL)
with no existing Lean 4 mechanization. Writing our own Lean 4 port of MiniRust
and proving that $M_{\text{anneal}}$ refines that port would mean comparing two
Anneal-authored models, losing the independent bug-finding value of an external
mechanization.

#### Aeneas / Charon LLBC as a Reference Model

We also considered using Aeneas or Charon's Low-Level Borrow Calculus (LLBC) as
$M_{\text{ref}}$. Aeneas translates safe, borrow-checked MIR into pure Lean 4
functions by *assuming* the input program is free of Undefined Behavior. Because
Anneal's primary goal is to verify `unsafe` Rust code (such as `zerocopy`) by
proving the absence of UB from operational semantics, a reference model that
assumes UB-freedom cannot serve as a ground-truth UB oracle.

#### Hybrid `lean-miri` + Shadow Move Automaton

We evaluated keeping `vendor/lean-miri/` completely unmodified and defining a
hybrid reference model in `Trusted.Correspondence` that runs `lean-miri`'s
`ExecutionMachine.step` in lockstep with a declarative shadow move-tracking
mask (`RefState := MiriInterpState × List Bool`). Under this hybrid design,
every `Operand.move` clears the local's initialization bit in the shadow mask,
every `Operand.copy` or `Operand.move` checks the shadow mask (halting with
`.ub` if the local was previously moved), and every assignment or `StorageLive`
restores the bit.

While this lockstep product works cleanly on Day 1 (~45 lines of Lean for
unprojected scalar locals), it does not scale to Phase 2:

- Partial field moves (`_1.0 = move _2.1`) deinitialize only the byte sub-range
  of field `1` inside `_2`, leaving `_2.0` initialized.
- Raw pointers aliasing a local (`_p = &raw const _1; _2 = move _1; _3 = *_p`)
  observe move deinitialization through memory addresses (`AllocId`, `Offset`)
  rather than syntactic `LocalId`s.
- Copying a partially moved `MaybeUninit<T>` copies the underlying `.uninit`
  bytes in `Memory` without faulting.

Tracking these cases in an external shadow automaton would require duplicating
`lean-miri`'s place-projection, layout-offset, and byte-level memory engine
inside `Trusted.Correspondence`. By contrast, the 10-file `deinitMovedPlace`
patch in [Section 2.4](#24-runtime-move-deinitialization) reuses `lean-miri`'s
existing `evalPlaceToOp` and `writeMemoryNoValidate choice .uninit` machinery
directly.

#### Eager `.indirect` Deinitialization in `evalOperand` vs. `OpTy.deinitOnRead`

When designing the `deinitMovedPlace` patch in `vendor/lean-miri/`, we also
evaluated two alternative ways to handle `Operand.indirect mplace`:

1. **Eager deinitialization inside `evalOperand`:** Deinitializing `mplace`
   immediately inside `OperandMachine.evalOperand` before returning `OpTy`
   fails because `evalOperand` returns `OpTy.indirect mplace` *by address*
   before the consumer (`PlaceMachine.readImmediate` or
   `Place.copyRuntimePlaceNoValidate`) reads the memory bytes. Deinitializing
   `mplace` inside `evalOperand` wipes the source bytes to `.uninit` before the
   consumer reads them, causing valid moves of indirect places to fault with
   `.invalidUninitBytes`.
2. **Adding `deinitOnRead : Bool := false` to `structure OpTy`:** Carrying the
   deferred deinitialization bit as a third field on `OpTy` in `Projection.lean`
   breaks 2-argument anonymous constructor applications (`⟨op, layout⟩`)
   across 174 files in `vendor/lean-miri/Miri/`. Recording
   `pendingMoveDeinit : Bool := false` on `MachineHooks.MachineState` and
   `takePendingMoveDeinit : PlaceM S Bool := pure false` on `PlaceHooks` avoids
   touching `OpTy.mk` while compiling cleanly across the entire 160-module
   `ExecutionMachine` closure.

#### Unmodified `lean-miri` with a Non-Injective `SimulationInv` Carve-Out

We also analyzed leaving `lean-miri` unmodified (so `Operand.move` does not
deinitialize in $M_{\text{ref}}$) while deinitializing moved places in
$M_{\text{anneal}}$ and replacing the trusted one-to-one `SimulationInv` with a
relaxed proof-internal invariant inside `correspondence/` so that a local slot
can be `.immediate none` in $M_{\text{anneal}}$ while remaining
`.immediate (some v)` in $M_{\text{ref}}$.

Mechanizing this approach revealed four structural flaws:

1. **Ghost move sets collapse to arbitrary `.immediate none` slack:**
   Adding an existential ghost set `movedSet : Finset LocalId` inside a
   proof-internal simulation invariant (allowing
   `annealSlot = .immediate none` while `miriSlot = .immediate (some v)` only
   when `id ∈ movedSet`) is logically equivalent (`↔`) to allowing
   `annealSlot = .immediate none` whenever `miriSlot = .immediate (some v)`.
   Because such an invariant is existentially quantified inside the untrusted
   proof, the proof can always instantiate `id ∈ movedSet` as
   `decide (annealSlot = .immediate none ∧ miriSlot ≠ .immediate none)`,
   regardless of whether `id` was deinitialized by `Operand.move` or by a bug.
2. **Blindness to missing move deinitialization in $M_{\text{anneal}}$:**
   Because `anneal_corresponds_to_miri` is gated on `WellFormed p q`, if a bug
   or future refactor in $M_{\text{anneal}}$ forgets to deinitialize on
   `Operand.move`, both $M_{\text{anneal}}$ and unmodified `lean-miri` treat
   `move` as `copy`, and `anneal_corresponds_to_miri` still compiles without
   error.
3. **Blindness to wrong-local deinitialization and reversed operand order:**
   If $M_{\text{anneal}}$ accidentally deinitializes local `j ≠ i` on
   `move _i`, or evaluates `BinOp(lhs, rhs)` right-to-left instead of
   left-to-right, any execution that reads the extra `.immediate none` local
   faults in $M_{\text{anneal}}$—making the premise `WellFormed p q` false and
   vacuously satisfying `anneal_corresponds_to_miri`.
4. **Phase 2 falsification on `MaybeUninit<T>` and padding copies:**
   In Phase 2, copying `MaybeUninit<u8>` (or struct padding bytes) copies
   `.uninit` bytes without faulting (`WellFormed p q` holds). If `_1 :
   MaybeUninit<u8>` holds `init 42`, is moved via `_2 = move _1` (setting `_1`
   to `uninit` in $M_{\text{anneal}}$ while leaving `_1` as `init 42` in
   unmodified `lean-miri`), and is then copied and returned via `_0 = copy _1;
   return`, $M_{\text{anneal}}$ returns `uninit` while unmodified `lean-miri`
   returns `init 42`. On such a program, `WellFormed p q` holds, but `Behavior p
   q out → RefBehavior (encodeProg p) q out` is mathematically false.

### A.2 Type Representation and Codec Alternatives

#### Nominal `TyId` Indirection Inside `Trusted.MirAst`

We considered mirroring `lean-miri`'s `TyId := Nat` index table inside
`Trusted.MirAst` (`Program.types : List MirTy`). We rejected this because a
nominal `TyId` table inside $M_{\text{anneal}}$ introduces two classes of
representation artifacts:

1. Programs can contain out-of-bounds `TyId`s (`tyId ≥ p.types.length`), forcing
   every type lookup in `Trusted.MirSemantics` and `Anneal.MirWp` to handle
   missing-type faults.
2. A program's `types` table can list the same structural `MirTy` (such as
   `u32`) at two distinct indices (`TyId 0` and `TyId 1`). In `lean-miri`,
   `assertSameType` and `assertRvalueLayout` compare nominal `TyId`s
   (`0 ≠ 1`), whereas structural type checks compare `MirTy` values
   (`u32 = u32`), breaking correspondence unless every `Program` carries an
   extra canonical-table well-formedness side condition. Carrying `MirTy` by
   value in `Trusted.MirAst` and deduplicating during `encodeProg` eliminates
   both issues by construction.

#### Pre-Seeded Primitive Type Table

We considered pre-seeding `collectProgTypes` with primitive types such as
`[.unit, .bool, .int .isize false]` at fixed `TyId`s `0`, `1`, and `2` instead
of starting from `[]`. Starting `collectProgTypes` from `[]` keeps
`RefProg.types` minimal and strictly faithful to the types appearing in `p`,
while `tyIdFor` / `auxTyCode` / `resolveTy` cleanly serve `ExecutionMachine`
built-in layout queries (`unitLayout`, `boolLayout`, `usizeLayout`, and
discriminant integer layouts) via out-of-band auxiliary `TyId` codes
`≥ types.length` without polluting `RefProg.types` or breaking
`typesAreCanonical`.

### A.3 State Machine and Step-Budget Alternatives

#### Synthetic `State.entry q` Constructor Inside `State`

We considered including `State.entry (q : Query)` as a constructor of `State` so
that `evalStep p c (.entry q)` performs entry initialization as the first step
of `Reaches`. We rejected this because `Trusted.Correspondence` performs entry
frame construction inside `initRefState` *before* the first call to
`evalRefStep`. Making entry initialization a transition step in
$M_{\text{anneal}}$ created a 1-step stuttering offset on every trace and
prevented `initState` and `initRefState` from corresponding directly.

#### Fixed Constant Step Budget (`maxSteps := K`)

We considered initializing `initRefState` with a fixed large constant step
budget (such as `maxSteps := 2^64`). We rejected this because `Behavior p q out`
in $M_{\text{anneal}}$ is an unbounded finite-step reachability predicate: for
any fixed constant $K$, there exists a terminating loop of length $K + 1$ that
returns `out` in $M_{\text{anneal}}$ but halts with `.exhaustedStepLimit` in
$M_{\text{ref}}$, making `Behavior p q out → RefBehavior (encodeProg p) q out`
unprovable.

#### Resetting `stepsExecuted := 0` Inside `RefStep`

We also considered initializing `maxSteps := 1` and resetting
`stepsExecuted := 0` before each single-step call inside `RefStep`. While
mathematically equivalent to quantifying over `maxSteps : Nat`, resetting
`stepsExecuted` inside `RefStep` mutates the `RefState` returned by
`evalRefStep` between steps. Quantifying over `maxSteps : Nat` in
`RefWellFormed` (`∀ maxSteps`) and `RefBehavior` (`∃ maxSteps`) allows
`RefReaches` to chain the exact states returned by `evalRefStep` without
modification.

### A.4 Local Initialization and Evaluation-Order Alternatives

#### Initializing `MirTy.unit` Locals to `.immediate none`

We considered initializing all non-argument locals (including `_0 : ()`) to
`.immediate none` at function entry and after `.storageLive` or `Operand.move`.
We rejected this because `rustc` emits `fn empty() { return }` without an
explicit `_0 = const ()` assignment, and in `lean-miri`, `.immediate .uninit` is
already the valid runtime representation of the 0-byte unit type `()`.
Initializing `.unit` locals to `.immediate none` caused `fn empty() { return }`
to fault with `.undefined` in $M_{\text{anneal}}$ while succeeding in
`lean-miri`.

#### Single-Stage `evalOperand` Checking Initialization Before Types

We considered a single `evalOperand` function that immediately faults with
`.undefined` whenever a local slot is `.immediate none`, before the caller
checks whether the operand's static type is supported by the enclosing
operation. We rejected this because `lean-miri` evaluates operands in two
stages: `OperandMachine.evalOperand` constructs an `OpTy` (carrying `.immediate
.uninit` together with its static `TyAndLayout`), and the consumer then checks
static type compatibility (`BackendRepr.Scalar` in `readImmediate` or
`src.layout.ty == dest.layout.ty` in `copyRuntimePlaceNoValidate`) *before*
validating that the runtime value is initialized. Splitting operand evaluation
into `evalOperandToSlot` and `evalPrimitiveOperand` / `evalRvalue` matches
`lean-miri`'s exact fault precedence on ill-typed uninitialized locals.
