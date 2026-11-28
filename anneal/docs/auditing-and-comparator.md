<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Auditing Architecture, Universal NDJSON Comparator, and Defense in Depth

> **Status: Target Architecture / In-Progress.**
>
> **Dual target-audit engines (`v4.34.1` and `v4.35.0+`):** `cargo-anneal`
> runs the **Universal NDJSON Comparator** (`5-init`/`5a`/`5b`/`5-pin`/`5c`,
> with `SpecPreflight` serving `"headers"`, `"spec-preflight"`,
> `"resolve-imports"`, `"sysroot-consts"`, and `"target-consts"`) only when
> `--allow-unpinned-lean` is passed and stock Lean `v4.35.0+` comparator
> binaries (`leanexport`, `nanoda_bin`, `con-ron`, plus optional `con-leche`
> and `lean4lean`) exist under `<sysroot>/bin/`. Pinned admission never adopts
> these binaries (no `v4.35.0+` comparator digests are pinned yet), so the
> pinned `v4.34.1` release always uses `loadExts := false`
> `TrustedBoundary.lean` replay. See
> [elaborator containment](elaborator-containment-design.md) and
> [trust model](trust-model.md).

> **Remaining design items:** Phase 3 closed-allowlist `SpecPreflight`
> grammar tightening (`TrapFreeHumanSpecAST`) and offline Pass 2 splitting
> remain tracked across
> [`#4012`](https://github.com/google/zerocopy/issues/4012),
> [`#4096`](https://github.com/google/zerocopy/issues/4096), and
> [`#4099`](https://github.com/google/zerocopy/issues/4099).

Traditional formal verification assumes a good-faith proof author making honest
mistakes against a trusted checker. Autonomous AI coding and proving agents
invert that assumption: an agent optimizing to make verification exit `0` may
probe every seam in the elaborator, artifact format, specification boundary, or
verifier codebase. As defined in [`THREAT_MODEL.md`](../THREAT_MODEL.md),
`Proof/*.lean` is treated as completely untrusted adversarial input and must
never require human review.

To uphold that guarantee without enlarging the human-audited Trusted Computing
Base (TCB), Anneal's target auditing architecture enforces three complementary
layers of defense:

1. **Universal NDJSON Comparator (`5a`/`5b`/`5c`):** Eliminates the Lean
   elaborator, C++ runtime, and `.olean` binary deserializer from the
   verdict-producing process by replaying exported proof terms through
   independent kernels over a canonical NDJSON stream.
2. **`MirSemantics` Guard-Mutation CI (`check_guard_mutation.py`):**
   Continuously verifies that individual undefined-behavior (UB) guards in
   `Trusted/MirSemantics/` and policy guards in the auditor remain active and
   exercised by negative refutation tests.
3. **Non-adversarial `audit-spec` sanity checks (`PreInhabited` and Dual-Polar
   `MutationRefute`):** Helps honest authors and reviewers catch accidental
   specification vacuity or missing bindings—while explicitly leaving
   anti-adversarial specification integrity to human review over golden
   spec closures ([Specification Core v2](spec-core-and-golden-closure.md)).

## 1. Universal NDJSON Comparator (`5a` / `5b` / `5c`)

### Why Anneal retires in-process `.olean` target auditing

A compiled `.olean` file is a binary heap image produced by the Lean elaborator
while processing untrusted `Proof/*.lean` code. Mapping untrusted `.olean`
files directly into the verdict-producing process places the Lean C++ runtime
and binary `.olean` loader inside the proof-checking TCB and couples the final
verdict to the integrity of attacker-influenced binary object graphs.

The Universal NDJSON Comparator enforces a strict **zero-trust artifact
boundary**: no `.olean` produced from untrusted proof code is ever mapped into
the verdict-producing process. Untrusted proofs are elaborated and exported
inside an isolated sandbox, and only a canonical UTF-8 NDJSON declaration
stream crosses the boundary into a small, pure-Rust `#![forbid(unsafe_code)]`
verifier backed by independent stock Lean `v4.35.0+` kernels.

```text
  Trusted/reviewed inputs only               Untrusted proof closure
  {Init, Trusted, Captured, Spec, Expected}  {Init, Trusted, Anneal, Captured,
  (ZERO Anneal.*, ZERO Proof.*)               Spec, Expected, Proof.*}
               │                                           │
               ▼                                           ▼
  ┌─────────────────────────────┐             ┌─────────────────────────────┐
  │ 5a: AnnealExportExpected    │             │ 5b: AnnealExportProof       │
  │   leanexport <trusted mods> │             │   (ExecSeal / isolated RBE) │
  │     -- Expected.claim       │             │   leanexport Proof --       │
  │     + all Spec constants    │             │     Proof.verify            │
  │     + target consts in 5b   │             │   -> proof_full.ndjson      │
  │   -> expected_cone.ndjson   │             └──────────────┬──────────────┘
  └──────────────┬──────────────┘                            │
                 │   ┌──────────────────────────────────┐    │
                 │   │ 5-init: init_primitives_cone     │    │
                 │   │ (39 prims + 3 axioms + Plat)     │    │
                 │   │ 5-pin: sysroot_pins (every       │    │
                 │   │ sysroot-named constant used)     │    │
                 │   │ (clean sysroot, 0 target .olean) │    │
                 │   └────────────────┬─────────────────┘    │
                 ▼                    ▼                      ▼
  ┌─────────────────────────────────────────────────────────────────────────┐
  │ 5c: AnnealVerifyNdjson (pure Rust, #![forbid(unsafe_code)], 0 .olean!)  │
  │   1. Closed exports; canonical DAG identity (`expected_bfs` ⊆ proof)    │
  │   2. Authenticated origin: sysroot names pinned to 5-init/5-pin,        │
  │      target-module constants (target-consts index) pinned to 5a,       │
  │      Trusted/reserved-root isolation for proof-origin constants         │
  │   3. Exact Proof.verify : Expected.claim, zero non-sysroot opaque or    │
  │      partial/unsafe, strict 3-axiom ceiling, specification bans         │
  │   4. Quotient primitive post-check (Quot, Quot.mk, Quot.lift, Quot.ind) │
  │   5. Independent kernel replay: nanoda_bin + con-ron (stock v4.35.0+)   │
  │      [+ optional `--paranoid-quorum`: con-leche + lean4lean --import]   │
  └────────────────────────────────────┬────────────────────────────────────┘
                                       ▼
                        Strict typed Receipt v3 JSON
```

### Exact contract of actions `5a`, `5b`, and `5c`

- **`"target-consts"` (module index):** `SpecPreflight` imports the admitted
  sysroot plus the compiled `Model`, `Capture`, `Specification`, and
  `Expected` `.olean`s (never a `Proof` `.olean`; `loadExts := false`, no
  initializers) and reports each module's exact constant inventory from
  each module's `ModuleData`. Before importing, every target `.olean` passes
  the same pre-import header, companion, and `isModule` validation as the
  legacy `"target-audit"`. It rejects any `unsafe` target constant and any
  non-realized constant that another loaded module also declares, and reports
  the targets' `@[implemented_by]`/`@[extern]`/`@[csimp]` subjects, none of
  which may be reached. Compiler-generated constants (anonymous and
  `deriving` instances, structure constructors/projections, `where`/`let rec`
  auxiliaries, matchers, `private` declarations) are thereby attributed to
  their defining module. Unlike the legacy `"target-audit"`, the comparator
  route does not inspect compiler-override attributes on `Proof`
  declarations (their `.olean`s never load outside the sandboxed exporter;
  such attributes cannot change kernel reduction), and receipts list that and
  the anti-vacuity lint under `deferred`.
- **Action `5a` (`AnnealExportExpected`):** Mounts strictly the trusted and
  reviewed statement closure (`Init.*`, `Trusted.*`, `Captured`, `Spec.*`, and
  `Expected`, including `.olean.server`/`.olean.private` parts for `module`
  files) with **zero** `Anneal.*` or `Proof.*` modules present in the
  filesystem. Invokes stock `leanexport` (`LEAN_ABORT_ON_PANIC=1`, never
  `--ignore-missing`, so an absent root or dependency aborts the export) over
  `Expected.claim`, every `Specification` constant from the module index
  (except paired well-founded `_unsafe_rec` auxiliaries, which are `partial`),
  and roots covering every target-module constant that `proof_full.ndjson`
  contains, emitting `expected_cone.ndjson`. It runs after `5b` for that
  reason; the two exports share no inputs or outputs.
- **Action `5b` (`AnnealExportProof`, sandboxed):** Mounts the read-only
  compiled proof closure inside `ExecSeal` (`bwrap` with `--seccomp` and
  `--disable-userns`, zero network, no access to `expected_cone.ndjson` or
  verdict output) or an isolated remote build container. Its sole output is the
  plain-text declaration stream `proof_full.ndjson`.
- **Action `5-init` (`init_primitives_cone.ndjson`):** Generated once per
  `(sysroot, leanexport_sha256, sysroot_key)` from the clean `Init` module
  with zero target `.olean`s mounted. It pins all 39 `Init` kernel-extension
  and elaborator primitives (`Nat.*` arithmetic/bitwise operations, `String.*`,
  `Char`, `List`, `Bool`, `Eq`, `Quot.*`, `eagerReduce`,
  `optParam`/`autoParam`/`semiOutParam`/`outParam`), the 3 standard axioms
  (`Classical.choice`, `Quot.sound`, `propext`), and
  `System.Platform.{numBits, getNumBits, numBits_eq}`. Pinning these primitives
  unconditionally closes unused-primitive substitution attacks where an
  untrusted proof export could otherwise inject an altered definition for a
  kernel-recognized primitive absent from `expected_cone.ndjson`.
- **Action `5-pin` (`sysroot_pins.ndjson`):** Re-exports, from the clean
  admitted sysroot with zero target `.olean`s mounted, every constant of
  `expected_cone.ndjson` or `proof_full.ndjson` whose name is in the
  `"sysroot-consts"` inventory. Sysroot status is therefore never granted by
  name alone: a proof module that redeclares a sysroot name (for example in a
  module that never imports the defining sysroot module) must reproduce the
  clean definition exactly.
- **Action `5c` (`AnnealVerifyNdjson`):** A pure-Rust verifier compiled with
  `#![forbid(unsafe_code)]` that never links or invokes a C++ `.olean` loader.
  It checks metadata consistency across exports, enforces five mandatory
  structural invariants, and invokes independent external kernels:
  1. **Well-formed exports and canonical hash-consed DAG identity:** Requires
     every export to declare each constant's dependencies before the constant
     (except within one inductive record, which must be a consistent mutual
     block), so a missing, forward, or cyclic reference fails closed;
     normalizes declaration table
     indices via structural `CanonName` trees (`Name` `.str`/`.num` nodes,
     rejecting duplicate JSON keys), and verifies that `expected_bfs.visited`
     appears in `proof_full.ndjson` and every constant common to both exports
     matches identically.
  2. **Authenticated origin and namespace isolation:** Every sysroot-named
     constant in either export must equal its `5-init`/`5-pin` clean
     re-export; every target-module constant in `proof_full.ndjson` must
     appear in `expected_cone.ndjson`; every `expected_cone.ndjson` constant
     must have one of those two origins; canonical inputs must come from their
     designated roles, and the canonical root must be `CrateTheorem` or
     `UnitTheorem` (applied to `Crate.mk`) or their Profile v2 counterparts
     (applied to `CrateV2.mk`). Proof-origin constants may not use
     `KERNEL_ACCELERATED_NAMES`, `RESERVED_KERNEL_ROOTS`, or the `Trusted`
     root (except generated equation/splitter helpers of a pinned parent).
     Strips elaboration-only `optParam` wrappers for statement-origin checks
     and applies the direct and transitive specification bans to every
     constant the `Specification` modules declare.
  3. **Exact theorem, opacity, and axiom checks:** Verifies that `Proof.verify`
     is a theorem with empty universe parameters whose type matches
     `Expected.claim`, that its transitive cone and export contain zero
     `unsafe`/`partial` declarations and zero non-sysroot `opaque` declarations
     (permitting pinned sysroot `System.Platform.getNumBits`), and that its
     axioms are a subset of `{Classical.choice, Quot.sound, propext}`
     (admitting `sorryAx` only on proof-only edges when
     `--allow-sorry-in-proof` is passed, which unconditionally taints Receipt
     v3).
  4. **Quotient primitive post-check:** Confirms `Quot`, `Quot.mk`,
     `Quot.lift`, and `Quot.ind` match the pinned kernel-synthesized primitive
     definitions and rejects any foreign `.quotInfo` declaration.
  5. **Independent dual-kernel checking (`nanoda_bin` + `con-ron`):** Invokes
     both **`nanoda_bin`** (memory-safe Rust checker configured with
     `"unpermitted_axiom_hard_error": true` and the closed 3-axiom allowlist)
     and **`con-ron`** (`--verified`, formally verified Rust arena kernel
     bundled in stock Lean `v4.35.0+`) over `proof_full.ndjson`. Both checkers
     must exit `0` (with `con-ron` explicitly recorded in `kernelsSkipped`
     only under tainted `--allow-sorry-in-proof` runs containing `sorryAx`).
     Verdict serialization uses strict `#[serde(deny_unknown_fields)]` typed
     Rust structures recording binary SHA-256 digests rather than untyped JSON
     maps. As with `TrustedBoundary.lean`'s `"target-audit"`, the verdict
     carries the admitted module import `graph` and subject, model, and
     specification closures listing exactly the reached declarations with
     their defining modules, so `cargo anneal verify` applies its bundled-model
     trust-tier and `candidate:*` checks unchanged.

For mega-crates whose exported proof cones exceed single-process budgets, an
optional action **`5d` (`AnnealLinkShardNdjson`)** runs `5a`/`5b`/`5c` per
depth-$D=1$ zero-axiom shard and verifies the parameterized implication
composition in pure Rust (see
[build-systems-and-receipts.md](build-systems-and-receipts.md)).

### Optional paranoid multi-kernel CI mode

Single-kernel verification remains vulnerable to an implementation bug in one
checker. On Lean `v4.35.0+`, release cuts, merge queues, and nightly CI jobs
can pass `--paranoid-quorum` (requiring `--allow-unpinned-lean` until a
`v4.35.0+` toolchain is pinned in `foundation-lock.json`), invoking two
additional independent kernels—**`con-leche`** and **`lean4lean --import`**—
over `proof_full.ndjson` inside `ExecSeal` alongside `nanoda_bin` and `con-ron`
for a four-independent-kernel quorum. The pure-Rust `5c` verifier remains the
portable primary driver while `--paranoid-quorum` serves as a multi-kernel
cross-check oracle.

### Retiring in-process `.olean` auditing and shrinking the runtime Lean TCB

Retiring in-process `.olean` target replay transforms Anneal's runtime Lean
audit surface:

- **Runtime Lean TCB shrinks to a parser-only `SpecPreflight`:** Once
  `5a`/`5b`/`5c` replaces `TrustedBoundary.lean`'s target-replay blocks and
  Pass 2 `lean-miri` correspondence auditing is split into an offline CI-only
  module, the only Lean audit code bundled with `cargo-anneal` is a unified,
  parser-only **closed-allowlist `SpecPreflight`** (`TrapFreeHumanSpecAST`,
  zero `.olean` loading, zero elaboration). Moving from a syntax denylist to a
  closed allowlist blocks macros, custom delaborators, `implemented_by`/
  `extern`/`csimp` attributes, `autoImplicit true`, and unguarded `Nat`
  subtraction or division on `Spec.*` modules. Today's `SpecPreflight` is not
  yet parser-only: its `"sysroot-consts"` and `"target-consts"` modes import
  the admitted sysroot and the compiled non-`Proof` target `.olean`s
  (`loadExts := false`) to build constant-to-module indices.
- **Hardened `ExecSeal` and out-of-band lock roots:** Local `ExecSeal` unifies
  Tier 1 `bwrap` with the Tier 2 `seccomp-bpf` allowlist (`--seccomp` and
  `--disable-userns`) so untrusted proof elaboration and `5b` export run under
  strict syscall filtering. Out-of-band specification lock roots
  (`--spec-lock-sha256` supplied by the host orchestrator or CI base branch)
  and compiled-in theory digests ensure that a workspace-writing agent cannot
  mutate a specification and its lockfile together to self-attest a weakened
  claim.

## 2. `MirSemantics` Guard-Mutation CI (`check_guard_mutation.py`)

Positive verification proofs and positive test suites share a structural blind
spot: they cannot detect the accidental deletion or weakening of a safety check
in `Trusted/MirSemantics/` or a rejection rule in the auditor. If a refactoring
commit accidentally removes a division-by-zero check, drops an alignment or
bounds check, skips move deinitialization, or disables a forbidden-import ban,
100% of positive proofs continue to pass while unsound Rust programs silently
become provable.

To catch silent guard erosion automatically in CI, Anneal's defense-in-depth
methodology introduces **`anneal/ci/check_guard_mutation.py`** (alongside
dedicated negative refutation fixtures outside `anneal/trusted/`):

1. **Explicit guard catalog:** Enumerates individual UB and admission guards
   across all eleven guard-bearing `Trusted/MirSemantics/` modules
   (`CoreContracts.lean`, `AllocContracts.lean`, `Ops.lean`, `Enum.lean`,
   `Layout.lean`, `Memory.lean`, `Bytes.lean`, `State.lean`, `Step.lean`,
   `Boundary.lean`, and `Contract.lean`, `342` guards; the twelfth file,
   `CanaryFixtures.lean`, is explicitly excluded as fixture/helper data
   verified directly by Pass 1 `Trusted.MirSemantics` canaries and Pass 2
   `Trusted.Correspondence`) alongside auditor header-import (`audit_headers`,
   `8` guards across `TrustedBoundary.lean` and `SpecPreflight.lean`) and
   boundary (`audit_boundary`, `12` `"spec-preflight"` and `"target-audit"`
   guards) checks in `TrustedBoundary.lean` (`362` Lean guards in total), plus
   `extract_guards` (`45` `rustc-capture` guards; `407` total cataloged
   guards). Each catalog entry pins a unique source anchor and its exact
   guard-weakening mutation.
2. **Isolated single-guard mutation:** Copies the relevant files into an
   isolated temporary directory (never modifying the working tree), applies one
   guard-removal mutation at a time, and recompiles only the minimal downstream
   `.olean` closure or isolated `rustc-capture` artifact on top of precompiled
   base artifacts.
3. **Anti-crash-masquerading gate:** Before checking negative fixtures, the
   runner confirms that the mutated target and a positive sanity suite still
   compile and pass cleanly. A syntax error, type error, or unexpected runtime
   crash therefore cannot masquerade as a mutant kill.
4. **100% kill-rate requirement:** Each semantics mutant must cause a localized
   proof failure in its dedicated negative refutation theorem (proving that the
   mutated semantics stopped rejecting the corresponding UB pattern); each
   auditor or `rustc-capture` mutant must cleanly flip a negative witness from
   reject to accept, break its targeted negative unit test, or trigger a labeled
   diagnostic-precedence check.

### Scope and limits of guard-mutation CI

- **What it guarantees:** Every executed guard in the catalog is live and
  actively exercised by a negative refutation, negative auditor or capture
  witness, negative unit test, or labeled diagnostic-precedence pin (`362` Lean
  guards enforced in GitHub Actions PR CI today; `45` `extract_guards` verified
  under pinned `rustc-dev` and pending `workspace-tests` workflow wiring).
- **What it does not guarantee:** It cannot detect bugs in unmodeled Rust
  semantics, missing guards that were never written, newly added guards not yet
  registered in the catalog, Rust-side `anneal-rustc-capture` checks outside the
  `45` cataloged `extract_guards`, or regressions in `extract_guards` on
  `--lean-only` CI jobs until `workspace-tests` workflow execution lands.

## 3. Non-adversarial `audit-spec` sanity checks

> [!WARNING]
> **Non-adversarial reviewer sanity checks only — NOT anti-adversarial
> security guarantees.**
>
> Everything in `cargo-anneal audit-spec` (`PreInhabited`, clause independence,
> and Dual-Polar `MutationRefute`) is designed to help *good-faith authors and
> human reviewers* catch accidental vacuity, contradictory preconditions, or
> missing return-value bindings. These checks **do not** defend against an
> adversarial author or reward-hacking agent trying to weaken a specification.
>
> **Why:** A single inhabitant witness (`PreInhabited`) proves only that the
> precondition set is non-empty, not that it covers the intended input domain.
> An adversarial specification can trivially satisfy `PreInhabited` by
> accepting *only that one witness* (for example, `requires(x == 0)` on a
> function intended to hold for all `u32`). Likewise, `MutationRefute` tests
> only the specific code mutants included in the mutation suite; an adversarial
> spec can reject those specific mutants while leaving other inputs or
> properties unconstrained.
>
> Defense against adversarial specification weakening remains **bounded human
> review** of the stated specifications ([`THREAT_MODEL.md`](../THREAT_MODEL.md)
> Section 1 and Section 2.2), enforced mechanically by out-of-band lock roots
> and always-rendered golden spec closures gated by `CODEOWNERS` / `OWNERS`
> ([`spec-core-and-golden-closure.md`](spec-core-and-golden-closure.md)).

Within that honest boundary, `cargo-anneal audit-spec` provides four structured
sanity and adequacy checks:

### 1. `PreInhabited` (accidental-vacuity witness)

For any precondition-guarded function (`safetyPre` or `behaviorPre`),
`PreInhabited` asks for an explicit constructive witness
`ValidEntryArgs body args_0 ∧ safetyPre args_0 ∧ behaviorPre args_0`. This
catches accidental contradictions (such as `x < 5 ∧ x > 10` or a typo that
collapses a precondition to `False`) where any postcondition would hold
vacuously.

*(Note: By contrast, `AssumedContractRealizable` on `#[anneal::trusted]` and
`extern` contracts is a mandatory **soundness obligation** preventing callers
from deriving `False`, not merely a sanity check; see
[spec-core-and-golden-closure.md](spec-core-and-golden-closure.md).)*

### 2. Linear $(m+1)$-witness clause independence

For a multi-conjunct functional specification $S = \bigwedge_{i=1}^m C_i$,
requiring one joint positive witness $w^+$ (satisfying every $C_i$) plus $m$
single-clause negative counter-witnesses $w_i^-$ (satisfying all $C_j$ for
$j \neq i$ while falsifying $C_i$) checks in $O(m)$ witnesses that no conjunct
accidentally implies or contradicts another.

### 3. Dual-Polar `MutationRefute` (`Pole A ∧ Pole B`)

Naive single-polar mutation testing—mutating a Rust function into
$P_{\text{mut}}$ and checking whether the existing proof script fails
(`exit != 0`)—is unreliable for two reasons:

1. **Proof-to-code coupling:** Even a vacuous specification (`Spec := True`)
   can cause a brittle proof script to fail when a mutant shifts basic-block
   numbering, step counts, or intermediate lemmas.
2. **Crash masquerading:** Treating any non-zero exit code—or any
   `proof_failed` receipt—as a killed mutant counts `maxHeartbeats` /
   `maxRecDepth` blowups, out-of-memory kills, and kernel errors as apparent
   specification strength. Authored `Proof`-module deterministic heartbeat and
   recursion-depth limits exit `1` (`status == "proof_failed"`,
   `phase == "audit"`) with a structured `"reason"` field
   (`"heartbeat_limit_exceeded"` or `"recursion_depth_exceeded"`) so negative
   and mutation checks must refuse to credit any `proof_failed` receipt carrying
   `"reason"` as a mutant kill.

Dual-Polar `MutationRefute` eliminates both failure modes by pinning the exact
SHA-256 digest of `Spec.lean` across the positive and negative checks and
requiring **both poles**:

- **Pole A (Clean pipeline rejection):** Running the verifier on
  $(P_{\text{mut}}, \mathsf{Spec}, \pi_{\text{shipped}})$ must exit cleanly
  with `"status": "proof_failed"`, `"phase": "audit"`, absent `"reason"` (never
  `"heartbeat_limit_exceeded"` or `"recursion_depth_exceeded"`), and zero
  runtime, resource-limit, or kernel errors.
- **Pole B (Kernel-checked refutation theorem):** A separate kernel-checked
  theorem (audited strictly within `{propext, Classical.choice, Quot.sound}`)
  proves **`⊢ ¬ CrateTheorem ⟨P_mut, Spec⟩`**—for example, by exhibiting a
  concrete input on which $P_{\text{mut}}$ returns a value violating `Spec` or
  triggers a concrete UB fault.

Passing Pole B proves mathematically that the *specification itself* excludes
the mutant's behavior (catching missing return-value bindings or overly weak
postconditions), rather than merely showing that a particular proof script
stopped compiling.

### Rollout posture

In Stage 1 (`#4012`), `MirSemantics` Guard-Mutation CI
(`check_guard_mutation.py`) is targeted as a mandatory repository CI check
protecting Anneal's own TCB, while `cargo-anneal audit-spec` (`PreInhabited`
and Dual-Polar `MutationRefute`) starts as an opt-in reviewer aid for crate
authors before graduating to recommended CI practice in Stage 2 (`#4096`).
