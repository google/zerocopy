# Anneal's Pass 2 `lean-miri` Correspondence Audit and the Requirements for an Analogous Sail RISC-V Reference Audit

## Summary

- **Anneal Pass 2 at `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`**
  anchors the trusted MIR semantics against a vendored upstream reference
  model, `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, using:
  (1) a content-addressed pin `vendor/lean-miri/UPSTREAM_PIN.json`
  (`schema_version` 2) whose own SHA-256 is locked in the auditor's Rust source;
  (2) a 160-module `Miri.Interpreter.ExecutionMachine` slice that is
  *enumerated* in the pin, not computed by the auditor; (3) a cold per-module
  build inside a bubblewrap sandbox with fixed flags
  (`lean -j1 -M2048 -t0 -DElab.async=false -Ddebug.skipKernelTC=false`) and
  SHA-256 checks of every `.olean`; (4) a fresh standalone kernel replay
  (`Kernel.Environment.replay`, not lean4checker) of every non-`isPartial`
  vendor constant onto an authenticated `Init`/`Std`/`Lean` sysroot base,
  followed by all repository constants; (5) per-constant checks on **every**
  vendor constant (no `axiom`, `unsafe`, `sorryAx`, compiler-reflection
  references); (6) cone checks from 21 roots and from every correspondence
  constant rejecting any reachable partial, unsafe, vendor `opaque`, or axiom
  outside `{propext, Classical.choice, Quot.sound}`; and (7) 30 locked
  `*Claim : Prop` theorems.
- The reference machine is **not** `lean-miri` alone: it is `lean-miri`'s
  `Step.step` instantiated with Anneal-authored hooks, a codec, and a step
  budget, which are human-audited TCB. Pass 2 runs in repository CI (and
  locally when the directories exist), never inside `cargo anneal verify`.
- A Sail-backed analogue can reuse the mechanism, but its inputs differ. The
  generated `opencompl/sail-riscv-lean@51c635c4` has 0
  `partial`/`unsafe`/`extern`/`implemented_by`/`opaque`/`sorry`, yet carries 75
  handwritten `axiom`s (8 platform + 67 softfloat) in `RiscvExtras.lean`, which
  Anneal's audit rejects even when unreachable. Module slicing does not help on
  the full RV64D model (one step needs 118 of 124 built modules, 159k LOC); the
  scoped `riscv-zkvm` extraction needs 80 modules (47k LOC), about the size of
  the audited `lean-miri` slice (44,730 LOC).
- Measured on Lean v4.34.1: `lean-sail` v10 replays 1,180/1,180 non-partial
  constants with only the three standard axioms; `lean-sail` v5 (v4.29.0)
  compiles on v4.34.1; the generated `LeanRV64D.Defs` fails under Anneal's
  vendor limit `-M2048` with `(kernel) excessive memory consumption detected`
  and succeeds at `-M4096` (53.6 s, 2.47 GB peak RSS, 33.9 MB `.olean`, 9,755
  constants replayed in 3.4 s). `.olean` hashes are identical across
  directories under identical flags but differ between Lake and Anneal-flag
  builds.
- Derived requirements: a pin schema that also records generator inputs and
  compile flags, an auditor-computed closure checked against the pin, a
  per-class axiom patch policy, and a raised `-M`. One seam cannot be patched in
  Lean alone: `match_reservation` and `valid_reservation` are *pure* in the Sail
  source, so no definition or global oracle can make SC success depend on an
  earlier LR.

## Applicability

- **Anneal mechanism:** public `joshlf/anneal` tree at
  `c131b320eeeb26ef692e5afd5ec8db49ee518613` (2026-11-19), introduced by commit
  `ec77c1a2f3a8d2090e650a3c46d291f316e2bad6` ("[audit] Enforce MIR
  correspondence and lean-miri pin in CI (#264)"). Line numbers refer to
  `c131b320`. The vendored reference model is `proofs-rs/lean-miri@c92d1d97…`
  (upstream `lean-toolchain` v4.35.0), built by Anneal under Lean v4.34.1.
- **Sail measurements:** `opencompl/sail-riscv-lean@51c635c460125ac87955d061fcd902ce03b8011f`
  (V1 interface, upstream toolchain v4.29.0, lean-sail tag `v5`);
  `rems-project/lean-sail@e4745c82fe329f162700020dcd31da6b342473b9` (tag `v10`,
  v4.34.1) and `@079463134b9c50450b8393e1566a09fc492a34d9` (tag `v5`, v4.29.0);
  `Verified-zkEVM/riscv-zkvm@6810fc14d9c40373101321cefaec59df8d82e3e7` (Lean
  v4.33.1, scoped extraction of sail-riscv `0.13.1`); `riscv/sail-riscv` at
  `27224ccb2290f022e46213c05b3e72e8a9ea635e` (tag `0.13.1`) and
  `ec5200bdfe0c10afa6dbb1f7b0980db2d236236e` (HEAD, 2026-11-19) for Sail
  sources and handwritten support. The Sail half evaluates those artifacts
  *through* Anneal's Pass 2 rules (what would pass, what would be rejected, what
  a second vendor root would need).
- **Execution environment:** Lean v4.34.1 release
  (`5045d0056413266e57c625dcd7c365b10e377c52`, x86_64-unknown-linux-gnu), one
  x86_64 Linux host, not under the bubblewrap sandbox, with Anneal's vendor
  compile flags unless stated. The full RISC-V model was not built; only
  `LeanRV64D.Defs` and `LeanRV64D.RiscvExtras` were compiled.
- Section 3 contains derived design conclusions for a generic "small
  kernel-reducible trusted RV64 S-mode model"; they are not facts about any
  upstream artifact.
- Sail-extraction facts (backend extern emission, exact axiom call sites,
  regeneration commands, V2 interface) are covered in more detail by package
  `sail-riscv-lean-extraction-provenance-extern-axioms-and-privileged-config`;
  this report summarizes them only where the audit depends on them, and its
  numbers agree with that package.

## Findings

### 1. Anneal Pass 2 mechanism (`joshlf/anneal@c131b320`)

#### 1.1 Trigger, placement, CI vs. local

Basis: source + documentation

- Pass 2 is implemented by the Rust auditor `anneal-audit`
  (`trusted/audit/src/lib.rs`) plus the Lean inspector
  `trusted/audit/TrustedBoundary.lean`, which runs as
  `lean -j1 -M8192 --run TrustedBoundary.lean <req.json> <res.json>` for Pass 2
  requests (`-M2048` for Pass 1; `lib.rs:2165-2180`;
  `TrustedBoundary.lean:2275-2333`).
- `Checker::run_correspondence` runs Pass 2 when `--require-correspondence` is
  set **or** any of `vendor/lean-miri`, `trusted/correspondence`,
  `correspondence` exists, and fails closed if only some of them exist
  (`lib.rs:2815-2854`). CI's step "Audit repository trusted boundary" passes
  `--require-correspondence` (`.github/workflows/ci.yml:423-439`). Running
  `anneal-audit` in a checkout locally also runs Pass 2; cold vendor
  compilation requires Linux `/usr/bin/bwrap` and fails closed otherwise
  (`lib.rs:3356-3400`).
- `vendor/lean-miri/` and `correspondence/` are "never shipped in the user
  toolchain archive" (`docs/trust-model.md:52-53`); a digest-bound
  correspondence provenance record in packaged archives is *planned* control 5
  (`docs/trust-model.md:493-508`). Hence `cargo anneal verify` does not re-run
  Pass 2.
- Placement: `trusted/correspondence/` is tactic-free TCB carrying
  `-- anneal-trust-tier:`; `correspondence/` is untrusted proof code (may use
  `noncomputable def`); `vendor/lean-miri/` is "for repository CI
  correspondence audits only (never packaged or imported by `trusted/lean/` or
  `theory/`)" (`AGENTS.md:178-196`, `406-411`).

#### 1.2 Pin schema and TCB locks

Basis: source + execution

`UPSTREAM_PIN.json` (3,379 lines) is deserialized with
`#[serde(deny_unknown_fields)]` into `UpstreamPin` (`lib.rs:4060-4148`):

| Field | Content at `c131b320` |
|---|---|
| `schema_version` | `2` |
| `repository`, `commit` | `https://github.com/proofs-rs/lean-miri.git`, `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` |
| `upstream_lean_toolchain` / `build_lean_toolchain` | `leanprover/lean4:v4.35.0` / `leanprover/lean4:v4.34.1` |
| `upstream_git_objects` | Git object ids at the pinned commit (`Miri` tree `ef473f04…`, `Miri.lean`, licenses, `tools/*`, `upstream/.pins/*`, `upstream/source-lock.json`) |
| `upstream_pins` | `miri_commit 7fa591d7…`, `rustc_commit 8144389c…`, `rustc_apfloat_commit`, `aes_commit`, `source_lock_sha256` |
| `patched_files` (10) | `{path, upstream_sha256, patched_sha256, rationale}` for the opt-in `deinitMovedPlace` delta in `Miri/Interpreter/{Call,Cast,ExecutionCalls,ExecutionCast,ExecutionMachine,LocalAccess,MachineHooks,OperandMachine,Place,PlaceMachine}.lean` |
| `execution_machine_closure` (160) | `{module, path, olean_sha256, olean_server_sha256?, olean_private_sha256?}`; only `Miri.Memory.QSortProof` (a module-system file) has the sidecar digests; first entry `Miri.ABI.Size`, last `Miri.Interpreter.ExecutionMachine` |
| `vendor_aux_files` (8) | `{path, sha256}` for licenses, `tools/check_semantic_sources.py`, `upstream/.pins/*`, `upstream/source-lock.json` |
| `vendor_tree` | `file_count` 608, `files[]{path, sha256, patched_sha256?}`, `manifest_sha256` `081747a3…` |

TCB constants (`lib.rs:123-157`): `LOCKED_MIRI_COMMIT = c92d1d97…`,
`LOCKED_UPSTREAM_PIN_SHA256 = b629a9b4c3fd184b20b791d34621a9f6aa1518ed9b164e42561b4eb688157271`,
`LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256 = 2fa0ec69…` (over sorted
`"{rel_path}:{sha256}\n"` lines of every `Init`/`Std`/`Lean`
`.olean`/`.olean.server`/`.olean.private` of the pinned toolchain), and
`LOCKED_PATCHED_MIRI_FILES` (the 10 paths). The SHA-256 of
`git show c131b320…:vendor/lean-miri/UPSTREAM_PIN.json` equals the locked
digest (`support/outputs/anneal_pin_facts.out`).

#### 1.3 Pin verification (`verify_upstream_pin`, `lib.rs:4150-4522`)

Basis: source

Regular-file/no-symlink checks; pin SHA-256 equals the locked digest;
`schema_version == 2`; `commit == LOCKED_MIRI_COMMIT`;
`build_lean_toolchain == "leanprover/lean4:v4.34.1"`; `patched_files` equals the
locked allowlist with distinct upstream/patched hashes and a non-empty
rationale; `vendor_tree.file_count` and a recomputed `manifest_sha256` over
`"{sha256}  {path}\n"`; a no-follow walk of `vendor/lean-miri/` rejecting
symlinks, non-regular files, unlisted files, hash mismatches, and missing files.
Closure entries must be `Miri.*`, have path equal to the module path, be listed
in `vendor_tree`, carry valid hex digests, be unique, number exactly **160**,
include `Miri.Interpreter.ExecutionMachine`, and exclude
`Miri.Input.NativeMathHost` ("which contains `@[extern]` host math bindings",
`lib.rs:4474-4519`).

#### 1.4 The slice is enumerated, ordered, and only indirectly checked for completeness

Basis: source + execution

The auditor does not compute an import closure. `verify_and_stage_miri_entries`
stages and compiles the entries **in pin-list order** against the
already-staged `miri-lib` (`lib.rs:3072-3354`), so the list must be
topologically ordered; a missing dependency surfaces only as a failure of the
per-module compile or of the inspector's later `importModules`. Measured with
`support/anneal_pin_facts.sh` (output `support/outputs/anneal_pin_facts.out`):
the 160 closure files total **44,730 lines** of 106,656 vendored `.lean` lines
(by namespace: Interpreter 93, Memory 21, Concurrency 13, TreeBorrows 12, Input
9, ABI 7, MIR 2, DataStructures 2, OperationalSafety 1). They contain 24
`partial def` (all in `Miri/Input/{Decoder,DecoderValues,LowerMIR,JsonTraversalCache,SharedPayloads}.lean`),
0 `@[extern]`, 0 `@[implemented_by]`, 0 `axiom`, 0 `opaque` keyword, 0 `sorry`,
0 `native_decide`, 1 `run_cmd` (`Miri/Memory/InitMask.lean:636`) and 1
`initialize` declaration (`Miri/Input/DecoderValues.lean:918`).

#### 1.5 Sandboxed per-module compilation and `.olean` digest checks

Basis: source

Each closure source is staged and re-hashed against the pin, then the `.olean`
(+ sidecars) is either restored from `--miri-cache-dir` after digest checks or
compiled cold inside a per-module `bwrap` sandbox
(`--unshare-all --die-with-parent --new-session --clearenv --tmpfs /`,
read-only toolchain/sources/`miri-lib`, single writable `/work/out`;
`lib.rs:3403-3465`, `3596-3730`) with exactly:

```text
lean -j1 -M2048 -t0 -DElab.async=false -Ddebug.skipKernelTC=false \
     -R src/vendor-miri -o out/<M>.olean src/vendor-miri/<M>.lean      # LEAN_PATH=/work/miri-lib
```

Unexpected outputs are rejected and `.olean`/`.olean.server`/`.olean.private`
digests are verified before staging and before any cache write
("write-after-verify", `lib.rs:3238-3351`). The cache must lie outside the
checkout (`ensure_miri_cache_outside_checkout`, `lib.rs:602`). CI keys it on
`trusted/lean/lean-toolchain` + `UPSTREAM_PIN.json` and skips it on
`merge_group`, `push`, and `workflow_dispatch`, so every landed revision is
built cold (`ci.yml:272-283`, `436-438`). Pass 2 repository modules
(`trusted/correspondence/`, `correspondence/`) compile in separate sandboxes
with `-M4096` (comment: importing the closure "consumes ~1.7 GiB of Lean's `-M`
allocator at startup", `lib.rs:2991-2993`, `3785-3830`); `correspondence/` also
gets `-DwarningAsError=true` (`lib.rs:3030`). Vendor compiles do not set
`warningAsError`.

#### 1.6 Kernel replay onto an authenticated base

Basis: source

`auditCorrespondence` (`TrustedBoundary.lean:2243-2273`):

1. `collectCorrEnv` (`:2121-2144`) imports foundation + trusted + theory +
   vendor modules with
   `importModules … (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)`
   (`importCorrEnv`, `:422-428`), classifies modules into
   `CorrOrigin = .foundation | .sysrootFoundation | .vendorMiri | .repo …`, and
   drops `isPartial` constants from the vendor replay set (`:2140-2143`).
2. `replayCorrAndVendor` (`:2146-2201`) re-imports **only** the authenticated
   sysroot (`Init`/`Std`/`Lean`) as `baseEnv`, rejects vendor names shadowing
   sysroot names, runs `baseEnv.toKernelEnv.replay vendorReplayLocals`, rejects
   repository names shadowing vendor/sysroot names, replays all Pass 1 and
   Pass 2 repository constants on top of the replayed vendor environment, and
   fails unless every correspondence constant is present afterwards.
3. `verifyCorrConesAndClaims` (`:2203-2223`) runs the cone and claim checks.

The replay runs on every invocation, cold build and cache hit alike. The
replayed-declaration count is stated as 38,728 in `docs/trust-model.md:432` and
as 38,718 in the inspector docstring (`TrustedBoundary.lean:2228`); this
in-tree inconsistency was not resolved (it requires an audit run).

#### 1.7 Constant checks, cone checks, and allowed axioms

Basis: source

| Layer | Scope | Rejects | Location |
|---|---|---|---|
| Vendor inventory | **every** `.vendorMiri` constant, reachable or not | `axiom`, `unsafe`, quotient primitive, missing body, direct `sorryAx` (`constantHasSorry`), direct reference to `Lean.ofReduceBool`/`ofReduceNat`/`trustCompiler`/`reduceBool`/`reduceNat` (`forbiddenVendorCompilerRefs`), declarations in `Trusted`/`Anneal` namespaces, non-identical duplicates | `TrustedBoundary.lean:1604-1758` |
| Replay set | vendor | omits `isPartial` (`*._unsafe_rec`), so a replayed reference to one fails with `unknown constant`; Lean's replay itself skips unsafe/partial ("We skip unsafe constants, and also partial constants") | `:1108-1124`, `:2164-2167` |
| Cone (`closureCorr`) | constants reachable via `declarationEdges` (type, value incl. opaque values, `all`, ctors, rec rules; `:1036-1049`) from 21 Miri roots (first root `Miri.Interpreter.ExecutionMachine.step`) and from every correspondence constant | reachable `unsafe` or `isPartial`; reachable **vendor** `.opaqueInfo` ("guaranteeing that none of the 24 `partial def` JSON parser helpers … is reachable"); reachable axiom not in the policy | `:1760-1809`, `:2220-2222` |
| Axiom policy | name **and** module | anything but `[[Classical.choice, Init.Prelude], [Quot.sound, Init.Prelude], [propext, Init.Core]]` from `trusted/lean/foundation-lock.json` | `closure`, `:1182-1207` |

Vendor `partial def` and `opaque` are tolerated as long as they are
unreachable. `@[implemented_by]`/`@[extern]` attributes are not inspected on
vendor code (`loadExts := false`); the kernel never uses compiled code, and the
one `@[extern]` module is excluded at pin level. Vendor sources are not
syntactically preflighted (`docs/trust-model.md:402-415`); repository Pass 2
sources are, twice (foundation parser and a sandboxed "union" parser that loads
`Miri` extensions), against closed allowlists forbidding `axiom`, `partial`,
`unsafe`, `noncomputable section`, `set_option`, `implemented_by`, `extern`,
macros, and elaborators (`docs/trust-model.md:204-271`).

#### 1.8 Claims and the structure of the reference machine

Basis: source + documentation

`verifyCorrespondenceClaims` (`TrustedBoundary.lean:1821-2021`) requires 30
`*Claim` definitions in `Trusted.Correspondence`, each universe-monomorphic,
of type `Prop`, referencing a non-empty list of required constants, and proved
by a theorem in `Anneal.MirCorrespondenceProof` whose type is exactly
`Expr.const claimName []` (`requireClaimProof`, `:1316-1365`). Top-level shapes
(`trusted/correspondence/Trusted/Correspondence.lean`):

```lean
def CorrespondenceClaim : Prop :=                                    -- :2565-2571
  ∀ (p : Program) (q : Query), WellFormed p q →
    RefWellFormed (encodeProg p) q ∧
    (∀ (out : TerminalOut), Behavior p q out ↔ RefBehavior (encodeProg p) q out) ∧
    (Diverges p q ↔ RefDiverges (encodeProg p) q)

def FaultEquivalenceClaim : Prop :=                                  -- :2575-2579
  ∀ (p : Program) (q : Query) (k : FaultKind),
    ReachesResult p q (.fault k) ↔
    ∃ maxSteps, RefReachesOutcome (encodeProg p) q maxSteps (faultToRefOutcome k)

def SimulationInv (p : Program) (s : State) (rs : RefState) : Prop := -- :2541-2549
  ∃ f rf retTy, s.frames = [f] ∧ rs.frames = [callerSentinelFrame retTy, rf] ∧
    rs.callerMem = s.callerMem ∧ entryRetTy? p = some retTy ∧
    f.defId = p.entryDefId ∧ FrameSimInv p f rf
```

`MiriMoveDeinitWiringClaim` (`:2599-…`) states, for all configurations and
limits, that `Miri.Interpreter.ExecutionMachine.step` equals
`Miri.Interpreter.Step.step` over `ExecutionMachine.stepHooks` with
`pendingMoveDeinit` reset. The reference step `evalRefStep` (`:2402-2433`) runs
`Miri.Interpreter.Step.step` with **Anneal-authored hooks** `refStepHooksFor`
(`:2219`) behind a codec (`encodeProg`/`decodeProg`) and a step budget.
`verifyRefEvaluatorIndependence` (`:2023-2088`) only checks that the reference
cone reaches 21 named `Miri.*` primitives and none of 25 named
`Trusted.MirSemantics` evaluator functions. The design doc calls the vendored
tree "part of the pinned, human-audited correspondence TCB, not merely an input
checked for forbidden axioms" (`docs/mir-correspondence-design.md:602-624`), and
every pin update requires human review of the old-to-new semantic diff
(`docs/trust-model.md:469-480`).

#### 1.9 Toolchain precedent

Basis: documentation

Anneal compiles and pins `.olean` digests for the v4.35.0-targeting upstream
under v4.34.1, stating that this "establishes kernel well-typedness under
`v4.34.1`, not semantic equivalence with upstream `lean-miri`'s `v4.35.0` test
suite" (`docs/mir-correspondence-design.md:632-648`;
`docs/trust-model.md:335-341`).

### 2. Measurements of the Sail Lean artifacts against those rules

#### 2.1 Construct census

Basis: source + execution (`support/count_constructs.py`, output
`support/outputs/counts.txt`; comment-stripped regex counts; file/line totals
count only the listed directory — the sibling package counts the root module
too: 161 files / 174,111 lines for opencompl, 121 / 60,278 for riscv-zkvm; the
difference is counting method only)

| Tree | Files | Lines | `partial def` | `unsafe` | `implemented_by` | `@[extern]` | `opaque` | `axiom` | `noncomputable section` | `termination_by` | `sorry`/`native_decide` |
|---|---|---|---|---|---|---|---|---|---|---|---|
| opencompl `LeanRV64D/` | 160 | 173,614 | 0 | 0 | 0 | 0 | 0 | **75** (all in `RiscvExtras.lean`) | 157 | 11 | 0 / 0 |
| riscv-zkvm `RiscvZkvm/Sail/` | 120 | 59,955 | 0 | 0 | 0 | 0 | 0 | **75** (all in `RiscvExtras.lean`) | 116 | 10 | 0 / 0 |
| lean-sail v5 | 10 | 1,599 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 0 / 0 |
| lean-sail v10 | 11 | 1,723 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 0 / 0 |

lean-sail's one `partial def` is the `match_bv` term elaborator
(`partial def elabMatchBv : TermElab`, `Sail/BitVec.lean:202-204` at `v10`),
which is compile-time only. Sail externs (`val f = pure/impure {c: "…"}`) do not
become Lean `@[extern]`: in the proof extraction they are `axiom`s supplied by
the handwritten `handwritten_support/RiscvExtras.lean` through
`--lean-import-file`, which also installs a global
`macro_rules | `(tactic| decreasing_trivial) => `(tactic| decide)` (line 118;
kernel `decide`, not native). The 75 axioms (opencompl `RiscvExtras.lean:30ff`):
8 platform — `plat_term_write {α} : α → SailM Unit`, `plat_term_read`,
`load_reservation : Arch.pa → Nat → SailM Unit`,
`match_reservation : Arch.pa → Bool`, `cancel_reservation : Unit → SailM Unit`,
`valid_reservation : Unit → Bool`,
`get_16_random_bits : Unit → SailM (BitVec 16)`,
`sys_enable_experimental_extensions : Unit → Bool`; and 67 softfloat, e.g.
`riscv_f32Add : BitVec 3 → BitVec 32 → BitVec 32 → (BitVec 5 × BitVec 32)`.
Categories, call sites and backend emission are covered in package
`sail-riscv-lean-extraction-provenance-extern-axioms-and-privileged-config`.

#### 2.2 Which axioms are reachable from step-relevant roots

Basis: source + execution (approximate) + documentation
(`support/const_reach.py`, output `support/outputs/reach_summary.txt`; a
*textual over-approximation* of `collectAxioms`/`closureCorr`: declaration
chunks, identifier tokens with strings and comments stripped, short-name
matching)

| Model | Root(s) | Reachable decls | ~Body LOC | Reachable axioms |
|---|---|---|---|---|
| opencompl (full RV64D) | `try_step` (`Step.lean:417`) | 2,240 / 5,033 | 85,628 | **74** (all but the never-called `plat_term_read`) |
| opencompl | `execute` (`InstsEnd.lean:72012`) | 1,708 | 43,579 | 73 (67 float + `cancel_reservation`, `get_16_random_bits`, `load_reservation`, `match_reservation`, `plat_term_write`, `sys_enable_experimental_extensions`; `valid_reservation` is reached only via the `try_step` loop) |
| opencompl | `fetch, ext_decode, execute_SRET, trap_handler, exception_handler, translateAddr, doCSR, dispatchInterrupt` | 1,130 | 59,845 | 3: `get_16_random_bits` (via `doCSR` → Zkr `seed`), `plat_term_write` (HTIF write on the physical-memory path), `sys_enable_experimental_extensions` (via `hartSupports`) |
| opencompl | `execute_SRET` / `translateAddr` / `doCSR` / `ext_decode` | 249 / 351 / 661 / 432 | 2,626 / 4,296 / 27,275 / 31,594 | 1 / 2 / 2 / 1 |
| riscv-zkvm (scoped) | `try_step` | 990 / 3,621 | 15,295 | **6**: `get_16_random_bits, load_reservation, match_reservation, plat_term_write, sys_enable_experimental_extensions, valid_reservation` |
| riscv-zkvm | the 8-root set above | 790 | 12,790 | 3 |

Consequences: (i) because `execute` is one monolithic dispatch over every
compiled instruction, any theorem whose statement mentions the full model's
`try_step`/`execute` has all float axioms in its cone; (ii) a scoped extraction
removes the float axioms from the cone; (iii) the reservation axioms are
reached through generic load/store helpers in `VmemUtils.lean` even when no
A-extension instruction is compiled. riscv-zkvm's own kernel-level gate
`scripts/AxiomSweep.lean` (`allowedAxioms`) admits exactly `propext,
Classical.choice, Quot.sound, load_reservation, match_reservation,
plat_term_write, sys_enable_experimental_extensions` for its user-mode
equivalence theorems (`docs/validation.md:150-172`), consistent with its
theorem selection. The sibling package's cone table agrees with these numbers.

#### 2.3 Module closures vs. the `lean-miri` slice

Basis: source + execution (`support/import_closure.py`)

opencompl's root `LeanRV64D` closes over **124** of 160 files (36 files such as
`Eq`, `Ge`, `Lt`, `CsrEnd`, `ZbaInsts` are imported by nothing and not built);
`LeanRV64D.Step` closes over **118 modules / 159,385 LOC** (largest: `InstsEnd`
72,377; `ZicsrInsts` 22,303; `PlatformConfig` 11,215; `HexBits`/`HexBitsSigned`
~3.2k each); `LeanRV64D.Vmem` over 57 modules / 40,520 LOC. riscv-zkvm's
`RiscvZkvm.Sail` closes over 85 modules / 49,009 LOC and `RiscvZkvm.Sail.Step`
over **80 modules / 46,669 LOC** (its `InstsEnd` is 4,973 lines). The only
external imports are `Sail` and `Sail.Sail`. For comparison, the audited
`lean-miri` slice is 160 modules / 44,730 LOC (§1.4).

#### 2.4 Recursion, `noncomputable`, and configuration baked into the model

Basis: source + documentation

opencompl has 11 `termination_by` sites: 10 in `PlatformConfig.lean` (e.g.
`hartSupports` with measure `hartSupports_measure ext`, `:1317`) and 1 in
`Vmem.lean:368` (the page-table walk, measure `level.toNat`). Extension gating
(`hartSupports`/`currentlyEnabled`) and the PTW are therefore well-founded
definitions; they produce `isPartial` `*._unsafe_rec` compiler helpers (§2.5),
which Anneal already omits from replay. The generated model is
`noncomputable section` throughout (generation flag `--lean-noncomputable`);
riscv-zkvm records that "the proof extraction is `noncomputable`, so the Sail
decoder does not evaluate" (`docs/validation.md`, "Known gaps" item 3). The
supported-extension configuration is compiled into `hartSupports` match arms
(e.g. `| .Ext_Svnapot => ((true : Bool) && (xlen == 64))`,
`PlatformConfig.lean:1300-1318`), so the generator's JSON config is a semantic
input; riscv-zkvm pins it as `config_sha256`.

#### 2.5 `lean-sail` passes an Anneal-style census and replay

Basis: execution (`support/ReplayProbe.lean`, which mimics `importCorrEnv`,
the vendor inventory, and `replayCorrAndVendor`; output
`support/outputs/replay-headA.log`)

On `lean-sail` v10 (`Sail` root, 9 modules): 1,195 constants; 15 `isPartial`,
all `*._unsafe_rec` (e.g. `Sail.ArchSem.FreeM.bind`,
`Sail.ConcurrencyInterfaceV1.PreSail.readBytes`, `readBytesVec`,
`whileFuelM.go`, `untilFuelM.go`); 0 unsafe; 2 `opaque` (the
`initialize`-generated `ext`/`extProc` of the `simp_sail` attribute in
`Sail.Attr`); 0 axioms; 0 direct `sorryAx`; 0 compiler-reflection references;
axioms reachable from every non-partial constant =
`{propext, Classical.choice, Quot.sound}`; standalone replay of 1,180/1,180
non-partial constants onto a clean 2,356-module sysroot base in 273 ms.
lean-sail imports `Lean` (`Sail/Attr.lean`) and `Std.Tactic.BVDecide`
(`Sail/BitVec.lean`), so — like `lean-miri` — it needs the authenticated
`Lean.*` sysroot.

#### 2.6 Lean v4.34.1 compile and memory behavior

Basis: execution (`support/outputs/`)

- lean-sail v5 (`lean-toolchain` v4.29.0) compiles 8/8 modules on v4.34.1 with
  Anneal's exact vendor flags (`manual-v5.log`) and under `lake build`, with one
  new `linter.ambiguousOpen` warning at `Sail/Sail.lean:34:5`
  (`ls-v5-on-4341.build.log`).
- opencompl `LeanRV64D.Defs` (2,063 lines) and `LeanRV64D.RiscvExtras` compile
  on v4.34.1 against v5 **only with `-M ≥ 4096`**. At Anneal's vendor `-M2048`:
  `Defs.lean:1371:0: error: (kernel) excessive memory consumption detected`,
  repeated for every later declaration (`rv-defs-probe.log`); the errors begin
  at small two-constructor enums, consistent with a process-wide allocator
  budget rather than one large declaration (the 180-constructor `Register`
  inductive and derived instances precede them). At `-M4096`, `-M8192` and
  `-M16384` it succeeds; at `-M16384`: 53.6 s wall, peak RSS 2,469,224 KB,
  `.olean` 33,851,104 bytes (`rv-defs-rss.log`, `rv-defs-probe-M16384.log`).
- Census + replay of `Defs` + `RiscvExtras`: 9,755 constants; 0 partial; 0
  unsafe; 0 opaque; **75 axioms**; all 9,755 replay standalone in 3.4 s
  (`replay-rvdefs.log`).

#### 2.7 `.olean` SHA-256 reproducibility depends on flags, not paths or `-M`

Basis: execution (`support/outputs/olean_hashes.txt`)

Same toolchain and flags in two different directories give byte-identical
`.olean`s (lean-sail v10, Anneal flags: 9/9; `lake build`: 9/9). Byte-identical
sources in the v5 and v10 trees (`BitVec`, `IntRange`, `Attr`, `Sail`) built in
different directories give identical hashes (e.g. `Sail/BitVec` `573a1f77…`).
The `-M` value does not change the hash (`Defs` `13b16712…` at
4096/8192/16384). But **Lake-built and Anneal-flag-built `.olean`s of the same
source differ** (9/9; e.g. `Sail/BitVec` lake `b3d8353d…` vs. `573a1f77…`).

#### 2.8 Build-cost data

Basis: documentation + execution

opencompl commits `build_log.txt` from its generation run (environment
unrecorded): 135 jobs (10 lean-sail + 124 model modules, matching the root
closure), serial per-module sum 300.4 s; `InstsEnd` 86 s, `PlatformConfig` 33 s,
`ZicsrInsts` 31 s, `Defs` 20 s; the `Step` closure modules sum to ~291 s. The
Anneal-flag compile of `Defs` took 53.6 s (2.7× the log's figure; flags
`-j1 -DElab.async=false` and host differ). No examined clone contains `.lake/`.
riscv-zkvm publishes `riscv-zkvm-oleans.tar.gz` (`preferReleaseBuild`), but
those are Lake-flag `.olean`s, which by §2.7 cannot satisfy Anneal-flag digest
pins.

#### 2.9 A latent `bv_decide` trip-wire, and why only an axiom allowlist catches it

Basis: source + execution (`support/BvDecideAxiom.lean`, output
`support/outputs/BvDecideAxiom.out`)

lean-sail's `match_bv` elaborator discharges side conditions with
`` `(fun _ => by try bv_decide -enums) `` (`Sail/BitVec.lean:231`). A
successful `bv_decide` does **not** leave a reference to `Lean.ofReduceBool` in
the proof: `Lean.Meta.nativeEqTrue` (leanprover/lean4 `5045d005…`,
`src/Lean/Meta/Native.lean:37-86`; docstring: "It is the basis for
`native_decide` and `bv_decide` tactics") compiles and evaluates the decision
procedure and then adds a fresh axiom `<thm>._native.<tactic>.ax_*` asserting
`e = true`. Probe on v4.34.1:
`theorem bv_probe (x y : BitVec 8) : x ^^^ y ^^^ y = x := by bv_decide`
`depends on axioms: [propext, Classical.choice, Quot.sound, bv_probe._native.bv_decide.ax_1_5]`;
the theorem value directly references that axiom, and no `bv_probe*` constant
directly references `Lean.ofReduceBool`. Anneal's "vendor cannot declare axiom"
rule (and any axiom allowlist) would reject such a constant. A denylist
containing only `Lean.ofReduceBool` — e.g. `forbiddenVendorCompilerRefs` taken
alone — would not. opencompl's generated model contains no `match_bv` (0
files); per the sibling package, the Sail backend emits `match_bv` only under
`--lean-matchbv`, which is off by default.

### 3. Derived requirements for a Sail-backed reference audit

All of §3 is **derived** (reasoning from §1–§2), not an observed fact.

**3.1 Shape.** Mirror Pass 2 with a second vendor root containing (a) the
pinned lean-sail runtime sources (they are in the replay set and the cone) and
(b) a *scoped, regenerated* extraction; add `trusted/correspondence/` adapters
(an RV reference state, a codec, and a reference step wrapping Sail
`try_step`/`run_hart_active` or per-phase functions) and `correspondence/`
proofs of behavior/divergence/fault equivalence through a one-to-one
`SimulationInv` between a small kernel-reducible trusted RV64 S-mode model and
Sail's `SequentialState`
(`regs : Std.ExtDHashMap Register RegisterType`, `mem : Std.ExtHashMap Nat (BitVec 8)`,
`choiceState`; lean-sail v5 `Sail/ConcurrencyInterfaceV1.lean:101-110`). As with
`lean-miri` (§1.8), the reference machine would be "Sail step + Anneal
adapter", and the adapter remains human-audited TCB.

**3.2 Pin schema additions.** Because the Lean is generated, the pin must cover
generator inputs as well as bytes: `sail_riscv {repo, tag, rev}`,
`sail_compiler {version, rev}`, `lean_sail {repo, rev}`,
`upstream_lean_toolchain` vs. `build_lean_toolchain`, the exact generation argv
(`--lean-noncomputable…`, `--lean-import-file`, scope list), config file +
sha256 (§2.4), normalizer/patch digests, `vendor_tree` + manifest digest,
`patched_files` (at least `RiscvExtras.lean`), a topologically ordered closure
with `.olean` digests, and **the compile flags that define those digests**
(§2.7). `-M` must be raised (§2.6); opencompl's lakefile also passes
`--tstack=400000`, and whether that is needed was not tested. TCB constants
would lock the pin digest, the upstream revisions, and the patch allowlist. A
byte-for-byte regeneration job (riscv-zkvm `regen-model.sh --check` pattern;
Sail + OCaml + Z3, documented as needing ~8 GiB) ties the checked-in Lean to
official Sail; without it, that link is documentary.

**3.3 Closure computation.** Do not rely on module slicing of the full RV64D
model (118/124 modules for one step, §2.3). Scope the extraction; riscv-zkvm's
module list plus what an S-mode kernel needs (e.g. `Zifencei`; `Zalrsc` only if
LR/SC is required) should give a slice near riscv-zkvm's size (~80–90 modules /
47–50k LOC; `try_step` cone ~1k declarations) — an estimate, since no S-mode
scope was generated. The auditor should compute the import closure from the
root `.olean` and require equality with the pinned list (today it only
enumerates, §1.4). Cone roots should be exactly the Sail functions the adapter
calls.

**3.4 Patch policy per axiom class.** Anneal rejects *any* vendor axiom (§1.7),
so all 75 must disappear from the vendored `RiscvExtras.lean` by recorded
patch:

| Class | Count | Policy | Note |
|---|---|---|---|
| softfloat `riscv_f*` | 67 | delete after scoping out F/D/Zfh/V | a leftover reference then fails to compile (fail-closed) |
| `sys_enable_experimental_extensions` | 1 | `def … := false`, matched to the pinned config | pure configuration |
| `plat_term_write` / `plat_term_read` | 2 | no-op definitions (`pure ()`) or `choose`-based ones | console only; `plat_term_read` is never called |
| `get_16_random_bits` | 1 | define via the monad's choice source, `PreSail.choose (.bitvector 16)` (`Sail.Primitive.bitvector` exists, lean-sail v5 `Sail/Common.lean:284-291`) | entropy becomes an explicit, universally quantifiable oracle |
| `load_reservation`, `cancel_reservation` | 2 | monadic; definable | — |
| `match_reservation`, `valid_reservation` | 2 | **open seam** | declared `pure` in Sail (`model/sys/sys_reservation.sail`, identical at `0.13.1` and HEAD) |

Because `val match_reservation = pure {…} : physaddrbits -> bool` and
`val valid_reservation = pure {…} : unit -> bool`, no Lean definition, and no
single global `axiom`/`opaque`/parameter, can make SC success depend on an
earlier LR within one execution. Options: change Sail to make them impure and
stateful; patch the SC path to an impure `choose`-based outcome (a sound
over-approximation the trusted model must mirror); or define them constantly
and have the trusted model fail closed on LR/SC. The sibling package reaches
the same conclusion about this seam. Do not reuse upstream
`RiscvExtrasExecutable.lean`: its `panic "TODO: …"` bodies reduce to `default`
in the kernel, silently fixing arbitrary semantics. Keeping externs
uninterpreted and stating the correspondence ∀-quantified over admissible
platform oracles would need backend support (or a large signature-threading
patch) and a policy carve-out for allowlisted platform `opaque` constants,
because the cone check rejects vendor `opaque`.

**3.5 What would trip `partial`/`unsafe`/axiom rejection.** Current artifacts
trip nothing (§2.1, §2.5): `_unsafe_rec` helpers are omitted from replay, the
one lean-sail `partial def` is unreachable, and `noncomputable section` and
`set_option maxHeartbeats` are tolerated in vendor code because vendor code is
not syntactically preflighted (they must not migrate into
`trusted/correspondence/`). Future trip-wires: any generated `match_bv` whose
`bv_decide` succeeds (§2.9); emitting `partial` via `--lean-partial-function`;
platform shims written as `opaque`/`implemented_by`.

**3.6 Toolchain portability.** lean-sail v5 and opencompl `Defs`/`RiscvExtras`
compile on v4.34.1 (§2.6). Not covered by these probes: opencompl has 74 files
containing the word `assert` (`grep -lw`) (`Defs`/`RiscvExtras` contain none), and the
sibling package documents that pre-2026-10-14 extractions' `assert c m`
collides with Lean ≥ 4.34's built-in `assert`. Sail `sail2` HEAD now targets
v4.34.1, lean-sail v10, and the V2/ArchSem interface, which no published
extraction uses yet; lean-sail v10's `FreeM.bind` is well-founded (§2.5), which
is fine for replay but blocks kernel reduction. Follow the `lean-miri`
precedent (§1.9): pin both toolchains, build under v4.34.1, and do not transfer
upstream test results.

**3.7 Effort and risk (judgement; assumptions: reuse of Anneal's Pass 2 code,
the scoped extraction of §3.3, no Sail-backend change).**
- Audit plumbing (second vendor root, origin class, pin parser and locks,
  closure equality, per-vendor flags and `-M`, cone roots, negative tests):
  ~2–4 engineer-weeks, medium risk. For scale, the `lean-miri` Pass 2 commit was
  +16,081/−2,228 lines over 15 files.
- Pinned scoped regeneration + `RiscvExtras` patch + regeneration CI job:
  ~1–2 weeks, medium risk (Sail / lean-sail / Lean version triad).
- S-mode correspondence proofs (fetch, decode, the execute subset, CSR — the
  `doCSR` cone is ~27k body LOC in the full model — trap entry, `sret`, Sv39
  PTW, interrupts): several person-months, high risk. riscv-zkvm's
  user-level-ISA-only forward simulation (executed in M-mode with bare
  translation and PMP off; no privilege, CSR or trap coverage; see package
  `riscv-privileged-isa-model-correspondence-prior-art`) spans 24 `SailEquiv`
  files for 51 instructions and
  still leaves decode and its interpreter untied (`docs/validation.md` known
  gaps 3–4). Risk comes from `ExtHashMap`-based state, well-founded
  `hartSupports`, and huge decoders.
- Cold CI: serial `-j1` per-module compile plus replay; scaling the 300 s
  serial log by the observed 2.7× gives ~13–14 min for the full model and
  perhaps ~4–6 min for a riscv-zkvm-sized scope (assuming similar per-LOC
  cost).

## Boundaries

- **Not examined:** a build of the full opencompl model or of any scoped
  S-mode extraction under Anneal flags; running `anneal-audit` itself;
  bubblewrap-sandboxed compilation of any Sail artifact; `.olean`
  reproducibility across hosts or CPU architectures; the sail-riscv HEAD
  (V2/ArchSem) Lean output; whether `--tstack=400000` is required under Anneal
  flags.
- **Unknown:** the exact constant-level cones (§2.2 is textual; precise cones
  need a built model); the `-M` needed for `InstsEnd` and other large modules;
  whether the 74 opencompl modules that use `assert` compile on v4.34.1 with
  lean-sail v5; which replayed-declaration count (38,728 vs. 38,718) is correct
  for `c131b320`.
- **Known not to apply:** module-level slicing of the full RV64D model to a
  step-sized slice (118/124 modules needed); `RiscvExtrasExecutable.lean` as a
  faithful axiom replacement (`panic` = `default` in the kernel); riscv-zkvm's
  release `.olean` archive as a way to satisfy Anneal-flag digest pins (Lake
  flags give different hashes); any Lean definition or global oracle as a fix
  for the reservation seam (the Sail functions are pure).
- **Unsupported:** Anneal's Pass 2 has no notion of a second vendor root; it
  hard-codes `Miri.*` names, exactly 160 entries, and the `lean-miri` locks.
- **Stronger conclusions not established:** that the scoped riscv-zkvm
  extraction is sufficient for an S-mode kernel (no Zifencei, no A, no S-mode
  correspondence work); that passing Pass 2-style checks would establish
  fidelity to the RISC-V ISA (it establishes kernel-checked equivalence to the
  *pinned reference*, given a human-audited adapter); that lean-sail v5 plus
  every generated module is v4.34.1-clean; that the effort figures are
  measurements (they are judgement).

## Evidence

Observation date for all execution: 2026-11-20. Lean v4.34.1
(`5045d0056413266e57c625dcd7c365b10e377c52`, Release, x86_64 Linux), run under
a memory-bounded wrapper.

**Anneal (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
`trusted/audit/src/lib.rs:123-157` (locks), `602`, `2165-2180` (inspector
invocation), `2815-2854`, `2856-3065`, `3067-3354`, `3403-3465`, `3596-3830`
(bwrap arguments), `4060-4148` (`UpstreamPin`), `4150-4522`
(`verify_upstream_pin`); `trusted/audit/TrustedBoundary.lean:422-428`,
`1036-1049`, `1108-1124`, `1182-1207`, `1316-1365`, `1604-1758`, `1760-1809`,
`1821-2088`, `2121-2273`, `2311-2333`;
`trusted/correspondence/Trusted/Correspondence.lean:2219`, `2402-2488`,
`2541-2620`; `trusted/lean/foundation-lock.json` (`axioms`);
`vendor/lean-miri/UPSTREAM_PIN.json` (closure line 4, `patched_files` line 812,
`upstream_pins` line 890, `vendor_tree` line 931);
`docs/trust-model.md:52-53`, `204-271`, `316-508`;
`docs/mir-correspondence-design.md:514-648`; `AGENTS.md:141-196`, `204-265`,
`406-411`; `.github/workflows/ci.yml:272-283`, `423-439`; commit
`ec77c1a2f3a8d2090e650a3c46d291f316e2bad6`.

**Sail side:** opencompl/sail-riscv-lean `51c635c4…`
(`LeanRV64D/RiscvExtras.lean`, `Step.lean:332,417`, `InstsEnd.lean:72012`,
`Vmem.lean:368,518`, `PlatformConfig.lean:1300-1318`, `ZicsrInsts.lean:22241`,
`build_log.txt`, `lakefile.toml`, `lake-manifest.json`); lean-sail `e4745c82…`
(v10) and `07946313…` (v5) (`Sail/BitVec.lean:202-231`,
`Sail/ConcurrencyInterfaceV1.lean:101-110,132-166`, `Sail/Common.lean:284-291`,
`Sail/Attr.lean`); riscv-zkvm `6810fc14…` (`sail-import/PROVENANCE.toml`,
`scripts/regen-model.sh`, `scripts/check-model-pin.sh`,
`scripts/AxiomSweep.lean`, `sail-import/RuntimeCompat.lean`,
`docs/validation.md`); sail-riscv `27224ccb…` and `ec5200bd…`
(`model/sys/sys_reservation.sail`, `handwritten_support/RiscvExtras.lean`,
`handwritten_support/RiscvExtrasExecutable.lean` at HEAD); leanprover/lean4
`5045d005…` (`src/Lean/Meta/Native.lean:37-86`, `src/Lean/Replay.lean`).

**Support material (`support/`; `$CLONES` = directory holding the clones,
`$WORK` = scratch directory; Lean = v4.34.1):**

| Probe | Command | Key output |
|---|---|---|
| `anneal_pin_facts.sh` | `support/anneal_pin_facts.sh <anneal-clone>` | `outputs/anneal_pin_facts.out`: pin sha `b629a9b4…`, 160 entries, closure LOC 44,730, construct counts |
| `count_constructs.py` | `python3 -B count_constructs.py sail-riscv-lean=$CLONES/sail-riscv-lean:LeanRV64D riscv-zkvm-Sail=$CLONES/riscv-zkvm:RiscvZkvm/Sail lean-sail-v5=<v5 tree> lean-sail-HEAD=$CLONES/lean-sail` | `outputs/counts.txt` |
| `import_closure.py` | `python3 -B import_closure.py $CLONES/sail-riscv-lean LeanRV64D.Step --list` | `closure_modules=118 of 161 in-tree; LOC=159385` |
| `const_reach.py` | `python3 -B const_reach.py $CLONES/sail-riscv-lean/LeanRV64D try_step --files` (add `--path <name>` for a witness chain) | `outputs/reach_try_step.txt`, `outputs/reach_summary.txt` |
| `anneal_style_compile.sh` | `anneal_style_compile.sh <lean> <src-root> <out> <extra-LEAN_PATH or -> <MiB> <Module>…` (Anneal vendor flags, no sandbox) | `outputs/manual-head.log`, `manual-headB.log`, `manual-v5.log`, `rv-defs-probe.log` (`-M2048` failure), `rv-defs-probe-M16384.log` |
| `/usr/bin/time -v` around the `Defs` compile | see `outputs/rv-defs-rss.log` | `Maximum resident set size (kbytes): 2469224` |
| `ReplayProbe.lean` | `lake env lean --run ReplayProbe.lean Sail Sail` (in a lean-sail v10 build); `LEAN_PATH=<sail-out>:<rv-out> lean --run ReplayProbe.lean LeanRV64D LeanRV64D.RiscvExtras` | `outputs/replay-headA.log`, `outputs/replay-rvdefs.log` |
| hash table | sha256 of the outputs above | `outputs/olean_hashes.txt` |
| `BvDecideAxiom.lean` | `lean BvDecideAxiom.lean` | `outputs/BvDecideAxiom.out` |
| lake builds | `lake build Sail SailTest` | `outputs/ls-headA.build.log`, `outputs/ls-v5-on-4341.build.log` |

Source files compiled by the probes were copied unmodified from the subjects
above; the v5 port changed only `lean-toolchain` to `leanprover/lean4:v4.34.1`.

## Revalidation

- **Anneal mechanism:** run `support/anneal_pin_facts.sh` on a newer Anneal
  revision and diff `trusted/audit/src/lib.rs` (`verify_upstream_pin`,
  `verify_and_stage_miri_entries`, `build_bwrap_miri_compile_args`) and
  `TrustedBoundary.lean` (`verifyAndCollectCorrLocals`, `closureCorr`,
  `verifyMiriExecutionMachineCone`, `replayCorrAndVendor`,
  `verifyCorrespondenceClaims`). Changes in pin schema, flags, roots, or axiom
  policy invalidate §1.
- **Sail census and axioms:** rerun `count_constructs.py` and `const_reach.py`
  on a new extraction; `grep -c '^axiom' RiscvExtras.lean`.
- **Toolchain/memory:** rerun `anneal_style_compile.sh` on `Defs` at `-M2048`
  and `-M4096` for the new toolchain or extraction. For a regenerated scoped
  model, compile the whole closure in topological order and run
  `ReplayProbe.lean` with the model prefix — the minimum check of §3.3/§3.5.
- **`.olean` reproducibility:** build the same sources in two directories (and
  on a second host or architecture) with identical flags and compare SHA-256.
- **`bv_decide` behavior:** rerun `BvDecideAxiom.lean` on the new Lean
  toolchain.
