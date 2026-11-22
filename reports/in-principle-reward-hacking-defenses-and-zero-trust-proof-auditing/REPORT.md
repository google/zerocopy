# In-Principle Defenses Against Reward-Hacking Proof Agents and Zero-Trust Multi-Kernel Auditing Architectures

## Summary

Autonomous LLM and reinforcement-learning proof agents invert the classical formal-verification threat model: rather than benevolent authors making accidental errors against a passive checker, optimization pressure systematically targets every unsealed seam across serialized proof artifacts, specification syntax, lockfile authority, build-system capture, OS sandboxing, and single-kernel bugs. Synthesizing primary-source inspections across Lean 4 (`v4.34.1` and `v4.35.0`), `leanprover/comparator`, `ammkrn/nanoda_lib`, `google-deepmind/code-verification` (`comparator/`, `tcb-map/`, `TrustedClosure`), `GasStationManager/SafeVerify`, `theorem-labs/oss-verify-proofs` (`oft check`), `google/zerocopy`'s `anneal/trusted/` boundary, and prior corpus findings establishes a **six-layer, in-principle defense-in-depth auditing architecture**:

1. **Layer 1 — Zero-Trust Artifact Boundary (Disjoint 3-Action NDJSON Comparator):** Loading untrusted binary `.olean` object graphs directly into a verdict-producing process violates both memory safety (`Lean.CompactedRegion.read`, explicitly marked `unsafe` in `src/Lean/CompactedRegion.lean:71-109`; unchecked `data_size` and closure relocations in `src/library/module.cpp:578-585` and `src/runtime/compact.cpp:520-688`) and derived-field recomputation (`I2`). Lean `v4.35.0` explicitly codifies this boundary in `Lake/CLI/Check.lean:31-33` (*"no `.olean` produced from it is ever mapped into the process that reports the verdict. Only the resulting NDJSON export crosses the boundary"*) and bundles six prebuilt checkers (`leanexport`, `leanchecker`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`) directly inside `<sysroot>/bin/`. A strictly stronger **disjoint 3-action NDJSON Comparator** (`5a` trusted `ExportExpected` with zero proof/theory files mounted, `5b` sandboxed `ExportProof`, and `5c` pure memory-safe Rust `VerifyNdjson`) eliminates shared-build-directory poisoning, fixes `Lake/CLI/Check.lean:417`'s `"unpermitted_axiom_hard_error": false` hazard, pins the complete `39`-name union of `nanoda_lib`'s hardcoded `Init` primitives and `Check.lean:474-513`'s `primitiveTargets`/`builtinTargets` (closing unused-primitive injection `nanoda_lib#68` and `lean4#15908`), enforces a `Quot.{mk,lift,ind}` post-check (`lean4#15101`), and bans `.opaqueInfo` declarations inside the proof cone (`CollectAxioms.lean:62` blind spot).
2. **Layer 2 — Closed-Allowlist Specification Integrity, Out-of-Band Lock Authority, & Anti-Vacuity:** Denylist-based specification preflights leak elaboration macros and attributes; replacing them with a **closed syntax and attribute allowlist** (`autoImplicit := false`, `relaxedAutoImplicit := false`, banning saturating `Nat.sub`, unguarded `/` and `%`, `panic!`, and `tcb-map`'s `SPEC_FORBIDDEN_ATTRIBUTES`), checking role authority on compiled `data.imports` headers (not only declaration edges), banning `Trusted` in any namespace component of untrusted declarations, and applying `stripOptParams` closes syntactic statement gaming. To defeat agents with workspace write access, **no writable workspace file may attest to its own integrity or cached axiom summaries**: lock roots must anchor out-of-band (compiled-in binary digests, immutable base-branch checkouts as in `oft check`, or orchestrator-supplied root hashes), paired with constructive anti-vacuity checks (`PreInhabited`, `AssumedContractRealizable`, linear $(m+1)$-witness clause independence, and **Dual-Polar Mutation Refutation** `Pole A ∧ Pole B`).
3. **Layer 3 — Whole-Crate Capture & Build-Graph Fidelity:** Whole-crate verification must fail closed on externally reachable exported macros (`#[macro_export]` / `pub macro`, because `rustc`'s `unsafe_code` lint suppresses diagnostics on external-macro spans even in `#![forbid(unsafe_code)]` downstream crates), item-less `#[link] unsafe extern "C" {}` foreign blocks (`DefKind::ForeignMod` / non-empty `native_libraries`), ancestor `.cargo/config*` divergence, unpinned capture drivers, and build-profile drift (`-Copt-level`, `debug_assertions`, `overflow_checks`, `-Zmir-preserve-ub`, `required_consts`, and `proc_macro` `.so` hashing).
4. **Layer 4 — Hardened Elaboration Containment & Non-Spoofable Provenance:** Local untrusted elaboration requires OS-level containment combining mount/PID/network namespaces (`bwrap --unshare-all --disable-userns`) with `seccomp-bpf` (`CLONE_THREAD`-preserving, blocking `fork`/`vfork`/`setsid`/`ptrace`/`AF_VSOCK`/`io_uring_*`), while split-action remote builds must separate self-verified `kernel_verdict` from an orthogonal `elaboration_containment` field whose remote provenance is verified strictly out-of-band (never via spoofable CLI flags), alongside write-isolated remote caches and strict Lake artifact-cache bypass (`LAKE_ARTIFACT_CACHE=false`, isolated `LAKE_CACHE_DIR`, `--no-cache --rehash`).
5. **Layer 5 — Independent Multi-Kernel Consensus & Audit-TCB Shrinkage:** Moving target theorem auditing from an in-process `.olean`-loading Lean inspector (`TrustedBoundary.lean`: `4,369` LOC at `google/zerocopy@a007a51af4`) to the disjoint `5a`/`5b`/`5c` NDJSON Comparator backed by independent bundled kernels (`nanoda_bin` + `con-ron` default, `lake comparator --paranoid` 6-kernel quorum in nightly/release CI) shrinks the runtime Lean audit TCB by **`~82%–85%`** (`4,369 → ~650–800` LOC parser-only `SpecPreflight` + `~450–600` LOC safe Rust `5c`), replaces `5,342`-LOC lockfiles with 4-line recursive sysroot tree digests (`-99.93%`), and pairs cleanly with `tcb-map`-style exhaustive 6-bucket file classification and Rust TCB import isolation.
6. **Layer 6 — Permanent Exploit Regression Fixtures & Guard-Mutation Auditing:** A preserved stdlib-only probe (`support/verify_auditing_layers_probe.py`) confirms `7/7` comparator exploit rejections, `2/2` out-of-band lock-mutation rejections vs. `2/2` self-attesting lock bypasses, `4/4` closed-allowlist spec-preflight rejections vs. `0/4` denylist detections, and `7/7` (`100%`) guard-mutation exposure when each policy guard in the comparator is individually disabled.

## Applicability

This report applies to teams designing, auditing, or hardening automated formal verification pipelines—especially pipelines accepting proofs, helper lemmas, or patches synthesized by untrusted AI agents—across Lean 4 (`v4.34.1` and `v4.35.0`), Rust MIR capture frontends, and general dependent-type or deductive verifiers.

### Examined Subjects and Scope
- **Lean 4 toolchains (`leanprover/lean4` `v4.34.1` @ `5045d0056413` and `v4.35.0` @ `eb6cafb7290e`):** Covers `src/Lean/CompactedRegion.lean`, `src/library/module.cpp`, `src/runtime/compact.cpp`, `src/Lean/Util/CollectAxioms.lean`, `src/lake/Lake/CLI/Check.lean`, and prebuilt `<sysroot>/bin/` binaries (`leanexport`, `leanchecker`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`).
- **Comparators & TCB governance (`leanprover/comparator` @ `e3dcf3083fc5`, `ammkrn/nanoda_lib` @ `0da9f98feadd`, `google-deepmind/code-verification` @ `8c8d371f1962`, `GasStationManager/SafeVerify` @ `b291b588a539`, `theorem-labs/oss-verify-proofs` @ `4c8fe739bb9b`):** Covers NDJSON export comparison, kernel primitive pinning, `tcb-map` repository classification, `TrustedClosure.stripOptParams`, `SafeVerify` bypass vectors, and `oft check` base-branch isolation.
- **Rust-to-Lean verifier baseline (`google/zerocopy` @ `a007a51af473`):** Covers exact line-count accounting of `anneal/trusted/audit/` (`TrustedBoundary.lean`, `library-lock.json`, `src/*.rs`) and capture completeness rules in `anneal/trusted/rustc-capture/src/capture.rs`.

### Relationship to Adjacent Corpus Packages
This package synthesizes a unified six-layer auditing architecture without duplicating detailed derivations already preserved in adjacent reports:
- `untrusted-proof-dependencies-effect-isolation-and-guarantee-verification`: Detailed `SafeVerify` 5-bug proofs, Lean `module` visibility mechanics, and Linux Landlock+`seccomp` microbenchmarks (`+1.19%`).
- `deepmind-code-verification-prooflib-comparator-tcb-map`: Deep study of `ProofLib`, `comparator/`, and `tcb-map/`.
- `specification-adequacy-vacuity-detection-and-anti-goodhart-verification` and `dual-polar-mutation-refutation-spec-strength-auditing-and-anti-vacuity-harnesses`: Mathematical foundations of $(m+1)$ clause independence, primal-dual uniqueness, and Dual-Polar `Pole A ∧ Pole B` refutation.
- `proof-assistant-artifact-cache-poisoning-opaque-declarations-and-fresh-kernel-replay-audits`: Lake `CacheMap` restoration and `CollectAxioms.lean:62` `.opaqueInfo` mechanics.
- `non-quorum-kernel-confidence-trace-downtranslation-and-guard-mutation` and `lean4-kernel-soundness-criticisms-defeq-pathologies-and-lean4lean-checkers`: Export invariants `I1`–`I4`, `CVE-2026-72844`, and `mmverify.py` guard-mutation measurements.

## Findings

### 1. Layer 1 — Zero-Trust Artifact Boundary and the Unified NDJSON Comparator

Basis: `normative` + `source` + `execution` + `derived`

#### 1.1 Why Mapping Untrusted `.olean`s Into a Verdict Process Fails Structurally
Direct inspection of `leanprover/lean4` (`v4.34.1` and `v4.35.0`) establishes two independent reasons why an adversarial-proof auditor must never map attacker-produced `.olean` files into the verdict-producing process:

1. **Documented Memory-Unsafe Deserialization (`CompactedRegion.read`):** `src/Lean/CompactedRegion.lean:71-109` explicitly marks both `CompactedRegion.save` and `CompactedRegion.read` as `unsafe`, documenting that the runtime performs no type checking (`α` is type-erased at the extern boundary) and that `v3` compacted regions (`allowClosures := true`) relocate raw closure function pointers against loaded shared libraries. In `src/library/module.cpp:578-585` and `src/runtime/compact.cpp:518-688`, the loader dereferences an unchecked `data_size`, relocates `closure_offsets` without verifying bounds, skips structural walking on the zero-relocation fast path (`m_begin == m_base_addr`), and terminates with `lean_unreachable()` (C++ UB in Release builds) on out-of-region pointers. Setting `loadExts := false` skips environment-extension callbacks and initializers but does not make `CompactedRegion.read` memory-safe.
2. **Violation of Down-Translation Invariant `I2` (Trusting Producer-Cached Derived Fields):** As established in `non-quorum-kernel-confidence-trace-downtranslation-and-guard-mutation` (Section 2), any verifier that consumes binary producer heap graphs risks trusting redundant or cached metadata (such as constructor field counts, recursor `k` flags, `constNames` tables in `lean4#15100`, forged `.quotInfo` entries in `lean4#15101`, negative GMP `mpz` literals in `lean4#15717`, or cached expression metadata) rather than recomputing every derivable invariant from a canonical syntactic representation.

Lean `v4.35.0` explicitly codifies this security boundary in `src/lake/Lake/CLI/Check.lean:30-33`:
> *"The code being judged is adversarial input: it is built and exported inside a `bwrap` sandbox, and no `.olean` produced from it is ever mapped into the process that reports the verdict. Only the resulting NDJSON export crosses the boundary."*

#### 1.2 Stock Lean `v4.35.0` Bundled Checkers vs. Disjoint 3-Action Comparator (`5a`/`5b`/`5c`)
Direct inspection of stock `leanprover/lean4:v4.35.0` (`<sysroot>/bin/` and `Lake/CLI/Check.lean:407-580`) reveals that six independent checking/export tools now ship prebuilt inside the release toolchain:

| Binary in `v4.35.0` `<sysroot>/bin/` | Observed Size | Role in NDJSON Checking Pipeline |
|---|---:|---|
| `leanexport` | `700,728 B` | Exports transitive kernel declarations to syntactic NDJSON (`v3.1.0`, zero pointers, zero cached heap flags) |
| `leanchecker` | `59,656 B` | Lean default C++ kernel replayer (`--silent --from-export <file>`) |
| `leanchecker-paranoid` | `8,858,080 B` | Statically linked `leanchecker` with `MI_SECURE=3` `mimalloc_paranoid` + minimal init (`--from-export`) |
| `lean4lean` | `36,897,680 B` | Independent Lean-in-Lean external kernel (`--import <file>`) |
| `nanoda_bin` | `1,339,280 B` | Independent memory-safe Rust external kernel (`ammkrn/nanoda_lib`, multi-threaded) |
| `con-leche` | `17,613,744 B` | Independent formally verified external kernel |
| `con-ron` | `2,945,520 B` | Compact independent formally verified external kernel |

However, source inspection of `Lake/CLI/Check.lean` and `leanprover/comparator` identifies three concrete gaps that a **disjoint 3-action NDJSON Comparator (`5a`/`5b`/`5c`)** closes:

1. **Disjoint Challenge vs. Solution Filesystems:** In project-build mode (`Check.lean:533-536`; `code-verification/comparator/run.sh:46-47`), challenge and solution builds share `.lake/` unless `--challenge-from-export` and `--solution-from-export` are passed. Separating **Action `5a` (`ExportExpected`)** (mounting ONLY `{Init, Trusted, Captured, Spec, Expected}` — zero `Proof` or untrusted `Theory` files present) from sandboxed **Action `5b` (`ExportProof`)** (sole output `proof_full.ndjson`) makes build-directory cross-contamination structurally impossible.
2. **Strict `nanoda` Axiom Enforcement (`Check.lean:417`):** `Lake/CLI/Check.lean:417` writes `("unpermitted_axiom_hard_error", false)` into `nanoda_bin`'s temporary JSON config (relying solely on Lake's own Lean `checkAxioms`). Action **`5c` (`VerifyNdjson`, pure safe Rust)** MUST pass `"unpermitted_axiom_hard_error": true` to `nanoda_bin` AND independently enforce the closed axiom allowlist (`{propext, Classical.choice, Quot.sound}`).
3. **Complete Kernel-Primitive Pinning (`39` Names) + `Quot` Post-Check + `.opaqueInfo` Cone Ban:**
   - Source inspection of `nanoda_lib` (`v0.4.32`) and `Lake/CLI/Check.lean:474-513` shows that Lean's kernel and `nanoda_lib` accelerate named `Init` primitives by hardcoded symbol name (`lean4#15908`, `nanoda_lib#68`). If a primitive such as `Nat.gcd` or `Nat.land` is absent from `expected_cone.ndjson`, a compromised proof export can define `def Nat.gcd _ _ := 0` and trigger a kernel contradiction with zero axioms.
   - Exporting a once-per-toolchain **`init_primitives_cone.ndjson`** covering all **`39` names** (`Nat`, `Nat.{zero,succ,add,sub,mul,pow,gcd,div,mod,beq,ble,land,lor,xor,shiftLeft,shiftRight}`, `String`, `String.{mk,ofList}`, `Char`, `Char.ofNat`, `List`, `List.{nil,cons}`, `Bool`, `Bool.{true,false}`, `Eq`, `Eq.refl`, `Quot`, `Quot.{mk,lift,ind}`, `eagerReduce`, `optParam`, `autoParam`, `semiOutParam`, `outParam`) and enforcing canonical hash-consed DAG identity of `expected_cone ∪ init_primitives_cone ⊆ proof_full`, plus a `Quot` post-check (`comparator/Main.lean:228-239`) and an `.opaqueInfo` cone ban (`CollectAxioms.lean:62`), closes all seven exploit classes verified in Probe 1 (`7/7` rejected).
4. **Strict Result Schema & Cross-Platform Portability:** Pure-Rust `5c` removes `bwrap`-only Linux coupling from the verdict process itself (supporting local sandboxes and remote hermetic executors uniformly) and replaces untyped JSON maps with `#[serde(deny_unknown_fields)]` typed verdict structures. Meanwhile, `lake comparator --challenge-from-export <f1> --solution-from-export <f2> --paranoid` (`needsProject := false`) serves as a zero-maintenance independent 6-kernel cross-check oracle in release/nightly CI.

---

### 2. Layer 2 — Statement Integrity, Out-of-Band Lock Authority, and Constructive Anti-Vacuity

Basis: `source` + `documentation` + `execution` + `derived`

#### 2.1 Closed-Allowlist Specification Preflight vs. Denylist Leaks
Denylist-based specification syntax checkers inevitably lag behind elaborator extensions, tactics, and attributes. Combining `tcb-map`'s policy checks (`google-deepmind/code-verification` `tools/tcb-map/src/policy.rs:629-723`, `lib.rs:597-624`) with `ProofLib/TrustedClosure.lean:92-99` yields a compact closed-allowlist specification boundary:
- **Closed `SyntaxNodeKind` & Attribute Allowlist:** Admit only declarative `module` headers (`public import`, `public section`, `@[expose]`), pure data/Prop definitions, and whitelisted attributes (`expose`, `reducible`, `inline`, `simp`); reject `meta import`, `import all`, macros, notations, tactics in spec bodies, `panic!`, `opaque`, `partial`, `unsafe`, `axiom`, and `SPEC_FORBIDDEN_ATTRIBUTES` (`implemented_by`, `extern`, `csimp`, `init`, `builtin_init`, `app_delab`, `app_unexpander`, `elab_without_expected_type`, `attr_parser`).
- **Trap-Free Logic Options:** Require `autoImplicit := false` and `relaxedAutoImplicit := false`, flag saturating `Nat.sub` and unguarded `/` `%` (requiring `BitVec` or Rust-matching `Int.tdiv`/`Int.tmod` with non-zero guards).
- **Module-Import Authority & Enclosing-Namespace Defense:** Enforce role import graphs on compiled `data.imports` headers (not solely on `declarationEdges`, which miss notation/macro expansions from a `TrojanProof` import), reject reserved roots (`Init`, `Std`, `Lean`, `Lake`, `Trusted`) and any untrusted declaration whose namespace components contain `Trusted`, and apply `stripOptParams` so elaboration-only default arguments do not pollute statement-origin cones.

#### 2.2 Closing the Self-Attesting Lock Hole (`M1`/`M2`)
When an autonomous agent holds workspace write access, checking a lockfile (`spec-lock.json` or `theory-lock.json`) solely for internal consistency fails in two modes (reproduced in Probe 2):
- **`M1` (Dual-File Self-Attestation):** The agent edits both `Specs/Foo.lean` (weakening a precondition or restricting the input domain) and `spec-lock.json` to match the weakened hash.
- **`M2` (Cached-Summary Poisoning):** The agent edits cached axiom/feature summaries inside a workspace `theory-lock.json` (e.g., claiming `axioms: []`) so Stage-2 skips replaying poisoned upstream `.olean`s.

**Structural Rule (Out-of-Band Root Authority):**
1. Never read runtime theory locks from an untrusted checkout; embed trusted model/theory manifests at binary build time (pure UTF-8 data via `include_str!`) and under `5a`/`5b`/`5c` replay full unmodified closures rather than trusting cached Stage-1 axiom summaries.
2. Anchor specification locks outside the agent's write authority: evaluate PR submissions against base-branch specifications (mirroring `theorem-labs/oss-verify-proofs` `tools/oft/check.py` base-branch isolation) or pass `--spec-lock-sha256 <hex>` from an out-of-band orchestrator with `Specs/` mounted read-only inside the agent sandbox.

#### 2.3 Constructive Anti-Vacuity and Dual-Polar Mutation Refutation
A kernel-valid proof of $T \models S$ does not rule out vacuous preconditions ($P \equiv \bot$), domain-narrowing hypotheses, or weak postconditions (`ensures True`):
- **Reachable Precondition Inhabitance (`PreInhabited`) & `AssumedContractRealizable`:** Require constructive inhabitedness witnesses at reachable call states (blocking contradictory preconditions) and default assumed contracts to `Partial` (always realizable via divergence), requiring explicit realizability proofs (`∃ out, Post args out`) only when escalated to total contracts.
- **Linear $(m+1)$-Witness Clause Independence:** One joint positive witness plus $m$ single-clause-isolating negative counter-witnesses defeat multi-conjunct canary masking in $O(m)$ checks.
- **Dual-Polar Mutation Refutation (`Pole A ∧ Pole B`):** Single-polar `proof_failed` on a seeded implementation mutant measures proof-to-code coupling (yielding `7/7` false kills even on `Spec := True`), while bare `code != 0` conflates `runtime.maxRecDepth` and `(kernel)` faults with semantic kills. Auditing specification strength requires both **Pole A** (clean frontend rejection `exit 1`, `stderr == ""`, zero `runtime.*`/`(kernel)` errors, enabled by logarithmic `stepPow2` execution) AND **Pole B** (a kernel-checked refutation theorem `⊢ ¬ CrateTheorem ⟨P_mut, Spec⟩` against SHA-256-identical `Spec.lean`, leveraging operational determinism for existential return specs).
- **Joint Patch-and-Prove Guarding:** Whenever an agent may also modify source code, enforce semantic-delta penalties and human/cold-auditor review on every source diff (mirroring `oss-verify-proofs` Footnote 06 and avoiding the `37.7%–45.6%` semantically broken test-passing patch rate observed in DARPA AIxCC).

---

### 3. Layer 3 — Whole-Crate Capture and Build-Graph Fidelity

Basis: `source` + `derived`

Inspecting `google/zerocopy@a007a51af4` (`anneal/trusted/rustc-capture/src/capture.rs:256-314`) highlights concrete subject-gaming vectors that apply to any MIR-based Rust verifier:
1. **Exported Macros (`DefKind::Macro`):** Because a macro definition owns no HIR body (`has_body == false`), gating whole-crate obligation classification on `has_body` silently marks `#[macro_export] macro_rules!` items as `required = false`. Yet `rustc`'s `unsafe_code` lint suppresses diagnostics when `unsafe` spans originate from an external macro expansion, allowing a `#![forbid(unsafe_code)]` downstream crate to execute UB from a "crate-verified" dependency. Whole-crate scope MUST classify externally visible macros (`is_exported || is_public`) as `required = true` (and audit `pub use dep::macro_name` once multi-crate dependencies are admitted).
2. **Item-Less Foreign Blocks (`DefKind::ForeignMod` / `ForeignTy`):** An empty `#[link(name = "...")] unsafe extern "C" {}` block also has `has_body == false` while embedding link-time native-library dependencies into `.rmeta`. Whole-crate capture MUST mark `ForeignMod`/`ForeignTy` as `required = true` and reject `!tcx.native_libraries(LOCAL_CRATE).is_empty()`.
3. **Build-Profile & Config Fidelity:** Capture must preserve production `-Copt-level`, `-Cdebug-assertions`, `-Coverflow-checks`, `-Cpanic`, and `--cfg` verbatim (injecting `-Zmir-preserve-ub -Zmir-opt-level=0 --emit=metadata` plus zero-LLVM `items_of_instance` `required_consts` checking), resolve `.cargo/config*` across all ancestor directories and `$CARGO_HOME` (or capture directly from build-system `rustc` argv), execute capture itself inside a sandbox, hash all dynamically loaded `proc_macro` `.so`s via closed-world `(st_dev, st_ino)` `/proc/self/maps` verification, and surface exact `profile_identity` and `tcb_shims` explicitly in the verification receipt.

---

### 4. Layer 4 — Elaboration Containment, Cache Hygiene, and Non-Spoofable Provenance

Basis: `source` + `documentation` + `derived`

1. **Layered Local Containment:** Combine Linux mount/PID/network namespaces (`bwrap --unshare-all --disable-userns --die-with-parent --proc /proc`) with a `seccomp-bpf` allowlist (`CLONE_THREAD`-preserving `SYS_clone` with `ENOSYS` on `SYS_clone3`, blocking `fork`/`vfork`/`setsid`/`ptrace`/`process_vm_{readv,writev}`/`request_key`/`AF_VSOCK`/`io_uring_*`), `PR_SET_DUMPABLE=0`, read-only input mounts, and an ephemeral pipe-FD HMAC key when a local orchestrator delegates compilation to child processes.
2. **Orthogonal Receipt Containment vs. Out-of-Band Remote Provenance:** Because CLI flags (`--modify_execution_info`, `--strategy=...=local`, `--external-executor-attestation`) are trivial to spoof, verification receipts MUST separate self-verified `kernel_verdict` from a closed 4-variant `elaboration_containment.enforcer` enum (`self_execseal_in_process` | `split_action_execseal_unauthenticated` | `external_unverified_by_binary` | `none`), marking caller executor hints `"UNTRUSTED"` and requiring CI policy gates to verify remote execution out-of-band (e.g., SLSA v1.0 provenance + remote execution logs confirming zero local fallback).
3. **Cache-Poisoning Isolation:** Untrusted PR builds must never hold write credentials to shared remote action caches (`--remote_upload_local_results=false`), and any Lake-based offline audit must disable Lake's artifact cache explicitly (`LAKE_ARTIFACT_CACHE=false`, isolated `LAKE_CACHE_DIR`, `--no-cache --rehash`, purged `.lake/{build,cache}`) rather than relying on `lake clean && lake --no-cache build`.

---

### 5. Layer 5 — Independent Multi-Kernel Consensus and Audit-TCB Minimization

Basis: `source` + `derived`

#### 5.1 Quantified Audit-TCB Reduction at `google/zerocopy@a007a51af4`
Measuring `anneal/trusted/audit/TrustedBoundary.lean` (`4,369` LOC) and `library-lock.json` (`5,342` LOC) at `a007a51af4` shows how replacing in-process `.olean` target auditing with the `5a`/`5b`/`5c` NDJSON Comparator simultaneously eliminates binary-deserialization risk and dramatically shrinks the runtime Lean audit TCB:

| `anneal/trusted/audit/` Block (`a007a51af4`) | Current LOC | Under Unified `5a`/`5b`/`5c` Architecture | Target LOC |
|---|---:|---|---:|
| `TrustedBoundary.lean` L1–578 (types, JSON, `.olean` `importEnv`) | `578` | Keep role/JSON types; delete `.olean` `importEnv` helpers | `~220` |
| `TrustedBoundary.lean` L579–2110 (Pass-1 preflight `715` + Spec preflight `817`) | `1,532` | Unify into one closed-allowlist `SpecPreflight.lean` | `~650` |
| `TrustedBoundary.lean` L2111–2551 (in-process `replayOntoBase` & alternates) | `441` | Deleted (superseded by `5a`/`5b`/`5c` external kernels) | `0` |
| `TrustedBoundary.lean` L2552–2868 (Pass-1 repo `audit`) | `317` | Offline NDJSON manifest check | `~120` *(offline)* |
| `TrustedBoundary.lean` L2869–3801 (Pass-2 `lean-miri` correspondence) | `933` | Split to offline `CorrespondenceAudit.lean` (`0` runtime LOC) | `0` *(runtime)* |
| `TrustedBoundary.lean` L3802–4273 (Phase 4 `targetAudit` `.olean` replay) | `472` | Deleted (replaced by `~450–600` LOC safe-Rust `5c`) | `0` |
| `TrustedBoundary.lean` L4274–4369 (CLI dispatch) | `96` | Minimal `SpecPreflight` CLI entrypoint | `~50` |
| **Runtime Lean Audit TCB Total** | **`4,369`** | **Parser-only `SpecPreflight.lean` (zero `.olean` loading)** | **`~650–800`** (`-82%` to `-85%`) |
| `library-lock.json` (`732` file hashes + `645` edges) | `5,342` | 4-line recursive sysroot tree digest (`-99.93%`) | `4` |

#### 5.2 Multi-Kernel Quorum & `tcb-map` Governance
Because `CVE-2026-72844` (`leanprover/lean4#14576`) demonstrated that a single kernel bug can yield axiom-free `False` (and independent kernels can occasionally share edge-case bugs unless diversely implemented and verified), high-assurance pipelines should run at least **two diverse NDJSON kernels by default** (`nanoda_bin` in safe Rust + `con-ron` formally verified, both bundled in `v4.35.0`), backed by the full 6-kernel `lake comparator --paranoid` quorum in nightly/release CI—and optionally pinned across distinct physical CPU cores against silent hardware data corruption. Harvesting `google-deepmind/code-verification`'s `tcb-map` adds fail-closed 6-bucket repository classification, `tcb_rust_import` isolation for TCB Rust crates, `module` `public import` vs. private `import` checks, and `TrustedClosure` BFS shortest-path blame (`findBlamePath`).

---

### 6. Layer 6 — Permanent Exploit Regression Fixtures, Guard Mutation, and Continuous Red-Teaming

Basis: `execution` + `derived`

Executing the preserved stdlib-only probe (`support/verify_auditing_layers_probe.py`, SHA-256 `493c8d38c4593095c874cfce2e12a5d451bfeaf419ca18c43cc2fdcb47ca4225`) on Python 3 on `2026-11-22` verifies all four automated audit layers:

```text
[Probe 1] Comparator 5c: pinned_primitives=39, honest=ADMITTED, exploits_rejected=7/7
[Probe 4] Guard-Mutation Audit: exposed=7/7 (100.0% load-bearing guards covered)
[Probe 2] Lock Authority: naive_self_attesting_bypasses=2/2 (M1, M2), out_of_band_bypasses=0/2
[Probe 3] Spec Preflight: denylist_caught=0/4, closed_allowlist+imports+ns_caught=4/4
ALL_PROBES_PASSED
```

In production verification systems, Layer 6 operationalizes three continuous loops:
1. **Permanent Exploit-Fixture Bank (Blocking CI):** Retain a must-reject fixture for every discovered bypass class (tampered statements, unused-primitive injection, `.opaqueInfo` stubs, `Quot` forgery, exported `unsafe` macros, item-less `#[link]`, denylist escapes, `TrojanProof` imports, self-attesting lock edits, `ExecSeal` escapes, and Dual-Polar vacuity mutants) plus the `lean-kernel-arena` 90-test must-reject export corpus on every toolchain bump.
2. **Automated Guard-Mutation Auditing:** Systematically disable each individual policy rejection branch in the comparator, spec preflight, capture gate, and operational semantics (one mutant per guard) and require `100%` exposure by the negative fixture suite—eliminating silent guard erosion (contrasting with the `5.6%` upstream guard-exposure rate previously measured on `mmverify.py`).
3. **Continuous Structure-Aware Fuzzing & PR-Triggered Red-Team Sweeps:** Pair 24/7 grammar/NDJSON fuzzing of parsers and verifiers with PR-triggered cross-model adversarial red-team sweeps targeting any diff that touches TCB code or toolchain pins.

## Boundaries

- **`not examined`:** Non-Linux OS containment implementations (macOS deny-default Seatbelt and Windows AppContainer) were **not examined** experimentally here; Layer 4 sandboxing specifics apply to Linux `bwrap` + Landlock + `seccomp-bpf`. Live end-to-end wall-clock benchmarking of combined `5a` + `5b` + `5c` (`nanoda_bin` + `con-ron`) on large multi-hundred-function Rust crates was **not examined** (estimated target-proof latency relies on published `nanoda_lib` throughput and prior corpus measurements).
- **`unknown`:** Whether future upstream `leanprover/lean4` releases will change `Lake/CLI/Check.lean:417`'s `unpermitted_axiom_hard_error: false` default, expand `primitiveTargets`, or deprecate `.olean`-mode `leanchecker` in favor of `--from-export` is **unknown**.
- **`known not to apply`:**
  - Checking `#print axioms` alone, running non-fresh `.olean` replay, or running `lake clean && lake --no-cache build` is **known not to apply** as a defense against `.opaqueInfo` stubs, cached artifact poisoning, or untrusted `.olean` deserialization.
  - Using `GasStationManager/SafeVerify` at `b291b588a539` as an adversarial judge is **known not to apply** due to its five documented bypasses (`partial def` whitelist, un-replayed helper `.olean` imports, `sorryAx` definition comparison bypass, discarded `supplementedDecls`, and `Nat.reprFast` negative-`mpz` sign stripping).
  - Single-polar `proof_failed` mutant counts are **known not to apply** as evidence of specification strength (`7/7` false kills on `Spec := True` under certificate coupling).
- **`unsupported`:** Enforcing axiom hygiene or complete informal-to-formal semantic fidelity purely inside the object logic is **unsupported** in principle (Gödel II, Tarski, Löb; Pollack's semantic-fidelity gap). Enforcing kernel-level theorem opacity via `@[irreducible]` is **unsupported** in Lean 4.
- **Model-probe qualification:** `support/verify_auditing_layers_probe.py` is a deterministic Python model (`Basis: execution`) verifying structural comparator, lock-authority, allowlist, and guard-mutation invariants; it does not replace running real `leanexport`, `nanoda_bin`, `con-ron`, `rustc`, or Linux `bwrap`/`seccomp` binaries.

## Evidence

### Primary Source Coordinates (Observed `2026-11-22`)
1. **`leanprover/lean4` `v4.35.0` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) & `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`):**
   - `src/lake/Lake/CLI/Check.lean`: `L30-33` (adversarial `.olean` isolation policy), `L407-458` (`runExternalKernel`, `unpermitted_axiom_hard_error: false` at `L417`), `L474-514` (`primitiveTargets` 27 names + `builtinTargets` 4 `Quot.*`), `L572-580` (`bundledKernels`: `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`), `L690-776` (`runComparator`, `runCheck`, `--challenge-from-export` / `--solution-from-export`).
   - `<sysroot>/bin/` (`v4.35.0` release binaries observed live): `leanexport` (`700,728 B`), `leanchecker` (`59,656 B`), `leanchecker-paranoid` (`8,858,080 B`), `lean4lean` (`36,897,680 B`), `nanoda_bin` (`1,339,280 B`), `con-leche` (`17,613,744 B`), `con-ron` (`2,945,520 B`).
   - `src/Lean/CompactedRegion.lean:71-109` (`unsafe` `save`/`read` & `v3` `allowClosures` contract); `src/library/module.cpp:578-585`; `src/runtime/compact.cpp:518-688`; `src/Lean/Util/CollectAxioms.lean:56-67, 102-146`.
2. **`leanprover/comparator` (`e3dcf3083fc53d44b27a4431fabf7d43181583f5`, `v4.35.0`):** `Main.lean:228-239` (Quotient post-check), `L241-280` (`primitiveTargets`).
3. **`ammkrn/nanoda_lib` (`0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`, `v0.4.32`):** `src/util.rs:757-791`, `src/tc.rs:359-455`, `src/expr.rs:606-640`, `src/quot.rs:67-316` (34 hardcoded `Init` primitives; `overflow-checks = true`, `#![deny(clippy::cast_possible_truncation)]`).
4. **`google-deepmind/code-verification` (`8c8d371f1962ac73435c8eb148678991f5c3470d`):** `arm64-semantics/tools/tcb-map/src/{policy.rs:191-440,629-723, tcb_rust_import.rs:48-156, lib.rs:597-624}`; `arm64-semantics/ProofLib/TrustedClosure.lean:92-299` (`stripOptParams`, bitset closure, `findBlamePath`); `comparator/{run.sh,computational.json,symbolic.json}`.
5. **`GasStationManager/SafeVerify` (`b291b588a53999a7e837dda61c7dbfe8c550c814`):** `Main.lean:28-30, 58, 157, 195-205, 232-286, 418-434`.
6. **`theorem-labs/oss-verify-proofs` (`4c8fe739bb9bc95898f410b37222626f26dd0061`):** `tools/oft/check.py` (base-branch isolation, `Redirect "assumptions" Print Assumptions`).
7. **`google/zerocopy` (`a007a51af473e5901915b003083e61c7c89c7bd1`):** `anneal/trusted/audit/TrustedBoundary.lean` (`4,369` LOC measured by section), `anneal/trusted/audit/library-lock.json` (`5,342` LOC), `anneal/trusted/rustc-capture/src/capture.rs:256-314` (`DefKind::Macro` / `ForeignMod` `has_body` gating).
8. **Preserved Executable Probe (`Basis: execution`, observed `2026-11-22`):** [`support/verify_auditing_layers_probe.py`](support/verify_auditing_layers_probe.py) (Python 3 stdlib only, SHA-256 `493c8d38c4593095c874cfce2e12a5d451bfeaf419ca18c43cc2fdcb47ca4225`).

## Revalidation

1. **Run the preserved model probe (< 0.2 s):**
   ```bash
   python3 -B reports/in-principle-reward-hacking-defenses-and-zero-trust-proof-auditing/support/verify_auditing_layers_probe.py
   ```
   Expected: exit code `0`, `exploits_rejected=7/7`, `exposed=7/7 (100.0%)`, `out_of_band_bypasses=0/2`, `closed_allowlist+imports+ns_caught=4/4`, and `ALL_PROBES_PASSED`.
2. **Check Lean `v4.35.0+` bundled checkers and `Check.lean` defaults:** On any newer Lean release, list `<sysroot>/bin/` for `leanexport`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, and `con-ron`, and diff `src/lake/Lake/CLI/Check.lean` around `unpermitted_axiom_hard_error`, `primitiveTargets`, and `builtinTargets` to confirm whether `39`-name primitive pinning or `nanoda` config defaults changed.
3. **Audit Rust capture completeness:** Diff `anneal/trusted/rustc-capture/src/capture.rs` (`required` and `collect`) to verify externally visible `DefKind::Macro`, `DefKind::ForeignMod`, `DefKind::ForeignTy`, and `tcx.native_libraries(LOCAL_CRATE)` are all fail-closed in whole-crate scope.
4. **Re-check `TrustedBoundary.lean` LOC:** Re-measure `anneal/trusted/audit/TrustedBoundary.lean` and `library-lock.json` on newer `google/zerocopy:main` commits to track runtime Lean audit TCB shrinkage as `5a`/`5b`/`5c` lands.
