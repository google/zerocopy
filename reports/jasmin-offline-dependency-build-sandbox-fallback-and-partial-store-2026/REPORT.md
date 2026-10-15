# Jasmin offline dependency failure: sandbox fallback, HOME guard and partial store

## Summary

The pinned native AArch64 Jasmin dependency build **failed after 20.144 seconds** at a Nix HOME-directory purity guard. Effective configuration had both `sandbox=true` and `sandbox-fallback=true`. The inspected Nix 2.34.8 implementation can silently select an unsandboxed local builder when its namespace-capability test fails; the observed guard is consistent with that path, rather than a Coq or EasyCrypt proof failure.

A later stopped-store snapshot resolves the partial result: **one of 19 named output paths was registered, EasyCrypt 2026.09; the other 18 were absent from `ValidPaths`**. HOME contains an 11-directory Dune-cache layout with no files. That supports cache initialization during the EasyCrypt build as a hypothesis; the creating process and rejected next derivation remain unknown. No cleanup, retry or strict-sandbox recovery probe was executed in this investigation.

## Applicability

This report concerns one completed failed phase, followed by source inspection and stopped-snapshot data analysis on 2026-10-15. It follows the [prebuild input-readiness report](../jasmin-native-aarch64-evaluation-and-verified-build-inputs-2026/REPORT.md), preserved at [immutable commit e616e78a38a318554aa58a9508f04086c1828671](https://github.com/google/zerocopy/blob/e616e78a38a318554aa58a9508f04086c1828671/reports/jasmin-native-aarch64-evaluation-and-verified-build-inputs-2026/REPORT.md). That earlier report covers evaluation, verified input acquisition and an owned printf-only probe. This report covers subsequent dependency compilation and its failure; it does not change the earlier phase's observations.

The input environment is Jasmin `34f15840f10625bbc2cbf59b3d877e94c75bfbd9` with nixpkgs `652efddd59a21783edff64959252ec1cfce09041` and EasyCrypt r2026.09. The exact runtime and source identities are in [REPORT.json](REPORT.json). Nix 2.34.8 runs on **AArch64 Linux**; the intended later Jasmin compiler output remains x86-64 with Linux calling convention. Neither a Jasmin compiler-root build nor target-code execution occurred in this phase.

The exact container was `5444ba00b8675ccd8ad2d5a55c01b6b88785e06642e6e0e5ac7f459e31a46fd5`, from platform image manifest `71f0139a696ef851a52bebc0b8facfd20e728e0b92f7b0251480979614e24558`. It inherited the earlier byte-identical 330-byte regular-file `/etc/group` overlay and explicit empty build-users-group policy; it is not a wholly unmodified image. Recorded limits were CPU 2, RAM and memory-plus-swap limits both 12 GiB, PIDs 512, cap-drop-ALL, no-new-privileges and no mounts. The network was detached (`Networks={}`); `HostConfig.NetworkMode` remained `bridge`.

The invocation supplied its exact multiline `NIX_CONFIG` through `docker exec --env`, overriding the older startup environment. The build explicitly set max-jobs=1 and cores=2, used `--offline --no-link --json --print-build-logs --keep-failed`, and requested all outputs of 18 exact derivations with `drv^*`: 17 dependency packages plus setupHook.sh, yielding **19 output paths** because Apron has dev and out. Import-from-derivation and unsafe native evaluation were disabled; builders/build-users-group were empty and signature checking remained enabled. [Complete argv, environment, configuration and streams](support/build-receipts.tar.gz) preserve the actual conditions.

## Findings

Basis: recorded native **execution**, pinned implementation **source**, host-side SQLite/archive **execution**, and explicitly identified **derived** conclusions.

### The error follows builder selection, not a theorem checker

The build returned status 1 in 20.144146583 seconds. Its stdout is empty; stderr is 3,813 bytes, SHA256 `7b4d0775bfc9da53493d933581b3fe2c8c315bf59fb9aaecc2e6e8d00ba25d10`. It records EasyCrypt unpack, patch, `dune build --profile=dev`, install and fixup, followed by a retained new build directory and the HOME guard error. It contains no other target's builder-start line. The effective-config observer succeeded with an offline-network warning; that warning is preserved, not treated as a failed build or theorem result. Final observations show the container stopped and not OOM-killed; no timeout is indicated.

The pinned implementation explains the distinction between a global setting and the selected builder:

1. [`makeDerivationBuilder`, lines 2082–2141](support/nix-source/src/libstore/unix/build/derivation-builder.cc), initially selects sandboxing for `sandbox=true`. On Linux, if `mountAndPidNamespacesSupported()` is false and fallback is enabled, it emits a debug-level message, sets `useSandbox=false`, and constructs `LinuxDerivationBuilder` instead of the chroot builder. A normal-verbosity transcript need not show that debug message.
2. The [namespace test, lines 52–89](support/nix-source/src/libutil/linux/linux-namespaces.cc), tries user/mount/PID namespace and mount/proc operations; failures produce false. The actual rejected syscall/errno is unobserved. Cap-drop-ALL alone does not identify it.
3. The base builder returns `needsHashRewrite=true` at lines 256–259, whereas the [chroot override, lines 25–28](support/nix-source/src/libstore/unix/build/chroot-derivation-builder.cc), returns false. `startBuild`, lines 832–835, rejects an existing HOME only when `needsHashRewrite() && pathExists(homeDir)`. This is the exact observed guard. The log opens later, at line 849, explaining why the rejected next start can lack a derivation-identifying builder log.

For this inspected implementation, the guard therefore identifies an unsandboxed local path despite `sandbox=true`. Since the namespace result is process-static, EasyCrypt's earlier same-process ordinary local build is also inferred to have used fallback. This is a source-derived explanation of the recorded binary behavior, **not proof that the binary was built from these source bytes**. The release source, image and executable are independently pinned; their relationship is not a source-build attestation.

All [18 target attribute records](support/target-18-attrs.json) use cached Bash 5.3p9, none is builtin, none has `__noChroot`, and none explicitly sets HOME or requiredSystemFeatures. Only setupHook.sh has `preferLocalBuild=1`, which concerns scheduling rather than disabling this sandbox. `__noChroot` would be rejected under `sandbox=true` in this source. The prior coqword fixed-output source is already acquired data, outside these 18 targets. Thus a builtin, fixed-output or local-preference exemption is not the explanation for this target set.

### The stopped database establishes EasyCrypt registration

The parent copied HOME and `/nix/var/nix/db` from the stopped container without starting a program. Both archive hashes match successful copy receipts. The copied database's WAL is empty; host queries used `mode=ro&immutable=1` and `query_only=ON`. SQLite integrity_check returned `ok`, and the selected copied database files remained byte-identical after querying. The main database has 2,335 ValidPaths entries. [The complete query results](support/target-output-census.json) bind all 18 derivations, their output-name mappings, and every one of the 19 expected paths.

EasyCrypt's output `/nix/store/6pd3q95qxhypqqrgaiqb6wwc9g0l2609-easycrypt-2026.09` is registered at 2026-10-15T15:39:02Z, with the expected deriver, recorded NAR size **57,956,152 bytes**, and hash `sha256:5da60afaf1c45459837decd6ce3675be732c45f2d750013a144e0ffac5f50f57`. Its 18 recorded references include self, Why3, OCaml 5.4.1 libraries, Bash, libc and Python. The database marks ultimate=1, with null signatures and CA fields. These are local registration records, not independent NAR-content or signature verification of the new output.

The other 18 output paths, belonging to 17 derivations, are absent from ValidPaths. This means they were not registered valid in that snapshot; it does not prove physical nonexistence or exclude partial files. All 18 derivations themselves and all expected output mappings are present. The aggregate invocation failed even though EasyCrypt registered successfully. Its empty stdout is not a partial-success JSON result. Target-list order does not identify the next scheduled goal.

### HOME has a Dune-shaped directory tree; its creator is unknown

[HOME's full member census](support/archive-censuses.json) shows 11 directories and no files, symlinks or special objects: `.cache/dune/db` contains `files/v4`, `meta/v5`, `temp`, and `values/v3`. Every directory is uid/gid0, mode0755, with mtime 2026-10-15T15:38:43Z. That is a modification time, not an observed creation time.

Nix defines HOME as `/homeless-shelter` and assigns it to the builder environment; that assignment does not create it. EasyCrypt's builder passed the earlier existence guard, while a subsequent start found it present. The directory layout, build command and timing support a hypothesis of Dune-cache initialization during that interval, assuming no unrecorded writer. They do not establish which process or syscall created it. No cache payload remains in the snapshot to narrow the attribution.

## Boundaries

**Established:** one failed offline dependency invocation, source-backed fallback/HOME-guard explanation, stopped-store EasyCrypt registration, and 18 unregistered named output paths. The strict `sandbox-fallback=false` recovery probe and any continuation were **not executed**. No cleanup or capability/sandbox relaxation was attempted by this investigation.

**Unknown:** exact failing namespace syscall/errno, exact HOME-creating process, and rejected next derivation. Retained failed directory `nix-1093-3578735763` does not identify its goal in the available normal-verbosity log. This report does not infer success or failure for each unstarted package from the list order.

**Not examined:** independent content verification of EasyCrypt's new output, compiler-root compilation, Coq kernel or EasyCrypt theorem replay, generated assembly correctness, ABI/byte execution, or the intended broader proof pilot. A dependency compiler running Dune is not a theorem replay. The earlier cached-input verification does not extend automatically to a newly built output.

Initial/final SizeRw observations were 3,705,458,688 and 3,763,892,224 bytes; the delta was 58,433,536 bytes. Final host-free observation was 35,951,505,408 bytes. These are aggregate point observations, not quotas, peak usage, wire traffic, or an output-size measurement. Stopped-readback host-free values were acquired later and are separate observations.

## Evidence

All evidence was acquired or materially checked on 2026-10-15. [Archive membership and member hashes](support/archive-members.json) cover every member of three deterministic archives:

- [Build receipts](support/build-receipts.tar.gz): exact resource-update/config/build/stop/observer argv, statuses, raw streams and timings.
- [Historical source diagnosis](support/diagnosis-records.tar.gz): frozen analysis, target attributes and manifests. Its then-unresolved output census is superseded by the later stopped-store results above; historical statements are not additional current findings.
- [Stopped-readback records](support/stopped-readback-records.tar.gz): parent identity/copy receipts, small raw HOME tar, original host SQL/archive audit source, status/streams, and complete compact query results. The old audit's references to omitted local database copies describe that historical execution, not included payloads.

[Input bindings](support/input-bindings.json), [frozen subject hashes](support/frozen-inputs.json), and [explicit omissions](support/omissions.json) retain the snapshot/source/phase coordinates. The 10,462,208-byte DB tar is deliberately omitted; its SHA256 is `7e3667920dc4efa75bc012a4aa0884da85bb927465e10ef2880a2e0360555034`. Exact per-member hashes/sizes remain in the census. OCI exports, NAR/package binaries, full source mirrors and duplicate bulky readbacks are also omitted.

Seven unchanged Nix source files from `NixOS/nix@f3f1c3c5b8ad91850e0f7c590cf177f7ab022024` are preserved with [Git blob/SHA256 identities](support/nix-source-manifest.json), exact [COPYING](support/nix-source/COPYING) and [attribution](support/NOTICES.md). Narrow immutable upstream pointers include [builder selection/HOME guard](https://github.com/NixOS/nix/blob/f3f1c3c5b8ad91850e0f7c590cf177f7ab022024/src/libstore/unix/build/derivation-builder.cc#L2082), [namespace test](https://github.com/NixOS/nix/blob/f3f1c3c5b8ad91850e0f7c590cf177f7ab022024/src/libutil/linux/linux-namespaces.cc#L52), and [goal startup](https://github.com/NixOS/nix/blob/f3f1c3c5b8ad91850e0f7c590cf177f7ab022024/src/libstore/build/derivation-building-goal.cc#L907). Per-file existing notices remain unchanged. License/release source observations do not establish binary-build provenance.

## Revalidation

Run `python3 support/check.py` from this package to verify the outer manifest, deterministic archive memberships, exact stream bindings, target/output census relationships, HOME snapshot and source Git blobs. This checks packaged consistency; it cannot independently requery an omitted database. With the exact omitted snapshot and an existing extracted main database supplied, run `python3 support/check.py --store-db-tar /path/to/jasmin-store-db.tar --sqlite-main /path/to/db.sqlite`. It verifies the archive hash, requires empty WAL, byte-matches the supplied main DB to its archive member, opens it with `mode=ro&immutable=1` and query_only, checks integrity, and repeats every output/derivation/mapping/reference query. It performs no extraction, archive code execution or database writes. The original optional helper used an unavailable sqlite3 deserialize API and failed before SQL comparisons; [the preserved ordinary-error diagnosis](support/validation/CHECKER-DIAGNOSIS.json), exact failed source and streams distinguish that helper error from the successful repaired requery. The failed optional check ran on host Python 3.9.6 despite the original documented 3.11+ requirement; the repaired path avoids that API.

For a changed Nix/runtime subject, inspect the preserved builder-selection, namespace-test and guard regions first. A separately authorized **fresh owned output**, with `sandbox=true` and **sandbox-fallback=false**, is the proposed discriminating build-start gate. Reusing an already-valid probe can return without starting a builder. A known-present host marker outside declared inputs can help distinguish actual filesystem isolation if a fresh probe is later authorized. This strict probe is a recommended discriminating experiment, not a user-imposed requirement to use Nix’s inner sandbox. The executed build already lived inside a detached-network, no-host-mount, cap-drop-ALL outer container; that isolation is distinct from Nix’s inner builder sandbox. Another proposed route is an explicitly disclosed nonroot single-user Nix runtime (uid/gid1000, empty build group, appropriately owned store/state, cap-drop-ALL and no-new-privileges). It may avoid the root-owned HOME-directory issue without broad privileges or changed derivations, but it has not been evaluated or executed here and would not establish inner Nix sandboxing. Either route is a new reviewed experiment; do not delete evidence and silently retry. Preserve the failed subject and partial outputs. Additional native observation or build requires its own grant and evidence.

*Authored by an AI agent acting on joshlf's behalf.*
