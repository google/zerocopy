# Frozen proposal: one independent original HOL positive replay

*Authored by an AI agent acting on joshlf's behalf.*

Status: preparation only. No runtime query, producer, compiler or native proof invocation has been run by this reviewer. An explicit parent gate is required before executing any prepared spec. `native_once.py` is excluded entirely.

Use only existing container `94afa6889b4a4af6f3dce4eb3e81bb6c698522130a9be617166e1a92a32535aa`, image `sha256:fc198c017f2474a20afe68636b3b790f7247c7593c7d252bb161673b11e5b9a2`. Keep CPU2, 4GiB memory, 8GiB memory-plus-swap setting, pids512, no-new-privileges, no mounts or published ports. Require it running, not paused/restarting/dead/OOM-killed, no state error and no restart since the retained inspection. The parent must confirm exclusive use for the one proof process. Do not alter any resource setting.

All new files are host-side under this review directory. No new directory or file is staged in the container. Reuse the existing native executable and its original source working directory. Limit new host logs to 32MiB as a stopping threshold observed between phases; do not claim a hard disk cap. Retain every complete phase stdout/stderr and exact status even if a gate fails. Do not retry a failed phase or change a mechanism without diagnosis and a new parent decision.

## Exact command and capture

`specs/independent-positive.json` retains the original argv exactly, including the host Docker CLI locator. The subject-operation form is:

```text
docker exec --workdir /home/opam/anneal-cross-sources/s2n-bignum
  --env OPAMROOT=/home/opam/anneal-hol-opam --env LC_ALL=C
  --env HOLLIGHT_DIR=/home/opam/anneal-cross-sources/hol-light
  --env HOLLIGHT_LOAD_PATH=
  94afa6889b4a4af6f3dce4eb3e81bb6c698522130a9be617166e1a92a32535aa
  opam exec --switch=hol54 -- timeout --signal=KILL 1200
  /home/opam/anneal-cross-output/selected.native
```

After the explicit grant, invoke each prepared spec serially with the byte-identical copied existing `host_run.py`, for example `python3 -B host_run.py independent-before-inspect`, from this directory. It places full streams, a start record and final receipt under this directory's `logs/`. It records the actual Docker-client return code and monotonic invocation wall time. A subject nonzero status is retained in the receipt even though the wrapper itself returns 1. The native timeout is the existing GNU timeout, not a custom lifecycle wrapper. An outer tooling timeout must allow the 1200-second subject limit and stream collection to finish. Yield the orchestration tool regularly for progress; do not put a 20-minute blocking wait in commentary.

## Serial phases and gates

1. Rehash the prepared helper/spec freeze and host Docker CLI before any runtime operation. The host CLI observed in preparation resolves to the existing OrbStack Docker tool, SHA256 `70d5a06adf388bd09b652f47ddc9ca31663a3e5353d24188bdb0054b3014ab3e`. This is a new preparation observation, not a historical worker tool identity.
2. `independent-before-inspect`: capture full existing-container inspection and require the exact subject/resource/liveness fields above.
3. `independent-before-identities`: run the byte-identical read-only `preflight_reader.py` through stdin with Python `-B`. Require no mismatches across all23,177 originals. Require the complete 69-tool, 2,417-compiler-library and 23-generated-module/object identity records, including resolved paths, symlink metadata, mode, size and SHA256, to equal the retained `hol-replay/logs/postpositive.stdout`. Require the unchanged absence of local HOL `_opam`. The source checksum file itself is pinned separately in the supplemental query; a self-selected manifest is insufficient.
4. `independent-before-census`: run the byte-identical corrected `inline_census_reader.py`. Require the entire actual core/selected source census, three audit inputs, chooser copies and 704 output-file identities to equal retained `hol-replay/logs/final-census.stdout`. This binds the exact existing inliner/native/owned-entry subjects, not merely their names.
5. `independent-before-supplemental`: run the proposed read-only supplementary identity reader under the same opam switch and positive environment. Require checksum-file SHA256 `eed7dd6b8ce62b4d71411955bfe2627389f1d5a9d1f53378cfb6ff2a0cd6e3df`, native SHA256 `b6f89be7d7a7e5ffb572dbc30bef3fb98816c41eadbac842474e09d17f090ec8`, selected inliner SHA256 `7063d0b883617faaaf516de6ffc0ae3608d4f2f70248247fbfa53f875604b12b`, and all three unchanged owned input hashes. Record Linux/AArch64 and the direct expected loader/DSO/configuration identities. Review any nonempty `LD_PRELOAD`, `LD_AUDIT` or `LD_LIBRARY_PATH`, unexpected file resolution, absent required file, or changed loader configuration before proceeding. The query does not run `ldd`, the loader, the native program or any compiler. The direct installed DSO paths are supplementary identities, not proof of actual process mapping or complete transitive dynamic-library resolution.
6. Stop for the launch gate: all fresh identities, recorded subject bytes and resource checks must pass and the parent's explicit one-positive grant must still apply. Then `independent-positive` runs exactly once. No additional producer, compile, mutation or negative-control invocation is allowed.
7. Regardless of the ordinary return status, retain full streams/status. An unexpected assertion, proof failure, timeout/signal, missing marker or identity discrepancy stops dependent work. Diagnose first; do not retry or silently reinterpret failure. If safe read-only postchecks remain authorized after a failed subject, capture them for diagnosis without launching a second proof program.
8. For a successful subject, run `independent-after-identities`, `independent-after-census`, `independent-after-supplemental`, and `independent-after-inspect`. Require complete equality with the before records for all specified sources, tools, libraries, generated modules/objects, outputs, supplemental file identities and selected environment; compare resource identity/liveness fields, not volatile process counters. Rehash the host CLI and prepared helpers/specs again. Any mismatch stops the verdict.
9. Independently parse the fresh positive stdout using the reviewed `positive_stream` function in `static_review.py` (import with Python `-B`; its main does not run on import), supplying the bound static core/selected events from `static-review-results.json`. Require the full71 theorem statements exactly equal to the previously reviewed statements, all181 slots exactly once, exact47/83 ordered ledger pairs, exact complete three global axiom statements, one inner and one outer policy marker, and both completion markers exactly once. Require exit0 and verify fresh stdout/stderr sizes/hashes against its own receipt. Do not compare the entire new stdout byte string to the old stream: proof-search timing/progress can differ. Preserve any changed diagnostic lines and investigate material failures. The original nonempty stderr is the45-byte opam root warning; empty stderr is not an acceptance requirement.

The proof invocation must preserve its original cwd because it reads `x86/generic/bignum_add.o` and `.obj` at runtime. Do not copy the program, chmod package files, add files to sources, or change environment/mechanisms merely to satisfy a gate. The public package revalidation document's fresh-directory reconstruction is a separate option requiring its own grant, not this plan.

## Expected evidence and qualification

The original program is30,819,144-byte AArch64 OCaml proof code. Its x86 ELF inputs have complete SHA256s `0f94fe2090387f5f63afc80049732384d3badbcd89aae7ffc5200e1c53ec53eb` and `a81541b03aa800d646b113b6da1d81363f0d8921bc74ddceae76a82a9d5d7f73`; their185/215-byte `.text` data are checked as theorem subjects, not executed. The independent observation, if it passes, would corroborate the same selected theorem slice under the same trusted implementation and runtime. It would not remove compiler/inliner/kernel/library/OS trust, compute per-theorem axiom dependencies, or complete E03/E31. Fresh loader/DSO identities would be new evidence, not retroactive author before/after measurements.
