# I148 five-function same-path Lake replay and function-change control

Observed 2026-09-29 at published parent `3b549cb1eddebc54896a106c5c94ede6c2c134e5`, with the retained [I148 five-function corpus](../anneal-3731-i148-multifunction-translation-repeat-2026-09-29/REPORT.md), locally pinned Charon/Aeneas, Lean 4.30.0-rc2, and Lake 5.0.0-src+3dc1a08. This is a sequential component experiment. It adds a substantive function-body change to the smaller order-only [R43](../anneal-3730-charon-shortname-aeneas-impact-2026-09-29/REPORT.md) same-path replay and the comment-only generated-source [M06](../anneal-3730-m06-generated-lake-source-order-trace-2026-09-29/REPORT.md) invalidation control.

## Question and procedure

The question was whether Lake would replay a warm, fixed-path, four-module consumer after its three generated source paths were replaced by each of four other **byte-identical Aeneas output sets**, then rebuild the affected graph after a real function-body change. The I148 corpus has five public functions (`add_one`, `choose`, `pair_sum`, `make_pair`, `combine`) and a two-field public struct. The prior report retained five independent Aeneas CLI output sets. Its five `Types.lean` files have SHA-256 `698540ae6f0215de8fe7c221807d967a2c34710f09bdc40028d84f48c8d84aa6`, five `Funs.lean` files have `a23e4de51aad5573134decee8733450afdb3924c306f51f51f41b537982c9ecd`, and five `Probe.lean` files have `88d15c5183e48c512f4ecfb38c430356859b255fe1dcf6a613fd51c7ba36820d`.

One private Lake consumer imported `Probe` from those generated paths and compiled five equality-to-self theorems, one for each function. The sequence was: fresh baseline build; warm no-write build; four sequential copies from prior `gen-2` through `gen-5` over the *same* `Probe/Types.lean`, `Probe/Funs.lean`, and `Probe.lean` paths, building after each; one function-change build; then a changed no-write build. All eight Lake invocations used `lake build -v`, `LAKE_NO_NET=1`, `LEAN_NUM_THREADS=1`, and `LAKE_JOBS=1`. The consumer's path dependency, package manifest, and `.lake/packages` symlink referenced already cached Aeneas backend dependencies. The symlink was removed from the retained package. No dependency was installed or downloaded.

For the positive control, the runner copied the prior Rust fixture to `support/work/mutant`, changed only `add_one`'s `x + 1` to `x + 2`, invoked pinned Charon with Cargo flags `--offline --locked -j 1`, and invoked pinned Aeneas with the prior corpus's Aeneas flags and common `probe.llbc` basename. The new LLBC had `has_errors: false`. A whole-file comparison shows `Probe/Funs.lean` changed in exactly one line, from `x + 1#u32` to `x + 2#u32`; `Probe/Types.lean` and `Probe.lean` stayed byte-identical. The changed `Funs.lean` SHA-256 is `f5f50d295621081c3f68e3e09add0e9eb88b822350adc4700eec892c8e77b160`.

Each phase checked system free memory of at least 30% and disk availability of at least 10 GiB. Each subprocess had a 60-second cap and a sampled process-tree RSS cap of 2.5 GiB. Lake builds were strictly sequential. The minimum recorded preflight memory was 35%; minimum disk was 42.64 GiB. The largest sampled process-tree RSS was 2.138 GiB. These are observed preflight and sampled process values, not a continuous system-wide peak record.

## Result

| Build | Seconds | Local `Probe.Types` / `Probe.Funs` / `Probe` / `Consumer` |
| --- | ---: | --- |
| Fresh baseline | 48.552 | Built / Built / Built / Built |
| Warm no-write | 4.911 | Replayed / Replayed / Replayed / Replayed |
| Replace with `gen-2` | 3.320 | Replayed / Replayed / Replayed / Replayed |
| Replace with `gen-3` | 3.093 | Replayed / Replayed / Replayed / Replayed |
| Replace with `gen-4` | 3.317 | Replayed / Replayed / Replayed / Replayed |
| Replace with `gen-5` | 3.128 | Replayed / Replayed / Replayed / Replayed |
| Function change `x + 1` → `x + 2` | 24.453 | Replayed / Built / Built / Built |
| Changed no-write | 4.170 | Replayed / Replayed / Replayed / Replayed |

The full cached Lake graph reported 1,686 jobs; the four rows above are the local consumer modules. During warm and identical-source replacement builds, every retained local `.trace` and `.olean` SHA-256 and mtime matched baseline. The function change altered `Probe.Funs.olean` and the traces for `Probe.Funs`, `Probe`, and `Consumer`; `Probe.Types`' trace and OLean remained unchanged. The `Probe` and `Consumer` OLean bytes also remained identical despite Lake marking those modules `Built`, while their traces changed. That distinction matters: a `Built` label does not imply byte-different compiled output.

| Local artifact | Baseline SHA-256 | Function-change SHA-256 |
| --- | --- | --- |
| `Probe/Types.olean` | `95ed236ac9ba3ac9b53eb3a759b450030972b715eb75c6b5ea03288bcb7a4cc9` | same |
| `Probe/Funs.olean` | `b92df6b2b630f36e561386f8570b1088c3de66378324d6241aa447b58e2304a3` | `8778abd80c28786145b81c844a9ed27e272abc1a1e85ce40ae22df8f82676a55` |
| `Probe/Types.trace` | `aaaa4c283932b973d84a6a11ce90151ba9608f78d8d1258078c74fb179c4d034` | same |
| `Probe/Funs.trace` | `4a2c7cb95160f2ff5da85998bf843bd67bbfb3d828e0e123b0b6b5d617f35359` | `3b0727dca7e3512ded11b140f51565fad5e6bd43e60237592ee97ca88b9124e8` |
| `Probe.trace` | `d5a78c4633c5e160d3cf67f11788c81d6a61c192a5cff34331190ccf83bf4984` | `f2e434221a5844085250d116c1c37e9f9674edd69e240877e0c3f658aaedd54b` |
| `Consumer.trace` | `99e1cc20cbe7883b804cac61c578ce5cd7f59555aa0b2131bd2e56be2cc602ac` | `6a183641850cfacc09ed24a4e2d5c976948e7a92a4cf8973be4d7facc17f7566` |

The five small consumer theorems compiled in both fresh and changed builds. The retained `#print axioms combine_self` output in each was `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` in that printed inventory. `support/theorem-output.txt` extracts those two lines from the full logs. This is a batch elaboration check of identity statements, not evidence that the generated model refines Rust or that its behavior is correct. Lake also printed warnings from cached Aeneas standard-library modules that use `sorry`; those are outside these five generated definitions and do not disappear from the retained full logs.

## Evidence and revalidation

`support/results.json` records exact absolute tool paths and SHA-256 values, the prior report/results/source identities, every command and working directory, relevant environment overrides, per-phase memory/disk preflight, exit status, elapsed time, sampled peak process-tree RSS, log hashes, local job lines, and source/trace/OLean hashes and mtimes after each build. `support/summary.json` keeps the compact build and scope summary, while `REPORT.json` supplies catalog metadata. `support/logs/*.gz` contains the full stdout/stderr streams compressed deterministically; their uncompressed hashes match the result record. `support/work/` retains the Rust mutant, LLBC, generated Lean, final consumer source, and Lake artifacts. The exact first and last state hashes are in the result record, even though only the last physical build outputs remain at the fixed paths.

Run `python3 -B support/check.py` from this report directory. It reads retained evidence and prior I148 artifacts, checks the eight build labels, guards, source and log hashes, full replay artifact identity, changed-function one-line delta, invalidation traces, and theorem output without invoking Lake or a network service. It passed after the run and after log compression. `support/probe.py` is the bounded sequential replay recipe for a fresh copy of this report package with `support/work`, `support/logs`, and `support/results.json` absent. A rerun requires the same local pins and cached dependency tree. The full Lake stdout is verbose because the cache graph has 1,686 jobs; only the four local job lines are interpreted here.

## Scope

This result supports a narrow I148 component claim: byte-identical generated five-function source at fixed paths replayed in warm Lake, and a real one-function generated byte change invalidated its module and downstream consumers. It provides context for E06, E07, and F20 without changing their status. I148 and those related rows remain **partial**. The Anneal V2 generator, publication path, proof attachment, editor/server behavior, representative workload, and product behavior were not exercised. The retained test has one local consumer, one pinned tool tuple, a one-shot Aeneas CLI invocation for the positive control, and no concurrent builds or shared writer. These observations do not establish a general cache-key rule, semantic equivalence, or end-to-end Anneal correctness.
