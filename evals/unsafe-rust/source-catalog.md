# Unsafe Rust Evaluation Source Catalog

> **Evaluator-only material**
>
> This catalog contains fixture leads, historical fixes, and expected-finding
> sources. It is not part of the `unsafe-rust` skill and must never be mounted
> into an evaluation agent's workspace. An agent that can read this file, an
> audit note, an advisory, a fixing diff, or an issue title has been given the
> answer and has not performed a blind audit.
>
> These sources are evidence for constructing and checking evaluations. They
> are not Rust semantic authorities and must never be cited as axioms in a
> soundness proof.

## Purpose and Snapshot Policy

This catalog identifies code from which maintainers can build semantic
evaluations of the `unsafe-rust` skill. It deliberately combines:

- real vulnerable source at exact historical revisions;
- the corresponding fixed source when available;
- code that expert auditors found difficult or insufficiently documented
  without proving it unsound;
- small pass/fail examples from analysis and verification tools;
- current, high-quality open-world code;
- hand-proved negative controls; and
- boundary cases that test whether an agent states the right theorem rather
  than mechanically labeling every unusual behavior Rust UB.

Every acquired source must be frozen by repository commit, crate checksum, or
content digest. Record the acquisition date because advisory databases, issue
labels, default branches, generated output, and tool suites change. Counts in
this document describe the 2026-07-30 research snapshot; the fixture manifest,
not a prose count, is the eventual coverage authority.

Refreshing a source creates a new corpus revision. Never silently replace an
old fixture: doing so destroys result comparability.

## Corpus Registry

| Corpus | What it contributes | Inclusion policy |
|---|---|---|
| [Google `rust-crate-audits`](https://github.com/google/rust-crate-audits) | Independent expert audit notes over a very broad crate population, including proof/documentation defects and high-risk code without confirmed unsoundness | Exhaustively classify every audit record and represent every explicit issue atom |
| [RustSec Advisory Database](https://github.com/RustSec/advisory-db) | Published affected ranges, advisories, references, and many vulnerable/fixed crate pairs | Include every Rust UB, memory-safety, or soundness advisory after de-duplication; do not limit the search to one label |
| [GitHub Advisory Database](https://github.com/github/advisory-database) and [OSV](https://osv.dev/) | Additional aliases, affected ranges, references, and occasionally records not yet represented elsewhere | Reconcile with RustSec; add unique Rust memory-safety records |
| [`google/zerocopy`](https://github.com/google/zerocopy) | A rich historical regression set plus a current, high-quality, heavily documented unsafe-code corpus with macros and many configuration axes | Include every located historical soundness incident as a vulnerable/fixed pair and shard a complete audit of the current pinned tree |
| [`rust-lang/rust`](https://github.com/rust-lang/rust) standard-library history | Bugs in authoritative-library implementations, unusual unsafe abstractions, and compiler-version interactions | Include closed `I-unsound` library issues with reconstructible source and fixes; separately classify compiler bugs |
| [`Qwaz/rust-cve`](https://github.com/Qwaz/rust-cve) | Curated historical Rust standard-library CVEs and soundness issue leads | Cross-check the standard-library inventory and reconstruct exact revisions |
| [`Artisan-Lab/Rust-memory-safety-bugs`](https://github.com/Artisan-Lab/Rust-memory-safety-bugs) | A published 186-incident study corpus spanning third-party libraries, the standard library, executables, and one compiler bug | Import unique reconstructible incidents; preserve the paper's classifications only as hypotheses to verify |
| [`rust-fuzz/trophy-case`](https://github.com/rust-fuzz/trophy-case) | Real fuzz-found defects and reproducers | Include genuine UB/memory-safety cases; retain panic, resource-exhaustion, and ordinary bounds-check failures as theorem-calibration controls |
| [`sslab-gatech/Rudra`](https://github.com/sslab-gatech/Rudra) | Real unsafe-code findings and checker pass/fail examples, especially panic safety, Send/Sync, and higher-order unsafe interactions | Reconstruct reported issues and include representative tool tests |
| [`vnrst/Yuga`](https://github.com/vnrst/Yuga) | Lifetime-annotation defects, a RustSec-derived example set, synthetic examples, and reported real-project findings | Include all available labeled examples, separating confirmed, fixed, unconfirmed, and synthetic cases |
| [`safer-rust/RAPx`](https://github.com/safer-rust/RAPx) and predecessor datasets | Drop, aliasing, ownership, API-dependency, and verification examples, including sound controls | Import exact pass/fail examples and reconstruct linked real findings |
| [`CodeSentryAI/lockbud`](https://github.com/CodeSentryAI/lockbud) | Concurrency, deadlock, atomicity, and memory-safety leads | Include only cases relevant to the claimed theorem and use non-UB concurrency bugs as calibration |
| [`rust-lang/miri`](https://github.com/rust-lang/miri) | Small executable UB examples covering validity, initialization, alignment, aliasing, provenance, intrinsics, FFI, races, and target behavior, plus passing controls | Sample every semantic family from compile-fail/run-fail and pass suites; never treat a clean Miri run as a universal proof |
| [`model-checking/kani`](https://github.com/model-checking/kani) and [`verify-rust-std`](https://model-checking.github.io/verify-rust-std/) | Proof harnesses, bounded-model examples, expected failures, and precise tool-scope questions | Use both genuine proofs and deliberately insufficient bounds/models |
| [`tokio-rs/loom`](https://github.com/tokio-rs/loom) and [`MPI-SWS/genmc`](https://github.com/MPI-SWS/genmc) | Weak-memory, scheduling, publication, refcount, and atomic-ordering examples | Preserve each tool's stated execution/model limits; include both found executions and bound/model gaps |
| [Verus](https://github.com/verus-lang/verus), [RefinedRust](https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev), and the [RustBelt artifact](https://plv.mpi-sws.org/rustbelt/popl18/) | Proof-bearing positive controls and examples of theorem/model boundaries | Admit only exact proved propositions and their explicit semantic/tool TCB |
| [`DavisPL/rust-counterexamples`](https://github.com/DavisPL/rust-counterexamples) | Environmental, compiler, build-time, and safe-code counterexamples outside the ordinary unsafe-library abstraction model | Use to test theorem boundaries, deployment assumptions, and TCB reporting |
| [`Speykious/cve-rs`](https://github.com/Speykious/cve-rs) | Deliberate exploitation of compiler/library soundness holes and safe-syntax boundary cases | Fetch on demand only after license review; use as boundary calibration, not a normal crate-audit benchmark |
| [RustMizan](https://sfu-rsl.github.io/rust-mizan/) | Recent RustSec-derived vulnerable/patched crate-, file-, and function-level variants plus mutation/evaluation infrastructure | Revalidate historical licensing and every transformation; reserve privately regenerated variants as holdouts |
| [RustXec](https://github.com/ying-selab/RustXec) | Reproducible vulnerability executions, build logs, fix links, and containers across many recent projects | Import only the memory-safety subset into soundness scoring; treat a reproduced bad outcome as evidence, not automatically as a Rust UB proof |
| [TypePulse artifact](https://zenodo.org/records/14750104) | Type confusion, alignment, layout, transmutation, and lifetime findings | Require upstream confirmation or an independent proof/witness before objective scoring |
| [`lizhuohua/rust-ffi-checker`](https://github.com/lizhuohua/rust-ffi-checker) and [`lizhuohua/rust-mir-checker`](https://github.com/lizhuohua/rust-mir-checker) | FFI ownership/lifetime and MIR bug leads, including trophy cases | Reconstruct from upstream; isolate GPL material and do not promote warnings to oracles |
| [RustSan](https://www.usenix.org/conference/usenixsecurity24/presentation/cho-kyuwon), [ERASan](https://github.com/S2-Lab/ERASan), and [SafeFFI](https://www.usenix.org/conference/usenixsecurity26/presentation/braunsdorf) | Sanitizer-compatible RustSec cases and cross-language lifetime/ownership examples | Use as discovery or executable evidence subject to artifact/license review and exact model limitations |
| [Awesome Rust Checker](https://github.com/BurtonQin/Awesome-Rust-Checker) | A discovery index for MirChecker, FFIChecker, TypePulse, PinChecker, MIRAI, Loom, Shuttle, and newer datasets | Re-run discovery at each corpus refresh; validate all leads against primary repositories |

The registry is intentionally broader than the release-gating suite. A source is
not a usable fixture until its exact artifact, license, expected theorem, and
hidden oracle have been validated.

### Legal disposition ledger

The fixture manifest, rather than this discovery table, is authoritative for
licensing. Use these initial dispositions:

| Material | Metadata/tool license observed | Initial disposition |
|---|---|---|
| Google audit log | Apache-2.0 | Vendor metadata if useful; fetch each audited crate under its own historical license |
| RustSec / imported GHSA | CC0-1.0 / CC-BY-4.0 metadata | Vendor metadata with attribution as required; fetch source/PoCs separately |
| Miri, Kani, Loom, Verus, FFIChecker | Generally MIT, Apache-2.0, or dual-licensed; verify exact files | Vendor selected tests only with notices and per-file review |
| MirChecker | GPL-3.0 | Isolate or link/fetch according to distribution policy |
| Rudra analyzer | MIT OR Apache-2.0 | Tool tests may be vendorable; treat artifact/PoC repositories as link-only until their licenses are confirmed |
| Yuga and its lifetime corpus | No clear redistribution license found in this review | Link-only; reconstruct cases from licensed upstream projects |
| RustMizan / RustXec / TypePulse / research datasets | Dataset wrappers commonly CC-BY-4.0; embedded-source licenses vary | Fetch-by-digest; verify every historical source, PoC, generated file, and container independently |
| ERASan / SafeFFI / RustSan artifacts | Reusable artifact or global license unclear for some material | Link-only until archive-level and per-file review succeeds |
| CVE-Rs | Nonstandard GLWTSPL | Link-only or independently recreate the underlying compiler-boundary case |
| Every historical crate or current challenge repository | Project-specific and revision-specific | Verify `Cargo.toml` plus `LICENSE*` at the exact snapshot; never infer from the current default branch |

Public GitHub access is not redistribution permission, and a dataset license
never silently relicenses embedded projects.

## Mandatory Corpus A: Google Audit Log

The pinned baseline is
[`audits.toml` at commit `2a67b488aa2a4d123e68d95edd1f1916bb3f937e`](https://github.com/google/rust-crate-audits/blob/2a67b488aa2a4d123e68d95edd1f1916bb3f937e/audits.toml),
dated 2026-07-29. It contains 2,177 audit records under 948 crate keys.
There are 103 `ub-risk-3` and 73 `ub-risk-4` records, for 176 high-risk
records across 149 crates. Across all grades, 91 records cite 114 distinct
GitHub or GitLab issue/PR URLs; within the high-risk records, 66 records cite
97 distinct such URLs. These numbers are inventory checks, not semantic labels.
The audit repository is Apache-2.0 licensed; that does not relicense any audited
crate source.

### Closure procedure

An import is complete only after all of the following hold:

1. Parse every `[[audits.<crate>]]` record from the pinned file. Preserve the
   crate key, record ordinal, version/delta range, criteria, notes, reviewer,
   date if present, source aggregation, and every URL.
2. Manually classify every record, including records whose notes are empty,
   records that say no issue was found, and incomplete or difficult audits.
3. Split each independent assertion or bullet in `notes` into an atom, then
   recursively inspect every linked issue, PR body/comment, fixing diff, and
   upstream discussion and atomize every additional independently checkable
   defect or proof claim. A note such as “multiple issues” is not one atom.
   Give source-derived atoms their own IDs and preserve the edge back to the
   note and audit record.
4. Classify each atom as one of:
   - demonstrated or strongly supported unsoundness;
   - a missing or invalid proof, safety contract, or safety comment;
   - a reachable safe-surface or visibility defect;
   - a configuration, generator, FFI, concurrency, panic, layout, validity, or
     other coverage defect;
   - a documented-postcondition defect;
   - auditability or maintenance debt without a claim of unsoundness;
   - an explicit no-known-defect result;
   - an unconfirmed or disputed claim; or
   - irrelevant to unsafe-code authoring and audit.
5. Resolve cross-record edges such as “same review as previous” and
   “see `<other crate>`.” Preserve every duplicate record-to-atom mapping even
   when execution artifacts are de-duplicated.
6. For delta audits, acquire both baseline and final source, preserve Cargo
   Vet's final-version semantics, and determine whether the note describes a
   newly present issue, a baseline issue, or an issue repaired by the final
   version. Resolve package identity and archive checksum from metadata rather
   than deriving it from the audit key.
7. Follow every linked issue, PR, commit, advisory, and upstream discussion.
   Validate that the cited source version actually contains the described code.
   A risk grade or audit note is not enough to establish the oracle.
8. Map every valid atom to an exact source snapshot and location. Where
   possible, record a safe reproducer, the fixing change, and the smallest
   authoritative Rust contract needed to adjudicate it.
9. Give every record and atom a stable ID such as
   `GRA:<audit-commit>:<crate-key>:<record-ordinal>:<atom-ordinal>`.
10. Give every extracted URL a disposition: incorporated evidence, duplicate,
    irrelevant, inaccessible, moved, or rejected with a reason. Record totals
    by URL kind.
11. Generate a closure report proving:
   - 2,177 of 2,177 records are classified;
   - every note atom, recursively source-derived atom, and URL has a
     disposition;
   - every confirmed atom appears in at least one blind fixture;
   - every `ub-risk-3/4` record appears either as a finding fixture or a
     calibration candidate with a recorded sampling/exclusion decision; and
   - no fixture exposes its audit record, links, expected answer, or fix.

Keyword extraction is useful for triage but is never the closure argument.
Phrases such as “issues found,” “unsound,” “undefined behavior,” “incorrect
safety comment,” “uninitialized,” and “missing safety documentation” miss
indirectly worded findings and can misclassify historical or hypothetical
discussion.

### Required fixture forms

Every confirmed issue atom gets a focused blind fixture containing enough
unaltered context to derive the issue but no oracle leak. Every multi-issue
record also gets a combined fixture to test whether the agent stops after its
first finding. Representative crates from every risk grade get full,
history-stripped source audits to test discovery in realistic noise.

High-risk records with no proved defect are essential negative/calibration
cases. The correct result may be a scoped `UNPROVED`, a documentation gap, or
an expensive but successful proof; the evaluator must not reward invented UB.

The audit log already supplies diverse regression leads, including:

- invalid layout, validity, transmute, and representation assumptions;
- premature `set_len` and uninitialized-memory exposure;
- aliasing, interior-mutability, and lifetime extension;
- panic/unwind and destructor invariants;
- mutable statics, Send/Sync, callbacks, and global handlers;
- `target_feature`, SIMD, architecture, OS, allocator, and debug-assertion
  branches;
- FFI declarations, ABI types, foreign ownership, and error behavior;
- unsafe macros and generated safe APIs;
- public pointer or invariant-bearing fields, `#[doc(hidden)]` items, sealing,
  and unsafe trait contracts;
- wrong, incomplete, or missing safety comments; and
- code that appears alarming but for which the auditor did not establish
  unsoundness.

These are discovery aids, not an exhaustive hazard taxonomy. The record/atom
closure check is what makes this corpus exhaustive.

## Mandatory Corpus B: RustSec and Advisory Feeds

The research checkout of RustSec is pinned at commit
[`7c7ccac53056b87f69ac677f15ea2d9a98a6f8e2`](https://github.com/RustSec/advisory-db/commit/7c7ccac53056b87f69ac677f15ea2d9a98a6f8e2).
At that snapshot, 192 crate advisory files contain
`informational = "unsound"` and `rust/std` contains 18 standard-library
advisory files.

RustSec's own advisory metadata is CC0-1.0; imported GitHub advisory metadata
may be CC-BY-4.0. Neither license applies to the underlying vulnerable source,
PoCs, containers, or generated artifacts.

The importer must not stop at those 192 records. Some concrete
memory-corruption vulnerabilities are not informational “unsound” advisories,
and one advisory may describe several defects. Search all RustSec records for
Rust UB and memory-safety categories, descriptions, aliases, keywords,
affected functions, and references. Reconcile aliases against GitHub's
advisory database and OSV, then atomize each distinct defect.

For each atom:

- acquire the exact affected crate release from crates.io and verify its
  checksum, or pin the exact repository commit if no published artifact exists;
- acquire the first known fixed release or commit separately;
- validate affected and patched ranges instead of trusting a title;
- preserve the safe reproducer when one exists, but hide it from blind agents;
- distinguish UB reachable from valid safe use, misuse of an unsafe API,
  ordinary security bugs, panic/DoS, unmaintained status, and withdrawn or
  disputed claims;
- de-duplicate against Google audit-log, research-corpus, and upstream issue
  atoms while retaining all provenance; and
- retain the vulnerable/fixed pair even if the fix merely narrows the API or
  changes its contract.

The complete RustSec-derived set is a release-scale suite. A stratified subset
is appropriate for rapid iteration, but every imported atom must remain
scheduled for a periodic exhaustive run.

## Mandatory Corpus C: Zerocopy

### Historical vulnerable/fixed registry

The history search produced this pre-admission registry. Full hashes shown with
an ellipsis must be resolved from repository history before materialization.
Before promotion from `Candidate`, the private manifest must add exact affected
paths, trigger configurations, affected/fixed releases, and a two-reviewer
source theorem. Unqualified `#NNN` references in this section are
`google/zerocopy` issues or pull requests.

| Case | Vulnerable state | Fixed state / primary source | Primary evaluation value | Initial class |
|---|---|---|---|---|
| Allocation `Layout` overflow | `173cd8eb117a967b6bb72c0b78cdac27e2100b31` | [`f3d80a93210d246a509bf56eed8bce6780b8160f`](https://github.com/google/zerocopy/commit/f3d80a93210d246a509bf56eed8bce6780b8160f), #63 | `usize` multiplication does not establish `Layout`'s `isize::MAX` bound; pointer-width/`alloc` case | Candidate |
| `MaybeUninit<T>` unsafe impls, 0.7 | `cb20ba09…` | `62f76d2a…`, #299/#308 | `T` containing `UnsafeCell` violates the unsafe trait theorem | Candidate |
| `MaybeUninit<T>` unsafe impls, 0.6 backport | `9bc48cc9…` | [`c33bc318160692090145d1e00f72259eab09ded5`](https://github.com/google/zerocopy/commit/c33bc318160692090145d1e00f72259eab09ded5), #309 | Same root obligation in a distinct release line | Candidate |
| `Ref::into_ref` / `Ref::into_mut` | `a8572dafd9a0a5f5f583ab4c16e62dab9b664b15` and affected releases | 0.7 fix `3c1a56ac…`, other backports, 0.8 fix [`dad47d5ca87595f11881657d377f595be471e65b`](https://github.com/google/zerocopy/commit/dad47d5ca87595f11881657d377f595be471e65b), #716/#721/#755, [RUSTSEC-2023-0074](https://rustsec.org/advisories/RUSTSEC-2023-0074.html) | Runtime guard ownership/lifetime, safe returned-reference API, released-range reconstruction | Candidate |
| `Ptr::forget_valid` | `f4995df6…` | [`7e62d435e1a9db1edc03d579c8f61f50d5ae37eb`](https://github.com/google/zerocopy/commit/7e62d435e1a9db1edc03d579c8f61f50d5ae37eb), #898 | `Valid` does not imply padding is initialized; non-total invariant ordering | Candidate |
| Generated “at least” invariant | `674e7fb1…` | [`449eaff57eea3d9328e96fe3c7a7cdc45991f4c6`](https://github.com/google/zerocopy/commit/449eaff57eea3d9328e96fe3c7a7cdc45991f4c6), #909 | The same false relation generated through a macro | Candidate |
| Atomic transparent wrapper | `4c3165f1…` | [`418555a37f3f92c89ce435624b38f215df515acb`](https://github.com/google/zerocopy/commit/418555a37f3f92c89ce435624b38f215df515acb), #1028/#1585 | Missing inner bound for `AtomicBool`; validity plus `target_has_atomic` | Candidate |
| Safe `IntoByteSlice` trait | `d2e6bb8f…` | [`0f4ef070c76cbb33e5654410e35a1f2790a12500`](https://github.com/google/zerocopy/commit/0f4ef070c76cbb33e5654410e35a1f2790a12500), #1215/#1261 | A caller-provided safe impl can violate the exact-range invariant | Candidate |
| Generic `repr(C, align(N))` derive | `2d5ef9f9…` | [`8e0de3fa2275f91abca38be83146136eb7fc726b`](https://github.com/google/zerocopy/commit/8e0de3fa2275f91abca38be83146136eb7fc726b), #1748/#1752 | Derive input closure and generic padding | Candidate |
| `repr(Rust)` derive follow-up | resolve from #1764 | resolve from #1783 | Separate derive-input/layout atom | Candidate |
| Aligned-enum derive follow-up | resolve from #1758 | resolve from #1784 | Separate enum layout/padding atom | Candidate |
| `Ptr::read_unaligned` | `2c237a30…` | [`040557496ce7a0b1dac08c11c5ae37268b5d7b85`](https://github.com/google/zerocopy/commit/040557496ce7a0b1dac08c11c5ae37268b5d7b85), #1892/#1893 | Shared aliasing/interior mutability across `UnsafeCell` | Candidate |
| Transient internal `Ptr::split_at` | change introduced immediately before #1890 | fixed before stable release, #1890 | Internal latent defect versus released safe-API/reachable-execution scope | Candidate calibration |
| Mutable transmute, original | `3ad056be…` | partial fix `118b6f3b18a4ae997768860f3256a83b3a00990f`, #2226/#2229 | `&mut Dst` writes may invalidate the shadowed `Src` | Candidate |
| Mutable transmute, partial fix | `118b6f3b18a4ae997768860f3256a83b3a00990f` | complete follow-up `25d27d579fc8ec9177384ff1e8175b8bf9f4838e`, #2331 | Detecting uncovered `TryFromBytes::*mut*` consumers | Candidate |
| `FromBytes::read_from_io` | `49a13ba9…` | [`f99854afb33365e9dada073a166b3047df7109d1`](https://github.com/google/zerocopy/commit/f99854afb33365e9dada073a166b3047df7109d1), #2319/#2358 | Arbitrary caller-provided safe `Read::read` can inspect uninitialized padding; the selected-safe-dependency exception does not apply | Candidate |
| DST/aligned-enum padding | `8647029c…` | [`ed93a1926701a1ac6e434e322a17473ac890ec8e`](https://github.com/google/zerocopy/commit/ed93a1926701a1ac6e434e322a17473ac890ec8e), #3063/#3064, fixed in 0.8.40 | Dynamic trailing padding and aligned enum cases | Candidate |
| Exclusive `Ptr::iter` | `5fc5d5be…` | [`f70e4224996ed73b2cd927719246361d977a629e`](https://github.com/google/zerocopy/commit/f70e4224996ed73b2cd927719246361d977a629e), #3419/#3421, fixed in 0.8.50 | Two calls through `&self` yield overlapping exclusive pointers | Candidate |
| `CastUnsized` safety proof | `5c67d2c8…` | [`7cc13f19f042482750f68c4abe0adecebc4d67e6`](https://github.com/google/zerocopy/commit/7cc13f19f042482750f68c4abe0adecebc4d67e6), #2908 | Invalid comment/proof, without automatically implying runtime unsoundness | Candidate calibration |
| Previously unprovable `size_of_val_raw` argument | `a51d64fc…` | [`50d9d621284c5b64ac371d1f1b1f2381fec30d1b`](https://github.com/google/zerocopy/commit/50d9d621284c5b64ac371d1f1b1f2381fec30d1b), #1574 | A documentation gap later closed by a stronger std contract | Candidate calibration |
| Raw-pointer read-only contract | parent of `403a890f…` | `403a890fcab08942c33e83d02884548544e31fe7`, #1607/#1617 | Contract needed to forbid assuming write permission | Candidate |
| Stale `SizeEq` contract | `09334fd9…` | `81a0fd941138c309e5309a29285e74300be7d2de`, #2564 | Implementation evolution without invariant-documentation evolution | Candidate |
| Missing/versionless citations | `9483f7dd…` | `16d065d1d59393cdcadbbce573a02b2279be59a9`, #1655/#2800 | Exact/versioned authority and independent citation verification | Candidate calibration |

Retain these zerocopy-specific non-defect/uncertainty controls:

- [#1757](https://github.com/google/zerocopy/issues/1757), a hypothesized
  packed-union issue rejected under the supported inputs and generated padding
  check;
- [#672](https://github.com/google/zerocopy/pull/672), an explicitly
  non-soundness `repr(C, packed(N))` regression;
- [#1086](https://github.com/google/zerocopy/issues/1086), a target build
  failure rather than demonstrated UB;
- [#874](https://github.com/google/zerocopy/issues/874), a
  potentially-unsound ZST/provenance concern not shown exercisable; and
- [#3380](https://github.com/google/zerocopy/issues/3380), a
  compiler/coinduction concern rather than a demonstrated current zerocopy
  exploit.

Search all branches and releases for `unsound`, `soundness`, `undefined
behavior`, `UB`, safety-comment fixes, RustSec/GHSA identifiers, and changes
that make an item or trait unsafe. Do not assume commit messages use those
words. Diff public safety contracts and consult changelog/advisory history.
Every distinct historical incident becomes a paired fixture; the fixing diff is
hidden from both agents in the pair.

### Current open-world audit

The current baseline is
[`53a3fbfa15d656b25b74688369f7248ff354a021`](https://github.com/google/zerocopy/commit/53a3fbfa15d656b25b74688369f7248ff354a021),
described locally as `v0.8.55-3-g53a3fbfa1`. It is assumed to be a
high-quality candidate, not assumed to be proved sound. A valid novel finding
must never be scored as a false positive merely because the code is current.
Materialize the fixture from that immutable commit object, not by copying the
possibly dirty live worktree.

The hidden minimum oracle for that snapshot must include these already known
questions and defects:

- [#2762](https://github.com/google/zerocopy/issues/2762): a nondeterministic
  function-like proc macro can make repeated field-type tokens expand
  differently, so a derive may validate one type and generate an unsafe impl
  for another; owner: proc-macro shard. The hygiene check in
  `830bc15e5…` does not repair nondeterministic repeated expansion;
- [#388](https://github.com/google/zerocopy/issues/388): an attribute proc
  macro running after a derive can mutate the item after the derive inspected
  its earlier shape; owner: proc-macro shard;
- [#2941](https://github.com/google/zerocopy/issues/2941): union field
  projection may treat validity through one overlapping field as validity of a
  different field; owners: pointer-projection and hidden-API shards;
- [#899](https://github.com/google/zerocopy/issues/899): deliberately unsound
  `#[cfg(test)]` implementations, which must be scoped to test executions rather
  than misreported as a shipped production API defect; owners:
  built-in-implementations and nonshipping-test-configuration shards;
- [#2965](https://github.com/google/zerocopy/issues/2965): validity-contract
  prose that may omit safety/provenance facts; owner: invariant-representation
  shard;
- [#2319](https://github.com/google/zerocopy/issues/2319): remaining
  constructor/padding documentation questions after the I/O implementation
  repair; owners: trait-contract and layout shards;
- [#1792](https://github.com/google/zerocopy/issues/1792): union
  `IntoBytes` derivation behind `zerocopy_derive_union_into_bytes`, with an
  explicit conditional assumption and unsettled union-validity basis; owners:
  proc-macro/generated-output and configuration shards; and
- [#3199](https://github.com/google/zerocopy/issues/3199): unfinished proof
  obligations for `layout::cast_from`, for which `UNPROVED` may be correct
  without a UB witness; owner: layout/proof shard.

These are a lower bound, not a complete answer key. Some are proof or
configuration questions rather than demonstrated production unsoundness.
Agents must independently derive the right classification and may find
additional valid issues. Their initial admission class is `Candidate` or
`Challenge`; an open issue alone does not make an objective defect oracle.

Use separate fresh agents for these audit units:

1. trait theorems and every safe method/surface in `src/lib.rs`;
2. pointer invariant representation in
   `src/pointer/{inner,invariant,ptr}.rs`;
3. pointer operations, projection, iteration, and splitting in `src/pointer/`,
   `src/lib.rs`, and `src/split_at.rs`;
4. transmutation algebra in `src/pointer/transmute.rs`, related pointer
   methods, and transmute macros;
5. byte-slice, `Ref`, borrow-guard, ownership, and returned-reference behavior
   in `src/byte_slice.rs` and `src/ref.rs`;
6. wrapper lifetimes, interior mutability, allocation, and destruction in
   `src/wrappers.rs`;
7. primitive, atomic, function-pointer, SIMD, float, and validity
   implementations in `src/impls.rs` and `src/byteorder.rs`;
8. layout/allocation arithmetic, ZSTs, DST metadata, and allocation failure in
   `src/layout.rs`, `src/util/mod.rs`, and alloc branches;
9. declarative macros and hidden support in `src/macros.rs` and `src/util/`;
10. the entire proc-macro generator as a theorem over every accepted token
    stream and interaction with other macros/attributes;
11. every checked-in generated output class and representative instantiated
    expansion under `zerocopy-derive/`;
12. build-script-produced Rust-version cfgs, feature closure, target
   architecture, endianness, atomic widths, SIMD/nightly modes,
   `debug_assertions`, `alloc`/`std`, documentation cfgs, Kani/Miri cfgs, and
   unstable/internal configurations that can ship;
13. all reachable `#[doc(hidden)]` safe surfaces, including direct downstream
    access and mutation possibilities;
14. dependency and TCB contracts; and
15. an integration pass that consumes the shard reports and proves or refuses
    the requested whole-crate conclusion.

The current configuration manifest must investigate, then classify from pinned
project policy:

- features `alloc`, `std`, `derive`, `simd`, `simd-nightly`, and
  `float-nightly`;
- architectures including `arm`, `aarch64`, `x86`, `x86_64`, `wasm32`,
  `powerpc`, and `powerpc64`;
- endianness, 16-bit pointer-width paths, and atomic widths 8/16/32/64/ptr;
- every build-script Rust-version cfg from the MSRV through current,
  including gates associated with Rust 1.57, 1.59, 1.60, 1.61, 1.78, 1.81,
  1.87, and 1.89;
- `zerocopy_derive_union_into_bytes`, `zerocopy_unstable_ptr`,
  `zerocopy_unstable_linux`, `zerocopy_inline_always`, `no_fp_fmt_parse`, and
  internal dev/nightly cfgs; and
- build/proc-macro host-target differences.

Do not assume that every syntactically present axis is supported or shippable.
Classify each combination as shipping-library, host-build, test-only,
documentation-only, analysis-only (for example Miri/Kani/coverage), internal,
or unsupported, with source evidence. The downstream theorem quantifies over
the actual supported shippable set; separate the other classes so they can be
audited without contaminating that theorem.

The intentionally unsound test-only implementations marked
`FIXME(#899)` in `src/impls.rs` are a scope-calibration fixture. An agent must
notice them when tests are in scope, but must not claim that an excluded
test-only path ships to downstream library users. Generated expected-output
files and derive tests remain useful for proving what the proc macro emits.

For the hidden-API shard, state explicitly that `#[doc(hidden)]` ordinarily
removes documentation/SemVer expectations but does not relax soundness
according to the item's safe/unsafe marking. Direct downstream use is not
forbidden misuse merely because Rustdoc omits the item.

The integration agent must receive raw source plus normalized shard reports,
not this catalog or historical answers. A time-bounded inability to close the
current whole crate should yield a precisely scoped `UNPROVED`, not an
optimistic or pessimistic verdict.

## Broader Real-World and Research Corpora

### Rust standard library and compiler

Cross-reference RustSec's `rust/std`, `Qwaz/rust-cve`, closed
`I-unsound` + library-team issues, fixing PRs, and
`tests/ui/known-bug` cases. Library implementation bugs are direct unsafe-code
fixtures. Compiler bugs test a different TCB boundary and must be labeled as
such; they must not be mixed into a score for author-written unsafe-library
proofs without a separate theorem. A `tests/ui/known-bug` case usually records
a pinned compiler regression expectation; it is not automatically an
unsafe-library-authoring defect.

High-value adversarial-safe-caller pairs include:

- [`Borrow` returning different values across calls](https://github.com/rust-lang/rust/issues/80335)
  and its fixing PR #81728;
- [`Read` returning a count larger than the supplied buffer](https://github.com/rust-lang/rust/issues/80894),
  fixing PR #80895, and documentation clarification #82892; and
- [a panicking callback observing `String::retain`'s temporary invariant
  violation](https://github.com/rust-lang/rust/issues/78498), initial repair
  #78499, and follow-up #82554.

The incomplete first `String::retain` repair is a useful partial-fix fixture.
These cases test arbitrary type-valid behavior, panic, reentrancy, and repeated
queries from caller-controlled safe code.

The 186-incident Artisan-Lab corpus reports 33 standard-library, 142
third-party-library, 10 executable, and one compiler case. Use it to discover
older issues missing from modern advisory filters, then revalidate every case
against primary source because labels and language rules may have evolved.

The
[Crates and Vulnerabilities dataset](https://zenodo.org/records/7828059)
indexes 84,105 packages, 433 vulnerabilities, 300 repositories, and 218 fix
commits. Its CC-BY-4.0 wrapper is useful for discovery and metadata joins, but
does not relicense embedded crate source.

### Packaged benchmark corpora

[RustMizan](https://github.com/sfu-rsl/rust-mizan) is unusually close to the
desired evaluation shape. Its published dataset contains 42 RustSec
memory-safety CVEs across 25 crates and 173 crate-, file-, and function-level
variants, often with vulnerable and patched sides, annotations, mutation
infrastructure, and Kani/RAPx integrations. Use its runner and transformations
as implementation leads, but independently verify:

- the exact historical code license for every embedded crate;
- that “patched” means only that the disclosed bug is repaired;
- that every supposedly semantics-preserving mutation actually preserves the
  relevant obligation; and
- that public variants have not become recognition tests through model
  training.

Regenerate and privately review metamorphic variants for holdout use.

[RustXec](https://github.com/ying-selab/RustXec) contains 102 vulnerabilities
from 89 projects from 2021–2025, with proof-of-vulnerability executions,
containers, fix links, and build/test logs. Its approximately 88.5 GB artifact
is best fetched on demand. Only its memory-corruption subset belongs in
soundness scoring; other security defects belong in separately labeled
robustness/security tests. Reproducing a disclosed bad outcome does not by
itself prove which Rust abstract-semantic rule is violated.

[TypePulse](https://zenodo.org/records/14750104) contributes 26 known
type-confusion examples and additional reported findings involving
misalignment, layout, transmutation scope, lifetime, and representation.
Analyzer output is a lead until an upstream acknowledgement, independent
witness, or source proof validates the exact snapshot.

### Checker and verifier corpora

For Rudra, Yuga, RAPx and its predecessors, Lockbud, MirChecker, FFIChecker,
TypePulse, and PinChecker:

1. acquire the tool's expected-pass and expected-fail examples;
2. locate every linked upstream issue and fixing commit;
3. distinguish developer-confirmed, independently reproduced, tool-only,
   disputed, and false-positive cases;
4. import real code independently of the detector output;
5. hide tool names, warnings, issue titles, and known reproducers from the
   audit agent; and
6. use the detector output only as an evaluator lead until a human has
   reconstructed the proof or counterexample.

Yuga is particularly useful for lifetime annotation and interprocedural
dataflow. Its repository includes synthetic/RustSec examples and reported
findings in projects such as `bv`, `cslice`, `json-rust`, `sled`, `tokio`, and
audio bindings. Confirmed and unconfirmed reports must be separate strata.

Miri's fail/pass suites provide precise microfixtures but measure different
behavior:

- a failing execution can witness an error under Miri's model and exact run;
- a passing execution does not prove soundness for all inputs/configurations;
- a fixture about unsupported behavior can test whether the agent records a
  model or documentation gap; and
- a sound tool with a proved exhaustive harness may discharge a stronger claim
  than ordinary sampled testing.

Kani and other proof tools should therefore contribute paired evidence
fixtures: one whose documented model and exhaustive harness imply the claimed
proposition, and one with a missing bound, environmental model, configuration,
or tool premise. The evaluation asks the agent to accept only the exact theorem
actually established.

Use [Loom](https://github.com/tokio-rs/loom) for controlled concurrency pairs
involving publication, refcounts, wakeups, aliasing, and memory ordering, but
retain its documented scheduling/model limitations in the hidden oracle. Use
[GenMC](https://github.com/MPI-SWS/genmc) as a complementary LLVM-level
weak-memory source after per-file license review.

Verus, RefinedRust, RustBelt, and `verify-rust-std` can supply genuine scoped
positive controls. The evaluator must preserve the exact specification,
semantic model, trusted toolchain, admitted axioms, and connection between the
proved artifact and audited code. A theorem about λRust or a translated/model
program is not silently a theorem about every detail of the current Rust
implementation.

Rudra's published work reported 264 bugs and 76 CVEs and is valuable for unsafe
generics/traits, uninitialized exposure, higher-order invariants, panic safety,
and Send/Sync. Its analyzer repository is permissively licensed, but the
inspected artifact/PoC repositories do not clearly grant the same license. Use
those as indexes and reconstruct fixtures from exact upstream crate revisions.

FFIChecker contributes FFI ownership, use-after-free, and double-free cases.
MirChecker contributes FFI lifetimes, possible double frees, and many
non-soundness arithmetic/panic warnings. The former is MIT; the latter is
GPL-3.0. Keep GPL material isolated and independently adjudicate both tools'
trophy cases.

RustSan selected ASan-compatible RustSec cases; ERASan contains additional
RustSec proof-of-concept material; and SafeFFI supplies vulnerable and benign
cross-language pairs, patched compiler/runtime pieces, and probabilistic
AArch64 HWASan tests. Where a reusable artifact or redistribution license is
unclear, retain only a link/acquisition recipe. Sanitizer failures are concrete
execution evidence; sanitizer silence does not cover all validity, provenance,
race, configuration, or execution obligations.

### Recent public development cases

The following 2026 leads are useful public development fixtures:

- [`jxl-grid` GHSA-5pmv-rx8r-wmv5](https://github.com/tirr-c/jxl-oxide/security/advisories/GHSA-5pmv-rx8r-wmv5),
  a 32-bit integer-overflow/out-of-bounds-write case with a vulnerable/fixed
  release pair and Miri reproducer;
- [`intrusive-rs` PR #104](https://github.com/Amanieu/intrusive-rs/pull/104)
  and adjacent 2026 fixes, covering use-after-free, iterator/splice
  transitions, concurrency, and panic safety;
- [`rkyv` issue #670](https://github.com/rkyv/rkyv/issues/670), involving
  crafted-archive out-of-bounds behavior; and
- current RustSec records such as exception-safety/uninitialized-value and
  bounds-checking unsoundness.

At each refresh, search advisory feeds, `I-unsound` issues, fixing PRs, Miri
regressions, and maintained checker result lists for newer cases. Keep holdout
identities and answers outside this repository in an access-controlled store.
Checked-in named cases are never “private holdouts,” regardless of their age.
Refer to true holdout cohorts only by opaque cohort/version IDs.

### Environmental and adversarial-safe-code boundaries

`rust-counterexamples` and selected compiler/OS cases test whether the agent
correctly separates:

- source-level Rust soundness from an OS, filesystem, process, or deployment
  theorem;
- trusted deliberately selected dependency behavior from arbitrary
  caller-provided safe code;
- compiler/std assumptions from library implementation proof;
- build-time or linker behavior from a runtime UB claim; and
- unconditional soundness from a cryptographic, negligible-probability, or
  deployment-restricted claim.

These fixtures are expected to produce qualified TCB entries and scoped
verdicts, not one universal classification.

## Hand-Built and Metamorphic Fixtures

Real incidents do not cover every load-bearing instruction in isolation.
Create small hand-proved fixtures for:

- public fields, constructors, safe methods, safe trait methods, and
  macro-generated safe APIs as alternate invariant-bypass surfaces;
- a properly sealed trait, an incompletely sealed trait, and a soundness
  requirement placed only in safe trait prose;
- a `pub(super)` invariant-bearing safe field versus a compiler-enforced
  public `unsafe` field with a complete contract;
- delayed dataflow in which an unsafe function stores state consumed by a later
  function;
- a caller callback or safe trait implementation that returns a type-valid but
  adversarial value, panics, reenters, or mutates accessible state;
- a deliberately selected safe dependency API versus caller-provided safe
  code with identical-looking documentation;
- a third-party unsafe dependency that is audited, admitted precisely, or
  silently trusted;
- a valid `SAFETY` citation, a misquote, a wrong-version citation, and a
  citation whose context does not imply the asserted fact;
- an unsafe API that is UB-free but violates a promised postcondition;
- a postcondition weakening or safety-precondition strengthening across
  SemVer, exact-pin, in-tree-fork, and out-of-band contract channels;
- UB hidden behind a feature/target/cfg combination, macro expansion,
  build-script result, allocator, panic path, `debug_assertions`, SIMD feature,
  or architecture;
- a cryptographic-signature or hash-collision guarded bad path;
- an execution that eventually exhibits UB, testing rejection of “before the
  UB was still guaranteed” reasoning;
- a deployment-restricted binary whose conditional theorem is valid but whose
  API would be unsound if exported safely; and
- a proof-producing static analysis result versus a sampled or bounded result
  that does not establish the requested universal claim.

Prefer reversible mutations of real fixed code over invented anti-patterns.
Examples include restoring one hunk of a historical fix, moving a check under
`debug_assert!`, exposing one private invariant-bearing field, deleting one
safety-contract conjunct, or generating the same defect through a macro. Each
mutation must have a human-reviewed proof that it changes exactly the intended
obligation and does not leak the answer through naming.

## Coverage Dimensions

The fixture manifest must tag, but must not assume exhaustiveness from, these
dimensions:

- raw pointer allocation, provenance, bounds, alignment, liveness, and access;
- references, aliasing, interior mutability, and concurrency;
- initialization, padding, byte exposure, and type validity;
- layout, `repr`, DST metadata, enums, `bool`, niches, and transmutation;
- arithmetic, indexing, capacity/length, zero-sized types, and address spaces;
- ownership transfer, panic/unwind, cancellation, reentrancy, drop, and leaks;
- lifetimes, variance, higher-ranked bounds, Pin, self-reference, and callbacks;
- unsafe traits/impls, Send/Sync, safe implementers, and sealing;
- FFI, ABI, unwinding, foreign allocation, symbols, linker behavior, and
  external specifications;
- atomics, races, memory ordering, and global/static state;
- target architecture/OS/endian/pointer width/atomic width, SIMD and
  `target_feature`, features, allocator, panic strategy, optimization,
  `debug_assertions`, toolchain version, and build/proc-macro output;
- all safe API surfaces, including hidden and generated surfaces;
- local invariant composition across functions and time;
- authoritative citations, documentation gaps, dependency trust, and TCB
  non-vacuity;
- mandatory postconditions, robustness scope, and contract evolution;
- probabilistic/deployment assumptions and exact verdict scope; and
- evidence interpretation, including testing, interpreters, static analysis,
  model checking, deductive verification, and manual proof.

This tag set is for measuring diversity and detecting omissions. The real
closure rule is proposition-based: every known issue atom and every requested
skill behavior must have a fixture.

## Fixture Admission and Provenance

A source's admission class determines how it may be scored:

- **Objective defect:** two independent reviewers have produced and reconciled
  an authority-rooted source theorem for the exact artifact, valid-use path,
  violated or missing proposition, and status. A runtime witness, upstream
  acknowledgement, vulnerable/fixed pair, formal result, and reproducer are
  independent corroboration tags; none substitutes for the source theorem.
- **Candidate:** an advisory, audit note, analyzer report, unresolved issue, or
  incomplete human argument still requires adjudication. It may test review
  behavior but cannot contribute to objective defect-recall scoring.
- **Scoped positive proof:** two reviewers have accepted a complete proof of an
  exact property under an explicit model and TCB. The proof may be rigorous
  English or machine-checked; machine form is not required.
- **Bug-specific fixed control:** the known defect theorem is false on the
  fixed artifact for a proved reason. This says nothing about other defects or
  whole-artifact soundness.
- **Challenge:** no complete positive or negative oracle. Score process, scope,
  and independently adjudicated findings; never score “agrees with no known
  bug” as soundness.

Record corroboration independently, for example `UPSTREAM-ACK`, `VULN-FIXED`,
`EXEC-WITNESS`, `FORMAL-WITNESS`, `SAFE-REPRODUCER`, and `MULTI-REVIEW`.

A fixture is admitted only when its hidden manifest records:

- stable fixture and oracle-atom IDs;
- `theorem_domain` and `boundary_class`, separating author/library unsafe
  abstractions, standard-library implementations, compiler TCB bugs,
  OS/FFI/environment/deployment claims, build/proc-macro/supply-chain
  execution, and non-UB robustness/security;
- all source URLs and immutable revisions/checksums;
- acquisition date and exact files included;
- vulnerable and fixed revisions, when applicable;
- affected Rust/compiler/dependency versions;
- supported and trigger configurations;
- license/SPDX expression, attribution, and redistribution decision;
- separate metadata, historical source, PoC/harness, generated-file, and
  container licenses, with disposition `vendor`, `fetch-by-digest`,
  `link-only`, or `exclude`;
- the exact claim the evaluation asks the agent to establish;
- a human-reviewed explanation for every known finding and accepted
  alternative reasoning;
- authoritative Rust/std citations or an explicit documentation/TCB gap;
- safe reproducers, tool results, and their limits;
- expected status for soundness, postconditions, and conditional claims;
- fixture transformations and a semantic-equivalence review;
- all oracle-leak removals;
- duplicate links to other corpora; and
- confidence, disputes, and required human adjudication.

Do not redistribute code when its license is absent, incompatible, or unclear.
Store an acquisition recipe and digest and fetch it on demand. Preserve all
required notices for vendored fixtures.

## Refresh Checklist

Before a release-scale evaluation:

1. Pin new commits for every database and discovery index.
2. Re-run exhaustive record/atom classification for changed records.
3. Search zerocopy and other designated repositories for new advisories,
   unsoundness issues, contract changes, and safety-comment fixes.
4. Import new RustSec/GHSA/OSV and standard-library incidents.
5. Search recent checker publications and primary issue trackers.
6. Reserve a private, recent holdout cohort.
7. Revalidate old fixtures against their pinned compiler and documentation.
8. Recheck licenses, acquisition digests, links, and oracle isolation.
9. Publish a corpus revision manifest and change summary.
10. Never rewrite prior result records to use the new corpus retroactively.
