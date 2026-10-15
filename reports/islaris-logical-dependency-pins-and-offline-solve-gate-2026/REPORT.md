# Islaris logical dependency pins and the offline solve gate

## Summary

The pinned Islaris/Lithium metadata determines an exact Iris revision and one
matching stdpp/bitvector/unstable family. Coq 8.19.0 excludes released bbv 1.4;
bbv 1.5 is a metadata-compatible candidate. Historical metadata supplies the
requested Dune 3.9.1 package family where the inspected modern snapshot lookup
failed. These source-backed selections support a reproducible offline solver
request; no complete dependency solution, installation or proof replay was
performed.

## Applicability

The subjects in REPORT.json describe one proposed combination: Islaris at
c978e10f50db5c40f0fdf113f5f76a779782c6f9 with Lithium's dated development
package, Coq 8.19.0, Dune 3.9.1, the older Sail 0.17/RISC-V Coq bridge, and the
exact package-metadata snapshots used to inspect their constraints. The modern
and historical OCaml opam snapshots are compared as metadata inputs; they are
not installed switches. bbv 1.5 is a proposed addition rather than a witnessed
upstream Islaris lock. The record-update and bbv archive hashes were read from
released metadata; the archive bytes were not acquired.

GitHub mirrors provide readable immutable primary files for Iris/stdpp/Lithium
and their opam metadata. The original GitLab repository URLs remain the package
source coordinates. The inspected Lithium mirror commit is the exact commit
named in official package metadata, not that mirror's modified default branch.
No claim extends to arbitrary later versions or modern Sail/Lean output.

## Findings

Basis: direct **source** inspection and upstream **documentation**, with
**derived** compatibility conclusions from the stated version formulas. No
compiler, opam solver, installer or prover execution is evidence for these
findings. In particular, satisfying a metadata formula does not establish that
packages build together or that a selected theorem checks.

### Exact logical package requests

| Package | Exact opam request | Immutable source commit |
|---|---|---|
| Islaris | local package at selected commit | rems-project/islaris `c978e10f50db5c40f0fdf113f5f76a779782c6f9` |
| coq-lithium | `dev.2024-09-11.0.7945a29d` | iris/refinedc `7945a29d1647970709a9b5ad2ffc53c757e130cc` |
| coq-iris | `dev.2024-09-10.1.6f24ed4b` | iris/iris `6f24ed4baa4d61967a95bac834eab2c66f3b76fa` |
| coq-stdpp | `dev.2024-09-10.3.a1a12e00` | iris/stdpp `a1a12e00fba07f2e41ccd74a8b593b88e48fc2c3` |
| coq-stdpp-bitvector | `dev.2024-09-10.3.a1a12e00` | same stdpp commit |
| coq-stdpp-unstable | `dev.2024-09-10.3.a1a12e00` | same stdpp commit |
| coq-record-update | `0.3.3` | released v0.3.3 archive, SHA512 below |
| coq-bbv | proposed `1.5` | mit-plv/bbv `c53d5b95c70839ae8e947010d85503bd1ada1120` (resolved v1.5) |

This chain is forced by inspected metadata, rather than guessed from chronology:
Islaris selects Lithium's dated version; Lithium selects the exact Iris version;
Iris selects the exact dated stdpp version. Bitvector depends on stdpp
`= version`; unstable depends on both stdpp and bitvector `= version`. Select
all three companions at the same dated version. Do not replace these requests
with `.dev`: the package formulas permit that escape, which would abandon the
selected compatibility chain.

Evidence is the [Lithium package metadata](https://github.com/rocq-iris/opam/blob/3c21518b509d33676776c36e160de1d76835b801/packages/coq-lithium/coq-lithium.dev.2024-09-11.0.7945a29d/opam),
[Iris package metadata](https://github.com/rocq-iris/opam/blob/3c21518b509d33676776c36e160de1d76835b801/packages/coq-iris/coq-iris.dev.2024-09-10.1.6f24ed4b/opam)
and the three matching stdpp metadata files preserved in
[preserved primary metadata](support/ISLARIS-primary-files.json). Direct pinned source opams for Iris and stdpp
confirm the dependency formulas. The exact Lithium source opam was readable
through the UIC-verif-group/refinedC mirror at the same full commit; the opam
package URL remains the original MPI repository. No modified UIC branch is
selected.

Read-only GitLab web access failed. Discovery found the rocq-iris GitHub mirror
of the official Iris opam repository, resolved once to
`3c21518b509d33676776c36e160de1d76835b801`; all subsequent metadata reads used
that immutable commit. These are primary repository metadata, not secondary
compatibility recommendations. Retain that exact repository snapshot for solving.

### bbv and the old Sail stack

Pinned coq-sail 0.17 requires coq>=8.14 and coq-bbv>=1.3, and conflicts with a
Sail package whose version differs from 0.17. The selected old Sail commit's own
opam confirms version 0.17. Its generator must remain
`b14f649845db850b3673696e2aa90565fa2a60ef`; coq-sail remains
`169934e27ceafe393ed4d365985f7b12d974d56e`; coq-sail-riscv remains
`837ede9b39fae2aa97849da89c4b3b5a93344890` (package version 0.5).
The obsolete separate deps/Makefile Sail target at `605cd…` is not selected.

The released coq-bbv 1.4 metadata requires Coq<8.19~ and therefore excludes the
requested Coq 8.19.0. Released 1.5 explicitly permits Coq>=8.16,<9.2~ and supplies
an immutable content hash. Select 1.5 as a new source-backed candidate; this is
metadata compatibility, not a witnessed coq-sail build result. Do not weaken the
1.4 constraint or silently upgrade Coq to get a solution. See the preserved
[1.5 metadata](https://github.com/rocq-prover/opam/blob/564ab90f5874c0c91cee746c4706bc2ba686a5a9/released/packages/coq-bbv/coq-bbv.1.5/opam).

Use released opam metadata snapshot
`rocq-prover/opam@564ab90f5874c0c91cee746c4706bc2ba686a5a9` with `released/`
as the repository root. Archive checksums are upstream declarations inspected
here; no archive was fetched or independently hashed:

```text
bbv-v1.5.tar.gz SHA512
43bf2c300b5a24275fecd4888ddda0a2ef88ceb22835130bf5fe61d00ddfd7c8634b70e35a45043f69d2f3ef783ee3295e6e1cd6b8b4645ab008d6c1afa36c33
coq-record-update-v0.3.3.tar.gz SHA512
fb88f33ba716d068506d31047969fff40630adc7df7f21a016c8d92ff3c802007ce4efc0ae93c5456b76544040c323ae4d66755c8b425087504ddb1146a8b81a
```

### Toolchain constraints and a newly found Dune metadata gap

Keep Coq=8.19.0, Dune=3.9.1, OCaml
`ocaml-variants.4.14.0+options` with `ocaml-option-flambda`, record-update=0.3.3,
and isla-lang at `bda86c9f0bd28bbaa2481f50ddc986ede342805a`. The Coq metapackage
requires coq-core, coq-stdlib and coqide-server all at exactly 8.19.0; freeze
their sources and runtime binaries too. Dune 3.9.1 accepts OCaml>=4.08 on this
path. Islaris dune-project uses language 3.8/Coq extension 0.8. Lithium requires
Dune>=3.9.1, consistent with Islaris's exact pin. Isla-lang requires Ott>=0.33,
stronger than Islaris's Ott>=0.31; include the stronger bound in solving.

Important: the inspected modern main opam snapshot
`56aefa37456aa263913289a4174daca01c4b9339` did not yield the requested
`packages/dune/dune.3.9.1/opam` path through the read-only connector. This failed
lookup is not an exhaustive tree-absence proof; do not assume an ordinary
solve against only that snapshot can satisfy the exact Dune request. A bounded
history lookup recovered the immutable historical metadata snapshot
`ocaml/opam-repository@0d269faa45d7a07cdd53bb713f56d453cf648218`. It contains
the exact Dune 3.9.1 metadata and same-version companion packages. Its Dune
`x-commit-hash` matches the independently resolved upstream tag commit
`3276f90725e4423790a43065cc51ddbbba61eb89`.

For an overlay on the modern metadata, retain exactly the historical package
metadata for dune, dune-site, dune-private-libs, dyn, stdune and ordering at
3.9.1. All six use the same `dune-3.9.1.tbz` release artifact:

```text
SHA256 f0c3ce49f36c733b8aee72611f107cf06de6bc423be7262aab1bb3f03c05a878
source commit 3276f90725e4423790a43065cc51ddbbba61eb89
```

Old libsail requires dune-site>=3.0.2. Dune-site3.9.1 pulls
dune-private-libs=3.9.1, which pulls dyn/stdune=3.9.1, and these pull
ordering=3.9.1, csexp>=1.5.0 and pp>=1.1.0. Explicitly select the six-package
3.9.1 family; its metadata permits some mixing, but matching the release is a
deliberate reproducibility choice. No arbitrary modern dune-site should be
selected solely because its lower bound permits it.

The old Sail opam is multi-package: its 0.17 meta-package requests same-version
libsail, sail_manifest and its OCaml/C/SMT/SV/Lem/Coq/LaTeX/doc/output backends.
Materialize every corresponding root `.opam` from that exact source tree in
the local input repository. Do not pin only `sail.0.17` and let the solver fetch
the remaining same-version package names from unrelated metadata/source.
libsail also needs Menhir>=20180523, Ott>=0.28, Lem>=2018-12-14, Linksem>=0.3,
GMP, zlib, Yojson>=1.6.0 and Pprint>=20220103; dev mode adds bisect_ppx>=2.5.0.
The stronger Islaris/isla-lang bounds still apply. Islaris adds cmdliner>=1.1.0,
integers and frontend dependencies. Pin package sources/versions for all of
these from the eventual solver output rather than inventing their compatibility.

Coq-sail-riscv's opam build runs BOTH RV64 and RV32 generation/build targets.
That is a material cost/effect of installing the package, even though the
selected theorem is RV64. Z3 is required for this old Sail generation according
to the upstream bridge README, but its exact compatible release is not fixed
by that source. Freeze and test a separately chosen solver; do not assume the
modern Sail runtime's Z3 or generated files belong to this old stack. GNU GMP,
zlib, make, C toolchain, Python/OCamlbuild/findlib as actually requested, opam
and solver binaries remain runtime identity obligations.

### Offline solver-input plan, not an executed solution

The parent can now construct one reviewed local metadata universe from:

1. Main opam snapshot 56aefa…; the six exact historical Dune 3.9.1 package
   overlays from 0d269f…; Coq released snapshot 564ab9… rooted at released/;
   Iris opam snapshot 3c2151…. Retain full Git/source tree identities, exact
   repository priority and the final materialized metadata hashes.
2. Source-pin overlays for Islaris, isla-lang, old Sail and every Sail 0.17
   sibling, coq-sail and coq-sail-riscv at the commits above. Preserve the dated
   Lithium/Iris/stdpp package VERSION identifiers; copying a source opam whose
   `version` field says `dev` into a local pin without explicitly preserving
   the selected package version can change the constraint interpretation.
3. Exact root requests: Coq 8.19.0; OCaml 4.14.0+options plus flambda; the six
   Dune 3.9.1 packages; the five dated Lithium/Iris/stdpp-family requests;
   record-update 0.3.3; bbv 1.5; isla-lang selected dev source; Sail/coq-sail 0.17;
   coq-sail-riscv 0.5; local Islaris. Disable docs/tests for initial dependency
   realization, explicitly recording dev/pinned/build filter variables.

In a NEW parent-owned opam root/switch, disconnect network and configure only
those local frozen repositories. A proposed first invocation is
`opam install --dry-run --show-actions --json=solve.json <exact requests>`;
retain opam version/config, complete CUDF/solver request/universe when the
chosen opam exposes them, solver identity, and solution/action order. This
must perform no install; inspect the actual dry-run behavior before using it.
Never run `opam update`, a moving-repository add, `make builddep`, `make saildep`
or upstream scripts that fetch their own dependencies. A network-disabled
unsatisfiable solve is a useful result, not authorization to unpin anything.

The [machine-readable root requests](support/root-requests.json) enumerate the
proposed exact package selections, including all Sail 0.17 siblings; the flambda
option package version and remaining inputs are explicitly unresolved.

The next gate is every transitive version, URL/checksum/Git commit, extra-source,
patch and system-depext selection, followed by byte-verified source acquisition
by the parent and a final offline solution. Local Git pins need complete source
tree verification at their immutable commits; a package's metadata-file hash
does not hash its source tree. No complete solution, full source-tree/archive acquisition or runtime realization was attempted.
These are logical-core selections and proposed solver inputs; installation
readiness remains unknown.

### Smallest relevant actual upstream proof replay

For arithmetic and trace/source origin, select
`isla.sail_riscv.riscv64_test.sim_instr_a4`: its statement relates actual Sail
step execution for opcode `0x00150513` (addi a0,a0,1) to the checked-in `a4`
trace, and its proof uses the genuine `execute_ITYPE`/word-add bridge. It is
a relevant one-instruction pilot, not a two-input ADD/carry ABI theorem.
Compile the original entire upstream file rather than manufacturing a toy
semantics or deleting imports to extract the lemma. Also retain
`sim_instr_a0/a8/ac/a10` and the enclosing `riscv_test_safe` theorem as planned
coverage; the file's memory/branch bridge obligations still incur their costs.

A cheaper first environment smoke replay is the unchanged
`examples/riscv64_test.v`, with `riscv_test` and `riscv_test_adequate` over its
five checked-in instruction traces. This does not require fresh Isla execution
or prove those traces originate in Sail. The latter boundary is exactly why
the selected `sim_instr_a4` and full Sail-linked file remain the next gate.

After verifying and allocating the exact installation environment, use explicit Dune targets at -j1 for
`examples/riscv64_test.vo` and then `sail-riscv/riscv64_test.vo` in a fresh
checkout. The Sail bridge is disabled by default: its checked-in `_dune` stanza
must be enabled as the normal `dune` entry in that new subject, with no semantic
edits; record that local filesystem change. The stanza requires theories
`isla`, `isla.instructions`, `isla.riscv64`, `isla.examples`, `Sail`, `RV64`,
`Riscv_common`, `bbv`. `theories/dune` obtains `isla_lang.v` from the installed
isla-lang share directory via `opam var`, so pin that installed file too.

Run recursive `coqchk` and `Print Assumptions` on the fully qualified selected
constants after ordinary `.vo` replay, without quick checking/admit/norec.
Retain exact theorem types and imported-axiom closure. Compilation alone is not
replay evidence for every requested constant. A later comparable two-input
ADD/memory port must preserve original domain, register resources and trace
coverage; this ADDI trace bridge cannot silently replace the wider E31 claim.
Fresh trace production additionally needs the already selected Isla/snapshot
commits, Rust/Cargo/Z3 locks, byte/assembler identities and feasible-path audit;
it is outside this source-only pass. Stop and diagnose first failures before
any changed rerun. No allocation increase or runtime reuse is implied.


## Boundaries

- **Established from source:** the dated logical-package chain, equal-version
  constraints on the stdpp companions, old Sail 0.17 package relationships,
  bbv 1.4's Coq 8.19 exclusion, bbv 1.5's permitted range, historical Dune metadata
  and the selected upstream proof statements/build stanzas.
- **Unknown:** a satisfiable complete offline solution, all transitive package
  versions/checksums and system-library selections, a compatible exact old-Sail
  Z3 version, complete runtime closure, installation costs and build success.
- **Not examined by execution:** dependency solving, source-archive acquisition,
  installation, model/trace generation, compilation, theorem replay, Coq kernel
  checking and actual imported-axiom closures. No frontier is completed here.
- **Known not to apply:** a dated package pin alone is not a full lock;
  metadata compatibility is not proof replay; finite trace adequacy alone does
  not establish Sail trace origin; the ADDI bridge is not a two-input ADD/carry,
  ABI-return, Rust-resource or modern Sail/Lean theorem.

## Evidence

New primary metadata was inspected on 2026-10-15. The [31-record primary file
collection](support/ISLARIS-primary-files.json) preserves all returned source
text and records failed-path responses as unavailable rather than empty source.
The [primary manifest](support/ISLARIS-source-manifest.json) records immutable
repository revisions, paths, reported/recomputed Git blobs, SHA256 and declared
archive checksums. All retrieved metadata's recomputed blob hashes matched the
reported identities. Two records are unavailable lookups: the default-disabled
sail-riscv/dune path and the modern snapshot's Dune 3.9.1 metadata path. Their
replacement _dune/historical sources are retained as distinct successful reads.

The [supplemental source manifest](support/upstream-fragments-manifest.json)
records repository, full commit, path, upstream blob and retained-fragment hash
for seven earlier inspected files/fragments. It binds the exact evidence retained
here, independent of other local directories. The complete small files are the
[old dependency recipe](support/upstream/islaris-deps-Makefile),
[Coq Sail opam](support/upstream/coq-sail.opam),
[RISC-V Coq opam](support/upstream/coq-sail-riscv.opam),
[bridge README](support/upstream/islaris-sail-riscv-README.md) and
[theory stanza](support/upstream/islaris-theories-dune).
The [Sail-linked proof fragment](support/upstream/islaris-sail-riscv-test-fragment.v)
retains sim_instr_a0/a4 and the riscv_test_safe statement at original lines
66–83/200–222. The [trace-proof fragment](support/upstream/islaris-trace-test-fragment.v)
retains riscv_test and riscv_test_adequate through its initial proof steps.
Fragments are labeled with original line coordinates and retain upstream
copyright/license headers; they are evidence rather than standalone compilable
proof files. Supplemental file identities were independently recomputed against
the saved immutable source index before copying. The proof/dependency sources
were originally gathered on 2026-10-15 or earlier during preparation; they were
materially re-inspected for this report on 2026-10-15.

The [source-selection receipt](support/source-selections.json) preserves narrow
read-only repository-resolution observations, including the bbv/Dune source
revisions and source opam/Coq-project pointers. It does not certify release
archive bytes. [Upstream attribution](support/upstream/README.md) identifies
licensing and the fragment policy. [Package file hashes](package-manifest.json)
bind every delivered file other than the manifest itself.

## Revalidation

For unchanged subjects, recompute preserved UTF-8 file Git-blob/SHA256 identities
and check the exact depends/version formulas in the primary metadata. Compare
Lithium→Iris→stdpp and each =version companion edge, bbv's Coq interval, and
historical Dune source hashes. These cheap checks revalidate the source argument
only. A newer package or metadata revision needs its own inspected formulas;
passing one old check does not establish compatibility with adjacent versions.

For the unsolved installation question, materialize the exact local repositories,
overlays, source pins and root requests described above, then run the proposed
network-disabled dry solve in a separately authorized fresh environment. Preserve
the full resulting package/source/system solution before installation. Record an
unsatisfiable outcome without unpinning; investigate the particular constraint.
Actual theorem evidence then requires replay of the unchanged selected files,
recursive coqchk and per-theorem Print Assumptions under the realized closure.
Stop on an unexpected invariant or first ordinary failure before a changed run.
No solver/build/proof outcome can be inferred from this package's validation.

*Authored by an AI agent acting on joshlf's behalf.*
