# Islaris Source Identity, Offline opam Dependency Solving, Local Git Transport, and Coq Kernel Adequacy Replay

## Summary

This report synthesizes five primary-source and execution investigations covering the dependency resolution, source-identity verification, offline Git transport recovery, and Coq kernel adequacy replay of Islaris and the *Program Logics à la Carte* modular-effects framework:

1. **Logical Dependency Pins and Offline Solve Gate (`rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9`):** Pinned Islaris and Lithium metadata determine an exact Iris revision (`dev.2024-09-10.1.6f24ed4b`, commit `6f24ed4baa4d61967a95bac834eab2c66f3b76fa`) and one matching `coq-stdpp` / `coq-stdpp-bitvector` / `coq-stdpp-unstable` family (`dev.2024-09-10.3.a1a12e00`, commit `a1a12e00fba07f2e41ccd74a8b593b88e48fc2c3`). Coq `8.19.0` excludes released `coq-bbv 1.4` (`Coq < 8.19~`), while released `coq-bbv 1.5` (`mit-plv/bbv@c53d5b95c70839ae8e947010d85503bd1ada1120`) permits `Coq >= 8.16, < 9.2~`. Historical opam repository metadata (`ocaml/opam-repository@0d269faa45d7a07cdd53bb713f56d453cf648218`) supplies the requested six-package Dune `3.9.1` family (`dune`, `dune-site`, `dune-private-libs`, `dyn`, `stdune`, `ordering` at `ocaml/dune@3276f90725e4423790a43065cc51ddbbba61eb89`) absent from the modern snapshot lookup (`56aefa37456aa263913289a4174daca01c4b9339`), alongside the 12-package old Sail `0.17` sibling family (`rems-project/sail@b14f649845db850b3673696e2aa90565fa2a60ef`), `coq-sail 0.17` (`169934e27ceafe393ed4d365985f7b12d974d56e`), and `coq-sail-riscv 0.5` (`837ede9b39fae2aa97849da89c4b3b5a93344890`).
2. **Offline opam Dependency Solution and CUDF Satisfaction Audit:** Against the constructed 19,399-file main metadata universe (`56aefa37...`) and 29-package overlay, `opam 2.1.6` (`263921263e1f745613e2882745114b7b08f3608b`, SHA256 `8f42016825a9b10fd21802a18c22d37060c95e8c5a1d2be3df5135402c6a494d`) with networking disabled (`--dry-run --show-actions --no-depexts --skip-updates`) produced a witnessed **74-package solution including all 35 exact requested roots** (exit `0` in `9.078333` seconds). An independent host CUDF checker (`support/audit_cudf.py`) verified all 74 selected packages plus the synthetic `%3dopam-invariant` record against the 18,951-record exported CUDF universe (`240` dependency clauses, `104` conflict atoms, `35` request atoms) and rejected a negative control removing dated `coq-iris`.
3. **Acquired-Source Identity and Build Prerequisites Audit:** The exact 74-package selection was acquired by `opam 2.1.6` with `install --download-only` (exit `0` in `107.592145` seconds, empty stderr, zero installed packages or pins afterward). An offline container audit bound all 43 deduplicated source artifacts (29 HTTP archives and 6 HTTP extra files totaling `62,541,749` bytes with all 63 declared checksum comparisons, plus 8 fixed Git commits across `4,998` per-repository object comparisons and `4,935` globally unique Git objects) to their 62 materialized main-source directories (41 archive copies with `67,569` member comparisons and 21 Git copies). Before/after filesystem inventories (`154,231` entries, `115,763` regular-file hashes) remained byte-identical. Source inspection of old Sail (`INSTALL.md`, `src/lib/constraint.ml`) and old `sail-riscv` (`Makefile`) exposed concrete build gates: external `z3`, `pkg-config`, `libgmp-dev`, and `zlib1g-dev` prerequisites, coupled RV64 + RV32 generation (`Makefile:405-413`), and `-dcoq_undef_axioms` (`Makefile:383-388`).
4. **Offline Git Retrieval After a Partial Install and Collection-Limit Boundary:** A verified Git object cache alone proved insufficient for an offline `opam install`: because `OpamRepository.pull_tree`, `OpamVCS.pull_url`, and `OpamGit.fetch` still contact original remotes for unpinned checksumless Git URLs before checking freshness, the first offline install completed **53 of 74 package actions** (including Coq `8.19.0`, Dune `3.9.1`, Menhir `20260209`, Lem `2026-05-01`, Yojson `3.0.0`, and `bisect_ppx 2.8.3`) and exited with code `40` on the 21 Git-backed consumers (`760.237923` seconds). Routing the 8 fixed Git base URLs via read-only `insteadOf` mappings to an audited local bare provider (`/solve/offline-git-origin`) allowed the subsequent offline `--download-only` run to succeed (exit `0` in `9.661343` seconds, all 21 pending source consumers retrieved with `no changes`, and all `55,642` source-file hash comparisons and postchecks passing), before the enclosing host controller exited `1` (`80.135147` seconds) when redundant DOT/CUDF graph copies (`274,060,624` bytes) exceeded its monitored `256 MiB` host-artifact threshold.
5. **Actual Coq Kernel Replay of Modular Effects, HeapLang, and Islaris Adequacy (*Program Logics à la Carte* v2, Zenodo `14180355`):** A fresh build of the 51-file `iris-itree` subtree from `the_artifact.zip` (SHA256 `bf5d86d5fef425b6031640391dddda4f60b3b029d680019ddaedefd17e4d3378`) under Coq `8.19.2` and OCaml `4.14.4` compiled 38 original `.vo` modules and 3 observation-only audit modules (`AuditCore.v`, `AuditHeapLang.v`, `AuditIslaris.v`), followed by a recursive native `coqchk -o -m` check of **542 loaded libraries** (exit `0` in `60.373` seconds, no `-admit` or `-norec` bypass). Across 25 audited result constants, 6 are closed under the global context (including `exec.handler_adequate_from_simple`, `exec.sumEH_adequate`, `exec.sumSEH_adequate`, `state.stateEH_adequate`, `threadpool.exec.threadpoolEH_adequate`, and `isla.adequacy.isla_adequacy`), 3 depend on strong ITree bisimulation equality (`B = ITree.Eq.EqAxiom.bisimulation_is_eq`), 12 depend on `U = iris.itree.axioms.Ax.eq_rect_eq` and `B` (including `isla.adequacy_itree.isla_exec_adequate` and `isla.adequacy_itree.isla_adequacy`), and 4 operational HeapLang bridge theorems additionally depend on functional choice (`C = iris.itree.axioms.AxChoice`).

---

## Applicability

This coalesced report applies to reproducible opam/Coq/Sail proof environments, Islaris trace verification, and modular ITree/Iris adequacy bridges across five coupled investigation scopes:

1. **Islaris Logical Dependency Selection (`islaris-logical-dependency-pins-and-offline-solve-gate-2026`):**
   - Applies to `rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9` paired with `coq-lithium` (`dev.2024-09-11.0.7945a29d`, `UIC-verif-group/refinedC@7945a29d1647970709a9b5ad2ffc53c757e130cc`), `coq-iris` (`dev.2024-09-10.1.6f24ed4b`, `rocq-iris/iris@6f24ed4baa4d61967a95bac834eab2c66f3b76fa`), `coq-stdpp` / `coq-stdpp-bitvector` / `coq-stdpp-unstable` (`dev.2024-09-10.3.a1a12e00`, `rocq-iris/stdpp@a1a12e00fba07f2e41ccd74a8b593b88e48fc2c3`), Coq `8.19.0`, Dune `3.9.1` (`ocaml/dune@3276f90725e4423790a43065cc51ddbbba61eb89`), `coq-record-update 0.3.3`, proposed `coq-bbv 1.5` (`mit-plv/bbv@c53d5b95c70839ae8e947010d85503bd1ada1120`), `isla-lang` (`rems-project/isla-lang@bda86c9f0bd28bbaa2481f50ddc986ede342805a`), old Sail `0.17` (`rems-project/sail@b14f649845db850b3673696e2aa90565fa2a60ef`), `coq-sail 0.17` (`rems-project/coq-sail@169934e27ceafe393ed4d365985f7b12d974d56e`), and `coq-sail-riscv 0.5` (`riscv/sail-riscv@837ede9b39fae2aa97849da89c4b3b5a93344890`).
   - Metadata repositories: main OCaml opam repository `ocaml/opam-repository@56aefa37456aa263913289a4174daca01c4b9339`, historical Dune metadata `ocaml/opam-repository@0d269faa45d7a07cdd53bb713f56d453cf648218`, Coq released opam repository `rocq-prover/opam@564ab90f5874c0c91cee746c4706bc2ba686a5a9` (`released/`), and Iris opam mirror `rocq-iris/opam@3c21518b509d33676776c36e160de1d76835b801`.
2. **Offline opam Dry-Solve and CUDF Audit (`islaris-offline-dependency-solution-and-cudf-audit-2026`):**
   - Applies to the concrete combination of the 19,399-file main metadata snapshot, the 29-package overlay, 35 exact root requests, platform/filter configuration (`support/runtime-spec-fixed.json`, `support/globals-fixed.stdout`), and `opam 2.1.6 (263921263e1f745613e2882745114b7b08f3608b)` (SHA256 `8f42016825a9b10fd21802a18c22d37060c95e8c5a1d2be3df5135402c6a494d`, inspected source `ocaml/opam@dfbe6a0b3a386376780bf68d35e4ce107072079d`) running in container image `ocaml/opam@sha256:fc198c017f2474a20afe68636b3b790f7247c7593c7d252bb161673b11e5b9a2` (Linux arm64, Debian 12, 1 CPU, 1 GiB RAM, 128 PIDs, network mode `none`, no host bind mounts, UID/GID 1000).
   - Preserved at immutable reference commit [`4d12e39fc14312b39debf4dde5c491f6accd93e0`](https://github.com/google/zerocopy/blob/4d12e39fc14312b39debf4dde5c491f6accd93e0/reports/islaris-offline-dependency-solution-and-cudf-audit-2026/REPORT.md).
3. **Acquired-Source Identity and Build Prerequisites (`islaris-acquired-source-identity-and-build-prerequisites-2026`):**
   - Applies to the 43 deduplicated source artifacts (`support/plan/ARTIFACTS.json`) acquired for the 74-package selection by `opam 2.1.6` (`install --download-only`) and frozen in downloaded-source audit image `sha256:1189d6a4a06d068d675121d121999a7a8d3afa35e6d922ee41a0679fc98876ce`. Modern Sail/Lean installations do not substitute for old Sail `0.17` (`b14f649845...`) or old `sail-riscv` (`837ede9b39...`).
4. **Offline Git Transport and Partial-Install Recovery (`islaris-offline-git-retrieval-and-partial-install-2026`):**
   - Applies to the partial switch state containing 53 installed packages, 14 installed roots, and zero pins (`support/context.json`) inside recovery runtime clone `47b9311b0cfb478fead61c0dea4c10f41cf6082c3567f3bc889225eb160eb397` (image `sha256:4a38115e6be661e04182a12c41f0e827477cf703b749a097f96344bbd56ef7b6`, network `none`, no mounts, UID/GID 1000, 1 CPU, 2 GiB RAM and memory+swap, 128 PIDs, `no-new-privileges`), using `opam 2.1.6` and `git 2.39.5` (SHA256 `54af380ba6ca1b36305358e99427a31ae4b0af5dc5cb6d0198c6f2f16e97651d`, documentation pinned to `git/git@cc7d11c16782041a6bb73e2fb56417b7d4c6d186`).
5. **Modular Effects, HeapLang, and Islaris Adequacy Coq Replay (`modular-effects-coq-kernel-replay-and-assumption-closure-2026`):**
   - Applies to [Zenodo artifact 14180355, v2](https://zenodo.org/records/14180355) (`support/the_artifact.zip`, `1,480,438` bytes, SHA256 `bf5d86d5fef425b6031640391dddda4f60b3b029d680019ddaedefd17e4d3378`, `476` regular source files totaling `5,420,269` bytes, including the 51-file `iris-itree` subtree and vendored `stdpp`/`iris` trees with manifest hashes `39a9f21debfea2d9a92f9198ed35338b7ad0dfa2c2267b1c623373ffda333335` and `1628dd123871e6d6aa6f2efa5be7433b1f4bf672faaa072e3d15a8a63a319a4e`), compiled and checked on Linux arm64 with Coq `8.19.2` (`coqc` SHA256 `73e0ac064f017c4c00e4f5a40c458c2bb4c3ef159b6a7e9680dd97272b7d38c6`, `coqchk` SHA256 `9c2be314b44dd7f8e874dad47e885c8861ba50b8e0a506500b025b5f051057fb`), OCaml `4.14.4`, ITree `5.1.2`, Paco `4.2.1`, `coq-elpi 2.2.3`, `coq-ext-lib 0.13.2`, `coq-record-update 0.3.6`, and Dune `3.17.2` (2 CPUs, 3 GiB RAM limit, `-j1`, `-native-compiler no`).

---

## Findings

### 1. Logical Dependency Pins and the Offline Solve Gate (`islaris-logical-dependency-pins-and-offline-solve-gate-2026`)

Basis: direct **source** inspection and upstream **documentation**, with **derived** compatibility conclusions from the stated version formulas. Satisfying a metadata formula does not establish that packages build together or that a selected theorem checks.

#### 1.1 Exact Logical Package Requests

| Package | Exact opam request | Immutable source commit |
|---|---|---|
| Islaris | local package at selected commit | `rems-project/islaris` `c978e10f50db5c40f0fdf113f5f76a779782c6f9` |
| `coq-lithium` | `dev.2024-09-11.0.7945a29d` | `iris/refinedc` `7945a29d1647970709a9b5ad2ffc53c757e130cc` |
| `coq-iris` | `dev.2024-09-10.1.6f24ed4b` | `iris/iris` `6f24ed4baa4d61967a95bac834eab2c66f3b76fa` |
| `coq-stdpp` | `dev.2024-09-10.3.a1a12e00` | `iris/stdpp` `a1a12e00fba07f2e41ccd74a8b593b88e48fc2c3` |
| `coq-stdpp-bitvector` | `dev.2024-09-10.3.a1a12e00` | same `stdpp` commit |
| `coq-stdpp-unstable` | `dev.2024-09-10.3.a1a12e00` | same `stdpp` commit |
| `coq-record-update` | `0.3.3` | released `v0.3.3` archive, SHA512 below |
| `coq-bbv` | proposed `1.5` | `mit-plv/bbv` `c53d5b95c70839ae8e947010d85503bd1ada1120` (resolved `v1.5`) |

This chain is forced by inspected metadata rather than guessed from chronology: Islaris selects Lithium's dated version; Lithium selects the exact Iris version; Iris selects the exact dated `stdpp` version. `coq-stdpp-bitvector` depends on `coq-stdpp = version`; `coq-stdpp-unstable` depends on both `coq-stdpp = version` and `coq-stdpp-bitvector = version`. All three companions must be selected at the same dated version rather than `.dev` (which the package formulas permit as an escape that would abandon the selected compatibility chain).

Evidence is preserved in the [Lithium package metadata](https://github.com/rocq-iris/opam/blob/3c21518b509d33676776c36e160de1d76835b801/packages/coq-lithium/coq-lithium.dev.2024-09-11.0.7945a29d/opam), [Iris package metadata](https://github.com/rocq-iris/opam/blob/3c21518b509d33676776c36e160de1d76835b801/packages/coq-iris/coq-iris.dev.2024-09-10.1.6f24ed4b/opam), and the three matching `stdpp` metadata files in [preserved primary metadata](support/ISLARIS-primary-files.json). Direct pinned source opams for Iris and `stdpp` confirm the dependency formulas. The exact Lithium source opam was readable through the `UIC-verif-group/refinedC` mirror at the same full commit; the opam package URL remains the original MPI GitLab repository. When read-only GitLab web access failed during initial metadata discovery, the `rocq-iris/opam` GitHub mirror of the official Iris opam repository was resolved once to `3c21518b509d33676776c36e160de1d76835b801` and used for all subsequent metadata reads.

#### 1.2 `coq-bbv` and the Old Sail `0.17` Stack

Pinned `coq-sail 0.17` requires `coq >= 8.14` and `coq-bbv >= 1.3`, and conflicts with any Sail package whose version differs from `0.17`. The selected old Sail commit's own opam confirms version `0.17`. Its generator must remain `b14f649845db850b3673696e2aa90565fa2a60ef`; `coq-sail` remains `169934e27ceafe393ed4d365985f7b12d974d56e`; `coq-sail-riscv` remains `837ede9b39fae2aa97849da89c4b3b5a93344890` (package version `0.5`). The obsolete separate `deps/Makefile` Sail target at `605cd...` is not selected.

Released `coq-bbv 1.4` metadata requires `Coq < 8.19~` and therefore excludes requested Coq `8.19.0`. Released [coq-bbv 1.5 metadata](https://github.com/rocq-prover/opam/blob/564ab90f5874c0c91cee746c4706bc2ba686a5a9/released/packages/coq-bbv/coq-bbv.1.5/opam) in `rocq-prover/opam@564ab90f5874c0c91cee746c4706bc2ba686a5a9` (`released/` root) explicitly permits `Coq >= 8.16, < 9.2~` and supplies an immutable content hash:

```text
bbv-v1.5.tar.gz SHA512
43bf2c300b5a24275fecd4888ddda0a2ef88ceb22835130bf5fe61d00ddfd7c8634b70e35a45043f69d2f3ef783ee3295e6e1cd6b8b4645ab008d6c1afa36c33
coq-record-update-v0.3.3.tar.gz SHA512
fb88f33ba716d068506d31047969fff40630adc7df7f21a016c8d92ff3c802007ce4efc0ae93c5456b76544040c323ae4d66755c8b425087504ddb1146a8b81a
```

#### 1.3 Toolchain Constraints and the Historical Dune `3.9.1` Metadata Overlay

The logical request keeps `coq = 8.19.0` (which pulls `coq-core`, `coq-stdlib`, and `coqide-server` at `8.19.0`), `dune = 3.9.1`, OCaml `ocaml-variants.4.14.0+options` with `ocaml-option-flambda`, `coq-record-update = 0.3.3`, and `isla-lang` at `bda86c9f0bd28bbaa2481f50ddc986ede342805a`. Islaris `dune-project` uses language `3.8` / Coq extension `0.8`; Lithium requires `dune >= 3.9.1`, consistent with Islaris's exact pin. `isla-lang` requires `ott >= 0.33`, stronger than Islaris's `ott >= 0.31`.

Because the modern main opam snapshot `56aefa37456aa263913289a4174daca01c4b9339` did not yield `packages/dune/dune.3.9.1/opam`, a bounded history lookup recovered the immutable historical snapshot `ocaml/opam-repository@0d269faa45d7a07cdd53bb713f56d453cf648218`, which contains the exact six-package Dune `3.9.1` family (`dune`, `dune-site`, `dune-private-libs`, `dyn`, `stdune`, and `ordering` at `3.9.1`), all sharing the `dune-3.9.1.tbz` release artifact:

```text
SHA256 f0c3ce49f36c733b8aee72611f107cf06de6bc423be7262aab1bb3f03c05a878
source commit 3276f90725e4423790a43065cc51ddbbba61eb89
```

Old `libsail` requires `dune-site >= 3.0.2`. `dune-site.3.9.1` pulls `dune-private-libs = 3.9.1`, which pulls `dyn = 3.9.1` and `stdune = 3.9.1`, which pull `ordering = 3.9.1`, `csexp >= 1.5.0`, and `pp >= 1.1.0`. Furthermore, the old Sail `0.17` repository is multi-package: its `sail.0.17` meta-package requests same-version `libsail`, `sail_manifest`, and its 9 backend packages (`sail_c_backend`, `sail_coq_backend`, `sail_doc_backend`, `sail_jib_backend`, `sail_latex_backend`, `sail_lem_backend`, `sail_ocaml_backend`, `sail_output`, `sail_smt_backend`, `sail_sv_backend`), so all 12 root `.opam` files from `rems-project/sail@b14f649845db850b3673696e2aa90565fa2a60ef` must be materialized in the overlay ([machine-readable root requests](support/root-requests.json)). `libsail` also requires `menhir >= 20180523`, `ott >= 0.28`, `lem >= 2018-12-14`, `linksem >= 0.3`, GMP, zlib, `yojson >= 1.6.0`, `pprint >= 20220103`, and in `dev` mode `bisect_ppx >= 2.5.0`; Islaris adds `cmdliner >= 1.1.0`, `integers`, and frontend dependencies.

#### 1.4 Smallest Relevant Upstream Islaris Proof Replay Targets

For arithmetic and Sail trace-origin verification, the smallest relevant upstream target is `isla.sail_riscv.riscv64_test.sim_instr_a4` in `sail-riscv/riscv64_test.v` ([Sail-linked proof fragment](support/upstream/islaris-sail-riscv-test-fragment.v), original lines 66–83 and 200–222): its statement relates actual Sail step execution for RV64I opcode `0x00150513` (`addi a0, a0, 1`) to the checked-in `a4` trace via `execute_ITYPE` and the word-add bridge, alongside companion instructions `sim_instr_a0`, `sim_instr_a8`, `sim_instr_ac`, `sim_instr_a10`, and the enclosing `riscv_test_safe` theorem. A cheaper trace-only environment smoke target is `examples/riscv64_test.v` (`riscv_test` and `riscv_test_adequate`, [trace-proof fragment](support/upstream/islaris-trace-test-fragment.v)), which verifies trace adequacy over five checked-in instruction traces without proving Sail trace origin. Note that `sail-riscv/_dune` is disabled by default and must be enabled as `sail-riscv/dune` (requiring theories `isla`, `isla.instructions`, `isla.riscv64`, `isla.examples`, `Sail`, `RV64`, `Riscv_common`, `bbv`), while `theories/dune` ([theory stanza](support/upstream/islaris-theories-dune)) copies `isla_lang.v` from the installed `isla-lang` share directory via `opam var`. This one-instruction `addi` pilot is distinct from a two-input arithmetic/carry and memory bridge.

---

### 2. Offline opam Dependency Solution and CUDF Satisfaction Audit (`islaris-offline-dependency-solution-and-cudf-audit-2026`)

Basis: **source** metadata and opam semantics; parent-owned **execution** with preserved native receipts; separate host-side **derived** hash/identity and CUDF satisfaction checks.

#### 2.1 Complete 74-Package Offline Dry-Run Solution Retaining All 35 Exact Roots

Using verb-first `opam install` in a fresh empty switch with repository priority `overlay` then `main`, the internal solver (`builtin-mccs+glpk`), `--dry-run --show-actions --no-depexts --skip-updates`, and all 35 exact request atoms, `opam 2.1.6` returned exit `0` in `9.078333` seconds with networking disabled, proposing **74 packages to install** ([executed argv/status](support/dry-solve.json), [actions](support/dry-solve.stdout), [raw opam JSON](support/native-dry-solve.json), [repository order](support/v3-repositories.stdout), [post packages](support/post-installed.stdout), [post pins](support/post-pins.stdout)). Real installed-package and pin sets remained empty before and after.

All 35 roots are retained at their exact requested versions (`support/root-requests.json`):
- `ocaml-variants.4.14.0+options` with `ocaml-option-flambda.1`;
- `coq.8.19.0`, `coq-core.8.19.0`, `coq-stdlib.8.19.0`, `coqide-server.8.19.0`;
- all six Dune-family packages at `3.9.1` (`dune`, `dune-site`, `dune-private-libs`, `dyn`, `stdune`, `ordering`);
- `coq-lithium.dev.2024-09-11.0.7945a29d`, `coq-iris.dev.2024-09-10.1.6f24ed4b`, `coq-stdpp.dev.2024-09-10.3.a1a12e00`, `coq-stdpp-bitvector.dev.2024-09-10.3.a1a12e00`, `coq-stdpp-unstable.dev.2024-09-10.3.a1a12e00`;
- `coq-record-update.0.3.3` and `coq-bbv.1.5`;
- `islaris.dev`, `isla-lang.dev`, `coq-sail.0.17`, `coq-sail-riscv.0.5`, and all **12 Sail `0.17` siblings**.

Every selected package is traced in [74-package origins and declared sources](support/selected-package-origins.json): 29 come from the higher-priority overlay and 45 from the main snapshot (`support/overlay-and-primary-inputs.tar.gz`, `support/main-metadata.tar.gz`). Of the 74 selected records, 65 have `url`/`extra-source` sections and 9 are virtual/metapackage records without sources. Note that the solver selects modern transitive packages from the main snapshot alongside old Sail `0.17`, including `menhir.20260209`, `lem.2026-05-01`, and `yojson.3.0.0`.

#### 2.2 opam 2.1.6 Version Normalization and Filter Semantics

Inspecting `ocaml/opam@dfbe6a0b3a386376780bf68d35e4ce107072079d` explains two key solver behaviors:
- `src/format/opamFile.ml:3098-3123` derives package identity from the repository directory path and replaces mismatched explicit `name`/`version` fields after warning; thus dated Iris/`stdpp` repository entries retain upstream `version: "dev"` text in source while their actual selected identities and `version` dependency variables are the dated strings.
- `src/state/opamPackageVar.ml:121-130` classifies checksum-free fixed-commit Git URLs as development packages (`dev = true`), even when the package version is numeric (`0.17`). Consequently, **`libsail`'s `{dev}`-filtered dependency on `bisect_ppx` is active**, and `bisect_ppx.2.8.3` is selected. Conversely, `pinned = false` because the switch pin list is empty, and `pin-depends` is inert for repository packages (`Manual.md:1114-1128`), which is why `isla-lang` had to be materialized explicitly in the repository overlay.

#### 2.3 Independent CUDF Satisfaction Audit and Rejecting Control

The host checker ([`support/audit_cudf.py`](support/audit_cudf.py)) parses the raw selected 74-package JSON (handling the identical duplicated `command-line` key via a duplicate-aware JSON parser) and the 18,951-record exported CUDF universe (`native-islaris-1.cudf`, SHA256 `0e3995239ad41487f8c32722352370d89471bc5ed42fe00996f2002e17f9a5c4`). After accounting for CUDF's single synthetic switch invariant record (`package: %3dopam-invariant`, `version: 1`, `installed: true`, `keep: version`, `opam-name: SWITCH_INVARIANT`, diagnosed in [`support/audit-attempt-1-diagnosis.json`](support/audit-attempt-1-diagnosis.json)), the checker verifies unique package/version identities, all **240 dependency clauses**, **104 conflict atoms**, and **35 request atoms** ([`support/cudf-audit.json`](support/cudf-audit.json)). A negative control removing dated `coq-iris` from the proposed solution is rejected on `coq-lithium`'s exported `coq-iris = 2 | coq-iris = 1` dependency clause ([`support/cudf-false-solution-control.json`](support/cudf-false-solution-control.json)).

#### 2.4 Operational Setup Diagnostics

Initial CLI flag ordering (`opam` 2.1.6 rejected `init`-specific options placed before the verb with exit `2`), a bind-mount `Operation not permitted` error, a census argv NUL-byte typo, and an unhandled `Cannot remove` cleanup failure when `opam init` tried to remove read-only `0555`/`0444` consumer-copied repository cache directories (`4,028,311`-byte stderr, [`support/fatal-cleanup-disposition.md`](support/fatal-cleanup-disposition.md)) were diagnosed and resolved via root-owned `0755`/`0644` input copies with consumer-writable cache directories ([`support/ownership-oracle-results.json`](support/ownership-oracle-results.json), [`support/earlier-operational-evidence.tar.gz`](support/earlier-operational-evidence.tar.gz), [`support/native-evidence.tar.gz`](support/native-evidence.tar.gz)), while all **19,429 input file hashes** (19,399 main + 30 overlay) remained unchanged.

---

### 3. Acquired-Source Identity Audit and Build Prerequisites (`islaris-acquired-source-identity-and-build-prerequisites-2026`)

Basis: **execution** + **source** inspection + independent artifact/code **audit**.

#### 3.1 Download-Only Acquisition Preserved the 74-Package Selection Without Installation

Running `opam install --root=/solve/opam --use-internal-solver --no-self-upgrade --switch=islaris-dry --download-only --no-depexts --skip-updates --yes --jobs=1` with `OPAMWITHTEST=false OPAMWITHDOC=false` and the 35 ordered roots exited `0` in `107.592145` seconds with empty stderr ([phase receipt](support/acquisition/download-phase.json), [stdout](support/acquisition/download.stdout), [empty stderr](support/acquisition/download.stderr), [raw native JSON](support/acquisition/native-acquire-result.json), [selection gate](support/acquisition/source-selection-gate.json)). Post-acquisition [installed](support/acquisition/post-installed.stdout) and [pin](support/acquisition/post-pins.stdout) observations were empty. All original GitLab and INRIA URLs succeeded without replacement URIs.

#### 3.2 Complete Reconciliation of 74 Records, 43 Artifacts, and 62 Materialized Source Copies

Of the 74 selected package records, 65 carry `source` or `extra-source` sections and 9 do not. Their 68 role/consumer associations deduplicate to **43 source artifacts** ([`support/plan/ARTIFACTS.json`](support/plan/ARTIFACTS.json), [`support/audit-summary/consumer-coverage.json`](support/audit-summary/consumer-coverage.json)):
- **35 HTTP objects** (29 HTTP archives and 6 HTTP extra-source files), totaling `62,541,749` transport bytes ([`support/audit-summary/http-object-map.json`](support/audit-summary/http-object-map.json)). Every declared checksum (63 comparisons across SHA256, SHA512, and MD5) matched while streaming into the host parser. Across **41 materialized archive consumer directories**, all `67,569` member/source-copy comparisons matched on regular-file bytes, regular owner-execute bits, and symlink targets.
- **8 fixed Git repositories** (listed in `REPORT.json`), none shallow and none containing gitlinks, with `git fsck --full --strict` returning `0` and empty streams. Streaming `git cat-file --batch` with Git SHA1 framing and SHA256 verified all `4,998` per-repository object comparisons (`4,935` globally unique Git object IDs across commits, recursive trees, and blobs). Across **21 materialized Git consumer directories**, every copy matched its complete tracked file and directory set, regular bytes, executable/nonexecutable mode distinction, and symlink targets with **zero extra entries** after excluding `.git` and its descendants, and all 21 `.git/objects/info/alternates` files matched the exact newline-free local object-store path.

#### 3.3 Filesystem Stability and Independent Audit Review

In the offline audit container (1 CPU, 1 GiB RAM, 128 PIDs, network `none`, writes restricted to `/audit`), before/after NUL-framed filesystem inventories ([`support/audit-summary/unchanged-state.json`](support/audit-summary/unchanged-state.json)) verified that all `115,763` regular-file hashes and all `154,231` seven-field filesystem entries remained byte-identical, as did all `19,429` metadata/config files. Observed apparent sizes were `1,524,081,218` bytes for the opam root, `212,005,364` bytes for the download cache, and `1,286,338,476` bytes for source directories (allocated sizes `1,816,207,360`, `212,185,088`, and `1,578,213,376` bytes, respectively). The [independent review](support/independent/REVIEW.md) (`support/frozen-independent-review.tar.gz`) rehashed every audit file, reconstructed all 8 commit identities and all 354 recursive tree identities, repeated the 21 Git-copy and 41 archive-copy ledger comparisons, and verified negative controls (missing-object, altered-manifest, omitted-consumer, truncated-stream).

#### 3.4 Concrete Build and Proof Prerequisites Exposed by Acquired Sources

- **Old Sail `0.17` external Z3 and C library dependencies:** [`support/source/old-sail/INSTALL.md`](support/source/old-sail/INSTALL.md) (lines 21–27, 40–46) requires external `z3`, GMP development headers, `pkg-config`, and zlib development headers; [`support/source/old-sail/src/lib/constraint.ml`](support/source/old-sail/src/lib/constraint.ml) (lines 95–105, 128–131) invokes external `z3 -t:1000 -T:10` by default. Read-only system inventory ([`support/audit-summary/system-package-observations.json`](support/audit-summary/system-package-observations.json)) found GCC/G++ 12.2, `build-essential`, `make`, `binutils`, and `libc-dev`, but found **no installed `z3`, `pkg-config`/`pkgconf`, `libgmp-dev`, `zlib1g-dev`, or `m4`** in the base container.
- **Old `sail-riscv` undefined-operation axioms and dual RV64/RV32 build:** [`support/source/old-riscv/Makefile`](support/source/old-riscv/Makefile) passes `-dcoq_undef_axioms` during Coq generation (lines 383–388) and requires generated outputs for **both RV64 and RV32** (lines 405–413). Consequently, an RV64-only build cannot satisfy the package's declared install target, and any downstream theorem replay must explicitly audit generated undefined-operation axioms.

---

### 4. Offline Git Retrieval After a Partial Install and Collection-Limit Boundary (`islaris-offline-git-retrieval-and-partial-install-2026`)

Basis: **source** + **execution** + **derived** ledger reconciliation.

#### 4.1 Why a Verified Git Cache Alone Failed During Offline `opam install`

In the first offline install attempt (`760.237923` seconds native phase, `771.301710` seconds controller), `opam 2.1.6` completed **53 distinct package installations** (including Coq `8.19.0`, Dune `3.9.1`, Menhir `20260209`, Lem `2026-05-01`, Yojson `3.0.0`, and `bisect_ppx 2.8.3`) and exited with status `40` on **21 source-download failures** corresponding to all 21 consumers of the 8 fixed Git repositories (`support/partial-install-evidence.tar.gz`).

Inspecting `ocaml/opam@dfbe6a0b3a386376780bf68d35e4ce107072079d` ([`support/PRIMARY.json`](support/PRIMARY.json)) explains why:
- `src/repository/opamRepository.ml:98-109,240-281` (`OpamRepository.pull_tree`) cannot use the checksum-addressed file cache for checksumless Git URLs.
- `src/repository/opamVCS.ml:76-102` (`OpamVCS.pull_url`) executes `clean -> fetch -> revision/up-to-date check` even when the local repository cache already contains the target commit.
- `src/repository/opamGit.ml:64-117` (`OpamGit.fetch`) attempts to fetch from the remote URL before checking commit availability; under `network=none`, remote DNS/connection failure aborts retrieval.
- Neither `--skip-updates` (which only suppresses pre-updates of *pinned* packages) nor `--reuse-build-dir` eliminates `Fetch` action vertices (`src/client/opamAction.ml:240-275`).

#### 4.2 Local Read-Only Git Transport and Successful 21-Consumer Offline Retrieval

To provide an offline Git transport without mutating metadata URLs, pins, or `{dev}` filter semantics, a separate read-only copy of the audited bare Git cache was materialized at `/solve/offline-git-origin` and bound via eight base-URL `url.<local>.insteadOf` mappings (`git 2.39.5`, all protocols except `file` disabled, hooks/fsmonitor/untracked-cache/system-config disabled, [`support/transport-evidence.tar.gz`](support/transport-evidence.tar.gz), [`support/transport-review.json`](support/transport-review.json)). The Git-only transport gate exited `0` in `48.987434` seconds across 8 independent bare fetch probes (`4,935` globally distinct objects, `4,998` per-repository object comparisons).

In the subsequent recovery run ([`support/download-evidence.tar.gz`](support/download-evidence.tar.gz), [`support/DOWNLOAD-GATE.json`](support/DOWNLOAD-GATE.json), [`support/FILTER-CONTEXT.json`](support/FILTER-CONTEXT.json), [`support/GIT-BOOKKEEPING-DELTA.json`](support/GIT-BOOKKEEPING-DELTA.json), [`support/fan-in-results.json`](support/fan-in-results.json)):
- Preflight dry-solve exited `0` in `10.405360` seconds and actual `opam install --download-only` exited `0` in `9.661343` seconds, planning exactly the **21 pending installs** (`53 installed + 21 pending = 74 total`) while retaining all 35 roots.
- Because `opamSolution.ml:454-472` prunes non-`Fetch` vertices for `--download-only` and `opamSolution.ml:677-714` excludes `Fetch` vertices from JSON `results`, the JSON output validly reports `"results": []` while `opamAction.ml:240-296` emits the 21 per-package retrieval messages (each reporting `no changes`).
- All scheduled postchecks passed before host collection stopped: `53` installed packages / `14` installed roots / `0` pins, `19,429` metadata hashes, `21` full Git worktrees (`55,642` file-hash comparisons across two passes; only `.git/FETCH_HEAD` changed as expected), `4,935` provider object identities, and `11,962` installed-prefix file hashes.

#### 4.3 Host Artifact Collection Threshold Failure

After all 270 native phase receipts exited `0`, the enclosing host controller returned **`1` after `80.135147` seconds** when redundant solver-graph copying crossed its monitored `256 MiB` host-artifact threshold (**`274,060,624` bytes** retained, dominated by three identical `64,689,921`-byte `download.dot` copies and six identical `7,498,481`-byte CUDF copies). The container (`SizeRw = 447,180,800` bytes, no OOM flag) was cleanly stopped (`exit 0`) without retry.

---

### 5. Actual Coq Kernel Replay of Modular Effects, HeapLang, and Islaris Adequacy (`modular-effects-coq-kernel-replay-and-assumption-closure-2026`)

Basis: **source** + **execution** (`coqc` + `coqchk` + `Print Assumptions`).

#### 5.1 Fresh Proof Compilation and 542-Library Recursive `coqchk` Verification

Building the nine original seed targets from *Program Logics à la Carte* v2 (`support/the_artifact.zip`, Zenodo `14180355`):
- `src/exec.vo`, `src/heap.vo`, `src/threadpool/exec.vo`, `src/threadpool/interleaving.vo`, `src/examplelang/adequacy.vo`;
- `src/heaplang/adequacy.vo`, `src/heaplang/opsem_adequacy.vo`;
- `islaris/adequacy.vo`, `islaris/adequacy_itree.vo`

compiled 38 original `.vo` files and 3 observation-only audit files ([`support/AuditCore.v`](support/AuditCore.v), [`support/AuditHeapLang.v`](support/AuditHeapLang.v), [`support/AuditIslaris.v`](support/AuditIslaris.v)). Running native `coqchk -o -m` with **no `-admit` or `-norec` bypass** recursively checked all **542 loaded libraries** and exited `0` (`Modules were successfully checked`), reporting predicative `Set`, no type-in-type constants/inductives, no unsafe (co)fixpoints, and no assumed positivity ([`support/kernel-context.json`](support/kernel-context.json), [`support/logs/recursive-coqchk.json`](support/logs/recursive-coqchk.json)). While the global context across all 542 imported modules lists 62 axiom/primitive declarations (from Coq standard classical/numeric libraries and ITree), individual theorem dependencies are strictly narrower and audited per constant below.

| Phase | Exit | Elapsed seconds |
| --- | ---: | ---: |
| Core, state/heap, threadpool, and ExampleLang build | 0 | 68.383 |
| Core annotation audit (`AuditCore.v`) | 0 | 8.129 |
| HeapLang and operational bridge build | 0 | 44.292 |
| HeapLang annotation audit (`AuditHeapLang.v`) | 0 | 8.117 |
| Original and ITree Islaris build | 0 | 46.262 |
| Islaris annotation audit (`AuditIslaris.v`) | 0 | 4.095 |
| Recursive native checker (`coqchk -o -m`) | 0 | 60.373 |

The final task directory held `21,891,326` apparent bytes (`21,885,246` regular-file bytes across `264` files); `coqchk` reported `total heap size = 576280 kbytes`.

#### 5.2 Per-Constant Axiom Closure Across All 25 Audited Results

Let **B** denote `ITree.Eq.EqAxiom.bisimulation_is_eq` (identifying strongly bisimilar ITrees), **U** denote `iris.itree.axioms.Ax.eq_rect_eq` (UIP), and **C** denote `iris.itree.axioms.AxChoice` (functional choice). Full qualified names and `Print Assumptions` blocks are preserved in [`support/actual-assumptions.json`](support/actual-assumptions.json):

| Actual result constants | Reported assumptions |
| --- | --- |
| `exec.handler_adequate_from_simple`, `exec.sumEH_adequate`, `exec.sumSEH_adequate` | Closed under the global context |
| `state.stateEH_adequate`, `threadpool.exec.threadpoolEH_adequate` | Closed under the global context |
| `heap.wpi_load`, `heap.wpi_store`, `heap.wpi_allocN` | B |
| `exec.wpi_adequate`, `exec.wpi_adequate_pure` | U, B |
| `state.state_adequacy`, `heap.heap_adequacy` | U, B |
| `threadpool.interleaving.threadpool_adequacy`, `examplelang.adequacy.wp_adequacy_irel` | U, B |
| `heaplang.adequacy.wp_adequacy_irel`, `wp_adequacy_eval`, `wp_partial_soundness`, `wp_total_soundness` | U, B |
| `heaplang.opsem_adequacy.execution_from_opsem_trace`, `partially_adequate_opsem_adequate`, `wp_later_opsem_adequate`, `wp_total_opsem_adequate` | U, B, C |
| `isla.adequacy.isla_adequacy` | Closed under the global context |
| `isla.adequacy_itree.isla_exec_adequate`, `isla.adequacy_itree.isla_adequacy` | U, B |

#### 5.3 Handler Composition, State/Heap/Threadpool Relations, HeapLang Operational Direction, and Islaris Adequacy Premises

1. **Handler Composition (`src/exec.v`):** `handler_adequate_from_simple` (line 555) lifts `seHandlerAdequate H EH` to `eHandlerAdequate H EH`. `sumEH_adequate` (line 805) and `sumSEH_adequate` (line 882) compose component handler adequacy across sum handlers (`⊕`) while keeping component invariants separate; they do not automatically prove that coupled MiniRust byte/provenance and alias/race handlers maintain a shared state invariant. `wpi_adequate` (line 707) and `wpi_adequate_pure` (line 727) extract execution and pure propositions under explicit `exec EH t s C`, handler adequacy, invariant, and credit premises.
2. **State, Value-Heap, Threadpool, and ExampleLang Adequacy:** `state_adequacy` (`src/state.v:244`) and `heap_adequacy` (`src/heap.v:527`; note line 537 is a commented-out sketch) transport WP across `state_irel` / `heap_irel` under `Sequential H` over a value heap (not a byte/provenance allocator; `wpi_store` is at line 356, distinct from `wpi_store'` at line 332). `threadpool_adequacy` (`src/threadpool/interleaving.v:1556`) transports concurrent ITree WP across `threadpool_irel`, permitting `LastThreadKilled` with `True`. ExampleLang's `wp_adequacy_irel` (`src/examplelang/adequacy.v:27`) chains `threadpool -> UB -> state -> demonic` interpretation relations and rules out the UB branch (`False`).
3. **HeapLang Operational Bridge Direction (`src/heaplang/adequacy.v`, `src/heaplang/opsem_adequacy.v`):** `wp_partial_soundness` (`adequacy.v:147`, `Later` WP with step bound) and `wp_total_soundness` (`adequacy.v:167`, `Identity` WP without step bound) still include the relational last-thread-death outcome. `execution_from_opsem_trace` (`opsem_adequacy.v:1521`) constructs a related ITree execution from an operational `nsteps` derivation **plus** a `tp_termination` witness (using functional choice **C**), and `partially_adequate_opsem_adequate` (line 1558), `wp_later_opsem_adequate` (line 1584), and `wp_total_opsem_adequate` (line 1594) all conclude standard Iris operational `adequate NotStuck` (not operational termination).
4. **Islaris Original vs. ITree Adequacy (`islaris/adequacy.v:91`, `islaris/adequacy_itree.v:265,273`):** Original `isla.adequacy.isla_adequacy` (closed under the global context) quantifies over a list of thread register maps and proves finite-step `nsteps` not-stuckness and trace postcondition `Pκs κs` conditional on `Arch`, pre-ghost state, instruction table, backed-memory domain, trace specification, and memory/register resources. The ITree adaptation (`isla_exec_adequate` and `isla.adequacy_itree.isla_adequacy`, depending on `U, B`) starts from a single initial register map and requires `statePreG`. Neither theorem certifies that traces originated from Sail, that raw instruction bytes decode to those traces, or that a calling Rust function's ABI/aliasing contracts hold.

---

## Boundaries

1. **Boundary Between Offline Solver Satisfaction, Source Acquisition, Partial Installation, and Full Old-Sail/Islaris Build:**
   - The 74-package offline dry-run solution (`islaris-offline-dependency-solution-and-cudf-audit-2026`), the 43-artifact download-only source audit (`islaris-acquired-source-identity-and-build-prerequisites-2026`), and the 53-package partial install plus 21-package offline Git retrieval (`islaris-offline-git-retrieval-and-partial-install-2026`) do **not** complete installation of the remaining 21 Git-backed packages, execute old Sail `0.17` / `coq-sail-riscv 0.5` model generation, or replay upstream Islaris Sail-bridge proofs (`sail-riscv/riscv64_test.v`).
   - Selecting modern `menhir.20260209`, `lem.2026-05-01`, and `yojson.3.0.0` satisfies opam metadata formulas, but does not prove API build compatibility with old Sail `0.17`.
   - Old `coq-sail-riscv` builds both RV64 and RV32 targets (`Makefile:405-413`) and passes `-dcoq_undef_axioms` (`Makefile:383-388`), and old Sail requires an external `z3` binary, `pkg-config`, `libgmp-dev`, and `zlib1g-dev`.
2. **Archive Comparison and Public Evidence Projection Boundaries:**
   - For the 41 HTTP archive consumer directories (`islaris-acquired-source-identity-and-build-prerequisites-2026`), the audit verified regular-file bytes, regular owner-execute bits, and symlink targets (`67,569` comparisons); unlike the 21 Git consumer copies, it did **not** establish archive directory entries, full Unix permission bits (notwithstanding the overbroad shorthand in raw preserved [`support/raw-audit-results.md`](support/raw-audit-results.md)), ownership preservation, or hardlink inode topology.
   - The public audit projection ([`support/public-projection-source-audit.tar.gz`](support/public-projection-source-audit.tar.gz), [`support/public-projection.json`](support/public-projection.json)) retains 232 of the 238 original audit files, omitting the six raw external extra-source bodies (numbered external extra-source entries 1, 2, 3, 5, 6, and 7) under a single publication rule while preserving all hashes, URLs, and check records. Similarly, [`support/download-evidence.tar.gz`](support/download-evidence.tar.gz) ([`support/projection-ledger.json`](support/projection-ledger.json)) omits redundant DOT graph payloads and 5 duplicate CUDF copies while retaining one complete CUDF (`native-run/133-dry-cudf.stdout`, SHA256 `6596acc28911d3e82e83cbca070789cd30dd4af388218cdb04afe226e1a0f09f`).
3. **Coq Modular-Effects Replay Scope Boundaries (`modular-effects-coq-kernel-replay-and-assumption-closure-2026`):**
   - Six `.v` files in `the_artifact.zip` were outside the selected 9-seed compilation closure: `src/angelic_choice.v`, `src/interpreter.v`, `src/heaplang/interpreter.v`, `src/heaplang/tactics.v`, `src/heaplang/examples/join.v`, and `src/heaplang/examples/spinlock.v`.
   - The replayed theorems completed the modular-effects artifact replay milestone, but do not instantiate MiniRust's coupled byte/provenance/alias/race semantics, RustBelt/`lambdaTB` lifetime logic, concrete ISA byte decoding, or open-client ABI linking; the remaining Rust-logic and ISA artifact replays are separate work.

---

## Evidence

All primary manifests, deterministic archives, audit scripts, and Coq verification logs are staged in `support/` and bound by [`FILE-MANIFEST.json`](FILE-MANIFEST.json), [`package-manifest.json`](package-manifest.json), [`support/archive-index.json`](support/archive-index.json), and [`support/archive-members.json.gz`](support/archive-members.json.gz):

- **Logical Dependency Pins & Metadata Universe (`islaris-logical-dependency-pins-and-offline-solve-gate-2026` & `islaris-offline-dependency-solution-and-cudf-audit-2026`):**
  - [`support/ISLARIS-primary-files.json`](support/ISLARIS-primary-files.json), [`support/ISLARIS-source-manifest.json`](support/ISLARIS-source-manifest.json), [`support/source-selections.json`](support/source-selections.json), [`support/root-requests.json`](support/root-requests.json), [`support/upstream-fragments-manifest.json`](support/upstream-fragments-manifest.json), and upstream excerpts under `support/upstream/` ([`support/upstream/README.md`](support/upstream/README.md), [`support/upstream/islaris-deps-Makefile`](support/upstream/islaris-deps-Makefile), [`support/upstream/coq-sail.opam`](support/upstream/coq-sail.opam), [`support/upstream/coq-sail-riscv.opam`](support/upstream/coq-sail-riscv.opam), [`support/upstream/islaris-sail-riscv-README.md`](support/upstream/islaris-sail-riscv-README.md), [`support/upstream/islaris-theories-dune`](support/upstream/islaris-theories-dune), [`support/upstream/islaris-sail-riscv-test-fragment.v`](support/upstream/islaris-sail-riscv-test-fragment.v), [`support/upstream/islaris-trace-test-fragment.v`](support/upstream/islaris-trace-test-fragment.v)).
  - [`support/main-metadata.tar.gz`](support/main-metadata.tar.gz), [`support/overlay-and-primary-inputs.tar.gz`](support/overlay-and-primary-inputs.tar.gz), [`support/native-evidence.tar.gz`](support/native-evidence.tar.gz), [`support/earlier-operational-evidence.tar.gz`](support/earlier-operational-evidence.tar.gz), [`support/prior-source-report.tar.gz`](support/prior-source-report.tar.gz), [`support/selected-package-origins.json`](support/selected-package-origins.json), [`support/audit_cudf.py`](support/audit_cudf.py), [`support/cudf-audit.json`](support/cudf-audit.json), [`support/cudf-false-solution-control.json`](support/cudf-false-solution-control.json), [`support/audit-attempt-1-diagnosis.json`](support/audit-attempt-1-diagnosis.json), [`support/fatal-cleanup-disposition.md`](support/fatal-cleanup-disposition.md), [`support/ownership-oracle-results.json`](support/ownership-oracle-results.json), and [`support/input-verification.json`](support/input-verification.json).
- **Acquired-Source Identity & Build Prerequisites (`islaris-acquired-source-identity-and-build-prerequisites-2026`):**
  - [`support/plan/ARTIFACTS.json`](support/plan/ARTIFACTS.json), [`support/acquisition/download-phase.json`](support/acquisition/download-phase.json), [`support/acquisition/native-acquire-result.json`](support/acquisition/native-acquire-result.json), [`support/acquisition/source-selection-gate.json`](support/acquisition/source-selection-gate.json), [`support/audit-summary/consumer-coverage.json`](support/audit-summary/consumer-coverage.json), [`support/audit-summary/http-object-map.json`](support/audit-summary/http-object-map.json), [`support/audit-summary/unchanged-state.json`](support/audit-summary/unchanged-state.json), [`support/audit-summary/system-package-observations.json`](support/audit-summary/system-package-observations.json), [`support/independent/REVIEW.md`](support/independent/REVIEW.md), [`support/public-projection-source-audit.tar.gz`](support/public-projection-source-audit.tar.gz), [`support/public-projection.json`](support/public-projection.json), [`support/frozen-independent-review.tar.gz`](support/frozen-independent-review.tar.gz), [`support/source-acquisition-evidence.tar.gz`](support/source-acquisition-evidence.tar.gz), [`support/source-realization-plan.tar.gz`](support/source-realization-plan.tar.gz), [`support/source-pointers.json`](support/source-pointers.json), [`support/attribution-inventory.json`](support/attribution-inventory.json), and [`support/notice-pointers.json`](support/notice-pointers.json).
- **Offline Git Retrieval & Partial Install (`islaris-offline-git-retrieval-and-partial-install-2026`):**
  - [`support/context.json`](support/context.json), [`support/PRIMARY.json`](support/PRIMARY.json), [`support/GIT-PRIMARY.json`](support/GIT-PRIMARY.json), [`support/DOWNLOAD-GATE.json`](support/DOWNLOAD-GATE.json), [`support/FILTER-CONTEXT.json`](support/FILTER-CONTEXT.json), [`support/GIT-BOOKKEEPING-DELTA.json`](support/GIT-BOOKKEEPING-DELTA.json), [`support/transport-review.json`](support/transport-review.json), [`support/fan-in-results.json`](support/fan-in-results.json), [`support/projection-ledger.json`](support/projection-ledger.json), [`support/partial-install-evidence.tar.gz`](support/partial-install-evidence.tar.gz), [`support/transport-evidence.tar.gz`](support/transport-evidence.tar.gz), [`support/download-evidence.tar.gz`](support/download-evidence.tar.gz), [`support/independent-review.tar.gz`](support/independent-review.tar.gz), and [`support/host-fan-in.tar.gz`](support/host-fan-in.tar.gz).
- **Modular Effects, HeapLang & Islaris Coq Kernel Replay (`modular-effects-coq-kernel-replay-and-assumption-closure-2026`):**
  - [`support/the_artifact.zip`](support/the_artifact.zip), [`support/source-identity-proposal.json`](support/source-identity-proposal.json), [`support/source-coordinates.json`](support/source-coordinates.json), [`support/AuditCore.v`](support/AuditCore.v), [`support/AuditHeapLang.v`](support/AuditHeapLang.v), [`support/AuditIslaris.v`](support/AuditIslaris.v), [`support/actual-assumptions.json`](support/actual-assumptions.json), [`support/kernel-context.json`](support/kernel-context.json), [`support/execution-summary.json`](support/execution-summary.json), [`support/logs/final-source-check.stdout`](support/logs/final-source-check.stdout), [`support/logs/loaded-object-hashes.stdout`](support/logs/loaded-object-hashes.stdout), [`support/logs/recursive-coqchk.json`](support/logs/recursive-coqchk.json), [`support/completed-task-tree.tar.gz`](support/completed-task-tree.tar.gz), [`support/successful-phases.json`](support/successful-phases.json), [`support/operational-diagnostics.json`](support/operational-diagnostics.json), [`support/parent-mode-diagnosis.json`](support/parent-mode-diagnosis.json), [`support/public-path-projection.json`](support/public-path-projection.json), and [`support/REPLAY.md`](support/REPLAY.md).

---

## Revalidation

1. **Offline CUDF Solution & Metadata Audit:**
   - Extract [`support/native-evidence.tar.gz`](support/native-evidence.tar.gz) to a temporary directory outside the package and run `python3 support/audit_cudf.py` against `native/native-islaris-1.cudf` and the preserved raw native JSON (`support/native-dry-solve.json`). Confirm all 74 selected package identities, the single `%3dopam-invariant` record, the `240` dependency / `104` conflict / `35` request counts, and rejection of the missing-Iris negative control (`support/cudf-false-solution-control.json`).
2. **Acquired-Source Identity & Offline Git Transport Ledgers:**
   - Verify archive and member SHA256 digests against [`support/archive-index.json`](support/archive-index.json), [`support/archive-members.json.gz`](support/archive-members.json.gz), [`support/public-projection.json`](support/public-projection.json), and [`support/projection-ledger.json`](support/projection-ledger.json).
   - For a future offline continuation of the remaining 21 packages from the 53-package partial switch state, clone the preserved recovery container with `/solve/offline-git-origin` and the 8 base-URL `insteadOf` mappings intact, supply explicit external `z3`, `pkg-config`, `libgmp-dev`, and `zlib1g-dev` prerequisites, retain only one copy of exported CUDF/DOT graphs on the host, and stop on the first compiler or Sail model-generation error.
3. **Coq Modular-Effects & Islaris Adequacy Kernel Replay:**
   - Follow [`support/REPLAY.md`](support/REPLAY.md): in the Coq `8.19.2` / OCaml `4.14.4` environment with the archive's vendored `stdpp` and `iris` subtrees installed (preserving executable permissions on `make-package` scripts), generate `Makefile.coq` from `_CoqProject`, build the 9 seed targets at `-j1` (`-native-compiler no`), compile [`support/AuditCore.v`](support/AuditCore.v), [`support/AuditHeapLang.v`](support/AuditHeapLang.v), and [`support/AuditIslaris.v`](support/AuditIslaris.v), compare all 25 theorem types and `Print Assumptions` blocks against [`support/actual-assumptions.json`](support/actual-assumptions.json), and run `coqchk -o -m` across all 542 modules ([`support/logs/recursive-coqchk.json`](support/logs/recursive-coqchk.json)).

*Authored by an AI agent acting on joshlf's behalf.*
