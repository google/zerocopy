# Proposed commands for parent review — none executed

The parent chooses the new container, task root, source copies, OPAMROOT and package installation. The agent has no runtime/install authorization in this planning assignment. Use the cached pinned `ocaml/opam@sha256:fc198c017f2474a20afe68636b3b790f7247c7593c7d252bb161673b11e5b9a2` image only as a parent-selected starting point; inspect the resulting actual image/tool identities. Do not mutate the existing Coq 8.19 prefix.

## Parent preparation and installation proposal

1. Acquire exact dependency sources from `DEPENDENCIES.json`; verify the listed checksums and Git commit identities. Source archive hashes for Iris/stdpp remain acquisition outputs to record, not guessed values. Preserve original executable modes. Review each source package's build/install scripts and its opam metadata before any installation. In particular Iris/stdpp invoke `make-package`; Equations/Rocq-Elpi/Elpi invoke Dune, and Rocq-Elpi may invoke its wrapper script when the compatibility package is absent.
2. In the new parent-owned OPAMROOT, create/select an explicit OCaml 4.14.4 switch. Freeze the OCaml-repository and Rocq-released metadata as well as Iris-opam snapshot `3c21518b509d33676776c36e160de1d76835b801`. Compare the three exact release-package blob identities in `primary-package-metadata.json`.
3. Request these direct versions together. `--show-actions` is the proposed solver-only gate; preserve and review its complete transitive solution. Add explicit pins/lock constraints for that reviewed solution before installation, with no implicit upgrades to source/compiler/dependencies.

```sh
opam install --show-actions dune.3.17.2 rocq-runtime.9.2.0 rocq-core.9.2.0 coq-core.9.2.0 rocq-stdlib.9.2.0 rocq-equations.1.3.2+9.2 rocq-elpi.3.5.1 elpi.3.7.3 rocq-stdpp.dev.2026-09-09.1.c3186aad rocq-iris.dev.2026-09-10.3.b3495ef9
```

The Iris repository must be selected at the fixed snapshot; the exact version requests avoid the source package's alternative unconstrained `dev`. A reviewed local source pin is also possible if it preserves the exact package version/source identity. No whole Simuliris package install is necessary for the selected proof closure.

Only after the parent approves the complete solver/source/script result:

```sh
opam install --jobs=1 dune.3.17.2 rocq-runtime.9.2.0 rocq-core.9.2.0 coq-core.9.2.0 rocq-stdlib.9.2.0 rocq-equations.1.3.2+9.2 rocq-elpi.3.5.1 elpi.3.7.3 rocq-stdpp.dev.2026-09-09.1.c3186aad rocq-iris.dev.2026-09-10.3.b3495ef9
```

Do not add test/doc/dev-setup flags for this dependency install. Preserve package source checksums, metadata, actual build/install argv/logs, final switch export and binary/library identities. Stop and review any conflict rather than replacing exact versions. `rocq-iris-heap-lang`, stdpp bitvector/unstable, ITree and Paco are not selected dependencies in the inspected import closure.

## Identity gate after explicit READY

The actual prefix must provide Rocq 9.2.0, OCaml 4.14.4, Dune 3.17.2 and the exact named package versions/sources. Read `rocq --version`, `rocqchk --version`, `rocq --help`, `rocq check --help`, `ocamlc -version`, `dune --version`, package metadata and load-path identities. Usage/help commands may intentionally return a usage status; preserve it separately from proof outcomes. Use the documented 9.2 command names (`rocq compile`, `rocq makefile`, `rocq check`/`rocqchk`) and confirm actual supported checker flags.

The parent must copy the exact archive into a task-owned source tree, verify all 185 file bytes and absence of prebuilt proof objects, then authorize writes only for generated objects/Makefile and the owned observation-only audits. The proposed three annotation files are ordinary source inputs; copy and hash them before building. They contain no proof or axiom changes.

## Selected full proof build

From that task-owned Simuliris root, using the selected prefix on PATH:

```sh
rocq makefile -f _RocqProject -o Makefile.rocq PlannedAuditFramework.v PlannedAuditResources.v PlannedAuditExamples.v
make -f Makefile.rocq -j1 theories/simulation/adequacy.vo
make -f Makefile.rocq -j1 theories/tree_borrows/adequacy.vo theories/tree_borrows/examples/lib.vo
make -f Makefile.rocq -j1 theories/tree_borrows/examples/protected/mutable_reorder_write_up_activated_paper.vo theories/tree_borrows/examples/unprotected/shared_delete_read_escaped.vo
make -f Makefile.rocq -j1 theories/tree_borrows/read_read_reorder/read_reorder.vo
make -f Makefile.rocq -j1 PlannedAuditFramework.vo PlannedAuditResources.vo PlannedAuditExamples.vo
```

The original project flags and logical map `-Q theories simuliris` remain intact. Save generated dependency files and actual recipes. Build full `.vo` files; do not switch to proof-skipping `.vos`, weaken warnings/checking, add admissions, patch source or update dependencies to obtain a pass. Avoid default `make all`, `make build-dep`/`builddep` and cleanup targets. The inspected `builddep` target mutates opam state and the default target includes the whole examples collection.

## Actual assumption audit and recursive checker

Capture the three audit stdout streams in full. They must show the exact qualified constants, quantified premises, conclusions and actual `Print Assumptions` results. Names and expectations in this plan are not a substitute for those outputs.

After confirming the installed checker's supported options, the proposed recursive invocation is:

```sh
rocq check -Q theories simuliris -o -m simuliris.simulation.adequacy simuliris.tree_borrows.adequacy simuliris.tree_borrows.examples.lib simuliris.tree_borrows.examples.protected.mutable_reorder_write_up_activated_paper simuliris.tree_borrows.examples.unprotected.shared_delete_read_escaped simuliris.tree_borrows.read_read_reorder.read_reorder PlannedAuditFramework PlannedAuditResources PlannedAuditExamples
```

`rocqchk` is the alternative documented entry point to the same tool. Do not add `-admit` or `-norec`. Save the entire recursive trace, global context summary, loaded-object paths/hashes and exit status. A pass needs the checker's actual success outcome, no skipped dependencies, expected source identity, and the complete per-constant audits. Distinguish ordinary theorem premises from declared axioms, and selected proof dependencies from declarations merely present in the global imported context. The checker does not prove its axioms, primitive interfaces, kernel or runtime correct.

Record resource measurements and all caps/stops. The plan proposes one proof worker, 3 GiB memory, two CPUs, ≤1 GiB additional project output, with per-phase caps in `PROPOSAL.md`. On unexpected panic/assertion/invariant failure or identity disagreement, stop the affected path, preserve evidence and diagnose before proposing a retry or workaround. Parent owns all install/resource/cleanup decisions.
