# Revalidate this selected replay

This file is evidence and reproducibility guidance. Use a separately authorized task-owned environment and output tree. It performs no installation and does not authorize another runtime or a broader examples build.

## Package-only integrity

From the report directory:

```sh
python3 -B support/verify_package.py
```

This reads package bytes and checks the recorded bindings. It neither compiles a proof nor substitutes for native checking.

## Native checking with the recorded environment

The original run used OCaml4.14.4 and the exact Rocq9.2.0/Iris/stdpp/dependency versions in the installed switch receipts. The source archives, opam metadata and dependency-lock receipts are retained. Reconstructing that environment is a separate installation/resource decision; do not silently select newer packages.

Copy `support/checked-project` to a fresh owned working directory, retaining its bytes. In that copy, with the recorded environment's PATH (the observed invocation used `opam exec --switch=4.14 --`), the substantive native command is:

```sh
rocq check -Q theories simuliris -o -m \
  simuliris.simulation.adequacy \
  simuliris.tree_borrows.adequacy \
  simuliris.tree_borrows.examples.lib \
  simuliris.tree_borrows.examples.protected.mutable_reorder_write_up_activated_paper \
  simuliris.tree_borrows.examples.unprotected.shared_delete_read_escaped \
  simuliris.tree_borrows.read_read_reorder.read_reorder \
  PlannedAuditFramework PlannedAuditResources PlannedAuditExamples
```

Require exit0, the final success marker, all selected constants in the full trace and the expected context summary. Do not add `-admit`, `-norec` or an axiom/proof patch. Compare the loaded `.vo` files against the recorded517-object hash listing. The fixed absolute container paths in that listing identify the observed files; if materialized at new paths, change only the physical prefix in a separate comparison map and retain every logical library identity and object hash.

## Fresh source compilation

Start from the retained exact `simuliris.tar.gz` in a new owned tree with no proof objects. Copy only the three preserved `PlannedAudit*.v` observation files into its source root. They do not belong in Makefile generation. Run the following selected targets serially:

```sh
rocq makefile -f _RocqProject -o Makefile.rocq
make -f Makefile.rocq -j1 theories/simulation/adequacy.vo
make -f Makefile.rocq -j1 \
  theories/tree_borrows/adequacy.vo \
  theories/tree_borrows/examples/lib.vo
make -f Makefile.rocq -j1 \
  theories/tree_borrows/examples/protected/mutable_reorder_write_up_activated_paper.vo \
  theories/tree_borrows/examples/unprotected/shared_delete_read_escaped.vo
make -f Makefile.rocq -j1 \
  theories/tree_borrows/read_read_reorder/read_reorder.vo
```

Before consuming builds, inspect `Makefile.rocq.conf`: logical flags must retain `-Q theories simuliris` with no overriding `-R . Top`. In the original corrected run, both partial objects from the failed namespace setup were explicitly forced to rebuild using `-W theories/logic/satisfiable.v -W theories/simulation/language.v`; a genuinely fresh tree has no such objects to reuse.

Compile each unchanged annotation separately. The exact argv prefix is in `audit-command-flags.json` (outside the copied project), derived from original generated `COQMF_OTHERFLAGS` and `COQMF_COQLIBS`, plus generated Makefile's default `-q`. It is:

```sh
rocq compile -q \
  -w -notation-overridden -w -redundant-canonical-projection \
  -w -notation-incompatible-prefix -w -notation-for-abbreviation \
  -w -missing-scheme -w -level-tolerance \
  -set 'Default Goal Selector=!' -set 'Default Proof Using=Type' \
  -set 'Suggest Proof Using' -Q theories simuliris PlannedAuditFramework.v
```

Repeat with `PlannedAuditResources.v` and `PlannedAuditExamples.v`, recording each full stream/status. Require24exact qualified `Check`/`Print Assumptions` observations:19closed and5with the two specified classical axioms. Then repeat the recursive native command above and hash the actual loaded objects. Recheck all185original source hashes before and after. A different theorem type, import mapping, assumption set or source byte is a review condition, not a reason to weaken the check.

The observed caps were generic5min, TBcore30min, examples15min, sequentialreads10min, cumulativeaudits/checker20min, one proof process and≤1GiB additional project output. SimuLang non-atomic-invariant builds are outside this selection. Timing is evidence for this observed run, not a promise for another machine.
