# Selected replay

The ZIP and completed-tree tarball are evidence, not installation instructions. Use a new caller-owned workspace. Do not replay into the original archive materialization.

Prerequisite environment: Coq 8.19.2/OCaml 4.14.4; ITree 5.1.2/Paco 4.2.1/coq-elpi 2.2.3/coq-ext-lib 0.13.2/coq-record-update 0.3.6; exact archive stdpp, stdpp-bitvector, stdpp-unstable, Iris and Iris-HeapLang installed. Installed switch metadata and the actual loaded object hashes are preserved in `logs/installed-switch-state.stdout` and `logs/loaded-object-hashes.stdout`. The archive stdpp/Iris hashes, rather than the package labels `dev`, identify the relevant source. Installation is a separate prerequisite and is not performed by this replay sequence.

1. Check the package manifest and ZIP SHA256. Extract `the_artifact.zip` into the new workspace, preserving original ZIP executable modes. The original archive's regular files have the hashes in `source-identity-proposal.json`; there are476 files and no prebuilt `.vo/.vos/.vok/.vio` objects. The helper scripts `stdpp/make-package` and `iris/make-package` are executable in the ZIP; they are not needed for the selected build after dependencies are ready.
2. Copy only the three supplied `Audit*.v` files into the extracted `the_artifact/iris-itree` directory. They are observation-only. Select the recorded Coq environment on PATH. Work from that directory.
3. Run the following commands, logging exit status/stdout/stderr separately. These use the recorded Linux tools; bound each phase externally and keep only one Coq worker. The original run capped core 20 min, HeapLang 15 min, optional Islaris 10 min, and checker/audits 20 min, with ≤1 GiB additional task outputs. A cap failure is not successful theorem replay.

```sh
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq -j1 src/exec.vo src/heap.vo src/threadpool/exec.vo src/threadpool/interleaving.vo src/examplelang/adequacy.vo
make -f Makefile.coq -j1 src/heaplang/adequacy.vo src/heaplang/opsem_adequacy.vo
make -f Makefile.coq -j1 islaris/adequacy.vo islaris/adequacy_itree.vo
coqc -q -w -redundant-canonical-projection -w -notation-overridden -w -future-coercion-class-field -Q src iris.itree -Q islaris isla AuditCore.v
coqc -q -w -redundant-canonical-projection -w -notation-overridden -w -future-coercion-class-field -Q src iris.itree -Q islaris isla AuditHeapLang.v
coqc -q -w -redundant-canonical-projection -w -notation-overridden -w -future-coercion-class-field -Q src iris.itree -Q islaris isla AuditIslaris.v
coqchk -Q src iris.itree -Q islaris isla -o -m iris.itree.exec iris.itree.heap iris.itree.threadpool.exec iris.itree.threadpool.interleaving iris.itree.examplelang.adequacy iris.itree.heaplang.adequacy iris.itree.heaplang.opsem_adequacy isla.adequacy isla.adequacy_itree AuditCore AuditHeapLang AuditIslaris
```

4. Compare the 25 actual result types and their assumption sets to `actual-assumptions.json`. Native checking must exit 0 with the success marker and retain its recursive dependency checks; neither `-admit` nor `-norec` may be added. Compare the global context separately from the per-constant assumptions. Recheck all original source hashes. Inspect actual loaded object hashes instead of assuming that version labels alone identify all dependencies.

For a cheaper recheck in a compatible existing environment, extract `completed-task-tree.tar.gz` into a new owned directory, verify its regular-file hashes against `logs/post-hashes.stdout`, then recompile the three audits and invoke the same recursive checker. Compatibility includes the dependency object identities; an inconsistent-assumptions error is an environment mismatch to diagnose, not a reason to weaken checking. The tar's UID/GID/mtime are transport-normalized; file bytes/modes are preserved.

The original author harness (`run_assigned.py`) is retained for provenance, with its task-specific container name and paths. It is not a generic dependency installer. All raw proof/output bytes are retained; only three public copy-command receipts have the declared host display-path projection.
