# Scratch tactic candidates with source and environment CAS

## Contract prototype

This is a **small contract prototype**, not an Anneal scratch service. It uses pinned Lean 4.30.0-rc2 on one theorem in `Proof.lean`, imported from `ProbeEnv.lean`. Canonical state is a sequence of immutable generation directories plus an atomically replaced `CURRENT.json` pointer. Each candidate gets a private copy of the proof, import source, and compiled `.olean`; it is batch-checked with `lean --json`. Under a file lock, application compares the candidate's recorded source bytes, import source and `.olean` hashes, Lean binary hash, and the canonical generation's exact source/environment/version preimage before creating a new immutable generation and switching the pointer.

The fixture's theorem statement and binder line must also remain byte-identical. This explicit guard catches one misleading batch-successful edit, but it is a fixture-specific text check, not a general Lean proposition/assumption equivalence oracle. The prototype rejects literal `sorry`/`admit` source text, even though `lean --json` can exit 0 for `sorry`; this is not a comprehensive axiom-use check.

## Executed decisions

Eleven decisions are retained in `support/results.json`:

| Case | Direct check and CAS result |
| --- | --- |
| Accepted tactic | `exact Nat.add_zero n` → `simp` passed scratch batch and published generation 2. |
| Duplicate retry | Same request ID returned the recorded version 2 without another generation. |
| Stale source | A valid candidate based on generation 1 was rejected after generation 2 changed proof bytes. |
| Partial tactic | `skip` left an unsolved goal; batch exit was nonzero and publication rejected. |
| Failed tactic | `exact False.elim` failed elaboration; publication rejected. |
| Admission | `sorry` had batch exit 0 but was rejected by the prototype's explicit admission rule. |
| Changed target | Replacing `n + 0 = n` with `n = n` and using `rfl` had batch exit 0, but statement-line identity rejected it. |
| Candidate mutated after check | A post-check source edit was rejected by the candidate-content hash. |
| Changed environment | Canonical `ProbeEnv.lean` changed `7` → `8` and was recompiled into generation 3 while proof bytes stayed fixed; an older valid candidate was rejected by import source/`.olean` identity. |
| Cancellation | A private Lean process group was stopped and killed before completion; no canonical pointer change occurred. |
| Scratch reuse | The cancelled scratch directory was rebuilt, its new candidate batch-checked, and generation 4 was published. |

The final published proof and environment are retained in `support/artifacts/`. A fresh `lean --json` on generation 4 exited 0 and produced the same stdout/stderr as the accepted scratch candidate. `support/verify.py` checks all eleven decisions, exact pointer hashes, final source/environment hashes, four generation states, cancellation result, and the batch comparison.

## [#3731](https://github.com/google/zerocopy/issues/3731) I070 coverage and residuals

This locally executable slice shows isolated candidate workspaces, exact-preimage publication, duplicate handling, post-check mutation rejection, changed import identity, partial/failed/cancelled attempts, and fresh batch comparison. The prototype does **not** implement Anneal's subject/proof identities, Rust annotation mapping, user/agent authority, or a long-lived Lean server fork. It tests one theorem and one direct import only. A production acceptance oracle still needs elaborated target and assumption comparison, transitive environment/options/native identity, absence of hidden admissions or unsafe axioms, complete obligation status, provenance to the intended Rust source, and durable transaction semantics. The file-lock/pointer model was not subjected to concurrent writers or crash injection; its separate request journal can be interrupted independently of pointer replacement.

No claim is made that I070 is complete or that an Anneal API behaves this way.

## Reproduce

With the pinned Lean binary already available, run from this package directory:

```sh
python3 support/probe.py --work /Users/josh/Codex/Meta/Data/20260929-issue-3730-3731/r19-replay-new
python3 support/verify.py
```

The work path must be absent and owned; the script requires at least 15 GiB free, uses one Lean thread, private scratch directories, and 20-second batch timeouts. It replaces retained result/artifact files in this package. The verifier reads only retained files.
