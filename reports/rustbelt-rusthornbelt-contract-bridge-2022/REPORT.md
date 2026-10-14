# Semantic Rust typing and the first-order contract bridge

## Summary

RustBelt and RustHornBelt give semantic typing judgments whose implementations must establish weakest preconditions under ownership, lifetime and continuation resources. RustHornBelt additionally tracks mutable references through current/final values and consistent parametric prophecy assignments. This makes a first-order contract useful only after its connection to the semantic judgment has been proved.

The directly inspected closed soundness theorems establish non-racing and non-stuck finite executions of LambdaRust programs. They do not establish rustc correspondence, termination, arbitrary unsafe-caller safety, or automatic acceptance of a solver's contract.

## Applicability

This report compares two separately pinned source archives: RustBelt's `lambda-rust-popl18.tar.gz` and the 2022 RustHornBelt artifact at Zenodo record 6417462. Their SHA-256 identities are in `REPORT.json` and their inspected source members in `source-evidence.json`. A tag's Git commit was not recovered; the acquired archive digest binds the exact examined bytes. The RustHornBelt README requests Coq 8.13.0 and Iris `dev.2021-03-27.0.f1484b2b`. No claim of compatibility with modern Rocq, modern Iris or Lean follows.

The RustHorn paper supplies a distinct theorem about its COR language and CHC encoding, rather than an implementation claim about the RustHornBelt artifact. The acquired author PDF is an updated full version, identifies a newer TOPLAS presentation, and is not identified with the original arXiv/ESOP PDF bytes. The RustHornBelt paper and its author erratum provide documentary context. Source inspection and paper reading occurred on 2026-10-14; no prover or solver was run.

## Findings

### Semantic types contain ownership and sharing obligations

RustBelt's `theories/typing/type.v:22–48` defines a type by its size, owned-value predicate and shared-location predicate. The shared predicate must be persistent; ownership entails a value list of the declared size; sharing requires a lifetime context, a borrow of the owned memory, a live lifetime token and an appropriate update mask. Sharing must also be monotone under lifetime inclusion. This is a representation invariant with laws, rather than a surface Rust type declaration. Basis: **source**.

`typed_body` in `theories/typing/programs.v` universally quantifies the thread identifier and consumes interpreted external/local lifetime, continuation and type contexts before proving a WP. Thus the abstraction boundary is explicit: a replacement implementation must establish the semantic judgment expected by clients. The examined RustBelt `type_soundness` theorem quantifies over every `typeG` instance and assumes a semantically typed empty-argument, unit-returning main. From `rtc step` beginning with that main and an empty state, it concludes a non-racing thread pool and that every thread is a value or reducible. The closed variant chooses `typeΣ`. Its conclusion is model safety for those executions. Basis: **source**, `typing/soundness.v:28–32,63–70`; [pinned archive](https://gitlab.mpi-sws.org/iris/lambda-rust/-/archive/popl18/lambda-rust-popl18.tar.gz).

A library-level all-client statement consequently needs the library's semantic interface and a linking argument placing each permitted client in the theorem's premises. Proving one use or translating an API signature does not discharge that quantification. This is a **derived** obligation from the universally quantified semantic judgment and closed-main theorem.

### Lifetime recovery is controlled by tokens, inclusion and continuations

The historical lifetime module signature exposes fractional live tokens, persistent death evidence, lifetime inclusion and guarded borrows. Its concrete implementation includes proved model modules. Borrow creation returns both the borrow and a continuation that recovers guarded ownership after death evidence; shortening needs inclusion evidence; accessors require a live token and return a closing continuation. `lft_tok_dead` rules out simultaneously live and dead ownership. These interfaces constrain when clients regain resources and prevent treating a shortened borrow as unrestricted ownership. Basis: **source**, `lifetime/lifetime_sig.v`, `lifetime.v`, `model/borrow.v` and `model/primitive.v` in the pinned archive.

This investigation inspected the interface and selected implementations. It did not audit every nested/reborrow derivation or port the module to a different Iris version.

### RustHornBelt adds logical values and predicate transformers to semantic typing

In the 2022 artifact, `typed_body` additionally quantifies a list of clairvoyant input values and a continuation postcondition. It requires lifetime, time, prophecy and unique-borrow contexts, interpreted ownership contexts, and a prophecy observation asserting the supplied predicate transformer before establishing WP. `typed_instr` returns interpreted output ownership and an observation about the output values. These are actual separation-logic judgments; an SMT relation is not itself one of their proofs. Basis: **source**, `typing/programs.v:13–17,44–52,82`.

The semantic `fn` type packages a guarded, persistent body obligation for all its instantiations, call lifetime, continuation and arguments. The source explicitly describes its lifetime-well-formedness constraints as simplified relative to Rust. `uniq_bor` carries a pair of logical values: the current value is represented by the borrowed body, and the final component is tied to a fresh prophecy variable. A verified `vec_push_type` transformer relates the final list to the current list extended by the inserted element. This is a concrete example of the bridge between an imperative implementation and a mathematical contract, for that LambdaRust vector implementation. Basis: **source**, `typing/function.v:60–76`, `typing/uniq_bor.v:22–33`, `typing/lib/vec/vec_pushpop.v` in the [2022 artifact](https://zenodo.org/records/6417462).

The artifact's `type_soundness` again assumes a semantically typed unit main, now with `main_transformer`, and finite `rtc erased_step` executions from an empty state. Its conclusion is non-racing and non-stuckness. The inspected theorem does not state a generic functional postcondition theorem for arbitrary externally supplied FOL contracts. Basis: **source**, `typing/soundness.v:27–35,69–76`.

### Parametric prophecy consistency prevents arbitrary future assumptions

`prophecy/prophecy.v` represents a prophecy assignment as a dependent mapping from typed prophecy variables to their values; a clairvoyant value is a function of an assignment. The dependency predicate states that assignments agreeing on a finite variable list produce the same value. A valid resolution log prohibits repeated resolution and dependence on already resolved variables. `proph_ok_sat` proves a satisfying assignment exists for such a log. Basis: **source**, lines 12–32,128–174.

The prophecy context owns the authoritative valid log. Resolution requires a full token for the variable being resolved, dependency tokens, a dependency proof for the resolved value, and an update mask containing the prophecy namespace. `proph_obs_sat` obtains an assignment satisfying an observation; `proph_obs_false` rules out an observation of false. The discipline therefore supports reasoning about eventual values without granting a client permission to assume an arbitrary inconsistent future. Basis: **source** + **derived**, lines 209–218,336–353,393–415.

This differs from an operational prophecy map whose state interpretation consumes an actual observation trace. The two mechanisms need their own consistency and adequacy connection; sharing the term “prophecy” does not supply an interchange theorem.

### CHC correspondence and tool integration have distinct boundaries

RustHorn's Theorem 1 equates the concrete input/output relation with the least model of its CHC translation for a COR program and a *simple* function. The definition of simple excludes lifetime parameters and reference input/output types. The proof uses an abstract semantics and ownership-sensitive readout. This is a precise model theorem, not a theorem for every unsafe Rust API or arbitrary caller. Basis: **documentation**; [author full-version paper](https://shiatsumat.github.io/papers/esop2020-rust-horn.pdf), §3.3, Theorem 1.

The RustHornBelt paper reports a remaining integration gap between Creusot/WhyML's pure-function specifications and the mechanized predicate-transformer formulation; unsafe APIs are proved manually in Iris. It also records limitations for reference-counted/interior-mutable library examples. The author erratum corrects swapped `last`/`init` occurrences in the paper's `Vec::pop` specification. These documentary qualifications must accompany a reused contract. Basis: **documentation**; [paper](https://www.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf), [erratum](https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/errata.txt).

The practical acceptance boundary is consequently: establish the API's semantic transformer; justify the frontend's translation and the client contract language; discharge the client's proof obligations; and compose them under the same operational interpretation and assumptions. That sequence is a **derived** dependency argument, not an executed tool workflow.

## Boundaries

- **Known not to apply:** the inspected soundness theorems do not prove rustc compilation correct, termination, current standard-library implementations, or arbitrary unsafe callers outside semantic typing premises.
- **Not examined:** full prover assumption closure, all feature rules and client linking cases; execution of the archived artifacts; RustHorn's actual solver/backend and invariant synthesis; genericity or recursion support beyond the stated formal models.
- **Unknown:** an end-to-end bridge from current Creusot or another CHC/FOL tool's emitted obligations to these exact semantic judgments and dependencies.
- **Not established:** treating a first-order contract or CHC solver success as direct RustHornBelt proof evidence without that bridge; importing the historical lifetime/prophecy module into a new prover by name alone.
- **Remaining scope:** ordinary and parametric prophecy interfaces are distinguished; a full comparative construction and cross-prover proof are absent. Lean-native feasibility is a separate investigation.

## Evidence

`source-evidence.json` records archive URLs, full digests, original member paths, member SHA-256 hashes and inspected symbols. No artifact program was executed or Coq proof freshly checked. “Proved” above describes source theorem declarations ending in `Qed`, with their displayed premises; it does not assert this inspection audited every transitive axiom.

The RustHornBelt artifact is public record 6417462, acquired SHA-256 `7e67c2d49b3b655113675c0d517d76589d615c9622eac2d91417d99263959121`. Its indexed MD5 matches the acquired archive. The paper SHA-256 is `3f058c16579bbff0e8f1b00e21ee964b3fa06c1d7f4351ff903047095f46ab38` (DOI `10.1145/3519939.3523704`); the erratum SHA-256 is `5112f5ce4e316b4fce265321ead594e368a232bae5b5cd1876baef655c7f65c5`. The updated RustHorn author PDF SHA-256 is `0bcf21029350d89ec36ead06489a5eef681af5d3308c31ea90a33fff9fe32ef9`, associated with ESOP DOI `10.1007/978-3-030-44914-8_18`; exact-byte identity takes precedence over interpreting its mutable URL as the original release.

## Revalidation

Reacquire and verify the exact archive/PDF digests. Inspect `type`, `typed_body`, the function/unique-borrow interpretation, prophecy resolution and the soundness theorem together: changing any contract carrier can change the proof obligation. Build only in the declared dependency environment and inspect the assumptions of accepted soundness/contract theorems. Before using another frontend, compare its specification meaning with the predicate transformer and prove the connection. For a library guarantee, retain the quantified client/linking premise and prove the implementation satisfies it; for a new language or compiler pipeline, supply a separate correspondence and source-safety argument.

*Authored by an AI agent acting on joshlf's behalf.*
