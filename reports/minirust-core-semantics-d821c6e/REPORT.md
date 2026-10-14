# MiniRust's memory interfaces and the limits of reusable Rust calculi

## Summary

MiniRust provides concrete definitions for bytes, provenance, representation, and aliasing-sensitive memory operations. Its language is parameterized by a memory implementation, so choosing MiniRust alone does not fix the safety property. The examined tree also contains a Rust-to-MiniRust translator, but no inspected theorem establishes that translation or the executable interpreter as a trustworthy foundation for Rust safety.

The older core calculi answer different questions. Their borrowing and typing results can supply useful mechanisms and proof patterns; their formal subjects and omitted unsafe behaviors remain part of every reused theorem.

## Applicability

MiniRust source and tooling were directly inspected at `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (committed 2026-07-27). Its toolchain file requests `nightly-2026-05-01`. The comparison uses exact paper versions in `REPORT.json`; Featherweight Rust uses the author-hosted preprint bytes identified by SHA-256, whose footer says March 2020, rather than assuming it is byte-identical to the published 2021 article. No translator, interpreter, K, Coq, or Rocq development was built or executed.

## Findings

### The memory parameter is part of the model's identity

`ThinPointer<Provenance>` contains `addr` and optional provenance; wide `Pointer` adds metadata. `Memory` supplies the provenance type, allocation, load/store, dereferenceability, retagging, and call-end hooks. Loads take mutable memory because reads can change aliasing state. `AbstractByte` distinguishes `Uninit` from `Init(u8, optional provenance fragment)`; a fragment carries its pointer-byte position. Basis: **source**, `spec/mem/pointer.md` and `interface.md`. [Pointer definitions](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/pointer.md), [memory interface](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/interface.md).

`BasicMemory` tracks allocation identity, address, contents, alignment, and whether the allocation is live. `check_ptr` accepts zero-length ranges without provenance; nonempty accesses require provenance, a live allocation, and an in-bounds range. Load/store check alignment before that zero-length shortcut. The basic implementation ignores aliasing. `TreeBorrowsMemory` adds a tree path to allocation provenance and updates permissions on accesses. Therefore BasicMemory acceptance does not establish Tree Borrows acceptance. Basis: **source** + **derived** consequence. [Basic model](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/basic.md), [Tree Borrows model](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/memory.md).

The README still says that no memory implementation is given, although it links both implementations. Actual definitions determine this report's source findings; the inconsistent introductory sentence should not be used to classify the tree as interface-only. The README also describes incompleteness and future theorem-prover translation. That is a documented prospect, not observed proof integration. Basis: **documentation** + **source** discrepancy. [Pinned README](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/README.md).

### Representation and exposure take different routes through provenance

Integer decoding discards byte provenance; integer encoding produces bytes without it. `encode_ptr` records provenance with byte positions; `decode_ptr` retains it only when all fragments agree and occupy the expected positions. Missing or mixed fragments produce a pointer without provenance. The file explicitly leaves pointer/integer transmutation choices under discussion. Basis: **source**, `Type::encode`, `Type::decode`, `encode_ptr`, `decode_ptr`. [Representation definitions](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/representation.md#L73).

Integer-pointer *casts* use separate `IntPtrCast` state. `expose` records provenance; `int2ptr` uses `predict` to choose absent or previously exposed provenance. The specification gives this choice an angelic reading: an available choice that makes behavior defined is chosen. The README's ordinary `pick` choices are demonic, requiring correctness for all choices. A theorem-prover embedding must preserve both interpretations; replacing `predict` with ordinary nondeterministic branching changes the specification. Basis: **source/documentation** + **derived** embedding obligation. [Cast model](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/intptrcast.md).

### Existing tooling is a concrete connection, with an unproved boundary

`tooling/README.md` identifies `minimize` as a Rust-via-MIR translator linking rustc. Its `main.rs` defaults include `-Zmir-emit-retag`, `-Zmir-opt-level=0`, and `-Zmir-preserve-ub`, and disables compiler-inserted UB checks. This is evidence that UB-preserving extraction matters operationally. It is not a proof that every source UB survives the pipeline or that every translation branch is supported. Basis: **source/documentation**. [Tooling](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/README.md), [translator arguments](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/main.rs#L105).

`ConcurrentMemory` records accesses and checks conflicting overlapping accesses unless both are atomic. Its atomicity domain contains only sequentially consistent atomic and non-atomic access; the introductory text says atomicity is currently ignored. The machine tracks threads and races, but these definitions do not supply a relaxed-atomic Rust model. Basis: **source**. [Concurrent wrapper](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/concurrent.md).

### Core calculi offer different reusable interfaces

| Formal subject | Definition/result useful to retain | Unsafe-verification boundary |
| --- | --- | --- |
| λRust / RustBelt, POPL 2018 | Semantic typing plus adequacy permits verified unsafe abstractions to compose with typed clients. Appendix Fig. 2 uses allocation locations and distinct non-atomic/SC operations | A custom MIR-inspired CPS language; main paper omits traits and relaxed memory. Its theorem does not certify actual Rust lowering or a current alias model |
| Oxide, arXiv v4 | Region sets approximate reference origins; progress/preservation handle borrow checking, branches, closures, and NLL | Tested correspondence is typechecking on a supported suite, not operational correspondence for arbitrary unsafe pointers; §3.8 excludes unsafe and other feature classes |
| Featherweight Rust, identified author preprint | Owned versus borrowed location values separate dropping from borrowing; flow typing and a type/borrow-safety theorem | Core syntax is small and lexical. §4.5.2 relies on termination; §5.3 discusses NLL mismatches. Core theorem does not establish source pointer-byte or alias-model rules |
| Rust Distilled, arXiv v2 | Region context tracks fractional capability and borrower metadata; dropping a borrow restores capability to its parent | An exploratory expressiveness tower and early Oxide account. Library operations are abstracted; progress/preservation and instrumented-state erasure correspondence remain planned in this version |
| KRust, arXiv v1 | K operational definitions for ownership, borrows, and a supported surface subset; executable-definition architecture | §VI explicitly leaves unsafe and concurrency unimplemented, along with reference fields, closures, traits and other features |

Basis: **source**, defining papers/appendix. [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf), [appendix](https://plv.mpi-sws.org/rustbelt/popl18/appendix.pdf), [Oxide v4](https://arxiv.org/pdf/1903.00982v4), [Featherweight preprint](https://whileydave.com/publications/Pea21_TOPLAS_preprint.pdf), [Rust Distilled v2](https://arxiv.org/pdf/1806.02693v2), [KRust v1](https://arxiv.org/pdf/1804.10806v1).

Reusing a capability, lifetime, or typing lemma first requires mapping the new operational subject into the theorem's subject and preserving its premises. Similar reference syntax supplies no such map. This is a **derived** constraint on theorem reuse.

## Boundaries

- **Unknown:** a proved source-safety-reflecting Rust-to-MiniRust correspondence or a verified Specr-to-proof-assistant translation for this revision. This investigation did not establish absence across all work elsewhere.
- **Not examined:** the complete `minimize` lowering, every language operator, every target, Specr transpiler internals, and theorem artifacts for the comparison calculi.
- **Unsupported in the compared KRust paper:** unsafe code and concurrency. This is a paper-version claim, not a claim about every later implementation.
- **Known not to apply:** the examined concurrent MiniRust wrapper does not specify Rust's full relaxed-memory behavior.
- **Not established:** equivalence of MiniRust Tree Borrows to the PLDI 2025 calculus, Miri at another revision, or a program logic's operational language. Exact aliases, byte behavior, targets and parameters require separate comparison.

## Evidence

All evidence was acquired or rechecked on 2026-10-14. MiniRust commit and source paths above are immutable coordinates. Additional narrow locations are `spec/prelude/target.md` (`Target` parameters), `spec/lang/machine.md` (`Machine::step`), and `spec/mem/tree_borrows/reborrow_settings.md` (retag settings). Paper bytes are bound by the SHA-256 values in `REPORT.json` where acquired.

- RustBelt DOI `10.1145/3158154`, §§1.2, 7 and 9; appendix dated 2017-11-09, Fig. 2, allocation/load/store transitions. Main paper was inspected through the author-hosted PDF; appendix bytes were hashed.
- Oxide `1903.00982v4`, 2021-10-19: §3.7 progress/preservation, §3.8 test scope. No artifact rebuild.
- Featherweight preprint: Fig. 1, §§4.5, 4.5.2 and 5.3. Published article DOI `10.1145/3443420` is bibliographic context; inspected bytes remain separately identified.
- Rust Distilled `1806.02693v2`, 2018-08-16: fractional region/capability example and abstraction discussion.
- KRust `1804.10806v1`, 2018-04-28: semantics overview and §VI unsupported features. No repository revision is inferred from a paper URL.

## Revalidation

For MiniRust, diff the memory interface, BasicMemory checks, byte representation, cast state, retag settings, and translator default arguments at the new commit. A useful next probe holds address bytes fixed while removing one provenance fragment, then contrasts exposed casts with integer transmutation. Run it only with a pinned interpreter, target, memory implementation, and parameters. For theorem reuse, inspect the theorem statement and the operational domains it quantifies over before attempting translation. Broad feature inventories or matching example outputs cannot replace that correspondence.

*Authored by an AI agent acting on joshlf's behalf.*
