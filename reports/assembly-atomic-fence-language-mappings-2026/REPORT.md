# Atomic and fence mappings across Rust, x86-TSO, and AArch64

## Summary

A concurrent assembly contract needs three distinct accounts: the language's allowed accesses and synchronization, the compiler's effects and transformations, and the hardware memory model. Observing the expected atomic instruction establishes only one part of that chain. A sequential state transformer does not supply reads-from, coherence, happens-before, RMW atomicity, or fence semantics.

This investigation inspects pinned x86-TSO and Arm CAT sources, published mapping/equivalence results and selected Coq theorem statements, Rust 1.99's C++20-derived rules, and actual Clang compilation. Header-free witnesses produced 51 function/configuration pairs across x86-64, baseline AArch64, and AArch64 with LSE; 167 computed IR/instruction predicates pass. Ten additional fixed-candidate relation calculations illustrate missing-fence distinctions; they are explicitly projections, not herd executions.

*Authored by an AI agent acting on joshlf's behalf.*

## Applicability

The source subjects are comparisons, not a proved combined implementation:

- herdtools7 `9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34`: the default `herd/libdir/x86tso.cat` and `aarch64.cat`, their inspected include closure, and selected AArch64 event generation.
- Rust `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` (1.99.0), Reference `2dafab96d919d6ab2884488e970bf95610ff83eb`, and Kraken `8af78062037bc237b341d20252aafd1797c1bcb7`.
- IMM source `4ca191b072df081dd3a6d9aa755959dc901b1bd0`, selected theorem/definition inspection only.
- Upstream LLVM 21.1.0 documentation at `3623fe661ae35c6c80ac221f14d85be76aa870f1`, informative context rather than an identity claim about Apple's compiler.
- Installed Apple clang 21.0.0, `clang-2100.3.34.2`, actual compiler binary SHA-256 `1590ac950a3d627817d09ade5cb60b2115f17a72182a3141e010b4bcc482a0c9`.

Compilation uses `-std=c11 -O2 -Wall -Wextra -Werror -ffreestanding -fno-stack-protector -S`, additionally `-emit-llvm` for IR. Targets are `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu -march=armv8-a -mno-outline-atomics`, and the latter with `-march=armv8.1-a+lse`. The source uses Clang's C11 atomic builtins and an eight-byte `_Atomic(unsigned long long)`; emitted atomic IR has alignment eight. No headers, target standard library, linking, native concurrency, or cross execution are involved. These are C compilation observations, not rustc code-generation observations.

## Findings

### Language access rules survive identical machine instructions

Basis: Rust documentation/source, C++ working-draft specification, derived comparison.

Rust's [atomic memory-model account](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/sync/atomic.rs#L25-L58) follows C++20's race/order rules without consume, translated from objects to accesses. A data race requires overlapping, non-synchronized conflicting accesses, at least one non-atomic; at least one access must write. Failed compare-exchange is not a write. Concurrent atomic and non-atomic reads can be permitted. Non-synchronized atomic pairs must be disjoint, cover exactly the same range and size, or both read. Thus an unsynchronized two-byte atomic write overlapping a one-byte atomic write is forbidden even if the hardware can perform each instruction indivisibly. Synchronized changes of access size are a different case.

The [N4868 draft](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2020/n4868.pdf), dated 2020-10-18, separates per-object modification order from the total order of SC operations, including fences (§6.9.2.2 and §31.4). Release/acquire synchronization requires the specified reads-from/release-sequence relationship. Fence synchronization likewise requires appropriate intervening atomic operations (§31.11); merely putting fences around racy ordinary accesses does not establish it. The draft is contextual evidence for Rust's explicitly documented translation, not a replacement for that translation.

This distinction matters when acquire and relaxed loads become the same x86 instruction, or release and SC stores become the same AArch64 instruction. Their language/IR orders still constrain compiler transformations and surrounding accesses. Machine-code coincidence does not equate the source operations or discharge Rust validity, aliasing, lifetime, alignment, or race obligations.

### What the named hardware models actually constrain

Basis: primary model source; published operational intuition.

In [x86-TSO](https://www.cl.cam.ac.uk/~pes20/weakmemory/cacm.pdf), FIFO store buffers allow a thread to read its own buffered write; MFENCE drains the issuing thread's buffer, while locked instructions have stronger ordering/atomicity. XCHG with memory is implicitly locked. The operational and axiomatic accounts were proved equivalent in HOL4. The paper's intended domain is coherent write-back memory, excluding exceptions, misaligned/mixed-size accesses, non-temporal operations, self-modification, and page-table changes. These qualifications constrain reuse of the model.

The pinned [x86 CAT](https://github.com/herd/herdtools7/blob/9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34/herd/libdir/x86tso.cat) checks same-location consistency, excludes intervening writes for RMW pairs, and requires an acyclic global relation built from preserved write-write/read-memory order, MFENCE, ordering implied by atomic events, external reads-from, from-read, and coherence. Ordinary write-to-read program order is deliberately absent unless additional ordering supplies it. LFENCE/SFENCE are defined in the included fence file but do not enter this CAT's global relation; this is not a complete model of their behavior for all instruction/memory classes.

The pinned [Arm CAT](https://github.com/herd/herdtools7/blob/9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34/herd/libdir/aarch64.cat) is Arm-authored and identifies itself as an application-level formal model. Its current ordered-before closure combines hardware-required ordering with observed-by edges, then checks irreflexivity; separate rules constrain internal visibility and RMW atomicity. The current file also includes translation, instruction-fetch, tag, and maintenance machinery. We inspect the explicit ordinary-memory fragment relevant to these witnesses, without claiming a complete feature configuration or model execution.

In `aarch64hwreqs.cat:122–138`, atomic ordering includes RMW edges. Barrier ordering includes full DMB edges across memory operations, DMB-load edges from preceding reads, DMB-store edges between writes, acquire-to-following-memory and preceding-memory-to-release edges, and release-to-later-full-acquire edges. Consequently an acquire barrier after a store is not interchangeable with a full barrier for store-to-load ordering. `aarch64fences.cat` classifies ISH/ISHLD/ISHST into the full/load/store sets; it also flags shareability arguments as deprecated in this revision. We report the compiler's emitted ISH spellings without extrapolating device-memory or system-scope guarantees.

The instruction/event connection is inspected, not inferred solely from the CAT names. Parser clauses map LDAR/LDXR/LDAXR/LDAPR to distinct variants; `AArch64Sem.ml:2056–2071` maps them to acquire, exclusive, acquire-exclusive, and RCpc-acquire reads. STLR generates release writes; exclusive stores check matching reservation size. LSE acquire/release modes produce XA/XL annotations, while LDADD uses `amo_strict`. `AArch64Annot.ml` distinguishes ordinary, atomic, exclusive, acquire, release, and RCpc-acquire sets. Replacing LDAR by LDAPR, discarding an exclusive reservation, or treating an RMW as two independent ordinary accesses therefore changes semantic obligations.

### Published proof scopes are narrower than compiler correctness

Basis: primary papers and source theorem inspection.

[Mathematizing C++ Concurrency](https://www.cl.cam.ac.uk/~pes20/cpp/popl085ap-sewell.pdf), §5 Theorem 3, proves correctness of a proposed event mapping for defined programs in its C++ model, excluding SC fences, forks, joins, locks, and unlocks. Atomic locations map to single target locations; distinct source locations have disjoint target footprints, and translation preserves required order. The proof is partly HOL4 and partly paper reasoning. It is not a checked verification of Clang or rustc's optimizer, ABI, or current Rust access model.

[Simplifying ARM Concurrency](https://www.cl.cam.ac.uk/~pes20/armv8-mca/armv8-mca-draft.pdf) proves equivalence of the 2018 Flat operational and revised MCA axiomatic models, with a finite, non-mechanized proof over their intersection. Its caveats exclude mixed-size behavior, LDAPR and LSE from that equivalence, and systems aspects. The [errata](https://www.cl.cam.ac.uk/~pes20/armv8-mca/errata.html) correct candidate coherence footprints and exclusive-instruction descriptions. This theorem does not automatically extend to today's richer pinned CAT.

The [IMM paper](https://plv.mpi-sws.org/imm/Podkopaev-al-POPL19_full.pdf), §4.2/Theorem 4.5, establishes target-consistency implying source-consistency for corresponding execution graphs. Its mappings preserve specified dependencies and add a load fence after *strong* RMWs. Its C11/RC11 bridge in §5 covers fragments excluding non-atomic and SC accesses; the text separately discusses extensions and leaves dedicated Arm SC accesses for future work. The source-language Promising theorem cannot be substituted for a Rust theorem merely because instructions resemble its mapping.

The later [pinned Coq artifact](https://github.com/weakmemory/imm/tree/4ca191b072df081dd3a6d9aa755959dc901b1bd0/src/hardware) is inspected separately from the 2019 text. Its actual file is `imm_sToARM.v`, although README retains a historical `immToARM.v` name. `IMM_s_psc_consistent:246–254` assumes finite events plus the section's Arm consistency and RMW/dependency hypotheses, producing an existential SC witness. `IMM_s_consistent:310–328` instead excludes SC fences. `immToTSO.v:897–906` exposes an SC-store-to-SC-load fencing premise. `C11Toimm_s.v` proves an implication between that artifact's consistency predicates. We did not replay their dependency closure or establish that emitted bytes satisfy those hypotheses.

Names themselves are not a correspondence: the artifact's Arm `Q` notation denotes acquire-mode reads and `A` SC-mode reads, whereas the current herd annotation sets use A for full acquire and Q for RCpc acquire. Its location/value labels also do not directly express Rust's byte-range access rules. A bridge needs an explicit mapping, not a shared vocabulary.

### Performed compiler observations

Basis: execution of the installed compiler, inspected IR and assembly.

All seventeen functions compile in all three configurations. The following table lists their relevant operations, omitting returns, register movement, and CAS control flow.

| Source operation | x86-64 observed | Baseline AArch64 observed | AArch64 +LSE observed |
| --- | --- | --- | --- |
| Relaxed/acquire/SC load | MOV / MOV / MOV | LDR / LDAR / LDAR | same |
| Relaxed/release/SC store | MOV / MOV / XCHG | STR / STLR / STLR | same |
| Relaxed fetch-add | LOCK XADD | LDXR, ADD, STXR retry | LDADD |
| AcqRel/SC fetch-add | LOCK XADD | LDAXR, ADD, STLXR retry | LDADDAL |
| Strong CAS, success AcqRel/failure Acquire | LOCK CMPXCHG | LDAXR/STLXR retry; CLREX on mismatch | CASAL |
| Acquire thread fence | no barrier instruction | DMB ISHLD | same |
| Release/AcqRel thread fence | no barrier instruction | DMB ISH | same |
| SC thread fence | LOCK ORL $0, -64(%rsp) | DMB ISH | same |
| SC signal fence | no barrier instruction | no barrier instruction | same |
| Empty volatile asm, memory clobber | no barrier instruction | no barrier instruction | same |
| Explicit hardware-fence asm, memory clobber | MFENCE | DMB ISH | same |

The x86 SC fence is a locked identity operation on stack memory, not an emitted MFENCE. The [primary mapping discussion](https://www.cl.cam.ac.uk/~pes20/cpp/cpp0xmappings.html) records that alternate implementation. That page expressly presents discussion mappings rather than a definitive specification, and warns that incompatible SC mapping conventions can break separately compiled interworking. These observations establish compiler output for the recorded flags, not execution-graph inclusion or conformance of every surrounding program.

The IR retains `monotonic`, `acquire`, `release`, `acq_rel`, and `seq_cst` as requested; CAS retains distinct success/failure orders. Signal fence becomes `fence syncscope("singlethread") seq_cst`; the empty asm retains side effects and a memory clobber. Explicit hardware asm includes both an instruction and that clobber. Thus absence of a barrier opcode does not imply absence of compiler-level ordering information.

The fixed SB relation probe calculates from-read edges and the selected ordering edges for ten cases. Both full fences produce a cycle; deleting either fence removes that cycle. A64 DMB-load after stores and an empty compiler barrier do not supply store-to-load edges. Locked x86 SC stores and A64 STLR/LDAR contribute the relevant ordering. Initial writes and RMW internals are projected away; this computes one necessary ordering check for a fixed candidate, not all named-model consistency conditions or allowed outcomes.

### Compiler-facing assembly effects are another contract

Basis: Rust Reference requirements, Rust API documentation/source, inspected compiler IR, derived implication.

At the pinned [Reference](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/inline-assembly.md#L1104), both `nomem` and `readonly` let the compiler assume that asm performs no interthread synchronization, including fences. A hardware barrier inside an asm block does not make either annotation truthful. `readonly` is not permission to implement a synchronization-only fence merely because it writes no ordinary data.

Rust's `fence` dispatches to ordering-specific atomic-fence intrinsics. `compiler_fence` dispatches to single-thread-fence intrinsics and documents synchronization with signal handlers or analogous same-CPU execution. It emits no machine code, but the documentation explicitly rejects treating it as an unrestricted compiler barrier. Synchronization still needs the specified atomic communication. The compile-only C signal-fence and memory-clobber witnesses therefore remain distinct specimens despite both producing only a return instruction here.

Kraken's inspected `MachineData.load/store` reads or updates one byte-map state; `Effects` carries access permissions, undefined values, and non-memory effects, without a concurrent execution graph. Its default `Effects.All` continues permission requests and rejects non-memory effects. The inspected AArch64 operation syntax/semantics does not supply these atomic/fence operations. Sequential register/memory correctness can support an exclusive-memory fragment, but cannot justify interthread synchronization annotations or the missing graph correspondence. A concurrent adapter needs access sizes/kinds/orders, RMW pairing, interference, reads-from/coherence, fence ordering, language races, and compiler-effect premises connected to the selected instruction semantics.

## Boundaries

- **Performed:** primary-source/model inspection; selected theorem-statement audit; 14 compiler invocations including dispatcher/direct-compiler repetition; 51 pairs and 167 predicates for the direct run; ten explicit relation projections. Dispatcher and direct-compiler function bodies agree.
- **Not performed:** herd7/rmem execution, Coq rebuilding/axiom-closure audit, proof of LLVM optimization correctness, rustc compilation of these witnesses, model-to-real-hardware validation, a complete concurrent Rust asm wrapper proof, or actual rejection of a falsely annotated Rust fence by a semantic checker. The Reference rule rejects that contract semantically; this is not a compiler diagnostic claim.
- **Not established:** equivalence between current Rust and the examined C11/RC11/Promising fragments; transplantation of historical proof results to current CAT; target graph extraction from emitted assembly; a general mixed-width Rust-to-hardware simulation.
- **Outside the observed input class:** atomics other than eight-byte integers, misaligned/overlapping accesses, outline helpers, consume/RCpc mappings, non-temporal or device memory, shareability/topology variants, nontermination/fairness, signal-handler correctness, privileged execution, SIMD/FP, and self-modifying code.
- No concurrent or generated target code was executed. The relation calculation is an owned projection of inspected rules; it is not an upstream model evaluator. The source audit makes no global claim that a stronger bridge or proof does not exist elsewhere.

## Evidence

`source-index.json` identifies 43 source entries: 37 full files verified against Git blob IDs and six explicitly marked excerpts, with preserved-file SHA-256 values and exact revisions/ranges. The package retains CAT include files, event annotation/generation excerpts, selected IMM theorem/definition source and licenses, Rust rules, LLVM documentation, and four Kraken source files with their license. `primary-paper-index.json` records exact paper/draft versions, URLs, and sections; PDF bytes/hashes are not claimed archived.

`support/atomics.c`, `compile.py`, and `check.py` preserve the owned compilation investigation. `support/observed` contains full commands, compiler version, assembly, IR, standard streams, function bodies, and computed checks. `observed-dispatcher` retains the preceding /usr/bin/clang invocation; the main run invokes the hashed compiler directly. Compiler argv and LLVM source-provenance paths are explicitly normalized for publication; `public-path-projection.json` records original/public hashes. Historical producer hashes refer to original observations; the package manifest binds public bytes. Source/program and assembly instruction bytes are unchanged. These paths are not required revalidation locations. `compiler-identities.json` distinguishes the system dispatcher from the compiler binary.

`support/sb_projection.py` and `sb-projection-result.json` retain the ten calculations, with expected values labeled fixtures and cycle results computed by transitive closure. No assertion/panic, compiler diagnostic, or real semantic disagreement occurred in compilation. One evidence-copy validation caught a license terminal-newline change; acquisition provenance records the cause and exact restoration before freeze.

## Revalidation

Run from the package directory, choosing a new output directory:

```sh
python3 support/compile.py --clang /path/to/clang --out support/replay
python3 support/check.py support/replay
python3 support/sb_projection.py support/replayed-sb.json
```

The instruction checks intentionally bind the observed mapping, including the locked-stack SC-fence choice. A compiler choosing another valid mapping requires source/model review rather than declaring language failure. Check IR orders separately from opcode similarity. To advance the concurrent claim, extract actual events for the complete wrapper into a pinned model and prove or check its required consistency/refinement and effect conditions. Replaying the owned probes does not do that work.
