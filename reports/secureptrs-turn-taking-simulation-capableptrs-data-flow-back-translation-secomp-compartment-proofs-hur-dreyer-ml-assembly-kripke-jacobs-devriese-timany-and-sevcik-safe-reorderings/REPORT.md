# Allocation renaming, step reordering and memory exhaustion in mechanized secure-compilation and full-abstraction proofs: SecurePtrs, CapablePtrs, SECOMP, Kripke logical relations, nominal techniques and safe reorderings

## Summary

- **No surveyed development treats memory exhaustion as an observable outcome inside its correctness theorem.**
  - SecurePtrs uses unbounded natural-number block identifiers. Allocation there fails only if the allocating component has no memory at all.
  - SECOMP inherits CompCert's total `Mem.alloc`.
  - Ahmed–Dreyer–Rossberg assume "an infinite set of locations". Hur–Dreyer's assembly has "word and memory sizes [that] are infinite". Jacobs–Devriese–Timany emulate the heap with a natural-number size.
  - The one exception in the semantics is CapablePtrs. Its source semantics is indexed by an *allocation limit* ∇ ("the maximum possible size of the shared heap"), and every cross-boundary trace label carries the shared allocator state `nalloc`. How exhaustion is handled is deferred to its technical report and was not examined.
  - The only finite-resource bound in a mechanized theorem is SECOMP's: trace prefixes must be shorter than 2^64 events, because the back-translation counts events in an `int64`.
  - Basis: source + documentation.
- **Renaming techniques differ in what they rename.**
  - SecurePtrs partitions memory by component, so the context's allocations never shift the component's block identifiers. Its Coq theorem uses only *constant-shift* renamings per component, which the authors list as a limitation.
  - SECOMP uses a single global block counter, so it must relate memories by CompCert injections. There are two of them (left run → recomposed run, right run → recomposed run), with zero offsets, and they are extended to preserve compartment ownership.
  - Hur–Dreyer relate logical and physical heaps through a GC lookup table that must be a bijection on the reachable parts.
  - Nominal techniques give renaming invariance for free only for permutation-equivariant definitions over a countably infinite name supply with finite support.
  - Basis: source + documentation.
- **No surveyed development justifies reordering component and context allocations against each other.**
  - SecurePtrs and SECOMP avoid the question with *turn-taking*: only the executing side's memory is strongly related, and relations are strengthened at calls and returns.
  - Ševčík proves that reorderings of *non-conflicting* accesses and certain eliminations preserve the DRF guarantee. Allocations against one shared budget behave like conflicting accesses to one location, so they fall outside the reorderable class.
  - A toy enumeration finds that swapping two allocations changes the allocating party's outcome in 120 of 204 small (a, b, B) cases.
  - Basis: documentation + derived + execution (toy model).
- **A proof of full abstraction at a single shared allocation budget has five obligations, O1–O5 below.**
  - Every surveyed technique covers O4 (renaming) only under unbounded allocation.
  - None covers O2 (exhaustion is permanent) or O3 (values are irrelevant after exhaustion).
  - O5 (interference between component and context must fault) is covered only in the DRF sense, and only for non-allocation accesses.
  - Basis: derived.

## Applicability

**Subjects and their relation.** This report reads mechanized developments and papers as *techniques* and maps each one to a fixed list of proof obligations.

- Executable artifacts were inspected at:
  - `secure-compilation/SecurePtrs@5b4c34eda0b827469a5c73e434a12c6c87773e04` (default branch `memory-sharing`; README targets Coq 8.12.2–8.14.1 with MathComp, Extensional Structures and Equations);
  - `secure-compilation/SECOMP@cbef9c338d23f40db5054c9a3d6f2b3b873e9204` (default branch `ccs-main`; README: "Rocq 9.1", "based on CompCert 3.12 and its 64-bit RISC-V backend").
- The papers are interpreted through their own text: CapablePtrs, SecurePtrs, SECOMP, Ahmed–Dreyer–Rossberg, Benton–Hur, Hur–Dreyer, Jacobs–Devriese–Timany, Urban, a survey by Pitts, and Ševčík.
- No proof was replayed. No Coq/Rocq installation was available, and neither development's main theorem file can be checked file by file within 60 s and 4 GiB without first building its dependencies. All statements are read from source text.
- Counts of `Admitted.` and `Axiom` are textual. Whether they are in the dependency cone of a main theorem was not examined; `Print Assumptions` was not run.

**The five obligations.** The obligations are those of a full-abstraction proof between a source and a target in which component and context draw from *one* finite allocation budget, and failure to allocate is observable:

| ID | Obligation |
| :-- | :-- |
| O1 | canonical start: initial configurations, including allocator state, are related |
| O2 | permanence of exhaustion: once an allocation fails, the budget stays exhausted in both related runs (or frees are shown to restore equivalently) |
| O3 | insensitivity after exhaustion: once exhausted, observations no longer depend on values that differ between related runs |
| O4 | simulation modulo renaming: related states may differ by a bijection on handles that is extended at each allocation |
| O5 | reordering: interference between component and context is shown to fault, or their allocation steps are shown to commute without changing observations |

The obligation list is this report's own framing for comparison. It is not taken from any surveyed paper.

## Findings

### 1. SecurePtrs: data-flow back-translation and turn-taking simulation

**Memory model** (`Common/Memory.v`, 2,188 lines):

- The abstract interface declares `Parameter alloc : t -> nat -> t * Block.id.` (line 44). It is total, with axioms `next_block_alloc` ("`b = next_block m /\ next_block m' = next_block m + 1`", 133–136) and `alloc_next_block` (138–140).
- The implementation record has `content : NMap block; nextblock : Block.id` (186–190). `alloc` returns `(…, fresh_block)` with `nextblock := (1 + nextblock m)` (259–265).
- `Block.id` is `nat` (`Common/Values.v:10`).
- Whole memory is `NMap ComponentMemory.t`, with one memory and one counter *per component* (1059–1061). `Memory.alloc mem C size : option (t * Pointer.t)` returns `None` only when `mem C` is `None` (1077–1083).
- Pointers are `(Permission.data, C, b, 0)`: the component id is part of the address.

The step rules require a positive size and a successful `Memory.alloc`:

- target `| Alloc:` (`Intermediate/CS.v:428–436`) emits a data-flow event `EAlloc`;
- source `KS_AllocEval` (`Source/CS.v:134–137`) requires `(size > 0)%Z`.

Basis: source.

**Renaming** (`Common/RenamingOption.v`, 1,842 lines):

```text
Definition sigma_shifting_lefttoright_option (b: Block.id) : option Block.id :=
  if b >= metadata_size_lhs
  then Some (b - metadata_size_lhs + metadata_size_rhs)
  else None.                                                    (163–166)
```

- Memory relations are stated per address: `memory_renames_memory_at_shared_addr` (1094ff) requires that loads on each side agree up to `rename_value_option`.
- `addr_shared_so_far` (737–745) is the reachability closure from event arguments over the event's memory snapshot.
- The trace relation is `traces_shift_each_other_option` (1326).
- `uniform_shift n` (1743) instantiates the shifts. The README describes "The +1 block id renaming" as `uniform_shift 0` and `uniform_shift 1`.
- The paper (§7) states: "our RSP theorem in Coq is stated only for a concrete subclass of renaming relations … we exploit this fact by only considering renamings that are constant shifts. We leave for future work the generalization of this subclass."

**Turn-taking relation** (`Intermediate/RecompositionRelCommon.v`, 2,983 lines). `mergeable_internal_states` (484–529) has two cases, depending on whether the recomposed state executes in `p` or in `c'`. For the executing part, `mem_of_part_executing_rel_original_and_recombined` (354–386) requires all three of:

- private addresses shift;
- shared-so-far addresses shift;
- `omap ComponentMemory.next_block (original_mem cid) = omap ComponentMemory.next_block (recombined_mem cid)` (385). That is, allocation counters agree exactly for every component of the executing part.

For the non-executing part, only private addresses are related (388ff). Lemma 5.3 *strengthens* the weak relation to the strong one at interaction events.

**Theorems.**

- `recombination_trace_rel` (`Intermediate/RecompositionRel.v:1538–1545`) concludes: from two runs whose traces shift each other, obtain a recomposed run related by `mergeable_internal_states`.
- `Theorem RSC` (`RSC.v:63–84`) concludes: for every target run of `p_compiled` linked with `Ct`, there exist a source context `Cs` and a source run whose trace satisfies `traces_shift_each_other_option size_meta size_meta' t t'`.

**Axioms** (README): whole-program compiler correctness (`forward_simulation_star`, `backward_simulation_star`), `well_formed_compilable`, `separate_compilation`, `compiler_preserves_non_leakage_of_private_pointers`, plus `proof_irrelevance`, `functional_extensionality_dep` and `classic`.

**Size.** "3k lines of specifications and 29k lines of proof" for back-translation and recomposition, against 2.7k lines total in the predecessor without memory sharing (paper). Measured: 55 `.v` files totalling 2,562,850 bytes. `Source/Definability.v` alone is 16,234 lines and `RecompositionRelLockstepSim.v` is 4,861.

**Allocation assumptions (derived).**

1. Each component has its own counter, so the context's allocation volume cannot change the component's block ids. This is why exact `next_block` equality is maintainable.
2. Block ids are unbounded `nat` and allocation is total.
3. The renaming is a fixed shift (metadata blocks), not a growing bijection.

Under a single shared budget, assumption 1 fails first. The `next_block` conjunct would have to become a joint statement about the budget consumed by both parties.

### 2. CapablePtrs: pointers as capabilities, TrICL

Source: CSF 2021 paper text; proofs in a technical report not examined.

- **Languages.** The source ImpMod has state `⟨Mem, Φ, pc, stk, nalloc⟩`, where `nalloc` is "the next-free-address". "The space for dynamic memory allocation (i.e., the heap) is also shared by all the program modules." Its semantics "use[s] the judgment → … indexed with … an allocation limit ∇. The allocation limit (∇) is the maximum possible size of the shared heap." The target CHERIExp state also contains `nalloc`.
- **Traces.** "Trace labels λ (of both our languages) have the following forms: λ ::= τ | ✓ | ret? Mem, nalloc | ret! Mem, nalloc | call(fid) v ? Mem, nalloc | call(fid) v ! Mem, nalloc". The allocator state is therefore part of every cross-boundary observation.
- **Equivalence.** Contextual equivalence is defined by termination: `p1 ≃ctx p2 ≝ ∀C. C[p1]⇓ ⟺ C[p2]⇓` (Definition 1). Full abstraction is preservation plus reflection (Definition 2).
- **Technique.** "a new 3-way simulation called TrICL", which "reuses the whole-program compiler correctness relation for full abstraction". The words "renaming", "bijection" and "injection" do not occur in the paper text, and no proof assistant is named.
- **Porting overhead** (Table I): zlib 130 of 11,255 lines altered (1.15%), LibYAML 114 of 12,762 (0.89%), GNU-barcode 164 of 4,657 (3.5%), libpng 51 of 33,029 (0.15%).

Derived reading: a single shared `nalloc` that is visible on traces means the context can observe the component's allocation volume, and vice versa. CapablePtrs is therefore the only surveyed development whose *observations* already include the shared allocator. Whether ∇ is reached in any proof case is unknown here.

### 3. SECOMP: injections extended to compartments

**Memory.** SECOMP's `common/Memory.v` (7,636 lines) adds `mem_compartments: PMap.t (compartment)` (line 62) to CompCert's `mem'`. `Program Definition alloc (m: mem) (c: compartment) (lo hi: Z)` (491–501) always returns `(…, m.(nextblock))` with `Pos.succ m.(nextblock)`. There is one global, unbounded counter.

**Injections.** `Record mem_inj` (4011ff) adds `mi_access: … f b1 = Some(b2, delta) -> perm m1 b1 ofs k p -> Mem.block_compartment m1 b1 = Mem.block_compartment m2 b2` (4019). Recomposition's `Record mem_rel` (`security/Recomposition.v:675–715`) requires:

- `partial_mem_inject: Mem.inject j m1 m2` (678);
- `delta_zero: mem_delta_zero j` (680): injections rename blocks without offset;
- `meminj_injective`;
- `image_same_domain` (712): the image lands on side δ or on global definitions.

`Lemma simulation` (9852) instantiates a three-way simulation diagram with metadata `(meminj * meminj)`: one injection from each original run into the recomposed run. `strong_equivalence` (756) relates the executing side; `weak_equivalence` (782) relates the other side.

`security/MemoryWeak.v` defines `mem_winj` (34–50) and `winject'` (553–573): injections *without* the contents clause, which relate permissions and ownership only.

**Back-translation of memory changes.** `security/MemoryDelta.v:163` defines `mem_delta_alloc := (compartment * Z * Z)`, which records no block id. `mem_delta_apply_alloc` (216–221) replays it as `Some (fst (Mem.alloc m cp lo hi))`. Fresh ids in the replay can differ from the original, and the injection absorbs the difference.

**Limits stated by the authors.**

- "we assume that compartments can only communicate via scalar values, but cannot pass each other pointers to share memory". Passing pointers "would require recording these pointers on the trace, which would significantly complicate back-translation, recomposition, and if also done for pointers to dynamically allocated memory also compiler correctness".
- The paper contrasts its approach with SecurePtrs: "we do not rely on maintaining the invariant that the memories are related by a memory renaming (or a memory injection)" *for the back-translation*. Only the global-buffer parts are related.
- "Because we use a finite, int64 counter to track how many events have been produced, we must limit the length of the (non-informative) trace prefix to 2^64 events." In code, `Theorem backtranslation_proof` (`security/BacktranslationProof2.v:1435–1443`) has the premise `(Z.of_nat (length tr) < Int64.modulus)`.
- Assumption 1 (the back-translation compiles), justified as "machine words being finite and other such finite resources", is *tested*, not proved: "more than 100k pairs of generated environments and traces with up to 880 events and close to 400 events on average … traces of more than 150k events also succeeded … over 16M Icall and Ireturn, 7M Isys and 500M delta_storev instances".
- Theorem 8.1 holds "for all trace prefixes m such that |m| ≤ MAX_TRACE_LENGTH". The top-level proof "is not yet integrated" with the step proofs (paper and README).

**State at the pin** (measured with `grep`):

- `security/RSC.v` (198 lines) declares 9 `Axiom`s (lines 63–133: `backtranslation`, `backtranslation_correct`, `backtranslation_compiles`, `backtranslation_pol`, `forward_correctness`, `recomposition`, `backward_correctness`, `blame`, `c_program_blame`) and 4 `Admitted` lemmas. `Theorem RSC` is at 143–150.
- `Admitted.` counts:
  - `Recomposition.v` 0 (10,147 lines);
  - `MemoryDelta.v` 0;
  - `BacktranslationProof.v` 0;
  - `Backtranslation.v` 3 (the three `Next Obligation`s of `gen_program`, 576–581);
  - `BacktranslationProof2.v` 1 (`step_fix_fix`, comment `TODO: FIXME`, 1242–1249);
  - `MemoryWeak.v` 3 (`drop_mapped_winj`, `mem_inj_implies_mem_winj`, `mem_winj_to_mem_inj`).
- The README says the back-translation proof lives on branch `ccs-backtranslation` and "is complete". These counts are for `ccs-main` only.

**Size (paper).** "SECOMP adds ∼43k LoC on top of CompCert". The CompCert extensions are about 7k LoC of specs and 11k of proofs (+7.2% and +22.3%). Back-translation is about 5k + 6k, recomposition about 1k + 8k, blame about 1k + 4k.

### 4. Kripke logical relations: worlds, location relations, step indices

| Work | World structure | Location relation | Step indexing and allocation | What the back-translation or relation needs from the target | Mechanized |
| :-- | :-- | :-- | :-- | :-- | :-- |
| Ahmed–Dreyer–Rossberg 2009 | separating conjunction of *islands*; each island has *populations* and *laws* that let a relational interpretation grow with local state | "our worlds have no specialized machinery for reasoning about visible locations": a reference adds an island `wref(k, ρ, τ, l1, l2)` relating `(l1, l2)` | "We assume an infinite set of locations Loc"; extension with a fresh island "is sound here precisely because the new island is (due to freshness of allocation) separate from the others" | n/a (equivalence within one language) | no proof assistant named |
| Benton–Hur 2009 | none (pure source); relations between denotations and SECD code | none for source state; low-level "predicate on low-level heaps, values or code" | biorthogonality (⊤⊤-closure over observing contexts) + step indices | none (compiler correctness, not full abstraction) | "formalized in the Coq proof assistant" |
| Hur–Dreyer 2011 | possible worlds as state transition systems (after Dreyer et al.) | logical memory with a lookup table; M represents Φ "only if M's lookup table describes a bijection between the reachable portions of M and Φ"; GC may mark unreachable logical pointers dead | LOW is "idealized … its word and memory sizes are infinite"; the allocator spec may perform a GC | a runtime-system specification: allocation returns a fresh block and preserves reachable data | companion technical appendix; no own mechanization stated |
| Jacobs–Devriese–Timany 2022 | Iris logical relation defining a semantically typed intermediate language λ⊨ | back-translated heap "encode[d] … by a right-nested cartesian product with all the allocated values so far, together with a natural number that represents its size" | Iris later modality (⊲) for recursion | ST computations are back-translated to state-passing pure functions `S → (S × a)`; the heap type cannot be syntactic because "these heaps grow over time" | "fully formalized in the Coq proof assistant using the Iris framework" |

**Would observable exhaustion break an assumption? (derived)**

- *ADR.* Yes. World extension at allocation presumes both sides obtain fresh locations. If one side fails while the other succeeds, no island can be added, and the expression relation must relate a value to a failure.
- *Benton–Hur.* The biorthogonal closure is parametric in the observation (termination). Making exhaustion observable means changing the pole, and the adequacy proof would need to be redone. The step-index structure is unaffected.
- *Hur–Dreyer.* Yes. The allocator specification promises a fresh block, so an infinite memory is assumed explicitly. A bounded LOW heap whose bound differs from HIGH's breaks the lookup-table bijection at the first asymmetric failure.
- *JDT.* The emulation stores the heap size as a natural number and the pure source has no bound. If the target ST heap were bounded, the back-translated context would need to emulate failure at exactly the same allocation count. That is possible in principle, because the size is tracked, but it is not in the development.

### 5. Nominal techniques

- **Urban 2008** (abstract, JAR 40(4):327–356): an Isabelle/HOL formalisation of λ-terms through "an inductive set that is bijective with the alpha-equated lambda-terms". It provides "a structural induction principle that requires to prove the lambda-case for fresh binders only" and a recursion combinator adapted from Pitts. "The main technical novelty … is that it is compatible with the axiom of choice." Basis: documentation (abstract only; full text not examined).
- **Pitts 2016 survey** (SIGLOG News 3(1):57–72).
  - The setting is "the set of all finite permutations of a fixed, countably infinite set A". Morphisms that preserve the permutation action are "equivariant".
  - An atom is fresh for x "if x is supported by some finite set of atoms A ⊆ 𝔸 with a ∉ A".
  - The survey points to Urban and Berghofer's Nominal package as evidence that the formal recursion and induction principles fit informal practice.

**What is automatic, and under which conditions (derived from the survey's definitions).** Invariance under renaming holds for any construction that is equivariant: built only from permutation-respecting operations. Freshness can always be chosen when supports are finite and the atom set is infinite. Both conditions fail for a single finite budget:

- handles drawn from a finite pool make "pick a fresh atom" partial;
- allocation in numeric order (as in SECOMP's `Pos.succ` or SecurePtrs' `1 + nextblock`) is equivariant only if no observation can compare or count handles.

Nominal techniques therefore discharge O4 for permutation-invariant observations, and say nothing about O2 or O3.

### 6. Ševčík: safe reorderings and eliminations for data-race-free programs

- **Reorderable actions.** "a is reorderable with b if either (i) a is a non-volatile memory access, and b is a non-conflicting non-volatile memory access, or an acquire action, or an external action; or (ii) b is a non-volatile memory access, and a is a non-conflicting non-volatile memory access, or a release, or an external action."
- **Reordering of a traceset.** Every transformed trace is a permutation of an original trace that swaps only reorderable actions, and every prefix of the permuted trace yields a trace of the original program.
- **Results.**
  - Theorem 1 (semantic elimination): "Let traceset T′ be an elimination of a data free traceset T. Then T′ is data race free and any execution of T′ has the same behaviour as some execution of T."
  - Theorem 2 is the same statement for reordering.
  - Theorems 3 and 4 lift both to syntactic transformations of a simple imperative language.
  - Out-of-thin-air values are excluded for arbitrary programs.
- **Proof structure.**
  - Elimination uses an *unelimination* function that maps transformed interleavings back to original ones and preserves happens-before.
  - "Since the reordering untransformation does not preserve happens-before order in general, we cannot use the same direct proof … Instead, we prove the safety by induction on the size of the interleaving of the transformed program", using an *unordering* function.
  - Racy programs get no behaviour-preservation guarantee: "the DRF guarantee leaves the behaviours of programs with races unspecified". The behaviour theorems are conditional on DRF of the *original* program.
  - Introducing irrelevant reads can invalidate otherwise DRF-safe optimizations.
  - "we mechanised the definitions and difficult parts of the semantic elimination safety proof … in the Isabelle/HOL proof assistant. The mechanisation has about ten thousand lines of proof script."

**Mapping to allocation (derived).** Model the shared budget as one memory location that every allocation reads and writes. Any two allocations then *conflict*, so no theorem above licenses swapping them. Under turn-taking, cross-party control transfer is synchronization, so every cross-party pair of allocations is ordered by happens-before, and DRF holds for the budget location. Ševčík's results then permit moving an allocation only past non-conflicting, non-allocating accesses within one party's turn. That supplies part of O5, the part that keeps allocation order fixed. It does not supply the cross-party commutation that a single-budget proof would need when component and context allocate in different orders.

### 7. Toy probe: allocation discipline versus renaming and reordering

Source: `support/alloc_discipline_toy_probe.py`, Python standard library only; output in `support/alloc_discipline_toy_probe.out`. Basis: execution (toy model, not any surveyed development).

The component's script allocates [1, 2, 1] cells on its three turns. The context allocates 0–3 cells per turn, giving 64 contexts. The component observes its own handles and success bits.

| Discipline | Distinct observations | Modulo bijective renaming |
| :-- | --: | --: |
| per-party unbounded counters (shape of SecurePtrs) | 1 | 1 |
| one global unbounded counter (shape of SECOMP and CompCert) | 64 | 1 |
| one global counter, budget B = 3 / 4 / 5 / 6 / 8 | 7 / 11 / 17 / 25 / 45 | 4 / 4 / 4 / 4 / 3 |

Reordering check: over 204 triples 1 ≤ a, b ≤ B ≤ 8, the order of a component allocation (a cells) and a context allocation (b cells) changes the component's outcome in 120 triples (58.8%). That happens exactly when a ≤ B, b ≤ B and a + b > B.

Reading:

- Per-party counters need no cross-context renaming.
- A global counter needs renaming, and renaming suffices.
- A shared budget leaves 3–4 classes that renaming cannot merge, so O4 alone cannot discharge the obligation.

### 8. Obligation coverage matrix

| Technique | O1 start | O2 permanence | O3 post-exhaustion | O4 renaming | O5 reordering |
| :-- | :-- | :-- | :-- | :-- | :-- |
| SecurePtrs turn-taking + shift renaming | initial states related with metadata shift (`match_initial_states`) | n/a: allocation total | n/a | per-component constant shifts only | avoided: only one side executes; strengthening at borders |
| CapablePtrs TrICL | not examined | not examined (∇ in semantics) | not examined | not stated in paper | not examined |
| SECOMP injections + three-way simulation | `meminj_preserves_globals` for both injections | n/a: `Mem.alloc` total | n/a | two zero-offset, compartment-preserving injections | avoided: strong/weak equivalence swap at events |
| ADR islands | trivial | n/a: infinite `Loc` | n/a | location pairs as islands; fresh-island extension | n/a (sequential) |
| Benton–Hur biorthogonality | n/a | n/a | the pole fixes what is observable | n/a | n/a |
| Hur–Dreyer STS worlds + GC table | runtime invariants at entry | n/a: infinite memory | n/a | lookup-table bijection on reachable heap, survives GC | n/a (sequential) |
| JDT semantically typed back-translation | empty emulated heap | n/a | n/a | location ↔ index in the emulated heap | n/a |
| Nominal techniques | n/a | no | no | automatic for equivariant constructions over infinite atoms | no |
| Ševčík | n/a | no | no | no | DRF-preserving reordering of non-conflicting accesses; allocations against one budget conflict |

### 9. Allocation-assumption register

| Development | Assumption | Location |
| :-- | :-- | :-- |
| SecurePtrs | block ids are `nat` | `Common/Values.v:10` |
| SecurePtrs | component allocation is total; ids are consecutive | `Common/Memory.v:44, 133–140, 259–265` |
| SecurePtrs | memory is partitioned by component; whole-memory `alloc` fails only for an absent component | `Common/Memory.v:1059–1083` |
| SecurePtrs | allocation counters are equal for the executing part | `Intermediate/RecompositionRelCommon.v:383–386` |
| SecurePtrs | renaming is a constant shift | `Common/RenamingOption.v:163–171`; paper §7 |
| SECOMP | one global counter; `alloc` total | `common/Memory.v:491–501` |
| SECOMP | allocation deltas carry no block id | `security/MemoryDelta.v:163, 216–221` |
| SECOMP | injections preserve compartments | `common/Memory.v:4019` |
| SECOMP | trace prefix shorter than 2^64 | `security/BacktranslationProof2.v:1440` |
| SECOMP | no pointer passing between compartments | paper (compartment model section) |
| CapablePtrs | shared heap with limit ∇; `nalloc` on traces | paper (ImpMod semantics; trace labels) |
| ADR | infinite set of locations | paper (definition of Fµ!) |
| Hur–Dreyer | infinite word and memory size | paper (definition of LOW) |
| JDT | emulated heap with natural-number size | paper §5.1 |

### 10. Performance and resource footprint (L1–L6)

| Level | Quantity | Value | Basis |
| :-- | :-- | :-- | :-- |
| L1 | SecurePtrs back-translation + recomposition | 3k spec + 29k proof lines (predecessor without sharing: 2.7k total) | cited |
| L1 | SecurePtrs repository size | 55 `.v` files, 2,562,850 bytes; `Definability.v` 16,234 lines | measured |
| L1 | SECOMP additions | ∼43k LoC; CompCert extension +7.2% specs, +22.3% proofs | cited |
| L1 | SECOMP repository size | 300 `.v` files, 10,911,881 bytes; `security/` 15 files, 1,485,117 bytes; `Recomposition.v` 10,147 lines | measured |
| L1 | Ševčík elimination proof | about 10k lines of Isabelle | cited |
| L1 | CapablePtrs porting effort | 0.15%–3.5% of lines altered (four C libraries) | cited |
| L2 | build time of Coq/Rocq or CompCert | not measured (no toolchain) | — |
| L3 | elaboration and checking time of main theorem files | not measured | — |
| L4 | CapablePtrs generated-code overhead | "roughly proportional to the number of cross-compilation-unit function calls" (no number extracted) | cited |
| L4 | SECOMP capability backend overhead | not measured | — |
| L5 | proof replay time | not measured | — |
| L5 | SECOMP back-translation testing volume | >100k environment/trace pairs; up to 880 events; >150k-event single tests | cited |
| L6 | toy probe | 10,348 KB peak RSS, 0.01 s (8 CPUs) | measured |
| L6 | `.vo` sizes, checker RSS | not measured | — |

### 11. Comprehensibility and simplicity (C1, C2)

**C1.** The turn-taking invariant needs four relations:

- strong relation on the executing part (private + shared + counters);
- weak relation on the other part (private only);
- trace shift;
- strengthening at borders.

SECOMP adds two injections plus weak injections. A reader must track which side is "executing" at every step: nonlocal reasoning that SecurePtrs's README makes auditable through a definition index. CapablePtrs's labels expose `nalloc`, which makes allocator effects visible in counterexample traces but enlarges every observation.

**C2.** Three mechanisms enforce one invariant ("related runs agree up to names"):

- shifts (SecurePtrs);
- injections (SECOMP, CompCert);
- bijection tables (Hur–Dreyer, JDT's index map).

A partial bijection extended at each allocation subsumes shifts and zero-offset injections (derived). It still does not absorb a shared budget, which the toy probe shows needs state *outside* the renaming: the consumed budget, related as an equality or as a joint invariant. The minimal extension suggested by the evidence is to carry the shared allocator state as an explicit, related component of every world or simulation state. CapablePtrs already places it on traces. That moves O2 and O3 into the relation instead of hiding them in adapters.

### 12. Validation (V1–V4)

| Axis | Evidence |
| :-- | :-- |
| V1 specification adequacy | SECOMP's QCheck testing of Assumption 1 (cited volumes); SecurePtrs keeps compiler correctness as axioms, so adequacy of those axioms is unvalidated in-repo (README) |
| V2 compiler and checker fuzzing | SECOMP compiles generated back-translations with CompCert (differential in spirit); no fuzzing of checkers found; not examined further |
| V3 concurrency validation | Ševčík's proofs are the only concurrency content; no model checking found |
| V4 human comprehension | none found |

## Boundaries

- **Not examined.**
  - Proof replay of either repository, and `Print Assumptions` for `RSC`, `recombination_trace_rel`, `simulation` or `backtranslation_proof`.
  - SECOMP branch `ccs-backtranslation`.
  - The CapablePtrs technical report, including how ∇ exhaustion is handled and whether TrICL renames.
  - The full text of Urban 2008; only its abstract and the Pitts survey were read.
  - Pilsner, CompCertM and other parametric-bisimulation or open-module developments.
  - The SECOMP capability backend.
- **Unknown.** Whether any `Admitted` at the SECOMP pin lies under Theorem RSC. Since RSC is axiomatized against its step proofs, the theorem is not end-to-end mechanized regardless.
- **Known not to apply.** The toy probe's counts depend on its arbitrary script and parameters. It does not show that any surveyed proof fails; it shows only that renaming cannot merge outcomes that differ in success bits.
- **Unsupported claims to avoid.**
  - "SecurePtrs handles arbitrary renamings": its Coq theorem uses constant shifts.
  - "SECOMP's security theorem is fully mechanized": RSC.v axiomatizes back-translation, recomposition, blame and compiler correctness.
  - "CapablePtrs proves full abstraction with observable OOM": ∇ appears in the semantics, but exhaustion handling was not read.
  - "Ševčík licenses reordering allocations": allocations against a shared budget conflict.
- **Interpretation risk.** O1–O5 are this report's framing. Another decomposition could assign techniques differently.

## Evidence

All evidence was gathered on 2026-11-21 (UTC).

- **`secure-compilation/SecurePtrs@5b4c34eda0b827469a5c73e434a12c6c87773e04`:**
  - `README.md` (definition index, axioms, versions);
  - `Common/Memory.v:38–175, 181–265, 1059–1100`;
  - `Common/Values.v:9–13`;
  - `Common/RenamingOption.v:76–171, 737–745, 1081–1130, 1314–1350, 1741–1750`;
  - `Intermediate/RecompositionRelCommon.v:354–410, 484–529`;
  - `Intermediate/RecompositionRel.v:1538–1545`;
  - `Intermediate/CS.v:428–436`;
  - `Source/CS.v:131–137`;
  - `RSC.v:47–84, 503`.
- **`secure-compilation/SECOMP@cbef9c338d23f40db5054c9a3d6f2b3b873e9204`:**
  - `README.md` (branches, completeness statements, toolchain);
  - `common/Memory.v:58–71, 491–501, 4011–4040`;
  - `security/Recomposition.v:675–715, 756–800, 9852–9870`;
  - `security/MemoryWeak.v:34–50, 553–574`;
  - `security/MemoryDelta.v:160–175, 216–221`;
  - `security/Backtranslation.v:565–581`;
  - `security/BacktranslationProof2.v:1242–1252, 1435–1451`;
  - `security/RSC.v:1–198`.

  Counts were obtained with `grep -c "Admitted\."` and `grep -c "^\s*Axiom"` per file.
- **Repository file lists and sizes:** GitHub git-trees API, recursive, at the pins.
- **Literature.** DOIs were verified against Crossref metadata for title, authors, venue and pages:
  - 10.1109/CSF51468.2021.00036 (El-Korashy, Tsampas, Patrignani, Devriese, Garg, Piessens; CSF 2021, pp. 1–16);
  - 10.1109/CSF54842.2022.9919680 (El-Korashy, Blanco, Thibault, Durier, Garg, Hriţcu; CSF 2022, pp. 64–79);
  - 10.1145/3658644.3670288 (Thibault, Blanco, Lee, Argo, Azevedo de Amorim, Georges, Hriţcu, Tolmach; CCS 2024, pp. 1061–1075);
  - 10.1145/1480881.1480925 (Ahmed, Dreyer, Rossberg; POPL 2009, pp. 340–353);
  - 10.1145/1596550.1596567 (Benton, Hur; ICFP 2009, pp. 97–108);
  - 10.1145/1926385.1926402 (Hur, Dreyer; POPL 2011, pp. 133–146);
  - 10.1145/3527326 (Jacobs, Devriese, Timany; PACMPL 6(OOPSLA1), pp. 1–27);
  - 10.1007/s10817-008-9097-2 (Urban; JAR 40(4), pp. 327–356);
  - 10.1145/2893582.2893594 (Pitts; ACM SIGLOG News 3(1), pp. 57–72);
  - 10.1145/1993498.1993534 (Ševčík; PLDI 2011, pp. 306–316).

  arXiv records were checked for 2110.01439 (v3, 3 Jun 2022), 2005.05944 (v2, 4 May 2021) and 2401.16277 (title page of the arXiv PDF). Quotations come from author-hosted PDFs and the arXiv PDF of SECOMP, as text-extracted on the observation date.
- **Execution.** `python3 support/alloc_discipline_toy_probe.py`, pinned to 8 CPUs with a 60 s limit. The output is preserved verbatim in `support/alloc_discipline_toy_probe.out`.

## Revalidation

- **SecurePtrs.** Check that `Common/Memory.v` still declares `alloc : t -> nat -> t * Block.id`, and that `RecompositionRelCommon.v` still has the `next_block` conjunct. If renamings beyond shifts are added, search `RenamingOption.v` for definitions not built from `sigma_shifting_*`.
- **SECOMP.**
  - Recount `Admitted.` and `Axiom` in `security/*.v`.
  - Check whether `security/RSC.v` still declares `Axiom recomposition` and `Axiom backtranslation_correct`. If they become theorems, the integration gap closed.
  - Check the `Int64.modulus` premise of `backtranslation_proof`.
  - With a Rocq 9.1 toolchain, run `make proof` and `Print Assumptions RSC`. This exceeds the 60 s bound used here.
- **Exhaustion.** Grep each development's memory file for an allocation that can return `None` or fail because of size. Today only SecurePtrs' absent-component case returns `None`.
- **Toy probe.** `python3 support/alloc_discipline_toy_probe.py` reproduces the table in under one second.
