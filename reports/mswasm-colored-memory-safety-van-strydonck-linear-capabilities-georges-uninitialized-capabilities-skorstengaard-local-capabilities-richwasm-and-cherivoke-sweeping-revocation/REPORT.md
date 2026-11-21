# Retained access to released storage: colored memory safety (MSWasm), linear, local, uninitialized and directed capabilities, RichWasm typing, and CHERI sweeping revocation

## Summary

When an untrusted context keeps a handle to storage that a component releases and uses it after the storage is reused, the examined systems split into four fates:

- **Excluded.** Linear capabilities (StkTokens; Van Strydonck–Piessens–Devriese) make a second live copy impossible. RichWasm's linear `Cap`/`Ref` is consumed by `free`, so a retained copyable pointer can never be dereferenced. Directed capabilities (Le Temps des Cerises) can be stored only through write-local capabilities, at addresses at or above their own readable range. They can therefore be stashed only in the same or younger stack frames, and uninitialized capabilities make those frames unreadable after return.
- **Faults.** In MSWasm's formal semantics a handle carries a segment id. Every load and store requires `nid ∈ A.allocated`, and ids (and the colors they map to) are never reused, so a stale handle traps. Uninitialized (U) stack capabilities trap on reads at or above their cursor.
- **Revoked.** Local capabilities are revoked by clearing the unused stack in software at every boundary crossing (Skorstengaard–Devriese–Birkedal). CHERIvoke and Cornucopia hold freed memory in quarantine and clear the tags of all capabilities into it before reuse. Until the sweep, the dangling capability still reaches the quarantined (not reused) memory: the guarantee is *no use after reallocation*, not no use after free.
- **Permitted.** MSWasm's baggy-bounds backend and its CHERI backend enforce no temporal safety. In the GC'd language of Swasey–Garg–Dreyer storage is never released while reachable; access is revocable only by program patterns such as the caretaker.

Proof strength differs: full abstraction (StkTokens; Van Strydonck et al.; Le Temps des Cerises, mechanized), robust trace safety (MSWasm; Swasey–Garg–Dreyer), logical relations with robust-safety examples (local and uninitialized capabilities), and type safety (RichWasm). Of the artifacts checked here, the two Cerise developments have 0 `Admitted.`/`admit.`/`Axiom`. RichWasm has 0 admits but 5 global `Axiom`s and 29 `Parameter`s of an abstract `Memory` module type that no module instantiates. CHERIvoke/Cornucopia guarantees are argued, not proved.

Measured costs use different baselines and are not comparable (details under Performance levels). MSWasm in software costs 21.4% (spatial), 52.2% (plus temporal) and 197.5% (plus handle integrity) over Wasm on PolyBenchC; its CHERI backend costs 51.7%, without temporal safety. CHERIvoke averages 4.7% runtime with a 25% heap quarantine, with capabilities simulated on x86. Cornucopia averages under 2% (worst 8.9%) on a CHERI FPGA. Nothing has been measured for linear, local, uninitialized or directed capabilities, or for RichWasm.

## Applicability

The report covers these pinned upstream revisions (observed 2026-11-21):

| Repository | Revision | What was examined |
|---|---|---|
| `PLSysSec/ms-wasm` | `b7cd1a0b2d875b317a2b637d7b4d3c764216e758` | Its single file, `README.md` |
| `PLSysSec/mswasm-graal` | `9668dbbdbc14a325d60277477ffaac99484388cc` | The MSWasm segment memory and opcodes |
| `logsem/cerise-stack-monotone` | `dff1909f6abc6de99c28d8f12e903b98dd76fb41` | The artifact of *Le temps des cerises*, OOPSLA 2022 |
| `logsem/cerise-stack` | `f68111362730aff998798d63c7d6a0a7176eff44` | The artifact of Georges et al., POPL 2021. Its `CITATION.cff` names that paper, DOI 10.1145/3434287 |
| `RichWasm/RichWasm-artifact` | `62c4bbcd67f4613304b3ae5bc6a85a901c2e9c8d` | The Coq theories |
| `CTSRD-CHERI/cheribsd` | `88f39900c32928d807dba245fba138808c666f34` | `sys/kern/kern_cheri_revoke.c` only |

The papers are identified by DOI in `REPORT.json`. Text read: for MSWasm, the published POPL version, plus arXiv 2208.13583v3 (revised 16 Apr 2026), which omits the CHERI backend and Evan Johnson; statements here come from the published version. For Van Strydonck et al., the authors' JFP extended-version preprint (30 March 2021), which says it extends the ICFP 2019 paper; section numbers refer to it. For local capabilities, the authors' TOPLAS-version preprint, not the ESOP 2018 text. For StkTokens, CHERIvoke, Cornucopia, Swasey et al. and RichWasm, the authors' PDFs. The Georges et al. POPL 2021 text could not be fetched; its claims come from the mechanization and from Georges' Aarhus PhD dissertation, which quotes it.

The subjects relate as alternative mechanisms for one question: whether a retained handle can be used after release. Rows of the cross-system table are independent; no subject was linked to another. The MSWasm and Graal findings are specific to the pinned revisions. The rWasm and MSWasm-CHERI backends were not inspected, so statements about them come from the paper.

## Findings

### Cross-system table

Abbreviations: FA = full abstraction; LR = logical relation; RS = robust safety.

| System | Machine / language | Discipline on context | Property proved | Memory and allocation assumptions | Fate of retained handle to released storage | Measured enforcement cost (cited) | Mechanization |
|---|---|---|---|---|---|---|---|
| MSWasm formal model (POPL'23) | Wasm + segment memory + 5-field handles | Runtime checks on every handle use; the context is any valid attacker module (`M ⊢ C : attacker`) | Robust memory safety: a trace property checked by a color monitor (Thm 1). C compiler: memory-safety preservation and trap-at-first-violation (Thms 2–3) | Abstract allocator; ids and colors fresh and never reused; fixed-length segment memory | **Faults** (`nid ∈ A.allocated` premise fails, so the access traps) | See next row | None found; proofs deferred to a technical report (not examined) |
| MSWasm implementations | rWasm AOT; GraalWasm JIT; rWasm→CHERI-C | Runtime | None (guided by the model) | rWasm uses a sentinel to prevent index reuse; Graal uses random keys | rWasm ST/STH: **faults**. rWasm S (baggy bounds): **permitted**. CHERI backend: **permitted** (no temporal safety). Graal ST: **faults** unless the freed key is redrawn (see below) | Over plain Wasm: 21.4% (S), 52.2% (ST), 197.5% (STH), 42.3% (Graal ST). CHERI: 51.7% over native pure-capability CHERI on Morello | n/a |
| Van Strydonck–Piessens–Devriese (ICFP'19) | Verified C-like source; target with hardware linear capabilities | Arbitrary well-formed target components; hardware non-duplication plus compiler-inserted boundary checks | FA of the compiler | `malloc` returns fresh, never-reused locations; no `free`; separation-logic rules assumed as axioms | **Excluded** (no alias of a linear capability can exist) | Not measured | None (paper proofs; mechanizing named as possible future work) |
| Local capabilities (ESOP'18 / TOPLAS'20) | Capability machine with local and write-local capabilities | Arbitrary code; hardware locality rules plus a calling convention | LR; FTLR (Thm 4.4); robust-safety examples | Infinite address space, unbounded integers | **Revoked**: retained local capabilities can sit only in registers or write-local stack, which is cleared before each adversary call or return | Not measured; clearing is proportional to unused stack per boundary crossing (§9) | None (paper) |
| StkTokens (POPL'19) | LCM: linear capabilities, seals, `split`/`splice` | Arbitrary code; hardware linearity | FA of the identity embedding of the overlay oLCM into LCM (Thm 1) for reasonable, well-formed components | Infinite address space, unbounded integers | **Excluded** (stack capability is linear; the caller re-splices it on return) | Not measured; "a constant and limited amount of checks on every boundary crossing" (§6.2) | None (technical report) |
| Uninitialized capabilities (POPL'21) | Cerise: local capabilities plus `URW…URWLX` | Unknown code with no capabilities in its initial memory (`is_initial_memory`: `Forall (λ w, is_cap w = false) adv_val`); hardware thereafter | LR; FTLR (Thm 6.1); adequacy of the awkward example (Thm 6.3) | Finite: `MemNum = 2000000` | **Faults**: stale frame contents above the cursor are unreadable (`LoadU` needs `a' < a`) | Not measured | Coq + Iris, `logsem/cerise-stack`; 0 holes in 73 files |
| Directed capabilities (OOPSLA'22) | Cerise: `Global`/`Local`/`Directed` × 12 permissions | Well-formed components (all words global and non-write-local, own segment only, disjoint from the stack); then hardware | FA from the overlay to the base machine (Thm 6.1, `compile_fully_abstract`) | Finite: `MemNum = 2000000`; stack between `b_stk` and `e_stk` | Overlay: **faults** (`Failed` once the frame is gone). Base: **excluded** (store rule plus U capabilities) | Not measured | Coq 8.12 + Iris 3.3; 0 holes in 141 files |
| RichWasm (PLDI'24) | Typed IL over Wasm: linear + GC'd memories | Context must typecheck as RichWasm (static) | Type safety (progress, preservation, `Soundness` including GC steps) | Abstract `Memory` module type; `free` only for linear locations | **Excluded** (free consumes the linear `Ref`/`Cap`; `PtrT` alone cannot access memory) | Not measured; capabilities are erased (paper claims zero runtime overhead) | Coq; 0 admits; 5 global axioms plus 29 module-type parameters |
| CHERIvoke (MICRO'19) | CHERI pure-capability code + allocator | Arbitrary code in the same address space; hardware tags + runtime sweep | None (argued) | 25% heap quarantine; shadow map of 1 bit per 16-byte granule | **Permitted** while quarantined; **revoked** (tag cleared) by the sweep before reuse | Averages 4.7% runtime and 12.5% memory (maxima 51% and 35%), SPEC CPU2006, capabilities simulated on x86 | None |
| Cornucopia (S&P'20) / CheriBSD | CheriBSD kernel revoker | As CHERIvoke; concurrent sweep, then a stop-the-world pass | None (argued; Juliet tests) | Allocator-defined quarantine (25% in the evaluation); revocation epochs | Same as CHERIvoke | Under 2% average, 8.9% worst case (concurrent); 5.8% stop-the-world. SPEC CPU2006 on multicore CHERI FPGA | None |
| Swasey–Garg–Dreyer OCPL (OOPSLA'17) | HLA: higher-order, concurrent, GC'd | Contexts with no location literals and no assertions (syntactic) | RS (Theorem RobustSafety) | No deallocation | **Permitted** (never released while reachable). A caretaker-wrapped access is **revoked**: it gets stuck when disabled | n/a | Coq + Iris (paper states it; artifact not examined) |

Basis: documentation (papers) + source (Coq and Java at the pinned revisions) + derived (fate classification).

### MSWasm: colored memory safety and the treatment of freeing

The published paper, §3.2.2 Fig. 4 (p. 15:10), gives these rules:

- **Handles:** `⟨n_base, n_offset, n_bound, b_valid, n_id⟩`.
- **(H-Load):** requires `v1 = ⟨n1, o, n2, true, nid⟩`, `0 ≤ o`, `o + |τ| < n2`, and `nid ∈ Σ.A.allocated`.
- **(H-Load-Handle):** additionally requires `n % |handle| = 0` and combines the per-byte tags (`bc = ⋀ (t = handle-tag)`) into the loaded handle's validity bit. Forged handles therefore load as corrupted.
- **(H-Free):** requires `h = ⟨a, 0, _, true, nid⟩` and an allocator step `sfree(a, nid)`, which traps if no such segment is allocated.
- **(Handle-Add):** changes only the offset. Out-of-bounds handles may be created and trap only when used.

The monitor (§4.2 Fig. 5, p. 15:12) checks reads and writes as follows:

- **(MS-Read)/(MS-Write):** step only if `T(a) = A(c,s)`, i.e. the location is allocated with the pointer's color and shade.
- **(MS-Free):** requires a prior `alloc(n, a_c, φ)` and no earlier `sfree(a_c)`.
- **Definition 1:** `MS(α*) ≜ ∃T. ε ⊢ ∅ ⇝α* T`.
- **Definition 4:** `⊢ RMS(M) ≜ ∀C s.t. M ⊢ C : attacker. ⊢ MS(M ∘ C)`.
- **Theorem 1 (p. 15:14):** "If `⊢ M : wt` then `⊢ RMS(M)`".

Temporal safety rests on one sentence (p. 15:14): "Because identifiers and colors are never reused, freed segments and regions can be reused for other allocations, while keeping dangling handles and colored pointers related by the bijection."

The property is memory safety of the linked whole `M ∘ C`. It does not say that the context cannot read memory that `M` handed it a valid handle to. It is a trace property, not full abstraction.

Basis: documentation.

### MSWasm implementations (rWasm, Graal, CHERI)

From the paper:

- **rWasm, segments as vectors** (§6.1, p. 15:22): "To enforce temporal safety we clear free segments from memory and use sentinel value to prevent the reuse of segment indexes".
- **rWasm baggy bounds** "gives up on handle integrity and temporal safety".
- **CHERI backend** (p. 15:22): "Temporal safety for CHERI code is still a work in progress … our MSWasm-on-CHERI prototype does not yet support it"; `segfree(handle)` becomes `free(handle)`.
- **Graal ST** (§6.2, p. 15:23) enforces "spatial and temporal safety, but not handle integrity".

From `mswasm-graal` at `9668dbbd…`:

- `Segment.java:22`: `this.key = Math.abs(rand.nextInt());`.
- `SegmentMemory.java:31-34`: `KEY_MASK = 0xffffffff_00000000L; OFFSET_MASK = 0x00000000_ffffffffL; KEY_SHIFT = 32`. A new handle is `(long)s.key() << KEY_SHIFT` (line 80).
- `freeSegment` (87–97) runs `unsafe.freeMemory(seg.memoryBase); segments.remove(seg.key());`.
- `getAndValidateSegment` (119–142) traps `trapNull` on key 0 and `trapCorrupted` on `!segments.contains(key)`. `trapFreed` (206) is never called.
- `getAndValidateEffectiveAddress` (155–168): `int offset = getOffset(handle); long effectiveAddr = s.memoryBase + offset; if (effectiveAddr >= s.memoryBound || effectiveAddr + accessSize > s.memoryBound) … trapOutOfBounds`.
- `WasmBlockNode.java:975-982` (`HANDLE_ADD`): `long result = value + shift;` with `int shift`.
- `load_handle` (375–378) runs `getAndValidateEffectiveAddress(node, handle, 4); long value = getLong(addr);`. `store_handle` (432–434) validates 4 bytes and runs `putLong`.

Three conclusions follow; none was executed:

1. **Freed keys can be redrawn.** `Math.abs(rand.nextInt())` maps K and −K to K, so each later allocation redraws a freed key K ≠ 0 with probability 2/2³² = 2⁻³¹. A redraw revalidates the stale handle. Over n allocations the union bound is ≤ n·2⁻³¹; for n = 10⁶ that is ≈ 4.7×10⁻⁴. Temporal safety here is therefore probabilistic, unlike the model's never-reused ids.
2. **No lower-bound check.** A 32-bit offset ≥ 2³¹ becomes a negative `int`, giving `effectiveAddr < memoryBase`, which passes. `handle.add` of 0x7fffffff twice and then 1 reaches `memoryBase − 1` without carrying into the key. The model requires `0 ≤ o`.
3. **Handle accesses overrun by 4 bytes.** A handle access at `bound − 4` passes the 4-byte check but touches `[bound−4, bound+4)`.

Whether compiled C reaches (2) or (3) is unknown. A hostile MSWasm context can emit `handle.add` freely.

The ms-wasm `README.md` (lines 118 and 189–190) links `Dockerfile` and `generate-graphs.py`, but the tree at `b7cd1a0…` contains only `README.md`. The README indexes implementations, the compiler, tools and benchmarks; it indexes no formal-semantics mechanization.

Basis: source + derived.

### Linear capabilities: StkTokens and fully abstract compilation of verified code

**StkTokens** (§2, p. 19:4): "when a linear capability is moved between registers or memory, the source is cleared"; `split` and `splice` replace sub-capability derivation. Theorem 1 (p. 19:20; equivalences per Def. 3, p. 19:19) reads: "For reasonable, well-formed components comp1 and comp2, we have comp1 ≈ctx comp2 ⇔ comp1 ≈ctx comp2" (oLCM on the left, LCM on the right; the compiler is the identity). The adversary "is not assumed to be reasonable". Costs (§6.2, pp. 19:25–26) are qualitative only: constant checks per crossing and "possibly a small memory overhead because stack frames must be of non-zero length". The paper relies "on the assumption that capability machines like CHERI can be extended with linear capabilities in an efficient way", and estimates (does not measure) atomic linear loads at "on the order of 10x slower or more".

**Van Strydonck et al.** (JFP preprint):

- **Approach (abstract):** "memory resources described by spatial separation logic predicates can be represented at run time by linear capabilities".
- **Allocation (§3, p. 10):** target `malloc` "guarantees a fresh heap location … This avoids reuse of locations after free; if any newly allocated location could have been previously used by the context, it could have kept a reference to it and hereby broken the linearity guarantees", and "we do not consider free". Supporting `free` is listed as future work (§8, p. 50).
- **Full abstraction (§6, p. 26):** stated as ⊢s ⇝ t ∧ ⊢s′ ⇝ t′ ⇒ (t ≃ctx t′ ⇔ s ≃ctx s′). It does not distinguish stuck from diverging programs.
- **Trust (§8.3, p. 51):** the separation-logic rules "are presented as axioms … assumed to be part of the trusted computing base".

Basis: documentation.

### Local, uninitialized and directed capabilities (Cerise)

**Local capabilities** (journal preprint §2, p. 3): "we assume an infinite address space and unbounded integers". In §9 (p. 33) the authors write: "we need to clear all of the stack that we are not using ourselves … on every boundary cross between trusted code and adversary code, a potentially large region of memory must be cleared". They suspect one of the two clearings can be dropped but note "the cost is halved, but remains asymptotically the same". Georges' dissertation (Chapter 1, printed p. 14) quotes the POPL'21 paper: this "requirement is very costly in practice". It also notes (printed p. 15) that Skorstengaard's formalization "is entirely done on paper".

**Machine definitions** in `cerise-stack-monotone` at `dff1909f…`:

- `theories/addr_reg.v:10-11`: `RegNum: nat := 31`, `MemNum: Z := 2000000`; lines 4–7 say the exact size "does not matter, it could be made a parameter".
- `theories/machine_base.v:7-29`: `Perm ::= O | RO | RW | RWL | RX | E | RWX | RWLX | URW | URWL | URWX | URWLX`; `Locality ::= Global | Local | Directed`; `Cap := (Perm * Locality) * Addr * Addr * Addr`.
- `machine_base.v:181-199`: `canReadUpTo` is `e`, or `a` for U permissions. `canStore p a w` is always true for `Global`, requires `pwl p` for `Local`, and requires `pwl p && leb_addr (canReadUpTo w) a` for `Directed`.
- `theories/cap_lang.v:94-124` (`verify_access` and its spec): `LoadU` needs `b ≤ a' < a ≤ e` and `StoreU` needs `b ≤ a' ≤ a < e`. `StoreU` at `a' = a` advances the cursor to `a+1` (470–492). `PromoteU` yields `(promote_perm p, g), b, min a e, a` (493–499).
- Consequently the callee has no read authority over stale frame contents above `a` until it overwrites them, so local revocation needs no clearing.

**Full abstraction and its context condition:**

- `theories/linking.v:30-39` (`well_formed_pre_comp`): every exported word and every word in the component's memory satisfies `can_address_only w (dom ms) /\ pwl w = false /\ is_global w = true`, and `forall a, a ∈ dom ms -> (e_stk <= a)`.
- `is_context` (155–158) is `link c comp p /\ is_program p`.
- `theories/full_abstraction.v:39-41`: `is_fully_abstract compile := forall compS1 compS2, contextually_equivalentS compS1 compS2 <-> contextually_equivalentT (compile compS1) (compile compS2)`. `contextually_equivalent` (27–37) compares `Terminates … v` for every context.
- Lines 678–681: `fully_abstract` instantiated for `lang.overlay_lang` versus `cap_lang.cap_lang`, and `Theorem compile_fully_abstract: fully_abstract compile`.

**Overlay semantics and the logical relation:**

- `theories/overlay/base.v:6-9` adds a depth-indexed `Stk: nat -> Perm -> Addr -> Addr -> Addr -> Cap` and `Ret`. In `overlay/lang.v:219-226`, a load through `Stk d …` whose frame is gone hits `None => (Failed, φ)`.
- `binary_model/region_invariants_binary.v:16-21`: `region_type ::= Monotemporary | Permanent | Revoked | Monostatic … | Uninitialized of (Word * Word)`; transitions at 23–36. `region_invariants_batch_uninitialized_binary.v:31-44`: `u_merge_op` maps `Monotemporary` to `Uninitialized w` for the given addresses.

Basis: source + documentation.

### RichWasm: typed shared memory between GC'd and manually managed code

**Types and freeing:**

- `theories/term.v:71-82` defines the pretypes, including `PtrT : Loc -> Pretype | OwnR : Loc -> Pretype | CapT : cap -> Loc -> HeapType -> Pretype | RefT : cap -> Loc -> HeapType -> Pretype`.
- `typing.v:2597-2606` (`FreeTyp`) requires `M.is_empty (LinTyp S) = true`, `QualLeq (qual F) Linear q = Some true` and `HeapTypeUnrestricted F ht`, and gives `[Free]` the type `EmptyRes (QualT (RefT W l ht) q)`: a linear reference is consumed.
- `reduction.v:607-612` (`red_free`): `free_mem_range st l Linear = Some st'` (comment: "We can only free linear locs").

**Garbage collection:**

- `GC_step` (`reduction.v:659-680`) takes roots from instructions, locals and the store.
- `collect_unr` (`locations.v:381-395`) keeps exactly the unrestricted locations reachable from the roots. It also frees linear locations reachable only through collected unrestricted cells ("Recursively free dangling chains of references in linear memory").
- The paper (§3.1, p. 214:9) says that a linear reference placed in GC'd memory makes the GC its owner. It requires "capabilities always be paired with a pointer in the form of a reference when placed in memory". Capabilities on the heap are disallowed in the formal version (p. 214:18).

**Theorems:**

- `safety.v:2800-2810` (`Preservation`): a well-typed, well-formed configuration taking a `Reduce` step is again typed `HasTypeConfig S' i s' vs' szs es' taus`.
- `preservation_GC.v:2447-2461` (`Preservation_reduce_GC`) covers `GC_step`.
- `safety.v:2928-2935` (`Soundness`): after `Red_Star` (which includes GC steps) the configuration is all values, `[Trap]`, or can step.

All of these sit inside `Module Safety (M : Memory) (T : MemTyping M)` (`safety.v:25`); no module in `theories/` instantiates the 29 `Parameter`s of `Module Type Memory` (`memory.v:7-155`). Two carry upstream `TODO` comments questioning correctness (`get_set_same_size` 44–48, `alloc_same_size` 78–80). The global axioms are `Axiom LEM` (`typing.v:17`); `SizeLeq`, `SizeLeq_desc`, `QualLeq` and `QualLeq_desc` (237, 247, 749, 764), which axiomatize a complete decision procedure for size and qualifier constraints; and `Parameter (M : nat)` (`functions.v:1281`).

The README (129–142) says the one admitted lemma reported in the paper (`HasTypeInstruction_subst_index`) is now proved. The guarantee assumes every linked module is RichWasm-typed. After lowering to Wasm, capabilities are erased and a free-list allocator manages Wasm memory (§6, p. 214:21).

Basis: source + documentation.

### Sweeping revocation: CHERIvoke, Cornucopia, CheriBSD

**CHERIvoke** (§3.7, p. 6): "Strictly, CHERIvoke prevents use-after-reallocation rather than use-after-free, as the program still holds references to quarantined memory until a revocation sweep. Nevertheless, CHERIvoke guarantees that an allocated object can be accessed only through references derived from the latest allocation of that memory". The guarantee covers the heap only. The shadow map uses 1 bit per 16-byte granule, i.e. 1/128 of the heap ≈ 0.78% (derived; the paper says "less than 1%").

The x86 evaluation (§5.1, pp. 6–7) does not run on CHERI hardware: it "simulate[s] the existence of capabilities … using conservative pointer estimation". Hardware extensions were measured on a 100 MHz CHERI FPGA over memory dumps. The headline 4.7% average and 51% maximum come from SPEC CPU2006 averaged over 5 runs (§6, p. 7; §6.6, p. 11).

**Cornucopia** (abstract) offers "non-probabilistic C/C++ temporal memory safety for standard heap allocations". Its "concurrent kernel-resident revocation service" sweeps concurrently and then "complet[es] revocation by stopping the world to sweep only those pages that have accepted capability writes during the initial sweep". Objects freed during a concurrent pass wait for the next one (§III, p. 4).

**CheriBSD** at `88f39900…`: `kern_cheri_revoke(struct thread *td, int flags, cheri_revoke_epoch_t start_epoch, …)` (`sys/kern/kern_cheri_revoke.c:349-352`) returns early when `cheri_revoke_epoch_clears(epoch, start_epoch)` holds ("An entire epoch has come and gone since the starting point of this request", 396–405). Cornucopia (Appendix B, pp. 16–17) defines a revocation epoch as "a per-address-space count of the number of revocations performed". Quarantine segments labeled with the epoch observed after painting the shadow bits are known revoked once "a sufficiently larger epoch counter" is observed.

Basis: documentation + source.

### Formulations of robust safety

- **Swasey–Garg–Dreyer** (§2.3, p. 89:10), Theorem RobustSafety: with `C ∈ AdvCtx` (contexts "containing neither locations nor assertions"), `e` closed and `{⊤} e {x. lowval x}_p`, every state reachable from `(C[e]); (∅, OK)` has `g′ = OK`. The caretaker (§4, pp. 89:14–15) is `wrap ≜ λ(sync, enabled) f x. sync (λ_. assume (!enabled); f x)`; a disabled wrapper "gets stuck", which is not a violation.
- **MSWasm RMS** has the same ∀-attacker trace shape, but the bad events are monitor-stuck memory accesses rather than failed assertions.
- **Full abstraction** (StkTokens, Van Strydonck et al., Cerise) is relational, not a trace property.

Basis: documentation + derived.

### Toy-model probe

A pure-Python model (`support/retained_handle_toy.py`) encodes, in one rule each, how the cited semantics decide a retained-handle use. In every case the component allocates, hands out a handle, frees and reallocates the same cells, and the context then loads through its copy. Results: plain linear memory PERMITTED (reads 42); unique segment ids (MSWasm rule) traps; linear move-only rejected; pointer/capability split rejected; uninitialized cursor traps; quarantine + sweep traps. With random 8-bit keys, 413 of 100,000 trials were PERMITTED (0.00413, against an expected 1/255 ≈ 0.00392). Run with Python 3.13.15, single-threaded, 0.17 s wall time, 12,628 KB maximum RSS; output in `support/retained_handle_toy_output.txt`.

Basis: execution (toy model of the rules, not of MSWasm, Cerise, RichWasm, or CHERI).

### Performance levels

| Level | Finding |
|---|---|
| L1 authoring effort | MSWasm implementation code (pp. 15:22–24): rWasm +1900 LOC (two software techniques of about 500 each in codegen), CHERI backend about 3000, Graal +1200, CHERI-LLVM plus WASI libc about 1600. RichWasm: 17k lines of specification and 58k lines of proof (p. 214:16); `wc` over the 23 artifact `.v` files gives 96,989 lines. Cerise: 68,634 lines in 141 files (directed) and 38,861 lines in 73 files (uninitialized). Others: not measured |
| L2 toolchain build | Documentation only (not run): ms-wasm Docker build about 45 min, >32 GB RAM, image about 80 GB (README 108, 126–130). RichWasm image about 13 GB, about 30 min (README 14). Cerise needs Coq 8.12.0 + Iris 3.3.0 (directed) |
| L3 compile latency | Not measured by any source examined. MSWasm reports only that, over JIT iterations, GraalWasm speeds up faster than Graal ST |
| L4 generated-code overhead | MSWasm: 21.4% / 52.2% / 197.5% / 42.3% over Wasm, and 51.7% over native pure-capability CHERI. CHERIvoke: 4.7% average, 51% maximum. Cornucopia: under 2% average, 8.9% maximum, 5.8% stop-the-world. StkTokens, local, uninitialized, directed, linear-capability compilation, RichWasm: not measured |
| L5 proof checking | Documentation only: Cerise directed "around 2 to 3 hours" with 32 GB RAM plus swap recommended (README 46–47); Cerise uninitialized "around 1h"; RichWasm 10–30 min. Not run (no `coqc` available) |
| L6 memory and binary footprint | CHERIvoke: 25% heap quarantine, 12.5% average and 35% maximum memory overhead, shadow map ≈ 0.78% of heap (derived). Cornucopia: quarantine capped at 25% of heap in the evaluation. MSWasm handles: 64-bit in Graal and baggy bounds, 128-bit CHERI capabilities. StkTokens: non-zero frame length. Binary sizes: not measured |

### Comprehensibility (C1) and orthogonality (C2)

Basis: derived; the counts are this report's tally of named concepts in the cited definitions.

C1, the number of distinct concepts a reader must hold:

- **MSWasm model:** 4 (validity bit and byte tags; segment id; color and shade; the bijection δ). **Graal:** 2 (random key, offset).
- **StkTokens:** 4 (linearity; seals; `split`/`splice`; return tokens).
- **Directed Cerise:** 12 permissions × 3 localities, a U cursor and the write-local store rule; the model adds 5 region states and 3 transition relations.
- **RichWasm:** lin/unr, `Ptr`/`Cap`/`Ref`/`Own`, size bounds, location polymorphism, two memories.
- **CHERIvoke/Cornucopia:** tags, bounds, quarantine, shadow map, revocation epochs, capability-dirty pages.

C2: the systems enforce one invariant, that *no handle that authorizes access survives reuse of its storage*, in four ways:

- statically proving there is no alias (linear capabilities, RichWasm `Cap`, directed store rule);
- checking per access against a never-reused generation (MSWasm ids; Graal keys, probabilistically);
- invalidating all copies before reuse (stack clearing; CHERIvoke/Cornucopia sweeps and epochs);
- moving a cursor so that reuse precedes readability (U capabilities).

Hypothesis, not established: a minimal unifying abstraction is a per-region generation `g` with `valid(h) ⇔ gen(h) = g(region(h))`, where reuse increments `g`. The four mechanisms differ only in when validity is decided: statically, at access, at a revocation epoch, or by write order.

### Validation (V1–V4)

- **V1, specification adequacy:** MSWasm implementations are guided by the model but not proved to refine it, and the Graal source deviates in three places (above). The Cerise machine was not checked against a CHERI ISA specification. RichWasm's `Memory` interface has no witness in the artifact. Van Strydonck et al.'s separation-logic rules are trusted axioms. CHERIvoke and Cornucopia guarantees are argued informally.
- **V2, compiler and checker fuzzing:** MSWasm: PolyBenchC runs only. RichWasm: unit and typechecker tests (`compilers/rich_wasm/typechecking_tests.ml`, `richwasm/src/*_tests.rs`), no fuzzing found. Cornucopia: Juliet test suite, plus booting multi-user CheriBSD with a revoking allocator. Others: not examined.
- **V3, concurrency and microarchitecture:** Cornucopia handles concurrent capability stores with a stop-the-world final pass. StkTokens discusses atomic linear loads on multiple hardware threads, without an implementation. OCPL's language has `fork`, and its robust-safety theorem covers it. MSWasm, Cerise and RichWasm are sequential as presented. Side channels: not examined by any subject.
- **V4, human-model validation:** not examined for any subject.

## Boundaries

- **Not examined:** the MSWasm technical report (arXiv ancillary `tr.pdf`, which the fetcher could not retrieve); rWasm and MSWasm-CHERI source; `mswasm-llvm`; the OCPL Coq development; the POPL'21 uninitialized-capabilities paper text (only its artifact and the dissertation quote); the ICFP'19 text of Van Strydonck et al. (the JFP extended preprint was read); the StkTokens technical-report appendices; CheriBSD beyond `kern_cheri_revoke`; follow-up work (Cornucopia Reloaded, later Cerise).
- **Unknown:** whether the Graal lower-bound and 8-byte-handle deviations are reachable from `mswasm-llvm` output; whether any backend is exploitable through key redraw; whether full abstraction holds for contexts constrained only to obey the component's own discipline, rather than arbitrary well-formed contexts (no examined result addresses it); whether RichWasm's `Memory` parameters are jointly satisfiable; the runtime cost of linear, U or directed capabilities in hardware.
- **Known not to apply:**
  - CHERIvoke and Cornucopia do not prevent use after free before a sweep, and do not cover the stack. The MSWasm CHERI backend gives no temporal safety.
  - MSWasm RMS says nothing about confidentiality of memory reachable from handles the component exports.
  - Cerise full abstraction relates an overlay to the base machine, not a high-level source language, and assumes syntactically well-formed contexts with no write-local or local words.
  - Van Strydonck et al. assume fresh, never-reused allocation; StkTokens assumes an infinite address space.
  - RichWasm's guarantee does not extend to untyped Wasm modules linked after lowering (derived: capabilities are erased and Wasm memory is a raw byte array).
- **Unsupported:** RichWasm cannot encode Rust borrowing or lifetimes (p. 214:4), and its formal version forbids capabilities on the heap. MSWasm's C compiler does not support integer-to-pointer casts beyond special cases (p. 15:23); C++ and type confusion are out of scope. Van Strydonck et al. model no `free`.
- **Stronger conclusions not established:** that any measured overhead transfers between platforms; that the toy model shows anything about the real systems; that "0 admits" means no trusted assumptions (RichWasm carries axioms; Cerise depends on its operational semantics being faithful).

## Evidence

Observed 2026-11-21. Repositories were fetched read-only through the GitHub API and raw endpoints. Line numbers are 1-based at the pinned revision.

- `PLSysSec/ms-wasm@b7cd1a0b2d875b317a2b637d7b4d3c764216e758`: `README.md` 3–4, 24–27 (overhead abstract), 38–93 (repository index), 108, 118, 126–130, 189–190. The tree has 1 blob.
- `PLSysSec/mswasm-graal@9668dbbdbc14a325d60277477ffaac99484388cc`, under `wasm/src/org.graalvm.wasm/src/org/graalvm/wasm/`: `mswasm/Segment.java` 14–23; `mswasm/SegmentList.java` 37–56; `mswasm/SegmentMemory.java` 31–34, 67–105, 119–168, 206, 375–379, 432–435; `nodes/WasmBlockNode.java` 960–982; `constants/Instructions.java` 257–266.
- `logsem/cerise-stack-monotone@dff1909f6abc6de99c28d8f12e903b98dd76fb41`: `README.md` 1–3, 11, 46–58, 74–88; `theories/addr_reg.v` 4–11; `theories/machine_base.v` 7–29, 124–140, 181–209; `theories/cap_lang.v` 94–124, 175–191, 456–499; `theories/linking.v` 30–39, 155–158; `theories/full_abstraction.v` 27–41, 678–681; `theories/overlay/base.v` 6–9; `theories/overlay/lang.v` 195–198, 219–226; `theories/binary_model/region_invariants_binary.v` 16–36; `theories/binary_model/region_invariants_batch_uninitialized_binary.v` 31–44.
- `logsem/cerise-stack@f68111362730aff998798d63c7d6a0a7176eff44`: `README.md` 1–3, 25–26, 70–92; `CITATION.cff`; `theories/machine_base.v` 7–23; `theories/addr_reg.v` 10–11; `theories/fundamental.v` 48, 187; `theories/examples/awkward_example_adequacy.v` 152–170 (`is_initial_memory`, `is_initial_registers`) and 576–589 (`awkward_example_adequacy`: `rtc erased_step … → m' !! fail_flag = Some (inl 0%Z)`).
- `RichWasm/RichWasm-artifact@62c4bbcd67f4613304b3ae5bc6a85a901c2e9c8d`: `README.md` 14, 59, 88–142; `theories/memory.v` 7–155; `theories/typing.v` 17, 237, 247, 749, 764, 2597–2606, 3691–3756; `theories/functions.v` 1281; `theories/term.v` 71–82, 121–131; `theories/reduction.v` 417–423, 607–612, 659–690; `theories/locations.v` 381–395; `theories/preservation_GC.v` 2158–2163, 2447–2461; `theories/safety.v` 25, 36–39, 2800–2810, 2928–2946.
- `CTSRD-CHERI/cheribsd@88f39900c32928d807dba245fba138808c666f34`: `sys/kern/kern_cheri_revoke.c` 349–405 (925 lines).
- Proof-hole counts (comment-stripped regex; script `support/count_proof_holes.py`, output `support/proof_hole_counts.txt`):

  | Repository | Files | `Admitted.` | `admit.` | `Axiom` | `Parameter` |
  |---|---|---|---|---|---|
  | cerise-stack-monotone | 141 | 0 | 0 | 0 | 0 |
  | cerise-stack | 73 | 0 | 0 | 0 | 0 |
  | RichWasm | 23 | 0 | 0 | 5 (`typing.v`) | 30 (29 in `memory.v` `Module Type`, 1 in `functions.v`) |

- Papers:
  - MSWasm, DOI 10.1145/3571208: author PDF of the published version (pp. 15:4, 15:10, 15:12, 15:14, 15:19, 15:22–25); arXiv 2208.13583v3 for comparison.
  - Van Strydonck–Piessens–Devriese, DOI 10.1145/3341688; extended version DOI 10.1017/s0956796821000022 (preprint pp. 1, 10, 26, 50–51).
  - Skorstengaard–Devriese–Birkedal, DOIs 10.1007/978-3-319-89884-1_17 and 10.1145/3363519 (journal preprint §2, §4, §9).
  - StkTokens, DOI 10.1145/3290332 (pp. 19:4, 19:19–20, 19:25–26).
  - Georges et al., DOI 10.1145/3434287 (through the artifact and Georges' dissertation, printed pp. 14–15).
  - Georges–Trieu–Birkedal, DOI 10.1145/3527318 (through the artifact README).
  - RichWasm, DOI 10.1145/3656444 (pp. 214:3–4, 9, 15–16, 18, 21).
  - CHERIvoke, DOI 10.1145/3352460.3358288 (pp. 1–2, 6–7, 11).
  - Cornucopia, DOI 10.1109/SP40000.2020.00098 (pp. 1, 4, 8, 16–17).
  - Swasey–Garg–Dreyer, DOI 10.1145/3133913 (pp. 89:10, 89:14–15).
- Probe: `support/retained_handle_toy.py --trials 100000 --keybits 8 --seed 1` under `timeout 60`; output as listed above.

## Revalidation

- **Cerise:** `curl -sSL https://raw.githubusercontent.com/logsem/cerise-stack-monotone/<rev>/theories/full_abstraction.v | grep -n 'Theorem compile_fully_abstract'`, then confirm that `machine_base.v` still has the `Directed =>` branch of `canStore` and `cap_lang.v` the `verify_access` bounds. Rerun `support/count_proof_holes.py` on the fetched `theories/**/*.v`.
- **RichWasm:** grep `Axiom` and `Parameter` in `theories/typing.v`, `memory.v` and `functions.v`, and check whether any module now implements `Memory` (`grep -n '^Module .*: Memory\|<: Memory'`).
- **Graal:** re-read `SegmentMemory.java` 155–168 and 375–379, and `Segment.java:22`. A lower-bound check, 8-byte validation for handles, or a monotone key counter would remove the respective findings. A small module run under a Graal build would turn derived claim (2) into an observation: allocate a segment, apply `handle.add` 0x7fffffff, 0x7fffffff and 1, then load one byte. That build was not attempted here.
- **MSWasm:** check the published PDF §6–7 for the 21.4/52.2/197.5/42.3/51.7 figures, and the README lines 24–27.
- **CHERIvoke and Cornucopia:** confirm the abstract numbers and the CHERIvoke §3.7 wording. For CheriBSD, grep `cheri_revoke_epoch_clears` in `sys/kern/kern_cheri_revoke.c` at a newer revision.
- **Toy model:** `python3 support/retained_handle_toy.py` finishes in under 1 s. It checks only the toy rules.
