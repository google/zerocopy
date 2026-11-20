# Time cost of register versus memory residence: WCET-aware, optimal and production spill-cost models, and what verified register allocators prove

## Summary

- **No examined allocator optimises a worst-case time bound except Falk's WCET-aware allocators, and no examined verified allocator, validator or promotion pass states any time property.** The verified passes in CompCert, CakeML and Vellvm prove only that observable behaviour is preserved. CakeML additionally proves that two fields of its semantic state are unchanged: the fuel `clock` and `stack_max`. Neither field counts machine cycles. Blazy–Robillard–Appel say explicitly that they do not formalise spill cost.
- **The spill-cost models fall into four classes:**
  - **WCET-driven:** Falk 2009 and Falk et al. 2011, using worst-case execution paths from the aiT analyser.
  - **Frequency-weighted expected cost:** LLVM greedy allocation and spill placement, the Appel–George integer linear program (ILP), and Unison. Each weights costs by an estimated block frequency.
  - **Static occurrence counts with no loop weighting:** CompCert and CakeML. CakeML takes a per-variable maximum over the two arms of an `If`. (Basis: source)
  - **Exactness:** only Appel–George and Unison are exact, each with respect to its own cost model. Appel–George assume each value lives in exactly one place. Unison assumes constant instruction latencies and LLVM's estimated block frequencies. Neither model is a worst-case bound.
- **Memory residence costs time when the value is on a dependency chain, but it adds no latency when only the load's address is off the chain.**
  - uops.info reports an L1-hit load-to-use latency of 5 cycles on Haswell, Skylake, Ice Lake and Alder Lake-P, and 4 cycles on Zen 3 and Zen 4. The register-register `ADD` latency is 1 cycle.
  - On an Ice Lake-SP host, the micro-probe in `support/` measured these minimum costs per chain link:
    - spill, reload, then `add`: 3.05–3.24 cycles (median up to 6.74);
    - read-modify-write `add [mem], r`: 6.84–7.08 cycles;
    - `add r, [mem]` with the address off the chain: 1.00 cycle.
  - These figures are for that host only.
- **Evidence for verified versus conventional compilation of certified control software is limited:**
  - **MTU engine-control study (Kästner et al. 2018):** CompCert's aiT WCET bounds were 19–41% lower than those of a conventional compiler run without optimisation. The worst-case response time was 28% lower.
  - **Airbus flight-control study (Bedin França et al. 2012):** reported only as "significantly improved" in the sources examined here. No numbers were examined.

## Applicability

This report has three parts.

1. **Production and research allocators.** Their cost models are compared at the pinned revisions:
   - LLVM `llvm/llvm-project@0c99e3f432142834a257cd4c3067d7a69373e6d1`;
   - Unison `unison-code/unison@9f9857e742156b51e6314488f4173cd1b42c4aec`;
   - CompCert `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`, untrusted OCaml allocator side;
   - CakeML `CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb`, heuristic side.

   Two further allocators are reconstructed from their papers: Appel–George 2001, read in its technical-report form, and Falk's 2009 and 2011 allocators.
2. **Verified allocation and promotion theorems.** These are classified by what they guarantee:
   - CompCert `Allocproof.v`;
   - CakeML `reg_allocProofScript.sml`, `linear_scanProofScript.sml` and `word_allocProofScript.sml`;
   - Vellvm `vellvm/vellvm-legacy@54a5c641ea94b74f551da1d6345c8f335bb7b227`, the PLDI 2013 `vmem2reg` development;
   - the Blazy–Robillard–Appel and Rideau–Leroy papers.
3. **Measured time cost of register versus memory operands.** Sources are uops.info pages fetched on 2026-11-20, one micro-probe run on one host, and published WCET comparisons for certified control software.

How the subjects relate:
- LLVM, Unison, CompCert, CakeML, Appel–George and Falk are compared side by side. Unison takes LLVM's machine IR as input and uses LLVM's block-frequency estimate, so its frequency weights inherit LLVM's.
- CompCert's allocator is untrusted OCaml (`IRC.ml`, `Regalloc.ml`). Its correctness rests only on the Coq validator in `Allocation.v`. The Blazy–Robillard–Appel Coq implementation of iterated register coalescing (IRC) is not in the pinned CompCert tree: the only allocation files are `backend/IRC.ml`, `IRC.mli`, `Regalloc.ml`, `Allocation.v` and `Allocproof.v`.
- The uops.info numbers describe the named commercial CPUs (see `support/uops_info_extract.txt`). The probe numbers describe one KVM guest on an Intel family-6 model-106 (Ice Lake-SP) host. Neither describes the TriCore, PowerPC or Hexagon cores used in the WCET and Unison studies.

Scope limits:
- Source claims hold at the pinned revisions only.
- The heuristic constants quoted below (25, 3, 1.01, 0.5, 10, 2, 4, 5) are revision-specific tuning values, not stable interfaces.
- Results for x86-64 memory operands do not carry over to load/store architectures. There, a spilled operand always costs a separate load instruction.

## Findings

### 1. Cost-model taxonomy

| Allocator | Objective minimised | Frequency or path source | Cost of a spilled value | Rematerialisation | Exact? | WCET-aware? |
|---|---|---|---|---|---|---|
| LLVM greedy (assignment, eviction, splitting, spilling) | Heuristic. Allocation order and eviction compare per-interval spill weights. Split decisions sum block frequencies. | `MachineBlockFrequencyInfo`, from profile or static estimate | Weight is the sum over uses and defs of `(isDef + isUse) × freq(block)/freq(entry)`, normalised by interval size plus 25 instructions | Weight × 0.5 if every def is rematerialisable; `InlineSpiller::reMaterializeFor` before reloads | No | No |
| LLVM `SpillPlacement` | Hopfield-network energy, "the expected spill code execution frequency" | Block frequencies | Bias and link weights are block frequencies | n/a | Local minimum only | No |
| CompCert `Regalloc.ml` and `IRC.ml` | IRC simplify, coalesce and spill. The spill candidate minimises `spillcost/degree²`. | None | 10 per use or def by an operation, load, store, condition or call; 1 per move; `max_int` means unspillable | None (no `remat` occurrence in `Regalloc.ml` or `IRC.ml`) | No | No |
| CakeML `word_alloc` heuristics | IRC or simple colouring picks the minimum `scost/degree`. Linear scan is the alternative. | None (an `If` takes the per-component maximum of its two arms; a `Loop` body is counted once) | `(c + 2·lr + 4·lm + 2·rr + 4·rm) × (5 if the variable is absent from the `calls` set else 1)` | None found | No | No (max-over-branches only) |
| Appel–George 2001 | Estimated runtime cost of spill loads, stores and CISC memory operands | Static frequency estimate (Wu–Larus); profiles possible | `weight_p·(C_load + 3·C_instr)` per reload; analogous for stores and memory operands | Not modelled | Yes, for the "one location at a time" model | No |
| Unison | `Σ_b weight(b) × cost(b)`. Speed: weight = freq(b), cost = issue cycle of the block's exit. Size: weight = 1, cost = Σ instruction sizes. | LLVM's block-frequency estimate | Implicit: optional spill and reload copies consume issue cycles and resources in a jointly scheduled model | Yes, as an alternative load from an unbounded "remat" register class | Yes, within the time limit, for its model | No |
| Falk 2009 (graph colouring) | Briggs colouring, driven by the worst-case execution path (WCEP) | aiT WCET analysis, recomputed after each basic block is allocated | Spill choice favours VREGs with fewest occurrences in the WCEP block with the most worst-case spill code | Not examined | No | Yes |
| Falk et al. 2011 (ILP) | ILP using "precise WCET models" | WCET timing data | Formulation not examined (full text not accessible) | Not examined | ILP-optimal for its model | Yes |

Basis: source for LLVM, CompCert, CakeML and Unison; documentation for Appel–George (technical report text), Unison (paper) and Falk (abstract and group project page).

### 2. LLVM: frequency-weighted spill weights, eviction and Hopfield spill placement

Weight of one instruction (`LiveIntervals.cpp:1048-1058`):

```cpp
float Weight = isDef + isUse;
if (OptForSize) return Weight;
return Weight * MBFI->getBlockFreqRelativeToEntryBlock(MBB);
```

Interval weight (`CalcSpillWeights.cpp:323-406`):
- The per-instruction weights are summed.
- A def in a loop-exiting block that is live out gets `Weight *= 3` ("what looks like a loop induction variable update").
- `TotalWeight *= 1.01F` if copy hints exist.
- `TotalWeight *= 0.5F` if `isRematerializable(...)`.
- The total is multiplied by `TRI.getSpillWeightScaleFactor(RC)`.
- Finally it is normalised by `UseDefFreq / (Size + 25*SlotIndex::InstrDist)` (`CalcSpillWeights.h:35-43`). The header comment explains the constant: "small intervals have a spill weight that is mostly proportional to the number of uses, while large intervals get a spill weight that is closer to a use density."

Eviction, by `DefaultEvictionAdvisor::shouldEvict` (`RegAllocEvictionAdvisor.cpp:218-233`):
- `A.weight() > B.weight()` decides eviction, unless a hint applies and the evictee can still be split.
- Spill weights are therefore expected use/def counts per function call. They are not cycles.

Stage machine, from `RAGreedy::selectOrSplitImpl` (`RegAllocGreedy.cpp:2777-2878`). Each step is tried only if the previous one fails:
1. Try a free register (`tryAssign`).
2. Evict lighter intervals (`tryEvict`).
3. On first sight, defer: stage becomes `RS_Split` and the interval is requeued.
4. Split (`trySplit`).
5. Recolour as a last chance (`tryLastChanceRecoloring`), or spill (`spiller().spill(LRE, &Order)`).

New intervals produced by spilling are marked `RS_Done`.

Spill cost used when deciding to take a callee-saved register for the first time (`calcSpillCost`, `RegAllocGreedy.cpp:2393-2413`):

```cpp
SpillCost += (Reads + Writes) * MBBFreq.getFrequency();
```

`SpillPlacement.cpp:11-25` documents the placement objective:

```text
E = -sum_n V_n * ( B_n + sum_{n, m linked by b} V_m * F_b )
The energy function represents the expected spill code execution frequency,
or the cost of spilling. ... It is guaranteed to converge to a local minimum.
```

`Node::update` (lines 151-178) uses a dead zone `Threshold`. `setThreshold` sets it to `max(1, (Entry >> 13) + bit12)` (lines 282-288), with the comment "Apparently 2 is a good threshold when Entry==2^14". Bundles larger than 100 blocks receive a negative bias of `EntryFreq >> 4` (lines 269-274).

Rematerialisation and memory operands are handled in `InlineSpiller.cpp`:
- `reMaterializeFor` (line 674) recomputes a value instead of reloading it.
- `foldMemoryOperand` (lines 998-1088) folds a stack-slot reference directly into the using instruction through `TII.foldMemoryOperand`. On x86 this produces the register-memory forms whose latency is tabulated in §6.

Basis: source.

Consequence: LLVM's objective is an expected-frequency proxy. A block that is rare in the frequency estimate but on the worst-case path receives low weight. Nothing in these files reads a path bound or a timing model. (Basis: derived from the source above.)

### 3. CompCert: untrusted static-count IRC, a posteriori validation

`Regalloc.ml:15-27` summarises the algorithm:
1. Split live ranges.
2. Convert RTL to XTL.
3. Eliminate dead code.
4. Repeat until no spilled variable must be in a register:
   - build the interference graph and colour it with IRC;
   - insert spill and reload code for spilled variables that must be in registers.

Spilling is "semi-naive" (lines 820-827):
- spill after every definition and reload before every use;
- a short list of equations `spilled-var = temp` avoids reloading a value already in a temporary.

The spill cost (`spill_costs`, lines 490-600) is a static count:
- `Xop`, `Xload`, `Xstore`, `Xcond`, `Xjumptable` and calls charge 10 per argument or result (`charge_list 10 1 args; charge 10 1 res`).
- `Xmove` charges 1.
- Reload destinations, spill sources and parallel-move temporaries charge `max_int`, which makes them unspillable.

Neither the file nor `IRC.ml` uses loop depth or execution frequency. A case-insensitive search of both files for `loop|freq|depth` matches only the word "frequently" in an `IRC.ml` comment about worklist operations (lines 121-122). `IRC.ml:731-745` selects the spill candidate by minimising `spillcost/(degree²)`. This is Bernstein et al. 1989's h0, as the comment at lines 721-723 records. Chaitin's `spillcost/degree` is left commented out at lines 714-719. The coalescing test is the Briggs criterion (`canCoalesceBriggs`, line 558).

Correctness does not depend on any of this. `Allocation.v:1355` declares `Parameter regalloc: RTL.function -> res LTL.function` (external oracle). `transf_function` (lines 1359-1367) accepts the oracle's output only if `check_function` succeeds. That check is the backward dataflow inference of variable-location equations from Rideau–Leroy. The theorem (`Allocproof.v:2528-2529`) is:

```coq
Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (LTL.semantics tprog).
```

It is proved with `forward_simulation_plus` (`Smallstep.v:702-713`): each source step is matched by one or more target steps (`Plus L2 s2 t s2'`), with the same trace `t` of observable events. The relation bounds the number of target steps neither above nor in cycles.

Classification: semantic preservation only. (Basis: source.)

The Rideau–Leroy paper (CC 2010) reports these costs for the validator:
- it adds 20% to register-allocation time and 6% to whole compilation time on the CompCert test suite;
- it is a 350-line validator with a 900-line Coq proof;
- verifying the original allocation and spilling passes took 4300 lines of Coq, and more than 10,000 lines including the Blazy–Robillard–Appel colouring proof.

The paper calls this "a ten-fold reduction in the proof effort". (Basis: documentation.)

### 4. CakeML: verified colouring and linear scan, static usage heuristics

Heuristics in `word_allocScript.sml`:
- `get_spillcost` (lines 1724-1728) is `(c + 2*lr + 4*lm + 2*rr + 4 * rm) * if istail then 5 else 1n`. Line 1722 is the comment `(* TODO: ALL of these magic numbers must be adjusted!! *)`. In `get_heuristics` (lines 1741-1753), the `istail` argument is `lookup k calls = NONE`: the variable is absent from the `calls` set, which `get_heu` accumulates at `Call` nodes through `add_call`.
- The counters `c`, `lr`, `lm`, `rr` and `rm` are accumulated by `get_heu`.
- For `If`, each counter takes the maximum over the two arms (`heu_max`, lines 1421-1424, comment "For Ifs, as a heuristic we take the max over branching paths").
- For `Loop`, the body is counted once (`get_heu fc (Loop names body exit_names) lr = get_heu fc body lr`, line 1502).
- `select_reg_alloc` (lines 1755-1760) chooses linear scan when `alg ≥ 4`, otherwise IRC or `Simple` colouring.
- The spill picker chooses the "cheapest node in the spill worklist, based on spill cost / degree" (`reg_allocScript.sml:767-772`).

Theorems:
- `reg_alloc_correct` (`reg_allocProofScript.sml:3451-3467`) and `linear_scan_reg_alloc_correct` (`linear_scanProofScript.sml:6003-6018`) state that:
  - the allocator returns `M_success col`;
  - `check_clash_tree (sp_default col) ct LN LN = SOME(...)`, so there is no clash;
  - physical variables are mapped to `x DIV 2`;
  - stack variables are mapped to colours `≥ k`;
  - forced pairs get distinct colours.
- `word_alloc_correct` (`word_allocProofScript.sml:3391-3406`) states that evaluating the allocated program gives the same result `res'` as the source, together with `word_state_eq_rel rst rcst`.
- `word_state_eq_rel` (lines 147-161 onward) includes `t.clock = s.clock`, `t.stack_max = s.stack_max` and `t.stack_size = s.stack_size`.

Classification: semantic preservation plus preservation of the fuel clock and `stack_max` observables. In the functional big-step semantics, the clock is decremented at calls and loop iterations (`dec_clock`). It is therefore a step-budget observable, not a cycle count, and register-versus-stack placement does not change it. (Basis: source; the interpretation of `clock` is derived from its use with `dec_clock` in `evaluate_apply_colour`, lines 994-1035.)

### 5. Appel–George optimal spilling

The model is a 0-1 ILP over program points `p` and variables `v`. It has register, memory, load and store indicator variables and these constraints:
- `Exists`: a variable is in exactly one place;
- register capacity `K[p]` (6 allocable registers on IA-32);
- copy propagation;
- Pentium-specific operand-class constraints (Binary, Unary, Mutate and others) that allow memory operands.

The objective is:

```text
minimize COST:
  sum_{(p,v) in Exists} weight_p((C_load + 3C_instr) l_{p,v} + (C_store + 3C_instr) s_{p,v})
+ sum_{(p1,p2,v1,v2) in Binary} weight_p1((C_load + C_instr)(m_{p1,s}+s_{p1,v1})
                                  + (C_load + C_store + C_instr)(m_{p2,v2} + l_{p2,v2}))
+ ...
```

Here `weight_p` is "an estimated frequency of execution", obtained statically using Wu–Larus. The authors assume `C_load > C_store > C_move > C_instr` and state: "Our spilling is optimal only with respect to this model". In this model a value lives in one place at a time. Their more accurate model, which lets a value live in both places, blew up the solver.

Reported costs, from the SML/NJ 110.23 backend on IA-32:
- ILP solve time at most 144 s for the largest cluster (15,561 instructions) on a 250 MHz SGI MIPS machine;
- "most clusters being solved within 10 seconds";
- empirical complexity about `O(n^1.3)`;
- with optimistic coalescing, a 9.5% geometric-mean speedup on Pentium over SSA splitting with IRC.

Optimal coalescing by ILP "blows up on any but the tiniest examples". (Basis: documentation, technical report TR-630-00, the text form of the PLDI 2001 paper.)

### 6. Unison: exact for a frequency-weighted makespan

The objective (`completemodel.cpp:295-308`) is:

```cpp
// The objective is to minimize the cost of each block possibly weighted by
// the estimated execution frequency:
if (input->optimize_dynamic[n])
  linear(*this, IntArgs(input->freq), fs, IRT_EQ, gf()[n]);
else
  linear(*this, fs, IRT_EQ, gf()[n]);
```

The block cost (`model.cpp:2255-2275`) is `c(out[b])`, the issue cycle of the exit operation, when the optimised resource is `ISSUE_CYCLES`. Otherwise it is the summed consumption of a resource, such as instruction size. `doc/objective-parameters.tex` exposes the weighting flag `optimize_dynamic` and the optimised resource `optimize_resource`, where `-1` means cycles. The branching heuristics also weight by frequency: `spilling_cost(w, b) = w * freq[b]` (`globalmodel.cpp:110-112`).

Results reported in the TOPLAS paper (arXiv v5):
- **Estimated speed:** mean estimated speedup over LLVM 3.8 of 1.1%–10% across Hexagon, ARM and MIPS. Functions of up to 946 instructions were solved optimally within a 15-minute limit.
- **Code size:** mean code-size reduction of 1.3%–3.8%.
- **Actual Hexagon V4 speedups (simulator):**
  - 6.6% mean speedup on the hottest MediaBench functions, and 5.6% mean on whole applications;
  - 17.7% of functions were actually slowed down; the paper gives the slowdown as "down by 11.1%";
  - the estimate overestimated actual speedup for 71% of the functions with a non-zero estimation error;
  - Spearman correlation between estimated and actual speedup of 0.7.
- **Stall-free processor configuration:** with pipeline stalls removed, only 3.8% of functions slow down and the correlation rises to 0.89. The authors conclude that dynamic processor behaviour is "the main source of inaccuracy".
- **Authors' caveat:** the speed model "assumes a processor with constant instruction latencies".

So Unison is exact for a static, frequency-weighted, constant-latency model. It is neither a WCET model nor a cycle-accurate one. (Basis: source + documentation.)

### 7. Falk's WCET-aware allocators

The TUHH WCC project page (dated 2017-09-01) describes the 2009 graph-colouring allocator. Its central difficulty is circular: WCET analysis needs register-allocated code, but allocation wants WCET data. Falk breaks the cycle by inverting the usual assumption:
- All VREGs start in memory, so intermediate code stays executable and analysable.
- VREGs are then moved into physical registers one basic block at a time.
- After each block the WCEP is recomputed with aiT.
- The next block chosen is "that basic block b leading to the highest execution of spill code in the worst case".
- Its VREGs, ordered by occurrence count, are handed to a Briggs allocator, which spills the VREG with the fewest occurrences.

Reported results, against Briggs colouring that spills the highest-degree node, on 46 benchmarks from MRTC, MediaBench, UTDSP and DSPstone:
- average WCET estimate of 68.8% of baseline, i.e. a 31.2% reduction;
- range from 6.9% (`qurt`) to 75.9% (`spectral`).

The ECRTS 2011 ILP allocator's abstract reports, on 55 benchmarks against standard graph colouring:
- WCET reduced by 20.2% on average;
- average-case execution time (ACET) reduced by 14%;
- "outperforms a WCET-aware graph coloring allocator by more than a factor of two ... while requiring less runtime".

Its constraint system was not examined. The WCC infrastructure page says WCC supports the Infineon TriCore TC1796 and TC1797 and ARM7. The papers' exact experimental target was not confirmed from their full texts. (Basis: documentation.)

### 8. What the verified theorems guarantee

| Artifact | Statement (abridged) | Semantic | Resource | Time |
|---|---|---|---|---|
| CompCert `Allocproof.transf_program_correct` | `forward_simulation (RTL.semantics prog) (LTL.semantics tprog)`, validated output only | yes | no | no |
| Rideau–Leroy validator (CC 2010) | Validator success implies forward simulation; semantic preservation follows | yes | no | no |
| Blazy–Robillard–Appel (ESOP 2010) | IRC terminates with a valid colouring (interfering vertices get different colours; range within precoloured registers). "We will not formalize move-cost and spill-cost." | yes, colouring validity | no | no |
| CakeML `reg_alloc_correct` and `linear_scan_reg_alloc_correct` | Success, no clash, physical and stack placement constraints, forced pairs distinct | yes | no | no |
| CakeML `word_alloc_correct` | Same result, and `word_state_eq_rel` including `clock`, `stack_max`, `stack_size` | yes | fuel `clock` and stack observables preserved | no (no cycle model) |
| Vellvm `mem2reg_run_sim_wfS` (`vmem2reg_correct.v:495-498`) | `program_sim [vmem2reg.run m] [m]`: converging, diverging and wrong behaviours of the output are matched by the input (`program_sim.v:42-56`) | yes | no | no |
| LLVM `PromoteMemoryToRegister.cpp`, `RegAllocGreedy.cpp` | Unverified; no theorem | n/a | n/a | n/a |

Where a time property would have to be stated (derived; not found in any subject):
1. The source semantics needs a cost that is preserved or bounded across allocation. Every examined preservation statement relates observable traces, plus fuel in CakeML, and none relates cycles.
2. The target semantics needs an explicit latency model that distinguishes register from memory access. None of the examined target semantics has one: LTL in CompCert and wordLang/stackLang in CakeML charge nothing for a stack-slot access.
3. A bound of the form `cyc_tgt(run) ≤ cyc_src(run) + Σ_{reloads/spills on run} c_mem` requires the allocator's spill-code placement to be part of the statement. A validator could check it per program, in the style of Rideau–Leroy, against a WCET objective chosen by an untrusted, WCET-aware oracle.

### 9. Measured register-operand versus memory-operand latency and throughput

Figures are taken from uops.info per-instruction pages, with values in cycles. "Load-to-use" is the latency from the address base register to the result. Reciprocal throughput ("tp") is from the measured loop. The CPUs are: Haswell = Xeon E3-1225 v3; Skylake = Core i5-6500; Ice Lake = Core i5-1035G1; Alder Lake-P = Core i5-12600K; Zen 3 = Ryzen 5 5600X; Zen 4 = Ryzen 5 7600X.

| Instruction form | HSW | SKL | ICL | ADL-P | Zen 3 | Zen 4 |
|---|---|---|---|---|---|---|
| `ADD r64,r64` latency / tp | 1 / 0.25 | 1 / 0.25 | 1 / 0.25 | 1 / 0.20 | 1 / 0.25 | 1 / 0.25 |
| `MOV r64,m64` load-to-use / tp | 5 / 0.50 | 5 / 0.50 | 5 / 0.50 | 5 / 0.33 | 4 / 0.33 | 4 / 0.33 |
| `ADD r64,m64` addr→result / tp / uops | 6 / 0.50 / 2 | 6 / 0.50 / 2 | 6 / 0.50 / 2 | 6 / 0.33 / 2 | 5 / 0.33 / 1 | 5 / 0.33 / 1 |
| `ADD m64,r64` mem→mem (RMW) / tp | 6 / 1.09 | 4 / 1.00 | 7 / 0.53 | 6 / 0.54 | 7 / 0.56 | 1 / 0.56 |
| `MOV m64,r64` tp / uops | 1.00 / 2 | 1.00 / 2 | 0.50 / 2 | 0.50 / 2 | 0.50 / 1 | 0.50 / 1 |
| `IMUL r64,r64` vs `IMUL r64,m64` addr→result | 3 vs 8 | 3 vs 8 | 3 vs 8 | 3 vs 8 | 3 vs 7 | 3 vs 7 |
| `ADDSD xmm,xmm` vs `ADDSD xmm,m64` addr→result | 3 vs ≤9 | 4 vs ≤11 | 4 vs ≤11 | 2 vs ≤10 | 3 vs ≤11 | 3 vs ≤11 |

Basis: documentation (uops.info measurement data). The uops.info paper (§5.2) describes the method:
- Memory-to-register latency is measured through a chain `XOR Ra, Rd; XOR Ra, Rd` that creates a dependency from the destination back to the address register.
- Values marked `≤` are upper bounds.
- The Zen 4 RMW value of 1 cycle and the `≤0`/`≤1` memory-operand bounds on Ice Lake and Alder Lake-P indicate that a store-to-load path faster than the L1 load-to-use path exists on those cores. This report does not identify the mechanism.

Host micro-probe (`support/spill_latency_probe.c`, output in `support/spill_latency_probe_output.txt`). Each variant is an 8-link dependency chain on `%rax`. TSC ticks are converted to core cycles by calibrating against variant A (`add %rbx,%rax`, which has 1-cycle latency). Variant G (`imul`) is a cross-check: it measured 3.00–3.01 against uops.info's 3. There were 101 interleaved rounds on each of logical CPUs 3, 20 and 40.

| Variant (per chain link) | min ratio (3 CPUs) | median ratio (3 CPUs) |
|---|---|---|
| A `add r,r` (calibration) | 1.00 | 1.00 |
| C `add r,[mem]`, address off chain | 1.00 | 1.01–1.02 |
| B spill to `[rsp+64]`, reload, `add` | 3.15–3.24 | 4.60–6.58 |
| S spill to `[rdi]`, reload, `add` | 3.05–3.19 | 4.26–6.74 |
| L memory-resident: load, `add`, store | 3.25–3.35 | 4.89–6.72 |
| D pointer chase `mov rax,[rax]` | 5.01–5.06 | 5.08–5.19 |
| M memory-resident RMW `add [mem],r` | 6.84–7.08 | 7.04–7.57 |

Basis: execution (real measurement on the stated host; not a property of other cores).

Derived readings, for this host only:
- A spill/reload round trip on a critical chain costs at least about 2.1–2.3 cycles more than keeping the value in a register (3.05–3.24 minus 1).
- The median cost was as much as about 5.7 cycles more.
- The B/S/L distributions were bimodal: about 3.2 cycles or about 6.4 cycles per link. The cause is not determined. The host was heavily shared, with a load average of 203–262 on 96 logical CPUs, so SMT co-runners are a candidate, as are alternative forwarding paths.
- A value kept entirely in memory and updated in place costs about 7 times the register latency per update (M).
- A memory source operand whose address does not depend on the chain adds no chain latency (C). It does cost an extra load µop: 2 versus 1 executed µops on Intel, per uops.info.

### 10. WCET and code-size evidence for verified versus conventional compilation

| Study | Software and target | Baseline | Analyzer | Reported effect of CompCert |
|---|---|---|---|---|
| Kästner et al., ERTS 2018 | MTU Friedrichshafen digital engine control unit for diesel engines that drive nuclear-plant emergency generators (handwritten and SCADE-generated C, PowerPC) | Conventional compiler "configured not to use any optimization" | aiT (WCET), StackAnalyzer | WCET −41% (synchronous function); −19%, −21%, −22% (interrupt modes 1–3); WCRT −28%. "total processor load ... about 28% smaller". Worst-case stack −50%, −18%, −39% total. Code segment "slightly smaller". Main cause given: "improved memory performance". |
| Leroy et al., ERTS 2016 | Whole Airbus flight-control software, "about 4 MB of assembly code" | Currently used compiler | aiT | "significantly improved performance in terms of WCET bounds and code size" (no figure in this source) |
| Bedin França et al., ERTS 2012 | Airbus ACG flight-control software, DO-178 level A | Currently used compiler (unoptimised generation) | WCET and code size | Abstract only examined; numbers not examined |
| Leroy et al., ERTS 2016 (average case) | Benchmark suite, PowerPC/ARM; IA32 | GCC 4 | measured runtime | About 10%, 15% and 20% slower than GCC `-O1`, `-O2` and `-O3`; on IA32 "due to its paucity of registers ... approximately 20% slower than GCC 4 at optimization level 1" |

Basis: documentation.

These are comparisons against *unoptimised* qualified baselines. They show the value of register allocation as such. They do not compare a verified allocator with an optimising unverified one under WCET analysis; no such comparison was found.

### 11. Toy model: frequency-weighted versus worst-path spill choice

`support/wcet_vs_freq_spill_toy.py` is a toy model, not any real allocator. It models one loop with bound N, an if/else with paths A and B, n virtual registers live across the loop, and k registers. Each use of a spilled register costs L cycles. Two criteria are solved exactly by enumeration:
- the expected spill overhead, which is the shape of a block-frequency-weighted weight;
- the longest-path (IPET) bound.

Worked example: n=2, k=1, L=4, N=100, pA=0.9, cA=20, cB=30, useA=[1,6], useB=[5,0].
- The frequency criterion spills v0. This gives a WCET bound of 5000 and an expected time of 2660, with path B worst.
- The WCET criterion spills v1. This gives a WCET bound of 4400 and an expected time of 4260, with path A worst.

So the worst-case path switches when the decision changes. This is the WCEP instability that Falk handles by recomputing the WCEP.

Campaign over 20,000 random instances, seed 1:
- the two criteria disagree in 34.8% of instances;
- in those instances the frequency choice raises the WCET bound by a median of 15.0% (p90 43.2%, max 240%) and lowers expected time by a median of 14.2%.

Seed 2 gives 34.9%. Basis: execution (toy model of the spill-criterion distinction, not of LLVM, Falk or any target). The percentages are artefacts of the chosen parameter distribution. They show only that the criteria can conflict in both directions.

### 12. Performance and resource footprint (L1–L6)

| Level | Measured or cited value | Source |
|---|---|---|
| L1 authoring and proof effort | BRA: 600 lines of Coq code, about 4800 lines of proof, a ratio of 8. Rideau–Leroy: 350-line validator, 900-line proof. Original CompCert allocation and spilling: 4300 lines of proof, more than 10,000 with the BRA colouring proof. CakeML proof-file sizes at the pin: `reg_allocProofScript.sml` 3482 lines, `linear_scanProofScript.sml` 6225, `word_allocProofScript.sml` 11587 (line counts of the fetched files; proof versus definition not separated). LLM token budgets: not measured. | papers; `wc -l` on fetched files |
| L2 toolchain build | not measured (LLVM, CompCert, CakeML, Unison builds not run) | — |
| L3 allocation and validation latency | CompCert validator: +20% of RA time, +6% of compile time. BRA extracted IRC: under 0.1 s per program, PowerPC 970 at 2.0 GHz. Appel–George ILP: at most 144 s, most clusters under 10 s, 250 MHz MIPS. Unison: 15-minute limit; optimal up to 946 instructions. Falk ILP: "requiring less runtime" than WCET-aware colouring (no figure examined). LLVM greedy: not measured. | papers |
| L4 generated-code time | Falk 2009: −31.2% WCET (average of 46). Falk 2011: −20.2% WCET, −14% ACET (55). Appel–George: 9.5% speedup. Unison: 1.1–10% estimated; 6.6% and 5.6% actual on Hexagon. CompCert vs unoptimised: −19 to −41% WCET (MTU). Host probe: §9. | papers; execution |
| L5 certificate checking | CompCert validation runs inside each compilation (L3 figure). A Coq proof-checking time for `Allocproof.v` is not measured. | — |
| L6 footprint | MTU worst-case stack −39% total with CompCert. CompCert-compiled code segment "slightly smaller". Unison code size −1.3 to −3.8%. Peak RSS of allocators and validators, `.vo` sizes, energy: not measured. | papers |

### 13. Comprehensibility and conceptual simplicity (C1, C2)

- **C1, human legibility of the cost model.**
  - CompCert's and CakeML's static weights fit on one line each and can be checked locally. Their constants are admittedly ad hoc; CakeML's comment says "must be adjusted".
  - LLVM's weight combines five multiplicative factors (frequency, ×3 induction, ×1.01 hint, ×0.5 remat, register-class scale) with a size normaliser and a separate Hopfield placement whose result is a local minimum. Explaining one spill decision means reconstructing interval weights, cascade numbers and the stage machine across about 3,000 lines of `RegAllocGreedy.cpp`.
  - Appel–George and Unison move the explanation into a declarative model: the objective is one formula and a spill is optimal "with respect to this model". The burden of understanding moves to the fidelity of the model, which Unison measures (§6).
  - A Falk-style allocator's decisions are explained only relative to a WCEP computed by an external analyser, and that WCEP can change after each block.
- **C2, one invariant, several mechanisms.**
  - The examined systems separate "is the allocation correct" (colouring validity, plus semantic preservation through a validator) from "is it cheap" (an unverified heuristic or optimiser).
  - The translation-validation split (untrusted oracle, verified checker) keeps the trusted part independent of the cost model. That is why CompCert can swap in any heuristic without new proofs.
  - The derived corollary: a WCET-aware or ILP-optimal allocator can sit behind the existing CompCert validator unchanged, since `Allocation.v` checks only the oracle's output. Its time benefit would remain unproved unless a cost-annotated target semantics is added.

### 14. Validation coverage (V1–V4)

- **V1, specification adequacy.**
  - CompCert's validator found "several mistakes" in a prototype spilling strategy and raised no false alarms on the CompCert test suite (Rideau–Leroy §5).
  - Unison validated its cost model against a cycle-accurate simulator (Spearman 0.7, or 0.89 without stalls).
  - Falk's results are WCET *estimates* from aiT. Hardware validation of those bounds was not examined.
- **V2, differential and fuzz testing of allocators.** Not examined for these subjects. No allocator-specific CSmith/YARPGen campaign was read.
- **V3, silicon validation.**
  - uops.info and the host probe are direct hardware measurements.
  - The probe's bimodal store/reload latencies show that per-access memory cost on an out-of-order x86 core is not a single constant, which matters for any time model that charges a fixed spill penalty.
- **V4, plant/HIL and human studies.** The MTU application passed simulator and engine-test validation before deployment (Kästner et al. 2018); this is functional validation, not timing. Human-comprehension studies of allocation diagnostics: not examined.

## Boundaries

- **Not examined:** the full text and ILP formulation of Falk et al. 2011, and the full text of Falk 2009 (only the project page and abstract). The quantitative WCET and code-size tables of Bedin França et al. 2012 and the PPES 2011 precursor (DOI `10.4230/OASIcs.PPES.2011.59`): the PDF was not retrievable through the tools used.
- **Not examined:** the Blazy–Robillard–Appel Coq development itself, outside its paper. LLVM `SROA.cpp`. CakeML's space-cost semantics work beyond the `stack_max` field.
- **Unknown:** whether any LLVM target uses profile or static block frequencies in a way that approximates a worst-case path. Nothing in the examined files does.
- **Unknown:** the cause of the bimodal spill/reload latency on the probe host (§9).
- **Known not to apply:**
  - The host probe and uops.info numbers do not describe in-order embedded cores (TriCore, PowerPC e200, ARM Cortex-R/M) or cores with scratchpad stacks.
  - The WCET reductions reported for Falk's allocators and for CompCert were measured against weak baselines: Briggs colouring with a highest-degree spill choice, standard graph colouring, and unoptimised compilation, respectively. They are not effects relative to LLVM greedy.
- **Unsupported by the evidence:**
  - Neither "a verified allocator preserves or bounds execution time" nor "memory residence costs the L1 latency per access" is established in general. Memory residence costs nothing on a chain when the address is independent (§9 C). Store/reload paths can be faster than a full L1 load on some cores (Zen 4 RMW 1 cycle; Ice Lake and Alder Lake-P `≤0`/`≤1` bounds) and slower or variable on others.
  - Unison and Appel–George are exact only for their stated models. Neither is a WCET optimum.
- **Attractive but unestablished:** that delegating register residence entirely to a verified allocation pass is free in time. Every examined verified pass is time-agnostic, so any time guarantee would need new statements of the kind in §8.

## Evidence

All repository observations were made on 2026-11-20 (UTC) at these revisions:
- **`llvm/llvm-project@0c99e3f432142834a257cd4c3067d7a69373e6d1`:**
  - `llvm/lib/CodeGen/LiveIntervals.cpp:1048-1058`;
  - `llvm/lib/CodeGen/CalcSpillWeights.cpp:246-407`;
  - `llvm/include/llvm/CodeGen/CalcSpillWeights.h:28-43`;
  - `llvm/lib/CodeGen/SpillPlacement.cpp:11-25, 72-178, 232-288`;
  - `llvm/lib/CodeGen/RegAllocGreedy.cpp:154, 342, 2393-2413, 2415-2472, 2777-2878`;
  - `llvm/lib/CodeGen/RegAllocEvictionAdvisor.cpp:218-233`;
  - `llvm/lib/CodeGen/InlineSpiller.cpp:674, 998-1088`;
  - `llvm/lib/Transforms/Utils/PromoteMemoryToRegister.cpp:1-15`.
- **`unison-code/unison@9f9857e742156b51e6314488f4173cd1b42c4aec`:**
  - `src/solvers/gecode/models/completemodel.cpp:295-308`;
  - `src/solvers/gecode/models/model.cpp:184-190, 1663-1677, 2255-2275`;
  - `src/solvers/gecode/models/globalmodel.cpp:55-112, 185-201, 412-424`;
  - `doc/objective-parameters.tex`.
- **`AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`:**
  - `backend/Regalloc.ml:15-27, 490-600, 818-827`;
  - `backend/IRC.ml:304-320, 553-580, 714-745`;
  - `backend/Allocation.v:1-40, 1345-1374`;
  - `backend/Allocproof.v:2528-2545`;
  - `common/Smallstep.v:566-591, 699-713`;
  - the repository tree listing, which shows no Coq IRC file.
- **`CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb`:**
  - `compiler/backend/word_allocScript.sml:1421-1424, 1466-1474, 1502, 1722-1760`;
  - `compiler/backend/reg_alloc/reg_allocScript.sml:767-812, 1347, 1440-1493`;
  - `compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml:3451-3467`;
  - `compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml:6003-6018`;
  - `compiler/backend/proofs/word_allocProofScript.sml:143-170, 1107-1130, 3391-3406`.
- **`vellvm/vellvm-legacy@54a5c641ea94b74f551da1d6345c8f335bb7b227`:**
  - `src3.0/Vellvm/program_sim.v:42-56`;
  - `src3.0/Transforms/vmem2reg_correct.v:495-498`;
  - `src3.0/Transforms/README`.

Papers and pages read on 2026-11-20. DOIs were checked against Crossref, the Dagstuhl DOI `10.4230/OASIcs.PPES.2011.59` against DataCite, and the arXiv IDs against arXiv.
- Appel–George technical report TR-630-00 (`https://www.cs.princeton.edu/techreports/2000/630.pdf`): §3.2, §7.
- Lozano et al., arXiv:1804.02452v5: §8, §11, Appendix B.
- Blazy–Robillard–Appel (`regalloc.pdf`): §2, §8.
- Rideau–Leroy (`validation-regalloc.pdf`): §5.
- Abel–Reineke, arXiv:1810.04610: §5.2.
- Kästner et al., ERTS 2018: §5, Figs. 4–5.
- Leroy et al., ERTS 2016: §4.
- Falk 2009 and Falk et al. 2011: the TUHH project page and the ECRTS 2011 abstract text only.
- Bedin França et al. 2012: HAL/bibliography abstract only.
- Chaitin 1982 (`10.1145/800230.806984`) and Bernstein et al. 1989 (`10.1145/73141.74841`) are cited only as the provenance named in CompCert's comments.

uops.info data come from the per-instruction pages listed in `REPORT.json`. They are extracted verbatim, by regular expression, into `support/uops_info_extract.txt`.

Execution:
- **Spill-latency probe:** `gcc -O2 -o /tmp/spill_latency_probe support/spill_latency_probe.c && taskset -c <cpu> /tmp/spill_latency_probe` with 101 rounds of 2,000,000 iterations × 8 links. Run with gcc 15.2.0 on an Intel Xeon @ 2.60 GHz, family 6, model 106, stepping 6, as a KVM guest on 2026-11-20. Full output: `support/spill_latency_probe_output.txt`.
- **Toy probe:** `python3 support/wcet_vs_freq_spill_toy.py 20000 1`, Python 3.13 standard library. Output: `support/wcet_vs_freq_spill_toy_output.txt`.

## Revalidation

- **LLVM cost model.** Diff `llvm/lib/CodeGen/CalcSpillWeights.cpp` (`weightCalcHelper`), `CalcSpillWeights.h` (`normalizeSpillWeight`), `LiveIntervals.cpp` (`getSpillWeight`) and `SpillPlacement.cpp` against the pinned revision. Look for the constants `25`, `* 3`, `1.01F`, `0.5F`, and for any new input other than `MachineBlockFrequencyInfo`.
- **CompCert.** Check that `backend/Allocation.v` still declares `Parameter regalloc` and that `Allocproof.v` still states `forward_simulation (RTL.semantics prog) (LTL.semantics tprog)`. Then search `Regalloc.ml` for `charge_list 10` and for any frequency or loop input.
- **CakeML.** Search `word_allocScript.sml` for `get_spillcost_def` and `heu_max_def`. Check whether `word_state_eq_rel_def` still includes `clock` and whether any cycle or cost field has been added.
- **Unison.** Search `completemodel.cpp` for `post_global_cost_definition`. A change of `freq` weighting, or a new resource kind, alters §6.
- **Hardware.** Rerun `support/spill_latency_probe.c` on the target core. The calibration is trustworthy only if variant G reads about 3.0. On a new microarchitecture, re-extract the same uops.info pages, and use `support/uops_info_extract.txt` as the format reference.
- **Toy model.** `python3 support/wcet_vs_freq_spill_toy.py 20000 1` must reproduce the non-comment lines (those not starting with `#`) of `support/wcet_vs_freq_spill_toy_output.txt` byte for byte, since it uses a seeded PRNG and pure arithmetic.
- **Falk and Bedin França quantitative claims.** These need the full papers, which this report could not obtain. Repeat the investigation with the full texts before relying on any formulation detail.
