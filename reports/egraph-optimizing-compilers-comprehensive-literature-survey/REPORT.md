# E-Graph-Based Optimizing Compilers: A Comprehensive Literature Survey

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

This literature survey and empirical synthesis integrates 50+ primary academic papers (1980–2026) with direct source audits, Lean 4 mechanizations, and reproducible probes from `google/zerocopy:reference@8fcbe48eb10bfac0016dec083c05f19caf265e90` across e-graph compiler architectures:

1. **Production Mid-Ends (`Cranelift aegraphs`):** Replacing standalone `egg` (`23%` serialization overhead) with an SSA-in-place acyclic e-graph (`ValueDef::Union`, single-pass domtree preorder, `5/5/5` hard caps, no general AC) yields **`~2%` Wasm speedup at `+7–8%` compile time**; Fallin's April 2026 ablation shows transient sea-of-nodes-over-CFG-skeleton drives virtually the entire gain, while multi-representation `Union` + DP adds **`~0.1%` speedup** (`1.13` e-nodes/class). Any operand-dropping rewrite requires `(subsume ...)` to prevent SSA dominance violations, and preheader LICM requires `!can_trap()`.
2. **Whole-Function Effectful EqSat (`eggcc` & `Statewalk DP`):** Lowering reducible CFGs to RVSDGs + `StateT` + `Statewalk DP` (`O(k n^2)` FPT in statewalk width $k$) achieves a **`520×` geometric-mean extraction speedup over Gurobi** (`98.4%` of regions have $k \le 5$, spiking to $k=106,259$ on `heat-3d`), yet `eggcc` disables `memory.egg` (`WeaklyLinear` fragility in `schedule.rs`), caps context substitution at `(repeat 5 ...)`, and trails `LLVM-O3-O0` overall (`0.571` vs. `0.326` on PolyBench; `0.876` vs. `0.695` on Bril) while hitting `6.52×` wins where loops collapse algebraically (Fenwick `lowbit`).
3. **Extraction Complexity & Schedule Blindness:** Optimal DAG extraction with shared subexpressions is NP-hard and constant-inapproximable (`arXiv:2408.17042`); naive binary ILPs admit detached zero-grounded cycles, and COIN-OR CBC restarts exceed `36,000 s` (`10h`). No existing fast extractor models finite register pressure (`Probe B`: naive postorder DFS hits `12` peak registers vs. `7` for schedule-aware interleaving on `W=8` dual-reduction DAGs).
4. **Verification & Deferred-UB Soundness:** `egg`'s `check_proof` fails open (`true` on missing rules or dynamic `Applier`s), `VeriISLE`/`Arrival` omit `egraph`/`elaborate`/`alias_analysis` and trust unverified SMT solvers, and IRs with `poison`/`undef` require splitting **`BiEqRule`** (symmetric e-classes) from **`DirRefineRule`** (`⊑`, guarded against non-monotonic `freeze` via `isFreezeFree`). DAG-shared `TreeExplanation` certificates cut proof size **`114.3×`** vs. flat proofs at depth `d=6` (`2,537 B` vs. `289,986 B`) and check in `<0.5 ms` via closed `CongruenceDag` reflection in Lean `v4.34.1`.

The complete 5-section survey, system comparison matrix (25+ systems), and 56-entry bibliography are preserved in [support/egraph_optimizing_compilers_literature_survey.md](support/egraph_optimizing_compilers_literature_survey.md).

## Applicability

- **Reference Synthesis Scope:** Covers congruence closure foundations (Nelson–Oppen 1980, Downey–Sethi–Tarjan 1980, Simplify 2005, unfailing completion / Twee 2021), superoptimization and EqSat engines (`Denali`, `Peggy`, `egg` `0.11.0`, `egglog`, `ECTA`, Colored/Slotted/Guided E-Graphs), production and research compilers (`Cranelift aegraph`, `eggcc`, `DialEgg`, `Tamagoyaki`, `SEER`, `TENSAT`, `Glenside`, `SpEQ`, `RISE`/`Elevate`, `Herbie`, `ROVER`, `E-Syn`, `CIRCT`, `Diospyros`, `Isaria`, `Ruler`, `Caviar`, `Szalinski`, vs. SMT synthesizers `Souper`/`Hydra`/`Hydride`), extractors (`Treewidth DP`, `SmoothE`, `e-boost`), and verification frameworks (`VeriISLE`/`Arrival`, `Lean-MLIR`, `Alive2`, `Chamois-CompCert BTL`, `IsaFoR/CeTA`, `CongruenceDag`, `SideCondCert`).
- **Experimental & Audit Anchor:** Grounded in the 10 detailed e-graph/backend reports archived in `google/zerocopy:reference@8fcbe48eb10bfac0016dec083c05f19caf265e90`.

## Findings

### Foundations, Structural Extensions & Compiler Taxonomy

Basis: `documentation` (published papers) + `source` (`egg` `0.11.0`, `egglog`, `Cranelift`, `eggcc`, `DialEgg`, `rustc_codegen_cranelift`, `egg-extraction-gym`) + `execution` (deterministic probes and Lean 4 mechanizations).

- **Algorithmic Evolution:** `egg` (POPL 2021) replaced eager per-union congruence rebuilding with batched amortized `rebuild()` + monotone e-class analyses (`>3,000×` Herbie speedup). `egglog` (PLDI 2023) unified relational WCOJ/Free Join e-matching (POPL 2022) with Datalog fixpoints and directed/contextual relations (`STEP_SIZE = 2048` adaptive rebuild). Structural extensions address path conditions (`Colored E-Graphs`, `~10×` lower overhead vs. cloning), variable binders (`Slotted E-Graphs` PLDI 2025, `<1 s` on `not_supIrred` where `egg` OOMs), entangled tree automata (`ECTA` ICFP 2022), and search-space explosions (`Guided EqSat` POPL 2024, reducing `RISE` `>60 GB` / `1 h` timeout to `<1 GB` / seconds with `<= 3` guides).
- **Control Flow & Memory Regimes:**
  - **Cyclic PEGs (`Peggy`):** Uniform loop representation at `1.2–6.0 s`/method ILP latency.
  - **Reducible RVSDG + `StateT` (`eggcc`):** Eliminates dominator/loop churn, but irreducible-CFG restructuring adds synthetic predicates (`2.463×` dynamic branches in 2-entry probe) and coarse state edges make `memory.egg` break `WeaklyLinear` invariants.
  - **Pure Sea-of-Nodes + CFG Skeleton (`Cranelift aegraph`):** $O(N)$ single-pass domtree walk; avoids V8 `TurboFan` cache misses (`3–7×` L1 dcache misses vs. `Turboshaft`); frontend audit of `rustc_codegen_cranelift` (`vtable.rs:8-12`) revealed `vtable_memflags()` sets `trusted()` + `readonly()` without `can_move()`, causing `is_pure_for_egraph` to reject all Rust vtable loads.
  - **In-IR MLIR (`Tamagoyaki`, `arXiv:2602.16707v2`) vs. External IPC (`DialEgg`, CGO 2025):** `Tamagoyaki` embeds `equivalence`/`pdl_interp` (`2.38×` e-match speedup; `-11%` delay / `-6%` area on CIRCT `ShiftedFma`) on pure straight-line fragments only (`§4.1`); `DialEgg` shells out per block via files and drops/opaques multi-result ops (`Egglog.cpp:864-868`).
- **SMT Superoptimizer Distinction:** `Souper`, `Hydra` (OOPSLA 2024), and `Hydride` (ASPLOS 2024, Rosette + Z3 CEGIS over AutoLLVM) use SMT synthesis rather than e-graph congruence closure.

### Quantitative Bottlenecks: Extraction, AC Blowup, and Schedule Blindness

Basis: `documentation` + `source` + `execution`.

- **AC Combinatorics (`[real measurement]`):** Saturating an $n$-term sum under $(x+y)=(y+x)$ and associativity generates $2^n - 1$ e-classes (`egg 0.11.0`: `15` classes / `63` nodes / `123 µs` at $n=4$ $\to$ `202` classes / `2,627` nodes / `3,593 µs` at $n=7$; deterministic Python `Probe A`: `127` classes / `1,939` nodes / `181.08 ms` uncapped vs. `49` classes / `154` nodes / `1.29 ms` under Cranelift `5/5` caps).
- **Extraction Hardness & Solvers:** Monotone circuit treewidth DP (`arXiv:2408.17042`) runs in $2^{O(w^2)} \mathrm{poly}(w, n)$ (`ms`–`s` for $w \le 8$, hitting a wall at $w \gtrsim 12$; source audit of `circuit.rs:69-72` uncovered a spurious self-loop bug in `contract_edge_remove_out`). `SmoothE` (ASPLOS 2025) takes `4.6–42.4 s` on A100 GPUs; `e-boost` (`arXiv:2508.13020v2`) achieves `558×` over vanilla ILP / `138×` over ASPLOS'25 `SmoothE` (`19.04%` lower cost) yet still hits `3,599–3,601 s` on `73k–1.2M`-node multipliers (`mul128`/`mul48`).
- **Register-Pressure Blindness (`Probe B`):** On symmetric $W=8$ dual-reduction DAGs, DAG sharing cuts ops `1.68×` (`47` vs. `79` tree ops), yet naive postorder DFS spills (`peak_regs = 12` vs. `7` under schedule-aware interleaving), corroborated by Cranelift `#6159`/`#6260`/`#8959`.

### Formal Assurance, Poison Refinement, and Three Non-Dominated Regimes

Basis: `source` + `[kernel-checked proof]` (`google/zerocopy:reference@8fcbe48eb10bfac0016dec083c05f19caf265e90`).

- **Built-In Checker Failures (`source`):** `egg/src/explain.rs:368-442, 780-856` returns `true` (fail-open) on missing rules, `get_pattern_ast() == None`, and `union_trusted`; `egglog`'s `ProofStore` runs in unverified Rust; `Crocus`/`VeriISLE` excludes `vector`/`atomics`/`i128`/skeleton passes and trusts unverified Z3/CVC5 (`~4 min` on `1,054` rules); `eggcc/proofs/proofs.v` is `240` LOC of Coq on a toy AST without `Load`/`Store` or `Statewalk DP`.
- **Poison & `freeze` Decomposition (`[kernel-checked proof]` Lean `v4.34.1`):** `symmetric_eclass_poison_unsound` proves symmetric e-classes containing `x * 0` and `0` allow backward `0 -> poison * 0`. Soundness requires separating symmetric `BiEqRule` from forward-only `DirRefineRule` (`⊑`), plus `isFreezeFree` ancestor guards over shared `let`-DAGs.
- **DAG Certificates & Reflection (`[real measurement]`):** `let`-shared `TreeExplanation` cuts depth `d=6` `dup^d` proof size `114.3×` (`10` steps / `2,537 B` vs. `319` flat steps / `289,986 B`), checked by a closed 5-constructor `CongruenceDag` kernel checker in `<0.5 ms` via Lean 4's `!has_fvar` GMP/WHNF fast path (`type_checker.cpp:1093, 1181`) under `{propext, Classical.choice, Quot.sound}`.
- **Three Non-Dominated Regimes:** (A) Fast JIT/AOT (`aegraph` + CFG skeleton + decoupled `ISLE`/`regalloc2` + post-pass TV + `CongruenceDag`); (B) Domain/Pure Superoptimization (`RVSDG`/`Slotted` + `Statewalk DP`/`Guided EqSat` + per-kernel refinement certs); (C) Hybrid Verified Systems Compiler (global `aegraph` + selective superoptimization + decoupled TV + kernel certificate replay).

## Boundaries

- **Literature survey scope (`not examined`):** Systems known only through published papers (`SEER`, `TENSAT`, `Glenside`, `SpEQ`, `ROVER`, `E-Syn`, `Diospyros`, `Isaria`, `Ruler`, `Caviar`, `Szalinski`, `SmoothE`, `e-boost`, `Tamagoyaki`, `Souper`, `Hydra`) were synthesized from published papers/preprints rather than independently benchmarked on local hardware; direct source audits and probes cover `egg 0.11.0`, `egglog`, `Cranelift aegraph`/`rustc_codegen_cranelift`, `eggcc`, `DialEgg`, `egg-extraction-gym`, `VeriISLE`, and `Hydride`.
- **Open engineering gaps (`unknown`):** Sub-millisecond register-pressure-aware DAG extraction, scalable alias-partitioned `MemorySSA`/separation-logic tokens in `egglog`, unifying forward `aegraph` GVN with backward target ISel (`wasmtime#8529`/`#7321`), and inductive loop EqSat remain open problems.

## Evidence

- **Primary archived survey:** [support/egraph_optimizing_compilers_literature_survey.md](support/egraph_optimizing_compilers_literature_survey.md) (`347` lines, 56 references, observed `2026-11-23`).
- **Underlying corpus reports (`google/zerocopy:reference@8fcbe48eb10bfac0016dec083c05f19caf265e90`):** `10` indexed reports covering backend representations, `egg 0.11.0` DAG vs. flat proof benchmarks, `CongruenceDag`, `aegraph` dominance/LICM/`vtable_memflags`, `Twee`/`CeTA`/`circuit.rs:72`, `SideCondCert`/`isFreezeFree`, `VeriISLE`/`MiniMach`, IR comparisons, shift/undef/freeze peepholes, and translation validation.

## Revalidation

1. Inspect newer upstream commits in `bytecodealliance/wasmtime` (`cranelift/codegen/src/opts/*.isle`, `egraph/`), `egraphs-good/egglog`, and `rust-lang/rustc_codegen_cranelift` (`vtable.rs`) to check whether `wasmtime#8529` or `vtable_memflags()` `set_can_move()` have been resolved.
2. Re-run `glenn-sun/egg-extraction-gym` or `eggcc` benchmarks if evaluating updates to `circuit.rs:69-72` or `schedule.rs` (`memory.egg` / `(repeat 5 ...)`).
