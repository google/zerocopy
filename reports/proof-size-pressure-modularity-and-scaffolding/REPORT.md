# Size-Pressure, Kernel-Cost Discipline, and Deterministic MIR Scaffolding for Modularity and Upgrade Resilience

## Summary

Prompting or constraining agents to make Lean 4 proofs, verification skills, and Rust/Lean code "smaller" produces **radically different architectural outcomes depending on what size metric is minimized** (`Rissanen 1978`, `Ousterhout 2021`, `arXiv:2510.15700`, `arXiv:2605.20244`, `arXiv:2606.03743`, and controlled experiments on `google/zerocopy` and `leanprover/lean4:v4.34.1`):

1. **Naive source-line size pressure backfires into a `9.45x–10.01x` `.olean` and `2.88x` replay-latency blowup (`Proof` Tasks A & C) and unreadable code (`Task B-Rust` & `Task B-Lean`):** Optimizing purely for short source lines compresses `Task A` (`zerocopy/proofs/04_substantive_and_frombytes_markers`) from `256` LOC to `32` LOC and `Task C` (`alignment` 4-function crate) from `599` LOC to `86` LOC, **while expanding `Proof.olean` to `1,358,416` B (`10.01x` vs `arm_perf`) and `2,573,776` B (`9.45x` vs `arm_perf`)**, materializing `151` and `220` hidden `_private.*.match_*.eq_*`/`.splitter` constants, inflating `module_union_dag` `6.63x–9.38x`, nearly tripling isolated `Lean.Kernel.Environment.replay` latency (`671.00 ms` vs `232.59 ms` in `arm_perf`, `2.92x` vs `230.01 ms` in `arm_base`), and nearly doubling authoring time (`41 min` vs `23.7 min` on `Task C`). On non-proof Rust (`cargo_request`), raw brevity deleted every rationale comment (`6 -> 0`), compressed lines up to `501` columns (`25` lines `> 100` cols), and collapsed function names (`rej`, `walk`, `tf`).
2. **Naive `.olean`/DAG minimization *without* kernel-time pressure hits two distinct Goodhart traps:**
   - **Computational WHNF reduction (`Probe R2-A`):** Replacing structural induction with `by rfl` over nested `checkGrid` (`N=64, cols=80`) keeps source LOC (`10`), `.olean` (`34,352` B, `0.71x`), `module_union_dag` (`205`, `0.44x`), and `sum_val_tree` (`473`, `0.28x`) flat while driving cold compilation `10.0x` slower (`1,229.3 ms` vs `122.4 ms`), exploding isolated kernel replay **`276.4x`** (`477.42 ms` vs `1.73 ms`), and failing on `maxRecDepth` at `N=128`, whereas structural induction executes in $O(1)$ (`140.4 ms` / `2.76 ms` even at $N=100{,}000$).
   - **Implicit `Expr` tree bombs behind clean DAGs (`Task C` `arm_struct`):** Nesting `erw` subproofs inside deep `Executes.next` steps kept `arm_struct` at `527,160` B `.olean` and `13,125` unique DAG nodes while generating **`120,286,239` unfolded `Expr` tree nodes** (hitting the `10^8` per-declaration measurement cap). Binding intermediate states (`let s1 := mkState ...; .next (next := s1)`) in `arm_perf` (`126,247`) and `arm_skillv3` (`105,789`) cuts tree nodes **`953x–1,137x`**.
3. **Structured Pass-1 modularity + kernel-cost discipline simultaneously improves source and kernel metrics (`Probe R2-C` & `R2-D`):**
   - Factoring two `> 60`-line Pass-1 `Anneal.PureLift.BlockCfg` proofs (`modular_block_cfg_loop_sound` `126L -> 39L`; `cfg_certificate_step_sound` `100L -> 37L`) via shared helper lemmas (`wrapJump_partial_sound` `19L`, `branchJump_partial_sound` `26L`, `returned_step_sound` `11L`, `continuing_ret_step_sound` `30L`) cut non-blank file LOC (`1,513 -> 1,445`, `-4.5%`), `.olean` size (`2,413,264 -> 2,343,696` B, `-2.88%`), `module_union_dag` (`48,584 -> 46,487`, `-4.32%`), and **kernel replay latency (`303.94 -> 220.45 ms`, `-27.5%`)**.
   - Updating skill guidance (`Skill v3` in `Probe R2-D`) to promote bundled `Anneal.BitVecArith` imports, single-pass `WellFormed ∧ ReturnsTotal` proofs, `let s_k` state bindings, zero `simp`-splitter AST tactics, and identity-keyed body lookup (`findEntry`) eliminated `Classical.choice` (`["propext", "Quot.sound"]`), cut `sum_val_tree` **`1,137x`** (`120.29M -> 105.79K`), cut `Proof.olean` `-24.5%` vs `Skill v2` (`527,160 -> 397,960` B), and achieved the first manual **`P2` declaration-order survival** (`rc=0`, untainted).
4. **Deterministic MIR scaffolding (`AutoScaffold`) outperforms manual size discipline on upgrade resilience (`0% -> 100%` survival on `P1`, `P2`, and `P3`):** All four manual arms (`arm_base`, `arm_raw`, `arm_struct`, `arm_perf`) broke (`0/12`) under three realistic semantics-preserving Rust changes (`P1` extra local in `from_elem_count`, `P2` `PointerMetadata` impl swap, `P3` `let inv = !mask` in `align_down_mask`), and `arm_skillv3` survived `P2` yet broke on `P3`. Generating identity-keyed straight-line `AutoScaffold.lean` (`TargetRole::Proof`, zero TCB growth) directly from captured MIR reduced hand-written `zerocopy/proofs/01..04` LOC by **`82.9%` (`573 -> 98`)** and `Task C` hand `Proof.lean` to **`17` non-blank LOC** (`-94.1%` vs `arm_perf`), passing **`baseline + P1 + P2 + P3` (`rc=0`, untainted, `0` hand-proof edits)**.

## Applicability

- **Examined code and tool versions (`source` + `execution`):**
  - `google/zerocopy` at `a68641199cdfa99f96cb62f0cde921c9d36bfb22` (`anneal` `0.2.0-alpha.8`: baseline census of `anneal/theory/`, `anneal/correspondence/`, `zerocopy/proofs/{01..04}`; `cargo-anneal` / `anneal-rustc-capture` under `nightly-2026-05-31`; `verify.rs` `cargo_request`; `Task A` & `Task C`) and `3f9d7d7048138494e17e419557f08e218fe36bba` (`anneal/skills/proof-scaling/SKILL.md`, `anneal/trusted/cargo-anneal/skills/cargo-anneal/SKILL.md`, and `Anneal.PureLift.BlockCfg`, whose `.lean` source matches `a68641199c` with zero diff across `anneal/{theory,correspondence}` and `zerocopy/proofs`).
  - Pinned Lean 4 toolchain `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`, `-Ddebug.skipKernelTC=false`), sandboxed `linux_bwrap` Elaborator Containment (`ExecSeal`).
  - `graydon/millipede` at `4f13d3980a5570177a774e63cfbc95e652dd3cde` (`Millipede/Meta/Burden.lean` theorem-length distribution and `Target/Budget.lean` / `Meta/Elab.lean` kernel scaling analysis).
- **Transfer scope:** Quantitative `.olean`, `Expr` DAG/tree, and perturbation findings apply directly to tactic- and term-mode Lean 4 program proofs over deeply embedded semantics (such as `Trusted.MirSemantics`, `Anneal.MirWp`, and `Anneal.PureLift`). The MDL/anti-golf principles generalize across proof assistants (`Isabelle`, `Rocq`/`Coq`), SMT verifiers (`Verus`/`Dafny`), and general systems code (`Rust`/`Lean 4`), subject to language-specific kernel/solver mechanisms documented below.

## Findings

### 1. Prior Art and Structural Failure Modes of Single-Objective Size Pressure

Basis: literature + source (`graydon/millipede@4f13d3980a5570177a774e63cfbc95e652dd3cde`, `google/zerocopy@a68641199cdfa99f96cb62f0cde921c9d36bfb22`).

1. **Multi-objective tension in proof refactoring (`arXiv:2510.15700`, `arXiv:2605.20244`, `arXiv:2606.03743`):** `ProofOptimizer` (`arXiv:2510.15700`) shows RL/iteration on Lean length cuts competition proofs `49%–87%`, while `Lean Refactor` (`arXiv:2605.20244`) and `Proof-Refactor` (`arXiv:2606.03743`) establish that naive length proxies trade away compile cost (heartbeats), library-version robustness, helper reusability, and readability unless decomposed into explicit extraction, signature design, helper proof, and repair stages. Library learning (`Peano` `arXiv:2211.15864`, `LEGO-Prover` `arXiv:2310.00656v3`, `Stitch` `arXiv:2211.16605`, `LILO` `arXiv:2310.19791`) and proof repair (`CoqGym` `arXiv:1905.09381`, `PUMPKIN Pi` `arXiv:2010.00774`, `DSP` `arXiv:2210.12283`, `Mariposa` `DOI: 10.34727/2023/isbn.978-3-85448-060-0_26`) similarly show stability requires minimal premise/trigger sets and explicit proof-term structure.
2. **Minimum Description Length (`Rissanen 1978`, `DOI: 10.1016/0005-1098(78)90005-5`) and Adapter Conservation (`Ousterhout 2021`, corpus report `concept-design-deep-modules-felleisen-expressiveness-and-adapter-conservation`):** Total complexity is $L(M) + L(D \mid M)$, yielding a U-shaped modularity optimum: under-abstraction duplicates boilerplate inside $L(D \mid M)$, whereas splitting cohesive logic into single-use shallow wrappers inflates vocabulary/interface cost $L(M)$ without hiding invariants.
3. **Anneal vs. `Millipede` theorem-size census (`source` + `execution`):** Using `strip_lean_comments` + top-level `theorem`/`lemma` scanning (`support/verify_size_pressure_probes.py --zerocopy-dir`) on `google/zerocopy@a68641199c` (`unchanged at 3f9d7d7048`):

| Codebase / Slice | Files | Non-blank LOC | Theorems | Median LOC | Mean LOC | p90 | p99 | Max LOC | `<= 5L` | `<= 15L` | `> 60L` (`count`) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| **`Millipede`** (`4f13d398`) | `195` | `81,070` (raw) | `3,332` | `6.0` | — | `25` | `86` | `247` | `44.7%` | `82.4%` | `2.4%` (`79`) |
| **`anneal/theory/`** | `58` | `51,416` | `2,310` | `8.0` | `16.29` | `37` | `114` | `319` | `35.8%` | `69.8%` | `4.4%` (`102`) |
| **`anneal/correspondence/`** | `16` | `23,587` | `785` | `14.0` | `29.24` | `70` | `213` | `907` | `26.0%` | `54.3%` | **`11.8%` (`93`)** |
| **`zerocopy/proofs/01..04`** | `4` | `468` | `74` | `4.0` | `6.04` | `15` | `28` | `28` | `59.5%` | `91.9%` | `0.0%` (`0`) |

Two distinct burdens appear: `anneal/correspondence/` and `anneal/theory/` exhibit heavy long-theorem tails (`907L` `evalRvalueIntoPlace_ref_eq`, `319L` in `theory/`), whereas `zerocopy/proofs/01..04` has compact individual lemmas (`median 4.0L`, `0% > 60L`) yet repeats structural MIR/`BodiesVerified` wiring across every target crate. Notably, `Millipede` itself (`Meta/Burden.lean:23-146`) tracks theorem counts strictly as a design signal (`CLAUDE.md` 60-line guideline), yet hit Lean `v4.35.0` kernel bottlenecks (`Sel.potential` array reduction and cubic `joinStmt` proofs), showing small source LOC never guarantees small kernel terms or fast checking.

### 2. Controlled Multi-Arm Proof Experiments (`Task A` & `Task C`) and Kernel Profiling (`Env.moduleData`)

Basis: `execution` (`lean v4.34.1`, `cargo-anneal 0.2.0-alpha.8`, 3-round interleaved round-robin profiling via `env.header.moduleData`, explicitly matching both `.thmInfo` and `.defnInfo` so `private` module constants are never skipped, plus 3-run `Lean.Kernel.Environment.replay`).

Four manual prompting/skill regimes plus two deterministic `AutoScaffold` regimes were evaluated on unmodified `zerocopy/proofs/04_substantive_and_frombytes_markers` (`Task A`, 8 MIR bodies) and a fresh `alignment` crate (`Task C`, 4 `u64`/`bool` functions: `align_down_mask`, `align_bits_in_mask`, `is_aligned_mask`, `align_down_page`):

| Task | Arm | Hand LOC (NB) | Max Col | `Proof.olean` (B) | Compiled Decls (`thm`/`def`) | Module Union DAG | Sum Value Tree | Elab+TC Med (`ms`) | Isolated Replay Med (`ms`) | E2E `proof_and_audit` (`ms`) | Axioms |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| **Task A** | `arm_base` (baseline) | `256` (`240`) | `85` | `249,376` (`1.84x`) | `17` (`13t,4d`) | `5,779` | `95,740` | `2,603.6` | `759.78` | **`26,292`** | `propext` |
| **Task A** | `arm_raw` (min LOC) | **`32`** (`32`) | **`759`** | **`1,358,416` (`10.01x`)** | **`151`** (`120t,31d`) | **`28,444` (`9.38x`)** | `210,112` | `3,087.8` | `1,004.17` | `26,428` | `propext` |
| **Task A** | `arm_struct` (`Skill v2`) | `240` (`219`) | `102` | `576,000` (`4.25x`) | `95` (`76t,19d`) | `10,943` | `104,368` | **`2,272.6`** | `1,103.92` | `30,254` | `propext, Quot.sound` |
| **Task A** | `arm_perf` (kernel size+time) | `123` (`113`) | `115` | **`135,672` (`1.00x`)** | **`8`** (`7t,1d`) | **`3,034` (`1.00x`)** | **`26,661` (`1.00x`)** | `2,462.6` | **`648.76` (`1.00x`)** | `27,663` | `propext` |
| **Task A** | `scaffold_v2` (`Auto` + hand) | **`44`** + `208` gen | — | `54,056` + `254,736` | `4` + `66` | `1,122` + `4,725` | `9,433` + `142,902` | — | `866.93` + `333.01` | **`25,230`** | `propext` |
| **Task C** | `arm_base` (baseline) | `599` (`568`) | `103` | `792,824` (`2.91x`) | `63` (`53t,10d`) | `19,121` | `513,490` | **`799.6`** | **`230.01`** | **`24,031`** | `propext, Choice, Quot` |
| **Task C** | `arm_raw` (min LOC) | **`86`** (`86`) | **`437`** | **`2,573,776` (`9.45x`)** | **`220`** (`169t,51d`) | **`45,082` (`6.63x`)** | `981,569` | **`1,843.7`** | **`671.00` (`2.88x`)** | `42,124` | `propext, Quot.sound` |
| **Task C** | `arm_struct` (`Skill v2`) | `436` (`402`) | `115` | `527,160` (`1.94x`) | `44` (`31t,13d`) | `13,125` | **`120,286,239` (cap!)** | `1,177.5` | `417.19` | `34,204` | `propext, Choice, Quot` |
| **Task C** | `arm_perf` (kernel size+time) | `307` (`289`) | `156` | **`272,360` (`1.00x`)** | **`15`** (`15t,0d`) | **`6,803` (`1.00x`)** | **`126,247` (`1.00x`)** | `1,038.5` | `232.59` | `29,136` | `propext, Choice, Quot` |
| **Task C** | `arm_skillv3` (`Skill v3`) | `517` (`477`) | **`100`** | `397,960` (`1.46x`) | `53` | `8,990` (`1.32x`) | **`105,789` (`0.84x`)** | — | `941.23` (`2,969.8` noisy) | `38,051` | **`propext, Quot` (`0` Choice)** |
| **Task C** | `scaffold_v3` (`Auto` + hand) | **`17`** + `331` gen | — | **`39,632`** + `279,968` | **`1`** + `37` | **`747`** + `6,385` | **`7,967`** + `110,498` | — | **`71.42`** + `147.09` | **`25,303`** | `propext, Choice, Quot` |

*(Derived + execution mechanism checks:*
1. **Why naive source-LOC compression explodes `.olean` (`arm_raw`):** Using `simp only` or compact local macros (`sl`/`sa`/`aw` on `Task C`) over huge pattern-matching definitions (`MirTy.beq`, `IntWidth.beq`, `evalStep`, `evalRvalue`) forces Lean 4 to elaborate and serialize hundreds of private equational/matcher helper constants (`_private.*.match_*.eq_*` and `.splitter`), exploding `.olean` size `9.45x–10.01x` and nearly doubling `Task C` proof authoring time (`41 min` vs `23.7 min` for `arm_struct`) due to collapsed error localization inside packed `<;>` chains and macros. Replacing `simp only` with explicit `unfold ...; rw [ite_bool_false ...]` inside `AutoScaffold v2` independently confirmed the exact causal mechanism, shrinking `AutoScaffold.olean` by **`-83.1%` (`1,503,864 -> 254,736` B, `228 -> 66` decls)**.
2. **Why DAG size hides `Expr` tree bombs (`arm_struct` vs `arm_perf`/`arm_skillv3`):** `arm_struct` (`Task C`) kept `.olean` small (`527` KB) and DAG small (`13,125`), yet nested `erw [show evalPrimitiveOperand ...]` subproofs inside consecutive `Executes.next` steps, hitting the `10^8` per-declaration unfolded tree cap (`120,286,239`). Naming intermediate states (`let s1 := mkState 0 1 ...; .next (next := s1)`) in `arm_perf`, `arm_skillv3`, and `AutoScaffold v3` keeps `sum_val_tree` at **`105.8K–126.2K`** (`953x–1,137x` lower). Note: a profiler checking only `.olean` bytes or `ConstantInfo.value?` (which returns `none` for `.thmInfo`) misses both `private` matcher bloat and unfolded tree bombs; `moduleData` matching both `.defnInfo` and `.thmInfo` is necessary.
3. **Why `Skill v3` fixed `Skill v2`'s defects and why runtime identity lookup still costs replay (`arm_skillv3` vs `arm_perf`):** `Skill v2` banned general imports, causing `arm_struct` and `arm_perf` to omit `Anneal.BitVecArith` and re-prove `nat_xor_compl` from scratch (`Classical.choice`). `Skill v3` explicitly promoted `Anneal.*` reuse while pruning unused `Init.*` modules, dropping `Classical.choice` (`["propext", "Quot.sound"]`). However, `arm_skillv3` resolved bodies inside Lean via runtime `findEntry` (`foldr` + `stringBeq`) plus `by decide` on `Nat.pow 2 128`, costing `941.23 ms` isolated replay (`[1019.7, 941.2, 915.7] ms`, `Anneal.BitVecArith` itself only `161.2 ms`; `2,969.8 ms` during concurrent workspace audit runs), whereas `AutoScaffold v3` shifts identity resolution out of Lean into deterministic Rust/Python scaffold generation (`71.42 ms` hand replay + `147.09 ms` scaffold replay).* )

### 3. The WHNF / `by rfl` Goodhart Failure Mode (`Probe R2-A`)

Basis: `execution` (`support/verify_size_pressure_probes.py --run-whnf-probe --lean v4.34.1`, `r2a_whnf_goodhart.json`, 3-run medians).

Optimizing solely for small source LOC, `.olean` bytes, and `Expr` DAG/tree size without a kernel-replay ceiling systematically rewards computational `by rfl` / `decide` proofs that push work into Lean's kernel weak-head normal-form (`whnf`) reducer:

| Case (`checkGrid cols rows` / `boundedCheck n`) | Exit (`rc`) | Source LOC | `.olean` (B) | Decls | Module Union DAG | Sum Value Tree | Cold Compile Med (`ms`) | Isolated Replay Med (`ms`) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `grid_rfl_2x80` (`by rfl`) | `0` | `10` | `34,336` | `11` | `205` | `473` | `155.5` | `6.933` |
| `grid_rfl_8x80` (`by rfl`) | `0` | `10` | `34,336` | `11` | `205` | `473` | `258.9` | `56.351` |
| `grid_rfl_32x80` (`by rfl`) | `0` | `10` | `34,352` | `11` | `205` | `473` | `684.6` | `186.691` |
| `grid_rfl_64x80` (`by rfl`) | `0` | **`10`** (`0.56x`) | **`34,352`** (`0.71x`) | `11` | **`205`** (`0.44x`) | **`473`** (`0.28x`) | **`1,229.3`** (`10.0x`) | **`477.423`** (**`276.4x`**) |
| `grid_rfl_128x80` (`by rfl`) | **`1` (`maxRecDepth`)** | `10` | — | — | — | — | `1,228.5` (fail) | — |
| `grid_struct_64x80` (induction) | `0` | `18` (`1.00x`) | `48,680` (`1.00x`) | `18` | `462` (`1.00x`) | `1,708` (`1.00x`) | **`122.4`** (`1.00x`) | **`1.727`** (`1.00x`) |
| `grid_struct_100000x80` (`1,562x` larger) | `0` | `18` | `48,680` | `18` | `462` | `1,708` | **`140.4`** | **`2.763`** |
| `range_rfl_50` / `150` / `250` (`List.range`) | `0` / `0` / **`1`** | `6` | `18,792` | `2` | `64` | `88` | `132.8` / `179.7` / fail | `3.685` / `11.904` / fail |
| `range_struct_150` / `100000` (induction) | `0` / `0` | `22` | `51,488` | `8` | `738` | `3,378` | `137.4` / `183.7` | **`2.365`** / **`3.194`** |

Source LOC, `.olean`, `module_union_dag`, and `sum_val_tree` are invariant across $N$ under `by rfl` (`2x80..64x80`), yet kernel replay explodes **`276.4x`** at $N=64$ before hitting `maxRecDepth` at $N=128$, whereas structural induction remains $O(1)$ (`2.763 ms` at $N=100{,}000$). Combining **kernel time + `.olean` + DAG/tree + syntactic readability** prevents this Goodhart failure.

### 4. Non-Proof Refactoring (`Task B-Rust` & `Task B-Lean`) and Pass-1 Library Factoring (`Probe R2-C`)

Basis: `execution` (`bench_4arms_final.json`, `ab_metrics.json`, `r2c_blockcfg_results.json`).

1. **Non-proof Rust (`cargo_request` from `verify.rs@a68641199c`) & non-proof Lean (`stepBasicBlock`):**
   - On `Task B-Rust` (all passing 7 black-box `cargo test` checks): `arm_base` had `283` total LOC (`257` code, `6` comments, `10` fns, `26` branch tokens, `maxCol=112`); `arm_raw` (`69` LOC, `0` comments, `6` fns `error`/`io`/`tf`/`rej`/`walk`/`cargo_request`, `maxCol=501`, `25` lines `> 100` cols) destroyed readability; **`arm_struct`** (`269` total / `239` code LOC, `6` comments preserved, **`15` functions (`+50%`)**, **`20` branch tokens (`-23%`)**, unified `collect_files`, `unsupported_cargo`/`check_cargo` guards, `maxCol=104`) delivered cleaner decomposition without losing rationale comments.
   - On `Task B-Lean` (`stepBasicBlock` in kernel `by rfl`): `arm_raw` (`34` LOC, `maxCol=162`, `1` inline helper, `.olean=152,112` B, `6.28 ms` replay) stripped comments and compacted expressions; `arm_struct` (`110` LOC, `7` top-level helper `def`s, `maxCol=90`, `.olean=163,288` B, `7.87 ms` replay) paid small per-declaration serialization overhead vs `arm_perf` (`77` LOC, `1` inline `let stepTerm`, `.olean=149,208` B, `195.5 ms` compile, `4.83 ms` replay) — illustrating MDL/adapter conservation (`Task B-Lean`) when extracting single-use helpers.
2. **Pass-1 `Anneal.PureLift.BlockCfg` refactoring (`Probe R2-C`, `@3f9d7d7048`, `prelude`, zero `omega`/`by_cases`/`Classical`):** Refactoring two `> 60`-line multi-case theorems (`modular_block_cfg_loop_sound` `126L -> 39L` via `wrapJump_partial_sound` `19L` + `branchJump_partial_sound` `26L`; `cfg_certificate_step_sound` `100L -> 37L` via `returned_step_sound` `11L` + `continuing_ret_step_sound` `30L`) deduplicated identical `jumpWrapped`/`convergedJump` and `continuing`/`guardedContinuing` continuations and **improved every metric simultaneously**:
   - Non-blank file LOC: `1,513 -> 1,445` (`-68` LOC, `-4.5%`; total `1,558 -> 1,494`)
   - `.olean` bytes: `2,413,264 -> 2,343,696` B (`-69,568` B, `-2.88%`)
   - `module_union_dag`: `48,584 -> 46,487` (`-2,097`, `-4.32%`) and `sum_val_tree`: `553,375 -> 549,213` (`-4,162`)
   - Cold compile: `3,184.8 -> 3,177.9 ms`; **isolated kernel replay: `303.94 -> 220.45 ms` (`-27.5%`**, non-overlapping `[288.4, 319.8, 303.9]` vs `[220.5, 258.8, 218.4]`).

### 5. Upgrade Resilience Matrix (`P1`–`P3`) and Deterministic `AutoScaffold` (`Experiment C2` & `Probe R2-B`)

Basis: `execution` (`cargo anneal verify`, untainted `selected_unit_verified` in `linux_bwrap`).

Three semantics-preserving Rust edits tested whether compact proofs survive realistic code churn without manual proof edits:
- **`P1` (`zerocopy/src/lib.rs`, Task A):** Insert `let count_copy = elems; count_copy` inside `<usize as PointerMetadata>::from_elem_count`.
- **`P2` (`zerocopy/src/lib.rs` & `Task C`, Task A & C):** Reorder `impl PointerMetadata` blocks (`Task A`) or move `align_down_page` ahead of `align_down_mask` (`Task C`).
- **`P3` (`Task C` `lib.rs`):** Insert `let inv = !mask; addr & inv` inside `align_down_mask`.

| Regime | `Task A` `P1` (`from_elem_count` copy) | `Task A` `P2` (`PointerMetadata` swap) | `Task C` `P2` (fn reorder) | `Task C` `P3` (`let inv = !mask`) | Hand `Proof.lean` Churn |
|---|---|---|---|---|---|
| `arm_base` / `arm_raw` / `arm_struct` / `arm_perf` | `0/4` (`rc=1`) | `0/4` (`rc=1`) | — | `0/4` (`rc=1`) | Requires manual rewrite |
| `arm_skillv3` (`Skill v3` + `findEntry`) | — | — | **`PASS` (`rc=0`, untainted)** | `FAIL` (`rc=1`) | `0` edits on `P2`, manual rewrite on `P3` |
| `scaffold_v2` (identity + copy chain, `Task A`) | **`PASS` (`rc=0`, `0` hand edits)** | **`PASS` (`rc=0`, `0` hand edits)** | — | — | `44` hand LOC (`-83.6%` vs `269` Suite 04) |
| `scaffold_v3` (identity + `u64`/bool MIR, `Task C`) | — | — | Identity-keyed (`id_<slug>`) | **`PASS` (`rc=0`, `0` hand edits)** | **`17` hand LOC** (`-94.1%` vs `arm_perf`) |

Across all four unmodified `zerocopy/proofs/01..04` suites, deterministic `AutoScaffold` v1 cut hand-written `Proof.lean` LOC from **`573 -> 98` (`-82.9%`: Suite 01 `146 -> 25`, Suite 02 `96 -> 25`, Suite 03 `62 -> 14`, Suite 04 `269 -> 34`)**, while `scaffold_v2` (`44` hand LOC) added full `P1 + P2` invariance and `scaffold_v3` (`17` hand LOC) extended `0`-edit invariance to `P3` bitwise/comparison arithmetic with `0` TCB increase (`AutoScaffold.lean` checked inside `TargetRole::Proof`).

## Boundaries

- **`arm_perf` on `Task B-Rust` (`not examined`):** `arm_perf` was run on `Task A`, `Task C`, and `Task B-Lean`, not on `Task B-Rust`.
- **`Task A` & `Task C` `P2` cross-check (`not examined`):** `P2` was tested directly on all 4 manual arms + `scaffold_v2` in `Task A` (`0/4` vs `1/1`), and on `arm_skillv3` in `Task C` (`rc=0`), whereas `scaffold_v3` was directly executed on `Task C` `baseline` and `P3` (its `P2` behavior follows by identical `id_<slug>`/`body_<slug>` generation and is checked structurally on `capture.json` fixtures in `support/verify_size_pressure_probes.py`).
- **Scope of deterministic `AutoScaffold v2/v3` (`unsupported` outside straight-line prototype):** The prototype lowers 1-block straight-line `isize`/`u64`/`bool` MIR chains (`storage_live`, `storage_dead`, `assign(use/unary not/binary bit_and/binary eq)`, `ret`). Multi-block control flow, loops (`LoopInv`), mutable-reference borrows, and aggregate/enum matching require either widening the deterministic MIR lowering pass or proving mathematical postconditions in manual `Proof.lean` atop scaffolded entry/frame lemmas.
- **Host contention caveat on isolated replay (`execution` qualification):** `arm_skillv3`'s initial `eval_r2d_skillv3.py` replay (`2,969.76 ms`) ran alongside unrelated background verification builds on the shared host; isolated re-measurement of the identical `Proof.olean` recorded `[1019.7, 941.2, 915.7] ms` (`median 941.2 ms`), leaving a real `4.0x` replay gap vs `arm_perf` (`232.6 ms`) attributable to `findEntry` `stringBeq` unfolding and `by decide` on `2^128`.
- **No CI hard gate on small line counts (`known not to apply`):** Following `Millipede` Decision 18 (`Burden.lean`) and `Probe R2-A`, gating CI on theorem line counts or `.olean` size alone encourages golfed `by rfl` / `<;>` / `simp only` splitter bombs and penalizes legitimate boundary abstraction. Multi-metric budgets (`.olean`, `sum_val_tree`, kernel replay time, and syntactic/structural review) plus `AutoScaffold` + identity binding are required.

## Evidence

- **Anneal codebase & proofs (`source` + `execution`):**
  - `google/zerocopy@a68641199cdfa99f96cb62f0cde921c9d36bfb22`: `zerocopy/proofs/{01_usize_pointer_metadata,02_unit_pointer_metadata,03_macros_unsafe,04_substantive_and_frombytes_markers}/{Proof.lean,Spec.lean,request.json}`, `anneal/trusted/cargo-anneal/src/verify.rs` (`cargo_request`), and all `.lean` files under `anneal/theory/` (`58` files) and `anneal/correspondence/` (`16` files).
  - `google/zerocopy@3f9d7d7048138494e17e419557f08e218fe36bba`: `anneal/theory/Anneal/PureLift/BlockCfg.lean` (`lines 415–522`, `653–778`, `1171–1270`), `anneal/theory/Anneal/MirWp/{MirWp.lean,Execution.lean,Scalars.lean}`, `anneal/theory/Anneal/BitVecArith.lean`, `anneal/skills/proof-scaling/SKILL.md`, `anneal/trusted/cargo-anneal/skills/cargo-anneal/SKILL.md`.
- **Lean toolchain & external compiler baseline (`source` + `execution`):**
  - `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, `Lean/Replay.lean` `Lean.Kernel.Environment.replay`, invoked with `-Ddebug.skipKernelTC=false`).
  - `graydon/millipede@4f13d3980a5570177a774e63cfbc95e652dd3cde` (`Millipede/Meta/Burden.lean:23-146`, `Target/Budget.lean:119-184`, `Meta/Elab.lean:926-1005`).
- **Preserved self-contained verification support (`support/verify_size_pressure_probes.py`):** Implements the comment-stripping Lean theorem-length scanner, deterministic identity-keyed `u64`/`bool` MIR stepper regression checks across `baseline`/`P2`/`P3`, module-exact `.olean` + `env.header.moduleData` (`Expr` DAG/tree + `Lean.Kernel.Environment.replay`) profiler, and the live `Probe R2-A` `checkGrid` WHNF Goodhart scaling benchmark.

## Revalidation

1. **Zero-dependency static check (`< 0.5 s`, Python 3.10+ stdlib):**
   ```bash
   python3 -I -B reports/proof-size-pressure-modularity-and-scaffolding/support/verify_size_pressure_probes.py --check-static
   ```
   Verifies `STATIC_SELFTEST_OK` (nested-comment theorem length scanner + identity-keyed symbolic `u64`/`bool` MIR lowering invariant across `P2` body reordering and `P3` `let inv = !mask` extra local).

2. **Live Anneal burden census on any `google/zerocopy` checkout (`~0.5 s`, stdlib only):**
   ```bash
   python3 -I -B reports/proof-size-pressure-modularity-and-scaffolding/support/verify_size_pressure_probes.py --zerocopy-dir /path/to/zerocopy
   ```
   Recomputes file counts, non-blank LOC, theorem counts, `median`/`mean`/`p90`/`p99`/`max`, and `> 60L` heavy-tail offenders for `anneal/theory/`, `anneal/correspondence/`, and `zerocopy/proofs/`.

3. **Live Lean `v4.34.1` WHNF Goodhart + kernel replay probe (`~10 s`, requires `--lean` binary):**
   ```bash
   python3 -I -B reports/proof-size-pressure-modularity-and-scaffolding/support/verify_size_pressure_probes.py \
     --run-whnf-probe --lean /path/to/lean
   ```
   Reproduces `grid_rfl_{2,8,32,64}x80` exponential replay inflation vs `grid_rfl_128x80` `maxRecDepth` failure and $O(1)$ `grid_struct_{64,100000}x80` scaling directly against `lean -Ddebug.skipKernelTC=false` and `Lean.Kernel.Environment.replay`. Passing `--check-static` and `--run-whnf-probe` revalidates the MIR identity-stepper invariants, theorem scanner, and WHNF Goodhart mechanism; re-evaluating `Task A`/`Task C` end-to-end requires running `cargo anneal verify` on the target crates.
