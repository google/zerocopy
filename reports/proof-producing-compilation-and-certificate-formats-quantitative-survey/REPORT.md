# Quantitative Survey of Proof-Producing Compilation and Certificate Formats

## Summary

Compilers that justify individual compilations with machine-checkable artifacts
divide into five architectural regimes with sharply different certificate-size
ratios, generation/checking costs, trusted computing bases (TCBs), and
real-code acceptance rates:

1. **Hint-Free Verified Symbolic Validators** (Tristan & Leroy POPL 2008/2009/
   PLDI 2010; CompCert RTLpath/BTL without invariants): **`0x` external
   certificate bytes**, **`0%` generation overhead**, **`10%–35%` compile-time
   checking overhead**, **`98.5%–100%` acceptance** on structured intra-block /
   superblock passes (scheduling, lazy code motion, register allocation), and a
   zero-growth ITP kernel TCB via verified boolean reflection
   (`validate f f' = true -> forward_simulation f f'`).
2. **Light-Witness / Gluing-Invariant Relational Validators** (CompCert-KVX BTL
   `gluemap`, Crellvm `.hint` files, NeculaOracle PCC): **`0.10x–2.5x` of IR or
   code size** and **`1.6%–15%` generation overhead**. However, checking cost
   depends by three orders of magnitude on *how* the checker discharges local
   verification conditions: CompCert-KVX's hash-consed verified symbolic
   evaluator adds only **`15%–40%` compile-time overhead** with **`99.8%–100%`
   acceptance**, whereas Crellvm's general relational post-dropping validator
   runs **`330x–1,100x` slower than LLVM compilation** (`22.6` CPU-hours on
   SPEC CINT2006) and achieves **`78.1%` aggregate pass acceptance** (`65.5%`
   on `InstCombine`, `71.1%` on `GVN`, `88.2%` on `LICM`, `98.4%` on `SROA`).
3. **Uninstrumented Post-Hoc Translation Validators** (Necula GCC 2.91 TV,
   Tristan-Govereau-Morrisett LLVM Value-Graph TV, seL4 `graph-refine`,
   Alive2): **`0x` compiler-emitted hints**, shifting all discovery work to the
   validator. Necula's GCC validator runs at **`~4x` compile time** (`96%+`
   acceptance on SPECint95 / Linux 2.2), LLVM Value-Graph TV takes **`0.5–4.0 s`
   per function** (`67%` composite `-O2` acceptance, `68%–91%` single-pass),
   and seL4 `graph-refine` achieves **`100%` acceptance on ~600 kernel
   functions** at the cost of **`2–6` CPU-hours of external SMT solving** and
   `15 MB` of SMT-LIB2 VCs (`5x–20x` binary size).
4. **Proof-Producing Term Synthesis in Interactive Theorem Provers** (CakeML
   `Hol2min`, Fiat Cryptography, Rupicola, Vale, Cogent/AutoCorres): **`10x–100x`
   certificate-to-code size ratio** in kernel proof objects (`.vo` / HOL4
   theorems), **`0.5–90 s` per-function synthesis time**, **`0.5–10 s` kernel
   replay time**, and **`100%` acceptance** within domain-specific or
   source-annotated subsets.
5. **E-Graph Explanations and Propositional/SMT Proof Certificates** (`egg`
   `TreeExplanation`, DRAT, LRAT, Alethe/Carcara, `lean-smt`): DAG-shared
   e-graph certificates (`TreeExplanation` with `let` bindings) require only
   **`1–10` rewrite steps (`0.6–2.5 KB`)** and **`50–1,992 us` extraction time**,
   whereas unshared flat explanations (`FlatExplanation`) blow up exponentially
   (**`319` steps / `290.0 KB` vs. `10` steps / `2.5 KB` at shared DAG depth
   `6`**). For side conditions, LRAT (`cake_lpr`, `Std.Tactic.BVDecide`) checks
   in linear time at **`1.5x–4.0x` DRAT size**, and replacing raw `bv_omega`
   term reconstruction (`8,416` Lean `Expr` DAG nodes, `48.1 ms` kernel check)
   with a domain-specific algebraic wrapper lemma (`bv64_add_range_algebraic`)
   shrinks the kernel proof term to **`230` DAG nodes (`36.6x` smaller)** and
   accelerates kernel checking to **`0.78 ms` (`61.7x` faster)**.

## Applicability

This report consolidates and extends the corpus's prior certificate-kernel and
translation-validation packages (`translation-validation-certifying-compilation-and-pass-refinement-certificates`,
`deductive-proof-object-and-refinement-certificate-kernels-2013-2026`,
`pcc-tal-verve-foundational-certificate-kernels-1996-2016`,
`ebpf-certificate-verifying-kernels-and-verified-jits-2014-2026`, and
`smt-sat-alethe-carcara-and-numerical-proof-certificate-reconstruction`) into a
single quantitative reference across 17 compiler certification architectures.
All machine-readable metrics and primary-source coordinates are preserved in
`support/certificate_comparison_table.json`. Direct empirical measurements for
`egg 0.11.0` DAG vs. tree explanation blowup and Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`)
side-condition proof-term scaling were executed on an `x86_64-unknown-linux-gnu`
host (`Rust 1.99.1`, commit `58cf8f9c35b355199727627d07ae34a4e2846d67`).

## Findings

### 1. Master Quantitative Comparison across 17 Certificate Architectures

Basis: documentation + source + execution (for `egg 0.11.0` and Lean `v4.34.1`
probes) + derived (comparative ratios).

| System / Architecture | Certificate Format | Size vs. Code / IR | Generation Time | Checking Time | Trusted Base (TCB) | Optimization Coverage & Real-Code Acceptance |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Necula PCC (`Touchstone` / `Special J`) & Oracle PCC** (POPL 97, PLDI 98, PLDI 00, POPL 01) | Explicit `LF` $\to$ Implicit `LF_i` $\to$ bit-stream `Oracle` strings guiding nondeterministic Horn search | `LF`: `1.5x–4.0x`; `LF_i`: `0.30x–0.90x`; Oracle: **`0.10x–0.19x`** of native code (`12%–20%` on Java) | `1.2x–2.0x` of base compile time | `1.3–45 ms` per module (`O(|cert|)` for `LF_i`, `O(|VC trace|)` for Oracle) | `23 KLoC` C (`Touchstone`); **`2.4 KLoC` C + `1.5 KLoC` LF** (Oracle PCC; VCGen in TCB) | Regalloc, scheduling, LICM, bounds/null-check elimination; **100% acceptance** on safe compiler subset (type/memory safety only) |
| **TAL (`TALx86`) & Foundational PCC (`FPCC`)** (TOPLAS 99, PLDI 99, LICS 01/02) | Block register/stack types (`.tal` / binary TAL); FPCC: Coq/Twelf semantic derivations to ISA | Uncompressed: `1.0x–2.0x`; binary TAL: **`0.25x–0.45x`** of object code | `~1.3x` base compile time (`Popcorn`) | `<50 ms` syntactic TAL check; `1–10 s` FPCC Coq/Twelf check | `TALx86`: `~8 KLoC` OCaml + assembler; `FPCC`: **`~2.7 KLoC` LF/Coq** ISA spec + kernel | Closure conversion, SSA/CPS, regalloc, stack layout; **100% acceptance** for `Popcorn` output (safety only) |
| **Pnueli, Siegel & Singerman TV** (TACAS 98) | Cut-point map + data abstraction + per-cut invariants (`TLV` / `CVC` script) | `0.5x–2.0x` of IR text | `10–500 ms` per routine | `0.1–5.0 s` per routine (BDD/SMT) | Unverified C VCGen + `TLV`/BDD/SMT solver | Synchronous clock scheduling, scalarization, DCE (`SIGNAL` $\to$ C); **100% on single-loop reactive code** |
| **Necula GCC 2.91 Translation Validator** (PLDI 00) | Inferred cut-point simulation relation + conjunction of linear/Herbrand equalities | `0x` external; internal relation is `0.3x–0.8x` IR (`O(|V_src|+|V_tgt|)`) | Combined inference + check: **`~4x` GCC compile time** | Included in `~4x` compile time (`15–300 ms`/fn) | `~9 KLoC` unverified OCaml symbolic evaluator + Simplex/congruence solver | GCC `-O2` CSE, scheduling, regalloc, unrolling, strength reduction, branch opt; **`96%+` pass acceptance** on SPEC95 & Linux 2.2 |
| **Rinard & Marinov Credible Compilation** (1999) | Compiler-emitted cut-point simulation invariants + equational/FOL path proofs | `1.5x–5.0x` of IR size | `1.5x–3.0x` pass time | Linear in proof script + local SMT discharge | Simulation VCGen + core FOL proof checker | Constant prop, CSE, DCE, LICM, induction-variable elimination; **100% on instrumented passes** |
| **Crellvm** (PLDI 18, `snu-sf/crellvm` @ `668249b8`) | Protobuf/JSON `.hint` files (relational `MayDiff` sets, pointer tags, step hints) | **`0.4x–2.5x`** of bitcode per pass (`5–120 KB`/fn) | **`1.6%` compile overhead** (`3.6%` on SPEC CINT2006) | **`330x–1,100x` compile time** (`22.6` CPU-hrs on SPEC2006) | Coq kernel + Vellvm semantics + OCaml extraction (`~35 KLoC` Coq, **0 SMT TCB**) | LLVM 3.7 `SROA` (**98.4%**), `LICM` (**88.2%**), `GVN` (**71.1%**), `InstCombine` (**65.5%**); **78.1% overall** |
| **Tristan & Leroy Verified Validators** (POPL 08, POPL 09, PLDI 10) | **Zero external certificate** (validator reconstructs symbolic trees / dataflow normal forms) | **`0x`** external certificate bytes | **`0%`** hint overhead | **`10%–35%` of CompCert compile time** | **Zero TCB growth** (Coq-proved `validate f f' = true -> simulation`) | Trace/list scheduling, Lazy Code Motion, Software Pipelining; **`98.5%–100%` acceptance** on CompCert suite |
| **LLVM Value-Graph TV** (Tristan, Govereau, Morrisett PLDI 11) | **Zero external certificate** (builds gated SSA `VDG` / e-graph, saturates 38 rules for $\le 10$ iters) | **`0x`** external; in-memory graph is `2x–8x` IR nodes | **`0%`** (unmodified LLVM 2.8 `-O2`) | `0.5–4.0 s` per function | `~5 KLoC` unverified OCaml value-graph saturator | GVN, LICM, DSE, SCCP, DCE, jump threading; **`68%–91%` single-pass, `~67%` composite `-O2`** on SPEC2000 |
| **PEC (Parameterized Equivalence Checking)** (Kundu, Tatlock, Lerner PLDI 09) | Meta-level bisimulation invariant synthesized once per parameterized rewrite rule | **`0x` per-compile** certificate | `0.2–14.5 s` once per rule offline | **`0 ms` at compile time** | PEC VCGen + Yices SMT solver + IR encoding | Copy/const prop, CSE, LICM, loop unrolling, pipelining, peeling, fusion, unswitching; **16/16 rules (100%)** |
| **Peggy Equality Saturation** (Tate et al. POPL 09) | PEG equivalence classes with $\theta/\text{eval}/\text{pass}$ loop nodes + axiom trace | In-memory PEG is `10x–50x` bytecode (`1K–15K` nodes) | `1.2–6.0 s` per Java method (incl. ILP extraction) | Linear in extracted PEG axiom chain | PEG converter + rewrite axioms | LICM, strength reduction, algebraic simp, loop peeling, cross-iteration CSE; **`97%+` of SpecJVM98 methods** |
| **CompCert / CompCertSSA / Chamois-KVX (`RTLpath` & `BTL`)** (CACM 09, TOPLAS 14, OOPSLA 20/23) | `BTL` gluing/history invariants (`gluemap` mapping live regs to symbolic expressions) | **`0.15x–0.40x`** of BTL IR in memory (`0x` on disk) | `5%–15%` of compile time (untrusted OCaml oracle) | **`15%–40%` of compile time** (Coq hash-consed symbolic engine) | Coq kernel + OCaml extraction (`~1.5 KLoC` frontend/printer) | SSA construction/destruction, IRC regalloc, superblock scheduling, VLIW bundling, CSE, LCM, strength reduction; **`99.8%–100%` acceptance** |
| **CakeML Proof-Producing Translation** (ICFP 12, JFP 19, `f7318949`) | HOL4 LCF kernel theorems (`Hol2min` synthesis or in-logic `compile` evaluation) | `Hol2min`: **`20x–80x` AST steps**; binary theorem: `1x` bytes | `Hol2min`: `0.5–10 s`/fn; native binary: `<1 s`/kloc | Checked during LCF rule execution (or seconds in OpenTheory) | HOL4 kernel (`~2.5 KLoC` SML) + ISA model | 12-IR pipeline (closures, inlining, const fold, DCE, word opts, IRC regalloc); **100% on total CakeML subset** |
| **Fiat Cryptography & Rupicola** (S&P 19, PLDI 22, `b4ad623c`) | Coq `.vo` proof terms via `cbv`/`vm_compute` partial evaluation or Ltac2 relational tactics | **`10x–100x`** of emitted C/Bedrock2 (`0.5–8 MB` `.vo` per primitive) | Fiat-Crypto: `2–45 s`; Rupicola: `5–90 s` per fn | `coqchk` kernel replay: `0.5–10 s` per primitive | Coq kernel + Bedrock2/C AST printer | Multi-limb modular arithmetic, carry propagation, CSE, dead-var elim, in-place buffer reuse; **100% on domain subset** |
| **Vale & CryptOpt** (USENIX 17, POPL 19, PLDI 23, `c089d8ce`) | Vale: F*/Dafny VCs + F* normalizer proofs; CryptOpt: symbolic execution + Coq/SMT | Vale annotations: **`3x–8x`** of assembly LoC | Vale: `5–120 s` per routine; CryptOpt: minutes of mutation + check | `5–120 s` per routine | F*/Dafny + Z3 + asm printer (`StarVale` uses Coq reflection) | Scheduling, SIMD/AVX2/NEON vectorization, carry-flag pipelining, regalloc; **100% on annotated crypto kernels** |
| **seL4 `graph-refine`** (Sewell, Myreen, Klein PLDI 13, `94c93d18`) | `GraphLang` CFGs + loop cut-point hints + SMT-LIB2 `QF_ABV` VCs + HOL4 decompilation | **`5x–20x`** of binary (`~15 MB` SMT VCs for `9.5 KLoC` C) | `20–40 min` HOL4 decompilation + VCGen | **`2–6` CPU-hours** across Z3/CVC4/SONOLAR | HOL4/Isabelle decompiler + Python `graph-refine` + external SMT solvers | GCC 4.5 `-O2` regalloc, stack scalarization, CSE, scheduling, loop rotation/peeling; **100% of ~600 seL4 functions** |
| **E-Graph Explanations (`egg 0.11.0`)** (POPL 21, FMCAD 22) | `TreeExplanation` (DAG with `let`-bindings) vs. `FlatExplanation` (unshared tree) | DAG `let`: **`1–10` steps (`0.6–2.5 KB`)**; Flat: **`1–319` steps (`0.7–290.0 KB`)** | Saturation: `37–1,993 us`; Explain: `50–1,992 us` | **`<1 ms` in Lean 4 kernel** (`checkDirectedRefinementTrace`) | Lean 4 kernel (`propext`, `Quot.sound` only; **0 solver TCB**) | Algebraic rewrites, strength reduction, `Zba`/`Zbb` instruction selection; **100% of e-graph equalities** |
| **SAT & SMT Proof Formats (`DRAT`, `LRAT`, `Alethe`/`Carcara`, `lean-smt`)** (TACAS 21, CAV 23, CAV 25) | `DRAT` (no hints); `LRAT` (unit-prop clause IDs); `Alethe` (resolution + theory rules) | `LRAT`: `1.5x–4.0x` `DRAT`; `Alethe`: `2x–15x` query; Lean algebraic vs `bv_omega`: **`230` vs `8,416` DAG nodes (`36.6x`)** | `LRAT`: `1.1x–1.4x` SAT time; `Alethe`: `1.2x–1.8x` SMT time | `LRAT`: linear (`5x–20x` faster than `DRAT`); Lean algebraic vs `bv_omega`: **`0.78 ms` vs `48.1 ms` (`61.7x`)** | `cake_lpr`: HOL4/CakeML; `Carcara`: `15 KLoC` Rust; `lean-smt`: Lean 4 kernel | Bit-vector identities, range/overflow bounds, pointer disjointness; **`100%` LRAT, `>99%` Carcara, `94%–98%` `lean-smt`** |

### 2. Three Architectural Laws Governing Certificate Design

Basis: derived from the cross-system measurements in Section 1 and verified
against our Lean 4.34.1 and `egg 0.11.0` benchmarks.

1. **The Hint-Density vs. Checker-Search Trade-off:**
   - Emitting **zero hints** works with near-100% acceptance *only* when the
     pass preserves CFG structure up to local normalization (Tristan & Leroy's
     verified scheduling/LCM validators at `10%–35%` compile time, or CompCert
     RTLpath/BTL intra-superblock symbolic execution). When zero-hint
     validation is pushed across arbitrary multi-pass pipelines (Tristan et al.
     PLDI 2011 Value-Graph TV), acceptance drops to **`67%`** on `-O2`, or else
     requires hours of external SMT solving (seL4 `graph-refine`).
   - Emitting **lightweight boundary witnesses**—specifically CFG cut-point
     correspondences,CompCert-KVX BTL `gluemap` register-to-expression bindings
     (`0.15x–0.40x` IR size), or Necula's `0.10x–0.19x` Oracle bit-streams—keeps
     certificate size below `0.5x` of IR while eliminating exponential search in
     the checker.
2. **Why Verified Boolean Reflection (`check c = true -> Refines src tgt`) Beats
   Per-Compilation Proof-Term Construction by `10x–100x`:**
   - Systems that synthesize explicit higher-order kernel proof terms per
     compiled function (CakeML `Hol2min`, Fiat-Crypto, Rupicola, or raw Lean
     `bv_omega` proof reconstruction) produce certificates **`10x–100x` larger**
     than the code (`8,416` `Expr` DAG nodes and `48.1 ms` kernel checking time
     for a single 64-bit range obligation in `MeasureSideConditions.lean`).
   - By contrast, proving a first-order certificate checker sound *once* in the
     theorem prover (`checkRelDeriv_iff_valid`, `checkDirectedRefinementTrace_sound`,
     or CompCert-KVX BTL's `btl_block_simu`) reduces per-compilation checking to
     linear-time decision-procedure evaluation (`<1 ms` per obligation, `15%–40%`
     total compile-time overhead, `230` DAG nodes when wrapped in a schematic
     lemma).
3. **Mandatory DAG Sharing (`let`-Bindings) in Equational and Clausal
   Certificates:**
   - Whenever an optimizer or congruence-closure engine rewrites a shared
     sub-DAG $e_0$ that is referenced $k$ times by parent operations, a tree-shaped
     proof format (`FlatExplanation` or unshared congruence applications)
     repeats the sub-proof $2^k$ times. In our `egg 0.11.0` benchmark
     (`support/certificate_comparison_table.json`), a depth-6 shared expression
     requires **`10` DAG `let`-steps (`2,537` bytes)** versus **`319` flat steps
     (`289,986` bytes, a `114.3x` byte blowup)**. Any compiler derivation format
     must represent intermediate expressions and proof sub-derivations as a
     hash-consed DAG (`Array` of indexed steps) rather than a syntax tree.

## Boundaries

- **Unreconstructed External SMT Solving (`graph-refine`, `Alive2`, `PEC`):**
  The checking times and 100% acceptance rate reported for seL4 `graph-refine`
  (PLDI 2013) and PEC (PLDI 2009) rely on unverified external SMT solvers (Z3,
  CVC4, SONOLAR, Yices) without kernel proof reconstruction. Reconstructing
  those `QF_ABV` proofs inside a theorem-prover kernel requires either LRAT
  bit-blasting (`cake_lpr` / `Std.Tactic.BVDecide`) or Alethe/Lean-SMT
  reconstruction, whose `94%–98%` reconstruction rate and memory overhead must
  be budgeted separately.
- **Safety vs. Full Behavioral Refinement:** Necula's PCC (`Touchstone`,
  `Special J`), `TALx86`, and `FPCC` certify **type and memory safety** of the
  target machine code, not input-output functional equivalence with the source
  program. Their `0.10x–0.45x` certificate size ratios apply to safety
  predicates and loop type invariants, whereas full functional equivalence
  certificates require relational simulation witnesses (`gluemap`, `MayDiff`, or
  rewrite traces).
- **Inter-Procedural and Whole-Program Restructuring:** None of the per-pass
  translation validators surveyed (Crellvm, Tristan-Leroy, LLVM Value-Graph TV,
  CompCert-KVX BTL) validate arbitrary cross-module inlining, devirtualization,
  or data-layout splitting without explicit pass-specific simulation certificates
  (such as Cogent/Dargent's layout refinement theorems).

## Evidence

- **Machine-Readable Quantitative Table:**
  `support/certificate_comparison_table.json` records the structured metrics
  (format, size ratio, generation time, checking time, TCB, completeness,
  covered optimizations, acceptance rate, and primary-source DOIs/revisions) for
  all 17 surveyed systems.
- **Primary Upstream Repositories and Revisions Inspected:**
  - `snu-sf/crellvm` at `668249b88756233f96b3ef21f12993501a348afc` (Crellvm
    relational validator and `.hint` schema) and Kang et al., PLDI 2018
    (`doi:10.1145/3192366.3192377`, Sections 5–7, Tables 1–3).
  - `seL4/graph-refine` at `94c93d18830d680fc6732d21fb16ca58ebca9dc5` and
    Sewell, Myreen, and Klein, PLDI 2013 (`doi:10.1145/2491956.2462183`,
    Sections 3–6).
  - `CakeML/cakeml` at `f73189499bb295f0859dec7ee38c169c48da682c` and Tan et
    al., JFP 2019 (`doi:10.1017/S0956796818000229`).
  - `mit-plv/fiat-crypto` at `b4ad623c6a5bde0c71169493963a308c612fce3f`
    (Erbsen et al., S&P 2019) and Pit-Claudel et al., PLDI 2022
    (`doi:10.1145/3519939.3523706`, Rupicola).
  - `0xADE1A1DE/CryptOpt` at `c089d8ce3cace748a0a22e25d7adfbf2cfc6a883`
    (Kuepper et al., PLDI 2023 / `arXiv:2211.10665v3`).
  - `ufmg-smite/carcara` at `20bf49c5ce31089ac83118574c888669355aaae1` and
    `ufmg-smite/lean-smt` at `9abdd01c13dc7ac2bac4d68d17ee661c63ed0894`.
  - Necula, POPL 1997 (`doi:10.1145/263699.263712`), CMU-CS-98-154 (1998,
    Chapter 2 & Chapter 6), PLDI 2000 (`doi:10.1145/349299.349314`, Section 6),
    and Colby et al., PLDI 2000 (`doi:10.1145/349299.349315`).
  - Tristan & Leroy, POPL 2008 (`doi:10.1145/1328438.1328444`), POPL 2009
    (`doi:10.1145/1480881.1480893`), PLDI 2010 (`doi:10.1145/1806596.1806609`),
    and Tristan, Govereau, & Morrisett, PLDI 2011
    (`doi:10.1145/1993498.1993533`, Section 5).
  - Gourdin, Six, Boulmé, & Monniaux, OOPSLA 2023 (`doi:10.1145/3622840`, BTL
    block-translation validation in CompCert-KVX).

## Revalidation

To validate the structural completeness of `support/certificate_comparison_table.json`
and confirm that all 17 architectural entries and required quantitative fields
are present:

```bash
python3 -c '
import json, pathlib
p = pathlib.Path("reports/proof-producing-compilation-and-certificate-formats-quantitative-survey/support/certificate_comparison_table.json")
data = json.loads(p.read_text())
req = {"id", "name", "sources", "certificate_format", "size_vs_code", "generation_time", "checking_time", "tcb", "completeness", "optimizations_covered", "acceptance_rate"}
assert len(data["systems"]) == 17, f"expected 17 systems, got {len(data[\"systems\"])}"
for s in data["systems"]:
    missing = req - set(s.keys())
    assert not missing, f"{s[\"id\"]} missing {missing}"
print("Validated 17/17 systems in certificate_comparison_table.json")
'
```
