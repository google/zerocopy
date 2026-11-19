# Proof-Generation Token Economics, Certificate Footprints, and Kernel Checker Throughput

## Summary

Scaling formal verification from isolated high-assurance kernels to ecosystem-wide software repositories shifts the engineering bottleneck across **four tightly coupled resource budgets**:

1. **Authoring & Token Expansion Economics (`seL4`, `CompCert`, `IronFleet`, `theorem-labs/oss-verify-proofs`):** Human deductive verification historically required `6:1` to `27:1` lines of proof per line of implementation (`seL4`: `20` person-years vs. `2` implementation person-years for `~7.5K–8.7K` C LoC and `~200K` initial Isabelle/HOL LoC; `CompCert`: `6` person-years, `~100K` Coq LoC; `IronFleet`: `3.7` person-years, `39,253` Dafny proof/spec LoC over `5,114` implementation LoC). Autonomous frontier LLMs (`Anthropic & Theorem`, Oct 2026) bypass human proof-authoring latency on machine code—generating `~180M` lines of Rocq across `239` OSS-Fuzz entry points in `123` libraries (`~600,000` Rocq lines per median `18,000`-instruction static `riscv64` binary, a **`33.3:1` proof-LoC-per-instruction ratio**)—at a cost of `5M` to `10^8+` LLM tokens per binary, mitigated by **`~40%` single-generation model token reductions** (`Opus 5` -> `Opus 5.5` across `36` OSS-Fuzz tasks) and **`17%` shared-workspace proof reuse** (`Basis: documentation + source`).
2. **SMT Quantifier Instability vs. Proof Compactness (`verus-lang/verus`, `secure-foundations/mariposa`):** SMT-backed verifiers (`Verus`, `Dafny`) compress proof-to-code annotations to `~5:1–8:1` without emitting explicit proof terms, bounded via deterministic solver resource units (`DEFAULT_RLIMIT_SECS = 10f32` in `Verus`). However, `Mariposa` (Zhou et al., **FMCAD 2023**, `DOI: 10.34727/2023/isbn.978-3-85448-060-0_26`) demonstrates across `60`-mutant ensembles (`shuffle`, `rename`, `reseed`) that E-matching quantifier instantiation cascades create sharp `rlimit` cliff failures under semantics-preserving edits and solver upgrades (`Basis: source + documentation`).
3. **Certificate Disk and `mmap` RSS Layouts (`.vo` vs. `.olean` vs. `.mmb` vs. `LRAT`/`VeriPB`):**
   - **Rocq `.vo` (`vernac/library.ml`)** lazily defers reading opaque `Qed` proof segments (`Delayed.in_delayed` file offset + MD5 digest) on `Require`, but deserializes module summaries via OCaml `Marshal` into mutable GC heap words, defeating cross-process OS page sharing and causing multi-GiB RSS spikes on large transparent constants (such as ELF `Images.v` segment tables) or full `rocqchk` runs.
   - **Lean 4 `.olean` (`src/runtime/compact.cpp`, `src/library/module.cpp`)** serializes hash-consed persistent runtime objects (`m_rc = 0`) at a fixed target `base_addr`, enabling **`O(1)` zero-allocation `mmap(..., MAP_FIXED_NOREPLACE)`** (`Init/Prelude.olean` = `3.24 MiB` in v2 at `0x31fc9d500000`; `OLEAN_VERSION = 4` adds closure-function offset tables), at the cost of mapping whole-module declaration graphs (`2–8 GiB` RSS across large transitive imports).
   - **Metamath Zero `.mmb` (`mm0-c/mmb.md`)** separates a human-readable `.mm0` text specification from a pointer-free `mmap` stack-bytecode stream (`1–5 B` variable-length opcodes + `55-bit` `u64` bound-variable dependency bitmasks), compressing `2,723` Peano Arithmetic theorems into `877,464 B` (`259.6 B/theorem` proof stream) (`Basis: source + execution`).
4. **Checker Throughput Spectrum (`mm0-c` vs. `nanoda_lib` vs. `rocqchk` vs. `zkVM`s):** Measured on `x86_64` (`gcc 15.2.0 -O2`), `mm0-c` (`2,857` C LoC, `35 KiB` stripped `-DBARE` binary) verifies `peano.mmb` + `peano.mm0` end-to-end in **`12.778 ms` median** (`~67.1 MiB/s`) using **only `8,856 B` of live expression store** via per-theorem arena reset (`Basis: execution`). `nanoda_lib` (`v0.4.32`) parallelizes Lean 4 kernel `check_declar` across `num_threads` workers over an immutable `&Env`. Cryptographic `zkVM`s (`risc0`, `sp1`) verify **single concrete `RV32IM` traces** in `1–15 ms` (`~256–300 B` Groth16 or `~200 KiB–1.5 MiB` STARK receipts) at `10^4x–10^6x` GPU prover overhead, complementing rather than replacing universal ($\forall$ input) deductive proofs (`Basis: source + documentation + execution`).

## Applicability

This report characterizes the coupled authoring, memory, artifact-size, and kernel-checking trade-offs across the fourteen subjects pinned in `REPORT.json`:

- **Autonomous binary-level & foundational proof systems:** `theorem-labs/oss-verify-proofs` (`4c8fe739bb9bc95898f410b37222626f26dd0061`) paired with the Anthropic Frontier Red Team & Theorem engineering report (*"LLMs are making formal software verification feasible at a much larger scale"*, Oct 22, 2026), `rocq-prover/rocq` (`25f5b18a320e4796f181f938d3b74bebe7db4dc4`), `leanprover/lean4` at both `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`, `.olean` format v2) and `86b17eabcd56925809598be76a87d3f9b717bdbb` (`.olean` format v4), `ammkrn/nanoda_lib` (`0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`, `v0.4.32`), `digama0/mm0` (`0d414c0bfdaaeb7fea571895127abc1fa5a3d956`), `seL4/l4v` (`b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`), and `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`).
- **SMT-backed verification & solver stability:** `verus-lang/verus` (`c821149050c1269f32771a11582bee2fc58e5a8a`) and `secure-foundations/mariposa` (`8646e7b1c601f7154e93d85ebb1083ce1ed47f95`, FMCAD 2023). Note on citation precision: although `Mariposa` is frequently referenced alongside the authors' OSDI 2023 (`IronSync`) and OOPSLA 2023 (`Verus`) systems-verification papers, the primary `Mariposa` instability study was published at **FMCAD 2023** (`DOI: 10.34727/2023/isbn.978-3-85448-060-0_26`).
- **Combinatorial & cryptographic execution certificates:** `marijnheule/drat-trim` (`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`) alongside `VeriPB`/`CakePB` literature, and `RV32IM` zero-knowledge virtual machines `risc0/risc0` (`5e1be36a7fcadf98f341e348d9314e5f1d519046`) and `succinctlabs/sp1` (`0cd151a8d7beaaad4ad245c8f37515d6b4f72597`).

 Note on `oss-verify-proofs` scope: The Anthropic & Theorem Oct 22, 2026 report describes the full multi-week campaign (`239` proved entry points across `123` OSS-Fuzz libraries totaling `~180M` lines of Rocq), whereas the public repository cut at `4c8fe739bb9bc95898f410b37222626f26dd0061` (`README.md:8`, `docs/facts.md:27-39`) publishes the **`90` entry points across `32` libraries** cleared for public unpatched release under Rocq `9.2.0` and LPS (`rocq-linux-process-semantics` @ `f1006fe8178338a499b5e5c41be83006c4edd058`), withholding targets with open/embargoed vulnerability patches or pending GPL source bundles. Both figures apply to their respective scopes without contradiction.

## Findings

### 1. Human Effort vs. Autonomous LLM Token Economics and Proof-to-Code Expansion Ratios

`Basis: documentation + source`

Across four decades of formal verification, proof volume and authoring cost scale inversely with the **semantic level of the target artifact** (source DSL vs. C vs. compiled assembly) and the **degree of trusted vs. kernel-checked automation**:

| Project & Verification Stack | Target Artifact & Size | Proof / Spec Artifact Size | Expansion Ratio | Authoring Cost (Human or LLM Tokens) |
|---|---|---|---|---|
| **seL4** (`seL4/l4v`, Isabelle/HOL; Klein et al., SOSP 2009) | `~7,500–8,700` LoC C microkernel (+ Haskell prototype) | `~200,000` initial Isabelle/HOL LoC (expanded to `500K–1M+` LoC with `aarch64`/`riscv64`/info-flow) | `~23:1–27:1` vs. C (`~10:1` incl. Haskell specs) | **`20` person-years** (`11` py kernel proofs + `9` py reusable frameworks; C kernel took `2` py: `~375–435` C LoC/py verified) |
| **CompCert** (`AbsInt/CompCert`, Coq/Rocq; Leroy, CACM 2009) | Optimizing C compiler (`Clight` -> `PowerPC`/`ARM`/`x86`/`RISC-V`) | `~100,000` initial Coq LoC (code + correctness proofs; `> 180K` LoC in modern releases) | `~6:1–8:1` proof-to-compiler-code | **`~6` person-years** for initial verified compiler |
| **IronFleet** (`Dafny` + Z3; Hawblitzel et al., SOSP 2015) | `5,114` LoC executable distributed systems (`IronRSL` + `IronKV`) | `39,253` LoC Dafny specs, invariants, and ghost lemmas | **`7.68:1`** ghost/spec-to-exec LoC | **`3.7` person-years** (`~1,380` verified exec LoC/py) |
| **OSS Verify** (`theorem-labs/oss-verify-proofs`, Rocq 9.2.0 + LPS) | `239` OSS-Fuzz entry points in `123` C/C++/Rust/Python libraries (`90` in `32` libs public); median **`18,000` `RV64GC` instructions** | **`~180,000,000` Rocq LoC** total (**`~600,000` Rocq LoC** per median binary) | **`~33.3` Rocq LoC / RISC-V instruction** (`~100:1–300:1` vs. C source) | Autonomous multi-week LLM campaign; **`5M` to `10^8+` tokens** per target |

Three structural mechanisms govern LLM token efficiency and soundness in `oss-verify-proofs` (`4c8fe739bb9bc95898f410b37222626f26dd0061`):

1. **Model-Capability Scaling (`-40%` Tokens per Generation):** On a controlled 36-task OSS-Fuzz verification benchmark (`3` independent single-agent attempts per task, `5,000,000`-token budget per attempt), upgrading a single model generation (`Opus 5` -> `Opus 5.5`) reduced the token budget required to solve `50%` of the tasks by **`~40%`** (`Anthropic & Theorem, Oct 2026`, §04).
2. **Cross-Target Proof Amortization (`-17%` Tokens via Shared Workspace):** Static binaries share substantial runtime scaffolding—`musl` `libc` startup (`_start`, `__libc_start_main`), allocator paths, and `AddressSanitizer` / `UndefinedBehaviorSanitizer` shadow-memory initialization. Allowing concurrent agents on the 36-task suite to read and copy finished files from a shared workspace reduced total token consumption by **`17%`**, beat solo-agent token cost on **`30` of `34` completed proofs**, and solved **`2` tasks** where all solo `5M`-token runs failed.
3. **Anti-Reward-Hacking Architecture (`docs/checking.md:24-94` & Report Footnote 06):**
   - *Specification Integrity (`oft check`):* Pull requests cannot weaken `Statements.v` or suppress axiom printing. In CI (`docker run --network none`), `oft check` verifies ELF SHA-256 digests against `harness.yaml`, regenerates `Images.v` and `Statements.v` from base-branch YAML facts, compiles the untrusted proof from `.v` sources, and generates its **own** uneditable wrapper (`docs/checking.md:42-50`):
     ```coq
     Definition certified : OSSVerify.zlib.checksum_fuzzer.Statements.plain_halts
       := OSSVerify.Proofs.zlib.checksum_fuzzer.plain_halts.Proof.plain_halts_holds.
     Set Printing Fully Qualified.
     Redirect "assumptions" Print Assumptions certified.
     ```
     A 30-line Python auditor (`wrapper_assumptions` in `tools/oft/check.py`) parses `assumptions.out` (ignoring compiler stdout/stderr) and rejects any assumption outside `toolchain/allowed-axioms.txt` (Rocq primitive `Int63`/`Array`/`Strings` plus six standard classical/extensionality axioms: `classic`, `functional_extensionality_dep`, `constructive_indefinite_description`, `propositional_extensionality`, `sig_forall_dec`, `sig_not_dec`), strictly forbidding `Admitted`, `unsafe` universe flags, assumed positivity/guardedness, or definitional UIP.
   - *Patch Trivialization Defense:* During bug-finding loops where agents were permitted to patch crashing C/C++ libraries and regenerate `Statements.v`, naive reinforcement allows an agent to rewrite `LLVMFuzzerTestOneInput` to `return 0;`. Scoring therefore penalized every source patch and awarded bonus credit for formally characterizing the exact input subset whose behavior changed, backed by human patch auditing (`Footnote 06`).

---

### 2. SMT Quantifier Instability and `rlimit` Tail Variance (`Verus` & `Mariposa`)

`Basis: source + documentation`

Auto-active SMT verifiers (`Dafny`, `F*`, `verus-lang/verus` at `c821149050c1269f32771a11582bee2fc58e5a8a`) avoid generating `600,000`-line tactical proof scripts by lowering Rust functions, `requires`/`ensures` contracts, and linear ghost permissions through Intermediate Representation (`VIR` -> `AIR`) into `SMT-LIB2` queries discharged by `Z3` or `cvc5`.

1. **Deterministic `rlimit` Accounting vs. Wall-Clock Timeouts (`verus` `source/rust_verify/src/config.rs:9`, `source/air/src/context.rs:136-337`):**
   Wall-clock timeouts (`-t 10000`) cause flaky CI failures when CPU frequency scaling or co-scheduled workloads slow solver threads by `15%`. `Verus` therefore translates `DEFAULT_RLIMIT_SECS: f32 = 10f32` into solver-internal deterministic operation counters—emitting `(set-option :rlimit <count>)` per `check-sat` in `Z3` (`air/src/context.rs:321-325, 419-420`) or upfront `(set-option :rlimit-per <count>)` in `cvc5` (`air/src/context.rs:328-331`)—and records quantifier instantiation profiles via `qid_map: RefCell<HashMap<String, BndInfo>>` (`vir/src/context.rs:71`).
2. **Quantifier E-Matching Instability (`secure-foundations/mariposa` at `8646e7b1c601f7154e93d85ebb1083ce1ed47f95`, Zhou et al., FMCAD 2023):**
   Even with deterministic `rlimit`, CDCL(T) + E-matching heuristics exhibit chaotic sensitivity to syntactically minor, semantics-preserving perturbations. `Mariposa` (`README.md:44-82`) evaluates query $(Q, S)$ by generating **`60` mutants per axis** (`61` total runs per axis):
   - **`shuffle`:** Permutes top-level `(assert ...)` and `(declare-fun ...)` commands, altering E-graph congruence-closure insertion order;
   - **`rename`:** Bijectively renames SMT identifiers, perturbing internal symbol-ID/pointer-hash tie-breaking inside Z3/cvc5 priority queues;
   - **`reseed`:** Varies `(set-option :smt.random_seed ...)` and `:sat.random_seed`.
   Across thousands of verification queries from `Komodo`, `IronFleet`, `Dafny`, `F*`, and `Verus`, `Mariposa` established that `~2%–10%+` of complex quantified obligations fall into `unstable` or `unsolvable` regimes where benign edits in an unrelated helper lemma push Z3 across an E-matching matching-loop cliff (`0.2 s` -> `rlimit` exhaustion), and upgrading Z3 versions (e.g., `4.8.5` -> `4.12.x`, bundled in `mariposa/bin/`) shifts which queries fail. Stabilizing SMT verification at scale requires **explicit trigger curation (`#![trigger ...]`)**, **default-opaque specification functions (`#[verifier::opaque]` + local `reveal`)**, and **context pruning (`unsat-core` / `shake` actions in `mariposa`, `README.md:90-91`)**.

---

### 3. Certificate Disk and `mmap` RSS Layouts: `.vo` vs. `.olean` vs. `.mmb` vs. `LRAT`/`VeriPB`

`Basis: source + execution + derived`

When scaling verification to `10^5`–`10^8` lines of proof, how compiled theories and proof certificates represent terms on disk and in virtual memory determines whether parallel build workers fit in `16 GiB` of RAM or OOM-crash a `512 GiB` server:

#### 3.1 Architectural Comparison of Proof Artifact Formats

| Artifact Format | On-Disk Encoding | Deserialization & `mmap` Behavior | Proof-Body Laziness on `import`/`Require` | Primary RSS / Disk Bottleneck |
|---|---|---|---|---|
| **Rocq `.vo`** (`rocq-prover/rocq` `vernac/library.ml:21-72`) | Multi-segment OCaml `Marshal` stream (`ObjFile` segment directory + MD5 `Digest.t` per segment) | `System.marshal_in` allocates mutable OCaml GC heap blocks (`8 B` header + `8 B`/field); **cannot `mmap` zero-copy** | **Yes (`Delayed.in_delayed`):** `opaques` (`Qed` proof terms) stay on disk (`del_off: int64`) until `rocqchk` or `Print Assumptions` calls `fetch_delayed` | Non-opaque `library` segment (`Defined` terms, universe graphs, and large binary data such as `oss-verify-proofs` ELF `Images.v`, which must split segments across files) inflates OCaml GC RSS by `3x–8x` |
| **Lean 4 `.olean`** (`lean4` `compact.cpp`, `module.cpp:108-140`) | `object_compactor` hash-consed (`max_sharing_table`) persistent `lean_object` graph (`m_rc = 0`) relocated to `base_addr` (`88 B` header in v2/v4) | **`O(1)` `mmap(..., MAP_FIXED_NOREPLACE)`** (`0x100000`) when `[base_addr, +size)` is unmapped; fallback adjusts pointers + v4 `m_closure_offsets` | **No in monolithic `.olean`:** exported `ConstantInfo` graph shares one compacted region (`Init/Prelude.olean` = `3.24 MiB` on disk & VM) | Importing deep dependency cones maps hundreds of `.olean` files (`2–8 GiB` RSS); any edit to an upstream definition invalidates downstream `base_addr`/githash |
| **MM0 `.mmb`** (`digama0/mm0` `mm0-c/mmb.md:26-120`) | `40 B` header (`MM0B`, v1) + `8 B` `term`/`thm` tables (`55-bit` `u64` `deps`) + `1–5 B` `(cmd, data)` proof & unify bytecode streams | **`O(1)` `mmap(PROT_READ, MAP_PRIVATE)`** (`main.c:63`); zero pointer relocation, zero deserialization | **Random-access per theorem:** `p_thms` + sequential `p_proof` command stream; `mm0-c` resets `g_store` after **each** theorem | Expresses foundational axiomatic steps only; translating heavy computational reflection (`vm_compute`) without reflection axioms expands stream length |
| **`LRAT` / `VeriPB`** (`drat-trim`, `VeriPB` / `CakePB`) | Explicit clause-ID RUP propagation hints + clause-deletion commands (`LRAT`), or `0-1` linear cutting-planes derivations (`VeriPB`) | Streaming sequential file scan (`O(buffer)` read window + active clause/constraint database) | N/A (single refutation/optimality certificate) | `LRAT` certificates reach `1–100+ GiB` on hard SAT instances (mitigated by explicit `d` deletion commands bounding checker RAM); `VeriPB` compresses symmetry/pigeonhole proofs exponentially over `LRAT` |

#### 3.2 Exact Binary Header Verified Across Lean 4 `.olean` v2 -> v4 and MM0 `.mmb` v1 (`Basis: source + execution`)

1. **Lean 4 `.olean` Evolution (`v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52` vs. `86b17eabcd56925809598be76a87d3f9b717bdbb`):**
   Direct binary unpacking (`Evidence` §2) of `Init/Prelude.olean` (`3,397,592 B`) from `Lean 4.34.1` confirms `marker = "olean"`, `version = 2`, `flags = 1` (`LEAN_USE_GMP`), `base_addr = 0x31fc9d500000`, followed immediately at offset `88` by the compacted root pointer `0x31fc9d6bd3a0` ($\in [\text{base\_addr}, \text{base\_addr} + 3,397,592)$). At upstream commit `86b17eabcd56925809598be76a87d3f9b717bdbb` (`src/library/module.cpp:108-140`, `src/runtime/compact.h:48-55`), `OLEAN_VERSION` advances to `4`, appending `size_t data_size`, `uint32_t num_closure_offsets`, and `num_closure_offsets * uint64_t` offsets so persisted native closures (`m_allow_closures`) can relocate `m_fun` pointers against loaded shared libraries (`get_loaded_libs()`).
2. **MM0 `.mmb` v1 Density (`peano.mmb` at `0d414c0bfdaaeb7fea571895127abc1fa5a3d956`):**
   Unpacking the `40 B` header of `peano.mmb` (`877,464 B` total) yields `magic = "MM0B"` (`0x42304D4D`), `version = 1`, `num_sorts = 3`, `num_terms = 170` (`p_terms = 48`), `num_thms = 2,723` (`p_thms = 8,456`), `p_proof = 170,532`, and `p_index = 877,376` (`debug_index = 88 B`). Across `2,723` theorems, the entire proof bytecode stream occupies `706,844 B`—an average of **`259.6 bytes` per verified theorem**.

---

### 4. Kernel & Certificate Checker Throughput: `mm0-c` vs. `nanoda_lib` vs. `rocqchk` vs. `zkVM`s

`Basis: source + execution + documentation`

1. **Sub-20 ms Bare-Metal Stack Checking (`mm0-c`, `digama0/mm0`):**
   The complete `mm0-c` verifier at `0d414c0bfdaaeb7fea571895127abc1fa5a3d956` comprises **`2,857` lines of C** across 7 files (`verifier.c`: `819` LoC; `parser.c`: `904` LoC; `types.c`: `329` LoC; `verifier_debug.c`: `322` LoC; `verifier_types.c`: `243` LoC; `index.c`: `161` LoC; `main.c`: `79` LoC) and compiles (`gcc -O2 -DBARE -s`) to a **`35 KiB` native `x86_64` executable**.
   - **Measured Execution (`peano.mmb` `857 KiB` + `peano.mm0` `27 KiB`, `Evidence` §2):** End-to-end process launch (`fork` + `execv`), `mmap`, `.mm0` specification text parsing on `stdin`, and full `.mmb` verification completes in **`12.778 ms` median (`11.749 ms` min, `7.03 ms` user + `7.03 ms` sys)**—an effective end-to-end throughput of **`67.1 MiB/s`** (`> 213,000` theorems/sec). On the full ZFC `set.mm` translation (`~38,000` theorems), `mm0-c` verifies the entire library in **`195 ± 5 ms`** (Carneiro 2020, `arXiv:1910.10703`).
   - **Theorem-Modular Arena Reset (`8,856 B` Live Store):** `mm0-c` pre-declares static BSS arrays (`STACK_SIZE = 65,536` words, `HEAP_SIZE = 65,536` words, `STORE_SIZE = 64 MiB`, `mm0-c/verifier_types.c:19-37`), which lazy Linux demand paging never faults in unless touched (`ru_maxrss = 14,768 KiB`, `minflt = 178`, `majflt = 0`). Running `-DHIGHWATER` reveals that across all `2,723` theorems of `peano.mmb`, peak live memory inside the verifier is **`28` stack words (`112 B`), `211` heap words (`844 B`), and `8,856 B` of expression store** (`0.013%` of `STORE_SIZE`), because `g_store_size`, `g_heap_size`, and `g_stack_top` reset to `0` at the end of every theorem statement.
2. **Multi-Core Declaration-Parallel Dependent Type Checking (`ammkrn/nanoda_lib` @ `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`, `v0.4.32`):**
   `nanoda_lib` (`~4.5K` LoC safe Rust, `overflow-checks = true`, `lto = true`, `Cargo.toml:11-15`) decouples kernel verification from the Lean 4 C++ runtime by consuming `lean4export` files (`README.md:10-39`, `src/tc.rs:58-84`). Because a well-formed Lean environment `Env` is immutable once parsed, `check_declar(&self, d: &Declar)` checks `Theorem`, `Definition`, `Opaque`, `Inductive`, and `Recursor` declarations **concurrently across `num_threads` worker threads**, each holding an isolated `TcCtx` and `TcCache` (`stack_size_bytes` defaulting to `32 MiB`, configurable to `1 GiB` for deep recursion) and enforcing an explicit `permitted_axioms` allowlist (`nat_extension` and `string_extension` disabled by default for minimal TCB).
3. **Single-Threaded Dependent & Reflective Kernels (`rocqchk` / `rocq compile`):**
   Checking `oss-verify-proofs` assembly proofs requires unfolding `RV64GC` step relations and bitvector memory maps inside Rocq `9.2.0` (`docs/checking.md:10-36`). Because dependent conversion (`vm_compute` / kernel WHNF reduction) shares mutable universe constraints and sequential `.vo` compilation dependencies unless explicitly factored into independent Dune libraries (`projects/<p>/<h>/proofs/lib/`), checking a `600,000`-line binary proof consumes **minutes to tens of minutes of CPU time and `2–16 GiB` of OCaml heap** (`~10^2`–`10^3` instructions verified per checker CPU-minute).
4. **Zero-Knowledge Virtual Machines (`risc0/risc0`, `succinctlabs/sp1`):**
   `zkVM`s prove computational integrity for **a single concrete execution trace** $\exists w.\; M(x, w) = y$ on `RV32IM` (`Plonky3` STARKs + cryptographic precompiles in `sp1`; STARK + BN254 Groth16 compression in `risc0`). Verifier latency is sub-`15 ms` (`~200K–300K` EVM gas on a `~256–300 B` Groth16 proof, or `10–100 ms` on a `~200 KiB–1.5 MiB` recursive STARK receipt) with $O(1)$ verifier RAM, **but** prover cost scales per dynamic execution cycle (`~100 kHz–5 MHz` on multi-GPU CUDA hardware = GPU-seconds to GPU-minutes per run) and establishes **zero guarantee** for any untested input $x' \neq x$.

---

### 5. Six-Level Performance and Resource Footprint Matrix Across Verification Stacks (L1–L6)

`Basis: source + documentation + execution + derived`

| Verification Stack | (L1) Human & Agent Authoring Velocity | (L2) Prover / Framework Build Time | (L3) Synthesis / Elaboration / Solver Latency | (L4) Verified Target Runtime Performance | (L5) Standalone Kernel / Certificate Check Speed | (L6) Peak RSS, Certificate & TCB Footprints |
|---|---|---|---|---|---|---|
| **seL4 (`Isabelle/HOL` `l4v`)** | Human: `~400` C LoC/person-year (`20:1–27:1` proof LoC); brittle `apply`-script repair on C struct layout edits | Isabelle + HOL-Word/AutoCorres heap build: `10–45 min`, `8–32 GiB` Poly/ML RSS | Interactive `Sledgehammer`/tactic step `0.2–15 s`; full `l4v` session build `hours` on multi-core server | **`1.00x`** bare-metal `-O2` C microkernel (`< 200–500` cycles IPC fastpath; deterministic WCET) | Isabelle LCF kernel checks during session build (no compact standalone `.mmb`-like export by default; `minutes–hours`) | Poly/ML session heaps `4–32+ GiB` disk/RSS; trusted ML runtime + C parser TCB |
| **CompCert / OSS Verify (`Rocq 9.2.0` + LPS)** | Human (`CompCert`): `6` py / `100K` LoC; Agent (`OSS Verify`): `5M–10^8+` tokens/binary (`-40%` per model gen, `-17%` shared reuse) | Rocq `9.2.0` + `stdpp` + `Flocq` + `LPS` Docker image build: `5–15 min` | `rocq compile` on `600K`-LoC RV64 proof: `minutes–hours` across Dune jobs; interactive `coq-lsp` `50 ms–5 s` | `CompCert`: `~0.85x–0.95x` `gcc -O2`; `OSS Verify` `plain` build: **`1.00x`** unmodified Clang static `riscv64` binary | `oft check` (`rocq compile` + `Print Assumptions` wrapper) or `rocqchk`: `~0.5–5 MB/s` `.vo`, single-thread per `.vo` | `.vo` + ELF `Images.v` `10^1–10^3 MiB`/target; `rocq` OCaml GC RSS `2–16 GiB`; TCB = Rocq + OCaml + `LPS` (`f1006fe8`) |
| **Verus / IronFleet (`Rust`/`Dafny` + `Z3`)** | `5:1–8:1` ghost/spec LoC; fast initial authoring, high Day-2 `rlimit` repair cost without `opaque`/trigger discipline | `Verus` Rust build + Z3 binary: `1–4 min` incremental/clean, `< 2 GiB` RSS | `0.05–10.0 s` per fn (`DEFAULT_RLIMIT_SECS = 10`); `Mariposa` shows `2%–10%+` query instability under `shuffle`/`rename`/`reseed` | **`1.00x`** native `rustc`/LLVM `-O3` (`spec`/`proof` ghost code erased `100%` before LLVM codegen; `0` runtime overhead) | **No proof certificate by default** (re-runs Z3 SMT search; optional SMT proof reconstruction adds `2x–20x` overhead) | `verus` + `z3` RSS `150 MiB–2 GiB`; `0 B` shipped proof artifact; large TCB (`Z3` `~400K+` C++ LoC + `VIR`/`AIR` lowering) |
| **Lean 4 + `nanoda_lib`** | Unified code/spec/tactics; warm `lake serve` InfoView `< 15–50 ms` enables rapid human & LLM (`multi-attempt`) iteration | Lean 4 stage2 `10–25 min`; `nanoda_lib` clean Rust `--release` LTO build `< 25 s` | Elaboration `0.1–30 s`/file (can stall on naive `dsimp`/`whnf` over symbolic ASTs without fuel/projection guards) | Functional Lean `0.5x–0.95x` C; when verifying external Rust/MIR models, target Rust executes at **`1.00x`** native speed | `nanoda_bin` parallel `num_threads` over `lean4export` checks Mathlib-scale exports in `tens of seconds` on 16–64 cores | `.olean` `mmap` `MAP_FIXED_NOREPLACE` (`Prelude.olean` `3.24 MiB`; full workspace `1–8 GiB` RSS); `nanoda_lib` TCB `~4.5K` safe Rust LoC |
| **Metamath Zero (`mm0` + `mm0-c`)** | `.mm1` Lisp-like tactic/MMC authoring; lower-level than Lean/Rocq (`~10x` more explicit lemmas without automation) | `mm0-c` compiles (`gcc -O2`) in **`< 0.3 s`**; `mm0-rs` Rust compiler builds in `~20–40 s` | `mm0-rs` compiles `.mm1` -> `.mmb` at `10K–100K` LoC/s (`< 50 ms` LSP diagnostics in `mm0-rs server`) | Verified `MMC` x86-64 ELF output runs at native assembly speed (`0` runtime GC/interpreter overhead) | **`12.78 ms`** for `peano.mmb` (`857 KiB`, **`67.1 MiB/s`**); `< 200 ms` for all of ZFC `set.mm` (`~38K` thms) | **`35 KiB`** stripped checker binary; **`8,856 B`** peak live store (`14.4 MiB` process RSS); **`259.6 B/thm`** `.mmb`; **`2,857` C LoC TCB** |
| **`LRAT` / `VeriPB` + `CakePB`** | Fully automatic solver output (`CaDiCaL`, `Kissat`, `RoundingSat`); `0` human proof tokens | `drat-trim` `< 1 s` C build; `CakePB` verified CakeML binary prebuilt/bootstrapped in HOL4 | CDCL / PB solving: `ms` to `hours` (NP-hard worst-case exponential tail) | N/A (certifies static UNSAT / combinatorial optimality bounds used by compilers or hardware) | `cake_lpr` / `drat-trim` `LRAT`: `20–150 MB/s` streaming; `CakePB`: `2x–10x` slower than unverified C++ `VeriPB` | `LRAT` disk `10 MiB–100+ GiB` (active RAM bounded via `d` clause-delete ops); `CakePB` machine-code verified down to x86-64 |
| **`zkVM`s (`SP1` / `RISC Zero`)** | Ordinary Rust guest code (`0` proof annotations, `1:1` LoC, minimal human/agent friction) | `cargo prove` guest + host SDK build `30 s–3 min`; CUDA prover containers multi-GiB | **Single-input** trace proving: `100 kHz–5 MHz` on GPUs (`seconds–minutes` per run; `10^4x–10^6x` native slowdown) | Native execution unaffected outside prover, but **proven** run pays `10^4x–10^6x` prover compute & kW GPU power | **`1–15 ms`** (`Groth16` BN254 `~256–300 B`) or `10–100 ms` (`STARK` `~200 KiB–1.5 MiB`), independent of trace length | Prover GPU VRAM `16–80+ GiB` + host RAM `32–128 GiB`; receipt `~260 B–1.5 MiB`; cryptographic + circuit-constraint TCB |

---

### 6. Human Comprehensibility and Universal Conceptual Minimization (`Model Refinement`: C1 & C2)

`Basis: source + derived`

#### 6.1 (C1) Human Comprehensibility: Why 180M-Line Agent Proofs Live or Die by 1-Page Boundary Specs

Autonomous LLM proof generation breaks the historical equivalence between *proof size* and *human review burden*: no human reads `600,000` lines of Rocq RISC-V state-stepping tactics, because the kernel guarantees proof validity relative to the theorem statement. Consequently, **100% of human cognitive burden concentrates on auditing the specification, environment model, and axiom allowlist** (`C1`):

1. **Nonlocal Semantic Subtleties in `oss-verify-proofs` (`docs/statements.md` & `docs/semantics.md`):**
   Direct inspection of `projects/ada-url/can_parse/Statements.v` (`lines 43-95`) and `docs/statements.md` (`lines 51-94`) exposes three specification subtleties that a casual human reviewer could easily misinterpret as stronger guarantees:
   - *Memory Budgets Are Premises, Not Bounds (`Statements.v:76-92`, `statements.md:86-88`):* In `asan_agrees`, the `2 GiB` plain-build limit (`Budgets.Asan.lim_source`) is an **implication hypothesis** ("on every input on which the plain build is never refused memory for exceeding 2 GiB..."). If a crafted `10 KiB` input causes `plain` to allocate `2.1 GiB` and then trigger a heap buffer overflow, `asan_agrees` holds **vacuously** on that input (`plain_halts` raises the premise to `16 GiB`, covering `[2 GiB, 16 GiB]` crashes, but inputs requiring `> 16 GiB` remain outside both theorems).
   - *Exit Status `78` (`rejects`) Aliasing (`statements.md:62-75`):* When a harness rejects uninteresting inputs by `return 1;` (mapped by the driver to exit status `78`), adding `rejects` widens `halts_within_budget` to allow status `78` from **any** line in the binary—meaning a custom check that reports a bug via `return 1;` (`stops_with: return-only`) is no longer bound by the halting theorem unless audited separately in `harness.yaml`.
   - *Emulator vs. Kernel Divergence (`semantics.md:38-42`):* `LPS` (`f1006fe8`) models Linux `v6.18.46` in-place `mremap` shrinking, whereas `qemu-riscv64` user mode under `MREMAP_MAYMOVE` can relocate a shrinking mapping—creating an explicit gap between counterexample execution (`qemu-riscv64`) and `LPS` proofs.
   *Positive C1 Design Pattern:* `oss-verify-proofs` renders explicit **"Not claimed:"** prose blocks directly above every `Definition` in `Statements.v` (`lines 48-50, 88-90`) and isolates the CI trust check to a 7-line wrapper (`checking.md:42-50`) plus a closed 8-entry axiom file (`allowed-axioms.txt`).
2. **Physical File Separation of Human Spec vs. Machine Proof (`mm0`):**
   Metamath Zero (`mm0-c/README.md:7-11, 27-28`) elevates `C1` into an OS-level interface invariant: `mm0-c foo.mmb < foo.mm0` reads the **human-authored specification** (`foo.mm0`, containing only sorts, term signatures, axioms, and target `theorem` statements—zero proofs) from `stdin`, and treats `foo.mmb` strictly as an untrusted binary witness side-channel. Even if an LLM generates `100 MiB` of unreadable `.mmb` bytecode, a human audits only `foo.mm0` (`27 KiB` for all of Peano Arithmetic), and compiling `mm0-c` without `-DNO_PARSER` guarantees the binary witness proves the exact statements in `foo.mm0`.

#### 6.2 (C2) Universal Conceptual Minimization

Comparing `.vo`, `.olean`, `.mmb`, `SMT-LIB2`, and `LPS` identifies three redundant complexities and the minimal universal representations that eliminate them:

1. **Eliminating Coupled Heap/Address-Space Serialization via Theorem-Modular Bytecode + `mmap`:**
   Rocq's `.vo` couples theorem checking to OCaml's GC object layout (`Marshal`), while Lean's `.olean` couples zero-copy `mmap` to collision-free virtual `base_addr` placement (`MAP_FIXED_NOREPLACE`) and persistent runtime headers across an entire module's term DAG. Exporting checked declarations into a **position-independent, index-addressed stack bytecode stream (`.mmb` / `lean4export`-binary) with per-theorem arena reset** eliminates pointer relocation, closure fixup tables (`m_closure_offsets`), and cross-theorem checker memory accumulation (`8,856 B` live store in `mm0-c`), while allowing `N` threads (`nanoda_lib` architecture) to check `N` theorems concurrently with zero shared locks.
2. **Eliminating Capture-Avoiding Binder Traversal via 55-Bit Hardware Dependency Masks (`mmb` `arg = u64`):**
   Locally nameless, named-binder, and de-Bruijn substitution kernels spend substantial code complexity and runtime cycles shifting indices and checking variable freshness (`x \notin FV(e)`). In `mm0-c` (`mmb.md:93-105`, `verifier_types.c:40-58`), tagging every expression node in `g_store` at construction time with a `u64` bitmask (`[u1; 55]` bound-variable dependencies + `7-bit` sort + `1-bit` bound flag) reduces arbitrary fresh/disjoint-variable side-condition verification across arbitrarily large terms to **one `u64` bitwise AND instruction** (`O(1)`), genuinely removing variable-occurrence tree walks from the trusted kernel.
3. **Unifying Memory-Safety and Functional Specs via Sanitizer-Differential Binary Relations (`agrees`):**
   Rather than inventing separate verification logics for bounds safety, integer overflow, memory leaks, and roundtrip functional laws, `oss-verify-proofs` (`Shapes.v` / `Statements.v`) reduces all four to **two relations over `MemImageType.Image`**: `halts_within_budget` (ruling out traps, `abort()`, infinite loops, and unmodeled syscalls) and `agrees_in_abort_modelled plain sanitizer` (proving `plain` and `asan`/`ubsan` emit identical output bytes and exit codes without firing sanitizer checks). Domain properties (e.g., `can_parse(s) == parse(s).has_value()`) become ordinary C++ `assert` statements compiled into `Images.plain`, adding zero logic extensions to the trusted kernel.

## Boundaries

1. **Computational Reflection Blowup in Non-Definitional Checkers (`known not to apply` to naive `.mmb` translation):**
   `mm0-c` achieves `67 MiB/s` checking because `MM0` conversion rules are structural rather than Turing-complete definitional reduction (`whnf` / `vm_compute` / `native_decide`). Proofs that rely heavily on executing bitvector evaluators or decision procedures inside type conversion (such as `oss-verify-proofs` RISC-V instruction stepping in Rocq or large symbolic evaluators in Lean 4) cannot be exported to `MM0` without either (a) emitting explicit equational trace steps (expanding `.mmb` size by `10^2x–10^4x`) or (b) trusting/verifying a separate reflective evaluator.
2. **`LPS` Single-Threaded Static `riscv64` Scope (`unsupported` / `not examined` for general production deployments):**
   Proofs in `theorem-labs/oss-verify-proofs` (`4c8fe739bb9bc95898f410b37222626f26dd0061`, `docs/semantics.md:5-36`, Anthropic report §05) apply strictly to single-threaded, static `RV64GC` binaries linked against `musl` (`clang`), on inputs `< 64 MiB`, within `2 GiB`/`16 GiB` allocation premises, under `LPS` (`f1006fe8`). Multi-threading/atomics, signal delivery, dynamic `glibc` linking, `x86_64`/`aarch64` weak memory or silicon errata, inputs $\ge 64\text{ MiB}$, and memory errors invisible to `ASan` (such as intra-object struct field overflows or uninstrumented assembly) are **`unsupported`** by these theorems (`x86` Linux `zlib` proofs described in Anthropic §03 were exploratory case studies using LLM-generated x86 semantics not included in `oss-verify-proofs`).
3. **`nanoda_lib` Sequential Export-Stream Parsing Prefix (`known not to apply` to sub-10 ms cold start):**
   While `nanoda_lib` parallelizes `check_declar` across `num_threads`, it first parses the textual `lean4export` format sequentially to populate `Env` (`README.md:10-32`). Consequently, `nanoda_lib` excels at high-throughput batch CI verification of whole libraries (`seconds` to `minutes`), not `< 10 ms` incremental per-keystroke checking (`known not to apply`).
4. **Exact Token Cost Distributions Across Unpublished Held Targets (`unknown`):**
   While the Anthropic & Theorem Oct 2026 release reports exact aggregate scale (`239` entry points, `180M` Rocq LoC, `600K` median LoC per `18K` instructions) and controlled 36-task ratios (`5M`-token cap, `-40%` model-gen reduction, `-17%` shared-workspace reduction), exact per-library token histograms and dollar/GPU-hour totals across the `149` held/unreleased OSS-Fuzz entry points are **`unknown`** from public artifacts.
5. **Existential `zkVM` Receipts vs. Universal Deductive Proofs (`known not to apply`):**
   A `risc0` or `sp1` Groth16/STARK receipt proves only that **one observed execution** on **one specific input** produced output $y$; extrapolating a `zkVM` proof to safety on unseen inputs is **`known not to apply`**.

## Evidence

### Primary Upstream Source & Publication Coordinates

1. **Autonomous Binary Verification (`theorem-labs/oss-verify-proofs` @ `4c8fe739bb9bc95898f410b37222626f26dd0061` & Anthropic Oct 22, 2026 Release):**
   - Keane Lucas, Aengus Lynch, Luna Tong, Luke Champine, Zygi Straznickas, Dino Distefano, Harshikaa Agrawal, Evyatar Ben Asher, Cheru Berhanu, Ava Howell, Sami Jawhar, Chris Rohlf, Nickolai Zeldovich, Nicholas Carlini, Rajashree Agrawal, and Jason Gross, *"LLMs are making formal software verification feasible at a much larger scale"*, Anthropic Frontier Red Team & Theorem, Oct 22, 2026 (`https://www.anthropic.com/research/formal-verification`).
   - `theorem-labs/oss-verify-proofs` (`4c8fe739bb9bc95898f410b37222626f26dd0061`): `README.md:6-50` (`90` public entry points in `32` libraries, Rocq `9.2.0`), `docs/facts.md:18-95` (`budgets` `[16GiB, 512GiB]` / `[2GiB, 512GiB]`, `builds.segments`, held-finding rules), `docs/checking.md:10-94` (`oft check` wrapper generation, `docker run --network none`, `toolchain/allowed-axioms.txt`, `wrapper_assumptions`), `docs/semantics.md:1-85` (`LPS` `f1006fe8178338a499b5e5c41be83006c4edd058`, Linux `v6.18.46` vs. QEMU `mremap` divergence), `docs/statements.md:31-94`, and `projects/ada-url/can_parse/Statements.v:1-95`.
2. **Metamath Zero (`digama0/mm0` @ `0d414c0bfdaaeb7fea571895127abc1fa5a3d956`):**
   - Mario Carneiro, *"Metamath Zero: The Cartesian Theorem Prover"*, CICM 2020 / `arXiv:1910.10703` (`DOI: 10.48550/arXiv.1910.10703`).
   - `mm0-c/README.md:1-36`, `mm0-c/mmb.md:26-120` (`40 B` `MM0B` v1 header, `55-bit` `u64` `arg` dependency mask, `1–5 B` `(cmd, data)` encoding), `mm0-c/main.c:36-79` (`mmap`), `mm0-c/verifier_types.c:12-80` (`STACK_SIZE`, `HEAP_SIZE`, `STORE_SIZE = 1 << 26`), and `mm0-c/verifier.c:1-95`.
3. **Lean 4 `.olean` & `nanoda_lib`:**
   - `leanprover/lean4` @ `86b17eabcd56925809598be76a87d3f9b717bdbb`: `src/runtime/compact.h:40-94`, `src/runtime/compact.cpp:40-70` (`max_sharing_table`), `src/library/module.cpp:47-52, 108-140` (`MAP_FIXED_NOREPLACE = 0x100000`, `OLEAN_VERSION = 4`, `olean_header`, `num_closure_offsets`); and release `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`OLEAN_VERSION = 2`).
   - `ammkrn/nanoda_lib` @ `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`: `Cargo.toml:1-37` (`v0.4.32`, `overflow-checks = true`, `lto = true`), `README.md:25-84` (`num_threads`, `stack_size_bytes = 33554432`, `permitted_axioms`), `src/env.rs:53-84`, `src/tc.rs:58-84`, `src/util.rs:902-939`.
4. **Rocq `.vo`, SMT Instability, Historical Baselines & Certificate Systems:**
   - `rocq-prover/rocq` @ `25f5b18a320e4796f181f938d3b74bebe7db4dc4`: `vernac/library.ml:21-72` (`ObjFile`, `Delayed.in_delayed` / `fetch_delayed`, `System.marshal_in`).
   - `verus-lang/verus` @ `c821149050c1269f32771a11582bee2fc58e5a8a`: `source/rust_verify/src/config.rs:9` (`DEFAULT_RLIMIT_SECS = 10f32`), `source/vir/src/context.rs:71-72` (`qid_map`), `source/air/src/context.rs:136-337, 419-420`.
   - Yi Zhou, Jay Bosamiya, Yoshiki Takashima, Jessica Li, Marijn Heule, and Bryan Parno, *"Mariposa: Measuring SMT Instability in Automated Program Verification"*, FMCAD 2023 (`DOI: 10.34727/2023/isbn.978-3-85448-060-0_26`; extended report `DOI: 10.1184/R1/23905905`), `secure-foundations/mariposa` @ `8646e7b1c601f7154e93d85ebb1083ce1ed47f95` (`README.md:44-94`).
   - Gerwin Klein et al., *"seL4: Formal Verification of an OS Kernel"*, SOSP 2009 (`DOI: 10.1145/1629575.1629596`), `seL4/l4v` @ `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`; Xavier Leroy, *"Formal Verification of a Realistic Compiler"*, CACM 2009 (`DOI: 10.1145/1538788.1538814`), `AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`; Chris Hawblitzel et al., *"IronFleet: Proving Practical Distributed Systems Correct"*, SOSP 2015 (`DOI: 10.1145/2815400.2815428`).
   - `marijnheule/drat-trim` @ `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`; `risc0/risc0` @ `5e1be36a7fcadf98f341e348d9314e5f1d519046`; `succinctlabs/sp1` @ `0cd151a8d7beaaad4ad245c8f37515d6b4f72597`.

### Reproducible Execution Micro-Probes (`Observed 2026-11-19`)

#### Probe 1: Compiling `mm0-c` from `0d414c0bfdaaeb7fea571895127abc1fa5a3d956` and Benchmarking `peano.mmb` (`x86_64`, `gcc 15.2.0`)

```bash
mkdir -p /tmp/mm0_probe && cd /tmp/mm0_probe
SHA=0d414c0bfdaaeb7fea571895127abc1fa5a3d956
for f in index.c main.c parser.c types.c verifier.c verifier_debug.c verifier_types.c; do
  curl -sSL "https://raw.githubusercontent.com/digama0/mm0/$SHA/mm0-c/$f" -o "$f"
done
curl -sSL "https://raw.githubusercontent.com/digama0/mm0/$SHA/examples/peano.mm0" -o peano.mm0
curl -sSL "https://raw.githubusercontent.com/digama0/mm0/$SHA/mm0-js/test/peano.mmb" -o peano.mmb
wc -l *.c
gcc -O2 -DHIGHWATER main.c -o mm0-c-hw
gcc -O2 -DBARE -s main.c -o mm0-c-bare
./mm0-c-hw peano.mmb < peano.mm0
```

Recorded outputs (`x86_64` Linux, `gcc 15.2.0`, `Python 3.13.15` `perf_counter_ns` & `os.wait4`):
- Line counts: `index.c` `161`, `main.c` `79`, `parser.c` `904`, `types.c` `329`, `verifier.c` `819`, `verifier_debug.c` `322`, `verifier_types.c` `243` -> **`2,857` total C lines**; `mm0-c-bare` stripped binary = **`35 KiB`**.
- Highwater telemetry (`./mm0-c-hw peano.mmb < peano.mm0`, exit `0`):
  `stack highwater: 28 / 65536`, `heap highwater: 211 / 65536`, `store highwater: 8856 / 67108864`, `hypothesis stack highwater: 6 / 256`, `unify stack highwater: 9 / 256`, `unify heap highwater: 13 / 65536`.
- 15-run `mm0-c-bare` wall-clock latency & OS `rusage`: **`min = 11.749 ms`, `median = 12.778 ms`, `p95 = 15.201 ms`**, `ru_maxrss = 14,768 KiB`, `utime = 7.029 ms`, `stime = 7.029 ms`, `minflt = 178`, `majflt = 0`.

#### Probe 2: Binary Unpacking of `peano.mmb` Header and Lean `Init/Prelude.olean` Header

```python
import os, struct
with open("/tmp/mm0_probe/peano.mmb", "rb") as fp:
    hdr = struct.unpack("<4sBBHIIIIIIQ", fp.read(40))
print("MM0B:", os.path.getsize("/tmp/mm0_probe/peano.mmb"), hdr)
```

Recorded outputs:
- `peano.mmb`: `877,464 B` (`magic = b'MM0B'`, `ver = 1`, `sorts = 3`, `terms = 170`, `thms = 2,723`, `p_terms = 48`, `p_thms = 8,456`, `p_proof = 170,532`, `p_index = 877,376` -> `706,844 B` proof stream = `259.6 B/theorem`).
- `Init/Prelude.olean` (`Lean 4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`): `3,397,592 B` (`marker = b'olean'`, `ver = 2`, `flags = 1`, `base_addr = 0x31fc9d500000`, root pointer `0x31fc9d6bd3a0`).

## Revalidation

1. **MM0 Checker Speed & Highwater Invariants (`< 3 s`):**
   Re-run `Probe 1` against any newer `digama0/mm0` commit; check `mm0-c/mmb.md` `version` (`1`), `sizeof(header) == 40`, and `./mm0-c-hw` `store highwater` (`8,856 B` on `peano.mmb`) to detect any regression in theorem-modular arena reclamation.
2. **Lean `.olean` Header Version & `mmap` Path (`< 5 s`):**
   Check `OLEAN_VERSION` and `struct olean_header` in `leanprover/lean4` `src/library/module.cpp` (`OLEAN_VERSION = 4` at `86b17eabcd56925809598be76a87d3f9b717bdbb`), plus `MAP_FIXED_NOREPLACE` handling.
3. **OSS Verify Wrapper & Axiom TCB (`< 5 s`):**
   Inspect `toolchain/allowed-axioms.txt`, `tools/oft/check.py` (`wrapper_assumptions`), and `release.yaml` (`semantics.commit`) in `theorem-labs/oss-verify-proofs` to verify whether additional axioms, target architectures, or `LPS` revisions have entered the trusted boundary.
4. **Verus `rlimit` & Mariposa Stability Check (`< 15 s`):**
   Inspect `DEFAULT_RLIMIT_SECS` in `verus-lang/verus` `source/rust_verify/src/config.rs` and run `python3 src/exper_wizard.py single` in `secure-foundations/mariposa` across `60` `shuffle`/`rename`/`reseed` mutants when evaluating a new Z3 or cvc5 release.
