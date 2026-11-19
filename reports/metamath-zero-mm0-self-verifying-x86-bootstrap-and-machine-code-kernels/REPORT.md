# Metamath Zero (MM0), Binary Proof Streams, Self-Verifying x86-64 Bootstrapping, and Machine-Code Theorem Prover Kernels

## Summary

Hardware-rooted proof checking aims to eliminate circular compiler and runtime trust ("Trusting Trust") from interactive theorem provers. **Metamath Zero (MM0)** pursues this via **radical kernel parsimony** (`arXiv:1910.10703v3`; CICM 2020 `DOI: 10.1007/978-3-030-53518-6_5`): rather than embedding dependent conversion, pattern matching, or recursion inside the trusted checker, MM0 separates a **human-auditable `.mm0` specification** (sorts, term/def signatures, axioms, and theorem statements) from an **untrusted binary `.mmb` proof stream** checked in a single pass by **`mm0-c`**, a **2,857-line C verifier** (`1,470` lines excluding the `.mm0` parser and debug printer) that compiles with `-DNO_PARSER -DBARE` into an **18,640-byte stripped x86-64 ELF binary** (`9,141` bytes `.text`).

By letting the untrusted compiler control heap allocation (`CMD_PROOF_TERM` / `CMD_PROOF_DUMMY` / `CMD_PROOF_SAVE` / `CMD_PROOF_REF`) and separating prefix `unify_stream` matching from postfix `proof_stream` stack evaluation, `mm0-c` reduces term equality in `Refl` and `URef` to $O(1)$ store-offset comparison without runtime hash-consing—verifying Metamath's entire `set.mm` ZFC corpus in **< 200 ms** within **< 1 MiB** of writable expression store (`arXiv:1910.10703v3`). Above this checker, MM0 specifies user-mode x86-64 ELF semantics (`examples/x86.mm0`, 1,727 LoC) and the proof-producing compiler `mmc` (`mm0-rs`), targeting the end-to-end self-verification theorem in `examples/verifier.mm0` (`Verifier_terminates` + `Verifier_Valid`), which at the pinned snapshot remains incomplete (`examples/compiler.mm0` still declares `axiom sorry`). By contrast, **CakeML/Candle** (`CakeML/candle`, `DOI: 10.4230/LIPIcs.ITP.2022.3`) already holds a completed, machine-checked end-to-end HOL4 proof down to machine code for a 676-line stateless LCF HOL Light kernel at the cost of a ~14-hour HOL4 compiler proof replay and ML garbage-collector overhead, while **MetaRocq/CertiCoq** (`DOI: 10.1145/3706056`) formalizes ~300 KLoC of PCUIC typechecking and certified `Clight` extraction while retaining axiomatized inductive guard checking and CompCert/OCaml toolchain trust.

## Applicability

This report examines the trust boundaries, file formats, execution semantics, cross-logic translations, and six-level resource footprints across eleven pinned subjects:

- **Metamath & MM0 stack**: `digama0/mm0` (`0d414c0bfdaaeb7fea571895127abc1fa5a3d956`), Carneiro's `arXiv:1910.10703v3` (extended version of the paper submitted to CPP 2020 and published in condensed form at CICM 2020, `DOI: 10.1007/978-3-030-53518-6_5`), `david-a-wheeler/metamath-knife` (`76fc9f7f39f46f4c43499a0c2bd1402eb8b1cf9a`), and `oriansj/stage0-posix` (`643598041bf7639883874fe2cdc9d9693c9b03d5`).
- **Verified LCF & CIC machine-code stacks**: `jrh13/hol-light` (`6dbb775efdff7f75aa20006532bf6336bc645861`), `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`, `DOI: 10.1017/S0956796818000229`), `CakeML/candle` (`a9aeaa1dffd50f7cfeed811db6ee61f98e2234da`, `DOI: 10.4230/LIPIcs.ITP.2022.3`), `MetaRocq/metarocq` (`51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56`, `DOI: 10.1145/3706056`), and `CertiCoq/certirocq` (`ab66e0164e7ecb63e5af95c90c8e479068bf95c2`).

ABI and completeness boundaries strictly apply:
1. **`mm0-c` host constraints**: `mm0-c/main.c:15–28` aborts with exit `999` unless the host is **little-endian**, respects `__attribute__((packed))` (`sizeof(cmd32) == 5`), and 4-byte aligns `store_expr`, with POSIX `mmap` (`MAP_PRIVATE`, `PROT_READ`) and virtual memory accommodating a `~658 MiB` `.bss` (`~64.8 MiB` under `-DNO_PARSER -DBARE`).
2. **Completion status distinction**: `CakeML/candle` and `CakeML/cakeml` ship a *completed* HOL4-verified binary/REPL bootstrap, whereas `digama0/mm0@0d414c0` provides complete specifications (`mm0.mm0`, `x86.mm0`, `verifier.mm0`), `mm0-c`, `mm0-rs`/`mmc`, and verified Peano libraries (`peano.mm1`), while `examples/compiler.mm0` retains `axiom sorry` for unfinished compiler proofs.

## Findings

### 1. From Classical Metamath (`metamath-knife`) to MM0's Multi-Sorted First-Order Logic

Basis: normative (`digama0/mm0/mm0.md`) + documentation (`david-a-wheeler/metamath-knife/README.md`, `arXiv:1910.10703v3`).

Classical Metamath eliminates built-in β/δ/ι/η conversion rules altogether: its sole inference step is **simultaneous variable substitution** constrained by disjoint-variable (`$d`) side conditions, letting parallel Rust verifiers like `david-a-wheeler/metamath-knife` check the > 28,000 theorems in `set.mm` in under 1 second via `--split` segment parsing. However, Carneiro's `arXiv:1910.10703v3` (and `digama0/mm0/README.md`) identifies **three structural soundness gaps** in classical Metamath that force trust outside the core verifier:

1. **Token-string grammar ambiguity**: Metamath formulas are flat token sequences rather than parsed abstract syntax trees; an ambiguous dynamic grammar (demonstrated in Carneiro's 2013 `set.mm` ambiguity exploit) lets an expression parse in two ways and pass token-level substitution to prove `False`. MM0 parses `.mm0` specifications unambiguously using static/dynamic precedence grammars (unique prefix heads or infix precedence levels `0..max`), and `.mmb` operates exclusively on typed ASTs (`store_term`).
2. **Unverified definitional conservativity**: Metamath records definitions (`$df-*`) as unchecked `$a` axioms, deferring conservativity/dummy-variable checks to external linters. MM0 elevates `def` into a kernel-checked primitive (`CMD_STMT_DEF`), verifying well-typedness, bound-variable hygiene, and explicit unfolding witnesses (`CMD_PROOF_UNFOLD`).
3. **Variable bundling (`$d` vs implicit distinctness)**: Metamath allows metavariables $x, y$ to alias unless `$d x y` is stated; MM0 uses **bound vs. regular variables** where bound variables of a term/theorem are pairwise disjoint by default, requiring `mm0-hs from-mm` to emit unbundled variants (`⊢ T[x, x]` and `⊢ T[x, y]`) during `set.mm` translation.

MM0's abstract logic is a **multi-sorted first-order logic** parameterized by user-declared sorts with four orthogonal capability flags packed into `sort_data` (`mm0-c/mmb.md`, `types.c`):

| Sort Modifier | Bit | Semantic & Kernel Restriction (`mm0-c/verifier.c`, `mmb.md`) | Typical Use |
| :--- | :--- | :--- | :--- |
| **`pure`** | `0x01` | Forbids `term`/`def` constructors returning this sort (`(g_sorts[sort] & SORT_PURE) == 0` at `verifier.c:727`) | Variable-only sorts (`var` in FOL/ZFC) |
| **`strict`** | `0x02` | Forbids dummy variable quantification (`Dummy s` rejects `strict` sorts) | Second-order sugar (`set` in `peano.mm0`, ensuring conservative extension) |
| **`provable`** | `0x04` | Permits `axiom`/`theorem` conclusions and `Hyp` statements in this sort (`verifier.c:526, 784`) | Truth judgments (`wff`) |
| **`free`** | `0x08` | Exempts sort from free-variable tracking constraints | Auxiliary syntactic sorts (`nat` vs bound `var`) |

Term and theorem arguments encode variable dependencies in a single **`arg = u64`** word (`mmb.md`): bits `[0..54]` form a 55-bit bound-variable dependency mask (`deps`), bit `55` is reserved (`0`, capping active bound variables per declaration including `Dummy` at `next_bv < 55`), bits `[56..62]` encode `sort` (`u7`), and bit `63` marks `bound = 1` (requiring `deps == 1 << i` for the `i`-th bound variable).

---

### 2. `.mm0`/`.mmb` Separation and `mm0-c`'s Single-Pass Pointer-Equality Stack Machine

Basis: normative (`mm0-c/mmb.md`, `mm0.md`) + source (`mm0-c/main.c`, `types.c`, `verifier_types.c`, `verifier.c`, `parser.c`) + execution (Probe 2).

MM0's core trust thesis (`mm0.md:1–18`) is that **an auditor only inspects `.mm0` (to verify what was claimed) and the verifier binary (to verify it implements MM0)**; the `.mmb` proof file is a completely untrusted certificate stream. Any theorem, definition, or local lemma in `.mmb` can use arbitrary intermediate helper derivations, yet `mm0-c` verifies `CMD_STMT_SORT`, `CMD_STMT_DEF` (non-`local`), `CMD_STMT_AXIOM`, and `CMD_STMT_THM` (non-`local`) lockstep against the parsed `.mm0` stream via `parse_until(...)` (`verifier.c:712, 756, 789`).

#### `.mmb` v1 Binary Layout and Dual-Stream Machine
A `.mmb` v1 file begins with a 40-byte 8-byte-aligned header (`magic = 0x42304D4D` `"MM0B"`, `version = 1`, `num_sorts`, `num_terms`, `num_thms`, `p_terms`, `p_thms`, `p_proof`, `p_index`) followed by `[u8; num_sorts]`, an array of 8-byte `term` entries (`num_args : u16`, `ret_sort : u7`, `is_def : u1`, `p_data : u32`), an array of 8-byte `thm` entries (`num_args : u16`, `p_data : u32`), variable-length commands `[data_size:2 | opcode:6]` (`1–5` bytes, padded by 4 preload bytes after the terminating `CMD_END = 0x00`), and optional debugging `index` trees.

Verification executes two complementary stack machines sharing a flat 64 MiB byte store (`g_store[STORE_SIZE]`, 4-byte-aligned offsets):
1. **Postfix `proof_stream` ($\Delta; H; S \hookrightarrow \Delta'; H'; S'$)**: Operates on `g_stack` (`STACK_SIZE = 65536`) holding 32-bit tagged words whose 2 low bits discriminate `STACK_TYPE_EXPR (0x00)`, `STACK_TYPE_PROOF (0x01)`, `STACK_TYPE_CONV (0x02)` ($e_1 = e_2$), and `STACK_TYPE_CO_CONV (0x03)` ($e_1 \stackrel{?}{=} e_2$, paired on the stack with `e2`). Convertibility obligations use **inverted co-convertibility**: `Conv` pops `e1, |- e2` and pushes `|- e1` guarded by obligation `e1 =?= e2`, discharged top-down by `Refl`, `Symm`, `Cong`, `Unfold`, and deduplicated via `ConvCut`/`ConvSave`. Crucially, for `CMD_PROOF_THM` (`verifier.c:480–515`), the caller must push `[hyp_0, ..., hyp_{k-1}, arg_0, ..., arg_{n-1}, concl]` from bottom to top; `mm0-c` pops `concl`, pops `num_args` arguments into `g_uheap`, and executes the target theorem's `unify_stream` in `UThm` mode.
2. **Prefix `unify_stream` ($S; U; K \hookrightarrow_u S'; U'; K'$)**: Stored per `def` and `thm` in prefix order (`UTerm`, `UTermSave`, `URef`, `UDummy`, `UHyp`). When declaring a theorem (`UThmEnd`), `unify_stream` validates that the serialized unifier faithfully reconstructs the conclusion and `g_hstack` hypotheses (in reverse push order); when applying a theorem (`UThm`), `UHyp` pops `|- A'` from `g_stack` onto `g_ustack` and checks `B[Γ ↦ e] = B'` via `URef`/`UTerm`.

#### Compiler-Controlled Pointer Equality and $O(m \cdot n)$ Complexity
In `mm0-c`, heap allocations into `g_store` occur **exclusively** on `CMD_PROOF_TERM` (`0x10`/`0x11`) and `CMD_PROOF_DUMMY` (`0x13`). Rather than running a trusted hash-consing table inside the kernel, MM0 makes **the untrusted compiler responsible for emitting `Save` (`0x1F` / `0x11`) and `Ref` (`0x12`) opcodes** wherever two expressions must compare equal in `Refl` or `URef`: equality testing is literally a single integer comparison `get_uheap(data) == pop_ustack()` (`verifier.c:245`, `550`) on 4-byte store offsets. As proven in `arXiv:1910.10703v3` (p. 20), total verification time is $O(m \cdot n)$ where $n$ is proof stream length and $m$ is the largest deduplicated theorem statement (`Unify(T)`), collapsing to linear time in the size of the `.mmb` file across all non-contrived mathematical libraries.

Live compilation and execution of upstream `digama0/mm0/mm0-c` (`Probe 2`) confirms these exact binary and runtime characteristics:
- **Source footprint**: `2,857` total C lines (`95,393` B) across 7 files: `verifier.c` (`819` LoC), `verifier_types.c` (`243` LoC), `types.c` (`329` LoC), `main.c` (`79` LoC) = **`1,470` LoC** core kernel, plus `parser.c` (`904` LoC), `verifier_debug.c` (`322` LoC), `index.c` (`161` LoC).
- **Minimal `-DNO_PARSER -DBARE` build**: Compiles with `gcc -O2` in **`597.6 ms`** (`43,300 KiB` peak RSS) to a **`21,624 B`** ELF (`18,640 B` stripped; **`.text` = `9,141 B`**, `.data` = `656 B`, `.bss` = `67,899,616 B`). Importantly, `-DBARE` strips out `CMD_PROOF_SORRY` (`0x20`) at compile time (`verifier.c:634`), causing `sorry.mmb` to fail immediately with exit `255` (`unknown opcode`) rather than even reaching `g_uses_sorry` (`exit 3` in the standard build).
- **100x cold-start verification & tamper rejection**: On a valid Hilbert propositional `.mm0` (`319 B`) + `.mmb` (`385 B`) proof of `a1i` and `id` (`⊢ a → a` using `Save`/`Ref` DAG sharing), `mm0-c` verifies in **`19.12 ms` median / `3.24 ms` min** (`std`, `13,876 KiB` RSS) and **`13.59 ms` median / `2.64 ms` min** (`bare`, `12,184 KiB` RSS), while a 1-byte mutation (`CMD_PROOF_THM` target swap) fails deterministically with `exit 255`.

---

### 3. Self-Verifying x86-64 ELF Bootstrapping (`mmc`, `x86.mm0`, `verifier.mm0`) and `stage0-posix`

Basis: normative (`examples/x86.mm0`, `examples/verifier.mm0`, `examples/compiler.mm0`, `mm0-rs/mmc.md`) + documentation (`arXiv:1910.10703v3` Section 6, `oriansj/stage0-posix/README.md`).

To eliminate Ken Thompson's *Trusting Trust* compiler backdoor and supply-chain attacks (such as malicious build-time binary/tarball injection exemplified by `CVE-2024-3094`), MM0 models machine-code execution directly inside Peano Arithmetic (`examples/peano.mm0` -> `examples/x86.mm0` 1,727 LoC):

1. **Minimal user-mode x86-64 + Linux ABI model (`examples/x86.mm0`)**: Ported from the Sail x86-64 specification (`Armstrong et al., POPL 2019`), `x86.mm0` covers ~25 integer/control instructions (no x87/SIMD needed by `mm0-c`), parses ELF64 `PT_LOAD` segment layouts (`isBasicElf`), and wraps register/memory state with an IO world modeling `sys_read`/`sys_write`/`sys_exit`. Crucially, reading `stdin` yields the concrete trusted `.mm0` byte string `mm0_file`, whereas opening the `.mmb` file via `open`/`read` is modeled as returning **arbitrary nondeterministic bytes** (`arXiv:1910.10703v3`, p. 28). Because an untrusted `.mmb` is merely an existential witness, nondeterminism requires no file-system model in the TCB.
2. **Total correctness specification (`examples/verifier.mm0:11–29`)**: Declaring an abstract `def Verifier: string;`, MM0 asserts three properties:
   - `Verifier_basicElf`: `$ isBasicElf Verifier $`
   - `Verifier_terminates`: `$ initialConfig Verifier k -> terminates_ensuring k (S\ mm0_file, {output | output = 0 /\ Valid mm0_file}) $`
   - `Verifier_Valid`: `$ initialConfig Verifier k /\ succeeds k mm0_file 0 -> Valid mm0_file $`
   Both `Verifier_terminates` and `Verifier_Valid` are required: an infinite-looping or always-failing binary trivially satisfies `Verifier_Valid` vacuously, so an auditor must observe the actual hardware run return exit code `0` on `mm0_file` to instantiate `succeeds k mm0_file 0` (`arXiv:1910.10703v3`, p. 28).
3. **Proof-producing compilation (`mm0-rs` / `mmc`, `mm0-rs/mmc.md`)**: Rather than verifying a monolithic optimizing compiler globally once and for all, `mmc` compiles a high-level imperative language with separation/singleton types (`{x : u64}`, `(sn e)`) and simultaneously emits an x86-64 proof trace witnessing that the emitted bytes satisfy the source behavioral predicate. Untrusted passes (like graph-coloring register allocation or dead-code elimination) need zero global correctness proofs—only per-program proof checking—and `output string` emits the verified ELF binary bytes directly.
4. **Hardware & bootstrap-seed anchoring (`oriansj/stage0-posix`)**: While `mm0-c` can still be compiled from C source, anchoring its C compilation in `stage0-posix` (`oriansj/stage0-posix`) eliminates unverified C compiler binaries (such as host `gcc`/`clang`): `stage0-posix` bootstraps from a **256-byte `hex0` machine-code seed** (auditable in hex by hand) -> `hex1`/`hex2` linkers -> `M1` macro assembler -> `M2-Planet` C subset -> `live-bootstrap` (`MesCC` -> `GCC` + `Guile`), or applies Wheeler's Diverse Double-Compiling (`DDC`) across independent compilers (`gcc`, `clang`, `M2-Planet`) compiling `mm0-c`.

---

### 4. Cross-Foundation Proof Interchange (`MM` / `HOL` / `Lean 4` $\leftrightarrow$ `MM0`)

Basis: source (`digama0/mm0/README.md`) + documentation (`arXiv:1910.10703v3` Section 5).

Because MM0 fixes no built-in logic, it acts as a cross-system interchange hub (`mm0-hs`):
- **Outward (`MM0 -> HOL / OpenTheory / Lean`)**: `mm0-hs to-hol` translates MM0 higher-order metavariables $\phi : s(\vec{x})$ into curried functions $\phi : s_1 \to \dots \to s_n \to s$ and quantifies hypotheses universally, targeting OpenTheory (HOL Light, HOL4, Isabelle, ProofPower) and Lean. Carneiro demonstrated this end-to-end by importing `set.mm` (`from-mm`) and porting Dirichlet's theorem on primes in arithmetic progressions into Lean (`mm0-lean/mm0/set/post.lean`), requiring only an isomorphism theorem between `set.mm`'s $\mathbb{N}$ and Lean's `Nat`.
- **Inward (`Lean 4 -> MM0`)**: Directly exporting Lean 4 proof terms shallowly to MM0 fails because MM0 lacks built-in CIC β/δ/ι/η conversion, universe `imax`, quotient reductions, and proof irrelevance: every kernel conversion check would have to be expanded into explicit congruence/substitution proof steps (`O(N · WHNF steps)` proof-size blowup). Instead, Carneiro (`arXiv:1910.10703v3` Section 5 & `arXiv:2403.14064v3`) proposes two scalable paths:
  1. **Deep-embedded CIC kernel axioms in `.mm0`**: Specify Lean's declarative typing judgment (`VEnv.IsDefEq`) inside an `.mm0` ZFC+$n$-inaccessibles theory and emit `.mmb` derivations justifying each exported declaration.
  2. **Cross-verified machine-code checkers (`O(n)` spider-web)**: Prove a Lean 4 checker (such as `Lean4Lean` or a `nanoda`-like Rust/MMC checker) sound in MM0 and compile it with `mmc` to an MM0-verified x86-64 ELF binary, avoiding per-proof `.mmb` reduction blowup while keeping only the `mm0-c` / `mmc` base in the hardware-rooted TCB.

---

### 5. Head-to-Head TCB & Architectural Comparison: `MM0/MMC` vs. `CakeML/Candle` vs. `MetaRocq/CertiCoq`

Basis: source (`CakeML/candle/fusion.ml`, `jrh13/hol-light/fusion.ml`, `MetaRocq/metarocq/README.md`, `CertiCoq/certirocq/README.md`, `digama0/mm0/examples/compiler.mm0`) + normative (`DOI: 10.4230/LIPIcs.ITP.2022.3`, `DOI: 10.1017/S0956796818000229`, `DOI: 10.1145/3706056`).

| Architecture Axis | `MM0` (`mm0-c` + `mmc` / `x86.mm0`) | `CakeML` + `Candle` (`ITP 2022`) | `MetaRocq` + `CertiCoq` (`JACM 2025`) |
| :--- | :--- | :--- | :--- |
| **Core Kernel Paradigm** | **Certificate checker** over untrusted `.mmb` binary proof DAG (`1,470` LoC C core); zero built-in conversion | **Stateless LCF** abstract `thm` type (`676` LoC ML ported from `jrh13/hol-light`'s `680`-LoC `fusion.ml`) | **CIC typechecker (`SafeChecker`)** over PCUIC AST + certified erasure (`LambdaBox`) |
| **Machine-Code Target & Verification Depth** | User-mode x86-64 Linux ELF (`x86.mm0`); **proof-producing** per-program compilation (`mmc`), **`sorry` still present** in `examples/compiler.mm0` | **Completed** HOL4 verification through 12+ CakeML compiler passes down to x86-64, ARMv8, RISC-V, MIPS, Silver ISA (`Tan et al. JFP 2019`) | CertiRocq compiles `LambdaBox` -> `LambdaANF` -> CompCert `Clight` & WebAssembly; relies on unverified OCaml/CompCert assembly or C runtime |
| **Runtime & Memory Model** | Zero GC in `mm0-c` (`mmap` + static 64 MiB store); compiler-controlled $O(1)$ pointer equality | Verified copying/generational GC in CakeML; **no let-polymorphism, no modules/functors, no pointer equality `(==)`** in Candle | Verified C mark-sweep GC (`CertiRocq`) + CompCert memory model; OCaml GC for standard extraction |
| **Fast Evaluation Story** | Proofs carry pre-evaluated traces (`mm0-rs` Scheme tactics); zero kernel compute needed | Added verified **`candle_compute.ml` (`cv_compute`-style)** in-logic evaluation primitive to mitigate pure LCF inference slowdowns | `vm_compute` / `native_compute` in Rocq (unverified C/OCaml bytecode vs MetaRocq's pure PCUIC reduction) |
| **Residual Unverified TCB** | Human inspection of `.mm0` + `x86.mm0` Sail port + (currently) `compiler.mm0`'s `sorry` + C compiler (`stage0-posix` mitigates) | HOL4 kernel + SML bootstrap compiler (`MLton`/`PolyML`, mitigated by CakeML in-logic self-compilation) + Fox L3 ISA specs | Rocq kernel + MetaRocq's **axiomatized inductive guard checker** + CompCert `asm` / C FFI glue |

---

### 6. Six-Level (L1–L6) Quantitative Comparison Across Proof Kernels and Bootstrapping Stacks

Basis: execution (Probe 2 `gcc`/runtime benchmarks) + documentation (`arXiv:1910.10703v3`, `DOI: 10.4230/LIPIcs.ITP.2022.3`, `README.md` across repos) + source (`mm0-c/`, `fusion.ml`).

| System | (L1) Authoring & Proof-Repair Velocity | (L2) Toolchain Build Time & RSS | (L3) Front-End Compile / Elab Speed | (L4) Runtime / Generated Execution Speed | (L5) Proof / Certificate Checking Speed | (L6) Binary, Artifact & Memory Footprints |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`mm0-c` + `mm0-rs` (`MMC`)** | `mm0-c`: **2,857 LoC** (`1,470` core); `x86.mm0`: **1,727 LoC**; Scheme tactics in `.mm1`; `peano.mm1` (~1,000 thms) | `gcc -O2`: **`4.76 s` / `61.8 MiB` RSS** (`std`); **`597.6 ms` / `43.3 MiB` RSS** (`-DBARE -DNO_PARSER`); `mm0-rs` Rust release build | `mm0-rs` compiles `peano.mm1` in **`306 ± 4 ms`** (`< 500 ms` LSP keystroke feedback); Scheme meta-eval | Native x86-64 ELF (`mmc`) with zero GC tax; `mm0-c` stack/heap machine uses static arrays | **`set.mm` (< 200 ms)** in `mm0-c`; `peano.mmb` (**`2 ± 0.05 ms`**); Probe 2 `hilbert`: **`13.6–19.1 ms` cold median** (**`2.6 ms` min**) | ELF: **`62,120 B`** (`std`), **`21,624 B`** (`bare`), **`18,640 B`** stripped (`9,141 B` `.text`); `.bss`: `658 MiB` (`std`), `64.8 MiB` (`bare`); runtime RSS **`12.2–13.9 MiB`** (`< 1 MiB` store highwater on `set.mm`) |
| **`metamath-knife` (Rust)** | Rust workspace (`metamath-rs` + `metamath-knife`); zero built-in conversion tactics | `cargo build --release` (`codegen-units=1`, LTO-free); builds in seconds | N/A (checks classical `.mm` sources directly; grammar check `-g`) | N/A (pure verifier) | **`< 1 s`** on `set.mm` (> 28,000 proofs, `--jobs 4 --split`); supports incremental `--repeat` | Native Rust binary + in-memory `set.mm` segment graph (~tens of MiB RSS) |
| **`oriansj/stage0-posix`** | `hex0` seed (**256 bytes** machine code) -> `M1` -> `hex2` -> `M2-Planet` C subset -> `live-bootstrap` | Host-free seed bootstrap (`kaem-optional-seed`); multi-minute/hour full `GCC+Guile` cascade | Minimal single-pass `M2-Planet` C compilation (no global optimization) | Unoptimized generated assembly until Stage 2 GCC takes over | Human visual hex audit of **256-byte `hex0`** seed | **256-byte** binary seed; zero dynamic linker / external libc in early stages |
| **`HOL Light` (`jrh13/hol-light`)** | **680-LoC** `fusion.ml` OCaml kernel; vast automation & tactic libraries | Native `ocamlopt` build in seconds | Interactive OCaml toplevel; tactic replay depends on `MESON`/`SIMP` search | Full `ocamlopt` native machine code + tuned generational OCaml GC | **Forward LCF replay**: must re-execute all tactic derivations from scratch | Multi-MiB OCaml bytecode/native heap; **zero stored proof objects** on disk |
| **`CakeML` + `Candle` (`ITP 2022`)** | **676-LoC** `fusion.ml` ported to CakeML + `~100+ KLoC` HOL4 CakeML compiler/GC proofs (`Candle` excludes let-poly & modules) | **~14 hours** (`~50,400 s`) to replay CakeML compiler correctness proof in HOL4 (`arXiv:1910.10703v3`, p. 30) | Interactive CakeML REPL compiles ML inside verified compiler loop | Slower than `ocamlopt` (verified generational GC & simpler unboxing); mitigated by `candle_compute.ml` | Must replay HOL Light proof scripts inside verified CakeML REPL (orders of magnitude slower than `mm0-c` on `set.mm`) | Multi-MiB CakeML ELF binary (`x86_64` / `ARMv8` / `RISC-V`); verified heap & stack |
| **`MetaRocq` + `CertiCoq` (`JACM 2025`)** | **~300 KLoC** Rocq + **~30 KLoC** OCaml (`MetaRocq`); high Day-2 repair cost for PCUIC/erasure changes | Tens of minutes to hours for full `MetaRocq` + `CertiCoq` + `CompCert` `coqc` proof builds | Elaboration in Rocq (`coqc`) + `MetaRocq Quote` reification + ANF/Clight pipeline | Compiled C (`CompCert`/`gcc`) or Wasm with verified C mark-sweep GC (`CertiRocq`) | Bootstrapped `SafeChecker` (`CertiRocq`-compiled) cannot yet verify all of Rocq stdlib (`eta`/template poly gaps); much slower than C++/MM0 | Multi-MiB `.vo` libraries + generated `.c`/`.wasm` + C GC runtime heap |

## Boundaries

- **known not to apply**:
  - At pinned commit `0d414c0bfdaaeb7fea571895127abc1fa5a3d956`, `digama0/mm0` **does not yet provide** a complete `sorry`-free self-verifying ELF proof of `verifier.mm0`: `examples/compiler.mm0` lines 5–8 explicitly declare `axiom sorry (p: wff): $ p $;` and `term sorry_{nat,set,wff}` as placeholders for unfinished compiler proofs.
  - Proving `Verifier_Valid` alone **does not guarantee** soundness of the checked specification without pairing it with `Verifier_terminates` and observing exit code `0` on concrete input, because a verifier that always exits non-zero trivially satisfies `succeeds k mm0_file 0 -> Valid mm0_file`.
  - Classical `metamath-knife` checks **do not verify** grammar unambiguity or definitional conservativity as part of the proof verifier itself, unlike MM0's kernel-checked `def` and deterministic parser contract.
- **unsupported**:
  - `mm0-c` explicitly aborts on big-endian hosts, architectures lacking `__attribute__((packed))` `sizeof(cmd32) == 5` or 4-byte `store_expr` alignment (`mm0-c/main.c:15–28`), specifications exceeding 55 active bound variables per declaration (`next_bv < 55`), or `--bare` builds attempting to use `CMD_PROOF_SORRY` (`0x20`).
  - `examples/x86.mm0` omits floating-point, vector/SIMD (`SSE`/`AVX`), kernel-mode privilege rings, and multi-core concurrency (`user-mode` Linux syscalls only).
  - `CakeML/candle` does not support OCaml `let`-polymorphism, modules/functors, `open`, polymorphic `Pervasives.compare`, or physical pointer equality `(==)` (`CakeML/candle/README.md`).
  - `MetaRocq/metarocq` does not verify Rocq's inductive guard checker (axiomatized) or full template polymorphism / module system (`arXiv:2403.14064v3` Section 8, `MetaRocq/README.md`).
- **unknown**:
  - The exact compressed `.mmb` proof size, `g_store` highwater, and `mm0-c` verification latency of a completed, `sorry`-free `verifier.mm1` x86-64 proof remain unknown until the remaining `compiler.mm1` proofs are discharged (Carneiro estimates $\le 100\times$ `peano.mm1` in `arXiv:1910.10703v3`, p. 23, which remains a projection).
  - Exact quantitative runtime slowdown ratios of `CakeML/candle` vs native `jrh13/hol-light` (`ocamlopt`) across the full HOL Light multivariable/real-analysis library were not directly executed in this study.
- **not examined**:
  - Formal gate-level or FPGA Verilog verification stacks below the ISA abstraction (e.g., CakeML on the Silver hardware-verified processor or `builder-hex0` kernel bootstrap).
  - Third-party Rust/Kotlin/Zig MM0 verifiers (`second_opinion`, `trivial-rs`, `mm0kt`, `mm0-zig`) beyond the upstream `mm0-c` reference implementation.

## Evidence

### Primary Repositories, Commits, and Source Locations Inspected
- `digama0/mm0` (`0d414c0bfdaaeb7fea571895127abc1fa5a3d956`):
  - `README.md` (lines 74–238), `mm0.md` (1–100, lexical/specification contract), `mm0-rs/mmc.md` (1–95), `mm0-c/mmb.md` (1–280, `.mmb` v1 header, sort/term/thm tables, `arg = u64`, dual-stream semantics).
  - `mm0-c/` (total `2,857` LoC / `95,393` B): `main.c` (1–79, endian/alignment static asserts & `mmap`), `types.c` (1–329, `CMD_*` & `CMD_UNIFY_*` opcodes `0x00–0x36`), `verifier_types.c` (1–243, `STACK_SIZE`, `STORE_SIZE = 1<<26`, `g_store`, parser tries), `verifier.c` (1–819, `run_unify`, `run_proof`, `CMD_PROOF_THM` at 480–515, `#ifndef BARE` `CMD_PROOF_SORRY` at 634–650, `verify` loop at 670–819), `parser.c` (1–904, `parse_until` at 612–637), `verifier_debug.c` (322 LoC), `index.c` (161 LoC).
  - `examples/verifier.mm0` (1–29, `Verifier_basicElf`, `Verifier_terminates`, `Verifier_Valid`), `examples/compiler.mm0` (1–13, `axiom sorry`), `examples/x86.mm0` (1–60 of 1,727 LoC).
- `david-a-wheeler/metamath-knife` (`76fc9f7f39f46f4c43499a0c2bd1402eb8b1cf9a`): `README.md` (1–90), `Cargo.toml`.
- `oriansj/stage0-posix` (`643598041bf7639883874fe2cdc9d9693c9b03d5`): `README.md` (1–80, 256-byte `hex0` seed bootstrap chain).
- `CakeML/candle` (`a9aeaa1dffd50f7cfeed811db6ee61f98e2234da`): `README.md` (1–90), `fusion.ml` (`676` LoC / `28,539` B); `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`).
- `jrh13/hol-light` (`6dbb775efdff7f75aa20006532bf6336bc645861`): `fusion.ml` (`680` LoC / `28,873` B).
- `MetaRocq/metarocq` (`51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56`): `README.md` (`~300 KLoC` Rocq / `~30 KLoC` OCaml); `CertiCoq/certirocq` (`ab66e0164e7ecb63e5af95c90c8e479068bf95c2`): `README.md`.

### Peer-Reviewed Literature
- Mario Carneiro, *Metamath Zero: The Cartesian Theorem Prover*, `arXiv:1910.10703v3` (30 Mar 2020), extended version of *Metamath Zero: Designing a Theorem Prover Prover*, CICM 2020 (LNCS 12236, pp. 71–88), `DOI: 10.1007/978-3-030-53518-6_5`.
- Oskar Abrahamsson, Magnus O. Myreen, Ramana Kumar, Thomas Sewell, *Candle: A Verified Implementation of HOL Light*, ITP 2022, LIPIcs Vol. 237, `DOI: 10.4230/LIPIcs.ITP.2022.3`.
- Yong Kiam Tan, Magnus O. Myreen, Ramana Kumar, Anthony Fox, Scott Owens, Michael Norrish, *The verified CakeML compiler backend*, J. Funct. Program. 29, 2019, `DOI: 10.1017/S0956796818000229`.
- Matthieu Sozeau, Yannick Forster, Meven Lennon-Bertrand, Jakob Nielsen, Nicolas Tabareau, Théo Winterhalter, *Correct and Complete Type Checking and Certified Erasure for Coq, in Coq*, J. ACM 72(1), Article 8, Jan 2025, `DOI: 10.1145/3706056` (preceded by *The MetaCoq Project*, JAR 2020, `DOI: 10.1007/s10817-019-09540-0`).

### Inline Compilation, Binary `.mmb` Generation, Cold-Start Benchmark, and Tamper Probe

Compiled upstream `digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956/mm0-c/` on x86-64 Linux (`observed_at: 2026-11-19`) and executed `probe_mm0c_mmb.py`:

```bash
gcc -O2 mm0-c/main.c -o mm0-c_bin
gcc -O2 -DNO_PARSER -DBARE mm0-c/main.c -o mm0-c_bare
cp mm0-c_bare mm0-c_bare_stripped && strip mm0-c_bare_stripped
```

```python
#!/usr/bin/env python3
"""Minimal self-contained .mm0 + .mmb v1 Hilbert-calculus specimen, cold-start benchmark, and tamper test."""
import os, statistics, struct, subprocess, time

MM0_SPEC = """delimiter $ ( ) $;
provable sort wff;
term im: wff > wff > wff; infixr im: $->$ prec 1;
axiom a1 (a b: wff): $ a -> b -> a $;
axiom a2 (a b c: wff): $ (a -> b -> c) -> (a -> b) -> a -> c $;
axiom mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
theorem a1i (a b: wff) (h: $ a $): $ b -> a $;
theorem id (a: wff): $ a -> a $;
"""

CMD_END, CMD_STMT_AXIOM, CMD_STMT_SORT, CMD_STMT_DEF, CMD_STMT_THM = 0x00, 0x02, 0x04, 0x05, 0x06
CMD_PROOF_TERM, CMD_PROOF_TERM_SAVE, CMD_PROOF_REF, CMD_PROOF_THM, CMD_PROOF_HYP, CMD_PROOF_SORRY = 0x10, 0x11, 0x12, 0x14, 0x16, 0x20
CMD_UNIFY_TERM, CMD_UNIFY_REF, CMD_UNIFY_HYP = 0x30, 0x32, 0x36

def enc_cmd(op, data=0):
    if data == 0: return struct.pack("<B", op)
    if data < 256: return struct.pack("<BB", op | 0x40, data)
    if data < 65536: return struct.pack("<BH", op | 0x80, data)
    return struct.pack("<BI", op | 0xC0, data)

def enc_stmt(op, payload):
    for hdr_sz in (1, 2, 3, 5):
        b = enc_cmd(op, hdr_sz + len(payload))
        if len(b) == hdr_sz: return b + payload
    raise ValueError("too large")

def make_arg(sort_id, bound=False, deps=0):
    return (deps & ((1 << 55) - 1)) | ((sort_id & 0x7F) << 56) | ((1 if bound else 0) << 63)

def build_hilbert_mmb(inject_sorry=False):
    buf = bytearray(48)
    pad8 = lambda: buf.extend(b"\x00" * ((-len(buf)) % 8))
    p_terms = len(buf); buf.extend(b"\x00" * 8); pad8()
    term0_off = len(buf); buf.extend(struct.pack("<QQQ", make_arg(0), make_arg(0), make_arg(0)))
    struct.pack_into("<HBB I", buf, p_terms, 2, 0, 0, term0_off)
    pad8(); p_thms = len(buf); buf.extend(b"\x00" * 40)
    thm_specs = [
        (2, bytes([*enc_cmd(CMD_UNIFY_TERM, 0), *enc_cmd(CMD_UNIFY_REF, 0), *enc_cmd(CMD_UNIFY_TERM, 0), *enc_cmd(CMD_UNIFY_REF, 1), *enc_cmd(CMD_UNIFY_REF, 0), CMD_END])),
        (3, bytes([*enc_cmd(CMD_UNIFY_TERM, 0), *enc_cmd(CMD_UNIFY_TERM, 0), *enc_cmd(CMD_UNIFY_REF, 0), *enc_cmd(CMD_UNIFY_TERM, 0), *enc_cmd(CMD_UNIFY_REF, 1), *enc_cmd(CMD_UNIFY_REF, 2), *enc_cmd(CMD_UNIFY_TERM, 0), *enc_cmd(CMD_UNIFY_TERM, 0), *enc_cmd(CMD_UNIFY_REF, 0), *enc_cmd(CMD_UNIFY_REF, 1), *enc_cmd(CMD_UNIFY_TERM, 0), *enc_cmd(CMD_UNIFY_REF, 0), *enc_cmd(CMD_UNIFY_REF, 2), CMD_END])),
        (2, bytes([*enc_cmd(CMD_UNIFY_REF, 1), *enc_cmd(CMD_UNIFY_HYP), *enc_cmd(CMD_UNIFY_REF, 0), *enc_cmd(CMD_UNIFY_HYP), *enc_cmd(CMD_UNIFY_TERM, 0), *enc_cmd(CMD_UNIFY_REF, 0), *enc_cmd(CMD_UNIFY_REF, 1), CMD_END])),
        (2, bytes([*enc_cmd(CMD_UNIFY_TERM, 0), *enc_cmd(CMD_UNIFY_REF, 1), *enc_cmd(CMD_UNIFY_REF, 0), *enc_cmd(CMD_UNIFY_HYP), *enc_cmd(CMD_UNIFY_REF, 0), CMD_END])),
        (1, bytes([*enc_cmd(CMD_UNIFY_TERM, 0), *enc_cmd(CMD_UNIFY_REF, 0), *enc_cmd(CMD_UNIFY_REF, 0), CMD_END])),
    ]
    for tid, (nargs, ustream) in enumerate(thm_specs):
        pad8(); off = len(buf)
        for _ in range(nargs): buf.extend(struct.pack("<Q", make_arg(0)))
        buf.extend(ustream); struct.pack_into("<HHI", buf, p_thms + tid * 8, nargs, 0, off)
    p_proof = len(buf)
    buf.extend(enc_stmt(CMD_STMT_SORT, b"")); buf.extend(enc_stmt(CMD_STMT_DEF, b""))
    buf.extend(enc_stmt(CMD_STMT_AXIOM, bytes([*enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 1), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_TERM, 0), *enc_cmd(CMD_PROOF_TERM, 0), CMD_END])))
    buf.extend(enc_stmt(CMD_STMT_AXIOM, bytes([*enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 1), *enc_cmd(CMD_PROOF_REF, 2), *enc_cmd(CMD_PROOF_TERM, 0), *enc_cmd(CMD_PROOF_TERM, 0), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 1), *enc_cmd(CMD_PROOF_TERM, 0), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 2), *enc_cmd(CMD_PROOF_TERM, 0), *enc_cmd(CMD_PROOF_TERM, 0), *enc_cmd(CMD_PROOF_TERM, 0), CMD_END])))
    buf.extend(enc_stmt(CMD_STMT_AXIOM, bytes([*enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 1), *enc_cmd(CMD_PROOF_TERM, 0), *enc_cmd(CMD_PROOF_HYP), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_HYP), *enc_cmd(CMD_PROOF_REF, 1), CMD_END])))
    buf.extend(enc_stmt(CMD_STMT_THM, bytes([*enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_HYP), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 1), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 1), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_TERM_SAVE, 0), *enc_cmd(CMD_PROOF_TERM, 0), *enc_cmd(CMD_PROOF_THM, 0), *enc_cmd(CMD_PROOF_REF, 2), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 3), *enc_cmd(CMD_PROOF_REF, 3), *enc_cmd(CMD_PROOF_THM, 2), CMD_END])))
    id_body = bytes([*enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_TERM, 0), *enc_cmd(CMD_PROOF_SORRY), CMD_END]) if inject_sorry else bytes([
        *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_TERM_SAVE, 0), *enc_cmd(CMD_PROOF_TERM_SAVE, 0),
        *enc_cmd(CMD_PROOF_REF, 1), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 1), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_TERM_SAVE, 0), *enc_cmd(CMD_PROOF_TERM_SAVE, 0),
        *enc_cmd(CMD_PROOF_REF, 2), *enc_cmd(CMD_PROOF_REF, 1), *enc_cmd(CMD_PROOF_TERM_SAVE, 0),
        *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 1), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 4), *enc_cmd(CMD_PROOF_REF, 5), *enc_cmd(CMD_PROOF_TERM, 0), *enc_cmd(CMD_PROOF_THM, 1),
        *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 1), *enc_cmd(CMD_PROOF_REF, 4), *enc_cmd(CMD_PROOF_THM, 0),
        *enc_cmd(CMD_PROOF_REF, 5), *enc_cmd(CMD_PROOF_THM, 2),
        *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 0), *enc_cmd(CMD_PROOF_REF, 2), *enc_cmd(CMD_PROOF_THM, 0),
        *enc_cmd(CMD_PROOF_REF, 1), *enc_cmd(CMD_PROOF_THM, 2), CMD_END])
    buf.extend(enc_stmt(CMD_STMT_THM, id_body)); buf.append(CMD_END); buf.extend(b"\x00" * 4)
    struct.pack_into("<4sBBHIIIIIIQ", buf, 0, b"MM0B", 1, 1, 0, 1, 5, p_terms, p_thms, p_proof, 0, 0)
    buf[40:41] = b"\x04"
    return bytes(buf)
```

Observed output (`2026-11-19`):

```text
gcc std: rc=0, elapsed=4764.1 ms, maxrss=61760 KiB  (ELF 62120 B; .text=44269, .data=760, .bss=690235056)
gcc bare: rc=0, elapsed=597.6 ms, maxrss=43300 KiB  (ELF 21624 B / 18640 B stripped; .text=9141, .data=656, .bss=67899616)
Generated hilbert.mm0 (319 B) and hilbert.mmb (385 B)
  std  valid.mmb   -> exit=0 (OK)           [single run: 4.97 ms, maxrss=13876 KiB]
  bare valid.mmb   -> exit=0 (OK)           [single run: 10.53 ms, maxrss=12184 KiB]
  std  sorry.mmb   -> exit=3 (error: some theorems used sorry)
  bare sorry.mmb   -> exit=255 (OK)
  std  tamper.mmb  -> exit=255 (5: expr (t0 (t0 v0 (t0 v0 v0)) (t0 v0 v0)))
  mm0-c std  100x cold-start: median=19.116 ms, p95=117.423 ms, min=3.235 ms
  mm0-c bare 100x cold-start: median=13.593 ms, p95=41.789 ms, min=2.638 ms
```

## Revalidation

1. **Check MM0 self-verification completion (`< 2 s`)**: Inspect `examples/compiler.mm0` and `examples/verifier.mm1` in newer revisions of `digama0/mm0` for removal of `axiom sorry`, and verify `verifier.mmb` under `mm0-c -DNO_PARSER -DBARE` (`exit 0`).
2. **Replay `mm0-c` golden `.mmb` probe (`< 5 s`)**: Recompile `mm0-c/main.c` with `gcc -O2 -DNO_PARSER -DBARE`, run against the inline `hilbert.mm0` / `hilbert.mmb` specimen, confirm `exit 0` on valid proof and `exit != 0` on both `sorry.mmb` (`exit 255`) and mutated proof bytes.
3. **Compare peer kernels**: Diff `CakeML/candle/fusion.ml` (`676` LoC) and `MetaRocq/metarocq` axiom declarations (`guard_checker` axioms) to track reductions in unverified TCB boundaries across upstream releases.
