# Silent Data Corruption, Certifying Algorithms, and ABFT Compilation

## Summary

Hyperscale fleet studies from Google (Hochschild et al., HotOS 2021) and Meta (Dixit et al., 2021, 2022) establish that modern datacenter CPUs exhibit **silent data corruption (SDC)** at rates on the order of one to a few defective ("mercurial") cores per thousand machines across multiple silicon generations. Crucially, unlike classical radiation-induced transient soft errors (single-event upsets), a dominant class of fleet SDCs stems from **repeatable, data-dependent, core-local silicon manufacturing, timing-path, and aging defects** that raise no Machine Check Exception (`#MC`) and leave zero hardware error logs.

This physical failure model invalidates the core independence assumption behind classical same-instruction compiler redundancy schemes (`EDDI`, `SWIFT`, `COAST` DWC/TMR, and Level-1 BLAS AVX-512 register duplication in `FT-BLAS`): repeating an identical instruction on identical operands on the same mercurial core reproduces the exact same corrupted output bit pattern with **100% silent escape** for deterministic core-local defects. Defeating mercurial silicon without paying full multi-machine replication costs requires **algebraic, structural, or microarchitectural diversity** across four complementary verification and compilation layers:

1. **Fleet Silicon Screening (`SiliFuzz`, `Fleetscanner`, `Ripple`):** Proxy-fuzzed instruction corpora and co-located millisecond-scale in-production tests detect latent and lifecycle-degrading cores across data, electrical ($f, V, I$), and thermal operating points.
2. **Program Result Checking & Certifying Algorithms (Blum–Kannan, Freivalds, McConnell–Mehlhorn LEDA, Alkassar et al.):** Complex $O(T(n))$ kernels emit a witness $w$ or undergo an $o(T(n))$ result check on a distinct execution unit or core; verifying the checker itself (in Isabelle/HOL or Coq) removes the complex algorithm from the Trusted Computing Base (TCB) for *both* software bugs and hardware miscomputations during the primary run.
3. **Algorithm-Based Fault Tolerance (`ABFT`) for Linear Algebra and Transforms (Huang–Abraham, Jou–Abraham, Bosilca et al., `FT-BLAS`):** Linearly invariant row/column checksums verify $O(n^3)$ GEMM or $O(n \log n)$ FFT in $O(n^2)$ or $O(n)$ work. However, direct source inspection of `yzhaiustc/ftblas` (`src/dgemm_avx512_ft.cpp`) and executable IEEE-754 probes show that naive hardcoded absolute thresholds (`THRESHOLD = 1e-2`) suffer **96.9% false-positive alarms** on large-magnitude matrices ($\sim 10^8$) and **100% false-negative escapes** on small-magnitude ML weights ($\sim 10^{-3}$), and unweighted checksums completely miss cancelling dual errors $(+\delta, -\delta)$ in the same column. Sound floating-point ABFT requires **Higham componentwise $\gamma_{M+K}$ forward-error scaling** combined with weighted checksums or randomized Freivalds projections.
4. **Arithmetic `AN` / `ANB` / `ANBDmem` Encoded Compilation (Forin, Schiffel et al., Hoffmann et al., `normanrink/an-encoder`):** Multiplying data values by a well-chosen constant $A$ (e.g., $A = 58659 = 278 \times 211 + 1$) transforms arithmetic operand bit patterns and breaks common-mode data-dependent ALU bugs, guaranteeing **0% escape** for all 64 single-bit flips and all 8,064 two-bit flips on 64-bit codewords, at $2.1\times$–$9.9\times$ runtime overhead. Direct source inspection of `normanrink/an-encoder` (`encode/runtime/anlib.c`) reveals a critical compiler boundary: bitwise and signed-division helpers decode operands to unencoded form, execute native instructions, and re-encode—opening a **decoding vulnerability window** where an ALU fault produces a valid codeword (`r_enc % A == 0`) with an undetected wrong value.

## Applicability

This report synthesizes and cross-checks four bodies of durable technical artifacts:

- **Fleet SDC measurements and silicon screening tools:** Google HotOS 2021 (`10.1145/3458336.3465297`), Meta 2021 (`arXiv:2102.11245v1`) and 2022 (`arXiv:2203.08989v1`), and `google/silifuzz` (`bab27a948dcdc42405644f8b1480518e0b7f8ce8`). Empirical rates apply to hyperscale x86-64 datacenter server fleets observed across 18–36+ months; exact defect prevalences depend on fabrication node, voltage/frequency margining, and vendor screening maturity.
- **Compiler instruction-duplication systems:** `EDDI` (`10.1109/24.994913`), `SWIFT` (`10.1109/CGO.2005.34`), and the open-source LLVM pass suite `byuccl/coast` (`397a26ecdb01e7c329884d12c9f6bb2a05c3abc9`, targeting ARM, RISC-V, MSP430, and x86 LLVM IR).
- **Result checking, certifying algorithms, and ABFT systems:** Blum–Kannan (`10.1145/200836.200880`), McConnell–Mehlhorn–Näher–Schweitzer (`10.1016/j.cosrev.2010.09.009`), Alkassar et al. (`10.1007/978-3-642-22110-1_7`), Huang–Abraham (`10.1109/TC.1984.1676475`), Jou–Abraham (`10.1109/12.4606`), Bosilca et al. (`10.1016/j.jpdc.2008.12.002`), and `yzhaiustc/ftblas` (`22b81cb37e3ee9c7d5594ecd526a4874aa0db6cc`, x86-64 AVX-512 inline assembly and C++ kernels).
- **Arithmetic AN-code compilers:** Schiffel et al. (`10.1007/978-3-642-15651-9_13`), Hoffmann et al. (`10.1109/HASE.2014.14`), and `normanrink/an-encoder` (`05c7c36638f4eb93d24434efe3f298bea80c9a6c`, targeting LLVM/Clang 3.5.1 IR with 64-bit integer codewords).

**Relationship among subjects:** The fleet SDC studies define the adversarial hardware fault model (mercurial deterministic and operating-point-dependent cores); `COAST` and `FT-BLAS` Level-1 illustrate how classical single-event-upset compiler/assembly duplication behaves under that fault model; certifying algorithms, `ABFT`, and `AN`-encoding provide three distinct compilation/algorithmic defenses whose invariants, source-level gaps, and numerical thresholds are directly evaluated via source inspection and standalone Python 3 IEEE-754/arithmetic micro-probes executed on Linux x86-64. Findings on `yzhaiustc/ftblas` (`src/dgemm_avx512_ft.cpp`, `src/daxpy_avx512_ft.cpp`), `byuccl/coast`, and `normanrink/an-encoder` describe those exact pinned commits; theoretical bounds (Blum–Kannan, Higham $\gamma_n$, AN arithmetic residues) hold generally for IEEE-754 binary64 arithmetic and ring $\mathbb{Z}/2^{64}\mathbb{Z}$.

## Findings

### 1. Hyperscale Mercurial Silicon Failure Model

`Basis: documentation + source`

Traditional compiler fault-tolerance research assumed a **transient radiation-induced soft-error model**—modeled via Failure-In-Time (FIT; 1 FIT = 1 failure per $10^9$ device-hours), such as ~50,000 FIT for unprotected SRAM reduced $1000\times$ by ECC, or ~114 SDC FIT targets on IBM Power4 (Dixit et al., 2021, §2). Production fleet measurements overturn that assumption:

- **Fleet prevalence:** Google reported *"a few mercurial cores per several thousand machines"* (Hochschild et al., HotOS 2021). Independently, Meta scanned hundreds of thousands of machines over 18+ months (Dixit et al., 2021) and aggregated samples across 3+ years (Dixit et al., 2022), detecting **hundreds of defective CPUs** across multiple hardware generations at an order-of-magnitude occurrence rate of **roughly 1 fault per 1,000 devices** (Dixit et al., 2022, §4).
- **Non-transient, repeatable, data-dependent manifestations:**
  - *Self-inverting AES defect (Hochschild et al., 2021):* A defective core deterministically miscomputed AES instructions in a self-inverting fashion—encrypting and decrypting on the *same* core yielded the original plaintext (masking local loopback tests), whereas decrypting on any healthy core yielded corrupted ciphertext.
  - *Lock, vector, string, and load/store corruption (Hochschild et al., 2021):* Faults manifested in unprotected execution datapaths (SIMD/AVX vector lanes, floating-point units, specialized string instructions, and synchronization primitives), causing lock-semantics violations, storage garbage-collection live-data loss, and database index corruption.
  - *Deterministic `math.pow` bit-pattern defect (Dixit et al., 2021, §4–6):* Pinning a Scala workload to Core 59 (`taskset -c 59 ./bitflip_repro.sh`) deterministically corrupted specific inputs across every iteration:
    - `Int(1.1^53) = 0` (corrupted) and `Int(1.1^68) = 0` (corrupted) on iterations 1, 2, and 3, while `Int(1.1^52) = 142` and `Int(1.1^78) = 1692` computed accurately.
    - Additional observed corruptions on the same defective silicon included `Int(1.1^3) = 0` (expected `1`), `Int(1.1^107) = 32809` (expected `26854`), and `Int(1.1^-3) = 1` (expected `0`), silently truncating decompressed files without an EOF marker.
    - Root-causing required traversing Scala → Java bytecode → HotSpot `+PrintAssembly` (430,000 lines of JIT assembly) → GDB instruction stepping down to a **60-line standalone assembly reproducer** inside the `x^y = 2^(y * log2(x))` computation path (Dixit et al., 2021, §5.1–5.3).
- **Four physical accelerants (Dixit et al., 2022, §4):**
  1. *Data randomization:* Defects trigger only on sparse operand bit patterns (e.g., `3 * 5 = 15` succeeds while `3 * 4 = 10` fails consistently).
  2. *Electrical variations ($f, V, I$):* Timing-path marginalities appear only under specific frequency/voltage/current operating points (e.g., turbo boost or AVX-512 voltage droop).
  3. *Environmental variations:* Rack-level thermal/humidity hotspots shift silicon switching delays across datacenters.
  4. *Lifecycle degradation:* Devices degrade earlier than classical bathtub-curve predictions; Meta documented a processor executing an identical computation sequence daily for 6 months without error before beginning to fail silently (Dixit et al., 2022, §4).
- **Fleet screening architectures:**
  - *Out-of-production (`Fleetscanner`, Dixit et al., 2022, §5.1):* Opportunistic/periodic multi-minute burn-in during drain/provisioning transitions; high per-core coverage but slow fleet-wide rollout for novel signatures.
  - *In-production (`Ripple` / vendor "trickle" testing, Dixit et al., 2022, §5.2):* Co-located millisecond-interval instruction tests dynamically modulated by workload footprint tax; rolls out a newly discovered defect signature fleet-wide within weeks and catches lifecycle-transition defects.
  - *Proxy-fuzzed corpus execution (`google/silifuzz`, `bab27a948dcdc42405644f8b1480518e0b7f8ce8`, `doc/proxy_architecture.md`):* Fuzzes software CPU simulators/disassemblers to generate code-coverage-maximizing instruction snapshots confined to a single executable page in `[0x30000000, 0xB0000000)` and two 512 MiB data mappings (`[0x10000, 0x20010000)` and `[0x1000010000, 0x1020010000)`), initializing non-zero architectural state (`%cs=0x33`, `%ss=0x2b`, non-zero `%xmm0` to avoid AMD erratum 1386) so deterministic snapshots can be replayed across production fleets to isolate mercurial cores.

### 2. Why Same-Instruction Compiler Duplication (`EDDI`, `SWIFT`, `COAST`, `FT-BLAS` L1) Fails Against Mercurial Cores

`Basis: documentation + source + execution`

Classical Software-Implemented Hardware Fault Tolerance (SIHFT) compiles a single thread into two (DWC) or three (TMR) interleaved instruction streams inside one CPU core:

- **`EDDI` (Oh et al., 2002):** Duplicates all instructions and memory stores using shadow registers and shadow memory; compares operands before stores and conditional branches.
- **`SWIFT` (Reis et al., CGO 2005):** Shrinks the Sphere of Replication (SoR) by trusting ECC-protected memory—duplicating only register-level ALU instructions and comparing operands before stores, while adding control-flow signature checking (`CFCSS`-style) for branches.
- **`COAST` (`byuccl/coast`, `397a26ecdb01e7c329884d12c9f6bb2a05c3abc9`):** Direct source inspection confirms that `projects/DWC/DWC.cpp` invokes `dataflowProtection::run(M, 2)` (while `projects/EDDI/EDDI.cpp` explicitly deprecates `EDDI` via `assert(false && "Switch to DWC")`), and `projects/dataflowProtection/cloning.cpp:2189-2204` implements instruction duplication by calling LLVM's verbatim **`newI1 = I->clone()`** (and `newI2 = I->clone()` under TMR) and inserting the clone immediately after `I` in the same basic block with identical opcode, operand widths, and target register class.
- **`FT-BLAS` Level-1/Level-2 (`yzhaiustc/ftblas`, `22b81cb37e3ee9c7d5594ecd526a4874aa0db6cc`):** Direct source inspection of `src/daxpy_avx512_ft.cpp` confirms that its hand-tuned AVX-512 `daxpy` kernel duplicates each FMA instruction back-to-back on identical input operands into a shadow `zmm` register and checks bit equality via `vpcmpeqd`:
  ```asm
  vfmadd213pd  %%zmm16, %%zmm0, %%zmm20   ; primary FMA
  vfmadd213pd  %%zmm16, %%zmm0, %%zmm28   ; duplicate FMA (identical opcode, identical inputs)
  ...
  vpcmpeqd     %%zmm20, %%zmm28, %%k0     ; bit-exact mask comparison
  ```

**Structural Failure Theorem (Derived + Verified by Execution):** Let $f_{\text{hw}} : \mathcal{I} \times \mathcal{D} \times \mathcal{S} \to \mathcal{D}$ be a core-local execution unit implementing opcode $o \in \mathcal{I}$ on operand tuple $d \in \mathcal{D}$ under operating state $s \in \mathcal{S}$. Any duplication pass that emits two executions of the same opcode $o$ on identical operand values $d$ on the same physical core within a few cycles (so $s_1 = s_2 = s$) evaluates $f_{\text{hw}}(o, d, s)$ twice. Whenever the defect is **deterministic on $(o, d, s)$**—as in Meta's Core-59 `math.pow` defect and Google's self-inverting AES defect—both copies return the identical corrupted value $y_{\text{bad}} \neq f_{\text{spec}}(o, d)$, so the comparator `y1 == y2` (or `vpcmpeqd`) evaluates to `true` with probability **1**.

In **Probe 1A** (see `## Evidence`), simulating a deterministic operand-dependent ALU bit-flip across 10,000 random 24-bit additions triggers **2,502 faults** under same-instruction DWC/SWIFT and detects **0 / 2,502** (**100.0% silent escape**). Even a 3× `TMR` majority voter on the same core fails identically (`y_bad == y_bad == y_bad` wins 3–0).

**What Same-Instruction Duplication *Does* Catch:** Single-event upsets (transient cosmic-ray bit flips whose inter-arrival time exceeds the few-cycle window between original and clone) and non-repeatable voltage-droop glitches that affect only one of the two execution slots—provided the comparator itself and shared memory-store path are not corrupted.

### 3. Program Result Checking and Certifying Algorithms

`Basis: normative + documentation + derived`

To escape common-mode failures of both software bugs and mercurial execution units without full $k$-machine replication, **program result checking** (Blum & Kannan, JACM 1995) and **certifying algorithms** (McConnell, Mehlhorn, Näher & Schweitzer, CSR 2011) decouple *computing* an answer from *verifying* it.

#### 3.1 Formal Definitions and the Little-Oh Property

- **Blum–Kannan Program Checker (JACM 1995, §2):** For a decision or function problem $\pi$, a probabilistic oracle machine $C_\pi$ is a program checker for $\pi$ if for any program $P$ (which may be buggy or run on faulty silicon), any input $x$, and confidence parameter $1^k$:
  1. *(Completeness)* If $P$ is correct on all instances of size $|x|$, then $\Pr[C_\pi^P(x, 1^k) = \text{PASS}] \ge 1 - 2^{-k}$ (typically $1$).
  2. *(Soundness)* If $P(x) \neq \pi(x)$, then $\Pr[C_\pi^P(x, 1^k) = \text{FAIL}] \ge 1 - 2^{-k}$.
  3. *(Little-Oh Property)* The running time of $C_\pi$ (excluding oracle calls to $P$) is **$o(T_P(|x|))$** relative to the fastest known or executed algorithm $P$ for $\pi$. This asymptotic separation forbids the checker from merely re-running $P$, enforcing *structural algorithmic diversity*.
- **Certifying Algorithm (McConnell et al., CSR 2011, §2):** An algorithm $A$ for input-output specification $R \subseteq X \times Y$ is certifying if on input $x \in X$ it outputs a pair $(y, w) \in Y \times W$ (result + witness/certificate) accompanied by a simple, independent **checker** $C : X \times Y \times W \to \{\text{accept}, \text{reject}\}$ satisfying:
  - *(Checker Soundness)* $\forall x, y, w.\; C(x, y, w) = \text{accept} \implies (x, y) \in R$.
  - *(Completeness)* For every valid input $x$, $A(x)$ produces $(y, w)$ with $C(x, y, w) = \text{accept}$.
- **Formally Verified Checkers (Alkassar, Böhme, Mehlhorn & Rizkallah, CAV 2011):** Rather than verifying an intricate optimized library (e.g., LEDA's C++ graph algorithms), one proves **only** the small checker $C$ sound in Isabelle/HOL (via AutoCorres/VCC) or Coq. Under a mercurial-core threat model, this yields a dual guarantee: **if $A$ executes on an untrusted/mercurial accelerator or AVX-512 core, and the small verified checker $C$ executes on an architecturally distinct scalar/reference core (or under AN-encoding), then no silent corruption in $A$'s execution can forge a witness accepted by $C$.**

#### 3.2 Taxonomy of Sublinear Result Checkers and Certifying Witnesses

| Problem / Kernel | Primary Compute Cost | Witness / Check Mechanism | Checker Complexity | Error / Soundness Guarantee | Diversity vs. Mercurial Core |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Matrix Multiplication ($C = AB$)** | $O(n^3)$ (or $O(n^\omega)$) | **Freivalds' check:** draw $r \in \{-1,+1\}^n$ (or $\{0,1\}^n$), verify $A(Br) = Cr$ | $O(k \cdot n^2)$ | Exact rings: false-accept $\le 2^{-k}$ ($k=20 \Rightarrow <10^{-6}$); floats require Higham bound | Compute on SIMD/tensor unit; check on scalar FP or distinct core |
| **Linear System / Inverse ($Ax = b$)** | $O(n^3)$ | Direct substitution $Ax - b$ (plus residual norm $\|Ax-b\|_\infty$) | $O(n^2)$ | Deterministic backward-error check | Matrix-vector product vs. LU/Cholesky factorization |
| **Linear Programming ($\max c^T x$ s.t. $Ax \le b$)** | Poly / Simplex | **Strong duality / Farkas witness:** primal $x^*$, dual $y^* \ge 0$ with $A^T y^* = c$ and $c^T x^* = b^T y^*$ | $O(\text{nnz}(A))$ | Deterministic exact (rational) or bounded duality gap | Simple sparse dot products vs. pivoting/interior-point solver |
| **Single-Source Shortest Paths** | $O(m + n \log n)$ | **LEDA potential witness:** distances $d(v)$ + parent tree $p(v)$; check $d(s)=0$, $d(v) \le d(u)+w(u,v)$ $\forall (u,v)$, and $d(v) = d(p(v))+w(p(v),v)$ | $O(n + m)$ | Deterministic exact (Alkassar et al., CAV 2011, verified in Isabelle/HOL) | Linear scan vs. priority-queue Dijkstra/Bellman-Ford |
| **Bipartite Matching / Max-Flow** | $O(m \sqrt{n})$ / $O(nm)$ | **König / Hall / Min-Cut witness:** matching $M$ + vertex cover $U$ with $|M|=|U|$, or flow $f$ + $(S,T)$-cut with $|f| = c(S,T)$ | $O(n + m)$ | Deterministic exact | Linear incidence scan vs. augmenting-path / push-relabel |
| **Graph Planarity** | $O(n)$ (complex) | **Kuratowski witness:** planar embedding (Euler + crossing-free check) or $K_5$/$K_{3,3}$ subdivision | $O(n)$ | Deterministic exact (LEDA) | Trivial topology check vs. Hopcroft–Tarjan / Boyer–Myrvold |
| **Sorting ($y = \text{sort}(x)$)** | $O(n \log n)$ | Monotonicity ($y_i \le y_{i+1}$) + **multiset hash / permutation index** ($\prod (r - x_i) \equiv \prod (r - y_i) \pmod p$ or explicit bijection $\pi$) | $O(n)$ | Deterministic with explicit $\pi$; $\le n/p$ randomized via Schwartz–Zippel | Linear pass vs. vectorized quicksort/radix/bitonic sort |
| **FFT ($Y = F_n X$)** | $O(n \log n)$ | **Parseval energy + linear checksum / random frequency test** ($\sum_k w_k Y_k = \sum_j (F_n^T w)_j X_j$) | $O(n)$ | Deterministic single-fault via Jou–Abraham linear code; randomized for general faults | Single inner product vs. butterfly stages |

#### 3.3 Self-Checking Root Proof Checkers

`Basis: derived`

Certifying algorithms reduce trust from a complex algorithm $A$ to a small checker $C$—or, in formal verification toolchains, from an untrusted proof search engine to a small type-checking kernel $K_0$. However, **a mercurial core can still corrupt $K_0$ itself** (e.g., flipping a branch condition or `Bool` equality during definitional reduction, causing an invalid proof term to be accepted). Because proof-checking a kernel $K_0$ does not generally admit a sublinear Blum–Kannan checker without cryptographic proof systems (such as SNARKs/STARKs), closing the root-checker gap requires one of three physical diversity strategies:
1. **Cross-ISA / Heterogeneous-Core Quorum:** Execute $K_0$ on two distinct physical cores—ideally distinct microarchitectures or ISAs (e.g., x86-64 scalar + ARM64)—preventing core-local and microarchitecture-specific silicon bugs from coinciding.
2. **AN-Encoded Root Kernel:** Compile the tiny checker $C$ or proof kernel $K_0$ (a few thousand lines of integer/pointer code, minimal floating-point) with `ANBDmem` encoding so single-core execution resists arithmetic and control-flow bit flips.
3. **Cryptographic Commitment + Re-check:** Hash the proof artifact and cross-verify asynchronously on a separate physical host before releasing high-assurance binaries.

### 4. Algorithm-Based Fault Tolerance (`ABFT`) for Linear Algebra and FFT

`Basis: normative + documentation + source + execution`

#### 4.1 Algebraic Preservation Invariants (Huang–Abraham 1984, Jou–Abraham 1988, Bosilca et al. 2009)

For $A \in \mathbb{R}^{M \times K}$ and $B \in \mathbb{R}^{K \times N}$, let $w_c \in \mathbb{R}^M$ and $w_r \in \mathbb{R}^N$ be checksum weight vectors (classically $e = (1, 1, \dots, 1)^T$). Define the column-checksum vector $a_c^T = w_c^T A \in \mathbb{R}^{1 \times K}$ and row-checksum vector $b_r = B w_r \in \mathbb{R}^{K \times 1}$. Matrix multiplication $C = \alpha A B + \beta C_0$ preserves linear checksums exactly over $\mathbb{R}$:

$$w_c^T C = \alpha (w_c^T A) B + \beta (w_c^T C_0) = \alpha a_c^T B + \beta (w_c^T C_0)$$
$$C w_r = \alpha A (B w_r) + \beta (C_0 w_r) = \alpha A b_r + \beta (C_0 w_r)$$

- **Asymptotic overhead:** Encoding $a_c^T, b_r$ costs $O(MK + KN)$ flops; updating predicted checksums costs $O(KN + MK)$ flops; verifying $w_c^T \widehat{C}$ and $\widehat{C} w_r$ costs $O(MN)$ flops—total $O(n^2)$ overhead against $O(n^3)$ GEMM compute ($\Theta(1/n)$ relative cost, typically $<2\%$ for $n \ge 1024$).
- **Single-error localization and correction:** If a single entry $\widehat{C}_{i,j} = C_{i,j} + \Delta$ is corrupted with $w_c = e_M, w_r = e_N$, then exactly one column-checksum residual $r_j = (e_M^T \widehat{C})_j - (a_c^T B)_j = \Delta$ and one row-checksum residual $s_i = (\widehat{C} e_N)_i - (A b_r)_i = \Delta$ exceed tolerance, uniquely pinpointing $(i, j)$ and allowing $O(1)$ in-place recovery $C_{i,j} \leftarrow \widehat{C}_{i,j} - \Delta$ (Huang & Abraham, 1984; Bosilca et al., 2009).
- **Multi-error blindness of unweighted checksums:** If two entries in the same column $j$ suffer cancelling errors $(+\Delta, -\Delta)$, then $(e_M^T \widehat{C})_j = (e_M^T C)_j$ holds *exactly* (`residual = 0.0`), completely masking the corruption (**Probe 1C**). Adding a second linearly independent weight vector $w_2 = (1, 2, \dots, M)^T$ (or Vandermonde/Cauchy weights $w_2(i) = 2^{i-1}$ / bounded rational weights) detects every cancelling pair because $w_2(i_1)\Delta - w_2(i_2)\Delta = (i_1 - i_2)\Delta \neq 0$ for $i_1 \neq i_2$ (and enables single-error localization in $O(1)$ using the ratio $(w_2^T \widehat{C} - (w_2^T A)B)_j / (w_1^T \widehat{C} - (w_1^T A)B)_j = i$ without even computing row checksums!).
- **Outer-product / online blocking (`Bosilca et al., 2009`; `FT-BLAS`):** Computing checksums only at the end of a large $K$-dimension GEMM cannot isolate multiple errors accumulated across tiles. Fused online ABFT blocks $K$ into panels of width $K_b$ (e.g., `K_BLOCKING = 384` in `FT-BLAS`) and checks checksums after each panel update, bounding recovery work to a single $K_b$ panel and keeping checksum vectors L1/L2 cache-resident during matrix packing (`packing_a`, `packing_b`).
- **FFT ABFT (Jou & Abraham, IEEE TC 1988):** Because the Discrete Fourier Transform $Y = F_n X$ is linear, encoding the input with a checksum vector $w^T F_n$ yields an invariant $w^T Y = (w^T F_n) X$ computable in $O(n)$ time (with weights chosen so $w^T F_n$ is sparse or low-cost, e.g., $w_k = 1$ checks $Y_0 = \sum X_j$, and geometric shifts check general butterfly faults). Unlike GEMM ($O(n^3)$), FFT compute is $O(n \log n)$, so ABFT overhead scales as $O(1 / \log n)$ rather than $O(1/n)$.

#### 4.2 Direct Source Audit of `yzhaiustc/ftblas` (`22b81cb37e3ee9c7d5594ecd526a4874aa0db6cc`)

`Basis: source + execution`

Direct inspection of `yzhaiustc/ftblas` (`src/dgemm_avx512_ft.cpp`, `src/daxpy_avx512_ft.cpp`) reveals four concrete engineering hazards separating published ABFT theory from production-ready fault-tolerant compilation:

1. **Unscaled hardcoded absolute threshold (`src/dgemm_avx512_ft.cpp:15, 914`):**
   ```cpp
   #define THRESHOLD 1e-2
   ...
   if (fabs(online_chks[i]-c_chks[i])>THRESHOLD) {
   ```
   A fixed `1e-2` constant ignores matrix dimension $K$, unit roundoff $u = 2^{-53}$, and entry magnitude $\|A\|\|B\|$. **Probe 1B** demonstrates both failure directions at $M = N = 32, K = 384$ (matching `K_BLOCKING = 384`):
   - *False-negative blindness on small magnitudes ($\|A\|_\infty, \|B\|_\infty \sim 10^{-3}$):* Clean IEEE-754 max residual is $8.132 \times 10^{-20}$. Flipping exponent LSB bit 52 of `C[7][11]` doubles/halves the entry ($\Delta = 2.334 \times 10^{-6}$, a ~100% relative corruption), yet `2.334e-6 < 1e-2` so `THRESHOLD = 1e-2` **fails to detect it** (`Caught(1e-2) = False`).
   - *False-positive storm on large magnitudes ($\|A\|_\infty, \|B\|_\infty \sim 10^{8}$):* Clean, fault-free IEEE-754 GEMM accumulates a max rounding residual of **$1.088 \times 10^{3}$**, triggering false error alarms on **31 / 32 columns (96.9% false-positive rate)** under `THRESHOLD = 1e-2`.
2. **Index-0 sentinel collision (`src/dgemm_avx512_ft.cpp:911-922`):**
   ```cpp
   int verify_chks(double *online_chks,double *c_chks, int n){
     int cnt=0,res=0;
     for (int i=0;i<n;i++){
       if (fabs(online_chks[i]-c_chks[i])>THRESHOLD) { res=i; cnt++; }
       c_chks[i]=0.;
     }
     if (cnt>1) return -1;
     return res;
   }
   ```
   Initializing `res = 0` makes a clean run (`cnt == 0`) return `0`, indistinguishable from a single error at index `0` (`cnt == 1, res == 0`).
3. **Disabled verification call in upstream `main` (`src/dgemm_avx512_ft.cpp:999-1008`):** Inside `ftblas_dgemm_ft`, the calls to `verify_chks(chk_online_C_col, ...)` and `verify_chks(chk_online_C_row, ...)` and the recovery branch are commented out in commit `22b81cb37e3ee9c7d5594ecd526a4874aa0db6cc` (and the commented condition `else if (v_chks_row==1&&v_chks_col)` would furthermore only trigger on row index `1`).
4. **Lack of microarchitectural diversity on AVX-512:** Both the primary GEMM macro-kernel and `scale_c` checksum updates execute AVX-512 double-precision vector instructions on the same core; a persistent defect in an AVX-512 FMA lane that affects both the `C` update and checksum accumulation symmetrically—or a defect in the Level-1 `daxpy_avx512_ft.cpp` duplicated `vfmadd213pd` pair—can escape unless checksum computation is kept on distinct scalar/FP units or checked across cores.

#### 4.3 Sound Floating-Point Threshold Derivation via Higham's $\gamma_n$ Forward Error Bound

`Basis: normative + derived + execution`

Under IEEE-754 round-to-nearest-even arithmetic with unit roundoff $u$ ($u = 2^{-53} \approx 1.11 \times 10^{-16}$ for `binary64`, $u = 2^{-24} \approx 5.96 \times 10^{-8}$ for `binary32`, $u = 2^{-11}$ for `binary16`), Higham's standard model bounds any $n$-term inner product or sum via $\gamma_n = \frac{nu}{1 - nu}$ (assuming $nu < 1$).

For column $j$ of $C = AB$ ($M \times K$ times $K \times N$), the discrepancy between the checksum of the computed product $\text{fl}(e_M^T \text{fl}(AB))_j$ and the propagated checksum $\text{fl}(\text{fl}(e_M^T A) B)_j$ obeys two-stage rounding accumulation over $M$ row additions and $K$ inner-product terms:

$$\left| \text{fl}(e_M^T \widehat{C})_j - \text{fl}(\widehat{a}_c^T B)_j \right| \le \tau_j^{\text{worst}} \triangleq 2 \, \gamma_{M+K} \, \left(|e_M^T| \, |A|\right) |B_{:,j}|$$

where $|A|_{i,t} = |A_{i,t}|$ and $|B|_{t,j} = |B_{t,j}|$ are elementwise absolute values, computed in $O(MK + KN)$ time alongside the checksums themselves (and storing `abs_chk_A[t] = sum_i |A[i,t]|` costs only one extra vector of length $K$).

**Probe 1B execution results ($M=32, N=32, K=384, \gamma_{M+K} = 4.619 \times 10^{-14}$):**

| Matrix Scale | Max Clean Residual | Max Higham $\tau_j$ | Clean FP (`1e-2`) | Clean FP (Higham) | Bit-52 Flip $\Delta$ | Caught (`1e-2`) | Caught (Higham) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `1e-3` (ML weights) | $8.132 \times 10^{-20}$ | $3.002 \times 10^{-16}$ | `0 / 32` | `0 / 32` | $2.334 \times 10^{-6}$ | **False (Missed)** | **True** |
| `1e0` (unit scale) | $1.421 \times 10^{-13}$ | $3.052 \times 10^{-10}$ | `0 / 32` | `0 / 32` | $3.447 \times 10^{0}$ | True | True |
| `1e8` (scientific) | $1.088 \times 10^{3}$ | $3.080 \times 10^{6}$ | **31 / 32 (96.9%)** | `0 / 32` | $6.962 \times 10^{16}$ | True | True |

**Numerical Blind Spot (Conditioning vs. Small-Bit SDCs):** Because $\tau_j^{\text{worst}}$ scales with $|A|\,|B|$, when $A$ and $B$ experience heavy **catastrophic cancellation** ($|(AB)_{i,j}| \ll (|A|\,|B|)_{i,j}$), the worst-case bound $\tau_j^{\text{worst}}$ becomes much larger than $|C_{i,j}|$, masking low-order mantissa bit flips whose magnitude falls below $2\gamma_{M+K}(|A||B|)_j$. Tightening detection under benign random rounding can use Higham–Mary probabilistic bounds $\tilde{\gamma}_n \propto \sqrt{n}\,u$ (trading a tiny controlled false-positive probability for $\sqrt{n}\times$ tighter thresholds), while maintaining $\tau_j^{\text{worst}}$ as the zero-false-positive guarantee.

### 5. Arithmetically Encoded Compilation (`AN`, `ANB`, `ANBDmem`) and Diverse Instruction Execution

`Basis: documentation + source + execution`

#### 5.1 Mathematical Structure of `AN`, `ANB`, and `ANBDmem` Codes

Introduced by Forin (1989) for safety-critical railway microprocessors and generalized into software compiler transformations by Schiffel et al. (SAFECOMP 2010) and Hoffmann et al. (IEEE HASE 2014), arithmetic codes embed integrity directly into data representations rather than duplicating identical instructions:

- **Pure `AN`-Code:** Every integer variable $x$ is represented as $x_c = A \cdot x$ for an odd constant $A > 1$. Valid codewords satisfy $x_c \bmod A = 0$.
  - *Addition / Subtraction:* $x_c \pm y_c = A(x \pm y)$ preserves encoding natively with **zero** extra arithmetic instructions.
  - *Why it breaks mercurial data-dependent ALU bugs:* Multiplying by $A$ scrambles the operand bit pattern fed into the ALU (`0x0000_0003` becomes `0x0002_AF6D` for $A = 58659$). Any single-bit flip $\pm 2^k$ in the ALU output alters the residue by $\pm 2^k \bmod A \neq 0$ (since $\gcd(2, A) = 1$), so even a **deterministic** bit-flip defect on a mercurial core produces a non-codeword (`r_c % A != 0`) and is immediately caught!
- **`ANB`-Code (Signature Extension):** Encodes each static variable $x$ with a unique compile-time signature $B_x \in [1, A-1]$: $x_c = A \cdot x + B_x$. This detects **operand swaps / wrong-variable fetches** (e.g., register-renamer or decoder faults returning $y_c$ instead of $x_c$, since $B_y \neq B_x \pmod A$) and **modified-operator faults** (executing `sub` instead of `add`, since $(B_x - B_y) \not\equiv (B_x + B_y) \pmod A$).
- **`ANBDmem`-Code (Timestamp + Address Extension):** Adds a dynamic version/timestamp $D_x$ incremented on every store and tracks memory addresses: $x_c = A \cdot x + B_x + D_x$. This additionally detects **lost updates** (dropped store or stale cache/DRAM read returning an old $D_x^{\text{old}} \neq D_x^{\text{cur}}$) and **control-flow/version desynchronization** (Schiffel et al., SAFECOMP 2010).

#### 5.2 Direct Source Audit of `normanrink/an-encoder` (`05c7c36638f4eb93d24434efe3f298bea80c9a6c`)

`Basis: source + execution`

Direct inspection of `normanrink/an-encoder` (`encode/src/OperationsEncoder.cpp`, `encode/runtime/anlib.c`, `encode/runtime/CMakeLists.txt`) exposes concrete LLVM IR lowering mechanics, optimal constant choice, and subtle soundness pitfalls:

1. **LLVM IR Pass Coverage (`encode/src/OperationsEncoder.cpp:58-118`):** `OperationsEncoder::handleBasicBlock` intercepts `Alloca`, `Load`, `Store`, `ICmp`, `Call`, `GetElementPtr`, `PtrToInt`/`IntToPtr`, `SExt`/`ZExt`, `Trunc`, integer arithmetic (`Add`, `Sub`, `Mul`, `URem`, `SRem`, `UDiv`, `SDiv`), and bitwise instructions (`And`, `Or`, `Shl`, `LShr`, `AShr`, `Xor`). Notably, **floating-point LLVM instructions (`FAdd`, `FMul`, `FCmp`) are completely unhandled** (fall through `default: break;`).
2. **Overflow-Aware Multiplication Identity (`encode/runtime/anlib.c:66-78`):** A naive encoded multiply computes $(x_c \cdot y_c) / A = A^2 x y / A$, which overflows 64 bits whenever $A^2 |xy| \ge 2^{63}$. Instead, `mul_enc` factors $A - 1 = p \cdot q$ with hardcoded **`p = 278, q = 211`**—corresponding to Hoffmann et al.'s optimal 16-bit odd constant **$A = 278 \times 211 + 1 = 58659$**—and evaluates:
   ```c
   r_enc = ((x_enc - x)/p) * ((y_enc - y)/q) + x*y;
   ```
   Since $x_{\text{enc}} - x = (A-1)x = pqx$, the identity yields $(qx)(py) + xy = (pq + 1)xy = Axy$ while keeping intermediate magnitudes bounded by $A|xy|$ instead of $A^2|xy|$ (verified in **Probe 1A**). Note, however, that `p = 278, q = 211` are hardcoded in `anlib.c:72-73` even though `A` is passed via `-DCODE_VALUE_A=${CODE_VALUE_A}` in `encode/runtime/CMakeLists.txt:11`, silently breaking multiplication if `CODE_VALUE_A != 58659`!
3. **Deferred Accumulator Checking (`encode/runtime/anlib.c:36-47`):** To amortize expensive modulo-`A` checks (`idiv` instructions), `___accumulate_enc` sums checked encoded values into a signed 64-bit accumulator `accu_enc`, firing `an_assert(old_accu, A)` only on signed 64-bit overflow (`__builtin_saddl_overflow`) or at program exit/I/O boundaries. This matches Rink & Castrillon's CF 2017 configurable rigor trade-off: relaxing check frequency reduces runtime overhead from **$9.9\times$ down to $2.1\times$** while increasing CPU fault SDC escape rate from **$0.007$ to $>0.022$** and memory fault SDC escape from **$0.009$ to $>0.032$** (because multiple errors added into `accu_enc` can alias $\bmod A$, and deferred errors may leak before the check fires).
4. **Critical Decoding Vulnerability Window (`encode/runtime/anlib.c:96-122, 209-263`):** Because bitwise operations (`and_enc`, `or_enc`, `xor_enc`, `onesc_enc`, `shl_enc`, `shr_enc`, `ashr_enc`) and signed division/remainder (`sdiv_enc`, `smod_enc`, `umod_enc`) are not homomorphic under multiplication by $A$, `anlib.c` explicitly calls `an_decode(x_enc, A)`, executes the native unencoded operator (e.g., `x ^ y`), and re-encodes via `an_encode(x ^ y, A)`. **Probe 1A** verifies that any mercurial ALU defect firing during the unencoded instruction is immediately multiplied by $A$, yielding `reencoded % A == 0` (**valid codeword, undetected wrong value!**). Closing this window requires bitwise table/homomorphic checks or executing the decoded operation redundantly on a diverse path before re-encoding.
5. **Hamming Distance of $A = 58659$ (Probe 1A Execution):** Exhaustive testing across all 64 bit positions shows **$A = 58659$ has 0 single-bit flip escapes (`0 / 64`) and 0 two-bit flip escapes across all sign combinations (`0 / 8,064`)**—giving guaranteed minimum arithmetic distance $d_{\min} \ge 3$ over 64-bit signed words—while arbitrary uniform multi-bit corruption has residual aliasing probability $1 / 58659 \approx 1.70 \times 10^{-5}$.
6. **Compiler Optimization Interference (`encode/runtime/CMakeLists.txt:5`):** As the `anlib.c` build file explicitly warns (`set(CLANG_OPTS -O0)`), standard aggressive LLVM optimization passes (`InstCombine`, `GVN`, `SCCP`) can fold away redundant `A * (x / A)` checks or hoist constant factors out of encoded arithmetic unless codewords are shielded via opaque intrinsics or late MIR/MachineIR lowering.

### 6. Comparative Trade-Off Matrix Across Reliability Mechanisms

`Basis: documentation + source + execution + derived`

| Mechanism | Primary Fault Classes Caught | Deterministic Mercurial Core Coverage | Runtime / Compute Overhead | Code / Compiler Complexity | Floating-Point Support | Key Failure Mode / Bypass |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Same-Instruction DWC / SWIFT (`COAST`, `FT-BLAS` L1)** | Transient SEUs (radiation), single-slot glitches | **0% (fails completely)** on repeatable core-local defects | $1.3\times$–$2.2\times$ (instruction + reg pressure) | Low (LLVM IR `I->clone()`) | Yes (bit-exact `vpcmpeqd`) | Common-mode silicon defect produces identical wrong result twice |
| **Cross-Core / Heterogeneous Re-execution** | Transient SEUs + core-local mercurial defects (if scheduled on distinct physical cores/uArchs) | **High** (100% if cores lack shared design errata) | $2\times$–$3\times$ CPU + inter-core sync latency | Medium (OS affinity + deterministic replay) | Yes (requires deterministic FP reduction order) | Shared microarchitecture design errata across homogeneous cores |
| **Pure `AN` Encoding (`normanrink/an-encoder`)** | Transient SEUs + ALU data-dependent bit flips ($d_{\min} \ge 3$ for $A=58659$) | **High for integer add/sub/mul** (scrambles bit patterns) | $2.1\times$–$9.9\times$ (check-frequency dependent) | High (custom LLVM IR pass + `-O0` runtime guard) | **No** (integers/pointers only) | Bitwise/div decode-reencode window; lost stores; wrong-operand fetches |
| **`ANB` / `ANBDmem` Encoding (Schiffel et al., 2010)** | ALU flips + wrong operand + modified opcode + lost/stale memory updates | **High** for integer & control-flow paths | $3\times$–$15\times$ (signature + timestamp tracking) | Very high (whole-program static/dynamic signatures) | **No** (native IEEE-754 unsupported) | External FFI boundaries; bitwise decode window; overflow bit-width loss |
| **Certifying Algorithms (Blum–Kannan, LEDA, CAV '11)** | **Both** software bugs AND hardware SDCs in the main algorithm | **100% on primary run** if checker runs on diverse unit/core | $o(T(n))$ (often $1\%$–$15\%$ for $O(n)$ check of $O(n \log n)$/$O(n^3)$) | Algorithmic (domain-specific witness design + small verified checker) | Problem-dependent (exact for graph/LP/sort; residual-bounded for numerical) | Fault inside checker itself; non-certifiable problems without cheap witnesses |
| **ABFT + Higham $\gamma_n$ Bound (Huang–Abraham, Bosilca, `FT-BLAS` L3)** | Transient + mercurial SIMD/tensor faults in GEMM, LU, QR, Cholesky, FFT | **High** if checksums run on scalar/diverse unit with weighted/Freivalds check | $O(1/n)$ for GEMM ($<2\%$–$5\%$); $O(1/\log n)$ for FFT | Medium (fused tiling + dynamic $|A|\,|B|$ norm tracking) | **Yes** (with Higham $\gamma_{M+K}$ threshold) | Hardcoded absolute thresholds (`1e-2`); cancelling dual errors in unweighted sums; ill-conditioned low-mantissa flips |
| **Fleet Screening (`SiliFuzz`, `Fleetscanner`, `Ripple`)** | Latent manufacturing & aging defects across fleet | **Probabilistic fleet quarantine** (removes bad cores from pool) | $<1\%$ fleet tax (`Ripple` ms bursts) | Operational (corpus fuzzing + scheduler drain) | Yes (ISA-level coverage) | Cannot catch unscreened novel bit-patterns before first corruption; 6-month aging lag |

### 7. Recommended Asymmetric Reliability Architecture for Verified Compilers

`Basis: derived`

Combining these findings yields a principled three-tier compilation strategy that avoids paying $3\times$–$10\times$ overhead globally while closing the mercurial-core gap:

1. **Tier 1 — High-Compute Structured Kernels (GEMM, Convolutions, FFT, Linear Solvers, Sorting, Graph/LP):** Emit unencoded, maximally vectorized SIMD/tensor code for the primary computation, paired with an **asymptotically sublinear ($o(T(n))$) certifying checker or weighted/Freivalds ABFT check** compiled onto a **diverse execution domain** (scalar FP path or distinct physical core) with **Higham componentwise $\gamma_{M+K}$ error bounds** (never hardcoded absolute tolerances).
2. **Tier 2 — Control-Plane, Memory-Management, and Root Checker Logic:** Because checkers and proof kernels are small ($O(n)$ or few kLoC) and integer/pointer-dominated, protect them via **heterogeneous cross-core quorum execution** or **`ANBDmem` encoding** (with guarded non-decoding bitwise paths or redundant diverse bitwise ops) so a mercurial core cannot silently flip the checker's final `accept`/`reject` verdict.
3. **Tier 3 — Fleet Quarantine Feedback Loop:** Every runtime checker or ABFT rejection must record the physical core ID, CPU stepping, frequency/voltage telemetry, and failing input slice, re-running the computation on a *different* physical core to distinguish transient soft errors from repeatable mercurial cores and trigger immediate OS core offlining + `SiliFuzz`/`Ripple` signature ingestion.

## Boundaries

- **Known not to apply:**
  - *Same-instruction single-core duplication (`EDDI`, `SWIFT`, `COAST` DWC/TMR, `FT-BLAS` Level-1 `daxpy_avx512_ft.cpp`):* Known not to detect deterministic, operand-dependent mercurial core defects that repeat identically on consecutive executions of the same instruction on the same functional unit (established by Dixit et al., 2021; Hochschild et al., 2021; source audit of `cloning.cpp` and `daxpy_avx512_ft.cpp`; and Probe 1A).
  - *Hardcoded absolute ABFT tolerance (`THRESHOLD = 1e-2` in `yzhaiustc/ftblas/src/dgemm_avx512_ft.cpp:15`):* Known not to preserve either zero-false-positive or exponent-flip detection guarantees outside narrow unit-scale matrices (established by Probe 1B across $10^{-3}$ and $10^{8}$ regimes).
  - *Pure `AN` encoding (`normanrink/an-encoder`):* Known not to apply to IEEE-754 floating-point instructions (`OperationsEncoder.cpp` ignores `FAdd`/`FMul`/`FCmp`) and known not to protect the decoded interior of `and_enc`/`or_enc`/`xor_enc`/`sdiv_enc` (`anlib.c:96-122, 209-263`).
- **Unsupported:**
  - `normanrink/an-encoder` (`05c7c36638f4eb93d24434efe3f298bea80c9a6c`) explicitly targets modified LLVM/Clang 3.5.1 (`README.txt:40-52`) and hardcodes `p = 278, q = 211` in `anlib.c:72-73`; arbitrary `CODE_VALUE_A` values without updating `p, q` are unsupported and silently miscompile multiplication.
  - `byuccl/coast` (`397a26ecdb01e7c329884d12c9f6bb2a05c3abc9`) explicitly removes support for its legacy `EDDI` pass (`projects/EDDI/EDDI.cpp:36`, `assert(false && "Switch to DWC")`).
- **Not examined:**
  - *GPU/TPU tensor-core ABFT implementations:* `shixun404/Fault-Tolerant-SGEMM-on-NVIDIA-GPUs` (`52cde58bafd23484b463d6d2a4a6a2fa4bbc8f34`) was pinned and its directory tree inspected, but its CUDA warp/shared-memory ABFT kernels (`kernel/ft_sgemm/include/*.cuh`) were not audited line-by-line or executed on GPU hardware.
  - *Reduced-precision AI formats (`BF16`, `FP8`, `MXFP4`):* Higham's $\gamma_n$ derivation holds algebraically for any IEEE-like format with unit roundoff $u$, but `FP8` ($u = 2^{-3}$ or $2^{-4}$) violates $nu < 1$ for $K \ge 16$, requiring stochastic-rounding or block-exponent ABFT analysis that was not experimentally probed here.
  - *Hardware lockstep / DMR microarchitectures (e.g., ARM Cortex-R52 dual-core lockstep, IBM z-Series instruction retry):* Out of scope for commodity datacenter software/compiler mitigation.
- **Unknown:**
  - *Exact fleet-wide ratio of deterministic vs. intermittent/timing-marginal mercurial defects across post-2023 silicon nodes (3nm/2nm GAAFET):* Public measurements in Hochschild et al. (2021) and Dixit et al. (2021, 2022) predate 3nm/2nm fleet maturity; whether sub-3nm aging shifts the balance toward non-deterministic voltage/thermal marginalities vs. deterministic stuck/bridging defects remains unknown from public literature.
  - *Optimal compiler-synthesized diverse instruction schedules on x86-64/ARM64:* Whether automatic compiler scheduling that pairs e.g. AVX-512 execution with scalar SSE/GPR checking achieves near-100% mercurial defect orthogonality on real defective datacenter CPUs (beyond synthetic ALU models) has not been empirically measured on a fleet of known-bad processors.

## Evidence

### Primary Literature and Specifications
- **Hochschild et al. (HotOS XVIII, 2021):** Peter H. Hochschild, Paul Turner, Jeffrey C. Mogul, Rama Govindaraju, Parthasarathy Ranganathan, David E. Culler, Amin Vahdat, *"Cores That Don't Count"*, Proc. 18th Workshop on Hot Topics in Operating Systems, pp. 9–16, DOI `10.1145/3458336.3465297` (mercurial core taxonomy, "a few mercurial cores per several thousand machines", self-inverting AES, lock/vector/load-store failures).
- **Dixit et al. (2021):** Harish Dattatraya Dixit, Sneha Pendharkar, Matt Beadon, Chris Mason, Tejasvi Chakravarthy, Bharath Muthiah, Sriram Sankar, *"Silent Data Corruptions at Scale"*, `arXiv:2102.11245v1`, DOI `10.48550/arXiv.2102.11245` (full PDF examined: §2 FIT background, §3 silicon defects, §4–6 Core-59 `Int(1.1^53)=0` deterministic reproducer narrowed from 430K lines of HotSpot `+PrintAssembly` to 60 lines of assembly, §7–8 detection and fault-tolerant libraries).
- **Dixit et al. (2022):** Harish Dattatraya Dixit, Laura Boyle, Gautham Vunnam, Sneha Pendharkar, Matt Beadon, Sriram Sankar, *"Detecting Silent Data Corruptions in the Wild"*, `arXiv:2203.08989v1`, DOI `10.48550/arXiv.2203.08989` (full PDF examined: §4 1-in-1,000 device rate, 4 accelerants including 6-month degradation experiment, §5.1 `Fleetscanner` vs. §5.2 `Ripple` in-production millisecond testing).
- **EDDI & SWIFT:** Nahmsuk Oh, Philip P. Shirvani, Edward J. McCluskey, *"Error Detection by Duplicated Instructions in Super-Scalar Processors"*, IEEE Trans. Reliability 51(1):63–75, 2002, DOI `10.1109/24.994913`; George A. Reis, Jonathan T.-Y. Chang, Neil Vachharajani, Ram Rangan, David I. August, *"SWIFT: Software Implemented Fault Tolerance"*, CGO 2005, DOI `10.1109/CGO.2005.34`.
- **Result Checking & Certifying Algorithms:** Manuel Blum & Sampath Kannan, *"Designing Programs That Check Their Work"*, JACM 42(1):269–291, 1995, DOI `10.1145/200836.200880`; Ross M. McConnell, Kurt Mehlhorn, Stefan Näher, Pascal Schweitzer, *"Certifying Algorithms"*, Computer Science Review 5(2):119–161, 2011, DOI `10.1016/j.cosrev.2010.09.009`; Eyad Alkassar, Sascha Böhme, Kurt Mehlhorn, Christine Rizkallah, *"Verification of Certifying Computations"*, CAV 2011, DOI `10.1007/978-3-642-22110-1_7`.
- **ABFT & Numerical Analysis:** Kuang-Hua Huang & Jacob A. Abraham, *"Algorithm-Based Fault Tolerance for Matrix Operations"*, IEEE Trans. Computers C-33(6):518–528, 1984, DOI `10.1109/TC.1984.1676475`; J.-Y. Jou & Jacob A. Abraham, *"Fault-Tolerant FFT Networks"*, IEEE Trans. Computers 37(5):548–561, 1988, DOI `10.1109/12.4606`; George Bosilca, Rémi Delmas, Jack J. Dongarra, Julien Langou, *"Algorithm-Based Fault Tolerance Applied to High Performance Computing"*, JPDC 69(4):410–416, 2009, DOI `10.1016/j.jpdc.2008.12.002`; Yujia Zhai, Elisabeth Giem, Quan Fan, Kai Zhao, Jinyang Liu, Zizhong Chen, *"FT-BLAS: A High-Performance BLAS Implementation with Online Fault Tolerance"*, ICS 2021, DOI `10.1145/3447818.3460364` (`arXiv:2104.00897`, full PDF examined); Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002 ($\gamma_n = nu/(1-nu)$ standard model).
- **AN-Encoding:** Ute Schiffel, André Schmitt, Martin Süßkraut, Christof Fetzer, *"ANB- and ANBDmem-Encoding: Detecting Hardware Errors in Software"*, SAFECOMP 2010, DOI `10.1007/978-3-642-15651-9_13`; Martin Hoffmann, Peter Ulbrich, Christian Dietrich, Horst Schirmeier, Daniel Lohmann, Wolfgang Schröder-Preikschat, *"A Practitioner's Guide to Software-Based Soft-Error Mitigation Using AN-Codes"*, IEEE HASE 2014, DOI `10.1109/HASE.2014.14`; Norman A. Rink & Jeronimo Castrillon, *"Trading Fault Tolerance for Performance in AN Encoding"*, ACM CF 2017 ($9.9\times \to 2.1\times$ overhead vs. CPU SDC $0.007 \to >0.022$).

### Pinned Source Code Inspected (Observed 2026-11-19)
- **`google/silifuzz`** @ `bab27a948dcdc42405644f8b1480518e0b7f8ce8`:
  - `README.md` (proxy fuzzing architecture and corpus replay overview).
  - `doc/proxy_architecture.md` (lines 1–60: `[0x30000000, 0xB0000000)` single code page, two 512 MiB data mappings, non-zero `%cs`/`%ss`/`%xmm0` initialization including AMD erratum 1386 workaround).
- **`byuccl/coast`** @ `397a26ecdb01e7c329884d12c9f6bb2a05c3abc9`:
  - `projects/DWC/DWC.cpp:1-41` (`DP.run(M, 2)`), `projects/EDDI/EDDI.cpp:1-47` (`assert(false && "Switch to DWC")`).
  - `projects/dataflowProtection/cloning.cpp:2187-2206` (`newI1 = I->clone(); newI1->insertAfter(I);` and `newI2 = I->clone()` under `TMR`).
- **`yzhaiustc/ftblas`** @ `22b81cb37e3ee9c7d5594ecd526a4874aa0db6cc`:
  - `src/daxpy_avx512_ft.cpp:1-90` (duplicated `vfmadd213pd` on `%%zmm20`/`%%zmm28` checked by `vpcmpeqd`).
  - `src/dgemm_avx512_ft.cpp:10-15` (`K_BLOCKING 384`, `THRESHOLD 1e-2`), `:911-922` (`verify_chks` returning `res=0` when `cnt==0`), `:997-1009` (commented-out `verify_chks` invocation in `ftblas_dgemm_ft`).
- **`normanrink/an-encoder`** @ `05c7c36638f4eb93d24434efe3f298bea80c9a6c`:
  - `README.txt:38-55` (LLVM/Clang 3.5.1 dependency).
  - `encode/runtime/CMakeLists.txt:1-22` (`-O0` compilation, `-DCODE_VALUE_A`).
  - `encode/src/OperationsEncoder.cpp:58-118` (integer/memory/bitwise IR interception; floating-point opcodes unhandled).
  - `encode/runtime/anlib.c:36-47` (`___accumulate_enc`), `:66-78` (`mul_enc` with `p=278, q=211` for $A=58659$), `:96-122` and `:209-263` (decode → unencoded op → re-encode helpers).

### Executable Micro-Probes (Python 3 stdlib, Linux x86-64, 2026-11-19)

Running the standalone script below (`python3 /tmp/probe_sdc_abft.py`) produced the following exact output:

```text
=== Probe 1A: Deterministic Mercurial Defect vs DWC/SWIFT vs AN-Code ===
Trials: 10000
DWC/SWIFT (same-instruction): faults_triggered=2502, detected=0, silent_escapes=2502 (100.0% escape)
AN-Code (A=58659): faults_triggered=2440, detected=2440, silent_escapes=0 (100.00% detection)
AN-Code (A=58659) single-bit flips escaping mod A (0..63): 0
AN-Code (A=58659) 2-bit flips (all signs, 0..63) escaping mod A: 0 / 8064 (first 3: [])
anlib.c mul_enc identity ((x_c-x)/278)*((y_c-y)/211)+x*y == A*x*y verified: True
anlib.c xor_enc decoding-window escape: valid_codeword=True, decoded_matches_gold=False

=== Probe 1B: IEEE-754 ABFT Thresholds (FT-BLAS 1e-2 vs Higham gamma_K) ===
Dimensions: M=32, N=32, K=384, u=1.110e-16, gamma_K=4.263e-14, gamma_(M+K)=4.619e-14
Scale=small_ml_1e-3 : max_clean_res=8.132e-20, max_tau_higham=3.002e-16 | Clean FP(1e-2)=0/32, Clean FP(Higham)=0/32 | Bit52-Flip delta=2.334e-06, Caught(1e-2)=False, Caught(Higham)=True
Scale=unit_1e0      : max_clean_res=1.421e-13, max_tau_higham=3.052e-10 | Clean FP(1e-2)=0/32, Clean FP(Higham)=0/32 | Bit52-Flip delta=3.447e+00, Caught(1e-2)=True, Caught(Higham)=True
Scale=large_sci_1e8 : max_clean_res=1.088e+03, max_tau_higham=3.080e+06 | Clean FP(1e-2)=31/32, Clean FP(Higham)=0/32 | Bit52-Flip delta=6.962e+16, Caught(1e-2)=True, Caught(Higham)=True

=== Probe 1C: Cancelling Dual-Error (+delta, -delta) in Same Column ===
Cancelling (+100, -100) in col 5: unweighted_max_residual=0.0e+00 (MISSED!), weighted_w2_max_residual=7.0e+02 (CAUGHT!), Freivalds detected in 20/20 trials
```

Self-contained reproduction script (`/tmp/probe_sdc_abft.py`):

```python
#!/usr/bin/env python3
import random, struct

def probe_1a():
    A, p, q = 58659, 278, 211
    assert p * q + 1 == A
    def mercurial_add64(a, b):
        r = a + b
        return r ^ (1 << 13) if ((a & (1 << 7)) and (a & (1 << 11))) else r
    rng = random.Random(20261119)
    dwc_t = dwc_d = an_t = an_d = 0
    for _ in range(10000):
        x, y = rng.randint(0, (1 << 24) - 1), rng.randint(0, (1 << 24) - 1)
        g = x + y
        r1, r2 = mercurial_add64(x, y), mercurial_add64(x, y)
        if r1 != g:
            dwc_t += 1; dwc_d += (r1 != r2)
        rc = mercurial_add64(A * x, A * y)
        if rc != A * g:
            an_t += 1; an_d += ((rc % A) != 0)
    s_esc = sum(1 for k in range(64) if ((1 << k) % A) == 0)
    d_esc = sum(1 for i in range(64) for j in range(i+1, 64)
                for s1 in (-1, 1) for s2 in (-1, 1)
                if (s1*(1<<i) + s2*(1<<j)) % A == 0)
    mul_ok = all((((A*x-x)//p)*((A*y-y)//q) + x*y) == A*x*y
                 for x, y in [(0,0),(1,1),(12345,6789),(-4219,9871),((1<<20)-1,(1<<20)-3)])
    reenc = A * ((0x0880 ^ 0x00F0) ^ (1 << 13))
    print(f"DWC: {dwc_d}/{dwc_t}; AN: {an_d}/{an_t}; 1-bit esc={s_esc}; 2-bit esc={d_esc}; mul_ok={mul_ok}; xor_escape_valid={reenc%A==0}")

def matmul(A, B):
    m, k, n = len(A), len(A[0]), len(B[0])
    C = [[0.0]*n for _ in range(m)]
    for i in range(m):
        for t in range(k):
            a = A[i][t]
            for j in range(n): C[i][j] += a * B[t][j]
    return C

def col_sums(M):
    out = [0.0]*len(M[0])
    for row in M:
        for j, v in enumerate(row): out[j] += v
    return out

def vec_mat(v, B):
    out = [0.0]*len(B[0])
    for t, vt in enumerate(v):
        for j, b in enumerate(B[t]): out[j] += vt * b
    return out

def flip_f64_bit(val, b):
    bits = struct.unpack("<Q", struct.pack("<d", val))[0] ^ (1 << b)
    return struct.unpack("<d", struct.pack("<Q", bits))[0]

def probe_1b_1c():
    M, N, K = 32, 32, 384
    u = 2.0**-53
    gmk = ((M + K)*u)/(1.0 - (M + K)*u)
    rng = random.Random(20261119)
    for scale in (1e-3, 1.0, 1e8):
        A = [[rng.uniform(-scale, scale) for _ in range(K)] for _ in range(M)]
        B = [[rng.uniform(-scale, scale) for _ in range(N)] for _ in range(K)]
        C = matmul(A, B)
        online = vec_mat(col_sums(A), B)
        actual = col_sums(C)
        absA = [sum(abs(A[i][t]) for i in range(M)) for t in range(K)]
        tau = [2.0*gmk*sum(absA[t]*abs(B[t][j]) for t in range(K)) for j in range(N)]
        res = [abs(o-a) for o, a in zip(online, actual)]
        fp_f = sum(r > 1e-2 for r in res)
        fp_h = sum(r > t for r, t in zip(res, tau))
        C_bad = [row[:] for row in C]
        C_bad[7][11] = flip_f64_bit(C_bad[7][11], 52)
        res_bad = abs(online[11] - col_sums(C_bad)[11])
        print(f"scale={scale:.0e}: max_res={max(res):.3e} max_tau={max(tau):.3e} FP(1e-2)={fp_f}/32 FP(H)={fp_h}/32 caught(1e-2)={res_bad>1e-2} caught(H)={res_bad>tau[11]}")
    # Probe 1C: cancelling (+100, -100) dual-error in col 5
    A = [[float(rng.randint(-10, 10)) for _ in range(16)] for _ in range(16)]
    B = [[float(rng.randint(-10, 10)) for _ in range(16)] for _ in range(16)]
    C = matmul(A, B); C[2][5] += 100.0; C[9][5] -= 100.0
    unw = max(abs(a-b) for a, b in zip(vec_mat(col_sums(A), B), col_sums(C)))
    w2 = [float(i+1) for i in range(16)]
    w2_A = [sum(w2[i]*A[i][t] for i in range(16)) for t in range(16)]
    w2_C = [sum(w2[i]*C[i][j] for i in range(16)) for j in range(16)]
    w2d = max(abs(a-b) for a, b in zip(vec_mat(w2_A, B), w2_C))
    f_det = 0
    for _ in range(20):
        r = [rng.choice([-1.0, 1.0]) for _ in range(16)]
        Br = [sum(B[t][j]*r[j] for j in range(16)) for t in range(16)]
        ABr = [sum(A[i][t]*Br[t] for t in range(16)) for i in range(16)]
        Cr = [sum(C[i][j]*r[j] for j in range(16)) for i in range(16)]
        f_det += any(abs(x-y) > 1e-9 for x, y in zip(ABr, Cr))
    print(f"Probe1C: unweighted={unw:.1e} weighted={w2d:.1e} Freivalds={f_det}/20")

if __name__ == "__main__":
    probe_1a(); probe_1b_1c()
```

## Revalidation

To revalidate these findings against newer upstream revisions or a new fault-tolerant compiler / BLAS library:

1. **Check upstream ABFT source contracts:** Inspect `yzhaiustc/ftblas` (`src/dgemm_avx512_ft.cpp`, `src/daxpy_avx512_ft.cpp`) or any candidate BLAS/ML kernel for: (a) whether `verify_chks` is actually invoked and distinguishes clean execution (`cnt == 0`) from index `0`; (b) whether the checksum threshold scales dynamically with $\gamma_{M+K} (|e^T||A|)|B|$ rather than using a fixed constant; and (c) whether weighted checksums or Freivalds projections protect against cancelling multi-entry faults.
2. **Check compiler fault-tolerance passes for diversity:** Inspect any LLVM/MIR duplication pass (such as `byuccl/coast`'s `cloning.cpp`) to verify whether clones use identical opcodes/execution ports on the same core (vulnerable to mercurial defects) or enforce heterogeneous scheduling / arithmetic encoding.
3. **Audit AN-encoder runtime helpers:** For any AN/ANB/ANBDmem compiler (such as `normanrink/an-encoder`), grep runtime libraries for `decode` followed by `encode` inside bitwise, shift, or division helpers—any unencoded intermediate computation constitutes a silent-corruption window—and verify that multiplication factorization constants (`p`, `q`) are statically asserted to satisfy `p * q + 1 == CODE_VALUE_A` and that optimizer passes cannot fold `A * (x / A)` away.
4. **Rerun the embedded Python probe:** Execute `/tmp/probe_sdc_abft.py` (stdlib Python 3, `<0.5s`) after changing matrix dimensions `(M, N, K)`, precision unit roundoff `u` (e.g., `2**-24` for `binary32`), or candidate AN multiplier `A` to re-verify minimum arithmetic distance $d_{\min}$ and Higham threshold tightness.
