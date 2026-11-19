# RISC-V Zero-Knowledge Virtual Machines: STARK/AIR Continuations, Lookup-Singularity Sumchecks, IVC Folding, and Underconstraint Soundness Bugs

## Summary

Zero-knowledge virtual machines (zkVMs) prove that an unmodified instruction-set binary (predominantly `RV32IM` or `RV64IMAC`) executed from an initial machine state commitment to a final output digest without exposing private witness inputs. Across production systems, instruction-set arithmetization splits into three distinct cryptographic paradigms:

1. **Small-Field Multi-Table STARKs with LogUp Cross-Chip Buses (`risc0/risc0`, `succinctlabs/sp1`, `Plonky3/Plonky3`):** Execution is sharded into fixed-budget segments connected by public pre/post Merkle state continuations (`ReceiptClaim`) or global bus accumulators. Arithmetic runs over 31-bit primes—`BabyBear` ($p = 2^{31} - 2^{27} + 1 = \text{0x78000001}$) or `KoalaBear` ($p = 2^{31} - 2^{24} + 1 = \text{0x7f000001}$)—representing 32-bit or 64-bit ISA words as byte or 16-bit limbs, offloading expensive cryptographic/algebraic primitives to stateful precompile chips (`SHA-256`, `Keccak-256`, `secp256k1`, `BN254`, `uint256`), and enforcing read-write RAM consistency via Blum–Evans–Gemmell–Kannan–Naor offline memory checking lowered into Haböck logarithmic-derivative (`LogUp`) rational sums.
2. **Lookup-Singularity Sumcheck VMs (`a16z/jolt` with `Lasso` and `Twist`/`Shout`):** Rather than writing per-opcode polynomial arithmetic constraints or decomposing words into bits, Jolt evaluates whole 64-bit RISC-V instructions against virtual structured tables of size $2^{128}$ via prefix-suffix multilinear extensions (`PrefixSuffixDecomposition<XLEN>`), read-only `Shout` lookups, one-hot increment (`Inc`) `Twist` read-write memory/register checking, and outer `Spartan` R1CS sumchecks over 254-bit elliptic-curve scalar fields.
3. **Non-Uniform Incrementally Verifiable Computation Folding (`microsoft/Nova`, `SuperNova`):** Instead of proving an entire execution segment via FFT/FRI or global sumcheck, folding schemes maintain running `RelaxedR1CSInstance` accumulators $(A Z) \circ (B Z) = u \cdot (C Z) + E$ over a 2-cycle of elliptic curves, paying per-step circuit cost proportional only to the active instruction (`SuperNova`) plus two group scalar multiplications for the cross-term commitment $\text{comm}_T$.

Soundness across all three paradigms hinges on **functional determinism of witness generation**: every prover-supplied witness column must be *uniquely* determined by the committed instruction stream, prior architectural state, and authenticated host-oracle inputs. Real-world zkVM soundness breaks (`CVE-2025-52484`, `CVE-2025-54873`, `CVE-2026-40323`, `GHSA-5c79-r6x7-3jx9`, `GHSA-8m24-3cfx-9fjw`, `GHSA-p7v2-jjv3-8p8f`, and Jolt `PR #1474`) cluster into five recurring bug classes: (a) underconstrained decode selectors and multi-cycle mode flags, (b) missing 32-bit/64-bit limb carry, borrow, or remainder-sign uniqueness checks, (c) forged offline memory timestamps or same-cycle `rs1 == rs2` read aliasing, (d) unverified host-oracle syscall/hint non-determinism, and (e) Fiat-Shamir transcript / sumcheck claim-splicing omissions.

## Applicability

This report characterizes comparative execution-trace arithmetization, memory-checking invariants, precompile FFI boundaries, and soundness failure modes across twelve pinned upstream artifacts:

- **RISC Zero (`risc0/risc0` at `5e1be36a7fcadf98f341e348d9314e5f1d519046`, workspace `v3.1.0`, `risc0-circuit-rv32im` `v4.1.0`):** `RV32IM` guest execution over `BabyBear` ($\mathbb{F}_p$, degree-4 extension $\mathbb{F}_{p^4} = \mathbb{F}_p[x]/(x^4 + 11)$), Poseidon2 paged memory continuations (`ReceiptClaim`, `CompositeReceipt`), `BytePolynomial` big-integer witness accelerators, and historical vulnerability advisories on `v1.x`–`v2.x` (`GHSA-5c79-r6x7-3jx9`, `GHSA-349p-x622-29x6`, `GHSA-g3qg-6746-3mg9` / `CVE-2025-52484`, `GHSA-f6rc-24x4-ppxp` / `CVE-2025-54873`, `GHSA-jqq4-c7wq-36h7`).
- **Succinct SP1 across two major architectural generations:**
  - **SP1 v5 (`succinctlabs/sp1` at `2a51f3dd370e4c5f74d04dfd89359a13a7e93f99`, `v5.2.4`):** `RV32IM` over Plonky3 univariate two-adic FRI STARKs on `BabyBear` (`sp1-stark`), single-word `(shard, clk)` memory timestamps, and byte-limb ALU chips.
  - **SP1 v6 (`succinctlabs/sp1` at `0cd151a8d7beaaad4ad245c8f37515d6b4f72597`, `v6.10.0`):** `RV64IM` over `sp1-hypercube` multilinear sumcheck + `slop-jagged` / `slop-basefold` / `slop-whir` commitments on `KoalaBear` ($p = 2^{31} - 2^{24} + 1$), two-limb 48-bit `(clk_high, clk_low)` memory timestamps, hardware-like page protection (`InteractionKind::PageProt`), and 16-bit limb `Word<T>` operations, alongside advisories `GHSA-8m24-3cfx-9fjw`, `GHSA-63x8-x938-vx33` (`CVE-2026-40323`), and `GHSA-p7v2-jjv3-8p8f`.
- **Plonky3 (`Plonky3/Plonky3` at `0d803737b681774186cd283b1fd2d8e493655c82`):** Underlying 31-bit Monty field arithmetic (`p3-baby-bear`, `p3-koala-bear`), `AirBuilder` / `PermutationAirBuilder`, and `LogUpGadget` (`p3-lookup`).
- **Jolt (`a16z/jolt` at `943f60ce477cd98f4682a99d82f388468fe20e61`) and its normative papers (`DOI: 10.1007/978-3-031-58751-1_1`, `DOI: 10.1007/978-3-031-58751-1_7`, `ePrint 2025/105`):** `RV64IMAC` (`XLEN = 64`, plus `XLEN = 8` hypercube test instantiation) using `Lasso`/`Shout` structured instruction tables, `Twist` one-hot increment memory/register checking, `Spartan` outer/product `uni-skip` sumchecks, and `Dory`/`HyperKZG` multilinear commitments.
- **Nova and SuperNova (`microsoft/Nova` at `01b1e2d662a847ed7029770ecbaf6687398899dd`, `nova-snark` `v0.76.0`; `DOI: 10.1007/978-3-031-15985-5_13`; `ePrint 2022/1758`):** Curve-cycle (`Pallas`/`Vesta`, `BN254`/`Grumpkin`, `secp`/`secq`) relaxed-R1CS `NIFS` folding, `MicroSpartan` compression, and experimental `NeutronNova` (`--features experimental`) non-uniform folding.
- **0xPARC ZK Bug Tracker (`0xPARC/zk-bug-tracker` at `56a996672fb50486279126c8e12530f2bf933d0b`):** Cross-ecosystem taxonomy of underconstrained, non-deterministic, range-check, and `Frozen Heart` transcript vulnerabilities.

Findings on algebraic soundness conditions (boolean/one-hot selector completeness, limb carry bounds, offline memory timestamp monotonicity, and Fiat-Shamir transcript binding) extend structurally to any zkVM or zkEVM instantiating AIR + LogUp, multilinear sumcheck lookups, or relaxed-R1CS folding, provided field characteristic $p$ and word limb widths are substituted into the range inequalities derived below.

## Findings

### 1. Cross-System Architectural Trade-Off Matrix

`Basis: source + normative + documentation`

| Dimension | RISC Zero (`risc0` v3.1) | Succinct SP1 v5 (`v5.2.4`) | Succinct SP1 v6 (`v6.10.0`) | Jolt (`a16z/jolt`) | Nova / SuperNova (`nova-snark` v0.76) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Target Guest ISA** | `RV32IM` | `RV32IM` | `RV64IM` (User/Supervisor) | `RV64IMAC` (`XLEN = 64`) | Arbitrary step circuits (`SuperNova` ISA) |
| **Native Field $\mathbb{F}$** | `BabyBear` ($2^{31} - 2^{27} + 1$) | `BabyBear` ($2^{31} - 2^{27} + 1$) | `KoalaBear` ($2^{31} - 2^{24} + 1$) | 254-bit curve scalar (`BN254` $\mathbb{F}_r$) | 2-cycle (`Pallas`/`Vesta`, `BN254`/`Grumpkin`) |
| **Soundness Extension** | Quartic $\mathbb{F}_{p^4}$ ($x^4 + 11$, ~124-bit) | Quartic $\mathbb{F}_{p^4}$ ($x^4 + 11$) | Quartic $\mathbb{F}_{p^4}$ (`slop-koala-bear`) | Native ~254-bit scalar field | Native ~254-bit scalar fields |
| **Constraint IR** | Zirgen polynomial AIR + taps | Plonky3 `AirBuilder` multi-chip | `sp1-hypercube` multilinear AIR | `Spartan` outer R1CS + MLE lookups | `RelaxedR1CS` $(AZ)\circ(BZ)=u(CZ)+E$ |
| **Polynomial Commitment** | Univariate 2-adic FRI (Poseidon2/SHA2) | Univariate 2-adic FRI (`p3-fri`) | Multilinear Jagged + Basefold/WHIR | Multilinear `Dory` / `HyperKZG` | `Pedersen`+`IPA`, `HyperKZG`, `Mercury` |
| **ALU Word Encoding** | 4 $\times$ `u8` / 2 $\times$ `u16` limbs | `Word<T>` = 4 $\times$ `u8` limbs | `Word<T>` = 4 $\times$ `u16` limbs (64-bit) | Single native $\mathbb{F}_r$ element | Non-native or limb gadgets in R1CS |
| **Instruction Evaluation** | Degree-bounded custom AIR columns | Per-family chips + `ByteChip` LogUp | Per-opcode chips + `ByteChip` LogUp | `Shout` / `Lasso` virtual $2^{128}$ tables | Active instruction R1CS $F_{pc}$ folded |
| **RAM / Register Checking** | Poseidon2 paged Merkle + in-segment Plonk/LogUp | `(shard, clk)` offline memory LogUp | `(clk_high, clk_low)` LogUp + `PageProt` | `Twist` one-hot `(Ra, Wa)` + `Inc` sumcheck | Merkleized RAM or Nebula/SuperNova MCC |
| **Acceleration Strategy** | Dedicated `keccak`, `sha2`, `bigint2` byte-polys | Stateful syscall precompile chips on bus | Stateful syscall precompile chips on bus | `jolt-inlines` virtual instructions (`VirtualXORROT*`) | Custom R1CS instruction circuits $F_j$ |
| **Long-Trace Scaling** | `SystemSplit` segment continuations + STARK recursion | Sharded `MemoryGlobalChip` + STARK recursion | Hypercube shards + recursion -> Groth16/Plonk | Streaming sumcheck over $T$-step trace | Constant-overhead $O(1)$ IVC step folding |

### 2. Small-Field Multi-Table STARKs, Continuations, and Precompile Buses (`risc0`, `SP1`, `Plonky3`)

#### 2.1 31-Bit Prime Selection and Multi-Limb Word Representation
`Basis: source`

In `Plonky3/Plonky3` (`baby-bear/src/baby_bear.rs:14-76`), `BabyBear` is instantiated as `MontyField31<BabyBearParameters>` with prime:
$$p_{\text{BabyBear}} = 2^{31} - 2^{27} + 1 = 15 \cdot 2^{27} + 1 = \text{0x78000001} = 2{,}013{,}265{,}921$$
Because $p - 1 = 15 \cdot 2^{27}$, $\mathbb{F}_p^\times$ has two-adicity $27$ (`TWO_ADICITY = 27`), supporting radix-2 NTT domains up to $2^{27}$ rows, S-box degree $d = 7$ ($\gcd(7, p - 1) = 1$, `exp_1725656503`), and binomial degree-4 extension $\mathbb{F}_{p^4} = \mathbb{F}_p[X]/(X^4 - 11)$ (`W = 11`, two-adicity $29$). SP1 v6 (`crates/hypercube/Cargo.toml:31`) transitions to `KoalaBear` ($p_{\text{KoalaBear}} = 2^{31} - 2^{24} + 1 = 127 \cdot 2^{24} + 1 = \text{0x7f000001} = 2{,}130{,}706{,}433$, two-adicity $24$), trading maximal NTT domain size (unneeded in multilinear sumcheck provers) for $24$-bit alignment with 8-bit and 16-bit range tables.

Because $p < 2^{32}$, neither a 32-bit `RV32IM` word nor a 64-bit `RV64IM` word embeds injectively into a single base-field element:
- In SP1 v5 (`crates/core/machine/src/cpu/air/register.rs:65`), a 32-bit `Word<T>` comprises four `u8` columns $[w_0, w_1, w_2, w_3]$ representing $\sum_{i=0}^3 w_i 2^{8i}$, requiring explicit `ByteOpcode::U8Range` lookups whenever witnesses are unconstrained by producer chips.
- In SP1 v6 (`crates/core/machine/src/alu/divrem/mod.rs:45-96`), a 64-bit `Word<T>` comprises four `u16` limbs (`WORD_SIZE = 4`), and 128-bit intermediate products (`c_times_quotient`) span `LONG_WORD_SIZE = 8` limbs.
- In RISC Zero (`risc0/circuit/rv32im/src/prove/witgen/byte_poly.rs:33-105`), 256-bit modular arithmetic (`bigint2`) avoids full bit decomposition by representing witnesses as SIMD-chunked byte polynomials $P(X) = \sum_i c_i X^i$ (`BytePolynomial`), verifying polynomial identities at $X = 256$ via carry-propagation instructions (`PolyOp::Carry1` shifting biased limbs `(delta - 128) * 64 * 256`, `PolyOp::Carry2`, and `PolyOp::EqZero` multiplying by $(X - 256)$ before asserting zero coefficients).

#### 2.2 Continuation Segments vs. Global Bus Sharding
`Basis: source`

Proving billion-cycle executions inside a single flat STARK matrix exhausts host RAM and NTT domain bounds. RISC Zero and SP1 partition traces differently:

1. **RISC Zero Paged-Merkle Continuations (`risc0/zkvm/src/claim/receipt.rs:57-72`, `risc0/zkvm/src/receipt/composite.rs:68-159`, `risc0/circuit/rv32im/src/execute/pager.rs:28-120`):**
   Execution splits at cycle thresholds (`ExitCode::SystemSplit`) into independent `SegmentReceipt` proofs. Only pages touched during a segment transition from `PageState::Unloaded` (`0b00`) to `Loaded` (`0b01`) or `Dirty` (`0b10 | 0b11`). At segment entry, the circuit hashes touched pages and Poseidon2 Merkle siblings (`PAGE_CYCLES`, `NODE_CYCLES`) against `claim.pre.merkle_root`; at exit, dirty pages re-hash into `claim.post.merkle_root`. `CompositeReceipt::verify_integrity_with_context` enforces:
   - Every non-final segment $i$ must have `exit_code == ExitCode::SystemSplit` (`composite.rs:90-92`) and `output.is_none()` (`composite.rs:93-95`).
   - Exact state chaining: $\operatorname{Digest}(\text{seg}_i.\text{post}) = \operatorname{Digest}(\text{seg}_{i+1}.\text{pre})$ (`composite.rs:86-88, 110-112`).
   - Every guest assumption (`env::verify`) recorded in the final segment's `Output.assumptions` must match an attached `InnerAssumptionReceipt` under either `Digest::ZERO` (same recursion control root) or an explicit `assumption.control_root` (`composite.rs:118-156`).
2. **SP1 Deferred Cross-Shard Accumulators (`sp1` v5 `crates/core/machine/src/memory/global.rs`, `operations/global_interaction.rs`):**
   Rather than Merkle-hashing touched pages at every shard boundary, SP1 shards the CPU trace and defers stateful precompile invocations (`SHA256`, `Keccak256`, `WeierstrassAdd`) into dedicated tables that can sit in separate shards. Intra-shard (`InteractionScope::Local`) consistency uses `LogUp` extension-field rational sums; cross-shard (`InteractionScope::Global`) consistency maps each sent/received tuple onto deterministic elliptic-curve points (or Septic extension accumulators) summed homomorphically across shards by the recursive verifier.

#### 2.3 Logarithmic-Derivative (`LogUp`) Bus & Offline Memory Checking
`Basis: normative + source`

Following Blum et al. (`DOI: 10.1109/SFCS.1991.185352`) and Haböck (`ePrint 2022/1530`), SP1 (`crates/core/machine/src/air/memory.rs:18-172` in v5; `:20-360` in v6) and Plonky3 (`lookup/src/logup.rs:70-220`) replace Plonk grand-product permutations $\prod (\alpha - a_i)^{m_i} = \prod (\alpha - b_j)^{m'_j}$ with extension-field rational sums:
$$\sum_{r, c} \frac{m_{c}(r)}{\alpha - \sum_{j=0}^{k-1} e_{c,j}(r)\,\beta^{k-1-j}} = 0 \pmod{\mathbb{F}_{p^4}}$$
In `Plonky3` (`lookup/src/logup.rs:93-98`), each lookup $c$ pins an auxiliary fraction column $f_c[r]$ via $U_c(r)\cdot f_c[r] - V_c(r) = 0$ and accumulates `acc[i+1] = acc[i] + sum_c f_c[i]`.

To prove read-write RAM consistency without sorting the entire trace into address-chronological order in a separate huge table:
- `MemoryGlobalChip` emits initial memory cells `(ts = 0, addr, init_val)` as *receives* (multiplicity $-1$) and final memory cells `(ts_final, addr, final_val)` as *sends* (multiplicity $+1$).
- Every active (`do_check == 1`, boolean-checked) memory read or write at current timestamp $t_{\text{curr}}$ witnesses `(prev_ts, prev_val)`, **sends** `(prev_ts, addr, prev_val)` with multiplicity $+1$, and **receives** `(curr_ts, addr, new_val)` with multiplicity $-1$ (`memory.rs:56-65, 107-116` in v6; for reads, `new_val = prev_val`).
- By telescoping cancellation, the global multiset sum vanishes (up to $\text{negl}(\lambda)$ Schwartz–Zippel soundness error $N / |\mathbb{F}_{p^4}|$) **if and only if** the directed edges $\text{prev\_ts} \to \text{curr\_ts}$ at each `addr` form disjoint chains from initialization to finalization—which holds **if and only if** strict chronological monotonicity $t_{\text{prev}} < t_{\text{curr}}$ holds at every transition, preventing zero-sum directed cycles!
- **Timestamp Monotonicity Reduction (`memory.rs:265-326` in v6; `:90-172` in v5):**
  In SP1 v6, timestamps are 48-bit pairs `(clk_high, clk_low)` with each limb $< 2^{24}$. A boolean witness `compare_low` selects whether `clk_high == prev_high` (checked via `when(compare_low).assert_eq(clk_high, prev_high)`); the active limb $v_{\text{curr}}, v_{\text{prev}}$ satisfies $v_{\text{curr}} > v_{\text{prev}}$ iff:
  $$v_{\text{curr}} - v_{\text{prev}} - 1 \equiv \ell_{16} + 2^{16}\cdot \ell_8 \pmod p, \qquad \ell_{16} \in [0, 2^{16}),\; \ell_8 \in [0, 2^8)$$
  Because $0 \le v_{\text{curr}}, v_{\text{prev}} < 2^{24}$ and $p > 2 \cdot 2^{24}$, any non-increasing transition $v_{\text{curr}} \le v_{\text{prev}}$ wraps modulo $p$ into $[p - 2^{24}, p - 1]$, which is disjoint from $[0, 2^{24} - 1]$ (`p - 2^24 = 2,113,929,217 >= 16,777,216`).

#### 2.4 Stateful Precompile Chips and FFI Syscall Contracts
`Basis: source`

Executing `SHA-256` or `secp256k1` scalar multiplication in guest `RV32IM`/`RV64IM` takes tens to hundreds of thousands of CPU rows; stateful precompile chips (`sp1` `crates/core/machine/src/syscall/precompiles/{sha256,keccak256,weierstrass,fptower,edwards,uint256,poseidon2}`) reduce this by $20\times$–$100\times$ via an explicit cross-table FFI contract:
1. Guest code invokes `ECALL` with `syscall_id` in `t0` (`x5`) and pointer/parameter arguments in `a0` (`x10`), `a1` (`x11`).
2. The CPU/Syscall chip emits `(shard/clk, syscall_id, arg1, arg2)` onto `InteractionKind::Syscall`.
3. The precompile chip receives that exact tuple on `InteractionKind::Syscall` and directly reads/writes guest RAM slices via `eval_memory_access_slice_read` / `eval_memory_access_slice_write` at sequential sub-timestamps derived from `clk`.
4. **Critical Precompile Soundness Invariants:** The precompile chip must (a) verify word alignment and non-aliasing of `arg1`/`arg2` buffers when simultaneous reads/writes occur in the same cycle, (b) enforce canonical field reductions ($< q_{\text{curve}}$, not merely limb bounds) on elliptic-curve/tower coordinates (`fptower`, `weierstrass`), and (c) validate `PageProt` read/write permissions when `mprotect` is active (`sp1` v6 `memory.rs:364-380`).

### 3. Lookup-Singularity Sumcheck ZKVMs (`Jolt`, `Lasso`, `Twist` & `Shout`)

#### 3.1 Decomposable Structured Tables Without Bit Decomposition
`Basis: normative + source`

Arun, Setty, and Thaler (`DOI: 10.1007/978-3-031-58751-1_1`) and Setty, Thaler, and Wahby (`DOI: 10.1007/978-3-031-58751-1_7`) observe that for a 64-bit two-operand RISC-V instruction $(x, y) \in \{0, 1\}^{64} \times \{0, 1\}^{64}$, the truth table $T \in \mathbb{F}^{2^{128}}$ is far too large to materialize, yet its **multilinear extension (MLE)** $\widetilde{T}(r_1, \dots, r_{128})$ is *prefix-suffix decomposable* (`SO` / `Spark`-structured) and evaluable by the verifier in $O(\log |T|) = O(\text{XLEN})$ field operations with **zero table commitment**.

In `a16z/jolt` (`crates/jolt-lookup-tables/src/tables/mod.rs:137-195`), every lookup-eligible instruction maps to one of 56 `LookupTableKind<XLEN>` variants (`RangeCheck`, `And`, `Andn`, `Or`, `Xor`, `SignedLessThan`, `ValidUnsignedRemainder`, `ValidDiv0`, `MulUNoOverflow`, `VirtualSRA`, `VirtualXORROT*`, etc.). For example, `ValidDiv0Table<XLEN>` (`tables/valid_div0.rs:15-65`) enforces the RISC-V `M`-extension division-by-zero rule ($d = 0 \implies q = 2^{\text{XLEN}} - 1$) over interleaved bit variables $(x_0, y_0, \dots, x_{\text{XLEN}-1}, y_{\text{XLEN}-1})$ via the exact closed-form MLE:
$$\widetilde{\text{ValidDiv0}}(x, y) = 1 - \prod_{i=0}^{\text{XLEN}-1} (1 - x_i) + \prod_{i=0}^{\text{XLEN}-1} (1 - x_i)\,y_i$$
decomposed via `PrefixSuffixDecomposition<XLEN>` into just two prefixes (`LeftOperandIsZero`, `DivByZero`) and three suffixes (`One`, `LeftOperandIsZero`, `DivByZero`) so chunked `Shout`/`Lasso` subtable sumchecks pay only for accessed entries.

#### 3.2 `Twist` and `Shout`: One-Hot Addressing and Increments
`Basis: normative + source`

Setty, Thaler, and Zhu (`ePrint 2025/105`) eliminate grand-product and LogUp rational-fraction commitments entirely:
- **`Shout` (Read-Only Lookups — Bytecode & Instruction Subtables):** Represents each step $j \in [T]$'s lookup address $k_j \in [K]$ as a $d$-dimensional tensor product of one-hot vectors $\text{ra}_1(k^{(1)}, j) \otimes \cdots \otimes \text{ra}_d(k^{(d)}, j) \in \{0, 1\}^K$, proving $\text{rv}(j) = \sum_{k \in \{0,1\}^{\log K}} \widetilde{\text{ra}}(k, j) \cdot \widetilde{T}(k)$ via sumcheck while checking Booleanity $\text{ra}_\ell(i, j) \cdot (1 - \text{ra}_\ell(i, j)) = 0$ and Hamming weight $\sum_i \text{ra}_\ell(i, j) = 1$.
- **`Twist` (Read-Write Registers & RAM — `crates/jolt-claims/src/twist/memory_checking.rs:34-88`):** Instead of committing to the full $K \times T$ memory-state matrix $\text{Val}(k, j)$ (which has $K \cdot T$ nonzeros), the prover commits *only* to the one-hot write-address indicator $\text{RdWa}(k, j)$ and a **single scalar increment** $\text{Inc}(j) = w_{\text{new}}(j) - \text{Val}(k_{\text{write}}(j), j)$ per cycle $j$ ($T$ nonzeros total!).
  `jolt-claims/src/twist/memory_checking.rs` enforces two degree-3 sumcheck identities:
  1. **Read/Write Checking (`READ_WRITE_CHECKING_DEGREE = 3`, lines 37-54):** Batches `rd_value`, `rs1_value`, and `rs2_value` with challenge $\gamma$:
     $$\text{rd} + \gamma\cdot\text{rs1} + \gamma^2\cdot\text{rs2} = \sum_{k, j} \widetilde{\text{eq}}(\tau, j)\Big(\widetilde{\text{RdWa}}(k, j)\widetilde{\text{Inc}}(j) + \big(\widetilde{\text{RdWa}}(k, j) + \gamma\widetilde{\text{Rs1Ra}}(k, j) + \gamma^2\widetilde{\text{Rs2Ra}}(k, j)\big)\widetilde{\text{Val}}(k, j)\Big)$$
  2. **Virtual Value Evaluation (`VAL_EVALUATION_DEGREE = 3`, lines 78-87):** Reduces any queried opening $\widetilde{\text{Val}}(r_{\text{addr}}, r_{\text{cycle}})$ to strictly earlier increments using the strict-less-than MLE $\widetilde{\text{lt}}(j, j')$:
     $$\widetilde{\text{Val}}(r_{\text{addr}}, r_{\text{cycle}}) = \sum_{j \in \{0,1\}^{\log T}} \widetilde{\text{lt}}(j, r_{\text{cycle}})\cdot \widetilde{\text{Inc}}(j)\cdot \widetilde{\text{RdWa}}(r_{\text{addr}}, j)$$

### 4. Folding-Based Non-Uniform IVC (`Nova`, `SuperNova`, `NeutronNova`)

`Basis: normative + source`

Kothapalli, Setty, and Tzialla (`DOI: 10.1007/978-3-031-15985-5_13`) replace recursive SNARK verification inside each step circuit with **Relaxed R1CS** (`microsoft/Nova` `src/r1cs/mod.rs:83-101, 447-502`). Given sparse matrices $A, B, C \in \mathbb{F}^{m \times n}$, a relaxed instance $U = (\overline{W}, \overline{E}, X, u)$ is satisfied by witness $(W, r_W, E, r_E)$ with $Z = (W, u, X)$ iff:
$$(A Z) \circ (B Z) = u \cdot (C Z) + E, \qquad \overline{W} = \operatorname{Com}(W, r_W),\quad \overline{E} = \operatorname{Com}(E, r_E)$$
Strict R1CS corresponds to $u = 1, E = \vec{0}$. To fold a running relaxed instance $(U_1, W_1)$ with a fresh step strict R1CS instance $(U_2, W_2)$ ($u_2 = 1, E_2 = \vec{0}$), `R1CSShape::commit_T` (`src/r1cs/mod.rs:551-598`) uses the Mova algebraic identity ($Z_+ = Z_1 + Z_2$) to compute the cross-term vector in 3 SpMVs instead of 6:
$$T = (A Z_+) \circ (B Z_+) - (u_1 + 1)(C Z_+) - E_1 = (A Z_1)\circ(B Z_2) + (A Z_2)\circ(B Z_1) - u_1(C Z_2) - (C Z_1)$$
Given Fiat-Shamir challenge $r \leftarrow \text{RO}(\text{pp\_digest}, U_2, \overline{T})$ (`src/nova/nifs.rs:47-72`), folding sets:
$$W \leftarrow W_1 + r W_2, \quad E \leftarrow E_1 + r T, \quad u \leftarrow u_1 + r, \quad X \leftarrow X_1 + r X_2, \quad \overline{W} \leftarrow \overline{W}_1 + r\overline{W}_2, \quad \overline{E} \leftarrow \overline{E}_1 + r\overline{T}$$
Only two homomorphic scalar multiplications ($r\overline{W}_2, r\overline{T}$) execute inside the augmented step circuit!

- **Non-Uniform Machine Executions (`SuperNova`, `ePrint 2022/1758`):** Standard uniform Nova forces every step to evaluate a universal circuit $\mathcal{U}$ summing all $|I|$ RISC-V instructions ($\Omega(\sum_{j=1}^{|I|} |F_j|)$ gates/step). SuperNova maintains a vector of $|I|$ running relaxed instances $\vec{U} = (U_1, \dots, U_{|I|})$, one per instruction shape $S_j$. At step $i$, program counter $\text{pc}_i \in [|I|]$ selects *only* circuit $F_{\text{pc}_i}$ to synthesize and fold into $U_{\text{pc}_i}$, leaving $U_{j \neq \text{pc}_i}$ untouched; the prover pays $O(|F_{\text{pc}_i}|)$ work while the augmented verifier circuit hashes $\vec{U}$ and updates entry $\text{pc}_i$. Note that `microsoft/Nova` `v0.76.0` (`01b1e2d662a847ed7029770ecbaf6687398899dd`) provides uniform two-curve IVC (`src/nova/`) plus experimental sumcheck-based `NeutronNova` (`src/neutron/mod.rs:1-2`, explicitly marked incomplete/non-production).

### 5. Taxonomy of Real-World ZKVM Soundness Bugs and Executable Micro-Probes

`Basis: source + normative + execution + derived`

Every soundness failure in a zkVM permits a malicious prover to construct a witness $w^* \neq w_{\text{honest}}$ satisfying all polynomial/lookup/folding checks for a false statement. Below are the five primary bug classes, grounded in disclosed advisories and verified via executable micro-probes.

#### Class A: Underconstrained Decode Selectors, Multi-Step Modes, and Exclusive LogUp Flags
- **Real Advisories:**
  - `risc0/risc0` **`GHSA-5c79-r6x7-3jx9`** (`< v1.1.1`): Multi-cycle RISC-V instructions set a major mode in cycle 1 to govern continuation cycles, but subsequent cycles lacked constraints proving the mode originated from a legitimate preceding instruction, enabling forged mid-instruction execution states.
- **Plonky3 `LogUpGadget::fold_exclusive_terms` Algebraic Hazard (`Plonky3/lookup/src/logup.rs:190-220`):**
  To avoid high-degree denominator products across mutually exclusive opcode branches, `fold_exclusive_terms` sets $N = \sum_k f_k m_k$ and $D = \sum_k f_k (\alpha - c_k) + (1 - \sum_k f_k)$, explicitly warning that the AIR *must* enforce $f_k \in \{0, 1\}$ AND $\sum_k f_k \in \{0, 1\}$. Our execution probe `[1A]` demonstrates two distinct breaks if an AIR omits either constraint:
  1. If $f_1 = 1, f_2 = 1$ (individual boolean checks hold, mutual-exclusion sum check omitted), the row folds to $(m_1 + m_2)/(2\alpha - c_1 - c_2 - 1) \neq m_1/(\alpha - c_1) + m_2/(\alpha - c_2)$, corrupting bus accounting.
  2. Worse, if booleanity is omitted on a selector pair with $m_1 = m_2 = 1$, setting $f_1 = 1, f_2 = p - 1$ yields $N = 0$ and $D = c_2 - c_1 + 1$ (**identically independent of the Fiat-Shamir challenge $\alpha$**), satisfying $D \cdot 0 - N = 0$ for all $\alpha$ while activating main-trace side effects with **zero** LogUp bus emission!

#### Class B: Missing 32/64-Bit Carry, Borrow, and Signed Division Uniqueness Constraints
- **Real Advisories:**
  - `risc0/risc0` **`GHSA-f6rc-24x4-ppxp` / `CVE-2025-54873`** (`risc0-circuit-rv32im >= 2.0, < 3.0`, found via Veridise *Picus*): Signed RV32IM division permitted two satisfying outputs for certain negative inputs, and division-by-zero ($c = 0$) output was underconstrained.
  - `0xPARC/zk-bug-tracker` (`56a996672fb50486279126c8e12530f2bf933d0b`, `README.md:36-78`): `LessThan` / `BigInt` / zkEVM missing bit-length and remainder bounds.
- **Exact Invariant (`SP1` `DivRemCols`, `crates/core/machine/src/alu/divrem/mod.rs:72-160`):**
  Euclidean identity $b = c \cdot q + r$ with $|r| < |c|$ is **insufficient** for signed RISC-V `DIV`/`REM` (`truncation toward zero`): as verified in probe `[1B]`, $b = -7, c = 3$ admits both $(q = -2, r = -1)$ (architectural) and $(q = -3, r = +2)$ (Euclidean floor) unless $\operatorname{sgn}(r) \in \{0, \operatorname{sgn}(b)\}$ is constrained alongside explicit boundary guards for $c = 0 \implies (q = -1, r = b)$ and signed overflow $(b = -2^{\text{XLEN}-1}, c = -1) \implies (q = -2^{\text{XLEN}-1}, r = 0)$. Similarly, omitting booleanity $c_{\text{top}} \in \{0, 1\}$ on the top overflow carry of wrapping 32-bit addition over `BabyBear` allows $c_{\text{top}} = 1{,}069{,}547{,}521 \equiv -(2^{32})^{-1} \pmod p$, forging `0 + 0 = 1` with all four output byte limbs cleanly inside $[0, 255]$!

#### Class C: Forged Offline Memory Timestamps and Same-Cycle `rs1 == rs2` Read Aliasing
- **Real Advisories:**
  - `risc0/risc0` **`GHSA-g3qg-6746-3mg9` / `CVE-2025-52484`** (`risc0-circuit-rv32im < 2.0.4`): Critical soundness flaw in 3-register RV32IM instructions (`remu`, `divu`, ALU ops). A malicious prover could alias `rs1` and `rs2` reads (`rs1 == rs2` vs `rs1 != rs2`) because performing two register reads to the same address within a single memory cycle violated unique-timestamp memory-subsystem assumptions.
- **Architectural Mitigations & Rogue-Timestamp Failure Mode:**
  1. **Sub-Cycle Offset Disambiguation (`SP1` `crates/core/machine/src/cpu/air/register.rs:28-60`):** SP1 stamps operand reads/writes within a single instruction at strictly distinct sub-cycle offsets `clk + MemoryAccessPosition::B`, `clk + MemoryAccessPosition::C`, and `clk + MemoryAccessPosition::A` (incrementing `clk` by `CLK_INC >= 4` per instruction), guaranteeing $t_B \neq t_C \neq t_A$ even when `rs1 == rs2 == rd`. (In Jolt's `Twist`, `memory_checking.rs:50-54` reads `Rs1Ra · Val` and `Rs2Ra · Val` against the *same* pre-write `Val(k, j)` before adding `RdWa · Inc`, avoiding read-read timestamp mutation altogether.)
  2. **Endpoint Range Precondition (`SP1` `memory.rs:295-308`):** As demonstrated in probe `[1C]`, the 24-bit difference range check $0 \le t_{\text{curr}} - t_{\text{prev}} - 1 < 2^{24}$ over `KoalaBear` ($p = \text{0x7f000001}$) is sound **only if** every producer chip also bounds emitted timestamps to $[0, 2^{24})$. If a custom chip emits a memory write at un-range-checked timestamp $t_{\text{rogue}} = p - 1$, a CPU read at $t_{\text{curr}} = 0$ witnesses $t_{\text{prev}} = p - 1$, yielding $(0 - (p - 1) - 1) \bmod p = 0$ (`limb_16 = 0, limb_8 = 0`) and reading a **future** or fabricated write at cycle 0!

#### Class D: Unverified Host-Oracle Hint Non-Determinism and Guest Syscall Corruption
- **Real Advisories:**
  - `risc0/risc0` **`GHSA-349p-x622-29x6`** (`< v1.1.3`) and **`GHSA-jqq4-c7wq-36h7`** (Oct 2025): Host-driven syscall manipulation and guest memory-safety corruption in `sys_read`.
- **Two-Layer Boundary Rule:**
  1. **Circuit Layer:** Hints (`HINT_LEN` / `HINT_READ` in SP1 `register.rs:62-65`, `BytePolyProgram` witnesses in RISC Zero) arrive as untrusted field elements; writing a hint into a `Word<T>` without `slice_range_check_u8`/`u16` injects non-canonical limbs ($w_i \ge 256$) that break downstream equality, bitwise, and comparison gadgets.
  2. **Guest Verification Layer:** Proving $\exists h.\; P(x, h) = 1$ is unsound whenever the specification requires functional determinism $y = f(x)$ and $P$ checks only a non-unique necessary condition (e.g., proving modular square root $r^2 \equiv a \pmod q$ without canonical parity/range bit, or accepting host key-value non-membership hints without verifying Merkle exclusion paths inside the guest).

#### Class E: Fiat-Shamir Transcript Omissions, Sumcheck Claim Splicing, and Verifier Shape Gaps
- **Real Advisories:**
  - `succinctlabs/sp1` **`GHSA-8m24-3cfx-9fjw`**: Insufficient Fiat-Shamir observation of LogUp cumulative sums.
  - `succinctlabs/sp1` **`GHSA-63x8-x938-vx33` / `CVE-2026-40323`** (`v6.0.0`–`v6.0.2`): Recursion circuit row-count binding gap allowing invalid shard proofs to be recursively wrapped.
  - `succinctlabs/sp1` **`GHSA-p7v2-jjv3-8p8f`** (`v6.0.0`–`v6.8.0`): Native Rust verifier trusted tensor dimension metadata without checking underlying buffer lengths.
  - `a16z/jolt` **PR #1474** (patched in `crates/jolt-verifier/src/stages/uniskip.rs:154-164`): Clear-mode `uni-skip` verifier previously checked the univariate first-round sumcheck polynomial $g_1(X)$ over `CenteredIntegerDomain` and passed proof-supplied `output_claim` to the batched remainder sumcheck **without** asserting `reduction.value == output_claim` ($g_1(r_0) = \text{output\_claim}$), allowing an attacker to splice a valid trivial `uni-skip` proof onto a forged execution remainder!
  - `microsoft/Nova` **`NIFS::prove` Transcript Precondition (`src/nova/nifs.rs:52-53` vs `NIFSRelaxed::prove` `:144`):** `NIFS::prove` deliberately omits absorbing running instance `U1` into the random oracle because Nova's augmented step circuit sets `U2.X[0] = Hash(params, U1, i, z0, zi)`. Any standalone caller invoking `NIFS::prove` on raw R1CS instances where `U2.X` does not cryptographically bind `U1` suffers immediate rogue-instance folding forgery.

#### Executable Verification Probe (`Basis: execution`)

Running the following standalone Python 3.13 script reproduces all four algebraic counterexamples and positive MLE/folding checks:

```python
#!/usr/bin/env python3
"""Deterministic micro-probes for ZKVM arithmetization and underconstraint bugs."""

BABY_BEAR = (1 << 31) - (1 << 27) + 1   # 0x78000001 = 2013265921
KOALA_BEAR = (1 << 31) - (1 << 24) + 1  # 0x7f000001 = 2130706433

def modinv(a: int, p: int) -> int:
    return pow(a % p, p - 2, p)

def run_probes() -> None:
    p = BABY_BEAR
    alpha, c1, c2, m1, m2 = 123456789, 42, 99, 1, 1
    # [1A] Plonky3 fold_exclusive_terms under dual-boolean vs non-boolean ghost flags
    f1, f2 = 1, 1
    N_excl = (f1 * m1 + f2 * m2) % p
    D_excl = (f1 * (alpha - c1) + f2 * (alpha - c2) + (1 - (f1 + f2))) % p
    folded_val = (N_excl * modinv(D_excl, p)) % p
    true_sum = (m1 * modinv(alpha - c1, p) + m2 * modinv(alpha - c2, p)) % p
    assert folded_val != true_sum
    f1_g, f2_g = 1, p - 1
    for test_alpha in (7, 314159, 1999999999):
        N_g = (f1_g * m1 + f2_g * m2) % p
        D_g = (f1_g * (test_alpha - c1) + f2_g * (test_alpha - c2) + (1 - (f1_g + f2_g))) % p
        assert N_g == 0 and D_g == (c2 - c1 + 1) % p
    print(f"[1A] BabyBear p={p:#x}: dual-boolean-flag folded={folded_val} != true_sum={true_sum}; "
          f"non-boolean ghost (f1=1, f2=p-1) gives alpha-independent D={c2 - c1 + 1}, N=0.")

    # [1B] Signed DIV(-7, 3) missing remainder-sign & top-carry non-boolean forgery
    b, c = -7, 3
    candidates = [(q, r) for q in range(-10, 10) for r in range(-abs(c) + 1, abs(c)) if c * q + r == b]
    assert candidates == [(-3, 2), (-2, -1)]
    two32_mod_p = (1 << 32) % p
    forged_carry_top = (modinv(two32_mod_p, p) * (p - 1)) % p
    forged_u32 = (0 + 0 - forged_carry_top * two32_mod_p) % p
    assert forged_u32 == 1 and forged_carry_top not in (0, 1)
    print(f"[1B] Signed DIV(-7, 3) unconstrained-sign witnesses={candidates}; "
          f"non-boolean carry_top={forged_carry_top} forges 0+0 == {forged_u32} (mod p) with valid u8 limbs!")

    # [1C] KoalaBear offline memory timestamp wrap-around when prev_low >= 2^24
    pk = KOALA_BEAR
    clk, prev_low = 0, pk - 1
    diff_minus_one = (clk - prev_low - 1) % pk
    assert diff_minus_one == 0
    print(f"[1C] KoalaBear p={pk:#x}: rogue prev_low=p-1 at clk=0 yields diff_minus_one={diff_minus_one} "
          f"(limb_16=0, limb_8=0), bypassing 24-bit timestamp ordering!")

    # [1D] Jolt ValidDiv0Table<8> MLE hypercube equivalence & Nova Mova-style cross-term T
    for d in range(256):
        for q in range(256):
            expected = (1 if q == 255 else 0) if d == 0 else 1
            d_zero, v_div0 = 1, 1
            for i in range(8):
                xi, yi = (d >> i) & 1, (q >> i) & 1
                d_zero = (d_zero * (1 - xi)) % p
                v_div0 = (v_div0 * (1 - xi) * yi) % p
            assert (1 - d_zero + v_div0) % p == expected
    Z1, u1, E1, Z2 = [5, 2, 10], 2, 5, [3, 1, 9]
    Z_sum = [(a + b_i) % p for a, b_i in zip(Z1, Z2)]
    T = (Z_sum[0] * Z_sum[0] - (u1 + 1) * Z_sum[2] - E1) % p
    r = 777
    Zf = [(a + r * b_i) % p for a, b_i in zip(Z1, Z2)]
    assert (Zf[0] * Zf[0]) % p == ((u1 + r) * Zf[2] + (E1 + r * T)) % p
    print(f"[1D] Jolt ValidDiv0Table<8> MLE verified across all 65,536 (d, q) pairs; "
          f"Nova folded R1CS satisfied with cross-term T={T}, E_fold={(E1 + r * T) % p}.")

if __name__ == "__main__":
    run_probes()
```

Observed output (`Python 3.13.15`):
```text
[1A] BabyBear p=0x78000001: dual-boolean-flag folded=660160971 != true_sum=180934212; non-boolean ghost (f1=1, f2=p-1) gives alpha-independent D=58, N=0.
[1B] Signed DIV(-7, 3) unconstrained-sign witnesses=[(-3, 2), (-2, -1)]; non-boolean carry_top=1069547521 forges 0+0 == 1 (mod p) with valid u8 limbs!
[1C] KoalaBear p=0x7f000001: rogue prev_low=p-1 at clk=0 yields diff_minus_one=0 (limb_16=0, limb_8=0), bypassing 24-bit timestamp ordering!
[1D] Jolt ValidDiv0Table<8> MLE verified across all 65,536 (d, q) pairs; Nova folded R1CS satisfied with cross-term T=2, E_fold=1559.
```

## Boundaries

- **Zero-knowledge (perfect/statistical hiding) vs. succinctness (`known not to apply` by default in several modes):** Passing `verify` in clear/transparent prover modes does not imply statistical zero-knowledge. RISC Zero documented non-zero-knowledge leakage nuances in `GHSA-5xgj-pmjj-gw49`; Jolt separates `verify_clear` (`stages/uniskip.rs:136`) from `BlindFold` `verify_zk` (`stages/uniskip.rs:174`); Nova achieves zero-knowledge only when the final running accumulator is randomized via `NIFSRelaxed` prior to Spartan compression (`microsoft/Nova` `README.md:21`).
- **`NeutronNova` production readiness (`unsupported`):** In `microsoft/Nova` `01b1e2d662a847ed7029770ecbaf6687398899dd`, `src/neutron/mod.rs:1-2` explicitly warns that `NeutronNova` lacks security checks and must not be used in production.
- **Floating-point (`F`/`D`) and compressed/vector (`V`) ISA extensions (`not examined` / `unsupported`):** RISC Zero and SP1 v5 target integer `RV32IM`; SP1 v6 targets `RV64IM`; Jolt targets `RV64IMAC`. Hardware IEEE 754 `F`/`D` rounding modes in native AIR circuits were `not examined` (typically emulated in soft-float guest libraries).
- **End-to-end mechanized Lean/Rocq soundness proofs of full production zkVMs (`unknown`):** While both `succinctlabs/sp1` v6 (`crates/hypercube/src/ir/lean.rs`) and `a16z/jolt` (`crates/jolt-lean-gen/`) include constraint-to-Lean extraction generators at the examined commits, whether complete machine-checked end-to-end equivalence proofs cover all production precompiles and recursion verifiers at these exact revisions was `not examined`.
- **Prover GPU wall-clock benchmarks (`not examined`):** GPU proving throughput (`sppark`, `jolt-metal`, `sp1-cuda`) was `not examined`; structural complexities are derived from committed field/group operation counts.

## Evidence

| Subject / Artifact | Coordinate | Inspected Paths / Identifiers | Evidentiary Role |
| :--- | :--- | :--- | :--- |
| `risc0/risc0` (`v3.1.0`) | `5e1be36a7fcadf98f341e348d9314e5f1d519046` | `Cargo.toml:1-85`, `risc0/zkvm/src/claim/receipt.rs:55-205`, `risc0/zkvm/src/receipt/composite.rs:44-195`, `risc0/circuit/rv32im/src/execute/pager.rs:28-135`, `risc0/circuit/rv32im/src/prove/witgen/byte_poly.rs:33-163` | `source` |
| `succinctlabs/sp1` (`v5.2.4`) | `2a51f3dd370e4c5f74d04dfd89359a13a7e93f99` | `crates/core/machine/src/cpu/air/register.rs:11-74`, `crates/core/machine/src/air/memory.rs:13-173`, `crates/stark/src/air/interaction.rs:1-18` | `source` |
| `succinctlabs/sp1` (`v6.10.0`) | `0cd151a8d7beaaad4ad245c8f37515d6b4f72597` | `Cargo.toml:1-35`, `crates/hypercube/Cargo.toml:18-39`, `crates/core/machine/src/air/memory.rs:17-380`, `crates/core/machine/src/alu/divrem/mod.rs:48-160` | `source` |
| `Plonky3/Plonky3` | `0d803737b681774186cd283b1fd2d8e493655c82` | `baby-bear/src/baby_bear.rs:8-106`, `lookup/src/logup.rs:1-220` | `source` |
| `a16z/jolt` | `943f60ce477cd98f4682a99d82f388468fe20e61` | `crates/jolt-claims/src/twist/memory_checking.rs:10-189`, `crates/jolt-lookup-tables/src/tables/mod.rs:1-196`, `crates/jolt-lookup-tables/src/tables/valid_div0.rs:13-65`, `crates/jolt-verifier/src/stages/uniskip.rs:37-200` | `source` |
| `microsoft/Nova` (`0.76.0`) | `01b1e2d662a847ed7029770ecbaf6687398899dd` | `README.md:1-94`, `src/r1cs/mod.rs:30-102, 447-620`, `src/nova/nifs.rs:19-200`, `src/neutron/mod.rs:1-152` | `source` + `documentation` |
| `0xPARC/zk-bug-tracker` | `56a996672fb50486279126c8e12530f2bf933d0b` | `README.md:1-120` (common vulnerability taxonomy & `LessThan` missing bit-length reproducer) | `documentation` |
| Arun, Setty, Thaler (EUROCRYPT 2024) | `DOI: 10.1007/978-3-031-58751-1_1` (`ePrint 2023/1217`) | Jolt RISC-V lookup decomposition and R1CS fetch-decode-execute constraints | `normative` |
| Setty, Thaler, Wahby (EUROCRYPT 2024) | `DOI: 10.1007/978-3-031-58751-1_7` (`ePrint 2023/1216`) | `Lasso` / `Spark` sparse & prefix-suffix structured lookup arguments | `normative` |
| Setty, Thaler, Zhu (2025) | `IACR ePrint 2025/105` | `Twist` (read-write increment memory checking) and `Shout` (one-hot read-only lookup) | `normative` |
| Kothapalli, Setty, Tzialla (CRYPTO 2022) & SuperNova | `DOI: 10.1007/978-3-031-15985-5_13` (`ePrint 2021/370`); `ePrint 2022/1758` | Relaxed R1CS `NIFS` folding and non-uniform per-instruction IVC | `normative` |
| Haböck (2022) & Blum et al. (1991) | `IACR ePrint 2022/1530`; `DOI: 10.1109/SFCS.1991.185352` | Multivariate `LogUp` rational sums and offline timestamped memory-checking reductions | `normative` |
| Security Advisories (`risc0`, `sp1`, `jolt`) | `CVE-2025-52484` (`GHSA-g3qg-6746-3mg9`), `CVE-2025-54873` (`GHSA-f6rc-24x4-ppxp`), `GHSA-5c79-r6x7-3jx9`, `GHSA-349p-x622-29x6`, `GHSA-jqq4-c7wq-36h7`, `GHSA-8m24-3cfx-9fjw`, `CVE-2026-40323` (`GHSA-63x8-x938-vx33`), `GHSA-p7v2-jjv3-8p8f`, `a16z/jolt#1474` | Documented production zkVM soundness breaks (observed `2026-11-19`) | `documentation` + `source` |
| Inline Python 3.13 Micro-Probes | Executed `2026-11-19` on Linux (`Python 3.13.15`) | `[1A]`–`[1D]` reproducible witness-forgery and MLE/folding verification script | `execution` |

## Revalidation

To revalidate these findings against a newer upstream zkVM revision without repeating broad exploration:

1. **Rerun the Inline Algebraic Micro-Probe (`< 0.2 s`):** Execute `python3 /tmp/zkvm_soundness_probes.py` (copied from **Findings §5**) after substituting any changed prime $p$ or timestamp limb width $W$; verify that $p > 2 \cdot 2^W$ still separates $[0, 2^W - 1]$ from $[p - 2^W, p - 1]$.
2. **Audit Exclusive-Lookup & Decode Selector Completeness:** Diff `Plonky3/lookup/src/logup.rs` (`fold_exclusive_terms`) and target CPU/ALU AIR chips to confirm every exclusive selector vector $(f_1, \dots, f_k)$ enforces *both* $f_i(f_i - 1) = 0$ and $(\sum_i f_i)(\sum_i f_i - 1) = 0$.
3. **Audit Offline Memory Sub-Cycle Offsets & Producer Timestamp Bounds:** Diff `crates/core/machine/src/air/memory.rs` and `register.rs` (in `sp1`) or `twist/memory_checking.rs` (in `jolt`): verify that (a) simultaneous `rs1`, `rs2`, and `rd` accesses within one instruction either read immutable pre-write state (`Twist`) or use distinct sub-cycle clock offsets (`clk + pos`), and (b) every custom/precompile chip emitting `InteractionKind::Memory` guarantees $0 \le \text{clk\_low}, \text{clk\_high} < 2^{24}$.
4. **Audit Sumcheck / Folding Claim-Bridge & Transcript Checks:** In sumcheck verifiers (`jolt-verifier/src/stages/uniskip.rs:154-164`), check that every stage's reduced evaluation `reduction.value` is hard-asserted equal to the downstream `output_claim` *and* absorbed into the Fiat-Shamir transcript prior to squeezing batching weights; in `NIFS` callers (`nova/nifs.rs:52-53`), verify `U1` is either absorbed directly or collision-resistently hashed into `U2.X`.
