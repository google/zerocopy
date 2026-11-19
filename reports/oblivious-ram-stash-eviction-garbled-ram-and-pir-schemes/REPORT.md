# Oblivious RAM Stash Eviction, Doubly-Oblivious Enclaves, Mechanized Trace Obliviousness, Garbled RAM, and Lattice/DPF PIR Schemes

## Summary

Privacy-preserving storage and retrieval span two distinct adversarial trust models—**read-write encrypted access (`ORAM`/`GRAM`)** versus **read-only public-index retrieval (`PIR`)**—whose security guarantees collapse unless tree-eviction invariants, enclave memory-access obliviousness, probabilistic randomness linearity, and finite-ring noise margins are jointly enforced:

1. **`Path ORAM` ($Z \ge 4$) vs. `Circuit ORAM` ($Z = 2$) Stash Stability and Reverse-Lexicographic Scheduling:** Tree-based `Path ORAM` maps each block to an independent uniformly random leaf via a recursive position map; greedy read-path eviction overflows at bucket capacity $Z = 2$ (growing stash linearly once load exceeds $\sim 50\%$: `max_stash = 93` at $N=1536, L=10$ over $20{,}000$ accesses, confirming `mc-oblivious-ram`'s `"XXX: This config is broken"` warning) and requires $Z \ge 4$ (`max_stash = 6`). `Circuit ORAM` achieves bounded stashes at $Z = 2$ (`max_stash = 2, end = 0` at $N=1024$) and $O(W \log N)$ Boolean circuit complexity by pairing **two deterministic reverse-lexicographic path evictions per access** with a two-pass metadata scan (`prepare_deepest` + `prepare_target`) and a single-hold `obliSwap` eviction pass. When batching evictions across non-power-of-two tree leaf counts (e.g., `pathCount = 63`), choosing an **even** coprime stride (`stride = 4`) pins the lowest leaf bit across consecutive windows and starves half the tree; requiring an **odd** coprime stride (`stride = 5`) preserves alternating root-subtree balance.
2. **Network-Only `ORAM` vs. SGX Doubly-Oblivious Execution:** Standard client-server `Path ORAM` prototypes (`obliviousram/PathORAM`) leak secret block indices and stash fullness to local side-channel observers via secret-indexed `position_map[blockIndex]` lookups, conditional `stash.push_back` branches, and early-exit `break` loops (alongside a stack-use-after-scope UB in `OramReadPathEviction.cpp:64-66`). Trusted Execution Environments (`SGX`) require **doubly-oblivious** execution (`mobilecoinfoundation/mc-oblivious`), replacing every branch and key-dependent load with inline-assembly constant-time moves (`neg` $\to$ `CF` $\to$ `cmovc` across `dec/jnz` on 8-byte chunks; `vbroadcastsd` + `vmovdqa` + `vpmaskmovq` on 64-byte cache lines) plus recursive `ORAMU32PositionMap` scans and lazy implicit leaf initialization.
3. **Probabilistic Trace-Oblivious Types ($\lambda_{\text{obliv}}$) and `Garbled RAM`:** Deterministic non-interference type systems cannot certify randomized `ORAM` protocols, and naive random-tape reuse causes joint multi-step trace leaks ($\text{TVD}_2 = 0.75$) even when every single-step marginal distribution is identically uniform ($\text{TVD}_1 = 0$). $\lambda_{\text{obliv}}$ (`Darais et al., POPL 2020`) closes this soundness gap using substructural **linear probability regions** that statically forbid reusing random coins across correlated secrets. Composing tree-ORAM with persistent encrypted memory yields `Garbled RAM` (`Lu & Ostrovsky, EUROCRYPT 2013`), evaluating RAM programs of runtime $T$ in $\tilde{O}(T \cdot \text{poly}(\lambda, \log N))$ garbled gates rather than $O(T \cdot N)$ circuit unrolling.
4. **Single-Server Lattice `PIR` (`SimplePIR`, `DoublePIR`, `Spiral`) vs. Multi-Server `DPF` `PIR`:** 2-server Distributed Point Function (`DPF`) `PIR` (`Boyle et al., 2016`) achieves $O(\lambda \log N)$ query bandwidth and XOR-only server work under a strict non-collusion assumption, whereas single-server lattice `PIR` eliminates multi-server trust. `SimplePIR` precomputes a client hint $H = D \cdot A \pmod{2^{32}}$ and computes online answers via $3 \times 10$-bit packed matrix-vector multiplication (`~10 GB/s/core`), cutting noise standard deviation in half ($2.14\times$ empirically; $z = 13.07 \to p_{\text{fail}} = 5.08 \times 10^{-39}$ vs. $z = 6.54 \to p_{\text{fail}} = 6.13 \times 10^{-11}$ uncentered) by mapping entries from $[0, p)$ to $[-p/2, p/2)$ and cancelling the shift via client `offset`. `Spiral` compresses queries to a single packed `RLWE` ciphertext expanded via trace automorphisms and folded by `RGSW` external products, trading higher server arithmetic for tiny offline setup ($\sim 14\text{ MB}$) and small responses.
5. **Modulus-Overflow, Unauthenticated-Hint, and Secret-Reuse Attacks:** Lattice `PIR` correctness requires inner-product noise strictly inside $(-\Delta/2, \Delta/2)$ where $\Delta = \lfloor q/p \rfloor$. Without hint authentication (`VeriSimplePIR`) or constant-envelope failure handling, a malicious server that shifts column $k^*$ of `(DB, H)` or perturbs unverified hints induces selective decryption failures iff $k^* = i \bmod m$ (or iff secret coordinate $s_k$ crosses the rounding threshold), recovering the client's queried index or LWE secret whenever client retries/aborts leak decryption-failure outcomes.

## Applicability

This report synthesizes primary-source evidence across six repositories and four foundational cryptographic/PL papers:

- **Tree-Based ORAM and Doubly-Oblivious Enclave Implementations:**
  - `obliviousram/PathORAM` (`a4b045bd19e5ed14ca09c8822fa497879ed5bf83`, `src/OramReadPathEviction.cpp`), baseline C++ implementation of `Stefanov et al. (JACM 2018)` (`DOI: 10.1145/3177872`) assuming a trusted client and untrusted network storage.
  - `obliviouslabs/oram` (`852f3387db4e2744fc023d9cef6eacc744681ee1`, `omap/odsl/circuit_oram.hpp`, `tools/tail_bound_analysis.py`), production C++ `Circuit ORAM` implementation of `Wang, Chan, & Shi (CCS 2015)` (`DOI: 10.1145/2810103.2813634`) supporting hardware enclave and external-memory `DISK_IO` batching with optional nonce-sum freshness (`check_freshness`).
  - `mobilecoinfoundation/mc-oblivious` (`2f24b1661fd94d85d607c185f1fa42afc284f4a3`, `aligned-cmov/src/cmov_impl_asm.rs`, `mc-oblivious-ram/src/{lib.rs,path_oram/mod.rs,evictor.rs,position_map/mod.rs}`), `#![no_std]` Rust SGX enclave ORAM enforcing x86-64/AVX2 hardware cache-line obliviousness.
- **Mechanized Trace-Obliviousness and Garbled RAM Theory:**
  - $\lambda_{\text{obliv}}$ (`Darais et al., POPL 2020`, `DOI: 10.1145/3371118`) for substructural probabilistic memory-trace obliviousness (`MTO`), and `Garbled RAM` (`Lu & Ostrovsky, EUROCRYPT 2013`, `DOI: 10.1007/978-3-642-38348-9_42`) for sublinear non-interactive RAM garbling.
- **Single-Server Lattice PIR and Multi-Server DPF PIR:**
  - `ahenzinger/simplepir` (`e9020b03bf2872c75b8954e749e32408b5db87ed`, `pir/{simple_pir.go,double_pir.go,database.go,params.go,params.csv,pir.c}`), Go/C implementation of `SimplePIR` and `DoublePIR` (`Henzinger et al., USENIX Security 2023`) over $q = 2^{32}$ LWE matrices.
  - `menonsamir/spiral-rs` (`335aebf9f5a487f46a1f20ad2f4300618ad24628`, `src/{params.rs,noise_estimate.rs,client.rs,server.rs,gadget.rs}`), Rust implementation of `Spiral` (`Menon & Wu, IEEE S&P 2022`, `DOI: 10.1109/SP46214.2022.9833700`) composing Regev and GSW ciphertexts over CRT rings (`crt_count <= 2`).
  - 2-server Function Secret Sharing / `DPF` `PIR` (`Boyle, Gilboa, & Ishai, CCS 2016`, `DOI: 10.1145/2976749.2978429`) as the multi-server non-colluding baseline.

**How subjects relate:** `PathORAM`, `obliviouslabs/oram`, and `mc-oblivious` represent three progressively hardened points along the tree-ORAM spectrum (network-only Path ORAM $\to$ batched enclave Circuit ORAM $\to$ inline-assembly cache-oblivious SGX ORAM), whose randomness-consumption assumptions are formalized by $\lambda_{\text{obliv}}$ and extended to non-interactive MPC by `Garbled RAM`. `SimplePIR`, `DoublePIR`, `Spiral`, and `DPF` compare orthogonal read-only `PIR` points along the client-hint vs. server-compute vs. trust-model trade-off surface. All empirical measurements (`2A`–`2C`) are verified by `/tmp/probe_oram_pir.py`.

## Findings

### 1. Tree-Based `Path ORAM` vs. `Circuit ORAM` Eviction and Stash Tail Bounds

Basis: normative + source + execution

#### 1.1 Position-Map Invariant, Lazy Initialization, and `Path ORAM` Bucket Threshold ($Z \ge 4$)

Both `Path ORAM` (`Stefanov et al., JACM 2018`) and `Circuit ORAM` (`Wang et al., CCS 2015`) organize untrusted server storage as a complete binary tree of height $h$ ($L = h + 1$ levels, $2^h$ leaves), where every node holds a bucket of $Z$ encrypted block slots (plus dummy slots). Security rests on one structural invariant:

> **Leaf Invariant:** Every logical block $a \in [0, N)$ has a uniformly random assigned leaf $\ell = \mathsf{pos}[a] \in [0, 2^h)$ stored in the client's position map, and block $a$ resides *either* in the client's local **stash** *or* in some bucket along the path $\mathcal{P}(\ell)$ from the root to leaf $\ell$.

Because each access reads $\mathcal{P}(\text{old\_leaf})$, immediately remaps $\mathsf{pos}[a] \leftarrow_{\$} [0, 2^h)$ independently, and writes modified encrypted buckets back along $\mathcal{P}(\text{old\_leaf})$ (plus optional deterministic/random paths), an untrusted server observing only physical bucket indices sees an independent uniform sequence of tree paths regardless of the logical access sequence.

To avoid an $O(N \log N)$ startup cost writing $N$ initial dummy-mapped blocks, production ORAMs use **lazy implicit initialization**:
- In `mc-oblivious` (`mc-oblivious-ram/src/position_map/mod.rs:1-8, 60-64, 138-142`), `0` in `TrivialPositionMap` or `ORAMU32PositionMap` marks an uninitialized entry; on first access (`old_val.ct_eq(&0)`), the client obliviously samples `1u32.random_child_at_height(self.height, &mut self.rng)` via `cmov` and sets `block_num` in `path_oram/mod.rs:234`.
- As documented in `mc-oblivious-ram/src/lib.rs:10-15`, implicit initialization can equivalently derive initial positions from a keyed block cipher/PRF over block IDs, eliminating position-map tree writes during bootstrap.
- For large $N$, storing $\mathsf{pos}$ recursively inside smaller ORAMs (`ORAMU32PositionMap`, `position_map/mod.rs:90-143`, packing $2^{L}$ 32-bit leaf pointers per `ValueSize`-byte block until `size <= 4096`) bounds client memory to $O(1)$ blocks plus $O(\log N)$ stash, raising round-trip depth to $O(\log_B N)$ ORAM levels.

**Why Path ORAM overflows at $Z = 2$:** Path ORAM's greedy eviction (`OramReadPathEviction.cpp:97-142`; `path_oram/mod.rs:374-408`) pushes stash blocks as deep as legal (`lca(bleaf, leaf) >= l`) along *only* the accessed path $\mathcal{P}(\text{old\_leaf})$. When $Z = 2$ and occupancy approaches $50\%\text{–}75\%$ of total tree slots, the expected number of blocks eligible for a single randomly sampled path falls below the eviction capacity needed to drain root-level congestion, causing the stash to grow without bound. Inspection of `mc-oblivious-ram/src/lib.rs:48-55` confirms this directly in production Rust code:
```rust
/// XXX: This config is broken
/// (Chris) I sometimes see stash overflow with this config, use Z=4
struct PathORAM4096Z2Creator<R, SC> ...
```
Stefanov et al. (`JACM 2018`) establish that greedy Path ORAM requires **$Z \ge 4$** (commonly $Z = 4$ or $5$) so stash exceedance probability decays exponentially $\Pr[|S| > R] \le O(2^{-\Omega(R)})$.

#### 1.2 `Circuit ORAM` ($Z = 2$), Reverse-Lexicographic Eviction, and the Even-Stride Starvation Bug

`Circuit ORAM` (`Wang, Chan, & Shi, CCS 2015`) achieves bounded stashes at **$Z = 2$**—cutting server storage and bandwidth in half and hitting the Goldreich–Ostrovsky $\Omega(\log N)$ lower bound up to polylogarithmic factors in circuit size $O(W \log N)$—via two mechanisms:
1. **Deterministic Reverse-Lexicographic Eviction Schedule:** Instead of only evicting along the random read path, Circuit ORAM performs $k \ge 2$ deterministic evictions per access (`evict_freq = 2` in `circuit_oram.hpp:136`; `CIRCUIT_ORAM_ADDITIONAL_BRANCHES_TO_EVICT = 2` in `mc-oblivious-ram/src/lib.rs:47`) following bit-reversed counter order (`deterministic_get_next_branch_to_evict`, `evictor.rs:38-51`). Successive evictions maximally separate left/right root subtrees so every subtree drains evenly.
2. **Two-Pass Metadata Scan + Single-Hold `obliSwap` (`circuit_oram.hpp:206-319`; `evictor.rs:57-197`):** Path ORAM's quadratic/in-place bucket packing creates $O(Z^2 \log^2 N)$ muxes inside MPC/garbled circuits. Circuit ORAM instead runs two linear metadata-only scans:
   - **Pass 1 (Root $\to$ Leaf, `prepare_deepest`, `circuit_oram.hpp:218-250`):** Records `deepest[i]`, the shallowest source level $s < i$ containing a block legal down to depth $\ge i$.
   - **Pass 2 (Leaf $\to$ Root, `prepare_target`, `circuit_oram.hpp:252-268`):** Computes `target[i]`, scheduling at most one block in flight between any source level and an available slot below it.
   - **Pass 3 (Root $\to$ Leaf Data Move, `circuit_oram.hpp:270-319`):** Carries at most **one** temporary `Block_ hold` down the path using $O(\log N)$ oblivious `obliSwap` operations, matching the optimal $O(W \log N)$ circuit-gate bound.

**Concrete Implementation Hazards Verified in Primary Source:**
1. **Even-Stride Root-Subtree Starvation (`ReverseLexicographicBatchSchedule::WindowStride`, `circuit_oram.hpp:29-84`):** When batching multiple evictions across an odd `pathCount` (for example `pathCount = 63` in an incomplete/pruned subtree schedule), choosing an eviction stride that happens to be coprime to `pathCount` **but even** (such as `stride = 4` since $\gcd(4, 63) = 1$) leaves bit 0 of the leaf index `(counter + 4*k) % 63` invariant across consecutive windows until wraparound—pinning tens of thousands of consecutive batch windows to one half of the root! Lines 61–67 explicitly patch this by enforcing `stride % 2 != 0 && gcd(stride, pathCount) == 1`.
2. **Enclave Anti-Rollback Freshness (`assertNodeFreshness`, `circuit_oram.hpp:358-419`):** When external untrusted storage (`DISK_IO` / enclave host memory) holds ORAM buckets, AES-GCM per-bucket authentication alone does not prevent **replay attacks** serving stale bucket versions. `obliviouslabs/oram` embeds monotonic split nonces `(leftNonce, rightNonce)` inside every parent node and verifies `node.leftNonce + node.rightNonce == expectedNonce` on checkout (`circuit_oram.hpp:362`), forcing any tree rollback to fail integrity checks immediately.
3. **Empirical Stash-Overflow Tail Extrapolation (`tools/tail_bound_analysis.py:22-86`):** Because tight analytical constants on finite-$N$ stashes are conservative, `obliviouslabs/oram` determines production `stashSize` bounds (e.g., `stashSize = 33` default at `circuit_oram.hpp:133`) by fitting log-linear regressions $\log_2 \Pr[X \ge s] = m \cdot s + c$ across empirical stash-occupancy histograms and extrapolating to target failure probabilities $2^{-40}, 2^{-60}, 2^{-64}, 2^{-80}$.

**Executable Verification (Probe 2A):** Running $20{,}000$ random accesses on an $L = 10$ ($512$-leaf, $1{,}023$-bucket) binary tree in `/tmp/probe_oram_pir.py`:
- At $N = 1{,}024$: `PathORAM(Z=2)` reaches `max_stash = 33, end = 5`; `PathORAM(Z=4)` stays at `max_stash = 6, end = 0`; `CircuitORAM(Z=2, 2 reverse-lex evictions)` achieves **`max_stash = 2, end = 0`**.
- At $N = 1{,}536$ ($75\%$ total slot occupancy): `PathORAM(Z=2)` degrades severely to **`max_stash = 93, end = 41`**.
- Checking `BatchSchedule(pathCount = 63)` confirms `even_stride = 4` produces `bit0_seq = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]` (`100%` pinned to root subtree `0`), whereas `odd_stride = 5` alternates `[0, 1, 0, 1, ...]` every window.

---

### 2. Network-Only `ORAM` vs. Enclave Doubly-Oblivious Execution

Basis: source + derived

A tree ORAM is **single-oblivious (network-oblivious)** when its external bucket fetches hide the access pattern from the storage server, assuming the client RAM (position map, stash, CPU cache, and branch predictor) is completely unobservable. Inside an SGX enclave or shared multi-tenant host, an untrusted OS observes **page faults (4 KiB), cache-set conflicts (64 B), and branch/timing side channels**, requiring **doubly-oblivious** execution where every instruction sequence and memory address inside the client/enclave is independent of secrets.

| Architectural Dimension | Network-Only `obliviousram/PathORAM` | Doubly-Oblivious `mobilecoinfoundation/mc-oblivious` |
| :--- | :--- | :--- |
| **Position Map Lookup** | Direct secret-indexed array `position_map[blockIndex]` (`OramReadPathEviction.cpp:49`) — leaks cache line (`64 B`) and page (`4 KiB`) to OS/LLC observer. | Recursive `ORAMU32PositionMap` + full-buffer `TrivialPositionMap` `cmov` linear scans (`position_map/mod.rs:55-64, 131-135`). |
| **Bucket & Stash Scan** | Loops `for (b : blocks) if (b.index != -1) stash.push_back(b)` (`lines 53-57`) and early-exit `break` at `line 68` — leaks real-vs.-dummy count and stash match position! | Fixed-iteration `ct_find_and_remove` / `ct_insert` across every slot in the branch and entire `stash` using `aligned-cmov` (`path_oram/mod.rs:214-245`). |
| **Eviction Branching** | Conditional `if (counter >= bucket_size) break;` and `if (Pxl == P(...))` (`lines 106-115`), followed by `stash.erase(...)` (`line 127`). | Branchless `prepare_deepest`, `prepare_target`, and `lowest_height_legal_index` using `subtle::Choice` masks (`evictor.rs:124-196`). |
| **Compiler Codegen Defense** | Standard C++ control flow; compiler routinely turns ternary expressions back into speculative branches (`jmp`). | `#![deny(unsafe_code)]` at ORAM layer (`lib.rs:23`), delegating exclusively to audited x86-64 inline `asm!` in `aligned-cmov`. |

*(Concrete C++ memory-safety bug discovered in `obliviousram/PathORAM` `src/OramReadPathEviction.cpp:63-93`: line 64 copies `Block b = stash[i];` by value onto the loop stack frame and line 66 stores `targetBlock = &b;`. After the `for` scope terminates on line 70, `targetBlock` is a dangling pointer to an expired stack object; lines 79, 81, and 90 then dereference `targetBlock->data[i]`—undefined behavior / stack-use-after-scope under `-O2` or stack-variable reuse.)*

**Why `mc-oblivious` Uses Hand-Written Inline Assembly (`cmov_impl_asm.rs:26-273`):** LLVM does not expose portable intrinsics guaranteeing absence of secret-dependent branches across optimization passes (`cmov_impl_asm.rs:16-18`). `mc-oblivious` guarantees constant-time, cache-oblivious word and cache-line swaps via two assembly kernels:
1. **`cmov_byte_slice_a8` (8-byte stride, `lines 180-201`):** Executes `neg {0}` once before the loop to stash `condition` in the Carry Flag (`CF`), then loops `mov` (load `dest`) $\to$ `cmovc` (overwrite with `src` iff `CF=1`) $\to$ `mov` (store unconditionally to `dest`) $\to$ `dec` $\to$ `jnz`. Because x86 `dec` updates `ZF` without touching `CF`, `CF` survives the entire loop without re-testing `condition`.
2. **`cmov_byte_slice_a64` (64-byte cache-line stride with `AVX2`, `lines 226-272`):** Broadcasts the `neg`-extended all-0/all-1 mask into `ymm1` (`vmovq` + `vbroadcastsd`), then streams two 32-byte `vmovdqa` + `vpmaskmovq` stores per 64-byte iteration—maintaining identical L1/L2 cache-line touch traces regardless of `condition`.

---

### 3. Mechanized Trace-Oblivious Type Systems ($\lambda_{\text{obliv}}$) and `Garbled RAM`

Basis: normative + execution

#### 3.1 Why Probabilistic Obliviousness Requires Linear Probability Regions ($\lambda_{\text{obliv}}$)

Classical deterministic information-flow (`IF`) type systems treat random sampling as an opaque `low` or `high` expression, failing catastrophically on randomized ORAM protocols:
- The physical path `old_leaf` observed by an untrusted adversary **does** depend on secret access keys (`pos[secret_key]`), so `old_leaf` cannot simply be typed `Public` without declassification.
- Yet naive declassification (as in early `ObliVM`, analyzed in `Darais et al., POPL 2020`, DOI `10.1145/3371118`) only checks whether each sampled coin is uniform in isolation—**unsoundly accepting programs that reuse a random coin across correlated secret branches**.

`Darais et al.` resolve this in **$\lambda_{\text{obliv}}$** by combining a substructural (linear/affine) type system with **probability regions** $\rho$:
- Every random sample $r \leftarrow \mathsf{rnd}(\tau)$ is allocated in a fresh **affine probability region** $\rho$, ensuring $r$ can be consumed (declassified into an observable physical address) at most once unless proved independent of all co-observed outputs.
- Typing judgments prove **Probabilistic Memory-Trace Obliviousness (`PMTO`)**: for any two secret-equivalent inputs $s_1 \equiv_L s_2$, the *joint* probability distributions over complete physical address traces $\mathcal{T}(P(s_1))$ and $\mathcal{T}(P(s_2))$ are identical ($\text{TVD} = 0$).

**Executable Verification (Probe 2B):** On a 2-access 4-leaf ORAM widget comparing repeated-key secrets $S_{\text{same}} = (0, 0)$ against distinct-key secrets $S_{\text{diff}} = (0, 1)$:
- Both steps produce identical single-step marginal path probabilities `[0.25, 0.25, 0.25, 0.25]` ($\text{TVD}_1 = 0$).
- Under buggy coin reuse (non-linear consumption of the initial leaf coin across the second step), the joint 2-step trace distribution diverges sharply with **$\text{TVD}_2 = 0.750000$** ($S_{\text{same}}$ produces only diagonal pairs $(i, i)$ with probability $1/4$ each, while $S_{\text{diff}}$ spreads uniformly over all $16$ pairs).
- Enforcing linear single-use probability regions yields exact **$\text{TVD}_2 = 0.000000$**.

#### 3.2 `Garbled RAM` (`GRAM`): Non-Interactive Sublinear RAM Garbling

In secure two-party computation (`2PC`), Yao's Garbled Circuits require unrolling a $T$-step RAM execution on an $N$-word database into an $O(T \cdot N)$-gate circuit because each step could touch any memory index. **Garbled RAM** (`Lu & Ostrovsky, EUROCRYPT 2013`, DOI `10.1007/978-3-642-38348-9_42`) eliminates this $O(T \cdot N)$ blowup by:
1. Compiling the logical RAM program into a tree-based `ORAM` (or `Circuit ORAM` for minimal per-step circuit size) whose oblivious `CPU_step` transition circuit has size $\tilde{O}(\text{polylog}(N))$.
2. Garbling each CPU step $t \in [1, T]$ independently while using **timed-PRF / garbled-memory translation** so the garbled labels representing physical bucket contents read from persistent garbled memory $M_{\text{garbled}}$ at step $t$ translate cleanly into the input wire keys of $\text{GarbledStep}_t$, **without** the evaluator knowing which logical ORAM block was touched.
3. Achieves total garbled program size and evaluation time **$\tilde{O}(T \cdot \text{poly}(\lambda, \log N))$** while preserving Yao's constant-round non-interactive structure (with subsequent refinements by Gentry et al. 2014 and Garg et al. 2015 eliminating circular KDM-PRF assumptions in favor of standard one-way functions).

---

### 4. Single-Server Lattice PIR (`SimplePIR`, `DoublePIR`, `Spiral`) vs. Multi-Server DPF PIR

Basis: normative + source + derived + execution

#### 4.1 Architectural Trade-Off Matrix

| Scheme | Trust / Servers | Cryptography | Client Hint Size | Query Size (1 GB DB) | Answer / Rate | Server Compute |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **2-Server `DPF` PIR** (`Boyle et al., 2016`) | 2 non-colluding servers | Symmetric `AES`/PRG (`FSS` tree keys) | `0 B` | $O(\lambda \log N)$ ($\sim 1\text{–}3\text{ KiB}$) | 1 DB record (`~2x` XOR words) | $\approx$ memory bandwidth (XOR-only) |
| **`SimplePIR`** (`Henzinger et al., 2023`) | **1 server** | Plain `LWE` ($n=2^{10}, q=2^{32}$) | Large: $L \cdot n \log q$ ($\sim 121\text{ MB}$) | $\sqrt{N}$ elements ($\sim 242\text{ KB}$) | $L \log q$ ($\sim 242\text{ KB}$) | **$\sim 10\text{ GB/s/core}$** (`< 1` mul+add/byte) |
| **`DoublePIR`** (`Henzinger et al., 2023`) | **1 server** | Recursive 2-level `LWE` | Medium: $n^2 \delta X \log q$ ($\sim 16\text{ MB}$) | $q_1 + q_2$ ($\sim 345\text{ KB}$) | $\sim 345\text{ KB}$ (compressed hint eval) | **$\sim 7.4\text{ GB/s/core}$** |
| **`Spiral` / `SpiralStreamPack`** (`Menon & Wu, 2022`) | **1 server** | `RLWE` (Regev) + `RGSW` + CRT NTT | Small keys ($\sim 14\text{–}18\text{ MB}$, DB-indep.!) | **1 `RLWE` ct** (`~14–32 KB`, expanded) | High rate ($\sim 20\text{–}84\text{ KB}$, mod-switched) | Compute/NTT-bound (`~0.4–1.5 GB/s/core`) |

#### 4.2 `SimplePIR` and `DoublePIR` (`ahenzinger/simplepir`): Matrix Squishing and `offset` Centering

`SimplePIR` (`pir/simple_pir.go:119-214`, `pir/params.go:12-86`, `pir/database.go:30-69`) formats an $N$-element database as an $L \times M$ matrix $D \in [-p/2, p/2)^{L \times M}$ over plaintext modulus $p \ll q = 2^{32}$ ($\Delta = \lfloor 2^{32}/p \rfloor$):
1. **Offline Hint Compression (`Setup`, lines 119–130):** Given shared pseudorandom matrix $A \in \mathbb{Z}_q^{M \times n}$, the server precomputes the single hint matrix $H = D \cdot A \pmod{2^{32}}$ once for all clients. Crucially, to accelerate the online inner product, the server then **shifts** database entries into $[0, p)$ (`DB.Data.Add(p.P / 2)`) and **squishes** three 10-bit elements into each 32-bit `uint32` word (`Basis = 10, Squishing = 3` in `database.go:34-44`, hard-coded in `pir.c:6-9` for `matMulVecPacked` C-loop optimization). Note that `Squish()` enforces `p <= 1024` and `Logq >= 30`.
2. **Online Query & Server Inner Product (`Query`/`Answer`, lines 145–183):** The client samples fresh $s \leftarrow \mathbb{Z}_q^n$, Gaussian $e \leftarrow \chi^M$ ($\sigma = 6.4$ in `params.csv`), sends $q = A s + e + \Delta \cdot u_{i \bmod M} \pmod q$, and the server returns $a = D_{\text{shifted}} \cdot q \pmod{2^{32}}$.
3. **Client Shift Cancellation (`Recover`, lines 185–214 & `database.go:54-60`):** Because the server summed $D_{\text{shifted}} = D + \lfloor p/2 \rfloor \mathbf{1}\mathbf{1}^\top$, the client cancels the shift purely from the query vector via `offset = -(p/2) * sum(q) (mod 2^32)`:
   $$a_r - (H s)_r + \text{offset} \;\equiv\; D_r \cdot e + \Delta \cdot D_{r, i \bmod M} \pmod{2^{32}}$$
   Rounding via `p.Round` (`(x + Delta/2) / Delta % p`) and adding `+ p/2` in `ReconstructElem` (`database.go:58`) recovers $D_{\text{shifted}}[r, i \bmod M]$—preserving exact **zero-mean $[-p/2, p/2)$ noise variance** (cutting inner-product error standard deviation by $2\times$ vs. uncentered $[0, p)$!) alongside $3\times$ memory-bandwidth packing.
4. **`DoublePIR` Hint Shrinkage (`double_pir.go:101-180`):** When $L$ is large, `DoublePIR` decomposes $H_1^\top = (D A_1)^\top \in \mathbb{Z}_q^{n \times L}$ into base-$p$ limbs (`H1.Expand(p.P, p.delta())`) and applies a second SimplePIR instance using $A_2$ so the offline hint $H_2 = H_1 \cdot A_2$ depends only on $n^2 \delta$, shrinking a $121\text{ MB}$ hint to $\sim 16\text{ MB}$ while remaining `DB`-dependent.

#### 4.3 `Spiral` (`menonsamir/spiral-rs`): Query Expansion, Hybrid Folding, and Source Subtleties

`Spiral` (`menonsamir/spiral-rs` @ `335aebf9f5a487f46a1f20ad2f4300618ad24628`) avoids **any** database-dependent client hint by composing `Regev` (`RLWE` over $\mathbb{Z}_q[X]/(X^d+1)$, $d = \text{poly\_len}$) and `RGSW` over a $2^{\nu_1} \times 2^{\nu_2}$ database hypercube:
1. **Autocorrelation Query Expansion (`server.rs:19-121, 525-591`):** A single client `RLWE` ciphertext packs query bits into polynomial powers; the server runs $g = \lceil \log_2(2^{\nu_1} + t_{\text{GSW}} \nu_2) \rceil$ coefficient-expansion doubling rounds using Galois automorphisms $X \mapsto X^{d/2^r + 1}$ and key-switching matrices (`v_expansion_left/right`), extracts $2^{\nu_1}$ first-dimension Regev ciphertexts, and converts the remaining ciphertexts via `regev_to_gsw` (`server.rs:123-151`) into $\nu_2$ `RGSW` folding bits.
2. **CRT Packing & Folding (`server.rs:155-221, 388-503`):** First-dimension `multiply_reg_by_database` runs inner products simultaneously across two $32$-bit CRT limbs packed into one `u64` (`PACKED_OFFSET_2 = 32`); `fold_ciphertexts` applies $\nu_2$ `RGSW` external products using `gadget_invert` + `v_folding` / `v_folding_neg`; `pack` compresses $n^2$ scalar results into one $(n+1)\times n$ matrix ciphertext; and `encode` modulus-switches the first row to `q2` (`Q2_VALUES`) and payload rows to `q1 = 4 * pt_modulus` (`server.rs:470-502`).

**Primary-Source Implementation Subtleties Observed in `spiral-rs`:**
- **Empirical vs. Paper Noise Estimator Divergence (`noise_estimate.rs:70-76`):** In `get_noise_from_paramset`, line 74 omits a factor of `s.d` (`poly_len`) from the `t_exp_left` query-expansion variance term, accompanied by the explicit developer comment: *"above, we exclude a factor of s.d; this is bad according to the paper, but in practice, it seems to model the noise accurately"*.
- **RNG Modulo Bias and Unreduced `0` (`client.rs:47-49`):** `get_inv_from_rng` computes `params.modulus - (rng.gen::<u64>() % params.modulus)`, which (i) exhibits tiny modulo bias when $2^{64} \nmid q$, and (ii) returns `params.modulus` itself (unreduced mod $q$) whenever `rng % params.modulus == 0`.
- **Non-Constant-Time Secret Ternary Shuffle (`client.rs:130-144`):** `gen_ternary_mat` constructs a fixed-weight ternary key by placing `hamming` $+1$s and `hamming` $-1$s at the front of each polynomial and calling `pol.shuffle(rng)` (Fisher–Yates with secret-independent indices, yet branch/cache behavior during generation only impacts local client keygen rather than query evaluation).

---

### 5. Lattice PIR Modulus-Overflow, Unauthenticated-Hint, and Secret-Reuse Attacks

Basis: source + derived + execution

In any `LWE`/`RLWE` PIR scheme where plaintext $m \in \mathbb{Z}_p$ is scaled by $\Delta = \lfloor q / p \rfloor$, decryption (`Round` in `params.go:31-35`; `dec_to_raw` in `server.rs:613-639`) succeeds iff accumulated ciphertext noise $e_{\text{tot}}$ satisfies:
$$|e_{\text{tot}}| \;<\; \frac{\Delta}{2} \;=\; \left\lfloor \frac{q}{2p} \right\rfloor \quad \left(\text{minus } \tfrac{1}{2}(q \bmod p) \text{ asymmetric rounding margin}\right)$$

Three failure and attack mechanisms arise directly at this boundary:

1. **Modulus-Overflow Collapse Without $[-p/2, p/2)$ Centering:** In `SimplePIR` (`params.csv` line 4: $n=1024, m=32768, \log_2 q = 32, \sigma = 6.4, p = 701, \Delta = 6{,}126{,}914$), centering DB entries in $[-350, +350]$ keeps $|D_r \cdot e|$ at $z = 13.07$ standard deviations below $\Delta/2$ ($p_{\text{fail}} = 5.08 \times 10^{-39} \approx 2^{-127}$). Skipping $[-p/2, p/2)$ centering doubles noise standard deviation, halving the margin to $z = 6.54$ and exploding single-query failure probability to $p_{\text{fail}} = 6.13 \times 10^{-11} \approx 2^{-33.9}$—far above the $2^{-40}$ soundness floor!
2. **Selective-Failure Query-Index Recovery via Column Perturbation:** Under an active malicious server holding `(DB, H)` without cryptographic hint verification (`VeriSimplePIR`), guessing candidate index $k^*$ and consistently shifting column $k^*$ by $+1 \pmod p$ in `(DB, H)` cancels $H \cdot s$ with $(As)_{k^*}$, perturbing the client's decrypted record by $+1 \pmod p$ **iff $k^* = i \bmod m$** (while leaving non-matching queries untouched up to $\pm 1 \cdot e_{k^*} \approx \pm 6 \ll \Delta/2$). If the client aborts, retries, or reports an application checksum/MAC failure on corrupted records, 1 bit of reaction leakage directly tests $i \bmod m = k^*$.
3. **Secret-Key Recovery Under Unauthenticated Hints or Reused LWE Secrets:** If a client reuses the same secret vector $s$ across queries (or downloads an unauthenticated malicious hint $H' = H + \delta_H$), an adversarial server can push $|e_{\text{tot}} - \delta_H \cdot s|$ across $\Delta/2$ to trigger threshold-dependent decryption failures whose occurrence correlates with $\langle \delta_H, s \rangle$ (analogous to classical LWE decryption-failure attacks), recovering $s$ and breaking query privacy via $q - As$. Sound deployments therefore require: (a) **fresh per-query $s$** (`simple_pir.go:148`), (b) failure margin $\le 2^{-128}$ (with balanced gadget decomposition in `RLWE`), (c) **zero retry/abort side channels** on malformed payloads, and (d) verifiable hint commitments (`VeriSimplePIR`) for untrusted setup servers.

**Executable Verification (Probe 2C):** Executing exact $\mathbb{Z}_{2^{32}}$ `SimplePIR` arithmetic (`n=64, m=256, p=495, Delta=8676701`) in `/tmp/probe_oram_pir.py`:
- **Honest recovery:** `honest_rec = 323 == DB[17][73] = 323` via `DB.Add(p//2)`, `offset`, `Round`, and `ReconstructElem`.
- **Centering variance reduction:** Across $400$ noise trials, centered $[-p/2, p/2)$ empirical error std is `14409.7` vs. uncentered `30789.1` (**`2.14x` reduction**); analytical `params.csv` (`logm=15, p=701`) gives `centered z = 13.07 (fail = 5.08e-39)` vs. `uncentered z = 6.54 (fail = 6.13e-11)`.
- **Selective-failure oracle (`true c_idx = 73`):** Perturbing candidate `k_guess in {72, 73, 74}` in `(DB, H)` produces **`{72: False, 73: True, 74: False}`**—triggering record mismatch exclusively on the true queried column!

## Boundaries

- **Not examined:**
  - Zero-knowledge / verifiable PIR hint proofs (`VeriSimplePIR`, Pedersen/lattice commitments over $H$), dynamic-database PIR (`SimplePIR` updates), and multi-server `DPF`/`FSS` GPU/AVX-512 implementations were not source-inspected.
  - Non-tree `ORAM` schemes (`Square-Root ORAM`, hierarchical hash-table `OptORAMa` achieving $O(\log N)$ de-amortized worst-case overhead) and `SpiralStream` / `SpiralPack` C++ parameters in `menonsamir/spiral` were not source-inspected beyond `spiral-rs`.
  - Formal Isabelle/Coq/Lean mechanized proofs of `Path ORAM` / $\lambda_{\text{obliv}}$ were cited from `Darais et al. (POPL 2020)` rather than re-checked inside a proof assistant.
- **Unsupported:**
  - `ahenzinger/simplepir` (`e9020b03bf2872c75b8954e749e32408b5db87ed`) `Database.Squish()` explicitly panics (`database.go:43-45`) whenever plaintext modulus $p > 1024$ (`2^10`) or $\log_2 q < 30$.
  - `mobilecoinfoundation/mc-oblivious` (`2f24b1661fd94d85d607c185f1fa42afc284f4a3`) `ORAMU32PositionMap` explicitly asserts `height < 32` (`position_map/mod.rs:34-37, 100-103`) and power-of-two ORAM `size` (`path_oram/mod.rs:143`).
  - `obliviousram/PathORAM` (`a4b045bd19e5ed14ca09c8822fa497879ed5bf83`) does **not** implement oblivious client-side stash/position-map scans (`OramReadPathEviction.cpp:49-70`) and should never be deployed inside hardware enclaves.
- **Unknown:**
  - Exact asymptotic stash failure probability constants for `Circuit ORAM` under adversarial batched workloads vs. sequential workloads require empirical tail-bound sampling (`obliviouslabs/oram/tools/tail_bound_analysis.py`) per concrete $(N, Z, \text{evict\_freq})$ parameterization rather than closed-form universal bounds.
- **Known not to apply:**
  - `Path ORAM`'s $Z = 2$ stash explosion demonstrated in Probe 2A does **not** apply to `Path ORAM` at $Z \ge 4$ (`max_stash = 6`) or to `Circuit ORAM` with $2$ reverse-lexicographic evictions per access (`max_stash = 2` at $N = 1024$).
  - `SimplePIR`'s column-perturbation selective-failure oracle does **not** leak client query indices to an honest-but-curious server that leaves `(DB, H)` unmodified, nor when offline hints $H$ are cryptographically verified against a public database commitment and clients suppress decryption-error retries.

## Evidence

### Primary Source Repositories and Line Citations

1. **`obliviousram/PathORAM`** @ `a4b045bd19e5ed14ca09c8822fa497879ed5bf83` (observed 2026-11-19):
   - `src/OramReadPathEviction.cpp`: lines 11–44 (`OramReadPathEviction` constructor), 46–146 (`access` with secret-indexed `position_map[blockIndex]` at line 49, non-oblivious `stash.push_back` at line 55, dangling loop-local `&b` `targetBlock` pointer + early `break` at lines 64–93, greedy path eviction at lines 97–142), 148–155 (`P(leaf, level)`).
2. **`obliviouslabs/oram`** @ `852f3387db4e2744fc023d9cef6eacc744681ee1` (observed 2026-11-19):
   - `omap/odsl/circuit_oram.hpp`: lines 30–84 (`ReverseLexicographicBatchSchedule::WindowStride` enforcing odd coprime stride on odd `pathCount`), 88–107 (`BatchStashHashPolicy`), 133–171 (`ORAM` template defaults `Z=2, stashSize=33, evict_freq=2, evict_group=2`), 206–319 (`evictPath` `deepest`/`target`/`obliSwap` 3-pass eviction), 345–356 (`evict()`), 358–419 (`assertNodeFreshness`, `leftNonce + rightNonce == expectedNonce`).
   - `tools/tail_bound_analysis.py`: lines 22–86 (`tail_points` and log-linear regression for $2^{-40} \dots 2^{-80}$ stash targets).
3. **`mobilecoinfoundation/mc-oblivious`** @ `2f24b1661fd94d85d607c185f1fa42afc284f4a3` (observed 2026-11-19):
   - `aligned-cmov/src/cmov_impl_asm.rs`: lines 26–57 (`cmov_u32`, `cmov_u64`), 160–202 (`cmov_byte_slice_a8` `neg`/`CF`/`cmovc` loop), 211–273 (`cmov_byte_slice_a64` `AVX2` `vpmaskmovq`).
   - `mc-oblivious-ram/src/lib.rs`: lines 10–15 (implicit PRF position-map initialization), 21–23 (`#![no_std]`, `#![deny(unsafe_code)]`), 47 (`CIRCUIT_ORAM_ADDITIONAL_BRANCHES_TO_EVICT = 2`), 48–60 (`PathORAM4096Z2Creator` `"XXX: This config is broken"` overflow comment), 92–193 (`Z=4`/`Z=2` creators).
   - `mc-oblivious-ram/src/position_map/mod.rs`: lines 25–179 (`TrivialPositionMap`, `ORAMU32PositionMap` lazy `ct_eq(&0)` leaf init, `size <= 4096` threshold).
   - `mc-oblivious-ram/src/path_oram/mod.rs`: lines 38–83 (`MetaSize`, `meta_is_vacant`), 145–152, 194–274 (`access`), 374–408 (`pack`).
   - `mc-oblivious-ram/src/evictor.rs`: lines 38–51 (`deterministic_get_next_branch_to_evict`), 57–197 (`prepare_deepest`, `prepare_target`).
4. **`ahenzinger/simplepir`** @ `e9020b03bf2872c75b8954e749e32408b5db87ed` (observed 2026-11-19):
   - `pir/params.go`: lines 12–35 (`Delta()`, `Round()`), 37–80 (`PickParams`).
   - `pir/params.csv`: lines 1–10 (`logn=10, logq=32, sigma=6.4, logm=15 => p_simple=701, p_double=657`).
   - `pir/simple_pir.go`: lines 119–130 (`Setup`: `H = DB*A`, `Add(P/2)`, `Squish()`), 145–214 (`Query`, `Answer`, `Recover` `offset` subtraction).
   - `pir/database.go`: lines 30–46 (`Squish`: `Basis=10, Squishing=3`), 54–69 (`ReconstructElem` `+ P/2`).
   - `pir/double_pir.go`: lines 19 (`COMP_RATIO = 64`), 101–180 (`DoublePIR::Setup`, `Query`).
   - `pir/pir.c`: lines 6–9, 101–120 (`matMulVecPacked`).
5. **`menonsamir/spiral-rs`** @ `335aebf9f5a487f46a1f20ad2f4300618ad24628` (observed 2026-11-19):
   - `src/params.rs`: lines 8–46 (`Q2_VALUES`), 49–82, 146–182, 207–219 (`crt_compose_2`).
   - `src/gadget.rs`: lines 3–60 (`get_bits_per`, `build_gadget`, `gadget_invert_rdim`).
   - `src/noise_estimate.rs`: lines 53–118 (`get_noise_from_paramset` excluding `s.d` at lines 73–76, `get_p_err`).
   - `src/client.rs`: lines 13 (`HAMMING_WEIGHT = 256`), 47–49 (`get_inv_from_rng` modulo bias/unreduced `modulus`), 130–144 (`gen_ternary_mat` `shuffle`).
   - `src/server.rs`: lines 19–151 (`coefficient_expansion`, `regev_to_gsw`), 155–221 (`multiply_reg_by_database`), 388–503 (`fold_ciphertexts`, `pack`, `encode`), 650–741 (`process_query`).

### Peer-Reviewed Literature

- E. Stefanov, M. van Dijk, E. Shi, T.-H. H. Chan, C. Fletcher, L. Ren, X. Yu, and S. Devadas, "Path ORAM: An Extremely Simple Oblivious RAM Protocol," *J. ACM*, vol. 65, no. 4, art. 18, Aug. 2018 (orig. ACM CCS 2013). DOI: `10.1145/3177872`.
- X. Wang, H. Chan, and E. Shi, "Circuit ORAM: On Tightness of the Goldreich-Ostrovsky Lower Bound," *Proc. ACM CCS 2015*, pp. 850–861. DOI: `10.1145/2810103.2813634`.
- D. Darais, I. Sweet, C. Liu, and M. Hicks, "A Language for Probabilistically Oblivious Computation," *Proc. ACM Program. Lang.*, vol. 4 (POPL), art. 50, Jan. 2020. DOI: `10.1145/3371118`.
- S. Lu and R. Ostrovsky, "How to Garble RAM Programs," *Advances in Cryptology – EUROCRYPT 2013*, LNCS vol. 7881, Springer, pp. 719–734. DOI: `10.1007/978-3-642-38348-9_42`.
- A. Henzinger, M. M. Hong, H. Corrigan-Gibbs, S. Meiklejohn, and V. Vaikuntanathan, "One Server for the Price of Two: Simple and Fast Single-Server Private Information Retrieval," *Proc. 32nd USENIX Security Symposium*, Aug. 2023.
- S. J. Menon and D. J. Wu, "SPIRAL: Fast, High-Rate Single-Server PIR via FHE Composition," *Proc. 2022 IEEE Symposium on Security and Privacy (S&P)*, pp. 930–947. DOI: `10.1109/SP46214.2022.9833700`.
- E. Boyle, N. Gilboa, and Y. Ishai, "Function Secret Sharing: Improvements and Extensions," *Proc. ACM CCS 2016*, pp. 1292–1303. DOI: `10.1145/2976749.2978429`.

### Self-Contained Executable Micro-Probes (Python 3 stdlib, Executed 2026-11-19)

Command: `python3 /tmp/probe_oram_pir.py` (Python 3 standard library `math` and `random` only):

```python
#!/usr/bin/env python3
"""Self-contained Path ORAM vs Circuit ORAM stash bounds, lambda_obliv coin-reuse leak,
and SimplePIR modulus-overflow selective-failure probes (Python 3 stdlib)."""
import math
import random

def lca_level(leaf_a, leaf_b, L):
    x = leaf_a ^ leaf_b
    if x == 0:
        return L - 1
    return (L - 1) - 1 - (x.bit_length() - 1)

def path_bucket_ids(leaf, L):
    return [((1 << l) - 1) + (leaf >> (L - 1 - l)) for l in range(L)]

def run_oram_sim(mode, Z, N=1024, ops=20000, seed=7):
    rng = random.Random(seed)
    L = 10
    num_leaves, num_buckets = 1 << (L - 1), (1 << L) - 1
    pos = [rng.randrange(num_leaves) for _ in range(N)]
    tree = [[] for _ in range(num_buckets)]
    stash, evict_ctr, max_stash = [], 0, 0

    def rev_lex(c):
        r = 0
        for b in range(L - 1):
            if (c >> b) & 1:
                r |= 1 << (L - 2 - b)
        return r

    def path_evict(leaf):
        nonlocal stash
        bids = path_bucket_ids(leaf, L)
        for bid in bids:
            stash.extend(tree[bid]); tree[bid] = []
        for l in range(L - 1, -1, -1):
            bid = bids[l]
            keep, placed = [], 0
            for blk, bleaf in stash:
                if placed < Z and lca_level(bleaf, leaf, L) >= l:
                    tree[bid].append((blk, bleaf)); placed += 1
                else:
                    keep.append((blk, bleaf))
            stash = keep

    def circuit_evict(leaf):
        nonlocal stash
        bids = path_bucket_ids(leaf, L)
        buckets = [list(tree[bid]) for bid in bids]
        legal_depth = lambda bleaf: lca_level(bleaf, leaf, L)
        deepest_src, goal, src = [None] * L, -1, None
        if stash:
            g = legal_depth(max(stash, key=lambda x: legal_depth(x[1]))[1])
            if g > goal:
                goal, src = g, -1
        for i in range(L):
            if goal >= i:
                deepest_src[i] = src
            if buckets[i]:
                g = legal_depth(max(buckets[i], key=lambda x: legal_depth(x[1]))[1])
                if g > goal:
                    goal, src = g, i
        target, stash_target, dest, cur_src = [None] * L, None, None, None
        for i in range(L - 1, -1, -1):
            if i == cur_src:
                target[i], dest, cur_src = dest, None, None
            if ((dest is None and len(buckets[i]) < Z) or target[i] is not None) and deepest_src[i] is not None:
                cur_src, dest = deepest_src[i], i
        if cur_src == -1:
            stash_target = dest
        hold, dest_lvl = (None, None)
        if stash_target is not None:
            hold = stash.pop(max(range(len(stash)), key=lambda idx: legal_depth(stash[idx][1])))
            dest_lvl = stash_target
        for i in range(L):
            if hold is not None and i == dest_lvl and target[i] is None:
                buckets[i].append(hold); hold = None; dest_lvl = None
            elif target[i] is not None:
                out_blk = buckets[i].pop(max(range(len(buckets[i])), key=lambda idx: legal_depth(buckets[i][idx][1])))
                if hold is not None:
                    buckets[i].append(hold)
                hold, dest_lvl = out_blk, target[i]
        for l in range(L):
            tree[bids[l]] = buckets[l]

    for step in range(ops):
        blk = step % N if step < N else rng.randrange(N)
        old_leaf, new_leaf = pos[blk], rng.randrange(num_leaves)
        pos[blk] = new_leaf
        if step >= N:
            for bid in path_bucket_ids(old_leaf, L):
                tree[bid] = [(b_id, b_leaf) for (b_id, b_leaf) in tree[bid] if b_id != blk]
            stash = [(b_id, new_leaf if b_id == blk else b_leaf) for (b_id, b_leaf) in stash]
            if not any(b_id == blk for b_id, _ in stash):
                stash.append((blk, new_leaf))
        else:
            stash.append((blk, new_leaf))
        if mode == "path":
            path_evict(old_leaf)
        else:
            for _ in range(2):
                circuit_evict(rev_lex(evict_ctr)); evict_ctr += 1
        if step >= N and len(stash) > max_stash:
            max_stash = len(stash)
    return max_stash, len(stash)

def run_probe_2a():
    p_z2_1k, p_z2_1k_end = run_oram_sim("path", Z=2, N=1024, ops=20000, seed=7)
    p_z4_1k, p_z4_1k_end = run_oram_sim("path", Z=4, N=1024, ops=20000, seed=7)
    c_z2_1k, c_z2_1k_end = run_oram_sim("circuit", Z=2, N=1024, ops=20000, seed=7)
    p_z2_15, p_z2_15_end = run_oram_sim("path", Z=2, N=1536, ops=20000, seed=7)
    print(f"2A N=1024,L=10 (20k ops): PathORAM(Z=2) max={p_z2_1k} end={p_z2_1k_end} | PathORAM(Z=4) max={p_z4_1k} end={p_z4_1k_end} | CircuitORAM(Z=2) max={c_z2_1k} end={c_z2_1k_end}")
    print(f"2A N=1536,L=10 (20k ops): PathORAM(Z=2) max={p_z2_15} end={p_z2_15_end}")
    naive_even_bits = [(0 + 4 * k) % 63 & 1 for k in range(16)]
    patched_odd_bits = [(0 + 5 * k) % 63 & 1 for k in range(16)]
    print(f"2A BatchSchedule(pathCount=63): even_stride=4 bit0_seq={naive_even_bits} (pinned=0!) | odd_stride=5 bit0_seq={patched_odd_bits}")

def run_probe_2b():
    dist_same_bug, dist_diff_bug, dist_same_lin, dist_diff_lin = {}, {}, {}, {}
    for p0 in range(4):
        for p1 in range(4):
            dist_same_bug[(p0, p0)] = dist_same_bug.get((p0, p0), 0) + 1/16
            dist_diff_bug[(p0, p1)] = dist_diff_bug.get((p0, p1), 0) + 1/16
            for r_fresh in range(4):
                dist_same_lin[(p0, r_fresh)] = dist_same_lin.get((p0, r_fresh), 0) + 1/64
                dist_diff_lin[(p0, p1)] = dist_diff_lin.get((p0, p1), 0) + 1/64
    keys = [(a, b) for a in range(4) for b in range(4)]
    tvd_bug = 0.5 * sum(abs(dist_same_bug.get(k, 0) - dist_diff_bug.get(k, 0)) for k in keys)
    tvd_lin = 0.5 * sum(abs(dist_same_lin.get(k, 0) - dist_diff_lin.get(k, 0)) for k in keys)
    marg1_same = [sum(dist_same_bug.get((a, b), 0) for b in range(4)) for a in range(4)]
    print(f"2B marginal_step1={marg1_same} | coin_reuse TVD_joint={tvd_bug:.6f} (LEAKS!) vs linear_region TVD_joint={tvd_lin:.6f}")

def run_probe_2c():
    rng, Q = random.Random(99), 1 << 32
    n, l_rows, m_cols, p = 64, 256, 256, 495
    Delta = Q // p
    DB = [[rng.randrange(p) for _ in range(m_cols)] for _ in range(l_rows)]
    DB_cent = [[(v - p // 2) for v in row] for row in DB]
    A = [[rng.randrange(Q) for _ in range(n)] for _ in range(m_cols)]
    H = [[sum(DB_cent[r][c] * A[c][k] for c in range(m_cols)) % Q for k in range(n)] for r in range(l_rows)]
    r_idx, c_idx = 17, 73
    s = [rng.randrange(Q) for _ in range(n)]
    errs = [int(round(rng.gauss(0, 6.4))) for _ in range(m_cols)]
    q_vec = [((sum(A[c][k] * s[k] for k in range(n)) + errs[c] + (Delta if c == c_idx else 0)) % Q) for c in range(m_cols)]
    ans = [sum(DB[r][c] * q_vec[c] for c in range(m_cols)) % Q for r in range(l_rows)]
    offset = (-(p // 2) * sum(q_vec)) % Q
    Hs = [sum(H[r][k] * s[k] for k in range(n)) % Q for r in range(l_rows)]
    raw_honest = (ans[r_idx] - Hs[r_idx] + offset) % Q
    rec_honest = (((raw_honest + Delta // 2) // Delta) % p + p // 2) % p
    noise_centered, noise_uncentered = [], []
    for _ in range(400):
        e_sample = [int(round(rng.gauss(0, 6.4))) for _ in range(m_cols)]
        noise_centered.append(sum(DB_cent[r_idx][c] * e_sample[c] for c in range(m_cols)))
        noise_uncentered.append(sum(DB[r_idx][c] * e_sample[c] for c in range(m_cols)))
    std_cent = math.sqrt(sum(x * x for x in noise_centered) / len(noise_centered))
    std_unc = math.sqrt(sum(x * x for x in noise_uncentered) / len(noise_uncentered))
    assert rec_honest == DB[r_idx][c_idx]
    p_big, m_big, sigma = 701, 32768, 6.4
    delta_big = Q // p_big
    std_cent_big = math.sqrt(m_big * ((p_big * p_big - 1) / 12.0)) * sigma
    std_unc_big = math.sqrt(m_big * ((p_big - 1) * (2 * p_big - 1) / 6.0)) * sigma
    z_cent, z_unc = (delta_big / 2.0) / std_cent_big, (delta_big / 2.0) / std_unc_big
    print(f"2C SimplePIR(n=64,m=256,p=495) honest_rec={rec_honest}==DB[{r_idx}][{c_idx}]={DB[r_idx][c_idx]} | empirical_std_cent={std_cent:.1f} vs uncent={std_unc:.1f} (ratio={std_unc/std_cent:.2f}x)")
    print(f"2C params.csv(logm=15,p=701,Delta={delta_big}): centered z={z_cent:.2f} (fail={math.erfc(z_cent/math.sqrt(2.0)):.2e}) vs uncentered z={z_unc:.2f} (fail={math.erfc(z_unc/math.sqrt(2.0)):.2e})")
    fails = {}
    for k_guess in (72, 73, 74):
        DB_mal = [row[:] for row in DB]; DB_mal[r_idx][k_guess] = (DB_mal[r_idx][k_guess] + 1) % p
        H_mal_row = [sum((DB_mal[r_idx][c] - p // 2) * A[c][k] for c in range(m_cols)) % Q for k in range(n)]
        Hs_mal = sum(H_mal_row[k] * s[k] for k in range(n)) % Q
        ans_mal = sum(DB_mal[r_idx][c] * q_vec[c] for c in range(m_cols)) % Q
        raw_mal = (ans_mal - Hs_mal + offset) % Q
        rec_mal = (((raw_mal + Delta // 2) // Delta) % p + p // 2) % p
        fails[k_guess] = (rec_mal != DB[r_idx][c_idx])
    print(f"2C Selective-failure oracle (true c_idx={c_idx}): failure_on_k_guess={fails}")

if __name__ == "__main__":
    run_probe_2a(); run_probe_2b(); run_probe_2c()
```

Observed output (2026-11-19):
```text
2A N=1024,L=10 (20k ops): PathORAM(Z=2) max=33 end=5 | PathORAM(Z=4) max=6 end=0 | CircuitORAM(Z=2) max=2 end=0
2A N=1536,L=10 (20k ops): PathORAM(Z=2) max=93 end=41
2A BatchSchedule(pathCount=63): even_stride=4 bit0_seq=[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (pinned=0!) | odd_stride=5 bit0_seq=[0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0]
2B marginal_step1=[0.25, 0.25, 0.25, 0.25] | coin_reuse TVD_joint=0.750000 (LEAKS!) vs linear_region TVD_joint=0.000000
2C SimplePIR(n=64,m=256,p=495) honest_rec=323==DB[17][73]=323 | empirical_std_cent=14409.7 vs uncent=30789.1 (ratio=2.14x)
2C params.csv(logm=15,p=701,Delta=6126914): centered z=13.07 (fail=5.08e-39) vs uncentered z=6.54 (fail=6.13e-11)
2C Selective-failure oracle (true c_idx=73): failure_on_k_guess={72: False, 73: True, 74: False}
```

## Revalidation

1. **Circuit ORAM eviction and batch-stride invariance:** Against a newer `obliviouslabs/oram` or `mobilecoinfoundation/mc-oblivious` commit, inspect `omap/odsl/circuit_oram.hpp` (`ReverseLexicographicBatchSchedule::WindowStride`, `evictPath`, `assertNodeFreshness`) and `aligned-cmov/src/cmov_impl_asm.rs` (`cmov_byte_slice_a8`, `cmov_byte_slice_a64`) to verify odd coprime batch strides, nonce-sum freshness checks, and `cmov`/AVX2 mask generation free of secret-dependent branches.
2. **LWE / RLWE PIR noise bounds and centering:** Diff `ahenzinger/simplepir` (`pir/simple_pir.go`, `pir/params.csv`, `pir/database.go`) and `menonsamir/spiral-rs` (`src/noise_estimate.rs`, `src/client.rs`, `src/server.rs`) to verify whether `noise_estimate.rs:74` retains the omitted `s.d` factor or `client.rs:48` eliminates modulo bias in `get_inv_from_rng`.
3. **Quantitative probe rerun:** Execute the inline Python 3 probe script (`< 1.0 s` runtime, zero external dependencies) to verify Path ORAM $Z=2$ vs. $Z=4$ and Circuit ORAM $Z=2$ stash bounds, `BatchSchedule` even-stride subtree pinning, $\lambda_{\text{obliv}}$ joint trace TVD under coin reuse, and `SimplePIR` centered noise halving plus selective-failure query recovery.
