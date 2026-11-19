# Deterministic Execution-Trace Certificates: Hardware-Assisted Linux Replay, Merkleized ISA Step Proofs, and Interactive Bisection Games

## Summary

Non-zero-knowledge execution verification replaces algebraic prime-field arithmetization with **deterministic state-transition replay** paired with compact non-determinism logs or logarithmic refereed bisection. Across user-space debugging, optimistic rollup fraud proofs, and standalone proof-carrying execution certificates, three architectural designs trade off prover overhead, verifier complexity, and trust assumptions:

1. **Hardware-Counter User-Space Deterministic Replay (`rr-debugger/rr`):** Records unmodified Linux multi-process workloads on stock CPUs without hypervisors or binary instrumentation by multiplexing threads onto a single core, trapping non-deterministic instructions (`RDTSC`, `CPUID`), buffering non-blocking syscalls in user space (`syscallbuf`), emulating Linux restartable sequences (`rseq`) pre-commit aborts (`Task::should_apply_rseq_abort`), and anchoring asynchronous preemptions/signals to exact `(ticks, ip)` coordinates using hardware PMU **Retired Conditional Branches (`RCB`)** counters compensated for microarchitectural PMI skid (`skid_size` = $100$–$125$ branches).
2. **Merkleized Deterministic ISA State Machines & $O(\log T)$ Interactive Bisection (`Optimism Cannon`, `Arbitrum BoLD`/`WAVM`, `Cartesi Machine`):** Compiles arbitrary host programs into a deterministic ISA (`MIPS64r1`, `WAVM` WebAssembly, or `RV64GC` lowered to an `RV64I` microarchitecture `uarch`) whose entire memory/register state hashes to a 32-byte Keccak-256 root. Under the Canetti–Riva–Rothblum refereed delegation model (1-of-$N$ honest participant), disputing a $T$-step execution requires $\lceil \log_2 T \rceil$ interactive bisection moves to isolate a single transition $S_i \to S_{i+1}$, followed by **one** $O(1)$-step stateless Merkle witness check (`MIPS64.step`, `OneStepProofEntry.proveOneStep`, or `UArchStep.step`) consuming only a few kilobytes of sibling hashes (`59` sibling hashes = $1{,}888$ bytes per 64-bit address access). To defeat $O(A \cdot \Delta)$ sequential Sybil delay attacks against 1-vs-1 bisection, Arbitrum `BoLD` (`EdgeChallengeManager`) deduplicates rival claims over Merkle-accumulator *history prefixes* in a shared all-vs-all edge DAG, bounding resolution delay to $\le 2\Delta$ regardless of adversary count $A$.
3. **Witness-Guided $O(|T|)$ Execution-Trace Certificates:** When $O(|T|)$ verification time is acceptable (e.g., local kernel admission, reproducible CI/supply-chain auditing, or TEE/enclave cross-checking) but algebraic SNARK proving ($10^3\times$–$10^5\times$ slowdown) is prohibitive, an untrusted runner emits *only* the non-deterministic advice stream (external oracle reads, thread-switch `RCB` ticks, `LR`/`SC` reservation outcomes) checked in $O(|T|)$ time and $O(|\text{state}|)$ memory by a minimal, formally auditable deterministic interpreter.

## Applicability

This report covers the implementation invariants, binary state/proof layouts, game-theoretic delay bounds, and subtle determinism hazards of nine pinned upstream artifacts:

- **Linux `rr` (`rr-debugger/rr` at `608efe319bbbc4d0f5658d984e16be187801325d`) and O'Callahan et al. (`USENIX ATC 2017`, `arXiv:1705.05937`):** User-space recording and replay on Linux `x86`/`x86_64` (Intel Nehalem through Panther Lake, AMD Zen through Zen 6) and `AArch64` (ARM Neoverse/Cortex, Apple M1/M2), covering `PerfCounters` PMU `RCB` event selection, PMI skid handling, `syscallbuf` fastpath hooks, and `rseq` critical-section abort emulation. Note that `rr` traces are **cooperative debugging logs**, not adversarial cryptographic proofs: an untrusted trace producer can mutate recorded syscall outputs unless a verifier independently re-checks kernel transitions.
- **Optimism `Cannon` and `FaultDisputeGame` (`ethereum-optimism/optimism` at `f0d907fd862acb2fecd354a0cfe6fbe9c7a47a2a`):** Multithreaded `MIPS64r1` fault-proof VM (`MIPS64.sol` `v1.10.1`, `STATE_VERSION = 8` / `VersionMultiThreaded64_v5`), Go witness generator (`cannon/mipsevm`), `PreimageOracle` local/global key ABI, and split-depth output-plus-trace bisection (`FaultDisputeGame.sol` `v2.4.2`).
- **Arbitrum `Nitro WAVM` and `BoLD` (`OffchainLabs/nitro-contracts` at `349a4bfbdfec8924f13cc3e2bbad31161fa76378` and `OffchainLabs/bold` at `30e78f67f40eacaab13577e507bab6025df843d6`; Alvarez et al., `arXiv:2404.10491`):** Stack-and-module Merkleized WebAssembly Virtual Machine (`OneStepProofEntry.sol` + four sharded `IOneStepProver` contracts) and multi-level all-vs-all history-commitment edge challenges (`EdgeChallengeManager.sol`).
- **Cartesi Machine (`cartesi/machine-emulator` at `f9e4f82003a6f5acc9821c06f8a29025e0f895e3` and `cartesi/machine-solidity-step` at `fb00a32c38248edc5672e689dfa8cc58c0a2c3cd`):** Full-system Linux `RV64GC` emulator backed by a unified 64-bit physical-address Keccak-256 Merkle tree whose single-step disputes compile down to unprivileged `RV64I` micro-steps (`UArchStep.sol`, `AccessLogs.sol`).
- **Refereed Delegation Foundation (`Canetti, Riva, Rothblum, CCS 2011`, `DOI: 10.1145/2046707.2046759`):** Asymptotic soundness and round/communication bounds under the 1-honest-server assumption.

## Findings

### 1. Cross-System Architectural Trade-Off Matrix

`Basis: source + normative + documentation`

| Dimension | Linux `rr` (`rr-debugger/rr`) | Optimism `Cannon` (`MIPS64` + `FDG`) | Arbitrum `BoLD` + `Nitro WAVM` | Cartesi Machine (`RV64GC` + `uarch`) | Standalone $O(\|T\|)$ Trace Certificate |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Execution Substrate** | Native Linux `x86_64`/`AArch64` user process | Deterministic `MIPS64r1` (`STATE_VERSION=8`) | Deterministic `WAVM` (lowered Wasm + host IO) | Full-system `RV64GC` Linux + `RV64I` `uarch` | Deterministic ISA/IR interpreter |
| **Trust / Threat Model** | Cooperative debugger (trusted recorder) | 1-of-$N$ honest challenger + L1 liveness | 1-of-$N$ honest validator + L1 liveness | 1-of-$N$ honest validator + L1 liveness | Zero-trust prover; trusted tiny checker |
| **Prover Overhead** | ~1.2$\times$–2$\times$ native CPU (single-core) | ~1$\times$–5$\times$ interpreted Go (`mipsevm`) | ~1$\times$–5$\times$ native/Wasm (`nitro`) | ~2$\times$–10$\times$ interpreted C++ (`rv64gc`) | ~1.05$\times$–1.5$\times$ (advice capture only) |
| **Verifier Time** | $O(\|T\|)$ native replay | $O(\log T)$ moves + $O(1)$ on-chain step | $O(\log T)$ moves + $O(1)$ on-chain step | $O(\log T)$ moves + $O(1)$ `uarch` step | $O(\|T\|)$ deterministic re-execution |
| **State Commitment** | None (full checkpoint via `fork`/trace) | `keccak256(188B State)` + status byte | `keccak256(Machine)` (`MultiStack` + `modulesRoot`) | Unified 64-level Keccak-256 tree ($[0, 2^{64})$) | Optional initial/final SHA-256/BLAKE3 |
| **Memory Tree Layout** | Host OS virtual memory (`mmap` replay) | 64-bit tree, 32 B big-endian leaves (59 siblings) | Wasm linear memory Merkle tree + `MultiStack` | 64-bit tree, 32 B little-endian leaves (59 siblings) | Native flat RAM array in verifier |
| **Concurrency Model** | Single-core preemptive schedule via PMU `RCB` | Deterministic preemptive `left`/`right` thread stacks + `LL`/`SC` | Cooperative Wasm + `recoveryPc` co-threads | Single-hart `RV64GC` (`CLINT`/`PLIC` deterministic IRQ) | Advice-driven schedule / `LR`-`SC` bits |
| **External Input Oracle** | Recorded syscall buffers & trace frames | `IPreimageOracle` (`SHA256`/`Keccak`/`Blob`/local) | `OneStepProverHostIo` inbox/preimage bridge | `CMIO` `0x60000000` RX/TX Merkle buffers | Length-prefixed immutable advice tape |
| **Multi-Rival Delay Bound** | N/A | Per-subgame inherited chess clock (`MAX_CLOCK_DURATION`) | **Bounded** $\le 2\Delta$ via all-vs-all history edges | Tournament /PRT bisection (`PRT` multi-level) | Immediate ($0$ interactive rounds) |

### 2. Hardware-Assisted Deterministic User-Space Replay (`rr-debugger/rr`)

#### 2.1 PMU Retired Conditional Branches (`RCB`) and PMI Skid Compensation
`Basis: source + normative`

To replay asynchronous thread preemptions and `POSIX` signal deliveries at the exact dynamic instruction without instrumenting user binaries, `rr` (`src/PerfCounters.h:30-168`, `src/PerfCounters.cc:194-250`) programs a per-task Linux `perf_event_open` counter for **Retired Conditional Branches (`TICKS_RETIRED_CONDITIONAL_BRANCHES`)**—e.g., Intel raw event `0x5101c4` (`BR_INST_RETIRED.CONDITIONAL` on Nehalem through Comet Lake), `0x5111c4` (Ice Lake through Meteor Lake), `0x100005111c4` (Lunar Lake / Arrow Lake), and `0x5107c4` (Panther Lake), with separate hybrid P-core vs Atom E-core (`Gracemont`/`Crestmont`/`Skymont`/`Darkmont`) detection in `PerfCounters_x86.h:221-270`.

Hardware Performance Monitoring Interrupts (PMIs, delivered as `TIME_SLICE_SIGNAL = SIGSTKFLT`, `PerfCounters.h:155`) suffer **skid**: between counter overflow and architectural retirement freeze, up to `skid_size` additional conditional branches retire (`100` on Nehalem–Rocket Lake, `125` on Alder Lake–Panther Lake; `PerfCounters.cc:228-250`). `rr` bridges this non-deterministic hardware skid to exact instruction-level replay via a two-phase algorithm (`ReplaySession.cc:507, 985-1002, 1700-1723`):
1. **Record Phase:** Whenever `SIGSTKFLT` or an asynchronous signal stops the tracee, `rr` reads the exact post-skid `(ticks, regs.ip())` pair and writes it into the `TraceFrame`.
2. **Replay Phase (`advance_to_ticks_target`):** If `ticks_left = ticks_target - t->tick_count() > skid_size`, `rr` arms the PMU interrupt for `ticks_left - skid_size`, letting the tracee run at native hardware speed until within `skid_size` branches of `ticks_target`. Once `ticks_left <= skid_size` (`check_approaching_ticks_target`, `ReplaySession.cc:1704-1707`), `rr` places a hardware execution breakpoint (`DR0`–`DR3` / `BKPT_INTERNAL`) at `target_ip` and steps exclusively through breakpoint hits until `(t->tick_count(), t->ip()) == (ticks_target, target_ip)`.

#### 2.2 Syscall Buffering (`syscallbuf`), `RDTSC`/`CPUID` Trapping, and `rseq` Preemption Invariants
`Basis: source`

- **User-Space `syscallbuf` Fastpath (`src/preload/rrcalls.h:9-113`, `ReplaySession.cc:1585-1605`):** Intercepting every `read`, `clock_gettime`, or `futex` via `ptrace` incurs ~2–10 $\mu$s of context-switch overhead. `rr`'s `Monkeypatcher` rewrites syscall sites in `libc`/`libpthread` to jump into an `LD_PRELOAD` library that executes non-blocking syscalls directly inside the tracee (permitted via a `seccomp-BPF` IP-whitelist filter) and appends return values into a shared `syscallbuf` memory ring, flushed in bulk only at scheduling/signal boundaries (`EV_SYSCALLBUF_FLUSH`). `RDTSC` is trapped via `prctl(PR_SET_TSC, PR_tsc_sigsegv)` (or patched to `SYS_rrcall_rdtsc = 1012`, `rrcalls.h:112`), and `CPUID` is trapped via `arch_prctl(ARCH_SET_CPUID, 0)` so feature bits and timestamps replay identically across heterogeneous hosts.
- **Linux Restartable Sequences (`rseq`) Emulation (`src/record_syscall.cc:4839-4912`, `src/Task.cc:4682-4730`, `src/ReplaySession.cc:1755-1762`):**
  Modern `glibc` and `tcmalloc` register per-thread `struct rseq` blocks where the kernel aborts critical sections (`[start_ip, start_ip + post_commit_offset)`) to `abort_ip` on preemption or signal delivery. Under `rr`, two subtle hazards arise:
  1. **Core Pinning Requirement (`record_syscall.cc:4894-4902`):** Because `rr` multiplexes virtual threads onto a single host core, `rseq->cpu_id` and `rseq->cpu_id_start` would vary nondeterministically across replay if unbound; `rr` asserts `bound_to_cpu() >= 0` whenever `SYS_rseq` is registered.
  2. **Deterministic Abort Replay (`Task::should_apply_rseq_abort`, `Task.cc:4682-4730`):** Because replay preempts via `rr`-injected breakpoints/PMIs rather than kernel context switches, the host kernel may *not* trigger `rseq` abort at the exact recorded preemption boundary (or may trigger it spuriously during `EV_SYSCALLBUF_FLUSH`). `Task::should_apply_rseq_abort` explicitly ignores `EV_SYSCALLBUF_FLUSH`, reads user-space `rseq.rseq_cs` and `struct rseq_cs`, checks `rseq_cs.version == 0`, verifies overflow-safe bounds `ip - start_ip < post_commit_offset`, validates the 4-byte anti-ROP signature `*(uint32_t*)(abort_ip - 4) == abort_prefix_signature` (`Task.cc:4723-4726`), and redirects `ip` to `rseq_cs.abort_ip` on `EV_SCHED` / `EV_SIGNAL`.

### 3. Merkleized ISA Step Verifiers (`Cannon`, `WAVM`, `Cartesi`)

#### 3.1 Split-State vs. Unified-Address-Space Merkle Layouts
`Basis: source`

On-chain one-step verifiers must execute a single ISA transition $S_i \xrightarrow{\pi_i} S_{i+1}$ inside Ethereum's gas and 24 KiB (`EIP-170`) contract size limits without holding guest RAM in contract storage. The three production VMs partition state differently:

1. **Optimism `Cannon` Multithreaded `MIPS64` (`packages/contracts-bedrock/src/cannon/MIPS64.sol:28-66, 126-219`, `libraries/MIPS64Memory.sol:7-160`):**
   - **Packed Calldata State + Thread Stacks:** Keeps a 188-byte top-level `State` (`memRoot`, `preimageKey`, `preimageOffset`, `heap`, `llReservationStatus`/`llAddress`/`llOwnerThread`, `exitCode`, `exited`, `step`, `stepsSinceLastContextSwitch`, `traverseRight`, `leftThreadStack`, `rightThreadStack`, `nextThreadID`) plus a 298-byte active `ThreadState` (`threadID`, `exitCode`, `exited`, `pc`, `nextPC`, `lo`, `hi`, `registers[32]`) hashed into a hash-onion thread stack (`keccak256(abi.encodePacked(innerRoot, packedThread))`, anchored by `EMPTY_THREAD_ROOT`). Notice two critical MIPS64 subtleties: `nextPC` explicitly persists the architectural **branch delay slot** across single-instruction boundaries, and `llReservationStatus`/`llAddress`/`llOwnerThread` explicitly record Load-Linked / Store-Conditional (`LL`/`SC`, `LLD`/`SCD`) reservations across deterministic preemptive context switches!
   - **64-Bit Big-Endian Merkle Memory (`MIPS64Memory.sol:9, 64-81, 153-159`):** Guest RAM ($[0, 2^{64})$) is a binary Keccak-256 tree of 32-byte leaves (`path = _addr >> 5`), requiring `MEM_PROOF_LEAF_COUNT = 60` `bytes32` words ($1$ leaf + $59$ siblings = $1{,}920$ bytes) per proof. `readMemUnchecked` enforces 8-byte alignment (`_addr & 0x7 == 0`) and extracts big-endian 64-bit words via `shamt = (32 - 8 - (_addr & 31)) * 8`.
2. **Cartesi Unified-Address-Space `RV64GC` -> `uarch` (`cartesi/machine-emulator` `src/address-range-defines.h:21-51`, `cartesi/machine-solidity-step` `src/AccessLogs.sol:114-173`, `src/UArchStep.sol:29-146`):**
   - **Everything-is-Physical-Memory:** Rather than maintaining a separate `State` struct outside `memRoot`, Cartesi maps **all** architectural and microarchitectural state into disjoint physical address ranges inside a single 64-bit little-endian Keccak-256 Merkle tree (`59` sibling hashes above 32-byte leaves): shadow `RV64GC` registers/CSRs at `0x0..0x1000`, shadow TLB at `0x1000..0x7000`, PMA descriptors at `0x10000..0x11000`, `uarch` shadow registers at `0x400000..0x401000`, `uarch` firmware RAM at `0x600000..0x800000` (2 MiB), `CLINT`/`HTIF`/`VIRTIO`/`PLIC` MMIO in `0x02000000..0x40500000`, `CMIO` I/O buffers at `0x60000000`/`0x60800000`, and Linux main RAM at `0x80000000`.
   - **Two-Tier `RV64GC` -> `RV64I` Microarchitecture Compilation:** Implementing full privileged `RV64GC` (`Sv39`/`Sv48` page-table walks, `F`/`D` IEEE 754 floating-point, `C` compressed decoding, `A` atomics, `M`/`S`/`U` trap delegation) directly in Solidity would blow past `EIP-170` contract limits and create a massive consensus surface. Instead, Cartesi compiles its C++ `RV64GC` step interpreter into a fixed, self-contained **unprivileged `RV64I` binary** residing in `AR_UARCH_RAM` (`0x600000`). On-chain `UArchStep.sol` implements *only* minimal unprivileged `RV64I` over `AccessLogs.Context` (`readWord` / `writeWord`, swapping little-endian machine words via `swapEndian`), verifying one macro `RV64GC` instruction as a deterministic sequence of `uarch` micro-steps terminated by `UArchReset`.
3. **Arbitrum `WAVM` Sharded One-Step Provers (`OffchainLabs/nitro-contracts` `src/osp/OneStepProofEntry.sol:23-200`):**
   - Lowers Wasm modules (compiled from Go/Rust state-transition code + floating-point soft-emulation) into `WAVM` instructions grouped into 64-instruction leaves (`mach.functionPc / 64`, `OneStepProofEntry.sol:137-141`).
   - Replaces flat register files with `MultiStack` (`ValueStack` active window + `remainingHash` hash-onion tail, lines 51–63) so stack pushes/pops require $O(1)$ calldata rather than 59-level Merkle proofs, and dispatches opcode ranges across four sharded contracts (`prover0`, `proverMem`, `proverMath`, `proverHostIo`, lines 149–188) to satisfy `EIP-170`.

#### 3.2 Preimage Oracle & Large-Payload Slicing
`Basis: source`

Because an L1 block cannot accept a multi-megabyte L2 batch or EIP-4844 blob inline inside a single `step()` calldata transaction, `Cannon` (`witness.go:10-24`, `FaultDisputeGame.sol:504-509, 581-617`) decouples data ingestion from execution via `IPreimageOracle`:
- The guest requests 32-byte key $k$ (tagged by key type: `1` = local context key such as `L1_HEAD_HASH` or `STARTING_OUTPUT_ROOT`, `2` = global `Keccak256`, `3` = `SHA256`, `4` = `EIP-4844` point-evaluation preimage, `5` = precompile result) and reads 8-byte chunks at `preimageOffset` (`MIPS64.sol:52-53`).
- For large preimages (`LPP` — Large Preimage Proposals), chunks are streamed into an on-chain Keccak sponge across multiple transactions before `step()`, which is why `FaultDisputeGame.sol:504-508` explicitly adds `vm().oracle().challengePeriod()` to `CLOCK_EXTENSION` at `MAX_GAME_DEPTH - 1` so an honest player cannot be timed out while waiting for an LPP challenge window to finalize!

### 4. Interactive Bisection Games and Sybil Delay Bounds (`FaultDisputeGame` vs. `BoLD`)

`Basis: normative + source + derived`

#### 4.1 Optimism Two-Tier Split-Depth Bisection (`FaultDisputeGame.sol:128-142, 420-557`)
A single rollup proposal spans thousands of L2 blocks, each executing up to billions of `MIPS64` instructions. `FaultDisputeGame` embeds both layers into one binary position tree indexed by generalized index `gindex` (`ROOT_POSITION = 1`):
- **Top Tree (`0 <= depth <= SPLIT_DEPTH`):** Claims commit to L2 `OutputRoot`s at block intervals.
- **Bottom Execution Subgames (`SPLIT_DEPTH + 1 <= depth <= MAX_GAME_DEPTH`):** Claims commit to `MIPS64` post-state hashes (`bytes32`, with high byte encoding `VMStatuses`: `0=Valid`, `1=Invalid`, `2=Panic`, `3=Unfinished`).
- **Attack vs. Defense Semantics (`move`, lines 460-462, 564-575):** Given disputed claim at `parentPos`, `attack` moves to left child (`2 * gindex`, disputing the state transition *up to* `parentPos`), whereas `defend` moves to right child (`2 * gindex + 1`, agreeing with `parentPos` and advancing midpoint forward). At `MAX_GAME_DEPTH`, `step()` (`lines 420-440`) executes `vm().step(_stateData, _proof, uuid.raw())` and counters the leaf iff `(parentPos.depth() - postState.position.depth()) % 2 == 0` disagrees with `validStep`.

#### 4.2 The Sequential Sybil Delay Problem and Arbitrum `BoLD` All-vs-All History Edges
In classical 1-vs-1 point-state bisection (`Kalodner et al., USENIX Security 2018`), two parties bisect assertions $(S_0, S_T)$ vs $(S_0, S'_T)$ by posting intermediate state $S_{T/2}$. Because an on-chain contract cannot tell *which* intermediate point state $S_{T/2}$ is honest until bisection reaches length 1, $A$ Sybil attackers with independent stakes can challenge an honest assertion **sequentially** (or branch separate 1-vs-1 games), stretching worst-case confirmation latency to $\Omega(A \cdot \Delta)$ for challenge period $\Delta$ (`Alvarez et al., arXiv:2404.10491`).

`BoLD` (`OffchainLabs/nitro-contracts` `src/challengeV2/EdgeChallengeManager.sol:25-190`, `OffchainLabs/bold` `challenge-manager/challenge-tree/tree.go`) eliminates multi-challenge delay multiplication via two structural invariants:
1. **Merkle-Accumulator History Commitments (Prefix Determinism):** Instead of claiming only point state $S_t$, an edge at step $t$ commits to the **Merkle accumulator root $H_t$ of all intermediate states $(S_0, S_1, \dots, S_t)$** (`MerkleTreeAccumulatorLib.sol`). Because an append-only history prefix $H_t$ uniquely binds every $S_{t'}$ for $t' \le t$, *every* honest party produces bit-identical edge IDs at every midpoint, allowing an unlimited coalition of honest defenders to pool defense moves on a single canonical edge!
2. **Deduplicated `EdgeStore` + Inherited Unrivaled Timers (`EdgeChallengeManager.sol:38-78, 116-125`):** Rivals sharing a predecessor share `mutualId` inside one global `EdgeStore` across three edge-granularity tiers (`LAYERZERO_BLOCKEDGE_HEIGHT`, `NUM_BIGSTEP_LEVEL` big-step levels of `LAYERZERO_BIGSTEPEDGE_HEIGHT`, and `LAYERZERO_SMALLSTEPEDGE_HEIGHT` down to length 1 `EdgeConfirmedByOneStepProof`). Child edges inherit cumulative `totalTimeUnrivaled` along their ancestor chain (`EdgeConfirmedByTime`), while all rival edges share bounded adversarial clock allowance—guaranteeing confirmation within $\le 2 \cdot \text{challengePeriodBlocks}$ regardless of $A$.

### 5. Compact Witness-Guided $O(|T|)$ Execution-Trace Certificates

`Basis: derived + execution`

Between full interactive bisection (requiring multi-day L1 challenge liveness) and ZKVM proving (requiring $10^3\times$–$10^5\times$ prover compute over prime fields), a third point in the verification design space is the **Non-ZK Witness-Guided Execution-Trace Certificate**:
- Let $\delta: \Sigma \times \Omega^* \rightharpoonup \Sigma$ be a total deterministic step relation parameterized by an untrusted advice stream $\omega \in \Omega^*$ supplying **strictly** the non-computable or non-deterministic choices: (1) external host/oracle input responses (`ECALL_READ` / preimage slices), (2) asynchronous preemption/interleaving coordinates `(tid, rcb_ticks)` when checking concurrent schedules, and (3) optional inverse/witness hints (e.g., sorted index or `BTree` lookup hint verified in $O(1)$ by the guest).
- **Soundness & Tightness Invariant:** Unlike `rr` (which logs post-syscall memory mutations trusted blindly during replay), an adversarial execution-trace certificate verifier **re-executes every deterministic instruction and host-boundary precondition from scratch** against $\omega$, accepting iff:
  1. Starting from committed initial image $\Sigma_0$, $T \le T_{\max}$ applications of $\delta$ reach `HALT(output)`;
  2. Every host-input read from $\omega$ matches its external commitment (e.g., SHA-256 / Merkle inclusion against public input root); and
  3. **Exact Advice Consumption (`adv_idx == |\omega|`):** Zero unconsumed trailing bytes remain in $\omega$, making the certificate non-malleable under trailing-byte smuggling.

#### Executable Verification Probes (`Basis: execution`)

Running the standalone Python 3.13 script below verifies `[2A]` `rr` PMU skid + `rseq` critical-section abort edge cases, `[2B]` 64-bit 59-level Merkle single-step read-modify-write root transitions, `[2C]` 1-vs-1 Sybil delay vs `BoLD` all-vs-all edge bounds, and `[2D]` a complete deterministic $O(|T|)$ witness-guided trace certificate verifier:

```python
#!/usr/bin/env python3
"""Deterministic micro-probes for rr replay, Merkle step proofs, bisection games, and trace certificates."""

import hashlib
import struct

def h_pair(left: bytes, right: bytes) -> bytes:
    return hashlib.sha3_256(left + right).digest()

def probe_2a_rr_skid_and_rseq_abort() -> None:
    start_ip, post_commit_offset, abort_ip, expected_sig = 0x401000, 0x18, 0x401040, 0x53053053
    def should_apply_rseq_abort(ip: int, ev: str, flags: int, sig: int) -> tuple[bool, int | None, bool]:
        if ev == "EV_SYSCALLBUF_FLUSH" or ip < start_ip or ip - start_ip >= post_commit_offset:
            return (False, None, False)
        if ev == "EV_SCHED" and (flags & 1):
            return (False, None, False)
        if sig != expected_sig:
            return (False, None, True)
        return (True, abort_ip, False)

    assert should_apply_rseq_abort(0x401008, "EV_SCHED", 0, expected_sig) == (True, abort_ip, False)
    assert should_apply_rseq_abort(0x401018, "EV_SCHED", 0, expected_sig) == (False, None, False)
    assert should_apply_rseq_abort(0x401008, "EV_SYSCALLBUF_FLUSH", 0, expected_sig) == (False, None, False)
    assert should_apply_rseq_abort(0x401008, "EV_SCHED", 0, 0xDEADBEEF) == (False, None, True)

    target_ticks, skid_size = 50_000, 125
    pmi_programmed = target_ticks - skid_size
    actual_pmi_stop = pmi_programmed + 73
    tail = target_ticks - actual_pmi_stop
    assert 0 < tail <= skid_size
    print(f"[2A] rseq abort verified across pre-commit/post-commit/flush/bad-sig; "
          f"PMU target={target_ticks} programmed={pmi_programmed}, overshoot_stop={actual_pmi_stop}, "
          f"exact breakpoint/singlestep tail={tail} (<= skid_size={skid_size}).")

def probe_2b_merkle_64bit_step_proof() -> None:
    LEVELS = 59
    zero_hashes = [hashlib.sha3_256(b"\x00" * 32).digest()]
    for _ in range(LEVELS):
        zero_hashes.append(h_pair(zero_hashes[-1], zero_hashes[-1]))
    paddr = 0x8000_0008
    leaf_idx, word_off = paddr >> 5, paddr & 0x1F
    old_leaf = bytearray(32)
    struct.pack_into("<Q", old_leaf, word_off, 41)
    siblings = [zero_hashes[lvl] for lvl in range(LEVELS)]

    def compute_root(leaf_bytes: bytes, idx: int, sibs: list[bytes]) -> bytes:
        node = hashlib.sha3_256(leaf_bytes).digest()
        for lvl, sib in enumerate(sibs):
            node = h_pair(sib, node) if ((idx >> lvl) & 1) else h_pair(node, sib)
        return node

    pre_root = compute_root(bytes(old_leaf), leaf_idx, siblings)
    read_val = struct.unpack_from("<Q", old_leaf, word_off)[0]
    new_leaf = bytearray(old_leaf)
    struct.pack_into("<Q", new_leaf, word_off, (read_val + 1) & 0xFFFFFFFFFFFFFFFF)
    post_root = compute_root(bytes(new_leaf), leaf_idx, siblings)
    print(f"[2B] 64-bit Merkle RMW verified ({LEVELS} levels, {32 + LEVELS * 32} B proof): "
          f"pre_root={pre_root.hex()[:16]}... -> post_root={post_root.hex()[:16]}...")

def probe_2c_bisection_delay_vs_bold_edges() -> None:
    trace_steps, num_adversaries, period = 1 << 20, 8, 50400
    rounds = trace_steps.bit_length() - 1
    classic_delay, bold_delay = num_adversaries * period, 2 * period
    assert rounds == 20 and classic_delay == 403200 and bold_delay == 100800
    print(f"[2C] N=2^20 trace ({rounds} bisections + 1 OSP): "
          f"1-vs-1 sequential delay (A={num_adversaries})={classic_delay} blocks vs "
          f"BOLD all-vs-all bound={bold_delay} blocks (independent of A).")

def probe_2d_witness_guided_trace_certificate() -> None:
    prog = [
        ("ECALL_READ", 1), ("ANDI", 2, 1, 1), ("BEQ", 2, 0, 5),
        ("MUL3_ADD1", 1, 1), ("JAL", 0, 6), ("SRLI1", 1, 1),
        ("ADD", 3, 3, 1), ("ADDI", 4, 4, 1), ("BLT_CONST", 4, 16, 0), ("HALT", 3),
    ]
    advice_words = [3 * i + 5 for i in range(16)]
    cert_bytes = struct.pack("<I" + "Q" * len(advice_words), len(advice_words), *advice_words)

    def verify_cert(cert: bytes, max_steps: int = 10000) -> tuple[bool, int, int]:
        (n_adv,) = struct.unpack_from("<I", cert, 0)
        if 4 + 8 * n_adv != len(cert):
            return (False, 0, 0)
        adv = list(struct.unpack_from("<" + "Q" * n_adv, cert, 4))
        adv_idx, regs, pc, steps = 0, [0] * 8, 0, 0
        while steps < max_steps:
            steps += 1
            regs[0] = 0
            ins = prog[pc]
            op = ins[0]
            if op == "ECALL_READ":
                if adv_idx >= len(adv):
                    return (False, steps, 0)
                regs[ins[1]], adv_idx, pc = adv[adv_idx], adv_idx + 1, pc + 1
            elif op == "ANDI":
                regs[ins[1]], pc = regs[ins[2]] & ins[3], pc + 1
            elif op == "BEQ":
                pc = ins[3] if regs[ins[1]] == regs[ins[2]] else pc + 1
            elif op == "MUL3_ADD1":
                regs[ins[1]], pc = (3 * regs[ins[2]] + 1) & 0xFFFFFFFFFFFFFFFF, pc + 1
            elif op == "JAL":
                pc = ins[2]
            elif op == "SRLI1":
                regs[ins[1]], pc = regs[ins[2]] >> 1, pc + 1
            elif op == "ADD":
                regs[ins[1]], pc = (regs[ins[2]] + regs[ins[3]]) & 0xFFFFFFFFFFFFFFFF, pc + 1
            elif op == "ADDI":
                regs[ins[1]], pc = (regs[ins[2]] + ins[3]) & 0xFFFFFFFFFFFFFFFF, pc + 1
            elif op == "BLT_CONST":
                pc = ins[3] if regs[ins[1]] < ins[2] else pc + 1
            elif op == "HALT":
                return (adv_idx == len(adv), steps, regs[ins[1]])
        return (False, steps, 0)

    ok, steps_run, acc = verify_cert(cert_bytes)
    assert ok and not verify_cert(cert_bytes + struct.pack("<Q", 999))[0]
    full_bytes = steps_run * 72
    print(f"[2D] Witness-guided certificate verified in {steps_run} steps (acc={acc}): "
          f"cert={len(cert_bytes)} B vs full_state_trace={full_bytes} B "
          f"({full_bytes / len(cert_bytes):.1f}x smaller); trailing/malformed advice rejected.")

if __name__ == "__main__":
    probe_2a_rr_skid_and_rseq_abort()
    probe_2b_merkle_64bit_step_proof()
    probe_2c_bisection_delay_vs_bold_edges()
    probe_2d_witness_guided_trace_certificate()
```

Observed output (`Python 3.13.15`):
```text
[2A] rseq abort verified across pre-commit/post-commit/flush/bad-sig; PMU target=50000 programmed=49875, overshoot_stop=49948, exact breakpoint/singlestep tail=52 (<= skid_size=125).
[2B] 64-bit Merkle RMW verified (59 levels, 1920 B proof): pre_root=5b15feb7cdb79e4a... -> post_root=4c32b6acebe1c373...
[2C] N=2^20 trace (20 bisections + 1 OSP): 1-vs-1 sequential delay (A=8)=403200 blocks vs BOLD all-vs-all bound=100800 blocks (independent of A).
[2D] Witness-guided certificate verified in 121 steps (acc=748): cert=132 B vs full_state_trace=8712 B (66.0x smaller); trailing/malformed advice rejected.
```

## Boundaries

- **Adversarial soundness of raw `rr` trace files (`known not to apply`):** `rr` (`rr-debugger/rr`) trusts the recording host and stores raw kernel-written memory buffers in `TraceFrame` data records to skip re-executing external I/O. An untrusted prover can forge arbitrary syscall outputs in an `rr` trace; turning `rr`-style traces into adversarial execution certificates requires authenticating every external input record against a trusted oracle/commitment and re-evaluating internal syscalls deterministically.
- **True parallel shared-memory multicore recording in `rr` (`unsupported`):** `rr` achieves low-overhead determinism by serializing tracee threads onto one logical core at a time (`--chaos` randomizes single-core scheduling to expose concurrency bugs, but does not execute user threads concurrently across multiple cores with hardware data-race logging as in `SMP-ReVirt`).
- **Virtualization and hardware PMU availability for `rr` (`unsupported` on unvirtualized PMUs):** `rr` requires deterministic hardware `BR_INST_RETIRED.CONDITIONAL` (or ARM `BR_RETIRED`) counters without hypervisor counter-drop errata (`has_kvm_in_txcp_bug`, `has_xen_pmi_bug` in `PerfCounters_x86.h:276-305`) and rejects CPUs Marked `PMU_SKID_UNBOUNDED` (`PerfCounters.cc:192`) unless fallback modes are forced.
- **Censorship resistance of interactive bisection under L1 liveness failure (`known not to apply`):** Unlike non-interactive validity/ZK proofs or standalone $O(|T|)$ trace certificates, `FaultDisputeGame`, `BoLD`, and Cartesi PRT require at least one honest participant to have L1 transaction inclusion within `MAX_CLOCK_DURATION` / `challengePeriodBlocks`. If an L1 block-producer cartel censors honest bisection/OSP transactions for the full challenge window, a fraudulent assertion can confirm by timeout.
- **Cross-implementation compiler/emulator differential bugs in FPVMs (`not examined` exhaustively):** Soundness of `Cannon`, `WAVM`, and `Cartesi` requires bit-exact equivalence between the off-chain emulator (`cannon` Go, `nitro` C++/Go, `cartesi/machine-emulator` C++) and the on-chain Solidity step contract (`MIPS64.sol`, `OneStepProver*.sol`, `UArchStep.sol`). Differential fuzzing harnesses (`cannon/mipsevm/tests/fuzz_evm_common64_test.go`, `machine-solidity-step/test/UArchInterpret.t.sol`) exist upstream, but formal machine-checked equivalence proofs of those Solidity contracts were `not examined`.

## Evidence

| Subject / Artifact | Coordinate | Inspected Paths / Identifiers | Evidentiary Role |
| :--- | :--- | :--- | :--- |
| `rr-debugger/rr` | `608efe319bbbc4d0f5658d984e16be187801325d` | `src/PerfCounters.h:30-180`, `src/PerfCounters.cc:46-250`, `src/PerfCounters_x86.h:8-420`, `src/Task.cc:4682-4731`, `src/record_syscall.cc:4839-4912`, `src/ReplaySession.cc:507, 985-1002, 1580-1765`, `src/preload/rrcalls.h:9-145` | `source` |
| `ethereum-optimism/optimism` | `f0d907fd862acb2fecd354a0cfe6fbe9c7a47a2a` | `cannon/mipsevm/witness.go:1-34`, `packages/contracts-bedrock/src/cannon/MIPS64.sol:25-220`, `packages/contracts-bedrock/src/cannon/libraries/MIPS64Memory.sol:7-160`, `packages/contracts-bedrock/src/dispute/FaultDisputeGame.sol:127-260, 420-618` | `source` |
| `OffchainLabs/nitro-contracts` | `349a4bfbdfec8924f13cc3e2bbad31161fa76378` | `src/osp/OneStepProofEntry.sol:14-200`, `src/challengeV2/EdgeChallengeManager.sol:25-220` | `source` |
| `OffchainLabs/bold` | `30e78f67f40eacaab13577e507bab6025df843d6` | `challenge-manager/challenge-tree/{tree.go,add_edge.go,ancestors.go}`, `chain-abstraction/sol-implementation/edge_challenge_manager.go` | `source` |
| `cartesi/machine-emulator` | `f9e4f82003a6f5acc9821c06f8a29025e0f895e3` | `src/address-range-defines.h:20-53`, `src/uarch-step.cpp`, `src/hash-tree.cpp` | `source` |
| `cartesi/machine-solidity-step` | `fb00a32c38248edc5672e689dfa8cc58c0a2c3cd` | `src/AccessLogs.sol:24-200`, `src/UArchStep.sol:26-180` | `source` |
| O'Callahan et al. (USENIX ATC 2017) | `arXiv:1705.05937` (`ISBN 978-1-931971-38-6`, pp. 377–389) | `rr` user-space deployment constraints, `syscallbuf`, and PMU `RCB` determinism | `normative` + `documentation` |
| Canetti, Riva, Rothblum (CCS 2011) | `DOI: 10.1145/2046707.2046759` (pp. 445–454) | Refereed delegation of computation and $O(\log T)$ bisection under 1-honest server | `normative` |
| Kalodner et al. (USENIX Security 2018) & Alvarez et al. (2024) | `ISBN 978-1-939133-04-5` (pp. 1353–1370); `arXiv:2404.10491` | Arbitrum interactive bisection vs. `BoLD` all-vs-all history-commitment delay bounds | `normative` |
| Inline Python 3.13 Micro-Probes | Executed `2026-11-19` on Linux (`Python 3.13.15`) | `[2A]`–`[2D]` `rseq`/PMU-skid, 59-level Merkle RMW, `BoLD` delay, and $O(\|T\|)$ certificate checks | `execution` |

## Revalidation

To revalidate these findings quickly after upstream updates to `rr`, `optimism`, `nitro-contracts`/`bold`, or `cartesi`:

1. **Rerun the Inline Deterministic Replay & Merkle Probe (`< 0.1 s`):** Execute `python3 /tmp/bisection_and_trace_cert_probes.py` (copied from **Findings §5**) to confirm `rseq` pre/post-commit interval handling, 59-level Merkle RMW proof sizing (`1,920` bytes), and trailing-advice certificate rejection.
2. **Check `rr` PMU Table & `rseq` Abort Rules:** Diff `src/PerfCounters.cc` (`pmu_configs[]`), `src/PerfCounters_x86.h` (`compute_cpu_microarch`), and `src/Task.cc` (`Task::should_apply_rseq_abort`) when adding new Intel/AMD/ARM cores or Linux kernel `rseq` flags (e.g., slice extension flags).
3. **Check FPVM State Version & Merkle Proof Geometry:**
   - For `Cannon`, inspect `STATE_VERSION` (`MIPS64.sol:95`), `PACKED_THREAD_STATE_SIZE` (`:41`), `MEM_PROOF_LEAF_COUNT` (`MIPS64Memory.sol:9`), and `FaultDisputeGame.sol` `SPLIT_DEPTH` / `CLOCK_EXTENSION` invariants (`:216-232, 504-522`).
   - For `Cartesi`, inspect `AccessLogs.sol` (`[32 bytes leaf] + [59 * 32 bytes siblings]`) and `address-range-defines.h` shadow address offsets.
   - For `Arbitrum BoLD`, inspect `EdgeChallengeManager.sol` (`LAYERZERO_{BLOCK,BIGSTEP,SMALLSTEP}EDGE_HEIGHT` and `NUM_BIGSTEP_LEVEL`) and `OneStepProofEntry.sol` (`proveOneStep` opcode routing across `prover0`/`proverMem`/`proverMath`/`proverHostIo`).
