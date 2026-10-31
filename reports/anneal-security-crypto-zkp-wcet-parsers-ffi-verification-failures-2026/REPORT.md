<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Historical Verification and Implementation Failures Across Constant-Time Compilation, Cryptographic Arithmetic and Protocols, Zero-Knowledge Proof Systems, WCET Resource Bounds, and Wire-Format Parsers

## Summary

Across thirty years of high-assurance systems engineering, the most severe
vulnerabilities in verified or heavily audited cryptography, zero-knowledge
proof (ZKP) circuits, hard real-time embedded controllers, and cross-language
wire-format parsers have rarely stemmed from broken mathematical conjectures or
unsound theorem-prover kernels. Instead, they share a recurring structural
anatomy: **semantic gaps at the boundary between an idealized specification
model and a concrete compiler, hardware microarchitecture, witness generator, or
serializer**. Evaluating these historical postmortems against Anneal's four
trusted primitives (`Trusted/Refinement.lean`, `BehaviorCodec` /
`PartialBehaviorCodec`, `Trusted/StepResult.lean`, and `VerificationResultOn` /
`TrustPolicy` / `ScopedVerificationResult`) yields four foundational lessons:

1. **Compiler-induced constant-time violations and microarchitectural escapes
   (`Obs` adequacy and `Compiles` trace preservation):** Mainstream optimizing
   compilers (`Clang`/LLVM, `GCC`, `MSVC`, and `rustc`) validate transformations
   solely against architectural return-value and memory-state refinement,
   routinely rewriting branchless bitwise selection masks
   (`(a & mask) | (b & ~mask)`) into secret-dependent conditional branches or
   spilling secret registers to unzeroized stack slots (Simon, Chisnall, &
   Anderson EuroS&P 2018; Kaufmann et al. CANS 2016; Schneider et al. 2024;
   `curve25519-dalek` / `cmov` CVE-2024-58262). Even when binary control flow
   and memory addresses are secret-independent, variable-latency instructions
   such as `idiv`/`udiv` in `ML-KEM`/Kyber (`KyberSlash1` and `KyberSlash2`,
   Dec 2023) and data-dependent hardware mechanisms such as x86/ARM Dynamic
   Voltage and Frequency Scaling (`Hertzbleed`, CVE-2022-23823) and Apple
   Silicon Data Memory-Dependent Prefetchers (`Augury` 2022; `GoFetch` USENIX
   Security 2024) leak secret keys because the leakage observation alphabet
   `Obs` omitted instruction-operand latency $\lambda(\mathsf{op}, v_1, v_2)$
   or pointer-value cache prefetch side effects. In Anneal, preserving
   constant-time or side-channel noninterference across compilation requires
   instantiating `SmallStepMachine` with an explicit leakage observation type
   `Obs`, proving trace-preserving `Compiles` (which rejects unverified LLVM
   backend rewrites unless mediated by single-source verified codegen), and
   recording unmodeled silicon hazards (DMP, DVFS) as explicit, auditable
   `TrustPolicy` obligations rather than silent model omissions.
2. **Cryptographic carry-propagation and protocol state-machine bugs
   (exhaustive bitvector domain coverage and `StepResult.externalCall`):**
   Multi-limb arithmetic bugs in OpenSSL (`bn_sqr8x_internal` CVE-2014-3570;
   `x86_64-mont5.pl` Montgomery squaring CVE-2015-3193), `libgcrypt`
   (CVE-2017-7526), and curve libraries occur on $2^{-32}$ or $2^{-64}$
   carry-chain boundary inputs that evade random testing and motivated
   `Fiat-Crypto` (Erbsen et al. S&P 2019) and `CryptoLine` (Polyakov et al. CAV
   2018). At the protocol layer, the 17-year-old Needham-Schroeder flaw (Lowe
   1995), TLS `3SHAKE` (Bhargavan et al. 2014), WPA2 `KRACK` (Vanhoef &
   Piessens CCS 2017, CVE-2017-13077), and TLS `Raccoon` (Merget et al. 2020,
   CVE-2020-1968) arose when symbolic models omitted active intruder
   interleaving, session-resumption context binding, retransmission-induced
   nonce resets, or leading-zero timing side channels. In Anneal,
   `PartialBehaviorCodec` enforces canonical multi-limb decoding across 100% of
   `(L.sem s q)` inputs (`WellFormedOn`), while `StepResult.externalCall
   boundaryInv next` enforces call-site state invariants (such as one-time
   nonce monotonicity and key separation) across every re-entrant adversary or
   network callback.
3. **Zero-knowledge proof under-constrained, over-constrained, and Frozen Heart
   bugs (`Compiles` + `ProductiveOn` duality and `PartialBehaviorCodec`):**
   Empirical analysis of 141 SNARK vulnerabilities (Chaliasos et al. USENIX
   Security 2024) across `Circomlib` (`MiMC`, `BabyJubJub`
   `Edwards2Montgomery`, `Num2Bits`/`AliasCheck`), Tornado Cash, Semaphore,
   Aztec 2.0, Polygon zkEVM, Scroll, `RISC Zero`, and `SP1` demonstrates that
   separating imperative witness generation (`<--` or host-oracle hints) from
   polynomial constraints (`===` over $\mathbb{F}_p$) splits correctness into
   two dual failure modes: **under-constrained circuits** (where constraints
   accept bogus witnesses, violating `Compiles`) and **over-constrained
   circuits** (where valid inputs admit zero witnesses, violating
   `ProductiveOn`). In Anneal, pairing `Compiles` ($t \le \pi_c(s)$) with
   `ProductiveOn` ($\forall q,\; \mathsf{pre}\;q \implies \exists h\;o,\;
   \mathsf{val}\;h\;o$) over a `PartialBehaviorCodec` whose `decodeOut` maps
   non-canonical field limbs ($\ge 2^w$ or $\ge p$) to `none` simultaneously
   blocks under-constrained proof forgery and over-constrained completeness
   freezes, while `StepResult.externalCall` blocks Trail of Bits' **Frozen
   Heart** Fiat-Shamir vulnerability by requiring `boundaryInv` to verify that
   all public inputs and prior phase commitments are absorbed into the sponge
   transcript before sampling challenge scalars.
4. **WCET timing anomalies, embedded stack overflows, and parser malleability
   (`EventualBehaviorOf` non-additivity and `encodeOut_of_decodeOut`
   injectivity):** On out-of-order microprocessors, a local L1 cache *hit* can
   trigger a globally *longer* execution time than a cache *miss* due to
   functional-unit contention (Lundqvist & Stenström RTSS 1999), falsifying
   compositional basic-block WCET addition unless pipeline/cache state is
   carried in `State`. In safety-critical firmware, the Toyota ETCS-i
   unintended-acceleration stack overflow (Bookout v. Toyota 2013; Koopman
   2014) and static stack analyzer blind spots (`cargo-call-stack` on indirect
   vtable calls and nested interrupts) show why stack-depth bounds must be
   enforced in target semantics (`X86Semantics.lean`) and audited via
   `ScopedVerificationResult`. Finally, parser differential and malleability
   exploits—Bitcoin DER signature malleability (BIP-62/BIP-66), X.509
   null-prefix attacks (CVE-2009-2408), Android Master Key ZIP differentials
   (CVE-2013-4787 / CVE-2013-8619), and Android `Parcel` deserialization
   mismatches (CVE-2014-7911)—all exploit non-injective parsing where two
   distinct wire byte sequences $b_1 \neq b_2$ decode to the same logical value
   or decode differently across two parsers. Anneal's `PartialBehaviorCodec`
   injectivity law (`encodeOut_of_decodeOut : decodeOut o₂ = some o₁ →
   encodeOut o₁ = o₂`) mathematically enforces canonical, non-malleable wire
   formats and rejects ambiguous encodings (`decodeOut o₂ = none`).

## Applicability

This report synthesizes primary postmortems, CVEs, and academic literature across
security, cryptography, zero-knowledge proof systems, real-time WCET/stack
analysis, and wire-format parsing, and maps their failure modes onto the pinned
Anneal verification architecture identified in `REPORT.json`:

| Subject | Identity / Coordinates | Scope in This Report |
| :--- | :--- | :--- |
| Anneal Core Framework | `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` (`trusted/lean/Trusted/Refinement.lean`, `Trusted/StepResult.lean`, `Trusted/MirSemantics.lean`) | Baseline definitions of `Preorder`, `Partial`, `Behavior`, `Language`, `Compiles`, `Abstracts`, `StepResult`, `ReachesPrefix`, `BehaviorOf`, `TrustPolicy`, and `VerificationResultOn`. |
| Anneal MIR-to-x86-64 Branch | `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14` (`trusted/lean/Trusted/X86Semantics.lean`, `theory/Anneal/Compiler/NaiveCodegen.lean`, `Peephole.lean`) | Target ISA small-step operational model (`X86Machine`), stack-slot bounds, `#DE` division traps (`idiv`/`udiv`), and assembly emission boundary. |
| Anneal Reference Hardening Corpus | `joshlf/anneal@df55c524a051d59e7dd35564f282b30d29133392` (`reports/anneal-*`) | Mechanized hardening primitives: `PartialBehaviorCodec`, `EventualBehaviorOf`, `ProductiveOn`, `StepResult.externalCall`, `ScopedVerificationResult`, `TCBModel`, and `BoundaryCanarySuite`. |
| Constant-Time & Side-Channel Postmortems | EuroS&P 2018; CANS 2016; USENIX Security 2024; `KyberSlash1/2`; `Hertzbleed` (CVE-2022-23823/24436); `Augury`; `GoFetch`; CVE-2024-58262 | Compiler optimization of branchless masks, variable-time division instructions, DVFS frequency throttling, and Apple Silicon DMP pointer-value prefetching. |
| Cryptographic Arithmetic & Protocols | CVE-2014-3570; CVE-2015-3193; CVE-2017-7526; CVE-2017-13077 (`KRACK`); CVE-2020-1968 (`Raccoon`); Lowe (1995); `3SHAKE`; `Fiat-Crypto`; `CryptoLine` | Multi-limb carry propagation bugs on rare inputs and symbolic-vs-computational protocol state-machine and timing vulnerabilities. |
| Zero-Knowledge Proof Postmortems | Chaliasos et al. (USENIX Security 2024); Trail of Bits `Frozen Heart` (2022); `Circomlib`, Tornado Cash, Semaphore, Aztec 2.0, Polygon zkEVM, Scroll, `RISC Zero`, `SP1` | Under-constrained and over-constrained R1CS/Plonkish/AIR circuits, field-aliasing bugs, zkVM guest-host oracle hints, and Fiat-Shamir transcript omissions. |
| WCET, Stack Bounds & Parser Differentials | Lundqvist & Stenström (RTSS 1999); Toyota ETCS-i (2013/2014); `cargo-call-stack`; BIP-62/66; CVE-2009-2408; CVE-2013-4787/8619; CVE-2014-7911 | Out-of-order CPU timing anomalies, RTOS stack overflows, indirect/ISR call-graph gaps, and non-injective ASN.1/ZIP/Parcel parser differentials. |

Separate exact upstream observation from architectural synthesis: the historical
CVEs and papers establish concrete failure mechanisms in their respective C,
Rust, assembly, Circom, and protocol implementations, while the mappings to
Anneal's four `trusted/` primitives are derived structural analyses showing how
Anneal's type and theorem signatures prevent or isolate each class of defect.

## Findings

### 1. Compiler-Induced Constant-Time Violations and Microarchitectural Side-Channel Escapes

#### 1.1 How Optimizing Compilers Break Constant-Time Source Code (Simon, Chisnall, & Anderson EuroS&P 2018; Kaufmann et al. CANS 2016; Schneider et al. 2024)

Basis: documentation + source + derived.

Cryptographic implementations defend against timing and cache-timing attacks by
following the **constant-time programming discipline**: control-flow decisions
(branches, loop bounds), memory access addresses (array/table indices), and
variable-latency instruction operands must never depend on secret values.
Because C and Rust provide no source-level semantics for execution time or
register allocation, cryptographic engineers encode conditional assignments as
branchless bitwise arithmetic over all-ones (`0xFFFF...`) or all-zeros
(`0x0000...`) masks:

```rust
// Branchless constant-time selection in source Rust/C:
// mask is 0u64.wrapping_sub(cond as u64), i.e., 0xFFFF_FFFF_FFFF_FFFF or 0.
let selected = (a & mask) | (b & !mask);
```

Three landmark empirical studies and recent Rust CVEs demonstrate that
mainstream optimizing compilers systematically destroy these source-level
guarantees because their internal intermediate representations (LLVM IR, GIMPLE,
MSVC CIL) model only value-level input/output behavior:

1. **Kaufmann, Pelletier, Vaudenay, & Villegas (CANS 2016), *"When Constant-Time
   Source Yields Variable-Time Binary: Exploiting Curve25519-donna Built with
   MSVC 2015"*:**
   Adam Langley's 32-bit `Curve25519-donna` C implementation was meticulously
   written without secret-dependent branches or secret-indexed lookups, using a
   constant-time conditional swap (`cswap`) in the Montgomery ladder and 64-bit
   `uint64_t` shifts for radix-$2^{25.5}$ limb reduction. When compiled for
   32-bit x86 with Microsoft Visual C++ 2015 (`cl.exe /O2`), the compiler
   lowered 64-bit right shifts (`int64_t >> k`) to a runtime helper function
   `__allshr` and optimized the constant-time bitwise mask inside the ladder swap
   into a `test` + conditional jump (`je`) that skipped the swap when the secret
   scalar bit was `0`. Because the branch predictor and instruction cache traced
   every bit of the 255-bit secret scalar during X25519 key exchange, Kaufmann et
   al. recovered the full private key from local cache-timing observations.
2. **Simon, Chisnall, & Anderson (IEEE EuroS&P 2018), *"What You Get Is What You
   C: Controlling Side Effects in Mainstream C Compilers"*:**
   Auditing `Clang`/LLVM (versions 3.0 through 5.0) and `GCC` across x86-64,
   ARM, and MIPS on production constant-time primitives from OpenSSL, BoringSSL,
   and NaCl (`crypto_verify_16`, `constant_time_eq`, `constant_time_select`),
   Simon et al. showed that LLVM's `SimplifyCFG`, `InstCombine`, and backend
   `SelectionDAG` / `EarlyIfConversion` passes recognize bitwise selection
   idioms (`(x & m) | (y & ~m)` where `m = -(cond != 0)`), reconstruct the high-
   level ternary `cond ? x : y`, and then lower that ternary back into a
   conditional branch (`jne`) whenever the target CPU's branch-cost heuristic
   estimates a branch as cheaper than two ALU instructions plus a `cmov`. Worse,
   Simon et al. documented two additional compiler-induced side channels:
   - **Dead-store elimination of secret zeroization (`memset`):** Standard
     `memset(secret_buf, 0, len)` at the end of a stack frame is deleted by LLVM
     `DSE` (`DeadStoreElimination`) because reading a local buffer after
     function return is Undefined Behavior in C/Rust.
   - **Register-allocator secret spilling:** Even if source variables are
     zeroized, LLVM's greedy register allocator (`RAGreedy`) may spill
     intermediate secret values from architectural registers onto unnamed stack
     spill slots during high register pressure without ever zeroizing those
     stack slots before `ret`.
3. **Schneider, Lain, Puddu, Dutly, & Čapkun (2024 / CCS-era empirical compiler
   studies) and Rust `cmov` / `curve25519-dalek` (`CVE-2024-58262`):**
   Large-scale differential binary analysis across LLVM 14–19, GCC 11–14, and
   `rustc` demonstrated that LLVM's middle-end range analysis (`CorrelatedValuePropagation`
   and `InstCombine`) combined with backend instruction selection (`TargetLowering`
   on ARM Cortex-M0/M4, RISC-V, and x86-64) introduces secret-dependent branches
   into Rust crates that rely on portable bitwise masks rather than opaque
   inline assembly (`core::arch::asm!`) or `core::hint::black_box`. In
   `CVE-2024-58262`, the RustCrypto `cmov` crate (used by downstream
   cryptographic libraries) suffered an LLVM optimization on ARMv6-M (Cortex-M0)
   and other targets without hardware `cmov` instructions where LLVM recognized
   the bitmask conditional select and emitted a conditional branch (`bne`) over
   the secret condition bit.

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

- **Why value-only `Out` fails (`Trusted/Refinement.lean` &
  `Trusted/StepResult.lean`):** If `L_src` and `L_tgt` define `Out` solely by
  terminal return values (`TerminationKind Val`) with an empty observation trace
  (`Obs := Unit`), a compiler pass that rewrites branchless bitwise selection
  `let res = (a & mask) | (b & !mask)` into `if mask != 0 { a } else { b }`
  satisfies `Compiles L_src L_tgt C.π s t` (`L_tgt.sem t ≤ C.π (L_src.sem s)` at
  `Trusted/Refinement.lean:369-372`) because both programs compute the identical
  return value on every input!
- **Enforcing constant-time via `StepResult.step obs next` and
  `PartialBehaviorCodec`:** As established in `Trusted/StepResult.lean:70-74`
  and `reports/security-observations-and-relational-compiler-preservation`,
  `SmallStepMachine` records an explicit per-step observation `obs : Obs` in
  `ExecOut.trace : List Obs` (`Trusted/StepResult.lean:114-116`). When `Obs`
  records the program counter (`pc`), memory access address (`addr`), and
  stack-spill addresses at every step:
  1. A target pass `s ↦ t` that turns a branchless ALU sequence into a
     conditional jump emits distinct `pc` traces on secret-varying inputs and
     violates `obs_decodeOut` in `PartialBehaviorCodec`.
  2. Furthermore, because `rustc` delegates code generation to unverified LLVM
     passes, Anneal's `mir-to-x86` architecture (`4f45f0a391a9`)—which compiles
     captured MIR directly to verified `X86Body` in Lean without passing through
     LLVM's middle-end `SimplifyCFG`/`InstCombine`—eliminates the unverified C/
     LLVM optimization gap entirely, provided `X86Body` is emitted from a single
     `.olean`-bound source (`SingleSourceCodegen.lean` in
     `anneal-rustc-obligation-inventory-and-single-source-codegen-2026`).

#### 1.2 Variable-Latency Integer Division in Post-Quantum Cryptography: `KyberSlash1` and `KyberSlash2` (Tamvada, Bhargavan, & Kiefer; Bernstein, Kannwischer, & Ravi Dec 2023)

Basis: documentation + source + derived.

In December 2023, two critical timing side-channel vulnerabilities—**`KyberSlash1`**
(discovered by Goutam Tamvada, Karthikeyan Bhargavan, and Franziskus Kiefer at
Cryspen) and **`KyberSlash2`** (discovered by Daniel J. Bernstein, Matthias J.
Kannwischer, and Prasanna Ravi)—were disclosed against the official C reference
implementation (`pq-crystals/kyber`) and over a dozen production libraries
(`PQClean`, `liboqs`, `circl`, `crystals-go`, `Botan`, `SYMCRYPT`) implementing
NIST's standardized post-quantum Key Encapsulation Mechanism **ML-KEM**
(CRYSTALS-Kyber, FIPS 203).

1. **Technical Root Cause (`idiv` / `udiv` on Secret Polynomial Coefficients):**
   - **`KyberSlash1` (`poly_tomsg`):** During Fujisaki-Okamoto (`FO`)
     decapsulation, after decrypting the noisy polynomial $v - s^T u \pmod q$
     (where $s$ is the secret key and $q = 3329$), `poly_tomsg` converts each
     polynomial coefficient $t \in \mathbb{Z}_q$ into a 1-bit message bit by
     computing:
     ```c
     t = (((t << 1) + KYBER_Q / 2) / KYBER_Q) & 1;
     ```
     Because `t` was a signed 16-bit integer (`int16_t`) rather than unsigned, or
     when compiled with `-Os` / size-optimization flags or on architectures
     where the compiler did not replace `/ 3329` with a Barrett/Montgomery
     multiply-shift sequence, `GCC` and `Clang` emitted a native hardware
     division instruction (`idiv` on x86, `sdiv`/`udiv` on ARMv7-A / ARMv8-M,
     `div` on RISC-V).
   - **`KyberSlash2` (`poly_compress` during re-encryption):** During the
     Fujisaki-Okamoto re-encryption check (which encrypts the decrypted candidate
     message $m'$ under a seed derived from $m'$ to verify that the resulting
     ciphertext matches the input ciphertext), `poly_compress` computed:
     ```c
     d0 <<= 4;
     d0 += 1665;
     d0 *= 80635;
     d0 >>= 28;
     ```
     in patched code, but in the unpatched reference implementation and several
     ports, compression divided secret-derived coefficients by `KYBER_Q` using
     `/` (`(((uint32_t)u[8*i+j] << 4) + KYBER_Q/2) / KYBER_Q`).
   - **Hardware Variable Latency:** On ARM Cortex-A7 (Raspberry Pi 2), Cortex-M4,
     Intel Skylake/Ice Lake, and RISC-V cores, hardware integer division is
     **not constant-time**: early-termination dividers take between 2 and 12+
     cycles depending on the number of leading zeros in the dividend and
     divisor. Using chosen ciphertexts, Bernstein et al. and Tamvada et al.
     demonstrated full ML-KEM private key recovery in **minutes** on ARM
     Cortex-A7 and Cortex-M4.
2. **Why Classic Constant-Time Static Analyzers Missed `KyberSlash`:**
   Early static constant-time verifiers defined the leakage observation trace
   solely as **control-flow (`PC`) + memory-access addresses (`Addr`)**. Under
   that restricted leakage model, `x / y` has no branches and touches no memory,
   so `((t << 1) + 1664) / 3329` verified as 100% "constant-time"! Only tools
   that include **variable-time instruction operands** in their leakage function
   $\lambda(\mathsf{instr}, \vec{v})$ (such as `ct-verif` Almeida et al. USENIX
   Security 2016, `Jasmin`'s constant-time checker, and the patched `Valgrind`
   `ctgrind` instruction-tainting rules released after `KyberSlash`) flag
   secret dividends/divisors in `idiv`/`udiv`/`sdiv`/`rem`.

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

- **Look at `Trusted/X86Semantics.lean` on the `mir-to-x86` branch
  (`4f45f0a391a9`):** In `X86Semantics.lean`, `X86Machine` models `idiv`/`udiv`
  functional division and `#DE` traps (verified by `BoundaryCanarySuite` guards
  for division by zero and `INT64_MIN / -1` in
  `anneal-structural-external-calls-and-tcb-mutation-testing-2026`), but emits
  `Obs := Unit`.
- **Instruction-operand leakage in `StepResult.step obs next`:** To prevent a
  `KyberSlash`-class vulnerability when verifying constant-time Rust/x86-64 code
  in Anneal, `X86Machine`'s step observation `obs : X86LeakageObs` must record
  not only `.branch pc taken` and `.memAccess addr`, but also
  `.varLatencyOp opcode dividend divisor` for every architectural instruction
  whose hardware execution latency is data-dependent (`idiv`, `div`, variable-
  count shifts on legacy cores, and non-constant-time floating-point instructions).
  Under relational verification over `BehaviorOf`, two executions with
  differing secret inputs produce distinct `.varLatencyOp` traces unless both
  operands of `idiv`/`div` are proven public.

#### 1.3 Microarchitectural Prefetcher and Frequency Side-Channel Escapes: `Hertzbleed`, `Augury`, and `GoFetch` (2022–2024)

Basis: documentation + derived.

Even when a binary satisfies the strongest software constant-time contract—
identical `PC` traces, identical memory load/store addresses, and zero variable-
latency instructions—two classes of silicon microarchitectural optimizations
discovered between 2022 and 2024 break software constant-time isolation by
converting **data values** in registers or L1 cache into observable timing or
cache-state variations:

1. **`Hertzbleed` (Wang, Paccagnella, He, Shacham, Fletcher, & Kohlbrenner,
   USENIX Security 2022; `CVE-2022-23823` Intel, `CVE-2022-24436` AMD):**
   Modern x86-64 and ARM processors employ **Dynamic Voltage and Frequency
   Scaling (DVFS)** (Intel Turbo Boost, AMD Precision Boost) to keep power
   consumption within package thermal design power (TDP) limits. Because switching
   transistors from `0` to `1` (Hamming distance) and holding `1`s (Hamming
   weight) in 64-bit ALU/multiplier datapaths consumes data-dependent dynamic
   and leakage power ($\Delta P \propto \mathsf{HW}(x) + \mathsf{HD}(x, y)$),
   sustained arithmetic on low-Hamming-weight values consumes less power than on
   high-Hamming-weight values, allowing the CPU to stay at a higher Turbo Boost
   clock frequency (in MHz). Wang et al. exploited this power-to-frequency
   conversion to mount a **remote timing attack** against two formally audited,
   strictly constant-time implementations of SIKE (Supersingular Isogeny Key
   Encapsulation) in Cloudflare's `CIRCL` (Go) and Microsoft's `PQCrypto-SIDH`
   (C): by crafting ciphertexts where a target secret key bit caused internal
   Montgomery ladder values to collapse to `0x0000...0000` (low Hamming weight,
   higher clock frequency, faster wall-clock completion), the attacker extracted
   the full SIKE secret key over the network despite zero branches, zero
   secret-dependent memory accesses, and zero variable-cycle instructions.
2. **`Augury` (Vicarte et al., IEEE S&P 2022) and `GoFetch` (Chen, Wang,
   Paccagnella,izi, Kohlbrenner, Payer, Fletcher, & Morrison, USENIX Security
   2024) on Apple Silicon Data Memory-Dependent Prefetchers (DMP):**
   Apple A14 and M1/M2/M3 processors include an undocumented hardware **Data
   Memory-Dependent Prefetcher (DMP)** attached to the L1/L2 cache hierarchy.
   Unlike classical stride or stream prefetchers (which inspect only the
   sequence of *load addresses*), a DMP inspects the **64-bit data values**
   loaded from memory into the cache/register file: whenever a loaded 64-bit
   word matches the bit-pattern heuristic of a valid virtual memory pointer
   within the process's address space, the DMP autonomously dereferences that
   value and prefetches the target cache line into L2—even if the program's
   instructions **never dereference, branch on, or index by that value**!
   While `Augury` (2022) initially believed DMP activation required specific
   array-of-pointers access patterns, `GoFetch` (March 2024) proved that standard
   loads of intermediate cryptographic state activate the DMP whenever a 64-bit
   secret-dependent intermediate value happens to collide with a valid pointer
   prefix. Using chosen inputs to steer intermediate values into pointer-shaped
   bit patterns and measuring L2 cache evictions (`Prime+Probe`) from an
   unprivileged co-located thread, `GoFetch` extracted complete secret keys from
   **constant-time** implementations of:
   - OpenSSL 3.x Diffie-Hellman key exchange,
   - Go's standard library `crypto/rsa` (2048-bit CRT decryption),
   - `CRYSTALS-Kyber` (`ML-KEM`), and
   - `CRYSTALS-Dilithium` (`ML-DSA`).
   On Apple M1 and M2 chips, the DMP cannot be disabled by software; mitigation
   requires either algorithmic operand blinding or setting the `DIT` (Data
   Independent Timing) / hardware chicken bit on Apple M3+ (`MSR DIT, #1`).

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

- **Hardware-contract boundaries in `TrustPolicy` and `ScopedVerificationResult`
  (`Trusted/Refinement.lean:418-456` and
  `anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`):**
  Software-level constant-time verification proves an architectural property of
  the ISA trace (`pc`, `addr`, `varLatencyOp`), **not** a physical silicon
  electromagnetic/DVFS or DMP prefetcher guarantee. If a verification framework
  conflates ISA trace noninterference with physical side-channel immunity, users
  are misled into deploying unblinded constant-time code on M1/M2 silicon where
  `GoFetch` extracts keys in under an hour.
- In Anneal's `ScopedVerificationResult` and `TrustPolicy`, any theorem that
  maps ISA-level trace equivalence (`ExecOut.trace`) to microarchitectural timing
  noninterference must carry an explicit, target-scoped `TrustedAssumption`—such
  as `.hardwareDataIndependentTiming_ARMv8_4_DIT` (requiring the `DIT` state bit
  to be set on entry in `ExecQuery.init` and hardware compliance with `DIT`
  semantics disabling DMP) and `.noDvfsPowerSideChannel`—audited by
  `TrustPolicy.isAllowed`. On M1/M2 targets where `DIT` does not disable the
  DMP, `policy.isAllowed .hardwareDataIndependentTiming_ARMv8_4_DIT` is `False`,
  forcing the cryptographic library to prove **value-blinding / pointer-prefix
  masking** in `theory/` so loaded 64-bit limbs never match virtual-address top
  bits.

### 2. Cryptographic Multi-Limb Arithmetic, Carry-Propagation, and Protocol State-Machine Failures

#### 2.1 Multi-Limb Carry-Propagation and Modular Reduction Bugs in OpenSSL, BoringSSL, `libgcrypt`, and `dalek`

Basis: documentation + source + derived.

High-performance public-key cryptography (RSA, Diffie-Hellman, X25519/Ed25519,
ECDSA over P-256/secp256k1) represents elements of large prime fields
$\mathbb{F}_p$ ($255$ to $4096$ bits) as arrays of 32-bit or 64-bit machine
words ("limbs"), using either saturated radixes ($2^{64}$) with hardware carry
flags (`CF` / `OF` via `adc`, `adcx`, `adox`, `mulx`) or unsaturated radixes
($2^{51}$ in 64-bit limbs or $2^{25.5}$ in 32-bit limbs) with delayed carry
propagation and conditional modular reduction. Because a carry out of an upper
limb occurs only when an intermediate limb equals $2^{64}-1$ (or $2^{51}-1$) and
receives an incoming carry—an event of probability $2^{-64}$ or $2^{-32}$ on
uniform random inputs—**random testing and differential fuzzing with uniform
inputs almost never exercise multi-limb carry-propagation bugs**:

1. **OpenSSL `bn_sqr8x_internal` Carry Overwrite (`CVE-2014-3570`):**
   In OpenSSL's hand-written x86-64 assembly squaring routine
   `bn_sqr8x_internal` (`crypto/bn/asm/x86_64-mont5.pl`), used whenever
   `BN_sqr` squared a multi-precision integer whose word length was divisible by
   8, a register spill/carry bug overwrote the carry flag (`CF`) before adding
   it into the next higher limb when a cross-product accumulation overflowed
   simultaneously with a diagonal square addition. The bug triggered with
   probability $\approx 2^{-64}$ per squaring operation, went undetected for
   years under millions of standard test vectors, and allowed an attacker to
   mount active fault/invalid-curve attacks against Diffie-Hellman and ECDH key
   exchanges to recover private key bits.
2. **OpenSSL `x86_64-mont5.pl` Montgomery Squaring Carry Bug (`CVE-2015-3193`):**
   Less than a year after `CVE-2014-3570`, differential fuzzing between OpenSSL
   1.0.2 and `libgcrypt` by Hanno Böck uncovered a second carry-propagation bug
   in `crypto/bn/asm/x86_64-mont5.pl` (`bn_sqr8x_mont` / `bn_mul4x_mont`) used
   by `BN_mod_exp` on Intel Broadwell/Haswell (`ADX`/`BMI2`) and standard
   x86-64 paths. During the final reduction step of 5-bit windowed Montgomery
   exponentiation, an unpropagated carry out of the most significant limb
   produced a corrupted modular power mod $N$. Because RSA with Chinese
   Remainder Theorem (`RSA-CRT`) computes $m_p = c^{d_p} \bmod p$ and
   $m_q = c^{d_q} \bmod q$ and combines them via Garner's formula, a single
   corrupted reduction in $m_p$ while $m_q$ is correct yields a signature $s'$
   satisfying $\gcd((s')^e - c, N) = q$—the classic **Bellcore (`Boneh-DeMillo-
   Lipton` 1997) single-fault RSA key recovery attack**, allowing a remote
   attacker who submits a crafted ciphertext/challenge triggering the $2^{-64}$
   carry edge case to factor the server's RSA modulus $N = p \cdot q$ in one
   query!
3. **`libgcrypt` Sliding-Window and Carry/Reduction Vulnerabilities
   (`CVE-2017-7526` & Differential Arithmetic Bugs):**
   In `libgcrypt` (used by GnuPG), Bernstein et al. (`CVE-2017-7526`) showed
   that the sliding-window modular exponentiation routine (`_gcry_mpi_powm`)
   leaked the complete sequence of squarings and multiplications—and sufficient
   information about the window multipliers—to recover 1024-bit and 2048-bit RSA
   secret keys via L1 cache bank conflict timing, while differential campaigns
   by Guido Vranken (`Cryptofuzz`) uncovered carry/reduction discrepancies across
   `libgcrypt`, OpenSSL, BoringSSL, and `mbedTLS` bignum routines.
4. **`curve25519-dalek` / `ed25519-dalek` Canonical Reduction, Scalar Bounds,
   and Double Public-Key Oracle Issues:**
   In pure-Rust cryptography, `curve25519-dalek` represents field elements
   modulo $p = 2^{255}-19$ in radix-$2^{51}$ (`FieldElement51([u64; 5])`) with
   explicit limb-bound invariants ($\forall i,\; l_i < 2^{51} + \epsilon$). Two
   classes of real-world vulnerabilities struck the `dalek` ecosystem:
   - **Limb-bound and constant-time compilation hazards:** Every field addition
     (`&a + &b`) adds limbs pointwise without carry propagation, increasing the
     limb bound from $2^{51}$ toward $2^{54}$. If a function omits an explicit
     `reduce()` call before a multiplication or serialization step whose
     tightness proof assumes 52-bit limbs, high bits overflow 128-bit
     intermediate accumulators (`u128`). This exact verification challenge
     motivated the formal verification of `curve25519-dalek`'s radix-$2^{51}$
     arithmetic using **Aeneas** (`Ho & Protzenko ICFP 2022`) and **Verus**.
   - **`ed25519-dalek` (< `v2.0.0`) Double Public-Key Signing Oracle:** In
     earlier versions of `ed25519-dalek`, the signing API accepted a caller-
     supplied public key $A$ alongside the secret key $s$ without re-deriving
     $A = [s]B$ or binding $s$ to $A$ in type invariants during deterministic
     nonce generation $r = H(\text{prefix} \parallel M)$ and challenge hashing
     $k = H(R \parallel A \parallel M)$: if a caller invoked `sign` twice on the
     same message $M$ with the same secret key $s$ but two different public key
     parameters $A_1 \neq A_2$, the deterministic nonce $r$ was identical ($R_1
     = R_2$) while the challenges $k_1 \neq k_2$ differed, giving the attacker
     two linear equations $S_1 = r + k_1 a \pmod \ell$ and
     $S_2 = r + k_2 a \pmod \ell$ and immediately solving for the secret scalar
     $a = (S_1 - S_2)(k_1 - k_2)^{-1} \bmod \ell$!
5. **How `Fiat-Crypto` (Erbsen et al., IEEE S&P 2019) and `CryptoLine` (Polyakov
   et al., CAV 2018) Solved Arithmetic Carry Bugs:**
   - **`Fiat-Crypto`** synthesizes saturated and unsaturated multi-limb C/Rust/
     Go/assembly routines from high-level prime-field specifications inside Coq
     using abstract interpretation over limb range intervals $[0, B_i]$,
     statically proving that no intermediate limb addition or multiplication can
     ever overflow machine word bounds.
   - **`CryptoLine`** verifies hand-written assembly (`x86_64-mont5.pl`,
     BoringSSL `fiat_curve25519`, NTT polynomial rings) by splitting each
     proof into an **algebraic polynomial ideal membership obligation**
     (checked via Singular/Gröbner bases over $\mathbb{Z}$) and a **bitvector
     range/carry no-overflow obligation** (checked via `Boolector`/`Bitwuzla`
     SMT solvers).

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

- **Universal query coverage (`WellFormedOn pre` + `Compiles`) vs. $2^{-64}$
  carry bugs:** In Anneal (`Trusted/Refinement.lean:347-372`), `L.sem s ≤
  L.SpecOn pre post` quantifies universally (`∀ q : L.Query`) over the entire
  input bitvector space. A $2^{-64}$ carry-propagation edge case is simply a
  specific `q₀ : L.Query` where the implementation produces a wrong value or
  overflows a limb bound.
- **Limb-bound invariants as `PartialBehaviorCodec.decodeOut`:** When verifying
  unsaturated radix-$2^{51}$ field arithmetic (`FieldElement51([u64; 5])`)
  against the mathematical prime field $\mathbb{F}_{2^{255}-19}$, `PartialBehaviorCodec`
  defines:
  - `decodeOut (limbs : [u64; 5]) : Option (ZMod (2^255 - 19))` to return
    `some (∑ i, limbs[i] * 2^(51*i) mod p)` **if and only if** every limb
    satisfies its declared headroom bound `limbs[i] < B_i` (and for canonical
    serialization outputs, `∑ i, limbs[i] * 2^(51*i) < 2^255 - 19`), and `none`
    otherwise!
  - If a routine omits a carry reduction and allows `limbs[i] ≥ B_i` on a
    $2^{-64}$ input `q₀`, `decodeOut` returns `none`, which falsifies
    `Compiles L_field L_mir codec.toMorphism spec_op mir_op` at `q₀`!
- **Enforcing `ed25519-dalek` key-pair coupling via `AdtInv` and
  `StepResult.externalCall`:** The `ed25519-dalek` double public-key bug is a
  classic **broken ADT invariant** where `Keypair { secret, public }` failed to
  enforce the coupling `public == derive_public(secret)` at the API boundary. In
  Anneal, attaching `AdtInv` (`public == derive_public(secret)`) to `Keypair` in
  `MirSemantics.lean` and checking `boundaryInv` at `StepResult.externalCall`
  prevents any safe caller or FFI boundary from constructing an uncoupled
  `(secret, public)` pair.

#### 2.2 Symbolic Protocol State-Machine and Timing Gaps: Needham-Schroeder (Lowe 1995), TLS `3SHAKE` (2014), WPA2 `KRACK` (2017), and TLS `Raccoon` (2020)

Basis: documentation + derived.

Even when underlying arithmetic primitives are 100% bug-free, cryptographic
protocols fail when their verification model makes an implicit closed-world or
idealized state-machine assumption that the real network environment violates:

1. **Needham-Schroeder Public-Key Protocol (1978) & Gavin Lowe's Man-in-the-
   Middle Attack (1995):**
   Needham and Schroeder's 3-message mutual authentication protocol:
   $$\begin{aligned}
   1.\quad A \to B &: \{N_A, A\}_{pk(B)} \\
   2.\quad B \to A &: \{N_A, N_B\}_{pk(A)} \\
   3.\quad A \to B &: \{N_B\}_{pk(B)}
   \end{aligned}$$
   was considered secure for **17 years** and was proved "correct" in Burrows-
   Abadi-Needham (**BAN**) logic (1989). In 1995, Gavin Lowe modeled the
   protocol in the CSP model checker **FDR** allowing an honest initiator $A$ to
   intentionally initiate a session with a compromised/malicious participant $I$
   while $I$ simultaneously impersonates $A$ to honest responder $B$:
   - $A \to I : \{N_A, A\}_{pk(I)}$
   - $I(A) \to B : \{N_A, A\}_{pk(B)}$ (re-encrypting $N_A, A$ under $B$'s key)
   - $B \to I(A) : \{N_A, N_B\}_{pk(A)}$
   - $I \to A : \{N_A, N_B\}_{pk(A)}$ ($A$ decrypts this, sees her own $N_A$,
     and returns $N_B$ encrypted under $I$'s key!)
   - $A \to I : \{N_B\}_{pk(I)}$
   - $I(A) \to B : \{N_B\}_{pk(B)}$ ($B$ concludes he is talking privately to
     $A$ with shared nonces $N_A, N_B$, which $I$ knows in full!).
   BAN logic missed the attack because its idealization rules assumed honest
   principals only ever initiate sessions with uncompromised principals (a
   **closed-world 2-party assumption**), and Message 2 $\{N_A, N_B\}_{pk(A)}$
   omitted the responder's identity $B$ (`Needham-Schroeder-Lowe` fixes Message
   2 to $\{N_A, N_B, B\}_{pk(A)}$).
2. **TLS `3SHAKE` Triple Handshake Attack (Bhargavan, Delignat-Lavaud, Fournet,
   Pironti, & Strub, IEEE S&P 2014):**
   Individual proofs of TLS 1.2 full handshakes, abbreviated session-resumption
   handshakes, and secure renegotiation (RFC 5746) held in isolation. However,
   by composing three handshakes across a client $C$, man-in-the-middle $M$, and
   honest server $S$, Bhargavan et al. showed that because the TLS 1.2 master
   secret `master_secret = PRF(pre_master_secret, "master secret", ClientRandom || ServerRandom)`
   depended only on the two nonces and **not on the full handshake transcript
   (specifically omitting the server's X.509 certificate)**, $M$ could forward
   `ClientRandom` and the abbreviated session-resumption ticket between $C \leftrightarrow M$
   and $M \leftrightarrow S$ so both sessions shared the **exact same `master_secret`
   and `Finished` verify data** while bound to different certificates, hijacking
   client-authenticated TLS renegotations. Fixing `3SHAKE` required RFC 7627
   (**Extended Master Secret**, binding the full session transcript hash into
   key derivation) and TLS 1.3's transcript-hashed key schedule.
3. **WPA2 `KRACK` Key Reinstallation Attack (Vanhoef & Piessens, ACM CCS 2017;
   `CVE-2017-13077`):**
   The IEEE 802.11i (WPA2) 4-way handshake was mathematically proved secure in
   the Bellare-Rogaway symbolic/computational model as an idealized 4-step
   exchange. In real networks, Wi-Fi frames can be lost, so the IEEE 802.11
   state machine specifies that if the Access Point (AP) does not receive
   **Message 4** from the client, the AP **retransmits Message 3**. Furthermore,
   to maintain layer separation, the 802.11 state machine tells the handshake
   module to install the Pairwise Transient Key (`PTK`) into the lower-layer
   `AES-CCMP` / `TKIP` data-confidentiality module via the `MLME-SETKEYS.request`
   primitive upon receiving Message 3. When a man-in-the-middle attacker blocked
   Message 4 from reaching the AP, the AP retransmitted Message 3; the client
   accepted the retransmitted Message 3 and called `MLME-SETKEYS.request` a
   **second time** with the same `PTK`. In Linux (`wpa_supplicant`), Android,
   iOS, Windows, and OpenBSD, reinstalling the `PTK` **reset the transmit
   packet number (nonce counter) and replay counter back to `1`**! Because the
   client had already transmitted data frames encrypted under `PTK` with nonces
   $1, 2, \dots, k$ after the first Message 3, resetting the nonce counter to
   `1` forced immediate **`AES-CCMP` / `GCM` nonce reuse** ($C_1 \oplus C_1' =
   P_1 \oplus P_1'$), completely breaking WPA2 encryption!
4. **TLS 1.2 `Raccoon` Timing Attack (Merget, Brinkmann, Aviram, Somorovsky,
   Mittmann, & Schwenk, USENIX Security 2020; `CVE-2020-1968`):**
   TLS 1.2 specification (RFC 5246 §8.1.2) mandated that in finite-field Diffie-
   Hellman (`DH` / `DHE`) key exchange, the negotiated shared secret $Z = g^{xy}
   \bmod p$ must have **all leading `0x00` bytes stripped** before being passed
   as the `pre_master_secret` into the HMAC-SHA256/SHA384 key derivation
   function (`PRF`). Because HMAC processes inputs in 64-byte (SHA-256) or
   128-byte (SHA-384) compression blocks, when stripping $k$ leading zero bytes
   shortened the total PRF input across a 64-byte/128-byte SHA block boundary,
   HMAC executed **one fewer SHA compression function call**! When a server
   reused an ephemeral or static DH key $g^y \bmod p$, an attacker could send
   chosen client shares $g^{x_i} \bmod p$, measure the server's response timing
   to detect when $g^{x_i y} \bmod p$ started with leading zero bytes (i.e.,
   $0 \le g^{x_i y} \bmod p < 2^{\text{bitlen}(p) - 8k}$), and solve the
   resulting **Hidden Number Problem (HNP)** via lattice reduction (`LLL`/`BKZ`)
   to recover the server's private key $y$ and decrypt the target TLS session.

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

- **Why `StepResult.externalCall boundaryInv next` (`Trusted/StepResult.lean` +
  `anneal-structural-external-calls-and-tcb-mutation-testing-2026`) is essential
  for protocol state machines:**
  Needham-Schroeder (Lowe 1995), `3SHAKE`, and `KRACK` are all **re-entrancy and
  cross-layer state-reset bugs**:
  - In `KRACK`, the 802.11 handshake state machine made an external call
    (`MLME-SETKEYS.request`) to the data-plane cipher module without enforcing a
    monotone key-epoch / non-reinstallation invariant, and the network input
    loop accepted re-entrant retransmissions of Message 3 in the `PTK-INIT-DONE`
    state.
  - In Anneal's operational semantics (`StepResult.externalCall boundaryInv next`),
    sending a network packet or invoking the crypto driver (`MLME-SETKEYS`) is
    an explicit `externalCall` step. Encoding the one-time nonce-monotonicity
    and key-installation latch (`¬ keyAlreadyInstalled(sessionId)`) inside
    `boundaryInv : Bool` and marking duplicate nonce reuse as `.failed .ub`
    (`defined = False`) causes `ReachesPrefix` to step immediately to `.failed`
    when a retransmitted Message 3 triggers a second `MLME-SETKEYS` call!
  - Similarly, for Needham-Schroeder and `3SHAKE`, `StepResult.externalCall`
    models the Dolev-Yao network adversary as an arbitrary open-world environment
    that can interleave, replay, and re-enter any public protocol endpoint with
    corrupted principals—the exact same open-world adversary quantified over by
    `open_world_callback_composition_sound` in
    `StructuralExternalCallAndCanaries.lean`!
- **Why `Raccoon`'s specification flaw highlights `PartialBehaviorCodec` +
  constant-time `Obs`:** RFC 5246's leading-zero stripping rule violated fixed-
  width representation invariance: a 256-byte field element $Z \in \mathbb{F}_p$
  was encoded into a variable-length byte slice whose length leaked the top bits
  of $Z$ into the SHA block-count observation trace `Obs`. In Anneal, fixed-
  length big-endian serialization (as adopted in TLS 1.3 RFC 8446 §7.4.1, which
  preserves all leading zero bytes) is a fixed-width bijection in
  `PartialBehaviorCodec` whose `Obs` trace length is constant across all
  $Z \in \mathbb{F}_p$.

### 3. Zero-Knowledge Proof (R1CS, Plonkish, AIR, and zkVM) Under-Constrained, Over-Constrained, and Transcript Vulnerabilities

#### 3.1 The Soundness–Completeness Anatomy of SNARK Bugs (Chaliasos et al. USENIX Security 2024 SoK)

Basis: documentation + source + derived.

In *"SoK: What Don't We Know? Understanding Security Vulnerabilities in SNARKs"*
(33rd USENIX Security Symposium, 2024, pp. 3855–3872), Chaliasos, Ernstberger,
Theodore, Wong, Jahanara, and Livshits analyzed **141 real-world vulnerability
reports** collected from 2018 to 2024 across the SNARK software stack (circuit
DSLs such as `Circom`, `Halo2`, `Noir`, `Cairo`, and `Arkworks`; zkEVMs; and
proof-system backends). Their central finding is that **over 90% of circuit-
layer vulnerabilities are under-constrained or over-constrained bugs caused by
the split between imperative witness generation and declarative polynomial
constraints**:

- In a SNARK DSL (such as `Circom`) or a zkVM (`RISC Zero`, `SP1`), a program is
  compiled into two distinct artifacts over a prime field $\mathbb{F}_p$:
  1. **The Witness Calculator ($W : \text{Input} \to \text{Option}(\mathbb{F}_p^m)$):**
     Imperative code (written in Circom `<--`, Rust, or C++) that computes values
     for the $m$ circuit wires given public and private inputs.
  2. **The Constraint System ($\mathcal{C} \subseteq \mathbb{F}_p^m$):** A set
     of R1CS (`(A·z) * (B·z) = (C·z)`), Plonkish custom-gate/lookup, or AIR
     polynomial equations (`===`) checked by the cryptographic verifier.
- A malicious prover **throws away the honest witness calculator $W$** and
  directly chooses any wire vector $\vec{z} \in \mathbb{F}_p^m$ that satisfies
  $\mathcal{C}$! Consequently:
  - **Under-Constrained Bug (Soundness Failure):** $W$ computes the intended
    wire assignment $\vec{z} \in \mathcal{C}$ on honest inputs, so all unit
    tests pass (`ProductiveOn` holds!), but $\mathcal{C}$ omits a polynomial
    equation or range check, allowing a malicious prover to supply a bogus wire
    assignment $\vec{z}' \in \mathcal{C}$ that projects to a false public
    statement (`Compiles` fails!).
  - **Over-Constrained Bug (Completeness / Liveness Failure):** $\mathcal{C}$
    includes an overly restrictive polynomial equation (e.g., requiring an
    intermediate difference to be non-zero when legitimate edge-case inputs make
    it zero), so for valid inputs $q$ satisfying `pre q`, **no** wire assignment
    $\vec{z} \in \mathcal{C}$ exists ($\mathcal{C}(q) = \emptyset$, violating
    `ProductiveOn` and permanently freezing user funds in a rollup bridge!).

#### 3.2 `Circomlib`, Tornado Cash, Semaphore, and Aztec 2.0 Under-Constrained & Alias Bugs

Basis: documentation + source + derived.

Concrete historical postmortems from `Circomlib`, Tornado Cash, Semaphore, and
Aztec 2.0 illustrate how subtle algebraic omissions in $\mathbb{F}_p$ turn into
total soundness breaks:

1. **`Circomlib` `Edwards2Montgomery` / `Montgomery2Edwards` Missing Division-by-
   Zero Constraint (`BabyJubJub`):**
   To speed up elliptic-curve point additions inside SNARK circuits,
   `Circomlib` converted points on the twisted Edwards curve `BabyJubJub`
   ($ax^2 + y^2 = 1 + dx^2y^2$ over the `BN254` scalar field $p \approx 2^{254}$)
   to its birationally equivalent Montgomery curve via the rational map:
   $$u = \frac{1 + y}{1 - y}, \qquad v = \frac{1 + y}{(1 - y) x}$$
   In `Circom`, division cannot be written directly inside a degree-2 R1CS
   constraint `===`, so `Edwards2Montgomery` computed the witness via `<--` and
   constrained it by multiplication:
   ```circom
   out[0] <-- (1 + in[1]) / (1 - in[1]);
   out[0] * (1 - in[1]) === 1 + in[1];
   out[1] <-- out[0] / in[0];
   out[1] * in[0] === out[0];
   ```
   Look at `out[1] * in[0] === out[0]`: when the input Edwards point has
   $x = \text{in}[0] = 0$ and $y = \text{in}[1] = -1 \pmod p$ (the point of
   order 2 on `BabyJubJub`), `1 + in[1] = 0`, so `out[0] = 0`. Then the second
   constraint becomes:
   $$\text{out}[1] \cdot 0 = 0$$
   which holds for **every** $\text{out}[1] \in \mathbb{F}_p$! A malicious
   prover could supply `in = (0, -1)` and set `out[1]` to **any arbitrary field
   element**, forging point additions and signatures.
2. **`Circomlib` `Num2Bits(254)` / `LessThan` Field-Aliasing Bug (`AliasCheck`)
   & Tornado Cash / Semaphore Nullifier Collisions:**
   On the `BN254` scalar field, the prime modulus $p$ is a 254-bit prime:
   $$p = 21888242871839275222246405745257275088548364400416034343698204186575808495617 < 2^{254} - 1$$
   When a circuit decomposes a field element $x \in \mathbb{F}_p$ into 254
   binary wires $b_0, \dots, b_{253} \in \{0, 1\}$ using `Num2Bits(254)`:
   $$x \equiv \sum_{i=0}^{253} b_i 2^i \pmod p$$
   every field element $x \in [0, 2^{254} - 1 - p]$ has **two distinct 254-bit
   binary representations** in $\mathbb{F}_p$: its canonical bit vector
   representing $x$, and its "aliased" bit vector representing $x + p < 2^{254}$!
   In early versions of `Circomlib` and downstream protocols (Tornado Cash note
   commitments/nullifiers and Semaphore identity commitments that hashed bit
   arrays via Pedersen hashes while exposing the field element $x$ as a public
   nullifier), omitting `AliasCheck` (which constrains $\sum_{i=0}^{253} b_i 2^i
   < p$) allowed an attacker to deposit **one** note with secret $x < 2^{254}-p$
   and withdraw **twice**—once using the bit decomposition of $x$ and once using
   the bit decomposition of $x + p$, yielding two distinct nullifiers from the
   same note!
3. **Tornado Cash `MiMC` Sponge & Governance / Circuit Postmortems:**
   In Tornado Cash and early `Circomlib` `MiMCSponge` usages, circuits that
   computed `MiMC` rounds or Merkle-tree path selectors without constraining
   intermediate state wires or selector bits ($s \cdot (s - 1) = 0$) allowed
   non-binary path indices ($s \notin \{0, 1\}$) to linearly interpolate left and
   right Merkle children:
   $$L' = (1 - s) \cdot L + s \cdot R$$
   enabling a prover to forge Merkle inclusion proofs for arbitrary un-deposited
   leaves unless $s \in \{0, 1\}$ was explicitly constrained.
4. **Aztec 2.0 Missing Range Check in Rollup Note Value Summation (2021/2022):**
   In Aztec 2.0's Plonkish rollup circuits, join-split notes represented token
   amounts as integers embedded in the `BN254` scalar field $\mathbb{F}_p$. While
   individual input/output notes had range checks in isolation, an inner/outer
   circuit path omitted a tight bit-length range check on a fee/value wire,
   allowing a prover to supply a negative value modulo $p$ ($p - v$) that wrapped
   around $\pmod p$ during note balance conservation ($v_{\text{in},1} +
   v_{\text{in},2} \equiv v_{\text{out},1} + v_{\text{out},2} \pmod p$),
   inflating token balances out of thin air before the bug was disclosed and
   patched via Plookup range tables.

#### 3.3 zkEVM and RISC-V zkVM Constraint & Bridge Vulnerabilities: Polygon zkEVM, Scroll, `RISC Zero`, and `SP1`

Basis: source + documentation + derived.

As zero-knowledge systems scaled from application-specific `Circom` circuits to
full Ethereum Virtual Machines (**Polygon zkEVM**, **Scroll**) and RISC-V Zero-
Knowledge Virtual Machines (**`RISC Zero`**, **`SP1`**), under-constrained and
boundary-binding bugs shifted to **CPU instruction decoding, memory-alignment
hints, cross-table `LogUp`/`Plookup` arguments, and receipt-verification APIs**:

1. **Polygon zkEVM & Scroll Plonkish/AIR Cross-Table & Limb-Range Bugs:**
   In zkEVMs, 256-bit EVM words (`U256`) are split into 8-bit, 16-bit, or 32-bit
   limbs across dedicated execution tables (Main State Machine, Binary SM,
   Arithmetic SM, Keccak SM, Storage SM) connected via permutation and lookup
   arguments (`Plookup` / `LogUp`). Audits and bug bounties in Polygon zkEVM and
   Scroll uncovered critical vulnerabilities where:
   - An arithmetic carry or byte-decomposition column in a secondary state
     machine calculated the limb split in the witness generator (`executor`)
     without adding the corresponding range-lookup inclusion constraint on the
     highest limb, allowing a forged carry to corrupt `ADDMOD`/`MULMOD` or
     `CALLDATA` byte-slicing; or
   - Selector polynomials guarding conditional lookup queries were not
     multiplied into both sides of the lookup identity, allowing an active row
     in the CPU table to match a disabled ("padding") zero row in the secondary
     precompile table.
2. **`RISC Zero` Under-Constrained 3-Byte Aligned Memory / `sys_div` Host-Oracle
   Hint Vulnerabilities & Receipt Binding Boundaries:**
   - **Host-Oracle / Unconstrained Witness Hints:** In `RISC Zero`'s RV32IM
     circuit, complex operations (such as division/remainder `divu`/`remu` or
     sub-word unaligned memory loads) obtain non-deterministic witness hints from
     the host emulator and check them inside the AIR constraints (for instance,
     checking $a = b \cdot q + r$ and $0 \le r < b$ for unsigned division). In a
     disclosed 2024 `RISC Zero` circuit vulnerability, an instruction/memory
     addressing path failed to fully constrain a low-bit alignment/remainder
     condition on witness advice columns, allowing a modified prover to supply a
     forged witness value that satisfied the AIR polynomial identities while
     diverging from true RV32IM instruction semantics.
   - **Receipt API Verification Boundaries (`reports/zkvm-receipt-binding-and-verification-boundaries`):**
     As documented directly in the reference corpus at
     `risc0/risc0@3bbcd44d6459b9ef6ac0df3846dc9215514934e8`
     (`risc0/zkvm/src/receipt.rs:152-206`), calling
     `verify_integrity_with_context` alone checks only cryptographic proof
     integrity and **does not constrain the guest `ImageID` or `Halted(0)` exit
     status** (`ReceiptClaim::ok` at `claim/receipt.rs:75-94`), nor does it
     discharge non-empty recursive verification assumptions (`claim/receipt.rs:426`).
     Moreover, `FakeReceipt::verify_integrity_with_context` (`receipt.rs:589-599`)
     returns `Ok` without cryptographic proof verification whenever `dev-mode` is
     enabled in `VerifierContext`.
3. **`SP1` (`succinctlabs/sp1`) Precompile Bridge, Verifying-Key Binding, and
   Mock Verifier Boundaries:**
   In `SP1` (`succinctlabs/sp1@02fa30185ecd658174b211d56128b14867ab8e81`),
   RISC-V `ecall` instructions delegate heavy cryptographic operations
   (`sha256_compress`, `keccak256`, `secp256k1_decompress`, `uint256_mul`) from
   the main CPU Stark chip to specialized precompile chips over a multi-table
   `LogUp` memory bus. Soundness requires that:
   - Every memory read/write timestamp and register value on the precompile bus
     matches the CPU table's state transition (`PartialBehaviorCodec` +
     `StepResult.externalCall`),
   - The `LogUp` sumcheck denominators $\sum_i \frac{m_i}{\alpha - t_i}$ cannot
     wrap around modulo the BabyBear/KoalaBear prime $p \approx 2^{31}$ when
     trace lengths approach $p$, and
   - On the SDK boundary (`crates/sdk/src/mock/mod.rs:88-109`), mock Plonk/
     Groth16 verification (`verify_mock_public_inputs` at `proof.rs:22-47`)
     ignores the requested `StatusCode` and accepts empty proof bytes whenever
     public hashes match.

#### 3.4 Fiat-Shamir Transcript Omissions: Trail of Bits **Frozen Heart** (2022)

Basis: documentation + derived.

Interactive zero-knowledge protocols (Σ-protocols, Bulletproofs, PlonK, STARKs)
are converted into non-interactive proofs (NIZKs / SNARKs) using the **Fiat-
Shamir heuristic** (Fiat & Shamir, CRYPTO 1986): instead of waiting for a live
verifier to sample a random challenge $e \xleftarrow{\$} \mathbb{F}_p$, the
prover computes $e = H(\text{Transcript})$ using a cryptographic hash function
or sponge (`Poseidon`, `Rescue`, `SHA-256`, `Merlin`/`Blake3`).

In April 2022, Trail of Bits (Jim Miller, Least Authority / Trail of Bits crypto
team) disclosed **Frozen Heart** ("The Most Dangerous Code in the World of Zero-
Knowledge"), a vulnerability class across numerous production PlonK,
Bulletproofs, and Schnorr/Girault proof implementations (including early versions
of Dusk Network's `plonk`, `bulletproofs` forks, and custom MPC threshold
wallets):

- **Technical Root Cause:** For the Fiat-Shamir transformation to be sound
  (preventing adaptive statement/witness manipulation in the Random Oracle Model),
  the hash transcript **must absorb all public inputs, public keys, circuit
  verification keys, and all round-1..$k$ prover polynomial commitments** before
  squeezing round-$k$ challenge scalar $\beta, \gamma, \alpha, \zeta \in
  \mathbb{F}_p$. In affected implementations, the prover hashed only the round
  commitments $H(A, B, C)$ and **omitted the public inputs $(x_1, \dots, x_\ell)$**
  (or omitted the commitment $R$ in Schnorr-style proofs) from the transcript!
- **Exploit:** Because the challenge scalar $\zeta$ did not depend on the public
  input $x$, a malicious prover could first generate a dummy commitment, compute
  the fixed challenge $\zeta = H(\text{commitments})$, and then algebraically
  solve the PlonK quotient polynomial identity *backward* for whatever false
  public input $x_{\text{forged}}$ balanced the equation at evaluation point
  $\zeta$—forging valid zero-knowledge proofs for arbitrary false statements in
  milliseconds without knowing any witness!

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

Anneal's four primitives provide a direct, mathematically airtight solution to
every ZKP failure class in §§3.1–3.4:

1. **Simultaneous Soundness (`Compiles`) + Completeness (`ProductiveOn`)
   (`Trusted/Refinement.lean` + `anneal-behavior-codec-and-progress-refinement-2026`):**
   Let `L_spec` be the high-level functional relation over fixed-width types
   (`BitVec 64`, `Point`), and let `L_circuit` be the constraint-system language
   whose programs are pairs $\langle \mathcal{C}, W \rangle$ and whose outcomes
   at input $q$ are wire assignments $\vec{z} \in \mathbb{F}_p^m$ satisfying
   $\mathcal{C}(q, \vec{z})$.
   - **`Compiles L_spec L_circuit codec.toMorphism spec ⟨C, W⟩` proves ZK
     Soundness (No Under-Constrained Bugs):** By definition of `Compiles`
     (`L_circuit.sem ⟨C, W⟩ ≤ codec.toMorphism (L_spec.sem spec)`), **every**
     satisfying wire vector $\vec{z} \in \mathcal{C}(q)$—even one crafted by a
     malicious prover bypassing $W$—must decode via `codec.decodeOut z` to
     `some o₁` satisfying `L_spec.sem spec q`!
   - **`ProductiveOn pre ⟨C, W⟩` & `InhabitedPre pre` prove ZK Completeness (No
     Over-Constrained Bugs):** If a circuit were over-constrained ($\mathcal{C}(q)
     = \emptyset$), `(L_circuit.sem ⟨C, W⟩ q).val h` would be the empty set
     `fun _ => False`, which refines every specification vacuously (`False →
     post q o`). Requiring `ProductiveOn pre ⟨C, W⟩` ($\forall q,\; \mathsf{pre}\;
     q \implies \exists h\;z,\; W(q) = \mathsf{some}\;z \land \mathcal{C}(q, z)$)
     forces the honest witness calculator $W$ to produce a valid satisfying
     assignment on every input in `pre`!
2. **Blocking `AliasCheck` and Missing Range Checks via `PartialBehaviorCodec`:**
   In `PartialBehaviorCodec`, `decodeOut : F_p^m → Option SpecOut` checks that
   every bit wire $b_i \in \{0, 1\}$, every $w$-bit limb wire is $< 2^w$, and
   every 254-bit bit-decomposition wire array satisfies $\sum_{i=0}^{253} b_i 2^i
   < p$. If a circuit omits `AliasCheck` or an Aztec-style note range check, a
   wire assignment $\vec{z} \in \mathcal{C}$ exists with $\sum b_i 2^i \ge p$,
   for which `decodeOut z = none`. Under `PartialBehaviorCodec.toMorphism`,
   `decodeOut z = none` maps to `False`, immediately refuting `Compiles`!
3. **Blocking `Frozen Heart` and Unconstrained Host Hints via
   `StepResult.externalCall boundaryInv next`:**
   In multi-phase Plonkish/STARK protocols and zkVMs (`RISC Zero`, `SP1`),
   sampling a Fiat-Shamir challenge from the transcript sponge or receiving an
   untrusted host-oracle hint (`sys_div`) is modeled as `StepResult.externalCall
   boundaryInv next`:
   - For Fiat-Shamir challenges, `boundaryInv : Bool` checks that the transcript
     state's absorbed message list equals the canonical prefix of `vk ||
     public_inputs || phase_1..k_commitments`. Any implementation that squeezes
     a challenge before absorbing `public_inputs` has `boundaryInv = false` and
     steps immediately to `.failed` (`Partial.ub`), catching **Frozen Heart** at
     compile/verification time!
   - For zkVM receipt and assumption tracking (`RISC Zero` `FakeReceipt` /
     unresolved recursive assumptions; `SP1` mock verifiers), `ScopedVerificationResult`
     and `TrustPolicy` (`Trusted/Refinement.lean:418-456`) ensure that any mock
     receipt or undischarged recursive assumption must appear as an explicit
     `TrustedAssumption` rejected by production `TrustPolicy`.

### 4. Quantitative Resource Bounds (WCET Timing Anomalies, Stack Overflows) and Wire-Format Parser Malleability

#### 4.1 Out-of-Order CPU Timing Anomalies (Lundqvist & Stenström RTSS 1999)

Basis: documentation + derived.

In hard real-time avionics, automotive braking/steering, and spacecraft control
software, verifying functional correctness is insufficient: the verifier must
establish a sound upper bound on **Worst-Case Execution Time (WCET)**. Classic
static WCET analyzers decompose a program into its control-flow graph (CFG) of
basic blocks, compute the worst-case cycle latency $T_{\max}(B_i)$ of each basic
block $B_i$ by assuming every ambiguous cache access is a **cache miss** (local
worst case), and solve an Implicit Path Enumeration Technique (`IPET`) integer
linear program to sum $\sum_i c_i T_{\max}(B_i)$ along the longest path.

In their landmark paper *"Timing Anomalies in Dynamically Scheduled
Microprocessors"* (20th IEEE Real-Time Systems Symposium, RTSS 1999, pp.
12–21), Thomas Lundqvist and Per Stenström proved that on out-of-order,
dynamically scheduled superscalar CPUs (such as PowerPC, modern Cortex-A/R, and
x86-64), **local worst-case latency does NOT imply global worst-case execution
time ($\Delta t_{\text{local}} < 0 \implies \Delta T_{\text{global}} > 0$)**:

1. **Concrete Counterexample (Cache Hit Causing Longer Total Execution Time):**
   Consider an out-of-order CPU with an L1 data cache (1-cycle hit, 10-cycle
   miss), a fast integer ALU (1 cycle), and a non-pipelined multi-cycle integer
   multiplier (`MUL`, 6 cycles, prioritized oldest-ready-first):
   - Instruction $I_1$: `LD r1, [addr]` (feeds $I_2$)
   - Instruction $I_2$: `MUL r2, r1, r3` (non-critical path; independent of loop
     exit)
   - Instruction $I_3$: `ADD r4, r5, r6` (delays $I_4$ by 2 cycles)
   - Instruction $I_4$: `MUL r7, r4, r8` (**critical path** feeding a long
     dependency chain $I_5 \to \dots \to I_k$)
   Compare the two executions:
   - **Case A ($I_1$ L1 Cache Miss — Local Slow Case, +9 cycles on $I_1$):**
     Because $I_1$ stalls for 10 cycles waiting for memory, $I_2$ is not ready at
     cycle 2. Instead, $I_3$ finishes at cycle 2 and critical-path instruction
     $I_4$ claims the non-pipelined multiplier at cycle 3, completing at cycle
     9 and allowing the critical path $I_5 \dots I_k$ to finish at **cycle 20**.
     Meanwhile, $I_2$ runs later in the shadow of the critical path.
   - **Case B ($I_1$ L1 Cache Hit — Local Fast Case, -9 cycles on $I_1$):**
     Because $I_1$ hits in cache at cycle 1, $I_2$ becomes ready at cycle 2—
     **one cycle before $I_4$**! Because $I_2$ is older and ready, the out-of-
     order scheduler dispatches non-critical $I_2$ to the non-pipelined
     multiplier at cycle 2, locking out critical-path instruction $I_4$ until
     cycle 8! The entire critical path shifts later, finishing at **cycle 25**
     (+5 cycles longer globally than the cache miss!).
2. **Domino Effects (Unbounded Amplification):**
   Lundqvist and Stenström further exhibited **domino timing anomalies** where a
   1-cycle local difference at loop entry alters hardware prefetcher or
   branch-predictor/pipeline phase alignment so that every subsequent loop
   iteration suffers an extra stall, making the global timing penalty
   proportional to the loop trip count $O(N)$.
3. **Why Compositional Basic-Block WCET Addition Fails:**
   Because the latency function $T(B_1 ; B_2)$ is **not monotone** in the local
   step latency of $B_1$ when microarchitectural pipeline/cache/reservation-
   station state $\mu$ is erased, any WCET verifier that abstracts a basic block
   to a single scalar cycle bound $[t_{\min}, t_{\max}] \in \mathbb{N}$ is
   **unsound** on out-of-order hardware! Sound static WCET tools (`aiT` by
   AbsInt) must instead propagate abstract microarchitectural states
   $\hat{\mu} \in \mathcal{P}(\text{CacheState} \times \text{PipelineState})$
   across every instruction step, retaining both the hit state and miss state at
   join points whenever they are incomparable.

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

- **Look at `ExecQuery` and `EventualBehaviorOf` (`Trusted/StepResult.lean:105-109`
  and `anneal-behavior-codec-and-progress-refinement-2026`):**
  In Anneal, `ExecQuery State` pairs `init : State` with `steps : Nat`, while
  `EventualBehaviorOf` abstracts away intermediate architectural instruction
  counts (`steps : Nat`) for functional partial/total correctness.
- **How to model sound WCET in Anneal:**
  1. Never equate architectural instruction step count `steps : Nat` in
     `ExecQuery` with wall-clock CPU cycles on an out-of-order core (`X86Semantics`),
     because deleting a `.nop` or turning a cache miss into a hit in
     `Peephole.lean` reduces `steps : Nat` while potentially *increasing*
     out-of-order cycle count due to a Lundqvist-Stenström timing anomaly!
  2. To verify hard real-time WCET in Anneal, either:
     - Target an **in-order, timing-compositional core** (such as ARM Cortex-M0+/
       M4 or an in-order RISC-V core without timing anomalies, recorded as an
       explicit `TrustedAssumption` in `TrustPolicy`) where per-instruction
       cycle bounds compose monotonically via a quantitative `Obs := Nat` cycle
       trace in `StepResult.step cycles next`; or
     - For out-of-order cores, include the abstract pipeline/cache state
       $\mu \in \text{MicroArchState}$ inside `SmallStepMachine.State` and use
       `StepResult.choice .demonic branches` (`Trusted/StepResult.lean:84`) to
       branch demonically over **both** the cache-hit successor state and the
       cache-miss successor state whenever cache residency is uncertain! Because
       `BehaviorOf` (`Trusted/StepResult.lean:172-183`) requires `defined` and
       `SpecOn` postconditions to hold across **all** reachable demonic branches
       (`∀ tr out, ReachesPrefix ... → post`), demonic branching over `{hit,
       miss}` automatically explores both Case A and Case B of the Lundqvist-
       Stenström anomaly without unsoundly dropping the cache-hit branch!

#### 4.2 Embedded Stack Overflow Disasters: Toyota ETCS-i Unintended Acceleration and `cargo-call-stack` Indirect/Interrupt Gaps

Basis: documentation + source + derived.

Unlike desktop/server operating systems that place unmapped virtual-memory guard
pages below thread stacks, bare-metal and RTOS-based embedded microcontrollers
(automotive ECUs, medical devices, flight controllers) run in a flat physical
address space without an MMU (or with an MPU disabled/misconfigured). When the
hardware stack pointer (`sp`) overflows its allocated RAM region, pushes and
local frame writes silently overwrite adjacent `.bss`/`.data` global variables
or RTOS kernel data structures:

1. **Toyota Electronic Throttle Control System (`ETCS-i`) Unintended
   Acceleration Postmortem (`Bookout v. Toyota` 2013; Michael Barr & Philip
   Koopman 2014):**
   During the 2013 litigation over unintended acceleration in the 2005 Toyota
   Camry (`89661-06C20` main CPU running the OSEK-compliant `vrtx`/NEC V850E1
   RTOS), embedded systems experts Michael Barr (Barr Group) and Prof. Philip
   Koopman (CMU) inspected the production ECM source code and testified to severe
   stack-safety failures:
   - Toyota's own internal stack-sizing link map calculated worst-case stack
     usage as **788 bytes out of 4,096 bytes (19%)**, but omitted **136 functions**
     (including recursive call chains and system calls) and underestimated task
     context-switch frames; actual static stack depth exceeded **94% of the
     allocated stack** before accounting for nested hardware interrupts (ISRs)
     and recursion!
   - Worse, the memory layout placed the **RTOS kernel's critical task-control
     and system tables directly adjacent to the bottom of the stack** with zero
     MPU guard region: when nested interrupts or recursive error handlers pushed
     `sp` past the 4,096-byte boundary, the stack overwrite corrupted the RTOS
     scheduler structures, killing the 8 ms / 65 ms throttle-angle control task
     while leaving the hardware PWM H-bridge driving the throttle motor open,
     and failing to trigger the watchdog timer because the timer-tick ISR
     continued servicing the hardware watchdog in interrupt context!
2. **Static Stack Analysis Blind Spots in Embedded Rust (`cargo-call-stack`):**
   In the embedded Rust ecosystem, tools such as `cargo-call-stack` compute
   worst-case stack usage by combining LLVM's `-Z emit-stack-sizes` section
   (`.stack_sizes`, which records each function's local stack frame size in
   bytes) with a static call-graph extracted from LLVM IR / ELF relocations.
   However, static call-graph extraction fails closed or silently under-
   approximates stack usage in three pervasive Rust patterns:
   - **Indirect Calls via Function Pointers and Trait Objects (`&dyn Trait` /
     `core::fmt`):** Formatting macros (`write!`, `panic!`) dispatch through
     `core::fmt::Arguments` function-pointer tables (`vtable`). Because LLVM IR
     represents the call as an indirect `call %fn_ptr`, `cargo-call-stack`
     cannot determine the concrete target from relocations alone and emits an
      unresolved `Dynamic` / unknown-cycle edge unless whole-program type-based
     call-graph refinement is provided.
   - **Compiler Intrinsic / `libcore` Formatting Cycles:** Panic handlers and
     integer/float formatting routines in precompiled `libcore` often contain
     apparent call-graph cycles (`fmt` $\to$ `pad` $\to$ `fmt`), making naive
     DAG longest-path stack summation return $\infty$ (unbounded) unless loop/
     recursion bounds are proved semantically.
   - **Asynchronous Interrupt Service Routine (ISR) Preemption:** On ARM
     Cortex-M (`NVIC`) and RISC-V (`CLIC`), up to $K$ priority levels of
     hardware interrupts can preempt the main thread at the exact instruction
     where the main thread's stack pointer is at its deepest peak, pushing $K$
     additional hardware exception frames (`8` or `26` words each, plus lazy
     FPU context stacking) plus all ISR call trees onto the same Main Stack
     Pointer (`MSP`).

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

- **Bounded stack frames in `Trusted/X86Semantics.lean` (`4f45f0a391a9`) and
  `BoundaryCanarySuite`:**
  In Anneal's `X86Semantics.lean` (hardened by `fixedX86Model` in
  `anneal-structural-external-calls-and-tcb-mutation-testing-2026`), every
  stack slot read/write checks `slot < maxFrameSlots` and every `call` checks
  stack-pointer alignment and remaining stack capacity (`sp ≥ frameBytes`); any
  stack overflow steps immediately to `.failed .ub` (`defined = False`).
- **Frame isolation and stack budgets across `StepResult.externalCall`:**
  When a function invokes an external or indirect callee via
  `StepResult.externalCall boundaryInv next`, `boundaryInv : Bool` can encode not
  only ADT invariants (`AdtInv`), but also the **remaining stack-budget
  precondition** `currentStackUsed + calleeMaxStack + isrReserve ≤ TotalStackSize`.
  If a callee's stack bound is not proved in Lean (for example, an external C
  function or an unverified ISR preemption reserve), that bound must be declared
  as an explicit, parameterized `TrustedAssumption` (`.externalStackBound "foo"
  256`) audited by `TrustPolicy` inside `ScopedVerificationResult`, making
  Toyota-style "136 omitted functions" impossible to hide inside a verified
  crate!

#### 4.3 Wire-Format Parser Malleability and Differential Bugs: Bitcoin DER (BIP-62/66), X.509 Null-Prefix (`CVE-2009-2408`), Android Master Key ZIP (`CVE-2013-4787`), and Android `Parcel` (`CVE-2014-7911`)

Basis: normative specification + documentation + source + derived.

Across network protocols, cryptographic ledgers, package managers, and OS IPC
boundaries (FFI/JNI), a **parser** decodes raw wire bytes $b \in \text{Bytes}$
into a structured domain value $v \in \text{Val}$, and a **serializer** encodes
$v$ back into bytes. When the decoding relation `decode : Bytes → Option Val` is
**non-injective** ($\exists b_1 \neq b_2,\; \mathsf{decode}(b_1) =
\mathsf{decode}(b_2) = \mathsf{some}\;v$) or when two subsystems use slightly
different decoders $\mathsf{decode}_A \neq \mathsf{decode}_B$ (**parser
differential**), catastrophic authentication and privilege-escalation exploits
follow:

1. **Bitcoin ASN.1 BER/DER Signature Malleability (Mt. Gox 2014; BIP-62 &
   BIP-66):**
   Prior to BIP-66 (activated July 2015), Bitcoin Core delegated ECDSA signature
   verification to OpenSSL's `d2i_ECDSA_SIG` ASN.1 parser. Instead of enforcing
   strict **Distinguished Encoding Rules (DER)**, OpenSSL accepted relaxed
   **Basic Encoding Rules (BER)** for the `(r, s)` signature tuple:
   - Arbitrary leading zero bytes (`0x00`) or negative-zero padding could be
     prepended to `r` or `s`;
   - Length fields could be encoded in multi-byte long form (`0x81 0x44` instead
     of `0x44`); and
   - Independently at the elliptic-curve layer (BIP-62), for every valid
     secp256k1 signature $(r, s)$, the pair $(r, n - s \pmod n)$ is also a
     mathematically valid ECDSA signature for the same message and public key!
   Because Bitcoin computed a transaction's unique identifier `txid =
   SHA256(SHA256(raw_tx_bytes))` over the **serialized wire bytes including the
   signature (`scriptSig`)**, any third party relay node on the peer-to-peer
   network could intercept an unconfirmed withdrawal transaction, pad the BER
   length/integer bytes or flip $s \mapsto n - s$, and broadcast the mutated
   transaction. The mutated transaction passed `ECDSA_verify` (same logical
   meaning!) and moved the coins to the same recipient, but had a **completely
   different `txid` hash**—causing exchange accounting databases that tracked
   withdrawals by `txid` to believe the withdrawal had failed and re-send the
   funds repeatedly (before SegWit BIP-141 moved witness data out of `txid` and
   BIP-66 enforced strict canonical DER).
2. **X.509 ASN.1 Null-Prefix Certificate Spoofing (`CVE-2009-2408` /
   `CVE-2009-2409`, Marlinspike & Kaminsky Black Hat 2009):**
   In ASN.1 DER (used by X.509 TLS certificates), string fields such as the
   Subject Common Name (`CN`) or Subject Alternative Name (`SAN`) are encoded as
   `(tag, length, bytes)` triples (`IA5String`, `UTF8String`, `PrintableString`),
   which may legally contain an embedded ASCII NUL byte (`0x00`) inside the
   explicit byte length. When an attacker requested a certificate from a
   commercial Certificate Authority (CA) for the domain string:
   $$\texttt{"www.bank.com\textbackslash 0.attacker.com"}\quad (\text{length} = 25)$$
   the CA's Pascal/Java/ASN.1 length-aware validation parser read the full
   25-byte string ending in `.attacker.com`, verified that the applicant owned
   `attacker.com`, and signed the X.509 certificate! When the attacker presented
   that signed certificate to a victim's web browser or SSL client (NSS, GnuTLS,
   OpenSSL, Windows CryptoAPI), the C client extracted the `CN` bytes into a
   `char *` buffer and called `strcmp` or `fnmatch` against the target hostname:
   because C strings are **NUL-terminated**, the client's hostname verifier
   stopped reading at `\0` and saw **`"www.bank.com"`**—accepting the
   certificate as valid for any bank or root domain on the Internet!
3. **Android "Master Key" ZIP Parser Differentials (`CVE-2013-4787` Bluebox
   Security, `CVE-2013-8619` Saurik):**
   Android application packages (`.apk`) are ZIP archives verified by a Java
   cryptographic signature verifier (`java.util.zip.ZipFile` in `PackageParser`)
   and then unpacked and installed by a privileged C++ daemon (`system/core/libziparchive`
   / `installd`). The ZIP file format places a **Central Directory (CD)** at the
   end of the file pointing to **Local File Headers (LFH)** scattered throughout
   the archive:
   - **Bug 1 (`CVE-2013-4787` Duplicate Central Directory Entries):** When an
     APK contained **two** Central Directory entries with the exact same
     filename `"classes.dex"`, Java's `ZipFile` stored entries in a
     `LinkedHashMap` (where the second entry overwrote the first, so the
     signature verifier checked the **second** benign `"classes.dex"`), whereas
     C++'s `ZipArchive` iterated linearly and extracted the **first** malicious
     `"classes.dex"`!
   - **Bug 2 (`CVE-2013-8619` Signed/Unsigned 16-Bit Field Length Overflow):**
     In the Local File Header, Java parsed the `extra field length` as a signed
     16-bit integer extended or handled differently from C++'s unsigned
     `uint16_t` offset calculation, allowing an attacker to make the Java
     signature verifier and C++ extractor read `"classes.dex"` from two
     completely different byte offsets within the same file!
4. **Android `Binder` `Parcel` Deserialization Mismatch (`CVE-2014-7911`,
    Jann Horn / Pangu Team):**
   In Android `< 5.0`, inter-process communication (`Binder` IPC) serializes
   `Bundle` / `ArrayMap` objects into a `Parcel` byte stream crossed between
   unprivileged app processes and the privileged `system_server` (`uid 1000`).
   When `ObjectInputStream` / `Parcel.readValue` deserialized a `Serializable`
   object inside `system_server`, it failed to verify that the class resolved by
   the receiver's classloader still satisfied `Serializable` invariants and matched
   the exact byte length consumed by the sender: by crafting a `Parcel` whose
   deserialized type confused `android.os.BinderProxy` fields with controlled
   64-bit pointers, an unprivileged app corrupted `BinderProxy.mObject` and
   achieved arbitrary native code execution inside `system_server` when the
   garbage collector ran `BinderProxy.finalize()`.

**Architectural Lesson for Anneal's 4 `trusted/` Primitives:**

Notice how **every single parser malleability and parser differential bug in
§4.3 is directly ruled out by Anneal's `PartialBehaviorCodec` (`anneal-behavior-codec-and-progress-refinement-2026`)**:

1. **Injectivity (`encodeOut_of_decodeOut`) Prohibits Signature & Transaction
   Malleability (BIP-62/66):**
   In `PartialBehaviorCodec`, the partial-bijection law:
   ```lean
   encode_of_decode_some : ∀ {o₁ : L₁.Out} {o₂ : L₂.Out},
     decodeOut o₂ = some o₁ → encodeOut o₁ = o₂
   ```
   states that if a wire byte sequence `o₂` is accepted by the parser
   (`decodeOut o₂ = some o₁`), then `o₂` **must equal the unique canonical
   serialization `encodeOut o₁`**!
   - Suppose two distinct byte strings $b_1 \neq b_2$ (such as a canonical DER
     signature and a BER leading-zero-padded signature, or $(r, s)$ and
     $(r, n - s)$) both decoded to `some sig`. Then by `encode_of_decode_some`,
     $b_1 = \mathsf{encodeOut}(\mathsf{sig}) = b_2$, contradicting $b_1 \neq
     b_2$!
   - Thus, **it is mathematically impossible to construct a `PartialBehaviorCodec`
     for a non-canonical or malleable parser**! Any non-canonical wire encoding
     (extra leading zeros, long-form lengths, high-$S$ signatures, duplicate ZIP
     central directory entries, or trailing unconsumed bytes) **must** map to
     `decodeOut b = none`.
2. **Round-Trip Identity (`decode_encode_out`) and Common Spine (`obs_decodeOut`)
   Prohibit Parser Differentials (`CVE-2009-2408`, `CVE-2013-4787`,
   `CVE-2014-7911`):**
   - In `CVE-2009-2408` (X.509 NUL prefix), the ASN.1 string `"bank.com\0.bad.com"`
     cannot round-trip through a C NUL-terminated string type `CStr`: either
     `CStr` forbids interior `\0` bytes (so `decodeOut` returns `none` on any
     ASN.1 string containing `0x00`), or `encode_of_decode_some` fails because
     truncating at `\0` loses `.bad.com`.
   - When two subsystems (such as a signature verifier $V$ and an installer $I$
     in Android Master Key, or a Rust caller and C++ FFI callee across a `Parcel`
     boundary) communicate over a wire format $L_{\text{wire}}$, requiring both
     $V$ and $I$ to refine the **same** `PartialBehaviorCodec L_domain L_wire`
     forces both parsers to agree on the exact `some`/`none` domain and the
     exact decoded value `o₁` for every byte sequence $b \in \text{Bytes}^*$,
     eliminating parser differentials by transitivity.

#### 4.4 Cross-Domain Synthesis Matrix: Mapping Historical Failures to Anneal's 4 Trusted Primitives

| Historical Failure / CVE / Paper | Domain | Technical Root Cause | Violated Formal Property | Anneal `trusted/` Primitive That Blocks or Isolates It |
| :--- | :--- | :--- | :--- | :--- |
| **Compiler CT Violations** (Kaufmann CANS 2016; Simon EuroS&P 2018; `CVE-2024-58262`) | Crypto / Compilers | `MSVC`/`LLVM`/`GCC` rewrite bitwise masks `(a & m) \| (b & ~m)` into branches & delete `memset` | Value-only refinement (`Obs = Unit`) ignores `PC` and stack-spill traces | `StepResult.step obs next` (`Obs` tracks `pc` + `addr`) + single-source `.olean`-bound x86 codegen |
| **`KyberSlash1` & `KyberSlash2`** (Bernstein et al.; Tamvada et al. Dec 2023) | Post-Quantum Crypto (`ML-KEM`) | Secret polynomial coefficients divided by $q=3329$ via variable-latency `idiv`/`udiv` | Leakage model `Obs` tracked only `PC`/`Addr`, omitting instruction operand latency $\lambda$ | `X86LeakageObs.varLatencyOp` in `StepResult` + relational trace equivalence |
| **`Hertzbleed` (`CVE-2022-23823`) & `GoFetch` (USENIX Sec 2024)** | Microarchitectural Side Channels | DVFS power throttling (SIKE) & Apple M1–M3 DMP dereferencing pointer-shaped secret data | Silicon violates ISA constant-time assumption without `DIT` / operand blinding | `TrustPolicy` / `ScopedVerificationResult` explicit `.hardwareDIT` assumption + blinding in `theory/` |
| **OpenSSL Carry Bugs** (`CVE-2014-3570`, `CVE-2015-3193`) & `dalek` Limb Bounds | Multi-Limb Arithmetic | $2^{-64}$ carry-flag overwrite in `bn_sqr8x_internal` / `x86_64-mont5.pl` enabling Bellcore RSA fault attack | Testing missed $2^{-64}$ inputs; unverified carry/headroom invariant across limbs | Universal query coverage (`WellFormedOn`) + `PartialBehaviorCodec.decodeOut` checking limb bounds |
| **Needham-Schroeder (Lowe 1995), `3SHAKE` (2014), `KRACK` (`CVE-2017-13077`), `Raccoon`** | Crypto Protocols (TLS, WPA2) | Closed-world 2-party model, missing transcript hash, Message 3 retransmission resetting nonces, DH zero-stripping | Unguarded re-entrant callbacks & variable-length secret encoding | `StepResult.externalCall boundaryInv` (enforcing monotone nonce latch) + fixed-width `PartialBehaviorCodec` |
| **SNARK Under-Constrained & Alias Bugs** (`Circomlib`, Tornado Cash, Aztec 2.0, Chaliasos SoK 2024) | Zero-Knowledge Proofs (R1CS / Plonkish) | `<--` witness generator works (`ProductiveOn`), but `===` omits $x \neq 0$, `AliasCheck` ($< p$), or limb range check | Target constraint set $\mathcal{C}$ is wider than source spec (`¬ Compiles`) | `Compiles` (soundness) + `ProductiveOn` (completeness) + `PartialBehaviorCodec` (`decodeOut = none` on $\ge p$) |
| **zkVM Host-Hint & Receipt Bugs** (`RISC Zero`, `SP1`, Polygon zkEVM, Scroll) | RISC-V zkVMs & zkEVMs | Under-constrained host division/alignment hints; `verify_integrity` omitting `ImageID`; `FakeReceipt` dev mode | Unchecked oracle return & unverified receipt configuration assumptions | `StepResult.externalCall` post-hint constraints + `ScopedVerificationResult` rejecting mock/dev assumptions |
| **Trail of Bits `Frozen Heart` (2022)** | Fiat-Shamir NIZKs / PlonK / Bulletproofs | Public inputs omitted from Fiat-Shamir hash transcript before squeezing challenge $\zeta$ | Challenge sampled before public statement & commitments bound to sponge | `StepResult.externalCall boundaryInv` requiring full transcript absorption before challenge squeeze |
| **Out-of-Order WCET Timing Anomalies** (Lundqvist & Stenström RTSS 1999) | Hard Real-Time WCET | Local L1 cache *hit* lets non-critical `MUL` seize functional unit, delaying critical path (+5 cycles vs. miss) | Local cycle latency is non-monotone when pipeline/cache state $\mu$ is erased | `StepResult.choice .demonic` branching over `{hit, miss}` microarchitectural states; `EventualBehaviorOf` separation |
| **Toyota ETCS-i Stack Overflow (2013) & `cargo-call-stack` Unknowns** | Embedded RTOS & Static Stack Bounds | 136 functions omitted from link map; nested ISRs + recursion overflow stack into RTOS globals; indirect vtable calls | Unbounded/unverified stack depth across indirect calls and interrupts | `X86Semantics.lean` bounded stack-frame checks + `StepResult.externalCall` stack-budget invariants |
| **Bitcoin DER (BIP-62/66), X.509 `\0` (`CVE-2009-2408`), Android Master Key (`CVE-2013-4787`), `Parcel` (`CVE-2014-7911`)** | Wire Formats, Parsers & FFI/IPC | Non-canonical BER padding/high-$S$ mutates `txid`; ASN.1 `\0` vs. C `strcmp`; duplicate ZIP CD entries; JNI `Parcel` mismatch | Parser `decode` is non-injective (`¬ encodeOut_of_decodeOut`) or differs across languages | `PartialBehaviorCodec` injectivity (`encode_of_decode_some`) + fail-closed `decodeOut = none` on non-canonical bytes |

## Boundaries

To prevent future agents from over-generalizing the findings in this report, the
following boundaries distinguish what is established from what remains outside
scope:

- **Not examined (Physical EM / Power Analysis and Fault-Injection Physics):**
  While this report covers software-visible microarchitectural side channels
  (`KyberSlash` instruction timing, `Hertzbleed` DVFS frequency throttling, and
  `GoFetch` DMP cache prefetching), it does **not** examine physical
  oscilloscope Differential Power Analysis (DPA), Electromagnetic (EM) probe
  side channels, or laser/voltage-glitch hardware fault injection (beyond the
  software-triggered Bellcore RSA-CRT carry bug in `CVE-2015-3193`).
- **Known not to apply (ISA Constant-Time $\neq$ Apple M1/M2 DMP Immunity):**
  Proving that a compiled binary has secret-independent `PC`, memory addresses,
  and instruction-operand latencies in Anneal's `SmallStepMachine` is **known
  not to apply** as a guarantee against Data Memory-Dependent Prefetcher (DMP)
  key extraction on Apple M1 and M2 processors (`GoFetch`), because the M1/M2
  DMP inspects 64-bit register/cache *values* loaded from memory and cannot be
  disabled via architectural state bits. Mitigating `GoFetch` on M1/M2 requires
  algorithmic blinding or pointer-prefix masking in the program's data
  representation.
- **Known not to apply (Architectural Step Count $\neq$ Out-of-Order WCET):**
  By Lundqvist and Stenström's theorem (RTSS 1999), reducing the architectural
  instruction step count `steps : Nat` in `ExecQuery` (or via `DilationCodec` in
  `Peephole.lean`) is **known not to apply** as a proof of reduced worst-case
  wall-clock cycle latency on out-of-order superscalar processors with shared
  non-pipelined functional units or speculative cache effects.
- **Unsupported in current `Trusted/X86Semantics.lean` (`4f45f0a391a9`):**
  The current `X86Semantics.lean` on `mir-to-x86` sets `Obs := Unit` and models
  architectural registers and bounded stack slots without microarchitectural
  cache/pipeline state, hardware interrupt preemption frames, or a built-in
  `.varLatencyOp` observation constructor. Extending `X86Semantics.lean` to emit
  constant-time leakage observations or cycle-accurate in-order WCET traces
  requires instantiating the parameterized `Obs` type in `SmallStepMachine`.

## Evidence

### 1. Anneal Repository Coordinates (`joshlf/anneal`)

- **Core Refinement, Partial Behaviors, and Trust Policy (`trusted-core` at
  `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`):**
  - `trusted/lean/Trusted/Refinement.lean` (blob
    `7a81836536870398a6d0846474b08ceadf8402c3`, lines 208–472): `Preorder`,
    `Partial` (`defined`, `val`, `Partial.ub`), `Behavior`, `Language`,
    `SpecOn`, `WellFormedOn`, `Compiles` (`L369–372`), `Abstracts` (`L381–384`),
    `Compiler.SoundOn`, `Compiler.Verified`, `TrustedAssumption`, `TrustPolicy`,
    and `VerificationResultOn` (`L444–456`).
  - `trusted/lean/Trusted/StepResult.lean` (blob
    `4805cf0c30910890eb5914957776d7a26c52ef0c`, lines 58–199):
    `TerminationKind`, `StepResult`, `PrefixOutcome`, `ExecQuery`, `ExecOut`,
    `SmallStepMachine`, `ReachesPrefix` (`.emptyChoice`, `.noStep` transitioning
    to `.stuck`), and `BehaviorOf`.
- **MIR-to-x86-64 Target Semantics (`mir-to-x86` at
  `4f45f0a391a921ced9c9dc773b9a040dbc215d14`):**
  - `trusted/lean/Trusted/X86Semantics.lean` (lines 24–343, 650–896): `X86Val`,
    `X86State`, `X86Instr` (`idiv`/`udiv`, ALU ops), `X86Machine`, and
    `EnsuresRetLibInv`.
  - `theory/Anneal/Compiler/NaiveCodegen.lean` & `Peephole.lean`: 2-stage
    lowering and peephole optimization passes.
- **Reference Corpus Hardening Packages (`zerocopy/reference` at
  `df55c524a051d59e7dd35564f282b30d29133392`):**
  - `reports/anneal-behavior-codec-and-progress-refinement-2026/`:
    `PartialBehaviorCodec` (`decodeOut : L₂.Out → Option L₁.Out`,
    `decode_encode_out`, `encode_of_decode_some`), `EventualBehaviorOf`,
    `ProductiveOn`, and `CertifiedOptimizationPass`.
  - `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/`:
    `StepResult.externalCall (boundaryInv : Bool) (next : State → Obs → Prop)`
    (`support/StructuralExternalCallAndCanaries.lean:148-236`) and
    `BoundaryCanarySuite` (`L2570-2655`).
  - `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/`:
    `TCBModel`, `refTCBModel`, `BoundaryCodec`, and `ScopedVerificationResult`
    (`support/ProofGatedCompilationAndTrustPolicy.lean`).
  - `reports/security-observations-and-relational-compiler-preservation/` &
    `reports/zkvm-receipt-binding-and-verification-boundaries/`:
    `ct-verif` (Almeida et al. USENIX Security 2016), `Jasmin`
    (`34f15840f10625bbc2cbf59b3d877e94c75bfbd9`), `risc0/risc0`
    (`3bbcd44d6459b9ef6ac0df3846dc9215514934e8`), and `succinctlabs/sp1`
    (`02fa30185ecd658174b211d56128b14867ab8e81`).

### 2. Primary Literature, CVEs, and Postmortem Sources

- **Compiler Constant-Time & Microarchitectural Side Channels:**
  - Thierry Kaufmann, Hervé Pelletier, Serge Vaudenay, & Karine Villegas, *"When
    Constant-Time Source Yields Variable-Time Binary: Exploiting
    Curve25519-donna Built with MSVC 2015"*, CANS 2016, LNCS 10052, pp. 573–582.
  - Laurent Simon, David Chisnall, & Ross J. Anderson, *"What You Get Is What
    You C: Controlling Side Effects in Mainstream C Compilers"*, IEEE EuroS&P
    2018, pp. 1–15.
  - Moritz Schneider, Daniele Lain, Ivan Puddu, Nicolas Dutly, & Srdjan Čapkun,
    *"Breaking Bad: How Compilers Break Constant-Time Implementations"*, 2024;
    `CVE-2024-58262` (Rust `cmov` / LLVM backend branch optimization).
  - Daniel J. Bernstein, Karthikeyan Bhargavan, Shivam Bhasin, Anupam Chattopadhyay,
    et al., *"KyberSlash: Exploiting Secret-Dependent Division Timings in Kyber
    Implementations"* (`https://kyberslash.cr.yp.to/`, Dec 2023 / 2024).
  - Yingchen Wang, Riccardo Paccagnella, Elizabeth Tang He, Hovav Shacham,
    Christopher W. Fletcher, & David Kohlbrenner, *"Hertzbleed: Turning Power
    Side-Channel Attacks Into Remote Timing Attacks on x86"*, USENIX Security
    2022, pp. 679–697 (`CVE-2022-23823`, `CVE-2022-24436`).
  - Jose Rodrigo Sanchez Vicarte et al., *"Augury: Using Data Memory-Dependent
    Prefetchers to Leak Data at Rest"*, IEEE S&P 2022, pp. 1491–1505.
  - Boru Chen, Yingchen Wang, Pradyumna Shome, Christopher W. Fletcher, David
    Kohlbrenner, Riccardo Paccagnella, & Daniel Genkin, *"GoFetch: Breaking
    Constant-Time Cryptographic Implementations Using Data Memory-Dependent
    Prefetchers"*, USENIX Security 2024 (`https://gofetch.fail/`).
- **Cryptographic Arithmetic & Protocol Postmortems:**
  - OpenSSL Security Advisories `CVE-2014-3570` (`bn_sqr8x_internal`) and
    `CVE-2015-3193` (`crypto/bn/asm/x86_64-mont5.pl`); `libgcrypt`
    `CVE-2017-7526`.
  - Andres Erbsen, Jade Philipoom, Jason Gross, Robert Sloan, & Adam Chlipala,
    *"Simple High-Level Code For Cryptographic Arithmetic — With Proofs, Without
    Compromises"* (`Fiat-Crypto`), IEEE S&P 2019, pp. 1202–1219.
  - Yu-Fu Fu, Jiaxiang Liu, Xiaomu Shi, Ming-Hsien Tsai, Bow-Yaw Wang, & Bo-Yin
    Yang, *"Signed Cryptographic Program Verification with Typed CryptoLine"*,
    ACM CCS 2019 / CAV 2018.
  - Gavin Lowe, *"An Attack on the Needham-Schroeder Public-Key Authentication
    Protocol"*, Information Processing Letters 56(3):131–133, 1995.
  - Karthikeyan Bhargavan, Antoine Delignat-Lavaud, Cédric Fournet, Alfredo
    Pironti, & Pierre-Yves Strub, *"Triple Handshakes and Cookie Cutters:
    Breaking and Fixing Authentication over TLS"* (`3SHAKE`), IEEE S&P 2014,
    pp. 98–113; IETF RFC 7627.
  - Mathy Vanhoef & Frank Piessens, *"Key Reinstallation Attacks: Forcing Nonce
    Reuse in WPA2"* (`KRACK`), ACM CCS 2017, pp. 1313–1328 (`CVE-2017-13077`).
  - Robert Merget et al., *"Raccoon Attack: Finding and Exploiting
    Most-Significant-Bit-Oracles in TLS-DH(E)"*, USENIX Security 2020
    (`CVE-2020-1968`).
- **Zero-Knowledge Proof Vulnerabilities:**
  - Stefanos Chaliasos, Jens Ernstberger, David Theodore, David Wong, Mohammad
    Jahanara, & Benjamin Livshits, *"SoK: What Don't We Know? Understanding
    Security Vulnerabilities in SNARKs"*, USENIX Security 2024, pp. 3855–3872.
  - Trail of Bits (Jim Miller et al.), *"Coordinated Disclosure of the Frozen
    Heart Vulnerability in Girault, PlonK, and Bulletproofs"*, April 2022.
- **WCET, Stack Analysis, and Parser Malleability:**
  - Thomas Lundqvist & Per Stenström, *"Timing Anomalies in Dynamically
    Scheduled Microprocessors"*, 20th IEEE RTSS 1999, pp. 12–21.
  - Michael Barr, *"Bookout v. Toyota Motor Corp. Trial Testimony and Expert
    Report on Camry ETCS-i Software"*, Oct 2013; Philip Koopman, *"A Case Study
    of Toyota Unintended Acceleration and Software Safety"*, Sept 2014.
  - Bitcoin Improvement Proposals BIP-62 (*"Dealing with Malleability"*) and
    BIP-66 (*"Strict DER Signatures"*); X.509 Null-Prefix `CVE-2009-2408`;
    Android Master Key `CVE-2013-4787` & `CVE-2013-8619`; Android `Parcel`
    `CVE-2014-7911`.

## Revalidation

To revalidate the architectural guarantees linking these historical failure modes
to Anneal's codebase when `trusted/lean/` or `theory/` evolves:

1. **Codec Injectivity & Non-Malleability Check (`PartialBehaviorCodec`):**
   Verify that any `PartialBehaviorCodec` used for wire formats, multi-limb
   field arithmetic, or ZKP witness decoding retains `encode_of_decode_some`
   (injectivity on `some`) and `decode_encode_out` by running the Lean 4 kernel
   over `reports/anneal-behavior-codec-and-progress-refinement-2026/support/BehaviorCodecExpressiveness.lean`:
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-behavior-codec-and-progress-refinement-2026/support/BehaviorCodecExpressiveness.lean
   ```
2. **Re-Entrant External Call & Target Guard Canary Check
   (`StepResult.externalCall` & `BoundaryCanarySuite`):**
   Verify that mid-call invariant violations (`KRACK`/`ed25519-dalek`/`Frozen
   Heart` pattern) and target x86-64 division/stack-overflow guards remain
   refuted by running:
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/support/StructuralExternalCallAndCanaries.lean
   ```
3. **Scoped Assumption Isolation Check (`ScopedVerificationResult`):**
   Verify that waiving a hardware side-channel or cryptographic hardness
   assumption (`GoFetch` DMP, `Hertzbleed` DVFS, or LWE/KZG) cannot explode
   unwaived obligations via `False.elim`:
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/support/ProofGatedCompilationAndTrustPolicy.lean
   ```
