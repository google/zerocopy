# Coalition-Presheaf Information Flow, Relational Hyperproperty Compilation, and Post-Zeroization Forward Secrecy

## Summary

Standard single-trace compiler correctness (`Beh_T(C(P)) subseteq Beh_S(P)`) preserves trace properties (1-safety and liveness) but is fundamentally insufficient for multi-party confidentiality, cross-module link-time optimization (LTO), and post-zeroization forward secrecy:

1. **Trace-relating compilation and the low-equivalence functionality criterion:** Under Abate et al.'s trace-relating compiler correctness framework (`ESOP 2020`, extended in `ACM TOPLAS 43(4):14, 2021`, DOI `10.1145/3460860`), an arbitrary trace relation `~ subseteq Tr_S x Tr_T` induces a Galois connection `(tau_tilde -| sigma_tilde)` mapping source properties to target guarantees, while robust preservation of `k`-hypersafety (`R^kHSP`, including 2-safety noninterference `R2HSP`) across distinct observation domains holds if and only if `~` is **low-equivalence functional** (equivalently, target leakage is a secret-independent function `F` of source leakage, matching Barthe et al.'s constant-time compiler preservation theorems in CSF 2018 and CompCertCT POPL 2020). Exhaustive enumeration of all `512` binary trace relations over 3-trace spaces confirms `0` 2-safety violations across all `95` low-equivalence-functional relations and exhibits minimal non-functional counterexamples.
2. **Coalition-presheaf observation lattices resolve mixed TEE/MPC/FHE LTO conflicts:** Indexing observations by individual principals fails under multi-party collusion (e.g., 2-out-of-2 additive secret sharing over `Z_4` has statistical distance `0.0` for `{B}` and `{C}` individually yet `1.0` for `{B, C}`), whereas a monolithic global plaintext observation floor is mathematically incompatible with blind FHE/MPC evaluators, and an unconstrained per-principal `Unit` floor opens trivial erasure exploits (`Eval(ct) := 0`). Modeling observations as a contravariant **coalition presheaf** `O : P(Pi)^op -> Obs` governed by dual bounds—**Lower-Bound Joint Authorized Output Faithfulness** on `Pi_out` and **Upper-Bound Adversarial Coalition Simulator Ceilings** across `C in A`, composed via a concrete-security advantage quantale—eliminates both flaws. During cross-module LTO, coarsening modules to a common meet `kappa_1 meet kappa_2` causes the **LTO Refinement Paradox** (resolving helper nondeterminism using a secret satisfies 1-trace refinement while leaking with probability `1`); LTO must instead optimize over the coalition-wise **product presheaf** `(O_1 (x)_P O_2)(C) = O_1(C) x O_2(C)` with virtual-boundary claim re-anchoring.
3. **Post-zeroization forward secrecy fails across compiler spill slots, callee-saved registers, time-travel logs, and CoW storage:** Source-level memory erasure (`RustCrypto/utils` `zeroize` v1.9.2 or ISO C23 `memset_explicit`) defeats dead-store elimination (DSE) on the explicitly named buffer only. Direct inspection of LLVM `PEIImpl::insertZeroCallUsedRegs` (`PrologEpilogInserter.cpp:1209-1352`) and live x86-64 compilation with `gcc 15.2.0 -O2 -std=c23 -fzero-call-used-regs=used` prove that even with both `memset_explicit` and caller-saved register clearing enabled, the compiler spills secret-derived vector state into an unzeroed 16-byte stack slot at `(%rsp)` that survives function return. Formally verified stack-frame zeroization (`jasmin-lang/jasmin`, `it_compile_prog_to_asmP` + `zeroized_u`) closes intra-frame stack persistence down to assembly (including `LFENCE`-hardened `SZSloopSCT`), yet post-zeroization forward secrecy as a relational 2-safety hyperproperty still fails unless non-recording execution isolation (blocking `rr` / Intel PT / core dumps / swap) and ephemeral-key cryptographic erasure over copy-on-write (CoW) filesystems and SSD Flash Translation Layers (FTLs) are enforced jointly.

## Applicability

This report combines formal compilation theory, multi-party cryptographic observation models, upstream compiler/library source audits, and executable probes:

- **Secure compilation & hyperproperty theory:** Clarkson & Schneider (*Hyperproperties*, JCS 2010), Abate et al. (*Journey Beyond Full Abstraction*, IEEE CSF 2019; *Trace-Relating Compiler Correctness and Secure Compilation*, ESOP 2020 / ACM TOPLAS 2021—note that the journal extension appeared in ACM TOPLAS, not JACM), Barthe, Grégoire, Laporte (IEEE CSF 2018), and Barthe et al. (*CompCertCT*, ACM POPL 2020).
- **Multi-party coalition and authority models:** Hirt & Maurer (*General Adversary Structures*, J. Cryptology 2000), Canetti (*Universally Composable Security*, JACM 2020), and Arden, Liu, Myers (*FLAM*, IEEE CSF 2015).
- **Erasure semantics and concrete compiler/library implementations:** Chong & Myers (CSFW 2005), Hunt & Sands (ESOP 2008), Simon, Chisnall, Anderson (IEEE EuroS&P 2018), Besson, Dang, Jensen (ACM PLAS 2018), ISO/IEC 9899:2024 §7.26.6.2 (`memset_explicit`), `RustCrypto/utils` `zeroize` v1.9.2 (commit `77d1a3e6c2e8c28f49189258abb5d4405c0f1330`), `jasmin-lang/jasmin` (commit `2854536f9b0cb6f72e641dd711b627c1df7fdcb3`), `llvm/llvm-project` (commit `8c2c5468578e037ffb3c2e00f0dfc4e1c00d21b9`), `gcc (Debian 15.2.0-14) 15.2.0` on `x86_64-linux-gnu`, Wei et al. (USENIX FAST 2011), and O'Callahan et al. (USENIX ATC 2017, `rr`).

**Relationship among subjects:** The theoretical frameworks (Abate et al., Clarkson & Schneider, Canetti, Hirt & Maurer, Chong & Myers) define the relational hyperproperty and coalition-adversary semantics; the upstream implementations (`zeroize`, LLVM, GCC 15.2.0, Jasmin) establish what current production and formally verified compilers actually guarantee versus omit at the machine boundary; and the executable Python + x86-64 GCC probes concretely discriminate safe from unsafe trace relations, LTO rewrites, and zeroization strategies.

## Findings

### 1. Trace-Relating Compiler Correctness, Galois Connections, and `R^kHSP` Preservation

Basis: normative + derived + execution

Following Clarkson & Schneider (JCS 2010, DOI `10.3233/JCS-2009-0393`), a **trace property** is a set of traces `pi in 2^Tr`, whereas a **hyperproperty** is a set of sets of traces `H in 2^(2^Tr)`. A **`k`-hypersafety** property is refutable by a finite set of at most `k` finite trace prefixes (for example, observational determinism and constant-time noninterference are **2-hypersafety** properties over pairs of traces `(t_1, t_2)` agreeing on low/public inputs).

In Abate et al. (CSF 2019, DOI `10.1109/CSF.2019.00025`; ESOP 2020 `arXiv:1907.05320`; ACM TOPLAS 2021, DOI `10.1145/3460860`), source traces `Tr_S` and target traces `Tr_T` need not belong to the same set (e.g., source traces record abstract I/O while target traces add memory-access addresses, branch PCs, undefined behavior, or resource exhaustion). Given any binary trace relation `~ subseteq Tr_S x Tr_T`, Abate et al. define two monotone property transformers:

```text
tau_tilde(pi_S) = { t in Tr_T | exists s in pi_S, s ~ t }          (existential forward image)
sigma_tilde(pi_T) = { s in Tr_S | forall t in Tr_T, s ~ t => t in pi_T }  (universal backward preimage)
```

These form an exact **Galois connection** `(tau_tilde -| sigma_tilde)` on `(2^Tr_S, subseteq)` and `(2^Tr_T, subseteq)`:

```text
forall pi_S subseteq Tr_S, pi_T subseteq Tr_T:
    tau_tilde(pi_S) subseteq pi_T   <==>   pi_S subseteq sigma_tilde(pi_T)
```

**Trace-Relating Compiler Correctness (`CC_~`):** A compiler `C` satisfies `CC_~` iff for every whole program `P`, `Beh_T(C(P)) subseteq tau_tilde(Beh_S(P))` (equivalently, every source property `pi_S` satisfied by `P` implies target property `tau_tilde(pi_S)` for `C(P)`). Lifting to open components `P` linked with adversarial target contexts `C_T` yields Robust Trace-Relating Preservation criteria:
- **Robust Safety Preservation (`RSP_~`)** and **Robust Trace Property Preservation (`RTP_~`)**: for every target context `C_T`, there exists a source context `C_S` such that `Beh_T(C_T[C(P)]) subseteq tau_tilde(Beh_S(C_S[P]))`.
- **Robust `k`-Hypersafety Preservation (`R^kHSP_~`)** (specifically `R2HSP` for noninterference): for every target context `C_T` and every `k`-tuple of target traces `t_1, ..., t_k in Beh_T(C_T[C(P)])`, there exists a single source context `C_S` and source traces `s_1, ..., s_k in Beh_S(C_S[P])` with `s_i ~ t_i` for all `i`.

#### Necessary and Sufficient Condition for Preserving 2-Safety Noninterference (`Low-Equivalence Functionality`)

Even when `CC_~` (or even `R2HSP_~`) holds, target noninterference `NI_T` (`forall t_1, t_2 in Beh_T, t_1 =_L t_2` on low-indistinguishable runs) is **NOT** automatically implied by source noninterference `NI_S` unless `~` respects low-equivalence classes. Specifically, `CC_~` guarantees `NI_S(Beh_S) => NI_T(Beh_T)` for all source behaviors `Beh_S` if and only if `~` is **Low-Equivalence Functional**:

```text
forall s_1, s_2 in Tr_S, forall t_1, t_2 in Tr_T:
    (s_1 =_{L,S} s_2  /\  s_1 ~ t_1  /\  s_2 ~ t_2)  ==>  t_1 =_{L,T} t_2
```

Equivalently, whenever `s ~ t`, the target low/leakage projection `leak_T(t)` must be a deterministic, secret-independent function `F(leak_S(s))` of the source low/leakage projection. This exact condition is what Barthe, Grégoire, and Laporte (CSF 2018, DOI `10.1109/CSF.2018.00031`) and CompCertCT (Barthe et al., POPL 2020, DOI `10.1145/3371075`) enforce via a **constant-time simulation diagram** with a secret-independent leakage transformer `F` (preventing optimizations from turning two source-indistinguishable executions into target executions with distinct cache/branch traces).

**Exhaustive finite-model verification (`/tmp/probe_coalition_hyperprop.py`):** Over 3-element source and target trace spaces with low-equivalence partition `{{0, 1}, {2}}`:
- All `1,984` sampled subset pairs verify the exact Galois equivalence `tau_tilde(pi_S) subseteq pi_T <=> pi_S subseteq sigma_tilde(pi_T)`.
- Out of all `2^9 = 512` binary trace relations:
  - Exactly **`95`** satisfy Low-Equivalence Functionality, and across all NI-satisfying source behaviors and all `CC_~`-admissible target behaviors, **`0` counterexamples** exist.
  - Among the **`417`** non-functional relations, the minimal witness `rel = {(0, 0), (0, 2)}` with `Beh_S = {0}` satisfies `NI_S` and `CC_~` for `Beh_T = {0, 2}`, yet `Beh_T` violates `NI_T` because `low_T(0) = 0 != 1 = low_T(2)`.

### 2. Coalition-Indexed Observation Presheaves for Mixed TEE / MPC / FHE Compilation

Basis: normative + derived + execution

When compiling and linking distributed or confidential programs that span heterogeneous trust domains—such as a client inside a TEE, a blind Fully Homomorphic Encryption (FHE) cloud evaluator `E`, and Multi-Party Computation (MPC) share-holders `B, C`—two foundational traps invalidate naive observation models:

#### Trap 2.1: Principal-Indexed (Singleton) Confidentiality Fails Under Collusion

In threshold MPC or secret sharing, confidentiality is **not** a property of isolated single principals. Over `Z_4` additive secret sharing (`x_A = (s_B + s_C) mod 4` with uniform `s_B`), direct enumeration in `/tmp/probe_coalition_hyperprop.py` confirms:
- `SD(View_{B}(x_A = u), View_{B}(x_A = v)) = 0.0` for all `u, v in Z_4`;
- `SD(View_{C}(x_A = u), View_{C}(x_A = v)) = 0.0` for all `u, v in Z_4`;
- `SD(View_{B, C}(x_A = u), View_{B, C}(x_A = v)) = 1.0` for `u != v`.

Thus, matching Hirt & Maurer's general adversary structures (J. Cryptology 2000, DOI `10.1007/s001459910002`) and FLAM's authority lattices (Arden, Liu, Myers, CSF 2015, DOI `10.1109/CSF.2015.48`), security policies MUST index observations over the **coalition poset** `(P(Pi), subseteq)` with a downward-closed **adversary structure** `A subseteq P(Pi)` (all coalitions permitted to be corrupted, e.g., `A = { empty, {E} }` in outsourced FHE or `A = { C | |C| < t }` in `t`-threshold MPC).

#### Trap 2.2: Monolithic Observation Floors vs. Blind Evaluators & Anti-Goodhart Erasure

1. **Global floor impossibility:** For a non-constant functionality `f : X -> Y` (`|Im(f)| >= 2`), requiring every runtime node to observe a global plaintext floor `O_min` distinguishing outputs of `f` directly contradicts FHE/MPC confidentiality (`View_E(x) approx_c View_E(x')`).
2. **Per-principal `Unit` loophole:** Conversely, allowing arbitrary principals to declare a trivial observation domain `O_min(pi) = Unit` without an end-to-end faithfulness constraint allows a degenerate compiler or prover to erase all observations to `Unit`, trivially validating miscompilations such as an FHE evaluator returning constant ciphertext `0` (`Eval(ct) := 0`).

#### Reconciled Structure: Dual-Bound Coalition Presheaf + Advantage Quantale

Define an **Authority-Indexed Observation Model** as a contravariant functor (presheaf) `O : (P(Pi))^op -> Obs` assigning each coalition `C subseteq Pi` its joint observation space `O(C)` together with restriction maps `rho_{C_2 -> C_1} : O(C_2) -> O(C_1)` for `C_1 subseteq C_2` satisfying functoriality (`rho_{C -> C} = id`, `rho_{C_2 -> C_1} o rho_{C_3 -> C_2} = rho_{C_3 -> C_1}`):

1. **Lower Bound — Joint Authorized Output Faithfulness (Anti-Erasure Floor):** There exists a non-empty authorized output coalition `Pi_out subseteq Pi` and a non-degenerate ideal observation domain `|O_min^ideal| >= 2` such that decoding the real execution's joint output refines the ideal functionality `F_ideal`:
   ```text
   Decode_{Pi_out}(O_real(Pi_out))  <=_{O_min^ideal}  F_ideal(In)
   ```
   Under this dual rule, blind evaluator `E notin Pi_out` legitimately has `O_plain({E}) = Unit`, yet `Eval(ct) := 0` fails Joint Authorized Output Faithfulness on `Pi_out = {A}` (`fhe_eraser_passes_confidentiality = true`, `fhe_eraser_passes_joint_faithfulness = false` in `/tmp/probe_coalition_hyperprop.py`).
2. **Upper Bound — Adversarial Coalition Simulator Ceiling (UC Confidentiality):** Following Canetti's Universally Composable security framework (JACM 2020, DOI `10.1145/3402457`), every corrupted coalition `C in A` satisfies:
   ```text
   forall C in A:  O_real(C)  approx_{c, eps_C(t, q; lambda)}  Sim_C(In_C, Out_C, L_max(C))
   ```
   where `L_max(C)` is the explicit permitted leakage ceiling (such as ciphertext size or oblivious circuit topology).
3. **Concrete-Security Advantage Quantale:** Composing verified kernel proofs (advantage `0`, assumptions `empty`), statistical security (`(empty, (t, q) |-> delta)`), and computational reductions (`(H, eps)`) forms a commutative ordered monoid:
   ```text
   Comp(H_1, eps_1) (x) Comp(H_2, eps_2)
     = Comp(H_1 U H_2, (t, q) |-> min(1, eps_1(t + t_red, q) + eps_2(t + t_red, q)))
   ```
   preserving associativity, monotonicity in `(t, q)`, and identity `(empty, 0)`.

### 3. Cross-Module Link-Time Optimization: The LTO Refinement Paradox & Product-Fibered Presheaves

Basis: derived + execution

Consider two verified modules linked at LTO time:
- Module `M_1` handles Alice's secret `s_A in {0, 1}` and satisfies Bob-noninterference (`NI_Bob`).
- Module `M_2` is a utility helper with timing nondeterminism `t in {1, 2}` whose local contract omits Bob's side-channel observation model (`kappa_2` tracks functional behavior only).

**The LTO Refinement Paradox:** If the linker combines `M_1(kappa_1)` and `M_2(kappa_2)` by projecting onto their common coarser observation model (the meet `kappa_1 meet kappa_2`, which drops `Leak_Bob`), an LTO specialization pass can resolve `M_2`'s nondeterminism as `t := s_A + 1`. Because `{(0, 0, 1), (1, 1, 2)} subseteq {(0, 0, 1), (0, 0, 2), (1, 1, 1), (1, 1, 2)}`, this optimization satisfies **100% sound 1-trace refinement**, yet completely destroys `NI_Bob` (`pre_lto_ni_bob = true`, `leaky_lto_is_trace_refinement = true`, `leaky_lto_ni_bob = false` in `/tmp/probe_coalition_hyperprop.py`).

**Safe Cross-Module LTO Rules:**
1. **Product-Fibered Presheaf (Join, Not Meet):** Link `M_1(O_1)` and `M_2(O_2)` over the coalition-wise product presheaf:
   ```text
   (O_1 (x)_P O_2)(C)  :=  O_1(C) x O_2(C)    for all C in P(Pi)
   ```
   Every fused LTO rewrite `l ~> r` MUST preserve functional refinement on `Pi_out` AND induce a **Low-Equivalence-Functional** secret-independent leakage transformer `F_C` for every corrupted coalition `C in A` (e.g., resolving `t := 1` independently of `s_A`, where `safe_lto_ni_bob = true`).
2. **Trust-Domain Inlining Boundaries:**
   - *Intra-domain inlining* (`Domain(M_1) == Domain(M_2)`): admissible under `O_1 (x)_P O_2` with low-equivalence-functional leakage preservation.
   - *Cross-principal inlining* (`A | B`): statically forbidden unless mediated by an explicit `Declassify` or protocol-realization boundary (preventing LTO from hoisting secret-dependent branches across trust walls).
   - *Intra-circuit homomorphic/MPC LTO* (`FHE.Eval(g, FHE.Eval(f, ct)) ~> FHE.Eval(g o f, ct)`): admissible only inside oblivious circuit IR when topology leakage `L_max(E)` is invariant and multiplicative depth / ciphertext noise budget is non-increasing.
3. **Virtual-Boundary Claim Re-Anchoring (`ReAnchor`):** When LTO inlines across an interface `Sigma_12` that previously anchored separate module proofs (e.g., separation-logic memory invariants in `M_1` and constant-time proofs in `M_2`), preserve `M_virt := M_1 +_{Sigma_12} M_2` as a virtual cut node in the verification derivation tree, materialize interface preconditions as proved ghost assumptions before inlining, and verify the post-inlining optimizer pass purely by vertical refinement `InlineOpt(M_virt) <=^{{F_C}}_{O_1 (x)_P O_2} M_virt` composed with `tau_tilde_F`—avoiding full re-verification of the fused unit from scratch.

### 4. Post-Zeroization Forward Secrecy Across Registers, Stack Spills, Time-Travel Logs, and CoW Storage

Basis: normative + documentation + source + execution

Formalizing cryptographic forward secrecy after key/secret erasure requires a **2-safety temporal erasure hyperproperty** (Chong & Myers, CSFW 2005, DOI `10.1109/CSFW.2005.1`; Hunt & Sands, ESOP 2008, DOI `10.1007/978-3-540-78791-4_18`; Besson, Dang, Jensen, PLAS 2018, DOI `10.1145/3264820.3264822`):

```text
Post-Zeroization Forward Secrecy (for adversary observation surface S_obs):
  For any two executions E(k_0) and E(k_1) differing only in secret k,
  once execution passes event zeroize(k) at time t_z, the post-erasure
  observable state snapshots on S_obs satisfy:
      Obs_{S_obs}(E(k_0), t >= t_z)  ==  Obs_{S_obs}(E(k_1), t >= t_z)
```

In real systems, an adversary compromising a process, hypervisor, debugger, or storage device after `t_z` can inspect **seven distinct persistence surfaces**. Primary-source inspection of `RustCrypto/utils`, `llvm/llvm-project`, `jasmin-lang/jasmin`, ISO C23, and live compilation on `gcc 15.2.0` reveals an exact hierarchy of guarantees and gaps:

| Persistence Surface | Representative Mechanism / Implementation | Verified Guarantee (`source` / `normative` / `execution`) | Concrete Failure Mode When Omitted |
| :--- | :--- | :--- | :--- |
| **1. Explicit heap/local buffer (DSE defense)** | `RustCrypto/utils` `zeroize` v1.9.2 (`zeroize/src/bulk.rs:21-60`, `barrier.rs:52-89`); ISO/IEC 9899:2024 C23 §7.26.6.2 `memset_explicit` | `zeroize` fills slice + emits `asm!("# {}", in(reg) ptr, options(readonly, preserves_flags, nostack))` on 9 targets (`aarch64`, `arm`, `arm64ec`, `loongarch64`, `riscv32/64`, `s390x`, `x86`, `x86_64`) and 16-byte chunked `write_volatile` fallback elsewhere. C23 `memset_explicit` forbids DSE elision. | Plain `memset` is completely deleted by `-O2` DSE (confirmed live on GCC 15.2.0 `use_secret_naive`: zero `memset` call or zeroing stores emitted). Rust `Vec`/`String` reallocations and stack `move` semantics leave unzeroed prior copies (`zeroize/src/lib.rs:165-185`). |
| **2. Caller-saved (call-used) registers** | LLVM `PEIImpl::insertZeroCallUsedRegs` (`llvm/lib/CodeGen/PrologEpilogInserter.cpp:1209-1352`); GCC `-fzero-call-used-regs=used` | Clears used allocatable non-fixed, non-return, non-callee-saved registers at return blocks (`L1266-1351`; GCC emits `xorl`/`pxor` before `ret`). | Without `-fzero-call-used-regs`, GCC 15.2.0 `use_secret_explicit` returns with secret-derived `(s0+s2, s1+s3)` live in `%xmm0` and `%xmm2`. Notice also LLVM `PrologEpilogInserter.cpp:1310` carries an explicit upstream `FIXME: Mixing physical registers and register units is likely a bug.` |
| **3. Callee-saved registers** | Explicitly **excluded** by LLVM `PrologEpilogInserter.cpp:1343-1346` (`for CSReg in getCalleeSavedRegs: RegsToZero.reset(...)`); requires caller scrubbing or dedicated asm trampoline | Callee restores caller's original register values from prologue stack pushes, leaving the callee's own secret-bearing values in registers only if caller-visible, OR leaving caller's secret-bearing callee-saved registers pushed on the callee's stack frame! | If a function holding a secret in `%rbx`/`%r12` calls a helper that spills `%rbx`/`%r12` to the stack, neither `memset_explicit` nor `-fzero-call-used-regs` clears the helper's prologue save slot! |
| **4. Compiler stack spill slots & red zone** | `RustCrypto` `zeroize_stack::<N>()` (`zeroize/src/stack.rs:48-52`, best-effort only); **Jasmin** verified stack zeroization (`proofs/lang/stack_zero_strategy.v:18-22`, `proofs/compiler/stack_zeroization_proof.v:36-58,295-308,523-536`, `proofs/compiler/it_compiler_proof.v:987-994,1674-1681,1703-1730`) | **Jasmin** proves in Coq/Rocq (`it_compile_prog_to_asmP`) that for every exported function configured with `SZSloop`, `SZSloopSCT` (loop + `LFENCE`), or `SZSunrolled`, every private stack byte in `[bottom, bottom + lfd_stk_max)` satisfies `zeroized_p` (either untouched since entry or explicitly overwritten with `0`). | **Live GCC 15.2.0 execution proof:** Even with BOTH `memset_explicit(buf, 0, 32)` AND `-fzero-call-used-regs=used`, GCC spills `(s0+s2, s1+s3)` to an undeclared 16-byte stack spill slot at `(%rsp)` (`movaps %xmm2, (%rsp)`), calls `memset_explicit` only on `16(%rsp)..47(%rsp)`, and returns leaving `(%rsp)..15(%rsp)` unzeroed! In Rust, `zeroize_stack` warns (`stack.rs:16-47`) that inlining causes it to zero the wrong stack region and `#[inline(never)]` is only a hint. |
| **5. Microarchitectural / physical register files** | Architectural `zeroize` + Jasmin `SZSloopSCT` (`LFENCE` barrier before return) | `SZSloopSCT` prevents speculative bypass of the zeroization loop across return; architectural zeroing overwrites architectural state. | Out-of-order physical register files, store buffers, fill buffers, and SIMD/AVX upper lanes (MDS/Fallout/RIDL/Downfall) can retain stale physical register contents beyond architectural `xor` (`zeroize/src/lib.rs:160-163`). |
| **6. Time-travel debug logs, core dumps & swap** | `rr` deterministic record-and-replay (O'Callahan et al., USENIX ATC 2017), Intel PT, WinDbg TTD; Linux `mlock`, `MADV_DONTDUMP`, `PR_SET_DUMPABLE=0` | `mlock` prevents paging secrets to unencrypted swap; `MADV_DONTDUMP` + `PR_SET_DUMPABLE=0` suppress core dumps; non-recording isolation excludes secret keys from `rr` syscall/entropy logs. | Any deterministic record-and-replay log (`rr` records `RDRAND`/syscall outputs and initial inputs) or unmasked core dump reproduces the entire pre-zeroization key material even when architectural RAM and stack are 100% zeroed! |
| **7. Copy-on-Write (CoW) filesystems & SSD FTLs** | ZFS, Btrfs, APFS, ext4 journals, NVMe/SATA SSD Flash Translation Layers (Wei et al., USENIX FAST 2011) | Overwriting a file in place on a CoW filesystem or wear-leveled SSD allocates a **new** physical block/page and leaves the old physical flash page intact until garbage collection/TRIM. | In-place file `zeroize` / `shred` fails completely on CoW filesystems and SSDs (`Wei et al., FAST 2011`). Reliable post-zeroization forward secrecy on persistent storage requires **envelope encryption + cryptographic erasure** (destroying a small ephemeral key-encryption key held in volatile RAM or a hardware KMS/TPM slot). |

#### Direct Live x86-64 GCC 15.2.0 Assembly Counterexample (`Basis: execution`)

Compiling `/tmp/zeroize_probe.c` with `gcc -O2 -std=c23 -fzero-call-used-regs=used -S` (GCC 15.2.0, `x86_64-linux-gnu`) yields the following exact instructions for `use_secret_explicit`:

```asm
use_secret_explicit:
    pushq   %rbx
    subq    $48, %rsp
    movdqu  16(%rdi), %xmm1
    movdqu  (%rdi), %xmm0
    ...
    paddq   %xmm0, %xmm2            # xmm2 := (s0 + s2, s1 + s3)  [secret-derived!]
    movaps  %xmm0, 16(%rsp)         # buf[0..1] at rsp+16..31
    movaps  %xmm1, 32(%rsp)         # buf[2..3] at rsp+32..47
    movaps  %xmm2, (%rsp)           # COMPILER SPILL SLOT at rsp+0..15 (NEVER ZEROED!)
    ...
    call    sink_call@PLT
    leaq    16(%rsp), %rdi          # memset_explicit ONLY covers rsp+16..47
    movl    $32, %edx
    xorl    %esi, %esi
    call    memset_explicit@PLT
    movdqa  (%rsp), %xmm2           # reloads unzeroed spill slot from rsp+0..15
    addq    $48, %rsp
    popq    %rbx
    ...
    xorl    %edx, %edx              # -fzero-call-used-regs=used clears caller-saved regs
    xorl    %esi, %esi
    xorl    %edi, %edi
    pxor    %xmm0, %xmm0
    pxor    %xmm1, %xmm1
    pxor    %xmm2, %xmm2
    pxor    %xmm3, %xmm3
    ret                             # rsp-48..rsp-33 STILL HOLDS (s0+s2, s1+s3)!
```

Meanwhile, in `use_secret_naive` (identical function using standard `memset(buf, 0, sizeof(buf))`), GCC 15.2.0 `-O2` deletes the `memset` call entirely AND leaves raw `in_key[0..3]` at `(%rsp)`, `16(%rsp)`, and `32(%rsp)` intact after `ret`.

## Boundaries

- **Probabilistic / quantitative information-flow leakage channels (`not examined`):** The exhaustive `512`-relation probe checks exact possibilistic 2-safety noninterference (`low_T(t_1) == low_T(t_2)`), and the coalition secret-sharing probe checks exact statistical distance over finite uniform distributions. Asymptotic/computational probabilistic hyperproperties (`HyperPCTL`, differential privacy composition) and concrete FHE noise-budget bounds were **not examined** mechanically beyond the quantale algebraic composition check.
- **Step-indexed circular proofs across heterogeneous LTO units (`unknown`):** While virtual-boundary `ReAnchor` handles acyclic horizontal linking of heterogeneous modules (e.g., separation logic + constant-time proofs), the general categorical condition for commuting step-indexed mutually recursive circular assumptions across non-linear cross-module LTO and subsequent incremental proof retraction remains **unknown**.
- **LLVM Clang `-fzero-call-used-regs` binary execution (`not examined`):** LLVM's `PEIImpl::insertZeroCallUsedRegs` was audited directly from upstream C++ source (`llvm/lib/CodeGen/PrologEpilogInserter.cpp:1209-1352`), whereas live x86-64 binary compilation was executed on `gcc 15.2.0` (`clang` was not installed in the observation environment). Both compilers share the architectural exclusion of callee-saved registers and stack spill slots.
- **Register clearing via `RustCrypto/utils` `zeroize` (`unsupported`):** `zeroize` v1.9.2 explicitly documents (`zeroize/src/lib.rs:187-206`) that clearing CPU registers, preventing Rust move/reallocation stack copies, `mlock()`, `mprotect()`, and defending against microarchitectural covert channels are **unsupported** and out of scope for the crate.
- **Single-trace compiler correctness for hyperproperties (`known not to apply`):** Standard 1-trace refinement (`Beh_T subseteq Beh_S`) is **known not to apply** to preserving 2-safety confidentiality across nondeterminism-resolving LTO passes (as proved by the LTO Refinement Paradox) or across trace relations that violate Low-Equivalence Functionality.
- **In-place byte overwrite for CoW filesystems and flash SSDs (`known not to apply`):** Applying `memset_explicit` / `zeroize` / in-place file overwrite to blocks residing on copy-on-write filesystems (ZFS, Btrfs, APFS) or wear-leveled SSDs is **known not to apply** to achieving post-zeroization forward secrecy (Wei et al., USENIX FAST 2011); cryptographic key erasure is required instead.

## Evidence

### Primary Git Repositories and Source Line Citations (Observed 2026-11-19)

1. **`RustCrypto/utils`** @ `77d1a3e6c2e8c28f49189258abb5d4405c0f1330` (`zeroize` v1.9.2):
   - `zeroize/Cargo.toml:1-38`: version `1.9.2`, Rust edition `2024`, MSRV `1.85`.
   - `zeroize/src/lib.rs:148-206,252-420`: documented guarantees and explicit non-guarantees (moves, stack spills, `Vec`/`String` reallocation, registers `rust-lang/rust#17046`, microarchitectural attacks, `mlock`/`mprotect`).
   - `zeroize/src/barrier.rs:52-89`: `optimization_barrier()` inline `asm!("# {}", in(reg) ptr, options(readonly, preserves_flags, nostack))` on 9 targets, `core::hint::black_box` fallback.
   - `zeroize/src/bulk.rs:6-94`: `fill_slice()`, `zeroize_byte_ptr()`, and 16-byte chunked `volatile_fill_slice()` fallback.
   - `zeroize/src/stack.rs:1-52`: `zeroize_stack<const N: usize>()` best-effort stack buffer zeroization and explicit inlining hazard warning (`L16-47`).
2. **`jasmin-lang/jasmin`** @ `2854536f9b0cb6f72e641dd711b627c1df7fdcb3`:
   - `proofs/lang/stack_zero_strategy.v:18-37`: `Variant stack_zero_strategy := | SZSloop | SZSloopSCT | SZSunrolled.`
   - `proofs/compiler/stack_zeroization_proof.v:36-70,295-308,394-408,523-536`: `sz_cmd_spec`, `Record match_mem_zero`, `match_mem_zero_export`, and `Lemma istack_zeroization_lprogP` (ITree `wkequiv_io`).
   - `proofs/compiler/it_compiler_proof.v:987-995,1674-1681,1703-1730`: `Definition zeroized_p`, `Definition zeroized_u`, `Definition full_post`, and end-to-end theorem `Lemma it_compile_prog_to_asmP`.
3. **`llvm/llvm-project`** @ `8c2c5468578e037ffb3c2e00f0dfc4e1c00d21b9`:
   - `llvm/lib/CodeGen/PrologEpilogInserter.cpp:1209-1352`: `PEIImpl::insertZeroCallUsedRegs()` — marks non-implicit used allocatable regs (`L1254-1256`), omits callee-saved registers (`L1343-1346`), performs zeroing only at `isReturnBlock()` (`L1349-1351`), does not scrub stack spill slots, and notes `FIXME` on mixing physical registers and register units (`L1310`).

### Standards and Peer-Reviewed Publications

- ISO/IEC 9899:2024 (C23), §7.26.6.2 (`memset_explicit`).
- M. R. Clarkson and F. B. Schneider, "Hyperproperties," *Journal of Computer Security* 18(6), 2010, DOI `10.3233/JCS-2009-0393`.
- C. Abate, R. Blanco, D. Garg, C. Hrițcu, M. Patrignani, and J. Thibault, "Journey Beyond Full Abstraction: Exploring Robust Property Preservation for Secure Compilation," *IEEE CSF 2019*, DOI `10.1109/CSF.2019.00025`.
- C. Abate, R. Blanco, Ş. Ciobâcă, A. Durier, D. Garg, C. Hrițcu, M. Patrignani, É. Tanter, and J. Thibault, "Trace-Relating Compiler Correctness and Secure Compilation," *ESOP 2020* (`arXiv:1907.05320`); extended journal version: "An Extended Account of Trace-Relating Compiler Correctness and Secure Compilation," *ACM TOPLAS* 43(4), Article 14, 2021, DOI `10.1145/3460860`.
- G. Barthe, B. Grégoire, and V. Laporte, "Secure Compilation of Side-Channel Countermeasures: The Case of Cryptographic 'Constant-Time'," *IEEE CSF 2018*, DOI `10.1109/CSF.2018.00031`.
- G. Barthe, S. Blazy, B. Grégoire, R. Hutin, V. Laporte, D. Pichardie, and A. Trieu, "Formal Verification of a Constant-Time Preserving C Compiler," *ACM POPL 2020*, DOI `10.1145/3371075`.
- M. Hirt and U. Maurer, "Player Simulation and General Adversary Structures in Perfect Multiparty Computation," *Journal of Cryptology* 13(1), 2000, DOI `10.1007/s001459910002`.
- R. Canetti, "Universally Composable Security," *Journal of the ACM* 67(5), 2020, DOI `10.1145/3402457`.
- O. Arden, J. Liu, and A. C. Myers, "Flow-Limited Authorization," *IEEE CSF 2015*, DOI `10.1109/CSF.2015.48`.
- S. Chong and A. C. Myers, "Language-Based Information Erasure," *IEEE CSFW 2005*, DOI `10.1109/CSFW.2005.1`.
- S. Hunt and D. Sands, "Just Forget It – The Semantics and Enforcement of Information Erasure," *ESOP 2008*, DOI `10.1007/978-3-540-78791-4_18`.
- L. Simon, D. Chisnall, and R. Anderson, "What You Get is What You C: Controlling Side Effects in Mainstream C Compilers," *IEEE EuroS&P 2018*, DOI `10.1109/EuroSP.2018.00009`.
- F. Besson, A. Dang, and T. P. Jensen, "Securing Compilation Against Memory Probing," *ACM PLAS 2018*, DOI `10.1145/3264820.3264822`.
- M. Wei, L. M. Grupp, F. E. Spada, and S. Swanson, "Reliably Erasing Data From Flash-Based Solid State Drives," *USENIX FAST 2011*.
- R. O'Callahan, C. Jones, N. Froyd, K. Huey, A. Noll, and N. Partush, "Engineering Record and Replay for Deployability," *USENIX ATC 2017*.

### Executable Probes & Observed Outputs (Observed 2026-11-19, Linux x86_64)

#### Probe A: Relational Hyperproperty, Coalition Presheaf & Erasure Surface Model (`python3 /tmp/probe_coalition_hyperprop.py`, Python 3.13.15, exit code `0`)

```python
#!/usr/bin/env python3
"""Exhaustive 512-relation TrCC 2-safety check, LTO refinement paradox,
3-party coalition presheaf collusion, and 7-surface zeroization model."""
from itertools import product
import json

def check_trcc():
    S = T = (0, 1, 2)
    low = {0: 0, 1: 0, 2: 1}
    subs = [frozenset(x for x in S if (m >> x) & 1) for m in range(8)]
    tau = lambda r, ps: frozenset(t for (s, t) in r if s in ps)
    sig = lambda r, pt: frozenset(s for s in S if all(t in pt for (s2, t) in r if s2 == s))
    func = lambda r: all(low[t1] == low[t2] for s1, t1 in r for s2, t2 in r if low[s1] == low[s2])
    ni = lambda b: len({low[x] for x in b}) <= 1
    pairs = list(product(S, T))
    ni_srcs = [b for b in subs if ni(b)]
    g_cnt = f_cnt = f_cex = nf_cnt = 0
    witness = None
    for mask in range(1 << len(pairs)):
        rel = frozenset(pairs[i] for i in range(len(pairs)) if (mask >> i) & 1)
        if mask % 17 == 0:
            for ps in subs:
                for pt in subs:
                    assert (tau(rel, ps) <= pt) == (ps <= sig(rel, pt))
                    g_cnt += 1
        if func(rel):
            f_cnt += 1
            for bs in ni_srcs:
                img = tau(rel, bs)
                assert ni(img)
                for bt in subs:
                    if bt <= img and not ni(bt):
                        f_cex += 1
        else:
            nf_cnt += 1
            if witness is None:
                for bs in ni_srcs:
                    img = tau(rel, bs)
                    if not ni(img):
                        witness = {"rel": sorted(rel), "beh_s": sorted(bs), "beh_t": sorted(img)}
                        break
    return {"total": 512, "galois_pairs": g_cnt, "functional": f_cnt,
            "functional_cex": f_cex, "nonfunctional": nf_cnt, "witness": witness}

def check_coalition_and_lto():
    pre = {(0, 0, 1), (0, 0, 2), (1, 1, 1), (1, 1, 2)}
    leaky, safe = {(0, 0, 1), (1, 1, 2)}, {(0, 0, 1), (1, 1, 1)}
    def ni_bob(b):
        by_s = {0: set(), 1: set()}
        for s, _, t in b: by_s[s].add(t)
        return by_s[0] == by_s[1] and len(by_s[0]) > 0
    def view_dist(coal, x):
        d = {}
        for sb in range(4):
            sh = {"B": sb, "C": (x - sb) % 4}
            k = tuple(sh[p] for p in sorted(coal))
            d[k] = d.get(k, 0) + 1
        return d
    def sd(d1, d2):
        tot = sum(d1.values())
        return 0.5 * sum(abs(d1.get(k, 0) - d2.get(k, 0)) for k in set(d1) | set(d2)) / tot
    eval_good = lambda x: (x ^ 1, "const_ct_size")
    eval_eraser = lambda x: (0, "const_ct_size")
    return {
        "pre_ni": ni_bob(pre), "leaky_refines": leaky <= pre, "leaky_ni": ni_bob(leaky),
        "safe_ni": ni_bob(safe),
        "sd_B": max(sd(view_dist({"B"}, x), view_dist({"B"}, y)) for x in range(4) for y in range(4)),
        "sd_C": max(sd(view_dist({"C"}, x), view_dist({"C"}, y)) for x in range(4) for y in range(4)),
        "sd_BC": max(sd(view_dist({"B", "C"}, x), view_dist({"B", "C"}, y)) for x in range(4) for y in range(4)),
        "fhe_eraser_passes_confidentiality": eval_eraser(0)[1] == eval_eraser(1)[1],
        "fhe_eraser_passes_joint_faithfulness": all(eval_eraser(x)[0] == (x ^ 1) for x in (0, 1)),
        "fhe_good_passes_joint_faithfulness": all(eval_good(x)[0] == (x ^ 1) for x in (0, 1)),
    }

if __name__ == "__main__":
    print(json.dumps({"trcc": check_trcc(), "coalition_lto": check_coalition_and_lto()}, indent=2))
```

Observed results: `total = 512`, `galois_pairs = 1984`, `functional = 95`, `functional_cex = 0`, `nonfunctional = 417`, `witness = {"rel": [[0, 0], [0, 2]], "beh_s": [0], "beh_t": [0, 2]}`; `pre_ni = true`, `leaky_refines = true`, `leaky_ni = false`, `safe_ni = true`; `sd_B = 0.0`, `sd_C = 0.0`, `sd_BC = 1.0`; `fhe_eraser_passes_confidentiality = true`, `fhe_eraser_passes_joint_faithfulness = false`, `fhe_good_passes_joint_faithfulness = true`.

#### Probe B: Live C23 `memset` vs. `memset_explicit` + `-fzero-call-used-regs=used` (`gcc 15.2.0`, x86-64)

Command:
```bash
gcc -O2 -std=c23 -fzero-call-used-regs=used -S -o /tmp/zeroize_zcur.s /tmp/zeroize_probe.c
```
Source (`/tmp/zeroize_probe.c`):
```c
#include <stdint.h>
#include <string.h>
extern void sink_call(uint64_t a, uint64_t b);
__attribute__((noinline))
uint64_t use_secret_explicit(const uint64_t *in_key) {
    uint64_t buf[4];
    memcpy(buf, in_key, sizeof(buf));
    uint64_t s0 = buf[0], s1 = buf[1], s2 = buf[2], s3 = buf[3];
    sink_call(s0 ^ s1, s2 ^ s3);
    uint64_t ret = (s0 + s2) ^ (s1 + s3);
    memset_explicit(buf, 0, sizeof(buf));
    return ret;
}
```
Observed result: `memset_explicit` zeroes `16(%rsp)..47(%rsp)` and `-fzero-call-used-regs=used` emits `xorl`/`pxor` on `%edx, %esi, %edi, %xmm0..3`, while the compiler-synthesized stack spill at `(%rsp)..15(%rsp)` holding `paddq %xmm0, %xmm2` (`(s0+s2, s1+s3)`) is never zeroed before `ret`.

## Revalidation

1. **Rerun the GCC/Clang C23 stack-spill probe:** Compile `/tmp/zeroize_probe.c` with `-O2 -std=c23 -fzero-call-used-regs=used -S` (and any new compiler stack-scrubbing flag such as `-fzero-stack` if introduced) and inspect whether any `movaps`/`movq` spill slots outside the `memset_explicit` range remain unzeroed before `ret`.
2. **Diff `RustCrypto/utils` `zeroize` internals:** Inspect `zeroize/src/{lib.rs,barrier.rs,bulk.rs,stack.rs}` against commit `77d1a3e6c2e8c28f49189258abb5d4405c0f1330` to verify whether Rust compiler intrinsics (such as native stack-frame or register clearing) have replaced `asm!`-barrier + best-effort `zeroize_stack`.
3. **Diff LLVM `insertZeroCallUsedRegs`:** Inspect `llvm/lib/CodeGen/PrologEpilogInserter.cpp` against commit `8c2c5468578e037ffb3c2e00f0dfc4e1c00d21b9` to check whether the register-unit `FIXME` (`L1310`) is resolved and whether callee-saved register or spill-slot clearing options have been added.
4. **Diff Jasmin stack-zeroization theorem statements:** Inspect `proofs/compiler/stack_zeroization_proof.v` (`match_mem_zero`, `istack_zeroization_lprogP`) and `proofs/compiler/it_compiler_proof.v` (`zeroized_p`, `zeroized_u`, `it_compile_prog_to_asmP`) against commit `2854536f9b0cb6f72e641dd711b627c1df7fdcb3` to verify whether register-scrubbing or speculative-leakage postconditions have been expanded.
5. **Rerun `/tmp/probe_coalition_hyperprop.py`:** Takes `< 50 ms` to verify the Galois adjunction, 512-relation functional classification, LTO refinement paradox, and 3-party coalition collusion checks.
