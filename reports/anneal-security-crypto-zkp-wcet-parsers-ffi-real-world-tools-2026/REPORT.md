# Real-world verification tooling for security, cryptography, zero-knowledge proofs, quantitative resource bounds, wire formats, and FFI boundaries mapped to Anneal's trusted primitives

## Summary

Across six high-assurance domains—constant-time and speculative side-channel
verification (Category 6.1), cryptographic primitives and protocol game-hopping
(Category 6.2), zero-knowledge proof circuits and zkVMs (Category 6.3),
worst-case execution time and stack bounds (Category 6.4), verified zero-copy
wire-format parsers (Category 6.5), and cross-language FFI, CHERI hardware
capabilities, and secret zeroization (Category 6.6)—production verification
tools repeatedly confront four structural failure modes that Anneal's four
`trusted/lean/` primitives resolve with a single unified kernel interface:

1. **Soundness–completeness and safety–liveness duality (`Compiles` +
   `ProductiveOn` + `InhabitedPre`):** In zero-knowledge circuits (`Picus`,
   `Coda`, `Garden`, `LAMPE`), under-constrained circuits violate downward
   refinement (`Compiles`), whereas over-constrained circuits satisfy
   `Compiles` vacuously by admitting zero witnesses unless paired with
   `ProductiveOn` and `InhabitedPre`. The same duality governs non-aborting
   cryptographic simulators (`EasyCrypt`, `SSProve`), non-rejecting zero-copy
   parsers (`EverParse`, `Vest`), and feasible WCET/stack configurations
   (`CompCertS`, `Stacking`).
2. **Representation-invariant observable spines (`Language SemObs`,
   `BehaviorCodec`, `obs_decodeOut`, and fail-closed `decodeOut = none`):**
   Whether projecting pair executions to public control-flow and cache leakage
   traces (`CompCert-CT`, `Jasmin`), coupling randomness tapes in game hops
   (`EasyCrypt`, `CertiCrypt`), enforcing non-malleable parser round-trips
   (`EverParse`, `Narcissus`, `Vest`), or verifying dead-store-resistant secret
   erasure (`Secret-Erasure CompCert`, `zeroize`), `BehaviorCodec`'s partial
   bijection laws (`decodeOut_encodeOut`, `encodeOut_of_decodeOut`) and
   fail-closed `decodeOut = none` rule out representation spoofing, non-canonical
   field elements, unaligned pointer casts, and residual secret bytes.
3. **Variable-step dilation and open-world boundary framing
   (`EventualBehaviorOf` and `StepResult.externalCall`):** Cryptographic
   oracles (`EasyCrypt`, `Tamarin`), Fiat-Shamir transcript challenges and zkVM
   precompiles (`RISC Zero`, `SP1`, `Jolt`), FFI transitions (`DimSum`,
   `CompCertO`, `VeriFFI`, `RLBox`), and multi-cycle instruction timing models
   (`AbsInt aiT`, `CerCo`, `Iris` time credits) require variable-step trace
   alignment (`EventualBehaviorOf`) and pre-call invariant enforcement plus
   demonic environment return branching (`StepResult.externalCall boundaryInv
   branches`).
4. **Positive per-obligation assumption tracking (`VerificationResult policy
   waived obligations`):** Cryptographic hardness assumptions (LWE, DDH, ROM),
   FRI/KZG commitment conjectures, hardware microarchitectural timing tables,
   and external SMT/CAS certificates (`SAW`, `CryptoLine`, `Picus`) must be
   recorded as positive per-obligation waivers (`ob.id ∈ waived ∨ ob.prop`)
   rather than negative hypotheses (`hTcb → ...`) so that an idealized
   microarchitectural or computational model cannot discharge unrelated memory
   or arithmetic safety obligations via `False.elim`.

## Applicability

This report applies to Anneal's four foundational `trusted/lean/` verification
primitives as mechanized in the `reference` branch corpus at commit
`df55c524a051d59e7dd35564f282b30d29133392` (Specifically within packages
`anneal-behavior-codec-and-progress-refinement-2026`,
`anneal-polar-ctfe-admission-and-semantic-polarity-2026`,
`anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`, and
`anneal-structural-external-calls-and-tcb-mutation-testing-2026`), and compares
their formal expressive power, trusted computing base (TCB) boundaries, and
encoding patterns against 75 real-world verification tools and frameworks across
Categories 6.1 through 6.6.

Relationship among subjects: Anneal's `trusted/lean/` primitives serve as the
target meta-theoretical framework; each external tool family identified in
`REPORT.json` is examined for its upstream problem domain, historical lineage,
verification tradeoffs, formal semantics, TCB boundary, and exact structural
embedding into Anneal's primitives. Claims about upstream tool behavior are
scoped to the cited primary publications and repositories; derived mappings
onto Anneal's primitives are labeled `Basis: derived` and explicitly state the
instantiation of `Language SemObs`, `BehaviorCodec`, `Compiles`/`Abstracts`,
`ProductiveOn`, `EventualBehaviorOf`, `StepResult.externalCall`, and
`VerificationResult`.

## Findings

### Cross-domain architectural synthesis: Anneal's four trusted primitives

**Basis: source + derived.** Across the Anneal `reference` corpus packages at
`df55c524a051d59e7dd35564f282b30d29133392`, the kernel-checked verification
boundary is factored into four orthogonal primitives:

1. **`Language SemObs` and `Partial` (`Prog`, `Query`, `Out`, `obs : Out →
   SemObs`, `defined` vs. `Partial.ub`):** Every semantic domain `L : Language
   SemObs` assigns to a program `prog : L.Prog` and query `q : L.Query` a
   demonic nondeterministic specification `L.sem prog q : Partial L.Out`,
   comprising a safety bit `defined : Prop` (where `defined = False` is
   `Partial.ub`) and an inhabited outcome predicate `val : defined → L.Out →
   Prop`, equipped with an observable projection `L.obs : L.Out → SemObs`.
2. **`BehaviorCodec L₁ L₂` (including `PartialBehaviorCodec`), `Compiles`, and
   `Abstracts`:** A codec connects two languages sharing `SemObs` via
   `encodeQuery`, `decodeQuery` (`decodeQuery_encodeQuery`), `encodeOut`, and
   `decodeOut : L₂.Out → Option L₁.Out` satisfying `decodeOut_encodeOut`,
   `encodeOut_of_decodeOut`, and `obs_decodeOut` (`decodeOut o₂ = some o₁ →
   L₂.obs o₂ = L₁.obs o₁`). Downward compilation `Compiles L₁ L₂ c s t`
   requires that on every encoded query where source `s` is `defined`, target
   `t` is `defined` and every target outcome `o₂` decodes to `some o₁` (never
   `none`!) satisfying `s`. Upward abstraction `Abstracts L₁ L₂ c v s`
   soundly lifts concrete execution `s` into an abstract verification domain
   `v`.
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`:** `InhabitedPre pre` and `ProductiveOn pre prog`
   rule out vacuous preconditions and miracle/empty-witness implementations
   (`val h = ∅`). `EventualBehaviorOf` provides fuel-independent trace
   refinement across variable-step compilation passes (`1`-to-`k` instruction
   expansion or loop unrolling) without `Classical.choice` while rejecting
   silent divergence. `StepResult.externalCall boundaryInv branches` enforces a
   pre-call invariant `boundaryInv` at open-world interaction points and
   universally quantifies over demonic environment return `branches`.
4. **Positive per-obligation waiver envelopes (`VerificationResult policy
   waived obligations`):** Every verification obligation `ob` in `obligations`
   must satisfy `ob.id ∈ waived ∨ ob.prop`, and every `id ∈ waived` must be
   permitted by `policy : TrustPolicy`. Because unproved environmental or
   cryptographic assumptions never appear as negative hypotheses (`hTcb →
   ...`), an inconsistent or idealized external assumption cannot collapse the
   proof of unrelated obligations via `False.elim`.

---

### Category 6.1: 2-safety, constant-time, speculative constant-time, and information-flow control (IFC)

#### 1. Goals, target users, and vulnerability classes

**Basis: documentation + normative literature.** Cryptographic implementations
and high-assurance kernels must satisfy **relational hyperproperties** (in the
sense of Clarkson and Schneider, *Hyperproperties*, JCS 2010), most notably
**2-safety non-interference** and **cryptographic constant-time (CT)**: for any
two executions starting from states $(s_1, s_2)$ that agree on public inputs
($s_1 \equiv_{\text{pub}} s_2$) while differing arbitrarily on secret keys or
plaintexts, the externally observable leakage traces must be identical
($\mathcal{L}(s_1) = \mathcal{L}(s_2)$). In the baseline architectural CT
model, $\mathcal{L}$ records all conditional branch outcomes, memory access
addresses (cache-line or byte granularity), and variable-latency arithmetic
operands (such as hardware division `UDIV`/`IDIV`). Under **Speculative
Constant-Time (SCT)** (Spectre-v1/PHT, Spectre-v4/STL, RSB), $\mathcal{L}$
additionally includes transient microarchitectural fetches and loads triggered
along mispredicted branch or store-bypass paths up to a speculation window $w$.
Target users include cryptographic library authors (`BoringSSL`, `AWS-LC`,
`pq-crystals`, `libcrux`, `Dalek`), compiler engineers preventing C/Rust/LLVM
optimizations from introducing secret-dependent branches (the "compiler-induced
timing gap" documented by Kaufmann et al. and Simon et al., EuroS&P 2018), and
hardware RTL designers preventing cross-domain cache and bus timing leaks.

#### 2. Concrete tool inventory, history, and lineage

**Basis: documentation + source.**

- **`CompCert-CT` (`knothed/CompCert-ct`, Barthe, Blazy, Grégoire, Laporte,
  Oliveira, Pichardie, Poitrenaud, Triqueneaux; CCS 2018 / POPL 2020):**
  Extends Xavier Leroy's Coq-verified `CompCert` C compiler with leakage-aware
  operational semantics across all intermediate languages (`Clight`, `Cminor`,
  `RTL`, `LTL`, `Linear`, `Mach`, assembly) and proves that compilation
  preserves constant-time non-interference from source to machine code.
- **`Jasmin` (`jasmin-lang/jasmin`, Almeida, Barbosa, Barthe, Blot, Grégoire,
  Laporte, Oliveira, Pacheco, Schmidt, Strub; CCS 2017 / POPL 2020 / CCS
  2021):** A Coq-verified compiler for an assembly-like structured language
  ("assembly in the head of the programmer") targeting x86-64/AVX2 and ARMv7/v8.
  Provides built-in static and relational verification for memory safety,
  constant-time (`jasminc -checkCT`), and speculative constant-time (`jasminc
  -checkSCT` / selective speculative load hardening `SLH`), with direct
  extraction to `EasyCrypt`.
- **`FaCT` (`PLSysSec/FaCT`, Cauligi, Soeller, Johannesmeyer, Brown, Wahby,
  Jero, Sherwood, Jhala, Stefan, Ristenpart; PLDI 2019):** A Rust-like domain
  specific language and secrecy-typed compiler (`public` vs. `secret` type
  qualifiers) that automatically transforms secret-dependent conditionals and
  array accesses into constant-time bitwise/cmov idioms and lowers to LLVM IR.
- **`ct-verif` (`imdea-software/verifying-constant-time`, Almeida, Barbosa,
  Barthe, Dupressoir, Emmi; USENIX Security 2016):** Verifies constant-time C
  code compiled to LLVM IR by constructing a **self-composition product
  program** in `SMACK`/`Boogie` and discharging 2-safety assertions with `Z3`.
- **`Binsec/Rel` and `Binsec/Haunted` (`binsec/Rel`, Daniel, Bardin, Rezk; IEEE
  S&P 2020 and CAV 2021):** Binary-level Relational Symbolic Execution (RelSE)
  on x86/ARM/RISC-V executables lifted to DBA IR. `Binsec/Rel` shares symbolic
  expressions across the paired runs when public values coincide ("on-the-fly
  relational state sharing"), while `Binsec/Haunted` extends RelSE to
  speculative constant-time by simultaneously tracking architectural and
  transient "ghost" executions in a single symbolic pass without unrolling a
  separate speculation tree per branch.
- **`Blade` (Vassena, Disselkoen, von Gleissenthall, Cauligi, Kıcı, Jhala,
  Tullsen, Stefan; POPL 2021):** A static flow-sensitive type system and
  automatic repair algorithm implemented in the `Cranelift` WebAssembly
  compiler (`PLSysSec`) that constructs a transient def-use graph from
  speculative loads ("sources") to address-dependent memory operations
  ("sinks") and computes a minimal cut to insert speculative protection
  primitives (`protect` via masks/cmov rather than full `lfence` serialization).
- **`Spectector` (`spectector/spectector`, Guarnieri, Köpf, Morales, Reineke,
  Sánchez; IEEE S&P 2020):** Formalizes **Speculative Non-Interference (SNI)**—
  requiring that a program leaks no more under speculative semantics than under
  standard sequential semantics—and verifies x86 assembly via symbolic
  execution in CIAO Prolog + `Z3`.
- **`Pitchfork` (`PLSysSec/haybale-pitchfork`, Cauligi et al., PLSysSec 2020):**
  A Rust symbolic execution engine built on `haybale` (LLVM bitcode symbolic
  executor using `boolector`) that verifies constant-time execution of Rust and
  C cryptographic crates (`ring`, `subtle`, `libsodium`) and pinpoints exact
  source lines where secret taint reaches a branch condition or memory index.
- **`CacheAudit` (`cacheaudit/cacheaudit`, Doychev, Feld, Köpf, Mauborgne,
  Reineke; CCS 2013 / TISSEC 2015):** Static abstract-interpretation analyzer
  for x86 binaries that computes quantitative upper bounds on cache side-channel
  leakage (in bits of Shannon/min-entropy over LRU/FIFO/PLRU cache state, time,
  or trace observations).
- **`Constantine` (Borrello, Querzoni, Giuffrida; CCS 2021) and `SC-Eliminator`
  (Wu, Guo, Schaumont, Wang; ISSTA 2018):** LLVM compiler passes that eliminate
  secret-dependent control flow and data-cache accesses via control-flow
  linearization (predicated execution) and oblivious scatter-gather memory
  preloading.
- **`Cartesian Hoare Logic (CHL)` / `Descartes` (Sousa and Dillig, PLDI 2016),
  `Blazer` (Antonopoulos et al., CCS 2017), and `Themis` (Chen, Feng, Dillig;
  CCS 2017):** Program logics and automated verifiers for $k$-safety
  hyperproperties in Java/bytecode, using product-program trace alignment and
  decomposition into loop-free partitions to detect algorithmic timing
  side-channels.
- **`SecVerilog` (Zhang, Wang, Suh, Myers; ASPLOS 2015), `Silver` (Kopf et al.),
  and `Iodine` (Gleissenthall, Gökhan Kıcı, Stefan, Jhala; CCS 2019):**
  Hardware-level information-flow and constant-time verifiers for Verilog RTL;
  `SecVerilog` uses dependent security labels on wires/registers, while `Iodine`
  checks pipeline-aware constant-time execution of hardware designs without
  manual label annotations using relational clock-aligned invariants.
- **`Jif` (Myers et al., Cornell), `FlowCaml` (Simonet and Pottier, ICFP 2002),
  and `LIO` (Stefan, Russo, Mitchell, Mazières; Haskell Symposium 2011):**
  Foundational language-based Information-Flow Control (IFC) systems enforcing
  termination-insensitive or termination-sensitive non-interference via static
  security lattices (`Jif`, `FlowCaml`) or monadic floating-label runtime checks
  (`LIO`).

#### 3. Design philosophy, tradeoffs, and ecosystem comparisons

**Basis: documentation + derived.** Tools in Category 6.1 divide along three
architectural axes:

- **Source/IR level vs. binary/compiler preservation:** Source- and LLVM-level
  tools (`ct-verif`, `Pitchfork`, `FaCT`, `Constantine`, `Blazer`, `Themis`)
  benefit from structured loops and rich type/pointer provenance, making
  product construction fast, but they remain vulnerable to downstream LLVM back-
  end passes (`SimplifyCFG`, `SelectOptimize`, register spilling) that rewrite
  constant-time `select`/bitwise masks back into conditional branches (as shown
  by `Binsec/Rel` and Kaufmann et al.). Conversely, binary-level analyzers
  (`Binsec/Rel`, `Spectector`, `CacheAudit`) verify actual machine instructions
  with zero compiler trust, at the cost of bounded loop unrolling or difficult
  alias recovery. `CompCert-CT` and `Jasmin` bridge both worlds by verifying
  compilation preservation in Coq.
- **2-Safety Self-Composition vs. Type Systems vs. Abstract Interpretation:**
  Security type systems (`FaCT`, `Blade`, `SecVerilog`, `Jif`, `FlowCaml`) are
  compositional and run in milliseconds, but over-approximate value-dependent
  invariants (rejecting benign branches on public bounds or masked secrets
  unless explicit declassification is used). Relational symbolic execution and
  product programs (`ct-verif`, `Binsec/Rel`, `Jasmin -checkCT`, `CHL`,
  `Iodine`) are path- and value-precise (allowing branches on expressions that
  provably evaluate identically in both runs), while `CacheAudit` trades relational
  2-safety for quantitative single-run abstract domain counting (`#outputs`).
- **Architectural CT vs. Speculative CT (SCT):** Architectural CT (`ct-verif`,
  `CompCert-CT`, `Pitchfork`, `FaCT`) assumes sequential ISA semantics. Under
  Spectre-v1/v4, a bounds check `if (i < len) { y = arr2[arr1[i] * 64]; }` is
  architecturally constant-time when `i` and `len` are public, yet leaks secret
  memory `arr1[i]` when mispredicted! `Spectector`, `Blade`, `Binsec/Haunted`,
  and `Jasmin -checkSCT` extend the operational semantics with microarchitectural
  prophecy/oracle directives (`Step_spec`), revealing whether fences (`lfence`)
  or dataflow masking (`SLH` / `protect`) are required.

#### 4. Formal theory and trusted computing base (TCB)

**Basis: source + normative literature.**
- **`CompCert-CT`:** Mechanized in Coq. Every transition $S \xrightarrow{e, l}
  S'$ emits both external I/O events $e$ and a micro-leakage event $l \in
  \text{Leakage}$ (branch boolean, memory address). Compiler passes are proved
  using **leakage-preserving backward/forward simulations** where stack block
  allocations are related by a public-offset-preserving memory injection $j :
  \text{block} \to \text{Option}(\text{block} \times \mathbb{Z})$. TCB: Coq
  kernel, source/target leakage semantics, and assembly printer.
- **`Jasmin`:** Core language and x86-64/ARM compiler verified in Coq;
  `-checkCT` and `-checkSCT` rely on an OCaml abstract analyzer or reduction to
  `EasyCrypt` relational Hoare logic (`pRHL`).
- **`ct-verif`, `Binsec/Rel`, `Spectector`, `Pitchfork`, `Blade`:** Unverified
  analyzers (OCaml/Rust/Prolog) discharging verification conditions via external
  SMT solvers (`Z3`, `Bitwuzla`, `Boolector`) without proof-certificate replay
  in a proof kernel.

#### 5. Exact mapping onto Anneal's four `trusted/` primitives

**Basis: derived.** Anneal's four primitives express 2-safety constant-time,
speculative non-interference, and quantitative cache bounds without adding any
new axiom to `trusted/lean/`:

1. **`Language SemObs` & `Partial` (Synchronized Product Language
   `L_ct2`):**
   - For any base language `L` (such as `MirSemantics` or `X86Semantics`) with
     step-level leakage trace $\vec{\ell} \in \text{List LeakEvent}$ (branch
     targets, effective load/store addresses, division operands, and under SCT,
     transient speculative load addresses), construct the **paired 2-safety
     language `L_ct2`** in `theory/`:
     - `Prog := L.Prog`
     - `Query := { (q₁, q₂) : L.Query × L.Query // PubEq q₁ q₂ }` (two inputs
       agreeing on all public parameters and public memory regions, while secret
       regions vary freely).
     - `Out := { (o₁, o₂) : L.Out × L.Out // LeakageTrace o₁ = LeakageTrace o₂ }`
     - `SemObs`: Public output projection paired with the shared leakage trace
       `(PubObs o₁, LeakageTrace o₁)`.
     - `defined` vs. `Partial.ub`: `(L_ct2.sem prog ⟨q₁, q₂⟩).defined` holds iff
       both runs `L.sem prog q₁` and `L.sem prog q₂` are `defined` (memory-safe)
       **and** for all outcomes $o_1$ of $q_1$ and $o_2$ of $q_2$,
       $\text{LeakageTrace}(o_1) = \text{LeakageTrace}(o_2)$! Any secret-dependent
       branch, secret-dependent cache/memory address, or speculative transient
       load discrepancy sets `defined = False` (`Partial.ub`).
2. **`BehaviorCodec L₁ L₂`, `Compiles`, and `Abstracts`:**
   - **Leakage-Preserving Compilation (`CompCert-CT` / `Jasmin`):** In
     `Compiles L_mir_ct2 L_x86_ct2 codec s t`, `SemObs` includes the public
     leakage trace (or public stack-offset bijection via `codec`).
     `obs_decodeOut` guarantees that the compiled x86-64 binary's branch and
     memory-access trace matches the source MIR's certified constant-time
     leakage spine (`L_x86_ct2.obs o₂ = L_mir_ct2.obs o₁`). If an LLVM-style
     backend optimization rewrites a branchless `cmov`/`select` into a
     secret-dependent jump `jne`, the two paired x86-64 runs diverge in
     `LeakageTrace`, yielding `decodeOut o₂ = none` (or `defined = False`),
     which falsifies `Compiles`!
   - **Type-Based / Taint Abstraction (`FaCT`, `Blade`, `SecVerilog`,
     `CacheAudit`):** `Abstracts L_secType L_mir_ct2 codec v s` lifts paired
     concrete executions `s` into a single-pass security-lattice abstract
     interpreter `v` (tracking `Public` vs. `Secret` labels and `Transient`
     speculative taint, or `CacheAudit` abstract cache sets). Proving
     `Abstracts` once in `theory/` allows fast linear-time type/taint checking
     on `v` to discharge `defined` on `L_mir_ct2`.
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`:**
   - **`ProductiveOn` & `InhabitedPre`:** Prevents a constant-time transformation
     (`FaCT` / `Blade` / `SC-Eliminator`) from "eliminating leakage" by trapping
     all secret inputs in an unreachable precondition (`pre = ∅`) or aborting
     the execution (`val = ∅`).
   - **`EventualBehaviorOf`:** Crucial for **instruction-level constant-time
     dilation**: when a single MIR bitwise select expands to a 3-instruction
     constant-time mask sequence in x86-64 (`neg`, `and`, `xor`), both paired
     runs expand by the *exact same* deterministic step count $k$, so
     `EventualBehaviorOf` on `L_ct2` preserves lockstep timing equivalence
     across variable-length lowering passes.
   - **`StepResult.externalCall boundaryInv branches`:** Models **speculative
     execution oracles (`Spectector`/`Binsec/Haunted`)** and **cross-module calls**:
     at a call boundary or speculative barrier, `boundaryInv` asserts that all
     transient speculative registers are masked (`SLH` predicate register is
     architecturally synced) and no secret value resides in public caller-saved
     registers before yielding to `branches`.
4. **`VerificationResult` and `TrustPolicy`:**
   - Hardware constant-time guarantees depend on explicit **microarchitectural
     leakage assumptions** (e.g., `X86Mul64ConstantLatency`,
     `NoDataDependentOverclocking_DMP`, `SpectreV1WindowBounded_250`,
     `CacheLineGranularity_64B`). Representing each hardware leakage assumption
     as a positive obligation ID in `VerificationResult` (`ob.id ∈ waived ∨
     ob.prop`) audited by `TrustPolicy` makes the exact hardware leakage model
     explicit—so moving a crate from a desktop CPU to an embedded Cortex-M0+
     with variable-time 32-bit `MULS` simply rejects the `X86Mul64ConstantLatency`
     waiver in `TrustPolicy` without invalidating the mathematical proofs.

---

### Category 6.2: Cryptographic primitives, BigInt arithmetic, and protocol game-hopping

#### 1. Goals, target users, and vulnerability classes

**Basis: documentation + normative literature.** Cryptographic engineering spans
two tightly coupled verification layers:

1. **Mathematical and side-channel correctness of low-level primitives:**
   Multi-precision modular arithmetic over prime fields $\mathbb{F}_p$ (such as
   Curve25519 $\mathbb{F}_{2^{255}-19}$, NIST P-256, secp256k1, BLS12-381) and
   polynomial rings $\mathbb{Z}_q[X]/(X^n + 1)$ (ML-KEM/Kyber, ML-DSA/Dilithium)
   relies on unsaturated radix-$2^{51}$ or Montgomery radix-$2^{64}$ limbs,
   delayed carry propagation, Barrett/Montgomery reductions, and Number-Theoretic
   Transforms (NTT). A single missed carry bit (such as CVE-2014-3570 in OpenSSL
   `BN_sqr`, firing with probability $2^{-64}$, or CVE-2017-5754 / P-256 carry
   bugs) enables private-key recovery via invalid-curve or fault attacks.
2. **Computational and symbolic security of cryptographic protocols:**
   Multi-party and network protocols (TLS 1.3, Signal Double Ratchet, Messaging
   Layer Security RFC 9420, WireGuard, SSH, AWS KMS) must preserve secrecy,
   forward secrecy, post-compromise security, and authentication against active
   adversaries. Proofs proceed either in the **computational model** (Bellare–
   Rogaway game-hopping or Canetti's Universal Composability [UC], bounding an
   adversary's distinguishing advantage $\text{Adv}(\mathcal{A}) \le \sum_i
   \epsilon_i(\lambda)$ via reductions to DDH, LWE, orPRF/ROM assumptions) or
   in the **symbolic Dolev–Yao model** (unbounded sessions over ideal term
   algebras with equational theories).

#### 2. Concrete tool inventory, history, and lineage

**Basis: documentation + source.**

- **`Fiat-Crypto` (`mit-plv/fiat-crypto`, Erbsen, Philipoom, Gross, Sloan,
  Chlipala; IEEE S&P 2019):** A Coq library and certifying compiler pipeline
  that synthesizes straight-line, constant-time finite-field arithmetic in C,
  Rust, Go, Java, and Bedrock2 from high-level associative/distributive ring
  specifications, using abstract interpretation over limb range intervals to
  prove absence of integer overflow during delayed carry chains. Deployed in
  BoringSSL, Chrome, Android, Firefox (`nss`), WireGuard, and the Linux kernel.
- **`HACL*` and `EverCrypt` (`project-everest/hacl-star`, Zinzindohoué,
  Bhargavan, Protzenko, Beurdouche; CCS 2017 and Protzenko et al.; IEEE S&P
  2020):** Part of Project Everest (Inria / Microsoft Research / CMU). `HACL*`
  writes cryptographic primitives in `Low*` (a shallow embedding of C inside
  dependently typed `F*`), verifies memory safety, secret independence, and
  functional equivalence to pure mathematical RFC specs using `Z3`, and extracts
  readable C via `KaRaMeL` (`KreMLin`). `EverCrypt` unifies `HACL*` C code with
  `Vale` assembly under a single agile multiplexing API with CPU feature
  auto-detection (`AVX2`, `AVX-512`, `NEON`).
- **`Vale` (Bond, Hawblitzel, Kapritsos, Leino, Lorch, Parno, Rane, Setty,
  Thompson; USENIX Security 2017):** A verification framework for high-speed
  assembly language (AES-GCM, SHA-256, Poly1305, Curve25519 in x86-64/ARM)
  that generates verification conditions in `Dafny` and `F*` from annotated
  assembly procedures.
- **`Libjade` (`formosa-crypto/libjade`, Barbosa et al., Formosa Crypto):** A
  formally verified C-callable cryptographic library written in `Jasmin` and
  verified with `EasyCrypt` for functional correctness, ABI compliance, and
  constant-time/speculative-constant-time security (including X25519, ChaCha20-
  Poly1305, SHA-3, ML-KEM/Kyber, and ML-DSA/Dilithium).
- **`Cryptol` (`GaloisInc/cryptol`) and `SAW` (`GaloisInc/saw-script`, Dockins,
  Foltz, Tomb et al., CAV 2016; AWS `s2n` / `AWS-LC` verification, USENIX
  Security 2020 / CAV 2021):** `Cryptol` is Galois's domain-specific functional
  language for bit-precise cryptographic specifications. The Software Analysis
  Workbench (`SAW`) symbolically executes LLVM bitcode, x86-64 machine code,
  JVM bytecode, and `Cryptol` models into shared `SAWCore` terms and proves
  equivalence via AIG bit-blasting (`ABC`), SAT, and SMT (`Z3`/`Yices`), with
  HOL-style term-rewriting tactics for compositional sub-proofs.
- **`CryptoLine` (`fmlab-iis/cryptoline`, Tsai, Bowditch, Wang, et al.; CCS 2014
  / CCS 2019 / CAV):** Specialized verifier for low-level multi-limb assembly
  arithmetic (`OpenSSL`, `BoringSSL`, `pqm4` NTT) that splits verification into
  two orthogonal conditions: **algebraic polynomial equations** (discharged by
  Computer Algebra Systems `Singular`/`Macaulay2` via Gröbner bases) and
  **bitvector range/carry-overflow constraints** (discharged by `Boolector` /
  `Bitwuzla`).
- **`EasyCrypt` (`easycrypt/easycrypt`, Barthe, Grégoire, Heraud, Béguelin;
  CRYPTO 2011 / CCS 2011):** The flagship interactive proof assistant for
  code-based game-playing cryptographic proofs, combining an ambient higher-
  order logic with a **Probabilistic Relational Hoare Logic (`pRHL`)** over
  imperative `pWhile` programs and a quantitative Hoare logic for bounding
  failure event probabilities ($\Pr[G : E]$).
- **`CryptoVerif` (Blanchet; IEEE S&P 2006 / 2008):** An automatic and
  semi-automatic protocol verifier in the **computational model** that
  represents games in a probabilistic process calculus and applies pre-proved
  cryptographic game transformations (IND-CPA, INT-CTXT, ROM, CDH/GDH) to bound
  distinguishing advantage and extract OCaml/F* implementations.
- **`SSProve` (`SSProve/ssprove`, Abate, Haselwarter, Rivas, Van Muylder,
  Winterhalter, Hriţcu, Maillard, Spitters; CSF 2021), `FCF` (Petcher and
  Morrisett, POST 2015), and `CertiCrypt` (Barthe, Grégoire, Zanella Béguelin;
  POPL 2009):** Foundational Coq mechanizations of computational cryptography.
  `CertiCrypt` and `FCF` embed probabilistic games and couplings in Coq;
  `SSProve` formalizes **State-Separating Proofs** (Brzuska et al., ASIACRYPT
  2018) inside Coq's relational `pRHL` (`Relational` / `Monadic` effect
  systems), enabling modular algebraic composition of game packages.
- **`CryptHOL` (Basin, Lochbihler, Sefidgar; Journal of Cryptology 2020):** A
  foundational framework in `Isabelle/HOL` for game-based cryptographic proofs
  using generative probabilistic monads (`GPV`) and Lifting/Transfer packages.
- **`Owl` (`secure-foundations/owl`, Gancher, Gibson, Singh, Dharanikota, Parno;
  IEEE S&P 2023):** A compositional verification framework for cryptographic
  protocols that encodes computational security properties (IND-CCA, PRF, MAC,
  Diffie-Hellman) into an **information-flow and refinement type system** checkable
  by SMT (`Z3`), paired with the `OwlC` compiler that extracts verified,
  constant-time Rust code (`WireGuard`, `HPKE`, `TLS 1.3`).
- **`Tamarin Prover` (`tamarin-prover/tamarin-prover`, Meier, Schmidt, Cremers,
  Basin; CAV 2013):** Symbolic protocol verifier based on **multiset rewriting
  rules**, equational theories (Diffie-Hellman, bilinear pairings, XOR), and
  guarded first-order temporal trace properties, supporting both automated
  backward constraint solving and interactive proof guidance (used to standardize
  TLS 1.3, 5G-AKA, EMV, and Apple iMessage PQ3).
- **`ProVerif` (Blanchet; CSFW 2001 / IEEE S&P 2016) and `DeepSec` (Cheval,
  Kremer, Rakotonirina; IEEE S&P 2018):** Symbolic applied pi-calculus
  verifiers; `ProVerif` translates protocols into Horn clauses for unbounded-
  session secrecy, correspondence, and observational equivalence, while
  `DeepSec` decides exact trace equivalence for bounded-session protocols via
  constraint-solving decision trees.
- **`Squirrel Prover` (`squirrel-prover/squirrel-prover`, Baelde, Delaune,
  Jacomme, Koutsos, Moreau; CCS 2021):** An interactive first-order logic proof
  assistant for cryptographic protocols with **computational soundness**
  (Computationally Complete Symbolic Attacker `CCSA` logic), reasoning directly
  about unbounded sessions and mutable state without explicit probability
  calculations.
- **`DY*` (Bhargavan, Bichhawat, Do, Hosseyni, Küsters, Schmitz, Würtele;
  EuroS&P 2021) and `MLS*` (Bhargavan, Beurdouche, Naldurg et al., CCS 2023):**
  A modular symbolic Dolev–Yao verification framework embedded directly inside
  `F*` using a global trace invariant over timestamped protocol events, enabling
  verification of executable `F*`/Rust protocol code (such as the TreeKEM group
  key agreement in RFC 9420 `MLS*`).
- **`Libcrux` (`cryspen/libcrux`, Cryspen / AWS) and `hax` (`hacspec/hax`,
  Bhargavan, Buyse, Hospes, Protzenko, et al.):** `hax` is a Rust compiler
  frontend that translates safe Rust AST/THIR into multiple verification
  backends (`F*`, `Coq`, `ProVerif`, `EasyCrypt`, and `Lean`), powering
  `Libcrux`'s formally verified Rust implementations of ML-KEM (FIPS 203),
  ML-DSA (FIPS 204), X25519, and SHA-3 deployed in Firefox, NSS, and Rosenpass.

#### 3. Design philosophy, tradeoffs, and ecosystem comparisons

**Basis: documentation + derived.**
- **Correct-by-construction synthesis (`Fiat-Crypto`) vs. post-hoc verification
  (`SAW`, `CryptoLine`, `Vale`, `hax`):** `Fiat-Crypto` achieves complete
  proof-kernel foundational assurance (Coq) with zero manual per-prime proof
  effort by parameterizing the compiler over the prime $p$ and limb layout,
  whereas `SAW` and `CryptoLine` verify existing hand-written assembly (`AWS-LC`,
  `OpenSSL`) automatically using external SAT/SMT/CAS solvers. `HACL*`,
  `Libjade`, and `Libcrux`/`hax` occupy the middle ground: developers write code
  in a structured subset (`Low*`, `Jasmin`, or safe Rust) and prove functional
  refinement interactively (`F*`, `EasyCrypt`).
- **Foundational game-hopping (`SSProve`, `CertiCrypt`, `CryptHOL`) vs.
  standalone relational logics (`EasyCrypt`, `CryptoVerif`) vs. Type-Based
  Computational Security (`Owl`):** `EasyCrypt` provides rapid proof iteration
  for game hops via SMT-discharged `pRHL` rules, while `SSProve` and `CryptHOL`
  reduce the TCB to the Coq/Isabelle kernel via monadic state-separating
  packages. However, game-hopping across a 20-message protocol can require
  dozens of manual intermediate games; `Owl` eliminates explicit intermediate
  games by baking IND-CPA/PRF/DH hybrid reductions into typing rules, trading
  arbitrary reduction expressiveness for 10x smaller proof scripts and direct
  Rust extraction.
- **Symbolic Dolev–Yao (`Tamarin`, `ProVerif`, `DY*`) vs. Computational
  (`EasyCrypt`, `CryptoVerif`, `Squirrel`):** `Tamarin` and `ProVerif` excel at
  finding intricate multi-session state-machine and key-compromise-impersonation
  (KCI) attacks automatically, but treat cryptographic primitives as black-box
  function symbols (ignoring length leaks, modular arithmetic malleability, or
  nonce-reuse probability bounds). `Squirrel` and `Owl` bridge symbolic
  ergonomics with computational soundness.

#### 4. Formal theory and trusted computing base (TCB)

**Basis: source + normative literature.**
- **`Fiat-Crypto`, `SSProve`, `CertiCrypt`, `FCF`, `CryptHOL`:** Foundational
  kernel checking inside Coq or Isabelle/HOL.
- **`HACL*`, `EverCrypt`, `Vale`, `DY*`, `MLS*`, `Owl`:** Rely on the `F*` type
  checker (or `Owl` type checker), the `Z3` SMT solver without proof-certificate
  reconstruction, and the `KaRaMeL` / `OwlC` C/Rust extraction pipeline.
- **`SAW` and `CryptoLine`:** Rely on the unverified `SAWCore` symbolic
  simulator, `ABC` AIG equivalence checker, `Z3`/`Yices`/`Boolector`, and
  `Singular` Gröbner-basis engine (though `CryptoLine` supports optional Coq
  certificate checking for algebraic polynomial identities).

#### 5. Exact mapping onto Anneal's four `trusted/` primitives

**Basis: derived.**

1. **`Language SemObs` & `Partial`:**
   - **Primitive Arithmetic (`Fiat-Crypto`, `HACL*`, `CryptoLine`, `SAW`):**
     Source `L_field` has `Prog := FieldSpec p`, `Query := Inputs (ZMod p)`,
     `Out := ZMod p`, `SemObs := ZMod p`. Target `L_mir` / `L_x86` has `Out :=
     LimbArray × LeakTrace`. `Partial.ub` (`defined = False`) captures **limb
     carry overflow**, **non-canonical Montgomery output**, or **secret-dependent
     timing leak**.
   - **Protocol Game-Hopping (`EasyCrypt`, `SSProve`, `Owl`, `Tamarin`):**
     Each game $G_i$ is a `Prog` in `L_game`. `Query` is an adversary oracle
     schedule and initial randomness tape $\rho \in \{0,1\}^\lambda$. `Out` is
     the full protocol state + randomness + transcript; `SemObs` (`obs`) is the
     adversary's view and authorized leakage trace $\langle \text{Transcript},
     \text{Leakage} \rangle$. `Partial.ub` (`defined = False`) models **bad
     cryptographic events** (AEAD nonce reuse, decrypting unauthenticated
     ciphertext, or signing-oracle forgery on a target message).
2. **`BehaviorCodec L₁ L₂`, `Compiles`, and `Abstracts`:**
   - **Multi-Limb Representation Refinement (`Fiat-Crypto` / `Libcrux`):**
     `BehaviorCodec` maps abstract field elements $x \in \mathbb{F}_p$ to
     canonical multi-limb vectors $\vec{u} \in (\text{UInt64})^k$. Crucially,
     `decodeOut : LimbVector → Option (ZMod p)` checks that the output limbs
     satisfy the canonical representation invariant (e.g., for Curve25519
     `fe_tobytes`, that $2^{255}-19 \le v < 2^{255}$ has been fully reduced so
     $\sum u_i 2^{w_i} < p$); any unreduced or overflowing limb vector decodes
     to `none`, causing `Compiles` to fail closed!
   - **Bijective Randomness Coupling in Game Hops (`EasyCrypt` / `SSProve`):**
     In an information-theoretic bridging hop $G_i \to G_{i+1}$ (such as
     one-time-pad masking $r \mapsto r \oplus m$ or lazy random-oracle
     permutation), `encodeOut` and `decodeOut` define the **randomness-tape
     bijection**. Anneal's partial bijection laws (`decodeOut_encodeOut` and
     `encodeOut_of_decodeOut`) structurally verify in the Lean kernel that the
     randomness coupling is injective and measure-preserving on uniform finite
     tapes, while `obs_decodeOut` guarantees that the adversary's observable
     view is identical across the hop!
   - **Algebraic + Range Splitting (`CryptoLine` / `SAW`):** `Abstracts L_polybv
     L_x86 codec v s` lifts machine instructions into polynomial ring +
     bitvector range constraints `v` discharged in `theory/`.
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`:**
   - **`ProductiveOn` & `InhabitedPre`:** Prevents a protocol simulator `Sim` in
     UC (`SSProve`) from trivially preventing forgery by aborting/blocking all
     honest session transcripts (`val = ∅`).
   - **`StepResult.externalCall boundaryInv branches`:** Directly models
     **adversary oracle queries (`O_Sign`, `O_Dec`, `O_RO`, `O_Corrupt`)** in
     game-hopping and symbolic protocols: before yielding to the adversary,
     `boundaryInv` verifies state-separation invariants (e.g., ephemeral secret
     sponges are zeroized, nonce counters are strictly monotone, and challenge
     keys are isolated), and `branches` quantifies over all possible adversary
     return messages.
4. **`VerificationResult` and `TrustPolicy`:**
   - Information-theoretic hops and field-arithmetic carries are proved
     constructively (`ob.prop`), while **computational hardness assumptions**
     (such as `MLWE_768_Indistinguishable`, `DDH_Curve25519`,
     `SHA3_RandomOracleModel`) and **external solver certificates** (`SAW_ABC`,
     `Singular_Groebner`) are isolated as typed obligation IDs in `VerificationResult`
     governed by `TrustPolicy`. If a computational assumption is weakened, the
     audit report identifies the exact hops that rely on `ob.id ∈ waived`
     without risking `False.elim` across the pure arithmetic proofs.

---

### Category 6.3: Zero-knowledge proof systems (R1CS, Plonkish, AIR, and zkVMs)

#### 1. Goals, target users, and vulnerability classes

**Basis: documentation + normative literature.** Zero-knowledge proof compilers
(`Circom`, `Halo2`, `Plonky2`/`Plonky3`, `Noir`, `Gnark`, `Cairo`, `Leo`,
`Arkworks`) and general-purpose RISC-V zkVMs (`RISC Zero`, `SP1`, `Jolt`,
`OpenVM`, `Valida`) split computation into two distinct artifacts: an
**off-circuit witness generator** $W(x, w_{\text{priv}}) \to \vec{z} \in
\mathbb{F}_p^m$ (written in imperative Rust, C++, or Wasm) and an **in-circuit
polynomial constraint system** $\mathcal{C}(\vec{z}) = 0$ over a prime field
$\mathbb{F}_p$ (R1CS rank-1 constraints $(A\vec{z}) \circ (B\vec{z}) = C\vec{z}$,
Plonkish custom gates + `Plookup`/`LogUp` lookup arguments, or STARK Algebraic
Intermediate Representations [AIR] over execution trace tables).

As documented in comprehensive ZK vulnerability studies (Chaliasos et al.,
*SoK: What don't we know? Understanding Security Vulnerabilities in SNARKs*,
USENIX Security 2024; Pailoor et al., PLDI 2023), **over 90% of critical circuit
vulnerabilities are under-constrained bugs** (where $W$ computes the intended
value via `<--`, but $\mathcal{C}$ omits an `===` constraint, bit-length range
check, or zero-divisor check, allowing a malicious prover to supply a bogus
witness $\vec{z}' \neq W(x, w_{\text{priv}})$ that satisfies $\mathcal{C}(\vec{z}')
= 0$ and forges a proof for a false public output). The dual vulnerability is
**over-constrained circuits** (completeness bugs), where $\mathcal{C}$ rejects
valid witnesses on edge-case inputs, causing honest rollup provers to deadlock.

#### 2. Concrete tool inventory, history, and lineage

**Basis: documentation + source.**

- **`Picus` (`Veridise/Picus`, formerly `QED^2`, Pailoor, Chen, Wang, Rodríguez,
  Geffen, Morton, Chu, Guarnieri, Pettai, Dillig; PLDI 2023):** An automated
  verifier built by Veridise and UT Austin that proves **weak uniqueness
  (circuit determinism)**—namely, that for any fixed public/private input vector
  $\vec{x}$, at most one output vector $\vec{y}$ can be extended to a satisfying
  wire assignment $\vec{z} \in \mathcal{C}$—by alternating lightweight static
  known-uniqueness propagation lemmas with SMT queries over finite fields (`cvc5`
  $\mathbb{F}_p$ solver / `Z3`).
- **`Ecne` (`0xPARC/Ecne`, Franklyn Wang; 2022):** The pioneering automated
  R1CS uniqueness checker that introduced iterative algebraic dependency
  propagation Rules (linear deduction, $a \cdot b = 0$ case splitting, and
  unique binary decomposition over $\mathbb{F}_p$) to detect under-constrained
  `Circom` signals without requiring a separate functional specification.
- **`Coda` (Chen, Pailoor, Wang, Rodríguez, Dillig, et al.; CAV 2024):** A
  statically typed ZK DSL and refinement-type checker built in **Coq** that
  embeds polynomial constraint predicates directly into refinement types over
  $\mathbb{F}_p$, discharging verification conditions via SMT and extracting
  certified `Circom`/R1CS circuits that are provably both sound
  (non-under-constrained) and complete (non-over-constrained).
- **`Garden` (`formal-land/garden`, Formal Land; 2024–2026):** A foundational
  verification framework in **Rocq (Coq)** for verifying **Plonky3** AIR chips
  (`SP1`/`OpenVM` RISC-V and precompile tables), `Circom`, and `LLZK` circuits,
  using a monadic shallow DSL (`M.t`) that separates deterministic functional
  specifications from non-deterministic relational constraint systems.
- **`Cairo` Lean Proofs (Avni, Bentov, Goldwasser, Chiesa, et al.; *A
  Formal Verification of the Cairo CPU*, CPP 2022):** A machine-checked proof in
  **Lean 3 / Lean 4** (StarkWare & CMU) that the polynomial AIR constraints of
  the Cairo Turing-complete STARK CPU soundly and completely enforce the
  fetch-decode-execute semantics of the Cairo instruction set over
  $\mathbb{F}_p$.
- **`Leo` ACL2 Verifier (Coglio, McCarthy, Smith, Chin, et al., Kestrel
  Institute & Aleo; FMCAD 2021):** A certifying compiler validation toolchain
  built in the **ACL2** theorem prover that parses `Leo` ASTs and generated R1CS
  files and generates machine-checked ACL2 theorems proving that each compiler
  pass and R1CS gadget refines the source language semantics.
- **`Circomspect` (`trailofbits/circomspect`, Trail of Bits; 2022–2026):** A
  fast static analyzer and SARIF linter for `Circom` integrated into CI that
  detects unconstrained outputs, `<--` simple assignments without `===`, unused
  sub-circuit outputs, and field aliasing hazards.
- **`ZKAP` (Wen, Stephens, Chen, Ferles, Pailoor, Dillig, Isiguzo; USENIX
  Security 2024):** A semantic static detector for `Circom` circuits based on
  circuit dependence graphs (CDGs) and abstract pattern predicates that catches
  missing sub-component constraints and arithmetic overflow bugs across large
  production circuits (`tornado-cash`, `maci`, `semaphore`, `zkEVM`).
- **`Korrect` (2023) and `Horus` (2024):** Automated symbolic and logic-programming
  (`Soufflé` Datalog + SMT) analyzers for R1CS and `Halo2` Plonkish constraint
  systems that check input-output functional dependency and range-check coverage.
- **`LAMPE` (`reilabs/lampe`, Reilabs & Aztec; 2024–2026):** A formal
  verification framework for **Noir** (Aztec's Rust-inspired ZK language) that
  extracts Noir ACIR/SSA programs into **Lean 4**, providing tactics and
  standard-library lemmas over prime fields to prove functional correctness,
  soundness, and completeness of Noir cryptographic libraries.
- **`RISC Zero` (`risc0/risc0`), `SP1` (`succinctlabs/sp1`), and `Jolt`
  (`a16z/jolt`) zkVM Verifiers:** Industrial RISC-V (`RV32IM` / `RV64IM`) zkVMs:
  `RISC Zero` and `SP1` use STARKs (`Plonky3` BabyBear/KoalaBear fields with
  `LogUp` cross-table lookups and Groth16/Plonk recursion wrappers), while
  `Jolt` uses `Lasso` sumcheck lookup arguments to decompose instruction
  execution into structured lookup tables. Ongoing community and vendor efforts
  (`Garden`, `zkLean`, `sail-riscv` to Lean/Rocq) verify the correspondence
  between the RISC-V ISA specification, precompile chips (`SHA-256`, `Keccak`,
  `Secp256k1`, `Ed25519`), and the receipt-binding verifier (`ReceiptClaim::ok`
  and `hashable_key` inspected in corpus package
  `zkvm-receipt-binding-and-verification-boundaries`).

#### 3. Design philosophy, tradeoffs, and ecosystem comparisons

**Basis: documentation + derived.**
- **Specification-free uniqueness (`Picus`, `Ecne`) vs. Full Functional
  Specification (`Cairo` Lean, `Garden`, `LAMPE`, `Coda`, `Leo` ACL2):**
  Because writing a complete formal specification for a 100,000-constraint circuit
  is labor-intensive, `Picus` and `Ecne` verify a *relational 2-safety
  hyperproperty* on the constraint system $\mathcal{C}$ alone: $\forall \vec{x}
  \vec{z}_1 \vec{z}_2,\, \mathcal{C}(\vec{x}, \vec{z}_1) \land
  \mathcal{C}(\vec{x}, \vec{z}_2) \implies \vec{y}(\vec{z}_1) =
  \vec{y}(\vec{z}_2)$. Uniqueness catches missing constraints without a spec,
  but cannot detect if the unique function computed by $\mathcal{C}$ is the
  *wrong* mathematical function (e.g., wrong SHA-256 round constant). `Cairo`
  Lean, `Garden`, `LAMPE`, and `Coda` prove full functional refinement against a
  high-level spec.
- **SMT over $\mathbb{F}_p$ (`cvc5`, `Z3`) vs. Interactive Theorem Proving
  (`Lean 4`, `Rocq`, `ACL2`):** SMT solvers struggle with nonlinear finite-field
  polynomials of degree $\ge 3$ and variable-length loops (such as 64-round
  hashes or 256-bit multi-limb multiplication over a 31-bit BabyBear field),
  frequently timing out unless decomposed into small sub-circuits (`Picus`
  modularity). Interactive frameworks (`LAMPE` in Lean 4, `Garden` in Rocq,
  `Cairo` in Lean) verify arbitrary-scale circuits compositionally via ring
  tactics (`ring`, `omega`, `bv_decide`) with a tiny kernel TCB.

#### 4. Formal theory and trusted computing base (TCB)

**Basis: source + normative literature.**
- **`Cairo` Lean, `Garden` (Rocq), `LAMPE` (Lean 4), `Leo` (ACL2):** Proof
  assistant kernel + circuit extractor/parser from R1CS/Plonky3/Noir AST.
- **`Picus` (`QED^2`), `Coda`, `Korrect`:** Unverified static propagation engine
  + `cvc5`/`Z3` finite-field theory solver.
- **zkVM Receipt Verifiers (`risc0`, `sp1`, `jolt`):** Rely on circuit-to-ISA
  soundness, Fiat-Shamir random oracle heuristics, FRI proximity-gap conjectures,
  and trusted verifier context configuration (disabling `FakeReceipt` / `mock`
  prover modes and discharging recursive `Assumption` lists).

#### 5. Exact mapping onto Anneal's four `trusted/` primitives

**Basis: derived.** ZKP circuit and zkVM verification provides perhaps the
purest demonstration of why Anneal's four primitives belong together:

1. **`Language SemObs` & `Partial`:**
   - **High-Level Specification Language `L_spec`:** `Prog` is a pure functional
     or relational specification over bitvectors (`BitVec 32`, `BitVec 256`) or
     RISC-V architectural state; `Query` is `(pubIn, privIn)`; `Out` is `pubOut`;
     `SemObs` is `(pubIn, pubOut)`.
   - **Arithmetic Constraint Language `L_zk` (R1CS / Plonkish / AIR):**
     - `Prog` is a pair $\langle \mathcal{C}, W \rangle$ of a polynomial/lookup
       constraint system $\mathcal{C} \subseteq \mathbb{F}_p^m$ and a witness
       generator $W : \text{Query} \to \text{Option}(\mathbb{F}_p^m)$.
     - `Out` is the set of satisfying wire assignments $\vec{z} \in
       \mathbb{F}_p^m$ such that $\mathcal{C}(\vec{z}) = 0$.
     - `SemObs` (`obs : Out → SemObs`): Extracts the public input/output
       instance columns $(x(\vec{z}), y_{\text{pub}}(\vec{z}))$, erasing all
       internal advice and zero-knowledge blinding wires!
     - `defined` vs. `Partial.ub`: `(L_zk.sem ⟨C, W⟩ q).defined` holds iff (i)
       every wire assignment $\vec{z} \in \mathcal{C}$ matching public input
       $x(q)$ satisfies local gate/lookup well-formedness (no division by zero,
       no `LogUp` multiplicity wrap-around modulo $p$), and (ii) for fixed input,
       `obs z` is uniquely determined (`Picus`/`Ecne` determinism!).
2. **`BehaviorCodec L_spec L_zk`, `Compiles` (Soundness / No Under-Constraint),
   and `Abstracts`:**
   - **`decodeOut : F_p^m → Option L_spec.Out`:** Decodes the public output and
     limb wires of $\vec{z} \in \mathbb{F}_p^m$ into high-level bitvectors/integers
     *only if every limb wire satisfies its canonical range bound* (e.g.,
     $0 \le z_i < 2^{16}$), and returns `none` on any out-of-range field element
     (such as $p - 1$)!
   - **Why `Compiles L_spec L_zk codec s ⟨C, W⟩` = ZK Soundness:**
     `Compiles` states that for every satisfying wire assignment $\vec{z} \in
     \mathcal{C}$ accepted by the verifier, `codec.decodeOut z` must equal
     `some o₁` (never `none`!) where `o₁` satisfies `L_spec.sem s`. If the
     circuit is **under-constrained** (e.g., omits a 16-bit range lookup on a
     carry limb or allows a malicious witness $\vec{z}'$ with the wrong output),
     then $\vec{z}' \in \mathcal{C}$ either decodes to `none` (violating
     `Compiles`) or decodes to `some o₁'` that violates `s` (violating
     `Compiles`)!
   - **Notice how `obs_decodeOut` permits zero-knowledge blinding:** Because
     `obs` erases internal blinding factors $r \in \mathbb{F}_p$ while preserving
     public outputs, randomized witness assignments remain sound under
     `Compiles`.
3. **`ProductiveOn` & `InhabitedPre` (ZK Completeness / No Over-Constraint),
   `EventualBehaviorOf`, and `StepResult.externalCall`:**
   - **Why `ProductiveOn pre ⟨C, W⟩` = ZK Completeness:** Suppose a buggy or
     Goodharted circuit compiler emits the unsatisfiable constraint $1 = 0$.
     Then the set of satisfying wire assignments is empty (`val h = ∅`), so
     `Compiles` holds **vacuously**! Requiring `ProductiveOn pre ⟨C, W⟩` and
     `InhabitedPre pre` forces the witness generator $W$ to produce at least one
     valid assignment $\vec{z} \in \mathcal{C}$ for every valid input $q$
     satisfying `pre q`. Thus, **Anneal's `Compiles` + `ProductiveOn` is the
     exact mathematical definition of ZK Soundness + Completeness**!
   - **`EventualBehaviorOf`:** In zkVMs (`RISC Zero`, `SP1`, `Jolt`), a single
     RISC-V `ecall` to a `SHA-256` or `Keccak` precompile expands into 24–64
     trace rows in a secondary STARK table, while multi-segment continuations
     split execution across variable-length shards. `EventualBehaviorOf` aligns
     variable-row AIR traces with single-step ISA semantics without `Classical.choice`.
   - **`StepResult.externalCall boundaryInv branches`:** Models **Fiat-Shamir
     challenge sampling** (where `boundaryInv` asserts that all prior phase
     witness columns have been absorbed into the cryptographic sponge transcript
     before sampling lookup challenge $\beta, \gamma \in \mathbb{F}_p$) and
     **untrusted host-oracle hints** (where the prover queries an external
     nondeterministic hint oracle and `boundaryInv` enforces the in-circuit
     constraint check on the returned hint).
4. **`VerificationResult` and `TrustPolicy`:**
   - Separates machine-checked algebraic circuit equivalence (`ob.prop` proved
     in Lean) from cryptographic protocol and configuration assumptions
     (`FRIConjectureListDecoding`, `Poseidon2RandomOracle`,
     `Groth16TrustedSetup_BN254`, `Risc0DevModeDisabled`,
     `RecursiveAssumptionsEmpty`) tracked as explicit obligation IDs in
     `VerificationResult`.

---

### Category 6.4: Quantitative resource bounds, stack depth, and worst-case execution time (WCET)

#### 1. Goals, target users, and vulnerability classes

**Basis: documentation + normative literature.** Safety-critical embedded
systems (DO-178C Level A avionics, ISO 26262 ASIL-D automotive brake/steering
controllers, IEC 61508 industrial PLCs, bare-metal Rust microcontrollers, and
smart-contract virtual machines) require **hard quantitative upper bounds** on
two non-functional resources that standard functional-correctness semantics
abstract away:

1. **Stack memory consumption (maximum stack-frame depth):** In standard C,
   Rust, and CompCert memory models, the call stack has infinite capacity. On
   real microcontrollers (ARM Cortex-M, RISC-V RV32E, Tricore) or kernel stacks,
   exceeding the fixed stack region silently overwrites adjacent `.bss`/heap
   memory or triggers a fatal double-fault reset.
2. **Worst-Case Execution Time (WCET) and algorithmic step/gas complexity:**
   Hard real-time tasks must provably complete before their scheduling deadline
   $D$ across all admissible inputs and initial pipeline/cache states; smart
   contracts and network packet handlers must resist algorithmic complexity
   Denial-of-Service (DoS) and out-of-gas traps.

#### 2. Concrete tool inventory, history, and lineage

**Basis: documentation + source.**

- **`AbsInt aiT` and `StackAnalyzer` (Wilhelm, Ferdinand, Heckmann et al.,
  AbsInt Angewandte Informatik; *The Worst-Case Execution-Time Problem—Overview
  of Methods and Survey of Tools*, ACM TECS 2008):** The industry gold-standard
  commercial static analyzers certified for DO-178B/C Level A (Airbus A380/A350
  fly-by-wire). `aiT` decodes binary executables, reconstructs control-flow
  graphs (CFGs), runs value/loop-bound abstract interpretation, models exact CPU
  instruction caches and out-of-order pipelines via abstract interpretation to
  bound basic-block cycle counts, and solves for the longest execution path via
  **Implicit Path Enumeration Technique (IPET)** using Integer Linear
  Programming (ILP). `StackAnalyzer` computes worst-case stack usage along the
  call graph.
- **`CompCertS` (Besson, Blazy, Wilke; POPL 2017) and Stack-Aware CompCert /
  `Stacking` (Wang, Wilke, Shao; POPL 2019; Carbonneaux, Hoffmann, Ramananandro,
  Shao; PLDI 2014):** Extensions of `CompCert` in Coq that replace the infinite
  block-based memory model with a **finite address-space memory model** (`2^{32}`
  or `2^{64}` bytes) and an explicit abstract stack frame list, propagating
  quantitative stack-consumption bounds through register allocation (`Linear`)
  and frame layout (`Stacking`) down to assembly so that source-level stack
  bounds guarantee freedom from stack overflow on hardware.
- **`CerCo` (*Certified Complexity*, Amadio, Ayache, Campbell, Mulligan,
  Piccolo, Pollack, Regis-Gianas, Sacerdoti Coen, Stark, Tranquilli; JAR 2014):**
  A Matita/Coq-verified C compiler targeting 8051 and ARM/Lustre that
  instruments source C basic blocks with **exact cycle-accurate cost
  annotations** induced by the backend assembly translation, allowing source-level
  Hoare logic proofs to certify exact machine-code execution time.
- **`RAML` (*Resource Aware ML*, Hoffmann, Aehlig, Hofmann; POPL 2012 / TOPLAS
  2017):** An automated resource-analysis system for OCaml/functional programs
  based on Tarjan's **potential method of amortized analysis** extended to
  multivariate resource polynomials, reducing worst-case heap, stack, and tick
  bound inference to Linear Programming (LP) over type derivations.
- **`TiML` (Wang, Wang, Chlipala; OOPSLA 2017):** A dependently typed ML-style
  language (mechanized in Coq) whose type system indexes function types by loop/
  data-structure sizes and big-$O$ / exact recurrence time bounds, discharging
  recurrence relations automatically via `Master Theorem` and SMT solvers.
- **`Iris` Time Credits and Space Credits (`CFML` / `Iris$`, Charguéraud and
  Pottier, JFP 2019; Mével, Jourdan, Pottier, ICFP 2019; Spies et al.):**
  Embeds quantitative amortized complexity and heap/stack space bounds into
  higher-order concurrent separation logic in Coq by treating each execution
  step as consuming one linear `$1` time credit (`$n ∗ ...`) and each allocation
  as consuming space credits.
- **`Bound-T` (Tidorum / Niklas Holsti):** Early aerospace WCET and stack
  analyzer (used on ESA space missions) based on Presburger arithmetic
  (`Omega` calculator) for loop-bound inference and IPET path analysis.
- **`OTAWA` (Ballabriga, Cassé, Rochange, Sainrat; Universite de Toulouse),
  `Chronos` (Li, Liang, Mitra, Roychoudhury; NUS), `Heptane` (Hardy, Puaut,
  Seznec; Inria Rennes), `SWEET` (Gustafsson et al., Mälardalen), and `Platin`
  (`t-crest/platin`, Hepp, Huber, Prokesch, Puschner; TU Wien):** Open-source
  static WCET toolchains combining binary CFG extraction, abstract-execution
  loop bound discovery (`SWEET`), cache/pipeline persistence analysis
  (`Heptane`, `OTAWA`, `Chronos`), and LLVM-to-machine-code flow-fact relation
  tracking (`Platin` PML format).
- **`RapiTime` (Rapita Systems):** Hybrid measurement-based and structural
  timing analysis tool used in avionics/automotive that combines hardware/on-target
  execution trace timestamps with structural CFG path aggregation.
- **`KoAT` (`aprove-developers/KoAT2-Releases`, Brockschmidt, Fabian, Giesl,
  et al.; TOPLAS 2016 / CAV), `Cofloco` (Flores-Montoya, Hähnle; SAS 2014), and
  `Loopus` (Sinn, Zuleger, Veith; CAV 2014):** Automated complexity and runtime
  bound analyzers for C/LLVM integer transition systems using multiphase linear
  ranking functions, size-change abstractions, and difference-bound reset chains.
- **`Gasol` and `Gastap` (Albert, Gordillo, Rubio, Sergey; CAV 2020):**
  Cost-equation and recurrence-solver tools built on `Cofloco` that infer symbolic
  upper bounds on EVM (Ethereum Virtual Machine) gas consumption and stack usage.
- **`cargo-call-stack` (`japaric/cargo-call-stack`, Jorge Aparicio / Rust
  Embedded Working Group):** Whole-program static stack usage analyzer for
  bare-metal Rust (`no_std`, ARM Cortex-M) that combines LLVM `-Z emit-stack-sizes`
  sections with call-graph analysis over ELF binaries to detect recursion,
  indirect calls, and maximum stack depth.

#### 3. Design philosophy, tradeoffs, and ecosystem comparisons

**Basis: documentation + derived.**
- **Binary WCET (`aiT`, `OTAWA`, `Heptane`, `cargo-call-stack`) vs.
  Source-Level Cost Lifting (`CerCo`, `CompCertS`, `Platin`) vs. Type/Logic
  Bounds (`RAML`, `TiML`, `Iris` Credits):** Binary analyzers inspect actual
  machine instructions and linker-allocated stack frame sizes, which is
  mandatory for hardware cache/pipeline timing and register-spill stack accounting.
  However, compiler optimizations destroy loop structure and data-structure
  invariants needed to bound loop iterations (`Platin` must export flow-fact
  transformations across LLVM passes, which are unverified). `CerCo` and
  `CompCertS`/`Stacking` solve this inside Coq by proving that compiled machine
  code refines source code equipped with quantitative cost/stack budgets!
- **Amortized Potential (`RAML`, `Iris` `$n` credits) vs. Worst-Case Path ILP
  (`aiT`, `Heptane`):** ILP/IPET excels at flat embedded control loops with
  fixed iteration counts, but cannot express amortized data-structure bounds
  (e.g., splay trees or dynamic vector resizing where individual operations take
  $O(n)$ steps but any sequence of $m$ operations takes $O(m \log n)$). `RAML`
  and `Iris` time credits verify amortized bounds cleanly by storing potential
  functions inside data-structure invariants.

#### 4. Formal theory and trusted computing base (TCB)

**Basis: source + normative literature.**
- **`CompCertS`, `Stacking`, `CerCo`, `TiML`, `Iris` (`CFML`):** Foundational
  Coq kernel proofs over operational semantics indexed by step counters and
  concrete byte-stack bounds.
- **`AbsInt aiT`, `OTAWA`, `Heptane`, `KoAT`, `RAML`, `cargo-call-stack`:**
  Unverified C++/OCaml/Rust analyzers relying on external LP/ILP/SMT solvers
  (`CPLEX`, `lp_solve`, `Z3`) and vendor-supplied microarchitectural pipeline
  timing models. Note a major soundness hazard in `cargo-call-stack` and
  static call-graph tools: any unresolved dynamic dispatch (`dyn Trait`),
  function pointer, or inline assembly without an explicit stack-size annotation
  can invalidate the whole-program stack bound if not fail-closed.

#### 5. Exact mapping onto Anneal's four `trusted/` primitives

**Basis: derived.**

1. **`Language SemObs` & `Partial`:**
   - **Resource-Indexed Language `L_res` (Cycle & Stack Budgeted Semantics):**
     - `Query` carries the input state together with an explicit **initial
       stack capacity $S_{\max} \in \mathbb{N}$** and **cycle/gas budget
       $T_{\max} \in \mathbb{N}$**.
     - `Out` carries `(retVal, peakStackBytes, elapsedCycles)`.
     - `SemObs` (`obs`): Projects to `(retVal, peakStackBytes ≤ S_max,
       elapsedCycles ≤ T_max)`.
     - `defined` vs. `Partial.ub`: `(L_res.sem prog q).defined` is **false**
       (`Partial.ub`) whenever any execution path exceeds the hardware stack
       limit ($\text{sp} < \text{stack\_limit}$, i.e., `peakStackBytes > S_max`)
       or exceeds the hard real-time WCET deadline (`elapsedCycles > T_max`)!
2. **`BehaviorCodec L₁ L₂`, `Compiles`, and `Abstracts`:**
   - **Stack-Preserving & Cost-Lifting Compilation (`Stacking` / `CerCo`):**
     In `Compiles L_mir_res L_x86_res codec s t`, `codec.encodeQuery` translates
     the MIR stack/time budget into the target x86-64 byte stack budget
     (accounting for callee-saved register spills and 16-byte ABI alignment computed
     by the register allocator). If the x86-64 frame overflows $S_{\max}$ or
     misses the WCET bound $T_{\max}$, `decodeOut` returns `none` (or target is
     `Partial.ub`), falsifying `Compiles`.
   - **Amortized Potential & Ranking Abstraction (`RAML`, `KoAT`, `aiT` IPET):**
     `Abstracts L_potential L_mir_res codec v s` lifts concrete loop steps into
     a polynomial potential or lexicographic ranking transition system `v`.
     An untrusted LP/ILP solver (`RAML` / `aiT` / `KoAT`) computes dual Farkas
     multipliers or potential coefficients; Lean's kernel checks the linear
     inequality certificate in `O(n)` arithmetic steps to establish `Abstracts`!
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`:**
   - **Why `EventualBehaviorOf` + `ProductiveOn` Prevents Step-Budget Distortion:**
     As proved in Anneal corpus package
     `anneal-behavior-codec-and-progress-refinement-2026`, naive bounded-fuel
     semantics allow a degenerate morphism to map fuel $k \mapsto 0$, making an
     infinite loop appear "safe" because 0 steps cannot trigger UB!
     `EventualBehaviorOf` requires that every terminating source computation
     reaches a terminal target state in some finite number of concrete target
     steps $k'$, while `L_res` additionally bounds $k' \le T_{\max}$ inside
     `Out`.
   - **`StepResult.externalCall boundaryInv branches`:** Essential for
     **indirect calls and interrupt service routines (ISRs)** in
     `cargo-call-stack` and `Stacking`: before any external or indirect call,
     `boundaryInv` asserts that remaining stack headroom $\text{sp} -
     \text{stack\_base} \ge S_{\text{callee\_contract}}$ meets the callee's
     certified stack requirement, failing closed if an unannotated `dyn Trait`
     or ISR could overflow the stack.
4. **`VerificationResult` and `TrustPolicy`:**
   - Hardware WCET depends on microarchitectural assumptions outside the ISA
     (e.g., `NoInstructionCacheMiss_LockedSRAM`, `FlashWaitStates_Zero`,
     `InterruptPreemptionDepth_Max2`, `BusContentionBounded_DMA`). Tracking each
     hardware timing assumption as a positive obligation ID in
     `VerificationResult` (`ob.id ∈ waived ∨ ob.prop`) ensures that software
     loop-bound and stack-frame proofs remain 100% kernel-checked while the
     board-level hardware timing contract is audited explicitly in `TrustPolicy`.

---

### Category 6.5: Verified zero-copy parsers and binary wire formats

#### 1. Goals, target users, and vulnerability classes

**Basis: documentation + normative literature.** Network protocol stacks (TLS,
QUIC, TCP/IP, DNS, SSH, Bluetooth, 5G), OS kernel IPC/virtio drivers, file-system
metadata readers, and cryptographic certificate parsers (X.509 ASN.1 DER, CBOR,
Protobuf) sit directly on the untrusted attack surface. In-place **zero-copy
parsers** and serializers must simultaneously prevent three classes of bugs:

1. **Spatial memory, alignment, and validity UB:** Out-of-bounds slice reads,
   integer overflow in length-field arithmetic (`offset + len` wrapping around
   `usize::MAX`), unaligned pointer dereferences, or transmuting arbitrary wire
   bytes into a Rust/C struct with invalid bit patterns (e.g., a `bool` byte
   $\notin \{0, 1\}$, an invalid `enum` discriminant, or uninitialized padding
   bytes read as initialized data).
2. **Parser malleability and format confusion (`Format-String / Ambiguity`
   attacks):** Two distinct high-level messages $m_1 \neq m_2$ serializing to
   the same byte slice (`Serializer(m₁) = Serializer(m₂)`), or two different
   byte slices $b_1 \neq b_2$ parsing to the same logical message $m$ in a
   context where cryptographic signatures cover the parsed AST rather than the
   canonical wire bytes (as in X.509 BER vs. DER signature-bypass vulnerabilities
   and Bitcoin transaction-malleability bugs).
3. **Parser starvation / rejection of valid inputs:** A buggy parser or
   overly restrictive zero-copy layout check that rejects compliant protocol
   frames, breaking interoperability.

#### 2. Concrete tool inventory, history, and lineage

**Basis: documentation + source.**

- **`EverParse` and `3d` (`project-everest/everparse`, Ramananandro, Delignat-
  Lavaud, Fournet, Swamy, Chajed, Kobeissi, Protzenko; USENIX Security 2019):**
  Project Everest's verified zero-copy parser generator in `F*`. Takes C-like
  data-format descriptions in the `3d` DSL (with dependent length constraints
  and field actions), synthesizes zero-allocation in-place validator functions
  in `Low*`/C (or Rust), and proves memory safety, arithmetic overflow freedom,
  and **non-malleability (bijective parser-serializer round-trip)** in `F*`.
  Deployed in the Microsoft Windows kernel (Hyper-V vSwitch network packet
  validators, USB/VMBus drivers) and Azure confidential computing firmware.
- **`Vest` (`secure-foundations/vest`, Cai, Wang, Bosamiya, Gancher, Parno;
  CMU Secure Foundations Lab, USENIX Security 2025):** A formally verified,
  high-performance zero-copy binary parsing and serialization framework for
  **Rust** verified in **Verus**. Provides a combinator library and RFC-style
  DSL that proves memory safety, absence of panics/overflows, and mutual inverse
  round-trip theorems (`parse(serialize(x)) == Ok(x)` and canonical
  non-malleability `serialize(parse(b)) == b`) on zero-copy Rust slices `&[u8]`.
- **`Narcissus` (Delaware, Suriyakarn, Pit-Claudel, Ye, Chlipala; MIT, ICFP
  2019):** A foundational Coq framework for synthesizing correct-by-construction
  binary encoders and decoders from relational format specifications using
  extensible combinators and automated tactic synthesis (` Fiat` refinement).
- **`Comparse` (`lthms/coq-comparse`, Wallez, Protzenko, Beurdouche, Bhargavan;
  CCS 2023):** A bit-precise parser combinator library in `F*` and `Coq`
  designed specifically for cryptographic protocol verification (`DY*` / `MLS*`),
  automatically proving that message concatenation grammars are **prefix-free
  and injective** so symbolic Dolev–Yao term equality coincides with concrete
  bitstring equality.
- **Google `zerocopy` (`google/zerocopy`, Liebow-Feeser et al.):** The flagship
  industrial Rust crate for safe zero-copy parsing and serialization via custom
  derive traits (`TryFromBytes`, `FromZeros`, `FromBytes`, `IntoBytes`,
  `KnownLayout`, `Immutable`, `Unaligned`). Replaces manual `unsafe {
  core::mem::transmute }` with compile-time layout, alignment, padding, and
  bit-validity obligation checks (analyzed extensively across the Anneal
  `reference` corpus packages `zerocopy-byte-domain-and-write-controls-2026-10-14`
  and `zerocopy-validity-real-pass-certificate-alpha24`).
- **`RecordFlux` (`AdaCore/RecordFlux`, Componolit & AdaCore; 2020–2026):**
  Formal binary protocol specification language and code generator targeting
  **SPARK / Ada**, generating zero-copy message parsers and protocol state
  machines backed by `GNATprove` proofs of absence of runtime errors (AoRTE)
  and functional postconditions.
- **`DaeDaLus` (`GaloisInc/daedalus`, Diatchki et al., Galois; DARPA SafeDocs):**
  A monadic data-description language (DDL) for complex context-sensitive
  formats (such as PDF, ICC profiles, NITF, and UTF-8) that compiles format
  grammars into deterministic C++/Rust/Haskell parsers with formal semantics.
- **`Nail` (Bangert and Zeldovich; OSDI 2014) and `Hammer` (Patterson and
  Hirsch; LangSec):** Early influential LangSec parser generators; `Nail`
  introduced declarative grammar-to-struct bijections eliminating semantic
  actions, while `Hammer` provided bit-oriented packrat/GLR combinators in C.
- **`ASN1*` (Project Everest / Haonan et al.):** Formally verified zero-copy
  ASN.1 DER parser and serializer family in `F*`/`Low*` enforcing canonical
  shortest-length encoding to prevent X.509 certificate malleability.
- **`Kaitai Struct` (`kaitai-io/kaitai_struct`) and `Spicy` (`zeek/spicy`,
  Sommer et al., Corelight/Zeek):** Widely deployed industrial declarative
  binary format compilers (`Kaitai` YAML schemas; `Spicy` safe C++ streaming
  network parsers in Zeek IDS), emphasizing bounds-checked code generation
  without mechanized proof-assistant verification.

#### 3. Design philosophy, tradeoffs, and ecosystem comparisons

**Basis: documentation + derived.**
- **Zero-Copy Transmute (`zerocopy`) vs. Zero-Copy Slice Validation (`EverParse`,
  `Vest`, `ASN1*`) vs. AST-Allocating Combinators (`Narcissus`, `DaeDaLus`):**
  Google `zerocopy` achieves **zero CPU instructions** for `FromBytes` types
  (pure pointer cast `&[u8] -> &T`) and minimal discriminant checks for
  `TryFromBytes` (`is_bit_valid`), whereas wire formats with variable-length
  fields (`TLV`, `TLS`, `QUIC`, `ASN.1 DER`) cannot be cast to a single
  fixed-layout C struct and instead require `EverParse` / `Vest` / `Comparse`
  offset-advancing slice validators.
- **Bijective Non-Malleability vs. Permissive Parsing:** Postel's Law ("be
  liberal in what you accept") is fatal in cryptographic protocols: if a parser
  accepts non-canonical encodings (e.g., leading zeros in an ASN.1 integer or
  trailing unparsed bytes), an attacker can mutate a signed packet's wire bytes
  (changing its hash/transcript) without changing the parsed struct! `EverParse`,
  `Vest`, `Comparse`, and `ASN1*` enforce **strict bijection** on canonical
  slices.

#### 4. Formal theory and trusted computing base (TCB)

**Basis: source + normative literature.**
- **`Narcissus` and `coq-comparse`:** Foundational Coq kernel proofs of
  encoder-decoder inversion laws.
- **`EverParse` (`F*`/`Z3`) and `Vest` (`Verus`/`Z3`):** SMT-backed mechanized
  proofs of memory safety and parser-serializer round-trip bijections.
- **Google `zerocopy` (`cargo-anneal` / Anneal target):** In standard Rust,
  `#[derive(FromBytes, TryFromBytes, IntoBytes)]` relies on the proc-macro
  implementation and `unsafe` trait contracts; when verified with Anneal, those
  layout, padding, alignment, and bit-validity obligations are extracted from
  `rustc` MIR and proved inside the Lean 4 kernel (`Trusted.CrateTheorem`)!

#### 5. Exact mapping onto Anneal's four `trusted/` primitives

**Basis: derived.** Look at the mathematical signature of `BehaviorCodec L₁ L₂`
in Anneal's `trusted/lean/`:

- `encodeOut : L₁.Out → L₂.Out`
- `decodeOut : L₂.Out → Option L₁.Out`
- `decodeOut_encodeOut : ∀ o₁, decodeOut (encodeOut o₁) = some o₁`
- `encodeOut_of_decodeOut : ∀ o₂ o₁, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`
- `obs_decodeOut : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁`

**Anneal's `BehaviorCodec` is literally the exact formalization of a Verified
Non-Malleable Parser and Serializer Pair (`EverParse` / `Vest` / `Narcissus` /
`Comparse` / `zerocopy`)!**

1. **`Language SemObs` & `Partial`:**
   - **Abstract Typed Value Language `L_typed`:** `Out` is the high-level Rust
     ADT / protocol message $v \in T$.
   - **Concrete Byte-Slice / Pointer Language `L_bytes` (`MirSemantics`):**
     `Out` is the raw memory byte slice `b : List Byte` (with provenance,
     initialization bits `InitMask`, and alignment). `Partial.ub` (`defined =
     False`) captures out-of-bounds slice indexing, unaligned pointer
     dereference, reading uninitialized padding bytes on `IntoBytes`, or
     constructing an invalid discriminant in `TryFromBytes::try_read_from_bytes`.
2. **`BehaviorCodec L_typed L_bytes`, `Compiles`, and `Abstracts`:**
   - **Parser Completeness (`decodeOut_encodeOut`):** Every serialized message
     `encodeOut v` parses back to `some v` (`parse(serialize(v)) == Some(v)`).
   - **Strict Non-Malleability / Canonical Representation (`encodeOut_of_decodeOut`):**
     Whenever `decodeOut b = some v`, `encodeOut v = b` (`serialize(parse(b)) == b`)!
     This single law in Anneal's `BehaviorCodec` automatically guarantees that
     no two distinct byte slices $b_1 \neq b_2$ can ever parse to the same typed
     value $v$ (ruling out BER/DER malleability, trailing garbage bytes, and
     format-confusion attacks!).
   - **Fail-Closed Invalid Bit-Pattern Rejection (`decodeOut b = none`):**
     For Google `zerocopy::TryFromBytes` or `EverParse` validators, any byte
     slice `b` containing an invalid enum tag, non-boolean byte $\notin \{0,1\}$,
     unaligned address, or truncated length maps to `decodeOut b = none`. Under
     `Compiles`, the target validator is forbidden from returning `Ok(&T)` on
     any input where `decodeOut b = none`!
3. **`ProductiveOn` & `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`:**
   - **`ProductiveOn` & `InhabitedPre`:** A trivial way to write a `TryFromBytes`
     or `EverParse` validator that never transmutes invalid bytes is to return
     `Err(())` on **every** byte slice! Pairing `Compiles` with `ProductiveOn
     ValidWirePre parser` proves that every valid wire encoding is actually
     accepted (`Ok`), preventing vacuous rejection.
   - **`StepResult.externalCall`:** Models streaming I/O buffer refills or
     `EverParse` field-action callbacks (`boundaryInv` asserts that the slice
     prefix up to `offset` has been validated before invoking the user callback).
4. **`VerificationResult` and `TrustPolicy`:**
   - Tracks target ABI layout assumptions (such as `TargetEndianness_Little`,
     `TargetPointerWidth_64`, or external RFC schema assumptions) as positive
     `TrustPolicy` obligation IDs while every `zerocopy` / `Vest` bit-validity
     and bounds check is discharged constructively in Lean.

---

### Category 6.6: Cross-language FFI, CHERI hardware capabilities, and secret zeroization

#### 1. Goals, target users, and vulnerability classes

**Basis: documentation + normative literature.** Real-world Rust and C crates
do not execute in a closed single-language world: they link against C/assembly
libraries (`libc`, `BoringSSL`, `sqlite`, OS syscalls), run on hardware with
capability-enforced pointer provenance (`CHERI` / ARM `Morello`), and must
securely erase cryptographic keys from stack and heap memory before returning
(`zeroize`). Three catastrophic failure modes occur at these boundaries:

1. **Cross-Language FFI ABI, Representation, and Re-Entrancy Mismatches:**
   Passing a Rust reference or boxed closure across `extern "C"` into C or
   OCaml can violate aliasing invariants (`&mut T` aliased by a retained C
   pointer), corrupt garbage-collector / allocator headers, or trigger **open-
   world callback re-entrancy** (where an external C function calls back into
   the Rust module while the module's private ADT invariant is temporarily
   broken—the exact exploit mechanized in Anneal corpus package
   `anneal-structural-external-calls-and-tcb-mutation-testing-2026`).
2. **Pointer Provenance Forgery and Spatial/Temporal Capability Violations:**
   In integer-address architectures, casting an integer `usize` to a pointer or
   performing out-of-bounds pointer arithmetic (`p + offset`) can forge access
   to adjacent allocations. Hardware capability architectures (`CHERI`) attach
   unforgeable 128-bit bounds, permissions, and a 1-bit validity tag to every
   pointer register and memory word.
3. **Dead-Store Elimination (DSE) and Register-Spill Leakage of Secrets:**
   When a cryptographic routine zeroes a stack buffer `memset(secret_key, 0,
   32)` immediately before the variable goes out of scope, standard optimizing
   compilers (LLVM, GCC, `rustc`) delete the `memset` as a "dead store" because
   the buffer is never read again in the abstract machine (`What You See Is
   Not What You Execute`, D'Silva, Payer, Song; USENIX HotOS 2015). Even when
   `memset_s` or `write_volatile` zeroes the stack array, compiler register
   allocators silently leave copies of `secret_key` in callee-saved or scratch
   CPU registers, stack spill slots, or red-zone bytes!

#### 2. Concrete tool inventory, history, and lineage

**Basis: documentation + source.**

- **`DimSum` (Sammler, Spies, Song, D'Osualdo, Krebbers, Garg, Dreyer; MPI-SWS,
  POPL 2023):** A decentralized Coq/Iris framework for **multi-language
  semantics and compositional compiler/FFI verification**. Instead of baking a
  fixed global memory model into all languages, `DimSum` models each module (in
  high-level `Rec`, `Asm` assembly, or mathematical `Spec`) as an event-driven
  labeled transition system communicating via call/return events and uses
  combinators + `Simuliris`-style relational separation logic to verify
  cross-language linking, pointer-to-integer casts, and stack-switching
  coroutines.
- **`SepCompCert` (Kang, Kim, Hur, Dreyer, Viktor Vafeiadis; POPL 2016),
  `CompCertM` (Song, Cho, Kim, Hur; POPL 2020), and `CompCertO` (Koenig and
  Shao; Yale, POPL 2021):** Compositional extensions of `CompCert` in Coq.
  `SepCompCert` handles separate compilation of C modules; `CompCertM` supports
  mixed-language linking between C and hand-written assembly (`RSim` relational
  simulations); `CompCertO` introduces **open simulations Indexed by Kripke
  worlds and call/return language interfaces** so each pass composes both
  horizontally (linking) and vertically (compilation).
- **`VeriFFI` (Wang, Paraskevopoulou, Appel; Princeton, PLDI 2024):** A
  foundational Coq framework connecting `CertiCoq` (verified OCaml/Gallina) and
  `VST` (Verified Software Toolchain for CompCert C), using **foreign interface
  specifications** that relate functional Coq inductive types (`list`, `tree`)
  to heap-allocated C/GC graph representations while preserving garbage-collection
  roots across FFI calls.
- **`RLBox` (`PLSysSec/rlbox_sandboxing_api`, Narayan, Disselkoen, Garfinkel,
  Froyd, Rahm, Sorokin, Stefan, Shacham; USENIX Security 2020):** A C++ type-
  driven library sandboxing framework deployed in **Mozilla Firefox** (isolating
  `libgraphite`, `libogg`, `libexpat`, `hunspell`, `woff2` inside WebAssembly /
  process sandboxes) that tags all values and pointers crossing the FFI boundary
  as `tainted<T>` and enforces compile-time validation gates before untainted
  host code can branch on or dereference them.
- **`Sail-CHERI` and ARM `Morello` (`CTSRD-CHERI/sail-cheri-riscv` and
  `sail-morello`, Nienhuis, Joannou, Woodruff, French, Sewell, Watson,
  Neumann, Moore, Naylor, et al.; IEEE S&P 2020):** Authoritative instruction-set
  architecture specifications in the **Sail** language (compiled to `Isabelle/HOL`,
  `Coq`/`Rocq`, `Lean`, and C emulators) with machine-checked proofs in
  `Isabelle/HOL` of universal capability monotonicity (no execution sequence can
  ever escalate permissions or widen spatial bounds of held capabilities).
- **`Cerberus-CHERI` and `VIP-CHERI` (Memarian, Matthiesen, Lingard, Nienhuis,
  Chisnall, Watson, Sewell; ASPLOS 2019 / PLDI 2022):** Formal semantics of
  C and capability-C in Coq/Lem integrating the **PNVI-ae-udi** (Pointer-Numeric
  Value Integration) and **VIP** (Verified Integer-Pointer) provenance models
  with CHERI hardware capability tags.
- **`Secret-Erasure CompCert` (Besson, Blazy, Dumas, Laporte; *Towards a Formally
  Verified Secret-Erasing C Compiler*, and Barthe et al.):** Extends `CompCert`
  in Coq to preserve **secret erasure (`zeroize`)** down to machine code,
  instrumenting register allocation and stack-frame deallocation so that every
  register and stack spill slot tainted by a secret variable is explicitly
  scrubbed before function return.
- **`WYSIWYC` / `Zeroize-LLVM` (Simon, Chisnall, Anderson; *What You Get Is
  What You C: Controlling Side Effects in Mainstream C Compilers*, EuroS&P 2018;
  and Tuan, et al., *Clean-Up After Yourself: Compiler-Supported Secret
  Erasure*):** Compiler back-end extensions for Clang/LLVM that introduce
  `__attribute__((zero_call_used_regs))` (now in GCC 11+ / Clang 15+) and stack
  frame scrubbing to prevent register/spill remnant leaks.
- **Rust `zeroize` (`RustCrypto/utils/zeroize`, Tony Arcieri / RustCrypto):**
  The standard Rust cryptographic secret-erasure crate (`Zeroize`,
  `ZeroizeOnDrop`), combining `core::ptr::write_volatile` with
  `core::sync::atomic::compiler_fence(Ordering::SeqCst)` and architecture-specific
  inline assembly barriers so LLVM cannot elide the zeroing stores as dead
  writes.

#### 3. Design philosophy, tradeoffs, and ecosystem comparisons

**Basis: documentation + derived.**
- **Decentralized Event Semantics (`DimSum`, `CompCertO`) vs. Shared-Memory
  Separation Logic (`VeriFFI`, `CompCertM`) vs. Tainted Sandboxing (`RLBox`):**
  `VeriFFI` and `CompCertM` verify trusted C and assembly modules that share a
  single flat address space with the caller, requiring explicit separation-logic
  ownership transfer of heap/stack footprints. `RLBox` assumes the foreign C
  library is **malicious or buggy** and isolates its memory inside a Wasm/CHERI
  sandbox, reducing FFI verification to checking the `tainted<T>` marshaling
  codec. `DimSum` unifies both by treating memory sharing and sandboxing as
  pluggable event-translation wrappers (`BehaviorCodec`!).
- **Library-Level `write_volatile` (`zeroize`) vs. Compiler-Integrated Secret
  Scrubbing (`Secret-Erasure CompCert`, `Jasmin`):** While Rust's `zeroize`
  prevents LLVM from deleting the explicit `write_volatile` loop over the User's
  struct in memory, it **cannot** erase secret values that LLVM's register
  allocator temporarily spilled to an anonymous stack slot during a complex
  calculation! Full secret erasure requires verifying the MIR-to-assembly
  register-allocation and stack-frame pass (`Stacking` / `Secret-Erasure
  CompCert`).

#### 4. Formal theory and trusted computing base (TCB)

**Basis: source + normative literature.**
- **`DimSum`, `CompCertO`, `CompCertM`, `SepCompCert`, `VeriFFI`,
  `Secret-Erasure CompCert`:** Foundational Coq kernel proofs.
- **`Sail-CHERI` / `Morello`:** Sail specification + Isabelle/HOL kernel proofs
  of capability monotonicity.
- **Rust `zeroize`:** Relies on `rustc`/LLVM honoring volatile store +
  `compiler_fence` semantics and does not cover compiler-generated stack spills.

#### 5. Exact mapping onto Anneal's four `trusted/` primitives

**Basis: derived.**

1. **`Language SemObs` & `Partial`:**
   - **Multi-Language FFI & CHERI Capability Semantics (`DimSum`, `Sail-CHERI`,
     `Cerberus-CHERI`):**
     - `Out` in `L_cheri` / `L_mir` carries pointer values as capability tuples
       `(addr, base, length, perms, tag : Bool)` (matching Anneal's allocation-id
       provenance and bounds in `MirSemantics`). Any dereference with `tag =
       false`, `addr ∉ [base, base + length)`, or missing `Load`/`Store`
       permission transitions immediately to `Partial.ub` (`defined = False`).
   - **Post-Return Secret-Erasure Semantics (`Secret-Erasure CompCert`,
     `zeroize`):**
     - In `L_zeroize`, `Out` includes the post-return deallocated stack frame
       and caller-visible scratch registers `(retVal, postStackBytes,
       postScratchRegs)`.
     - `defined` requires that upon returning from any function holding a
       `ZeroizeOnDrop` secret, all bytes in `postStackBytes` (including compiler
       spill slots!) and `postScratchRegs` equal `0x00`.
2. **`BehaviorCodec L₁ L₂`, `Compiles`, and `Abstracts`:**
   - **FFI Marshaling & `RLBox` Taint Validation (`VeriFFI`, `RLBox`, `DimSum`):**
     `BehaviorCodec L_rust L_c_abi` defines the exact cross-language C ABI
     representation bijection (`#[repr(C)]` struct layout, pointer provenance,
     and ownership invariants). For `RLBox`-style sandboxed FFI, `decodeOut :
     TaintedCOut → Option ValidatedRustOut` runs the boundary validator and
     returns `none` on any out-of-bounds sandbox offset or invalid enum
     discriminant!
   - **Zeroization Verification via `decodeOut = none`:** In `Compiles
     L_idealZeroized L_x86 codec s t`, `codec.decodeOut` inspects the post-return
     x86-64 stack frame and scratch registers and **returns `none` if any secret-
     tainted spill slot or register is non-zero**! Consequently, if a backend
     dead-store-elimination pass deletes the zeroing store or leaves a secret
     limb in `%r11`, `decodeOut` yields `none`, and `Compiles` fails in the
     Lean kernel!
3. **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
   `StepResult.externalCall`:**
   - **`StepResult.externalCall boundaryInv branches` (The Exact FFI & Callback
     Re-Entrancy Gate!):** As proved in Anneal corpus package
     `anneal-structural-external-calls-and-tcb-mutation-testing-2026`,
     `StepResult.externalCall boundaryInv branches` was specifically designed to
     solve the cross-language FFI and re-entrancy problem (`DimSum` / `CompCertO`
     / `VeriFFI`):
     - Before invoking an `extern "C"` function or dynamic callback, the
       interpreter checks `boundaryInv` (asserting that all private module/ADT
       invariants are restored, CHERI capabilities passed to the callee are
       bounds-restricted, and secret scratch buffers are scrubbed).
     - If `boundaryInv` fails, the step transitions to `Partial.ub` (`defined =
       False`).
     - If `boundaryInv` holds, `branches` demonically havoc-updates all memory
       reachable by the external callee while preserving caller-local frame
       isolation.
4. **`VerificationResult` and `TrustPolicy`:**
   - Foreign C/assembly functions that are not verified in Lean (e.g., an OS
     `getrandom` syscall or hardware cryptographic accelerator) are isolated as
     explicit external contract obligations (`ExternABIContract_libc_getrandom`)
     in `VerificationResult` governed by `TrustPolicy`.

---

### Comparative synthesis matrix across all six categories

| Category | Representative Tool Families | Primary Verification Target | Anneal `Language SemObs` & `Partial.ub` (`defined = False`) | Anneal `BehaviorCodec`, `Compiles` & `Abstracts` | Anneal `ProductiveOn`, `EventualBehaviorOf` & `StepResult.externalCall` | Anneal `VerificationResult` (`TrustPolicy` Waivers) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **6.1: 2-Safety, CT, SCT & IFC** | `CompCert-CT`, `Jasmin` (`-checkCT`/`-checkSCT`), `FaCT`, `ct-verif`, `Binsec/Rel` & `Haunted`, `Blade`, `Spectector`, `Pitchfork`, `CacheAudit`, `Constantine`, `CHL`/`Blazer`/`Themis`, `SecVerilog`/`Iodine`, `Jif`/`FlowCaml`/`LIO` | Architectural & speculative constant-time non-interference; cache leakage bounds | Paired 2-safety language `L_ct2`: `Partial.ub` on secret-dependent branch, cache address, variable-time opcode, or speculative transient leak | `obs_decodeOut` locks paired leakage traces across compilation; `Abstracts` lifts to security-type / taint / cache abstract domains | `ProductiveOn` prevents empty-domain CT transformations; `EventualBehaviorOf` aligns lockstep instruction expansion; `externalCall` checks `SLH` masks at calls | Hardware timing contracts (`X86Mul64ConstantLatency`, `SpectreWindow_250`, `CacheLine_64B`) |
| **6.2: Crypto Primitives & Protocol Game-Hopping** | `Fiat-Crypto`, `HACL*`/`EverCrypt`, `Vale`, `Libjade`, `Cryptol`/`SAW`, `CryptoLine`, `EasyCrypt`, `CryptoVerif`, `SSProve`/`FCF`/`CertiCrypt`, `CryptHOL`, `Owl`, `Tamarin`, `ProVerif`/`DeepSec`, `Squirrel`, `DY*`/`MLS*`, `Libcrux`/`hax` | Multi-limb $\mathbb{F}_p$ / NTT carry safety; computational game-hopping & Dolev–Yao protocol security | `Partial.ub` on limb carry overflow, non-canonical field output, AEAD nonce reuse, or signing-oracle forgery bad events | `decodeOut = none` rejects unreduced limbs; `decodeOut_encodeOut` + `encodeOut_of_decodeOut` certify bijective randomness-tape couplings across game hops | `ProductiveOn` ensures non-aborting UC simulators; `StepResult.externalCall` models adversary `O_Sign`/`O_Dec`/`O_RO` oracle queries with state-separation `boundaryInv` | Computational hardness assumptions (`MLWE_768`, `DDH_25519`, `ROM`) & external `SAW`/`Singular` certificates |
| **6.3: Zero-Knowledge Proofs & zkVMs** | `Picus` (`QED^2`), `Ecne`, `Coda`, `Garden`, `Cairo` Lean, `Leo` ACL2, `Circomspect`, `ZKAP`, `Korrect`/`Horus`, `LAMPE` (Noir/Lean 4), `RISC Zero`, `SP1`, `Jolt` | R1CS, Plonkish (`Halo2`/`Plonky3`), AIR & RISC-V zkVM circuit soundness + completeness | `SemObs` is public statement $(x, y_{\text{pub}})$ (erasing ZK blinding); `Partial.ub` on missing range check, witness ambiguity, or `LogUp` overflow | **`Compiles` = ZK Soundness** (`decodeOut = none` rejects out-of-range field limbs); `obs_decodeOut` preserves public instance columns | **`ProductiveOn` = ZK Completeness** (every valid input admits a satisfying witness $\vec{z} \in \mathcal{C}$); `EventualBehaviorOf` aligns zkVM precompile rows; `externalCall` gates Fiat-Shamir challenges | `FRIConjecture`, `KZG_BN254`, `Poseidon2_ROM`, `Risc0DevModeDisabled`, `RecursiveAssumptionsEmpty` |
| **6.4: Quantitative Resource Bounds & WCET** | `AbsInt aiT` & `StackAnalyzer`, `CompCertS`, `Stacking`, `CerCo`, `RAML`, `TiML`, `Iris` Time Credits (`CFML`), `Bound-T`, `OTAWA`/`Chronos`/`Heptane`/`SWEET`/`Platin`, `RapiTime`, `KoAT`/`Cofloco`/`Loopus`, `Gasol`, `cargo-call-stack` | Hard real-time WCET cycle bounds, maximum call-stack byte depth, amortized heap/gas complexity | `Query` carries $(S_{\max}, T_{\max})$; `Partial.ub` on stack overflow ($\text{sp} < \text{limit}$) or deadline overrun ($\text{cycles} > T_{\max}$) | `Compiles` propagates concrete stack spill sizes & cycle costs from MIR to x86-64; `Abstracts` checks LP/Farkas potential & ranking certificates | `EventualBehaviorOf` + `ProductiveOn` block step-zero fuel collapse while guaranteeing termination within $T_{\max}$; `externalCall` checks stack headroom at indirect calls/ISRs | Microarchitectural pipeline & cache tables (`LockedSRAM`, `FlashWaitStates_Zero`, `MaxISRDepth_2`) |
| **6.5: Verified Zero-Copy Parsers & Wire Formats** | `EverParse` (`3d`), `Vest`, `Narcissus`, `Comparse`, Google `zerocopy`, `RecordFlux`, `DaeDaLus`, `Nail`/`Hammer`, `ASN1*`, `Kaitai Struct`, `Spicy` | Spatial safety, bit-validity, alignment, and non-malleable parser-serializer bijections | `Partial.ub` on slice OOB, length-addition overflow, unaligned cast, uninitialized padding read, or invalid enum discriminant | **`BehaviorCodec` is a Non-Malleable Parser/Serializer Pair:** `decodeOut_encodeOut` = parse-serialize roundtrip; `encodeOut_of_decodeOut` = canonical non-malleability; `decodeOut = none` rejects invalid bit patterns | `ProductiveOn` guarantees parser completeness on valid wire messages (ruling out always-`Err` validators); `externalCall` gates streaming buffer callbacks | Target ABI layout parameters (`LittleEndian`, `PointerWidth_64`) & external RFC wire schema versions |
| **6.6: Cross-Language FFI, CHERI & Zeroization** | `DimSum`, `SepCompCert`/`CompCertM`/`CompCertO`, `VeriFFI`, `RLBox`, `Sail-CHERI`/`Morello`, `Cerberus-CHERI`/`VIP-CHERI`, `Secret-Erasure CompCert`, `WYSIWYC`/`Zeroize-LLVM`, Rust `zeroize` | Multi-language FFI linking, callback re-entrancy safety, CHERI capability monotonicity, and DSE-resistant secret erasure | `Partial.ub` on untagged/out-of-bounds CHERI capability dereference, FFI aliasing violation, or non-zero secret remnant in post-return stack/registers | `BehaviorCodec` checks `#[repr(C)]` FFI layout & `RLBox` taint validation; `decodeOut = none` rejects any non-zero post-return secret spill slot or scratch register | **`StepResult.externalCall` is the exact FFI & re-entrancy gate** (enforcing `boundaryInv` before external calls and demonically branching over returns) | Unverified foreign C/syscall specifications (`ExternContract_libc`, `HardwareRNG_Entropy`) |

### Phase-2 Long-Tail Ecosystem Additions and Primitive Mappings

Basis: documentation, derived — incorporates the Stage-2 exhaustive long-tail
tool discovery sweep (`agent_a_shard_*_tools.md`) into the package's tool
taxonomy and four-primitive `trusted/` mapping.

- **LLVM `__builtin_ct_select` (2024-2025), Coq SCT Jasmin Compiler (POPL 2025),
  `CT-Wasm` (POPL 2019), `SideTrail`, and `CTGREP` / `LIF`:** Compiler
  optimization barriers and Coq/Isabelle verifiers preserving Constant-Time and
  Speculative Constant-Time across lowering.
- **`LeaVe` (CCS 2023), `UPEC` (DAC 2019), `Revizor` (`microsoft/sca-fuzzer`),
  and `Hyper Hoare Logic (HHL)` / `AutoHyper` (PLDI 2024 / TACAS 2023):**
  2-safety relational RTL hardware-software leakage contract checkers and
  $\forall^*\exists^*$ hyperproperty verifiers.
- **Rupicola/Bedrock2 (`mit-plv/rupicola`), `s2n-bignum` (`awslabs/s2n-bignum`
  in HOL Light), `mlkem-native` (`CBMC` + `SLOTHY` + `s2n-bignum`), and
  `EasyUC`/`IPDL`:** Relational cryptographic synthesis, machine-code byte
  verification in HOL Light, and Universal Composability / MPC proof frameworks.
- **CertiPlonk (`NethermindEth/CertiPlonk`), Clean (`zksecurity/clean`), ArkLib
  (`Verified-zkEVM/ArkLib`), LLZK (`Veridise/llzk-lib`), and `acl2-jolt`
  (2024-2025):** Lean 4, MLIR, and ACL2 frameworks verifying Plonky3/AIR/Jolt ZK
  circuit soundness (`Compiles`) and witness completeness (`ProductiveOn`).
- **`C4B` (PLDI 2015), `RelCost` (POPL 2017), `LiquidATE` (POPL 2020), Menhir
  Coq-Verified LR(1) Parser (ESOP 2012), `Cogent` (ICFP 2016), `CHERIoT`, and
  `Iris-MSWasm` (POPL 2023):** Amortized C/relational cost logics, verified
  LR(1) grammar parsers, linear C FFI types, and microcontroller capability
  compartments.

## Boundaries

- **Not examined — standalone execution of third-party external verifiers:**
  This report synthesizes the architecture, formal semantics, TCB boundaries,
  and exact mathematical embeddings of the 75 tools across Categories 6.1–6.6
  from primary literature, upstream repositories, and existing Anneal
  `reference` corpus packages (`df55c524a051d59e7dd35564f282b30d29133392` and
  `zkvm-receipt-binding-and-verification-boundaries`). Commercial binaries
  (such as `AbsInt aiT`, `StackAnalyzer`, `RapiTime`, and `Bound-T`) and
  external solver pipelines (`EasyCrypt`, `Tamarin`, `Picus`, `EverParse`) were
  not executed locally during this synthesis.
- **Known not to apply — unverified SMT/CAS solver Equivalence to Lean Kernel
  Proofs:** Tools relying on unverified SMT (`Z3`, `cvc5`, `Bitwuzla`), SAT/AIG
  (`ABC`), or CAS (`Singular`) backends (`ct-verif`, `Binsec/Rel`, `HACL*`,
  `Owl`, `Picus`, `Vest`, `CryptoLine` without Coq certificates) do not satisfy
  Anneal's `trusted/` kernel-only soundness boundary unless their outputs are
  exported as checkable proof certificates (such as `LRAT`, Farkas LP duals,
  Gröbner-basis Nullstellensatz cofactors, or explicit `BehaviorCodec` witnesses)
  and re-checked inside the Lean 4 kernel (`theory/`).
- **Known not to apply — source-only `zeroize` or `ct-verif` as a machine-code
  guarantee:** Verifying constant-time (`ct-verif`, `Pitchfork`) or secret
  erasure (`RustCrypto/zeroize`) purely at the source or high-level IR layer
  does not prevent downstream unverified compiler passes (such as LLVM
  `SimplifyCFG` or register spilling) from re-introducing secret-dependent
  branches or un-zeroed stack spills unless paired with a verified backend
  (`CompCert-CT`, `Jasmin`, `Secret-Erasure CompCert`, or Anneal's verified
  `mir-to-x86` compilation pipeline).

## Evidence

- **Anneal `trusted/lean/` primitives and mechanized proofs (acquired
  2026-10-31):** Repository `joshlf/anneal`, branch `reference`, commit
  `df55c524a051d59e7dd35564f282b30d29133392`:
  - `reports/anneal-behavior-codec-and-progress-refinement-2026/REPORT.md` and
    `support/MorphismAdmissibility.lean`,
    `support/BehaviorCodecExpressiveness.lean`,
    `support/AntiDegeneracyAndCallbackFraming.lean` (`Language`, `Partial`,
    `BehaviorCodec`, `PartialBehaviorCodec`, `Compiles`, `Abstracts`,
    `ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`).
  - `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/REPORT.md`
    and `support/ProofGatedCompilationAndTrustPolicy.lean` (`VerificationResult`,
    `TrustPolicy`, `Obligation`, relational cut elimination, positive waiver
    scoping).
  - `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/REPORT.md`
    and `support/StructuralExternalCallAndCanaries.lean`
    (`StepResult.externalCall`, callback re-entrancy protection, and 48-mutant
    TCB audit).
  - `reports/zkvm-receipt-binding-and-verification-boundaries/REPORT.md` (pinned
    source analysis of `risc0/risc0@3bbcd44d6459b9ef6ac0df3846dc9215514934e8`
    and `succinctlabs/sp1@02fa30185ecd658174b211d56128b14867ab8e81`).
  - `reports/zerocopy-byte-domain-and-write-controls-2026-10-14/REPORT.md` and
    `reports/zerocopy-validity-real-pass-certificate-alpha24/REPORT.md` (Google
    `zerocopy` byte validity and layout verification).
- **Primary upstream repositories and specifications (observed 2026-10-31):**
  - Category 6.1: `jasmin-lang/jasmin`, `knothed/CompCert-ct`, `PLSysSec/FaCT`,
    `imdea-software/verifying-constant-time`, `binsec/Rel`,
    `PLSysSec/haybale-pitchfork`, `spectector/spectector`,
    `cacheaudit/cacheaudit`, `crocs-muni/ct-tools`.
  - Category 6.2: `mit-plv/fiat-crypto`, `project-everest/hacl-star`,
    `formosa-crypto/libjade`, `GaloisInc/cryptol`, `GaloisInc/saw-script`,
    `fmlab-iis/cryptoline`, `easycrypt/easycrypt`, `SSProve/ssprove`,
    `secure-foundations/owl`, `tamarin-prover/tamarin-prover`,
    `squirrel-prover/squirrel-prover`, `cryspen/libcrux`, `hacspec/hax`.
  - Category 6.3: `Veridise/Picus`, `0xPARC/Ecne`, `formal-land/garden`,
    `reilabs/lampe`, `trailofbits/circomspect`, `risc0/risc0`,
    `succinctlabs/sp1`, `a16z/jolt`.
  - Category 6.4: `aprove-developers/KoAT2-Releases`, `t-crest/platin`,
    `japaric/cargo-call-stack`.
  - Category 6.5: `project-everest/everparse`, `secure-foundations/vest`,
    `lthms/coq-comparse`, `google/zerocopy`, `AdaCore/RecordFlux`,
    `GaloisInc/daedalus`, `kaitai-io/kaitai_struct`, `zeek/spicy`.
  - Category 6.6: `CTSRD-CHERI/sail-cheri-riscv`,
    `PLSysSec/rlbox_sandboxing_api`, `RustCrypto/utils`.

## Revalidation

To revalidate the structural mappings onto Anneal's four `trusted/lean/`
primitives after any change to Anneal's kernel interface, inspect and re-check
the Lean 4 mechanizations in:

```console
lean reports/anneal-behavior-codec-and-progress-refinement-2026/support/MorphismAdmissibility.lean
lean reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/support/ProofGatedCompilationAndTrustPolicy.lean
lean reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/support/StructuralExternalCallAndCanaries.lean
```

Verify that:
1. `BehaviorCodec` retains `decodeQuery_encodeQuery`, `decodeOut_encodeOut`,
   `encodeOut_of_decodeOut`, and `obs_decodeOut` with `Option`-valued `decodeOut`
   (required for non-malleable parsers in Category 6.5, ZK range checks in
   Category 6.3, randomness couplings in Category 6.2, and post-return secret
   erasure in Category 6.6);
2. `Compiles` and `ProductiveOn` remain paired with `InhabitedPre` (required for
   ZK soundness + completeness in Category 6.3 and non-vacuous CT/parser/WCET
   synthesis in Categories 6.1, 6.4, and 6.5);
3. `EventualBehaviorOf` and `StepResult.externalCall` preserve fuel-independent
   step dilation and pre-call `boundaryInv` enforcement (required for oracle
   queries in Category 6.2, zkVM precompiles in Category 6.3, and FFI/callback
   isolation in Category 6.6); and
4. `VerificationResult` continues to enforce positive per-obligation waiver
   disjunction (`ob.id ∈ waived ∨ ob.prop`).

*Authored by an AI agent acting on joshlf's behalf.*
