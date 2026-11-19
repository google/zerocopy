# Symbolic and Computational Protocol Verifiers for Stateful and Hardware-Coupled Protocols

## Summary

Verifying cryptographic protocols that couple unbounded concurrent sessions with **non-monotonic mutable hardware state**—such as Trusted Platform Module (`TPM 2.0`) Platform Configuration Registers (PCRs) and NV monotonic counters, `DMTF SPDM` multi-mode device attestation handshakes, and `PCIe TDISP/IDE` confidential-device assignment—exposes sharp semantic, decidability, and trust-boundary trade-offs across modern mechanized verifiers:

1. **Linear Multiset Rewriting (`Tamarin`) vs. Monotonic Horn Clauses (`ProVerif`):** `Tamarin` natively encodes destructive state updates using *linear facts* (consumed upon rule firing) alongside *persistent facts* (`!Fact`), supporting unbounded sessions modulo Diffie–Hellman, bilinear pairings, XOR, and associative-commutative multiset equational theories. By contrast, `ProVerif` compiles applied $\pi$-calculus processes into *monotonic* Horn clauses: once a state predicate becomes derivable, overwriting that cell never retracts the old clause, causing spurious **false attacks** on non-monotonic state transitions (directly demonstrated by executable `Probe 2A` on the TPM Envelope PCR protocol). Compiling stateful `SAPIC+` specifications cleanly to `ProVerif` requires proving state-access *purity* (`Sapic/States.hs`: single unlocked initialization + strictly `Lock t; Lookup t` / `Insert t; Unlock t` pairs on bound identifiers) or lifting via `GSVerif` lemma transformations.
2. **Computational Meta-Logic (`Squirrel`) vs. Game-Hopping (`CryptoVerif`):** Symbolic Dolev–Yao proofs idealize primitives and miss weak-randomness, padding-oracle, key-confirmation, or concrete-advantage pitfalls. `CryptoVerif` (`v2.13`) automates probabilistic polynomial-time (PPT) game transformations and produces concrete advantage bounds, but struggles with complex unbounded mutable state machines. `Squirrel` (`ebef0aca...`) embeds the Bana–Comon Computationally Complete Symbolic Attacker (`CCSA`) into an interactive higher-order meta-logic with native mutable cells, mutex locks, and SMT-discharged timestamp induction (`induction t; smt`). Crucially, recent extensions present directly in the pinned `squirrel-prover` tree close two historic limitations: **higher-order logic with errors for concrete cryptography** (CSF 2026, e.g., `yubikey_concrete.sp`) and **post-quantum hybrid KEM combiners and AKE foundations** (CCS 2026, `biKEM`, `C-SigMA`, `BCGNP`).
3. **Eliminating the Model-to-Code Gap (`DY*`):** `Tamarin`, `ProVerif`, `Squirrel`, and `CryptoVerif` verify abstract protocol models that can diverge from deployed C/Rust parsers and state transitions. `DY*` (`REPROSEC/dolev-yao-star` @ `8a0e9992...`) encodes Dolev–Yao trace invariants, secrecy labels, and fine-grained per-session-version corruption (`Corrupt p s v`) directly in `F*` dependent types over an append-only global trace (`GlobalRuntimeLib.fsti`), extracting verified protocol implementations (e.g., Signal, ISO KEM/DH, and descendant `MLS*` for `RFC 9420`) directly to executable OCaml.
4. **Holistic Multi-Mode Modeling Catches Cross-Protocol Attacks (`SPDM`):** Real hardware-attestation stacks (`DMTF/libspdm` @ `3f1253df...`) multiplex distinct authentication modes (`CHALLENGE`, `KEY_EXCHANGE`, `PSK_EXCHANGE`, `PSK_EXCHANGE` without `PSK_FINISH`, mutual auth) over shared connection state (`libspdm_connection_state_t`, 7 states) and session state (`libspdm_session_state_t`, 3 states). Analyzing SPDM 1.2 sub-protocols in isolation missed a critical **cross-protocol PSK reflection/authentication break** (CVSS 9.0) that `Tamarin` automatically discovered only when Cremers, Dax, and Naska (`ePrint 2024/2047`) modeled all modes simultaneously.
5. **Cross-Chip Reset Domains Break Software-Only State Assumptions (`TPM 2.0`, `PCIe TDISP/IDE`):** Discrete security chips occupy independent power/reset domains from the host CPU/hypervisor. Adding an unauthenticated discrete bus reset (`_TPM_Init`) to a sound linear-MSR TPM PCR model immediately yields a concrete 7-step exclusivity violation (`Probe 2A`), and permitting an untrusted VMM to issue a PCIe Function Level Reset (`FLR`) between `TDISP` `LOCK_INTERFACE` (`CONFIG_LOCKED`) and `START_INTERFACE` (`RUN`) violates confidential-VM DMA isolation (`Probe 2B`, 6-step counterexample) unless the device binds a strictly fresh CSPRNG `START_INTERFACE_NONCE` across `LOCK -> REPORT -> START` (and fails even under nonce-checking if reset recycles predictable nonces!).

## Applicability

This report relates ten durable subjects listed in `REPORT.json` across three analytical axes:

- **Verifier Core Implementations (Comparison & Source Analysis):** Direct source inspection of `tamarin-prover/tamarin-prover` @ `03215cd0...`, `squirrel-prover/squirrel-prover` @ `ebef0aca...`, and `REPROSEC/dolev-yao-star` @ `8a0e9992...`, contrasted against documented official releases of `ProVerif` (`2.05`, released 2023-10-18) and `CryptoVerif` (`2.13`).
- **Protocol & Hardware Attestation Targets (Interpretation Through Verifier Semantics):** Direct source inspection of `DMTF/libspdm` @ `3f1253df...` implementing `DSP0274` (SPDM 1.2–1.4), combined with normative state-machine and security requirements from PCI-SIG `PCIe 6.0 IDE / TDISP`, TCG `TPM 2.0 Library Specification`, and IETF `RFC 9420` (`MLS`).
- **Executable Counterexample Probes (`Basis: execution`):** Two standalone Python 3.13.15 state-space verifiers characterizing (a) monotonic Horn-clause saturation vs. linear multiset rewriting with and without discrete `_TPM_Init` bus reset, and (b) coupled SPDM + PCIe TDISP/IDE reset desynchronization with absent, recycled, and strictly fresh `START_INTERFACE_NONCE` binding.

**Scope qualifications:** Claims about `Tamarin`, `Squirrel`, `DY*`, and `libspdm` internals apply to the exact pinned commits in `REPORT.json`. Because `ProVerif 2.05` and `CryptoVerif 2.13` were characterized via official Inria release documentation and peer-reviewed papers (Blanchet 2008, 2016; Cheval et al. 2018, 2022) rather than direct binary execution in this environment, claims about their internal saturation heuristics are grounded in normative/documentation evidence and replicated conceptually via the Horn-clause probe rather than `proverif`/`cryptoverif` CLI timings.

## Findings

### 1. Comparative Architecture Matrix: Symbolic, Computational, and Executable Protocol Verifiers

Basis: source (`tamarin-prover`, `squirrel-prover`, `dolev-yao-star`) + documentation (`ProVerif 2.05`, `CryptoVerif 2.13`, `CAV 2013`, `CCS 2015`, `CSF 2018`, `IEEE S&P 2021`, `EuroS&P 2021`, `USENIX Security 2022`)

| Verifier | Security Model | Native Protocol Calculus / Semantics | Equational Theories / Primitives | Unbounded Sessions & Mutable State | Property Classes | Automation & Termination | Code / Artifact Extraction |
| --- | --- | --- | --- | --- | --- | --- | --- |
| **Tamarin** (`03215cd0...`) | Symbolic (Dolev–Yao) | Labeled Multiset Rewriting (`MSR`) with linear vs. persistent (`!`) facts (`Theory/Model/Fact.hs:133`) + `SAPIC+` frontend | Builtin Maude theories: `DH`, `BP` (bilinear), `XOR`, `Multiset`, `Nat`, plus user subterm-convergent rules (`Term/Maude/Signature.hs:200-205`) | Native destructive state via linear facts (`PCR(x)` consumed on extend/reset); arbitrary loops require inductive `[reuse, use_induction]` lemmas & custom oracles | First-order guarded trace formulas (secrecy, injective/non-injective agreement, accountability) & `diff`-equivalence (observational equivalence) | Semi-automated backward constraint solving; interactive GUI + Python/tactic oracles; undecidable in general | Model-only (though `SAPIC+` exports to ProVerif/DeepSec; no verified C/Rust codegen) |
| **ProVerif** (`v2.05`) | Symbolic (Dolev–Yao) | Applied $\pi$-calculus compiled to **monotonic Horn clauses** | Convergent rewrite theories; limited DH (approximated); weak native XOR/AC support compared to Tamarin | Sound over-approximation for unbounded sessions; mutable cells/tables cause **false attacks** unless restricted via `GSVerif` / `SAPIC+` pure-state compilation | Reachability secrecy, injective/non-injective correspondence assertions, biprocess observational equivalence (`diff[...]`) | Highly automated resolution saturation; fast (seconds) when state is monotonic or pure, may diverge or emit spurious counterexamples on loops | Model-only (historical `FS2PV`/`ProScript` bridges exist separately) |
| **SAPIC+** (in `tamarin-prover` `lib/sapic/`) | Symbolic (multi-backend IR) | Stateful applied $\pi$-calculus (`new`, `in`/`out`, `insert`/`lookup`, `lock`/`unlock`, `event`) | Translates to Tamarin MSR, ProVerif Horn/GSVerif, or DeepSec (bounded sessions) | Static pass `annotatePureStates` (`Sapic/States.hs:192-220`) detects pure locked cells to optimize ProVerif/Tamarin encodings | Unified trace properties & equivalence across backends | Delegates to chosen backend; cross-checking ProVerif speed with Tamarin state precision | Frontend IR only |
| **Squirrel** (`ebef0aca...`) | **Computational** (PPT, CCSA meta-logic + CSF 2026 concrete errors) | Stateful applied $\pi$-calculus with `mutable` registers & `mutex` locks (`toy-counter-smt.sp:33-42`) | Bana–Comon CCSA axioms (`fresh`, `euf`, `int_ctxt`, `cca`, `prf`, `ddh`, `ddh_pq` / KEM combiners in `examples/pq-ccs-2026/`) | Native unbounded replicated sessions (`!_i`) + mutable cells + timestamp induction (`t' < t`) + SMT backend (`smt ~steps:...`) | Computational reachability (`reach`) and indistinguishability (`equiv`/`diff`) — both asymptotic AND concrete error bounds (CSF 2026) | Interactive proof assistant (Coq-like tactics + SMT automation); steeper human proof effort, high soundness | Model-only |
| **CryptoVerif** (`v2.13`) | **Computational** (PPT, sequences of games) | Typed probabilistic $\pi$-calculus with oracle calls and bounded/polynomial replications | Game-based cryptographic assumptions (`IND-CPA`, `INT-CTXT`, `UF-CMA`, `ROM`, `PRF`, `GDH`, `KEM`) | Polynomial sessions; supports tables/arrays, but complex cross-session mutable state machines (like PCR reboots) require manual game structuring | Secrecy, correspondences (authentication), observational indistinguishability with **explicit concrete probability bounds** | Semi-automated game-hopping (automatic proof search guided by interactive proof scripts) | Can extract OCaml/F* reference implementations (limited ecosystem compared to DY*) |
| **DY*** (`8a0e9992...`) | Symbolic (Dolev–Yao in F*) | Functional `F*` code in `Crypto` monad over append-only global trace (`GlobalRuntimeLib.fsti`) | Abstract symbolic `CryptoLib.fsti` (`aead`, `pke`, `sign`, `dh`, `kdf`, `mac`) instantiated with concrete crypto (`HACL*`) at extraction | Unbounded sessions & mutable per-principal state via `SetState p version_vec state_vec` + fine-grained `Corrupt p s v` (`GlobalRuntimeLib.fsti:144-193`) | Global trace invariants (secrecy via `SecrecyLabels`, forward secrecy, post-compromise security, authentication via `Event`) | Semi-automated via `F*` + Z3 SMT verification of dependent types & lemmas | **Direct extraction to executable OCaml** (`Makefile.concrete`, `test.exe`); `ComparseGlue.fst` for verified wire formats |

### 2. Mutable State Semantics: Why Monotonic Horn Clauses Fail Where Linear Multiset Rewriting Succeeds

Basis: source (`tamarin-prover` `Theory/Model/Fact.hs`, `Sapic/States.hs`, `examples/ccs15/TPM_Envelope.spthy`, `examples/features/multiset/counter.spthy`) + execution (`Probe 2A`) + documentation (`CSF 2011`, `CSF 2018`, `USENIX Security 2022`)

#### 2.1 Linear vs. Persistent Facts and Dual-Fact PCR Disciplines in `Tamarin`

In `tamarin-prover/tamarin-prover` (`lib/theory/src/Theory/Model/Fact.hs:133,375-388`), every fact carries a `Multiplicity = Persistent | Linear`. Adversary deduction facts (`KUFact`, `KDFact`) and `!`-prefixed protocol facts (such as long-term keys `!AIK(~aik)`) are `Persistent`: matching them in a rule's left-hand side (LHS) never removes them from the global multiset. Unprefixed protocol facts (such as `PCR(x)` or `Counter(~s, x)`) are `Linear`: firing a rule `[ L ] --[ A ]-> [ R ]` atomically **consumes** `L` and **produces** `R`, enforcing linear exclusivity (mutual exclusion of old and new state values) at every trace timestamp.

Inspecting `tamarin-prover`'s canonical stateful hardware case studies exposes two non-obvious modeling idioms that are mandatory for proof termination:

1. **Monotonic Counter Encoding (`examples/features/multiset/counter.spthy:5-35`):**
   Uses Tamarin's associative-commutative `multiset` builtin (`+`) to represent unary counter increments `[ Counter(~s, x), In(x) ] --[ Counter(~s, x) ]-> [ Counter(~s, x + '1'), Out(senc(x, ~s)) ]`. Without helper invariants, backward constraint solving loops infinitely unfolding `x + '1'`. Proving secrecy of older counter ciphertexts requires chaining three `[reuse, use_induction]` lemmas:
   - `counters_linear_order`: any two counter states `x, y` satisfy `(Ex z. x + z = y) | (Ex z. y + z = x) | y = x`.
   - `counter_start`: every `Counter(s, x) @ i` has a strictly earlier `Start(s) @ j & #j < #i`.
   - `counter_increases`: `#i < #j ==> Ex z. x + z = y`.
2. **Dual-Fact PCR Write Tracking (`examples/ccs15/TPM_Envelope.spthy:49-230`):**
   A TPM PCR supports *non-destructive reads* (`PCR_Quote`, `PCR_Unbind`, `CreateLockedKey` consume `PCR(x)` and immediately re-emit `PCR(x)`) alongside *destructive writes* (`PCR_Extend` consumes `PCR(x)` and emits `PCR(h(x, y))`; `PCR_Reboot` resets `PCR(x)` to `PCR('pcr0')`). Because backward search on `PCR(x)` can loop arbitrarily through `PCR_Quote`/`PCR_Unbind` read rules, `TPM_Envelope.spthy` introduces a companion linear fact **`PCR_Write(x)`** that is touched **only** by write rules (`PCR_Init`, `PCR_Extend`, `Alice1`, `PCR_Reboot`) and links them via an inductive reuse lemma `PCR_Write_charn`:
   ```text
   All x #i. PCR_Read(x) @ i ==> (Ex #j. PCR_Write(x) @ j)
   ```
   This forces Tamarin's backward solver to descend directly along the hash chain `h(h('pcr0', ~n), 'obtain') -> h('pcr0', ~n) -> 'pcr0'` instead of looping on reads. Even with `PCR_Write`, `TPM_Envelope.spthy:226-229` documents a severe heuristic cliff when `PCR_Reboot` is enabled: the hand-guided proof closes in **28 steps (0.5 s)**, whereas the default heuristic expands **7,136 steps (74 s)** because reboot cycles confuse automatic goal ranking.

#### 2.2 Monotonic Horn-Clause False Attacks vs. Linear MSR (`Probe 2A`, `Basis: execution`)

In `ProVerif`'s standard translation of applied $\pi$-calculus to Horn clauses, each clause $H_1 \land \dots \land H_k \to C$ is monotonic: deriving `PCR(h(h(pcr0, n), obtain))` never invalidates `PCR(h(pcr0, n))`. Consequently, the same intermediate state `h(pcr0, n)` can be simultaneously extended with BOTH `'obtain'` (triggering `PCR_Unbind -> K(s)`) and `'deny'` (triggering `PCR_Quote -> Denied(s)`), fabricating an impossible trace.

`Probe 2A` executes both semantics side-by-side on the exact TPM Envelope PCR state machine (`pcr0 -> h(pcr0, n) -> {obtain, deny}`):

| Semantics / Model Variant | Security Goal `NOT (K(s) ∧ Denied(s))` | States / Facts Explored | Interpretation |
| --- | --- | ---: | --- |
| **Monotonic Horn-clause saturation** (ProVerif abstract semantics, no reset) | **Attack derived (`True`)** | 14 Horn facts | **FALSE ATTACK:** Both `PCR(h(h(pcr0,n),obtain))` and `PCR(h(h(pcr0,n),deny))` coexist monotonically from shared `PCR(h(pcr0,n))` |
| **Linear Multiset Rewriting** (Tamarin semantics, no bus reset) | **Verified (`False` — 0 attacks)** | 12 states | **SOUND PROOF:** Extending `h(pcr0,n)` with `'obtain'` consumes the linear PCR fact, making `'deny'` unreachable |
| **Linear Multiset Rewriting + discrete `_TPM_Init` bus reset** | **Attack found (`True`)** | 39 states | **REAL HARDWARE ATTACK (7 steps):** `1. Alice_Extend_Send(n,s) -> 2. PCR_Extend(obtain) -> 3. PCR_Unbind->K(s) -> 4. Discrete_TPM_Bus_Reset(_TPM_Init) -> 5. Adv_Replay_Extend(pcr0,n) -> 6. PCR_Extend(deny) -> 7. PCR_Quote->Denied(s)` |

#### 2.3 How `SAPIC+` and `GSVerif` Bridge Mutable State to `ProVerif`

Inspecting `tamarin-prover/tamarin-prover` (`lib/sapic/src/Sapic/States.hs:127-220`) shows the exact static check (`annotatePureStates`) that enables sound ProVerif translation for restricted mutable state:
- `existsAttackerUnpure` checks whether any state identifier `t` containing free (attacker-controlled/unbound) variables is accessed outside strict `Lock t; Lookup t` or `Insert t; Unlock t` pairs.
- `isPureState` verifies that a bound state cell has **at most one unlocked `Insert`** (initialization) and that every subsequent access obeys strict lock-guarded read-modify-write pairs (`Lock t; Lookup t` followed by `Insert t; Unlock t`).
- When a state is pure, `SAPIC+` can emit tight cell-channel invariants and `GSVerif`-style monotonicity/injectivity lemmas (Cheval, Cortier, Turuani, CSF 2018) that let `ProVerif` eliminate false attacks; when state indices depend on attacker inputs or undergo asynchronous non-locked resets (like discrete TPM bus resets or PCIe FLR), `ProVerif`'s Horn-clause abstraction degrades and `Tamarin`'s linear MSR remains the stronger engine.

### 3. Computational Protocol Verification: `Squirrel` Meta-Logic vs. `CryptoVerif` Game-Hopping

Basis: source (`squirrel-prover/squirrel-prover`) + documentation (`IEEE S&P 2021`, `CSF 2022`, `CSF 2025`, `CSF 2026`, `CCS 2026`, `CryptoVerif 2.13`, `TDSC 2008`)

Symbolic Dolev–Yao verifiers cannot detect computational flaws such as non-IND-CCA encryption malleability, weak KDF separation, length-extension collisions, or multi-user advantage degradation. Two mature verifiers address the computational model through fundamentally different proof architectures:

1. **`Squirrel` (CCSA Meta-Logic + Mutable State + Concrete & PQ Extensions):**
   - **Foundations:** Built on the Bana–Comon Computationally Complete Symbolic Attacker (`CCSA`, CCS 2014; Baelde et al., IEEE S&P 2021, `10.1109/SP40001.2021.00118`). Rather than restricting the adversary to fixed Dolev–Yao rewrite rules, `Squirrel` treats the adversary as an arbitrary PPT Turing machine and restricts it *negatively* via computationally sound axioms (`fresh`, `euf`, `int_ctxt`, `cca`, `prf`, `ddh`) over first-order terms indexed by protocol execution timestamps (`@t`).
   - **Native Stateful Verification + SMT (`examples/smt-csf-2025/toy-counter-smt.sp:19-56`):** `Squirrel` directly supports `mutable cpt : nat = one` and `mutex l : 0` with `lock l; ...; cpt := Succ(cpt); unlock l`. Monotonicity across unbounded concurrent sessions (`!_i A`) is proved in two lines via timestamp induction and SMT:
     ```text
     lemma counterIncrease (t,t':timestamp): t' < t => cpt@t' ~< cpt@t.
     Proof. induction t. smt ~steps:30000. Qed.
     lemma reach (tau:timestamp): input@tau <> h(cpt@tau,k).
     Proof. intro Eq; euf Eq. use counterIncrease; smt ~steps:30000. Qed.
     ```
   - **Concrete Security Bounds (`examples/concrete-csf-2026/README.md`):** Historically, a key trade-off favored `CryptoVerif` over `Squirrel` whenever concrete advantage bounds (rather than asymptotic negligible probability) were required. At pinned revision `ebef0aca...`, `squirrel-prover` incorporates **Higher-Order Logic with Errors for Concrete Cryptography** (Fontaine, Koutsos, Scerri, Vignon, CSF 2026), proving concrete bounds on birthday collisions, Merkle-tree collision resistance, and stateful YubiKey authentication (`yubikey_concrete.sp`).
   - **Post-Quantum Hybrid KEM Foundations (`examples/pq-ccs-2026/README.md`):** At the same revision, `squirrel-prover` includes mechanized computational proofs for post-quantum hybrid KEM combiners (`biKEM_from_KEM_dualPRF_cca.sp`, `biKEM_from_KEM_xormac_cca.sp`) and post-quantum hybrid AKE protocols (`CSigMA-multi-session-KEM`, `kemKE_BCGNP`, Baelde et al., CCS 2026).
2. **`CryptoVerif` (`v2.13`, Blanchet, TDSC 2008):**
   - Models protocols in a typed probabilistic $\pi$-calculus and transforms the initial protocol game step-by-step into an idealized game where the target secrecy/correspondence property holds syntactically, tracking the exact sum of adversary advantages ($\sum_i \text{Adv}^{\text{prim}_i}(t, q_i)$) automatically.
   - Excels at high-automation concrete proofs of modern key exchanges (TLS 1.3, WireGuard, Noise, Signal X3DH, HPKE), where game hops map cleanly onto standard `PRF`/`GDH`/`ROM`/`AEAD` library definitions, whereas deeply stateful hardware devices with arbitrary reboot/counter induction remain more natural in `Squirrel`'s timestamp-indexed logic or `Tamarin`.

### 4. Executable Verified Protocol Code: `DY*` Dependent-Type Trace Invariants and `RFC 9420` (MLS)

Basis: source (`REPROSEC/dolev-yao-star`) + documentation (`IEEE EuroS&P 2021`, `RFC 9420`)

Abstract verifier models leave a notorious **model-to-code gap**: wire-format framing bugs, missing length checks, unverified state deserialization, or omitted transcript fields in C/Rust/OCaml implementations can completely invalidate a verified Tamarin or ProVerif model.

`DY*` (`REPROSEC/dolev-yao-star` @ `8a0e9992...`, Bhargavan et al., IEEE EuroS&P 2021, `10.1109/EuroSP51992.2021.00042`) eliminates this gap inside `F*`:

- **Append-Only Global Trace Semantics (`GlobalRuntimeLib.fsti:16-193`):** Every protocol action executes in the `Crypto` effect, appending typed entries to a global trace indexed by `timestamp = trace_len t0`:
  - `RandGen r label usage` (`gen l u`), attaching a secrecy `label` (lattice of principals/sessions/versions) and cryptographic `usage` (AEAD key, signing key, KDF secret, nonce) at generation time.
  - `Event p (ev, tl)` (`trigger_event`), recording authentication milestones.
  - `Message p1 p2 t` (`send` / `receive_i`), publishing messages to the Dolev–Yao attacker (`AttackerAPI.fsti`).
  - `SetState principal version_vec state_vec` (`set_state` / `get_last_state_before`), separating public structural metadata (`version_vec`, tracking session epochs) from secret session contents (`state_vec`).
  - `Corrupt p s v` (`compromise p s v`), allowing **fine-grained session-version compromise** to prove Forward Secrecy (FS) and Post-Compromise Security (PCS) without collapsing the entire principal's history.
- **Modular Type-Driven Proof & Extraction:** `LabeledCryptoAPI.fsti` assigns dependent refinement types (`msg i l`, `secret i l u`) proving by typechecking that no honest code ever leaks a secret labeled `l` to a principal outside `l` unless `can_flow i l public` (i.e., an authorized version was corrupted). Protocol implementations (e.g., Signal double ratchet in `signal/`, ISO KEM/DH) compile directly from `F*` to executable OCaml (`Makefile.concrete`) and pair with verified parser/serializer combinators (`ComparseGlue.fst` / EverParse).
- **Group Messaging & Continuous Key Agreement (`RFC 9420` MLS):** `RFC 9420` (Messaging Layer Security, published July 2023) relies on `TreeKEM`—a continuously mutating binary ratchet tree where any member's `Commit` updates a direct path of HPKE/KEM secrets and advances the group epoch to restore PCS after compromise. Verifying MLS's unbounded group-size and arbitrary-epoch state transitions motivated both `DY*`-descendant `MLS*` F* proofs (executable tree-invariant verification) and specialized `Tamarin`/`ProVerif` models that bound tree depth or abstract epoch history via inductive invariants.

### 5. Hardware-Coupled Attestation & Session State Machines: SPDM, PCIe TDISP/IDE, and TPM 2.0

Basis: source (`DMTF/libspdm`, `tamarin-prover`) + normative (`DSP0274`, `PCIe 6.0 IDE/TDISP`, `TPM 2.0 Library Spec`) + execution (`Probe 2A`, `Probe 2B`) + documentation (`USENIX Security 2023`, `ePrint 2024/2047`, `HotSec 2008`, `ASIACCS 2020`)

#### 5.1 DMTF SPDM (`DSP0274` v1.2–1.4) and `DMTF/libspdm` (`3f1253df...`)

Direct inspection of `DMTF/libspdm` establishes a **two-tier coupled state machine**:

1. **Connection State (`include/library/spdm_common_lib.h:202-226`, `libspdm_connection_state_t`):**
   `NOT_STARTED` $\xrightarrow{\text{VERSION}}$ `AFTER_VERSION` $\xrightarrow{\text{CAPABILITIES}}$ `AFTER_CAPABILITIES` $\xrightarrow{\text{ALGORITHMS}}$ `NEGOTIATED` $\xrightarrow{\text{DIGESTS}}$ `AFTER_DIGESTS` $\xrightarrow{\text{CERTIFICATE}}$ `AFTER_CERTIFICATE` $\xrightarrow{\text{CHALLENGE}}$ `AUTHENTICATED`.
   Additionally, `libspdm_response_state_t` (`NORMAL`, `BUSY`, `NOT_READY`, `NEED_RESYNC`) handles asynchronous hardware readiness (`RESPOND_IF_READY`) and firmware-update resynchronization.
2. **Session State (`include/library/spdm_secured_message_lib.h:25-38`, `libspdm_session_state_t`):**
   `NOT_STARTED` $\xrightarrow{\text{KEY\_EXCHANGE / PSK\_EXCHANGE}}$ `HANDSHAKING` $\xrightarrow{\text{FINISH / PSK\_FINISH}}$ `ESTABLISHED` $\xrightarrow{\text{END\_SESSION}}$ `NOT_STARTED`.
   Crucially, in `libspdm_req_psk_exchange.c:570-598`, when `PSK_CAP_WITHOUT_CONTEXT` (no `PSK_FINISH`) is negotiated, `libspdm` advances directly from `HANDSHAKING` to `ESTABLISHED` inside `PSK_EXCHANGE_RSP`, immediately deriving application data keys from `TH2`.
3. **Transcript Hash Construction (`library/spdm_common_lib/libspdm_com_crypto_service_session.c:10-82,433-515`):**
   - For public-key `KEY_EXCHANGE`: `TH1 = Hash(VCA || [message_d if multi_key] || Hash(cert_chain) || KEY_EXCHANGE || KEY_EXCHANGE_RSP)`.
   - For `PSK_EXCHANGE` (`session_info->use_psk == true`): `cert_chain_buffer = NULL`, so `TH1 = Hash(VCA || PSK_EXCHANGE || PSK_EXCHANGE_RSP)`.
4. **Holistic Formal Verification Finding (Cremers, Dax, Naska, USENIX Security 2023 & `ePrint 2024/2047`):**
   - Modeling SPDM 1.2's individual modes in isolation initially established mode-local properties, but combining all key-exchange modes (`KEY_EXCHANGE`, `PSK_EXCHANGE`, mutual authentication, certificate/raw-public-key slots) into a single holistic `Tamarin` model uncovered a **cross-protocol reflection/authentication attack breaking PSK mode authentication**, verified on `libspdm` and registered by DMTF as a **critical CVE (CVSS 9.0)**.
   - The attack exploited symmetric role/transcript overlap when an endpoint could play both requester and responder roles or reuse PSK material across sessions without unambiguous role/transcript separation; the formally verified fix (now adopted in the standard and `libspdm`) enforces strict cross-mode transcript and key-schedule separation, proving absence of all cross-protocol attacks across the unified SPDM 1.2 Tamarin model.
   - **SPDM 1.4 PQC Extension Surface:** `spdm.h:482-524,1398-1482` adds `ML-KEM-{512,768,1024}`, `ML-DSA-{44,65,87}`, all 12 `SLH-DSA` sets, and 32-bit `chunk_seq_no` framing—expanding the state space with KEM-based key exchange (no longer Diffie–Hellman contributory symmetry!) and multi-chunk reassembly error states (`EARLY_ERROR_DETECTED`), which require fresh symbolic/computational verification beyond SPDM 1.2 DH models.

#### 5.2 PCIe TDISP & IDE Coupled Device-Assignment State Machine

Confidential computing device assignment (e.g., Intel TDX Connect, AMD SEV-TIO) layers **PCIe TDISP** (TEE Device Interface Security Protocol) over an **SPDM-over-DOE** secure session and **PCIe IDE** (Integrity and Data Encryption, AES-GCM link/selective-stream protection with `K_SET_GO`/`K_SET_STOP` key-slot rotation):

- **TDI Lifecycle (`CONFIG_UNLOCKED -> CONFIG_LOCKED -> RUN -> ERROR`):**
  1. `CONFIG_UNLOCKED`: Default post-reset state; untrusted Host VMM configures PCIe BARs, MSI-X, and routing registers; private/T-bit DMA disabled.
  2. `LOCK_INTERFACE_REQUEST` / `LOCK_INTERFACE_RESPONSE`: Host TEE Security Manager (TSM) locks the device's configuration registers via the Device Security Manager (DSM), transitioning the TDI to `CONFIG_LOCKED` and obtaining a fresh 32-byte **`START_INTERFACE_NONCE`**.
  3. `GET_DEVICE_INTERFACE_REPORT`: TSM fetches and verifies the signed MMIO/MSI-X/BAR/IDE configuration report over SPDM while locked.
  4. `START_INTERFACE_REQUEST(START_INTERFACE_NONCE)`: TSM echoes the exact lock nonce to transition the TDI into `RUN`, enabling trusted PCIe T-bit DMA/MMIO inside the Confidential VM (TVM) bound to the active IDE stream.
  5. `ERROR`: Any IDE MAC failure, sequence-number overflow, unauthorized config write, or protocol/nonce mismatch transitions the TDI to `ERROR`, tearing down keys and blocking T-bit traffic until explicit host reclamation/reset.

**Cross-Chip Reset Desynchronization Counterexamples (`Probe 2B`, `Basis: execution`):**
Modeling an untrusted Host VMM capable of issuing a **PCIe Function Level Reset (`FLR`) / Hot Reset** on the device asynchronously while the TSM holds verified attestation state yields three crisp state-space outcomes:

| TDISP Nonce Enforcement Policy | TVM Isolation Violated? | States Explored | Exact Shortest Counterexample Trace |
| --- | --- | ---: | --- |
| **1. No `START_INTERFACE_NONCE` check** | **YES (6 steps)** | 36 | `1. DSM_Lock(benign, n=1) -> 2. TSM_VerifyReport(benign, n=1) -> 3. VMM_PCIe_FLR_Reset -> 4. VMM_Config(malicious_mmio) -> 5. DSM_Lock(malicious_mmio, n=2) -> 6. DSM_StartInterface(malicious_mmio, dev_n=2, req_n=1)` |
| **2. Checked nonce, but predictable/reused across reset** (e.g., reset resets PRNG/counter to `1`) | **YES (6 steps)** | 29 | `1. DSM_Lock(benign, n=1) -> 2. TSM_VerifyReport(benign, n=1) -> 3. VMM_PCIe_FLR_Reset -> 4. VMM_Config(malicious_mmio) -> 5. DSM_Lock(malicious_mmio, n=1) -> 6. DSM_StartInterface(malicious_mmio, dev_n=1, req_n=1)` |
| **3. Strictly fresh CSPRNG `START_INTERFACE_NONCE`** (survives FLR via non-volatile/TRNG entropy) | **NO (0 violations)** | 56 | Isolation holds across all reachable interleavings; FLR forces a new `n' != n`, rejecting stale `START_INTERFACE` |

This proves two coupled hardware-verification requirements: (a) TDISP's `START_INTERFACE_NONCE` binding is load-bearing against VMM-induced FLR TOCTOU attacks, and (b) the device's nonce generator **must not reset to a deterministic seed on PCIe FLR/Hot-Reset**—a subtle cross-layer entropy requirement invisible to pure Dolev–Yao models that assume `Fr(~nonce)` is magically fresh across hardware resets!

#### 5.3 Discrete TPM 2.0 State, Locality, Bus-Reset, and Cuckoo Hazards

Modeling discrete `TPM 2.0` (`SPI`/`LPC` attached chips) in `Tamarin` or `Squirrel` must account for four physical-to-protocol boundaries:
1. **Unauthenticated Bus Resets (`_TPM_Init` / `TPM2_Startup(CLEAR)`):** Because discrete TPM reset pins can be toggled independently of the host CPU (or via warm-reset/interposer attacks), `Probe 2A` demonstrates that any protocol locking secrets to PCR values derived from replayed nonces without binding a TPM-generated monotonic counter or hardware-enforced CPU reset coupling (such as DRTM Locality 4 `SENTER`/`SKINIT`) is broken in 7 steps.
2. **Locality Gating (Localities 0–4):** TPM 2.0 restricts dynamic PCR resets (`PCR 17–22`) to Locality 3/4 (CPU microcode/DRTM) so OS-level software (Locality 0) cannot forge a reset-and-replay chain. Formal models MUST tag every `PCR_Extend` / `PCR_Reset` transition with an explicit locality parameter and restrict adversary rules to Locality 0–2 unless the threat model includes physical bus interposition.
3. **Cleartext SPI/LPC Bus Sniffing & Salted/Encrypted Sessions:** Default unsealing flows (e.g., BitLocker VMK unseal) transmit secrets in cleartext over the SPI/LPC traces unless wrapped in a **salted, parameter-encrypted `TPM2_StartAuthSession`** (HMAC/policy session with rolling `nonceCaller`/`nonceTPM` anti-replay and `TPMA_SESSION_ENCRYPT`/`DECRYPT`, or TCG *TPM Communication over SPDM Secure Session*).
4. **Cuckoo Attacks (Parno et al., HotSec 2008):** Even with an uncompromised remote TPM and sound PCR proofs (such as Whitefield et al.'s `ASIACCS 2020` `Tamarin` ECC-DAA models in `examples/asiaccs20-eccDAA/QUOTE/TPM_DAA_JoinQuotePCR_with_fix_BSN.spthy`), malware on a compromised host can proxy TPM quotes to an attacker-owned physical TPM unless the verifier binds physical platform presence (e.g., physically bound EK/SPDM device identity + authenticated bus channel).

### 6. Verifier Selection Decision Matrix for Systems & Hardware Protocol Engineers

Basis: derived from Sections 1–5 (`Tamarin`, `ProVerif`, `SAPIC+`, `Squirrel`, `CryptoVerif`, `DY*`)

| Protocol / Assurance Scenario | Primary Verifier Choice | Secondary / Cross-Check | Key Modeling & Soundness Watchouts |
| --- | --- | --- | --- |
| **Stateful hardware attestation (SPDM 1.2/1.4, PCIe TDISP/IDE, TPM 2.0 PCRs & resets)** | **Tamarin** (native linear MSR + `SAPIC+`) | `Squirrel` (if computational/concrete bounds required) | Model ALL protocol modes jointly (`ePrint 2024/2047`); add explicit bus-reset/FLR transitions; use dual `PCR_Write` facts + `[reuse, use_induction]` lemmas + custom oracles to prevent heuristic blowup |
| **Fast prototyping / large stateless or pure-state wire protocols** | **ProVerif** (via `SAPIC+`) | `Tamarin` (to resolve any state-related false attack) | Check `Sapic/States.hs` purity; verify no attacker-indexed mutable cells silently trigger monotonic Horn over-approximation |
| **Computational / post-quantum hybrid KEM AKE & concrete stateful bounds** | **Squirrel** (CCSA + CSF 2026 concrete + CCS 2026 PQ) or **CryptoVerif** | `Tamarin` (for broad multi-mode symbolic state exploration) | Use `CryptoVerif` for automated concrete game-hopping on bounded-state AKEs; use `Squirrel` for unbounded mutable counters/registers with SMT timestamp induction |
| **Production executable protocol implementation (zero model-to-code gap, FS/PCS)** | **DY*** (`F*` + `Comparse`/EverParse + `HACL*`/`Libcrux`) | `Tamarin` / `CryptoVerif` (for independent attack finding) | Model explicit wire-format parsers (`ComparseGlue.fst`) and per-session-version `Corrupt p s v`; remember DY* proves *symbolic* (not computational) security unless paired with computational primitive reductions |

## Boundaries

- **Direct CLI execution of `tamarin-prover`, `proverif`, `squirrel`, `cryptoverif`, and `F*`/`DY*` binaries:** *not examined* in this environment; all tool-internal findings are backed by direct source inspection of the pinned repositories (`tamarin-prover`, `squirrel-prover`, `dolev-yao-star`, `libspdm`), official Inria release pages (`ProVerif 2.05`, `CryptoVerif 2.13`), peer-reviewed publications, and standalone Python state-space probes (`Probe 2A`, `Probe 2B`).
- **Complete SPDM 1.4 (`ML-KEM` + `ML-DSA` + `SLH-DSA` + 32-bit chunking) formal verification:** *unknown / not examined*. While `DMTF/libspdm` @ `3f1253df...` already implements SPDM 1.4 PQC wire structures, the cited holistic Tamarin proof (`ePrint 2024/2047`) covers SPDM 1.2 (classical DHE/signatures/PSK). Whether KEM-based non-contributory key exchange and SPDM 1.4 multi-bank certificate slots introduce new cross-protocol or downgrade interactions requires extending the Tamarin/Squirrel models to DSP0274 v1.4.
- **Computational soundness of `Tamarin`, `ProVerif`, and `DY*` symbolic models:** *known not to apply* automatically. Symbolic Dolev–Yao proofs do not rule out concrete cryptographic breaks (e.g., weak PRF instantiation, padding oracles, side-channel leakage during decryption/decapsulation, or insufficient nonce entropy after hardware reset); bridging requires `Squirrel`/`CryptoVerif` or explicit computational soundness theorems.
- **Full PCIe 6.0 IDE hardware packet-level MAC/key-refresh (`K_SET_GO`/`K_SET_STOP`) TLP reordering:** *not examined* at the PCIe Transaction Layer Packet (TLP) / Data Link Layer level; `Probe 2B` abstracts the TDISP control plane (`CONFIG_UNLOCKED -> CONFIG_LOCKED -> RUN -> ERROR`) and FLR nonce-binding invariant rather than concurrent in-flight TLP key-slot rollover races.
- **DeepSec / bounded-session equivalence verifiers:** *not examined* beyond noting `SAPIC+` backend translation support.

## Evidence

### Primary Repositories and Source Coordinates (Observed 2026-11-19)

1. **`tamarin-prover/tamarin-prover`** @ `03215cd03e7c844ca2be116b45aef9737db495fd`:
   - `lib/theory/src/Theory/Model/Fact.hs:133,375-388,552-553` (`Multiplicity = Persistent | Linear`; `KUFact`/`KDFact` persistent vs. linear protocol facts).
   - `lib/term/src/Term/Maude/Signature.hs:36-51,200-213` (builtin Maude equational theories `dhMaudeSig`, `bpMaudeSig`, `msetMaudeSig`, `natMaudeSig`, `xorMaudeSig`).
   - `lib/sapic/src/Sapic/States.hs:27-220` (`hasBoundUnboundStates`, `existsAttackerUnpure`, `isPureState`, `annotatePureStates`).
   - `examples/features/multiset/counter.spthy:1-37` (associative-commutative multiset counter + `[reuse, use_induction]` ordering lemmas).
   - `examples/ccs15/TPM_Envelope.spthy:49-250` (`PCR`/`PCR_Write` dual-fact discipline, `PCR_Reboot`, `diff(~s, ~f)` observational equivalence, lines 226–229 heuristic 28-step/0.5 s manual vs. 7,136-step/74 s automatic comparison).
   - `examples/asiaccs20-eccDAA/QUOTE/TPM_DAA_JoinQuotePCR_with_fix_BSN.spthy` (TPM 2.0 ECC-DAA PCR quote model).
2. **`squirrel-prover/squirrel-prover`** @ `ebef0aca4f668b3b6c8e8e2796e59a16e7e50c9c`:
   - `examples/smt-csf-2025/toy-counter-smt.sp:1-56` (`mutable cpt`, `mutex l`, timestamp induction `induction t. smt ~steps:30000`, `euf Eq`).
   - `examples/concrete-csf-2026/README.md:1-32` & `examples/concrete-csf-2026/yubikey_concrete.sp` (Fontaine, Koutsos, Scerri, Vignon, CSF 2026 concrete higher-order logic with errors; stateful YubiKey CSF 2022 reference).
   - `examples/pq-ccs-2026/README.md:1-27` & `examples/pq-ccs-2026/{bikem,protocols}/*` (Baelde, Dallon, Delaune, Jacomme, Koutsos, CCS 2026 post-quantum hybrid KEM combiners & AKE protocols).
3. **`REPROSEC/dolev-yao-star`** @ `8a0e999267c436d9d57db0f1aa289476049b08a2`:
   - `README.md:1-94` (Signal, ISO KEM/DH, NSL case studies, `F*` -> OCaml `test.exe` extraction).
   - `GlobalRuntimeLib.fsti:16-193` (`was_rand_generated_at`, `did_event_occur_at`, `was_message_sent_at`, `state_was_set_at`, `was_corrupted_at`, `set_state p version_vec state_vec`, `has_last_update`, `compromise p s v`).
   - `LabeledCryptoAPI.fsti`, `SecrecyLabels.fsti`, `SecurityLemmas.fsti`, `ComparseGlue.fst` (labeled secrecy invariants and wire-format parsing glue).
4. **`DMTF/libspdm`** @ `3f1253df61ef1af917f1f18ce40db065e93ff82c`:
   - `include/library/spdm_common_lib.h:202-240` (`libspdm_connection_state_t` 7 states, `libspdm_response_state_t`).
   - `include/library/spdm_secured_message_lib.h:25-38` (`libspdm_session_state_t`: `NOT_STARTED`, `HANDSHAKING`, `ESTABLISHED`).
   - `library/spdm_common_lib/libspdm_com_crypto_service_session.c:10-82,433-515` (`libspdm_calculate_th_for_exchange`, `libspdm_calculate_th1_hash`, `libspdm_calculate_th2_hash` for `KEY_EXCHANGE` vs. `PSK_EXCHANGE`).
   - `library/spdm_requester_lib/libspdm_req_psk_exchange.c:529-598` (single-RTT `HANDSHAKING -> ESTABLISHED` transition when `PSK_FINISH` is omitted).
   - `include/industry_standard/spdm.h:116-120,482-524,1398-1482` (SPDM 1.4 PQC algorithm definitions and 32-bit `chunk_seq_no`).

### Official Release Documentation, Standards & Peer-Reviewed Papers

- **ProVerif 2.05** (released 2023-10-18, observed on `https://bblanche.gitlabpages.inria.fr/proverif/news.html`); Blanchet, *Modeling and Verifying Security Protocols with the Applied Pi Calculus and ProVerif*, Foundations and Trends in Privacy and Security (2016).
- **CryptoVerif 2.13** (observed on `https://bblanche.gitlabpages.inria.fr/CryptoVerif/`); Blanchet, *A Computationally Sound Mechanized Prover for Security Protocols*, IEEE TDSC (2008).
- Meier, Schmidt, Cremers, Basin, *The TAMARIN Prover for the Symbolic Analysis of Security Protocols*, CAV 2013; Basin, Dreier, Sasse, *Automated Symbolic Proofs of Observational Equivalence*, ACM CCS 2015.
- Cheval, Cortier, Turuani, *A Little More Conversation, a Little Less Action, a Lot More Satisfaction: Global States in ProVerif (GSVerif)*, IEEE CSF 2018; Cheval, Jacomme, Kremer, Künnemann, *SAPIC+: Protocol Verifiers of the World, Unite!*, USENIX Security 2022.
- Baelde, Delaune, Jacomme, Koutsos, Moreau, *An Interactive Prover for Protocol Verification in the Computational Model*, IEEE S&P 2021 (`10.1109/SP40001.2021.00118`); Baelde, Delaune, Koutsos, Moreau, *Cracking the Stateful Nut*, IEEE CSF 2022; Fontaine, Koutsos, Scerri, Vignon, CSF 2026; Baelde, Dallon, Delaune, Jacomme, Koutsos, CCS 2026.
- Bhargavan, Bichhawat, Do, Hosseyni, Küsters, Schmitz, Würtele, *DY\*: A Modular Symbolic Verification Framework for Executable Cryptographic Protocol Code*, IEEE EuroS&P 2021 (`10.1109/EuroSP51992.2021.00042`).
- Cremers, Dax, Naska, *Formal Analysis of SPDM: Security Protocol and Data Model version 1.2*, USENIX Security 2023; Cremers, Dax, Naska, *Breaking and Provably Restoring Authentication: A Formal Analysis of SPDM 1.2 including Cross-Protocol Attacks*, `ePrint 2024/2047` (CVSS 9.0 critical PSK cross-protocol CVE + Tamarin proof of fix).
- Parno, *Bootstrapping Trust in a "Trusted" Platform*, USENIX HotSec 2008; Whitefield, Chen, Sasse, Schneider, Treharne, Wesemeyer, *Formal Analysis and Implementation of a TPM 2.0-based Direct Anonymous Attestation Scheme*, ASIACCS 2020; Barnes et al., IETF `RFC 9420` (`10.17487/RFC9420`, July 2023).

### Executable Micro-Probes (Observed 2026-11-19, Python 3.13.15)

1. **`Probe 2A` (Horn-Clause Saturation vs. Linear MSR on TPM Envelope PCR):** Confirmed monotonic Horn closure derives a false attack (`K(s) ∧ Denied(s)`, 14 facts) with no reset; linear MSR proves safety (`0` attacks across 12 reachable states) without bus reset; adding an unauthenticated discrete `_TPM_Init` reset yields a concrete 7-step attack trace across 39 states (`Alice_Extend_Send -> PCR_Extend(obtain) -> PCR_Unbind->K(s) -> Discrete_TPM_Bus_Reset -> Adv_Replay_Extend(pcr0,n) -> PCR_Extend(deny) -> PCR_Quote->Denied(s)`).
2. **`Probe 2B` (TDISP/IDE Cross-Chip FLR Reset & `START_INTERFACE_NONCE` Exploration):** Confirmed a 6-step TVM isolation violation when `START_INTERFACE_NONCE` is omitted (36 states) AND a 6-step violation when reset recycles a predictable nonce (`mod 1`, 29 states), versus `0` violations across 56 states when every `LOCK_INTERFACE` emits a strictly fresh CSPRNG nonce surviving PCIe FLR.

## Revalidation

1. **Re-run Executable State-Semantics & TDISP Counterexample Probes (~0.1 s):** Any future reader can revalidate the Horn-vs-Linear-MSR separation and TDISP FLR nonce-freshness counterexamples directly with standard-library Python 3.10+:
   ```python
   # Minimal TDISP FLR + START_INTERFACE_NONCE revalidation check:
   # Verify that removing nonce binding OR recycling nonces after FLR produces a 6-step
   # CONFIG_LOCKED(benign) -> VerifyReport -> FLR -> Config(malicious) -> Lock -> RUN trace,
   # whereas strictly monotonic/fresh nonces reject stale START_INTERFACE requests.
   from collections import deque
   def check_tdisp(enforce_nonce, reuse_nonce):
       init = ("UNLOCKED", "benign", 0, 0, "INIT", None, None, False)
       seen, q = {init: []}, deque([init])
       while q:
           ds, dcfg, dn, locks, ts, tcfg, tn, bad = st = q.popleft()
           if bad: return True, seen[st]
           nxt = []
           if ds == "UNLOCKED":
               for c in ("benign", "malicious"):
                   if c != dcfg: nxt.append((f"Cfg({c})", (ds, c, dn, locks, ts, tcfg, tn, bad)))
               if locks < 3:
                   nn = 1 if reuse_nonce else locks + 1
                   nxt.append((f"Lock({dcfg},{nn})", ("LOCKED", dcfg, nn, locks+1, ts, tcfg, tn, bad)))
           if ds == "LOCKED" and dcfg == "benign" and ts == "INIT":
               nxt.append((f"Verify({dn})", (ds, dcfg, dn, locks, "VERIFIED", dcfg, dn, bad)))
           if ds in ("LOCKED", "RUN"):
               nxt.append(("FLR", ("UNLOCKED", "benign", 0, locks, ts, tcfg, tn, bad)))
           if ts == "VERIFIED" and ds == "LOCKED" and (not enforce_nonce or dn == tn):
               nxt.append((f"Start({dcfg},{dn},{tn})", ("RUN", dcfg, dn, locks, "RUN", tcfg, tn, dcfg != tcfg)))
           for a, s2 in nxt:
               if s2 not in seen: seen[s2] = seen[st] + [a]; q.append(s2)
       return False, None
   assert check_tdisp(False, False)[0] is True
   assert check_tdisp(True, True)[0] is True
   assert check_tdisp(True, False)[0] is False
   print("TDISP revalidation passed")
   ```
2. **Re-check Upstream Verifier Capabilities (~5 s):**
   - `tamarin-prover/tamarin-prover`: inspect `lib/term/src/Term/Maude/Signature.hs` for newly added builtin equational theories (e.g., KEM or AC extensions) and `lib/sapic/src/Sapic/States.hs` for updates to pure-state ProVerif compilation.
   - `squirrel-prover/squirrel-prover`: inspect `examples/` for newly merged concrete-bound (`concrete-*`), SMT (`smt-*`), or post-quantum (`pq-*`) libraries and check whether `ProVerif`/`CryptoVerif` have released newer versions past `2.05` / `2.13`.
   - `DMTF/libspdm`: diff `include/library/spdm_common_lib.h`, `include/library/spdm_secured_message_lib.h`, and `library/spdm_common_lib/libspdm_com_crypto_service_session.c` (`TH1`/`TH2` construction) whenever migrating to a new SPDM 1.4/1.5 draft or adding hybrid KEM modes.
3. **Full Re-investigation Needed:** Certifying SPDM 1.4 post-quantum modes (`ML-KEM` + `ML-DSA`/`SLH-DSA` + 32-bit chunking) or PCIe 6.0 IDE TLP key-rollover (`K_SET_GO`/`K_SET_STOP`) against active bus-interposer adversaries requires authoring and running full machine-checked `Tamarin` or `Squirrel` theories against the updated wire specifications; the minimal state-space probe above verifies only the TDISP FLR nonce-binding invariant.
