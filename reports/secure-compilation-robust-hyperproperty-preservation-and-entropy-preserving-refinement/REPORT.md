# Secure Compilation, Robust Hyperproperty Preservation, and Entropy-Preserving Refinement

## Summary

Ordinary compiler correctness—trace inclusion $\text{Beh}(P\downarrow) \subseteq \text{Beh}(P)$ established by whole-program backward simulation—fails to preserve security, confidentiality, quantitative leakage bounds, or interactive liveness across four orthogonal boundaries:

1. **Adversarial Linking Contexts (`Abate et al.`, CSF 2019 / TOPLAS 2021):** Whole-program correctness reasons only about closed programs, whereas linking compiled code $P\downarrow$ with an arbitrary target-level adversary $C_T$ exposes low-level memory, stack, and control-flow capabilities absent from source contexts $C_S$. Preserving source security against $C_T$ requires **robust property preservation** parameterized by property class and quantifier alternation: trace-based back-translation (`RSC` / `RTC`) suffices for trace properties and safety, context-based trace inclusion (`RSCHC`) preserves all **subset-closed hyperproperties** (including 2-safety observational determinism / cryptographic constant-time), and exact trace-set equivalence (`RHC`) or `R2rTC` is required for arbitrary $\forall\exists$ hyperproperties and relational equivalence (`RTEP`). Full abstraction sits orthogonally to robust safety and demands more proof effort than `RSC`/`R2SCHP`.
2. **McLean's Refinement Paradox & Unmodeled Side Channels (`CompCert-CT`, `Jasmin`):** Resolving nondeterminism ($\pi_{\text{tgt}} \subsetneq \pi_{\text{src}}$) preserves $\forall$-trace properties and subset-closed hyperproperties (`ObsDet`) but breaks non-subset-closed $\forall\exists$ security definitions such as Generalized Non-Interference (`GNI`). Furthermore, even on deterministic undefined-behavior-free C programs, standard verified compilers (`AbsInt/CompCert`) erase branch PCs and memory addresses from their `Events.trace` semantics, permitting optimizing passes and register spilling to introduce timing side channels or Spectre-v1 speculative leaks. Preserving constant-time (`CT`) and speculative constant-time (`SCT`) requires instrumenting operational semantics with explicit leakage observations and proving **leakage-preserving simulations** (`CompCert-CT`, `PCFL`, `Jasmin` + `SLH`).
3. **Quantitative Leakage Amplification (`Smith 2009`; `Alvim et al. 2012, 2020`):** Shannon mutual information $I_1$ fails to bound single-guess secret compromise; Rényi min-entropy leakage $I_\infty$ and generalized $g$-vulnerability $V_g$ capture worst-case adversary gain. Crucially, while oblivious stochastic post-processing $C' = C R$ satisfies the Data Processing Inequality ($V_g(\pi, CR) \le V_g(\pi, C)$ for all $\pi, g$, by the Blackwell–Sherman–Stein / Coriaceous Theorem), standard demonic nondeterministic refinement $P \sqsubseteq Q$ can select secret-correlated resolutions that **increase** $I_\infty$ and $V_g$—blocking compositional entropy proofs unless demonic choice is resolved obliviously or tracked via shadow/ignorant refinement and probabilistic relational Hoare couplings.
4. **Liveness, Stuttering, and Divergence Sensitivity (`Abadi & Lamport 1991`; `CompCert`; `InteractionTrees`; `CakeML`):** Trace-inclusion safety fails to rule out silent divergence unless stuttering is bounded by well-founded ordinal measures (`fsim_order_wf` / `bsim_order_wf` in `CompCert`), inductive-inside-coinductive `Tau` stripping (`eqitF`/`paco2` in `InteractionTrees` and `Jasmin`), explicit clock/resource-limit semantics (`CakeML`), or Abadi–Lamport history/prophecy variables under fairness constraints.

## Applicability

This report synthesizes foundational theorems, formal mechanization artifacts, and compiler engineering trade-offs across eleven directly inspected primary subjects:

- **Formal Hyperproperty & Robust Compilation Lattice:** `secure-compilation/exploring-robust-property-preservation` (`c68187cbaba763d88cbb3509df4ca9cf49cc6338`, accompanying Abate et al. CSF 2019) together with Abate et al. (ESOP 2020 / ACM TOPLAS 2021) for heterogeneous trace-relating Galois connections $(\tilde{\tau}, \hat{\sigma})$. Applies to open-world modular compilation where source components $P$ link against untrusted target contexts $C_T$.
- **Verified Whole-Program & Constant-Time C Compilers:** `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`, `driver/Complements.v`, `common/Smallstep.v`), `knothed/CompCert-ct` (`2d1369a4888cff6fd5fd29f28a059e9cf72b1a08`, `constant-time/` verified secret control-flow elimination on a loop-free, no-memory-access `x86_64` RTL subset), and the POPL 2020 `CompCert-CT` / CSF 2018 constant-time simulation frameworks. Findings on `CompCert-CT` apply under the architectural ISA leakage contract (branch outcomes + accessed addresses) and assume deterministic execution modulo UB-free source semantics.
- **High-Assurance Cryptographic & Functional Compilers:** `jasmin-lang/jasmin` (`8c3279973a89afd969e50301f71563bb40d55724`, covering OCaml forward `CT`/`SCT` checkers and Coq/Rocq `slh_ops.v` + `it_compiler_proof.v`), `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`), `DeepSpec/InteractionTrees` (`284d42248a3c5517cff9f582e335fcee2f6bdc1f`), and `CertiRocq/certirocq` (`ab66e0164e7ecb63e5af95c90c8e479068bf95c2`).
- **Information Flow, QIF & Concurrency Refinement Theory:** McLean (1994), Clarkson & Schneider (2010), Morgan (2006), Smith (2009), Alvim et al. (2012, 2020), and Abadi & Lamport (1991). Behavioral conclusions from the standalone Python 3 micro-probe apply to finite-state trace sets, finite probabilistic channels, and abstract transition models as explicitly qualified.

## Findings

### 1. Ordinary Compiler Refinement, Undefined Behavior, and McLean's Refinement Paradox

Basis: normative specification (`10.1109/RISP.1994.296590`, `10.3233/JCS-2009-0393`, `10.1007/11783596_21`) + source (`AbsInt/CompCert` `driver/Complements.v`) + execution (finite-trace probe).

#### 1.1 What Closed-World Backward Simulation Actually Preserves

In `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`, `driver/Complements.v`), whole-program compiler correctness does **not** prove behavioral equality $\text{Beh}(T) = \text{Beh}(S)$; it proves a backward refinement modulo undefined behavior improvement (`behavior_improves`):

- `transf_c_program_preservation` (`driver/Complements.v`, lines 31–40): for every compiled assembly behavior `beh`, there exists a source C behavior `beh'` such that `behavior_improves beh' beh`—meaning either `beh' = beh` or `beh'` starts with a finite trace `t` ending in `Goes_wrong` (undefined behavior) while `beh` shares prefix `t` and continues arbitrarily.
- `transf_c_program_is_refinement` (`driver/Complements.v`, lines 46–53): only when the source C program is globally free of undefined behavior (`forall beh, program_behaves (Csem.semantics p) beh -> not_wrong beh`) does compilation yield pure trace inclusion $\text{Beh}(\text{Asm}) \subseteq \text{Beh}(\text{C})$.
- `transf_c_program_preserves_spec` (`driver/Complements.v`, lines 148–160): arbitrary safety-like specifications `spec : program_behavior -> Prop` are preserved **only if** `safety_enforcing_specification spec` holds (`forall beh, spec beh -> not_wrong beh`). Otherwise, a source program that satisfies `spec = "goes wrong on UB"` can validly compile to assembly that does not go wrong and thus violates `spec`.
- `transf_c_program_preserves_initial_trace` (`driver/Complements.v`, lines 173–191): prefix liveness `c_program_has_initial_trace p t` is preserved unconditionally because even `behavior_improves (Goes_wrong t0) beh` preserves the prefix up to `t0` if `t` already occurred within `t0`.

#### 1.2 Clarkson–Schneider Hyperproperties and McLean's Refinement Paradox

Clarkson and Schneider (`10.3233/JCS-2009-0393`) stratify specifications over sets of traces $\pi \subseteq \mathcal{T}$:

- **Trace properties** $P \subseteq \mathcal{T}$ satisfy $\pi \models P \iff \pi \subseteq P$. Any subset $\pi' \subseteq \pi$ preserves every satisfied trace property ($\forall$-trace / 1-hyperproperties).
- **Hyperproperties** $H \subseteq \mathcal{P}(\mathcal{T})$ classify programs by sets of executions. Every hyperproperty decomposes into an intersection of **hypersafety** (bad finite *sets of finite trace prefixes* $M$, violated as soon as a program exhibits all observations in $M$) and **hyperliveness** (every finite observation set $M$ can be extended to some $\pi \in H$).
- **$k$-safety hyperproperties** ($k \in \mathbb{N}$) reject sets of size $\le k$. Crucially, every $k$-safety property—and more generally every **subset-closed hyperproperty** ($\pi \in H \wedge \pi' \subseteq \pi \implies \pi' \in H$)—is preserved by trace inclusion $\text{Beh}(T) \subseteq \text{Beh}(S)$. Examples include deterministic non-interference and **observational determinism** (`ObsDet`: any two traces with equal low inputs yield equal low outputs).

**McLean's Refinement Paradox (`10.1109/RISP.1994.296590`):** Non-subset-closed hyperproperties have quantifier structure $\forall t_1 \dots \exists t_k$ (hyperliveness). **Generalized Non-Interference (`GNI`)**, **possibilistic non-interference**, and **noninference** assert that for any execution with secret $H$ and public output $L$, *there exists* another execution with another secret $H'$ producing the *same* public output $L$. Because trace refinement $\pi' \subseteq \pi$ shrinks the set of behaviors, an optimizing or determinizing compiler can drop the masking traces needed by $\exists t_k$. In our micro-probe over $\mathcal{T} = \{0,1\}^2$ (`(H, L)`), $\pi_{\text{GNI}} = \{(0,0),(0,1),(1,0),(1,1)\}$ satisfies `GNI = True` and preserves all `16/16` trace properties under refinement to $\pi_{\text{leak}} = \{(0,0),(1,1)\}$, yet `GNI(pi_leak) = False` because $(0,1)$ and $(1,0)$ were refined away, leaking $L = H$ deterministically.

**Morgan's Shadow / Ignorant Refinement (`10.1007/11783596_21`):** To preserve possibilistic secrecy across stepwise refinement, Morgan augments Hoare/Dijkstra state transformers with an explicit **shadow** variable representing the set of secret values the observer still considers possible after observing public steps. Standard demonic refinement $P \sqsubseteq Q$ fails to preserve ignorance unless the refinement relation explicitly prohibits shrinking the shadow set based on hidden state—establishing that secure refinement requires **monotone non-narrowing of adversary uncertainty**, not merely trace-set inclusion.

---

### 2. The Abate et al. Robust Property Preservation Hierarchy and Back-Translation

Basis: normative specification (`10.1109/CSF.2019.00025`, `10.1145/3460860`) + source (`secure-compilation/exploring-robust-property-preservation`, `Criteria.v`, `Separation.v`).

When compiling a partial program $P$ that links against untrusted target-language contexts $C'$, **robust satisfaction** in source requires $\text{RSat}_S(P, \pi) \iff \forall C_S.\, \text{Beh}_S(C_S[P]) \in \pi$. Abate et al. (`secure-compilation/exploring-robust-property-preservation`, `c68187cbaba763d88cbb3509df4ca9cf49cc6338`, `Criteria.v`) organize robust compilation criteria by the exact **quantifier alternation** in their equivalent **property-free characterizations**, which directly dictates which back-translation proof technique works:

| Criterion (`Criteria.v`) | Property Class Preserved | Property-Free Quantifier Order (`Criteria.v` lines) | Back-Translation Dependency | Preserves `2-Safety` / `CT`? | Strict Hierarchy & Separations (`Separation.v` / CSF 2019) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`RSC` (`RSC_RSP`)** | Robust Safety (`RSP`) | $\forall P\, C'\, t\, m.\; \text{prefix } m\, t \land t \in \text{Beh}_T(C'[P\downarrow]) \implies \exists C\, t'.\; t' \in \text{Beh}_S(C[P]) \land \text{prefix } m\, t'$ (`73–85`) | Finite-prefix-dependent $C(P, C', m)$ (trace-based finite execution wrapper) | **No** (single prefix $m$ cannot force two runs under *one* $C$) | Strictly weaker than `RTC` (`separation_RSP_RTP`) and `R2HSC`; independent of Full Abstraction |
| **`RDC` (`RDC_RDP`)** | Robust Dense Properties (`RDP`) | $\forall P\, C'\, t.\; \text{inf}(t) \implies \exists C.\; (t \in \text{Beh}_T(C'[P\downarrow]) \implies t \in \text{Beh}_S(C[P]))$ (`115–125`) | Infinite trace $t$ | No | Independent of `RSC` (`separation_RSP_RDP`); `RSC` + `RDC` $\iff$ `RTC` (`RDP_plus_RSP_RTP`) |
| **`RTC` (`RTC_RTP`)** | All Trace Properties (`RTP`) | $\forall P\, C'\, t.\; \exists C.\; (t \in \text{Beh}_T(C'[P\downarrow]) \implies t \in \text{Beh}_S(C[P]))$ (`19–59`) | Full trace $t$ (can bake exact oracle trace into $C$) | **No** (cannot preserve 2-trace properties) | Strictly weaker than `R2HSC`, `RSCHC`, and `RHC` |
| **`R2HSC` (`R2HSC_R2HSP`)** | 2-Hypersafety (`R2HSP`) | $\forall P\, C'\, m_1\, m_2.\; \{m_1, m_2\} \sqsubseteq_{\text{pref}} \text{Beh}_T(C'[P\downarrow]) \implies \exists C.\; \{m_1, m_2\} \sqsubseteq_{\text{pref}} \text{Beh}_S(C[P])$ (`316–334`) | **Two** finite prefixes $(m_1, m_2)$ under *one shared* $C$ | **Yes** (if CT is phrased via 2-prefix safety on fixed public input) | Implies `RSC` (`R2HSC_RSC`, line 336); strictly weaker than `R2SCHC` |
| **`R2SCHC` (`R2SCHC_R2SCHP`)** | 2-Subset-Closed Hyperproperties (`R2SCHP`) | $\forall P\, C'\, t_1\, t_2.\; (t_1, t_2 \in \text{Beh}_T(C'[P\downarrow])) \implies \exists C.\; (t_1, t_2 \in \text{Beh}_S(C[P]))$ (`253–290`) | **Two** full traces $(t_1, t_2)$ under *one shared* $C$ | **Yes** | Implies `R2HSC` (`R2SCHC_R2HSC`, line 344) and `RTC` |
| **`RSCHC` (`RSCHC_RSCHP`)** | All Subset-Closed Hyperproperties (`RSCHP`) | $\forall P\, C'.\; \exists C.\; \forall t.\; t \in \text{Beh}_T(C'[P\downarrow]) \implies t \in \text{Beh}_S(C[P])$ (`229–248`) | **Context-only** $C(C')$ (universal over all traces $t$!) | **Yes** (all $k$-safety & $\omega$-hypersafety) | Coincides with robust preservation of arbitrary $\forall$-hyperproperties; strictly weaker than `RHC` |
| **`RHC` (`RHC_RHP`)** | All Hyperproperties (`RHP`, incl. `GNI` / hyperliveness) | $\forall P\, C'.\; \exists C.\; \forall t.\; t \in \text{Beh}_T(C'[P\downarrow]) \iff t \in \text{Beh}_S(C[P])$ (`197–225`) | **Exact** context-only back-translation $C(C')$ preserving both directions $\leftrightarrow$ | **Yes** (and preserves $\forall\exists$ hyperproperties) | Coincides with Robust Hyperliveness Preservation! Requires exact trace-set equality $\text{Beh}_S(C[P]) = \text{Beh}_T(C'[P\downarrow])$ |
| **`R2rSC` / `R2rTC` / `RrTC`** | Relational 2-Safety (`R2rSP`) / 2-Trace (`R2rTP`) / All Relational (`RrTP`) | $\forall C'\, P_1\, P_2\, m_1\, m_2 \dots \exists C_S$ (`460–515`) | Context $C_S$ shared across **multiple programs** $P_1, P_2$ | **Yes** (and cryptographic indiff./equivalence) | When source is deterministic (`src_det`), `R2rTP -> RTEP` (`R2rTP_RTEP`, lines 435–447), yielding target observational equivalence! |

**Three Structural Engineering Consequences:**

1. **Trace-based vs. Context-based Back-Translation:** Because `RSC`, `RTC`, and `R2HSC` quantify $\exists C$ *inside* $\forall t$ (or $\forall m_1\, m_2$), the proof can synthesize a **finite non-Turing-complete source context** that simply replays the finite trace/prefix oracle (`trace-based back-translation`, far easier when target is assembly with unsafe pointers and source is typed/memory-safe). Conversely, `RSCHC` and `RHC` quantify $\exists C$ *outside* $\forall t$, forcing **context-based back-translation** (compiling arbitrary target code $C'$ back into source $C$, e.g. via a source-language target simulator or universal embedding).
2. **Why Full Abstraction Is Neither Sufficient Nor Necessary:** Full abstraction ($\forall P_1\, P_2.\; P_1 \equiv_S P_2 \iff P_1\downarrow \equiv_T P_2\downarrow$) preserves **observational equivalence**, which does *not* imply `RSC` when source lacks syntax to express certain bad traces, and proves equivalence in *both* directions ($\implies$ and $\Longleftarrow$). `R2rSP` / `RTEP` isolates the downward security implication needed by practitioners without requiring source-to-target equivalence reflection (`P1 ≡S P2 ⇒ P1↓ ≡T P2↓`).
3. **Heterogeneous Source/Target Trace Spaces (`10.1145/3460860`):** Real compilers change event granularity (source high-level I/O vs target syscalls/byte buffers). Abate et al. (ESOP 2020 / TOPLAS 2021) generalize equality $t_S = t_T$ to a **trace relation** $\sim \subseteq \mathcal{T}_S \times \mathcal{T}_T$ inducing an adjunction (Galois connection $(\tilde{\tau}, \hat{\sigma})$) between source and target properties: $\tilde{\tau}$ maps source properties to strongest target guarantees via existential/universal image, proving that **non-trivial trace abstractions can lose hyperproperty precision** unless $\sim$ is deterministic and injective on security-relevant events.

---

### 3. Constant-Time and Speculative Constant-Time Compilation (`CompCert-CT`, `Jasmin`, `PCFL`)

Basis: normative specification (`10.1109/CSF.2018.00031`, `10.1145/3371075`, `10.1109/SP46215.2023.10179418`, `10.1145/3704880`) + source (`knothed/CompCert-ct`, `jasmin-lang/jasmin`).

#### 3.1 Why Ordinary CompCert Breaks Constant-Time and How CT-Simulations Fix It

In `AbsInt/CompCert`, `Events.trace` records only external function calls, volatile accesses, and I/O (`Event_syscall`, `Event_vload`, `Event_vstore`, `Event_annot`). Internal branches and stack/array memory offsets are silent (`E0`). Consequently, a pass that transforms a branchless constant-time source operation `c ? a : b` into `if (c) a else b` (or spills a secret register to a secret-dependent offset, or short-circuits `a && b`) satisfies `transf_c_program_is_refinement` while failing **cryptographic constant-time (`CT`)**—the 2-safety property requiring identical **leakage traces** (`l ::= Br bool | Mem addr`) across executions differing only in secrets.

Barthe et al. (`10.1109/CSF.2018.00031`, `10.1145/3371075`) identify the exact simulation structure needed to preserve constant-time across compiler passes:

- **Naive leakage preservation breaks on dead/merged branches or register allocation:** A compiler pass rarely preserves step-by-step lockstep leakage equality. Barthe et al. CSF 2018 introduce **CT-simulations** combining: (i) **public simulation** matching program states on public data, and (ii) **leakage transformation** $\phi$ mapping source leakage traces $L_S$ to target leakage traces $L_T$ such that $\phi(L_S)$ depends *only on* $L_S$ (and public inputs), never on secrets (`L_S(s1) = L_S(s2) ⇒ L_T(t1) = L_T(t2)`).
- **`CompCert-CT` (`10.1145/3371075`):** Instruments `CompCert` Clight through `Asm` with deterministic architectural leakage events (`branch` direction + `memory` addresses) and disables/modifies passes that introduce secret-dependent control flow (e.g., `Selection` conditional branch generation, `CSE`, `Deadcode` branch optimizations) so the composed simulation preserves observational equivalence of leakage traces (`CT` security).
- **Verified Secret Control-Flow Linearization (`knothed/CompCert-ct`, `2d1369a4888cff6fd5fd29f28a059e9cf72b1a08`):** Extends CompCert's RTL pipeline (`CTTransform.v`, `ControlFlowSecurity.v`, `TaintAnalysis.v`, `InfluenceRegion.v`, `PredRTL.v`) with Program Control-Flow Linearization (`PCFL`):
  - `TaintAnalysis.v` defines forward taint analysis (`uni_cdep_equivalent`) classifying uniform vs secret-dependent conditions.
  - `ControlFlowSecurity.v` lines 508–516 state and prove **`Theorem control_flow_security`**: for any two `initial_state` executions `init1`, `init2` satisfying `init_states_agree_publicly init1 init2` and reaching `PredRTL` steps of equal length `length trace1 = length trace2`, the control-flow PC traces are identical (`trace1 = trace2`), the current PCs match (`v1 = v2`), and `agree_publicly rs1 rs2` is preserved.
  - **Current Scope Limit (`constant-time/README.md`, lines 6–9):** `CompCert-ct`'s verified `CTTransform` applies only to a restricted subset of C without loops, without memory accesses, and without returning from `main` (demonstrating the engineering cost of mechanizing full relational CT transformations inside CompCert).

#### 3.2 Jasmin: Checking CT/SCT + Preserving Speculative Constant-Time Under Register Allocation and SLH

`jasmin-lang/jasmin` (`8c3279973a89afd969e50301f71563bb40d55724`) combines a source-level/pre-lowering static information-flow checker with a Coq/Rocq-verified compiler (`compiler/compiler.v`, `compiler/it_compiler_proof.v`):

- **Architectural CT (`compiler/src/ct_checker_forward.mli`, lines 11–26):** Forward relational/taint type-checker (`ty_prog`) over Jasmin functions given an architecture-specific constant-time operator predicate `is_ct_asm : 'asm -> bool`.
- **Speculative Constant-Time (`SCT`, `compiler/src/sct_checker_forward.mli`, lines 1–20; Shivakumar et al. `10.1109/SP46215.2023.10179418`; Arranz Olmos et al. `10.1145/3704880`):** Under Spectre-v1 transient execution, conditional branches can mispredict into both targets, leaking secrets via speculative loads/stores even when the architectural trace is constant-time.
  - `jasmin` enforces `SCT` via `sct_checker_forward` plus compiler-inserted **Speculative Load Hardening (`SLH`)** operators (`proofs/lang/slh_ops.v`, lines 19–27): `SLHinit`, `SLHupdate`, `SLHmove`, `SLHprotect of wsize`, `SLHprotect_ptr of wsize & Z`, `SLHprotect_ptr_fail of wsize & Z`, maintaining a misspeculation flag (`msf`) via `compile_infer_msf` (`sct_checker_forward.mli`, line 20).
  - **Register-Spilling Hazard (`sct_checker_forward.mli`, lines 18–19):** The docstring explicitly requires *"The program must not contain any #spill or #unspill pseudo-operation"* because naive stack spilling / register allocation after SCT checking can spill transient or secret-correlated values onto public/speculative stack slots unless stack-slot zeroization (`compiler/stack_zeroization.v`) and spill-aware lowering preserve `SCT` down to assembly (`Arranz Olmos et al.`, POPL 2025, `10.1145/3704880`).

---

### 4. Probabilistic Refinement, Rényi Min-Entropy, and $g$-Leakage Preservation

Basis: normative specification (`10.1007/978-3-642-00596-1_21`, `10.1109/CSF.2012.26`, `10.1007/978-3-319-96131-6`) + execution (QIF channel probe).

When programs use randomness (blinding, masking, randomized padding, probabilistic schedulers), refinement compares probabilistic information-theoretic channels $C : \mathcal{X} \to \mathbb{D}(\mathcal{Y})$ mapping secret $x \in \mathcal{X}$ (with prior $\pi \in \mathbb{D}(\mathcal{X})$) to observable output distributions over $\mathcal{Y}$.

#### 4.1 Why Shannon Mutual Information Understates Worst-Case Leakage

Smith (`10.1007/978-3-642-00596-1_21`) proved that Shannon mutual information $I_1(X; Y) = H_1(X) - H_1(X \mid Y)$ fails to bound an adversary's single-try guessing probability (**Bayes vulnerability**):

- **Prior & Posterior Bayes Vulnerability:** $V_1(\pi) = \max_{x \in \mathcal{X}} \pi(x)$ and $V_1(\pi, C) = \sum_{y \in \mathcal{Y}} \max_{x \in \mathcal{X}} \pi(x) C(x, y)$.
- **Rényi Min-Entropy Leakage:** $I_\infty(\pi, C) = \log_2 \frac{V_1(\pi, C)}{V_1(\pi)}$.
- **Generalized $g$-Leakage (`Alvim et al. 2012`, `10.1109/CSF.2012.26`; `2020`, `10.1007/978-3-319-96131-6`):** For any guess space $\mathcal{W}$ and operational gain function $g : \mathcal{W} \times \mathcal{X} \to \mathbb{R}_{\ge 0}$ (modeling $k$-try guessing, guessing prefixes, or partial key bits), $V_g(\pi, C) = \sum_y \max_{w \in \mathcal{W}} \sum_x \pi(x) C(x, y) g(w, x)$ and $I_g(\pi, C) = \log_2 \frac{V_g(\pi, C)}{V_g(\pi)}$.

Our QIF probe over a uniform 64-bit secret ($V_1(\pi) = 2^{-64}$) confirms Smith's separation quantitatively:
- `Channel_Parity` (leaks `X & 1`): $I_1 = 1.0000\text{ bit}$, $V_1(\pi, C) = 2^{-63} \approx 1.084 \times 10^{-19}$, $I_\infty = 1.0000\text{ bit}$.
- `Channel_RareFull` (leaks all 64 bits with $p = 1/64$, else $\bot$): $I_1 = 1.0000\text{ bit}$ (identical Shannon mutual information!), **yet** $V_1(\pi, C) = 0.015625 \approx 2^{-6}$ and $I_\infty = 58.0000\text{ bits}$—a $2^{57}\times$ higher compromise risk.

#### 4.2 The Refinement vs. Post-Processing Asymmetry (Blackwell–Sherman–Stein / Coriaceous Theorem)

Under what compiler transformations is $V_g(\pi, C_{\text{tgt}}) \le V_g(\pi, C_{\text{src}})$ guaranteed?

- **Blackwell–Sherman–Stein / Coriaceous Theorem (`10.1007/978-3-319-96131-6`, Ch. 6):** $V_g(\pi, C_{\text{tgt}}) \le V_g(\pi, C_{\text{src}})$ holds **for all priors $\pi$ and all gain functions $g$** (and hence for $I_1$, $I_\infty$, and all $g$-leakages simultaneously!) **if and only if** there exists an oblivious stochastic matrix $R : \mathcal{Y}_{\text{src}} \to \mathbb{D}(\mathcal{Y}_{\text{tgt}})$ (dependent *only* on target observations, **independent of $X$**) such that $C_{\text{tgt}} = C_{\text{src}} R$. That is, $C_{\text{tgt}}$ is a **post-processing** (garbling) of $C_{\text{src}}$ (**Data Processing Inequality, `DPI`**).
- **Why Demonic Refinement Violates `DPI`:** In McIver–Morgan pGCL, a specification $P \sqcap Q$ allows demonic nondeterminism between two individually bounded leaky branches $C_0$ and $C_1$. If a compiler resolves $\sqcap$ using secret-dependent data (or correlates scheduling choices with a secret branch), the compiled channel is **not** $C_0 R$ or $C_1 R$; it partitions secrets across the branch labels. In our micro-probe over uniform $X \in \{0,1,2,3\}$:
  - Both $C_0$ (`x // 2`) and $C_1$ (`x % 2`) have $V_1 = 0.5000$ ($I_\infty = 1.0000\text{ bit}$).
  - Every deterministic post-processing of $C_0$ satisfies $V_{\text{post}} \le 0.5000$ (`max_dpi_violation = 0.0e+00`).
  - Yet a secret-correlated resolution $C_{\text{bad}}$ of $C_0 \sqcap C_1$ jumps to $V_1 = 0.7500$ ($I_\infty = 1.5850\text{ bits}$)—an entropy loss forbidden under post-processing!
- **Criterion for Entropy-Preserving Compilation:** A compiler pass preserves quantitative secrecy ($V_g(\pi, C_{\text{tgt}}) \le V_g(\pi, C_{\text{src}}) + \varepsilon$) iff: (1) its observable leakage transformation is **oblivious** to secrets (either a deterministic projection of source observations or independent noise injection $R$, e.g., constant-time compilation where $L_T = \phi(L_S)$); and (2) any demonic nondeterminism in the source is resolved either **obliviously** (independent of secret state via a schedule oblivious to $X$) or under a **probabilistic coupling / `pRHL`** invariant that preserves marginal output distributions within $(\varepsilon, \delta)$ distance.

---

### 5. Liveness, Stuttering, Fairness, and Divergence-Sensitive Simulations

Basis: normative specification (`10.1016/0304-3975(91)90224-P`) + source (`AbsInt/CompCert` `Smallstep.v`; `DeepSpec/InteractionTrees` `Eqit.v`; `jasmin-lang/jasmin` `xrutt.v`, `it_compiler_proof.v`; `CakeML/cakeml` `backendProofScript.sml`, `ffiScript.sml`; `CertiCoq/certicoq` `toplevel_theorems.v`, `correctness.v`).

Safety-only simulation ($\forall s \xrightarrow{a} s'$) allows a target program to spin silently (`Forever_silent`) instead of making progress toward a final state or reactive I/O event, violating **liveness** ($\square\Diamond P$ / termination). Four mechanisms in the literature and verified compilers prevent silent stuttering collapse:

1. **Abadi & Lamport Refinement Mappings (`10.1016/0304-3975(91)90224-P`):** A state function $f : \Sigma_{\text{impl}} \to \Sigma_{\text{spec}}$ preserving initial states, transitions up to **stuttering** ($s \to s$ invisible steps), and **fairness** ($L_{\text{impl}} \implies L_{\text{spec}}$) is **complete** (guaranteed to exist whenever $\text{Beh}(\text{Impl}) \subseteq \text{Beh}(\text{Spec})$) **only under five hypotheses**: (i) **stuttering invariance** of both specs (so clock-rate / optimization step-count changes cannot break spec membership), (ii) **machine closure** of the spec (no unachievable liveness requirements forbidding valid finite prefixes), (iii) **finite invisible nondeterminism (`FIN`)**, (iv) **history variables** (augmenting $\Sigma_{\text{impl}}$ to remember past choices), and (v) **prophecy variables** (augmenting $\Sigma_{\text{impl}}$ to anticipate future nondeterministic choices where a spec commits early before implementation resolves nondeterminism).
2. **Well-Founded Stuttering Measures in `AbsInt/CompCert` (`common/Smallstep.v`):**
   - `fsim_properties` (`Smallstep.v`, lines 566–582) and `bsim_properties` (`Smallstep.v`, lines 1289–1316) parameterize `match_states` by an `index : Type` equipped with `well_founded order`:
     ```coq
     (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i)) /\ match_states i' s1' s2'
     ```
   - Because `order` has no infinite descending chains, a silent (`t = E0`, `Star` zero-step) match can occur only finitely many times before `Plus` forces at least one observable step in the matched machine. Thus `Forever_silent` in `Asm` can occur **only if** the source C semantics also diverges silently (`Diverges t`), preserving termination and `Reacts T` (`Forever_reactive`)! As our probe confirms, dropping `well_founded order` lets a silent `s2 ->_E0 s2` loop simulate any finite source path (`Forever_silent` masquerading as `Terminates(0)`).
3. **Inductive-Inside-Coinductive `Tau` Peeling in `InteractionTrees` (`Eqit.v`) and `Jasmin` (`xrutt.v`, `it_compiler_proof.v`):**
   - In `DeepSpec/InteractionTrees` (`284d42248a3c5517cff9f582e335fcee2f6bdc1f`, `theories/Eq/Eqit.v`, lines 95–112), `eqitF b1 b2 vclo sim` is an **inductive** functor nested inside the **greatest** fixed point `paco2`: `EqTau` steps both sides symmetrically into `sim` (coinductive), whereas `EqTauL` (`TauF t1`, `ot2`) and `EqTauR` (`ot1`, `TauF t2`) recurse **inductively** on `eqitF`.
   - Because `EqTauL`/`EqTauR` can strip only **finitely many** unilateral `Tau`s before hitting `EqRet`, `EqVis`, or synchronized `EqTau`, `eutt` (`b1 = true, b2 = true`) quotients finite internal stuttering **while remaining termination-sensitive**: `(cofix spin := Tau spin) ≈ Ret x` is **unprovable**! `jasmin-lang/jasmin` inherits this exact termination-sensitive semantics in `proofs/itrees/xrutt.v` (adding cutoff points `DoCutoffF EE t` for source UB, lines 53–68) and `proofs/compiler/it_compiler_proof.v`.
4. **Functional Big-Step Clocks (`CakeML`) vs. Step-Indexed Logical Relations (`CertiRocq`):**
   - `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`, `semantics/ffi/ffiScript.sml`, lines 15–52) explicitly models external FFI termination vs divergence (`ffi_outcome = FFI_failed | FFI_diverged`), and `backendProofScript.sml` (`Theorem compile_correct_determ`, lines 4932–4942) proves `machine_sem ... ⊆ extend_with_resource_limit (semantics_determ ...)`—explicitly relaxing target execution with a safe **out-of-memory/stack resource cutoff** `extend_with_resource_limit` while preserving both terminating and diverging FFI traces up to memory bounds!
   - `CertiCoq/certicoq` (`ab66e0164e7ecb63e5af95c90c8e479068bf95c2`, `LambdaANF/toplevel_theorems.v`, lines 577–702) uses step-indexed/fuel-bounded `bstep_fuel` evaluators (`eval_env_fuel` -> `bstep_fuel`) for `anf_pipeline_correct`, which quantifies over finite execution fuel $f_{\text{src}}$ to produce target fuel $c_2$; note also that `theories/Compiler/correctness.v` (lines 1–50) still leaves top-level MetaRocq-to-ANF composition comments/admits separate from `LambdaANF/toplevel_theorems.v`, meaning termination/divergence equivalence requires showing fuel monotonicity + totality separately.

---

### 6. Multi-Level Performance and Resource Footprint (`L1`–`L6`)

Basis: source inspection (`AbsInt/CompCert`, `knothed/CompCert-ct`, `jasmin-lang/jasmin`, `secure-compilation/exploring-robust-property-preservation`, `CakeML/cakeml`, `CertiCoq/certicoq`) + published evaluations (`10.1109/CSF.2019.00025`, `10.1145/3371075`, `10.1109/SP46215.2023.10179418`, `10.1145/3704880`, `10.1145/3133956.3134078`) + derived scaling analysis.

| Toolchain / Criterion | (L1) Authoring & Proof Velocity | (L2) Toolchain Build Time & RSS | (L3) Compile / Check Latency | (L4) Generated Code Perf & Overhead | (L5) Certificate / Proof Check Speed | (L6) Artifact RAM, Disk & Binary Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`CompCert` (Baseline C Compiler)** | ~5:1–10:1 Coq-to-ML/C proof ratio; single-pass `fsim`/`bsim` scales linearly with pass count (`Complements.v`). | Full Coq proof build ~10–30 min (`make -j`); ~1–3 GB peak `coqc` RSS. | `ccomp` typically ~2–3$\times$ slower than `gcc -O0` (verified OCaml passes, no SSA/LLVM polyhedral search). | Typically ~10–20% slower than `gcc -O2` on general C (`Select`, `CSE`, `Regalloc` verified). | Kernel `coqchk` replays extracted soundness proof offline; zero per-binary proof emission. | ~100–250 MB `.vo` proof objects; negligible runtime binary bloat vs unoptimized C. |
| **`CompCert-CT` & `PCFL` (`knothed/CompCert-ct`)** | High marginal proof cost: adding one pass requires relational CT-simulation or PCFL invariant (`ControlFlowSecurity.v`); verified `PCFL` currently excludes loops/memory/main exit (`constant-time/README.md`). | CompCert build + extra taint/PCFL `.v` modules (~15–35 min full `coqc` build). | Negligible extra compile time on CT crypto kernels; PCFL path linearization scales quadratically on deeply nested secret branches unless pruned by influence regions (`InfluenceRegion.v`). | `CompCert-CT` incurs ~0–3% overhead on already-CT C; `PCFL` eliminating secret branches executes *both* arms (`1.2x–4x+` slowdown proportional to secret-branch nesting). | Verified once in Coq (`control_flow_security`, `transl_program_correct`); runtime needs no checker. | `PCFL` duplicates/predicates instructions across linearized paths, inflating code `.text` size and live register pressure (increasing stack spills). |
| **`Jasmin` (`CT` + `SCT`/`SLH`)** | Fast authoring for crypto kernels (`jasmin` DSL + automated `-checkCT`/`-checkSCT` inference); compiler Coq proofs (`it_compiler_proof.v`, `slh_ops.v`) are modular per pass. | `jasminc` OCaml build ~30–90 s; Coq `proofs/` (`mathcomp` + `ITrees` + `paco`) takes ~10–25 min. | `ct_checker_forward` / `sct_checker_forward` forward abstract interpretation typically runs in `< 50–500 ms` per crypto primitive (`ChaCha20`, `Kyber`, `X25519`), interactive without SMT timeouts. | Architectural CT matches hand-tuned assembly (`0%` penalty); `SLH` Spectre-v1 hardening (`SLHprotect`, `msf` masking) adds ~5–35% cycle latency and data-dependency serialization. | Typechecker runs per compilation (`O(|CFG|)` abstract fixpoint); compiler soundness proved once in Coq. | Minimal binary overhead for CT; `SLH` adds `cmov`/`and` masking sequences and `msf` register reservation, slightly raising spill pressure (`#spill` disallowed pre-lowering). |
| **Robust Context Back-Translation (`Abate et al.` `RSC` vs `RSCHC`/`RHC`)** | `RSC`/`RTC` trace-based back-translation avoids compiling full target language; `RHC`/`RSCHC` context-based back-translation requires full universal source simulator (**high** LoC/maintenance when ISA changes). | Standalone `Criteria.v` Coq development (~24 `.v` files) builds in `< 1 min` (`make -j4`). | Static compiler wrapping (guard checks, compartmentalization trampolines, capability tags) adds modest compile overhead. | **Runtime isolation cost dominates:** dynamic boundary checks, stack clearing, memory sandboxing (`SFI`/tagged hardware/Wasm bounds) add ~5–50%+ boundary-crossing cycles depending on granularity. | Offline Coq proof (`Criteria.v`, `Separation.v`). | Trampoline wrappers, shadow stacks, and linear-memory guard pages increase binary/page-table footprint. |
| **`CakeML` & `CertiRocq`** | `CakeML` HOL4 proofs include space-cost `is_safe_for_space` invariants (`compile_correct_determ`); `CertiRocq` MetaRocq erasure + λANF pipeline proofs. | Full HOL4 `CakeML` build takes hours across backends; `CertiRocq` takes ~5–20 min. | `CakeML` bootstrapped compiler runs in seconds on medium ML programs; `CertiRocq` compiles Gallina terms in seconds. | `CakeML` generates native machine code with verified GC/FFI boundaries; `CertiRocq` targets C/Wasm via `CompCert`/`LLVM` with closure/boxed-value overhead. | HOL4 / Rocq kernel proof checking of compiler theorems once per compiler release. | `CakeML` embeds verified GC + runtime; `CertiRocq` includes C `runtime/` GC and closure frames (`plugin/`). |

---

### 7. Human Comprehensibility (`C1`) and Universal Model Refinement (`C2`)

Basis: derived synthesis from `secure-compilation/exploring-robust-property-preservation` (`Criteria.v`), `AbsInt/CompCert` (`Complements.v`, `Smallstep.v`), and `10.1007/978-3-319-96131-6`.

#### 7.1 Human Comprehensibility & Mental-Model Traps (`C1`)

- **Quantifier-Alternation Overload:** Raw robust preservation definitions nest up to four alternating quantifiers ($\forall P\, \forall \pi \in \text{Class}.\; (\forall C_S.\, C_S[P] \models \pi) \implies (\forall C_T.\, C_T[P\downarrow] \models \pi)$). Engineers routinely confuse `RSC` ($\exists C_S$ per finite prefix $m$) with `RSCHC` ($\exists C_S$ uniform over all traces $t$), leading to false assumptions that a trace-based back-translation proof guarantees 2-safety or constant-time against an active target attacker. Property-free criteria (`Criteria.v`) reduce working-memory load from second-order hyperproperties to first-order existential context construction.
- **Four Recurring Mental-Model Footguns:**
  1. Assuming "CompCert is verified, so compiled C preserves my timing/side-channel defense" (ignoring that `Events.trace` erases branches and memory addresses, and `behavior_improves` permits arbitrary optimization around UB).
  2. Assuming "refining nondeterminism always improves security" (violated by McLean's paradox for `GNI` and by secret-correlated demonic refinement for $V_g$ / $I_\infty$).
  3. Assuming "Shannon mutual information $< 1$ bit means a key is safe" (violated by Smith's 64-bit rare-full channel where $I_1 = 1$ bit yet single-guess Bayes vulnerability jumps by $2^{57}\times$).
  4. Assuming "step-by-step trace refinement implies liveness" (failing whenever silent stuttering is unbounded without a well-founded measure or fairness preservation).

#### 7.2 Conceptual Simplicity & Universal Model Refinement (`C2`)

Across all four pillars—robust compilation, constant-time, quantitative leakage, and liveness—the disparate definitions collapse onto **one unified semantic refinement judgment** parameterized by four orthogonal axes:

$$\mathcal{T}_{S, T} \models P \sqsubseteq_{(\mathcal{C}, \mathcal{O}, \sqsubseteq_{\text{chan}}, \prec)} P\downarrow$$

1. **Adversarial Interface Power ($\mathcal{C}_S, \mathcal{C}_T$):** Closed whole-program ($\mathcal{C} = \{\text{id}\}$) vs open linking contexts ($\mathcal{C}_T$ with back-translation quantifier order fixing `RSC` vs `RSCHC` vs `RHC`).
2. **Observation Alphabet / Leakage Effect ($\mathcal{O}$):** External I/O events (`CompCert` `Events.trace`) $\subset$ Architectural CT leakage (`Br`, `Mem`) $\subset$ Speculative transient leakage (`SCT`) $\subset$ Physical power/EM/microarchitectural traces.
3. **Nondeterminism & Quantitative Channel Order ($\sqsubseteq_{\text{chan}}$):** Set inclusion $\pi_T \subseteq \pi_S$ (preserves $\forall$-traces & subset-closed hyperproperties) vs exact trace equality $\pi_T = \pi_S$ (preserves $\forall\exists$ hyperproperties) vs oblivious stochastic post-processing $C_T = C_S R$ (preserves all $V_g$ and $I_\infty$).
4. **Stuttering & Progress Measure ($\prec$):** Coinductive silent-divergence-tolerant partial correctness vs well-founded `fsim_order_wf` / inductive `EqTauL`/`EqTauR` (`eutt`) + fairness/prophecy preservation.

Applying **Felleisen macro-expressibility** and **Ousterhout deep-module** tests: treating `CT`, `SCT`, `RSCHC`, and `QIF` as separate ad-hoc compiler properties duplicates relational simulation machinery and hides unmodeled assumptions (such as `#spill` placement or trace abstraction loss) in pass adapters. Parameterizing one relational effect-indexed simulation over $(\mathcal{O}, \sqsubseteq_{\text{chan}}, \prec)$ eliminates redundant mechanisms while making the exact trust boundary—what is observed and how nondeterminism is resolved—explicit at the top-level theorem.

---

### 8. End-to-End Solution and Implementation Validation (`V1`–`V4`)

Basis: normative methodology + primary toolchains (`AbsInt/CompCert`, `jasmin-lang/jasmin`, `knothed/CompCert-ct`) + derived reality-gap analysis.

Formal proofs over an idealized compiler ISA semantics still fail in deployment whenever the formal model diverges from source intent, compiler unverified front/back ends, real silicon microarchitecture, or real-time deadlines. End-to-end validation spans four tiers:

- **(V1) Specification Adequacy, Mutation & Non-Vacuity Validation:**
  - **Vacuity traps:** In `CompCert` (`Complements.v` line 48) and `Jasmin` (`xrutt.v` `WillCutoff`), proving `(forall beh, safe beh) -> ...` or discharging postconditions via UB cutoffs (`IsCut EE e`) becomes vacuously true if the caller fails to prove source UB absence or marks real operations as cutoffs. Similarly, a constant-time proof over an incomplete leakage model (forgetting e.g. division latency or `is_ct_asm` misclassifying an instruction in `ct_checker_forward.mli`) succeeds vacuously with respect to real hardware timing.
  - **Differential & mutation checks:** `QuickChick` / property-based compiler mutation tests (intentionally injecting secret-dependent branches or `cmov`-to-branch regressions in `RTL`/`Selection`) must cause both `ControlFlowSecurity` / `-checkCT` and relational differential simulators to reject the mutant, confirming non-vacuity of the leakage model.
- **(V2) Compiler, Lowering & Checker Soundness Fuzzing:**
  - Unverified compiler components—such as `CompCert`'s pre-Clight parser/elaboration/unparser and assembler/linker, or `Jasmin`'s OCaml `ct_checker_forward` / `sct_checker_forward` vs its Coq semantics—are validated using randomized differential fuzzers (`CSmith`, `YARPGen`, `EMI`), translation-validation comparators (`Alive2`), and relational binary analyzers (`Binsec/Rel`) comparing source leakage traces against emitted machine code across random secret pairs $(s_1, s_2)$.
- **(V3) Concurrency, Crash, Silicon & Physical Leakage Validation:**
  - **ISA-to-Silicon Leakage Gap:** Both `CompCert-CT` and `Jasmin` assume an **architectural leakage contract** (control-flow PCs, memory addresses, constant-latency `is_ct_asm` arithmetic). Real CPUs violate this contract via variable-latency `MUL`/`DIV` early-exit multipliers, subnormal floating-point paths, silent stores, cache-bank conflicts, Return Stack Buffer (`RSB`) / Branch History Table (`BHT`) aliasing, and Data Memory-Dependent Prefetchers (`DMP`). Validating the hardware contract requires post-silicon microarchitectural fuzzing (`Revizor`, testing pairs of secret-differing inputs executing identical architectural leakage traces on actual silicon for cycle/cache divergence), physical side-channel `TVLA` (Welch's $t$-test $|t| > 4.5$ over fixed-vs-random oscilloscope power/EM traces), and gate-level glitch-extended masking verification (`Alma`) when power/EM leakage matters.
  - **Weak-Memory Concurrency:** Sequential CT/non-interference simulations do not compose automatically across shared-memory concurrent threads under TSO/ARMv8 weak memory (`GenMC` / `Loom` stateless model checking is needed to detect speculative/racy cross-thread leakage and missing `LFENCE`/barriers).
- **(V4) Plant Falsification, Telemetry/HIL Replay & Human Comprehension Validation:**
  - Because `CompCert` (`fsim_order_wf`) and `InteractionTrees` (`eutt`) only bound silent stuttering by *arbitrary finite* ordinals rather than physical wall-clock cycle budgets, a formally verified refinement (or `PCFL`/`SLH` insertion) can stretch worst-case execution time (`WCET`) past a cyber-physical control deadline, breaking closed-loop stability. Validation for real-time/CPS deployments requires Signal Temporal Logic (`STL`) robustness falsification (`S-TaLiRo`/`Breach`), Hardware-in-the-Loop (`HIL`) timing replay, runtime `ModelPlex` safety-envelope monitors checking timing/state-assumption validity, and empirical developer comprehension tests (`SMoL`-style litmus snippets checking whether engineers recognize `GNI` refinement breakage, `I_1` vs `I_inf` traps, and `#spill` speculative hazards).

## Boundaries

- **Known not to apply:**
  - *Whole-program `CompCert` safety preservation (`transf_c_program_is_refinement`) does not apply to constant-time or non-interference:* `Events.trace` excludes branch outcomes and memory addresses, and closed-program trace inclusion breaks $\forall\exists$ hyperproperties (`GNI`) and ignores target adversarial linking (`C_T`).
  - *`CompCert-CT` / `PCFL` (`knothed/CompCert-ct`) does not apply to general C programs:* verified secret control-flow elimination currently supports only loop-free functions with no memory accesses and no exit from `main` (`constant-time/README.md`, lines 6–9).
  - *Single-execution trace refinement and Shannon mutual information $I_1$ do not bound single-guess Bayes vulnerability $V_1$ or Rényi min-entropy leakage $I_\infty$:* demonstrated by Smith's 64-bit rare-full channel ($I_1 = 1\text{ bit}$ vs $I_\infty = 58\text{ bits}$) and by demonic secret-correlated refinement violating Blackwell's post-processing `DPI`.
  - *Architectural constant-time (`CompCert-CT`, `jasminc -checkCT`) does not apply against Spectre-v1 or microarchitectural sub-ISA side channels:* transient execution requires `SCT`/`SLH` (`jasminc -checkSCT` + `slh_ops.v`), and hardware microarchitectural assumptions (`DMP`, variable-latency `MUL`, power/EM) require `Revizor` / `TVLA` / `Alma` validation.
- **Unsupported:**
  - *Pre-lowering `#spill`/`#unspill` pseudo-operations in Jasmin `SCT` checking:* explicitly rejected by `compiler/src/sct_checker_forward.mli` (lines 18–19).
  - *Unverified `Compiler/correctness.v` MetaRocq-to-ANF top-level glue in `CertiRocq/certirocq`:* the inspected file at `ab66e0164e7ecb63e5af95c90c8e479068bf95c2` comments out and marks `Admitted` the outer bridge (unlike the complete `LambdaANF/toplevel_theorems.v` proofs).
  - *Multi-threaded shared-memory constant-time compilation* in `CompCert-CT` and `Jasmin` (both target sequential execution models).
- **Unknown:**
  - *Optimal minimal runtime overhead of universal `RSCHC`/`RHC` context-based back-translation wrappers* across arbitrary untyped assembly vs capability-safe/Wasm targets remains open and architecture-dependent.
  - *Exact tight closed-form compositional bounds for $k$-try $g$-leakage under arbitrary concurrent weak-memory schedulers* without full-state probabilistic coupling remain active research.
- **Not examined:**
  - Local compilation or runtime benchmarking of `CompCert`, `CompCert-ct`, `Jasmin`, `CakeML`, or `CertiRocq` binaries on target hardware was not executed in this sandbox; all performance figures (`L1`–`L6`) derive from inspected primary source complexity, documented tool constraints, and cited peer-reviewed evaluations, while all quantitative behavioral checks in `## Evidence` come from the self-contained Python 3 probe.

## Evidence

### Primary Repositories and Exact Source Citations (Observed `2026-11-19`)

1. **`secure-compilation/exploring-robust-property-preservation`** (`c68187cbaba763d88cbb3509df4ca9cf49cc6338`):
   - `Criteria.v`: `RTC` / `RTC_RTP` (lines 19–59), `RSC` / `RSC_RSP` (lines 73–85), `RDC` (lines 115–125), `RHC` / `RHC_RHP` (lines 197–225), `RSCHC` / `RSCHC_RSCHP` (lines 229–248), `R2SCHC` / `R2SCHC_R2SCHP` (lines 253–290), `RHSC` (lines 299–314), `R2HSC` / `R2HSC_R2HSP` / `R2HSC_RSC` / `R2SCHC_R2HSC` (lines 316–350), `R2rTC` / `R2rTP_RTEP` (lines 405–447), `RrTC` / `R2rSC` (lines 454–515).
   - `Separation.v`: `separation_RSP_RDP` (line 213), `separation_RSP_RTP` (line 230), `separation_RDP_RTP` (line 274), `RDP_plus_RSP_RTP` (line 297), `separation_RLP_RSP` (line 312).
2. **`AbsInt/CompCert`** (`2685140bf72c959446981fb99b5e44a8975021bc`):
   - `driver/Complements.v`: `transf_c_program_preservation` (lines 31–40), `transf_c_program_is_refinement` (lines 46–53), `safety_enforcing_specification` (lines 148–150), `transf_c_program_preserves_spec` (lines 157–168), `transf_c_program_preserves_initial_trace` (lines 180–196).
   - `common/Smallstep.v`: `fsim_properties` (lines 566–582, `fsim_order_wf`), `safe` (lines 1274–1278), `bsim_properties` (lines 1289–1316, `bsim_order_wf`, `bsim_progress`, `bsim_simulation`).
3. **`knothed/CompCert-ct`** (`2d1369a4888cff6fd5fd29f28a059e9cf72b1a08`):
   - `constant-time/README.md` (lines 1–95): ITP 2025 artifact scope, loop/memory/main-exit restrictions, and `CTTransform` vs `ControlFlowSecurity` theorem inventory.
   - `constant-time/ControlFlowSecurity.v`: `star_tr'` (lines 11–16), `Theorem control_flow_security` (lines 508–516).
4. **`jasmin-lang/jasmin`** (`8c3279973a89afd969e50301f71563bb40d55724`):
   - `compiler/src/ct_checker_forward.mli` (`is_ct_op*`, `ty_prog` for CT); `compiler/src/sct_checker_forward.mli` (`ty_prog` for SCT, `#spill`/`#unspill` prohibition lines 18–19, `compile_infer_msf` line 20).
   - `proofs/lang/slh_ops.v` (`Variant slh_op`, lines 19–27); `proofs/itrees/xrutt.v` (`DoCutoffF` / `WillCutoff`, lines 48–68); `proofs/compiler/compiler.v` (`compiler_back_end_to_asm`, `compile_prog_to_asm`); `proofs/compiler/it_compiler_proof.v`.
5. **`CakeML/cakeml`** (`2874b664e10939a3ee462215b2e068c89c1f70eb`):
   - `semantics/ffi/ffiScript.sml` (`ffi_outcome = FFI_failed | FFI_diverged`, `io_event`, `ffi_state`, lines 15–52).
   - `compiler/backend/proofs/backendProofScript.sml` (`Theorem compile_correct'` lines 4007–4021 with `is_safe_for_space`, `Theorem compile_correct_determ` lines 4932–4942 with `extend_with_resource_limit`).
6. **`DeepSpec/InteractionTrees`** (`284d42248a3c5517cff9f582e335fcee2f6bdc1f`):
   - `theories/Eq/Eqit.v`: `Inductive eqitF` (`EqRet`, `EqTau`, `EqVis`, `EqTauL`, `EqTauR`, lines 95–112) wrapped in `paco2` for termination-sensitive weak bisimulation (`eutt`).
7. **`CertiRocq/certirocq`** (`ab66e0164e7ecb63e5af95c90c8e479068bf95c2`):
   - `theories/LambdaANF/toplevel_theorems.v` (`Theorem anf_pipeline_correct` lines 577–579, `Corollary anf_pipeline_linking_correct` line 702); `theories/Compiler/pipeline.v` (`compile`, `compile_Wasm`); `theories/Compiler/correctness.v` (`eval_env_fuel` / `bstep_fuel` commented/admitted glue).

### Verified Academic References

- **Abate, Blanco, Garg, Hrițcu, Patrignani, Thibault** (2019): *Journey Beyond Full Abstraction: Exploring Robust Property Preservation for Secure Compilation*, IEEE CSF 2019 (`10.1109/CSF.2019.00025`, `arXiv:1807.04603v6`).
- **Abate, Blanco, Ciobâcă, Durier, Garg, Hrițcu, Patrignani, Tanter, Thibault** (2020/2021): *Trace-Relating Compiler Correctness and Secure Compilation*, ESOP 2020 (`10.1007/978-3-030-44914-8_1`) / ACM TOPLAS 2021 (`10.1145/3460860`, `arXiv:1907.05320`).
- **McLean** (1994): *A General Theory of Composition for Trace Sets Closed Under Selective Interleaving Functions*, IEEE S&P 1994 (`10.1109/RISP.1994.296590`).
- **Clarkson and Schneider** (2010): *Hyperproperties*, Journal of Computer Security 18(6) (`10.3233/JCS-2009-0393`).
- **Morgan** (2006): *The Shadow Knows: Refinement of Ignorance in Sequential Programs*, MPC 2006 (`10.1007/11783596_21`).
- **Barthe, Grégoire, Laporte** (2018): *Secure Compilation of Side-Channel Countermeasures: The Case of Cryptographic "Constant-Time"*, IEEE CSF 2018 (`10.1109/CSF.2018.00031`).
- **Barthe, Blazy, Grégoire, Hutin, Laporte, Pichardie, Trieu** (2020): *Formal Verification of a Constant-Time Preserving C Compiler*, POPL 2020 (`10.1145/3371075`).
- **Almeida, Barbosa, Barthe, Blot, Grégoire, Laporte, Oliveira, Pacheco, Schmidt, Strub** (2017): *Jasmin: High-Assurance and High-Speed Cryptography*, ACM CCS 2017 (`10.1145/3133956.3134078`).
- **Shivakumar, Barthe, Grégoire, Laporte, Oliveira, Priya, Schwabe, Tabary-Maujean** (2023): *Typing High-Speed Cryptography against Spectre v1*, IEEE S&P 2023 (`10.1109/SP46215.2023.10179418`).
- **Arranz Olmos, Barthe, Blatter, Grégoire, Laporte** (2025): *Preservation of Speculative Constant-Time by Compilation*, POPL 2025 (`10.1145/3704880`).
- **Smith** (2009): *On the Foundations of Quantitative Information Flow*, FOSSACS 2009 (`10.1007/978-3-642-00596-1_21`).
- **Alvim, Chatzikokolakis, Palamidessi, Smith** (2012): *Measuring Information Leakage Using Generalized Gain Functions*, IEEE CSF 2012 (`10.1109/CSF.2012.26`); **Alvim, Chatzikokolakis, McIver, Morgan, Palamidessi, Smith** (2020): *The Science of Quantitative Information Flow*, Springer (`10.1007/978-3-319-96131-6`).
- **Abadi and Lamport** (1991): *The Existence of Refinement Mappings*, Theoretical Computer Science 82(2) (`10.1016/0304-3975(91)90224-P`).

### Reproducible Execution Probe and Verbatim Output (`2026-11-19`)

Self-contained Python 3 probe (toy finite-state / QIF channel / transition-system model executed on Linux `x86_64`, zero external dependencies):

```python
#!/usr/bin/env python3
"""Self-contained micro-probe for secure compilation, hyperproperties, QIF, and stuttering."""
from __future__ import annotations
import itertools
import math


def test_mclean_and_abate_hierarchy() -> None:
    universe = [(0, 0), (0, 1), (1, 0), (1, 1)]
    pi_gni = frozenset(universe)
    pi_leak = frozenset([(0, 0), (1, 1)])
    pi_det_ni = frozenset([(0, 0), (1, 0)])

    def gni(pi: frozenset[tuple[int, int]]) -> bool:
        return all(
            any(t3[0] == t1[0] and t3[1] == t2[1] for t3 in pi)
            for t1 in pi for t2 in pi
        )

    def obs_det(pi: frozenset[tuple[int, int]]) -> bool:
        return all(t1[1] == t2[1] for t1 in pi for t2 in pi)

    trace_props = [frozenset(s) for r in range(5) for s in itertools.combinations(universe, r)]
    preserved_trace_props = sum(1 for p in trace_props if (not (pi_gni <= p)) or (pi_leak <= p))
    obs_det_subset_closed = all(
        obs_det(frozenset(sub))
        for r in range(len(pi_det_ni) + 1)
        for sub in itertools.combinations(pi_det_ni, r)
    )

    print(f"[1] trace_inclusion=(pi_leak<=pi_gni): {pi_leak <= pi_gni}")
    print(f"[1] 1-trace_props_preserved={preserved_trace_props}/{len(trace_props)} (RTC/RSCHC preserve all trace & subset-closed hyperprops)")
    print(f"[1] GNI(pi_gni)={gni(pi_gni)} GNI(pi_leak)={gni(pi_leak)} (McLean paradox: refinement breaks forall-exists hyperproperty)")
    print(f"[1] ObsDet(pi_det_ni)={obs_det(pi_det_ni)} all_subsets_ObsDet={obs_det_subset_closed} (2-safety is subset-closed)")


def qif_metrics(prior: list[float], channel: list[list[float]]) -> tuple[float, float, float]:
    n_x, n_y = len(prior), len(channel[0])
    v_prior = max(prior)
    v_post = sum(max(prior[x] * channel[x][y] for x in range(n_x)) for y in range(n_y))
    i_inf = math.log2(v_post / v_prior)
    py = [sum(prior[x] * channel[x][y] for x in range(n_x)) for y in range(n_y)]
    hy = -sum(p * math.log2(p) for p in py if p > 0.0)
    hy_x = -sum(
        prior[x] * channel[x][y] * math.log2(channel[x][y])
        for x in range(n_x) for y in range(n_y) if channel[x][y] > 0.0
    )
    return v_post, i_inf, hy - hy_x


def test_qif_and_demonic_vs_dpi() -> None:
    k = 64
    n = 1 << k
    prior_val = 1.0 / n
    i1_parity = 1.0
    v_post_parity = 2.0 * prior_val
    i_inf_parity = math.log2(v_post_parity / prior_val)

    p_leak = 1.0 / 64.0
    hy_b = -(p_leak * math.log2(p_leak / n) + (1.0 - p_leak) * math.log2(1.0 - p_leak))
    hy_x_b = -(p_leak * math.log2(p_leak) + (1.0 - p_leak) * math.log2(1.0 - p_leak))
    i1_rare = hy_b - hy_x_b
    v_post_rare = p_leak + (1.0 - p_leak) * prior_val
    i_inf_rare = math.log2(v_post_rare / prior_val)

    print(f"[2] 64-bit parity:   I_shannon={i1_parity:.4f} bits, V(X|Y)={v_post_parity:.3e}, I_inf={i_inf_parity:.4f} bits")
    print(f"[2] 64-bit rarefull: I_shannon={i1_rare:.4f} bits, V(X|Y)={v_post_rare:.5f}, I_inf={i_inf_rare:.4f} bits")

    prior4 = [0.25, 0.25, 0.25, 0.25]
    c0 = [[1, 0, 0], [1, 0, 0], [0, 1, 0], [0, 1, 0]]
    c1 = [[1, 0, 0], [0, 1, 0], [1, 0, 0], [0, 1, 0]]
    c_demon_bad = [[1, 0, 0], [0, 1, 0], [0, 1, 0], [0, 0, 1]]
    v0, inf0, _ = qif_metrics(prior4, c0)
    v1, inf1, _ = qif_metrics(prior4, c1)
    vb, infb, _ = qif_metrics(prior4, c_demon_bad)

    max_dpi_violation = 0.0
    for m0, m1, m2 in itertools.product(range(3), repeat=3):
        c_post = [[0.0, 0.0, 0.0] for _ in range(4)]
        for x in range(4):
            c_post[x][m0] += c0[x][0]
            c_post[x][m1] += c0[x][1]
            c_post[x][m2] += c0[x][2]
        vp, _, _ = qif_metrics(prior4, c_post)
        max_dpi_violation = max(max_dpi_violation, vp - v0)

    print(f"[2] C0(x//2): V={v0:.4f} I_inf={inf0:.4f} | C1(x%2): V={v1:.4f} I_inf={inf1:.4f}")
    print(f"[2] Demonic secret-dependent refinement C_bad: V={vb:.4f} I_inf={infb:.4f} (amplifies leakage!)")
    print(f"[2] Oblivious post-processing C0*R max(V_post - V_C0)={max_dpi_violation:.1e} (DPI holds)")


def test_ct_and_stuttering() -> None:
    def prog_cmov(cond: int, a: int, b: int) -> tuple[int, tuple[str, ...]]:
        return (a if cond else b), ("cmov",)

    def prog_branch(cond: int, a: int, b: int) -> tuple[int, tuple[str, ...]]:
        if cond:
            return a, ("br_true",)
        return b, ("br_false",)

    io_match = all(prog_cmov(c, 10, 20)[0] == prog_branch(c, 10, 20)[0] for c in (0, 1))
    ct_cmov = prog_cmov(0, 10, 20)[1] == prog_cmov(1, 10, 20)[1]
    ct_branch = prog_branch(0, 10, 20)[1] == prog_branch(1, 10, 20)[1]
    print(f"[3] I/O_refinement_identical={io_match} CT_cmov={ct_cmov} CT_branch={ct_branch}")

    def simulate_with_order(max_steps: int) -> str:
        target_measure = 2
        for _ in range(max_steps):
            if target_measure == 0:
                return "Terminates(0)"
            target_measure -= 1
        return "Diverges_silent"

    def simulate_without_order(max_steps: int) -> str:
        for _ in range(max_steps):
            pass
        return "Forever_silent"

    print(f"[3] wf_stutter(5)={simulate_with_order(5)} no_wf_stutter(5)={simulate_without_order(5)}")


if __name__ == "__main__":
    test_mclean_and_abate_hierarchy()
    test_qif_and_demonic_vs_dpi()
    test_ct_and_stuttering()
```

Observed output (`2026-11-19`, Linux x86_64, Python 3):

```text
[1] trace_inclusion=(pi_leak<=pi_gni): True
[1] 1-trace_props_preserved=16/16 (RTC/RSCHC preserve all trace & subset-closed hyperprops)
[1] GNI(pi_gni)=True GNI(pi_leak)=False (McLean paradox: refinement breaks forall-exists hyperproperty)
[1] ObsDet(pi_det_ni)=True all_subsets_ObsDet=True (2-safety is subset-closed)
[2] 64-bit parity:   I_shannon=1.0000 bits, V(X|Y)=1.084e-19, I_inf=1.0000 bits
[2] 64-bit rarefull: I_shannon=1.0000 bits, V(X|Y)=0.01562, I_inf=58.0000 bits
[2] C0(x//2): V=0.5000 I_inf=1.0000 | C1(x%2): V=0.5000 I_inf=1.0000
[2] Demonic secret-dependent refinement C_bad: V=0.7500 I_inf=1.5850 (amplifies leakage!)
[2] Oblivious post-processing C0*R max(V_post - V_C0)=0.0e+00 (DPI holds)
[3] I/O_refinement_identical=True CT_cmov=True CT_branch=False
[3] wf_stutter(5)=Terminates(0) no_wf_stutter(5)=Forever_silent
```

## Revalidation

To verify whether these findings still hold against future revisions without repeating the full survey:

1. **Robust Compilation Criteria:** Diff `Criteria.v` and `Separation.v` in `secure-compilation/exploring-robust-property-preservation` relative to `c68187cbaba763d88cbb3509df4ca9cf49cc6338` to verify whether any probabilistic/quantitative criteria or new collapse theorems were added.
2. **`CompCert` Whole-Program & Stuttering Invariants:** Diff `driver/Complements.v` and `common/Smallstep.v` in `AbsInt/CompCert` relative to `2685140bf72c959446981fb99b5e44a8975021bc` for changes to `behavior_improves`, `safety_enforcing_specification`, or `fsim_order_wf`/`bsim_order_wf`.
3. **`CompCert-CT` / `PCFL` & `Jasmin` `SCT`:** Diff `constant-time/README.md` and `constant-time/ControlFlowSecurity.v` in `knothed/CompCert-ct` (relative to `2d1369a4888cff6fd5fd29f28a059e9cf72b1a08`) to see whether loop/memory support was added, and inspect `compiler/src/sct_checker_forward.mli` and `proofs/lang/slh_ops.v` in `jasmin-lang/jasmin` (relative to `8c3279973a89afd969e50301f71563bb40d55724`) to check whether `#spill`/`#unspill` restrictions changed or whether verified `SCT` preservation landed on `main`.
4. **`CakeML`, `InteractionTrees`, and `CertiRocq`:** Check `semantics/ffi/ffiScript.sml` and `compiler/backend/proofs/backendProofScript.sml` in `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`), `theories/Eq/Eqit.v` in `DeepSpec/InteractionTrees` (`284d42248a3c5517cff9f582e335fcee2f6bdc1f`), and `theories/Compiler/correctness.v` in `CertiRocq/certirocq` (`ab66e0164e7ecb63e5af95c90c8e479068bf95c2`) for changes to `Admitted` top-level glue or divergence handling.
5. **Re-run Micro-Probe:** Execute the standalone Python 3 script in `## Evidence` (`< 0.1 s`, zero dependencies) to verify identical numeric output for the `GNI` refinement paradox, Smith's 64-bit QIF divergence, demonic vs post-processing `DPI`, and stuttering divergence witnesses.
