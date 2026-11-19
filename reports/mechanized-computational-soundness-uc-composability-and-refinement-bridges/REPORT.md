# Mechanized computational soundness, UC composability, and compiler-refinement bridges

## Summary

A pipeline that synthesizes a cryptographic protocol and then compiles it with a kernel-checked
compiler crosses three different "implements" relations, and no mechanized tool proves more than
one of them:

- **(S) symbolic equivalence** of Dolev–Yao terms (patterns, deduction);
- **(C) computational indistinguishability** up to an advantage `ε` against resource-bounded
  probabilistic adversaries (game-based, state-separating, simulation-based/UC);
- **(R) possibilistic trace refinement**, the statement of verified compilers (CompCert backward
  simulation, Jasmin equivalence of interaction trees).

What a future design should retain:

1. **S ⇒ C holds only inside fences.** Abadi–Rogaway's soundness theorem needs *acyclic*
   expressions, a *type-0* (repetition-, which-key- and length-concealing) encryption scheme and a
   *passive* adversary, and it loses a factor `m + n` (number of keys in the two expressions) in
   the concrete bound. Key cycles need key-dependent-message security, which is independent of
   CCA-2. Adaptive corruption breaks simulation arguments for encryption. Owl, the examined tool
   that automates such reasoning with a computational theorem, excludes key cycles by typing and
   supports static corruption and asymptotic bounds only.
2. **C composes additively, and the ledger can be kernel-checked.** In EasyCrypt the UC
   composition theorem is `Adv(ρ(π), F) ≤ ε_ρ + ε_π` over cost-indexed adversary classes; a hybrid
   over `q` oracle calls costs exactly a factor `q`; in SSProve a reduction (`link`) costs nothing
   and a game hop adds by the triangle inequality. The additive bound is worst-case tight.
3. **R ⇒ C is false in general.** Refinement preserves exactly the subset-closed hyperproperties;
   CompCert's preservation theorem is stated for predicates on single behaviours. A refinement may
   resolve nondeterminism with a secret (executable counterexample below).
4. **The bridge that works is "equality per coin tape".** If randomness is an explicit,
   deterministic input of the semantics (CompCert's `world`, Jasmin's `syscall_state` with
   `get_random`), the source is safe, and both sides are determinate, then compiler correctness
   yields the *same* observable behaviour for the same coin tape, so every output distribution and
   every `ε` is preserved with zero loss. Leakage (timing, memory access) is not in that trace
   and needs a separate preservation theorem.
5. **Robust compilation is the PL-side name of UC.** UC perfect emulation coincides with robust
   hyperproperty preservation; the computational case is a separate, later result.

## Applicability

The report compares mechanized frameworks at the revisions listed in `REPORT.json` and relates
them through the papers listed there. The subjects are not a combined system: they are compared,
and the report states which interface conditions would let their theorems be chained.

- **Source-inspected at a pinned revision:** EasyCrypt (`theories/encryption/Hybrid.ec`,
  `README.md`), EasyUC (`README.md`, directory layout), SSProve
  (`theories/Crypt/package/pkg_advantage.v`, `README.md`), CryptHOL and Constructive Cryptography
  in the AFP development mirror (`thys/CryptHOL/ROOT`,
  `thys/Constructive_Cryptography/Constructive_Cryptography.thy`), Owl (`README.md`), CompCert 3.18
  development head (`driver/Complements.v`, `driver/Compiler.v`, `common/Behaviors.v`,
  `common/Smallstep.v`, `common/Determinism.v`, `common/Events.v`, `x86/Asm.v`), Jasmin
  (`proofs/lang/syscall.v`, `proofs/lang/relational_logic.v`, `proofs/lang/core_logics.v`,
  `proofs/itrees/xrutt.v`, `proofs/compiler/it_compiler_proof.v`), Clutch (`README.md`).
- **Read in full text:** Abadi–Rogaway; Owl and OwlC papers (author/USENIX copies); the journal
  version of Barbosa et al.; Patrignani–Künnemann–Wahby (arXiv v3); Clarkson–Schneider.
- **Read at abstract level only:** Canetti's UC paper (the full text could not be retrieved; UC
  definitions below are taken from the abstract plus the restatements in Barbosa et al. and
  Patrignani et al.), the SSProve journal paper (the repository README maps paper claims to
  lemmas), and the supporting citations on key cycles, non-committing encryption and
  simulatable Dolev–Yao libraries.

No proof assistant was run: lemma statements were read, not rechecked. Statements about a
repository apply to the pinned revision only. Statements labelled *derived* are this report's
reasoning. The executable probe uses toy, information-theoretic objects (exact rational
arithmetic) to exhibit mechanisms; it does not model any real scheme.

Naming note for retrieval: the computational-soundness theorem for formal encryption is due to
**Abadi and Rogaway**. It is unrelated to the Abadi–Burrows–Lampson–Plotkin access-control
calculus, which is an authorization logic.

## Findings

### 1. Three judgments and what each quantifies over

| | (S) symbolic | (C) computational | (R) refinement |
|---|---|---|---|
| Objects | terms over keys, pairs, `{M}_K` | probabilistic programs / packages / ITMs | labelled transition systems, interaction trees |
| Judgment | `M ≅ N` (equal patterns up to key renaming) | `\|Pr[A∘G₀ ⇒ 1] − Pr[A∘G₁ ⇒ 1]\| ≤ ε(A)`; UC: `∀A ∃S ∀Z. Exec(Z,A,π) ≈ Exec(Z,S,F)` | `∀ beh ∈ Beh(tgt). ∃ beh' ∈ Beh(src). beh' improves-to beh` |
| Adversary | fixed deduction rules | any program in a cost class (time, oracle calls) | none: the environment supplies event results |
| Randomness | fresh names | sampling with a distribution | absent; at most results of external events |
| Number | none | `ε`, cost | none |
| Property class preserved under composition | equivalence | advantage bounds (additive) | trace properties; subset-closed hyperproperties |

Basis: derived, from the definitions quoted in the following sections.

### 2. Symbolic ⇒ computational: the Abadi–Rogaway theorem and its exact hypotheses

- **Formal side.** Expressions are bits, keys, pairs and encryptions. `pattern(M)` replaces every
  ciphertext whose key is not recoverable from `M` by an undecryptable box; `M ≡ N` iff the
  patterns are equal, and `≅` additionally allows key renaming. Example from the paper:
  `pattern(({{K1}K2}K3, K3)) = ({□}K3, K3)`.
- **Computational side.** *Type-0 security*: no probabilistic polynomial-time adversary
  distinguishes the oracle pair `(E_k(·), E_k'(·))` under two independent keys from
  `(E_k(0), E_k(0))`. The paper classifies eight notions by whether ciphertexts conceal or reveal
  repetition, which key was used, and message length; type-0 conceals all three, whereas the
  conventional notion is type-3: "a ciphertext may reveal the length of the message and which key
  is being used, but it should not reveal if two ciphertexts are encryptions of the same message".
- **Theorem 1.** "Let M and N be acyclic expressions and let Π be a type-0 secure encryption
  scheme. Suppose that M ≅ N. Then [[M]]_Π ≈ [[N]]_Π."
- **Concrete form** (stated in the paper after the proof): if `M`, `N` have `m`, `n ≥ 1` keys and
  an adversary of time `t` distinguishes the two ensembles with advantage `ε`, there is an
  adversary against type-0 security with advantage `ε' ≥ ε/(m+n)`, at most `max{m,n}` oracle
  queries, and time `t + α·T_Π·(|M|+|N|)`.
- **No converse.** Indistinguishability does not imply equivalence; the paper gives the reason
  (messages outside the plaintext space can make inequivalent expressions coincide).
- **Scope.** Expressions, not protocols; an eavesdropper, not an active attacker. Extensions to
  active adversaries (Micciancio–Warinschi) and to reactive simulatability
  (Backes–Pfitzmann–Waidner) are separate theorems with their own restrictions.

Basis: normative for the theorem (the paper defines it) + derived for the scope remarks.

### 3. Key cycles

- Abadi–Rogaway, Section 4.2: from any type-`n` secure scheme one can build a type-`n` secure
  scheme that "would be completely insecure if the adversary were given ... even a single
  encryption of the underlying key"; hybrid arguments "do not work in the presence of such
  cycles", hence the acyclicity hypothesis. The formal model has no such restriction:
  `{K}_K ≅ {0}_K` formally.
- Soundness with key cycles requires key-dependent-message (KDM) security; soundness for key
  cycles "neither implies nor is implied by" CCA-2 security (Adão–Bana–Herzog–Scedrov, abstract).
  KDM security was introduced by Black–Rogaway–Shrimpton; a standard-model circular-secure
  scheme is Boneh–Halevi–Hamburg–Ostrovsky.
- Owl removes the case by construction: "name types for encryption keys rule out key cycles by
  fiat, since encryption keys may only encrypt data that has been previously declared", and "key
  cycles (e.g., k encrypts k′, which encrypts k) break standard security notions, and thus they
  are excluded by our type system".
- **Probe A** (exact, n-bit one-time pad `E_k(m) = m ⊕ k` and a variant `Π′` that returns `(1,k)`
  when `m = k`): against key-independent messages the worst one-time distinguishing advantage is
  `0` for the pad and exactly `2^-n` for `Π′`; yet `{K}_K` versus `{0}_K` is distinguishable with
  advantage `1 − 2^-n` for both, and `Π′` reveals the key with probability 1.

Basis: normative (paper text) + documentation (abstract-level citations) + execution (probe A).

Design consequence (derived): a synthesis front end that emits key-wrapping terms must either
prove acyclicity of the "encrypts" relation (a static, graph-level check, as Owl's declaration
order does) or demand a KDM assumption explicitly in the assumption ledger; an IND-CPA or CCA-2
hypothesis does not cover it.

### 4. Adaptive corruption and the commitment problem

- Non-interactive encryption secure against adaptive corruption (non-committing encryption) has
  a simple random-oracle solution but none in the standard model with a non-programmable oracle
  (Nielsen, abstract). The simulator must output a ciphertext before knowing the plaintext and
  later explain it with a key.
- The same obstacle appears in simulatable Dolev–Yao libraries for symmetric encryption as the
  "commitment problem" when a key is revealed after use (Backes–Pfitzmann; the one-time pad is
  noted there as the exception).
- Owl: "OWL only supports static corruptions via the adversary label; this is inherited from our
  use of simulation-based security ... commitments and encryptions are known to interact with
  simulation-based security in subtle ways". Corruption is by *name* (information-flow labels) and
  hierarchical; forward secrecy is encoded "by having the adversary commit to the point in time
  where compromise happens".
- UC commitments are impossible in the plain model and need a setup such as a common reference
  string (Canetti–Fischlin); shared or global setup changes the composition theorem's
  hypotheses (Canetti–Dodis–Pass–Walfish).

Basis: documentation (Owl paper full text; other items at abstract level).

Design consequence (derived): the corruption model is part of the theorem's type. A component
proved under static, name-based corruption cannot be plugged into a context whose environment
may corrupt adaptively without a new proof; record the corruption model next to `ε`.

### 5. Simulation-based security and universal composition, as mechanized

- **Definition shape.** `π` UC-emulates `F` iff `∀A. ∃S. ∀Z. Exec(Z, A, π) ≈ Exec(Z, S, F)`, where
  the environment `Z` outputs one bit; it suffices to consider the dummy adversary; composition:
  if `π_s` emulates `F_s` then `π_l[π_s]` emulates `π_l[F_s]`. (Restated from Patrignani et al.,
  Definitions 1–2 and Theorems 5 and 7, which cite Canetti.) Canetti's abstract: security "is
  maintained under a general composition operation, called universal composition".
- **EasyCrypt with a cost logic (Barbosa et al.).** Adversaries, simulators and environments are
  modules whose types restrict memory footprint and cost (intrinsic time plus counts of oracle
  calls). The generic statement pattern is
  `∀A. ∃B. adv_S(A) ≤ adv_H(B) + ε ∧ cost(B) ≤ cost(A) + δ`; the authors stress that it "is only
  meaningful because the cost of B is conditioned on the cost of A". A simulator able to look
  inside the ideal functionality would make "all protocols ... secure", so the simulator's type
  excludes that memory. Mechanized lemmas: transitivity (Lemma 6.1), dummy adversary
  (Theorem 6.2) and
  **Theorem 6.3**: `Adv^{uc,Sπ}(π, f) ≤ ε_π ⇒ Adv^{uc,Sρ}(ρ(f), F) ≤ ε_ρ ⇒ Adv^{uc}(ρ(π), F) ≤ ε_ρ + ε_π`,
  with the environment class for `π` enlarged to "an environment that internally uses c_env
  resources and additionally runs ρ".
- **EasyUC.** Functionalities have hierarchical addresses; abstractions route messages,
  "modeling the coroutine-style communication of UC". A DSL (`uc-dsl/`) type-checks
  functionalities and simulators and rejects "badly formed messages", simulators that interfere
  with environment–adversary communication, and "violations of the coroutine model"; a prototype
  translator emits EasyCrypt, and proofs rely on "the EasyUC versions of the UC composition and
  dummy adversary theorems". Case study: Diffie–Hellman key exchange plus one-time pad (`smc/`).
- **CryptHOL constructive cryptography.** `advantage 𝒜 res1 res2 = |spmf (connect 𝒜 res1) True −
  spmf (connect 𝒜 res2) True|`; the locale `constructive_security_aux` assumes, for every
  well-typed distinguisher with `interaction_bounded_by ... (bound η)`, that
  `negligible (λη. advantage (𝒜 η) (sim η |= 1_C ⊳ ideal_resource η) (real_resource η))`. The
  statement is asymptotic in `η`; theorems named `composability` and
  `parallel_constructive_security` follow in the same file (their statements were not analysed).
- **SSProve.** Not a UC framework: packages with import/export interfaces, composed by `link`
  and `par`, proved with a probabilistic relational Hoare logic. Stated axioms: functional and
  propositional extensionality, constructive indefinite description, an abstract real-number
  type, and one admitted `mathcomp-analysis` lemma (`interchange_psum`) on older library versions.
- **UC as secure compilation.** For perfect emulation, UC coincides with *robust hyperproperty
  preservation* of the "compiler" from the ideal language to the protocol language
  (Patrignani et al., Theorems 1 and 4); composition and the dummy-adversary theorem are derived
  on the compilation side. The paper restricts itself to perfect emulation and conjectures that
  computational UC "may result in a connection with a different RC criterion"; a computational
  treatment is Künnemann–Patrignani–Cecchetti (CSF 2024).

Basis: source (EasyUC README, AFP theory, SSProve README and lemma file) + documentation (papers).

### 6. The algebra of ε: every rule that moves a bound, with its kernel-checked form

| Step | Loss | Mechanized statement (file at pinned revision) |
|---|---|---|
| Definition | — | SSProve `AdvantageE G₀ G₁ A := \|Pr (A ∘ G₀) true − Pr (A ∘ G₁) true\|` (`pkg_advantage.v:79`) |
| Reduction (move a package into the adversary) | 0 | `Advantage_link : AdvantageE G₀ G₁ (A ∘ P) = AdvantageE (P ∘ G₀) (P ∘ G₁) A` (`:123`) |
| Parallel context | 0 | `Advantage_par : AdvantageE (par G₀ G₁) (par G₀ G₁') A = AdvantageE G₁ G₁' (A ∘ par G₀ (ID E₁))` (`:142`) |
| Game hop | additive | `Advantage_triangle : AdvantageE P Q A <= AdvantageE P R A + AdvantageE R Q A` (`:188`) |
| Hybrid over `q` oracle calls | ×`q` (equality) | EasyCrypt `Hybrid_restr`: `Pr[Ln(Ob,A)…] − Pr[Rn(Ob,A)…] = q%r * (Pr[HybGame(A,Ob,L(Ob))…] − Pr[HybGame(A,Ob,R(Ob))…])` (`theories/encryption/Hybrid.ec:594`) |
| UC composition | additive | Barbosa et al., Theorem 6.3: `ε_ρ + ε_π` |
| Symbolic → computational (expressions) | ×`(m+n)` | Abadi–Rogaway, concrete form of Theorem 1 |
| Error budget as a resource | additive, splittable | Eris error credits: "a separation logic resource that tracks an upper bound on the probability that a program returns an erroneous result" (abstract; Clutch project, built on Iris 4.5.0) |

Observations:

- **State separation is a hypothesis, not a law.** SSProve's `adv_equiv` quantifies only over
  adversaries whose locations are `fseparate` from both games; the README notes "disjointness of
  state is not required by our package definitions and laws" and is added as a hypothesis of each
  security theorem. A linker that merges modules must discharge it.
- **The additive bound cannot be improved in general (Probe B).** For `n` modules that each
  differ from their ideal by a visible bad event of probability `ε`, the exact distance of the
  composition is `1 − (1−ε)^n`, within a factor `(1−ε)^{n−1}` of `nε` (e.g. `ε = 1/1024`, `n = 64`:
  `0.060616` vs bound `0.0625`). For modules whose gap is an independent bias of size `ε`, the
  exact distance grows much more slowly (`0.006215` for the same `ε`, `n`). A ledger that only
  stores `ε` per module must assume the first case.
- **Security bits.** Composing `n` instances costs at most `log2 n` bits; a `q`-query hybrid
  costs `log2 q` bits; the Abadi–Rogaway step costs `log2(m+n)` bits. Asymptotic frameworks
  (Owl, CryptHOL constructive security) yield no number to enter.
- **Cost must travel with ε.** A bound against adversaries of cost `c` says nothing after a
  reduction that raises cost; Barbosa et al. enlarge the environment's cost class in
  Theorem 6.3 for exactly this reason.

Basis: source + documentation + execution (Probe B) + derived (bit accounting).

### 7. What a verified compiler proves, and why it is not secrecy

CompCert (quotations from the pinned revision):

```coq
Inductive program_behavior: Type :=
  | Terminates: trace -> int -> program_behavior | Diverges: trace -> program_behavior
  | Reacts: traceinf -> program_behavior        | Goes_wrong: trace -> program_behavior.
Definition behavior_improves (beh1 beh2: program_behavior) : Prop :=
  beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.
Theorem transf_c_program_correct: forall p tp, transf_c_program p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Theorem transf_c_program_preservation: forall p tp beh, transf_c_program p = OK tp ->
  program_behaves (Asm.semantics tp) beh ->
  exists beh', program_behaves (Csem.semantics p) beh' /\ behavior_improves beh' beh.
Definition specification := program_behavior -> Prop.
Definition safety_enforcing_specification (spec: specification): Prop :=
  forall beh, spec beh -> not_wrong beh.
Theorem transf_c_program_preserves_spec: forall p tp spec, transf_c_program p = OK tp ->
  safety_enforcing_specification spec -> c_program_satisfies_spec p spec ->
  asm_program_satisfies_spec tp spec.
```

- Events are `Event_syscall`, `Event_vload`, `Event_vstore`, `Event_annot`; the inspected files
  contain no notion of probability. A `specification` is a predicate on *one* behaviour, so only
  trace properties are expressible; the theorem needs the specification to exclude going wrong.
- The final-state, progress and step clauses of `bsim_properties` (`common/Smallstep.v:1289`)
  all assume `safe L1 s1`: once the source can go wrong, the target is unconstrained.
- Clarkson–Schneider: for trace properties "satisfaction is the same relation as refinement",
  but "this kind of refinement does not generally work for security policies"; refinement is
  valid exactly for subset-closed hyperproperties, and every safety hyperproperty is subset
  closed (Theorem 1, `SHP ⊂ SSC`). Possibilistic information-flow policies such as generalized
  noninterference are not subset closed.
- **Probe C.** A specification "output any bit" is trace-refined by "output the secret bit";
  the specification is noninterferent, the implementation is not, and reading the specification
  probabilistically (uniform bit) the distinguishing advantage rises from `0` to `1`.

Basis: source (CompCert) + documentation (Clarkson–Schneider) + execution (Probe C).

### 8. The working bridge: randomness as a deterministic resource, equality per coin tape

Source facts:

- **CompCert.** `common/Determinism.v` models "a notion of deterministic external world that
  uniquely determines the results of external calls": `CoInductive world := World (io: string ->
  list eventval -> option (eventval * world)) ...`; `world_sem` pairs a semantics with a world and
  `Theorem world_sem_deterministic: sem_deterministic world_sem` holds under `determinate L`.
  `x86/Asm.v` proves `semantics_determinate`. `transf_cstrategy_program_preservation`
  (`driver/Complements.v:58`) includes both directions: every non-wrong `Cstrategy` behaviour is
  an `Asm` behaviour, and if no `Cstrategy` behaviour goes wrong, every `Asm` behaviour is a
  `Cstrategy` behaviour.
- **Jasmin.** Randomness is the only system call: `Variant syscall_t := RandomBytes of wsize & Z`
  and `Class syscall_sem (syscall_state : Type) := { get_random : syscall_state -> Z ->
  syscall_state * seq u8 }` (`proofs/lang/syscall.v`). The back-end theorem
  `it_compiler_back_end_to_asmP` (`proofs/compiler/it_compiler_proof.v:1579`) concludes
  `wkequiv_io (back_end_to_asm_pre xfd) (isem_stack sp rip fn) (isem_asm xp fn)
  (back_end_to_asm_post fn xfd)`, and both relations contain the conjunct
  `s.(fscs) = t.(asm_scs)` / `s'.(fscs) = t'.(asm_scs)`: source and target start and end with the
  *same* randomness state. `wkequiv_io` is defined with `xrutt (errcutoff (is_error wE_l))
  nocutoff ...` (`proofs/lang/relational_logic.v:222`); `xrutt` is "a generalization of rutt that
  supports the representation of undefined behavior", relating trees "up to triggered events that
  we call cutoff points, beyond which the relation holds trivially", and the cutoff is placed on
  source error events only.

Derived bridge lemma (not mechanized in any examined subject; the argument is elementary):

```text
Assume  (a) source and target observable behaviour are functions  b_src, b_tgt : CoinTape × Input → Behaviour
            (determinacy once the world / syscall state is fixed);
        (b) the source is safe on the inputs considered (no Goes_wrong / no cutoff);
        (c) compiler correctness in its two-sided or determinate form: b_tgt(w, i) = b_src(w, i).
Then    for every distribution D on coin tapes, every input i and every measurable test T on behaviours,
            Pr_{w←D}[T(b_tgt(w,i))] = Pr_{w←D}[T(b_src(w,i))],
        hence every advantage statement about the source's observable behaviour holds for the target
        with the same ε and an adversary of the same cost (the adversary is unchanged).
```

Conditions that are easy to violate (derived):

1. **Inclusion is not enough.** With a nondeterministic source (C expression evaluation order in
   `Csem`, unspecified values), (c) only gives membership in a set; Probe C shows the failure.
   Use the determinate strategy semantics or prove the source determinate.
2. **All randomness through the modelled interface.** Coins obtained by any other event (reading
   a device, timing) are outside `w`.
3. **Same consumption.** The randomness-state equalities in the Jasmin pre- and postcondition
   are the part of the statement that ties the target's draws to the source's; a compiler
   statement without them would permit re-sampling, which preserves distributions only by a
   separate argument. (How strongly an abstract `get_random` plus state equality pins down the
   number and order of draws was not analysed beyond the statement.)
4. **Adversarial contexts.** (c) is a whole-program or per-function statement against
   well-behaved callers. Security against arbitrary *target* contexts is robust compilation
   (Section 5), a different theorem.
5. **Leakage.** Behaviours contain I/O events, not time or addresses. Constant-time preservation
   for a CompCert variant is a separate result (Barthe et al., POPL 2020); OwlC obtains
   source-level side-channel resistance from an opaque secret type and states that it provides no
   "assembly- or hardware-level guarantees since we use stock rustc".

Probe C's last line is the positive case: two different programs computing `c ⊕ h` from a coin
`c` agree on all four `(c, h)` pairs and both have advantage exactly `0`.

Basis: source (CompCert, Jasmin) + derived (lemma and conditions) + execution (Probe C).

### 9. An existing end-to-end instance and its trust ledger: Owl and OwlC

| Layer | Statement | Evidence kind | Explicit limits |
|---|---|---|---|
| Owl type system | well-typed protocols satisfy *simulatability* and *correctness* (paper Theorem 1 over a core language with symmetric/asymmetric primitives, Diffie–Hellman, random-oracle hashing) | paper proof; type checker uses Z3 | asymptotic bounds; static, name-based corruption; no unlinkability properties |
| Specification compiler | Owl protocol → interaction-tree specification in Verus | trusted, "simple" | in the TCB |
| OwlC code generator | Rust code refines the interaction tree: "performs exactly the network I/O that the protocol specified"; secrets behind an opaque constant-time type; declassification controlled by linear ghost permissions | untrusted generator, output verified by Verus | TCB: "the Rust compiler, Verus, Owl, and OwlC's specification compiler"; link to the verified primitive library is axiomatized |
| rustc | none | — | microarchitectural channels out of scope |

The repository at the pinned revision lists supported primitives (authenticated symmetric
encryption, CCA-secure public-key encryption, MACs, signatures, Diffie–Hellman, HKDF, unique
nonces) and ships WireGuard and HPKE case studies (`wg/`, `hpke/`).

Basis: documentation (papers, README) + source (directory layout).

### 10. Comparison matrix

| System (revision in `REPORT.json`) | Host / kernel | Relation proved | Bounds | Composition principle | Path to executable code |
|---|---|---|---|---|---|
| EasyCrypt | own kernel; goals may go to SMT solvers through Why3 (README) | probabilistic relational Hoare logic; game hops | concrete; cost logic per Barbosa et al. | module functors; `Hybrid` theory | README: "proving the functional correctness of low-level implementations"; the Jasmin tree has `proofs/toEC/` and `eclib/` (contents not analysed) |
| EasyUC | EasyCrypt | UC emulation in a coroutine model | concrete | composition and dummy-adversary meta theorems | none stated |
| CryptHOL + Constructive Cryptography | Isabelle/HOL (AFP) | game-based; constructive (simulation) security | asymptotic locale (`negligible`), bounded interaction | `composability`, parallel composition | none stated |
| SSProve | Rocq + stated axioms | advantage between packages | concrete | `link`, `par`, interchange law | Jasmin word/utility files present under `theories/Crypt` |
| Owl / OwlC | Haskell checker + Z3; Verus for output | simulatability via typing | asymptotic | modular typing of sub-protocols | verified Rust library |
| Clutch family | Rocq + Iris 4.5.0 | refinement / couplings / error bounds for higher-order probabilistic programs | concrete (error credits) | separation-logic framing | none stated |
| CompCert | Rocq | backward simulation, behaviour improvement | none | separate compilation theorem | assembly |
| Jasmin | Rocq | interaction-tree equivalence with cutoff, equal randomness state | none | per-function, per-pass | assembly |

Squirrel ("higher-order probabilistic logic following the computationally complete symbolic
attacker approach, and provides guarantees in the computational model"), IPDL (Coq 8.14.1) and
FCF ("machine-checked proofs of cryptography in the computational model", Coq 8.13) were seen
only through their README files.

Basis: source (READMEs and files named above) + documentation.

### 11. Interface invariants for chaining the three relations

Derived checklist; each row names the theorem that fails silently if the invariant is dropped.

| # | Invariant at the boundary | Breaks if absent |
|---|---|---|
| I1 | Key-usage discipline: acyclic "encrypts" relation, or an explicit KDM assumption | S ⇒ C soundness |
| I2 | Encryption assumption matches what terms hide (length, key identity, repetition) | S ⇒ C soundness (type-0 vs type-3) |
| I3 | Adversary activity and corruption model identical on both sides of a composition | simulation proofs; UC composition |
| I4 | Every `ε` stored with its adversary cost class; reductions update both | meaning of any composed bound |
| I5 | State separation between adversary and games, and between linked modules | SSProve-style laws, UC simulator restrictions |
| I6 | Setup (random oracle, reference string) is local to one instance or the theorem is for global setup | UC composition |
| I7 | Source determinate and safe; randomness only through one modelled interface; equal consumption | R ⇒ C transfer |
| I8 | Leakage model stated and preserved by its own theorem | secrecy after compilation |
| I9 | Target-context adversaries covered by a robust-compilation statement, not by whole-program correctness | security of linked foreign code |
| I10 | The trusted base is the union: kernels, SMT solvers, specification translators, unverified back ends | "verified" as a single bit |

### 12. Failure catalogue

| Trap | Smallest instance | Detected by |
|---|---|---|
| Key cycle | `{K}_K` treated as `{0}_K` | declaration-order typing (Owl); acyclicity check; KDM hypothesis |
| Length leak | formal `{0}_K ≅ {00}_K`, scheme reveals length | choose type-0 scheme or a length-revealing formal equivalence |
| Late key reveal | key output after ciphertexts under adaptive corruption | restrict to static corruption; non-committing primitives |
| Bound without cost | `∃B. adv(A) ≤ adv(B)` with unbounded `B` | cost-indexed module types |
| Simulator peeks | simulator reads ideal functionality's memory | memory-footprint restriction in the simulator's type |
| Shared state across packages | adversary and game share a location | `fseparate` hypotheses |
| Refinement resolves a choice with a secret | "any bit" ↦ "secret bit" | determinate source; hyperproperty-aware criterion |
| Re-sampling in the target | target draws extra coins | equal randomness-state conjunct |
| Unverified last step | stock compiler after a verified front end | TCB ledger entry |

Basis: derived from Sections 2–9.

## Boundaries

- **Not examined:** the Iris core development (hosted outside GitHub; seen only as a dependency
  version in Clutch's README); CryptoVerif, Squirrel, IPDL, FCF, ILC and DY* beyond README or
  citation level; quantum adversaries; the internals of EasyCrypt's kernel and of the Why3/SMT
  interface; UC variants (GUC, IITM, GNUC, simplified UC) and their mutual differences; the
  constant-time-preserving CompCert development itself (cited from its abstract only).
- **Not examined:** the full text of Canetti's UC paper, of the SSProve journal paper, and of
  the cited works on KDM security, non-committing encryption, UC commitments and simulatable
  Dolev–Yao libraries; claims about them are abstract-level.
- **Unknown:** whether any examined repository mechanizes the bridge lemma of Section 8 (a
  theorem transferring an advantage bound across a compiler-correctness theorem). It was not
  found in the files read; a full search of Jasmin, SSProve or EasyCrypt libraries was not done.
- **Unknown:** the exact form of `xrutt` beyond its header comment, and therefore whether the
  Jasmin statement is strictly a two-sided equivalence for safe programs in every case
  (`safe_xrutt_rutt` in `proofs/lang/core_logics.v` states an equivalence with `rutt` for safe
  source programs; its hypotheses were not analysed).
- **Known not to apply:** Abadi–Rogaway's theorem to cyclic expressions, to active adversaries,
  or to schemes that are not type-0; Owl's theorem to adaptive corruption or concrete bounds; the
  UC = robust-hyperproperty-preservation equivalence to computational emulation; CompCert's
  specification-preservation theorem to properties that relate several executions.
- **Unsupported:** probabilistic semantics in CompCert's behaviours; assembly-level side-channel
  guarantees in OwlC; concrete security bounds in Owl.
- **Attractive but not established:** "a verified compiler preserves cryptographic security";
  "symbolic verification plus IND-CCA implies computational security"; "UC-secure components
  compose regardless of shared setup"; "the probe's toy pad models a real cipher".

## Evidence

Observed on 2026-11-19. Repository heads were resolved with `git ls-remote <url> HEAD` on that
date and files were read at those revisions.

Source (repository @ revision: path):

- `EasyCrypt/easycrypt` @ `ce19cb6cbab4951e58553c36128e8a19f2f90c6a`:
  `theories/encryption/Hybrid.ec` (header comment lines 13–40; `Hybrid` line 412; `Hybrid_restr`
  line 594; `Hybrid_restr_div` line 646); `README.md` (purpose; Why3 and SMT solver dependency).
- `easyuc/EasyUC` @ `3a39ffef812c5ef6a57a2bf6148488a0facd4f03`: `README.md`; top-level `smc/`,
  `uc-dsl/`.
- `SSProve/ssprove` @ `9a37fe0ab79d041f8d835e6cf18e37614b16a791`:
  `theories/Crypt/package/pkg_advantage.v` (lines 70–97, 123–130, 142–166, 188–195); `README.md`
  (package laws, `security_based_on_prf`, section "Axioms").
- `isabelle-prover/mirror-afp-devel` @ `773174513872254f8efe1cb3a3ce64037f0b1da6`:
  `thys/CryptHOL/ROOT`; `thys/Constructive_Cryptography/Constructive_Cryptography.thy`
  (definition line 7; locale lines 9–26; `composability` line 155; `parallel_constructive_security`
  line 382).
- `secure-foundations/owl` @ `1b56f8cc70a067721917b9ccb60430417ada68f0`: `README.md`; `wg/`, `hpke/`,
  `extraction/`.
- `AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc` (`VERSION`: `version=3.18`):
  `driver/Compiler.v` lines 446–449, 466–472; `driver/Complements.v` lines 31–35, 45–49, 58–70,
  130–164; `common/Behaviors.v` lines 41–45, 81–82; `common/Events.v` lines 64–68;
  `common/Smallstep.v` lines 1058–1070, 1274–1278, 1289–1317; `common/Determinism.v` lines 25–42,
  195–205, 509–522; `x86/Asm.v` line 1179.
- `jasmin-lang/jasmin` @ `5741d17e3134f5b3b110e5e53494704d6d54f7c7`: `proofs/lang/syscall.v` lines
  11–12, 40–42; `proofs/lang/it_sems_core.v` line 31 (`Record fstate := { fscs; fmem; fvals }`);
  `proofs/lang/relational_logic.v` lines 222–226; `proofs/lang/core_logics.v` lines 301–306;
  `proofs/itrees/xrutt.v` header; `proofs/compiler/it_compiler_proof.v` lines 1552–1590.
- `logsem/clutch` @ `cc81450edd699bfcd9fa806d628a57d16c48f75d`: `README.md` (publication list;
  Rocq 9.1.1, Iris 4.5.0).

Papers (bibliographic data confirmed against Crossref or arXiv records on the observation date):

- Abadi, Rogaway. J. Cryptology 15(2):103–127, 2002. doi:10.1007/s00145-001-0014-7 (Sections 3,
  4.2, 4.3, Theorem 1 and the concrete-security paragraph following its proof).
- Canetti. Universally Composable Security. J. ACM 67(5), 2020. doi:10.1145/3402457; conference
  version FOCS 2001, doi:10.1109/SFCS.2001.959888 (abstract only).
- Barbosa, Barthe, Grégoire, Koutsos, Strub. CCS 2021. doi:10.1145/3460120.3484548 (journal
  version read: Sections 1 and 6).
- Canetti, Stoughton, Varia. EasyUC. CSF 2019. doi:10.1109/CSF.2019.00019 (abstract).
- Basin, Lochbihler, Sefidgar. CryptHOL. J. Cryptology 33(2):494–566, 2020.
  doi:10.1007/s00145-019-09341-z; Lochbihler, Sefidgar, Basin, Maurer. CSF 2019.
  doi:10.1109/CSF.2019.00018.
- Haselwarter et al. SSProve. TOPLAS 45(3), 2023. doi:10.1145/3594735; Brzuska et al. State
  Separation for Code-Based Game-Playing Proofs. ASIACRYPT 2018. doi:10.1007/978-3-030-03332-3_9.
- Gancher, Gibson, Singh, Dharanikota, Parno. Owl. IEEE S&P 2023.
  doi:10.1109/SP46215.2023.10179477 (Sections 1, 3.4, 4). Singh, Gancher, Parno. OwlC. USENIX
  Security 2025 (Sections 1–3).
- Patrignani, Künnemann, Wahby. arXiv:1910.08634v3 (Sections 2–4). Künnemann, Patrignani,
  Cecchetti. CSF 2024. doi:10.1109/CSF61375.2024.00024 (abstract).
- Clarkson, Schneider. Hyperproperties. J. Computer Security 18(6), 2010.
  doi:10.3233/JCS-2009-0393 (Section 2.6; Theorem 1).
- Leroy. CACM 52(7), 2009. doi:10.1145/1538788.1538814. Barthe et al. POPL 2020.
  doi:10.1145/3371075 (abstract).
- Adão, Bana, Herzog, Scedrov. ESORICS 2005. doi:10.1007/11555827_22. Black, Rogaway, Shrimpton.
  SAC 2002. doi:10.1007/3-540-36492-7_6. Boneh, Halevi, Hamburg, Ostrovsky. CRYPTO 2008.
  doi:10.1007/978-3-540-85174-5_7. Nielsen. CRYPTO 2002. doi:10.1007/3-540-45708-9_8. Backes,
  Pfitzmann. CSFW 2004. doi:10.1109/CSFW.2004.1310742. Micciancio, Warinschi. TCC 2004.
  doi:10.1007/978-3-540-24638-1_8. Backes, Pfitzmann, Waidner. CCS 2003.
  doi:10.1145/948109.948140. Canetti, Fischlin. CRYPTO 2001. doi:10.1007/3-540-44647-8_2. Canetti,
  Dodis, Pass, Walfish. TCC 2007. doi:10.1007/978-3-540-70936-7_4 (abstracts).
- Clutch family: POPL 2024 doi:10.1145/3632868; ICFP 2024 doi:10.1145/3674635; POPL 2025
  doi:10.1145/3704877 (abstracts).

Execution. Python 3.13, standard library only, about two seconds. Save the script as
`/tmp/cs_probe.py` and run `python3 /tmp/cs_probe.py`.

```python
from fractions import Fraction as Fr
from itertools import product
from math import comb, log2

def sd(d0, d1):   # statistical distance of two finite distributions
    return sum(abs(d0.get(x, Fr(0)) - d1.get(x, Fr(0))) for x in set(d0) | set(d1)) / 2

def dist(samples):
    out = {}
    for x in samples:
        out[x] = out.get(x, Fr(0)) + Fr(1, len(samples))
    return out

def otp(k, m):                      # one-time pad on n-bit integers
    return (0, m ^ k)

def otp_leaky(k, m):                # identical to the pad unless the plaintext IS the key
    return (1, k) if m == k else (0, m ^ k)

def probe_a(n):
    keys, res = range(2 ** n), {}
    for name, enc in (("otp", otp), ("otp_leaky", otp_leaky)):
        per_msg = [dist([enc(k, m) for k in keys]) for m in keys]
        ind = max(sd(per_msg[m0], per_msg[m1]) for m0 in keys for m1 in range(m0))
        cyc = sd(dist([enc(k, k) for k in keys]), dist([enc(k, 0) for k in keys]))
        rec = Fr(sum(1 for k in keys if enc(k, k) == (1, k)), 2 ** n)
        res[name] = (ind, cyc, rec)
    return res

def probe_b(eps, n):
    p = Fr(1, 2) + eps              # real module: Bernoulli(1/2+eps); ideal: Bernoulli(1/2)
    biased = sum(comb(n, k) * abs(p ** k * (1 - p) ** (n - k) - Fr(1, 2 ** n))
                 for k in range(n + 1)) / 2
    bad = 1 - (1 - eps) ** n        # real module raises a visible flag w.p. eps; ideal never
    return biased, bad, min(Fr(1), n * eps)

def probe_c():
    H = (0, 1)
    spec = {h: {0, 1} for h in H}   # specification: output ANY bit
    impl = {h: {h} for h in H}      # implementation: resolve the choice with the secret
    refines = all(impl[h] <= spec[h] for h in H)
    ni = lambda s: all(s[a] == s[b] for a in H for b in H)
    adv_spec = sd({0: Fr(1, 2), 1: Fr(1, 2)}, {0: Fr(1, 2), 1: Fr(1, 2)})
    adv_impl = sd({0: Fr(1)}, {1: Fr(1)})
    src = lambda c, h: c ^ h
    tgt = lambda c, h: (c | h) & (1 - (c & h))   # different code, same function
    equal = all(src(c, h) == tgt(c, h) for c, h in product(H, H))
    adv = lambda f: sd(dist([f(c, 0) for c in H]), dist([f(c, 1) for c in H]))
    return refines, ni(spec), ni(impl), adv_spec, adv_impl, equal, adv(src), adv(tgt)

print("A. scheme n  IND(key-indep)  SD({K}_K,{0}_K)  Pr[key recovered]")
for n in (2, 4, 6):
    for name, (ind, cyc, rec) in probe_a(n).items():
        print(f"   {name:9s} n={n}  {ind}  {cyc}  {rec}")
print("B. eps  n  SD(biased coins)  SD(bad events)  min(1,n*eps)  log2(n)")
for e in (Fr(1, 64), Fr(1, 1024)):
    for n in (1, 4, 16, 64, 256):
        b, bad, bound = probe_b(e, n)
        assert b <= bound and bad <= bound
        print(f"   1/{e.denominator} {n} {float(b):.6f} {float(bad):.6f} {float(bound):.6f} {log2(n):.0f}")
r = probe_c()
print(f"C. refines={r[0]} NI(spec)={r[1]} NI(impl)={r[2]} adv(spec)={r[3]} adv(impl)={r[4]}")
print(f"   equal-behaviour={r[5]} adv(src)={r[6]} adv(tgt)={r[7]}")
```

Observed output:

```text
A. scheme n  IND(key-indep)  SD({K}_K,{0}_K)  Pr[key recovered]
   otp       n=2  0  3/4  0
   otp_leaky n=2  1/4  3/4  1
   otp       n=4  0  15/16  0
   otp_leaky n=4  1/16  15/16  1
   otp       n=6  0  63/64  0
   otp_leaky n=6  1/64  63/64  1
B. eps  n  SD(biased coins)  SD(bad events)  min(1,n*eps)  log2(n)
   1/64 1 0.015625 0.015625 0.015625 0
   1/64 4 0.023796 0.061050 0.062500 2
   1/64 16 0.049748 0.222735 0.250000 4
   1/64 64 0.099882 0.635013 1.000000 6
   1/64 256 0.197260 0.982254 1.000000 8
   1/1024 1 0.000977 0.000977 0.000977 0
   1/1024 4 0.001466 0.003901 0.003906 2
   1/1024 16 0.003071 0.015511 0.015625 4
   1/1024 64 0.006215 0.060616 0.062500 6
   1/1024 256 0.012465 0.221294 0.250000 8
C. refines=True NI(spec)=True NI(impl)=False adv(spec)=0 adv(impl)=1
   equal-behaviour=True adv(src)=0 adv(tgt)=0
```

## Revalidation

- **Probe.** Re-run the script; the A and C lines are exact rationals and must match
  character for character; the B lines must match to six decimals.
- **ε algebra.** In SSProve, `grep -n "Lemma Advantage_" theories/Crypt/package/pkg_advantage.v`
  and confirm `Advantage_link` is an equality and `Advantage_triangle` an inequality with a sum.
  In EasyCrypt, `grep -n "lemma Hybrid_restr" theories/encryption/Hybrid.ec` and confirm the
  factor `q%r`. A changed statement shape (for example an inequality replacing the equality)
  changes the ledger rules of Section 6.
- **Compiler statements.** In CompCert, diff `driver/Complements.v` around
  `transf_c_program_preserves_spec` and `transf_cstrategy_program_preservation`, and check that
  `specification` is still `program_behavior -> Prop`. In Jasmin,
  `grep -n "fscs) = " proofs/compiler/it_compiler_proof.v` must still show the randomness-state
  equality in both the pre- and postcondition of the top-level theorems, and
  `grep -n "get_random" proofs/lang/syscall.v` must still show randomness as a function of the
  system-call state. If either conjunct disappears, condition 3 of Section 8 no longer follows
  from the compiler theorem.
- **Tool limits.** For Owl, search the current paper or documentation for "static corruptions",
  "asymptotic" and "key cycles"; for OwlC, re-read the trusted-computing-base paragraph. For the
  constructive-cryptography locale, check whether `negligible` has been replaced by a concrete
  bound.
- **Literature-level claims** (KDM independence from CCA-2, non-committing encryption,
  computational robust compilation) have no cheap probe; re-read the cited abstracts or full
  texts. A mechanized version of the Section 8 bridge lemma, if one appears, should replace the
  derived argument and its conditions.
