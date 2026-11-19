# Cryptographic protocol synthesis, MPC compilers and information-flow labels: Viaduct, Owl/OwlC, Wysteria/Symphony, and under-constrained ZK circuits

## Summary

Four compiler families turn a single high-level program into code for mutually
distrusting parties. They differ in *what the type system tracks* and in *which
link of the chain from source program to executable cryptography is actually
proved*:

- **Viaduct** infers a confidentiality/integrity label for every value and
  assigns each computation to a back-end protocol (cleartext on one host,
  replication, commitment, zero-knowledge proof, or two-party MPC) whose
  declared *authority label* acts for the value's label; among admissible
  assignments an SMT optimizer minimizes a static cost model. The adversary
  model is not a compiler switch: semi-honest MPC becomes admissible only when
  the program declares that the hosts trust each other for integrity. A model
  transcribed from the pinned source shows the two-party MPC back end can hold
  a joint secret `{alice & bob}` only under that mutual-trust assumption.
- **Owl** types protocol code with name-based secrecy labels and refinement
  types and has a paper proof that well-typed protocols are simulatable in the
  computational model (static corruption only). **OwlC** compiles Owl
  protocols to Rust verified with Verus against an interaction-tree
  specification; secrets live in an opaque buffer type whose only exits are
  token-guarded declassifying operations.
- **Wysteria** and **Symphony** make party sets and shares language values and
  prove that a single-threaded reading of the program corresponds to its
  distributed execution. Symphony is dynamically typed: coordination errors
  are detected at run time, and the theorem says the single-threaded run
  detects them exactly when the distributed run does.
- **Circuit languages for zero-knowledge proofs** (Circom, Noir, Halo2) split
  every program into a *witness generator* and a *constraint system*. The
  verifier only ever checks the constraints, so any value the constraints do
  not pin down is chosen by the prover. Three canonical instances are
  reproduced here with exact arithmetic: a dropped constraint after a hint, a
  non-unique 254-bit decomposition over the BN254 scalar field (32.25% of
  field elements have two), and a comparison gadget applied to inputs that
  were never range-checked.

No artifact examined here mechanically connects an ideal functionality (or a
label policy) to the executable cryptographic back end that implements it;
each system stops at a clearly identifiable trusted seam, tabulated under
Findings.

## Applicability

The subjects in `REPORT.json` are examined as a *comparison*, not as a
combined system. They fall into four groups:

| Group | Subjects | How examined |
|---|---|---|
| Label-directed protocol selection | `apl-cornell/viaduct` at `34b7a4df04ca7230abf62ad9f3abd17092a74d5c`; the PLDI 2021 paper (technical report, ePrint 2021/468); the later compiler-security proof (arXiv 2401.04131v1) | source inspection; paper text; an executable model of the label lattice |
| Security-typed protocol code | `secure-foundations/owl` at `1b56f8cc70a067721917b9ccb60430417ada68f0`; Owl (IEEE S&P 2023, ePrint 2023/473); OwlC (USENIX Security 2025, ePrint 2025/1092) | README, extraction library source, paper text |
| First-class parties and shares | Wysteria (IEEE S&P 2014); Symphony (‹Programming› 2023, arXiv 2302.10076v1); `plum-umd/symphony-lang` at `4396e5fb45c57bf7a045c2d00fd53108744caa5c` | paper text; source and example programs |
| Zero-knowledge circuit front ends | `iden3/circom` at `9b4b23331644e17868c90a85768826ed3bcba59f`; `iden3/circomlib` at `8852c3bc91e3ede890f2143f36457b25302abce2`; `noir-lang/noir` at `af5d97aaa0f67fde5da9a7a790968b88cffff439`; `zcash/halo2` at `7465edf9110aace00b8c24b96270e1b820fd39fb`; `trailofbits/circomspect` at `50010b623ed4f3bff9d1b0363cfe952385b47af3`; `Veridise/Picus` at `138b151d3a388e5b6c040c163e0a1db04f2ceda6`; `0xPARC/zk-bug-tracker` at `56a996672fb50486279126c8e12530f2bf933d0b`; the QED² paper (PLDI 2023) and the SNARK-vulnerability SoK (arXiv 2402.15293v4) | documentation and source at the pinned revisions; an executable model of three circomlib templates |

Scope conditions that materially limit the findings:

- **Nothing was built or run from the subject repositories.** No Viaduct,
  Owl, Symphony, Circom, Noir or Halo2 toolchain was executed. Every
  `Basis: execution` finding refers to a standard-library Python model whose
  complete source is reproduced under Evidence. A model establishes what the
  transcribed definitions imply, not what a compiler binary does.
- Viaduct statements describe the pinned `master` revision, whose surface
  syntax (`host alice`, `assume for <- alice trusts bob`) differs from the
  2021 paper's figures. Paper-only constructs are marked as such.
- Owl statements describe the pinned `main` revision; the README states that
  language, verifier and compiler "are all subject to change". The S&P 2023
  and USENIX Security 2025 artifacts are separate archived snapshots and were
  not examined.
- The circuit findings concern R1CS-style constraint systems over a prime
  field. The executable model uses the BN254 scalar field order
  `21888242871839275222246405745257275088548364400416034343698204186575808495617`
  (Circom's default prime, option `bn128`) and small primes for exhaustive
  enumeration. Aliasing counts are specific to that modulus.
- Constant-time compilation, oblivious RAM, and trusted-execution back ends
  are outside this report.

## Findings

### 1. Viaduct: labels, protocol authority, and selection

#### 1.1 Label algebra

Basis: source (`compiler/src/main/kotlin/io/github/aplcornell/viaduct/security/{SecurityLattice,Label,LabelExpression}.kt`).

A label is a pair `(C, I)` of elements of the free distributive lattice
generated by per-host atoms: a *confidentiality* atom `h→` and an *integrity*
atom `h←` for every host `h`. The underlying order `p ≤ q` reads "principal
`p` is at least as strong as `q`" (`p` acts for `q`); `∧` (lattice meet) is
therefore the stronger conjunction and `∨` (join) the weaker disjunction. The
weakest principal is the lattice top, written `⊤w` below.

```text
join(l1, l2)        = (C1 ∧ C2 , I1 ∨ I2)     information-flow least upper bound   surface: ⊔
meet(l1, l2)        = (C1 ∨ C2 , I1 ∧ I2)                                          surface: ⊓
and (l1, l2)        = (C1 ∧ C2 , I1 ∧ I2)     combined authority                   surface: &
or  (l1, l2)        = (C1 ∨ C2 , I1 ∨ I2)                                          surface: |
confidentiality(l)  = (C , ⊤w)                                                     surface: l->
integrity(l)        = (⊤w , I)                                                     surface: l<-
swap(l)             = (I , C)
flowsTo(l1, l2)   <=>  C2 ≤ C1  and  I1 ≤ I2
actsFor(l1, l2)   <=>  C1 ≤ C2  and  I1 ≤ I2
label of host h     = (h→ , h←)
```

Both relations are decided modulo a set of hypotheses (a lattice congruence)
assembled from the program text:

- for **every** declared host `h`, the built-in axiom `h← ≤ h→` (whoever
  controls a host's integrity can also read its secrets);
- for each delegation `assume for <- x trusts y`, the inequality `y← ≤ x←`
  (the grammar's `for ->` projection yields `y→ ≤ x→`, and a delegation with
  no projection yields both).  Source: `parsing/Parser.cup` (`projection`
  production) and `syntax/intermediate/TopLevelDeclarations.kt`.

The implementation keeps lattice elements in join-of-meets normal form and
decides `≤` by forward-chaining applicable hypotheses over each meet
(`algebra/FreeDistributiveLattice.kt`, `lessThanOrEqualTo`).

#### 1.2 Authority declared by each back end

Basis: source (the `authority()` override of each protocol class).

| Protocol constructor | `authority()` as written | Normal form `(C ; I)` for hosts `a`, `b` |
|---|---|---|
| `Local(a)` | `host.label` | `(a→ ; a←)` |
| `Replication({a,b})` | `hosts.map { it.label }.reduce(Label::meet)` | `(a→ ∨ b→ ; a← ∧ b←)` |
| `Commitment(sender a, receivers {b})` | `cleartextHost.label and` each `hashHost.label.integrity()` | `(a→ ; a← ∧ b←)` |
| `ZKP(prover a, verifiers {b})` | `prover.label and` each `verifier.label.integrity()` | `(a→ ; a← ∧ b←)` |
| `ArithABY` / `BoolABY` / `YaoABY (server a, client b)` | `combined = server.label join client.label; combined meet combined.integrity().swap()` | `((a→ ∧ b→) ∨ a← ∨ b← ; a← ∨ b←)` |

The ABY line carries the source comment "We limit confidentiality by
integrity since ABY provides semi-honest security": the secret is lost if the
attacker controls *both* confidentialities **or either host's integrity**,
and the result is only as trustworthy as the weaker host. This matches the
technical report's `SH-MPC(H)` description. The report additionally defines a
maliciously secure `MAL-MPC(H)` with label `∧ L(h)`; the pinned repository's
`backends/` directory contains only `aby`, `cleartext`, `commitment` and
`zkp`, i.e. no malicious-MPC back end is present at that revision.

#### 1.3 Selection is filtering by authority, then cost minimization

Basis: source (`selection/SelectionConstraintGenerator.kt`, `selection/Z3SelectionProblemSolver.kt`, `backends/aby/ABYProtocolFactory.kt`).

```text
viableProtocols(node):
    required := informationFlowAnalysis.label(node)
    if node has an explicit protocol annotation P:
        if not actsFor(P.authority(), required): raise InvalidProtocolAnnotationError
        return {P}
    S := { P in protocolFactory.viableProtocols(node) | actsFor(P.authority(), required) }
    if S is empty: raise NoApplicableProtocolError
    return S
```

`protocolFactory.viableProtocols` encodes *capability* only (for example the
ABY factory excludes `ArithABY` for comparison, logical, `Not`, `Mux`,
`Maximum`, `Minimum` and `Division` operators). The remaining choice is
encoded as integer constraints with one variable per program variable and
solved with Z3's optimizer (`ctx.mkOptimize()`, `MkMinimize(costExpr)`).

#### 1.4 The cost model is a table of small integers

Basis: source (`selection/SimpleCostEstimator.kt`).

Cost is a vector over four features, combined by a weighted sum:

| Feature | LAN weight | WAN weight | Meaning in source comments |
|---|---|---|---|
| `numberOfMessages` | 3 | 5 | messages between hosts |
| `executionCost` | 1 | 1 | per-statement base cost |
| `lan` | 1 | 0 | per-operator MPC cost, low latency |
| `wan` | 0 | 1 | per-operator MPC cost, high latency |

Per-statement base cost: `Local` 1; `Replication` number of hosts;
`Commitment` 20 + receivers; `ZKP` 50 + verifiers; any `ABY` 100. MPC
operators add a `(lan, wan)` pair looked up in the table the estimator
actually indexes (`mpcOperationCostMap3`, commented "from my own
estimation"; two other tables, one attributed to Table 2 of Ishaq et al.,
CCS 2019, and one to the original ABY paper, remain in the file but are not
consulted):

| Operator | ArithABY | BoolABY | YaoABY |
|---|---|---|---|
| add | (4, 5) | (24, 31) | (17, 15) |
| subtract / negate | (5, 5) | (60, 92) | (16, 15) |
| multiply | (17, 15) | (80, 102) | (46, 15) |
| divide | not applicable | (378, 552) | (130, 17) |
| equal | not applicable | (25, 26) | (18, 15) |
| less-than | not applicable | (26, 26) | (18, 15) |
| mux | not applicable | (14, 10) | (9, 10) |

Share conversions (`abyConversionCostMap3`): A→B (19, 15), A→Y (18, 15),
B→A (15, 15), B→Y (16, 15), Y→A (15, 15), Y→B (5, 5). The library entry point
defaults to the WAN regime (`passes/Compilation.kt`).

Consequences (Basis: derived from the tables). Arithmetic sharing has the
lowest entry for add, subtract and multiply in both regimes and has no entry
for division, comparison or mux, so a program that mixes arithmetic with
comparison pays at least one conversion (15–19 units, except Y→B at 5).
Between the two circuit sharings, Yao has the lower entry for every
arithmetic and comparison operator listed above in both columns; the file's
entries for AND, OR and NOT (Boolean (20, 15), (35, 30), (5, 5) against Yao
(22, 15), (40, 30), (6, 5)) favour Boolean sharing only under LAN weights.
The LAN/WAN switch therefore acts mainly through the message-count weight
(3 against 5) and the choice of column. The 2021 paper states that more
sophisticated ABY cost reasoning from prior work was left as future work;
these integers are a heuristic, not a measured model.

#### 1.5 Downgrades are checked for non-malleability

Basis: source (`analysis/InformationFlowAnalysis.kt`, the `DeclassificationNode`/`EndorsementNode` case).

For `declassify e to L'` / `endorse e to L' from L` the analysis emits, among
others, `flowsTo(from, swap(from))` and `flowsTo(to, swap(to))`; failure
raises `MalleableDowngradeError`. Unfolding the definitions, `l flowsTo
swap(l)` is exactly `I(l) ≤ C(l)`: a value may be downgraded only if it is at
least as trusted as it is secret. Declassification must not change integrity
and endorsement must not change confidentiality
(`IntegrityChangingDeclassificationError`,
`ConfidentialityChangingEndorsementError`). `SecurityLattice.swap` cites
nonmalleable information flow control (Cecchetti, Myers, Arden, CCS 2017) as
the property being enforced.

#### 1.6 Executable model: which protocol can hold which label

Basis: execution of a model transcribed from the definitions in 1.1–1.2
(source: Evidence, `viaduct_authority_model.py`); not a run of the compiler.

```text
== no delegation (malicious) ==
protocol authority actsFor ->           {alice}             {bob}     {alice | bob}   {alice & bob<-}     {alice & bob}
Local(alice)                               yes                 -               yes                 -                 -
Local(bob)                                   -               yes               yes                 -                 -
Replication{alice,bob}                       -                 -               yes                 -                 -
Commitment(alice;bob)                      yes                 -               yes               yes                 -
ZKP(alice;bob)                             yes                 -               yes               yes                 -
ABY(alice,bob)                               -                 -               yes                 -                 -
  ({alice} join {bob}) flowsTo {alice & bob}: False
  downgrade source {alice & bob}        nonmalleable (l flowsTo swap(l)): True
  downgrade source {alice} join {bob}   nonmalleable (l flowsTo swap(l)): False

== mutual integrity trust (semi-honest) ==
protocol authority actsFor ->           {alice}             {bob}     {alice | bob}   {alice & bob<-}     {alice & bob}
Local(alice)                               yes                 -               yes               yes                 -
Local(bob)                                   -               yes               yes                 -                 -
Replication{alice,bob}                       -                 -               yes                 -                 -
Commitment(alice;bob)                      yes                 -               yes               yes                 -
ZKP(alice;bob)                             yes                 -               yes               yes                 -
ABY(alice,bob)                             yes               yes               yes               yes               yes
  ({alice} join {bob}) flowsTo {alice & bob}: True
  downgrade source {alice & bob}        nonmalleable (l flowsTo swap(l)): True
  downgrade source {alice} join {bob}   nonmalleable (l flowsTo swap(l)): True
```

Reading the table:

- The comparison `a <= b` with `a : {alice}`, `b : {bob}` has label
  `{alice} ⊔ {bob} = (a→ ∧ b→ ; a← ∨ b←)`. Storing it in a variable of label
  `{alice & bob}` — as the repository's `Millionaires.via` test does — is a
  legal flow **only** with the two `assume for <-` lines; without them the
  flow condition fails, so the model predicts a label error before protocol
  selection is reached.
- With mutual integrity trust, `ABY(alice,bob)` is the *only* protocol in the
  table that acts for `{alice & bob}`; without it, ABY acts for nothing more
  secret than `{alice | bob}` (data both hosts may already read). This is the
  executable form of the technical report's sentence that the label of
  `SH-MPC(alice, bob)` is `A ∧ B` when both hosts have integrity
  `(A ∧ B)←` and is `A ∨ B` otherwise.
- In the malicious configuration, `{alice & bob<-}` (Alice's secret that Bob
  must be able to rely on — the label of `a_min` in the repository's
  `HistoricalMillionaires.via` benchmark) is covered by `Commitment` and
  `ZKP` but not by `Local(alice)`; under mutual trust `Local(alice)` suffices.
  Commitments and proofs are thus selected *because* integrity trust is
  absent, not because the programmer asked for them.
- A value of label `{alice} ⊔ {bob}` is a non-malleable downgrade source only
  under mutual trust.

#### 1.7 What is proved about the compiler

Basis: documentation (paper texts).

- The PLDI 2021 paper presents the compiler, runtime and evaluation; its
  conclusion calls "a full correctness proof for the Viaduct compiler" a
  future "significant research achievement".
- "Secure Synthesis of Distributed Cryptographic Applications" (Acay,
  Gancher, Recto, Myers; arXiv 2401.04131v1) proves security for a compiler
  *model* covering multiple mechanisms, malicious corruption and asynchronous
  communication, by combining simulation-based security, information-flow
  control, choreographic programming and sequentialization. The abstract
  states the proof "targets hybrid protocols, which abstract cryptographic
  mechanisms as idealized functionalities" and yields robust hyperproperty
  preservation; instantiating the functionalities is left to Universal
  Composability.
- The PLDI paper therefore contains no compiler-correctness proof, and the
  later report's abstract describes a proof about hybrid protocols without
  mentioning mechanization. Neither statement is about the Kotlin
  implementation, its cost tables, or its ABY and libsnark bindings.

### 2. Owl and OwlC: labels for protocol secrets, and a verified Rust back end

#### 2.1 Owl's type discipline

Basis: documentation (S&P 2023 paper) + source (example protocols under `tests/success/`).

| Concept | Form | Meaning |
|---|---|---|
| Name | `name k : enckey t @ alice` | a cryptographic secret with a *name type* (those occurring in the pinned tests: `nonce`, `enckey t`, `DH`, `kdfkey`, `pkekey`, `sigkey`, `st_aead`, `mackey`) owned by a locality |
| Label | `[n]`, `l1 /\ l2`, `adv` | atomic label of name `n`; conjunction; the adversary's label |
| Corruption | `n` is corrupt iff `[n] ≤ adv` | corruption is per *name*, not per party, and is hierarchical: corrupting `k : enckey t` corrupts everything in `t` |
| Secrecy | every network output must have label `adv` | outputs carry no more than the adversary already knows |
| Integrity | refinement types, e.g. `x:Result{... ==> happened(bob_main())}` | facts that hold "with high probability" unless a relevant name is corrupt |
| Case split | `corr_case n in ...` / conditional types `if sec(k) then T else Data<adv>` | the checker types the body once per corruption scenario |

Decryption illustrates the interplay (rule sketched in the pinned
`tests/success/encrypted_key.owl`): with `k : enckey t` and ciphertext
`c : adv`, `adec(k, c) : option t` if `[k] ≰ adv`, and `option adv` if
`[k] ≤ adv`.

Guarantee and limits, as the paper states them: well-typed protocols satisfy
**simulatability** (running the protocol leaks no more to an adversary
corrupting a chosen set of names than it knew beforehand) and **correctness**
(all refinements hold with high probability), proved on paper for a core
calculus `OwlLang` with symmetric/asymmetric primitives, Diffie–Hellman and
random-oracle hashing. Stated limitations: static corruption only; no
unlinkability properties or injective correspondences; and the 2023
extraction mechanism was "not yet verified for functional correctness or
security".

#### 2.2 OwlC: what the compiled artifact is

Basis: source (`extraction/src/{speclib,execlib}.rs`, `extraction/Cargo.toml`, `README.md`) + documentation (USENIX Security 2025 paper).

`owl --extract protocol.owl` emits Rust to be verified by Verus (the README
names Verus release `0.2026.09.06.8dea4a2`, Rust toolchain `1.98.0`). The
generated code is checked against a specification written as an interaction
tree:

```rust
pub enum DeclassifyingOp {
    ControlFlow (Seq<u8>),
    EnumParse   (Seq<u8>),
    EqCheck     (Seq<u8>, Seq<u8>),
    ADec        (Seq<u8>, Seq<u8>),                     // key, ctxt
    StAeadDec   (Seq<u8>, Seq<u8>, Seq<u8>, Seq<u8>),   // key, ctxt, aad, nonce
    SigVrfy     (Seq<u8>, Seq<u8>, Seq<u8>),            // pubkey, msg, signature
    MacVrfy     (Seq<u8>, Seq<u8>, Seq<u8>),            // mackey, msg, mac
    PkDec       (Seq<u8>, Seq<u8>),                     // key, ctxt
}
pub enum ITree<A, Endpoint> {
    Input       (spec_fn(Seq<u8>, Endpoint) -> ITree<A, Endpoint>),
    Output      (Seq<u8>, Option<Endpoint>, Box<ITree<A, Endpoint>>),
    Sample      (usize, spec_fn(Seq<u8>) -> ITree<A, Endpoint>),
    Declassify  (DeclassifyingOp, Box<ITree<A, Endpoint>>),
    Ret         (A),
}
```

Executable code may perform network input/output, sampling and
declassification only as the tree dictates; the paper describes this as
"higher-order ghost linear tokens enforcing permissions to perform effects".
The paper notes the Verus trees are inductive, so they describe terminating
computations only.

Secrets are held in `SecretBuf<'a>`, a wrapper around a byte buffer whose
public interface offers length, sub-ranging, concatenation and re-borrowing
but no byte access. The exits are:

| Exit from `SecretBuf` | Precondition | Verifier status |
|---|---|---|
| `declassify(&self, Tracked(t))` | token `t` views as `DeclassifyingOp::ControlFlow(b)` with `b == self.view()` | `#[verifier::external_body]` |
| `declassify_first_byte` | token is `EnumParse(b)` with `b == self.view()` | `external_body` |
| `secret_eq(&self, other, Tracked(t))` | token is `EqCheck(l, r)` matching the operands; body folds `acc \| (x ^ y)` over all bytes | `external_body` |
| `owl_dec`, `owl_vrfy`, `owl_mac_vrfy`, `owl_pkdec`, `owl_dec_st_aead` | matching `ADec` / `SigVrfy` / `MacVrfy` / `PkDec` / `StAeadDec` token | wrappers over the crypto provider |
| `expose_to_application(&self) -> &[u8]` | `requires false` ("For unverified application code only") | callable only from unverified code |
| `private_as_slice` | module-private | feeds the crypto provider inside module `secret` |

At the pinned revision `execlib.rs` contains 35 `external_body` attributes;
wire formats are handled through the `vest_lib` parser-combinator crate
(`=0.2.1`), and primitives come from `libcrux` at a pinned git revision plus
RustCrypto crates.

#### 2.3 Trusted computing base

Basis: documentation (OwlC paper, "Limitations" and "Trusted Computing Base").

| Trusted | Stated by the paper |
|---|---|
| Owl's soundness theorem | "OwlC's guarantees rely on the correctness of the underlying tools, namely Owl, Verus, and Rust" |
| Specification compiler (Owl → interaction tree) | "We trust the correctness of the simple specification compiler" |
| Cryptographic library binding | "we axiomatize the connection between OwlC's output and this library" |
| Constant-time behaviour of the secret type | "we trust that our secret type is implemented in constant time" |
| Compilation below Rust source | "we do not provide assembly- or hardware-level guarantees since we use stock rustc"; microarchitectural channels "are out of scope" |

The adversary considered at the Rust level may call API functions in
type-safe ways, deliver network messages, and observe timing and memory
access patterns.

### 3. Wysteria and Symphony: parties and shares as values

Basis: documentation (paper texts) + source (`plum-umd/symphony-lang`, `src/lib/common/Symphony/Lang/Syntax.hs`, `res/Programming23/symphony/*.sym`).

| | Wysteria (2014) | Symphony (2023) |
|---|---|---|
| Program shape | mixed-mode: per-party local blocks plus `sec` blocks run as secure computations | one program; `par P e` runs `e` at party set `P` |
| Party sets | static; refinement and dependent types mention principals | first-class run-time values (`{A,B}` can be computed, pattern-matched, passed) |
| Per-party data | *wire bundles* `W w τ` mapping each principal to its own value | bundles `⟪ ρ \| v ⟫ ⧺ ...` |
| Shares | built-in share type `Sh w τ` | first-class; `share [φ, τ : P → Q] e`, `reveal [φ, τ : P → Q] e`; may be re-shared and delegated |
| Typing | static refinement type system; type soundness proved | dynamically typed; errors surface at run time |
| Metatheory | simulation theorem from single-threaded to multi-threaded semantics; soundness implies data is revealed only through agreed secure computations | three theorems: termination coincides (hence no deadlock), and run-time errors are detected in the single-threaded run iff some party detects them in the distributed run |
| Protocols | circuits executed by an underlying engine (GMW in the paper's implementation) | `data Prot = RepP \| YaoP \| GmwP` (replicated, Yao, GMW) at the pinned revision |

A complete Symphony program from the pinned repository
(`res/Programming23/symphony/gcd.sym`) shows share placement as an explicit,
typed coercion between party sets:

```text
principal A B

def sec gcd (a, b) =
  mux if (a == 0) then b
  else gcd (b % a, a)

def main () = par {A,B}
  let inputA = par {A} 102334155 in
  let inputB = par {B} 165580141 in
  let shareA = share [gmw, ℤ : {A} → {A,B}] inputA in
  let shareB = share [gmw, ℤ : {B} → {A,B}] inputB in
  reveal [gmw, ℤ : {A,B} → {A}] (bnd_rec gcd (const 0) 45n (shareA, shareB))
```

Two structural facts follow from the text of the example (Basis: derived):
a secret-dependent conditional is written `mux if`, i.e. both arms are
evaluated; and recursion over secret data needs a public bound (`bnd_rec ...
45n`). The Symphony paper states that a static type system preventing all
failures "would be very challenging, and so remains future work", and that
Wysteria's party sets "can always be resolved statically when given a whole
program" and its shares "cannot be re-shared to different parties".

Neither language tracks *integrity* in types (Basis: derived): in Symphony
the protocol tag of a `share` expression, and in Wysteria the choice of
secure-computation engine, fixes the adversary model implicitly.

### 4. Zero-knowledge circuit languages: the witness/constraint split

#### 4.1 The obligation

A circuit defines a relation `C(x, y, w)` over public inputs `x`, outputs `y`
and private intermediates `w`. A proof convinces the verifier that *some* `w`
satisfies `C`. The front end additionally contains a witness generator `G`
computing `(y, w)` from the inputs. Two different properties are needed:

```text
completeness of G :  for all x.  C(x, G(x))
output determinism:  for all x, y, y', w, w'.  C(x, y, w) and C(x, y', w')  implies  y = y'
```

Only `C` reaches the verifier. If output determinism fails, a prover can
substitute its own `(y', w')` for `G(x)` and prove a false statement about
`y'`. Determinism of *outputs* is the property the QED² tool decides ("prove
whether or not each signal is uniquely determined by the input"); uniqueness
of the *whole witness* is neither required nor typical (see 4.5, `inv`).

#### 4.2 Circom

Basis: documentation (`mkdocs/docs/circom-language/{signals,constraint-generation,basic-operators}.md`, `code-quality/inspect.md`).

| Operator | Witness code | Constraint | Documentation's verdict |
|---|---|---|---|
| `a <== e` / `e ==> a` | assigns | adds `a === e` | "The safe options" |
| `a <-- e` / `e --> a` | assigns | none | "considered dangerous"; "it is crucial to add other constraints" |
| `e1 === e2` | adds an assert (omitted with `--sanity_check 0`) | adds the constraint | — |
| `var v = e` | compile-time/witness variable | none | not a signal |

Constraints must be quadratic, `A*B + C = 0` with `A`, `B`, `C` linear in
the signals; a non-quadratic `<==` is rejected ("Non quadratic constraints
are not allowed!"). Since 2.0.8 the compiler warns when `<--` is given an
expression that *is* quadratic. `--inspect` reports signals that appear in no
constraint of their template instance (warning `CA01`) and subcomponent
signals unused by the parent, with `_ <== s` as the explicit opt-out. Signal
*tags* (2.1.0, e.g. `signal input {binary} in[n]`) let a template state an
assumed invariant on an input. Outputs of the main component are always
public; inputs are private unless listed in `{public [...]}`.

#### 4.3 Noir

Basis: documentation (`docs/docs/language/unconstrained.md`) + source (`compiler/noirc_evaluator/src/ssa/checks/`).

An `unconstrained fn` compiles to Brillig bytecode executed by the prover
outside the circuit. Calling one from constrained code requires an
`unsafe { ... }` block, and the compiler warns unless a `// Safety:` comment
accompanies it. Two SSA checks report "bugs":

- *independent subgraph detection* (`check_for_underconstrained_values.rs`) —
  values that neither derive from inputs nor reach outputs; disabled with
  `--skip-underconstrained-check`;
- *Brillig manual constraint coverage*
  (`check_for_missing_brillig_constraints.rs`) — every result of a Brillig
  call must have a descendant that appears in an assertion whose other side
  has an ancestor among the call's arguments (or is a constant).

Basis: derived. The coverage check is an ancestry (connectivity) criterion,
not a determinism proof. The documentation's own passing example,
`assert(factored[0] * factored[1] == foo)`, connects both results to the
argument yet leaves the factorization free (`[1, foo]`, `[foo, 1]`, ...). The
check finds *forgotten* constraints; it cannot find *insufficient* ones.

#### 4.4 Halo2

Basis: documentation (`book/src/concepts/arithmetization.md`, `book/src/user/dev-tools.md`) + source (`halo2_proofs/src/dev/failure.rs`).

A PLONKish circuit is a matrix of field cells with *fixed*, *advice*
(witness) and *instance* (public) columns; polynomial constraints that must
vanish on every row, typically gated by selector columns (`q_i · p(...) =
0`); equality (copy) constraints between cells; and lookup arguments.
Assigning an advice cell is the analogue of Circom's `<--`: it constrains
nothing unless a gate with an enabled selector, a copy constraint or a
lookup mentions the cell. `MockProver::run` "will test every constraint in
the circuit directly" for the supplied witness; its `VerifyFailure` variants
are `CellNotAssigned`, `InstanceCellNotAssigned`, `ConstraintNotSatisfied`,
`ConstraintPoisoned` ("active on an unusable row, and is likely missing a
selector"), `Lookup` and `Permutation`.

Basis: derived. Every one of those variants reports a constraint that the
*given* witness violates. A missing constraint violates nothing, so a passing
`MockProver` run is evidence of completeness for that witness only and says
nothing about determinism.

#### 4.5 Three hazards, executed

Basis: execution (source and command under Evidence, `r1cs_underconstraint_probe.py`), modelling these templates from `iden3/circomlib` at the pinned revision:

```text
template IsZero() {                       template Num2Bits(n) {
    signal input in;                          signal input in;
    signal output out;                        signal output out[n];
    signal inv;                               var lc1=0;
    inv <-- in!=0 ? 1/in : 0;                 var e2=1;
    out <== -in*inv +1;                       for (var i = 0; i<n; i++) {
    in*out === 0;                                 out[i] <-- (in >> i) & 1;
}                                                 out[i] * (out[i] -1 ) === 0;
                                                  lc1 += out[i] * e2;
template LessThan(n) {                            e2 = e2+e2;
    assert(n <= 252);                         }
    signal input in[2];                       lc1 === in;
    signal output out;                    }
    component n2b = Num2Bits(n+1);
    n2b.in <== in[0]+ (1<<n) - in[1];
    out <== 1-n2b.out[n];
}
```

```text
== Part 1: IsZero over F_97 (exhaustive) ==
[both constraints]
  output uniquely determined for every input: True
  the unique output equals (in == 0 ? 1 : 0):   True
  #outputs accepted for in=0: 1, for in=5: 1
  #witnesses (out,inv) for in=0: 97, for in=5: 1
[`in*out === 0` removed]
  output uniquely determined for every input: False
  the unique output equals (in == 0 ? 1 : 0):   False
  #outputs accepted for in=0: 1, for in=5: 97
  #witnesses (out,inv) for in=0: 97, for in=5: 97
  forged claim 'IsZero(5) = 1' satisfiable: True  (witness inv=0)
== Part 2: Num2Bits(254) aliasing over the BN254 scalar field ==
  p.bit_length() = 254,  2^254 > p: True
  field elements with two 254-bit decompositions: 2^254 - p = 7059779437489773633646340506914701874769131765994106666166191815402473914367
  fraction of the field: 0.322538
  x = 5
  canonical bits satisfy Num2Bits(254): True
  bits of x+p    satisfy Num2Bits(254): True
  the two bit vectors differ: True; LSB canonical=1, LSB alias=0
  AliasCheck on canonical: CompConstant(-1) satisfiable=True, out=0 -> `out === 0` holds
  AliasCheck on alias    : CompConstant(-1) satisfiable=True, out=1 -> `out === 0` FAILS
  CompConstant(-1) on bits(p-1): satisfiable=True, out=0
  CompConstant(-1) on bits(p (alias of 0)): satisfiable=True, out=1
  CompConstant(-1) on bits(2^254-1): satisfiable=True, out=1
== Part 3: LessThan(8) with inputs not range-checked to 8 bits ==
  [exhaustive, F_1009] #a with LessThan(8)(a, 10) = 1: 256; of these, integers a < 10: 10; false accepts: 246
  [exhaustive, F_1009] false accepts are exactly a in [763, 1008]: True
  [exhaustive, F_1009] correct on all 256x256 pairs of 8-bit inputs: True
  [BN254] honest   in=[3, 10]      -> out=1
  [BN254] honest   in=[10, 3]      -> out=0
  [BN254] attacker in=[p-100, 10]  -> out=1   (integer truth: p-100 < 10 is False)
  [BN254] attacker in=[10, p-100]  -> out=0   (integer truth: 10 < p-100 is True)
```

Interpretation:

1. **Hint without its second constraint (`IsZero`).** With both constraints
   the output is unique for every input over `F_97`, although the *witness*
   is not: for `in = 0` all 97 values of `inv` are accepted. Deleting
   `in*out === 0` leaves `out = 1 - in*inv` with `inv` free, so every one of
   the 97 outputs is accepted for a non-zero input; `IsZero(5) = 1` is proved
   with `inv = 0`. The honest witness generator still computes the right
   answer, so tests that only run the generator pass.
2. **Aliasing (`Num2Bits(254)`).** The BN254 scalar field order `p` has 254
   bits and `2^254 > p`, so `x` and `x + p` are both 254-bit integers
   congruent to `x`. Exactly `2^254 − p` field elements — 32.25% of the field
   — have two satisfying bit vectors, differing already in the least
   significant bit. `Num2Bits_strict` adds `AliasCheck`, i.e.
   `CompConstant(-1)` followed by `out === 0`; a direct port of
   `CompConstant` evaluates to 0 on the canonical bits (and on `p − 1`) and
   to 1 on the alias (and on `p`, and on `2^254 − 1`), so the strict template
   rejects the second representation.
3. **Unstated precondition (`LessThan(n)`).** The template is correct on all
   256 × 256 pairs of 8-bit inputs, but the input width is not enforced. For
   `b = 10`, 256 field elements `a` are accepted as "less than 10": the ten
   integers below 10 and the 246 elements `a ≡ 10 − d (mod q)` for
   `d = 11..256`, i.e. the top of the field. Over BN254, `a = p − 100` is
   accepted as less than 10. The algebra is general: the output is 1 exactly
   when `a − b + 2^n` reduces into `[0, 2^n)`, i.e. `a − b ∈ [−2^n, −1]`
   modulo the field order.

The upstream linter documentation describes all three as analysis passes
("Signal assignment", "Non-strict binary conversion", "Unconstrained
less-than"), and notes for the third that `p − 254` "is equal to −254 which
*is* less than two, so there is nothing wrong with the Circomlib `LessThan`
circuit" — the defect is the caller's missing range check.

#### 4.6 Prevalence and tooling

Basis: documentation (paper abstracts/tables and tool documentation at the pinned revisions).

- The SNARK-vulnerability SoK (Chaliasos et al., USENIX Security 2024)
  collected 141 vulnerabilities from 107 audit reports, 16 disclosures and
  bug trackers; 99 are circuit-layer issues, of which 95 are under-constrained,
  1 over-constrained and 3 computational/hint errors. By root cause, the 95
  under-constrained cases split into: wrong translation of logic into
  constraints 32, missing input constraints 25, assigned but not constrained
  14, unsafe reuse of circuit 9, arithmetic field errors 8, bad
  circuit/protocol design 4, and one each for incorrect custom gates,
  out-of-circuit computation, and other programming errors.
- QED² (Pailoor et al., PLDI 2023) combines SMT solving with lightweight
  uniqueness inference over the generated finite-field equations; on 163
  Circom circuits it "can successfully solve 70%" (proving output uniqueness
  or exhibiting two witnesses) and found 8 previously unknown
  vulnerabilities. `Veridise/Picus` describes itself as an implementation of
  QED² supporting Circom, R1CS and gnark targets.
- The pinned `0xPARC/zk-bug-tracker` catalogues 27 bugs "in the wild" and 8
  common vulnerability classes (under-constrained circuits, nondeterministic
  circuits, arithmetic over/underflows, mismatching bit lengths, unused
  public inputs optimized out, Frozen Heart, trusted setup leak, assigned but
  not constrained). It notes that not all nondeterminism is exploitable.

| Tool | Decides | Cannot decide |
|---|---|---|
| `circom --inspect` | a signal occurs in no constraint | whether the constraints it occurs in determine it |
| circomspect | syntactic patterns: `<--` with quadratic right-hand side, intermediate signal in a single constraint, `Num2Bits(n)` with `n` not provably below the prime size, `LessThan` inputs not provably range-checked | semantic determinism |
| Noir SSA checks | disconnected value subgraphs; Brillig results never related to arguments by an assertion | sufficiency of the assertion |
| Halo2 `MockProver` | the supplied witness satisfies gates, copies and lookups | existence of other satisfying witnesses |
| QED² / Picus | output uniqueness, by SMT plus inference | 30% of its own benchmark (per the abstract) |

### 5. Cross-system comparison

#### 5.1 What a label means, and what it selects

| System | What the label ranges over | How the adversary is expressed | What the label decides | Integrity tracked |
|---|---|---|---|---|
| Viaduct | hosts, as confidentiality and integrity principals in a free distributive lattice | trust delegations between hosts in the program text | which back-end protocol may execute each statement | yes, as a lattice component |
| Owl | cryptographic *names* (keys, nonces) | a static label `adv`: the set of corrupted names | whether a value may be output; which type a decryption/verification returns | via refinement types, per corruption case |
| Wysteria | principals in types of wire bundles and shares | implicit in the secure-computation engine | where code runs and who may see a value | no |
| Symphony | run-time party sets | implicit in the protocol tag of `share`/`reveal` | where code runs; which parties hold a share | no |
| Circom / Noir / Halo2 | nothing (optional tags or `unsafe` markers) | the prover is fully adversarial for every unconstrained value | nothing | the constraint system *is* the integrity mechanism |

#### 5.2 Where each proof stops

| System | Proved | By what means | First unproved link |
|---|---|---|---|
| Viaduct (repository) | label checking and authority filtering are enforced by the compiler | implementation | compiler correctness; cost model; back-end bindings |
| Viaduct-style compilation (arXiv 2401.04131) | simulation-based security of a compiler model against hybrid protocols | paper proof | instantiation of ideal functionalities by real cryptography |
| Owl | simulatability and correctness of well-typed protocols | paper proof over a core calculus; an SMT-backed type checker | the checker's implementation; adaptive corruption |
| OwlC | generated Rust refines the interaction-tree specification; no secret-dependent exits except token-guarded ones | Verus | specification compiler; crypto-library axioms; machine code |
| Wysteria | type soundness; single- to multi-threaded simulation | paper proof | implementation; the secure-computation engine |
| Symphony | three single-threaded/distributed correspondence theorems | paper proof over a core language | absence of run-time errors (dynamically typed) |
| Circuit languages | nothing by default | — | output determinism of every hinted value |

#### 5.3 Boundary invariants for anyone composing these systems

Basis: derived from the findings above.

1. **A protocol tag is an adversary-model declaration.** `ABY` in Viaduct and
   `gmw`/`yao` in Symphony each commit to a specific corruption model. In
   Viaduct the commitment is checked against stated trust (1.6); in Symphony
   and Wysteria it is not represented in any type.
2. **Authority must be re-established at every representation change.**
   Viaduct's ABY composer enumerates the permitted hand-offs (cleartext ↔
   ABY for participating hosts, and the six A/B/Y share conversions); each
   has a cost entry and each is a point where a value leaves one protocol's
   guarantee.
3. **Declassification needs a reason attached to the value.** OwlC's tokens
   carry the exact bytes being released (`ControlFlow(b)` with
   `b == self.view()`), Viaduct's `declassify` carries source and target
   labels checked for non-malleability, Symphony's `reveal` names sender and
   receiver sets. A circuit's public output is the analogous release, with no
   annotation at all.
4. **Hints are untrusted input.** Circom `<--`, Noir Brillig results and
   Halo2 advice assignments are values supplied by the party the system is
   defending against; each needs a determinism argument, not merely a
   constraint that mentions it (4.3).
5. **Field elements are not machine integers.** Any gadget whose
   specification is stated over integers (`LessThan`, bit decomposition)
   carries an unstated range precondition; over a 254-bit prime a "254-bit
   number" is not unique.

## Boundaries

- **Not examined — running toolchains.** No subject compiler, verifier or
  prover was executed. In particular it is *not examined* whether the Viaduct
  compiler at the pinned revision accepts or rejects the programs discussed
  in 1.6 exactly as the model predicts; the model decides lattice entailment
  semantically (two-valued valuations), whereas the implementation forward-
  chains over a normal form, and the two were not compared on adversarial
  inputs.
- **Not examined — archived artifacts.** The PLDI 2021 Viaduct artifact, the
  `ieee-sp-2023` Owl release and the USENIX Security 2025 OwlC archive
  (Zenodo `10.5281/zenodo.15605318`) were not inspected; statements about
  repositories are about the pinned heads only.
- **Not examined — Wysteria's implementation.** No public Git revision of
  the 2014 implementation was located on GitHub; all Wysteria statements are
  from the paper. The Symphony paper names EMP and MOTION as back ends; the
  pinned repository's sources reference EMP and an MP-SPDZ binding, and this
  discrepancy was not resolved.
- **Not examined — the full text of arXiv 2401.04131.** Only its abstract was
  read; the side conditions of its theorem are not reported here.
- **Not examined — other MPC compilers** (HyCC, CirC, MP-SPDZ, Silph),
  choreographic languages, and zkVMs.
- **Unknown — accuracy of Viaduct's cost tables.** The estimator's active
  table is labelled as the developer's own estimation; no measurement
  connecting it to ABY run time was found in the repository.
- **Unknown — mechanization.** No machine-checked proof of Owl's soundness
  theorem, of the Viaduct compiler-security theorem, or of the Wysteria and
  Symphony correspondence theorems was found in the examined material; their
  absence from other venues was not established.
- **Known not to apply.** The 32.25% aliasing figure is specific to the BN254
  scalar field with a 254-bit decomposition. It does not apply to
  `Num2Bits(n)` with `2^n ≤ p`, where the decomposition is unique, nor to
  other primes without recomputation.
- **Known not to apply.** The `IsZero` result does not indicate a defect in
  circomlib: the pinned template has both constraints and its output is
  unique. The defective variant is constructed for illustration.
- **Unsupported.** Owl explicitly does not support adaptive corruption,
  unlinkability properties or injective correspondences (S&P 2023,
  "Limitations"). OwlC's interaction trees describe terminating computations
  only. Symphony provides no static guarantee against coordination errors.
- **Stronger conclusions the evidence does not support.** (a) That Viaduct's
  output is secure because the source type-checks: the proof that exists
  concerns a model and idealized functionalities. (b) That an OwlC library is
  constant-time as machine code. (c) That passing `--inspect`, circomspect,
  Noir's checks or `MockProver` implies a circuit is sound. (d) That the SoK's
  proportions describe all deployed circuits; its authors list reliance on
  public reports as a threat to validity.

## Evidence

Observation date for all material: 2026-11-19. Repository heads were resolved
with `git ls-remote https://github.com/<owner>/<repo>.git HEAD` and files were
read from tarballs of exactly those commits.

### Source locations

`apl-cornell/viaduct` @ `34b7a4df04ca7230abf62ad9f3abd17092a74d5c` (head commit dated 2025-09-02), paths relative to `compiler/src/main/kotlin/io/github/aplcornell/viaduct/`:

| Path | Lines | Content |
|---|---|---|
| `security/SecurityLattice.kt` | 53–85 | `join`, `meet`, `or`, `and`, `swap` |
| `security/Label.kt` | 11–34 | host label, `confidentiality()`, `integrity()`, `flowsTo`, `actsFor` |
| `security/LabelExpression.kt` | 40–95 | surface operators `⊔ ⊓ & \| -> <-` |
| `algebra/FreeDistributiveLattice.kt` | 31–43 | `lessThanOrEqualTo` with assumptions |
| `analysis/HostTrustConfiguration.kt` | 19–29 | per-host axiom `IntegrityComponent(h) ≤ ConfidentialityComponent(h)` |
| `syntax/intermediate/TopLevelDeclarations.kt` | 165–189 | delegation → inequality |
| `backends/cleartext/Local.kt` 28–29; `Replication.kt` 35–36; `backends/commitment/Commitment.kt` 35–39; `backends/zkp/ZKP.kt` 31–35; `backends/aby/ABY.kt` 31–35 | | `authority()` |
| `selection/SelectionConstraintGenerator.kt` | 66–84 | `viableProtocols` |
| `selection/Z3SelectionProblemSolver.kt` | 128, 166 | `mkOptimize`, `MkMinimize` |
| `selection/SimpleCostEstimator.kt` | 217–288, 290–322, 389–409, 495–523 | operator table in use, base costs, conversion table in use, feature weights |
| `backends/aby/ABYProtocolFactory.kt` | 55–73 | operators excluded from `ArithABY` |
| `analysis/InformationFlowAnalysis.kt` | 344–380 | downgrade constraints |

Also `compiler/tests/should-pass/Millionaires.via` and
`benchmarks/benchmarks/HistoricalMillionaires.via` (label annotations quoted
in 1.6).

`secure-foundations/owl` @ `1b56f8cc70a067721917b9ccb60430417ada68f0` (head commit dated 2026-11-06): `README.md`; `extraction/Cargo.toml`; `extraction/src/speclib.rs` lines 283–301 (`DeclassifyingOp`, `ITree`); `extraction/src/execlib.rs` lines 743–865 (`SecretBuf` and its exits); `tests/success/encrypted_key.owl`.

`plum-umd/symphony-lang` @ `4396e5fb45c57bf7a045c2d00fd53108744caa5c` (head commit dated 2022-12-29): `src/lib/common/Symphony/Lang/Syntax.hs` lines 117–128 (`data Prot`); `res/Programming23/symphony/gcd.sym`.

`iden3/circomlib` @ `8852c3bc91e3ede890f2143f36457b25302abce2`: `circuits/comparators.circom` lines 24–34 (`IsZero`), 89–99 (`LessThan`); `circuits/bitify.circom` lines 25–53 (`Num2Bits`, `Num2Bits_strict`); `circuits/aliascheck.circom` lines 24–33; `circuits/compconstant.circom` lines 25–74.

`iden3/circom` @ `9b4b23331644e17868c90a85768826ed3bcba59f` (commit subject "preparing release 2.2.4"): `mkdocs/docs/circom-language/signals.md`, `constraint-generation.md`, `basic-operators.md` (shift semantics `x >> k = x/(2**k)`), `tags.md`, `code-quality/inspect.md`; `mkdocs/docs/getting-started/compilation-options.md` (primes, `--O0/--O1/--O2`).

`noir-lang/noir` @ `af5d97aaa0f67fde5da9a7a790968b88cffff439`: `docs/docs/language/unconstrained.md`; `compiler/noirc_evaluator/src/ssa/checks/check_for_missing_brillig_constraints.rs` (module documentation), `check_for_underconstrained_values.rs`; `compiler/noirc_driver/src/lib.rs` lines 197–203 (skip options).

`zcash/halo2` @ `7465edf9110aace00b8c24b96270e1b820fd39fb` (`halo2_proofs` 0.4.1): `book/src/concepts/arithmetization.md`; `book/src/user/dev-tools.md`; `halo2_proofs/src/dev/failure.rs` lines 110–185 (`VerifyFailure`).

`trailofbits/circomspect` @ `50010b623ed4f3bff9d1b0363cfe952385b47af3`: `doc/analysis_passes.md`.
`Veridise/Picus` @ `138b151d3a388e5b6c040c163e0a1db04f2ceda6`: `README.md`.
`0xPARC/zk-bug-tracker` @ `56a996672fb50486279126c8e12530f2bf933d0b`: `README.md`.

### Publications

| Work | Identity | Used for |
|---|---|---|
| Acay, Recto, Gancher, Myers, Shi. *Viaduct: An Extensible, Optimizing Compiler for Secure Distributed Programs.* PLDI 2021 | DOI `10.1145/3453483.3454074`; technical report ePrint 2021/468 | protocol descriptions (`SH-MPC`, `MAL-MPC`), evaluation setup, conclusion |
| Acay, Gancher, Recto, Myers. *Secure Synthesis of Distributed Cryptographic Applications (Technical Report).* | arXiv 2401.04131v1 (6 Jan 2024) | scope of the compiler-security proof (abstract only) |
| Cecchetti, Myers, Arden. *Nonmalleable Information Flow Control.* CCS 2017 | DOI `10.1145/3133956.3134054` | cited by `SecurityLattice.swap` |
| Gancher, Gibson, Singh, Dharanikota, Parno. *Owl: Compositional Verification of Security Protocols via an Information-Flow Type System.* IEEE S&P 2023, pp. 1130–1147 | DOI `10.1109/SP46215.2023.10179477`; ePrint 2023/473 | label model, guarantees, limitations |
| Singh, Gancher, Parno. *OwlC: Compiling Security Protocols to Verified, Secure, High-Performance Libraries.* USENIX Security 2025 | ePrint 2025/1092 | architecture, TCB, limitations |
| Rastogi, Hammer, Hicks. *Wysteria: A Programming Language for Generic, Mixed-Mode Multiparty Computations.* IEEE S&P 2014 | DOI `10.1109/SP.2014.48` | constructs and theorems |
| Sweet, Darais, Heath, Harris, Estes, Hicks. *Symphony: Expressive Secure Multiparty Computation with Coordination.* ‹Programming› 7(3), 2023 | DOI `10.22152/programming-journal.org/2023/7/14`; arXiv 2302.10076v1 | constructs, theorems, comparison with Wysteria |
| Pailoor et al. (ten authors). *Automated Detection of Under-Constrained Circuits in Zero-Knowledge Proofs.* PLDI 2023 (Proc. ACM Program. Lang. 7, article 168) | DOI `10.1145/3591282`; ePrint 2023/512 | QED² definition and results |
| Chaliasos, Ernstberger, Theodore, Wong, Jahanara, Livshits. *SoK: What don't we know? Understanding Security Vulnerabilities in SNARKs.* USENIX Security 2024 | arXiv 2402.15293v4 | counts in 4.6 (Table 4 of the paper) |

### Executable models

Environment: CPython 3.13.15 on Linux x86_64; standard library only; both
scripts are deterministic (no randomness) and finish in under two seconds.

```bash
mkdir -p /tmp/probe && cd /tmp/probe
# save the two listings below under the names shown, then:
python3 viaduct_authority_model.py      # output reproduced in Findings 1.6
python3 r1cs_underconstraint_probe.py   # output reproduced in Findings 4.5
```

`viaduct_authority_model.py`:

```python
#!/usr/bin/env python3
"""Model of Viaduct's label lattice and protocol-authority check (stdlib only).

Transcribes, from apl-cornell/viaduct @ 34b7a4df04ca7230abf62ad9f3abd17092a74d5c:
  security/SecurityLattice.kt   join / meet / and / or / swap / integrity()
  security/Label.kt             actsFor / flowsTo
  backends/*/{Local,Replication,Commitment,ZKP,ABY}.kt   authority()
  analysis/HostTrustConfiguration.kt   per-host axiom  I(h) <= C(h)
  syntax/intermediate/TopLevelDeclarations.kt   `assume for <- x trusts y`  =>  I(y) <= I(x)

This is NOT a run of the Viaduct compiler.  Entailment `X <= Y` under hypotheses
is decided semantically: a Horn clause over distributive lattices holds in every
distributive lattice iff it holds in the two-element lattice, so we enumerate all
0/1 valuations of the atoms (0 = strongest principal, 1 = weakest).
"""
import itertools

HOSTS = ("alice", "bob")
ATOMS = [(k, h) for h in HOSTS for k in ("C", "I")]

# principal expression = frozenset of frozensets of atoms (join of meets)
TOP = frozenset([frozenset()])            # weakest principal (empty meet)
def atom(k, h): return frozenset([frozenset([(k, h)])])
def p_join(x, y): return frozenset(x | y)
def p_meet(x, y): return frozenset(a | b for a in x for b in y)
def ev(x, v): return max((min((v[a] for a in m), default=1) for m in x), default=0)

class Label:
    def __init__(self, c, i): self.c, self.i = c, i
    def join(self, o): return Label(p_meet(self.c, o.c), p_join(self.i, o.i))
    def meet(self, o): return Label(p_join(self.c, o.c), p_meet(self.i, o.i))
    def and_(self, o): return Label(p_meet(self.c, o.c), p_meet(self.i, o.i))
    def or_(self, o): return Label(p_join(self.c, o.c), p_join(self.i, o.i))
    def swap(self): return Label(self.i, self.c)
    def integrity(self): return Label(TOP, self.i)

def host(h): return Label(atom("C", h), atom("I", h))

def leq(x, y, hyps):
    for bits in itertools.product((0, 1), repeat=len(ATOMS)):
        v = dict(zip(ATOMS, bits))
        if all(ev(a, v) <= ev(b, v) for a, b in hyps) and ev(x, v) > ev(y, v):
            return False
    return True

def acts_for(frm, to, hyps): return leq(frm.c, to.c, hyps) and leq(frm.i, to.i, hyps)
def flows_to(frm, to, hyps): return leq(to.c, frm.c, hyps) and leq(frm.i, to.i, hyps)

A, B = host("alice"), host("bob")
HOST_AXIOMS = [(atom("I", h), atom("C", h)) for h in HOSTS]
MUTUAL_INTEGRITY_TRUST = [(atom("I", "bob"), atom("I", "alice")),   # assume for <- alice trusts bob
                          (atom("I", "alice"), atom("I", "bob"))]   # assume for <- bob trusts alice
SCENARIOS = {"no delegation (malicious)": HOST_AXIOMS,
             "mutual integrity trust (semi-honest)": HOST_AXIOMS + MUTUAL_INTEGRITY_TRUST}

def aby(s, c):
    combined = s.join(c)
    return combined.meet(combined.integrity().swap())

PROTOCOLS = {
    "Local(alice)":            A,
    "Local(bob)":              B,
    "Replication{alice,bob}":  A.meet(B),
    "Commitment(alice;bob)":   A.and_(B.integrity()),
    "ZKP(alice;bob)":          A.and_(B.integrity()),
    "ABY(alice,bob)":          aby(A, B),
}
DATA = {
    "{alice}":            A,
    "{bob}":              B,
    "{alice | bob}":      A.or_(B),
    "{alice & bob<-}":    A.and_(B.integrity()),
    "{alice & bob}":      A.and_(B),
}

for name, hyps in SCENARIOS.items():
    print(f"== {name} ==")
    print(f"{'protocol authority actsFor ->':28s}" + "".join(f"{d:>18s}" for d in DATA))
    for pn, auth in PROTOCOLS.items():
        row = "".join(f"{('yes' if acts_for(auth, lab, hyps) else '-'):>18s}" for lab in DATA.values())
        print(f"{pn:28s}{row}")
    cmp_label = A.join(B)                       # label of `a <= b` with a:{alice}, b:{bob}
    print(f"  ({'{alice}'} join {'{bob}'}) flowsTo {'{alice & bob}'}: "
          f"{flows_to(cmp_label, A.and_(B), hyps)}")
    for dn, lab in (("{alice & bob}", A.and_(B)), ("{alice} join {bob}", cmp_label)):
        print(f"  downgrade source {dn:20s} nonmalleable (l flowsTo swap(l)): "
              f"{flows_to(lab, lab.swap(), hyps)}")
    print()
```

`r1cs_underconstraint_probe.py`:

```python
#!/usr/bin/env python3
"""Under-constrained circuit micro-probe (pure Python 3, standard library only).

Models three circomlib templates as *constraint systems over F_p* and counts the
witnesses a malicious prover may choose.  A circuit is modelled as a predicate
C(inputs, outputs, intermediates) made only of the `===`/`<==` equations; the
`<--` hints are deliberately NOT part of the predicate, because the verifier
never sees them.

  Part 1  IsZero            (exhaustive over a small prime field)
  Part 2  Num2Bits(254)     (BN254 scalar field; aliasing x vs x+p)
  Part 3  LessThan(n)       (BN254 scalar field; unchecked input width)
"""
import itertools

# ---------------------------------------------------------------- Part 1
def iszero_constraints(p, x, out, inv, with_second_constraint=True):
    c1 = (out - (-x * inv + 1)) % p == 0          # out <== -in*inv + 1
    c2 = (x * out) % p == 0                       # in*out === 0
    return c1 and (c2 if with_second_constraint else True)

def part1(p=97):
    print(f"== Part 1: IsZero over F_{p} (exhaustive) ==")
    for full in (True, False):
        outs_per_input = {}
        wits_per_input = {}
        for x in range(p):
            outs = set()
            wits = 0
            for out, inv in itertools.product(range(p), repeat=2):
                if iszero_constraints(p, x, out, inv, full):
                    outs.add(out)
                    wits += 1
            outs_per_input[x] = outs
            wits_per_input[x] = wits
        label = "both constraints" if full else "`in*out === 0` removed"
        unique = all(len(o) == 1 for o in outs_per_input.values())
        correct = all(o == {1 if x == 0 else 0} for x, o in outs_per_input.items())
        print(f"[{label}]")
        print(f"  output uniquely determined for every input: {unique}")
        print(f"  the unique output equals (in == 0 ? 1 : 0):   {correct}")
        print(f"  #outputs accepted for in=0: {len(outs_per_input[0])}, "
              f"for in=5: {len(outs_per_input[5])}")
        print(f"  #witnesses (out,inv) for in=0: {wits_per_input[0]}, "
              f"for in=5: {wits_per_input[5]}")
        if not full:
            print(f"  forged claim 'IsZero(5) = 1' satisfiable: "
                  f"{iszero_constraints(p, 5, 1, 0, False)}  (witness inv=0)")

# ---------------------------------------------------------------- Part 2
BN254_R = 21888242871839275222246405745257275088548364400416034343698204186575808495617

def bits_le(v, n):
    return [(v >> i) & 1 for i in range(n)]

def num2bits_constraints(p, x, bits):
    boolean = all((b * (b - 1)) % p == 0 for b in bits)       # out[i]*(out[i]-1) === 0
    lc = sum(b << i for i, b in enumerate(bits))
    return boolean and (lc - x) % p == 0                      # lc1 === in

def compconstant_out(p, ct, bits):
    """Port of circomlib CompConstant(ct): returns (satisfiable, out)."""
    assert len(bits) == 254
    b = (1 << 128) - 1
    a = 1
    e = 1
    total = 0
    for i in range(127):
        clsb = (ct >> (i * 2)) & 1
        cmsb = (ct >> (i * 2 + 1)) & 1
        slsb = bits[i * 2]
        smsb = bits[i * 2 + 1]
        if cmsb == 0 and clsb == 0:
            part = -b * smsb * slsb + b * smsb + b * slsb
        elif cmsb == 0 and clsb == 1:
            part = a * smsb * slsb - a * slsb + b * smsb - a * smsb + a
        elif cmsb == 1 and clsb == 0:
            part = b * smsb * slsb - a * smsb + a
        else:
            part = -a * smsb * slsb + a
        total = (total + part) % p
        b -= e
        a += e
        e *= 2
    satisfiable = total < (1 << 135)          # Num2Bits(135) on sout
    return satisfiable, (total >> 127) & 1

def part2():
    p = BN254_R
    print("== Part 2: Num2Bits(254) aliasing over the BN254 scalar field ==")
    print(f"  p.bit_length() = {p.bit_length()},  2^254 > p: {(1 << 254) > p}")
    alias_count = (1 << 254) - p
    print(f"  field elements with two 254-bit decompositions: 2^254 - p = {alias_count}")
    print(f"  fraction of the field: {alias_count / p:.6f}")
    x = 5
    canon = bits_le(x, 254)
    alias = bits_le(x + p, 254)
    print(f"  x = {x}")
    print(f"  canonical bits satisfy Num2Bits(254): {num2bits_constraints(p, x, canon)}")
    print(f"  bits of x+p    satisfy Num2Bits(254): {num2bits_constraints(p, x, alias)}")
    print(f"  the two bit vectors differ: {canon != alias}; "
          f"LSB canonical={canon[0]}, LSB alias={alias[0]}")
    ct = p - 1                                  # circom `CompConstant(-1)`
    for name, bits in (("canonical", canon), ("alias", alias)):
        sat, out = compconstant_out(p, ct, bits)
        print(f"  AliasCheck on {name:9s}: CompConstant(-1) satisfiable={sat}, out={out} "
              f"-> `out === 0` {'holds' if sat and out == 0 else 'FAILS'}")
    # boundary sanity: largest canonical value p-1 passes, p itself (alias of 0) fails
    for name, v in (("p-1", p - 1), ("p (alias of 0)", p), ("2^254-1", (1 << 254) - 1)):
        sat, out = compconstant_out(p, ct, bits_le(v, 254))
        print(f"  CompConstant(-1) on bits({name}): satisfiable={sat}, out={out}")

# ---------------------------------------------------------------- Part 3
def lessthan_out(p, n, a, b):
    """circomlib LessThan(n): n2b.in <== in[0] + (1<<n) - in[1]; out <== 1 - n2b.out[n].
    Returns None when Num2Bits(n+1) has no satisfying bit vector."""
    v = (a + (1 << n) - b) % p
    if v >= (1 << (n + 1)):
        return None
    return 1 - ((v >> n) & 1)

def part3():
    n = 8
    print(f"== Part 3: LessThan({n}) with inputs not range-checked to {n} bits ==")
    # (a) exhaustive over a small prime field: every a in F_q, fixed b = 10
    q = 1009                                   # prime, 2^(n+1) = 512 < q
    b = 10
    accepted = [a for a in range(q) if lessthan_out(q, n, a, b) == 1]
    truly_less = [a for a in accepted if a < b]
    print(f"  [exhaustive, F_{q}] #a with LessThan({n})(a, {b}) = 1: {len(accepted)}; "
          f"of these, integers a < {b}: {len(truly_less)}; "
          f"false accepts: {len(accepted) - len(truly_less)}")
    print(f"  [exhaustive, F_{q}] false accepts are exactly a in "
          f"[{min(a for a in accepted if a >= b)}, {max(accepted)}]: "
          f"{sorted(a for a in accepted if a >= b) == list(range(q - (1 << n) + b, q))}")
    in_range = all((lessthan_out(q, n, a, c) == (1 if a < c else 0))
                   for a in range(1 << n) for c in range(1 << n))
    print(f"  [exhaustive, F_{q}] correct on all {1 << n}x{1 << n} pairs of {n}-bit inputs: {in_range}")
    # (b) concrete forgeries over the BN254 scalar field
    p = BN254_R
    print(f"  [BN254] honest   in=[3, 10]      -> out={lessthan_out(p, n, 3, 10)}")
    print(f"  [BN254] honest   in=[10, 3]      -> out={lessthan_out(p, n, 10, 3)}")
    huge = p - 100
    print(f"  [BN254] attacker in=[p-100, 10]  -> out={lessthan_out(p, n, huge, 10)}   "
          f"(integer truth: p-100 < 10 is {huge < 10})")
    print(f"  [BN254] attacker in=[10, p-100]  -> out={lessthan_out(p, n, 10, huge)}   "
          f"(integer truth: 10 < p-100 is {10 < huge})")

if __name__ == "__main__":
    part1()
    part2()
    part3()
```

The entailment procedure in the first listing relies on a standard fact: an
implication between lattice inequalities holds in every distributive lattice
iff it holds in the two-element lattice, because every distributive lattice
embeds in a power of the two-element lattice and such implications are
preserved by sublattices and products.

## Revalidation

Cheapest discriminating checks, in order of cost:

1. **Viaduct authority labels (seconds).** Diff the five `authority()`
   bodies and `HostTrustConfiguration.kt` against the table in 1.2 and the
   axiom in 1.1. If any changed, update the corresponding line of
   `PROTOCOLS`/`HOST_AXIOMS` in `viaduct_authority_model.py` and rerun; the
   decisive cells are `ABY(alice,bob)` × `{alice & bob}` in the two
   scenarios. A new directory under `backends/` (for example a maliciously
   secure MPC protocol) invalidates the "no malicious-MPC back end" statement.
2. **Viaduct cost model (seconds).** Check which map
   `SimpleCostEstimator.executionCost` and `abyShareConversionCost` index and
   whether `lanWeights`/`wanWeights` changed.
3. **Viaduct end to end (requires a JVM and Z3).** Compile
   `compiler/tests/should-pass/Millionaires.via` with and without its two
   `assume` lines; the model predicts acceptance with ABY selected for
   `bob_richer` in the first case and a label error in the second.
4. **OwlC seams (seconds).** `grep -c external_body extraction/src/execlib.rs`
   and re-read the `SecretBuf` impl block; any new public method returning
   bytes without a `DeclassifyingOpToken` precondition widens the exit
   surface in 2.2.
5. **Circuit templates (seconds).** Re-extract `IsZero`, `Num2Bits`,
   `LessThan` and `CompConstant` from circomlib; if unchanged, rerun
   `r1cs_underconstraint_probe.py`. For another curve, replace `BN254_R`; the
   aliasing count is `max(0, 2^n − p)` for an `n`-bit decomposition.
6. **Tool behaviour (requires the tools).** Feed the 4.5 `IsZero` variant
   without its second constraint to `circom --inspect`, circomspect and
   Picus. Untested predictions from the tools' documentation: `--inspect`
   stays silent (every signal still occurs in a constraint); circomspect's
   single-constraint heuristic flags `inv` in both the correct and the
   defective template, so it does not separate them; a uniqueness checker
   reports `out` only for the defective one. Any other outcome is new
   information.
7. **Paper claims.** The proof-status table in 5.2 changes if a mechanized
   proof of Owl's core calculus or of the Viaduct compiler model is
   published; search for artifacts citing ePrint 2023/473 and arXiv
   2401.04131.

A passing run of either listing establishes only that the transcribed
definitions have the stated consequences.
