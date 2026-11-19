# Authorization logics, speaks-for calculi, and attested capability delegation

## Summary

A remote call across a trust boundary needs an answer to "who is speaking, on whose authority,
about which code, and how recently". Four bodies of work answer parts of that question and fit
together only at specific joints:

1. **Says / speaks-for logics** turn credentials into formulas `K says s` and access decisions
   into proofs. The decisive design choice is the modal strength of `says`. In a *classical* logic
   the natural axiom `s ⊃ A says s` (Unit) forces *Escalation*, `A says s ⊃ (s ∨ A says false)`;
   constructive logics (CDD, ICL, NAL, BL) avoid it and confine an inconsistent principal's damage
   to that principal; in CDD and NAL hand-off, `B says (A ⇒ B) ⊃ (A ⇒ B)`, is a theorem.
   The executable model checker below reproduces each of these facts and shows that the direction
   of hand-off matters (`A says (A ⇒ B)` grants nothing).
2. **Attestation is a chain of nested `says`**: hardware key says OS says program says `F`
   (NAL sub-principals; RATS layered attestation). It establishes *which code holds a key*, not
   that the code is correct. Ironclad Apps close that gap by verifying the measured binary against
   an abstract state machine and binding the app's key to its code through TPM registers.
3. **RATS** (RFC 9334) standardises the roles and messages but not the logic: Endorsements are
   hand-offs, Evidence and Attestation Results are `says` statements, the two appraisal policies
   are `controls` assumptions. Freshness (timestamp, nonce, epoch identifier) is outside pure
   `says` logic and needs time-indexed formulas, epoch sub-principals or state predicates.
4. **Transparency logs** (Certificate Transparency, Sigstore) upgrade "K says s" to "K said s
   where everyone can see it, by time t". Inclusion and consistency proofs detect rewriting; they do
   not detect a split view from a single vantage point (probe). Rekor v2 no longer returns the
   log's own inclusion promise or timestamp; it relies on verified checkpoints and RFC 3161
   timestamps, and states a plan for witness co-signatures.
5. **Capability hand-off** (OCapN CapTP, Cap'n Proto level 3) delegates by *introduction*: the
   gifter deposits the reference at the exporter and gives the receiver a signed certificate naming
   the receiver's session key; the receiver redeems it with a second signature and a never-reused
   counter. In logic terms this is a one-shot, session-bound restricted delegation, in contrast to
   bearer secrets (swiss numbers, tokens) where knowledge is authority.

## Applicability

The subjects in `REPORT.json` are compared and related; they do not form one system. The
report states (as *derived*) how their artifacts would be chained for an attested remote
foreign-function interface.

- **Read in full text:** Abadi–Burrows–Lampson–Plotkin (ABLP); Abadi, *Variations*; Garg–Abadi
  (full version); Garg–Pfenning 2006 (introduction and judgments); Garg–Pfenning 2010 (PCFS/BL);
  Schneider–Walsh–Sirer (NAL); Sirer et al. (logical attestation); Hawblitzel et al. (Ironclad
  Apps); RFC 9334; RFC 6962 and RFC 9162 Section 2.1; RFC 2693 Section 6.3; the table of contents
  and nonce claim of RFC 9711.
- **Source-inspected at pinned revisions:** OCapN `draft-specifications/CapTP Specification.md`
  and `Locators.md`; Cap'n Proto `c++/src/capnp/rpc.capnp`; Endo `packages/ocapn/README.md`;
  Rekor v1 `openapi.yaml`; Rekor v2 `README.md` and `CLIENTS.md`; Fulcio `docs/`; the
  transparency-dev Merkle library's `testonly/constants.go`; in-toto `spec/README.md`; Ironclad
  `ironclad-apps/README.md` and `ironclad-apps/src/Dafny/Apps/Notary/Notary.s.dfy`.
- **Not executed:** no examined implementation was run. The two probes are self-contained
  re-implementations of published definitions (Kripke semantics of ICL; RFC 6962/9162 Merkle
  algorithms) and are checked against published facts and the Merkle library's test vectors.
- **Status caveats:** the OCapN documents open with "Warning: This is a draft specification likely
  to undergo significant change"; the Endo package calls itself "a tentative implementation"; Rekor
  v2 statements about witnessing are stated plans. Findings about these apply to the pinned
  revisions only. The authorization logics are stable published definitions.

## Findings

### 1. Four logics of `says`

| | ABLP (1993) | CDD / ICL (2006–2008) | BL (PCFS, 2010) | NAL (Nexus, 2011) |
|---|---|---|---|---|
| Base logic | classical propositional modal logic | intuitionistic (CDD second-order; ICL propositional) | first-order intuitionistic | constructive, second-order (extends CDD) |
| `says` | normal modality: K axiom + necessitation | lax modality: Unit, closure under consequence, idempotence (ICL: unit, cuc, idem; CDD: Unit, Bind) | indexed modality whose interpretation "is different from that in any existing work", "designed to facilitate faster proof search and to increase expressiveness" | SAYS-I (theorems are believed by everyone), SAYS-E (`A says A says F` ⊢ `A says F`), DEDUCE |
| Principals | `A ∧ B`, quoting `B\|A`, roles `A as R`, delegation `B for A` (the last two coded from `∧` and `\|`) | atomic; ICL^B adds Boolean combinations | terms; strongest principal ℓ ("local authority") | keys, hashes, sub-principals `A.τ`, groups `{\|v : P\|}` |
| Speaks-for | `A ⇒ B` stands for `A = A ∧ B`; axiom `(A ⇒ B) ⊃ (A says s ⊃ B says s)` | `∀X. A says X → B says X` (CDD), primitive `A ⇒ B` with refl, trans, speaking-for, handoff (ICL⇒) | constraint `k1 ≽ k2` decided by an external procedure; forces `(k1 says s) ⊃ (k2 says s)` | `A → B` abbreviates `∀x. A says x ⇒ B says x`; restricted form `A →(v:F) B` |
| Hand-off | not among the axioms quoted below; Garg–Abadi attribute the hand-off axiom to the companion systems paper by Lampson, Abadi, Burrows and Wobber | theorem of CDD; axiom of ICL⇒ | not examined | derived rule HAND-OFF |
| Time / state | not modelled ("we do not explain how principals come to believe that messages are recent") | none | `s @ [u1,u2]`, constraints, interpreted predicates over system state | state predicates via authorities; epochs as sub-principals |
| Semantics / metatheory | Kripke semantics; axioms sound, not complete | sound and complete translation to S4; Kripke models; PSPACE decidability (ICL, ICL⇒) | sequent calculus; enforcement theorem for capabilities | worldviews `ω(A)`; `A says F` iff `F ∈ ω(A)` |

Exact axioms, quoted:

- **ABLP.** Propositional tautologies and modus ponens; `⊢ A says (s ⊃ s′) ⊃ (A says s ⊃ A says s′)`;
  "if ⊢ s then ⊢ A says s, for every A"; `⊢ (A ∧ B) says s ≡ (A says s) ∧ (B says s)`;
  `⊢ (B|A) says s ≡ B says A says s`; `⊢ (A ⇒ B) ⊃ ((A says s) ⊃ (B says s))`.
  `A controls s` abbreviates `(A says s) ⊃ s`; an access-control list for `s` is a list of
  `A controls s`. Principals form a "multiplicative semilattice semigroup" (`∧` a semilattice, `|`
  associative and distributing over `∧`). In the Kripke semantics
  `E(A ⇒ B) = W if R(B) ⊆ R(A) and ∅ otherwise`, so the formula
  `(C says (A ⇒ B)) ≡ ((A ⇒ B) ∨ (C says false))` "is valid but not provable".
- **ICL.** `⊢ s ⊃ (A says s)` (unit); `⊢ (A says (s ⊃ t)) ⊃ (A says s) ⊃ (A says t)` (cuc);
  `⊢ (A says A says s) ⊃ A says s` (idem). ICL⇒ adds `A ⇒ A`; transitivity;
  `(A ⇒ B) ⊃ (A says s) ⊃ (B says s)`; `(B says (A ⇒ B)) ⊃ (A ⇒ B)` (handoff).
  Translation to S4: atoms and implications are boxed, `⌜A says s⌝ = □(A ∨ ⌜s⌝)` and
  `⌜A ⇒ B⌝ = □(A ⊃ B)`, with each principal read as an S4 atom ("principal A is unhappy").
- **NAL.** `false` is `∀x. x`; from `A says false` DEDUCE yields `A says G` for any `G` "but
  DEDUCE cannot be used to derive `B says G` for a different principal B"; SUBPRIN: `A → A.τ`.
- **BL.** `k says s`, `s @ [u1,u2]`, uninterpreted predicates "established using logical rules and
  a priori using signed certificates", constraints "interpreted through trusted decision
  procedures", interpreted predicates capturing "properties of the environment" (file-system
  state); `(ℓ says s) ⊃ (k says s)` for every `k`.

Basis: normative (each paper defines its logic).

### 2. The axiom menu and its consequences

Abadi's *Variations* compares axioms over a second-order base with closure under consequence and
necessitation:

```text
[Unit]        X → A says X
[Bind]        (X → A says Y) → (A says X) → (A says Y)
[C4]          A says A says X → A says X
[Escalation]  (A says X) → (X ∨ (A says Y))
[Hand-off]    A controls (B ⇒ A)            i.e.  (A says (B ⇒ A)) → (B ⇒ A)
```

Results stated there: classically, "Bind is equivalent to Escalation, while Unit implies
Escalation"; C4 alone avoids Escalation but such systems "appear quite limited in their support
of delegation"; intuitionistically, CDD (Unit + Bind) "does not lead to Escalation"; Bind implies
C4, and Unit with C4 implies Bind; the generalized hand-off axiom "is equivalent to Bind"; DCC
proves `(A says B says s) → (B says A says s)` while CDD does not.

**Probe 1** checks formulas on every ICL⇒ Kripke model with at most three worlds. A countermodel
is a proof of unprovability (the models are sound and complete); validity on small models is
bounded evidence only, but every "valid" row below is an axiom, a theorem stated in the sources,
or (for the attested chain of Section 5) derivable from handoff, speaking-for and modus ponens.

| Formula | All models ≤ 3 worlds | One-world (classical) models |
|---|---|---|
| unit, cuc, idem, speaking-for, handoff, transitivity | valid | valid |
| `A says false → A says s` (local explosion) | valid | valid |
| `A says s → s` | countermodel | countermodel |
| `A says false → B says false` (cross-principal explosion) | countermodel | countermodel |
| `A says s → (s ∨ A says false)` (Escalation) | countermodel (2 worlds) | **valid** |
| `A says B says s → B says A says s` | countermodel (2 worlds) | **valid** |
| `A says (A ⇒ B) → (A ⇒ B)` (self-grant) | countermodel | countermodel |
| `(A says s → B says s) → (A ⇒ B)` (one statement is not a delegation) | countermodel | countermodel |
| `s ∨ (s → false)` | countermodel (2 worlds) | valid |

The two rows that flip between columns are the executable form of the classical collapse: a
guard built on a classical prover (or on a one-world model such as a flat fact database) that
also believes Unit will accept Escalation.

Why constructive matters operationally (Garg–Pfenning 2006): "it is in general impossible to
come up with a proof of either A or K says B given a proof of K says A"; their logic has a
judgment `K affirms A` beside `A true`, cut elimination, and non-interference properties
stating that "without explicit links between principals K and L, no assertions made by K
(including even contradictory statements) can influence the truth of assertions made by L".

Basis: normative (papers) + execution (Probe 1).

### 3. Delegation forms, weakest to strongest

| Form | Statement | Scope control | Source |
|---|---|---|---|
| Quoting | `(B\|A) says s ≡ B says A says s` | none; no proof that `A` agreed | ABLP |
| Full hand-off | `B says (A ⇒ B)` gives `A ⇒ B` | none: "all beliefs in the worldview of principal A also appear in the worldview of principal B" | NAL; ICL⇒ |
| Restricted hand-off | `B says (A →(v:F) B)`: only statements of shape `F` flow | by formula shape | NAL |
| Sub-principal | `A → A.τ` | by naming convention; "from A says F we could derive A.τ says F for any sub-principal" | NAL |
| Constraint order | `k1 ≽ k2` | decided outside the logic | BL |
| Certificate chain | `<I1,S1,D1,A1,V1> + <I2,S2,D2,A2,V2>` yields `<I1,S2,D2,AIntersect(A1,A2),VIntersect(V1,V2)>` provided `S1 = I2` and `D1 = TRUE` | authorization-tag and validity intersection; Boolean delegation bit | SPKI, RFC 2693 §6.3 |
| Proven capability | proof checked once; result authenticated with a symmetric key and carrying residual time/state conditions | conditions re-checked at use | PCFS "procap" |

Two cautions recorded by the sources. NAL: a restricted delegation and a second delegation on the
negated predicate together "could allow CSdept says false to be derived if UnivReg is
compromised". ABLP: `B ⇒ (B|A)` must *not* hold, "since B may wish to say s without this being
taken as a quotation of A".

Basis: normative.

### 4. Proof-carrying authorization: who searches, who checks, what is cached

- **PCFS.** Workflow "Policy → Proof → Procap → File access". Proof search is "not a trusted
  component"; the verifier "is a simple piece of code and must be trusted", checks proof structure
  and certificate signatures, and returns a *procap* "signed using a shared symmetric key that is
  known only to the verifier and the file system reference monitor". Interpreted predicates are
  "defined (and verified) relative to the environment E prevailing at the time that the procap ...
  is used for access", so a proof never freezes mutable state.
- **Nexus.** A *label* is a formula `P says S` created by the `say` system call and held in a
  kernel *labelstore*; a *goal formula* in NAL is attached to an operation on a resource; a *guard*
  checks a client-supplied proof that labels entail the goal; a kernel *decision cache* avoids
  repeated checks. Dynamic facts come from *authorities* that "attest to the veracity of a label
  only when asked" and whose answers are not transferable. Externalised labels have the shape
  "TPM says kernel says labelstore says processid says S".
- **Bases for trust** (logical attestation): *axiomatic* (a hash or signer is trusted outright),
  *analytic* (an analyzer says a property holds of the code) and *synthetic* (the code was
  rewritten or is monitored to enforce it). "Hash-based attestation forces all trust decisions to
  be axiomatic".

Basis: documentation (system papers).

### 5. Attestation as nested speech; the RATS roles in logical form

NAL gives two credential shapes: a signature verifying under `K_A` "conveys NAL formula
`K_A says F`"; content `F` stored in an object conveys `H(obj) says F`, useful only for "static
sets of beliefs held by objects whose state is fixed". A measured boot chain is
`K_CPU says (K_CPU.H_OS says (K_CPU.H_OS.H_CA says F))`, collapsed by SUBPRIN and SAYS-E to
`K_CPU.H_OS.H_CA says F`. Epochs and nonces are further sub-principals (`FileSys.1`,
`FileSys.2`, …) so that "a guard can reject requests accompanied by outdated credentials".

RFC 9334 defines roles and conceptual messages; the right-hand column is this report's reading.

| RATS term (RFC 9334 §4) | Definition (abridged quotation) | Logical reading (derived) |
|---|---|---|
| Attester | "whose Evidence must be appraised" | principal `K_att`, usually a sub-principal chain per layer |
| Endorser / Endorsement | "vouches for the integrity of an Attester's various capabilities, such as Claims collection and Evidence signing" | `E says (K_att ⇒ E)`, ideally restricted to measurement claims |
| Evidence | "A set of Claims generated by an Attester" | `K_att says claims(target) ∧ nonce = n` |
| Reference Value Provider / Reference Values | values "against which values of Claims can be compared" | `R says good(c)` |
| Verifier / Attestation Result | "appraises the validity of Evidence ... and produces Attestation Results" | `V says ok(attester, n)` derived under `E controls …`, `R controls good` |
| Appraisal Policy for Evidence | rules "a Verifier uses to evaluate the validity of information about an Attester" | the Verifier's `controls` assumptions |
| Appraisal Policy for Attestation Results | rules for "how a Relying Party uses the Attestation Results" | `V controls ok`, held by the Relying Party |
| Passport / Background-Check model | Attester carries the result / Relying Party forwards Evidence to the Verifier | who transports the credential; the formulas are identical |

Supporting text: the trust model itself uses the calculus's vocabulary, requiring that channel
key material be "trusted by the Verifier to speak for the Attesting Environment(s) that collected
Claims" (§7.4). In layered attestation "a previous layer acts as the Attesting Environment for
the next layer" and "Claims about an initial layer are typically asserted by an Endorser" (§3.2),
which is the nested-`says` chain with an endorsed root. A Relying Party may require the Verifier
itself to attest first (§7.1): a Verifier is an ordinary principal.

Freshness (§10): timestamps need "synchronized and trustworthy clocks"; a nonce shows "the
Claims were signed after the nonce was generated" but the epoch is "rough" because it "applies
to the entire Claim set" and "the time between the creation of Claims and the collection of
Claims is indistinguishable"; epoch identifiers "can be used more than once and can even be used
by more than one entity at the same time". "There is, however, always a race condition possible
in that the state of the Attester and the appraisal policies might change immediately after".
EAT (RFC 9711) carries these as claims: `eat_nonce` (§4.1), `ueid`, `measurements`, `measres`,
`submods` (§4.2).

**Probe 1, attestation rows.** With `H1 = E says (K ⇒ E)`, `H2 = K says (M ⇒ K)`,
`H3 = M says p`, `H4 = (E says p) → p`: `H1 ∧ H2 ∧ H3 ∧ H4 → p` is valid on all 67,344 models
checked; dropping the relying party's trust root `H4`, or the quote `H2`, yields countermodels.

Basis: normative (RFC 9334, NAL) + derived (mapping) + execution (Probe 1).

### 6. What attestation does not give, and how Ironclad Apps supply it

- Goal: "remote equivalence": a remote party "should receive the same sequence of messages as
  she would have received if she were communicating with the app's abstract state machine". The
  proof "covers the assembly code that gets executed", assumes hardware correct and "assumes
  nothing about the correctness of the compiler or runtime".
- Binding code to key: the Notary state machine holds a key pair "computed using the RSA key
  generation algorithm from the first consecutive sequence of random bytes read from the TPM", "a
  TPM, whose PCR 19 has been extended with the public part of that key pair", and a counter; on
  `connect, Nonce` it obtains "a quote ... over PCRs 17–19 and external nonce Nonce" and outputs
  the public key with the quote. The attestation "convinces a remote user that a notarization
  signed with the corresponding private key was generated by the Notary's code, which is
  equivalent to the abstract Notary state machine".
- Information flow: remote equivalence follows from functional correctness plus input and output
  noninterference around an abstract declassifier (Theorems 2–3, Corollary 1).
- Specification as trust anchor: "specs themselves are part of the TCB". In the source tree the
  Notary specification is 48 lines; its core predicate requires
  `out_state.counter == in_state.counter + 1`,
  `notary_statement_out == NotaryCounterAdvanceStatement(out_state.counter, message_in)` and
  `notary_attestation_out == RSASignature(common_state.key_pair, notary_statement_out)`.
- Threat model: software attackers who may control firmware, BIOS and peripherals before and
  after the app runs; "CPU, memory, and chipset are correct"; no physical attacks; liveness is
  not proved; the hardware model is "currently inadequate to prove the absence of side channels
  due to cache or timing effects".

Logical reading (derived): the quote gives `K_TPM says (code H is running ∧ H holds K_app)`; the
verification artifact gives `behaviours(H) ⊆ Spec`; together `K_app says m` implies `Spec`
permits `m`. Attestation alone delivers only the first conjunct.

Basis: documentation (paper) + source (`Notary.s.dfy`) + derived.

### 7. Transparency: from "says" to "said publicly, by time t"

Sigstore components at the pinned revisions:

- **Fulcio** issues short-lived certificates binding a client key to an OIDC identity after a
  proof of possession ("a signature of the `sub` claim" or a CSR). Identity facts are X.509
  extensions under `1.3.6.1.4.1.57264.1.*` (for example `.8` Issuer (V2), `.9` Build Signer URI,
  `.12` Source Repository URI). Certificates are logged: a precertificate carries the poison
  extension `1.3.6.1.4.1.11129.2.4.3` and the returned SCT "is a promise of inclusion in the log".
  Security model: "Fulcio assumes that a valid OIDC token is a sufficient 'proof of ownership'";
  "Clients MUST NOT trust certificates that are not in the log"; revocation is avoided because
  "what really matters for code signing is to know that an artifact was signed while the
  certificate was valid", checked against log inclusion time; "an entry in Rekor provides a
  single-party attestation that a piece of data existed prior to a certain time".
- **Rekor v1** returns an inclusion proof with a signed checkpoint and a
  `signedEntryTimestamp`: "Signature over the logID, logIndex, body and integratedTime".
- **Rekor v2** (tile-backed): `serve` mode "only supports `hashedrekord`
  (`HashedRekordLogEntryV002`)"; DSSE attestations are logged as a hash of the pre-authentication
  encoding; the server "blocks on returning a response until a checkpoint has been published whose
  tree size includes the newly uploaded entry"; it "will no longer return SignedEntryTimestamps or
  include integrated time", `integrated_time` "will always be `0`" and "clients MUST use an RFC3161
  timestamp"; root hash and tree size must be "parsed from a verified checkpoint"; witness
  co-signed checkpoints are planned ("we plan to support synchronous witnessing"). The
  public-good instance is re-sharded "approximately every 6 months" and discovered through
  TUF-distributed signing configuration and trust roots.
- **in-toto attestations** layer Predicate (typed metadata), Statement (binds subjects and
  predicate type), Envelope (authentication) and Bundle.

Merkle log mechanics (RFC 6962 §2.1, repeated in RFC 9162 §2.1): `MTH({}) = HASH()`,
`MTH({d0}) = HASH(0x00 || d0)`, `MTH(D_n) = HASH(0x01 || MTH(D[0:k]) || MTH(D[k:n]))` with `k`
the largest power of two smaller than `n`; the leaf/node prefix gives "second preimage
resistance"; a consistency proof has at most `ceil(log2(n)) + 1` nodes.

**Probe 2** implements MTH, PATH, PROOF and the RFC 9162 verification procedures:

- roots for tree sizes 0–8 equal the `RootHashes()` vectors of the Merkle library;
- all 36 inclusion proofs and all 28 consistency proofs for sizes up to 8 verify; no proof
  verifies for a wrong leaf or a wrong index;
- **rewrite is detected:** after entry 2 is replaced, no proof from the old size-4 head to the new
  size-8 head verifies;
- **split view is not detected locally:** two size-8 logs sharing six entries have different
  heads, each is consistent with the common size-6 head, and each proves inclusion of its own
  entry 7. Detection requires two parties to compare heads (gossip, witnesses, monitors).

Logical reading (derived): a log is a principal `L` asserting `included(e, i, root)`; consistency
proofs prevent `L` from retracting within one observer's history; witness co-signing replaces
`L` by the conjunction principal `L ∧ W1 ∧ … ∧ Wk`, whose statements, by ABLP's
`(A ∧ B) says s ≡ (A says s) ∧ (B says s)`, need every member. An inclusion *promise* (SCT,
Rekor v1 signed entry timestamp) is only `L says will-include(e)`.

Basis: source (pinned Sigstore and in-toto files) + normative (RFCs) + execution (Probe 2) + derived.

### 8. Capability hand-off protocols

**OCapN CapTP third-party handoff** (draft). Roles: *Gifter* shares a reference, *Receiver*
obtains it, *Exporter* hosts the object; three pairwise sessions. Each session has per-session
Ed25519 keys; a Public Identifier is the double SHA-256 of the serialized public key; a Session
ID is the double SHA-256 of `"prot0"` followed by the two sorted Public Identifiers. "When a
message is sent over a CapTP boundary that includes a Reference imported from a different
session, a handoff MUST occur."

| Step | Message | Signed with | Checked by |
|---|---|---|---|
| 1 | Gifter → Exporter: `op:deliver-only` to bootstrap object, `['deposit-gift, gift-id, reference]`, `gift-id` = 32 random bytes | session authentication only | Exporter holds the gift for later lookup by Gifter–Exporter session and `gift-id` (implied by step 3) |
| 2 | Gifter → Receiver: `<desc:handoff-give receiver-key exporter-location session gifter-side gift-id>` in a `desc:sig-envelope`, in place of the reference | Gifter's key from the **Gifter–Exporter** session | Receiver: "The only field that the Receiver can verify is the receiver-key" |
| 3 | Receiver → Exporter (connecting if needed): `withdraw-gift` with `<desc:handoff-receive receiving-session receiving-side handoff-count signed-give>` in a `desc:sig-envelope` | Receiver's key from the **Gifter–Receiver** session ("**NOT** the Exporter–Receiver session") | Exporter: find both sessions by Session ID; verify the give signature with the Gifter's key; verify the receive signature with `receiver-key` from the give; `handoff-count` "has NOT been used before in the Exporter–Receiver session" ("This protects against replay attacks") |
| 4 | Exporter → Receiver: promise resolves to the gift, immediately or when the deposit arrives (deposit and withdrawal "can happen in any order") | — | — |

Properties and observations:

- The give certificate is useless to an eavesdropper: redemption needs the private key matching
  `receiver-key`. "The Receiver should be the only party able to withdraw the gift left by the
  Gifter."
- The receive certificate ties two identities of the Receiver together (its Gifter–Receiver key
  signs a statement naming its Exporter–Receiver session), so the gift is delivered only on that
  session.
- Bearer path for bootstrapping: the bootstrap object's `fetch` method takes a `swiss-number`;
  sturdyref locators are `ocapn://<designator>.<transport>/s/<swiss-num>`. Here knowledge of
  the number is the authority.
- **Internal inconsistencies at the pinned revision:** `op:start-session` says, when
  constructing, "The `crypto-version` MUST be `Ed25519_SHA256`" and, when receiving, "MUST be
  equal to `Ed25519`"; the field description says a reused `handoff-count` "MUST not have been
  used" while the checking section says the handoff "should be aborted". The Endo package README
  describes itself as "a testbed for building specification consensus".

**Cap'n Proto level 3** (`rpc.capnp`): levels 0–4, where level 3 means that if Alice "sends Bob
... a capability pointing to Carol ... then Vat B will automatically form a direct connection to
Vat C rather than have requests be proxied through Vat A". `Provide` (introducer → host, naming
the recipient with `ThirdPartyToAwait`) and `Accept` (recipient → host, with
`ThirdPartyCompletion`); the recipient learns where to go from `ThirdPartyCapDescriptor { id
:ThirdPartyToContact; vineId :ExportId }`. The *vine* is a proxy through the introducer that
lower-level peers may simply call and that level-3 peers hold "until the `Accept` has completed".
An embargo identifier preserves call ordering across the path change. The three `ThirdParty*`
types are `AnyPointer`: authentication is delegated to the network, and the file sketches three
designs:

| Design in `rpc.capnp` comments | Redemption authority | Forwardable |
|---|---|---|
| `SimpleExample` | a `secretToken` (bearer) | yes, freely |
| `NoSecretsExample` | authenticated `VatId` plus a guessable nonce; "ONLY this Vat is permitted to redeem the nonce" | no |
| `PublicKeyExample` | public keys plus nonce; each forward adds a signature over `(introducer, nonce, to)` | yes, with a signature chain |

"A VatNetwork may choose not to allow forwarding if it doesn't want its security to be dependent
on secret bearer tokens nor cryptographic signatures."

Basis: source (pinned specifications; draft status noted).

### 9. Capability hand-off read through the logic

Derived correspondence:

| Protocol object | Formula |
|---|---|
| `desc:handoff-give` | `K_G^{GX} says (K_R^{GR} may withdraw gift-id at X, session GX)` — a restricted, single-object delegation |
| `desc:handoff-receive` | `K_R^{GR} says (session XR, side R, count c, redeems give)` — the delegate names the channel it will use |
| Exporter's rule | `K_G^{GX} controls` withdrawal of gifts deposited on session GX; `c` fresh in session XR |
| Bearer token / swiss number | `∀P. (P knows t) → (P ⇒ object)`: secrecy of `t` is the whole policy |
| Cap'n Proto `NoSecretsExample` | `Introducer says (VatId_R may accept nonce n)`, with `VatId_R` authenticated by the network |
| SPKI chain with `D = TRUE` | iterated restricted hand-off with tag and validity intersection |

Differences that survive the translation:

- **Where the proof is evaluated.** In authorization logics the resource's guard evaluates a
  proof over a chain of statements; in CapTP the exporter checks exactly two signatures and a
  counter, and the gifter's own right to the reference is established by the fact that the
  deposit arrives on a session that already imports it.
- **Designation and authority travel together** in the capability protocols (the certificate
  names the object by `gift-id`), which is the structural defence against the confused deputy
  (Hardy); a `says` credential can be presented in a context its issuer did not intend unless the
  statement names the request.
- **Revocation.** Logics revoke by time (`@ [u1,u2]`, epoch sub-principals, short-lived
  certificates); capability systems revoke by interposing a forwarder. The examined CapTP
  sections define reference counting (`op:gc-exports`) but no expiry for undelivered gifts.
- **Attenuation.** Restricted delegation (NAL), tag intersection (SPKI) and caveats (macaroons)
  narrow authority inside the credential; in object-capability systems attenuation is a new
  object.

Basis: derived.

### 10. Composition recipe for an attested remote foreign-function interface

Derived rule; each premise has a different trust root and a different failure mode.

```text
(1) endorsement    E says (K_att ⇒ E)                              restricted to measurement claims
(2) evidence       K_att says (runs(m) ∧ binds(m, K_ch) ∧ nonce = n)   n chosen by the caller, unused
(3) transparency   L says included(m ↦ σ, i, root)                 root consistent with a head the caller
                                                                   already holds, and seen by witnesses
(4) correctness    C says refines(m, σ)                            proof object or verified-build statement
(5) local policy   E controls runs, binds;  L controls included;  C controls refines
---------------------------------------------------------------------------------------------------
    K_ch ⇒ σ  on this channel, for the lifetime the caller assigns to n
    (calls arriving under K_ch may be typed by the interface σ)
```

| # | Boundary invariant | Violated when | Grounding |
|---|---|---|---|
| A1 | The guard's logic is constructive, or lacks Unit | classical prover accepts Escalation | Abadi; Probe 1 |
| A2 | Hand-off is stated by the grantor, about itself | accepting `A says (A ⇒ B)` | Probe 1 |
| A3 | Delegations are restricted to the claim shapes needed | full `K_att ⇒ E` lets a device speak for its vendor on anything | NAL restricted delegation |
| A4 | The channel key is inside the signed evidence | relay of a genuine quote over an attacker's channel | Ironclad PCR 19 binding; RFC 9334 §7.4 |
| A5 | Freshness is explicit and scoped | cached evidence or results reused beyond their epoch | RFC 9334 §10 |
| A6 | Mutable facts are evaluated at use, not at proof time | file or policy state changes after the proof | BL interpreted predicates; Nexus authorities |
| A7 | Measurement-to-specification maps are logged and the log head is cross-checked | split view serves a different `σ` to one caller | Probe 2 |
| A8 | Identity is not correctness | treating a valid quote as a proof of behaviour | Ironclad |
| A9 | Capability transfer is bound to recipient and session and is single-use | bearer token leaks; replayed handoff | OCapN handoff checks |
| A10 | The request is named in what is signed | confused deputy across contexts | Hardy; ABLP on quoting |

### 11. Failure catalogue

| Failure | Smallest instance | Remedy in the examined work |
|---|---|---|
| Escalation | classical logic + Unit | constructive logic (CDD, NAL, BL) |
| Inconsistent principal | `A says false` | effect confined to `A` (DEDUCE is local); avoid delegating both a predicate and its negation |
| Over-broad sub-principal | `A says F` attributed to every `A.τ` | naming convention for a distinguished sub-principal |
| Stale evidence | quote replayed | nonce, epoch identifier, epoch sub-principal |
| Proof over stale state | permission bit changed after proof | conditions carried in the capability and re-checked |
| Axiomatic-only trust | allow-list of hashes breaks on every update | analytic or synthetic labels |
| Log equivocation | two heads for one size | witness co-signatures, monitors, gossip |
| Promise mistaken for inclusion | SCT or signed entry timestamp accepted alone | require inclusion proof against a verified checkpoint |
| Hand-off replay | reused `handoff-count` | per-session uniqueness check |
| Hand-off theft | intercepted give certificate | redemption requires the receiver's session key |

Basis: derived from Sections 1–8.

## Boundaries

- **Not examined:** proof-carrying authentication's higher-order logic (Appel–Felten), Binder,
  SecPAL, delegation logic, DKAL, flow-limited authorization and belief semantics (cited for
  orientation only); Garg's thesis and the stateful extension of BL; the internals of Nexus and of
  the Ironclad toolchain; TPM, SGX, SEV-SNP, TDX, CCA or DICE evidence formats; RATS companion
  documents (CoRIM, attestation-result profiles, interaction models); the E language's original
  CapTP and Pluribus; Spritely Goblins; macaroons and Biscuit beyond the citation; the Trillian
  and Tessera log implementations; Cosign's verification code.
- **Not examined:** whether any implementation enforces the OCapN checks listed in Section 8;
  no CapTP or Cap'n Proto level-3 implementation was run.
- **Unknown:** how the OCapN group will resolve the two inconsistencies noted; lifetime and
  garbage collection of deposited but unredeemed gifts (not specified in the sections read);
  when Rekor v2 will return witness co-signed checkpoints.
- **Unknown:** whether a mechanized proof exists that the OCapN handoff achieves the
  restricted-delegation reading of Section 9. The correspondence is this report's.
- **Known not to apply:** ICL's Kripke completeness to second-order CDD or to NAL (Probe 1
  speaks about propositional ICL⇒ only); consistency proofs to split-view detection; attestation
  to behavioural correctness; Ironclad's guarantees to physical attackers, liveness, or timing
  channels.
- **Unsupported:** Rekor v2 entry types other than `hashedrekord` in `serve` mode; signed entry
  timestamps and integrated time in Rekor v2; forwarding of a third-party contact in Cap'n
  Proto's `NoSecretsExample` design.
- **Attractive but not established:** "validity on all models with at most three worlds proves
  a formula" (it does not; only countermodels are conclusive); "RATS specifies an authorization
  logic" (it specifies roles and messages; the logical reading is derived); "a transparency log
  prevents mis-issuance" (it makes it detectable).

## Evidence

Observed on 2026-11-19. Repository heads were resolved with `git ls-remote <url> HEAD` on that
date and files read at those revisions.

Papers and standards (bibliographic data confirmed against Crossref records on that date):

- Abadi, Burrows, Lampson, Plotkin. TOPLAS 15(4):706–734, 1993. doi:10.1145/155183.155225
  (Sections 2–3). Lampson, Abadi, Burrows, Wobber. TOCS 10(4), 1992. doi:10.1145/138873.138874.
- Abadi. Variations in Access Control Logic. DEON 2008. doi:10.1007/978-3-540-70525-3_9
  (Sections 1–4). Abadi. Access Control in a Core Calculus of Dependency. ICFP 2006.
  doi:10.1145/1159803.1159839.
- Garg, Abadi. FoSSaCS 2008. doi:10.1007/978-3-540-78499-9_16 (Sections 2–3, Figure 1,
  Definitions 1–2, Theorems 1–2, Corollaries 2–3).
- Garg, Pfenning. CSFW 2006. doi:10.1109/CSFW.2006.18 (Sections 1–2). Garg, Pfenning. IEEE S&P
  2010. doi:10.1109/SP.2010.28 (Sections II–III).
- Schneider, Walsh, Sirer. TISSEC 14(1), 2011. doi:10.1145/1952982.1952990 (Section 2). Sirer et
  al. SOSP 2011. doi:10.1145/2043556.2043580 (Sections 1–2).
- Hawblitzel et al. OSDI 2014,
  `https://www.usenix.org/system/files/conference/osdi14/osdi14-paper-hawblitzel.pdf` (Sections
  1–2, 4–5).
- RFC 9334 (§3.2, §4, §5, §7, §10); RFC 9711 (§4.1, §4.2); RFC 6962 §2.1; RFC 9162 §2.1.1–2.1.4;
  RFC 2693 §6.3.
- Cited for orientation: Appel, Felten. CCS 1999. doi:10.1145/319709.319718. Hardy. The Confused
  Deputy. doi:10.1145/54289.871709. Birgisson et al. Macaroons. NDSS 2014.
  doi:10.14722/ndss.2014.23212. Newman, Meyers, Torres-Arias. Sigstore. CCS 2022.
  doi:10.1145/3548606.3560596.

Source (repository @ revision: path):

- `ocapn/ocapn` @ `ebf68742a40a89fff4730886a8788c5fe1bc9b96`:
  `draft-specifications/CapTP Specification.md` (cryptography, lines 252–284; third-party
  handoffs, 285–389; bootstrap object, 391–465; `op:start-session`, 468–531 with the two
  `crypto-version` sentences at 499 and 521; descriptors, 865–1028);
  `draft-specifications/Locators.md` (lines 82–133).
- `endojs/endo` @ `679d9afaa4acd089f578055118b6711a22537f05`: `packages/ocapn/README.md`.
- `capnproto/capnproto` @ `20fe8fd325bf3825d6cdc3cf16bb263a4c142326`: `c++/src/capnp/rpc.capnp`
  (levels, lines 72–99; `Provide` 824–854; `Accept` 856–903; `ThirdPartyCapDescriptor`
  1215–1238; network-specific types and examples 1441–1610).
- `sigstore/rekor` @ `0baa39712ffa627b70756ea555193ec84bea4507`: `openapi.yaml` (lines 454–481,
  607–638).
- `sigstore/rekor-tiles` @ `accb9fd3dc86abb0dde10cb04bca36a99fe0b9e2`: `README.md` (lines 1–6,
  80–112); `CLIENTS.md` (lines 129–232).
- `sigstore/fulcio` @ `b01d056a925d1f15d1315676d454adf46b6b6629`:
  `docs/how-certificate-issuing-works.md`, `docs/oid-info.md`, `docs/certificate-specification.md`,
  `docs/security-model.md`.
- `transparency-dev/merkle` @ `c39fbf350a405f68571bf4c42a6a518eb0a46a4b`:
  `testonly/constants.go` (`LeafInputs`, `RootHashes`, `EmptyRootHash`).
- `in-toto/attestation` @ `50bf01716982189898823e90586075f37cd9bb7d`: `spec/README.md`.
- `microsoft/Ironclad` @ `2fe4dcdc323b92e93f759cc3e373521366b7f691`: `ironclad-apps/README.md`;
  `ironclad-apps/src/Dafny/Apps/Notary/Notary.s.dfy` (lines 38–48).

Execution. Python 3.13, standard library only; each script runs in under three seconds.

**Probe 1** — save as `/tmp/acl_kripke.py`, run `python3 /tmp/acl_kripke.py`. Semantics
(Garg–Abadi Definitions 1–2 and Section 3.3): a model is `(W, ≤, ρ, θ)` with `≤` a preorder,
`ρ(p)` upward closed and `θ(A)` an arbitrary set of worlds "invisible to A";
`w ⊨ s → t` iff every `w′ ≥ w` satisfying `s` satisfies `t`; `w ⊨ A says s` iff every `w′ ≥ w`
is in `θ(A)` or satisfies `s`; `w ⊨ A ⇒ B` iff every `w′ ≥ w` in `θ(A)` is in `θ(B)`.

```python
from itertools import product

MAXW = 3

def preorders(n):
    pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
    for bits in product((0, 1), repeat=len(pairs)):
        le = {(i, i) for i in range(n)} | {p for p, b in zip(pairs, bits) if b}
        if all((a, d) in le for (a, b) in le for (c, d) in le if b == c):
            yield [sum(1 << j for j in range(n) if (i, j) in le) for i in range(n)]  # up-sets

def symbols(f, atoms, prins):
    op = f[0]
    if op == "p":
        atoms.add(f[1])
    elif op == "says":
        prins.add(f[1]); symbols(f[2], atoms, prins)
    elif op == "sf":
        prins.update(f[1:])
    elif op in ("and", "or", "imp"):
        symbols(f[1], atoms, prins); symbols(f[2], atoms, prins)

def ev(f, up, full, rho, theta):    # truth set of f as a bitmask over worlds
    box = lambda x: sum(1 << w for w in range(len(up)) if up[w] & ~x & full == 0)
    op = f[0]
    if op == "p":   return rho[f[1]]
    if op == "bot": return 0
    if op == "and": return ev(f[1], up, full, rho, theta) & ev(f[2], up, full, rho, theta)
    if op == "or":  return ev(f[1], up, full, rho, theta) | ev(f[2], up, full, rho, theta)
    if op == "imp": return box((~ev(f[1], up, full, rho, theta) & full) | ev(f[2], up, full, rho, theta))
    if op == "says": return box(theta[f[1]] | ev(f[2], up, full, rho, theta))
    if op == "sf":  return box((~theta[f[1]] & full) | theta[f[2]])
    raise ValueError(op)

def check(f, max_w=MAXW):
    atoms, prins = set(), set()
    symbols(f, atoms, prins)
    atoms, prins, count = sorted(atoms), sorted(prins), 0
    for n in range(1, max_w + 1):
        full = (1 << n) - 1
        for up in preorders(n):
            upsets = [x for x in range(full + 1)
                      if all(up[w] & ~x & full == 0 for w in range(n) if x >> w & 1)]
            for rv in product(upsets, repeat=len(atoms)):
                for tv in product(range(full + 1), repeat=len(prins)):
                    count += 1
                    if ev(f, up, full, dict(zip(atoms, rv)), dict(zip(prins, tv))) != full:
                        return count, dict(worlds=n, up=up, rho=dict(zip(atoms, rv)),
                                           theta=dict(zip(prins, tv)))
    return count, None

P, Q, BOT = ("p", "p"), ("p", "q"), ("bot",)
says = lambda a, s: ("says", a, s)
imp = lambda *fs: fs[0] if len(fs) == 1 else ("imp", fs[0], imp(*fs[1:]))   # right-nested
conj = lambda *fs: fs[0] if len(fs) == 1 else ("and", fs[0], conj(*fs[1:]))
sf = lambda a, b: ("sf", a, b)                                              # a speaks for b
H1, H2, H3, H4 = says("E", sf("K", "E")), says("K", sf("M", "K")), says("M", P), imp(says("E", P), P)

FORMULAS = [
    ("unit            s -> A says s", imp(P, says("A", P))),
    ("cuc             A says (s->t) -> A says s -> A says t", imp(says("A", imp(P, Q)), says("A", P), says("A", Q))),
    ("idem            A says A says s -> A says s", imp(says("A", says("A", P)), says("A", P))),
    ("speaking-for    (A=>B) -> A says s -> B says s", imp(sf("A", "B"), says("A", P), says("B", P))),
    ("handoff         B says (A=>B) -> (A=>B)", imp(says("B", sf("A", "B")), sf("A", "B"))),
    ("trans           (A=>B) -> (B=>C) -> (A=>C)", imp(sf("A", "B"), sf("B", "C"), sf("A", "C"))),
    ("local-explosion A says false -> A says s", imp(says("A", BOT), says("A", P))),
    ("attested-chain  H1 & H2 & H3 & H4 -> p", imp(conj(H1, H2, H3, H4), P)),
    ("NO says-elim    A says s -> s", imp(says("A", P), P)),
    ("NO cross-explosion A says false -> B says false", imp(says("A", BOT), says("B", BOT))),
    ("NO escalation   A says s -> (s or A says false)", imp(says("A", P), ("or", P, says("A", BOT)))),
    ("NO commute      A says B says s -> B says A says s", imp(says("A", says("B", P)), says("B", says("A", P)))),
    ("NO self-grant   A says (A=>B) -> (A=>B)", imp(says("A", sf("A", "B")), sf("A", "B"))),
    ("NO pointwise    (A says s -> B says s) -> (A=>B)", imp(imp(says("A", P), says("B", P)), sf("A", "B"))),
    ("NO no-root      H1 & H2 & H3 -> p", imp(conj(H1, H2, H3), P)),
    ("NO no-quote     H1 & H3 & H4 -> p", imp(conj(H1, H3, H4), P)),
    ("NO excl-middle  s or (s -> false)", ("or", P, imp(P, BOT))),
]

for name, f in FORMULAS:
    n, cm = check(f)
    verdict = f"valid on all {n} models" if cm is None else f"COUNTERMODEL #{n}: {cm}"
    print(f"{name}\n    {verdict}; one-world models: {'valid' if check(f, 1)[1] is None else 'countermodel'}")
```

Observed output (`up[w]` is the bitmask of worlds above `w`; `rho`, `theta` are bitmasks):

```text
unit            s -> A says s
    valid on all 1092 models; one-world models: valid
cuc             A says (s->t) -> A says s -> A says t
    valid on all 5216 models; one-world models: valid
idem            A says A says s -> A says s
    valid on all 1092 models; one-world models: valid
speaking-for    (A=>B) -> A says s -> B says s
    valid on all 8520 models; one-world models: valid
handoff         B says (A=>B) -> (A=>B)
    valid on all 1924 models; one-world models: valid
trans           (A=>B) -> (B=>C) -> (A=>C)
    valid on all 15112 models; one-world models: valid
local-explosion A says false -> A says s
    valid on all 1092 models; one-world models: valid
attested-chain  H1 & H2 & H3 & H4 -> p
    valid on all 67344 models; one-world models: valid
NO says-elim    A says s -> s
    COUNTERMODEL #2: {'worlds': 1, 'up': [1], 'rho': {'p': 0}, 'theta': {'A': 1}}; one-world models: countermodel
NO cross-explosion A says false -> B says false
    COUNTERMODEL #3: {'worlds': 1, 'up': [1], 'rho': {}, 'theta': {'A': 1, 'B': 0}}; one-world models: countermodel
NO escalation   A says s -> (s or A says false)
    COUNTERMODEL #27: {'worlds': 2, 'up': [1, 3], 'rho': {'p': 1}, 'theta': {'A': 2}}; one-world models: valid
NO commute      A says B says s -> B says A says s
    COUNTERMODEL #82: {'worlds': 2, 'up': [1, 3], 'rho': {'p': 0}, 'theta': {'A': 2, 'B': 1}}; one-world models: valid
NO self-grant   A says (A=>B) -> (A=>B)
    COUNTERMODEL #3: {'worlds': 1, 'up': [1], 'rho': {}, 'theta': {'A': 1, 'B': 0}}; one-world models: countermodel
NO pointwise    (A says s -> B says s) -> (A=>B)
    COUNTERMODEL #7: {'worlds': 1, 'up': [1], 'rho': {'p': 1}, 'theta': {'A': 1, 'B': 0}}; one-world models: countermodel
NO no-root      H1 & H2 & H3 -> p
    COUNTERMODEL #8: {'worlds': 1, 'up': [1], 'rho': {'p': 0}, 'theta': {'E': 1, 'K': 1, 'M': 1}}; one-world models: countermodel
NO no-quote     H1 & H3 & H4 -> p
    COUNTERMODEL #2: {'worlds': 1, 'up': [1], 'rho': {'p': 0}, 'theta': {'E': 0, 'K': 0, 'M': 1}}; one-world models: countermodel
NO excl-middle  s or (s -> false)
    COUNTERMODEL #8: {'worlds': 2, 'up': [1, 3], 'rho': {'p': 1}, 'theta': {}}; one-world models: valid
```

**Probe 2** — save as `/tmp/merkle_probe.py`, run `python3 /tmp/merkle_probe.py`.

```python
import hashlib

H = lambda b: hashlib.sha256(b).digest()
leaf = lambda d: H(b"\x00" + d)
node = lambda l, r: H(b"\x01" + l + r)

def split(n):                       # largest power of two strictly smaller than n
    k = 1
    while k * 2 < n:
        k *= 2
    return k

def mth(d):                         # RFC 6962 section 2.1
    if not d:
        return H(b"")
    if len(d) == 1:
        return leaf(d[0])
    k = split(len(d))
    return node(mth(d[:k]), mth(d[k:]))

def path(m, d):                     # inclusion proof PATH(m, D_n)
    if len(d) == 1:
        return []
    k = split(len(d))
    return path(m, d[:k]) + [mth(d[k:])] if m < k else path(m - k, d[k:]) + [mth(d[:k])]

def proof(m, d, b=True):            # consistency proof PROOF(m, D_n) = SUBPROOF(m, D_n, true)
    if m == len(d):
        return [] if b else [mth(d)]
    k = split(len(d))
    return proof(m, d[:k], b) + [mth(d[k:])] if m <= k else proof(m - k, d[k:], False) + [mth(d[:k])]

def verify_inclusion(index, size, leaf_hash, pth, root):        # RFC 9162 section 2.1.3.2
    if index >= size:
        return False
    fn, sn, r = index, size - 1, leaf_hash
    for p in pth:
        if sn == 0:
            return False
        if fn & 1 or fn == sn:
            r = node(p, r)
            while not fn & 1 and fn != 0:
                fn >>= 1; sn >>= 1
        else:
            r = node(r, p)
        fn >>= 1; sn >>= 1
    return sn == 0 and r == root

def verify_consistency(first, second, first_hash, second_hash, cpath):   # RFC 9162 section 2.1.4.2
    if not cpath:
        return False
    cpath = list(cpath)
    if first & (first - 1) == 0:
        cpath.insert(0, first_hash)
    fn, sn = first - 1, second - 1
    while fn & 1:
        fn >>= 1; sn >>= 1
    fr = sr = cpath[0]
    for c in cpath[1:]:
        if sn == 0:
            return False
        if fn & 1 or fn == sn:
            fr, sr = node(c, fr), node(c, sr)
            while not fn & 1 and fn != 0:
                fn >>= 1; sn >>= 1
        else:
            sr = node(sr, c)
        fn >>= 1; sn >>= 1
    return fr == first_hash and sr == second_hash and sn == 0

D = [bytes.fromhex(x) for x in
     ("", "00", "10", "2021", "3031", "40414243", "5051525354555657",
      "606162636465666768696a6b6c6d6e6f")]
ROOTS = """e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d
fac54203e7cc696cf0dfcb42c92a1d9dbaf70ad9e621f4bd8d98662f00e3c125
aeb6bcfe274b70a14fb067a5e5578264db0fa9b51af5e0ba159158f329e06e77
d37ee418976dd95753c1c73862b9398fa2a2cf9b4ff0fdfe8b30cd95209614b7
4e3bbb1f7b478dcfe71fb631631519a3bca12c9aefca1612bfce4c13a86264d4
76e67dadbcdf1e10e1b74ddc608abd2f98dfb16fbce75277b5232a127f2087ef
ddb89be403809e325750d3d263cd78929c2942b7942a34b77e122c9594a74c8c
5dc9da79a70659a9ad559cb701ded9a2ab9d823aad2f4960cfe370eff4604328""".split()

print("1. known-answer roots, sizes 0..8:", all(mth(D[:n]).hex() == ROOTS[n] for n in range(9)))
incl = [(m, n) for n in range(1, 9) for m in range(n)]
ok = sum(verify_inclusion(m, n, leaf(D[m]), path(m, D[:n]), mth(D[:n])) for m, n in incl)
bad_leaf = sum(verify_inclusion(m, n, leaf(b"evil"), path(m, D[:n]), mth(D[:n])) for m, n in incl)
bad_idx = sum(verify_inclusion((m + 1) % n, n, leaf(D[m]), path(m, D[:n]), mth(D[:n]))
              for m, n in incl if n > 1)
print(f"2. inclusion: {ok}/{len(incl)} verify; wrong leaf accepted: {bad_leaf}; wrong index accepted: {bad_idx}")
cons = [(m, n) for n in range(2, 9) for m in range(1, n)]
ok = sum(verify_consistency(m, n, mth(D[:m]), mth(D[:n]), proof(m, D[:n])) for m, n in cons)
print(f"3. consistency: {ok}/{len(cons)} verify")
R = D[:2] + [b"rewritten"] + D[3:]          # entry 2 replaced after the size-4 head was published
print("4. rewrite: proof 4->8 from rewritten log accepted against old head:",
      verify_consistency(4, 8, mth(D[:4]), mth(R), proof(4, R)))
A, B = D, D[:6] + [b"fork-7", b"fork-8"]    # two size-8 logs sharing six entries
h6, ha, hb = mth(D[:6]), mth(A), mth(B)
print("5. split view: heads equal:", ha == hb,
      "| 6->8 consistent on A:", verify_consistency(6, 8, h6, ha, proof(6, A)),
      "| on B:", verify_consistency(6, 8, h6, hb, proof(6, B)),
      "| B's entry 7 under head B:", verify_inclusion(6, 8, leaf(B[6]), path(6, B), hb),
      "| under head A:", verify_inclusion(6, 8, leaf(B[6]), path(6, B), ha))
```

Observed output:

```text
1. known-answer roots, sizes 0..8: True
2. inclusion: 36/36 verify; wrong leaf accepted: 0; wrong index accepted: 0
3. consistency: 28/28 verify
4. rewrite: proof 4->8 from rewritten log accepted against old head: False
5. split view: heads equal: False | 6->8 consistent on A: True | on B: True | B's entry 7 under head B: True | under head A: False
```

## Revalidation

- **Logic facts.** Re-run Probe 1. The verdict of each row (valid or countermodel, and the
  one-world column) must not change; these depend only on the published semantics. To test a new
  axiom or policy shape, add a tuple to `FORMULAS`; raise `MAXW` to 4 for more assurance on
  "valid" rows (run time grows quickly).
- **Merkle facts.** Re-run Probe 2 and compare line 1 against `testonly/constants.go` of the
  Merkle library at the revision of interest. Lines 4 and 5 are properties of the RFC algorithms
  and should be stable.
- **OCapN.** `grep -n "crypto-version" "draft-specifications/CapTP Specification.md"` shows whether
  the mismatch persists; diff the sections "Third Party Handoffs", "desc:handoff-give" and
  "desc:handoff-receive" for changes to signing keys or to the `handoff-count` rule. Any change to
  which key signs the receive certificate changes row 3 of the table in Section 8 and the
  reading in Section 9.
- **Cap'n Proto.** `grep -n "ThirdParty" c++/src/capnp/rpc.capnp` to confirm the three types are
  still `AnyPointer` and the three example designs are unchanged.
- **Sigstore.** In `rekor-tiles`, `grep -n -i "SignedEntryTimestamp\|witness\|integrated_time"
  CLIENTS.md`; in `rekor`, `grep -n "signedEntryTimestamp" openapi.yaml`; in `fulcio`, re-read
  `docs/security-model.md`. A shipped witness requirement would change the "planned" wording in
  Section 7.
- **RATS.** RFC text is immutable; check only for updating or obsoleting documents.
- **Derived mappings** (Sections 5, 9, 10) have no mechanical check; re-derive them if a logic
  with different `says` axioms is adopted, starting from the rows of Probe 1 that the new logic
  would change.
