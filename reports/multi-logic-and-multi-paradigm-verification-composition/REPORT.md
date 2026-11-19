# Multi-Logic and Multi-Paradigm Verification Composition: Semantic Bridges, Paired Contract Export, and Hyperproperty Limits

## Summary

- **Composition is semantic, not syntactic.** Theorems from an SMT-backed
  auto-active verifier, a step-indexed separation logic, an abstract
  interpreter, a bounded model checker and a verified compiler differ in
  quantifier structure (Findings 1). They compose only after each is
  interpreted in one shared object: one semantics of the *linked* program, one
  observation alphabet, one linking operator, and one accounting of which
  module may read or write which state.
- **Step-indexed logics export meta-level facts only at closed-program
  adequacy.** Iris's `wp_strong_adequacy_gen` concludes a meta-level `φ` from
  weakest preconditions for *all* initial threads plus a concrete execution
  `nsteps n (es, σ1) κs (t2, σ2)`, stripping a number of laters computed from
  `n`. CCR's Wrapper Elimination Theorem needs a closed program and one global
  PCM. RustHornBelt's adequacy covers closed λRust programs and leaves the
  SMT-side verifier trusted. A later-guarded fact at a fixed step index is not
  a safety fact (Findings 2).
- **A compiled theorem alone is not a reusable contract.** From
  `Sem_tgt(t) ≤ π(P)` and `Sem_tgt(t) ≤ π(Sem_src(s))` one cannot derive
  `Sem_src(s) ≤ P`: compilation refines, and the codec `π` may identify source
  behaviours the source logic distinguishes. The source contract is
  recoverable exactly when compilation is exact *and* `π` is order-reflecting,
  hence injective. Sound separate verification exports a pair: a contract at
  the source-level interface plus a refinement certificate, either
  `(Sem_src(s) ≤ P, Sem_tgt(t) ≤ π(Sem_src(s)))` or an open,
  context-parametric simulation as in CompCertO's `compose_simulation` and
  CCR's `refines2_add` (Findings 7).
- **Refinement preserves hypersafety over a shared alphabet; it does not
  preserve possibilistic policies or policies over erased observations.**
  Clarkson and Schneider prove that every safety hyperproperty, hence every
  k-safety hyperproperty, is subset closed, and that refinement is valid for
  exactly the subset-closed hyperproperties. A verified compiler breaks
  constant-time guarantees because (a) its inclusion theorem ranges over
  input/output events, not leakage, or (b) the source policy was possibilistic
  and nondeterminism was resolved in a secret-dependent way. Preservation
  needs a relational, leakage-carrying criterion (Findings 8).
- **Termination, frames and axioms are separate side conditions.** Total
  correctness needs every callee to be total and proof-only code must be
  total; an analyzer's environment assumptions are contracts on the other
  modules; axiom bases must be unioned in one host logic (Findings 3 to 5).
- **Coordinates per publisher metadata.** CompCertO: PLDI 2021. Constant-time
  CompCert: Barthe, Blazy, Grégoire, Hutin, Laporte, Pichardie, Trieu.
  Conditional Contextual Refinement: Song, Cho, Lee, Hur, Sammler, Dreyer.
- **Executable evidence.** `support/verify_heterogeneous_composition_laws.py`
  checks 31 finite-model laws and witnesses (Findings 9).

## Applicability

This report is a comparison and synthesis. The subjects in `REPORT.json` play
three roles:

1. **Sources of theorem statements** that are quoted and compared: Iris,
   CompCert, CompCertO (branch `compcerto`), the Conditional Contextual
   Refinement artifact, the Interaction Trees library, and the papers that
   introduce them.
2. **Sources of paradigm-specific side conditions**: the Dafny reference
   manual, the Verus and Creusot guides, the Kani tutorial, the IKOS analyzer
   manual, and Creusot's standard-library specifications.
3. **A consumer architecture**: `joshlf/anneal` at the pinned revision. There
   `trusted/lean/Trusted.lean` is a 19-line module that starts from `prelude`,
   imports `Init.NotationExtra` and contains only a docstring;
   `trusted/lean/foundation-lock.json` admits the axioms `Classical.choice`,
   `Quot.sound` and `propext`; the relations `Abstracts` and `Compiles` and
   the statement `Trusted.CrateTheorem` are described in
   `docs/architecture.md` but have no Lean definition under `trusted/lean/`.
   Statements about them below are statements about documentation.

Scope and limits:

- The findings concern *semantic and program-logic* composition. Syntactic
  proof export and checker accounting are in
  `cross-prover-interoperability-verified-checkers-and-tcb-accounting` and
  `cross-prover-guarantee-composition-and-native-checker-soundness`.
- The order-theoretic vocabulary is defined in place (Findings 6, 7).
  Mechanised codec degeneracy and step-budget results are in
  `anneal-behavior-codec-and-partial-compile-refinement-algebra`; logic
  translation and incompleteness limits are in
  `anneal-universal-algebra-institutions-and-incompleteness-bounds`.
- Rust verifier comparisons, leakage-model catalogues, property-transfer
  matrices and the Iris liveness literature are in
  `rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers`,
  `side-channel-freedom-foundations-and-leakage-contracts-1996-2026`,
  `observable-behavior-property-transfer-and-anneal-statement-forms` and
  `iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic`.
- Exact observation covers the quoted definitions, theorem statements and
  documentation at the pinned revisions and the probe's finite models. The
  laws in Findings 7 and 8 are derived, with proofs given. No cited tool was
  executed; concurrency, weak memory, probabilistic hyperproperties and
  speculative leakage are out of scope.

## Findings

### 1. What each paradigm's theorem states

The "crossing point" is the only place where another paradigm can soundly
consume the result.

| Paradigm (example) | Judgment delivered | Quantifies over | Termination | Crossing point |
| --- | --- | --- | --- | --- |
| Auto-active SMT verification (Dafny, Verus, Creusot, Flux) | Verification conditions valid in classical first-order logic with theories, as decided by an external solver | Inputs satisfying `requires`; callees replaced by contracts | Per tool and code mode (Findings 5) | A first-order contract over the tool's own model of the language; the verifier is trusted |
| Step-indexed separation logic (Iris) | `WP e {{ Φ }}` in a logic indexed by remaining steps and by ghost resources from one global functor `Σ` | Step indices, frames, invariant-respecting interference | None in `adequate` | Closed-program adequacy yielding a meta-level `φ` |
| Refinement with separation-logic conditions (CCR) | `M_tgt ⊑ctx ⟨S ⊢ M_src⟩` | All linking contexts | Traces distinguish termination, silent divergence, error, partial termination | Wrapper Elimination Theorem for a closed program |
| Abstract interpretation (IKOS) | Concrete behaviours covered by an abstract fixpoint; no alarm means absence of the checked runtime errors | Executions permitted by the analyzer's environment assumptions | Not addressed | The assumption list becomes a contract on every other module |
| Bounded model checking (Kani) | Checked properties hold on all executions of a harness within the unwinding bound | Inputs of one closed harness | Bounded | A closed-harness statement, not a contract for arbitrary callers |
| Verified compilation (CompCert) | `backward_simulation (Csem.semantics p) (Asm.semantics tp)` | Whole programs, or separately compiled units linked at source level | Preserved for safe sources (`Diverges`, `Reacts`) | Inclusion of observable-event behaviours for sources that do not go wrong |
| Open verified compilation (CompCertO) | `forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp)` and the backward counterpart | Open components relative to a simulation convention | As above | Horizontal composition with any component related by the same convention |

Details:

- **Iris.** `adequate s e1 σ1 φ` has two fields: `adequate_result` (a value
  `v2` of the main thread in state `σ2` satisfies `φ v2 σ2`) and
  `adequate_not_stuck`. Neither mentions termination.
- **CompCert.** `program_behavior` has constructors `Terminates : trace -> int`,
  `Diverges : trace`, `Reacts : traceinf`, `Goes_wrong : trace`;
  `behavior_improves beh1 beh2` is
  `beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2`;
  `backward_simulation_same_safe_behavior` states that if every source
  behaviour is `not_wrong` then every target behaviour is a source behaviour.
- **Kani.** The tutorial states that bounding "means we may no longer be
  proving as much as we originally hoped"; with too low a bound an "unwinding
  assertion" fails and other properties become "undetermined".

Basis: source (Iris `adequacy.v`; CompCert `Behaviors.v`, `Compiler.v`;
CompCertO `Compiler.v`) + documentation (Kani tutorial, IKOS manual, CCR
paper) + derived (the classification).

### 2. Step-indexed logics cross a boundary only at closed-program adequacy

**The Iris statement** (abridged; `Λ` is the language, `Σ` the global functor
of ghost-state cameras):

```coq
Lemma wp_strong_adequacy_gen hlc Σ Λ `{!invGpreS Σ} s es σ1 n κs t2 σ2 φ
        (num_laters_per_step : nat → nat) :
  (∀ `{Hinv : !invGS_gen hlc Σ},
      ⊢ |={⊤}=> ∃ stateI Φs fork_post state_interp_mono, ...
       stateI σ1 0 κs 0 ∗
       ([∗ list] e;Φ ∈ es;Φs, WP e @ s; ⊤ {{ Φ }}) ∗
       (∀ es' t2', ... -∗ |={⊤,∅}=> ⌜ φ ⌝)) →
  nsteps n (es, σ1) κs (t2, σ2) →
  φ.
```

Its proof opens with `apply (pure_soundness (PROP:=iPropI Σ))` and
`apply (laterN_soundness _ (steps_sum num_laters_per_step 0 n + 1))`. Hence:

1. The premise supplies a weakest precondition for **every** initial thread;
   there is no slot for code that lacks a `WP` proof.
2. The conclusion `φ` is a meta-level proposition. Nothing step-indexed or
   resource-indexed is exported.
3. The number of laters removed is a function of the execution length `n`:
   the collapse of `▷` is an argument about one finite prefix at a time.
4. All ghost state of all components lives in the single `Σ` fixed at the
   adequacy call.

The weakest precondition consumes laters per physical step: for each
`prim_step`, `wp_pre` requires
`£ (S (num_laters_per_step ns)) ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=> ...`
before the recursive occurrence `wp E e2 Φ`.

**Why a fixed index is not enough.** In the standard model (resources aside) a
proposition is a set of step indices closed under decreasing the index. There (probe section D,
indices `0..6`): `P ∨ ¬P` is valid only for the two index-independent
propositions (D1); `▷P ⇒ P` is valid only for `P = True` (D2);
`(▷P ⇒ P) ⇒ P` is valid for every `P` (D3, Löb induction); and `▷ⁿ False`
holds at exactly the indices below `n` (D4). D4 is the precise sense in which
adequacy erases step-indexing: a contradiction under `n` laters is visible
only to an observer who supplies more than `n` steps, and only a closed
program has a well-defined supply of steps. Operationally (C1): over all 1000
closed three-state transition systems, `∀n. wp n` is equivalent to "no
reachable state is stuck and every reachable final state satisfies the
postcondition", while 184 unsafe systems satisfy `wp k` for some fixed
`k ≥ 1`.

**Consequences for a mixed-logic link.**

- An Iris triple for a library can be consumed by another Iris proof over the
  same `Λ` and `Σ`, or discharged by adequacy once *all* code has a `WP`. A
  client verified by an SMT-backed tool contributes none.
- The sound route is to prove once that the other tool's judgment *implies* a
  `WP` in the same logic, as RustHornBelt does for RustHorn-style
  specifications (Findings 6).
- An invariant that holds only "later" cannot be re-exported as an
  unconditional first-order assumption. Only pure facts obtained under
  adequacy are index-free.

**The same shape in CCR.** Theorem 4.1 (Wrapper Elimination Theorem): for a
global PCM `Σ`, wrapped abstractions `⟨S ⊢αi Ai⟩` and an initial resource `α`
to `main` satisfying its precondition with `V(α + α1 + ... + αn)`, *if
`A1 ∘ ... ∘ An` is a closed program* then
`⟨S ⊢α1 A1⟩ ∘ ... ∘ ⟨S ⊢αn An⟩ ⊑beh A1 ∘ ... ∘ An`. The artifact's
`adequacy_type` concludes
`refines_closed (Mod.add_list mds_tgt0) (Mod.add_list mds_src)`, where
`refines_closed md_tgt md_src` is
`Beh.of_program (ModL.compile md_tgt) <1= Beh.of_program (ModL.compile md_src)`,
under a hypothesis that the initial resource satisfies `main`'s precondition.

Basis: source (Iris `adequacy.v`, `weakestpre.v`; CCR `ems/ModSem.v`,
`spc/Hoare.v`) + documentation (CCR paper, Theorem 4.1) + execution (probe
C1a, C1b, D1 to D4) + derived (the numbered facts and consequences).

### 3. Frames, footprints and environment assumptions

| Paradigm | Frame notion | What it assumes of other modules |
| --- | --- | --- |
| Separation logic (Iris, CCR) | Ownership of resources in a partial commutative monoid; disjointness is validity of the composed resource | Compatible resources from the *same* algebra; invariants re-established at interaction points |
| Ownership-typed SMT verification (Verus, Creusot, Flux) | The language's ownership and borrowing discipline; linearly typed ghost permissions (Verus); current and prophesied final values of mutable borrows (Creusot) | All code obeys the discipline, or carries a trusted or separately proved specification |
| Abstract interpretation (IKOS) | A fixed list of environment assumptions | The listed behaviours of unknown code |
| Open verified compilation (CompCertO) | A simulation convention whose Kripke world relates source and target memories | Callers and callees related by the same convention |

IKOS "aims at proving the absence of runtime errors in C and C++ programs"
under an "Analysis Assumptions" list that is a representative concrete
contract: "The program is single-threaded", "The program does not receive
signals", "Extern functions (without implementation) do not update global
variables", "Extern functions can write on their pointer parameters, but only
with one level of indirection", "Extern functions do not call user-defined
functions (no callbacks)", "Assembly codes are treated as extern function
calls". A separate
"soundness analysis" (`-a=sound`) "checks for instructions that could make the
analysis unsound". Flux states its soundness as "well-borrowed evaluations of
well-typed programs do not get stuck" under the Stacked Borrows model. The CCR
paper notes that its simulation re-establishes the relational invariant at
every function call unless a call is known not to be re-entrant.

Two composition failures follow:

- **Footprint overlap (C5).** A caller verified under "the call leaves my
  stable cells unchanged" and a callee verified under "I own and may overwrite
  my cells" are each correct alone. Over all 64 pairs of (callee write set,
  caller-stable set) on three cells, the caller's assertion survives in
  exactly the 27 disjoint pairs. The side condition is footprint
  disjointness, which neither proof states in a form the other tool checks.
- **Re-entrancy during a broken invariant (C4).** A library whose invariant
  holds at call boundaries but is broken between two raw writes is safe in
  isolation; a callback between the writes observes the broken state. The
  IKOS "no callbacks" assumption and the CCR invariant discipline exclude the
  same hazard by different means.

Basis: documentation (IKOS manual; Flux abstract; Verus abstract; CCR paper)
+ source (CompCertO `callconv`) + execution (probe C4, C5) + derived.

### 4. Proof foundations: axiom bases and what may cross

| Development | Axioms recorded at the examined revision |
| --- | --- |
| CompCert | `Behaviors.v` uses `classic`; "The proof requires classical logic: the axiom of excluded middle and an axiom of description" |
| CompCertO | `compose_transf_c_program_correct` applies `Axioms.functional_extensionality` |
| Interaction Trees | README: UIP (`eq_rect_eq`) for `eqit_inv_Vis`; `functional_extensionality`; excluded middle and a choice axiom in the trace theory of `itree-extra`; exported `bisimulation_is_eq : t1 ≅ t2 -> t1 = t2` |
| CCR artifact | README: functional choice, CompCert-style system-call semantics, propositional extensionality, proof irrelevance, functional extensionality, UIP, constructive definite description, excluded middle, `bisimulation_is_eq` |
| Anneal foundation lock | `Classical.choice`, `Quot.sound`, `propext` |
| SMT-backed verifiers | Classical validity as judged by the solver; per RustHornBelt the verifier implementation "remains part of the trusted computing base" |

1. **Classical reasoning is the norm in these developments.** The practical
   mismatch is whether the *union* of the axiom sets is acceptable to, and
   auditable by, the host that states the final theorem. A host that already
   admits choice and propositional extensionality takes on nothing new by
   accepting a classically derived pure fact; a host admitting less must
   re-prove it or enlarge its audited set.
2. **Classical reasoning does not extend to step-indexed propositions.**
   Excluded middle fails for index-dependent propositions (D1); a
   solver-derived case split is importable only for pure facts.
3. **Solver validity is a trust assumption unless replayed** in the host;
   certificate formats are outside this report's scope.

Basis: source (CompCert `Behaviors.v`; CompCertO `Compiler.v`; Anneal
`foundation-lock.json`) + documentation (Interaction Trees and CCR READMEs;
RustHornBelt paper) + execution (probe D1) + derived (the observations).

### 5. Partial correctness, total correctness and divergence

- **Dafny.** "Loops and compiled methods (but not functions and not ghost
  methods, including lemmas) can be specified to be possibly non-terminating.
  This is done by declaring the method or loop with `decreases *`, which causes
  the proof of termination to be skipped." Also: "A method that contains a
  possibly non-terminating loop or a call to a possibly non-terminating method
  must itself be declared as possibly non-terminating."
- **Verus.** "While recursive `spec` functions and `proof` functions must
  always terminate ..., nontermination is allowed for exec functions." The
  default `decreases` requirement on `exec` code "only guarantees that the
  present function will terminate, on the assumption that all the callees also
  terminate, so it should be treated as a lint, not a complete guarantee of
  termination".
- **Creusot.** "Termination of logic functions (in Pearlite) is crucial for
  soundness. Otherwise you could prove `false`", illustrated by a `#[logic]`
  function `falso` with `#[ensures(false)]` that calls itself; for ordinary
  functions "By default, we prove *partial correctness*", and
  `#[check(terminates)]` "changes the goal to *total correctness*".
- **Iris.** `adequate` has no termination field.
- **CompCert, CCR, Interaction Trees.** Behaviours and traces distinguish
  termination from silent divergence; CCR adds "partial termination";
  interaction-tree equivalence `eutt` is weak bisimulation and the paper
  proves "termination-sensitive correctness" of its example compiler.

Composition rules (derived, with finite witnesses):

| Caller claim | Callee claim | Linked claim | Evidence |
| --- | --- | --- | --- |
| Partial | Partial | Partial | Monotonicity of safety; C1a |
| Total | Total | Total | Induction on the callee's measure |
| Total against the callee's contract | Partial only | Partial only | C6: the caller is total when the call is one contract step; the linked system diverges yet satisfies `wp n` at every `n` |
| Logical lemma (proof-only code) | Possibly diverging | Unsound | C1c: a self-loop satisfies `{True} f {False}` at every index; read as `True ⇒ False` it proves anything (Creusot's `falso`) |

A termination claim crosses a boundary only if the exporting claim is total
*and* its callees' totality is accounted for.

Basis: documentation (Dafny reference manual; Verus and Creusot guides;
Interaction Trees abstract; CCR paper) + source (Iris `adequate`; CompCert
`program_behavior`; Interaction Trees `Eqit.v`) + execution (probe C1a, C1c,
C6) + derived.

### 6. Bridge architectures compared

| Architecture | Shared semantic object | Horizontal / vertical composition | How a foreign proof enters | Residual limits |
| --- | --- | --- | --- | --- |
| CompCertO | Open transition systems `semantics liA liB` over language interfaces, related by simulation conventions `callconv` | `compose_simulation` (same convention at both interfaces) / `compose_forward_simulations` | As an open transition system at the C-level interface that compiled code simulates through `cc_compcert` | Conventions are Kripke relations, not functions; interfaces are C and assembly calls |
| Conditional Contextual Refinement | Executable Module Semantics on interaction trees; behaviours are trace sets | `refines2_add` / `refines2_PreOrder` | As a wrapped abstraction `⟨S ⊢ M⟩` with separation-logic conditions over one global PCM | Conditions are erased only for a closed program (Findings 2) |
| Interaction Trees | Coinductive trees `itree E R` over an event signature; handlers interpret events into monads | Signature sums and `mrec` / equational reasoning up to `eutt` | Each logic must be proved sound for the tree denotation | A semantic substrate, not a program logic; axioms per Findings 4 |
| RustHornBelt | One Iris model of λRust interpreting both the unsafe library proof and the first-order client specification | Typing rules of the type-spec system, each proved sound semantically | The client verifier's judgment is modelled by `L \| T ⊢ I ⊣ r. L' \| T' ⇝ Φ` | The real client verifier stays trusted; λRust only; some APIs not covered |
| Institutions | Signatures, sentences, models, and satisfaction invariant under change of notation | Gluing theories along signature morphisms / institution morphisms | By a morphism under which reuse of a prover is sound | Logical translation only: no linking, step indexing or resources |
| Order-theoretic codec chain | Posets of behaviours with monotone maps between languages | Monotone contexts / transitivity | As an over-approximation `Sem_src(s) ≤ π_v(Sem_v(v))` | Vacuous unless maps are constrained (Findings 7) and the alphabet carries the property (Findings 8) |

**CompCertO.** A language interface is
`{ query : Type; reply : Type; entry : query -> val }`. A transition system
`lts liA liB state` receives questions `query liB` (`initial_state`), asks
`query liA` (`at_external`), resumes on `reply liA` (`after_external`) and
answers `reply liB` (`final_state`). A convention `callconv li1 li2` supplies
worlds `ccworld` and world-indexed relations `match_senv`, `match_query`,
`match_reply`. The clause that makes open composition work is

```coq
fsim_match_external:
  forall i s1 s2 q1, match_states i s1 s2 -> at_external L1 s1 q1 ->
  exists w q2, at_external L2 s2 q2 /\ match_query ccA w q1 q2 /\
    match_senv ccA w se1 se2 /\
  forall r1 r2 s1', match_reply ccA w r1 r2 -> after_external L1 s1 r1 s1' ->
  exists i' s2', after_external L2 s2 r2 s2' /\ match_states i' s1' s2';
```

every outgoing source question is matched by a related target question, and
the simulation continues for *all* related answers. Horizontal composition:

```coq
Lemma compose_simulation {li1 li2} (cc: callconv li1 li2) L1a L1b L1 L2a L2b L2:
  forward_simulation cc cc L1a L2a ->
  forward_simulation cc cc L1b L2b ->
  compose L1a L1b = Some L1 ->
  compose L2a L2b = Some L2 ->
  forward_simulation cc cc L1 L2.
```

The compiler's convention is
`cc_compcert := cc_cklrs^{*} @ wt_c @ lessdef_c @ cc_c_locset @ cc_locset_mach @ cc_mach_asm @ cc_asm vainj`.
`clight_semantic_preservation` gives, for `match_prog p tp`, both
`forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp)`
and the matching `backward_simulation`; `compose_transf_c_program_correct`
combines it with `compose_simulation` and assembly linking for two separately
compiled units. Per the paper's abstract, CompCertO "extends the correctness
theorem of CompCert to characterize compiled program components directly in
terms of their interaction with each other".

**Conditional Contextual Refinement.** In the artifact, `refines2 md_tgt md_src`
states that for every list of context modules `ctx` the behaviours
(`Beh.of_program`) of the compiled link of `ctx` with `md_tgt` are included in
those of `ctx` with `md_src`, and
`refines2_add : refines2 t0 s0 -> refines2 t1 s1 -> refines2 (t0 ++ t1) (s0 ++ s1)`.
The paper's wrapper `⟨S ⊢ M⟩` "converts `M` into a module that
'self-enforces' the pre- and postconditions of `S` at the points where `M`
interacts with its program context". Because the refinement is an inclusion
of trace sets under all contexts, Findings 8 applies to it unchanged.

**Interaction Trees.** `itreeF` has constructors `RetF (r : R)`,
`TauF (t : itree)` and `VisF {X} (e : E X) (k : X -> itree)`; `itree` is
coinductive with the single field `_observe : itreeF itree`.
`eq_itree := eqit false false`, `eutt := eqit true true` (ignoring `Tau` steps
on both sides) and `euttge := eqit true false`.
`interp (h : E ~> M) : itree E ~> M` folds a handler over a tree for any monad
with an iteration operator.

**RustHornBelt and Creusot.** The paper presents "the first machine-checked
proof of soundness for RustHorn-style verification which supports giving FOL
specs to safe APIs implemented with unsafe code", extending RustBelt's model
"to reason not only about safety but also functional correctness" via
"parametric prophecies". Its adequacy theorem "says that a complete (i.e.,
closed) and semantically well-typed Rust program will never encounter
undefined behavior (formalized as a 'stuck state') under any execution trace".
Stated limits: it "does not constitute an automated verification framework in
itself. One must link it with a separate RustHorn-style verifier for safe Rust
code (e.g., Creusot), and the implementation of that verifier remains part of
the trusted computing base"; "there remains a formal gap between RustHornBelt
and Creusot" (surface Rust versus λRust; WhyML functions versus predicate
transformers); no specifications for `Rc`, `Arc`, `RefCell` and `RwLock`,
"largely due to a technical issue related to step-indexing"; and the weakest
precondition is strengthened with time receipts so that the n-th step can
strip n laters, because prophecy tokens of nested mutable references "may be
buried under statically unbounded number of laters".

Creusot's guide states that "mutable borrows are handled via **prophecies**":
a borrow carries its current value and "the _last_ value written in the
borrow, called the **prophecy**", and when the borrow is dropped "Creusot adds
the assumption `current == prophecy`". In its standard-library specifications,
inside an `extern_spec!` block, `Vec::push` is declared without a body as
`#[check(terminates)] #[ensures((^self)@ == self@.snoc(v))] fn push(&mut self, v: T);`.
The contract is attached to an external function, not proved against its
implementation at that site; RustHornBelt-style reasoning is the kind of
argument that could justify it.

The probe reproduces the paper's `max_mut` example at finite scale: a client
condition quantified over all prophesied final values, a raw-pointer library
that satisfies its prophetic specification when each prophecy is resolved to
the value observed when the borrow ends, and all 49 closed runs satisfying the
assertion (C2a). The client condition stays valid for two incorrect libraries
whose semantic check and closed runs fail (C2b); an exists-quantified prophecy
accepts a false claim (C3); and the incorrect library is detected only at a
step index that reaches the assertion (C7).

**Institutions.** The abstract requires "a satisfaction relation between
models and sentences that is consistent under change of notation" and lists
"conditions under which it is sound to use a theorem prover for one
institution on theories from another". This fits verifiers that describe the
same models in different notations; it supplies no linking operator, alphabet
or adequacy theorem.

**The order-theoretic chain.** Give each language a poset of behaviours in
which smaller means more refined and undefined behaviour is the top element.
A compiler certificate is `Sem_tgt(t) ≤ π_c(Sem_src(s))`; a verifier, lifter
or abstract interpreter certificate is `Sem_src(s) ≤ π_v(Sem_v(v))`. With
`π_c` monotone they compose into `Sem_tgt(t) ≤ π_c(π_v(Sem_v(v)))`, one chain
instead of a two-legged diagram. The Anneal architecture document uses the
same two directions: a backward simulation `Abstracts A C` for verification
lowering (every trace of the concrete captured program is matched by the
abstract program, whose freedom from undefined behaviour implies the concrete
program's), and "`Compiles` for compilation lowering".

**Related bridges (abstracts only).** DimSum treats languages as "independent
modules communicating via events"; Melocoton is a program logic for OCaml and
C "on top of the Iris separation logic framework".

Basis: source (CompCertO, CCR artifact, Interaction Trees, Creusot at pinned
revisions) + documentation (paper abstracts, RustHornBelt full text, Creusot
guide, Anneal `docs/architecture.md`) + execution (probe C2, C3, C7) + derived
(the comparison table and the chain).

### 7. Forgetful codecs and paired contract export

**Setting.** `(B_src, ≤)` and `(B_tgt, ≤)` are posets of behaviours.
`π : B_src → B_tgt` is monotone. A linking context is a monotone map
`C : B_src → W_src` into whole-program behaviours with codec
`π_w : W_src → W_tgt`. For a callee with source `s`, binary `t` and contract
`P ∈ B_src`, and a client verified against `P` with goal `G ∈ W_src`:

```text
CR  (compilation refinement)   Sem_tgt(t) ≤ π(Sem_src(s))
TT  (target theorem)           Sem_tgt(t) ≤ π(P)
SC  (source contract)          Sem_src(s) ≤ P
CV  (client verified)          C[P] ≤ G
SW  (source-level whole claim) C[Sem_src(s)] ≤ G
```

**Proposition 7.1 (the pair implies the target theorem and the whole
claim).** `SC ∧ CR ⟹ TT` and `SC ∧ CV ⟹ SW`.
*Proof.* `Sem_tgt(t) ≤ π(Sem_src(s)) ≤ π(P)` by monotonicity of `π`;
`C[Sem_src(s)] ≤ C[P] ≤ G` by monotonicity of `C`. ∎

**Proposition 7.2 (the target theorem does not imply the source contract).**

(a) *Exact compilation.* Suppose `Sem_tgt(t) = π(Sem_src(s))`. Then `TT ⟹ SC`
for all denotable `Sem_src(s)` and all `P` if and only if `π` is
order-reflecting on those behaviours (`π(A) ≤ π(B) ⟹ A ≤ B`). An
order-reflecting map is injective, since `π(A) = π(B)` gives `A ≤ B` and
`B ≤ A`.
*Proof.* If `π` reflects order, `π(Sem_src(s)) = Sem_tgt(t) ≤ π(P)` gives `SC`.
Conversely pick `A ≰ B` with `π(A) ≤ π(B)`, a source with `Sem_src(s) = A`,
its exact binary, and `P = B`. ∎

(b) *Refining compilation.* Suppose some correct binary strictly refines,
`Sem_tgt(t) < π(Sem_src(s))`, and `π` is the identity. Then `P := Sem_tgt(t)`
satisfies `TT` with equality and violates `SC`. A different correct binary of
the same source may violate `P`. ∎

For codecs that act on sets of outcomes by direct image, order reflection is
exactly injectivity on outcomes (probe A1: 6 of the 27 codecs on three
outcomes). Exhaustively over three source outcomes, three target outcomes and
all union-homomorphic clients (A4): the pair is sound in all 2151 instances;
3240 of 6633 instances satisfying `CR ∧ TT ∧ CV` violate `SW`; and the
violations split into 1152 with exact compilation and a forgetful codec, 540
with an injective codec and refining compilation, the remainder with both, and
**none** with exact compilation and an injective codec.

**Two concrete witnesses.**

- *Forgetful codec (A2).* The source distinguishes an uninitialised result
  from an initialised `0`; the binary materialises both as byte `0x00`. The
  callee's source semantics is `{uninit}`, the contract is `{init 0}`. `TT`
  holds (`{0x00} ⊆ {0x00}`); `SC` fails. A client verified against the
  contract branches on the result, which at source level is undefined
  behaviour for `uninit`, so `C[Sem_src(s)]` is the top behaviour and any
  whole-program compilation is correct, including one that emits a failing
  binary. Every exported certificate is true and the linked binary is wrong.
- *Refining compilation (A3).* The callee's source may return `1` or `2`; one
  binary returns `1`; the exported theorem says "returns `1`". A client
  asserts the result is `1`. Recompiling the same source to the equally
  correct binary that returns `2` breaks the client.

**Proposition 7.3 (an open certificate is the alternative).** Let `Ct` be the
compiled client, monotone, and suppose the lax square `Ct[π(X)] ≤ π_w(C[X])`
holds for every source behaviour `X`. Then `TT ∧ CV ⟹ Ct[Sem_tgt(t)] ≤ π_w(G)`
without `SC`.
*Proof.* `Ct[Sem_tgt(t)] ≤ Ct[π(P)] ≤ π_w(C[P]) ≤ π_w(G)`. ∎

The lax square is the algebraic content of CompCertO's `fsim_match_external`
together with `compose_simulation`: the compiled client must be correct
against *every* target callee related by the convention to *some* source-level
behaviour, not merely against the compilation of one particular source callee.
Exhaustively on two outcomes (A5): with the square, all 56 instances are
correct; without it there are 196 violations. The A2 witness is precisely a
violation of the square at the shared byte: the inlining compiler used
source-level knowledge of the callee, whereas a client compiled separately
against the binary interface satisfies the square and the linked binary is
correct (A5b), even though the source-level whole claim `SW` remains false.

**What to export.** Either form is a pair consisting of a contract stated at
the source-level interface and a refinement certificate:

| Export | Supports | Does not support |
| --- | --- | --- |
| `SC` and `CR` | Source-level modular proofs; any correct recompilation; whole-program or inlining compilation; `TT` by Proposition 7.1 | Callees with no source in the client's language |
| `TT` plus a context-parametric certificate for every client (Proposition 7.3) | Foreign or hand-written callees; binary-level linking | Any use of the callee's *source* by the client's compiler or verifier (inlining, generic instantiation, link-time optimisation) |
| `TT` alone | A statement about one binary run in isolation | Modular reuse of either kind |

The second row is the pattern of CompCertO and CCR, where the contract is
itself an open component; the first is required whenever downstream
compilation units re-instantiate upstream source or intermediate code.

Basis: derived (Propositions 7.1 to 7.3, proofs given) + execution (probe A1
to A5b) + source (CompCertO `fsim_match_external`, `compose_simulation`; CCR
`refines2_add`).

### 8. Hyperproperties across refinement

**Definitions and theorems, from Clarkson and Schneider.** A system is a set of
traces; a trace property is a set of traces; a hyperproperty is a set of sets
of traces. "Specification S1 refines specification S2 ... iff every behavior
permitted by S1 is also permitted by S2"; with an interpretation function `α`
on traces, "Trace property P1 refines P2 under interpretation α ... iff
α(P1) ⊆ P2", and `H1 HREF_α H2` iff `α(H1) ⊆ H2`. Satisfaction and refinement
agree for a hyperproperty exactly when it is subset closed: "the set of
hyperproperties with which refinement works is the set SSC of subset-closed
hyperproperties". Then:

- **Theorem 1.** `SHP ⊂ SSC`: every safety hyperproperty is subset closed.
  Observational determinism "is subset closed ... but ... is not a lifted
  trace property"; generalized noninterference "is not subset closed: a system
  containing traces t1 and t2 and interleaved trace t3 might satisfy GNI, but
  the subset containing only t1 and t2 would not".
- **k-safety and Theorem 2.** A k-safety hyperproperty is a safety
  hyperproperty "in which the bad thing never involves more than k traces";
  it reduces to a safety property of the k-fold product `S^k`.
- **Theorem 3.** `PIF ⊂ LHP`: possibilistic information-flow policies "are
  therefore never hypersafety".
- The introductory example: a system that "nondeterministically chooses to
  output 0, 1 or the value of a secret bit h" satisfies "The possible output
  values are independent of the values of secrets", but "one refinement ... is
  the system that always outputs h, and this system does not satisfy the
  security policy". The set of hyperproperties for which refinement is valid
  "includes the safety hyperproperties".

**Proposition 8.1 (what inclusion preserves).** If `α(Beh(tgt)) ⊆ Beh(src)`
and `H` is subset closed with `Beh(src) ∈ H`, then `α(Beh(tgt)) ∈ H`. So every
k-safety hyperproperty of the source, *stated over the alphabet in which the
inclusion holds*, transfers to the `α`-image of the target, including
for-all/for-all noninterference and a for-all/for-all formulation of constant
time ("any two runs with equal public inputs have equal leakage") when leakage
is in that alphabet. *Proof.* Definition of subset closure. ∎ (Probe B2: 289
system/refinement pairs over eight traces, no violation.)

**Two ways a correct compiler nevertheless breaks a security policy.**

1. *The policy is possibilistic.* A for-all/exists policy ("for every public
   input, the set of possible leaks does not depend on the secret") tolerates
   secret-independent nondeterminism in the source and is not subset closed: a
   compiler that resolves the nondeterminism as a function of the secret is a
   correct refinement and violates it. B1 is the Clarkson-Schneider example;
   B3 finds 96 violating refinements among 121 input-total ones, with witness
   "leak jitter `{0,1}` resolved to `leak = sec`". The jittering source does
   *not* satisfy the for-all/for-all formulation, so this never contradicts
   Proposition 8.1.
2. *The policy is about observations the refinement erases.* CompCert's
   theorem concerns `program_behavior` values built from `trace` and
   `traceinf`, where `trace := list event` and `event` has exactly the
   constructors `Event_syscall`, `Event_vload`, `Event_vstore` and
   `Event_annot`. Branch outcomes and ordinary (non-volatile) memory accesses
   are not events, so the inclusion holds for an `α` that forgets leakage and
   Proposition 8.1 yields only policies over input/output events. B4a: equal
   input/output behaviours, a constant-time source, a target whose leak equals
   the secret, and target leak traces that are not a subset of the source's;
   B4b counts 48 such pairs among the 16 × 16 leak assignments. In the terms
   of Findings 7 this is a forgetful codec: the property lives in the part of
   the behaviour that `π` discards. Moreover `behavior_improves` permits any
   target behaviour after a source `Goes_wrong`, so even input/output policies
   transfer only for sources that do not go wrong.

The sentence "trace refinement destroys 2-safety" is therefore accurate only
in one of these two readings. Where a for-all/for-all 2-safety property is
stated over an alphabet shared by source and target and the inclusion holds on
that alphabet, Theorem 1 guarantees preservation. Counterexamples in which a
compiler turns secret-independent timing jitter into secret-dependent timing
belong to the first reading: their source policy is possibilistic.

**What restores preservation of leakage policies.** A pass is *relational for
leakage* if, for every two inputs with equal public parts, equal source
leakage implies equal target leakage. This 2-trace condition transfers
for-all/for-all constant time (B5b: 144 relational pairs with a constant-time
source, no leaky target) and holds for every pass whose target leakage is a
secret-independent function of source leakage (B5a: all 12544 pairs of a
source and a per-event leakage transformer); a pass whose target leak depends
on the secret fails it (B5c). Lock-step two-execution simulation diagrams are
a proof technique for establishing the condition pass by pass.

The constant-time CompCert paper follows this route. Its abstract describes
the method: "we modify the CompCert compiler to eliminate sources of potential
leakage. Then, we instrument the operational semantics of CompCert
intermediate languages so as to be able to capture cryptographic
constant-time. Finally, we prove that the modified CompCert compiler preserves
constant-time". Both parts of the diagnosis are visible: the alphabet is
extended by instrumentation, and preservation is a separate theorem rather
than a corollary of the existing inclusion.

**Property classes.** Abate et al. study "robustly preserving various classes
of trace properties such as safety, of hyperproperties such as
noninterference, and of relational hyperproperties such as trace
equivalence", where robust means "against arbitrary adversarial contexts". A
cross-language certificate should name the property class it preserves.
Across logics, a relational proof for module A and single-trace proofs for
module B yield a hyperproperty of the link only if B's contribution to the
relevant observation is covered relationally or shown independent of secrets.

Basis: normative (Clarkson and Schneider, definitions and Theorems 1 to 3) +
source (CompCert `Behaviors.v`, `Events.v`) + documentation (constant-time
CompCert abstract; Abate et al. abstract) + execution (probe B1 to B5c) +
derived (Proposition 8.1 and the two-way diagnosis).

### 9. Executable finite-model evidence

`support/verify_heterogeneous_composition_laws.py` is a standard-library
Python 3.10+ script with no inputs. It prints one line per check and exits 0
only if all 31 hold; `support/expected_output.txt` is its exact output. Each
check is exhaustive over a small finite universe or confirms a specific
witness.

| Group | Checks | Established at finite scale |
| --- | --- | --- |
| A codecs | A1, A2, A3, A4a-c, A5, A5b | Order reflection equals injectivity for image codecs; the witnesses of Findings 7; soundness of the pair; insufficiency of the target theorem; sufficiency of the lax square |
| B hyperproperties | B1, B2, B3, B4a-b, B5a-c | The Clarkson-Schneider example; subset closure of for-all/for-all constant time; failure of possibilistic noninterference; the alphabet gap; the relational condition |
| C step indexing and linking | C1a-c, C2a-b, C3 to C7 | Adequacy as quantification over all indices; insufficiency of a fixed index; vacuity of partial correctness on divergence; prophetic client plus semantic library specification; quantifier discipline; re-entrancy; frames; partial versus total; closed-system adequacy |
| D step-indexed propositions | D0 to D4 | Model closure; failure of excluded middle; non-eliminability of later; Löb induction; `▷ⁿ False` |

Modelling limits: behaviours are finite sets, contexts are union-homomorphisms
and undefined behaviour is a top element; traces in group B are triples
`(public, secret, leak)` or short leak sequences without time or probability;
group C systems have three states, the prophecy example uses integers in
`[-3, 3]`, and assertion failure is a stuck state (the RustHornBelt paper
likewise notes "Abortion is implemented just as a stuck term"); group D uses
indices `0..6`.

Basis: execution (Python 3, 31 of 31 checks pass, exit status 0, about 0.3 s)
+ derived (the reading of each check).

### 10. Acceptance checklist for a cross-paradigm boundary

Each item needs an explicit answer that some party checks:

1. **Semantics.** One semantics of the linked program, with each tool's model
   proved to refine or abstract it.
2. **Alphabet.** The observations each certificate ranges over; a property
   over erased observations is not transferred (Findings 7, 8).
3. **Direction.** Downward refinement (compiler) or upward abstraction
   (verifier, analyzer, lifter); chains compose only as
   `target ≤ ... ≤ source ≤ ... ≤ specification`.
4. **Export form.** A source-interface contract plus a refinement certificate;
   mandatory in the `SC` form if clients re-instantiate callee source.
5. **Adequacy.** The closed-program theorem that discharges step and resource
   indices, with all code proved in one logic and resource algebra
   (Findings 2).
6. **Frames and re-entrancy.** Disjoint footprints; invariants re-established
   before any call that can re-enter (Findings 3).
7. **Environment assumptions.** Every analyzer's assumption list satisfied by
   all other modules.
8. **Termination.** Which claims are total, whether all their callees are, and
   that proof-only code is total (Findings 5).
9. **Property class.** Trace property, subset-closed hyperproperty,
   possibilistic policy or relational property, and whether each certificate
   preserves that class (Findings 8).
10. **Foundations and trust.** The union of axioms, and which solvers,
    generators and translators are trusted rather than checked (Findings 4).

Basis: derived (from Findings 1 to 9).

## Boundaries

- **not examined**: the full text of the constant-time CompCert paper (only
  its bibliographic record and abstract were retrieved), so its proof
  techniques, compiler modifications and leakage model are not characterised
  here. Likewise abstract-only: the CompCertO paper, Abate et al., DimSum,
  Melocoton, Flux, Verus, and Goguen and Burstall; bibliographic record only:
  Astrée.
- **not examined**: executing any cited tool or rebuilding any cited Coq or
  Lean development; concurrency, weak memory, speculative execution,
  probabilistic information flow, and liveness beyond the partial-versus-total
  distinction.
- **not examined**: the axiom footprint of Iris, the joint consistency of the
  listed axiom sets in any one proof assistant, and how Creusot documents the
  trust status of `extern_spec!` contracts (Findings 6 rests on the bodiless
  declaration in the source file).
- **unknown**: whether the quoted Iris files are byte-identical at the pinned
  commit. They were retrieved by branch name on the observation date, when the
  commit feed reported the listed revision as the branch tip; retrieval by
  commit hash was not possible through the available fetch path.
- **unknown**: whether one resource algebra can be embedded soundly in both a
  step-indexed logic and the linear ghost types of an SMT-backed verifier so
  that ownership could cross the boundary directly.
- **unknown**: how Anneal's `Abstracts` and `Compiles` relations are defined
  in Lean; at the pinned revision they appear only in documentation.
- **known not to apply**: Proposition 8.1 to possibilistic policies (Theorem 3
  of Clarkson and Schneider) and to properties over observations outside the
  inclusion's alphabet; Proposition 7.2(a)'s recovery of the source contract
  when compilation is not exact or the codec is not order-reflecting.
- **unsupported**: RustHornBelt provides no specifications for `Rc`, `Arc`,
  `RefCell` and `RwLock` and does not cover surface Rust or the implementation
  of a client verifier, by the paper's own statement; IKOS gives no guarantee
  for programs that violate its stated assumptions.
- **Stronger conclusions not established**: that any existing system composes
  all five paradigms under one machine-checked theorem; that the probe's
  finite checks prove the general propositions (those are proved in the text);
  that a source-level constant-time proof implies anything about a binary
  produced by an unmodified verified compiler.

## Evidence

All retrievals were made on 2026-11-19.

**Bibliographic records** (Crossref metadata per DOI: authors, title, venue,
pages, date). Clarkson and Schneider, J. Computer Security 18(6):1157-1210,
2010, 10.3233/JCS-2009-0393. Barthe, Blazy, Grégoire, Hutin, Laporte,
Pichardie and Trieu, PACMPL 4(POPL), 2020, 10.1145/3371075. Xia, Zakowski, He,
Hur, Malecha, Pierce and Zdancewic, PACMPL 4(POPL), Article 51, 2020,
10.1145/3371119. Koenig and Shao, PLDI 2021, pp. 1095-1109,
10.1145/3453483.3454097. Matsushita, Denis, Jourdan and Dreyer, PLDI 2022,
pp. 841-856, 10.1145/3519939.3523704. Song, Cho, Lee, Hur, Sammler and Dreyer,
PACMPL 7(POPL), Article 39, 2023, 10.1145/3571232. Goguen and Burstall,
J. ACM 39(1):95-146, 1992, 10.1145/147508.147524. Abate, Blanco, Garg, Hritcu,
Patrignani and Thibault, CSF 2019, 10.1109/CSF.2019.00025. Also confirmed by
DOI: DimSum (10.1145/3571220), Melocoton (10.1145/3622823), Flux
(10.1145/3591283), Verus (10.1145/3586037), and Blanchet et al., "A static
analyzer for large safety-critical software" (10.1145/781131.781153).

**Full texts read**: Clarkson and Schneider (introduction p. 1159; Section 2.6
pp. 1166-1167; Theorem 1 in Section 3; k-safety and Theorem 2 in Section 4;
Theorem 3 in Section 5); RustHornBelt (abstract, Sections 2.1, 3.1, 3.5, 4.2
and its discussion of limitations); Conditional Contextual Refinement
(abstract, Sections 2 to 4, Theorems 3.1, 4.1, 4.2). Abstracts only: the
remaining works.

**Pinned revisions.**

```text
AbsInt/CompCert                2685140bf72c959446981fb99b5e44a8975021bc
CertiKOS/compcert (compcerto)  87a62d95cd24a44e3ecd5fefddc70a969a881bcb
alxest/CCR                     edcda8faae6580581e8e5b28050d755bcb29f55f
DeepSpec/InteractionTrees      284d42248a3c5517cff9f582e335fcee2f6bdc1f
creusot-rs/creusot             dc57a795e1b457ea54c3080f4663ded461db6843
NASA-SW-VnV/ikos               ac7f7c1738976cabc58c6a53413df6e458995c38
dafny-lang/dafny               8c137ba351c60a521cfb122011770fdbea9a0453
verus-lang/verus               a95764f23c6876b47500beda6118e2d142a87cc3
model-checking/kani            c25a57bcbf8c8af41617e7171a535a3518ce514a
joshlf/anneal                  08f1184dce262d8d3ab610d4becedc3a0ae4486c
iris/iris (master, reported)   2fe2f450add5678d9a2492343c638ccdb428a677
```

**Source locations** (path: lines at the revision above):

| Repository | Path: lines | Content |
| --- | --- | --- |
| CompCert | `common/Behaviors.v`: 41-45, 81-82, 158-160, 493-496, 519-522 | `program_behavior`; `behavior_improves`; classical-logic remark; the two backward-simulation behaviour theorems |
| CompCert | `common/Events.v`: 64-68, 73; `driver/Compiler.v`: 446-449, 466-472 | `event`, `trace`; `transf_c_program_correct`, `separate_transf_c_program_correct` |
| CompCertO | `common/LanguageInterface.v`: 11-16, 48-63; `common/Smallstep.v`: 478-493, 536-552, 817-837, 956-959 | `language_interface`, `callconv`; `lts`, `semantics`, `fsim_properties`, `forward_simulation`, `compose_forward_simulations` |
| CompCertO | `common/SmallstepLinking.v`: 334-343; `driver/Compiler.v`: 407-413, 695-699, 809-838, 846-868 | `compose`, `compose_simulation`; `cc_compcert`, `clight_semantic_preservation`, commented-out separate-compilation theorem, `compose_transf_c_program_correct` |
| CCR | `ems/ModSem.v`: 919-937, 1046-1063; `spc/Hoare.v`: 216-224; `README.md`: 98-119, 179-198 | `refines`, `refines2`, `refines_closed`, `refines2_add`; `adequacy_type`; paper-to-Coq map and axiom list |
| Interaction Trees | `theories/Core/ITreeDefinition.v`: 30-42; `theories/Eq/Eqit.v`: 90-105, 139-151; `theories/Interp/Interp.v`: 78-87; `README.md`: 43-91 | `itreeF`, `itree`; `eqitF`, `eutt`; `interp`; axiom list |
| Creusot | `creusot-std/src/std/vec.rs`: 93, 117-119; `guide/src/representation_of_types/mutable_borrows.md`: 3-11; `guide/src/termination.md`: 5-27 | `extern_spec!` and `Vec::push`; prophecies; termination |
| IKOS | `analyzer/README.md`: 45, 252, 527-548 | purpose; soundness analysis; analysis assumptions |
| Dafny | `docs/DafnyRef/Specifications.md`: 124-131 | `decreases *` |
| Verus | `source/docs/guide/src/exec_termination.md`: 3-5 | termination of `exec` code |
| Kani | `docs/src/tutorial-loop-unwinding.md`: 30-50 | bounded proofs, unwinding assertions |
| Anneal | `trusted/lean/Trusted.lean`: 1-19; `trusted/lean/foundation-lock.json`: 2-15; `docs/architecture.md`: 134-136, 166-186, 238-243 | prelude-only root; axiom list; documented `Trusted.CrateTheorem`, `Abstracts`, `Compiles` |
| Iris | `iris/program_logic/adequacy.v`: 107-148, 180-188; `iris/program_logic/weakestpre.v`: 65-84 | `wp_strong_adequacy_gen` and the start of its proof; `adequate`; `wp_pre` |

The Iris identity is weaker than the others (see Boundaries); the statement
in Findings 2 is reproduced from the retrieved text for comparison.

**Execution.** `python3 -B support/verify_heterogeneous_composition_laws.py`
with CPython 3 on Linux: 31 checks, all `PASS`, exit status 0, about 0.3
seconds; deterministic output preserved in `support/expected_output.txt`.

**Synthesis versus source facts.** Quoted definitions, theorem statements and
documentation sentences are source facts. The propositions, tables and
checklist are this report's synthesis.

## Revalidation

- **Probe.** Run `python3 -B support/verify_heterogeneous_composition_laws.py`
  and compare with `support/expected_output.txt`. A pass re-establishes only
  the finite models.
- **Iris adequacy shape.** In `iris/program_logic/adequacy.v` check that
  `wp_strong_adequacy_gen` still takes a `WP` for every element of `es` and an
  `nsteps n` execution and concludes a bare `φ`, and that `adequate` has only
  the result and not-stuck fields. A termination field, or a premise admitting
  unverified threads, would change Findings 1, 2 and 5.
- **CompCertO composition.** Check `compose_simulation` in
  `common/SmallstepLinking.v` (same convention on both interfaces) and
  `cc_compcert` and `clight_semantic_preservation` in `driver/Compiler.v`.
- **CompCert alphabet.** Check in `common/Events.v` that `event` still has
  only system-call, volatile-access and annotation constructors. If leakage
  events are added, the second failure mode of Findings 8 needs re-examination
  for that revision.
- **CCR.** Check `refines2` and `refines2_add` in `ems/ModSem.v` and that
  `adequacy_type` in `spc/Hoare.v` concludes `refines_closed`.
- **Tool documentation.** Re-read four short passages: Dafny
  `docs/DafnyRef/Specifications.md` on `decreases *`; Verus
  `exec_termination.md`; Creusot `guide/src/termination.md`; IKOS
  `analyzer/README.md`, "Analysis Assumptions". Check that Creusot still
  specifies `Vec::push` inside `extern_spec!` with a `^self` postcondition.
- **Anneal.** List `trusted/lean/` at the revision of interest; if Lean
  definitions of the refinement relations appear, re-check them against
  Propositions 7.1 to 7.3.
- **No cheap revalidation exists** for the claim that no examined system
  composes all paradigms under one theorem; that requires repeating the
  survey.
