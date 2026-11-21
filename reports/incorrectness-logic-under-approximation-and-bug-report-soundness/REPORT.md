# Incorrectness logic and bug-report soundness: what over- and under-approximate results license (Lean 4 toy formalization)

## Summary

This package is a self-contained, Mathlib-free Lean 4 formalization (namespace `Toy.IL`, Lake
library `ToyIL`) of two kinds of program triple over a small nondeterministic command language
with a normal (`ok`) and an erroneous (`er`) exit, following the generic fragment of O'Hearn's
*Incorrectness Logic* (POPL 2020): Hoare triples `{P} c {e : Q}` (over-approximate: every
`e`-outcome from a `P` state satisfies `Q`) and incorrectness triples `[P] c [e : Q]`
(under-approximate: every `Q` state is an `e`-outcome from some `P` state). Its 19 results fix
which conclusions each kind of result licenses. A valid incorrectness error triple with a
nonempty post is a true positive (some run from some pre state errs), but one with an empty post
is not a safety proof. A Hoare error triple with post `False` is exactly a safety proof, but a
nonempty Hoare error post, or an over-approximate summary composed with a true-positive check, is
not a bug report. A sound under-approximate analysis's alarm is a reachable error while its
silence is not safety, and the converse holds for sound over-approximate analyses. The
incorrectness proof rules are sound and relatively complete, while the conjunction rule is
unsound in general (it is sound exactly for backward-unique commands). Manifest errors, which
are reachable from every initial state, survive extension of the state by an untouched frame
component and every program context that reaches them.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Results (each is a theorem about the toy semantics described under Applicability):

1. **hoare-consequence-strengthen-pre-weaken-post** (theorem, T0, definitional): For every command c and exit kind e: if {P} c {e : Q} is a valid Hoare triple, P' ⊆ P and Q ⊆ Q', then {P'} c {e : Q'} is valid (strengthen the pre, weaken the post).
2. **il-consequence-weaken-pre-strengthen-post** (theorem, T0, definitional): For every command c and exit kind e: if [P] c [e : Q] is a valid incorrectness triple, P ⊆ P' and Q' ⊆ Q, then [P'] c [e : Q'] is valid (weaken the pre, strengthen the post — the reverse of Hoare consequence).
3. **exact-post-duality-and-or-symmetry** (characterization, T0, definitional): For a fixed pre P, command c and exit kind e: an assertion Q is both a Hoare post and an incorrectness post iff Q equals post c e P pointwise; two incorrectness posts both hold iff their disjunction is an incorrectness post, [P]c[e:Q1] ∧ [P]c[e:Q2] ↔ [P]c[e:Q1 ∨ Q2]; two Hoare posts both hold iff their conjunction is a Hoare post, {P}c{e:Q1} ∧ {P}c{e:Q2} ↔ {P}c{e:Q1 ∧ Q2}.
4. **il-hoare-agreement-and-denial** (theorem, T0, definitional): Agreement: if [U] c [e : U'] is a valid incorrectness triple, U ⊆ O, and {O} c {e : O'} is a valid Hoare triple, then U' ⊆ O'. Denial (contrapositive): if [U] c [e : U'] is a valid incorrectness triple, U ⊆ O, and U' ⊄ O', then {O} c {e : O'} is not valid.
5. **hoare-invalid-iff-il-singleton-outside-post** (characterization, T0, definitional): A Hoare triple {P} c {e : Q} is invalid iff there is a single state t with t ∉ Q such that the incorrectness triple [P] c [e : {t}] is valid.
6. **il-error-triple-nonempty-post-true-positive** (theorem, T0, definitional): If [P] c [er : Q] is a valid incorrectness triple and Q is nonempty, then some run of c from a state in P terminates with an error in a state in Q (a true positive relative to P). Consequently an error is reachable from P iff some valid incorrectness error triple [P] c [er : Q] has nonempty Q, and c is safe from P iff every valid incorrectness error triple from P has an empty post.
7. **safety-iff-hoare-error-triple-false** (characterization, T0, definitional): c is safe from P (no run from P terminates with an error) iff the Hoare error triple {P} c {er : False} is valid. Stating safety of c needs only this error-exit triple, and no normal-exit triple about c can replace it: {True} error() {ok : False} is valid although error() is unsafe.
8. **il-error-triple-empty-post-does-not-imply-safety** (impossibility, T0, definitional): A valid incorrectness error triple with empty post, [P] c [er : False], does not imply that c is safe from P: such triples are valid for every P and c, including error(), which is unsafe.
9. **hoare-summaries-do-not-imply-reachable-error** (impossibility, T0, definitional): Over-approximate (Hoare) summaries do not establish reachable errors. (a) A valid Hoare error triple {P} c {er : Q} with nonempty Q does not imply that an error is reachable from P: {True} x := 2; assume (x = 4); error() {er : x = 4} is valid — vacuously, because the program has no erroneous runs — and no error is reachable. (b) Compositionally (O'Hearn's mkeven example): an over-approximate normal-exit summary {P} c1 {ok : Q} followed by a valid incorrectness error triple [Q] c2 [er : R] with nonempty R does not imply that c1; c2 has a reachable error from P: {True} x := 2 {ok : x = 2 ∨ x = 4} and [x = 2 ∨ x = 4] assume (x = 4); error() [er : x = 4] are valid, yet x := 2; assume (x = 4); error() never errs.
10. **il-proof-rules-sound** (theorem, T0, shallow): Every triple derivable with the incorrectness-logic rules — empty post, consequence (IL direction), disjunction, sequencing (short-circuit and normal), iterate zero, iterate non-zero, backwards variant (one premise per natural number n), choice, error, assume and assignment — is a valid under-approximate triple. In particular the backwards-variant rule is sound: if [p n] c [ok : p (n+1)] is valid for every n, then [p 0] c⋆ [ok : ∃ n, p n] is valid.
11. **il-conjunction-rule-unsound** (impossibility, T0, definitional): The conjunction rule — from [P1] c [e : Q1] and [P2] c [e : Q2] infer [P1 ∧ P2] c [e : Q1 ∧ Q2] — is unsound for incorrectness triples over Nat: for C = (assume x = 1; x := 88) + (assume x = 2; x := 88) both premises hold with post x = 88 but the conclusion fails. Over an arbitrary state type, the rule holds for all commands and assertions iff the state type has at most one element.
12. **conjunction-and-disjunction-rule-soundness** (theorem, T0, definitional): The disjunction rule (from two triples infer the triple with both pres and both posts disjoined) is sound for Hoare and for incorrectness triples; the conjunction rule is sound for Hoare triples. For incorrectness triples, at a fixed command c and exit kind e, the conjunction rule holds for all assertions P1, P2, Q1, Q2 iff the e-relation of c is backward-unique (each final state has at most one initial state).
13. **il-proof-rules-complete** (theorem, T0, shallow): Every valid incorrectness triple [P] c [e : Q] is derivable with the incorrectness-logic rules (with semantic assertions and semantic entailment as the consequence oracle), because [P] c [e : post c e P] is always derivable.
14. **abs-post-sound-iff-extensive** (characterization, T0, shallow): For every map ρ on assertions, the compositional analysis absPost ρ is a sound over-approximate analysis (every computed post is a Hoare post) iff ρ is extensive (X ⊆ ρ X for all X). absPost ρ applies ρ to the exact post at atomic commands; at c1; c2 it runs c2's analysis on c1's normal-exit result (exit ok, no extra ρ) or applies ρ to the disjunction of c1's error post and c2's error post from c1's normal-exit result (exit er); at c1 + c2 it applies ρ to the disjunction of the branch results; at c⋆ it uses the set Inv, the intersection of all assertions X with P ⊆ X and absPost ρ c ok X ⊆ X, returning ρ Inv (exit ok) and ρ (absPost ρ c er Inv) (exit er).
15. **sound-overapproximate-alarm-not-a-true-positive** (impossibility, T0, shallow): A sound over-approximate analysis that never alarms on a program without error() can still raise an alarm without a reachable error: the interval-hull analysis absPost hull is sound, silent on every error-free program, and alarms on (x := 0 + x := 2); assume (x = 1); error() from True, which has no reachable error.
16. **sound-analyses-license-alarms-or-silence** (theorem, T0, definitional): An alarm (nonempty computed error post) of a sound under-approximate analysis is a true positive relative to the analysed pre, and the silence (empty computed error post) of a sound over-approximate analysis is safety from the analysed pre.
17. **sound-underapproximate-silence-not-safety** (impossibility, T0, shallow): A sound under-approximate analysis that is exact on every loop-free program can still be silent on an unsafe program: unrolling every loop at most k times is a sound under-approximate analysis for every k and is exact on loop-free programs (for every k: `unrollAnalysis_exactOnLoopFree`, ToyIL/Analyses.lean:589), and with k = 2 it is silent on (x := x+1)⋆; assume (x = 3); error() from x = 0, which errs.
18. **manifest-error-preserved-under-state-frame-extension** (theorem, T1, shallow): If [P] c [er : Q] is a manifest error — a valid incorrectness error triple such that from every initial state some run of c errs in a Q state — then running c on the first component of a product state with an untouched frame component gives a manifest error [P × True] c↑ [er : Q × True]; when the frame type has an element, the converse also holds.
19. **manifest-reach-iff-error-in-every-reaching-context** (characterization, T0, shallow): If running K[c] from s can arrive at the hole in state u and c can err from u into Q, then K[c] can err from s into Q. Hence c can err into Q from every state iff, for every one-hole context K and all s, u such that K[c] reaches the hole from s in state u, K[c] can err into Q from s; and if K reaches its hole from every state, K[c] can again err into Q from every state.

**Non-claims come first under Boundaries.** Read them before relying on any result: they rule out
the most tempting over-readings, for example that an incorrectness alarm means the error is
triggered in a real deployment (it may be latent), that bounded exploration can never establish
safety (a larger bound or a loop-free program changes that), or that anything here is a statement
about a production analyzer or verifier (every theorem is about the toy semantics; the bridge to
real tools is a separately labeled, derived claim).
Model–system relation: none proved (the soundness results relate the package's own proof rules and
analyses to its own toy semantics). These are statements about the toy model; they neither establish
nor refute the corresponding claims about real bug finders and verifiers (tools based on incorrectness
logic or incorrectness separation logic, bounded model checkers, symbolic executors, Hoare-logic
verifiers, abstract interpreters).

This package belongs to a library of formalized results whose documentation rule is that no
result may be read more broadly than its statement deserves. Here that rule is also the subject
matter. A valid incorrectness triple, like each theorem in this package, licenses exactly its
stated conclusion. Reading one empty error post as safety, an over-approximate alarm as a bug, or
a latent error as a manifest one is the program-logic counterpart of reading a formal result more
broadly than its hypotheses allow. Each negative result is therefore paired with the nearby
positive statement it must not be confused with (positive controls under Findings; attractive
stronger readings under Boundaries).

## Applicability

### Model fidelity

**This is a toy model.** The definitions are meant to capture the semantic core shared by tools
that report bugs (under-approximate reasoning: incorrectness logic and incorrectness separation
logic, bounded model checking, symbolic execution with under-approximate summaries) and tools
that prove their absence (over-approximate reasoning: Hoare logic, sound abstract
interpretation). They do not mirror the definitions of any production tool. Known gaps:

- **Language.** `assign f` is a deterministic state update standing in for an assignment
  `x := e`; `assume b` blocks when `b` is false; `error` stops with exit `er` and leaves the
  state unchanged; sequencing, binary nondeterministic choice, and Kleene star. There are no
  `while` loops as primitives, no procedures, calls, or parameters, no local variables, no heap,
  allocation, or separation-logic resources, and no error handlers: an error short-circuits the
  rest of the program. There is a single error kind.
- **Semantics.** Big-step relational semantics with exit kinds, as in O'Hearn 2020, Fig. 4.
  Divergence has no outcome, so all triples are partial-correctness statements. Errors are
  may-errors: "c errs from s" means that *some* run of `c` from `s` errs.
- **Assertions.** Assertions are semantic predicates `σ → Prop`. Entailments are supplied as
  proofs, so entailment is an oracle. Nothing is said about assertion languages, decidability, or
  entailment checkers.
- **Analyses.** An analysis is an arbitrary function `Cmd σ → Exit → Assn σ → Assn σ`. Soundness
  (`SoundOver`, `SoundUnder`) is a global property over all pres, commands, and exits, and an
  alarm is a nonempty computed error post. Real analyzers compute over finite abstract domains
  with widening, build procedure summaries, and report alarms with traces; none of this is
  modeled. The interval-hull and bounded-unrolling analyses are concrete witnesses, not models of
  particular tools.
- **State types.** Negative results are stated over the state type `Nat`, and each needs a
  minimum number of states. Over the empty state type the refuted implications of cards 8, 9
  (both parts), 15, and 17 hold vacuously (`refuted_implications_hold_on_empty_state_space`), so
  these five need at least one state. The IL conjunction rule refuted on card 11 holds over every
  state type with at most one element, for example `Unit`
  (`il_conjunction_rule_sound_iff_subsingleton`, `il_conjunction_rule_sound_on_unit`), so that
  result needs at least two states.
- **Manifest errors** follow Le et al. 2022, Definition 3.2, with `q ∗ true` read as `q` (there
  is no heap). Frame extension is product-state extension `σ × τ` with an untouched second
  component, not separating conjunction. Contexts are syntactic one-hole contexts of this
  language, not calling contexts of procedures.

### How the subjects relate

The Lean 4 toolchain release listed in `REPORT.json` is the checker for every theorem. The listed
papers are prior art. Results tagged T0 restate a known result over this toy semantics. The single
T1 result (manifest-error preservation under frame extension) makes precise, for disjoint product
states, a property that Le et al. build into their separation-logic definition. No paper's formal
system is mirrored exactly; where the toy differs from a cited statement, the card says so.

### Toolchain and dependencies

Lean `leanprover/lean4:v4.34.1`, core Lean and `Std` only: no Mathlib and no Lake dependencies
(`lean/lakefile.toml` declares one `lean_lib`, `ToyIL`). Modules: `ToyIL.Basic` (language,
semantics, the two triples, and their proved positive and negative examples), `ToyIL.Consequence`
(consequence rules, exact-post duality, agreement and denial, singleton refutation),
`ToyIL.Licensing` (what error triples license), `ToyIL.Rules` (the incorrectness proof system,
soundness, relative completeness, conjunction and disjunction), `ToyIL.Analyses` (abstract
analyses, alarms, silence), and `ToyIL.Manifest` (manifest errors, frames, contexts).

## Findings

Every result below is a kernel-checked theorem about the toy semantics. Lean names are in
namespace `Toy.IL`. For each result the card gives: kind, tier, and depth; the plain claim; the
Lean statement quoted from the source; the statement with key definitions unfolded; the
hypothesis ledger (every `tight` entry names a theorem stating that all other hypotheses hold
and the conclusion fails); a non-vacuity witness (a theorem stating that all hypotheses hold for
a concrete instance); for impossibility results, positive controls; prior art; and the design
question. All 19 cards inform one design question: which conclusions may a tool draw from an
over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which
inference rules may it use for each? Cards whose design question begins "Reference point" are
definitional baselines for the other cards.

### Core definitions

The definitions that the statements depend on, quoted from the sources (doc comments omitted;
`variable {σ : Type}` is in scope):

```lean
-- ToyIL/Basic.lean
inductive Exit where
  | ok
  | er
  deriving DecidableEq, Repr

inductive Cmd (σ : Type) where
  | assign (f : σ → σ)
  | assume (b : σ → Bool)
  | error
  | seq (c₁ c₂ : Cmd σ)
  | choice (c₁ c₂ : Cmd σ)
  | star (c : Cmd σ)

def Cmd.skip : Cmd σ := .assume (fun _ => true)

inductive Exec : Cmd σ → σ → Exit → σ → Prop where
  | assign {f : σ → σ} {s : σ} : Exec (.assign f) s .ok (f s)
  | assume {b : σ → Bool} {s : σ} : b s = true → Exec (.assume b) s .ok s
  | error {s : σ} : Exec .error s .er s
  | seqOk {c₁ c₂ : Cmd σ} {s m t : σ} {e : Exit} :
      Exec c₁ s .ok m → Exec c₂ m e t → Exec (.seq c₁ c₂) s e t
  | seqEr {c₁ c₂ : Cmd σ} {s t : σ} : Exec c₁ s .er t → Exec (.seq c₁ c₂) s .er t
  | choiceL {c₁ c₂ : Cmd σ} {s t : σ} {e : Exit} : Exec c₁ s e t → Exec (.choice c₁ c₂) s e t
  | choiceR {c₁ c₂ : Cmd σ} {s t : σ} {e : Exit} : Exec c₂ s e t → Exec (.choice c₁ c₂) s e t
  | starNil {c : Cmd σ} {s : σ} : Exec (.star c) s .ok s
  | starOk {c : Cmd σ} {s m t : σ} {e : Exit} :
      Exec c s .ok m → Exec (.star c) m e t → Exec (.star c) s e t
  | starEr {c : Cmd σ} {s t : σ} : Exec c s .er t → Exec (.star c) s .er t

abbrev Assn (σ : Type) := σ → Prop

def Entails (P Q : Assn σ) : Prop := ∀ s, P s → Q s

def post (c : Cmd σ) (e : Exit) (P : Assn σ) : Assn σ := fun t => ∃ s, P s ∧ Exec c s e t

def Hoare (P : Assn σ) (c : Cmd σ) (e : Exit) (Q : Assn σ) : Prop := Entails (post c e P) Q

def IL (P : Assn σ) (c : Cmd σ) (e : Exit) (Q : Assn σ) : Prop := Entails Q (post c e P)

def ErrReachable (P : Assn σ) (c : Cmd σ) : Prop := ∃ s t, P s ∧ Exec c s .er t

def Safe (P : Assn σ) (c : Cmd σ) : Prop := ∀ s t, P s → ¬ Exec c s .er t
```

```lean
-- ToyIL/Analyses.lean
abbrev Analysis (σ : Type) := Cmd σ → Exit → Assn σ → Assn σ

def SoundOver (A : Analysis σ) : Prop := ∀ P c e, Hoare P c e (A c e P)

def SoundUnder (U : Analysis σ) : Prop := ∀ P c e, IL P c e (U c e P)

def Alarm (A : Analysis σ) (P : Assn σ) (c : Cmd σ) : Prop := ∃ t, A c .er P t

def Cmd.errorFree : Cmd σ → Bool
  | .assign _ => true
  | .assume _ => true
  | .error => false
  | .seq c₁ c₂ => c₁.errorFree && c₂.errorFree
  | .choice c₁ c₂ => c₁.errorFree && c₂.errorFree
  | .star c => c.errorFree

def SilentOnErrorFree (A : Analysis σ) : Prop :=
  ∀ P c, Cmd.errorFree c = true → ¬ Alarm A P c

def Cmd.loopFree : Cmd σ → Bool
  | .assign _ => true
  | .assume _ => true
  | .error => true
  | .seq c₁ c₂ => c₁.loopFree && c₂.loopFree
  | .choice c₁ c₂ => c₁.loopFree && c₂.loopFree
  | .star _ => false

def ExactOnLoopFree (U : Analysis σ) : Prop :=
  ∀ P c e t, Cmd.loopFree c = true → (U c e P t ↔ post c e P t)
```

```lean
-- ToyIL/Manifest.lean
def ManifestReach (c : Cmd σ) (Q : Assn σ) : Prop := ∀ s, ∃ t, Q t ∧ Exec c s .er t

def ManifestError (P : Assn σ) (c : Cmd σ) (Q : Assn σ) : Prop :=
  IL P c .er Q ∧ ManifestReach c Q
```

Other definitions, summarized (each is quoted in full in the source file named):

- **Proof system** `ILDeriv : Assn σ → Cmd σ → Exit → Assn σ → Prop` (`ToyIL/Rules.lean`;
  O'Hearn 2020, Fig. 2, with semantic assertions): `empty` `[P] c [e : False]`; `conseq`
  (`P ⊆ P'`, `[P] c [e : Q]`, `Q' ⊆ Q` ⊢ `[P'] c [e : Q']`); `disj`; `seqShort`; `seqNormal`;
  `iterZero` `[P] c⋆ [ok : P]` (derivable from the others, `iterZero_derivable`); `iterNonzero`
  (`[P] c⋆;c [e : Q]` ⊢ `[P] c⋆ [e : Q]`); `backwardsVariant` (`∀ n, [p n] c [ok : p (n+1)]` ⊢
  `[p 0] c⋆ [ok : ∃ n, p n]`); `choiceL`/`choiceR`; `errorEr` `[P] error [er : P]`; `assumeOk`
  `[P] assume b [ok : P ∧ b]`; `assign` `[P] assign f [ok : ∃ s, P s ∧ t = f s]`. The
  `[ok : false]`/`[er : false]` halves of O'Hearn's axioms are instances of `empty`.
- **Analyses** (`ToyIL/Analyses.lean`): `exactAnalysis c e P := post c e P`;
  `topAnalysis := True` and `botAnalysis := False` (the trivial analyses).
  `Extensive ρ := ∀ X, Entails X (ρ X)`. `absPost ρ` applies `ρ ∘ post` at atomic commands; at
  `seq` with exit `ok` it is `absPost c₂ ok (absPost c₁ ok P)`; at `seq` with exit `er` it is
  `ρ (absPost c₁ er P ∨ absPost c₂ er (absPost c₁ ok P))`; at `choice` it is
  `ρ (absPost c₁ e P ∨ absPost c₂ e P)`; at `star` with exit `ok` it is `ρ Inv` with
  `Inv t := ∀ X, P ⊆ X → absPost c ok X ⊆ X → X t`; at `star` with exit `er` it is
  `ρ (absPost c er Inv)`. `hull X n := ∃ a b, X a ∧ X b ∧ a ≤ n ∧ n ≤ b` (interval hull on
  `Nat`) and `hullAnalysis := absPost hull`. The counterexample map
  `nonMonoRho : Assn Nat → Assn Nat` is `nonMonoRho X := if X = {0} then True else X`, where `{0}`
  is the assertion `fun n => n = 0` and the test `X = {0}` is decided classically; it is extensive
  but not monotone (`nonMonoRho_extensive`, `nonMonoRho_not_monotone`). `Cmd.upTo 0 c := skip`,
  `Cmd.upTo (n+1) c := skip + (c ; upTo n c)`; `Cmd.unroll k` replaces every `c⋆` by
  `upTo k (c.unroll k)`; `unrollAnalysis k c e P := post (c.unroll k) e P`.
- **Frames and contexts** (`ToyIL/Manifest.lean`): `Cmd.liftFst : Cmd σ → Cmd (σ × τ)` runs `c`
  on the first component (`exec_liftFst_iff : Exec c.liftFst (s, r) e (t, r') ↔ Exec c s e t ∧ r' = r`).
  One-hole contexts `Ctx` (`hole`, `seqL K c₂`, `seqR c₁ K`, `choiceL K c₂`, `choiceR c₁ K`,
  `star K`) with `Ctx.fill`. `Reaches c K s u` says that running `K[c]` from `s` can arrive at
  the hole in state `u` (inductive; the loop case runs earlier iterations of the filled body; its
  constructors are unfolded on card 19).
- **Concrete programs** (state `Nat`, writing `x` for the state): `mkevenProg := x := 2;
  assume (x = 4); error()` (`= mkevenBody; mkevenCheck`); `conjCounterProg := (assume (x = 1);
  x := 88) + (assume (x = 2); x := 88)`; `falseAlarmProg := (x := 0 + x := 2); assume (x = 1);
  error()`; `countProg := (x := x+1)⋆; assume (x = 3); error()`.

Each core definition has proved positive and negative examples (definition adequacy):
`exec_pos_seq_error`, `exec_pos_star_three`, `exec_neg_error_ok`, `exec_neg_assume_false`,
`exec_neg_seq_error_state`, `exec_neg_star_assign_er`, `entails_pos`/`entails_neg`,
`post_pos`/`post_neg`, `hoare_pos`, `hoare_pos_error_ok`, `hoare_neg`, `il_pos`,
`il_pos_drop_branch`, `il_neg`, `errReachable_pos`/`errReachable_neg`,
`safe_pos`/`safe_neg` (`ToyIL/Basic.lean`); `soundOver_exactAnalysis`, `soundOver_topAnalysis`,
`not_soundOver_botAnalysis`, `soundUnder_exactAnalysis`, `soundUnder_botAnalysis`,
`not_soundUnder_topAnalysis`, `alarm_pos`/`alarm_neg`, `hull_pos`/`hull_neg`, `hull_extensive`,
`nonMonoRho_extensive`, `nonMonoRho_not_monotone`, `silentOnErrorFree_hullAnalysis`,
`silentOnErrorFree_exactAnalysis`, `not_silentOnErrorFree_topAnalysis`,
`unrollAnalysis_exactOnLoopFree`, `not_exactOnLoopFree_botAnalysis` (`ToyIL/Analyses.lean`);
`manifestError_pos`, `latent_error_not_manifest`, `manifestReach_not_manifestError`,
`manifestError_pre_need_not_be_true`, `reaches_pos`/`reaches_neg` (`ToyIL/Manifest.lean`);
`ilDeriv_count_up`, `ilDeriv_count_up_error` (`ToyIL/Rules.lean`). The conditions
`SilentOnErrorFree` and `ExactOnLoopFree` are non-degeneracy conditions that exclude the trivial
analyses `topAnalysis` and `botAnalysis`; they are not precision guarantees.

### 1. hoare-consequence-strengthen-pre-weaken-post

- **Kind / tier / depth:** theorem / T0 / definitional.
- **Tier justification.** Hoare's rule of consequence (Hoare 1969) restated over this toy semantics; the ⇑⇓ symmetry with the IL rule is O'Hearn 2020 Fig. 1.
- **Plain claim.** For every command c and exit kind e: if {P} c {e : Q} is a valid Hoare triple, P' ⊆ P and Q ⊆ Q', then {P'} c {e : Q'} is valid (strengthen the pre, weaken the post).

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Consequence.lean:19-21
-- ToyIL/Consequence.lean
theorem hoare_consequence_strengthen_pre_weaken_post {P P' Q Q' : Assn σ} {c : Cmd σ}
    {e : Exit} (hpre : Entails P' P) (h : Hoare P c e Q) (hpost : Entails Q Q') :
    Hoare P' c e Q'
```

With the key definitions unfolded:

```lean
(∀ s, P' s → P s) → (∀ t, (∃ s, P s ∧ Exec c s e t) → Q t) → (∀ t, Q t → Q' t) → ∀ t, (∃ s, P' s ∧ Exec c s e t) → Q' t
```

Hypothesis ledger:

- `hpre : Entails P' P`: the new pre must be stronger; the IL direction P ⊆ P' is unsound for Hoare triples. Tightness: tight: counterexample `Toy.IL.hoare_consequence_pre_tight`.
- `h : Hoare P c e Q`: the triple being adapted. Tightness: tight: counterexample `Toy.IL.hoare_consequence_triple_tight`.
- `hpost : Entails Q Q'`: the new post must be weaker; the IL direction Q' ⊆ Q is unsound for Hoare triples. Tightness: tight: counterexample `Toy.IL.hoare_consequence_post_tight`.

- **Non-vacuity witness.** {x = 0} ⊊ {x ≤ 1}, {x ≤ 1} x := x+1 {ok : x ≤ 2}, {x ≤ 2} ⊊ {x ≤ 3} (both inclusions strict); conclusion {x = 0} x := x+1 {ok : x ≤ 3}. (`Toy.IL.nonvacuity_hoare_consequence`)
- **Prior art.**
  - C. A. R. Hoare, "An axiomatic basis for computer programming", Communications of the ACM 12(10), pp. 576-580, October 1969, doi:10.1145/363235.363259. Introduces Hoare triples and the rules of consequence, composition and iteration.
  - P. W. O'Hearn, "Incorrectness logic", Proceedings of the ACM on Programming Languages 4(POPL), Article 10, January 2020, doi:10.1145/3371078. Definition 1 defines the under-approximate triple [p]r[q] as post(r)p ⊇ q and the Hoare triple {p}r{q} as post(r)p ⊆ q; Lemma 3 (Characterization): [p]r[q] iff every state of q is reachable from some state of p; Fig. 1 states the ∧∨ and ⇑⇓ symmetries and the Principles of Agreement and Denial; Fig. 2 gives the generic rules (Empty under-approximates, Consequence, Disjunction, Unit, Sequencing short-circuit/normal, Iterate zero, Iterate non-zero, Backwards Variant, Choice, Error, Assume); Fig. 4 the relational semantics; Theorem 5 soundness; Theorem 6 completeness for finitely-supported predicates.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `hoare_consequence_strengthen_pre_weaken_post` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — A verifier that has proved `{P} c {e : Q}` may report the triple with a stronger pre or a weaker post. Reasoning: the proof uses only that a Hoare triple is the inclusion `post c e P ⊆ Q` and that entailment is inclusion of predicates. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 2. il-consequence-weaken-pre-strengthen-post

- **Kind / tier / depth:** theorem / T0 / definitional.
- **Tier justification.** The IL rule of consequence of O'Hearn 2020 (Fig. 2; ⇑⇓ symmetry of Fig. 1) and rule Con of de Vries and Koutavas 2011, restated semantically.
- **Plain claim.** For every command c and exit kind e: if [P] c [e : Q] is a valid incorrectness triple, P ⊆ P' and Q' ⊆ Q, then [P'] c [e : Q'] is valid (weaken the pre, strengthen the post — the reverse of Hoare consequence).

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Consequence.lean:27-29
-- ToyIL/Consequence.lean
theorem il_consequence_weaken_pre_strengthen_post {P P' Q Q' : Assn σ} {c : Cmd σ}
    {e : Exit} (hpre : Entails P P') (h : IL P c e Q) (hpost : Entails Q' Q) :
    IL P' c e Q'
```

With the key definitions unfolded:

```lean
(∀ s, P s → P' s) → (∀ t, Q t → ∃ s, P s ∧ Exec c s e t) → (∀ t, Q' t → Q t) → ∀ t, Q' t → ∃ s, P' s ∧ Exec c s e t
```

Hypothesis ledger:

- `hpre : Entails P P'`: the new pre must be weaker; strengthening the pre (Hoare direction) can remove the only states that reach the post. Tightness: tight: counterexample `Toy.IL.il_consequence_pre_tight`.
- `h : IL P c e Q`: the triple being adapted. Tightness: tight: counterexample `Toy.IL.il_consequence_triple_tight`.
- `hpost : Entails Q' Q`: the new post must be stronger; weakening the post (Hoare direction) can add unreachable states. Tightness: tight: counterexample `Toy.IL.il_consequence_post_tight`.

- **Non-vacuity witness.** {x ≤ 1} ⊊ {x ≤ 2}, [x ≤ 1] x := x+1 [ok : x = 1 ∨ x = 2], {x = 1} ⊊ {x = 1 ∨ x = 2} (both inclusions strict); conclusion [x ≤ 2] x := x+1 [ok : x = 1]. (`Toy.IL.nonvacuity_il_consequence`)
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", Proceedings of the ACM on Programming Languages 4(POPL), Article 10, January 2020, doi:10.1145/3371078. Definition 1 defines the under-approximate triple [p]r[q] as post(r)p ⊇ q and the Hoare triple {p}r{q} as post(r)p ⊆ q; Lemma 3 (Characterization): [p]r[q] iff every state of q is reachable from some state of p; Fig. 1 states the ∧∨ and ⇑⇓ symmetries and the Principles of Agreement and Denial; Fig. 2 gives the generic rules (Empty under-approximates, Consequence, Disjunction, Unit, Sequencing short-circuit/normal, Iterate zero, Iterate non-zero, Backwards Variant, Choice, Error, Assume); Fig. 4 the relational semantics; Theorem 5 soundness; Theorem 6 completeness for finitely-supported predicates.
  - E. de Vries and V. Koutavas, "Reverse Hoare logic", Software Engineering and Formal Methods (SEFM 2011), LNCS 7041, pp. 155-171, Springer, 2011, doi:10.1007/978-3-642-24690-6_12. Definition 1 (reverse Hoare validity): every final state satisfying Q is reachable from some initial state satisfying P. Fig. 2: rule Con (consequence with the implications reversed), rule While with a fresh natural-number index (a backwards-variant-style rule), the infinitary rule Split, and rule Frame for unmodified variables. Theorem 1 (soundness), Theorem 2 (relative completeness, via a weakest-postcondition calculus). The language has no error exit.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `il_consequence_weaken_pre_strengthen_post` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — A bug finder holding a valid under-approximate triple may shrink its post (report fewer error states) or enlarge its pre; enlarging the pre, for instance to `True`, can hide which inputs trigger the error (see the card's non-claims). Reasoning: the proof uses only that an incorrectness triple is the inclusion `Q ⊆ post c e P`. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 3. exact-post-duality-and-or-symmetry

- **Kind / tier / depth:** characterization / T0 / definitional.
- **Tier justification.** Immediate from O'Hearn 2020 Definition 1; the ∧∨ symmetry is stated in his Fig. 1.
- **Plain claim.** For a fixed pre P, command c and exit kind e: an assertion Q is both a Hoare post and an incorrectness post iff Q equals post c e P pointwise; two incorrectness posts both hold iff their disjunction is an incorrectness post, [P]c[e:Q1] ∧ [P]c[e:Q2] ↔ [P]c[e:Q1 ∨ Q2]; two Hoare posts both hold iff their conjunction is a Hoare post, {P}c{e:Q1} ∧ {P}c{e:Q2} ↔ {P}c{e:Q1 ∧ Q2}.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Consequence.lean:151-152
-- ToyIL/Consequence.lean
theorem hoare_and_il_iff_eq_post {P Q : Assn σ} {c : Cmd σ} {e : Exit} :
    Hoare P c e Q ∧ IL P c e Q ↔ ∀ t, Q t ↔ post c e P t
-- lean/ToyIL/Consequence.lean:167-168
-- ToyIL/Consequence.lean
theorem il_or_post_iff {P Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit} :
    IL P c e Q₁ ∧ IL P c e Q₂ ↔ IL P c e (fun t => Q₁ t ∨ Q₂ t)
-- lean/ToyIL/Consequence.lean:177-178
-- ToyIL/Consequence.lean
theorem hoare_and_post_iff {P Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit} :
    Hoare P c e Q₁ ∧ Hoare P c e Q₂ ↔ Hoare P c e (fun t => Q₁ t ∧ Q₂ t)
```

With the key definitions unfolded (prose):

```text
hoare_and_il_iff_eq_post: ((∀ t, (∃ s, P s ∧ Exec c s e t) → Q t) ∧ (∀ t, Q t → ∃ s, P s ∧ Exec c s e t)) ↔ ∀ t, Q t ↔ ∃ s, P s ∧ Exec c s e t
il_or_post_iff: ((∀ t, Q₁ t → ∃ s, P s ∧ Exec c s e t) ∧ (∀ t, Q₂ t → ∃ s, P s ∧ Exec c s e t)) ↔ ∀ t, Q₁ t ∨ Q₂ t → ∃ s, P s ∧ Exec c s e t
hoare_and_post_iff: ((∀ t, (∃ s, P s ∧ Exec c s e t) → Q₁ t) ∧ (∀ t, (∃ s, P s ∧ Exec c s e t) → Q₂ t)) ↔ ∀ t, (∃ s, P s ∧ Exec c s e t) → Q₁ t ∧ Q₂ t
```

Hypothesis ledger: no hypotheses beyond the universally quantified objects.

- **Non-vacuity witness.** For x := 0 + x := 2 from True: x = 0 ∨ x = 2 is exact; x = 2 is an IL post but not a Hoare post; x ≤ 5 is a Hoare post but not an IL post. (`Toy.IL.nonvacuity_duality`)
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", Proceedings of the ACM on Programming Languages 4(POPL), Article 10, January 2020, doi:10.1145/3371078. Definition 1 defines the under-approximate triple [p]r[q] as post(r)p ⊇ q and the Hoare triple {p}r{q} as post(r)p ⊆ q; Lemma 3 (Characterization): [p]r[q] iff every state of q is reachable from some state of p; Fig. 1 states the ∧∨ and ⇑⇓ symmetries and the Principles of Agreement and Denial; Fig. 2 gives the generic rules (Empty under-approximates, Consequence, Disjunction, Unit, Sequencing short-circuit/normal, Iterate zero, Iterate non-zero, Backwards Variant, Choice, Error, Assume); Fig. 4 the relational semantics; Theorem 5 soundness; Theorem 6 completeness for finitely-supported predicates.
  - B. Möller, P. W. O'Hearn and T. Hoare, "On algebra of program correctness and incorrectness", Relational and Algebraic Methods in Computer Science (RAMiCS 2021), LNCS 13027, pp. 325-343, Springer, 2021, doi:10.1007/978-3-030-88701-8_20. Modal Kleene algebra with countable joins of tests embedding both incorrectness logic and Hoare logic.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `hoare_and_il_iff_eq_post`, `il_or_post_iff`, `hoare_and_post_iff` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — A tool that holds both an over-approximate and an under-approximate result with the same pre, command, exit and post has computed the exact post-image. Reasoning: the two triple meanings are opposite inclusions with the same post-image, which is all the proof uses. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 4. il-hoare-agreement-and-denial

- **Kind / tier / depth:** theorem / T0 / definitional.
- **Tier justification.** O'Hearn 2020 Fig. 1, Principles of Agreement and Denial, restated semantically.
- **Plain claim.** Agreement: if [U] c [e : U'] is a valid incorrectness triple, U ⊆ O, and {O} c {e : O'} is a valid Hoare triple, then U' ⊆ O'. Denial (contrapositive): if [U] c [e : U'] is a valid incorrectness triple, U ⊆ O, and U' ⊄ O', then {O} c {e : O'} is not valid.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Consequence.lean:236-237
-- ToyIL/Consequence.lean
theorem il_hoare_agreement {U U' O O' : Assn σ} {c : Cmd σ} {e : Exit}
    (hil : IL U c e U') (hsub : Entails U O) (hh : Hoare O c e O') : Entails U' O'
-- lean/ToyIL/Consequence.lean:244-246
-- ToyIL/Consequence.lean
theorem il_denies_hoare {U U' O O' : Assn σ} {c : Cmd σ} {e : Exit}
    (hil : IL U c e U') (hsub : Entails U O) (hout : ¬ Entails U' O') :
    ¬ Hoare O c e O'
```

With the key definitions unfolded (prose):

```text
il_hoare_agreement: (∀ t, U' t → ∃ s, U s ∧ Exec c s e t) → (∀ s, U s → O s) → (∀ t, (∃ s, O s ∧ Exec c s e t) → O' t) → ∀ t, U' t → O' t
il_denies_hoare: (∀ t, U' t → ∃ s, U s ∧ Exec c s e t) → (∀ s, U s → O s) → ¬ (∀ t, U' t → O' t) → ¬ (∀ t, (∃ s, O s ∧ Exec c s e t) → O' t)
```

Hypothesis ledger:

- `hil : IL U c e U' (agreement and denial)`: the under-approximate witness; without it U' may contain unreachable states. The counterexample serves both theorems: hsub holds, U' ⊄ O' (so denial's hout holds), the Hoare triple holds, and both conclusions fail. Tightness: tight: counterexample `Toy.IL.il_hoare_agreement_il_tight`.
- `hsub : Entails U O (agreement and denial)`: the witness must start inside the Hoare pre. The counterexample serves both theorems in the same way. Tightness: tight: counterexample `Toy.IL.il_hoare_agreement_sub_tight`.
- `hh : Hoare O c e O' (agreement only)`: agreement's conclusion needs the Hoare triple. Tightness: tight: counterexample `Toy.IL.il_hoare_agreement_hoare_tight`.
- `hout : ¬ Entails U' O' (denial only)`: denial needs the post of the IL triple to escape O'; with U' ⊆ O' the Hoare triple can be valid. Tightness: tight: counterexample `Toy.IL.il_denies_hoare_hout_tight`.

- **Non-vacuity witness.** c = x := 0 + x := 2. Agreement: [x = 5] c [ok : x = 2], {x = 5} ⊆ True, {True} c {ok : x even}, and {x = 2} ⊆ {x even}. Denial: [x = 5] c [ok : x = 2], {x = 5} ⊆ True, {x = 2} ⊄ {x = 0}, hence {True} c {ok : x = 0} is invalid. (`Toy.IL.nonvacuity_agreement`, `Toy.IL.nonvacuity_denial`)
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", Proceedings of the ACM on Programming Languages 4(POPL), Article 10, January 2020, doi:10.1145/3371078. Definition 1 defines the under-approximate triple [p]r[q] as post(r)p ⊇ q and the Hoare triple {p}r{q} as post(r)p ⊆ q; Lemma 3 (Characterization): [p]r[q] iff every state of q is reachable from some state of p; Fig. 1 states the ∧∨ and ⇑⇓ symmetries and the Principles of Agreement and Denial; Fig. 2 gives the generic rules (Empty under-approximates, Consequence, Disjunction, Unit, Sequencing short-circuit/normal, Iterate zero, Iterate non-zero, Backwards Variant, Choice, Error, Assume); Fig. 4 the relational semantics; Theorem 5 soundness; Theorem 6 completeness for finitely-supported predicates.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `il_hoare_agreement`, `il_denies_hoare` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — A tool can move facts between an under-approximate and an over-approximate result about the same command and exit: an incorrectness post lies inside every Hoare post whose pre covers the incorrectness pre (agreement), and a found incorrectness post escaping a Hoare post refutes that Hoare triple (denial). Reasoning: both triples are inclusions involving the same post-image. This requires both results to be about the same semantics; this transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 5. hoare-invalid-iff-il-singleton-outside-post

- **Kind / tier / depth:** characterization / T0 / definitional.
- **Tier justification.** Möller, O'Hearn and Hoare 2021, Theorem 4.1 (an invalid Hoare triple is refuted by a valid IL triple with a pre below p and a post not below q; its proof uses p0 = p), specialised to the relation model with a singleton post; related falsification results in outcome logic (Zilberstein et al. 2023, Corollary 5.7) and Hyper Hoare Logic (Dardinier and Müller 2024, Theorem 5).
- **Plain claim.** A Hoare triple {P} c {e : Q} is invalid iff there is a single state t with t ∉ Q such that the incorrectness triple [P] c [e : {t}] is valid.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Consequence.lean:325-326
-- ToyIL/Consequence.lean
theorem not_hoare_iff_exists_il_singleton_outside {P Q : Assn σ} {c : Cmd σ} {e : Exit} :
    ¬ Hoare P c e Q ↔ ∃ t, ¬ Q t ∧ IL P c e (fun x => x = t)
```

With the key definitions unfolded:

```lean
¬ (∀ t, (∃ s, P s ∧ Exec c s e t) → Q t) ↔ ∃ t, ¬ Q t ∧ ∀ x, x = t → ∃ s, P s ∧ Exec c s e x
```

Hypothesis ledger: no hypotheses beyond the universally quantified objects.

- **Non-vacuity witness.** {x = 0} x := x+1 {ok : x = 0} is invalid, refuted by [x = 0] x := x+1 [ok : x = 1] with 1 ∉ {x = 0}. (`Toy.IL.nonvacuity_not_hoare_singleton`)
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", Proceedings of the ACM on Programming Languages 4(POPL), Article 10, January 2020, doi:10.1145/3371078. Definition 1 defines the under-approximate triple [p]r[q] as post(r)p ⊇ q and the Hoare triple {p}r{q} as post(r)p ⊆ q; Lemma 3 (Characterization): [p]r[q] iff every state of q is reachable from some state of p; Fig. 1 states the ∧∨ and ⇑⇓ symmetries and the Principles of Agreement and Denial; Fig. 2 gives the generic rules (Empty under-approximates, Consequence, Disjunction, Unit, Sequencing short-circuit/normal, Iterate zero, Iterate non-zero, Backwards Variant, Choice, Error, Assume); Fig. 4 the relational semantics; Theorem 5 soundness; Theorem 6 completeness for finitely-supported predicates.
  - B. Möller, P. W. O'Hearn and T. Hoare, "On algebra of program correctness and incorrectness", Relational and Algebraic Methods in Computer Science (RAMiCS 2021), LNCS 13027, pp. 325-343, Springer, 2021, doi:10.1007/978-3-030-88701-8_20. Modal Kleene algebra with countable joins of tests embedding both incorrectness logic and Hoare logic. Theorem 4.1: {p} a {q} is invalid iff there are p0 ≤ p and q0 ≰ q with [p0] a [q0] valid (the proof takes p0 = p and q0 the strongest post); the text notes that in concrete testing in the relation model p0 and q0 denote singleton sets.
  - N. Zilberstein, D. Dreyer and A. Silva, "Outcome logic: a unifying foundation for correctness and incorrectness reasoning", Proceedings of the ACM on Programming Languages 7(OOPSLA1), Article 93, April 2023, doi:10.1145/3586045 (full version arXiv:2303.03111). Corollary 5.7 (Hoare Logic Falsification): a Hoare triple {P} C {Q} is invalid iff some satisfiable assertion stronger than P has a valid outcome-logic triple witnessing an outcome outside Q. Outcome logic is a different formalism; it is not formalized here.
  - T. Dardinier and P. Müller, "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties", Proceedings of the ACM on Programming Languages 8(PLDI), Article 207, June 2024, doi:10.1145/3656437 (arXiv:2301.10037); Isabelle/HOL formalization: T. Dardinier, "Formalization of Hyper Hoare Logic: A Logic to (Dis-)Prove Program Hyperproperties", Archive of Formal Proofs, April 2023, https://isa-afp.org/entries/HyperHoareLogic.html. Theorem 5 (disproving hyper-triples): a hyper-triple is invalid iff some satisfiable hyper-assertion entailing the pre yields a valid triple with the negated post; Proposition 6 expresses IL triples as hyper-triples.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `not_hoare_iff_exists_il_singleton_outside` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — Every refutation of a Hoare specification can be given as an incorrectness triple with the same pre and a single-state post outside the Hoare post, which is the semantic core of a counterexample report. Reasoning: the theorem constructs a singleton post assertion; it keeps the whole pre, so it does not isolate one initial test state, and a tool's assertion language must be able to express the singleton for the witness to be reportable (see the card's non-claims). This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 6. il-error-triple-nonempty-post-true-positive

- **Kind / tier / depth:** theorem / T0 / definitional.
- **Tier justification.** The true-positive reading of IL error triples (O'Hearn 2020 Lemma 3); the two characterizations are Möller, O'Hearn and Hoare 2021 Theorem 4.5 restated in this toy semantics.
- **Plain claim.** If [P] c [er : Q] is a valid incorrectness triple and Q is nonempty, then some run of c from a state in P terminates with an error in a state in Q (a true positive relative to P). Consequently an error is reachable from P iff some valid incorrectness error triple [P] c [er : Q] has nonempty Q, and c is safe from P iff every valid incorrectness error triple from P has an empty post.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Licensing.lean:22-23
-- ToyIL/Licensing.lean
theorem il_er_nonempty_post_true_positive {P Q : Assn σ} {c : Cmd σ}
    (hil : IL P c .er Q) (hne : ∃ t, Q t) : ∃ s t, P s ∧ Q t ∧ Exec c s .er t
-- lean/ToyIL/Licensing.lean:69-70
-- ToyIL/Licensing.lean
theorem errReachable_iff_exists_il_er_nonempty {P : Assn σ} {c : Cmd σ} :
    ErrReachable P c ↔ ∃ Q, IL P c .er Q ∧ ∃ t, Q t
-- lean/ToyIL/Licensing.lean:80-81
-- ToyIL/Licensing.lean
theorem safe_iff_all_il_er_posts_empty {P : Assn σ} {c : Cmd σ} :
    Safe P c ↔ ∀ Q, IL P c .er Q → ∀ t, ¬ Q t
```

With the key definitions unfolded (prose):

```text
il_er_nonempty_post_true_positive: (∀ t, Q t → ∃ s, P s ∧ Exec c s .er t) → (∃ t, Q t) → ∃ s t, P s ∧ Q t ∧ Exec c s .er t
errReachable_iff_exists_il_er_nonempty: (∃ s t, P s ∧ Exec c s .er t) ↔ ∃ Q, (∀ t, Q t → ∃ s, P s ∧ Exec c s .er t) ∧ ∃ t, Q t
safe_iff_all_il_er_posts_empty: (∀ s t, P s → ¬ Exec c s .er t) ↔ ∀ Q, (∀ t, Q t → ∃ s, P s ∧ Exec c s .er t) → ∀ t, ¬ Q t
```

Hypothesis ledger:

- `hil : IL P c er Q (il_er_nonempty_post_true_positive)`: under-approximation is what makes post states reachable. Tightness: tight: counterexample `Toy.IL.il_er_nonempty_post_true_positive_il_tight`.
- `hne : ∃ t, Q t (il_er_nonempty_post_true_positive)`: an empty post makes every incorrectness triple vacuously valid. Tightness: tight: counterexample `Toy.IL.il_er_nonempty_post_true_positive_nonempty_tight`.

- **Non-vacuity witness.** [x = 7] assume (x = 7); error() [er : x = 7], with post state 7; for the characterizations, assume (x = 7); error() errs from x = 7 and assume false; error() is safe from True. (`Toy.IL.nonvacuity_il_true_positive`, `Toy.IL.nonvacuity_il_characterization`)
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", Proceedings of the ACM on Programming Languages 4(POPL), Article 10, January 2020, doi:10.1145/3371078. Definition 1 defines the under-approximate triple [p]r[q] as post(r)p ⊇ q and the Hoare triple {p}r{q} as post(r)p ⊆ q; Lemma 3 (Characterization): [p]r[q] iff every state of q is reachable from some state of p; Fig. 1 states the ∧∨ and ⇑⇓ symmetries and the Principles of Agreement and Denial; Fig. 2 gives the generic rules (Empty under-approximates, Consequence, Disjunction, Unit, Sequencing short-circuit/normal, Iterate zero, Iterate non-zero, Backwards Variant, Choice, Error, Assume); Fig. 4 the relational semantics; Theorem 5 soundness; Theorem 6 completeness for finitely-supported predicates. Section 4: the existence of a consistent error assertion does not indicate a definite bug; for f(x) = {assert(x!=0);...} the error spec [x==0]f(x)[er:x==0] is valid, but no bug occurs unless a caller supplies x == 0.
  - B. Möller, P. W. O'Hearn and T. Hoare, "On algebra of program correctness and incorrectness", Relational and Algebraic Methods in Computer Science (RAMiCS 2021), LNCS 13027, pp. 325-343, Springer, 2021, doi:10.1007/978-3-030-88701-8_20. Modal Kleene algebra with countable joins of tests embedding both incorrectness logic and Hoare logic. Theorem 4.5: (1) {p} c {er : 0} is valid iff every valid [p] c [er : q] has q = 0; (2) some valid [p] c [er : q] has q ≠ 0 iff {p} c {er : 0} is invalid. Section 4.4 also gives over-approximate error rules whose sequencing rule uses a normal-exit summary {p} c1 {ok : q} and whose iteration rule uses a loop invariant {p} c {ok : p}.
  - Q. L. Le, A. Raad, J. Villard, J. Berdine, D. Dreyer and P. W. O'Hearn, "Finding real bugs in big programs with incorrectness logic", Proceedings of the ACM on Programming Languages 6(OOPSLA1), Article 81, April 2022, doi:10.1145/3527325. Distinguishes latent from manifest errors. Definition 3.2: a valid error triple |= [p] C [er : q] denotes a manifest error iff ∀s. ∃s'. (s,s') ∈ ⟦C⟧er ∧ s' ∈ ⟦q ∗ true⟧. Theorem 3.3 gives a sufficient logical condition; Theorem 3.4 (True Positives Property): if a procedure in a complete program has a manifest error then it is dead code or ⟦main⟧er ≠ ∅.
  - A. Raad, J. Berdine, H.-H. Dang, D. Dreyer, P. W. O'Hearn and J. Villard, "Local reasoning about the presence of bugs: Incorrectness Separation Logic", Computer Aided Verification (CAV 2020), LNCS 12225, pp. 225-252, Springer, 2020, doi:10.1007/978-3-030-53291-8_14. Combines incorrectness logic with separation logic and states that when ISL identifies a bug there is indeed a bug (no false positives), given the assumptions of the underlying model. Heaps, separating conjunction and the frame rule are not modelled in this package.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `il_er_nonempty_post_true_positive`, `errReachable_iff_exists_il_er_nonempty`, `safe_iff_all_il_er_posts_empty` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — An under-approximate tool that reports a valid error triple with a satisfiable post has found an error reachable from some state of its pre; whether any real caller supplies such a state (manifest versus latent errors) is not implied. Reasoning: validity says every post state is an error outcome from a pre state, and a nonempty post supplies one. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 7. safety-iff-hoare-error-triple-false

- **Kind / tier / depth:** characterization / T0 / definitional.
- **Tier justification.** Definitional for partial-correctness triples with an error exit; the error-exit form is Möller, O'Hearn and Hoare 2021 Section 4.4 (Theorem 4.5 relates it to IL error triples).
- **Plain claim.** c is safe from P (no run from P terminates with an error) iff the Hoare error triple {P} c {er : False} is valid. Stating safety of c needs only this error-exit triple, and no normal-exit triple about c can replace it: {True} error() {ok : False} is valid although error() is unsafe.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Licensing.lean:97-98
-- ToyIL/Licensing.lean
theorem safe_iff_hoare_er_false {P : Assn σ} {c : Cmd σ} :
    Safe P c ↔ Hoare P c .er (fun _ => False)
-- lean/ToyIL/Licensing.lean:105-106
-- ToyIL/Licensing.lean
theorem safe_of_hoare_er_false {P : Assn σ} {c : Cmd σ}
    (h : Hoare P c .er (fun _ => False)) : Safe P c
```

With the key definitions unfolded (prose):

```text
safe_iff_hoare_er_false: (∀ s t, P s → ¬ Exec c s .er t) ↔ ∀ t, (∃ s, P s ∧ Exec c s .er t) → False
safe_of_hoare_er_false: (∀ t, (∃ s, P s ∧ Exec c s .er t) → False) → ∀ s t, P s → ¬ Exec c s .er t
```

Hypothesis ledger:

- `h : Hoare P c er False (safe_of_hoare_er_false)`: the error-exit triple; a normal-exit triple cannot replace it, even with the strongest post False. Tightness: tight: counterexample `Toy.IL.safe_of_hoare_er_false_tight`.

- **Non-vacuity witness.** {True} assume false; error() {er : False}. (`Toy.IL.nonvacuity_hoare_safe`)
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", Proceedings of the ACM on Programming Languages 4(POPL), Article 10, January 2020, doi:10.1145/3371078. Definition 1 defines the under-approximate triple [p]r[q] as post(r)p ⊇ q and the Hoare triple {p}r{q} as post(r)p ⊆ q; Lemma 3 (Characterization): [p]r[q] iff every state of q is reachable from some state of p; Fig. 1 states the ∧∨ and ⇑⇓ symmetries and the Principles of Agreement and Denial; Fig. 2 gives the generic rules (Empty under-approximates, Consequence, Disjunction, Unit, Sequencing short-circuit/normal, Iterate zero, Iterate non-zero, Backwards Variant, Choice, Error, Assume); Fig. 4 the relational semantics; Theorem 5 soundness; Theorem 6 completeness for finitely-supported predicates.
  - B. Möller, P. W. O'Hearn and T. Hoare, "On algebra of program correctness and incorrectness", Relational and Algebraic Methods in Computer Science (RAMiCS 2021), LNCS 13027, pp. 325-343, Springer, 2021, doi:10.1007/978-3-030-88701-8_20. Modal Kleene algebra with countable joins of tests embedding both incorrectness logic and Hoare logic. Theorem 4.5: (1) {p} c {er : 0} is valid iff every valid [p] c [er : q] has q = 0; (2) some valid [p] c [er : q] has q ≠ 0 iff {p} c {er : 0} is invalid. Section 4.4 also gives over-approximate error rules whose sequencing rule uses a normal-exit summary {p} c1 {ok : q} and whose iteration rule uses a loop invariant {p} c {ok : p}.
  - C. A. R. Hoare, "An axiomatic basis for computer programming", Communications of the ACM 12(10), pp. 576-580, October 1969, doi:10.1145/363235.363259. Introduces Hoare triples and the rules of consequence, composition and iteration.
- **Design question.** Reference point (definitional baseline for other cards). Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `safe_iff_hoare_er_false`, `safe_of_hoare_er_false` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — Reference point: a verifier establishes that no error is reachable from `P` exactly by proving `{P} c {er : False}`. Reasoning: the Hoare error triple with post `False` unfolds to the definition of `Safe`. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 8. il-error-triple-empty-post-does-not-imply-safety

- **Kind / tier / depth:** impossibility / T0 / definitional.
- **Tier justification.** O'Hearn 2020's 'Empty under-approximates' axiom makes every empty-post triple valid; the consequence for safety is immediate and is the contrapositive reading of Möller, O'Hearn and Hoare 2021 Theorem 4.5(1).
- **Plain claim.** A valid incorrectness error triple with empty post, [P] c [er : False], does not imply that c is safe from P: such triples are valid for every P and c, including error(), which is unsafe.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Licensing.lean:166-167
-- ToyIL/Licensing.lean
theorem not_il_er_empty_post_implies_safe :
    ¬ ∀ (P : Assn Nat) (c : Cmd Nat), IL P c .er (fun _ => False) → Safe P c
-- lean/ToyIL/Licensing.lean:159-161
-- ToyIL/Licensing.lean
theorem il_er_empty_post_valid_yet_unsafe :
    IL (fun _ : Nat => True) .error .er (fun _ => False) ∧
      ¬ Safe (fun _ : Nat => True) (.error : Cmd Nat)
-- lean/ToyIL/Licensing.lean:154
-- ToyIL/Licensing.lean
theorem il_empty_post (P : Assn σ) (c : Cmd σ) (e : Exit) : IL P c e (fun _ => False)
```

With the key definitions unfolded (prose):

```text
not_il_er_empty_post_implies_safe: ¬ ∀ (P : Nat → Prop) (c : Cmd Nat), (∀ t, False → ∃ s, P s ∧ Exec c s .er t) → ∀ s t, P s → ¬ Exec c s .er t
il_er_empty_post_valid_yet_unsafe: (∀ t : Nat, False → ∃ s, True ∧ Exec .error s .er t) ∧ ¬ ∀ s t : Nat, True → ¬ Exec .error s .er t
il_empty_post: ∀ t, False → ∃ s, P s ∧ Exec c s e t
```

Hypothesis ledger: no hypotheses beyond the universally quantified objects.

- **Non-vacuity witness.** [True] error() [er : False] is valid, and error() errs from every state. (`Toy.IL.il_er_empty_post_valid_yet_unsafe`)
- **Positive control** (nearby settings where the refuted conclusion does hold): `Toy.IL.safe_iff_all_il_er_posts_empty` (safety from P holds iff *every* valid IL error triple [P] c [er : Q] has an empty post Q).
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", Proceedings of the ACM on Programming Languages 4(POPL), Article 10, January 2020, doi:10.1145/3371078. Definition 1 defines the under-approximate triple [p]r[q] as post(r)p ⊇ q and the Hoare triple {p}r{q} as post(r)p ⊆ q; Lemma 3 (Characterization): [p]r[q] iff every state of q is reachable from some state of p; Fig. 1 states the ∧∨ and ⇑⇓ symmetries and the Principles of Agreement and Denial; Fig. 2 gives the generic rules (Empty under-approximates, Consequence, Disjunction, Unit, Sequencing short-circuit/normal, Iterate zero, Iterate non-zero, Backwards Variant, Choice, Error, Assume); Fig. 4 the relational semantics; Theorem 5 soundness; Theorem 6 completeness for finitely-supported predicates.
  - B. Möller, P. W. O'Hearn and T. Hoare, "On algebra of program correctness and incorrectness", Relational and Algebraic Methods in Computer Science (RAMiCS 2021), LNCS 13027, pp. 325-343, Springer, 2021, doi:10.1007/978-3-030-88701-8_20. Modal Kleene algebra with countable joins of tests embedding both incorrectness logic and Hoare logic. Theorem 4.5: (1) {p} c {er : 0} is valid iff every valid [p] c [er : q] has q = 0; (2) some valid [p] c [er : q] has q ≠ 0 iff {p} c {er : 0} is invalid. Section 4.4 also gives over-approximate error rules whose sequencing rule uses a normal-exit summary {p} c1 {ok : q} and whose iteration rule uses a loop invariant {p} c {ok : p}.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `not_il_er_empty_post_implies_safe`, `il_er_empty_post_valid_yet_unsafe`, `il_empty_post` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — A bug finder whose result is an empty error post ("nothing found") has not proved safety; bounded model checkers and under-approximate symbolic executors that return no report are in this position. Reasoning: `[P] c [er : False]` is valid for every `P` and `c`, including programs that err. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 9. hoare-summaries-do-not-imply-reachable-error

- **Kind / tier / depth:** impossibility / T0 / definitional.
- **Tier justification.** O'Hearn 2020 Section 3.3 (mkeven/usemkeven) describes the compositional false positive mechanized in the second pair of statements; the first pair is the whole-program form, which holds vacuously.
- **Plain claim.** Over-approximate (Hoare) summaries do not establish reachable errors. (a) A valid Hoare error triple {P} c {er : Q} with nonempty Q does not imply that an error is reachable from P: {True} x := 2; assume (x = 4); error() {er : x = 4} is valid — vacuously, because the program has no erroneous runs — and no error is reachable. (b) Compositionally (O'Hearn's mkeven example): an over-approximate normal-exit summary {P} c1 {ok : Q} followed by a valid incorrectness error triple [Q] c2 [er : R] with nonempty R does not imply that c1; c2 has a reachable error from P: {True} x := 2 {ok : x = 2 ∨ x = 4} and [x = 2 ∨ x = 4] assume (x = 4); error() [er : x = 4] are valid, yet x := 2; assume (x = 4); error() never errs.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Licensing.lean:198-199
-- ToyIL/Licensing.lean
theorem not_hoare_er_nonempty_post_implies_errReachable :
    ¬ ∀ (P Q : Assn Nat) (c : Cmd Nat), Hoare P c .er Q → (∃ t, Q t) → ErrReachable P c
-- lean/ToyIL/Licensing.lean:190-192
-- ToyIL/Licensing.lean
theorem hoare_er_nonempty_post_without_reachable_error :
    Hoare (fun _ => True) mkevenProg .er (fun n => n = 4) ∧ (∃ t : Nat, t = 4) ∧
      ¬ ErrReachable (fun _ => True) mkevenProg
-- lean/ToyIL/Licensing.lean:228-230
-- ToyIL/Licensing.lean
theorem not_hoare_ok_then_il_er_implies_errReachable :
    ¬ ∀ (P Q R : Assn Nat) (c₁ c₂ : Cmd Nat),
      Hoare P c₁ .ok Q → IL Q c₂ .er R → (∃ t, R t) → ErrReachable P (.seq c₁ c₂)
-- lean/ToyIL/Licensing.lean:216-219
-- ToyIL/Licensing.lean
theorem hoare_ok_summary_then_il_er_without_reachable_error :
    Hoare (fun _ => True) mkevenBody .ok (fun n => n = 2 ∨ n = 4) ∧
      IL (fun n => n = 2 ∨ n = 4) mkevenCheck .er (fun n => n = 4) ∧ (∃ t : Nat, t = 4) ∧
      ¬ ErrReachable (fun _ => True) (.seq mkevenBody mkevenCheck)
```

With the key definitions unfolded (prose):

```text
not_hoare_er_nonempty_post_implies_errReachable: ¬ ∀ (P Q : Nat → Prop) (c : Cmd Nat), (∀ t, (∃ s, P s ∧ Exec c s .er t) → Q t) → (∃ t, Q t) → ∃ s t, P s ∧ Exec c s .er t
not_hoare_ok_then_il_er_implies_errReachable: ¬ ∀ (P Q R : Nat → Prop) (c₁ c₂ : Cmd Nat), (∀ t, (∃ s, P s ∧ Exec c₁ s .ok t) → Q t) → (∀ t, R t → ∃ s, Q s ∧ Exec c₂ s .er t) → (∃ t, R t) → ∃ s t, P s ∧ Exec (.seq c₁ c₂) s .er t
where mkevenProg = mkevenBody; mkevenCheck, mkevenBody = x := 2, mkevenCheck = assume (x = 4); error()
```

Hypothesis ledger: no hypotheses beyond the universally quantified objects.

- **Non-vacuity witness.** mkevenProg = x := 2; assume (x = 4); error() from True, with Hoare error post x = 4; and its split into mkevenBody with summary x = 2 ∨ x = 4 and mkevenCheck with IL error post x = 4. (`Toy.IL.hoare_er_nonempty_post_without_reachable_error`, `Toy.IL.hoare_ok_summary_then_il_er_without_reachable_error`)
- **Positive control** (nearby settings where the refuted conclusion does hold): `Toy.IL.il_er_nonempty_post_true_positive` (a valid IL error triple [P] c [er : Q] with nonempty Q yields a run from a P state that errs in a Q state), `Toy.IL.il_ok_then_il_er_errReachable` (with an under-approximate summary [P] c₁ [ok : Q] in place of the Hoare summary, a valid [Q] c₂ [er : R] with nonempty R makes an error of c₁; c₂ reachable from P).
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", Proceedings of the ACM on Programming Languages 4(POPL), Article 10, January 2020, doi:10.1145/3371078. Definition 1 defines the under-approximate triple [p]r[q] as post(r)p ⊇ q and the Hoare triple {p}r{q} as post(r)p ⊆ q; Lemma 3 (Characterization): [p]r[q] iff every state of q is reachable from some state of p; Fig. 1 states the ∧∨ and ⇑⇓ symmetries and the Principles of Agreement and Denial; Fig. 2 gives the generic rules (Empty under-approximates, Consequence, Disjunction, Unit, Sequencing short-circuit/normal, Iterate zero, Iterate non-zero, Backwards Variant, Choice, Error, Assume); Fig. 4 the relational semantics; Theorem 5 soundness; Theorem 6 completeness for finitely-supported predicates. Section 3.3 (Under-approximate Success): for mkeven() { x=2; } the over-approximate normal-exit summary 'ok: x==2 || x==4', used in usemkeven() { mkeven(); if (x==4) error(); }, would yield a false positive warning; the paper therefore uses under-approximate summaries for both normal and erroneous termination.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `not_hoare_er_nonempty_post_implies_errReachable`, `hoare_er_nonempty_post_without_reachable_error`, `not_hoare_ok_then_il_er_implies_errReachable`, `hoare_ok_summary_then_il_er_without_reachable_error` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — A compositional analyzer that combines an over-approximate summary with a check that would be a true positive under an exact summary can report a false positive (O'Hearn's `mkeven` example); a tool that wants reports without false positives must use under-approximate summaries for both exits. Reasoning: the over-approximate summary admits states the callee never produces, and the positive control shows that an under-approximate prefix summary restores the conclusion. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 10. il-proof-rules-sound

- **Kind / tier / depth:** theorem / T0 / shallow.
- **Tier justification.** O'Hearn 2020 Theorem 5 (soundness) for the generic rules of Fig. 2, specialised to this language; cf. de Vries and Koutavas 2011 Theorem 1.
- **Plain claim.** Every triple derivable with the incorrectness-logic rules — empty post, consequence (IL direction), disjunction, sequencing (short-circuit and normal), iterate zero, iterate non-zero, backwards variant (one premise per natural number n), choice, error, assume and assignment — is a valid under-approximate triple. In particular the backwards-variant rule is sound: if [p n] c [ok : p (n+1)] is valid for every n, then [p 0] c⋆ [ok : ∃ n, p n] is valid.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Rules.lean:76-77
-- ToyIL/Rules.lean
theorem ilDeriv_sound {P Q : Assn σ} {c : Cmd σ} {e : Exit} (h : ILDeriv P c e Q) :
    IL P c e Q
-- lean/ToyIL/Rules.lean:64-65
-- ToyIL/Rules.lean
theorem il_backwardsVariant_sound {c : Cmd σ} (p : Nat → Assn σ)
    (h : ∀ n, IL (p n) c .ok (p (n + 1))) : IL (p 0) (.star c) .ok (fun s => ∃ n, p n s)
```

With the key definitions unfolded (prose):

```text
ilDeriv_sound: ILDeriv P c e Q → ∀ t, Q t → ∃ s, P s ∧ Exec c s e t
il_backwardsVariant_sound: (∀ n t, p (n + 1) t → ∃ s, p n s ∧ Exec c s .ok t) → ∀ t, (∃ n, p n t) → ∃ s, p 0 s ∧ Exec (.star c) s .ok t
ILDeriv constructors: empty [P] c [e : False]; conseq (P ⊆ P', [P] c [e : Q], Q' ⊆ Q ⊢ [P'] c [e : Q']); disj; seqShort ([P] c₁ [er : R] ⊢ [P] c₁;c₂ [er : R]); seqNormal ([P] c₁ [ok : Q], [Q] c₂ [e : R] ⊢ [P] c₁;c₂ [e : R]); iterZero [P] c⋆ [ok : P]; iterNonzero ([P] c⋆;c [e : Q] ⊢ [P] c⋆ [e : Q]); backwardsVariant (∀ n, [p n] c [ok : p (n+1)] ⊢ [p 0] c⋆ [ok : ∃ n, p n]); choiceL/choiceR; errorEr [P] error [er : P]; assumeOk [P] assume b [ok : P ∧ b]; assign [P] assign f [ok : ∃ s, P s ∧ t = f s]
```

Hypothesis ledger:

- `h : ILDeriv P c e Q (ilDeriv_sound)`: the triple must be produced by the rules; an arbitrary triple need not be valid. The counterexample [True] skip [er : True] is neither derivable nor valid. Tightness: tight: counterexample `Toy.IL.ilDeriv_sound_deriv_tight`.
- `h : ∀ n, IL (p n) c ok (p (n + 1)) (il_backwardsVariant_sound)`: every step of the variant must be under-approximate; holding for the first step only is not enough. Tightness: tight: counterexample `Toy.IL.il_backwardsVariant_sound_premise_tight`.

- **Non-vacuity witness.** [x = 0] (x := x+1)⋆ [ok : True] derived via the backwards variant p(n) = (x = n), and [x = 0] (x := x+1)⋆; assume (x = 3); error() [er : x = 3]; for il_backwardsVariant_sound, ∀ n, [x = n] x := x+1 [ok : x = n+1]. (`Toy.IL.ilDeriv_count_up`, `Toy.IL.ilDeriv_count_up_error`, `Toy.IL.nonvacuity_ilDeriv_sound`, `Toy.IL.nonvacuity_backwardsVariant`)
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", Proceedings of the ACM on Programming Languages 4(POPL), Article 10, January 2020, doi:10.1145/3371078. Definition 1 defines the under-approximate triple [p]r[q] as post(r)p ⊇ q and the Hoare triple {p}r{q} as post(r)p ⊆ q; Lemma 3 (Characterization): [p]r[q] iff every state of q is reachable from some state of p; Fig. 1 states the ∧∨ and ⇑⇓ symmetries and the Principles of Agreement and Denial; Fig. 2 gives the generic rules (Empty under-approximates, Consequence, Disjunction, Unit, Sequencing short-circuit/normal, Iterate zero, Iterate non-zero, Backwards Variant, Choice, Error, Assume); Fig. 4 the relational semantics; Theorem 5 soundness; Theorem 6 completeness for finitely-supported predicates.
  - E. de Vries and V. Koutavas, "Reverse Hoare logic", Software Engineering and Formal Methods (SEFM 2011), LNCS 7041, pp. 155-171, Springer, 2011, doi:10.1007/978-3-642-24690-6_12. Definition 1 (reverse Hoare validity): every final state satisfying Q is reachable from some initial state satisfying P. Fig. 2: rule Con (consequence with the implications reversed), rule While with a fresh natural-number index (a backwards-variant-style rule), the infinitary rule Split, and rule Frame for unmodified variables. Theorem 1 (soundness), Theorem 2 (relative completeness, via a weakest-postcondition calculus). The language has no error exit.
  - C. Zhang, A. Azevedo de Amorim and M. Gaboardi, "On incorrectness logic and Kleene algebra with top and tests", Proceedings of the ACM on Programming Languages 6(POPL), Article 29, January 2022, doi:10.1145/3498690. Shows that Kleene algebra with tests cannot express incorrectness triples, while Kleene algebra with top and tests can and validates the rules of O'Hearn's logic equationally.
  - T. Murray, "An Under-Approximate Relational Logic", Archive of Formal Proofs, March 2020, https://isa-afp.org/entries/Relational-Incorrectness-Logic.html. An Isabelle/HOL mechanization of an under-approximate relational logic for IMP, proved sound and complete, with a decomposition into a non-relational under-approximate Hoare logic.
  - F. Verbeek, M. S. Sefat, Z. Fu and B. Ravindran, "On Extending Incorrectness Logic with Backwards Reasoning", Proceedings of the ACM on Programming Languages 9(POPL), Article 14, January 2025, doi:10.1145/3704850. Extends incorrectness logic with underspecification; soundness and completeness for a subset of presumptions are formalized in Isabelle/HOL.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `ilDeriv_sound`, `il_backwardsVariant_sound` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — A bug finder whose derivations are instances of these rules (with sound entailment and exact posts for atomic commands) produces valid under-approximate triples. Reasoning: each rule preserves validity over the relational semantics. A tool whose rules are not instances of these, or whose semantics differs, needs its own soundness argument. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 11. il-conjunction-rule-unsound

- **Kind / tier / depth:** impossibility / T0 / definitional.
- **Tier justification.** O'Hearn 2020's own counterexample, mechanized; the dependence on the state type is an elementary consequence of the backward-uniqueness characterization (conjunction-and-disjunction-rule-soundness).
- **Plain claim.** The conjunction rule — from [P1] c [e : Q1] and [P2] c [e : Q2] infer [P1 ∧ P2] c [e : Q1 ∧ Q2] — is unsound for incorrectness triples over Nat: for C = (assume x = 1; x := 88) + (assume x = 2; x := 88) both premises hold with post x = 88 but the conclusion fails. Over an arbitrary state type, the rule holds for all commands and assertions iff the state type has at most one element.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Rules.lean:304-306
-- ToyIL/Rules.lean
theorem il_conjunction_rule_unsound :
    ¬ ∀ (P₁ P₂ Q₁ Q₂ : Assn Nat) (c : Cmd Nat) (e : Exit),
      IL P₁ c e Q₁ → IL P₂ c e Q₂ → IL (fun s => P₁ s ∧ P₂ s) c e (fun s => Q₁ s ∧ Q₂ s)
-- lean/ToyIL/Rules.lean:292-295
-- ToyIL/Rules.lean
theorem il_conjunction_counterexample :
    IL (fun n => n = 1) conjCounterProg .ok (fun n => n = 88) ∧
    IL (fun n => n = 2) conjCounterProg .ok (fun n => n = 88) ∧
    ¬ IL (fun n => n = 1 ∧ n = 2) conjCounterProg .ok (fun n => n = 88 ∧ n = 88)
-- lean/ToyIL/Rules.lean:441-444
-- ToyIL/Rules.lean
theorem il_conjunction_rule_sound_iff_subsingleton (τ : Type) :
    (∀ (P₁ P₂ Q₁ Q₂ : Assn τ) (c : Cmd τ) (e : Exit),
        IL P₁ c e Q₁ → IL P₂ c e Q₂ → IL (fun s => P₁ s ∧ P₂ s) c e (fun t => Q₁ t ∧ Q₂ t)) ↔
      (∀ s₁ s₂ : τ, s₁ = s₂)
```

With the key definitions unfolded (prose):

```text
il_conjunction_rule_unsound: ¬ ∀ P₁ P₂ Q₁ Q₂ c e, IL P₁ c e Q₁ → IL P₂ c e Q₂ → IL (P₁ ∧ P₂) c e (Q₁ ∧ Q₂)   (over Nat)
il_conjunction_rule_sound_iff_subsingleton τ: (∀ P₁ P₂ Q₁ Q₂ c e, IL P₁ c e Q₁ → IL P₂ c e Q₂ → IL (P₁ ∧ P₂) c e (Q₁ ∧ Q₂)) ↔ ∀ s₁ s₂ : τ, s₁ = s₂
```

Hypothesis ledger: no hypotheses beyond the universally quantified objects.

- **Non-vacuity witness.** conjCounterProg with P1 = (x = 1), P2 = (x = 2), Q1 = Q2 = (x = 88); for the characterization, both sides hold over Unit. (`Toy.IL.il_conjunction_counterexample`, `Toy.IL.il_conjunction_rule_sound_on_unit`)
- **Positive control** (nearby settings where the refuted conclusion does hold): `Toy.IL.il_conjunction_sound_of_backward_unique` (the IL conjunction rule holds for a command whose e-runs are backward-unique: each final state has at most one initial state), `Toy.IL.hoare_conjunction_sound` (the conjunction rule holds for Hoare triples), `Toy.IL.il_conjunction_rule_sound_on_unit` (over the one-element state type Unit the IL conjunction rule holds for all commands and assertions), `Toy.IL.il_conjunction_same_pre_sound` (from [P] c [e : Q₁] and [P] c [e : Q₂] with the same pre P, [P ∧ P] c [e : Q₁ ∧ Q₂] holds), `Toy.IL.il_conjunction_backward_preserved_sound` (conjoining to both pre and post an assertion F that c preserves backwards at exit e, meaning every e-run ending in F started in F, keeps an IL triple valid).
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", PACMPL 4(POPL), Article 10, 2020, doi:10.1145/3371078, Section 4: the dual of the disjunction rule (with ∧) is omitted because it is unsound for under-approximation, with the counterexample C = (assume x==1; x=88) + (assume x==2; x=88): [x==1]C[ok:x==88] and [x==2]C[ok:x==88] hold but [false]C[ok:x==88] does not. Fig. 3 includes a Constancy rule for unmodified variables.
  - A. Raad, J. Berdine, H.-H. Dang, D. Dreyer, P. W. O'Hearn and J. Villard, "Local reasoning about the presence of bugs: Incorrectness Separation Logic", Computer Aided Verification (CAV 2020), LNCS 12225, pp. 225-252, Springer, 2020, doi:10.1007/978-3-030-53291-8_14. Combines incorrectness logic with separation logic and states that when ISL identifies a bug there is indeed a bug (no false positives), given the assumptions of the underlying model. Heaps, separating conjunction and the frame rule are not modelled in this package.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `il_conjunction_rule_unsound`, `il_conjunction_counterexample`, `il_conjunction_rule_sound_iff_subsingleton` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — An under-approximate analysis must not conjoin two separately derived results with different pres: doing so can claim error states that no single pre state produces. Reasoning: a command that maps two distinct states to one (state merging) makes each conjunct valid while the conjunction is not; the hazard therefore applies to any tool whose commands can merge states. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 12. conjunction-and-disjunction-rule-soundness

- **Kind / tier / depth:** theorem / T0 / definitional.
- **Tier justification.** Standard for Hoare triples; IL disjunction is O'Hearn 2020 Fig. 2; the backward-unique characterization of IL conjunction is an elementary observation (singleton pres and posts).
- **Plain claim.** The disjunction rule (from two triples infer the triple with both pres and both posts disjoined) is sound for Hoare and for incorrectness triples; the conjunction rule is sound for Hoare triples. For incorrectness triples, at a fixed command c and exit kind e, the conjunction rule holds for all assertions P1, P2, Q1, Q2 iff the e-relation of c is backward-unique (each final state has at most one initial state).

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Rules.lean:239-241
-- ToyIL/Rules.lean
theorem hoare_conjunction_sound {P₁ P₂ Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit}
    (h₁ : Hoare P₁ c e Q₁) (h₂ : Hoare P₂ c e Q₂) :
    Hoare (fun s => P₁ s ∧ P₂ s) c e (fun s => Q₁ s ∧ Q₂ s)
-- lean/ToyIL/Rules.lean:231-233
-- ToyIL/Rules.lean
theorem hoare_disjunction_sound {P₁ P₂ Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit}
    (h₁ : Hoare P₁ c e Q₁) (h₂ : Hoare P₂ c e Q₂) :
    Hoare (fun s => P₁ s ∨ P₂ s) c e (fun s => Q₁ s ∨ Q₂ s)
-- lean/ToyIL/Rules.lean:223-225
-- ToyIL/Rules.lean
theorem il_disjunction_sound {P₁ P₂ Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit}
    (h₁ : IL P₁ c e Q₁) (h₂ : IL P₂ c e Q₂) :
    IL (fun s => P₁ s ∨ P₂ s) c e (fun s => Q₁ s ∨ Q₂ s)
-- lean/ToyIL/Rules.lean:313-316
-- ToyIL/Rules.lean
theorem il_conjunction_sound_of_backward_unique {P₁ P₂ Q₁ Q₂ : Assn σ} {c : Cmd σ} {e : Exit}
    (huniq : ∀ s₁ s₂ t, Exec c s₁ e t → Exec c s₂ e t → s₁ = s₂)
    (h₁ : IL P₁ c e Q₁) (h₂ : IL P₂ c e Q₂) :
    IL (fun s => P₁ s ∧ P₂ s) c e (fun s => Q₁ s ∧ Q₂ s)
-- lean/ToyIL/Rules.lean:407-410
-- ToyIL/Rules.lean
theorem il_conjunction_rule_iff_backward_unique (c : Cmd σ) (e : Exit) :
    (∀ P₁ P₂ Q₁ Q₂ : Assn σ, IL P₁ c e Q₁ → IL P₂ c e Q₂ →
        IL (fun s => P₁ s ∧ P₂ s) c e (fun t => Q₁ t ∧ Q₂ t)) ↔
      (∀ s₁ s₂ t, Exec c s₁ e t → Exec c s₂ e t → s₁ = s₂)
```

With the key definitions unfolded (prose):

```text
hoare_conjunction_sound / hoare_disjunction_sound: Hoare P₁ c e Q₁ → Hoare P₂ c e Q₂ → Hoare (P₁ ∧ P₂) c e (Q₁ ∧ Q₂), and the same with ∨
il_disjunction_sound: IL P₁ c e Q₁ → IL P₂ c e Q₂ → IL (P₁ ∨ P₂) c e (Q₁ ∨ Q₂)
il_conjunction_sound_of_backward_unique: (∀ s₁ s₂ t, Exec c s₁ e t → Exec c s₂ e t → s₁ = s₂) → IL P₁ c e Q₁ → IL P₂ c e Q₂ → IL (P₁ ∧ P₂) c e (Q₁ ∧ Q₂)
il_conjunction_rule_iff_backward_unique c e: (∀ P₁ P₂ Q₁ Q₂, IL P₁ c e Q₁ → IL P₂ c e Q₂ → IL (P₁ ∧ P₂) c e (Q₁ ∧ Q₂)) ↔ ∀ s₁ s₂ t, Exec c s₁ e t → Exec c s₂ e t → s₁ = s₂
```

Hypothesis ledger:

- `h₁ : first premise triple (Hoare for the Hoare rules, IL for the IL rules)`: each conclusion needs the first premise; one canonical counterexample per rule (the other hypotheses hold, h₁ fails, the conclusion fails). Tightness: tight: counterexample `Toy.IL.conj_disj_rules_h1_tight`.
- `h₂ : second premise triple`: each conclusion needs the second premise; one canonical counterexample per rule. Tightness: tight: counterexample `Toy.IL.conj_disj_rules_h2_tight`.
- `huniq : ∀ s₁ s₂ t, Exec c s₁ e t → Exec c s₂ e t → s₁ = s₂ (il_conjunction_sound_of_backward_unique)`: makes the two witnesses for a post state coincide. Tightness: tight: counterexample `Toy.IL.il_conjunction_sound_of_backward_unique_tight`.

- **Non-vacuity witness.** x := x+1 with {x ≤ 1}/{1 ≤ x} for Hoare, [x = 0]/[x = 4] for IL disjunction, and [x ≤ 3]/[1 ≤ x] with post x = 2 for backward-unique IL conjunction; for the characterization, both sides hold for x := x+1 and both fail for conjCounterProg. (`Toy.IL.nonvacuity_conj_disj`, `Toy.IL.nonvacuity_il_conjunction_backward_unique`, `Toy.IL.nonvacuity_il_conjunction_rule_iff`)
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", Proceedings of the ACM on Programming Languages 4(POPL), Article 10, January 2020, doi:10.1145/3371078. Definition 1 defines the under-approximate triple [p]r[q] as post(r)p ⊇ q and the Hoare triple {p}r{q} as post(r)p ⊆ q; Lemma 3 (Characterization): [p]r[q] iff every state of q is reachable from some state of p; Fig. 1 states the ∧∨ and ⇑⇓ symmetries and the Principles of Agreement and Denial; Fig. 2 gives the generic rules (Empty under-approximates, Consequence, Disjunction, Unit, Sequencing short-circuit/normal, Iterate zero, Iterate non-zero, Backwards Variant, Choice, Error, Assume); Fig. 4 the relational semantics; Theorem 5 soundness; Theorem 6 completeness for finitely-supported predicates.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `hoare_conjunction_sound`, `hoare_disjunction_sound`, `il_disjunction_sound`, `il_conjunction_sound_of_backward_unique`, `il_conjunction_rule_iff_backward_unique` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — Over-approximate tools may conjoin and disjoin results; under-approximate tools may disjoin results and may conjoin them only for backward-unique commands (each final state has at most one predecessor) or under the escape hatches listed under Boundaries. Reasoning: the characterization at fixed `(c, e)` is exact. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 13. il-proof-rules-complete

- **Kind / tier / depth:** theorem / T0 / shallow.
- **Tier justification.** O'Hearn 2020 Theorem 6 (completeness) for this language without variables, so no finite-support side condition is needed; cf. de Vries and Koutavas 2011 Theorem 2 and Möller, O'Hearn and Hoare 2021 Theorems 3.2 and 4.4.
- **Plain claim.** Every valid incorrectness triple [P] c [e : Q] is derivable with the incorrectness-logic rules (with semantic assertions and semantic entailment as the consequence oracle), because [P] c [e : post c e P] is always derivable.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Rules.lean:581-582
-- ToyIL/Rules.lean
theorem ilDeriv_relatively_complete {P Q : Assn σ} {c : Cmd σ} {e : Exit} (h : IL P c e Q) :
    ILDeriv P c e Q
-- lean/ToyIL/Rules.lean:507
-- ToyIL/Rules.lean
theorem ilDeriv_post (c : Cmd σ) : ∀ (P : Assn σ) (e : Exit), ILDeriv P c e (post c e P)
```

With the key definitions unfolded (prose):

```text
ilDeriv_relatively_complete: (∀ t, Q t → ∃ s, P s ∧ Exec c s e t) → ILDeriv P c e Q
ilDeriv_post: ∀ P e, ILDeriv P c e (fun t => ∃ s, P s ∧ Exec c s e t)
```

Hypothesis ledger:

- `h : IL P c e Q`: only valid triples are derivable (soundness). Tightness: tight: counterexample `Toy.IL.ilDeriv_complete_valid_tight`.

- **Non-vacuity witness.** [x = 0] (x := x+1)⋆; assume (x = 3); error() [er : x = 3] is valid, hence derivable. (`Toy.IL.nonvacuity_ilDeriv_complete`)
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", Proceedings of the ACM on Programming Languages 4(POPL), Article 10, January 2020, doi:10.1145/3371078. Definition 1 defines the under-approximate triple [p]r[q] as post(r)p ⊇ q and the Hoare triple {p}r{q} as post(r)p ⊆ q; Lemma 3 (Characterization): [p]r[q] iff every state of q is reachable from some state of p; Fig. 1 states the ∧∨ and ⇑⇓ symmetries and the Principles of Agreement and Denial; Fig. 2 gives the generic rules (Empty under-approximates, Consequence, Disjunction, Unit, Sequencing short-circuit/normal, Iterate zero, Iterate non-zero, Backwards Variant, Choice, Error, Assume); Fig. 4 the relational semantics; Theorem 5 soundness; Theorem 6 completeness for finitely-supported predicates.
  - E. de Vries and V. Koutavas, "Reverse Hoare logic", Software Engineering and Formal Methods (SEFM 2011), LNCS 7041, pp. 155-171, Springer, 2011, doi:10.1007/978-3-642-24690-6_12. Definition 1 (reverse Hoare validity): every final state satisfying Q is reachable from some initial state satisfying P. Fig. 2: rule Con (consequence with the implications reversed), rule While with a fresh natural-number index (a backwards-variant-style rule), the infinitary rule Split, and rule Frame for unmodified variables. Theorem 1 (soundness), Theorem 2 (relative completeness, via a weakest-postcondition calculus). The language has no error exit.
  - B. Möller, P. W. O'Hearn and T. Hoare, "On algebra of program correctness and incorrectness", Relational and Algebraic Methods in Computer Science (RAMiCS 2021), LNCS 13027, pp. 325-343, Springer, 2021, doi:10.1007/978-3-030-88701-8_20. Modal Kleene algebra with countable joins of tests embedding both incorrectness logic and Hoare logic. Lemma 3.4: [p] a [⟨a|p] (strongest post) is provable; Theorem 3.2: soundness and relative completeness of the variable-free IL rules; Theorem 4.4: soundness and completeness of the rules with an error exit.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `ilDeriv_relatively_complete`, `ilDeriv_post` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — Relative completeness: with an entailment oracle, every valid under-approximate triple is derivable, so a rule-based bug finder loses nothing in principle by restricting itself to these rules. Reasoning: the proof derives the exact post-image and weakens by consequence. Real tools with decidable assertion fragments and finite representations get no such guarantee from this result. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 14. abs-post-sound-iff-extensive

- **Kind / tier / depth:** characterization / T0 / shallow.
- **Tier justification.** Soundness of compositional abstract interpretation is standard (Cousot and Cousot 1977, 1979), and the authors' summary of the 1979 paper states that isotony is not required for approximate predicate transformers to be correct; a mechanized abstract interpreter exists in Isabelle/HOL (Nipkow 2012). Restated here for this toy analysis, with the converse.
- **Plain claim.** For every map ρ on assertions, the compositional analysis absPost ρ is a sound over-approximate analysis (every computed post is a Hoare post) iff ρ is extensive (X ⊆ ρ X for all X). absPost ρ applies ρ to the exact post at atomic commands; at c1; c2 it runs c2's analysis on c1's normal-exit result (exit ok, no extra ρ) or applies ρ to the disjunction of c1's error post and c2's error post from c1's normal-exit result (exit er); at c1 + c2 it applies ρ to the disjunction of the branch results; at c⋆ it uses the set Inv, the intersection of all assertions X with P ⊆ X and absPost ρ c ok X ⊆ X, returning ρ Inv (exit ok) and ρ (absPost ρ c er Inv) (exit er).

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Analyses.lean:226
-- ToyIL/Analyses.lean
theorem absPost_sound {ρ : Assn σ → Assn σ} (hρ : Extensive ρ) : SoundOver (absPost ρ)
-- lean/ToyIL/Analyses.lean:240-241
-- ToyIL/Analyses.lean
theorem soundOver_absPost_iff_extensive (ρ : Assn σ → Assn σ) :
    SoundOver (absPost ρ) ↔ Extensive ρ
```

With the key definitions unfolded (prose):

```text
absPost_sound: (∀ X s, X s → ρ X s) → ∀ P c e t, (∃ s, P s ∧ Exec c s e t) → absPost ρ c e P t
soundOver_absPost_iff_extensive ρ: (∀ P c e t, (∃ s, P s ∧ Exec c s e t) → absPost ρ c e P t) ↔ ∀ X s, X s → ρ X s
absPost ρ: atomic c ↦ ρ (post c e P); seq ok ↦ absPost c₂ ok (absPost c₁ ok P); seq er ↦ ρ (absPost c₁ er P ∨ absPost c₂ er (absPost c₁ ok P)); choice ↦ ρ (absPost c₁ e P ∨ absPost c₂ e P); star ok ↦ ρ Inv; star er ↦ ρ (absPost c er Inv), Inv t := ∀ X, P ⊆ X → absPost ρ c ok X ⊆ X → X t
```

Hypothesis ledger:

- `hρ : Extensive ρ (absPost_sound)`: each abstraction step must keep every concrete state; the converse direction of the characterization shows it is also necessary for every ρ. Tightness: tight: counterexample `Toy.IL.absPost_sound_extensive_tight`.

- **Non-vacuity witness.** ρ = hull, the interval hull on Nat, is extensive and absPost hull is sound. (`Toy.IL.nonvacuity_absPost_sound`)
- **Prior art.**
  - P. Cousot and R. Cousot, "Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints", POPL 1977, pp. 238-252, doi:10.1145/512950.512973. Sound over-approximation of program semantics by abstract interpretation.
  - P. Cousot and R. Cousot, "Systematic design of program analysis frameworks", Conference Record of the Sixth Annual ACM Symposium on Principles of Programming Languages (POPL 1979), pp. 269-282, doi:10.1145/567752.567778. Per the authors' published summary of the paper, Section 7 gives a local correctness condition for approximate predicate transformers and notes that, since isotony is not required for them to be correct, non-isotone program analysis frameworks are manageable; it also discusses best approximate predicate transformers for upper closure operators.
  - T. Nipkow, "Abstract Interpretation of Annotated Commands", Interactive Theorem Proving (ITP 2012), LNCS 7406, pp. 116-132, Springer, 2012, doi:10.1007/978-3-642-32347-8_9; Isabelle/HOL formalization in the Archive of Formal Proofs entry Abs_Int_ITP2012 (https://isa-afp.org/entries/Abs_Int_ITP2012.html): a mechanized generic abstract interpreter for a while-language, including widening and narrowing.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `absPost_sound`, `soundOver_absPost_iff_extensive` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — An abstract interpreter that applies an operator after each concrete step and treats loops through the intersection of all assertions that contain the pre and are closed under the abstract loop body is sound over-approximate exactly when that operator is extensive. Reasoning: extensiveness is used at every step, and it is necessary already at `skip`. Finite abstract domains, widening and termination of real abstract interpreters are not modeled. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 15. sound-overapproximate-alarm-not-a-true-positive

- **Kind / tier / depth:** impossibility / T0 / shallow.
- **Tier justification.** False positives of sound over-approximate analyses are folklore (discussed in O'Hearn 2020 Section 2 and by Bruni et al. 2021); mechanized here with an interval-hull analysis that is silent on every program without error().
- **Plain claim.** A sound over-approximate analysis that never alarms on a program without error() can still raise an alarm without a reachable error: the interval-hull analysis absPost hull is sound, silent on every error-free program, and alarms on (x := 0 + x := 2); assume (x = 1); error() from True, which has no reachable error.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Analyses.lean:486-488
-- ToyIL/Analyses.lean
theorem soundOver_silentOnErrorFree_alarm_not_imply_errReachable :
    ¬ ∀ (A : Analysis Nat), SoundOver A → SilentOnErrorFree A →
      ∀ P c, Alarm A P c → ErrReachable P c
-- lean/ToyIL/Analyses.lean:461-464
-- ToyIL/Analyses.lean
theorem hullAnalysis_false_alarm :
    SoundOver hullAnalysis ∧ SilentOnErrorFree hullAnalysis ∧
      Alarm hullAnalysis (fun _ => True) falseAlarmProg ∧
      ¬ ErrReachable (fun _ => True) falseAlarmProg
```

With the key definitions unfolded (prose):

```text
soundOver_silentOnErrorFree_alarm_not_imply_errReachable: ¬ ∀ A : Analysis Nat, (∀ P c e t, (∃ s, P s ∧ Exec c s e t) → A c e P t) → (∀ P c, c.errorFree = true → ¬ ∃ t, A c .er P t) → ∀ P c, (∃ t, A c .er P t) → ∃ s t, P s ∧ Exec c s .er t
hullAnalysis_false_alarm: SoundOver hullAnalysis ∧ SilentOnErrorFree hullAnalysis ∧ Alarm hullAnalysis (fun _ => True) falseAlarmProg ∧ ¬ ErrReachable (fun _ => True) falseAlarmProg
```

Hypothesis ledger: no hypotheses beyond the universally quantified objects.

- **Non-vacuity witness.** hullAnalysis on falseAlarmProg from True: the abstract state after the choice is hull {0, 2} ∋ 1. hullAnalysis is also silent on mkevenProg, whose error is unreachable. (`Toy.IL.hullAnalysis_false_alarm`, `Toy.IL.hullAnalysis_silent_on_mkevenProg`)
- **Positive control** (nearby settings where the refuted conclusion does hold): `Toy.IL.soundUnder_alarm_errReachable` (an alarm of a sound under-approximate analysis is a reachable error), `Toy.IL.exactAnalysis_alarm_iff_errReachable` (the exact analysis alarms exactly on reachable errors), `Toy.IL.alarm_errReachable_of_er_post_under` (an alarm at (P, c) is a reachable error whenever the computed error post at (P, c) is contained in the true error post post c er P).
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", PACMPL 4(POPL), Article 10, 2020, doi:10.1145/3371078, Section 2: tools based on over-approximation suffer from false positives, reports of bugs that cannot occur.
  - P. Cousot and R. Cousot, "Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints", POPL 1977, pp. 238-252, doi:10.1145/512950.512973. Sound over-approximation of program semantics by abstract interpretation.
  - R. Bruni, R. Giacobazzi, R. Gori and F. Ranzato, "A Logic for Locally Complete Abstract Interpretations", 36th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2021), pp. 1-13, doi:10.1109/LICS52264.2021.9470608. A provable triple gives an under-approximation Q of the strongest post with the same abstraction; Corollary V.5 (Precision): for specifications expressible in the abstract domain, such a triple decides both correctness and incorrectness, so the abstract interpretation raises no false alert for that input.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `soundOver_silentOnErrorFree_alarm_not_imply_errReachable`, `hullAnalysis_false_alarm` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — A sound over-approximate analyzer, even one that is silent on every program without an `error` command, can raise an alarm on a program from which no error is reachable (interval-hull example); its alarms need confirmation, for instance by an under-approximate check, before they are read as bugs. Reasoning: joining states (as an interval domain does) adds states the program never reaches. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 16. sound-analyses-license-alarms-or-silence

- **Kind / tier / depth:** theorem / T0 / definitional.
- **Tier justification.** Immediate from the definitions; the standard division of labour between bug finders and verifiers.
- **Plain claim.** An alarm (nonempty computed error post) of a sound under-approximate analysis is a true positive relative to the analysed pre, and the silence (empty computed error post) of a sound over-approximate analysis is safety from the analysed pre.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Analyses.lean:76-77
-- ToyIL/Analyses.lean
theorem soundUnder_alarm_errReachable {U : Analysis σ} {P : Assn σ} {c : Cmd σ}
    (hU : SoundUnder U) (ha : Alarm U P c) : ErrReachable P c
-- lean/ToyIL/Analyses.lean:82-83
-- ToyIL/Analyses.lean
theorem soundOver_no_alarm_safe {A : Analysis σ} {P : Assn σ} {c : Cmd σ}
    (hA : SoundOver A) (hna : ¬ Alarm A P c) : Safe P c
```

With the key definitions unfolded (prose):

```text
soundUnder_alarm_errReachable: (∀ P c e t, U c e P t → ∃ s, P s ∧ Exec c s e t) → (∃ t, U c .er P t) → ∃ s t, P s ∧ Exec c s .er t
soundOver_no_alarm_safe: (∀ P c e t, (∃ s, P s ∧ Exec c s e t) → A c e P t) → ¬ (∃ t, A c .er P t) → ∀ s t, P s → ¬ Exec c s .er t
```

Hypothesis ledger:

- `hU : SoundUnder U`: under-approximation makes alarms real; only its instance at (P, c, er) is used (the pointwise form is il_er_nonempty_post_true_positive). Tightness: tight: counterexample `Toy.IL.soundUnder_alarm_errReachable_tight`.
- `ha : Alarm U P c`: without an alarm nothing is reported. Tightness: tight: counterexample `Toy.IL.soundUnder_alarm_errReachable_alarm_tight`.
- `hA : SoundOver A`: over-approximation makes silence meaningful; only its instance at (P, c, er) is used (the pointwise form is safe_of_hoare_er_false). Tightness: tight: counterexample `Toy.IL.soundOver_no_alarm_safe_tight`.
- `hna : ¬ Alarm A P c`: an alarm of an over-approximate analysis proves nothing. Tightness: tight: counterexample `Toy.IL.soundOver_no_alarm_safe_alarm_tight`.

- **Non-vacuity witness.** The exact analysis alarms on error() and is silent on skip. (`Toy.IL.nonvacuity_analysis_licensing`)
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", Proceedings of the ACM on Programming Languages 4(POPL), Article 10, January 2020, doi:10.1145/3371078. Definition 1 defines the under-approximate triple [p]r[q] as post(r)p ⊇ q and the Hoare triple {p}r{q} as post(r)p ⊆ q; Lemma 3 (Characterization): [p]r[q] iff every state of q is reachable from some state of p; Fig. 1 states the ∧∨ and ⇑⇓ symmetries and the Principles of Agreement and Denial; Fig. 2 gives the generic rules (Empty under-approximates, Consequence, Disjunction, Unit, Sequencing short-circuit/normal, Iterate zero, Iterate non-zero, Backwards Variant, Choice, Error, Assume); Fig. 4 the relational semantics; Theorem 5 soundness; Theorem 6 completeness for finitely-supported predicates.
  - A. Raad, J. Berdine, H.-H. Dang, D. Dreyer, P. W. O'Hearn and J. Villard, "Local reasoning about the presence of bugs: Incorrectness Separation Logic", Computer Aided Verification (CAV 2020), LNCS 12225, pp. 225-252, Springer, 2020, doi:10.1007/978-3-030-53291-8_14. Combines incorrectness logic with separation logic and states that when ISL identifies a bug there is indeed a bug (no false positives), given the assumptions of the underlying model. Heaps, separating conjunction and the frame rule are not modelled in this package.
- **Design question.** Reference point (definitional baseline for other cards). Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `soundUnder_alarm_errReachable`, `soundOver_no_alarm_safe` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — Reference point: sound under-approximate alarms are reachable errors and sound over-approximate silence is safety; this is the licensing rule a real tool should follow for each direction. Reasoning: the definitions of `SoundUnder` and `SoundOver` instantiated at the error exit. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 17. sound-underapproximate-silence-not-safety

- **Kind / tier / depth:** impossibility / T0 / shallow.
- **Tier justification.** Folklore (bounded exploration finds bugs but does not prove their absence; O'Hearn 2020 Sections 4 and 5.2 discuss bounded unrolling); mechanized with a bounded-unrolling analysis shown sound under-approximate for every bound and exact on loop-free programs.
- **Plain claim.** A sound under-approximate analysis that is exact on every loop-free program can still be silent on an unsafe program: unrolling every loop at most k times is a sound under-approximate analysis for every k and is exact on loop-free programs (for every k: `unrollAnalysis_exactOnLoopFree`, ToyIL/Analyses.lean:589), and with k = 2 it is silent on (x := x+1)⋆; assume (x = 3); error() from x = 0, which errs.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Analyses.lean:632-634
-- ToyIL/Analyses.lean
theorem soundUnder_exactOnLoopFree_no_alarm_not_imply_safe :
    ¬ ∀ (U : Analysis Nat), SoundUnder U → ExactOnLoopFree U →
      ∀ P c, ¬ Alarm U P c → Safe P c
-- lean/ToyIL/Analyses.lean:607-610
-- ToyIL/Analyses.lean
theorem unrollAnalysis_two_false_negative :
    SoundUnder (unrollAnalysis 2 : Analysis Nat) ∧ ExactOnLoopFree (unrollAnalysis 2 : Analysis Nat) ∧
      ¬ Alarm (unrollAnalysis 2) (fun n => n = 0) countProg ∧
      ¬ Safe (fun n => n = 0) countProg
-- lean/ToyIL/Analyses.lean:552
-- ToyIL/Analyses.lean
theorem unrollAnalysis_soundUnder (k : Nat) : SoundUnder (unrollAnalysis k : Analysis σ)
```

With the key definitions unfolded (prose):

```text
soundUnder_exactOnLoopFree_no_alarm_not_imply_safe: ¬ ∀ U : Analysis Nat, (∀ P c e t, U c e P t → ∃ s, P s ∧ Exec c s e t) → (∀ P c e t, c.loopFree = true → (U c e P t ↔ ∃ s, P s ∧ Exec c s e t)) → ∀ P c, ¬ (∃ t, U c .er P t) → ∀ s t, P s → ¬ Exec c s .er t
unrollAnalysis_two_false_negative: SoundUnder (unrollAnalysis 2) ∧ ExactOnLoopFree (unrollAnalysis 2) ∧ ¬ Alarm (unrollAnalysis 2) (fun n => n = 0) countProg ∧ ¬ Safe (fun n => n = 0) countProg
unrollAnalysis_soundUnder k: ∀ P c e t, post (c.unroll k) e P t → post c e P t
```

Hypothesis ledger: no hypotheses beyond the universally quantified objects.

- **Non-vacuity witness.** unrollAnalysis 2 on countProg from x = 0; unrollAnalysis 2 does alarm on the same loop followed by assume (x = 2); error(). (`Toy.IL.unrollAnalysis_two_false_negative`, `Toy.IL.unrollAnalysis_two_alarm_two_iterations`)
- **Positive control** (nearby settings where the refuted conclusion does hold): `Toy.IL.soundOver_no_alarm_safe` (silence of a sound over-approximate analysis is safety), `Toy.IL.unrollAnalysis_three_alarm` (the analysis that unrolls every loop up to three times raises an alarm on countProg from x = 0), `Toy.IL.exactOnLoopFree_no_alarm_safe` (on a loop-free program, silence of an analysis that is exact on loop-free programs is safety).
- **Prior art.**
  - P. W. O'Hearn, "Incorrectness logic", PACMPL 4(POPL), Article 10, 2020, doi:10.1145/3371078: Section 4 states a Derived Unrolling Rule (iteration can execute its body i times) and compares it to symbolic bounded model checking (citing Clarke et al. 2004); Section 5.2 notes that under-approximation via bounded loop unrollings is well known and not sufficient in all situations.
  - A. Biere, A. Cimatti, E. M. Clarke and Y. Zhu, "Symbolic model checking without BDDs", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 1999), LNCS 1579, pp. 193-207, Springer, 1999, doi:10.1007/3-540-49059-0_14. Introduces SAT-based bounded model checking, which explores executions up to a fixed bound. Context for the bounded-unrolling witness only.
  - E. Clarke, D. Kroening and F. Lerda, "A Tool for Checking ANSI-C Programs", TACAS 2004, LNCS 2988, pp. 168-176, Springer, 2004, doi:10.1007/978-3-540-24730-2_15. The CBMC bounded model checker for C, which unrolls loops up to a bound. Context for the bounded-unrolling witness only.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `soundUnder_exactOnLoopFree_no_alarm_not_imply_safe`, `unrollAnalysis_two_false_negative`, `unrollAnalysis_soundUnder` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — Bounded exploration (loop unrolling up to a bound, as in bounded model checking) that is exact on loop-free code can miss errors that need more iterations than the bound; its silence is not a safety proof. Reasoning: the 2-unrolling witness misses an error that needs three iterations. Completeness thresholds and other bound-selection techniques of real bounded model checkers are not modeled. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 18. manifest-error-preserved-under-state-frame-extension

- **Kind / tier / depth:** theorem / T1 / shallow.
- **Tier justification.** Le et al. 2022 build frame extension into Definition 3.2 via q ∗ true in separation logic (another formalism); this toy (no heap) proves preservation, and reflection for a nonempty frame type, for disjoint product states. No mechanization of this property was found; the closest formal statement is outcome logic's characterization of manifest errors (Zilberstein et al. 2023, Lemma 6.7).
- **Plain claim.** If [P] c [er : Q] is a manifest error — a valid incorrectness error triple such that from every initial state some run of c errs in a Q state — then running c on the first component of a product state with an untouched frame component gives a manifest error [P × True] c↑ [er : Q × True]; when the frame type has an element, the converse also holds.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Manifest.lean:93-95
-- ToyIL/Manifest.lean
theorem manifestError_liftFst {τ : Type} {P Q : Assn σ} {c : Cmd σ}
    (h : ManifestError P c Q) :
    ManifestError (fun p : σ × τ => P p.1) c.liftFst (fun p => Q p.1)
-- lean/ToyIL/Manifest.lean:205-207
-- ToyIL/Manifest.lean
theorem manifestError_liftFst_iff {τ : Type} (r₀ : τ) {P Q : Assn σ} {c : Cmd σ} :
    ManifestError (fun p : σ × τ => P p.1) (c.liftFst (τ := τ)) (fun p => Q p.1) ↔
      ManifestError P c Q
```

With the key definitions unfolded (prose):

```text
manifestError_liftFst: ((∀ t, Q t → ∃ s, P s ∧ Exec c s .er t) ∧ ∀ s, ∃ t, Q t ∧ Exec c s .er t) → ((∀ p, Q p.1 → ∃ p₀, P p₀.1 ∧ Exec c.liftFst p₀ .er p) ∧ ∀ p₀, ∃ p, Q p.1 ∧ Exec c.liftFst p₀ .er p)
manifestError_liftFst_iff (r₀ : τ): ManifestError (fun p => P p.1) c.liftFst (fun p => Q p.1) ↔ ManifestError P c Q
exec_liftFst_iff: Exec c.liftFst (s, r) e (t, r') ↔ Exec c s e t ∧ r' = r
```

Hypothesis ledger:

- `h.1 : IL P c er Q (validity half of ManifestError; manifestError_liftFst)`: needed for the validity half of the conclusion. Tightness: tight: counterexample `Toy.IL.manifestError_liftFst_il_tight`.
- `h.2 : ManifestReach c Q (every-state half of ManifestError; manifestError_liftFst)`: a latent error (reachable only from some states) stays latent after extension. Tightness: tight: counterexample `Toy.IL.manifestError_liftFst_reach_tight`.
- `r₀ : τ (manifestError_liftFst_iff)`: reflection needs a frame value; over the empty frame type every lifted triple is vacuously a manifest error. Tightness: tight: counterexample `Toy.IL.manifestError_liftFst_iff_frame_tight`.

- **Non-vacuity witness.** x := 0; error() with P = True, Q = (x = 0), lifted to Nat × Nat. (`Toy.IL.nonvacuity_manifestError_liftFst`, `Toy.IL.nonvacuity_manifestError_liftFst_iff`)
- **Prior art.**
  - Q. L. Le, A. Raad, J. Villard, J. Berdine, D. Dreyer and P. W. O'Hearn, "Finding real bugs in big programs with incorrectness logic", Proceedings of the ACM on Programming Languages 6(OOPSLA1), Article 81, April 2022, doi:10.1145/3527325. Distinguishes latent from manifest errors. Definition 3.2: a valid error triple |= [p] C [er : q] denotes a manifest error iff ∀s. ∃s'. (s,s') ∈ ⟦C⟧er ∧ s' ∈ ⟦q ∗ true⟧. Theorem 3.3 gives a sufficient logical condition; Theorem 3.4 (True Positives Property): if a procedure in a complete program has a manifest error then it is dead code or ⟦main⟧er ≠ ∅.
  - N. Zilberstein, D. Dreyer and A. Silva, "Outcome logic: a unifying foundation for correctness and incorrectness reasoning", Proceedings of the ACM on Programming Languages 7(OOPSLA1), Article 93, April 2023, doi:10.1145/3586045 (full version arXiv:2303.03111). Lemma 6.7 (Manifest Error Characterization): [p] C [er : q] is a manifest error in the sense of Le et al. iff the outcome-logic triple ⟨ok : true⟩ C ⟨er : q ∗ true⟩ holds; the accompanying text observes that IL preconditions do not describe conditions sufficient to reach an end state.
  - A. Raad, J. Berdine, H.-H. Dang, D. Dreyer, P. W. O'Hearn and J. Villard, "Local reasoning about the presence of bugs: Incorrectness Separation Logic", Computer Aided Verification (CAV 2020), LNCS 12225, pp. 225-252, Springer, 2020, doi:10.1007/978-3-030-53291-8_14. Combines incorrectness logic with separation logic and states that when ISL identifies a bug there is indeed a bug (no false positives), given the assumptions of the underlying model. Heaps, separating conjunction and the frame rule are not modelled in this package.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

Basis: execution (Lean kernel check) — `manifestError_liftFst`, `manifestError_liftFst_iff` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — A manifest error found on part of the state stays manifest when unrelated, untouched state is added, and conversely when the added state type is inhabited. Reasoning: the lifted command acts only on the first component. Real separation-logic tools rely on a frame rule with disjointness, which this product model only approximates; shared resources such as allocators can break preservation (see the card's non-claims). This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

### 19. manifest-reach-iff-error-in-every-reaching-context

- **Kind / tier / depth:** characterization / T0 / shallow.
- **Tier justification.** Toy analogue of Le et al. 2022 Theorem 3.4 (True Positives Property) for one-hole syntactic contexts; the characterization is elementary.
- **Plain claim.** If running K[c] from s can arrive at the hole in state u and c can err from u into Q, then K[c] can err from s into Q. Hence c can err into Q from every state iff, for every one-hole context K and all s, u such that K[c] reaches the hole from s in state u, K[c] can err into Q from s; and if K reaches its hole from every state, K[c] can again err into Q from every state.

Lean statement(s), quoted from the sources:

```lean
-- lean/ToyIL/Manifest.lean:291-293
-- ToyIL/Manifest.lean
theorem error_in_context_of_err_at_hole {c : Cmd σ} {Q : Assn σ} {K : Ctx σ} {s u : σ}
    (hu : ∃ t, Q t ∧ Exec c u .er t) (hr : Reaches c K s u) :
    ∃ t, Q t ∧ Exec (K.fill c) s .er t
-- lean/ToyIL/Manifest.lean:311-313
-- ToyIL/Manifest.lean
theorem manifestReach_iff_forall_reaching_contexts {c : Cmd σ} {Q : Assn σ} :
    ManifestReach c Q ↔
      ∀ (K : Ctx σ) (s u : σ), Reaches c K s u → ∃ t, Q t ∧ Exec (K.fill c) s .er t
-- lean/ToyIL/Manifest.lean:318-319
-- ToyIL/Manifest.lean
theorem manifestReach_fill_of_reaches_from_every_state {c : Cmd σ} {Q : Assn σ} {K : Ctx σ}
    (hm : ManifestReach c Q) (hr : ∀ s, ∃ u, Reaches c K s u) : ManifestReach (K.fill c) Q
```

With the key definitions unfolded (prose):

```text
error_in_context_of_err_at_hole: (∃ t, Q t ∧ Exec c u .er t) → Reaches c K s u → ∃ t, Q t ∧ Exec (K.fill c) s .er t
manifestReach_iff_forall_reaching_contexts: (∀ s, ∃ t, Q t ∧ Exec c s .er t) ↔ ∀ K s u, Reaches c K s u → ∃ t, Q t ∧ Exec (K.fill c) s .er t
manifestReach_fill_of_reaches_from_every_state: (∀ s, ∃ t, Q t ∧ Exec c s .er t) → (∀ s, ∃ u, Reaches c K s u) → ∀ s, ∃ t, Q t ∧ Exec (K.fill c) s .er t
Reaches c K s u (inductive): hole: Reaches c hole s s; seqL: Reaches c K s u → Reaches c (seqL K c₂) s u; seqR: Exec c₁ s ok m → Reaches c K m u → Reaches c (seqR c₁ K) s u; choiceL/choiceR: Reaches c K s u → Reaches c (choice… K …) s u; star: Exec (star (K.fill c)) s ok m → Reaches c K m u → Reaches c (star K) s u
```

Hypothesis ledger:

- `hu : ∃ t, Q t ∧ Exec c u er t (error_in_context_of_err_at_hole)`: c must be able to err from the state in which the context enters the hole; a latent error can be avoided even when every state satisfies a valid pre of c (for [True] assume (x = 7); error() [er : x = 7], the context x := 0; [·] enters the hole in 0). Tightness: tight: counterexample `Toy.IL.error_in_context_err_at_hole_tight`.
- `hr : Reaches c K s u (error_in_context_of_err_at_hole)`: an error behind dead code produces no error. Tightness: tight: counterexample `Toy.IL.error_in_context_reaches_tight`.
- `hm : ManifestReach c Q (manifestReach_fill_of_reaches_from_every_state)`: a latent error may never be triggered by a context that reaches the hole from every state. Tightness: tight: counterexample `Toy.IL.manifestReach_fill_manifest_tight`.
- `hr : ∀ s, ∃ u, Reaches c K s u (manifestReach_fill_of_reaches_from_every_state)`: reaching the hole from some state is not enough for the every-state conclusion. Tightness: tight: counterexample `Toy.IL.manifestReach_fill_every_state_tight`.

- **Non-vacuity witness.** c = x := 0; error() inside x := x+1; (skip + [·])⋆, reaching the hole from 0 in state 1 after one complete loop iteration; the same context reaches its hole from every state. (`Toy.IL.nonvacuity_error_in_context`, `Toy.IL.nonvacuity_manifestReach_fill`)
- **Prior art.**
  - Q. L. Le, A. Raad, J. Villard, J. Berdine, D. Dreyer and P. W. O'Hearn, "Finding real bugs in big programs with incorrectness logic", Proceedings of the ACM on Programming Languages 6(OOPSLA1), Article 81, April 2022, doi:10.1145/3527325. Distinguishes latent from manifest errors. Definition 3.2: a valid error triple |= [p] C [er : q] denotes a manifest error iff ∀s. ∃s'. (s,s') ∈ ⟦C⟧er ∧ s' ∈ ⟦q ∗ true⟧. Theorem 3.3 gives a sufficient logical condition; Theorem 3.4 (True Positives Property): if a procedure in a complete program has a manifest error then it is dead code or ⟦main⟧er ≠ ∅.
  - N. Zilberstein, D. Dreyer and A. Silva, "Outcome logic: a unifying foundation for correctness and incorrectness reasoning", Proceedings of the ACM on Programming Languages 7(OOPSLA1), Article 93, April 2023, doi:10.1145/3586045 (full version arXiv:2303.03111). Lemma 6.7 (Manifest Error Characterization): [p] C [er : q] is a manifest error in the sense of Le et al. iff the outcome-logic triple ⟨ok : true⟩ C ⟨er : q ∗ true⟩ holds; the accompanying text observes that IL preconditions do not describe conditions sufficient to reach an end state.
  - P. W. O'Hearn, "Incorrectness logic", PACMPL 4(POPL), Article 10, 2020, doi:10.1145/3371078, Section 4: the existence of a consistent error assertion does not indicate a definite bug; for f(x) = {assert(x!=0);...} the error spec [x==0]f(x)[er:x==0] is valid, but no bug occurs unless a caller supplies x == 0.
- **Design question.** Which conclusions may a tool draw from an over-approximate (Hoare) result versus an under-approximate (incorrectness) result, and which inference rules may it use for each, so that 'no alarm' is read as safety only for over-approximation and 'alarm' is read as a real bug only for under-approximation?

**Full manifest errors do not transfer to contexts.** The card characterizes only the every-state
clause `ManifestReach c Q`. The following kernel-checked boundary theorem shows that the full
`ManifestError P c Q`, validity conjunct included, does not carry over to a context, even one that
reaches its hole from every state. It is not one of this card's recorded results, so it has no row
under Evidence; `support/revalidate.py` checks the axioms of every declaration of the library,
including this one.

```lean
-- lean/ToyIL/Manifest.lean:415-422
-- ToyIL/Manifest.lean
theorem manifestError_not_preserved_by_context :
    let c : Cmd Nat := .choice (.seq (.assume (fun n => n == 0)) .error)
                               (.seq (.assign (fun _ => 1)) .error)
    let P : Assn Nat := fun n => n = 0
    let Q : Assn Nat := fun n => n = 0 ∨ n = 1
    let K : Ctx Nat := .seqR (.assign (fun _ => 2)) .hole
    ManifestError P c Q ∧ (∀ s, ∃ u, Reaches c K s u) ∧
      (∀ P' : Assn Nat, ¬ ManifestError P' (K.fill c) Q)
```

In words: for this particular command c = (assume (x = 0); error()) + (x := 1; error()), pre
P = (x = 0), post Q = (x = 0 ∨ x = 1), and context K = x := 2; [·], `ManifestError P c Q` holds
and K reaches its hole from every state, yet **no** pre `P'` at all makes
`ManifestError P' (K.fill c) Q` hold with the same post Q. The theorem therefore refutes
`∃ P', ManifestError P' (K.fill c) Q` for this c, P, Q, K, not merely the instance `P' = P`. The
reason is that after x := 2 the error state 0 of Q is unreachable, so the validity conjunct
`IL P' (K.fill c) .er Q` fails for every `P'`. The theorem says nothing about other posts (for
example x = 1 alone).

Basis: execution (Lean kernel check) — `error_in_context_of_err_at_hole`, `manifestReach_iff_forall_reaching_contexts`, `manifestReach_fill_of_reaches_from_every_state` checked by the Lean 4 v4.34.1 kernel; axioms and hashes under Evidence.

Basis: derived (modeling bridge) — A manifest error can be reported independently of the calling context: every context that reaches the command reaches the error. This supports reporting manifest errors without whole-program analysis. Reasoning: an error short-circuits the rest of the program, so an error at the hole is an error of the filled program. Le et al.'s Theorem 3.4 about procedures in complete programs is the real-system statement; this is a syntactic-context analogue, not a formalization of it. This transfers to a real tool only to the extent that the tool's results mean what the toy definitions say over the tool's actual semantics and its entailment checks are sound; the toy model's gaps (Applicability) are not covered.

## Boundaries

### Non-claims

What each result does **not** show, card by card. Two non-claims apply to every card: every
theorem is about the toy semantics (see Applicability) and neither establishes nor refutes the
corresponding claim about a real analyzer or verifier, and "proved" never means "true of a
real analyzer or verifier"; the `derived (modeling bridge)` lines under Findings are reasoned
claims, not kernel-checked ones.

**1. hoare-consequence-strengthen-pre-weaken-post**

- Says nothing about incorrectness triples, whose consequence rule runs in the opposite direction (il-consequence-weaken-pre-strengthen-post); the counterexamples show each direction fails in the other logic.
- Entailments are semantic and supplied as proofs; nothing is claimed about a tool whose entailment checker is unsound or incomplete.
- Partial correctness only: says nothing about termination or about the other exit kind.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**2. il-consequence-weaken-pre-strengthen-post**

- Does not license weakening the post of an incorrectness triple: il_consequence_post_tight shows [x = 0] skip [ok : x = 0] holds but [x = 0] skip [ok : True] does not.
- Does not license strengthening the pre: il_consequence_pre_tight shows [True] skip [ok : x = 1] holds but [x = 0] skip [ok : x = 1] does not.
- Weakening the pre of an error triple [P] c [er : Q] to [True] c [er : Q] is sound, but it does not make the error manifest: [True] c [er : Q] only guarantees that some initial state reaches Q via er, not that every initial state does, nor that a caller reaching c in a state satisfying True triggers the error (il_er_true_pre_yet_caller_state_avoids_error).
- Entailments are semantic and supplied as proofs.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**3. exact-post-duality-and-or-symmetry**

- Does not say exact posts are computable or expressible in any assertion language; assertions here are arbitrary predicates.
- The two iff-laws are not characterizations of post c e P: any family of assertions of the form {Q | Q ⊆ R} (or {Q | R ⊆ Q}) satisfies the corresponding law.
- For a fixed pre P, the dual laws fail in the splitting direction: [P] c [e : Q1 ∧ Q2] does not imply [P] c [e : Q1] ∧ [P] c [e : Q2] (il_and_post_not_split, with Q1 = True, Q2 = False), and {P} c {e : Q1 ∨ Q2} does not imply {P} c {e : Q1} ∧ {P} c {e : Q2} (hoare_or_post_not_split). Incorrectness posts for a fixed pre are closed under conjunction (il_and_post_of_il_left, by strengthening the post), whereas conjoining two incorrectness triples with different pres P1 ∧ P2 is unsound in general (il-conjunction-rule-unsound); Hoare triples with different pres are closed under disjunction (conjunction-and-disjunction-rule-soundness).
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**4. il-hoare-agreement-and-denial**

- Denial refutes one specific Hoare triple {O} c {e : O'}; it does not show that c is wrong with respect to any other specification, nor that the pre O is reachable in any enclosing program.
- Agreement does not let a Hoare triple prove an incorrectness triple, or vice versa.
- An incorrectness triple with empty post never satisfies the escape hypothesis of denial (the empty assertion is contained in every O', entails_empty_left), so [U] c [er : False] never refutes any Hoare triple.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**5. hoare-invalid-iff-il-singleton-outside-post**

- The left-to-right direction is classical (it uses excluded middle): it asserts that a refuting state exists, not that one can be computed or found by a bounded search.
- The refuting incorrectness triple keeps the entire pre P; it does not isolate a single initial test state. Moreover {t} is a semantic singleton predicate and need not be expressible in any syntactic assertion language.
- Says nothing about refuting Hoare triples for the other exit kind or with a different pre.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**6. il-error-triple-nonempty-post-true-positive**

- The witness is existential over P (∃ s, P s ∧ Exec c s er t), not universal over P: even if an enclosing program reaches c in a state satisfying P — including when P = True, to which every valid pre weakens by consequence — c need not err from that state. For example [True] assume (x = 7); error() [er : x = 7] is valid, yet x := 0; assume (x = 7); error() never errs (il_er_true_pre_yet_caller_state_avoids_error). Nor does the theorem say that any caller ever reaches an error-triggering state of P (a latent error; see manifest-reach-iff-error-in-every-reaching-context).
- Does not say every error of c is in Q, or that c errs from every state of P.
- Does not say c terminates on all of P; other runs may diverge or exit normally.
- The safety characterization quantifies over all assertions Q; a single valid triple with empty post, or the empty result of any particular search, does not establish safety (il-error-triple-empty-post-does-not-imply-safety). Nothing is claimed about whether a witnessing post is expressible in a given assertion language or found by a given analysis.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**7. safety-iff-hoare-error-triple-false**

- A Hoare triple about the ok exit, {P} c {ok : Q}, says nothing about errors: {True} error() {ok : False} is valid and error() is unsafe (safe_of_hoare_er_false_tight).
- While stating safety of a whole command c needs no ok-exit triple, proving {P} c1; c2 {er : False} or {P} c⋆ {er : False} compositionally uses over-approximate ok-exit summaries and loop invariants of subcommands (hoare_seq_er_false); the error-exit triples of the parts from the same pre do not determine safety of a sequence (safe_seq_not_of_safe_parts).
- Safety here is absence of erroneous termination only; it says nothing about divergence or about the values of normal exits.
- A Hoare error triple with a satisfiable post does not show that an error is reachable (hoare-summaries-do-not-imply-reachable-error).
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**8. il-error-triple-empty-post-does-not-imply-safety**

- Does not say under-approximate reasoning can never establish safety: if every valid incorrectness error triple from P has an empty post, c is safe (the positive control safe_iff_all_il_er_posts_empty); the failure is in reading one empty result as that universal statement.
- Combining [P] c [er : False] with a valid normal-exit triple [P] c [ok : Q] whose post Q is nonempty still does not imply safety: skip + error() satisfies [True] c [ok : True] and [True] c [er : False] and is unsafe (il_ok_nonempty_and_er_empty_yet_unsafe).
- Stated over the state type Nat; over the empty state type the refuted implication holds vacuously (refuted_implications_hold_on_empty_state_space), so the negative result needs at least one state. Likewise, when P is unsatisfiable, Safe P c holds regardless of any triple.
- Does not say anything about over-approximate analyses, whose silence does imply safety (sound-analyses-license-alarms-or-silence).
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**9. hoare-summaries-do-not-imply-reachable-error**

- Part (a) works by vacuity: a Hoare error triple holds for every post when there are no erroneous runs, and post True is a valid Hoare post for every program (hoare_true_post); nonemptiness of a Hoare post therefore carries no information about reachability.
- Does not say Hoare error triples are useless: with post False they are exactly safety (safety-iff-hoare-error-triple-false).
- Does not say every Hoare-derived alarm is spurious; replacing the Hoare triple, or the over-approximate summary of the prefix, by an incorrectness triple restores the conclusion (positive controls il_er_nonempty_post_true_positive and il_ok_then_il_er_errReachable).
- Stated over the state type Nat; over the empty state type the refuted implication holds vacuously (refuted_implications_hold_on_empty_state_space), so the negative result needs at least one state.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**10. il-proof-rules-sound**

- The conjunction rule is not part of the system and is unsound (il-conjunction-rule-unsound).
- Consequence premises are semantic entailments supplied as proofs; nothing is claimed about a tool with an unsound entailment checker.
- The backwards-variant premise is infinitary (one derivation per n); nothing is claimed about finitary syntactic variants.
- iterZero is derivable from backwardsVariant, empty and conseq (iterZero_derivable); it is kept as a separate rule only to mirror O'Hearn's Fig. 2.
- Atomic updates are deterministic state functions f : σ → σ; nondeterminism comes only from binary choice and iteration. Nondeterministic assignment (x := nondet()) and the variable-specific rules of O'Hearn's Fig. 3 (assignment with substitution, constancy, local variables, substitution) are not modelled.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**11. il-conjunction-rule-unsound**

- Does not say the conjunction rule fails for every command: at a fixed (c, e) it holds for all assertions exactly when c is backward-unique at e (il_conjunction_rule_iff_backward_unique), and it is always sound for Hoare triples (positive controls).
- Escape hatches that keep a conjunction-like rule sound for every command: conjoining posts for the same pre ([P] c [e : Q1] and [P] c [e : Q2] give [P] c [e : Q1 ∧ Q2], il_conjunction_same_pre_sound), and conjoining an assertion F that c preserves backwards (every e-run ending in F started in F; the constancy idea) to both pre and post (il_conjunction_backward_preserved_sound), even for commands that merge states.
- Over a state type with at most one element (for instance Unit) the conjunction rule holds universally (il_conjunction_rule_sound_on_unit); the failure needs two distinct states.
- Concerns ordinary conjunction of assertions on a single state; separating conjunction and the frame rule of Incorrectness Separation Logic are not modelled.
- Does not concern the disjunction rule, which is sound for both logics.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**12. conjunction-and-disjunction-rule-soundness**

- The characterization is about the rule for all assertions at a fixed (c, e). A single instance of the conclusion can hold for a command that is not backward-unique, for example with empty posts (il_conjunction_instance_without_backward_unique), or with P1 = P2 (il_conjunction_same_pre_sound).
- For commands that merge states (such as assignments of constants) the rule fails for some choice of P1, P2, Q1, Q2 (in general, with different pres); it is not claimed to fail for every instance.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**13. il-proof-rules-complete**

- Relative completeness only: assertions are arbitrary predicates and entailment is an oracle; nothing is claimed about any assertion language, about decidability, or about finding derivations.
- The loop case uses an infinitary backwards-variant premise; nothing is claimed for finitary rule sets.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**14. abs-post-sound-iff-extensive**

- Soundness is not precision: the hull analysis raises false alarms (sound-overapproximate-alarm-not-a-true-positive).
- ρ need not be monotone or idempotent, so it need not be an upper closure operator; ρ ∘ post is not claimed to be a best abstract transformer. For a non-monotone extensive ρ the loop set Inv need not itself satisfy absPost ρ c ok Inv ⊆ Inv (absPost_loop_set_not_closed_of_nonmonotone, with nonMonoRho X := if X = {0} then True else X over Nat, which is extensive but not monotone); soundness does not depend on that closure.
- Inv quantifies over all assertions X, not only over the image of ρ; it is defined impredicatively and is not computable in general; no termination, widening or effective-analysis claim is made, and nothing is claimed about which other analyses (for example with widening) are sound.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**15. sound-overapproximate-alarm-not-a-true-positive**

- Does not say every alarm of a sound over-approximate analysis is false, nor that interval analysis is useless; alarms of a sound under-approximate analysis, and of the exact analysis, are true positives (positive controls).
- The witness depends on a join losing precision (hull {0, 2} contains 1); an analysis whose computed error post at (P, c) is contained in the true error post raises only true alarms there (alarm_errReachable_of_er_post_under). Locally complete abstract interpretations (Bruni et al. 2021) give conditions of this kind for a given input; that theory is not formalized here.
- The non-degeneracy condition SilentOnErrorFree only excludes analyses that alarm on programs without error() (such as topAnalysis, not_silentOnErrorFree_topAnalysis); it is not a precision guarantee.
- Stated over the state type Nat; over the empty state type the refuted implication holds vacuously (refuted_implications_hold_on_empty_state_space), so the negative result needs at least one state.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**16. sound-analyses-license-alarms-or-silence**

- The converses fail: under-approximate silence is not safety (sound-underapproximate-silence-not-safety) and over-approximate alarms are not true positives (sound-overapproximate-alarm-not-a-true-positive).
- An alarm of a sound under-approximate analysis for P (even P = True) establishes only ErrReachable P c — an existential, possibly latent error — not that any caller or enclosing context triggers it (il-error-triple-nonempty-post-true-positive, manifest-reach-iff-error-in-every-reaching-context).
- Silence of a sound over-approximate analysis establishes only absence of erroneous termination (Safe P c); it says nothing about divergence or about the correctness of normal exits.
- SoundUnder and SoundOver require soundness for all commands and both exit kinds, more than these two theorems use; compositional analyses do rely on soundness at the ok exit to propagate summaries across sequences and loops (hoare_seq_er_false, absPost).
- Soundness is with respect to this relational semantics; whether an analysis's assumptions match a real program is outside the claim.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**17. sound-underapproximate-silence-not-safety**

- Does not say bounded unrolling cannot find this bug: with k = 3 it alarms (unrollAnalysis_three_alarm).
- Does not say under-approximate silence is never informative: it is safety when the analysis is also over-approximate (soundOver_no_alarm_safe), and on loop-free programs silence of an analysis that is exact there is safety (exactOnLoopFree_no_alarm_safe). More generally, when every erroneous run from P iterates each loop at most k times, the k-unrolling finds every error and its silence is safety; that general bounded-iteration statement is not formalized here.
- The non-degeneracy condition ExactOnLoopFree excludes the trivial analysis botAnalysis (not_exactOnLoopFree_botAnalysis) and forces any unsafe program on which U is silent to contain a loop (c.loopFree = false; for unrollAnalysis k, specifically an error requiring more than k iterations of some loop). The first part is exactOnLoopFree_no_alarm_safe; the unrollAnalysis refinement is the contrapositive of the bounded-iteration remark above and is likewise not formalized here. ExactOnLoopFree does not place the missed error inside or after that loop, and it is not a completeness guarantee for programs with loops.
- Stated over the state type Nat; over the empty state type the refuted implication holds vacuously (refuted_implications_hold_on_empty_state_space), so the negative result needs at least one state.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**18. manifest-error-preserved-under-state-frame-extension**

- Frames are untouched, disjoint product components; nothing is claimed about heaps, separating conjunction, allocation, or Le et al.'s Theorem 3.3 sufficient condition. When a command and its context share a resource (for example an allocator that can return addresses the context also uses), frame preservation can fail; that is not modelled here.
- Frames that constrain the extra component (posts Q × F with F not everywhere true) are not covered: the every-state clause would fail.
- ManifestError P c Q does not require P = True: [x = 99] x := 0; error() [er : x = 0] is a manifest error (manifestError_pre_need_not_be_true), so the pre of a manifest error need not describe the states that trigger it.
- Over the empty frame type the lifted statement holds vacuously (manifestError_liftFst_iff_frame_tight); only the forward direction holds there.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

**19. manifest-reach-iff-error-in-every-reaching-context**

- Only the every-state clause ManifestReach is characterized. Full ManifestError, validity conjunct included, is not preserved by contexts, even by contexts that reach the hole from every state: manifestError_not_preserved_by_context gives a command c, pre P, post Q, and a context K that reaches its hole from every state such that ManifestError P c Q holds but ManifestError P' (K.fill c) Q fails for every pre P' (same post Q), because the IL validity conjunct fails for every P'.
- Errors are existential (may-errors): the conclusion is that some run of K[c] from s errs in Q; other nondeterministic runs of K[c] from s may exit normally or diverge.
- Exact preservation of the error post Q relies on errors short-circuiting the rest of the program, with no handlers, cleanup code or state restoration in this language.
- In loop contexts (star K'), whether the context reaches its hole depends on c itself, because earlier iterations run the filled body K'.fill c.
- A latent error can still be triggered by a context that enters the hole in a triggering state (latent_error_triggered_by_context); manifestness is what makes the conclusion independent of the context.
- Contexts are syntactic one-hole contexts of this language; there are no procedures, parameters or calls, so this is an analogue of, not a formalization of, Le et al.'s Theorem 3.4, which concludes only that main can err.
- Toy model: an abstract state type, deterministic state updates in place of assignment, no heap, no procedures or calls, no local variables, a single error kind, semantic assertions with entailment as an oracle. The kernel-checked theorems neither establish nor refute the corresponding claims about real analyzers and verifiers (incorrectness-logic bug finders, bounded model checkers, symbolic executors, Hoare-logic verifiers, abstract interpreters); the `derived (modeling bridge)` lines under Findings argue such connections separately.

### Attractive stronger readings that are not established

Each negative result comes with the nearby positive statement it must not be confused with:

- **il-error-triple-empty-post-does-not-imply-safety** refutes reading *one* empty incorrectness
  error post as safety. It does not say that under-approximate reasoning cannot establish safety:
  if *every* valid incorrectness error post from `P` is empty, `c` is safe from `P`
  (`safe_iff_all_il_er_posts_empty`).
- **hoare-summaries-do-not-imply-reachable-error** and
  **sound-overapproximate-alarm-not-a-true-positive** refute reading an over-approximate alarm,
  or an over-approximate summary composed with a true-positive triple, as a bug. They do not say
  that such alarms are usually false or that over-approximate analysis is useless: its silence is
  safety (`soundOver_no_alarm_safe`).
- **sound-underapproximate-silence-not-safety** refutes reading under-approximate silence as
  safety, even for an analysis that is exact on loop-free programs. It does not say that bounded
  exploration misses every bug: a larger bound finds this one (`unrollAnalysis_three_alarm`).
- **il-conjunction-rule-unsound** refutes the conjunction rule for incorrectness triples in
  general. It does not say that conjunction fails for every command, or for Hoare triples.
- Every negative result is stated over `Nat`. Over the empty state type the refuted implications
  of cards 8, 9, 15, and 17 hold vacuously (`refuted_implications_hold_on_empty_state_space`), so
  they need at least one state; the IL conjunction rule refuted on card 11 holds over every state
  type with at most one element (`il_conjunction_rule_sound_iff_subsingleton`), so that result
  needs at least two states.
- A "true positive" in this package is always relative to a pre and to the toy semantics, and it
  is existential over the pre: some state satisfying the pre leads to the error. Whether a real
  program ever reaches a triggering state is a separate question (manifest versus latent errors,
  cards 18 and 19), and whether the toy semantics matches a real system is a modeling bridge that
  no theorem here establishes.

### Escape hatches (what defeats each impossibility result)

- **il-error-triple-empty-post-does-not-imply-safety:** quantify over all valid error posts
  instead of one (`safe_iff_all_il_er_posts_empty`); use an over-approximate error triple with
  post `False` (`safe_iff_hoare_er_false`); or take the empty state type.
- **hoare-summaries-do-not-imply-reachable-error:** replace the over-approximate error triple or
  `ok` summary by an under-approximate one with nonempty error post
  (`il_er_nonempty_post_true_positive`, `il_ok_then_il_er_errReachable`); or take the empty state
  type.
- **il-conjunction-rule-unsound:** backward-unique commands, i.e. each final state has at most one
  predecessor (`il_conjunction_sound_of_backward_unique`; exact characterization at fixed
  `(c, e)` in `il_conjunction_rule_iff_backward_unique`); the same pre on both sides
  (`il_conjunction_same_pre_sound`); a conjunct `F` preserved backwards along `c`
  (`il_conjunction_backward_preserved_sound`); a state type with at most one element
  (`il_conjunction_rule_sound_iff_subsingleton`, `il_conjunction_rule_sound_on_unit`); or Hoare
  triples instead (`hoare_conjunction_sound`).
- **sound-overapproximate-alarm-not-a-true-positive:** an analysis that is sound
  under-approximate (`soundUnder_alarm_errReachable`) or exact
  (`exactAnalysis_alarm_iff_errReachable`), or whose computed error post at the given `(P, c)` is
  contained in the exact one (`alarm_errReachable_of_er_post_under`, a pointwise form of local
  completeness; the local-completeness logic of Bruni et al. itself is not formalized); or the
  empty state type.
- **sound-underapproximate-silence-not-safety:** an analysis that is also sound over-approximate
  (`soundOver_no_alarm_safe`); a loop-free program with an analysis exact on loop-free programs
  (`exactOnLoopFree_no_alarm_safe`); a larger unrolling bound for this program
  (`unrollAnalysis_three_alarm`); or the empty state type. The general statement that the
  `k`-unrolling is silent only on programs whose erroneous runs all need more than `k` iterations
  of some loop is not formalized here.

### Tightness status

All 31 hypotheses recorded in the hypothesis ledgers are `tight`, each with a kernel-checked
counterexample theorem stating that all other hypotheses hold and the conclusion fails. No
hypothesis is labeled `harmless`, and none has `unknown` tightness.

### Not examined

- Heaps, separating conjunction, the frame rule of incorrectness separation logic, allocation,
  and memory errors.
- Procedures, calls, parameters, and procedure summaries beyond the single sequencing example of
  card 9; Le et al.'s Theorem 3.3 sufficient condition for manifest errors.
- Concurrency, probabilistic choice, and hyperproperties (Hyper Hoare Logic and Outcome Logic are
  cited for related statements only; their logics are not formalized).
- Termination and total correctness (divergence has no outcome in this semantics).
- Assertion languages, decidability of entailment, finitary proof systems, and algorithms for
  finding derivations or computing analyses (widening, abstract domains, completeness
  thresholds).

### Refuted stronger formulations

All 19 results and all 110 declarations referenced by `results.json` are proved. One natural
strengthening of card 19 is false:

- **Full manifest errors are not preserved by reaching contexts.** It is false that whenever
  `ManifestError P c Q` holds and a context `K` reaches its hole from every state, some pre `P'`
  makes `ManifestError P' (K.fill c) Q` hold with the same post `Q`. Counterexample
  (`manifestError_not_preserved_by_context`, quoted on card 19; state `Nat`, writing `x` for the
  state): `c = (assume (x = 0); error()) + (x := 1; error())`, `P = (x = 0)`,
  `Q = (x = 0 ∨ x = 1)`, `K = x := 2; [·]`. Here `ManifestError P c Q` holds and `K` reaches its
  hole from every state, but `ManifestError P' (K.fill c) Q` fails for every `P'`: after `x := 2`
  the error state `0` of `Q` is unreachable, so the validity conjunct `IL P' (K.fill c) .er Q`
  fails. This is why card 19 characterizes the every-state clause `ManifestReach c Q`
  (`manifestReach_iff_forall_reaching_contexts`) rather than `ManifestError P c Q`, and why
  `error_in_context_of_err_at_hole` assumes only that `c` can err from the state in which the
  context enters the hole.

## Evidence

**Kernel-check record.** Basis: execution (Lean kernel check). Toolchain
`leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean
and `Std` only. `lake build` of `lean/` succeeds. Every one of the 500 declarations of the
`ToyIL` library depends on at most `propext`, `Classical.choice`, and `Quot.sound` (computed with
Lean's `collectAxioms`; 379 use no axiom at all). The Lean sources contain no `sorry`, `admit`,
`native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `@[extern]`, `unsafe`, or
`debug.skipKernelTC`. Evidence acquired 2026-11-20.

The table lists each of the 110 declarations referenced by `results.json` with its role, its
axioms, the SHA-256 of its statement, and the SHA-256 and size of its definition closure. The
statement hash is the SHA-256 of `toString (repr type)` of the declaration. The closure is the
set of `ToyIL` constants reachable from the statement through types, definition values, and
inductive constructors (theorem bodies are not followed); each member is rendered as
`name : repr(type)`, followed by ` := repr(value)` for non-theorems, and the lines are sorted and
joined with newlines before hashing. The same records are in `audit/statements.json` and
`audit/axioms.json` (axioms for all 500 declarations).

| Declaration | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.IL.absPost_sound` | result | propext | `193e31f5804a8f1e77efd086f53cb299c3c0d0e05b510de69c36b3cb6159268e` | `93d22bc702bf9e443cac9e06a6904b0f7b7e3959ec3ab3e2b65a5010f90fc6b7` (38) |
| `Toy.IL.absPost_sound_extensive_tight` | counterexample | none | `12d2cb5333dd999ecd003b4cbbd697010851daa06245b3f3cbaddf5c2ab85ac6` | `93d22bc702bf9e443cac9e06a6904b0f7b7e3959ec3ab3e2b65a5010f90fc6b7` (38) |
| `Toy.IL.alarm_errReachable_of_er_post_under` | positive control | none | `139ebf76cbde4a63d64bf26e32787ac61dcde6c4714fa7f2a149f47c195a5f90` | `bd208bab2311a41d50fad4b8a2c2e254d1d6ed2891c5d62d0af6e598fd8aeed4` (27) |
| `Toy.IL.conj_disj_rules_h1_tight` | counterexample | Quot.sound, propext | `0d661d4fc0333c113094bd3e13d0bea74a43216313ee7378ef02c194e548bd31` | `e8174dbd39da07f07514da637e7bd0755c34431b2cc7061148a398f5c3654fd3` (27) |
| `Toy.IL.conj_disj_rules_h2_tight` | counterexample | Quot.sound, propext | `8823736caeab681cf20578b17c0887a27825c6abb7d67d6df9b78a015f5ae5b8` | `e8174dbd39da07f07514da637e7bd0755c34431b2cc7061148a398f5c3654fd3` (27) |
| `Toy.IL.errReachable_iff_exists_il_er_nonempty` | result | none | `8d44e40d9e1f6e1f911e7381656743d8563c6fa327be18b7a438dbf5eeb7c586` | `6f481689f85619b67c86316fd7c54e7ce2c1af0c4aa0db5d2b7c4776ed89318f` (26) |
| `Toy.IL.error_in_context_err_at_hole_tight` | counterexample | Quot.sound, propext | `7f2a05c8dac70cea61c1cbf1a43bcf25ce58c6872d9f0b25d229142b4e03ab5b` | `5456ef8f9217942f7d4c37975a5d327ffb80bfef22a450b041ebb78d427f4ecd` (43) |
| `Toy.IL.error_in_context_of_err_at_hole` | result | none | `55c8aef7c3e4c327b883758c0ad951795f5004448dc82f49ccfead372992f771` | `b0b653b27f9bc2430f26e36ccf21c8ebd42a7d94c44cb9d7364503390d7eb6d0` (44) |
| `Toy.IL.error_in_context_reaches_tight` | counterexample | Quot.sound, propext | `50c9b8097c162051d7163ae39d1e385e8dcdd9b9db2ab92168b2186e0ba4feac` | `5456ef8f9217942f7d4c37975a5d327ffb80bfef22a450b041ebb78d427f4ecd` (43) |
| `Toy.IL.exactAnalysis_alarm_iff_errReachable` | positive control | none | `09e802e65f5bd1b27c96a2cb66b05f0ed845b7fc9315b4ef28a62a418f2d1eee` | `59c30c1607c4efe18527241495b385f897b90ddcfbf5d2703887b39c0451d792` (27) |
| `Toy.IL.exactOnLoopFree_no_alarm_safe` | positive control | none | `c280a5c8a87870b931c5780aff1d81e15daaacd7b98b2c761c3ad04a96dc237e` | `5c040618b717c7b6fbbc880c98483397b18a6e160585fadcf503b471695a7c21` (35) |
| `Toy.IL.hoare_and_il_iff_eq_post` | result | none | `915d777b662d4d1c713e8188ca1dddd1d506f7b4cc25dbb0a32ecceb979f1685` | `e81583127c135d4d375431d534eff421d9dac4d835226e0efb6968f954a72d6d` (26) |
| `Toy.IL.hoare_and_post_iff` | result | none | `31366169363dd8dffb8690f45c8b43001af7bae975d396528b82e0d4e7e7c645` | `cb36f60527f6473b4405ddfd3c5566bdd72846d5b016c88cf2be8c1f846b1d05` (25) |
| `Toy.IL.hoare_conjunction_sound` | positive control, result | none | `34a9ab9f9bf2928f76850d03fb1bfa4f0bf1b45e48a11f49955bc9aa052a41d7` | `cb36f60527f6473b4405ddfd3c5566bdd72846d5b016c88cf2be8c1f846b1d05` (25) |
| `Toy.IL.hoare_consequence_post_tight` | counterexample | propext | `18cd248ae6666d1fccc0cece6491270a0cf5568e32c7ee72c20db3466df1cc93` | `207f892cc5559129d3003dbc7cc297fe29e513d00c780dcfb25a34d07c878ecb` (26) |
| `Toy.IL.hoare_consequence_pre_tight` | counterexample | Quot.sound, propext | `536bf191e8c64a2e5faaec3073fb5d9d6ecf1eebe3ec28e7851cce43be77b145` | `207f892cc5559129d3003dbc7cc297fe29e513d00c780dcfb25a34d07c878ecb` (26) |
| `Toy.IL.hoare_consequence_strengthen_pre_weaken_post` | result | none | `ed36502826c9bbb87c16a6c13ebfc6218a56d855fa16e17bb6ba037adbbeaf93` | `cb36f60527f6473b4405ddfd3c5566bdd72846d5b016c88cf2be8c1f846b1d05` (25) |
| `Toy.IL.hoare_consequence_triple_tight` | counterexample | propext | `fd5af58db79e9a5752ce6c1ff0360e78e592eb1836029fad5b33f28423b27b68` | `207f892cc5559129d3003dbc7cc297fe29e513d00c780dcfb25a34d07c878ecb` (26) |
| `Toy.IL.hoare_disjunction_sound` | result | none | `ef931188d24a3372548e119370394c52f0c23bc1ff1fc9d8863e956f76e781e1` | `cb36f60527f6473b4405ddfd3c5566bdd72846d5b016c88cf2be8c1f846b1d05` (25) |
| `Toy.IL.hoare_er_nonempty_post_without_reachable_error` | non-vacuity, result | Quot.sound, propext | `8eb126005f73d551fece30ac5da8c21e845f4b3e14f2e6ca9a3dfa11e738983a` | `e0fc0de8881acc5c3c167c47ebdd37ebdb62ac7d2c4e8c86bed7898e37f36bfe` (27) |
| `Toy.IL.hoare_ok_summary_then_il_er_without_reachable_error` | non-vacuity, result | Quot.sound, propext | `2dc312d281be6c9d04c35865dc471f3bdb34f51df88b83854a64d025dbf8583b` | `8df2dbffbaed1cb1d92d5a3015d4d7975e3e772a3edc3b17003b5e2104de5e58` (29) |
| `Toy.IL.hullAnalysis_false_alarm` | non-vacuity, result | Quot.sound, propext | `e373b41d56c888514a446f3fab0114a92668521ae2184f42d73b9e674658abcb` | `24fabc1d9c2d28fecbe8afb94b80d6df7d5720a6fb1235099d34915be58cd718` (46) |
| `Toy.IL.hullAnalysis_silent_on_mkevenProg` | non-vacuity | Quot.sound, propext | `789427dacc2640bfa44d6801ffc5f52221532ff5c066f66b64963019eb65554c` | `b3c07d95c23ff4c68837d9e6f9de5aee4f1bb194fd1e352ced5dbb3368f38877` (39) |
| `Toy.IL.ilDeriv_complete_valid_tight` | counterexample | propext | `4f46451c98142827ecf7c982a8223c20beb51417bd90f1fa8ecaf19caf61b522` | `9ddeb70054d027c678ee033bce9e12a3a262460d66ba2f1d146298c908b27746` (40) |
| `Toy.IL.ilDeriv_count_up` | non-vacuity | none | `8efcae9a727ea7b958ed5a4d02ff121e12363d38352ce127f2ef19ff9536ebd4` | `0268de8aa9906b53dd35eaf04263a81b69b731f9bc6d4a8231c50722bb942b84` (26) |
| `Toy.IL.ilDeriv_count_up_error` | non-vacuity | Classical.choice, Quot.sound, propext | `cb0f048e87eee4e190e74979c76156f6d45fdfa4dacdcdfddcd23593da30a5e7` | `0268de8aa9906b53dd35eaf04263a81b69b731f9bc6d4a8231c50722bb942b84` (26) |
| `Toy.IL.ilDeriv_post` | result | propext | `1c2f84a3cadf693e97fed224e11208138ff2a1cbded49df3fba04aac0fb16495` | `f9569549c945ff963ea1fa8f31dfabaf6ca3d9ade225870c544965a58ee5adc6` (38) |
| `Toy.IL.ilDeriv_relatively_complete` | result | propext | `2d7ad11976dd22dbbf40c2ab167cb1063304f0b6f8db2b7ac9d40e59ba014ca8` | `b5df1a6738bb8e36a7df2fb0f4583067adb98bd58df418f23cf16d39e3d59089` (39) |
| `Toy.IL.ilDeriv_sound` | result | none | `0ca0754580804f41ed385986a76befeb82a86c1833bda40219822a7cfb0144eb` | `b5df1a6738bb8e36a7df2fb0f4583067adb98bd58df418f23cf16d39e3d59089` (39) |
| `Toy.IL.ilDeriv_sound_deriv_tight` | counterexample | propext | `6a318085a4a3182e975a2caed68d9b1e56000084639377e41f085739c6d822a6` | `9ddeb70054d027c678ee033bce9e12a3a262460d66ba2f1d146298c908b27746` (40) |
| `Toy.IL.il_backwardsVariant_sound` | result | none | `798143cb7369578e4143602372f3175e623004e66385086e7c0ed46b21f9d7c2` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.il_backwardsVariant_sound_premise_tight` | counterexample | Quot.sound, propext | `dbc8a5e4cb236e70def321efd6f7b77fc8e29a2c59b37f9e7bd37ff8f41d91e8` | `08b9d0b39e834e2ebea48cd98f5cba3ae83dd79523adca0f1d3980d532681e4b` (26) |
| `Toy.IL.il_conjunction_backward_preserved_sound` | positive control | none | `bc5a7d21c240aad7dc60ccafe182b8f50d8301cc9c38fcf2026b787f6f413555` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.il_conjunction_counterexample` | non-vacuity, result | Quot.sound, propext | `f0dc0b426c9cfea52668ded3f3c98c5c743ab8c67ae1ae5737ce0b0bbc57d0de` | `3ede363dd702c78541aec1b41e33972b2bfd6a371f07a6b5cda464394595b42d` (26) |
| `Toy.IL.il_conjunction_rule_iff_backward_unique` | result | none | `2c801d6cebcf42f44e77f5caf967059524710a87803e5b23ab6321acaa5a8d81` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.il_conjunction_rule_sound_iff_subsingleton` | result | none | `4d3a6ab9c45627fa5cce7e826710ee64e911c45d0377f1f7d18cfdc992a18ebb` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.il_conjunction_rule_sound_on_unit` | non-vacuity, positive control | none | `81b829288c9830de81ed034d4200a424307d0b035190cb6af72f108cfa40ca13` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.il_conjunction_rule_unsound` | result | Quot.sound, propext | `3ddc889a892f664a06a2d4de38d8798f466e6c76d25e47b7975ccbb068c2adc5` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.il_conjunction_same_pre_sound` | positive control | none | `71ba44095f51e4fe662079b5964d8e21e31bd252df6c4a0ca03a794321668d83` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.il_conjunction_sound_of_backward_unique` | positive control, result | none | `c4957a985142296c08cbd86dfeb05606c639453594b60d114a38be9f96d16ae8` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.il_conjunction_sound_of_backward_unique_tight` | counterexample | Quot.sound, propext | `87772a9f582cfce10be99b51a4ff094af90b992e255817c41e6a6e6ab14f321e` | `3ede363dd702c78541aec1b41e33972b2bfd6a371f07a6b5cda464394595b42d` (26) |
| `Toy.IL.il_consequence_post_tight` | counterexample | Quot.sound, propext | `b5ea53e7c619f5ffbd56bd865b146e889ac3cdd6daacd602fed66a68c859b06d` | `2c83e390a432bc1f3cbdf8a148eab45c12773853160da6e5098a114c937f5672` (26) |
| `Toy.IL.il_consequence_pre_tight` | counterexample | Quot.sound, propext | `c0a0093d6eb5e985f6f16a54c25659be4a3093cb3f99d04f394f080193cf86e1` | `2c83e390a432bc1f3cbdf8a148eab45c12773853160da6e5098a114c937f5672` (26) |
| `Toy.IL.il_consequence_triple_tight` | counterexample | Quot.sound, propext | `1c921e9d94b01e5881705a02c64e2892335459da8bc4ec53e86e1fcab5beceda` | `2c83e390a432bc1f3cbdf8a148eab45c12773853160da6e5098a114c937f5672` (26) |
| `Toy.IL.il_consequence_weaken_pre_strengthen_post` | result | none | `9c42ca7599f7cc3f7aa33b5adc873e2dd0224c6f789a6108d97eea0050a929c2` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.il_denies_hoare` | result | none | `ff3373461a651aee81d26bda4c3d82c33db7eef3c04191f1ba53a402d3948c72` | `e81583127c135d4d375431d534eff421d9dac4d835226e0efb6968f954a72d6d` (26) |
| `Toy.IL.il_denies_hoare_hout_tight` | counterexample | Quot.sound, propext | `ad16ac48c82cdbea2b9ef2372e5c5cfb5ea5faf01246e1f448df6ac4ad3c38a3` | `e81583127c135d4d375431d534eff421d9dac4d835226e0efb6968f954a72d6d` (26) |
| `Toy.IL.il_disjunction_sound` | result | none | `9d287fbcdeb894aaf77386bf3891ad960448f6abead2d14c9592d4ebf0fa1961` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.il_empty_post` | result | none | `e1182b37d39eac2d96c6bd3fb9fd6bf589885aefb6f7c24f3d7939aa8b33c276` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.il_er_empty_post_valid_yet_unsafe` | non-vacuity, result | none | `080f2a4bbe147e5a7ccde5f816ce8adcdf2025e271f91b4d0df8c6bb826303af` | `32bed4ec58aebc1af3e43b69604955078e6d508800fada8c34eade68213d413a` (26) |
| `Toy.IL.il_er_nonempty_post_true_positive` | positive control, result | none | `34d3c9a79e3ec08351704f1ac0fcbacc350d70e859de4ee02a285134c4fc7c6f` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.il_er_nonempty_post_true_positive_il_tight` | counterexample | propext | `cba9fa857fa9c7d9ada98505361bc9c8364e980ff13b09d06c5dd31e3865170f` | `2c83e390a432bc1f3cbdf8a148eab45c12773853160da6e5098a114c937f5672` (26) |
| `Toy.IL.il_er_nonempty_post_true_positive_nonempty_tight` | counterexample | none | `c2349f07df099c5dfad2635f642fee64faa613968733c21d0ccecf04328ec114` | `2c83e390a432bc1f3cbdf8a148eab45c12773853160da6e5098a114c937f5672` (26) |
| `Toy.IL.il_hoare_agreement` | result | none | `cde40d20f7f8e8ee2b2e30a80ee4b934cda5a056b501c08851443a865b069b8c` | `e81583127c135d4d375431d534eff421d9dac4d835226e0efb6968f954a72d6d` (26) |
| `Toy.IL.il_hoare_agreement_hoare_tight` | counterexample | propext | `0b1ee548aeab58599aa581718ddd0ace4bac1e5a729008804a79d8fccaae309b` | `e8174dbd39da07f07514da637e7bd0755c34431b2cc7061148a398f5c3654fd3` (27) |
| `Toy.IL.il_hoare_agreement_il_tight` | counterexample | Quot.sound, propext | `d9bd791013bf436b34cd2b27c83b12700d8e2af80d4d1b24629a7249af41fc27` | `e8174dbd39da07f07514da637e7bd0755c34431b2cc7061148a398f5c3654fd3` (27) |
| `Toy.IL.il_hoare_agreement_sub_tight` | counterexample | Quot.sound, propext | `db8810517e4f9cd1de586bbff1c193b46f21f7304e34af2cb3509c3a89698863` | `e8174dbd39da07f07514da637e7bd0755c34431b2cc7061148a398f5c3654fd3` (27) |
| `Toy.IL.il_ok_then_il_er_errReachable` | positive control | none | `97523acf2c7436ab0778f49b6ee0b404857d72a64bd70da642b58194c647c9a6` | `6f481689f85619b67c86316fd7c54e7ce2c1af0c4aa0db5d2b7c4776ed89318f` (26) |
| `Toy.IL.il_or_post_iff` | result | none | `ce3a169058245fafff1d80381f7ae19495b348dae76c33c3fcbb477c3890d011` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.manifestError_liftFst` | result | none | `4a75cff011323d53b3b81a7bd4c83389cb48abafa4fd855cf3c8708269382e08` | `c5e4876a84e1638c7213e6a7d0811689935264699ce3439b63f957b46103348c` (35) |
| `Toy.IL.manifestError_liftFst_iff` | result | propext | `cab2ba673157f63a9ee9127dd5e69fbdb86c324cb59a65ec3d019ed653ad5788` | `c5e4876a84e1638c7213e6a7d0811689935264699ce3439b63f957b46103348c` (35) |
| `Toy.IL.manifestError_liftFst_iff_frame_tight` | counterexample | propext | `503eae497106014b60507a7f1f02d9c5e8619cdea861b110e519732c0504e4a5` | `9ac4b8dd6c1ca7976e9352cd6b2da0fa5cdaa9925c619f7f064141a154316274` (36) |
| `Toy.IL.manifestError_liftFst_il_tight` | counterexample | Quot.sound, propext | `57551169e25070c7cce3e2c1722683c4c26f088df97a62634c1f2ab5d60d2e19` | `c5e4876a84e1638c7213e6a7d0811689935264699ce3439b63f957b46103348c` (35) |
| `Toy.IL.manifestError_liftFst_reach_tight` | counterexample | Quot.sound, propext | `96d3e3d893bcff4ea1b2b1fc145e71cc91382faef4652b8fd4207338f4ba146e` | `c5e4876a84e1638c7213e6a7d0811689935264699ce3439b63f957b46103348c` (35) |
| `Toy.IL.manifestReach_fill_every_state_tight` | counterexample | Quot.sound, propext | `062a571a2f55063da480271f6cbedcd4ae0380db9af42464892096ff3d17b151` | `b6be8c323a1107654075aec760d58872c580745eb3c3909560aab0e34742c24c` (45) |
| `Toy.IL.manifestReach_fill_manifest_tight` | counterexample | Quot.sound, propext | `d3aefeb23b333cff3dad66368f8d7acfe5d187b56d04370ee10a51b71631c9b4` | `b6be8c323a1107654075aec760d58872c580745eb3c3909560aab0e34742c24c` (45) |
| `Toy.IL.manifestReach_fill_of_reaches_from_every_state` | result | none | `39f770f2e52a273bb5191c6aef37d111a294c6ee39c2f69563e11da6c6f1c3ba` | `b6be8c323a1107654075aec760d58872c580745eb3c3909560aab0e34742c24c` (45) |
| `Toy.IL.manifestReach_iff_forall_reaching_contexts` | result | none | `a801ab4ae193105457fa9e1e68f7da1eaf26a67bc1a2f36ce4fa7f702cb02fb0` | `b6be8c323a1107654075aec760d58872c580745eb3c3909560aab0e34742c24c` (45) |
| `Toy.IL.nonvacuity_absPost_sound` | non-vacuity | propext | `6c17b6534eb969033050e56e25425e9d6f05951d8ac4f22a5e126302bf9171a8` | `ef1a4b855798c83419860f562a247c42a2ef2199bedad0575bacac9bb1593b06` (39) |
| `Toy.IL.nonvacuity_agreement` | non-vacuity | Quot.sound, propext | `dc8f3b207da0cebac9c93bc5037c78c127f877f9935d60607615245c162a6067` | `e81583127c135d4d375431d534eff421d9dac4d835226e0efb6968f954a72d6d` (26) |
| `Toy.IL.nonvacuity_analysis_licensing` | non-vacuity | propext | `98e52f8f5c79722eb3f94b8c9e43311571b58f0bbee89a89083589d36cdd5ca6` | `8cbf6f6f43933179cdccb33a6338e9896265c3a5ba5f87600e23b40f1b090f64` (32) |
| `Toy.IL.nonvacuity_backwardsVariant` | non-vacuity | propext | `987fffb803a9178f43924fd3ab77df7f93b25977e1fa5704c06de30c205aa568` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.nonvacuity_conj_disj` | non-vacuity | Quot.sound, propext | `9c7cb6f854a09192e0336ef9bbab729612806ef089105d788764173c7347db4a` | `e81583127c135d4d375431d534eff421d9dac4d835226e0efb6968f954a72d6d` (26) |
| `Toy.IL.nonvacuity_denial` | non-vacuity | none | `2cc61bbedfb5757b09aed5621368975a58c2ee879702c4b0f60df6b2ac4b9cc7` | `e81583127c135d4d375431d534eff421d9dac4d835226e0efb6968f954a72d6d` (26) |
| `Toy.IL.nonvacuity_duality` | non-vacuity | Quot.sound, propext | `02cf147d0a3683b8d7a35f816721f684413603c79a2ff85b3f7cee352ebbbfaa` | `e81583127c135d4d375431d534eff421d9dac4d835226e0efb6968f954a72d6d` (26) |
| `Toy.IL.nonvacuity_error_in_context` | non-vacuity | none | `f68e320f6274be77cadf3d307618df92a9eb7383ff66e25b9957ee73ecb9831d` | `633d38b3d1aef3798a0a095564c4515296b5cf50354e28828bac74738da569eb` (46) |
| `Toy.IL.nonvacuity_hoare_consequence` | non-vacuity | Quot.sound, propext | `79d22d885872c1ff5b07621b60f62564189d7cd236a30f5274042fa9291063fc` | `cb36f60527f6473b4405ddfd3c5566bdd72846d5b016c88cf2be8c1f846b1d05` (25) |
| `Toy.IL.nonvacuity_hoare_safe` | non-vacuity | Quot.sound, propext | `f3121c0f24f1663b0eefe773336d17f4b494d379388ca1d982cff6d320585138` | `cb36f60527f6473b4405ddfd3c5566bdd72846d5b016c88cf2be8c1f846b1d05` (25) |
| `Toy.IL.nonvacuity_ilDeriv_complete` | non-vacuity | Classical.choice, Quot.sound, propext | `cd083ce2422433720d91b7b7d1be8cc86590634a7f116f76d32cd346d1e7188a` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.nonvacuity_ilDeriv_sound` | non-vacuity | Classical.choice, Quot.sound, propext | `f1f82587b93b9cc1bc836ff6b2c69ad02e683a7d07abe0b970eb908da4732751` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.nonvacuity_il_characterization` | non-vacuity | Quot.sound, propext | `29e22262b456dde86499abe65a1a7d3e8f5f97d4ded0a44f2bc18afa43c6ad29` | `a26bcabadd7ff72fded5621ceab53f1b67fb0e4dc46e5ca868e1c78753174c8f` (24) |
| `Toy.IL.nonvacuity_il_conjunction_backward_unique` | non-vacuity | Quot.sound, propext | `5eb018bfc47ea6967eeb516f9ad070cd029fff5e783c3856bfeb40c8429b7c83` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.nonvacuity_il_conjunction_rule_iff` | non-vacuity | Quot.sound, propext | `c06999cce09cb9ef148b76f39da81a5018ee345cf168147e9f8e11ae305082b3` | `617066faa3203d6b9943317d0350faae914ff1eb8fb1dea232094f28e913a9e6` (22) |
| `Toy.IL.nonvacuity_il_consequence` | non-vacuity | Quot.sound, propext | `baa92f17d8eb5f96ba5816861687e52930835d6c214b3611eb059388911f6595` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.nonvacuity_il_true_positive` | non-vacuity | none | `bb6c53b25a48f30348a70eb32adf647795e8225ff0398437c456381b9daf9021` | `60bbb87069050c263f2be59bf8d11b7f7ae05493b9599cc8ab76df4cefb490fa` (25) |
| `Toy.IL.nonvacuity_manifestError_liftFst` | non-vacuity | none | `670d67f1cfcb2e1c1de86c7cea10274b58b211fec1e0010f6842883d22245dc2` | `c5e4876a84e1638c7213e6a7d0811689935264699ce3439b63f957b46103348c` (35) |
| `Toy.IL.nonvacuity_manifestError_liftFst_iff` | non-vacuity | none | `367d918c49966dcbc64c5fe57722ea95e48cac0efe5423ed8bb759383b05e3d6` | `c5e4876a84e1638c7213e6a7d0811689935264699ce3439b63f957b46103348c` (35) |
| `Toy.IL.nonvacuity_manifestReach_fill` | non-vacuity | none | `67aeeef796dd0560669df7e791329c16670c15c026ddc118b9b9e6c2428cd03a` | `633d38b3d1aef3798a0a095564c4515296b5cf50354e28828bac74738da569eb` (46) |
| `Toy.IL.nonvacuity_not_hoare_singleton` | non-vacuity | none | `81df16c7248b84ecfd7112cb3b40e50c3eb9afde8f925a6b1d90b0b57c9c2848` | `e81583127c135d4d375431d534eff421d9dac4d835226e0efb6968f954a72d6d` (26) |
| `Toy.IL.not_hoare_er_nonempty_post_implies_errReachable` | result | Quot.sound, propext | `a656e4423aaefa08a5a5b4db1cef87c506839b2fae91a8ac6c2a591faf1724f2` | `186a498316d5d47ad3674e65783cc2b524923d977602baf5948a6339a429bf61` (26) |
| `Toy.IL.not_hoare_iff_exists_il_singleton_outside` | result | Classical.choice, Quot.sound, propext | `3918b19a7c0a4239bffca3c5fb94d6327ff81bafc7053cdd4dd83c5bab83464e` | `e81583127c135d4d375431d534eff421d9dac4d835226e0efb6968f954a72d6d` (26) |
| `Toy.IL.not_hoare_ok_then_il_er_implies_errReachable` | result | Quot.sound, propext | `9f82efa481e09e81c3ec87895561bdeb0af0ccc578235a0f36b443fc1185b3c3` | `11b12d05ac3b9cdfb54a6d041967782c93ea29ede78b59fbcc2b3ad3cdd31d69` (27) |
| `Toy.IL.not_il_er_empty_post_implies_safe` | result | none | `8f8a22dabec675cf46a2a9090c43059105b3d9aa549029297da13250d53efa67` | `32bed4ec58aebc1af3e43b69604955078e6d508800fada8c34eade68213d413a` (26) |
| `Toy.IL.safe_iff_all_il_er_posts_empty` | positive control, result | propext | `4b02e13619ea6f4d836743c4a598331328934f91d537329ba5e3c25e05657fd9` | `32bed4ec58aebc1af3e43b69604955078e6d508800fada8c34eade68213d413a` (26) |
| `Toy.IL.safe_iff_hoare_er_false` | result | propext | `14e6f6598f195cf46f38bc73ca3ba8eb6440cc9ff45ba7dfc0f16186e724a7a7` | `759b83660e2cdad6b86e2dc1f7a2d12a3b20ea5fe6c18c18f43a43ed76e9a502` (26) |
| `Toy.IL.safe_of_hoare_er_false` | result | propext | `068572fee80f9bc904102f05cdf868c98068d395b991fa53f4924e50bb335fb1` | `759b83660e2cdad6b86e2dc1f7a2d12a3b20ea5fe6c18c18f43a43ed76e9a502` (26) |
| `Toy.IL.safe_of_hoare_er_false_tight` | counterexample | propext | `4076d127d7fe7f3afc7e0f0c42ea19df34db739c5d03618c56f9cdb8416a9aec` | `759b83660e2cdad6b86e2dc1f7a2d12a3b20ea5fe6c18c18f43a43ed76e9a502` (26) |
| `Toy.IL.soundOver_absPost_iff_extensive` | result | Quot.sound, propext | `226ef3210180cee080f707c26c52ff22b21fae6051053adf193a6455c0e5e666` | `93d22bc702bf9e443cac9e06a6904b0f7b7e3959ec3ab3e2b65a5010f90fc6b7` (38) |
| `Toy.IL.soundOver_no_alarm_safe` | positive control, result | none | `d72d24b68e443d187996b9911ed9bf029a19896e412875ae38f156f3c1401d05` | `db3f96f392bcd29172ef5160c900b9053d88d0919861871ce9ecfcec326e474a` (29) |
| `Toy.IL.soundOver_no_alarm_safe_alarm_tight` | counterexample | none | `094e376aa01f521599fd325776f6b3b00eaa1ca0740cad53c0ef415e06efcdab` | `688de8d842b1cb6a1751f6b8bcba19aa16e1522211f08c9bc98b2796eec236fe` (30) |
| `Toy.IL.soundOver_no_alarm_safe_tight` | counterexample | none | `71a6b18a6f01f3b49a22de98b06cdf7d3330f63df6a41a20548a96f4c896d36a` | `138c2feeac9c075c72158f411620d673cd367fc0b3f98f59429537321837e21d` (30) |
| `Toy.IL.soundOver_silentOnErrorFree_alarm_not_imply_errReachable` | result | Quot.sound, propext | `836e4cab27ac0e5415de96f0b105d3708acb81aafb72c97ebf002bf3a64ef57d` | `edc7455cf2b7ee9fe6833217298763e2369a46be5594d17341a8784b152ac552` (38) |
| `Toy.IL.soundUnder_alarm_errReachable` | positive control, result | none | `873f60f2d78f6204c8c051591c0a0bc0009cd71449cf19da343890a851bcc238` | `41e46a581c6554fb3a41a48f94c453382c0e0a9010e9a9a680cd2796e2c87eea` (29) |
| `Toy.IL.soundUnder_alarm_errReachable_alarm_tight` | counterexample | propext | `49e64f9e0ae9d672e5ef2b8039ad9dd331e1a35fab5f1ee3fda2b350ebe43214` | `23bd4ace6a404eecce35e0a59b2be2aff7b33fac18de1ecd7bd67a5138b165df` (31) |
| `Toy.IL.soundUnder_alarm_errReachable_tight` | counterexample | propext | `9cb37295c0ef2b9bb460054970d93f1969fcd6d5abfd2684e21fe7562cbc3cdd` | `92956b0aeb50a335f40954073edc562c71b24b46965755d064371de12fe12c14` (31) |
| `Toy.IL.soundUnder_exactOnLoopFree_no_alarm_not_imply_safe` | result | Quot.sound, propext | `7b51173402028633045c39c20137c5c4882c987631e7bbc69857da64b6dd070f` | `17713c76fe1112d9a9a54d6055fbb0f52224f642bc72709f15386b0a2d09a13d` (38) |
| `Toy.IL.unrollAnalysis_soundUnder` | result | propext | `b1c9043d1b82a09e1c301bc27b641ef3c1bcaec08aba5cc7f5703972d9c9af4f` | `1cabe0276cba7289d5576a8612e60d7e0bf1bdadc3e639f2686744ffebe207c2` (40) |
| `Toy.IL.unrollAnalysis_three_alarm` | positive control | Quot.sound, propext | `910942d82a75ff577dc6f2391e8eb23d83fc3088e28ec0d3dab39efe8699fc32` | `2664df3c3e6502274886ae979821977e56cf71c60383771274f2cfb34c157253` (39) |
| `Toy.IL.unrollAnalysis_two_alarm_two_iterations` | non-vacuity | Quot.sound, propext | `aaf69111076cee9765e859d1d9e560820a31177021f0ceee73ec0ce97b3d97e5` | `fdfd6600ad6c47deefa5f93f7d12e4c60e9ee996232d045a3421a8dacf1261e9` (38) |
| `Toy.IL.unrollAnalysis_two_false_negative` | non-vacuity, result | Quot.sound, propext | `0316d71acf8f911368a1ee1f8ae08d8cf2e6eac416255f38e706d1b97409a3f1` | `7287cb5b3afae1e4d62edefa4d4b2baa7f30124ef217f8f426acc78929e58c37` (46) |

### Primary sources

Exact records, with what was read. Citations in the cards above quote only what these sources
were checked to contain.

- P. W. O'Hearn, "Incorrectness Logic", *Proceedings of the ACM on Programming Languages* 4(POPL),
  Article 10, January 2020, doi:10.1145/3371078. Read in the author's PDF: Definition 1,
  Lemma 3, Figs. 1, 2 and 4, Theorems 5 and 6, and Sections 2, 3.3, 4 and 5.2.
- Q. L. Le, A. Raad, J. Villard, J. Berdine, D. Dreyer and P. W. O'Hearn, "Finding Real Bugs in Big
  Programs with Incorrectness Logic", *Proceedings of the ACM on Programming Languages*
  6(OOPSLA1), Article 81, April 2022, doi:10.1145/3527325. Read: Definition 3.2, Theorems 3.3
  and 3.4.
- B. Möller, P. W. O'Hearn and T. Hoare, "On Algebra of Program Correctness and Incorrectness",
  RAMiCS 2021, LNCS 13027, pp. 325–343, Springer, 2021, doi:10.1007/978-3-030-88701-8_20. Read in
  the authors' PDF: Theorem 3.2, Lemma 3.4, Theorems 4.1, 4.4 and 4.5, Section 4.4, Section 5.
- E. de Vries and V. Koutavas, "Reverse Hoare Logic", SEFM 2011, LNCS 7041, pp. 155–171,
  Springer, 2011, doi:10.1007/978-3-642-24690-6_12. Read in the authors' PDF: Definition 1, Fig. 2,
  Theorems 1 and 2.
- N. Zilberstein, D. Dreyer and A. Silva, "Outcome Logic: A Unifying Foundation for Correctness and
  Incorrectness Reasoning", *Proceedings of the ACM on Programming Languages* 7(OOPSLA1),
  Article 93, April 2023, doi:10.1145/3586045; full version arXiv:2303.03111. Read: Corollary 5.7
  and Lemma 6.7 in the full version (the card paraphrases Corollary 5.7 rather than reproducing
  its displayed formula).
- A. Raad, J. Berdine, H.-H. Dang, D. Dreyer, P. W. O'Hearn and J. Villard, "Local Reasoning about
  the Presence of Bugs: Incorrectness Separation Logic", CAV 2020, LNCS 12225, pp. 225–252,
  Springer, 2020, doi:10.1007/978-3-030-53291-8_14. Read: the passage stating that bugs identified
  by the logic are true positives under the model's assumptions.
- T. Dardinier and P. Müller, "Hyper Hoare Logic: (Dis-)Proving Program Hyperproperties",
  *Proceedings of the ACM on Programming Languages* 8(PLDI), Article 207, June 2024,
  doi:10.1145/3656437; arXiv:2301.10037. Read: Theorem 5 and Proposition 6. Cited as a related
  hyper-triple result, not as the same statement.
- R. Bruni, R. Giacobazzi, R. Gori and F. Ranzato, "A Logic for Locally Complete Abstract
  Interpretations", LICS 2021, doi:10.1109/LICS52264.2021.9470608. Read in the authors' PDF: the
  abstract and Corollary V.5 (Precision).
- P. Cousot and R. Cousot, "Systematic Design of Program Analysis Frameworks", POPL 1979,
  pp. 269–282, doi:10.1145/567752.567778. Only Patrick Cousot's published summary page of the
  paper was read (its statement on isotony in Section 7); the scanned paper itself was not read,
  and the card attributes the statement to that summary.
- Cited for bibliographic facts and what their titles and abstracts state only: C. A. R. Hoare,
  "An Axiomatic Basis for Computer Programming", *Communications of the ACM* 12(10), pp. 576–580,
  1969, doi:10.1145/363235.363259; P. Cousot and R. Cousot, "Abstract Interpretation: A Unified
  Lattice Model for Static Analysis of Programs by Construction or Approximation of Fixpoints",
  POPL 1977, pp. 238–252, doi:10.1145/512950.512973; E. Clarke, D. Kroening and F. Lerda, "A Tool
  for Checking ANSI-C Programs", TACAS 2004, LNCS 2988, pp. 168–176,
  doi:10.1007/978-3-540-24730-2_15; A. Biere, A. Cimatti, E. M. Clarke and Y. Zhu, "Symbolic Model
  Checking without BDDs", TACAS 1999, LNCS 1579, pp. 193–207, doi:10.1007/3-540-49059-0_14;
  T. Nipkow, "Abstract Interpretation of Annotated Commands", ITP 2012, LNCS 7406, pp. 116–132,
  doi:10.1007/978-3-642-32347-8_9; C. Zhang, A. Azevedo de Amorim and M. Gaboardi, "On
  Incorrectness Logic and Kleene Algebra with Top and Tests", *Proceedings of the ACM on
  Programming Languages* 6(POPL), Article 29, 2022, doi:10.1145/3498690; F. Verbeek, M. S. Sefat,
  Z. Fu and B. Ravindran, "On Extending Incorrectness Logic with Backwards Reasoning",
  *Proceedings of the ACM on Programming Languages* 9(POPL), Article 14, 2025,
  doi:10.1145/3704850.
- Mechanization entries (entry and abstract pages): T. Murray, "An Under-Approximate Relational
  Logic", Archive of Formal Proofs, March 2020,
  https://isa-afp.org/entries/Relational-Incorrectness-Logic.html; T. Dardinier, "Formalization of
  Hyper Hoare Logic", Archive of Formal Proofs, 2023,
  https://isa-afp.org/entries/HyperHoareLogic.html; T. Nipkow, `Abs_Int_ITP2012`, Archive of
  Formal Proofs, https://isa-afp.org/entries/Abs_Int_ITP2012.html.

The DOIs of the papers listed as subjects in `REPORT.json` were re-checked against their titles,
authors, and venues on 2026-11-20.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`,
`leanprover/lean4:v4.34.1`) and `python3`. No network access is needed after the toolchain is
installed; the project has no Lake dependencies.

**Primary check.** From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package: it copies `lean/` to a temporary directory and
then

1. runs `lake build` and fails if the build fails;
2. scans the Lean sources (comments stripped) for `sorry`, `admit`, `native_decide`, and `axiom`
   declarations;
3. writes and runs an inline Lean audit program (`lake env lean RevalidateAudit.lean`) that
   computes `collectAxioms` for every declaration of the `ToyIL` library and fails if any depends
   on an axiom other than `propext`, `Classical.choice`, `Quot.sound`;
4. for every name referenced by `results.json` (result names, non-vacuity witnesses, positive
   controls, and counterexamples) or recorded in `audit/statements.json`, recomputes the
   statement hash (SHA-256 of `toString (repr type)`) and the closure hash (SHA-256 of the sorted,
   newline-joined lines `name : repr(type)`, plus ` := repr(value)` for non-theorems, over all
   `ToyIL` constants reachable from the statement through types, definition values, and inductive
   constructors; theorem bodies are not followed) and compares both, and the closure size, with
   `audit/statements.json`.

It prints one `ok`/`FAIL` line per check and `REVALIDATED`, and exits with status 0, iff all checks
pass.

**Manual axiom audit.** From the package directory:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` is outside the library target. It imports `ToyIL` and runs
`#print axioms` for each of the 110 declarations listed under Evidence; compare its output with
the Axioms column there.

**Scope of these checks.** A passing run establishes that the recorded statements and the
definitions they depend on are unchanged and kernel-checked with the standard axioms. It does
not re-examine the prose: the plain claims, non-claims, and modeling-bridge lines must be
re-read against the quoted Lean statements after any change. Statement hashes are computed from
Lean's `repr` output, which may change across Lean releases even when meaning does not; after a
toolchain change, a hash mismatch calls for re-reading the affected statements, not automatic
rejection.
