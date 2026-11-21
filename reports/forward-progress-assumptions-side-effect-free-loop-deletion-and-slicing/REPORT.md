# Forward-progress assumptions, side-effect-free loop deletion, and slicing: a Lean 4 toy model

## Summary

This package is a kernel-checked Lean 4 model of a deterministic While language whose only observable effect is
`emit`, under three behaviour semantics: a divergence-observable semantics `ObsBeh` (silent divergence is an
observable outcome, the reading under which Rust's `loop {}` is defined), a thread-level forward-progress semantics
`FPBeh` (a run that never terminates and eventually stops emitting is undefined behaviour, the reading behind C++
[intro.progress] and LLVM `mustprogress`), and a per-loop semantics `MixedBeh` in which each loop carries its own
progress flag. Its 13 results characterize when deleting an emit-free loop and slicing with respect to all `emit`
statements are refinements under each semantics, and what an inliner must do when code from the two regimes is
merged. Every result below is proved in Lean (`Basis: execution (Lean kernel check)`); statements about C, C++, LLVM
or rustc are separate modelling-bridge claims (`Basis: derived (modeling bridge)`) in **Findings**.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

The non-claims of every result are listed first under **Boundaries**; read them before applying a result. One
sentence per result (each is the result's plain-language claim, verbatim):

1. **`loop-deletion-unsound-divergence-observable`** (`loopDeletion_spin_not_refines_divergenceObservable`): Under the divergence-observable semantics, for either loop flag mp, deleting `while 1 do skip` from `while 1 do skip ;; emit 1` is not a refinement: from every initial state the target `emit 1` terminates emitting [1], while the source has the behaviour `div []` (it silently diverges with empty trace) and never terminates emitting [1].
2. **`loop-deletion-sound-forward-progress`** (`deleteEmitFreeLoop_withDeadWrites_refines_forwardProgress`): Under the forward-progress semantics, for every prefix p, condition b, flag mp, loop body body and continuation k: if the body is emit-free (hEmit) and the variables it writes are dead before k in every state reachable at the end of p (hDead), then deleting `while b do body` from `p ;; while b do body ;; k` is a refinement. The theorem has no termination hypothesis: the loop may diverge from reachable states.
3. **`loop-deletion-exact-condition-divergence-observable`** (`deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff`): Under the divergence-observable semantics, for an emit-free loop body (hEmit) whose written variables are dead before k in every state reachable at the end of p (hDead), deleting the loop from `p ;; loop ;; k` is a refinement iff from every state reachable at the end of a terminating run of p, the loop terminates or k itself silently diverges with empty trace (`ObsBeh k s₁ (div [])`).
4. **`loop-deletion-termination-condition-not-necessary`** (`deleteLoop_refines_divergenceObservable_without_termination`): Deleting the always-diverging loop `while 1 do skip` from `skip ;; while 1 do skip ;; while 1 do skip` is a divergence-observable refinement although the loop terminates from no state; the hypotheses of the exact characterization hold (the body skip is emit-free and writes nothing), so 'deletion is a refinement only if the loop terminates from every reachable entry state' is false.
5. **`loop-deletion-iff-terminates-under-nonsilent-continuation`** (`deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff_terminates`): Corollary of the exact characterization: if additionally k never has the behaviour `div []` at a state reachable at the end of p (hNoSilentK), then, for an emit-free body (hEmit) whose writes are dead before k at reachable states (hDead), deleting the loop from `p ;; loop ;; k` is a divergence-observable refinement iff the loop terminates from every state reachable at the end of p.
6. **`forward-progress-admits-divergence-observable-refinements`** (`refines_forwardProgress_of_refines_divergenceObservable_strict`): Divergence-observable refinement is strictly stronger than forward-progress refinement: for all programs src and tgt, if tgt refines src under the divergence-observable semantics then tgt refines src under the forward-progress semantics, and there exist programs src and tgt such that tgt refines src under forward progress but not under the divergence-observable semantics.
7. **`classic-slice-preserves-terminating-traces`** (`classicSlice_preserves_terminating_traces`): For every classic slice c' of c with respect to all emit statements (hSlice), every state s and every trace t: if c terminates from s emitting t, then c' terminates from s emitting t.
8. **`classic-slice-may-terminate-when-original-diverges`** (`classicSlice_spin_terminates_while_original_diverges`): `skip ;; emit 1` is a classic slice of `while 1 do skip ;; emit 1`; from every state the original silently diverges with empty trace while the slice terminates emitting [1], so this classic slice is not a divergence-observable refinement.
9. **`termination-sensitive-slice-preserves-behaviours`** (`terminationSensitiveSlice_preserves_obsBeh`): For every termination-guarded slice c' of c with respect to all emit statements (hSlice: every dropped sub-command terminates from every state), every state s and behaviour b: c' has behaviour b from s under the divergence-observable semantics iff c does, including silent divergence and infinite traces.
10. **`classic-slice-refines-forward-progress`** (`classicSlice_refines_forwardProgress`): For all commands c and c', if c' is a classic slice of c with respect to all emit statements (hSlice), then c' refines c under the thread-level forward-progress semantics. Equivalently (refines_fpBeh_iff_silentlyDiverges_or_obsBeh_iff; the instance is classicSlice_silentlyDiverges_or_obsBeh_iff): from every initial state s, either c silently diverges from s (undefined behaviour under forward progress) or c' has exactly the same divergence-observable behaviours from s as c.
11. **`per-loop-semantics-restricts-to-both-global-semantics`** (`mixedBeh_markAll_restricts`): For every command c, state s and behaviour b: the per-loop semantics of c with every loop flagged (c.markAll true) admits b from s iff the thread-level forward-progress semantics of c does, and the per-loop semantics of c with no loop flagged (c.markAll false) admits b from s iff the divergence-observable semantics of c does.
12. **`unmarked-inlining-of-divergence-observable-callee-miscompiles`** (`inlineUnmarked_divergenceObservableCallee_not_refines`): For the forward-progress call site `skip ;; call g ;; emit 1` (hazardSite) and the divergence-observable callee g whose body is `while 1 do skip` (spinFn), the linked program has no progress violation from any state, inlining g so that the caller's attribute flags the inlined loop yields a progress violation from every state and is not a per-loop refinement, and replacing the now-flagged loop by skip (giving `skip ;; skip ;; emit 1`) refines the inlined program but not the linked one.
13. **`attribute-dropping-inlining-refines`** (`inlineDroppingAttr_refines_linked`): For every top-level call site `pre ;; call g ;; post` with caller attribute cm and every callee g with attribute gm, inlining g and giving every loop of the merged body the attribute cm && gm refines the linked program under the per-loop semantics.

## Applicability

### Model fidelity

This is a **toy model**, not a model of any production compiler intermediate representation. All definitions live
in the Lean namespace `Toy.Progress` (Lake library `Toy`).

* **Language.** Natural-number variables, side-effect-free expressions (`num`, `var`, `add`, truncated `sub`, `lt`,
  `eq`), and commands `skip`, `assign`, `emit`, `seq`, `ite`, and `loop mp b body` (`while b do body` with a
  Boolean progress flag `mp`). Execution is a deterministic small-step function; from each initial state a command
  has exactly one run. Termination, silent divergence and infinite output are defined from the finite prefixes of
  that run (no coinduction). Final states are not observable; only the emitted trace is.
* **What the three semantics are meant to capture.**
  * `ObsBeh` (divergence-observable): terminating with a finite trace, diverging after a finite trace, and reacting
    forever with an infinite trace are three distinct observable behaviours. Intended to capture Rust's treatment of
    `loop {}` as defined behaviour and CompCert-style behaviour sets (`Terminates`, `Diverges`, `Reacts`), without
    CompCert's `Goes_wrong`.
  * `FPBeh` (thread-level forward progress): a run that never terminates and from some point on emits nothing
    (`SilentlyDiverges`) is undefined behaviour and admits every behaviour; otherwise the behaviours are those of
    `ObsBeh`. Intended to capture the first paragraph of C++ [intro.progress] and LLVM's `mustprogress` function
    attribute, read as a property of the whole run.
  * `MixedBeh` (per-loop flags): undefined behaviour arises only when a loop whose own flag is set is entered and that
    loop itself completes infinitely many iterations of its body, from some iteration on emitting nothing
    (`SilentlyIterates`). Intended to capture code in which loops compiled under the two regimes are mixed, for
    example after inlining, as in LLVM where `isMustProgress(L)` consults the enclosing function's attribute or the
    loop's own `llvm.loop.mustprogress` metadata.
* **Refinement** `Refines sem src tgt` means: from every initial state, every `sem`-behaviour of `tgt` is a
  `sem`-behaviour of `src`. Because execution is deterministic and `ObsBeh` has no undefined-behaviour case, every run
  has exactly one divergence-observable behaviour (`obsBeh_exists`, `obsBeh_unique`), so `Refines ObsBeh` coincides
  with behavioural equivalence (`refines_obsBeh_iff_equiv`), and `Refines FPBeh src tgt` holds iff from every initial
  state either `src` silently diverges or `tgt` and `src` have the same divergence-observable behaviours
  (`refines_fpBeh_iff_silentlyDiverges_or_obsBeh_iff`).
* **Known gaps** (none of these is modelled): pointers, memory, volatile accesses, atomics, threads and synchronization;
  input; any undefined behaviour other than the progress obligations; nondeterminism; recursion and general function
  calls (a single top-level call site is modelled by the `CallSite` construction only); loops nested inside other
  constructs as deletion targets (deletion is formalized for `p ;; loop ;; k` only); the C11 exemption of loops with a
  constant controlling expression and the C++ trivial-infinite-loop exemption; LLVM's replacement of an exitless deleted
  loop by `unreachable`; LLVM loop metadata as distinct from the per-loop flag; slicing criteria other than "all
  `emit` statements"; interprocedural slicing; any slicing or liveness algorithm (the slice relations and the deadness
  condition are declarative and semantic).

### Toolchain

Lean 4 `v4.34.1` (`leanprover/lean4`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library only: **no
Mathlib** and no other Lake dependency (`lean/lakefile.toml` declares one `[[lean_lib]]`, `Toy`, and no
`[[require]]`). Modules: `Toy.Progress.{Syntax, Semantics, RunLemmas, BigStep, Iteration, Examples, Deletion, Slicing,
Mixing, Characterizations}`; `import Toy` and `import Toy.Progress` each bring all ten into scope.

### How the subjects relate

The Lean toolchain is the checker of every theorem. The papers in `REPORT.json` are prior art for the known results
restated here (Weiser; Reps and Yang; Ranganath et al.; Back and von Wright; Leroy). The C++ working draft, the LLVM
revision, the CompCert revision, WG21 P2809R3, C11 draft N1570, C++ draft N4861 and the rustc merge commit are real
systems or specifications that the toy definitions are *interpreted against* in the modelling-bridge claims; none of
them was executed, and no theorem quantifies over them.

## Findings

### Definitions

The key definitions, quoted verbatim from the Lean sources (doc comments omitted). Statements below use Lean's
anonymous-constructor notation (`.seq`, `.loop`, `.emit`, ...) for `Cmd` and `Exp` constructors; `spin mp` is
`while 1 do skip` with flag `mp`. In prose, `xN` is variable `N`, `c₁ ;; c₂` is `.seq c₁ c₂`, and `while⁺ b do c` and
`while⁻ b do c` are `.loop true b c` and `.loop false b c`.

#### Syntax (`Toy/Progress/Syntax.lean`)

```lean
abbrev Var := Nat

abbrev Val := Nat

abbrev State := Var → Val

def State.update (s : State) (x : Var) (v : Val) : State :=
  fun y => if y = x then v else s y

inductive Exp where
  | num (n : Nat)
  | var (x : Var)
  | add (a b : Exp)
  | sub (a b : Exp)
  | lt (a b : Exp)
  | eq (a b : Exp)
  deriving DecidableEq, Repr

def Exp.eval (s : State) : Exp → Val
  | .num n => n
  | .var x => s x
  | .add a b => a.eval s + b.eval s
  | .sub a b => a.eval s - b.eval s
  | .lt a b => if a.eval s < b.eval s then 1 else 0
  | .eq a b => if a.eval s = b.eval s then 1 else 0

def Exp.vars : Exp → List Var
  | .num _ => []
  | .var x => [x]
  | .add a b | .sub a b | .lt a b | .eq a b => a.vars ++ b.vars

inductive Cmd where
  | skip
  | assign (x : Var) (e : Exp)
  | emit (e : Exp)
  | seq (c₁ c₂ : Cmd)
  | ite (b : Exp) (c₁ c₂ : Cmd)
  | loop (mp : Bool) (b : Exp) (body : Cmd)
  deriving DecidableEq, Repr

def Cmd.writes : Cmd → List Var
  | .skip | .emit _ => []
  | .assign x _ => [x]
  | .seq c₁ c₂ | .ite _ c₁ c₂ => c₁.writes ++ c₂.writes
  | .loop _ _ c => c.writes

def Cmd.noEmit : Cmd → Bool
  | .skip | .assign _ _ => true
  | .emit _ => false
  | .seq c₁ c₂ | .ite _ c₁ c₂ => c₁.noEmit && c₂.noEmit
  | .loop _ _ c => c.noEmit

def EmitFree (c : Cmd) : Prop := c.noEmit = true

def Cmd.markAll (m : Bool) : Cmd → Cmd
  | .seq c₁ c₂ => .seq (c₁.markAll m) (c₂.markAll m)
  | .ite b c₁ c₂ => .ite b (c₁.markAll m) (c₂.markAll m)
  | .loop _ b c => .loop m b (c.markAll m)
  | c => c

def spin (mp : Bool) : Cmd := .loop mp (.num 1) .skip
```

#### Execution and behaviours (`Toy/Progress/Semantics.lean`)

```lean
def step : Cmd → State → Option (Cmd × State × List Val)
  | .skip, _ => none
  | .assign x e, s => some (.skip, State.update s x (e.eval s), [])
  | .emit e, s => some (.skip, s, [e.eval s])
  | .seq c₁ c₂, s =>
      match step c₁ s with
      | none => some (c₂, s, [])
      | some (c₁', s', o) => some (.seq c₁' c₂, s', o)
  | .ite b c₁ c₂, s => some (if b.eval s = 0 then c₂ else c₁, s, [])
  | .loop mp b body, s => some (.ite b (.seq body (.loop mp b body)) .skip, s, [])

def run : Nat → Cmd → State → Cmd × State × List Val
  | 0, c, s => (c, s, [])
  | n + 1, c, s =>
      match step c s with
      | none => (c, s, [])
      | some (c', s', o) =>
          let r := run n c' s'
          (r.1, r.2.1, o ++ r.2.2)

def traceAt (n : Nat) (c : Cmd) (s : State) : List Val := (run n c s).2.2

def TermsWith (c : Cmd) (s : State) (t : List Val) (s' : State) : Prop :=
  ∃ n, run n c s = (.skip, s', t)

def Terminates (c : Cmd) (s : State) : Prop := ∃ t s', TermsWith c s t s'

def Diverges (c : Cmd) (s : State) : Prop := ∀ n, (run n c s).1 ≠ .skip

inductive Beh where
  | term (t : List Val)
  | div (t : List Val)
  | react (f : Nat → Val)

def prefixOf (f : Nat → Val) (k : Nat) : List Val := (List.range k).map f

def ObsBeh (c : Cmd) (s : State) : Beh → Prop
  | .term t => ∃ s', TermsWith c s t s'
  | .div t => Diverges c s ∧ ∃ N, ∀ n, N ≤ n → traceAt n c s = t
  | .react f => ∀ k, ∃ n, traceAt n c s = prefixOf f k

def SilentlyDiverges (c : Cmd) (s : State) : Prop := ∃ t, ObsBeh c s (.div t)

def FPBeh (c : Cmd) (s : State) (b : Beh) : Prop :=
  SilentlyDiverges c s ∨ ObsBeh c s b

def Cmd.head : Cmd → Cmd
  | .seq c₁ _ => c₁.head
  | c => c

def SilentlyIterates (b : Exp) (body : Cmd) (s : State) : Prop :=
  ∃ σ : Nat → State, ∃ o : Nat → List Val, σ 0 = s ∧
    (∀ i, b.eval (σ i) ≠ 0 ∧ TermsWith body (σ i) (o i) (σ (i + 1))) ∧
    ∃ N, ∀ i, N ≤ i → o i = []

def ProgressViolation (c : Cmd) (s : State) : Prop :=
  ∃ n b body, (run n c s).1.head = .loop true b body ∧
    SilentlyIterates b body (run n c s).2.1

def MixedBeh (c : Cmd) (s : State) (b : Beh) : Prop :=
  ProgressViolation c s ∨ ObsBeh c s b

def Refines (sem : Cmd → State → Beh → Prop) (src tgt : Cmd) : Prop :=
  ∀ s b, sem tgt s b → sem src s b

def AgreeOff (X : List Var) (s₁ s₂ : State) : Prop := ∀ y, y ∉ X → s₁ y = s₂ y

def DeadAtEntry (X : List Var) (k : Cmd) : Prop :=
  ∀ s₁ s₂, AgreeOff X s₁ s₂ → ∀ b, ObsBeh k s₁ b ↔ ObsBeh k s₂ b

def ReachableAt (p : Cmd) (s₁ : State) : Prop := ∃ s₀ t, TermsWith p s₀ t s₁

def DeadAfterPrefix (p : Cmd) (X : List Var) (k : Cmd) : Prop :=
  ∀ s₁ s₂, ReachableAt p s₁ → AgreeOff X s₁ s₂ → ∀ b, ObsBeh k s₁ b ↔ ObsBeh k s₂ b
```

#### Big-step runs and finite execution prefixes (`Toy/Progress/BigStep.lean`)

```lean
-- lean/Toy/Progress/BigStep.lean lines 18-32
inductive BigStep : Cmd → State → List Val → State → Prop
  | skip (s : State) : BigStep .skip s [] s
  | assign (x : Var) (e : Exp) (s : State) : BigStep (.assign x e) s [] (State.update s x (e.eval s))
  | emit (e : Exp) (s : State) : BigStep (.emit e) s [e.eval s] s
  | seq {c₁ c₂ : Cmd} {s s₁ s₂ : State} {t₁ t₂ : List Val} :
      BigStep c₁ s t₁ s₁ → BigStep c₂ s₁ t₂ s₂ → BigStep (.seq c₁ c₂) s (t₁ ++ t₂) s₂
  | iteT {b : Exp} {c₁ c₂ : Cmd} {s s' : State} {t : List Val} :
      b.eval s ≠ 0 → BigStep c₁ s t s' → BigStep (.ite b c₁ c₂) s t s'
  | iteF {b : Exp} {c₁ c₂ : Cmd} {s s' : State} {t : List Val} :
      b.eval s = 0 → BigStep c₂ s t s' → BigStep (.ite b c₁ c₂) s t s'
  | loopExit {mp : Bool} {b : Exp} {body : Cmd} {s : State} :
      b.eval s = 0 → BigStep (.loop mp b body) s [] s
  | loopIter {mp : Bool} {b : Exp} {body : Cmd} {s s₁ s₂ : State} {t₁ t₂ : List Val} :
      b.eval s ≠ 0 → BigStep body s t₁ s₁ → BigStep (.loop mp b body) s₁ t₂ s₂ →
      BigStep (.loop mp b body) s (t₁ ++ t₂) s₂

-- lean/Toy/Progress/BigStep.lean line 248
def Reach (c : Cmd) (s : State) (t : List Val) : Prop := ∃ n, traceAt n c s = t

-- lean/Toy/Progress/BigStep.lean lines 252-266
inductive Partial : Cmd → State → List Val → Prop
  | nil (c : Cmd) (s : State) : Partial c s []
  | emit (e : Exp) (s : State) : Partial (.emit e) s [e.eval s]
  | seqL {c₁ c₂ : Cmd} {s : State} {t : List Val} : Partial c₁ s t → Partial (.seq c₁ c₂) s t
  | seqR {c₁ c₂ : Cmd} {s s₁ : State} {t₁ t₂ : List Val} :
      BigStep c₁ s t₁ s₁ → Partial c₂ s₁ t₂ → Partial (.seq c₁ c₂) s (t₁ ++ t₂)
  | iteT {b : Exp} {c₁ c₂ : Cmd} {s : State} {t : List Val} :
      b.eval s ≠ 0 → Partial c₁ s t → Partial (.ite b c₁ c₂) s t
  | iteF {b : Exp} {c₁ c₂ : Cmd} {s : State} {t : List Val} :
      b.eval s = 0 → Partial c₂ s t → Partial (.ite b c₁ c₂) s t
  | loopBody {mp : Bool} {b : Exp} {body : Cmd} {s : State} {t : List Val} :
      b.eval s ≠ 0 → Partial body s t → Partial (.loop mp b body) s t
  | loopIter {mp : Bool} {b : Exp} {body : Cmd} {s s₁ : State} {t₁ t₂ : List Val} :
      b.eval s ≠ 0 → BigStep body s t₁ s₁ → Partial (.loop mp b body) s₁ t₂ →
      Partial (.loop mp b body) s (t₁ ++ t₂)
```

`BigStep c s t s'`: `c` run from `s` terminates in `s'` having emitted `t` (equivalent to `TermsWith c s t s'` by
`termsWith_iff_bigStep`, quoted below). `Reach c s t`: after some finite number
of small steps from `(c, s)` the emitted output is `t`. `Partial c s t` describes the same finite output prefixes
structurally; the two are equivalent by `reach_iff_partial`. Both equivalences are quoted under *Supporting lemmas
cited by name* below.

#### Slicing (`Toy/Progress/Slicing.lean`)

```lean
abbrev VarSet := Var → Prop

inductive IsSlice (ts : Bool) : VarSet → Cmd → Cmd → VarSet → Prop
  | skip (R : VarSet) : IsSlice ts R .skip .skip R
  | assign (R R' : VarSet) (x : Var) (e : Exp)
      (h : ∀ y, (R y ∧ y ≠ x) ∨ y ∈ e.vars → R' y) :
      IsSlice ts R (.assign x e) (.assign x e) R'
  | emit (R R' : VarSet) (e : Exp) (h : ∀ y, R y ∨ y ∈ e.vars → R' y) :
      IsSlice ts R (.emit e) (.emit e) R'
  | seq (R R₁ R' : VarSet) (c₁ c₁' c₂ c₂' : Cmd) :
      IsSlice ts R c₂ c₂' R₁ → IsSlice ts R₁ c₁ c₁' R' →
      IsSlice ts R (.seq c₁ c₂) (.seq c₁' c₂') R'
  | ite (R R₁ R₂ R' : VarSet) (b : Exp) (c₁ c₁' c₂ c₂' : Cmd) :
      IsSlice ts R c₁ c₁' R₁ → IsSlice ts R c₂ c₂' R₂ →
      (∀ y, R₁ y ∨ R₂ y ∨ y ∈ b.vars → R' y) →
      IsSlice ts R (.ite b c₁ c₂) (.ite b c₁' c₂') R'
  | loop (R I I' : VarSet) (mp : Bool) (b : Exp) (c c' : Cmd) :
      (∀ y, R y ∨ y ∈ b.vars → I y) → IsSlice ts I c c' I' → (∀ y, I' y → I y) →
      IsSlice ts R (.loop mp b c) (.loop mp b c') I
  | drop (R : VarSet) (c : Cmd) :
      EmitFree c → (∀ y, y ∈ c.writes → ¬ R y) → (ts = true → ∀ s, Terminates c s) →
      IsSlice ts R c .skip R

def IsClassicSlice (c c' : Cmd) : Prop := ∃ R', IsSlice false (fun _ => False) c c' R'

def IsTerminationSensitiveSlice (c c' : Cmd) : Prop :=
  ∃ R', IsSlice true (fun _ => False) c c' R'

-- lean/Toy/Progress/Slicing.lean line 177
def AgreeOn (R : VarSet) (s s' : State) : Prop := ∀ y, R y → s y = s' y
```

#### Functions and inlining (`Toy/Progress/Mixing.lean`)

```lean
structure Fn where
  body : Cmd
  mustProgress : Bool

def Fn.code (f : Fn) : Cmd := f.body.markAll f.mustProgress

structure CallSite where
  pre : Cmd
  post : Cmd
  mustProgress : Bool

def CallSite.linked (cs : CallSite) (g : Fn) : Cmd :=
  .seq (cs.pre.markAll cs.mustProgress) (.seq g.code (cs.post.markAll cs.mustProgress))

def CallSite.inlineUnmarked (cs : CallSite) (g : Fn) : Cmd :=
  (Cmd.seq cs.pre (.seq g.body cs.post)).markAll cs.mustProgress

def CallSite.inlineDroppingAttr (cs : CallSite) (g : Fn) : Cmd :=
  (Cmd.seq cs.pre (.seq g.body cs.post)).markAll (cs.mustProgress && g.mustProgress)

def hazardSite : CallSite := { pre := .skip, post := .emit (.num 1), mustProgress := true }

def spinFn : Fn := { body := spin false, mustProgress := false }

def callerLoopSite : CallSite := { pre := spin false, post := .emit (.num 1), mustProgress := true }
```

#### Concrete commands used by examples and counterexamples (`Examples.lean`, `Deletion.lean`)

```lean
def beep (mp : Bool) : Cmd := .loop mp (.num 1) (.emit (.num 7))

def x0IsZero : Exp := .eq (.var 0) (.num 0)

def flaggedOverUnflagged : Cmd := .loop true x0IsZero (.seq (spin false) (.assign 0 (.num 1)))

def unflaggedOverFlagged : Cmd := .loop false x0IsZero (.seq (spin true) (.assign 0 (.num 1)))

def emitBody : Cmd := .seq (.emit (.num 7)) (.assign 0 (.num 1))

def resetBody : Cmd := .assign 0 (.num 1)

def countBody : Cmd := .assign 1 (.add (.var 1) (.num 1))

def countLoop : Cmd := .loop false x0IsZero countBody

def setX2 : Cmd := .assign 2 (.num 1)

def guardedEmit : Cmd := .ite (.eq (.var 2) (.num 0)) (.emit (.var 1)) (.emit (.var 0))
```

**What the core definitions are meant to capture, with proved intended examples.** Example theorems whose statement
hashes are not recorded under **Evidence** are given with the proposition each proves (file under `lean/Toy/Progress/`
and line of the theorem; universally quantified variables written in words).

* `EmitFree c` — `c` contains no `emit` anywhere (the toy's notion of a side-effect-free command). Positive:
  `emitFree_example_pos` (`Syntax.lean` line 101): `EmitFree (.loop false (.eq (.var 0) (.num 0)) (.assign 0 (.num 1)))`.
  Negative (an `emit` nested in a conditional in a loop is detected): `emitFree_example_neg` (`Syntax.lean` line 105):
  `¬ EmitFree (.loop false (.num 1) (.ite (.var 0) (.emit (.num 7)) .skip))`.
* `Cmd.writes`, `Cmd.markAll` — positive: `writes_example` (`Syntax.lean` line 109):
  `(Cmd.seq (.assign 3 (.num 0)) (.loop false (.var 3) (.ite (.var 1) (.assign 4 (.num 1)) (.emit (.var 5))))).writes = [3, 4]`
  (assignment targets in loop bodies and branches are collected); `markAll_example` (`Syntax.lean` line 118):
  `(Cmd.seq (spin false) (.loop false (.var 0) (spin false))).markAll true = .seq (spin true) (.loop true (.var 0) (spin true))`
  (nested loops are reached). Negative: `writes_example_neg` (`Syntax.lean` line 115): `5 ∉ (Cmd.emit (.var 5)).writes`
  (reading is not writing); `markAll_example_neg` (`Syntax.lean` line 123): `(spin false).markAll true ≠ .loop true (.num 0) .skip`
  (only flags change; the loop condition is kept).
* `SilentlyIterates` / `ProgressViolation` / `MixedBeh` — the progress obligation belongs to the innermost loop that
  fails to make progress. Positive: `mixedBeh_example_ub` (`Examples.lean` line 114): for every state `s`,
  `MixedBeh (.seq (spin true) (.emit (.num 1))) s (.term [42])` (entering a flagged loop that silently iterates is a
  progress violation, so every behaviour is admitted); `progressViolation_unflaggedOverFlagged` (a flagged loop nested in
  an unflagged one is blamed). Negative: `mixedBeh_example_neg` (`Examples.lean` line 126): for every state `s`,
  `¬ MixedBeh (.seq (spin false) (.emit (.num 1))) s (.term [42])` (the same loop unflagged is divergence-observable);
  `not_progressViolation_beep` (`Examples.lean` line 159): for every state `s`, `¬ ProgressViolation (beep true) s` (a
  flagged loop that keeps emitting); `not_progressViolation_flaggedOverUnflagged` and `mixedBeh_flaggedOverUnflagged`
  (`while⁺ x0 = 0 do (while⁻ 1 do skip ;; x0 := 1)` from a state with `x0 = 0` has no progress violation and has
  exactly the behaviour `div []`). Every silent divergence enters some loop that silently iterates
  (`exists_head_silentlyIterates`), and a progress violation implies silent divergence
  (`silentlyDiverges_of_progressViolation`).
* `DeadAfterPrefix p X k` — the variables in `X` are dead at the entry of `k` in every state reachable at the end of
  `p`. Implied by the all-state condition `DeadAtEntry X k` (`deadAfterPrefix_of_deadAtEntry`) and strictly weaker
  (`deadAfterPrefix_example_not_deadAtEntry`: after `x2 := 1`, `x1` is dead before
  `if x2 = 0 then emit x1 else emit x0`, but not from arbitrary states).
* `IsSlice ts R c c' R'` — `c'` arises from `c` by replacing sub-commands with `skip`; no `emit` is ever removed; data
  and control dependences are respected; a dropped sub-command must be emit-free and write no relevant variable, and
  with `ts = true` must also terminate from every state (a semantic, undecidable premise). Here `R` is the set of
  relevant variables after the command and `R'` the set before it. Positive: `isClassicSlice_example` (`Slicing.lean`
  line 70): `IsClassicSlice (.seq countLoop (.emit (.num 1))) (.seq .skip (.emit (.num 1)))` (the possibly diverging loop
  `while⁻ x0 = 0 do x1 := x1 + 1` is deleted); `isTerminationSensitiveSlice_example` (`Slicing.lean` line 78):
  `IsTerminationSensitiveSlice (.seq countLoop (.emit (.num 1))) (.seq (.loop false x0IsZero .skip) (.emit (.num 1)))` (the
  loop and its condition are kept and only the always-terminating body is dropped);
  `isTerminationSensitiveSlice_drops_terminating_loop`; and every command is a slice of itself: `isSlice_refl`
  (`Slicing.lean` line 90): for every flag `ts`, command `c` and set `R`, there is `R'` with `IsSlice ts R c c R'`; also
  `isClassicSlice_refl`, `isTerminationSensitiveSlice_refl`. Negative: `not_isSlice_drop_emit` (`Slicing.lean` line 116):
  for every `ts`, `R`, `R'` and `e`, `¬ IsSlice ts R (.emit e) .skip R'`; `not_isClassicSlice_drop_definition`
  (`Slicing.lean` line 124; data dependence):
  `¬ IsClassicSlice (.seq (.assign 0 (.num 5)) (.emit (.var 0))) (.seq .skip (.emit (.var 0)))`;
  `not_isClassicSlice_drop_guard_definition` (`Slicing.lean` line 137; control dependence):
  `¬ IsClassicSlice (.seq (.assign 1 (.num 0)) (.ite (.var 1) (.emit (.num 1)) .skip)) (.seq .skip (.ite (.var 1) (.emit (.num 1)) .skip))`;
  `not_isTerminationSensitiveSlice_spin`.
* `CallSite.linked` / `inlineUnmarked` / `inlineDroppingAttr` — the meaning of `pre ;; call g ;; post` before inlining
  (the callee's loops keep the callee's attribute) and two inlining strategies. Examples, all with the call site
  `hazardSite` and the callee `spinFn` quoted above except the last: `linked_hazard` (`Mixing.lean` line 58):
  `hazardSite.linked spinFn = .seq .skip (.seq (spin false) (.emit (.num 1)))` (the callee's loop stays unflagged);
  `inlineUnmarked_hazard` (`Mixing.lean` line 62):
  `hazardSite.inlineUnmarked spinFn = .seq .skip (.seq (spin true) (.emit (.num 1)))` (unmarked inlining flags it);
  `inlineDroppingAttr_hazard` (`Mixing.lean` line 67):
  `hazardSite.inlineDroppingAttr spinFn ≠ .seq .skip (.seq (spin true) (.emit (.num 1)))` (attribute-dropping inlining does
  not flag it); `inlineDroppingAttr_eq_linked_of_both` (`Mixing.lean` line 73): for all commands `pre`, `post` and `body`,
  if both the call site and the callee have `mustProgress := true`, then attribute-dropping inlining of the callee
  produces exactly the linked program.

#### Supporting lemmas cited by name (`Toy/Progress/BigStep.lean`, `Toy/Progress/Slicing.lean`)

The definitions above, the depth notes of results 7, 9 and 10 and the non-claims of result 10 cite the following
proved lemmas, quoted verbatim (proofs omitted). `slice_partial_fwd` is also a companion of result 10, with its
statement hash recorded under **Evidence**; the other five are not results or companions and carry no recorded
statement hash, but like every declaration of the `Toy` library they appear in the axiom record `audit/axioms.json`
(`termsWith_iff_bigStep`: `propext`; `reach_iff_partial`: `propext`; `slice_bigStep_fwd`, `slice_bigStep_bwd`,
`slice_partial_bwd`: `Quot.sound`, `propext`).

```lean
-- lean/Toy/Progress/BigStep.lean lines 128-129
theorem termsWith_iff_bigStep {c : Cmd} {s s' : State} {t : List Val} :
    TermsWith c s t s' ↔ BigStep c s t s'

-- lean/Toy/Progress/BigStep.lean line 384
theorem reach_iff_partial {c : Cmd} {s : State} {t : List Val} : Reach c s t ↔ Partial c s t

-- lean/Toy/Progress/Slicing.lean lines 200-203
theorem slice_bigStep_fwd {ts : Bool} {c : Cmd} {s : State} {t : List Val} {s₁ : State}
    (hB : BigStep c s t s₁) :
    ∀ {R R' : VarSet} {c' : Cmd} {s' : State}, IsSlice ts R c c' R' → AgreeOn R' s s' →
      ∃ s₁', BigStep c' s' t s₁' ∧ AgreeOn R s₁ s₁'

-- lean/Toy/Progress/Slicing.lean lines 279-282
theorem slice_partial_fwd {ts : Bool} {c : Cmd} {s : State} {t : List Val}
    (hP : Partial c s t) :
    ∀ {R R' : VarSet} {c' : Cmd} {s' : State}, IsSlice ts R c c' R' → AgreeOn R' s s' →
      Partial c' s' t

-- lean/Toy/Progress/Slicing.lean lines 342-345
theorem slice_bigStep_bwd {c' : Cmd} {s' : State} {t : List Val} {s₁' : State}
    (hB : BigStep c' s' t s₁') :
    ∀ {R R' : VarSet} {c : Cmd} {s : State}, IsSlice true R c c' R' → AgreeOn R' s s' →
      ∃ s₁, BigStep c s t s₁ ∧ AgreeOn R s₁ s₁'

-- lean/Toy/Progress/Slicing.lean lines 413-415
theorem slice_partial_bwd {c' : Cmd} {s' : State} {t : List Val} (hP : Partial c' s' t) :
    ∀ {R R' : VarSet} {c : Cmd} {s : State}, IsSlice true R c c' R' → AgreeOn R' s s' →
      Partial c s t
```

In words: `termsWith_iff_bigStep` says that the big-step relation describes exactly the terminating small-step runs,
and `reach_iff_partial` says that the structural prefixes `Partial` are exactly the outputs `Reach` observed
after finitely many small steps. `slice_bigStep_fwd` says that every terminating run of `c` from `s` is reproduced,
with the same output, by any slice `c'` of `c` run from any state `s'` that agrees with `s` on the slice's entry set
`R'`, ending in states that agree on the exit set `R`; `slice_partial_fwd` says that, under the same agreement on
`R'`, every finite output prefix `Partial c s t` is also one of `c'` from `s'`. `slice_bigStep_bwd` and
`slice_partial_bwd` are the converse directions, stated for termination-sensitive slices (`ts = true`) only.

### Results

Every theorem in this section: `Basis: execution (Lean kernel check)` — proved in Lean 4 `v4.34.1` with no axioms beyond `propext`, `Classical.choice` and `Quot.sound` (per-declaration record under **Evidence**). Claims about real systems appear only on the separate `Basis: derived (modeling bridge)` lines.

#### 1. `loop-deletion-unsound-divergence-observable`

* **Theorem:** `Toy.Progress.loopDeletion_spin_not_refines_divergenceObservable`
* **Kind:** counterexample; **tier:** T1; **depth:** `shallow` — a concrete computation of two runs.
* Basis: execution (Lean kernel check)

**Plain claim.** Under the divergence-observable semantics, for either loop flag mp, deleting `while 1 do skip` from `while 1 do skip ;; emit 1` is not a refinement: from every initial state the target `emit 1` terminates emitting [1], while the source has the behaviour `div []` (it silently diverges with empty trace) and never terminates emitting [1].

**Lean statement**, `lean/Toy/Progress/Deletion.lean` line 140:

```lean
theorem loopDeletion_spin_not_refines_divergenceObservable (mp : Bool) :
    (∀ s, ObsBeh (.emit (.num 1)) s (.term [1]) ∧
          ObsBeh (.seq (spin mp) (.emit (.num 1))) s (.div []) ∧
          ¬ ObsBeh (.seq (spin mp) (.emit (.num 1))) s (.term [1])) ∧
    ¬ Refines ObsBeh (.seq (spin mp) (.emit (.num 1))) (.emit (.num 1))
```

**Hypothesis ledger.** The theorem has no hypotheses: it is a closed statement about concrete programs or quantifies over all its parameters unconditionally.

**Non-vacuity witness.** The statement is a concrete instance for each loop flag mp; it has no hypotheses.

The theorem itself is the witness (it has no hypotheses).

**Positive control.** Under the forward-progress semantics the same deletion is a refinement. `loopDeletion_spin_refines_forwardProgress`, `lean/Toy/Progress/Deletion.lean` line 154:

```lean
theorem loopDeletion_spin_refines_forwardProgress (mp : Bool) :
    Refines FPBeh (.seq (spin mp) (.emit (.num 1))) (.emit (.num 1))
```

**Non-claims.** Listed under **Boundaries**, `loop-deletion-unsound-divergence-observable`.

**Prior art.**

* rust-lang/rust issue #28728, 'LLVM loop optimization can make safe programs crash' (opened 2015-09-29; closed 2021-03-05 as completed with the comment 'Closed by #81451'), https://github.com/rust-lang/rust/issues/28728; rust-lang/rust pull request #81451, 'Upgrade to LLVM 12' (merged 2021-03-04, merge commit 409920873cf8a95739a55dc5fe5adb05e1b4758e).
* CompCert, AbsInt/CompCert commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v: `program_behavior` has constructors Terminates (trace and exit code), Diverges (finite trace), Reacts (infinite trace) and Goes_wrong (trace); `behavior_improves beh1 beh2` holds iff beh1 = beh2 or beh1 = Goes_wrong t for a prefix t of beh2. Prose comparison only.
* Xavier Leroy, 'A Formally Verified Compiler Back-end', Journal of Automated Reasoning 43(4):363-446, 2009, DOI 10.1007/s10817-009-9155-4 (compiler correctness stated over observable behaviours, including divergence).
* Nuno P. Lopes, Juneyoung Lee, Chung-Kil Hur, Zhengyang Liu, John Regehr, 'Alive2: Bounded Translation Validation for LLVM', PLDI 2021, pp. 65-79, DOI 10.1145/3453483.3454030.

**Design question.** When divergence is observable (the reading under which Rust's `loop {}` is defined behaviour), is deleting a silent infinite loop in front of an output a sound transformation, and does the answer depend on the loop's progress flag? This card answers with the smallest program pair, `while 1 do skip ;; emit 1` versus `emit 1`, for either flag value.

**Modelling bridge.** Basis: derived (modeling bridge). In Rust, `loop {}` is defined behaviour and silent divergence is an observable outcome, which `ObsBeh` models; `while 1 do skip ;; emit 1` stands for code that spins in `loop {}` before an observable effect. rust-lang/rust issue #28728 reported that LLVM, which then assumed forward progress for all code, could remove such loops; the issue was closed by pull request #81451 ('Upgrade to LLVM 12', merge commit 409920873cf8a95739a55dc5fe5adb05e1b4758e). The theorem is the toy counterpart of that miscompilation: the deletion is not a refinement when divergence is observable. The bridge assumes that the observable effect after the loop corresponds to `emit` and that final states are unobservable; it is an argument, not part of the kernel-checked statement.

#### 2. `loop-deletion-sound-forward-progress`

* **Theorem:** `Toy.Progress.deleteEmitFreeLoop_withDeadWrites_refines_forwardProgress`
* **Kind:** theorem; **tier:** T1; **depth:** `substantive` — uses the big-step/partial-trace theory of sequencing (`BigStep.lean`) and the deadness hypothesis at reachable states.
* Basis: execution (Lean kernel check)

**Plain claim.** Under the forward-progress semantics, for every prefix p, condition b, flag mp, loop body body and continuation k: if the body is emit-free (hEmit) and the variables it writes are dead before k in every state reachable at the end of p (hDead), then deleting `while b do body` from `p ;; while b do body ;; k` is a refinement. The theorem has no termination hypothesis: the loop may diverge from reachable states.

**Lean statement**, `lean/Toy/Progress/Deletion.lean` line 164:

```lean
theorem deleteEmitFreeLoop_withDeadWrites_refines_forwardProgress
    (p k : Cmd) (mp : Bool) (b : Exp) (body : Cmd)
    (hEmit : EmitFree body) (hDead : DeadAfterPrefix p body.writes k) :
    Refines FPBeh (.seq p (.seq (.loop mp b body) k)) (.seq p k)
```

**Hypothesis ledger.** `tight` means that the named counterexample satisfies all the other hypotheses of the theorem and the conclusion fails; the counterexample class is stated in each row.

| Hypothesis | Why it is needed | Tightness | Counterexample |
| :--- | :--- | :--- | :--- |
| `hEmit : EmitFree body` | The loop body contains no `emit`, so deleting the loop cannot drop output and a diverging execution of the loop is silent. Syntactic; a semantic 'emits nothing from reachable entry states' condition would also suffice (not proved here) but is not stated. Counterexample class: one concrete program, p = `x0 := 0`, body `emit 7 ;; x0 := 1` (one iteration, emits 7), k = skip, loop flag false; deletion drops the output 7. | tight | `deleteLoop_forwardProgress_needs_emitFree` |
| `hDead : DeadAfterPrefix p body.writes k` | In every state reachable at the end of p, changing the variables the body may assign does not change the observable behaviours of k, so a terminating loop's effect on the state is unobservable. Implied by the all-state condition DeadAtEntry body.writes k (deadAfterPrefix_of_deadAtEntry) and strictly weaker (deadAfterPrefix_example_not_deadAtEntry). Counterexample class: one concrete program, p = `x0 := 0`, emit-free body `x0 := 1`, k = `emit x0`, loop flag false; deletion changes the output from [1] to [0]. | tight | `deleteLoop_forwardProgress_needs_deadWrites` |

Counterexample for `hEmit`, `lean/Toy/Progress/Deletion.lean` line 233:

```lean
theorem deleteLoop_forwardProgress_needs_emitFree :
    DeadAfterPrefix (.assign 0 (.num 0)) emitBody.writes .skip ∧
    ¬ Refines FPBeh (.seq (.assign 0 (.num 0)) (.seq (.loop false x0IsZero emitBody) .skip))
        (.seq (.assign 0 (.num 0)) .skip)
```

Counterexample for `hDead`, `lean/Toy/Progress/Deletion.lean` line 243:

```lean
theorem deleteLoop_forwardProgress_needs_deadWrites :
    EmitFree resetBody ∧
    ¬ Refines FPBeh
        (.seq (.assign 0 (.num 0)) (.seq (.loop false x0IsZero resetBody) (.emit (.var 0))))
        (.seq (.assign 0 (.num 0)) (.emit (.var 0)))
```

**Non-vacuity witness.** With p = skip, body `x1 := x1 + 1` (emit-free, writes only x1) and continuation `emit x0` (x1 dead): the hypotheses hold, and the loop `while x0 = 0 do x1 := x1 + 1` does not terminate from the reachable all-zero state, so the theorem covers deleting a loop that can diverge.

`deleteLoop_hypotheses_nonvacuous`, `lean/Toy/Progress/Deletion.lean` line 191:

```lean
theorem deleteLoop_hypotheses_nonvacuous :
    EmitFree countBody ∧ DeadAfterPrefix .skip countBody.writes (.emit (.var 0)) ∧
    ReachableAt .skip (fun _ => 0) ∧ ¬ Terminates countLoop (fun _ => 0)
```

**Companion theorems cited by this card** (statement hashes recorded under **Evidence**):

```lean
-- lean/Toy/Progress/Deletion.lean line 63
theorem deadAfterPrefix_of_deadAtEntry (p : Cmd) {X : List Var} {k : Cmd}
    (h : DeadAtEntry X k) : DeadAfterPrefix p X k

-- lean/Toy/Progress/Deletion.lean line 76
theorem deadAfterPrefix_example_not_deadAtEntry :
    ¬ DeadAtEntry countBody.writes guardedEmit ∧ DeadAfterPrefix setX2 countBody.writes guardedEmit
```

**Non-claims.** Listed under **Boundaries**, `loop-deletion-sound-forward-progress`.

**Prior art.**

* ISO/IEC JTC1/SC22/WG21 N4861 (C++ working draft, 2020-04-01), §6.9.2.2 [intro.progress] paragraph 1: the implementation may assume that any thread will eventually terminate, call a library I/O function, perform a volatile access, or perform a synchronization or atomic operation; its note says this is intended to allow removal of empty loops even when termination cannot be proven. Rendering: https://timsong-cpp.github.io/cppwp/n4861/intro.progress.
* ISO/IEC 9899 draft N1570 (C11), §6.8.5 paragraph 6: an iteration statement whose controlling expression is not a constant expression and that performs no input/output operations, does not access volatile objects, and performs no synchronization or atomic operations in its body, controlling expression, or (for a for statement) expression-3, may be assumed by the implementation to terminate. Rendering: https://port70.net/~nsz/c/c11/n1570.html.
* JF Bastien, 'Trivial infinite loops are not Undefined Behavior', WG21 P2809R3, 2024-03-21, https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2024/p2809r3.html. Its wording is in [stmt.iter.general] of the C++ working draft, cplusplus/draft commit 604674fa5028d318770a1b689966cffeeedd4e2b, source/statements.tex lines 585-597: a trivial infinite loop is a trivially empty iteration statement (body `;` or `{}`) whose converted controlling expression is a constant expression evaluating to true; its statement is replaced by a call to std::this_thread::yield, and whether this replacement occurs on freestanding implementations is implementation-defined.
* LLVM Language Reference Manual at llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6, file llvm/docs/LangRef.md (quoted sentence at line 2981): function attribute `mustprogress` (the function is required to return, unwind, or interact with the environment in an observable way; intended to model the first section of [intro.progress]; terminating loops without side effects can be removed; 'If a mustprogress function calls a function not marked mustprogress, and that function never returns, the program is well-defined even if there isn't any other observable progress') and loop metadata `llvm.loop.mustprogress`.
* llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6: llvm/lib/Transforms/Scalar/LoopDeletion.cpp line 110 (`isLoopDead` ends with `return isLoopNestFinite(L, SE, LI);`, defined at llvm/lib/Analysis/LoopInfo.cpp line 1216: the loop must be finite by assumption (ScalarEvolution::loopIsFiniteByAssumption), or every loop of its nest must be finite by assumption or have a computable constant maximal backedge-taken count); llvm/lib/Transforms/Utils/LoopUtils.cpp lines 622-628 (`deleteDeadLoop` replaces the branch into a deleted loop that has no exit block by `unreachable`).
* Nuno P. Lopes, Juneyoung Lee, Chung-Kil Hur, Zhengyang Liu, John Regehr, 'Alive2: Bounded Translation Validation for LLVM', PLDI 2021, pp. 65-79, DOI 10.1145/3453483.3454030.

**Design question.** Under a thread-level forward-progress assumption (the reading behind C++ [intro.progress] and LLVM `mustprogress`), which side conditions suffice to delete a loop that may not terminate, so that a compiler needs no termination proof? This card answers: an emit-free body whose written variables are dead before the continuation at the loop's reachable entry states.

**Modelling bridge.** Basis: derived (modeling bridge). C++ [intro.progress] paragraph 1 (N4861 §6.9.2.2) lets an implementation assume that every thread eventually terminates, calls a library I/O function, performs a volatile access, or performs a synchronization or atomic operation. With `emit` as the only effect, a run that violates the assumption is exactly a `SilentlyDiverges` run, which `FPBeh` treats as undefined. LLVM documents its `mustprogress` attribute as modelling that paragraph (LangRef.md at the pinned commit), and its LoopDeletion pass classifies a loop as dead (`isLoopDead`, which ends with `return isLoopNestFinite(L, SE, LI);`) only if `isLoopNestFinite` holds, which is the case when the loop is finite by assumption (`loopIsFiniteByAssumption`: `isFinite(L) || (isMustProgress(L) && loopHasNoSideEffects(L))`, ScalarEvolution.cpp lines 7423-7428). The theorem is the toy counterpart: under forward progress an emit-free loop whose writes are dead at its reachable entry states may be deleted without a termination proof. Gaps: C11 §6.8.5p6 and the C++ trivial-infinite-loop rule exempt some loops, and LLVM replaces an exitless deleted loop by `unreachable` (see the non-claims).

#### 3. `loop-deletion-exact-condition-divergence-observable`

* **Theorem:** `Toy.Progress.deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff`
* **Kind:** characterization; **tier:** T1; **depth:** `substantive` — the 'only if' direction uses determinism (`refines_obsBeh_iff_equiv`) and bounds on reached traces.
* Basis: execution (Lean kernel check)

**Plain claim.** Under the divergence-observable semantics, for an emit-free loop body (hEmit) whose written variables are dead before k in every state reachable at the end of p (hDead), deleting the loop from `p ;; loop ;; k` is a refinement iff from every state reachable at the end of a terminating run of p, the loop terminates or k itself silently diverges with empty trace (`ObsBeh k s₁ (div [])`).

**Lean statement**, `lean/Toy/Progress/Deletion.lean` line 259:

```lean
theorem deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff
    (p k : Cmd) (mp : Bool) (b : Exp) (body : Cmd)
    (hEmit : EmitFree body) (hDead : DeadAfterPrefix p body.writes k) :
    Refines ObsBeh (.seq p (.seq (.loop mp b body) k)) (.seq p k) ↔
      ∀ s₁, ReachableAt p s₁ →
        Terminates (.loop mp b body) s₁ ∨ ObsBeh k s₁ (.div [])
```

**Hypothesis ledger.** `tight` means that the named counterexample satisfies all the other hypotheses of the theorem and the conclusion fails; the counterexample class is stated in each row.

| Hypothesis | Why it is needed | Tightness | Counterexample |
| :--- | :--- | :--- | :--- |
| `hEmit : EmitFree body` | The loop body contains no `emit`, so deleting the loop cannot drop output and a diverging execution of the loop is silent. Syntactic; a semantic 'emits nothing from reachable entry states' condition would also suffice (not proved here) but is not stated. Counterexample class: the same concrete program as for the forward-progress card (p = `x0 := 0`, body `emit 7 ;; x0 := 1`, k = skip); the loop terminates at every reachable entry state, yet deletion is not a refinement, so the equivalence fails. | tight | `deleteLoop_divergenceObservable_iff_needs_emitFree` |
| `hDead : DeadAfterPrefix p body.writes k` | In every state reachable at the end of p, the variables the body may assign are dead before k, so a terminating loop leaves k's behaviours unchanged. Used only in the 'if' direction. Counterexample class: one concrete program, p = `x0 := 0`, body `x0 := 1`, k = `emit x0`; the loop terminates at every reachable entry state, yet deletion is not a refinement, so the equivalence fails. | tight | `deleteLoop_divergenceObservable_iff_needs_deadWrites` |

Counterexample for `hEmit`, `lean/Toy/Progress/Deletion.lean` line 321:

```lean
theorem deleteLoop_divergenceObservable_iff_needs_emitFree :
    DeadAfterPrefix (.assign 0 (.num 0)) emitBody.writes .skip ∧
    ¬ (Refines ObsBeh (.seq (.assign 0 (.num 0)) (.seq (.loop false x0IsZero emitBody) .skip))
          (.seq (.assign 0 (.num 0)) .skip) ↔
        ∀ s₁, ReachableAt (.assign 0 (.num 0)) s₁ →
          Terminates (.loop false x0IsZero emitBody) s₁ ∨ ObsBeh .skip s₁ (.div []))
```

Counterexample for `hDead`, `lean/Toy/Progress/Deletion.lean` line 336:

```lean
theorem deleteLoop_divergenceObservable_iff_needs_deadWrites :
    EmitFree resetBody ∧
    ¬ (Refines ObsBeh
          (.seq (.assign 0 (.num 0)) (.seq (.loop false x0IsZero resetBody) (.emit (.var 0))))
          (.seq (.assign 0 (.num 0)) (.emit (.var 0))) ↔
        ∀ s₁, ReachableAt (.assign 0 (.num 0)) s₁ →
          Terminates (.loop false x0IsZero resetBody) s₁ ∨
            ObsBeh (.emit (.var 0)) s₁ (.div []))
```

**Non-vacuity witness.** With p = `x0 := 1`, body `x1 := x1 + 1` and k = `emit x0`, the hypotheses hold and both sides of the equivalence are true: the loop terminates at every reachable entry state although it does not terminate from the unreachable all-zero state, and deletion is a refinement.

`deleteLoop_iff_terminates_nonvacuous`, `lean/Toy/Progress/Deletion.lean` line 389:

```lean
theorem deleteLoop_iff_terminates_nonvacuous :
    EmitFree countBody ∧ DeadAfterPrefix (.assign 0 (.num 1)) countBody.writes (.emit (.var 0)) ∧
    (∀ s₁, ReachableAt (.assign 0 (.num 1)) s₁ → ¬ ObsBeh (.emit (.var 0)) s₁ (.div [])) ∧
    (∀ s₁, ReachableAt (.assign 0 (.num 1)) s₁ → Terminates countLoop s₁) ∧
    ¬ Terminates countLoop (fun _ => 0) ∧
    Refines ObsBeh (.seq (.assign 0 (.num 1)) (.seq countLoop (.emit (.var 0))))
      (.seq (.assign 0 (.num 1)) (.emit (.var 0)))
```

**Companion theorems cited by this card** (statement hashes recorded under **Evidence**):

```lean
-- lean/Toy/Progress/BigStep.lean line 627
theorem refines_obsBeh_iff_equiv (src tgt : Cmd) :
    Refines ObsBeh src tgt ↔ ∀ s b, ObsBeh src s b ↔ ObsBeh tgt s b

-- lean/Toy/Progress/BigStep.lean line 597
theorem obsBeh_exists (c : Cmd) (s : State) : ∃ b, ObsBeh c s b

-- lean/Toy/Progress/BigStep.lean line 557
theorem obsBeh_unique {c : Cmd} {s : State} {b₁ b₂ : Beh} (h₁ : ObsBeh c s b₁)
    (h₂ : ObsBeh c s b₂) : b₁ = b₂
```

**Non-claims.** Listed under **Boundaries**, `loop-deletion-exact-condition-divergence-observable`.

**Prior art.**

* CompCert, AbsInt/CompCert commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v: `program_behavior` has constructors Terminates (trace and exit code), Diverges (finite trace), Reacts (infinite trace) and Goes_wrong (trace); `behavior_improves beh1 beh2` holds iff beh1 = beh2 or beh1 = Goes_wrong t for a prefix t of beh2. Prose comparison only.
* Xavier Leroy, 'A Formally Verified Compiler Back-end', Journal of Automated Reasoning 43(4):363-446, 2009, DOI 10.1007/s10817-009-9155-4 (compiler correctness stated over observable behaviours, including divergence).
* rust-lang/rust issue #28728, 'LLVM loop optimization can make safe programs crash' (opened 2015-09-29; closed 2021-03-05 as completed with the comment 'Closed by #81451'), https://github.com/rust-lang/rust/issues/28728; rust-lang/rust pull request #81451, 'Upgrade to LLVM 12' (merged 2021-03-04, merge commit 409920873cf8a95739a55dc5fe5adb05e1b4758e).

**Design question.** When divergence is observable, what exactly must hold, given an emit-free body with dead writes, for loop deletion to be a refinement, i.e. what replaces the termination proof that the forward-progress semantics makes unnecessary?

**Modelling bridge.** Basis: derived (modeling bridge). For a divergence-observable language (Rust's reading of `loop {}`), the theorem states what a loop-deletion transformation must establish instead of termination: at every reachable entry state, the loop terminates or the continuation itself silently diverges with no further output. Real divergence-observable intermediate languages also have undefined behaviour unrelated to loops, under which refinement is one-way; there the 'only if' direction need not hold (not proved here; see the non-claims).

#### 4. `loop-deletion-termination-condition-not-necessary`

* **Theorem:** `Toy.Progress.deleteLoop_refines_divergenceObservable_without_termination`
* **Kind:** counterexample; **tier:** T1; **depth:** `shallow` — a concrete instance.
* Basis: execution (Lean kernel check)

**Plain claim.** Deleting the always-diverging loop `while 1 do skip` from `skip ;; while 1 do skip ;; while 1 do skip` is a divergence-observable refinement although the loop terminates from no state; the hypotheses of the exact characterization hold (the body skip is emit-free and writes nothing), so 'deletion is a refinement only if the loop terminates from every reachable entry state' is false.

**Lean statement**, `lean/Toy/Progress/Deletion.lean` line 355:

```lean
theorem deleteLoop_refines_divergenceObservable_without_termination :
    EmitFree .skip ∧ DeadAfterPrefix .skip Cmd.skip.writes (spin false) ∧
    Refines ObsBeh (.seq .skip (.seq (spin false) (spin false))) (.seq .skip (spin false)) ∧
    ∀ s₁, ReachableAt .skip s₁ ∧ ¬ Terminates (spin false) s₁
```

**Hypothesis ledger.** The theorem has no hypotheses: it is a closed statement about concrete programs or quantifies over all its parameters unconditionally.

**Non-vacuity witness.** Concrete instance; it also establishes EmitFree skip and DeadAfterPrefix skip [] (while 1 do skip).

The theorem itself is the witness (it has no hypotheses).

**Positive control.** With the continuation `emit 1` instead of a silent loop, deleting `while 1 do skip` is not a divergence-observable refinement. `loopDeletion_spin_not_refines_divergenceObservable`, `lean/Toy/Progress/Deletion.lean` line 140:

```lean
theorem loopDeletion_spin_not_refines_divergenceObservable (mp : Bool) :
    (∀ s, ObsBeh (.emit (.num 1)) s (.term [1]) ∧
          ObsBeh (.seq (spin mp) (.emit (.num 1))) s (.div []) ∧
          ¬ ObsBeh (.seq (spin mp) (.emit (.num 1))) s (.term [1])) ∧
    ¬ Refines ObsBeh (.seq (spin mp) (.emit (.num 1))) (.emit (.num 1))
```

**Non-claims.** Listed under **Boundaries**, `loop-deletion-termination-condition-not-necessary`.

**Prior art.**

* CompCert, AbsInt/CompCert commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v: `program_behavior` has constructors Terminates (trace and exit code), Diverges (finite trace), Reacts (infinite trace) and Goes_wrong (trace); `behavior_improves beh1 beh2` holds iff beh1 = beh2 or beh1 = Goes_wrong t for a prefix t of beh2. Prose comparison only.

**Design question.** Is 'the loop terminates from every reachable entry state' necessary for deletion when divergence is observable, or can a continuation that itself silently diverges make deletion of a never-terminating loop sound? Reference counterexample delimiting the exact characterization.

**Modelling bridge.** None: this card makes no claim about a real system.

#### 5. `loop-deletion-iff-terminates-under-nonsilent-continuation`

* **Theorem:** `Toy.Progress.deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff_terminates`
* **Kind:** characterization; **tier:** T1; **depth:** `shallow` — a three-line corollary of the exact characterization.
* Basis: execution (Lean kernel check)

**Plain claim.** Corollary of the exact characterization: if additionally k never has the behaviour `div []` at a state reachable at the end of p (hNoSilentK), then, for an emit-free body (hEmit) whose writes are dead before k at reachable states (hDead), deleting the loop from `p ;; loop ;; k` is a divergence-observable refinement iff the loop terminates from every state reachable at the end of p.

**Lean statement**, `lean/Toy/Progress/Deletion.lean` line 374:

```lean
theorem deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff_terminates
    (p k : Cmd) (mp : Bool) (b : Exp) (body : Cmd)
    (hEmit : EmitFree body) (hDead : DeadAfterPrefix p body.writes k)
    (hNoSilentK : ∀ s₁, ReachableAt p s₁ → ¬ ObsBeh k s₁ (.div [])) :
    Refines ObsBeh (.seq p (.seq (.loop mp b body) k)) (.seq p k) ↔
      ∀ s₁, ReachableAt p s₁ → Terminates (.loop mp b body) s₁
```

**Hypothesis ledger.** `tight` means that the named counterexample satisfies all the other hypotheses of the theorem and the conclusion fails; the counterexample class is stated in each row.

| Hypothesis | Why it is needed | Tightness | Counterexample |
| :--- | :--- | :--- | :--- |
| `hEmit : EmitFree body` | The loop body contains no `emit`, so deleting the loop cannot drop output and a diverging execution of the loop is silent. Syntactic; a semantic 'emits nothing from reachable entry states' condition would also suffice (not proved here) but is not stated. Counterexample class: one concrete program, p = `x0 := 0`, body `emit 7 ;; x0 := 1`, k = skip (which never has behaviour `div []`). | tight | `deleteLoop_iff_terminates_needs_emitFree` |
| `hDead : DeadAfterPrefix p body.writes k` | In every state reachable at the end of p, the variables the body may assign are dead before k. Counterexample class: one concrete program, p = `x0 := 0`, body `x0 := 1`, k = `emit x0` (which never has behaviour `div []`). | tight | `deleteLoop_iff_terminates_needs_deadWrites` |
| `hNoSilentK : ∀ s₁, ReachableAt p s₁ → ¬ ObsBeh k s₁ (.div [])` | Rules out a continuation whose own silent divergence masks the loop's divergence; without it the 'only if' direction fails. Counterexample class: one concrete program, p = skip, loop `while 1 do skip`, k = `while 1 do skip`; deletion is a refinement although the loop terminates from no state. | tight | `deleteLoop_iff_terminates_needs_continuation_not_silent` |

Counterexample for `hEmit`, `lean/Toy/Progress/Deletion.lean` line 433:

```lean
theorem deleteLoop_iff_terminates_needs_emitFree :
    DeadAfterPrefix (.assign 0 (.num 0)) emitBody.writes .skip ∧
    (∀ s₁, ReachableAt (.assign 0 (.num 0)) s₁ → ¬ ObsBeh .skip s₁ (.div [])) ∧
    ¬ (Refines ObsBeh (.seq (.assign 0 (.num 0)) (.seq (.loop false x0IsZero emitBody) .skip))
          (.seq (.assign 0 (.num 0)) .skip) ↔
        ∀ s₁, ReachableAt (.assign 0 (.num 0)) s₁ →
          Terminates (.loop false x0IsZero emitBody) s₁)
```

Counterexample for `hDead`, `lean/Toy/Progress/Deletion.lean` line 449:

```lean
theorem deleteLoop_iff_terminates_needs_deadWrites :
    EmitFree resetBody ∧
    (∀ s₁, ReachableAt (.assign 0 (.num 0)) s₁ → ¬ ObsBeh (.emit (.var 0)) s₁ (.div [])) ∧
    ¬ (Refines ObsBeh
          (.seq (.assign 0 (.num 0)) (.seq (.loop false x0IsZero resetBody) (.emit (.var 0))))
          (.seq (.assign 0 (.num 0)) (.emit (.var 0))) ↔
        ∀ s₁, ReachableAt (.assign 0 (.num 0)) s₁ →
          Terminates (.loop false x0IsZero resetBody) s₁)
```

Counterexample for `hNoSilentK`, `lean/Toy/Progress/Deletion.lean` line 410:

```lean
theorem deleteLoop_iff_terminates_needs_continuation_not_silent :
    EmitFree .skip ∧ DeadAfterPrefix .skip Cmd.skip.writes (spin false) ∧
    ¬ (Refines ObsBeh (.seq .skip (.seq (spin false) (spin false))) (.seq .skip (spin false)) ↔
        ∀ s₁, ReachableAt .skip s₁ → Terminates (spin false) s₁)
```

**Non-vacuity witness.** With p = `x0 := 1`, body `x1 := x1 + 1` and k = `emit x0`, all three hypotheses hold and both sides of the equivalence are true (the loop terminates at every reachable entry state but not from the unreachable all-zero state).

`deleteLoop_iff_terminates_nonvacuous`, `lean/Toy/Progress/Deletion.lean` line 389:

```lean
theorem deleteLoop_iff_terminates_nonvacuous :
    EmitFree countBody ∧ DeadAfterPrefix (.assign 0 (.num 1)) countBody.writes (.emit (.var 0)) ∧
    (∀ s₁, ReachableAt (.assign 0 (.num 1)) s₁ → ¬ ObsBeh (.emit (.var 0)) s₁ (.div [])) ∧
    (∀ s₁, ReachableAt (.assign 0 (.num 1)) s₁ → Terminates countLoop s₁) ∧
    ¬ Terminates countLoop (fun _ => 0) ∧
    Refines ObsBeh (.seq (.assign 0 (.num 1)) (.seq countLoop (.emit (.var 0))))
      (.seq (.assign 0 (.num 1)) (.emit (.var 0)))
```

**Companion theorems cited by this card** (statement hashes recorded under **Evidence**):

```lean
-- lean/Toy/Progress/Deletion.lean line 420
theorem noSilentK_admits_emit_then_spin (s : State) :
    ¬ ObsBeh (.seq (.emit (.num 1)) (spin false)) s (.div []) ∧
    SilentlyDiverges (.seq (.emit (.num 1)) (spin false)) s

-- lean/Toy/Progress/BigStep.lean line 627
theorem refines_obsBeh_iff_equiv (src tgt : Cmd) :
    Refines ObsBeh src tgt ↔ ∀ s b, ObsBeh src s b ↔ ObsBeh tgt s b
```

**Non-claims.** Listed under **Boundaries**, `loop-deletion-iff-terminates-under-nonsilent-continuation`.

**Prior art.**

* rust-lang/rust issue #28728, 'LLVM loop optimization can make safe programs crash' (opened 2015-09-29; closed 2021-03-05 as completed with the comment 'Closed by #81451'), https://github.com/rust-lang/rust/issues/28728; rust-lang/rust pull request #81451, 'Upgrade to LLVM 12' (merged 2021-03-04, merge commit 409920873cf8a95739a55dc5fe5adb05e1b4758e).
* CompCert, AbsInt/CompCert commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v: `program_behavior` has constructors Terminates (trace and exit code), Diverges (finite trace), Reacts (infinite trace) and Goes_wrong (trace); `behavior_improves beh1 beh2` holds iff beh1 = beh2 or beh1 = Goes_wrong t for a prefix t of beh2. Prose comparison only.

**Design question.** Corollary and reference point: under which extra hypothesis on the continuation does the exact divergence-observable deletion condition reduce to the familiar requirement that the loop terminate from every reachable entry state?

**Modelling bridge.** None: this card makes no claim about a real system.

#### 6. `forward-progress-admits-divergence-observable-refinements`

* **Theorem:** `Toy.Progress.refines_forwardProgress_of_refines_divergenceObservable_strict`
* **Kind:** theorem; **tier:** T0; **depth:** `shallow` — the first conjunct is a two-line unfolding of the definitions; the second reuses the loop-deletion example.
* Basis: execution (Lean kernel check)

**Plain claim.** Divergence-observable refinement is strictly stronger than forward-progress refinement: for all programs src and tgt, if tgt refines src under the divergence-observable semantics then tgt refines src under the forward-progress semantics, and there exist programs src and tgt such that tgt refines src under forward progress but not under the divergence-observable semantics.

The second conjunct is existential. A concrete witness pair is `while 1 do skip ;; emit 1` (source) and `emit 1` (target): `loopDeletion_spin_refines_forwardProgress` and `loopDeletion_spin_not_refines_divergenceObservable` prove its two parts.

**Lean statement**, `lean/Toy/Progress/Deletion.lean` line 474:

```lean
theorem refines_forwardProgress_of_refines_divergenceObservable_strict :
    (∀ src tgt, Refines ObsBeh src tgt → Refines FPBeh src tgt) ∧
    ∃ src tgt, Refines FPBeh src tgt ∧ ¬ Refines ObsBeh src tgt
```

**Hypothesis ledger.** The theorem has no hypotheses: it is a closed statement about concrete programs or quantifies over all its parameters unconditionally.

**Non-vacuity witness.** The statement has no hypotheses; its first conjunct applies, for example, to removing a dead store, which is a divergence-observable refinement.

`refines_divergenceObservable_example`, `lean/Toy/Progress/Deletion.lean` line 497:

```lean
theorem refines_divergenceObservable_example :
    Refines ObsBeh (.seq (.assign 1 (.num 5)) (.emit (.num 1))) (.emit (.num 1))
```

**Companion theorems cited by this card** (statement hashes recorded under **Evidence**):

```lean
-- lean/Toy/Progress/Deletion.lean line 466
theorem refines_forwardProgress_of_refines_divergenceObservable (src tgt : Cmd)
    (h : Refines ObsBeh src tgt) : Refines FPBeh src tgt

-- lean/Toy/Progress/Deletion.lean line 485
theorem refines_divergenceObservable_not_imp_refines_mixed :
    Refines ObsBeh (spin false) (spin true) ∧ ¬ Refines MixedBeh (spin false) (spin true)

-- lean/Toy/Progress/BigStep.lean line 627
theorem refines_obsBeh_iff_equiv (src tgt : Cmd) :
    Refines ObsBeh src tgt ↔ ∀ s b, ObsBeh src s b ↔ ObsBeh tgt s b

-- lean/Toy/Progress/Deletion.lean line 154
theorem loopDeletion_spin_refines_forwardProgress (mp : Bool) :
    Refines FPBeh (.seq (spin mp) (.emit (.num 1))) (.emit (.num 1))

-- lean/Toy/Progress/Deletion.lean line 140
theorem loopDeletion_spin_not_refines_divergenceObservable (mp : Bool) :
    (∀ s, ObsBeh (.emit (.num 1)) s (.term [1]) ∧
          ObsBeh (.seq (spin mp) (.emit (.num 1))) s (.div []) ∧
          ¬ ObsBeh (.seq (spin mp) (.emit (.num 1))) s (.term [1])) ∧
    ¬ Refines ObsBeh (.seq (spin mp) (.emit (.num 1))) (.emit (.num 1))

-- lean/Toy/Progress/Deletion.lean line 507
theorem refines_forwardProgress_needs_hypothesis : ¬ Refines FPBeh .skip (.emit (.num 1))
```

**Non-claims.** Listed under **Boundaries**, `forward-progress-admits-divergence-observable-refinements`.

**Prior art.**

* CompCert, AbsInt/CompCert commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v: `program_behavior` has constructors Terminates (trace and exit code), Diverges (finite trace), Reacts (infinite trace) and Goes_wrong (trace); `behavior_improves beh1 beh2` holds iff beh1 = beh2 or beh1 = Goes_wrong t for a prefix t of beh2. Prose comparison only.
* Ralph-Johan Back, Joakim von Wright, 'Refinement Calculus: A Systematic Introduction', Springer, 1998, DOI 10.1007/978-1-4612-1674-2.

**Design question.** Reference point: in this deterministic toy language, is every divergence-observable refinement also a forward-progress refinement, so that a transformation validated with observable divergence may also be used under forward progress, and does the forward-progress semantics admit strictly more refinements?

**Modelling bridge.** Basis: derived (modeling bridge). In the deterministic toy, a transformation that is a refinement with observable divergence remains a refinement under thread-level forward progress. Transferring this to a real compiler additionally requires determinism and the absence of other undefined behaviour (see the non-claims); the transfer into the per-loop semantics fails even in the toy (`refines_divergenceObservable_not_imp_refines_mixed`).

#### 7. `classic-slice-preserves-terminating-traces`

* **Theorem:** `Toy.Progress.classicSlice_preserves_terminating_traces`
* **Kind:** theorem; **tier:** T0; **depth:** `substantive` — forward simulation of big-step runs by slices with relevant-set agreement (`slice_bigStep_fwd`).
* Basis: execution (Lean kernel check)

**Plain claim.** For every classic slice c' of c with respect to all emit statements (hSlice), every state s and every trace t: if c terminates from s emitting t, then c' terminates from s emitting t.

**Lean statement**, `lean/Toy/Progress/Slicing.lean` line 467:

```lean
theorem classicSlice_preserves_terminating_traces (c c' : Cmd)
    (hSlice : IsClassicSlice c c') :
    ∀ s t, ObsBeh c s (.term t) → ObsBeh c' s (.term t)
```

**Hypothesis ledger.** `tight` means that the named counterexample satisfies all the other hypotheses of the theorem and the conclusion fails; the counterexample class is stated in each row.

| Hypothesis | Why it is needed | Tightness | Counterexample |
| :--- | :--- | :--- | :--- |
| `hSlice : IsClassicSlice c c'` | c' arises from c by the data- and control-dependence rules of IsSlice with termination-insensitive dropping and nothing relevant after the program. Counterexample class: one concrete pair, c = `emit 1`, c' = skip (not a classic slice), from the all-zero state. | tight | `classicSlice_preserves_terminating_traces_needs_slice` |

Counterexample for `hSlice`, `lean/Toy/Progress/Slicing.lean` line 487:

```lean
theorem classicSlice_preserves_terminating_traces_needs_slice :
    ¬ IsClassicSlice (.emit (.num 1)) .skip ∧
    ObsBeh (.emit (.num 1)) (fun _ => 0) (.term [1]) ∧
    ¬ ObsBeh .skip (fun _ => 0) (.term [1])
```

**Non-vacuity witness.** `skip ;; emit 1` is a classic slice of `while x0 = 0 do x1 := x1 + 1 ;; emit 1`, and the original terminates with [1] from a state with x0 = 1.

`classicSlice_preserves_terminating_traces_nonvacuous`, `lean/Toy/Progress/Slicing.lean` line 478:

```lean
theorem classicSlice_preserves_terminating_traces_nonvacuous :
    IsClassicSlice (.seq countLoop (.emit (.num 1))) (.seq .skip (.emit (.num 1))) ∧
    ObsBeh (.seq countLoop (.emit (.num 1))) (fun _ => 1) (.term [1])
```

**Companion theorems cited by this card** (statement hashes recorded under **Evidence**):

```lean
-- lean/Toy/Progress/Slicing.lean line 110
theorem isClassicSlice_refl (c : Cmd) : IsClassicSlice c c
```

**Non-claims.** Listed under **Boundaries**, `classic-slice-preserves-terminating-traces`.

**Prior art.**

* Mark Weiser, 'Program Slicing', IEEE Transactions on Software Engineering SE-10(4):352-357, July 1984, DOI 10.1109/TSE.1984.5010248. Its definition of a slice (p. 353) requires: 'Whenever P halts on an input I with state trajectory T, then S also halts on input I with state trajectory T'' with equal projections; a footnote says that extending the definition to inputs on which the original program does not halt 'causes many new problems', since there is no way to guarantee that a slice fails to halt whenever the original program fails to halt.
* Thomas Reps and Wuu Yang, 'The Semantics of Program Slicing', Computer Sciences Technical Report #777, University of Wisconsin-Madison, June 1988; conference version: Thomas W. Reps and Wuu Yang, 'The Semantics of Program Slicing and Program Integration', TAPSOFT '89 Vol. 2, LNCS 352:360-374, Springer, 1989, DOI 10.1007/3-540-50940-2_47. Slicing Theorem: from any initial state on which the program halts, a dependence-graph slice also halts and computes the same sequence of values at each of its program points.
* Susan Horwitz, Thomas W. Reps, David W. Binkley, 'Interprocedural Slicing Using Dependence Graphs', ACM TOPLAS 12(1):26-60, 1990, DOI 10.1145/77606.77608.
* Daniel Wasserrab, 'Towards Certified Slicing', Archive of Formal Proofs, September 16, 2008, https://www.isa-afp.org/entries/Slicing.html (Isabelle/HOL framework for dynamic and static intraprocedural slicing over control-flow and dependence graphs, instantiated to a While language and to Jinja bytecode; correctness is stated as a weak simulation of the original by the slice).
* Sandrine Blazy, André Maroneze, David Pichardie, 'Verified Validation of Program Slicing', CPP 2015, pp. 109-117, DOI 10.1145/2676724.2693169 (Coq, CompCert).
* Torben Amtoft, 'Slicing for modern program structures: a theory for eliminating irrelevant loops', Information Processing Letters 106(2):45-51, 2008, DOI 10.1016/j.ipl.2007.10.002.
* Sebastian Danicic, Richard W. Barraclough, Mark Harman, John D. Howroyd, Ákos Kiss, Michael R. Laurence, 'A unifying theory of control dependence and its application to arbitrary program structures', Theoretical Computer Science 412(49):6809-6842, 2011, DOI 10.1016/j.tcs.2011.08.033.

**Design question.** What does classic (termination-insensitive) slicing with respect to all outputs guarantee independently of how divergence is treated? Reference restatement of the Weiser and Reps-Yang guarantee for runs on which the original program terminates.

**Modelling bridge.** Basis: derived (modeling bridge). Literature comparison, not a claim about a real system: Weiser's definition of a slice (1984, p. 353) and the Slicing Theorem of Reps and Yang constrain only inputs on which the original program halts; this theorem is the toy counterpart for slicing with respect to all outputs.

#### 8. `classic-slice-may-terminate-when-original-diverges`

* **Theorem:** `Toy.Progress.classicSlice_spin_terminates_while_original_diverges`
* **Kind:** counterexample; **tier:** T0; **depth:** `shallow` — a concrete instance.
* Basis: execution (Lean kernel check)

**Plain claim.** `skip ;; emit 1` is a classic slice of `while 1 do skip ;; emit 1`; from every state the original silently diverges with empty trace while the slice terminates emitting [1], so this classic slice is not a divergence-observable refinement.

**Lean statement**, `lean/Toy/Progress/Slicing.lean` line 500:

```lean
theorem classicSlice_spin_terminates_while_original_diverges :
    IsClassicSlice (.seq (spin false) (.emit (.num 1))) (.seq .skip (.emit (.num 1))) ∧
    (∀ s, ObsBeh (.seq (spin false) (.emit (.num 1))) s (.div []) ∧
          ObsBeh (.seq .skip (.emit (.num 1))) s (.term [1])) ∧
    ¬ Refines ObsBeh (.seq (spin false) (.emit (.num 1))) (.seq .skip (.emit (.num 1)))
```

**Hypothesis ledger.** The theorem has no hypotheses: it is a closed statement about concrete programs or quantifies over all its parameters unconditionally.

**Non-vacuity witness.** Concrete instance; no hypotheses.

The theorem itself is the witness (it has no hypotheses).

**Positive control.** No termination-guarded slice drops the loop, so the same pair is excluded by the termination-guarded slice relation. `not_isTerminationSensitiveSlice_spin`, `lean/Toy/Progress/Slicing.lean` line 151:

```lean
theorem not_isTerminationSensitiveSlice_spin :
    ¬ IsTerminationSensitiveSlice (.seq (spin false) (.emit (.num 1)))
      (.seq .skip (.emit (.num 1)))
```

**Non-claims.** Listed under **Boundaries**, `classic-slice-may-terminate-when-original-diverges`.

**Prior art.**

* Mark Weiser, 'Program Slicing', IEEE Transactions on Software Engineering SE-10(4):352-357, July 1984, DOI 10.1109/TSE.1984.5010248. Its definition of a slice (p. 353) requires: 'Whenever P halts on an input I with state trajectory T, then S also halts on input I with state trajectory T'' with equal projections; a footnote says that extending the definition to inputs on which the original program does not halt 'causes many new problems', since there is no way to guarantee that a slice fails to halt whenever the original program fails to halt.
* Thomas Reps and Wuu Yang, 'The Semantics of Program Slicing', Computer Sciences Technical Report #777, University of Wisconsin-Madison, June 1988; conference version: Thomas W. Reps and Wuu Yang, 'The Semantics of Program Slicing and Program Integration', TAPSOFT '89 Vol. 2, LNCS 352:360-374, Springer, 1989, DOI 10.1007/3-540-50940-2_47. Slicing Theorem: from any initial state on which the program halts, a dependence-graph slice also halts and computes the same sequence of values at each of its program points.
* Andy Podgurski and Lori A. Clarke, 'A Formal Model of Program Dependences and Its Implications for Software Testing, Debugging, and Maintenance', IEEE TSE 16(9):965-979, 1990, DOI 10.1109/32.58784 (weak and strong control dependence).
* Venkatesh Prasad Ranganath, Torben Amtoft, Anindya Banerjee, Matthew B. Dwyer, John Hatcliff, 'A New Foundation for Control-Dependence and Slicing for Modern Program Structures', ESOP 2005, LNCS 3444:77-93, Springer, 2005, DOI 10.1007/978-3-540-31987-0_7; journal version: Venkatesh Prasad Ranganath, Torben Amtoft, Anindya Banerjee, John Hatcliff, Matthew B. Dwyer, 'A new foundation for control dependence and slicing for modern program structures', ACM TOPLAS 29(5), Article 27, 2007, DOI 10.1145/1275497.1275502. Defines non-termination-sensitive and non-termination-insensitive control dependence on control-flow graphs.
* Torben Amtoft, 'Slicing for modern program structures: a theory for eliminating irrelevant loops', Information Processing Letters 106(2):45-51, 2008, DOI 10.1016/j.ipl.2007.10.002.

**Design question.** Can a classic slice terminate and produce output from a state on which the original program silently diverges, so that classic slicing is not a divergence-observable refinement?

**Modelling bridge.** Basis: derived (modeling bridge). Literature comparison: Weiser's footnote (1984, p. 353) observes that a slice cannot be guaranteed to fail to halt whenever the original fails to halt; this card exhibits that gap and shows that it makes classic slicing unsound when divergence is observable.

#### 9. `termination-sensitive-slice-preserves-behaviours`

* **Theorem:** `Toy.Progress.terminationSensitiveSlice_preserves_obsBeh`
* **Kind:** theorem; **tier:** T1; **depth:** `substantive` — forward and backward simulation of terminating runs and finite output prefixes (`slice_bigStep_fwd`, `slice_partial_fwd`, `slice_bigStep_bwd`, `slice_partial_bwd`).
* Basis: execution (Lean kernel check)

**Plain claim.** For every termination-guarded slice c' of c with respect to all emit statements (hSlice: every dropped sub-command terminates from every state), every state s and behaviour b: c' has behaviour b from s under the divergence-observable semantics iff c does, including silent divergence and infinite traces.

**Lean statement**, `lean/Toy/Progress/Slicing.lean` line 521:

```lean
theorem terminationSensitiveSlice_preserves_obsBeh (c c' : Cmd)
    (hSlice : IsTerminationSensitiveSlice c c') :
    ∀ s b, ObsBeh c' s b ↔ ObsBeh c s b
```

**Hypothesis ledger.** `tight` means that the named counterexample satisfies all the other hypotheses of the theorem and the conclusion fails; the counterexample class is stated in each row.

| Hypothesis | Why it is needed | Tightness | Counterexample |
| :--- | :--- | :--- | :--- |
| `hSlice : IsTerminationSensitiveSlice c c'` | As for classic slices, but a sub-command may be dropped only if it terminates from every state, so a possibly diverging loop is kept together with the statements its condition depends on. Counterexample class: one concrete pair that is a classic but not a termination-guarded slice, c = `while 1 do skip ;; emit 1`, c' = `skip ;; emit 1`. | tight | `terminationSensitiveSlice_needs_terminationSensitivity` |

Counterexample for `hSlice`, `lean/Toy/Progress/Slicing.lean` line 541:

```lean
theorem terminationSensitiveSlice_needs_terminationSensitivity :
    IsClassicSlice (.seq (spin false) (.emit (.num 1))) (.seq .skip (.emit (.num 1))) ∧
    ¬ (∀ s b, ObsBeh (.seq .skip (.emit (.num 1))) s b ↔
        ObsBeh (.seq (spin false) (.emit (.num 1))) s b)
```

**Non-vacuity witness.** `while x0 = 0 do skip ;; emit 1` is a termination-guarded slice of `while x0 = 0 do x1 := x1 + 1 ;; emit 1`: the always-terminating body `x1 := x1 + 1` is dropped, while the possibly diverging loop and its condition are kept.

`terminationSensitiveSlice_preserves_obsBeh_nonvacuous`, `lean/Toy/Progress/Slicing.lean` line 534:

```lean
theorem terminationSensitiveSlice_preserves_obsBeh_nonvacuous :
    IsTerminationSensitiveSlice (.seq countLoop (.emit (.num 1)))
      (.seq (.loop false x0IsZero .skip) (.emit (.num 1)))
```

**Companion theorems cited by this card** (statement hashes recorded under **Evidence**):

```lean
-- lean/Toy/Progress/Slicing.lean line 163
theorem isTerminationSensitiveSlice_drops_terminating_loop :
    IsTerminationSensitiveSlice (.seq (.loop false x0IsZero resetBody) (.emit (.num 1)))
      (.seq .skip (.emit (.num 1)))

-- lean/Toy/Progress/Slicing.lean line 112
theorem isTerminationSensitiveSlice_refl (c : Cmd) : IsTerminationSensitiveSlice c c

-- lean/Toy/Progress/BigStep.lean line 627
theorem refines_obsBeh_iff_equiv (src tgt : Cmd) :
    Refines ObsBeh src tgt ↔ ∀ s b, ObsBeh src s b ↔ ObsBeh tgt s b
```

**Non-claims.** Listed under **Boundaries**, `termination-sensitive-slice-preserves-behaviours`.

**Prior art.**

* Andy Podgurski and Lori A. Clarke, 'A Formal Model of Program Dependences and Its Implications for Software Testing, Debugging, and Maintenance', IEEE TSE 16(9):965-979, 1990, DOI 10.1109/32.58784 (weak and strong control dependence).
* Venkatesh Prasad Ranganath, Torben Amtoft, Anindya Banerjee, Matthew B. Dwyer, John Hatcliff, 'A New Foundation for Control-Dependence and Slicing for Modern Program Structures', ESOP 2005, LNCS 3444:77-93, Springer, 2005, DOI 10.1007/978-3-540-31987-0_7; journal version: Venkatesh Prasad Ranganath, Torben Amtoft, Anindya Banerjee, John Hatcliff, Matthew B. Dwyer, 'A new foundation for control dependence and slicing for modern program structures', ACM TOPLAS 29(5), Article 27, 2007, DOI 10.1145/1275497.1275502. Defines non-termination-sensitive and non-termination-insensitive control dependence on control-flow graphs.
* Torben Amtoft, 'Slicing for modern program structures: a theory for eliminating irrelevant loops', Information Processing Letters 106(2):45-51, 2008, DOI 10.1016/j.ipl.2007.10.002.
* Sebastian Danicic, Richard W. Barraclough, Mark Harman, John D. Howroyd, Ákos Kiss, Michael R. Laurence, 'A unifying theory of control dependence and its application to arbitrary program structures', Theoretical Computer Science 412(49):6809-6842, 2011, DOI 10.1016/j.tcs.2011.08.033.
* Jean-Christophe Léchenet, Nikolai Kosmatov, Pascale Le Gall, 'Cut branches before looking for bugs: certifiably sound verification on relaxed slices', Formal Aspects of Computing 30(1):107-131, 2018, DOI 10.1007/s00165-017-0439-x (Coq).
* Daniel Wasserrab, Denis Lohner, Gregor Snelting, 'On PDG-Based Noninterference and its Modular Proof', PLAS 2009, pp. 31-44, DOI 10.1145/1554339.1554345 (Isabelle/HOL).
* Daniel Wasserrab, 'Towards Certified Slicing', Archive of Formal Proofs, September 16, 2008, https://www.isa-afp.org/entries/Slicing.html (Isabelle/HOL framework for dynamic and static intraprocedural slicing over control-flow and dependence graphs, instantiated to a While language and to Jinja bytecode; correctness is stated as a weak simulation of the original by the slice).

**Design question.** Which restriction on what a slice may drop recovers preservation of all divergence-observable behaviours, including silent divergence and infinite traces? This card answers with the semantic condition that every dropped sub-command terminate from every state.

**Modelling bridge.** Basis: derived (modeling bridge). Literature comparison: the termination premise is semantic and undecidable; it is not the control-flow-graph notion of non-termination-sensitive control dependence of Podgurski and Clarke or Ranganath et al. A slicer that keeps every loop it cannot prove terminating from every state produces slices in this relation (not proved here; no slicing algorithm is formalized).

#### 10. `classic-slice-refines-forward-progress`

* **Theorem:** `Toy.Progress.classicSlice_refines_forwardProgress`
* **Kind:** theorem; **tier:** T1; **depth:** `substantive` — if c silently diverges from s the conclusion is immediate; otherwise c either terminates or emits unboundedly from s, and the forward simulation lemmas (`slice_bigStep_fwd`, `slice_partial_fwd`) with determinism give equal divergence-observable behaviours.
* Basis: execution (Lean kernel check)

**Plain claim.** For all commands c and c', if c' is a classic slice of c with respect to all emit statements (hSlice), then c' refines c under the thread-level forward-progress semantics. Equivalently (refines_fpBeh_iff_silentlyDiverges_or_obsBeh_iff; the instance is classicSlice_silentlyDiverges_or_obsBeh_iff): from every initial state s, either c silently diverges from s (undefined behaviour under forward progress) or c' has exactly the same divergence-observable behaviours from s as c.

Explanation (no additional claim): the typical way in which c silently diverges while its classic slice c' does not is an emit-free sub-command that runs forever and is dropped by the slice, as in `classicSlice_spin_terminates_while_original_diverges`. The theorem does not depend on where the divergence happens: c may also silently diverge inside kept code, and from such a state the conclusion holds through its first disjunct alone.

**Lean statement**, `lean/Toy/Progress/Slicing.lean` line 553:

```lean
theorem classicSlice_refines_forwardProgress (c c' : Cmd)
    (hSlice : IsClassicSlice c c') : Refines FPBeh c c'
```

**Hypothesis ledger.** `tight` means that the named counterexample satisfies all the other hypotheses of the theorem and the conclusion fails; the counterexample class is stated in each row.

| Hypothesis | Why it is needed | Tightness | Counterexample |
| :--- | :--- | :--- | :--- |
| `hSlice : IsClassicSlice c c'` | c' arises from c by the IsSlice rules with termination-insensitive dropping. Counterexample class: one concrete pair, c = `x0 := 5 ;; emit x0`, c' = `skip ;; emit x0` (drops the definition of an emitted variable, so not a classic slice). | tight | `classicSlice_refines_forwardProgress_needs_slice` |

Counterexample for `hSlice`, `lean/Toy/Progress/Slicing.lean` line 601:

```lean
theorem classicSlice_refines_forwardProgress_needs_slice :
    ¬ IsClassicSlice (.seq (.assign 0 (.num 5)) (.emit (.var 0)))
      (.seq .skip (.emit (.var 0))) ∧
    ¬ Refines FPBeh (.seq (.assign 0 (.num 5)) (.emit (.var 0))) (.seq .skip (.emit (.var 0)))
```

**Non-vacuity witness.** `skip ;; emit 1` is a classic slice of `while x0 = 0 do x1 := x1 + 1 ;; emit 1`.

`classicSlice_refines_forwardProgress_nonvacuous`, `lean/Toy/Progress/Slicing.lean` line 594:

```lean
theorem classicSlice_refines_forwardProgress_nonvacuous :
    IsClassicSlice (.seq countLoop (.emit (.num 1))) (.seq .skip (.emit (.num 1)))
```

**Companion theorems cited by this card** (statement hashes recorded under **Evidence**):

```lean
-- lean/Toy/Progress/Characterizations.lean line 21
theorem refines_fpBeh_iff_silentlyDiverges_or_obsBeh_iff (src tgt : Cmd) :
    Refines FPBeh src tgt ↔
      ∀ s, SilentlyDiverges src s ∨ ∀ b, ObsBeh tgt s b ↔ ObsBeh src s b

-- lean/Toy/Progress/Characterizations.lean line 60
theorem classicSlice_silentlyDiverges_or_obsBeh_iff (c c' : Cmd)
    (hSlice : IsClassicSlice c c') :
    ∀ s, SilentlyDiverges c s ∨ ∀ b, ObsBeh c' s b ↔ ObsBeh c s b

-- lean/Toy/Progress/Slicing.lean line 279
theorem slice_partial_fwd {ts : Bool} {c : Cmd} {s : State} {t : List Val}
    (hP : Partial c s t) :
    ∀ {R R' : VarSet} {c' : Cmd} {s' : State}, IsSlice ts R c c' R' → AgreeOn R' s s' →
      Partial c' s' t
```

`BigStep`, `Partial` and `AgreeOn` are quoted under **Definitions**; the equivalence
`reach_iff_partial : Reach c s t ↔ Partial c s t`, which connects `Partial` to the small-step output `traceAt`, is
quoted there under *Supporting lemmas cited by name*.

**Non-claims.** Listed under **Boundaries**, `classic-slice-refines-forward-progress`.

**Prior art.**

* ISO/IEC JTC1/SC22/WG21 N4861 (C++ working draft, 2020-04-01), §6.9.2.2 [intro.progress] paragraph 1: the implementation may assume that any thread will eventually terminate, call a library I/O function, perform a volatile access, or perform a synchronization or atomic operation; its note says this is intended to allow removal of empty loops even when termination cannot be proven. Rendering: https://timsong-cpp.github.io/cppwp/n4861/intro.progress.
* Mark Weiser, 'Program Slicing', IEEE Transactions on Software Engineering SE-10(4):352-357, July 1984, DOI 10.1109/TSE.1984.5010248. Its definition of a slice (p. 353) requires: 'Whenever P halts on an input I with state trajectory T, then S also halts on input I with state trajectory T'' with equal projections; a footnote says that extending the definition to inputs on which the original program does not halt 'causes many new problems', since there is no way to guarantee that a slice fails to halt whenever the original program fails to halt.
* Thomas Reps and Wuu Yang, 'The Semantics of Program Slicing', Computer Sciences Technical Report #777, University of Wisconsin-Madison, June 1988; conference version: Thomas W. Reps and Wuu Yang, 'The Semantics of Program Slicing and Program Integration', TAPSOFT '89 Vol. 2, LNCS 352:360-374, Springer, 1989, DOI 10.1007/3-540-50940-2_47. Slicing Theorem: from any initial state on which the program halts, a dependence-graph slice also halts and computes the same sequence of values at each of its program points.
* Torben Amtoft, 'Slicing for modern program structures: a theory for eliminating irrelevant loops', Information Processing Letters 106(2):45-51, 2008, DOI 10.1016/j.ipl.2007.10.002.

**Design question.** Is classic slicing, which may delete emit-free code that does not terminate, a refinement under the thread-level forward-progress semantics?

**Modelling bridge.** Basis: derived (modeling bridge). Under a C++-style thread-level forward-progress assumption with the outputs as the only effects, slicing with respect to all outputs may delete emit-free code that does not terminate. Gaps: the C11 and C++ trivial-infinite-loop exemptions are not modelled (see the non-claims).

#### 11. `per-loop-semantics-restricts-to-both-global-semantics`

* **Theorem:** `Toy.Progress.mixedBeh_markAll_restricts`
* **Kind:** theorem; **tier:** T1; **depth:** `substantive` — the `markAll true` direction needs `exists_head_silentlyIterates` (every silent divergence enters a loop that silently iterates); the `markAll false` half is near-definitional.
* Basis: execution (Lean kernel check)

**Plain claim.** For every command c, state s and behaviour b: the per-loop semantics of c with every loop flagged (c.markAll true) admits b from s iff the thread-level forward-progress semantics of c does, and the per-loop semantics of c with no loop flagged (c.markAll false) admits b from s iff the divergence-observable semantics of c does.

**Lean statement**, `lean/Toy/Progress/Mixing.lean` line 200:

```lean
theorem mixedBeh_markAll_restricts (c : Cmd) (s : State) (b : Beh) :
    (MixedBeh (c.markAll true) s b ↔ FPBeh c s b) ∧
    (MixedBeh (c.markAll false) s b ↔ ObsBeh c s b)
```

**Hypothesis ledger.** The theorem has no hypotheses: it is a closed statement about concrete programs or quantifies over all its parameters unconditionally.

**Non-vacuity witness.** On `skip ;; while 1 do skip ;; emit 1` with every loop flagged, both sides admit `term [42]`; with no loop flagged, neither side admits it.

`mixedBeh_markAll_nonvacuous`, `lean/Toy/Progress/Mixing.lean` line 209:

```lean
theorem mixedBeh_markAll_nonvacuous (s : State) :
    (MixedBeh ((Cmd.seq .skip (.seq (spin false) (.emit (.num 1)))).markAll true) s
        (.term [42]) ∧
      FPBeh (.seq .skip (.seq (spin false) (.emit (.num 1)))) s (.term [42])) ∧
    (¬ MixedBeh ((Cmd.seq .skip (.seq (spin true) (.emit (.num 1)))).markAll false) s
        (.term [42]) ∧
      ¬ ObsBeh (.seq .skip (.seq (spin true) (.emit (.num 1)))) s (.term [42]))
```

**Companion theorems cited by this card** (statement hashes recorded under **Evidence**):

```lean
-- lean/Toy/Progress/Mixing.lean line 170
theorem mixedBeh_markAll_true_iff_fpBeh (c : Cmd) (s : State) (b : Beh) :
    MixedBeh (c.markAll true) s b ↔ FPBeh c s b

-- lean/Toy/Progress/Mixing.lean line 191
theorem mixedBeh_markAll_false_iff_obsBeh (c : Cmd) (s : State) (b : Beh) :
    MixedBeh (c.markAll false) s b ↔ ObsBeh c s b

-- lean/Toy/Progress/Mixing.lean line 163
theorem fpBeh_of_mixedBeh {c : Cmd} {s : State} {b : Beh} (h : MixedBeh c s b) : FPBeh c s b

-- lean/Toy/Progress/Examples.lean line 213
theorem not_progressViolation_flaggedOverUnflagged {s : State} (h0 : s 0 = 0) :
    ¬ ProgressViolation flaggedOverUnflagged s

-- lean/Toy/Progress/Examples.lean line 233
theorem mixedBeh_flaggedOverUnflagged {s : State} (h0 : s 0 = 0) (b : Beh) :
    MixedBeh flaggedOverUnflagged s b ↔ b = .div []

-- lean/Toy/Progress/Examples.lean line 256
theorem progressViolation_unflaggedOverFlagged {s : State} (h0 : s 0 = 0) :
    ProgressViolation unflaggedOverFlagged s

-- lean/Toy/Progress/Iteration.lean line 165
theorem exists_head_silentlyIterates : ∀ (c : Cmd) (s : State), SilentlyDiverges c s →
    ∃ n mp b body, (run n c s).1.head = .loop mp b body ∧
      SilentlyIterates b body (run n c s).2.1

-- lean/Toy/Progress/Iteration.lean line 108
theorem silentlyDiverges_of_progressViolation {c : Cmd} {s : State}
    (h : ProgressViolation c s) : SilentlyDiverges c s
```

**Non-claims.** Listed under **Boundaries**, `per-loop-semantics-restricts-to-both-global-semantics`.

**Prior art.**

* ISO/IEC JTC1/SC22/WG21 N4861 (C++ working draft, 2020-04-01), §6.9.2.2 [intro.progress] paragraph 1: the implementation may assume that any thread will eventually terminate, call a library I/O function, perform a volatile access, or perform a synchronization or atomic operation; its note says this is intended to allow removal of empty loops even when termination cannot be proven. Rendering: https://timsong-cpp.github.io/cppwp/n4861/intro.progress.
* LLVM Language Reference Manual at llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6, file llvm/docs/LangRef.md (quoted sentence at line 2981): function attribute `mustprogress` (the function is required to return, unwind, or interact with the environment in an observable way; intended to model the first section of [intro.progress]; terminating loops without side effects can be removed; 'If a mustprogress function calls a function not marked mustprogress, and that function never returns, the program is well-defined even if there isn't any other observable progress') and loop metadata `llvm.loop.mustprogress`.
* llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6: llvm/include/llvm/IR/Attributes.td line 515 `def : MergeRule<"setAND<MustProgressAttr>">;`; llvm/lib/IR/Attributes.cpp lines 2680-2684 (`setAND` removes the attribute from the caller when the callee lacks it), applied by AttributeFuncs::mergeAttributesForInlining, which llvm/lib/Transforms/Utils/InlineFunction.cpp calls at lines 3399 and 3567; llvm/lib/Analysis/LoopInfo.cpp lines 1249-1250 (`isMustProgress(L)` holds if the enclosing function is mustprogress or the loop carries llvm.loop.mustprogress).

**Design question.** Is the per-loop flag semantics used to model mixing the two progress regimes a conservative common generalization, i.e. does it coincide with the forward-progress semantics when every loop is flagged and with the divergence-observable semantics when no loop is flagged?

**Modelling bridge.** Basis: derived (modeling bridge). LLVM decides per loop whether progress may be assumed: `isMustProgress(L)` holds if the enclosing function carries `mustprogress` or the loop carries `llvm.loop.mustprogress` (LoopInfo.cpp lines 1249-1250 at the pinned commit). The toy per-loop flag models that per-loop decision; `markAll true` corresponds to a function compiled entirely with the attribute and `markAll false` to one compiled without it. Difference: LLVM's metadata on an outer loop covers every cycle nested inside it (`isLoopNestFinite`), whereas `SilentlyIterates` blames only the innermost loop that fails to make progress.

#### 12. `unmarked-inlining-of-divergence-observable-callee-miscompiles`

* **Theorem:** `Toy.Progress.inlineUnmarked_divergenceObservableCallee_not_refines`
* **Kind:** counterexample; **tier:** T1; **depth:** `shallow` — a concrete instance.
* Basis: execution (Lean kernel check)

**Plain claim.** For the forward-progress call site `skip ;; call g ;; emit 1` (hazardSite) and the divergence-observable callee g whose body is `while 1 do skip` (spinFn), the linked program has no progress violation from any state, inlining g so that the caller's attribute flags the inlined loop yields a progress violation from every state and is not a per-loop refinement, and replacing the now-flagged loop by skip (giving `skip ;; skip ;; emit 1`) refines the inlined program but not the linked one.

**Lean statement**, `lean/Toy/Progress/Mixing.lean` line 235:

```lean
theorem inlineUnmarked_divergenceObservableCallee_not_refines :
    (∀ s, ¬ ProgressViolation (hazardSite.linked spinFn) s ∧
          ProgressViolation (hazardSite.inlineUnmarked spinFn) s) ∧
    ¬ Refines MixedBeh (hazardSite.linked spinFn) (hazardSite.inlineUnmarked spinFn) ∧
    Refines MixedBeh (hazardSite.inlineUnmarked spinFn) (.seq .skip (.seq .skip (.emit (.num 1)))) ∧
    ¬ Refines MixedBeh (hazardSite.linked spinFn) (.seq .skip (.seq .skip (.emit (.num 1))))
```

**Hypothesis ledger.** The theorem has no hypotheses: it is a closed statement about concrete programs or quantifies over all its parameters unconditionally.

**Non-vacuity witness.** Concrete instance (hazardSite, spinFn); no hypotheses.

The theorem itself is the witness (it has no hypotheses).

**Positive control.** Attribute-dropping inlining of the same call site introduces no progress violation and is a per-loop refinement of the linked program. `inlineDroppingAttr_hazard_defined`, `lean/Toy/Progress/Mixing.lean` line 259:

```lean
theorem inlineDroppingAttr_hazard_defined :
    (∀ s, ¬ ProgressViolation (hazardSite.inlineDroppingAttr spinFn) s) ∧
    Refines MixedBeh (hazardSite.linked spinFn) (hazardSite.inlineDroppingAttr spinFn)
```

**Non-claims.** Listed under **Boundaries**, `unmarked-inlining-of-divergence-observable-callee-miscompiles`.

**Prior art.**

* LLVM Language Reference Manual at llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6, file llvm/docs/LangRef.md (quoted sentence at line 2981): function attribute `mustprogress` (the function is required to return, unwind, or interact with the environment in an observable way; intended to model the first section of [intro.progress]; terminating loops without side effects can be removed; 'If a mustprogress function calls a function not marked mustprogress, and that function never returns, the program is well-defined even if there isn't any other observable progress') and loop metadata `llvm.loop.mustprogress`.
* llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6: llvm/include/llvm/IR/Attributes.td line 515 `def : MergeRule<"setAND<MustProgressAttr>">;`; llvm/lib/IR/Attributes.cpp lines 2680-2684 (`setAND` removes the attribute from the caller when the callee lacks it), applied by AttributeFuncs::mergeAttributesForInlining, which llvm/lib/Transforms/Utils/InlineFunction.cpp calls at lines 3399 and 3567; llvm/lib/Analysis/LoopInfo.cpp lines 1249-1250 (`isMustProgress(L)` holds if the enclosing function is mustprogress or the loop carries llvm.loop.mustprogress).
* llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6: llvm/lib/Transforms/Scalar/LoopDeletion.cpp line 110 (`isLoopDead` ends with `return isLoopNestFinite(L, SE, LI);`, defined at llvm/lib/Analysis/LoopInfo.cpp line 1216: the loop must be finite by assumption (ScalarEvolution::loopIsFiniteByAssumption), or every loop of its nest must be finite by assumption or have a computable constant maximal backedge-taken count); llvm/lib/Transforms/Utils/LoopUtils.cpp lines 622-628 (`deleteDeadLoop` replaces the branch into a deleted loop that has no exit block by `unreachable`).
* rust-lang/rust issue #28728, 'LLVM loop optimization can make safe programs crash' (opened 2015-09-29; closed 2021-03-05 as completed with the comment 'Closed by #81451'), https://github.com/rust-lang/rust/issues/28728; rust-lang/rust pull request #81451, 'Upgrade to LLVM 12' (merged 2021-03-04, merge commit 409920873cf8a95739a55dc5fe5adb05e1b4758e).
* Nuno P. Lopes, Juneyoung Lee, Chung-Kil Hur, Zhengyang Liu, John Regehr, 'Alive2: Bounded Translation Validation for LLVM', PLDI 2021, pp. 65-79, DOI 10.1145/3453483.3454030.

**Design question.** What goes wrong if an inliner lets the forward-progress attribute of the caller govern the loops of an inlined divergence-observable callee, and how does a subsequent loop deletion turn that into a miscompilation?

**Modelling bridge.** Basis: derived (modeling bridge). If an inliner let the `mustprogress` attribute of a caller govern the loops of an inlined callee that lacks the attribute, the callee's infinite loop would become deletable. At the pinned LLVM commit the inliner instead merges the attribute with `setAND` (Attributes.td line 515; Attributes.cpp lines 2680-2684; called via `AttributeFuncs::mergeAttributesForInlining` from InlineFunction.cpp lines 3399 and 3567), which corresponds to `inlineDroppingAttr`. The theorem exhibits the hazard that this merge rule avoids; it does not claim that any compiler performs unmarked inlining.

#### 13. `attribute-dropping-inlining-refines`

* **Theorem:** `Toy.Progress.inlineDroppingAttr_refines_linked`
* **Kind:** theorem; **tier:** T1; **depth:** `shallow` — a case split on the two attributes; when both are set the inlined program equals the linked one, otherwise no loop of the inlined program is flagged.
* Basis: execution (Lean kernel check)

**Plain claim.** For every top-level call site `pre ;; call g ;; post` with caller attribute cm and every callee g with attribute gm, inlining g and giving every loop of the merged body the attribute cm && gm refines the linked program under the per-loop semantics.

**Lean statement**, `lean/Toy/Progress/Mixing.lean` line 278:

```lean
theorem inlineDroppingAttr_refines_linked (cs : CallSite) (g : Fn) :
    Refines MixedBeh (cs.linked g) (cs.inlineDroppingAttr g)
```

**Hypothesis ledger.** The theorem has no hypotheses: it is a closed statement about concrete programs or quantifies over all its parameters unconditionally.

**Non-vacuity witness.** For the caller `while 1 do skip ;; call g ;; emit 1` (forward-progress caller) and g = spinFn, attribute-dropping inlining unflags the caller's own loop: the linked program has a progress violation from every state, the inlined one has none, and the refinement holds.

`inlineDroppingAttr_callerLoop_nonvacuous`, `lean/Toy/Progress/Mixing.lean` line 292:

```lean
theorem inlineDroppingAttr_callerLoop_nonvacuous :
    callerLoopSite.inlineDroppingAttr spinFn ≠ callerLoopSite.linked spinFn ∧
    (∀ s, ProgressViolation (callerLoopSite.linked spinFn) s) ∧
    (∀ s, ¬ ProgressViolation (callerLoopSite.inlineDroppingAttr spinFn) s) ∧
    Refines MixedBeh (callerLoopSite.linked spinFn) (callerLoopSite.inlineDroppingAttr spinFn)
```

**Non-claims.** Listed under **Boundaries**, `attribute-dropping-inlining-refines`.

**Prior art.**

* LLVM Language Reference Manual at llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6, file llvm/docs/LangRef.md (quoted sentence at line 2981): function attribute `mustprogress` (the function is required to return, unwind, or interact with the environment in an observable way; intended to model the first section of [intro.progress]; terminating loops without side effects can be removed; 'If a mustprogress function calls a function not marked mustprogress, and that function never returns, the program is well-defined even if there isn't any other observable progress') and loop metadata `llvm.loop.mustprogress`.
* llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6: llvm/include/llvm/IR/Attributes.td line 515 `def : MergeRule<"setAND<MustProgressAttr>">;`; llvm/lib/IR/Attributes.cpp lines 2680-2684 (`setAND` removes the attribute from the caller when the callee lacks it), applied by AttributeFuncs::mergeAttributesForInlining, which llvm/lib/Transforms/Utils/InlineFunction.cpp calls at lines 3399 and 3567; llvm/lib/Analysis/LoopInfo.cpp lines 1249-1250 (`isMustProgress(L)` holds if the enclosing function is mustprogress or the loop carries llvm.loop.mustprogress).

**Design question.** Which flag assignment for the merged body makes inlining across the two progress regimes a per-loop refinement for every top-level call site, and what does it cost the caller's own loops?

**Modelling bridge.** Basis: derived (modeling bridge). LLVM's `setAND` merge rule corresponds to `inlineDroppingAttr`: after inlining a callee without `mustprogress`, the caller loses the function attribute, so none of its loops is treated as must-progress unless the loop carries `llvm.loop.mustprogress` metadata. The theorem says that this flag assignment is a per-loop refinement for every top-level call site. Loop metadata is not modelled; see the non-claims for caller loops that enclose a call.

## Boundaries

### Non-claims

What each result does **not** show. These are part of each result's meaning.

#### 1. Non-claims of `loop-deletion-unsound-divergence-observable`

* Says nothing about forward-progress semantics; there the same deletion is a refinement (loopDeletion_spin_refines_forwardProgress).
* Concerns one concrete program pair; it does not say that every deletion of a possibly diverging loop is unsound (deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff).
* Escape hatches: under the divergence-observable semantics, deleting an emit-free loop with dead writes from `p ;; loop ;; k` is a refinement whenever, at every state reachable at the end of p, the loop terminates (for example because it is never entered or its condition is false there) or k itself has the behaviour `div []` (deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff).
* The loop `while 1 do skip` is exactly a loop that C11 (constant controlling expression) and the current C++ working draft (trivial infinite loop) do not let an implementation assume to terminate; the toy uses it only as the simplest silent loop.
* The setting is a toy deterministic While language over natural-number variables whose only observable effect is `emit`; final states are not observable. It has no pointers, memory, volatile accesses, atomics, threads, recursion or function calls (calls appear only through the `CallSite` construction).
* That this models rustc's `loop {}` and the historical miscompilation is a modelling-bridge argument, not part of the kernel-checked statement.

#### 2. Non-claims of `loop-deletion-sound-forward-progress`

* Forward progress here is the thread-level reading: any run that never terminates and eventually stops emitting is undefined behaviour.
* C11 §6.8.5p6 and C++26 (WG21 P2809R3) differ in which loops they exempt from termination assumptions: C11 exempts every loop whose controlling expression is a constant expression regardless of its body (so `while (1) { x1 = x1 + 1; }` may not be assumed to terminate in C11), whereas the C++ working draft exempts only trivial infinite loops, whose body is `;` or `{}` and whose controlling expression is a constant expression evaluating to true (so `while (true) { x1 = x1 + 1; }` may still be assumed to terminate). `FPBeh` models neither exemption.
* Undefined behaviour admits every behaviour, including behaviours that contradict output already produced (C++-style). The deletion `p ;; loop ;; k` to `p ;; k` nevertheless reproduces every output prefix emitted by p, so it does not depend on contradicting earlier output; transformations that hoist a trap or a contradictory output above p rely on retroactive undefined behaviour and are not sound under CompCert-style undefined behaviour that only admits extensions of the trace produced so far (not proved here).
* Deletion here replaces `p ;; loop ;; k` by `p ;; k`, falling through to k. In LLVM, deleting a dead loop that has no exit block replaces the branch into it by `unreachable` (LoopUtils.cpp `deleteDeadLoop`), which additionally licenses removing k; that stronger transformation is not modelled.
* Deletion is formalized only for a loop in top-level sequence position `p ;; loop ;; k`; loops nested inside other loops or conditionals are not covered.
* EmitFree is syntactic and DeadAfterPrefix is semantic; neither a liveness analysis nor an effect analysis that would establish them is formalized.
* Does not say the deletion is a refinement under the divergence-observable semantics (loopDeletion_spin_not_refines_divergenceObservable). Nor does it say that deleting a flagged loop `.loop true b body` with `EmitFree body` and `DeadAfterPrefix` is a refinement under the per-loop semantics `MixedBeh`: when `body` silently diverges inside a nested unflagged loop, the enclosing flagged loop has no progress violation. For example, `flaggedOverUnflagged` (`.loop true x0IsZero (.seq (spin false) (.assign 0 (.num 1)))`, whose body is emit-free), run from a state with `x0 = 0`, has no progress violation (not_progressViolation_flaggedOverUnflagged) and has exactly the per-loop behaviour `div []` (mixedBeh_flaggedOverUnflagged); that deleting such a loop is therefore not a `MixedBeh` refinement is not stated as a separate theorem (not proved here).
* Refinement compares behaviours from every initial state separately; it says nothing about programs run from a restricted set of initial states.
* The setting is a toy deterministic While language over natural-number variables whose only observable effect is `emit`; final states are not observable. It has no pointers, memory, volatile accesses, atomics, threads, recursion or function calls (calls appear only through the `CallSite` construction).

#### 3. Non-claims of `loop-deletion-exact-condition-divergence-observable`

* The condition is not 'the loop terminates from every reachable entry state': that condition is sufficient but not necessary (deleteLoop_refines_divergenceObservable_without_termination); it becomes necessary when k never has the behaviour `div []` at reachable entry states (deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff_terminates).
* `hEmit : EmitFree body` (syntactic) and `hDead : DeadAfterPrefix p body.writes k` (semantic, over all states reachable at the end of p) are fixed sufficient hypotheses outside the equivalence, not necessary conditions for deletion to be a refinement: deleting a loop whose body contains an `emit` that is never executed from reachable entry states, or whose writes are read by k only in ways that cannot change k's behaviour along the loop's actual runs, can still be a refinement under `ObsBeh` (not proved here).
* Because the language is deterministic and `ObsBeh` has no undefined-behaviour case, `Refines ObsBeh src tgt` is symmetric and coincides with behavioural equivalence `∀ s b, ObsBeh src s b ↔ ObsBeh tgt s b` (refines_obsBeh_iff_equiv). In divergence-observable intermediate languages that also have non-loop undefined behaviour (such as Rust MIR or CompCert's languages with Goes_wrong), refinement is one-way, and a loop that triggers undefined behaviour from every reachable non-terminating entry state can be deleted although it neither terminates nor is followed by a silently diverging continuation (not proved here); this is not modelled.
* Reachability is relative to the prefix p only; the condition is not decidable in general and no analysis that establishes it is formalized.
* Deletion is formalized only for a loop in top-level sequence position `p ;; loop ;; k`.
* The setting is a toy deterministic While language over natural-number variables whose only observable effect is `emit`; final states are not observable. It has no pointers, memory, volatile accesses, atomics, threads, recursion or function calls (calls appear only through the `CallSite` construction).

#### 4. Non-claims of `loop-deletion-termination-condition-not-necessary`

* Escape hatch restoring necessity of termination: adding the hypothesis that k never has the behaviour `div []` at any state reachable at the end of p makes reachable loop termination both necessary and sufficient (deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff_terminates).
* Does not say that deleting diverging loops is generally sound when divergence is observable; the continuation here is itself a silent infinite loop. With the continuation `emit 1` the deletion fails (loopDeletion_spin_not_refines_divergenceObservable).
* The setting is a toy deterministic While language over natural-number variables whose only observable effect is `emit`; final states are not observable. It has no pointers, memory, volatile accesses, atomics, threads, recursion or function calls (calls appear only through the `CallSite` construction).

#### 5. Non-claims of `loop-deletion-iff-terminates-under-nonsilent-continuation`

* A reference corollary of deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff (three-line proof); it adds no independent semantic content.
* hNoSilentK excludes only the behaviour `div []` (silent divergence without any output after p); a continuation that emits and then silently diverges, such as `emit 1 ;; while 1 do skip`, satisfies hNoSilentK (noSilentK_admits_emit_then_spin).
* `hEmit : EmitFree body` (syntactic) and `hDead : DeadAfterPrefix p body.writes k` (semantic, over all states reachable at the end of p) are fixed sufficient hypotheses outside the equivalence, not necessary conditions for deletion to be a refinement: deleting a loop whose body contains an `emit` that is never executed from reachable entry states, or whose writes are read by k only in ways that cannot change k's behaviour along the loop's actual runs, can still be a refinement under `ObsBeh` (not proved here).
* Because the language is deterministic and `ObsBeh` has no undefined-behaviour case, `Refines ObsBeh src tgt` is symmetric and coincides with behavioural equivalence `∀ s b, ObsBeh src s b ↔ ObsBeh tgt s b` (refines_obsBeh_iff_equiv). In divergence-observable intermediate languages that also have non-loop undefined behaviour (such as Rust MIR or CompCert's languages with Goes_wrong), refinement is one-way, and a loop that triggers undefined behaviour from every reachable non-terminating entry state can be deleted although it neither terminates nor is followed by a silently diverging continuation (not proved here); this is not modelled.
* The setting is a toy deterministic While language over natural-number variables whose only observable effect is `emit`; final states are not observable. It has no pointers, memory, volatile accesses, atomics, threads, recursion or function calls (calls appear only through the `CallSite` construction).

#### 6. Non-claims of `forward-progress-admits-divergence-observable-refinements`

* The second conjunct is purely existential and names no programs. A concrete pair with this property is src = `while 1 do skip ;; emit 1` and tgt = `emit 1` (deleting the loop), by loopDeletion_spin_refines_forwardProgress and loopDeletion_spin_not_refines_divergenceObservable. A reference point combining monotonicity of the forward-progress completion with the loop-deletion example; the first conjunct is a two-line unfolding of the definitions. The premise `Refines ObsBeh src tgt` of the first conjunct cannot be dropped: adding an output is not a forward-progress refinement (refines_forwardProgress_needs_hypothesis).
* The analogous transfer into the per-loop semantics `MixedBeh` is false: because `ObsBeh` ignores loop flags, `Refines ObsBeh (spin false) (spin true)` holds while `Refines MixedBeh (spin false) (spin true)` fails (refines_divergenceObservable_not_imp_refines_mixed).
* Relies on `FPBeh` being determined by `ObsBeh` and on determinism (under which `Refines ObsBeh` is behavioural equivalence, refines_obsBeh_iff_equiv). In a language with internal nondeterminism, refining a choice between `term [1]` and `div []` to `div []` is a divergence-observable refinement that turns a possibly progressing program into one that always silently diverges; the statement says nothing about that setting (not proved here).
* The setting is a toy deterministic While language over natural-number variables whose only observable effect is `emit`; final states are not observable. It has no pointers, memory, volatile accesses, atomics, threads, recursion or function calls (calls appear only through the `CallSite` construction).

#### 7. Non-claims of `classic-slice-preserves-terminating-traces`

* Says nothing about runs of c that do not terminate; the slice may terminate when c diverges (classicSlice_spin_terminates_while_original_diverges).
* The slicing criterion is the set of all emit statements; slicing with respect to a proper subset of the outputs (trace projection) is not formalized.
* Intraprocedural only; the interprocedural slicing of Horwitz, Reps and Binkley is not modelled.
* `IsSlice` is a declarative relation, not an algorithm: every command is a slice of itself (isClassicSlice_refl), and the statement says nothing about how slices are computed or about minimality.
* The setting is a toy deterministic While language over natural-number variables whose only observable effect is `emit`; final states are not observable. It has no pointers, memory, volatile accesses, atomics, threads, recursion or function calls (calls appear only through the `CallSite` construction).

#### 8. Non-claims of `classic-slice-may-terminate-when-original-diverges`

* Does not say classic slicing is unsound under forward progress; it is a refinement there (classicSlice_refines_forwardProgress).
* No termination-sensitive slice drops this loop (not_isTerminationSensitiveSlice_spin); the example says nothing against termination-sensitive slicing.
* Escape hatches: classic slicing preserves behaviour on every initial state from which the original program terminates (classicSlice_preserves_terminating_traces), is a refinement across all states under thread-level forward progress (classicSlice_refines_forwardProgress), and preserves all divergence-observable behaviours when every dropped sub-command terminates from every state (terminationSensitiveSlice_preserves_obsBeh).
* The setting is a toy deterministic While language over natural-number variables whose only observable effect is `emit`; final states are not observable. It has no pointers, memory, volatile accesses, atomics, threads, recursion or function calls (calls appear only through the `CallSite` construction).

#### 9. Non-claims of `termination-sensitive-slice-preserves-behaviours`

* The drop rule of IsTerminationSensitiveSlice requires semantic termination from every state (`∀ s, Terminates c s`), an undecidable premise; the relation is a semantic termination-guarded slicing relation, not the computable control-flow-graph notion of non-termination-sensitive control dependence of Podgurski & Clarke and Ranganath et al. It differs from that notion: it may drop `while x0 = 0 do x0 := 1` before `emit 1` (isTerminationSensitiveSlice_drops_terminating_loop), whereas in a control-flow graph that loop's back edge yields an infinite path avoiding `emit 1`, so that analysis makes `emit 1` control dependent on the loop condition and keeps the loop (not proved here).
* Because execution is deterministic and `ObsBeh` has no undefined-behaviour case, the conclusion `∀ s b, ObsBeh c' s b ↔ ObsBeh c s b` has the same strength as `Refines ObsBeh c c'` (refines_obsBeh_iff_equiv).
* Termination evidence is required from every state, not only from states reachable at the dropped sub-command.
* `IsSlice` is a declarative relation (every command is a slice of itself); no slicing algorithm or minimality is formalized; the criterion is the set of all emit statements.
* The setting is a toy deterministic While language over natural-number variables whose only observable effect is `emit`; final states are not observable. It has no pointers, memory, volatile accesses, atomics, threads, recursion or function calls (calls appear only through the `CallSite` construction).

#### 10. Non-claims of `classic-slice-refines-forward-progress`

* Does not say where the silent divergence of c occurs: it may be inside a sub-command that the slice dropped or inside kept code (in which case c' silently diverges too). The theorem only splits each initial state into 'c silently diverges' and 'c' and c have the same divergence-observable behaviours'.
* Fails under the divergence-observable semantics (classicSlice_spin_terminates_while_original_diverges).
* C11 §6.8.5p6 and C++26 (WG21 P2809R3) differ in which loops they exempt from termination assumptions: C11 exempts every loop whose controlling expression is a constant expression regardless of its body (so `while (1) { x1 = x1 + 1; }` may not be dropped by classic slicing under C11 rules), whereas the C++ working draft exempts only trivial infinite loops, whose body is `;` or `{}` and whose controlling expression is a constant expression evaluating to true (so `while (true) { x1 = x1 + 1; }` may still be assumed to terminate). `FPBeh` models neither exemption.
* Although `FPBeh` models undefined behaviour retroactively, for every classic slice c' of c and every state s, every finite output prefix emitted by c from s is also emitted by c' from s: writing `Reach c s t` for `∃ n, traceAt n c s = t`, `Reach c s t → Reach c' s t` follows from slice_partial_fwd (applied with equal initial states, which agree on every variable) together with the adequacy equivalence reach_iff_partial : Reach c s t ↔ Partial c s t. This implication is established inside the proof of classicSlice_refines_forwardProgress (`lean/Toy/Progress/Slicing.lean` lines 561-562) and is not a separately named theorem. So the theorem does not rely on contradicting output already emitted.
* `IsSlice` is a declarative relation; no slicing algorithm is formalized; the criterion is the set of all emit statements; intraprocedural only.
* Not claimed novel.
* The setting is a toy deterministic While language over natural-number variables whose only observable effect is `emit`; final states are not observable. It has no pointers, memory, volatile accesses, atomics, threads, recursion or function calls (calls appear only through the `CallSite` construction).

#### 11. Non-claims of `per-loop-semantics-restricts-to-both-global-semantics`

* Shows that toy definitions agree; it does not show that either global semantics matches the C++ standard, LLVM or rustc.
* The per-loop semantics attributes undefined behaviour to a flagged loop only when that loop itself completes infinitely many iterations of its body and eventually stops emitting (SilentlyIterates). Silent divergence inside one iteration, for example in a nested unflagged loop, is never blamed on an enclosing flagged loop (not_progressViolation_flaggedOverUnflagged, mixedBeh_flaggedOverUnflagged), while a flagged loop nested in an unflagged one is blamed (progressViolation_unflaggedOverFlagged). This theorem compares only the two uniform flag assignments; programs with mixed flags are not compared with any external semantics.
* Every per-loop behaviour is a forward-progress behaviour for arbitrary flags (fpBeh_of_mixedBeh); the restriction to uniform flags is what makes the two sides equal.
* The `markAll false` half is near-definitional: no loop is flagged, so no progress violation exists.
* The setting is a toy deterministic While language over natural-number variables whose only observable effect is `emit`; final states are not observable. It has no pointers, memory, volatile accesses, atomics, threads, recursion or function calls (calls appear only through the `CallSite` construction).

#### 12. Non-claims of `unmarked-inlining-of-divergence-observable-callee-miscompiles`

* Does not say any particular compiler performs unmarked inlining; at the referenced LLVM revision the inliner merges mustprogress by logical AND (setAND), which corresponds to inlineDroppingAttr.
* Escape hatches: unmarked inlining into a forward-progress caller introduces no progress violation when every loop of the callee terminates or keeps emitting from every state reachable at the call site, and the subsequent loop deletion adds no behaviour when post already silently diverges with empty trace or has a progress violation (not proved here).
* `CallSite` models only a single top-level call `pre ;; call g ;; post` sharing one global variable store, with no parameters, local variables, early return, unwinding, recursion, or calls nested inside conditionals or loops.
* The setting is a toy deterministic While language over natural-number variables whose only observable effect is `emit`; final states are not observable. It has no pointers, memory, volatile accesses, atomics, threads, recursion or function calls (calls appear only through the `CallSite` construction).

#### 13. Non-claims of `attribute-dropping-inlining-refines`

* Dropping the attribute is sound but coarse: it also removes the progress assumption from the caller's own loops (inlineDroppingAttr_callerLoop_nonvacuous). Inlining that keeps each loop's original flag produces exactly the linked program, so its soundness is reflexivity; for that to be meaningful the per-loop semantics attributes undefined behaviour only to the innermost loop that fails to make progress (SilentlyIterates).
* In LLVM (LoopInfo.cpp `isMustProgress`), a loop is treated as must-progress if its enclosing function carries mustprogress or the loop carries llvm.loop.mustprogress metadata. Intersecting the function attribute (setAND) therefore keeps must-progress optimization of caller loops that carry the loop metadata, whereas attaching llvm.loop.mustprogress to inlined callee loops would bypass setAND and reintroduce the hazard of unmarked inlining (not proved here). Loop metadata is not modelled separately from the per-loop flag. Unlike `SilentlyIterates`, which blames only the innermost loop that fails to make progress, LLVM's `isLoopNestFinite` (llvm/lib/Analysis/LoopInfo.cpp lines 1216-1219 at llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6, whose first test is `SE.loopIsFiniteByAssumption(L)` under the comment 'An assumption on L covers every cycle inside it') treats llvm.loop.mustprogress on an outer loop L as covering every cycle inside L, and llvm/lib/Transforms/Utils/InlineFunction.cpp at that commit contains no handling of llvm.loop.mustprogress, so that metadata on a caller loop is not stripped when a callee without mustprogress is inlined into it. Keeping caller loop metadata is therefore hazard-free for loops that are siblings of the call (pre and post in `CallSite`) but not for a caller loop that encloses a call to a callee without mustprogress (not proved here); calls inside loops are outside `CallSite`.
* `CallSite` models only a single top-level call `pre ;; call g ;; post` sharing one global variable store, with no parameters, local variables, early return, unwinding, recursion, or calls nested inside conditionals or loops.
* The setting is a toy deterministic While language over natural-number variables whose only observable effect is `emit`; final states are not observable. It has no pointers, memory, volatile accesses, atomics, threads, recursion or function calls (calls appear only through the `CallSite` construction).

### Escape hatches

Which settings defeat the negative results (counterexample cards), and which hypotheses, if dropped, defeat the
positive ones:

* `loop-deletion-unsound-divergence-observable`: the deletion becomes a refinement under forward progress
  (`loopDeletion_spin_refines_forwardProgress`), and, under the divergence-observable semantics, whenever at every
  state reachable at the end of p the loop terminates or k itself has the behaviour `div []`
  (`deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff`).
* `loop-deletion-termination-condition-not-necessary`: the example depends on a continuation that itself silently
  diverges; under the extra hypothesis that k never has the behaviour `div []` at reachable states, termination of the
  loop at every reachable entry state is necessary and sufficient
  (`deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff_terminates`).
* `classic-slice-may-terminate-when-original-diverges`: classic slices preserve behaviour from every state on which
  the original terminates (`classicSlice_preserves_terminating_traces`), are forward-progress refinements
  (`classicSlice_refines_forwardProgress`), and termination-guarded slices preserve all divergence-observable
  behaviours (`terminationSensitiveSlice_preserves_obsBeh`).
* `unmarked-inlining-of-divergence-observable-callee-miscompiles`: attribute-dropping inlining is a per-loop
  refinement for every top-level call site (`inlineDroppingAttr_refines_linked`; on this call site
  `inlineDroppingAttr_hazard_defined`).
* For each `tight` hypothesis of a positive result, the named counterexample shows that dropping it (keeping the other
  hypotheses) defeats the conclusion; see the hypothesis ledgers in **Findings**.

### Not examined, known not to apply, and unknown tightness

* **Not examined:** nondeterministic or concurrent languages; languages with memory, pointers, volatile accesses,
  atomics or input; any undefined behaviour other than progress obligations; loops in positions other than
  `p ;; loop ;; k` as deletion targets; calls nested in loops or conditionals; recursion; slicing criteria other than
  all `emit` statements; interprocedural slicing; slicing and liveness algorithms; programs run from a restricted set
  of initial states (refinement always quantifies over every initial state).
* **Known not to apply:** the per-loop transfer of divergence-observable refinements
  (`refines_divergenceObservable_not_imp_refines_mixed`); classic slicing under the divergence-observable semantics
  (`classicSlice_spin_terminates_while_original_diverges`).
* **Unknown tightness:** none. Every hypothesis of every result is labelled `tight` and has a proved counterexample;
  there are no `harmless` or `unknown` entries.

### Refuted stronger statements and dropped statements

Stronger or alternative statements that are **false**, each with a proved counterexample in the package:

* "Deleting an emit-free loop with dead writes is a divergence-observable refinement only if the loop terminates from
  every reachable entry state." False: `deleteLoop_refines_divergenceObservable_without_termination` (deleting
  `while 1 do skip` before another `while 1 do skip`). The statement becomes true under the extra hypothesis
  `hNoSilentK` (`deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff_terminates`).
* "Every classic slice is a divergence-observable refinement." False:
  `classicSlice_spin_terminates_while_original_diverges`.
* "Every divergence-observable refinement is a per-loop refinement, whatever the loop flags." False:
  `refines_divergenceObservable_not_imp_refines_mixed` (`spin true` versus `spin false`).
* "Inlining under the caller's attribute (unmarked inlining) is a per-loop refinement of the linked program." False:
  `inlineUnmarked_divergenceObservableCallee_not_refines`.
* "Every program refines every other under the forward-progress semantics" (that is, the hypotheses of the
  forward-progress theorems carry no content). False: `refines_forwardProgress_needs_hypothesis` (adding an output is
  not a forward-progress refinement), and each hypothesis of the deletion and slicing theorems has its own tightness
  counterexample.
* "Requiring deadness from all states (`DeadAtEntry`) instead of from the states reachable after the prefix
  (`DeadAfterPrefix`) loses nothing." False as a statement about the two conditions:
  `deadAfterPrefix_example_not_deadAtEntry`; the theorems are stated with the weaker `DeadAfterPrefix`.
* "A per-loop progress violation is attributed to an enclosing flagged loop when the silent divergence happens inside
  one of its iterations." Not the case for `ProgressViolation`: `flaggedOverUnflagged` silently diverges from a state
  with `x0 = 0` (`mixedBeh_flaggedOverUnflagged`: its only per-loop behaviour is `div []`, which with no progress
  violation is its divergence-observable behaviour) yet has no progress violation
  (`not_progressViolation_flaggedOverUnflagged`). A definition that blamed every flagged loop whose own run silently
  diverges would make this program undefined; that alternative definition is not formalized here.

No statement of this package was dropped or found false: all 13 results are proved as stated.

## Evidence

### Kernel-check record

Toolchain: Lean 4 `v4.34.1` (`leanprover/lean4` tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), core only, no Mathlib. All 635 declarations of the `Toy` library were audited with `Lean.collectAxioms`; 0 depend on any axiom outside `propext`, `Classical.choice`, `Quot.sound`. No Lean source contains `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC`. The full per-declaration record is `audit/axioms.json`.

For every Lean name referenced by `results.json`: its roles, its axioms, the SHA-256 of its statement (Lean `repr` of its type) and the SHA-256 of its definition closure (the sorted lines `name : type [:= value]` of every `Toy` constant reachable from the statement, theorem bodies omitted), as recorded in `audit/statements.json`.

| Theorem | Roles | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `classicSlice_preserves_terminating_traces` | result `classic-slice-preserves-terminating-traces` | Quot.sound, propext | `b509c24cd25bbf88e58da16104be0eaf937a57467ac8bc05827ae8fd733a11d7` | `e26a9e3f8ba15d4461964372667a1084f17ef5c51b09756be76284b889e197c4` (70) |
| `classicSlice_preserves_terminating_traces_needs_slice` | counterexample (`hSlice`) of `classic-slice-preserves-terminating-traces` | Quot.sound, propext | `9b48ca1d263902bd885263ff1b742c8a699ebf382826e6167fcc352590b08069` | `e26a9e3f8ba15d4461964372667a1084f17ef5c51b09756be76284b889e197c4` (70) |
| `classicSlice_preserves_terminating_traces_nonvacuous` | non-vacuity witness of `classic-slice-preserves-terminating-traces` | Quot.sound, propext | `f423d0012c11156ca07e79250ccefa997e6df055c92b4e66e0745d95ca499c5e` | `f60cd92008227a88d854966ee86bf4d26c7a0ca42d5f90d1626cda4190621d42` (73) |
| `classicSlice_refines_forwardProgress` | result `classic-slice-refines-forward-progress` | Classical.choice, Quot.sound, propext | `2d3fc1039f719928d943b307ec39972f990ec11ffdcfb91f414d91f350b8b0d3` | `90606af5fbe1c868fb3c407a370c23a492f18e59ac81e2a325ce591421d8db60` (73) |
| `classicSlice_refines_forwardProgress_needs_slice` | counterexample (`hSlice`) of `classic-slice-refines-forward-progress` | Quot.sound, propext | `1b8198925da641ea915d3b2d691a1d13be2cb8715cf2b70486072072f6c3b728` | `90606af5fbe1c868fb3c407a370c23a492f18e59ac81e2a325ce591421d8db60` (73) |
| `classicSlice_refines_forwardProgress_nonvacuous` | non-vacuity witness of `classic-slice-refines-forward-progress` | Quot.sound, propext | `4da2b69fb74756c58fb4006f68019be374acf7f7d36fe4fd497e00f919c9a992` | `61ab9979acfa7a3d06181221363e19c693cf460bf7b38c2dfa719f2693a2a577` (62) |
| `classicSlice_silentlyDiverges_or_obsBeh_iff` | companion of `classic-slice-refines-forward-progress` | Classical.choice, Quot.sound, propext | `2047666c8ad6a021836d61ca4f4300e80913d847b85ebef8b4ac78520007191f` | `8ea0338079ffa189b8f3797cec0eeaa754741d77d5d00624d32638b3f4c25640` (71) |
| `classicSlice_spin_terminates_while_original_diverges` | result `classic-slice-may-terminate-when-original-diverges` | Quot.sound, propext | `c00879ef5fd863c683dc36c410d039d75c66c0d7540559d94bfd980b14d6abad` | `9f46ee03ce9fce78969e0be77fd94148b22ff32b5947b3e69f9e407b9596c5b9` (72) |
| `deadAfterPrefix_example_not_deadAtEntry` | companion of `loop-deletion-sound-forward-progress` | Quot.sound, propext | `7b8b94c4ea77c9e120942b0cc5a72e4e79df2487b43060a78490a5b06ddedc1e` | `5650dcdc4e12002952a00946287fe1a2149c76eef7ec0130a664a831cb1b8ffe` (60) |
| `deadAfterPrefix_of_deadAtEntry` | companion of `loop-deletion-sound-forward-progress` | none | `1934229e893c8ef2e642752031f2277736e35091da4c40875bc638a1006d4bde` | `633654e6c0d7f9b9b970f8a01283c91ad2e3002b91bc931d736c9dcd2c660e86` (54) |
| `deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff` | result `loop-deletion-exact-condition-divergence-observable` | Classical.choice, Quot.sound, propext | `dcd21fc996564607d6c5eb7a21b13a099e756db43c47c1df4c2c9e8360df771f` | `60f2a738ded4dda79900bc78d4b7b788192926cfe3fd0cdfcde59af9fcc034d6` (62) |
| `deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff_terminates` | result `loop-deletion-iff-terminates-under-nonsilent-continuation` | Classical.choice, Quot.sound, propext | `cffa99dbe5a219c2f7ffc88735b4f5c280946dbe53be273f6539b5bf827755d5` | `60f2a738ded4dda79900bc78d4b7b788192926cfe3fd0cdfcde59af9fcc034d6` (62) |
| `deleteEmitFreeLoop_withDeadWrites_refines_forwardProgress` | result `loop-deletion-sound-forward-progress` | Classical.choice, Quot.sound, propext | `faca9e73a022b6284f988ca62ffc6dfbe26fd1fa10b87255cfcaa6319a4076f4` | `ef9268f88e2abc53d4e87c491b895d5beaeefce897cf35694efa6680340b5be7` (63) |
| `deleteLoop_divergenceObservable_iff_needs_deadWrites` | counterexample (`hDead`) of `loop-deletion-exact-condition-divergence-observable` | Quot.sound, propext | `4db787f4351eac4d50abd183290e7212d0f3b1f0f6432bacd14ac8b1cf55c149` | `e9962e77f0f81978ea49af6834f96944d271e908f848b001d89af824d86ab1d2` (59) |
| `deleteLoop_divergenceObservable_iff_needs_emitFree` | counterexample (`hEmit`) of `loop-deletion-exact-condition-divergence-observable` | Quot.sound, propext | `ee83e4cb5c435b2734cc8efa31e098a288b639450c98d1464ede415b1cd0109c` | `f87671162dee635b6fd6725a7e098a2f4ebeeae99f30062aeda50d29f871fac0` (60) |
| `deleteLoop_forwardProgress_needs_deadWrites` | counterexample (`hDead`) of `loop-deletion-sound-forward-progress` | Quot.sound, propext | `75ad5ac7f25f8ba1976f04aa62b34cfd1f973e25f88ffca0de3ef446dd36b580` | `c9684125510941f8cdf977508f3f234b09b3b9dbbb4b2c1d3d5648d3e3cf18d5` (59) |
| `deleteLoop_forwardProgress_needs_emitFree` | counterexample (`hEmit`) of `loop-deletion-sound-forward-progress` | Quot.sound, propext | `4ba17b97fd7847f0968bf7d51d25cc3ce300f21b5bf5c4f9ceb8e83efa02bf5c` | `d4d1a979d20ebc39d6941ebd6e4b3f183c80cb00212ef8ad5cc635f847748654` (61) |
| `deleteLoop_hypotheses_nonvacuous` | non-vacuity witness of `loop-deletion-sound-forward-progress` | Quot.sound, propext | `5f7f4d95b0745a326a4306f6081b7ec74c0445d2ac616193ca4e0880390f1cce` | `055d7b9588db932f722054a358c78dab87c9ff37317a546bf9c3a2c8ae7acce6` (64) |
| `deleteLoop_iff_terminates_needs_continuation_not_silent` | counterexample (`hNoSilentK`) of `loop-deletion-iff-terminates-under-nonsilent-continuation` | propext | `1cbccd2768ec1c64a43d8e6751712b5afb43fdb280680fd2b049a669dfbf2291` | `57cf5a73680b913f44d956eabd5614ffc2d868b41e8e9a0bf93201c99ae10d9f` (63) |
| `deleteLoop_iff_terminates_needs_deadWrites` | counterexample (`hDead`) of `loop-deletion-iff-terminates-under-nonsilent-continuation` | Quot.sound, propext | `c25ec0b865856d8e8d9cb76ad4419b75df2874716941ffb29349985f3c2e52fe` | `e9962e77f0f81978ea49af6834f96944d271e908f848b001d89af824d86ab1d2` (59) |
| `deleteLoop_iff_terminates_needs_emitFree` | counterexample (`hEmit`) of `loop-deletion-iff-terminates-under-nonsilent-continuation` | Quot.sound, propext | `3397aea4b0b75df0d670d63a668a143494c77ee8509ebd94940d47bd842ce98d` | `f87671162dee635b6fd6725a7e098a2f4ebeeae99f30062aeda50d29f871fac0` (60) |
| `deleteLoop_iff_terminates_nonvacuous` | non-vacuity witness of `loop-deletion-exact-condition-divergence-observable`; non-vacuity witness of `loop-deletion-iff-terminates-under-nonsilent-continuation` | Classical.choice, Quot.sound, propext | `78f61ca6271ec2ed85cadc7456019553877d7ecbe9a47764329dcf297af8baa5` | `05f313df883dd4519408c0f37661957b24cb588eaf1a33295ec0808898733770` (65) |
| `deleteLoop_refines_divergenceObservable_without_termination` | result `loop-deletion-termination-condition-not-necessary` | propext | `3bbb0d9ccb285f412d40065bc4b31c0cf4b7e3dbf0211debf5b0bc3cd1c4c315` | `57cf5a73680b913f44d956eabd5614ffc2d868b41e8e9a0bf93201c99ae10d9f` (63) |
| `exists_head_silentlyIterates` | companion of `per-loop-semantics-restricts-to-both-global-semantics` | Classical.choice, Quot.sound, propext | `61668471a067a8e0e5f3ffd2f6dc39370741b4b757833038285b3931e31bf22c` | `034b28f5ee1368a7e40020e301f5a50c56430aba2f11c360bf956aab3b309cf6` (57) |
| `fpBeh_of_mixedBeh` | companion of `per-loop-semantics-restricts-to-both-global-semantics` | Classical.choice, Quot.sound, propext | `fc412863f182aa965e4308e0d5e2437853eed249c71ddf1e523fb3bf6920f2de` | `19b9884b6c1f5ff08dfce32b057971c60c1740bfa8a3be4614f44fed1c610f69` (60) |
| `inlineDroppingAttr_callerLoop_nonvacuous` | non-vacuity witness of `attribute-dropping-inlining-refines` | Quot.sound, propext | `8ceffd29f98ba4ad4b1a935f798d6891696635eb47fedecfd437b3ad035b3d9b` | `de6aadeac2d31900d6435467fbcab101a78a3836e7b9c20cbd6c8875b2640146` (78) |
| `inlineDroppingAttr_hazard_defined` | positive control of `unmarked-inlining-of-divergence-observable-callee-miscompiles` | propext | `1f603a6f2368fe291a7e90c4541cbbf298bb19f1a758b4e35aeb3e2f794735a1` | `6ec0ff7a1914b4318d96f63504472ebda783d90262e38f5823141707c3578aa2` (78) |
| `inlineDroppingAttr_refines_linked` | result `attribute-dropping-inlining-refines` | Quot.sound, propext | `54fce3d2d1f2e946763247d8b0fe0516f09fb445684b72489eeaf3a0bc0bfcd2` | `d43e6b5d1d7712f168a8b8148fb27974a7dabe2125a67a4c7b80ee96734a6e07` (75) |
| `inlineUnmarked_divergenceObservableCallee_not_refines` | result `unmarked-inlining-of-divergence-observable-callee-miscompiles` | Quot.sound, propext | `b19f2197dc7b7aa8901ac06d87be34da493087d904e5248240cafc15a4b0b8ac` | `dcce01be1ea1ef66bfa8ec645a95f932fbe6a5ebca572b5a4aa446234d1a8544` (78) |
| `isClassicSlice_refl` | companion of `classic-slice-preserves-terminating-traces` | none | `16c3d353a21764ffce29f3ea8955603a4a3c91e92e964adc53be0fc9638c4b9b` | `8ac0b371157890797b19b68392394f0a26a7d8309c1709ca50cffc0e94473e1a` (59) |
| `isTerminationSensitiveSlice_drops_terminating_loop` | companion of `termination-sensitive-slice-preserves-behaviours` | Quot.sound, propext | `6eb3fa3f44422fb8930a89ed933a8558c613de0a79d4c79892d54d6c02d3ce97` | `06252dde6f5d9056e49a66ce9cc203cfa7a4b8eb1d75238d9c8d36259d9e0ee7` (61) |
| `isTerminationSensitiveSlice_refl` | companion of `termination-sensitive-slice-preserves-behaviours` | none | `6bb36dff2b221ff0b2a58b915d65a8230ded5b8e97075fb45587f73f96084485` | `2457e409d5bb44fab158469b9b24ed0bb11d448ffa960f80bad9fda5ac150353` (59) |
| `loopDeletion_spin_not_refines_divergenceObservable` | result `loop-deletion-unsound-divergence-observable`; positive control of `loop-deletion-termination-condition-not-necessary`; companion of `forward-progress-admits-divergence-observable-refinements` | Quot.sound, propext | `35dc576eef304968dc05df5444727a38c3e679ed390a2be0fe14ae518038a8f4` | `f1e252dfd23f07ac89d3257e4cf4d3081d7d7141308a5aea9ade9330f0c5a57e` (52) |
| `loopDeletion_spin_refines_forwardProgress` | positive control of `loop-deletion-unsound-divergence-observable`; companion of `forward-progress-admits-divergence-observable-refinements` | propext | `4a9888f722e32b286c2a8e0eea6e66a4164ad55f49b77e336e753db2950d3da1` | `18aaa77083603db8082b79c34c830a7c2aa78622f557c17c0152c93093d96b86` (54) |
| `mixedBeh_flaggedOverUnflagged` | companion of `per-loop-semantics-restricts-to-both-global-semantics` | propext | `e0b1a611d8bbd73380db8736536430e3cfeabc14c309e5355d5882d36849d1f8` | `652937cf6cc9d2eb16dea662b072ccefd0c6e13bb4a336626bb81b221eeb8c7b` (61) |
| `mixedBeh_markAll_false_iff_obsBeh` | companion of `per-loop-semantics-restricts-to-both-global-semantics` | Quot.sound, propext | `cbd1c03f008e9d8e3474687814ed3d40eddfa99a38a6ffd5672ee9c968a8ec3a` | `16d7222730dadf755ee95fb0a6e81c8ea303956d42c50bc09621e73dd506df35` (62) |
| `mixedBeh_markAll_nonvacuous` | non-vacuity witness of `per-loop-semantics-restricts-to-both-global-semantics` | propext | `ebb3267062f11d7b5f945e84274379364da03eef2de12b04d7e036539193e75b` | `cbe54c1d78d439c445f0277d9a75e42c0358eaac8f1e6c3232c075889de827b7` (65) |
| `mixedBeh_markAll_restricts` | result `per-loop-semantics-restricts-to-both-global-semantics` | Classical.choice, Quot.sound, propext | `33d69a5aff8c1683d82256b1bee946c67ff34a653567fa62628e671a52548d19` | `4a9d69888831935d1e69fb7e5100a92e06c936fca88bb746ae2fce0d2bfe02b1` (64) |
| `mixedBeh_markAll_true_iff_fpBeh` | companion of `per-loop-semantics-restricts-to-both-global-semantics` | Classical.choice, Quot.sound, propext | `9bcc4aa88cacb3f036702c675ca1fb086bc3a2ede60b6313545026e3f1fab117` | `4a9d69888831935d1e69fb7e5100a92e06c936fca88bb746ae2fce0d2bfe02b1` (64) |
| `noSilentK_admits_emit_then_spin` | companion of `loop-deletion-iff-terminates-under-nonsilent-continuation` | Classical.choice, Quot.sound, propext | `7f77102e0aa692244a94ef30a3632cabae0c4a9a6f5f6ea0cff1ea30c8d29089` | `dfa5bd2fb8ef7a4d5869e23544c334fb1cf64853cb7019bca4940427d1b2fd49` (52) |
| `not_isTerminationSensitiveSlice_spin` | positive control of `classic-slice-may-terminate-when-original-diverges` | propext | `5c87c8271fb5f8c43985763b44dc3a3db90c21c393c35cdff7c6278c06f3e7b8` | `0786ebe6c12325958989dc465cf6ebbf3ed6fa6cecec5cea2d48dfbee30c5635` (60) |
| `not_progressViolation_flaggedOverUnflagged` | companion of `per-loop-semantics-restricts-to-both-global-semantics` | propext | `c66e007e7e52dd4b133f4dc122cfc46d4ddfc273dde761a97d1158dc621546a6` | `d2dba86290cf70683b1212e3df9c7e04a2ac2c55eb8e5ed95e4eb49e01af81f5` (49) |
| `obsBeh_exists` | companion of `loop-deletion-exact-condition-divergence-observable` | Classical.choice, Quot.sound, propext | `e09b8c20bc6f0404ec2df14d784593f165e0cdb7f44a0e0b5490e069b49bd5a5` | `210c38de261530637a25b10ea9c420104fecf39e8dcce524262a3f9dbd094f67` (50) |
| `obsBeh_unique` | companion of `loop-deletion-exact-condition-divergence-observable` | Quot.sound, propext | `e2ede3b3a67a5705b499c8c07fe22e1dc8f6bce19138e4b0e48351dec26ce80e` | `210c38de261530637a25b10ea9c420104fecf39e8dcce524262a3f9dbd094f67` (50) |
| `progressViolation_unflaggedOverFlagged` | companion of `per-loop-semantics-restricts-to-both-global-semantics` | propext | `6a56f19e58e27fcb4045d14f073ade0e0cf9d995da44d5ad78162c9750d1db84` | `83650015e34de673798c32744c0cf96b3ec1ff3889405f6d06f7a61dc60a1154` (49) |
| `refines_divergenceObservable_example` | non-vacuity witness of `forward-progress-admits-divergence-observable-refinements` | Quot.sound, propext | `416ac46341d98a3b9c53e3892a82903e07e7d7fa09769dd51004492faadba2cf` | `a3f6129713903fc4c8648c2b1f8d9e443d036f0f0888d32a8df6994b54de6d97` (51) |
| `refines_divergenceObservable_not_imp_refines_mixed` | companion of `forward-progress-admits-divergence-observable-refinements` | propext | `ff885e549fc5ce4922a90bce388ae0372b708986e7fb8c43e2fb88e2a972238b` | `9aedf511e52bbf2e3690307cf57aa91242caf257e89a6562fa15b26a95936f81` (60) |
| `refines_forwardProgress_needs_hypothesis` | companion of `forward-progress-admits-divergence-observable-refinements` | Quot.sound, propext | `52bbd4e3316f69841c3d01bdc1075c13f892f35c288830c3c06b484dc4a6c0ef` | `c57d0c231259e6c420ede2202c8ecbfa879fbbd4edf523edf0c8b7feec004b71` (53) |
| `refines_forwardProgress_of_refines_divergenceObservable` | companion of `forward-progress-admits-divergence-observable-refinements` | none | `fbdb14c1f6bd36470c1af09ca633259dcbada44cfb2e8351f83e4d476f6e8ef3` | `c57d0c231259e6c420ede2202c8ecbfa879fbbd4edf523edf0c8b7feec004b71` (53) |
| `refines_forwardProgress_of_refines_divergenceObservable_strict` | result `forward-progress-admits-divergence-observable-refinements` | Quot.sound, propext | `2845333d1649542f052f596d4a4b139e7e7cb7d237a0ae576cd786dafe2f42c3` | `c57d0c231259e6c420ede2202c8ecbfa879fbbd4edf523edf0c8b7feec004b71` (53) |
| `refines_fpBeh_iff_silentlyDiverges_or_obsBeh_iff` | companion of `classic-slice-refines-forward-progress` | Classical.choice, Quot.sound, propext | `33ad698ea2f0546d360e135379c45e01a2ba3d5ab3d474c95b0fc26b79707cf4` | `c57d0c231259e6c420ede2202c8ecbfa879fbbd4edf523edf0c8b7feec004b71` (53) |
| `refines_obsBeh_iff_equiv` | companion of `loop-deletion-exact-condition-divergence-observable`; companion of `loop-deletion-iff-terminates-under-nonsilent-continuation`; companion of `forward-progress-admits-divergence-observable-refinements`; companion of `termination-sensitive-slice-preserves-behaviours` | Classical.choice, Quot.sound, propext | `3db16b67fb13101fa69ca0cfa9dcbe59e7f41f4aa6ee0d47e97ad23bce7ea9f3` | `a3f6129713903fc4c8648c2b1f8d9e443d036f0f0888d32a8df6994b54de6d97` (51) |
| `silentlyDiverges_of_progressViolation` | companion of `per-loop-semantics-restricts-to-both-global-semantics` | Classical.choice, Quot.sound, propext | `576226d09fdc3b628ac198c7e4e6f2327a2452c2ac0e3d09e03da6565be29730` | `a0f0025bc2937992b902b40cd7f760267c77f86b806d62ae975eda4a32fb43e9` (58) |
| `slice_partial_fwd` | companion of `classic-slice-refines-forward-progress` | Quot.sound, propext | `4a18b9e04e25d702ecc1fed58bf5b6bf81f88c983fc84be5fd73966c262e2e33` | `544fbf1307e8378a9c4e6ae5c601c8c5961f39d684d59a449bf984a6d4a4dd73` (77) |
| `terminationSensitiveSlice_needs_terminationSensitivity` | counterexample (`hSlice`) of `termination-sensitive-slice-preserves-behaviours` | Quot.sound, propext | `5a253f0763698af1eae7b9aacddbc4f470b331dd53d06e111a0f3a8071443564` | `e9e4d8796a1654fc302842d499ed9a9aff145189d51d9621bf407321e8776bd9` (71) |
| `terminationSensitiveSlice_preserves_obsBeh` | result `termination-sensitive-slice-preserves-behaviours` | Quot.sound, propext | `5c4dcbef2c90b8d7cd06d4d57d121be738fc86f15f5834fbd2517d34b26b9cca` | `87ecb9486d73dba75537e323c1c1f6b075b7068179df741bc137d98207123ad2` (70) |
| `terminationSensitiveSlice_preserves_obsBeh_nonvacuous` | non-vacuity witness of `termination-sensitive-slice-preserves-behaviours` | Quot.sound, propext | `b4a199fea976046aeec39d4e27cac5ed6fe5b015f93cc3fc07c9d1c4453ef2d6` | `2906da6d28c2783a81ad9a928fca998ccd0350f47608ec33e7ce3f26ffe87b61` (62) |

### Primary sources

Bibliographic records (titles, venues, volumes, pages, authors) were checked against Crossref for every DOI below; GitHub sources were read at the pinned commits; the C11 and C++ texts were read in the renderings given. Evidence observed on 2026-11-21.

* rust-lang/rust issue #28728, 'LLVM loop optimization can make safe programs crash' (opened 2015-09-29; closed 2021-03-05 as completed with the comment 'Closed by #81451'), https://github.com/rust-lang/rust/issues/28728; rust-lang/rust pull request #81451, 'Upgrade to LLVM 12' (merged 2021-03-04, merge commit 409920873cf8a95739a55dc5fe5adb05e1b4758e).
* CompCert, AbsInt/CompCert commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, common/Behaviors.v: `program_behavior` has constructors Terminates (trace and exit code), Diverges (finite trace), Reacts (infinite trace) and Goes_wrong (trace); `behavior_improves beh1 beh2` holds iff beh1 = beh2 or beh1 = Goes_wrong t for a prefix t of beh2. Prose comparison only.
* Xavier Leroy, 'A Formally Verified Compiler Back-end', Journal of Automated Reasoning 43(4):363-446, 2009, DOI 10.1007/s10817-009-9155-4 (compiler correctness stated over observable behaviours, including divergence).
* Nuno P. Lopes, Juneyoung Lee, Chung-Kil Hur, Zhengyang Liu, John Regehr, 'Alive2: Bounded Translation Validation for LLVM', PLDI 2021, pp. 65-79, DOI 10.1145/3453483.3454030.
* ISO/IEC JTC1/SC22/WG21 N4861 (C++ working draft, 2020-04-01), §6.9.2.2 [intro.progress] paragraph 1: the implementation may assume that any thread will eventually terminate, call a library I/O function, perform a volatile access, or perform a synchronization or atomic operation; its note says this is intended to allow removal of empty loops even when termination cannot be proven. Rendering: https://timsong-cpp.github.io/cppwp/n4861/intro.progress.
* ISO/IEC 9899 draft N1570 (C11), §6.8.5 paragraph 6: an iteration statement whose controlling expression is not a constant expression and that performs no input/output operations, does not access volatile objects, and performs no synchronization or atomic operations in its body, controlling expression, or (for a for statement) expression-3, may be assumed by the implementation to terminate. Rendering: https://port70.net/~nsz/c/c11/n1570.html.
* JF Bastien, 'Trivial infinite loops are not Undefined Behavior', WG21 P2809R3, 2024-03-21, https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2024/p2809r3.html. Its wording is in [stmt.iter.general] of the C++ working draft, cplusplus/draft commit 604674fa5028d318770a1b689966cffeeedd4e2b, source/statements.tex lines 585-597: a trivial infinite loop is a trivially empty iteration statement (body `;` or `{}`) whose converted controlling expression is a constant expression evaluating to true; its statement is replaced by a call to std::this_thread::yield, and whether this replacement occurs on freestanding implementations is implementation-defined.
* LLVM Language Reference Manual at llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6, file llvm/docs/LangRef.md (quoted sentence at line 2981): function attribute `mustprogress` (the function is required to return, unwind, or interact with the environment in an observable way; intended to model the first section of [intro.progress]; terminating loops without side effects can be removed; 'If a mustprogress function calls a function not marked mustprogress, and that function never returns, the program is well-defined even if there isn't any other observable progress') and loop metadata `llvm.loop.mustprogress`.
* llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6: llvm/lib/Transforms/Scalar/LoopDeletion.cpp line 110 (`isLoopDead` ends with `return isLoopNestFinite(L, SE, LI);`, defined at llvm/lib/Analysis/LoopInfo.cpp line 1216: the loop must be finite by assumption (ScalarEvolution::loopIsFiniteByAssumption), or every loop of its nest must be finite by assumption or have a computable constant maximal backedge-taken count); llvm/lib/Transforms/Utils/LoopUtils.cpp lines 622-628 (`deleteDeadLoop` replaces the branch into a deleted loop that has no exit block by `unreachable`).
* Ralph-Johan Back, Joakim von Wright, 'Refinement Calculus: A Systematic Introduction', Springer, 1998, DOI 10.1007/978-1-4612-1674-2.
* Mark Weiser, 'Program Slicing', IEEE Transactions on Software Engineering SE-10(4):352-357, July 1984, DOI 10.1109/TSE.1984.5010248. Its definition of a slice (p. 353) requires: 'Whenever P halts on an input I with state trajectory T, then S also halts on input I with state trajectory T'' with equal projections; a footnote says that extending the definition to inputs on which the original program does not halt 'causes many new problems', since there is no way to guarantee that a slice fails to halt whenever the original program fails to halt.
* Thomas Reps and Wuu Yang, 'The Semantics of Program Slicing', Computer Sciences Technical Report #777, University of Wisconsin-Madison, June 1988; conference version: Thomas W. Reps and Wuu Yang, 'The Semantics of Program Slicing and Program Integration', TAPSOFT '89 Vol. 2, LNCS 352:360-374, Springer, 1989, DOI 10.1007/3-540-50940-2_47. Slicing Theorem: from any initial state on which the program halts, a dependence-graph slice also halts and computes the same sequence of values at each of its program points.
* Susan Horwitz, Thomas W. Reps, David W. Binkley, 'Interprocedural Slicing Using Dependence Graphs', ACM TOPLAS 12(1):26-60, 1990, DOI 10.1145/77606.77608.
* Daniel Wasserrab, 'Towards Certified Slicing', Archive of Formal Proofs, September 16, 2008, https://www.isa-afp.org/entries/Slicing.html (Isabelle/HOL framework for dynamic and static intraprocedural slicing over control-flow and dependence graphs, instantiated to a While language and to Jinja bytecode; correctness is stated as a weak simulation of the original by the slice).
* Sandrine Blazy, André Maroneze, David Pichardie, 'Verified Validation of Program Slicing', CPP 2015, pp. 109-117, DOI 10.1145/2676724.2693169 (Coq, CompCert).
* Torben Amtoft, 'Slicing for modern program structures: a theory for eliminating irrelevant loops', Information Processing Letters 106(2):45-51, 2008, DOI 10.1016/j.ipl.2007.10.002.
* Sebastian Danicic, Richard W. Barraclough, Mark Harman, John D. Howroyd, Ákos Kiss, Michael R. Laurence, 'A unifying theory of control dependence and its application to arbitrary program structures', Theoretical Computer Science 412(49):6809-6842, 2011, DOI 10.1016/j.tcs.2011.08.033.
* Andy Podgurski and Lori A. Clarke, 'A Formal Model of Program Dependences and Its Implications for Software Testing, Debugging, and Maintenance', IEEE TSE 16(9):965-979, 1990, DOI 10.1109/32.58784 (weak and strong control dependence).
* Venkatesh Prasad Ranganath, Torben Amtoft, Anindya Banerjee, Matthew B. Dwyer, John Hatcliff, 'A New Foundation for Control-Dependence and Slicing for Modern Program Structures', ESOP 2005, LNCS 3444:77-93, Springer, 2005, DOI 10.1007/978-3-540-31987-0_7; journal version: Venkatesh Prasad Ranganath, Torben Amtoft, Anindya Banerjee, John Hatcliff, Matthew B. Dwyer, 'A new foundation for control dependence and slicing for modern program structures', ACM TOPLAS 29(5), Article 27, 2007, DOI 10.1145/1275497.1275502. Defines non-termination-sensitive and non-termination-insensitive control dependence on control-flow graphs.
* Jean-Christophe Léchenet, Nikolai Kosmatov, Pascale Le Gall, 'Cut branches before looking for bugs: certifiably sound verification on relaxed slices', Formal Aspects of Computing 30(1):107-131, 2018, DOI 10.1007/s00165-017-0439-x (Coq).
* Daniel Wasserrab, Denis Lohner, Gregor Snelting, 'On PDG-Based Noninterference and its Modular Proof', PLAS 2009, pp. 31-44, DOI 10.1145/1554339.1554345 (Isabelle/HOL).
* llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6: llvm/include/llvm/IR/Attributes.td line 515 `def : MergeRule<"setAND<MustProgressAttr>">;`; llvm/lib/IR/Attributes.cpp lines 2680-2684 (`setAND` removes the attribute from the caller when the callee lacks it), applied by AttributeFuncs::mergeAttributesForInlining, which llvm/lib/Transforms/Utils/InlineFunction.cpp calls at lines 3399 and 3567; llvm/lib/Analysis/LoopInfo.cpp lines 1249-1250 (`isMustProgress(L)` holds if the enclosing function is mustprogress or the loop carries llvm.loop.mustprogress).
* Lean 4 toolchain: repository `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` (also reported by `lean --version`).

### Package contents

* `results.json` — machine-readable result cards (claims, hypothesis ledgers, witnesses, non-claims, prior art, design questions).
* `lean/` — the Lake project (`lean-toolchain`, `lakefile.toml`, `Toy.lean`, `Toy/Progress/*.lean`) and `RevalidationAudit.lean`, an audit program outside the library target.
* `audit/axioms.json`, `audit/statements.json` — the recorded axiom audit and statement/closure hashes.
* `support/revalidate.py` — the revalidation script described below.

## Revalidation

Requirements: `elan` (so that `lake` installs and uses the toolchain pinned in `lean/lean-toolchain`) and `python3`.
No network access is needed beyond the toolchain download; the project has no dependencies.

**Primary check.** From the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, rejects any Lean source
containing `sorry`, `admit`, `native_decide` or an `axiom` declaration (comments excluded), audits every declaration of
the `Toy` library with `Lean.collectAxioms` (only `propext`, `Classical.choice`, `Quot.sound` are allowed), and, for
every Lean name referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`,
`positive_control_lean`, and hypothesis `counterexample`s) and every name in `audit/statements.json`, recomputes
SHA-256 of the statement (Lean `repr` of the declaration's type) and of the definition closure (one line
`name : repr type [:= repr value]` for each `Toy` constant reachable from the statement through types, definition
values and inductive constructors, theorem bodies omitted, sorted, joined with newlines) and compares them with
`audit/statements.json`. It prints `REVALIDATED` and exits 0 iff every check passes.

**Manual equivalent** (same computation, step by step):

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/revalidation-audit.txt
cd ..
python3 - <<'EOF'
import hashlib, json, re
out = open('/tmp/revalidation-audit.txt').read()
audit = json.loads(re.search(r'REVALIDATE_JSON (\{.*\})', out).group(1))
recorded = json.load(open('audit/statements.json'))['statements']
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
bad_axioms = [d['name'] for d in audit['decls'] if set(d['axioms']) - allowed]
bad_hashes = []
for s in audit['stmts']:
    got = None if s.get('missing') else {
        'statement_sha256': hashlib.sha256(s['type_repr'].encode()).hexdigest(),
        'closure_sha256': hashlib.sha256('\n'.join(s['closure']).encode()).hexdigest(),
        'closure_size': len(s['closure'])}
    if got != recorded.get(s['name']):
        bad_hashes.append(s['name'])
print(len(audit['decls']), 'declarations; axiom violations:', bad_axioms)
print(len(audit['stmts']), 'statements; hash mismatches:', bad_hashes)
EOF
```

`RevalidationAudit.lean` lists exactly the names referenced by `results.json`; both lists must come out empty.

**What a passing run establishes.** That the theorems, as stated in `lean/`, are accepted by the Lean kernel with the
standard axioms only and that their statements and definition closures are the ones recorded here. It does not
re-check the modelling-bridge claims. To revalidate those against a newer subject, re-read: for LLVM, `isMustProgress`
and `isLoopNestFinite` in `llvm/lib/Analysis/LoopInfo.cpp`, `loopIsFiniteByAssumption` in
`llvm/lib/Analysis/ScalarEvolution.cpp`, `isLoopDead` in `llvm/lib/Transforms/Scalar/LoopDeletion.cpp`, `deleteDeadLoop`
in `llvm/lib/Transforms/Utils/LoopUtils.cpp`, the `MustProgressAttr` merge rule in `llvm/include/llvm/IR/Attributes.td`
and `setAND` in `llvm/lib/IR/Attributes.cpp`, and the `mustprogress` and `llvm.loop.mustprogress` entries of
`llvm/docs/LangRef.md`; for C++, [intro.progress] and [stmt.iter.general] in `source/` of `cplusplus/draft`; for C, the
iteration-statement termination paragraph (§6.8.5p6 in N1570).
