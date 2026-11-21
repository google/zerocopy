# Weak-memory execution graphs and compilation mappings: a toy SC/TSO model in Lean 4

## Summary

> **This is a toy model.** Every theorem below is about finite candidate executions of
> straight-line programs (constant stores and loads, one access size, one full fence, no
> registers, control flow, dependencies, read-modify-write or locked instructions) in an
> axiomatic model written in the style of Alglave, Maranget and Tautschnig. The Lean kernel checks
> the theorems about that model. Any statement about x86 hardware, x86-TSO, C11/C++ or Rust is a
> separate modeling-bridge claim (`derived`), argued from the cited papers, never a theorem here.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

The package defines candidate executions (events, `po`, `rf`, `co`, derived `fr`), SC
consistency (`po ∪ rf ∪ co ∪ fr` acyclic), a two-axiom x86-TSO-style consistency (SC per location
plus acyclicity of `ppo ∪ rfe ∪ co ∪ fr ∪ fence`, where `ppo` and `fence` relate memory accesses
only), straight-line programs, and the mapping `fenceAfterStores` that inserts an `mfence`
after every store. It proves these results (identifiers are the `results.json` ids):

1. **acyclicity-decision-procedure** (reference point). For every Boolean relation on `Fin n`,
   the Floyd–Warshall stage `warshall r n` relates `a` to `b` exactly when there is a non-empty
   `r`-path from `a` to `b`, and `acyclicB r = true` exactly when `r` is acyclic.
2. **sc-implies-tso.** Every SC-consistent candidate execution, well formed or not, is
   TSO-consistent.
3. **sb-tso-not-sc.** The store-buffering weak outcome `sbWeak` is a well-formed, TSO-consistent,
   not SC-consistent candidate execution of the SB program, so TSO-consistency does not imply
   SC-consistency even for well-formed executions.
4. **litmus-table.** For MP, LB, 2+2W, IRIW and SB+mfences, the weak-outcome execution of the
   program defined in `Litmus.lean` (`mpWeak`, `lbWeak`, `w22Weak`, `iriwWeak`, `sbFencedWeak`;
   card 4 lists their read values and final writes) is well formed and neither TSO- nor
   SC-consistent; for R, the execution `rWeak` (`r0 = 0`, final `y = 3`) is well formed,
   TSO-consistent and not SC-consistent.
5. **keep-same-location-wr-ppo-variant-rejected.** Keeping same-location write→read pairs in
   preserved program order gives a strictly stronger model: everything it accepts is
   TSO-consistent, and it rejects the n6 store-forwarding execution `n6Weak` (`r0 = 1`, `r1 = 0`,
   final `x = 1`), which is well formed and TSO-consistent.
6. **fence-mapping-soundness-execution.** If `po` is total on each thread, `rf` respects
   locations, every `po`-ordered write→read pair is separated by a fence, and the execution is
   TSO-consistent, then it is SC-consistent after erasing fence events.
7. **fence-mapping-soundness-program.** Every candidate execution of `fenceAfterStores P` whose
   `rf` respects locations and which is TSO-consistent is SC-consistent after erasing fence
   events.
8. **fence-mapping-source-execution.** Every TSO-consistent candidate execution `X` of
   `fenceAfterStores P` with well-formed `rf` and `co` (`RfCoWf`) is, read through an
   order-preserving map `f` from the events of `P` that hits every memory access of `X`, a
   well-formed SC-consistent candidate execution `X.comap f` of `P`.
9. **fence-erasure** (reference point). If `po` is irreflexive and transitive, `rf` goes from
   writes to reads and `co` relates same-location writes, SC after erasing fences implies SC with
   fences present.
10. **shared-location-fencing-soundness.** If `po` is transitive, within threads and total on
    each thread, `rf` and `co` stay on one location, every `po`-ordered write→read pair whose
    write and read locations are both accessed by two or more threads is fenced, and the
    execution is TSO-consistent, then it is SC-consistent after erasing fences.
11. **partial-fencing-unsound.** SB with an `mfence` after thread 0's store only has a
    well-formed TSO-consistent execution that is not SC-consistent even after fence erasure.
12. **straight-line-race-freedom-collapse.** For straight-line programs, every conflicting pair
    is `hb`-unordered in some well-formed SC execution, so "every well-formed SC execution is
    race free" collapses to a static condition on the program, for the plain `hb` definition
    (no conflicts at all) and for the both-sides and either-side fence exemptions.
13. **static-both-sides-fencing-sc-on-tso.** If every conflicting pair of a program has both
    accesses free of unfenced write→read pairs (`P.ConflictsWRFenced`), every candidate
    execution of `P` with location-respecting `rf` from writes to reads, `co` on same-location
    writes, and TSO-consistency is SC-consistent.
14. **drf-either-fenced-variant-rejected.** Exempting a conflicting pair when either access is
    free of unfenced write→read pairs does not give SC on TSO (counterexample: SB with one fence).

Results 3, 5, 11 and 14 are counterexamples. None of the results is an x86 hardware theorem, a
C11/RC11 compilation theorem, or a DRF-SC theorem. Read **Boundaries** (non-claims first)
before relying on any of them.

## Applicability

### Model fidelity: what the toy captures and what it omits

The definitions are meant to capture the axiomatic presentation of SC and x86-TSO used by
Alglave, Maranget and Tautschnig (*Herding Cats*, TOPLAS 2014): SC PER LOCATION (Fig. 5) and the
TSO instance of Fig. 21 (`ppo = po \ WR` over memory events, full fence `mfence`), which their
Lemma 4.1 proves equivalent to SPARC TSO via Alglave (FMSD 2012), Def. 23. The same `ppo` and
`fence` relations appear in the Coq development `weakmemory/imm` (commit
`4ca191b072df081dd3a6d9aa755959dc901b1bd0`), file `src/hardware/TSO.v`, lines 48–50
(`ppo := ([RW];sb;[RW]) \ (W×R)`, `fence := [RW];sb;[MFENCE];sb;[RW]`). That this axiomatic
predicate describes x86 multiprocessors is the published claim of Owens, Sarkar and Sewell
(TPHOLs 2009) and Sewell et al. (CACM 2010); this package does not formalize the x86-TSO abstract
machine and proves no equivalence with it.

Known gaps (each is a reason a theorem here may fail to transfer):

- **Programs.** Straight-line only: `store l v`, `load l`, `mfence`, constant locations and
  values, no registers, no control flow, no dependencies, no read-modify-write or `LOCK`-prefixed
  instructions, one access size. Reads may return any value that `rf` permits.
- **Executions.** Finite candidate executions with explicit initialisation writes (one per
  location, belonging to no thread). `rf` and `co` are arbitrary Boolean relations; every
  well-formedness condition is a separate predicate, so each theorem names exactly what it uses.
  Executions of a program fix the events and `po` canonically (`layout`).
- **Fences.** One full fence. Fence events are never endpoints of `ppo` or `fence`.
- **Not modelled.** C11/RC11, Java, Rust atomics, out-of-thin-air behaviour, mixed-size accesses,
  ARM/POWER/RISC-V, and compiler transformations other than fence insertion.

### Key definitions (quoted from `lean/ToyWMM/`)

The blocks below are abridged (field lists and some bodies condensed onto one line, `X : Exec n`
implicit); the source files are authoritative.

```lean
-- Exec.lean
inductive Kind where | init | read | write | fence
structure Event where  kind : Kind; tid : Nat; loc : Nat; val : Nat
def Event.isWrite (e : Event) : Bool := match e.kind with | .write | .init => true | _ => false
def Event.isAccess (e : Event) : Bool := !e.isFence
structure Exec (n : Nat) where  ev : Fin n → Event; po : Rel n; rf : Rel n; co : Rel n
def sameThread (a b : Fin n) : Bool := !(X.ev a).isInit && !(X.ev b).isInit && (X.ev a).tid == (X.ev b).tid
def fr : Rel n := fun a b => decide (∃ w : Fin n, X.rf w a = true ∧ X.co w b = true)
def rfe : Rel n := fun a b => X.rf a b && !X.sameThread a b
def ppo : Rel n := fun a b =>
  X.po a b && (X.ev a).isAccess && (X.ev b).isAccess && !((X.ev a).isWrite && (X.ev b).isRead)
def fenceOrd : Rel n := fun a b => (X.ev a).isAccess && (X.ev b).isAccess &&
  decide (∃ f : Fin n, X.po a f = true ∧ (X.ev f).isFence = true ∧ X.po f b = true)
def poLoc : Rel n := fun a b => X.po a b && X.sameLoc a b && (X.ev a).isAccess && (X.ev b).isAccess
def scRel : Rel n := fun a b => X.po a b || X.rf a b || X.co a b || X.fr a b
def uniprocRel : Rel n := fun a b => X.poLoc a b || X.rf a b || X.co a b || X.fr a b
def tsoRel : Rel n := fun a b => X.ppo a b || X.rfe a b || X.co a b || X.fr a b || X.fenceOrd a b
def eraseFences (r : Rel n) : Rel n := Rel.restrict (fun a => (X.ev a).isAccess) r
def SCConsistent : Prop := Rel.Acyclic X.scRel
def SCConsistentErased : Prop := Rel.Acyclic (X.eraseFences X.scRel)
def PerLocSC : Prop := Rel.Acyclic X.uniprocRel
def TsoGhbAcyclic : Prop := Rel.Acyclic X.tsoRel
def TSOConsistent : Prop := X.PerLocSC ∧ X.TsoGhbAcyclic
-- Rel.lean
abbrev Rel (n : Nat) := Fin n → Fin n → Bool
def Path (r : Rel n) : Fin n → Fin n → Prop := Relation.TransGen (fun a b => r a b = true)
def Acyclic (r : Rel n) : Prop := ∀ a, ¬ Path r a a
```

Well-formedness (`Exec.lean`), one predicate per condition: `PoIrrefl`, `PoTrans`,
`PoWithinThread` (`po a b → sameThread a b`), `PoTotal` (distinct same-thread events are
`po`-ordered), `RfSameLoc`, `RfKinds` (`rf` from a write to a read), `RfSameVal`, `RfTotal`
(every read has an `rf` source), `RfFunctional`, `CoKinds` (`co` between same-location writes),
`CoIrrefl`, `CoTrans`, `CoTotal` (on the writes to each location), `CoInitFirst`
(initialisation writes `co`-first). `Wf` is their conjunction; `RfCoWf` is the conjunction of
the nine conditions on `rf` and `co` other than `CoIrrefl`; `CoSameLoc` is the location part of
`CoKinds`.

Fencing and sharing (`Exec.lean`):

```lean
def FenceBetweenWR : Prop := ∀ a b, X.po a b = true → (X.ev a).isWrite = true →
  (X.ev b).isRead = true → X.fenceOrd a b = true
def LocalLoc (l : Nat) : Prop := ∀ a b, (X.ev a).isAccess = true → (X.ev b).isAccess = true →
  (X.ev a).isInit = false → (X.ev b).isInit = false → (X.ev a).loc = l → (X.ev b).loc = l →
  (X.ev a).tid = (X.ev b).tid
def FenceBetweenSharedWR : Prop := ∀ a b, X.po a b = true → (X.ev a).isWrite = true →
  (X.ev b).isRead = true → ¬ X.LocalLoc (X.ev a).loc → X.fenceOrd a b = true
def FenceBetweenBothSharedWR : Prop := ∀ a b, X.po a b = true → (X.ev a).isWrite = true →
  (X.ev b).isRead = true → ¬ X.LocalLoc (X.ev a).loc → ¬ X.LocalLoc (X.ev b).loc →
  X.fenceOrd a b = true
```

Programs and the mapping (`Prog.lean`, `DRF.lean`, `SourceExec.lean`):

```lean
inductive Instr where | store (loc val : Nat) | load (loc : Nat) | mfence
abbrev Prog := List (List Instr)          -- thread t has thread id t
def layout (P : Prog) : List Event :=     -- init writes for 0 … numLocs-1, then threads in order
  (List.range P.numLocs).map Event.initW ++ threadEvents 0 P
structure ExecOf (P : Prog) {n : Nat} (X : Exec n) : Prop where
  length : n = (layout P).length
  kind : ∀ i, (X.ev i).kind = ((layout P).getD i.val default).kind
  tid  : ∀ i, (X.ev i).tid  = ((layout P).getD i.val default).tid
  loc  : ∀ i, (X.ev i).loc  = ((layout P).getD i.val default).loc
  val  : ∀ i, (X.ev i).isRead = false → (X.ev i).val = ((layout P).getD i.val default).val
  po   : ∀ a b, X.po a b = (X.sameThread a b && decide (a.val < b.val))
def fenceThread : List Instr → List Instr
  | [] => [] | .store l v :: rest => .store l v :: .mfence :: fenceThread rest
  | .load l :: rest => .load l :: fenceThread rest | .mfence :: rest => .mfence :: fenceThread rest
def fenceAfterStores (P : Prog) : Prog := P.map fenceThread
def skel (P : Prog) : Exec (layout P).length   -- events and po of layout P, empty rf and co
def Exec.comap (X : Exec n) (f : Fin m → Fin n) : Exec m where
  ev a := X.ev (f a); po a b := X.po (f a) (f b); rf a b := X.rf (f a) (f b); co a b := X.co (f a) (f b)
```

Races (`DRF.lean`):

```lean
def hbRel : Rel n := fun a b => X.po a b || X.rf a b
def HB (a b : Fin n) : Prop := Rel.Path X.hbRel a b
def Conflict (a b : Fin n) : Prop := (X.ev a).isAccess = true ∧ (X.ev b).isAccess = true ∧
  (X.ev a).isInit = false ∧ (X.ev b).isInit = false ∧ (X.ev a).tid ≠ (X.ev b).tid ∧
  (X.ev a).loc = (X.ev b).loc ∧ ((X.ev a).isWrite = true ∨ (X.ev b).isWrite = true)
def NoUnfencedWRIncident (a : Fin n) : Prop :=
  ((X.ev a).isWrite = true → ∀ b, X.po a b = true → (X.ev b).isRead = true → X.fenceOrd a b = true) ∧
  ((X.ev a).isRead = true → ∀ b, X.po b a = true → (X.ev b).isWrite = true → X.fenceOrd b a = true)
def Race (a b) : Prop := X.Conflict a b ∧ ¬ X.HB a b ∧ ¬ X.HB b a ∧
  ¬ (X.NoUnfencedWRIncident a ∧ X.NoUnfencedWRIncident b)
def RaceFree : Prop := ∀ a b, ¬ X.Race a b
def RaceEither (a b) : Prop := X.Conflict a b ∧ ¬ X.HB a b ∧ ¬ X.HB b a ∧
  ¬ (X.NoUnfencedWRIncident a ∨ X.NoUnfencedWRIncident b)
def RaceFreeEither : Prop := ∀ a b, ¬ X.RaceEither a b
def Prog.ConflictsWRFenced (P : Prog) : Prop := ∀ a b, (skel P).Conflict a b →
  (skel P).NoUnfencedWRIncident a ∧ (skel P).NoUnfencedWRIncident b
def Prog.ConflictsWRFencedEither (P : Prog) : Prop := ∀ a b, (skel P).Conflict a b →
  (skel P).NoUnfencedWRIncident a ∨ (skel P).NoUnfencedWRIncident b
```

Each core definition has proved positive and negative examples in `lean/ToyWMM/Examples.lean`
(for instance `scConsistent_example_pos/neg`, `tsoConsistent_example_pos/neg`,
`perLocSC_example_pos/neg`, `keepSameLocWR_example_pos/neg`, `ppo_example`, `fenceOrd_example`,
`wf_example_pos`), and the litmus programs and executions are in `Litmus.lean`.

### Subjects and toolchain

The Lean 4 toolchain `v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`) is the
checker; all proofs use core Lean only (no Mathlib, no Std imports), and the Lake project has
no dependencies. The papers listed as subjects are the sources of the definitions restated and of
the published results re-derived; they are related to the Lean statements only through the
`derived (modeling bridge)` claims marked below.

## Findings

Every theorem named in this section is kernel-checked and depends only on `propext`,
`Classical.choice` and `Quot.sound` (per-declaration records are in **Evidence**). Unless stated
otherwise all names are in namespace `Toy.WMM` (litmus theorems in `Toy.WMM.Litmus`). A
counterexample in a hypothesis ledger is a theorem stating that a concrete instance satisfies
all the other hypotheses (literally, or through `Wf`/`TSOConsistent`, which bundle them), violates
the named one, and violates the conclusion. Most tightness counterexamples and non-vacuity
witnesses are kernel `decide` checks on concrete executions; a few combine `decide` with proved
lemmas, and `forall_prog_exists_wf_sc_exec` is a proof for all programs.

Basis (all theorems in this section): execution (Lean kernel check).

### 1. `acyclicity-decision-procedure` (reference point: supporting infrastructure)

- **Tier:** T0 (Roy–Floyd–Warshall closure is textbook; mechanized in Isabelle/HOL by Wenzel,
  AFP 2014). **Kind:** characterization. **Depth:** shallow.
- **Statement** (`Rel.lean:18`, `Rel.lean:156`, `Rel.lean:160`; inside `namespace Rel`):
  ```lean
  variable {n : Nat}
  theorem warshall_iff_path {r : Rel n} {a b : Fin n} : warshall r n a b = true ↔ Path r a b
  theorem acyclicB_eq_true_iff {r : Rel n} : acyclicB r = true ↔ Acyclic r
  -- warshall r 0 = r;  warshall r (k+1) a b = warshall r k a b || (k < n && warshall r k a k && warshall r k k b)
  -- acyclicB r = (List.finRange n).all fun a => !warshall r n a a
  ```
- **Plain claim:** for every Boolean relation `r` on `Fin n`, `warshall r n` relates `a` to `b`
  exactly when `r` has a non-empty path from `a` to `b`, and `acyclicB r` is `true` exactly when
  no element reaches itself by a non-empty `r`-path. The `Decidable` instance for `Acyclic` is
  defined from `acyclicB`, so a `decide` verdict on `Acyclic` is a verdict about the
  `TransGen`-based definition.
- **Hypotheses:** none.
- **Non-vacuity:** `acyclic_example_pos` (the chain 0→1→2 with 0→2 is acyclic),
  `acyclic_example_neg` (a 3-cycle is not), `acyclic_example_neg_self` (a self-loop is not).
- **Prior art:** Wenzel, *Transitive closure according to Roy-Floyd-Warshall*, AFP 2014.
- **Design question:** can litmus verdicts be checked mechanically against the `Prop`-level
  consistency predicates?

### 2. `sc-implies-tso`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Statement** (`Inclusion.lean:14-15`):
  `theorem tsoConsistent_of_scConsistent {n : Nat} (X : Exec n) (h : X.SCConsistent) : X.TSOConsistent`
- **Plain claim:** every candidate execution, well formed or not, that is SC-consistent
  (`po ∪ rf ∪ co ∪ fr` acyclic) is TSO-consistent (SC per location, and
  `ppo ∪ rfe ∪ co ∪ fr ∪ fenceOrd` acyclic, where `ppo` and `fenceOrd` relate memory accesses
  only).
- **Hypothesis ledger:**

  | Hypothesis | Why needed | Tightness |
  | :--- | :--- | :--- |
  | `h : X.SCConsistent` | the premise of the inclusion | tight: `tsoConsistent_of_scConsistent_needs_sc` (MP weak outcome: neither SC nor TSO) |

- **Non-vacuity:** `nonvacuity_tsoConsistent_of_scConsistent` (the SC outcome `sbSC` of SB).
- **Prior art:** Lamport 1979 (SC); Sindhu, Frailong, Cekleov 1992 (SPARC TSO); Herding Cats
  (TOPLAS 2014) Fig. 5, Fig. 21 and Lemma 4.1; Alglave, Maranget, Sarkar, Sewell, CAV 2010 /
  FMSD 2012 (Coq-formalized framework relating SC, TSO and Power); Alglave, FMSD 2012;
  Nagarajan, Sorin, Hill, Wood, *A Primer on Memory Consistency and Cache Coherence*, 2nd ed.,
  2020.
- **Design question:** is the TSO-like target weaker than SC in this toy, so that a mapping from
  SC must add ordering rather than remove it?
- Basis: derived (modeling bridge). *If* `TSOConsistent` captures x86-TSO, every SC behaviour is
  an x86-TSO behaviour. Reasoning: `TSOConsistent` is the two-axiom form (SC per location;
  acyclicity of `ppo ∪ rfe ∪ co ∪ fr ∪ fence` with `ppo = ([RW];po;[RW]) \ (W×R)` and
  `fence = [RW];po;[F];po;[RW]`) of Herding Cats Fig. 5 and Fig. 21, whose Lemma 4.1 proves the
  Fig. 21 model equivalent to SPARC TSO via Alglave (FMSD 2012), Def. 23; the x86-TSO model
  itself is defined by Owens, Sarkar, Sewell (TPHOLs 2009). No theorem here relates
  `TSOConsistent` to the x86-TSO abstract machine or to hardware.

### 3. `sb-tso-not-sc` (counterexample)

- **Tier:** T0. **Kind:** counterexample. **Depth:** definitional.
- **Statement** (`Litmus.lean`, `Inclusion.lean`):
  ```lean
  theorem Litmus.sb_weak_tso_allowed_sc_forbidden :
      ExecOf sbProg sbWeak ∧ sbWeak.Wf ∧ sbWeak.TSOConsistent ∧ ¬ sbWeak.SCConsistent
  theorem not_forall_wf_tsoConsistent_scConsistent :
      ¬ ∀ (X : Exec 6), X.Wf → X.TSOConsistent → X.SCConsistent
  -- sbProg := [[.store 0 1, .load 1], [.store 1 2, .load 0]]; in sbWeak both loads read the initial 0
  ```
- **Plain claim:** the store-buffering weak-outcome execution `sbWeak` (both reads return the
  initial value) is a well-formed, TSO-consistent, not SC-consistent candidate execution of the
  SB program `sbProg`; hence TSO-consistency does not imply SC-consistency, even for well-formed
  6-event executions.
- **Hypotheses:** none.
- **Non-vacuity:** `Litmus.sb_weak_tso_allowed_sc_forbidden` (`sbWeak` is an execution of
  `sbProg`). **Positive control:** `tsoConsistent_of_scConsistent` (the converse inclusion
  holds).
- **Prior art:** Sewell et al., CACM 2010, Sect. 1 (SB allowed on x86); Lamport 1979.
- **Design question:** is the TSO-like target strictly weaker than SC, so that a mapping from SC
  needs fences at all?
- Basis: derived (modeling bridge). x86 allows the SB weak outcome (CACM 2010, Sect. 1); the toy
  verdict agrees. That agreement is by citation; no hardware was run.

### 4. `litmus-table`

- **Tier:** T0. **Kind:** theorem. **Depth:** definitional.
- **Statement** (`Litmus.lean`):
  ```lean
  theorem Litmus.mp_weak_tso_forbidden_sc_forbidden :
      ExecOf mpProg mpWeak ∧ mpWeak.Wf ∧ ¬ mpWeak.TSOConsistent ∧ ¬ mpWeak.SCConsistent
  theorem Litmus.lb_weak_tso_forbidden_sc_forbidden :
      ExecOf lbProg lbWeak ∧ lbWeak.Wf ∧ ¬ lbWeak.TSOConsistent ∧ ¬ lbWeak.SCConsistent
  theorem Litmus.w22_weak_tso_forbidden_sc_forbidden :
      ExecOf w22Prog w22Weak ∧ w22Weak.Wf ∧ ¬ w22Weak.TSOConsistent ∧ ¬ w22Weak.SCConsistent
  theorem Litmus.iriw_weak_tso_forbidden_sc_forbidden :
      ExecOf iriwProg iriwWeak ∧ iriwWeak.Wf ∧ ¬ iriwWeak.TSOConsistent ∧
        ¬ iriwWeak.SCConsistent
  theorem Litmus.sbFenced_weak_tso_forbidden_sc_forbidden :
      ExecOf (fenceAfterStores sbProg) sbFencedWeak ∧ sbFencedWeak.Wf ∧
        ¬ sbFencedWeak.TSOConsistent ∧ ¬ sbFencedWeak.SCConsistent
  theorem Litmus.r_weak_tso_allowed_sc_forbidden :
      ExecOf rProg rWeak ∧ rWeak.Wf ∧ rWeak.TSOConsistent ∧ ¬ rWeak.SCConsistent
  ```
  Programs (`x` is location 0, `y` is location 1): MP `[[x:=1, y:=2], [r0:=y, r1:=x]]`; LB
  `[[r0:=x, y:=1], [r1:=y, x:=2]]`; 2+2W `[[x:=1, y:=2], [y:=3, x:=4]]`; IRIW
  `[[x:=1], [y:=2], [r0:=x, r1:=y], [r2:=y, r3:=x]]`; SB+mfences
  `fenceAfterStores sbProg = [[x:=1, mfence, r0:=y], [y:=2, mfence, r1:=x]]`
  (`fenceAfterStores_sbProg`); R `[[x:=1, y:=2], [y:=3, r0:=x]]`.

  Outcomes of the executions defined in `Litmus.lean` (each is an `Exec.ofList` with the two
  initialisation writes of value 0 first; a read's value is the value of its `rf` source, and
  the final value of a location is its `co`-maximal write):

  | Execution | Read values (`rf` source) | `co` per location, initial write first | Final memory |
  | :--- | :--- | :--- | :--- |
  | `Litmus.mpWeak` | `r0 = 2` (`y:=2`), `r1 = 0` (initial `x`) | x: init, `x:=1`; y: init, `y:=2` | `x = 1`, `y = 2` |
  | `Litmus.lbWeak` | `r0 = 2` (`x:=2`), `r1 = 1` (`y:=1`) | x: init, `x:=2`; y: init, `y:=1` | `x = 2`, `y = 1` |
  | `Litmus.w22Weak` | none (no reads) | x: init, `x:=4`, `x:=1`; y: init, `y:=2`, `y:=3` | `x = 1`, `y = 3` |
  | `Litmus.iriwWeak` | `r0 = 1` (`x:=1`), `r1 = 0` (initial `y`), `r2 = 2` (`y:=2`), `r3 = 0` (initial `x`) | x: init, `x:=1`; y: init, `y:=2` | `x = 1`, `y = 2` |
  | `Litmus.sbFencedWeak` | `r0 = 0` (initial `y`), `r1 = 0` (initial `x`) | x: init, `x:=1`; y: init, `y:=2` | `x = 1`, `y = 2` |
  | `Litmus.rWeak` | `r0 = 0` (initial `x`) | x: init, `x:=1`; y: init, `y:=2`, `y:=3` | `x = 1`, `y = 3` |

  For 2+2W and R the order of the two writes to the overwritten location is what makes the
  execution non-SC: 2+2W has the cycle `x:=1 →po y:=2 →co y:=3 →po x:=4 →co x:=1`, and R has
  `x:=1 →po y:=2 →co y:=3 →po r0:=x →fr x:=1`, whose edge `y:=3 → r0:=x` is a write→read pair
  to different locations and so not in `ppo` (R is TSO-consistent). These cycles explain the
  verdicts; the theorems themselves are proved by `decide`, which does not exhibit a cycle.
- **Plain claim:** for each of MP, LB, 2+2W, IRIW and SB+mfences (`fenceAfterStores sbProg`), the
  weak-outcome candidate execution of that program defined in `Litmus.lean` (`Litmus.mpWeak`,
  `Litmus.lbWeak`, `Litmus.w22Weak`, `Litmus.iriwWeak`, `Litmus.sbFencedWeak`, with the outcomes
  in the table above) is well formed and neither TSO-consistent nor SC-consistent; for R, the
  weak-outcome execution `Litmus.rWeak` of `rProg` (`r0 = 0`, final `y = 3`) is well formed,
  TSO-consistent and not SC-consistent. (SB, n6 and SB with one fence are covered by cards 3, 5
  and 11.)
- **Hypotheses:** none.
- **Non-vacuity:** each theorem proves its execution is a well-formed candidate execution of the
  named program; `wf_example_pos` checks `Wf` for all nine litmus executions.
- **Prior art:** Sewell et al., CACM 2010 (SB allowed, Sect. 1; n6 allowed, Sect. 2.2; IRIW
  forbidden, Intel Example 8-7; MP shape forbidden, Example 8-1; LB shape forbidden, Example 8-2;
  amd5 = SB with MFENCEs forbidden, Sect. 3.2); Herding Cats Fig. 5, Fig. 21, Lemma 4.1.
- **Design question:** definition adequacy: does the toy TSO predicate give the published x86-TSO
  verdicts on standard litmus tests, so that the soundness results are about the intended model?
- Basis: derived (modeling bridge). MP, LB, IRIW and SB+mfences verdicts match those stated by
  Sewell et al. (CACM 2010); the 2+2W and R verdicts follow from the Herding Cats TSO model and
  are not quoted x86 test verdicts. No hardware was run.

### 5. `keep-same-location-wr-ppo-variant-rejected` (counterexample)

- **Tier:** T0. **Kind:** counterexample. **Depth:** definitional.
- **Statement** (`Inclusion.lean:38-39`, `Litmus.lean`):
  ```lean
  theorem tsoConsistent_of_tsoConsistentKeepSameLocWR {n : Nat} (X : Exec n)
      (h : X.TSOConsistentKeepSameLocWR) : X.TSOConsistent
  theorem Litmus.n6_weak_tso_allowed_keepSameLocWR_forbidden :
      ExecOf n6Prog n6Weak ∧ n6Weak.Wf ∧ n6Weak.TSOConsistent ∧
        ¬ n6Weak.TSOConsistentKeepSameLocWR ∧ ¬ n6Weak.SCConsistent
  -- ppoKeepSameLocWR a b := po a b && isAccess a && isAccess b && !(isWrite a && isRead b && !sameLoc a b)
  -- TSOConsistentKeepSameLocWR := PerLocSC ∧ Acyclic (ppoKeepSameLocWR ∪ rfe ∪ co ∪ fr ∪ fenceOrd)
  -- n6Prog := [[x:=1, r0:=x, r1:=y], [y:=2, x:=2]]
  -- n6Weak: r0 = 1 (rf from thread 0's own x:=1), r1 = 0 (rf from the initial y);
  --         co on x: init, x:=2 (thread 1), x:=1 (thread 0); final x = 1, y = 2
  ```
- **Plain claim:** keeping same-location write→read pairs in preserved program order (dropping
  only different-location write→read pairs) gives a model strictly stronger than
  `TSOConsistent`: every execution consistent under the variant is `TSOConsistent`, and the n6
  execution `Litmus.n6Weak` of `n6Prog` defined in `Litmus.lean` (`r0 = 1`, `r1 = 0`, final
  `x = 1`, as in the comment above), a store-forwarding outcome that x86-TSO allows, is well
  formed and `TSOConsistent` but rejected by the variant.

  Why the variant rejects it (explanation of the `decide` verdict, not a separate theorem): the
  variant keeps the same-location pair `x:=1 → r0:=x` of thread 0, giving the cycle
  `x:=1 →ppoK r0:=x →ppoK r1:=y →fr y:=2 →ppoK x:=2 →co x:=1` (`ppoK` = `ppoKeepSameLocWR`). In
  `TSOConsistent` that pair is a write→read pair, so it is not in `ppo`, and the `rf` edge
  `x:=1 → r0:=x` is internal, so it is not in `rfe`; this breaks the cycle.
- **Hypothesis ledger:**

  | Hypothesis | Why needed | Tightness |
  | :--- | :--- | :--- |
  | `h : X.TSOConsistentKeepSameLocWR` (inclusion theorem) | the premise of the inclusion | tight: `tsoConsistent_of_tsoConsistentKeepSameLocWR_needs_keep` (MP weak outcome) |

- **Non-vacuity:** `keepSameLocWR_example_pos` (the SB weak outcome is consistent under the
  variant), `Litmus.n6_weak_tso_allowed_keepSameLocWR_forbidden`. **Positive control:**
  `keepSameLocWR_example_pos`, `tsoConsistent_example_pos` (executions the variant and TSO both
  accept).
- **Prior art:** CACM 2010, Sect. 2.2 (n6 allowed); Owens, Sarkar, Sewell, TPHOLs 2009,
  paragraph "Interpreting 'not reordered with'" (memory-order edges for same-address write→read
  give a strictly stronger model that forbids test n7); Herding Cats Fig. 21.
- **Design question:** which preserved-program-order relation is right for a TSO-like target? (For
  x86-TSO: `po \ WR` over memory accesses, with same-location ordering supplied by SC per
  location.)
- Basis: derived (modeling bridge). n6 is allowed by x86-TSO and was observed on x86 hardware
  according to Sewell et al. (CACM 2010, Sect. 2.2); the toy agrees by citation.

### 6. `fence-mapping-soundness-execution`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Statement** (`Fence.lean:43-45`):
  ```lean
  theorem scConsistentErased_of_tso_of_fenceBetweenWR {n : Nat} (X : Exec n)
      (htot : X.PoTotal) (hrf : X.RfSameLoc) (hfence : X.FenceBetweenWR)
      (hloc : X.PerLocSC) (hghb : X.TsoGhbAcyclic) : X.SCConsistentErased
  ```
- **Plain claim:** if `po` is total on each thread, `rf` only relates same-location events, every
  `po`-ordered write→read pair is separated by a fence (`fenceOrd`), and the execution is
  TSO-consistent, then it is SC-consistent after erasing its fence events.
- **Hypothesis ledger:**

  | Hypothesis | Why needed | Tightness |
  | :--- | :--- | :--- |
  | `htot : X.PoTotal` | orients internal reads-from along `po` | tight: `fenceBetweenWR_needs_poTotal` |
  | `hrf : X.RfSameLoc` | lets SC per location orient internal reads-from | tight: `fenceBetweenWR_needs_rfSameLoc` |
  | `hfence : X.FenceBetweenWR` | every write→read pair restored by `fenceOrd` | tight: `fenceBetweenWR_needs_fenceBetweenWR` (SB weak outcome) |
  | `hloc : X.PerLocSC` | first TSO axiom; orients same-location internal edges | tight: `fenceBetweenWR_needs_perLocSC` |
  | `hghb : X.TsoGhbAcyclic` | second TSO axiom | tight: `fenceBetweenWR_needs_tsoGhbAcyclic` (SB+mfences weak outcome) |

- **Non-vacuity:** `nonvacuity_scConsistentErased_of_tso_of_fenceBetweenWR` (the SC outcome of
  SB+mfences).
- **Prior art:** CACM 2010, Sect. 3.2 ("In x86-TSO adding MFENCE between every instruction would
  clearly suffice to regain sequential consistency"); Herding Cats Fig. 5, Fig. 21; Podkopaev,
  Lahav, Vafeiadis, POPL 2019, Coq development `weakmemory/imm` at commit
  `4ca191b072df081dd3a6d9aa755959dc901b1bd0` (`src/hardware/TSO.v`, lines 48–50, defines the
  same `ppo` and `fence`; `src/hardware/immToTSO.v`, lines 897–898, Lemma `IMM_consistent`, assumes
  `SCF : [W∩Sc];sb;[R∩Sc] ⊆ sb;[MFENCE];sb`); Alglave et al., CAV 2010 / FMSD 2012.
- **Design question:** which condition makes a TSO-consistent execution SC (after erasing
  fences)? Here: a fence between every `po`-ordered write→read pair, per-thread-total `po` and
  location-respecting `rf`.
- Basis: derived (modeling bridge). For x86 programs whose behaviour is captured by
  `TSOConsistent`, an `MFENCE` between every store and later load restores SC, as CACM 2010
  Sect. 3.2 states informally; the toy theorem is the axiomatic counterpart.

### 7. `fence-mapping-soundness-program`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Statement** (`Fence.lean:64-66`):
  ```lean
  theorem scConsistentErased_of_tso_fenceAfterStores (P : Prog) {n : Nat} (X : Exec n)
      (hX : ExecOf (fenceAfterStores P) X) (hrf : X.RfSameLoc) (hloc : X.PerLocSC)
      (hghb : X.TsoGhbAcyclic) : X.SCConsistentErased
  ```
- **Plain claim:** for every straight-line program `P`, every candidate execution of
  `fenceAfterStores P` (an `mfence` inserted immediately after every store) whose `rf` relates
  same-location events and which is TSO-consistent is SC-consistent after erasing its fence
  events.
- **Hypothesis ledger:**

  | Hypothesis | Why needed | Tightness |
  | :--- | :--- | :--- |
  | `hX : ExecOf (fenceAfterStores P) X` | `X` is an execution of the compiled program | tight: `fenceAfterStores_needs_execOf` (SB weak outcome of the unfenced program) |
  | `hrf : X.RfSameLoc` | `rf` respects locations | tight: `fenceAfterStores_needs_rfSameLoc` |
  | `hloc : X.PerLocSC` | first TSO axiom | tight: `fenceAfterStores_needs_perLocSC` |
  | `hghb : X.TsoGhbAcyclic` | second TSO axiom | tight: `fenceAfterStores_needs_tsoGhbAcyclic` |

- **Non-vacuity:** `nonvacuity_scConsistentErased_of_tso_fenceAfterStores`
  (`fenceAfterStores sbProg` and its SC execution `sbFencedSC`).
- **Prior art:** CACM 2010, Sect. 3.2; Batty, Owens, Sarkar, Sewell, Weber, POPL 2011, Sect. 5
  (correctness of compiling C++11 primitives, including SC atomics, to x86-TSO, in Isabelle/HOL);
  `weakmemory/imm` as in card 6.
- **Design question:** is inserting an `mfence` after every store a sound mapping from SC to TSO
  at the level of target executions?
- Basis: derived (modeling bridge). `fenceAfterStores` mirrors the x86 implementation of SC
  stores as a store followed by `MFENCE` (with plain loads), whose correctness for C++11 SC
  atomics Batty et al. (POPL 2011, Sect. 5) prove for their x86-TSO model; the toy theorem is the
  axiomatic counterpart for straight-line programs in which every access is fenced this way, and
  says nothing about programs mixing SC and non-SC accesses.

### 8. `fence-mapping-source-execution`

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow (the SC argument is card 7 plus card 9;
  the new content is the construction of the order-preserving source-event map and the transfer
  of `ExecOf` and each `Wf` conjunct along it).
- **Statement** (`SourceExec.lean`):
  ```lean
  theorem exists_sc_source_execution_of_tso_fenceAfterStores (P : Prog) {n : Nat} (X : Exec n)
      (hX : ExecOf (fenceAfterStores P) X) (hwf : X.RfCoWf) (htso : X.TSOConsistent) :
      ∃ f : Fin (layout P).length → Fin n,
        (∀ a b, a < b ↔ f a < f b) ∧ (∀ e, (X.ev e).isAccess = true → ∃ a, f a = e) ∧
        ExecOf P (X.comap f) ∧ (X.comap f).Wf ∧ (X.comap f).SCConsistent
  -- RfCoWf := RfSameLoc ∧ RfKinds ∧ RfSameVal ∧ RfTotal ∧ RfFunctional ∧
  --           CoKinds ∧ CoTrans ∧ CoTotal ∧ CoInitFirst
  ```
- **Plain claim:** for every straight-line program `P` and every TSO-consistent candidate
  execution `X` of `fenceAfterStores P` whose `rf` and `co` are well formed (`RfCoWf`: `rf` from
  writes to reads of the same location and value, total and functional; `co` between
  same-location writes, transitive, total, with initialisation writes first), there is an
  order-preserving map `f` from the events of `P` to the events of `X` that hits every memory
  access of `X` (so it misses only fence events) such that `X.comap f` (the events, `po`, `rf`
  and `co` of `X` read through `f`) is a well-formed SC-consistent candidate execution of `P`.
- **Proof outline.** `numLocs (fenceAfterStores P) = numLocs P` because inserted fences have
  location `0`. `SourceMap.validEmbed_layout` builds, by induction over threads and
  instructions, a strictly increasing index list embedding `layout P` into
  `layout (fenceAfterStores P)` event-for-event and hitting every memory access; it becomes `f`.
  `ExecOf P (X.comap f)` and each conjunct of `Wf` transfer along `f` (`CoIrrefl` from
  `PerLocSC`; `RfTotal` uses that `f` hits every write). SC of `X.comap f` follows from card 7,
  card 9 and the fact that `comap` maps `scRel`-paths to `scRel`-paths.
- **Hypothesis ledger:**

  | Hypothesis | Why needed | Tightness |
  | :--- | :--- | :--- |
  | `hX : ExecOf (fenceAfterStores P) X` | `X` is an execution of the compiled program | tight: `sourceExec_needs_execOf` (SB weak outcome of the unfenced program) |
  | `hwf : X.RfCoWf` | well-formedness of `rf` and `co`: every `Wf` conjunct except the four `po` conditions (implied by `hX`) and `CoIrrefl` (implied by SC per location); each conjunct is inherited by the corresponding conjunct of `(X.comap f).Wf` | tight as a bundle: `sourceExec_needs_rfCoWf` (a read with no `rf` source, i.e. the `RfTotal` conjunct fails); see the note below |
  | `htso : X.TSOConsistent` | the target model | tight: `sourceExec_needs_tso` (SB+mfences weak outcome) |

  *Note on `RfCoWf`.* The conjuncts are not independent once `PerLocSC` holds: `RfFunctional`
  follows
  from `RfSameLoc`, `RfKinds` and `CoTotal` (`Exec.rfFunctional_of_perLocSC`), and `CoTrans`
  follows from `CoKinds` and `CoTotal` (`Exec.coTrans_of_perLocSC`). The counterexample tests the
  bundle only through `RfTotal`; necessity of the individual conjuncts is not claimed. `RfCoWf`
  also constrains edges at inserted fences, which `X.comap f` never sees:
  `storeFenceExtraRfOnInserted_check` exhibits an execution of `fenceAfterStores [[.store 0 1]]`
  with an `rf` edge into the inserted fence that violates `RfCoWf` while the conclusion still
  holds.
- **Non-vacuity:** `nonvacuity_exists_sc_source_execution_of_tso_fenceAfterStores`
  (`fenceAfterStores sbProg` with its SC execution `sbFencedSC` satisfies all hypotheses) and
  `sbFencedSC_source_execution` (the conclusion with the explicit map `sbSrcIdx`, indices
  `0, 1, 2, 4, 5, 7`; the source execution is SB's SC outcome).
- **Prior art:** CACM 2010, Sect. 3.2; Batty et al., POPL 2011, Sect. 5 (lifting x86-TSO
  executions back to consistent C++11 executions); `weakmemory/imm` as in card 6.
- **Design question:** which correctness statement does a compilation mapping from SC to a
  TSO-like target need? Here: every target execution allowed by TSO arises from a source
  execution allowed by SC with the same communication (`rf`, `co`) and read values.
- Basis: derived (modeling bridge). This is the toy analogue of the compilation-correctness
  statements of Batty et al. (POPL 2011) and `weakmemory/imm`, restricted to straight-line
  programs and the all-stores fencing mapping.

### 9. `fence-erasure` (reference point: supporting infrastructure)

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Statement** (`Fence.lean:335-337`):
  ```lean
  theorem scConsistent_of_scConsistentErased {n : Nat} (X : Exec n)
      (hirr : X.PoIrrefl) (htrans : X.PoTrans) (hrfk : X.RfKinds) (hcok : X.CoKinds)
      (h : X.SCConsistentErased) : X.SCConsistent
  ```
- **Plain claim:** if `po` is irreflexive and transitive, `rf` goes from writes to reads, and `co`
  relates same-location writes, then SC-consistency after erasing fence events implies
  SC-consistency with the fence events present. The converse holds unconditionally
  (`scConsistentErased_of_scConsistent`).
- **Hypothesis ledger:**

  | Hypothesis | Why needed | Tightness |
  | :--- | :--- | :--- |
  | `hirr : X.PoIrrefl` | excludes `po` self-loops on fences | tight: `scConsistent_of_scConsistentErased_needs_poIrrefl` |
  | `htrans : X.PoTrans` | shortens cycles through fences | tight: `scConsistent_of_scConsistentErased_needs_poTrans` |
  | `hrfk : X.RfKinds` | no `rf` edge touches a fence | tight: `scConsistent_of_scConsistentErased_needs_rfKinds` |
  | `hcok : X.CoKinds` | no `co` edge touches a fence | tight: `scConsistent_of_scConsistentErased_needs_coKinds` |
  | `h : X.SCConsistentErased` | the premise | tight: `scConsistent_of_scConsistentErased_needs_scErased` |

  The proof uses only that `rf` and `co` edges join memory accesses.
- **Non-vacuity:** `nonvacuity_scConsistent_of_scConsistentErased` (the SC outcome of
  SB+mfences).
- **Prior art:** Owens, Sarkar, Sewell, TPHOLs 2009, axiomatic model: "There is no need to include
  fence events themselves in the memory ordering."
- **Design question:** is "SC after erasing fences" the same correctness target as "SC" for
  compiled executions?

### 10. `shared-location-fencing-soundness`

- **Tier:** T1 (known informally from delay-set analysis, Shasha and Snir 1988, and used by
  escape-analysis-based fence omission, Sura et al. 2005; no mechanization of this execution-level
  statement was found in the works cited, a search limited to them and the Coq/HOL4 developments
  listed; Vafeiadis and Zappa Nardelli, SAS 2011, mechanize a different fence optimisation).
  **Kind:** theorem. **Depth:** substantive.
- **Statement** (`Fence.lean:91-95`; the corollary at `Fence.lean:321-325`):
  ```lean
  theorem scConsistentErased_of_tso_of_fenceBetweenBothSharedWR {n : Nat} (X : Exec n)
      (hptrans : X.PoTrans) (hpth : X.PoWithinThread) (htot : X.PoTotal)
      (hrfl : X.RfSameLoc) (hcol : X.CoSameLoc)
      (hfence : X.FenceBetweenBothSharedWR) (hloc : X.PerLocSC) (hghb : X.TsoGhbAcyclic) :
      X.SCConsistentErased
  theorem scConsistentErased_of_tso_of_fenceBetweenSharedWR {n : Nat} (X : Exec n)
      (hptrans : X.PoTrans) (hpth : X.PoWithinThread) (htot : X.PoTotal)
      (hrfl : X.RfSameLoc) (hcok : X.CoKinds)
      (hfence : X.FenceBetweenSharedWR) (hloc : X.PerLocSC) (hghb : X.TsoGhbAcyclic) :
      X.SCConsistentErased
  ```
- **Plain claim:** fencing only the `po`-ordered write→read pairs whose write and read are both
  to locations accessed (excluding initialisation writes) by two or more threads suffices: if
  `po` is transitive, within threads and total on each thread, `rf` and `co` only relate events at
  the same location, those pairs are separated by a fence, and the execution is TSO-consistent,
  then it is SC-consistent after erasing fences. The form that fences every pair whose write's
  location is shared (`FenceBetweenSharedWR`, with `CoKinds`) is a corollary.
- **Hypothesis ledger.** The first eight rows are the hypotheses of the **primary theorem**
  `scConsistentErased_of_tso_of_fenceBetweenBothSharedWR`. The **corollary**
  `scConsistentErased_of_tso_of_fenceBetweenSharedWR` strengthens `CoSameLoc` to `CoKinds` and
  `FenceBetweenBothSharedWR` to `FenceBetweenSharedWR`; both strengthenings are strict
  (`coBetweenReadsSameLoc_separates_coSameLoc_from_coKinds` satisfies `FenceBetweenSharedWR`,
  hence `FenceBetweenBothSharedWR`, and the other premises of the primary theorem, but not
  `CoKinds`; `sharedWLocalR`, in
  `nonvacuity_scConsistentErased_of_tso_of_fenceBetweenBothSharedWR`, satisfies
  `FenceBetweenBothSharedWR` but not `FenceBetweenSharedWR`). The last eight rows show that
  each corollary hypothesis is nevertheless needed (same executions as the primary rows).

  | Hypothesis | Why needed | Tightness |
  | :--- | :--- | :--- |
  | primary `hptrans : X.PoTrans` | shortens cycles through thread-local accesses | tight: `fenceBetweenBothSharedWR_needs_poTrans` |
  | primary `hpth : X.PoWithinThread` | `po` never enters an initialisation write | tight: `fenceBetweenBothSharedWR_needs_poWithinThread` |
  | primary `htot : X.PoTotal` | orients same-thread communication along `po` | tight: `fenceBetweenBothSharedWR_needs_poTotal` |
  | primary `hrfl : X.RfSameLoc` | communication stays on one location | tight: `fenceBetweenBothSharedWR_needs_rfSameLoc` |
  | primary `hcol : X.CoSameLoc` | `co` stays on one location | tight: `fenceBetweenBothSharedWR_needs_coSameLoc` |
  | primary `hfence : X.FenceBetweenBothSharedWR` | write→read pairs between shared locations fenced | tight: `fenceBetweenBothSharedWR_needs_fenceBetweenBothSharedWR`, `sbOneFence_execution_tso_not_scErased` |
  | primary `hloc : X.PerLocSC` | first TSO axiom | tight: `fenceBetweenBothSharedWR_needs_perLocSC` |
  | primary `hghb : X.TsoGhbAcyclic` | second TSO axiom | tight: `fenceBetweenBothSharedWR_needs_tsoGhbAcyclic` |
  | corollary `hptrans : X.PoTrans` | as above | tight: `fenceBetweenSharedWR_needs_poTrans` |
  | corollary `hpth : X.PoWithinThread` | as above | tight: `fenceBetweenSharedWR_needs_poWithinThread` |
  | corollary `htot : X.PoTotal` | as above | tight: `fenceBetweenSharedWR_needs_poTotal` |
  | corollary `hrfl : X.RfSameLoc` | as above | tight: `fenceBetweenSharedWR_needs_rfSameLoc` |
  | corollary `hcok : X.CoKinds` | `co` joins same-location writes (stronger than `CoSameLoc`) | tight: `fenceBetweenSharedWR_needs_coKinds` |
  | corollary `hfence : X.FenceBetweenSharedWR` | pairs whose write is shared fenced (stronger than `FenceBetweenBothSharedWR`) | tight: `fenceBetweenSharedWR_needs_fenceBetweenSharedWR` |
  | corollary `hloc : X.PerLocSC` | first TSO axiom | tight: `fenceBetweenSharedWR_needs_perLocSC` |
  | corollary `hghb : X.TsoGhbAcyclic` | second TSO axiom | tight: `fenceBetweenSharedWR_needs_tsoGhbAcyclic` |

- **Non-vacuity:** `nonvacuity_scConsistentErased_of_tso_of_fenceBetweenBothSharedWR`: `localWR`
  (`T0: z := 1; r := x ‖ T1: x := 2`, `z` thread-local) fails `FenceBetweenWR`, and
  `sharedWLocalR` (`T0: x := 1; r := z ‖ T1: x := 2`) fails `FenceBetweenSharedWR`; both satisfy
  every hypothesis of the primary theorem.
- **Prior art:** Shasha and Snir, TOPLAS 1988 (delay sets: only program-order pairs on critical
  cycles need delays); Sura et al., PPoPP 2005 (escape analysis and delay-set analysis to omit
  fences on thread-local accesses); Alglave, Kroening, Nimal, Poetzl, CAV 2014 / TOPLAS 2017;
  Vafeiadis and Zappa Nardelli, SAS 2011 (Coq-verified fence elimination on x86-TSO, a
  different optimisation); Owens, ECOOP 2010 (Sect. 4, Def. 4 memorySC; Sect. 6, Def. 6 and
  Theorem 1, triangular-race freedom; Fig. 6; Appendix A, Lemma 4, mechanically verified in
  HOL4).
- **Design question:** may a compiler omit fences after accesses to thread-local locations when
  targeting a TSO-like model, and which execution-level sharing condition makes that sound?
- Basis: derived (modeling bridge). The theorem supports, for x86 programs captured by the toy,
  omitting fences between write→read pairs where the write or the read is to a location that no
  other thread accesses *anywhere in the execution*; turning this into a compiler rule needs a
  sound static sharing analysis, which is not formalized here.

### 11. `partial-fencing-unsound` (counterexample)

- **Tier:** T0. **Kind:** counterexample. **Depth:** definitional.
- **Statement** (`Tightness.lean:210-215`):
  ```lean
  theorem sbOneFence_execution_tso_not_scErased :
      ExecOf sbOneFenceProg sbOneFenceWeak ∧ sbOneFenceWeak.Wf ∧
        sbOneFenceWeak.TSOConsistent ∧ ¬ sbOneFenceWeak.SCConsistentErased ∧
        sbOneFenceWeak.fenceOrd ⟨2, by decide⟩ ⟨4, by decide⟩ = true ∧
        sbOneFenceWeak.fenceOrd ⟨5, by decide⟩ ⟨6, by decide⟩ = false ∧
        ¬ sbOneFenceWeak.FenceBetweenSharedWR ∧ ¬ sbOneFenceWeak.FenceBetweenBothSharedWR
  -- sbOneFenceProg := [[.store 0 1, .mfence, .load 1], [.store 1 2, .load 0]]
  ```
- **Plain claim:** fencing only some shared write→read pairs is unsound: the SB program with an
  `mfence` after thread 0's store only has a well-formed TSO-consistent execution that is not
  SC-consistent even after fence erasure; in it thread 0's write→read pair is fenced and thread
  1's is not, so the execution fails `FenceBetweenSharedWR` and `FenceBetweenBothSharedWR`.
- **Hypotheses:** none.
- **Non-vacuity:** the theorem itself (`sbOneFenceWeak` is an execution of `sbOneFenceProg`).
  **Positive control:** `Litmus.sbFenced_weak_tso_forbidden_sc_forbidden` (with fences on both
  sides the weak outcome is not TSO-consistent) and
  `scConsistentErased_of_tso_of_fenceBetweenBothSharedWR`.
- **Prior art:** Herding Cats, discussion of `sb+ffences`: "We need a full fence on each side to
  prevent the reads b and d from reading the initial state"; Shasha and Snir 1988.
- **Design question:** must every shared write→read pair be fenced, or can a mapping fence only
  one side of a communication pattern?
- Basis: derived (modeling bridge). For x86, the claim that one `MFENCE` in SB does not forbid
  the weak outcome rests on the Herding Cats remark about their TSO model (a full fence is needed
  on each side); no hardware was run and no x86 test verdict for this program is quoted.

### 12. `straight-line-race-freedom-collapse`

- **Tier:** T1 (that a program without synchronization operations is data-race free only if it
  has no conflicting accesses is folklore of the DRF literature; Adve and Hill 1990 identify
  synchronization explicitly). **Kind:** characterization. **Depth:** substantive.
- **Statement** (`StraightLine.lean`):
  ```lean
  theorem exists_sc_execution_hb_unordered_of_conflict (P : Prog)
      {a b : Fin (layout P).length} (hc : (skel P).Conflict a b) :
      ∃ Y : Exec (layout P).length,
        ExecOf P Y ∧ Y.Wf ∧ Y.SCConsistent ∧ Y.Conflict a b ∧ ¬ Y.HB a b ∧ ¬ Y.HB b a
  theorem hbRaceFree_sc_executions_iff_noConflict (P : Prog) :
      (∀ (m : Nat) (Y : Exec m), ExecOf P Y → Y.Wf → Y.SCConsistent →
          ∀ a b, Y.Conflict a b → Y.HB a b ∨ Y.HB b a) ↔
        (∀ a b, ¬ (skel P).Conflict a b)
  theorem raceFree_sc_executions_iff_conflictsWRFenced (P : Prog) :
      (∀ (m : Nat) (Y : Exec m), ExecOf P Y → Y.Wf → Y.SCConsistent → Y.RaceFree) ↔
        P.ConflictsWRFenced
  theorem raceFreeEither_sc_executions_iff_conflictsWRFencedEither (P : Prog) :
      (∀ (m : Nat) (Y : Exec m), ExecOf P Y → Y.Wf → Y.SCConsistent → Y.RaceFreeEither) ↔
        P.ConflictsWRFencedEither
  ```
- **Plain claim:** for every straight-line program `P`: (i) every conflicting pair of accesses is
  unordered by `hb = (po ∪ rf)⁺` in some well-formed SC-consistent execution of `P`; hence (ii)
  every well-formed SC-consistent execution of `P` orders all its conflicting pairs by `hb` if
  and only if `P` has no conflicting pair at all; (iii) every well-formed SC-consistent execution
  of `P` is `RaceFree` (conflicting accesses `hb`-ordered or both satisfying
  `NoUnfencedWRIncident`) if and only if the static condition `P.ConflictsWRFenced` holds; and
  (iv) every such execution is `RaceFreeEither` (one side suffices) if and only if
  `P.ConflictsWRFencedEither` holds.
- **Hypothesis ledger:** the three equivalences have no hypotheses.

  | Hypothesis | Why needed | Tightness |
  | :--- | :--- | :--- |
  | `hc : (skel P).Conflict a b` (of `exists_sc_execution_hb_unordered_of_conflict`) | the pair must be a conflicting pair of accesses of `P` | tight: `exists_sc_execution_hb_unordered_needs_conflict` (in `loadStoreSameProg`, `r := x; x := 1` in one thread, the load and the store do not conflict and are `po`-ordered, hence `hb`-ordered, in every execution) |

- **Non-vacuity:** `nonvacuity_straightLine_race_characterizations` (`loadStoreProg` has no
  conflicts, where `loadStoreProg := [[.load 1, .store 0 1]]` is the one-thread program
  `r0 := y; x := 1`; `sbProg` has some; `fenceAfterStores sbProg` satisfies `ConflictsWRFenced`;
  `sbProg` fails even `ConflictsWRFencedEither`; `sbOneFenceProg` satisfies the either-side but
  not the both-sides condition, so each static condition is exhibited both holding and failing), and
  `forall_prog_exists_wf_sc_exec` (every program, including `[]` and `[[]]`, has a well-formed
  SC-consistent execution, its sequential execution in layout order, so the universal
  quantifiers over well-formed SC executions never range over an empty set).
- **Prior art:** Adve and Hill, ISCA 1990 (DRF0: SC for data-race-free programs whose
  synchronization operations are explicitly identified); Owens, ECOOP 2010 (Sect. 5, Def. 5,
  data races on SC execution prefixes, "a locked write and unlocked read can form a data race",
  and Corollary 1, DRF theorem; Sect. 6, Def. 6 and Theorem 1, triangular-race freedom).
- **Design question:** can a happens-before data-race-freedom contract serve as the source-level
  correctness criterion for compiling straight-line toy programs to TSO? (No: on such programs it
  degenerates to a static condition on fence placement; a meaningful DRF-SC statement needs
  control flow or synchronization operations.)

### 13. `static-both-sides-fencing-sc-on-tso`

- **Tier:** T1 (corollary of cards 10 and 9; the static condition is the race-freedom premise of
  card 12). **Kind:** theorem. **Depth:** shallow.
- **Statement** (`StraightLine.lean`):
  ```lean
  theorem fenceBetweenSharedWR_of_conflictsWRFenced (P : Prog) (h : P.ConflictsWRFenced)
      {n : Nat} (X : Exec n) (hX : ExecOf P X) : X.FenceBetweenSharedWR
  theorem scConsistent_of_tso_of_conflictsWRFenced (P : Prog) (h : P.ConflictsWRFenced)
      {n : Nat} (X : Exec n) (hX : ExecOf P X) (hrfl : X.RfSameLoc) (hrfk : X.RfKinds)
      (hcok : X.CoKinds) (htso : X.TSOConsistent) : X.SCConsistent
  ```
- **Plain claim:** if every conflicting pair of accesses of a straight-line program `P` has both
  accesses satisfying `NoUnfencedWRIncident` (`P.ConflictsWRFenced`; equivalently, every
  well-formed SC execution of `P` is `RaceFree`), then every candidate execution of `P` fences
  every `po`-ordered write→read pair whose write is to a shared location, and every candidate
  execution of `P` whose `rf` goes from writes to reads of the same location, whose `co` relates
  same-location writes, and which is TSO-consistent, is SC-consistent.
- **Hypothesis ledger:**

  | Hypothesis | Why needed | Tightness |
  | :--- | :--- | :--- |
  | `h : P.ConflictsWRFenced` | the static race-freedom condition | tight: `scConsistent_of_tso_of_conflictsWRFenced_needs_conflictsWRFenced` (SB) |
  | `hX : ExecOf P X` | `X` is an execution of `P` | tight: `scConsistent_of_tso_of_conflictsWRFenced_needs_execOf` |
  | `hrfl : X.RfSameLoc` | communication stays on one location | tight: `scConsistent_of_tso_of_conflictsWRFenced_needs_rfSameLoc` |
  | `hrfk : X.RfKinds` | `rf` joins memory accesses (fence erasure) | tight: `scConsistent_of_tso_of_conflictsWRFenced_needs_rfKinds` |
  | `hcok : X.CoKinds` | `co` joins same-location writes | tight: `scConsistent_of_tso_of_conflictsWRFenced_needs_coKinds` |
  | `htso : X.TSOConsistent` | the target model | tight: `scConsistent_of_tso_of_conflictsWRFenced_needs_tso` |
  | `h : P.ConflictsWRFenced` (of `fenceBetweenSharedWR_of_conflictsWRFenced`) | the static condition | tight: `fenceBetweenSharedWR_of_conflictsWRFenced_needs_conflictsWRFenced` |
  | `hX : ExecOf P X` (of `fenceBetweenSharedWR_of_conflictsWRFenced`) | `X` is an execution of `P` | tight: `fenceBetweenSharedWR_of_conflictsWRFenced_needs_execOf` |

- **Non-vacuity:** `nonvacuity_scConsistent_of_tso_of_conflictsWRFenced`
  (`fenceAfterStores sbProg` with its SC execution `sbFencedSC`).
- **Prior art:** Owens, ECOOP 2010 (as in card 10); Shasha and Snir 1988.
- **Design question:** how must a fence-based race exemption treat the two accesses of a
  conflicting pair for SC to hold on TSO? (Requiring both sides suffices; one side does not, see
  card 14.)

### 14. `drf-either-fenced-variant-rejected` (counterexample)

- **Tier:** T0. **Kind:** counterexample. **Depth:** shallow.
- **Statement** (`Tightness.lean:351-357`):
  ```lean
  theorem conflictsWRFencedEither_does_not_imply_sc :
      sbOneFenceProg.ConflictsWRFencedEither ∧
        (∀ (m : Nat) (Y : Exec m), ExecOf sbOneFenceProg Y → Y.Wf → Y.SCConsistent →
          Y.RaceFreeEither) ∧
        sbOneFenceWeak.fenceOrd ⟨2, by decide⟩ ⟨4, by decide⟩ = true ∧
        ExecOf sbOneFenceProg sbOneFenceWeak ∧ sbOneFenceWeak.Wf ∧
        sbOneFenceWeak.TSOConsistent ∧ ¬ sbOneFenceWeak.SCConsistent
  ```
- **Plain claim:** exempting a conflicting pair when either (rather than both) of its accesses
  satisfies `NoUnfencedWRIncident` does not give SC on TSO: in SB with an `mfence` after thread
  0's store (`sbOneFenceProg`), thread 0's write and read are separated by an actual fence, every
  conflicting pair has a side satisfying `NoUnfencedWRIncident`, and hence every well-formed SC
  execution is `RaceFreeEither`; yet the program has a well-formed TSO-consistent execution that
  is not SC-consistent.
- **Hypotheses:** none.
- **Non-vacuity:** the theorem itself. **Positive control:**
  `scConsistent_of_tso_of_conflictsWRFenced` (with the both-sides condition SC does follow).
- **Prior art:** Herding Cats (`sb+ffences`: a full fence is needed on each side); Owens, ECOOP
  2010, Sect. 5, Def. 5 (a locked write and an unlocked read can race) and Sect. 6 (triangular
  races); Batty et al., POPL 2011.
- **Design question:** how must a fence-based race exemption treat the two accesses of a
  conflicting pair for SC to hold on TSO? (One side is not enough.)

## Boundaries

### Non-claims

**Package-wide.**

- **Toy model only.** Finite candidate executions of straight-line programs, one access size, no
  read-modify-write or locked instructions, no registers, dependencies or control flow, a single
  full fence. Nothing is claimed about C11/RC11, Java, Rust atomics, out-of-thin-air behaviour,
  mixed-size accesses, ARM, POWER, RISC-V, or compiler optimisations other than fence insertion.
- **TSO is a modeling bridge.** That `TSOConsistent` captures x86-TSO is derived, not a theorem:
  it is the two-axiom form (SC per location; acyclic(`ppo ∪ rfe ∪ co ∪ fr ∪ fence`) with
  `ppo = ([RW];po;[RW]) \ (W×R)` and `fence = [RW];po;[F];po;[RW]`) of Alglave, Maranget and
  Tautschnig (TOPLAS 2014, Fig. 5 and Fig. 21), whose Lemma 4.1 proves equivalence to SPARC TSO
  via Alglave (FMSD 2012), Def. 23. No theorem here relates it to the x86-TSO abstract machine or
  to hardware, and no hardware was run.
- **No DRF-SC theorem.** No Adve–Hill-style or Owens-style data-race-freedom theorem is stated
  or proved; on straight-line programs the `hb`-based contract degenerates (card 12).
- **No completeness, minimality or optimality.** No result shows that every SC execution of `P`
  is matched by a TSO-consistent execution of `fenceAfterStores P`, that fencing after every
  store is minimal, or that any fence placement is optimal.
- **No partial or mixed mappings.** `fenceAfterStores` fences every store; nothing justifies
  mappings that fence only some stores (such as C11/Rust `SeqCst`-to-x86, where relaxed or
  non-atomic stores stay unfenced), fence-before-load mappings, or `LOCK XCHG` stores.
- **Litmus verdicts are about the executions defined in `Litmus.lean`.** That such an execution
  is the only well-formed candidate with its stated outcome (card 4 lists the read values and
  final writes) is argued in prose, not proved.

**Per result** (the first two package-wide items above are also attached to every relevant card
in `results.json`):

- **1. `acyclicity-decision-procedure`**
  - Supporting infrastructure: a reference point used to check litmus verdicts by kernel evaluation; it says nothing about memory models.
  - Says nothing about efficiency beyond kernel evaluation of small instances (n ≤ 8 is used here).
  - `Acyclic` is defined via `Relation.TransGen`; no claim about other cycle notions (e.g. simple cycles of bounded length).

- **2. `sc-implies-tso`**
  - This is the inclusion (permissiveness) direction: every SC-consistent execution is TSO-consistent. It does not justify running SC programs unfenced on TSO; that would need the converse, which fails (`sb-tso-not-sc`).
  - No well-formedness is assumed. The premise is SC-consistency with fence events present; no claim is made with `SCConsistentErased` as premise.
  - Fence events are not endpoints of `ppo` or `fenceOrd`, so fence events (and, e.g., a `po` self-loop on a fence) never lie on a TSO cycle.

- **3. `sb-tso-not-sc`**
  - Shows strictness on one execution; does not characterize the gap between SC and TSO.
  - Escape hatch: fencing every `po`-ordered write→read pair (`fence-mapping-soundness-execution`), or every such pair between shared locations (`shared-location-fencing-soundness`), makes TSO-consistent executions satisfying those theorems' other hypotheses SC-consistent after fence erasure.

- **4. `litmus-table`**
  - Verdicts concern the specific candidate execution of each program defined in `Litmus.lean` (`mpWeak`, `lbWeak`, `w22Weak`, `iriwWeak`, `sbFencedWeak`, `rWeak`), with the outcomes listed in card 4. That it is the only well-formed candidate execution with that outcome (distinct written values fix `rf`; the final state fixes `co`) is argued in prose, not proved, so no outcome-level statement such as 'TSO forbids the outcome' is a theorem here.
  - Agreement with x86 is by citation (derived, modeling bridge): MP (Intel Example 8-1 shape), LB (Example 8-2 shape), IRIW (Example 8-7) and SB+mfences (amd5) are verdicts stated by Sewell et al. (CACM 2010); the 2+2W and R verdicts follow from the Herding Cats TSO model and are not quoted x86 test verdicts. No hardware was run.
  - The SB+mfences verdict depends on `fenceOrd`: the execution has no cycle in `ppo ∪ rfe ∪ co ∪ fr` (`sbFencedWeak_needs_fenceOrd`).

- **5. `keep-same-location-wr-ppo-variant-rejected`**
  - Shows the variant is too strong on one test; does not classify all differences between the two models.
  - That `TSOConsistent` captures x86-TSO, and that n6 is allowed by x86-TSO and observed on x86 hardware, is a modeling bridge (derived) from Sewell et al. (CACM 2010, Sect. 2.2) and Owens, Sarkar and Sewell (TPHOLs 2009); no theorem here relates `TSOConsistent` to the x86-TSO abstract machine or to hardware.
  - Escape hatch: the separating execution uses store forwarding (a read of the thread's own buffered write, an internal `rf` edge) followed by a read of another location; no claim is made either way about executions without such a pattern.

- **6. `fence-mapping-soundness-execution`**
  - Conclusion is SC after fence erasure (restriction to memory accesses); for SC with fences present combine with `fence-erasure`; for a statement about source executions see `fence-mapping-source-execution`.
  - No claim that the fences are necessary pair by pair (see `shared-location-fencing-soundness` and `partial-fencing-unsound`).
  - Does not show the converse or any optimality of fence placement.

- **7. `fence-mapping-soundness-program`**
  - The conclusion is about the target execution (restriction to non-fence events); the source-execution statement is `fence-mapping-source-execution`.
  - Does not show that fencing after every store is minimal or unique: alternative mappings such as fencing before every load, or implementing stores with locked instructions (e.g., x86 `LOCK XCHG`), are not modelled or compared.
  - Does not prove completeness (backward preservation): that every SC execution of `P` gives rise to a TSO-consistent execution of `fenceAfterStores P` with the same outcome is not proved.
  - Does not justify partial or mixed-ordering mappings (such as C11/Rust `SeqCst`-to-x86, where only `SeqCst` stores receive `MFENCE` while relaxed or non-atomic stores remain unfenced): `fenceAfterStores` fences every store in the program.
  - Programs have no registers, control flow, or dependencies; reads may return any value permitted by `rf`.

- **8. `fence-mapping-source-execution`**
  - Outcome agreement is by construction: the read values, `rf` and `co` of `X.comap f` are those of `X` at the images of `f`; no separate observational-equivalence theorem is stated.
  - The map `f` is not claimed to be unique (when `P` has its own `mfence` next to an inserted one, either fence event may be chosen).
  - Does not prove completeness: that every SC execution of `P` is matched by a TSO-consistent execution of `fenceAfterStores P` is not proved.
  - `RfCoWf` is not claimed to be the weakest premise: two of its conjuncts are redundant given `PerLocSC` (`Exec.rfFunctional_of_perLocSC`, `Exec.coTrans_of_perLocSC`), and it also constrains `rf` and `co` at the inserted fences, which the source execution never sees (`storeFenceExtraRfOnInserted_check`: an `rf` edge into an inserted fence violates `RfCoWf` while the conclusion still holds). Only the necessity of the bundle is shown, through `RfTotal` (`sourceExec_needs_rfCoWf`).
  - Does not justify partial or mixed-ordering mappings: `fenceAfterStores` fences every store in the program.

- **9. `fence-erasure`**
  - Supporting infrastructure: relates the two SC targets on the same execution; the converse holds unconditionally (`scConsistentErased_of_scConsistent`).
  - Does not erase fences from a program (mapping `fenceAfterStores P` back to `P`) or construct a re-indexed execution of the source program; premise and conclusion are predicates on the same `Exec n` whose vertex set still contains the fence events (for source executions see `fence-mapping-source-execution`).
  - Fences are not inert under TSO: `sbFencedWeak` is not TSO-consistent while its fence-free counterpart `sbWeak` is, so there is no TSO analogue of this theorem.
  - The proof uses only that `rf` and `co` edges join memory accesses; `RfKinds` and `CoKinds` are stated as the package's well-formedness conditions, and each is shown necessary by an execution with a fence endpoint.

- **10. `shared-location-fencing-soundness`**
  - 'Shared' is computed from the execution's own events (accessed, excluding initialisation writes, by two or more threads); no program-level mapping 'fence after shared stores' is formalized, and no static sharing analysis is validated.
  - Conclusion is SC after fence erasure (`SCConsistentErased`); for SC with fences present combine with `fence-erasure`; no re-indexed execution of a source program is constructed.
  - The first eight hypothesis entries belong to the primary theorem `scConsistentErased_of_tso_of_fenceBetweenBothSharedWR`; the corollary `scConsistentErased_of_tso_of_fenceBetweenSharedWR` assumes `CoKinds` instead of `CoSameLoc` and `FenceBetweenSharedWR` instead of `FenceBetweenBothSharedWR`, both strictly stronger, so the corollary is the weaker statement. Its own eight hypotheses are each necessary (`fenceBetweenSharedWR_needs_*`).
  - Does not justify omitting fences after writes to locations that are only temporarily thread-local (e.g., before publication through a pointer): `LocalLoc` requires that at most one thread accesses the location anywhere in the execution.
  - Does not claim necessity: omitting fences on some shared write→read pairs can still preserve SC (e.g., accesses to a single shared location, where SC per location already rules out cycles); see `partial-fencing-unsound` for a case where the omitted fence matters.
  - Does not claim `FenceBetweenBothSharedWR` is the weakest sound static condition: e.g., triangular-race freedom (Owens, ECOOP 2010, Sect. 6) also exempts reads that race with no write of another thread; no such refinement is formalized here.
  - Establishes axiomatic SC-consistency (acyclicity of `po ∪ rf ∪ co ∪ fr` on memory accesses), not preservation of a global write order across locations: Owens (ECOOP 2010, Fig. 6) shows that a write to a location accessed by one thread followed by an unfenced read of a shared location (the shape of `localWR`) violates memorySC, which also preserves the global order of writes, while such executions are SC-consistent in the sense used here.

- **11. `partial-fencing-unsound`**
  - One missing pair suffices in SB; no claim about which pairs can be omitted in other programs beyond `shared-location-fencing-soundness`.
  - Escape hatch: this counterexample refutes fencing only one side of SB; it does not show that every shared write→read pair in every program needs a fence (e.g., `T0: x := 1; r := x ‖ T1: x := 2` touches a single location, where SC per location already rules out cycles; not stated as a theorem here).

- **12. `straight-line-race-freedom-collapse`**
  - The collapse is a property of straight-line programs: with control flow (branches on loaded values) or synchronization operations, `hb` can order conflicting accesses in every SC execution. No such language is modelled, so no DRF-SC theorem (Adve-Hill or Owens style) is stated or proved in this package.
  - `NoUnfencedWRIncident` is syntactic: every write with no `po`-later read and every read with no `po`-earlier write satisfies it vacuously with zero fences (in the fence-free MP and LB executions every event satisfies it; `noUnfencedWRIncident_vacuous_example`). It does not model C11/x86 SC atomics: an SC-atomic load compiled as a plain `MOV` after a plain store does not satisfy it.
  - Race freedom here is not C11's, Java's, or Owens's x86 data-race freedom (ECOOP 2010, Def. 5, defined on SC execution prefixes with locked instructions).

- **13. `static-both-sides-fencing-sc-on-tso`**
  - Strictly weaker than `shared-location-fencing-soundness`: `localWRProg` fails `ConflictsWRFenced`, yet its execution `localWR` satisfies `FenceBetweenSharedWR` (`localWRProg_not_conflictsWRFenced_but_fenceBetweenSharedWR`).
  - Not a DRF-SC theorem: `hb` plays no role in the premise (`straight-line-race-freedom-collapse`).
  - `NoUnfencedWRIncident` holds vacuously for writes with no `po`-later read and reads with no `po`-earlier write, and does not model C11/x86 SC atomics.

- **14. `drf-either-fenced-variant-rejected`**
  - The exemption is a static condition on the program (`straight-line-race-freedom-collapse`); `hb` plays no role.
  - `NoUnfencedWRIncident` holds vacuously for writes with no `po`-later read and reads with no `po`-earlier write; in the counterexample thread 0's accesses satisfy it through an actual fence and thread 1's accesses do not satisfy it.
  - Escape hatch: write-write conflicts, and conflicts whose read has no unfenced `po`-earlier write, are not the failing pattern; the counterexample needs an unfenced write→read pair on a thread whose read conflicts with another thread's write, as in triangular races (Owens, ECOOP 2010, Sect. 6). No theorem here characterizes the failing pattern.

### Escape hatches (which hypotheses, if dropped or weakened, defeat a counterexample or impossibility)

- **`sb-tso-not-sc`, `partial-fencing-unsound`, `drf-either-fenced-variant-rejected`.** Fencing
  every `po`-ordered write→read pair (card 6), every such pair between shared locations (card
  10), or requiring both sides of every conflicting pair to be free of unfenced write→read pairs
  (card 13) makes TSO-consistent executions satisfying those theorems' other hypotheses SC
  (after fence erasure where stated). `partial-fencing-unsound` refutes fencing only one side of
  SB; it does not show that every shared write→read pair in every program needs a fence (for
  example, `T0: x := 1; r := x ‖ T1: x := 2` touches a single location, where SC per location
  already rules out cycles; not stated as a theorem here).
- **`keep-same-location-wr-ppo-variant-rejected`.** The separating execution uses store
  forwarding (a read of the thread's own buffered write, an internal `rf` edge) followed by a read
  of another location; nothing is claimed either way about executions without that pattern.
- **`drf-either-fenced-variant-rejected`.** Write-write conflicts, and conflicts whose read has no
  unfenced `po`-earlier write, are not the failing pattern; the counterexample needs an unfenced
  write→read pair on a thread whose read conflicts with another thread's write, as in triangular
  races (Owens, ECOOP 2010, Sect. 6). No theorem here characterizes the failing pattern.
- **`straight-line-race-freedom-collapse`.** The collapse depends on straight-line programs: with
  control flow (branches on loaded values) or synchronization operations, `hb` can order
  conflicting accesses in every SC execution.

### Hypotheses that are stronger than necessary (all tight, but not weakest)

- `fence-mapping-source-execution`, `hwf : X.RfCoWf`: tight as a bundle only; given `PerLocSC`,
  `RfFunctional` and `CoTrans` are redundant (`Exec.rfFunctional_of_perLocSC`,
  `Exec.coTrans_of_perLocSC`), and `RfCoWf` constrains edges at inserted fences that the source
  execution never sees (`storeFenceExtraRfOnInserted_check`).
- `shared-location-fencing-soundness`, corollary form: `CoKinds` and `FenceBetweenSharedWR` are
  strictly stronger than the primary theorem's `CoSameLoc` and `FenceBetweenBothSharedWR`
  (`coBetweenReadsSameLoc_separates_coSameLoc_from_coKinds`, `sharedWLocalR`).
- `shared-location-fencing-soundness`, primary form: not claimed to be the weakest sound static
  condition; triangular-race freedom (Owens, ECOOP 2010, Sect. 6) also exempts reads that race
  with no write of another thread. A refinement in that direction (fence `W →po R` only if the
  read's location is written by another thread) looks plausible but is **not examined** in Lean.

### Tightness `unknown`

None. Every hypothesis on every card is `tight` with a kernel-checked counterexample.

### Considered and not stated

- **DRF-SC for straight-line programs** with `hb = (po ∪ rf)⁺` and a both-sides fence exemption:
  not stated as a result, because on straight-line programs its premise collapses to the static
  condition of card 12; its former conclusion survives as card 13 with minimal hypotheses.
- **A program-level "fence after shared stores" mapping** (`fenceAfterSharedStores`): not
  formalized. Card 10 computes sharing from the execution's own events, and relating that to a
  static sharing analysis was not examined.
- **Extending `Prog` with control flow:** not done; it changes the program model (event sets
  depend on read values) and is outside this package.
- No stated result of this package was found false, and none was omitted for lack of a proof.

## Evidence

### Kernel-check record

- **Toolchain:** Lean `leanprover/lean4:v4.34.1` (`lean --version`: `Lean (version 4.34.1,
  x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`); tag
  `v4.34.1` of `leanprover/lean4` resolves to that commit. Core Lean only; the Lake project
  (`lean/lakefile.toml`, one `[[lean_lib]]` named `ToyWMM`, no `[[require]]`) has no dependencies.
- **Build:** `lake build` of `lean/` succeeds with 17 jobs and no warnings.
- **Banned constructs:** no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations,
  `implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC` in any Lean source. All
  concrete checks are kernel `decide` through the proved Floyd–Warshall test (card 1).
- **Axioms:** all 590 non-internal declarations of the `ToyWMM` modules (computed with
  `Lean.collectAxioms`) depend only on subsets of `{propext, Classical.choice, Quot.sound}`:
  211 on none, 91 on `propext` only, 275 on `propext, Quot.sound`, 13 on all three. Per-declaration
  lists are in `audit/axioms.json`.
- **Statement hashes:** for each name below, `statement` is the SHA-256 of the Lean `repr` of its
  type, and `closure` is the SHA-256 of the sorted, newline-joined list of
  `name : repr(type)[ := repr(value)]` lines for every `ToyWMM` constant reachable from the type
  (values of definitions included, proofs of theorems excluded); `audit/statements.json` records
  both plus the closure size. Names marked `+` are the supplementary witnesses in
  `lean/ToyWMM/Remarks.lean` (universal non-vacuity and the `hc` counterexample of card 12, and
  the corollary counterexamples of card 10).
- **Observed:** 2026-11-20 (build, axiom audit, hashes, and bibliographic checks of the primary
  sources below).

| Card | Lean name | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 1 | `Rel.acyclicB_eq_true_iff` | result | Quot.sound, propext | `c344c5d0778ccfa118288ba121e755e4a7382585456ac983aef5745edd9a7070` | `166a6eed982f88ef87cd70aa24cc96d229c2976efbc11dfb283439da65a7b199` (7) |
| 1 | `Rel.warshall_iff_path` | result | Quot.sound, propext | `d7f65f5a6b50f8edce72a24000028f9eb5837edab5ba9fe4dae2d566716b0722` | `3899cdf4ab0cd91b57db88c14c74fa02277fdb43100c4c5ce0bdcfb0dd89568a` (5) |
| 1 | `acyclic_example_pos` | non-vacuity | Quot.sound, propext | `85fac8ef60e3c576ac608df867d0caecfff7229fb1af400b894956fb3bc1ac09` | `d9d086ac3ef53c3482d1d985fdb9f0e7046757f6ce97faa508c49bea769d6e26` (4) |
| 1 | `acyclic_example_neg` | non-vacuity | Quot.sound, propext | `89a90bad6d3d679b2d08e6f5288c13fa9fc091170c2af068e8b445930ab23e00` | `d9d086ac3ef53c3482d1d985fdb9f0e7046757f6ce97faa508c49bea769d6e26` (4) |
| 1 | `acyclic_example_neg_self` | non-vacuity | Quot.sound, propext | `40dab753723998d1c6814fb2d51fe8324272a4be1486da7353afd24056783ecc` | `d9d086ac3ef53c3482d1d985fdb9f0e7046757f6ce97faa508c49bea769d6e26` (4) |
| 2 | `tsoConsistent_of_scConsistent` | result | Quot.sound, propext | `f2507dd96d1a8cf62eb19155cd8cf12a8a42030af0e940bd0943abdd9338e1ee` | `c488592ecdb6c50b39a1ef882fb486d9d16ea500b7b1ea6c98a7cba7edf85cf0` (49) |
| 2 | `tsoConsistent_of_scConsistent_needs_sc` | counterexample | Quot.sound, propext | `03864680bcebfafbaaac81dfcbe3ed675face86f3d1877a1ea4da443e4dd1d15` | `55b25d35b6bbceb1f22d5bdde1c67b2118a1ea604ebbb34ad433e3b6d3b9d413` (56) |
| 2 | `nonvacuity_tsoConsistent_of_scConsistent` | non-vacuity | Quot.sound, propext | `abb6980f97097c35a315a98965971d9eb5c459b6b4775e1f41cbb652a46f3ace` | `21604ef97db2dc7e0bf481e85aaf368a762ad884c80109bc88b4853bf24aa0f8` (33) |
| 3 | `Litmus.sb_weak_tso_allowed_sc_forbidden` | result | Quot.sound, propext | `e6355ebbae03574d050a0bdf3b7144ba8eaba74d3bf1f1e2c40e7706c7985c57` | `883c18a00377b6a5999e4b0ca66606cae8df915000e932d3a1957cf04df07595` (94) |
| 3 | `not_forall_wf_tsoConsistent_scConsistent` | result | Quot.sound, propext | `47ee76c2df4afb781b3e94e2dd49db9b324f50de0531878a0503be1b5f355eb8` | `fdf9399fe4e3b9e2a62914aa964380b1e2366771acea5c8bd616b5432938f115` (65) |
| 3 | `Litmus.sb_weak_tso_allowed_sc_forbidden` | non-vacuity | Quot.sound, propext | `e6355ebbae03574d050a0bdf3b7144ba8eaba74d3bf1f1e2c40e7706c7985c57` | `883c18a00377b6a5999e4b0ca66606cae8df915000e932d3a1957cf04df07595` (94) |
| 3 | `tsoConsistent_of_scConsistent` | positive control | Quot.sound, propext | `f2507dd96d1a8cf62eb19155cd8cf12a8a42030af0e940bd0943abdd9338e1ee` | `c488592ecdb6c50b39a1ef882fb486d9d16ea500b7b1ea6c98a7cba7edf85cf0` (49) |
| 4 | `Litmus.mp_weak_tso_forbidden_sc_forbidden` | result | Quot.sound, propext | `e00707efe8dd6bc3fbb0b06290ecb04b10c584c5cfaf1fc84bf433f0e97c1356` | `2c6bd5418eab730d316ecf2230ea0e3f023de00f99b4c861db9add3c97a253d1` (94) |
| 4 | `Litmus.lb_weak_tso_forbidden_sc_forbidden` | result | Quot.sound, propext | `c9780adc9de0aad13cd868e07c56b84a501d419d77a3074a7288ca7038b02d9b` | `8ae0950e6a2d292f201f414f96d6f7eac246db59d664d398d8f2d2eff10f26f0` (94) |
| 4 | `Litmus.w22_weak_tso_forbidden_sc_forbidden` | result | Quot.sound, propext | `83f5714e8e04b893c25f7cd33ec18bfb739c0bb4cfac391fb5f1c57801fed2f5` | `3e42acee305f4f33d49aacb3c9e234d6d4a768f51e671a58997a6077532d47e8` (93) |
| 4 | `Litmus.iriw_weak_tso_forbidden_sc_forbidden` | result | Quot.sound, propext | `840b9e09a0714cd868120e360155666776e3e00329f9c8f30adee92c3bbaaf9b` | `be896b70bde8bc000f0425213749e438667e61d34dc8a5893b0aa41929fa00eb` (94) |
| 4 | `Litmus.sbFenced_weak_tso_forbidden_sc_forbidden` | result | Quot.sound, propext | `7516f339631b6b28d0939a627b90db0bc5868ba10d45a77674b39e3d5f22777a` | `0ae184fca9711a079a31c05b58c0dba148413d515403bc1a8c07acc38caab8fe` (99) |
| 4 | `Litmus.r_weak_tso_allowed_sc_forbidden` | result | Quot.sound, propext | `ebee8e622559a5bf0e618e8a7bf1fd8df1d76c50e85512518a462e0a75c0bcc0` | `e74f74d505d40e02048e4e7b3912664edd787a62b1983b413f7fc7e2dbfcc078` (94) |
| 4 | `Litmus.mp_weak_tso_forbidden_sc_forbidden` | non-vacuity | Quot.sound, propext | `e00707efe8dd6bc3fbb0b06290ecb04b10c584c5cfaf1fc84bf433f0e97c1356` | `2c6bd5418eab730d316ecf2230ea0e3f023de00f99b4c861db9add3c97a253d1` (94) |
| 4 | `Litmus.lb_weak_tso_forbidden_sc_forbidden` | non-vacuity | Quot.sound, propext | `c9780adc9de0aad13cd868e07c56b84a501d419d77a3074a7288ca7038b02d9b` | `8ae0950e6a2d292f201f414f96d6f7eac246db59d664d398d8f2d2eff10f26f0` (94) |
| 4 | `Litmus.w22_weak_tso_forbidden_sc_forbidden` | non-vacuity | Quot.sound, propext | `83f5714e8e04b893c25f7cd33ec18bfb739c0bb4cfac391fb5f1c57801fed2f5` | `3e42acee305f4f33d49aacb3c9e234d6d4a768f51e671a58997a6077532d47e8` (93) |
| 4 | `Litmus.iriw_weak_tso_forbidden_sc_forbidden` | non-vacuity | Quot.sound, propext | `840b9e09a0714cd868120e360155666776e3e00329f9c8f30adee92c3bbaaf9b` | `be896b70bde8bc000f0425213749e438667e61d34dc8a5893b0aa41929fa00eb` (94) |
| 4 | `Litmus.sbFenced_weak_tso_forbidden_sc_forbidden` | non-vacuity | Quot.sound, propext | `7516f339631b6b28d0939a627b90db0bc5868ba10d45a77674b39e3d5f22777a` | `0ae184fca9711a079a31c05b58c0dba148413d515403bc1a8c07acc38caab8fe` (99) |
| 4 | `Litmus.r_weak_tso_allowed_sc_forbidden` | non-vacuity | Quot.sound, propext | `ebee8e622559a5bf0e618e8a7bf1fd8df1d76c50e85512518a462e0a75c0bcc0` | `e74f74d505d40e02048e4e7b3912664edd787a62b1983b413f7fc7e2dbfcc078` (94) |
| 4 | `wf_example_pos` | non-vacuity | Quot.sound, propext | `d85a35b653caa9bfa6c72a94c5df09327c1eb6084fe584be58f89e79b23aba7f` | `b671c4cabbef3f56da9ae76dc510c15b16e1453172fe46bf5169c9efd8da4671` (65) |
| 5 | `tsoConsistent_of_tsoConsistentKeepSameLocWR` | result | Quot.sound, propext | `6067479f96358d075771d5201d8a5f4d272b077415d15dcd4ed724ed14a56506` | `fbe170c10a71ddf5b6d2f64fe66b9abd8037c6900f56e91d5dbd546dcae06532` (49) |
| 5 | `Litmus.n6_weak_tso_allowed_keepSameLocWR_forbidden` | result | Quot.sound, propext | `3d48d67118b58c2055ebd92ff53a3a7a809451aa1d33c3859dc6c806ccf536df` | `5795ce9b05da34cabdb873387af3872a8e8c88eec3d3f41c8a2011f709d9c58a` (96) |
| 5 | `tsoConsistent_of_tsoConsistentKeepSameLocWR_needs_keep` | counterexample | Quot.sound, propext | `e4453deb296a27340bafc9b008202b9eade6473dcb8a6bb7436f1ca0110bc023` | `78bb73e02c2ab467b341c12b7ee7c7b7260e6e9072213798e47eef5299a49611` (56) |
| 5 | `keepSameLocWR_example_pos` | non-vacuity | Quot.sound, propext | `3ad44bde8cadc26ff14f0844b923f6a8d10d05852463393015648b1ab3b8d500` | `9e6fa92cd3006fe50e96c7dfb2c139af6f54191e9ed8b54d839c3bfb7f03e6cb` (52) |
| 5 | `Litmus.n6_weak_tso_allowed_keepSameLocWR_forbidden` | non-vacuity | Quot.sound, propext | `3d48d67118b58c2055ebd92ff53a3a7a809451aa1d33c3859dc6c806ccf536df` | `5795ce9b05da34cabdb873387af3872a8e8c88eec3d3f41c8a2011f709d9c58a` (96) |
| 5 | `keepSameLocWR_example_pos` | positive control | Quot.sound, propext | `3ad44bde8cadc26ff14f0844b923f6a8d10d05852463393015648b1ab3b8d500` | `9e6fa92cd3006fe50e96c7dfb2c139af6f54191e9ed8b54d839c3bfb7f03e6cb` (52) |
| 5 | `tsoConsistent_example_pos` | positive control | Quot.sound, propext | `619699dc575e14a19f95b9f60da8b9c05c8761ccde244592ed9e88f440beb291` | `eb49e786356d651f6476c1bb5a5ee7914585613b15f723998cf0e3e54f74d32c` (54) |
| 6 | `scConsistentErased_of_tso_of_fenceBetweenWR` | result | Quot.sound, propext | `3d8c01b5f0ee315a6262fea3684f45a789237f6f18d768c901e36585ae104626` | `1ef81b6586ef0e2ce0a2cfa71bede45e01d3a8cfd631230eba34faecab8000ef` (53) |
| 6 | `fenceBetweenWR_needs_poTotal` | counterexample | Quot.sound, propext | `b8e7c5e448a142e361b818f0f160cf2f98276b19f4d14b9a838554d41c5c67b2` | `b8c89c91d70fd34c1316fff48e33bb75d96eabfe2401e4d7e2dff1068865215b` (61) |
| 6 | `fenceBetweenWR_needs_rfSameLoc` | counterexample | Quot.sound, propext | `478775cf83a92b56210bc9a89e6015bb08e3f1ddcfe98b46e5e966bf8da392a5` | `f3bb02bdf807fc5b12915f606167b8a75a68bef4bdfcd07eedfc1aae1bb3e197` (59) |
| 6 | `fenceBetweenWR_needs_fenceBetweenWR` | counterexample | Quot.sound, propext | `028c7ec9e9b622767c1f6b34d90929963390115087725e15ca1a29a47fe55e4c` | `7c1f7e8bfd10c5c34e63b9218c89c26b402f5fed23fbddee5fd620bd1d3b40ca` (60) |
| 6 | `fenceBetweenWR_needs_perLocSC` | counterexample | Quot.sound, propext | `b8c4a686b357af828820247bde5c5babaa56405ed3a2b7c8180024c3fedd64a2` | `0764ca9f3e2c15f0fdea3aa6fc251c6d7ceb16b7bcf93a20c82f3be017152f53` (60) |
| 6 | `fenceBetweenWR_needs_tsoGhbAcyclic` | counterexample | Quot.sound, propext | `45dad8f16ae788a79c4020e02538ed45c8f8a396f653a26495f4700a4e7266ea` | `0e9db8c1653bcc9d2925a213383dbc4a80f917f5ff677a1a58b98dfbfd076e71` (61) |
| 6 | `nonvacuity_scConsistentErased_of_tso_of_fenceBetweenWR` | non-vacuity | Quot.sound, propext | `a67a917603fd37d7b16ebb2a5f87d8a4f64a6af9fd214c72b5f07b25def0fb33` | `77c3bbaabf82dd1c5a7ae12fe27a38181e3aceda340bb35fd30a43eed61e28bb` (57) |
| 7 | `scConsistentErased_of_tso_fenceAfterStores` | result | Classical.choice, Quot.sound, propext | `d2b29e42bea13ec33d60d1c43011285eddd94f15be53ed319cb1c1e1a14a003f` | `7b98973068e82cfb2be17d52384af1a28c9c3d063b790d8bc2738481c294e224` (78) |
| 7 | `fenceAfterStores_needs_execOf` | counterexample | Quot.sound, propext | `dfe7d3cc087d0e03ca3d70519ac7ce7c70f0011f1debac41c9801e12cb5d8fce` | `60c58c1bf9a65025d93c1de187df5ad6794a126c0581dd6fe028869123528121` (85) |
| 7 | `fenceAfterStores_needs_rfSameLoc` | counterexample | Quot.sound, propext | `8164c24c1f468333aab3abc82bdbc2b35a58b0da3ba0bbaa64ccaac23959d295` | `593faa315885fffcf172f9948312221c0d80644f9122efe81f717d19bb17c97b` (86) |
| 7 | `fenceAfterStores_needs_perLocSC` | counterexample | Quot.sound, propext | `ed844bad7868de43f07f4de29f4cb9e22017bb552cbee8fcf33c403fe1c42ffe` | `8ea4e3e70181c0cc7000fa29d760e758ebad9795d520ec51a1c2b9458c0c0429` (86) |
| 7 | `fenceAfterStores_needs_tsoGhbAcyclic` | counterexample | Quot.sound, propext | `0bc300e4f16151260fe9a30291df1646a7a2a10c9cf3d57f9e9a882cefb67791` | `cf24285e13dae842e8934865f3d19c62ea7856aa1d52408592ace35d58e0909e` (86) |
| 7 | `nonvacuity_scConsistentErased_of_tso_fenceAfterStores` | non-vacuity | Quot.sound, propext | `fcd8646f3144d008f9693e523b70805a1cd55d825e5da48ebb01dcd0d5a83c42` | `8a835229426f9b47bc57802961a0991f6728797fbadb4081fb78f69a9102d59b` (82) |
| 8 | `exists_sc_source_execution_of_tso_fenceAfterStores` | result | Classical.choice, Quot.sound, propext | `0a82bef72fab2b612b5a10a781e13f3eae4aacbbf6fb674b317264f357c73e67` | `aac26a8478a5f9d836e566205f0fde772aed0e39c3348d89d0b4379701587a30` (93) |
| 8 | `sourceExec_needs_execOf` | counterexample | Quot.sound, propext | `14adf95d285c11122e5992c276d857988db313d76a808f96782e25d39e898e5f` | `1289b4ae364bd3dee8f90f51f4ea62e591fdeb90b5ec4751fa6541a628724ab5` (100) |
| 8 | `sourceExec_needs_rfCoWf` | counterexample | Quot.sound, propext | `6cfb50fa0e352151cf33e565536156f480511c5d6d2de2f86711aa14b7ae2c1a` | `294a765eac12e4e6e59227fd73775529ac21ef75275a3960d8e670db990e494a` (98) |
| 8 | `sourceExec_needs_tso` | counterexample | Quot.sound, propext | `9131a8d8e0f91544b1bc8bcf18acd94835c9982adeeb407a41404843cf42c982` | `cb3edd8e7914f20a3e5c080834b1cffdadda407d3f7551bac19a21c271add87f` (101) |
| 8 | `nonvacuity_exists_sc_source_execution_of_tso_fenceAfterStores` | non-vacuity | Quot.sound, propext | `c6c1031137728781618650163c28928b9edfd550031d7e306716c43a1408c604` | `8059efaaae2a70c2ce1de162b22a0fb022ad8781903730ab3b61a72c9c2e2d74` (92) |
| 8 | `sbFencedSC_source_execution` | non-vacuity | Quot.sound, propext | `f5a24715693adf0ec1dc13bd89dbea0029d12c17f005d607730a611c0c15a8f4` | `1e52435e3b2bf7056e935d892f5acaa9550058477084fdbf097e55de71411b1b` (89) |
| 9 | `scConsistent_of_scConsistentErased` | result | Quot.sound, propext | `b385d115101baff98749fa1416d983ea104f4d73f6bbd360ccd1d189809b370e` | `bb8d514093eee5fa91d8615744035396f811a4125bd3c3828b00b79527b9ce56` (42) |
| 9 | `scConsistent_of_scConsistentErased_needs_poIrrefl` | counterexample | Quot.sound, propext | `754ffb9ade573134c2f543b2623c510cf0b9f8fa3e27066ede9fe1d1e0f05ac3` | `c922dc5b27d73195a4b22900c7498f89875315ce054252fd1c1f1bbf43df5cc3` (47) |
| 9 | `scConsistent_of_scConsistentErased_needs_poTrans` | counterexample | Quot.sound, propext | `d0c5c85f73eac8b36a7e2ced9e158203fc734c2150749243470d02e61af2a56d` | `fb8fd22ffa8772bcb14111cf725c3b7cd16f327080ad54f53a48dc9f3071bbd5` (49) |
| 9 | `scConsistent_of_scConsistentErased_needs_rfKinds` | counterexample | Quot.sound, propext | `ddbc88296c1b755571a48b459cb154a70e9e0eaed46c03e84d1ac30e02ee7d54` | `19573a9e090b29ce72ee0a8463e7c6d76bd03a2d7c5ac306c0612b518ae1fef6` (48) |
| 9 | `scConsistent_of_scConsistentErased_needs_coKinds` | counterexample | Quot.sound, propext | `cf565182fe08dbbe31014a15605d6e07d8df575b7bfb1cbd4bba78411e5a1a08` | `35c12cfa01bce236b5ebc821efd1968315e58fde069a7bf0302aeb1d131f745d` (48) |
| 9 | `scConsistent_of_scConsistentErased_needs_scErased` | counterexample | Quot.sound, propext | `8cb865b6957c995026fd9f2ac277f29aa3f124f3335b370414b98b7c80db0b46` | `8d849d72cd5085797541e4a0214adeb5620d874653d4fd2928b5f2d48576b47f` (53) |
| 9 | `nonvacuity_scConsistent_of_scConsistentErased` | non-vacuity | Quot.sound, propext | `3793146d1f99fd87a5e7108dae3c5177cb35fab57c180ceb63c1b28ad728dc2f` | `badb1b7b1a59f245dbe3440069aacfe26cee6e7354095c10f4552500361fa77a` (53) |
| 10 | `scConsistentErased_of_tso_of_fenceBetweenBothSharedWR` | result | Classical.choice, Quot.sound, propext | `c03f6c910b0fceec76a4cdf4bc923d1807ea5518368e1ce852bf403134b6748b` | `49282619534111aa98c1784cff0257131379f187c7f2547fbf47b679b3d4a9ea` (57) |
| 10 | `scConsistentErased_of_tso_of_fenceBetweenSharedWR` | result | Classical.choice, Quot.sound, propext | `17826641a92e37ced0c318261c544e0d26fc39fee2fbfc6c94a6081546d7eaa3` | `650e13e1c1120fac45b5ed72d40aefe870f24fdf0db25920bd178544a087f233` (57) |
| 10 | `fenceBetweenBothSharedWR_needs_poTrans` | counterexample | Quot.sound, propext | `36a2d56323e5df07f8516c43478328629513c40ed60f306fb15585239c5d2af4` | `856ffb10a38c767bc6cd06704a182350296f1470c8a8c5f952a797b95f643076` (64) |
| 10 | `fenceBetweenBothSharedWR_needs_poWithinThread` | counterexample | Quot.sound, propext | `3a086c31a3125cf416b2aa265cd395c4eceb7042c331d84c4c3f00b0efd15dd0` | `6aae2fb244c5ff1f595176ecbdafd410a187f739a3290b7fc7e4abe8ba024798` (64) |
| 10 | `fenceBetweenBothSharedWR_needs_poTotal` | counterexample | Quot.sound, propext | `06cf40ac23d09f8f96a453dfe5848b6aad844146f4245bf31b6983ab7351b427` | `17e77864af3148c0b67df6550b19506b38cddaf3f80a6df9d2a643d224171dea` (65) |
| 10 | `fenceBetweenBothSharedWR_needs_rfSameLoc` | counterexample | Quot.sound, propext | `140993d4ca7bf5d011afd4002e406134a660e65b048a25fb5409ad5ef82b68e8` | `47847f2279ee8f2790a854375d2cc44202cb2d5af9310167c1f3216f59c3da1b` (63) |
| 10 | `fenceBetweenBothSharedWR_needs_coSameLoc` | counterexample | Quot.sound, propext | `4fe5cd4b57b209d0012f7b896665bf4dc7727cc94e906a307ab71dd7ade38fd1` | `72c4d45971077ffbfba14c77c068ea987c610235d0a64c0113d6b8ae1798978e` (64) |
| 10 | `fenceBetweenBothSharedWR_needs_fenceBetweenBothSharedWR` | counterexample | Quot.sound, propext | `4ce76f99b7d6a4db7d367942197796c994445fa40b83d1cd28bb976e3a68ac30` | `9c81291f1030c5da244250bfd1120bc321c71c38d13ac44c52fe428e3f456682` (64) |
| 10 | `sbOneFence_execution_tso_not_scErased` | counterexample | Quot.sound, propext | `9cd15a636ac982fda95474c8392533e9ff2cd6e9193aee541e17a5cd99006a11` | `2b4e13fa1b95b16c1a2cd58557a1ec1192b5a6e9521bbc8c97308e9542b5a284` (100) |
| 10 | `fenceBetweenBothSharedWR_needs_perLocSC` | counterexample | Quot.sound, propext | `a89a3e689029494d8e3cd652a0ccdb2f1c13e4dcb76e84f3dc1637c8822ad486` | `f1575e7a78438ce1e8da10641f8d1ffdeb5f759d3df6460a16ca47a840cdfc95` (64) |
| 10 | `fenceBetweenBothSharedWR_needs_tsoGhbAcyclic` | counterexample | Quot.sound, propext | `4ccca2d51401ff6b9a48c2239169fdc753f77ce8989741a00391c580ebd59527` | `07af052a6591889251160c2609f4554f6ee946b9b87a9f45e1669d1f12dadeb5` (65) |
| 10 | `fenceBetweenSharedWR_needs_poTrans` + | counterexample | Quot.sound, propext | `897a281002417358159ec0d2e06a40ddd98471cc37d4ed6b11342d102f25288d` | `e1217d48d19dde4fbd93b693ffd7d5ff1c06174cf7a34609f6695fed0f83d474` (64) |
| 10 | `fenceBetweenSharedWR_needs_poWithinThread` + | counterexample | Quot.sound, propext | `c1ebf53759954d3dec9c521622ab8bf09862e42a80c1d420bb37c01785578c29` | `eb9d16ea1623ddfba4d858fc97e9bf7975fc74ac3f6682e2f976a2a06c91445c` (64) |
| 10 | `fenceBetweenSharedWR_needs_poTotal` + | counterexample | Quot.sound, propext | `5c3f0223034e4d57a1a5cbfb5c71bd19f35d9b8488767bddbe4716372af7ae3f` | `2ac2c1f44a437b5f09b478e28df293b0c7c57e1d04e3988b5ff492ee0e95eada` (65) |
| 10 | `fenceBetweenSharedWR_needs_rfSameLoc` + | counterexample | Quot.sound, propext | `8f4b0ee73212033ff0e4df2a801f98da4ab95486ed3381e1796316d87e36370c` | `dbe8bbf1ecf62d36a0972b594e501f987ad7c2d380380d277716f8175b86bf61` (63) |
| 10 | `fenceBetweenSharedWR_needs_coKinds` + | counterexample | Quot.sound, propext | `a42aea50e2d9b17a62e58cc5b02299075969ed6a50f2e006916e8e84938ad856` | `2d83cb6c02b9c37412c780c0abed173291272accd1f80db7ae4b34c423cd32a7` (64) |
| 10 | `fenceBetweenSharedWR_needs_fenceBetweenSharedWR` + | counterexample | Quot.sound, propext | `c5d87d2952604ebabe321f612360d8dfd59809ad79218c82ae7d7b3855c4b1c3` | `e26ea01d8c934bbd4bff25283ff627530791af6670cc5793f72d75823d873df2` (64) |
| 10 | `fenceBetweenSharedWR_needs_perLocSC` + | counterexample | Quot.sound, propext | `cc6c0992b6ec8d1462f55761fa621756e090c6da9ddeb1b5f6e29b60b9fab6cd` | `678a3735363da8285855c346b85ca13087c6cdd5124133643613106446b638e2` (64) |
| 10 | `fenceBetweenSharedWR_needs_tsoGhbAcyclic` + | counterexample | Quot.sound, propext | `472ceaa52b89a4c5dbb0e8616352432096d2dde127fbe30bded9e5a858befa62` | `32f1b5e3c1f4ddee0b36dd73ad623083d49bba59dc129d79179700a7f773fd39` (65) |
| 10 | `nonvacuity_scConsistentErased_of_tso_of_fenceBetweenBothSharedWR` | non-vacuity | Quot.sound, propext | `4c440e164427984e19ec2b24cb1d4ec62fcb493a49ab0cdae020f38674e2ef7d` | `680a6088c3b17b35424982fa97d06bf139b796458862148693d168495526327b` (63) |
| 11 | `sbOneFence_execution_tso_not_scErased` | result | Quot.sound, propext | `9cd15a636ac982fda95474c8392533e9ff2cd6e9193aee541e17a5cd99006a11` | `2b4e13fa1b95b16c1a2cd58557a1ec1192b5a6e9521bbc8c97308e9542b5a284` (100) |
| 11 | `sbOneFence_execution_tso_not_scErased` | non-vacuity | Quot.sound, propext | `9cd15a636ac982fda95474c8392533e9ff2cd6e9193aee541e17a5cd99006a11` | `2b4e13fa1b95b16c1a2cd58557a1ec1192b5a6e9521bbc8c97308e9542b5a284` (100) |
| 11 | `Litmus.sbFenced_weak_tso_forbidden_sc_forbidden` | positive control | Quot.sound, propext | `7516f339631b6b28d0939a627b90db0bc5868ba10d45a77674b39e3d5f22777a` | `0ae184fca9711a079a31c05b58c0dba148413d515403bc1a8c07acc38caab8fe` (99) |
| 11 | `scConsistentErased_of_tso_of_fenceBetweenBothSharedWR` | positive control | Classical.choice, Quot.sound, propext | `c03f6c910b0fceec76a4cdf4bc923d1807ea5518368e1ce852bf403134b6748b` | `49282619534111aa98c1784cff0257131379f187c7f2547fbf47b679b3d4a9ea` (57) |
| 12 | `hbRaceFree_sc_executions_iff_noConflict` | result | Classical.choice, Quot.sound, propext | `88b40727ac58d16c6dfeea81780e37b86472c5a2efdddf81e5b250a96e6d7ad6` | `b450b764f387c996959447d662ee370df0374d314c1fc2a8ca49675c47b473e8` (83) |
| 12 | `raceFree_sc_executions_iff_conflictsWRFenced` | result | Classical.choice, Quot.sound, propext | `31788e564b9e6c1cefb238ee9d7e3d5a4370950be7b1bbe1477e65c67e502167` | `e21cc3971d962b7c6d41702a4fe672c6b316bfec6dc5424d794cd55f5d891914` (88) |
| 12 | `raceFreeEither_sc_executions_iff_conflictsWRFencedEither` | result | Classical.choice, Quot.sound, propext | `3404c8b38520a1ffe6b65611328688e122034e6a70f9533d2ded8d5c9c9faefe` | `7aa07e883852e99b440de32eba246382758751ab87f2271e44f82de4a579a31a` (88) |
| 12 | `exists_sc_execution_hb_unordered_of_conflict` | result | Classical.choice, Quot.sound, propext | `c4dc063c9b876ca4947c2d27a69053e839ad62b70646cffc274860ee3fe2ff12` | `b450b764f387c996959447d662ee370df0374d314c1fc2a8ca49675c47b473e8` (83) |
| 12 | `exists_sc_execution_hb_unordered_needs_conflict` + | counterexample | Quot.sound, propext | `0d54081e323f3aea5505e0e96f665961cb46f3522bbe2555185ce47a437b60b4` | `5531e343ad5c80339e8dea0dfc8cd768264ccfa848a460fca53dc4c933381957` (84) |
| 12 | `nonvacuity_straightLine_race_characterizations` | non-vacuity | Quot.sound, propext | `e0b8285d74310647999b6c9aa4badc2550ae58980d8f5b1296b49eb4597b1a77` | `b9dade87af227568f2e2dfe7f18f037f8057bce7a28d366c31b259a7aeb52539` (61) |
| 12 | `forall_prog_exists_wf_sc_exec` + | non-vacuity | Classical.choice, Quot.sound, propext | `d2a5da28f499b6e99fe654850f656b0fea104fc8d18aab1604367a0cb9ee8016` | `f5461e5db19e7ef37695dc235ee393169ab502eaf429d67fa91cb1cad49a2a2d` (78) |
| 13 | `scConsistent_of_tso_of_conflictsWRFenced` | result | Classical.choice, Quot.sound, propext | `5b7016148ea99e63c16065b506a89824858a54a580b567c69fc7533d9e002147` | `5179e237726a17615bd581a985640cab5bdb0a09068384cfe6ba9bf27ea998a3` (80) |
| 13 | `fenceBetweenSharedWR_of_conflictsWRFenced` | result | Classical.choice, Quot.sound, propext | `bd029f3f21994a622dbd36c98c1fe867192214f8bf3f3ae202544d63cd50a7ff` | `081a1f065758a4cc56dee73f7421076ec82dbd36016d1ff86b64821149fda481` (63) |
| 13 | `scConsistent_of_tso_of_conflictsWRFenced_needs_conflictsWRFenced` | counterexample | Quot.sound, propext | `6781585843f033e692c224992a40d1ff75f53a901a000f24bbd8d7bcfd35dfd6` | `e1e42289ea23b4c889a66d789ca6153f5a96c03d0c6dc9ac6d0130d43a7f4fef` (87) |
| 13 | `scConsistent_of_tso_of_conflictsWRFenced_needs_execOf` | counterexample | Quot.sound, propext | `a44193901935ddf5a4f310823fd4c174fad4dda9ce83b4cbff2d3184ca37e32a` | `0bcf4a1bfc7355d9cbdcce13a340cc4fdb301cfe3c608d38616683024d663e9b` (86) |
| 13 | `scConsistent_of_tso_of_conflictsWRFenced_needs_rfSameLoc` | counterexample | Quot.sound, propext | `eb96c34fd03f4534fca8d6ec96ee04adfcaccd4ed66f5907bc3b23968c9efa8e` | `811860e3accefb60468a0037bfb9d175bfa9a1cd9969d5128f03d0af34ed285e` (87) |
| 13 | `scConsistent_of_tso_of_conflictsWRFenced_needs_rfKinds` | counterexample | Quot.sound, propext | `65a0936186d28326a049b174b3c96eed4cbb5252b7a9354315f73198e0e888b6` | `ec4484204af3bbdd7786d44993b94c1ef62799cabe96477a2eb1dc4bf0deb72e` (87) |
| 13 | `scConsistent_of_tso_of_conflictsWRFenced_needs_coKinds` | counterexample | Quot.sound, propext | `fa5a261b587036e5c20364d289fa92368c0e9a062e6778ac4d113c45df8dc787` | `8cc9b4d449d1e1d0a805ee80782a04944f7825526a99577c0446a1c4c9d44944` (86) |
| 13 | `scConsistent_of_tso_of_conflictsWRFenced_needs_tso` | counterexample | Quot.sound, propext | `f82ec1ef3ee469f6f9ed646107d1564c7193d1bfb61b2b184de4bc33f6e9cbd0` | `f4b357aea44bbcdbd78e6d33c1e66cb298e1a11bb44dbfa400e218bb5629156c` (92) |
| 13 | `fenceBetweenSharedWR_of_conflictsWRFenced_needs_conflictsWRFenced` | counterexample | Quot.sound, propext | `e8ef66c823dc6c87d03c61b3d0932f0795a6dff71b2ed4788084f0c23f1adb24` | `ec565b36b323e76765995f7e4882cd2bfc169b9775874104af2f74362ed4dbfb` (70) |
| 13 | `fenceBetweenSharedWR_of_conflictsWRFenced_needs_execOf` | counterexample | Quot.sound, propext | `6a56bed9d1705f0e1322cfeef5e0d4dad7428a19acc56c8993cacc83f6f8950d` | `32f273836d0b3181f8c61bad908a9fa6a735ffae065628f7475a9a5a339eadd6` (69) |
| 13 | `nonvacuity_scConsistent_of_tso_of_conflictsWRFenced` | non-vacuity | Quot.sound, propext | `9dee548ff8668567e73c1d3abc803a7bf302f66cf6862708e5eccbb5a21be8cc` | `e5f6fd11c9c0652a926b01c8216f82b98b54b0c808037012d0a7aae2dc0dd70d` (90) |
| 14 | `conflictsWRFencedEither_does_not_imply_sc` | result | Classical.choice, Quot.sound, propext | `9ab13ee5c88113b45a38b181c67416320a4032bf6f7dd96f4e0bc4ea988bbf1e` | `680a42139d99fa278f64b28339b2784c544d98d9a22db72cb079c3eee9b8e419` (104) |
| 14 | `conflictsWRFencedEither_does_not_imply_sc` | non-vacuity | Classical.choice, Quot.sound, propext | `9ab13ee5c88113b45a38b181c67416320a4032bf6f7dd96f4e0bc4ea988bbf1e` | `680a42139d99fa278f64b28339b2784c544d98d9a22db72cb079c3eee9b8e419` (104) |
| 14 | `scConsistent_of_tso_of_conflictsWRFenced` | positive control | Classical.choice, Quot.sound, propext | `5b7016148ea99e63c16065b506a89824858a54a580b567c69fc7533d9e002147` | `5179e237726a17615bd581a985640cab5bdb0a09068384cfe6ba9bf27ea998a3` (80) |

Supplementary theorems cited in the cards but not part of the statement record (each is listed in
the `scope_witnesses_lean` field of its card in `results.json`; existence and axioms are checked
by the revalidation commands, which carry no recorded hash for them):

- `Exec.rfFunctional_of_perLocSC` (card 8): axioms Quot.sound, propext.
- `Exec.coTrans_of_perLocSC` (card 8): axioms Quot.sound, propext.
- `storeFenceExtraRfOnInserted_check` (card 8): axioms Quot.sound, propext.
- `coBetweenReadsSameLoc_separates_coSameLoc_from_coKinds` (card 10): axioms Quot.sound, propext.
- `sbFencedWeak_needs_fenceOrd` (card 4): axioms Quot.sound, propext.
- `fenceAfterStores_sbProg` (card 4): axioms none.
- `scConsistentErased_of_scConsistent` (card 9): axioms Quot.sound, propext.
- `noUnfencedWRIncident_vacuous_example` (card 12): axioms Quot.sound, propext.
- `localWRProg_not_conflictsWRFenced_but_fenceBetweenSharedWR` (card 13): axioms Quot.sound,
  propext.

Statements of the last five (files `lean/ToyWMM/Examples.lean`, `Litmus.lean`, `Fence.lean`,
`Examples.lean` and `Tightness.lean` respectively):

```lean
theorem sbFencedWeak_needs_fenceOrd :
    Rel.Acyclic (fun a b => sbFencedWeak.ppo a b || sbFencedWeak.rfe a b ||
        sbFencedWeak.co a b || sbFencedWeak.fr a b) ∧ ¬ sbFencedWeak.TsoGhbAcyclic
theorem fenceAfterStores_sbProg :
    fenceAfterStores sbProg = [[.store 0 1, .mfence, .load 1], [.store 1 2, .mfence, .load 0]]
theorem scConsistentErased_of_scConsistent {n : Nat} (X : Exec n) (h : X.SCConsistent) :
    X.SCConsistentErased
theorem noUnfencedWRIncident_vacuous_example :
    (∀ a, mpWeak.NoUnfencedWRIncident a) ∧ (∀ a, lbWeak.NoUnfencedWRIncident a)
theorem localWRProg_not_conflictsWRFenced_but_fenceBetweenSharedWR :
    ¬ localWRProg.ConflictsWRFenced ∧ ExecOf localWRProg localWR ∧ localWR.Wf ∧
      localWR.TSOConsistent ∧ localWR.FenceBetweenSharedWR ∧ localWR.SCConsistent
-- localWRProg := [[.store 2 1, .load 0], [.store 0 2]]   (T0: z := 1; r := x ‖ T1: x := 2)
-- localWR: initW 0, initW 1, initW 2, W 0 2 1, R 0 0 0, W 1 0 2; rf 0 → 4; co 0 → 5, 2 → 3
```

Statements of the other supplementary theorems (`lean/ToyWMM/Remarks.lean`;
`Exec.rfFunctional_of_perLocSC` is at lines 280-282, `Exec.coTrans_of_perLocSC` at 300-302 and
`exists_sc_execution_hb_unordered_needs_conflict` at 350-355):

```lean
theorem forall_prog_exists_wf_sc_exec (P : Prog) :
    ExecOf P (seqSCExec P) ∧ (seqSCExec P).Wf ∧ (seqSCExec P).SCConsistent
theorem Exec.rfFunctional_of_perLocSC {n : Nat} (X : Exec n)
    (hloc : X.PerLocSC) (hrfl : X.RfSameLoc) (hrfk : X.RfKinds) (hcot : X.CoTotal) :
    X.RfFunctional
theorem Exec.coTrans_of_perLocSC {n : Nat} (X : Exec n)
    (hloc : X.PerLocSC) (hcok : X.CoKinds) (hcot : X.CoTotal) :
    X.CoTrans
theorem storeFenceExtraRfOnInserted_check :     -- initW 0, W 0 0 1, F 0 with rf 0 → 2 (into the fence)
    ExecOf (fenceAfterStores [[.store 0 1]]) storeFenceExtraRfOnInserted ∧
      storeFenceExtraRfOnInserted.TSOConsistent ∧ ¬ storeFenceExtraRfOnInserted.RfCoWf ∧
      ∃ f : Fin (layout [[.store 0 1]]).length → Fin 3, (∀ a b, a < b ↔ f a < f b) ∧
        (∀ e, (storeFenceExtraRfOnInserted.ev e).isAccess = true → ∃ a, f a = e) ∧
        ExecOf [[.store 0 1]] (storeFenceExtraRfOnInserted.comap f) ∧
        (storeFenceExtraRfOnInserted.comap f).Wf ∧ (storeFenceExtraRfOnInserted.comap f).SCConsistent
theorem exists_sc_execution_hb_unordered_needs_conflict :
    ¬ (skel loadStoreSameProg).Conflict ⟨1, by decide⟩ ⟨2, by decide⟩ ∧
      ¬ ∃ Y : Exec (layout loadStoreSameProg).length,
        ExecOf loadStoreSameProg Y ∧ Y.Wf ∧ Y.SCConsistent ∧
        Y.Conflict ⟨1, by decide⟩ ⟨2, by decide⟩ ∧
        ¬ Y.HB ⟨1, by decide⟩ ⟨2, by decide⟩ ∧ ¬ Y.HB ⟨2, by decide⟩ ⟨1, by decide⟩
theorem coBetweenReadsSameLoc_separates_coSameLoc_from_coKinds :   -- initW 0, R 0 0 0, R 1 0 0, co 1 → 2
    coBetweenReadsSameLoc.PoTrans ∧ coBetweenReadsSameLoc.PoWithinThread ∧
      coBetweenReadsSameLoc.PoTotal ∧ coBetweenReadsSameLoc.RfSameLoc ∧
      coBetweenReadsSameLoc.CoSameLoc ∧ ¬ coBetweenReadsSameLoc.CoKinds ∧
      coBetweenReadsSameLoc.FenceBetweenSharedWR ∧ coBetweenReadsSameLoc.PerLocSC ∧
      coBetweenReadsSameLoc.TsoGhbAcyclic ∧ coBetweenReadsSameLoc.SCConsistentErased
-- fenceBetweenSharedWR_needs_<h>, for each hypothesis h of the corollary: on the execution used by
-- fenceBetweenBothSharedWR_needs_<h>, the other seven corollary hypotheses hold, h fails, and
-- SCConsistentErased fails.
```

### Primary sources

Section, figure, lemma and quotation pointers in the cards were checked against the full texts
named here (author copies, the arXiv preprint, the Coq sources) before 2026-11-20; on 2026-11-20
the bibliographic records (authors, title, venue, volume, pages, DOI) of the paper subjects in
`REPORT.json` were rechecked, and the quoted `weakmemory/imm` definitions and lemma were
rechecked verbatim at the commit pinned below. No hardware was run and no unpublished source is
relied on.

- L. Lamport. How to Make a Multiprocessor Computer That Correctly Executes Multiprocess
  Programs. IEEE Trans. Computers C-28(9):690–691, 1979. DOI 10.1109/TC.1979.1675439.
- P. S. Sindhu, J.-M. Frailong, M. Cekleov. Formal Specification of Memory Models. In *Scalable
  Shared Memory Multiprocessors*, pp. 25–41, Springer, 1992. DOI 10.1007/978-1-4615-3604-8_2.
- D. Shasha, M. Snir. Efficient and Correct Execution of Parallel Programs that Share Memory. ACM
  TOPLAS 10(2):282–312, 1988. DOI 10.1145/42190.42277.
- S. V. Adve, M. D. Hill. Weak Ordering — A New Definition. ISCA 1990, pp. 2–14. DOI
  10.1145/325164.325100.
- S. Owens, S. Sarkar, P. Sewell. A Better x86 Memory Model: x86-TSO. TPHOLs 2009, LNCS 5674,
  pp. 391–407. DOI 10.1007/978-3-642-03359-9_27. Author copy:
  https://www.cl.cam.ac.uk/~pes20/weakmemory/x86tso-paper.tphols.pdf
- P. Sewell, S. Sarkar, S. Owens, F. Zappa Nardelli, M. O. Myreen. x86-TSO: A Rigorous and Usable
  Programmer's Model for x86 Multiprocessors. CACM 53(7):89–97, 2010. DOI
  10.1145/1785414.1785443. Author copy: https://www.cl.cam.ac.uk/~pes20/weakmemory/cacm.pdf
- S. Owens. Reasoning about the Implementation of Concurrency Abstractions on x86-TSO. ECOOP 2010,
  LNCS 6183, pp. 478–503. DOI 10.1007/978-3-642-14107-2_23. Author copy:
  https://www.cl.cam.ac.uk/~pes20/weakmemory/ecoop10.pdf
- J. Alglave, L. Maranget, S. Sarkar, P. Sewell. Fences in Weak Memory Models. CAV 2010, LNCS
  6174, pp. 258–272, DOI 10.1007/978-3-642-14295-6_25; extended version in Formal Methods in
  System Design 40(2):170–205, 2012, DOI 10.1007/s10703-011-0135-z.
- J. Alglave. A formal hierarchy of weak memory models. Formal Methods in System Design
  41(2):178–210, 2012. DOI 10.1007/s10703-012-0161-5.
- M. Batty, S. Owens, S. Sarkar, P. Sewell, T. Weber. Mathematizing C++ Concurrency. POPL 2011,
  pp. 55–66. DOI 10.1145/1926385.1926394.
- V. Vafeiadis, F. Zappa Nardelli. Verifying Fence Elimination Optimisations. SAS 2011, LNCS
  6887, pp. 146–162. DOI 10.1007/978-3-642-23702-7_14.
- J. Alglave, L. Maranget, M. Tautschnig. Herding Cats: Modelling, Simulation, Testing, and Data
  Mining for Weak Memory. ACM TOPLAS 36(2), Article 7, 2014. DOI 10.1145/2627752; preprint
  arXiv:1308.6810.
- J. Alglave, D. Kroening, V. Nimal, D. Poetzl. Don't Sit on the Fence: A Static Analysis
  Approach to Automatic Fence Insertion. CAV 2014, DOI 10.1007/978-3-319-08867-9_33; ACM TOPLAS
  39(2), Article 6, 2017, DOI 10.1145/3037273.
- Z. Sura, X. Fang, C.-L. Wong, S. P. Midkiff, J. Lee, D. Padua. Compiler Techniques for High
  Performance Sequentially Consistent Java Programs. PPoPP 2005, pp. 2–13. DOI
  10.1145/1065944.1065947.
- M. Wenzel. Transitive closure according to Roy-Floyd-Warshall. Archive of Formal Proofs, May
  2014. https://isa-afp.org/entries/Roy_Floyd_Warshall.html
- A. Podkopaev, O. Lahav, V. Vafeiadis. Bridging the Gap between Programming Languages and
  Hardware Weak Memory Models. PACMPL 3(POPL), Article 69, 2019. DOI 10.1145/3290382; Coq
  development https://github.com/weakmemory/imm at commit
  `4ca191b072df081dd3a6d9aa755959dc901b1bd0` (committed 2025-02-05): `src/hardware/TSO.v`,
  lines 48–50 (`Definition ppo := (⦗RW⦘ ⨾ sb ⨾ ⦗RW⦘) \ (fun x y => W x /\ R y).` and
  `Definition fence := ⦗RW⦘ ⨾ sb ⨾ ⦗MFENCE⦘ ⨾ sb ⨾ ⦗RW⦘.`), and `src/hardware/immToTSO.v`,
  lines 897–899 (`Lemma IMM_consistent (SCF : ⦗ W∩₁Sc ⦘ ⨾ sb ⨾ ⦗ R∩₁Sc⦘ ⊆ sb ⨾ ⦗MFENCE⦘ ⨾ sb):
  imm_consistent G.`). The development is cited for comparison only; no theorem here depends on
  it.
- V. Nagarajan, D. J. Sorin, M. D. Hill, D. A. Wood. A Primer on Memory Consistency and Cache
  Coherence, Second Edition. Synthesis Lectures on Computer Architecture, 2020. DOI
  10.2200/S00962ED2V01Y201910CAC049.

## Revalidation

The cheapest complete check rebuilds the Lean project, rescans the sources for banned
constructs, recomputes the axioms of every declaration, and recomputes every recorded statement
and closure hash. It needs `elan` (so that `lake` uses the toolchain pinned in
`lean/lean-toolchain`) and `python3`; it copies `lean/` to a temporary directory and never
modifies the package. From the package directory:

```sh
python3 support/revalidate.py .
```

It prints one `ok`/`FAIL` line per check and ends with `REVALIDATED` (exit status 0) or
`REVALIDATION FAILED`. What it hashes is described in its docstring and under **Evidence**:
the `repr` of each referenced declaration's type, and its definition closure.

Equivalent manual commands, using the package-included audit program
`lean/RevalidationAudit.lean` (outside the library target; it prints `#print axioms` for every
name referenced by `results.json` and a `STATEMENTS_JSON` line with each statement and
closure):

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/wmm_audit.txt
python3 - /tmp/wmm_audit.txt ../audit/statements.json <<'PY'
import hashlib, json, re, sys
out = open(sys.argv[1]).read()
rec = json.load(open(sys.argv[2]))["statements"]
allowed = {"propext", "Classical.choice", "Quot.sound"}
axs = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out)
axs += [(n, "") for n in re.findall(r"'([^']+)' does not depend on any axioms", out)]
bad = [n for n, a in axs if set(x.strip() for x in a.split(",") if x.strip()) - allowed]
stmts = json.loads(re.search(r"STATEMENTS_JSON (\[.*\])", out).group(1))
miss = [s["name"] for s in stmts if s.get("missing")]
drift = []
for s in stmts:
    r = rec.get(s["name"])
    if s.get("missing") or r is None:
        continue
    got = {"statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
           "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
           "closure_size": len(s["closure"])}
    if got != r:
        drift.append(s["name"])
hashed = sum(1 for s in stmts if s["name"] in rec)
print(f"{len(axs)} axiom reports, bad: {bad}; {len(stmts)} names, missing: {miss}; "
      f"{hashed} hashed, drift: {drift}")
sys.exit(1 if bad or miss or drift or len(axs) != len(stmts) else 0)
PY
```

The last command prints the number of axiom reports and names, and lists any declaration with a
disallowed axiom, any missing name, and any hash drift (exit status 0 iff there are none). A
passing run establishes only that the same statements, with the same definitions, are
kernel-checked under the pinned toolchain with standard axioms; whether the toy model is
faithful to x86-TSO or to any compiler must be re-argued from the sources (the `derived`
claims in **Findings**). To check one result after an edit, `lake env lean` a file containing
`import ToyWMM` and `#print axioms <name>` for that name, and compare its hashes as above.
