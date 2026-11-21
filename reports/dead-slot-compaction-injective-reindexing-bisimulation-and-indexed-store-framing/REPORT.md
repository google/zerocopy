# Dead-slot compaction in a toy control-flow language: injective reindexing, lockstep bisimulation, verification-condition transport, and indexed-store framing (Lean 4)

## Summary

This package is a kernel-checked Lean 4 toy model of a compiler pass that renumbers the local
slots of a function through a map from the slots that a liveness mask keeps into a (typically
smaller) index set, as in unused-local removal and stack-slot sharing, and of a verifier that
reasons about stores indexed by slot number. It states, with every hypothesis shown to be tight
in a stated witness class, when such a compaction is a lockstep bisimulation, when weakest
preconditions and verification conditions transport across it, how a Boolean liveness-certificate
checker relates to syntactic path liveness, and how an indexed store and an association-list store
compare under store laws, representation independence and a toy cost model.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding
claims about rustc MIR, LLVM, CompCert, CakeML or any register allocator. Connections to those
systems are separate `derived (modeling bridge)` claims under **Findings**.

One sentence (or short paragraph) per result, each restating its card's plain claim. The non-claims
of every result are listed first under **Boundaries**; read them before relying on a result.

* **`compact-bisim-no-clobber`** (theorem, T0): Let p be a program over N slots, L a liveness mask and π a map from the kept slots (those L declares live somewhere) into M slots, not necessarily injective. If L is a liveness certificate for p (every use at a point, i.e. every semantic read and every halt output, is of a slot L declares live there, and L is closed under the backward transfer), every debug read is of a slot L declares live there, for every assignment to a kept slot d no different kept slot declared live just after it has the same target as d under π, and likewise for every storage marker of a kept slot, then CompactRel (same program counter, and σ'(π i) = σ i for every kept slot i declared live at the current point) is a lockstep bisimulation between p and compact p L π for the small-step function step: from related states both programs step to related states with equal debug events, or both halt in related states emitting equal output values, or both are stuck. Control flow is arbitrary, including loops.
* **`compact-bisim-injective`** (theorem, T0): If π is injective, the mask L is a liveness certificate for p (every semantic read and halt output at a point is of a slot L declares live there, and L is closed under the backward transfer), and every debug read is of a slot L declares live there, then CompactRel is a lockstep bisimulation between p and compact p L π for step (equal debug events, equal halt outputs, related successor states), for arbitrary control flow; storage markers that reset slots are allowed.
* **`compact-kept-bisim-injective`** (theorem, T0): If π is injective and every semantic read, every halt output and every debug read of p is of a kept slot (a slot the mask L declares live at some point of p), then KeptRel (same program counter, and σ'(π i) = σ i for every kept slot i, live or not) is a lockstep bisimulation between p and compact p L π for step; no per-point condition on L (in particular no transfer closure) is assumed.
* **`entry-adequacy-iff-injective-on-live`** (characterization, T1): For any slot map π and any program point pc (the intended use is the entry point pc = 0): every original store σ has some compacted store σ' that is CompactRel-related to it at pc if and only if π is injective on the kept slots declared live at pc; when π is injective there, the push-forward pushStore π pc σ is such a σ'. Independently of injectivity, every compacted store σ' is CompactRel-related at pc to its pull-back pullStore π σ' (which reads dropped slots as 0).
* **`wp-transport-no-clobber`** (theorem, T1): If the mask L is a liveness certificate for p (reads and halt outputs live, closed under the backward transfer), π satisfies NoAssignClobber and NoMarkerClobber (in particular if π is injective), and the postconditions Q (original) and Q' (compacted) agree on every pair of CompactRel-related halting states of p, then for every CompactRel-related pair of states the total-correctness weakest precondition wp, defined from the fuel-bounded execution exec, of p for Q holds if and only if that of compact p L π for Q' holds; debug reads play no role.
* **`transportable-postconditions-characterization`** (characterization, T1): For any slot map π: if a postcondition Q depends, at every halt of p, only on the slots the mask declares live there, then pullPost π Q (Q evaluated on the pulled-back store) agrees with Q on every pair of CompactRel-related halting states. If moreover π is injective on the live slots at each halt, the converse also holds: Q has some compacted counterpart Q' agreeing with it on all related halting states if and only if Q depends only on live slots at every halt.
* **`vc-transfer-original-to-compacted`** (theorem, T1): If the mask L is a liveness certificate for p, π satisfies NoAssignClobber and NoMarkerClobber, and Q depends only on live slots at every halt, then: if for every store σ, Pre σ implies wp p Q from the entry state with store σ, then for every compacted store σ', Pre (pullStore π σ') implies wp (compact p L π) (pullPost π Q) from the entry state with store σ'. No injectivity at entry and no condition on Pre is assumed; the price is that the transported precondition Pre ∘ pullStore π can be unsatisfiable although Pre is satisfiable (see the non-claims).
* **`vc-transfer-compacted-to-original`** (theorem, T1): If the mask L is a liveness certificate for p, π satisfies NoAssignClobber and NoMarkerClobber and is injective on the kept slots live at entry, Pre depends only on kept entry-live slots, and Q depends only on live slots at every halt, then: if for every compacted store σ', Pre (pullStore π σ') implies wp (compact p L π) (pullPost π Q) from the entry state with store σ', then for every store σ, Pre σ implies wp p Q from the entry state with store σ.
* **`non-live-read-breaks-compaction`** (counterexample, T1): For p = [x1 := x0; halt [x1]] over 2 slots, the mask LR that declares only x1 live and only at the halt (it omits x0 at the read but is transfer closed), and the injective map πR of the kept slot x1 onto one slot: every hypothesis of compact-bisim-no-clobber, compact-bisim-injective and wp-transport-no-clobber except ReadsLive holds, and each conclusion fails.
* **`non-transfer-closed-mask-breaks-compaction`** (counterexample, T1): For p = [nop; halt [x0]] over 1 slot with the mask LT that declares x0 live at the halt but not before the nop (LT satisfies ReadsLive but is not transfer closed), the identity compaction satisfies every other hypothesis of compact-bisim-no-clobber, compact-bisim-injective and wp-transport-no-clobber, and each conclusion fails.
* **`merging-simultaneously-live-slots-breaks-compaction`** (counterexample, T1): For p = [x1 := 5; halt [x0, x1]] over 2 slots with its path-liveness mask LA, the map πAm merging x0 and x1 into one slot satisfies the certificate, debug and marker conditions but neither injectivity nor NoAssignClobber, and the conclusions of compact-bisim-no-clobber, compact-bisim-injective, compact-kept-bisim-injective and wp-transport-no-clobber fail.
* **`marker-reset-breaks-slot-sharing`** (counterexample, T1): For p = [StorageLive(x1); x1 := x0; halt [x1]] over 2 slots with its path-liveness mask LM, the map πMm merging x0 and x1 into one slot satisfies the certificate, debug and NoAssignClobber conditions but not NoMarkerClobber, and the conclusions of compact-bisim-no-clobber and wp-transport-no-clobber fail.
* **`dead-debug-read-breaks-lockstep-bisimulation`** (counterexample, T1): For p = [dbg x0; halt []] over 1 slot with the empty mask (nothing is live, because debug reads are not liveness uses) and the empty compaction πD, every hypothesis of compact-bisim-no-clobber, compact-bisim-injective and compact-kept-bisim-injective except the debug condition holds, and each conclusion fails.
* **`liveness-certificate-overapproximates`** (theorem, T0): If a mask L satisfies the gen inequality for p (every use at a point, i.e. every semantic read and halt output, is of a slot L declares live there) and the transfer inequality (a slot declared live at a successor and not overwritten by the instruction is declared live before it), and slot i is path-live at pc (some control-flow path from pc reaches a use of i, with no overwrite of i before that use), then L pc i = true.
* **`liveness-checker-characterization-and-soundness`** (theorem, T0): The Boolean checker checkLive accepts a mask L for p exactly when L satisfies both certificate inequalities (ReadsLive and TransferClosed). Consequently, if checkLive accepts L and slot i is path-live at pc, then L pc i = true.
* **`liveness-checker-rejects-omitted-path-live-slot`** (theorem, T0): If slot i is path-live at pc in p and the mask L omits it there (L pc i = false), then checkLive p L = false.
* **`path-liveness-least-certificate`** (theorem, T0): For every program p, the (noncomputable) path-liveness mask pathLiveMask p satisfies both certificate inequalities, is accepted by checkLive, and is pointwise below every mask that satisfies both inequalities; so it is the least certificate.
* **`store-laws-on-common-domain`** (theorem, T0): For every N and V, the indexed store funOps N V (a total function Fin N → V) satisfies GetPutSame, GetPutOther, PutGetId and PutPut. For every default d, the association-list store alistOps N d (first match wins; put replaces the first match or appends) satisfies GetPutSame, GetPutOther and PutPut on all lists, and PutGetId on complete lists (lists containing every key). When N ≥ 1 the empty list is incomplete and violates PutGetId (writing back the value read for slot 0 appends an entry); when N = 0, PutGetId holds.
* **`certificate-checker-representation-independence`** (theorem, T0): For the replay checker runCheck, which uses the store only through get and put: if two store implementations both satisfy GetPutSame and GetPutOther and the initial stores have the same view (equal get on every key), then the checker gives the same verdict on every command list. In particular, if the view of an association list l with default d is the indexed store σ (alistGet d l = σ), then the indexed store started from σ and the association-list store started from l give the same verdict on every command list.
* **`alist-checker-toy-cost-theta-SL`** (theorem, T0): Toy cost-model theorem (not real performance), counting one primitive operation per association-list cell scanned by each get and put that runCheck performs (runCost stops at the first failing check, as runCheck does): (a) for the family of S increments of the last of K = L + 1 slots, run from the complete key-ordered list of length K, the checker scans exactly 2 S K cells; (b) for any command list c run from a complete association list l, it scans at most 2 · c.length · l.length cells. Hence on that family the cost is Θ(S · K), with K the number of slots.
* **`unit-cost-checker-toy-cost-O-S`** (theorem, T0): Toy cost-model theorem (not real performance): under the unit cost model unitCost, which charges one primitive operation per get and per put (the usual model of an array indexed by slot number), the run of runCheck over any store implementation and any command list c costs at most 2 · c.length operations, independent of the number of slots, and exactly 2 S on the family of S increments. The bound comes from the cost model alone: it holds for every StoreOps, including the association-list store; the indexed store funOps is the intended instantiation.

## Applicability

### Model fidelity

This is a toy model (namespace `Toy.SlotCompact`). The definitions are meant to capture the shape
of two things:

* a compiler pass that renumbers a function's local slots: removal of unused locals followed by
  renumbering (for example rustc's MIR `SimplifyLocals`), and sharing of one storage slot between
  locals whose live ranges do not interfere (for example LLVM's `StackColoring` and
  `StackSlotColoring`, or register colouring);
* a verification pipeline that states pre- and postconditions over a store indexed by slot number
  and must move them across such a renumbering.

The toy language has `N` slots holding natural numbers; pure expressions (`const`, `slot`, `add`);
instructions `assign`, `storageLive`, `storageDead` (both markers reset the slot to `0`), `dbg`
(emits the value of an expression as an observable event and is not a liveness use), `nop`,
`branch` (two-way jump on zero) and `halt outs` (stops and emits the values of the listed slots).
`step` is a deterministic small-step function. A liveness mask `L : Nat → Fin N → Bool` is
*claimed* by the pass and *checked* (the certificate conditions `ReadsLive` and `TransferClosed`),
not computed. A compaction is a map `π` from the kept slots (those `L` declares live somewhere) to
`Fin M`; `compact` rewrites every instruction at the same program point (erased instructions become
`nop`). The weakest precondition `wp` is total correctness over the fuel-bounded executor `exec`.
The core definitions are quoted verbatim under **Findings / Definitions**, and the concrete instances
and the other declarations this report names under **Findings / Auxiliary declarations cited by name**.

Model–system relation: none proved. No embedding, abstraction or simulation between the toy and any
real compiler pass, intermediate representation or verifier is stated or proved; the bisimulations
proved here relate two toy programs (`p` and `compact p L π`). These are statements about the toy
model; they neither establish nor refute the corresponding claims about the systems named above.

Known gaps between the toy and real systems (each is a modeling choice, not a finding):

* no memory, pointers, address-taken slots, projections or aggregates; no calls, exceptions or
  concurrency; values are natural numbers;
* storage markers reset the slot to `0`; real IRs make access to dead storage undefined behaviour
  (for example LLVM's `lifetime.end`), which is not modeled;
* `dbg` reads are observable but do not extend live ranges; rustc instead treats locals referenced
  by debug info as always used, so the debug hypotheses (`DbgReadsLive`, `DbgReadsKept`) model a
  different policy;
* the compacted program keeps a `nop` at every erased instruction, so program points coincide;
  passes that delete instructions and renumber program points are not covered;
* `ReadsKept` is a single-pass syntactic condition, and `PathLive` counts the operand of an
  assignment as a use even when the assigned slot is dead (it is not strong liveness); the
  fixed-point removal of chains of dead assignments performed by rustc's `SimplifyLocals` is not
  modeled;
* the interference conditions `NoAssignClobber` and `NoMarkerClobber` are a write-versus-live-after
  formulation relative to the given mask; no equivalence with live-interval overlap tests is
  claimed;
* the cost model counts get/put operations (unit cost, or cells scanned in an association list);
  it is not a performance measurement.

### Toolchain and project

* Lean `leanprover/lean4` release `v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`); no Mathlib, no
  Lake dependencies (`lakefile.toml` declares one `[[lean_lib]]`, `ToySlotCompact`, and no
  `[[require]]`).
* Library `ToySlotCompact`, 12 modules under `lean/ToySlotCompact/`: `Basic` (language, masks,
  compaction, relations), `Bisim` (bisimulation theorems, entry adequacy), `WP` (weakest
  preconditions and transport), `Liveness` (path liveness, checker), `Stores` (store laws,
  representation independence, cost model), `Decide` (Boolean checks used to discharge concrete
  instances), `Instances`, `Instances2` (concrete programs), `Counterexamples`, `NonVacuity`,
  `Boundaries` (theorems cited by non-claims), `Examples` (positive and negative examples for every
  definition).
* `lean/RevalidationAudit.lean` (outside the library target) prints the axioms of every
  declaration referenced by `results.json`.

### Relation between the subjects

The Lean toolchain is the subject that checks every `execution (Lean kernel check)` finding. The
papers and the pinned revisions of CakeML, CompCert, llvm-project and rust-lang/rust in
`REPORT.json` are prior art; each comparison with them is a separate `derived (modeling bridge)`
claim whose reasoning is stated where it is made. None of them is modeled exactly.

## Findings

Every theorem below is an `execution (Lean kernel check)` finding: it builds under the pinned
toolchain and its axioms are among `propext`, `Classical.choice`, `Quot.sound` (see **Evidence**).
Statements are quoted verbatim from the Lean sources, with the file and line range in a `--`
comment at the top of each block; proofs are elided as `:= …`. Implicit size parameters such as
`{N M : Nat}` come from the `variable` line of the cited file, quoted under **Definitions**. A block
introduced by the word "Unfolded" is a Lean term that elaborates, in the theorem's own context, to
a proposition definitionally equal to the quoted statement (or to its conclusion).

In every hypothesis ledger, `tight` means: the named counterexample theorem exhibits an instance,
in the stated witness class, that satisfies all the other hypotheses of the theorem the hypothesis
belongs to and in which the conclusion fails. It does not mean that the hypothesis is necessary
outside that class; hypotheses known not to be necessary in general are listed under
**Boundaries**.

### Definitions

Key definitions, quoted verbatim (with their docstrings omitted). The card statements below use them unchanged.

**Language and semantics.** Slots, expressions, instructions and the deterministic small-step function. `Res.ev` (in `Bisim.lean`, whose `variable` line below supplies the implicit `N`) projects the debug event of a step result: the event of a `running` result, and `none` for `halted` and `stuck`. The `variable` lines give the implicit size parameters of the theorems in each file.

```lean
-- lean/ToySlotCompact/Basic.lean:16-16
abbrev Store (N : Nat) := Fin N → Nat

-- lean/ToySlotCompact/Basic.lean:19-20
def upd {N : Nat} (σ : Store N) (i : Fin N) (v : Nat) : Store N :=
  fun j => if j = i then v else σ j

-- lean/ToySlotCompact/Basic.lean:30-34
inductive Expr (N : Nat) where
  | const (n : Nat)
  | slot (i : Fin N)
  | add (a b : Expr N)
  deriving DecidableEq, Repr

-- lean/ToySlotCompact/Basic.lean:37-40
def Expr.eval {N : Nat} (σ : Store N) : Expr N → Nat
  | .const n => n
  | .slot i => σ i
  | .add a b => a.eval σ + b.eval σ

-- lean/ToySlotCompact/Basic.lean:43-46
def Expr.reads {N : Nat} : Expr N → Fin N → Bool
  | .const _, _ => false
  | .slot j, i => decide (j = i)
  | .add a b, i => a.reads i || b.reads i

-- lean/ToySlotCompact/Basic.lean:49-52
def Expr.subst {N M : Nat} (f : Fin N → Expr M) : Expr N → Expr M
  | .const n => .const n
  | .slot i => f i
  | .add a b => .add (a.subst f) (b.subst f)

-- lean/ToySlotCompact/Basic.lean:76-84
inductive Instr (N : Nat) where
  | assign (d : Fin N) (e : Expr N)
  | storageLive (i : Fin N)
  | storageDead (i : Fin N)
  | dbg (e : Expr N)
  | nop
  | branch (c : Expr N) (t f : Nat)
  | halt (outs : List (Fin N))
  deriving DecidableEq, Repr

-- lean/ToySlotCompact/Basic.lean:87-87
abbrev Prog (N : Nat) := List (Instr N)

-- lean/ToySlotCompact/Basic.lean:90-92
structure State (N : Nat) where
  pc : Nat
  st : Store N

-- lean/ToySlotCompact/Basic.lean:96-99
inductive Res (N : Nat) where
  | running (s : State N) (ev : Option Nat)
  | halted (s : State N) (out : List Nat)
  | stuck

-- lean/ToySlotCompact/Bisim.lean:159-161
def Res.ev : Res N → Option Nat
  | .running _ e => e
  | _ => none

-- lean/ToySlotCompact/Basic.lean:102-109
def stepInstr {N : Nat} : Instr N → State N → Res N
  | .assign d e, ⟨pc, σ⟩ => .running ⟨pc + 1, upd σ d (e.eval σ)⟩ none
  | .storageLive i, ⟨pc, σ⟩ => .running ⟨pc + 1, upd σ i 0⟩ none
  | .storageDead i, ⟨pc, σ⟩ => .running ⟨pc + 1, upd σ i 0⟩ none
  | .dbg e, ⟨pc, σ⟩ => .running ⟨pc + 1, σ⟩ (some (e.eval σ))
  | .nop, ⟨pc, σ⟩ => .running ⟨pc + 1, σ⟩ none
  | .branch c t f, ⟨_, σ⟩ => .running ⟨if c.eval σ = 0 then f else t, σ⟩ none
  | .halt outs, s => .halted s (outs.map s.st)

-- lean/ToySlotCompact/Basic.lean:112-115
def step {N : Nat} (p : Prog N) (s : State N) : Res N :=
  match p[s.pc]? with
  | none => .stuck
  | some ins => stepInstr ins s

-- lean/ToySlotCompact/Bisim.lean:9
variable {N M : Nat}

-- lean/ToySlotCompact/WP.lean:9
variable {N M : Nat}

-- lean/ToySlotCompact/Liveness.lean:9
variable {N : Nat}

-- lean/ToySlotCompact/Stores.lean:16
variable {S S₁ S₂ V : Type} {N : Nat}
```

**Liveness masks and certificate conditions.** `ReadsLive` is the gen half and `TransferClosed` the transfer half of the backward liveness inequality; together they are what this package calls a liveness certificate. Debug reads are excluded from `Instr.uses` and are constrained separately.

```lean
-- lean/ToySlotCompact/Basic.lean:128-128
abbrev Ann (N : Nat) := Nat → Fin N → Bool

-- lean/ToySlotCompact/Basic.lean:131-135
def Instr.uses {N : Nat} : Instr N → Fin N → Bool
  | .assign _ e, i => e.reads i
  | .branch c _ _, i => c.reads i
  | .halt outs, i => decide (i ∈ outs)
  | _, _ => false

-- lean/ToySlotCompact/Basic.lean:138-142
def Instr.defs {N : Nat} : Instr N → Fin N → Bool
  | .assign d _, i => decide (d = i)
  | .storageLive j, i => decide (j = i)
  | .storageDead j, i => decide (j = i)
  | _, _ => false

-- lean/ToySlotCompact/Basic.lean:145-148
def Instr.succs {N : Nat} (pc : Nat) : Instr N → List Nat
  | .branch _ t f => [t, f]
  | .halt _ => []
  | _ => [pc + 1]

-- lean/ToySlotCompact/Basic.lean:152-153
def ReadsLive {N : Nat} (p : Prog N) (L : Ann N) : Prop :=
  ∀ (pc : Nat) (ins : Instr N), p[pc]? = some ins → ∀ i, ins.uses i = true → L pc i = true

-- lean/ToySlotCompact/Basic.lean:158-160
def TransferClosed {N : Nat} (p : Prog N) (L : Ann N) : Prop :=
  ∀ (pc : Nat) (ins : Instr N), p[pc]? = some ins → ∀ s ∈ ins.succs pc, ∀ i, L s i = true → ins.defs i = false →
    L pc i = true

-- lean/ToySlotCompact/Basic.lean:163-164
def DbgReadsLive {N : Nat} (p : Prog N) (L : Ann N) : Prop :=
  ∀ (pc : Nat) (e : Expr N), p[pc]? = some (.dbg e) → ∀ i, e.reads i = true → L pc i = true

-- lean/ToySlotCompact/Basic.lean:168-169
def Kept {N : Nat} (p : Prog N) (L : Ann N) (i : Fin N) : Bool :=
  (List.range p.length).any (fun pc => L pc i)

-- lean/ToySlotCompact/Basic.lean:179-180
def ReadsKept {N : Nat} (p : Prog N) (L : Ann N) : Prop :=
  ∀ (pc : Nat) (ins : Instr N), p[pc]? = some ins → ∀ i, ins.uses i = true → Kept p L i = true

-- lean/ToySlotCompact/Basic.lean:183-184
def DbgReadsKept {N : Nat} (p : Prog N) (L : Ann N) : Prop :=
  ∀ (pc : Nat) (e : Expr N), p[pc]? = some (.dbg e) → ∀ i, e.reads i = true → Kept p L i = true
```

**Compaction.** A compaction map is defined on the kept slots only; dropped slots read as the constant `0` in rewritten expressions, and writes to and markers of dropped slots become `nop`.

```lean
-- lean/ToySlotCompact/Basic.lean:199-200
abbrev Compaction {N : Nat} (p : Prog N) (L : Ann N) (M : Nat) :=
  {i : Fin N // Kept p L i = true} → Fin M

-- lean/ToySlotCompact/Basic.lean:203-205
def Compaction.get? {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M) (i : Fin N) :
    Option (Fin M) :=
  if h : Kept p L i = true then some (π ⟨i, h⟩) else none

-- lean/ToySlotCompact/Basic.lean:217-221
def Compaction.slotExpr {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M)
    (i : Fin N) : Expr M :=
  match π.get? i with
  | some k => .slot k
  | none => .const 0

-- lean/ToySlotCompact/Basic.lean:224-226
def compactExpr {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M) (e : Expr N) :
    Expr M :=
  e.subst π.slotExpr

-- lean/ToySlotCompact/Basic.lean:231-248
def compactInstr {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M) :
    Instr N → Instr M
  | .assign d e =>
    match π.get? d with
    | some k => .assign k (compactExpr π e)
    | none => .nop
  | .storageLive i =>
    match π.get? i with
    | some k => .storageLive k
    | none => .nop
  | .storageDead i =>
    match π.get? i with
    | some k => .storageDead k
    | none => .nop
  | .dbg e => .dbg (compactExpr π e)
  | .nop => .nop
  | .branch c t f => .branch (compactExpr π c) t f
  | .halt outs => .halt (outs.filterMap π.get?)

-- lean/ToySlotCompact/Basic.lean:251-252
def compact {N M : Nat} (p : Prog N) (L : Ann N) (π : Compaction p L M) : Prog M :=
  p.map (compactInstr π)
```

**Relations, bisimulation and interference conditions.** `ResRel` compares debug events and halt outputs; `ResRelS` ignores debug events but still compares outputs.

```lean
-- lean/ToySlotCompact/Basic.lean:272-274
def CompactRel {N M : Nat} (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (s : State N) (s' : State M) : Prop :=
  s'.pc = s.pc ∧ ∀ (i : Fin N) (h : Kept p L i = true), L s.pc i = true → s'.st (π ⟨i, h⟩) = s.st i

-- lean/ToySlotCompact/Basic.lean:277-279
def KeptRel {N M : Nat} (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (s : State N) (s' : State M) : Prop :=
  s'.pc = s.pc ∧ ∀ (i : Fin N) (h : Kept p L i = true), s'.st (π ⟨i, h⟩) = s.st i

-- lean/ToySlotCompact/Basic.lean:283-287
def ResRel {N M : Nat} (R : State N → State M → Prop) : Res N → Res M → Prop
  | .running s e, .running s' e' => e = e' ∧ R s s'
  | .halted s o, .halted s' o' => o = o' ∧ R s s'
  | .stuck, .stuck => True
  | _, _ => False

-- lean/ToySlotCompact/Basic.lean:291-295
def ResRelS {N M : Nat} (R : State N → State M → Prop) : Res N → Res M → Prop
  | .running s _, .running s' _ => R s s'
  | .halted s o, .halted s' o' => o = o' ∧ R s s'
  | .stuck, .stuck => True
  | _, _ => False

-- lean/ToySlotCompact/Basic.lean:301-302
def LockstepBisim {N M : Nat} (p : Prog N) (q : Prog M) (R : State N → State M → Prop) : Prop :=
  ∀ s s', R s s' → ResRel R (step p s) (step q s')

-- lean/ToySlotCompact/Basic.lean:306-307
def SilentBisim {N M : Nat} (p : Prog N) (q : Prog M) (R : State N → State M → Prop) : Prop :=
  ∀ s s', R s s' → ResRelS R (step p s) (step q s')

-- lean/ToySlotCompact/Basic.lean:319-321
def NoAssignClobber {N M : Nat} (p : Prog N) (L : Ann N) (π : Compaction p L M) : Prop :=
  ∀ (pc : Nat) (d : Fin N) (e : Expr N), p[pc]? = some (.assign d e) → ∀ (hd : Kept p L d = true) (i : Fin N)
    (hi : Kept p L i = true), i ≠ d → L (pc + 1) i = true → π ⟨i, hi⟩ ≠ π ⟨d, hd⟩

-- lean/ToySlotCompact/Basic.lean:324-327
def NoMarkerClobber {N M : Nat} (p : Prog N) (L : Ann N) (π : Compaction p L M) : Prop :=
  ∀ (pc : Nat) (j : Fin N), (p[pc]? = some (.storageLive j) ∨ p[pc]? = some (.storageDead j)) →
    ∀ (hj : Kept p L j = true) (i : Fin N) (hi : Kept p L i = true), i ≠ j →
      L (pc + 1) i = true → π ⟨i, hi⟩ ≠ π ⟨j, hj⟩

-- lean/ToySlotCompact/Basic.lean:330-332
def InjOnLiveAt {N M : Nat} (p : Prog N) (L : Ann N) (π : Compaction p L M) (pc : Nat) : Prop :=
  ∀ (i j : Fin N) (hi : Kept p L i = true) (hj : Kept p L j = true),
    L pc i = true → L pc j = true → π ⟨i, hi⟩ = π ⟨j, hj⟩ → i = j

-- lean/ToySlotCompact/Basic.lean:352-356
def pullStore {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M) (σ' : Store M) :
    Store N :=
  fun i => match π.get? i with
    | some k => σ' k
    | none => 0

-- lean/ToySlotCompact/Basic.lean:360-364
def pushStore {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M) (pc : Nat)
    (σ : Store N) : Store M :=
  fun k => match (List.finRange N).find? (fun i => L pc i && decide (π.get? i = some k)) with
    | some i => σ i
    | none => 0
```

**Weakest preconditions and transport.**

```lean
-- lean/ToySlotCompact/WP.lean:14-20
def exec (p : Prog N) : Nat → State N → Option (State N)
  | 0, _ => none
  | n + 1, s =>
    match step p s with
    | .running s' _ => exec p n s'
    | .halted s' _ => some s'
    | .stuck => none

-- lean/ToySlotCompact/WP.lean:23-23
def IsHalt (p : Prog N) (pc : Nat) : Prop := ∃ outs, p[pc]? = some (Instr.halt outs)

-- lean/ToySlotCompact/WP.lean:27-28
def wp (p : Prog N) (Q : State N → Prop) (s : State N) : Prop :=
  ∃ n sf, exec p n s = some sf ∧ Q sf

-- lean/ToySlotCompact/WP.lean:111-113
def PostCorr (p : Prog N) (L : Ann N) (π : Compaction p L M) (Q : State N → Prop)
    (Q' : State M → Prop) : Prop :=
  ∀ s s', IsHalt p s.pc → CompactRel p L π s s' → (Q s ↔ Q' s')

-- lean/ToySlotCompact/WP.lean:128-130
def DependsOnlyOnLive (p : Prog N) (L : Ann N) (Q : State N → Prop) : Prop :=
  ∀ s t : State N, IsHalt p s.pc → s.pc = t.pc → (∀ i, L s.pc i = true → s.st i = t.st i) →
    (Q s ↔ Q t)

-- lean/ToySlotCompact/WP.lean:133-135
def pullPost {p : Prog N} {L : Ann N} (π : Compaction p L M) (Q : State N → Prop) :
    State M → Prop :=
  fun s' => Q ⟨s'.pc, pullStore π s'.st⟩

-- lean/ToySlotCompact/WP.lean:173-174
def DependsOnlyOnEntryLive (p : Prog N) (L : Ann N) (Pre : Store N → Prop) : Prop :=
  ∀ σ τ : Store N, (∀ i, L 0 i = true → Kept p L i = true → σ i = τ i) → (Pre σ ↔ Pre τ)
```

**Path liveness and the Boolean checker.** `PathLive` is syntactic path liveness: paths follow every syntactic successor, and an operand of an assignment counts as a use even when the assigned slot is dead afterwards.

```lean
-- lean/ToySlotCompact/Liveness.lean:18-23
inductive PathLive (p : Prog N) : Nat → Fin N → Prop
  | use {pc : Nat} {ins : Instr N} {i : Fin N} :
      p[pc]? = some ins → ins.uses i = true → PathLive p pc i
  | pass {pc : Nat} {ins : Instr N} {s : Nat} {i : Fin N} :
      p[pc]? = some ins → s ∈ ins.succs pc → ins.defs i = false → PathLive p s i →
      PathLive p pc i

-- lean/ToySlotCompact/Liveness.lean:34-38
def checkReads (p : Prog N) (L : Ann N) : Bool :=
  (List.range p.length).all fun pc =>
    match p[pc]? with
    | none => true
    | some ins => (List.finRange N).all fun i => !ins.uses i || L pc i

-- lean/ToySlotCompact/Liveness.lean:41-46
def checkTransfer (p : Prog N) (L : Ann N) : Bool :=
  (List.range p.length).all fun pc =>
    match p[pc]? with
    | none => true
    | some ins => (List.finRange N).all fun i =>
        (ins.succs pc).all (fun s => !L s i || ins.defs i || L pc i)

-- lean/ToySlotCompact/Liveness.lean:50-50
def checkLive (p : Prog N) (L : Ann N) : Bool := checkReads p L && checkTransfer p L

-- lean/ToySlotCompact/Liveness.lean:127-128
noncomputable def pathLiveMask (p : Prog N) : Ann N :=
  fun pc i => @decide (PathLive p pc i) (Classical.propDecidable _)
```

**Stores, laws, checker and cost model.**

```lean
-- lean/ToySlotCompact/Stores.lean:12-14
structure StoreOps (S : Type) (N : Nat) (V : Type) where
  get : S → Fin N → V
  put : S → Fin N → V → S

-- lean/ToySlotCompact/Stores.lean:19-19
def GetPutSame (ops : StoreOps S N V) : Prop := ∀ s k v, ops.get (ops.put s k v) k = v

-- lean/ToySlotCompact/Stores.lean:22-23
def GetPutOther (ops : StoreOps S N V) : Prop :=
  ∀ s k k' v, k' ≠ k → ops.get (ops.put s k v) k' = ops.get s k'

-- lean/ToySlotCompact/Stores.lean:27-27
def PutGetId (ops : StoreOps S N V) : Prop := ∀ s k, ops.put s k (ops.get s k) = s

-- lean/ToySlotCompact/Stores.lean:30-30
def PutPut (ops : StoreOps S N V) : Prop := ∀ s k v w, ops.put (ops.put s k v) k w = ops.put s k w

-- lean/ToySlotCompact/Stores.lean:33-35
def funOps (N : Nat) (V : Type) : StoreOps (Fin N → V) N V where
  get σ k := σ k
  put σ k v := fun j => if j = k then v else σ j

-- lean/ToySlotCompact/Stores.lean:38-40
def alistGet (d : V) : List (Fin N × V) → Fin N → V
  | [], _ => d
  | (k', v) :: l, k => if k' = k then v else alistGet d l k

-- lean/ToySlotCompact/Stores.lean:43-45
def alistPut : List (Fin N × V) → Fin N → V → List (Fin N × V)
  | [], k, v => [(k, v)]
  | (k', v') :: l, k, v => if k' = k then (k, v) :: l else (k', v') :: alistPut l k v

-- lean/ToySlotCompact/Stores.lean:48-48
def alistOps (N : Nat) (d : V) : StoreOps (List (Fin N × V)) N V := ⟨alistGet d, alistPut⟩

-- lean/ToySlotCompact/Stores.lean:51-51
def Complete (l : List (Fin N × V)) : Prop := ∀ k : Fin N, k ∈ l.map Prod.fst

-- lean/ToySlotCompact/Stores.lean:128-129
def consPutOps (N : Nat) : StoreOps (List (Fin N × Nat)) N Nat :=
  ⟨alistGet 0, fun l k v => (k, v) :: l⟩

-- lean/ToySlotCompact/Stores.lean:158-161
inductive Cmd (N : Nat) where
  | incr (dst src : Fin N) (c : Nat)
  | check (k : Fin N) (v : Nat)
  deriving DecidableEq, Repr

-- lean/ToySlotCompact/Stores.lean:165-168
def runCheck (ops : StoreOps S N Nat) : S → List (Cmd N) → Bool
  | _, [] => true
  | s, .incr d src c :: rest => runCheck ops (ops.put s d (ops.get s src + c)) rest
  | s, .check k v :: rest => decide (ops.get s k = v) && runCheck ops s rest

-- lean/ToySlotCompact/Stores.lean:202-204
structure CostModel (S : Type) (N : Nat) where
  getCost : S → Fin N → Nat
  putCost : S → Fin N → Nat

-- lean/ToySlotCompact/Stores.lean:208-213
def runCost (ops : StoreOps S N Nat) (cm : CostModel S N) : S → List (Cmd N) → Nat
  | _, [] => 0
  | s, .incr d src c :: rest =>
    cm.getCost s src + cm.putCost s d + runCost ops cm (ops.put s d (ops.get s src + c)) rest
  | s, .check k v :: rest =>
    cm.getCost s k + (if ops.get s k = v then runCost ops cm s rest else 0)

-- lean/ToySlotCompact/Stores.lean:217-217
def unitCost (S : Type) (N : Nat) : CostModel S N := ⟨fun _ _ => 1, fun _ _ => 1⟩

-- lean/ToySlotCompact/Stores.lean:220-222
def scanCost : List (Fin N) → Fin N → Nat
  | [], _ => 0
  | k' :: l, k => if k' = k then 1 else 1 + scanCost l k

-- lean/ToySlotCompact/Stores.lean:226-227
def alistCost (N : Nat) (V : Type) : CostModel (List (Fin N × V)) N :=
  ⟨fun l k => scanCost (l.map Prod.fst) k, fun l k => scanCost (l.map Prod.fst) k⟩

-- lean/ToySlotCompact/Stores.lean:308-308
def famAlist (L : Nat) : List (Fin (L + 1) × Nat) := (List.finRange (L + 1)).map fun k => (k, 0)

-- lean/ToySlotCompact/Stores.lean:311-311
def famScript (S L : Nat) : List (Cmd (L + 1)) := List.replicate S (.incr (Fin.last L) (Fin.last L) 1)
```

### Concrete instances

The concrete programs used by witnesses and counterexamples, with the Lean names of their masks and
maps (informal notation; this table is prose, and the Lean definitions in `Instances.lean`,
`Instances2.lean` and, for `pDisj`, `Boundaries.lean` are authoritative; they are quoted verbatim in
the counterexample cards or under **Auxiliary declarations cited by name** below). `xk` is slot `k`.
A map described as empty has an empty domain: its mask declares no slot live anywhere, so no slot is
kept.

| name | program (informal) | mask | map | role |
| --- | --- | --- | --- | --- |
| `pA` | `x1 := 5; halt [x0, x1]` | `LA`: path liveness | `πAm`: merge (M = 1) | assignment clobber |
| `pM` | `StorageLive(x1); x1 := x0; halt [x1]` | `LM`: path liveness | `πMm`: merge | marker clobber |
| `pR` | `x1 := x0; halt [x1]` | `LR`: omits `x0` at the read | `πR`: onto 1 slot | non-live read |
| `pT` | `nop; halt [x0]` | `LT`: omits `x0` before `nop` | `πT`: identity | not transfer closed |
| `pD` | `dbg x0; halt []` | `LD`: empty | `πD`: empty | dead debug read |
| `pE` | `halt [x0, x1]` | `LE`: both live | `πEm`: merge | entry merge |
| `pE3` | `halt [x0, x1]` over 3 slots | `LE3`: `{x0, x1}` | `πE3`: merge | postcondition class |
| `pV` | `x1 := 5; nop; halt [x0, x1]` | `LV`: omits `x0` before the halt | `πVm`: merge | VC, transfer closure |
| `pX` | `x1 := 5; x1 := x0; halt [x1]` | `LX`: omits `x0` at the read | `πXm`: merge | forward VC, non-live read |
| `pK` | `x0 := 1; halt []` | `LK`: empty | `πK`: empty | forward VC, dead postcondition |
| `pH` | `halt []` | `LH`: empty | `πH`: empty | dead pre/postconditions |
| `pU` | `halt [x0]` | `LU`: empty | — | certificate, gen half |
| `pS` | `x2 := 9; StorageLive(x1); x1 := x0+1; dbg x1; StorageDead(x0); halt [x1]` | `LS`: path liveness | `πS`: injective, drops `x2` | positive (straight line) |
| `pC` | `x2 := 9; x1 := x0+1; dbg x1; halt [x1]` | `LC`: path liveness | `πCm`: merge `x0`, `x1` | positive (sharing) |
| `pB` | `0: if x0 goto 1 else 4; 1: x1 := x1+2; 2: x0 := 0; 3: goto 0; 4: halt [x1]` | `LB`: path liveness | `πB`: injective, drops `x2` | positive (loop) |
| `pO` | `x0 := 42; halt [x0]` | `LO`: empty (not a certificate) | `πO`: onto 0 slots | output erasure is observed |
| `pKD` | `dbg x0; x0 := 5; halt [x0]` | `LKD`: path liveness | `πKD`: identity | kept-but-dead debug read |
| `pNK` | `nop; halt [x0, x1]` | `LNK`: both live at the halt | `πNK`: merge | write-free merge under `KeptRel` |
| `pF` | `x1 := x0; halt []` | `LF`: empty | `πF`: empty | faint operand (path-live, droppable) |
| `pI` | `if 0 goto 1 else 2; halt [x0]; halt []` | — | — | use behind a branch never taken |
| `pDisj` | `x1 := 5; dbg x1; x0 := 42; x1 := 99; halt [x0]` | `LDisj`: disjoint live ranges | `πDisj`: merge | disjoint ranges vs `NoAssignClobber` |

The core definitions above have positive and negative examples checked as anonymous `example`
declarations in `Examples.lean` (for instance `ReadsLive pA LA` and `¬ ReadsLive pR LR`;
`TransferClosed pB LB` and `¬ TransferClosed pT LT`; `NoAssignClobber pC LC πCm` and
`¬ NoAssignClobber pA LA πAm`; `PathLive pT 0 0` and `¬ PathLive pB 0 2`; `checkLive pB LB = true`;
`¬ LockstepBisim pO (compact pO LO πO) (CompactRel pO LO πO)`, an output-erasing compaction).

### Auxiliary declarations cited by name

Every package-local Lean declaration that this report mentions by name and that is not quoted under
**Definitions** or in a card is quoted here verbatim from the source (docstrings omitted; theorem
proofs elided as `:= …`), together with the package-local definitions that these quotes use. Every
theorem quoted here is listed in `results.json` (as a non-vacuity witness, as a tightness
counterexample, or, for lemmas cited in remarks and non-claims, under a card's `lean_names`), so its
statement hash and definition-closure hash are recorded under **Evidence**. Every definition quoted
here occurs in the statement of at least one of those theorems, directly or through another quoted
definition, so its body is covered by that theorem's closure hash.

**Concrete instances and auxiliary definitions** (programs, masks, maps, pre- and postconditions, and
the store operations used by counterexamples; the table above describes the programs informally).
`πS` and `πB` send a kept slot `x` to `x mod 2` (natural-number modulo); their masks `LS` and `LB`
keep exactly `x0` and `x1`, so both maps act as `x0 ↦ 0`, `x1 ↦ 1`, and `x2`, which is not kept, is
outside their domain:

```lean
-- lean/ToySlotCompact/Boundaries.lean:119-120
def pDisj : Prog 2 :=
  [.assign 1 (.const 5), .dbg (.slot 1), .assign 0 (.const 42), .assign 1 (.const 99), .halt [0]]

-- lean/ToySlotCompact/Boundaries.lean:122-123
def LDisj : Ann 2 := fun pc i =>
  if pc = 1 then decide (i = 1) else decide ((pc = 3 ∨ pc = 4) ∧ i = 0)

-- lean/ToySlotCompact/Boundaries.lean:125
def πDisj : Compaction pDisj LDisj 1 := fun _ => 0

-- lean/ToySlotCompact/Boundaries.lean:174
def preNe : Store 2 → Prop := fun σ => σ 0 ≠ σ 1
```

```lean
-- lean/ToySlotCompact/Counterexamples.lean:313
def ignorePutOps (N : Nat) : StoreOps (Fin N → Nat) N Nat := ⟨fun σ k => σ k, fun σ _ _ => σ⟩

-- lean/ToySlotCompact/Counterexamples.lean:315-316
def clobberOps (N : Nat) : StoreOps (Fin N → Nat) N Nat :=
  ⟨fun σ k => σ k, fun _ k v => fun j => if j = k then v else 0⟩
```

```lean
-- lean/ToySlotCompact/Instances.lean:28
def preTrue {N : Nat} : Store N → Prop := fun _ => True

-- lean/ToySlotCompact/Instances.lean:59
def preA : Store 2 → Prop := fun σ => σ 0 = 3

-- lean/ToySlotCompact/Instances.lean:199
def postR0 : State 2 → Prop := postAt 1 1 0
```

```lean
-- lean/ToySlotCompact/Instances2.lean:16
def pE : Prog 2 := [.halt [0, 1]]

-- lean/ToySlotCompact/Instances2.lean:18
def LE : Ann 2 := fun pc _ => decide (pc = 0)

-- lean/ToySlotCompact/Instances2.lean:20
def πEm : Compaction pE LE 1 := fun _ => 0

-- lean/ToySlotCompact/Instances2.lean:36
def postE : State 2 → Prop := fun s => s.st 0 = s.st 1

-- lean/ToySlotCompact/Instances2.lean:68
def pE3 : Prog 3 := [.halt [0, 1]]

-- lean/ToySlotCompact/Instances2.lean:70
def LE3 : Ann 3 := fun pc i => decide (pc = 0 ∧ i.val < 2)

-- lean/ToySlotCompact/Instances2.lean:72
def πE3 : Compaction pE3 LE3 1 := fun _ => 0

-- lean/ToySlotCompact/Instances2.lean:74
def postE3 : State 3 → Prop := fun s => s.st 0 ≠ s.st 1 ∧ s.st 2 = 0

-- lean/ToySlotCompact/Instances2.lean:109
def pV : Prog 2 := [.assign 1 (.const 5), .nop, .halt [0, 1]]

-- lean/ToySlotCompact/Instances2.lean:111-112
def LV : Ann 2 := fun pc i => if pc = 0 then false else if pc = 1 then decide (i = 1)
  else decide (pc = 2)

-- lean/ToySlotCompact/Instances2.lean:114
def πVm : Compaction pV LV 1 := fun _ => 0

-- lean/ToySlotCompact/Instances2.lean:130
def postV : State 2 → Prop := postAt 2 0 5

-- lean/ToySlotCompact/Instances2.lean:152
def pH : Prog 1 := [.halt []]

-- lean/ToySlotCompact/Instances2.lean:154
def LH : Ann 1 := fun _ _ => false

-- lean/ToySlotCompact/Instances2.lean:156
def πH : Compaction pH LH 1 := fun _ => 0

-- lean/ToySlotCompact/Instances2.lean:167
def preH : Store 1 → Prop := fun σ => σ 0 = 1

-- lean/ToySlotCompact/Instances2.lean:169
def postFalse {N : Nat} : State N → Prop := fun _ => False

-- lean/ToySlotCompact/Instances2.lean:171
def postTrue {N : Nat} : State N → Prop := fun _ => True

-- lean/ToySlotCompact/Instances2.lean:173
def postH : State 1 → Prop := fun s => s.st 0 = 0

-- lean/ToySlotCompact/Instances2.lean:231
def pU : Prog 1 := [.halt [0]]

-- lean/ToySlotCompact/Instances2.lean:233
def LU : Ann 1 := fun _ _ => false

-- lean/ToySlotCompact/Instances2.lean:248-250
def pS : Prog 3 :=
  [.assign 2 (.const 9), .storageLive 1, .assign 1 (.add (.slot 0) (.const 1)), .dbg (.slot 1),
    .storageDead 0, .halt [1]]

-- lean/ToySlotCompact/Instances2.lean:252
def LS : Ann 3 := fun pc i => if pc ≤ 2 then decide (i = 0) else decide (pc ≤ 5 ∧ i = 1)

-- lean/ToySlotCompact/Instances2.lean:254
def πS : Compaction pS LS 2 := fun x => ⟨x.1.val % 2, Nat.mod_lt _ (by decide)⟩

-- lean/ToySlotCompact/Instances2.lean:267-268
def pC : Prog 3 := [.assign 2 (.const 9), .assign 1 (.add (.slot 0) (.const 1)), .dbg (.slot 1),
  .halt [1]]

-- lean/ToySlotCompact/Instances2.lean:270
def LC : Ann 3 := fun pc i => if pc ≤ 1 then decide (i = 0) else decide (pc ≤ 3 ∧ i = 1)

-- lean/ToySlotCompact/Instances2.lean:272
def πCm : Compaction pC LC 1 := fun _ => 0

-- lean/ToySlotCompact/Instances2.lean:291-293
def pB : Prog 3 :=
  [.branch (.slot 0) 1 4, .assign 1 (.add (.slot 1) (.const 2)), .assign 0 (.const 0),
    .branch (.const 1) 0 0, .halt [1]]

-- lean/ToySlotCompact/Instances2.lean:295-296
def LB : Ann 3 := fun pc i =>
  if pc = 0 ∨ pc = 3 then decide (i.val < 2) else decide (pc ≤ 4 ∧ i = 1)

-- lean/ToySlotCompact/Instances2.lean:298
def πB : Compaction pB LB 2 := fun x => ⟨x.1.val % 2, Nat.mod_lt _ (by decide)⟩

-- lean/ToySlotCompact/Instances2.lean:312
def postB : State 3 → Prop := postAt 4 1 12

-- lean/ToySlotCompact/Instances2.lean:318
def postA5 : State 2 → Prop := postAt 1 0 5

-- lean/ToySlotCompact/Instances2.lean:338
def postM0 : State 2 → Prop := postAt 2 1 0

-- lean/ToySlotCompact/Instances2.lean:358
def postV3 : State 2 → Prop := postAt 2 0 3

-- lean/ToySlotCompact/Instances2.lean:378
def pX : Prog 2 := [.assign 1 (.const 5), .assign 1 (.slot 0), .halt [1]]

-- lean/ToySlotCompact/Instances2.lean:380
def LX : Ann 2 := fun pc i => if pc = 0 then decide (i = 0) else decide (pc = 2 ∧ i = 1)

-- lean/ToySlotCompact/Instances2.lean:382
def πXm : Compaction pX LX 1 := fun _ => 0

-- lean/ToySlotCompact/Instances2.lean:397
def postX : State 2 → Prop := postAt 2 1 3

-- lean/ToySlotCompact/Instances2.lean:417
def pK : Prog 1 := [.assign 0 (.const 1), .halt []]

-- lean/ToySlotCompact/Instances2.lean:419
def LK : Ann 1 := fun _ _ => false

-- lean/ToySlotCompact/Instances2.lean:421
def πK : Compaction pK LK 1 := fun _ => 0

-- lean/ToySlotCompact/Instances2.lean:423
def postK : State 1 → Prop := fun s => s.st 0 = 1

-- lean/ToySlotCompact/Instances2.lean:455
def pO : Prog 1 := [.assign 0 (.const 42), .halt [0]]

-- lean/ToySlotCompact/Instances2.lean:457
def LO : Ann 1 := fun _ _ => false

-- lean/ToySlotCompact/Instances2.lean:459
def πO : Compaction pO LO 0 := fun x => nomatch x.2

-- lean/ToySlotCompact/Instances2.lean:478
def pKD : Prog 1 := [.dbg (.slot 0), .assign 0 (.const 5), .halt [0]]

-- lean/ToySlotCompact/Instances2.lean:480
def LKD : Ann 1 := fun pc _ => decide (pc = 2)

-- lean/ToySlotCompact/Instances2.lean:482
def πKD : Compaction pKD LKD 1 := fun x => x.val

-- lean/ToySlotCompact/Instances2.lean:497
def pNK : Prog 2 := [.nop, .halt [0, 1]]

-- lean/ToySlotCompact/Instances2.lean:499
def LNK : Ann 2 := fun pc _ => decide (pc = 1)

-- lean/ToySlotCompact/Instances2.lean:501
def πNK : Compaction pNK LNK 1 := fun _ => 0

-- lean/ToySlotCompact/Instances2.lean:514
def pF : Prog 2 := [.assign 1 (.slot 0), .halt []]

-- lean/ToySlotCompact/Instances2.lean:516
def LF : Ann 2 := fun _ _ => false

-- lean/ToySlotCompact/Instances2.lean:518
def πF : Compaction pF LF 1 := fun _ => 0

-- lean/ToySlotCompact/Instances2.lean:531
def pI : Prog 1 := [.branch (.const 0) 1 2, .halt [0], .halt []]
```

```lean
-- lean/ToySlotCompact/NonVacuity.lean:72
def preS : Store 3 → Prop := fun σ => σ 0 = 0

-- lean/ToySlotCompact/NonVacuity.lean:74
def postS : State 3 → Prop := postAt 5 1 1

-- lean/ToySlotCompact/NonVacuity.lean:100
def preC : Store 3 → Prop := fun σ => σ 0 = 4

-- lean/ToySlotCompact/NonVacuity.lean:102
def postC : State 3 → Prop := postAt 3 1 5
```

**Non-vacuity witnesses and tightness counterexamples** (the card that uses each one is named in the
**Evidence** table):

```lean
-- lean/ToySlotCompact/Counterexamples.lean:75-77
theorem cex_keptBisim_readsKept :
    Function.Injective πR ∧ ¬ ReadsKept pR LR ∧ DbgReadsKept pR LR ∧
      ¬ LockstepBisim pR (compact pR LR πR) (KeptRel pR LR πR) := …

-- lean/ToySlotCompact/Counterexamples.lean:119-123
theorem cex_wp_postCorr :
    ReadsLive pH LH ∧ TransferClosed pH LH ∧ NoAssignClobber pH LH πH ∧
      NoMarkerClobber pH LH πH ∧ ¬ PostCorr pH LH πH postTrue postFalse ∧
      ¬ (∀ s s', CompactRel pH LH πH s s' →
        (wp pH postTrue s ↔ wp (compact pH LH πH) postFalse s')) := …

-- lean/ToySlotCompact/Counterexamples.lean:128-130
theorem cex_postClass_injAtHalts :
    ¬ (∀ pc, IsHalt pE3 pc → InjOnLiveAt pE3 LE3 πE3 pc) ∧
      ¬ ((∃ Q', PostCorr pE3 LE3 πE3 postE3 Q') ↔ DependsOnlyOnLive pE3 LE3 postE3) := …

-- lean/ToySlotCompact/Counterexamples.lean:138-140
theorem cex_pushStore_injOnLiveAt :
    ¬ InjOnLiveAt pE LE πEm 0 ∧
      ¬ CompactRel pE LE πEm ⟨0, fun i => i.val⟩ ⟨0, pushStore πEm 0 (fun i => i.val)⟩ := …

-- lean/ToySlotCompact/Counterexamples.lean:151-152
theorem cex_postCorr_pullPost_dependsOnlyOnLive :
    ¬ DependsOnlyOnLive pH LH postH ∧ ¬ PostCorr pH LH πH postH (pullPost πH postH) := …

-- lean/ToySlotCompact/Counterexamples.lean:164-171
theorem cex_vcFwd_readsLive :
    ¬ ReadsLive pX LX ∧
      TransferClosed pX LX ∧
      NoAssignClobber pX LX πXm ∧
      NoMarkerClobber pX LX πXm ∧
      DependsOnlyOnLive pX LX postX ∧
      ¬ ((∀ σ, preA σ → wp pX postX ⟨0, σ⟩) →
        (∀ σ', preA (pullStore πXm σ') → wp (compact pX LX πXm) (pullPost πXm postX) ⟨0, σ'⟩)) := …

-- lean/ToySlotCompact/Counterexamples.lean:174-181
theorem cex_vcFwd_transferClosed :
    ReadsLive pV LV ∧
      ¬ TransferClosed pV LV ∧
      NoAssignClobber pV LV πVm ∧
      NoMarkerClobber pV LV πVm ∧
      DependsOnlyOnLive pV LV postV3 ∧
      ¬ ((∀ σ, preA σ → wp pV postV3 ⟨0, σ⟩) →
        (∀ σ', preA (pullStore πVm σ') → wp (compact pV LV πVm) (pullPost πVm postV3) ⟨0, σ'⟩)) := …

-- lean/ToySlotCompact/Counterexamples.lean:184-191
theorem cex_vcFwd_noAssignClobber :
    ReadsLive pA LA ∧
      TransferClosed pA LA ∧
      ¬ NoAssignClobber pA LA πAm ∧
      NoMarkerClobber pA LA πAm ∧
      DependsOnlyOnLive pA LA postA ∧
      ¬ ((∀ σ, preA σ → wp pA postA ⟨0, σ⟩) →
        (∀ σ', preA (pullStore πAm σ') → wp (compact pA LA πAm) (pullPost πAm postA) ⟨0, σ'⟩)) := …

-- lean/ToySlotCompact/Counterexamples.lean:194-201
theorem cex_vcFwd_noMarkerClobber :
    ReadsLive pM LM ∧
      TransferClosed pM LM ∧
      NoAssignClobber pM LM πMm ∧
      ¬ NoMarkerClobber pM LM πMm ∧
      DependsOnlyOnLive pM LM postM ∧
      ¬ ((∀ σ, preA σ → wp pM postM ⟨0, σ⟩) →
        (∀ σ', preA (pullStore πMm σ') → wp (compact pM LM πMm) (pullPost πMm postM) ⟨0, σ'⟩)) := …

-- lean/ToySlotCompact/Counterexamples.lean:204-211
theorem cex_vcFwd_post :
    ReadsLive pK LK ∧
      TransferClosed pK LK ∧
      NoAssignClobber pK LK πK ∧
      NoMarkerClobber pK LK πK ∧
      ¬ DependsOnlyOnLive pK LK postK ∧
      ¬ ((∀ σ, preTrue σ → wp pK postK ⟨0, σ⟩) →
        (∀ σ', preTrue (pullStore πK σ') → wp (compact pK LK πK) (pullPost πK postK) ⟨0, σ'⟩)) := …

-- lean/ToySlotCompact/Counterexamples.lean:216-225
theorem cex_vcBwd_readsLive :
    ¬ ReadsLive pR LR ∧
      TransferClosed pR LR ∧
      NoAssignClobber pR LR πR ∧
      NoMarkerClobber pR LR πR ∧
      InjOnLiveAt pR LR πR 0 ∧
      DependsOnlyOnEntryLive pR LR preTrue ∧
      DependsOnlyOnLive pR LR postR0 ∧
      ¬ ((∀ σ', preTrue (pullStore πR σ') → wp (compact pR LR πR) (pullPost πR postR0) ⟨0, σ'⟩) →
        (∀ σ, preTrue σ → wp pR postR0 ⟨0, σ⟩)) := …

-- lean/ToySlotCompact/Counterexamples.lean:228-237
theorem cex_vcBwd_transferClosed :
    ReadsLive pV LV ∧
      ¬ TransferClosed pV LV ∧
      NoAssignClobber pV LV πVm ∧
      NoMarkerClobber pV LV πVm ∧
      InjOnLiveAt pV LV πVm 0 ∧
      DependsOnlyOnEntryLive pV LV preTrue ∧
      DependsOnlyOnLive pV LV postV ∧
      ¬ ((∀ σ', preTrue (pullStore πVm σ') → wp (compact pV LV πVm) (pullPost πVm postV) ⟨0, σ'⟩) →
        (∀ σ, preTrue σ → wp pV postV ⟨0, σ⟩)) := …

-- lean/ToySlotCompact/Counterexamples.lean:240-249
theorem cex_vcBwd_noAssignClobber :
    ReadsLive pA LA ∧
      TransferClosed pA LA ∧
      ¬ NoAssignClobber pA LA πAm ∧
      NoMarkerClobber pA LA πAm ∧
      InjOnLiveAt pA LA πAm 0 ∧
      DependsOnlyOnEntryLive pA LA preTrue ∧
      DependsOnlyOnLive pA LA postA5 ∧
      ¬ ((∀ σ', preTrue (pullStore πAm σ') → wp (compact pA LA πAm) (pullPost πAm postA5) ⟨0, σ'⟩) →
        (∀ σ, preTrue σ → wp pA postA5 ⟨0, σ⟩)) := …

-- lean/ToySlotCompact/Counterexamples.lean:252-261
theorem cex_vcBwd_noMarkerClobber :
    ReadsLive pM LM ∧
      TransferClosed pM LM ∧
      NoAssignClobber pM LM πMm ∧
      ¬ NoMarkerClobber pM LM πMm ∧
      InjOnLiveAt pM LM πMm 0 ∧
      DependsOnlyOnEntryLive pM LM preTrue ∧
      DependsOnlyOnLive pM LM postM0 ∧
      ¬ ((∀ σ', preTrue (pullStore πMm σ') → wp (compact pM LM πMm) (pullPost πMm postM0) ⟨0, σ'⟩) →
        (∀ σ, preTrue σ → wp pM postM0 ⟨0, σ⟩)) := …

-- lean/ToySlotCompact/Counterexamples.lean:264-273
theorem cex_vcBwd_injOnLiveAt :
    ReadsLive pE LE ∧
      TransferClosed pE LE ∧
      NoAssignClobber pE LE πEm ∧
      NoMarkerClobber pE LE πEm ∧
      ¬ InjOnLiveAt pE LE πEm 0 ∧
      DependsOnlyOnEntryLive pE LE preTrue ∧
      DependsOnlyOnLive pE LE postE ∧
      ¬ ((∀ σ', preTrue (pullStore πEm σ') → wp (compact pE LE πEm) (pullPost πEm postE) ⟨0, σ'⟩) →
        (∀ σ, preTrue σ → wp pE postE ⟨0, σ⟩)) := …

-- lean/ToySlotCompact/Counterexamples.lean:276-285
theorem cex_vcBwd_pre :
    ReadsLive pH LH ∧
      TransferClosed pH LH ∧
      NoAssignClobber pH LH πH ∧
      NoMarkerClobber pH LH πH ∧
      InjOnLiveAt pH LH πH 0 ∧
      ¬ DependsOnlyOnEntryLive pH LH preH ∧
      DependsOnlyOnLive pH LH postFalse ∧
      ¬ ((∀ σ', preH (pullStore πH σ') → wp (compact pH LH πH) (pullPost πH postFalse) ⟨0, σ'⟩) →
        (∀ σ, preH σ → wp pH postFalse ⟨0, σ⟩)) := …

-- lean/ToySlotCompact/Counterexamples.lean:288-297
theorem cex_vcBwd_post :
    ReadsLive pH LH ∧
      TransferClosed pH LH ∧
      NoAssignClobber pH LH πH ∧
      NoMarkerClobber pH LH πH ∧
      InjOnLiveAt pH LH πH 0 ∧
      DependsOnlyOnEntryLive pH LH preTrue ∧
      ¬ DependsOnlyOnLive pH LH postH ∧
      ¬ ((∀ σ', preTrue (pullStore πH σ') → wp (compact pH LH πH) (pullPost πH postH) ⟨0, σ'⟩) →
        (∀ σ, preTrue σ → wp pH postH ⟨0, σ⟩)) := …

-- lean/ToySlotCompact/Counterexamples.lean:302-303
theorem cex_cert_readsLive :
    ¬ ReadsLive pU LU ∧ TransferClosed pU LU ∧ PathLive pU 0 0 ∧ LU 0 0 = false := …

-- lean/ToySlotCompact/Counterexamples.lean:306-307
theorem cex_cert_transferClosed :
    ReadsLive pT LT ∧ ¬ TransferClosed pT LT ∧ PathLive pT 0 0 ∧ LT 0 0 = false := …

-- lean/ToySlotCompact/Counterexamples.lean:331-336
theorem cex_repInd_h1s :
    ¬ GetPutSame (ignorePutOps 1) ∧ GetPutOther (ignorePutOps 1) ∧ GetPutSame (funOps 1 Nat) ∧
      GetPutOther (funOps 1 Nat) ∧
      (∀ k, (ignorePutOps 1).get (fun _ => 0) k = (funOps 1 Nat).get (fun _ => 0) k) ∧
      runCheck (ignorePutOps 1) (fun _ => 0) [.incr 0 0 1, .check 0 1] ≠
        runCheck (funOps 1 Nat) (fun _ => 0) [.incr 0 0 1, .check 0 1] := …

-- lean/ToySlotCompact/Counterexamples.lean:340-345
theorem cex_repInd_h1o :
    GetPutSame (clobberOps 2) ∧ ¬ GetPutOther (clobberOps 2) ∧ GetPutSame (funOps 2 Nat) ∧
      GetPutOther (funOps 2 Nat) ∧
      (∀ k, (clobberOps 2).get (fun _ => 5) k = (funOps 2 Nat).get (fun _ => 5) k) ∧
      runCheck (clobberOps 2) (fun _ => 5) [.incr 0 0 1, .check 1 5] ≠
        runCheck (funOps 2 Nat) (fun _ => 5) [.incr 0 0 1, .check 1 5] := …

-- lean/ToySlotCompact/Counterexamples.lean:349-354
theorem cex_repInd_h2s :
    GetPutSame (funOps 1 Nat) ∧ GetPutOther (funOps 1 Nat) ∧ ¬ GetPutSame (ignorePutOps 1) ∧
      GetPutOther (ignorePutOps 1) ∧
      (∀ k, (funOps 1 Nat).get (fun _ => 0) k = (ignorePutOps 1).get (fun _ => 0) k) ∧
      runCheck (funOps 1 Nat) (fun _ => 0) [.incr 0 0 1, .check 0 1] ≠
        runCheck (ignorePutOps 1) (fun _ => 0) [.incr 0 0 1, .check 0 1] := …

-- lean/ToySlotCompact/Counterexamples.lean:358-363
theorem cex_repInd_h2o :
    GetPutSame (funOps 2 Nat) ∧ GetPutOther (funOps 2 Nat) ∧ GetPutSame (clobberOps 2) ∧
      ¬ GetPutOther (clobberOps 2) ∧
      (∀ k, (funOps 2 Nat).get (fun _ => 5) k = (clobberOps 2).get (fun _ => 5) k) ∧
      runCheck (funOps 2 Nat) (fun _ => 5) [.incr 0 0 1, .check 1 5] ≠
        runCheck (clobberOps 2) (fun _ => 5) [.incr 0 0 1, .check 1 5] := …

-- lean/ToySlotCompact/Counterexamples.lean:367-371
theorem cex_repInd_view :
    GetPutSame (funOps 1 Nat) ∧ GetPutOther (funOps 1 Nat) ∧
      ¬ (∀ k, (funOps 1 Nat).get (fun _ => 0) k = (funOps 1 Nat).get (fun _ => 1) k) ∧
      runCheck (funOps 1 Nat) (fun _ => 0) [.check 0 0] ≠
        runCheck (funOps 1 Nat) (fun _ => 1) [.check 0 0] := …

-- lean/ToySlotCompact/Counterexamples.lean:376-378
theorem cex_repInd_funOps_alistOps_view :
    alistGet 0 ([] : List (Fin 1 × Nat)) ≠ (fun _ => 1) ∧
      runCheck (funOps 1 Nat) (fun _ => 1) [.check 0 1] ≠ runCheck (alistOps 1 0) [] [.check 0 1] := …

-- lean/ToySlotCompact/Counterexamples.lean:383-386
theorem cex_alistCost_complete :
    ¬ Complete ([] : List (Fin 1 × Nat)) ∧
      ¬ runCost (alistOps 1 0) (alistCost 1 Nat) [] [.incr 0 0 0, .incr 0 0 0] ≤
        2 * [Cmd.incr (0 : Fin 1) 0 0, .incr 0 0 0].length * ([] : List (Fin 1 × Nat)).length := …
```

```lean
-- lean/ToySlotCompact/Instances.lean:275
theorem pT_pathLive : PathLive pT 0 0 := …
```

```lean
-- lean/ToySlotCompact/NonVacuity.lean:13-15
theorem nonvacuous_bisim_noClobber_sharing :
    ReadsLive pC LC ∧ TransferClosed pC LC ∧ DbgReadsLive pC LC ∧ NoAssignClobber pC LC πCm ∧
      NoMarkerClobber pC LC πCm ∧ ¬ Function.Injective πCm := …

-- lean/ToySlotCompact/NonVacuity.lean:19-21
theorem nonvacuous_bisim_noClobber_loop :
    ReadsLive pB LB ∧ TransferClosed pB LB ∧ DbgReadsLive pB LB ∧ NoAssignClobber pB LB πB ∧
      NoMarkerClobber pB LB πB := …

-- lean/ToySlotCompact/NonVacuity.lean:27-29
theorem nonvacuous_bisim_injective_straightLine :
    Function.Injective πS ∧ ReadsLive pS LS ∧ TransferClosed pS LS ∧ DbgReadsLive pS LS ∧
      Kept pS LS 2 = false := …

-- lean/ToySlotCompact/NonVacuity.lean:33-34
theorem nonvacuous_bisim_injective_loop :
    Function.Injective πB ∧ ReadsLive pB LB ∧ TransferClosed pB LB ∧ DbgReadsLive pB LB := …

-- lean/ToySlotCompact/NonVacuity.lean:38-39
theorem nonvacuous_keptBisim :
    Function.Injective πS ∧ ReadsKept pS LS ∧ DbgReadsKept pS LS := …

-- lean/ToySlotCompact/NonVacuity.lean:44
theorem nonvacuous_entry_iff : InjOnLiveAt pB LB πB 0 ∧ ¬ InjOnLiveAt pE LE πEm 0 := …

-- lean/ToySlotCompact/NonVacuity.lean:49-52
theorem nonvacuous_wp_transport :
    ReadsLive pB LB ∧ TransferClosed pB LB ∧ NoAssignClobber pB LB πB ∧
      NoMarkerClobber pB LB πB ∧ PostCorr pB LB πB postB (pullPost πB postB) ∧
      wp pB postB ⟨0, fun i => if i = 0 then 1 else if i = 1 then 10 else 0⟩ := …

-- lean/ToySlotCompact/NonVacuity.lean:61-63
theorem nonvacuous_wp_transport_rel :
    CompactRel pB LB πB ⟨0, fun i => if i = 0 then 1 else if i = 1 then 10 else 0⟩
      ⟨0, pushStore πB 0 (fun i => if i = 0 then 1 else if i = 1 then 10 else 0)⟩ := …

-- lean/ToySlotCompact/NonVacuity.lean:67-68
theorem nonvacuous_postClass :
    (∀ pc, IsHalt pB pc → InjOnLiveAt pB LB πB pc) ∧ DependsOnlyOnLive pB LB postB := …

-- lean/ToySlotCompact/NonVacuity.lean:81-85
theorem nonvacuous_vc :
    ReadsLive pS LS ∧ TransferClosed pS LS ∧ NoAssignClobber pS LS πS ∧
      NoMarkerClobber pS LS πS ∧ InjOnLiveAt pS LS πS 0 ∧ DependsOnlyOnEntryLive pS LS preS ∧
      DependsOnlyOnLive pS LS postS ∧ (∃ σ, preS σ) ∧ (∃ σ', preS (pullStore πS σ')) ∧
      (∀ σ, preS σ → wp pS postS ⟨0, σ⟩) := …

-- lean/ToySlotCompact/NonVacuity.lean:110-117
theorem nonvacuous_vc_bwd_sharing :
    ReadsLive pC LC ∧ TransferClosed pC LC ∧ NoAssignClobber pC LC πCm ∧
      NoMarkerClobber pC LC πCm ∧ InjOnLiveAt pC LC πCm 0 ∧
      DependsOnlyOnEntryLive pC LC preC ∧ DependsOnlyOnLive pC LC postC ∧
      ¬ Function.Injective πCm ∧
      (∃ σ', preC (pullStore πCm σ')) ∧
      (∀ σ', preC (pullStore πCm σ') →
        wp (compact pC LC πCm) (pullPost πCm postC) ⟨0, σ'⟩) := …

-- lean/ToySlotCompact/NonVacuity.lean:135
theorem nonvacuous_cert : ReadsLive pB LB ∧ TransferClosed pB LB ∧ PathLive pB 0 0 := …

-- lean/ToySlotCompact/NonVacuity.lean:140
theorem checkLive_rejects_underapprox : PathLive pR 0 0 ∧ LR 0 0 = false ∧ checkLive pR LR = false := …

-- lean/ToySlotCompact/NonVacuity.lean:163-164
theorem cex_cert_pathLive :
    ReadsLive pB LB ∧ TransferClosed pB LB ∧ ¬ PathLive pB 0 2 ∧ LB 0 2 = false := …

-- lean/ToySlotCompact/NonVacuity.lean:168
theorem nonvacuous_checkLive_sound : checkLive pB LB = true ∧ PathLive pB 0 0 ∧ LB 0 0 = true := …

-- lean/ToySlotCompact/NonVacuity.lean:172
theorem checkLive_both_verdicts : checkLive pB LB = true ∧ checkLive pR LR = false := …

-- lean/ToySlotCompact/NonVacuity.lean:176-177
theorem cex_checkLive_sound_accepted :
    checkLive pU LU = false ∧ PathLive pU 0 0 ∧ LU 0 0 = false := …

-- lean/ToySlotCompact/NonVacuity.lean:181-182
theorem cex_checkLive_sound_pathLive :
    checkLive pB LB = true ∧ ¬ PathLive pB 0 2 ∧ LB 0 2 = false := …

-- lean/ToySlotCompact/NonVacuity.lean:187-188
theorem cex_missing_requires_pathLive :
    ¬ PathLive pB 0 2 ∧ LB 0 2 = false ∧ checkLive pB LB = true := …

-- lean/ToySlotCompact/NonVacuity.lean:193-194
theorem cex_missing_requires_omission :
    PathLive pB 0 0 ∧ LB 0 0 = true ∧ checkLive pB LB = true := …

-- lean/ToySlotCompact/NonVacuity.lean:199-200
theorem nonvacuous_keptBisim_not_transferClosed :
    Function.Injective πT ∧ ReadsKept pT LT ∧ DbgReadsKept pT LT ∧ ¬ TransferClosed pT LT := …

-- lean/ToySlotCompact/NonVacuity.lean:205-206
theorem nonvacuous_keptBisim_kept_dead_dbg :
    Function.Injective πKD ∧ ReadsKept pKD LKD ∧ DbgReadsKept pKD LKD ∧ ¬ DbgReadsLive pKD LKD := …

-- lean/ToySlotCompact/NonVacuity.lean:211-214
theorem nonvacuous_repInd_funOps_alistOps :
    alistGet 0 [((0 : Fin 2), 4), (1, 7)] = (fun k : Fin 2 => if k = 0 then 4 else 7) ∧
      runCheck (funOps 2 Nat) (fun k : Fin 2 => if k = 0 then 4 else 7)
        [.incr 1 0 3, .check 1 7, .check 0 4] = true := …

-- lean/ToySlotCompact/NonVacuity.lean:222-227
theorem nonvacuous_repInd :
    GetPutSame (funOps 2 Nat) ∧ GetPutOther (funOps 2 Nat) ∧ GetPutSame (alistOps 2 0) ∧
      GetPutOther (alistOps 2 0) ∧
      (∀ k, (funOps 2 Nat).get (alistGet 0 [(0, 4), (1, 7)]) k =
        (alistOps 2 0).get [(0, 4), (1, 7)] k) ∧
      runCheck (alistOps 2 0) [(0, 4), (1, 7)] [.incr 1 0 3, .check 1 7, .check 0 4] = true := …

-- lean/ToySlotCompact/NonVacuity.lean:233
theorem famAlist_complete (L : Nat) : Complete (famAlist L) := …
```

**Further lemmas cited in remarks and non-claims** (listed under `lean_names` of the cards whose text
cites them):

```lean
-- lean/ToySlotCompact/Boundaries.lean:17-19
theorem bisim_observes_halt_outputs :
    ¬ ReadsLive pO LO ∧ compact pO LO πO = [.nop, .halt []] ∧
      ¬ LockstepBisim pO (compact pO LO πO) (CompactRel pO LO πO) := …

-- lean/ToySlotCompact/Boundaries.lean:27-32
theorem keptBisim_kept_dead_dbg :
    Kept pKD LKD 0 = true ∧ LKD 0 0 = false ∧
      ReadsLive pKD LKD ∧ TransferClosed pKD LKD ∧ ¬ DbgReadsLive pKD LKD ∧
      ReadsKept pKD LKD ∧ DbgReadsKept pKD LKD ∧ Function.Injective πKD ∧
      LockstepBisim pKD (compact pKD LKD πKD) (KeptRel pKD LKD πKD) ∧
      ¬ LockstepBisim pKD (compact pKD LKD πKD) (CompactRel pKD LKD πKD) := …

-- lean/ToySlotCompact/Boundaries.lean:45-47
theorem keptBisim_noninjective_writeFree :
    ¬ Function.Injective πNK ∧ ReadsKept pNK LNK ∧ DbgReadsKept pNK LNK ∧
      LockstepBisim pNK (compact pNK LNK πNK) (KeptRel pNK LNK πNK) := …

-- lean/ToySlotCompact/Boundaries.lean:67-70
theorem pathLive_faint_operand :
    PathLive pF 0 0 ∧ ¬ ReadsLive pF LF ∧ ¬ ReadsKept pF LF ∧
      LockstepBisim pF (compact pF LF πF) (CompactRel pF LF πF) ∧
      LockstepBisim pF (compact pF LF πF) (KeptRel pF LF πF) := …

-- lean/ToySlotCompact/Boundaries.lean:93-94
theorem pathLive_infeasible_branch :
    PathLive pI 0 0 ∧ ∀ σ : Store 1, step pI ⟨0, σ⟩ = .running ⟨2, σ⟩ none := …

-- lean/ToySlotCompact/Boundaries.lean:104-106
theorem checkLive_pathLiveMask_not_sufficient_with_dbg :
    checkLive pD LD = true ∧ (∀ pc i, LD pc i = pathLiveMask pD pc i) ∧
      Function.Injective πD ∧ ¬ LockstepBisim pD (compact pD LD πD) (CompactRel pD LD πD) := …

-- lean/ToySlotCompact/Boundaries.lean:130-134
theorem disjoint_live_ranges_not_noAssignClobber :
    ReadsLive pDisj LDisj ∧ TransferClosed pDisj LDisj ∧ DbgReadsLive pDisj LDisj ∧
      (∀ pc, InjOnLiveAt pDisj LDisj πDisj pc) ∧
      ¬ NoAssignClobber pDisj LDisj πDisj ∧
      ¬ LockstepBisim pDisj (compact pDisj LDisj πDisj) (CompactRel pDisj LDisj πDisj) := …

-- lean/ToySlotCompact/Boundaries.lean:163-167
theorem vc_forward_vacuous_dropped :
    ReadsLive pH LH ∧ TransferClosed pH LH ∧ NoAssignClobber pH LH πH ∧
      NoMarkerClobber pH LH πH ∧ DependsOnlyOnLive pH LH postTrue ∧
      (∃ σ, preH σ) ∧ (∀ σ, preH σ → wp pH postTrue ⟨0, σ⟩) ∧
      (∀ σ', ¬ preH (pullStore πH σ')) := …

-- lean/ToySlotCompact/Boundaries.lean:180-184
theorem vc_forward_vacuous_merged :
    ReadsLive pE LE ∧ TransferClosed pE LE ∧ NoAssignClobber pE LE πEm ∧
      NoMarkerClobber pE LE πEm ∧ DependsOnlyOnLive pE LE postTrue ∧
      (∃ σ, preNe σ) ∧ (∀ σ, preNe σ → wp pE postTrue ⟨0, σ⟩) ∧
      (∀ σ', ¬ preNe (pullStore πEm σ')) := …

-- lean/ToySlotCompact/Boundaries.lean:195-198
theorem vc_backward_without_inj0_postTrue :
    ¬ InjOnLiveAt pE LE πEm 0 ∧
      ((∀ σ', preTrue (pullStore πEm σ') → wp (compact pE LE πEm) (pullPost πEm postTrue) ⟨0, σ'⟩) →
        (∀ σ, preTrue σ → wp pE postTrue ⟨0, σ⟩)) := …

-- lean/ToySlotCompact/Boundaries.lean:204-206
theorem complete_with_repeated_keys :
    Complete (List.replicate 3 ((0 : Fin 1), (0 : Nat))) ∧
      (List.replicate 3 ((0 : Fin 1), (0 : Nat))).length = 3 := …

-- lean/ToySlotCompact/Boundaries.lean:213-215
theorem pD_silent_not_lockstep :
    SilentBisim pD (compact pD LD πD) (CompactRel pD LD πD) ∧
      ¬ LockstepBisim pD (compact pD LD πD) (CompactRel pD LD πD) := …
```

```lean
-- lean/ToySlotCompact/Liveness.lean:9
variable {N : Nat}

-- lean/ToySlotCompact/Liveness.lean:135-136
theorem pathLiveMask_cert (p : Prog N) :
    ReadsLive p (pathLiveMask p) ∧ TransferClosed p (pathLiveMask p) := …
```

```lean
-- lean/ToySlotCompact/NonVacuity.lean:154-155
theorem checkLive_accepts_overapprox :
    checkLive pB (fun _ _ => true) = true ∧ ∀ pc, ¬ PathLive pB pc 2 := …
```

```lean
-- lean/ToySlotCompact/Stores.lean:16
variable {S S₁ S₂ V : Type} {N : Nat}

-- lean/ToySlotCompact/Stores.lean:131
theorem consPutOps_getPutSame (N : Nat) : GetPutSame (consPutOps N) := …

-- lean/ToySlotCompact/Stores.lean:134
theorem consPutOps_getPutOther (N : Nat) : GetPutOther (consPutOps N) := …

-- lean/ToySlotCompact/Stores.lean:140
theorem consPutOps_not_putPut (N : Nat) : ¬ PutPut (consPutOps (N + 1)) := …
```

```lean
-- lean/ToySlotCompact/WP.lean:9
variable {N M : Nat}

-- lean/ToySlotCompact/WP.lean:212-217
theorem vc_transfer_of_noClobber (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hR : ReadsLive p L) (hT : TransferClosed p L) (hA : NoAssignClobber p L π)
    (hM : NoMarkerClobber p L π) (hinj0 : InjOnLiveAt p L π 0) (Pre : Store N → Prop)
    (Q : State N → Prop) (hPre : DependsOnlyOnEntryLive p L Pre) (hQ : DependsOnlyOnLive p L Q) :
    (∀ σ, Pre σ → wp p Q ⟨0, σ⟩) ↔
      (∀ σ', Pre (pullStore π σ') → wp (compact p L π) (pullPost π Q) ⟨0, σ'⟩) := …
```

### `compact-bisim-no-clobber` (theorem)

**Tier:** T0. Soundness of slot sharing under liveness-based interference conditions is mechanized in other formalisms: the HOL4 proof of register and stack-slot colouring in CakeML (colouring_ok, evaluate_apply_colour), for a structured language with computed liveness, and validated register allocation in CompCert (Rideau and Leroy 2010). Restated here for a control-flow graph with a claimed mask that is checked rather than computed, resetting storage markers, and debug observations.

**Plain claim:** Let p be a program over N slots, L a liveness mask and π a map from the kept slots (those L declares live somewhere) into M slots, not necessarily injective. If L is a liveness certificate for p (every use at a point, i.e. every semantic read and every halt output, is of a slot L declares live there, and L is closed under the backward transfer), every debug read is of a slot L declares live there, for every assignment to a kept slot d no different kept slot declared live just after it has the same target as d under π, and likewise for every storage marker of a kept slot, then CompactRel (same program counter, and σ'(π i) = σ i for every kept slot i declared live at the current point) is a lockstep bisimulation between p and compact p L π for the small-step function step: from related states both programs step to related states with equal debug events, or both halt in related states emitting equal output values, or both are stuck. Control flow is arbitrary, including loops.

**Lean statement** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/Bisim.lean:9
variable {N M : Nat}

-- lean/ToySlotCompact/Bisim.lean:209-212
theorem compact_lockstepBisim_of_noClobber (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hR : ReadsLive p L) (hT : TransferClosed p L) (hD : DbgReadsLive p L)
    (hA : NoAssignClobber p L π) (hM : NoMarkerClobber p L π) :
    LockstepBisim p (compact p L π) (CompactRel p L π) := …
```

Unfolded conclusion (`LockstepBisim` and the hypothesis `CompactRel p L π s s'` unfolded; checked to be definitionally equal to the conclusion):

```lean
∀ (s : State N) (s' : State M),
  (s'.pc = s.pc ∧ ∀ (i : Fin N) (h : Kept p L i = true), L s.pc i = true → s'.st (π ⟨i, h⟩) = s.st i) →
    ResRel (CompactRel p L π) (step p s) (step (compact p L π) s')
```

**Hypothesis ledger.** `tight`: the counterexample satisfies all other hypotheses of the named theorem and the conclusion fails, in the stated witness class; not a claim of necessity in general.

| hypothesis | purpose | tightness | counterexample | witness class |
| --- | --- | --- | --- | --- |
| `hR : ReadsLive p L` | every use at a point (semantic read or halt output) is of a slot the mask declares live there (gen half of the certificate) | tight | `cex_bisim_noClobber_readsLive` | two instructions over 2 slots, M = 1 |
| `hT : TransferClosed p L` | a slot declared live at a successor and not overwritten by the instruction is declared live before it (transfer half of the certificate) | tight | `cex_bisim_noClobber_transferClosed` | two instructions over 1 slot, identity map |
| `hD : DbgReadsLive p L` | debug observations read only slots declared live; liveness itself ignores debug reads | tight | `cex_bisim_noClobber_dbgReadsLive` | two instructions over 1 slot, nothing kept |
| `hA : NoAssignClobber p L π` | an assignment never writes the shared target of a different kept slot that is declared live after it | tight | `cex_bisim_noClobber_noAssignClobber` | two instructions over 2 slots merged into 1 |
| `hM : NoMarkerClobber p L π` | a storage marker (which resets its slot) never resets the shared target of a different kept slot that is declared live after it | tight | `cex_bisim_noClobber_noMarkerClobber` | three instructions over 2 slots merged into 1 |

**Depth:** shallow.

**Non-vacuity witness:** pC (a non-injective sharing of two slots with disjoint live ranges onto one slot) and pB (a loop with an injective map) satisfy all hypotheses. Lean: `nonvacuous_bisim_noClobber_sharing`, `nonvacuous_bisim_noClobber_loop`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* CakeML/cakeml at commit 2874b664e10939a3ee462215b2e068c89c1f70eb, file compiler/backend/proofs/word_allocProofScript.sml (read at that commit), the HOL4 correctness proof of register and stack-slot colouring in the CakeML compiler backend (described in Tan et al., 'The verified CakeML compiler backend', Journal of Functional Programming 29, e2, 2019, DOI 10.1017/S0956796818000229; bibliographic data from search results, paper not read here). colouring_ok (lines 99-141) requires the colouring f to be injective on each live set and on the union of an instruction's writes with the set live after it; strong_locals_rel (lines 178-183) relates source and target locals on a live set through f; Theorem evaluate_apply_colour (from line 1107) shows that, unless the source evaluation fails, evaluating apply_colour f prog from strong_locals_rel-related states gives the same result, for a structured language with sequencing, conditionals, loops and calls. Modeling bridge (derived, not kernel-checked): the same shape as InjOnLiveAt, NoAssignClobber and CompactRel, mechanized for computed liveness in a structured language rather than for a checked mask over a control-flow graph; storage markers and debug events have no counterpart there.
* Silvain Rideau and Xavier Leroy, 'Validating Register Allocation and Spilling', Compiler Construction (CC 2010), LNCS 6011, Springer, 2010, pp. 224-243, DOI 10.1007/978-3-642-11970-5_13 (bibliographic data from search results; paper text not read here). The corresponding Coq development is AbsInt/CompCert backend/Allocation.v, whose header reads 'Register allocation by external oracle and a posteriori validation' (read at commit 2685140bf72c959446981fb99b5e44a8975021bc), with its proof in backend/Allocproof.v. Modeling bridge (derived, not kernel-checked): a mechanized validator for a proposed, generally non-injective, assignment of variables to locations, the analogue of checking a claimed mask and interference conditions instead of recomputing them.
* llvm/llvm-project at commit 25b1c803e1e1504f6dc11f7afd68e65ad3ee5964, file llvm/lib/CodeGen/StackSlotColoring.cpp (read at that commit). Spill slots are colored so that a color is reused only when the slot's live interval does not overlap the intervals already given that color (ColorAssignmentInfo::overlaps, lines 109-115; StackSlotColoring::ColorSlot from line 303). Modeling bridge (derived, not kernel-checked): a non-injective compaction under an interference condition on live intervals; the package's NoAssignClobber/NoMarkerClobber (write versus live-after) conditions are a different formulation and no equivalence is claimed.
* llvm/llvm-project at commit 25b1c803e1e1504f6dc11f7afd68e65ad3ee5964, file llvm/lib/CodeGen/StackColoring.cpp (read at that commit), implementation notes lines 135-160: rules L1-L7 (lines 138-152) say that on a lifetime.start a stack slot is marked in-scope 'and the stack slot is overwritten with undef' (L2, lines 141-142), that lifetime.end marks it out-of-scope (L3) and that memory accesses to out-of-scope slots are UB (L6, line 147); lines 154-160 define a slot as in-use at a point 'if it either can be written to at that point, or if it has a live and non-undef content at that point' and state that slots never in-use together can be merged. Modeling bridge (derived, not kernel-checked): a lifetime start behaves as a write, the analogue of counting storage markers as writes in NoMarkerClobber; unlike LLVM, the toy resets slots to 0 at both markers instead of making later access undefined.
* AbsInt/CompCert at commit 2685140bf72c959446981fb99b5e44a8975021bc (read at that commit). backend/Stacking.v lays out activation records and maps local stack slot x to byte offset fe_ofs_local + 4 * x (offset_local, line 27), an injective slot renumbering; backend/Stackingproof.v proves transf_program_correct : forward_simulation (Linear.semantics prog) (Mach.semantics return_address_offset tprog) (lines 2201-2202) using forward_simulation_plus; backend/Linearizeproof.v proves a forward simulation from LTL to Linear for code linearization (lines 728-729), which concerns control-flow layout rather than slot assignment; backend/Allocproof.v proves a forward simulation for register allocation by validated translation from RTL to LTL (header lines 13-14, theorem lines 2528-2529). Modeling bridge (derived, not kernel-checked): realistic forward simulations, not lockstep bisimulations of this toy.
* Andrew W. Appel, Modern Compiler Implementation in ML (also in Java and in C), Cambridge University Press, 1998: chapter 10 'Liveness analysis' with sections 'Solution of dataflow equations', 'Liveness in the Tiger compiler' and 'Interference graph construction', and chapter 11 'Register allocation' (chapter and section titles verified on the author's table-of-contents page; chapter text not read here).

**Design question:** When is renumbering a function's slots through a map from the live slots into a smaller index set a sound transformation for executions, and which conditions make it fail?

**Non-claims:** listed under **Boundaries**, `compact-bisim-no-clobber`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. Reading `π` as a stack-slot colouring and `NoAssignClobber`/`NoMarkerClobber` as its interference condition, the theorem has the shape of the soundness argument behind slot sharing in LLVM's `StackColoring`/`StackSlotColoring` and behind CakeML's verified register and stack-slot colouring (prior art above). The inference is by correspondence of definitions: the toy has no memory, `lifetime` markers are modeled as resets to `0` rather than as undefined behaviour, the mask is checked rather than computed, and LLVM's interference test is an overlap test on live intervals, a different formulation. This card neither establishes nor refutes the corresponding property of any real compiler pass or verifier (model–system relation: none proved).

### `compact-bisim-injective` (theorem)

**Tier:** T0. Injective renaming of live slots is the injective special case of verified colouring (CakeML word_alloc) and the shape of CompCert's injective stack-slot layout (Stacking.v); here a corollary of compact-bisim-no-clobber.

**Plain claim:** If π is injective, the mask L is a liveness certificate for p (every semantic read and halt output at a point is of a slot L declares live there, and L is closed under the backward transfer), and every debug read is of a slot L declares live there, then CompactRel is a lockstep bisimulation between p and compact p L π for step (equal debug events, equal halt outputs, related successor states), for arbitrary control flow; storage markers that reset slots are allowed.

**Lean statement** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/Bisim.lean:9
variable {N M : Nat}

-- lean/ToySlotCompact/Bisim.lean:218-221
theorem compact_lockstepBisim_of_injective (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hInj : Function.Injective π) (hR : ReadsLive p L) (hT : TransferClosed p L)
    (hD : DbgReadsLive p L) :
    LockstepBisim p (compact p L π) (CompactRel p L π) := …
```

Unfolded conclusion (`LockstepBisim` and the hypothesis `CompactRel p L π s s'` unfolded; checked to be definitionally equal to the conclusion):

```lean
∀ (s : State N) (s' : State M),
  (s'.pc = s.pc ∧ ∀ (i : Fin N) (h : Kept p L i = true), L s.pc i = true → s'.st (π ⟨i, h⟩) = s.st i) →
    ResRel (CompactRel p L π) (step p s) (step (compact p L π) s')
```

**Hypothesis ledger.** `tight`: the counterexample satisfies all other hypotheses of the named theorem and the conclusion fails, in the stated witness class; not a claim of necessity in general.

| hypothesis | purpose | tightness | counterexample | witness class |
| --- | --- | --- | --- | --- |
| `hInj : Function.Injective π` | distinct kept slots get distinct targets | tight | `cex_bisim_injective_injective` | two instructions over 2 slots merged into 1, both live after the write |
| `hR : ReadsLive p L` | every use at a point (semantic read or halt output) is of a slot the mask declares live there (gen half of the certificate) | tight | `cex_bisim_injective_readsLive` | two instructions over 2 slots, M = 1 |
| `hT : TransferClosed p L` | a slot declared live at a successor and not overwritten by the instruction is declared live before it (transfer half of the certificate) | tight | `cex_bisim_injective_transferClosed` | two instructions over 1 slot, identity map |
| `hD : DbgReadsLive p L` | debug observations read only slots declared live; liveness itself ignores debug reads | tight | `cex_bisim_injective_dbgReadsLive` | two instructions over 1 slot, nothing kept |

**Depth:** shallow.

**Non-vacuity witness:** pS (straight-line code with StorageLive/StorageDead resets, a debug read of a live slot, and a write to a dropped slot) and pB (a loop) satisfy all hypotheses. Lean: `nonvacuous_bisim_injective_straightLine`, `nonvacuous_bisim_injective_loop`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* CakeML/cakeml at commit 2874b664e10939a3ee462215b2e068c89c1f70eb, file compiler/backend/proofs/word_allocProofScript.sml (read at that commit), the HOL4 correctness proof of register and stack-slot colouring in the CakeML compiler backend (described in Tan et al., 'The verified CakeML compiler backend', Journal of Functional Programming 29, e2, 2019, DOI 10.1017/S0956796818000229; bibliographic data from search results, paper not read here). colouring_ok (lines 99-141) requires the colouring f to be injective on each live set and on the union of an instruction's writes with the set live after it; strong_locals_rel (lines 178-183) relates source and target locals on a live set through f; Theorem evaluate_apply_colour (from line 1107) shows that, unless the source evaluation fails, evaluating apply_colour f prog from strong_locals_rel-related states gives the same result, for a structured language with sequencing, conditionals, loops and calls. Modeling bridge (derived, not kernel-checked): the same shape as InjOnLiveAt, NoAssignClobber and CompactRel, mechanized for computed liveness in a structured language rather than for a checked mask over a control-flow graph; storage markers and debug events have no counterpart there.
* rust-lang/rust at commit c7d5ba59d8e11ee2e2204b173458eec4cb41c973, file compiler/rustc_mir_transform/src/simplify.rs (read at that commit). The SimplifyLocals pass (enum at line 436, run_pass from line 455) counts actual uses of each local (UsedLocals), treats the return place, the arguments and locals referenced by debug info as always used (line 529: always_used = debuginfo_locals(body)), turns assignments and StorageLive/StorageDead statements of unused locals into nops (remove_unused_definitions_helper from line 629; make_nop at line 659), and renumbers the remaining locals in order (make_local_map from line 496). Removal is iterated to a fixed point (comment at lines 461-466; loop 'while modified' at line 636): removing a statement decrements the use counts of the locals it read (statement_removed, line 658), so chains of dead assignments disappear; uses through indirect places (line 568) and right-hand sides that are not safe to remove (line 600) are kept. Modeling bridge (derived, not kernel-checked): an injective, order-preserving compaction keyed on use counts rather than per-point liveness, which is the shape of compact_keptRel_lockstepBisim_of_injective; the toy's single-pass ReadsKept does not model the fixed-point cascade, and the toy keeps nops in place whereas rustc strips them (line 661).
* AbsInt/CompCert at commit 2685140bf72c959446981fb99b5e44a8975021bc (read at that commit). backend/Stacking.v lays out activation records and maps local stack slot x to byte offset fe_ofs_local + 4 * x (offset_local, line 27), an injective slot renumbering; backend/Stackingproof.v proves transf_program_correct : forward_simulation (Linear.semantics prog) (Mach.semantics return_address_offset tprog) (lines 2201-2202) using forward_simulation_plus; backend/Linearizeproof.v proves a forward simulation from LTL to Linear for code linearization (lines 728-729), which concerns control-flow layout rather than slot assignment; backend/Allocproof.v proves a forward simulation for register allocation by validated translation from RTL to LTL (header lines 13-14, theorem lines 2528-2529). Modeling bridge (derived, not kernel-checked): realistic forward simulations, not lockstep bisimulations of this toy.
* Andrew W. Appel, Modern Compiler Implementation in ML (also in Java and in C), Cambridge University Press, 1998: chapter 10 'Liveness analysis' with sections 'Solution of dataflow equations', 'Liveness in the Tiger compiler' and 'Interference graph construction', and chapter 11 'Register allocation' (chapter and section titles verified on the author's table-of-contents page; chapter text not read here).

**Design question:** When is renumbering a function's slots through a map from the live slots into a smaller index set a sound transformation for executions, and which conditions make it fail?

**Non-claims:** listed under **Boundaries**, `compact-bisim-injective`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. An injective `π` corresponds to a renumbering of the kept locals such as the one rustc's `SimplifyLocals` applies after removing unused locals, and to the injective slot layout of CompCert's `Stacking` (prior art above). rustc keys removal on use counts rather than on per-point liveness, treats debug-info locals as always used, and strips nops; those differences are not modeled. This card neither establishes nor refutes the corresponding property of any real compiler pass or verifier (model–system relation: none proved).

### `compact-kept-bisim-injective` (theorem)

**Tier:** T0. Combines injective renaming (the injective special case of verified colouring, CakeML word_alloc) with erasure of writes to slots that are never read, a degenerate case of the mechanized dead-computation elimination in CompCert (Deadcodeproof.v); restated here with the relation on all kept slots.

**Plain claim:** If π is injective and every semantic read, every halt output and every debug read of p is of a kept slot (a slot the mask L declares live at some point of p), then KeptRel (same program counter, and σ'(π i) = σ i for every kept slot i, live or not) is a lockstep bisimulation between p and compact p L π for step; no per-point condition on L (in particular no transfer closure) is assumed.

**Lean statement** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/Bisim.lean:9
variable {N M : Nat}

-- lean/ToySlotCompact/Bisim.lean:228-231
theorem compact_keptRel_lockstepBisim_of_injective (p : Prog N) (L : Ann N)
    (π : Compaction p L M) (hInj : Function.Injective π) (hRK : ReadsKept p L)
    (hDK : DbgReadsKept p L) :
    LockstepBisim p (compact p L π) (KeptRel p L π) := …
```

Unfolded conclusion (`LockstepBisim` and the hypothesis `KeptRel p L π s s'` unfolded; checked to be definitionally equal to the conclusion):

```lean
∀ (s : State N) (s' : State M),
  (s'.pc = s.pc ∧ ∀ (i : Fin N) (h : Kept p L i = true), s'.st (π ⟨i, h⟩) = s.st i) →
    ResRel (KeptRel p L π) (step p s) (step (compact p L π) s')
```

**Hypothesis ledger.** `tight`: the counterexample satisfies all other hypotheses of the named theorem and the conclusion fails, in the stated witness class; not a claim of necessity in general.

| hypothesis | purpose | tightness | counterexample | witness class |
| --- | --- | --- | --- | --- |
| `hInj : Function.Injective π` | distinct kept slots get distinct targets | tight | `cex_keptBisim_injective` | two instructions over 2 slots merged into 1, with a write to one merged slot |
| `hRK : ReadsKept p L` | every semantic read and halt output is of a kept slot, so renamed reads never see the constant 0 used for dropped slots | tight | `cex_keptBisim_readsKept` | two instructions over 2 slots, one kept |
| `hDK : DbgReadsKept p L` | every debug read is of a kept slot | tight | `cex_keptBisim_dbgReadsKept` | two instructions over 1 slot, nothing kept |

**Depth:** shallow.

**Non-vacuity witness:** pS with the injective πS; pT, whose mask is not transfer closed; and pKD, which has a debug read of a kept slot at a point where it is dead: all satisfy every hypothesis. Lean: `nonvacuous_keptBisim`, `nonvacuous_keptBisim_not_transferClosed`, `nonvacuous_keptBisim_kept_dead_dbg`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* rust-lang/rust at commit c7d5ba59d8e11ee2e2204b173458eec4cb41c973, file compiler/rustc_mir_transform/src/simplify.rs (read at that commit). The SimplifyLocals pass (enum at line 436, run_pass from line 455) counts actual uses of each local (UsedLocals), treats the return place, the arguments and locals referenced by debug info as always used (line 529: always_used = debuginfo_locals(body)), turns assignments and StorageLive/StorageDead statements of unused locals into nops (remove_unused_definitions_helper from line 629; make_nop at line 659), and renumbers the remaining locals in order (make_local_map from line 496). Removal is iterated to a fixed point (comment at lines 461-466; loop 'while modified' at line 636): removing a statement decrements the use counts of the locals it read (statement_removed, line 658), so chains of dead assignments disappear; uses through indirect places (line 568) and right-hand sides that are not safe to remove (line 600) are kept. Modeling bridge (derived, not kernel-checked): an injective, order-preserving compaction keyed on use counts rather than per-point liveness, which is the shape of compact_keptRel_lockstepBisim_of_injective; the toy's single-pass ReadsKept does not model the fixed-point cascade, and the toy keeps nops in place whereas rustc strips them (line 661).
* CakeML/cakeml at commit 2874b664e10939a3ee462215b2e068c89c1f70eb, file compiler/backend/proofs/word_allocProofScript.sml (read at that commit), the HOL4 correctness proof of register and stack-slot colouring in the CakeML compiler backend (described in Tan et al., 'The verified CakeML compiler backend', Journal of Functional Programming 29, e2, 2019, DOI 10.1017/S0956796818000229; bibliographic data from search results, paper not read here). colouring_ok (lines 99-141) requires the colouring f to be injective on each live set and on the union of an instruction's writes with the set live after it; strong_locals_rel (lines 178-183) relates source and target locals on a live set through f; Theorem evaluate_apply_colour (from line 1107) shows that, unless the source evaluation fails, evaluating apply_colour f prog from strong_locals_rel-related states gives the same result, for a structured language with sequencing, conditionals, loops and calls. Modeling bridge (derived, not kernel-checked): the same shape as InjOnLiveAt, NoAssignClobber and CompactRel, mechanized for computed liveness in a structured language rather than for a checked mask over a control-flow graph; storage markers and debug events have no counterpart there.
* AbsInt/CompCert at commit 2685140bf72c959446981fb99b5e44a8975021bc (read at that commit). backend/Liveness.v ('Liveness analysis over RTL') computes liveness with Backward_Dataflow_Solver (line 111); its transfer function (lines 68-91) makes the arguments of an operation live only if the result register is live after it (lines 78-79), i.e. strong liveness, unlike PathLive here. backend/Deadcodeproof.v ('Elimination of unneeded computations over RTL: correctness proof') proves transf_program_correct : forward_simulation (RTL.semantics prog) (RTL.semantics tprog) (lines 1263-1264). Modeling bridge (derived, not kernel-checked): mechanized backward liveness and dead-computation elimination in a realistic compiler.

**Design question:** When is renumbering a function's slots through a map from the live slots into a smaller index set a sound transformation for executions, and which conditions make it fail?

**Non-claims:** listed under **Boundaries**, `compact-kept-bisim-injective`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. `KeptRel` with an injective `π` and `ReadsKept` is the shape of rustc's `SimplifyLocals`: used locals are renumbered injectively and in order, and assignments to and storage markers of unused locals become nops. rustc iterates the removal to a fixed point (the toy's single-pass `ReadsKept` does not model that cascade) and strips the nops (the toy keeps them, so program points coincide). This card neither establishes nor refutes the corresponding property of any real compiler pass or verifier (model–system relation: none proved).

### `entry-adequacy-iff-injective-on-live` (characterization)

**Tier:** T1. That simultaneously live values cannot share a location is folklore. Mechanized colouring proofs assume injectivity on live sets as a hypothesis (CakeML colouring_ok), which is the sufficiency direction; the converse, that injectivity on the live slots is needed for every original store to have a related compacted store, was not found mechanized. Made precise here as an exact condition with exposed witnesses.

**Plain claim:** For any slot map π and any program point pc (the intended use is the entry point pc = 0): every original store σ has some compacted store σ' that is CompactRel-related to it at pc if and only if π is injective on the kept slots declared live at pc; when π is injective there, the push-forward pushStore π pc σ is such a σ'. Independently of injectivity, every compacted store σ' is CompactRel-related at pc to its pull-back pullStore π σ' (which reads dropped slots as 0).

**Lean statements** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/Bisim.lean:9
variable {N M : Nat}

-- lean/ToySlotCompact/Bisim.lean:319-321
theorem forall_exists_compactRel_iff_injOnLiveAt {p : Prog N} {L : Ann N}
    (π : Compaction p L M) (pc : Nat) :
    (∀ σ : Store N, ∃ σ' : Store M, CompactRel p L π ⟨pc, σ⟩ ⟨pc, σ'⟩) ↔ InjOnLiveAt p L π pc := …

-- lean/ToySlotCompact/Bisim.lean:312-314
theorem compactRel_pushStore {p : Prog N} {L : Ann N} {π : Compaction p L M} {pc : Nat}
    (hinj : InjOnLiveAt p L π pc) (σ : Store N) :
    CompactRel p L π ⟨pc, σ⟩ ⟨pc, pushStore π pc σ⟩ := …

-- lean/ToySlotCompact/Bisim.lean:306-307
theorem compactRel_pullStore {p : Prog N} {L : Ann N} (π : Compaction p L M) (σ' : Store M)
    (pc : Nat) : CompactRel p L π ⟨pc, pullStore π σ'⟩ ⟨pc, σ'⟩ := …
```

Unfolded `forall_exists_compactRel_iff_injOnLiveAt` (right-hand side `InjOnLiveAt p L π pc` unfolded; checked to be definitionally equal to the statement):

```lean
(∀ σ : Store N, ∃ σ' : Store M, CompactRel p L π ⟨pc, σ⟩ ⟨pc, σ'⟩) ↔
  ∀ (i j : Fin N) (hi : Kept p L i = true) (hj : Kept p L j = true),
    L pc i = true → L pc j = true → π ⟨i, hi⟩ = π ⟨j, hj⟩ → i = j
```

**Hypothesis ledger.** `tight`: the counterexample satisfies all other hypotheses of the named theorem and the conclusion fails, in the stated witness class; not a claim of necessity in general.

| hypothesis | purpose | tightness | counterexample | witness class |
| --- | --- | --- | --- | --- |
| `hinj : InjOnLiveAt p L π pc (hypothesis of compactRel_pushStore)` | pushStore stores one value per target slot, so two live slots sharing a target cannot both be represented (cex_pushStore_injOnLiveAt; the general statement is forall_exists_compactRel_iff_injOnLiveAt) | tight | `cex_pushStore_injOnLiveAt` | a one-instruction program over 2 slots, both live at entry, merged into 1 |

**Depth:** shallow.

**Non-vacuity witness:** Both sides of the equivalence hold for pB at entry and both fail for pE (two entry-live slots merged); pB at entry satisfies the hypothesis of compactRel_pushStore. compactRel_pullStore has no hypotheses. Lean: `nonvacuous_entry_iff`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* CakeML/cakeml at commit 2874b664e10939a3ee462215b2e068c89c1f70eb, file compiler/backend/proofs/word_allocProofScript.sml (read at that commit), the HOL4 correctness proof of register and stack-slot colouring in the CakeML compiler backend (described in Tan et al., 'The verified CakeML compiler backend', Journal of Functional Programming 29, e2, 2019, DOI 10.1017/S0956796818000229; bibliographic data from search results, paper not read here). colouring_ok (lines 99-141) requires the colouring f to be injective on each live set and on the union of an instruction's writes with the set live after it; strong_locals_rel (lines 178-183) relates source and target locals on a live set through f; Theorem evaluate_apply_colour (from line 1107) shows that, unless the source evaluation fails, evaluating apply_colour f prog from strong_locals_rel-related states gives the same result, for a structured language with sequencing, conditionals, loops and calls. Modeling bridge (derived, not kernel-checked): the same shape as InjOnLiveAt, NoAssignClobber and CompactRel, mechanized for computed liveness in a structured language rather than for a checked mask over a control-flow graph; storage markers and debug events have no counterpart there.
* Andrew W. Appel, Modern Compiler Implementation in ML (also in Java and in C), Cambridge University Press, 1998: chapter 10 'Liveness analysis' with sections 'Solution of dataflow equations', 'Liveness in the Tiger compiler' and 'Interference graph construction', and chapter 11 'Register allocation' (chapter and section titles verified on the author's table-of-contents page; chapter text not read here).

**Design question:** When is renumbering a function's slots through a map from the live slots into a smaller index set a sound transformation for executions, and which conditions make it fail?

**Non-claims:** listed under **Boundaries**, `entry-adequacy-iff-injective-on-live`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. A verifier that must relate every original entry store to some compacted one (for example to transport a precondition quantified over all inputs) needs, in the toy, injectivity of `π` on the slots live at entry; real calling conventions keep simultaneously live arguments in distinct slots, which is consistent with this theorem but not derived from it. This card neither establishes nor refutes the corresponding property of any real compiler pass or verifier (model–system relation: none proved).

### `wp-transport-no-clobber` (theorem)

**Tier:** T1. Weakest preconditions are preserved along a bisimulation: folklore made precise for this toy.

**Plain claim:** If the mask L is a liveness certificate for p (reads and halt outputs live, closed under the backward transfer), π satisfies NoAssignClobber and NoMarkerClobber (in particular if π is injective), and the postconditions Q (original) and Q' (compacted) agree on every pair of CompactRel-related halting states of p, then for every CompactRel-related pair of states the total-correctness weakest precondition wp, defined from the fuel-bounded execution exec, of p for Q holds if and only if that of compact p L π for Q' holds; debug reads play no role.

**Lean statement** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/WP.lean:9
variable {N M : Nat}

-- lean/ToySlotCompact/WP.lean:119-123
theorem wp_transport_of_noClobber (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hR : ReadsLive p L) (hT : TransferClosed p L) (hA : NoAssignClobber p L π)
    (hM : NoMarkerClobber p L π) {Q : State N → Prop} {Q' : State M → Prop}
    (hQ : PostCorr p L π Q Q') :
    ∀ s s', CompactRel p L π s s' → (wp p Q s ↔ wp (compact p L π) Q' s') := …
```

Unfolded conclusion (`wp` unfolded; checked to be definitionally equal to the conclusion):

```lean
∀ (s : State N) (s' : State M), CompactRel p L π s s' →
  ((∃ n sf, exec p n s = some sf ∧ Q sf) ↔ (∃ n sf, exec (compact p L π) n s' = some sf ∧ Q' sf))
```

**Hypothesis ledger.** `tight`: the counterexample satisfies all other hypotheses of the named theorem and the conclusion fails, in the stated witness class; not a claim of necessity in general.

| hypothesis | purpose | tightness | counterexample | witness class |
| --- | --- | --- | --- | --- |
| `hR : ReadsLive p L` | every use at a point (semantic read or halt output) is of a slot the mask declares live there (gen half of the certificate) | tight | `cex_wp_readsLive` | two instructions over 2 slots |
| `hT : TransferClosed p L` | a slot declared live at a successor and not overwritten by the instruction is declared live before it (transfer half of the certificate) | tight | `cex_wp_transferClosed` | two instructions over 1 slot |
| `hA : NoAssignClobber p L π` | an assignment never writes the shared target of a different kept slot that is declared live after it | tight | `cex_wp_noAssignClobber` | two instructions over 2 slots merged |
| `hM : NoMarkerClobber p L π` | a storage marker (which resets its slot) never resets the shared target of a different kept slot that is declared live after it | tight | `cex_wp_noMarkerClobber` | three instructions over 2 slots merged |
| `hQ : PostCorr p L π Q Q'` | Q and Q' agree on every pair of related halting states | tight | `cex_wp_postCorr` | a one-instruction program with Q = True, Q' = False |

**Depth:** shallow.

**Non-vacuity witness:** The loop pB with LB, πB and postB (x1 = 12 at the halt) and its transport: all hypotheses hold, wp holds for a run that goes once around the loop, and that entry store is CompactRel-related to its push-forward. Lean: `nonvacuous_wp_transport`, `nonvacuous_wp_transport_rel`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* AbsInt/CompCert at commit 2685140bf72c959446981fb99b5e44a8975021bc (read at that commit). backend/Stacking.v lays out activation records and maps local stack slot x to byte offset fe_ofs_local + 4 * x (offset_local, line 27), an injective slot renumbering; backend/Stackingproof.v proves transf_program_correct : forward_simulation (Linear.semantics prog) (Mach.semantics return_address_offset tprog) (lines 2201-2202) using forward_simulation_plus; backend/Linearizeproof.v proves a forward simulation from LTL to Linear for code linearization (lines 728-729), which concerns control-flow layout rather than slot assignment; backend/Allocproof.v proves a forward simulation for register allocation by validated translation from RTL to LTL (header lines 13-14, theorem lines 2528-2529). Modeling bridge (derived, not kernel-checked): realistic forward simulations, not lockstep bisimulations of this toy.

**Design question:** When does a verification condition proved for the original program transfer to the compacted program, or back, and for which postconditions?

**Non-claims:** listed under **Boundaries**, `wp-transport-no-clobber`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. A verification pipeline that reasons about a slot-compacted function body could move total-correctness statements across the compaction if the real pass satisfied the toy hypotheses; whether any real pass (for example rustc MIR passes or CompCert's `Stacking`) does is not examined. This card neither establishes nor refutes the corresponding property of any real compiler pass or verifier (model–system relation: none proved).

### `transportable-postconditions-characterization` (characterization)

**Tier:** T1. 'Postconditions may mention only live variables' is folklore; the exact class, and which direction needs which hypothesis, is made precise.

**Plain claim:** For any slot map π: if a postcondition Q depends, at every halt of p, only on the slots the mask declares live there, then pullPost π Q (Q evaluated on the pulled-back store) agrees with Q on every pair of CompactRel-related halting states. If moreover π is injective on the live slots at each halt, the converse also holds: Q has some compacted counterpart Q' agreeing with it on all related halting states if and only if Q depends only on live slots at every halt.

**Lean statements** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/WP.lean:9
variable {N M : Nat}

-- lean/ToySlotCompact/WP.lean:155-157
theorem exists_postCorr_iff_dependsOnlyOnLive (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hinj : ∀ pc, IsHalt p pc → InjOnLiveAt p L π pc) (Q : State N → Prop) :
    (∃ Q' : State M → Prop, PostCorr p L π Q Q') ↔ DependsOnlyOnLive p L Q := …

-- lean/ToySlotCompact/WP.lean:142-143
theorem postCorr_pullPost {p : Prog N} {L : Ann N} (π : Compaction p L M) {Q : State N → Prop}
    (hQ : DependsOnlyOnLive p L Q) : PostCorr p L π Q (pullPost π Q) := …
```

**Hypothesis ledger.** `tight`: the counterexample satisfies all other hypotheses of the named theorem and the conclusion fails, in the stated witness class; not a claim of necessity in general.

| hypothesis | purpose | tightness | counterexample | witness class |
| --- | --- | --- | --- | --- |
| `hinj : ∀ pc, IsHalt p pc → InjOnLiveAt p L π pc (hypothesis of exists_postCorr_iff_dependsOnlyOnLive)` | needed in the proof of the direction from a counterpart to DependsOnlyOnLive: merged live slots make some original halting states unrelatable, so Q can depend on dead slots there | tight | `cex_postClass_injAtHalts` | a one-instruction program over 3 slots with two live slots merged |
| `hQ : DependsOnlyOnLive p L Q (hypothesis of postCorr_pullPost)` | pullPost reads dropped slots as 0, so it can disagree with a Q that inspects dead slots (cex_postCorr_pullPost_dependsOnlyOnLive) | tight | `cex_postCorr_pullPost_dependsOnlyOnLive` | a one-instruction program over 1 slot with nothing live, Q reading the dropped slot |

**Depth:** shallow.

**Non-vacuity witness:** pB with LB, πB and postB (x1 = 12 at the halt): πB is injective on the slots LB declares live at the halt, and postB depends only on live slots, so both theorems apply with nontrivial content. Lean: `nonvacuous_postClass`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* Andrew W. Appel, Modern Compiler Implementation in ML (also in Java and in C), Cambridge University Press, 1998: chapter 10 'Liveness analysis' with sections 'Solution of dataflow equations', 'Liveness in the Tiger compiler' and 'Interference graph construction', and chapter 11 'Register allocation' (chapter and section titles verified on the author's table-of-contents page; chapter text not read here).

**Design question:** When does a verification condition proved for the original program transfer to the compacted program, or back, and for which postconditions?

**Non-claims:** listed under **Boundaries**, `transportable-postconditions-characterization`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. For a verifier that states postconditions over a slot-indexed store, the theorem says (in the toy) which postconditions have a counterpart after compaction; applying it to a real pipeline requires the real pass to satisfy the toy's hypotheses, which is not examined. This card neither establishes nor refutes the corresponding property of any real compiler pass or verifier (model–system relation: none proved).

### `vc-transfer-original-to-compacted` (theorem)

**Tier:** T1. Verification conditions transfer along a correct compilation step: folklore made precise.

**Plain claim:** If the mask L is a liveness certificate for p, π satisfies NoAssignClobber and NoMarkerClobber, and Q depends only on live slots at every halt, then: if for every store σ, Pre σ implies wp p Q from the entry state with store σ, then for every compacted store σ', Pre (pullStore π σ') implies wp (compact p L π) (pullPost π Q) from the entry state with store σ'. No injectivity at entry and no condition on Pre is assumed; the price is that the transported precondition Pre ∘ pullStore π can be unsatisfiable although Pre is satisfiable (see the non-claims).

**Lean statement** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/WP.lean:9
variable {N M : Nat}

-- lean/ToySlotCompact/WP.lean:181-186
theorem vc_forward_of_noClobber (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hR : ReadsLive p L) (hT : TransferClosed p L) (hA : NoAssignClobber p L π)
    (hM : NoMarkerClobber p L π) (Pre : Store N → Prop) (Q : State N → Prop)
    (hQ : DependsOnlyOnLive p L Q) :
    (∀ σ, Pre σ → wp p Q ⟨0, σ⟩) →
      (∀ σ', Pre (pullStore π σ') → wp (compact p L π) (pullPost π Q) ⟨0, σ'⟩) := …
```

Unfolded conclusion (`wp` unfolded; checked to be definitionally equal to the conclusion):

```lean
(∀ σ, Pre σ → ∃ n sf, exec p n ⟨0, σ⟩ = some sf ∧ Q sf) →
  ∀ σ', Pre (pullStore π σ') → ∃ n sf, exec (compact p L π) n ⟨0, σ'⟩ = some sf ∧ pullPost π Q sf
```

**Hypothesis ledger.** `tight`: the counterexample satisfies all other hypotheses of the named theorem and the conclusion fails, in the stated witness class; not a claim of necessity in general.

| hypothesis | purpose | tightness | counterexample | witness class |
| --- | --- | --- | --- | --- |
| `hR : ReadsLive p L` | every use at a point (semantic read or halt output) is of a slot the mask declares live there (gen half of the certificate) | tight | `cex_vcFwd_readsLive` | three instructions over 2 slots merged into 1 |
| `hT : TransferClosed p L` | a slot declared live at a successor and not overwritten by the instruction is declared live before it (transfer half of the certificate) | tight | `cex_vcFwd_transferClosed` | three instructions over 2 slots merged into 1 |
| `hA : NoAssignClobber p L π` | an assignment never writes the shared target of a different kept slot that is declared live after it | tight | `cex_vcFwd_noAssignClobber` | two instructions over 2 slots merged |
| `hM : NoMarkerClobber p L π` | a storage marker (which resets its slot) never resets the shared target of a different kept slot that is declared live after it | tight | `cex_vcFwd_noMarkerClobber` | three instructions over 2 slots merged |
| `hQ : DependsOnlyOnLive p L Q` | Q mentions only slots live at each halt | tight | `cex_vcFwd_post` | a dead store over 1 slot with Q reading the dropped slot |

**Depth:** shallow.

**Non-vacuity witness:** pS with preS (x0 = 0) and postS (x1 = 1 at the halt): all hypotheses hold, preS and the transported precondition are satisfiable, and the original condition (the premise) is proved. Lean: `nonvacuous_vc`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* AbsInt/CompCert at commit 2685140bf72c959446981fb99b5e44a8975021bc (read at that commit). backend/Stacking.v lays out activation records and maps local stack slot x to byte offset fe_ofs_local + 4 * x (offset_local, line 27), an injective slot renumbering; backend/Stackingproof.v proves transf_program_correct : forward_simulation (Linear.semantics prog) (Mach.semantics return_address_offset tprog) (lines 2201-2202) using forward_simulation_plus; backend/Linearizeproof.v proves a forward simulation from LTL to Linear for code linearization (lines 728-729), which concerns control-flow layout rather than slot assignment; backend/Allocproof.v proves a forward simulation for register allocation by validated translation from RTL to LTL (header lines 13-14, theorem lines 2528-2529). Modeling bridge (derived, not kernel-checked): realistic forward simulations, not lockstep bisimulations of this toy.

**Design question:** When does a verification condition proved for the original program transfer to the compacted program, or back, and for which postconditions?

**Non-claims:** listed under **Boundaries**, `vc-transfer-original-to-compacted`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. The forward direction is the shape a verifier needs to reuse a proof about an original body for its compacted form; the vacuity caveat in the non-claims applies to any such reuse. Real pipelines are not examined. This card neither establishes nor refutes the corresponding property of any real compiler pass or verifier (model–system relation: none proved).

### `vc-transfer-compacted-to-original` (theorem)

**Tier:** T1. Reflecting verification conditions back through a compilation step is folklore; the additional hypotheses that make it work here (injectivity on the entry-live slots, a precondition on kept entry-live slots) are made precise, each tight in the witness class of its counterexample.

**Plain claim:** If the mask L is a liveness certificate for p, π satisfies NoAssignClobber and NoMarkerClobber and is injective on the kept slots live at entry, Pre depends only on kept entry-live slots, and Q depends only on live slots at every halt, then: if for every compacted store σ', Pre (pullStore π σ') implies wp (compact p L π) (pullPost π Q) from the entry state with store σ', then for every store σ, Pre σ implies wp p Q from the entry state with store σ.

**Lean statement** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/WP.lean:9
variable {N M : Nat}

-- lean/ToySlotCompact/WP.lean:196-201
theorem vc_backward_of_noClobber (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hR : ReadsLive p L) (hT : TransferClosed p L) (hA : NoAssignClobber p L π)
    (hM : NoMarkerClobber p L π) (hinj0 : InjOnLiveAt p L π 0) (Pre : Store N → Prop)
    (Q : State N → Prop) (hPre : DependsOnlyOnEntryLive p L Pre) (hQ : DependsOnlyOnLive p L Q) :
    (∀ σ', Pre (pullStore π σ') → wp (compact p L π) (pullPost π Q) ⟨0, σ'⟩) →
      (∀ σ, Pre σ → wp p Q ⟨0, σ⟩) := …
```

**Hypothesis ledger.** `tight`: the counterexample satisfies all other hypotheses of the named theorem and the conclusion fails, in the stated witness class; not a claim of necessity in general.

| hypothesis | purpose | tightness | counterexample | witness class |
| --- | --- | --- | --- | --- |
| `hR : ReadsLive p L` | every use at a point (semantic read or halt output) is of a slot the mask declares live there (gen half of the certificate) | tight | `cex_vcBwd_readsLive` | two instructions over 2 slots |
| `hT : TransferClosed p L` | a slot declared live at a successor and not overwritten by the instruction is declared live before it (transfer half of the certificate) | tight | `cex_vcBwd_transferClosed` | three instructions over 2 slots merged |
| `hA : NoAssignClobber p L π` | an assignment never writes the shared target of a different kept slot that is declared live after it | tight | `cex_vcBwd_noAssignClobber` | two instructions over 2 slots merged |
| `hM : NoMarkerClobber p L π` | a storage marker (which resets its slot) never resets the shared target of a different kept slot that is declared live after it | tight | `cex_vcBwd_noMarkerClobber` | three instructions over 2 slots merged |
| `hinj0 : InjOnLiveAt p L π 0` | gives every original entry store a related compacted entry store, pushStore π 0 σ | tight | `cex_vcBwd_injOnLiveAt` | one instruction, two entry-live slots merged |
| `hPre : DependsOnlyOnEntryLive p L Pre` | lets the precondition survive the round trip through pushStore and pullStore | tight | `cex_vcBwd_pre` | one instruction over 1 dead slot |
| `hQ : DependsOnlyOnLive p L Q` | Q mentions only slots live at each halt | tight | `cex_vcBwd_post` | one instruction over 1 dead slot |

**Depth:** shallow.

**Non-vacuity witness:** pC with the non-injective πCm, preC (x0 = 4) and postC (x1 = 5 at the halt): all hypotheses hold, the transported precondition is satisfiable, and the compacted verification condition (the premise) is proved directly. Lean: `nonvacuous_vc_bwd_sharing`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* AbsInt/CompCert at commit 2685140bf72c959446981fb99b5e44a8975021bc (read at that commit). backend/Stacking.v lays out activation records and maps local stack slot x to byte offset fe_ofs_local + 4 * x (offset_local, line 27), an injective slot renumbering; backend/Stackingproof.v proves transf_program_correct : forward_simulation (Linear.semantics prog) (Mach.semantics return_address_offset tprog) (lines 2201-2202) using forward_simulation_plus; backend/Linearizeproof.v proves a forward simulation from LTL to Linear for code linearization (lines 728-729), which concerns control-flow layout rather than slot assignment; backend/Allocproof.v proves a forward simulation for register allocation by validated translation from RTL to LTL (header lines 13-14, theorem lines 2528-2529). Modeling bridge (derived, not kernel-checked): realistic forward simulations, not lockstep bisimulations of this toy.

**Design question:** When does a verification condition proved for the original program transfer to the compacted program, or back, and for which postconditions?

**Non-claims:** listed under **Boundaries**, `vc-transfer-compacted-to-original`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. The backward direction is the shape a verifier needs when it proves properties of compacted code (for example code after local renumbering) and wants them for the source body. Real pipelines are not examined. This card neither establishes nor refutes the corresponding property of any real compiler pass or verifier (model–system relation: none proved).

### `non-live-read-breaks-compaction` (counterexample)

**Role:** reference card.

**Tier:** T1. Concrete kernel-checked instance of the folklore pitfall of reading a slot that the liveness information declares dead.

**Plain claim:** For p = [x1 := x0; halt [x1]] over 2 slots, the mask LR that declares only x1 live and only at the halt (it omits x0 at the read but is transfer closed), and the injective map πR of the kept slot x1 onto one slot: every hypothesis of compact-bisim-no-clobber, compact-bisim-injective and wp-transport-no-clobber except ReadsLive holds, and each conclusion fails. Concretely, from any original store σ the original halts with x1 = σ x0 (pR_exec), while the compacted program reads the dropped x0 as the constant 0 and halts with its slot equal to 0 (pR_exec_c); so from the entry stores (x0 = 7, x1 = 0) and (0), which are CompactRel-related (pR_rel), the original halts with x1 = 7 and the compacted program with 0.

**Lean statements** (verbatim source; proofs elided as `:= …`; the concrete instance definitions come first):

```lean
-- lean/ToySlotCompact/Instances.lean:169-169
def pR : Prog 2 := [.assign 1 (.slot 0), .halt [1]]

-- lean/ToySlotCompact/Instances.lean:171-171
def LR : Ann 2 := fun pc i => decide (pc = 1 ∧ i = 1)

-- lean/ToySlotCompact/Instances.lean:173-173
def πR : Compaction pR LR 1 := fun _ => 0

-- lean/ToySlotCompact/Instances.lean:197-197
def postR7 : State 2 → Prop := postAt 1 1 7

-- lean/ToySlotCompact/Decide.lean:160-160
def postAt (h : Nat) (j : Fin N) (v : Nat) : State N → Prop := fun s => s.pc = h → s.st j = v

-- lean/ToySlotCompact/Counterexamples.lean:16-19
theorem cex_bisim_noClobber_readsLive :
    ¬ ReadsLive pR LR ∧ TransferClosed pR LR ∧ DbgReadsLive pR LR ∧ NoAssignClobber pR LR πR ∧
      NoMarkerClobber pR LR πR ∧
      ¬ LockstepBisim pR (compact pR LR πR) (CompactRel pR LR πR) := …

-- lean/ToySlotCompact/Counterexamples.lean:53-55
theorem cex_bisim_injective_readsLive :
    Function.Injective πR ∧ ¬ ReadsLive pR LR ∧ TransferClosed pR LR ∧ DbgReadsLive pR LR ∧
      ¬ LockstepBisim pR (compact pR LR πR) (CompactRel pR LR πR) := …

-- lean/ToySlotCompact/Counterexamples.lean:87-91
theorem cex_wp_readsLive :
    ¬ ReadsLive pR LR ∧ TransferClosed pR LR ∧ NoAssignClobber pR LR πR ∧
      NoMarkerClobber pR LR πR ∧ PostCorr pR LR πR postR7 (pullPost πR postR7) ∧
      ¬ (∀ s s', CompactRel pR LR πR s s' →
        (wp pR postR7 s ↔ wp (compact pR LR πR) (pullPost πR postR7) s')) := …

-- lean/ToySlotCompact/Instances.lean:203-203
theorem pR_rel : CompactRel pR LR πR ⟨0, fun i => if i = 0 then 7 else 0⟩ ⟨0, fun _ => 0⟩ := …

-- lean/ToySlotCompact/Instances.lean:192-192
theorem pR_exec (σ : Store 2) : exec pR 2 ⟨0, σ⟩ = some ⟨1, upd σ 1 (σ 0)⟩ := …

-- lean/ToySlotCompact/Instances.lean:193-194
theorem pR_exec_c (σ' : Store 1) :
    exec (compact pR LR πR) 2 ⟨0, σ'⟩ = some ⟨1, upd σ' 0 0⟩ := …
```

**Hypothesis ledger.** No hypotheses: every statement of this card is about a fixed concrete instance.

**Depth:** definitional.

**Non-vacuity witness:** Reference card: collects the canonical counterexamples used in the hypothesis ledgers of compact-bisim-no-clobber, compact-bisim-injective and wp-transport-no-clobber (hypothesis hR); the statement is itself a concrete instance, so no separate non-vacuity witness applies.

**Positive control:** not an impossibility result. The nearby settings in which the conclusions hold are the main theorems' non-vacuity witnesses (for example `nonvacuous_bisim_noClobber_sharing`, `nonvacuous_bisim_injective_loop`, `nonvacuous_wp_transport`).

**Prior art:**

* Andrew W. Appel, Modern Compiler Implementation in ML (also in Java and in C), Cambridge University Press, 1998: chapter 10 'Liveness analysis' with sections 'Solution of dataflow equations', 'Liveness in the Tiger compiler' and 'Interference graph construction', and chapter 11 'Register allocation' (chapter and section titles verified on the author's table-of-contents page; chapter text not read here).

**Design question:** When is renumbering a function's slots through a map from the live slots into a smaller index set a sound transformation for executions, and which conditions make it fail?

**Non-claims:** listed under **Boundaries**, `non-live-read-breaks-compaction`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. By analogy, a liveness annotation that omits an operand that is still read lets a pass drop the slot and read a stale or default value instead. This is an analogy, not a claim about any real analysis.

### `non-transfer-closed-mask-breaks-compaction` (counterexample)

**Role:** reference card.

**Tier:** T1. Concrete instance showing that a mask that satisfies the gen inequality but is not closed under the backward transfer fails bisimulation.

**Plain claim:** For p = [nop; halt [x0]] over 1 slot with the mask LT that declares x0 live at the halt but not before the nop (LT satisfies ReadsLive but is not transfer closed), the identity compaction satisfies every other hypothesis of compact-bisim-no-clobber, compact-bisim-injective and wp-transport-no-clobber, and each conclusion fails. Concretely (pT_first_step), the entry states with x0 = 7 and x0 = 0 are CompactRel-related because LT leaves x0 unconstrained at pc 0; one nop step takes both to pc 1, where LT declares x0 live, so the successor states are not related; the runs then halt with x0 = 7 and x0 = 0 respectively (pT_exec, pT_exec_c).

**Lean statements** (verbatim source; proofs elided as `:= …`; the concrete instance definitions come first):

```lean
-- lean/ToySlotCompact/Instances.lean:240-240
def pT : Prog 1 := [.nop, .halt [0]]

-- lean/ToySlotCompact/Instances.lean:242-242
def LT : Ann 1 := fun pc _ => decide (pc = 1)

-- lean/ToySlotCompact/Instances.lean:244-244
def πT : Compaction pT LT 1 := fun x => x.val

-- lean/ToySlotCompact/Instances.lean:260-260
def postT : State 1 → Prop := postAt 1 0 7

-- lean/ToySlotCompact/Decide.lean:160-160
def postAt (h : Nat) (j : Fin N) (v : Nat) : State N → Prop := fun s => s.pc = h → s.st j = v

-- lean/ToySlotCompact/Counterexamples.lean:22-25
theorem cex_bisim_noClobber_transferClosed :
    ReadsLive pT LT ∧ ¬ TransferClosed pT LT ∧ DbgReadsLive pT LT ∧ NoAssignClobber pT LT πT ∧
      NoMarkerClobber pT LT πT ∧
      ¬ LockstepBisim pT (compact pT LT πT) (CompactRel pT LT πT) := …

-- lean/ToySlotCompact/Counterexamples.lean:58-60
theorem cex_bisim_injective_transferClosed :
    Function.Injective πT ∧ ReadsLive pT LT ∧ ¬ TransferClosed pT LT ∧ DbgReadsLive pT LT ∧
      ¬ LockstepBisim pT (compact pT LT πT) (CompactRel pT LT πT) := …

-- lean/ToySlotCompact/Counterexamples.lean:95-99
theorem cex_wp_transferClosed :
    ReadsLive pT LT ∧ ¬ TransferClosed pT LT ∧ NoAssignClobber pT LT πT ∧
      NoMarkerClobber pT LT πT ∧ PostCorr pT LT πT postT (pullPost πT postT) ∧
      ¬ (∀ s s', CompactRel pT LT πT s s' →
        (wp pT postT s ↔ wp (compact pT LT πT) (pullPost πT postT) s')) := …

-- lean/ToySlotCompact/Boundaries.lean:228-232
theorem pT_first_step :
    CompactRel pT LT πT ⟨0, fun _ => 7⟩ ⟨0, fun _ => 0⟩ ∧
      step pT ⟨0, fun _ => 7⟩ = .running ⟨1, fun _ => 7⟩ none ∧
      step (compact pT LT πT) ⟨0, fun _ => 0⟩ = .running ⟨1, fun _ => 0⟩ none ∧
      ¬ CompactRel pT LT πT ⟨1, fun _ => 7⟩ ⟨1, fun _ => 0⟩ := …

-- lean/ToySlotCompact/Instances.lean:256-256
theorem pT_exec (σ : Store 1) : exec pT 2 ⟨0, σ⟩ = some ⟨1, σ⟩ := …

-- lean/ToySlotCompact/Instances.lean:257-257
theorem pT_exec_c (σ' : Store 1) : exec (compact pT LT πT) 2 ⟨0, σ'⟩ = some ⟨1, σ'⟩ := …
```

**Hypothesis ledger.** No hypotheses: every statement of this card is about a fixed concrete instance.

**Depth:** definitional.

**Non-vacuity witness:** Reference card: collects the canonical counterexamples used in the hypothesis ledgers of compact-bisim-no-clobber, compact-bisim-injective and wp-transport-no-clobber (hypothesis hT); the statement is itself a concrete instance, so no separate non-vacuity witness applies.

**Positive control:** not an impossibility result. The nearby settings in which the conclusions hold are the main theorems' non-vacuity witnesses (for example `nonvacuous_bisim_noClobber_sharing`, `nonvacuous_bisim_injective_loop`, `nonvacuous_wp_transport`).

**Prior art:**

* Andrew W. Appel, Modern Compiler Implementation in ML (also in Java and in C), Cambridge University Press, 1998: chapter 10 'Liveness analysis' with sections 'Solution of dataflow equations', 'Liveness in the Tiger compiler' and 'Interference graph construction', and chapter 11 'Register allocation' (chapter and section titles verified on the author's table-of-contents page; chapter text not read here).

**Design question:** When is renumbering a function's slots through a map from the live slots into a smaller index set a sound transformation for executions, and which conditions make it fail?

**Non-claims:** listed under **Boundaries**, `non-transfer-closed-mask-breaks-compaction`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. By analogy, a liveness annotation that is not closed under the backward transfer leaves a slot unconstrained at a point from which it is later read. This is an analogy, not a claim about any real analysis.

### `merging-simultaneously-live-slots-breaks-compaction` (counterexample)

**Role:** reference card.

**Tier:** T1. Concrete instance of the classic interference pitfall.

**Plain claim:** For p = [x1 := 5; halt [x0, x1]] over 2 slots with its path-liveness mask LA, the map πAm merging x0 and x1 into one slot satisfies the certificate, debug and marker conditions but neither injectivity nor NoAssignClobber, and the conclusions of compact-bisim-no-clobber, compact-bisim-injective, compact-kept-bisim-injective and wp-transport-no-clobber fail. Concretely, from any original store σ the original halts with x0 = σ x0 (pA_exec), while the compacted program halts with the shared slot equal to 5 (pA_exec_c); so from the entry stores (x0 = 3, x1 = 0) and (3), which are CompactRel-related (pA_rel), the original halts with x0 = 3 and the compacted program with 5.

**Lean statements** (verbatim source; proofs elided as `:= …`; the concrete instance definitions come first):

```lean
-- lean/ToySlotCompact/Instances.lean:35-35
def pA : Prog 2 := [.assign 1 (.const 5), .halt [0, 1]]

-- lean/ToySlotCompact/Instances.lean:37-37
def LA : Ann 2 := fun pc i => if pc = 0 then decide (i = 0) else decide (pc = 1)

-- lean/ToySlotCompact/Instances.lean:39-39
def πAm : Compaction pA LA 1 := fun _ => 0

-- lean/ToySlotCompact/Instances.lean:61-61
def postA : State 2 → Prop := postAt 1 0 3

-- lean/ToySlotCompact/Decide.lean:160-160
def postAt (h : Nat) (j : Fin N) (v : Nat) : State N → Prop := fun s => s.pc = h → s.st j = v

-- lean/ToySlotCompact/Counterexamples.lean:48-50
theorem cex_bisim_injective_injective :
    ¬ Function.Injective πAm ∧ ReadsLive pA LA ∧ TransferClosed pA LA ∧ DbgReadsLive pA LA ∧
      ¬ LockstepBisim pA (compact pA LA πAm) (CompactRel pA LA πAm) := …

-- lean/ToySlotCompact/Counterexamples.lean:34-37
theorem cex_bisim_noClobber_noAssignClobber :
    ReadsLive pA LA ∧ TransferClosed pA LA ∧ DbgReadsLive pA LA ∧ ¬ NoAssignClobber pA LA πAm ∧
      NoMarkerClobber pA LA πAm ∧
      ¬ LockstepBisim pA (compact pA LA πAm) (CompactRel pA LA πAm) := …

-- lean/ToySlotCompact/Counterexamples.lean:70-72
theorem cex_keptBisim_injective :
    ¬ Function.Injective πAm ∧ ReadsKept pA LA ∧ DbgReadsKept pA LA ∧
      ¬ LockstepBisim pA (compact pA LA πAm) (KeptRel pA LA πAm) := …

-- lean/ToySlotCompact/Counterexamples.lean:103-107
theorem cex_wp_noAssignClobber :
    ReadsLive pA LA ∧ TransferClosed pA LA ∧ ¬ NoAssignClobber pA LA πAm ∧
      NoMarkerClobber pA LA πAm ∧ PostCorr pA LA πAm postA (pullPost πAm postA) ∧
      ¬ (∀ s s', CompactRel pA LA πAm s s' →
        (wp pA postA s ↔ wp (compact pA LA πAm) (pullPost πAm postA) s')) := …

-- lean/ToySlotCompact/Instances.lean:77-77
theorem pA_rel : CompactRel pA LA πAm ⟨0, fun i => if i = 0 then 3 else 0⟩ ⟨0, fun _ => 3⟩ := …

-- lean/ToySlotCompact/Instances.lean:54-54
theorem pA_exec (σ : Store 2) : exec pA 2 ⟨0, σ⟩ = some ⟨1, upd σ 1 5⟩ := …

-- lean/ToySlotCompact/Instances.lean:55-56
theorem pA_exec_c (σ' : Store 1) :
    exec (compact pA LA πAm) 2 ⟨0, σ'⟩ = some ⟨1, upd σ' 0 5⟩ := …
```

**Hypothesis ledger.** No hypotheses: every statement of this card is about a fixed concrete instance.

**Depth:** definitional.

**Non-vacuity witness:** Reference card: collects the canonical counterexamples used in the hypothesis ledgers of compact-bisim-injective and compact-kept-bisim-injective (hypothesis hInj), compact-bisim-no-clobber and wp-transport-no-clobber (hypothesis hA); the statement is itself a concrete instance, so no separate non-vacuity witness applies.

**Positive control:** not an impossibility result. The nearby settings in which the conclusions hold are the main theorems' non-vacuity witnesses (for example `nonvacuous_bisim_noClobber_sharing`, `nonvacuous_bisim_injective_loop`, `nonvacuous_wp_transport`).

**Prior art:**

* llvm/llvm-project at commit 25b1c803e1e1504f6dc11f7afd68e65ad3ee5964, file llvm/lib/CodeGen/StackSlotColoring.cpp (read at that commit). Spill slots are colored so that a color is reused only when the slot's live interval does not overlap the intervals already given that color (ColorAssignmentInfo::overlaps, lines 109-115; StackSlotColoring::ColorSlot from line 303). Modeling bridge (derived, not kernel-checked): a non-injective compaction under an interference condition on live intervals; the package's NoAssignClobber/NoMarkerClobber (write versus live-after) conditions are a different formulation and no equivalence is claimed.
* Andrew W. Appel, Modern Compiler Implementation in ML (also in Java and in C), Cambridge University Press, 1998: chapter 10 'Liveness analysis' with sections 'Solution of dataflow equations', 'Liveness in the Tiger compiler' and 'Interference graph construction', and chapter 11 'Register allocation' (chapter and section titles verified on the author's table-of-contents page; chapter text not read here).

**Design question:** When is renumbering a function's slots through a map from the live slots into a smaller index set a sound transformation for executions, and which conditions make it fail?

**Non-claims:** listed under **Boundaries**, `merging-simultaneously-live-slots-breaks-compaction`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. By analogy with LLVM's `StackSlotColoring`, which reuses a colour only when live intervals do not overlap: merging two slots that are live at the same time loses one of the values. This is an analogy, not a claim about LLVM.

### `marker-reset-breaks-slot-sharing` (counterexample)

**Role:** reference card.

**Tier:** T1. Concrete instance of the folklore pitfall that a lifetime-start marker acts as a write.

**Plain claim:** For p = [StorageLive(x1); x1 := x0; halt [x1]] over 2 slots with its path-liveness mask LM, the map πMm merging x0 and x1 into one slot satisfies the certificate, debug and NoAssignClobber conditions but not NoMarkerClobber, and the conclusions of compact-bisim-no-clobber and wp-transport-no-clobber fail. Concretely, from any original store σ the original halts with x1 = σ x0 (pM_exec), while in the compacted program StorageLive resets the shared slot, destroying x0 before it is copied, and the run halts with its slot equal to 0 (pM_exec_c).

**Lean statements** (verbatim source; proofs elided as `:= …`; the concrete instance definitions come first):

```lean
-- lean/ToySlotCompact/Instances.lean:111-111
def pM : Prog 2 := [.storageLive 1, .assign 1 (.slot 0), .halt [1]]

-- lean/ToySlotCompact/Instances.lean:113-113
def LM : Ann 2 := fun pc i => if pc ≤ 1 then decide (i = 0) else decide (pc = 2 ∧ i = 1)

-- lean/ToySlotCompact/Instances.lean:115-115
def πMm : Compaction pM LM 1 := fun _ => 0

-- lean/ToySlotCompact/Instances.lean:130-130
def postM : State 2 → Prop := postAt 2 1 3

-- lean/ToySlotCompact/Decide.lean:160-160
def postAt (h : Nat) (j : Fin N) (v : Nat) : State N → Prop := fun s => s.pc = h → s.st j = v

-- lean/ToySlotCompact/Counterexamples.lean:40-43
theorem cex_bisim_noClobber_noMarkerClobber :
    ReadsLive pM LM ∧ TransferClosed pM LM ∧ DbgReadsLive pM LM ∧ NoAssignClobber pM LM πMm ∧
      ¬ NoMarkerClobber pM LM πMm ∧
      ¬ LockstepBisim pM (compact pM LM πMm) (CompactRel pM LM πMm) := …

-- lean/ToySlotCompact/Counterexamples.lean:111-115
theorem cex_wp_noMarkerClobber :
    ReadsLive pM LM ∧ TransferClosed pM LM ∧ NoAssignClobber pM LM πMm ∧
      ¬ NoMarkerClobber pM LM πMm ∧ PostCorr pM LM πMm postM (pullPost πMm postM) ∧
      ¬ (∀ s s', CompactRel pM LM πMm s s' →
        (wp pM postM s ↔ wp (compact pM LM πMm) (pullPost πMm postM) s')) := …

-- lean/ToySlotCompact/Instances.lean:125-125
theorem pM_exec (σ : Store 2) : exec pM 3 ⟨0, σ⟩ = some ⟨2, upd (upd σ 1 0) 1 (σ 0)⟩ := …

-- lean/ToySlotCompact/Instances.lean:126-127
theorem pM_exec_c (σ' : Store 1) :
    exec (compact pM LM πMm) 3 ⟨0, σ'⟩ = some ⟨2, upd (upd σ' 0 0) 0 0⟩ := …
```

**Hypothesis ledger.** No hypotheses: every statement of this card is about a fixed concrete instance.

**Depth:** definitional.

**Non-vacuity witness:** Reference card: collects the canonical counterexamples used in the hypothesis ledgers of compact-bisim-no-clobber and wp-transport-no-clobber (hypothesis hM); the statement is itself a concrete instance, so no separate non-vacuity witness applies.

**Positive control:** not an impossibility result. The nearby settings in which the conclusions hold are the main theorems' non-vacuity witnesses (for example `nonvacuous_bisim_noClobber_sharing`, `nonvacuous_bisim_injective_loop`, `nonvacuous_wp_transport`).

**Prior art:**

* llvm/llvm-project at commit 25b1c803e1e1504f6dc11f7afd68e65ad3ee5964, file llvm/lib/CodeGen/StackColoring.cpp (read at that commit), implementation notes lines 135-160: rules L1-L7 (lines 138-152) say that on a lifetime.start a stack slot is marked in-scope 'and the stack slot is overwritten with undef' (L2, lines 141-142), that lifetime.end marks it out-of-scope (L3) and that memory accesses to out-of-scope slots are UB (L6, line 147); lines 154-160 define a slot as in-use at a point 'if it either can be written to at that point, or if it has a live and non-undef content at that point' and state that slots never in-use together can be merged. Modeling bridge (derived, not kernel-checked): a lifetime start behaves as a write, the analogue of counting storage markers as writes in NoMarkerClobber; unlike LLVM, the toy resets slots to 0 at both markers instead of making later access undefined.
* rust-lang/rust at commit c7d5ba59d8e11ee2e2204b173458eec4cb41c973, file compiler/rustc_mir_transform/src/simplify.rs (read at that commit). The SimplifyLocals pass (enum at line 436, run_pass from line 455) counts actual uses of each local (UsedLocals), treats the return place, the arguments and locals referenced by debug info as always used (line 529: always_used = debuginfo_locals(body)), turns assignments and StorageLive/StorageDead statements of unused locals into nops (remove_unused_definitions_helper from line 629; make_nop at line 659), and renumbers the remaining locals in order (make_local_map from line 496). Removal is iterated to a fixed point (comment at lines 461-466; loop 'while modified' at line 636): removing a statement decrements the use counts of the locals it read (statement_removed, line 658), so chains of dead assignments disappear; uses through indirect places (line 568) and right-hand sides that are not safe to remove (line 600) are kept. Modeling bridge (derived, not kernel-checked): an injective, order-preserving compaction keyed on use counts rather than per-point liveness, which is the shape of compact_keptRel_lockstepBisim_of_injective; the toy's single-pass ReadsKept does not model the fixed-point cascade, and the toy keeps nops in place whereas rustc strips them (line 661).

**Design question:** When is renumbering a function's slots through a map from the live slots into a smaller index set a sound transformation for executions, and which conditions make it fail?

**Non-claims:** listed under **Boundaries**, `marker-reset-breaks-slot-sharing`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. LLVM's `StackColoring` notes treat `lifetime.start` as overwriting the slot with `undef` and count slots that can be written at a point as in use; the toy's `NoMarkerClobber` likewise treats storage markers as writes. The toy resets to `0` where LLVM makes the content undefined. This is an analogy, not a claim about LLVM.

### `dead-debug-read-breaks-lockstep-bisimulation` (counterexample)

**Role:** reference card.

**Tier:** T1. Concrete instance of the folklore pitfall that debuggers can observe dead variables.

**Plain claim:** For p = [dbg x0; halt []] over 1 slot with the empty mask (nothing is live, because debug reads are not liveness uses) and the empty compaction πD, every hypothesis of compact-bisim-no-clobber, compact-bisim-injective and compact-kept-bisim-injective except the debug condition holds, and each conclusion fails: at entry the original emits the debug event x0, while the compacted program reads the dropped slot as the constant 0 and emits 0 (pD_events), so the events differ exactly when the initial x0 is nonzero.

**Lean statements** (verbatim source; proofs elided as `:= …`; the concrete instance definitions come first):

```lean
-- lean/ToySlotCompact/Instances.lean:282-282
def pD : Prog 1 := [.dbg (.slot 0), .halt []]

-- lean/ToySlotCompact/Instances.lean:284-284
def LD : Ann 1 := fun _ _ => false

-- lean/ToySlotCompact/Instances.lean:286-286
def πD : Compaction pD LD 1 := fun _ => 0

-- lean/ToySlotCompact/Counterexamples.lean:28-31
theorem cex_bisim_noClobber_dbgReadsLive :
    ReadsLive pD LD ∧ TransferClosed pD LD ∧ ¬ DbgReadsLive pD LD ∧ NoAssignClobber pD LD πD ∧
      NoMarkerClobber pD LD πD ∧
      ¬ LockstepBisim pD (compact pD LD πD) (CompactRel pD LD πD) := …

-- lean/ToySlotCompact/Counterexamples.lean:63-65
theorem cex_bisim_injective_dbgReadsLive :
    Function.Injective πD ∧ ReadsLive pD LD ∧ TransferClosed pD LD ∧ ¬ DbgReadsLive pD LD ∧
      ¬ LockstepBisim pD (compact pD LD πD) (CompactRel pD LD πD) := …

-- lean/ToySlotCompact/Counterexamples.lean:80-82
theorem cex_keptBisim_dbgReadsKept :
    Function.Injective πD ∧ ReadsKept pD LD ∧ ¬ DbgReadsKept pD LD ∧
      ¬ LockstepBisim pD (compact pD LD πD) (KeptRel pD LD πD) := …

-- lean/ToySlotCompact/Boundaries.lean:221-222
theorem pD_events (σ σ' : Store 1) :
    (step pD ⟨0, σ⟩).ev = some (σ 0) ∧ (step (compact pD LD πD) ⟨0, σ'⟩).ev = some 0 := …
```

**Hypothesis ledger.** No hypotheses: every statement of this card is about a fixed concrete instance.

**Depth:** definitional.

**Non-vacuity witness:** Reference card: collects the canonical counterexamples used in the hypothesis ledgers of compact-bisim-no-clobber and compact-bisim-injective (hypothesis hD) and compact-kept-bisim-injective (hypothesis hDK); the statement is itself a concrete instance, so no separate non-vacuity witness applies.

**Positive control:** not an impossibility result. The nearby settings in which the conclusions hold are the main theorems' non-vacuity witnesses (for example `nonvacuous_bisim_noClobber_sharing`, `nonvacuous_bisim_injective_loop`, `nonvacuous_wp_transport`).

**Prior art:**

* rust-lang/rust at commit c7d5ba59d8e11ee2e2204b173458eec4cb41c973, file compiler/rustc_mir_transform/src/simplify.rs (read at that commit). The SimplifyLocals pass (enum at line 436, run_pass from line 455) counts actual uses of each local (UsedLocals), treats the return place, the arguments and locals referenced by debug info as always used (line 529: always_used = debuginfo_locals(body)), turns assignments and StorageLive/StorageDead statements of unused locals into nops (remove_unused_definitions_helper from line 629; make_nop at line 659), and renumbers the remaining locals in order (make_local_map from line 496). Removal is iterated to a fixed point (comment at lines 461-466; loop 'while modified' at line 636): removing a statement decrements the use counts of the locals it read (statement_removed, line 658), so chains of dead assignments disappear; uses through indirect places (line 568) and right-hand sides that are not safe to remove (line 600) are kept. Modeling bridge (derived, not kernel-checked): an injective, order-preserving compaction keyed on use counts rather than per-point liveness, which is the shape of compact_keptRel_lockstepBisim_of_injective; the toy's single-pass ReadsKept does not model the fixed-point cascade, and the toy keeps nops in place whereas rustc strips them (line 661).

**Design question:** When is renumbering a function's slots through a map from the live slots into a smaller index set a sound transformation for executions, and which conditions make it fail?

**Non-claims:** listed under **Boundaries**, `dead-debug-read-breaks-lockstep-bisimulation`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. rustc's `SimplifyLocals` treats locals referenced by debug info as always used, which avoids exactly this failure; the toy instead makes debug reads non-uses and adds the separate hypotheses `DbgReadsLive`/`DbgReadsKept`. This is an analogy, not a claim about rustc.

### `liveness-certificate-overapproximates` (theorem)

**Tier:** T0. Correctness of solutions of the backward liveness inequalities with respect to path liveness is textbook material; mechanized backward liveness analyses exist (CompCert Liveness.v).

**Plain claim:** If a mask L satisfies the gen inequality for p (every use at a point, i.e. every semantic read and halt output, is of a slot L declares live there) and the transfer inequality (a slot declared live at a successor and not overwritten by the instruction is declared live before it), and slot i is path-live at pc (some control-flow path from pc reaches a use of i, with no overwrite of i before that use), then L pc i = true.

**Lean statement** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/Liveness.lean:9
variable {N : Nat}

-- lean/ToySlotCompact/Liveness.lean:27-28
theorem pathLive_imp_mask_of_cert {p : Prog N} {L : Ann N} (hR : ReadsLive p L)
    (hT : TransferClosed p L) {pc : Nat} {i : Fin N} (h : PathLive p pc i) : L pc i = true := …
```

**Hypothesis ledger.** `tight`: the counterexample satisfies all other hypotheses of the named theorem and the conclusion fails, in the stated witness class; not a claim of necessity in general.

| hypothesis | purpose | tightness | counterexample | witness class |
| --- | --- | --- | --- | --- |
| `hR : ReadsLive p L` | every use at a point is declared live there (gen half of the certificate) | tight | `cex_cert_readsLive` | one instruction over 1 slot, empty mask |
| `hT : TransferClosed p L` | a slot declared live at a successor and not overwritten is declared live before (transfer half of the certificate) | tight | `cex_cert_transferClosed` | two instructions over 1 slot |
| `h : PathLive p pc i` | the conclusion is promised only for path-live slots | tight | `cex_cert_pathLive` | a 5-instruction loop over 3 slots whose certificate omits a never-used slot |

**Depth:** definitional.

**Non-vacuity witness:** The loop pB with its mask, where x0 is path-live at entry. Lean: `nonvacuous_cert`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* Andrew W. Appel, Modern Compiler Implementation in ML (also in Java and in C), Cambridge University Press, 1998: chapter 10 'Liveness analysis' with sections 'Solution of dataflow equations', 'Liveness in the Tiger compiler' and 'Interference graph construction', and chapter 11 'Register allocation' (chapter and section titles verified on the author's table-of-contents page; chapter text not read here).
* Flemming Nielson, Hanne Riis Nielson, Chris Hankin, Principles of Program Analysis, Springer, 1999, hardcover ISBN 978-3-540-65410-0, DOI 10.1007/978-3-662-03811-6 (ISBN and DOI read on the publisher page); chapter 2 'Data Flow Analysis', section 2.1.4 'Live Variables Analysis' (section number confirmed by table-of-contents listings found by search; section text not read here).
* Tobias Nipkow and Gerwin Klein, Concrete Semantics with Isabelle/HOL, Springer, 2014, DOI 10.1007/978-3-319-10542-0 (bibliographic data from search results): chapter 10 'Program Analysis', section 10.3 'Live Variable Analysis' (p. 164) and section 10.4 'True Liveness' (p. 172), titles and pages checked in the table of contents of the authors' freely available PDF; section text not read here. Cited for terminology: PathLive here is the plain live-variable notion of section 10.3; because the following section is titled 'True Liveness', this package does not use that name for PathLive.
* AbsInt/CompCert at commit 2685140bf72c959446981fb99b5e44a8975021bc (read at that commit). backend/Liveness.v ('Liveness analysis over RTL') computes liveness with Backward_Dataflow_Solver (line 111); its transfer function (lines 68-91) makes the arguments of an operation live only if the result register is live after it (lines 78-79), i.e. strong liveness, unlike PathLive here. backend/Deadcodeproof.v ('Elimination of unneeded computations over RTL: correctness proof') proves transf_program_correct : forward_simulation (RTL.semantics prog) (RTL.semantics tprog) (lines 1263-1264). Modeling bridge (derived, not kernel-checked): mechanized backward liveness and dead-computation elimination in a realistic compiler.

**Design question:** Can a certificate checker accept claimed liveness masks soundly, so that compaction can rely on checked rather than recomputed liveness?

**Non-claims:** listed under **Boundaries**, `liveness-certificate-overapproximates`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. Checking a claimed mask against the gen and transfer inequalities is the a-posteriori validation pattern of CompCert's register-allocation validator (Rideau and Leroy 2010), and CompCert's own liveness (`Liveness.v`) is a strong-liveness backward dataflow, unlike `PathLive`. This card neither establishes nor refutes the corresponding property of any real compiler pass or verifier (model–system relation: none proved).

### `liveness-checker-characterization-and-soundness` (theorem)

**Tier:** T0. Checking a claimed dataflow solution pointwise is standard, and mechanized validators of claimed allocation and liveness information exist (Rideau and Leroy 2010); made precise here.

**Plain claim:** The Boolean checker checkLive accepts a mask L for p exactly when L satisfies both certificate inequalities (ReadsLive and TransferClosed). Consequently, if checkLive accepts L and slot i is path-live at pc, then L pc i = true.

**Lean statements** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/Liveness.lean:9
variable {N : Nat}

-- lean/ToySlotCompact/Liveness.lean:107-108
theorem checkLive_eq_true_iff (p : Prog N) (L : Ann N) :
    checkLive p L = true ↔ ReadsLive p L ∧ TransferClosed p L := …

-- lean/ToySlotCompact/Liveness.lean:112-113
theorem checkLive_sound {p : Prog N} {L : Ann N} (h : checkLive p L = true) {pc : Nat}
    {i : Fin N} (hl : PathLive p pc i) : L pc i = true := …
```

Unfolded `checkLive_eq_true_iff` (`ReadsLive` and `TransferClosed` unfolded; checked to be definitionally equal to the statement):

```lean
checkLive p L = true ↔
  (∀ (pc : Nat) (ins : Instr N), p[pc]? = some ins → ∀ i, ins.uses i = true → L pc i = true) ∧
  (∀ (pc : Nat) (ins : Instr N), p[pc]? = some ins → ∀ s ∈ ins.succs pc, ∀ i, L s i = true →
    ins.defs i = false → L pc i = true)
```

**Hypothesis ledger.** `tight`: the counterexample satisfies all other hypotheses of the named theorem and the conclusion fails, in the stated witness class; not a claim of necessity in general.

| hypothesis | purpose | tightness | counterexample | witness class |
| --- | --- | --- | --- | --- |
| `h : checkLive p L = true (checkLive_sound)` | the conclusion is promised only for accepted masks | tight | `cex_checkLive_sound_accepted` | a one-instruction program over 1 slot with the empty mask |
| `hl : PathLive p pc i (checkLive_sound)` | the conclusion is promised only for path-live slots | tight | `cex_checkLive_sound_pathLive` | a 5-instruction loop over 3 slots, a never-used slot |

**Depth:** shallow.

**Non-vacuity witness:** On pB the mask LB is accepted and x0 is path-live at entry, so both hypotheses of checkLive_sound hold; both verdicts of checkLive occur (pB accepted, pR rejected), so both sides of the equivalence are inhabited. Lean: `nonvacuous_checkLive_sound`, `checkLive_both_verdicts`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* Silvain Rideau and Xavier Leroy, 'Validating Register Allocation and Spilling', Compiler Construction (CC 2010), LNCS 6011, Springer, 2010, pp. 224-243, DOI 10.1007/978-3-642-11970-5_13 (bibliographic data from search results; paper text not read here). The corresponding Coq development is AbsInt/CompCert backend/Allocation.v, whose header reads 'Register allocation by external oracle and a posteriori validation' (read at commit 2685140bf72c959446981fb99b5e44a8975021bc), with its proof in backend/Allocproof.v. Modeling bridge (derived, not kernel-checked): a mechanized validator for a proposed, generally non-injective, assignment of variables to locations, the analogue of checking a claimed mask and interference conditions instead of recomputing them.
* Andrew W. Appel, Modern Compiler Implementation in ML (also in Java and in C), Cambridge University Press, 1998: chapter 10 'Liveness analysis' with sections 'Solution of dataflow equations', 'Liveness in the Tiger compiler' and 'Interference graph construction', and chapter 11 'Register allocation' (chapter and section titles verified on the author's table-of-contents page; chapter text not read here).
* Flemming Nielson, Hanne Riis Nielson, Chris Hankin, Principles of Program Analysis, Springer, 1999, hardcover ISBN 978-3-540-65410-0, DOI 10.1007/978-3-662-03811-6 (ISBN and DOI read on the publisher page); chapter 2 'Data Flow Analysis', section 2.1.4 'Live Variables Analysis' (section number confirmed by table-of-contents listings found by search; section text not read here).
* AbsInt/CompCert at commit 2685140bf72c959446981fb99b5e44a8975021bc (read at that commit). backend/Liveness.v ('Liveness analysis over RTL') computes liveness with Backward_Dataflow_Solver (line 111); its transfer function (lines 68-91) makes the arguments of an operation live only if the result register is live after it (lines 78-79), i.e. strong liveness, unlike PathLive here. backend/Deadcodeproof.v ('Elimination of unneeded computations over RTL: correctness proof') proves transf_program_correct : forward_simulation (RTL.semantics prog) (RTL.semantics tprog) (lines 1263-1264). Modeling bridge (derived, not kernel-checked): mechanized backward liveness and dead-computation elimination in a realistic compiler.

**Design question:** Can a certificate checker accept claimed liveness masks soundly, so that compaction can rely on checked rather than recomputed liveness?

**Non-claims:** listed under **Boundaries**, `liveness-checker-characterization-and-soundness`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. `checkLive` corresponds to validating a claimed liveness annotation instead of trusting the analysis that produced it, as in translation validation of register allocation (Rideau and Leroy 2010). This card neither establishes nor refutes the corresponding property of any real compiler pass or verifier (model–system relation: none proved).

### `liveness-checker-rejects-omitted-path-live-slot` (theorem)

**Tier:** T0. Contrapositive of checker soundness; standard.

**Plain claim:** If slot i is path-live at pc in p and the mask L omits it there (L pc i = false), then checkLive p L = false.

**Lean statement** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/Liveness.lean:9
variable {N : Nat}

-- lean/ToySlotCompact/Liveness.lean:119-120
theorem checkLive_eq_false_of_missing {p : Prog N} {L : Ann N} {pc : Nat} {i : Fin N}
    (hl : PathLive p pc i) (hL : L pc i = false) : checkLive p L = false := …
```

**Hypothesis ledger.** `tight`: the counterexample satisfies all other hypotheses of the named theorem and the conclusion fails, in the stated witness class; not a claim of necessity in general.

| hypothesis | purpose | tightness | counterexample | witness class |
| --- | --- | --- | --- | --- |
| `hl : PathLive p pc i` | rejection is promised only for omitted slots that are path-live | tight | `cex_missing_requires_pathLive` | a 5-instruction loop over 3 slots whose mask omits a never-used slot |
| `hL : L pc i = false` | rejection is promised only when the slot is actually omitted | tight | `cex_missing_requires_omission` | the same loop with the slot present |

**Depth:** shallow.

**Non-vacuity witness:** pR with mask LR omits the path-live x0 at the read and is rejected. Lean: `checkLive_rejects_underapprox`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* Andrew W. Appel, Modern Compiler Implementation in ML (also in Java and in C), Cambridge University Press, 1998: chapter 10 'Liveness analysis' with sections 'Solution of dataflow equations', 'Liveness in the Tiger compiler' and 'Interference graph construction', and chapter 11 'Register allocation' (chapter and section titles verified on the author's table-of-contents page; chapter text not read here).
* Flemming Nielson, Hanne Riis Nielson, Chris Hankin, Principles of Program Analysis, Springer, 1999, hardcover ISBN 978-3-540-65410-0, DOI 10.1007/978-3-662-03811-6 (ISBN and DOI read on the publisher page); chapter 2 'Data Flow Analysis', section 2.1.4 'Live Variables Analysis' (section number confirmed by table-of-contents listings found by search; section text not read here).

**Design question:** Can a certificate checker accept claimed liveness masks soundly, so that compaction can rely on checked rather than recomputed liveness?

**Non-claims:** listed under **Boundaries**, `liveness-checker-rejects-omitted-path-live-slot`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. A validator built like `checkLive` rejects annotations that miss a path-live slot; real validators are not examined. This card neither establishes nor refutes the corresponding property of any real compiler pass or verifier (model–system relation: none proved).

### `path-liveness-least-certificate` (theorem)

**Tier:** T0. Path liveness is the least solution of the liveness inequalities: textbook material.

**Plain claim:** For every program p, the (noncomputable) path-liveness mask pathLiveMask p satisfies both certificate inequalities, is accepted by checkLive, and is pointwise below every mask that satisfies both inequalities; so it is the least certificate.

**Lean statements** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/Liveness.lean:9
variable {N : Nat}

-- lean/ToySlotCompact/Liveness.lean:149-152
theorem pathLiveMask_least_cert (p : Prog N) :
    (ReadsLive p (pathLiveMask p) ∧ TransferClosed p (pathLiveMask p)) ∧
      ∀ L : Ann N, ReadsLive p L → TransferClosed p L →
        ∀ pc i, pathLiveMask p pc i = true → L pc i = true := …

-- lean/ToySlotCompact/Liveness.lean:144-144
theorem checkLive_pathLiveMask (p : Prog N) : checkLive p (pathLiveMask p) = true := …
```

**Hypothesis ledger.** No hypotheses: the statements hold for all values of their parameters.

**Depth:** shallow.

**Non-vacuity witness:** No hypotheses (holds for every program); pT_pathLive exhibits a nonempty path-live set. Lean: `pT_pathLive`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* Andrew W. Appel, Modern Compiler Implementation in ML (also in Java and in C), Cambridge University Press, 1998: chapter 10 'Liveness analysis' with sections 'Solution of dataflow equations', 'Liveness in the Tiger compiler' and 'Interference graph construction', and chapter 11 'Register allocation' (chapter and section titles verified on the author's table-of-contents page; chapter text not read here).
* Flemming Nielson, Hanne Riis Nielson, Chris Hankin, Principles of Program Analysis, Springer, 1999, hardcover ISBN 978-3-540-65410-0, DOI 10.1007/978-3-662-03811-6 (ISBN and DOI read on the publisher page); chapter 2 'Data Flow Analysis', section 2.1.4 'Live Variables Analysis' (section number confirmed by table-of-contents listings found by search; section text not read here).
* Tobias Nipkow and Gerwin Klein, Concrete Semantics with Isabelle/HOL, Springer, 2014, DOI 10.1007/978-3-319-10542-0 (bibliographic data from search results): chapter 10 'Program Analysis', section 10.3 'Live Variable Analysis' (p. 164) and section 10.4 'True Liveness' (p. 172), titles and pages checked in the table of contents of the authors' freely available PDF; section text not read here. Cited for terminology: PathLive here is the plain live-variable notion of section 10.3; because the following section is titled 'True Liveness', this package does not use that name for PathLive.

**Design question:** Can a certificate checker accept claimed liveness masks soundly, so that compaction can rely on checked rather than recomputed liveness?

**Non-claims:** listed under **Boundaries**, `path-liveness-least-certificate`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. Path liveness is the least fixed point that textbook backward live-variable analysis computes (Nielson, Nielson and Hankin; Nipkow and Klein); the theorem is the toy counterpart. This card neither establishes nor refutes the corresponding property of any real compiler pass or verifier (model–system relation: none proved).

### `store-laws-on-common-domain` (theorem)

**Tier:** T0. Read-over-write laws of function stores go back to McCarthy (1963) and reappear as lens laws (Foster et al. 2007); the association-list case is standard.

**Plain claim:** For every N and V, the indexed store funOps N V (a total function Fin N → V) satisfies GetPutSame, GetPutOther, PutGetId and PutPut. For every default d, the association-list store alistOps N d (first match wins; put replaces the first match or appends) satisfies GetPutSame, GetPutOther and PutPut on all lists, and PutGetId on complete lists (lists containing every key). When N ≥ 1 the empty list is incomplete and violates PutGetId (writing back the value read for slot 0 appends an entry); when N = 0, PutGetId holds.

**Lean statements** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/Stores.lean:16
variable {S S₁ S₂ V : Type} {N : Nat}

-- lean/ToySlotCompact/Stores.lean:53-55
theorem funOps_laws (N : Nat) (V : Type) :
    GetPutSame (funOps N V) ∧ GetPutOther (funOps N V) ∧ PutGetId (funOps N V) ∧
      PutPut (funOps N V) := …

-- lean/ToySlotCompact/Stores.lean:104-106
theorem alistOps_laws (N : Nat) (d : V) :
    GetPutSame (alistOps N d) ∧ GetPutOther (alistOps N d) ∧ PutPut (alistOps N d) ∧
      ∀ l : List (Fin N × V), Complete l → ∀ k, (alistOps N d).put l k ((alistOps N d).get l k) = l := …

-- lean/ToySlotCompact/Stores.lean:112-115
theorem alistOps_empty_not_putGetId (N : Nat) (d : V) :
    ¬ Complete ([] : List (Fin (N + 1) × V)) ∧
      (alistOps (N + 1) d).put [] ⟨0, Nat.zero_lt_succ N⟩
        ((alistOps (N + 1) d).get [] ⟨0, Nat.zero_lt_succ N⟩) ≠ [] := …

-- lean/ToySlotCompact/Stores.lean:124-124
theorem alistOps_zero_putGetId (d : V) : PutGetId (alistOps 0 d) := …
```

`alistOps_empty_not_putGetId` writes slot `0` of `Fin (N + 1)` as `⟨0, Nat.zero_lt_succ N⟩`.

**Hypothesis ledger.** `tight`: the counterexample satisfies all other hypotheses of the named theorem and the conclusion fails, in the stated witness class; not a claim of necessity in general.

| hypothesis | purpose | tightness | counterexample | witness class |
| --- | --- | --- | --- | --- |
| `Complete l (hypothesis of the PutGetId clause of alistOps_laws)` | writing back the read value appends a new entry when the key is absent | tight | `alistOps_empty_not_putGetId` | the empty list, for any number of slots N + 1 ≥ 1 |

**Depth:** shallow.

**Non-vacuity witness:** famAlist L is complete for every L; the remaining clauses have no hypotheses. Lean: `famAlist_complete`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* John McCarthy, 'Towards a Mathematical Science of Computation', Information Processing 1962 (Proceedings of IFIP Congress 62), C. M. Popplewell (ed.), North-Holland, 1963, pp. 21-28 (bibliographic data from search results). The author's web version of the paper (read) introduces c(var, ξ), the contents of a variable in a state vector, and a(var, val, ξ), assignment, with the axioms c(u, a(v, α, ξ)) = if u = v then α else c(u, ξ); a(v, c(v, ξ), ξ) = ξ; and a(u, α, a(v, β, ξ)) = if u = v then a(u, α, ξ) else a(v, β, a(u, α, ξ)). These are GetPutSame with GetPutOther, PutGetId, and PutPut (with commutation of writes to distinct keys) for the indexed store.
* J. Nathan Foster, Michael B. Greenwald, Jonathan T. Moore, Benjamin C. Pierce, Alan Schmitt, 'Combinators for Bidirectional Tree Transformations: A Linguistic Approach to the View-Update Problem', ACM Transactions on Programming Languages and Systems 29(3), Article 17, 2007, DOI 10.1145/1232420.1232424 (bibliographic data and law names from search results; paper text not read here): the lens laws PutGet, GetPut and PutPut, defining well-behaved and very well-behaved lenses. Viewing one key of a store as a lens, they correspond to GetPutSame, PutGetId and PutPut; GetPutOther (framing across keys) is not a single-lens law.
* Andrew W. Appel, Verified Functional Algorithms (Software Foundations, volume 3), chapter 'ADT: Abstract Data Types', https://softwarefoundations.cis.upenn.edu/vfa-current/ADT.html (opening of the chapter read: an association-table ADT with a formal specification that hides its implementation). Modeling bridge (derived, not kernel-checked): the textbook form, in Coq, of interchangeable table implementations behind an interface.

**Design question:** When is an array-backed indexed store a faithful replacement for an association-list store inside a certificate checker, and what does it buy in primitive operations?

**Non-claims:** listed under **Boundaries**, `store-laws-on-common-domain`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. Verification frameworks that model a function's locals either as a total map from indices or as an association list face the same distinction between observational laws (`GetPutSame`, `GetPutOther`) and representation-level laws (`PutGetId`, `PutPut`). No specific framework is examined. This card neither establishes nor refutes the corresponding property of any real compiler pass or verifier (model–system relation: none proved).

### `certificate-checker-representation-independence` (theorem)

**Tier:** T0. Representation independence for data abstraction is classical (Reynolds 1983) and mechanized for interchangeable map implementations (Isabelle Collections Framework; Verified Functional Algorithms, chapter ADT); proved here directly for one command language.

**Plain claim:** For the replay checker runCheck, which uses the store only through get and put: if two store implementations both satisfy GetPutSame and GetPutOther and the initial stores have the same view (equal get on every key), then the checker gives the same verdict on every command list. In particular, if the view of an association list l with default d is the indexed store σ (alistGet d l = σ), then the indexed store started from σ and the association-list store started from l give the same verdict on every command list.

**Lean statements** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/Stores.lean:16
variable {S S₁ S₂ V : Type} {N : Nat}

-- lean/ToySlotCompact/Stores.lean:173-176
theorem runCheck_eq_of_getPut (ops₁ : StoreOps S₁ N Nat) (ops₂ : StoreOps S₂ N Nat)
    (h1s : GetPutSame ops₁) (h1o : GetPutOther ops₁) (h2s : GetPutSame ops₂)
    (h2o : GetPutOther ops₂) (c : List (Cmd N)) (s₁ : S₁) (s₂ : S₂)
    (hview : ∀ k, ops₁.get s₁ k = ops₂.get s₂ k) : runCheck ops₁ s₁ c = runCheck ops₂ s₂ c := …

-- lean/ToySlotCompact/Stores.lean:192-194
theorem runCheck_funOps_eq_alistOps (d : Nat) (σ : Fin N → Nat) (l : List (Fin N × Nat))
    (hview : alistGet d l = σ) (c : List (Cmd N)) :
    runCheck (funOps N Nat) σ c = runCheck (alistOps N d) l c := …
```

**Hypothesis ledger.** `tight`: the counterexample satisfies all other hypotheses of the named theorem and the conclusion fails, in the stated witness class; not a claim of necessity in general.

| hypothesis | purpose | tightness | counterexample | witness class |
| --- | --- | --- | --- | --- |
| `h1s : GetPutSame ops₁` | reads after writes return the written value | tight | `cex_repInd_h1s` | 1 key, a store whose put is ignored |
| `h1o : GetPutOther ops₁` | writes do not disturb other keys (framing) | tight | `cex_repInd_h1o` | 2 keys, a store whose put zeroes other keys |
| `h2s : GetPutSame ops₂` | as h1s, for the second implementation | tight | `cex_repInd_h2s` | 1 key, a store whose put is ignored |
| `h2o : GetPutOther ops₂` | as h1o, for the second implementation | tight | `cex_repInd_h2o` | 2 keys, a store whose put zeroes other keys |
| `hview : ∀ k, ops₁.get s₁ k = ops₂.get s₂ k` | the initial views agree | tight | `cex_repInd_view` | 1 key, initial values 0 and 1 |
| `hview : alistGet d l = σ (runCheck_funOps_eq_alistOps)` | the association list's view is the indexed store | tight | `cex_repInd_funOps_alistOps_view` | 1 key, indexed store holding 1 versus the empty list with default 0 |

**Depth:** shallow.

**Non-vacuity witness:** The indexed store and a complete association list with the same view, on a script whose verdict is true, for both theorems. Lean: `nonvacuous_repInd`, `nonvacuous_repInd_funOps_alistOps`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* John C. Reynolds, 'Types, Abstraction and Parametric Polymorphism', Information Processing 83, R.E.A. Mason (ed.), Elsevier Science Publishers B.V. (North-Holland), 1983, pp. 513-523 (first page and abstract read from a scan; page range per dblp). The abstract generalizes homomorphisms to relations to obtain an 'abstraction' theorem; the opening example concerns two representations of complex numbers used interchangeably through their primitive operations. The package's result is a direct induction for one fixed command language, not an instance of the abstraction theorem.
* Peter Lammich (with contributions from Andreas Lochbihler and Thomas Tuerk), 'Collections Framework', Archive of Formal Proofs, November 25, 2009, https://www.isa-afp.org/entries/Collections.html (entry page read: an Isabelle/HOL collections library that uses data refinement from abstract specifications to concrete data structures; its theories include Impl_Array_Map); companion paper Peter Lammich and Andreas Lochbihler, 'The Isabelle Collections Framework', Interactive Theorem Proving (ITP 2010), pp. 339-354, DOI 10.1007/978-3-642-14052-5_24 (as listed on the entry page). Modeling bridge (derived, not kernel-checked): mechanized data refinement lets algorithms written against a map interface run on interchangeable implementations, the shape of runCheck_eq_of_getPut.
* Andrew W. Appel, Verified Functional Algorithms (Software Foundations, volume 3), chapter 'ADT: Abstract Data Types', https://softwarefoundations.cis.upenn.edu/vfa-current/ADT.html (opening of the chapter read: an association-table ADT with a formal specification that hides its implementation). Modeling bridge (derived, not kernel-checked): the textbook form, in Coq, of interchangeable table implementations behind an interface.

**Design question:** When is an array-backed indexed store a faithful replacement for an association-list store inside a certificate checker, and what does it buy in primitive operations?

**Non-claims:** listed under **Boundaries**, `certificate-checker-representation-independence`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. A certificate checker written against a get/put interface (as with the map interfaces of the Isabelle Collections Framework or the table ADT of Verified Functional Algorithms) can be run on either store representation. No specific checker is examined. This card neither establishes nor refutes the corresponding property of any real compiler pass or verifier (model–system relation: none proved).

### `alist-checker-toy-cost-theta-SL` (theorem)

**Tier:** T0. Linear-scan association lists cost time proportional to their length per access: folklore, stated in a toy cost model.

**Plain claim:** Toy cost-model theorem (not real performance), counting one primitive operation per association-list cell scanned by each get and put that runCheck performs (runCost stops at the first failing check, as runCheck does): (a) for the family of S increments of the last of K = L + 1 slots, run from the complete key-ordered list of length K, the checker scans exactly 2 S K cells; (b) for any command list c run from a complete association list l, it scans at most 2 · c.length · l.length cells. Hence on that family the cost is Θ(S · K), with K the number of slots.

**Lean statements** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/Stores.lean:16
variable {S S₁ S₂ V : Type} {N : Nat}

-- lean/ToySlotCompact/Stores.lean:324-326
theorem runCost_alistOps_family (S L : Nat) :
    runCost (alistOps (L + 1) 0) (alistCost (L + 1) Nat) (famAlist L) (famScript S L) =
      2 * S * (L + 1) := …

-- lean/ToySlotCompact/Stores.lean:280-281
theorem runCost_alistOps_le (d : Nat) (l : List (Fin N × Nat)) (hl : Complete l)
    (c : List (Cmd N)) : runCost (alistOps N d) (alistCost N Nat) l c ≤ 2 * c.length * l.length := …
```

Binder note: in both theorems the slot count is `N` (bound (b)) or `L + 1` (family (a)); `S : Nat` is the number of commands of `famScript S L`; `l.length` (bound (b)) is the length of the association list; when `Complete l` holds it is at least the number of slots (not proved here), and it may exceed the number of slots when keys repeat (`complete_with_repeated_keys`).

**Hypothesis ledger.** `tight`: the counterexample satisfies all other hypotheses of the named theorem and the conclusion fails, in the stated witness class; not a claim of necessity in general.

| hypothesis | purpose | tightness | counterexample | witness class |
| --- | --- | --- | --- | --- |
| `hl : Complete l (hypothesis of bound (b))` | puts never append to a complete list, so its length stays l.length | tight | `cex_alistCost_complete` | the empty list over 1 key, two commands |

**Depth:** shallow.

**Non-vacuity witness:** The family inputs are complete lists. Lean: `famAlist_complete`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* No source establishes these toy counts; they are self-contained cost-model facts. For context (not a source for these counts): verified association-list and array-backed map implementations coexist behind one interface in the Isabelle Collections Framework (Lammich, Archive of Formal Proofs, 2009, https://www.isa-afp.org/entries/Collections.html; entry page read).

**Design question:** When is an array-backed indexed store a faithful replacement for an association-list store inside a certificate checker, and what does it buy in primitive operations?

**Non-claims:** listed under **Boundaries**, `alist-checker-toy-cost-theta-SL`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. These are counts in a toy cost model (model–system relation: none proved); they neither establish nor refute any running-time or memory claim about a real checker or store implementation.

### `unit-cost-checker-toy-cost-O-S` (theorem)

**Tier:** T0. Constant cost per access gives cost linear in the number of commands: immediate in a unit-cost model.

**Plain claim:** Toy cost-model theorem (not real performance): under the unit cost model unitCost, which charges one primitive operation per get and per put (the usual model of an array indexed by slot number), the run of runCheck over any store implementation and any command list c costs at most 2 · c.length operations, independent of the number of slots, and exactly 2 S on the family of S increments. The bound comes from the cost model alone: it holds for every StoreOps, including the association-list store; the indexed store funOps is the intended instantiation.

**Lean statements** (verbatim source; proofs elided as `:= …`; the `variable` line of the source file, which supplies the implicit parameters, comes first):

```lean
-- lean/ToySlotCompact/Stores.lean:16
variable {S S₁ S₂ V : Type} {N : Nat}

-- lean/ToySlotCompact/Stores.lean:262-263
theorem runCost_unitCost_le (ops : StoreOps S N Nat) (s : S) (c : List (Cmd N)) :
    runCost ops (unitCost S N) s c ≤ 2 * c.length := …

-- lean/ToySlotCompact/Stores.lean:345-346
theorem runCost_unitCost_family {St : Type} (S L : Nat) (ops : StoreOps St (L + 1) Nat) (s : St) :
    runCost ops (unitCost St (L + 1)) s (famScript S L) = 2 * S := …
```

Binder note: in `runCost_unitCost_le` the name `S` is the store representation type, introduced by `variable {S S₁ S₂ V : Type} {N : Nat}` at `Stores.lean:16` (quoted in the block above), and the bound is `2 * c.length` in the length of the command list `c`. In `runCost_unitCost_family` the store representation type is `St : Type`, `S : Nat` is the number of commands of `famScript S L` (and `L + 1` the number of slots), and the cost is exactly `2 * S`.

**Hypothesis ledger.** No hypotheses: the statements hold for all values of their parameters.

**Depth:** definitional.

**Non-vacuity witness:** No hypotheses (holds for every store implementation, store and script); the family run is an instance. Lean: `runCost_unitCost_family`.

**Positive control:** not applicable (not an impossibility result).

**Prior art:**

* No source establishes these toy counts; they are self-contained cost-model facts. For context (not a source for these counts): verified association-list and array-backed map implementations coexist behind one interface in the Isabelle Collections Framework (Lammich, Archive of Formal Proofs, 2009, https://www.isa-afp.org/entries/Collections.html; entry page read).

**Design question:** When is an array-backed indexed store a faithful replacement for an association-list store inside a certificate checker, and what does it buy in primitive operations?

**Non-claims:** listed under **Boundaries**, `unit-cost-checker-toy-cost-O-S`.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — a separate claim from the kernel-checked statements above. These are counts in a toy cost model; unit cost per get/put is an assumption (the usual model of an array indexed by slot number), not derived from `funOps`. They neither establish nor refute any running-time claim about a real checker (model–system relation: none proved).

## Boundaries

### Non-claims (per result)

What each result does not show. Every refutation stated here cites a kernel-checked theorem by name or is marked "(not proved here)".

#### `compact-bisim-no-clobber`

* The bisimulation is relative to CompactRel: it says nothing about initial store pairs that are not related. For a non-injective π, some original stores have no related compacted store at all unless π is injective on the slots live at entry (entry-adequacy-iff-injective-on-live).
* The interference conditions are stated relative to the given mask, not to path liveness, and they are a write-versus-live-after formulation. Pointwise disjoint live ranges (π injective on the live slots at every point) do not imply NoAssignClobber, because compact keeps writes to kept slots even where the written slot is dead (disjoint_live_ranges_not_noAssignClobber). No equivalence with the live-interval overlap tests of real allocators is claimed.
* Each counterexample shows that dropping that one hypothesis can break the conclusion in its witness class; it neither establishes nor refutes that the hypothesis is necessary outside that class. For instance, ReadsLive is not necessary in general: dropping every slot of x1 := x0; halt [] with the empty mask, which violates ReadsLive, still gives a lockstep bisimulation (pathLive_faint_operand).
* Observations are the debug events emitted by dbg and the output values emitted by halt outs (the values of the slots in outs, in order). The compacted halt emits the values of outs.filterMap π.get?, which drops unkept slots; the outputs agree because ReadsLive makes every output slot live, hence kept and related. The rest of the final store is constrained only through the relation, and no relation-free notion of observational equivalence is defined.
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.
* The compacted program keeps a nop at every erased instruction, so program points coincide; compaction that also removes instructions and renumbers program points is not covered.
* Neither establishes nor refutes any claim about rustc, LLVM, CompCert, CakeML or any verification framework; any connection is a separate derived modeling bridge, and no performance figure is claimed.

#### `compact-bisim-injective`

* Injectivity is sufficient, not necessary: compact-bisim-no-clobber covers non-injective sharings (nonvacuous_bisim_noClobber_sharing).
* Injectivity together with ReadsLive is not enough on its own: dropping closure under the backward transfer breaks the conclusion on a two-instruction program over 1 slot (cex_bisim_injective_transferClosed). With the path-liveness mask, both certificate halves hold automatically (pathLiveMask_cert).
* A certificate, even one accepted by checkLive and even L = pathLiveMask p with an injective π, says nothing about debug reads or slot-sharing interference: checkLive checks only ReadsLive and TransferClosed, not DbgReadsLive, NoAssignClobber or NoMarkerClobber, and on dbg x0; halt [] the compaction is not a lockstep bisimulation (checkLive_pathLiveMask_not_sufficient_with_dbg).
* Storage-marker resets are harmless here because markers are renamed through the same injective π; nothing is claimed for compactions that drop or move markers of kept slots.
* Observations are the debug events emitted by dbg and the output values emitted by halt outs (the values of the slots in outs, in order). The compacted halt emits the values of outs.filterMap π.get?, which drops unkept slots; the outputs agree because ReadsLive makes every output slot live, hence kept and related. The rest of the final store is constrained only through the relation, and no relation-free notion of observational equivalence is defined.
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.
* The compacted program keeps a nop at every erased instruction, so program points coincide; compaction that also removes instructions and renumbers program points is not covered.
* Neither establishes nor refutes any claim about rustc, LLVM, CompCert, CakeML or any verification framework; any connection is a separate derived modeling bridge, and no performance figure is claimed.

#### `compact-kept-bisim-injective`

* KeptRel relates only stores that agree on every kept slot, live or dead; it is stronger than CompactRel and relates fewer state pairs.
* Debug reads of kept slots at points where they are dead are allowed here, while under CompactRel the same compaction is not a lockstep bisimulation although the mask is a certificate (keptBisim_kept_dead_dbg); debug reads of dropped slots break both (cex_keptBisim_dbgReadsKept, cex_bisim_injective_dbgReadsLive).
* Injectivity is not necessary in general: on the write-free program nop; halt [x0, x1], merging both kept slots still gives a KeptRel lockstep bisimulation (keptBisim_noninjective_writeFree). Dropping injectivity breaks the conclusion when a write lands on a merged kept slot (cex_keptBisim_injective); slot sharing in the presence of writes is covered, under CompactRel, by compact-bisim-no-clobber.
* ReadsKept is a single-pass syntactic condition: a read whose value flows only into an assignment to a dropped slot still counts as a read. On x1 := x0; halt [] with nothing kept ReadsKept fails, yet dropping both slots gives a KeptRel lockstep bisimulation (pathLive_faint_operand), so ReadsKept is not necessary in general. The iterated removal of such assignments, as in rustc's SimplifyLocals, is not modeled.
* Observations are the debug events emitted by dbg and the output values emitted by halt outs (the values of the slots in outs, in order). The compacted halt emits the values of outs.filterMap π.get?, which drops unkept slots; the outputs agree because ReadsKept makes every output slot kept, hence related. The rest of the final store is constrained only through the relation, and no relation-free notion of observational equivalence is defined.
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.
* The compacted program keeps a nop at every erased instruction, so program points coincide; compaction that also removes instructions and renumbers program points is not covered.
* Neither establishes nor refutes any claim about rustc, LLVM, CompCert, CakeML or any verification framework; any connection is a separate derived modeling bridge, and no performance figure is claimed.

#### `entry-adequacy-iff-injective-on-live`

* Says nothing about executions; combine with a bisimulation result for program equivalence from related initial states.
* pushStore π pc σ is one witness; uniqueness of related compacted stores is not claimed, and the pull-back reads dropped slots as 0, so it is in general not the original store a compacted store was obtained from.
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.

#### `wp-transport-no-clobber`

* wp is total correctness (it requires the program to halt within some fuel); partial correctness and nontermination are not examined.
* Postconditions are evaluated on halting states, and debug events are ignored, which is why DbgReadsLive is not a hypothesis.
* The relation is CompactRel; agreement of wp on unrelated states is not claimed.
* exec p n and exec (compact p L π) n are related for the same fuel n because compact keeps a nop at every erased instruction; for a pass that also removes instructions the required fuel would differ (not proved here).
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.
* The compacted program keeps a nop at every erased instruction, so program points coincide; compaction that also removes instructions and renumbers program points is not covered.
* Neither establishes nor refutes any claim about rustc, LLVM, CompCert, CakeML or any verification framework; any connection is a separate derived modeling bridge, and no performance figure is claimed.

#### `transportable-postconditions-characterization`

* The class is relative to the mask; with a larger mask more postconditions qualify, but the transport theorems still assume that the mask is a certificate.
* Counterparts other than pullPost π Q are not characterized.
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.

#### `vc-transfer-original-to-compacted`

* Without InjOnLiveAt p L π 0 and DependsOnlyOnEntryLive p L Pre, the transferred implication can hold vacuously, because the compacted precondition is restricted to pulled-back stores, Pre ∘ pullStore π: if Pre requires a dropped slot to be nonzero (vc_forward_vacuous_dropped) or two merged entry-live slots to differ (vc_forward_vacuous_merged), then Pre (pullStore π σ') is false for every σ' and the transferred condition holds vacuously.
* The covered transports are Pre ∘ pullStore π and pullPost π Q (pullStore reads dropped slots as 0); other ways of transporting pre- and postconditions are not examined.
* The statement concerns total correctness from the entry point (pc 0); other entry points and partial correctness are not examined.
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.
* The compacted program keeps a nop at every erased instruction, so program points coincide; compaction that also removes instructions and renumbers program points is not covered.
* Neither establishes nor refutes any claim about rustc, LLVM, CompCert, CakeML or any verification framework; any connection is a separate derived modeling bridge, and no performance figure is claimed.

#### `vc-transfer-compacted-to-original`

* InjOnLiveAt p L π 0 is not necessary in general: with the postcondition True the conclusion holds on pE although πEm merges both entry-live slots (vc_backward_without_inj0_postTrue); its tightness is witnessed in the class of cex_vcBwd_injOnLiveAt (a one-instruction program over 3 slots), not in general.
* The witness compacted entry store is pushStore π 0 σ; other choices are not discussed.
* vc_transfer_of_noClobber packages both directions as an equivalence under the union of the hypotheses; the forward direction alone needs fewer (vc-transfer-original-to-compacted).
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.
* The compacted program keeps a nop at every erased instruction, so program points coincide; compaction that also removes instructions and renumbers program points is not covered.
* Neither establishes nor refutes any claim about rustc, LLVM, CompCert, CakeML or any verification framework; any connection is a separate derived modeling bridge, and no performance figure is claimed.

#### `non-live-read-breaks-compaction`

* Shows that the gen half of the certificate cannot be dropped in this instance; it does not quantify how often such masks arise, and ReadsLive is not necessary in general (pathLive_faint_operand).
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.

#### `non-transfer-closed-mask-breaks-compaction`

* Injective compactions do not need transfer closure for the stronger kept-slot relation (compact-kept-bisim-injective, witness nonvacuous_keptBisim_not_transferClosed on this same program); the failure is specific to the live-slot relation CompactRel.
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.

#### `merging-simultaneously-live-slots-breaks-compaction`

* Non-injective maps are not unsound in general: on pC a merging map satisfies every hypothesis of compact-bisim-no-clobber, so that compaction is a lockstep bisimulation (nonvacuous_bisim_noClobber_sharing with compact_lockstepBisim_of_noClobber), and on write-free programs even merging simultaneously kept slots is a KeptRel bisimulation (keptBisim_noninjective_writeFree).
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.

#### `marker-reset-breaks-slot-sharing`

* Resets do not break injective compactions: compact-bisim-injective allows resetting markers (nonvacuous_bisim_injective_straightLine).
* Both markers reset the slot to 0 here; in LLVM, lifetime.end instead makes later access undefined behaviour (StackColoring.cpp rule L6), which is not modeled.
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.

#### `dead-debug-read-breaks-lockstep-bisimulation`

* Debug reads do not affect weakest preconditions: wp-transport-no-clobber has no debug hypothesis, and on this instance the compaction is a silent bisimulation (events ignored) though not a lockstep one (pD_silent_not_lockstep).
* The checker checkLive accepts this mask, which is the path-liveness mask, so checked liveness does not exclude this failure (checkLive_pathLiveMask_not_sufficient_with_dbg).
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.

#### `liveness-certificate-overapproximates`

* PathLive is syntactic path liveness: it follows every syntactic successor, including branch targets that are never taken (pathLive_infeasible_branch), and it counts the operand of an assignment to a dead slot as a use (pathLive_faint_operand). It is neither strong (non-faint) liveness nor dynamic liveness; semantic (observational) liveness is not defined or compared.
* Masks are over-approximations, not exact liveness: they can be arbitrarily larger than path liveness; the all-live mask is accepted on pB although slot x2 is never used (checkLive_accepts_overapprox). A larger mask keeps more slots (fewer writes become nop in compact) and makes NoAssignClobber, NoMarkerClobber and InjOnLiveAt harder to satisfy (immediate from the definitions; not stated as a theorem).
* A certificate, even one accepted by checkLive and even L = pathLiveMask p with an injective π, says nothing about debug reads or slot-sharing interference: checkLive checks only ReadsLive and TransferClosed, not DbgReadsLive, NoAssignClobber or NoMarkerClobber, and on dbg x0; halt [] the compaction is not a lockstep bisimulation (checkLive_pathLiveMask_not_sufficient_with_dbg).
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.

#### `liveness-checker-characterization-and-soundness`

* Acceptance certifies over-approximation, not precision: the all-live mask is accepted (checkLive_accepts_overapprox), so the checker certifies neither precision nor minimality.
* A certificate, even one accepted by checkLive and even L = pathLiveMask p with an injective π, says nothing about debug reads or slot-sharing interference: checkLive checks only ReadsLive and TransferClosed, not DbgReadsLive, NoAssignClobber or NoMarkerClobber, and on dbg x0; halt [] the compaction is not a lockstep bisimulation (checkLive_pathLiveMask_not_sufficient_with_dbg).
* PathLive is syntactic path liveness: it follows every syntactic successor, including branch targets that are never taken (pathLive_infeasible_branch), and it counts the operand of an assignment to a dead slot as a use (pathLive_faint_operand). It is neither strong (non-faint) liveness nor dynamic liveness; semantic (observational) liveness is not defined or compared.
* The checker runs over a finite program and finitely many slots; its running time is not analysed.
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.

#### `liveness-checker-rejects-omitted-path-live-slot`

* This is a sufficient condition for rejection; the exact acceptance condition is liveness-checker-characterization-and-soundness.
* Omission is measured against syntactic path liveness; slots that are live in a dynamic or semantic sense but are not path-live are not examined.
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.

#### `path-liveness-least-certificate`

* pathLiveMask is defined with classical choice and is not computed; no iterative analysis is implemented or proved to converge.
* PathLive is syntactic path liveness: it follows every syntactic successor, including branch targets that are never taken (pathLive_infeasible_branch), and it counts the operand of an assignment to a dead slot as a use (pathLive_faint_operand). It is neither strong (non-faint) liveness nor dynamic liveness; semantic (observational) liveness is not defined or compared.
* A certificate, even one accepted by checkLive and even L = pathLiveMask p with an injective π, says nothing about debug reads or slot-sharing interference: checkLive checks only ReadsLive and TransferClosed, not DbgReadsLive, NoAssignClobber or NoMarkerClobber, and on dbg x0; halt [] the compaction is not a lockstep bisimulation (checkLive_pathLiveMask_not_sufficient_with_dbg).
* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about real compilers or verifiers. The toy has no memory, pointers or address-taken slots, calls, exceptions, or undefined behaviour; values are natural numbers; storage markers reset the slot to 0 instead of making later access undefined.

#### `store-laws-on-common-domain`

* The indexed store here is a mathematical function, not a machine array; array bounds, sharing and destructive update are not modeled.
* Representation-level laws can distinguish implementations that get cannot: the shadowing association list consPutOps (put prepends an entry) satisfies GetPutSame and GetPutOther (consPutOps_getPutSame, consPutOps_getPutOther) but, with at least one slot, not PutPut (consPutOps_not_putPut).

#### `certificate-checker-representation-independence`

* runCheck is a standalone straight-line replay checker for incr/check command lists over StoreOps; it does not execute Prog N and is not the liveness checker checkLive.
* Representation independence holds here because runCheck touches the store only through get and put. A client that compares stores structurally (for example to detect a fixpoint) can distinguish implementations satisfying GetPutSame and GetPutOther: consPutOps satisfies both laws, yet putting twice and putting once give structurally different lists with the same view (consPutOps_getPutSame, consPutOps_getPutOther, consPutOps_not_putPut).
* Proved for this one command language and checker by induction; it is not a parametricity (free) theorem, and no parametricity principle is used.
* Equal verdicts, not equal costs (see the cost results).
* PutGetId and PutPut are not needed and are not hypotheses.

#### `alist-checker-toy-cost-theta-SL`

* Toy cost model: one unit per scanned cell; allocation, caching, hashing, kernel reduction cost and real hardware are not modeled.
* l.length counts entries, not distinct keys: a complete list may repeat keys and be longer than the number of slots (complete_with_repeated_keys).
* The lower bound is exhibited on one family (famAlist L with famScript S L); it is not a worst-case lower bound over all inputs or all association-list implementations.
* runCost charges nothing for building the initial store. A dense indexed store over N slots needs work proportional to N to allocate or initialize, and copies proportional to N per update if updated non-destructively, whereas an association list started from [] grows only with the slots a script touches; neither effect is modeled (not proved here).
* No figure about any real verification framework or proof checker is implied.

#### `unit-cost-checker-toy-cost-O-S`

* Unit cost per access is an assumption of the toy model, not a property of funOps or of any real array implementation. In Lean, funOps.put builds a nested conditional function, and evaluating a lookup after S updates by reduction inspects up to S conditionals (not proved here); unitCost does not measure that.
* runCost charges nothing for building the initial store; allocating or initializing a dense N-slot array costs work proportional to N, which is one reason to shrink N by dead-slot compaction before switching to an indexed store (not proved here).
* No claim about speedups of any real verification or kernel-checking pipeline.

### Hypotheses known not to be necessary in general

Each item is backed by kernel-checked theorems exhibiting an instance where the hypothesis fails and the conclusion still holds; the corresponding ledger entries remain `tight` in their own witness classes.

* `ReadsLive` (bisimulation theorems) and `ReadsKept` (`compact_keptRel_lockstepBisim_of_injective`): `pathLive_faint_operand` (on `x1 := x0; halt []` with the empty mask, both fail and the compaction is still a lockstep bisimulation for `CompactRel` and for `KeptRel`).
* Injectivity of `π` for the `CompactRel` bisimulation: `nonvacuous_bisim_noClobber_sharing` proves all hypotheses of `compact_lockstepBisim_of_noClobber` together with `¬ Function.Injective πCm` on `pC`, so that theorem gives the conclusion for a non-injective map.
* Injectivity of `π` for the `KeptRel` bisimulation: `keptBisim_noninjective_writeFree` (write-free program `nop; halt [x0, x1]`, both kept slots merged).
* `InjOnLiveAt p L π 0` in `vc_backward_of_noClobber`: `vc_backward_without_inj0_postTrue` (postcondition `True` on `pE`).

### Related negative results (kernel-checked)

* `bisim_observes_halt_outputs`: a compaction that erases a `halt` output is not a lockstep bisimulation (halt outputs are observed).
* `checkLive_pathLiveMask_not_sufficient_with_dbg`: the checker accepts the path-liveness mask of `pD` and `πD` is injective, yet the compaction is not a lockstep bisimulation (`checkLive` does not check `DbgReadsLive`).
* `keptBisim_kept_dead_dbg`: on `pKD` the mask is a certificate, the `KeptRel` compaction is a lockstep bisimulation, and the `CompactRel` one is not (a debug read of a kept but dead slot).
* `disjoint_live_ranges_not_noAssignClobber`: `π` injective on the live slots at every point does not imply `NoAssignClobber`, and on that instance (`pDisj`) the `CompactRel` compaction is not a lockstep bisimulation.
* `vc_forward_vacuous_dropped`, `vc_forward_vacuous_merged`: the forward verification-condition transfer can hold vacuously (the transported precondition is unsatisfiable although `Pre` is satisfiable).
* `pD_silent_not_lockstep`: on `pD` the compaction is a silent bisimulation but not a lockstep bisimulation.
* `pathLive_infeasible_branch`: path liveness follows a branch successor that no run takes.

### Escape hatches

This package contains no impossibility result, so there is no hypothesis whose removal defeats an impossibility. The positive theorems are sufficient conditions; the five counterexample cards show, for one concrete instance each, that dropping one hypothesis can make the conclusion fail, and the list above shows which hypotheses can fail while the conclusion still holds.

### Tightness status `unknown`

None. Every hypothesis of every result is recorded as `tight`, with a kernel-checked counterexample and a witness class.

### Disproved or omitted candidate statements

None. All 21 results are proved exactly as stated; their statement and definition-closure hashes are recorded under **Evidence**.

### Not examined

* Semantic (observational) liveness, and its exact relation to path liveness; the difference is illustrated by `pathLive_faint_operand` and `pathLive_infeasible_branch`, but no semantic notion is defined.
* A computed liveness analysis (fixed-point iteration) with a termination or convergence proof; masks here are claimed and checked.
* A parametricity (relational) formulation of representation independence; `runCheck_eq_of_getPut` is a direct induction for one command language.
* Worst-case lower bounds over all inputs or all association-list implementations.
* Passes that delete `nop`s and renumber program points; memory, pointers, address-taken slots, calls, exceptions and undefined behaviour.

### Attractive stronger conclusions not established

* That rustc's `SimplifyLocals`, LLVM's `StackColoring` or `StackSlotColoring`, CompCert's `Stacking`, or any register allocator is correct: these are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about those systems.
* That `NoAssignClobber`/`NoMarkerClobber` are equivalent to live-interval non-overlap: not claimed; `disjoint_live_ranges_not_noAssignClobber` shows that pointwise disjointness of live sets does not imply `NoAssignClobber` in the toy.
* That any hypothesis is necessary in general: the ledgers record tightness within stated witness classes, and four hypotheses are shown above not to be necessary in general.
* That `checkLive` acceptance makes a compaction sound: it checks `ReadsLive` and `TransferClosed` but not `DbgReadsLive`, `NoAssignClobber` or `NoMarkerClobber` (`checkLive_pathLiveMask_not_sufficient_with_dbg`).
* Real-time or memory performance of any store implementation: the cost cards count operations in a toy cost model.

## Evidence

### Toolchain and build

* Lean `leanprover/lean4` `v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`; no Mathlib; no Lake dependencies.
* Observed 2026-11-21: `lake build` of `lean/` succeeds with no errors, warnings or `sorry`; the sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern` or `unsafe`.
* Axiom audit (Lean `collectAxioms` over all 824 declarations of the library, recorded in `audit/axioms.json`): 311 declarations use {no axioms}; 330 declarations use {propext}; 134 declarations use {Quot.sound, propext}; 49 declarations use {Classical.choice, Quot.sound, propext}.

### Kernel-check record per referenced declaration

For each Lean name referenced by `results.json` (the statement of a card, a non-vacuity witness, a tightness counterexample, or a lemma cited by name in a card's text or non-claims, listed under that card's `lean_names` and marked "cited lemma" below): its axioms, the SHA-256 of the Lean `repr` of its type (statement hash), and the SHA-256 of its definition closure: the newline-joined, sorted list of `name : repr(type)` (followed by ` := repr(value)` for non-theorems) over every library constant reachable from the statement, with theorem bodies excluded (closure hash; the number of constants in parentheses). The same values are in `audit/statements.json`; `support/revalidate.py` recomputes them. All names are in namespace `Toy.SlotCompact`.

| name | used by | axioms | statement sha256 | closure sha256 (size) |
| --- | --- | --- | --- | --- |
| `alistOps_empty_not_putGetId` | store-laws-on-common-domain (counterexample); store-laws-on-common-domain (statement) | propext | `bd198f5fffeb5ab55607c90040dcc2234dc8497ae3be657e3d51b78a207df0ca` | `5c4b990b3f8b15311155721a8909be16feddac2be07569d078e9a991ecedf9b2` (12) |
| `alistOps_laws` | store-laws-on-common-domain (statement) | propext | `89eade9a9f26839d749592de4a0a656b2292139e6dd54105cb49cc0e0db9ff35` | `2ad27f4f40c6998b3987c8ee519f8ad2971884b73b4dcc2bd88cbaeef10b84b7` (15) |
| `alistOps_zero_putGetId` | store-laws-on-common-domain (statement) | none | `29c9cdbdff018206163fabdcda69f78f50fd505c6f5f1d128aa6a932096806d7` | `c301f32ffcda9809c83beff50aed6459315c1089ccba2878da1ab1141ccfc87d` (12) |
| `bisim_observes_halt_outputs` | compact-bisim-no-clobber (cited lemma) | propext | `df48063504109ac2feecc6254a80262c1f2453b1a181887826e9c804dca6c09b` | `15759e8a36b41e0c20a142e7eb8b98b496b1ff8ae7e71dbd71f994f5d05ef76f` (76) |
| `cex_alistCost_complete` | alist-checker-toy-cost-theta-SL (counterexample) | propext | `652d2af77ecce6a44babd9c80cbdd7ca3024d082f1178429d55a4be27bb65847` | `725144285303d0176455d2ff7cb96b28436d1f97c1fba6e4a59ff2cdd98feda8` (28) |
| `cex_bisim_injective_dbgReadsLive` | compact-bisim-injective (counterexample); dead-debug-read-breaks-lockstep-bisimulation (statement) | Classical.choice, Quot.sound, propext | `aa2cf9f649e509e7b029f101029320fd2a2eb6f8af9f80aaff381e4fa7fb319d` | `c0574e0b115cb235d0764b45f88abbc41a2ead9204a2b934a94ccf8de8964adb` (82) |
| `cex_bisim_injective_injective` | compact-bisim-injective (counterexample); merging-simultaneously-live-slots-breaks-compaction (statement) | Quot.sound, propext | `adcd35f2705d02ff477e3f10926ebff6fae5eee5e85e8c427b36d68a71801e9a` | `27dba0f285731d72f9424f7bc68f6dab33e6eafca4db30920bdad4dfa736be09` (83) |
| `cex_bisim_injective_readsLive` | compact-bisim-injective (counterexample); non-live-read-breaks-compaction (statement) | Classical.choice, Quot.sound, propext | `6b84ea68fb46cd63f45f0c09e56b493d1e87f1131b67160ea2894dcc8b996473` | `2ceb3081b1ad50a67c86f6ef3e1e425fa8c55f1f124103450896c3b5ebcb3912` (83) |
| `cex_bisim_injective_transferClosed` | compact-bisim-injective (counterexample); non-transfer-closed-mask-breaks-compaction (statement) | Classical.choice, Quot.sound, propext | `35131eeda5a0c67312f0dc21c6c9f8d965259da2c2ea1819723c4349e2d4ce02` | `57dcc7035ab7b9de4a26235202c7c9a29635c11e94b17429199c55a001a13dff` (82) |
| `cex_bisim_noClobber_dbgReadsLive` | compact-bisim-no-clobber (counterexample); dead-debug-read-breaks-lockstep-bisimulation (statement) | Quot.sound, propext | `91bad413fcb7ab292717d8828a9c59935c88854d3245b5755be9979f2c41087d` | `4bcc07add043e6c790de1af3ae51d798beb42b54045dbb07d81d128917eda261` (84) |
| `cex_bisim_noClobber_noAssignClobber` | compact-bisim-no-clobber (counterexample); merging-simultaneously-live-slots-breaks-compaction (statement) | Quot.sound, propext | `c659806995232adbfd3acc2cf889b9ececbe543c3e7ba7221156f0a64ff50d46` | `103af85cd921ce65097426d596dd299b24cfb3e100a535ac24f1495f940d0582` (85) |
| `cex_bisim_noClobber_noMarkerClobber` | compact-bisim-no-clobber (counterexample); marker-reset-breaks-slot-sharing (statement) | Quot.sound, propext | `f532dd64ac0c891f143702967e064fffc1c42fee5c7b07c5baf864cf35e3e98e` | `5b7d930a87c0dfbb08610b0c6ead8a0844e579dc2e21985d60a01d7383f728fc` (85) |
| `cex_bisim_noClobber_readsLive` | compact-bisim-no-clobber (counterexample); non-live-read-breaks-compaction (statement) | Quot.sound, propext | `5e9817be4a4c84341df844b61fcfb8283e13922d4635b86ba2d371f9a8f28352` | `dd259b0ee1a504794a116d4b0556a22e8f4e59810a2ef2a2a4d7aed075969b09` (85) |
| `cex_bisim_noClobber_transferClosed` | compact-bisim-no-clobber (counterexample); non-transfer-closed-mask-breaks-compaction (statement) | Quot.sound, propext | `6aec427dd4208ebf9d47ca26341fc279f4a297924168e0feb5870f388465772e` | `c58b9611aceeed28e017ac5c9dce3e504606aff8a611928ed42472336dda8dc6` (84) |
| `cex_cert_pathLive` | liveness-certificate-overapproximates (counterexample) | Quot.sound, propext | `08d2662ecfb38cfb74b94f8b8cfdab76becb00c221710ebb210a8642e01b49e1` | `b296be65bda12a0546f5a61b20cdda338dfeb66e023df2e7b0e998d18ab5e519` (43) |
| `cex_cert_readsLive` | liveness-certificate-overapproximates (counterexample) | Quot.sound, propext | `9e60b38a799a4f3ab5b9994addf562d82f51670c98196a46e965ae551bfb261e` | `7d5b2d2b9092cb6960546cadc2c1c1d626f1078493c7ad4599675774a1317200` (43) |
| `cex_cert_transferClosed` | liveness-certificate-overapproximates (counterexample) | Quot.sound, propext | `9b763ccb67c91638f70ffd753948f05957ebce21c3931b8c59ca87521cb155db` | `3549b67860b482373976748e1749d4146a7ee8afeadf08f2234ea480c49813c6` (43) |
| `cex_checkLive_sound_accepted` | liveness-checker-characterization-and-soundness (counterexample) | propext | `98d4cd943a173aa72e22aa3373f50c9a451573ecfb58ff4ce430a52e021a7705` | `93f83282d2f80eb67965d141d95778186df68926e1df965b7430c3fc4314f58c` (45) |
| `cex_checkLive_sound_pathLive` | liveness-checker-characterization-and-soundness (counterexample) | Quot.sound, propext | `3b917b8916fcf51b977e3c821995134a5bcd6e515e282e06aadc940e668816df` | `65bc143e0e86aba4e587be509dc986462e4f51352dfe06a114b9865e5bf1c6ad` (45) |
| `cex_keptBisim_dbgReadsKept` | compact-kept-bisim-injective (counterexample); dead-debug-read-breaks-lockstep-bisimulation (statement) | Classical.choice, Quot.sound, propext | `f905260328ddd8128803f823ec28e6415e41201fd05d1e98ceb04a259f150fc8` | `36d0c90ef38ac53bdfff82d24c065e15b94675f0701ca19c5689dd268cd8f8a5` (75) |
| `cex_keptBisim_injective` | compact-kept-bisim-injective (counterexample); merging-simultaneously-live-slots-breaks-compaction (statement) | Quot.sound, propext | `ac6f0f264ae266003397471dfe2986cc1eecfbbbf1d8b7ce2faf6f85d4be2332` | `b2252a3604e65365996b313d614f727eebf1c5be0dd989a7ed1277f56c67bfb6` (76) |
| `cex_keptBisim_readsKept` | compact-kept-bisim-injective (counterexample) | Classical.choice, Quot.sound, propext | `47a815006137cc92443130945601c9dbb71ba697e600d2c67312872c23cbf24f` | `a0ab0757e868b6c442a515374971fe2c3b6f5115310f223df1ceaa0fdbbe0c43` (76) |
| `cex_missing_requires_omission` | liveness-checker-rejects-omitted-path-live-slot (counterexample) | Quot.sound, propext | `619660f998da2e080805915c6c7c2433c7d75b14a6850d007828b28eab792807` | `65bc143e0e86aba4e587be509dc986462e4f51352dfe06a114b9865e5bf1c6ad` (45) |
| `cex_missing_requires_pathLive` | liveness-checker-rejects-omitted-path-live-slot (counterexample) | Quot.sound, propext | `c1447ea715d0352680fbfa51d4ed4fddd94c608c59429973aedcb82eb4fc990e` | `65bc143e0e86aba4e587be509dc986462e4f51352dfe06a114b9865e5bf1c6ad` (45) |
| `cex_postClass_injAtHalts` | transportable-postconditions-characterization (counterexample) | propext | `8110eed7457825e1e5cfc7e8b618efd8ebc95941cf397808b02c3f58fc436316` | `9f28b7446a924a4ce507d60361664da8679bbbc05e041382eab184c27c619e7b` (32) |
| `cex_postCorr_pullPost_dependsOnlyOnLive` | transportable-postconditions-characterization (counterexample) | propext | `5f34ea23a4b1aa0360baf09c79d854ad5feec352718499c5d940405dfd853b8f` | `49c6f005bf74f965b27aa8ecf81db8dcf8eedb249bc69d40e3b067f37654a13f` (34) |
| `cex_pushStore_injOnLiveAt` | entry-adequacy-iff-injective-on-live (counterexample) | propext | `001062c0d2ecc78feec4850560f70f21b79a50a8618ea0c0f8a21981ff778531` | `4e127ab59f3e806c4950f32786fc0bdd4397baa189aac2b666cf4ef79758fcd0` (31) |
| `cex_repInd_funOps_alistOps_view` | certificate-checker-representation-independence (counterexample) | propext | `0a8746bbb88ae1c6400950b33e17009789649687cc7b0b5aaab68c043b8c2f7c` | `26ccbd615d0249b0065eb3969b5a87288d1bd267e80be07ed915301bd600262f` (20) |
| `cex_repInd_h1o` | certificate-checker-representation-independence (counterexample) | Quot.sound, propext | `cebd4f070131f0ddf6bf0b62cf5b49ed35835ed849bd3ab4508dd44cb183cd47` | `ca3647e0acfed065a31ef3dd5e31f7c5176a087d4d2b05afc1d7eed5f2a6b7c0` (16) |
| `cex_repInd_h1s` | certificate-checker-representation-independence (counterexample) | Quot.sound, propext | `aaf9743a2d6840a30dcc36ac4d878d8ce6ac3dc3baf0635e082da6f2bdef3e20` | `d53bf0af808caff531ff86a1e382656e3506597c3e7d0f1999343d485590fc59` (16) |
| `cex_repInd_h2o` | certificate-checker-representation-independence (counterexample) | Quot.sound, propext | `3b22dfd7e6115cf9970fe3866b277d81429fb1db5ee8640a7afb4abeeeb2374f` | `ca3647e0acfed065a31ef3dd5e31f7c5176a087d4d2b05afc1d7eed5f2a6b7c0` (16) |
| `cex_repInd_h2s` | certificate-checker-representation-independence (counterexample) | Quot.sound, propext | `cebf6f4547fbb312304086f07578e69b2298b5fd16a21f71db065be7716bb754` | `d53bf0af808caff531ff86a1e382656e3506597c3e7d0f1999343d485590fc59` (16) |
| `cex_repInd_view` | certificate-checker-representation-independence (counterexample) | Quot.sound, propext | `0ff15109bf4c192ef526d2d77cbdb49725aaca78b676195cfe592e923ff20af1` | `5e386598ec6b1ad7d9fc35e6a679014560f68888e3e058f22117611863b046b3` (15) |
| `cex_vcBwd_injOnLiveAt` | vc-transfer-compacted-to-original (counterexample) | Quot.sound, propext | `31c59ff127dc6a165f7b018b20616c6cb82ee97b521250205c470e80e8f2e1bb` | `4be617f683c822b27c247fbbb07516670ec1d4a16c1cae4c2e9236a0420b6906` (89) |
| `cex_vcBwd_noAssignClobber` | vc-transfer-compacted-to-original (counterexample) | Classical.choice, Quot.sound, propext | `25fdf8377e2654115620c6ae3cf98c38881b1a96e8ab6f0af44a526904137eb8` | `09b676f978c53c1f7f712461f3f95bfda1a6d9c7a2e5c8b2e9add0e2831a1e48` (91) |
| `cex_vcBwd_noMarkerClobber` | vc-transfer-compacted-to-original (counterexample) | Classical.choice, Quot.sound, propext | `a4bb8d04600c4ad813567e4cd19dd5eb7d6c7875b414c950d42666cc04a60952` | `5900883a1970a6ab70f8ac32256401be0d8370e346b3b7d30f36ca1a73b9c7e5` (91) |
| `cex_vcBwd_post` | vc-transfer-compacted-to-original (counterexample) | Classical.choice, Quot.sound, propext | `d421f858e34291483ad35b62ef3e22b614611214e52e7bdb3ad0d1585ba8afb8` | `3aba81c18ea7c642512a01002de34df7dbc2129f982ed94b22df0d4f2eaad19e` (88) |
| `cex_vcBwd_pre` | vc-transfer-compacted-to-original (counterexample) | Classical.choice, Quot.sound, propext | `0d2559f9861a66009588d5eda5ca0f9a635cedbbc982057e943bfbfd75822dd9` | `cd559c45b7f92bed9bf44a5702e89fdc5a78c09163b6ba3b81f18c2503ca9955` (88) |
| `cex_vcBwd_readsLive` | vc-transfer-compacted-to-original (counterexample) | Classical.choice, Quot.sound, propext | `d1aa049f9953b731dc653854b258761ba16846ebf209b7180aa814513569f1e1` | `f529c0012d74e2252294159f73664fee6d17235133108e482171cfbbcdfde68b` (90) |
| `cex_vcBwd_transferClosed` | vc-transfer-compacted-to-original (counterexample) | Classical.choice, Quot.sound, propext | `69971892b543d9f384f1908b5009a034666b4ee32cc9a5954a863d64075712d4` | `6273073a99f4a0d4cfc409aee2f63c6bbca066086e94d3c41b541cca1b1c7207` (90) |
| `cex_vcFwd_noAssignClobber` | vc-transfer-original-to-compacted (counterexample) | Quot.sound, propext | `47fde973b77c3462ebf8e14235d0276764c1e5e1bd81347b1fd14df4900ee4e6` | `90b510c1e17846eb0c85d9551078832c525f6cb85699da323442ebde66b02efd` (88) |
| `cex_vcFwd_noMarkerClobber` | vc-transfer-original-to-compacted (counterexample) | Quot.sound, propext | `52abb920c66e232dccffadb8cc55d8163171634d7adde66090424365c9324ed2` | `e6991ef2dde59503e37eecc5ce0a8ee011e390444b0bfed227e9173ce1060778` (88) |
| `cex_vcFwd_post` | vc-transfer-original-to-compacted (counterexample) | Quot.sound, propext | `7393b1ab58c8811e35ad6e0ad4292c61a338963ef5bd08f72cd13e18603b9429` | `59a581770e2f3a031a8456a8a1561adab7f70e36554c7b1a25c0a2836bfd016c` (86) |
| `cex_vcFwd_readsLive` | vc-transfer-original-to-compacted (counterexample) | Quot.sound, propext | `3c215b30b5c08481088e815843dc81d477cbd78da04a7a04882d7e523038f389` | `aca18c869e0097820d6f6f0ff55e9f9af812fcdd165960a5449a7298e2580e55` (89) |
| `cex_vcFwd_transferClosed` | vc-transfer-original-to-compacted (counterexample) | Quot.sound, propext | `59a38b2c0360b245248d6c52032b9465dfa8c15fe8b2efe6cf7d57a4b423c729` | `26712cecfd53641389d363597329593382a82c6a21a11a4e38f806427b30f2c3` (89) |
| `cex_wp_noAssignClobber` | merging-simultaneously-live-slots-breaks-compaction (statement); wp-transport-no-clobber (counterexample) | Quot.sound, propext | `a0f780bfaac4d62040ff6b2f9dc7f14311408927b0bc0a2a11378cef3b569052` | `3404eeb28c4b49c2f9085f63f49e5577d679bc08ef5509d8c23d533ba97b814e` (88) |
| `cex_wp_noMarkerClobber` | marker-reset-breaks-slot-sharing (statement); wp-transport-no-clobber (counterexample) | Quot.sound, propext | `c2996a8cace6a0bbc7a8a438e7ce1df2e27fddcca4331ab9f9cea9e661a169de` | `e10bf0d5319c142825fe8d4f3843e94d38448db8680c607f28c16f4b3121318f` (88) |
| `cex_wp_postCorr` | wp-transport-no-clobber (counterexample) | Quot.sound, propext | `c8159bab252f10286f632c2f3b269bf72f449885fdc1c347b39eca249b937f8e` | `2bb2554fc67d88d5970832c5aebc5533881481c796abd331692fba357383300e` (85) |
| `cex_wp_readsLive` | non-live-read-breaks-compaction (statement); wp-transport-no-clobber (counterexample) | Quot.sound, propext | `dafaa5072b5efdc024dfd669ddd4cd6ffb3c6f8c72a367e84fc12c1bad734ec8` | `c0610b6e2a99f25707deaebe74352b2e8274dabfbb61fb6ccff1ea80ce0bd290` (88) |
| `cex_wp_transferClosed` | non-transfer-closed-mask-breaks-compaction (statement); wp-transport-no-clobber (counterexample) | Quot.sound, propext | `d13ce351107dc31d141b1eabeea97470891ec7532a8c8ea95d16ed6369b3d5e8` | `b6e58c446be2e332cd6acd360dde0107fec28311097823b6cc089611da9f3357` (87) |
| `checkLive_accepts_overapprox` | liveness-certificate-overapproximates (cited lemma); liveness-checker-characterization-and-soundness (cited lemma) | Quot.sound, propext | `32d7c8a33ce15d65114b22618c88f8f12493901c041e98d040cc8eef42299702` | `b02795c47cab542e280f9725ee0436f73bcbd47fe1e8430285302f2f54cfe498` (44) |
| `checkLive_both_verdicts` | liveness-checker-characterization-and-soundness (non-vacuity) | propext | `d3a1c01ecb13315f47289df8e4576c6e2e7324a71abd9c6a775fa327cfe2d394` | `a6c29bef138b99fa670797eadaa5a6b4c4d51428d70406aab1cbc131e99a1864` (45) |
| `checkLive_eq_false_of_missing` | liveness-checker-rejects-omitted-path-live-slot (statement) | Quot.sound, propext | `f9d1acde533a4a5ffb2c6de3db230e3820060645d875325368f3fe99552aeee1` | `dcda69f10ff938c57136b490ac22ca673d5c5ef07695680b067c4ee488cadf78` (42) |
| `checkLive_eq_true_iff` | liveness-checker-characterization-and-soundness (statement) | Quot.sound, propext | `142cd9bff7b6970a03e1a63b808d19460ebb8c9a7cc320c84376298842e9097f` | `b69582b3d66328066298da170e151b3e7a1f7d67585c0c2c80e2ea754467d7a5` (41) |
| `checkLive_pathLiveMask` | path-liveness-least-certificate (statement) | Classical.choice, Quot.sound, propext | `a0189e00f7566d02a65c28018669fa6c1d08875c195b8b5cbed18415f2cb60b8` | `add9282e5d663fcdde7bbf15129ed0be53cd0d7ea12a7d600e159497c12d11a8` (43) |
| `checkLive_pathLiveMask_not_sufficient_with_dbg` | compact-bisim-injective (cited lemma); dead-debug-read-breaks-lockstep-bisimulation (cited lemma); liveness-certificate-overapproximates (cited lemma); liveness-checker-characterization-and-soundness (cited lemma); path-liveness-least-certificate (cited lemma) | Classical.choice, Quot.sound, propext | `d89cdadb85b599278a698fa5be35055e5683c0209bf81d431d2a0ccf1f35cc4c` | `4cb353e236c6be23173b18317a8d35f59ecda35b44d16cf3b1514dfd8762df77` (87) |
| `checkLive_rejects_underapprox` | liveness-checker-rejects-omitted-path-live-slot (non-vacuity) | propext | `cfc8f25429e17f33f375238f03a4e672ef952f6e0d0ab4dddf4777870ff6343d` | `e04edabce260c284384b10762822b3d32c18738325950910c64eb4b947291b48` (45) |
| `checkLive_sound` | liveness-checker-characterization-and-soundness (statement) | Quot.sound, propext | `25a2d6c01512d3e774172edb8f9f9a86330ccd9a163890f73d9b76dbd119aa91` | `dcda69f10ff938c57136b490ac22ca673d5c5ef07695680b067c4ee488cadf78` (42) |
| `compactRel_pullStore` | entry-adequacy-iff-injective-on-live (statement) | propext | `5e8d9db2d22a5e78ab140e331a3d7c95732565831d8fb8a248cb7207fd9bbf74` | `fbb52db81bd47a16f529e7ecbae212342b5b2e1b8cf5bff2f8304e4a70046f6d` (25) |
| `compactRel_pushStore` | entry-adequacy-iff-injective-on-live (statement) | Quot.sound, propext | `371b6f1929db28464f6bd0764bd35b4f005e2089d1e2a3b7daeeae60c02dd325` | `0c455564ecb0e4b13f0e49961b44ba570041658947fea70e41314ad02a1c9730` (26) |
| `compact_keptRel_lockstepBisim_of_injective` | compact-kept-bisim-injective (statement) | propext | `3dd92bfd433f2a16bd01b7e0888b18bf72c84b57ad8e4cd1a6cf888a340ce302` | `a3868f25129eb8b9d81677be7002bb943914a41bdefd6e84f60be4ef17c353a9` (71) |
| `compact_lockstepBisim_of_injective` | compact-bisim-injective (statement) | Quot.sound, propext | `a8d5d0b79537ae03aec9527d632d151f37fae8e39a323bc704fcba5165ecb1f6` | `fff8e99181e2d44611615d3c52d3cf978d8492f0ca28dfb9d5fd251b9aa3dcb1` (78) |
| `compact_lockstepBisim_of_noClobber` | compact-bisim-no-clobber (statement) | Quot.sound, propext | `9669b39b3cbe08ce6272077a247f2d9779fee32930591df45b11181087a43a0a` | `e99ed4ea131bb285909906df942e0e3e5390ff101c90c50276b057068dc87f1a` (80) |
| `complete_with_repeated_keys` | alist-checker-toy-cost-theta-SL (cited lemma) | propext | `fc0675dce6148b7be4d888c3eb44b7c02c4887c407517d83df3c4d44fe149edc` | `b46b0f82bf15aafe4f55d762db9940d83fc21bc8916f1a045c1014422cf00e29` (1) |
| `consPutOps_getPutOther` | store-laws-on-common-domain (cited lemma); certificate-checker-representation-independence (cited lemma) | propext | `1b2d78f610cb461195bafab3b2ef3f31883e57663180db66930ebecf55241c72` | `17979e1443da6004fb1316d059c618ee28e66637360d4c471eab0b089974afd0` (9) |
| `consPutOps_getPutSame` | store-laws-on-common-domain (cited lemma); certificate-checker-representation-independence (cited lemma) | propext | `3744505c0f74bd80319ecee704aee883c5e2eb2f282588f0212699de2ef23400` | `5410bc5ac4f513ab989d1527877c9422e1acda58a92c3997210e78cefe225629` (9) |
| `consPutOps_not_putPut` | store-laws-on-common-domain (cited lemma); certificate-checker-representation-independence (cited lemma) | propext | `d3b07789991e7aced6ea53fa5f34f328990438c357fb9013fbc4c0e3adb7c2b2` | `9d124c293144c6127d9ec0e0d5c02328bc9a86df6e824eb298b9d35f62789050` (8) |
| `disjoint_live_ranges_not_noAssignClobber` | compact-bisim-no-clobber (cited lemma) | Classical.choice, Quot.sound, propext | `fcdd0f697bd5e29a1dc22ff71f21eef662ec3e27b1b43b03ee72ae9febd76657` | `1de495971b4a4294b979f9f705ddc5067c9facdbb1f8ca3b67113f35dbf99137` (85) |
| `exists_postCorr_iff_dependsOnlyOnLive` | transportable-postconditions-characterization (statement) | Quot.sound, propext | `31dcf67bdd92762f9814f7b7171463c0c2ad20e43b7812ae4e7e85783c702e3b` | `16da563f2bcc5efe6bb5ffa77ee1161833b48b88edbcb89c3cdaf9f5e9570604` (26) |
| `famAlist_complete` | alist-checker-toy-cost-theta-SL (non-vacuity); store-laws-on-common-domain (non-vacuity) | Quot.sound, propext | `90de8e48123fa64e001d42420dd1a59fdfb426752e8a7ccf442179aa30c091be` | `d0c3019ac7271fbe8461f790645988eacda1c3ca070902cfd45fc3a1348172bf` (2) |
| `forall_exists_compactRel_iff_injOnLiveAt` | entry-adequacy-iff-injective-on-live (statement) | Classical.choice, Quot.sound, propext | `67c5515f5654790aad5639ba310333279954c1723e318bb71825bb79643d7d29` | `333b54cfb5abe8a035b8d434db5ebe0dc7ef8fafbb2ecfcbb84ccd4760fa1115` (23) |
| `funOps_laws` | store-laws-on-common-domain (statement) | Quot.sound, propext | `eae711bb6b14f3becd226d019c96fbd96ef53037a1dfc5e81d5264911c571734` | `ff1c879b0839c427e6d1ce36ec5abcec2f9ea1534ef3ae838acf23315131d106` (9) |
| `keptBisim_kept_dead_dbg` | compact-kept-bisim-injective (cited lemma) | Classical.choice, Quot.sound, propext | `dc86b240eadc50ee3cdd5046f355aaf87221dc506f6e89cf1f46afbf471ccfb0` | `f2441058b26793fc2705edb0cad2641a4920642dd2b0d3f16b3418b36be10b5a` (85) |
| `keptBisim_noninjective_writeFree` | compact-kept-bisim-injective (cited lemma); merging-simultaneously-live-slots-breaks-compaction (cited lemma) | Quot.sound, propext | `9d4b5b7dfc8a3af760025c1f1ea19bc28b965e8b0a468c0e7b9224dcede25f3e` | `f4dfca8c789eae0bacaabea469f990ef641ae32e48efdcfdd5baff96a38dc5c9` (76) |
| `nonvacuous_bisim_injective_loop` | compact-bisim-injective (non-vacuity) | Classical.choice, Quot.sound, propext | `88b7d85eecb832f7510d54ebf08a1343094203ce756efb04efa74135b09687fd` | `097efa363edd2c25ec14d9613fc7fcb1f6f802341d5f42b97eeeeebaeffa61f1` (45) |
| `nonvacuous_bisim_injective_straightLine` | compact-bisim-injective (non-vacuity) | Classical.choice, Quot.sound, propext | `08e6a59609ad66c9163bec02fcb7c451747fabeaf4436e496ca796756f284256` | `2262eda45817fa948e5fae75fb41e57db586954429a9a545d79692d58b906fc5` (45) |
| `nonvacuous_bisim_noClobber_loop` | compact-bisim-no-clobber (non-vacuity) | Classical.choice, Quot.sound, propext | `36e8b0ad4f09cb755be399e55e9fea54559c83d76f2e534abf9d7f4668aabd20` | `0bb4ede121c6e2e03ee63aa7060ee5b7c223ee5f9a4979648c1b5403ccce48af` (47) |
| `nonvacuous_bisim_noClobber_sharing` | compact-bisim-no-clobber (non-vacuity) | Quot.sound, propext | `269416774e23914691b6fc7cd3491442bf1f094730443794f847c1965c3c7550` | `484d9da714a98a1661a71db46d871ccec36c876d20f009f867f7de68d8b0d25d` (47) |
| `nonvacuous_cert` | liveness-certificate-overapproximates (non-vacuity) | Quot.sound, propext | `4cd4b9927f17fc8e6fcedb0e0847c67cf5c4301e28a66647182faaf1a9eab50f` | `b296be65bda12a0546f5a61b20cdda338dfeb66e023df2e7b0e998d18ab5e519` (43) |
| `nonvacuous_checkLive_sound` | liveness-checker-characterization-and-soundness (non-vacuity) | Quot.sound, propext | `1dc2f2204e89dfb176eb3934d2ab6609d5ee8595e6e0491c2ee879002f4c498c` | `65bc143e0e86aba4e587be509dc986462e4f51352dfe06a114b9865e5bf1c6ad` (45) |
| `nonvacuous_entry_iff` | entry-adequacy-iff-injective-on-live (non-vacuity) | Classical.choice, Quot.sound, propext | `82dacff005148a83f223bc6a3f3f6f2158841313ec0b4c11a80689f928c57213` | `4678d68a54cc392834f5a78220ac3269f45b27d00913a013d222c3f647d98ab8` (27) |
| `nonvacuous_keptBisim` | compact-kept-bisim-injective (non-vacuity) | Classical.choice, Quot.sound, propext | `17d0e33da5520b2e3c00980c3716c177d4f1402d8fbae956ff7e263ae1ab9918` | `10a7664e985f2b8917b861a7063d2cf86ae0b09860a27497ddb0a9c54f66ab53` (38) |
| `nonvacuous_keptBisim_kept_dead_dbg` | compact-kept-bisim-injective (non-vacuity) | Classical.choice, Quot.sound, propext | `ff24f32554788d615a84f17fd0e947f1035bd07706ac2d8ab4a76b3b5e0352bc` | `f5f1b2b443a7f9cd961d75f71a806e393a6c0dfde8db35c4cc549da5a91aeb46` (38) |
| `nonvacuous_keptBisim_not_transferClosed` | compact-kept-bisim-injective (non-vacuity) | Classical.choice, Quot.sound, propext | `429d109c0847fb6f2cf6df99a702f2bde94edca1568c2938da76e84fda6293fd` | `367eac32b47c569007d33e4c1d43176385ed00471e86614822132fe81329a125` (44) |
| `nonvacuous_postClass` | transportable-postconditions-characterization (non-vacuity) | Classical.choice, Quot.sound, propext | `4dff981fa83a26b876a79fa00cb30da6d6220392e276b19797b68e57c5967c88` | `8e2ffd6cf7e8e9d5689918d2026425293e261af83d4ec2268fdcf9bc32e259d9` (31) |
| `nonvacuous_repInd` | certificate-checker-representation-independence (non-vacuity) | Quot.sound, propext | `23defd54085b2eede939d5f4dc674531b08be84272bdb90028e46260177497a8` | `b762ebd1989b3f708bb6216698336c25e9e1ba5c5959f9faa756e30c81e7d272` (22) |
| `nonvacuous_repInd_funOps_alistOps` | certificate-checker-representation-independence (non-vacuity) | Quot.sound, propext | `b77a6f42a9e3a0d42f6d16bc0ea17878fbe7618e4a5994abcf5703e738998a32` | `ee7f534aec70c92b0890ab413f45430449e0f6c002f32f2dc14a406eb895f7d7` (16) |
| `nonvacuous_vc` | vc-transfer-original-to-compacted (non-vacuity) | Classical.choice, Quot.sound, propext | `314ba1e707df7d61e6e5d042140b0b2112580302eb91917ee6021db06a3a5092` | `3de652f015fd232c36de7f3037ccbb4c5ec7cce0ba63cfd17125f06be7a5d564` (83) |
| `nonvacuous_vc_bwd_sharing` | vc-transfer-compacted-to-original (non-vacuity) | Classical.choice, Quot.sound, propext | `167a8afc0a9157a9906e780074557e1a5afe91e6cce4d0de704390a94a3f0d0b` | `815acbdbfa795a8337af045664a0ae4c6b7ca30cecfd76b20e42674c36b72dee` (91) |
| `nonvacuous_wp_transport` | wp-transport-no-clobber (non-vacuity) | Classical.choice, Quot.sound, propext | `5dc7734374c9ff2a938988a80cde6a112d726752bb0fc115d0dea5673ee1acc5` | `923906d217ebb9b8c309160d205e31f48c582fcd3fdfedfbcf4f150d592ea651` (81) |
| `nonvacuous_wp_transport_rel` | wp-transport-no-clobber (non-vacuity) | Classical.choice, Quot.sound, propext | `513ad323c2ba267f31844c9b2b10489c190a0ee68488f5c264f4391f6033ce4d` | `53369a604dcd2aa346d4b61b3e3a9900ddcc498bef3300e96cad87dcce735fcd` (30) |
| `pA_exec` | merging-simultaneously-live-slots-breaks-compaction (statement) | propext | `43a5cd9bcfaf9741267d611f179f45373848870fa6255b6dd89ad5972ac0c990` | `a9eab861d1cf8353f3c1613e6259aae1c91a5de97dc8bbc031e378843f9aec49` (47) |
| `pA_exec_c` | merging-simultaneously-live-slots-breaks-compaction (statement) | propext | `3a099ed2dfdef5e09c77c3c46933e92569f8ddbd403e70bf2424d9e1b5aace3e` | `2018f1d0b188ec8e057796b24139e85ccc905e97993642c8b6082d3da8b90afa` (62) |
| `pA_rel` | merging-simultaneously-live-slots-breaks-compaction (statement) | propext | `6daff5c1b373d137974905ef87b79bad80ecc53c32c26388c32c42afdff11141` | `c23864ed165b404d47d15247753f5b995a68f653504511d11b4e9ada72145e56` (27) |
| `pD_events` | dead-debug-read-breaks-lockstep-bisimulation (statement) | propext | `5d403d052b4c5ec16d53b5ccfe9e513385292c923f2035322dbe4b6504ea8dba` | `ba9bd1cabcd2425958a30431f2d9f5af77e53dcc55ac44a99b654ff99d8a738e` (61) |
| `pD_silent_not_lockstep` | dead-debug-read-breaks-lockstep-bisimulation (cited lemma) | Quot.sound, propext | `17f284d71409462a67d5ab555b52b1efa850266e15309e2f3d4bf7eec861baff` | `999d9cd6076fb7af21241fe490be5b817d4e622aaf4636ac639308eb5708775a` (67) |
| `pM_exec` | marker-reset-breaks-slot-sharing (statement) | propext | `10ddabc762b5a423e74590fc919a943bf2f80656943ea0872148cf40bdc8892d` | `e9c62f24e4c9df7b21f9b7b730701e817aa58ebba05fcdd2abdd190701807299` (47) |
| `pM_exec_c` | marker-reset-breaks-slot-sharing (statement) | propext | `855b772c1dac7f20afcd778f57bff7232896eb4911c8373a2c618596eaf59763` | `f64e78149c8e5a5ec6578c35243d88a2eb980a647ae4f06c60d23bfb6b36ca1a` (62) |
| `pR_exec` | non-live-read-breaks-compaction (statement) | propext | `02addc45de4f1ebcd78c198f75dc346847d3fc57536dea1c8bde7b3716401316` | `2d15541fc386d22342db291f97ec3f301cb507b8540fc7b25751af29e3c5212e` (47) |
| `pR_exec_c` | non-live-read-breaks-compaction (statement) | propext | `f3d4429be0ce0f7f8967c5f0a9ce3c80b7f4f3cf901be5aabcb2e49dd84831de` | `9e15332f33edde951711ed720b9590ad351b3f6e5c69de919229208470ff3df4` (62) |
| `pR_rel` | non-live-read-breaks-compaction (statement) | propext | `36008fc81c45cc2d3c0ad55320f2976b035b5db4c40af3e4e4be1db84006b55a` | `4e336e715a81aa97520b987b6e52b746bb3bb983730cb26e3a6e6ac5d39bee0a` (27) |
| `pT_exec` | non-transfer-closed-mask-breaks-compaction (statement) | propext | `2451a17efafa2e18398090b5f4a1449702d5482567d3602a5b2227f9d5924382` | `f20502b3b67eb4da00ac7dbbef9f0192ecd7c7cc6461e3aabef2fdb4d7f6abdb` (47) |
| `pT_exec_c` | non-transfer-closed-mask-breaks-compaction (statement) | propext | `08858c20021f8000b8f1520b3c1c3464e47885ffdd758dc81b711c8ed6762c43` | `962c32e9f2c05cdf2cbe2b6dce32a098d196d6062005f4736ac3f125fd4b4e7d` (61) |
| `pT_first_step` | non-transfer-closed-mask-breaks-compaction (statement) | propext | `b9e8620b83accfd2a53081084b37260e1fa895af976bb1faeb43c0af75832897` | `ebce50642ba9b3813026e431aac6c3d40d4e6d3fe5dc5cba3d27582295a458cb` (56) |
| `pT_pathLive` | path-liveness-least-certificate (non-vacuity) | Quot.sound, propext | `eff285011c15d9dc52d9ba608a2e9e090860fc188baf47dea916d8956222d9b7` | `62f456284d11af35b0833f4faccd3af0518c851911efc36585d49dcc8fc4d492` (39) |
| `pathLiveMask_cert` | compact-bisim-injective (cited lemma) | Classical.choice, Quot.sound, propext | `3687c76ebe6333cfd3f3da0c66e5a509f5f3269212994fe80fa3c37133c1191c` | `b6ba9eda6e564f75dd3b2477030f44d8a5299815f8a47b946df7265863f96893` (41) |
| `pathLiveMask_least_cert` | path-liveness-least-certificate (statement) | Classical.choice, Quot.sound, propext | `1006686136e342e2b2621290bbfda66d17fe8b9df74af6b82e99d5eb2df25e73` | `b6ba9eda6e564f75dd3b2477030f44d8a5299815f8a47b946df7265863f96893` (41) |
| `pathLive_faint_operand` | compact-bisim-no-clobber (cited lemma); compact-kept-bisim-injective (cited lemma); non-live-read-breaks-compaction (cited lemma); liveness-certificate-overapproximates (cited lemma); liveness-checker-characterization-and-soundness (cited lemma); path-liveness-least-certificate (cited lemma) | propext | `9572e726a1b35b5d8c3b31fc33524de4614b07848978e49a04c88385512bf50c` | `8042edaae0b2f21e2a48219bfa96ae6c21f68738139998e0ece389acbfddd226` (86) |
| `pathLive_imp_mask_of_cert` | liveness-certificate-overapproximates (statement) | propext | `00f8fe3e4bab9d7b79c5b34b05b83f58f9860d421ef0ff5ce8d4847a2714648e` | `12d9841d8879ebbe535d8b12dc3388b8eae3400e77b9fb3aa6945237510e748c` (40) |
| `pathLive_infeasible_branch` | liveness-certificate-overapproximates (cited lemma); liveness-checker-characterization-and-soundness (cited lemma); path-liveness-least-certificate (cited lemma) | Quot.sound, propext | `95788ebf321522b1b8024970d94002a9709533858a338de6068ccbe153fe8c41` | `0d9060a27dc6a0fec9f1aef35d4ec400a9ff9274362454c4cfda73ec68fd674c` (58) |
| `postCorr_pullPost` | transportable-postconditions-characterization (statement) | Quot.sound, propext | `49ba3776ceaa5c043555a5a146d19db9dcadfdfeb9e8caf953b2b5101125eefd` | `a5bcb83edbc89322973e1cc6f1552ee18c13a1ed63e496c12e20fbc489db0a61` (29) |
| `runCheck_eq_of_getPut` | certificate-checker-representation-independence (statement) | propext | `063958e83eb1dc8ad6150e9caed8f199cb7f699afad2cd08b657981581a77f83` | `c1731186240fa4cb56678de2c776964a7529c3de7b6a574619231fb2d55aa4cf` (14) |
| `runCheck_funOps_eq_alistOps` | certificate-checker-representation-independence (statement) | Quot.sound, propext | `20c80d6cf10cd9dbdf28bb26fda22e70a55c03dd8ebaec9204d4644422a288bf` | `26ccbd615d0249b0065eb3969b5a87288d1bd267e80be07ed915301bd600262f` (20) |
| `runCost_alistOps_family` | alist-checker-toy-cost-theta-SL (statement) | Quot.sound, propext | `3415597806f6d441e804dd96efec032505597f924af9188b23fb171c070da0b1` | `9e77dad6a34b9e9c0a580ca4f28c8d3d780cd76fa90e5d39c7b2b6c9ba8c9cf6` (29) |
| `runCost_alistOps_le` | alist-checker-toy-cost-theta-SL (statement) | Quot.sound, propext | `85f4b189b177720d1a815f4485bae96d54a5f25660a895890046521a4773699e` | `725144285303d0176455d2ff7cb96b28436d1f97c1fba6e4a59ff2cdd98feda8` (28) |
| `runCost_unitCost_family` | unit-cost-checker-toy-cost-O-S (non-vacuity); unit-cost-checker-toy-cost-O-S (statement) | Quot.sound, propext | `9b78d3d705c806d8cffb708e05e2f4c05ef2f440b820082805024f39cdc589fa` | `d28dc7bb1c1efa9144215ed7295a7dd55ca72114006d28c38e58230d3b5bbc17` (18) |
| `runCost_unitCost_le` | unit-cost-checker-toy-cost-O-S (statement) | Quot.sound, propext | `f6bcb561271024b6c50770526bd7ce83fe93ffa6b1d1a4cfb564657b35b9f8d8` | `ca1eb5ff9533dfd80e0c5d7fa1b20a756a55f158793bf8b0c6ece2df4c6f902e` (17) |
| `vc_backward_of_noClobber` | vc-transfer-compacted-to-original (statement) | Quot.sound, propext | `2bef38936a85eed6cca121d61ea1ad81427fbe48b4e54f03e164b334da7198a7` | `d245bba3d950d4fd8ac7b25d97f5a39923ac52876734e21b585a2362c1763766` (82) |
| `vc_backward_without_inj0_postTrue` | vc-transfer-compacted-to-original (cited lemma) | propext | `47718d4d4998f4992788c5cef6e19ca41ece614ec0c334d39fc5fd4c2a9918c7` | `e2226d58057abe7bb5bae0127c9fdf4cd5d9700767d6cca55d62b7705b96cef2` (68) |
| `vc_forward_of_noClobber` | vc-transfer-original-to-compacted (statement) | Quot.sound, propext | `7695cc6b0efe8e78736bf868bf77e651fef5cb6ed368d801023cdefa7f938faf` | `e4978979eea8c919b2db759302fcc41b66a3bd8f4c2ada0e87116439e11c8526` (80) |
| `vc_forward_vacuous_dropped` | vc-transfer-original-to-compacted (cited lemma) | Quot.sound, propext | `c6b8534d267d4d2e8c90af8a9ab096233a3ea92735cf2057b09743630376f524` | `2a00e061d705f496711a625945aa0a2e0df28962d85c06cedd79508182446eac` (78) |
| `vc_forward_vacuous_merged` | vc-transfer-original-to-compacted (cited lemma) | Quot.sound, propext | `cb4ade3d960d11d4f8dc994444142375acc9a5bf40532e62d12481c64f3887b3` | `8ba1c56eef0e1dc4498f750e9f767413f5053959a00c8e18333eb60bb6c21744` (80) |
| `vc_transfer_of_noClobber` | vc-transfer-compacted-to-original (cited lemma) | Quot.sound, propext | `665fb546d2d4539de926a7f7182ed0cae59636e74dc28d8b12559ecd3a3f2d68` | `d245bba3d950d4fd8ac7b25d97f5a39923ac52876734e21b585a2362c1763766` (82) |
| `wp_transport_of_noClobber` | wp-transport-no-clobber (statement) | Quot.sound, propext | `dd474cb5e00ef921b0d7071505e5107f44d2cfeca88ec71790c6215ae14ae8f2` | `00f9402fb07bdd1afa15dd4ab7b3cb5c3dfbceb15cc35d2e6d839dccef5941d1` (79) |

### Primary sources

* Lean 4 toolchain: repository `leanprover/lean4`, release tag `v4.34.1`, tag commit
  `5045d0056413266e57c625dcd7c365b10e377c52` (from the GitHub API `git/ref/tags/v4.34.1`, a lightweight tag on that
  commit; read 2026-11-21).
* CakeML: repository `CakeML/cakeml`, commit `2874b664e10939a3ee462215b2e068c89c1f70eb`, file
  `compiler/backend/proofs/word_allocProofScript.sml`: `colouring_ok` (lines 99-141), `strong_locals_rel`
  (lines 178-183), `evaluate_apply_colour` (from line 1107). Paper: Tan, Myreen, Kumar, Fox, Owens,
  Norrish, "The verified CakeML compiler backend", Journal of Functional Programming 29, e2 (2019),
  DOI `10.1017/S0956796818000229` (bibliographic record; paper text not consulted).
* CompCert: repository `AbsInt/CompCert`, commit `2685140bf72c959446981fb99b5e44a8975021bc`, files
  `backend/Allocation.v` (header), `backend/Allocproof.v` (header lines 13-14, theorem lines 2528-2529),
  `backend/Stacking.v` (`offset_local`, line 27), `backend/Stackingproof.v` (lines 2201-2202),
  `backend/Linearizeproof.v` (lines 728-729), `backend/Liveness.v` (lines 68-91, 111),
  `backend/Deadcodeproof.v` (lines 1263-1264). Paper: Rideau and Leroy, "Validating Register Allocation
  and Spilling", CC 2010, LNCS 6011, pp. 224-243, DOI `10.1007/978-3-642-11970-5_13` (bibliographic
  record; paper text not consulted).
* LLVM: repository `llvm/llvm-project`, commit `25b1c803e1e1504f6dc11f7afd68e65ad3ee5964`, files
  `llvm/lib/CodeGen/StackColoring.cpp` (implementation notes, lines 135-160) and
  `llvm/lib/CodeGen/StackSlotColoring.cpp` (`ColorAssignmentInfo::overlaps`, lines 109-115;
  `StackSlotColoring::ColorSlot` from line 303).
* rustc: repository `rust-lang/rust`, commit `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, file
  `compiler/rustc_mir_transform/src/simplify.rs` (`SimplifyLocals` from line 436; `run_pass` line 455;
  fixed-point loop line 636; `always_used = debuginfo_locals(body)` line 529; `statement_removed` line
  658; `make_nop` line 659; `strip_nops` line 661).
* J. McCarthy, "Towards a Mathematical Science of Computation", Information Processing 1962 (IFIP
  Congress 62), North-Holland, 1963, pp. 21-28; author's web version
  http://www-formal.stanford.edu/jmc/towards/towards.html.
* J. N. Foster, M. B. Greenwald, J. T. Moore, B. C. Pierce, A. Schmitt, "Combinators for Bidirectional
  Tree Transformations", ACM TOPLAS 29(3), Article 17, 2007, DOI `10.1145/1232420.1232424`
  (bibliographic record and law names; paper text not consulted).
* T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014, DOI
  `10.1007/978-3-319-10542-0` (table of contents of the authors' PDF, http://concrete-semantics.org/concrete-semantics.pdf).
* F. Nielson, H. R. Nielson, C. Hankin, *Principles of Program Analysis*, Springer, 1999, ISBN
  978-3-540-65410-0, DOI `10.1007/978-3-662-03811-6`, section 2.1.4.
* A. W. Appel, *Modern Compiler Implementation in ML*, Cambridge University Press, 1998, chapters 10-11
  (table of contents, https://www.cs.princeton.edu/~appel/modern/ml/); A. W. Appel, *Verified
  Functional Algorithms*, chapter "ADT", https://softwarefoundations.cis.upenn.edu/vfa-current/ADT.html.
* P. Lammich et al., "Collections Framework", Archive of Formal Proofs, 2009,
  https://www.isa-afp.org/entries/Collections.html; P. Lammich and A. Lochbihler, "The Isabelle
  Collections Framework", ITP 2010, pp. 339-354, DOI `10.1007/978-3-642-14052-5_24`.
* J. C. Reynolds, "Types, Abstraction and Parametric Polymorphism", Information Processing 83,
  North-Holland, 1983, pp. 513-523 (first page and abstract).

The repository line numbers above were re-read at the stated commits on 2026-11-21
for `word_allocProofScript.sml`, `simplify.rs` and `StackColoring.cpp`; the remaining records are as
stated on each card's prior-art entry. No source establishes any theorem of this package; they are
cited for prior art and for the derived modeling bridges.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`. Nothing else is downloaded: the Lean project has no dependencies.

Primary check, from the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory and (1) runs `lake build`; (2) scans the Lean sources for `sorry`, `admit`, `native_decide` and `axiom` declarations; (3) generates and runs a small Lean program that computes `collectAxioms` for every library declaration and fails unless each uses only `propext`, `Classical.choice`, `Quot.sound`; (4) for every name referenced by `results.json` and every name in `audit/statements.json`, recomputes the statement hash (SHA-256 of the `repr` of its type) and the closure hash (SHA-256 of the sorted `name : repr(type) := repr(value)` lines of the library constants reachable from the statement, theorem bodies excluded) and compares them with `audit/statements.json`. It prints `REVALIDATED` and exits 0 iff every check passes. The package directory itself is not modified.

Manual axiom check with Lean alone:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` is outside the library target; it imports `ToySlotCompact` and runs `#print axioms` for each of the 124 referenced declarations. Each output line must list a subset of `propext`, `Classical.choice`, `Quot.sound`.

Narrow checks after a change: a change to any definition reachable from a card's statement changes that card's closure hash, and a change to the statement changes its statement hash, so a failing hash in step (4) names exactly the affected cards. A passing revalidation establishes that the same statements are kernel-checked under the pinned toolchain with the standard axioms; it does not re-examine the prose, the prior-art records or the modeling bridges, and it says nothing about real compilers or verifiers.
