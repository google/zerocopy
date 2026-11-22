/-!
# Box-deref elaboration, critical call-edge splitting, unneeded-drop removal and
# return duplication: a small mechanized model

This file is self-contained (Lean core only, no imports). It models four `rustc` MIR
transformations on a deliberately small control-flow-graph language and proves the
properties stated in the accompanying report:

* `addCallGuards` (model of `AddCallGuards::CriticalCallEdges`): exact preservation of
  terminal behaviour, absence of critical output-bearing edges afterwards, and soundness
  of the "store the result at the entry of the destination block" lowering that LLVM
  `invoke` / `callbr` force on a code generator.
* `removeUnneededDrops` (model of `RemoveUnneededDrops`).
* `multipleReturnTerminators` (model of `MultipleReturnTerminators`).
* `elaborate` (model of `ElaborateBoxDerefs`).

together with constructive counterexamples for the unsound variants.

Everything here is a *model*: the statements are about the definitions in this file.
How those definitions correspond to `rustc` source is argued in the report, not here.
-/

namespace BoxDerefCallGuards

/-! Every `def` below carries `noncomputable`. Nothing here is meant to run as compiled code:
all evaluation in this file happens in the kernel. Without the marker Lean generates a
compiler-only helper constant `<name>._unsafe_rec` (flagged `partial`) for each recursive
definition; a section-level `noncomputable section` does not prevent that in Lean v4.34.1, a
per-definition marker does. With the markers, the checked environment contains no `partial`,
`unsafe` or `._unsafe_rec` constant. -/

/-! ## Part 0. Deterministic machines, fuel-indexed runs, and one-step-stuttering simulation -/

/-- Result of one machine step: keep running in a new state, or halt with a result. -/
inductive Outcome (σ : Type) (ρ : Type) where
  | running (s : σ)
  | halt (r : ρ)

/-- Relabel the state carried by a `running` outcome. -/
noncomputable def Outcome.map {σ τ ρ : Type} (f : σ → τ) : Outcome σ ρ → Outcome τ ρ
  | .running s => .running (f s)
  | .halt r => .halt r

/-- Run a deterministic step function for at most `n` steps. -/
noncomputable def run {σ ρ : Type} (step : σ → Outcome σ ρ) : Nat → σ → Outcome σ ρ
  | 0, s => .running s
  | n + 1, s =>
    match step s with
    | .running s' => run step n s'
    | .halt r => .halt r

/-- `Halts step s r`: started in `s`, the machine halts with result `r` after finitely many steps. -/
noncomputable def Halts {σ ρ : Type} (step : σ → Outcome σ ρ) (s : σ) (r : ρ) : Prop :=
  ∃ n, run step n s = .halt r

theorem run_zero {σ ρ : Type} (step : σ → Outcome σ ρ) (s : σ) :
    run step 0 s = .running s := rfl

theorem run_succ_running {σ ρ : Type} {step : σ → Outcome σ ρ} {s s' : σ} (n : Nat)
    (h : step s = .running s') : run step (n + 1) s = run step n s' := by
  show (match step s with
    | .running s' => run step n s'
    | .halt r => .halt r) = run step n s'
  rw [h]

theorem run_succ_halt {σ ρ : Type} {step : σ → Outcome σ ρ} {s : σ} {r : ρ} (n : Nat)
    (h : step s = .halt r) : run step (n + 1) s = .halt r := by
  show (match step s with
    | .running s' => run step n s'
    | .halt r => .halt r) = .halt r
  rw [h]

/-- One-step correspondence between machine `A` and machine `B`, where `B` may need one extra
step: either both halt with the same result, or both move to corresponding states, and in both
cases `B` is allowed to pass through one intermediate state `m` first. -/
inductive StepMatch {σA σB ρ : Type} (stepA : σA → Outcome σA ρ) (stepB : σB → Outcome σB ρ)
    (emb : σA → σB) (a : σA) : Prop where
  | halt (r : ρ) (hA : stepA a = .halt r) (hB : stepB (emb a) = .halt r)
  | run1 (a' : σA) (hA : stepA a = .running a') (hB : stepB (emb a) = .running (emb a'))
  | run2 (a' : σA) (m : σB) (hA : stepA a = .running a') (hB₁ : stepB (emb a) = .running m)
      (hB₂ : stepB m = .running (emb a'))
  | halt2 (r : ρ) (m : σB) (hA : stepA a = .halt r) (hB₁ : stepB (emb a) = .running m)
      (hB₂ : stepB m = .halt r)

theorem halts_of_stepMatch_forward {σA σB ρ : Type} {stepA : σA → Outcome σA ρ}
    {stepB : σB → Outcome σB ρ} {emb : σA → σB} (h : ∀ a, StepMatch stepA stepB emb a) (r : ρ) :
    ∀ (n : Nat) (a : σA), run stepA n a = .halt r → ∃ m, run stepB m (emb a) = .halt r := by
  intro n
  induction n with
  | zero =>
    intro a ha
    rw [run_zero] at ha
    cases ha
  | succ n ih =>
    intro a ha
    cases h a with
    | halt r' hA hB =>
      rw [run_succ_halt n hA] at ha
      cases ha
      exact ⟨0 + 1, run_succ_halt 0 hB⟩
    | run1 a' hA hB =>
      rw [run_succ_running n hA] at ha
      obtain ⟨m, hm⟩ := ih a' ha
      exact ⟨m + 1, by rw [run_succ_running m hB]; exact hm⟩
    | run2 a' mid hA hB₁ hB₂ =>
      rw [run_succ_running n hA] at ha
      obtain ⟨m, hm⟩ := ih a' ha
      exact ⟨m + 1 + 1, by rw [run_succ_running (m + 1) hB₁, run_succ_running m hB₂]; exact hm⟩
    | halt2 r' mid hA hB₁ hB₂ =>
      rw [run_succ_halt n hA] at ha
      cases ha
      exact ⟨0 + 1 + 1, by rw [run_succ_running (0 + 1) hB₁]; exact run_succ_halt 0 hB₂⟩

theorem halts_of_stepMatch_backward {σA σB ρ : Type} {stepA : σA → Outcome σA ρ}
    {stepB : σB → Outcome σB ρ} {emb : σA → σB} (h : ∀ a, StepMatch stepA stepB emb a) (r : ρ) :
    ∀ (n k : Nat), k ≤ n → ∀ (a : σA), run stepB k (emb a) = .halt r →
      ∃ j, run stepA j a = .halt r := by
  intro n
  induction n with
  | zero =>
    intro k hk a ha
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    rw [run_zero] at ha
    cases ha
  | succ n ih =>
    intro k hk a ha
    cases k with
    | zero =>
      rw [run_zero] at ha
      cases ha
    | succ k =>
      have hkn : k ≤ n := Nat.le_of_succ_le_succ hk
      cases h a with
      | halt r' hA hB =>
        rw [run_succ_halt k hB] at ha
        cases ha
        exact ⟨0 + 1, run_succ_halt 0 hA⟩
      | run1 a' hA hB =>
        rw [run_succ_running k hB] at ha
        obtain ⟨j, hj⟩ := ih k hkn a' ha
        exact ⟨j + 1, by rw [run_succ_running j hA]; exact hj⟩
      | run2 a' mid hA hB₁ hB₂ =>
        rw [run_succ_running k hB₁] at ha
        cases k with
        | zero =>
          rw [run_zero] at ha
          cases ha
        | succ k =>
          rw [run_succ_running k hB₂] at ha
          obtain ⟨j, hj⟩ := ih k (Nat.le_of_succ_le hkn) a' ha
          exact ⟨j + 1, by rw [run_succ_running j hA]; exact hj⟩
      | halt2 r' mid hA hB₁ hB₂ =>
        rw [run_succ_running k hB₁] at ha
        cases k with
        | zero =>
          rw [run_zero] at ha
          cases ha
        | succ k =>
          rw [run_succ_halt k hB₂] at ha
          cases ha
          exact ⟨0 + 1, run_succ_halt 0 hA⟩

/-- Machines related by `StepMatch` have exactly the same terminal behaviours. -/
theorem halts_iff_of_stepMatch {σA σB ρ : Type} {stepA : σA → Outcome σA ρ}
    {stepB : σB → Outcome σB ρ} {emb : σA → σB} (h : ∀ a, StepMatch stepA stepB emb a)
    (a : σA) (r : ρ) : Halts stepA a r ↔ Halts stepB (emb a) r :=
  ⟨fun ⟨n, hn⟩ => halts_of_stepMatch_forward h r n a hn,
   fun ⟨k, hk⟩ => halts_of_stepMatch_backward h r k k (Nat.le_refl k) a hk⟩

/-- Lock-step simulation through a state projection `f`. -/
theorem run_map {σ τ ρ : Type} {stepA : σ → Outcome σ ρ} {stepB : τ → Outcome τ ρ} {f : σ → τ}
    (h : ∀ s, stepB (f s) = (stepA s).map f) :
    ∀ (n : Nat) (s : σ), run stepB n (f s) = (run stepA n s).map f := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    cases hs : stepA s with
    | running s' =>
      have hB : stepB (f s) = .running (f s') := by rw [h s, hs]; rfl
      rw [run_succ_running n hB, run_succ_running n hs]
      exact ih s'
    | halt r =>
      have hB : stepB (f s) = .halt r := by rw [h s, hs]; rfl
      rw [run_succ_halt n hB, run_succ_halt n hs]
      rfl

theorem halts_map_iff {σ τ ρ : Type} {stepA : σ → Outcome σ ρ} {stepB : τ → Outcome τ ρ}
    {f : σ → τ} (h : ∀ s, stepB (f s) = (stepA s).map f) (s : σ) (r : ρ) :
    Halts stepA s r ↔ Halts stepB (f s) r := by
  constructor
  · intro ⟨n, hn⟩
    exact ⟨n, by rw [run_map h n s, hn]; rfl⟩
  · intro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [run_map h n s] at hn
    cases hr : run stepA n s with
    | running s' => rw [hr] at hn; cases hn
    | halt r' => rw [hr] at hn; cases hn; rfl

/-! ## Part 1. A small MIR-like control-flow-graph language -/

/-- Local-variable environment: local index ↦ value. -/
abbrev Env := Nat → Nat

/-- Overwrite local `x` with `v`. -/
noncomputable def upd (e : Env) (x v : Nat) : Env := fun y => if y = x then v else e y

theorem upd_upd_same (e : Env) (x v : Nat) : upd (upd e x v) x v = upd e x v := by
  funext y
  by_cases h : y = x <;> simp [upd, h]

/-- Total list indexing, defined here so that every lemma about it is local to this file. -/
noncomputable def nth {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, n + 1 => nth l n

/-- Terminal result: `some env` is a normal return, `none` is undefined behaviour or an abort. -/
abbrev Res := Option Env

/-- Terminators. Semantic ingredients (conditions, callee results, drop glue) are shallowly
embedded as functions of the environment.

* `out inv dst rhs sel targets cleanup` is an *output-bearing multi-successor terminator*: it
  models both `Call { destination, target: Some(_), unwind }` (one normal target) and
  `InlineAsm` with `out`/`inout` operands (fallthrough plus `label` targets). If `sel env`
  indexes a normal target, the output `rhs env` is written to local `dst` and control goes
  there; otherwise control takes the `cleanup` edge without writing `dst` (or aborts if there is
  none). The flag `inv` records whether a code generator must emit the terminator as a
  block-terminating instruction (`invoke` / `callbr`), so that the store of the output cannot be
  placed in the same block.
* `drop needsDrop glue t unwind` runs drop glue: `glue env = some env'` continues at `t`,
  `glue env = none` unwinds. -/
inductive Term (ι : Type) where
  | goto (t : ι)
  | switch (c : Env → Bool) (t e : ι)
  | out (inv : Bool) (dst : Nat) (rhs : Env → Nat) (sel : Env → Nat) (targets : List ι)
      (cleanup : Option ι)
  | drop (needsDrop : Bool) (glue : Env → Option Env) (t : ι) (unwind : Option ι)
  | ret
  | unreachable

/-- A basic block: straight-line statements (each may be UB, i.e. `none`) and a terminator. -/
structure Blk (ι : Type) where
  stmts : List (Env → Option Env)
  term : Term ι

/-- A control-flow graph over block identifiers `ι`; `none` means "no such block". -/
abbrev Cfg (ι : Type) := ι → Option (Blk ι)

/-- Machine state: current block and environment. -/
abbrev St (ι : Type) := ι × Env

noncomputable def execStmts : List (Env → Option Env) → Env → Option Env
  | [], e => some e
  | s :: ss, e =>
    match s e with
    | some e' => execStmts ss e'
    | none => none

noncomputable def stepTerm {ι : Type} : Term ι → Env → Outcome (St ι) Res
  | .goto t, e => .running (t, e)
  | .switch c t f, e => .running (if c e = true then t else f, e)
  | .out _ dst rhs sel ts c, e =>
    match nth ts (sel e) with
    | some t => .running (t, upd e dst (rhs e))
    | none =>
      match c with
      | some u => .running (u, e)
      | none => .halt none
  | .drop _ glue t u, e =>
    match glue e with
    | some e' => .running (t, e')
    | none =>
      match u with
      | some u' => .running (u', e)
      | none => .halt none
  | .ret, e => .halt (some e)
  | .unreachable, _ => .halt none

/-- One MIR step: run the whole current block. -/
noncomputable def step {ι : Type} (q : Cfg ι) (s : St ι) : Outcome (St ι) Res :=
  match q s.1 with
  | none => .halt none
  | some b =>
    match execStmts b.stmts s.2 with
    | none => .halt none
    | some e' => stepTerm b.term e'

/-- Fuel-indexed MIR evaluation. -/
noncomputable def evalMir {ι : Type} (q : Cfg ι) (n : Nat) (pc : ι) (e : Env) : Outcome (St ι) Res :=
  run (step q) n (pc, e)

theorem step_none {ι : Type} {q : Cfg ι} {s : St ι} (h : q s.1 = none) :
    step q s = .halt none := by
  show (match q s.1 with
    | none => Outcome.halt none
    | some b =>
      match execStmts b.stmts s.2 with
      | none => .halt none
      | some e' => stepTerm b.term e') = .halt none
  rw [h]

theorem step_stmts_none {ι : Type} {q : Cfg ι} {s : St ι} {b : Blk ι} (h : q s.1 = some b)
    (h2 : execStmts b.stmts s.2 = none) : step q s = .halt none := by
  show (match q s.1 with
    | none => Outcome.halt none
    | some b =>
      match execStmts b.stmts s.2 with
      | none => .halt none
      | some e' => stepTerm b.term e') = .halt none
  rw [h]
  show (match execStmts b.stmts s.2 with
    | none => Outcome.halt none
    | some e' => stepTerm b.term e') = .halt none
  rw [h2]

theorem step_some {ι : Type} {q : Cfg ι} {s : St ι} {b : Blk ι} {e' : Env} (h : q s.1 = some b)
    (h2 : execStmts b.stmts s.2 = some e') : step q s = stepTerm b.term e' := by
  show (match q s.1 with
    | none => Outcome.halt none
    | some b =>
      match execStmts b.stmts s.2 with
      | none => .halt none
      | some e' => stepTerm b.term e') = stepTerm b.term e'
  rw [h]
  show (match execStmts b.stmts s.2 with
    | none => Outcome.halt none
    | some e' => stepTerm b.term e') = stepTerm b.term e'
  rw [h2]


theorem stepTerm_out_some {ι : Type} {inv : Bool} {dst : Nat} {rhs sel : Env → Nat}
    {ts : List ι} {c : Option ι} {e : Env} {t : ι} (h : nth ts (sel e) = some t) :
    stepTerm (.out inv dst rhs sel ts c) e = .running (t, upd e dst (rhs e)) := by
  simp [stepTerm, h]

theorem stepTerm_out_none_some {ι : Type} {inv : Bool} {dst : Nat} {rhs sel : Env → Nat}
    {ts : List ι} {u : ι} {e : Env} (h : nth ts (sel e) = none) :
    stepTerm (.out inv dst rhs sel ts (some u)) e = .running (u, e) := by
  simp [stepTerm, h]

theorem stepTerm_out_none_none {ι : Type} {inv : Bool} {dst : Nat} {rhs sel : Env → Nat}
    {ts : List ι} {e : Env} (h : nth ts (sel e) = none) :
    stepTerm (.out inv dst rhs sel ts none) e = .halt none := by
  simp [stepTerm, h]

theorem stepTerm_drop_some {ι : Type} {nd : Bool} {g : Env → Option Env} {t : ι} {u : Option ι}
    {e e' : Env} (h : g e = some e') : stepTerm (.drop nd g t u) e = .running (t, e') := by
  simp [stepTerm, h]

theorem stepTerm_drop_none_some {ι : Type} {nd : Bool} {g : Env → Option Env} {t u : ι}
    {e : Env} (h : g e = none) : stepTerm (.drop nd g t (some u)) e = .running (u, e) := by
  simp [stepTerm, h]

theorem stepTerm_drop_none_none {ι : Type} {nd : Bool} {g : Env → Option Env} {t : ι}
    {e : Env} (h : g e = none) : stepTerm (.drop nd g t none) e = .halt none := by
  simp [stepTerm, h]

/-! ## Part 2. `AddCallGuards::CriticalCallEdges` -/

theorem nth_nil {α : Type} (i : Nat) : nth ([] : List α) i = none := by
  cases i <;> rfl

/-- Successor in a given *slot*: `some i` is the `i`-th normal successor, `none` is the
unwind/cleanup edge. -/
noncomputable def Term.succAt {ι : Type} : Term ι → Option Nat → Option ι
  | .goto t, some i => if i = 0 then some t else none
  | .goto _, none => none
  | .switch _ t e, some i => if i = 0 then some t else if i = 1 then some e else none
  | .switch _ _ _, none => none
  | .out _ _ _ _ ts _, some i => nth ts i
  | .out _ _ _ _ _ c, none => c
  | .drop _ _ t _, some i => if i = 0 then some t else none
  | .drop _ _ _ u, none => u
  | .ret, _ => none
  | .unreachable, _ => none

/-- `1` if `x` is the block `t`, else `0`. -/
noncomputable def hit (t x : Nat) : Nat := if x = t then 1 else 0

noncomputable def hitOpt (t : Nat) : Option Nat → Nat
  | some x => hit t x
  | none => 0

noncomputable def countIn (t : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => hit t x + countIn t xs

/-- Number of successor occurrences of block `t` in one terminator (with multiplicity), i.e. this
terminator's contribution to `pred_count[t]`. -/
noncomputable def Term.predContrib (t : Nat) : Term Nat → Nat
  | .goto a => hit t a
  | .switch _ a b => hit t a + hit t b
  | .out _ _ _ _ ts c => countIn t ts + hitOpt t c
  | .drop _ _ a u => hit t a + hitOpt t u
  | .ret => 0
  | .unreachable => 0

/-- A program: basic blocks indexed by position. -/
abbrev Prog := List (Blk Nat)

noncomputable def Prog.cfg (p : Prog) : Cfg Nat := fun b => nth p b

/-- `predCount p t` is `pred_count[t]`: the number of successor occurrences of `t` over all
terminators of `p`, with multiplicity. -/
noncomputable def predCount : Prog → Nat → Nat
  | [], _ => 0
  | b :: bs, t => b.term.predContrib t + predCount bs t

/-- Block identifiers after the pass: original blocks, plus one fresh guard block per
(source block, normal-successor slot). `rustc` numbers fresh blocks consecutively after the
existing ones; only freshness matters, so the model uses a tagged identifier instead. -/
inductive GId where
  | orig (b : Nat)
  | guard (b : Nat) (i : Nat)

/-- The splitting criterion: the terminator must be emitted as `invoke`/`callbr` (`inv`) and the
target must have more than one predecessor edge. -/
noncomputable def splitEdge (p : Prog) (inv : Bool) (t : Nat) : Bool := inv && decide (1 < predCount p t)

noncomputable def retargetList (p : Prog) (b : Nat) (inv : Bool) : Nat → List Nat → List GId
  | _, [] => []
  | i, t :: ts =>
    (if splitEdge p inv t = true then GId.guard b i else GId.orig t) ::
      retargetList p b inv (i + 1) ts

noncomputable def retarget (p : Prog) (b : Nat) : Term Nat → Term GId
  | .goto t => .goto (.orig t)
  | .switch c t e => .switch c (.orig t) (.orig e)
  | .out inv dst rhs sel ts c => .out inv dst rhs sel (retargetList p b inv 0 ts) (c.map .orig)
  | .drop nd g t u => .drop nd g (.orig t) (u.map .orig)
  | .ret => .ret
  | .unreachable => .unreachable

/-- The guard block created for slot `i` of block `b`, if that edge is split: an empty block
whose terminator is `goto` to the original target. -/
noncomputable def guardBlock (p : Prog) (b i : Nat) : Option (Blk GId) :=
  match nth p b with
  | some blk =>
    match blk.term with
    | .out inv _ _ _ ts _ =>
      match nth ts i with
      | some t => if splitEdge p inv t = true then some ⟨[], .goto (.orig t)⟩ else none
      | none => none
    | _ => none
  | none => none

/-- Model of `AddCallGuards::CriticalCallEdges`. -/
noncomputable def addCallGuards (p : Prog) : Cfg GId
  | .orig b => (nth p b).map (fun blk => ⟨blk.stmts, retarget p b blk.term⟩)
  | .guard b i => guardBlock p b i

theorem nth_retargetList (p : Prog) (b : Nat) (inv : Bool) :
    ∀ (ts : List Nat) (k i : Nat),
      nth (retargetList p b inv k ts) i =
        (nth ts i).map
          (fun t => if splitEdge p inv t = true then GId.guard b (k + i) else GId.orig t)
  | [], k, i => by rw [nth_nil]; show nth [] i = none; rw [nth_nil]
  | t :: ts, k, 0 => rfl
  | t :: ts, k, i + 1 => by
    show nth (retargetList p b inv (k + 1) ts) i = _
    rw [nth_retargetList p b inv ts (k + 1) i]
    have hk : k + 1 + i = k + (i + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 i]
    rw [hk]
    rfl

theorem guardBlock_split (p : Prog) (b i : Nat) {blk : Blk Nat} {inv : Bool} {dst : Nat}
    {rhs : Env → Nat} {sel : Env → Nat} {ts : List Nat} {c : Option Nat} {t : Nat}
    (hb : nth p b = some blk) (ht : blk.term = .out inv dst rhs sel ts c)
    (hi : nth ts i = some t) (hs : splitEdge p inv t = true) :
    guardBlock p b i = some ⟨[], .goto (.orig t)⟩ := by
  unfold guardBlock
  rw [hb]
  simp only [ht, hi, hs]
  rfl

/-- One step of the original program is matched by one step of the transformed program, or by
two steps when the edge taken was split (the second being the guard block's `goto`). -/
theorem addCallGuards_stepMatch (p : Prog) (a : St Nat) :
    StepMatch (step p.cfg) (step (addCallGuards p)) (fun a => (GId.orig a.1, a.2)) a := by
  obtain ⟨b, e⟩ := a
  cases hb : nth p b with
  | none =>
    have hA : step p.cfg (b, e) = .halt none := step_none hb
    have hB : step (addCallGuards p) (GId.orig b, e) = .halt none := by
      apply step_none
      show (nth p b).map _ = none
      rw [hb]; rfl
    exact .halt none hA hB
  | some blk =>
    have hq : addCallGuards p (GId.orig b) = some ⟨blk.stmts, retarget p b blk.term⟩ := by
      show (nth p b).map _ = _
      rw [hb]; rfl
    cases hs : execStmts blk.stmts e with
    | none =>
      exact .halt none (step_stmts_none (q := p.cfg) (s := (b, e)) hb hs)
        (step_stmts_none (q := addCallGuards p) (s := (GId.orig b, e)) hq hs)
    | some e' =>
      have hA : step p.cfg (b, e) = stepTerm blk.term e' :=
        step_some (q := p.cfg) (s := (b, e)) hb hs
      have hB : step (addCallGuards p) (GId.orig b, e) = stepTerm (retarget p b blk.term) e' :=
        step_some (q := addCallGuards p) (s := (GId.orig b, e)) hq hs
      cases ht : blk.term with
      | goto t =>
        rw [ht] at hA hB
        exact .run1 (t, e') hA hB
      | switch c t f =>
        rw [ht] at hA hB
        refine .run1 (if c e' = true then t else f, e') hA ?_
        rw [hB]
        show Outcome.running ((if c e' = true then GId.orig t else GId.orig f), e') = _
        cases c e' <;> rfl
      | ret =>
        rw [ht] at hA hB
        exact .halt (some e') hA hB
      | unreachable =>
        rw [ht] at hA hB
        exact .halt none hA hB
      | drop nd g t u =>
        rw [ht] at hA hB
        have hB' : step (addCallGuards p) (GId.orig b, e) =
            stepTerm (.drop nd g (GId.orig t) (u.map GId.orig)) e' := hB
        cases hg : g e' with
        | some e'' =>
          rw [stepTerm_drop_some hg] at hA hB'
          exact .run1 (t, e'') hA hB'
        | none =>
          cases u with
          | some u' =>
            rw [stepTerm_drop_none_some hg] at hA
            have hB'' : step (addCallGuards p) (GId.orig b, e) =
                stepTerm (.drop nd g (GId.orig t) (some (GId.orig u'))) e' := hB'
            rw [stepTerm_drop_none_some hg] at hB''
            exact .run1 (u', e') hA hB''
          | none =>
            rw [stepTerm_drop_none_none hg] at hA
            have hB'' : step (addCallGuards p) (GId.orig b, e) =
                stepTerm (.drop nd g (GId.orig t) none) e' := hB'
            rw [stepTerm_drop_none_none hg] at hB''
            exact .halt none hA hB''
      | out inv dst rhs sel ts c =>
        rw [ht] at hA hB
        have hB' : step (addCallGuards p) (GId.orig b, e) =
            stepTerm (.out inv dst rhs sel (retargetList p b inv 0 ts) (c.map GId.orig)) e' := hB
        have hrt := nth_retargetList p b inv ts 0 (sel e')
        cases hn : nth ts (sel e') with
        | none =>
          rw [hn] at hrt
          have hrt' : nth (retargetList p b inv 0 ts) (sel e') = none := hrt
          cases c with
          | some u =>
            rw [stepTerm_out_none_some hn] at hA
            have hB'' : step (addCallGuards p) (GId.orig b, e) =
                stepTerm (.out inv dst rhs sel (retargetList p b inv 0 ts) (some (GId.orig u)))
                  e' := hB'
            rw [stepTerm_out_none_some hrt'] at hB''
            exact .run1 (u, e') hA hB''
          | none =>
            rw [stepTerm_out_none_none hn] at hA
            have hB'' : step (addCallGuards p) (GId.orig b, e) =
                stepTerm (.out inv dst rhs sel (retargetList p b inv 0 ts) none) e' := hB'
            rw [stepTerm_out_none_none hrt'] at hB''
            exact .halt none hA hB''
        | some t =>
          rw [hn] at hrt
          rw [stepTerm_out_some hn] at hA
          cases hsp : splitEdge p inv t with
          | false =>
            have hrt' : nth (retargetList p b inv 0 ts) (sel e') = some (GId.orig t) := by
              rw [hrt]
              show some (if splitEdge p inv t = true then GId.guard b (0 + sel e')
                else GId.orig t) = _
              rw [hsp]; rfl
            rw [stepTerm_out_some hrt'] at hB'
            exact .run1 (t, upd e' dst (rhs e')) hA hB'
          | true =>
            have hrt' : nth (retargetList p b inv 0 ts) (sel e') =
                some (GId.guard b (sel e')) := by
              rw [hrt]
              show some (if splitEdge p inv t = true then GId.guard b (0 + sel e')
                else GId.orig t) = _
              rw [hsp, Nat.zero_add]; rfl
            rw [stepTerm_out_some hrt'] at hB'
            have hg : addCallGuards p (GId.guard b (sel e')) = some ⟨[], .goto (.orig t)⟩ :=
              guardBlock_split p b (sel e') hb ht hn hsp
            exact .run2 (t, upd e' dst (rhs e')) (GId.guard b (sel e'), upd e' dst (rhs e'))
              hA hB'
              (step_some (q := addCallGuards p)
                (s := (GId.guard b (sel e'), upd e' dst (rhs e'))) hg rfl)

/-- **Exact operational equivalence of critical-edge splitting.** From corresponding start
states, the original and the transformed program have exactly the same terminal behaviours:
the same returned environment, or the same undefined-behaviour/abort outcome (`r = none`). -/
theorem addCallGuards_operational_equivalence (p : Prog) (b : Nat) (e : Env) (r : Res) :
    Halts (step p.cfg) (b, e) r ↔ Halts (step (addCallGuards p)) (GId.orig b, e) r :=
  halts_iff_of_stepMatch (addCallGuards_stepMatch p) (b, e) r


/-! ### Edges, slots and predecessor counting -/

theorem ite_some_none_inv {α : Type} {c : Prop} [Decidable c] {a y : α}
    (h : (if c then some a else none) = some y) : c ∧ a = y := by
  split at h
  · exact ⟨by assumption, Option.some.inj h⟩
  · cases h

theorem goto_succAt_inv {ι : Type} {a y : ι} {s : Option Nat}
    (h : (Term.goto a).succAt s = some y) : s = some 0 ∧ a = y := by
  cases s with
  | none => cases h
  | some i =>
    have h' : (if i = 0 then some a else none) = some y := h
    obtain ⟨hi, ha⟩ := ite_some_none_inv h'
    exact ⟨by rw [hi], ha⟩

theorem switch_succAt_inv {ι : Type} {c : Env → Bool} {a b y : ι} {s : Option Nat}
    (h : (Term.switch c a b).succAt s = some y) :
    (s = some 0 ∧ a = y) ∨ (s = some 1 ∧ b = y) := by
  cases s with
  | none => cases h
  | some i =>
    have h' : (if i = 0 then some a else if i = 1 then some b else none) = some y := h
    split at h'
    · exact .inl ⟨by rw [‹i = 0›], Option.some.inj h'⟩
    · obtain ⟨hi, hb⟩ := ite_some_none_inv h'
      exact .inr ⟨by rw [hi], hb⟩

theorem drop_succAt_inv {ι : Type} {nd : Bool} {g : Env → Option Env} {a y : ι} {u : Option ι}
    {s : Option Nat} (h : (Term.drop nd g a u).succAt s = some y) :
    (s = some 0 ∧ a = y) ∨ (s = none ∧ u = some y) := by
  cases s with
  | none => exact .inr ⟨rfl, h⟩
  | some i =>
    have h' : (if i = 0 then some a else none) = some y := h
    obtain ⟨hi, ha⟩ := ite_some_none_inv h'
    exact .inl ⟨by rw [hi], ha⟩

theorem hit_self (t : Nat) : hit t t = 1 := by simp [hit]

theorem not_two_le_one {a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a + b ≤ 1) : False :=
  absurd (Nat.le_trans (Nat.add_le_add ha hb) h) (by decide)

theorem one_le_countIn {t : Nat} :
    ∀ (ts : List Nat) (i : Nat), nth ts i = some t → 1 ≤ countIn t ts
  | [], i, h => by rw [nth_nil] at h; cases h
  | x :: xs, 0, h => by
    have hx : x = t := Option.some.inj h
    show 1 ≤ hit t x + countIn t xs
    rw [hx, hit_self]
    exact Nat.le_add_right 1 _
  | x :: xs, i + 1, h =>
    Nat.le_trans (one_le_countIn xs i h) (Nat.le_add_left _ _)

theorem countIn_unique {t : Nat} :
    ∀ (ts : List Nat) (i j : Nat), countIn t ts ≤ 1 → nth ts i = some t → nth ts j = some t →
      i = j
  | [], i, _, _, h, _ => by rw [nth_nil] at h; cases h
  | _ :: _, 0, 0, _, _, _ => rfl
  | x :: xs, 0, j + 1, hc, hi, hj => by
    have hx : x = t := Option.some.inj hi
    have h1 : 1 ≤ hit t x := by rw [hx, hit_self]; exact Nat.le_refl 1
    exact (not_two_le_one h1 (one_le_countIn xs j hj) hc).elim
  | x :: xs, i + 1, 0, hc, hi, hj => by
    have hx : x = t := Option.some.inj hj
    have h1 : 1 ≤ hit t x := by rw [hx, hit_self]; exact Nat.le_refl 1
    exact (not_two_le_one h1 (one_le_countIn xs i hi) hc).elim
  | _ :: xs, i + 1, j + 1, hc, hi, hj =>
    congrArg (· + 1) (countIn_unique xs i j (Nat.le_trans (Nat.le_add_left _ _) hc) hi hj)

/-- A successor occurrence contributes at least one to the predecessor count. -/
theorem succAt_one_le_predContrib {t : Nat} (tm : Term Nat) (s : Option Nat)
    (h : tm.succAt s = some t) : 1 ≤ tm.predContrib t := by
  cases tm with
  | goto a =>
    obtain ⟨_, ha⟩ := goto_succAt_inv h
    show 1 ≤ hit t a
    rw [ha, hit_self]; exact Nat.le_refl 1
  | switch c a b =>
    show 1 ≤ hit t a + hit t b
    cases switch_succAt_inv h with
    | inl h1 => rw [h1.2, hit_self]; exact Nat.le_add_right 1 _
    | inr h1 => rw [h1.2, hit_self]; exact Nat.le_add_left 1 _
  | out inv dst rhs sel ts c =>
    show 1 ≤ countIn t ts + hitOpt t c
    cases s with
    | some i => exact Nat.le_trans (one_le_countIn ts i h) (Nat.le_add_right _ _)
    | none =>
      have hc : c = some t := h
      rw [hc]
      show 1 ≤ countIn t ts + hit t t
      rw [hit_self]; exact Nat.le_add_left 1 _
  | drop nd g a u =>
    show 1 ≤ hit t a + hitOpt t u
    cases drop_succAt_inv h with
    | inl h1 => rw [h1.2, hit_self]; exact Nat.le_add_right 1 _
    | inr h1 =>
      rw [h1.2]
      show 1 ≤ hit t a + hit t t
      rw [hit_self]; exact Nat.le_add_left 1 _
  | ret => cases h
  | unreachable => cases h

/-- If a terminator contributes at most one predecessor edge to `t`, the slot is unique. -/
theorem succAt_unique {t : Nat} (tm : Term Nat) (s s' : Option Nat)
    (hc : tm.predContrib t ≤ 1) (h : tm.succAt s = some t) (h' : tm.succAt s' = some t) :
    s = s' := by
  cases tm with
  | goto a =>
    rw [(goto_succAt_inv h).1, (goto_succAt_inv h').1]
  | switch c a b =>
    have hc' : hit t a + hit t b ≤ 1 := hc
    cases switch_succAt_inv h with
    | inl h1 =>
      cases switch_succAt_inv h' with
      | inl h2 => rw [h1.1, h2.1]
      | inr h2 =>
        rw [h1.2, h2.2, hit_self] at hc'
        exact absurd hc' (by decide)
    | inr h1 =>
      cases switch_succAt_inv h' with
      | inl h2 =>
        rw [h1.2, h2.2, hit_self] at hc'
        exact absurd hc' (by decide)
      | inr h2 => rw [h1.1, h2.1]
  | out inv dst rhs sel ts c =>
    have hc' : countIn t ts + hitOpt t c ≤ 1 := hc
    cases s with
    | some i =>
      cases s' with
      | some j =>
        exact congrArg some
          (countIn_unique ts i j (Nat.le_trans (Nat.le_add_right _ _) hc') h h')
      | none =>
        have hcu : c = some t := h'
        rw [hcu] at hc'
        have h1 : 1 ≤ hitOpt t (some t) := by show 1 ≤ hit t t; rw [hit_self]; exact Nat.le_refl 1
        exact (not_two_le_one (one_le_countIn ts i h) h1 hc').elim
    | none =>
      cases s' with
      | some j =>
        have hcu : c = some t := h
        rw [hcu] at hc'
        have h1 : 1 ≤ hitOpt t (some t) := by show 1 ≤ hit t t; rw [hit_self]; exact Nat.le_refl 1
        exact (not_two_le_one (one_le_countIn ts j h') h1 hc').elim
      | none => rfl
  | drop nd g a u =>
    have hc' : hit t a + hitOpt t u ≤ 1 := hc
    cases drop_succAt_inv h with
    | inl h1 =>
      cases drop_succAt_inv h' with
      | inl h2 => rw [h1.1, h2.1]
      | inr h2 =>
        rw [h1.2, h2.2] at hc'
        have hc'' : hit t t + hit t t ≤ 1 := hc'
        rw [hit_self] at hc''
        exact absurd hc'' (by decide)
    | inr h1 =>
      cases drop_succAt_inv h' with
      | inl h2 =>
        rw [h1.2, h2.2] at hc'
        have hc'' : hit t t + hit t t ≤ 1 := hc'
        rw [hit_self] at hc''
        exact absurd hc'' (by decide)
      | inr h2 => rw [h1.1, h2.1]
  | ret => cases h
  | unreachable => cases h

theorem one_le_predCount {t : Nat} :
    ∀ (p : Prog) (b : Nat) (blk : Blk Nat) (s : Option Nat),
      nth p b = some blk → blk.term.succAt s = some t → 1 ≤ predCount p t
  | [], b, _, _, h, _ => by rw [nth_nil] at h; cases h
  | a :: _, 0, blk, s, h, hs => by
    have ha : a = blk := Option.some.inj h
    subst ha
    exact Nat.le_trans (succAt_one_le_predContrib a.term s hs) (Nat.le_add_right _ _)
  | _ :: as, b + 1, blk, s, h, hs =>
    Nat.le_trans (one_le_predCount as b blk s h hs) (Nat.le_add_left _ _)

/-- **Counting to uniqueness.** If `pred_count[t] ≤ 1`, then `t` has at most one incoming edge:
any two (block, slot) pairs with successor `t` coincide. -/
theorem predCount_unique {t : Nat} :
    ∀ (p : Prog) (b b' : Nat) (blk blk' : Blk Nat) (s s' : Option Nat),
      predCount p t ≤ 1 → nth p b = some blk → blk.term.succAt s = some t →
      nth p b' = some blk' → blk'.term.succAt s' = some t → b = b' ∧ s = s'
  | [], b, _, _, _, _, _, _, h, _, _, _ => by rw [nth_nil] at h; cases h
  | a :: _, 0, 0, blk, blk', s, s', hc, h, hs, h', hs' => by
    have ha : a = blk := Option.some.inj h
    have ha' : a = blk' := Option.some.inj h'
    subst ha
    subst ha'
    exact ⟨rfl, succAt_unique a.term s s' (Nat.le_trans (Nat.le_add_right _ _) hc) hs hs'⟩
  | a :: as, 0, b' + 1, blk, blk', s, s', hc, h, hs, h', hs' => by
    have ha : a = blk := Option.some.inj h
    subst ha
    exact (not_two_le_one (succAt_one_le_predContrib a.term s hs)
      (one_le_predCount as b' blk' s' h' hs') hc).elim
  | a :: as, b + 1, 0, blk, blk', s, s', hc, h, hs, h', hs' => by
    have ha : a = blk' := Option.some.inj h'
    subst ha
    exact (not_two_le_one (succAt_one_le_predContrib a.term s' hs')
      (one_le_predCount as b blk s h hs) hc).elim
  | _ :: as, b + 1, b' + 1, blk, blk', s, s', hc, h, hs, h', hs' => by
    obtain ⟨hb, hss⟩ := predCount_unique as b b' blk blk' s s'
      (Nat.le_trans (Nat.le_add_left _ _) hc) h hs h' hs'
    exact ⟨congrArg (· + 1) hb, hss⟩

/-- `Edge q x s y`: block `x` has successor `y` in slot `s`. -/
noncomputable def Edge {ι : Type} (q : Cfg ι) (x : ι) (s : Option Nat) (y : ι) : Prop :=
  ∃ blk, q x = some blk ∧ blk.term.succAt s = some y

/-- `OutEdge q x i y dst`: block `x` ends in an `invoke`/`callbr`-like output-bearing terminator
with destination local `dst`, whose `i`-th normal successor is `y`. -/
noncomputable def OutEdge {ι : Type} (q : Cfg ι) (x : ι) (i : Nat) (y : ι) (dst : Nat) : Prop :=
  ∃ blk rhs sel ts c, q x = some blk ∧ blk.term = .out true dst rhs sel ts c ∧ nth ts i = some y

/-- No output-bearing edge is critical: the target of every such edge has that edge as its only
incoming edge (so in particular `pred_count[target] = 1`). -/
noncomputable def NoCriticalOutEdge {ι : Type} (q : Cfg ι) : Prop :=
  ∀ x i y dst, OutEdge q x i y dst → ∀ x' s', Edge q x' s' y → x' = x ∧ s' = some i

theorem retarget_succAt_guard (p : Prog) (b : Nat) (tm : Term Nat) (s : Option Nat) (b' i' : Nat)
    (h : (retarget p b tm).succAt s = some (GId.guard b' i')) :
    b' = b ∧ s = some i' ∧ ∃ inv dst rhs sel ts c t,
      tm = .out inv dst rhs sel ts c ∧ nth ts i' = some t ∧ splitEdge p inv t = true := by
  cases tm with
  | goto a =>
    have h' : (Term.goto (GId.orig a)).succAt s = some (GId.guard b' i') := h
    cases (goto_succAt_inv h').2
  | switch c a d =>
    have h' : (Term.switch c (GId.orig a) (GId.orig d)).succAt s = some (GId.guard b' i') := h
    cases switch_succAt_inv h' with
    | inl h1 => cases h1.2
    | inr h1 => cases h1.2
  | drop nd g a u =>
    have h' : (Term.drop nd g (GId.orig a) (u.map GId.orig)).succAt s =
        some (GId.guard b' i') := h
    cases drop_succAt_inv h' with
    | inl h1 => cases h1.2
    | inr h1 =>
      cases u with
      | none => cases h1.2
      | some u' =>
        have h2 : some (GId.orig u') = some (GId.guard b' i') := h1.2
        cases h2
  | ret => cases h
  | unreachable => cases h
  | out inv dst rhs sel ts c =>
    cases s with
    | none =>
      have h' : c.map GId.orig = some (GId.guard b' i') := h
      cases c with
      | none => cases h'
      | some u =>
        have h2 : some (GId.orig u) = some (GId.guard b' i') := h'
        cases h2
    | some i =>
      have h' : nth (retargetList p b inv 0 ts) i = some (GId.guard b' i') := h
      rw [nth_retargetList p b inv ts 0 i] at h'
      cases hn : nth ts i with
      | none => rw [hn] at h'; cases h'
      | some t =>
        rw [hn] at h'
        have h2 : (if splitEdge p inv t = true then GId.guard b (0 + i) else GId.orig t) =
            GId.guard b' i' := Option.some.inj h'
        cases hsp : splitEdge p inv t with
        | false => rw [hsp] at h2; cases h2
        | true =>
          rw [hsp] at h2
          have h3 : GId.guard b (0 + i) = GId.guard b' i' := h2
          rw [Nat.zero_add] at h3
          cases h3
          exact ⟨rfl, rfl, inv, dst, rhs, sel, ts, c, t, rfl, hn, hsp⟩

theorem retarget_succAt_orig (p : Prog) (b : Nat) (tm : Term Nat) (s : Option Nat) (t : Nat)
    (h : (retarget p b tm).succAt s = some (GId.orig t)) : tm.succAt s = some t := by
  cases tm with
  | goto a =>
    have h' : (Term.goto (GId.orig a)).succAt s = some (GId.orig t) := h
    obtain ⟨hs, ha⟩ := goto_succAt_inv h'
    cases ha
    rw [hs]; rfl
  | switch c a d =>
    have h' : (Term.switch c (GId.orig a) (GId.orig d)).succAt s = some (GId.orig t) := h
    cases switch_succAt_inv h' with
    | inl h1 => obtain ⟨hs, ha⟩ := h1; cases ha; rw [hs]; rfl
    | inr h1 => obtain ⟨hs, ha⟩ := h1; cases ha; rw [hs]; rfl
  | drop nd g a u =>
    have h' : (Term.drop nd g (GId.orig a) (u.map GId.orig)).succAt s = some (GId.orig t) := h
    cases drop_succAt_inv h' with
    | inl h1 => obtain ⟨hs, ha⟩ := h1; cases ha; rw [hs]; rfl
    | inr h1 =>
      obtain ⟨hs, hu⟩ := h1
      cases u with
      | none => cases hu
      | some u' =>
        have h2 : some (GId.orig u') = some (GId.orig t) := hu
        cases h2
        rw [hs]; rfl
  | ret => cases h
  | unreachable => cases h
  | out inv dst rhs sel ts c =>
    cases s with
    | none =>
      have h' : c.map GId.orig = some (GId.orig t) := h
      cases c with
      | none => cases h'
      | some u =>
        have h2 : some (GId.orig u) = some (GId.orig t) := h'
        cases h2
        rfl
    | some i =>
      have h' : nth (retargetList p b inv 0 ts) i = some (GId.orig t) := h
      rw [nth_retargetList p b inv ts 0 i] at h'
      show nth ts i = some t
      cases hn : nth ts i with
      | none => rw [hn] at h'; cases h'
      | some t0 =>
        rw [hn] at h'
        have h2 : (if splitEdge p inv t0 = true then GId.guard b (0 + i) else GId.orig t0) =
            GId.orig t := Option.some.inj h'
        cases hsp : splitEdge p inv t0 with
        | true => rw [hsp] at h2; cases h2
        | false =>
          rw [hsp] at h2
          have h3 : GId.orig t0 = GId.orig t := h2
          cases h3
          rfl

theorem guardBlock_inv (p : Prog) (b i : Nat) (g : Blk GId) (h : guardBlock p b i = some g) :
    ∃ blk inv dst rhs sel ts c t, nth p b = some blk ∧ blk.term = .out inv dst rhs sel ts c ∧
      nth ts i = some t ∧ splitEdge p inv t = true ∧ g = ⟨[], .goto (.orig t)⟩ := by
  unfold guardBlock at h
  cases hb : nth p b with
  | none => rw [hb] at h; cases h
  | some blk =>
    rw [hb] at h
    cases ht : blk.term with
    | goto a => simp [ht] at h
    | switch c a d => simp [ht] at h
    | drop nd gl a u => simp [ht] at h
    | ret => simp [ht] at h
    | unreachable => simp [ht] at h
    | out inv dst rhs sel ts c =>
      simp only [ht] at h
      cases hn : nth ts i with
      | none => rw [hn] at h; cases h
      | some t =>
        rw [hn] at h
        cases hsp : splitEdge p inv t with
        | false => simp [hsp] at h
        | true =>
          simp [hsp] at h
          exact ⟨blk, inv, dst, rhs, sel, ts, c, t, rfl, ht, hn, hsp, h.symm⟩

theorem addCallGuards_orig_inv (p : Prog) (b : Nat) (g : Blk GId)
    (h : addCallGuards p (GId.orig b) = some g) :
    ∃ blk, nth p b = some blk ∧ g = ⟨blk.stmts, retarget p b blk.term⟩ := by
  have h' : (nth p b).map (fun blk => (⟨blk.stmts, retarget p b blk.term⟩ : Blk GId)) = some g := h
  cases hb : nth p b with
  | none => rw [hb] at h'; cases h'
  | some blk =>
    rw [hb] at h'
    exact ⟨blk, rfl, (Option.some.inj h').symm⟩

theorem splitEdge_true {p : Prog} {inv : Bool} {t : Nat} (h : splitEdge p inv t = true) :
    1 < predCount p t := by
  simp [splitEdge] at h
  exact h.2

theorem splitEdge_inv_false {p : Prog} {t : Nat} (h : splitEdge p true t = false) :
    predCount p t ≤ 1 := by
  simp [splitEdge] at h
  exact h

/-- **Critical-edge freedom after the pass.** In `addCallGuards p`, the target of every
output-bearing `invoke`/`callbr`-like edge has exactly one incoming edge, namely that edge. -/
theorem addCallGuards_noCriticalOutEdge (p : Prog) : NoCriticalOutEdge (addCallGuards p) := by
  intro x i y dst hOut x' s' hEdge
  obtain ⟨gblk, rhs, sel, ts', c', hx, hterm, hy⟩ := hOut
  obtain ⟨blk', hx', hs'⟩ := hEdge
  cases x with
  | guard b j =>
    obtain ⟨_, _, _, _, _, _, _, t, _, _, _, _, hg⟩ := guardBlock_inv p b j gblk hx
    rw [hg] at hterm
    cases hterm
  | orig b =>
    obtain ⟨blk0, hb, hg⟩ := addCallGuards_orig_inv p b gblk hx
    rw [hg] at hterm
    have hterm' : retarget p b blk0.term = Term.out true dst rhs sel ts' c' := hterm
    cases ht0 : blk0.term with
    | goto a => rw [ht0] at hterm'; cases hterm'
    | switch c a d => rw [ht0] at hterm'; cases hterm'
    | drop nd gl a u => rw [ht0] at hterm'; cases hterm'
    | ret => rw [ht0] at hterm'; cases hterm'
    | unreachable => rw [ht0] at hterm'; cases hterm'
    | out inv dst0 rhs0 sel0 ts c =>
      rw [ht0] at hterm'
      have hterm'' : Term.out inv dst0 rhs0 sel0 (retargetList p b inv 0 ts) (c.map GId.orig) =
          Term.out true dst rhs sel ts' c' := hterm'
      injection hterm'' with hinv hdst hrhs hsel hts hc
      subst hinv
      rw [← hts, nth_retargetList p b true ts 0 i] at hy
      cases hn : nth ts i with
      | none => rw [hn] at hy; cases hy
      | some t =>
        rw [hn] at hy
        have hy' : (if splitEdge p true t = true then GId.guard b (0 + i) else GId.orig t) = y :=
          Option.some.inj hy
        have hbi : blk0.term.succAt (some i) = some t := by rw [ht0]; exact hn
        cases hsp : splitEdge p true t with
        | true =>
          rw [hsp] at hy'
          have hy'' : GId.guard b (0 + i) = y := hy'
          rw [Nat.zero_add] at hy''
          subst hy''
          cases x' with
          | guard b2 j2 =>
            obtain ⟨_, _, _, _, _, _, _, t2, _, _, _, _, hg2⟩ := guardBlock_inv p b2 j2 blk' hx'
            rw [hg2] at hs'
            have hs'' : (Term.goto (GId.orig t2)).succAt s' = some (GId.guard b i) := hs'
            cases (goto_succAt_inv hs'').2
          | orig b2 =>
            obtain ⟨blk2, _, hg2⟩ := addCallGuards_orig_inv p b2 blk' hx'
            rw [hg2] at hs'
            obtain ⟨hbb, hss, _⟩ := retarget_succAt_guard p b2 blk2.term s' b i hs'
            exact ⟨by rw [hbb], hss⟩
        | false =>
          rw [hsp] at hy'
          have hy'' : GId.orig t = y := hy'
          subst hy''
          have hle : predCount p t ≤ 1 := splitEdge_inv_false hsp
          cases x' with
          | guard b2 j2 =>
            obtain ⟨_, inv2, _, _, _, _, _, t2, _, _, _, hsp2, hg2⟩ :=
              guardBlock_inv p b2 j2 blk' hx'
            rw [hg2] at hs'
            have hs'' : (Term.goto (GId.orig t2)).succAt s' = some (GId.orig t) := hs'
            have ht2 : GId.orig t2 = GId.orig t := (goto_succAt_inv hs'').2
            cases ht2
            exact absurd (Nat.lt_of_lt_of_le (splitEdge_true hsp2) hle) (by decide)
          | orig b2 =>
            obtain ⟨blk2, hb2, hg2⟩ := addCallGuards_orig_inv p b2 blk' hx'
            rw [hg2] at hs'
            have horig : blk2.term.succAt s' = some t :=
              retarget_succAt_orig p b2 blk2.term s' t hs'
            obtain ⟨h1, h2⟩ := predCount_unique p b2 b blk2 blk0 s' (some i) hle hb2 horig hb hbi
            exact ⟨by rw [h1], h2⟩


/-! ## Part 3. Code-generator model: storing an output at the entry of the destination block

LLVM `invoke` and `callbr` are block terminators, so a code generator cannot place the store of
their result after them in the same block. `rustc` emits the store at the start of each normal
destination block instead. The model below makes that placement explicit: the result lives in a
register `reg`, and every block `y` has a list `entry y` of locals that are overwritten from the
register whenever control *enters* `y`, from whichever predecessor. -/

/-- Low-level machine state: block, environment, and the result register. -/
structure LowSt (ι : Type) where
  pc : ι
  env : Env
  reg : Nat

/-- Forget the register. -/
noncomputable def erase {ι : Type} (l : LowSt ι) : St ι := (l.pc, l.env)

/-- Store the register into every listed local. -/
noncomputable def storeAll (reg : Nat) : List Nat → Env → Env
  | [], e => e
  | d :: ds, e => storeAll reg ds (upd e d reg)

/-- Enter block `t`: run its entry stores from the current register value. -/
noncomputable def enter {ι : Type} (entry : ι → List Nat) (t : ι) (e : Env) (reg : Nat) :
    Outcome (LowSt ι) Res :=
  .running ⟨t, storeAll reg (entry t) e, reg⟩

/-- Terminators whose effect is completed inside their own block behave as in MIR; the register
is left unchanged. -/
noncomputable def lowGeneric {ι : Type} (entry : ι → List Nat) (tm : Term ι) (e : Env) (reg : Nat) :
    Outcome (LowSt ι) Res :=
  match stepTerm tm e with
  | .running s => enter entry s.1 s.2 reg
  | .halt r => .halt r

/-- An `invoke`/`callbr`: on a normal edge the result goes to the register and *no store is
performed in this block*; on the cleanup edge the register is left unchanged. -/
noncomputable def lowInvoke {ι : Type} (entry : ι → List Nat) (rhs sel : Env → Nat) (ts : List ι)
    (c : Option ι) (e : Env) (reg : Nat) : Outcome (LowSt ι) Res :=
  match nth ts (sel e) with
  | some t => enter entry t e (rhs e)
  | none =>
    match c with
    | some u => enter entry u e reg
    | none => .halt none

noncomputable def stepLowTerm {ι : Type} (entry : ι → List Nat) : Term ι → Env → Nat → Outcome (LowSt ι) Res
  | .out true _ rhs sel ts c, e, reg => lowInvoke entry rhs sel ts c e reg
  | .out false dst rhs sel ts c, e, reg => lowGeneric entry (.out false dst rhs sel ts c) e reg
  | .goto t, e, reg => lowGeneric entry (.goto t) e reg
  | .switch c t f, e, reg => lowGeneric entry (.switch c t f) e reg
  | .drop nd g t u, e, reg => lowGeneric entry (.drop nd g t u) e reg
  | .ret, e, reg => lowGeneric entry .ret e reg
  | .unreachable, e, reg => lowGeneric entry .unreachable e reg

noncomputable def stepLow {ι : Type} (q : Cfg ι) (entry : ι → List Nat) (l : LowSt ι) :
    Outcome (LowSt ι) Res :=
  match q l.pc with
  | none => .halt none
  | some b =>
    match execStmts b.stmts l.env with
    | none => .halt none
    | some e' => stepLowTerm entry b.term e' l.reg

/-- Fuel-indexed evaluation of the lowered program. -/
noncomputable def evalLow {ι : Type} (q : Cfg ι) (entry : ι → List Nat) (n : Nat) (pc : ι) (e : Env)
    (reg : Nat) : Outcome (LowSt ι) Res :=
  run (stepLow q entry) n ⟨pc, e, reg⟩

/-- List membership, defined locally. -/
noncomputable def InList (d : Nat) : List Nat → Prop
  | [] => False
  | x :: xs => d = x ∨ InList d xs

/-- `entry` is the placement a code generator is forced into: block `y` stores the register
into `d` on entry exactly when `y` is a normal destination of some `invoke`/`callbr`-like
terminator whose destination local is `d`. -/
noncomputable def IsEntryLowering {ι : Type} (q : Cfg ι) (entry : ι → List Nat) : Prop :=
  ∀ y d, InList d (entry y) ↔ ∃ x i, OutEdge q x i y d

theorem stepLow_none {ι : Type} {q : Cfg ι} {entry : ι → List Nat} {l : LowSt ι}
    (h : q l.pc = none) : stepLow q entry l = .halt none := by
  unfold stepLow
  rw [h]

theorem stepLow_stmts_none {ι : Type} {q : Cfg ι} {entry : ι → List Nat} {l : LowSt ι}
    {b : Blk ι} (h : q l.pc = some b) (h2 : execStmts b.stmts l.env = none) :
    stepLow q entry l = .halt none := by
  unfold stepLow
  rw [h]
  show (match execStmts b.stmts l.env with
    | none => Outcome.halt none
    | some e' => stepLowTerm entry b.term e' l.reg) = .halt none
  rw [h2]

theorem stepLow_some {ι : Type} {q : Cfg ι} {entry : ι → List Nat} {l : LowSt ι} {b : Blk ι}
    {e' : Env} (h : q l.pc = some b) (h2 : execStmts b.stmts l.env = some e') :
    stepLow q entry l = stepLowTerm entry b.term e' l.reg := by
  unfold stepLow
  rw [h]
  show (match execStmts b.stmts l.env with
    | none => Outcome.halt none
    | some e' => stepLowTerm entry b.term e' l.reg) = _
  rw [h2]

theorem storeAll_same (r dst : Nat) :
    ∀ (l : List Nat) (e : Env), (∀ d, InList d l → d = dst) →
      storeAll r l (upd e dst r) = upd e dst r
  | [], _, _ => rfl
  | d :: ds, e, h => by
    have hd : d = dst := h d (Or.inl rfl)
    show storeAll r ds (upd (upd e dst r) d r) = upd e dst r
    rw [hd, upd_upd_same]
    exact storeAll_same r dst ds e (fun d' hd' => h d' (Or.inr hd'))

theorem storeAll_const (r dst : Nat) (l : List Nat) (e : Env)
    (h : ∀ d, InList d l → d = dst) (hne : l ≠ []) : storeAll r l e = upd e dst r := by
  cases l with
  | nil => exact absurd rfl hne
  | cons d ds =>
    have hd : d = dst := h d (Or.inl rfl)
    show storeAll r ds (upd e d r) = upd e dst r
    rw [hd]
    exact storeAll_same r dst ds e (fun d' hd' => h d' (Or.inr hd'))

theorem eq_nil_of_no_member {l : List Nat} (h : ∀ d, ¬ InList d l) : l = [] := by
  cases l with
  | nil => rfl
  | cons d ds => exact absurd (Or.inl rfl) (h d)

/-- Every MIR transition follows an edge of the graph. -/
theorem stepTerm_edge {ι : Type} (tm : Term ι) (e e'' : Env) (t : ι)
    (h : stepTerm tm e = .running (t, e'')) : ∃ s, tm.succAt s = some t := by
  cases tm with
  | goto a =>
    have h' : Outcome.running (a, e) = (Outcome.running (t, e'') : Outcome (St ι) Res) := h
    cases h'
    exact ⟨some 0, rfl⟩
  | switch c a b =>
    have h' : Outcome.running ((if c e = true then a else b), e) =
        (Outcome.running (t, e'') : Outcome (St ι) Res) := h
    cases hc : c e with
    | true => rw [hc] at h'; cases h'; exact ⟨some 0, rfl⟩
    | false => rw [hc] at h'; cases h'; exact ⟨some 1, rfl⟩
  | out inv dst rhs sel ts c =>
    cases hn : nth ts (sel e) with
    | some t0 =>
      rw [stepTerm_out_some hn] at h
      cases h
      exact ⟨some (sel e), hn⟩
    | none =>
      cases c with
      | some u =>
        rw [stepTerm_out_none_some hn] at h
        cases h
        exact ⟨none, rfl⟩
      | none =>
        rw [stepTerm_out_none_none hn] at h
        cases h
  | drop nd g a u =>
    cases hg : g e with
    | some e1 =>
      rw [stepTerm_drop_some hg] at h
      cases h
      exact ⟨some 0, rfl⟩
    | none =>
      cases u with
      | some u' =>
        rw [stepTerm_drop_none_some hg] at h
        cases h
        exact ⟨none, rfl⟩
      | none =>
        rw [stepTerm_drop_none_none hg] at h
        cases h
  | ret => cases h
  | unreachable => cases h

/-- A block entered along an edge that is not an output-bearing normal edge has no entry
stores, provided no output-bearing edge is critical. -/
theorem entry_nil_of_edge {ι : Type} {q : Cfg ι} {entry : ι → List Nat}
    (hq : NoCriticalOutEdge q) (hl : IsEntryLowering q entry) {x y : ι} {blk : Blk ι}
    {s : Option Nat} (hx : q x = some blk) (hs : blk.term.succAt s = some y)
    (hno : ∀ i dst rhs sel ts c, blk.term = .out true dst rhs sel ts c → s = some i → False) :
    entry y = [] := by
  apply eq_nil_of_no_member
  intro d hd
  obtain ⟨x0, i0, hOut⟩ := (hl y d).mp hd
  obtain ⟨hxx, hss⟩ := hq x0 i0 y d hOut x s ⟨blk, hx, hs⟩
  obtain ⟨blk0, rhs, sel, ts, c, hx0, ht0, _⟩ := hOut
  subst hxx
  rw [hx] at hx0
  have hbb : blk = blk0 := Option.some.inj hx0
  subst hbb
  exact hno i0 d rhs sel ts c ht0 hss

/-- A block entered along an output-bearing normal edge stores exactly that edge's destination
local, provided no output-bearing edge is critical. -/
theorem entry_const_of_outEdge {ι : Type} {q : Cfg ι} {entry : ι → List Nat}
    (hq : NoCriticalOutEdge q) (hl : IsEntryLowering q entry) {x y : ι} {blk : Blk ι}
    {dst i : Nat} {rhs sel : Env → Nat} {ts : List ι} {c : Option ι} (hx : q x = some blk)
    (ht : blk.term = .out true dst rhs sel ts c) (hn : nth ts i = some y) :
    (∀ d, InList d (entry y) → d = dst) ∧ entry y ≠ [] := by
  have hOut : OutEdge q x i y dst := ⟨blk, rhs, sel, ts, c, hx, ht, hn⟩
  constructor
  · intro d hd
    obtain ⟨x0, i0, hOut0⟩ := (hl y d).mp hd
    have hEdge : Edge q x (some i) y := ⟨blk, hx, by rw [ht]; exact hn⟩
    obtain ⟨hxx, _⟩ := hq x0 i0 y d hOut0 x (some i) hEdge
    obtain ⟨blk0, rhs0, sel0, ts0, c0, hx0, ht0, _⟩ := hOut0
    subst hxx
    rw [hx] at hx0
    have hbb : blk = blk0 := Option.some.inj hx0
    subst hbb
    rw [ht] at ht0
    injection ht0 with _ hdd
    exact hdd.symm
  · intro hnil
    have hmem : InList dst (entry y) := (hl y dst).mpr ⟨x, i, hOut⟩
    rw [hnil] at hmem
    exact hmem

theorem lowGeneric_erase {ι : Type} (entry : ι → List Nat) (tm : Term ι) (e : Env) (reg : Nat)
    (h : ∀ t e'', stepTerm tm e = .running (t, e'') → entry t = []) :
    stepTerm tm e = (lowGeneric entry tm e reg).map erase := by
  unfold lowGeneric
  cases hst : stepTerm tm e with
  | halt r => rfl
  | running s =>
    obtain ⟨t, e''⟩ := s
    have hnil : entry t = [] := h t e'' hst
    show Outcome.running (t, e'') = (enter entry t e'' reg).map erase
    unfold enter
    rw [hnil]
    rfl

/-- **Soundness of destination-entry stores in the absence of critical output edges.** One step
of the lowered program, with the register forgotten, is exactly one MIR step. -/
theorem stepLow_erase {ι : Type} {q : Cfg ι} {entry : ι → List Nat}
    (hq : NoCriticalOutEdge q) (hl : IsEntryLowering q entry) (l : LowSt ι) :
    step q (erase l) = (stepLow q entry l).map erase := by
  obtain ⟨pc, e, reg⟩ := l
  cases hb : q pc with
  | none =>
    rw [step_none (q := q) (s := erase ⟨pc, e, reg⟩) hb,
      stepLow_none (q := q) (entry := entry) (l := ⟨pc, e, reg⟩) hb]
    rfl
  | some blk =>
    cases hs : execStmts blk.stmts e with
    | none =>
      rw [step_stmts_none (q := q) (s := erase ⟨pc, e, reg⟩) hb hs,
        stepLow_stmts_none (q := q) (entry := entry) (l := ⟨pc, e, reg⟩) hb hs]
      rfl
    | some e' =>
      rw [step_some (q := q) (s := erase ⟨pc, e, reg⟩) hb hs,
        stepLow_some (q := q) (entry := entry) (l := ⟨pc, e, reg⟩) hb hs]
      show stepTerm blk.term e' = (stepLowTerm entry blk.term e' reg).map erase
      -- Targets reached by a terminator that is not `out true ..` have no entry stores.
      have hgen : (∀ dst rhs sel ts c, blk.term ≠ .out true dst rhs sel ts c) →
          ∀ t e'', stepTerm blk.term e' = .running (t, e'') → entry t = [] := by
        intro hne t e'' hst
        obtain ⟨s, hsucc⟩ := stepTerm_edge blk.term e' e'' t hst
        exact entry_nil_of_edge hq hl hb hsucc
          (fun i dst rhs sel ts c htm _ => hne dst rhs sel ts c htm)
      cases ht : blk.term with
      | goto a =>
        rw [ht] at hgen
        exact lowGeneric_erase entry (.goto a) e' reg (hgen (fun _ _ _ _ _ h => by cases h))
      | switch c a b =>
        rw [ht] at hgen
        exact lowGeneric_erase entry (.switch c a b) e' reg
          (hgen (fun _ _ _ _ _ h => by cases h))
      | drop nd g a u =>
        rw [ht] at hgen
        exact lowGeneric_erase entry (.drop nd g a u) e' reg
          (hgen (fun _ _ _ _ _ h => by cases h))
      | ret =>
        rw [ht] at hgen
        exact lowGeneric_erase entry .ret e' reg (hgen (fun _ _ _ _ _ h => by cases h))
      | unreachable =>
        rw [ht] at hgen
        exact lowGeneric_erase entry .unreachable e' reg
          (hgen (fun _ _ _ _ _ h => by cases h))
      | out inv dst rhs sel ts c =>
        cases inv with
        | false =>
          rw [ht] at hgen
          exact lowGeneric_erase entry (.out false dst rhs sel ts c) e' reg
            (hgen (fun _ _ _ _ _ h => by cases h))
        | true =>
          show stepTerm (.out true dst rhs sel ts c) e' =
            (lowInvoke entry rhs sel ts c e' reg).map erase
          unfold lowInvoke
          cases hn : nth ts (sel e') with
          | some t =>
            rw [stepTerm_out_some hn]
            obtain ⟨hall, hne⟩ := entry_const_of_outEdge hq hl hb ht hn
            show Outcome.running (t, upd e' dst (rhs e')) = (enter entry t e' (rhs e')).map erase
            unfold enter
            rw [storeAll_const (rhs e') dst (entry t) e' hall hne]
            rfl
          | none =>
            cases c with
            | none =>
              rw [stepTerm_out_none_none hn]
              rfl
            | some u =>
              rw [stepTerm_out_none_some hn]
              have hnil : entry u = [] :=
                entry_nil_of_edge hq hl hb (s := none) (by rw [ht]; rfl)
                  (fun i _ _ _ _ _ _ hsi => by cases hsi)
              show Outcome.running (u, e') = (enter entry u e' reg).map erase
              unfold enter
              rw [hnil]
              rfl

/-- **Unique immediate predecessor (hence dominance).** Without critical output edges, the
destination `y` of an output-bearing edge out of `x` can only be entered by a step taken from
`x`: every execution that reaches `y` was in `x` one step earlier. -/
theorem outEdge_target_entered_only_from_source {ι : Type} {q : Cfg ι}
    (hq : NoCriticalOutEdge q) {x y : ι} {i dst : Nat} (hOut : OutEdge q x i y dst)
    (s : St ι) (e' : Env) (h : step q s = .running (y, e')) : s.1 = x := by
  cases hb : q s.1 with
  | none => rw [step_none hb] at h; cases h
  | some b =>
    cases hs : execStmts b.stmts s.2 with
    | none => rw [step_stmts_none hb hs] at h; cases h
    | some e1 =>
      rw [step_some hb hs] at h
      obtain ⟨slot, hslot⟩ := stepTerm_edge b.term e1 e' y h
      exact (hq x i y dst hOut s.1 slot ⟨b, hb, hslot⟩).1

/-- The same statement for the output of `addCallGuards`, with no side condition. -/
theorem addCallGuards_outEdge_target_entered_only_from_source (p : Prog) {x y : GId}
    {i dst : Nat} (hOut : OutEdge (addCallGuards p) x i y dst) (s : St GId) (e' : Env)
    (h : step (addCallGuards p) s = .running (y, e')) : s.1 = x :=
  outEdge_target_entered_only_from_source (addCallGuards_noCriticalOutEdge p) hOut s e' h

/-- Lock-step agreement of the lowered program with MIR, for every amount of fuel. -/
theorem lowering_sound {ι : Type} {q : Cfg ι} {entry : ι → List Nat}
    (hq : NoCriticalOutEdge q) (hl : IsEntryLowering q entry) (n : Nat) (pc : ι) (e : Env)
    (reg : Nat) : evalMir q n pc e = (evalLow q entry n pc e reg).map erase :=
  run_map (stepLow_erase hq hl) n ⟨pc, e, reg⟩

/-- **Phi-interference freedom.** Without critical output edges, the observable behaviour of the
lowered program does not depend on the register value that is live on entry: no entry store ever
reads a register value that was not defined along the edge just taken. -/
theorem lowering_register_independent {ι : Type} {q : Cfg ι} {entry : ι → List Nat}
    (hq : NoCriticalOutEdge q) (hl : IsEntryLowering q entry) (n : Nat) (pc : ι) (e : Env)
    (reg reg' : Nat) :
    (evalLow q entry n pc e reg).map erase = (evalLow q entry n pc e reg').map erase := by
  rw [← lowering_sound hq hl n pc e reg, ← lowering_sound hq hl n pc e reg']

/-- **End-to-end statement for `AddCallGuards`.** After critical-edge splitting, *any* placement
of result stores at destination-block entries yields a program with exactly the terminal
behaviours of the original MIR program. -/
theorem addCallGuards_then_lowering_sound (p : Prog) (entry : GId → List Nat)
    (hl : IsEntryLowering (addCallGuards p) entry) (b : Nat) (e : Env) (reg : Nat) (r : Res) :
    Halts (stepLow (addCallGuards p) entry) ⟨GId.orig b, e, reg⟩ r ↔
      Halts (step p.cfg) (b, e) r := by
  have h1 := halts_map_iff (stepLow_erase (addCallGuards_noCriticalOutEdge p) hl)
    ⟨GId.orig b, e, reg⟩ r
  have h2 := addCallGuards_operational_equivalence p b e r
  exact ⟨fun h => h2.mpr (h1.mp h), fun h => h1.mpr (h2.mp h)⟩


/-! ## Part 4. `RemoveUnneededDrops` and `MultipleReturnTerminators` -/

/-- Replace `Drop` of a type that does not need dropping by `goto`. -/
noncomputable def rudTerm {ι : Type} : Term ι → Term ι
  | .drop false _ t _ => .goto t
  | .drop true g t u => .drop true g t u
  | .goto t => .goto t
  | .switch c t e => .switch c t e
  | .out inv dst rhs sel ts c => .out inv dst rhs sel ts c
  | .ret => .ret
  | .unreachable => .unreachable

/-- Model of `RemoveUnneededDrops` (without the follow-up CFG simplification). -/
noncomputable def removeUnneededDrops {ι : Type} (q : Cfg ι) : Cfg ι :=
  fun x => (q x).map (fun b => ⟨b.stmts, rudTerm b.term⟩)

/-- The semantic content of `needs_drop = false`: the type has no drop glue, so dropping is a
no-op that never unwinds. -/
noncomputable def DropsWf {ι : Type} (q : Cfg ι) : Prop :=
  ∀ x b g t u, q x = some b → b.term = .drop false g t u → ∀ e, g e = some e

theorem rudTerm_stepTerm {ι : Type} (tm : Term ι)
    (h : ∀ g t u, tm = .drop false g t u → ∀ e, g e = some e) (e : Env) :
    stepTerm (rudTerm tm) e = stepTerm tm e := by
  cases tm with
  | goto t => rfl
  | switch c t f => rfl
  | out inv dst rhs sel ts c => rfl
  | ret => rfl
  | unreachable => rfl
  | drop nd g t u =>
    cases nd with
    | true => rfl
    | false =>
      rw [stepTerm_drop_some (h g t u rfl e)]
      rfl

theorem removeUnneededDrops_step {ι : Type} {q : Cfg ι} (hwf : DropsWf q) (s : St ι) :
    step (removeUnneededDrops q) s = step q s := by
  cases hb : q s.1 with
  | none =>
    have hb' : removeUnneededDrops q s.1 = none := by
      show (q s.1).map _ = none
      rw [hb]; rfl
    rw [step_none hb, step_none hb']
  | some b =>
    have hb' : removeUnneededDrops q s.1 = some ⟨b.stmts, rudTerm b.term⟩ := by
      show (q s.1).map _ = _
      rw [hb]; rfl
    cases hs : execStmts b.stmts s.2 with
    | none => rw [step_stmts_none hb hs, step_stmts_none hb' hs]
    | some e' =>
      rw [step_some hb hs, step_some hb' hs]
      exact rudTerm_stepTerm b.term (fun g t u ht => hwf s.1 b g t u hb ht) e'

/-- **Soundness of `removeUnneededDrops`, lock-step.** -/
theorem removeUnneededDrops_sound {ι : Type} {q : Cfg ι} (hwf : DropsWf q) (n : Nat) (pc : ι)
    (e : Env) : evalMir (removeUnneededDrops q) n pc e = evalMir q n pc e := by
  have hstep : step (removeUnneededDrops q) = step q := funext (removeUnneededDrops_step hwf)
  show run (step (removeUnneededDrops q)) n (pc, e) = run (step q) n (pc, e)
  rw [hstep]

/-- **Bidirectional soundness of `removeUnneededDrops`.** -/
theorem removeUnneededDrops_bidirectional {ι : Type} {q : Cfg ι} (hwf : DropsWf q) (s : St ι)
    (r : Res) : Halts (step (removeUnneededDrops q)) s r ↔ Halts (step q) s r := by
  have hstep : step (removeUnneededDrops q) = step q := funext (removeUnneededDrops_step hwf)
  rw [hstep]

/-- The unsound variant: remove a `Drop` regardless of `needsDrop`. -/
noncomputable def dropAllTerm {ι : Type} : Term ι → Term ι
  | .drop _ _ t _ => .goto t
  | .goto t => .goto t
  | .switch c t e => .switch c t e
  | .out inv dst rhs sel ts c => .out inv dst rhs sel ts c
  | .ret => .ret
  | .unreachable => .unreachable

noncomputable def removeAllDrops {ι : Type} (q : Cfg ι) : Cfg ι :=
  fun x => (q x).map (fun b => ⟨b.stmts, dropAllTerm b.term⟩)

noncomputable def Term.isDrop {ι : Type} : Term ι → Bool
  | .drop _ _ _ _ => true
  | .goto _ => false
  | .switch _ _ _ => false
  | .out _ _ _ _ _ _ => false
  | .ret => false
  | .unreachable => false

noncomputable def Term.isRet {ι : Type} : Term ι → Bool
  | .ret => true
  | .goto _ => false
  | .switch _ _ _ => false
  | .out _ _ _ _ _ _ => false
  | .drop _ _ _ _ => false
  | .unreachable => false

/-- A block with no statements and a `return` terminator. -/
noncomputable def isSimpleReturn {ι : Type} (q : Cfg ι) (t : ι) : Bool :=
  match q t with
  | some b =>
    match b.stmts with
    | [] => b.term.isRet
    | _ :: _ => false
  | none => false

/-- Replace `goto` to a simple return block by `return`. -/
noncomputable def mrtTerm {ι : Type} (q : Cfg ι) : Term ι → Term ι
  | .goto t => if isSimpleReturn q t = true then .ret else .goto t
  | .switch c t e => .switch c t e
  | .out inv dst rhs sel ts c => .out inv dst rhs sel ts c
  | .drop nd g t u => .drop nd g t u
  | .ret => .ret
  | .unreachable => .unreachable

/-- Model of `MultipleReturnTerminators` (without the follow-up dead-block removal). The set of
simple return blocks is computed on the *input* graph, as in `rustc`. -/
noncomputable def multipleReturnTerminators {ι : Type} (q : Cfg ι) : Cfg ι :=
  fun x => (q x).map (fun b => ⟨b.stmts, mrtTerm q b.term⟩)

theorem isRet_inv {ι : Type} {tm : Term ι} (h : tm.isRet = true) : tm = .ret := by
  cases tm with
  | ret => rfl
  | goto t => cases h
  | switch c t e => cases h
  | out inv dst rhs sel ts c => cases h
  | drop nd g t u => cases h
  | unreachable => cases h

theorem isSimpleReturn_inv {ι : Type} {q : Cfg ι} {t : ι} (h : isSimpleReturn q t = true) :
    ∃ b, q t = some b ∧ b.stmts = [] ∧ b.term = .ret := by
  unfold isSimpleReturn at h
  cases hb : q t with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    cases hs : b.stmts with
    | cons x xs => simp [hs] at h
    | nil =>
      simp [hs] at h
      exact ⟨b, rfl, hs, isRet_inv h⟩

theorem stepMatch_same {σ ρ : Type} {stepA stepB : σ → Outcome σ ρ} {a : σ} {o : Outcome σ ρ}
    (hA : stepA a = o) (hB : stepB a = o) : StepMatch stepA stepB id a := by
  cases o with
  | running a' => exact .run1 a' hA hB
  | halt r => exact .halt r hA hB

/-- One step of the transformed program is one step of the original, or two when a `goto` to a
simple return block was replaced by `return`. -/
theorem multipleReturnTerminators_stepMatch {ι : Type} (q : Cfg ι) (a : St ι) :
    StepMatch (step (multipleReturnTerminators q)) (step q) id a := by
  cases hb : q a.1 with
  | none =>
    have hb' : multipleReturnTerminators q a.1 = none := by
      show (q a.1).map _ = none
      rw [hb]; rfl
    exact stepMatch_same (step_none hb') (step_none hb)
  | some b =>
    have hb' : multipleReturnTerminators q a.1 = some ⟨b.stmts, mrtTerm q b.term⟩ := by
      show (q a.1).map _ = _
      rw [hb]; rfl
    cases hs : execStmts b.stmts a.2 with
    | none => exact stepMatch_same (step_stmts_none hb' hs) (step_stmts_none hb hs)
    | some e' =>
      have hA : step (multipleReturnTerminators q) a = stepTerm (mrtTerm q b.term) e' :=
        step_some hb' hs
      have hB : step q a = stepTerm b.term e' := step_some hb hs
      cases ht : b.term with
      | switch c t f => rw [ht] at hA hB; exact stepMatch_same hA hB
      | out inv dst rhs sel ts c => rw [ht] at hA hB; exact stepMatch_same hA hB
      | drop nd g t u => rw [ht] at hA hB; exact stepMatch_same hA hB
      | ret => rw [ht] at hA hB; exact stepMatch_same hA hB
      | unreachable => rw [ht] at hA hB; exact stepMatch_same hA hB
      | goto t =>
        rw [ht] at hA hB
        cases hsr : isSimpleReturn q t with
        | false =>
          have hA' : step (multipleReturnTerminators q) a = stepTerm (.goto t) e' := by
            rw [hA]
            show stepTerm (if isSimpleReturn q t = true then Term.ret else Term.goto t) e' = _
            rw [hsr]; rfl
          exact stepMatch_same hA' hB
        | true =>
          have hA' : step (multipleReturnTerminators q) a = .halt (some e') := by
            rw [hA]
            show stepTerm (if isSimpleReturn q t = true then Term.ret else Term.goto t) e' = _
            rw [hsr]; rfl
          obtain ⟨tb, htb, hst, htt⟩ := isSimpleReturn_inv hsr
          have hB₂ : step q (t, e') = .halt (some e') := by
            rw [step_some (q := q) (s := (t, e')) (e' := e') htb (by rw [hst]; rfl), htt]
            rfl
          exact .halt2 (some e') (t, e') hA' hB hB₂

/-- **Bidirectional soundness of `multipleReturnTerminators`.** -/
theorem multipleReturnTerminators_bidirectional {ι : Type} (q : Cfg ι) (s : St ι) (r : Res) :
    Halts (step (multipleReturnTerminators q)) s r ↔ Halts (step q) s r :=
  halts_iff_of_stepMatch (multipleReturnTerminators_stepMatch q) s r

/-- The unsound variant: treat any block ending in `return` as duplicable, ignoring its
statements. -/
noncomputable def endsInReturn {ι : Type} (q : Cfg ι) (t : ι) : Bool :=
  match q t with
  | some b => b.term.isRet
  | none => false

noncomputable def mrtAnyTerm {ι : Type} (q : Cfg ι) : Term ι → Term ι
  | .goto t => if endsInReturn q t = true then .ret else .goto t
  | .switch c t e => .switch c t e
  | .out inv dst rhs sel ts c => .out inv dst rhs sel ts c
  | .drop nd g t u => .drop nd g t u
  | .ret => .ret
  | .unreachable => .unreachable

noncomputable def duplicateAnyReturn {ι : Type} (q : Cfg ι) : Cfg ι :=
  fun x => (q x).map (fun b => ⟨b.stmts, mrtAnyTerm q b.term⟩)

/-! ## Part 5. `ElaborateBoxDerefs`

A separate, smaller model with a heap. A `Box<T>` value is `Val.box a`; a `*const T` value is
`Val.raw a`. Address `0` is null and `heap a = none` means "not live". -/

namespace BoxModel

inductive Val where
  | int (n : Nat)
  | box (addr : Nat)
  | raw (addr : Nat)

structure Store where
  loc : Nat → Val
  heap : Nat → Option Val

noncomputable def setLoc (σ : Store) (x : Nat) (v : Val) : Store :=
  ⟨fun y => if y = x then v else σ.loc y, σ.heap⟩

/-- Dereferenceability check plus load: `none` when the address is null or not live. -/
noncomputable def load (σ : Store) (a : Nat) : Option Val := if a = 0 then none else σ.heap a

/-- Statements; each has a destination local and a source local.

* `derefBox dst src`: `dst = copy (*src)` with `src: Box<T>` (only legal before the pass).
* `addrOfBox dst src`: `dst = &raw const (*src)` with `src: Box<T>` (only legal before the pass);
  evaluating the place `*src` requires `src` to be a valid `Box<T>` even though nothing is read.
* `boxDerefTransmute tmp src`: `tmp = copy (src.0) as *const T (BoxDerefTransmute)`; UB unless
  the input is valid as `Box<T>`.
* `transmute tmp src`: the same reinterpretation as a plain `Transmute`, with no such check.
* `derefRaw dst src`: `dst = copy (*src)` with `src: *const T`.
* `addrOfRaw dst src`: `dst = &raw const (*src)` with `src: *const T`; never UB. -/
inductive Stmt where
  | derefBox (dst src : Nat)
  | addrOfBox (dst src : Nat)
  | boxDerefTransmute (tmp src : Nat)
  | transmute (tmp src : Nat)
  | derefRaw (dst src : Nat)
  | addrOfRaw (dst src : Nat)

/-- Destination local of a statement. -/
noncomputable def Stmt.dst : Stmt → Nat
  | .derefBox d _ => d
  | .addrOfBox d _ => d
  | .boxDerefTransmute d _ => d
  | .transmute d _ => d
  | .derefRaw d _ => d
  | .addrOfRaw d _ => d

/-- Source local of a statement. -/
noncomputable def Stmt.src : Stmt → Nat
  | .derefBox _ s => s
  | .addrOfBox _ s => s
  | .boxDerefTransmute _ s => s
  | .transmute _ s => s
  | .derefRaw _ s => s
  | .addrOfRaw _ s => s

/-- The value a statement stores into its destination, as a function of the value of its source
local and of the checked-load function; `none` is undefined behaviour. -/
noncomputable def result : Stmt → Val → (Nat → Option Val) → Option Val
  | .derefBox _ _, .box a, ld => ld a
  | .derefBox _ _, .int _, _ => none
  | .derefBox _ _, .raw _, _ => none
  | .addrOfBox _ _, .box a, ld => (ld a).map (fun _ => Val.raw a)
  | .addrOfBox _ _, .int _, _ => none
  | .addrOfBox _ _, .raw _, _ => none
  | .boxDerefTransmute _ _, .box a, ld => (ld a).map (fun _ => Val.raw a)
  | .boxDerefTransmute _ _, .int _, _ => none
  | .boxDerefTransmute _ _, .raw _, _ => none
  | .transmute _ _, .box a, _ => some (Val.raw a)
  | .transmute _ _, .int _, _ => none
  | .transmute _ _, .raw _, _ => none
  | .derefRaw _ _, .raw a, ld => ld a
  | .derefRaw _ _, .int _, _ => none
  | .derefRaw _ _, .box _, _ => none
  | .addrOfRaw _ _, .raw a, _ => some (Val.raw a)
  | .addrOfRaw _ _, .int _, _ => none
  | .addrOfRaw _ _, .box _, _ => none

noncomputable def exec (s : Stmt) (σ : Store) : Option Store :=
  (result s (σ.loc s.src) (load σ)).map (setLoc σ s.dst)

noncomputable def execList : List Stmt → Store → Option Store
  | [], σ => some σ
  | s :: ss, σ =>
    match exec s σ with
    | some σ' => execList ss σ'
    | none => none

/-- `ElaborateBoxDerefs` on one statement, using the temporary `tmp`. -/
noncomputable def elaborate (tmp : Nat) : Stmt → List Stmt
  | .derefBox dst src => [.boxDerefTransmute tmp src, .derefRaw dst tmp]
  | .addrOfBox dst src => [.boxDerefTransmute tmp src, .addrOfRaw dst tmp]
  | .boxDerefTransmute t s => [.boxDerefTransmute t s]
  | .transmute t s => [.transmute t s]
  | .derefRaw d s => [.derefRaw d s]
  | .addrOfRaw d s => [.addrOfRaw d s]

/-- The same elaboration using a plain `Transmute` (no `Box<T>`-validity check on the cast). -/
noncomputable def elaborateWithPlainTransmute (tmp : Nat) : Stmt → List Stmt
  | .derefBox dst src => [.transmute tmp src, .derefRaw dst tmp]
  | .addrOfBox dst src => [.transmute tmp src, .addrOfRaw dst tmp]
  | .boxDerefTransmute t s => [.boxDerefTransmute t s]
  | .transmute t s => [.transmute t s]
  | .derefRaw d s => [.derefRaw d s]
  | .addrOfRaw d s => [.addrOfRaw d s]

/-- `ElaborateBoxDerefs` on a statement list. -/
noncomputable def elaborateList (tmp : Nat) : List Stmt → List Stmt
  | [] => []
  | s :: ss => elaborate tmp s ++ elaborateList tmp ss

/-- Stores that agree on the heap and on every local except `tmp`. -/
noncomputable def AgreeExcept (tmp : Nat) (σ τ : Store) : Prop :=
  σ.heap = τ.heap ∧ ∀ x, x ≠ tmp → σ.loc x = τ.loc x

/-- Both undefined, or both defined and related. -/
noncomputable def OptRel {α : Type} (R : α → α → Prop) : Option α → Option α → Prop
  | none, none => True
  | some a, some b => R a b
  | none, some _ => False
  | some _, none => False

/-- `tmp` does not occur in `s`. -/
noncomputable def Fresh (tmp : Nat) (s : Stmt) : Prop := s.dst ≠ tmp ∧ s.src ≠ tmp

/-- `tmp` does not occur in any statement of the list. -/
noncomputable def FreshList (tmp : Nat) : List Stmt → Prop
  | [] => True
  | s :: ss => Fresh tmp s ∧ FreshList tmp ss

theorem setLoc_loc_self (σ : Store) (x : Nat) (v : Val) : (setLoc σ x v).loc x = v := by
  show (if x = x then v else σ.loc x) = v
  simp

theorem setLoc_loc_ne (σ : Store) {x y : Nat} (v : Val) (h : y ≠ x) :
    (setLoc σ x v).loc y = σ.loc y := by
  show (if y = x then v else σ.loc y) = σ.loc y
  simp [h]

theorem load_setLoc (σ : Store) (x : Nat) (v : Val) : load (setLoc σ x v) = load σ := rfl

theorem agree_refl (tmp : Nat) (σ : Store) : AgreeExcept tmp σ σ := ⟨rfl, fun _ _ => rfl⟩

theorem agree_trans {tmp : Nat} {σ τ υ : Store} (h₁ : AgreeExcept tmp σ τ)
    (h₂ : AgreeExcept tmp τ υ) : AgreeExcept tmp σ υ :=
  ⟨h₁.1.trans h₂.1, fun x hx => (h₁.2 x hx).trans (h₂.2 x hx)⟩

theorem agree_setLoc {tmp : Nat} {σ τ : Store} (h : AgreeExcept tmp σ τ) (x : Nat) (v : Val) :
    AgreeExcept tmp (setLoc σ x v) (setLoc τ x v) := by
  refine ⟨h.1, fun y hy => ?_⟩
  by_cases hyx : y = x
  · rw [hyx, setLoc_loc_self, setLoc_loc_self]
  · rw [setLoc_loc_ne _ _ hyx, setLoc_loc_ne _ _ hyx]
    exact h.2 y hy

theorem agree_setLoc_tmp (tmp : Nat) (σ : Store) (v : Val) :
    AgreeExcept tmp σ (setLoc σ tmp v) :=
  ⟨rfl, fun _ hy => (setLoc_loc_ne σ v hy).symm⟩

theorem agree_load {tmp : Nat} {σ τ : Store} (h : AgreeExcept tmp σ τ) : load σ = load τ := by
  funext a
  show (if a = 0 then none else σ.heap a) = (if a = 0 then none else τ.heap a)
  rw [h.1]

theorem optRel_trans {tmp : Nat} {a b c : Option Store} (h₁ : OptRel (AgreeExcept tmp) a b)
    (h₂ : OptRel (AgreeExcept tmp) b c) : OptRel (AgreeExcept tmp) a c := by
  cases a with
  | none =>
    cases b with
    | none => exact h₂
    | some _ => exact h₁.elim
  | some x =>
    cases b with
    | none => exact h₁.elim
    | some y =>
      cases c with
      | none => exact h₂.elim
      | some z => exact agree_trans h₁ h₂

/-- A statement that does not mention `tmp` cannot tell apart stores that differ only at `tmp`. -/
theorem exec_congr {tmp : Nat} {s : Stmt} (hf : Fresh tmp s) {σ τ : Store}
    (h : AgreeExcept tmp σ τ) : OptRel (AgreeExcept tmp) (exec s σ) (exec s τ) := by
  unfold exec
  rw [← h.2 s.src hf.2, ← agree_load h]
  cases result s (σ.loc s.src) (load σ) with
  | none => trivial
  | some v => exact agree_setLoc h s.dst v

/-- **Bidirectional soundness of `elaborate` on a single statement.** The elaborated sequence is
undefined exactly when the original statement is, and otherwise produces the same store up to
the value of `tmp`. (No freshness assumption is needed for a single statement started in one
store; it is needed to compose statements, see `elaborateList_sound`.) -/
theorem elaborate_sound (tmp : Nat) (s : Stmt) (σ : Store) :
    OptRel (AgreeExcept tmp) (exec s σ) (execList (elaborate tmp s) σ) := by
  have hsame : ∀ s' : Stmt, OptRel (AgreeExcept tmp) (exec s' σ) (execList [s'] σ) := by
    intro s'
    show OptRel _ (exec s' σ) (match exec s' σ with
      | some σ' => some σ'
      | none => none)
    cases exec s' σ with
    | none => trivial
    | some τ => exact agree_refl tmp τ
  cases s with
  | boxDerefTransmute t src => exact hsame _
  | transmute t src => exact hsame _
  | derefRaw d src => exact hsame _
  | addrOfRaw d src => exact hsame _
  | derefBox dst src =>
    cases hv : σ.loc src with
    | int n => simp [exec, execList, elaborate, result, Stmt.src, Stmt.dst, hv, OptRel]
    | raw a => simp [exec, execList, elaborate, result, Stmt.src, Stmt.dst, hv, OptRel]
    | box a =>
      cases hl : load σ a with
      | none => simp [exec, execList, elaborate, result, Stmt.src, Stmt.dst, hv, hl, OptRel]
      | some v =>
        simp [exec, execList, elaborate, result, Stmt.src, Stmt.dst, hv, hl, OptRel,
          setLoc_loc_self, load_setLoc]
        exact agree_setLoc (agree_setLoc_tmp tmp σ (Val.raw a)) dst v
  | addrOfBox dst src =>
    cases hv : σ.loc src with
    | int n => simp [exec, execList, elaborate, result, Stmt.src, Stmt.dst, hv, OptRel]
    | raw a => simp [exec, execList, elaborate, result, Stmt.src, Stmt.dst, hv, OptRel]
    | box a =>
      cases hl : load σ a with
      | none => simp [exec, execList, elaborate, result, Stmt.src, Stmt.dst, hv, hl, OptRel]
      | some v =>
        simp [exec, execList, elaborate, result, Stmt.src, Stmt.dst, hv, hl, OptRel,
          setLoc_loc_self]
        exact agree_setLoc (agree_setLoc_tmp tmp σ (Val.raw a)) dst (Val.raw a)

/-- **`ElaborateBoxDerefs` never changes definedness.** -/
theorem elaborate_ub_iff (tmp : Nat) (s : Stmt) (σ : Store) :
    exec s σ = none ↔ execList (elaborate tmp s) σ = none := by
  have h := elaborate_sound tmp s σ
  cases h1 : exec s σ with
  | none =>
    cases h2 : execList (elaborate tmp s) σ with
    | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | some τ => rw [h1, h2] at h; exact h.elim
  | some τ =>
    cases h2 : execList (elaborate tmp s) σ with
    | none => rw [h1, h2] at h; exact h.elim
    | some τ' => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem execList_append (l₁ l₂ : List Stmt) (σ : Store) :
    execList (l₁ ++ l₂) σ =
      (match execList l₁ σ with
        | some σ' => execList l₂ σ'
        | none => none) := by
  induction l₁ generalizing σ with
  | nil => rfl
  | cons s ss ih =>
    show (match exec s σ with
      | some σ' => execList (ss ++ l₂) σ'
      | none => none) = (match (match exec s σ with
        | some σ' => execList ss σ'
        | none => none) with
        | some σ' => execList l₂ σ'
        | none => none)
    cases exec s σ with
    | none => rfl
    | some σ' => exact ih σ'

/-- **Bidirectional soundness of `ElaborateBoxDerefs` on straight-line code.** If the temporary
is fresh for the whole list, then running the original list and running the elaborated list from
stores that agree except at `tmp` are both undefined, or both defined with final stores that
agree except at `tmp`. -/
theorem elaborateList_sound (tmp : Nat) :
    ∀ (l : List Stmt), FreshList tmp l → ∀ (σ τ : Store), AgreeExcept tmp σ τ →
      OptRel (AgreeExcept tmp) (execList l σ) (execList (elaborateList tmp l) τ)
  | [], _, σ, τ, h => h
  | s :: ss, hf, σ, τ, h => by
    have hstep : OptRel (AgreeExcept tmp) (exec s σ) (execList (elaborate tmp s) τ) :=
      optRel_trans (exec_congr hf.1 h) (elaborate_sound tmp s τ)
    show OptRel _ (match exec s σ with
      | some σ' => execList ss σ'
      | none => none) (execList (elaborate tmp s ++ elaborateList tmp ss) τ)
    rw [execList_append]
    cases h1 : exec s σ with
    | none =>
      cases h2 : execList (elaborate tmp s) τ with
      | none => trivial
      | some τ' => rw [h1, h2] at hstep; exact hstep.elim
    | some σ' =>
      cases h2 : execList (elaborate tmp s) τ with
      | none => rw [h1, h2] at hstep; exact hstep.elim
      | some τ' =>
        rw [h1, h2] at hstep
        exact elaborateList_sound tmp ss hf.2 σ' τ' hstep

/-- A dangling `Box` used only in a place expression: undefined before elaboration, undefined
after elaboration with `BoxDerefTransmute`, but *defined* after elaboration with a plain
`Transmute`. This is the undefined behaviour that the dedicated cast kind preserves. -/
theorem plain_transmute_loses_box_validity_ub :
    let σ : Store := ⟨fun _ => .box 7, fun _ => none⟩
    exec (.addrOfBox 0 1) σ = none ∧
    execList (elaborate 9 (.addrOfBox 0 1)) σ = none ∧
    (execList (elaborateWithPlainTransmute 9 (.addrOfBox 0 1)) σ).isSome = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- For a *load*, by contrast, the plain-`Transmute` elaboration is also sound in this model:
the raw-pointer load performs the same dereferenceability check. -/
theorem plain_transmute_sound_for_loads (tmp dst src : Nat) (σ : Store) :
    OptRel (AgreeExcept tmp) (exec (.derefBox dst src) σ)
      (execList (elaborateWithPlainTransmute tmp (.derefBox dst src)) σ) := by
  cases hv : σ.loc src with
  | int n =>
    simp [exec, execList, elaborateWithPlainTransmute, result, Stmt.src, Stmt.dst, hv, OptRel]
  | raw a =>
    simp [exec, execList, elaborateWithPlainTransmute, result, Stmt.src, Stmt.dst, hv, OptRel]
  | box a =>
    cases hl : load σ a with
    | none =>
      simp [exec, execList, elaborateWithPlainTransmute, result, Stmt.src, Stmt.dst, hv, hl,
        OptRel, setLoc_loc_self, load_setLoc]
    | some v =>
      simp [exec, execList, elaborateWithPlainTransmute, result, Stmt.src, Stmt.dst, hv, hl,
        OptRel, setLoc_loc_self, load_setLoc]
      exact agree_setLoc (agree_setLoc_tmp tmp σ (Val.raw a)) dst v

end BoxModel

/-! ## Part 6. Constructive counterexamples and non-vacuity witnesses

All statements below are closed and are proved by evaluation in the kernel. -/

/-- Observe local `_0` of a normal return. -/
noncomputable def observe {σ : Type} : Outcome σ Res → Option Nat
  | .halt (some e) => some (e 0)
  | .halt none => none
  | .running _ => none

/-- All locals zero. -/
noncomputable def env0 : Env := fun _ => 0

/-- Local `_1` (the branch condition) set, everything else zero. -/
noncomputable def envTakeCall : Env := fun x => if x = 1 then 1 else 0

/-- Shape of the optimized MIR `rustc` produces for

```
let _g = Guard(1); let y = if c { opaque(1) } else { 7 }; y
```

with the guard's drops omitted:

```
bb0: switchInt(_1) -> [0: bb2, otherwise: bb1]
bb1: _3 = opaque(1) -> [return: bb3, unwind: bb4]     -- unwinding call
bb2: _3 = const 7; goto -> bb3
bb3: _0 = copy _3; return
bb4 (cleanup): ...
```

The edge `bb1 -> bb3` is critical: `bb1` has two successors and `bb3` has two predecessors. -/
noncomputable def ce1Prog : Prog :=
  [ ⟨[], .switch (fun e => decide (e 1 ≠ 0)) 1 2⟩,
    ⟨[], .out true 3 (fun _ => 42) (fun e => e 9) [3] (some 4)⟩,
    ⟨[fun e => some (upd e 3 7)], .goto 3⟩,
    ⟨[fun e => some (upd e 0 (e 3))], .ret⟩,
    ⟨[], .unreachable⟩ ]

/-- The store placement a code generator is forced into for the *unsplit* program: the result of
the `invoke` in `bb1` is stored into `_3` at the entry of `bb3`. -/
noncomputable def ce1Entry : Nat → List Nat
  | 3 => [3]
  | _ => []

theorem ce1Entry_ne {y : Nat} (h : y ≠ 3) : ce1Entry y = [] := by
  unfold ce1Entry
  split
  · exact absurd rfl h
  · rfl

theorem ce1_isEntryLowering : IsEntryLowering ce1Prog.cfg ce1Entry := by
  intro y d
  constructor
  · intro h
    by_cases hy : y = 3
    · subst hy
      have hd : d = 3 := by
        cases (h : d = 3 ∨ False) with
        | inl h => exact h
        | inr h => exact h.elim
      subst hd
      exact ⟨1, 0, ⟨[], .out true 3 (fun _ => 42) (fun e => e 9) [3] (some 4)⟩, _, _, _, _,
        rfl, rfl, rfl⟩
    · rw [ce1Entry_ne hy] at h
      exact h.elim
  · intro ⟨x, i, blk, rhs, sel, ts, c, hx, ht, hn⟩
    have hx' : nth ce1Prog x = some blk := hx
    cases x with
    | zero =>
      have hb := Option.some.inj hx'
      subst hb
      cases ht
    | succ x =>
      cases x with
      | zero =>
        have hb := Option.some.inj hx'
        subst hb
        have ht' : Term.out true 3 (fun _ => 42) (fun e => e 9) [3] (some 4) =
            Term.out true d rhs sel ts c := ht
        injection ht' with _ hd _ _ hts _
        subst hd
        subst hts
        cases i with
        | zero =>
          have hy : 3 = y := Option.some.inj hn
          subst hy
          exact Or.inl rfl
        | succ i =>
          have hn' : nth ([] : List Nat) i = some y := hn
          rw [nth_nil] at hn'
          cases hn'
      | succ x =>
        cases x with
        | zero =>
          have hb := Option.some.inj hx'
          subst hb
          cases ht
        | succ x =>
          cases x with
          | zero =>
            have hb := Option.some.inj hx'
            subst hb
            cases ht
          | succ x =>
            cases x with
            | zero =>
              have hb := Option.some.inj hx'
              subst hb
              cases ht
            | succ x =>
              have hx'' : nth ([] : List (Blk Nat)) x = some blk := hx'
              rw [nth_nil] at hx''
              cases hx''

/-- **Counterexample 1 (unwinding call).** On the unsplit program the forced store placement is
a valid entry lowering, the output edge is critical, and along the *other* predecessor
(`bb2`, which wrote `_3 = 7`) the entry store at `bb3` overwrites `_3` with the stale register:
MIR returns `7`, the lowered program returns `0`. -/
theorem ce1_unsplit_call_or_callbr_critical_edge_clobbers_other_predecessor_value :
    IsEntryLowering ce1Prog.cfg ce1Entry ∧
    ¬ NoCriticalOutEdge ce1Prog.cfg ∧
    observe (evalMir ce1Prog.cfg 3 0 env0) = some 7 ∧
    observe (evalLow ce1Prog.cfg ce1Entry 3 0 env0 0) = some 0 := by
  refine ⟨ce1_isEntryLowering, ?_, rfl, rfl⟩
  intro h
  have h2 := h 1 0 3 3
    ⟨⟨[], .out true 3 (fun _ => 42) (fun e => e 9) [3] (some 4)⟩, _, _, _, _, rfl, rfl, rfl⟩
    2 (some 0) ⟨⟨[fun e => some (upd e 3 7)], .goto 3⟩, rfl, rfl⟩
  exact absurd h2.1 (by decide)

/-- Store placement for the *split* program: the result store sits at the entry of the guard
block created for slot `0` of `bb1`, and nowhere else. -/
noncomputable def ce1EntryAfter : GId → List Nat
  | .guard 1 0 => [3]
  | _ => []

theorem ce1_after_split_isEntryLowering :
    IsEntryLowering (addCallGuards ce1Prog) ce1EntryAfter := by
  intro y d
  constructor
  · intro h
    have key : y = GId.guard 1 0 ∧ d = 3 := by
      cases y with
      | orig b => exact (h : False).elim
      | guard b j =>
        cases b with
        | zero => exact (h : False).elim
        | succ b =>
          cases b with
          | succ b => exact (h : False).elim
          | zero =>
            cases j with
            | succ j => exact (h : False).elim
            | zero =>
              cases (h : d = 3 ∨ False) with
              | inl h => exact ⟨rfl, h⟩
              | inr h => exact h.elim
    obtain ⟨hy, hd⟩ := key
    subst hy
    subst hd
    exact ⟨GId.orig 1, 0,
      ⟨[], retarget ce1Prog 1 (.out true 3 (fun _ => 42) (fun e => e 9) [3] (some 4))⟩,
      _, _, _, _, rfl, rfl, rfl⟩
  · intro ⟨x, i, blk, rhs, sel, ts, c, hx, ht, hn⟩
    cases x with
    | guard b j =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg⟩ := guardBlock_inv ce1Prog b j blk hx
      rw [hg] at ht
      cases ht
    | orig b =>
      obtain ⟨blk0, hb, hg⟩ := addCallGuards_orig_inv ce1Prog b blk hx
      rw [hg] at ht
      have ht' : retarget ce1Prog b blk0.term = Term.out true d rhs sel ts c := ht
      cases b with
      | zero =>
        have hb0 := Option.some.inj hb
        subst hb0
        cases ht'
      | succ b =>
        cases b with
        | zero =>
          have hb0 := Option.some.inj hb
          subst hb0
          have ht'' : Term.out true 3 (fun _ => 42) (fun e => e 9)
              (retargetList ce1Prog 1 true 0 [3]) (some (GId.orig 4)) =
              Term.out true d rhs sel ts c := ht'
          injection ht'' with _ hd _ _ hts _
          subst hd
          subst hts
          cases i with
          | zero =>
            have hy : GId.guard 1 0 = y := Option.some.inj hn
            subst hy
            exact Or.inl rfl
          | succ i =>
            have hn' : nth ([] : List GId) i = some y := hn
            rw [nth_nil] at hn'
            cases hn'
        | succ b =>
          cases b with
          | zero =>
            have hb0 := Option.some.inj hb
            subst hb0
            cases ht'
          | succ b =>
            cases b with
            | zero =>
              have hb0 := Option.some.inj hb
              subst hb0
              cases ht'
            | succ b =>
              cases b with
              | zero =>
                have hb0 := Option.some.inj hb
                subst hb0
                cases ht'
              | succ b =>
                have hb' : nth ([] : List (Blk Nat)) b = some blk0 := hb
                rw [nth_nil] at hb'
                cases hb'

/-- **Non-vacuity witness.** For the same program after `addCallGuards`, a valid store
placement exists and the lowered program agrees with MIR on both paths (the path through the
other predecessor returns `7`; the path through the call returns the call's result `42`). -/
theorem ce1_after_split_lowering_agrees :
    IsEntryLowering (addCallGuards ce1Prog) ce1EntryAfter ∧
    observe (evalMir ce1Prog.cfg 3 0 env0) = some 7 ∧
    observe (evalLow (addCallGuards ce1Prog) ce1EntryAfter 3 (GId.orig 0) env0 0) = some 7 ∧
    observe (evalMir ce1Prog.cfg 3 0 envTakeCall) = some 42 ∧
    observe (evalLow (addCallGuards ce1Prog) ce1EntryAfter 4 (GId.orig 0) envTakeCall 0) =
      some 42 :=
  ⟨ce1_after_split_isEntryLowering, rfl, rfl, rfl, rfl⟩

/-- `callbr` shape: inline asm with an output and a label whose block overwrites the output
local and then joins the fallthrough path.

```
bb0: asm!(.., out(reg) _2, label ..) -> [return: bb1, label: bb2]
bb1: _0 = copy _2; return
bb2: _2 = const 5; goto -> bb1
```
-/
noncomputable def ce1bProg : Prog :=
  [ ⟨[], .out true 2 (fun _ => 42) (fun e => e 9) [1, 2] none⟩,
    ⟨[fun e => some (upd e 0 (e 2))], .ret⟩,
    ⟨[fun e => some (upd e 2 5)], .goto 1⟩ ]

/-- Output stores at the entry of both destinations of the `callbr`. -/
noncomputable def ce1bEntry : Nat → List Nat
  | 1 => [2]
  | 2 => [2]
  | _ => []

/-- Take the label edge. -/
noncomputable def envTakeLabel : Env := fun x => if x = 9 then 1 else 0

theorem ce1b_isEntryLowering : IsEntryLowering ce1bProg.cfg ce1bEntry := by
  intro y d
  constructor
  · intro h
    cases y with
    | zero => exact (h : False).elim
    | succ y =>
      cases y with
      | zero =>
        cases (h : d = 2 ∨ False) with
        | inr h => exact h.elim
        | inl h =>
          subst h
          exact ⟨0, 0, ⟨[], .out true 2 (fun _ => 42) (fun e => e 9) [1, 2] none⟩, _, _, _, _,
            rfl, rfl, rfl⟩
      | succ y =>
        cases y with
        | succ y => exact (h : False).elim
        | zero =>
          cases (h : d = 2 ∨ False) with
          | inr h => exact h.elim
          | inl h =>
            subst h
            exact ⟨0, 1, ⟨[], .out true 2 (fun _ => 42) (fun e => e 9) [1, 2] none⟩, _, _, _, _,
              rfl, rfl, rfl⟩
  · intro ⟨x, i, blk, rhs, sel, ts, c, hx, ht, hn⟩
    have hx' : nth ce1bProg x = some blk := hx
    cases x with
    | zero =>
      have hb := Option.some.inj hx'
      subst hb
      have ht' : Term.out true 2 (fun _ => 42) (fun e => e 9) [1, 2] none =
          Term.out true d rhs sel ts c := ht
      injection ht' with _ hd _ _ hts _
      subst hd
      subst hts
      cases i with
      | zero =>
        have hy : 1 = y := Option.some.inj hn
        subst hy
        exact Or.inl rfl
      | succ i =>
        cases i with
        | zero =>
          have hy : 2 = y := Option.some.inj hn
          subst hy
          exact Or.inl rfl
        | succ i =>
          have hn' : nth ([] : List Nat) i = some y := hn
          rw [nth_nil] at hn'
          cases hn'
    | succ x =>
      cases x with
      | zero =>
        have hb := Option.some.inj hx'
        subst hb
        cases ht
      | succ x =>
        cases x with
        | zero =>
          have hb := Option.some.inj hx'
          subst hb
          cases ht
        | succ x =>
          have hx'' : nth ([] : List (Blk Nat)) x = some blk := hx'
          rw [nth_nil] at hx''
          cases hx''

/-- **Counterexample 1b (`callbr`).** The fallthrough edge `bb0 -> bb1` is critical. Along the
label edge the label block sets `_2 = 5`; on entering `bb1` the fallthrough edge's output store
re-executes and overwrites it with the asm result `42`: MIR returns `5`, the lowered program
returns `42`. Here the register *was* defined on the path taken, so the lowered program is not
reading an undefined value; it is simply wrong. -/
theorem ce1b_unsplit_callbr_critical_edge_reexecutes_output_store :
    IsEntryLowering ce1bProg.cfg ce1bEntry ∧
    observe (evalMir ce1bProg.cfg 3 0 envTakeLabel) = some 5 ∧
    observe (evalLow ce1bProg.cfg ce1bEntry 3 0 envTakeLabel 0) = some 42 :=
  ⟨ce1b_isEntryLowering, rfl, rfl⟩

/-- `bb0: drop(_x) -> bb1` for a type with drop glue that increments local `_9`;
`bb1: _0 = copy _9; return`. -/
noncomputable def ce2Prog : Prog :=
  [ ⟨[], .drop true (fun e => some (upd e 9 (e 9 + 1))) 1 none⟩,
    ⟨[fun e => some (upd e 0 (e 9))], .ret⟩ ]

/-- **Counterexample 2.** Removing a `Drop` whose type needs dropping omits the destructor's
side effect. `removeUnneededDrops` keeps it (result `1`); the variant that ignores `needsDrop`
returns `0`. -/
theorem ce2_remove_drop_on_needs_drop_type_omits_destructor_side_effect :
    observe (evalMir ce2Prog.cfg 2 0 env0) = some 1 ∧
    observe (evalMir (removeUnneededDrops ce2Prog.cfg) 2 0 env0) = some 1 ∧
    observe (evalMir (removeAllDrops ce2Prog.cfg) 2 0 env0) = some 0 :=
  ⟨rfl, rfl, rfl⟩

/-- `bb0: goto -> bb1`; `bb1: _0 = const 5; return` (a *non-empty* return block). -/
noncomputable def ce3Prog : Prog :=
  [ ⟨[], .goto 1⟩,
    ⟨[fun e => some (upd e 0 5)], .ret⟩ ]

/-- **Counterexample 3.** Replacing a `goto` to a return block that still has statements by a
bare `return` omits those statements. `multipleReturnTerminators` leaves the program alone
(result `5`); the variant that ignores the "no statements" condition returns `0`. -/
theorem ce3_multiple_return_duplicating_nonempty_return_block_omits_statements :
    observe (evalMir ce3Prog.cfg 2 0 env0) = some 5 ∧
    observe (evalMir (multipleReturnTerminators ce3Prog.cfg) 2 0 env0) = some 5 ∧
    observe (evalMir (duplicateAnyReturn ce3Prog.cfg) 2 0 env0) = some 0 :=
  ⟨rfl, rfl, rfl⟩

/-- `bb0: _0 = const 5; goto -> bb1`; `bb1: return` (an *empty* return block). -/
noncomputable def mrtFiresProg : Prog :=
  [ ⟨[fun e => some (upd e 0 5)], .goto 1⟩,
    ⟨[], .ret⟩ ]

/-- **The pass does fire, and the transformed program is one step shorter.** With one unit of
fuel the original is still running while the transformed program has already returned `5`. -/
theorem multipleReturnTerminators_fires :
    observe (evalMir mrtFiresProg.cfg 1 0 env0) = none ∧
    observe (evalMir mrtFiresProg.cfg 2 0 env0) = some 5 ∧
    observe (evalMir (multipleReturnTerminators mrtFiresProg.cfg) 1 0 env0) = some 5 :=
  ⟨rfl, rfl, rfl⟩

/-- `bb0: drop(_x) -> bb1` for a type *without* drop glue; `bb1: _0 = const 3; return`. -/
noncomputable def rudFiresProg : Prog :=
  [ ⟨[], .drop false (fun e => some e) 1 none⟩,
    ⟨[fun e => some (upd e 0 3)], .ret⟩ ]

/-- **The well-formedness hypothesis is satisfiable and the pass does fire.** -/
theorem removeUnneededDrops_fires :
    DropsWf rudFiresProg.cfg ∧
    (rudFiresProg.cfg 0).map (fun b => b.term.isDrop) = some true ∧
    (removeUnneededDrops rudFiresProg.cfg 0).map (fun b => b.term.isDrop) = some false ∧
    observe (evalMir rudFiresProg.cfg 2 0 env0) = some 3 ∧
    observe (evalMir (removeUnneededDrops rudFiresProg.cfg) 2 0 env0) = some 3 := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  intro x b g t u hx ht e
  have hx' : nth rudFiresProg x = some b := hx
  cases x with
  | zero =>
    have hb := Option.some.inj hx'
    subst hb
    have ht' : Term.drop false (fun e => some e) 1 none = Term.drop false g t u := ht
    injection ht' with _ hg _ _
    subst hg
    rfl
  | succ x =>
    cases x with
    | zero =>
      have hb := Option.some.inj hx'
      subst hb
      cases ht
    | succ x =>
      have hx'' : nth ([] : List (Blk Nat)) x = some b := hx'
      rw [nth_nil] at hx''
      cases hx''

/-! ## Axiom audit

Each line prints the axioms the named theorem depends on. -/

#print axioms halts_iff_of_stepMatch
#print axioms addCallGuards_operational_equivalence
#print axioms predCount_unique
#print axioms addCallGuards_noCriticalOutEdge
#print axioms stepLow_erase
#print axioms lowering_sound
#print axioms lowering_register_independent
#print axioms addCallGuards_outEdge_target_entered_only_from_source
#print axioms addCallGuards_then_lowering_sound
#print axioms removeUnneededDrops_sound
#print axioms removeUnneededDrops_bidirectional
#print axioms multipleReturnTerminators_bidirectional
#print axioms BoxModel.elaborate_sound
#print axioms BoxModel.elaborate_ub_iff
#print axioms BoxModel.elaborateList_sound
#print axioms BoxModel.plain_transmute_sound_for_loads
#print axioms BoxModel.plain_transmute_loses_box_validity_ub
#print axioms ce1_unsplit_call_or_callbr_critical_edge_clobbers_other_predecessor_value
#print axioms ce1_after_split_lowering_agrees
#print axioms ce1b_unsplit_callbr_critical_edge_reexecutes_output_store
#print axioms ce2_remove_drop_on_needs_drop_type_omits_destructor_side_effect
#print axioms ce3_multiple_return_duplicating_nonempty_return_block_omits_statements
#print axioms multipleReturnTerminators_fires
#print axioms removeUnneededDrops_fires

end BoxDerefCallGuards
