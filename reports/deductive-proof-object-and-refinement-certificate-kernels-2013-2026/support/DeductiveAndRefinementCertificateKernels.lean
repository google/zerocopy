/-
  DeductiveAndRefinementCertificateKernels.lean
  Certificate-Verifying Kernels: Deductive Proof-Object Checkers,
  seL4 Binary/Cogent Refinement Certificates, and Anneal's Ring-0 Kernel
  Extension Admission Architecture (2013–2026)

  Toolchain: Lean 4 v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52)
  Axiom Discipline: Zero axioms (0 sorryAx, 0 Classical.choice, 0 Lean.ofReduceBool).
-/

namespace DeductiveAndRefinementCertificateKernels

/-!
## Prelude: Constructive Equality & Comparison Helpers (Zero `Classical.choice`)

We define inductive boolean comparisons on `Nat` and `List Nat` with constructive
soundness and reflexivity lemmas so that no theorem pulls in `Classical.choice`
via stdlib `BEq` or `Decidable` instances.
-/

theorem band_eq_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> try contradiction
  exact ⟨rfl, rfl⟩

def natEq : Nat → Nat → Bool
  | 0, 0 => true
  | n + 1, m + 1 => natEq n m
  | _, _ => false

theorem natEq_refl (n : Nat) : natEq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natEq_eq {n m : Nat} (h : natEq n m = true) : n = m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ _ => contradiction
  | succ k ih =>
    cases m with
    | zero => contradiction
    | succ j =>
      have hk : k = j := ih h
      rw [hk]

theorem natEq_ne {n m : Nat} (h : natEq n m = false) : n ≠ m := by
  intro heq
  subst heq
  rw [natEq_refl] at h
  contradiction

def natLe : Nat → Nat → Bool
  | 0, _ => true
  | _ + 1, 0 => false
  | n + 1, m + 1 => natLe n m

theorem natLe_refl (n : Nat) : natLe n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

def natLt (n m : Nat) : Bool := natLe (n + 1) m

def inRange (addr lo hi : Nat) : Bool :=
  natLe lo addr && natLt addr hi

def natListEq : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => natEq x y && natListEq xs ys
  | _, _ => false

theorem natListEq_refl (xs : List Nat) : natListEq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [natListEq, natEq_refl, ih]

theorem natListEq_eq {xs ys : List Nat} (h : natListEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => contradiction
  | cons x rest ih =>
    cases ys with
    | nil => contradiction
    | cons y restY =>
      have hBoth := band_eq_true h
      have hx : x = y := natEq_eq hBoth.1
      have hrest : rest = restY := ih hBoth.2
      rw [hx, hrest]

/-!
================================================================================
## Section 1: seL4 Binary `GraphLang` Cutpoint Refinement &
## Cogent / Dargent Linear Value-to-In-Place-Update Refinement Certificates
================================================================================
-/

/-!
### 1A. seL4 Binary Translation Validation (`seL4/graph-refine`, PLDI 2013)
Cutpoint-Indexed Acyclic Segment Refinement Composition
-/

abbrev CutpointId := Nat
abbrev StateVal := Nat

/-- A single cutpoint-to-cutpoint acyclic segment transition in `GraphLang`. -/
structure CutpointStep where
  entryCutpoint : CutpointId
  exitCutpoint  : CutpointId
  srcTransform  : StateVal → StateVal
  binTransform  : StateVal → StateVal

/-- State equivalence / refinement invariant at cutpoints between `AutoCorres`/`Simpl`
    source state and HOL4-decompiled binary `GraphLang` state. -/
def CutpointStateRel (sSrc sBin : StateVal) : Prop :=
  sSrc = sBin

/-- Local SMT-discharged cutpoint segment refinement obligation:
    if entry states refine at `seg.entryCutpoint`, then exit states refine at `seg.exitCutpoint`. -/
def SegmentRefines (seg : CutpointStep) : Prop :=
  ∀ sSrc sBin : StateVal,
    CutpointStateRel sSrc sBin →
    CutpointStateRel (seg.srcTransform sSrc) (seg.binTransform sBin)

/-- Execute a sequence of cutpoint segments on a state. -/
def evalSrcTrace : List CutpointStep → StateVal → StateVal
  | [], s => s
  | seg :: rest, s => evalSrcTrace rest (seg.srcTransform s)

def evalBinTrace : List CutpointStep → StateVal → StateVal
  | [], s => s
  | seg :: rest, s => evalBinTrace rest (seg.binTransform s)

/-- All segments in a trace satisfy their local cutpoint refinement obligation. -/
def AllSegmentsRefine : List CutpointStep → Prop
  | [] => True
  | seg :: rest => SegmentRefines seg ∧ AllSegmentsRefine rest

/-- **Theorem (`sel4_graph_refine_cutpoint_composition_soundness`)**:
    In the `seL4/graph-refine` architecture (Sewell, Myreen & Klein, PLDI 2013),
    decomposing whole-kernel binary translation validation into loop-free segments
    between cutpoints is compositional: if every cutpoint-to-cutpoint segment
    discharges its local refinement obligation (`AllSegmentsRefine trace`), then
    any multi-segment binary execution trace refines the corresponding `Simpl`/`AutoCorres`
    C execution trace from matching initial states. -/
theorem sel4_graph_refine_cutpoint_composition_soundness
    (trace : List CutpointStep)
    (sSrc sBin : StateVal)
    (hAll : AllSegmentsRefine trace)
    (hInit : CutpointStateRel sSrc sBin) :
    CutpointStateRel (evalSrcTrace trace sSrc) (evalBinTrace trace sBin) := by
  induction trace generalizing sSrc sBin with
  | nil => exact hInit
  | cons seg rest ih =>
    have hSeg : SegmentRefines seg := hAll.1
    have hRest : AllSegmentsRefine rest := hAll.2
    have hStep : CutpointStateRel (seg.srcTransform sSrc) (seg.binTransform sBin) :=
      hSeg sSrc sBin hInit
    exact ih (seg.srcTransform sSrc) (seg.binTransform sBin) hRest hStep

/-!
### 1B. Cogent & Dargent Linear Value-to-In-Place-Update Refinement Certificate
(Amani et al. ASPLOS 2016; O'Connor et al. ICFP 2016; Chen et al. POPL 2023)

In `Cogent`, systems components (such as `BilbyFS` and `ext2`) are written in a pure
functional language with a **linear / uniqueness type system** and **Dargent** data
layout descriptors. The compiler emits both C code (mutating heap-allocated structs
in-place without garbage collection or copying) and an Isabelle/HOL refinement chain:
$$\text{Shallow Spec} \sqsubseteq \text{Deep Embedding} \sqsubseteq_{\text{Value}\leftrightarrow\text{Update}} \text{Linear In-Place State} \sqsubseteq_{\text{AutoCorres}} \text{C}$$
We formalize the core $\text{Value} \leftrightarrow \text{Update}$ step and prove both its
frame-preserving soundness under `LinearCert` and its exact failure mode under aliasing.
-/

abbrev VarId := Nat
abbrev FieldId := Nat
abbrev BufPtr := Nat
abbrev ByteOffset := Nat

/-- Pure functional record value (`Value` semantics in Cogent). -/
structure PureVal where
  fields : FieldId → Nat

/-- Pure variable environment mapping live variables to immutable `PureVal` records. -/
abbrev PureEnv := VarId → PureVal

/-- Pure functional field update on a record variable `x`: returns a new `PureEnv`
    where `x` has `field` updated to `newVal` and all other variables `y ≠ x` are unchanged. -/
def evalPureUpdate (env : PureEnv) (x : VarId) (field : FieldId) (newVal : Nat) : PureEnv :=
  fun v =>
    match natEq v x with
    | true =>
      { fields := fun f =>
          match natEq f field with
          | true => newVal
          | false => (env x).fields f }
    | false =>
      env v

/-- Imperative pointer environment mapping each variable `v` to a C struct pointer `BufPtr`. -/
abbrev PtrEnv := VarId → BufPtr

/-- Imperative kernel heap (`Update` semantics in Cogent): maps buffer pointer `p` and
    Dargent byte/word offset `off` to its stored machine word. -/
abbrev HeapState := BufPtr → ByteOffset → Nat

/-- Dargent layout descriptor mapping abstract `FieldId` to concrete byte/word offset. -/
abbrev DargentLayout := FieldId → ByteOffset

/-- A Dargent layout is collision-free (injective on fields) when distinct fields map
    to distinct offsets inside the struct. -/
def LayoutDisjoint (layout : DargentLayout) : Prop :=
  ∀ f1 f2 : FieldId, natEq (layout f1) (layout f2) = true → natEq f1 f2 = true

/-- In-place imperative C struct mutation: writes `newVal` directly into heap buffer
    `ptrs x` at offset `layout field` with zero allocation, zero copying, and zero GC. -/
def evalImpInPlace
    (ptrs : PtrEnv) (layout : DargentLayout) (h : HeapState)
    (x : VarId) (field : FieldId) (newVal : Nat) : HeapState :=
  fun p off =>
    match natEq p (ptrs x) && natEq off (layout field) with
    | true => newVal
    | false => h p off

/-- `VarRefines layout pEnv ptrs h v` holds when every field `f` of variable `v` in
    the pure environment `pEnv` matches the imperative heap word at `(ptrs v, layout f)`. -/
def VarRefines (layout : DargentLayout) (pEnv : PureEnv) (ptrs : PtrEnv) (h : HeapState) (v : VarId) : Prop :=
  ∀ f : FieldId, h (ptrs v) (layout f) = (pEnv v).fields f

/-- Frame-separated refinement relation `FrameRel` across a list of live variables. -/
def FrameRel (liveVars : List VarId) (layout : DargentLayout) (pEnv : PureEnv) (ptrs : PtrEnv) (h : HeapState) : Prop :=
  ∀ v : VarId, v ∈ liveVars → VarRefines layout pEnv ptrs h v

/-- Decidable linear/uniqueness type-checker certificate (`LinearCert`):
    verifies that `targetVar` owns a unique buffer pointer disjoint from every other
    live variable `v ∈ liveVars` (`natEq v targetVar = false → natEq (ptrs v) (ptrs targetVar) = false`). -/
def LinearCert : List VarId → PtrEnv → VarId → Bool
  | [], _, _ => true
  | v :: rest, ptrs, targetVar =>
    (match natEq v targetVar with
     | true => true
     | false => !(natEq (ptrs v) (ptrs targetVar))) &&
      LinearCert rest ptrs targetVar

theorem linearCert_disjoint_ptr
    {liveVars : List VarId} {ptrs : PtrEnv} {targetVar v : VarId}
    (hCert : LinearCert liveVars ptrs targetVar = true)
    (hMem : v ∈ liveVars)
    (hNe : natEq v targetVar = false) :
    natEq (ptrs v) (ptrs targetVar) = false := by
  induction liveVars with
  | nil => contradiction
  | cons hd tl ih =>
    have hBoth := band_eq_true hCert
    cases hMem with
    | head =>
      have hHd : (match natEq v targetVar with
        | true => true
        | false => !(natEq (ptrs v) (ptrs targetVar))) = true := hBoth.1
      rw [hNe] at hHd
      cases hPtr : natEq (ptrs v) (ptrs targetVar)
      · rfl
      · rw [hPtr] at hHd
        contradiction
    | tail _ hInTl =>
      exact ih hBoth.2 hInTl

/-- **Theorem (`frame_disjoint_preservation`)**:
    In-place mutation of `targetVar`'s buffer in `evalImpInPlace` leaves every disjoint
    kernel heap object `q` (`natEq q (ptrs targetVar) = false`) byte-for-byte identical. -/
theorem frame_disjoint_preservation
    (ptrs : PtrEnv) (layout : DargentLayout) (h : HeapState)
    (targetVar : VarId) (field : FieldId) (newVal : Nat)
    (q : BufPtr) (off : ByteOffset)
    (hDisjoint : natEq q (ptrs targetVar) = false) :
    evalImpInPlace ptrs layout h targetVar field newVal q off = h q off := by
  unfold evalImpInPlace
  rw [hDisjoint]
  rfl

/-- **Theorem (`cogent_linear_in_place_refinement_soundness`)**:
    If `LinearCert liveVars ptrs targetVar = true` (Cogent's linear type system certifies
    that no other live variable aliases `ptrs targetVar`) and `LayoutDisjoint layout` holds
    (Dargent's field offsets are non-overlapping), then in-place destructive mutation
    `evalImpInPlace` refines the pure functional update `evalPureUpdate` across all
    live variables (`FrameRel` is preserved without copying or garbage collection). -/
theorem cogent_linear_in_place_refinement_soundness
    (liveVars : List VarId)
    (layout : DargentLayout)
    (pEnv : PureEnv)
    (ptrs : PtrEnv)
    (h : HeapState)
    (targetVar : VarId)
    (field : FieldId)
    (newVal : Nat)
    (hFrame : FrameRel liveVars layout pEnv ptrs h)
    (hLinear : LinearCert liveVars ptrs targetVar = true)
    (hLayout : LayoutDisjoint layout) :
    FrameRel liveVars layout
      (evalPureUpdate pEnv targetVar field newVal)
      ptrs
      (evalImpInPlace ptrs layout h targetVar field newVal) := by
  intro v hMem f
  unfold evalImpInPlace evalPureUpdate
  cases hVarEq : natEq v targetVar
  · -- Case 1: `v ≠ targetVar`. By `LinearCert`, `ptrs v ≠ ptrs targetVar`.
    have hPtrDisj : natEq (ptrs v) (ptrs targetVar) = false :=
      linearCert_disjoint_ptr hLinear hMem hVarEq
    rw [hPtrDisj]
    exact hFrame v hMem f
  · -- Case 2: `v = targetVar`.
    have hvEq : v = targetVar := natEq_eq hVarEq
    subst hvEq
    rw [natEq_refl]
    dsimp only
    cases hFieldEq : natEq f field
    · -- Subcase 2a: `f ≠ field`. By `LayoutDisjoint`, `layout f ≠ layout field`.
      cases hOffEq : natEq (layout f) (layout field)
      · exact hFrame v hMem f
      · have hContr : natEq f field = true := hLayout f field hOffEq
        rw [hFieldEq] at hContr
        contradiction
    · -- Subcase 2b: `f = field`.
      have hfEq : f = field := natEq_eq hFieldEq
      subst hfEq
      rw [natEq_refl (layout f)]
      rfl

/-- **Theorem (`nonlinear_alias_breaks_in_place_refinement`)**:
    If two distinct live variables (`x = 0`, `y = 1`) alias the same heap buffer pointer
    (`ptrs 0 = 0`, `ptrs 1 = 0`) because linear uniqueness checking is omitted
    (`LinearCert [0, 1] ptrs 0 = false`), then in-place mutation of `x` silently
    corrupts the pure observation of `y`, violating `FrameRel` even when starting
    from a state satisfying `FrameRel`. -/
theorem nonlinear_alias_breaks_in_place_refinement :
    let liveVars : List VarId := [0, 1]
    let layout : DargentLayout := fun f => f
    let pEnv : PureEnv := fun _ => { fields := fun _ => 2 }
    let ptrs : PtrEnv := fun _ => 0
    let h : HeapState := fun _ _ => 2
    FrameRel liveVars layout pEnv ptrs h ∧
    LinearCert liveVars ptrs 0 = false ∧
    ¬ FrameRel liveVars layout
        (evalPureUpdate pEnv 0 0 9)
        ptrs
        (evalImpInPlace ptrs layout h 0 0 9) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v _ f
    rfl
  · rfl
  · intro hAfter
    have hY : VarRefines (fun f => f) (evalPureUpdate (fun _ => { fields := fun _ => 2 }) 0 0 9)
        (fun _ => 0) (evalImpInPlace (fun _ => 0) (fun f => f) (fun _ _ => 2) 0 0 9) 1 :=
      hAfter 1 (List.Mem.tail 0 (List.Mem.head []))
    have hField0 := hY 0
    revert hField0
    decide

/-!
================================================================================
## Section 2: Compact Proof-Object Certificate Checkers (`Metamath Zero / .mmb`,
## Signed Attestation Daemons, and Anneal's Consumer-Bound Proof-Checking Gate)
================================================================================

We model Mario Carneiro's `.mmb` binary proof verifier (`mm0-c/verifier.c`, CPP 2020)
with its $O(1)$ array-indexed heap (`g_heap`) and linear stack machine (`g_stack`),
prove deductive soundness (`mmb_verifier_sound`), and prove why a kernel admission gate
must bind the theorem conclusion to the consumer's exact byte artifact (`consumer_bound_mmb_gate_sound`
vs. `unbound_theorem_checker_admits_spoofed_subject`).
-/

/-- Proposition AST for kernel proof-object verification. -/
inductive PropFormula where
  | atom     : Nat → PropFormula
  | imp      : PropFormula → PropFormula → PropFormula
  | byteSafe : List Nat → Nat → PropFormula

def formulaEq : PropFormula → PropFormula → Bool
  | .atom a, .atom b => natEq a b
  | .imp a1 b1, .imp a2 b2 => formulaEq a1 a2 && formulaEq b1 b2
  | .byteSafe bs1 p1, .byteSafe bs2 p2 => natListEq bs1 bs2 && natEq p1 p2
  | _, _ => false

theorem formulaEq_refl (f : PropFormula) : formulaEq f f = true := by
  induction f with
  | atom a => exact natEq_refl a
  | imp a b iha ihb => simp [formulaEq, iha, ihb]
  | byteSafe bs p => simp [formulaEq, natListEq_refl, natEq_refl]

theorem formulaEq_eq {f1 f2 : PropFormula} (h : formulaEq f1 f2 = true) : f1 = f2 := by
  induction f1 generalizing f2 with
  | atom a =>
    cases f2 with
    | atom b =>
      have hab : a = b := natEq_eq h
      rw [hab]
    | imp _ _ => contradiction
    | byteSafe _ _ => contradiction
  | imp a1 b1 iha ihb =>
    cases f2 with
    | atom _ => contradiction
    | imp a2 b2 =>
      have hBoth := band_eq_true h
      have ha : a1 = a2 := iha hBoth.1
      have hb : b1 = b2 := ihb hBoth.2
      rw [ha, hb]
    | byteSafe _ _ => contradiction
  | byteSafe bs1 p1 =>
    cases f2 with
    | atom _ => contradiction
    | imp _ _ => contradiction
    | byteSafe bs2 p2 =>
      have hBoth := band_eq_true h
      have hbs : bs1 = bs2 := natListEq_eq hBoth.1
      have hp : p1 = p2 := natEq_eq hBoth.2
      rw [hbs, hp]

/-- True deductive derivability from a hypothesis context `hyps` (Hilbert-style kernel). -/
inductive Deriv (hyps : List PropFormula) : PropFormula → Prop where
  | hyp  {f : PropFormula} : f ∈ hyps → Deriv hyps f
  | mp   {a b : PropFormula} : Deriv hyps (.imp a b) → Deriv hyps a → Deriv hyps b

/-- `.mmb` binary proof-stream opcodes (`MP_HYP`, `MP_REF`, `MP_SAVE`, `MP_THM`). -/
inductive MmbCmd where
  | loadHyp          : Nat → MmbCmd  -- MP_HYP: push hyps[idx] onto stack and heap
  | loadHeap         : Nat → MmbCmd  -- MP_REF: push g_heap[idx] onto stack in O(1)
  | saveHeap         : MmbCmd        -- MP_SAVE: append top of stack to g_heap
  | applyModusPonens : MmbCmd        -- MP_THM: pop `a` and `imp a b`, push `b`

/-- Linear stack-machine state of `mm0-c/verifier.c` (`g_stack` and `g_heap`). -/
structure MmbState where
  stack : List PropFormula
  heap  : List PropFormula

/-- Index lookup in a list without `Classical.choice`. -/
def listGetOpt {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGetOpt xs n

theorem listGetOpt_mem {α : Type} {xs : List α} {n : Nat} {x : α}
    (h : listGetOpt xs n = some x) : x ∈ xs := by
  induction xs generalizing n with
  | nil => contradiction
  | cons hd tl ih =>
    cases n with
    | zero =>
      injection h with hEq
      subst hEq
      exact List.Mem.head tl
    | succ k =>
      exact List.Mem.tail hd (ih h)

/-- Single-step execution of the `.mmb` proof-stream verifier (`mm0-c/verifier.c`). -/
def stepMmb (hyps : List PropFormula) (st : MmbState) : MmbCmd → Option MmbState
  | .loadHyp idx =>
    match listGetOpt hyps idx with
    | some f => some { stack := f :: st.stack, heap := st.heap ++ [f] }
    | none => none
  | .loadHeap idx =>
    match listGetOpt st.heap idx with
    | some f => some { stack := f :: st.stack, heap := st.heap }
    | none => none
  | .saveHeap =>
    match st.stack with
    | f :: _ => some { stack := st.stack, heap := st.heap ++ [f] }
    | [] => none
  | .applyModusPonens =>
    match st.stack with
    | a :: (.imp a' b) :: rest =>
      match formulaEq a a' with
      | true => some { stack := b :: rest, heap := st.heap }
      | false => none
    | _ => none

/-- Run a sequence of `.mmb` proof commands from `st`. -/
def runMmbStream (hyps : List PropFormula) : List MmbCmd → MmbState → Option MmbState
  | [], st => some st
  | cmd :: rest, st =>
    match stepMmb hyps st cmd with
    | some st' => runMmbStream hyps rest st'
    | none => none

/-- Complete `.mmb` proof checker: runs `stream` from empty stack/heap and checks
    that the final stack contains the unique theorem `expectedConclusion`. -/
def verifyMmbProof
    (hyps : List PropFormula) (stream : List MmbCmd) (expectedConclusion : PropFormula) : Bool :=
  match runMmbStream hyps stream { stack := [], heap := [] } with
  | some stFinal =>
    match stFinal.stack with
    | [finalF] => formulaEq finalF expectedConclusion
    | _ => false
  | none => false

/-- Invariant of the `.mmb` verifier state: every formula on `g_stack` and `g_heap`
    is deductively derivable from `hyps`. -/
def MmbStateValid (hyps : List PropFormula) (st : MmbState) : Prop :=
  (∀ f ∈ st.stack, Deriv hyps f) ∧ (∀ f ∈ st.heap, Deriv hyps f)

theorem mem_append_singleton {α : Type} {xs : List α} {x y : α}
    (h : y ∈ xs ++ [x]) : y ∈ xs ∨ y = x := by
  induction xs with
  | nil =>
    cases h with
    | head => exact Or.inr rfl
    | tail _ hEmpty => contradiction
  | cons hd tl ih =>
    cases h with
    | head => exact Or.inl (List.Mem.head tl)
    | tail _ hTl =>
      cases ih hTl with
      | inl hIn => exact Or.inl (List.Mem.tail hd hIn)
      | inr hEq => exact Or.inr hEq

theorem stepMmb_preserves_valid
    {hyps : List PropFormula} {st st' : MmbState} {cmd : MmbCmd}
    (hValid : MmbStateValid hyps st)
    (hStep : stepMmb hyps st cmd = some st') :
    MmbStateValid hyps st' := by
  cases cmd with
  | loadHyp idx =>
    change (match listGetOpt hyps idx with
      | some f => some { stack := f :: st.stack, heap := st.heap ++ [f] }
      | none => none) = some st' at hStep
    cases hLookup : listGetOpt hyps idx with
    | none => rw [hLookup] at hStep; contradiction
    | some f =>
      rw [hLookup] at hStep
      injection hStep with hEq
      subst hEq
      have hDerivF : Deriv hyps f := Deriv.hyp (listGetOpt_mem hLookup)
      refine ⟨?_, ?_⟩
      · intro g hg
        cases hg with
        | head => exact hDerivF
        | tail _ hInStack => exact hValid.1 g hInStack
      · intro g hg
        cases mem_append_singleton hg with
        | inl hInHeap => exact hValid.2 g hInHeap
        | inr hEq => subst hEq; exact hDerivF
  | loadHeap idx =>
    change (match listGetOpt st.heap idx with
      | some f => some { stack := f :: st.stack, heap := st.heap }
      | none => none) = some st' at hStep
    cases hLookup : listGetOpt st.heap idx with
    | none => rw [hLookup] at hStep; contradiction
    | some f =>
      rw [hLookup] at hStep
      injection hStep with hEq
      subst hEq
      have hDerivF : Deriv hyps f := hValid.2 f (listGetOpt_mem hLookup)
      refine ⟨?_, hValid.2⟩
      intro g hg
      cases hg with
      | head => exact hDerivF
      | tail _ hInStack => exact hValid.1 g hInStack
  | saveHeap =>
    change (match st.stack with
      | f :: _ => some { stack := st.stack, heap := st.heap ++ [f] }
      | [] => none) = some st' at hStep
    cases hStack : st.stack with
    | nil => rw [hStack] at hStep; contradiction
    | cons top rest =>
      rw [hStack] at hStep
      injection hStep with hEq
      subst hEq
      have hDerivTop : Deriv hyps top := by
        apply hValid.1 top
        rw [hStack]
        exact List.Mem.head rest
      refine ⟨?_, ?_⟩
      · intro g hg
        apply hValid.1 g
        rw [hStack]
        exact hg
      · intro g hg
        cases mem_append_singleton hg with
        | inl hInHeap => exact hValid.2 g hInHeap
        | inr hEq => subst hEq; exact hDerivTop
  | applyModusPonens =>
    change (match st.stack with
      | a :: (.imp a' b) :: rest =>
        match formulaEq a a' with
        | true => some { stack := b :: rest, heap := st.heap }
        | false => none
      | _ => none) = some st' at hStep
    cases hStack : st.stack with
    | nil => rw [hStack] at hStep; contradiction
    | cons a rest1 =>
      cases rest1 with
      | nil => rw [hStack] at hStep; contradiction
      | cons mid rest2 =>
        cases mid with
        | atom _ => rw [hStack] at hStep; contradiction
        | byteSafe _ _ => rw [hStack] at hStep; contradiction
        | imp a' b =>
          rw [hStack] at hStep
          change (match formulaEq a a' with
            | true => some { stack := b :: rest2, heap := st.heap }
            | false => none) = some st' at hStep
          cases hEqA : formulaEq a a' with
          | false => rw [hEqA] at hStep; contradiction
          | true =>
            rw [hEqA] at hStep
            injection hStep with hStEq
            subst hStEq
            have haEq : a = a' := formulaEq_eq hEqA
            subst haEq
            have hDerivA : Deriv hyps a := by
              apply hValid.1 a
              rw [hStack]
              exact List.Mem.head _
            have hDerivImp : Deriv hyps (.imp a b) := by
              apply hValid.1 (.imp a b)
              rw [hStack]
              exact List.Mem.tail a (List.Mem.head rest2)
            have hDerivB : Deriv hyps b := Deriv.mp hDerivImp hDerivA
            refine ⟨?_, hValid.2⟩
            intro g hg
            cases hg with
            | head => exact hDerivB
            | tail _ hInRest =>
              apply hValid.1 g
              rw [hStack]
              exact List.Mem.tail a (List.Mem.tail (.imp a b) hInRest)

theorem runMmbStream_preserves_valid
    {hyps : List PropFormula} {stream : List MmbCmd} {st st' : MmbState}
    (hValid : MmbStateValid hyps st)
    (hRun : runMmbStream hyps stream st = some st') :
    MmbStateValid hyps st' := by
  induction stream generalizing st with
  | nil =>
    injection hRun with hEq
    subst hEq
    exact hValid
  | cons cmd rest ih =>
    unfold runMmbStream at hRun
    cases hStep : stepMmb hyps st cmd with
    | none => rw [hStep] at hRun; contradiction
    | some stMid =>
      rw [hStep] at hRun
      have hMidValid : MmbStateValid hyps stMid := stepMmb_preserves_valid hValid hStep
      exact ih hMidValid hRun

/-- **Theorem (`mmb_verifier_sound`)**:
    If the linear stack-machine `.mmb` verifier `verifyMmbProof hyps stream target = true`,
    then `Deriv hyps target` holds in the deductive kernel. -/
theorem mmb_verifier_sound
    {hyps : List PropFormula} {stream : List MmbCmd} {target : PropFormula}
    (hCheck : verifyMmbProof hyps stream target = true) :
    Deriv hyps target := by
  unfold verifyMmbProof at hCheck
  cases hRun : runMmbStream hyps stream { stack := [], heap := [] } with
  | none => rw [hRun] at hCheck; contradiction
  | some stFinal =>
    rw [hRun] at hCheck
    change (match stFinal.stack with
      | [finalF] => formulaEq finalF target
      | _ => false) = true at hCheck
    cases hStack : stFinal.stack with
    | nil => rw [hStack] at hCheck; contradiction
    | cons finalF rest =>
      cases rest with
      | cons _ _ => rw [hStack] at hCheck; contradiction
      | nil =>
        rw [hStack] at hCheck
        have hEq : finalF = target := formulaEq_eq hCheck
        subst hEq
        have hInitValid : MmbStateValid hyps { stack := [], heap := [] } :=
          ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
        have hFinalValid : MmbStateValid hyps stFinal :=
          runMmbStream_preserves_valid hInitValid hRun
        apply hFinalValid.1 finalF
        rw [hStack]
        exact List.Mem.head []

/-- A proof-carrying certificate containing a claimed theorem statement and an `.mmb` proof stream. -/
structure MmbCert where
  claimedTheorem : PropFormula
  proofStream    : List MmbCmd

/-- Unbound proof checker: verifies that `cert.proofStream` proves `cert.claimedTheorem`,
    WITHOUT checking that `cert.claimedTheorem` is about the consumer's `candidateBytes`. -/
def unboundMmbGate (hyps : List PropFormula) (cert : MmbCert) : Bool :=
  verifyMmbProof hyps cert.proofStream cert.claimedTheorem

/-- Consumer-bound proof checker (Anneal's `StrictUnitTheorem` + `EmittedArtifact` + `CertChecker` pattern):
    checks that `cert.claimedTheorem` equals `.byteSafe candidateBytes reqPolicy` AND verifies the proof stream. -/
def consumerBoundMmbGate
    (hyps : List PropFormula) (candidateBytes : List Nat) (reqPolicy : Nat) (cert : MmbCert) : Bool :=
  formulaEq cert.claimedTheorem (.byteSafe candidateBytes reqPolicy) &&
    verifyMmbProof hyps cert.proofStream (.byteSafe candidateBytes reqPolicy)

/-- **Theorem (`consumer_bound_mmb_gate_sound`)**:
    When the kernel admission gate enforces consumer-side theorem binding
    (`consumerBoundMmbGate hyps candidateBytes reqPolicy cert = true`),
    any accepted certificate deductively proves `.byteSafe candidateBytes reqPolicy`
    for the exact bytes loaded by the kernel. -/
theorem consumer_bound_mmb_gate_sound
    {hyps : List PropFormula} {candidateBytes : List Nat} {reqPolicy : Nat} {cert : MmbCert}
    (hGate : consumerBoundMmbGate hyps candidateBytes reqPolicy cert = true) :
    Deriv hyps (.byteSafe candidateBytes reqPolicy) := by
  have hBoth := band_eq_true hGate
  exact mmb_verifier_sound hBoth.2

/-- **Theorem (`unbound_theorem_checker_admits_spoofed_subject`)**:
    If a kernel proof checker only checks that `cert.proofStream` validly proves
    `cert.claimedTheorem` (`unboundMmbGate`) without binding `cert.claimedTheorem`
    to the consumer's `candidateBytes`, a valid proof for a benign artifact `[1]`
    is accepted when loading a malicious artifact `[2, 3]` (`swapgs`/`wrmsr`),
    whereas `consumerBoundMmbGate` rejects it. -/
theorem unbound_theorem_checker_admits_spoofed_subject :
    let benignBytes : List Nat := [1]
    let maliciousBytes : List Nat := [2, 3]
    let policy : Nat := 1
    let hyps : List PropFormula := [.byteSafe benignBytes policy]
    let spoofedCert : MmbCert := {
      claimedTheorem := .byteSafe benignBytes policy
      proofStream := [.loadHyp 0]
    }
    unboundMmbGate hyps spoofedCert = true ∧
    consumerBoundMmbGate hyps maliciousBytes policy spoofedCert = false := by
  refine ⟨rfl, rfl⟩

/-!
================================================================================
## Section 3: Anneal's Complete Ring-0 Kernel Extension Admission Gate
## (`KernelExtensionAdmissionGate`) — Six-Way Sufficiency & Necessity
================================================================================

We now formalize Anneal's complete consumer-bound Ring-0 kernel extension admission
gate (`KernelExtensionAdmissionGate`) with all **Six Obligations**:
1. `ob1_byteBinding`: Whole-artifact byte sequence equality (`cert.boundBytes = candidateImage.bytes`),
   relocation table binding, and instruction-decode binding;
2. `ob2_isaPrivilegeConfinement`: Every reachable instruction is in the permitted unprivileged
   Ring-0 subset (no `wrmsr`, `mov cr3`, `cli`, `lidt`);
3. `ob3_frameDisjointMemory`: Every memory read stays in `[readableLo, readableHi)` and every
   memory write stays in `[writableLo, writableHi)`, strictly disjoint from `KernelCoreFrame`;
4. `ob4_abiCalleeSaveRestoration`: Callee-saved registers (`calleeSaveRbp`), stack pointer,
   and interrupt flags are preserved/restored to their entry values on return;
5. `ob5_interruptSafePointInvariant`: At every instruction step, the stack pointer satisfies
   the hardware interrupt/red-zone/IST alignment invariant and no kernel spinlock/RCU lock
   is held across an unmasked instruction step;
6. `ob6_boundedFuelTermination`: The certificate supplies a verified fuel bound
   `certifiedFuel ≤ maxKernelExtensionFuel` such that execution from the entry state
   reaches a clean `Ret outVal` within `certifiedFuel` steps and refines `expectedOutput`.
-/

/-- Abstract Ring-0 instruction set modeling privileged operations, memory accesses,
    ABI callee-saved register effects, interrupt-alignment/lock states, loops, and returns. -/
inductive Ring0Instr where
  | compute                     : Nat → Ring0Instr
  | privOp                      : Nat → Ring0Instr
  | memRead                     : Nat → Ring0Instr
  | memWrite                    : Nat → Nat → Ring0Instr
  | corruptCalleeSave           : Nat → Ring0Instr
  | misalignStackOrHoldSpinlock : Ring0Instr
  | infiniteLoop                : Ring0Instr
  | ret                         : Nat → Ring0Instr

def isInfiniteLoop : Ring0Instr → Bool
  | .infiniteLoop => true
  | _ => false

def instrEq : Ring0Instr → Ring0Instr → Bool
  | .compute a, .compute b => natEq a b
  | .privOp a, .privOp b => natEq a b
  | .memRead a, .memRead b => natEq a b
  | .memWrite a1 v1, .memWrite a2 v2 => natEq a1 a2 && natEq v1 v2
  | .corruptCalleeSave a, .corruptCalleeSave b => natEq a b
  | .misalignStackOrHoldSpinlock, .misalignStackOrHoldSpinlock => true
  | .infiniteLoop, .infiniteLoop => true
  | .ret a, .ret b => natEq a b
  | _, _ => false

theorem instrEq_refl (i : Ring0Instr) : instrEq i i = true := by
  cases i with
  | compute a => exact natEq_refl a
  | privOp a => exact natEq_refl a
  | memRead a => exact natEq_refl a
  | memWrite a v => simp [instrEq, natEq_refl]
  | corruptCalleeSave a => exact natEq_refl a
  | misalignStackOrHoldSpinlock => rfl
  | infiniteLoop => rfl
  | ret a => exact natEq_refl a

theorem instrEq_eq {i1 i2 : Ring0Instr} (h : instrEq i1 i2 = true) : i1 = i2 := by
  cases i1 <;> cases i2 <;> try contradiction
  case compute.compute a b =>
    rw [natEq_eq h]
  case privOp.privOp a b =>
    rw [natEq_eq h]
  case memRead.memRead a b =>
    rw [natEq_eq h]
  case memWrite.memWrite a1 v1 a2 v2 =>
    have hBoth := band_eq_true h
    rw [natEq_eq hBoth.1, natEq_eq hBoth.2]
  case corruptCalleeSave.corruptCalleeSave a b =>
    rw [natEq_eq h]
  case misalignStackOrHoldSpinlock.misalignStackOrHoldSpinlock => rfl
  case infiniteLoop.infiniteLoop => rfl
  case ret.ret a b =>
    rw [natEq_eq h]

def progEq : List Ring0Instr → List Ring0Instr → Bool
  | [], [] => true
  | i :: is, j :: js => instrEq i j && progEq is js
  | _, _ => false

theorem progEq_refl (p : List Ring0Instr) : progEq p p = true := by
  induction p with
  | nil => rfl
  | cons i rest ih => simp [progEq, instrEq_refl, ih]

theorem progEq_eq {p1 p2 : List Ring0Instr} (h : progEq p1 p2 = true) : p1 = p2 := by
  induction p1 generalizing p2 with
  | nil =>
    cases p2 with
    | nil => rfl
    | cons _ _ => contradiction
  | cons i rest ih =>
    cases p2 with
    | nil => contradiction
    | cons j restJ =>
      have hBoth := band_eq_true h
      rw [instrEq_eq hBoth.1, ih hBoth.2]

/-- Candidate ELF / machine-code binary image presented to the Ring-0 kernel loader. -/
structure CandidateImage where
  bytes       : List Nat
  relocHash   : Nat
  decodedProg : List Ring0Instr

/-- Host kernel admission request specifying the extension's sandbox bounds, entry ABI,
    maximum allowed fuel, and expected functional specification output. -/
structure AdmissionRequest where
  expectedReloc          : Nat
  entryRbp               : Nat
  readableLo             : Nat
  readableHi             : Nat
  writableLo             : Nat
  writableHi             : Nat
  maxKernelExtensionFuel : Nat
  expectedOutput         : Nat

/-- Proof-carrying admission certificate accompanying `CandidateImage`. -/
structure ExtensionCert where
  boundBytes    : List Nat
  relocHash     : Nat
  certifiedProg : List Ring0Instr
  certifiedFuel : Nat

/-- Ring-0 operational state tracking privilege integrity, `KernelCoreFrame` memory isolation,
    callee-saved ABI register `rbp`, interrupt-safe point invariants, and return outcome. -/
structure Ring0State where
  acc                   : Nat
  calleeSaveRbp         : Nat
  privStateIntact       : Bool
  kernelCoreFrameIntact : Bool
  irqSafeEveryStep      : Bool
  terminatedRet         : Option Nat

/-- Initial Ring-0 state at extension entry. -/
def initRing0State (req : AdmissionRequest) : Ring0State := {
  acc                   := 0
  calleeSaveRbp         := req.entryRbp
  privStateIntact       := true
  kernelCoreFrameIntact := true
  irqSafeEveryStep      := true
  terminatedRet         := none
}

/-- Single-instruction Ring-0 transition semantics. -/
def stepRing0Instr (req : AdmissionRequest) (st : Ring0State) (instr : Ring0Instr) : Ring0State :=
  match instr with
  | .compute v =>
    { st with acc := v }
  | .privOp _ =>
    { st with privStateIntact := false }
  | .memRead addr =>
    match inRange addr req.readableLo req.readableHi with
    | true => st
    | false => { st with kernelCoreFrameIntact := false }
  | .memWrite addr v =>
    match inRange addr req.writableLo req.writableHi with
    | true => { st with acc := v }
    | false => { st with kernelCoreFrameIntact := false }
  | .corruptCalleeSave badRbp =>
    { st with calleeSaveRbp := badRbp }
  | .misalignStackOrHoldSpinlock =>
    { st with irqSafeEveryStep := false }
  | .infiniteLoop =>
    st
  | .ret outVal =>
    { st with terminatedRet := some outVal }

/-- Fuel-bounded execution of a Ring-0 instruction stream.
    - Halts cleanly as soon as `st.terminatedRet = some outVal`.
    - `isInfiniteLoop instr = true` consumes one unit of fuel without advancing the
      instruction stream, modeling a backward branch that exhausts fuel without reaching `.ret`. -/
def runRing0Prog (req : AdmissionRequest) : List Ring0Instr → Nat → Ring0State → Ring0State
  | _, 0, st => st
  | [], _ + 1, st => st
  | instr :: rest, fuel + 1, st =>
    match st.terminatedRet with
    | some _ => st
    | none =>
      let st' := stepRing0Instr req st instr
      match isInfiniteLoop instr with
      | true =>
        runRing0Prog req (instr :: rest) fuel st'
      | false =>
        match st'.terminatedRet with
        | some _ => st'
        | none => runRing0Prog req rest fuel st'

/-- Execute a `CandidateImage` in Ring 0 with the request's maximum extension fuel. -/
def runRing0Extension (req : AdmissionRequest) (img : CandidateImage) : Ring0State :=
  runRing0Prog req img.decodedProg req.maxKernelExtensionFuel (initRing0State req)

/-- Complete Ring-0 safety, ABI, interrupt-safety, termination, and functional refinement predicate. -/
def SafeAndRefinesRing0 (req : AdmissionRequest) (finalSt : Ring0State) : Prop :=
  finalSt.privStateIntact = true ∧
  finalSt.kernelCoreFrameIntact = true ∧
  finalSt.calleeSaveRbp = req.entryRbp ∧
  finalSt.irqSafeEveryStep = true ∧
  finalSt.terminatedRet = some req.expectedOutput

/-!
### The Six Consumer-Bound Ring-0 Admission Obligations (`ob1` .. `ob6`)
-/

/-- **Obligation 1 (`ob1_byteBinding`)**:
    Whole-artifact byte sequence equality (`cert.boundBytes = img.bytes`), relocation table
    hash equality, and verified instruction stream equality (`cert.certifiedProg = img.decodedProg`). -/
def ob1_byteBinding (req : AdmissionRequest) (img : CandidateImage) (cert : ExtensionCert) : Bool :=
  natListEq cert.boundBytes img.bytes &&
  natEq cert.relocHash img.relocHash &&
  natEq img.relocHash req.expectedReloc &&
  progEq cert.certifiedProg img.decodedProg

/-- Check that a single instruction is in the unprivileged Ring-0 subset. -/
def instrIsUnprivileged : Ring0Instr → Bool
  | .privOp _ => false
  | _ => true

/-- **Obligation 2 (`ob2_isaPrivilegeConfinement`)**:
    Every instruction in `cert.certifiedProg` is in the permitted unprivileged Ring-0 subset
    (no `wrmsr`, `mov cr3`, `cli`, `lidt`). -/
def ob2_isaPrivilegeConfinement : List Ring0Instr → Bool
  | [] => true
  | i :: rest => instrIsUnprivileged i && ob2_isaPrivilegeConfinement rest

/-- Check that a single instruction's memory accesses stay within the extension's granted slices. -/
def instrMemoryInFrame (req : AdmissionRequest) : Ring0Instr → Bool
  | .memRead addr => inRange addr req.readableLo req.readableHi
  | .memWrite addr _ => inRange addr req.writableLo req.writableHi
  | _ => true

/-- **Obligation 3 (`ob3_frameDisjointMemory`)**:
    Every memory read stays in `[readableLo, readableHi)` and every memory write stays in
    `[writableLo, writableHi)`, strictly disjoint from `KernelCoreFrame`. -/
def ob3_frameDisjointMemory (req : AdmissionRequest) : List Ring0Instr → Bool
  | [] => true
  | i :: rest => instrMemoryInFrame req i && ob3_frameDisjointMemory req rest

/-- Check that an instruction preserves callee-saved registers (`rbp`/`rbx`/`r12..r15`). -/
def instrPreservesCalleeSaves (req : AdmissionRequest) : Ring0Instr → Bool
  | .corruptCalleeSave newRbp => natEq newRbp req.entryRbp
  | _ => true

/-- **Obligation 4 (`ob4_abiCalleeSaveRestoration`)**:
    Callee-saved registers equal their entry values at every step / return boundary. -/
def ob4_abiCalleeSaveRestoration (req : AdmissionRequest) : List Ring0Instr → Bool
  | [] => true
  | i :: rest => instrPreservesCalleeSaves req i && ob4_abiCalleeSaveRestoration req rest

/-- Check that an instruction maintains interrupt-safe stack alignment and lock discipline. -/
def instrIsIrqSafe : Ring0Instr → Bool
  | .misalignStackOrHoldSpinlock => false
  | _ => true

/-- **Obligation 5 (`ob5_interruptSafePointInvariant`)**:
    At every instruction step, the stack pointer satisfies hardware interrupt/IST alignment
    and no spinlock/RCU lock is held across an unmasked instruction step. -/
def ob5_interruptSafePointInvariant : List Ring0Instr → Bool
  | [] => true
  | i :: rest => instrIsIrqSafe i && ob5_interruptSafePointInvariant rest

/-- **Obligation 6 (`ob6_boundedFuelTermination`)**:
    The certificate supplies `certifiedFuel ≤ maxKernelExtensionFuel` such that running
    `cert.certifiedProg` within `req.maxKernelExtensionFuel` steps terminates cleanly with
    `terminatedRet = some req.expectedOutput`. -/
def ob6_boundedFuelTermination (req : AdmissionRequest) (cert : ExtensionCert) : Bool :=
  natLe cert.certifiedFuel req.maxKernelExtensionFuel &&
  match (runRing0Prog req cert.certifiedProg req.maxKernelExtensionFuel (initRing0State req)).terminatedRet with
  | some outVal => natEq outVal req.expectedOutput
  | none => false

/-- Complete 6-Obligation Ring-0 Kernel Extension Admission Gate (`admitKernelExtension`). -/
def admitKernelExtension
    (req : AdmissionRequest) (img : CandidateImage) (cert : ExtensionCert) : Bool :=
  ob1_byteBinding req img cert &&
  ob2_isaPrivilegeConfinement cert.certifiedProg &&
  ob3_frameDisjointMemory req cert.certifiedProg &&
  ob4_abiCalleeSaveRestoration req cert.certifiedProg &&
  ob5_interruptSafePointInvariant cert.certifiedProg &&
  ob6_boundedFuelTermination req cert

/-!
### Invariant Preservation Lemmas for `runRing0Prog`
-/

/-- The four safety invariants preserved step-by-step when Obligations 2, 3, 4, and 5 hold. -/
def SafetyInvariantsHold (req : AdmissionRequest) (st : Ring0State) : Prop :=
  st.privStateIntact = true ∧
  st.kernelCoreFrameIntact = true ∧
  st.calleeSaveRbp = req.entryRbp ∧
  st.irqSafeEveryStep = true

theorem stepRing0Instr_preserves_safety
    (req : AdmissionRequest) (st : Ring0State) (instr : Ring0Instr)
    (hSafe : SafetyInvariantsHold req st)
    (hOb2 : instrIsUnprivileged instr = true)
    (hOb3 : instrMemoryInFrame req instr = true)
    (hOb4 : instrPreservesCalleeSaves req instr = true)
    (hOb5 : instrIsIrqSafe instr = true) :
    SafetyInvariantsHold req (stepRing0Instr req st instr) := by
  rcases hSafe with ⟨hPriv, hMem, hRbp, hIrq⟩
  cases instr with
  | compute v =>
    exact ⟨hPriv, hMem, hRbp, hIrq⟩
  | privOp _ =>
    contradiction
  | memRead addr =>
    change inRange addr req.readableLo req.readableHi = true at hOb3
    change SafetyInvariantsHold req
      (match inRange addr req.readableLo req.readableHi with
      | true => st
      | false => { st with kernelCoreFrameIntact := false })
    rw [hOb3]
    exact ⟨hPriv, hMem, hRbp, hIrq⟩
  | memWrite addr v =>
    change inRange addr req.writableLo req.writableHi = true at hOb3
    change SafetyInvariantsHold req
      (match inRange addr req.writableLo req.writableHi with
      | true => { st with acc := v }
      | false => { st with kernelCoreFrameIntact := false })
    rw [hOb3]
    exact ⟨hPriv, hMem, hRbp, hIrq⟩
  | corruptCalleeSave newRbp =>
    change natEq newRbp req.entryRbp = true at hOb4
    exact ⟨hPriv, hMem, natEq_eq hOb4, hIrq⟩
  | misalignStackOrHoldSpinlock =>
    contradiction
  | infiniteLoop =>
    exact ⟨hPriv, hMem, hRbp, hIrq⟩
  | ret outVal =>
    exact ⟨hPriv, hMem, hRbp, hIrq⟩

theorem runRing0Prog_preserves_safety
    (req : AdmissionRequest) (prog : List Ring0Instr) (fuel : Nat) (st : Ring0State)
    (hSafe : SafetyInvariantsHold req st)
    (hOb2 : ob2_isaPrivilegeConfinement prog = true)
    (hOb3 : ob3_frameDisjointMemory req prog = true)
    (hOb4 : ob4_abiCalleeSaveRestoration req prog = true)
    (hOb5 : ob5_interruptSafePointInvariant prog = true) :
    SafetyInvariantsHold req (runRing0Prog req prog fuel st) := by
  induction fuel generalizing prog st with
  | zero => exact hSafe
  | succ k ih =>
    cases prog with
    | nil => exact hSafe
    | cons instr rest =>
      have hOb2Split := band_eq_true hOb2
      have hOb3Split := band_eq_true hOb3
      have hOb4Split := band_eq_true hOb4
      have hOb5Split := band_eq_true hOb5
      change SafetyInvariantsHold req
        (match st.terminatedRet with
        | some _ => st
        | none =>
          let st' := stepRing0Instr req st instr
          match isInfiniteLoop instr with
          | true =>
            runRing0Prog req (instr :: rest) k st'
          | false =>
            match st'.terminatedRet with
            | some _ => st'
            | none => runRing0Prog req rest k st')
      cases hTerm : st.terminatedRet with
      | some _ => exact hSafe
      | none =>
        have hStepSafe : SafetyInvariantsHold req (stepRing0Instr req st instr) :=
          stepRing0Instr_preserves_safety req st instr hSafe
            hOb2Split.1 hOb3Split.1 hOb4Split.1 hOb5Split.1
        change SafetyInvariantsHold req
          (match isInfiniteLoop instr with
          | true =>
            runRing0Prog req (instr :: rest) k (stepRing0Instr req st instr)
          | false =>
            match (stepRing0Instr req st instr).terminatedRet with
            | some _ => stepRing0Instr req st instr
            | none => runRing0Prog req rest k (stepRing0Instr req st instr))
        cases hLoop : isInfiniteLoop instr with
        | true =>
          exact ih (instr :: rest) (stepRing0Instr req st instr) hStepSafe hOb2 hOb3 hOb4 hOb5
        | false =>
          change SafetyInvariantsHold req
            (match (stepRing0Instr req st instr).terminatedRet with
            | some _ => stepRing0Instr req st instr
            | none => runRing0Prog req rest k (stepRing0Instr req st instr))
          cases hNextTerm : (stepRing0Instr req st instr).terminatedRet with
          | some _ => exact hStepSafe
          | none =>
            exact ih rest (stepRing0Instr req st instr) hStepSafe
              hOb2Split.2 hOb3Split.2 hOb4Split.2 hOb5Split.2

/-- **Master Sufficiency Theorem (`anneal_ring0_extension_admission_soundness`)**:
    If `admitKernelExtension req candidateImage cert = true` (all 6 obligations hold),
    then executing `candidateImage` in Ring 0 from `initRing0State req` within
    `req.maxKernelExtensionFuel` steps is completely safe and refines `req.expectedOutput`
    (`SafeAndRefinesRing0 req (runRing0Extension req candidateImage)`):
    1. No privileged state (`wrmsr`/`cr3`/`cli`/`lidt`) is corrupted;
    2. `KernelCoreFrame` (page tables, IDT, scheduler) is preserved byte-for-byte;
    3. All caller ABI callee-saved registers (`rbp`) are restored to `req.entryRbp`;
    4. Every instruction step remains interrupt-safe (aligned stack, no held spinlock);
    5. Execution terminates within `req.maxKernelExtensionFuel` and returns `req.expectedOutput`. -/
theorem anneal_ring0_extension_admission_soundness
    (req : AdmissionRequest)
    (candidateImage : CandidateImage)
    (cert : ExtensionCert)
    (hAdmit : admitKernelExtension req candidateImage cert = true) :
    SafeAndRefinesRing0 req (runRing0Extension req candidateImage) := by
  have h1_5 := (band_eq_true hAdmit).1
  have hOb6 := (band_eq_true hAdmit).2
  have h1_4 := (band_eq_true h1_5).1
  have hOb5 := (band_eq_true h1_5).2
  have h1_3 := (band_eq_true h1_4).1
  have hOb4 := (band_eq_true h1_4).2
  have h1_2 := (band_eq_true h1_3).1
  have hOb3 := (band_eq_true h1_3).2
  have hOb1 := (band_eq_true h1_2).1
  have hOb2 := (band_eq_true h1_2).2
  -- From Obligation 1, `cert.certifiedProg = candidateImage.decodedProg`
  have hProgEq : cert.certifiedProg = candidateImage.decodedProg :=
    progEq_eq (band_eq_true hOb1).2
  -- Apply `runRing0Prog_preserves_safety`
  have hInitSafe : SafetyInvariantsHold req (initRing0State req) :=
    ⟨rfl, rfl, rfl, rfl⟩
  have hFinalSafe : SafetyInvariantsHold req (runRing0Extension req candidateImage) := by
    unfold runRing0Extension
    rw [← hProgEq]
    exact runRing0Prog_preserves_safety req cert.certifiedProg
      req.maxKernelExtensionFuel (initRing0State req)
      hInitSafe hOb2 hOb3 hOb4 hOb5
  -- From Obligation 6, `terminatedRet = some req.expectedOutput`
  have hOb6Term := (band_eq_true hOb6).2
  cases hTerm : (runRing0Prog req cert.certifiedProg req.maxKernelExtensionFuel (initRing0State req)).terminatedRet with
  | none => rw [hTerm] at hOb6Term; contradiction
  | some outVal =>
    rw [hTerm] at hOb6Term
    have hOutEq : outVal = req.expectedOutput := natEq_eq hOb6Term
    subst hOutEq
    have hExtTerm : (runRing0Extension req candidateImage).terminatedRet = some req.expectedOutput := by
      unfold runRing0Extension
      rw [← hProgEq]
      exact hTerm
    rcases hFinalSafe with ⟨hPriv, hMem, hRbp, hIrq⟩
    exact ⟨hPriv, hMem, hRbp, hIrq, hExtTerm⟩

/-!
### Six-Way Non-Redundancy / Necessity Counterexamples (`drop_ob1_unsound` .. `drop_ob6_unsound`)

We now define the six weakened admission gates `admitWithoutOb1` .. `admitWithoutOb6`,
each omitting *strictly one* of the six obligations while enforcing all remaining five,
and prove that each weakened gate admits a concrete pair `(badImage_i, cert_i)` that
violates `SafeAndRefinesRing0`.
-/

def admitWithoutOb1 (req : AdmissionRequest) (_img : CandidateImage) (cert : ExtensionCert) : Bool :=
  ob2_isaPrivilegeConfinement cert.certifiedProg &&
  ob3_frameDisjointMemory req cert.certifiedProg &&
  ob4_abiCalleeSaveRestoration req cert.certifiedProg &&
  ob5_interruptSafePointInvariant cert.certifiedProg &&
  ob6_boundedFuelTermination req cert

def admitWithoutOb2 (req : AdmissionRequest) (img : CandidateImage) (cert : ExtensionCert) : Bool :=
  ob1_byteBinding req img cert &&
  ob3_frameDisjointMemory req cert.certifiedProg &&
  ob4_abiCalleeSaveRestoration req cert.certifiedProg &&
  ob5_interruptSafePointInvariant cert.certifiedProg &&
  ob6_boundedFuelTermination req cert

def admitWithoutOb3 (req : AdmissionRequest) (img : CandidateImage) (cert : ExtensionCert) : Bool :=
  ob1_byteBinding req img cert &&
  ob2_isaPrivilegeConfinement cert.certifiedProg &&
  ob4_abiCalleeSaveRestoration req cert.certifiedProg &&
  ob5_interruptSafePointInvariant cert.certifiedProg &&
  ob6_boundedFuelTermination req cert

def admitWithoutOb4 (req : AdmissionRequest) (img : CandidateImage) (cert : ExtensionCert) : Bool :=
  ob1_byteBinding req img cert &&
  ob2_isaPrivilegeConfinement cert.certifiedProg &&
  ob3_frameDisjointMemory req cert.certifiedProg &&
  ob5_interruptSafePointInvariant cert.certifiedProg &&
  ob6_boundedFuelTermination req cert

def admitWithoutOb5 (req : AdmissionRequest) (img : CandidateImage) (cert : ExtensionCert) : Bool :=
  ob1_byteBinding req img cert &&
  ob2_isaPrivilegeConfinement cert.certifiedProg &&
  ob3_frameDisjointMemory req cert.certifiedProg &&
  ob4_abiCalleeSaveRestoration req cert.certifiedProg &&
  ob6_boundedFuelTermination req cert

def admitWithoutOb6 (req : AdmissionRequest) (img : CandidateImage) (cert : ExtensionCert) : Bool :=
  ob1_byteBinding req img cert &&
  ob2_isaPrivilegeConfinement cert.certifiedProg &&
  ob3_frameDisjointMemory req cert.certifiedProg &&
  ob4_abiCalleeSaveRestoration req cert.certifiedProg &&
  ob5_interruptSafePointInvariant cert.certifiedProg

/-- Standard reference admission request used across all 6 necessity counterexamples. -/
def stdReq : AdmissionRequest := {
  expectedReloc          := 2
  entryRbp               := 5
  readableLo             := 1
  readableHi             := 3
  writableLo             := 4
  writableHi             := 6
  maxKernelExtensionFuel := 3
  expectedOutput         := 7
}

/-- **Necessity Counterexample 1 (`drop_ob1_unsound`)**:
    Omitting `ob1_byteBinding` (whole-artifact byte & decode binding) while enforcing
    Obligations 2–6 allows a valid certificate for `[.ret 7]` to admit a mutated binary
    image `[.privOp 1, .ret 7]` that executes `wrmsr`/`mov cr3` in Ring 0. -/
theorem drop_ob1_unsound :
    let badImg : CandidateImage := {
      bytes := [1, 2]
      relocHash := 2
      decodedProg := [.privOp 1, .ret 7]
    }
    let cert : ExtensionCert := {
      boundBytes := [1]
      relocHash := 2
      certifiedProg := [.ret 7]
      certifiedFuel := 1
    }
    admitWithoutOb1 stdReq badImg cert = true ∧
    ¬ SafeAndRefinesRing0 stdReq (runRing0Extension stdReq badImg) := by
  refine ⟨rfl, ?_⟩
  intro hSafe
  have hPriv := hSafe.1
  revert hPriv
  decide

/-- **Necessity Counterexample 2 (`drop_ob2_unsound`)**:
    Omitting `ob2_isaPrivilegeConfinement` while enforcing Obligations 1, 3, 4, 5, and 6
    admits an extension that executes a privileged instruction (`.privOp 1`, e.g.,
    overwriting `IA32_LSTAR` syscall entry MSR) before returning `7`. -/
theorem drop_ob2_unsound :
    let badImg : CandidateImage := {
      bytes := [1, 2]
      relocHash := 2
      decodedProg := [.privOp 1, .ret 7]
    }
    let cert : ExtensionCert := {
      boundBytes := [1, 2]
      relocHash := 2
      certifiedProg := [.privOp 1, .ret 7]
      certifiedFuel := 2
    }
    admitWithoutOb2 stdReq badImg cert = true ∧
    ¬ SafeAndRefinesRing0 stdReq (runRing0Extension stdReq badImg) := by
  refine ⟨rfl, ?_⟩
  intro hSafe
  have hPriv := hSafe.1
  revert hPriv
  decide

/-- **Necessity Counterexample 3 (`drop_ob3_unsound`)**:
    Omitting `ob3_frameDisjointMemory` while enforcing Obligations 1, 2, 4, 5, and 6
    admits an extension that writes to address `9` outside `[writableLo, writableHi) = [4, 6)`,
    corrupting `KernelCoreFrame` (host page tables / scheduler runqueue). -/
theorem drop_ob3_unsound :
    let badImg : CandidateImage := {
      bytes := [1, 2]
      relocHash := 2
      decodedProg := [.memWrite 9 8, .ret 7]
    }
    let cert : ExtensionCert := {
      boundBytes := [1, 2]
      relocHash := 2
      certifiedProg := [.memWrite 9 8, .ret 7]
      certifiedFuel := 2
    }
    admitWithoutOb3 stdReq badImg cert = true ∧
    ¬ SafeAndRefinesRing0 stdReq (runRing0Extension stdReq badImg) := by
  refine ⟨rfl, ?_⟩
  intro hSafe
  have hMem := hSafe.2.1
  revert hMem
  decide

/-- **Necessity Counterexample 4 (`drop_ob4_unsound`)**:
    Omitting `ob4_abiCalleeSaveRestoration` while enforcing Obligations 1, 2, 3, 5, and 6
    admits an extension that clobbers the host kernel caller's `rbp` (`corruptCalleeSave 0`)
    without restoring `entryRbp = 5` before `ret 7`. -/
theorem drop_ob4_unsound :
    let badImg : CandidateImage := {
      bytes := [1, 2]
      relocHash := 2
      decodedProg := [.corruptCalleeSave 0, .ret 7]
    }
    let cert : ExtensionCert := {
      boundBytes := [1, 2]
      relocHash := 2
      certifiedProg := [.corruptCalleeSave 0, .ret 7]
      certifiedFuel := 2
    }
    admitWithoutOb4 stdReq badImg cert = true ∧
    ¬ SafeAndRefinesRing0 stdReq (runRing0Extension stdReq badImg) := by
  refine ⟨rfl, ?_⟩
  intro hSafe
  have hRbp := hSafe.2.2.1
  revert hRbp
  decide

/-- **Necessity Counterexample 5 (`drop_ob5_unsound`)**:
    Omitting `ob5_interruptSafePointInvariant` while enforcing Obligations 1, 2, 3, 4, and 6
    admits an extension that misaligns the Ring-0 stack pointer or holds a spinlock across
    an unmasked instruction boundary (`misalignStackOrHoldSpinlock`), violating interrupt safety. -/
theorem drop_ob5_unsound :
    let badImg : CandidateImage := {
      bytes := [1, 2]
      relocHash := 2
      decodedProg := [.misalignStackOrHoldSpinlock, .ret 7]
    }
    let cert : ExtensionCert := {
      boundBytes := [1, 2]
      relocHash := 2
      certifiedProg := [.misalignStackOrHoldSpinlock, .ret 7]
      certifiedFuel := 2
    }
    admitWithoutOb5 stdReq badImg cert = true ∧
    ¬ SafeAndRefinesRing0 stdReq (runRing0Extension stdReq badImg) := by
  refine ⟨rfl, ?_⟩
  intro hSafe
  have hIrq := hSafe.2.2.2.1
  revert hIrq
  decide

/-- **Necessity Counterexample 6 (`drop_ob6_unsound`)**:
    Omitting `ob6_boundedFuelTermination` while enforcing Obligations 1–5 admits an
    unprivileged, memory-safe, ABI-clean, interrupt-aligned extension containing an
    unbounded loop (`[.infiniteLoop]`) that exhausts `maxKernelExtensionFuel` without
    returning (`terminatedRet = none ≠ some 7`), hanging the Ring-0 kernel thread. -/
theorem drop_ob6_unsound :
    let badImg : CandidateImage := {
      bytes := [1]
      relocHash := 2
      decodedProg := [.infiniteLoop]
    }
    let cert : ExtensionCert := {
      boundBytes := [1]
      relocHash := 2
      certifiedProg := [.infiniteLoop]
      certifiedFuel := 3
    }
    admitWithoutOb6 stdReq badImg cert = true ∧
    ¬ SafeAndRefinesRing0 stdReq (runRing0Extension stdReq badImg) := by
  refine ⟨rfl, ?_⟩
  intro hSafe
  have hTerm := hSafe.2.2.2.2
  revert hTerm
  decide

/-- **Master Necessity Theorem (`anneal_ring0_six_obligations_necessary`)**:
    All six obligations of Anneal's Ring-0 Kernel Extension Admission Gate are strictly
    necessary and mutually non-redundant: dropping *any single obligation* `i ∈ {1..6}`
    while enforcing the remaining 5 admits a concrete `(badImg_i, cert_i)` that violates
    `SafeAndRefinesRing0`. -/
theorem anneal_ring0_six_obligations_necessary :
    (∃ img cert, admitWithoutOb1 stdReq img cert = true ∧ ¬ SafeAndRefinesRing0 stdReq (runRing0Extension stdReq img)) ∧
    (∃ img cert, admitWithoutOb2 stdReq img cert = true ∧ ¬ SafeAndRefinesRing0 stdReq (runRing0Extension stdReq img)) ∧
    (∃ img cert, admitWithoutOb3 stdReq img cert = true ∧ ¬ SafeAndRefinesRing0 stdReq (runRing0Extension stdReq img)) ∧
    (∃ img cert, admitWithoutOb4 stdReq img cert = true ∧ ¬ SafeAndRefinesRing0 stdReq (runRing0Extension stdReq img)) ∧
    (∃ img cert, admitWithoutOb5 stdReq img cert = true ∧ ¬ SafeAndRefinesRing0 stdReq (runRing0Extension stdReq img)) ∧
    (∃ img cert, admitWithoutOb6 stdReq img cert = true ∧ ¬ SafeAndRefinesRing0 stdReq (runRing0Extension stdReq img)) := by
  refine ⟨
    ⟨_, _, drop_ob1_unsound⟩,
    ⟨_, _, drop_ob2_unsound⟩,
    ⟨_, _, drop_ob3_unsound⟩,
    ⟨_, _, drop_ob4_unsound⟩,
    ⟨_, _, drop_ob5_unsound⟩,
    ⟨_, _, drop_ob6_unsound⟩
  ⟩

/-!
================================================================================
## Section 4: Linear Capability Transfer & Borrow Across Host-Kernel
## Helper Calls (`StepResult.externalCall` + `Cogent` Linear Frame + `ob3`/`ob5`)
================================================================================

In Anneal (`Trusted/StepResult.lean:92-95`), external environment interactions are
modeled via `StepResult.externalCall`. When a Ring-0 extension invokes a whitelisted
host-kernel helper (e.g., `skb_borrow_header`, `netif_tx_submit`, `kfree_skb`, or
`spin_lock`/`spin_unlock`), capabilities to kernel buffers or locks are borrowed,
consumed/transferred, or newly acquired.

We model three host-kernel helper disciplines (`ExternalHelperKind`):
1. `.borrowReadOnly cap`: Temporarily borrows `cap` (`Cogent`'s `!` bang operator) without
   consuming linear ownership;
2. `.consumeAndTransfer cap`: Transfers linear ownership of `cap` back to the host kernel
   (removing `cap` from the extension's capability set `ownedCaps`);
3. `.allocAcquire cap`: Acquires a fresh linear capability/lock `cap` from the host kernel
   (adding `cap` to `ownedCaps`, which must be released or transferred before extension exit).
-/

abbrev CapId := Nat
abbrev CapSet := List CapId

/-- Constructive membership check for `CapId` in `CapSet`. -/
def hasCap (c : CapId) : CapSet → Bool
  | [] => false
  | x :: xs =>
    match natEq c x with
    | true => true
    | false => hasCap c xs

/-- Remove all occurrences of capability `c` from `CapSet` upon linear consumption/transfer. -/
def removeCap (c : CapId) : CapSet → CapSet
  | [] => []
  | x :: xs =>
    match natEq c x with
    | true => removeCap c xs
    | false => x :: removeCap c xs

/-- Key linear capability erasure lemma: after `removeCap c cs`, `hasCap c` is guaranteed `false`. -/
theorem hasCap_removeCap_self (c : CapId) (cs : CapSet) :
    hasCap c (removeCap c cs) = false := by
  induction cs with
  | nil => rfl
  | cons x xs ih =>
    unfold removeCap
    cases hEq : natEq c x with
    | true =>
      exact ih
    | false =>
      unfold hasCap
      rw [hEq]
      exact ih

/-- Host-kernel helper call kinds (`StepResult.externalCall` categories). -/
inductive ExternalHelperKind where
  | borrowReadOnly     : CapId → ExternalHelperKind
  | consumeAndTransfer : CapId → ExternalHelperKind
  | allocAcquire       : CapId → ExternalHelperKind

/-- Extension instruction stream with capability-checked memory accesses and helper calls. -/
inductive CapInstr where
  | readCapBuf  : CapId → CapInstr
  | writeCapBuf : CapId → Nat → CapInstr
  | callHelper  : ExternalHelperKind → CapInstr
  | retClean    : Nat → CapInstr

/-- Operational state of a Ring-0 extension executing with linear capabilities. -/
structure CapExecState where
  ownedCaps             : CapSet
  kernelCoreFrameIntact : Bool
  useAfterTransferFault : Bool
  returnedVal           : Option Nat

/-- Single-step operational semantics of capability-bearing instructions and helper calls. -/
def stepCapInstr (st : CapExecState) (instr : CapInstr) : CapExecState :=
  match instr with
  | .readCapBuf cap =>
    match hasCap cap st.ownedCaps with
    | true => st
    | false => { st with kernelCoreFrameIntact := false, useAfterTransferFault := true }
  | .writeCapBuf cap _ =>
    match hasCap cap st.ownedCaps with
    | true => st
    | false => { st with kernelCoreFrameIntact := false, useAfterTransferFault := true }
  | .callHelper (.borrowReadOnly cap) =>
    match hasCap cap st.ownedCaps with
    | true => st
    | false => { st with kernelCoreFrameIntact := false, useAfterTransferFault := true }
  | .callHelper (.consumeAndTransfer cap) =>
    match hasCap cap st.ownedCaps with
    | true => { st with ownedCaps := removeCap cap st.ownedCaps }
    | false => { st with kernelCoreFrameIntact := false, useAfterTransferFault := true }
  | .callHelper (.allocAcquire cap) =>
    match hasCap cap st.ownedCaps with
    | false => { st with ownedCaps := cap :: st.ownedCaps }
    | true => { st with kernelCoreFrameIntact := false, useAfterTransferFault := true }
  | .retClean outVal =>
    { st with returnedVal := some outVal }

/-- Run a sequence of capability instructions. -/
def runCapProg : List CapInstr → CapExecState → CapExecState
  | [], st => st
  | i :: rest, st =>
    runCapProg rest (stepCapInstr st i)

/-- Static linear capability type-checker for a single instruction:
    tracks the exact live capability set `CapSet` before and after each step. -/
def checkCapInstr (caps : CapSet) (instr : CapInstr) : Option CapSet :=
  match instr with
  | .readCapBuf cap =>
    match hasCap cap caps with
    | true => some caps
    | false => none
  | .writeCapBuf cap _ =>
    match hasCap cap caps with
    | true => some caps
    | false => none
  | .callHelper (.borrowReadOnly cap) =>
    match hasCap cap caps with
    | true => some caps
    | false => none
  | .callHelper (.consumeAndTransfer cap) =>
    match hasCap cap caps with
    | true => some (removeCap cap caps)
    | false => none
  | .callHelper (.allocAcquire cap) =>
    match hasCap cap caps with
    | false => some (cap :: caps)
    | true => none
  | .retClean _ =>
    some caps

/-- Static linear capability type-checker across an instruction sequence. -/
def checkCapProg : CapSet → List CapInstr → Option CapSet
  | caps, [] => some caps
  | caps, i :: rest =>
    match checkCapInstr caps i with
    | some caps' => checkCapProg caps' rest
    | none => none

/-- Complete Linear Helper Admission Gate with Zero-Net-Acquired-Capability Return Obligation:
    verifies that `checkCapProg` succeeds AND that the final capability set at exit equals
    the expected post-transfer capability set `expectedExitCaps` (e.g. `entryCaps` when all
    acquired locks/buffers must be released before return). -/
def checkLinearHelperGate (entryCaps expectedExitCaps : CapSet) (prog : List CapInstr) : Bool :=
  match checkCapProg entryCaps prog with
  | some finalCaps => natListEq finalCaps expectedExitCaps
  | none => false

/-- **Theorem (`helper_linear_borrow_preserves_frame`)**:
    Invoking a `.borrowReadOnly cap` host-kernel helper when `hasCap cap st.ownedCaps = true`
    preserves `st.ownedCaps` without consuming the capability, preserves `kernelCoreFrameIntact`,
    and triggers no `useAfterTransferFault`. -/
theorem helper_linear_borrow_preserves_frame
    (st : CapExecState) (cap : CapId)
    (hOwned : hasCap cap st.ownedCaps = true)
    (hCore : st.kernelCoreFrameIntact = true)
    (hNoFault : st.useAfterTransferFault = false) :
    let st' := stepCapInstr st (.callHelper (.borrowReadOnly cap))
    st'.ownedCaps = st.ownedCaps ∧
    st'.kernelCoreFrameIntact = true ∧
    st'.useAfterTransferFault = false := by
  dsimp only [stepCapInstr]
  rw [hOwned]
  exact ⟨rfl, hCore, hNoFault⟩

/-- **Theorem (`use_after_transfer_rejected`)**:
    For any initial capability set `caps` and any capability `p`, if an extension invokes
    `.callHelper (.consumeAndTransfer p)` (transferring ownership of `p` to the host kernel),
    any subsequent `.readCapBuf p` or `.writeCapBuf p val` is statically rejected (`= none`)
    by `checkCapProg`. -/
theorem use_after_transfer_rejected (caps : CapSet) (p : CapId) (val : Nat) :
    checkCapProg caps [.callHelper (.consumeAndTransfer p), .readCapBuf p] = none ∧
    checkCapProg caps [.callHelper (.consumeAndTransfer p), .writeCapBuf p val] = none := by
  refine ⟨?_, ?_⟩
  · unfold checkCapProg
    dsimp only [checkCapInstr]
    cases hHas : hasCap p caps with
    | false => rfl
    | true =>
      dsimp only
      unfold checkCapProg
      dsimp only [checkCapInstr]
      rw [hasCap_removeCap_self p caps]
  · unfold checkCapProg
    dsimp only [checkCapInstr]
    cases hHas : hasCap p caps with
    | false => rfl
    | true =>
      dsimp only
      unfold checkCapProg
      dsimp only [checkCapInstr]
      rw [hasCap_removeCap_self p caps]

theorem stepCapInstr_sound
    {st : CapExecState} {instr : CapInstr} {caps' : CapSet}
    (hCore : st.kernelCoreFrameIntact = true)
    (hNoFault : st.useAfterTransferFault = false)
    (hCheck : checkCapInstr st.ownedCaps instr = some caps') :
    let st' := stepCapInstr st instr
    st'.ownedCaps = caps' ∧
    st'.kernelCoreFrameIntact = true ∧
    st'.useAfterTransferFault = false := by
  cases instr with
  | readCapBuf cap =>
    change (match hasCap cap st.ownedCaps with | true => some st.ownedCaps | false => none) = some caps' at hCheck
    cases hHas : hasCap cap st.ownedCaps with
    | false => rw [hHas] at hCheck; contradiction
    | true =>
      rw [hHas] at hCheck
      injection hCheck with hEq
      subst hEq
      dsimp only [stepCapInstr]
      rw [hHas]
      exact ⟨rfl, hCore, hNoFault⟩
  | writeCapBuf cap val =>
    change (match hasCap cap st.ownedCaps with | true => some st.ownedCaps | false => none) = some caps' at hCheck
    cases hHas : hasCap cap st.ownedCaps with
    | false => rw [hHas] at hCheck; contradiction
    | true =>
      rw [hHas] at hCheck
      injection hCheck with hEq
      subst hEq
      dsimp only [stepCapInstr]
      rw [hHas]
      exact ⟨rfl, hCore, hNoFault⟩
  | callHelper helper =>
    cases helper with
    | borrowReadOnly cap =>
      change (match hasCap cap st.ownedCaps with | true => some st.ownedCaps | false => none) = some caps' at hCheck
      cases hHas : hasCap cap st.ownedCaps with
      | false => rw [hHas] at hCheck; contradiction
      | true =>
        rw [hHas] at hCheck
        injection hCheck with hEq
        subst hEq
        dsimp only [stepCapInstr]
        rw [hHas]
        exact ⟨rfl, hCore, hNoFault⟩
    | consumeAndTransfer cap =>
      change (match hasCap cap st.ownedCaps with | true => some (removeCap cap st.ownedCaps) | false => none) = some caps' at hCheck
      cases hHas : hasCap cap st.ownedCaps with
      | false => rw [hHas] at hCheck; contradiction
      | true =>
        rw [hHas] at hCheck
        injection hCheck with hEq
        subst hEq
        dsimp only [stepCapInstr]
        rw [hHas]
        exact ⟨rfl, hCore, hNoFault⟩
    | allocAcquire cap =>
      change (match hasCap cap st.ownedCaps with | false => some (cap :: st.ownedCaps) | true => none) = some caps' at hCheck
      cases hHas : hasCap cap st.ownedCaps with
      | true => rw [hHas] at hCheck; contradiction
      | false =>
        rw [hHas] at hCheck
        injection hCheck with hEq
        subst hEq
        dsimp only [stepCapInstr]
        rw [hHas]
        exact ⟨rfl, hCore, hNoFault⟩
  | retClean outVal =>
    injection hCheck with hEq
    subst hEq
    exact ⟨rfl, hCore, hNoFault⟩

/-- **Theorem (`helper_linear_consume_prevents_use_after_free`)**:
    If `checkCapProg st.ownedCaps prog = some exitCaps`, then executing `prog` from `st`
    is guaranteed free of use-after-transfer / double-release / double-acquire faults
    (`useAfterTransferFault = false`), preserves `kernelCoreFrameIntact = true`, and
    terminates with exact capability set `ownedCaps = exitCaps`. -/
theorem helper_linear_consume_prevents_use_after_free
    (prog : List CapInstr) (st : CapExecState) (exitCaps : CapSet)
    (hCore : st.kernelCoreFrameIntact = true)
    (hNoFault : st.useAfterTransferFault = false)
    (hCheck : checkCapProg st.ownedCaps prog = some exitCaps) :
    let stFinal := runCapProg prog st
    stFinal.ownedCaps = exitCaps ∧
    stFinal.kernelCoreFrameIntact = true ∧
    stFinal.useAfterTransferFault = false := by
  induction prog generalizing st with
  | nil =>
    injection hCheck with hEq
    subst hEq
    exact ⟨rfl, hCore, hNoFault⟩
  | cons instr rest ih =>
    unfold checkCapProg at hCheck
    cases hStepCheck : checkCapInstr st.ownedCaps instr with
    | none => rw [hStepCheck] at hCheck; contradiction
    | some midCaps =>
      rw [hStepCheck] at hCheck
      have hStep := stepCapInstr_sound hCore hNoFault hStepCheck
      rcases hStep with ⟨hMidOwned, hMidCore, hMidNoFault⟩
      unfold runCapProg
      rw [← hMidOwned] at hCheck
      exact ih (stepCapInstr st instr) hMidCore hMidNoFault hCheck

/-- **Theorem (`untracked_helper_leak_across_exit_unsound`)**:
    Without the Zero-Net-Acquired-Capability Return Obligation (`checkLinearHelperGate`),
    an extension that calls `.allocAcquire 9` (acquiring a kernel spinlock or packet buffer)
    and returns via `.retClean 7` without releasing/transferring `9` passes `checkCapProg`
    (`checkCapProg [] leakProg = some [9]`) and leaks capability `9` on exit, whereas
    `checkLinearHelperGate [] [] leakProg = false` rejects it. -/
theorem untracked_helper_leak_across_exit_unsound :
    let leakProg : List CapInstr := [.callHelper (.allocAcquire 9), .retClean 7]
    let initSt : CapExecState := {
      ownedCaps := []
      kernelCoreFrameIntact := true
      useAfterTransferFault := false
      returnedVal := none
    }
    checkCapProg [] leakProg = some [9] ∧
    (runCapProg leakProg initSt).ownedCaps = [9] ∧
    checkLinearHelperGate [] [] leakProg = false := by
  refine ⟨rfl, rfl, rfl⟩

/-- **Theorem (`linear_helper_discipline_leak_free`)**:
    Enforcing `checkLinearHelperGate entryCaps entryCaps prog = true` guarantees both:
    1. Complete memory & capability safety (`kernelCoreFrameIntact = true` and `useAfterTransferFault = false`), and
    2. Strict capability/lock conservation across extension exit (`stFinal.ownedCaps = entryCaps`, zero resource or spinlock leaks). -/
theorem linear_helper_discipline_leak_free
    (prog : List CapInstr) (st : CapExecState)
    (hCore : st.kernelCoreFrameIntact = true)
    (hNoFault : st.useAfterTransferFault = false)
    (hGate : checkLinearHelperGate st.ownedCaps st.ownedCaps prog = true) :
    let stFinal := runCapProg prog st
    stFinal.ownedCaps = st.ownedCaps ∧
    stFinal.kernelCoreFrameIntact = true ∧
    stFinal.useAfterTransferFault = false := by
  unfold checkLinearHelperGate at hGate
  cases hCheck : checkCapProg st.ownedCaps prog with
  | none => rw [hCheck] at hGate; contradiction
  | some finalCaps =>
    rw [hCheck] at hGate
    have hCapsEq : finalCaps = st.ownedCaps := natListEq_eq hGate
    subst hCapsEq
    exact helper_linear_consume_prevents_use_after_free prog st st.ownedCaps hCore hNoFault hCheck

/-!
================================================================================
## Section 5: Formal TCB-Transfer & Equivalence Bridge Between
## Extracted `CertChecker.check` and In-Kernel `.mmb` Proof-Stream Verification
================================================================================

In Anneal (`theory/Anneal/Refinement.lean:1941-1963`), a verified certificate checker
is packaged as:
- `check : Prog → Cert → Bool`
- `check_sound : ∀ p c, check p c = true → Adm p`

When deploying this checker at the Ring-0 admission boundary, we have two choices:
1. **Direct Extracted Boolean Checker**: Execute `check p c` directly in the kernel loader;
2. **Proof-Emitting Certificate Translator (`.mmb` Bridge)**: Run `check p c` in user space
   alongside a translator `compileToMmb : List Nat → Cert → List MmbCmd` that emits an `.mmb`
   proof stream checked in Ring 0 by `consumerBoundMmbGate`.

We prove the **TCB-Transfer & Equivalence Bridge Theorem (`extracted_cert_checker_to_mmb_bridge`)**:
any verified `CertChecker` equipped with a sound `.mmb` proof-stream emitter transfers its
target admissibility guarantee `Adm candidateBytes` through `consumerBoundMmbGate`,
reducing the Ring-0 in-kernel checker to the fixed 4-opcode `.mmb` stack machine.
-/

/-- An Anneal-style verified boolean certificate checker over raw artifact bytes. -/
structure ByteCertChecker (Cert : Type) (Adm : List Nat → Nat → Prop) where
  check       : List Nat → Nat → Cert → Bool
  check_sound : ∀ bytes policy c, check bytes policy c = true → Adm bytes policy

/-- A proof-emitting translator from `Cert` into a consumer-bound `.mmb` certificate,
    paired with a deductive soundness reflection bridge `(Deriv hyps (.byteSafe bytes policy) → Adm bytes policy)`. -/
structure CertToMmbBridge (Cert : Type) (hyps : List PropFormula) (Adm : List Nat → Nat → Prop) where
  translate     : List Nat → Nat → Cert → MmbCert
  translate_ok  : ∀ bytes policy c,
    consumerBoundMmbGate hyps bytes policy (translate bytes policy c) = true →
    Deriv hyps (.byteSafe bytes policy)
  reflect_sound : ∀ bytes policy,
    Deriv hyps (.byteSafe bytes policy) → Adm bytes policy

/-- **Theorem (`extracted_cert_checker_to_mmb_bridge`)**:
    Given a `CertToMmbBridge`, whenever the Ring-0 kernel admission gate verifies the
    translated `.mmb` certificate via `consumerBoundMmbGate hyps candidateBytes reqPolicy (bridge.translate candidateBytes reqPolicy c) = true`,
    both the deductive derivation `Deriv hyps (.byteSafe candidateBytes reqPolicy)` and the
    semantic admissibility property `Adm candidateBytes reqPolicy` hold—without executing
    any domain-specific abstract interpreter or pass logic in Ring 0. -/
theorem extracted_cert_checker_to_mmb_bridge
    {Cert : Type} {hyps : List PropFormula} {Adm : List Nat → Nat → Prop}
    (bridge : CertToMmbBridge Cert hyps Adm)
    (candidateBytes : List Nat) (reqPolicy : Nat) (c : Cert)
    (hGate : consumerBoundMmbGate hyps candidateBytes reqPolicy (bridge.translate candidateBytes reqPolicy c) = true) :
    Deriv hyps (.byteSafe candidateBytes reqPolicy) ∧ Adm candidateBytes reqPolicy := by
  have hDeriv : Deriv hyps (.byteSafe candidateBytes reqPolicy) :=
    consumer_bound_mmb_gate_sound hGate
  exact ⟨hDeriv, bridge.reflect_sound candidateBytes reqPolicy hDeriv⟩

/-- Concrete 3-Step Modus-Ponens `.mmb` Reflection Certificate:
    Given a hypothesis context containing:
    - `hyps[0] = .atom certWitnessId` (the certificate check witness), and
    - `hyps[1] = .imp (.atom certWitnessId) (.byteSafe candidateBytes reqPolicy)` (the `check_sound` theorem),
    the 3-instruction `.mmb` stream `[.loadHyp 1, .loadHyp 0, .applyModusPonens]` is accepted by
    `consumerBoundMmbGate` and deductively proves `.byteSafe candidateBytes reqPolicy`. -/
theorem concrete_mmb_modus_ponens_bridge_sound
    (candidateBytes : List Nat) (reqPolicy certWitnessId : Nat) :
    let hyps : List PropFormula := [
      .atom certWitnessId,
      .imp (.atom certWitnessId) (.byteSafe candidateBytes reqPolicy)
    ]
    let mmbCert : MmbCert := {
      claimedTheorem := .byteSafe candidateBytes reqPolicy
      proofStream := [.loadHyp 1, .loadHyp 0, .applyModusPonens]
    }
    consumerBoundMmbGate hyps candidateBytes reqPolicy mmbCert = true ∧
    Deriv hyps (.byteSafe candidateBytes reqPolicy) := by
  intro hyps mmbCert
  have hGate : consumerBoundMmbGate hyps candidateBytes reqPolicy mmbCert = true := by
    dsimp only [hyps, mmbCert, consumerBoundMmbGate, verifyMmbProof, runMmbStream, stepMmb, listGetOpt]
    rw [formulaEq_refl (.byteSafe candidateBytes reqPolicy)]
    rw [formulaEq_refl (.atom certWitnessId)]
    dsimp only
    rw [formulaEq_refl (.byteSafe candidateBytes reqPolicy)]
    rfl
  exact ⟨hGate, consumer_bound_mmb_gate_sound hGate⟩

/-!
## Axiom Verification (`#print axioms`)
Every theorem in this file must depend on `0` axioms (`no axioms` or at most `propext`/`Quot.sound`,
with zero `sorryAx`, zero `Classical.choice`, and zero `Lean.ofReduceBool`).
-/

#print axioms sel4_graph_refine_cutpoint_composition_soundness
#print axioms frame_disjoint_preservation
#print axioms cogent_linear_in_place_refinement_soundness
#print axioms nonlinear_alias_breaks_in_place_refinement
#print axioms mmb_verifier_sound
#print axioms consumer_bound_mmb_gate_sound
#print axioms unbound_theorem_checker_admits_spoofed_subject
#print axioms anneal_ring0_extension_admission_soundness
#print axioms drop_ob1_unsound
#print axioms drop_ob2_unsound
#print axioms drop_ob3_unsound
#print axioms drop_ob4_unsound
#print axioms drop_ob5_unsound
#print axioms drop_ob6_unsound
#print axioms anneal_ring0_six_obligations_necessary
#print axioms helper_linear_borrow_preserves_frame
#print axioms use_after_transfer_rejected
#print axioms helper_linear_consume_prevents_use_after_free
#print axioms untracked_helper_leak_across_exit_unsound
#print axioms linear_helper_discipline_leak_free
#print axioms extracted_cert_checker_to_mmb_bridge
#print axioms concrete_mmb_modus_ponens_bridge_sound

end DeductiveAndRefinementCertificateKernels
