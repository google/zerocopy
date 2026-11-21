import ToyInline.Inline
import ToyInline.RunLemmas

/-!
# Named hypotheses and observation properties

Each law or side condition is a separate named `Prop`, so that every theorem names exactly
the hypotheses it uses. All of them are decidable on concrete programs.
-/

namespace Toy.Inline

/-! ## The call site -/

/-- Function `f` of `p` is `F`, its block `b` ends in the call `ci`, and the callee of `ci`
is `G`. This names the objects the other hypotheses talk about. -/
def IsCallSite (p : Program) (f b : Nat) (F : Fn) (ci : CallInfo) (G : Fn) : Prop :=
  nth? p.fns f = some F ∧ (nth? F.blocks b).map Block.term = some (.call ci) ∧
    nth? p.fns ci.callee = some G

instance (p : Program) (f b : Nat) (F : Fn) (ci : CallInfo) (G : Fn) :
    Decidable (IsCallSite p f b F ci G) := by
  unfold IsCallSite; exact inferInstance

/-! ## Well-formedness of bodies -/

/-- Every local mentioned by `F` (including the return place read by `ret`) is below
`F.nlocals`. -/
def LocalsBounded (F : Fn) : Prop := ∀ B ∈ F.blocks, ∀ x ∈ B.locals, x < F.nlocals

/-- Every block `F` may jump to (goto, call target, cleanup unwind target) exists. -/
def BlocksBounded (F : Fn) : Prop := ∀ B ∈ F.blocks, ∀ t ∈ B.term.succs, t < F.blocks.length

/-- `inlinedParent` of scope `i` (if any) is a smaller index. -/
def Scope.parentBelow (sc : Scope) (i : Nat) : Bool :=
  match sc.inlinedParent with
  | none => true
  | some t => decide (t < i)

/-- Every `inlinedParent` link of the table points to a strictly smaller index (`t < i` for the
link of scope `i`). This is stronger than acyclicity: an acyclic table with a link from a scope
to a larger index is rejected. -/
def ScopeParentsBelow (scopes : List Scope) : Prop :=
  ∀ i, i < scopes.length → (nth? scopes i).all (·.parentBelow i) = true

/-- A scope table is well formed: scope `0` exists and carries neither `inlined` nor
`inlinedParent` (a clean outermost scope), and every `inlinedParent` link points to a strictly
smaller index (`ScopeParentsBelow`). -/
def ScopeTreeWF (scopes : List Scope) : Prop :=
  nth? scopes 0 = some ⟨none, none⟩ ∧ ScopeParentsBelow scopes

/-- Every scope mentioned by `F`'s statements and calls exists. -/
def ScopeRefsBounded (F : Fn) : Prop := ∀ B ∈ F.blocks, ∀ s ∈ B.scopeRefs, s < F.scopes.length

/-- Scope well-formedness of a function: a well-formed scope table and in-range references. -/
def ScopesWF (F : Fn) : Prop := ScopeTreeWF F.scopes ∧ ScopeRefsBounded F

/-! ## Slot renaming -/

/-- Callee locals `1 ≤ i < G.nlocals` go to host locals at or above `F.nlocals` (a range
disjoint from all declared host locals). -/
def SlotsFresh (cfg : InlineCfg) (F G : Fn) : Prop :=
  ∀ i, i < G.nlocals → 1 ≤ i → F.nlocals ≤ cfg.slot i

/-- Distinct callee locals `1 ≤ i, j < G.nlocals` go to distinct host locals. -/
def SlotsInjective (cfg : InlineCfg) (G : Fn) : Prop :=
  ∀ i, i < G.nlocals → ∀ j, j < G.nlocals → 1 ≤ i → 1 ≤ j → cfg.slot i = cfg.slot j → i = j

/-- The return temporary `t` is a fresh host local, distinct from every callee slot. -/
def TempFresh (t : Local) (cfg : InlineCfg) (F G : Fn) : Prop :=
  F.nlocals ≤ t ∧ ∀ i, i < G.nlocals → 1 ≤ i → cfg.slot i ≠ t

/-! ## Destination mode: the destination is unobservable on the unwind path -/

/-- Whether block `t` of `F` is marked cleanup (`false` if missing). -/
def cleanupAt (F : Fn) (t : BlockId) : Bool := ((nth? F.blocks t).map Block.isCleanup).getD false

/-- Blocks reached by unwinding from a terminator. -/
def Term.unwindTargets : Term → List BlockId
  | .call ci => ci.unwind.blocks
  | .panic u => u.blocks
  | _ => []

/-- Cleanup code is closed: unwind edges lead to cleanup blocks, and cleanup blocks only lead
to cleanup blocks. -/
def CleanupClosed (F : Fn) : Prop :=
  ∀ B ∈ F.blocks, (∀ c ∈ B.term.unwindTargets, cleanupAt F c = true) ∧
    (B.isCleanup = true → ∀ t ∈ B.term.succs, cleanupAt F t = true)

def Stmt.reads : Stmt → List Local
  | .assign _ rv => rv.locals
  | .emit o => o.locals
  | _ => []

def Term.reads : Term → List Local
  | .branch o _ _ => o.locals
  | .call ci => ci.args.flatMap Operand.locals
  | .ret => [0]
  | _ => []

def Block.reads (B : Block) : List Local := B.stmts.flatMap Stmt.reads ++ B.term.reads

/-- No cleanup block of `F` reads local `d`. -/
def DestNotReadInCleanup (F : Fn) (d : Local) : Prop :=
  ∀ B ∈ F.blocks, B.isCleanup = true → d ∉ B.reads

/-! ## Capabilities and ABI -/

/-- `caller ⊇ callee`. -/
def CapsSubset (G F : Fn) : Prop := ∀ c ∈ G.caps, c ∈ F.caps

def Stmt.capOk (caps : CapSet) : Stmt → Bool
  | .needCap c => caps.contains c
  | _ => true

/-- Every `needCap c` in `G` names a capability `G` holds (static legality). -/
def CapLegal (G : Fn) : Prop := ∀ B ∈ G.blocks, ∀ s ∈ B.stmts, s.capOk G.caps = true

/-- No block of `G`, reachable or not, terminates in an ABI-sensitive call. -/
def AbiInsensitive (G : Fn) : Prop := ∀ B ∈ G.blocks, B.term.abiSensitive = false

/-- Host and callee capability lists have the same ABI class under the program-wide map
`p.abi`. -/
def AbiAgree (p : Program) (F G : Fn) : Prop := p.abi F.caps = p.abi G.caps

/-! ## Store-level frame relation (for the slot-renaming lemma) -/

/-- Store-level effect of a statement: the new store and the emitted `out` values. This
auxiliary function covers the store-touching statements `assign` and `emit`; it maps `needCap`
and `loc` to `(st, [])`, so it ignores capability faults and `loc` events (which `step`
does produce). `step_storeStmt` relates it to `step` for `assign` and `emit`. -/
def stmtStore (st : Local → Nat) : Stmt → (Local → Nat) × List Nat
  | .assign x rv => (upd st x (evalRv st rv), [])
  | .emit o => (st, [evalOp st o])
  | .needCap _ => (st, [])
  | .loc _ _ => (st, [])

/-- For the store-touching statements `assign` and `emit`, one `step` of a frame positioned at
that statement updates the store and emits events exactly as `stmtStore` says (each emitted
value `v` becomes the event `out v`), and advances `pc`. -/
theorem step_storeStmt (pol : LocPolicy) (p : Program) (fr : Frame) (rest : List Frame)
    (F : Fn) (B : Block) (s : Stmt)
    (hF : nth? p.fns fr.fn = some F) (hB : nth? F.blocks fr.block = some B)
    (hs : nth? B.stmts fr.pc = some s)
    (hst : (∃ x rv, s = .assign x rv) ∨ (∃ o, s = .emit o)) :
    step pol p (fr :: rest) =
      (.running ({ fr with pc := fr.pc + 1, store := (stmtStore fr.store s).1 } :: rest),
        (stmtStore fr.store s).2.map Event.out) := by
  rcases hst with ⟨x, rv, rfl⟩ | ⟨o, rfl⟩ <;> simp [step, hF, hB, hs, stmtStore]

/-- The merged store `M` agrees with the caller store `C` on the caller locals `L` that are live
across the call, and with the callee store `G` through `ρ` on callee locals below `n`. -/
def FrameRel (ρ : Nat → Local) (n : Nat) (L : List Local) (C G M : Local → Nat) : Prop :=
  (∀ x ∈ L, M x = C x) ∧ (∀ i, i < n → M (ρ i) = G i)

/-- `ρ` is injective on callee locals below `n`. -/
def RenameInjectiveOn (ρ : Nat → Local) (n : Nat) : Prop :=
  ∀ i, i < n → ∀ j, j < n → ρ i = ρ j → i = j

/-- `ρ` maps callee locals below `n` outside the live caller locals `L`. -/
def RenameAvoids (ρ : Nat → Local) (n : Nat) (L : List Local) : Prop :=
  ∀ i, i < n → ρ i ∉ L

/-- Statement `s` mentions only locals below `n`. -/
def StmtLocalsLt (n : Nat) (s : Stmt) : Prop := ∀ x ∈ s.locals, x < n

/-! ## Observation properties (verification conditions) -/

/-- Partial-correctness property over halted observations (covers normal and exceptional
postconditions): every halted observation from `e` satisfies `P`. It holds vacuously for every
`P` when the run from `e` never halts. -/
def TerminalHolds (P : Obs → Prop) (p : Program) (e : Entry) : Prop :=
  ∀ n, (run p n (init p e)).outcome.isSome → P (run p n (init p e))

/-- Every finite observation from `e` (at every step budget `n`, including `n = 0`) satisfies
`S`. This is a safety property in the usual sense only when `S` is prefix-closed
(`PrefixClosed`); the definition does not require it. -/
def SafetyHolds (S : Obs → Prop) (p : Program) (e : Entry) : Prop :=
  ∀ n, S (run p n (init p e))

/-- `S` is closed under observation prefixes. -/
def PrefixClosed (S : Obs → Prop) : Prop := ∀ o o', o.Prefix o' → S o' → S o

/-- The run did not end in an escaped panic. -/
def NoPanic (o : Obs) : Prop := o.outcome ≠ some .unwound

instance : DecidablePred NoPanic := fun o => by unfold NoPanic; exact inferInstance

/-- A halted observation determines `TerminalHolds`. -/
theorem terminalHolds_of_halted {P : Obs → Prop} {p : Program} {e : Entry} {n : Nat}
    (hh : (run p n (init p e)).outcome.isSome) (hP : P (run p n (init p e))) :
    TerminalHolds P p e := by
  intro m hm
  have h : run p m (init p e) = run p n (init p e) := runWith_halted_unique hm hh
  rw [h]
  exact hP

theorem not_terminalHolds_of_halted {P : Obs → Prop} {p : Program} {e : Entry} {n : Nat}
    (hh : (run p n (init p e)).outcome.isSome) (hP : ¬ P (run p n (init p e))) :
    ¬ TerminalHolds P p e :=
  fun h => hP (h n hh)

/-! ## Decidability (all hypotheses are checkable on concrete programs) -/

instance (F : Fn) : Decidable (LocalsBounded F) := by unfold LocalsBounded; exact inferInstance
instance (F : Fn) : Decidable (BlocksBounded F) := by unfold BlocksBounded; exact inferInstance
instance (s : List Scope) : Decidable (ScopeParentsBelow s) := by
  unfold ScopeParentsBelow; exact inferInstance
instance (s : List Scope) : Decidable (ScopeTreeWF s) := by unfold ScopeTreeWF; exact inferInstance
instance (F : Fn) : Decidable (ScopeRefsBounded F) := by
  unfold ScopeRefsBounded; exact inferInstance
instance (F : Fn) : Decidable (ScopesWF F) := by unfold ScopesWF; exact inferInstance
instance (cfg : InlineCfg) (F G : Fn) : Decidable (SlotsFresh cfg F G) := by
  unfold SlotsFresh; exact inferInstance
instance (cfg : InlineCfg) (G : Fn) : Decidable (SlotsInjective cfg G) := by
  unfold SlotsInjective; exact inferInstance
instance (t : Local) (cfg : InlineCfg) (F G : Fn) : Decidable (TempFresh t cfg F G) := by
  unfold TempFresh; exact inferInstance
instance (F : Fn) : Decidable (CleanupClosed F) := by unfold CleanupClosed; exact inferInstance
instance (F : Fn) (d : Local) : Decidable (DestNotReadInCleanup F d) := by
  unfold DestNotReadInCleanup; exact inferInstance
instance (G F : Fn) : Decidable (CapsSubset G F) := by unfold CapsSubset; exact inferInstance
instance (G : Fn) : Decidable (CapLegal G) := by unfold CapLegal; exact inferInstance
instance (G : Fn) : Decidable (AbiInsensitive G) := by unfold AbiInsensitive; exact inferInstance
instance (p : Program) (F G : Fn) : Decidable (AbiAgree p F G) := by
  unfold AbiAgree; exact inferInstance
instance (n : Nat) (s : Stmt) : Decidable (StmtLocalsLt n s) := by
  unfold StmtLocalsLt; exact inferInstance
instance (ρ : Nat → Local) (n : Nat) : Decidable (RenameInjectiveOn ρ n) := by
  unfold RenameInjectiveOn; exact inferInstance
instance (ρ : Nat → Local) (n : Nat) (L : List Local) : Decidable (RenameAvoids ρ n L) := by
  unfold RenameAvoids; exact inferInstance
instance (ρ : Nat → Local) (n : Nat) (L : List Local) (C G M : Local → Nat) :
    Decidable (FrameRel ρ n L C G M) := by
  unfold FrameRel; exact inferInstance

end Toy.Inline
