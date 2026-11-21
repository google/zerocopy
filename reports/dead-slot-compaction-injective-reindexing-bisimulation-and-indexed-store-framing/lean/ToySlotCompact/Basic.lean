/-!
# Slot compaction: the toy language

A small control-flow-graph language over `N` local slots, its small-step semantics, per-point
liveness masks, compaction maps, and the compacted program.

This is a toy model. It is meant to capture the shape of a compiler pass that renumbers a
function's local slots (unused-local removal, stack-slot sharing) and of a verification pipeline
that reasons about stores indexed by slot numbers. It does not model any real intermediate
representation.
-/

namespace Toy.SlotCompact

/-- A store gives a natural-number value to each of `N` local slots. -/
abbrev Store (N : Nat) := Fin N → Nat

/-- Point update of a store: slot `i` now holds `v`; every other slot is unchanged. -/
def upd {N : Nat} (σ : Store N) (i : Fin N) (v : Nat) : Store N :=
  fun j => if j = i then v else σ j

@[simp] theorem upd_same {N : Nat} (σ : Store N) (i : Fin N) (v : Nat) : upd σ i v i = v := by
  simp [upd]

theorem upd_other {N : Nat} (σ : Store N) {i j : Fin N} (v : Nat) (h : j ≠ i) :
    upd σ i v j = σ j := by
  simp [upd, h]

/-- Pure expressions over slots. -/
inductive Expr (N : Nat) where
  | const (n : Nat)
  | slot (i : Fin N)
  | add (a b : Expr N)
  deriving DecidableEq, Repr

/-- Evaluation of an expression in a store. -/
def Expr.eval {N : Nat} (σ : Store N) : Expr N → Nat
  | .const n => n
  | .slot i => σ i
  | .add a b => a.eval σ + b.eval σ

/-- `e.reads i` holds iff slot `i` occurs in `e`. -/
def Expr.reads {N : Nat} : Expr N → Fin N → Bool
  | .const _, _ => false
  | .slot j, i => decide (j = i)
  | .add a b, i => a.reads i || b.reads i

/-- Substitution of an expression for every slot occurrence. -/
def Expr.subst {N M : Nat} (f : Fin N → Expr M) : Expr N → Expr M
  | .const n => .const n
  | .slot i => f i
  | .add a b => .add (a.subst f) (b.subst f)

/-- Evaluation only looks at the slots an expression reads. -/
theorem Expr.eval_congr {N : Nat} (e : Expr N) {σ τ : Store N}
    (h : ∀ i, e.reads i = true → σ i = τ i) : e.eval σ = e.eval τ := by
  induction e with
  | const n => rfl
  | slot j => exact h j (by simp [Expr.reads])
  | add a b iha ihb =>
    simp only [Expr.eval]
    rw [iha (fun i hi => h i (by simp [Expr.reads, hi])),
      ihb (fun i hi => h i (by simp [Expr.reads, hi]))]

/-- Instructions. Every instruction except `branch` and `halt` falls through to `pc + 1`.

* `assign d e`: slot `d` receives the value of `e`.
* `storageLive i`, `storageDead i`: storage markers. In this toy both discard the slot's contents
  (the slot is reset to `0`); undefined behaviour on access to dead storage is not modeled.
* `dbg e`: a debug or reflection observation. It emits the value of `e` as an observable event
  and does not count as a use for liveness (debug reads do not extend live ranges).
* `nop`: does nothing.
* `branch c t f`: jumps to `f` if `c` evaluates to `0`, and to `t` otherwise.
* `halt outs`: stops and emits the values of the slots listed in `outs` (the outputs, in order) as
  an observable result; they count as uses for liveness. -/
inductive Instr (N : Nat) where
  | assign (d : Fin N) (e : Expr N)
  | storageLive (i : Fin N)
  | storageDead (i : Fin N)
  | dbg (e : Expr N)
  | nop
  | branch (c : Expr N) (t f : Nat)
  | halt (outs : List (Fin N))
  deriving DecidableEq, Repr

/-- A program is a list of instructions indexed by the program counter. -/
abbrev Prog (N : Nat) := List (Instr N)

/-- A machine state: program counter and store. -/
structure State (N : Nat) where
  pc : Nat
  st : Store N

/-- The result of one step: a successor state with an optional observable event, a halted state
together with the emitted output values, or stuck (program counter outside the program). -/
inductive Res (N : Nat) where
  | running (s : State N) (ev : Option Nat)
  | halted (s : State N) (out : List Nat)
  | stuck

/-- The effect of one instruction on a state. -/
def stepInstr {N : Nat} : Instr N → State N → Res N
  | .assign d e, ⟨pc, σ⟩ => .running ⟨pc + 1, upd σ d (e.eval σ)⟩ none
  | .storageLive i, ⟨pc, σ⟩ => .running ⟨pc + 1, upd σ i 0⟩ none
  | .storageDead i, ⟨pc, σ⟩ => .running ⟨pc + 1, upd σ i 0⟩ none
  | .dbg e, ⟨pc, σ⟩ => .running ⟨pc + 1, σ⟩ (some (e.eval σ))
  | .nop, ⟨pc, σ⟩ => .running ⟨pc + 1, σ⟩ none
  | .branch c t f, ⟨_, σ⟩ => .running ⟨if c.eval σ = 0 then f else t, σ⟩ none
  | .halt outs, s => .halted s (outs.map s.st)

/-- One deterministic small step of a program. -/
def step {N : Nat} (p : Prog N) (s : State N) : Res N :=
  match p[s.pc]? with
  | none => .stuck
  | some ins => stepInstr ins s

theorem step_of_getElem? {N : Nat} {p : Prog N} {s : State N} {ins : Instr N}
    (h : p[s.pc]? = some ins) : step p s = stepInstr ins s := by
  simp [step, h]

theorem step_of_getElem?_none {N : Nat} {p : Prog N} {s : State N}
    (h : p[s.pc]? = none) : step p s = .stuck := by
  simp [step, h]

/-! ## Liveness masks -/

/-- A liveness annotation: the claimed live-in mask at every program point. -/
abbrev Ann (N : Nat) := Nat → Fin N → Bool

/-- Slots an instruction reads for its semantics (liveness uses). Debug reads are excluded. -/
def Instr.uses {N : Nat} : Instr N → Fin N → Bool
  | .assign _ e, i => e.reads i
  | .branch c _ _, i => c.reads i
  | .halt outs, i => decide (i ∈ outs)
  | _, _ => false

/-- Slots an instruction overwrites (liveness kills): assignment targets and storage markers. -/
def Instr.defs {N : Nat} : Instr N → Fin N → Bool
  | .assign d _, i => decide (d = i)
  | .storageLive j, i => decide (j = i)
  | .storageDead j, i => decide (j = i)
  | _, _ => false

/-- Control-flow successors of an instruction at `pc`. -/
def Instr.succs {N : Nat} (pc : Nat) : Instr N → List Nat
  | .branch _ t f => [t, f]
  | .halt _ => []
  | _ => [pc + 1]

/-- Every semantic read at a point is of a slot the mask declares live there (the "gen" half of
the backward liveness inequality). -/
def ReadsLive {N : Nat} (p : Prog N) (L : Ann N) : Prop :=
  ∀ (pc : Nat) (ins : Instr N), p[pc]? = some ins → ∀ i, ins.uses i = true → L pc i = true

/-- The mask is closed under the backward transfer: a slot live at a successor and not
overwritten by the instruction is live before it (the "transfer" half of the backward liveness
inequality). -/
def TransferClosed {N : Nat} (p : Prog N) (L : Ann N) : Prop :=
  ∀ (pc : Nat) (ins : Instr N), p[pc]? = some ins → ∀ s ∈ ins.succs pc, ∀ i, L s i = true → ins.defs i = false →
    L pc i = true

/-- Every debug observation reads only slots the mask declares live at that point. -/
def DbgReadsLive {N : Nat} (p : Prog N) (L : Ann N) : Prop :=
  ∀ (pc : Nat) (e : Expr N), p[pc]? = some (.dbg e) → ∀ i, e.reads i = true → L pc i = true

/-- The global live set: slots that the mask declares live at some point of the program. These
are the slots a compaction keeps. -/
def Kept {N : Nat} (p : Prog N) (L : Ann N) (i : Fin N) : Bool :=
  (List.range p.length).any (fun pc => L pc i)

theorem kept_of_getElem? {N : Nat} {p : Prog N} {L : Ann N} {pc : Nat} {ins : Instr N}
    (h : p[pc]? = some ins) {i : Fin N} (hi : L pc i = true) : Kept p L i = true := by
  have hlt : pc < p.length := by
    rcases List.getElem?_eq_some_iff.mp h with ⟨hlt, _⟩
    exact hlt
  exact List.any_eq_true.mpr ⟨pc, List.mem_range.mpr hlt, hi⟩

/-- Every semantic read anywhere in the program is of a kept slot. Weaker than `ReadsLive`. -/
def ReadsKept {N : Nat} (p : Prog N) (L : Ann N) : Prop :=
  ∀ (pc : Nat) (ins : Instr N), p[pc]? = some ins → ∀ i, ins.uses i = true → Kept p L i = true

/-- Every debug observation reads only kept slots. Weaker than `DbgReadsLive`. -/
def DbgReadsKept {N : Nat} (p : Prog N) (L : Ann N) : Prop :=
  ∀ (pc : Nat) (e : Expr N), p[pc]? = some (.dbg e) → ∀ i, e.reads i = true → Kept p L i = true

theorem readsKept_of_readsLive {N : Nat} {p : Prog N} {L : Ann N} (h : ReadsLive p L) :
    ReadsKept p L :=
  fun pc ins hins i hi => kept_of_getElem? hins (h pc ins hins i hi)

theorem dbgReadsKept_of_dbgReadsLive {N : Nat} {p : Prog N} {L : Ann N} (h : DbgReadsLive p L) :
    DbgReadsKept p L :=
  fun pc e hins i hi => kept_of_getElem? hins (h pc e hins i hi)

/-! ## Compaction -/

/-- A compaction map: a renumbering of the kept slots (those live somewhere) into `M` slots.
It need not be injective; injectivity and weaker interference conditions are separate
hypotheses. -/
abbrev Compaction {N : Nat} (p : Prog N) (L : Ann N) (M : Nat) :=
  {i : Fin N // Kept p L i = true} → Fin M

/-- The compaction map as a partial map on all slots (`none` on dropped slots). -/
def Compaction.get? {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M) (i : Fin N) :
    Option (Fin M) :=
  if h : Kept p L i = true then some (π ⟨i, h⟩) else none

theorem Compaction.get?_of_kept {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M)
    {i : Fin N} (h : Kept p L i = true) : π.get? i = some (π ⟨i, h⟩) := by
  simp [Compaction.get?, h]

theorem Compaction.get?_of_not_kept {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M)
    {i : Fin N} (h : ¬ Kept p L i = true) : π.get? i = none := by
  simp [Compaction.get?, h]

/-- Rewriting a slot occurrence: a kept slot is renamed through `π`; a dropped slot (which a
well-formed program never reads) is replaced by the constant `0`. -/
def Compaction.slotExpr {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M)
    (i : Fin N) : Expr M :=
  match π.get? i with
  | some k => .slot k
  | none => .const 0

/-- Rewriting an expression through `π`. -/
def compactExpr {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M) (e : Expr N) :
    Expr M :=
  e.subst π.slotExpr

/-- Rewriting an instruction through `π`. Writes to dropped slots (slots the mask declares live
nowhere) and the storage markers of dropped slots become `nop`; every other slot occurrence is
renamed. Writes to kept slots are kept even at points where the written slot is dead. -/
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

/-- The compacted program: every instruction rewritten through `π`, at the same program point. -/
def compact {N M : Nat} (p : Prog N) (L : Ann N) (π : Compaction p L M) : Prog M :=
  p.map (compactInstr π)

theorem compact_getElem? {N M : Nat} (p : Prog N) (L : Ann N) (π : Compaction p L M) (pc : Nat) :
    (compact p L π)[pc]? = (p[pc]?).map (compactInstr π) := by
  simp [compact]

theorem step_compact_of_getElem? {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M)
    {pc : Nat} {ins : Instr N} (h : p[pc]? = some ins) (σ' : Store M) :
    step (compact p L π) ⟨pc, σ'⟩ = stepInstr (compactInstr π ins) ⟨pc, σ'⟩ :=
  step_of_getElem? (s := ⟨pc, σ'⟩) (by simp [compact_getElem?, h])

theorem step_compact_of_getElem?_none {N M : Nat} {p : Prog N} {L : Ann N}
    (π : Compaction p L M) {pc : Nat} (h : p[pc]? = none) (σ' : Store M) :
    step (compact p L π) ⟨pc, σ'⟩ = .stuck :=
  step_of_getElem?_none (s := ⟨pc, σ'⟩) (by simp [compact_getElem?, h])

/-! ## Relations and bisimulation -/

/-- The live-slot compaction relation: same program counter, and the compacted store holds, at
`π i`, the value of every kept slot `i` that the mask declares live at the current point. -/
def CompactRel {N M : Nat} (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (s : State N) (s' : State M) : Prop :=
  s'.pc = s.pc ∧ ∀ (i : Fin N) (h : Kept p L i = true), L s.pc i = true → s'.st (π ⟨i, h⟩) = s.st i

/-- The stronger relation for injective compactions: every kept slot is tracked, live or not. -/
def KeptRel {N M : Nat} (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (s : State N) (s' : State M) : Prop :=
  s'.pc = s.pc ∧ ∀ (i : Fin N) (h : Kept p L i = true), s'.st (π ⟨i, h⟩) = s.st i

/-- Matching of one-step results under a state relation `R`, including equality of debug events
and of emitted output values. -/
def ResRel {N M : Nat} (R : State N → State M → Prop) : Res N → Res M → Prop
  | .running s e, .running s' e' => e = e' ∧ R s s'
  | .halted s o, .halted s' o' => o = o' ∧ R s s'
  | .stuck, .stuck => True
  | _, _ => False

/-- Matching of one-step results under `R`, ignoring debug events (output values are still
compared). -/
def ResRelS {N M : Nat} (R : State N → State M → Prop) : Res N → Res M → Prop
  | .running s _, .running s' _ => R s s'
  | .halted s o, .halted s' o' => o = o' ∧ R s s'
  | .stuck, .stuck => True
  | _, _ => False

/-- `R` is a lockstep bisimulation between `p` and `q`: from related states both programs take
one step with equal events into related states, or both halt with equal output values in related
states, or both are stuck. Because `step` is a function, this one clause gives both simulation
directions. -/
def LockstepBisim {N M : Nat} (p : Prog N) (q : Prog M) (R : State N → State M → Prop) : Prop :=
  ∀ s s', R s s' → ResRel R (step p s) (step q s')

/-- Lockstep bisimulation ignoring debug events (used for verification conditions, which do not
observe debug events). -/
def SilentBisim {N M : Nat} (p : Prog N) (q : Prog M) (R : State N → State M → Prop) : Prop :=
  ∀ s s', R s s' → ResRelS R (step p s) (step q s')

theorem silentBisim_of_lockstepBisim {N M : Nat} {p : Prog N} {q : Prog M}
    {R : State N → State M → Prop} (h : LockstepBisim p q R) : SilentBisim p q R := by
  intro s s' hs
  have := h s s' hs
  revert this
  cases step p s <;> cases step q s' <;> simp_all [ResRel, ResRelS]

/-! ## Interference conditions for non-injective compactions -/

/-- An assignment never clobbers a different slot that is live after it and shares its target. -/
def NoAssignClobber {N M : Nat} (p : Prog N) (L : Ann N) (π : Compaction p L M) : Prop :=
  ∀ (pc : Nat) (d : Fin N) (e : Expr N), p[pc]? = some (.assign d e) → ∀ (hd : Kept p L d = true) (i : Fin N)
    (hi : Kept p L i = true), i ≠ d → L (pc + 1) i = true → π ⟨i, hi⟩ ≠ π ⟨d, hd⟩

/-- A storage marker never resets a different slot that is live after it and shares its target. -/
def NoMarkerClobber {N M : Nat} (p : Prog N) (L : Ann N) (π : Compaction p L M) : Prop :=
  ∀ (pc : Nat) (j : Fin N), (p[pc]? = some (.storageLive j) ∨ p[pc]? = some (.storageDead j)) →
    ∀ (hj : Kept p L j = true) (i : Fin N) (hi : Kept p L i = true), i ≠ j →
      L (pc + 1) i = true → π ⟨i, hi⟩ ≠ π ⟨j, hj⟩

/-- `π` is injective on the kept slots live at `pc`. -/
def InjOnLiveAt {N M : Nat} (p : Prog N) (L : Ann N) (π : Compaction p L M) (pc : Nat) : Prop :=
  ∀ (i j : Fin N) (hi : Kept p L i = true) (hj : Kept p L j = true),
    L pc i = true → L pc j = true → π ⟨i, hi⟩ = π ⟨j, hj⟩ → i = j

theorem noAssignClobber_of_injective {N M : Nat} {p : Prog N} {L : Ann N} {π : Compaction p L M}
    (h : Function.Injective π) : NoAssignClobber p L π := by
  intro pc d e _ hd i hi hne _ heq
  exact hne (congrArg Subtype.val (h heq))

theorem noMarkerClobber_of_injective {N M : Nat} {p : Prog N} {L : Ann N} {π : Compaction p L M}
    (h : Function.Injective π) : NoMarkerClobber p L π := by
  intro pc j _ hj i hi hne _ heq
  exact hne (congrArg Subtype.val (h heq))

theorem injOnLiveAt_of_injective {N M : Nat} {p : Prog N} {L : Ann N} {π : Compaction p L M}
    (h : Function.Injective π) (pc : Nat) : InjOnLiveAt p L π pc := by
  intro i j hi hj _ _ heq
  exact congrArg Subtype.val (h heq)

/-! ## Store transport along a compaction -/

/-- Pull a compacted store back to an original store (dropped slots read as `0`). -/
def pullStore {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M) (σ' : Store M) :
    Store N :=
  fun i => match π.get? i with
    | some k => σ' k
    | none => 0

/-- Push an original store forward to a compacted store, using the slots live at `pc`: target slot
`k` receives the value of the first slot live at `pc` that `π` sends to `k` (or `0`). -/
def pushStore {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M) (pc : Nat)
    (σ : Store N) : Store M :=
  fun k => match (List.finRange N).find? (fun i => L pc i && decide (π.get? i = some k)) with
    | some i => σ i
    | none => 0

theorem pullStore_kept {N M : Nat} {p : Prog N} {L : Ann N} (π : Compaction p L M)
    (σ' : Store M) {i : Fin N} (h : Kept p L i = true) : pullStore π σ' i = σ' (π ⟨i, h⟩) := by
  simp [pullStore, π.get?_of_kept h]

theorem pushStore_live {N M : Nat} {p : Prog N} {L : Ann N} {π : Compaction p L M} {pc : Nat}
    (hinj : InjOnLiveAt p L π pc) (σ : Store N) {i : Fin N} (hk : Kept p L i = true)
    (hl : L pc i = true) : pushStore π pc σ (π ⟨i, hk⟩) = σ i := by
  unfold pushStore
  cases hf : (List.finRange N).find? (fun j => L pc j && decide (π.get? j = some (π ⟨i, hk⟩)))
    with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf i (List.mem_finRange i)
    simp [hl, π.get?_of_kept hk] at this
  | some j =>
    have hj := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    obtain ⟨hlj, hgj⟩ := hj
    by_cases hkj : Kept p L j = true
    · rw [π.get?_of_kept hkj] at hgj
      have : j = i := hinj j i hkj hk hlj hl (Option.some.inj hgj)
      simp [this]
    · rw [π.get?_of_not_kept hkj] at hgj
      exact absurd hgj (by simp)

end Toy.SlotCompact
