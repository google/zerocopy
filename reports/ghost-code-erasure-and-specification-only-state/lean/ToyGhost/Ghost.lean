import ToyGhost.Semantics

/-!
# Erasure and the ghost-code restrictions

* `erase` deletes ghost statements: every `ghost` block and every assignment to a
  ghost variable becomes `skip`; real statements are kept and erased recursively.
* `GhostWritesGhost` (restriction R1): ghost blocks assign only ghost variables.
* `RealReadsReal` (restriction R2): real statements read no ghost variable, neither
  through data (right-hand sides, assertion expressions) nor through control
  (conditions of real `if` and `while`).
* `GhostNoDivergeFrom` / `GhostNoFailFrom` (restriction R3, split in two): every
  ghost block that the run of the program from a given initial state starts does
  not diverge (it terminates normally or fails) / does not fail (it terminates
  normally or diverges). Only the conjunction of the two says that every such
  ghost block terminates normally. These are per-run conditions, as delivered by
  verification of the original program; `GhostBlocksNoDiverge` / `GhostBlocksNoFail`
  are the stronger all-states static variants.

R1 and R2 are syntactic and inspect every statement, including unreachable ones,
and they require an explicit `ghost { … }` block around any conditional or loop
whose guard reads a ghost variable (no ghost inference). R3a and R3b are semantic
and constrain only ghost blocks that a run actually reaches.
-/

namespace Toy.Ghost

/-- Erasure: delete ghost blocks and assignments to ghost variables. Real
assignments, assertions, sequencing, and real control flow are kept with their
expressions unchanged.

Encoding choice: `erase P` is again a `Stmt` and is run on a full `Store`. If `P`
violates R2, `erase P` still reads ghost variables (for example `erase (x := g)` is
`x := g`); a compiler targeting real stores only would reject such a program
instead. Under R2 the erased program mentions no ghost variable
(`noGhostVars_erase_of_realReadsReal`) and its real behaviour depends only on the
real part of the initial store (`erase_rbehaves_congr_of_realReadsReal`), so it can
be read as a program over real stores. -/
def erase : Stmt → Stmt
  | .skip => .skip
  | .assign (.real i) e => .assign (.real i) e
  | .assign (.ghost _) _ => .skip
  | .assert e => .assert e
  | .seq s t => .seq (erase s) (erase t)
  | .ite c s t => .ite c (erase s) (erase t)
  | .loop c b => .loop c (erase b)
  | .ghost _ => .skip

/-- `WritesOnlyGhost s`: every assignment anywhere in `s` (including inside nested
ghost blocks) targets a ghost variable. -/
def WritesOnlyGhost : Stmt → Prop
  | .skip => True
  | .assign (.real _) _ => False
  | .assign (.ghost _) _ => True
  | .assert _ => True
  | .seq s t => WritesOnlyGhost s ∧ WritesOnlyGhost t
  | .ite _ s t => WritesOnlyGhost s ∧ WritesOnlyGhost t
  | .loop _ b => WritesOnlyGhost b
  | .ghost s => WritesOnlyGhost s

/-- Restriction R1, `GhostWritesGhost P`: every ghost block of `P` writes only ghost
variables. (Assignments to ghost variables outside ghost blocks are ghost
statements that write a ghost variable by construction.) -/
def GhostWritesGhost : Stmt → Prop
  | .skip => True
  | .assign _ _ => True
  | .assert _ => True
  | .seq s t => GhostWritesGhost s ∧ GhostWritesGhost t
  | .ite _ s t => GhostWritesGhost s ∧ GhostWritesGhost t
  | .loop _ b => GhostWritesGhost b
  | .ghost s => WritesOnlyGhost s

/-- Restriction R2, `RealReadsReal P`: no real statement of `P` reads a ghost
variable, through data or through control. Ghost statements (ghost blocks and
assignments to ghost variables) may read anything. -/
def RealReadsReal : Stmt → Prop
  | .skip => True
  | .assign (.real _) e => e.ReadsOnlyReal
  | .assign (.ghost _) _ => True
  | .assert e => e.ReadsOnlyReal
  | .seq s t => RealReadsReal s ∧ RealReadsReal t
  | .ite c s t => c.ReadsOnlyReal ∧ RealReadsReal s ∧ RealReadsReal t
  | .loop c b => c.ReadsOnlyReal ∧ RealReadsReal b
  | .ghost _ => True

/-- `GhostReach Q n P σ`: every *outermost* ghost block that the run of `P` from `σ`
starts within fuel `n` satisfies `Q` at the state in which it starts. Ghost blocks
nested inside a ghost block are covered only through `Q` applied to the enclosing
block. Assignments and assertions impose nothing here because expression
evaluation is total in this language (it cannot fail or diverge). -/
def GhostReach (Q : Stmt → Store → Prop) : Nat → Stmt → Store → Prop
  | 0, _, _ => True
  | _ + 1, .skip, _ => True
  | _ + 1, .assign _ _, _ => True
  | _ + 1, .assert _, _ => True
  | n + 1, .seq s t, σ =>
      GhostReach Q n s σ ∧ ∀ σ', run n s σ = some (.ok σ') → GhostReach Q n t σ'
  | n + 1, .ite c s t, σ => if c.eval σ = 0 then GhostReach Q n t σ else GhostReach Q n s σ
  | n + 1, .loop c b, σ =>
      if c.eval σ = 0 then True else
        GhostReach Q n b σ ∧ ∀ σ', run n b σ = some (.ok σ') → GhostReach Q n (.loop c b) σ'
  | _ + 1, .ghost s, σ => Q s σ

/-- Restriction R3a (per run), `GhostNoDivergeFrom P σ`: every ghost block started
during the run of `P` from `σ` does not diverge from the state in which it starts;
it terminates normally or fails. (A failing ghost block such as `ghost { assert 0 }`
satisfies this condition; failure is excluded separately by `GhostNoFailFrom`.) -/
def GhostNoDivergeFrom (P : Stmt) (σ : Store) : Prop :=
  ∀ n, GhostReach (fun g τ => ¬ Diverges g τ) n P σ

/-- Restriction R3b (per run), `GhostNoFailFrom P σ`: every ghost block started
during the run of `P` from `σ` does not fail from the state in which it starts;
it terminates normally or diverges. -/
def GhostNoFailFrom (P : Stmt) (σ : Store) : Prop :=
  ∀ n, GhostReach (fun g τ => ¬ Fails g τ) n P σ

/-- `GhostBlocksSatisfy Q P`: every *outermost* ghost block of `P` satisfies `Q` from
*every* state (a static, context-free condition). Ghost blocks nested inside a ghost
block are not checked individually; they are covered by `Q` on the enclosing block. -/
def GhostBlocksSatisfy (Q : Stmt → Store → Prop) : Stmt → Prop
  | .skip => True
  | .assign _ _ => True
  | .assert _ => True
  | .seq s t => GhostBlocksSatisfy Q s ∧ GhostBlocksSatisfy Q t
  | .ite _ s t => GhostBlocksSatisfy Q s ∧ GhostBlocksSatisfy Q t
  | .loop _ b => GhostBlocksSatisfy Q b
  | .ghost s => ∀ σ, Q s σ

/-- Static variant of R3a: no outermost ghost block diverges from any state. -/
def GhostBlocksNoDiverge (P : Stmt) : Prop := GhostBlocksSatisfy (fun g τ => ¬ Diverges g τ) P

/-- Static variant of R3b: no outermost ghost block fails from any state. -/
def GhostBlocksNoFail (P : Stmt) : Prop := GhostBlocksSatisfy (fun g τ => ¬ Fails g τ) P

/-- `NoGhostVars s`: `s` mentions no ghost variable at all (read or written),
including inside ghost blocks. A ghost block that mentions only real variables,
such as `ghost { skip }`, is admitted; whether `s` contains ghost blocks is a
separate question (`NoGhostCode`). -/
def NoGhostVars : Stmt → Prop
  | .skip => True
  | .assign (.real _) e => e.ReadsOnlyReal
  | .assign (.ghost _) _ => False
  | .assert e => e.ReadsOnlyReal
  | .seq s t => NoGhostVars s ∧ NoGhostVars t
  | .ite c s t => c.ReadsOnlyReal ∧ NoGhostVars s ∧ NoGhostVars t
  | .loop c b => c.ReadsOnlyReal ∧ NoGhostVars b
  | .ghost s => NoGhostVars s

/-- `NoGhostCode s`: `s` contains no ghost block and no assignment to a ghost
variable. -/
def NoGhostCode : Stmt → Prop
  | .skip => True
  | .assign (.real _) _ => True
  | .assign (.ghost _) _ => False
  | .assert _ => True
  | .seq s t => NoGhostCode s ∧ NoGhostCode t
  | .ite _ s t => NoGhostCode s ∧ NoGhostCode t
  | .loop _ b => NoGhostCode b
  | .ghost _ => False

/-! ## Structural facts about erasure (fully proved) -/

/-- Erasure removes all ghost code. -/
theorem noGhostCode_erase (P : Stmt) : NoGhostCode (erase P) := by
  induction P with
  | skip => trivial
  | assign x e => cases x <;> trivial
  | assert e => trivial
  | seq s t ihs iht => exact ⟨ihs, iht⟩
  | ite c s t ihs iht => exact ⟨ihs, iht⟩
  | loop c b ih => exact ih
  | ghost s _ => trivial

/-- Under R2, erasure also deletes every *mention* of a ghost variable: the erased
program can be run on real stores alone. -/
theorem noGhostVars_erase_of_realReadsReal {P : Stmt} (h : RealReadsReal P) :
    NoGhostVars (erase P) := by
  induction P with
  | skip => trivial
  | assign x e => cases x <;> simp_all [RealReadsReal, erase, NoGhostVars]
  | assert e => exact h
  | seq s t ihs iht => exact ⟨ihs h.1, iht h.2⟩
  | ite c s t ihs iht => exact ⟨h.1, ihs h.2.1, iht h.2.2⟩
  | loop c b ih => exact ⟨h.1, ih h.2⟩
  | ghost s _ => trivial

/-- Erasure is the identity on programs without ghost code. -/
theorem erase_eq_self_of_noGhostCode {P : Stmt} (h : NoGhostCode P) : erase P = P := by
  induction P with
  | skip => rfl
  | assign x e => cases x <;> simp_all [NoGhostCode, erase]
  | assert e => rfl
  | seq s t ihs iht => simp [erase, ihs h.1, iht h.2]
  | ite c s t ihs iht => simp [erase, ihs h.1, iht h.2]
  | loop c b ih => simp [erase, ih h]
  | ghost s _ => exact h.elim

/-- Erasure is idempotent. -/
theorem erase_erase (P : Stmt) : erase (erase P) = erase P :=
  erase_eq_self_of_noGhostCode (noGhostCode_erase P)

/-- The static all-states condition implies the per-run condition. -/
theorem ghostReach_of_ghostBlocksSatisfy {Q : Stmt → Store → Prop} {P : Stmt}
    (h : GhostBlocksSatisfy Q P) : ∀ n σ, GhostReach Q n P σ := by
  intro n
  induction n generalizing P with
  | zero => intro σ; trivial
  | succ n ih =>
    intro σ
    cases P with
    | skip => trivial
    | assign x e => trivial
    | assert e => trivial
    | seq s t => exact ⟨ih h.1 σ, fun σ' _ => ih h.2 σ'⟩
    | ite c s t =>
      simp only [GhostReach]
      split
      · exact ih h.2 σ
      · exact ih h.1 σ
    | loop c b =>
      simp only [GhostReach]
      split
      · trivial
      · exact ⟨ih (P := b) h σ, fun σ' _ => ih (P := .loop c b) h σ'⟩
    | ghost s => exact h σ

theorem ghostNoDivergeFrom_of_ghostBlocksNoDiverge {P : Stmt}
    (h : GhostBlocksNoDiverge P) (σ : Store) : GhostNoDivergeFrom P σ :=
  fun n => ghostReach_of_ghostBlocksSatisfy h n σ

theorem ghostNoFailFrom_of_ghostBlocksNoFail {P : Stmt}
    (h : GhostBlocksNoFail P) (σ : Store) : GhostNoFailFrom P σ :=
  fun n => ghostReach_of_ghostBlocksSatisfy h n σ

end Toy.Ghost
