import ToyGhost.Specs

/-!
# Concrete programs used as examples, counterexamples, and witnesses

Variables: `x` and `y` are real, `g` is ghost. `σ0` is the all-zero store and
`σ0g` differs from it only in the ghost variable `g`.
-/

namespace Toy.Ghost

/-- Real variable `x`. -/
def x : Var := .real 0
/-- Real variable `y`. -/
def y : Var := .real 1
/-- Ghost variable `g`. -/
def g : Var := .ghost 0

/-- The all-zero store. -/
def σ0 : Store := fun _ => 0
/-- `σ0` with ghost variable `g` set to `1`; same real part as `σ0`. -/
def σ0g : Store := σ0.update g 1

/-- `while 1 do skip`, the canonical diverging loop. -/
def spin : Stmt := .loop (.lit 1) .skip

/-- Ghost write to a real variable: `ghost { x := 1 }`. Violates R1 only. -/
def ceGhostWritesReal : Stmt := .ghost (.assign x (.lit 1))

/-- Implicit flow: `ghost { g := 1 }; if g then x := 1 else skip`. Violates R2 only
(a real `if` branches on a ghost value). -/
def ceImplicitFlow : Stmt :=
  .seq (.ghost (.assign g (.lit 1))) (.ite (.var g) (.assign x (.lit 1)) .skip)

/-- Explicit flow: `ghost { g := 1 }; x := g`. Violates R2 only (data flow). -/
def ceDataFlow : Stmt := .seq (.ghost (.assign g (.lit 1))) (.assign x (.var g))

/-- Non-terminating ghost code: `ghost { while 1 do skip }` (a diverging "lemma").
Violates R3a only. -/
def ceGhostDiverges : Stmt := .ghost spin

/-- Failing ghost assertion: `ghost { assert 0 }`. Violates R3b only. -/
def ceGhostFails : Stmt := .ghost (.assert (.lit 0))

/-- Ghost write to a ghost variable: `ghost { g := 1 }` (positive control). -/
def pcGhostWritesGhost : Stmt := .ghost (.assign g (.lit 1))

/-- Real branch on a real value after ghost code:
`ghost { g := 1 }; if x then x := 1 else skip` (positive control). -/
def pcRealBranch : Stmt :=
  .seq (.ghost (.assign g (.lit 1))) (.ite (.var x) (.assign x (.lit 1)) .skip)

/-- Terminating ghost loop: `ghost { while 0 do skip }` (positive control). -/
def pcGhostTerminatingLoop : Stmt := .ghost (.loop (.lit 0) .skip)

/-- Passing ghost assertion: `ghost { assert 1 }` (positive control). -/
def pcGhostPassingAssert : Stmt := .ghost (.assert (.lit 1))

/-- A ghost-state-dependent ghost loop: `ghost { while g do skip }`. It writes
nothing and real code reads nothing ghost, yet it terminates or diverges depending
on the initial ghost value (a termination channel). -/
def ghostSpinOnG : Stmt := .ghost (.loop (.var g) .skip)

/-- A ghost loop guarded by a *real* variable: `ghost { while x do skip }`. Its
termination depends only on real state, so it leaks nothing about ghost state, but
erasing it turns divergence (from `x ≠ 0`) into termination. -/
def ghostSpinOnX : Stmt := .ghost (.loop (.var x) .skip)

/-- `ghost { while g do skip }; x := 1`: its ghost block diverges from some initial
ghost values but not from others. -/
def ghostSpinThenSetX : Stmt := .seq ghostSpinOnG (.assign x (.lit 1))

/-- `ghost { g := 1 }; while 1 do skip`: satisfies every restriction and diverges
through real code. -/
def ghostThenSpin : Stmt := .seq pcGhostWritesGhost spin

/-- `ghost { g := 1 }; assert 0`: satisfies every restriction and fails at a real
run-time check. -/
def ghostThenRealFail : Stmt := .seq pcGhostWritesGhost (.assert (.lit 0))

/-- Real data flow after ghost code: `ghost { g := 1 }; x := y` (positive control
for the data-flow variant of the implicit-flow counterexample). -/
def pcRealDataFlow : Stmt := .seq (.ghost (.assign g (.lit 1))) (.assign x (.var y))

/-- The witness program
`x := 3; ghost { g := x + 1 }; y := x + x; ghost { assert g = x + 1 }`.
Its ghost assertion holds on every run but fails from some states. -/
def demo : Stmt :=
  .seq (.assign x (.lit 3))
    (.seq (.ghost (.assign g (.add (.var x) (.lit 1))))
      (.seq (.assign y (.add (.var x) (.var x)))
        (.ghost (.assert (.eq (.var g) (.add (.var x) (.lit 1)))))))

/-! ## Behaviour helpers (fully proved) -/

theorem behaves_skip (σ : Store) : Behaves .skip σ (.term σ) := ⟨1, rfl⟩

theorem not_fails_of_term {s : Stmt} {σ σ' : Store} (h : Behaves s σ (.term σ')) :
    ¬ Fails s σ := fun hf => by cases Behaves.unique h hf

theorem not_diverges_of_term {s : Stmt} {σ σ' : Store} (h : Behaves s σ (.term σ')) :
    ¬ Diverges s σ := fun hd => by cases Behaves.unique h hd

theorem not_diverges_of_fails {s : Stmt} {σ : Store} (h : Fails s σ) :
    ¬ Diverges s σ := fun hd => by cases Behaves.unique h hd

theorem not_fails_of_diverges {s : Stmt} {σ : Store} (h : Diverges s σ) :
    ¬ Fails s σ := fun hf => by cases Behaves.unique h hf

theorem run_spin (n : Nat) (σ : Store) : run n spin σ = none := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ m => simp only [spin, run, Expr.eval]; exact ih σ

theorem spin_diverges (σ : Store) : Diverges spin σ := fun n => run_spin n σ

theorem spin_not_fails (σ : Store) : ¬ Fails spin σ := not_fails_of_diverges (spin_diverges σ)

theorem ceGhostDiverges_diverges (σ : Store) : Diverges ceGhostDiverges σ := by
  intro n
  cases n with
  | zero => rfl
  | succ n => exact run_spin n σ

theorem ceGhostFails_fails (σ : Store) : Fails ceGhostFails σ := ⟨2, rfl⟩

theorem realPart_update_ghost (σ : Store) (i : Nat) (v : Int) :
    realPart (σ.update (.ghost i) v) = realPart σ := by
  funext j; simp [realPart, Store.update]

theorem realPart_σ0g : realPart σ0g = realPart σ0 := realPart_update_ghost σ0 0 1

theorem realPart_update_x_ne {σ : Store} (h : σ x = 0) :
    realPart (σ.update x 1) ≠ realPart σ := by
  intro he
  have := congrFun he 0
  simp [realPart, Store.update, x] at this
  simp [x] at h
  omega

end Toy.Ghost
