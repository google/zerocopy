/-
Toy.RedGreen.Examples
=====================

Concrete instances used by the definition examples, counterexamples and
non-vacuity theorems.  Values and fingerprints are natural numbers.
-/
import Toy.RedGreen.Basic

namespace Toy.RedGreen

/-- Generic constructor of a consistent database: execute every query from
scratch in state `inp` (fuel `n`) and record its trace and result; queries that
panic or run out of fuel get no entry. -/
def recordAll {Q I V F : Type} (rules : Rules Q I V) (fp : V → F) (inp : I → V) (n : Nat) :
    OldDB Q I V F :=
  fun q => match (rules q).runT (eval rules inp n) fp with
    | (.val v, tr) => some ⟨tr, v⟩
    | (.panic, _) => none
    | (.stuck, _) => none

theorem recordAll_consistent {Q I V F : Type} (rules : Rules Q I V) (fp : V → F) (inp : I → V)
    (n : Nat) : DBConsistent rules fp inp (recordAll rules fp inp n) := by
  intro q e h
  refine ⟨n, ?_⟩
  unfold recordAll at h
  revert h
  cases (rules q).runT (eval rules inp n) fp with
  | mk o tr =>
    cases o with
    | val v => intro h; cases h; rfl
    | panic => intro h; cases h
    | stuck => intro h; cases h

/-! ## Key types, fingerprints, input states -/

/-- Query keys of examples D and C. -/
inductive QK : Type where
  | top
  | guard
  | risky
  deriving DecidableEq, Repr

/-- Query keys of the remaining examples. -/
inductive Q3 : Type where
  | top
  | a
  | b
  deriving DecidableEq, Repr

/-- Input keys. -/
inductive IK : Type where
  | x
  | y
  deriving DecidableEq, Repr

/-- Identity fingerprints on `Nat` (collision-free). -/
def fpId : Nat → Nat := fun v => v

/-- Parity fingerprints (collide on all values of equal parity). -/
def fpParity : Nat → Nat := fun v => v % 2

/-- Saturating fingerprints: `min v 10` (collide on all values `≥ 10`). -/
def fpSat : Nat → Nat := fun v => min v 10

/-- The input state `x = a, y = b`. -/
def inpXY (a b : Nat) : IK → Nat
  | .x => a
  | .y => b

/-! ## Example D: a recorded dependency that becomes dead and panics -/

/-- `guard` tests whether `x ≠ 0`; `risky` divides by `x` and panics when
`x = 0`; `top` fetches `guard`, and only if it is `1` fetches `risky`.  In a
state with `x = 0`, `risky` is a dead dependency of `top`. -/
def rulesD : Rules QK IK Nat
  | .guard => .fetch (.inr .x) fun v => .ret (if v = 0 then 0 else 1)
  | .risky => .fetch (.inr .x) fun v => if v = 0 then .panic else .ret (100 / v)
  | .top => .fetch (.inl .guard) fun g =>
      if g = 0 then .ret 0 else .fetch (.inl .risky) fun r => .ret r

/-! ## Example C: a code-level cycle that is dead in both states -/

/-- Like `rulesD`, but when `x = 0` the query `risky` fetches `top` instead of
panicking.  The code contains the cycle `top → risky → top`, yet in every state
at most one direction is live: `top` fetches `risky` only when `x ≠ 0`, and
`risky` fetches `top` only when `x = 0`.  Both states below terminate. -/
def rulesC : Rules QK IK Nat
  | .guard => .fetch (.inr .x) fun v => .ret (if v = 0 then 0 else 1)
  | .risky => .fetch (.inr .x) fun v => if v = 0 then .fetch (.inl .top) .ret else .ret (100 / v)
  | .top => .fetch (.inl .guard) fun g =>
      if g = 0 then .ret 0 else .fetch (.inl .risky) fun r => .ret r

/-- Old state of examples D and C (`x = 5`). -/
def oldD : IK → Nat := inpXY 5 0
/-- New state of examples D and C (`x = 0`). -/
def newD : IK → Nat := inpXY 0 0

/-- Database recorded from scratch in the old state of example D. -/
def odbD : OldDB QK IK Nat Nat := recordAll rulesD fpId oldD 10
/-- Database recorded from scratch in the old state of example C. -/
def odbC : OldDB QK IK Nat Nat := recordAll rulesC fpId oldD 10

theorem odbD_top : odbD .top = some ⟨[(.inl .guard, 1), (.inl .risky, 20)], 20⟩ := by decide
theorem odbD_guard : odbD .guard = some ⟨[(.inr .x, 5)], 1⟩ := by decide
theorem odbD_risky : odbD .risky = some ⟨[(.inr .x, 5)], 20⟩ := by decide
theorem odbC_top : odbC .top = some ⟨[(.inl .guard, 1), (.inl .risky, 20)], 20⟩ := by decide
theorem odbC_risky : odbC .risky = some ⟨[(.inr .x, 5)], 20⟩ := by decide

/-! ## Example K: early cutoff -/

/-- `a` reads `x` but always returns `0`; `top` returns `a + y`.  When only `x`
changes, `a` must be re-executed but reproduces its old value, so `top`'s
recorded dependencies are all unchanged. -/
def rulesK : Rules Q3 IK Nat
  | .a => .fetch (.inr .x) fun _ => .ret 0
  | .b => .ret 7
  | .top => .fetch (.inl .a) fun m => .fetch (.inr .y) fun w => .ret (m + w)

def oldK : IK → Nat := inpXY 1 2
def newK : IK → Nat := inpXY 3 2
def odbK : OldDB Q3 IK Nat Nat := recordAll rulesK fpId oldK 10

theorem odbK_top : odbK .top = some ⟨[(.inl .a, 0), (.inr .y, 2)], 2⟩ := by decide
theorem odbK_a : odbK .a = some ⟨[(.inr .x, 1)], 0⟩ := by decide

/-! ## Example L: a live cycle in the new state -/

/-- `top` reads `x`; when `x = 0` it fetches itself.  Terminates when `x ≠ 0`,
diverges when `x = 0`. -/
def rulesL : Rules Q3 IK Nat
  | .a => .ret 0
  | .b => .ret 0
  | .top => .fetch (.inr .x) fun v => if v = 0 then .fetch (.inl .top) .ret else .ret v

def oldL : IK → Nat := inpXY 1 0
def newL : IK → Nat := inpXY 0 0
def odbL : OldDB Q3 IK Nat Nat := recordAll rulesL fpId oldL 10

theorem odbL_top : odbL .top = some ⟨[(.inr .x, 1)], 1⟩ := by decide

/-! ## Example H: fingerprint collision on an input -/

/-- `top` returns `x`. -/
def rulesH : Rules Q3 IK Nat
  | .a => .ret 0
  | .b => .ret 0
  | .top => .fetch (.inr .x) .ret

def oldH : IK → Nat := inpXY 1 0
def newH : IK → Nat := inpXY 3 0
def odbH : OldDB Q3 IK Nat Nat := recordAll rulesH fpParity oldH 10

/-! ## Example S: fingerprint collision on a re-executed query only -/

/-- `a` returns `10 + x` (for `x ≠ 0`); `top` returns `a`.  Under `fpSat`,
inputs `1` and `2` have distinct fingerprints, but `a`'s old and new results
`11` and `12` collide. -/
def rulesS : Rules Q3 IK Nat
  | .a => .fetch (.inr .x) fun v => .ret (if v = 0 then 0 else 10 + v)
  | .b => .ret 0
  | .top => .fetch (.inl .a) .ret

def oldS : IK → Nat := inpXY 1 0
def newS : IK → Nat := inpXY 2 0
def odbS : OldDB Q3 IK Nat Nat := recordAll rulesS fpSat oldS 10

/-! ## Example N: an untracked parameter that changes between revisions -/

/-- Query code parameterized by a value `noise` that is not a tracked input:
a revision-wide setting such as a compiler version or a global build flag,
fixed for a whole revision and different between revisions.  `rulesN 0` and
`rulesN 1` are two deterministic rule sets.  `a` returns `x + noise`, `b`
returns `y`, and `top` returns `10 * a + b + 100 * noise`.  (This is not a
model of per-call non-determinism such as a clock read independently by each
query execution; see the card `untracked-change-breaks-reuse`.) -/
def rulesN (noise : Nat) : Rules Q3 IK Nat
  | .a => .fetch (.inr .x) fun v => .ret (v + noise)
  | .b => .fetch (.inr .y) .ret
  | .top => .fetch (.inl .a) fun u => .fetch (.inl .b) fun w => .ret (10 * u + w + 100 * noise)

def oldN : IK → Nat := inpXY 0 0
def newN : IK → Nat := inpXY 0 1
/-- Recorded with ambient value `0`. -/
def odbN : OldDB Q3 IK Nat Nat := recordAll (rulesN 0) fpId oldN 10

/-- A second program with an untracked revision-wide parameter, for early
cutoff: `a` reads `x` and returns `0`; `top` returns `a + noise`. -/
def rulesM (noise : Nat) : Rules Q3 IK Nat
  | .a => .fetch (.inr .x) fun _ => .ret 0
  | .b => .ret 0
  | .top => .fetch (.inl .a) fun u => .ret (u + noise)

def oldM : IK → Nat := inpXY 1 0
def newM : IK → Nat := inpXY 3 0
/-- Recorded with ambient value `0`. -/
def odbM : OldDB Q3 IK Nat Nat := recordAll (rulesM 0) fpId oldM 10

/-! ## Example B: an inconsistent database -/

/-- `a` reads `x` and returns `0`; `top` returns `a`. -/
def rulesB : Rules Q3 IK Nat
  | .a => .fetch (.inr .x) fun _ => .ret 0
  | .b => .ret 0
  | .top => .fetch (.inl .a) .ret

def oldB : IK → Nat := inpXY 1 0
def newB : IK → Nat := inpXY 3 0

/-- A database whose entry for `top` has the right trace but a wrong result
(`99` instead of `0`); the entry for `a` is correct. -/
def odbB : OldDB Q3 IK Nat Nat
  | .top => some ⟨[(.inl .a, 0)], 99⟩
  | .a => some ⟨[(.inr .x, 1)], 0⟩
  | .b => none

/-! ## Example P: an execution that aborts leaves the slot unchanged -/

/-- `top` reads `x` and panics when `x = 0`. -/
def rulesP : Rules Q3 IK Nat
  | .a => .ret 0
  | .b => .ret 0
  | .top => .fetch (.inr .x) fun v => if v = 0 then .panic else .ret v

def oldP : IK → Nat := inpXY 5 0
def newP : IK → Nat := inpXY 0 0
def odbP : OldDB Q3 IK Nat Nat := recordAll rulesP fpId oldP 10

/-! ## Example K′: example K without a cached entry for `top` -/

/-- The database of example K with the entry of `top` removed (a partial
cache, still consistent). -/
def odbKnoTop : OldDB Q3 IK Nat Nat
  | .top => none
  | .a => odbK .a
  | .b => odbK .b

/-! ## Example F: a collision upstream forces a needless re-execution -/

/-- Collides on `1` and `3`, distinct everywhere else. -/
def fpCollide13 : Nat → Nat := fun v => if v = 3 then 1 else v

/-- `a` returns `x`; `b` reads `y` then `a` and returns `30` when `y = 0` or
`a = 3`, else `10`; `top` returns `b`.  Old state `x = 1, y = 0`: `a = 1`,
`b = 30`.  New state `x = 3, y = 1`: from scratch `a = 3`, `b = 30`. -/
def rulesF : Rules Q3 IK Nat
  | .a => .fetch (.inr .x) .ret
  | .b => .fetch (.inr .y) fun vy => .fetch (.inl .a) fun va =>
      .ret (if vy = 0 then 30 else if va = 3 then 30 else 10)
  | .top => .fetch (.inl .b) .ret

def oldF : IK → Nat := inpXY 1 0
def newF : IK → Nat := inpXY 3 1
def odbF : OldDB Q3 IK Nat Nat := recordAll rulesF fpCollide13 oldF 10

/-! ## Example R: reversed replay separates the two cutoff modes -/

/-- Query keys of example R. -/
inductive Q4 : Type where
  | top
  | guard
  | risky
  | a
  deriving DecidableEq, Repr

/-- As example D, but after `risky` the query `top` also fetches `a`, which
reads `x` and always returns `0`.  Old trace of `top` (`x = 5`):
`[(guard, 1), (risky, 20), (a, 0)]`. -/
def rulesR : Rules Q4 IK Nat
  | .guard => .fetch (.inr .x) fun v => .ret (if v = 0 then 0 else 1)
  | .risky => .fetch (.inr .x) fun v => if v = 0 then .panic else .ret (100 / v)
  | .a => .fetch (.inr .x) fun _ => .ret 0
  | .top => .fetch (.inl .guard) fun g =>
      if g = 0 then .ret 0 else .fetch (.inl .risky) fun r => .fetch (.inl .a) fun u => .ret (r + u)

def odbR : OldDB Q4 IK Nat Nat := recordAll rulesR fpId oldD 10

/-! ## Divergence instances (terminating new state, diverging fetch) -/

/-- Every query returns `0`. -/
def rulesZ : Rules Q3 IK Nat := fun _ => .ret 0

/-- An inconsistent database: every query's entry records the query `top` as
its only dependency. -/
def odbLoop : OldDB Q3 IK Nat Nat := fun _ => some ⟨[(.inl .top, 0)], 0⟩

/-- The empty database. -/
def odbEmpty : OldDB Q3 IK Nat Nat := fun _ => none

/-- A working database with an `old` slot for every query whose recorded
dependency is `top` itself. -/
def loopDb : DB Q3 IK Nat Nat := fun _ => .old ⟨[(.inl .top, 0)], 0⟩

/-- `top` reads `x`; if `x = 3` it returns `0`, else it returns `a`.  `a`
reads `y`; if `y = 1` it returns `top`, else `20`.  Under parity fingerprints
the change `x : 1 → 3` is invisible. -/
def rulesFpLoop : Rules Q3 IK Nat
  | .top => .fetch (.inr .x) fun vx => if vx = 3 then .ret 0 else .fetch (.inl .a) .ret
  | .a => .fetch (.inr .y) fun vy => if vy = 1 then .fetch (.inl .top) .ret else .ret 20
  | .b => .ret 0

def oldFpLoop : IK → Nat := inpXY 1 0
def newFpLoop : IK → Nat := inpXY 3 1
def odbFpLoop : OldDB Q3 IK Nat Nat := recordAll rulesFpLoop fpParity oldFpLoop 10

/-- Old code: `top` returns `a`; `a` reads `x` and returns `0`. -/
def rulesOldLoop : Rules Q3 IK Nat
  | .top => .fetch (.inl .a) .ret
  | .a => .fetch (.inr .x) fun _ => .ret 0
  | .b => .ret 0

/-- New code: `top` returns `0`; `a` reads `x` and returns `top`. -/
def rulesNewLoop : Rules Q3 IK Nat
  | .top => .ret 0
  | .a => .fetch (.inr .x) fun _ => .fetch (.inl .top) .ret
  | .b => .ret 0

def odbOldLoop : OldDB Q3 IK Nat Nat := recordAll rulesOldLoop fpId (inpXY 0 0) 10

/-! ## Example PC: a partial cache -/

/-- `a` returns `x`; `top` returns `a + 1`. -/
def rulesPC : Rules Q3 IK Nat
  | .a => .fetch (.inr .x) .ret
  | .b => .ret 0
  | .top => .fetch (.inl .a) fun v => .ret (v + 1)

/-- A consistent database for `x = 5` that caches `top` but not its
dependency `a`. -/
def odbPC : OldDB Q3 IK Nat Nat
  | .top => some ⟨[(.inl .a, 5)], 6⟩
  | .a => none
  | .b => none

end Toy.RedGreen
