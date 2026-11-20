import ToyProphecy.Syntax

/-!
# The borrow discipline

A static checker in the spirit of a (lexical, explicit-end) borrow checker. It
tracks, without looking at values, which locals are lent and the status of each
reference variable (`unborn`, `active`, `frozen` = currently reborrowed, `ended`),
and records each kind of violation it meets. A borrow selected at run time
(`borrowSel r c x y`) conservatively lends *both* `x` and `y` until `r` ends.

Each kind of violation gives a separate named property of a program
(`NoLentAccess`, `NoFrozenAccess`, `NoUseAfterEnd`, `FreshBindings`,
`AllEndedAtExit`), so that every theorem names exactly the parts of the
discipline it uses.

Scoping errors (using a reference variable that was never bound, a local
operation inside a callee body, a callee returning a reference variable that was
never bound) are not violations, and the checker stops at the first one: once it
is stuck (`CState.stuck`), `checkOp` and `checkStmt` record nothing further
(`checkOps_of_stuck`, `checkStmts_of_stuck`), and
`violations` does not report `unendedAtExit` for a stuck program. So a program
with a scoping error satisfies `Avoids k` as soon as no violation of kind `k` is
recorded before the checker gets stuck (in the statements before the error, or
earlier in the statement containing it), whatever follows
(`stuckProg_satisfies_all_avoids`), and likewise for `CalleeAvoids k` on a callee
with a scoping error (`stuckCallee_satisfies_all_avoids`). The discipline properties therefore
constrain only the part of a program up to its first scoping error.

After a violation the checker performs the same bookkeeping as for the
corresponding legal step, so that one violation does not by itself cause
violations of other kinds to be reported.

Statuses and lender links are kept per reference-variable *name*. Rebinding a
name that is already bound (a `rebind` violation) makes the borrow previously
held under that name unreachable: it is *leaked* (it never ends, so a local it
lends stays lent and a borrow it reborrows stays frozen for the rest of the
frame). Lender links of other names that pointed to the rebound name referred to
the leaked borrow and are dropped at the rebinding, so that ending one of those
reborrows later cannot change the status of the new borrow held under that name.
A leaked borrow is reported only as `rebind`, not as `unendedAtExit`.
-/

namespace Toy.Prophecy

/-- Status of a reference variable. -/
inductive RStatus where
  | unborn
  | active
  | frozen
  | ended
  deriving Repr, DecidableEq

/-- What a borrow was taken from. -/
inductive Lender where
  | loc (x : Var)
  | sel (x y : Var)
  | ref (q : RefVar)
  deriving Repr, DecidableEq

/-- Kinds of violation of the borrow discipline. -/
inductive Violation where
  /-- reading, assigning, or borrowing a local while it is lent -/
  | lentAccess
  /-- reading or writing through, reborrowing, ending, passing to a call, or
  returning a borrow while it is reborrowed -/
  | frozenAccess
  /-- any use of a borrow after it has ended (including ending it twice) -/
  | useAfterEnd
  /-- binding a reference variable that is already bound in its frame (live,
  frozen, or already ended) -/
  | rebind
  /-- a borrow of the main program is still live when the program ends -/
  | unendedAtExit
  deriving Repr, DecidableEq

/-- State of the checker. -/
structure CState where
  lent : Var → Bool
  status : RefVar → RStatus
  lender : RefVar → Option Lender
  bound : List RefVar
  viol : List Violation
  stuck : Bool

namespace CState

/-- Point update of a function (local copy, to keep this file independent). -/
def upd {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α :=
  fun j => if j = k then v else f j

def addV (c : CState) (v : Violation) : CState := { c with viol := c.viol ++ [v] }

def setStuck (c : CState) : CState := { c with stuck := true }

/-- Check a use of borrow `r`: stuck if unbound, violation if frozen or ended. -/
def useRef (c : CState) (r : RefVar) : CState :=
  match c.status r with
  | .unborn => c.setStuck
  | .active => c
  | .frozen => c.addV .frozenAccess
  | .ended => c.addV .useAfterEnd

/-- Bind reference variable `r`. Binding a name that is already bound, in any
status including `ended`, is a `rebind` violation; the borrow previously held
under `r` is then leaked, and every lender link `.ref r` of another name (which
referred to the leaked borrow) is dropped. -/
def bindRef (c : CState) (r : RefVar) : CState :=
  if c.status r = .unborn then { c with bound := c.bound ++ [r] }
  else
    let c := c.addV .rebind
    { c with bound := c.bound ++ [r],
             lender := fun q => if c.lender q = some (.ref r) then none else c.lender q }

/-- Release the lender of `r` when `r` ends. -/
def release (c : CState) (r : RefVar) : CState :=
  match c.lender r with
  | some (.loc x) => { c with lent := upd c.lent x false }
  | some (.sel x y) => { c with lent := upd (upd c.lent x false) y false }
  | some (.ref q) =>
      if c.status q = .frozen then { c with status := upd c.status q .active } else c
  | none => c

end CState

open CState in
/-- Check an expression. `L` says whether locals are accessible (main program). -/
def checkExpr (L : Bool) (c : CState) : Expr → CState
  | .lit _ => c
  | .var x => if !L then c.setStuck else if c.lent x then c.addV .lentAccess else c
  | .deref r => c.useRef r
  | .add a b => checkExpr L (checkExpr L c a) b

open CState in
/-- Check one basic operation (no effect once stuck). -/
def checkOp (L : Bool) (c : CState) (o : Op) : CState :=
  if c.stuck then c else
  match o with
  | .assign x e =>
      if !L then c.setStuck else
      let c := checkExpr L c e
      if c.lent x then c.addV .lentAccess else c
  | .borrow r x =>
      if !L then c.setStuck else
      let c := if c.lent x then c.addV .lentAccess else c
      let c := c.bindRef r
      { c with lent := upd c.lent x true, status := upd c.status r .active,
               lender := upd c.lender r (some (.loc x)) }
  | .borrowSel r e x y =>
      if !L then c.setStuck else
      let c := checkExpr L c e
      let c := if c.lent x || c.lent y then c.addV .lentAccess else c
      let c := c.bindRef r
      { c with lent := upd (upd c.lent x true) y true, status := upd c.status r .active,
               lender := upd c.lender r (some (.sel x y)) }
  | .reborrow t r =>
      let c := c.useRef r
      if c.stuck then c else
      let c := c.bindRef t
      let st := if c.status r = .ended then c.status else upd c.status r .frozen
      { c with status := upd st t .active, lender := upd c.lender t (some (.ref r)) }
  | .write r e =>
      let c := checkExpr L c e
      if c.stuck then c else c.useRef r
  | .endBorrow r =>
      let st := c.status r
      let c := c.useRef r
      if c.stuck then c else
      if st = .ended then c else
      let c := c.release r
      { c with status := upd c.status r .ended }

/-- Check a list of basic operations. -/
def checkOps (L : Bool) : CState → List Op → CState
  | c, [] => c
  | c, o :: os => checkOps L (checkOp L c o) os

/-- The checker state at callee entry: only the parameter is bound (and active). -/
def CState.calleeInit : CState :=
  { lent := fun _ => false
    status := CState.upd (fun _ => .unborn) Callee.param .active
    lender := fun _ => none
    bound := [Callee.param]
    viol := []
    stuck := false }

open CState in
/-- Check a callee: its body, then the returned borrow (returning counts as a use;
the returned borrow must be the active one). -/
def checkCallee (f : Callee) : CState :=
  let c := checkOps false CState.calleeInit f.body
  if c.stuck then c else c.useRef f.ret

open CState in
/-- Check one main-program statement. A call checks the argument as a use, checks
the callee in its own frame (its violations count as violations of the program),
and then freezes the argument until the returned borrow ends. -/
def checkStmt (c : CState) : Stmt → CState
  | .op o => checkOp true c o
  | .call t f r =>
      if c.stuck then c else
      let c := c.useRef r
      if c.stuck then c else
      let cf := checkCallee f
      if cf.stuck then c.setStuck else
      let c := { c with viol := c.viol ++ cf.viol }
      let c := c.bindRef t
      let st := if c.status r = .ended then c.status else upd c.status r .frozen
      { c with status := upd st t .active, lender := upd c.lender t (some (.ref r)) }

/-- Check a list of main-program statements. -/
def checkStmts : CState → Prog → CState
  | c, [] => c
  | c, s :: ss => checkStmts (checkStmt c s) ss

/-- The checker state at program start. -/
def CState.init : CState :=
  { lent := fun _ => false, status := fun _ => .unborn, lender := fun _ => none,
    bound := [], viol := [], stuck := false }

/-- All violations of the discipline in program `P` recorded before its first
scoping error, including borrows still live at the end (not reported for stuck
programs). -/
def violations (P : Prog) : List Violation :=
  let c := checkStmts CState.init P
  if !c.stuck && c.bound.any (fun r => c.status r = .active || c.status r = .frozen) then
    c.viol ++ [.unendedAtExit]
  else c.viol

/-- Program `P` has no violation of kind `k`. -/
def Avoids (k : Violation) (P : Prog) : Prop := k ∉ violations P

instance (k : Violation) (P : Prog) : Decidable (Avoids k P) :=
  inferInstanceAs (Decidable (k ∉ violations P))

/-- A lent local is neither read, assigned, nor borrowed again until its borrow
ends. -/
abbrev NoLentAccess (P : Prog) : Prop := Avoids .lentAccess P
/-- A reborrowed borrow is not used (read, written, reborrowed, ended, passed to
a call, or returned) until the reborrow ends. -/
abbrev NoFrozenAccess (P : Prog) : Prop := Avoids .frozenAccess P
/-- A borrow is never used after it ends. -/
abbrev NoUseAfterEnd (P : Prog) : Prop := Avoids .useAfterEnd P
/-- Every borrow-creating statement binds a reference variable not bound before
in its frame: syntactic single assignment of borrow names per frame. This is
stricter than forbidding the overwrite of a live borrow: reusing the name of a
borrow that has already ended is also rejected (`rebind_ended_neg`). On the
example `rebindEnded` that reuse is harmless for both translations
(`rebindEnded_harmless`); no general statement about it is made. -/
abbrev FreshBindings (P : Prog) : Prop := Avoids .rebind P
/-- Every borrow of the main program has ended when the program ends. -/
abbrev AllEndedAtExit (P : Prog) : Prop := Avoids .unendedAtExit P

/-- Violations of a callee checked on its own. -/
def calleeViolations (f : Callee) : List Violation := (checkCallee f).viol

/-- Callee `f` has no violation of kind `k`. Only `.frozenAccess`,
`.useAfterEnd` and `.rebind` can occur in a callee: callee frames have no locals
(so nothing is ever lent) and `checkCallee` does not report borrows live at
callee exit, so `CalleeAvoids .lentAccess f` and `CalleeAvoids .unendedAtExit f`
hold for every callee (`calleeAvoids_lentAccess_unendedAtExit`). -/
def CalleeAvoids (k : Violation) (f : Callee) : Prop := k ∉ calleeViolations f

instance (k : Violation) (f : Callee) : Decidable (CalleeAvoids k f) :=
  inferInstanceAs (Decidable (k ∉ calleeViolations f))

/-- Callee `f` has no scoping error, in its body *or in its returned reference
variable*: the body uses no reference variable that was never bound and no local
(no `var`, `assign`, `borrow`, `borrowSel`), and the returned name `f.ret` is the
parameter or is bound by the body (it may have ended; that is a `useAfterEnd`
violation, not a scoping error). For example `{ body := [], ret := 1 }` has an
empty body but is not scoped (`emptyBody_unboundRet_not_scoped`). -/
def CalleeScoped (f : Callee) : Prop := (checkCallee f).stuck = false

instance (f : Callee) : Decidable (CalleeScoped f) :=
  inferInstanceAs (Decidable ((checkCallee f).stuck = false))

/-- No borrow of callee `f` is used while it is reborrowed (`CalleeAvoids
.frozenAccess`). -/
abbrev CalleeNoFrozenAccess (f : Callee) : Prop := CalleeAvoids .frozenAccess f
/-- No borrow of callee `f` is used after it ends (`CalleeAvoids .useAfterEnd`). -/
abbrev CalleeNoUseAfterEnd (f : Callee) : Prop := CalleeAvoids .useAfterEnd f
/-- Every borrow-creating operation of callee `f`'s body binds a name not bound
before in the callee frame (the parameter counts as bound): syntactic single
assignment of borrow names, which also rejects reusing the name of an ended
borrow (`CalleeAvoids .rebind`). -/
abbrev CalleeFreshBindings (f : Callee) : Prop := CalleeAvoids .rebind f

end Toy.Prophecy
