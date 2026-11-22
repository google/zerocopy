import ToyLoanFlow.Analyses

/-!
# Executable versions of the checkers and of the semantics

Worklist closures computing over-approximations of the inductive predicates of
`Analyses.lean`, and a bounded exploration of reachable (node, state) pairs. Concrete
theorems never trust these functions: they are used to compute candidate certificates, which
are then checked against the rules (`Certificates.lean`).
-/

namespace Toy.LoanFlow

variable {n m : Nat}

/-- Worklist closure: start from `init`, add `step x` for every `x` added, at most `fuel`
items processed. -/
def closure {α : Type} [DecidableEq α] (step : α → List α) : Nat → List α → List α → List α
  | 0, acc, _ => acc
  | _ + 1, acc, [] => acc
  | k + 1, acc, x :: work =>
      let new := (step x).filter fun y => !acc.contains y
      let new := new.eraseDups
      closure step k (acc ++ new) (work ++ new)

/-- Executable liveness facts `(v, q)`. -/
def liveList (p : Prog n m) : List (Fin m × Fin n) :=
  let init := (List.finRange n).flatMap fun q => (p.stmt q).uses.map fun v => (v, q)
  let init := init.eraseDups
  let step : Fin m × Fin n → List (Fin m × Fin n) := fun ⟨v, q'⟩ =>
    (List.finRange n).filterMap fun q =>
      if (p.succ q).contains q' && !(p.stmt q).defs.contains v then some (v, q) else none
  closure step (n * m + 1) init init

/-- Executable reachability set from `u` (reflexive). -/
def reachList (p : Prog n m) (u : Fin n) : List (Fin n) :=
  closure (fun x => p.succ x) (n + 1) [u] [u]

/-- Executable reachability relation (all pairs). -/
def reachAll (p : Prog n m) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u => (reachList p u).map fun w => (u, w)

/-- All constraint pairs generated anywhere, with the node that generates them. -/
def genAll (vm : VarMode) (p : Prog n m) : List (Fin n × Origin m × Origin m) :=
  (List.finRange n).flatMap fun b => (gen vm p b).map fun pr => (b, pr.1, pr.2)

/-- Executable subset facts `(o₁, o₂, q)`. -/
def subList (vm : VarMode) (p : Prog n m) : List (Origin m × Origin m × Fin n) :=
  let lv := liveList p
  let init :=
    ((List.finRange n).flatMap fun q => (gen vm p q).map fun pr => (pr.1, pr.2, q)).eraseDups
  let step (S : List (Origin m × Origin m × Fin n)) :
      Origin m × Origin m × Fin n → List (Origin m × Origin m × Fin n) := fun ⟨o₁, o₂, q⟩ =>
    let pers := (p.succ q).filterMap fun q' =>
      if lv.contains (o₁.1, q') && lv.contains (o₂.1, q') then some (o₁, o₂, q') else none
    let tr1 := S.filterMap fun ⟨a, b, q2⟩ => if q2 == q && b == o₁ then some (a, o₂, q) else none
    let tr2 := S.filterMap fun ⟨a, b, q2⟩ => if q2 == q && a == o₂ then some (o₁, b, q) else none
    pers ++ tr1 ++ tr2
  let rec iter : Nat → List (Origin m × Origin m × Fin n) → List (Origin m × Origin m × Fin n)
    | 0, S => S
    | k + 1, S =>
      let S' := closure (step S) (S.length * 4 + 64) S S
      if S'.length == S.length then S else iter k S'
  iter (n * m * m * 16 + 16) init

/-- Executable location-sensitive facts `(l, o, q)` (after `q`). -/
def lsList (km : KillMode) (vm : VarMode) (p : Prog n m) : List (Fin n × Origin m × Fin n) :=
  let sb := subList vm p
  let init := ((List.finRange n).flatMap fun l =>
    match p.stmt l with
    | .borrow _ d _ => [(l, (d, 0), l)]
    | _ => []).eraseDups
  let step : Fin n × Origin m × Fin n → List (Fin n × Origin m × Fin n) := fun ⟨l, o, q⟩ =>
    let carries := (p.succ q).filterMap fun q' =>
      if killsAt km p q' o.1 then none else some (l, o, q')
    let steps := (p.succ q).flatMap fun q' =>
      if (p.stmt q').defs.contains o.1 then []
      else (gen vm p q').filterMap fun pr => if pr.1 == o then some (l, pr.2, q') else none
    let subs := sb.filterMap fun ⟨a, b, q2⟩ => if q2 == q && a == o then some (l, b, q) else none
    carries ++ steps ++ subs
  closure step (n * n * (m * 8 + 1) * 4 + 16) init init

/-- Executable location-sensitive acceptance. -/
def lsAcceptsB (km : KillMode) (vm : VarMode) (p : Prog n m) : Bool :=
  let ls := lsList km vm p
  let lv := liveList p
  (List.finRange n).all fun l => (List.finRange n).all fun q =>
    !(decide (Conflicts p l q)) ||
      !(ls.any fun ⟨l', o, q₀⟩ => l' == l && (p.succ q₀).contains q && lv.contains (o.1, q))

/-- Executable regions `(o, q)`. -/
def regionList (vm : VarMode) (p : Prog n m) : List (Origin m × Fin n) :=
  let lv := liveList p
  let init1 := lv.flatMap fun ⟨v, q⟩ => (List.range (p.ty v).length).map fun k => ((v, k), q)
  let init2 := (List.finRange n).flatMap fun b =>
    match p.stmt b with
    | .ret v => (List.finRange n).map fun q => ((v, 0), q)
    | _ => []
  let init := (init1 ++ init2).eraseDups
  let ga := genAll vm p
  let step : Origin m × Fin n → List (Origin m × Fin n) := fun ⟨o, q⟩ =>
    ga.filterMap fun ⟨_, o₁, o₂⟩ => if o₂ == o then some (o₁, q) else none
  closure step (n * (m * 8 + 1) * 4 + 16) init init

/-- Executable scope facts `(l, q)`. -/
def scopeList (vm : VarMode) (p : Prog n m) : List (Fin n × Fin n) :=
  let rg := regionList vm p
  let inR (l q : Fin n) : Bool :=
    match loanDst p l with
    | some d => rg.contains ((d, 0), q)
    | none => false
  let init := (List.finRange n).flatMap fun l =>
    (p.succ l).filterMap fun q => if inR l q then some (l, q) else none
  let init := init.eraseDups
  let step : Fin n × Fin n → List (Fin n × Fin n) := fun ⟨l, q⟩ =>
    (p.succ q).filterMap fun q' => if inR l q' then some (l, q') else none
  closure step (n * n + 1) init init

/-- Executable location-insensitive acceptance. -/
def nllAcceptsB (vm : VarMode) (p : Prog n m) : Bool :=
  let sc := scopeList vm p
  (List.finRange n).all fun l => (List.finRange n).all fun q =>
    !(decide (Conflicts p l q)) || !(sc.contains (l, q))

/-- Explore reachable (node, state) pairs; return `true` if some step from an explored pair is
UB. -/
def explore (p : Prog n m) (fuel : Nat) : List (Fin n × RState n m) × Bool :=
  let init : List (Fin n × RState n m) := [(p.entry, RState.init)]
  let rec go : Nat → List (Fin n × RState n m) → List (Fin n × RState n m) →
      List (Fin n × RState n m) × Bool
    | 0, acc, _ => (acc, false)
    | _ + 1, acc, [] => (acc, false)
    | k + 1, acc, (q, σ) :: work =>
      match exec p q σ with
      | .ub => (acc, true)
      | .halt => go k acc work
      | .ok σ' =>
        let new := ((p.succ q).map fun y => (y, σ')).filter fun x => !acc.contains x
        let new := new.eraseDups
        go k (acc ++ new) (work ++ new)
  go fuel init init

/-- Executable unsafety check (bounded exploration). -/
def unsafeB (p : Prog n m) (fuel : Nat := 5000) : Bool := (explore p fuel).2

end Toy.LoanFlow
