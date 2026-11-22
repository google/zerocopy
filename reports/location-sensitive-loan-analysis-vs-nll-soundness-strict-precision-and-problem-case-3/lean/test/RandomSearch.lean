import ToyLoanFlow
open Toy.LoanFlow
instance {m : Nat} : Inhabited (Stmt m) := ⟨.nop⟩

/-- LCG -/
def nextR (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % (2^64)

structure G where
  seed : Nat

def G.nat (g : G) (k : Nat) : Nat × G :=
  let s := nextR g.seed
  ((s / 65536) % (max k 1), ⟨s⟩)

def tyPool : List (List Mutbl) := [[], [], [], [.mut], [.shr], [.mut, .shr], [.mut, .mut], [.shr, .shr], [.mut], [.shr], [.mut], [.shr, .mut]]

def pick {α} [Inhabited α] (g : G) (l : List α) : α × G :=
  let (i, g) := g.nat l.length
  (l[i]!, g)

/-- all well-typed statements, grouped by kind -/
def wtStmts (m : Nat) (ty : Fin m → List Mutbl) : List (List (Stmt m)) :=
  let L := List.finRange m
  let p : Prog 1 m := ⟨0, fun _ => [], fun _ => .nop, ty⟩
  let ok (st : Stmt m) : Bool := decide (StmtWellTyped p st)
  let groups : List (List (Stmt m)) :=
    [ L.flatMap (fun d => L.flatMap fun s => [Stmt.borrow .mut d s, Stmt.borrow .shr d s]),
      L.flatMap (fun d => L.map fun s => Stmt.copy d s),
      L.flatMap (fun v => [Stmt.deref .rd v, Stmt.deref .wr v]),
      L.flatMap (fun v => [Stmt.access .rd v, Stmt.access .wr v]),
      L.flatMap (fun d => L.map fun s => Stmt.store d s),
      L.map (fun v => Stmt.ret v) ]
  (groups.map fun g => g.filter ok).filter (· ≠ [])

/-- random statement; `wt` makes it well typed -/
def randStmt (m : Nat) (ty : Fin m → List Mutbl) (g : G) (wt : Bool) : Stmt m × G := Id.run do
  let mut g := g
  if wt then
    let gs := wtStmts m ty
    let (k, g1) := g.nat (gs.length + 1); g := g1
    if k = gs.length then return (.nop, g)
    let grp := gs[k]!
    let (i, g2) := g.nat grp.length; g := g2
    return (grp[i]!, g)
  for _ in [0:30] do
    let (k0, g1) := g.nat 12; g := g1
    let k := if k0 ≥ 8 then (if k0 < 10 then 0 else 3) else k0
    let (a, g2) := g.nat m; g := g2
    let (b, g3) := g.nat m; g := g3
    let (mu, g4) := g.nat 2; g := g4
    if h : a < m then
     if h2 : b < m then
      let A : Fin m := ⟨a, h⟩
      let B : Fin m := ⟨b, h2⟩
      let M := if mu = 0 then Mutbl.mut else Mutbl.shr
      let acc := if mu = 0 then Acc.wr else Acc.rd
      let st : Stmt m := match k with
        | 0 => .borrow M A B | 1 => .borrow M A B | 2 => .copy A B | 3 => .deref acc A
        | 4 => .access acc A | 5 => .store A B | 6 => .ret A | _ => .nop
      return (st, g)
  return (.nop, g)

def scenTys : List (List (List Mutbl)) := [[[],[],[.shr],[.mut,.shr],[.shr]], [[],[],[.mut],[.mut],[.mut,.mut]], [[],[],[.shr],[.mut],[.mut,.shr],[.shr,.shr]], [[],[.mut],[.mut],[.shr],[.mut,.mut],[.mut, .shr]]]

def randProg (g : G) (wt : Bool) (scen : Nat := 0) : (Σ n m, Prog n m) × G := Id.run do
  let mut g := g
  let (n0, g1) := g.nat 8; g := g1
  let n := n0 + 2
  let (m0, g2) := g.nat 4; g := g2
  let m := if scen = 0 then m0 + 2 else (scenTys[scen-1]!).length
  let mut tys : Array (List Mutbl) := #[]
  for i in [0:m] do
    let (t, g') := pick g tyPool; g := g'
    let t := if scen ≠ 0 then (scenTys[scen-1]!)[i]! else if wt && i < 2 then [] else t
    tys := tys.push t
  let ty : Fin m → List Mutbl := fun v => tys[v.val]!
  let mut stmts : Array (Stmt m) := #[]
  let mut succs : Array (List (Fin n)) := #[]
  for _ in [0:n] do
    let (st, g') := randStmt m ty g wt; g := g'
    stmts := stmts.push st
    let (shape, g'') := g.nat 10; g := g''
    let (t, g3) := g.nat n; g := g3
    let i := succs.size
    let l0 : List Nat := if shape < 6 then [i+1] else if shape < 9 then [i+1, t] else [t]
    let l : List (Fin n) := l0.filterMap fun j => if h : j < n then some ⟨j, h⟩ else none
    succs := succs.push l.eraseDups
  have hn : 0 < n := by omega
  let p : Prog n m := ⟨⟨0, hn⟩, fun q => succs[q.val]!, fun q => stmts[q.val]!, ty⟩
  return (⟨n, m, p⟩, g)

def showProg {n m : Nat} (p : Prog n m) : String :=
  let tys := (List.finRange m).map fun v => repr (p.ty v)
  let ns := (List.finRange n).map fun q => s!"{q.val}: {repr (p.stmt q)} -> {(p.succ q).map (·.val)}"
  s!"n={n} m={m} ty={tys}\n" ++ String.intercalate "\n" ns

def test (iters : Nat) (seed : Nat) (wt : Bool) (scen : Nat := 0) : IO Unit := do
  let mut g : G := ⟨seed⟩
  let mut cnt := (0, 0, 0, 0, 0, 0)
  let mut lsAcc := 0
  let mut nllAcc := 0
  let mut unsafeCnt := 0
  for _ in [0:iters] do
    let (⟨n, m, p⟩, g') := randProg g wt scen; g := g'
    let wtp := decide (WellTyped p)
    if wt && !wtp then continue
    let uns := unsafeB p
    let nll := nllAcceptsB .inv p
    let ls := lsAcceptsB .overwrite .inv p
    if uns then unsafeCnt := unsafeCnt + 1
    if ls then lsAcc := lsAcc + 1
    if nll then nllAcc := nllAcc + 1
    if nll && uns then
      cnt := (cnt.1 + 1, cnt.2)
      if cnt.1 ≤ 2 then IO.println s!"NLL UNSOUND wt={wtp}\n{showProg p}"
    if ls && uns then
      cnt := (cnt.1, cnt.2.1 + 1, cnt.2.2)
      if cnt.2.1 ≤ 2 then IO.println s!"LS UNSOUND wt={wtp}\n{showProg p}"
    if nll && !ls then
      cnt := (cnt.1, cnt.2.1, cnt.2.2.1 + 1, cnt.2.2.2)
      if cnt.2.2.1 ≤ 2 then IO.println s!"NLL not subset LS wt={wtp}\n{showProg p}"
    if lsAcceptsB .overwrite .cov p && uns then
      cnt := (cnt.1, cnt.2.1, cnt.2.2.1, cnt.2.2.2.1 + 1, cnt.2.2.2.2)
    if lsAcceptsB .overwriteAndCopySrc .inv p && uns then
      cnt := (cnt.1, cnt.2.1, cnt.2.2.1, cnt.2.2.2.1, cnt.2.2.2.2.1 + 1, cnt.2.2.2.2.2)
    if ls && !nll && !uns then
      cnt := (cnt.1, cnt.2.1, cnt.2.2.1, cnt.2.2.2.1, cnt.2.2.2.2.1, cnt.2.2.2.2.2 + 1)
  IO.println s!"wt={wt} nllUnsound={cnt.1} lsUnsound={cnt.2.1} nllNotSubLs={cnt.2.2.1} lsCovUnsound={cnt.2.2.2.1} lsCopyKillUnsound={cnt.2.2.2.2.1} lsStrict={cnt.2.2.2.2.2} lsAcc={lsAcc} nllAcc={nllAcc} unsafe={unsafeCnt}"

/-! Usage (bounded random search; not part of the library build):
`lake env lean test/RandomSearch.lean` after appending lines such as
`#eval test 4000 31 true 1` (iterations, seed, well-typed only, type scenario 0-4). -/
