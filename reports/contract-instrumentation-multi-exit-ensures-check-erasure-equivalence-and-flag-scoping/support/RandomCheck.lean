import ToyContracts
open Toy.Contracts

/-! Bounded pseudo-random check of the main statements. Run from `lean/` after `lake build`:
`lake env lean ../support/RandomCheck.lean`. Prints failure counts per statement (all expected 0)
and the number of generated functions that are lowered. -/


def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

structure Gen where s : Nat
def Gen.next (g : Gen) (k : Nat) : Nat × Gen := let s' := lcg g.s; ((s' / 65536) % k, ⟨s'⟩)

def genOp (g : Gen) : Operand × Gen :=
  let (t, g) := g.next 3
  let (v, g) := g.next 4
  (match t with | 0 => .arg | 1 => .lit v | _ => .loc (v % 2), g)

def genStmt (g : Gen) (allowChecks : Bool) : Stmt × Gen :=
  let (t, g) := g.next (if allowChecks then 6 else 4)
  let (a, g) := genOp g
  let (b, g) := genOp g
  let (i, g) := g.next 2
  (match t with
   | 0 => .assign i (.add a b)
   | 1 => .assign i (.sub a b)
   | 2 => .emit a
   | 3 => .assign i (.use a)
   | 4 => .checkEns a
   | _ => .checkReq, g)

def genStmts (g : Gen) (allowChecks : Bool) : Nat → List Stmt × Gen
  | 0 => ([], g)
  | k+1 => let (s, g) := genStmt g allowChecks; let (ss, g) := genStmts g allowChecks k; (s :: ss, g)

def genTerm (g : Gen) (nb : Nat) (allowTry : Bool) : Term × Gen :=
  let (t, g) := g.next (if allowTry then 7 else 6)
  let (b1, g) := g.next (nb + 1)
  let (b0, g) := g.next (nb + 1)
  let (o, g) := genOp g
  let (e, g) := genOp g
  let (k, g) := g.next 3
  let kind : ExitKind := match k with | 0 => .tail | 1 => .early | _ => .tryErr
  (match t with
   | 0 => .goto b1
   | 1 => .branch o b1 b0
   | 2 => .ret kind o
   | 3 => .ret kind e
   | 4 => .panic
   | 5 => .branch o b1 b0
   | _ => .tryQ o e b1, g)

def genBlocks (g : Gen) (nb : Nat) (allowTry allowChecks : Bool) : Nat → List Block × Gen
  | 0 => ([], g)
  | k+1 =>
    let (ns, g) := g.next 3
    let (ss, g) := genStmts g allowChecks ns
    let (t, g) := genTerm g nb allowTry
    let (bs, g) := genBlocks g nb allowTry allowChecks k
    (⟨ss, t⟩ :: bs, g)

def genFn (g : Gen) (allowTry allowChecks : Bool) : Fn × Gen :=
  let (nb, g) := g.next 4
  let nb := nb + 1
  let (np, g) := g.next 2
  let (pro, g) := genStmts g allowChecks np
  let (bs, g) := genBlocks g nb allowTry allowChecks nb
  let (en, g) := g.next nb
  (⟨pro, en, bs⟩, g)

def contracts : List Contract :=
  [ ⟨fun x => decide (x < 3), fun x r => decide (r ≤ x)⟩,
    ⟨fun x => x % 2 == 0, fun x r => r == x⟩,
    ⟨fun _ => true, fun _ r => r % 2 == 0⟩,
    ⟨fun x => x != 1, fun _ _ => true⟩ ]

def isFinal (o : Obs) : Bool := o.outcome != .fuelOut

def N := 7
def xs := List.range 5
def ns := List.range (N+1)

-- R1: Lowered g → run (instr allExits g) = instrObs (run g)
def chkR1 (c : Contract) (g : Fn) : Bool :=
  !(decide (Lowered g)) || xs.all fun x => ns.all fun n => run c (instr .allExits g) x n == instrObs c x (run c g x n)
-- R2: ret in instr allExits (lower f) → req ∧ ens
def chkR2 (c : Contract) (f : Fn) : Bool :=
  xs.all fun x => (List.range 16).all fun n => match run c (instr .allExits (lower f)) x n with
    | ⟨_, .ret r⟩ => c.req x && c.ens x r | _ => true
-- R4: JumpsInRange f → final obs of f at fuel n occurs in lower f at fuel n + 1, and conversely at fuel n
def chkR4 (c : Contract) (f : Fn) : Bool :=
  !(decide (JumpsInRange f)) || xs.all fun x => ns.all fun n =>
    (let o := run c f x n; !isFinal o || run c (lower f) x (n+1) == o) &&
    (let o := run c (lower f) x n; !isFinal o || run c f x n == o)
-- determinism / monotonicity
def chkMono (c : Contract) (f : Fn) : Bool :=
  xs.all fun x => ns.all fun n => let o := run c f x n; !isFinal o || run c f x (n+1) == o
-- R8
def chkR8 (f : Fn) : Bool := !(decide (NoChecks f)) || (erase (instr .allExits f) == f && erase (instr .tailOnly f) == f)
-- R9 (bounded at fuel ≤ N): Lowered, NoChecks, req x → (runEq up to N ↔ ens on returns up to N)
def chkR9 (c : Contract) (g : Fn) : Bool :=
  !(decide (Lowered g) && decide (NoChecks g)) || xs.all fun x => !c.req x ||
    ((ns.all fun n => run c (erase (instr .allExits g)) x n == run c (instr .allExits g) x n) ==
     (ns.all fun n => match run c g x n with | ⟨_, .ret r⟩ => c.ens x r | _ => true))
-- R24 (bounded at fuel ≤ N): Lowered, req x → (instr allExits g = g up to N ↔ ens on returns up to N)
def chkR24 (c : Contract) (g : Fn) : Bool :=
  !(decide (Lowered g)) || xs.all fun x => !c.req x ||
    ((ns.all fun n => run c (instr .allExits g) x n == run c g x n) ==
     (ns.all fun n => match run c g x n with | ⟨_, .ret r⟩ => c.ens x r | _ => true))
-- R11: req false → instr halts with ⟨[], pre⟩ at fuel 0 and erase never checkFails
def chkR11 (c : Contract) (g : Fn) (p : Placement) : Bool :=
  xs.all fun x => c.req x || (run c (instr p g) x 0 == ⟨[], .checkFail .pre⟩ &&
    ns.all fun n => match (run c (erase (instr p g)) x n).outcome with | .checkFail _ => false | _ => true)
-- R12
def chkR12 (c : Contract) (g : Fn) (p : Placement) : Bool :=
  xs.all fun x => ns.all fun n =>
    run c (assumeErase (instr p g)) x n == (if c.req x then run c (erase (instr p g)) x n else ⟨[], .ub⟩)
-- R13 (bounded): NoChecks g, obligation at x (bounded) → every final obs of instr at fuel n is final obs of assumeErase at fuel n, or src ub
def chkR13 (c : Contract) (g : Fn) : Bool :=
  !(decide (NoChecks g)) || xs.all fun x =>
    let ob := !c.req x || (ns.all fun n => match run c g x n with | ⟨_, .ret r⟩ => c.ens x r | _ => true)
    !ob || ns.all fun n => let o := run c (instr .allExits g) x n
      !isFinal o || run c (assumeErase (instr .allExits g)) x n == o ||
        (ns.any fun m => let s := run c (assumeErase (instr .allExits g)) x m; s.outcome == .ub && s.events.isPrefixOf o.events)
-- R15/R17
def flagsets : List (Nat → Bool) := [fun _ => true, fun _ => false, fun k => k == 0, fun k => k == 1, fun k => k == 2]
def sites : List Site := [.calleeSide, .callerSide]
def ress : List Resolution := [.atDefinition, .atInstantiation]
def css : List CallSite := [⟨0,1,0,false⟩, ⟨0,1,0,true⟩, ⟨1,1,1,true⟩, ⟨0,1,2,true⟩]
def chkR15 (c : Contract) (g : Fn) : Bool :=
  !(decide (Lowered g)) || flagsets.all fun fl => sites.all fun s => ress.all fun res => css.all fun cs =>
    xs.all fun x => ns.all fun n => callRun fl s res cs c g x n ==
      (if fl (governingCrate s res cs) then instrObs c x (run c g x n) else run c g x n)
-- R17 (bounded no-violation, no Lowered)
def chkR17 (c : Contract) (g : Fn) : Bool :=
  flagsets.all fun fl => sites.all fun s => ress.all fun res => css.all fun cs => xs.all fun x =>
    let noviol := c.req x && (ns.all fun n => match run c g x n with | ⟨_, .ret r⟩ => c.ens x r | _ => true)
    !noviol || ns.all fun n => callRun fl s res cs c g x n == run c g x n
-- R16 (bounded)
def chkR16 (c : Contract) (g : Fn) : Bool :=
  !(decide (Lowered g) && decide (NoChecks g)) || flagsets.all fun fl => sites.all fun s => ress.all fun res => css.all fun cs => xs.all fun x =>
    let viol := !c.req x || (ns.any fun n => match run c g x n with | ⟨_, .ret r⟩ => !c.ens x r | _ => false)
    let det := ns.any fun n => match (callRun fl s res cs c g x n).outcome with | .checkFail _ => true | _ => false
    !viol || det == fl (governingCrate s res cs)
-- R20/R21 (bounded): Lowered, NoChecks, ctfe skip const r → (runtime value r ↔ req ∧ ens r)
def chkR20 (c : Contract) (g : Fn) : Bool :=
  !(decide (Lowered g) && decide (NoChecks g)) || xs.all fun x => ns.all fun n =>
    match ctfeRun .skipChecks c (instr .allExits g) x n with
    | ⟨_, .ret r⟩ =>
      let rv := (List.range 12).any fun m => (run c (instr .allExits g) x m).outcome == .ret r
      rv == (c.req x && c.ens x r)
    | _ => true

def runAll (seed count : Nat) : List (String × Nat) := Id.run do
  let mut g : Gen := ⟨seed⟩
  let mut fails : Array Nat := Array.replicate 15 0
  let mut nLow := 0
  for _ in [0:count] do
    let (t, g1) := g.next 2
    let (ch, g2) := g1.next 3
    let (f, g3) := genFn g2 (t == 0) (ch == 0)
    g := g3
    if decide (Lowered f) then nLow := nLow + 1
    for c in contracts do
      if !chkR1 c f then fails := fails.modify 0 (·+1)
      if !chkR2 c f then fails := fails.modify 1 (·+1)
      if !chkR4 c f then fails := fails.modify 2 (·+1)
      if !chkMono c f then fails := fails.modify 3 (·+1)
      if !chkR9 c f then fails := fails.modify 5 (·+1)
      if !(chkR11 c f .allExits && chkR11 c f .tailOnly) then fails := fails.modify 6 (·+1)
      if !(chkR12 c f .allExits && chkR12 c f .tailOnly) then fails := fails.modify 7 (·+1)
      if !chkR13 c f then fails := fails.modify 8 (·+1)
      if !chkR15 c f then fails := fails.modify 9 (·+1)
      if !chkR17 c f then fails := fails.modify 10 (·+1)
      if !chkR16 c f then fails := fails.modify 11 (·+1)
      if !chkR20 c f then fails := fails.modify 12 (·+1)
      if !chkR24 c f then fails := fails.modify 13 (·+1)
    if !chkR8 f then fails := fails.modify 4 (·+1)
  return [("R1",fails[0]!),("R2",fails[1]!),("R4",fails[2]!),("mono",fails[3]!),("R8",fails[4]!),("R9",fails[5]!),("R11",fails[6]!),("R12",fails[7]!),("R13",fails[8]!),("R15",fails[9]!),("R17",fails[10]!),("R16",fails[11]!),("R20",fails[12]!),("R24",fails[13]!),("lowered",nLow)]

#eval runAll 42 400
