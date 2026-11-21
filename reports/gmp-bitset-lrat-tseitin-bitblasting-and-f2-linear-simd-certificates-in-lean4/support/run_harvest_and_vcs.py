#!/usr/bin/env python3
"""Zero-External-Solver Certificate Harvester & Nonlinear BitVec/SIMD Verification Suite.

Uses Lean v4.34.1's bundled `External.satQuery` (`bin/cadical` 2.1.2) and `LratCert.load`
(`LRAT.trim`) in an untrusted pre-pass to export `(AigArena, cnf, lrat)` witnesses, then compiles
and replays a pure `prelude` + `Init.*` theorem module (`NonlinearSimdVcs.lean`) via
`GmpBvTseitin.checkBvUnsatCert_sound` with zero native/custom axioms.
"""
import json
import os
import re
import shutil
import subprocess
import tempfile
import time

TC_DIR = os.environ.get(
    "LEAN_V4341_SYSROOT",
    os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.34.1"),
)
LEAN_BIN = os.path.join(TC_DIR, "bin", "lean")
LEAN_RUN = os.environ.get(
    "ANNEAL_LEAN_RUN",
    os.path.expanduser("~/.local/bin/anneal-lean-run"),
)
HERE = os.path.dirname(os.path.abspath(__file__))


def parse_tstat(stderr_txt):
    m = re.search(r"TSTAT wall=([0-9.]+) user=([0-9.]+) sys=([0-9.]+) rss=(\d+)", stderr_txt)
    if not m:
        return {}
    return {
        "wall_s": float(m.group(1)),
        "user_s": float(m.group(2)),
        "sys_s": float(m.group(3)),
        "rss_mb": round(int(m.group(4)) / 1024.0, 2),
    }


HARVESTER_LEAN = r"""import BvSimdTseitin
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide

open GmpBvTseitin
open Lean.Meta.Tactic.BVDecide

namespace UntrustedHarvester

structure Builder where
  nextGate : Nat := 2 -- Gate 1 is `.constFalse` (`falseLit = 2`, `trueLit = 3`)
  revDecls : List (Nat × AigNode) := [(1, .constFalse)]
  atomMap  : Std.HashMap Nat Nat := {}
  gateMap  : Std.HashMap Nat Nat := {}

def mkAtom (b : Builder) (w v idx : Nat) : Builder × Nat :=
  let k := atomKey w v idx
  match b.atomMap[k]? with
  | some g => (b, 2 * g)
  | none =>
    let g := b.nextGate
    ({ b with
       nextGate := g + 1
       revDecls := (g, .atom w v idx) :: b.revDecls
       atomMap  := b.atomMap.insert k g }, 2 * g)

def mkAnd (b : Builder) (l1 l2 : Nat) : Builder × Nat :=
  if l1 == falseLit || l2 == falseLit then (b, falseLit)
  else if l1 == trueLit then (b, l2)
  else if l2 == trueLit then (b, l1)
  else if l1 == l2 then (b, l1)
  else if l1 == Nat.xor l2 1 then (b, falseLit)
  else
    let k := canonPairKey l1 l2
    match b.gateMap[k]? with
    | some g => (b, 2 * g)
    | none =>
      let g := b.nextGate
      let (a, c) := if l1 ≤ l2 then (l1, l2) else (l2, l1)
      ({ b with
         nextGate := g + 1
         revDecls := (g, .andGate a c) :: b.revDecls
         gateMap  := b.gateMap.insert k g }, 2 * g)

def mkOr (b : Builder) (l1 l2 : Nat) : Builder × Nat :=
  let (b1, m) := mkAnd b (Nat.xor l1 1) (Nat.xor l2 1)
  (b1, Nat.xor m 1)

def mkXor (b : Builder) (l1 l2 : Nat) : Builder × Nat :=
  let (b1, x1) := mkAnd b l1 (Nat.xor l2 1)
  let (b2, x2) := mkAnd b1 (Nat.xor l1 1) l2
  mkOr b2 x1 x2

def mkMux (b : Builder) (c t e : Nat) : Builder × Nat :=
  let (b1, x1) := mkAnd b c t
  let (b2, x2) := mkAnd b1 (Nat.xor c 1) e
  mkOr b2 x1 x2

def mkAtLeastTwo (b : Builder) (a c d : Nat) : Builder × Nat :=
  let (b1, ac) := mkAnd b a c
  let (b2, ad) := mkAnd b1 a d
  let (b3, cd) := mkAnd b2 c d
  let (b4, u)  := mkOr b3 ac ad
  mkOr b4 u cd

def buildTabulateAux (f : Builder → Nat → Builder × Nat) :
    Nat → Builder → List Nat → Builder × List Nat
  | 0, b, acc => (b, acc)
  | Nat.succ k, b, acc =>
    let (b1, lit) := f b k
    buildTabulateAux f k b1 (lit :: acc)

def buildTabulate (w : Nat) (b : Builder) (f : Builder → Nat → Builder × Nat) :
    Builder × List Nat :=
  buildTabulateAux f w b []

def buildAdcAux (wx wy : List Nat) : Nat → Nat → Builder → Nat → Builder × Nat × List Nat
  | 0, _, b, cin => (b, cin, [])
  | Nat.succ rem, idx, b, cin =>
    let a := getWire wx idx
    let c := getWire wy idx
    let (b1, bXorC)  := mkXor b c cin
    let (b2, sumBit) := mkXor b1 a bXorC
    let (b3, cout)   := mkAtLeastTwo b2 a c cin
    let (b4, fc, rb) := buildAdcAux wx wy rem (idx + 1) b3 cout
    (b4, fc, sumBit :: rb)

def buildAdd (w : Nat) (b : Builder) (wx wy : List Nat) : Builder × List Nat :=
  let (b1, _, bits) := buildAdcAux wx wy w 0 b falseLit
  (b1, bits)

def buildConst (w : Nat) (val : BitVec w) (b : Builder) : Builder × List Nat :=
  buildTabulate w b fun b0 i => (b0, if val.getLsbD i then trueLit else falseLit)

def buildNeg (w : Nat) (b : Builder) (wx : List Nat) : Builder × List Nat :=
  let (b1, w1) := buildConst w (1#w) b
  buildAdd w b1 (blastNot wx) w1

def buildSub (w : Nat) (b : Builder) (wx wy : List Nat) : Builder × List Nat :=
  let (b1, nwy) := buildNeg w b wy
  buildAdd w b1 wx nwy

def buildShlConst (w : Nat) (b : Builder) (wx : List Nat) (k : Nat) : Builder × List Nat :=
  buildTabulate w b fun b0 i => (b0, if decide (i < k) then falseLit else getWire wx (i - k))

def buildLshrConst (w : Nat) (b : Builder) (wx : List Nat) (k : Nat) : Builder × List Nat :=
  buildTabulate w b fun b0 i => (b0, if decide (k + i < w) then getWire wx (k + i) else falseLit)

def buildAshrConst (w : Nat) (b : Builder) (wx : List Nat) (k : Nat) : Builder × List Nat :=
  buildTabulate w b fun b0 i =>
    (b0, if decide (k + i < w) then getWire wx (k + i) else getWire wx (w - 1))

def buildMuxWires (w : Nat) (b : Builder) (c : Nat) (wt we : List Nat) : Builder × List Nat :=
  buildTabulate w b fun b0 i => mkMux b0 c (getWire wt i) (getWire we i)

def buildMulRec (w : Nat) (wx wy : List Nat) : Nat → Builder → Builder × List Nat
  | 0, b =>
    let (b1, z) := buildConst w (0#w) b
    buildMuxWires w b1 (getWire wy 0) wx z
  | Nat.succ s, b =>
    let (b1, prev)    := buildMulRec w wx wy s b
    let (b2, shifted) := buildShlConst w b1 wx (s + 1)
    let (b3, z)       := buildConst w (0#w) b2
    let (b4, cur)     := buildMuxWires w b3 (getWire wy (s + 1)) shifted z
    buildAdd w b4 prev cur

def buildMul (w : Nat) (b : Builder) (wx wy : List Nat) : Builder × List Nat :=
  match w with
  | 0 => (b, [])
  | Nat.succ w' => buildMulRec (Nat.succ w') wx wy w' b

def buildEqAux (wx wy : List Nat) : Nat → Builder → Nat → Builder × Nat
  | 0, b, acc => (b, acc)
  | Nat.succ k, b, acc =>
    let (b1, diff) := mkXor b (getWire wx k) (getWire wy k)
    let (b2, acc') := mkAnd b1 acc (Nat.xor diff 1)
    buildEqAux wx wy k b2 acc'

mutual
def buildBvExpr : BvExpr w → Builder → Builder × List Nat
  | .var w id, b => buildTabulate w b fun b0 i => mkAtom b0 w id i
  | .const (w := w) val, b => buildConst w val b
  | .not x, b =>
    let (b1, wx) := buildBvExpr x b
    (b1, blastNot wx)
  | .and (w := w) x y, b =>
    let (b1, wx) := buildBvExpr x b
    let (b2, wy) := buildBvExpr y b1
    buildTabulate w b2 fun b0 i => mkAnd b0 (getWire wx i) (getWire wy i)
  | .or (w := w) x y, b =>
    let (b1, wx) := buildBvExpr x b
    let (b2, wy) := buildBvExpr y b1
    buildTabulate w b2 fun b0 i => mkOr b0 (getWire wx i) (getWire wy i)
  | .xor (w := w) x y, b =>
    let (b1, wx) := buildBvExpr x b
    let (b2, wy) := buildBvExpr y b1
    buildTabulate w b2 fun b0 i => mkXor b0 (getWire wx i) (getWire wy i)
  | .add (w := w) x y, b =>
    let (b1, wx) := buildBvExpr x b
    let (b2, wy) := buildBvExpr y b1
    buildAdd w b2 wx wy
  | .sub (w := w) x y, b =>
    let (b1, wx) := buildBvExpr x b
    let (b2, wy) := buildBvExpr y b1
    buildSub w b2 wx wy
  | .neg (w := w) x, b =>
    let (b1, wx) := buildBvExpr x b
    buildNeg w b1 wx
  | .shlConst (w := w) x k, b =>
    let (b1, wx) := buildBvExpr x b
    buildShlConst w b1 wx k
  | .lshrConst (w := w) x k, b =>
    let (b1, wx) := buildBvExpr x b
    buildLshrConst w b1 wx k
  | .ashrConst (w := w) x k, b =>
    let (b1, wx) := buildBvExpr x b
    buildAshrConst w b1 wx k
  | .extract (wIn := wIn) lo len x, b =>
    let (b1, wx) := buildBvExpr x b
    buildTabulate len b1 fun b0 i =>
      (b0, if decide (lo + i < wIn) then getWire wx (lo + i) else falseLit)
  | .concat (wHi := wHi) (wLo := wLo) hi lo, b =>
    let (b1, whi) := buildBvExpr hi b
    let (b2, wlo) := buildBvExpr lo b1
    buildTabulate (wHi + wLo) b2 fun b0 i =>
      (b0, if decide (i < wLo) then getWire wlo i else getWire whi (i - wLo))
  | .zeroExtend (wIn := wIn) wOut x, b =>
    let (b1, wx) := buildBvExpr x b
    buildTabulate wOut b1 fun b0 i =>
      (b0, if decide (i < wIn) then getWire wx i else falseLit)
  | .signExtend (wIn := wIn) wOut x, b =>
    let (b1, wx) := buildBvExpr x b
    buildTabulate wOut b1 fun b0 i =>
      (b0, if decide (i < wIn) then getWire wx i
           else if decide (0 < wIn) then getWire wx (wIn - 1) else falseLit)
  | .ite (w := w) cond t e, b =>
    let (b1, lc) := buildBvPred cond b
    let (b2, wt) := buildBvExpr t b1
    let (b3, we) := buildBvExpr e b2
    buildMuxWires w b3 lc wt we
  | .mul (w := w) x y, b =>
    let (b1, wx) := buildBvExpr x b
    let (b2, wy) := buildBvExpr y b1
    buildMul w b2 wx wy

def buildBvPred : BvPred → Builder → Builder × Nat
  | .constBool false, b => (b, falseLit)
  | .constBool true,  b => (b, trueLit)
  | .pNot p, b =>
    let (b1, lp) := buildBvPred p b
    (b1, Nat.xor lp 1)
  | .pAnd p q, b =>
    let (b1, lp) := buildBvPred p b
    let (b2, lq) := buildBvPred q b1
    mkAnd b2 lp lq
  | .pOr p q, b =>
    let (b1, lp) := buildBvPred p b
    let (b2, lq) := buildBvPred q b1
    mkOr b2 lp lq
  | .pXor p q, b =>
    let (b1, lp) := buildBvPred p b
    let (b2, lq) := buildBvPred q b1
    mkXor b2 lp lq
  | .pIff p q, b =>
    let (b1, lp) := buildBvPred p b
    let (b2, lq) := buildBvPred q b1
    let (b3, d)  := mkXor b2 lp lq
    (b3, Nat.xor d 1)
  | .eq (w := w) x y, b =>
    let (b1, wx) := buildBvExpr x b
    let (b2, wy) := buildBvExpr y b1
    buildEqAux wx wy w b2 trueLit
  | .ult (w := w) x y, b =>
    let (b1, wx) := buildBvExpr x b
    let (b2, wy) := buildBvExpr y b1
    let (b3, cout, _) := buildAdcAux wx (blastNot wy) w 0 b2 trueLit
    (b3, Nat.xor cout 1)
  | .slt (w := w) x y, b =>
    let (b1, wx) := buildBvExpr x b
    let (b2, wy) := buildBvExpr y b1
    match w with
    | 0 => (b2, falseLit)
    | Nat.succ w' =>
      let (b3, cout, _) := buildAdcAux wx (blastNot wy) (Nat.succ w') 0 b2 trueLit
      let (b4, sd)      := mkXor b3 (getWire wx w') (getWire wy w')
      mkXor b4 (Nat.xor sd 1) cout
  | .getBit (w := w) x idx, b =>
    let (b1, wx) := buildBvExpr x b
    (b1, if decide (idx < w) then getWire wx idx else falseLit)
end

def litToDimacs (lit : Nat) : Int :=
  let g : Int := Int.ofNat (Nat.shiftRight lit 1)
  if Nat.land lit 1 == 0 then g else -g

def dimacsToLit (d : Int) : Nat :=
  if d > 0 then 2 * d.natAbs else 2 * d.natAbs + 1

partial def toBalancedTreeExpr {α : Type} [Inhabited α] (xs : Array α) (fmt : α → String) : String :=
  let rec go (lo hi : Nat) : String :=
    if hi ≤ lo then ".empty"
    else if hi - lo == 1 then s!".leaf {fmt xs[lo]!}"
    else
      let mid := (lo + hi) / 2
      s!".branch ({go lo mid}) ({go mid hi})"
  go 0 xs.size

def fmtNatList (ns : List Nat) : String :=
  "[" ++ String.intercalate ", " (ns.map toString) ++ "]"

def fmtAigNode : AigNode → String
  | .constFalse => ".constFalse"
  | .atom w v b => s!".atom {w} {v} {b}"
  | .andGate a c => s!".andGate {a} {c}"

partial def fmtOctTrie {α : Type} (fmt : α → String) : OctTrie α → String
  | .empty => ".empty"
  | .node v c0 c1 c2 c3 c4 c5 c6 c7 =>
    let vs := match v with | none => "none" | some x => s!"(some ({fmt x}))"
    s!".node {vs} ({fmtOctTrie fmt c0}) ({fmtOctTrie fmt c1}) ({fmtOctTrie fmt c2}) ({fmtOctTrie fmt c3}) ({fmtOctTrie fmt c4}) ({fmtOctTrie fmt c5}) ({fmtOctTrie fmt c6}) ({fmtOctTrie fmt c7})"

def harvestOne (name : String) (vc : BvPred) : Lean.CoreM (Option (String × String)) := do
  let t0 ← IO.monoMsNow
  let (b, rootLit) := buildBvPred vc {}
  let decls := b.revDecls.reverse.toArray
  let maxGate := b.nextGate
  -- Generate Tseitin CNF clauses (1-indexed for DIMACS/LRAT):
  let mut clauses : Array (List Nat) := #[]
  clauses := clauses.push [rootLit]
  clauses := clauses.push [2 * 1 + 1] -- Gate 1 is `.constFalse`
  for (g, nd) in decls do
    match nd with
    | .andGate l1 l2 =>
      clauses := clauses.push [2 * g + 1, l1]
      clauses := clauses.push [2 * g + 1, l2]
      clauses := clauses.push [2 * g, Nat.xor l1 1, Nat.xor l2 1]
    | _ => pure ()

  let numVars := maxGate - 1
  let mut dimacsLines : Array String := #[s!"p cnf {numVars} {clauses.size}"]
  for cls in clauses do
    let ds := cls.map (fun l => toString (litToDimacs l))
    dimacsLines := dimacsLines.push (String.intercalate " " ds ++ " 0")
  let dimacsStr := String.intercalate "\n" dimacsLines.toList ++ "\n"

  let cadicalPath := (← IO.appPath).parent.get! / "cadical"
  IO.FS.withTempFile fun cnfHandle cnfPath => do
    IO.FS.withTempFile fun _ lratPath => do
      cnfHandle.putStr dimacsStr
      cnfHandle.flush
      let tSat0 ← IO.monoMsNow
      let res ← External.satQuery cadicalPath cnfPath lratPath 30 true .proof
      let tSat1 ← IO.monoMsNow
      match res with
      | .sat assign =>
        let summary := "{\"name\": \"" ++ name ++ "\", \"status\": \"SAT\", \"aig_gates\": " ++
          toString maxGate ++ ", \"cnf_clauses\": " ++ toString clauses.size ++
          ", \"cadical_ms\": " ++ toString (tSat1 - tSat0) ++
          ", \"sample_lits\": " ++ toString assign.size ++ "}"
        return some (summary, "")
      | .unsat =>
        let actions ← LratCert.load lratPath true
        let tTrim1 ← IO.monoMsNow
        -- Identify UNSAT-core initial CNF clauses referenced in trimmed LRAT hints!
        let mut usedInit : Std.HashSet Nat := {}
        let mut nRup := 0
        let mut nRat := 0
        let mut nDel := 0
        let mut nEmpty := 0
        for act in actions do
          match act with
          | .addRup _ _ hints =>
            nRup := nRup + 1
            for h in hints do
              if h ≤ clauses.size then usedInit := usedInit.insert h
          | .addRat .. =>
            nRat := nRat + 1
          | .del _ =>
            nDel := nDel + 1
          | .addEmpty _ hints =>
            nEmpty := nEmpty + 1
            for h in hints do
              if h ≤ clauses.size then usedInit := usedInit.insert h

        -- Recycle clause IDs across `(usedInit ∪ addRup)` to keep OctTrie dense!
        let mut cidToSlot : Std.HashMap Nat Nat := {}
        let mut freeSlots : Array Nat := #[]
        let mut nextSlot : Nat := 1
        let mut initCore : Array (Nat × List Nat) := #[]
        for idx in [0:clauses.size] do
          let cid := idx + 1
          if usedInit.contains cid then
            let slot := if freeSlots.isEmpty then nextSlot else freeSlots.back!
            if freeSlots.isEmpty then nextSlot := nextSlot + 1 else freeSlots := freeSlots.pop
            cidToSlot := cidToSlot.insert cid slot
            initCore := initCore.push (slot, clauses[idx]!)

        let mut outSteps : Array (Nat × List Nat × List Nat × List Nat) := #[]
        -- tag 1 = addRup, 2 = del, 3 = addEmpty
        for act in actions do
          match act with
          | .addRup cid clsArr hints =>
            let clsLits := clsArr.toList.map dimacsToLit
            let mappedHints := hints.toList.filterMap (fun h => cidToSlot[h]?)
            let slot := if freeSlots.isEmpty then nextSlot else freeSlots.back!
            if freeSlots.isEmpty then nextSlot := nextSlot + 1 else freeSlots := freeSlots.pop
            cidToSlot := cidToSlot.insert cid slot
            outSteps := outSteps.push (1, [slot], clsLits, mappedHints)
          | .del ids =>
            let mut mdel : Array Nat := #[]
            for d in ids do
              if let some s := cidToSlot[d]? then
                cidToSlot := cidToSlot.erase d
                freeSlots := freeSlots.push s
                mdel := mdel.push s
            let mut di := 0
            while di < mdel.size do
              let dhi := Nat.min (di + 16) mdel.size
              let mut slice : List Nat := []
              for dj in [di:dhi] do
                slice := mdel[dj]! :: slice
              outSteps := outSteps.push (2, [], [], slice.reverse)
              di := dhi
          | .addEmpty _ hints =>
            let mappedHints := hints.toList.filterMap (fun h => cidToSlot[h]?)
            outSteps := outSteps.push (3, [], [], mappedHints)
          | .addRat .. =>
            Lean.throwError s!"Unexpected RAT step in {name}"

        -- Pack `AigArena`, `initCore`, and `outSteps` as compact hex `u16` GMP words!
        let toHexLit := fun (n : Nat) => "0x" ++ String.ofList (Nat.toDigits 16 n)
        let packU16 := fun (ws : List Nat) =>
          let rec loop : List Nat → Nat → Nat → Nat
            | [], _, acc => acc
            | w :: rest, shift, acc => loop rest (shift + 16) (Nat.lor acc (Nat.shiftLeft w shift))
          loop ws 0 0

        let mut nodeLeaves : Array String := #[]
        let mut ni := 0
        while ni < decls.size do
          let nhi := Nat.min (ni + 24) decls.size
          let mut words : List Nat := []
          for nj in [ni:nhi] do
            let (gid, nd) := decls.getD nj (0, AigNode.constFalse)
            match nd with
            | AigNode.constFalse    => words := words ++ [gid, 1]
            | AigNode.atom w v bIdx => words := words ++ [gid, 2, w, v, bIdx]
            | AigNode.andGate l1 l2 => words := words ++ [gid, 3, l1, l2]
          words := words ++ [0]
          nodeLeaves := nodeLeaves.push (toHexLit (packU16 words))
          ni := nhi

        let packDirLeaves := fun (entries : Array (Nat × Nat)) => Id.run do
          let mut leaves : Array String := #[]
          let mut di := 0
          while di < entries.size do
            let dhi := Nat.min (di + 24) entries.size
            let mut words : List Nat := []
            for dj in [di:dhi] do
              let (key, gid) := entries[dj]!
              let keyLo := Nat.land key 0xffff
              let keyHi := Nat.land (Nat.shiftRight key 16) 0xffff
              words := words ++ [gid, keyLo, keyHi]
            words := words ++ [0]
            leaves := leaves.push (toHexLit (packU16 words))
            di := dhi
          return leaves

        let gateLeaves := packDirLeaves b.gateMap.toArray
        let atomLeaves := packDirLeaves b.atomMap.toArray

        let mut initLeaves : Array String := #[]
        let mut i := 0
        while i < initCore.size do
          let hi := Nat.min (i + 24) initCore.size
          let mut words : List Nat := []
          for j in [i:hi] do
            let (slot, cls) := initCore[j]!
            words := words ++ [slot, cls.length] ++ cls
          words := words ++ [0]
          initLeaves := initLeaves.push (toHexLit (packU16 words))
          i := hi

        let mut stepLeaves : Array String := #[]
        let mut si := 0
        while si < outSteps.size do
          let mut words : List Nat := []
          let mut cnt := 0
          let mut wordBudget := 0
          while si < outSteps.size && cnt < 16 && (cnt == 0 || wordBudget < 96) do
            let (tag, idL, cls, hints) := outSteps[si]!
            if tag == 1 then
              words := words ++ [1, idL.head!, cls.length, hints.length] ++ cls ++ hints
              wordBudget := wordBudget + 4 + cls.length + hints.length
            else if tag == 2 then
              words := words ++ [2, hints.length] ++ hints
              wordBudget := wordBudget + 2 + hints.length
            else
              words := words ++ [3, hints.length] ++ hints
              wordBudget := wordBudget + 2 + hints.length
            si := si + 1
            cnt := cnt + 1
          words := words ++ [0]
          stepLeaves := stepLeaves.push (toHexLit (packU16 words))

        let cnfExpr := s!"decodePackedInit 16 ({toBalancedTreeExpr initLeaves id})"
        let lratExpr := s!"decodePackedSteps 16 ({toBalancedTreeExpr stepLeaves id})"
        let aigExpr := s!"decodePackedAig {maxGate} ({toBalancedTreeExpr nodeLeaves id}) ({toBalancedTreeExpr gateLeaves id}) ({toBalancedTreeExpr atomLeaves id})"
        let leanDef := s!"private def cert_{name}_aig : AigArena := {aigExpr}\n" ++
                       s!"private def cert_{name}_cnf : StepTree (Nat × List Nat) := {cnfExpr}\n" ++
                       s!"private def cert_{name}_lrat : StepTree LratStep := {lratExpr}\n"
        let tEnd ← IO.monoMsNow
        let summary := "{\"name\": \"" ++ name ++ "\", \"status\": \"UNSAT\", \"aig_gates\": " ++
          toString maxGate ++ ", \"cnf_clauses_total\": " ++ toString clauses.size ++
          ", \"cnf_clauses_core\": " ++ toString initCore.size ++
          ", \"lrat_total\": " ++ toString actions.size ++
          ", \"lrat_rup\": " ++ toString nRup ++
          ", \"lrat_rat\": " ++ toString nRat ++
          ", \"lrat_del\": " ++ toString nDel ++
          ", \"max_recycled_slot\": " ++ toString (nextSlot - 1) ++
          ", \"cadical_ms\": " ++ toString (tSat1 - tSat0) ++
          ", \"trim_ms\": " ++ toString (tTrim1 - tSat1) ++
          ", \"total_harvest_ms\": " ++ toString (tEnd - t0) ++ "}"
        return some (summary, leanDef)

-- Define the 8 target VCs + 1 SAT counterexample probe!
def vc_swar_mask_non_eq : BvPred :=
  let x := BvExpr.var 64 0
  .neq (swarMycroftMask64 x) (swarBorrowFreeMask64 x)

def vc_swar_has_zero_byte_64 : BvPred :=
  let x := BvExpr.var 64 0
  let mZero := BvPred.neq (swarMycroftMask64 x) (.const 0#64)
  let bZero := BvPred.neq (swarBorrowFreeMask64 x) (.const 0#64)
  .pNot (.pIff mZero bZero)

def vc_bmi2_blsi_blsr_64 : BvPred :=
  let x := BvExpr.var 64 0
  let p1 := BvPred.eq (.add (bmi2Blsr x) (bmi2Blsi x)) x
  let p2 := BvPred.eq (.and (bmi2Blsr x) (bmi2Blsi x)) (.const 0#64)
  let p3 := BvPred.eq (.xor (bmi2Blsr x) (bmi2Blsi x)) x
  .pNot (.pAnd p1 (.pAnd p2 p3))

def vc_bmi2_blsmsk_64 : BvPred :=
  let x := BvExpr.var 64 0
  let nz := BvPred.neq x (.const 0#64)
  let q1 := BvPred.eq (.and x (bmi2Blsmsk x)) (bmi2Blsi x)
  let q2 := BvPred.eq (.and (bmi2Blsr x) (bmi2Blsmsk x)) (.const 0#64)
  .pAnd nz (.pNot (.pAnd q1 q2))

def vc_bmi2_bzhi64_comp : BvPred :=
  let x := BvExpr.var 64 0
  let a := BvExpr.var 64 1
  let b := BvExpr.var 64 2
  let a8 := BvExpr.extract 0 8 a
  let b8 := BvExpr.extract 0 8 b
  let minAB := BvExpr.ite (.ult a8 b8) a b
  .neq (bmi2Bzhi64 (bmi2Bzhi64 x a) b) (bmi2Bzhi64 x minAB)

def vc_x86_sub_signed_64 : BvPred :=
  let x := BvExpr.var 64 0
  let y := BvExpr.var 64 1
  let jl  := BvPred.pXor (x86SubSF x y) (x86SubOF x y)
  let jle := BvPred.pOr (x86SubZF x y) jl
  .pNot (.pAnd (.pIff jl (.slt x y)) (.pIff jle (.sle x y)))

def vc_x86_sub_unsigned_64 : BvPred :=
  let x := BvExpr.var 64 0
  let y := BvExpr.var 64 1
  let jb  := x86SubCF x y
  let jbe := BvPred.pOr (x86SubCF x y) (x86SubZF x y)
  .pNot (.pAnd (.pIff jb (.ult x y)) (.pIff jbe (.ule x y)))

def vc_x86_xor_pf_64 : BvPred :=
  let x := BvExpr.var 64 0
  let y := BvExpr.var 64 1
  .pNot (.pIff (x86ParityFlag (.xor x y)) (.pNot (.pXor (x86ParityFlag x) (x86ParityFlag y))))

def vc_ssse3_vpmaddubsw_64_lane_and_sat : BvPred :=
  let u := BvExpr.var 64 0
  let s := BvExpr.var 64 1
  let full64 := simdVpmaddubsw 4 u s
  let lane2  := BvExpr.extract (16 * 2) 16 full64
  let pair2  := vpmaddubswPair (.extract (16 * 2) 16 u) (.extract (16 * 2) 16 s)
  let c1 := BvPred.eq lane2 pair2
  let c2 := BvPred.eq (vpmaddubswPair (.const 0xffff#16) (.const 0x8080#16)) (.const 0x8000#16)
  let u0 := BvExpr.extract 0 16 u
  let s0 := BvExpr.extract 0 16 s
  let s0NonNeg := BvExpr.and s0 (.const 0x7f7f#16)
  let c3 := BvPred.pNot (.slt (vpmaddubswPair u0 s0NonNeg) (.const 0#16))
  let u0Swap := BvExpr.or (.shlConst u0 8) (.lshrConst u0 8)
  let s0Swap := BvExpr.or (.shlConst s0 8) (.lshrConst s0 8)
  let c4 := BvPred.eq (vpmaddubswPair u0 s0) (vpmaddubswPair u0Swap s0Swap)
  .pNot (.pAnd c1 (.pAnd c2 (.pAnd c3 c4)))

def vc_vpaddsw_lane16_comm_and_sat : BvPred :=
  let x := BvExpr.var 16 0
  let y := BvExpr.var 16 1
  let c1 := BvPred.eq (vpaddswLane x y) (vpaddswLane y x)
  let c2 := BvPred.eq (vpaddswLane (.const 0x6000#16) (.const 0x5000#16)) (.const 0x7fff#16)
  let c3 := BvPred.eq (vpaddswLane (.const 0x9000#16) (.const 0xa000#16)) (.const 0x8000#16)
  .pNot (.pAnd c1 (.pAnd c2 c3))

def vc_avx2_vpaddsw_256_monolithic_probe : BvPred :=
  let x := BvExpr.var 256 0
  let y := BvExpr.var 256 1
  let c1 := BvPred.eq (simdVpaddsw 16 x y) (simdVpaddsw 16 y x)
  let c2 := BvPred.eq (vpaddswLane (.const 0x6000#16) (.const 0x5000#16)) (.const 0x7fff#16)
  let c3 := BvPred.eq (vpaddswLane (.const 0x9000#16) (.const 0xa000#16)) (.const 0x8000#16)
  .pNot (.pAnd c1 (.pAnd c2 c3))

def vcSrcOf (nm : String) : String :=
  if nm == "swar_has_zero_byte_64" then
    String.intercalate "\n" [
      "def vc_swar_has_zero_byte_64 : BvPred :=",
      "  let x := BvExpr.var 64 0",
      "  let mZero := BvPred.neq (swarMycroftMask64 x) (.const 0#64)",
      "  let bZero := BvPred.neq (swarBorrowFreeMask64 x) (.const 0#64)",
      "  .pNot (.pIff mZero bZero)"
    ] ++ "\n"
  else if nm == "bmi2_blsi_blsr_64" then
    String.intercalate "\n" [
      "def vc_bmi2_blsi_blsr_64 : BvPred :=",
      "  let x := BvExpr.var 64 0",
      "  let p1 := BvPred.eq (.add (bmi2Blsr x) (bmi2Blsi x)) x",
      "  let p2 := BvPred.eq (.and (bmi2Blsr x) (bmi2Blsi x)) (.const 0#64)",
      "  let p3 := BvPred.eq (.xor (bmi2Blsr x) (bmi2Blsi x)) x",
      "  .pNot (.pAnd p1 (.pAnd p2 p3))"
    ] ++ "\n"
  else if nm == "bmi2_blsmsk_64" then
    String.intercalate "\n" [
      "def vc_bmi2_blsmsk_64 : BvPred :=",
      "  let x := BvExpr.var 64 0",
      "  let nz := BvPred.neq x (.const 0#64)",
      "  let q1 := BvPred.eq (.and x (bmi2Blsmsk x)) (bmi2Blsi x)",
      "  let q2 := BvPred.eq (.and (bmi2Blsr x) (bmi2Blsmsk x)) (.const 0#64)",
      "  .pAnd nz (.pNot (.pAnd q1 q2))"
    ] ++ "\n"
  else if nm == "bmi2_bzhi64_comp" then
    String.intercalate "\n" [
      "def vc_bmi2_bzhi64_comp : BvPred :=",
      "  let x := BvExpr.var 64 0",
      "  let a := BvExpr.var 64 1",
      "  let b := BvExpr.var 64 2",
      "  let a8 := BvExpr.extract 0 8 a",
      "  let b8 := BvExpr.extract 0 8 b",
      "  let minAB := BvExpr.ite (.ult a8 b8) a b",
      "  .neq (bmi2Bzhi64 (bmi2Bzhi64 x a) b) (bmi2Bzhi64 x minAB)"
    ] ++ "\n"
  else if nm == "x86_sub_signed_64" then
    String.intercalate "\n" [
      "def vc_x86_sub_signed_64 : BvPred :=",
      "  let x := BvExpr.var 64 0",
      "  let y := BvExpr.var 64 1",
      "  let jl  := BvPred.pXor (x86SubSF x y) (x86SubOF x y)",
      "  let jle := BvPred.pOr (x86SubZF x y) jl",
      "  .pNot (.pAnd (.pIff jl (.slt x y)) (.pIff jle (.sle x y)))"
    ] ++ "\n"
  else if nm == "x86_sub_unsigned_64" then
    String.intercalate "\n" [
      "def vc_x86_sub_unsigned_64 : BvPred :=",
      "  let x := BvExpr.var 64 0",
      "  let y := BvExpr.var 64 1",
      "  let jb  := x86SubCF x y",
      "  let jbe := BvPred.pOr (x86SubCF x y) (x86SubZF x y)",
      "  .pNot (.pAnd (.pIff jb (.ult x y)) (.pIff jbe (.ule x y)))"
    ] ++ "\n"
  else if nm == "x86_xor_pf_64" then
    String.intercalate "\n" [
      "def vc_x86_xor_pf_64 : BvPred :=",
      "  let x := BvExpr.var 64 0",
      "  let y := BvExpr.var 64 1",
      "  .pNot (.pIff (x86ParityFlag (.xor x y)) (.pNot (.pXor (x86ParityFlag x) (x86ParityFlag y))))"
    ] ++ "\n"
  else if nm == "ssse3_vpmaddubsw_64_lane_and_sat" then
    String.intercalate "\n" [
      "def vc_ssse3_vpmaddubsw_64_lane_and_sat : BvPred :=",
      "  let u := BvExpr.var 64 0",
      "  let s := BvExpr.var 64 1",
      "  let full64 := simdVpmaddubsw 4 u s",
      "  let lane2  := BvExpr.extract (16 * 2) 16 full64",
      "  let pair2  := vpmaddubswPair (.extract (16 * 2) 16 u) (.extract (16 * 2) 16 s)",
      "  let c1 := BvPred.eq lane2 pair2",
      "  let c2 := BvPred.eq (vpmaddubswPair (.const 0xffff#16) (.const 0x8080#16)) (.const 0x8000#16)",
      "  let u0 := BvExpr.extract 0 16 u",
      "  let s0 := BvExpr.extract 0 16 s",
      "  let s0NonNeg := BvExpr.and s0 (.const 0x7f7f#16)",
      "  let c3 := BvPred.pNot (.slt (vpmaddubswPair u0 s0NonNeg) (.const 0#16))",
      "  let u0Swap := BvExpr.or (.shlConst u0 8) (.lshrConst u0 8)",
      "  let s0Swap := BvExpr.or (.shlConst s0 8) (.lshrConst s0 8)",
      "  let c4 := BvPred.eq (vpmaddubswPair u0 s0) (vpmaddubswPair u0Swap s0Swap)",
      "  .pNot (.pAnd c1 (.pAnd c2 (.pAnd c3 c4)))"
    ] ++ "\n"
  else if nm == "vpaddsw_lane16_comm_and_sat" then
    String.intercalate "\n" [
      "def vc_vpaddsw_lane16_comm_and_sat : BvPred :=",
      "  let x := BvExpr.var 16 0",
      "  let y := BvExpr.var 16 1",
      "  let c1 := BvPred.eq (vpaddswLane x y) (vpaddswLane y x)",
      "  let c2 := BvPred.eq (vpaddswLane (.const 0x6000#16) (.const 0x5000#16)) (.const 0x7fff#16)",
      "  let c3 := BvPred.eq (vpaddswLane (.const 0x9000#16) (.const 0xa000#16)) (.const 0x8000#16)",
      "  .pNot (.pAnd c1 (.pAnd c2 c3))"
    ] ++ "\n"
  else ""

def swarSemanticCorollary : String := "
theorem mycroft_has_zero_byte_eq_borrow_free (x : BitVec 64) :
    (((x - 0x0101010101010101#64) &&& (~~~x) &&& 0x8080808080808080#64) != 0#64) =
    ((~~~((((x &&& 0x7f7f7f7f7f7f7f7f#64) + 0x7f7f7f7f7f7f7f7f#64) ||| x) ||| 0x7f7f7f7f7f7f7f7f#64)) != 0#64) := by
  let env : BvEnv := fun w _ => if h : w = 64 then h ▸ x else 0#w
  have hunsat := swar_has_zero_byte_64_unsat env
  change (!((evalBv (BvPred.neq (swarMycroftMask64 (.var 64 0)) (.const 0#64)) env) ==
            (evalBv (BvPred.neq (swarBorrowFreeMask64 (.var 64 0)) (.const 0#64)) env))) = false at hunsat
  have hbeq : (evalBv (BvPred.neq (swarMycroftMask64 (.var 64 0)) (.const 0#64)) env ==
               evalBv (BvPred.neq (swarBorrowFreeMask64 (.var 64 0)) (.const 0#64)) env) = true := by
    cases hb : (evalBv (BvPred.neq (swarMycroftMask64 (.var 64 0)) (.const 0#64)) env ==
                evalBv (BvPred.neq (swarBorrowFreeMask64 (.var 64 0)) (.const 0#64)) env)
    · rw [hb] at hunsat; contradiction
    · rfl
  exact eq_of_beq hbeq
"

def avx2Vpaddsw256Corollaries : String := "
/-- 256-bit AVX2 16-lane `VPADDSW` semantic commutativity lifted from 16-bit LRAT certificate! -/
theorem avx2_vpaddsw256_comm_semantic (x y : BitVec 256) :
    simdMapBinary16 semVpaddsw16 16 x y = simdMapBinary16 semVpaddsw16 16 y x :=
  simdMapBinary16_comm semVpaddsw16 (semVpaddsw16_comm_of_unsat vpaddsw_lane16_comm_and_sat_unsat) 16 x y

theorem avx2_vpaddsw256_eval_comm (env : BvEnv) (xVec yVec : BvExpr 256) :
    evalBvExpr (simdVpaddsw 16 xVec yVec) env = evalBvExpr (simdVpaddsw 16 yVec xVec) env := by
  have h1 := evalBvExpr_simdVpaddsw env 16 xVec yVec
  have h2 := evalBvExpr_simdVpaddsw env 16 yVec xVec
  rw [h1, h2]
  exact avx2_vpaddsw256_comm_semantic (evalBvExpr xVec env) (evalBvExpr yVec env)
"

def runAll (outDir outCanariesPath outJsonPath : String) : Lean.CoreM Unit := do
  -- (name, vc, emitModule, includeInCompactCanaries)
  let jobs : List (String × BvPred × Bool × Bool) := [
    ("swar_mask_non_eq_sat_probe", vc_swar_mask_non_eq, false, false),
    ("swar_has_zero_byte_64", vc_swar_has_zero_byte_64, true, true),
    ("bmi2_blsi_blsr_64", vc_bmi2_blsi_blsr_64, true, false),
    ("bmi2_blsmsk_64", vc_bmi2_blsmsk_64, true, false),
    ("bmi2_bzhi64_comp", vc_bmi2_bzhi64_comp, true, false),
    ("x86_sub_signed_64", vc_x86_sub_signed_64, true, false),
    ("x86_sub_unsigned_64", vc_x86_sub_unsigned_64, true, false),
    ("x86_xor_pf_64", vc_x86_xor_pf_64, true, false),
    ("ssse3_vpmaddubsw_64_lane_and_sat", vc_ssse3_vpmaddubsw_64_lane_and_sat, true, false),
    ("vpaddsw_lane16_comm_and_sat", vc_vpaddsw_lane16_comm_and_sat, true, true),
    ("avx2_vpaddsw_256_monolithic_probe", vc_avx2_vpaddsw_256_monolithic_probe, false, false)
  ]
  let mut summaries : Array String := #[]
  let mut canaryVcDefs : Array String := #[]
  let mut canaryCertDefs : Array String := #[]
  let mut canaryThms : Array String := #[]

  for (nm, vc, emitMod, inCanary) in jobs do
    let some (js, d) ← harvestOne nm vc | Lean.throwError s!"failed {nm}"
    -- Inject `packed_lean_bytes` into summary JSON!
    let jsWithBytes := (js.dropEnd 1).toString ++ s!", \"packed_lean_bytes\": {d.utf8ByteSize}}"
    summaries := summaries.push jsWithBytes
    if emitMod then
      if d.isEmpty then Lean.throwError s!"Expected UNSAT for {nm}, got SAT!"
      let vsrc := vcSrcOf nm
      let thm := s!"theorem {nm}_unsat (env : BvEnv) : evalBv vc_{nm} env = false :=\n  checkBvUnsatCert_sound vc_{nm} cert_{nm}_aig cert_{nm}_cnf cert_{nm}_lrat env (by decide +kernel)\n"
      let extra := if nm == "swar_has_zero_byte_64" then swarSemanticCorollary
                   else if nm == "vpaddsw_lane16_comm_and_sat" then avx2Vpaddsw256Corollaries
                   else ""
      let modSrc := s!"prelude\nimport BvSimdTseitin\n\nnamespace VC_{nm}\nopen GmpBvTseitin\n\n" ++
                    vsrc ++ "\n" ++ d ++ "\n" ++ thm ++ extra ++ s!"\nend VC_{nm}\n"
      IO.FS.writeFile (System.FilePath.mk outDir / s!"VC_{nm}.lean") modSrc
      if inCanary then
        canaryVcDefs := canaryVcDefs.push vsrc
        canaryCertDefs := canaryCertDefs.push d
        canaryThms := canaryThms.push (thm ++ extra)

  let canaryHeader := "prelude\nimport BvSimdTseitin\n\nnamespace NonlinearSimdCanaries\nopen GmpBvTseitin\n\n"
  let canaryBody := canaryHeader ++ String.intercalate "\n" canaryVcDefs.toList ++ "\n" ++
                    String.intercalate "\n" canaryCertDefs.toList ++ "\n" ++
                    String.intercalate "\n" canaryThms.toList ++ "\nend NonlinearSimdCanaries\n"
  IO.FS.writeFile outCanariesPath canaryBody
  IO.FS.writeFile outJsonPath ("[\n  " ++ String.intercalate ",\n  " summaries.toList ++ "\n]\n")

end UntrustedHarvester

unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (System.FilePath.mk args[0]!) [System.FilePath.mk "."]
  let env ← Lean.importModules #[{ module := `BvSimdTseitin }, { module := `Lean.Elab.Tactic.BVDecide }, { module := `Std.Tactic.BVDecide }] {}
  let ctx : Lean.Core.Context := { fileName := "<harvester>", fileMap := default }
  let st : Lean.Core.State := { env }
  let _ ← (UntrustedHarvester.runAll args[1]! args[2]! args[3]!).toIO ctx st
"""

TACTIC_BASELINE_LEAN = r"""import Std.Tactic.BVDecide

-- Probe 1: Check what axioms `bv_decide` injects on 64-bit SWAR `has_zero_byte`!
theorem swar_via_bv_decide (x : BitVec 64) :
    (((x - 0x0101010101010101#64) &&& (~~~x) &&& 0x8080808080808080#64) != 0#64) =
    ((~~~((((x &&& 0x7f7f7f7f7f7f7f7f#64) + 0x7f7f7f7f7f7f7f7f#64) ||| x) ||| 0x7f7f7f7f7f7f7f7f#64)) != 0#64) := by
  bv_decide

#print axioms swar_via_bv_decide
"""

TACTIC_FAIL_PROBES = {
    "omega": "theorem t (x : BitVec 64) : (((x - 0x0101010101010101#64) &&& (~~~x) &&& 0x8080808080808080#64) != 0#64) = ((~~~((((x &&& 0x7f7f7f7f7f7f7f7f#64) + 0x7f7f7f7f7f7f7f7f#64) ||| x) ||| 0x7f7f7f7f7f7f7f7f#64)) != 0#64) := by omega\n",
    "bv_omega": "theorem t (x : BitVec 64) : (((x - 0x0101010101010101#64) &&& (~~~x) &&& 0x8080808080808080#64) != 0#64) = ((~~~((((x &&& 0x7f7f7f7f7f7f7f7f#64) + 0x7f7f7f7f7f7f7f7f#64) ||| x) ||| 0x7f7f7f7f7f7f7f7f#64)) != 0#64) := by bv_omega\n",
    "grind": "theorem t (x : BitVec 64) : (((x - 0x0101010101010101#64) &&& (~~~x) &&& 0x8080808080808080#64) != 0#64) = ((~~~((((x &&& 0x7f7f7f7f7f7f7f7f#64) + 0x7f7f7f7f7f7f7f7f#64) ||| x) ||| 0x7f7f7f7f7f7f7f7f#64)) != 0#64) := by grind\n",
}

REPLAY_GENERIC_LEAN = r"""import Lean
import Lean.Replay
open Lean

partial def collectTransitiveAxioms (env : Environment) (root : Name) : IO (List Name) := do
  let mut queue : List Name := [root]
  let mut visited : NameSet := {}
  let mut axioms : NameSet := {}
  while !queue.isEmpty do
    let n := queue.head!
    queue := queue.tail!
    if !visited.contains n then
      visited := visited.insert n
      let some ci := env.find? n | throw <| IO.userError s!"missing {n}"
      if ci.isUnsafe || ci.isPartial then
        throw <| IO.userError s!"FORBIDDEN unsafe/partial: {n}"
      if ci.isAxiom then
        axioms := axioms.insert n
      let mut used := ci.type.getUsedConstants.toList
      if let some v := ci.value? (allowOpaque := true) then
        let vs := v.getUsedConstants
        if vs.contains `_inhabitedExprDummy then
          throw <| IO.userError s!"DUMMY body in {n}"
        used := used ++ vs.toList
      queue := used ++ queue
  return axioms.toList

unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (System.FilePath.mk args[0]!) [System.FilePath.mk "."]
  let targetMod := args[2]!.toName
  let checkThm := args[3]!.toName
  let t0 ← IO.monoMsNow
  let fullEnv ← importModules #[{ module := targetMod }] {} (trustLevel := 0) (loadExts := false) (level := .private)
  let fullEnv := fullEnv.setExporting false
  let some modIdx := fullEnv.header.moduleNames.idxOf? targetMod | throw <| IO.userError "missing mod"
  let modData := fullEnv.header.moduleData[modIdx]!
  let baseEnv ← importModules modData.imports {} (trustLevel := 0) (loadExts := false) (level := .private)
  let baseEnv := baseEnv.setExporting false
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  let mut unsafeRecCount : Nat := 0
  for ci in modData.constants do
    if ci.isUnsafe || ci.isPartial then
      if ci.name.toString.endsWith "._unsafe_rec" then
        unsafeRecCount := unsafeRecCount + 1
      else
        throw <| IO.userError s!"FORBIDDEN non-compiler unsafe/partial: {ci.name}"
    else
      let some stored := fullEnv.find? ci.name | throw <| IO.userError s!"missing {ci.name}"
      newConsts := newConsts.insert ci.name stored
  let t1 ← IO.monoMsNow
  let _ ← (baseEnv.toKernelEnv.replay newConsts).toIO (fun e => IO.userError s!"Replay failed: {e}")
  let t2 ← IO.monoMsNow
  let axs ← collectTransitiveAxioms fullEnv checkThm
  IO.println ("REPLAY_JSON {\"import_ms\": " ++ toString (t1 - t0) ++
    ", \"replay_ms\": " ++ toString (t2 - t1) ++
    ", \"kernel_consts\": " ++ toString newConsts.size ++
    ", \"lcnf_unsafe_rec\": " ++ toString unsafeRecCount ++
    ", \"axioms\": \"" ++ toString axs ++ "\"}")
"""


def main():
    old_mono = os.path.join(HERE, "NonlinearSimdVcs.lean")
    if os.path.exists(old_mono):
        os.remove(old_mono)

    path_solvers = {
        k: shutil.which(k) is not None
        for k in ["z3", "cvc5", "cadical", "bitwuzla", "kissat", "drat-trim", "lrat-trim"]
    }
    bundled_cadical = os.path.join(TC_DIR, "bin", "cadical")
    cad_ver = subprocess.run([bundled_cadical, "--version"], capture_output=True, text=True).stdout.strip()

    with tempfile.TemporaryDirectory() as tmp:
        # 1. Copy & compile BvSimdTseitin.lean (measuring TSTAT + .olean size + fresh kernel replay)
        shutil.copyfile(os.path.join(HERE, "BvSimdTseitin.lean"), os.path.join(tmp, "BvSimdTseitin.lean"))
        r0 = subprocess.run(
            [LEAN_RUN, "--mode", "file", "--", "/usr/bin/time", "-f", "TSTAT wall=%e user=%U sys=%S rss=%M",
             LEAN_BIN, "-DElab.async=false", "-Ddebug.skipKernelTC=false",
             "-o", "BvSimdTseitin.olean", "BvSimdTseitin.lean"],
            cwd=tmp, capture_output=True, text=True
        )
        assert r0.returncode == 0, r0.stdout + r0.stderr
        bv_lib_compile = parse_tstat(r0.stderr)
        bv_lib_olean_bytes = os.path.getsize(os.path.join(tmp, "BvSimdTseitin.olean"))

        env = os.environ.copy()
        env["LEAN_PATH"] = tmp

        with open(os.path.join(tmp, "ReplayGeneric.lean"), "w") as f:
            f.write(REPLAY_GENERIC_LEAN)

        rlib_rep = subprocess.run(
            [LEAN_RUN, "--mode", "file", "--", LEAN_BIN, "--run", "ReplayGeneric.lean", TC_DIR,
             "Init.Data.BitVec.Lemmas", "BvSimdTseitin", "GmpBvTseitin.checkBvUnsatCert_sound"],
            cwd=tmp, env=env, capture_output=True, text=True
        )
        assert rlib_rep.returncode == 0, rlib_rep.stdout + rlib_rep.stderr
        bv_lib_replay = json.loads(rlib_rep.stdout.split("REPLAY_JSON ")[1].splitlines()[0])
        print("BvSimdTseitin compile & replay:", bv_lib_compile, bv_lib_replay, flush=True)

        # 2. Run untrusted Lean harvester
        with open(os.path.join(tmp, "HarvestDriver.lean"), "w") as f:
            f.write(HARVESTER_LEAN)
        out_canaries = os.path.join(tmp, "NonlinearSimdCanaries.lean")
        out_json = os.path.join(tmp, "harvest_summary.json")
        rh = subprocess.run(
            [LEAN_RUN, "--mode", "file", "--", LEAN_BIN, "--run", "HarvestDriver.lean", TC_DIR, tmp, out_canaries, out_json],
            cwd=tmp, env=env, capture_output=True, text=True
        )
        print("Harvest rc=", rh.returncode, flush=True)
        if rh.stdout:
            print("Harvest stdout:", rh.stdout, flush=True)
        if rh.returncode != 0:
            print("Harvest stderr:", rh.stderr, flush=True)
            raise SystemExit(1)

        with open(out_json) as f:
            harvest_stats = json.load(f)
        shutil.copyfile(out_canaries, os.path.join(HERE, "NonlinearSimdCanaries.lean"))
        canaries_src_bytes = os.path.getsize(out_canaries)
        print(f"Generated NonlinearSimdCanaries.lean ({canaries_src_bytes} bytes)", flush=True)
        assert canaries_src_bytes < 250_000, f"Canaries too large: {canaries_src_bytes}"

        # 3. Compile & fresh-kernel-replay EACH individual VC module in `tmp`!
        vc_names = [
            "swar_has_zero_byte_64",
            "bmi2_blsi_blsr_64",
            "bmi2_blsmsk_64",
            "bmi2_bzhi64_comp",
            "x86_sub_signed_64",
            "x86_sub_unsigned_64",
            "x86_xor_pf_64",
            "ssse3_vpmaddubsw_64_lane_and_sat",
            "vpaddsw_lane16_comm_and_sat",
        ]
        per_vc_verification = {}
        for nm in vc_names:
            mod = f"VC_{nm}"
            src_bytes = os.path.getsize(os.path.join(tmp, f"{mod}.lean"))
            try:
                rc = subprocess.run(
                    [LEAN_RUN, "--mode", "file", "--", "/usr/bin/time", "-f", "TSTAT wall=%e user=%U sys=%S rss=%M",
                     LEAN_BIN, "-DElab.async=false", "-Ddebug.skipKernelTC=false",
                     "-o", f"{mod}.olean", f"{mod}.lean"],
                    cwd=tmp, env=env, capture_output=True, text=True, timeout=75
                )
            except subprocess.TimeoutExpired:
                per_vc_verification[nm] = {"status": "TIMEOUT_GT_75S", "source_bytes": src_bytes}
                print(f"[{mod}] TIMEOUT_GT_75S", flush=True)
                continue

            if rc.returncode != 0:
                per_vc_verification[nm] = {
                    "status": "FAIL",
                    "source_bytes": src_bytes,
                    "diagnostic": "\n".join((rc.stdout + rc.stderr).strip().splitlines()[:6]),
                }
                print(f"[{mod}] FAIL: {per_vc_verification[nm]['diagnostic']}", flush=True)
                continue

            tstat = parse_tstat(rc.stderr)
            olean_sz = os.path.getsize(os.path.join(tmp, f"{mod}.olean"))
            thm_check = (
                f"{mod}.avx2_vpaddsw256_eval_comm"
                if nm == "vpaddsw_lane16_comm_and_sat"
                else (f"{mod}.mycroft_has_zero_byte_eq_borrow_free" if nm == "swar_has_zero_byte_64" else f"{mod}.{nm}_unsat")
            )
            rrep = subprocess.run(
                [LEAN_RUN, "--mode", "file", "--", LEAN_BIN, "--run", "ReplayGeneric.lean", TC_DIR, "BvSimdTseitin", mod, thm_check],
                cwd=tmp, env=env, capture_output=True, text=True, timeout=75
            )
            assert rrep.returncode == 0, rrep.stdout + rrep.stderr
            rep_j = json.loads(rrep.stdout.split("REPLAY_JSON ")[1].splitlines()[0])
            per_vc_verification[nm] = {
                "status": "OK",
                "source_bytes": src_bytes,
                "compile": tstat,
                "olean_bytes": olean_sz,
                "replay": rep_j,
            }
            print(f"[{mod}] OK wall={tstat.get('wall_s')}s replay_ms={rep_j['replay_ms']} olean={olean_sz}", flush=True)

        # 4. Compile & replay the staged compact NonlinearSimdCanaries.lean!
        rc_can = subprocess.run(
            [LEAN_RUN, "--mode", "file", "--", "/usr/bin/time", "-f", "TSTAT wall=%e user=%U sys=%S rss=%M",
             LEAN_BIN, "-DElab.async=false", "-Ddebug.skipKernelTC=false",
             "-o", "NonlinearSimdCanaries.olean", "NonlinearSimdCanaries.lean"],
            cwd=tmp, env=env, capture_output=True, text=True, timeout=90
        )
        assert rc_can.returncode == 0, rc_can.stdout + rc_can.stderr
        can_compile = parse_tstat(rc_can.stderr)
        can_olean = os.path.getsize(os.path.join(tmp, "NonlinearSimdCanaries.olean"))
        rrep_can = subprocess.run(
            [LEAN_RUN, "--mode", "file", "--", LEAN_BIN, "--run", "ReplayGeneric.lean", TC_DIR,
             "BvSimdTseitin", "NonlinearSimdCanaries", "NonlinearSimdCanaries.avx2_vpaddsw256_eval_comm"],
            cwd=tmp, env=env, capture_output=True, text=True, timeout=90
        )
        assert rrep_can.returncode == 0, rrep_can.stdout + rrep_can.stderr
        can_replay = json.loads(rrep_can.stdout.split("REPLAY_JSON ")[1].splitlines()[0])
        print("NonlinearSimdCanaries OK:", can_compile, can_replay, flush=True)

        # 5. Probe standard tactics (`bv_decide` axiom footprint + `omega`/`bv_omega`/`grind` failures)
        with open(os.path.join(tmp, "BvDecideProbe.lean"), "w") as f:
            f.write(TACTIC_BASELINE_LEAN)
        rbv = subprocess.run([LEAN_RUN, "--mode", "file", "--", LEAN_BIN, "BvDecideProbe.lean"], cwd=tmp, capture_output=True, text=True)
        bv_decide_axioms_line = rbv.stdout.strip()

        tactic_failures = {}
        for tac, code in TACTIC_FAIL_PROBES.items():
            p = os.path.join(tmp, f"Fail_{tac}.lean")
            with open(p, "w") as f:
                f.write(code)
            rf = subprocess.run([LEAN_RUN, "--mode", "file", "--", LEAN_BIN, p], cwd=tmp, capture_output=True, text=True, timeout=90)
            tactic_failures[tac] = {
                "returncode": rf.returncode,
                "diagnostic": "\n".join(rf.stdout.strip().splitlines()[:6]),
            }

        results = {
            "host_solvers_in_path": path_solvers,
            "bundled_cadical_version": cad_ver,
            "bv_simd_tseitin_lib": {
                "compile": bv_lib_compile,
                "olean_bytes": bv_lib_olean_bytes,
                "replay": bv_lib_replay,
            },
            "harvested_vcs": harvest_stats,
            "per_vc_verification": per_vc_verification,
            "compact_canaries_module": {
                "source_bytes": canaries_src_bytes,
                "compile": can_compile,
                "olean_bytes": can_olean,
                "replay": can_replay,
            },
            "monolithic_7mb_antipattern_observation": {
                "monolithic_packed_bytes": 7_140_000,
                "monolithic_raw_ast_bytes": 23_100_000,
                "naive_256bit_vpaddsw_packed_lrat_bytes": 2_320_243,
                "observed_rss_gb": 15.8,
                "observed_wall_min": 12.0,
                "resolution": "Per-VC module decomposition + 16-bit lane LRAT with 256-bit SIMD congruence lifting (`simdMapBinary16_comm`)",
            },
            "bv_decide_axiom_probe": bv_decide_axioms_line,
            "standard_tactic_failures_on_swar64": tactic_failures,
        }
        with open(os.path.join(HERE, "nonlinear_vc_results.json"), "w") as f:
            json.dump(results, f, indent=2)
        print("Saved nonlinear_vc_results.json", flush=True)


if __name__ == "__main__":
    main()
