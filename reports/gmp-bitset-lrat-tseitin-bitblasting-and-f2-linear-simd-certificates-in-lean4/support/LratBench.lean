prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Init.Data.Array.Basic
import Init.Data.Array.Set
import Init.Tactics

namespace LratBench

inductive LratStep where
  | addRup (id : Nat) (clause : List Nat) (hints : List Nat)
  | del (ids : List Nat)
  | addEmpty (hints : List Nat)

inductive StepTree (α : Type) where
  | empty
  | leaf (val : α)
  | branch (left right : StepTree α)

-- ============================================================================
-- 1. Tuple-Free Strict Radix-2 Trie & Radix-4 QuadTrie (NO Nat.casesOn overhead!)
-- ============================================================================

inductive Trie (α : Type) where
  | empty
  | node (val : Option α) (ev od : Trie α)

def Trie.get {α : Type} : Nat → Trie α → Nat → Option α
  | 0, _, _ => none
  | Nat.succ _, .empty, _ => none
  | Nat.succ _, .node v _ _, 0 => v
  | Nat.succ fuel, .node _ ev od, idx =>
    match Nat.beq (Nat.land idx 1) 0 with
    | true  => Trie.get fuel ev (Nat.shiftRight idx 1)
    | false => Trie.get fuel od (Nat.shiftRight idx 1)

def Trie.set {α : Type} : Nat → Trie α → Nat → Option α → Trie α
  | 0, cur, _, _ => cur
  | Nat.succ _, .empty, 0, v => .node v .empty .empty
  | Nat.succ _, .node _ ev od, 0, v => .node v ev od
  | Nat.succ fuel, .empty, idx, v =>
    match Nat.beq (Nat.land idx 1) 0 with
    | true =>
      match Trie.set fuel .empty (Nat.shiftRight idx 1) v with
      | .empty => .node none .empty .empty
      | .node cv cev cod => .node none (.node cv cev cod) .empty
    | false =>
      match Trie.set fuel .empty (Nat.shiftRight idx 1) v with
      | .empty => .node none .empty .empty
      | .node cv cev cod => .node none .empty (.node cv cev cod)
  | Nat.succ fuel, .node v0 ev0 od0, idx, v =>
    match Nat.beq (Nat.land idx 1) 0 with
    | true =>
      match Trie.set fuel ev0 (Nat.shiftRight idx 1) v with
      | .empty => .node v0 .empty od0
      | .node cv cev cod => .node v0 (.node cv cev cod) od0
    | false =>
      match Trie.set fuel od0 (Nat.shiftRight idx 1) v with
      | .empty => .node v0 ev0 .empty
      | .node cv cev cod => .node v0 ev0 (.node cv cev cod)

inductive QuadTrie (α : Type) where
  | empty
  | node (val : Option α) (c0 c1 c2 c3 : QuadTrie α)

def QuadTrie.get {α : Type} : Nat → QuadTrie α → Nat → Option α
  | 0, _, _ => none
  | Nat.succ _, .empty, _ => none
  | Nat.succ _, .node v _ _ _ _, 0 => v
  | Nat.succ fuel, .node _ c0 c1 c2 c3, idx =>
    let rem := Nat.land idx 3
    let nxt := Nat.shiftRight idx 2
    match Nat.beq rem 0 with
    | true => QuadTrie.get fuel c0 nxt
    | false =>
      match Nat.beq rem 1 with
      | true => QuadTrie.get fuel c1 nxt
      | false =>
        match Nat.beq rem 2 with
        | true => QuadTrie.get fuel c2 nxt
        | false => QuadTrie.get fuel c3 nxt

def QuadTrie.set {α : Type} : Nat → QuadTrie α → Nat → Option α → QuadTrie α
  | 0, cur, _, _ => cur
  | Nat.succ _, .empty, 0, v => .node v .empty .empty .empty .empty
  | Nat.succ _, .node _ c0 c1 c2 c3, 0, v => .node v c0 c1 c2 c3
  | Nat.succ fuel, .empty, idx, v =>
    let rem := Nat.land idx 3
    let nxt := Nat.shiftRight idx 2
    match Nat.beq rem 0 with
    | true =>
      match QuadTrie.set fuel .empty nxt v with
      | .empty => .node none .empty .empty .empty .empty
      | .node u b0 b1 b2 b3 => .node none (.node u b0 b1 b2 b3) .empty .empty .empty
    | false =>
      match Nat.beq rem 1 with
      | true =>
        match QuadTrie.set fuel .empty nxt v with
        | .empty => .node none .empty .empty .empty .empty
        | .node u b0 b1 b2 b3 => .node none .empty (.node u b0 b1 b2 b3) .empty .empty
      | false =>
        match Nat.beq rem 2 with
        | true =>
          match QuadTrie.set fuel .empty nxt v with
          | .empty => .node none .empty .empty .empty .empty
          | .node u b0 b1 b2 b3 => .node none .empty .empty (.node u b0 b1 b2 b3) .empty
        | false =>
          match QuadTrie.set fuel .empty nxt v with
          | .empty => .node none .empty .empty .empty .empty
          | .node u b0 b1 b2 b3 => .node none .empty .empty .empty (.node u b0 b1 b2 b3)
  | Nat.succ fuel, .node v0 c0 c1 c2 c3, idx, v =>
    let rem := Nat.land idx 3
    let nxt := Nat.shiftRight idx 2
    match Nat.beq rem 0 with
    | true =>
      match QuadTrie.set fuel c0 nxt v with
      | .empty => .node v0 .empty c1 c2 c3
      | .node u b0 b1 b2 b3 => .node v0 (.node u b0 b1 b2 b3) c1 c2 c3
    | false =>
      match Nat.beq rem 1 with
      | true =>
        match QuadTrie.set fuel c1 nxt v with
        | .empty => .node v0 c0 .empty c2 c3
        | .node u b0 b1 b2 b3 => .node v0 c0 (.node u b0 b1 b2 b3) c2 c3
      | false =>
        match Nat.beq rem 2 with
        | true =>
          match QuadTrie.set fuel c2 nxt v with
          | .empty => .node v0 c0 c1 .empty c3
          | .node u b0 b1 b2 b3 => .node v0 c0 c1 (.node u b0 b1 b2 b3) c3
        | false =>
          match QuadTrie.set fuel c3 nxt v with
          | .empty => .node v0 c0 c1 c2 .empty
          | .node u b0 b1 b2 b3 => .node v0 c0 c1 c2 (.node u b0 b1 b2 b3)

-- ============================================================================
-- 2. GMP Word-Parallel Bitset RUP / LRAT Checker
-- ============================================================================

def compileClauseMask : List Nat → Nat
  | [] => 0
  | lit :: rest => Nat.lor (Nat.shiftLeft 1 lit) (compileClauseMask rest)

def propagateGmpHints (qDepth : Nat) (clauses : QuadTrie Nat) (falsified : Nat) : List Nat → Bool
  | [] => false
  | cid :: rest =>
    match QuadTrie.get qDepth clauses cid with
    | none => false
    | some mask =>
      let rem := Nat.xor mask (Nat.land mask falsified)
      match Nat.beq rem 0 with
      | true => true
      | false =>
        match Nat.beq (Nat.land rem (Nat.sub rem 1)) 0 with
        | false => false
        | true =>
          let negRaw := match Nat.beq (Nat.mod rem 3) 1 with
            | true  => Nat.shiftLeft rem 1
            | false => Nat.shiftRight rem 1
          let falsified' := Nat.lor falsified negRaw
          -- Force `falsified'` in C++ `reduce_nat` via `Nat.beq` (does NOT build `Nat.succ`!)
          match Nat.beq falsified' 0 with
          | true  => propagateGmpHints qDepth clauses 0 rest
          | false => propagateGmpHints qDepth clauses falsified' rest

inductive GmpRunState where
  | running (db : QuadTrie Nat)
  | proved
  | failed

def deleteGmpIds (qDepth : Nat) : QuadTrie Nat → List Nat → QuadTrie Nat
  | db, [] => db
  | db, cid :: rest =>
    match QuadTrie.set qDepth db cid none with
    | .empty => deleteGmpIds qDepth .empty rest
    | .node v c0 c1 c2 c3 => deleteGmpIds qDepth (.node v c0 c1 c2 c3) rest

def stepGmp (qDepth : Nat) (st : GmpRunState) (s : LratStep) : GmpRunState :=
  match st with
  | .proved => .proved
  | .failed => .failed
  | .running db =>
    match s with
    | .addRup cid cls hints =>
      let targetMask := compileClauseMask cls
      match propagateGmpHints qDepth db targetMask hints with
      | false => .failed
      | true =>
        match Nat.beq targetMask 0 with
        | true => .proved
        | false =>
          match QuadTrie.set qDepth db cid (some targetMask) with
          | .empty => .running .empty
          | .node v c0 c1 c2 c3 => .running (.node v c0 c1 c2 c3)
    | .del ids => .running (deleteGmpIds qDepth db ids)
    | .addEmpty hints =>
      match propagateGmpHints qDepth db 0 hints with
      | true  => .proved
      | false => .failed

def runGmpTree (qDepth : Nat) : Nat → GmpRunState → StepTree LratStep → GmpRunState
  | 0, _, _ => .failed
  | Nat.succ _, st, .empty => st
  | Nat.succ _, st, .leaf s => stepGmp qDepth st s
  | Nat.succ fuel, st, .branch l r =>
    match runGmpTree qDepth fuel st l with
    | .proved => .proved
    | .failed => .failed
    | .running db => runGmpTree qDepth fuel (.running db) r

def initGmpTree (qDepth : Nat) : Nat → QuadTrie Nat → StepTree (Nat × List Nat) → QuadTrie Nat
  | 0, db, _ => db
  | Nat.succ _, db, .empty => db
  | Nat.succ _, db, .leaf (cid, cls) =>
    let m := compileClauseMask cls
    match Nat.beq m 0 with
    | true => QuadTrie.set qDepth db cid (some 0)
    | false => QuadTrie.set qDepth db cid (some m)
  | Nat.succ fuel, db, .branch l r =>
    match initGmpTree qDepth fuel db l with
    | .empty => initGmpTree qDepth fuel .empty r
    | .node v c0 c1 c2 c3 => initGmpTree qDepth fuel (.node v c0 c1 c2 c3) r

def checkLratGmp (qDepth treeFuel : Nat) (initClauses : StepTree (Nat × List Nat))
    (steps : StepTree LratStep) : Bool :=
  let db0 := initGmpTree qDepth treeFuel .empty initClauses
  match runGmpTree qDepth treeFuel (.running db0) steps with
  | .proved => true
  | _ => false

-- ============================================================================
-- 2b. Zero-Allocation Direct GMP Stream + GMP Bitset Checker
-- ============================================================================

inductive MaskStream where
  | mk (mask : Nat) (rest : Nat)

def readMaskStream : Nat → Nat → Nat → MaskStream
  | 0, s, acc => .mk acc s
  | Nat.succ k, s, acc =>
    let lit := Nat.land s 0xffffffff
    let s' := Nat.shiftRight s 32
    let acc' := Nat.lor acc (Nat.shiftLeft 1 lit)
    match Nat.beq acc' 0, Nat.beq s' 0 with
    | true, true => readMaskStream k 0 0
    | true, false => readMaskStream k s' 0
    | false, true => readMaskStream k 0 acc'
    | false, false => readMaskStream k s' acc'

inductive PropStreamRes where
  | mk (ok : Bool) (rest : Nat)

def skipWords (k : Nat) (s : Nat) : Nat :=
  Nat.shiftRight s (Nat.mul 32 k)

def propGmpStream (qDepth : Nat) (clauses : QuadTrie Nat) : Nat → Nat → Nat → PropStreamRes
  | 0, _, s => .mk false s
  | Nat.succ k, falsified, s =>
    let cid := Nat.land s 0xffffffff
    let s' := Nat.shiftRight s 32
    match QuadTrie.get qDepth clauses cid with
    | none => .mk false (skipWords k s')
    | some mask =>
      let rem := Nat.xor mask (Nat.land mask falsified)
      match Nat.beq rem 0 with
      | true => .mk true (skipWords k s')
      | false =>
        match Nat.beq (Nat.land rem (Nat.sub rem 1)) 0 with
        | false => .mk false (skipWords k s')
        | true =>
          let negRaw := match Nat.beq (Nat.mod rem 3) 1 with
            | true  => Nat.shiftLeft rem 1
            | false => Nat.shiftRight rem 1
          let falsified' := Nat.lor falsified negRaw
          match Nat.beq falsified' 0 with
          | true => propGmpStream qDepth clauses k 0 s'
          | false => propGmpStream qDepth clauses k falsified' s'

inductive DelStreamRes where
  | mk (db : QuadTrie Nat) (rest : Nat)

def delGmpStream (qDepth : Nat) : Nat → QuadTrie Nat → Nat → DelStreamRes
  | 0, db, s => .mk db s
  | Nat.succ k, db, s =>
    let cid := Nat.land s 0xffffffff
    let s' := Nat.shiftRight s 32
    match QuadTrie.set qDepth db cid none with
    | .empty => delGmpStream qDepth k .empty s'
    | .node v c0 c1 c2 c3 => delGmpStream qDepth k (.node v c0 c1 c2 c3) s'

def runGmpChunkDirect (qDepth : Nat) : Nat → GmpRunState → Nat → GmpRunState
  | 0, st, _ => st
  | Nat.succ fuel, st, s =>
    match st with
    | .proved => .proved
    | .failed => .failed
    | .running db =>
      let tag := Nat.land s 0xffffffff
      let s1 := Nat.shiftRight s 32
      match Nat.beq tag 0 with
      | true => .running db
      | false =>
        match Nat.beq tag 1 with
        | true =>
          let cid := Nat.land s1 0xffffffff
          let cLen := Nat.land (Nat.shiftRight s1 32) 0xffffffff
          let hLen := Nat.land (Nat.shiftRight s1 64) 0xffffffff
          let s4 := Nat.shiftRight s1 96
          match readMaskStream cLen s4 0 with
          | .mk targetMask s5 =>
            match propGmpStream qDepth db hLen targetMask s5 with
            | .mk false _ => .failed
            | .mk true s6 =>
              match Nat.beq targetMask 0 with
              | true => .proved
              | false =>
                match QuadTrie.set qDepth db cid (some targetMask) with
                | .empty => runGmpChunkDirect qDepth fuel (.running .empty) s6
                | .node v c0 c1 c2 c3 => runGmpChunkDirect qDepth fuel (.running (.node v c0 c1 c2 c3)) s6
        | false =>
          match Nat.beq tag 2 with
          | true =>
            let dLen := Nat.land s1 0xffffffff
            let s2 := Nat.shiftRight s1 32
            match delGmpStream qDepth dLen db s2 with
            | .mk db' s3 => runGmpChunkDirect qDepth fuel (.running db') s3
          | false =>
            let hLen := Nat.land s1 0xffffffff
            let s2 := Nat.shiftRight s1 32
            match propGmpStream qDepth db hLen 0 s2 with
            | .mk true _ => .proved
            | .mk false _ => .failed

def initGmpChunkDirect (qDepth : Nat) : Nat → QuadTrie Nat → Nat → QuadTrie Nat
  | 0, db, _ => db
  | Nat.succ fuel, db, s =>
    let cid := Nat.land s 0xffffffff
    let s1 := Nat.shiftRight s 32
    match Nat.beq cid 0 with
    | true => db
    | false =>
      let cLen := Nat.land s1 0xffffffff
      let s2 := Nat.shiftRight s1 32
      match readMaskStream cLen s2 0 with
      | .mk m s3 =>
        match QuadTrie.set qDepth db cid (some m) with
        | .empty => initGmpChunkDirect qDepth fuel .empty s3
        | .node v c0 c1 c2 c3 => initGmpChunkDirect qDepth fuel (.node v c0 c1 c2 c3) s3

def initGmpStreamTree (qDepth : Nat) : Nat → QuadTrie Nat → StepTree Nat → QuadTrie Nat
  | 0, db, _ => db
  | Nat.succ _, db, .empty => db
  | Nat.succ _, db, .leaf s => initGmpChunkDirect qDepth 40 db s
  | Nat.succ fuel, db, .branch l r =>
    match initGmpStreamTree qDepth fuel db l with
    | .empty => initGmpStreamTree qDepth fuel .empty r
    | .node v c0 c1 c2 c3 => initGmpStreamTree qDepth fuel (.node v c0 c1 c2 c3) r

def runGmpStreamTree (qDepth : Nat) : Nat → GmpRunState → StepTree Nat → GmpRunState
  | 0, _, _ => .failed
  | Nat.succ _, st, .empty => st
  | Nat.succ _, st, .leaf s => runGmpChunkDirect qDepth 40 st s
  | Nat.succ fuel, st, .branch l r =>
    match runGmpStreamTree qDepth fuel st l with
    | .proved => .proved
    | .failed => .failed
    | .running db => runGmpStreamTree qDepth fuel (.running db) r

def checkLratGmpStream (qDepth treeFuel : Nat) (initTree stepsTree : StepTree Nat) : Bool :=
  let db0 := initGmpStreamTree qDepth treeFuel .empty initTree
  match runGmpStreamTree qDepth treeFuel (.running db0) stepsTree with
  | .proved => true
  | _ => false

-- ============================================================================
-- 3. Stream Decoder + Strict Trie / List / Array Checkers
-- ============================================================================

inductive NatListStream where
  | mk (items : List Nat) (restStream : Nat)

def readNatListRev : Nat → Nat → List Nat → NatListStream
  | 0, s, acc => .mk acc.reverse s
  | Nat.succ k, s, acc =>
    let x := Nat.land s 0xffffffff
    let s' := Nat.shiftRight s 32
    readNatListRev k s' (x :: acc)

def decodeStepsChunkRev : Nat → Nat → List LratStep → List LratStep
  | 0, _, acc => acc.reverse
  | Nat.succ fuel, s, acc =>
    let tag := Nat.land s 0xffffffff
    let s1 := Nat.shiftRight s 32
    match Nat.beq tag 0 with
    | true => acc.reverse
    | false =>
      match Nat.beq tag 1 with
      | true =>
        let cid := Nat.land s1 0xffffffff
        let cLen := Nat.land (Nat.shiftRight s1 32) 0xffffffff
        let hLen := Nat.land (Nat.shiftRight s1 64) 0xffffffff
        let s4 := Nat.shiftRight s1 96
        match readNatListRev cLen s4 [] with
        | .mk cls s5 =>
          match readNatListRev hLen s5 [] with
          | .mk hints s6 =>
            decodeStepsChunkRev fuel s6 ((.addRup cid cls hints) :: acc)
      | false =>
        match Nat.beq tag 2 with
        | true =>
          let dLen := Nat.land s1 0xffffffff
          let s2 := Nat.shiftRight s1 32
          match readNatListRev dLen s2 [] with
          | .mk ids s3 => decodeStepsChunkRev fuel s3 ((.del ids) :: acc)
        | false =>
          let hLen := Nat.land s1 0xffffffff
          let s2 := Nat.shiftRight s1 32
          match readNatListRev hLen s2 [] with
          | .mk hints s3 => decodeStepsChunkRev fuel s3 ((.addEmpty hints) :: acc)

def listToStepTreeAux {α : Type} : Nat → List (StepTree α) → List (StepTree α)
  | 0, xs => xs
  | Nat.succ _, [] => []
  | Nat.succ _, [x] => [x]
  | Nat.succ fuel, x :: y :: rest =>
    (.branch x y) :: listToStepTreeAux fuel rest

def listToStepTreeLoop {α : Type} : Nat → Nat → List (StepTree α) → StepTree α
  | _, _, [] => .empty
  | _, _, [t] => t
  | 0, _, t :: _ => t
  | Nat.succ outer, pairFuel, ts =>
    listToStepTreeLoop outer pairFuel (listToStepTreeAux pairFuel ts)

def mapStepLeaves : List LratStep → List (StepTree LratStep)
  | [] => []
  | x :: xs => (.leaf x) :: mapStepLeaves xs

def mapInitLeaves : List (Nat × List Nat) → List (StepTree (Nat × List Nat))
  | [] => []
  | x :: xs => (.leaf x) :: mapInitLeaves xs

def decodeStepChunkToTree (stepFuel : Nat) (s : Nat) : StepTree LratStep :=
  let steps := decodeStepsChunkRev stepFuel s []
  listToStepTreeLoop 8 64 (mapStepLeaves steps)

def decodePackedTree : Nat → StepTree Nat → StepTree LratStep
  | 0, _ => .empty
  | Nat.succ _, .empty => .empty
  | Nat.succ _, .leaf chunkNat => decodeStepChunkToTree 40 chunkNat
  | Nat.succ fuel, .branch l r =>
    .branch (decodePackedTree fuel l) (decodePackedTree fuel r)

def decodeInitChunkRev : Nat → Nat → List (Nat × List Nat) → List (Nat × List Nat)
  | 0, _, acc => acc.reverse
  | Nat.succ fuel, s, acc =>
    let cid := Nat.land s 0xffffffff
    let s1 := Nat.shiftRight s 32
    match Nat.beq cid 0 with
    | true => acc.reverse
    | false =>
      let cLen := Nat.land s1 0xffffffff
      let s2 := Nat.shiftRight s1 32
      match readNatListRev cLen s2 [] with
      | .mk cls s3 =>
        decodeInitChunkRev fuel s3 ((cid, cls) :: acc)

def decodePackedInit : Nat → StepTree Nat → StepTree (Nat × List Nat)
  | 0, _ => .empty
  | Nat.succ _, .empty => .empty
  | Nat.succ _, .leaf chunkNat =>
    let items := decodeInitChunkRev 40 chunkNat []
    listToStepTreeLoop 8 64 (mapInitLeaves items)
  | Nat.succ fuel, .branch l r =>
    .branch (decodePackedInit fuel l) (decodePackedInit fuel r)

inductive ClauseEvalRes where
  | mk (sat : Bool) (unitLit : Option Nat) (unassignedCount : Nat)

def evalClauseTrie (tDepth : Nat) (assign : Trie Bool) : List Nat → ClauseEvalRes
  | [] => .mk false none 0
  | lit :: rest =>
    match evalClauseTrie tDepth assign rest with
    | .mk true u n => .mk true u n
    | .mk false u n =>
      let varId := Nat.shiftRight lit 1
      let wantPos := Nat.beq (Nat.land lit 1) 0
      match Trie.get tDepth assign varId with
      | some val =>
        match val, wantPos with
        | true, true => .mk true none 0
        | false, false => .mk true none 0
        | _, _ => .mk false u n
      | none => .mk false (some lit) (Nat.succ n)

inductive InitAssignRes where
  | taut
  | ok (a : Trie Bool)

def initAssignTrie (tDepth : Nat) : List Nat → InitAssignRes
  | [] => .ok .empty
  | lit :: rest =>
    match initAssignTrie tDepth rest with
    | .taut => .taut
    | .ok a =>
      let varId := Nat.shiftRight lit 1
      let negVal := !Nat.beq (Nat.land lit 1) 0
      match Trie.get tDepth a varId with
      | some old =>
        match old, negVal with
        | true, false => .taut
        | false, true => .taut
        | _, _ => .ok a
      | none =>
        match Trie.set tDepth a varId (some negVal) with
        | .empty => .ok .empty
        | .node v ev od => .ok (.node v ev od)

def propTrieHints (tDepth : Nat) (clauses : Trie (List Nat)) (assign : Trie Bool) : List Nat → Bool
  | [] => false
  | cid :: rest =>
    match Trie.get tDepth clauses cid with
    | none => false
    | some cls =>
      match evalClauseTrie tDepth assign cls with
      | .mk true _ _ => false
      | .mk false _ 0 => true
      | .mk false (some uLit) 1 =>
        let varId := Nat.shiftRight uLit 1
        let wantPos := Nat.beq (Nat.land uLit 1) 0
        match Trie.set tDepth assign varId (some wantPos) with
        | .empty => propTrieHints tDepth clauses .empty rest
        | .node v ev od => propTrieHints tDepth clauses (.node v ev od) rest
      | .mk false _ _ => false

inductive TrieRunState where
  | running (db : Trie (List Nat))
  | proved
  | failed

def deleteTrieIds (tDepth : Nat) : Trie (List Nat) → List Nat → Trie (List Nat)
  | db, [] => db
  | db, cid :: rest =>
    match Trie.set tDepth db cid none with
    | .empty => deleteTrieIds tDepth .empty rest
    | .node v ev od => deleteTrieIds tDepth (.node v ev od) rest

def stepTrie (tDepth : Nat) (st : TrieRunState) (s : LratStep) : TrieRunState :=
  match st with
  | .proved => .proved
  | .failed => .failed
  | .running db =>
    match s with
    | .addRup cid cls hints =>
      let ok := match initAssignTrie tDepth cls with
        | .taut => true
        | .ok a0 => propTrieHints tDepth db a0 hints
      match ok with
      | false => .failed
      | true =>
        match Trie.set tDepth db cid (some cls) with
        | .empty => .running .empty
        | .node v ev od => .running (.node v ev od)
    | .del ids => .running (deleteTrieIds tDepth db ids)
    | .addEmpty hints =>
      match propTrieHints tDepth db .empty hints with
      | true  => .proved
      | false => .failed

def runTrieTree (tDepth : Nat) : Nat → TrieRunState → StepTree LratStep → TrieRunState
  | 0, _, _ => .failed
  | Nat.succ _, st, .empty => st
  | Nat.succ _, st, .leaf s => stepTrie tDepth st s
  | Nat.succ fuel, st, .branch l r =>
    match runTrieTree tDepth fuel st l with
    | .proved => .proved
    | .failed => .failed
    | .running db => runTrieTree tDepth fuel (.running db) r

def initTrieDb (tDepth : Nat) : Nat → Trie (List Nat) → StepTree (Nat × List Nat) → Trie (List Nat)
  | 0, db, _ => db
  | Nat.succ _, db, .empty => db
  | Nat.succ _, db, .leaf (cid, cls) => Trie.set tDepth db cid (some cls)
  | Nat.succ fuel, db, .branch l r =>
    match initTrieDb tDepth fuel db l with
    | .empty => initTrieDb tDepth fuel .empty r
    | .node v ev od => initTrieDb tDepth fuel (.node v ev od) r

def checkLratTrie (tDepth treeFuel : Nat) (initClauses : StepTree (Nat × List Nat))
    (steps : StepTree LratStep) : Bool :=
  let db0 := initTrieDb tDepth treeFuel .empty initClauses
  match runTrieTree tDepth treeFuel (.running db0) steps with
  | .proved => true
  | _ => false

def assocGet {α : Type} : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (k, v) :: rest, target =>
    match Nat.beq k target with
    | true => some v
    | false => assocGet rest target

def assocDel {α : Type} : List (Nat × α) → Nat → List (Nat × α)
  | [], _ => []
  | (k, v) :: rest, target =>
    match Nat.beq k target with
    | true => assocDel rest target
    | false => (k, v) :: assocDel rest target

def evalClauseList (assign : List (Nat × Bool)) : List Nat → ClauseEvalRes
  | [] => .mk false none 0
  | lit :: rest =>
    match evalClauseList assign rest with
    | .mk true u n => .mk true u n
    | .mk false u n =>
      let varId := Nat.shiftRight lit 1
      let wantPos := Nat.beq (Nat.land lit 1) 0
      match assocGet assign varId with
      | some val =>
        match val, wantPos with
        | true, true => .mk true none 0
        | false, false => .mk true none 0
        | _, _ => .mk false u n
      | none => .mk false (some lit) (Nat.succ n)

def propListHints (clauses : List (Nat × List Nat)) (assign : List (Nat × Bool)) : List Nat → Bool
  | [] => false
  | cid :: rest =>
    match assocGet clauses cid with
    | none => false
    | some cls =>
      match evalClauseList assign cls with
      | .mk true _ _ => false
      | .mk false _ 0 => true
      | .mk false (some uLit) 1 =>
        let varId := Nat.shiftRight uLit 1
        let wantPos := Nat.beq (Nat.land uLit 1) 0
        propListHints clauses ((varId, wantPos) :: assign) rest
      | .mk false _ _ => false

inductive ListRunState where
  | running (db : List (Nat × List Nat))
  | proved
  | failed

def stepList (st : ListRunState) (s : LratStep) : ListRunState :=
  match st with
  | .proved => .proved
  | .failed => .failed
  | .running db =>
    match s with
    | .addRup cid cls hints =>
      let a0 := cls.map (fun lit => (Nat.shiftRight lit 1, !Nat.beq (Nat.land lit 1) 0))
      match propListHints db a0 hints with
      | false => .failed
      | true => .running ((cid, cls) :: db)
    | .del ids => .running (ids.foldr (fun cid cur => assocDel cur cid) db)
    | .addEmpty hints =>
      match propListHints db [] hints with
      | true => .proved
      | false => .failed

def runListTree : Nat → ListRunState → StepTree LratStep → ListRunState
  | 0, _, _ => .failed
  | Nat.succ _, st, .empty => st
  | Nat.succ _, st, .leaf s => stepList st s
  | Nat.succ fuel, st, .branch l r =>
    match runListTree fuel st l with
    | .proved => .proved
    | .failed => .failed
    | .running db => runListTree fuel (.running db) r

def initListDb : Nat → List (Nat × List Nat) → StepTree (Nat × List Nat) → List (Nat × List Nat)
  | 0, db, _ => db
  | Nat.succ _, db, .empty => db
  | Nat.succ _, db, .leaf e => e :: db
  | Nat.succ fuel, db, .branch l r => initListDb fuel (initListDb fuel db l) r

def checkLratList (treeFuel : Nat) (initClauses : StepTree (Nat × List Nat))
    (steps : StepTree LratStep) : Bool :=
  let db0 := initListDb treeFuel [] initClauses
  match runListTree treeFuel (.running db0) steps with
  | .proved => true
  | _ => false

def mkNoneArray (α : Type) : Nat → List (Option α) → Array (Option α)
  | 0, acc => Array.mk acc
  | Nat.succ n, acc => mkNoneArray α n (none :: acc)

def mkZeroArray : Nat → List Nat → Array Nat
  | 0, acc => Array.mk acc
  | Nat.succ n, acc => mkZeroArray n (0 :: acc)

def arrayGetOpt {α : Type} (arr : Array (Option α)) (idx : Nat) : Option α :=
  if h : idx < arr.size then arr[idx] else none

def arraySetOpt {α : Type} (arr : Array (Option α)) (idx : Nat) (v : Option α) : Array (Option α) :=
  if h : idx < arr.size then arr.set idx v h else arr

def arrayGetNat (arr : Array Nat) (idx : Nat) : Nat :=
  if h : idx < arr.size then arr[idx] else 0

def arraySetNat (arr : Array Nat) (idx : Nat) (v : Nat) : Array Nat :=
  if h : idx < arr.size then arr.set idx v h else arr

def evalClauseArray (assign : Array Nat) : List Nat → ClauseEvalRes
  | [] => .mk false none 0
  | lit :: rest =>
    match evalClauseArray assign rest with
    | .mk true u n => .mk true u n
    | .mk false u n =>
      let varId := Nat.shiftRight lit 1
      let wantPos := Nat.beq (Nat.land lit 1) 0
      let cur := arrayGetNat assign varId
      match Nat.beq cur 0 with
      | true => .mk false (some lit) (Nat.succ n)
      | false =>
        let isTrue := Nat.beq cur 2
        match isTrue, wantPos with
        | true, true => .mk true none 0
        | false, false => .mk true none 0
        | _, _ => .mk false u n

inductive ArrayAssignRes where
  | taut
  | ok (a : Array Nat)

def initAssignArrayAux : List Nat → Array Nat → ArrayAssignRes
  | [], a => .ok a
  | lit :: rest, a =>
    let varId := Nat.shiftRight lit 1
    let negCode := match Nat.beq (Nat.land lit 1) 0 with | true => 1 | false => 2
    let old := arrayGetNat a varId
    match Nat.beq old 0 with
    | true => initAssignArrayAux rest (arraySetNat a varId negCode)
    | false =>
      match Nat.beq old negCode with
      | true => initAssignArrayAux rest a
      | false => .taut

def propArrayHints (clauses : Array (Option (List Nat))) (assign : Array Nat) : List Nat → Bool
  | [] => false
  | cid :: rest =>
    match arrayGetOpt clauses cid with
    | none => false
    | some cls =>
      match evalClauseArray assign cls with
      | .mk true _ _ => false
      | .mk false _ 0 => true
      | .mk false (some uLit) 1 =>
        let varId := Nat.shiftRight uLit 1
        let code := match Nat.beq (Nat.land uLit 1) 0 with | true => 2 | false => 1
        propArrayHints clauses (arraySetNat assign varId code) rest
      | .mk false _ _ => false

inductive ArrayRunState where
  | running (db : Array (Option (List Nat)))
  | proved
  | failed

def stepArray (numVars : Nat) (st : ArrayRunState) (s : LratStep) : ArrayRunState :=
  match st with
  | .proved => .proved
  | .failed => .failed
  | .running db =>
    match s with
    | .addRup cid cls hints =>
      let ok := match initAssignArrayAux cls (mkZeroArray numVars []) with
        | .taut => true
        | .ok a0 => propArrayHints db a0 hints
      match ok with
      | false => .failed
      | true => .running (arraySetOpt db cid (some cls))
    | .del ids => .running (ids.foldr (fun cid cur => arraySetOpt cur cid none) db)
    | .addEmpty hints =>
      match propArrayHints db (mkZeroArray numVars []) hints with
      | true => .proved
      | false => .failed

def runArrayTree (numVars : Nat) : Nat → ArrayRunState → StepTree LratStep → ArrayRunState
  | 0, _, _ => .failed
  | Nat.succ _, st, .empty => st
  | Nat.succ _, st, .leaf s => stepArray numVars st s
  | Nat.succ fuel, st, .branch l r =>
    match runArrayTree numVars fuel st l with
    | .proved => .proved
    | .failed => .failed
    | .running db => runArrayTree numVars fuel (.running db) r

def initArrayDb : Nat → Array (Option (List Nat)) → StepTree (Nat × List Nat) → Array (Option (List Nat))
  | 0, db, _ => db
  | Nat.succ _, db, .empty => db
  | Nat.succ _, db, .leaf (cid, cls) => arraySetOpt db cid (some cls)
  | Nat.succ fuel, db, .branch l r => initArrayDb fuel (initArrayDb fuel db l) r

def checkLratArray (maxCid numVars treeFuel : Nat) (initClauses : StepTree (Nat × List Nat))
    (steps : StepTree LratStep) : Bool :=
  let db0 := initArrayDb treeFuel (mkNoneArray (List Nat) maxCid []) initClauses
  match runArrayTree numVars treeFuel (.running db0) steps with
  | .proved => true
  | _ => false

end LratBench
