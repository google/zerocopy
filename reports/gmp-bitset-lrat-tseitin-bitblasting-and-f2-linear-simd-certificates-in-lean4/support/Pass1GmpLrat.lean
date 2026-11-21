prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Init.Tactics

namespace Pass1GmpLrat

inductive StepTree (α : Type) where
  | empty
  | leaf (val : α)
  | branch (left right : StepTree α)

-- ============================================================================
-- 1. 8-Way Persistent OctTrie GMP Checker (`Nat.beq` strictness for `by rfl`)
-- ============================================================================

inductive OctTrie (α : Type) where
  | empty
  | node (val : Option α) (c0 c1 c2 c3 c4 c5 c6 c7 : OctTrie α)

def octGet {α : Type} (fuel : Nat) (t : OctTrie α) (idx : Nat) : Option α :=
  @Nat.rec (fun _ => OctTrie α → Nat → Option α)
    (fun _ _ => none)
    (fun _ ih cur i =>
      match cur with
      | .empty => none
      | .node v c0 c1 c2 c3 c4 c5 c6 c7 =>
        match Nat.beq i 0 with
        | true => v
        | false =>
          let nxt := Nat.shiftRight i 3
          match Nat.beq (Nat.land i 4) 0 with
          | true =>
            match Nat.beq (Nat.land i 2) 0 with
            | true  => match Nat.beq (Nat.land i 1) 0 with | true => ih c0 nxt | false => ih c1 nxt
            | false => match Nat.beq (Nat.land i 1) 0 with | true => ih c2 nxt | false => ih c3 nxt
          | false =>
            match Nat.beq (Nat.land i 2) 0 with
            | true  => match Nat.beq (Nat.land i 1) 0 with | true => ih c4 nxt | false => ih c5 nxt
            | false => match Nat.beq (Nat.land i 1) 0 with | true => ih c6 nxt | false => ih c7 nxt)
    fuel t idx

def octSet {α : Type} (fuel : Nat) (t : OctTrie α) (idx : Nat) (valOpt : Option α) : OctTrie α :=
  @Nat.rec (fun _ => OctTrie α → Nat → Option α → OctTrie α)
    (fun cur _ _ => cur)
    (fun _ ih cur i v =>
      match cur with
      | .empty =>
        match Nat.beq i 0 with
        | true => .node v .empty .empty .empty .empty .empty .empty .empty .empty
        | false =>
          let nxt := Nat.shiftRight i 3
          match ih .empty nxt v with
          | .empty => .empty
          | .node sv s0 s1 s2 s3 s4 s5 s6 s7 =>
            let sn := OctTrie.node sv s0 s1 s2 s3 s4 s5 s6 s7
            match Nat.beq (Nat.land i 4) 0 with
            | true =>
              match Nat.beq (Nat.land i 2) 0 with
              | true  => match Nat.beq (Nat.land i 1) 0 with
                | true  => .node none sn .empty .empty .empty .empty .empty .empty .empty
                | false => .node none .empty sn .empty .empty .empty .empty .empty .empty
              | false => match Nat.beq (Nat.land i 1) 0 with
                | true  => .node none .empty .empty sn .empty .empty .empty .empty .empty
                | false => .node none .empty .empty .empty sn .empty .empty .empty .empty
            | false =>
              match Nat.beq (Nat.land i 2) 0 with
              | true  => match Nat.beq (Nat.land i 1) 0 with
                | true  => .node none .empty .empty .empty .empty sn .empty .empty .empty
                | false => .node none .empty .empty .empty .empty .empty sn .empty .empty
              | false => match Nat.beq (Nat.land i 1) 0 with
                | true  => .node none .empty .empty .empty .empty .empty .empty sn .empty
                | false => .node none .empty .empty .empty .empty .empty .empty .empty sn
      | .node v0 c0 c1 c2 c3 c4 c5 c6 c7 =>
        match Nat.beq i 0 with
        | true => .node v c0 c1 c2 c3 c4 c5 c6 c7
        | false =>
          let nxt := Nat.shiftRight i 3
          match Nat.beq (Nat.land i 4) 0 with
          | true =>
            match Nat.beq (Nat.land i 2) 0 with
            | true =>
              match Nat.beq (Nat.land i 1) 0 with
              | true  => match ih c0 nxt v with | .empty => .node v0 .empty c1 c2 c3 c4 c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c1 c2 c3 c4 c5 c6 c7
              | false => match ih c1 nxt v with | .empty => .node v0 c0 .empty c2 c3 c4 c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c2 c3 c4 c5 c6 c7
            | false =>
              match Nat.beq (Nat.land i 1) 0 with
              | true  => match ih c2 nxt v with | .empty => .node v0 c0 c1 .empty c3 c4 c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c3 c4 c5 c6 c7
              | false => match ih c3 nxt v with | .empty => .node v0 c0 c1 c2 .empty c4 c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c4 c5 c6 c7
          | false =>
            match Nat.beq (Nat.land i 2) 0 with
            | true =>
              match Nat.beq (Nat.land i 1) 0 with
              | true  => match ih c4 nxt v with | .empty => .node v0 c0 c1 c2 c3 .empty c5 c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c5 c6 c7
              | false => match ih c5 nxt v with | .empty => .node v0 c0 c1 c2 c3 c4 .empty c6 c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 c4 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c6 c7
            | false =>
              match Nat.beq (Nat.land i 1) 0 with
              | true  => match ih c6 nxt v with | .empty => .node v0 c0 c1 c2 c3 c4 c5 .empty c7 | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 c4 c5 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c7
              | false => match ih c7 nxt v with | .empty => .node v0 c0 c1 c2 c3 c4 c5 c6 .empty | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 c4 c5 c6 (.node sv s0 s1 s2 s3 s4 s5 s6 s7))
    fuel t idx valOpt

inductive MaskStream where | mk (mask : Nat) (rest : Nat)
inductive PropStream where | mk (ok : Bool) (rest : Nat)
inductive DelStream  where | mk (db : OctTrie Nat) (rest : Nat)
inductive RunState   where | running (db : OctTrie Nat) | proved | failed

def readMaskU16 (cnt s0 : Nat) : MaskStream :=
  @Nat.rec (fun _ => Nat → Nat → MaskStream)
    (fun s acc => .mk acc s)
    (fun _ ih s acc =>
      let lit := Nat.land s 0xffff
      let s'  := Nat.shiftRight s 16
      let acc' := Nat.lor acc (Nat.shiftLeft 1 lit)
      match Nat.beq acc' 0, Nat.beq s' 0 with
      | true, true   => ih 0 0
      | true, false  => ih s' 0
      | false, true  => ih 0 acc'
      | false, false => ih s' acc')
    cnt s0 0

def propHintsU16 (oDepth : Nat) (clauses : OctTrie Nat) (cnt falsified0 s0 : Nat) : PropStream :=
  @Nat.rec (fun _ => Nat → Nat → PropStream)
    (fun _ s => .mk false s)
    (fun k ih falsified s =>
      let cid := Nat.land s 0xffff
      let s'  := Nat.shiftRight s 16
      match octGet oDepth clauses cid with
      | none => .mk false (Nat.shiftRight s' (Nat.mul 16 k))
      | some mask =>
        let rem := Nat.xor mask (Nat.land mask falsified)
        match Nat.beq rem 0 with
        | true => .mk true (Nat.shiftRight s' (Nat.mul 16 k))
        | false =>
          match Nat.beq (Nat.land rem (Nat.sub rem 1)) 0 with
          | false => .mk false (Nat.shiftRight s' (Nat.mul 16 k))
          | true =>
            let negRaw := match Nat.beq (Nat.mod rem 3) 1 with
              | true  => Nat.shiftLeft rem 1
              | false => Nat.shiftRight rem 1
            let falsified' := Nat.lor falsified negRaw
            match Nat.beq falsified' 0 with
            | true  => ih 0 s'
            | false => ih falsified' s')
    cnt falsified0 s0

def delIdsU16 (oDepth cnt : Nat) (db0 : OctTrie Nat) (s0 : Nat) : DelStream :=
  @Nat.rec (fun _ => OctTrie Nat → Nat → DelStream)
    (fun db s => .mk db s)
    (fun _ ih db s =>
      let cid := Nat.land s 0xffff
      let s'  := Nat.shiftRight s 16
      match octSet oDepth db cid none with
      | .empty => ih .empty s'
      | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih (.node v c0 c1 c2 c3 c4 c5 c6 c7) s')
    cnt db0 s0

def initChunkU16 (oDepth fuel : Nat) (db0 : OctTrie Nat) (s0 : Nat) : OctTrie Nat :=
  @Nat.rec (fun _ => OctTrie Nat → Nat → OctTrie Nat)
    (fun db _ => db)
    (fun _ ih db s =>
      let cid := Nat.land s 0xffff
      let s1  := Nat.shiftRight s 16
      match Nat.beq cid 0 with
      | true => db
      | false =>
        let cLen := Nat.land s1 0xffff
        let s2   := Nat.shiftRight s1 16
        match readMaskU16 cLen s2 with
        | .mk m s3 =>
          match octSet oDepth db cid (some m) with
          | .empty => ih .empty s3
          | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih (.node v c0 c1 c2 c3 c4 c5 c6 c7) s3)
    fuel db0 s0

def runChunkU16 (oDepth fuel : Nat) (st0 : RunState) (s0 : Nat) : RunState :=
  @Nat.rec (fun _ => RunState → Nat → RunState)
    (fun st _ => st)
    (fun _ ih st s =>
      match st with
      | .proved => .proved
      | .failed => .failed
      | .running db =>
        let tag := Nat.land s 0xffff
        let s1  := Nat.shiftRight s 16
        match Nat.beq tag 0 with
        | true => .running db
        | false =>
          match Nat.beq tag 1 with
          | true =>
            let cid  := Nat.land s1 0xffff
            let cLen := Nat.land (Nat.shiftRight s1 16) 0xffff
            let hLen := Nat.land (Nat.shiftRight s1 32) 0xffff
            let s4   := Nat.shiftRight s1 48
            match readMaskU16 cLen s4 with
            | .mk targetMask s5 =>
              match propHintsU16 oDepth db hLen targetMask s5 with
              | .mk false _ => .failed
              | .mk true s6 =>
                match Nat.beq targetMask 0 with
                | true => .proved
                | false =>
                  match octSet oDepth db cid (some targetMask) with
                  | .empty => ih (.running .empty) s6
                  | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih (.running (.node v c0 c1 c2 c3 c4 c5 c6 c7)) s6
          | false =>
            match Nat.beq tag 2 with
            | true =>
              let dLen := Nat.land s1 0xffff
              let s2   := Nat.shiftRight s1 16
              match delIdsU16 oDepth dLen db s2 with
              | .mk db' s3 => ih (.running db') s3
            | false =>
              let hLen := Nat.land s1 0xffff
              let s2   := Nat.shiftRight s1 16
              match propHintsU16 oDepth db hLen 0 s2 with
              | .mk true _  => .proved
              | .mk false _ => .failed)
    fuel st0 s0

def initStreamTree (oDepth treeFuel : Nat) (t0 : StepTree Nat) (db0 : OctTrie Nat) : OctTrie Nat :=
  @Nat.rec (fun _ => StepTree Nat → OctTrie Nat → OctTrie Nat)
    (fun _ db => db)
    (fun _ ih t db =>
      match t with
      | .empty => db
      | .leaf s => initChunkU16 oDepth 40 db s
      | .branch l r =>
        match ih l db with
        | .empty => ih r .empty
        | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih r (.node v c0 c1 c2 c3 c4 c5 c6 c7))
    treeFuel t0 db0

def runStreamTree (oDepth treeFuel : Nat) (t0 : StepTree Nat) (st0 : RunState) : RunState :=
  @Nat.rec (fun _ => StepTree Nat → RunState → RunState)
    (fun _ _ => .failed)
    (fun _ ih t st =>
      match t with
      | .empty => st
      | .leaf s => runChunkU16 oDepth 40 st s
      | .branch l r =>
        match ih l st with
        | .proved => .proved
        | .failed => .failed
        | .running db =>
          match db with
          | .empty => ih r (.running .empty)
          | .node v c0 c1 c2 c3 c4 c5 c6 c7 => ih r (.running (.node v c0 c1 c2 c3 c4 c5 c6 c7)))
    treeFuel t0 st0

def checkLratPass1Clean (oDepth : Nat) (initTree stepsTree : StepTree Nat) : Bool :=
  match initStreamTree oDepth 18 initTree .empty with
  | .empty => false
  | .node v c0 c1 c2 c3 c4 c5 c6 c7 =>
    match runStreamTree oDepth 18 stepsTree (.running (.node v c0 c1 c2 c3 c4 c5 c6 c7)) with
    | .proved => true
    | _ => false

-- ============================================================================
-- 2. 16-Bucket Non-Recursive Bit-Paged GMP Clause Database (`GmpDb16`)
--    Zero tree recursion on clause lookup/update; `@Nat.casesOn` collapses
--    updated GMP `mpz_t` bucket integers directly in `Kernel.whnf`!
-- ============================================================================

structure GmpDb16 where
  b0  : Nat
  b1  : Nat
  b2  : Nat
  b3  : Nat
  b4  : Nat
  b5  : Nat
  b6  : Nat
  b7  : Nat
  b8  : Nat
  b9  : Nat
  b10 : Nat
  b11 : Nat
  b12 : Nat
  b13 : Nat
  b14 : Nat
  b15 : Nat

def GmpDb16.empty : GmpDb16 :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def withCollapsedNat {α : Type} (x : Nat) (k : Nat → α) : α :=
  @Nat.casesOn (fun _ => α) x (k 0) (fun p => k (Nat.succ p))

def GmpDb16.getBucket (db : GmpDb16) (b : Nat) : Nat :=
  match db with
  | ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩ =>
    match b with
    | 0  => x0  | 1  => x1  | 2  => x2  | 3  => x3
    | 4  => x4  | 5  => x5  | 6  => x6  | 7  => x7
    | 8  => x8  | 9  => x9  | 10 => x10 | 11 => x11
    | 12 => x12 | 13 => x13 | 14 => x14 | _  => x15

def GmpDb16.setBucket (db : GmpDb16) (b : Nat) (v : Nat) : GmpDb16 :=
  withCollapsedNat v fun fv =>
    match db with
    | ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩ =>
      match b with
      | 0  => ⟨fv,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩
      | 1  => ⟨x0,fv,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩
      | 2  => ⟨x0,x1,fv,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩
      | 3  => ⟨x0,x1,x2,fv,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩
      | 4  => ⟨x0,x1,x2,x3,fv,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩
      | 5  => ⟨x0,x1,x2,x3,x4,fv,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩
      | 6  => ⟨x0,x1,x2,x3,x4,x5,fv,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩
      | 7  => ⟨x0,x1,x2,x3,x4,x5,x6,fv,x8,x9,x10,x11,x12,x13,x14,x15⟩
      | 8  => ⟨x0,x1,x2,x3,x4,x5,x6,x7,fv,x9,x10,x11,x12,x13,x14,x15⟩
      | 9  => ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,fv,x10,x11,x12,x13,x14,x15⟩
      | 10 => ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,fv,x11,x12,x13,x14,x15⟩
      | 11 => ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,fv,x12,x13,x14,x15⟩
      | 12 => ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,fv,x13,x14,x15⟩
      | 13 => ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,fv,x14,x15⟩
      | 14 => ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,fv,x15⟩
      | _  => ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,fv⟩

def GmpDb16.getClause (strideBits strideMask : Nat) (db : GmpDb16) (slotId : Nat) : Nat :=
  let b   := Nat.land slotId 15
  let idx := Nat.shiftRight slotId 4
  let off := Nat.mul idx strideBits
  Nat.land (Nat.shiftRight (db.getBucket b) off) strideMask

def GmpDb16.setClause (strideBits strideMask : Nat) (db : GmpDb16) (slotId : Nat) (mask : Nat) : GmpDb16 :=
  let b        := Nat.land slotId 15
  let idx      := Nat.shiftRight slotId 4
  let off      := Nat.mul idx strideBits
  let curB     := db.getBucket b
  let oldSlice := Nat.shiftLeft (Nat.land (Nat.shiftRight curB off) strideMask) off
  let cleared  := Nat.xor curB oldSlice
  let newB     := Nat.lor cleared (Nat.shiftLeft (Nat.land mask strideMask) off)
  db.setBucket b newB

inductive Del16Stream where | mk (db : GmpDb16) (rest : Nat)
inductive Run16State  where | running (db : GmpDb16) | proved | failed

def propGmp16Hints (strideBits strideMask : Nat) (db : GmpDb16) (cnt falsified0 s0 : Nat) : PropStream :=
  @Nat.rec (fun _ => Nat → Nat → PropStream)
    (fun _ s => .mk false s)
    (fun k ih falsified s =>
      let slotId := Nat.land s 0xffff
      let s'     := Nat.shiftRight s 16
      let mask   := db.getClause strideBits strideMask slotId
      match Nat.beq mask 0 with
      | true => .mk false (Nat.shiftRight s' (Nat.mul 16 k))
      | false =>
        let rem := Nat.xor mask (Nat.land mask falsified)
        match Nat.beq rem 0 with
        | true => .mk true (Nat.shiftRight s' (Nat.mul 16 k))
        | false =>
          match Nat.beq (Nat.land rem (Nat.sub rem 1)) 0 with
          | false => .mk false (Nat.shiftRight s' (Nat.mul 16 k))
          | true =>
            let negRaw := match Nat.beq (Nat.mod rem 3) 1 with
              | true  => Nat.shiftLeft rem 1
              | false => Nat.shiftRight rem 1
            withCollapsedNat (Nat.lor falsified negRaw) fun fStrict =>
              ih fStrict s')
    cnt falsified0 s0

def delGmp16Ids (strideBits strideMask cnt : Nat) (db0 : GmpDb16) (s0 : Nat) : Del16Stream :=
  @Nat.rec (fun _ => GmpDb16 → Nat → Del16Stream)
    (fun db s => .mk db s)
    (fun _ ih db s =>
      let slotId := Nat.land s 0xffff
      let s'     := Nat.shiftRight s 16
      match db.setClause strideBits strideMask slotId 0 with
      | ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩ =>
        ih ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩ s')
    cnt db0 s0

def initChunkGmp16 (strideBits strideMask fuel : Nat) (db0 : GmpDb16) (s0 : Nat) : GmpDb16 :=
  @Nat.rec (fun _ => GmpDb16 → Nat → GmpDb16)
    (fun db _ => db)
    (fun _ ih db s =>
      let slotId := Nat.land s 0xffff
      let s1     := Nat.shiftRight s 16
      match Nat.beq slotId 0 with
      | true => db
      | false =>
        let cLen := Nat.land s1 0xffff
        let s2   := Nat.shiftRight s1 16
        match readMaskU16 cLen s2 with
        | .mk m s3 =>
          match db.setClause strideBits strideMask slotId m with
          | ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩ =>
            ih ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩ s3)
    fuel db0 s0

def runChunkGmp16 (strideBits strideMask fuel : Nat) (st0 : Run16State) (s0 : Nat) : Run16State :=
  @Nat.rec (fun _ => Run16State → Nat → Run16State)
    (fun st _ => st)
    (fun _ ih st s =>
      match st with
      | .proved => .proved
      | .failed => .failed
      | .running db =>
        let tag := Nat.land s 0xffff
        let s1  := Nat.shiftRight s 16
        match Nat.beq tag 0 with
        | true => .running db
        | false =>
          match Nat.beq tag 1 with
          | true =>
            let slotId := Nat.land s1 0xffff
            let cLen   := Nat.land (Nat.shiftRight s1 16) 0xffff
            let hLen   := Nat.land (Nat.shiftRight s1 32) 0xffff
            let s4     := Nat.shiftRight s1 48
            match readMaskU16 cLen s4 with
            | .mk targetMask s5 =>
              match propGmp16Hints strideBits strideMask db hLen targetMask s5 with
              | .mk false _ => .failed
              | .mk true s6 =>
                match Nat.beq targetMask 0 with
                | true => .proved
                | false =>
                  withCollapsedNat s6 fun fs6 =>
                    match db.setClause strideBits strideMask slotId targetMask with
                    | ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩ =>
                      ih (.running ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩) fs6
          | false =>
            match Nat.beq tag 2 with
            | true =>
              let dLen := Nat.land s1 0xffff
              let s2   := Nat.shiftRight s1 16
              match delGmp16Ids strideBits strideMask dLen db s2 with
              | .mk db' s3 =>
                withCollapsedNat s3 fun fs3 =>
                  match db' with
                  | ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩ =>
                    ih (.running ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩) fs3
            | false =>
              let hLen := Nat.land s1 0xffff
              let s2   := Nat.shiftRight s1 16
              match propGmp16Hints strideBits strideMask db hLen 0 s2 with
              | .mk true _  => .proved
              | .mk false _ => .failed)
    fuel st0 s0

def initTreeGmp16 (strideBits strideMask treeFuel : Nat) (t0 : StepTree Nat) (db0 : GmpDb16) : GmpDb16 :=
  @Nat.rec (fun _ => StepTree Nat → GmpDb16 → GmpDb16)
    (fun _ db => db)
    (fun _ ih t db =>
      match t with
      | .empty => db
      | .leaf s => initChunkGmp16 strideBits strideMask 16 db s
      | .branch l r =>
        match ih l db with
        | ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩ =>
          ih r ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩)
    treeFuel t0 db0

def runTreeGmp16 (strideBits strideMask treeFuel : Nat) (t0 : StepTree Nat) (st0 : Run16State) : Run16State :=
  @Nat.rec (fun _ => StepTree Nat → Run16State → Run16State)
    (fun _ _ => .failed)
    (fun _ ih t st =>
      match t with
      | .empty => st
      | .leaf s => runChunkGmp16 strideBits strideMask 16 st s
      | .branch l r =>
        match ih l st with
        | .proved => .proved
        | .failed => .failed
        | .running ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩ =>
          ih r (.running ⟨x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15⟩))
    treeFuel t0 st0

def checkLratGmp16Clean (strideBits treeFuel : Nat) (initTree stepsTree : StepTree Nat) : Bool :=
  let strideMask := Nat.sub (Nat.shiftLeft 1 strideBits) 1
  let db0 := initTreeGmp16 strideBits strideMask treeFuel initTree GmpDb16.empty
  match runTreeGmp16 strideBits strideMask treeFuel stepsTree (.running db0) with
  | .proved => true
  | _ => false

end Pass1GmpLrat
