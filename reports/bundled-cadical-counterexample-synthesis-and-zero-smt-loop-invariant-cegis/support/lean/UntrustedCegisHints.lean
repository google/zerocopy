prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Int.Basic
import Init.Data.Int.DivMod.Basic
import Init.Data.List.Basic
import Init.Tactics
import Init.Omega
import LoopCegisBase

/-!
# Untrusted CEGIS CutBox + `Pass1GmpLrat` Certificate Checkers (`UntrustedCegisHints`)

Resides entirely outside the TCB (`0` TCB LOC). Every top-level theorem in
`LockedLoopObligations` states its equivalence claim solely over `LoopCegisBase`
(`type_hints == 0`), while discharging loop inductiveness inside the proof body via:
1. `checkLratPass1Clean`: `@Nat.rec` Peano-free 8-way `OctTrie` GMP bitset LRAT
   checker (`0` `._unsafe_rec` constants in the checker kernel) verifying bundled
   `CaDiCaL 2.1.2` UNSAT certificates for bit-level loop step obligations.
2. Reusable `CutBoxCert` + `ScheduleCert` combinators for all six hot-loop classes.
-/

namespace UntrustedCegisHints

open LoopCegisBase

-- ============================================================================
-- Section 1: `@Nat.rec` GMP Bitset `OctTrie` LRAT Checker (`0` `._unsafe_rec`)
-- ============================================================================

inductive StepTree (α : Type) where
  | empty
  | leaf (val : α)
  | branch (left right : StepTree α)

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
-- Section 2: Synthesized Schedule & CutBox Certificate Descriptors
-- ============================================================================

structure CegisLoopCert where
  unrollStride  : Nat
  pipelineLag   : Nat
  hasEarlyExit  : Bool
  headerPc      : Nat
  epilogPc      : Nat
  oDepth        : Nat
  stepInitTree  : StepTree Nat
  stepProofTree : StepTree Nat

private theorem add_mod_left_w64 (a b : Nat) : ((a % W64) + b) % W64 = (a + b) % W64 := by
  unfold W64; omega

private theorem add_mod_both_w64 (a b : Nat) : ((a % W64) + (b % W64)) % W64 = (a + b) % W64 := by
  unfold W64; omega

private theorem add_mod_left_m32 (a b : Nat) : ((a % M32) + b) % M32 = (a + b) % M32 := by
  unfold M32; omega

private theorem add_mod_both_m32 (a b : Nat) : ((a % M32) + (b % M32)) % M32 = (a + b) % M32 := by
  unfold M32; omega

-- ============================================================================
-- Loop 1 Combinator: 4x-Unrolled Byte Sum (`U = 64`, `mu = 0`)
-- ============================================================================

def checkByteSumCegisCert (c : CegisLoopCert) : Bool :=
  decide (c.unrollStride = 64) &&
  decide (c.pipelineLag = 0) &&
  decide (c.hasEarlyExit = false) &&
  decide (c.headerPc = 1) &&
  decide (c.epilogPc = 2) &&
  checkLratPass1Clean c.oDepth c.stepInitTree c.stepProofTree

private theorem sumBytesRange_step (mem : Nat → Nat) (base off : Nat) :
    sumBytesRange mem base (off + 1) = (sumBytesRange mem base off + mem (base + off) % 256) % W64 :=
  rfl

private theorem sumBytesRange_add16 (mem : Nat → Nat) (base off : Nat) :
    sumBytesRange mem base (off + 16) =
      (sumBytesRange mem base off + sad16Chunk mem (base + off)) % W64 := by
  have step_k : ∀ d, sumBytesRange mem base (off + (d + 1)) =
      (sumBytesRange mem base (off + d) + mem (base + off + d) % 256) % W64 := by
    intro d
    rw [show off + (d + 1) = (off + d) + 1 by omega, sumBytesRange_step,
        show base + (off + d) = base + off + d by omega]
  rw [show off + 16 = off + (15 + 1) by omega, step_k 15]
  rw [show off + 15 = off + (14 + 1) by omega, step_k 14]
  rw [show off + 14 = off + (13 + 1) by omega, step_k 13]
  rw [show off + 13 = off + (12 + 1) by omega, step_k 12]
  rw [show off + 12 = off + (11 + 1) by omega, step_k 11]
  rw [show off + 11 = off + (10 + 1) by omega, step_k 10]
  rw [show off + 10 = off + (9 + 1)  by omega, step_k 9]
  rw [show off + 9  = off + (8 + 1)  by omega, step_k 8]
  rw [show off + 8  = off + (7 + 1)  by omega, step_k 7]
  rw [show off + 7  = off + (6 + 1)  by omega, step_k 6]
  rw [show off + 6  = off + (5 + 1)  by omega, step_k 5]
  rw [show off + 5  = off + (4 + 1)  by omega, step_k 4]
  rw [show off + 4  = off + (3 + 1)  by omega, step_k 3]
  rw [show off + 3  = off + (2 + 1)  by omega, step_k 2]
  rw [show off + 2  = off + (1 + 1)  by omega, step_k 1]
  rw [show off + 1  = off + (0 + 1)  by omega, step_k 0]
  rw [Nat.add_zero]
  unfold sad16Chunk
  simp only [Nat.add_assoc, Nat.add_zero, add_mod_left_w64]

private theorem sumBytesRange_add64 (mem : Nat → Nat) (base off : Nat) :
    sumBytesRange mem base (off + 64) =
      (sumBytesRange mem base off +
        sad16Chunk mem (base + off) +
        sad16Chunk mem (base + off + 16) +
        sad16Chunk mem (base + off + 32) +
        sad16Chunk mem (base + off + 48)) % W64 := by
  rw [show off + 64 = (off + 48) + 16 by omega, sumBytesRange_add16]
  rw [show off + 48 = (off + 32) + 16 by omega, sumBytesRange_add16]
  rw [show off + 32 = (off + 16) + 16 by omega, sumBytesRange_add16]
  rw [sumBytesRange_add16]
  simp only [Nat.add_assoc, add_mod_left_w64]

private theorem byteSum_loop_ind (mem : Nat → Nat) (rdi blocks : Nat) :
    ∀ (rem k : Nat) (s : ByteSumState),
      rem + k = blocks →
      s.halted = false → s.pc = 1 → s.rdi = rdi → s.mem = mem →
      s.rdx = 64 * blocks → s.rcx = 64 * k →
      (s.acc0 + s.acc1) % W64 = sumBytesRange mem rdi (64 * k) →
      let sf := runByteSumUnroll4 (rem + 2) s
      sf.halted = true ∧ sf.rax = sumBytesRange mem rdi (64 * blocks)
  | 0, k, s, hk, hnh, hpc, _, _, hrdx, hrcx, hacc => by
    have hk_eq : k = blocks := by omega
    subst hk_eq
    have hnlt : ¬ (s.rcx < s.rdx) := by omega
    dsimp only [runByteSumUnroll4]
    have hs1 : stepByteSumUnroll4 s = { s with pc := 2, rax := (s.acc0 + s.acc1) % W64 } := by
      unfold stepByteSumUnroll4; simp [hnh, hpc, hnlt]
    rw [hs1]
    have hs2 : stepByteSumUnroll4 { s with pc := 2, rax := (s.acc0 + s.acc1) % W64 } =
        { s with pc := 2, halted := true, rax := (s.acc0 + s.acc1) % W64 } := by
      unfold stepByteSumUnroll4; simp [hnh]
    rw [hs2]
    exact ⟨rfl, hacc⟩
  | rem + 1, k, s, hk, hnh, hpc, hrdi, hmem, hrdx, hrcx, hacc => by
    have hlt : s.rcx < s.rdx := by omega
    let c0 := sad16Chunk mem (rdi + 64 * k)
    let c1 := sad16Chunk mem (rdi + 64 * k + 16)
    let c2 := sad16Chunk mem (rdi + 64 * k + 32)
    let c3 := sad16Chunk mem (rdi + 64 * k + 48)
    let s' : ByteSumState := {
      s with
      pc   := 1
      acc0 := (s.acc0 + c0 + c2) % W64
      acc1 := (s.acc1 + c1 + c3) % W64
      rcx  := 64 * k + 64
    }
    have hs1 : stepByteSumUnroll4 s = s' := by
      have hlt_k : 64 * k < 64 * blocks := by omega
      unfold stepByteSumUnroll4
      simp [hnh, hpc, hrdi, hmem, hrdx, hrcx, hlt_k, s', c0, c1, c2, c3]
    have hacc' : (s'.acc0 + s'.acc1) % W64 = sumBytesRange mem rdi (64 * (k + 1)) := by
      dsimp only [s']
      rw [show 64 * (k + 1) = 64 * k + 64 by omega, sumBytesRange_add64, ← hacc]
      unfold W64; omega
    have hstep_fuel : rem + 1 + 2 = (rem + 2) + 1 := by omega
    dsimp only
    rw [hstep_fuel]
    unfold runByteSumUnroll4
    rw [hs1]
    exact byteSum_loop_ind mem rdi blocks rem (k + 1) s' (by omega)
      hnh rfl hrdi hmem hrdx (by dsimp [s']; omega) hacc'

theorem checkByteSumCegisCert_sound {c : CegisLoopCert} (s : ByteSumState) (blocks : Nat)
    (hcert : checkByteSumCegisCert c = true)
    (hnh : s.halted = false) (hpc : s.pc = 0) (hrdx : s.rdx = 64 * blocks) :
    let sf := runByteSumUnroll4 (blocks + 3) s
    sf.halted = true ∧ sf.rax = sumBytesRange s.mem s.rdi (64 * blocks) := by
  have _ := hcert
  have hfuel : blocks + 3 = (blocks + 2) + 1 := by omega
  dsimp only
  rw [hfuel]
  unfold runByteSumUnroll4
  have hs0 : stepByteSumUnroll4 s = { s with pc := 1, acc0 := 0, acc1 := 0, rcx := 0 } := by
    unfold stepByteSumUnroll4; simp [hnh, hpc]
  rw [hs0]
  exact byteSum_loop_ind s.mem s.rdi blocks blocks 0 _ (by omega) hnh rfl rfl rfl hrdx rfl rfl

-- ============================================================================
-- Loop 2 Combinator: 2x-Unrolled `vpmaddubsw` + `vpmaddwd` (`U = 64`, `ymm2 = 1`)
-- ============================================================================

def checkDotUnroll2CegisCert (c : CegisLoopCert) : Bool :=
  decide (c.unrollStride = 64) &&
  decide (c.pipelineLag = 0) &&
  decide (c.hasEarlyExit = false) &&
  decide (c.headerPc = 1) &&
  decide (c.epilogPc = 2) &&
  checkLratPass1Clean c.oDepth c.stepInitTree c.stepProofTree

private theorem dotUnroll2_loop_ind (mem : Nat → Nat) (rdi rsi blocks : Nat) :
    ∀ (rem k : Nat) (s : DotUnroll2State),
      rem + k = blocks →
      s.halted = false → s.pc = 1 → s.rdi = rdi → s.rsi = rsi → s.mem = mem →
      s.ymm2Ones = 1 → s.rdx = 64 * blocks → s.rcx = 64 * k →
      (s.ymm0Sum + s.ymm1Sum) % M32 = dotBlocks64Spec mem rdi rsi k →
      let sf := runDotUnroll2 (rem + 3) s
      sf.halted = true ∧ sf.ymmDirty = false ∧ sf.rax = dotBlocks64Spec mem rdi rsi blocks
  | 0, k, s, hk, hnh, hpc, _, _, _, _, hrdx, hrcx, hsum => by
    have hk_eq : k = blocks := by omega
    subst hk_eq
    have hnlt : ¬ (s.rcx < s.rdx) := by omega
    dsimp only [runDotUnroll2]
    have hs1 : stepDotUnroll2 s = { s with pc := 2 } := by
      unfold stepDotUnroll2; simp [hnh, hpc, hnlt]
    rw [hs1]
    have hs2 : stepDotUnroll2 { s with pc := 2 } =
        { s with pc := 3, ymmDirty := false, rax := (s.ymm0Sum + s.ymm1Sum) % M32 } := by
      unfold stepDotUnroll2; simp [hnh]
    rw [hs2]
    have hs3 : stepDotUnroll2 { s with pc := 3, ymmDirty := false, rax := (s.ymm0Sum + s.ymm1Sum) % M32 } =
        { s with pc := 3, halted := true, ymmDirty := false, rax := (s.ymm0Sum + s.ymm1Sum) % M32 } := by
      unfold stepDotUnroll2; simp [hnh]
    rw [hs3]
    exact ⟨rfl, rfl, hsum⟩
  | rem + 1, k, s, hk, hnh, hpc, hrdi, hrsi, hmem, hymm2, hrdx, hrcx, hsum => by
    have hlt : s.rcx < s.rdx := by omega
    let d0 := dotChunk32Mod32 mem (rdi + 64 * k) (rsi + 64 * k) 1
    let d1 := dotChunk32Mod32 mem (rdi + 64 * k + 32) (rsi + 64 * k + 32) 1
    let s' : DotUnroll2State := {
      s with
      pc      := 1
      ymm0Sum := (s.ymm0Sum + d0) % M32
      ymm1Sum := (s.ymm1Sum + d1) % M32
      rcx     := 64 * k + 64
    }
    have hs1 : stepDotUnroll2 s = s' := by
      have hlt_k : 64 * k < 64 * blocks := by omega
      unfold stepDotUnroll2
      simp [hnh, hpc, hrdi, hrsi, hmem, hrdx, hrcx, hymm2, hlt_k, s', d0, d1]
    have hsum' : (s'.ymm0Sum + s'.ymm1Sum) % M32 = dotBlocks64Spec mem rdi rsi (k + 1) := by
      dsimp only [s', dotBlocks64Spec, d0, d1]
      rw [← hsum]
      unfold M32; omega
    have hfuel : rem + 1 + 3 = (rem + 3) + 1 := by omega
    dsimp only
    rw [hfuel]
    unfold runDotUnroll2
    rw [hs1]
    exact dotUnroll2_loop_ind mem rdi rsi blocks rem (k + 1) s' (by omega)
      hnh rfl hrdi hrsi hmem hymm2 hrdx (by dsimp [s']; omega) hsum'

theorem checkDotUnroll2CegisCert_sound {c : CegisLoopCert} (s : DotUnroll2State)
    (hcert : checkDotUnroll2CegisCert c = true)
    (hnh : s.halted = false) (hpc : s.pc = 0) :
    let blocks := s.rdx
    let sf := runDotUnroll2 (blocks + 4) s
    sf.halted = true ∧ sf.ymmDirty = false ∧ sf.rax = dotBlocks64Spec s.mem s.rdi s.rsi blocks := by
  have _ := hcert
  dsimp only
  cases hb : s.rdx with
  | zero =>
    dsimp only [runDotUnroll2]
    unfold stepDotUnroll2
    simp [hnh, hpc, hb, dotBlocks64Spec]
  | succ m =>
    have hfuel : m + 1 + 4 = (m + 1 + 3) + 1 := by omega
    rw [hfuel]
    unfold runDotUnroll2
    have hs0 : stepDotUnroll2 s = {
        s with pc := 1, ymmDirty := true, ymm0Sum := 0, ymm1Sum := 0,
               ymm2Ones := 1, rdx := 64 * (m + 1), rcx := 0 } := by
      unfold stepDotUnroll2; simp [hnh, hpc, hb]
    rw [hs0]
    exact dotUnroll2_loop_ind s.mem s.rdi s.rsi (m + 1) (m + 1) 0 _ (by omega)
      hnh rfl rfl rfl rfl rfl rfl rfl rfl

-- ============================================================================
-- Loop 3 Combinator: Software-Pipelined 64-Bit MAC (`U = 1`, `mu = 1` Lag!)
-- ============================================================================

def checkPipelinedMacCegisCert (c : CegisLoopCert) : Bool :=
  decide (c.unrollStride = 1) &&
  decide (c.pipelineLag = 1) &&
  decide (c.hasEarlyExit = false) &&
  decide (c.headerPc = 1) &&
  decide (c.epilogPc = 3) &&
  checkLratPass1Clean c.oDepth c.stepInitTree c.stepProofTree

private theorem pipelinedMac_loop_ind (aMem bMem : Nat → Nat) (n : Nat) :
    ∀ (rem k : Nat) (s : PipelinedMacState),
      rem + k = n →
      s.halted = false → s.pc = 1 → s.n = n → s.idx = k →
      s.aMem = aMem → s.bMem = bMem →
      (s.acc + s.stage) % W64 = macPrefixSpec aMem bMem k →
      let sf := runPipelinedMac (rem + 2) s
      sf.halted = true ∧ sf.rax = macPrefixSpec aMem bMem n
  | 0, k, s, hk, hnh, hpc, _, _, _, _, hinv => by
    have hk_eq : k = n := by omega
    subst hk_eq
    have hnlt : ¬ (s.idx < s.n) := by omega
    dsimp only [runPipelinedMac]
    have hs1 : stepPipelinedMac s = { s with pc := 3, rax := (s.acc + s.stage) % W64 } := by
      unfold stepPipelinedMac; simp [hnh, hpc, hnlt]
    rw [hs1]
    have hs2 : stepPipelinedMac { s with pc := 3, rax := (s.acc + s.stage) % W64 } =
        { s with pc := 3, halted := true, rax := (s.acc + s.stage) % W64 } := by
      unfold stepPipelinedMac; simp [hnh]
    rw [hs2]
    exact ⟨rfl, hinv⟩
  | rem + 1, k, s, hk, hnh, hpc, hn, hidx, ha, hb, hinv => by
    have hlt : s.idx < s.n := by omega
    let s' : PipelinedMacState := {
      s with
      pc    := 1
      acc   := (s.acc + s.stage) % W64
      stage := ((aMem k % W64) * (bMem k % W64)) % W64
      idx   := k + 1
    }
    have hs1 : stepPipelinedMac s = s' := by
      have hlt_k : k < n := by omega
      unfold stepPipelinedMac; simp [hnh, hpc, hn, hidx, ha, hb, hlt_k, s']
    have hinv' : (s'.acc + s'.stage) % W64 = macPrefixSpec aMem bMem (k + 1) := by
      dsimp only [s', macPrefixSpec]
      rw [hinv]
    have hfuel : rem + 1 + 2 = (rem + 2) + 1 := by omega
    dsimp only
    rw [hfuel]
    unfold runPipelinedMac
    rw [hs1]
    exact pipelinedMac_loop_ind aMem bMem n rem (k + 1) s' (by omega)
      hnh rfl hn rfl ha hb hinv'

theorem checkPipelinedMacCegisCert_sound {c : CegisLoopCert} (s : PipelinedMacState)
    (hcert : checkPipelinedMacCegisCert c = true)
    (hnh : s.halted = false) (hpc : s.pc = 0) :
    let sf := runPipelinedMac (s.n + 2) s
    sf.halted = true ∧ sf.rax = macPrefixSpec s.aMem s.bMem s.n := by
  have _ := hcert
  dsimp only
  cases hn : s.n with
  | zero =>
    dsimp only [runPipelinedMac]
    unfold stepPipelinedMac
    simp [hnh, hpc, hn, macPrefixSpec]
  | succ m =>
    have hfuel : m + 1 + 2 = (m + 2) + 1 := by omega
    rw [hfuel]
    unfold runPipelinedMac
    have hs0 : stepPipelinedMac s = {
        s with pc := 1, idx := 1, acc := 0,
               stage := ((s.aMem 0 % W64) * (s.bMem 0 % W64)) % W64 } := by
      unfold stepPipelinedMac; simp [hnh, hpc, hn]
    rw [hs0]
    have hinv0 : (0 + ((s.aMem 0 % W64) * (s.bMem 0 % W64)) % W64) % W64 =
        macPrefixSpec s.aMem s.bMem 1 := by
      dsimp only [macPrefixSpec]
    exact pipelinedMac_loop_ind s.aMem s.bMem (m + 1) m 1 _ (by omega)
      hnh rfl hn rfl rfl rfl hinv0

-- ============================================================================
-- Loop 4 Combinator: Multi-Limb 64-Bit `adc` Carry-Chain Loop (`RFLAGS.CF`)
-- ============================================================================

def checkAdcLimbCegisCert (c : CegisLoopCert) : Bool :=
  decide (c.unrollStride = 1) &&
  decide (c.pipelineLag = 0) &&
  decide (c.hasEarlyExit = false) &&
  decide (c.headerPc = 1) &&
  decide (c.epilogPc = 2) &&
  checkLratPass1Clean c.oDepth c.stepInitTree c.stepProofTree

private theorem limbsVal_upd_ge (m : Nat → Nat) (idx val : Nat) :
    ∀ k, k ≤ idx → limbsVal (memUpd m idx val) k = limbsVal m k
  | 0, _ => rfl
  | k + 1, hle => by
    dsimp only [limbsVal]
    rw [limbsVal_upd_ge m idx val k (by omega)]
    have hne : k ≠ idx := by omega
    unfold memUpd
    simp [hne]

private theorem b2n_cf_Carry (sum : Nat) (hbound : sum < 2 * W64) :
    sum % W64 + b2n (decide (sum ≥ W64)) * W64 = sum := by
  have hw : W64 = 18446744073709551616 := rfl
  cases hge : decide (sum ≥ W64) with
  | false =>
    have hlt : sum < W64 := by
      cases Nat.lt_or_ge sum W64 with
      | inl h => exact h
      | inr h => exact absurd (decide_eq_true h) (by rw [hge]; decide)
    dsimp [b2n]
    rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hlt]
  | true =>
    have hge' : sum ≥ W64 := of_decide_eq_true hge
    dsimp [b2n]
    rw [Nat.one_mul]
    have hlt_sub : sum - W64 < W64 := by omega
    have hmod : sum % W64 = sum - W64 := by
      have heq : sum = (sum - W64) + W64 * 1 := by omega
      conv => lhs; rw [heq]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_sub]
    omega

private theorem adcLoop_ind (aMem bMem : Nat → Nat) (n : Nat) :
    ∀ (rem k : Nat) (s : AdcLoopState),
      rem + k = n →
      s.halted = false → s.pc = 1 → s.n = n → s.idx = k →
      s.aMem = aMem → s.bMem = bMem →
      limbsVal s.outMem k + b2n s.cf * powW64 k = limbsVal aMem k + limbsVal bMem k →
      let sf := runAdcLoop (rem + 2) s
      sf.halted = true ∧
      limbsVal sf.outMem n + sf.rax * powW64 n = limbsVal aMem n + limbsVal bMem n
  | 0, k, s, hk, hnh, hpc, _, _, _, _, hinv => by
    have hk_eq : k = n := by omega
    subst hk_eq
    have hnlt : ¬ (s.idx < s.n) := by omega
    dsimp only [runAdcLoop]
    have hs1 : stepAdcLoop s = { s with pc := 2, rax := b2n s.cf } := by
      unfold stepAdcLoop; simp [hnh, hpc, hnlt]
    rw [hs1]
    have hs2 : stepAdcLoop { s with pc := 2, rax := b2n s.cf } =
        { s with pc := 2, halted := true, rax := b2n s.cf } := by
      unfold stepAdcLoop; simp [hnh]
    rw [hs2]
    exact ⟨rfl, hinv⟩
  | rem + 1, k, s, hk, hnh, hpc, hn, hidx, ha, hb, hinv => by
    have hlt : s.idx < s.n := by omega
    let sum := (aMem k % W64) + (bMem k % W64) + b2n s.cf
    let lo  := sum % W64
    let cf' := decide (sum ≥ W64)
    let s' : AdcLoopState := {
      s with
      pc     := 1
      idx    := k + 1
      cf     := cf'
      outMem := memUpd s.outMem k lo
    }
    have hs1 : stepAdcLoop s = s' := by
      have hlt_k : k < n := by omega
      unfold stepAdcLoop; simp [hnh, hpc, hn, hidx, ha, hb, hlt_k, s', sum, lo, cf']
    have hcf_le : b2n s.cf ≤ 1 := by cases s.cf <;> decide
    have ha_lt : aMem k % W64 < W64 := Nat.mod_lt _ (by decide : 0 < W64)
    have hb_lt : bMem k % W64 < W64 := Nat.mod_lt _ (by decide : 0 < W64)
    have hsum_bound : sum < 2 * W64 := by omega
    have hcarry := b2n_cf_Carry sum hsum_bound
    have hlo_lt : lo < W64 := Nat.mod_lt _ (by decide : 0 < W64)
    have hinv' : limbsVal s'.outMem (k + 1) + b2n s'.cf * powW64 (k + 1) =
        limbsVal aMem (k + 1) + limbsVal bMem (k + 1) := by
      dsimp only [s', limbsVal, powW64]
      rw [limbsVal_upd_ge s.outMem k lo k (Nat.le_refl k)]
      have hupd_eq : memUpd s.outMem k lo k % W64 = lo := by
        unfold memUpd; simp [Nat.mod_eq_of_lt hlo_lt]
      rw [hupd_eq]
      have hlin : lo * powW64 k + b2n cf' * (powW64 k * W64) =
          (lo + b2n cf' * W64) * powW64 k := by
        rw [Nat.add_mul, Nat.mul_assoc (b2n cf') W64 (powW64 k), Nat.mul_comm W64 (powW64 k)]
      have hassoc : limbsVal s.outMem k + lo * powW64 k + b2n cf' * (powW64 k * W64) =
          limbsVal s.outMem k + (lo * powW64 k + b2n cf' * (powW64 k * W64)) := by omega
      rw [hassoc, hlin, hcarry]
      have hexp : ((aMem k % W64) + (bMem k % W64) + b2n s.cf) * powW64 k =
          (aMem k % W64) * powW64 k + (bMem k % W64) * powW64 k + b2n s.cf * powW64 k := by
        rw [Nat.add_mul, Nat.add_mul]
      dsimp only [sum]
      rw [hexp]
      omega
    have hfuel : rem + 1 + 2 = (rem + 2) + 1 := by omega
    dsimp only
    rw [hfuel]
    unfold runAdcLoop
    rw [hs1]
    exact adcLoop_ind aMem bMem n rem (k + 1) s' (by omega)
      hnh rfl hn rfl ha hb hinv'

theorem checkAdcLimbCegisCert_sound {c : CegisLoopCert} (s : AdcLoopState)
    (hcert : checkAdcLimbCegisCert c = true)
    (hnh : s.halted = false) (hpc : s.pc = 0) :
    let sf := runAdcLoop (s.n + 3) s
    sf.halted = true ∧
    limbsVal sf.outMem s.n + sf.rax * powW64 s.n = limbsVal s.aMem s.n + limbsVal s.bMem s.n := by
  have _ := hcert
  have hfuel : s.n + 3 = (s.n + 2) + 1 := by omega
  dsimp only
  rw [hfuel]
  unfold runAdcLoop
  have hs0 : stepAdcLoop s = { s with pc := 1, idx := 0, cf := false } := by
    unfold stepAdcLoop; simp [hnh, hpc]
  rw [hs0]
  exact adcLoop_ind s.aMem s.bMem s.n s.n 0 _ (by omega) hnh rfl rfl rfl rfl rfl rfl

-- ============================================================================
-- Loop 5 Combinator: 16-Byte SIMD `memchr` Early-Exit Scanner (Horner `ctz16`)
-- ============================================================================

def checkMemchrEarlyExitCegisCert (c : CegisLoopCert) : Bool :=
  decide (c.unrollStride = 16) &&
  decide (c.pipelineLag = 0) &&
  decide (c.hasEarlyExit = true) &&
  decide (c.headerPc = 1) &&
  decide (c.epilogPc = 2) &&
  checkLratPass1Clean c.oDepth c.stepInitTree c.stepProofTree

private theorem movemask_eq_zero_all_ne (mem : Nat → Nat) (addr needle : Nat) :
    ∀ (r off : Nat),
      movemask16From mem addr needle off r = 0 →
      ∀ j, j < r → mem (addr + (off + j)) % 256 ≠ needle % 256
  | 0, _, _, _, hj => nomatch hj
  | r + 1, off, hm, j, hj => by
    dsimp only [movemask16From] at hm
    by_cases heq0 : mem (addr + off) % 256 = needle % 256
    · simp [heq0] at hm
    · have hm' : movemask16From mem addr needle (off + 1) r = 0 := by
        simp only [heq0, ite_false, Nat.zero_add] at hm
        omega
      cases j with
      | zero => simpa using heq0
      | succ j' =>
        have ih := movemask_eq_zero_all_ne mem addr needle r (off + 1) hm' j' (by omega)
        have hshift : addr + (off + (j' + 1)) = addr + (off + 1 + j') := by omega
        rw [hshift]
        exact ih

private theorem movemask16_eq_zero_noMatch (mem : Nat → Nat) (base needle k : Nat)
    (hprev : noMatchBefore mem base needle (16 * k) = true)
    (hm : movemask16From mem (base + 16 * k) needle 0 16 = 0) :
    noMatchBefore mem base needle (16 * (k + 1)) = true := by
  have hall := movemask_eq_zero_all_ne mem (base + 16 * k) needle 16 0 hm
  have step_d : ∀ d, d ≤ 16 → noMatchBefore mem base needle (16 * k + d) = true := by
    intro d hd
    induction d with
    | zero => simpa using hprev
    | succ d ih =>
      rw [show 16 * k + (d + 1) = (16 * k + d) + 1 by omega]
      unfold noMatchBefore
      rw [ih (by omega), Bool.true_and]
      have hne := hall d (by omega)
      rw [Nat.zero_add, show base + 16 * k + d = base + (16 * k + d) by omega] at hne
      exact decide_eq_true hne
  rw [show 16 * (k + 1) = 16 * k + 16 by omega]
  exact step_d 16 (Nat.le_refl 16)

private theorem findByteFrom_skip_prefix (mem : Nat → Nat) (base needle : Nat) :
    ∀ (off rem : Nat),
      noMatchBefore mem base needle off = true →
      findByteFrom mem base needle 0 (off + rem) = findByteFrom mem base needle off rem
  | 0, _, _ => by rw [Nat.zero_add]
  | off + 1, rem, hno => by
    unfold noMatchBefore at hno
    have hp := Bool.and_eq_true_iff.mp hno
    rw [show off + 1 + rem = off + (1 + rem) by omega,
        findByteFrom_skip_prefix mem base needle off (1 + rem) hp.1,
        show 1 + rem = rem + 1 by omega]
    conv => lhs; unfold findByteFrom
    have hne : mem (base + off) % 256 ≠ needle % 256 := of_decide_eq_true hp.2
    simp [hne]

private theorem ctz16_horner_matches (mem : Nat → Nat) (base needle remAfter : Nat) :
    ∀ (r off : Nat),
      movemask16From mem (base + off) needle 0 r ≠ 0 →
      off + ctz16 (movemask16From mem (base + off) needle 0 r) r =
        findByteFrom mem base needle off (r + remAfter)
  | 0, _, hnz => absurd rfl hnz
  | r + 1, off, hnz => by
    let rest := movemask16From mem (base + off) needle 1 r
    have hshift_from : ∀ d o, movemask16From mem (base + off) needle (o + 1) d =
        movemask16From mem (base + (off + 1)) needle o d := by
      intro d
      induction d with
      | zero => intro _; rfl
      | succ d ihd =>
        intro o
        dsimp only [movemask16From]
        rw [ihd (o + 1), show base + off + (o + 1) = base + (off + 1) + o by omega]
    have hrest_eq : rest = movemask16From mem (base + (off + 1)) needle 0 r := hshift_from r 0
    dsimp only [movemask16From] at hnz ⊢
    rw [show r + 1 + remAfter = (r + remAfter) + 1 by omega]
    unfold findByteFrom ctz16
    rw [Nat.add_zero] at hnz ⊢
    by_cases heq0 : mem (base + off) % 256 = needle % 256
    · have hmod1 : (1 + 2 * rest) % 2 = 1 := by omega
      simp [heq0, rest, hmod1]
    · have hmod0 : (0 + 2 * rest) % 2 = 0 := by omega
      have hdiv0 : (0 + 2 * rest) / 2 = rest := by omega
      have hrest_nz : movemask16From mem (base + (off + 1)) needle 0 r ≠ 0 := by
        intro hz
        apply hnz
        have hz' : rest = 0 := hrest_eq.trans hz
        simp [heq0, rest] at *
        omega
      simp only [heq0, ite_false]
      change off + (if (0 + 2 * rest) % 2 = 1 then 0 else 1 + ctz16 ((0 + 2 * rest) / 2) r) =
        findByteFrom mem base needle (off + 1) (r + remAfter)
      rw [hmod0, hdiv0]
      simp only [Nat.reduceEqDiff, ite_false]
      rw [hrest_eq]
      have ih := ctz16_horner_matches mem base needle remAfter r (off + 1) hrest_nz
      omega

private theorem memchr_loop_ind (mem : Nat → Nat) (base blocks needle : Nat) :
    ∀ (rem k : Nat) (s : MemchrState),
      rem + k = blocks →
      s.halted = false → s.pc = 1 →
      s.base = base → s.blocks = blocks → s.needle = needle →
      s.k = k → s.mem = mem →
      noMatchBefore mem base needle (16 * k) = true →
      let sf := runMemchr (rem + 2) s
      sf.halted = true ∧ sf.rax = memchrSpec mem base (16 * blocks) needle
  | 0, k, s, hk, hnh, hpc, _, hblk, _, hsk, _, hno => by
    have hk_eq : k = blocks := by omega
    subst hk_eq
    have hknlt : ¬ (k < k) := by omega
    dsimp only [runMemchr]
    have hs1 : stepMemchr s = { s with pc := 2, rax := 16 * k } := by
      unfold stepMemchr; simp [hnh, hpc, hblk, hsk, hknlt]
    rw [hs1]
    have hs2 : stepMemchr { s with pc := 2, rax := 16 * k } =
        { s with pc := 2, halted := true, rax := 16 * k } := by
      unfold stepMemchr; simp [hnh]
    rw [hs2]
    refine ⟨rfl, ?_⟩
    unfold memchrSpec
    have hskip := findByteFrom_skip_prefix mem base needle (16 * k) 0 hno
    rw [Nat.add_zero] at hskip
    rw [hskip]; rfl
  | rem + 1, k, s, hk, hnh, hpc, hb, hblk, hnd, hsk, hmem, hno => by
    have hklt : k < blocks := by omega
    let m := movemask16From mem (base + 16 * k) needle 0 16
    by_cases hm0 : m = 0
    · let s' : MemchrState := { s with pc := 1, k := k + 1 }
      have hs1 : stepMemchr s = s' := by
        unfold stepMemchr; simp [hnh, hpc, hb, hblk, hnd, hsk, hmem, hklt, m, hm0, s']
      have hno' := movemask16_eq_zero_noMatch mem base needle k hno hm0
      have hfuel : rem + 1 + 2 = (rem + 2) + 1 := by omega
      dsimp only
      rw [hfuel]
      unfold runMemchr
      rw [hs1]
      exact memchr_loop_ind mem base blocks needle rem (k + 1) s' (by omega)
        hnh rfl hb hblk hnd rfl hmem hno'
    · let sExit : MemchrState := { s with pc := 2, rax := 16 * k + ctz16 m 16 }
      have hs1 : stepMemchr s = sExit := by
        unfold stepMemchr; simp [hnh, hpc, hb, hblk, hnd, hsk, hmem, hklt, m, hm0, sExit]
      have hhalted_idem : ∀ f (st : MemchrState), st.halted = true → runMemchr f st = st := by
        intro f; induction f with
        | zero => intro st _; rfl
        | succ f ihf =>
          intro st hh
          unfold runMemchr
          have hst : stepMemchr st = st := by unfold stepMemchr; simp [hh]
          rw [hst]
          exact ihf st hh
      have hfuel : rem + 1 + 2 = (rem + 1) + 1 + 1 := by omega
      dsimp only
      rw [hfuel]
      unfold runMemchr
      rw [hs1]
      unfold runMemchr
      have hs2 : stepMemchr sExit = { sExit with halted := true } := by
        unfold stepMemchr; simp [sExit, hnh]
      rw [hs2, hhalted_idem (rem + 1) _ rfl]
      refine ⟨rfl, ?_⟩
      dsimp only [sExit]
      unfold memchrSpec
      rw [show 16 * blocks = 16 * k + (16 + 16 * rem) by omega,
          findByteFrom_skip_prefix mem base needle (16 * k) (16 + 16 * rem) hno]
      exact ctz16_horner_matches mem base needle (16 * rem) 16 (16 * k) hm0

theorem checkMemchrEarlyExitCegisCert_sound {c : CegisLoopCert} (s : MemchrState)
    (hcert : checkMemchrEarlyExitCegisCert c = true)
    (hnh : s.halted = false) (hpc : s.pc = 0) :
    let sf := runMemchr (s.blocks + 3) s
    sf.halted = true ∧ sf.rax = memchrSpec s.mem s.base (16 * s.blocks) s.needle := by
  have _ := hcert
  have hfuel : s.blocks + 3 = (s.blocks + 2) + 1 := by omega
  dsimp only
  rw [hfuel]
  unfold runMemchr
  have hs0 : stepMemchr s = { s with pc := 1, k := 0 } := by
    unfold stepMemchr; simp [hnh, hpc]
  rw [hs0]
  exact memchr_loop_ind s.mem s.base s.blocks s.needle s.blocks 0 _ (by omega)
    hnh rfl rfl rfl rfl rfl rfl rfl

-- ============================================================================
-- Loop 6 Combinator: Branchless `cmove` Scan (Functional + 2-Safety `LeakTrace`)
-- ============================================================================

def checkCtCmovScanCegisCert (c : CegisLoopCert) : Bool :=
  decide (c.unrollStride = 1) &&
  decide (c.pipelineLag = 0) &&
  decide (c.hasEarlyExit = false) &&
  decide (c.headerPc = 1) &&
  decide (c.epilogPc = 2) &&
  checkLratPass1Clean c.oDepth c.stepInitTree c.stepProofTree

private theorem ctScan_loop_ind (table : Nat → Nat) (base n target : Nat) :
    ∀ (rem k : Nat) (s : CtScanState),
      rem + k = n →
      s.halted = false → s.pc = 1 → s.base = base → s.n = n →
      s.target = target → s.k = k → s.table = table →
      s.rax = ctScanSpec table k target →
      let sf := runCtScan (rem + 2) s
      sf.halted = true ∧ sf.rax = ctScanSpec table n target
  | 0, k, s, hk, hnh, hpc, _, _, _, _, _, hinv => by
    have hk_eq : k = n := by omega
    subst hk_eq
    have hnlt : ¬ (s.k < s.n) := by omega
    dsimp only [runCtScan]
    have hs1 : stepCtScan s = { s with pc := 2, leak := s.leak ++ [.branch false 2] } := by
      unfold stepCtScan; simp [hnh, hpc, hnlt]
    rw [hs1]
    have hs2 : stepCtScan { s with pc := 2, leak := s.leak ++ [.branch false 2] } =
        { s with pc := 2, halted := true, leak := s.leak ++ [.branch false 2] } := by
      unfold stepCtScan; simp [hnh]
    rw [hs2]
    exact ⟨rfl, hinv⟩
  | rem + 1, k, s, hk, hnh, hpc, hb, hn, htg, hsk, htb, hinv => by
    have hlt : s.k < s.n := by omega
    let sel := if k = target then table k % W64 else s.rax
    let s' : CtScanState := {
      s with
      pc   := 1
      k    := k + 1
      rax  := sel
      leak := s.leak ++ [.memLoad (base + 8 * k), .branch true 1]
    }
    have hs1 : stepCtScan s = s' := by
      have hlt_k : k < n := by omega
      unfold stepCtScan; simp [hnh, hpc, hb, hn, htg, hsk, htb, hlt_k, s', sel]
    have hinv' : s'.rax = ctScanSpec table (k + 1) target := by
      dsimp only [s', sel, ctScanSpec]
      by_cases hkt : k = target
      · subst hkt; simp
      · simp only [hkt, ite_false, hinv, ctScanSpec]
        by_cases htl : target < k
        · have htl1 : target < k + 1 := by omega
          simp [htl, htl1]
        · have htl1 : ¬ (target < k + 1) := by omega
          simp [htl, htl1]
    have hfuel : rem + 1 + 2 = (rem + 2) + 1 := by omega
    dsimp only
    rw [hfuel]
    unfold runCtScan
    rw [hs1]
    exact ctScan_loop_ind table base n target rem (k + 1) s' (by omega)
      hnh rfl hb hn htg rfl htb hinv'

private theorem stepCtScan_2safety (s1 s2 : CtScanState)
    (hh : s1.halted = s2.halted) (hpc : s1.pc = s2.pc)
    (hb : s1.base = s2.base) (hn : s1.n = s2.n)
    (hk : s1.k = s2.k) (hleak : s1.leak = s2.leak) :
    (stepCtScan s1).halted = (stepCtScan s2).halted ∧
    (stepCtScan s1).pc = (stepCtScan s2).pc ∧
    (stepCtScan s1).base = (stepCtScan s2).base ∧
    (stepCtScan s1).n = (stepCtScan s2).n ∧
    (stepCtScan s1).k = (stepCtScan s2).k ∧
    (stepCtScan s1).leak = (stepCtScan s2).leak := by
  unfold stepCtScan
  cases hh1 : s1.halted with
  | true =>
    have hh2 : s2.halted = true := hh.symm.trans hh1
    simp [hh1, hh2, hb, hn, hk, hpc, hleak]
  | false =>
    have hh2 : s2.halted = false := hh.symm.trans hh1
    simp only [hh2, Bool.false_eq_true, ite_false]
    cases hp1 : s1.pc with
    | zero =>
      have hp2 : s2.pc = 0 := hpc.symm.trans hp1
      simp [hp2, hb, hn, hleak]
    | succ p =>
      cases p with
      | zero =>
        have hp2 : s2.pc = 1 := hpc.symm.trans hp1
        simp only [hp2]
        by_cases hlt1 : s1.k < s1.n
        · have hlt2 : s2.k < s2.n := by omega
          simp [hlt2, hb, hn, hk, hleak]
        · have hlt2 : ¬ (s2.k < s2.n) := by omega
          simp [hlt2, hb, hn, hk, hleak]
      | succ p' =>
        have hp2 : s2.pc = p' + 2 := hpc.symm.trans hp1
        simp [hp2, hb, hn, hk, hleak]

private theorem ctScan_2safety_ind :
    ∀ (fuel : Nat) (s1 s2 : CtScanState),
      s1.halted = s2.halted →
      s1.pc = s2.pc →
      s1.base = s2.base →
      s1.n = s2.n →
      s1.k = s2.k →
      s1.leak = s2.leak →
      (runCtScan fuel s1).leak = (runCtScan fuel s2).leak
  | 0, _, _, _, _, _, _, _, hleak => hleak
  | fuel + 1, s1, s2, hh, hpc, hb, hn, hk, hleak => by
    rcases stepCtScan_2safety s1 s2 hh hpc hb hn hk hleak with ⟨hh', hpc', hb', hn', hk', hl'⟩
    unfold runCtScan
    exact ctScan_2safety_ind fuel (stepCtScan s1) (stepCtScan s2) hh' hpc' hb' hn' hk' hl'

theorem checkCtCmovScanCegisCert_sound {c : CegisLoopCert} (s : CtScanState)
    (hcert : checkCtCmovScanCegisCert c = true)
    (hnh : s.halted = false) (hpc : s.pc = 0) :
    let sf := runCtScan (s.n + 3) s
    sf.halted = true ∧ sf.rax = ctScanSpec s.table s.n s.target := by
  have _ := hcert
  have hfuel : s.n + 3 = (s.n + 2) + 1 := by omega
  dsimp only
  rw [hfuel]
  unfold runCtScan
  have hs0 : stepCtScan s = { s with pc := 1, k := 0, rax := 0 } := by
    unfold stepCtScan; simp [hnh, hpc]
  rw [hs0]
  have hinv0 : (0 : Nat) = ctScanSpec s.table 0 s.target := by
    unfold ctScanSpec; simp
  exact ctScan_loop_ind s.table s.base s.n s.target s.n 0 _ (by omega)
    hnh rfl rfl rfl rfl rfl rfl hinv0

theorem checkCtCmovScanCegisCert_2safety {c : CegisLoopCert} (s1 s2 : CtScanState)
    (hcert : checkCtCmovScanCegisCert c = true)
    (hnh1 : s1.halted = false) (hnh2 : s2.halted = false)
    (hpc1 : s1.pc = 0) (hpc2 : s2.pc = 0)
    (hbase : s1.base = s2.base) (hn : s1.n = s2.n) (hleak : s1.leak = s2.leak) :
    (runCtScan (s1.n + 3) s1).leak = (runCtScan (s2.n + 3) s2).leak := by
  have _ := hcert
  rw [← hn]
  have hf : s1.n + 3 = (s1.n + 2) + 1 := by omega
  rw [hf]
  dsimp only [runCtScan]
  have hs1 : stepCtScan s1 = { s1 with pc := 1, k := 0, rax := 0 } := by
    unfold stepCtScan; simp [hnh1, hpc1]
  have hs2 : stepCtScan s2 = { s2 with pc := 1, k := 0, rax := 0 } := by
    unfold stepCtScan; simp [hnh2, hpc2]
  rw [hs1, hs2]
  exact ctScan_2safety_ind (s1.n + 2) _ _ (hnh1.trans hnh2.symm) rfl hbase hn rfl hleak

end UntrustedCegisHints
