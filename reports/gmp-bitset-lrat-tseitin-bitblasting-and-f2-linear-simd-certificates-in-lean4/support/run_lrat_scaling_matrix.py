#!/usr/bin/env python3
"""Comprehensive GMP Bitset vs. Trie / List / Array RUP-LRAT Scaling Benchmark (250..15,000 Steps).

Verifies:
1. `@Nat.rec` recursion elimination (`lcnf_unsafe_rec = 0` across all `ModuleData.constants`,
   satisfying strict Pass-1 `TrustedBoundary.validateRepoConstant` audits).
2. `by rfl` (`Meta.whnf`, 0 axioms `{}`) vs `by decide +kernel` (`Kernel.whnf`, `[propext]`).
3. Scaling across `250`, `1,000`, `5,000`, and `15,000` RUP steps for:
   - `gmp_db16_bitpaged` (16-bucket non-recursive GMP bit-paged clause DB, slot-recycled, u16 stream)
   - `gmp_oct3_recycled` (8-way `OctTrie` GMP bitset DB, slot-recycled, u16 stream)
   - `gmp_quad8_unrecycled` (4-way `QuadTrie` GMP bitset DB, monotonic IDs, u32 stream)
   - `trie_bool_depth15` (`Trie Bool` assignment + `Trie (List Nat)` clause DB)
   - `list_assoc` (`List` association clause & assignment DB)
   - `array_flat` (`Array` flat indexing at `numVars = 520` `maxRecDepth = 512` failure and
     `numVars = 500` symbolic bounds-proof blowup)
4. `.olean` certificate compactness: raw constructor AST (`StepTree LratStep`) vs GMP-packed streams.
"""
import json
import os
import re
import shutil
import subprocess
import tempfile

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
    matches = re.findall(r"TSTAT wall=([0-9.]+) user=([0-9.]+) sys=([0-9.]+) rss=(\d+)", stderr_txt)
    if not matches:
        return {}
    w, u, s, r = matches[-1]
    return {
        "wall_s": float(w),
        "user_s": float(u),
        "sys_s": float(s),
        "rss_mb": round(int(r) / 1024.0, 2),
    }


def lit_pos(v):
    return 2 * v


def lit_neg(v):
    return 2 * v + 1


def build_step_tree_expr(items, render_fn):
    if not items:
        return ".empty"
    if len(items) == 1:
        return f"(.leaf ({render_fn(items[0])}))"
    mid = len(items) // 2
    l = build_step_tree_expr(items[:mid], render_fn)
    r = build_step_tree_expr(items[mid:], render_fn)
    return f"(.branch {l} {r})"


def generate_rup_benchmark(num_rup_steps):
    """Realistic multi-hint RUP/LRAT derivation (~500 vars, 6-7 hints/step, sliding-window deletions)."""
    u = [1, 83, 167, 251, 337, 421]
    x = [430 + i for i in range(64)]
    s_vars = [10 + b for b in range(260) if (10 + b) not in u]

    init_clauses = []
    cid = 1
    init_clauses.append((cid, [lit_neg(u[0]), lit_pos(u[1])])); c1 = cid; cid += 1
    init_clauses.append((cid, [lit_neg(u[0]), lit_neg(u[1]), lit_pos(u[2])])); c2 = cid; cid += 1
    init_clauses.append((cid, [lit_neg(u[1]), lit_neg(u[2]), lit_pos(u[3])])); c3 = cid; cid += 1
    init_clauses.append((cid, [lit_neg(u[2]), lit_neg(u[3]), lit_pos(u[4])])); c4 = cid; cid += 1
    init_clauses.append((cid, [lit_neg(u[3]), lit_neg(u[4]), lit_pos(u[5])])); c5 = cid; cid += 1
    init_clauses.append((cid, [lit_neg(u[4]), lit_neg(u[5]), lit_pos(x[1])])); base_x1 = cid; cid += 1

    step_cids = {}
    for m in range(1, 63):
        init_clauses.append((cid, [lit_neg(u[4]), lit_neg(u[5]), lit_neg(x[m]), lit_pos(x[m + 1])]))
        step_cids[m] = cid
        cid += 1

    unit_u0 = cid; init_clauses.append((cid, [lit_pos(u[0])])); cid += 1
    unit_s_cid = cid; cid += 1
    neg_x_cid = cid; cid += 1

    steps = []
    rup_needed = num_rup_steps - 1
    b = 0
    m = 1
    prev_cid = None
    last_sb = None
    last_xm = None
    batch_cids = []
    old_batches = []

    for _ in range(rup_needed):
        sb = s_vars[b]
        xm = x[m]
        cls = [lit_neg(u[0]), lit_neg(sb), lit_pos(xm)]
        hints = [c1, c2, c3, c4, c5, base_x1] if m == 1 else [c1, c2, c3, c4, c5, prev_cid, step_cids[m - 1]]
        my_cid = cid
        cid += 1
        steps.append(("addRup", my_cid, cls, hints))
        batch_cids.append(my_cid)
        prev_cid = my_cid
        last_sb = sb
        last_xm = xm
        m += 1
        if m == 64:
            m = 1
            b += 1
            old_batches.append(batch_cids)
            batch_cids = []
            if len(old_batches) > 4:
                to_del = old_batches.pop(0)
                steps.append(("del", to_del))

    init_clauses.append((unit_s_cid, [lit_pos(last_sb)]))
    init_clauses.append((neg_x_cid, [lit_neg(last_xm)]))
    steps.append(("addEmpty", [unit_u0, unit_s_cid, prev_cid, neg_x_cid]))
    return init_clauses, steps, cid + 2, 500


def recycle_slots(init_clauses, steps):
    cid_to_slot = {}
    free_slots = []
    next_slot = 1

    def alloc_slot(cid):
        nonlocal next_slot
        if free_slots:
            s = free_slots.pop()
        else:
            s = next_slot
            next_slot += 1
        cid_to_slot[cid] = s
        return s

    new_init = [(alloc_slot(cid), cls) for cid, cls in init_clauses]
    new_steps = []
    for st in steps:
        if st[0] == "addRup":
            _, cid, cls, hints = st
            mapped_hints = [cid_to_slot[h] for h in hints]
            s = alloc_slot(cid)
            new_steps.append(("addRup", s, cls, mapped_hints))
        elif st[0] == "del":
            _, ids = st
            mapped_del = []
            for d in ids:
                if d in cid_to_slot:
                    s = cid_to_slot.pop(d)
                    free_slots.append(s)
                    mapped_del.append(s)
            if mapped_del:
                for j in range(0, len(mapped_del), 16):
                    new_steps.append(("del", mapped_del[j:j + 16]))
        elif st[0] == "addEmpty":
            _, hints = st
            new_steps.append(("addEmpty", [cid_to_slot[h] for h in hints]))
    return new_init, new_steps, next_slot - 1


def pack_u16(words):
    val = 0
    for i, w in enumerate(words):
        assert 0 <= w < 65536, w
        val |= (w << (16 * i))
    return hex(val)


def pack_steps_u16(steps_slice):
    words = []
    for st in steps_slice:
        if st[0] == "addRup":
            _, cid, cls, hints = st
            words.extend([1, cid, len(cls), len(hints)] + cls + hints)
        elif st[0] == "del":
            _, ids = st
            words.extend([2, len(ids)] + ids)
        elif st[0] == "addEmpty":
            _, hints = st
            words.extend([3, len(hints)] + hints)
    words.append(0)
    return pack_u16(words)


def pack_init_u16(init_slice):
    words = []
    for cid, cls in init_slice:
        words.extend([cid, len(cls)] + cls)
    words.append(0)
    return pack_u16(words)


def render_raw_init(item):
    cid, cls = item
    cls_s = "[" + ", ".join(str(x) for x in cls) + "]"
    return f"({cid}, {cls_s})"


def render_raw_step(st):
    if st[0] == "addRup":
        _, cid, cls, hints = st
        cls_s = "[" + ", ".join(str(x) for x in cls) + "]"
        h_s = "[" + ", ".join(str(x) for x in hints) + "]"
        return f"LratStep.addRup {cid} {cls_s} {h_s}"
    if st[0] == "del":
        _, ids = st
        d_s = "[" + ", ".join(str(x) for x in ids) + "]"
        return f"LratStep.del {d_s}"
    _, hints = st
    h_s = "[" + ", ".join(str(x) for x in hints) + "]"
    return f"LratStep.addEmpty {h_s}"


# 100% `_unsafe_rec`-free Pass-1 GMP LRAT checkers (`OctTrie` + 16-bucket bit-paged `GmpDb16`)
# using direct `@Nat.rec` strictly within the 51-module `foundation-lock.json` `Init.*` subset!
PASS1_ZERO_UNSAFE_REC_LEAN = r"""prelude
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
"""


def main():
    lrat_bench_path = os.path.join(HERE, "LratBench.lean")
    with open(lrat_bench_path) as f:
        legacy_core = f.read()

    with tempfile.TemporaryDirectory() as tmp:
        with open(os.path.join(tmp, "Pass1GmpLrat.lean"), "w") as f:
            f.write(PASS1_ZERO_UNSAFE_REC_LEAN)
        with open(os.path.join(tmp, "LratBench.lean"), "w") as f:
            f.write(legacy_core)

        for mod in ["Pass1GmpLrat", "LratBench"]:
            r = subprocess.run(
                [LEAN_RUN, "--mode", "file", "--", LEAN_BIN, "-DElab.async=false", "-Ddebug.skipKernelTC=false",
                 "-o", f"{mod}.olean", f"{mod}.lean"],
                cwd=tmp, capture_output=True, text=True
            )
            assert r.returncode == 0, f"{mod} failed:\n" + r.stdout + r.stderr

        replay_driver = rf"""import Lean
import Lean.Replay
open Lean

partial def collectTransitiveAxioms (env : Environment) (root : Name) : IO (List Name) := do
  let mut queue : List Name := [root]
  let mut visited : NameSet := {{}}
  let mut axioms : NameSet := {{}}
  while !queue.isEmpty do
    let n := queue.head!
    queue := queue.tail!
    if !visited.contains n then
      visited := visited.insert n
      let some ci := env.find? n | throw <| IO.userError s!"missing {{n}}"
      if ci.isUnsafe || ci.isPartial then
        throw <| IO.userError s!"FORBIDDEN unsafe/partial in cone: {{n}}"
      if ci.isAxiom then
        axioms := axioms.insert n
      let mut used := ci.type.getUsedConstants.toList
      if let some v := ci.value? (allowOpaque := true) then
        let vs := v.getUsedConstants
        if vs.contains `_inhabitedExprDummy then
          throw <| IO.userError s!"DUMMY body in {{n}}"
        used := used ++ vs.toList
      queue := used ++ queue
  return axioms.toList

unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (System.FilePath.mk "{TC_DIR}") [System.FilePath.mk "."]
  let _ := args[0]!.toName
  let targetMod := args[1]!.toName
  let strictZeroUnsafe := args[2]! == "strict"
  let t0 ← IO.monoMsNow
  let fullEnv ← importModules #[{{ module := targetMod }}] {{}} (trustLevel := 0) (loadExts := false) (level := .private)
  let fullEnv := fullEnv.setExporting false
  let some modIdx := fullEnv.header.moduleNames.idxOf? targetMod | throw <| IO.userError "missing targetMod"
  let modData := fullEnv.header.moduleData[modIdx]!
  let baseEnv ← importModules modData.imports {{}} (trustLevel := 0) (loadExts := false) (level := .private)
  let baseEnv := baseEnv.setExporting false
  let mut newConsts : Std.HashMap Name ConstantInfo := {{}}
  let mut unsafeCount := 0
  for ci in modData.constants do
    if ci.isUnsafe || ci.isPartial then
      if strictZeroUnsafe || !ci.name.toString.endsWith "._unsafe_rec" then
        throw <| IO.userError s!"STRICT/FORBIDDEN unsafe/partial: {{ci.name}}"
      unsafeCount := unsafeCount + 1
    else
      let some stored := fullEnv.find? ci.name | throw <| IO.userError s!"missing {{ci.name}}"
      newConsts := newConsts.insert ci.name stored
  let t1 ← IO.monoMsNow
  let _ ← (baseEnv.toKernelEnv.replay newConsts).toIO (fun e => IO.userError s!"Replay failed: {{e}}")
  let t2 ← IO.monoMsNow
  let mut axs : List Name := []
  if fullEnv.contains `BenchRun.cert_valid then
    axs ← collectTransitiveAxioms fullEnv `BenchRun.cert_valid
  IO.println ("REPLAY_JSON {{\"import_ms\": " ++ toString (t1 - t0) ++
    ", \"replay_ms\": " ++ toString (t2 - t1) ++
    ", \"kernel_consts\": " ++ toString newConsts.size ++
    ", \"lcnf_unsafe_rec\": " ++ toString unsafeCount ++
    ", \"axioms\": \"" ++ toString axs ++ "\"}}")
"""
        with open(os.path.join(tmp, "ReplayOne.lean"), "w") as f:
            f.write(replay_driver)

        env = os.environ.copy()
        env["LEAN_PATH"] = tmp

        # Verify BOTH Pass1GmpLrat (strict: 0 `_unsafe_rec`) and LratBench (equation-compiled: >0 `_unsafe_rec`)!
        rp0 = subprocess.run(
            [LEAN_RUN, "--mode", "file", "--", LEAN_BIN, "--run", "ReplayOne.lean", "Init.Tactics", "Pass1GmpLrat", "strict"],
            cwd=tmp, env=env, capture_output=True, text=True
        )
        assert rp0.returncode == 0, "Pass1GmpLrat strict audit failed:\n" + rp0.stdout + rp0.stderr
        pass1_lib_audit = json.loads(rp0.stdout.split("REPLAY_JSON ")[1].splitlines()[0])
        pass1_lib_audit["olean_bytes"] = os.path.getsize(os.path.join(tmp, "Pass1GmpLrat.olean"))

        rp_legacy = subprocess.run(
            [LEAN_RUN, "--mode", "file", "--", LEAN_BIN, "--run", "ReplayOne.lean", "Init.Tactics", "LratBench", "normal"],
            cwd=tmp, env=env, capture_output=True, text=True
        )
        assert rp_legacy.returncode == 0, "LratBench audit failed:\n" + rp_legacy.stdout + rp_legacy.stderr
        legacy_lib_audit = json.loads(rp_legacy.stdout.split("REPLAY_JSON ")[1].splitlines()[0])
        legacy_lib_audit["olean_bytes"] = os.path.getsize(os.path.join(tmp, "LratBench.olean"))
        print(f"[Library Audit] Pass1GmpLrat={pass1_lib_audit} | LratBench={legacy_lib_audit}", flush=True)

        def pack_words_u32(words):
            val = 0
            for i, w in enumerate(words):
                val |= (w << (32 * i))
            return hex(val)

        def pack_steps_u32(steps_slice):
            words = []
            for st in steps_slice:
                if st[0] == "addRup":
                    _, cid, cls, hints = st
                    words.extend([1, cid, len(cls), len(hints)] + cls + hints)
                elif st[0] == "del":
                    _, ids = st
                    words.extend([2, len(ids)] + ids)
                elif st[0] == "addEmpty":
                    _, hints = st
                    words.extend([3, len(hints)] + hints)
            words.append(0)
            return pack_words_u32(words)

        def pack_init_u32(init_slice):
            words = []
            for cid, cls in init_slice:
                words.extend([cid, len(cls)] + cls)
            words.append(0)
            return pack_words_u32(words)

        def run_bench_case(label, base_mod, mod_name, src, strict=False, timeout_s=180):
            lp = os.path.join(tmp, f"{mod_name}.lean")
            op = os.path.join(tmp, f"{mod_name}.olean")
            with open(lp, "w") as f:
                f.write(src)
            src_bytes = os.path.getsize(lp)
            try:
                res = subprocess.run(
                    [LEAN_RUN, "--mode", "file", "--", "/usr/bin/time", "-f", "TSTAT wall=%e user=%U sys=%S rss=%M",
                     LEAN_BIN, "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-o", op, lp],
                    cwd=tmp, env=env, capture_output=True, text=True, timeout=timeout_s
                )
            except subprocess.TimeoutExpired:
                return {"label": label, "status": f"TIMEOUT_GT_{timeout_s}S", "source_bytes": src_bytes}

            tstat = parse_tstat(res.stderr)
            if res.returncode != 0:
                diag = "\n".join((res.stdout + res.stderr).strip().splitlines()[:4])
                return {"label": label, "status": "FAIL", "source_bytes": src_bytes, "compile": tstat, "diagnostic": diag}

            sz = os.path.getsize(op)
            rep = subprocess.run(
                [LEAN_RUN, "--mode", "file", "--", "/usr/bin/time", "-f", "TSTAT wall=%e user=%U sys=%S rss=%M",
                 LEAN_BIN, "--run", "ReplayOne.lean", base_mod, mod_name, "strict" if strict else "normal"],
                cwd=tmp, env=env, capture_output=True, text=True, timeout=timeout_s
            )
            assert rep.returncode == 0, rep.stdout + rep.stderr
            rj = json.loads(rep.stdout.split("REPLAY_JSON ")[1].splitlines()[0])
            rj["process_tstat"] = parse_tstat(rep.stderr)
            return {
                "label": label,
                "status": "OK",
                "source_bytes": src_bytes,
                "compile": tstat,
                "olean_bytes": sz,
                "replay": rj,
            }

        results = {
            "pass1_gmp_lrat_library_strict_audit": pass1_lib_audit,
            "legacy_lrat_bench_library_audit": legacy_lib_audit,
            "rfl_vs_decide_kernel": [],
            "olean_ast_vs_gmp_stream": [],
            "scaling_matrix_250_to_15000": [],
            "array_boundary_probes": [],
        }

        # Part A: `by rfl` (`Meta.whnf`, 0 axioms `{}`) vs `by decide +kernel` (`Kernel.whnf`, `[propext]`)
        for n in [250, 500, 750, 1000, 1500, 2000]:
            ic_raw, st_raw, _, _ = generate_rup_benchmark(n)
            ic, st, max_slot = recycle_slots(ic_raw, st_raw)
            ic_tree = build_step_tree_expr([pack_init_u16(ic[i:i+8]) for i in range(0, len(ic), 8)], lambda h: h)
            st_tree = build_step_tree_expr([pack_steps_u16(st[i:i+8]) for i in range(0, len(st), 8)], lambda h: h)
            src_rfl = f"prelude\nimport Pass1GmpLrat\nnamespace BenchRun\nopen Pass1GmpLrat\ntheorem cert_valid : checkLratPass1Clean 4 ({ic_tree}) ({st_tree}) = true := rfl\nend BenchRun\n"
            r = run_bench_case(f"gmp_oct3_rfl_{n}", "Pass1GmpLrat", f"M_rfl_{n}", src_rfl, strict=True, timeout_s=60)
            r["n_steps"] = n
            r["max_recycled_slot"] = max_slot
            results["rfl_vs_decide_kernel"].append(r)
            print(f"[rfl N={n}] -> {r['status']} {r.get('compile', {})}", flush=True)
            if r["status"] != "OK":
                break

        # Part A2: Raw constructor AST (`StepTree LratStep`) `.olean` vs GMP-packed stream `.olean` (N=250, 1000)
        for n in [250, 1000]:
            ic_raw, st_raw, _, _ = generate_rup_benchmark(n)
            ic_ast = build_step_tree_expr(ic_raw, render_raw_init)
            st_ast = build_step_tree_expr(st_raw, render_raw_step)
            src_ast = f"prelude\nimport LratBench\nnamespace BenchRun\nopen LratBench\ntheorem cert_valid : checkLratGmp 8 18 ({ic_ast}) ({st_ast}) = true := by decide +kernel\nend BenchRun\n"
            r_ast = run_bench_case(f"gmp_quad8_raw_ast_{n}", "LratBench", f"M_ast_{n}", src_ast, strict=False, timeout_s=60)
            r_ast["n_steps"] = n
            results["olean_ast_vs_gmp_stream"].append(r_ast)
            print(f"[raw_ast N={n}] -> {r_ast['status']} src={r_ast['source_bytes']}B olean={r_ast.get('olean_bytes')}B {r_ast.get('compile', {})}", flush=True)

        # Part B: Full 250, 1,000, 5,000, 15,000 scaling matrix across checker architectures!
        skip_kinds = set()
        for n in [250, 1000, 5000, 15000]:
            ic_raw, st_raw, max_cid, _ = generate_rup_benchmark(n)
            ic_rec, st_rec, max_slot = recycle_slots(ic_raw, st_raw)

            # 8 steps per leaf for u16 stream trees
            ic16_8 = build_step_tree_expr([pack_init_u16(ic_rec[i:i+8]) for i in range(0, len(ic_rec), 8)], lambda h: h)
            st16_8 = build_step_tree_expr([pack_steps_u16(st_rec[i:i+8]) for i in range(0, len(st_rec), 8)], lambda h: h)

            # 1. `gmp_db16_bitpaged` (`GmpDb16` 16-bucket non-recursive bit-paged GMP DB, `lcnf_unsafe_rec = 0`!)
            if "gmp_db16_bitpaged" in skip_kinds:
                results["scaling_matrix_250_to_15000"].append({
                    "checker": "gmp_db16_bitpaged", "n_steps": n, "status": "SKIPPED_AFTER_PRIOR_TIMEOUT_OR_GT_45S"
                })
            else:
                src_db16 = f"prelude\nimport Pass1GmpLrat\nnamespace BenchRun\nopen Pass1GmpLrat\ntheorem cert_valid : checkLratGmp16Clean 1024 16 ({ic16_8}) ({st16_8}) = true := by decide +kernel\nend BenchRun\n"
                r_db16 = run_bench_case(f"gmp_db16_bitpaged_{n}", "Pass1GmpLrat", f"M_db16_{n}", src_db16, strict=True, timeout_s=90)
                r_db16.update({"checker": "gmp_db16_bitpaged", "n_steps": n, "max_slot": max_slot})
                results["scaling_matrix_250_to_15000"].append(r_db16)
                print(f"[gmp_db16 N={n}] -> {r_db16['status']} {r_db16.get('compile', {})} olean={r_db16.get('olean_bytes')}B replay_ms={r_db16.get('replay', {}).get('replay_ms')}", flush=True)
                if r_db16["status"] != "OK" or r_db16["compile"]["wall_s"] > 45.0:
                    skip_kinds.add("gmp_db16_bitpaged")

            # 2. `gmp_oct3_recycled` (`OctTrie` depth 3, Peano-free 3-bit Bool dispatch, slot-recycled, u16 GMP stream, `lcnf_unsafe_rec = 0`!)
            src_oct3 = f"prelude\nimport Pass1GmpLrat\nnamespace BenchRun\nopen Pass1GmpLrat\ntheorem cert_valid : checkLratPass1Clean 4 ({ic16_8}) ({st16_8}) = true := by decide +kernel\nend BenchRun\n"
            r_oct3 = run_bench_case(f"gmp_oct3_recycled_{n}", "Pass1GmpLrat", f"M_oct3_{n}", src_oct3, strict=True, timeout_s=180)
            r_oct3.update({"checker": "gmp_oct3_recycled", "n_steps": n, "max_slot": max_slot})
            results["scaling_matrix_250_to_15000"].append(r_oct3)
            print(f"[gmp_oct3 N={n}] -> {r_oct3['status']} {r_oct3.get('compile', {})} olean={r_oct3.get('olean_bytes')}B replay_ms={r_oct3.get('replay', {}).get('replay_ms')}", flush=True)

            # Prepare u32 tree for unrecycled QuadTrie / Trie Bool / List (8 steps per leaf)
            ic32 = build_step_tree_expr([pack_init_u32(ic_raw[i:i+8]) for i in range(0, len(ic_raw), 8)], lambda h: h)
            st32 = build_step_tree_expr([pack_steps_u32(st_raw[i:i+8]) for i in range(0, len(st_raw), 8)], lambda h: h)

            other_specs = [
                ("gmp_quad8_unrecycled", f"checkLratGmpStream 8 18 ({ic32}) ({st32})", 75),
                ("trie_bool_depth15", f"checkLratTrie 15 18 (decodePackedInit 12 ({ic32})) (decodePackedTree 14 ({st32}))", 60),
                ("list_assoc", f"checkLratList 18 (decodePackedInit 12 ({ic32})) (decodePackedTree 14 ({st32}))", 60),
            ]
            for kind, expr, tmo in other_specs:
                if kind in skip_kinds:
                    results["scaling_matrix_250_to_15000"].append({
                        "checker": kind, "n_steps": n, "status": "SKIPPED_AFTER_PRIOR_TIMEOUT_OR_GT_45S"
                    })
                    continue
                src_k = f"prelude\nimport LratBench\nnamespace BenchRun\nopen LratBench\ntheorem cert_valid : {expr} = true := by decide +kernel\nend BenchRun\n"
                rk = run_bench_case(f"{kind}_{n}", "LratBench", f"M_{kind}_{n}", src_k, strict=False, timeout_s=tmo)
                rk.update({"checker": kind, "n_steps": n})
                results["scaling_matrix_250_to_15000"].append(rk)
                print(f"[{kind} N={n}] -> {rk['status']} {rk.get('compile', {})}", flush=True)
                if rk["status"] != "OK" or rk["compile"]["wall_s"] > 45.0:
                    skip_kinds.add(kind)

        # Part C: Array checker probes (`maxRecDepth = 512` crash at `numVars = 520` AND symbolic bounds blowup at `numVars = 500`, N=25 raw AST)
        ic25, st25, mcid25, _ = generate_rup_benchmark(25)
        ic_ast25 = build_step_tree_expr(ic25, render_raw_init)
        st_ast25 = build_step_tree_expr(st25, render_raw_step)
        for nvars in [520, 500]:
            src_arr = f"prelude\nimport LratBench\nnamespace BenchRun\nopen LratBench\ntheorem cert_valid : checkLratArray {mcid25} {nvars} 10 ({ic_ast25}) ({st_ast25}) = true := by decide +kernel\nend BenchRun\n"
            ra = run_bench_case(f"array_nvars_{nvars}_25", "LratBench", f"M_arr_{nvars}", src_arr, strict=False, timeout_s=30)
            ra.update({"checker": "array_flat", "n_steps": 25, "num_vars": nvars})
            results["array_boundary_probes"].append(ra)
            print(f"[array nvars={nvars} N=25] -> {ra['status']} {ra.get('diagnostic', '')[:160]}", flush=True)

        with open(os.path.join(HERE, "lrat_scaling_results.json"), "w") as f:
            json.dump(results, f, indent=2)
        shutil.copyfile(os.path.join(tmp, "Pass1GmpLrat.lean"), os.path.join(HERE, "Pass1GmpLrat.lean"))
        print("Saved lrat_scaling_results.json and Pass1GmpLrat.lean")


if __name__ == "__main__":
    main()
