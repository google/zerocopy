# Branch relaxation fixpoints and unwind-table frame restoration in Lean toy models

## Summary

This package contains 20 kernel-checked results about two small Lean 4 models: `Toy.Relax`, a toy model of span-dependent branch encoding ("branch relaxation") in an assembler, and `Toy.Unwind`, a toy model of DWARF-CFI-style unwind tables for one straight-line function body. All results are proved in core Lean `v4.34.1` without Mathlib; no result is a claim about a real assembler, linker, compiler or unwinder (every such connection is a separately labeled `derived (modeling bridge)` statement under **Findings**). Model–system relation: none proved. These are statements about the toy models; they neither establish nor refute the corresponding claims about real assemblers and linkers (such as LLVM's MC layer or CompCert's `Branch_relaxation` module), compiler-emitted DWARF call frame information or real unwinders.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

The non-claims of every result are listed first under **Boundaries**; read them before relying on a result. One sentence per result (identifiers `R1a`–`R7b` are local to this report):

**Grow-only relaxation (`Toy.Relax`; all branches decided simultaneously from one layout, a short branch is promoted when out of reach, nothing is ever demoted).**

- **R1a** — For every program, encoding parameters and start assignment, the grow-only relaxation loop stops within `numBranches p + 1` passes and returns `relax prm p a`, the `numBranches p`-fold iterate of the grow-only step; no hypothesis on sizes or alignment.
- **R1b** — For every program, parameters and start `a`, the grow-only result `relax prm p a` is valid (every short branch reaches its target) and pointwise above `a`; no hypothesis on sizes or alignment.
- **R1c** — If every branch distance is monotone in the assignment (`DistMonotone`), then `relax prm p a` lies below every valid assignment `b` with `a ≤ b`, so it is the least valid assignment above `a`; the order compares every index `i : Nat`, including positions that hold no branch.
- **R1d** — The `numBranches + 1` pass bound of R1a is attained: on `[fixed 2, branch 0, branch 1]` (short 1, long 2, reach 1) the loop with `numBranches = 2` passes from all-short returns `none`, although the 2-fold iterate is already valid.
- **R2a** — The distance between the starts of instructions `i` and `t` depends only on the sizes of the instructions in `[min i t, max i t)` and is monotone in those sizes.
- **R2b** — If every instruction size is monotone in the assignment (`SizesMonotone`), every branch distance is monotone in the assignment (`DistMonotone`).
- **R2c** — A program without alignment directives, under parameters with `shortSize ≤ longSize`, has every instruction size monotone in the assignment.
- **R2e** — With an alignment directive (and `shortSize ≤ longSize`), leastness fails while termination and validity still hold: on `[branch 1, align 4, branch 1]` (short 1, long 2, reach 2) relaxation from all-short stops at a valid assignment that promotes branch 2, yet promoting only branch 0 is also valid and the relaxation result is not below it.
- **R4a** — If `DistMonotone` holds and `shortSize ≤ longSize`, the grow-only result from all-short has the minimum total size among all valid assignments (alignment directives are allowed as long as `DistMonotone` holds).
- **R4b** — With alignment padding inside a branch span (and `shortSize ≤ longSize`), the grow-only fixpoint from all-short need not have minimum total size: on `[branch 1, align 4, branch 1]` it has total size 6, while a valid assignment of total size 5 exists.
- **R5** — If assignment `a` is valid, position `j` is promoted and grow-only relaxation is re-run to obtain `r = relax prm p (promote a j)`, and every instruction has positive size in both layouts `a` and `r`, then in each layout every branch has an encodable displacement, recomputed from that layout, that lands exactly on its target index (`min t p.length`).

**Grow-and-shrink relaxation (`stepGS`; long branches may be demoted).** Here each branch `i` is re-decided from the **counterfactual layout** `setShort a i`, in which branch `i` itself is tentatively short and every other position is as in `a`: branch `i` becomes long iff that short encoding would be out of reach. This is a different procedure from reading every distance in the current layout `a`; that current-layout reading is modeled only as the contrast definition `stepGSCurrent`, about which no general result is stated.

- **R3a** — Grow-and-shrink relaxation `stepGS` can oscillate forever even with monotone sizes when started from a non-bottom assignment: on `[fixed 1, branch 3, branch 0]` (short 1, long 2, reach 2), started from "branch 1 long", it alternates forever between two assignments.
- **R3b** — If `DistMonotone` holds, every iterate of `stepGS` started from all-short equals the corresponding grow-only iterate, so from all-short it never demotes and its `numBranches`-th iterate is `relax prm p allShort`.
- **R3c** — Without `DistMonotone`, `stepGS` can oscillate forever from all-short: on `[branch 2, branch 3, align 4]` (short 1, long 2, reach 2; the alignment directive breaks `DistMonotone`) it cycles with period 4 and never reaches a fixpoint, and on `[fixed 2, branch 3, branch 0]` with short 2, long 1, reach 3 (no alignment, but `shortSize > longSize`) it alternates forever. The aligned 4-cycle depends on the counterfactual `setShort` reading: the contrast step `stepGSCurrent` reaches a valid fixpoint on that program after 3 steps, whereas the inverted-size 2-cycle persists under `stepGSCurrent`.

**Unwind tables (`Toy.Unwind`; single-frame virtual unwinding of a straight-line body, quantified over every entry state).**

- **R6a** — If the abstract interpretation that generates a table assigns no caller-visible register the rule `undefined` at any offset, the generated table is correct: at every offset it recovers the caller's stack pointer (the CFA) and the entry values of the caller-visible registers, for every entry state.
- **R6b** — For the body `[push 3, setReg 3 0]`, the tables that place the post-push CFA row one instruction late or one instruction early are both incorrect, for every entry state.
- **R6c** — For the body `[push 3, setReg 3 0, pop 3]`, the table that keeps the pre-pop row after the pop is incorrect: its CFA is one word above the caller's stack pointer, for every entry state.
- **R6d** — For the body `[push 3, setReg 3 0, pop 3, push 4]`, a table that updates the CFA after the pop but keeps register 3's stale `savedAt` rule is incorrect after the later push overwrites the freed slot; without the later push the same stale rule gives a correct table.
- **R7a** — If the decidable checker `checkTable`, which replays the abstract interpretation, accepts a table, the table is correct (`TableCorrect`).
- **R7b** — Every correct table is accepted by `checkTable`; for this straight-line toy language the abstract interpretation is exact, so with R7a the checker decides `TableCorrect`.

## Applicability

### What the results apply to

Every theorem in this package is a statement about the Lean definitions in `lean/ToyRelax/`; these theorems neither establish nor refute the corresponding claims about real assemblers, linkers, compiler-emitted call frame information or unwinders. The definitions are toy models chosen to isolate two questions; they are not production definitions and they mirror no particular implementation. All Lean sources are part of this package; no other package or external Lean library is needed.

**Relaxation model (`lean/ToyRelax/Relax/Model.lean`, namespace `Toy.Relax`).** A toy model of span-dependent branch encoding in an assembler.

* A program is a `List Instr` with `Instr := fixed (size) | branch (target : Nat) | align (k)`. Branch targets are instruction **indices**; any index `≥ length` denotes the end of the program (addresses are clamped there). `align k` pads to the next multiple of `k`: `padTo k addr = if k = 0 then 0 else (k - addr % k) % k`.
* `Params := {shortSize, longSize, reach}`. A short branch reaches its target iff `dist ≤ reach`. A long branch always reaches (there is no long-form limit).
* An assignment `Asg := Nat → Bool` (`true` = long). The layout reads it only at branch positions, but `step`, `stepGS` and `relax` carry the values at all other indices along unchanged, and the order `Asg.Le a b := ∀ i, a i = true → b i = true` compares **every** index `i : Nat`. `Asg.LeOnBranches p` is the order restricted to branch positions of `p`.
* Addresses are prefix sums: `addr 0 = 0` and `addr (k+1) = addr k + size k`, where `size k = instrSize (addr k) (a k) p[k]` (0 past the end). Displacement convention: `dist i t = |addr t − addr i|` (start of branch to start of target), so a forward branch's own size lies in its span.
* Grow-only relaxation updates **all branches simultaneously** from one layout (Jacobi style). `step a i = a i || outOfReach a i`, `relax a = iter step (numBranches p) a`, and `relaxLoop` is the pass-bounded loop that stops when a pass would change nothing.
* Grow-and-shrink relaxation `stepGS` re-decides every branch `i` from the **counterfactual layout** `setShort a i`, in which branch `i` itself is tentatively short and every other position is as in `a`: branch `i` becomes long iff that short encoding would be out of reach. Reading the distance from the current layout `a` instead is a different procedure (on a forward long branch its own long size lies in its span); see `stepGS_decides_from_counterfactual_layout`. That procedure appears only as the contrast definition `stepGSCurrent`, which no main result is about: on the instance of R3a and on the aligned instance of R3c it stops at a valid fixpoint (`osc_stepGSCurrent_reaches_valid_fixpoint`, `alignOsc_stepGSCurrent_reaches_valid_fixpoint`), while on the inverted-size instance of R3c it still oscillates (`invOsc_stepGSCurrent_two_cycle`).
* `emitDisp prm p a i` is the displacement an assembler can encode for position `i`: `some (addr t − addr i)` if `i` holds a branch to `t` that is long, or short and within reach; `none` otherwise. `disp` is the unbounded difference without the reach check.
* **Known gaps:** no relocations, linker relaxation, sections, symbols with offsets, more than two encodings per branch, finite long-branch reach, or per-branch reach. Sequential (Gauss–Seidel style) passes, such as the in-place pass of LLVM's `MCAssembler::relaxOnce`, are not modeled (a support check in `lean/Search/Sequential.lean` shows that a sequential pass can stop at a different valid assignment). The end-of-instruction displacement convention used by x86 is not modeled. Relaxation of non-branch fragments (LEB128 values, CFI advance deltas) is not modeled.

**Unwind model (`lean/ToyRelax/Unwind/Model.lean`, namespace `Toy.Unwind`).** A toy model of DWARF-CFI-style unwind tables for one straight-line function body.

* `Op := push r | subSp n | saveAt r off | pop r | addSp n | setReg r v`. `setReg` stands for any computation that clobbers a register; without it, saving a register would never be necessary.
* The machine state is `MState := {sp : Int, regs : Nat → Int, mem : Int → Int}` (unbounded integers). The stack grows downward and one push moves `sp` by one word.
* A `Row` is `{cfa : Int, rule : Nat → RegRule}`, meaning `CFA = sp + cfa`. A register rule is `savedAt off` (the value is at `CFA − off`), `sameValue`, or `undefined`. Sign conventions: `Op.saveAt r off` stores at `sp + off`; `RegRule.savedAt off` reads at `CFA − off`; DWARF `offset(N)` reads at `CFA + N`, so `savedAt off` corresponds to `offset(−off)`. A `Table` is `Nat → Row`, one materialized row per operation offset (offset `i` is the point after the first `i` operations), not a CIE/FDE instruction stream.
* The CFA is the entry `sp`, which is also the caller's `sp` after return. The toy has no return-address slot.
* `TableCorrect` is **single-frame virtual unwinding**: it quantifies over every entry state (including unaligned `sp` and arbitrary memory) and requires each row to recover the caller's `sp` and the entry values of the caller-visible registers. It does not forbid writes into the caller's frame and does not require the body to restore `sp` or registers by its end (`tableCorrect_permits_caller_frame_write`, `tableCorrect_permits_unrestored_sp`).
* **Known gaps:** no frame-pointer-based CFA, no register-to-register saves, no `val_offset` rules, no DWARF expressions, no control flow, no calls, no multi-frame unwinding, no fixed-width machine words, no asynchronous writes below `sp`.

**The two models are independent.** `Toy.Unwind` indexes table rows by operation count, not byte offset, so the effect of branch relaxation on CFI advance-location deltas (which real assemblers re-encode during relaxation, for example LLVM's `relaxDwarfCallFrameFragment`) is not modeled.

### Real systems the models are meant to inform

* `Toy.Relax` abstracts the choice between a short and a long encoding of span-dependent branch instructions made by assemblers and linkers (Szymanski 1978; LLVM's MC layer; CompCert's `Branch_relaxation` module; the CakeML `lab_to_target` loop). The design questions are when iterative relaxation converges, to which fixpoint, whether that fixpoint is least or smallest, and whether re-relaxation after a change keeps branches correct.
* `Toy.Unwind` abstracts the CFA and register rules of DWARF call frame information (DWARF 5, Section 6.4). The design questions are what it means for a table to be correct with respect to the code it describes, which simple table mistakes break correctness, and whether a static check can decide correctness.

Every statement about a real system in this report is labeled `Basis: derived (modeling bridge)` and states its reasoning; the Lean proofs establish none of them.

### Subjects and their relationship

`REPORT.json` lists the Lean 4 toolchain release that checks every proof, and the primary sources (papers, the DWARF 5 specification, and three source repositories at fixed commits) that the results cite as prior art or as the target of a modeling bridge. The toolchain is the only subject that the evidence executes; the sources were read, and nothing in this package was executed against them.

### Toolchain and library constraints

* Lean `leanprover/lean4:v4.34.1` (`lean/lean-toolchain`), Lake project `lean/lakefile.toml` with one library target `ToyRelax` and no dependencies.
* Core Lean only: no Mathlib, and no module imports anything outside the package.
* `#print axioms` for every declaration of the library reports a subset of `propext`, `Classical.choice`, `Quot.sound` (recorded per declaration in `audit/axioms.json`).
* `lean/Search/*.lean` (bounded-search scripts and one `decide` support check) and `lean/RevalidationAudit.lean` are outside the library target; no result depends on them.

## Findings

Evidence roles: every theorem below is kernel-checked and labeled `Basis: execution (Lean kernel check)`; its axioms and hashes are recorded under **Evidence**. Every statement connecting a result to a real assembler, compiler, specification or unwinder is a separate line labeled `Basis: derived (modeling bridge)`, with its reasoning; no such statement is established by the Lean proofs. Lean statements are quoted as printed by `#check @name` with the namespaces `Toy.Relax` and `Toy.Unwind` opened.

### Key definitions (verbatim from the Lean sources, doc comments omitted)

The block is self-contained: split at the `-- Toy.Unwind` line and wrapped in `namespace Toy.Relax` … `end Toy.Relax` and `namespace Toy.Unwind` … `end Toy.Unwind`, it elaborates with core Lean alone.

```lean
-- Toy.Relax
structure Params where
  shortSize : Nat
  longSize : Nat
  reach : Nat
deriving Repr, DecidableEq
inductive Instr where
  | fixed (size : Nat)
  | branch (target : Nat)
  | align (k : Nat)
deriving Repr, DecidableEq
def Instr.isBranch : Instr → Bool
  | .branch _ => true
  | _ => false
def Instr.isAlign : Instr → Bool
  | .align _ => true
  | _ => false
abbrev Prog := List Instr
abbrev Asg := Nat → Bool
def Asg.Le (a b : Asg) : Prop := ∀ i, a i = true → b i = true
def allShort : Asg := fun _ => false
def promote (a : Asg) (j : Nat) : Asg := fun i => if i = j then true else a i
def setShort (a : Asg) (j : Nat) : Asg := fun i => if i = j then false else a i
def padTo (k addr : Nat) : Nat := if k = 0 then 0 else (k - addr % k) % k
def instrSize (prm : Params) (base : Nat) (long : Bool) : Instr → Nat
  | .fixed s => s
  | .branch _ => if long then prm.longSize else prm.shortSize
  | .align k => padTo k base
def addr (prm : Params) (p : Prog) (a : Asg) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let b := addr prm p a k
    b + (match p[k]? with
         | some ins => instrSize prm b (a k) ins
         | none => 0)
def size (prm : Params) (p : Prog) (a : Asg) (k : Nat) : Nat :=
  match p[k]? with
  | some ins => instrSize prm (addr prm p a k) (a k) ins
  | none => 0
def dist (prm : Params) (p : Prog) (a : Asg) (i t : Nat) : Nat :=
  if i ≤ t then addr prm p a t - addr prm p a i else addr prm p a i - addr prm p a t
def outOfReach (prm : Params) (p : Prog) (a : Asg) (i : Nat) : Bool :=
  match p[i]? with
  | some (.branch t) => !a i && decide (prm.reach < dist prm p a i t)
  | _ => false
def Valid (prm : Params) (p : Prog) (a : Asg) : Prop :=
  ∀ i, i < p.length → outOfReach prm p a i = false
def step (prm : Params) (p : Prog) (a : Asg) : Asg := fun i => a i || outOfReach prm p a i
def numBranches (p : Prog) : Nat := p.countP Instr.isBranch
def iter (f : Asg → Asg) : Nat → Asg → Asg
  | 0, a => a
  | n + 1, a => iter f n (f a)
def relax (prm : Params) (p : Prog) (a : Asg) : Asg := iter (step prm p) (numBranches p) a
def changed (prm : Params) (p : Prog) (a : Asg) : Bool := (List.range p.length).any (outOfReach prm p a)
def relaxLoop (prm : Params) (p : Prog) : Nat → Asg → Option Asg
  | 0, _ => none
  | n + 1, a => if changed prm p a then relaxLoop prm p n (step prm p a) else some a
def stepGS (prm : Params) (p : Prog) (a : Asg) : Asg :=
  fun i => match p[i]? with
    | some (.branch t) => decide (prm.reach < dist prm p (setShort a i) i t)
    | _ => a i
def stepGSCurrent (prm : Params) (p : Prog) (a : Asg) : Asg :=
  fun i => match p[i]? with
    | some (.branch t) => decide (prm.reach < dist prm p a i t)
    | _ => a i
def totalSize (prm : Params) (p : Prog) (a : Asg) : Nat := addr prm p a p.length
def DistMonotone (prm : Params) (p : Prog) : Prop :=
  ∀ a b, Asg.Le a b → ∀ i t, p[i]? = some (.branch t) → dist prm p a i t ≤ dist prm p b i t
def SizesMonotone (prm : Params) (p : Prog) : Prop :=
  ∀ a b, Asg.Le a b → ∀ k, size prm p a k ≤ size prm p b k
def NoAlign (p : Prog) : Prop := ∀ ins ∈ p, ins.isAlign = false
def AllSizesPositive (prm : Params) (p : Prog) : Prop := ∀ a k, k < p.length → 0 < size prm p a k
def SizesPositiveAt (prm : Params) (p : Prog) (c : Asg) : Prop := ∀ k, k < p.length → 0 < size prm p c k
def disp (prm : Params) (p : Prog) (a : Asg) (i t : Nat) : Int := (addr prm p a t : Int) - (addr prm p a i : Int)
def JumpsTo (prm : Params) (p : Prog) (a : Asg) (i : Nat) (d : Int) (k : Nat) : Prop :=
  (addr prm p a i : Int) + d = (addr prm p a k : Int)
def emitDisp (prm : Params) (p : Prog) (a : Asg) (i : Nat) : Option Int :=
  match p[i]? with
  | some (.branch t) =>
    if a i || decide (dist prm p a i t ≤ prm.reach) then some (disp prm p a i t) else none
  | _ => none
def LandsExactly (prm : Params) (p : Prog) (c : Asg) (i t : Nat) : Prop :=
  ∃ d, emitDisp prm p c i = some d ∧
    ∀ k, k ≤ p.length → (JumpsTo prm p c i d k ↔ k = min t p.length)
def isBranchAt (p : Prog) (i : Nat) : Bool :=
  match p[i]? with
  | some ins => ins.isBranch
  | none => false
def Asg.LeOnBranches (p : Prog) (a b : Asg) : Prop :=
  ∀ i, isBranchAt p i = true → a i = true → b i = true

-- Toy.Unwind
inductive Op where
  | push (r : Nat)
  | subSp (n : Nat)
  | saveAt (r : Nat) (off : Int)
  | pop (r : Nat)
  | addSp (n : Nat)
  | setReg (r : Nat) (v : Int)
deriving Repr, DecidableEq
structure MState where
  sp : Int
  regs : Nat → Int
  mem : Int → Int
def upd {α β : Type} [DecidableEq α] (f : α → β) (x : α) (v : β) : α → β :=
  fun y => if y = x then v else f y
def execOp : Op → MState → MState
  | .push r, s => { sp := s.sp - 1, regs := s.regs, mem := upd s.mem (s.sp - 1) (s.regs r) }
  | .subSp n, s => { s with sp := s.sp - n }
  | .saveAt r off, s => { s with mem := upd s.mem (s.sp + off) (s.regs r) }
  | .pop r, s => { sp := s.sp + 1, regs := upd s.regs r (s.mem s.sp), mem := s.mem }
  | .addSp n, s => { s with sp := s.sp + n }
  | .setReg r v, s => { s with regs := upd s.regs r v }
def run : List Op → MState → MState
  | [], s => s
  | o :: os, s => run os (execOp o s)
inductive RegRule where
  | savedAt (off : Int)
  | sameValue
  | undefined
deriving Repr, DecidableEq
structure Row where
  cfa : Int
  rule : Nat → RegRule
abbrev Table := Nat → Row
def recoverReg (row : Row) (s : MState) (r : Nat) : Option Int :=
  match row.rule r with
  | .savedAt off => some (s.mem (s.sp + row.cfa - off))
  | .sameValue => some (s.regs r)
  | .undefined => none
def TableCorrect (body : List Op) (cs : List Nat) (tbl : Table) : Prop :=
  ∀ (s0 : MState) (i : Nat), i ≤ body.length →
    (run (body.take i) s0).sp + (tbl i).cfa = s0.sp ∧
    ∀ r ∈ cs, recoverReg (tbl i) (run (body.take i) s0) r = some (s0.regs r)
inductive AVal where
  | entry (r : Nat)
  | unknown
deriving Repr, DecidableEq
-- abstract state: sp = entrySp - d; slot k is the word at entrySp - k; written lists the slots written so far, most recent first
structure AState where
  d : Int
  regs : Nat → AVal
  slot : Int → AVal
  written : List Int
def AState.init : AState := ⟨0, AVal.entry, fun _ => .unknown, []⟩
def absOp : Op → AState → AState
  | .push r, A =>
    { d := A.d + 1, regs := A.regs, slot := upd A.slot (A.d + 1) (A.regs r),
      written := (A.d + 1) :: A.written }
  | .subSp n, A => { A with d := A.d + n }
  | .saveAt r off, A =>
    { A with slot := upd A.slot (A.d - off) (A.regs r), written := (A.d - off) :: A.written }
  | .pop r, A => { A with d := A.d - 1, regs := upd A.regs r (A.slot A.d) }
  | .addSp n, A => { A with d := A.d - n }
  | .setReg r _, A => { A with regs := upd A.regs r .unknown }
def absRun : List Op → AState → AState
  | [], A => A
  | o :: os, A => absRun os (absOp o A)
def ruleOk (A : AState) (r : Nat) : RegRule → Bool
  | .savedAt off => A.slot off == .entry r
  | .sameValue => A.regs r == .entry r
  | .undefined => false
def checkRow (A : AState) (cs : List Nat) (row : Row) : Bool :=
  row.cfa == A.d && cs.all (fun r => ruleOk A r (row.rule r))
def checkTable (body : List Op) (cs : List Nat) (tbl : Table) : Bool :=
  (List.range (body.length + 1)).all
    (fun i => checkRow (absRun (body.take i) AState.init) cs (tbl i))
def genRule (A : AState) (r : Nat) : RegRule :=
  if A.regs r = .entry r then .sameValue
  else match A.written.find? (fun k => A.slot k == .entry r) with
    | some k => .savedAt k
    | none => .undefined
def genTable (body : List Op) : Table := fun i =>
  let A := absRun (body.take i) AState.init
  { cfa := A.d, rule := genRule A }
```

### Definition examples (all proved)

| Definition | What it captures | Positive example | Negative example |
| :--- | :--- | :--- | :--- |
| `padTo`, `instrSize`, `size`, `addr`, `dist` | alignment padding; prefix-sum layout | `padTo_example_pos`, `size_example_align`, `addr_example`, `dist_example` | `padTo_example_aligned` (no padding when aligned); `size_example_align_shrinks` (padding shrinks from 3 to 2 bytes when code before it grows) |
| `Asg.Le` | pointwise `false < true` at every index | `asgLe_example_pos` | `asgLe_example_neg`; `asgLe_compares_nonbranch_positions` (fails because of an index holding no branch) |
| `Asg.LeOnBranches` | the same order at branch positions only | `asgLeOnBranches_example_pos` (ignores a non-branch position) | `asgLeOnBranches_example_neg` |
| `outOfReach` | short branch out of reach | `outOfReach_example_pos` | `outOfReach_example_neg`, `outOfReach_example_long` |
| `Valid` | all short branches reach | `valid_example_pos`, `valid_example_pos_long` | `valid_example_neg`, `valid_example_neg_cascade` |
| `step`, `relax`, `relaxLoop` | grow-only relaxation | `step_example`, `relax_example`, `relaxLoop_example_pos` | `relaxLoop_example_neg` (fuel 2 is not enough) |
| `stepGS` | grow-and-shrink relaxation from the counterfactual layout | `stepGS_example_promotes` | `stepGS_example_demotes`; `stepGS_decides_from_counterfactual_layout` (differs from reading the current layout) |
| `stepGSCurrent` | contrast definition only: grow-and-shrink reading the current layout | `stepGSCurrent_example_short` (a short branch within reach stays short) | `stepGSCurrent_example_keeps_long` (keeps long the branch that `stepGS` demotes); `alignOsc_counterfactual_vs_current` |
| `NoAlign` | no alignment directives | `noAlign_example_pos` | `noAlign_example_neg` |
| `SizesMonotone` | sizes monotone in the assignment | `sizesMonotone_example_pos` | `sizesMonotone_example_neg_align`, `sizesMonotone_example_neg_inverted` |
| `DistMonotone` | distances monotone in the assignment | `relax_least_nonvacuity` (first conjunct), `distMonotone_selfProg` | `distMonotone_example_neg_align`, `distMonotone_example_neg_inverted` |
| `AllSizesPositive` | no zero-size instruction under any assignment | `allSizesPositive_example_pos` | `allSizesPositive_example_neg`; `promote_relax_nonvacuity_aligned` (fourth conjunct: an alignment directive can pad 0 bytes) |
| `SizesPositiveAt` | no zero-size instruction in one layout | `sizesPositiveAt_example_pos` | `sizesPositiveAt_example_neg` (alignment padding becomes 0 bytes after a promotion) |
| `totalSize` | program length | `totalSize_example` | — |
| `disp`, `JumpsTo` | unbounded displacement; landing address | `jumpsTo_example_pos`, `jumpsTo_disp_self` | `jumpsTo_example_neg` (stale displacement) |
| `emitDisp` | encodable displacement | `emitDisp_example_pos`, `emitDisp_example_long` | `emitDisp_example_neg_reach` (short branch out of reach), `emitDisp_example_neg_nonbranch` |
| `LandsExactly` | encodable and lands exactly on the target | `landsExactly_example_pos` | `landsExactly_example_neg_zero` (a zero-size branch also lands on the next index); `landsExactly_example_neg_reach` (a short branch out of reach has no displacement) |
| `execOp`, `run`, `recoverReg` | concrete frame semantics; unwinder | `run_example`, `recoverReg_example_savedAt` | `recoverReg_example_undefined` |
| `TableCorrect` | table restores CFA and caller-visible registers | `tableCorrect_example_pos`, `tableCorrect_example_pos_frame`, `tableCorrect_example_pos_pop`, `tableCorrect_example_pos_reuse` | `tableCorrect_example_neg_cfa`, `offByOne_push_tables_incorrect` |
| `genTable` | table from abstract interpretation | `genTable_example`, `genTable_example_pop`, `genTable_example_frame` | `genTable_with_undefined_incorrect` (first conjunct: `undefined` generated) |
| `checkTable` | decidable checker | `checkTable_example_pos` | `checkTable_example_neg` |

Concrete instances: `chainPrm = ⟨1,2,1⟩`, `chainProg = [fixed 2, branch 0, branch 1]`, `chainExtraProg = [fixed 2, branch 0, branch 1, branch 3]`, `chainExtraB = fun i => decide (1 ≤ i ∧ i ≤ 3)`, `cascadeValidProg = [fixed 1, branch 0, branch 1]`; `alignPrm = ⟨1,2,2⟩`, `alignProg = [branch 1, align 4, branch 1]`, `alignB = promote allShort 0`, `alignOscProg = [branch 2, branch 3, align 4]`, `demoteProg = [fixed 1, align 4, branch 0, align 4, branch 3]`, `trailingAlignProg = [fixed 2, branch 0, align 4]`; `invPrm = ⟨2,1,1⟩`, `invProg = [branch 0, branch 0]`, `selfProg = [branch 0]`; `invOscPrm = ⟨2,1,3⟩`, `invOscProg = [fixed 2, branch 3, branch 0]`; `oscPrm = ⟨1,2,2⟩`, `oscProg = [fixed 1, branch 3, branch 0]`, `oscStart = promote allShort 1`, `oscOther = promote allShort 2`; `zeroPrm = ⟨0,1,5⟩`, `zeroProg = [branch 0, fixed 1]`; `fwdPrm = ⟨1,2,5⟩`, `fwdProg = [branch 2, fixed 1, fixed 1]`, `alignZeroProg = [branch 1, align 2, fixed 1]`, `alignGlobalProg = [branch 0, branch 1, align 4]`; `oneProg = [fixed 1, branch 0]`. Unwind bodies: `bodyPush = [push 3, setReg 3 0]`, `bodyPop = [push 3, setReg 3 0, pop 3]`, `bodyReuse = bodyPop ++ [push 4]`, `bodyFrame = [subSp 2, saveAt 3 1, setReg 3 7, addSp 1, pop 3]`, `bodyClobber = [setReg 1 5]`, `cs3 = [3]`. Unwind tables: `tblLate` (offset 1 keeps the entry row of `genTable bodyPush`), `tblEarly` (offset 0 already uses the post-push row), `tblNoRowAfterPop` (offset 3 of `genTable bodyPop` keeps the row of offset 2), and `tblStaleRule body fromRow rows` (at the offsets in `rows`, the CFA of `genTable body` with the register rules of row `fromRow`).

### Results

#### R1a — `Toy.Relax.relaxLoop_returns_relax_within_numBranches_succ`

**Kind / tier / depth.** theorem / T0 / shallow.

**Plain claim.** For every program, encoding parameters and start assignment a, the grow-only relaxation loop (each pass promotes, simultaneously, every short branch that is out of reach in the current layout; the loop stops when a pass would change nothing) stops within numBranches + 1 passes and returns exactly relax prm p a, the numBranches-fold iterate of the grow-only step; no hypothesis on sizes or alignment is needed.

**Lean statement.**

```lean
relaxLoop_returns_relax_within_numBranches_succ : ∀ (prm : Params) (p : Prog) (a : Asg),
  relaxLoop prm p (numBranches p + 1) a = some (relax prm p a)
```

**Unfolded reading.** For all `prm p a`: running `relaxLoop` with fuel `p.countP isBranch + 1` returns `some r`, where `r = iter (fun a i => a i || outOfReach prm p a i) (numBranches p) a`.

**Hypothesis ledger.** No hypotheses: the statement holds for every program, parameter set and start assignment.

**Depth.** shallow.

**Non-vacuity witness.** Two-branch promotion chain [fixed 2, branch 0, branch 1], short 1/long 2/reach 1: all-short is invalid and the returned assignment has both branches long. (`Toy.Relax.relax_nonvacuity_chain`)

**Control.** `Toy.Relax.relaxLoop_numBranches_passes_insufficient` — with `numBranches` passes instead of `numBranches + 1`, the loop returns `none` on `chainProg` from all-short, although the 2-fold iterate is valid; the bound cannot be lowered in general (this is R1d).

**Prior art.**

* T. G. Szymanski, "Assembling code for machines with span-dependent instructions", Communications of the ACM 21(4):300-308, April 1978, doi:10.1145/359460.359474. Abstract: an efficient solution is presented for the case in which the operand of every span-dependent instruction is a label or an assembly-time expression of a restricted form; with more general assembly-time expressions the length-minimization problem is NP-complete.
* J. Boender and C. Sacerdoti Coen, "On the Correctness of a Branch Displacement Algorithm", TACAS 2014, LNCS 8413, pp. 605-619, Springer, doi:10.1007/978-3-642-54862-8_53 (preprint arXiv:1209.5920). Abstract: within the CerCo verified C compiler project the authors implemented and proved correct an algorithm for choosing among jump instructions of different sizes, a problem they describe as NP-hard for minimal program size. Prior mechanized correctness proof of a branch-displacement algorithm; this package does not claim that its toy statements coincide with theirs.
* Y. K. Tan, M. O. Myreen, R. Kumar, A. Fox, S. Owens, M. Norrish, "The verified CakeML compiler backend", Journal of Functional Programming 29 (2019), e2, doi:10.1017/S0956796818000229. Source: CakeML/cakeml commit 2874b664e10939a3ee462215b2e068c89c1f70eb, compiler/backend/lab_to_targetScript.sml: enc_lines_again (line 118; a re-encoded instruction gets length MAX (LENGTH bs) l, so lengths never shrink inside the loop), enc_line (line 39; label padding is held at skip_len during the loop), upd_lab_len (line 156; label padding is recomputed only after the loop has stabilized), remove_labels_loop (line 285; fuel-bounded, returns NONE when the clock runs out); compiler/backend/proofs/lab_to_targetProofScript.sml: remove_labels_thm (line 6299; when remove_labels returns SOME (code2, labs), all_enc_ok holds for code2 and every label resolves to its position in code2). A mechanized (HOL4) grow-only relaxation loop with an encodability-and-label-position theorem.
* CompCert, AbsInt/CompCert commit 2685140bf72c959446981fb99b5e44a8975021bc, backend/Asmexpandaux.ml lines 191-249 (module Branch_relaxation): each pass computes all label positions from the current code (set_label_positions), decides every instruction against those positions and the pass-start program counters (do_relaxation), replaces each instruction that needs relaxation by its relaxed instruction list, and repeats until no instruction needs relaxation. Unverified OCaml outside the Coq proofs. Derived (modeling bridge): decisions within a pass use the layout at the start of the pass, as in the simultaneous updates of the toy model; no pass bound is coded.
* LLVM MC assembler, llvm/llvm-project commit ef02d46bb33d10383f6ba5a5d9a5511416ee790c, llvm/lib/MC/MCAssembler.cpp: MCAssembler::layout (lines 699-709, "Layout until everything fits." loop over relaxOnce); MCAssembler::relaxOnce (lines 1137-1176: one forward pass per section that updates fragment offsets in place with a Stretch correction, and stops a section after more passes than its fragment count, comment "Assume each iteration finalizes at least one extra fragment. If the layout does not converge after N+1 iterations, bail out.", lines 1164-1167); MCAssembler::relaxInstruction (lines 879-910, replaces an instruction by its relaxed form, never the reverse); relaxLEB (comment at line 941: an LEB fragment is only ever grown, "See PR35809"); relaxDwarfCallFrameFragment (lines 1043-1061, re-encodes CFI advance deltas during relaxation). Derived (modeling bridge): grow-only relaxation of instructions with recomputed alignment padding corresponds to the non-monotone setting of this package; LLVM's pass is sequential, while the toy model updates all branches simultaneously; nothing is proved here about LLVM's pass cap.

**Design question.** Assemblers/linkers choosing short or long span-dependent encodings: when does iterative relaxation converge, to which fixpoint, and is the result correct?

**Non-claims.** Listed under **Boundaries**, result R1a.

Basis: execution (Lean kernel check) — `relaxLoop_returns_relax_within_numBranches_succ`.

Basis: derived (modeling bridge) — CompCert's `Branch_relaxation` module (`backend/Asmexpandaux.ml` at the cited commit) decides every instruction of a pass against label positions and program counters computed at the start of the pass and replaces each instruction that needs relaxation by its relaxed form, which matches the simultaneous grow-only step of the toy; CakeML's `enc_lines_again` gives a re-encoded instruction the maximum of its old and new length, so encodings never shrink inside its loop. For grow-only procedures of this kind with two encodings per branch and an unbounded long form, the reasoning behind R1a carries over (the set of long branches only grows and is bounded by the number of branches). LLVM's `relaxOnce` is sequential, updates offsets in place and also relaxes non-branch fragments, so R1a says nothing about LLVM's pass cap.

#### R1b — `Toy.Relax.relax_valid_and_above_start`

**Kind / tier / depth.** theorem / T0 / shallow.

**Plain claim.** For every program, encoding parameters and start assignment a, the grow-only relaxation result relax prm p a is valid (every short branch reaches its target) and is pointwise above a in Asg.Le; no hypothesis on sizes or alignment is needed.

**Lean statement.**

```lean
relax_valid_and_above_start : ∀ (prm : Params) (p : Prog) (a : Asg), Valid prm p (relax prm p a) ∧ a.Le (relax prm p a)
```

**Unfolded reading.** `∀ i < p.length, outOfReach prm p r i = false` and `∀ i : Nat, a i = true → r i = true`, where `r = relax prm p a`.

**Hypothesis ledger.** No hypotheses: the statement holds for every program, parameter set and start assignment.

**Depth.** shallow.

**Non-vacuity witness.** Two-branch promotion chain [fixed 2, branch 0, branch 1] with short 1, long 2, reach 1: all-short is invalid, and the relaxation result from all-short is valid with both branches long. (`Toy.Relax.relax_nonvacuity_chain`)

**Prior art.**

* T. G. Szymanski, "Assembling code for machines with span-dependent instructions", Communications of the ACM 21(4):300-308, April 1978, doi:10.1145/359460.359474. Abstract: an efficient solution is presented for the case in which the operand of every span-dependent instruction is a label or an assembly-time expression of a restricted form; with more general assembly-time expressions the length-minimization problem is NP-complete.
* J. Boender and C. Sacerdoti Coen, "On the Correctness of a Branch Displacement Algorithm", TACAS 2014, LNCS 8413, pp. 605-619, Springer, doi:10.1007/978-3-642-54862-8_53 (preprint arXiv:1209.5920). Abstract: within the CerCo verified C compiler project the authors implemented and proved correct an algorithm for choosing among jump instructions of different sizes, a problem they describe as NP-hard for minimal program size. Prior mechanized correctness proof of a branch-displacement algorithm; this package does not claim that its toy statements coincide with theirs.
* Y. K. Tan, M. O. Myreen, R. Kumar, A. Fox, S. Owens, M. Norrish, "The verified CakeML compiler backend", Journal of Functional Programming 29 (2019), e2, doi:10.1017/S0956796818000229. Source: CakeML/cakeml commit 2874b664e10939a3ee462215b2e068c89c1f70eb, compiler/backend/lab_to_targetScript.sml: enc_lines_again (line 118; a re-encoded instruction gets length MAX (LENGTH bs) l, so lengths never shrink inside the loop), enc_line (line 39; label padding is held at skip_len during the loop), upd_lab_len (line 156; label padding is recomputed only after the loop has stabilized), remove_labels_loop (line 285; fuel-bounded, returns NONE when the clock runs out); compiler/backend/proofs/lab_to_targetProofScript.sml: remove_labels_thm (line 6299; when remove_labels returns SOME (code2, labs), all_enc_ok holds for code2 and every label resolves to its position in code2). A mechanized (HOL4) grow-only relaxation loop with an encodability-and-label-position theorem.
* LLVM MC assembler, llvm/llvm-project commit ef02d46bb33d10383f6ba5a5d9a5511416ee790c, llvm/lib/MC/MCAssembler.cpp: MCAssembler::layout (lines 699-709, "Layout until everything fits." loop over relaxOnce); MCAssembler::relaxOnce (lines 1137-1176: one forward pass per section that updates fragment offsets in place with a Stretch correction, and stops a section after more passes than its fragment count, comment "Assume each iteration finalizes at least one extra fragment. If the layout does not converge after N+1 iterations, bail out.", lines 1164-1167); MCAssembler::relaxInstruction (lines 879-910, replaces an instruction by its relaxed form, never the reverse); relaxLEB (comment at line 941: an LEB fragment is only ever grown, "See PR35809"); relaxDwarfCallFrameFragment (lines 1043-1061, re-encodes CFI advance deltas during relaxation). Derived (modeling bridge): grow-only relaxation of instructions with recomputed alignment padding corresponds to the non-monotone setting of this package; LLVM's pass is sequential, while the toy model updates all branches simultaneously; nothing is proved here about LLVM's pass cap.

**Design question.** Assemblers/linkers choosing short or long span-dependent encodings: when does iterative relaxation converge, to which fixpoint, and is the result correct?

**Non-claims.** Listed under **Boundaries**, result R1b.

Basis: execution (Lean kernel check) — `relax_valid_and_above_start`.

Basis: derived (modeling bridge) — In a grow-only procedure that stops when no short branch is out of reach, the stopping condition is exactly the toy notion of validity. R1b shows that validity of the result needs no monotonicity of sizes, which is the situation of assemblers that recompute alignment padding during relaxation (the LLVM MC layer relaxes alignment fragments in the same layout loop). Validity covers the reach constraint only; encodability of the long form, relocations and linker behavior are outside the model.

#### R1c — `Toy.Relax.relax_le_of_valid_of_le_of_distMonotone`

**Kind / tier / depth.** theorem / T0 / shallow.

**Plain claim.** If every branch's distance is monotone in the assignment (DistMonotone), then for every valid b with a <= b in Asg.Le, the grow-only relaxation result from a satisfies relax prm p a <= b; together with R1b, relax prm p a is the least valid assignment above a. Asg.Le is the pointwise order at every index i : Nat, including positions that hold no branch.

**Lean statement.**

```lean
@relax_le_of_valid_of_le_of_distMonotone : ∀ {prm : Params} {p : Prog},
  DistMonotone prm p → ∀ {a b : Asg}, Valid prm p b → a.Le b → (relax prm p a).Le b
```

**Unfolded reading.** If `∀ a b, (∀ i, a i → b i) → ∀ i t, p[i]? = some (branch t) → dist a i t ≤ dist b i t`, then for every `b` with no out-of-reach short branch and `∀ i : Nat, a i → b i`: `∀ i : Nat, relax prm p a i → b i`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hmono : DistMonotone prm p` | a branch that is out of reach under a stays out of reach under any b above a, so every promotion is forced | tight: counterexample `Toy.Relax.align_padding_breaks_leastness` |
| `hb : Valid prm p b` | b is a candidate fixpoint | tight: counterexample `Toy.Relax.leastness_needs_valid_upper_bound` |
| `hab : Asg.Le a b` | relaxation never demotes, so it cannot go below its start | tight: counterexample `Toy.Relax.leastness_needs_upper_bound_above_start` |

**Depth.** shallow.

**Non-vacuity witness.** chainExtraProg = [fixed 2, branch 0, branch 1, branch 3], short 1/long 2/reach 1, a = all-short, b = chainExtraB (exactly positions 1-3 long): DistMonotone holds, b is valid and above a, and the conclusion is not trivial because the relaxation result keeps branch 3 short while b has it long. (`Toy.Relax.relax_least_nonvacuity`)

**Prior art.**

* T. G. Szymanski, "Assembling code for machines with span-dependent instructions", Communications of the ACM 21(4):300-308, April 1978, doi:10.1145/359460.359474. Abstract: an efficient solution is presented for the case in which the operand of every span-dependent instruction is a label or an assembly-time expression of a restricted form; with more general assembly-time expressions the length-minimization problem is NP-complete.
* A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2):285-309, 1955, doi:10.2140/pjm.1955.5.285: a monotone function on a complete lattice has a least fixpoint. Derived (background): under DistMonotone the grow-only step is monotone and inflationary on assignments, the valid assignments are exactly its fixpoints, and this result (R1c) is the corresponding least-fixpoint statement above a start, reached after finitely many steps.
* J. Boender and C. Sacerdoti Coen, "On the Correctness of a Branch Displacement Algorithm", TACAS 2014, LNCS 8413, pp. 605-619, Springer, doi:10.1007/978-3-642-54862-8_53 (preprint arXiv:1209.5920). Abstract: within the CerCo verified C compiler project the authors implemented and proved correct an algorithm for choosing among jump instructions of different sizes, a problem they describe as NP-hard for minimal program size. Prior mechanized correctness proof of a branch-displacement algorithm; this package does not claim that its toy statements coincide with theirs.

**Design question.** Assemblers/linkers choosing short or long span-dependent encodings: when does iterative relaxation converge, to which fixpoint, and is the result correct?

**Non-claims.** Listed under **Boundaries**, result R1c.

Basis: execution (Lean kernel check) — `relax_le_of_valid_of_le_of_distMonotone`.

Basis: derived (modeling bridge) — For an instruction stream whose branch spans contain no alignment padding and whose long branch encodings are at least as long as the short ones, the toy hypothesis `DistMonotone` holds (R2b with R2c), and R1c is the familiar statement that grow-only relaxation yields the least set of long branches above its start, consistent with the abstract of Szymanski 1978. The order compares assignments pointwise; nothing is claimed about any particular assembler's data structures.

#### R1d — `Toy.Relax.relaxLoop_numBranches_passes_insufficient`

**Kind / tier / depth.** counterexample / T0 / definitional.

**Plain claim.** The numBranches + 1 pass bound of R1a is attained: on [fixed 2, branch 0, branch 1] with short 1, long 2, reach 1 (numBranches = 2), relaxLoop with 2 passes from all-short returns none, although the 2-fold iterate of the grow-only step is already valid; the third pass is the one that observes that nothing changes.

**Lean statement.**

```lean
relaxLoop_numBranches_passes_insufficient : numBranches chainProg = 2 ∧
  relaxLoop chainPrm chainProg (numBranches chainProg) allShort = none ∧
    Valid chainPrm chainProg (iter (step chainPrm chainProg) 2 allShort)
```

**Unfolded reading.** `chainProg` has 2 branches, `relaxLoop chainPrm chainProg 2 allShort = none`, and `iter step 2 allShort` (= `relax chainPrm chainProg allShort`) is valid.

**Hypothesis ledger.** No hypotheses: the statement is about the concrete instances it names.

**Depth.** definitional.

**Non-vacuity witness.** The instance itself. (`Toy.Relax.relaxLoop_numBranches_passes_insufficient`)

**Control.** `Toy.Relax.relax_nonvacuity_chain` — with `numBranches + 1` passes the loop on the same program returns `some (relax chainPrm chainProg allShort)`, whose branches 1 and 2 are long, and all-short is invalid.

**Prior art.**

* LLVM MC assembler, llvm/llvm-project commit ef02d46bb33d10383f6ba5a5d9a5511416ee790c, llvm/lib/MC/MCAssembler.cpp: MCAssembler::layout (lines 699-709, "Layout until everything fits." loop over relaxOnce); MCAssembler::relaxOnce (lines 1137-1176: one forward pass per section that updates fragment offsets in place with a Stretch correction, and stops a section after more passes than its fragment count, comment "Assume each iteration finalizes at least one extra fragment. If the layout does not converge after N+1 iterations, bail out.", lines 1164-1167); MCAssembler::relaxInstruction (lines 879-910, replaces an instruction by its relaxed form, never the reverse); relaxLEB (comment at line 941: an LEB fragment is only ever grown, "See PR35809"); relaxDwarfCallFrameFragment (lines 1043-1061, re-encodes CFI advance deltas during relaxation). Derived (modeling bridge): grow-only relaxation of instructions with recomputed alignment padding corresponds to the non-monotone setting of this package; LLVM's pass is sequential, while the toy model updates all branches simultaneously; nothing is proved here about LLVM's pass cap.

**Design question.** Assemblers/linkers choosing short or long span-dependent encodings: when does iterative relaxation converge, to which fixpoint, and is the result correct?

**Non-claims.** Listed under **Boundaries**, result R1d.

Basis: execution (Lean kernel check) — `relaxLoop_numBranches_passes_insufficient`.

Basis: derived (modeling bridge) — None beyond the model: the bound concerns the toy loop `relaxLoop`. LLVM's per-section cap (more passes than fragments, `MCAssembler.cpp` lines 1164-1167 at the cited commit) bounds a different, sequential procedure and is not analyzed here.

#### R2a — `Toy.Relax.dist_le_dist_of_size_le_between`

**Kind / tier / depth.** theorem / T0 / shallow.

**Plain claim.** The distance between the start of the instruction at i and the start of the instruction at t depends only on the sizes of the instructions in [min i t, max i t), and is monotone in them: if each of those sizes under a is at most its size under b, the distance under a is at most the distance under b.

**Lean statement.**

```lean
@dist_le_dist_of_size_le_between : ∀ {prm : Params} {p : Prog} {a b : Asg} {i t : Nat},
  (∀ (j : Nat), min i t ≤ j → j < max i t → size prm p a j ≤ size prm p b j) → dist prm p a i t ≤ dist prm p b i t
```

**Unfolded reading.** If the sizes of the instructions with indices in `[min i t, max i t)` under `a` are pointwise at most those under `b`, then `|addr_a t − addr_a i| ≤ |addr_b t − addr_b i|`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `h : ∀ j, min i t ≤ j → j < max i t → size prm p a j ≤ size prm p b j` | the in-between sizes grow | tight: counterexample `Toy.Relax.dist_decreases_when_size_between_decreases` |

**Depth.** shallow.

**Non-vacuity witness.** Chain program: promoting branch 1 grows the only in-between size of branch 2 and strictly grows its distance. (`Toy.Relax.dist_mono_nonvacuity`)

**Prior art.**

* T. G. Szymanski, "Assembling code for machines with span-dependent instructions", Communications of the ACM 21(4):300-308, April 1978, doi:10.1145/359460.359474. Abstract: an efficient solution is presented for the case in which the operand of every span-dependent instruction is a label or an assembly-time expression of a restricted form; with more general assembly-time expressions the length-minimization problem is NP-complete.

**Design question.** Assemblers/linkers choosing short or long span-dependent encodings: when does iterative relaxation converge, to which fixpoint, and is the result correct?

**Non-claims.** Listed under **Boundaries**, result R2a.

Basis: execution (Lean kernel check) — `dist_le_dist_of_size_le_between`.

Basis: derived (modeling bridge) — The lemma holds for any layout defined by prefix sums of instruction sizes with start-to-start displacements. Encodings that measure a displacement from the end of the branch instruction (as on x86) shift the span by the branch's own size, which the lemma does not cover.

#### R2b — `Toy.Relax.distMonotone_of_sizesMonotone`

**Kind / tier / depth.** theorem / T0 / definitional.

**Plain claim.** If every instruction size is monotone in the assignment (SizesMonotone), then every branch distance is monotone in the assignment (DistMonotone).

**Lean statement.**

```lean
@distMonotone_of_sizesMonotone : ∀ {prm : Params} {p : Prog}, SizesMonotone prm p → DistMonotone prm p
```

**Unfolded reading.** `(∀ a ≤ b, ∀ k, size a k ≤ size b k) → (∀ a ≤ b, ∀ branch i → t, dist a i t ≤ dist b i t)`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `h : SizesMonotone prm p` | feeds R2a | tight: counterexample `Toy.Relax.distMonotone_example_neg_align` |

**Depth.** definitional.

**Non-vacuity witness.** Chain program (no alignment, short <= long), on which some distance actually grows. (`Toy.Relax.distMonotone_nonvacuity`)

**Prior art.**

* T. G. Szymanski, "Assembling code for machines with span-dependent instructions", Communications of the ACM 21(4):300-308, April 1978, doi:10.1145/359460.359474. Abstract: an efficient solution is presented for the case in which the operand of every span-dependent instruction is a label or an assembly-time expression of a restricted form; with more general assembly-time expressions the length-minimization problem is NP-complete.
* J. Boender and C. Sacerdoti Coen, "On the Correctness of a Branch Displacement Algorithm", TACAS 2014, LNCS 8413, pp. 605-619, Springer, doi:10.1007/978-3-642-54862-8_53 (preprint arXiv:1209.5920). Abstract: within the CerCo verified C compiler project the authors implemented and proved correct an algorithm for choosing among jump instructions of different sizes, a problem they describe as NP-hard for minimal program size. Prior mechanized correctness proof of a branch-displacement algorithm; this package does not claim that its toy statements coincide with theirs.

**Design question.** Assemblers/linkers choosing short or long span-dependent encodings: when does iterative relaxation converge, to which fixpoint, and is the result correct?

**Non-claims.** Listed under **Boundaries**, result R2b.

Basis: execution (Lean kernel check) — `distMonotone_of_sizesMonotone`.

Basis: derived (modeling bridge) — None beyond the model: this is an order-theoretic consequence of the prefix-sum layout (R2a).

#### R2c — `Toy.Relax.sizesMonotone_of_noAlign_of_short_le_long`

**Kind / tier / depth.** theorem / T0 / shallow.

**Plain claim.** A program without alignment directives, under parameters with shortSize <= longSize, has every instruction size monotone in the assignment.

**Lean statement.**

```lean
@sizesMonotone_of_noAlign_of_short_le_long : ∀ {prm : Params} {p : Prog},
  NoAlign p → prm.shortSize ≤ prm.longSize → SizesMonotone prm p
```

**Unfolded reading.** If no instruction of `p` is `align _` and `shortSize ≤ longSize`, then `∀ a ≤ b, ∀ k, size a k ≤ size b k`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hna : NoAlign p` | alignment padding can shrink when earlier code grows | tight: counterexample `Toy.Relax.noAlign_needed_for_sizesMonotone` |
| `hsl : prm.shortSize ≤ prm.longSize` | promotion must not shrink a branch | tight: counterexample `Toy.Relax.short_le_long_needed_for_sizesMonotone` |

**Depth.** shallow.

**Non-vacuity witness.** Chain program: promoting branch 1 strictly grows its size. (`Toy.Relax.sizesMonotone_nonvacuity`)

**Prior art.**

* T. G. Szymanski, "Assembling code for machines with span-dependent instructions", Communications of the ACM 21(4):300-308, April 1978, doi:10.1145/359460.359474. Abstract: an efficient solution is presented for the case in which the operand of every span-dependent instruction is a label or an assembly-time expression of a restricted form; with more general assembly-time expressions the length-minimization problem is NP-complete.
* Y. K. Tan, M. O. Myreen, R. Kumar, A. Fox, S. Owens, M. Norrish, "The verified CakeML compiler backend", Journal of Functional Programming 29 (2019), e2, doi:10.1017/S0956796818000229. Source: CakeML/cakeml commit 2874b664e10939a3ee462215b2e068c89c1f70eb, compiler/backend/lab_to_targetScript.sml: enc_lines_again (line 118; a re-encoded instruction gets length MAX (LENGTH bs) l, so lengths never shrink inside the loop), enc_line (line 39; label padding is held at skip_len during the loop), upd_lab_len (line 156; label padding is recomputed only after the loop has stabilized), remove_labels_loop (line 285; fuel-bounded, returns NONE when the clock runs out); compiler/backend/proofs/lab_to_targetProofScript.sml: remove_labels_thm (line 6299; when remove_labels returns SOME (code2, labs), all_enc_ok holds for code2 and every label resolves to its position in code2). A mechanized (HOL4) grow-only relaxation loop with an encodability-and-label-position theorem.

**Design question.** Assemblers/linkers choosing short or long span-dependent encodings: when does iterative relaxation converge, to which fixpoint, and is the result correct?

**Non-claims.** Listed under **Boundaries**, result R2c.

Basis: execution (Lean kernel check) — `sizesMonotone_of_noAlign_of_short_le_long`.

Basis: derived (modeling bridge) — The sufficient condition corresponds to an instruction stream without alignment directives in which every long branch encoding is at least as long as the short one. Alignment padding recomputed from the current address is exactly what breaks size monotonicity (`noAlign_needed_for_sizesMonotone`), and so does a long form shorter than the short form (`short_le_long_needed_for_sizesMonotone`).

#### R2e — `Toy.Relax.align_padding_breaks_leastness`, `Toy.Relax.align_counterexample_still_terminates_valid`

**Kind / tier / depth.** counterexample / T1 / definitional.

**Plain claim.** With an alignment directive, leastness fails while termination and validity still hold: on [branch 1, align 4, branch 1] (short 1, long 2, reach 2; shortSize <= longSize), relaxation from all-short stops within numBranches + 1 passes at a valid assignment that promotes branch 2, yet promoting only branch 0 is also valid (it shrinks the alignment padding and brings branch 2 into reach), and the relaxation result is not below it.

**Lean statement.**

```lean
align_padding_breaks_leastness : alignPrm.shortSize ≤ alignPrm.longSize ∧
  Valid alignPrm alignProg alignB ∧ allShort.Le alignB ∧ ¬(relax alignPrm alignProg allShort).Le alignB
align_counterexample_still_terminates_valid : relaxLoop alignPrm alignProg (numBranches alignProg + 1) allShort =
    some (relax alignPrm alignProg allShort) ∧
  Valid alignPrm alignProg (relax alignPrm alignProg allShort)
```

**Unfolded reading.** On `alignProg = [branch 1, align 4, branch 1]`, `alignPrm = ⟨1, 2, 2⟩`, `alignB = promote allShort 0`: `1 ≤ 2`, `alignB` is valid and above all-short, the relaxation result is not below `alignB` (it has branch 2 long), and `relaxLoop` with fuel `numBranches + 1` returns the relaxation result, which is valid.

**Hypothesis ledger.** No hypotheses: the statement is about the concrete instances it names.

**Depth.** definitional.

**Non-vacuity witness.** The instance itself. (`Toy.Relax.align_counterexample_still_terminates_valid`)

**Control.** `Toy.Relax.relax_le_of_valid_of_le_of_noAlign_of_short_le_long` — without alignment directives and with `shortSize ≤ longSize`, leastness holds for every program (auxiliary corollary of R1c, R2b and R2c).

**Prior art.**

* LLVM MC assembler, llvm/llvm-project commit ef02d46bb33d10383f6ba5a5d9a5511416ee790c, llvm/lib/MC/MCAssembler.cpp: MCAssembler::layout (lines 699-709, "Layout until everything fits." loop over relaxOnce); MCAssembler::relaxOnce (lines 1137-1176: one forward pass per section that updates fragment offsets in place with a Stretch correction, and stops a section after more passes than its fragment count, comment "Assume each iteration finalizes at least one extra fragment. If the layout does not converge after N+1 iterations, bail out.", lines 1164-1167); MCAssembler::relaxInstruction (lines 879-910, replaces an instruction by its relaxed form, never the reverse); relaxLEB (comment at line 941: an LEB fragment is only ever grown, "See PR35809"); relaxDwarfCallFrameFragment (lines 1043-1061, re-encodes CFI advance deltas during relaxation). Derived (modeling bridge): grow-only relaxation of instructions with recomputed alignment padding corresponds to the non-monotone setting of this package; LLVM's pass is sequential, while the toy model updates all branches simultaneously; nothing is proved here about LLVM's pass cap.
* Y. K. Tan, M. O. Myreen, R. Kumar, A. Fox, S. Owens, M. Norrish, "The verified CakeML compiler backend", Journal of Functional Programming 29 (2019), e2, doi:10.1017/S0956796818000229. Source: CakeML/cakeml commit 2874b664e10939a3ee462215b2e068c89c1f70eb, compiler/backend/lab_to_targetScript.sml: enc_lines_again (line 118; a re-encoded instruction gets length MAX (LENGTH bs) l, so lengths never shrink inside the loop), enc_line (line 39; label padding is held at skip_len during the loop), upd_lab_len (line 156; label padding is recomputed only after the loop has stabilized), remove_labels_loop (line 285; fuel-bounded, returns NONE when the clock runs out); compiler/backend/proofs/lab_to_targetProofScript.sml: remove_labels_thm (line 6299; when remove_labels returns SOME (code2, labs), all_enc_ok holds for code2 and every label resolves to its position in code2). A mechanized (HOL4) grow-only relaxation loop with an encodability-and-label-position theorem.
* T. G. Szymanski, "Assembling code for machines with span-dependent instructions", Communications of the ACM 21(4):300-308, April 1978, doi:10.1145/359460.359474. Abstract: an efficient solution is presented for the case in which the operand of every span-dependent instruction is a label or an assembly-time expression of a restricted form; with more general assembly-time expressions the length-minimization problem is NP-complete.

**Design question.** Assemblers/linkers choosing short or long span-dependent encodings: when does iterative relaxation converge, to which fixpoint, and is the result correct?

**Non-claims.** Listed under **Boundaries**, result R2e.

Basis: execution (Lean kernel check) — `align_padding_breaks_leastness`, `align_counterexample_still_terminates_valid`.

Basis: derived (modeling bridge) — Assemblers that recompute alignment padding during grow-only relaxation (the LLVM MC layer relaxes alignment fragments in the same layout loop) are in the non-monotone setting of this result: the toy shows that such a loop can still stop at a valid encoding that is not the least one. CakeML holds label padding fixed during its loop and recomputes it only afterwards (`enc_line`, `upd_lab_len`). Whether any real assembler produces a non-least encoding on some input is not established here.

#### R3a — `Toy.Relax.growShrink_two_cycle_from_nonbottom_start`

**Kind / tier / depth.** counterexample / T1 / definitional.

**Plain claim.** Grow-and-shrink relaxation, in which each branch i is re-decided from the counterfactual layout setShort a i (branch i tentatively short, every other position as in a) and long branches may be demoted, can oscillate forever even with monotone sizes when started from a non-bottom assignment: on [fixed 1, branch 3, branch 0] (short 1, long 2, reach 2), started from 'branch 1 long', it alternates forever between 'branch 1 long, branch 2 short' and 'branch 1 short, branch 2 long'.

**Lean statement.**

```lean
growShrink_two_cycle_from_nonbottom_start : SizesMonotone oscPrm oscProg ∧
  oscStart ≠ oscOther ∧
    ∀ (n : Nat),
      iter (stepGS oscPrm oscProg) (2 * n) oscStart = oscStart ∧
        iter (stepGS oscPrm oscProg) (2 * n + 1) oscStart = oscOther
```

**Unfolded reading.** With `oscStart = promote allShort 1`, `oscOther = promote allShort 2`: sizes are monotone, the two assignments differ, and the even/odd iterates of `stepGS` from `oscStart` are `oscStart`/`oscOther`.

**Hypothesis ledger.** No hypotheses: the statement is about the concrete instances it names.

**Depth.** definitional.

**Non-vacuity witness.** The instance itself; on it grow-only relaxation from the same start converges and grow-and-shrink from all-short is already at a fixpoint. (`Toy.Relax.growShrink_two_cycle_controls`)

**Control.** `Toy.Relax.growShrink_two_cycle_controls` — on the same program, grow-only relaxation from the same start promotes both branches and is valid, and `stepGS` already fixes all-short.

**Prior art.**

* LLVM MC assembler, llvm/llvm-project commit ef02d46bb33d10383f6ba5a5d9a5511416ee790c, llvm/lib/MC/MCAssembler.cpp: MCAssembler::layout (lines 699-709, "Layout until everything fits." loop over relaxOnce); MCAssembler::relaxOnce (lines 1137-1176: one forward pass per section that updates fragment offsets in place with a Stretch correction, and stops a section after more passes than its fragment count, comment "Assume each iteration finalizes at least one extra fragment. If the layout does not converge after N+1 iterations, bail out.", lines 1164-1167); MCAssembler::relaxInstruction (lines 879-910, replaces an instruction by its relaxed form, never the reverse); relaxLEB (comment at line 941: an LEB fragment is only ever grown, "See PR35809"); relaxDwarfCallFrameFragment (lines 1043-1061, re-encodes CFI advance deltas during relaxation). Derived (modeling bridge): grow-only relaxation of instructions with recomputed alignment padding corresponds to the non-monotone setting of this package; LLVM's pass is sequential, while the toy model updates all branches simultaneously; nothing is proved here about LLVM's pass cap.

**Design question.** Assemblers/linkers choosing short or long span-dependent encodings: when does iterative relaxation converge, to which fixpoint, and is the result correct?

**Non-claims.** Listed under **Boundaries**, result R3a.

**Contrast with the current-layout reading `stepGSCurrent`.** `stepGS` decides branch `i` from `setShort a i`; on this instance, from `oscStart`, branch 1 is out of short reach in the current layout but within reach when tentatively short, so `stepGS` demotes it (`stepGS_decides_from_counterfactual_layout`). The contrast step `stepGSCurrent`, which reads every distance from the current layout `a`, does not oscillate from the same start: it makes both branches long, a valid fixpoint (`osc_stepGSCurrent_reaches_valid_fixpoint`). No general result about `stepGSCurrent` is stated. These are auxiliary lemmas (kernel-checked, axioms at most `propext`, `Quot.sound`), not results with their own entries:

```lean
stepGS_decides_from_counterfactual_layout : oscStart 1 = true ∧
  oscPrm.reach < dist oscPrm oscProg oscStart 1 3 ∧
    dist oscPrm oscProg (setShort oscStart 1) 1 3 ≤ oscPrm.reach ∧ stepGS oscPrm oscProg oscStart 1 = false
osc_stepGSCurrent_reaches_valid_fixpoint : stepGSCurrent oscPrm oscProg oscStart = promote oscStart 2 ∧
  stepGSCurrent oscPrm oscProg (promote oscStart 2) = promote oscStart 2 ∧ Valid oscPrm oscProg (promote oscStart 2)
```

Basis: execution (Lean kernel check) — `growShrink_two_cycle_from_nonbottom_start`.

Basis: derived (modeling bridge) — LLVM's `relaxInstruction` replaces an instruction by its relaxed form and never the reverse, so the LLVM MC layer does not perform grow-and-shrink relaxation. R3a is a property of procedures that demote, not a finding about an existing assembler.

#### R3b — `Toy.Relax.iter_stepGS_allShort_eq_iter_step_of_distMonotone`

**Kind / tier / depth.** theorem / T1 / shallow.

**Plain claim.** If distances are monotone in the assignment (DistMonotone), every iterate of grow-and-shrink relaxation (each branch i re-decided from the counterfactual layout setShort a i) started from all-short equals the corresponding iterate of grow-only relaxation; so from all-short it never demotes and its numBranches-th iterate is the grow-only result relax prm p allShort.

**Lean statement.**

```lean
@iter_stepGS_allShort_eq_iter_step_of_distMonotone : ∀ {prm : Params} {p : Prog},
  DistMonotone prm p → ∀ (n : Nat), iter (stepGS prm p) n allShort = iter (step prm p) n allShort
```

**Unfolded reading.** If distances are monotone, then for every `n`, `iter (stepGS prm p) n allShort = iter (step prm p) n allShort`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hmono : DistMonotone prm p` | a branch promoted once stays out of short reach | tight: counterexample `Toy.Relax.align_growShrink_differs_from_growOnly` |

**Depth.** shallow.

**Non-vacuity witness.** Chain program: after two grow-and-shrink steps branch 2 is long, exactly as in grow-only. (`Toy.Relax.growShrink_allShort_nonvacuity`)

**Prior art.**

* A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2):285-309, 1955, doi:10.2140/pjm.1955.5.285: a monotone function on a complete lattice has a least fixpoint. Derived (background): under DistMonotone the grow-only step is monotone and inflationary on assignments, so its iterates from all-short form an ascending chain that reaches its least fixpoint (bottom-up iteration). This result (R3b) says that grow-and-shrink relaxation from all-short follows exactly that ascending chain: under DistMonotone every long branch of an iterate stays out of short reach in its counterfactual layout setShort a i, so no branch is ever demoted.
* LLVM MC assembler, llvm/llvm-project commit ef02d46bb33d10383f6ba5a5d9a5511416ee790c, llvm/lib/MC/MCAssembler.cpp: MCAssembler::layout (lines 699-709, "Layout until everything fits." loop over relaxOnce); MCAssembler::relaxOnce (lines 1137-1176: one forward pass per section that updates fragment offsets in place with a Stretch correction, and stops a section after more passes than its fragment count, comment "Assume each iteration finalizes at least one extra fragment. If the layout does not converge after N+1 iterations, bail out.", lines 1164-1167); MCAssembler::relaxInstruction (lines 879-910, replaces an instruction by its relaxed form, never the reverse); relaxLEB (comment at line 941: an LEB fragment is only ever grown, "See PR35809"); relaxDwarfCallFrameFragment (lines 1043-1061, re-encodes CFI advance deltas during relaxation). Derived (modeling bridge): grow-only relaxation of instructions with recomputed alignment padding corresponds to the non-monotone setting of this package; LLVM's pass is sequential, while the toy model updates all branches simultaneously; nothing is proved here about LLVM's pass cap.

**Design question.** Assemblers/linkers choosing short or long span-dependent encodings: when does iterative relaxation converge, to which fixpoint, and is the result correct?

**Non-claims.** Listed under **Boundaries**, result R3b.

Basis: execution (Lean kernel check) — `iter_stepGS_allShort_eq_iter_step_of_distMonotone`.

Basis: derived (modeling bridge) — Under the same conditions as R1c (no alignment padding inside any branch span and long encodings at least as long as short ones), a procedure that decides each branch from its counterfactual short layout and starts from all-short behaves exactly like grow-only relaxation. No real assembler is claimed to implement `stepGS`.

#### R3c — `Toy.Relax.align_growShrink_four_cycle_from_allShort`, `Toy.Relax.inverted_growShrink_two_cycle_from_allShort`

**Kind / tier / depth.** counterexample / T1 / definitional.

**Plain claim.** Grow-and-shrink relaxation stepGS, in which each branch i is re-decided from the counterfactual layout setShort a i (branch i tentatively short, every other position as in a; branch i becomes long iff that short encoding would be out of reach) and long branches may be demoted, can oscillate forever from all-short when distances are not monotone: on [branch 2, branch 3, align 4] with short 1, long 2, reach 2 (shortSize <= longSize; the alignment directive breaks DistMonotone) it cycles with period 4 through all-short, {1}, {0, 1}, {0}, and no iterate is a fixpoint; on [fixed 2, branch 3, branch 0] with short 2, long 1, reach 3 (no alignment, but shortSize > longSize, which also breaks DistMonotone) it alternates forever between all-short and {1, 2}.

**Lean statement.**

```lean
align_growShrink_four_cycle_from_allShort : alignPrm.shortSize ≤ alignPrm.longSize ∧
  ¬DistMonotone alignPrm alignOscProg ∧
    (∀ (n : Nat),
        iter (stepGS alignPrm alignOscProg) (n + 1) allShort ≠ iter (stepGS alignPrm alignOscProg) n allShort) ∧
      ∀ (n : Nat),
        iter (stepGS alignPrm alignOscProg) (4 * n) allShort = allShort ∧
          iter (stepGS alignPrm alignOscProg) (4 * n + 1) allShort = promote allShort 1 ∧
            iter (stepGS alignPrm alignOscProg) (4 * n + 2) allShort = promote (promote allShort 1) 0 ∧
              iter (stepGS alignPrm alignOscProg) (4 * n + 3) allShort = promote allShort 0
inverted_growShrink_two_cycle_from_allShort : NoAlign invOscProg ∧
  invOscPrm.longSize < invOscPrm.shortSize ∧
    ¬DistMonotone invOscPrm invOscProg ∧
      allShort ≠ promote (promote allShort 1) 2 ∧
        ∀ (n : Nat),
          iter (stepGS invOscPrm invOscProg) (2 * n) allShort = allShort ∧
            iter (stepGS invOscPrm invOscProg) (2 * n + 1) allShort = promote (promote allShort 1) 2
```

**Unfolded reading.** All iterates are of `stepGS`, which re-decides branch `i` from `setShort a i`. First program: `1 ≤ 2`, distances not monotone, consecutive iterates always differ, and iterates `4n, 4n+1, 4n+2, 4n+3` are all-short, `{1}`, `{0,1}`, `{0}`. Second program: no alignment, `1 < 2` (long smaller than short), distances not monotone, and iterates `2n, 2n+1` are all-short and `{1,2}`.

**Hypothesis ledger.** No hypotheses: the statement is about the concrete instances it names.

**Depth.** definitional.

**Non-vacuity witness.** The instances themselves. (`Toy.Relax.align_growShrink_four_cycle_from_allShort`)

**Control.** `Toy.Relax.iter_stepGS_allShort_eq_iter_step_of_distMonotone` — R3b: under `DistMonotone`, `stepGS` from all-short follows the grow-only iterates and cannot oscillate.

**Prior art.**

* LLVM MC assembler, llvm/llvm-project commit ef02d46bb33d10383f6ba5a5d9a5511416ee790c, llvm/lib/MC/MCAssembler.cpp: MCAssembler::layout (lines 699-709, "Layout until everything fits." loop over relaxOnce); MCAssembler::relaxOnce (lines 1137-1176: one forward pass per section that updates fragment offsets in place with a Stretch correction, and stops a section after more passes than its fragment count, comment "Assume each iteration finalizes at least one extra fragment. If the layout does not converge after N+1 iterations, bail out.", lines 1164-1167); MCAssembler::relaxInstruction (lines 879-910, replaces an instruction by its relaxed form, never the reverse); relaxLEB (comment at line 941: an LEB fragment is only ever grown, "See PR35809"); relaxDwarfCallFrameFragment (lines 1043-1061, re-encodes CFI advance deltas during relaxation). Derived (modeling bridge): grow-only relaxation of instructions with recomputed alignment padding corresponds to the non-monotone setting of this package; LLVM's pass is sequential, while the toy model updates all branches simultaneously; nothing is proved here about LLVM's pass cap.

**Design question.** Assemblers/linkers choosing short or long span-dependent encodings: when does iterative relaxation converge, to which fixpoint, and is the result correct?

**Non-claims.** Listed under **Boundaries**, result R3c.

**Contrast with the current-layout reading `stepGSCurrent`.** The aligned 4-cycle depends on the counterfactual `setShort` reading: at `{0}`, branch 0's distance to its target is 3 in the current layout (out of short reach 2) but 2 in the counterfactual layout `setShort {0} 0`, so `stepGS` demotes branch 0 while `stepGSCurrent` keeps it long (`alignOsc_counterfactual_vs_current`). From all-short, `stepGSCurrent` follows all-short, `{1}`, `{0, 1}`, `{0}` and then stays at the valid fixpoint `{0}` from step 3 on (`alignOsc_stepGSCurrent_reaches_valid_fixpoint`). The inverted-size 2-cycle also occurs under `stepGSCurrent` (`invOsc_stepGSCurrent_two_cycle`). No general result about `stepGSCurrent` is stated. These are auxiliary lemmas (kernel-checked, axioms at most `propext`, `Quot.sound`), not results with their own entries:

```lean
alignOsc_counterfactual_vs_current : promote allShort 0 0 = true ∧
  alignPrm.reach = 2 ∧
    dist alignPrm alignOscProg (promote allShort 0) 0 2 = 3 ∧
      dist alignPrm alignOscProg (setShort (promote allShort 0) 0) 0 2 = 2 ∧
        stepGS alignPrm alignOscProg (promote allShort 0) 0 = false ∧
          stepGSCurrent alignPrm alignOscProg (promote allShort 0) 0 = true
alignOsc_stepGSCurrent_reaches_valid_fixpoint : stepGSCurrent alignPrm alignOscProg allShort = promote allShort 1 ∧
  stepGSCurrent alignPrm alignOscProg (promote allShort 1) = promote (promote allShort 1) 0 ∧
    stepGSCurrent alignPrm alignOscProg (promote (promote allShort 1) 0) = promote allShort 0 ∧
      stepGSCurrent alignPrm alignOscProg (promote allShort 0) = promote allShort 0 ∧
        Valid alignPrm alignOscProg (promote allShort 0) ∧
          ∀ (n : Nat), iter (stepGSCurrent alignPrm alignOscProg) (n + 3) allShort = promote allShort 0
invOsc_stepGSCurrent_two_cycle : ∀ (n : Nat),
  iter (stepGSCurrent invOscPrm invOscProg) (2 * n) allShort = allShort ∧
    iter (stepGSCurrent invOscPrm invOscProg) (2 * n + 1) allShort = promote (promote allShort 1) 2
```

Basis: execution (Lean kernel check) — `align_growShrink_four_cycle_from_allShort`, `inverted_growShrink_two_cycle_from_allShort`.

Basis: derived (modeling bridge) — No real assembler is claimed to implement `stepGS` or `stepGSCurrent`, and the LLVM MC layer never demotes. The result informs the design of relaxation procedures that allow demotion: with alignment padding, or with a long form shorter than the short form, starting from all-short does not guarantee termination, and on the aligned instance termination depends on whether each branch is decided from its counterfactual short layout (`stepGS`, which cycles) or from the current layout (`stepGSCurrent`, which reaches a valid fixpoint).

#### R4a — `Toy.Relax.relax_allShort_totalSize_le_of_valid_of_distMonotone_of_short_le_long`

**Kind / tier / depth.** theorem / T0 / shallow.

**Plain claim.** If every branch's distance is monotone in the assignment (DistMonotone) and shortSize <= longSize, the grow-only relaxation result from all-short has the minimum total size among all valid assignments. Alignment directives are allowed as long as DistMonotone holds (the end address of an alignment directive is monotone in its start address).

**Lean statement.**

```lean
@relax_allShort_totalSize_le_of_valid_of_distMonotone_of_short_le_long : ∀ {prm : Params} {p : Prog},
  DistMonotone prm p →
    prm.shortSize ≤ prm.longSize →
      ∀ {b : Asg}, Valid prm p b → totalSize prm p (relax prm p allShort) ≤ totalSize prm p b
```

**Unfolded reading.** If distances are monotone and `shortSize ≤ longSize`, then for every valid `b`, `addr_r p.length ≤ addr_b p.length` where `r = relax prm p allShort`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hmono : DistMonotone prm p` | gives leastness of the relaxation result (R1c) | tight: counterexample `Toy.Relax.size_optimality_needs_distMonotone` |
| `hsl : prm.shortSize ≤ prm.longSize` | makes every address, hence total size, monotone in the assignment | tight: counterexample `Toy.Relax.size_optimality_needs_short_le_long` |
| `hb : Valid prm p b` | competitors must be valid | tight: counterexample `Toy.Relax.size_optimality_needs_valid` |

**Depth.** shallow.

**Non-vacuity witness.** chainExtraProg = [fixed 2, branch 0, branch 1, branch 3], short 1/long 2/reach 1, b = chainExtraB: all hypotheses hold and the relaxation result (total size 7) is strictly smaller than b (total size 8). (`Toy.Relax.size_optimality_nonvacuity`)

**Prior art.**

* T. G. Szymanski, "Assembling code for machines with span-dependent instructions", Communications of the ACM 21(4):300-308, April 1978, doi:10.1145/359460.359474. Abstract: an efficient solution is presented for the case in which the operand of every span-dependent instruction is a label or an assembly-time expression of a restricted form; with more general assembly-time expressions the length-minimization problem is NP-complete.
* G. Frieder and H. J. Saal, "A process for the determination of addresses in variable length addressing", Communications of the ACM 19(6):335-338, June 1976, doi:10.1145/360238.360241. Abstract: an algorithm assigns instruction addresses and formats when instruction length depends on the distance to the target, under an optimality criterion such as the smallest number of long instructions, which minimizes total code length.
* B. W. Leverett and T. G. Szymanski, "Chaining span-dependent jump instructions", ACM TOPLAS 2(3):274-289, July 1980, doi:10.1145/357103.357105. Abstract: minimizing object length by chaining jumps with the same target is NP-complete in its most general form; several restricted forms have efficient solutions. Not modeled here (no jump chaining).
* J. Boender and C. Sacerdoti Coen, "On the Correctness of a Branch Displacement Algorithm", TACAS 2014, LNCS 8413, pp. 605-619, Springer, doi:10.1007/978-3-642-54862-8_53 (preprint arXiv:1209.5920). Abstract: within the CerCo verified C compiler project the authors implemented and proved correct an algorithm for choosing among jump instructions of different sizes, a problem they describe as NP-hard for minimal program size. Prior mechanized correctness proof of a branch-displacement algorithm; this package does not claim that its toy statements coincide with theirs.

**Design question.** Assemblers/linkers choosing short or long span-dependent encodings: when does iterative relaxation converge, to which fixpoint, and is the result correct?

**Non-claims.** Listed under **Boundaries**, result R4a.

Basis: execution (Lean kernel check) — `relax_allShort_totalSize_le_of_valid_of_distMonotone_of_short_le_long`.

Basis: derived (modeling bridge) — Consistent with the abstracts of Szymanski 1978 (an efficient minimum-length solution when every span-dependent operand is a label or a restricted expression), Frieder & Saal 1976 and Leverett & Szymanski 1980. For a real instruction stream the hypotheses correspond to monotone distances (for example, no alignment padding inside any branch span) and long encodings at least as long as short ones. This package proves no complexity result.

#### R4b — `Toy.Relax.align_padding_breaks_size_optimality`

**Kind / tier / depth.** counterexample / T1 / definitional.

**Plain claim.** With alignment padding, the grow-only fixpoint from all-short need not have minimum total size: on [branch 1, align 4, branch 1] (short 1, long 2, reach 2; shortSize <= longSize) it has total size 6, while the valid assignment with only branch 0 long has total size 5.

**Lean statement.**

```lean
align_padding_breaks_size_optimality : alignPrm.shortSize ≤ alignPrm.longSize ∧
  Valid alignPrm alignProg alignB ∧
    totalSize alignPrm alignProg alignB = 5 ∧ totalSize alignPrm alignProg (relax alignPrm alignProg allShort) = 6
```

**Unfolded reading.** On `alignProg`, `alignPrm`: `1 ≤ 2`, `alignB` is valid, `totalSize alignB = 5`, and `totalSize (relax allShort) = 6`.

**Hypothesis ledger.** No hypotheses: the statement is about the concrete instances it names.

**Depth.** definitional.

**Non-vacuity witness.** The instance itself. (`Toy.Relax.align_padding_breaks_size_optimality`)

**Control.** `Toy.Relax.relax_allShort_totalSize_le_of_valid_of_distMonotone_of_short_le_long` — R4a: under `DistMonotone` and `shortSize ≤ longSize` the grow-only fixpoint from all-short has minimum total size.

**Prior art.**

* T. G. Szymanski, "Assembling code for machines with span-dependent instructions", Communications of the ACM 21(4):300-308, April 1978, doi:10.1145/359460.359474. Abstract: an efficient solution is presented for the case in which the operand of every span-dependent instruction is a label or an assembly-time expression of a restricted form; with more general assembly-time expressions the length-minimization problem is NP-complete.
* LLVM MC assembler, llvm/llvm-project commit ef02d46bb33d10383f6ba5a5d9a5511416ee790c, llvm/lib/MC/MCAssembler.cpp: MCAssembler::layout (lines 699-709, "Layout until everything fits." loop over relaxOnce); MCAssembler::relaxOnce (lines 1137-1176: one forward pass per section that updates fragment offsets in place with a Stretch correction, and stops a section after more passes than its fragment count, comment "Assume each iteration finalizes at least one extra fragment. If the layout does not converge after N+1 iterations, bail out.", lines 1164-1167); MCAssembler::relaxInstruction (lines 879-910, replaces an instruction by its relaxed form, never the reverse); relaxLEB (comment at line 941: an LEB fragment is only ever grown, "See PR35809"); relaxDwarfCallFrameFragment (lines 1043-1061, re-encodes CFI advance deltas during relaxation). Derived (modeling bridge): grow-only relaxation of instructions with recomputed alignment padding corresponds to the non-monotone setting of this package; LLVM's pass is sequential, while the toy model updates all branches simultaneously; nothing is proved here about LLVM's pass cap.
* Y. K. Tan, M. O. Myreen, R. Kumar, A. Fox, S. Owens, M. Norrish, "The verified CakeML compiler backend", Journal of Functional Programming 29 (2019), e2, doi:10.1017/S0956796818000229. Source: CakeML/cakeml commit 2874b664e10939a3ee462215b2e068c89c1f70eb, compiler/backend/lab_to_targetScript.sml: enc_lines_again (line 118; a re-encoded instruction gets length MAX (LENGTH bs) l, so lengths never shrink inside the loop), enc_line (line 39; label padding is held at skip_len during the loop), upd_lab_len (line 156; label padding is recomputed only after the loop has stabilized), remove_labels_loop (line 285; fuel-bounded, returns NONE when the clock runs out); compiler/backend/proofs/lab_to_targetProofScript.sml: remove_labels_thm (line 6299; when remove_labels returns SOME (code2, labs), all_enc_ok holds for code2 and every label resolves to its position in code2). A mechanized (HOL4) grow-only relaxation loop with an encodability-and-label-position theorem.

**Design question.** Assemblers/linkers choosing short or long span-dependent encodings: when does iterative relaxation converge, to which fixpoint, and is the result correct?

**Non-claims.** Listed under **Boundaries**, result R4b.

Basis: execution (Lean kernel check) — `align_padding_breaks_size_optimality`.

Basis: derived (modeling bridge) — Assemblers that place alignment padding inside branch spans and run grow-only relaxation from all-short can, on suitable inputs, produce code larger than necessary; the toy instance shows the mechanism (promoting one branch shrinks a padding and brings another branch into reach). No specific output of a real assembler is shown to be larger than necessary.

#### R5 — `Toy.Relax.promote_relax_landsExactly_of_valid_of_sizesPositiveAt`

**Kind / tier / depth.** theorem / T0 / shallow.

**Plain claim.** Let a be a valid assignment, promote any position j to long and re-run grow-only relaxation, obtaining r = relax prm p (promote a j). If every instruction inside the program has positive size in layout a and in layout r, then for every branch i with target t, in each of the two layouts the branch has an encodable displacement (emitDisp: the branch is long, or short and within reach) and that displacement, recomputed from its own layout, lands on an instruction index k <= p.length exactly when k = min t p.length; in particular the two displacements land on the same instruction indices.

**Lean statement.**

```lean
@promote_relax_landsExactly_of_valid_of_sizesPositiveAt : ∀ {prm : Params} {p : Prog} {a : Asg} {j : Nat},
  Valid prm p a →
    SizesPositiveAt prm p a →
      SizesPositiveAt prm p (relax prm p (promote a j)) →
        ∀ (i t : Nat),
          p[i]? = some (Instr.branch t) → LandsExactly prm p a i t ∧ LandsExactly prm p (relax prm p (promote a j)) i t
```

**Unfolded reading.** With `r = relax prm p (promote a j)`: if `a` is valid and `0 < size c k` for all `k < p.length` and `c ∈ {a, r}`, then for every `i, t` with `p[i]? = some (branch t)` and each `c ∈ {a, r}` there is `d` with `emitDisp prm p c i = some d` (so `d = addr_c t − addr_c i`, and the branch is long or `dist ≤ reach`) and `∀ k ≤ p.length, addr_c i + d = addr_c k ↔ k = min t p.length`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hv : Valid prm p a` | every branch of the original layout must be encodable | tight: counterexample `Toy.Relax.promote_relax_landsExactly_needs_valid` |
| `hposA : SizesPositiveAt prm p a` | distinct instruction indices have distinct addresses in layout a | tight: counterexample `Toy.Relax.promote_relax_landsExactly_needs_sizesPositiveAt_before` |
| `hposR : SizesPositiveAt prm p (relax prm p (promote a j))` | distinct instruction indices have distinct addresses in layout r; promotion can shrink alignment padding to 0 bytes | tight: counterexample `Toy.Relax.promote_relax_landsExactly_needs_sizesPositiveAt_after` |

**Depth.** shallow.

**Non-vacuity witness.** [branch 2, fixed 1, fixed 1], short 1/long 2/reach 5, a = all-short (valid), j = 0: sizes are positive in both layouts and the promotion is not a no-op; promote_relax_nonvacuity_aligned gives an instance with an alignment directive. (`Toy.Relax.promote_relax_nonvacuity`)

**Control.** `Toy.Relax.promote_without_relax_breaks_emitDisp`, `Toy.Relax.stale_displacement_lands_elsewhere` — `promote_without_relax_breaks_emitDisp`: on `cascadeValidProg`, promoting branch 1 without re-relaxing leaves branch 2 without an encodable displacement (`emitDisp … = none`), and re-relaxing restores one (displacement −2, it was −1 before). `stale_displacement_lands_elsewhere`: on `fwdProg`, branch 0's displacement computed in the old layout lands at index 1 instead of its target 2 in the re-relaxed layout.

**Prior art.**

* Y. K. Tan, M. O. Myreen, R. Kumar, A. Fox, S. Owens, M. Norrish, "The verified CakeML compiler backend", Journal of Functional Programming 29 (2019), e2, doi:10.1017/S0956796818000229. Source: CakeML/cakeml commit 2874b664e10939a3ee462215b2e068c89c1f70eb, compiler/backend/lab_to_targetScript.sml: enc_lines_again (line 118; a re-encoded instruction gets length MAX (LENGTH bs) l, so lengths never shrink inside the loop), enc_line (line 39; label padding is held at skip_len during the loop), upd_lab_len (line 156; label padding is recomputed only after the loop has stabilized), remove_labels_loop (line 285; fuel-bounded, returns NONE when the clock runs out); compiler/backend/proofs/lab_to_targetProofScript.sml: remove_labels_thm (line 6299; when remove_labels returns SOME (code2, labs), all_enc_ok holds for code2 and every label resolves to its position in code2). A mechanized (HOL4) grow-only relaxation loop with an encodability-and-label-position theorem.
* J. Boender and C. Sacerdoti Coen, "On the Correctness of a Branch Displacement Algorithm", TACAS 2014, LNCS 8413, pp. 605-619, Springer, doi:10.1007/978-3-642-54862-8_53 (preprint arXiv:1209.5920). Abstract: within the CerCo verified C compiler project the authors implemented and proved correct an algorithm for choosing among jump instructions of different sizes, a problem they describe as NP-hard for minimal program size. Prior mechanized correctness proof of a branch-displacement algorithm; this package does not claim that its toy statements coincide with theirs.
* LLVM MC assembler, llvm/llvm-project commit ef02d46bb33d10383f6ba5a5d9a5511416ee790c, llvm/lib/MC/MCAssembler.cpp: MCAssembler::layout (lines 699-709, "Layout until everything fits." loop over relaxOnce); MCAssembler::relaxOnce (lines 1137-1176: one forward pass per section that updates fragment offsets in place with a Stretch correction, and stops a section after more passes than its fragment count, comment "Assume each iteration finalizes at least one extra fragment. If the layout does not converge after N+1 iterations, bail out.", lines 1164-1167); MCAssembler::relaxInstruction (lines 879-910, replaces an instruction by its relaxed form, never the reverse); relaxLEB (comment at line 941: an LEB fragment is only ever grown, "See PR35809"); relaxDwarfCallFrameFragment (lines 1043-1061, re-encodes CFI advance deltas during relaxation). Derived (modeling bridge): grow-only relaxation of instructions with recomputed alignment padding corresponds to the non-monotone setting of this package; LLVM's pass is sequential, while the toy model updates all branches simultaneously; nothing is proved here about LLVM's pass cap.

**Design question.** Assemblers/linkers choosing short or long span-dependent encodings: when does iterative relaxation converge, to which fixpoint, and is the result correct?

**Non-claims.** Listed under **Boundaries**, result R5.

Basis: execution (Lean kernel check) — `promote_relax_landsExactly_of_valid_of_sizesPositiveAt`.

Basis: derived (modeling bridge) — An assembler or linker that changes one branch's encoding after layout must re-run relaxation and recompute every displacement from the new layout; reusing a displacement computed from the old layout can land on a different instruction. CakeML's `remove_labels_thm` states a related property (all encodings acceptable and every label resolving to its position) for its own loop. Relocations and linker relaxation are outside the model.

#### R6a — `Toy.Unwind.genTable_correct_of_no_undefined`

**Kind / tier / depth.** theorem / T1 / shallow.

**Plain claim.** If the abstract interpretation (tracking the sp delta, register contents and stack-slot contents symbolically) assigns no caller-visible register the rule undefined at any offset, then the table it generates is correct: at every offset it recovers the caller's sp (CFA) and the entry values of all caller-visible registers, for every entry state.

**Lean statement.**

```lean
@genTable_correct_of_no_undefined : ∀ {body : List Op} {cs : List Nat},
  (∀ (i : Nat), i ≤ body.length → ∀ (r : Nat), r ∈ cs → (genTable body i).rule r ≠ RegRule.undefined) →
    TableCorrect body cs (genTable body)
```

**Unfolded reading.** If `genRule` never returns `undefined` for a register of `cs` at any offset `i ≤ len`, then for all `s0` and `i ≤ len`, `s.sp + d_i = s0.sp` and each `r ∈ cs` is recovered as `s0.regs r` from `genTable body i`, where `s = run (take i body) s0`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `h : ∀ i ≤ body.length, ∀ r ∈ cs, (genTable body i).rule r ≠ .undefined` | every caller-visible register is recoverable at every offset | tight: counterexample `Toy.Unwind.genTable_with_undefined_incorrect` |

**Depth.** shallow.

**Non-vacuity witness.** Body [subSp 2, saveAt 3 1, setReg 3 7, addSp 1, pop 3], cs = [3]. (`Toy.Unwind.genTable_no_undefined_nonvacuity`)

**Prior art.**

* DWARF Debugging Information Format Version 5 (February 13, 2017), Section 6.4 "Call Frame Information", pp. 171-173 (CFA: "Typically, the CFA is defined to be the value of the stack pointer at the call site in the previous frame"; register rules "undefined", "same value", "offset(N)": "The previous value of this register is saved at the address CFA+N"), and Section 6.4.2.3 "Register Rule Instructions": DW_CFA_same_value sets a register's rule to "same value"; DW_CFA_restore (item 11, p. 180) sets it to the rule assigned by the CIE's initial instructions, which need not be "same value". The toy rule savedAt off corresponds to offset(-off) (opposite sign), and a toy table is one materialized row per offset, not a CIE/FDE instruction stream.
* T. Bastian, S. Kell, F. Zappa Nardelli, "Reliable and fast DWARF-based stack unwinding", Proc. ACM Program. Lang. 3(OOPSLA), Article 146 (October 2019), 24 pages (146:1-146:24), doi:10.1145/3360572. Section 2.1 (pp. 146:6-146:8) validates .eh_frame tables dynamically along one execution path (single-stepping under gdb and comparing each row with tracked addresses); Section 2.2 (from p. 146:8) synthesizes tables statically; Section 4 (p. 146:18) discusses the Linux kernel's objtool and ORC tables, which are derived statically from object code. No mechanized proofs. Contrast: checkTable here is a static check over all entry states of a straight-line toy body, proved sound and complete for that language.
* CompCert, AbsInt/CompCert commit 2685140bf72c959446981fb99b5e44a8975021bc: backend/Mach.v lines 39-50 and 97-100 (Mgetstack/Msetstack are loads/stores relative to the stack pointer, the analogue of saveAt and of reloads); x86/Asm.v line 266 declares "Pcfi_adjust (n: int)", listed at lines 979-992 among "instructions and directives not generated directly by [Asmgen], so we do not model them" (their step is Stuck). Derived: CompCert's verified semantics does not cover CFI directives.
* Y. Wang, P. Wilke, Z. Shao, "An abstract stack based approach to verified compositional compilation to machine code", Proc. ACM Program. Lang. 3(POPL), Article 62 (January 2019), 30 pages, doi:10.1145/3290375. Abstract: enriches CompCert's memory model with an abstract stack that bounds stack consumption and enforces a stack access policy through fine-grained permissions on stack memory. A mechanized stack-frame discipline of the kind that TableCorrect does not express (caller-frame protection); it does not treat unwind tables.

**Design question.** What does it mean for a CFA/register-rule unwind table to be correct with respect to the code it describes, and which simple checks are sound?

**Non-claims.** Listed under **Boundaries**, result R6a.

Basis: execution (Lean kernel check) — `genTable_correct_of_no_undefined`.

Basis: derived (modeling bridge) — DWARF 5 Section 6.4 describes the CFA as typically the stack pointer at the call site in the previous frame, and defines the register rules `undefined`, `same value` and `offset(N)`; the toy `TableCorrect` is single-frame virtual unwinding under those rules, with `savedAt off` corresponding to `offset(−off)`. Generators that derive tables statically by tracking stack-pointer deltas and stack-slot contents (such as the synthesis in Section 2.2 of Bastian, Kell & Zappa Nardelli 2019) follow the same idea; R6a does not establish correctness of any such tool.

#### R6b — `Toy.Unwind.offByOne_push_tables_incorrect`

**Kind / tier / depth.** counterexample / T1 / definitional.

**Plain claim.** For the body [push 3, setReg 3 0] with caller-visible register 3, the table that places the post-push CFA row one instruction late (offset 1 keeps the entry row) and the table that places it one instruction early (offset 0 already uses the post-push row) are both incorrect: at the misplaced offset the computed CFA is one word below (late) or above (early) the caller's sp, for every entry state.

**Lean statement.**

```lean
offByOne_push_tables_incorrect : ¬TableCorrect bodyPush cs3 tblLate ∧
  ¬TableCorrect bodyPush cs3 tblEarly ∧
    (∀ (s0 : MState), (run (List.take 1 bodyPush) s0).sp + (tblLate 1).cfa = s0.sp - 1) ∧
      ∀ (s0 : MState), (run (List.take 0 bodyPush) s0).sp + (tblEarly 0).cfa = s0.sp + 1
```

**Unfolded reading.** For `bodyPush`, the two tables are incorrect, and for every `s0`: at offset 1 the late table computes CFA `s0.sp − 1`; at offset 0 the early table computes CFA `s0.sp + 1`.

**Hypothesis ledger.** No hypotheses: the statement is about the concrete instances it names.

**Depth.** definitional.

**Non-vacuity witness.** Body [push 3, setReg 3 0], cs = [3]; its generated table is correct. (`Toy.Unwind.tableCorrect_example_pos`)

**Control.** `Toy.Unwind.tableCorrect_example_pos` — the generated table `genTable bodyPush`, whose post-push row starts at offset 1, is correct.

**Prior art.**

* DWARF Debugging Information Format Version 5 (February 13, 2017), Section 6.4 "Call Frame Information", pp. 171-173 (CFA: "Typically, the CFA is defined to be the value of the stack pointer at the call site in the previous frame"; register rules "undefined", "same value", "offset(N)": "The previous value of this register is saved at the address CFA+N"), and Section 6.4.2.3 "Register Rule Instructions": DW_CFA_same_value sets a register's rule to "same value"; DW_CFA_restore (item 11, p. 180) sets it to the rule assigned by the CIE's initial instructions, which need not be "same value". The toy rule savedAt off corresponds to offset(-off) (opposite sign), and a toy table is one materialized row per offset, not a CIE/FDE instruction stream.
* T. Bastian, S. Kell, F. Zappa Nardelli, "Reliable and fast DWARF-based stack unwinding", Proc. ACM Program. Lang. 3(OOPSLA), Article 146 (October 2019), 24 pages (146:1-146:24), doi:10.1145/3360572. Section 2.1 (pp. 146:6-146:8) validates .eh_frame tables dynamically along one execution path (single-stepping under gdb and comparing each row with tracked addresses); Section 2.2 (from p. 146:8) synthesizes tables statically; Section 4 (p. 146:18) discusses the Linux kernel's objtool and ORC tables, which are derived statically from object code. No mechanized proofs. Contrast: checkTable here is a static check over all entry states of a straight-line toy body, proved sound and complete for that language. Relevant to this result: Fig. 4 of the paper (p. 146:8, in Section 2.1) shows hand-written .eh_frame bytecode in glibc's lowlevellock.h with an off-by-one error in a return-address offset (an off-by-one in a rule's value, a related but different fault from the misplaced rows of this result).

**Design question.** What does it mean for a CFA/register-rule unwind table to be correct with respect to the code it describes, and which simple checks are sound?

**Non-claims.** Listed under **Boundaries**, result R6b.

Basis: execution (Lean kernel check) — `offByOne_push_tables_incorrect`.

Basis: derived (modeling bridge) — In real CFI, the row that applies at an instruction boundary must reflect every stack-pointer change before that boundary; emitting the CFA adjustment one instruction late or early yields a CFA off by the pushed size there. Bastian, Kell & Zappa Nardelli 2019 (Fig. 4) report a related but different off-by-one fault, in a rule's offset value, in hand-written glibc CFI.

#### R6c — `Toy.Unwind.missing_row_after_pop_incorrect`

**Kind / tier / depth.** counterexample / T1 / definitional.

**Plain claim.** For the body [push 3, setReg 3 0, pop 3] with caller-visible register 3, the table whose offset 3 (after the pop) keeps the row of offset 2 is incorrect: after the pop the computed CFA is one word above the caller's sp, for every entry state.

**Lean statement.**

```lean
missing_row_after_pop_incorrect : ¬TableCorrect bodyPop cs3 tblNoRowAfterPop ∧
  ∀ (s0 : MState), (run (List.take 3 bodyPop) s0).sp + (tblNoRowAfterPop 3).cfa = s0.sp + 1
```

**Unfolded reading.** For `bodyPop`, the table is incorrect, and for every `s0` the CFA computed at offset 3 is `s0.sp + 1`.

**Hypothesis ledger.** No hypotheses: the statement is about the concrete instances it names.

**Depth.** definitional.

**Non-vacuity witness.** Body [push 3, setReg 3 0, pop 3], cs = [3]; its generated table is correct. (`Toy.Unwind.tableCorrect_example_pos_pop`)

**Control.** `Toy.Unwind.tableCorrect_example_pos_pop` — the generated table `genTable bodyPop` is correct.

**Prior art.**

* DWARF Debugging Information Format Version 5 (February 13, 2017), Section 6.4 "Call Frame Information", pp. 171-173 (CFA: "Typically, the CFA is defined to be the value of the stack pointer at the call site in the previous frame"; register rules "undefined", "same value", "offset(N)": "The previous value of this register is saved at the address CFA+N"), and Section 6.4.2.3 "Register Rule Instructions": DW_CFA_same_value sets a register's rule to "same value"; DW_CFA_restore (item 11, p. 180) sets it to the rule assigned by the CIE's initial instructions, which need not be "same value". The toy rule savedAt off corresponds to offset(-off) (opposite sign), and a toy table is one materialized row per offset, not a CIE/FDE instruction stream.
* T. Bastian, S. Kell, F. Zappa Nardelli, "Reliable and fast DWARF-based stack unwinding", Proc. ACM Program. Lang. 3(OOPSLA), Article 146 (October 2019), 24 pages (146:1-146:24), doi:10.1145/3360572. Section 2.1 (pp. 146:6-146:8) validates .eh_frame tables dynamically along one execution path (single-stepping under gdb and comparing each row with tracked addresses); Section 2.2 (from p. 146:8) synthesizes tables statically; Section 4 (p. 146:18) discusses the Linux kernel's objtool and ORC tables, which are derived statically from object code. No mechanized proofs. Contrast: checkTable here is a static check over all entry states of a straight-line toy body, proved sound and complete for that language. Relevant to this result: Fig. 3 of the paper (p. 146:6, in Section 2.1) shows a clang 3.8 table whose row after "pop %rbx" still gives CFA = rsp+16 instead of rsp+8, the real counterpart of the missing row after a pop in this result.

**Design question.** What does it mean for a CFA/register-rule unwind table to be correct with respect to the code it describes, and which simple checks are sound?

**Non-claims.** Listed under **Boundaries**, result R6c.

Basis: execution (Lean kernel check) — `missing_row_after_pop_incorrect`.

Basis: derived (modeling bridge) — A real counterpart is reported by Bastian, Kell & Zappa Nardelli 2019 (Fig. 3): a clang 3.8 table whose row after `pop %rbx` still gives CFA = rsp+16 instead of rsp+8. In the toy, every entry state is affected.

#### R6d — `Toy.Unwind.stale_savedAt_after_pop_incorrect_after_slot_reuse`, `Toy.Unwind.stale_savedAt_after_pop_correct_without_reuse`

**Kind / tier / depth.** counterexample / T1 / definitional.

**Plain claim.** For the body [push 3, setReg 3 0, pop 3, push 4] with caller-visible register 3, the table that updates the CFA after the pop but keeps register 3's rule savedAt 1 (instead of sameValue) is incorrect: at offset 4, after push 4 has overwritten the freed slot, the unwinder reports register 4's entry value for register 3, for every entry state. For the body [push 3, setReg 3 0, pop 3] without the later push, the same stale rule gives a correct table, because a pop does not erase memory.

**Lean statement.**

```lean
stale_savedAt_after_pop_incorrect_after_slot_reuse : ¬TableCorrect bodyReuse cs3 (tblStaleRule bodyReuse 2 [3, 4]) ∧
  ∀ (s0 : MState), recoverReg (tblStaleRule bodyReuse 2 [3, 4] 4) (run (List.take 4 bodyReuse) s0) 3 = some (s0.regs 4)
stale_savedAt_after_pop_correct_without_reuse : TableCorrect bodyPop cs3 (tblStaleRule bodyPop 2 [3])
```

**Unfolded reading.** For `bodyReuse`, the table is incorrect, and for every `s0` the value recovered for register 3 at offset 4 is `s0.regs 4`; for `bodyPop`, the analogous table (rows 3 with the register rules of row 2) is correct.

**Hypothesis ledger.** No hypotheses: the statement is about the concrete instances it names.

**Depth.** definitional.

**Non-vacuity witness.** Bodies [push 3, setReg 3 0, pop 3, push 4] and [push 3, setReg 3 0, pop 3], cs = [3]; the generated table of the first body is correct. (`Toy.Unwind.tableCorrect_example_pos_reuse`)

**Control.** `Toy.Unwind.tableCorrect_example_pos_reuse` — the generated table `genTable bodyReuse`, which restores register 3 to `sameValue` after the pop, is correct.

**Prior art.**

* DWARF Debugging Information Format Version 5 (February 13, 2017), Section 6.4 "Call Frame Information", pp. 171-173 (CFA: "Typically, the CFA is defined to be the value of the stack pointer at the call site in the previous frame"; register rules "undefined", "same value", "offset(N)": "The previous value of this register is saved at the address CFA+N"), and Section 6.4.2.3 "Register Rule Instructions": DW_CFA_same_value sets a register's rule to "same value"; DW_CFA_restore (item 11, p. 180) sets it to the rule assigned by the CIE's initial instructions, which need not be "same value". The toy rule savedAt off corresponds to offset(-off) (opposite sign), and a toy table is one materialized row per offset, not a CIE/FDE instruction stream.

**Design question.** What does it mean for a CFA/register-rule unwind table to be correct with respect to the code it describes, and which simple checks are sound?

**Non-claims.** Listed under **Boundaries**, result R6d.

Basis: execution (Lean kernel check) — `stale_savedAt_after_pop_incorrect_after_slot_reuse`, `stale_savedAt_after_pop_correct_without_reuse`.

Basis: derived (modeling bridge) — In DWARF CFI, after a register is restored by a pop its rule should become `same value` (DW_CFA_same_value) or the CIE's initial rule (DW_CFA_restore), which need not be `same value`. The toy shows that a stale `offset` rule is harmless only while the freed slot keeps its value; on a real stack the slot can be overwritten by a later push, and possibly by asynchronous writes below the stack pointer, which the toy does not model.

#### R7a — `Toy.Unwind.checkTable_sound`

**Kind / tier / depth.** theorem / T1 / shallow.

**Plain claim.** If the decidable checker that replays the abstract interpretation accepts a table for a body and a caller-visible register set, the table is correct (TableCorrect).

**Lean statement.**

```lean
@checkTable_sound : ∀ {body : List Op} {cs : List Nat} {tbl : Table},
  checkTable body cs tbl = true → TableCorrect body cs tbl
```

**Unfolded reading.** `checkTable body cs tbl = true → TableCorrect body cs tbl`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `h : checkTable body cs tbl = true` | the premise of soundness | tight: counterexample `Toy.Unwind.checker_premise_needed` |

**Depth.** shallow.

**Non-vacuity witness.** Frame body [subSp 2, saveAt 3 1, setReg 3 7, addSp 1, pop 3] with its generated table. (`Toy.Unwind.checkTable_nonvacuity`)

**Prior art.**

* DWARF Debugging Information Format Version 5 (February 13, 2017), Section 6.4 "Call Frame Information", pp. 171-173 (CFA: "Typically, the CFA is defined to be the value of the stack pointer at the call site in the previous frame"; register rules "undefined", "same value", "offset(N)": "The previous value of this register is saved at the address CFA+N"), and Section 6.4.2.3 "Register Rule Instructions": DW_CFA_same_value sets a register's rule to "same value"; DW_CFA_restore (item 11, p. 180) sets it to the rule assigned by the CIE's initial instructions, which need not be "same value". The toy rule savedAt off corresponds to offset(-off) (opposite sign), and a toy table is one materialized row per offset, not a CIE/FDE instruction stream.
* T. Bastian, S. Kell, F. Zappa Nardelli, "Reliable and fast DWARF-based stack unwinding", Proc. ACM Program. Lang. 3(OOPSLA), Article 146 (October 2019), 24 pages (146:1-146:24), doi:10.1145/3360572. Section 2.1 (pp. 146:6-146:8) validates .eh_frame tables dynamically along one execution path (single-stepping under gdb and comparing each row with tracked addresses); Section 2.2 (from p. 146:8) synthesizes tables statically; Section 4 (p. 146:18) discusses the Linux kernel's objtool and ORC tables, which are derived statically from object code. No mechanized proofs. Contrast: checkTable here is a static check over all entry states of a straight-line toy body, proved sound and complete for that language.

**Design question.** What does it mean for a CFA/register-rule unwind table to be correct with respect to the code it describes, and which simple checks are sound?

**Non-claims.** Listed under **Boundaries**, result R7a.

Basis: execution (Lean kernel check) — `checkTable_sound`.

Basis: derived (modeling bridge) — A static checker of this shape (replaying an abstract interpretation of stack-pointer deltas and slot contents against each row) is sound for the toy language. Real code has control flow, frame-pointer CFAs, DWARF expressions and calls, none of which are modeled. Bastian, Kell & Zappa Nardelli 2019 validate tables dynamically along executions (Section 2.1), and the Linux kernel's objtool, discussed in their Section 4, derives tables statically; neither is analyzed here.

#### R7b — `Toy.Unwind.checkTable_complete`

**Kind / tier / depth.** theorem / T1 / shallow.

**Plain claim.** Every table that is correct (TableCorrect) for a body and caller-visible register set is accepted by the checker: for this straight-line toy language the abstract interpretation is exact. With R7a, the checker decides TableCorrect (auxiliary lemma Toy.Unwind.checkTable_iff_tableCorrect).

**Lean statement.**

```lean
@checkTable_complete : ∀ {body : List Op} {cs : List Nat} {tbl : Table},
  TableCorrect body cs tbl → checkTable body cs tbl = true
```

**Unfolded reading.** `TableCorrect body cs tbl → checkTable body cs tbl = true`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `h : TableCorrect body cs tbl` | the premise of completeness | tight: counterexample `Toy.Unwind.checker_premise_needed` |

**Depth.** shallow.

**Non-vacuity witness.** The generated table of the frame body [subSp 2, saveAt 3 1, setReg 3 7, addSp 1, pop 3] is correct; the table with a missing row after a pop is not. (`Toy.Unwind.tableCorrect_nonvacuity`)

**Prior art.**

* DWARF Debugging Information Format Version 5 (February 13, 2017), Section 6.4 "Call Frame Information", pp. 171-173 (CFA: "Typically, the CFA is defined to be the value of the stack pointer at the call site in the previous frame"; register rules "undefined", "same value", "offset(N)": "The previous value of this register is saved at the address CFA+N"), and Section 6.4.2.3 "Register Rule Instructions": DW_CFA_same_value sets a register's rule to "same value"; DW_CFA_restore (item 11, p. 180) sets it to the rule assigned by the CIE's initial instructions, which need not be "same value". The toy rule savedAt off corresponds to offset(-off) (opposite sign), and a toy table is one materialized row per offset, not a CIE/FDE instruction stream.
* T. Bastian, S. Kell, F. Zappa Nardelli, "Reliable and fast DWARF-based stack unwinding", Proc. ACM Program. Lang. 3(OOPSLA), Article 146 (October 2019), 24 pages (146:1-146:24), doi:10.1145/3360572. Section 2.1 (pp. 146:6-146:8) validates .eh_frame tables dynamically along one execution path (single-stepping under gdb and comparing each row with tracked addresses); Section 2.2 (from p. 146:8) synthesizes tables statically; Section 4 (p. 146:18) discusses the Linux kernel's objtool and ORC tables, which are derived statically from object code. No mechanized proofs. Contrast: checkTable here is a static check over all entry states of a straight-line toy body, proved sound and complete for that language.

**Design question.** What does it mean for a CFA/register-rule unwind table to be correct with respect to the code it describes, and which simple checks are sound?

**Non-claims.** Listed under **Boundaries**, result R7b.

Basis: execution (Lean kernel check) — `checkTable_complete`.

Basis: derived (modeling bridge) — Exactness of the abstract interpretation depends on the straight-line toy language with every entry state quantified; with control flow, merges or partially known memory, a sound real checker can be incomplete. No completeness claim is made for any real tool.

### Statements of counterexamples, non-vacuity witnesses and controls

Every name below is a fully proved theorem. A counterexample for a hypothesis states that all other hypotheses of the result hold on a concrete instance and that its conclusion fails there; a non-vacuity witness states that all hypotheses of the result hold on a concrete instance; a control states the nearby positive or negative behavior named in the result's entry.

* `Toy.Relax.align_growShrink_differs_from_growOnly` (R3b counterexample for `hmono`):

  ```lean
  align_growShrink_differs_from_growOnly : ¬DistMonotone alignPrm demoteProg ∧
    iter (stepGS alignPrm demoteProg) 2 allShort 4 = false ∧
      iter (step alignPrm demoteProg) 2 allShort 4 = true ∧
        stepGS alignPrm demoteProg (iter (stepGS alignPrm demoteProg) 2 allShort) =
            iter (stepGS alignPrm demoteProg) 2 allShort ∧
          Valid alignPrm demoteProg (iter (stepGS alignPrm demoteProg) 2 allShort)
  ```

* `Toy.Relax.distMonotone_example_neg_align` (R2b counterexample for `h`):

  ```lean
  distMonotone_example_neg_align : ¬DistMonotone alignPrm alignProg
  ```

* `Toy.Relax.distMonotone_nonvacuity` (R2b non-vacuity):

  ```lean
  distMonotone_nonvacuity : SizesMonotone chainPrm chainProg ∧
    dist chainPrm chainProg allShort 2 1 < dist chainPrm chainProg (promote allShort 1) 2 1
  ```

* `Toy.Relax.dist_decreases_when_size_between_decreases` (R2a counterexample for `h`):

  ```lean
  dist_decreases_when_size_between_decreases : size alignPrm alignProg alignB 1 < size alignPrm alignProg allShort 1 ∧
    dist alignPrm alignProg alignB 2 1 < dist alignPrm alignProg allShort 2 1
  ```

* `Toy.Relax.dist_mono_nonvacuity` (R2a non-vacuity):

  ```lean
  dist_mono_nonvacuity : (∀ (j : Nat),
      min 2 1 ≤ j → j < max 2 1 → size chainPrm chainProg allShort j ≤ size chainPrm chainProg (promote allShort 1) j) ∧
    dist chainPrm chainProg allShort 2 1 < dist chainPrm chainProg (promote allShort 1) 2 1
  ```

* `Toy.Relax.growShrink_allShort_nonvacuity` (R3b non-vacuity):

  ```lean
  growShrink_allShort_nonvacuity : DistMonotone chainPrm chainProg ∧ iter (stepGS chainPrm chainProg) 2 allShort 2 = true
  ```

* `Toy.Relax.growShrink_two_cycle_controls` (R3a non-vacuity; R3a control):

  ```lean
  growShrink_two_cycle_controls : relax oscPrm oscProg oscStart 1 = true ∧
    relax oscPrm oscProg oscStart 2 = true ∧
      Valid oscPrm oscProg (relax oscPrm oscProg oscStart) ∧ stepGS oscPrm oscProg allShort = allShort
  ```

* `Toy.Relax.leastness_needs_upper_bound_above_start` (R1c counterexample for `hab`):

  ```lean
  leastness_needs_upper_bound_above_start : NoAlign oneProg ∧
    chainPrm.shortSize ≤ chainPrm.longSize ∧
      DistMonotone chainPrm oneProg ∧
        Valid chainPrm oneProg allShort ∧ ¬(relax chainPrm oneProg (promote allShort 1)).Le allShort
  ```

* `Toy.Relax.leastness_needs_valid_upper_bound` (R1c counterexample for `hb`):

  ```lean
  leastness_needs_valid_upper_bound : NoAlign chainProg ∧
    chainPrm.shortSize ≤ chainPrm.longSize ∧
      DistMonotone chainPrm chainProg ∧ allShort.Le allShort ∧ ¬(relax chainPrm chainProg allShort).Le allShort
  ```

* `Toy.Relax.noAlign_needed_for_sizesMonotone` (R2c counterexample for `hna`):

  ```lean
  noAlign_needed_for_sizesMonotone : alignPrm.shortSize ≤ alignPrm.longSize ∧ ¬SizesMonotone alignPrm alignProg
  ```

* `Toy.Relax.promote_relax_landsExactly_needs_sizesPositiveAt_after` (R5 counterexample for `hposR`):

  ```lean
  promote_relax_landsExactly_needs_sizesPositiveAt_after : Valid fwdPrm alignZeroProg allShort ∧
    SizesPositiveAt fwdPrm alignZeroProg allShort ∧
      ¬∀ (i t : Nat),
          alignZeroProg[i]? = some (Instr.branch t) →
            LandsExactly fwdPrm alignZeroProg allShort i t ∧
              LandsExactly fwdPrm alignZeroProg (relax fwdPrm alignZeroProg (promote allShort 0)) i t
  ```

* `Toy.Relax.promote_relax_landsExactly_needs_sizesPositiveAt_before` (R5 counterexample for `hposA`):

  ```lean
  promote_relax_landsExactly_needs_sizesPositiveAt_before : Valid zeroPrm zeroProg allShort ∧
    SizesPositiveAt zeroPrm zeroProg (relax zeroPrm zeroProg (promote allShort 0)) ∧
      ¬∀ (i t : Nat),
          zeroProg[i]? = some (Instr.branch t) →
            LandsExactly zeroPrm zeroProg allShort i t ∧
              LandsExactly zeroPrm zeroProg (relax zeroPrm zeroProg (promote allShort 0)) i t
  ```

* `Toy.Relax.promote_relax_landsExactly_needs_valid` (R5 counterexample for `hv`):

  ```lean
  promote_relax_landsExactly_needs_valid : SizesPositiveAt chainPrm chainProg allShort ∧
    SizesPositiveAt chainPrm chainProg (relax chainPrm chainProg (promote allShort 1)) ∧
      ¬∀ (i t : Nat),
          chainProg[i]? = some (Instr.branch t) →
            LandsExactly chainPrm chainProg allShort i t ∧
              LandsExactly chainPrm chainProg (relax chainPrm chainProg (promote allShort 1)) i t
  ```

* `Toy.Relax.promote_relax_nonvacuity` (R5 non-vacuity):

  ```lean
  promote_relax_nonvacuity : Valid fwdPrm fwdProg allShort ∧
    SizesPositiveAt fwdPrm fwdProg allShort ∧
      SizesPositiveAt fwdPrm fwdProg (relax fwdPrm fwdProg (promote allShort 0)) ∧
        allShort 0 = false ∧ relax fwdPrm fwdProg (promote allShort 0) 0 = true
  ```

* `Toy.Relax.promote_without_relax_breaks_emitDisp` (R5 control):

  ```lean
  promote_without_relax_breaks_emitDisp : Valid chainPrm cascadeValidProg allShort ∧
    emitDisp chainPrm cascadeValidProg allShort 2 = some (-1) ∧
      emitDisp chainPrm cascadeValidProg (promote allShort 1) 2 = none ∧
        emitDisp chainPrm cascadeValidProg (relax chainPrm cascadeValidProg (promote allShort 1)) 2 = some (-2)
  ```

* `Toy.Relax.relax_le_of_valid_of_le_of_noAlign_of_short_le_long` (R2e control):

  ```lean
  @relax_le_of_valid_of_le_of_noAlign_of_short_le_long : ∀ {prm : Params} {p : Prog},
    NoAlign p → prm.shortSize ≤ prm.longSize → ∀ {a b : Asg}, Valid prm p b → a.Le b → (relax prm p a).Le b
  ```

* `Toy.Relax.relax_least_nonvacuity` (R1c non-vacuity):

  ```lean
  relax_least_nonvacuity : DistMonotone chainPrm chainExtraProg ∧
    Valid chainPrm chainExtraProg chainExtraB ∧
      allShort.Le chainExtraB ∧ relax chainPrm chainExtraProg allShort 3 = false ∧ chainExtraB 3 = true
  ```

* `Toy.Relax.relax_nonvacuity_chain` (R1a non-vacuity; R1b non-vacuity; R1d control):

  ```lean
  relax_nonvacuity_chain : relaxLoop chainPrm chainProg (numBranches chainProg + 1) allShort =
      some (relax chainPrm chainProg allShort) ∧
    relax chainPrm chainProg allShort 1 = true ∧
      relax chainPrm chainProg allShort 2 = true ∧ ¬Valid chainPrm chainProg allShort
  ```

* `Toy.Relax.short_le_long_needed_for_sizesMonotone` (R2c counterexample for `hsl`):

  ```lean
  short_le_long_needed_for_sizesMonotone : NoAlign invProg ∧ ¬SizesMonotone invPrm invProg
  ```

* `Toy.Relax.size_optimality_needs_distMonotone` (R4a counterexample for `hmono`):

  ```lean
  size_optimality_needs_distMonotone : alignPrm.shortSize ≤ alignPrm.longSize ∧
    Valid alignPrm alignProg alignB ∧
      ¬totalSize alignPrm alignProg (relax alignPrm alignProg allShort) ≤ totalSize alignPrm alignProg alignB
  ```

* `Toy.Relax.size_optimality_needs_short_le_long` (R4a counterexample for `hsl`):

  ```lean
  size_optimality_needs_short_le_long : DistMonotone invPrm selfProg ∧
    Valid invPrm selfProg (promote allShort 0) ∧
      ¬totalSize invPrm selfProg (relax invPrm selfProg allShort) ≤ totalSize invPrm selfProg (promote allShort 0)
  ```

* `Toy.Relax.size_optimality_needs_valid` (R4a counterexample for `hb`):

  ```lean
  size_optimality_needs_valid : DistMonotone chainPrm chainProg ∧
    chainPrm.shortSize ≤ chainPrm.longSize ∧
      ¬Valid chainPrm chainProg allShort ∧
        ¬totalSize chainPrm chainProg (relax chainPrm chainProg allShort) ≤ totalSize chainPrm chainProg allShort
  ```

* `Toy.Relax.size_optimality_nonvacuity` (R4a non-vacuity):

  ```lean
  size_optimality_nonvacuity : DistMonotone chainPrm chainExtraProg ∧
    chainPrm.shortSize ≤ chainPrm.longSize ∧
      Valid chainPrm chainExtraProg chainExtraB ∧
        totalSize chainPrm chainExtraProg (relax chainPrm chainExtraProg allShort) = 7 ∧
          totalSize chainPrm chainExtraProg chainExtraB = 8
  ```

* `Toy.Relax.sizesMonotone_nonvacuity` (R2c non-vacuity):

  ```lean
  sizesMonotone_nonvacuity : NoAlign chainProg ∧
    chainPrm.shortSize ≤ chainPrm.longSize ∧
      size chainPrm chainProg allShort 1 < size chainPrm chainProg (promote allShort 1) 1
  ```

* `Toy.Relax.stale_displacement_lands_elsewhere` (R5 control):

  ```lean
  stale_displacement_lands_elsewhere : Valid fwdPrm fwdProg allShort ∧
    Valid fwdPrm fwdProg (relax fwdPrm fwdProg (promote allShort 0)) ∧
      ¬JumpsTo fwdPrm fwdProg (relax fwdPrm fwdProg (promote allShort 0)) 0 (disp fwdPrm fwdProg allShort 0 2) 2 ∧
        JumpsTo fwdPrm fwdProg (relax fwdPrm fwdProg (promote allShort 0)) 0 (disp fwdPrm fwdProg allShort 0 2) 1
  ```

* `Toy.Unwind.checkTable_nonvacuity` (R7a non-vacuity):

  ```lean
  checkTable_nonvacuity : checkTable bodyFrame cs3 (genTable bodyFrame) = true ∧
    checkTable bodyPop cs3 tblNoRowAfterPop = false
  ```

* `Toy.Unwind.checker_premise_needed` (R7a counterexample for `h`; R7b counterexample for `h`):

  ```lean
  checker_premise_needed : checkTable bodyPush cs3 tblLate = false ∧ ¬TableCorrect bodyPush cs3 tblLate
  ```

* `Toy.Unwind.genTable_no_undefined_nonvacuity` (R6a non-vacuity):

  ```lean
  genTable_no_undefined_nonvacuity : ∀ (i : Nat),
    i ≤ bodyFrame.length → ∀ (r : Nat), r ∈ cs3 → (genTable bodyFrame i).rule r ≠ RegRule.undefined
  ```

* `Toy.Unwind.genTable_with_undefined_incorrect` (R6a counterexample for `h`):

  ```lean
  genTable_with_undefined_incorrect : (genTable bodyClobber 1).rule 1 = RegRule.undefined ∧
    ¬TableCorrect bodyClobber [1] (genTable bodyClobber)
  ```

* `Toy.Unwind.tableCorrect_example_pos` (R6b non-vacuity; R6b control):

  ```lean
  tableCorrect_example_pos : TableCorrect bodyPush cs3 (genTable bodyPush)
  ```

* `Toy.Unwind.tableCorrect_example_pos_pop` (R6c non-vacuity; R6c control):

  ```lean
  tableCorrect_example_pos_pop : TableCorrect bodyPop cs3 (genTable bodyPop)
  ```

* `Toy.Unwind.tableCorrect_example_pos_reuse` (R6d non-vacuity; R6d control):

  ```lean
  tableCorrect_example_pos_reuse : TableCorrect bodyReuse cs3 (genTable bodyReuse)
  ```

* `Toy.Unwind.tableCorrect_nonvacuity` (R7b non-vacuity):

  ```lean
  tableCorrect_nonvacuity : TableCorrect bodyFrame cs3 (genTable bodyFrame) ∧ ¬TableCorrect bodyPop cs3 tblNoRowAfterPop
  ```

Some result theorems also serve as non-vacuity witnesses or controls of other results: `align_counterexample_still_terminates_valid` (R2e result, R2e non-vacuity); `align_growShrink_four_cycle_from_allShort` (R3c result, R3c non-vacuity); `align_padding_breaks_leastness` (R1c counterexample for `hmono`, R2e result); `align_padding_breaks_size_optimality` (R4b result, R4b non-vacuity); `iter_stepGS_allShort_eq_iter_step_of_distMonotone` (R3b result, R3c control); `relaxLoop_numBranches_passes_insufficient` (R1a control, R1d result, R1d non-vacuity); `relax_allShort_totalSize_le_of_valid_of_distMonotone_of_short_le_long` (R4a result, R4b control). Their statements are quoted in the corresponding result entries above.

### Consequences that refine common expectations

1. **Grow-only relaxation with non-monotone sizes still terminates and is still valid.** R1a and R1b have *no* size hypothesis: the assignment only grows and is bounded, so the loop stops within `numBranches + 1` passes, and its stopping condition is exactly validity. Monotone distances are needed only for **leastness** (R1c), and monotone distances together with `shortSize ≤ longSize` for **minimum total size** (R4a). The alignment counterexample (R2e) shows exactly that: termination and validity hold, leastness fails.
2. **Optimality holds whenever distances are monotone and long is not smaller than short.** Under `DistMonotone` and `shortSize ≤ longSize` (for example, no alignment and `shortSize ≤ longSize`, or alignment directives that no branch spans), the grow-only fixpoint from all-short has minimum total size among valid assignments (R4a). It can fail with alignment padding inside a branch span (R4b). This is consistent with Szymanski's 1978 abstract: an efficient solution exists for label operands, and NP-completeness holds for more general assembly-time expressions. This package proves no complexity result.
3. **Grow-and-shrink oscillation needs a non-bottom start or non-monotone distances, and both suffice** (for `stepGS`, which re-decides each branch `i` from the counterfactual layout `setShort a i`). Under monotone distances, grow-and-shrink started from all-short coincides with grow-only at every iterate (R3b). With monotone sizes, it oscillates from a non-bottom start (R3a). Without monotone distances, it oscillates from all-short — with alignment and `shortSize ≤ longSize`, on a 3-instruction program, with period 4; and without alignment when `shortSize > longSize` (R3c). The aligned 4-cycle depends on the counterfactual reading: the contrast step `stepGSCurrent`, which reads the current layout, reaches a valid fixpoint on that program after 3 steps, whereas the inverted-size 2-cycle occurs under either reading.
4. **Re-relaxation after a promotion keeps every branch encodable and landing on its target** (R5), given a valid start and positive instruction sizes in both layouts. Promoting without re-relaxing can break encodability, and displacements must be recomputed from the new layout.
5. **A "missing restore row after pop" has two variants.** Keeping the whole pre-pop row is wrong immediately, because the CFA is off by one word (R6c). Keeping only a stale `savedAt` register rule is wrong only after the freed slot is overwritten (R6d) — in the toy, by a later push of a different value; on real stacks possibly by asynchronous writes.
6. **The checker is complete** for this straight-line language (R7b, proved), so `checkTable` decides `TableCorrect` (`checkTable_iff_tableCorrect`).

```text
Basis: execution (Lean kernel check) for each cited result; derived for the comparison with Szymanski 1978 in item 2
```

## Boundaries

### Non-claims (read first)

Each result does **not** show the following. The toy-model disclaimer repeated in many entries applies to every result. Paths of the form `Search/<file>.lean` below are relative to `lean/`.

**R1a** (`relaxLoop_returns_relax_within_numBranches_succ`):

* Does not say the result is least or of minimum total size; leastness needs monotone distances (R1c) and minimum size needs monotone distances and shortSize <= longSize (R4a).
* The bound counts all branches and is attained (relaxLoop_numBranches_passes_insufficient). A sharper bound (the number of short branch positions in the start, plus one) is stated separately as the auxiliary lemma Toy.Relax.relaxLoop_spec.
* Grow-only termination does not extend to grow-and-shrink relaxation (each branch i re-decided from the counterfactual layout setShort a i, long branches may be demoted), which can oscillate forever (from a non-bottom start with monotone sizes, R3a; from all-short without monotone distances, R3c).
* Simultaneous (Jacobi) updates only. A sequential pass that re-lays out the program after each promotion is not part of the model; a support check (Search/Sequential.lean, kernel-checked by decide, not a library result) shows that on [branch 3, branch 3, align 4] with short 1, long 2, reach 2 it stops at a different valid assignment (only branch 0 long) than the simultaneous passes (branches 0 and 1 long).
* Two encodings per branch with unbounded long reach only: instruction sets with more than two branch sizes (where more passes can be needed) and long forms with a finite reach (where relaxation can fail) are not modeled.
* No convergence or validity claim is made about LLVM's MCAssembler::relaxOnce, which updates offsets in place during a pass, also relaxes non-branch fragments (LEB128 values, CFI advance deltas, alignment), and stops a section after a pass count derived from its fragment count.
* Toy model: the results apply to the Lean model Toy.Relax (two encodings per branch, instruction-index targets, simultaneous updates). These theorems neither establish nor refute the corresponding claims about real assemblers or linkers (such as LLVM's MC layer, CompCert's Branch_relaxation module or the CakeML lab_to_target loop); every connection to a real toolchain is a separately labeled derived modeling bridge.

**R1b** (`relax_valid_and_above_start`):

* Validity is only the reach constraint of the toy model; encodability of the long form, relocations and linker behavior are outside the model.
* Valid does not mean least or smallest (R2e, R4b).
* Asg.Le compares every index i : Nat; at non-branch positions and indices >= p.length relax keeps the values of a unchanged.
* Two encodings per branch with unbounded long reach only: instruction sets with more than two branch sizes (where more passes can be needed) and long forms with a finite reach (where relaxation can fail) are not modeled.
* Toy model: the results apply to the Lean model Toy.Relax (two encodings per branch, instruction-index targets, simultaneous updates). These theorems neither establish nor refute the corresponding claims about real assemblers or linkers (such as LLVM's MC layer, CompCert's Branch_relaxation module or the CakeML lab_to_target loop); every connection to a real toolchain is a separately labeled derived modeling bridge.

**R1c** (`relax_le_of_valid_of_le_of_distMonotone`):

* Least in the pointwise order on assignments; minimum total size additionally needs shortSize <= longSize (R4a).
* Without DistMonotone (e.g. with alignment padding) relaxation still terminates with a valid result; only leastness fails (R2e).
* Asg.Le compares total functions Nat -> Bool at every index, including non-branch and out-of-range indices that relax copies from a; a valid b that dominates a at every branch position but not at some irrelevant index does not satisfy a <= b (asgLe_compares_nonbranch_positions). The branch-restricted form is stated separately as the auxiliary lemma Toy.Relax.relax_leOnBranches_of_valid_of_leOnBranches_of_distMonotone.
* A concrete sufficient condition for DistMonotone is no alignment directives together with shortSize <= longSize (R2b with R2c); the composed statement is the auxiliary lemma Toy.Relax.relax_le_of_valid_of_le_of_noAlign_of_short_le_long.
* Says nothing about the assignment reached from a start that is not below b.
* Toy model: the results apply to the Lean model Toy.Relax (two encodings per branch, instruction-index targets, simultaneous updates). These theorems neither establish nor refute the corresponding claims about real assemblers or linkers (such as LLVM's MC layer, CompCert's Branch_relaxation module or the CakeML lab_to_target loop); every connection to a real toolchain is a separately labeled derived modeling bridge.

**R1d** (`relaxLoop_numBranches_passes_insufficient`):

* Shows the bound is attained for one program, not for every program.
* No convergence or validity claim is made about LLVM's MCAssembler::relaxOnce, which updates offsets in place during a pass, also relaxes non-branch fragments (LEB128 values, CFI advance deltas, alignment), and stops a section after a pass count derived from its fragment count.
* Toy model: the results apply to the Lean model Toy.Relax (two encodings per branch, instruction-index targets, simultaneous updates). These theorems neither establish nor refute the corresponding claims about real assemblers or linkers (such as LLVM's MC layer, CompCert's Branch_relaxation module or the CakeML lab_to_target loop); every connection to a real toolchain is a separately labeled derived modeling bridge.

**R2a** (`dist_le_dist_of_size_le_between`):

* Uses the start-of-instruction displacement convention, under which a forward branch's own size lies in its interval; an end-of-instruction convention shifts which instruction's own size is in the interval (not formalized).
* Indices >= p.length are clamped: the address of any such index is the end address of the program, so the distance to a target t >= p.length is the distance to the end.
* Says nothing about how sizes depend on the assignment (R2b, R2c).
* Toy model: the results apply to the Lean model Toy.Relax (two encodings per branch, instruction-index targets, simultaneous updates). These theorems neither establish nor refute the corresponding claims about real assemblers or linkers (such as LLVM's MC layer, CompCert's Branch_relaxation module or the CakeML lab_to_target loop); every connection to a real toolchain is a separately labeled derived modeling bridge.

**R2b** (`distMonotone_of_sizesMonotone`):

* The converse is not claimed: DistMonotone can hold while some size that no branch spans is non-monotone (distMonotone_short_le_long_without_sizesMonotone).
* Toy model: the results apply to the Lean model Toy.Relax (two encodings per branch, instruction-index targets, simultaneous updates). These theorems neither establish nor refute the corresponding claims about real assemblers or linkers (such as LLVM's MC layer, CompCert's Branch_relaxation module or the CakeML lab_to_target loop); every connection to a real toolchain is a separately labeled derived modeling bridge.

**R2c** (`sizesMonotone_of_noAlign_of_short_le_long`):

* Alignment is the only address-dependent size in the toy; other address-dependent encodings (e.g. linker relaxation that deletes bytes) are not modeled.
* Assemblers that hold alignment padding at a fixed upper bound until branch relaxation has stabilized and only then recompute it (as CakeML's lab_to_target does with label padding) do not face this non-monotonicity inside the loop; that strategy is not modeled.
* Toy model: the results apply to the Lean model Toy.Relax (two encodings per branch, instruction-index targets, simultaneous updates). These theorems neither establish nor refute the corresponding claims about real assemblers or linkers (such as LLVM's MC layer, CompCert's Branch_relaxation module or the CakeML lab_to_target loop); every connection to a real toolchain is a separately labeled derived modeling bridge.

**R2e** (`align_padding_breaks_leastness`, `align_counterexample_still_terminates_valid`):

* Does not show non-termination or invalidity; in this model grow-only relaxation always terminates with a valid result (R1a, R1b).
* Simultaneous (Jacobi) updates only. A sequential pass that re-lays out the program after each promotion is not part of the model; a support check (Search/Sequential.lean, kernel-checked by decide, not a library result) shows that on [branch 3, branch 3, align 4] with short 1, long 2, reach 2 it stops at a different valid assignment (only branch 0 long) than the simultaneous passes (branches 0 and 1 long).
* Assemblers that hold alignment padding at a fixed upper bound until branch relaxation has stabilized and only then recompute it (as CakeML's lab_to_target does with label padding) do not face this non-monotonicity inside the loop; that strategy is not modeled.
* Does not show that any real assembler produces this layout.
* Toy model: the results apply to the Lean model Toy.Relax (two encodings per branch, instruction-index targets, simultaneous updates). These theorems neither establish nor refute the corresponding claims about real assemblers or linkers (such as LLVM's MC layer, CompCert's Branch_relaxation module or the CakeML lab_to_target loop); every connection to a real toolchain is a separately labeled derived modeling bridge.

**R3a** (`growShrink_two_cycle_from_nonbottom_start`):

* The oscillation uses a start that is not all-short; from all-short and under monotone distances grow-and-shrink cannot oscillate (R3b), while without monotone distances it can oscillate from all-short as well (R3c).
* The counterfactual reading matters: reading branch i's distance from the current layout a instead differs on forward long branches, whose own size lies in their span; from the start of this instance, branch 1 is out of short reach in the current layout but fits when tentatively short (stepGS_decides_from_counterfactual_layout). The contrast definition stepGSCurrent, which reads the current layout, does not oscillate on this instance: from the same start it makes both branches long, a valid fixpoint (osc_stepGSCurrent_reaches_valid_fixpoint). No general result about stepGSCurrent is stated.
* Two branches is the minimum number for any oscillation: with one branch, setShort a i makes the layout independent of a, so its decision is constant after one step - derived argument, not formalized; minimality in instruction count is not claimed.
* Toy model: the results apply to the Lean model Toy.Relax (two encodings per branch, instruction-index targets, simultaneous updates). These theorems neither establish nor refute the corresponding claims about real assemblers or linkers (such as LLVM's MC layer, CompCert's Branch_relaxation module or the CakeML lab_to_target loop); every connection to a real toolchain is a separately labeled derived modeling bridge.

**R3b** (`iter_stepGS_allShort_eq_iter_step_of_distMonotone`):

* Only for the all-short start; from other starts grow-and-shrink can oscillate even with monotone sizes (R3a).
* Without DistMonotone, grow-and-shrink from all-short can demote and stop at a different valid fixpoint (align_growShrink_differs_from_growOnly, on [fixed 1, align 4, branch 0, align 4, branch 3] with short 1, long 2, reach 2) and can oscillate forever (R3c).
* Toy model: the results apply to the Lean model Toy.Relax (two encodings per branch, instruction-index targets, simultaneous updates). These theorems neither establish nor refute the corresponding claims about real assemblers or linkers (such as LLVM's MC layer, CompCert's Branch_relaxation module or the CakeML lab_to_target loop); every connection to a real toolchain is a separately labeled derived modeling bridge.

**R3c** (`align_growShrink_four_cycle_from_allShort`, `inverted_growShrink_two_cycle_from_allShort`):

* Grow-only relaxation on the same programs still terminates with a valid result (R1a, R1b); the oscillation needs demotion.
* The aligned 4-cycle depends on the counterfactual reading of stepGS: at {0}, branch 0's distance to its target is 3 in the current layout {0} (out of short reach 2) but 2 in the counterfactual layout setShort {0} 0 (within reach), so stepGS demotes branch 0 and returns to all-short (alignOsc_counterfactual_vs_current). A grow-and-shrink step that reads every distance from the current layout a instead (the contrast definition stepGSCurrent) does not oscillate on this program: from all-short it follows all-short, {1}, {0, 1}, {0} and then stays at {0}, a valid fixpoint, after 3 steps (alignOsc_stepGSCurrent_reaches_valid_fixpoint). The inverted-size 2-cycle on [fixed 2, branch 3, branch 0] also occurs under the current-layout reading (invOsc_stepGSCurrent_two_cycle). No general result about stepGSCurrent is stated.
* Minimality is not claimed. Bounded search, not a proof (Search/LeastnessOptimality.lean): over all 3-instruction programs over {fixed 1, fixed 2, fixed 3, align 2, align 4} and branch targets 0-3, with 10 parameter sets all having shortSize <= longSize, the only oscillations from all-short are this program with long size 2 or 3 (short 1, reach 2).
* Does not show that any real assembler uses grow-and-shrink relaxation; LLVM's relaxInstruction never demotes.
* Toy model: the results apply to the Lean model Toy.Relax (two encodings per branch, instruction-index targets, simultaneous updates). These theorems neither establish nor refute the corresponding claims about real assemblers or linkers (such as LLVM's MC layer, CompCert's Branch_relaxation module or the CakeML lab_to_target loop); every connection to a real toolchain is a separately labeled derived modeling bridge.

**R4a** (`relax_allShort_totalSize_le_of_valid_of_distMonotone_of_short_le_long`):

* Optimality is for this toy cost (sum of sizes) and reach model; it does not contradict NP-completeness results for general assembly-time operand expressions or jump chaining (Szymanski 1978; Leverett & Szymanski 1980), which are outside the model.
* SizesMonotone (e.g. no alignment and shortSize <= longSize) is a sufficient single hypothesis, stated separately as the auxiliary lemma Toy.Relax.relax_allShort_totalSize_le_of_valid_of_sizesMonotone; DistMonotone with shortSize <= longSize is strictly weaker (distMonotone_short_le_long_without_sizesMonotone).
* No complexity claim is made for programs without monotone distances.
* Toy model: the results apply to the Lean model Toy.Relax (two encodings per branch, instruction-index targets, simultaneous updates). These theorems neither establish nor refute the corresponding claims about real assemblers or linkers (such as LLVM's MC layer, CompCert's Branch_relaxation module or the CakeML lab_to_target loop); every connection to a real toolchain is a separately labeled derived modeling bridge.

**R4b** (`align_padding_breaks_size_optimality`):

* Does not claim NP-hardness of the alignment case.
* Simultaneous (Jacobi) updates only. A sequential pass that re-lays out the program after each promotion is not part of the model; a support check (Search/Sequential.lean, kernel-checked by decide, not a library result) shows that on [branch 3, branch 3, align 4] with short 1, long 2, reach 2 it stops at a different valid assignment (only branch 0 long) than the simultaneous passes (branches 0 and 1 long).
* Assemblers that hold alignment padding at a fixed upper bound until branch relaxation has stabilized and only then recompute it (as CakeML's lab_to_target does with label padding) do not face this non-monotonicity inside the loop; that strategy is not modeled.
* Toy model: the results apply to the Lean model Toy.Relax (two encodings per branch, instruction-index targets, simultaneous updates). These theorems neither establish nor refute the corresponding claims about real assemblers or linkers (such as LLVM's MC layer, CompCert's Branch_relaxation module or the CakeML lab_to_target loop); every connection to a real toolchain is a separately labeled derived modeling bridge.

**R5** (`promote_relax_landsExactly_of_valid_of_sizesPositiveAt`):

* Re-relaxation is needed: promoting without re-relaxing can leave another short branch out of reach, with no encodable displacement (promote_without_relax_breaks_emitDisp).
* Displacements must be recomputed from the new layout: a displacement computed in the old layout lands on a different instruction in the new one (stale_displacement_lands_elsewhere).
* The result factors through two facts: r is valid (R1b), and in any valid layout with positive sizes every branch lands exactly on its target (auxiliary lemma Toy.Relax.landsExactly_of_valid_of_sizesPositiveAt). The position j need not hold a short branch.
* Landing is stated for indices k <= p.length; a target index t >= p.length denotes the end of the program.
* Says nothing about execution semantics beyond the landing index of each branch.
* Two encodings per branch with unbounded long reach only: instruction sets with more than two branch sizes (where more passes can be needed) and long forms with a finite reach (where relaxation can fail) are not modeled.
* Toy model: the results apply to the Lean model Toy.Relax (two encodings per branch, instruction-index targets, simultaneous updates). These theorems neither establish nor refute the corresponding claims about real assemblers or linkers (such as LLVM's MC layer, CompCert's Branch_relaxation module or the CakeML lab_to_target loop); every connection to a real toolchain is a separately labeled derived modeling bridge.

**R6a** (`genTable_correct_of_no_undefined`):

* Straight-line bodies only; no branches, loops, calls, frame-pointer-based CFA, register-to-register saves, val_offset rules or DWARF expressions.
* Word-addressed stack with one word per push; no return-address slot.
* Says nothing about unwinding through more than one frame.
* Single-frame virtual unwinding only: TableCorrect does not forbid the body from writing into the caller's frame (addresses >= entry sp; tableCorrect_permits_caller_frame_write) and does not require the body to restore sp or any register by its end (tableCorrect_permits_unrestored_sp).
* TableCorrect quantifies over every entry state, including ones a real ABI excludes (unaligned sp, arbitrary memory); registers and stack words are unbounded integers.
* Does not claim the generator succeeds whenever a correct table exists (not stated; checker completeness R7b is about checking, not generation).
* The relaxation model and the unwind-table model are independent: Toy.Unwind indexes table rows by operation count, not byte offset, so the effect of branch relaxation on CFI advance-location deltas (which real assemblers re-encode during relaxation) is not modeled.
* Toy model: the results apply to the Lean model Toy.Unwind (one straight-line body, word-addressed downward stack, no return-address slot, CFA = entry sp). These theorems neither establish nor refute the corresponding claims about real compiler-emitted DWARF call frame information or real unwinders; every connection to them is a separately labeled derived modeling bridge.

**R6b** (`offByOne_push_tables_incorrect`):

* One concrete body; not a classification of all off-by-one faults.
* Toy model: the results apply to the Lean model Toy.Unwind (one straight-line body, word-addressed downward stack, no return-address slot, CFA = entry sp). These theorems neither establish nor refute the corresponding claims about real compiler-emitted DWARF call frame information or real unwinders; every connection to them is a separately labeled derived modeling bridge.

**R6c** (`missing_row_after_pop_incorrect`):

* The fault here is the stale CFA rule; a stale register rule alone is not immediately wrong (R6d).
* One concrete body.
* Toy model: the results apply to the Lean model Toy.Unwind (one straight-line body, word-addressed downward stack, no return-address slot, CFA = entry sp). These theorems neither establish nor refute the corresponding claims about real compiler-emitted DWARF call frame information or real unwinders; every connection to them is a separately labeled derived modeling bridge.

**R6d** (`stale_savedAt_after_pop_incorrect_after_slot_reuse`, `stale_savedAt_after_pop_correct_without_reuse`):

* Concrete bodies only; not every later push makes the stale rule wrong (a push that stores the value register 3 had at entry leaves it correct).
* Known not to apply where the freed slot below sp can be written without an operation of the body (for example by an asynchronous signal or interrupt frame on a stack without a protected red zone): the toy semantics has no such writes, and any write of a different value into the freed slot makes the stale rule wrong by the same mechanism as the first body. Derived (modeling bridge).
* Does not say DW_CFA_restore or DW_CFA_same_value is unnecessary in practice.
* Toy model: the results apply to the Lean model Toy.Unwind (one straight-line body, word-addressed downward stack, no return-address slot, CFA = entry sp). These theorems neither establish nor refute the corresponding claims about real compiler-emitted DWARF call frame information or real unwinders; every connection to them is a separately labeled derived modeling bridge.

**R7a** (`checkTable_sound`):

* Proved for the toy language; whether checkTable stays sound for extensions (calls, branches, computed addresses) is not addressed (not proved either way), and any extension needs a new proof.
* The checker checks only registers in cs; rules for other registers are ignored.
* Single-frame virtual unwinding only: TableCorrect does not forbid the body from writing into the caller's frame (addresses >= entry sp; tableCorrect_permits_caller_frame_write) and does not require the body to restore sp or any register by its end (tableCorrect_permits_unrestored_sp).
* TableCorrect quantifies over every entry state, including ones a real ABI excludes (unaligned sp, arbitrary memory); registers and stack words are unbounded integers.
* The relaxation model and the unwind-table model are independent: Toy.Unwind indexes table rows by operation count, not byte offset, so the effect of branch relaxation on CFI advance-location deltas (which real assemblers re-encode during relaxation) is not modeled.
* Toy model: the results apply to the Lean model Toy.Unwind (one straight-line body, word-addressed downward stack, no return-address slot, CFA = entry sp). These theorems neither establish nor refute the corresponding claims about real compiler-emitted DWARF call frame information or real unwinders; every connection to them is a separately labeled derived modeling bridge.

**R7b** (`checkTable_complete`):

* Exactness depends on the toy language: entry values can only be copied, never computed, so a single entry state with pairwise distinct register values above every constant the body writes separates all abstract distinctions. With arithmetic on registers, memory loads through computed addresses or control flow, completeness is not claimed.
* The proof uses unbounded integers for registers and stack words; fixed-width machine words are not modeled. Whether completeness transfers to them is not examined (it needs an entry state whose register values avoid every constant the body writes).
* Straight-line bodies only; no branches, loops, calls, frame-pointer-based CFA, register-to-register saves, val_offset rules or DWARF expressions.
* Not a statement about real CFI validators.
* Toy model: the results apply to the Lean model Toy.Unwind (one straight-line body, word-addressed downward stack, no return-address slot, CFA = entry sp). These theorems neither establish nor refute the corresponding claims about real compiler-emitted DWARF call frame information or real unwinders; every connection to them is a separately labeled derived modeling bridge.

### Escape hatches

Which hypotheses or modeling choices, if changed, defeat the negative results (counterexamples) of this package:

* **R2e (leastness fails) and R4b (minimum size fails)** disappear when distances are monotone: under `DistMonotone` the grow-only result is least (R1c), and with `shortSize ≤ longSize` also smallest (R4a). Removing alignment directives (with `shortSize ≤ longSize`) is one sufficient way to obtain `DistMonotone` (R2b, R2c). Alignment directives that lie outside every branch span also keep `DistMonotone` when `shortSize ≤ longSize`, because by R2a a distance depends only on the sizes inside its span; this is a derived argument, not a separate theorem.
* **R3a (oscillation from a non-bottom start)** disappears when grow-and-shrink starts from all-short and `DistMonotone` holds (R3b), and when grow-only relaxation is used instead (R1a, R1b; `growShrink_two_cycle_controls`). It also disappears on this instance under the current-layout reading `stepGSCurrent` (`osc_stepGSCurrent_reaches_valid_fixpoint`).
* **R3c (oscillation from all-short)** disappears under `DistMonotone` (R3b) and under grow-only relaxation (R1a, R1b). The aligned 4-cycle additionally depends on the counterfactual `setShort` reading of `stepGS`: under the current-layout reading `stepGSCurrent` the same program reaches the valid fixpoint `{0}` after 3 steps (`alignOsc_stepGSCurrent_reaches_valid_fixpoint`). The inverted-size 2-cycle does not depend on the reading (`invOsc_stepGSCurrent_two_cycle`).
* **R1d (bound attained)** concerns the loop's own termination check; the iterate `relax` is already valid after `numBranches` steps on that instance.
* **R6b, R6c (misplaced or missing CFA rows)** are incorrect for every entry state; there is no entry state on which they work. **R6d (stale `savedAt` rule)** is defeated by the absence of a later write to the freed slot: without the later push the same stale rule gives a correct table (`stale_savedAt_after_pop_correct_without_reuse`).

### Hypotheses whose tightness is `unknown`

None. Every one of the 17 hypotheses in the hypothesis ledgers is `tight`, with a kernel-checked counterexample that satisfies all other hypotheses of the theorem and violates its conclusion (statements listed under **Findings**).

### Disproved or dropped statements

None. Every result stated for this package was proved exactly as stated. Two consequences that could have been separate results are kept as auxiliary lemmas without their own result entries: `relax_le_of_valid_of_le_of_noAlign_of_short_le_long` (R1c composed with R2b and R2c) and `checkTable_iff_tableCorrect` (R7a and R7b combined). Auxiliary lemmas mentioned in this report are kernel-checked like everything else in the library (see `audit/axioms.json`) but carry no hypothesis ledger.

### Not examined or unknown

* **Unknown:** general results about the current-layout reading `stepGSCurrent` (for example, whether it can oscillate from all-short with alignment and `shortSize ≤ longSize`); only the three instances listed under R3a and R3c are proved.
* **Unknown:** minimality of the R3c instances in instruction count; only a bounded search over 3-instruction programs exists (see below).
* **Not examined:** NP-hardness or any complexity result for relaxation with alignment; sequential (Gauss–Seidel style) relaxation as a library definition (only the support check in `lean/Search/Sequential.lean` exists); more than two encodings per branch; finite long-branch reach; relocations and linker relaxation; displacements measured from the end of the branch instruction.
* **Not examined:** multi-frame unwinding, frame-pointer-based CFA, `register(R)` and `val_offset` rules, DWARF expressions, control flow and calls in the unwound body, fixed-width machine words, asynchronous writes below the stack pointer, the encoding of rows as CIE/FDE instruction streams, and the interaction of branch relaxation with CFI advance-location deltas.

### Bounded searches and support checks (`[bounded search]`, not proofs)

The scripts are preserved in `lean/Search/` and are not part of the library build; run them with `lake env lean Search/<file>.lean` from `lean/` after `lake build`. Every program generator enumerates programs of exactly `n` instructions in which every branch may target any index `0 … n` (index `n` is the end of the program).

* `lean/Search/LeastnessOptimality.lean`: all programs of exactly 3 instructions over `{fixed 1, fixed 2, fixed 3, align 2, align 4}` and branch targets `0 … 3`, with 10 parameter sets (all with `shortSize ≤ longSize`). Leastness and optimality failures from all-short are found only in programs containing `align 4`, and only with the parameter sets `⟨1,2,2⟩` and `⟨1,3,2⟩`: 16 (program, parameters) pairs fail leastness and 10 fail optimality. Every failing program has one of two shapes: `[branch t, align 4, branch 1]` (the shape of `alignProg` used in R2e and R4b; 8 leastness and 8 optimality failures) or `[branch t, branch 3, align 4]` (8 leastness and 2 optimality failures). The script prints only the first four hits of each search (`.take 4`); removing `.take 4` lists all of them. Grow-and-shrink oscillation from all-short is detected as a difference between the 10th and 11th iterates, counting all-short as the 0th iterate (the 11th and 12th entries of the 12-entry trace). This is exhaustive for programs of 3 instructions: the iteration ranges over at most 2^3 = 8 assignments to the 3 positions, so both iterates already lie on the eventual cycle, and they differ exactly when that cycle is longer than one step. Oscillation is found for exactly two (program, parameters) pairs: `[branch 2, branch 3, align 4]` with `⟨1,2,2⟩` and with `⟨1,3,2⟩`; the first is R3c.
* `lean/Search/OscillationA.lean`, `lean/Search/OscillationB.lean`, `lean/Search/BoundAndCycle.lean`: larger enumerations (4–5 instructions) over smaller alphabets; no result relies on their outputs.
* `lean/Search/Sequential.lean`: defines a sequential grow-only pass and checks by `decide` that on `[branch 3, branch 3, align 4]` with `⟨1,2,2⟩` it stops at a different valid assignment (only branch 0 long) than the simultaneous passes (branches 0 and 1 long). This is a kernel-checked support example, not a library result.

## Evidence

### Kernel-check record

Every name referenced by `results.json`, with its role, the axioms reported by Lean's `collectAxioms`, the SHA-256 of its statement and the SHA-256 of its definition closure (closure size in parentheses), exactly as recorded in `audit/statements.json` and `audit/axioms.json`. Hashing is described under **Revalidation**. All 583 declarations of the library use only `propext`, `Classical.choice` and `Quot.sound` (most use fewer).

| Lean name | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.Relax.align_counterexample_still_terminates_valid` | R2e result; R2e non-vacuity | Quot.sound, propext | `8a00d2a100eeee37bcbea11761925ab8654115f56e0dfa685b7ac99ab247a20c` | `190f32ae1cf754708da81d91bcfb58ca0780e9668a40bd8435e5bfa6aa2f1ba0` (41) |
| `Toy.Relax.align_growShrink_differs_from_growOnly` | R3b counterexample for `hmono` | Classical.choice, Quot.sound, propext | `884d7b0f6e7aa3bf0d29ac5d7f44eba5bcd1cc73d98a66cda5eab8cd0a71d505` | `d2dba0c47ece6a677b9aedfff7087affcf91b90d46cd9f7be91fadf6cf8d384f` (38) |
| `Toy.Relax.align_growShrink_four_cycle_from_allShort` | R3c result; R3c non-vacuity | Quot.sound, propext | `d6dbe843c5d623f55e76eb080b779e22344b99b9d3f697c176e48996234a173b` | `15b90c633df221953ff85c13f08d3d772906bdd85c768091683953cc64156986` (36) |
| `Toy.Relax.align_padding_breaks_leastness` | R1c counterexample for `hmono`; R2e result | propext | `a763295e1d1ca85706d79aaeea4ac85a40fbd471914438a1213609d818e9a79c` | `6deb6dfc65c356a4e64fdacb999c854538ce48ce61fc72ad17e7e199d1b973da` (41) |
| `Toy.Relax.align_padding_breaks_size_optimality` | R4b result; R4b non-vacuity | propext | `925824389f200e1a5aee6e6ea2231e8061db3706f0a4913cdae01c939e7909db` | `ac9c8353e6966d8d5c7e3b5c570aa25ed3b1063ae3206070ec19ffef9ccbc6d8` (41) |
| `Toy.Relax.distMonotone_example_neg_align` | R2b counterexample for `h` | propext | `5cf2c46b9b5d80d649147aed47dadfbcbe113b2d9c66cc770e96f6fb23643dd4` | `c0c8ae31c3d7b570b67562cc66b6a2c40fc723254b2a7588854c7ac20ceec02c` (24) |
| `Toy.Relax.distMonotone_nonvacuity` | R2b non-vacuity | propext | `9aaf0990b494c362b43fd84230f331ab8735303d1eb1d0109b200b0a9d34399e` | `093e0f21c467894a5ae9dab37f168ad70446c2b88efdbf83ff17a2f645e2eb72` (27) |
| `Toy.Relax.distMonotone_of_sizesMonotone` | R2b result | Quot.sound, propext | `5a758fdfc23ecc6fe7e5f981fbad332d640039032363bf83aceb78db591dca63` | `710e4b827cac9833d6b8ae1841b644f8bd7349cded405f455779bbdce6966426` (24) |
| `Toy.Relax.dist_decreases_when_size_between_decreases` | R2a counterexample for `h` | propext | `4cc5a54404af4fbcf6ebd6839a63c4d01058a076fe0f360074556427064a1ab1` | `18d1b4a1faca4a0d1a7601143331d4efe74211b9cd5e4e7893e60fb2e014b54a` (26) |
| `Toy.Relax.dist_le_dist_of_size_le_between` | R2a result | Quot.sound, propext | `2f35ccc3ec245fbecb8b3e4db1ffc4f9317d5d4329e57a8e3e73f186e7b43eec` | `1d4a26cc11a8bdddb00641af2b76fdc56f44f9b3c0831732e0423350ccbbf0a3` (21) |
| `Toy.Relax.dist_mono_nonvacuity` | R2a non-vacuity | Quot.sound, propext | `6dce0ed0ef69a4361f9c89dfbcf2f9937919832339013ad44db94f6c6a530fb4` | `7d187c543726f7fb9b443a97a94e74abc9d292185a3e15697264206d947a8d8e` (25) |
| `Toy.Relax.growShrink_allShort_nonvacuity` | R3b non-vacuity | Quot.sound, propext | `328bfe30474222ec2feb6e676202356fca553a16ad034d1e6f75898271e850cb` | `b43c0ad8fdf120483382eb4eefd0677af92131bcb0f6e81472f97057a401542d` (35) |
| `Toy.Relax.growShrink_two_cycle_controls` | R3a non-vacuity; R3a control | Quot.sound, propext | `bea4ea989cdea9e9ca2874689563c287440e4d4f6163732a8c2bd37dea88e23c` | `7b9f368ef2e3e7e7e0fa931d7c73234765ceba96c37ef8d079cfd4b325621454` (42) |
| `Toy.Relax.growShrink_two_cycle_from_nonbottom_start` | R3a result | Quot.sound, propext | `9ba54e08753b17b06c59bca41d18982f25019dfcca7222e9157fa41c0aa160dc` | `30e0b879abfb364acad9043c988d89b6d19d0cc213e849164e49b94635fa120e` (39) |
| `Toy.Relax.inverted_growShrink_two_cycle_from_allShort` | R3c result | Quot.sound, propext | `a499c3c9bf121bc8bee49c26a907bf7cabbf1ee7e4b66a2138cbf4526bc34c56` | `74b0f65dfb817efa213914467687e9622a2fdd119e48023aa1aac925c388ab41` (40) |
| `Toy.Relax.iter_stepGS_allShort_eq_iter_step_of_distMonotone` | R3b result; R3c control | Quot.sound, propext | `6270a31857f6d8ddec979862400ad2b5472ad3d0af3cbd0b6936b4b20d05b906` | `f24ae97d110a92241d4e2f96450894c524bcc367896259045fb41168eea91a19` (35) |
| `Toy.Relax.leastness_needs_upper_bound_above_start` | R1c counterexample for `hab` | Quot.sound, propext | `d32f3127e298951636f08ec1cbf2c847d0c2056003c80430dd8fc025d919d1a6` | `a048a0c993a53df0f307ca4c98bb166136079fb0f2f286598d6be26378c63925` (45) |
| `Toy.Relax.leastness_needs_valid_upper_bound` | R1c counterexample for `hb` | Quot.sound, propext | `7cbe0afc467888c5ef1a73ba5c3f0299dcb35f2a0860fe6a740a5256ed149f6b` | `bb60ab5a2cf31bdf41b70f851630d702fa6314e3c186be4d0a03c1754c95e9e7` (43) |
| `Toy.Relax.noAlign_needed_for_sizesMonotone` | R2c counterexample for `hna` | propext | `414b978977db3aa5e642344200aa1a644c378761ffc3c7ebb3233a75e228994b` | `c2850c4380ff48aed45ef72f9f6f7939497851e2cd6e2156ba97d8a7f8082602` (24) |
| `Toy.Relax.promote_relax_landsExactly_needs_sizesPositiveAt_after` | R5 counterexample for `hposR` | propext | `436cfe754950f00d1f45ae2a2108b709d5737179a263ca9c5ce2a0f805f2a11d` | `343ace1efae1c4210259eb96960b2b72beb3bdeb580c633bcb1492d342c87586` (45) |
| `Toy.Relax.promote_relax_landsExactly_needs_sizesPositiveAt_before` | R5 counterexample for `hposA` | propext | `430570b335558e4f0acc4f356af267157012d0177ac7eafd61745e2ab0afdd8e` | `3a0270ed92403b4c1e4896f29e2316c83e805f00b5e22c2987bc3899ec424f05` (45) |
| `Toy.Relax.promote_relax_landsExactly_needs_valid` | R5 counterexample for `hv` | propext | `8cc7500840fa849f7482d18606f6fdd9ed1f0a330f1b2a2d5feb232ee44cfab3` | `661d7258897dd1316fa1acf547f6e2ca63e2c5f75dfebe4a9c9c92bc9a4c617c` (44) |
| `Toy.Relax.promote_relax_landsExactly_of_valid_of_sizesPositiveAt` | R5 result | Quot.sound, propext | `c2bfaba4d1bdbf1d245f72bc700c5ce41a8ee61782e70de52b853592f9345e94` | `e6760e9b654a0b6509cb6f99219057b4e9f5a65f69edcb4204b19a9d7380fea1` (42) |
| `Toy.Relax.promote_relax_nonvacuity` | R5 non-vacuity | propext | `6c26719fc8cfd93871b0e1639c5e9d8b581f59337ffc62a3cfa7815bd4d7fc2a` | `6353985aa1a98d000fd8602f89cf25e44460e2c289434603a57b46ed83e229db` (41) |
| `Toy.Relax.promote_without_relax_breaks_emitDisp` | R5 control | propext | `fd26617f8f74fdb0260953bfcd1f5346aa0020502e3a786495802db87d4857bf` | `3104c17d46a619a4c7c5270339daa2dbd8d3c006e415ba82828ee662d24be05a` (41) |
| `Toy.Relax.relaxLoop_numBranches_passes_insufficient` | R1a control; R1d result; R1d non-vacuity | propext | `c51e47645257121c921eb343075b372a56ebbb7200cd2431e015d419e10d6e21` | `43822d4bfe50a40007f3356c7a92ae0369990ff98644ddf0b12a8fd88a4f761c` (40) |
| `Toy.Relax.relaxLoop_returns_relax_within_numBranches_succ` | R1a result | Quot.sound, propext | `96ff58b1301973840908d0bbf78aa9ab9385d61be8b703e0f39273104a96e3eb` | `10082df87a5a86255cb44f3a9ee7360cbb147d80bfeeb4d4f331c634e4615180` (37) |
| `Toy.Relax.relax_allShort_totalSize_le_of_valid_of_distMonotone_of_short_le_long` | R4a result; R4b control | Quot.sound, propext | `6a046c9154eaba1eca11e3ded28f6cb026ca13a89a084070f66ed292a17d1aac` | `6490d836836826a38afcb0bda9fb6532a5a99bf80da1b4368fa7ce8a09242ca4` (39) |
| `Toy.Relax.relax_le_of_valid_of_le_of_distMonotone` | R1c result | Quot.sound, propext | `35c0ba2370ff25b5b84abe876f7ed195f1fc1850535f17e7d8797ef78dfb1a4e` | `048f579d2ce3749a4865bf508bac0341d1d8912cf8d292c5b7274f8f8f7e85f9` (37) |
| `Toy.Relax.relax_le_of_valid_of_le_of_noAlign_of_short_le_long` | R2e control | Quot.sound, propext | `9c1221be3c2d11afb171de0202fdae1f82c890fdae0d3c349010978af6217c5b` | `ce166e894c8386b183622a9afaa3e2282170e410e7e5d4786f82f298a240d447` (40) |
| `Toy.Relax.relax_least_nonvacuity` | R1c non-vacuity | Quot.sound, propext | `5003e2c182fa44ff9828dd44fe864caf1252db949ddf9c20fa427e34aecb2864` | `710fda9497c8c0d1a06109f54fcc2bd57527713d06c7eb2535cdc747f16173f1` (41) |
| `Toy.Relax.relax_nonvacuity_chain` | R1a non-vacuity; R1b non-vacuity; R1d control | Quot.sound, propext | `26d7c68bb14283a8449da5f5049d330c0473cb5107cd91f3ada69846ea80c226` | `74f2406583896e4a4449f3b8ccbe743341b3467257c1b1c1684145d11bc12e44` (41) |
| `Toy.Relax.relax_valid_and_above_start` | R1b result | Quot.sound, propext | `53afd666d78ecb68c99e1f5336473d8290d3f8b1dca53f2878d73bd4caf5466b` | `dec59be0885d8b5e65551afb0c5a764beabf3acb438e348dd933a5da838d42a6` (36) |
| `Toy.Relax.short_le_long_needed_for_sizesMonotone` | R2c counterexample for `hsl` | propext | `d558e8ab5156559b10d99ea717d668fdfac4f6f7bd8533e931c8f40494d4a4c4` | `bc7c092e45e1cbc4536a888ac14c6349e6c2a537adc7c06dbb2896fd729b0228` (29) |
| `Toy.Relax.size_optimality_needs_distMonotone` | R4a counterexample for `hmono` | propext | `4ecd1dd2f94a9b55b1bf289a022fc9921a5a882671bdc9f50aabce6c566886eb` | `ac9c8353e6966d8d5c7e3b5c570aa25ed3b1063ae3206070ec19ffef9ccbc6d8` (41) |
| `Toy.Relax.size_optimality_needs_short_le_long` | R4a counterexample for `hsl` | Quot.sound, propext | `a9d1622b1f33d575e4cef7f05d2c000291c694ebfa9e89017820d219d8937280` | `57beb33d4bc5a8769147bad82798e0a0385ba114b4f4be0e48aee597e85c83dd` (42) |
| `Toy.Relax.size_optimality_needs_valid` | R4a counterexample for `hb` | Quot.sound, propext | `ec3c512cecf55d56917e8b6bfbebb30778f45b0bd24c1fc000ea28fdcb912ed0` | `3986ab20822dc343bf4ec2b73cd9337b1ae3857533b2c58499f53e73f4c73e37` (41) |
| `Toy.Relax.size_optimality_nonvacuity` | R4a non-vacuity | Quot.sound, propext | `b70bff65b067f5f3a58e57ca364ccacdfa788a3304549b64f0d560dc8c589935` | `9ba961ac4fd376429a6472f2e6c83138656e34132bb022b0fd56740e818d04c6` (42) |
| `Toy.Relax.sizesMonotone_nonvacuity` | R2c non-vacuity | propext | `572fcd7e47c2908a07bad7eef461fe51c6d872dec1e3645db69585edb51569a9` | `b380ca3aadc16746cceac047b887ed2b694951ef5ba9aa112e5821bae52741ec` (29) |
| `Toy.Relax.sizesMonotone_of_noAlign_of_short_le_long` | R2c result | propext | `8b7b2b85e26b7ce4ecef33a8c6fc999b8f3091742b17603be612a3f88fcbf6f2` | `d43bf4e01e9215d6d14c0378d3d19d43f668bd2b53d34d66ba7e877aaa91bb68` (27) |
| `Toy.Relax.stale_displacement_lands_elsewhere` | R5 control | propext | `c34bf0100bd74302c4834d2dd988e2c711f30bf7bc9c028869b89e6cd9bf94a8` | `b469e041fbcce6aa4dbd69013bc81503d20bd003f0f6898a7b23ec8e7cbde5f3` (41) |
| `Toy.Unwind.checkTable_complete` | R7b result | Quot.sound, propext | `fb5ac70c7a5be1199f7f024db098f9e60e076c17c59c587d4a4346dd841fa602` | `5508f936f3ef81ae3f6c4cad89dca5cd575f38300c7f1ece0d1dd1ee1711b6bb` (61) |
| `Toy.Unwind.checkTable_nonvacuity` | R7a non-vacuity | none | `f3055e78789b709a327e605200b4f1b5cab489454ad05b8735a665e6950471f7` | `ff6814c88415ed325d05ad2e3b401b64f5dde3fef36e8956e9fb8c62ae94ab6c` (56) |
| `Toy.Unwind.checkTable_sound` | R7a result | Quot.sound, propext | `a24b09ef3eb732680d8bcd7424e8b662cc1316c0c5083392a5ee788a418d3aff` | `5508f936f3ef81ae3f6c4cad89dca5cd575f38300c7f1ece0d1dd1ee1711b6bb` (61) |
| `Toy.Unwind.checker_premise_needed` | R7a counterexample for `h`; R7b counterexample for `h` | propext | `513b1dab20e42fca77557fe4b0eb1d52b8399f7bee5c7e98a44a3cb28119dc97` | `755d58b6e68a244b02790baab4cf4468a6c2a2071e5840e2d327a0d6764b14b6` (67) |
| `Toy.Unwind.genTable_correct_of_no_undefined` | R6a result | Quot.sound, propext | `ee7b49cabc992af6287466d814c720a7844bb66d86894267809da79028fabb09` | `377c7165485c6802335667e52b967313e4ff27479031d3207967adad0dd5ddc8` (61) |
| `Toy.Unwind.genTable_no_undefined_nonvacuity` | R6a non-vacuity | none | `fb402549676170d247244e65f1c4f466ad2f4c6c55df7679b0bb49b3da82fcd3` | `e3639422c8a11b91c1a30ce3e17cd788272734daaeb228408be33b7752acb67d` (47) |
| `Toy.Unwind.genTable_with_undefined_incorrect` | R6a counterexample for `h` | Quot.sound, propext | `6098bb941393642067bbd5bb035fa58911f424376f7b3303e36e9a225c784c42` | `cb60d4b7af4cb467e87c9d4556c238269ff6b21c068b8fc449fb412ae0760dce` (62) |
| `Toy.Unwind.missing_row_after_pop_incorrect` | R6c result | propext | `6ccfb743fb5eaaaacf8f9ee79adef087b7c1817f503a12d4a499af74cdc9302d` | `d4bbe26c53d829d08e20ee2bcf61fa1a77cf72d6163cfe3df345bab72124e9ec` (64) |
| `Toy.Unwind.offByOne_push_tables_incorrect` | R6b result | propext | `d5d166ef2e56a9374660074f77750cbfba6d95133f7a6a82d91d1ac697407d83` | `78b5de812da78cc63cd99912453da9de39965a44546a5144d7dea0e71c84abd7` (65) |
| `Toy.Unwind.stale_savedAt_after_pop_correct_without_reuse` | R6d result | Quot.sound, propext | `5cde27567f5d63ff3001642e7b8bc890c9b5b4722cde6e4b6121e69c9603390f` | `18f595d6b65a7f4afbb1e033a2bb3b7fbea2c22a9315738bb3f90804609576a6` (64) |
| `Toy.Unwind.stale_savedAt_after_pop_incorrect_after_slot_reuse` | R6d result | Quot.sound, propext | `0779f77049c597307a09aab95caf4e6bd53cdd77ad1e87dff0cdf084904b7257` | `b662128da8e02f179d6427524f785dd5cfc77b7ecd689fd731642647ce12dc80` (64) |
| `Toy.Unwind.tableCorrect_example_pos` | R6b non-vacuity; R6b control | Quot.sound, propext | `2ee322cb0a0ce077f2337ce9dcde1cf33278219866696724d862beb49e9c55bf` | `55512470e6200dac1418af746fe20a1d1fd5c927219b563d6c13afc4c9091e0d` (63) |
| `Toy.Unwind.tableCorrect_example_pos_pop` | R6c non-vacuity; R6c control | Quot.sound, propext | `a0b35d850946b4731e7a0548d8bc1f7b13f3431ae0bdbeb2194c981d6e13c3de` | `25e89e10c3436e157da36e65eb0bb19b8e711015877266126d2193beb6fa100b` (63) |
| `Toy.Unwind.tableCorrect_example_pos_reuse` | R6d non-vacuity; R6d control | Quot.sound, propext | `f30c7f26df3377226e34fb1c48dbd920c63cbdf24abc82ece3d5b0c95b26dd4a` | `de2495aff19f63bdb93b16f8131272e249f97d61e2803ecf8d01dcf2aa04bfd7` (63) |
| `Toy.Unwind.tableCorrect_nonvacuity` | R7b non-vacuity | Quot.sound, propext | `9b9697ee301cc3a8b781aee6472060e52ac55cbae03ca55b24acfe3bf91df53e` | `e96fd6106b9c8771de43038791bc8919bb1bdd73cfd61b08fa5ba5514a5af5fa` (65) |

### Toolchain

* Lean 4, repository `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` (the GitHub ref `refs/tags/v4.34.1` points directly at this commit; `lean --version` of the toolchain used reports `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`).
* Lake project: `lean/lakefile.toml` (package `toy_relax`, one library `ToyRelax`, no `[[require]]`), `lean/lean-toolchain` = `leanprover/lean4:v4.34.1`, `lean/lake-manifest.json` with no packages.
* Banned constructs: the Lean sources contain no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC`.

### Primary sources (accessed 2026-11-20)

Statements attributed to papers whose full text was not read are taken from their abstracts only; this is stated per entry.

* T. G. Szymanski, "Assembling code for machines with span-dependent instructions", Communications of the ACM 21(4):300–308, April 1978, doi:10.1145/359460.359474. Bibliographic data and abstract only; full text not read.
* B. W. Leverett and T. G. Szymanski, "Chaining span-dependent jump instructions", ACM Transactions on Programming Languages and Systems 2(3):274–289, July 1980, doi:10.1145/357103.357105. Bibliographic data and abstract only; full text not read.
* G. Frieder and H. J. Saal, "A process for the determination of addresses in variable length addressing", Communications of the ACM 19(6):335–338, June 1976, doi:10.1145/360238.360241. Bibliographic data and abstract only; full text not read.
* A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2):285–309, 1955, doi:10.2140/pjm.1955.5.285. Cited for the standard statement of the theorem only.
* J. Boender and C. Sacerdoti Coen, "On the Correctness of a Branch Displacement Algorithm", TACAS 2014, LNCS 8413, pp. 605–619, Springer, doi:10.1007/978-3-642-54862-8_53; preprint arXiv:1209.5920. Abstract only; full text not read.
* Y. K. Tan, M. O. Myreen, R. Kumar, A. Fox, S. Owens, M. Norrish, "The verified CakeML compiler backend", Journal of Functional Programming 29 (2019), e2, doi:10.1017/S0956796818000229. Source read at repository `CakeML/cakeml`, commit `2874b664e10939a3ee462215b2e068c89c1f70eb`: `compiler/backend/lab_to_targetScript.sml` (`enc_line`, line 39; `enc_lines_again_def`, line 118; `upd_lab_len_def`, line 156; `remove_labels_loop_def`, line 285) and `compiler/backend/proofs/lab_to_targetProofScript.sml` (`remove_labels_thm`, line 6299).
* CompCert, repository `AbsInt/CompCert`, commit `2685140bf72c959446981fb99b5e44a8975021bc`: `backend/Asmexpandaux.ml` lines 191–249 (module `Branch_relaxation`, beginning at the comment `(* Branch relaxation *)`), `backend/Mach.v` lines 39–50 and 97–100 (`Mgetstack`/`Msetstack` as stack-pointer-relative loads and stores), `x86/Asm.v` line 266 (`Pcfi_adjust (n: int)`) and lines 979–992 (instructions "not generated directly by [Asmgen], so we do not model them").
* LLVM, repository `llvm/llvm-project`, commit `ef02d46bb33d10383f6ba5a5d9a5511416ee790c`, `llvm/lib/MC/MCAssembler.cpp`: `MCAssembler::layout` lines 699–709 ("Layout until everything fits."), `MCAssembler::relaxInstruction` lines 879–910, the LEB comment at line 941 ("only increase an LEB fragment size here, not decrease it. See PR35809."), `MCAssembler::relaxDwarfCallFrameFragment` lines 1043–1061, `MCAssembler::relaxOnce` lines 1137–1176 with the pass cap comment at lines 1164–1167.
* DWARF Debugging Information Format Committee, "DWARF Debugging Information Format Version 5", February 13, 2017, https://dwarfstd.org/doc/DWARF5.pdf: Section 6.4 "Call Frame Information" (pp. 171–173) and Section 6.4.2.3 "Register Rule Instructions" (`DW_CFA_restore`, item 11, p. 180). The item number of `DW_CFA_same_value` within Section 6.4.2.3 is not cited because it was not checked against the PDF.
* T. Bastian, S. Kell, F. Zappa Nardelli, "Reliable and fast DWARF-based stack unwinding", Proc. ACM Program. Lang. 3(OOPSLA), Article 146 (October 2019), 24 pages (146:1–146:24), doi:10.1145/3360572. Full text read (open-access PDF at https://fzn.fr/projects/frdwarf/frdwarf-oopsla19.pdf): Section 2.1, Fig. 3 (p. 146:6, an incorrect `.eh_frame` table generated by clang), Fig. 4 (p. 146:8, hand-written `.eh_frame` bytecode in glibc's `lowlevellock.h`), Section 2.2 (from p. 146:8) and Section 4 (p. 146:18).
* Y. Wang, P. Wilke, Z. Shao, "An abstract stack based approach to verified compositional compilation to machine code", Proc. ACM Program. Lang. 3(POPL), Article 62 (January 2019), 30 pages, doi:10.1145/3290375. Bibliographic data and abstract only; full text not read.

### Observation date

All Lean evidence (build, axiom audit, statement and closure hashes) and all source checks recorded above were acquired on 2026-11-20.

## Revalidation

Requirements: `elan` (so that `lake` selects the toolchain pinned in `lean/lean-toolchain`) and `python3`. No network access is needed after the toolchain is installed, and no file of the package is modified.

**Primary check.** From the package directory, run:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory, runs `lake build`, rejects any Lean source containing `sorry`, `admit`, `native_decide` or an `axiom` declaration, and then runs a generated Lean program (embedded in the script) that

1. computes, with Lean's `collectAxioms`, the axioms of every declaration in the `ToyRelax` modules and fails if any declaration uses an axiom other than `propext`, `Classical.choice`, `Quot.sound`;
2. for every Lean name referenced by `results.json` (fields `lean`, `nonvacuity_witness_lean`, `positive_control_lean` and every hypothesis `counterexample`) and every name in `audit/statements.json`, computes the **statement hash** — SHA-256 of the UTF-8 text of `repr` of the declaration's type (the elaborated `Expr`) — and the **closure hash** — SHA-256 of the newline-joined, sorted list of entries `name : repr(type)` (followed by ` := repr(value)` for non-theorems) over every package-local constant reachable from the statement's type through types, definition bodies and inductive constructors (theorem bodies are excluded) — and compares both, together with the closure size, with `audit/statements.json`.

Expected output on an unchanged package:

```text
ok   lake build
ok   axioms (583 declarations)
ok   statement hashes (56 hashed names; 0 referenced names exist but carry no recorded hash)
REVALIDATED
```

A passing run establishes that the recorded statements, with the recorded definitions, are kernel-checked under the pinned toolchain with standard axioms only. It does not re-check the prose of this report against the statements; for that, compare each result's Lean statement under **Findings** with `#check` output (below).

**Manual commands.** From `lean/`:

```sh
lake build                              # builds the library target ToyRelax
lake env lean RevalidationAudit.lean    # prints #check and #print axioms for every name referenced by results.json
lake env lean Search/Sequential.lean    # support check (decide), not a library result
lake env lean Search/LeastnessOptimality.lean   # bounded search; prints its findings
```

`lean/RevalidationAudit.lean` is outside the library target. For each of the 56 names it prints the pretty-printed statement (the same form as the Lean statements quoted under **Findings**, with namespaces `Toy.Relax` and `Toy.Unwind` opened) and the `#print axioms` line, which must list only a subset of `propext`, `Classical.choice`, `Quot.sound`.

**After a change.** If a definition in `lean/ToyRelax/Relax/Model.lean` or `lean/ToyRelax/Unwind/Model.lean` changes, the closure hashes of every dependent result change and `support/revalidate.py` fails; the affected results must then be re-examined rather than assumed to carry over. A toolchain change can alter `repr` output and hence the hashes even when the mathematics is unchanged; in that case re-run the build and axiom audit, and compare the `#check` output of `lean/RevalidationAudit.lean` with the statements quoted in this report.
