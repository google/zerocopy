# DWARF-style call-frame information over CFG layouts with a state stack, and call-site-table landing-pad unwinding: a kernel-checked toy model

## Summary

This package is a Lean 4 model (namespace `Toy.CFI`, no Mathlib) of DWARF-style call-frame information (CFI) for machine functions whose basic blocks are laid out linearly in an order that need not follow control flow, of a `remember_state`/`restore_state` state stack, of call-site (LSDA-style) tables that map call PCs to landing pads, and of multi-frame unwinding that combines both. It contains 18 kernel-checked results. Model–system relation: none proved. Every result is a statement about the toy model; it neither establishes nor refutes the corresponding claims about real compilers' CFI emission (such as LLVM's CFIFixup and CFIInstrInserter passes), real unwinders and personality routines (such as LLVM libunwind and libc++abi), or the DWARF specification and the Itanium C++ ABI's exception-handling rules; statements about real compilers, unwinders and ABIs are separate *derived (modeling bridge)* claims. Here "correct" (`TableCorrect`) means: at every PC of every reachable state, for every caller and memory, the program's row computes the caller's CFA and the caller's values of the callee-saved registers `fp` and `s1`.

- **R1** (`genCFI_tableCorrect_of_sound_recoverable_annotation`; theorem, T1, substantive): if every non-empty block appears in the layout, the per-block annotation of abstract frame states is sound (implied by the entry state and consistent with every CFG edge), and at every PC of every annotated block the abstract state entails some row, then the program emitted by the toy generator `genCFI` (row deltas inside blocks; at layout boundaries `remember_state`/`restore_state` or an explicit re-definition) is `TableCorrect`.
- **R2** (`no_tableCorrect_of_conflictingCfaOffsetsAt`; impossibility, T1, shallow): if at some PC every register's offset from the CFA varies across reachable states (`ConflictingCfaOffsetsAt`, e.g. a merge point reached with and without a push), then no CFI program whatsoever is `TableCorrect` for the function (CFA rules are register + offset).
- **R3** (`coldBlocks_no_row_recovers_at_both_epilogue_ret_and_cold_entry`; impossibility, T1, shallow): for the blocks of the example function `coldFn` (prologue, epilogue, and a cold block entered with the frame established that jumps to the epilogue), in every layout no single row recovers the caller both at every reachable state of the epilogue's `ret` and at every reachable state of the cold block's first PC.
- **R3b** (`coldFn_not_tableCorrect_of_cold_entry_row_eq_epilogue_ret_row`; impossibility, T1, shallow): for `coldFn` laid out as blocks 0, 1, 2 (cold block directly after the epilogue's `ret`), any CFI program whose row at the cold block's address 6 equals its row at the `ret`'s address 5 is not `TableCorrect`.
- **R3c** (`naiveCFI_coldFn_cold_entry_cfa_is_true_cfa_minus_one`; counterexample, T0, definitional): the naive emitter `naiveCFI` (deltas only at frame-affecting instructions, nothing at block boundaries) gives `coldFn`'s cold block the post-epilogue row CFA = sp + 0, which computes CFA - 1 at every reachable state there.
- **R4** (`probeLoop_cfa_correct_at_every_iteration_iff_fp_anchor`; characterization, T1, shallow): for the stack-probing loop `probeFn page` with `page > 0`, a row computes the correct CFA at every reachable state of the loop PC (every iteration, caller and memory) if and only if its CFA rule is fp + 1, i.e. anchored in the frame pointer rather than in the moving sp.
- **R4b** (`spRelative_cfa_right_on_entry_wrong_after_first_iteration_of_pos_page`; counterexample, T1, shallow): for `page > 0` and any register rules, the SP-relative row CFA = sp + 1 is right on loop entry and off by `page` after the first iteration, and the SP-relative table `probeSpCFI` is not `TableCorrect` for `probeFn page`.
- **R5a** (`lookupFirst_eq_result_of_uniqueAt`; theorem, T0, shallow): if `e` is an entry of a call-site table, `e` contains `pc` (half-open range), and no entry with a different value contains `pc` (`UniqueAt`), then first-match lookup returns `e`'s outcome (its landing pad or 'no landing pad').
- **R5b** (`lookupFirst_eq_notFound_iff`; characterization, T0, shallow): for every call-site table, first-match lookup reports 'not found' exactly when no entry contains `pc`.
- **R5c** (`lookupScan_eq_result_of_sorted_uniqueAt`; theorem, T0, shallow): for a call-site table sorted by start address (`SortedByStart`) with `UniqueAt t pc`, and an entry `e` of the table containing `pc`, the early-exit scan `lookupScan` returns `e`'s outcome.
- **R5d** (`uniqueAt_of_nonOverlapping`; theorem, T0, shallow): if the ranges at distinct positions of a call-site table are pairwise disjoint (`NonOverlapping`), then `UniqueAt t pc` holds at every `pc`.
- **R5e** (`lookupIncl_wrong_on_adjacent_ranges`, `lookup_at_return_address_misses_last_call_in_range`; counterexample, T0, definitional): on the sorted, non-overlapping table [0,4) -> 1, [4,8) -> 2, a lookup with an inclusive end returns the wrong outcome at 4 and at 8, and looking up the return address 3 + 1 of a call at 3 (instead of return address - 1) returns landing pad 2 instead of 1.
- **R6** (`unwind_caught_at_first_handler_frame_with_caller_registers`; theorem, T1, substantive): if the true states of frames 0..j form a call chain, the tables of frames 0..j are `TableCorrect`, the toy personality routine `frameAction` skips frames 0..j-1 and returns `handle lp` at frame j, the call-site rows of frames 1..j use sp or a callee-saved register as CFA base, and the throw-time memory still holds the save slots read by the call-site rows of frames 1..j-1, then unwinding stops at frame j with landing pad `lp` in a state that agrees with frame j's true state on sp, `fp` and `s1` (memory: the throw-time memory), and frame j's row at its call PC computes frame j's true CFA and frame base.
- **R6c** (`unwind_caught_at_first_handler_frame_of_sorted_unique_lsda`; theorem, T1, shallow): the same conclusion holds when the personality outcomes are replaced by conditions on the call-site tables: the tables of frames 0..j are sorted with at most one distinct entry value containing the call PC, frames 0..j-1 have no table or a covering entry without landing pad, and frame j's table has a covering entry with landing pad `lp` (together with the call-chain, table-correctness, CFA-base and save-slot hypotheses).
- **R6b** (`recovers_of_reads_agree`; theorem, T0, shallow): a row that recovers caller `c` from a state also recovers `c` from any state that agrees with it on the row's CFA base register, on the callee-saved registers whose rule is 'same', and on the memory at the save slots read by 'offset' rules.
- **R7** (`checkCFI_sound`; theorem, T1, substantive): if the decidable checker `checkCFI` (forward abstract interpretation with join to one entry state per block, then a per-PC check that the program's row is entailed by the abstract state) accepts a CFI program, the program is `TableCorrect`.
- **R7b** (`checkCFI_incomplete`; counterexample, T1, shallow): `checkCFI` is incomplete: for `incFn` (CFA anchored in the scratch register `t1`, a loop moving sp, then a store and reload of `fp` through `[sp]`) the table `incCFI` is `TableCorrect` but `checkCFI` rejects it.
- **R7c** (`reach_inv_of_annSound`; theorem, T0, shallow): under a sound block annotation, every state reachable at offset k of block b satisfies the abstract state obtained by running the abstract transfer function over the first k operations from b's annotated entry state.

The most important qualifications: the call operation is a state-preserving no-op (callee effects, including clobbering of the scratch register `t1`, are not modeled), empty basic blocks are unenterable, rows exist at every PC with one address unit per operation, and unwinding is a single pass over a given frame list with no type matching or cleanups. What each result does *not* show is listed first under **Boundaries**; read those non-claims before relying on any result.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**This is a toy model.** All definitions live under `Toy.CFI` in the Lake project `lean/` (library `ToyCFI`), checked with Lean `leanprover/lean4:v4.34.1` using core Lean and `Std` only (no Mathlib, no `[[require]]` dependencies). The definitions are meant to capture the frame-related parts of: a machine function's CFG and its linear block layout; DWARF call-frame rows (CFA = register + offset; callee-saved register rules 'same value' and 'saved at CFA + N'); the CFA instructions `def_cfa`, `def_cfa_register`, `def_cfa_offset`, `offset`, `restore`, `remember_state`, `restore_state` and `advance_loc`; a CFI emitter for non-control-flow layouts in the style of LLVM's CFIFixup and CFIInstrInserter passes; a static table checker based on abstract interpretation; an Itanium-style call-site table with half-open ranges as scanned by libc++abi's personality routine; and iterated caller-state reconstruction as performed by an unwinder such as LLVM libunwind.

The subjects listed in `REPORT.json` relate to the results as follows. The Lean toolchain release is the checker of every kernel-checked statement. The papers, specifications and source revisions are prior art and modeling references: each is connected to the toy model by explicitly labeled *derived (modeling bridge)* prose, not by any proved relation, and none of them was executed or compared against the toy definitions. In particular, no output of LLVM's passes, libunwind or libc++abi was compared with the toy generator, checker or unwinder.

### Model fidelity

Each toy object, what it is meant to capture, and the known gaps:

| Toy object | Meant to capture | Known gaps |
| :--- | :--- | :--- |
| `Reg = sp, fp, s1, t1`; `calleeSaved = [fp, s1]` | stack pointer, frame pointer, a callee-saved register, a scratch register of an ABI | 4 registers; no return-address column |
| `Op` (`push`, `pop`, `subSp`, `addSp`, `movReg`, `saveAt`, `restore`, `call`, `ret`), `step` | frame-affecting machine instructions | every op is one address unit; arithmetic only on `sp`; `call`/`ret` leave the state unchanged (callee effects not modeled; in particular the scratch register `t1` and all memory survive a call); no branch conditions |
| `Func` = blocks + successor lists + `layout` | a machine function's CFG and the linear placement of its blocks | entry is block 0; one contiguous range (no hot/cold section split, one FDE) |
| `Caller`, `entryState` | the caller-side truth an unwinder must recover | CFA = `sp` on entry (the return-address slot is omitted, so the caller's `sp` equals the CFA) |
| `Reach f c m b k st` | states reachable at PC `(b, k)` along CFG paths | all CFG paths are feasible; empty blocks are dead ends (a CFG projected to frame-affecting operations must contract or pad blocks that become empty); independent of the layout (`Reach.layout_irrelevant`) |
| `Row`, `RegRule = same / offset k`, `initRow` | a DWARF CFI row: CFA = register + offset, per-register rules `same value` / `offset(N)` (saved at CFA+N) | no `undefined`, `register`, `val_offset`, expression rules; no `DW_CFA_def_cfa_expression` |
| `CFIInst`, `execInst`, `rowAt?` | CFA instructions `def_cfa`, `def_cfa_register`, `def_cfa_offset`, `offset`, `restore`, `remember_state`, `restore_state`, `advance_loc`, interpreted linearly with a state stack | instructions located at addresses `<= pc` apply at `pc`; `restore_state` on an empty stack has no row; advances in address units |
| `Recovers`, `TableCorrect` | per-PC unwind-table correctness for every caller, memory, reachable PC and reachable state | only CFA and callee-saved registers are recovered |
| `SymVal`, `AState`, `xfer`, `Inv`, `entails`, `leqA`, `stateRecoverableB` | an abstract interpretation of frame state: registers and stack slots as CFA-relative values or caller values | stores through a non-CFA-relative address forget all slots; loads from such addresses are unknown |
| `annSoundB`, `checkWith`, `inferEntries`, `checkCFI` | a static checker replaying the abstract interpretation along the CFG and comparing rows at each linear PC | inference is fuel-bounded (fails closed) |
| `genCFI`, `naiveCFI` | a CFI emitter for linear layouts with `remember_state`/`restore_state` or explicit re-definition at block boundaries; an emitter that attaches CFI only to frame-affecting instructions | rows at every PC; no encoding-size concerns |
| `CallSite`, `LSDA`, `lookupFirst`, `lookupScan`, `lookupIncl` | a call-site table `[start, stop) -> landing pad` and its scans | unit addresses; landing pads as plain numbers; no action table |
| `Frame`, `frameAction`, `unwindRegs`, `unwindFrom` | per-frame personality decision and iterated caller-state reconstruction | single pass (no two-phase protocol), no cleanups, no type matching; the frame list (function, program, table, call PC of every outer frame) is given, not recovered from return addresses; `Row.rules.sp` is ignored (the caller's `sp` is the CFA) |

Further known gaps that affect every result: addresses are abstract unit-size PCs; there is one FDE per function (no hot/cold section split); there is no return-address column; the caller's `sp` equals the CFA (the return-address slot is omitted); all CFG paths are treated as feasible (branch conditions are ignored); `TableCorrect` demands correctness at every PC (asynchronous unwinding), not only at call sites.

## Findings

Lean blocks below are copied verbatim from the package sources (`lean/ToyCFI/*.lean`). The first line of each block is a comment `-- lean/ToyCFI/<File>.lean:A-B` giving the quoted source lines. Definitions, structures and inductive types are quoted in full; a theorem is quoted with its complete statement up to its top-level proof `:=` (on line B), and the proof is elided as `:= …`. Every card-referenced declaration is kernel-checked and uses only the axioms recorded under **Evidence**. Card identifiers (R1, R2, ...) are the `id` fields of `results.json` in this package.

### Definitions

Each group lists its proved positive (+) and negative (−) examples, followed by the definitions. These definitions are part of the definition closure that is hashed for every result (see **Evidence**).

#### Machine

Examples: + `step_push_example`; − `step_push_moves_sp`.

`Toy.CFI.Reg` (`lean/ToyCFI/Machine.lean:21-28`):

```lean
-- lean/ToyCFI/Machine.lean:21-28
/-- Toy register names: the stack pointer `sp`, the frame pointer `fp`, one more
callee-saved register `s1`, and one scratch (caller-saved) register `t1`. -/
inductive Reg
  | sp
  | fp
  | s1
  | t1
  deriving DecidableEq, Repr
```

`Toy.CFI.Reg.all` (`lean/ToyCFI/Machine.lean:30-31`):

```lean
-- lean/ToyCFI/Machine.lean:30-31
/-- All registers, in a fixed order. -/
def Reg.all : List Reg := [.sp, .fp, .s1, .t1]
```

`Toy.CFI.RegFile` (`lean/ToyCFI/Machine.lean:36-43`):

```lean
-- lean/ToyCFI/Machine.lean:36-43
/-- A register file: one value per register.  A structure (rather than a function)
so that register files of decidable values have decidable equality. -/
structure RegFile (α : Type) where
  sp : α
  fp : α
  s1 : α
  t1 : α
  deriving DecidableEq, Repr
```

The register-file accessors below are declared inside `namespace RegFile` with `variable {α : Type}`.

`Toy.CFI.RegFile.get` (`lean/ToyCFI/Machine.lean:49-54`):

```lean
-- lean/ToyCFI/Machine.lean:49-54
/-- Read a register. -/
def get (f : RegFile α) : Reg → α
  | .sp => f.sp
  | .fp => f.fp
  | .s1 => f.s1
  | .t1 => f.t1
```

`Toy.CFI.RegFile.set` (`lean/ToyCFI/Machine.lean:56-61`):

```lean
-- lean/ToyCFI/Machine.lean:56-61
/-- Overwrite one register. -/
def set (f : RegFile α) : Reg → α → RegFile α
  | .sp, v => { f with sp := v }
  | .fp, v => { f with fp := v }
  | .s1, v => { f with s1 := v }
  | .t1, v => { f with t1 := v }
```

`Toy.CFI.RegFile.const` (`lean/ToyCFI/Machine.lean:63-64`):

```lean
-- lean/ToyCFI/Machine.lean:63-64
/-- The register file holding `a` in every register. -/
def const (a : α) : RegFile α := ⟨a, a, a, a⟩
```

`Toy.CFI.Op` (`lean/ToyCFI/Machine.lean:84-107`):

```lean
-- lean/ToyCFI/Machine.lean:84-107
/-- Frame-affecting operations of the toy instruction set.

* `push r`: `sp := sp - 1`, then store (the old value of) `r` at `[sp]`.
* `pop r`: load `[sp]`, `sp := sp + 1`, then write the loaded value to `r`.
* `subSp n` / `addSp n`: adjust `sp` by `n`.
* `movReg dst src`: `dst := src` (any registers, including `sp`).
* `saveAt r off`: store `r` at `[sp + off]`.
* `restore r off`: load `r` from `[sp + off]`.
* `call`: a call site.  The callee is assumed frame-neutral and its effects are
  not modeled; the operation leaves the state unchanged (including the
  caller-saved scratch register `t1` and all memory).
* `ret`: return; leaves the state unchanged (a block ending in `ret` normally
  has no successors). -/
inductive Op
  | push (r : Reg)
  | pop (r : Reg)
  | subSp (n : Nat)
  | addSp (n : Nat)
  | movReg (dst src : Reg)
  | saveAt (r : Reg) (off : Int)
  | restore (r : Reg) (off : Int)
  | call
  | ret
  deriving DecidableEq, Repr
```

`Toy.CFI.MState` (`lean/ToyCFI/Machine.lean:109-112`):

```lean
-- lean/ToyCFI/Machine.lean:109-112
/-- Machine state: registers and memory. -/
structure MState where
  regs : RegFile Int
  mem : Int → Int
```

`Toy.CFI.write` (`lean/ToyCFI/Machine.lean:114-116`):

```lean
-- lean/ToyCFI/Machine.lean:114-116
/-- Point update of memory. -/
def write (m : Int → Int) (a v : Int) : Int → Int :=
  fun x => if x = a then v else m x
```

`Toy.CFI.step` (`lean/ToyCFI/Machine.lean:118-132`):

```lean
-- lean/ToyCFI/Machine.lean:118-132
/-- One-step semantics of a frame-affecting operation. -/
def step (st : MState) : Op → MState
  | .push r =>
    let sp' := st.regs.get .sp - 1
    { regs := st.regs.set .sp sp', mem := write st.mem sp' (st.regs.get r) }
  | .pop r =>
    { regs := (st.regs.set .sp (st.regs.get .sp + 1)).set r (st.mem (st.regs.get .sp)),
      mem := st.mem }
  | .subSp n => { st with regs := st.regs.set .sp (st.regs.get .sp - (n : Int)) }
  | .addSp n => { st with regs := st.regs.set .sp (st.regs.get .sp + (n : Int)) }
  | .movReg d s => { st with regs := st.regs.set d (st.regs.get s) }
  | .saveAt r off => { st with mem := write st.mem (st.regs.get .sp + off) (st.regs.get r) }
  | .restore r off => { st with regs := st.regs.set r (st.mem (st.regs.get .sp + off)) }
  | .call => st
  | .ret => st
```

#### CFG and layout

Examples: + `pcOf_cold_block_example` (`coldFn.pcOf 2 0 = some 6`); − `pcOf_missing_block_example` (block absent from the layout has no address).

`Toy.CFI.Block` (`lean/ToyCFI/Machine.lean:134-138`):

```lean
-- lean/ToyCFI/Machine.lean:134-138
/-- A basic block: a list of operations and the indices of its CFG successors. -/
structure Block where
  ops : List Op
  succs : List Nat
  deriving DecidableEq, Repr
```

`Toy.CFI.Func` (`lean/ToyCFI/Machine.lean:140-146`):

```lean
-- lean/ToyCFI/Machine.lean:140-146
/-- A function: blocks indexed by position (block `0` is the entry block) and a
linear layout, i.e. the order in which blocks are placed in memory.  The layout
need not follow control flow. -/
structure Func where
  blocks : List Block
  layout : List Nat
  deriving DecidableEq, Repr
```

`Toy.CFI.Func.blockOps` (`lean/ToyCFI/Machine.lean:150-151`):

```lean
-- lean/ToyCFI/Machine.lean:150-151
/-- Operations of block `b` (empty for an out-of-range index). -/
def blockOps (f : Func) (b : Nat) : List Op := (f.blocks[b]?.map Block.ops).getD []
```

`Toy.CFI.Func.succs` (`lean/ToyCFI/Machine.lean:153-154`):

```lean
-- lean/ToyCFI/Machine.lean:153-154
/-- Successors of block `b` (empty for an out-of-range index). -/
def succs (f : Func) (b : Nat) : List Nat := (f.blocks[b]?.map Block.succs).getD []
```

`Toy.CFI.Func.opAt` (`lean/ToyCFI/Machine.lean:156-157`):

```lean
-- lean/ToyCFI/Machine.lean:156-157
/-- The operation at offset `k` of block `b`. -/
def opAt (f : Func) (b k : Nat) : Option Op := (f.blockOps b)[k]?
```

`Toy.CFI.Func.startIn` (`lean/ToyCFI/Machine.lean:159-163`):

```lean
-- lean/ToyCFI/Machine.lean:159-163
/-- Linear start address of block `b` in a layout suffix, given the address `acc`
of that suffix's first block; the first occurrence of `b` counts. -/
def startIn (f : Func) : List Nat → Nat → Nat → Option Nat
  | [], _, _ => none
  | x :: xs, acc, b => if x = b then some acc else startIn f xs (acc + (f.blockOps x).length) b
```

`Toy.CFI.Func.blockStart` (`lean/ToyCFI/Machine.lean:165-166`):

```lean
-- lean/ToyCFI/Machine.lean:165-166
/-- Linear start address of block `b`. -/
def blockStart (f : Func) (b : Nat) : Option Nat := f.startIn f.layout 0 b
```

`Toy.CFI.Func.pcOf` (`lean/ToyCFI/Machine.lean:168-169`):

```lean
-- lean/ToyCFI/Machine.lean:168-169
/-- Linear address (PC) of offset `k` in block `b`. -/
def pcOf (f : Func) (b k : Nat) : Option Nat := (f.blockStart b).map (· + k)
```

#### Callers and reachability

Examples: + `coldFn_reach_cold`, `coldFn_reach_ret`, `probeLoopState_reach`, `mergeFn_reach_via1`, `mergeFn_reach_via2`; − `not_reach_coldFn_cold_with_sp_eq_cfa`, and the unreachable state in `multiFrame_fails_without_chainUpTo`. Layout independence: `Reach.layout_irrelevant`.

`Toy.CFI.Caller` (`lean/ToyCFI/Machine.lean:173-177`):

```lean
-- lean/ToyCFI/Machine.lean:173-177
/-- The caller-side ground truth an unwinder must recover: the CFA (the caller's
stack pointer at the call) and the caller's register values. -/
structure Caller where
  cfa : Int
  regs : RegFile Int
```

`Toy.CFI.entryState` (`lean/ToyCFI/Machine.lean:179-182`):

```lean
-- lean/ToyCFI/Machine.lean:179-182
/-- State on function entry: `sp` holds the CFA, every other register holds the
caller's value, memory is arbitrary. -/
def entryState (c : Caller) (m : Int → Int) : MState :=
  { regs := c.regs.set .sp c.cfa, mem := m }
```

`Toy.CFI.Reach` (`lean/ToyCFI/Machine.lean:184-196`):

```lean
-- lean/ToyCFI/Machine.lean:184-196
/-- `Reach f c m b k st`: state `st` is reachable at offset `k` of block `b`
(before executing the operation there), starting from `entryState c m` at the
start of block `0` and following CFG paths.  Only valid PCs are reachable:
`k` is always below the block length, and paths do not enter empty blocks. -/
inductive Reach (f : Func) (c : Caller) (m : Int → Int) : Nat → Nat → MState → Prop
  | entry : 0 < (f.blockOps 0).length → Reach f c m 0 0 (entryState c m)
  | next {b k : Nat} {st : MState} {op : Op} :
      Reach f c m b k st → f.opAt b k = some op → k + 1 < (f.blockOps b).length →
      Reach f c m b (k + 1) (step st op)
  | edge {b k b' : Nat} {st : MState} {op : Op} :
      Reach f c m b k st → f.opAt b k = some op → k + 1 = (f.blockOps b).length →
      b' ∈ f.succs b → 0 < (f.blockOps b').length →
      Reach f c m b' 0 (step st op)
```

#### Rows and CFI programs

Examples: + `rowAt_example` (instructions after `advanceLoc 1` apply from address 1), `rowAt_restoreState_restores_cfa` (the CFA rule is restored); − `rowAt_underflow_none`.

`Toy.CFI.RegRule` (`lean/ToyCFI/Table.lean:16-21`):

```lean
-- lean/ToyCFI/Table.lean:16-21
/-- Per-register recovery rule: `same` (the register still holds the caller's
value) or `offset k` (the caller's value is saved at address `CFA + k`). -/
inductive RegRule
  | same
  | offset (k : Int)
  deriving DecidableEq, Repr
```

`Toy.CFI.Row` (`lean/ToyCFI/Table.lean:23-28`):

```lean
-- lean/ToyCFI/Table.lean:23-28
/-- An unwind row: the CFA rule `cfaReg + cfaOff` and a rule per register. -/
structure Row where
  cfaReg : Reg
  cfaOff : Int
  rules : RegFile RegRule
  deriving DecidableEq, Repr
```

`Toy.CFI.initRow` (`lean/ToyCFI/Table.lean:30-32`):

```lean
-- lean/ToyCFI/Table.lean:30-32
/-- The initial row (the toy counterpart of a CIE's initial instructions):
`CFA = sp + 0`, every register `same`. -/
def initRow : Row := { cfaReg := .sp, cfaOff := 0, rules := RegFile.const .same }
```

`Toy.CFI.CFIInst` (`lean/ToyCFI/Table.lean:34-45`):

```lean
-- lean/ToyCFI/Table.lean:34-45
/-- Row-modifying instructions. `advanceLoc d` moves the current location by `d`
address units; `restore r` resets `r` to its rule in `initRow`. -/
inductive CFIInst
  | defCfa (r : Reg) (off : Int)
  | defCfaRegister (r : Reg)
  | defCfaOffset (off : Int)
  | offset (r : Reg) (k : Int)
  | restore (r : Reg)
  | rememberState
  | restoreState
  | advanceLoc (d : Nat)
  deriving DecidableEq, Repr
```

`Toy.CFI.CFIState` (`lean/ToyCFI/Table.lean:47-52`):

```lean
-- lean/ToyCFI/Table.lean:47-52
/-- Interpreter state: current location, current row, and the state stack. -/
structure CFIState where
  loc : Nat
  row : Row
  stack : List Row
  deriving DecidableEq, Repr
```

`Toy.CFI.execInst` (`lean/ToyCFI/Table.lean:54-69`):

```lean
-- lean/ToyCFI/Table.lean:54-69
/-- Effect of one non-advancing instruction.  `rememberState` pushes the whole
row (CFA rule included); `restoreState` pops it and fails (`none`) on an empty
stack. `advanceLoc` is handled by `rowAtAux` and is a no-op here. -/
def execInst (s : CFIState) : CFIInst → Option CFIState
  | .defCfa r off => some { s with row := { s.row with cfaReg := r, cfaOff := off } }
  | .defCfaRegister r => some { s with row := { s.row with cfaReg := r } }
  | .defCfaOffset off => some { s with row := { s.row with cfaOff := off } }
  | .offset r k => some { s with row := { s.row with rules := s.row.rules.set r (.offset k) } }
  | .restore r =>
    some { s with row := { s.row with rules := s.row.rules.set r (initRow.rules.get r) } }
  | .rememberState => some { s with stack := s.row :: s.stack }
  | .restoreState =>
    match s.stack with
    | [] => none
    | R :: rest => some { s with row := R, stack := rest }
  | .advanceLoc _ => some s
```

`Toy.CFI.rowAtAux` (`lean/ToyCFI/Table.lean:71-83`):

```lean
-- lean/ToyCFI/Table.lean:71-83
/-- Row in effect at `pc`: interpret instructions in order; an `advanceLoc d`
that would move the location past `pc` ends the interpretation.  Instructions
located at an address `≤ pc` therefore apply at `pc`. -/
def rowAtAux : List CFIInst → CFIState → Nat → Option Row
  | [], s, _ => some s.row
  | i :: rest, s, pc =>
    match i with
    | .advanceLoc d =>
      if pc < s.loc + d then some s.row else rowAtAux rest { s with loc := s.loc + d } pc
    | _ =>
      match execInst s i with
      | none => none
      | some s' => rowAtAux rest s' pc
```

`Toy.CFI.rowAt?` (`lean/ToyCFI/Table.lean:85-88`):

```lean
-- lean/ToyCFI/Table.lean:85-88
/-- The row of a CFI program at address `pc` (the program starts at address `0`
with `initRow` and an empty stack); `none` on state-stack underflow. -/
def rowAt? (prog : List CFIInst) (pc : Nat) : Option Row :=
  rowAtAux prog { loc := 0, row := initRow, stack := [] } pc
```

#### Recovery and table correctness

Examples: `Recovers`: + `recovers_cold_entry_example`; − `not_recovers_cold_entry_initRow`. `TableCorrect`: + `genCFI_coldFn_tableCorrect`, `probeAnchorCFI_tableCorrect`, `incFn` part of `checkCFI_incomplete`; − `naiveCFI_coldFn_not_tableCorrect`, `probeSpCFI_not_tableCorrect`, `mergeFn_no_tableCorrect`.

`Toy.CFI.cfaOf` (`lean/ToyCFI/Table.lean:90-91`):

```lean
-- lean/ToyCFI/Table.lean:90-91
/-- CFA computed by row `R` from state `st`. -/
def cfaOf (R : Row) (st : MState) : Int := st.regs.get R.cfaReg + R.cfaOff
```

`Toy.CFI.ruleVal` (`lean/ToyCFI/Table.lean:93-97`):

```lean
-- lean/ToyCFI/Table.lean:93-97
/-- Value of register `r` in the caller, as recovered by row `R` from `st`. -/
def ruleVal (R : Row) (st : MState) (r : Reg) : Int :=
  match R.rules.get r with
  | .same => st.regs.get r
  | .offset k => st.mem (cfaOf R st + k)
```

`Toy.CFI.calleeSaved` (`lean/ToyCFI/Table.lean:99-100`):

```lean
-- lean/ToyCFI/Table.lean:99-100
/-- The toy ABI's callee-saved registers. -/
def calleeSaved : List Reg := [.fp, .s1]
```

`Toy.CFI.Recovers` (`lean/ToyCFI/Table.lean:102-105`):

```lean
-- lean/ToyCFI/Table.lean:102-105
/-- Row `R` applied to state `st` recovers caller `c`: the computed CFA is the
caller's CFA and every callee-saved register is recovered. -/
def Recovers (R : Row) (c : Caller) (st : MState) : Prop :=
  cfaOf R st = c.cfa ∧ ∀ r ∈ calleeSaved, ruleVal R st r = c.regs.get r
```

`Toy.CFI.TableCorrect` (`lean/ToyCFI/Table.lean:107-113`):

```lean
-- lean/ToyCFI/Table.lean:107-113
/-- Per-PC table correctness for a CFG with a linear layout: for every caller,
every initial memory, every reachable `(block, offset)` and every state
reachable there, the PC has a linear address, the CFI program has a row at that
address, and the row recovers the caller. -/
def TableCorrect (f : Func) (prog : List CFIInst) : Prop :=
  ∀ (c : Caller) (m : Int → Int) (b k : Nat) (st : MState), Reach f c m b k st →
    ∃ pc R, f.pcOf b k = some pc ∧ rowAt? prog pc = some R ∧ Recovers R c st
```

#### Abstract frame states

Examples: `Inv`: + `absInit_sound`, `xfer_sound`; − `not_inv_absInit_example`, `reach_inv_fails_without_annSound`. `entails`: + `entails_example`; − `not_entails_example`. `leqA`: + `leqA_example`, `leqA_shadowed_examples` (shadowed slot entries are ignored; `leqA_refl`); − `not_leqA_example`.

`Toy.CFI.SymVal` (`lean/ToyCFI/Abstract.lean:14-19`):

```lean
-- lean/ToyCFI/Abstract.lean:14-19
/-- Symbolic values of the abstract frame state. -/
inductive SymVal
  | cfaRel (d : Int)
  | callerOf (r : Reg)
  | unknown
  deriving DecidableEq, Repr
```

`Toy.CFI.AState` (`lean/ToyCFI/Abstract.lean:21-26`):

```lean
-- lean/ToyCFI/Abstract.lean:21-26
/-- Abstract frame state: symbolic registers and a list of CFA-relative slots
`(k, v)` meaning "memory at `CFA + k` holds `v`" (first entry for `k` wins). -/
structure AState where
  regs : RegFile SymVal
  slots : List (Int × SymVal)
  deriving DecidableEq, Repr
```

`Toy.CFI.slotAt` (`lean/ToyCFI/Abstract.lean:28-31`):

```lean
-- lean/ToyCFI/Abstract.lean:28-31
/-- Symbolic content of slot `k` (`unknown` if absent). -/
def slotAt : List (Int × SymVal) → Int → SymVal
  | [], _ => .unknown
  | (k', v) :: rest, k => if k' = k then v else slotAt rest k
```

`Toy.CFI.symAdd` (`lean/ToyCFI/Abstract.lean:33-36`):

```lean
-- lean/ToyCFI/Abstract.lean:33-36
/-- Add a constant to a symbolic value (only CFA-relative values stay known). -/
def symAdd : SymVal → Int → SymVal
  | .cfaRel d, n => .cfaRel (d + n)
  | _, _ => .unknown
```

`Toy.CFI.storeSlot` (`lean/ToyCFI/Abstract.lean:38-43`):

```lean
-- lean/ToyCFI/Abstract.lean:38-43
/-- Store `v` at symbolic address `addr`: a CFA-relative address updates one slot;
any other address forgets all slots (the write may alias any of them). -/
def storeSlot (sl : List (Int × SymVal)) (addr v : SymVal) : List (Int × SymVal) :=
  match addr with
  | .cfaRel d => (d, v) :: sl.filter (fun e => e.1 != d)
  | _ => []
```

`Toy.CFI.loadSlot` (`lean/ToyCFI/Abstract.lean:45-48`):

```lean
-- lean/ToyCFI/Abstract.lean:45-48
/-- Load from symbolic address `addr`. -/
def loadSlot (sl : List (Int × SymVal)) : SymVal → SymVal
  | .cfaRel d => slotAt sl d
  | _ => .unknown
```

`Toy.CFI.xfer` (`lean/ToyCFI/Abstract.lean:50-67`):

```lean
-- lean/ToyCFI/Abstract.lean:50-67
/-- Abstract transfer function, mirroring `step`. -/
def xfer (A : AState) : Op → AState
  | .push r =>
    let sp' := symAdd (A.regs.get .sp) (-1)
    { regs := A.regs.set .sp sp', slots := storeSlot A.slots sp' (A.regs.get r) }
  | .pop r =>
    { regs := (A.regs.set .sp (symAdd (A.regs.get .sp) 1)).set r
        (loadSlot A.slots (A.regs.get .sp)),
      slots := A.slots }
  | .subSp n => { A with regs := A.regs.set .sp (symAdd (A.regs.get .sp) (-(n : Int))) }
  | .addSp n => { A with regs := A.regs.set .sp (symAdd (A.regs.get .sp) (n : Int)) }
  | .movReg d s => { A with regs := A.regs.set d (A.regs.get s) }
  | .saveAt r off =>
    { A with slots := storeSlot A.slots (symAdd (A.regs.get .sp) off) (A.regs.get r) }
  | .restore r off =>
    { A with regs := A.regs.set r (loadSlot A.slots (symAdd (A.regs.get .sp) off)) }
  | .call => A
  | .ret => A
```

`Toy.CFI.absRun` (`lean/ToyCFI/Abstract.lean:69-70`):

```lean
-- lean/ToyCFI/Abstract.lean:69-70
/-- Run the abstract transfer over a list of operations. -/
def absRun (A : AState) (ops : List Op) : AState := ops.foldl xfer A
```

`Toy.CFI.absInit` (`lean/ToyCFI/Abstract.lean:72-74`):

```lean
-- lean/ToyCFI/Abstract.lean:72-74
/-- Abstract state on function entry. -/
def absInit : AState :=
  { regs := ⟨.cfaRel 0, .callerOf .fp, .callerOf .s1, .callerOf .t1⟩, slots := [] }
```

`Toy.CFI.symLe` (`lean/ToyCFI/Abstract.lean:76-77`):

```lean
-- lean/ToyCFI/Abstract.lean:76-77
/-- `symLe a b`: `b` is `unknown` or equal to `a` (so `a` is at least as precise). -/
def symLe (a b : SymVal) : Bool := b == .unknown || a == b
```

`Toy.CFI.leqA` (`lean/ToyCFI/Abstract.lean:79-85`):

```lean
-- lean/ToyCFI/Abstract.lean:79-85
/-- `leqA A B`: every fact recorded in `B` is recorded in `A`.  Slots are
compared through `slotAt` on both sides, so a shadowed (later) entry of
`B.slots` for an already-listed offset is ignored, as it is by `Inv`; in
particular `leqA` is reflexive (`leqA_refl`). -/
def leqA (A B : AState) : Bool :=
  Reg.all.all (fun r => symLe (A.regs.get r) (B.regs.get r)) &&
    B.slots.all (fun e => symLe (slotAt A.slots e.1) (slotAt B.slots e.1))
```

`Toy.CFI.SymHolds` (`lean/ToyCFI/Abstract.lean:87-91`):

```lean
-- lean/ToyCFI/Abstract.lean:87-91
/-- Concretization of a symbolic value relative to caller `c`. -/
def SymHolds (c : Caller) : SymVal → Int → Prop
  | .cfaRel d, x => x = c.cfa + d
  | .callerOf r, x => x = c.regs.get r
  | .unknown, _ => True
```

`Toy.CFI.Inv` (`lean/ToyCFI/Abstract.lean:93-97`):

```lean
-- lean/ToyCFI/Abstract.lean:93-97
/-- `Inv A c st`: concrete state `st` (of a frame called by `c`) satisfies every
fact of the abstract state `A`. -/
def Inv (A : AState) (c : Caller) (st : MState) : Prop :=
  (∀ r, SymHolds c (A.regs.get r) (st.regs.get r)) ∧
    (∀ k, SymHolds c (slotAt A.slots k) (st.mem (c.cfa + k)))
```

`Toy.CFI.ruleOK` (`lean/ToyCFI/Abstract.lean:99-103`):

```lean
-- lean/ToyCFI/Abstract.lean:99-103
/-- Does abstract state `A` justify rule `R.rules.get r` for register `r`? -/
def ruleOK (A : AState) (R : Row) (r : Reg) : Bool :=
  match R.rules.get r with
  | .same => A.regs.get r == .callerOf r
  | .offset k => slotAt A.slots k == .callerOf r
```

`Toy.CFI.entails` (`lean/ToyCFI/Abstract.lean:105-108`):

```lean
-- lean/ToyCFI/Abstract.lean:105-108
/-- `entails A R`: in every concrete state satisfying `A`, row `R` recovers the
CFA and the callee-saved registers. -/
def entails (A : AState) (R : Row) : Bool :=
  A.regs.get R.cfaReg == .cfaRel (-R.cfaOff) && calleeSaved.all (ruleOK A R)
```

#### Checker

Examples: `annSoundB`: + `coldFn_annSound`, `probeAnn_sound`; − `genCFI_incorrect_without_annSound` (`coldBadAnn`). `checkCFI`: + / − `checkCFI_examples`; incompleteness `checkCFI_incomplete`.

`Toy.CFI.Ann` (`lean/ToyCFI/Checker.lean:15-16`):

```lean
-- lean/ToyCFI/Checker.lean:15-16
/-- A block annotation: a candidate abstract entry state per block index. -/
abbrev Ann := Nat → Option AState
```

`Toy.CFI.absAt` (`lean/ToyCFI/Checker.lean:18-19`):

```lean
-- lean/ToyCFI/Checker.lean:18-19
/-- Abstract state at offset `k` of a block entered in state `A`. -/
def absAt (f : Func) (A : AState) (b k : Nat) : AState := absRun A ((f.blockOps b).take k)
```

`Toy.CFI.edgesOK` (`lean/ToyCFI/Checker.lean:21-30`):

```lean
-- lean/ToyCFI/Checker.lean:21-30
/-- Edge check for one block: every successor is annotated and the block's
abstract exit state is at least as precise as the successor's entry state. -/
def edgesOK (f : Func) (ann : Ann) (b : Nat) : Bool :=
  match ann b with
  | none => true
  | some A =>
    (f.succs b).all (fun b' =>
      match ann b' with
      | some B => leqA (absRun A (f.blockOps b)) B
      | none => false)
```

`Toy.CFI.annSoundB` (`lean/ToyCFI/Checker.lean:32-38`):

```lean
-- lean/ToyCFI/Checker.lean:32-38
/-- `annSoundB f ann`: the annotation is sound — block `0` is annotated with a
state implied by `absInit`, and `edgesOK` holds for every block index. -/
def annSoundB (f : Func) (ann : Ann) : Bool :=
  (match ann 0 with
   | some A => leqA absInit A
   | none => false) &&
  (List.range f.blocks.length).all (edgesOK f ann)
```

`Toy.CFI.rowsOK` (`lean/ToyCFI/Checker.lean:40-52`):

```lean
-- lean/ToyCFI/Checker.lean:40-52
/-- Row check for one block: at the linear address of each PC of an annotated
block, the program has a row and the row is entailed by the abstract state. -/
def rowsOK (f : Func) (prog : List CFIInst) (ann : Ann) (b : Nat) : Bool :=
  match ann b with
  | none => true
  | some A =>
    (List.range (f.blockOps b).length).all (fun k =>
      match f.pcOf b k with
      | none => false
      | some pc =>
        match rowAt? prog pc with
        | none => false
        | some R => entails (absAt f A b k) R)
```

`Toy.CFI.checkWith` (`lean/ToyCFI/Checker.lean:54-56`):

```lean
-- lean/ToyCFI/Checker.lean:54-56
/-- Check a CFI program against a given annotation. -/
def checkWith (f : Func) (prog : List CFIInst) (ann : Ann) : Bool :=
  annSoundB f ann && (List.range f.blocks.length).all (rowsOK f prog ann)
```

`Toy.CFI.joinSym` (`lean/ToyCFI/Checker.lean:60-61`):

```lean
-- lean/ToyCFI/Checker.lean:60-61
/-- Join of symbolic values. -/
def joinSym (a b : SymVal) : SymVal := if a = b then a else .unknown
```

`Toy.CFI.joinA` (`lean/ToyCFI/Checker.lean:63-67`):

```lean
-- lean/ToyCFI/Checker.lean:63-67
/-- Join of abstract states (keeps the facts common to both). -/
def joinA (A B : AState) : AState :=
  { regs := ⟨joinSym A.regs.sp B.regs.sp, joinSym A.regs.fp B.regs.fp,
      joinSym A.regs.s1 B.regs.s1, joinSym A.regs.t1 B.regs.t1⟩,
    slots := A.slots.filter (fun e => slotAt B.slots e.1 == e.2) }
```

`Toy.CFI.propagate` (`lean/ToyCFI/Checker.lean:69-79`):

```lean
-- lean/ToyCFI/Checker.lean:69-79
/-- One propagation pass over all blocks in index order. -/
def propagate (f : Func) (ann : List (Option AState)) : List (Option AState) :=
  (List.range f.blocks.length).foldl (fun acc b =>
    match acc[b]?.join with
    | none => acc
    | some A =>
      let out := absRun A (f.blockOps b)
      (f.succs b).foldl (fun acc' b' =>
        acc'.set b' (some (match acc'[b']?.join with
          | none => out
          | some B => joinA B out))) acc) ann
```

`Toy.CFI.inferLoop` (`lean/ToyCFI/Checker.lean:81-86`):

```lean
-- lean/ToyCFI/Checker.lean:81-86
/-- Iterate `propagate` until it is stable or fuel runs out. -/
def inferLoop (f : Func) : Nat → List (Option AState) → Option (List (Option AState))
  | 0, _ => none
  | n + 1, ann =>
    let ann' := propagate f ann
    if ann' = ann then some ann else inferLoop f n ann'
```

`Toy.CFI.inferEntries` (`lean/ToyCFI/Checker.lean:88-92`):

```lean
-- lean/ToyCFI/Checker.lean:88-92
/-- Inferred block entry states (`none` if propagation did not stabilize within
the fuel bound). -/
def inferEntries (f : Func) : Option (List (Option AState)) :=
  inferLoop f (8 * (f.blocks.length + 1) * (f.blocks.length + 1) + 8)
    ((List.replicate f.blocks.length none).set 0 (some absInit))
```

`Toy.CFI.checkCFI` (`lean/ToyCFI/Checker.lean:94-98`):

```lean
-- lean/ToyCFI/Checker.lean:94-98
/-- The decidable checker. -/
def checkCFI (f : Func) (prog : List CFIInst) : Bool :=
  match inferEntries f with
  | none => false
  | some ann => checkWith f prog (fun b => ann[b]?.join)
```

#### Generator

Examples: `genCFI`: + `genCFI_coldFn_eq` (verbatim output with `rememberState`/`restoreState`), `genCFI_probeFn_eq`, `genCFI_shadowedClobberFn_tableCorrect`. `naiveCFI`: + `naiveCFI_coldFnFallthrough_tableCorrect`; − `naiveCFI_coldFn_not_tableCorrect`. `ruleChoice`: `ruleChoice_shadowed_example` (shadowed slot entries are skipped). `stateRecoverableB`: + / − `stateRecoverableB_examples`; characterization `stateRecoverableB_iff_exists_entails`. `annRecoverableB`: + `genCFI_hypotheses_hold_coldFn`; − `mergeFn_inferred_sound_not_recoverable`; characterization `annRecoverableB_iff`. `LayoutCovers`: + `coldFn_layoutCovers`; − `genCFI_incorrect_without_layoutCovers`.

`Toy.CFI.cfaChoice` (`lean/ToyCFI/Generator.lean:23-29`):

```lean
-- lean/ToyCFI/Generator.lean:23-29
/-- Preferred CFA base: the first of `fp, sp, s1, t1` whose symbolic value is
CFA-relative. -/
def cfaChoice (A : AState) : Option (Reg × Int) :=
  [Reg.fp, .sp, .s1, .t1].findSome? (fun r =>
    match A.regs.get r with
    | .cfaRel d => some (r, -d)
    | _ => none)
```

`Toy.CFI.ruleChoice` (`lean/ToyCFI/Generator.lean:31-39`):

```lean
-- lean/ToyCFI/Generator.lean:31-39
/-- Rule chosen for register `r`: `same` if `r` still holds the caller's value,
else the offset of the first slot entry whose offset is not shadowed (its
`slotAt` value) and holds the caller's value, else `same` (unrecoverable). -/
def ruleChoice (A : AState) (r : Reg) : RegRule :=
  if A.regs.get r = .callerOf r then .same
  else
    match A.slots.find? (fun e => slotAt A.slots e.1 == .callerOf r) with
    | some e => .offset e.1
    | none => .same
```

`Toy.CFI.rowOf` (`lean/ToyCFI/Generator.lean:41-45`):

```lean
-- lean/ToyCFI/Generator.lean:41-45
/-- Row derived from an abstract state. -/
def rowOf (A : AState) : Row :=
  let cr := (cfaChoice A).getD (.sp, 0)
  { cfaReg := cr.1, cfaOff := cr.2,
    rules := ⟨ruleChoice A .sp, ruleChoice A .fp, ruleChoice A .s1, ruleChoice A .t1⟩ }
```

`Toy.CFI.cfaDelta` (`lean/ToyCFI/Generator.lean:47-52`):

```lean
-- lean/ToyCFI/Generator.lean:47-52
/-- Instructions changing the CFA rule of `R` into that of `R'`. -/
def cfaDelta (R R' : Row) : List CFIInst :=
  if R.cfaReg = R'.cfaReg then
    (if R.cfaOff = R'.cfaOff then [] else [.defCfaOffset R'.cfaOff])
  else if R.cfaOff = R'.cfaOff then [.defCfaRegister R'.cfaReg]
  else [.defCfa R'.cfaReg R'.cfaOff]
```

`Toy.CFI.ruleDelta` (`lean/ToyCFI/Generator.lean:54-60`):

```lean
-- lean/ToyCFI/Generator.lean:54-60
/-- Instructions changing the register rules of `R` into those of `R'`. -/
def ruleDelta (R R' : Row) : List CFIInst :=
  Reg.all.filterMap (fun r =>
    if R.rules.get r = R'.rules.get r then none
    else some (match R'.rules.get r with
      | .same => .restore r
      | .offset k => .offset r k))
```

`Toy.CFI.delta` (`lean/ToyCFI/Generator.lean:62-63`):

```lean
-- lean/ToyCFI/Generator.lean:62-63
/-- Instructions turning row `R` into row `R'`. -/
def delta (R R' : Row) : List CFIInst := cfaDelta R R' ++ ruleDelta R R'
```

`Toy.CFI.blockRows` (`lean/ToyCFI/Generator.lean:65-67`):

```lean
-- lean/ToyCFI/Generator.lean:65-67
/-- Desired rows of block `b` under annotation `ann` (one per PC). -/
def blockRows (f : Func) (ann : Ann) (b : Nat) : Option (List Row) :=
  (ann b).map (fun A => (List.range (f.blockOps b).length).map (fun k => rowOf (absAt f A b k)))
```

`Toy.CFI.emitRows` (`lean/ToyCFI/Generator.lean:69-73`):

```lean
-- lean/ToyCFI/Generator.lean:69-73
/-- Emit rows for consecutive PCs: before each PC the delta from the previous
row, then `advanceLoc 1`. -/
def emitRows : Row → List Row → List CFIInst
  | _, [] => []
  | cur, R :: Rs => delta cur R ++ [.advanceLoc 1] ++ emitRows R Rs
```

`Toy.CFI.entryRow` (`lean/ToyCFI/Generator.lean:75-77`):

```lean
-- lean/ToyCFI/Generator.lean:75-77
/-- Entry row of block `b`, if annotated and non-empty. -/
def entryRow (f : Func) (ann : Ann) (b : Nat) : Option Row :=
  (blockRows f ann b).bind List.head?
```

`Toy.CFI.genBlocks` (`lean/ToyCFI/Generator.lean:79-92`):

```lean
-- lean/ToyCFI/Generator.lean:79-92
/-- Emit blocks in layout order. `cur` is the row inherited at the current
location; `pend` records that the previous block remembered a row for us. -/
def genBlocks (f : Func) (ann : Ann) : Row → Bool → List Nat → List CFIInst
  | _, _, [] => []
  | cur, pend, b :: rest =>
    match blockRows f ann b with
    | none => [.advanceLoc (f.blockOps b).length] ++ genBlocks f ann cur false rest
    | some [] => genBlocks f ann cur false rest
    | some (E :: Rs) =>
      let X := ((E :: Rs).getLast?).getD E
      let pre := if pend then [CFIInst.restoreState] else delta cur E
      let rem := decide (rest.head?.bind (entryRow f ann) = some E ∧ X ≠ E)
      pre ++ (if rem then [CFIInst.rememberState] else []) ++ emitRows E (E :: Rs) ++
        genBlocks f ann X rem rest
```

`Toy.CFI.genCFI` (`lean/ToyCFI/Generator.lean:94-96`):

```lean
-- lean/ToyCFI/Generator.lean:94-96
/-- The generator (with `rememberState`/`restoreState` or explicit re-definition
at block boundaries). -/
def genCFI (f : Func) (ann : Ann) : List CFIInst := genBlocks f ann initRow false f.layout
```

`Toy.CFI.naiveCFI` (`lean/ToyCFI/Generator.lean:98-105`):

```lean
-- lean/ToyCFI/Generator.lean:98-105
/-- Naive emitter: per-block deltas only, starting each block from its own entry
row without emitting anything at the boundary. -/
def naiveCFI (f : Func) (ann : Ann) : List CFIInst :=
  f.layout.flatMap (fun b =>
    match blockRows f ann b with
    | none => [.advanceLoc (f.blockOps b).length]
    | some [] => []
    | some (E :: Rs) => emitRows E (E :: Rs))
```

`Toy.CFI.stateRecoverableB` (`lean/ToyCFI/Generator.lean:107-115`):

```lean
-- lean/ToyCFI/Generator.lean:107-115
/-- `stateRecoverableB A`: some register holds a CFA-relative value, and every
callee-saved register either still holds the caller's value or is the
(unshadowed) content of some CFA-relative slot.  This mentions no emitter:
`stateRecoverableB_iff_exists_entails` shows it holds exactly when some row is
entailed by `A`. -/
def stateRecoverableB (A : AState) : Bool :=
  (cfaChoice A).isSome &&
    calleeSaved.all (fun r =>
      (A.regs.get r == .callerOf r) || A.slots.any (fun e => slotAt A.slots e.1 == .callerOf r))
```

`Toy.CFI.annRecoverableB` (`lean/ToyCFI/Generator.lean:117-125`):

```lean
-- lean/ToyCFI/Generator.lean:117-125
/-- `annRecoverableB f ann`: at every PC of every annotated block the abstract
state is recoverable (`stateRecoverableB`), i.e. some row is entailed by it
(`annRecoverableB_iff`). -/
def annRecoverableB (f : Func) (ann : Ann) : Bool :=
  (List.range f.blocks.length).all (fun b =>
    match ann b with
    | none => true
    | some A => (List.range (f.blockOps b).length).all (fun k =>
        stateRecoverableB (absAt f A b k)))
```

`Toy.CFI.LayoutCovers` (`lean/ToyCFI/Generator.lean:127-128`):

```lean
-- lean/ToyCFI/Generator.lean:127-128
/-- Every non-empty block appears in the layout. -/
def LayoutCovers (f : Func) : Prop := ∀ b, 0 < (f.blockOps b).length → b ∈ f.layout
```

`Toy.CFI.inferredAnn` (`lean/ToyCFI/Generator.lean:130-131`):

```lean
-- lean/ToyCFI/Generator.lean:130-131
/-- Inferred annotation (empty if inference fails). -/
def inferredAnn (f : Func) : Ann := fun b => ((inferEntries f).getD [])[b]?.join
```

#### Merge points

Examples: + `mergeFn_conflictingCfaOffsetsAt`; − `no_tableCorrect_fails_without_conflictingCfaOffsetsAt` (`mergeFnBalanced`).

`Toy.CFI.ConflictingCfaOffsetsAt` (`lean/ToyCFI/Merge.lean:37-45`):

```lean
-- lean/ToyCFI/Merge.lean:37-45
/-- `ConflictingCfaOffsetsAt f b k`: at PC `(b, k)` no register has a fixed
offset from the CFA across reachable states — for every register `r` there are
two reachable states there (possibly for different callers and memories) in
which `r - CFA` differs.  This is a semantic (concrete-state) condition; it
does not mention the abstract domain. -/
def ConflictingCfaOffsetsAt (f : Func) (b k : Nat) : Prop :=
  ∀ r : Reg, ∃ c₁ m₁ st₁ c₂ m₂ st₂,
    Reach f c₁ m₁ b k st₁ ∧ Reach f c₂ m₂ b k st₂ ∧
      st₁.regs.get r - c₁.cfa ≠ st₂.regs.get r - c₂.cfa
```

#### Example functions

Examples: Used by the results below.

`Toy.CFI.coldBlocks` (`lean/ToyCFI/Funcs.lean:9-18`):

```lean
-- lean/ToyCFI/Funcs.lean:9-18
/-- Frame-pointer prologue with a call, an epilogue, and a cold block that is
entered with the frame established and jumps back to the epilogue.

* block 0 (prologue): `push fp; movReg fp sp; call`, successors `[1, 2]`;
* block 1 (epilogue): `movReg sp fp; pop fp; ret`;
* block 2 (cold): `call`, successor `[1]`. -/
def coldBlocks : List Block :=
  [⟨[.push .fp, .movReg .fp .sp, .call], [1, 2]⟩,
   ⟨[.movReg .sp .fp, .pop .fp, .ret], []⟩,
   ⟨[.call], [1]⟩]
```

`Toy.CFI.coldFn` (`lean/ToyCFI/Funcs.lean:20-22`):

```lean
-- lean/ToyCFI/Funcs.lean:20-22
/-- Layout `0, 1, 2`: the epilogue physically precedes the cold block.
Addresses: block 0 at 0–2, block 1 at 3–5 (`ret` at 5), block 2 at 6. -/
def coldFn : Func := { blocks := coldBlocks, layout := [0, 1, 2] }
```

`Toy.CFI.coldFnFallthrough` (`lean/ToyCFI/Funcs.lean:24-26`):

```lean
-- lean/ToyCFI/Funcs.lean:24-26
/-- Layout `0, 2, 1`: the cold block follows the prologue (the CFG order).
Addresses: block 0 at 0–2, block 2 at 3, block 1 at 4–6. -/
def coldFnFallthrough : Func := { blocks := coldBlocks, layout := [0, 2, 1] }
```

`Toy.CFI.probeFn` (`lean/ToyCFI/Funcs.lean:28-38`):

```lean
-- lean/ToyCFI/Funcs.lean:28-38
/-- Stack-probing loop with a frame-pointer anchor:

* block 0: `push fp; movReg fp sp`, successor `[1]`;
* block 1 (loop): `subSp page`, successors `[1, 2]`;
* block 2: `movReg sp fp; pop fp; ret`.

Addresses: block 0 at 0–1, block 1 at 2, block 2 at 3–5. -/
def probeFn (page : Nat) : Func :=
  { blocks := [⟨[.push .fp, .movReg .fp .sp], [1]⟩, ⟨[.subSp page], [1, 2]⟩,
      ⟨[.movReg .sp .fp, .pop .fp, .ret], []⟩],
    layout := [0, 1, 2] }
```

`Toy.CFI.mergeFn` (`lean/ToyCFI/Funcs.lean:40-46`):

```lean
-- lean/ToyCFI/Funcs.lean:40-46
/-- Two paths with different frame states merge: block 1 pushes `fp`, block 2
does not, both continue to block 3.

Addresses: block 0 at 0, block 1 at 1, block 2 at 2, block 3 at 3. -/
def mergeFn : Func :=
  { blocks := [⟨[.call], [1, 2]⟩, ⟨[.push .fp], [3]⟩, ⟨[.call], [3]⟩, ⟨[.ret], []⟩],
    layout := [0, 1, 2, 3] }
```

`Toy.CFI.mergeFnBalanced` (`lean/ToyCFI/Funcs.lean:48-51`):

```lean
-- lean/ToyCFI/Funcs.lean:48-51
/-- Balanced variant of `mergeFn`: block 2 also pushes `fp`. -/
def mergeFnBalanced : Func :=
  { blocks := [⟨[.call], [1, 2]⟩, ⟨[.push .fp], [3]⟩, ⟨[.push .fp], [3]⟩, ⟨[.ret], []⟩],
    layout := [0, 1, 2, 3] }
```

`Toy.CFI.incFn` (`lean/ToyCFI/Incomplete.lean:19-24`):

```lean
-- lean/ToyCFI/Incomplete.lean:19-24
/-- `t1` anchors the CFA, a loop moves `sp`, then `fp` is stored to and reloaded
from `[sp]`.  Addresses: block 0 at 0, block 1 at 1, block 2 at 2–4. -/
def incFn : Func :=
  { blocks := [⟨[.movReg .t1 .sp], [1]⟩, ⟨[.subSp 1], [1, 2]⟩,
      ⟨[.saveAt .fp 0, .restore .fp 0, .ret], []⟩],
    layout := [0, 1, 2] }
```

`Toy.CFI.incCFI` (`lean/ToyCFI/Incomplete.lean:26-28`):

```lean
-- lean/ToyCFI/Incomplete.lean:26-28
/-- `CFA = t1 + 0` from address 1 on; every register `same`. -/
def incCFI : List CFIInst :=
  [.advanceLoc 1, .defCfaRegister .t1, .advanceLoc 1, .advanceLoc 1, .advanceLoc 1, .advanceLoc 1]
```

`Toy.CFI.probeAnn` (`lean/ToyCFI/ProbeLoop.lean:14-23`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:14-23
/-- Hand-written annotation for `probeFn` (independent of `page`): in the loop
and after it, `sp` is unknown and `fp` is the anchor `CFA - 1`, with the
caller's `fp` saved at `CFA - 1`. -/
def probeAnn : Ann
  | 0 => some absInit
  | 1 => some { regs := ⟨.unknown, .cfaRel (-1), .callerOf .s1, .callerOf .t1⟩,
                slots := [(-1, .callerOf .fp)] }
  | 2 => some { regs := ⟨.unknown, .cfaRel (-1), .callerOf .s1, .callerOf .t1⟩,
                slots := [(-1, .callerOf .fp)] }
  | _ => none
```

`Toy.CFI.probeAnchorCFI` (`lean/ToyCFI/ProbeLoop.lean:27-30`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:27-30
/-- Anchor-relative table: after `movReg fp sp` the CFA is `fp + 1`. -/
def probeAnchorCFI : List CFIInst :=
  [.advanceLoc 1, .defCfaOffset 1, .advanceLoc 1, .defCfaRegister .fp, .offset .fp (-1),
   .advanceLoc 1, .advanceLoc 1, .advanceLoc 1, .defCfa .sp 0, .restore .fp, .advanceLoc 1]
```

`Toy.CFI.probeSpCFI` (`lean/ToyCFI/ProbeLoop.lean:32-35`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:32-35
/-- SP-relative table: the CFA stays `sp + 1` (fixed offset) through the loop. -/
def probeSpCFI : List CFIInst :=
  [.advanceLoc 1, .defCfaOffset 1, .advanceLoc 1, .offset .fp (-1),
   .advanceLoc 1, .advanceLoc 1, .advanceLoc 1, .defCfaOffset 0, .restore .fp, .advanceLoc 1]
```

`Toy.CFI.coldExplicitCFI` (`lean/ToyCFI/ColdBlock.lean:155-161`):

```lean
-- lean/ToyCFI/ColdBlock.lean:155-161
/-- An explicit re-definition at address 6 (instead of `restoreState`) also works:
the naive program with `defCfa fp 1; offset fp (-1)` inserted before the last
`advanceLoc`. -/
def coldExplicitCFI : List CFIInst :=
  [.advanceLoc 1, .defCfaOffset 1, .advanceLoc 1, .defCfaRegister .fp, .offset .fp (-1),
   .advanceLoc 1, .advanceLoc 1, .advanceLoc 1, .defCfa .sp 0, .restore .fp,
   .advanceLoc 1, .defCfa .fp 1, .offset .fp (-1), .advanceLoc 1]
```

#### Call-site tables

Examples: `contains`: + / − `contains_examples` (`[0,4)` contains 3, not 4). `UniqueAt`: + / − `uniqueAt_examples`. `NonOverlapping`: + / − `nonOverlapping_examples`. `SortedByStart`: + / − `sortedByStart_examples`.

`Toy.CFI.CallSite` (`lean/ToyCFI/LSDA.lean:12-18`):

```lean
-- lean/ToyCFI/LSDA.lean:12-18
/-- One call-site entry: the half-open address range `[start, stop)` and an
optional landing pad. -/
structure CallSite where
  start : Nat
  stop : Nat
  lp : Option Nat
  deriving DecidableEq, Repr
```

`Toy.CFI.LSDA` (`lean/ToyCFI/LSDA.lean:20-21`):

```lean
-- lean/ToyCFI/LSDA.lean:20-21
/-- A call-site table. -/
abbrev LSDA := List CallSite
```

`Toy.CFI.CallSite.contains` (`lean/ToyCFI/LSDA.lean:23-24`):

```lean
-- lean/ToyCFI/LSDA.lean:23-24
/-- `e.contains pc`: `pc ∈ [e.start, e.stop)` (exclusive end). -/
def CallSite.contains (e : CallSite) (pc : Nat) : Prop := e.start ≤ pc ∧ pc < e.stop
```

`Toy.CFI.LookupResult` (`lean/ToyCFI/LSDA.lean:29-34`):

```lean
-- lean/ToyCFI/LSDA.lean:29-34
/-- Lookup outcomes. -/
inductive LookupResult
  | landingPad (lp : Nat)
  | noLandingPad
  | notFound
  deriving DecidableEq, Repr
```

`Toy.CFI.CallSite.result` (`lean/ToyCFI/LSDA.lean:36-40`):

```lean
-- lean/ToyCFI/LSDA.lean:36-40
/-- Outcome of a matching entry. -/
def CallSite.result (e : CallSite) : LookupResult :=
  match e.lp with
  | some lp => .landingPad lp
  | none => .noLandingPad
```

`Toy.CFI.lookupFirst` (`lean/ToyCFI/LSDA.lean:42-45`):

```lean
-- lean/ToyCFI/LSDA.lean:42-45
/-- First-match linear scan. -/
def lookupFirst : LSDA → Nat → LookupResult
  | [], _ => .notFound
  | e :: es, pc => if e.contains pc then e.result else lookupFirst es pc
```

`Toy.CFI.lookupScan` (`lean/ToyCFI/LSDA.lean:47-54`):

```lean
-- lean/ToyCFI/LSDA.lean:47-54
/-- Early-exit scan over a table sorted by start address: stop with `notFound`
at the first entry starting after `pc`. -/
def lookupScan : LSDA → Nat → LookupResult
  | [], _ => .notFound
  | e :: es, pc =>
    if pc < e.start then .notFound
    else if pc < e.stop then e.result
    else lookupScan es pc
```

`Toy.CFI.lookupIncl` (`lean/ToyCFI/LSDA.lean:56-59`):

```lean
-- lean/ToyCFI/LSDA.lean:56-59
/-- Off-by-one variant treating the end address as inclusive. -/
def lookupIncl : LSDA → Nat → LookupResult
  | [], _ => .notFound
  | e :: es, pc => if e.start ≤ pc ∧ pc ≤ e.stop then e.result else lookupIncl es pc
```

`Toy.CFI.SortedByStart` (`lean/ToyCFI/LSDA.lean:61-62`):

```lean
-- lean/ToyCFI/LSDA.lean:61-62
/-- Entries are sorted by start address. -/
def SortedByStart (t : LSDA) : Prop := t.Pairwise (fun a b => a.start ≤ b.start)
```

`Toy.CFI.NonOverlapping` (`lean/ToyCFI/LSDA.lean:64-66`):

```lean
-- lean/ToyCFI/LSDA.lean:64-66
/-- Ranges of distinct table positions are disjoint. -/
def NonOverlapping (t : LSDA) : Prop :=
  t.Pairwise (fun a b => ∀ pc, ¬ (a.contains pc ∧ b.contains pc))
```

`Toy.CFI.UniqueAt` (`lean/ToyCFI/LSDA.lean:68-73`):

```lean
-- lean/ToyCFI/LSDA.lean:68-73
/-- At most one distinct entry *value* contains `pc`: any two entries containing
`pc` are equal as values.  Duplicate identical entries are therefore permitted
(`duplicate_entries_uniqueAt_not_nonOverlapping`), unlike `NonOverlapping`,
which compares distinct table positions. -/
def UniqueAt (t : LSDA) (pc : Nat) : Prop :=
  ∀ e₁ ∈ t, ∀ e₂ ∈ t, e₁.contains pc → e₂.contains pc → e₁ = e₂
```

#### Frames and unwinding

Examples: `frameAction`: all three outcomes in `frameAction_examples`. `CfaBaseSafe`: + / − `cfaBaseSafe_examples`. `Agree`: + / − `agree_examples`. `SlotsPreserved`: + / − `slotsPreserved_examples`. `ChainUpTo`: + `multiFrame_hypotheses_hold`; − `multiFrame_fails_without_chainUpTo`. `CaughtWithCallerState`: + / − `caughtWithCallerState_examples` (fails when the handler frame has no row at its call site, although unwinding reports `caught`). `LsdaWellFormedUpTo`, `DeclarativeSkippedBelow`, `DeclarativeCatch`: + `multiFrame_declarative_hypotheses_hold`; − `multiFrameDecl_fails_without_lsdaWellFormed`, `multiFrameDecl_fails_without_declarativeSkippedBelow`, `multiFrameDecl_fails_without_declarativeCatch`.

`Toy.CFI.Frame` (`lean/ToyCFI/MultiFrame.lean:17-24`):

```lean
-- lean/ToyCFI/MultiFrame.lean:17-24
/-- A suspended frame. `callPC` is the linear address of the `call` operation
at which it is suspended; `frameSize` locates its frame base below the CFA. -/
structure Frame where
  fn : Func
  prog : List CFIInst
  lsda : Option LSDA
  callPC : Nat
  frameSize : Nat
```

`Toy.CFI.FrameAction` (`lean/ToyCFI/MultiFrame.lean:26-31`):

```lean
-- lean/ToyCFI/MultiFrame.lean:26-31
/-- Per-frame decision of the toy personality routine. -/
inductive FrameAction
  | handle (lp : Nat)
  | skip
  | terminate
  deriving DecidableEq, Repr
```

`Toy.CFI.frameAction` (`lean/ToyCFI/MultiFrame.lean:33-43`):

```lean
-- lean/ToyCFI/MultiFrame.lean:33-43
/-- No call-site table: skip the frame.  With a table (early-exit scan): a
landing pad handles, an entry without landing pad skips, and a call PC that no
entry covers terminates. -/
def frameAction (fr : Frame) : FrameAction :=
  match fr.lsda with
  | none => .skip
  | some t =>
    match lookupScan t fr.callPC with
    | .landingPad lp => .handle lp
    | .noLandingPad => .skip
    | .notFound => .terminate
```

`Toy.CFI.unwindRegs` (`lean/ToyCFI/MultiFrame.lean:45-48`):

```lean
-- lean/ToyCFI/MultiFrame.lean:45-48
/-- Caller state reconstructed by applying row `R` to `st`: `sp` becomes the
CFA, other registers follow their rules, memory is unchanged. -/
def unwindRegs (R : Row) (st : MState) : MState :=
  { regs := ⟨cfaOf R st, ruleVal R st .fp, ruleVal R st .s1, ruleVal R st .t1⟩, mem := st.mem }
```

`Toy.CFI.Outcome` (`lean/ToyCFI/MultiFrame.lean:50-55`):

```lean
-- lean/ToyCFI/MultiFrame.lean:50-55
/-- Outcome of unwinding. -/
inductive Outcome
  | caught (depth lp : Nat) (st : MState)
  | terminated (depth : Nat)
  | escaped
  | malformed (depth : Nat)
```

`Toy.CFI.unwindFrom` (`lean/ToyCFI/MultiFrame.lean:57-67`):

```lean
-- lean/ToyCFI/MultiFrame.lean:57-67
/-- Iterated unwinding from frame depth `d` in state `st`. -/
def unwindFrom : List Frame → Nat → MState → Outcome
  | [], _, _ => .escaped
  | fr :: rest, d, st =>
    match frameAction fr with
    | .handle lp => .caught d lp st
    | .terminate => .terminated d
    | .skip =>
      match rowAt? fr.prog fr.callPC with
      | none => .malformed d
      | some R => unwindFrom rest (d + 1) (unwindRegs R st)
```

`Toy.CFI.unwind` (`lean/ToyCFI/MultiFrame.lean:69-70`):

```lean
-- lean/ToyCFI/MultiFrame.lean:69-70
/-- Unwind from the innermost frame. -/
def unwind (frames : List Frame) (st : MState) : Outcome := unwindFrom frames 0 st
```

`Toy.CFI.frameBase` (`lean/ToyCFI/MultiFrame.lean:72-73`):

```lean
-- lean/ToyCFI/MultiFrame.lean:72-73
/-- Frame base computed from a row: `CFA - frameSize`. -/
def frameBase (R : Row) (st : MState) (frameSize : Nat) : Int := cfaOf R st - frameSize
```

`Toy.CFI.callerCtx` (`lean/ToyCFI/MultiFrame.lean:75-80`):

```lean
-- lean/ToyCFI/MultiFrame.lean:75-80
/-- Ground-truth caller of frame `j`: the true state of frame `j + 1` (its `sp`
is the CFA of frame `j`), or `top` for the outermost frame. -/
def callerCtx (truth : List MState) (top : Caller) (j : Nat) : Caller :=
  match truth[j + 1]? with
  | some s => ⟨s.regs.get .sp, s.regs⟩
  | none => top
```

`Toy.CFI.AtCallSite` (`lean/ToyCFI/MultiFrame.lean:82-85`):

```lean
-- lean/ToyCFI/MultiFrame.lean:82-85
/-- `st` is a reachable state of `fr.fn`, called by `c`, at the `call` operation
whose address is `fr.callPC`. -/
def AtCallSite (fr : Frame) (c : Caller) (st : MState) : Prop :=
  ∃ m b k, fr.fn.pcOf b k = some fr.callPC ∧ fr.fn.opAt b k = some .call ∧ Reach fr.fn c m b k st
```

`Toy.CFI.ChainReachable` (`lean/ToyCFI/MultiFrame.lean:87-91`):

```lean
-- lean/ToyCFI/MultiFrame.lean:87-91
/-- The true frame states form a call chain: frame `j`'s true state is reachable
in its function when called from frame `j + 1`'s true state. -/
def ChainReachable (frames : List Frame) (truth : List MState) (top : Caller) : Prop :=
  frames.length = truth.length ∧
    ∀ j fr st, frames[j]? = some fr → truth[j]? = some st → AtCallSite fr (callerCtx truth top j) st
```

`Toy.CFI.Agree` (`lean/ToyCFI/MultiFrame.lean:93-95`):

```lean
-- lean/ToyCFI/MultiFrame.lean:93-95
/-- Agreement on `sp` and the callee-saved registers. -/
def Agree (st σ : MState) : Prop :=
  st.regs.get .sp = σ.regs.get .sp ∧ ∀ r ∈ calleeSaved, st.regs.get r = σ.regs.get r
```

`Toy.CFI.CfaBaseSafe` (`lean/ToyCFI/MultiFrame.lean:97-98`):

```lean
-- lean/ToyCFI/MultiFrame.lean:97-98
/-- The CFA base register is `sp` or callee-saved (so a callee preserves it). -/
def CfaBaseSafe (R : Row) : Prop := R.cfaReg = .sp ∨ R.cfaReg ∈ calleeSaved
```

`Toy.CFI.SlotsPreserved` (`lean/ToyCFI/MultiFrame.lean:100-103`):

```lean
-- lean/ToyCFI/MultiFrame.lean:100-103
/-- Memory `M` agrees with the true memory of `σ` at every save slot read by
`R`'s callee-saved rules. -/
def SlotsPreserved (R : Row) (M : Int → Int) (σ : MState) : Prop :=
  ∀ r ∈ calleeSaved, ∀ k, R.rules.get r = .offset k → M (cfaOf R σ + k) = σ.mem (cfaOf R σ + k)
```

`Toy.CFI.ChainUpTo` (`lean/ToyCFI/MultiFrame.lean:105-110`):

```lean
-- lean/ToyCFI/MultiFrame.lean:105-110
/-- Frames `0, …, j` form a call chain: frame `i`'s true state is reachable at
its `call` when its function is called from frame `i + 1`'s true state (or from
`top` if there is none). -/
def ChainUpTo (frames : List Frame) (truth : List MState) (top : Caller) (j : Nat) : Prop :=
  ∀ i fr st, i ≤ j → frames[i]? = some fr → truth[i]? = some st →
    AtCallSite fr (callerCtx truth top i) st
```

`Toy.CFI.TablesUpTo` (`lean/ToyCFI/MultiFrame.lean:112-114`):

```lean
-- lean/ToyCFI/MultiFrame.lean:112-114
/-- The tables of frames `0, …, j` are correct. -/
def TablesUpTo (frames : List Frame) (j : Nat) : Prop :=
  ∀ i fr, i ≤ j → frames[i]? = some fr → TableCorrect fr.fn fr.prog
```

`Toy.CFI.SkippedBelow` (`lean/ToyCFI/MultiFrame.lean:116-118`):

```lean
-- lean/ToyCFI/MultiFrame.lean:116-118
/-- Frames `0, …, j-1` are skipped by the toy personality routine. -/
def SkippedBelow (frames : List Frame) (j : Nat) : Prop :=
  ∀ i fr, i < j → frames[i]? = some fr → frameAction fr = .skip
```

`Toy.CFI.BaseSafeUpTo` (`lean/ToyCFI/MultiFrame.lean:120-123`):

```lean
-- lean/ToyCFI/MultiFrame.lean:120-123
/-- The call-site rows of frames `1, …, j` have a safe CFA base register. -/
def BaseSafeUpTo (frames : List Frame) (j : Nat) : Prop :=
  ∀ i fr R, 0 < i → i ≤ j → frames[i]? = some fr → rowAt? fr.prog fr.callPC = some R →
    CfaBaseSafe R
```

`Toy.CFI.SlotsPreservedBelow` (`lean/ToyCFI/MultiFrame.lean:125-130`):

```lean
-- lean/ToyCFI/MultiFrame.lean:125-130
/-- Memory `M` still holds the save slots read by the call-site rows of frames
`1, …, j-1`. -/
def SlotsPreservedBelow (frames : List Frame) (truth : List MState) (M : Int → Int) (j : Nat) :
    Prop :=
  ∀ i fr σ R, 0 < i → i < j → frames[i]? = some fr → truth[i]? = some σ →
    rowAt? fr.prog fr.callPC = some R → SlotsPreserved R M σ
```

`Toy.CFI.CaughtWithCallerState` (`lean/ToyCFI/MultiFrame.lean:132-143`):

```lean
-- lean/ToyCFI/MultiFrame.lean:132-143
/-- The conclusion of the composition theorem: unwinding from `st0` stops at
frame `j` with landing pad `lp` in a state `st` that agrees with frame `j`'s
true state `stj` on `sp` and the callee-saved registers and whose memory is the
throw-time memory `st0.mem`; frame `j`'s CFI program has a row `R` at its call
site, and in `st` that row computes frame `j`'s true CFA and hence the frame
base `CFA - frameSize`. -/
def CaughtWithCallerState (frames : List Frame) (truth : List MState) (top : Caller)
    (st0 : MState) (j lp : Nat) (frj : Frame) (stj : MState) : Prop :=
  ∃ st R, unwind frames st0 = .caught j lp st ∧ Agree st stj ∧ st.mem = st0.mem ∧
    rowAt? frj.prog frj.callPC = some R ∧
    cfaOf R st = (callerCtx truth top j).cfa ∧
    frameBase R st frj.frameSize = (callerCtx truth top j).cfa - frj.frameSize
```

`Toy.CFI.LsdaWellFormedUpTo` (`lean/ToyCFI/MultiFrame.lean:145-150`):

```lean
-- lean/ToyCFI/MultiFrame.lean:145-150
/-- Frames `0, …, j` have well-formed call-site tables at their call PCs:
sorted by start address and with at most one distinct entry value containing
the call PC. -/
def LsdaWellFormedUpTo (frames : List Frame) (j : Nat) : Prop :=
  ∀ i fr t, i ≤ j → frames[i]? = some fr → fr.lsda = some t →
    SortedByStart t ∧ UniqueAt t fr.callPC
```

`Toy.CFI.DeclarativeSkip` (`lean/ToyCFI/MultiFrame.lean:152-155`):

```lean
-- lean/ToyCFI/MultiFrame.lean:152-155
/-- Declarative skip condition: the frame has no call-site table, or some entry
of its table contains the call PC and has no landing pad. -/
def DeclarativeSkip (fr : Frame) : Prop :=
  fr.lsda = none ∨ ∃ t e, fr.lsda = some t ∧ e ∈ t ∧ e.contains fr.callPC ∧ e.lp = none
```

`Toy.CFI.DeclarativeSkippedBelow` (`lean/ToyCFI/MultiFrame.lean:157-159`):

```lean
-- lean/ToyCFI/MultiFrame.lean:157-159
/-- Frames `0, …, j-1` satisfy the declarative skip condition. -/
def DeclarativeSkippedBelow (frames : List Frame) (j : Nat) : Prop :=
  ∀ i fr, i < j → frames[i]? = some fr → DeclarativeSkip fr
```

`Toy.CFI.DeclarativeCatch` (`lean/ToyCFI/MultiFrame.lean:161-164`):

```lean
-- lean/ToyCFI/MultiFrame.lean:161-164
/-- Declarative catch condition: some entry of the frame's call-site table
contains the call PC and has landing pad `lp`. -/
def DeclarativeCatch (fr : Frame) (lp : Nat) : Prop :=
  ∃ t e, fr.lsda = some t ∧ e ∈ t ∧ e.contains fr.callPC ∧ e.lp = some lp
```

#### Concrete objects used by witnesses and counterexamples

<details><summary>Concrete functions, programs, tables, frames and states (verbatim)</summary>

Examples: none (concrete data).

`Toy.CFI.coldSt02` (`lean/ToyCFI/ColdBlock.lean:15-17`):

```lean
-- lean/ToyCFI/ColdBlock.lean:15-17
/-- State after the prologue's first two operations. -/
def coldSt02 (c : Caller) (m : Int → Int) : MState :=
  step (step (entryState c m) (.push .fp)) (.movReg .fp .sp)
```

`Toy.CFI.coldStRet` (`lean/ToyCFI/ColdBlock.lean:19-21`):

```lean
-- lean/ToyCFI/ColdBlock.lean:19-21
/-- State at the epilogue's `ret` (block 1, offset 2, address 5). -/
def coldStRet (c : Caller) (m : Int → Int) : MState :=
  step (step (step (coldSt02 c m) .call) (.movReg .sp .fp)) (.pop .fp)
```

`Toy.CFI.coldStCold` (`lean/ToyCFI/ColdBlock.lean:23-24`):

```lean
-- lean/ToyCFI/ColdBlock.lean:23-24
/-- State at the cold block's first PC (block 2, offset 0, address 6). -/
def coldStCold (c : Caller) (m : Int → Int) : MState := step (coldSt02 c m) .call
```

`Toy.CFI.coldBadAnn` (`lean/ToyCFI/Generic.lean:314-320`):

```lean
-- lean/ToyCFI/Generic.lean:314-320
/-- An unsound annotation of `coldFn`: it claims the cold block is entered with
no frame (the entry state). -/
def coldBadAnn : Ann
  | 0 => some absInit
  | 1 => inferredAnn coldFn 1
  | 2 => some absInit
  | _ => none
```

`Toy.CFI.coldFnMissing` (`lean/ToyCFI/Generic.lean:344-345`):

```lean
-- lean/ToyCFI/Generic.lean:344-345
/-- `coldFn`'s blocks with the cold block missing from the layout. -/
def coldFnMissing : Func := { blocks := coldBlocks, layout := [0, 1] }
```

`Toy.CFI.coldEntryA` (`lean/ToyCFI/Examples.lean:96-98`):

```lean
-- lean/ToyCFI/Examples.lean:96-98
/-- The abstract state at the cold block's entry. -/
def coldEntryA : AState :=
  { regs := ⟨.cfaRel (-1), .cfaRel (-1), .callerOf .s1, .callerOf .t1⟩, slots := [(-1, .callerOf .fp)] }
```

`Toy.CFI.mergeStVia1` (`lean/ToyCFI/Merge.lean:13-15`):

```lean
-- lean/ToyCFI/Merge.lean:13-15
/-- State at block 3 reached through block 1 (`sp = CFA - 1`). -/
def mergeStVia1 (c : Caller) (m : Int → Int) : MState :=
  step (step (entryState c m) .call) (.push .fp)
```

`Toy.CFI.mergeStVia2` (`lean/ToyCFI/Merge.lean:17-19`):

```lean
-- lean/ToyCFI/Merge.lean:17-19
/-- State at block 3 reached through block 2 (`sp = CFA`). -/
def mergeStVia2 (c : Caller) (m : Int → Int) : MState :=
  step (step (entryState c m) .call) .call
```

`Toy.CFI.probeLoopState` (`lean/ToyCFI/ProbeLoop.lean:40-43`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:40-43
/-- State on entry to the loop block after `n` iterations. -/
def probeLoopState (page : Nat) (c : Caller) (m : Int → Int) : Nat → MState
  | 0 => step (step (entryState c m) (.push .fp)) (.movReg .fp .sp)
  | n + 1 => step (probeLoopState page c m n) (.subSp page)
```

`Toy.CFI.probeAnnZero` (`lean/ToyCFI/ProbeLoop.lean:135-142`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:135-142
/-- Annotation for `probeFn 0` (the loop does not move `sp`). -/
def probeAnnZero : Ann
  | 0 => some absInit
  | 1 => some { regs := ⟨.cfaRel (-1), .cfaRel (-1), .callerOf .s1, .callerOf .t1⟩,
                slots := [(-1, .callerOf .fp)] }
  | 2 => some { regs := ⟨.cfaRel (-1), .cfaRel (-1), .callerOf .s1, .callerOf .t1⟩,
                slots := [(-1, .callerOf .fp)] }
  | _ => none
```

`Toy.CFI.shadowedInit` (`lean/ToyCFI/Examples.lean:116-120`):

```lean
-- lean/ToyCFI/Examples.lean:116-120
/-- An abstract state equivalent to `absInit` whose slot list has a shadowed
entry: the first entry for offset `-1` is `unknown`, a later one claims the
caller's `fp`.  `Inv` (through `slotAt`) ignores the later entry. -/
def shadowedInit : AState :=
  { regs := absInit.regs, slots := [(-1, .unknown), (-1, .callerOf .fp)] }
```

`Toy.CFI.shadowedB` (`lean/ToyCFI/Examples.lean:138-143`):

```lean
-- lean/ToyCFI/Examples.lean:138-143
/-- A state whose slot list shadows a stale claim: slot `-1` reads `unknown`
(first entry) although a later entry claims the caller's `fp`; the caller's
`fp` is really at `-2`. -/
def shadowedB : AState :=
  { regs := ⟨.cfaRel (-2), .cfaRel (-2), .callerOf .s1, .callerOf .t1⟩,
    slots := [(-1, .unknown), (-1, .callerOf .fp), (-2, .callerOf .fp)] }
```

`Toy.CFI.shadowedAnn` (`lean/ToyCFI/Examples.lean:155-159`):

```lean
-- lean/ToyCFI/Examples.lean:155-159
/-- An annotation using the shadowed state `shadowedB` at block 1. -/
def shadowedAnn : Ann
  | 0 => some absInit
  | 1 => some shadowedB
  | _ => none
```

`Toy.CFI.shadowedClobberFn` (`lean/ToyCFI/Examples.lean:149-153`):

```lean
-- lean/ToyCFI/Examples.lean:149-153
/-- Two pushes of `fp`, a store of `t1` over the first save slot, then a frame
pointer: the caller's `fp` survives only at `CFA - 2`. -/
def shadowedClobberFn : Func :=
  { blocks := [⟨[.push .fp, .push .fp, .saveAt .t1 1, .movReg .fp .sp], [1]⟩, ⟨[.ret], []⟩],
    layout := [0, 1] }
```

`Toy.CFI.lsdaOverlap` (`lean/ToyCFI/LSDA.lean:168-169`):

```lean
-- lean/ToyCFI/LSDA.lean:168-169
/-- Overlapping table: `[0,10) ↦ 1` and `[5,15) ↦ 2`. -/
def lsdaOverlap : LSDA := [⟨0, 10, some 1⟩, ⟨5, 15, some 2⟩]
```

`Toy.CFI.lsdaUnsorted` (`lean/ToyCFI/LSDA.lean:195-196`):

```lean
-- lean/ToyCFI/LSDA.lean:195-196
/-- Unsorted table: `[10,20) ↦ 1` before `[0,5) ↦ 2`. -/
def lsdaUnsorted : LSDA := [⟨10, 20, some 1⟩, ⟨0, 5, some 2⟩]
```

`Toy.CFI.lsdaAdjacent` (`lean/ToyCFI/LSDA.lean:210-211`):

```lean
-- lean/ToyCFI/LSDA.lean:210-211
/-- Adjacent ranges `[0,4) ↦ 1` and `[4,8) ↦ 2`. -/
def lsdaAdjacent : LSDA := [⟨0, 4, some 1⟩, ⟨4, 8, some 2⟩]
```

`Toy.CFI.flCaller` (`lean/ToyCFI/MultiFrame.lean:385-386`):

```lean
-- lean/ToyCFI/MultiFrame.lean:385-386
/-- Caller, true state and rows used below. -/
def flCaller : Caller := ⟨100, ⟨0, 5, 6, 0⟩⟩
```

`Toy.CFI.flSigma` (`lean/ToyCFI/MultiFrame.lean:387-387`):

```lean
-- lean/ToyCFI/MultiFrame.lean:387-387
def flSigma : MState := ⟨⟨100, 5, 6, 0⟩, fun _ => 0⟩
```

`Toy.CFI.flRowSaved` (`lean/ToyCFI/MultiFrame.lean:388-388`):

```lean
-- lean/ToyCFI/MultiFrame.lean:388-388
def flRowSaved : Row := ⟨.sp, 0, ⟨.same, .offset (-1), .same, .same⟩⟩
```

`Toy.CFI.flSigmaSaved` (`lean/ToyCFI/MultiFrame.lean:389-389`):

```lean
-- lean/ToyCFI/MultiFrame.lean:389-389
def flSigmaSaved : MState := ⟨⟨100, 0, 6, 0⟩, fun a => if a = 99 then 5 else 0⟩
```

`Toy.CFI.innerFn` (`lean/ToyCFI/MultiFrameExamples.lean:11-14`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:11-14
/-- Inner function: frame-pointer prologue, a call (at address 2), epilogue. -/
def innerFn : Func :=
  { blocks := [⟨[.push .fp, .movReg .fp .sp, .call, .movReg .sp .fp, .pop .fp, .ret], []⟩],
    layout := [0] }
```

`Toy.CFI.outerFn` (`lean/ToyCFI/MultiFrameExamples.lean:16-17`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:16-17
/-- Outer function: allocate two words, call (at address 1), release, return. -/
def outerFn : Func := { blocks := [⟨[.subSp 2, .call, .addSp 2, .ret], []⟩], layout := [0] }
```

`Toy.CFI.innerT1Fn` (`lean/ToyCFI/MultiFrameExamples.lean:19-24`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:19-24
/-- Inner function that also overwrites the scratch register `t1` before its call
(at address 3). -/
def innerT1Fn : Func :=
  { blocks := [⟨[.push .fp, .movReg .fp .sp, .movReg .t1 .sp, .call, .movReg .sp .fp, .pop .fp,
      .ret], []⟩],
    layout := [0] }
```

`Toy.CFI.outerT1Fn` (`lean/ToyCFI/MultiFrameExamples.lean:26-28`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:26-28
/-- Outer function anchoring its CFA in the scratch register `t1`; call at address 2. -/
def outerT1Fn : Func :=
  { blocks := [⟨[.movReg .t1 .sp, .subSp 2, .call, .addSp 2, .ret], []⟩], layout := [0] }
```

`Toy.CFI.outerT1CFI` (`lean/ToyCFI/MultiFrameExamples.lean:30-32`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:30-32
/-- `outerT1Fn`'s table: `CFA = t1 + 0` from address 1 on. -/
def outerT1CFI : List CFIInst :=
  [.advanceLoc 1, .defCfaRegister .t1, .advanceLoc 1, .advanceLoc 1, .advanceLoc 1, .advanceLoc 1]
```

`Toy.CFI.clobberFn` (`lean/ToyCFI/MultiFrameExamples.lean:34-36`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:34-36
/-- Innermost function that stores `t1` at its own CFA (into its caller's frame),
then calls (at address 1). -/
def clobberFn : Func := { blocks := [⟨[.saveAt .t1 0, .call, .ret], []⟩], layout := [0] }
```

`Toy.CFI.innerFrame` (`lean/ToyCFI/MultiFrameExamples.lean:51-53`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:51-53
def innerFrame : Frame :=
  { fn := innerFn, prog := genCFI innerFn (inferredAnn innerFn), lsda := none, callPC := 2,
    frameSize := 1 }
```

`Toy.CFI.outerFrame` (`lean/ToyCFI/MultiFrameExamples.lean:54-56`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:54-56
def outerFrame : Frame :=
  { fn := outerFn, prog := genCFI outerFn (inferredAnn outerFn), lsda := some [⟨1, 2, some 7⟩],
    callPC := 1, frameSize := 2 }
```

`Toy.CFI.topCaller` (`lean/ToyCFI/MultiFrameExamples.lean:58-58`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:58-58
def topCaller : Caller := ⟨1000, ⟨0, 11, 22, 33⟩⟩
```

`Toy.CFI.topMem` (`lean/ToyCFI/MultiFrameExamples.lean:59-59`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:59-59
def topMem : Int → Int := fun _ => 0
```

`Toy.CFI.outerSt` (`lean/ToyCFI/MultiFrameExamples.lean:61-62`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:61-62
/-- True state of the outer frame at its call. -/
def outerSt : MState := step (entryState topCaller topMem) (.subSp 2)
```

`Toy.CFI.ctxOf` (`lean/ToyCFI/MultiFrameExamples.lean:63-64`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:63-64
/-- Caller context of a frame called from state `s`. -/
def ctxOf (s : MState) : Caller := ⟨s.regs.get .sp, s.regs⟩
```

`Toy.CFI.innerSt` (`lean/ToyCFI/MultiFrameExamples.lean:65-67`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:65-67
/-- True state of the inner frame at its call (called from `outerSt`). -/
def innerSt : MState :=
  step (step (entryState (ctxOf outerSt) outerSt.mem) (.push .fp)) (.movReg .fp .sp)
```

`Toy.CFI.frames2` (`lean/ToyCFI/MultiFrameExamples.lean:69-69`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:69-69
def frames2 : List Frame := [innerFrame, outerFrame]
```

`Toy.CFI.truth2` (`lean/ToyCFI/MultiFrameExamples.lean:70-70`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:70-70
def truth2 : List MState := [innerSt, outerSt]
```

`Toy.CFI.innerFrameBad` (`lean/ToyCFI/MultiFrameExamples.lean:183-184`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:183-184
/-- The inner frame with the empty program (the initial row everywhere). -/
def innerFrameBad : Frame := { innerFrame with prog := [] }
```

`Toy.CFI.innerFrameTerm` (`lean/ToyCFI/MultiFrameExamples.lean:209-211`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:209-211
/-- The inner frame with an empty call-site table: its call PC is not found and
the toy personality terminates. -/
def innerFrameTerm : Frame := { innerFrame with lsda := some [] }
```

`Toy.CFI.outerFrameNoLsda` (`lean/ToyCFI/MultiFrameExamples.lean:236-237`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:236-237
/-- The outer frame without a call-site table: it is skipped too. -/
def outerFrameNoLsda : Frame := { outerFrame with lsda := none }
```

`Toy.CFI.outerFrameMalformed` (`lean/ToyCFI/MultiFrameExamples.lean:543-545`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:543-545
/-- The outer frame with a malformed program (`restoreState` on an empty
stack): it has no row at its call site. -/
def outerFrameMalformed : Frame := { outerFrame with prog := [.restoreState] }
```

`Toy.CFI.outerFrameUnsorted` (`lean/ToyCFI/MultiFrameExamples.lean:608-611`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:608-611
/-- The outer frame with an unsorted table whose second entry covers the call
PC with landing pad `7`. -/
def outerFrameUnsorted : Frame :=
  { outerFrame with lsda := some [⟨10, 20, some 1⟩, ⟨1, 2, some 7⟩] }
```

`Toy.CFI.innerT1Frame` (`lean/ToyCFI/MultiFrameExamples.lean:263-265`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:263-265
def innerT1Frame : Frame :=
  { fn := innerT1Fn, prog := genCFI innerT1Fn (inferredAnn innerT1Fn), lsda := none, callPC := 3,
    frameSize := 1 }
```

`Toy.CFI.outerT1Frame` (`lean/ToyCFI/MultiFrameExamples.lean:266-268`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:266-268
def outerT1Frame : Frame :=
  { fn := outerT1Fn, prog := outerT1CFI, lsda := some [⟨2, 3, some 7⟩], callPC := 2,
    frameSize := 2 }
```

`Toy.CFI.outerT1St` (`lean/ToyCFI/MultiFrameExamples.lean:270-271`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:270-271
def outerT1St : MState :=
  step (step (entryState topCaller topMem) (.movReg .t1 .sp)) (.subSp 2)
```

`Toy.CFI.innerT1St` (`lean/ToyCFI/MultiFrameExamples.lean:272-274`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:272-274
def innerT1St : MState :=
  step (step (step (entryState (ctxOf outerT1St) outerT1St.mem) (.push .fp)) (.movReg .fp .sp))
    (.movReg .t1 .sp)
```

`Toy.CFI.middleFrame` (`lean/ToyCFI/MultiFrameExamples.lean:333-333`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:333-333
def middleFrame : Frame := { innerFrame with lsda := none }
```

`Toy.CFI.clobberFrame` (`lean/ToyCFI/MultiFrameExamples.lean:334-336`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:334-336
def clobberFrame : Frame :=
  { fn := clobberFn, prog := genCFI clobberFn (inferredAnn clobberFn), lsda := none, callPC := 1,
    frameSize := 0 }
```

`Toy.CFI.middleSt` (`lean/ToyCFI/MultiFrameExamples.lean:338-339`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:338-339
/-- True state of the middle frame (the inner function called from `outerSt`). -/
def middleSt : MState := innerSt
```

`Toy.CFI.clobberSt` (`lean/ToyCFI/MultiFrameExamples.lean:340-342`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:340-342
/-- True state of the innermost frame: it stored `t1` at its CFA, which is the
middle frame's save slot for `fp`. -/
def clobberSt : MState := step (entryState (ctxOf middleSt) middleSt.mem) (.saveAt .t1 0)
```

`Toy.CFI.frames3` (`lean/ToyCFI/MultiFrameExamples.lean:344-344`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:344-344
def frames3 : List Frame := [clobberFrame, middleFrame, outerFrame]
```

`Toy.CFI.truth3` (`lean/ToyCFI/MultiFrameExamples.lean:345-345`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:345-345
def truth3 : List MState := [clobberSt, middleSt, outerSt]
```

`Toy.CFI.innerStBad` (`lean/ToyCFI/MultiFrameExamples.lean:419-420`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:419-420
/-- `innerSt` with `fp` replaced by `900`: not a reachable state of `innerFn`. -/
def innerStBad : MState := { innerSt with regs := innerSt.regs.set .fp 900 }
```

</details>

### Key definitions unfolded

The renderings below are prose paraphrases, not Lean terms; the verbatim Lean definitions are quoted under
**Definitions** above.

* `TableCorrect f prog` ≡ for all `c : Caller`, `m : Int → Int`, `b k : Nat`, `st : MState`, if
  `Reach f c m b k st` then there are `pc` and `R` with `f.pcOf b k = some pc`, `rowAt? prog pc = some R`, and
  `st.regs.get R.cfaReg + R.cfaOff = c.cfa` and, for `r ∈ [fp, s1]`, `st.regs.get r = c.regs.get r` if
  `R.rules.get r = same`, `st.mem (c.cfa + k) = c.regs.get r` if `R.rules.get r = offset k`.
* `rowAt? prog pc`: run `prog` from location 0, row `initRow` (`CFA = sp + 0`, all `same`), empty stack;
  `advanceLoc d` with `pc < loc + d` stops and returns the current row; `rememberState` pushes the whole row (CFA
  rule included); `restoreState` pops it, or yields `none` on an empty stack.
* `Inv A c st` ≡ every register `r` satisfies `A.regs.get r` and every slot `k` satisfies `slotAt A.slots k` (the
  first entry for `k` wins), where `cfaRel d` means "equals `c.cfa + d`", `callerOf r'` means "equals
  `c.regs.get r'`", `unknown` is no constraint; slot `k` concerns memory at `c.cfa + k`.
* `leqA A B = true` ≡ every register fact of `B` is a fact of `A`, and for every entry `(k, _)` of `B.slots`,
  `slotAt B.slots k` is `unknown` or equals `slotAt A.slots k` (shadowed entries of `B` are ignored).
* `entails A R = true` ≡ `A.regs.get R.cfaReg = cfaRel (-R.cfaOff)` and, for `r ∈ [fp, s1]`, either
  `R.rules.get r = same ∧ A.regs.get r = callerOf r` or `R.rules.get r = offset k ∧ slotAt A.slots k = callerOf r`.
* `stateRecoverableB A = true` ≡ some register of `A` is `cfaRel _`, and each `r ∈ [fp, s1]` has
  `A.regs.get r = callerOf r` or some slot entry `(k, _)` with `slotAt A.slots k = callerOf r`; equivalently
  (`stateRecoverableB_iff_exists_entails`) `∃ R, entails A R = true`.
* `annSoundB f ann = true` ≡ `ann 0 = some A` with `leqA absInit A`, and for every block index `b <
  f.blocks.length` with `ann b = some A` and every successor `b'`, `ann b' = some B` with
  `leqA (absRun A (f.blockOps b)) B`.
* `annRecoverableB f ann = true` ≡ (`annRecoverableB_iff`) for every `b < f.blocks.length` with `ann b = some A` and
  every `k < (f.blockOps b).length`, `∃ R, entails (absAt f A b k) R = true`.
* `checkWith f prog ann = annSoundB f ann && (∀ annotated b, ∀ k < len b, rowAt? prog (pcOf b k) = some R ∧
  entails (absAt f A b k) R)`; `checkCFI f prog = checkWith f prog (inferred annotation)` (false if inference
  does not stabilize).
* `ConflictingCfaOffsetsAt f b k` ≡ for every register `r` there are reachable states `st₁` (caller `c₁`) and `st₂`
  (caller `c₂`) at `(b, k)` with `st₁.regs.get r - c₁.cfa ≠ st₂.regs.get r - c₂.cfa`.
* `frameAction fr`: no call-site table → `skip`; otherwise `lookupScan t fr.callPC`: landing pad `lp` →
  `handle lp`, entry without landing pad → `skip`, not found → `terminate`.
* `unwindFrom (fr :: rest) d st`: `handle lp` → `caught d lp st`; `terminate` → `terminated d`; `skip` →
  continue with `unwindRegs R st` (sp := CFA, other registers by their rules, memory unchanged) where
  `R = rowAt? fr.prog fr.callPC` (`malformed d` if there is no row).
* `CaughtWithCallerState frames truth top st0 j lp frj stj` ≡ there are `st` and `R` with
  `unwind frames st0 = caught j lp st`, `st` agreeing with `stj` on `sp`, `fp`, `s1`, `st.mem = st0.mem`,
  `rowAt? frj.prog frj.callPC = some R`, `cfaOf R st = (callerCtx truth top j).cfa`, and
  `frameBase R st frj.frameSize = (callerCtx truth top j).cfa - frj.frameSize`.

* `Recovers R c st` ≡ `cfaOf R st = c.cfa` and, for `r ∈ [fp, s1]`, `ruleVal R st r = c.regs.get r`, where `cfaOf R st = st.regs.get R.cfaReg + R.cfaOff` and `ruleVal` reads the register itself for `same` and `st.mem (cfaOf R st + k)` for `offset k`. `Row.rules.sp` and `t1` are never read.
* `Reach f c m b k st`: block 0, offset 0 is reached in `entryState c m` (sp = CFA, other registers = caller values, memory `m`) if block 0 is non-empty; each operation steps with `step`; after the last operation of a block, every successor `b'` with a non-empty block is reached at offset 0. The layout plays no role (`Reach.layout_irrelevant`).
* `e.contains pc` ≡ `e.start ≤ pc ∧ pc < e.stop`. `lookupFirst t pc`: the outcome (`CallSite.result`: landing pad or 'no landing pad') of the first entry containing `pc`, else `notFound`. `lookupScan t pc`: walks the entries in order and returns `notFound` at the first entry with `pc < start`, the entry's outcome if `pc < stop`, and otherwise continues. `lookupIncl`: like `lookupFirst` with the test `start ≤ pc ∧ pc ≤ stop`.
* `UniqueAt t pc` ≡ any two entries of `t` that contain `pc` are equal as values. `SortedByStart t` ≡ `t.Pairwise (·.start ≤ ·.start)`. `NonOverlapping t` ≡ entries at distinct positions never both contain a `pc`.

### R1: `genCFI_tableCorrect_of_sound_recoverable_annotation`

- **Kind:** theorem.  **Tier:** T1 (folklore made precise).  **Depth:** substantive.
- **Plain claim:** If every non-empty block of a function appears in its layout, the block annotation is sound (block 0's state is implied by the entry state and, along every CFG edge, the abstract exit state of a block is at least as precise as the successor's single annotated entry state), and at every PC of every annotated block the abstract state is recoverable - some row is entailed by it (annRecoverableB_iff), a condition that does not mention the emitter - then the program emitted by genCFI (row deltas inside blocks, and at a layout boundary whose inherited row differs from the entry row either rememberState at the start of the layout predecessor plus restoreState, or an explicit re-definition) is TableCorrect.
- **Key definitions:** `TableCorrect`, `Recovers`, `rowAt?`, `Reach`, `LayoutCovers`, `annSoundB`, `leqA`, `annRecoverableB`, `stateRecoverableB`, `entails`, `genCFI` (all quoted under Definitions; unfolded forms under Key definitions unfolded).

Lean statement (proof elided as `…`):

`Toy.CFI.genCFI_tableCorrect_of_sound_recoverable_annotation` (`lean/ToyCFI/Generic.lean:269-281`):

```lean
-- lean/ToyCFI/Generic.lean:269-281
/-- **Generator correctness (general case).** If every non-empty block appears
in the layout, the annotation is sound (block `0`'s state is implied by the
entry state, and along every CFG edge a block's abstract exit state is at least
as precise as the successor's annotated entry state — one entry frame state per
block, shared by all incoming edges), and at every PC of every annotated block
the abstract state is recoverable (some row is entailed by it; see
`annRecoverableB_iff`), then the program emitted by `genCFI` (row deltas inside
blocks; at a layout boundary whose inherited row differs from the entry row,
`rememberState` at the start of the layout predecessor plus `restoreState`, or
an explicit re-definition) is correct. -/
theorem genCFI_tableCorrect_of_sound_recoverable_annotation (f : Func) (ann : Ann)
    (hcover : LayoutCovers f) (hsound : annSoundB f ann = true)
    (hrec : annRecoverableB f ann = true) : TableCorrect f (genCFI f ann) := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hcover : LayoutCovers f` | every reachable block needs a linear address | tight: counterexample `genCFI_incorrect_without_layoutCovers`; witness class: a concrete 3-block function, `coldFnMissing` (the blocks of `coldFn` with layout `[0, 1]`), whose reachable cold block 2 has no address; its inferred annotation is sound and recoverable |
| `hsound : annSoundB f ann = true` | one entry frame state per block, consistent with every incoming CFG edge (and with function entry) | tight: counterexample `genCFI_incorrect_without_annSound`; witness class: the concrete 3-block function `coldFn` (covering layout 0, 1, 2) with the hand-written annotation `coldBadAnn`, which is recoverable but unsound at the cold block 2 |
| `hrec : annRecoverableB f ann = true` | at every PC of every annotated block some row is entailed by the abstract state: some register holds a CFA-relative value and each callee-saved register holds the caller's value or is the (unshadowed) content of a CFA-relative slot; emitter-independent (stateRecoverableB_iff_exists_entails, annRecoverableB_iff) | tight: counterexample `genCFI_incorrect_without_annRecoverable`; witness class: the concrete 4-block merge function `mergeFn` (covering layout) with its inferred annotation, which is sound but not recoverable (`annRecoverableB = false`) |

**Depth:** substantive. Proved through an encoder lemma (`rowAt_genCFI_eq_rowOf`: at every PC of an annotated, laid-out block the emitted program's row is the derived row `rowOf` of the abstract state), induction over the layout with the state stack as invariant, completeness of `rowOf` for recoverable states (`entails_rowOf_of_stateRecoverableB`), and the checker soundness lemma `checkWith_sound`.

**Non-vacuity witness:** coldFn (epilogue placed before a cold block) with its inferred annotation satisfies all three hypotheses; the generated program uses rememberState/restoreState and is correct (genCFI_coldFn_tableCorrect). A second instance with a user-supplied annotation containing shadowed slot entries is genCFI_shadowedClobberFn_tableCorrect, which applies this theorem directly. (`genCFI_hypotheses_hold_coldFn`)

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.genCFI_incorrect_without_layoutCovers` (`lean/ToyCFI/Generic.lean:347-352`):

```lean
-- lean/ToyCFI/Generic.lean:347-352
/-- Tightness of layout coverage: the annotation is sound and recoverable, but a
reachable block has no address, so no table is correct. -/
theorem genCFI_incorrect_without_layoutCovers :
    ¬ LayoutCovers coldFnMissing ∧ annSoundB coldFnMissing (inferredAnn coldFnMissing) = true ∧
      annRecoverableB coldFnMissing (inferredAnn coldFnMissing) = true ∧
      ¬ TableCorrect coldFnMissing (genCFI coldFnMissing (inferredAnn coldFnMissing)) := …
```

`Toy.CFI.genCFI_incorrect_without_annSound` (`lean/ToyCFI/Generic.lean:322-326`):

```lean
-- lean/ToyCFI/Generic.lean:322-326
/-- Tightness of soundness: `coldBadAnn` is recoverable and the layout covers all
blocks, but the annotation is unsound and the generated table is incorrect. -/
theorem genCFI_incorrect_without_annSound :
    LayoutCovers coldFn ∧ annSoundB coldFn coldBadAnn = false ∧
      annRecoverableB coldFn coldBadAnn = true ∧ ¬ TableCorrect coldFn (genCFI coldFn coldBadAnn) := …
```

`Toy.CFI.genCFI_incorrect_without_annRecoverable` (`lean/ToyCFI/Generic.lean:334-340`):

```lean
-- lean/ToyCFI/Generic.lean:334-340
/-- Tightness of recoverability: `mergeFn` with its inferred annotation has a
covering layout and a sound annotation, but no table (in particular not the
generated one) is correct. -/
theorem genCFI_incorrect_without_annRecoverable :
    LayoutCovers mergeFn ∧ annSoundB mergeFn (inferredAnn mergeFn) = true ∧
      annRecoverableB mergeFn (inferredAnn mergeFn) = false ∧
      ¬ TableCorrect mergeFn (genCFI mergeFn (inferredAnn mergeFn)) := …
```

`Toy.CFI.genCFI_hypotheses_hold_coldFn` (`lean/ToyCFI/Generic.lean:306-311`):

```lean
-- lean/ToyCFI/Generic.lean:306-311
/-- Non-vacuity: `coldFn` with its inferred annotation satisfies all hypotheses
(and its generated program, which uses `rememberState`/`restoreState`, is
correct: `genCFI_coldFn_tableCorrect`). -/
theorem genCFI_hypotheses_hold_coldFn :
    LayoutCovers coldFn ∧ annSoundB coldFn (inferredAnn coldFn) = true ∧
      annRecoverableB coldFn (inferredAnn coldFn) = true := …
```

</details>

**Prior art.**

- LLVM CFIFixup pass, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, llvm/lib/CodeGen/CFIFixup.cpp: header comment (lines 10-66) - after the prologue each block either 'has a call frame' or not; where the state at a block's start differs from the state at the end of its layout predecessor, the pass inserts either a target-specific reset to the initial state or '.cfi_restore_state' followed by '.cfi_remember_state', with a '.cfi_remember_state' after the last prologue CFI instruction; stated preconditions include 'CFI instructions are not contained in any loops'; stated limitations: an epilogue preceding the prologue in layout, and functions using SP as frame pointer with SP adjustments in different blocks. insertRememberRestorePair (line 195), fixupBlock (line 245). Derived (modeling bridge): the toy genCFI handles arbitrary rows rather than the pass's two states, but it remembers a row only at the start of the immediately preceding layout block and otherwise falls back to explicit re-definition, whereas the pass keeps one remember insertion point per section and chains remember/restore pairs across any number of intervening blocks (fixupBlock, lines 288-300; runImpl, lines 304-341) and, for the first block of a new section, clones the prologue's CFI instructions instead (lines 290-294). genCFI was not compared against the pass's output.
- LLVM CFIInstrInserter pass, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, llvm/lib/CodeGen/CFIInstrInserter.cpp: header comment (lines 9-17) - verifies that the outgoing CFA information of predecessors matches the incoming information of successors and inserts CFI instructions at block beginnings when 'a non-linear layout of blocks' leaves an incorrect rule. Besides the CFA offset and register it tracks callee-saved register save locations (CSRSavedLocation with kinds Register and CFAOffset, CSRLocMap, IncomingCSRSaved/OutgoingCSRSaved; lines 64-162; propagated along CFG edges, line 408), repairs them at block beginnings with .cfi_restore, .cfi_offset and .cfi_register (insertCFIInstrs, lines 415-511; a block that begins a new section gets a full def_cfa plus the callee-saved moves, lines 431-470), and reports CFG-edge CFA and callee-saved mismatches in verify (lines 545-571; CFA mismatches into blocks with no successors that are not return blocks are exempt, lines 553-557). It requires a single save location per callee-saved register ('Different saved locations for the same CSR', lines 366-369). In builds with assertions (#ifndef NDEBUG) it accepts cfi_remember_state/cfi_restore_state only as balanced depth-1 pairs inside one basic block and otherwise reports 'Support for cfi_remember_state not implemented!' (lines 316-339, 375-381); in builds without assertions its analysis ignores both instructions. Derived (modeling bridge): this is the explicit re-definition alternative; like the toy genCFI it repairs both the CFA rule and callee-saved register rules at layout boundaries, but it never places a remember/restore pair across blocks. It was not compared against the toy's output.
- T. Bastian, S. Kell, F. Zappa Nardelli, 'Reliable and fast DWARF-based stack unwinding', Proc. ACM Program. Lang. 3(OOPSLA), Article 146, October 2019, doi:10.1145/3360572. §2.2 (pp. 146:8-146:12; the passages summarized here are on pp. 146:9-146:11): unwind rows are synthesized by forward propagation along CFG edges, relying on stack offsets being invariant at merge points; with variable-size stack allocation compilers fall back to a base-pointer register; if different rows reach a merge point the tool aborts (a lossy merge is enabled only for terminal blocks). Appendix A (pp. 146:21-146:23): remember_state pushes 'the state of all the registers of this row', and restore(reg) is not supported (p. 146:21); the formal interpretation keeps a state-saving stack of rows (Row*, p. 146:22; Table 5, p. 146:23). The paper contains no mechanized proof.
- DWARF Debugging Information Format Committee, DWARF Debugging Information Format, Version 5 (February 13, 2017), https://dwarfstd.org/doc/DWARF5.pdf. §2.5.1.2 DW_OP_fbreg (an offset from the address given by DW_AT_frame_base); §2.5.1.3 item 15 (printed page 33; PDF page 51) DW_OP_call_frame_cfa (pushes the CFA obtained from the call frame information; computing DW_AT_frame_base from registers would 'in some cases ... require an extensive location list because the values of the registers used in computing the CFA change during a subroutine'). §6.4.2.4 (printed page 181; PDF page 199) DW_CFA_remember_state / DW_CFA_restore_state ('push the set of rules for every register onto an implicit stack' / 'pop the set of rules off the implicit stack and place them in the current row') in the wording quoted by DWARF issue 230103.1. The toy's register rules and CFA-definition instructions are modeled on the pinned LLVM libunwind implementation (libunwind/src/DwarfParser.hpp and DwarfInstructions.hpp at llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc) rather than on the text of §6.4.1 and §6.4.2.2.
- DWARF issue 230103.1, 'Clarify that DW_CFA_remember_state includes the current CFA' (F. Song; submitted 2023-01-03; accepted 2023-07-24; DWARF Version 6), https://dwarfstd.org/issues/230103.1.html: proposes 'push the set of rules for the current CFA and every register onto an implicit stack' and states that nongnu libunwind src/dwarf/Gparser.c, libgcc unwind-dw2.c and llvm-project libunwind/src/DwarfParser.hpp all include the current CFA in the implicit stack. Derived (modeling bridge): the toy rememberState/restoreState save and restore the whole row, CFA rule included.

**Design question:** What must a CFI emitter guarantee for a linear layout of a CFG whose blocks are not placed in control-flow order, and which checks of the emitted table are sound?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM CFIFixup (llvm/llvm-project 701f926a): the toy genCFI handles arbitrary rows rather than the pass's two states, but it remembers a row only at the start of the immediately preceding layout block and otherwise falls back to explicit re-definition, whereas the pass keeps one remember insertion point per section and chains remember/restore pairs across any number of intervening blocks (fixupBlock, lines 288-300; runImpl, lines 304-341) and, for the first block of a new section, clones the prologue's CFI instructions instead (lines 290-294). genCFI was not compared against the pass's output.
- LLVM CFIInstrInserter (llvm/llvm-project 701f926a): this is the explicit re-definition alternative; like the toy genCFI it repairs both the CFA rule and callee-saved register rules at layout boundaries, but it never places a remember/restore pair across blocks. It was not compared against the toy's output.
- DWARF issue 230103.1: the toy rememberState/restoreState save and restore the whole row, CFA rule included.
- General: the theorem transfers to a real emitter only to the extent that the emitter's rows, layout boundaries and abstract frame states match the toy definitions; the gaps are listed under **Applicability** and in this result's non-claims (in particular `call` as a no-op and rows at every PC).

### R2: `no_tableCorrect_of_conflictingCfaOffsetsAt`

- **Kind:** impossibility.  **Tier:** T1 (folklore made precise).  **Depth:** shallow.
- **Plain claim:** If at some PC (b, k) of a function no register keeps a fixed offset from the CFA across reachable states - for every register r there are two reachable states there (for possibly different callers and memories) in which r - CFA differs (ConflictingCfaOffsetsAt f b k) - then no CFI program whatsoever is TableCorrect for the function: a row is a function of the PC, and a register+offset CFA rule is right only if its base register has a fixed offset from the CFA. mergeFn, where one CFG path into block 3 pushes fp and the other does not, satisfies the hypothesis at its merge PC (mergeFn_conflictingCfaOffsetsAt), so no table is correct for it (mergeFn_no_tableCorrect).
- **Key definitions:** `ConflictingCfaOffsetsAt` (for every register `r` there are reachable states at `(b, k)` whose offsets `r - CFA` differ), `TableCorrect`, `rowAt?`, `Reach`.

Lean statement (proof elided as `…`):

`Toy.CFI.no_tableCorrect_of_conflictingCfaOffsetsAt` (`lean/ToyCFI/Merge.lean:47-53`):

```lean
-- lean/ToyCFI/Merge.lean:47-53
/-- **Impossibility (merge point).** If at some PC `(b, k)` every register's
offset from the CFA varies across reachable states
(`ConflictingCfaOffsetsAt`), then no CFI program whatsoever is correct for `f`:
a row is a function of the PC, and a register+offset CFA rule computes the CFA
only if its base register has a fixed offset from the CFA. -/
theorem no_tableCorrect_of_conflictingCfaOffsetsAt {f : Func} {b k : Nat}
    (hconf : ConflictingCfaOffsetsAt f b k) (prog : List CFIInst) : ¬ TableCorrect f prog := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hconf : ConflictingCfaOffsetsAt f b k` | at one PC, every register's offset from the CFA varies across reachable states, so no register+offset CFA rule can be right there | tight: counterexample `no_tableCorrect_fails_without_conflictingCfaOffsetsAt`; witness class: the concrete 4-block function `mergeFnBalanced` at its merge PC (3, 0), where both incoming paths push `fp`; a correct table exists |

**Depth:** shallow. The row at `(b, k)` is fixed by the PC; applying `TableCorrect` to two reachable states whose offsets from the CFA differ in that row's CFA base register gives two different CFAs from one rule.

**Non-vacuity witness:** mergeFn at its merge PC (3, 0): sp is CFA - 1 via block 1 and CFA via block 2; fp, s1, t1 hold caller values whose offset from the CFA depends on the caller. (`mergeFn_conflictingCfaOffsetsAt`)

**Positive control:** `genCFI_mergeFnBalanced_tableCorrect`. When both incoming paths of the merge block push `fp` (`mergeFnBalanced`), the generated table is `TableCorrect`: the conclusion fails in this nearby setting.

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.no_tableCorrect_fails_without_conflictingCfaOffsetsAt` (`lean/ToyCFI/Merge.lean:98-103`):

```lean
-- lean/ToyCFI/Merge.lean:98-103
/-- Tightness of `ConflictingCfaOffsetsAt`: at the merge PC `(3, 0)` of
`mergeFnBalanced` the condition fails (some register keeps a fixed CFA offset)
and a correct table exists. -/
theorem no_tableCorrect_fails_without_conflictingCfaOffsetsAt :
    ¬ ConflictingCfaOffsetsAt mergeFnBalanced 3 0 ∧
      ∃ prog, TableCorrect mergeFnBalanced prog := …
```

`Toy.CFI.mergeFn_conflictingCfaOffsetsAt` (`lean/ToyCFI/Merge.lean:65-68`):

```lean
-- lean/ToyCFI/Merge.lean:65-68
/-- Non-vacuity: in `mergeFn` the merge PC `(3, 0)` has conflicting CFA
offsets (`sp` is `CFA - 1` via block 1 and `CFA` via block 2; `fp`, `s1`, `t1`
hold caller values, whose offset from the CFA depends on the caller). -/
theorem mergeFn_conflictingCfaOffsetsAt : ConflictingCfaOffsetsAt mergeFn 3 0 := …
```

`Toy.CFI.genCFI_mergeFnBalanced_tableCorrect` (`lean/ToyCFI/Merge.lean:85-88`):

```lean
-- lean/ToyCFI/Merge.lean:85-88
/-- Positive control: when both paths push `fp` (`mergeFnBalanced`), the
generated table is correct. -/
theorem genCFI_mergeFnBalanced_tableCorrect :
    TableCorrect mergeFnBalanced (genCFI mergeFnBalanced (inferredAnn mergeFnBalanced)) := …
```

</details>

**Prior art.**

- T. Bastian, S. Kell, F. Zappa Nardelli, 'Reliable and fast DWARF-based stack unwinding', Proc. ACM Program. Lang. 3(OOPSLA), Article 146, October 2019, doi:10.1145/3360572. §2.2 (pp. 146:8-146:12; the passages summarized here are on pp. 146:9-146:11): unwind rows are synthesized by forward propagation along CFG edges, relying on stack offsets being invariant at merge points; with variable-size stack allocation compilers fall back to a base-pointer register; if different rows reach a merge point the tool aborts (a lossy merge is enabled only for terminal blocks). Appendix A (pp. 146:21-146:23): remember_state pushes 'the state of all the registers of this row', and restore(reg) is not supported (p. 146:21); the formal interpretation keeps a state-saving stack of rows (Row*, p. 146:22; Table 5, p. 146:23). The paper contains no mechanized proof.
- LLVM CFIInstrInserter pass, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, llvm/lib/CodeGen/CFIInstrInserter.cpp: header comment (lines 9-17) - verifies that the outgoing CFA information of predecessors matches the incoming information of successors and inserts CFI instructions at block beginnings when 'a non-linear layout of blocks' leaves an incorrect rule. Besides the CFA offset and register it tracks callee-saved register save locations (CSRSavedLocation with kinds Register and CFAOffset, CSRLocMap, IncomingCSRSaved/OutgoingCSRSaved; lines 64-162; propagated along CFG edges, line 408), repairs them at block beginnings with .cfi_restore, .cfi_offset and .cfi_register (insertCFIInstrs, lines 415-511; a block that begins a new section gets a full def_cfa plus the callee-saved moves, lines 431-470), and reports CFG-edge CFA and callee-saved mismatches in verify (lines 545-571; CFA mismatches into blocks with no successors that are not return blocks are exempt, lines 553-557). It requires a single save location per callee-saved register ('Different saved locations for the same CSR', lines 366-369). In builds with assertions (#ifndef NDEBUG) it accepts cfi_remember_state/cfi_restore_state only as balanced depth-1 pairs inside one basic block and otherwise reports 'Support for cfi_remember_state not implemented!' (lines 316-339, 375-381); in builds without assertions its analysis ignores both instructions. Derived (modeling bridge): this is the explicit re-definition alternative; like the toy genCFI it repairs both the CFA rule and callee-saved register rules at layout boundaries, but it never places a remember/restore pair across blocks. It was not compared against the toy's output.
- J. Oakley, S. Bratus, 'Exploiting the hard-working DWARF: Trojan and exploit techniques with no native executable code', USENIX WOOT 2011, https://www.usenix.org/conference/woot11/exploiting-hard-working-dwarf-trojan-and-exploit-techniques-no-native-executable: DWARF call-frame/expression bytecode interpreted by the unwinder is Turing-complete. Derived (modeling bridge): expression-based CFA rules (DW_CFA_def_cfa_expression, not modeled) are far more expressive than the toy's register+offset rule, so the impossibility results stated for register+offset rules are not claimed for them (whether they fail for such rules is not proved here).

**Design question:** What must a CFI emitter guarantee for a linear layout of a CFG whose blocks are not placed in control-flow order, and which checks of the emitted table are sound?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM CFIInstrInserter (llvm/llvm-project 701f926a): this is the explicit re-definition alternative; like the toy genCFI it repairs both the CFA rule and callee-saved register rules at layout boundaries, but it never places a remember/restore pair across blocks. It was not compared against the toy's output.
- Oakley and Bratus (2011): expression-based CFA rules (DW_CFA_def_cfa_expression, not modeled) are far more expressive than the toy's register+offset rule, so the impossibility results stated for register+offset rules are not claimed for them (whether they fail for such rules is not proved here).

### R3: `coldBlocks_no_row_recovers_at_both_epilogue_ret_and_cold_entry`

- **Kind:** impossibility.  **Tier:** T1 (folklore made precise).  **Depth:** shallow.
- **Plain claim:** For the blocks of coldFn - prologue (push fp; movReg fp sp; call), epilogue (movReg sp fp; pop fp; ret), and a cold block (call) entered with the frame established that jumps to the epilogue - placed in any layout, no single row recovers the caller both at every reachable state of the epilogue's ret (block 1, offset 2) and at every reachable state of the cold block's first PC (block 2, offset 0). This concerns two CFG program points: reachability does not depend on the layout, and the layout only decides whether the two points receive the same row (for layout 0, 1, 2, a program whose row at the cold block's address equals its row at the epilogue's ret is not TableCorrect: coldFn_not_tableCorrect_of_cold_entry_row_eq_epilogue_ret_row).
- **Key definitions:** `coldBlocks`, `Func`, `Reach`, `Recovers` (a single row `R`; the layout `lay` is universally quantified).

Lean statement (proof elided as `…`):

`Toy.CFI.coldBlocks_no_row_recovers_at_both_epilogue_ret_and_cold_entry` (`lean/ToyCFI/ColdBlock.lean:68-80`):

```lean
-- lean/ToyCFI/ColdBlock.lean:68-80
/-- **No single row serves the epilogue's `ret` and the cold block's entry, in
any layout.** For the blocks of `coldFn` (prologue; epilogue
`movReg sp fp; pop fp; ret`; cold block entered with the frame established)
placed in an arbitrary layout `lay`, no row recovers the caller both at every
reachable state of the epilogue's `ret` (block 1, offset 2) and at every
reachable state of the cold block's first PC (block 2, offset 0).  This is a
statement about two CFG program points, not about addresses: reachability does
not depend on the layout (`Reach.layout_irrelevant`).  What the layout decides
is whether the two points receive the same row
(`coldFn_not_tableCorrect_of_cold_entry_row_eq_epilogue_ret_row`). -/
theorem coldBlocks_no_row_recovers_at_both_epilogue_ret_and_cold_entry (lay : List Nat) :
    ¬ ∃ R : Row, (∀ c m st, Reach ⟨coldBlocks, lay⟩ c m 1 2 st → Recovers R c st) ∧
      (∀ c m st, Reach ⟨coldBlocks, lay⟩ c m 2 0 st → Recovers R c st) := …
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete objects.

**Depth:** shallow. Reduces, via `Reach.layout_irrelevant`, to the layout 0, 1, 2 and a case analysis of the row's CFA base register on the two reachable states.

**Non-vacuity witness:** Both program points are reachable for every caller and memory, with sp = CFA at the ret and sp = CFA - 1 at the cold entry (shown for layout 0, 1, 2; reachability is layout-independent, Reach.layout_irrelevant). (`coldFn_both_pcs_reachable`)

**Positive control:** `coldBlocks_one_row_recovers_at_epilogue_entry_and_cold_entry`. A different pair of program points of the same blocks, the epilogue's first PC and the cold block's entry, does share a recovering row, in every layout.

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.coldFn_both_pcs_reachable` (`lean/ToyCFI/ColdBlock.lean:44-48`):

```lean
-- lean/ToyCFI/ColdBlock.lean:44-48
/-- Non-vacuity: both PCs are reachable for every caller and memory, with
different `sp` offsets (`CFA` at address 5, `CFA - 1` at address 6). -/
theorem coldFn_both_pcs_reachable (c : Caller) (m : Int → Int) :
    Reach coldFn c m 1 2 (coldStRet c m) ∧ Reach coldFn c m 2 0 (coldStCold c m) ∧
      (coldStRet c m).regs.get .sp = c.cfa ∧ (coldStCold c m).regs.get .sp = c.cfa - 1 := …
```

`Toy.CFI.coldBlocks_one_row_recovers_at_epilogue_entry_and_cold_entry` (`lean/ToyCFI/ColdBlock.lean:172-179`):

```lean
-- lean/ToyCFI/ColdBlock.lean:172-179
/-- Positive control for the layout-independent impossibility: in every layout
of the same blocks, one row (`CFA = fp + 1`, `fp` saved at `CFA - 1`) recovers
the caller both at the epilogue's first PC (block 1, offset 0) and at the cold
block's first PC (block 2, offset 0), so "no single row serves two program
points" is specific to the pair (epilogue `ret`, cold entry). -/
theorem coldBlocks_one_row_recovers_at_epilogue_entry_and_cold_entry (lay : List Nat) :
    ∃ R : Row, (∀ c m st, Reach ⟨coldBlocks, lay⟩ c m 1 0 st → Recovers R c st) ∧
      (∀ c m st, Reach ⟨coldBlocks, lay⟩ c m 2 0 st → Recovers R c st) := …
```

</details>

**Prior art.**

- LLVM CFIFixup pass, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, llvm/lib/CodeGen/CFIFixup.cpp: header comment (lines 10-66) - after the prologue each block either 'has a call frame' or not; where the state at a block's start differs from the state at the end of its layout predecessor, the pass inserts either a target-specific reset to the initial state or '.cfi_restore_state' followed by '.cfi_remember_state', with a '.cfi_remember_state' after the last prologue CFI instruction; stated preconditions include 'CFI instructions are not contained in any loops'; stated limitations: an epilogue preceding the prologue in layout, and functions using SP as frame pointer with SP adjustments in different blocks. insertRememberRestorePair (line 195), fixupBlock (line 245). Derived (modeling bridge): the toy genCFI handles arbitrary rows rather than the pass's two states, but it remembers a row only at the start of the immediately preceding layout block and otherwise falls back to explicit re-definition, whereas the pass keeps one remember insertion point per section and chains remember/restore pairs across any number of intervening blocks (fixupBlock, lines 288-300; runImpl, lines 304-341) and, for the first block of a new section, clones the prologue's CFI instructions instead (lines 290-294). genCFI was not compared against the pass's output.
- LLVM CFIInstrInserter pass, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, llvm/lib/CodeGen/CFIInstrInserter.cpp: header comment (lines 9-17) - verifies that the outgoing CFA information of predecessors matches the incoming information of successors and inserts CFI instructions at block beginnings when 'a non-linear layout of blocks' leaves an incorrect rule. Besides the CFA offset and register it tracks callee-saved register save locations (CSRSavedLocation with kinds Register and CFAOffset, CSRLocMap, IncomingCSRSaved/OutgoingCSRSaved; lines 64-162; propagated along CFG edges, line 408), repairs them at block beginnings with .cfi_restore, .cfi_offset and .cfi_register (insertCFIInstrs, lines 415-511; a block that begins a new section gets a full def_cfa plus the callee-saved moves, lines 431-470), and reports CFG-edge CFA and callee-saved mismatches in verify (lines 545-571; CFA mismatches into blocks with no successors that are not return blocks are exempt, lines 553-557). It requires a single save location per callee-saved register ('Different saved locations for the same CSR', lines 366-369). In builds with assertions (#ifndef NDEBUG) it accepts cfi_remember_state/cfi_restore_state only as balanced depth-1 pairs inside one basic block and otherwise reports 'Support for cfi_remember_state not implemented!' (lines 316-339, 375-381); in builds without assertions its analysis ignores both instructions. Derived (modeling bridge): this is the explicit re-definition alternative; like the toy genCFI it repairs both the CFA rule and callee-saved register rules at layout boundaries, but it never places a remember/restore pair across blocks. It was not compared against the toy's output.
- DWARF Debugging Information Format Committee, DWARF Debugging Information Format, Version 5 (February 13, 2017), https://dwarfstd.org/doc/DWARF5.pdf. §2.5.1.2 DW_OP_fbreg (an offset from the address given by DW_AT_frame_base); §2.5.1.3 item 15 (printed page 33; PDF page 51) DW_OP_call_frame_cfa (pushes the CFA obtained from the call frame information; computing DW_AT_frame_base from registers would 'in some cases ... require an extensive location list because the values of the registers used in computing the CFA change during a subroutine'). §6.4.2.4 (printed page 181; PDF page 199) DW_CFA_remember_state / DW_CFA_restore_state ('push the set of rules for every register onto an implicit stack' / 'pop the set of rules off the implicit stack and place them in the current row') in the wording quoted by DWARF issue 230103.1. The toy's register rules and CFA-definition instructions are modeled on the pinned LLVM libunwind implementation (libunwind/src/DwarfParser.hpp and DwarfInstructions.hpp at llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc) rather than on the text of §6.4.1 and §6.4.2.2.
- DWARF issue 230103.1, 'Clarify that DW_CFA_remember_state includes the current CFA' (F. Song; submitted 2023-01-03; accepted 2023-07-24; DWARF Version 6), https://dwarfstd.org/issues/230103.1.html: proposes 'push the set of rules for the current CFA and every register onto an implicit stack' and states that nongnu libunwind src/dwarf/Gparser.c, libgcc unwind-dw2.c and llvm-project libunwind/src/DwarfParser.hpp all include the current CFA in the implicit stack. Derived (modeling bridge): the toy rememberState/restoreState save and restore the whole row, CFA rule included.

**Design question:** What must a CFI emitter guarantee for a linear layout of a CFG whose blocks are not placed in control-flow order, and which checks of the emitted table are sound?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM CFIFixup (llvm/llvm-project 701f926a): the toy genCFI handles arbitrary rows rather than the pass's two states, but it remembers a row only at the start of the immediately preceding layout block and otherwise falls back to explicit re-definition, whereas the pass keeps one remember insertion point per section and chains remember/restore pairs across any number of intervening blocks (fixupBlock, lines 288-300; runImpl, lines 304-341) and, for the first block of a new section, clones the prologue's CFI instructions instead (lines 290-294). genCFI was not compared against the pass's output.
- LLVM CFIInstrInserter (llvm/llvm-project 701f926a): this is the explicit re-definition alternative; like the toy genCFI it repairs both the CFA rule and callee-saved register rules at layout boundaries, but it never places a remember/restore pair across blocks. It was not compared against the toy's output.
- DWARF issue 230103.1: the toy rememberState/restoreState save and restore the whole row, CFA rule included.
- General: if a real table's row at a cold block placed after an epilogue is the inherited post-epilogue row, an unwinder interrupted at that block computes a CFA from a rule that is wrong there; that a given real compiler emits such a table is not shown here.

### R3b: `coldFn_not_tableCorrect_of_cold_entry_row_eq_epilogue_ret_row`

- **Kind:** impossibility.  **Tier:** T1 (folklore made precise).  **Depth:** shallow.
- **Plain claim:** For coldFn with layout 0, 1, 2 (epilogue at addresses 3-5 with ret at 5, cold block at 6), any CFI program whose row at address 6 equals its row at address 5 (as happens when no instruction is located at address 6, i.e. neither restoreState nor an explicit re-definition) is not TableCorrect.
- **Key definitions:** `coldFn` (`coldBlocks` with layout 0, 1, 2), `rowAt?`, `TableCorrect`.

Lean statement (proof elided as `…`):

`Toy.CFI.coldFn_not_tableCorrect_of_cold_entry_row_eq_epilogue_ret_row` (`lean/ToyCFI/ColdBlock.lean:86-91`):

```lean
-- lean/ToyCFI/ColdBlock.lean:86-91
/-- **Inherited row is wrong.** Any CFI program whose row at the cold block's
first PC (address 6) equals its row at the epilogue's `ret` (address 5) — as
happens when no instruction is located at address 6 — is not correct for
`coldFn` (layout `0, 1, 2`). -/
theorem coldFn_not_tableCorrect_of_cold_entry_row_eq_epilogue_ret_row (prog : List CFIInst)
    (hinh : rowAt? prog 6 = rowAt? prog 5) : ¬ TableCorrect coldFn prog := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hinh : rowAt? prog 6 = rowAt? prog 5` | the row at the cold block is inherited from the epilogue | tight: counterexample `genCFI_coldFn_rows_differ_and_tableCorrect`; witness class: a single concrete program, `genCFI coldFn (inferredAnn coldFn)` for `coldFn` in layout 0, 1, 2, whose rows at addresses 6 and 5 differ and which is `TableCorrect` |

**Depth:** shallow. Instantiates the layout-independent fact for layout 0, 1, 2.

**Non-vacuity witness:** The naive emitter's program (per-block deltas, nothing at block boundaries) satisfies hinh (naiveCFI_coldFn_rows_equal); naiveCFI_coldFn_not_tableCorrect instantiates the theorem. (`naiveCFI_coldFn_rows_equal`)

**Positive control:** `genCFI_coldFn_rows_differ_and_tableCorrect`. `genCFI coldFn (inferredAnn coldFn)` gives address 6 a row different from address 5 (it emits `restoreState` there) and is `TableCorrect`.

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.genCFI_coldFn_rows_differ_and_tableCorrect` (`lean/ToyCFI/ColdBlock.lean:148-152`):

```lean
-- lean/ToyCFI/ColdBlock.lean:148-152
/-- Tightness of the inherited-row hypothesis: in the generator's (correct)
program the rows at addresses 5 and 6 differ. -/
theorem genCFI_coldFn_rows_differ_and_tableCorrect :
    rowAt? (genCFI coldFn (inferredAnn coldFn)) 6 ≠ rowAt? (genCFI coldFn (inferredAnn coldFn)) 5 ∧
      TableCorrect coldFn (genCFI coldFn (inferredAnn coldFn)) := …
```

`Toy.CFI.naiveCFI_coldFn_rows_equal` (`lean/ToyCFI/ColdBlock.lean:166-169`):

```lean
-- lean/ToyCFI/ColdBlock.lean:166-169
/-- The naive program's rows at addresses 6 and 5 coincide (it emits nothing at
the cold block's address). -/
theorem naiveCFI_coldFn_rows_equal :
    rowAt? (naiveCFI coldFn (inferredAnn coldFn)) 6 = rowAt? (naiveCFI coldFn (inferredAnn coldFn)) 5 := …
```

</details>

**Prior art.**

- LLVM CFIFixup pass, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, llvm/lib/CodeGen/CFIFixup.cpp: header comment (lines 10-66) - after the prologue each block either 'has a call frame' or not; where the state at a block's start differs from the state at the end of its layout predecessor, the pass inserts either a target-specific reset to the initial state or '.cfi_restore_state' followed by '.cfi_remember_state', with a '.cfi_remember_state' after the last prologue CFI instruction; stated preconditions include 'CFI instructions are not contained in any loops'; stated limitations: an epilogue preceding the prologue in layout, and functions using SP as frame pointer with SP adjustments in different blocks. insertRememberRestorePair (line 195), fixupBlock (line 245). Derived (modeling bridge): the toy genCFI handles arbitrary rows rather than the pass's two states, but it remembers a row only at the start of the immediately preceding layout block and otherwise falls back to explicit re-definition, whereas the pass keeps one remember insertion point per section and chains remember/restore pairs across any number of intervening blocks (fixupBlock, lines 288-300; runImpl, lines 304-341) and, for the first block of a new section, clones the prologue's CFI instructions instead (lines 290-294). genCFI was not compared against the pass's output.
- LLVM CFIInstrInserter pass, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, llvm/lib/CodeGen/CFIInstrInserter.cpp: header comment (lines 9-17) - verifies that the outgoing CFA information of predecessors matches the incoming information of successors and inserts CFI instructions at block beginnings when 'a non-linear layout of blocks' leaves an incorrect rule. Besides the CFA offset and register it tracks callee-saved register save locations (CSRSavedLocation with kinds Register and CFAOffset, CSRLocMap, IncomingCSRSaved/OutgoingCSRSaved; lines 64-162; propagated along CFG edges, line 408), repairs them at block beginnings with .cfi_restore, .cfi_offset and .cfi_register (insertCFIInstrs, lines 415-511; a block that begins a new section gets a full def_cfa plus the callee-saved moves, lines 431-470), and reports CFG-edge CFA and callee-saved mismatches in verify (lines 545-571; CFA mismatches into blocks with no successors that are not return blocks are exempt, lines 553-557). It requires a single save location per callee-saved register ('Different saved locations for the same CSR', lines 366-369). In builds with assertions (#ifndef NDEBUG) it accepts cfi_remember_state/cfi_restore_state only as balanced depth-1 pairs inside one basic block and otherwise reports 'Support for cfi_remember_state not implemented!' (lines 316-339, 375-381); in builds without assertions its analysis ignores both instructions. Derived (modeling bridge): this is the explicit re-definition alternative; like the toy genCFI it repairs both the CFA rule and callee-saved register rules at layout boundaries, but it never places a remember/restore pair across blocks. It was not compared against the toy's output.

**Design question:** What must a CFI emitter guarantee for a linear layout of a CFG whose blocks are not placed in control-flow order, and which checks of the emitted table are sound?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM CFIFixup (llvm/llvm-project 701f926a): the toy genCFI handles arbitrary rows rather than the pass's two states, but it remembers a row only at the start of the immediately preceding layout block and otherwise falls back to explicit re-definition, whereas the pass keeps one remember insertion point per section and chains remember/restore pairs across any number of intervening blocks (fixupBlock, lines 288-300; runImpl, lines 304-341) and, for the first block of a new section, clones the prologue's CFI instructions instead (lines 290-294). genCFI was not compared against the pass's output.
- LLVM CFIInstrInserter (llvm/llvm-project 701f926a): this is the explicit re-definition alternative; like the toy genCFI it repairs both the CFA rule and callee-saved register rules at layout boundaries, but it never places a remember/restore pair across blocks. It was not compared against the toy's output.
- General: the row-equality hypothesis is the toy counterpart of 'no CFI instruction is placed at the cold block's address'.

### R3c: `naiveCFI_coldFn_cold_entry_cfa_is_true_cfa_minus_one`

- **Kind:** counterexample.  **Tier:** T0 (re-derivation of a known result).  **Depth:** definitional.
- **Plain claim:** The naive emitter's program for coldFn has the post-epilogue row initRow (CFA = sp + 0) at the cold block's address 6, and for every caller and every reachable state there it computes CFA - 1 instead of the CFA.
- **Key definitions:** `coldFn`, `naiveCFI`, `rowAt?`, `initRow`, `cfaOf`, `Reach`.

Lean statement (proof elided as `…`):

`Toy.CFI.naiveCFI_coldFn_cold_entry_cfa_is_true_cfa_minus_one` (`lean/ToyCFI/ColdBlock.lean:111-117`):

```lean
-- lean/ToyCFI/ColdBlock.lean:111-117
/-- **The naive (per-block, no boundary compensation) program computes a bogus
CFA in the cold block.** Its row at address 6 is the post-epilogue row
`initRow` (`CFA = sp + 0`, all registers `same`), and for every caller and every
reachable state at the cold block's first PC that row yields `CFA - 1`. -/
theorem naiveCFI_coldFn_cold_entry_cfa_is_true_cfa_minus_one :
    rowAt? (naiveCFI coldFn (inferredAnn coldFn)) 6 = some initRow ∧
      ∀ c m st, Reach coldFn c m 2 0 st → cfaOf initRow st = c.cfa - 1 := …
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete objects.

**Depth:** definitional. A concrete evaluation of `naiveCFI coldFn` and of the reachable states at address 6.

**Non-vacuity witness:** coldFn_reach_cold: the cold block's first PC is reachable for every caller. (`coldFn_reach_cold`)

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.coldFn_reach_cold` (`lean/ToyCFI/ColdBlock.lean:31-32`):

```lean
-- lean/ToyCFI/ColdBlock.lean:31-32
theorem coldFn_reach_cold (c : Caller) (m : Int → Int) :
    Reach coldFn c m 2 0 (coldStCold c m) := …
```

</details>

**Prior art.**

- LLVM CFIFixup pass, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, llvm/lib/CodeGen/CFIFixup.cpp: header comment (lines 10-66) - after the prologue each block either 'has a call frame' or not; where the state at a block's start differs from the state at the end of its layout predecessor, the pass inserts either a target-specific reset to the initial state or '.cfi_restore_state' followed by '.cfi_remember_state', with a '.cfi_remember_state' after the last prologue CFI instruction; stated preconditions include 'CFI instructions are not contained in any loops'; stated limitations: an epilogue preceding the prologue in layout, and functions using SP as frame pointer with SP adjustments in different blocks. insertRememberRestorePair (line 195), fixupBlock (line 245). Derived (modeling bridge): the toy genCFI handles arbitrary rows rather than the pass's two states, but it remembers a row only at the start of the immediately preceding layout block and otherwise falls back to explicit re-definition, whereas the pass keeps one remember insertion point per section and chains remember/restore pairs across any number of intervening blocks (fixupBlock, lines 288-300; runImpl, lines 304-341) and, for the first block of a new section, clones the prologue's CFI instructions instead (lines 290-294). genCFI was not compared against the pass's output.
- T. Bastian, S. Kell, F. Zappa Nardelli, 'Reliable and fast DWARF-based stack unwinding', Proc. ACM Program. Lang. 3(OOPSLA), Article 146, October 2019, doi:10.1145/3360572. §2.2 (pp. 146:8-146:12; the passages summarized here are on pp. 146:9-146:11): unwind rows are synthesized by forward propagation along CFG edges, relying on stack offsets being invariant at merge points; with variable-size stack allocation compilers fall back to a base-pointer register; if different rows reach a merge point the tool aborts (a lossy merge is enabled only for terminal blocks). Appendix A (pp. 146:21-146:23): remember_state pushes 'the state of all the registers of this row', and restore(reg) is not supported (p. 146:21); the formal interpretation keeps a state-saving stack of rows (Row*, p. 146:22; Table 5, p. 146:23). The paper contains no mechanized proof.

**Design question:** What must a CFI emitter guarantee for a linear layout of a CFG whose blocks are not placed in control-flow order, and which checks of the emitted table are sound?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM CFIFixup (llvm/llvm-project 701f926a): the toy genCFI handles arbitrary rows rather than the pass's two states, but it remembers a row only at the start of the immediately preceding layout block and otherwise falls back to explicit re-definition, whereas the pass keeps one remember insertion point per section and chains remember/restore pairs across any number of intervening blocks (fixupBlock, lines 288-300; runImpl, lines 304-341) and, for the first block of a new section, clones the prologue's CFI instructions instead (lines 290-294). genCFI was not compared against the pass's output.
- General: the size of the error (one address unit) reflects the toy prologue's single push; real errors depend on the real prologue.

### R4: `probeLoop_cfa_correct_at_every_iteration_iff_fp_anchor`

- **Kind:** characterization.  **Tier:** T1 (folklore made precise).  **Depth:** shallow.
- **Plain claim:** For the probing loop probeFn page (push fp; movReg fp sp; loop subSp page) with page > 0, a row computes the correct CFA at every reachable state of the loop PC - every iteration, every caller, every memory - if and only if its CFA rule is fp + 1, i.e. relative to the anchor register rather than to the varying sp.
- **Key definitions:** `probeFn`, `Reach`, `cfaOf`, `Row` (the iff concerns `cfaOf R st = c.cfa` at every reachable state of the loop PC; register rules are left free).

Lean statement (proof elided as `…`):

`Toy.CFI.probeLoop_cfa_correct_at_every_iteration_iff_fp_anchor` (`lean/ToyCFI/ProbeLoop.lean:77-83`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:77-83
/-- **Characterization.** For `page > 0`, a row computes the correct CFA at every
reachable state of the loop PC (every iteration, every caller, every memory)
if and only if its CFA rule is the anchor rule `fp + 1`. -/
theorem probeLoop_cfa_correct_at_every_iteration_iff_fp_anchor (page : Nat) (hpage : 0 < page)
    (R : Row) :
    (∀ c m st, Reach (probeFn page) c m 1 0 st → cfaOf R st = c.cfa) ↔
      (R.cfaReg = .fp ∧ R.cfaOff = 1) := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hpage : 0 < page` | sp must actually vary between iterations | tight: counterexample `probeLoop_characterization_fails_for_page_zero`; witness class: degenerate boundary instance `page = 0`: the loop body `subSp 0` leaves `sp` unchanged, and a row whose CFA rule is not `fp + 1` is correct at every reachable loop state |

**Depth:** shallow. Case analysis of the CFA base register against the reachable loop states after 0 and 1 iterations for two callers; the converse uses the loop invariant that `fp` stays at CFA - 1.

**Non-vacuity witness:** For page = 4096 the anchor rule fp + 1 satisfies the left side and sp + 1 does not (both sides of the iff are exercised); every iteration's state is reachable (probeLoopState_reach) and the anchor-relative table is correct for every page (probeAnchorCFI_tableCorrect). (`probeLoop_characterization_nonvacuity`)

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.probeLoop_characterization_fails_for_page_zero` (`lean/ToyCFI/ProbeLoop.lean:144-148`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:144-148
/-- Tightness of `0 < page`: with `page = 0` the SP-relative rule `sp + 1` is
correct at every reachable loop state, so the characterization fails. -/
theorem probeLoop_characterization_fails_for_page_zero :
    ∃ R : Row, (∀ c m st, Reach (probeFn 0) c m 1 0 st → cfaOf R st = c.cfa) ∧
      ¬ (R.cfaReg = .fp ∧ R.cfaOff = 1) := …
```

`Toy.CFI.probeLoop_characterization_nonvacuity` (`lean/ToyCFI/ProbeLoop.lean:158-162`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:158-162
/-- Non-vacuity of the characterization: for `page = 4096` the anchor rule
satisfies the left side and the SP-relative rule `sp + 1` does not. -/
theorem probeLoop_characterization_nonvacuity (rules : RegFile RegRule) :
    0 < 4096 ∧ (∀ c m st, Reach (probeFn 4096) c m 1 0 st → cfaOf ⟨.fp, 1, rules⟩ st = c.cfa) ∧
      ¬ (∀ c m st, Reach (probeFn 4096) c m 1 0 st → cfaOf ⟨.sp, 1, rules⟩ st = c.cfa) := …
```

</details>

**Prior art.**

- DWARF Debugging Information Format Committee, DWARF Debugging Information Format, Version 5 (February 13, 2017), https://dwarfstd.org/doc/DWARF5.pdf. §2.5.1.2 DW_OP_fbreg (an offset from the address given by DW_AT_frame_base); §2.5.1.3 item 15 (printed page 33; PDF page 51) DW_OP_call_frame_cfa (pushes the CFA obtained from the call frame information; computing DW_AT_frame_base from registers would 'in some cases ... require an extensive location list because the values of the registers used in computing the CFA change during a subroutine'). §6.4.2.4 (printed page 181; PDF page 199) DW_CFA_remember_state / DW_CFA_restore_state ('push the set of rules for every register onto an implicit stack' / 'pop the set of rules off the implicit stack and place them in the current row') in the wording quoted by DWARF issue 230103.1. The toy's register rules and CFA-definition instructions are modeled on the pinned LLVM libunwind implementation (libunwind/src/DwarfParser.hpp and DwarfInstructions.hpp at llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc) rather than on the text of §6.4.1 and §6.4.2.2.
- T. Bastian, S. Kell, F. Zappa Nardelli, 'Reliable and fast DWARF-based stack unwinding', Proc. ACM Program. Lang. 3(OOPSLA), Article 146, October 2019, doi:10.1145/3360572. §2.2 (pp. 146:8-146:12; the passages summarized here are on pp. 146:9-146:11): unwind rows are synthesized by forward propagation along CFG edges, relying on stack offsets being invariant at merge points; with variable-size stack allocation compilers fall back to a base-pointer register; if different rows reach a merge point the tool aborts (a lossy merge is enabled only for terminal blocks). Appendix A (pp. 146:21-146:23): remember_state pushes 'the state of all the registers of this row', and restore(reg) is not supported (p. 146:21); the formal interpretation keeps a state-saving stack of rows (Row*, p. 146:22; Table 5, p. 146:23). The paper contains no mechanized proof.
- LLVM CFIFixup pass, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, llvm/lib/CodeGen/CFIFixup.cpp: header comment (lines 10-66) - after the prologue each block either 'has a call frame' or not; where the state at a block's start differs from the state at the end of its layout predecessor, the pass inserts either a target-specific reset to the initial state or '.cfi_restore_state' followed by '.cfi_remember_state', with a '.cfi_remember_state' after the last prologue CFI instruction; stated preconditions include 'CFI instructions are not contained in any loops'; stated limitations: an epilogue preceding the prologue in layout, and functions using SP as frame pointer with SP adjustments in different blocks. insertRememberRestorePair (line 195), fixupBlock (line 245). Derived (modeling bridge): the toy genCFI handles arbitrary rows rather than the pass's two states, but it remembers a row only at the start of the immediately preceding layout block and otherwise falls back to explicit re-definition, whereas the pass keeps one remember insertion point per section and chains remember/restore pairs across any number of intervening blocks (fixupBlock, lines 288-300; runImpl, lines 304-341) and, for the first block of a new section, clones the prologue's CFI instructions instead (lines 290-294). genCFI was not compared against the pass's output.
- LLVM libunwind, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc. libunwind/src/DwarfParser.hpp: struct PrologInfo (lines 95-100: cfaRegister, cfaRegisterOffset, savedRegisters); parseFDEInstructions loop 'while ((p < instructionsEnd) && (codeOffset < pcoffset))' (line 503); DW_CFA_remember_state pushes a copy of the whole PrologInfo ('entry->info = *results', lines 606-621); DW_CFA_restore_state pops it ('*results = top->info') and returns false on an empty stack (lines 622-632); DW_CFA_def_cfa_register sets only cfaRegister and DW_CFA_def_cfa_offset only cfaRegisterOffset (lines 646-661). libunwind/src/DwarfInstructions.hpp: getCFA returns register value + cfaRegisterOffset (lines 66-76); kRegisterInCFA reads memory at cfa + value (lines 107-108); the caller's SP is set to the CFA (line 284). Derived (modeling bridge): the toy rowAt? applies every instruction located at an address <= pc, whereas this loop stops before instructions located exactly at pcoffset; how that interacts with the caller-side PC adjustment was not examined.
- J. Oakley, S. Bratus, 'Exploiting the hard-working DWARF: Trojan and exploit techniques with no native executable code', USENIX WOOT 2011, https://www.usenix.org/conference/woot11/exploiting-hard-working-dwarf-trojan-and-exploit-techniques-no-native-executable: DWARF call-frame/expression bytecode interpreted by the unwinder is Turing-complete. Derived (modeling bridge): expression-based CFA rules (DW_CFA_def_cfa_expression, not modeled) are far more expressive than the toy's register+offset rule, so the impossibility results stated for register+offset rules are not claimed for them (whether they fail for such rules is not proved here).

**Design question:** When the stack pointer varies at run time (probing loops, dynamic allocation), which CFA rule keeps the table correct?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM CFIFixup (llvm/llvm-project 701f926a): the toy genCFI handles arbitrary rows rather than the pass's two states, but it remembers a row only at the start of the immediately preceding layout block and otherwise falls back to explicit re-definition, whereas the pass keeps one remember insertion point per section and chains remember/restore pairs across any number of intervening blocks (fixupBlock, lines 288-300; runImpl, lines 304-341) and, for the first block of a new section, clones the prologue's CFI instructions instead (lines 290-294). genCFI was not compared against the pass's output.
- LLVM libunwind (llvm/llvm-project 701f926a): the toy rowAt? applies every instruction located at an address <= pc, whereas this loop stops before instructions located exactly at pcoffset; how that interacts with the caller-side PC adjustment was not examined.
- Oakley and Bratus (2011): expression-based CFA rules (DW_CFA_def_cfa_expression, not modeled) are far more expressive than the toy's register+offset rule, so the impossibility results stated for register+offset rules are not claimed for them (whether they fail for such rules is not proved here).

### R4b: `spRelative_cfa_right_on_entry_wrong_after_first_iteration_of_pos_page`

- **Kind:** counterexample.  **Tier:** T1 (folklore made precise).  **Depth:** shallow.
- **Plain claim:** For page > 0, for every caller, memory and choice of register rules, the SP-relative row CFA = sp + 1 computes the true CFA at the loop PC of probeFn page on loop entry, computes CFA - page (which differs from the CFA) after the first iteration, and the SP-relative table probeSpCFI is not TableCorrect for probeFn page.
- **Key definitions:** `probeFn`, `probeSpCFI`, `cfaOf`, `TableCorrect`.

Lean statement (proof elided as `…`):

`Toy.CFI.spRelative_cfa_right_on_entry_wrong_after_first_iteration_of_pos_page` (`lean/ToyCFI/ProbeLoop.lean:121-131`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:121-131
/-- **SP-relative CFA with a fixed offset is right on loop entry and wrong after
the first iteration, for `page > 0`.** For every caller, memory and register
rules, the row `CFA = sp + 1` computes the true CFA at the loop PC on entry and
`CFA - page ≠ CFA` after one iteration; consequently the SP-relative table
`probeSpCFI` is not correct for `probeFn page`. -/
theorem spRelative_cfa_right_on_entry_wrong_after_first_iteration_of_pos_page (page : Nat)
    (hpage : 0 < page) (c : Caller) (m : Int → Int) (rules : RegFile RegRule) :
    cfaOf ⟨.sp, 1, rules⟩ (probeLoopState page c m 0) = c.cfa ∧
      cfaOf ⟨.sp, 1, rules⟩ (probeLoopState page c m 1) = c.cfa - page ∧
      cfaOf ⟨.sp, 1, rules⟩ (probeLoopState page c m 1) ≠ c.cfa ∧
      ¬ TableCorrect (probeFn page) probeSpCFI := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hpage : 0 < page` | the loop moves sp; with page = 0 the SP-relative row is right at every iteration | tight: counterexample `spRelative_wrong_after_first_iteration_fails_for_page_zero`; witness class: degenerate boundary instance `page = 0` (the loop body `subSp 0` leaves `sp` unchanged), for every caller, memory and register rules |

**Depth:** shallow. Evaluation of the SP-relative rule on the loop states after 0 and 1 iterations.

**Non-vacuity witness:** page = 4096 satisfies the hypothesis (and probeSpCFI is incorrect there). (`spRelative_wrong_after_first_iteration_nonvacuity`)

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.spRelative_wrong_after_first_iteration_fails_for_page_zero` (`lean/ToyCFI/ProbeLoop.lean:168-176`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:168-176
/-- Tightness of `0 < page` for the SP-relative statement: with `page = 0` the
row `CFA = sp + 1` is right after the first iteration too, so the conclusion
fails for every caller, memory and register rules. -/
theorem spRelative_wrong_after_first_iteration_fails_for_page_zero :
    ¬ (0 < 0) ∧ ∀ (c : Caller) (m : Int → Int) (rules : RegFile RegRule),
      ¬ (cfaOf ⟨.sp, 1, rules⟩ (probeLoopState 0 c m 0) = c.cfa ∧
        cfaOf ⟨.sp, 1, rules⟩ (probeLoopState 0 c m 1) = c.cfa - (0 : Nat) ∧
        cfaOf ⟨.sp, 1, rules⟩ (probeLoopState 0 c m 1) ≠ c.cfa ∧
        ¬ TableCorrect (probeFn 0) probeSpCFI) := …
```

`Toy.CFI.spRelative_wrong_after_first_iteration_nonvacuity` (`lean/ToyCFI/ProbeLoop.lean:181-184`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:181-184
/-- Non-vacuity of the SP-relative statement: its hypothesis holds for
`page = 4096`. -/
theorem spRelative_wrong_after_first_iteration_nonvacuity :
    0 < 4096 ∧ ¬ TableCorrect (probeFn 4096) probeSpCFI := …
```

</details>

**Prior art.**

- T. Bastian, S. Kell, F. Zappa Nardelli, 'Reliable and fast DWARF-based stack unwinding', Proc. ACM Program. Lang. 3(OOPSLA), Article 146, October 2019, doi:10.1145/3360572. §2.2 (pp. 146:8-146:12; the passages summarized here are on pp. 146:9-146:11): unwind rows are synthesized by forward propagation along CFG edges, relying on stack offsets being invariant at merge points; with variable-size stack allocation compilers fall back to a base-pointer register; if different rows reach a merge point the tool aborts (a lossy merge is enabled only for terminal blocks). Appendix A (pp. 146:21-146:23): remember_state pushes 'the state of all the registers of this row', and restore(reg) is not supported (p. 146:21); the formal interpretation keeps a state-saving stack of rows (Row*, p. 146:22; Table 5, p. 146:23). The paper contains no mechanized proof.

**Design question:** When the stack pointer varies at run time (probing loops, dynamic allocation), which CFA rule keeps the table correct?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- General: in the toy, for `page > 0` no row whose CFA rule is not `fp + 1` (in particular no SP-relative rule) computes the CFA at every iteration of the loop PC (`probeLoop_cfa_correct_at_every_iteration_iff_fp_anchor`), and the rule `sp + 1` is right on entry and wrong after the first iteration (this theorem); for real stack-probing loops that share one PC across iterations the analogous statement is derived, not proved here. This is why the toy anchors the CFA in `fp`.

### R5a: `lookupFirst_eq_result_of_uniqueAt`

- **Kind:** theorem.  **Tier:** T0 (re-derivation of a known result).  **Depth:** shallow.
- **Plain claim:** If at most one distinct entry value of a call-site table contains pc (duplicate identical entries are permitted) (half-open [start, stop)), then for the entry e containing pc, first-match lookup returns e's outcome: its landing pad, or 'no landing pad'.
- **Key definitions:** `CallSite`, `CallSite.contains` (half-open), `CallSite.result`, `LookupResult`, `lookupFirst`, `UniqueAt`.

Lean statement (proof elided as `…`):

`Toy.CFI.lookupFirst_eq_result_of_uniqueAt` (`lean/ToyCFI/LSDA.lean:77-82`):

```lean
-- lean/ToyCFI/LSDA.lean:77-82
/-- **First-match lookup returns the unique matching entry's outcome.** If at
most one distinct entry value contains `pc` and `e` is an entry containing
`pc`, then
`lookupFirst` returns `e`'s outcome (its landing pad, or "no landing pad"). -/
theorem lookupFirst_eq_result_of_uniqueAt {t : LSDA} {pc : Nat} {e : CallSite}
    (hu : UniqueAt t pc) (he : e ∈ t) (hc : e.contains pc) : lookupFirst t pc = e.result := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hu : UniqueAt t pc` | no entry with a different value also contains pc | tight: counterexample `lookupFirst_wrong_without_uniqueAt`; witness class: a concrete 2-entry table with overlapping ranges, `lsdaOverlap` = [0,10) ↦ 1, [5,15) ↦ 2, at `pc = 7` with `e` = [5,15) ↦ 2 |
| `he : e ∈ t` | e is an entry of the table (without it, e may be any range containing pc) | tight: counterexample `lookup_eq_result_fails_without_mem`; witness class: degenerate boundary instance: the empty table `[]` (sorted and unique vacuously) at `pc = 0`, with `e` = [0,4) ↦ 1, which contains 0 but is not an entry |
| `hc : e.contains pc` | e contains pc (without it, e may be an entry that does not cover pc) | tight: counterexample `lookup_eq_result_fails_without_contains`; witness class: a concrete 1-entry table [[0,4) ↦ 1] at `pc = 8`, which its only entry does not contain |

**Depth:** shallow. Induction over the table.

**Non-vacuity witness:** lsdaAdjacent ([0,4) -> 1, [4,8) -> 2) at pc 4 with e = [4,8): unique, lookup returns 2. (`lookupFirst_nonvacuity`)

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.lookupFirst_wrong_without_uniqueAt` (`lean/ToyCFI/LSDA.lean:171-176`):

```lean
-- lean/ToyCFI/LSDA.lean:171-176
/-- Tightness of uniqueness for `lookupFirst`: with overlapping ranges, an entry
containing `pc = 7` exists whose landing pad is not the one returned. -/
theorem lookupFirst_wrong_without_uniqueAt :
    (⟨5, 15, some 2⟩ : CallSite) ∈ lsdaOverlap ∧ (⟨5, 15, some 2⟩ : CallSite).contains 7 ∧
      ¬ UniqueAt lsdaOverlap 7 ∧
      lookupFirst lsdaOverlap 7 ≠ (⟨5, 15, some 2⟩ : CallSite).result := …
```

`Toy.CFI.lookup_eq_result_fails_without_mem` (`lean/ToyCFI/LSDA.lean:258-264`):

```lean
-- lean/ToyCFI/LSDA.lean:258-264
/-- Tightness of membership for `lookupFirst_eq_result_of_uniqueAt` and
`lookupScan_eq_result_of_sorted_uniqueAt`: an entry containing `pc` that is not
in the (empty, sorted, unique) table; both lookups differ from its outcome. -/
theorem lookup_eq_result_fails_without_mem :
    let e : CallSite := ⟨0, 4, some 1⟩
    SortedByStart [] ∧ UniqueAt [] 0 ∧ e ∉ ([] : LSDA) ∧ e.contains 0 ∧
      lookupFirst [] 0 ≠ e.result ∧ lookupScan [] 0 ≠ e.result := …
```

`Toy.CFI.lookup_eq_result_fails_without_contains` (`lean/ToyCFI/LSDA.lean:269-275`):

```lean
-- lean/ToyCFI/LSDA.lean:269-275
/-- Tightness of containment for the same two results: an entry of a sorted,
unique table that does not contain `pc = 8`; both lookups differ from its
outcome. -/
theorem lookup_eq_result_fails_without_contains :
    let e : CallSite := ⟨0, 4, some 1⟩
    SortedByStart [e] ∧ UniqueAt [e] 8 ∧ e ∈ [e] ∧ ¬ e.contains 8 ∧
      lookupFirst [e] 8 ≠ e.result ∧ lookupScan [e] 8 ≠ e.result := …
```

`Toy.CFI.lookupFirst_nonvacuity` (`lean/ToyCFI/LSDA.lean:280-283`):

```lean
-- lean/ToyCFI/LSDA.lean:280-283
/-- Non-vacuity for first-match lookup: a unique containing entry. -/
theorem lookupFirst_nonvacuity :
    UniqueAt lsdaAdjacent 4 ∧ (⟨4, 8, some 2⟩ : CallSite) ∈ lsdaAdjacent ∧
      (⟨4, 8, some 2⟩ : CallSite).contains 4 ∧ lookupFirst lsdaAdjacent 4 = .landingPad 2 := …
```

</details>

**Prior art.**

- LLVM libc++abi, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, libcxxabi/src/cxa_personality.cpp, scan_eh_tab: no LSDA gives _URC_CONTINUE_UNWIND (lines 684-688); 'uintptr_t ip = _Unwind_GetIP(context) - 1' (line 698); comments 'The call sites are non-overlapping in [start, start+length)' and 'The call sites are ordered in increasing value of start' (lines 747-748); match condition 'start <= ipOffset && ipOffset < start + length' (line 753); landingPad == 0 gives _URC_CONTINUE_UNWIND (lines 763-768); 'else if (ipOffset < start)' calls call_terminate (lines 899-905); falling off the end of the table calls call_terminate (lines 910-911). Derived (modeling bridge): lookupScan mirrors this scan with unit-size toy addresses and frameAction mirrors the three outcomes.
- Itanium C++ ABI: Exception Handling ($Revision: 1.22 $), https://itanium-cxx-abi.github.io/cxx-abi/abi-eh.html: two-phase unwinding (the search phase calls the personality routine frame by frame and, if it reports failure, terminate() is called instead of phase 2; the cleanup phase restores the register state at the handler frame); the personality routine is language- and vendor-specific; _Unwind_GetLanguageSpecificData returns the frame's LSDA. The call-site table layout is not specified in that document.
- G. Klein, T. Nipkow, 'A machine-checked model for a Java-like language, virtual machine, and compiler', ACM TOPLAS 28(4):619-695, 2006, doi:10.1145/1146809.1146811; Isabelle AFP entry Jinja (https://www.isa-afp.org/entries/Jinja.html), theory JVM/JVMExceptions.thy: matches_ex_entry tests the half-open range 's <= pc < e' plus a class check, match_ex_table returns the first matching entry's handler (None if no entry matches), and find_handler pops frames until some frame's exception table matches. Derived (modeling bridge): the same first-match half-open lookup and frame-by-frame handler search, mechanized; Jinja has no register restoration from unwind rows, no 'entry without landing pad' outcome and no terminate-on-uncovered-PC outcome.

**Design question:** Which properties of a call-site table make the personality routine's lookup return the intended landing pad, and which off-by-one conventions break it?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM libc++abi (llvm/llvm-project 701f926a): lookupScan mirrors this scan with unit-size toy addresses and frameAction mirrors the three outcomes.
- Klein and Nipkow (2006) / AFP Jinja: the same first-match half-open lookup and frame-by-frame handler search, mechanized; Jinja has no register restoration from unwind rows, no 'entry without landing pad' outcome and no terminate-on-uncovered-PC outcome.

### R5b: `lookupFirst_eq_notFound_iff`

- **Kind:** characterization.  **Tier:** T0 (re-derivation of a known result).  **Depth:** shallow.
- **Plain claim:** For every call-site table, first-match lookup reports 'not found' exactly when no entry contains pc; no ordering or disjointness hypothesis is needed.
- **Key definitions:** `lookupFirst`, `CallSite.contains`, `LookupResult.notFound`.

Lean statement (proof elided as `…`):

`Toy.CFI.lookupFirst_eq_notFound_iff` (`lean/ToyCFI/LSDA.lean:94-97`):

```lean
-- lean/ToyCFI/LSDA.lean:94-97
/-- **First-match lookup reports "not found" exactly when no entry contains `pc`.**
No hypothesis on the table is needed. -/
theorem lookupFirst_eq_notFound_iff (t : LSDA) (pc : Nat) :
    lookupFirst t pc = .notFound ↔ ∀ e ∈ t, ¬ e.contains pc := …
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete objects.

**Depth:** shallow. Induction over the table; uses no interval structure.

**Non-vacuity witness:** lookupIncl_wrong_on_adjacent_ranges includes lookupFirst lsdaAdjacent 8 = notFound. (`lookupIncl_wrong_on_adjacent_ranges`)

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.lookupIncl_wrong_on_adjacent_ranges` (`lean/ToyCFI/LSDA.lean:219-225`):

```lean
-- lean/ToyCFI/LSDA.lean:219-225
/-- Off-by-one (inclusive end): on a sorted, non-overlapping table with adjacent
ranges, treating `stop` as inclusive returns the landing pad of the range
ending at `4` for a call at `4`, and reports a landing pad for a call at `8`
that no range contains. -/
theorem lookupIncl_wrong_on_adjacent_ranges :
    lookupIncl lsdaAdjacent 4 = .landingPad 1 ∧ lookupFirst lsdaAdjacent 4 = .landingPad 2 ∧
      lookupIncl lsdaAdjacent 8 = .landingPad 2 ∧ lookupFirst lsdaAdjacent 8 = .notFound := …
```

</details>

**Prior art.**

- LLVM libc++abi, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, libcxxabi/src/cxa_personality.cpp, scan_eh_tab: no LSDA gives _URC_CONTINUE_UNWIND (lines 684-688); 'uintptr_t ip = _Unwind_GetIP(context) - 1' (line 698); comments 'The call sites are non-overlapping in [start, start+length)' and 'The call sites are ordered in increasing value of start' (lines 747-748); match condition 'start <= ipOffset && ipOffset < start + length' (line 753); landingPad == 0 gives _URC_CONTINUE_UNWIND (lines 763-768); 'else if (ipOffset < start)' calls call_terminate (lines 899-905); falling off the end of the table calls call_terminate (lines 910-911). Derived (modeling bridge): lookupScan mirrors this scan with unit-size toy addresses and frameAction mirrors the three outcomes.
- G. Klein, T. Nipkow, 'A machine-checked model for a Java-like language, virtual machine, and compiler', ACM TOPLAS 28(4):619-695, 2006, doi:10.1145/1146809.1146811; Isabelle AFP entry Jinja (https://www.isa-afp.org/entries/Jinja.html), theory JVM/JVMExceptions.thy: matches_ex_entry tests the half-open range 's <= pc < e' plus a class check, match_ex_table returns the first matching entry's handler (None if no entry matches), and find_handler pops frames until some frame's exception table matches. Derived (modeling bridge): the same first-match half-open lookup and frame-by-frame handler search, mechanized; Jinja has no register restoration from unwind rows, no 'entry without landing pad' outcome and no terminate-on-uncovered-PC outcome.

**Design question:** Which properties of a call-site table make the personality routine's lookup return the intended landing pad, and which off-by-one conventions break it?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM libc++abi (llvm/llvm-project 701f926a): lookupScan mirrors this scan with unit-size toy addresses and frameAction mirrors the three outcomes.
- Klein and Nipkow (2006) / AFP Jinja: the same first-match half-open lookup and frame-by-frame handler search, mechanized; Jinja has no register restoration from unwind rows, no 'entry without landing pad' outcome and no terminate-on-uncovered-PC outcome.
- General: in the C++ personality cited under prior art, 'not found' leads to terminate and 'entry without landing pad' to continued unwinding; the toy `frameAction` mirrors this split.

### R5c: `lookupScan_eq_result_of_sorted_uniqueAt`

- **Kind:** theorem.  **Tier:** T0 (re-derivation of a known result).  **Depth:** shallow.
- **Plain claim:** For a call-site table sorted by start address in which at most one distinct entry value contains pc (duplicate identical entries are permitted), the early-exit scan (stop with 'not found' at the first entry starting after pc) returns the outcome of the entry e containing pc.
- **Key definitions:** `lookupScan`, `SortedByStart`, `UniqueAt`, `CallSite.contains`, `CallSite.result`.

Lean statement (proof elided as `…`):

`Toy.CFI.lookupScan_eq_result_of_sorted_uniqueAt` (`lean/ToyCFI/LSDA.lean:109-115`):

```lean
-- lean/ToyCFI/LSDA.lean:109-115
/-- **Sorted early-exit scan returns the unique matching entry's outcome.** For a
table sorted by start address in which at most one distinct entry value
contains `pc`, the
early-exit scan returns the outcome of the entry containing `pc`. -/
theorem lookupScan_eq_result_of_sorted_uniqueAt {t : LSDA} {pc : Nat} {e : CallSite}
    (hs : SortedByStart t) (hu : UniqueAt t pc) (he : e ∈ t) (hc : e.contains pc) :
    lookupScan t pc = e.result := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hs : SortedByStart t` | the early exit must not skip the containing entry | tight: counterexample `lookupScan_wrong_without_sorted`; witness class: a concrete 2-entry unsorted table, `lsdaUnsorted` = [10,20) ↦ 1, [0,5) ↦ 2, at `pc = 3` with `e` = [0,5) ↦ 2 |
| `hu : UniqueAt t pc` | no entry with a different value also contains pc | tight: counterexample `lookupScan_wrong_without_uniqueAt`; witness class: the concrete sorted 2-entry table with overlapping ranges `lsdaOverlap` = [0,10) ↦ 1, [5,15) ↦ 2, at `pc = 7` with `e` = [5,15) ↦ 2 |
| `he : e ∈ t` | e is an entry of the table (without it, e may be any range containing pc) | tight: counterexample `lookup_eq_result_fails_without_mem`; witness class: degenerate boundary instance: the empty table `[]` (sorted and unique vacuously) at `pc = 0`, with `e` = [0,4) ↦ 1, which contains 0 but is not an entry |
| `hc : e.contains pc` | e contains pc (without it, e may be an entry that does not cover pc) | tight: counterexample `lookup_eq_result_fails_without_contains`; witness class: a concrete 1-entry table [[0,4) ↦ 1] at `pc = 8`, which its only entry does not contain |

**Depth:** shallow. Induction over the table using sortedness for the early exit.

**Non-vacuity witness:** lsdaAdjacent is sorted, unique at pc 4, and [4,8) contains 4; the scan returns 2. (`lookupScan_nonvacuity`)

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.lookupScan_wrong_without_sorted` (`lean/ToyCFI/LSDA.lean:198-203`):

```lean
-- lean/ToyCFI/LSDA.lean:198-203
/-- Tightness of sortedness for the early-exit scan: unique entry containing
`pc = 3`, but the scan stops at the first entry and reports "not found". -/
theorem lookupScan_wrong_without_sorted :
    ¬ SortedByStart lsdaUnsorted ∧ UniqueAt lsdaUnsorted 3 ∧
      (⟨0, 5, some 2⟩ : CallSite) ∈ lsdaUnsorted ∧ (⟨0, 5, some 2⟩ : CallSite).contains 3 ∧
      lookupScan lsdaUnsorted 3 = .notFound := …
```

`Toy.CFI.lookupScan_wrong_without_uniqueAt` (`lean/ToyCFI/LSDA.lean:187-191`):

```lean
-- lean/ToyCFI/LSDA.lean:187-191
/-- Tightness of uniqueness for `lookupScan` (the overlapping table is sorted). -/
theorem lookupScan_wrong_without_uniqueAt :
    SortedByStart lsdaOverlap ∧ (⟨5, 15, some 2⟩ : CallSite) ∈ lsdaOverlap ∧
      (⟨5, 15, some 2⟩ : CallSite).contains 7 ∧ ¬ UniqueAt lsdaOverlap 7 ∧
      lookupScan lsdaOverlap 7 ≠ (⟨5, 15, some 2⟩ : CallSite).result := …
```

`Toy.CFI.lookup_eq_result_fails_without_mem` (`lean/ToyCFI/LSDA.lean:258-264`):

```lean
-- lean/ToyCFI/LSDA.lean:258-264
/-- Tightness of membership for `lookupFirst_eq_result_of_uniqueAt` and
`lookupScan_eq_result_of_sorted_uniqueAt`: an entry containing `pc` that is not
in the (empty, sorted, unique) table; both lookups differ from its outcome. -/
theorem lookup_eq_result_fails_without_mem :
    let e : CallSite := ⟨0, 4, some 1⟩
    SortedByStart [] ∧ UniqueAt [] 0 ∧ e ∉ ([] : LSDA) ∧ e.contains 0 ∧
      lookupFirst [] 0 ≠ e.result ∧ lookupScan [] 0 ≠ e.result := …
```

`Toy.CFI.lookup_eq_result_fails_without_contains` (`lean/ToyCFI/LSDA.lean:269-275`):

```lean
-- lean/ToyCFI/LSDA.lean:269-275
/-- Tightness of containment for the same two results: an entry of a sorted,
unique table that does not contain `pc = 8`; both lookups differ from its
outcome. -/
theorem lookup_eq_result_fails_without_contains :
    let e : CallSite := ⟨0, 4, some 1⟩
    SortedByStart [e] ∧ UniqueAt [e] 8 ∧ e ∈ [e] ∧ ¬ e.contains 8 ∧
      lookupFirst [e] 8 ≠ e.result ∧ lookupScan [e] 8 ≠ e.result := …
```

`Toy.CFI.lookupScan_nonvacuity` (`lean/ToyCFI/LSDA.lean:286-289`):

```lean
-- lean/ToyCFI/LSDA.lean:286-289
/-- Non-vacuity for the sorted early-exit scan. -/
theorem lookupScan_nonvacuity :
    SortedByStart lsdaAdjacent ∧ UniqueAt lsdaAdjacent 4 ∧ (⟨4, 8, some 2⟩ : CallSite) ∈ lsdaAdjacent ∧
      (⟨4, 8, some 2⟩ : CallSite).contains 4 ∧ lookupScan lsdaAdjacent 4 = .landingPad 2 := …
```

</details>

**Prior art.**

- LLVM libc++abi, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, libcxxabi/src/cxa_personality.cpp, scan_eh_tab: no LSDA gives _URC_CONTINUE_UNWIND (lines 684-688); 'uintptr_t ip = _Unwind_GetIP(context) - 1' (line 698); comments 'The call sites are non-overlapping in [start, start+length)' and 'The call sites are ordered in increasing value of start' (lines 747-748); match condition 'start <= ipOffset && ipOffset < start + length' (line 753); landingPad == 0 gives _URC_CONTINUE_UNWIND (lines 763-768); 'else if (ipOffset < start)' calls call_terminate (lines 899-905); falling off the end of the table calls call_terminate (lines 910-911). Derived (modeling bridge): lookupScan mirrors this scan with unit-size toy addresses and frameAction mirrors the three outcomes.
- Itanium C++ ABI: Exception Handling ($Revision: 1.22 $), https://itanium-cxx-abi.github.io/cxx-abi/abi-eh.html: two-phase unwinding (the search phase calls the personality routine frame by frame and, if it reports failure, terminate() is called instead of phase 2; the cleanup phase restores the register state at the handler frame); the personality routine is language- and vendor-specific; _Unwind_GetLanguageSpecificData returns the frame's LSDA. The call-site table layout is not specified in that document.
- G. Klein, T. Nipkow, 'A machine-checked model for a Java-like language, virtual machine, and compiler', ACM TOPLAS 28(4):619-695, 2006, doi:10.1145/1146809.1146811; Isabelle AFP entry Jinja (https://www.isa-afp.org/entries/Jinja.html), theory JVM/JVMExceptions.thy: matches_ex_entry tests the half-open range 's <= pc < e' plus a class check, match_ex_table returns the first matching entry's handler (None if no entry matches), and find_handler pops frames until some frame's exception table matches. Derived (modeling bridge): the same first-match half-open lookup and frame-by-frame handler search, mechanized; Jinja has no register restoration from unwind rows, no 'entry without landing pad' outcome and no terminate-on-uncovered-PC outcome.

**Design question:** Which properties of a call-site table make the personality routine's lookup return the intended landing pad, and which off-by-one conventions break it?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM libc++abi (llvm/llvm-project 701f926a): lookupScan mirrors this scan with unit-size toy addresses and frameAction mirrors the three outcomes.
- Klein and Nipkow (2006) / AFP Jinja: the same first-match half-open lookup and frame-by-frame handler search, mechanized; Jinja has no register restoration from unwind rows, no 'entry without landing pad' outcome and no terminate-on-uncovered-PC outcome.

### R5d: `uniqueAt_of_nonOverlapping`

- **Kind:** theorem.  **Tier:** T0 (re-derivation of a known result).  **Depth:** shallow.
- **Plain claim:** If the ranges at distinct positions of a call-site table are pairwise disjoint, then at every pc at most one distinct entry value contains pc.
- **Key definitions:** `NonOverlapping`, `UniqueAt`.

Lean statement (proof elided as `…`):

`Toy.CFI.uniqueAt_of_nonOverlapping` (`lean/ToyCFI/LSDA.lean:151-153`):

```lean
-- lean/ToyCFI/LSDA.lean:151-153
/-- Derivation: pairwise-disjoint ranges imply uniqueness at every `pc`. -/
theorem uniqueAt_of_nonOverlapping {t : LSDA} (h : NonOverlapping t) (pc : Nat) :
    UniqueAt t pc := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `h : NonOverlapping t` | disjointness of ranges | tight: counterexample `uniqueAt_fails_without_nonOverlapping`; witness class: the concrete 2-entry table with overlapping ranges `lsdaOverlap` = [0,10) ↦ 1, [5,15) ↦ 2, where uniqueness fails at `pc = 7` |

**Depth:** shallow. Induction over the table.

**Non-vacuity witness:** lsdaAdjacent is non-overlapping. (`lsdaAdjacent_wellFormed`)

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.uniqueAt_fails_without_nonOverlapping` (`lean/ToyCFI/LSDA.lean:237-240`):

```lean
-- lean/ToyCFI/LSDA.lean:237-240
/-- Tightness of non-overlap for `uniqueAt_of_nonOverlapping`: the overlapping
table is not `NonOverlapping`, and uniqueness fails at `pc = 7`. -/
theorem uniqueAt_fails_without_nonOverlapping :
    ¬ NonOverlapping lsdaOverlap ∧ ¬ UniqueAt lsdaOverlap 7 := …
```

`Toy.CFI.lsdaAdjacent_wellFormed` (`lean/ToyCFI/LSDA.lean:213-213`):

```lean
-- lean/ToyCFI/LSDA.lean:213-213
theorem lsdaAdjacent_wellFormed : SortedByStart lsdaAdjacent ∧ NonOverlapping lsdaAdjacent := …
```

</details>

**Prior art.**

- LLVM libc++abi, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, libcxxabi/src/cxa_personality.cpp, scan_eh_tab: no LSDA gives _URC_CONTINUE_UNWIND (lines 684-688); 'uintptr_t ip = _Unwind_GetIP(context) - 1' (line 698); comments 'The call sites are non-overlapping in [start, start+length)' and 'The call sites are ordered in increasing value of start' (lines 747-748); match condition 'start <= ipOffset && ipOffset < start + length' (line 753); landingPad == 0 gives _URC_CONTINUE_UNWIND (lines 763-768); 'else if (ipOffset < start)' calls call_terminate (lines 899-905); falling off the end of the table calls call_terminate (lines 910-911). Derived (modeling bridge): lookupScan mirrors this scan with unit-size toy addresses and frameAction mirrors the three outcomes.

**Design question:** Which properties of a call-site table make the personality routine's lookup return the intended landing pad, and which off-by-one conventions break it?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM libc++abi (llvm/llvm-project 701f926a): lookupScan mirrors this scan with unit-size toy addresses and frameAction mirrors the three outcomes.
- General: the libc++abi scan cites non-overlapping, start-ordered call sites as an invariant of the table (comment lines 747-748 of cxa_personality.cpp at the pinned commit); this lemma connects that global invariant to the pointwise uniqueness condition used by the lookup lemmas.

### R5e: `lookupIncl_wrong_on_adjacent_ranges`, `lookup_at_return_address_misses_last_call_in_range`

- **Kind:** counterexample.  **Tier:** T0 (re-derivation of a known result).  **Depth:** definitional.
- **Plain claim:** Two off-by-one conventions break lookup on the sorted, non-overlapping table [0,4) -> 1, [4,8) -> 2: a lookup that treats the end as inclusive returns landing pad 1 for a call at 4 (correct: 2) and landing pad 2 for a call at 8, which no range contains (correct: not found); and looking up the return address 3 + 1 of a call at address 3, the last address of [0,4), finds landing pad 2, whereas looking up return address - 1 finds the correct landing pad 1.
- **Key definitions:** `lookupIncl`, `lookupFirst`, `lsdaAdjacent` (concrete table [0,4) -> 1, [4,8) -> 2).

Lean statement (proof elided as `…`):

`Toy.CFI.lookupIncl_wrong_on_adjacent_ranges` (`lean/ToyCFI/LSDA.lean:219-225`):

```lean
-- lean/ToyCFI/LSDA.lean:219-225
/-- Off-by-one (inclusive end): on a sorted, non-overlapping table with adjacent
ranges, treating `stop` as inclusive returns the landing pad of the range
ending at `4` for a call at `4`, and reports a landing pad for a call at `8`
that no range contains. -/
theorem lookupIncl_wrong_on_adjacent_ranges :
    lookupIncl lsdaAdjacent 4 = .landingPad 1 ∧ lookupFirst lsdaAdjacent 4 = .landingPad 2 ∧
      lookupIncl lsdaAdjacent 8 = .landingPad 2 ∧ lookupFirst lsdaAdjacent 8 = .notFound := …
```

`Toy.CFI.lookup_at_return_address_misses_last_call_in_range` (`lean/ToyCFI/LSDA.lean:228-234`):

```lean
-- lean/ToyCFI/LSDA.lean:228-234
/-- Off-by-one (return address): a call at address `3`, the last instruction of
the range `[0,4)`, has return address `4`; looking up the return address finds
the next range's landing pad, looking up `return address - 1` finds the right
one. -/
theorem lookup_at_return_address_misses_last_call_in_range :
    lookupFirst lsdaAdjacent (3 + 1) = .landingPad 2 ∧
      lookupFirst lsdaAdjacent (3 + 1 - 1) = .landingPad 1 := …
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete objects.

**Depth:** definitional. Concrete evaluations.

**Non-vacuity witness:** lsdaAdjacent_wellFormed: the table is sorted and non-overlapping. (`lsdaAdjacent_wellFormed`)

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.lsdaAdjacent_wellFormed` (`lean/ToyCFI/LSDA.lean:213-213`):

```lean
-- lean/ToyCFI/LSDA.lean:213-213
theorem lsdaAdjacent_wellFormed : SortedByStart lsdaAdjacent ∧ NonOverlapping lsdaAdjacent := …
```

</details>

**Prior art.**

- LLVM libc++abi, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, libcxxabi/src/cxa_personality.cpp, scan_eh_tab: no LSDA gives _URC_CONTINUE_UNWIND (lines 684-688); 'uintptr_t ip = _Unwind_GetIP(context) - 1' (line 698); comments 'The call sites are non-overlapping in [start, start+length)' and 'The call sites are ordered in increasing value of start' (lines 747-748); match condition 'start <= ipOffset && ipOffset < start + length' (line 753); landingPad == 0 gives _URC_CONTINUE_UNWIND (lines 763-768); 'else if (ipOffset < start)' calls call_terminate (lines 899-905); falling off the end of the table calls call_terminate (lines 910-911). Derived (modeling bridge): lookupScan mirrors this scan with unit-size toy addresses and frameAction mirrors the three outcomes.

**Design question:** Which properties of a call-site table make the personality routine's lookup return the intended landing pad, and which off-by-one conventions break it?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM libc++abi (llvm/llvm-project 701f926a): lookupScan mirrors this scan with unit-size toy addresses and frameAction mirrors the three outcomes.
- General: libc++abi looks up `_Unwind_GetIP(context) - 1` (cxa_personality.cpp line 698 at the pinned commit), which avoids the return-address off-by-one shown here; real tables use byte offsets.

### R6: `unwind_caught_at_first_handler_frame_with_caller_registers`

- **Kind:** theorem.  **Tier:** T1 (folklore made precise).  **Depth:** substantive.
- **Plain claim:** Let the true states of frames 0..j (innermost first) form a call chain - frame i's true state is reachable at its call when its function is called from frame i+1's true state (or from top) - let st0 be frame 0's true state, and let the tables of frames 0..j be correct. Suppose the toy personality routine frameAction (an early-exit scan lookupScan of the frame's call-site table; no table means skip) returns skip for frames 0..j-1 and handle lp for frame j; the call-site rows of frames 1..j use sp or a callee-saved register as CFA base; and the throw-time memory st0.mem still holds the save slots read by the call-site rows of frames 1..j-1. Then unwinding from st0 stops at frame j with landing pad lp, in a state st that agrees with frame j's true state on sp and the callee-saved registers and whose memory is st0.mem (frame 0's throw-time memory, not frame j's pre-call memory); frame j's CFI program has a row R at frame j's call PC, and in st that row computes frame j's true CFA and hence the frame base CFA - frameSize.
- **Key definitions:** `Frame`, `frameAction`, `unwind`, `unwindFrom`, `unwindRegs`, `callerCtx`, `AtCallSite`, `ChainUpTo`, `TablesUpTo`, `SkippedBelow`, `BaseSafeUpTo`, `CfaBaseSafe`, `SlotsPreservedBelow`, `SlotsPreserved`, `CaughtWithCallerState`, `Agree`, `frameBase`.

Lean statement (proof elided as `…`):

`Toy.CFI.unwind_caught_at_first_handler_frame_with_caller_registers` (`lean/ToyCFI/MultiFrame.lean:306-327`):

```lean
-- lean/ToyCFI/MultiFrame.lean:306-327
/-- **Multi-frame composition.** Let the true states of frames `0, …, j`
(innermost first) form a call chain — frame `i`'s true state is reachable at its
`call` when its function is called from frame `i + 1`'s true state (or from
`top`) — let `st0` be frame `0`'s true state, and let the tables of frames
`0, …, j` be correct.  Suppose the toy personality routine (`frameAction`, an
early-exit scan of the call-site table) returns `skip` for frames `0, …, j-1`
and `handle lp` for frame `j`; the call-site rows of frames `1, …, j` use `sp`
or a callee-saved register as CFA base; and the throw-time memory `st0.mem`
still holds the save slots read by the call-site rows of frames `1, …, j-1`.
Then unwinding from `st0` stops at frame `j` with landing pad `lp`, in a state
that agrees with frame `j`'s true state on `sp` and the callee-saved registers
and whose memory is `st0.mem`; frame `j`'s program has a row at its call site,
and that row computes frame `j`'s true CFA and hence the frame base
`CFA - frameSize`. -/
theorem unwind_caught_at_first_handler_frame_with_caller_registers
    (frames : List Frame) (truth : List MState) (top : Caller) (st0 : MState)
    (j lp : Nat) (frj : Frame) (stj : MState)
    (hchain : ChainUpTo frames truth top j) (htab : TablesUpTo frames j)
    (h0 : truth[0]? = some st0) (hj : frames[j]? = some frj) (htj : truth[j]? = some stj)
    (hskip : SkippedBelow frames j) (hcatch : frameAction frj = .handle lp)
    (hbase : BaseSafeUpTo frames j) (hslots : SlotsPreservedBelow frames truth st0.mem j) :
    CaughtWithCallerState frames truth top st0 j lp frj stj := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hchain : ChainUpTo frames truth top j` | ties the claimed true states to executions of each frame's function called from the next frame | tight: counterexample `multiFrame_fails_without_chainUpTo`; witness class: a concrete 2-frame instance (`frames2`; j = 1, so `SlotsPreservedBelow` holds vacuously) whose claimed innermost true state and starting state `innerStBad` (`innerSt` with `fp` set to 900) is not reachable at `innerFn`'s call from the caller context of `outerSt`, so `ChainUpTo` fails |
| `htab : TablesUpTo frames j` | each frame's row at its call site must recover its caller | tight: counterexample `multiFrame_fails_without_tablesUpTo`; witness class: a concrete 2-frame instance (j = 1, so `SlotsPreservedBelow` holds vacuously) whose inner frame `innerFrameBad` has the empty CFI program (the initial row at every PC), so its table is not correct |
| `h0 : truth[0]? = some st0` | ties the starting state st0 to frame 0's true state | tight: counterexample `multiFrame_fails_without_h0`; witness class: a concrete 2-frame instance (`frames2`, `truth2`; j = 1, so `SlotsPreservedBelow` holds vacuously) started from `innerStBad` (`innerSt` with `fp` set to 900) instead of `truth[0] = innerSt` |
| `hj : frames[j]? = some frj` | names frame j and carries j < frames.length | tight: counterexample `multiFrame_fails_without_hj`; witness class: degenerate boundary instance: the empty frame list `[]` with `j = 1` and the 2-state truth list `truth2`; `ChainUpTo`, `TablesUpTo`, `SkippedBelow`, `BaseSafeUpTo` and `SlotsPreservedBelow` hold vacuously, and unwinding escapes |
| `htj : truth[j]? = some stj` | names frame j's true state and carries j < truth.length (otherwise ChainUpTo does not constrain frame j) | tight: counterexample `multiFrame_fails_without_htj`; witness class: degenerate boundary instance: `frames2` at `j = 1` with the truncated 1-state truth list `[innerSt]` and top caller `ctxOf outerSt`, so `ChainUpTo` does not constrain frame 1; `stj` is the arbitrary state `innerStBad` |
| `hskip : SkippedBelow frames j` | the personality routine (operationally: frameAction, via lookupScan) skips frames 0..j-1 | tight: counterexample `multiFrame_fails_without_skippedBelow`; witness class: a concrete 2-frame instance (j = 1, so `SlotsPreservedBelow` holds vacuously) whose inner frame `innerFrameTerm` has the empty call-site table (`lsda = some []`), so `frameAction` terminates at depth 0 |
| `hcatch : frameAction frj = .handle lp` | the personality routine (operationally: frameAction, via lookupScan) returns handle lp at frame j | tight: counterexample `multiFrame_fails_without_handler`; witness class: a concrete 2-frame instance (j = 1, so `SlotsPreservedBelow` holds vacuously) whose outer frame `outerFrameNoLsda` has no call-site table, so it is skipped too and unwinding escapes |
| `hbase : BaseSafeUpTo frames j` | a reconstructed state is only right on sp and callee-saved registers, so CFA rules must not read scratch registers | tight: counterexample `multiFrame_fails_without_baseSafeUpTo`; witness class: a concrete 2-frame instance (`innerT1Frame`, `outerT1Frame`; j = 1, so `SlotsPreservedBelow` holds vacuously) in which the outer frame's correct hand-written table `outerT1CFI` anchors the CFA in the scratch register `t1`, which the inner frame overwrites |
| `hslots : SlotsPreservedBelow frames truth st0.mem j` | inner frames must not have overwritten the save slots that outer rows read | tight: counterexample `multiFrame_fails_without_slotsPreservedBelow`; witness class: a concrete 3-frame instance (`frames3`, `truth3`; `j = 2`, so the index range 0 < i < j is non-empty) in which the innermost frame `clobberFrame` stores `t1` into the middle frame's save slot for `fp` |

**Depth:** substantive. Induction on the handler depth j, applying at each skipped frame the frame lemma `recovers_of_reads_agree` to the row at the call site, with `BaseSafeUpTo` and `SlotsPreservedBelow` supplying the agreement it needs.

**Non-vacuity witness:** Two frames: an inner function with a frame-pointer prologue and no call-site table, called from an outer function whose call site has landing pad 7; the state reached at the handler has the outer frame's sp = 998, fp = 11, s1 = 22 (multiFrame_outcome). The handler depth is j = 1, so the index range 0 < i < j of SlotsPreservedBelow is empty and that hypothesis holds vacuously (slotsPreservedBelow_one); no instance in the package satisfies all hypotheses with j >= 2 (the 3-frame, j = 2 instance multiFrame_fails_without_slotsPreservedBelow is one in which SlotsPreservedBelow fails). (`multiFrame_hypotheses_hold`)

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.multiFrame_fails_without_chainUpTo` (`lean/ToyCFI/MultiFrameExamples.lean:429-438`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:429-438
/-- Tightness of the chain hypothesis: with an unreachable innermost "true"
state, every other hypothesis holds but the reconstructed outer `sp` is wrong. -/
theorem multiFrame_fails_without_chainUpTo :
    ¬ ChainUpTo frames2 [innerStBad, outerSt] topCaller 1 ∧ TablesUpTo frames2 1 ∧
      [innerStBad, outerSt][0]? = some innerStBad ∧ frames2[1]? = some outerFrame ∧
      [innerStBad, outerSt][1]? = some outerSt ∧ SkippedBelow frames2 1 ∧
      frameAction outerFrame = .handle 7 ∧ BaseSafeUpTo frames2 1 ∧
      SlotsPreservedBelow frames2 [innerStBad, outerSt] innerStBad.mem 1 ∧
      ¬ CaughtWithCallerState frames2 [innerStBad, outerSt] topCaller innerStBad 1 7 outerFrame
        outerSt := …
```

`Toy.CFI.multiFrame_fails_without_tablesUpTo` (`lean/ToyCFI/MultiFrameExamples.lean:186-194`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:186-194
theorem multiFrame_fails_without_tablesUpTo :
    ChainUpTo [innerFrameBad, outerFrame] truth2 topCaller 1 ∧
      ¬ TablesUpTo [innerFrameBad, outerFrame] 1 ∧
      truth2[0]? = some innerSt ∧ [innerFrameBad, outerFrame][1]? = some outerFrame ∧
      truth2[1]? = some outerSt ∧ SkippedBelow [innerFrameBad, outerFrame] 1 ∧
      frameAction outerFrame = .handle 7 ∧ BaseSafeUpTo [innerFrameBad, outerFrame] 1 ∧
      SlotsPreservedBelow [innerFrameBad, outerFrame] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [innerFrameBad, outerFrame] truth2 topCaller innerSt 1 7 outerFrame
        outerSt := …
```

`Toy.CFI.multiFrame_fails_without_h0` (`lean/ToyCFI/MultiFrameExamples.lean:514-523`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:514-523
/-- Tightness of `h0 : truth[0]? = some st0` (it ties the starting state to
frame `0`'s true state): starting from `innerStBad` instead of `truth2[0]`,
every other hypothesis holds and the reconstructed `sp` is wrong. -/
theorem multiFrame_fails_without_h0 :
    ChainUpTo frames2 truth2 topCaller 1 ∧ TablesUpTo frames2 1 ∧
      truth2[0]? ≠ some innerStBad ∧ frames2[1]? = some outerFrame ∧
      truth2[1]? = some outerSt ∧ SkippedBelow frames2 1 ∧
      frameAction outerFrame = .handle 7 ∧ BaseSafeUpTo frames2 1 ∧
      SlotsPreservedBelow frames2 truth2 innerStBad.mem 1 ∧
      ¬ CaughtWithCallerState frames2 truth2 topCaller innerStBad 1 7 outerFrame outerSt := …
```

`Toy.CFI.multiFrame_fails_without_hj` (`lean/ToyCFI/MultiFrameExamples.lean:467-476`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:467-476
/-- Tightness of `hj : frames[j]? = some frj` (it carries `j < frames.length`):
with no frames every other hypothesis holds (vacuously or concretely) and
unwinding escapes. -/
theorem multiFrame_fails_without_hj :
    ChainUpTo [] truth2 topCaller 1 ∧ TablesUpTo [] 1 ∧
      truth2[0]? = some innerSt ∧ ([] : List Frame)[1]? ≠ some outerFrame ∧
      truth2[1]? = some outerSt ∧ SkippedBelow [] 1 ∧
      frameAction outerFrame = .handle 7 ∧ BaseSafeUpTo [] 1 ∧
      SlotsPreservedBelow [] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [] truth2 topCaller innerSt 1 7 outerFrame outerSt := …
```

`Toy.CFI.multiFrame_fails_without_htj` (`lean/ToyCFI/MultiFrameExamples.lean:483-494`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:483-494
/-- Tightness of `htj : truth[j]? = some stj` (it carries `j < truth.length`):
with a one-element truth list, `ChainUpTo` no longer constrains frame `1` and
`callerCtx` falls back to the context of the outer frame's state; every other
hypothesis holds for an arbitrary `stj` (here `innerStBad`), and the
reconstructed state does not agree with it. -/
theorem multiFrame_fails_without_htj :
    ChainUpTo frames2 [innerSt] (ctxOf outerSt) 1 ∧ TablesUpTo frames2 1 ∧
      [innerSt][0]? = some innerSt ∧ frames2[1]? = some outerFrame ∧
      ([innerSt][1]? : Option MState) ≠ some innerStBad ∧ SkippedBelow frames2 1 ∧
      frameAction outerFrame = .handle 7 ∧ BaseSafeUpTo frames2 1 ∧
      SlotsPreservedBelow frames2 [innerSt] innerSt.mem 1 ∧
      ¬ CaughtWithCallerState frames2 [innerSt] (ctxOf outerSt) innerSt 1 7 outerFrame innerStBad := …
```

`Toy.CFI.multiFrame_fails_without_skippedBelow` (`lean/ToyCFI/MultiFrameExamples.lean:213-221`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:213-221
theorem multiFrame_fails_without_skippedBelow :
    ChainUpTo [innerFrameTerm, outerFrame] truth2 topCaller 1 ∧
      TablesUpTo [innerFrameTerm, outerFrame] 1 ∧
      truth2[0]? = some innerSt ∧ [innerFrameTerm, outerFrame][1]? = some outerFrame ∧
      truth2[1]? = some outerSt ∧ ¬ SkippedBelow [innerFrameTerm, outerFrame] 1 ∧
      frameAction outerFrame = .handle 7 ∧ BaseSafeUpTo [innerFrameTerm, outerFrame] 1 ∧
      SlotsPreservedBelow [innerFrameTerm, outerFrame] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [innerFrameTerm, outerFrame] truth2 topCaller innerSt 1 7 outerFrame
        outerSt := …
```

`Toy.CFI.multiFrame_fails_without_handler` (`lean/ToyCFI/MultiFrameExamples.lean:239-247`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:239-247
theorem multiFrame_fails_without_handler :
    ChainUpTo [innerFrame, outerFrameNoLsda] truth2 topCaller 1 ∧
      TablesUpTo [innerFrame, outerFrameNoLsda] 1 ∧
      truth2[0]? = some innerSt ∧ [innerFrame, outerFrameNoLsda][1]? = some outerFrameNoLsda ∧
      truth2[1]? = some outerSt ∧ SkippedBelow [innerFrame, outerFrameNoLsda] 1 ∧
      frameAction outerFrameNoLsda ≠ .handle 7 ∧ BaseSafeUpTo [innerFrame, outerFrameNoLsda] 1 ∧
      SlotsPreservedBelow [innerFrame, outerFrameNoLsda] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [innerFrame, outerFrameNoLsda] truth2 topCaller innerSt 1 7
        outerFrameNoLsda outerSt := …
```

`Toy.CFI.multiFrame_fails_without_baseSafeUpTo` (`lean/ToyCFI/MultiFrameExamples.lean:292-305`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:292-305
/-- Tightness of the CFA-base condition: the outer frame anchors its CFA in the
scratch register `t1`, which the inner frame overwrites (and, `t1` not being
callee-saved, need not recover); the outer frame's computed frame base is
wrong. -/
theorem multiFrame_fails_without_baseSafeUpTo :
    ChainUpTo [innerT1Frame, outerT1Frame] [innerT1St, outerT1St] topCaller 1 ∧
      TablesUpTo [innerT1Frame, outerT1Frame] 1 ∧
      [innerT1St, outerT1St][0]? = some innerT1St ∧
      [innerT1Frame, outerT1Frame][1]? = some outerT1Frame ∧
      [innerT1St, outerT1St][1]? = some outerT1St ∧ SkippedBelow [innerT1Frame, outerT1Frame] 1 ∧
      frameAction outerT1Frame = .handle 7 ∧ ¬ BaseSafeUpTo [innerT1Frame, outerT1Frame] 1 ∧
      SlotsPreservedBelow [innerT1Frame, outerT1Frame] [innerT1St, outerT1St] innerT1St.mem 1 ∧
      ¬ CaughtWithCallerState [innerT1Frame, outerT1Frame] [innerT1St, outerT1St] topCaller innerT1St
        1 7 outerT1Frame outerT1St := …
```

`Toy.CFI.multiFrame_fails_without_slotsPreservedBelow` (`lean/ToyCFI/MultiFrameExamples.lean:369-377`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:369-377
/-- Tightness of save-slot preservation: the innermost frame overwrites the middle
frame's saved `fp`; every other hypothesis holds (`j = 2`), but the
reconstructed outer `fp` is wrong. -/
theorem multiFrame_fails_without_slotsPreservedBelow :
    ChainUpTo frames3 truth3 topCaller 2 ∧ TablesUpTo frames3 2 ∧
      truth3[0]? = some clobberSt ∧ frames3[2]? = some outerFrame ∧ truth3[2]? = some outerSt ∧
      SkippedBelow frames3 2 ∧ frameAction outerFrame = .handle 7 ∧ BaseSafeUpTo frames3 2 ∧
      ¬ SlotsPreservedBelow frames3 truth3 clobberSt.mem 2 ∧
      ¬ CaughtWithCallerState frames3 truth3 topCaller clobberSt 2 7 outerFrame outerSt := …
```

`Toy.CFI.multiFrame_hypotheses_hold` (`lean/ToyCFI/MultiFrameExamples.lean:158-165`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:158-165
/-- **Non-vacuity.** The two-frame chain (inner frame without call-site table,
outer frame with landing pad `7` at its call) satisfies every hypothesis of
`unwind_caught_at_first_handler_frame_with_caller_registers` with `j = 1`. -/
theorem multiFrame_hypotheses_hold :
    ChainUpTo frames2 truth2 topCaller 1 ∧ TablesUpTo frames2 1 ∧
      truth2[0]? = some innerSt ∧ frames2[1]? = some outerFrame ∧ truth2[1]? = some outerSt ∧
      SkippedBelow frames2 1 ∧ frameAction outerFrame = .handle 7 ∧
      BaseSafeUpTo frames2 1 ∧ SlotsPreservedBelow frames2 truth2 innerSt.mem 1 := …
```

</details>

**Prior art.**

- Itanium C++ ABI: Exception Handling ($Revision: 1.22 $), https://itanium-cxx-abi.github.io/cxx-abi/abi-eh.html: two-phase unwinding (the search phase calls the personality routine frame by frame and, if it reports failure, terminate() is called instead of phase 2; the cleanup phase restores the register state at the handler frame); the personality routine is language- and vendor-specific; _Unwind_GetLanguageSpecificData returns the frame's LSDA. The call-site table layout is not specified in that document.
- LLVM libc++abi, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, libcxxabi/src/cxa_personality.cpp, scan_eh_tab: no LSDA gives _URC_CONTINUE_UNWIND (lines 684-688); 'uintptr_t ip = _Unwind_GetIP(context) - 1' (line 698); comments 'The call sites are non-overlapping in [start, start+length)' and 'The call sites are ordered in increasing value of start' (lines 747-748); match condition 'start <= ipOffset && ipOffset < start + length' (line 753); landingPad == 0 gives _URC_CONTINUE_UNWIND (lines 763-768); 'else if (ipOffset < start)' calls call_terminate (lines 899-905); falling off the end of the table calls call_terminate (lines 910-911). Derived (modeling bridge): lookupScan mirrors this scan with unit-size toy addresses and frameAction mirrors the three outcomes.
- LLVM libunwind, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc. libunwind/src/DwarfParser.hpp: struct PrologInfo (lines 95-100: cfaRegister, cfaRegisterOffset, savedRegisters); parseFDEInstructions loop 'while ((p < instructionsEnd) && (codeOffset < pcoffset))' (line 503); DW_CFA_remember_state pushes a copy of the whole PrologInfo ('entry->info = *results', lines 606-621); DW_CFA_restore_state pops it ('*results = top->info') and returns false on an empty stack (lines 622-632); DW_CFA_def_cfa_register sets only cfaRegister and DW_CFA_def_cfa_offset only cfaRegisterOffset (lines 646-661). libunwind/src/DwarfInstructions.hpp: getCFA returns register value + cfaRegisterOffset (lines 66-76); kRegisterInCFA reads memory at cfa + value (lines 107-108); the caller's SP is set to the CFA (line 284). Derived (modeling bridge): the toy rowAt? applies every instruction located at an address <= pc, whereas this loop stops before instructions located exactly at pcoffset; how that interacts with the caller-side PC adjustment was not examined.
- DWARF Debugging Information Format Committee, DWARF Debugging Information Format, Version 5 (February 13, 2017), https://dwarfstd.org/doc/DWARF5.pdf. §2.5.1.2 DW_OP_fbreg (an offset from the address given by DW_AT_frame_base); §2.5.1.3 item 15 (printed page 33; PDF page 51) DW_OP_call_frame_cfa (pushes the CFA obtained from the call frame information; computing DW_AT_frame_base from registers would 'in some cases ... require an extensive location list because the values of the registers used in computing the CFA change during a subroutine'). §6.4.2.4 (printed page 181; PDF page 199) DW_CFA_remember_state / DW_CFA_restore_state ('push the set of rules for every register onto an implicit stack' / 'pop the set of rules off the implicit stack and place them in the current row') in the wording quoted by DWARF issue 230103.1. The toy's register rules and CFA-definition instructions are modeled on the pinned LLVM libunwind implementation (libunwind/src/DwarfParser.hpp and DwarfInstructions.hpp at llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc) rather than on the text of §6.4.1 and §6.4.2.2.
- G. Klein, T. Nipkow, 'A machine-checked model for a Java-like language, virtual machine, and compiler', ACM TOPLAS 28(4):619-695, 2006, doi:10.1145/1146809.1146811; Isabelle AFP entry Jinja (https://www.isa-afp.org/entries/Jinja.html), theory JVM/JVMExceptions.thy: matches_ex_entry tests the half-open range 's <= pc < e' plus a class check, match_ex_table returns the first matching entry's handler (None if no entry matches), and find_handler pops frames until some frame's exception table matches. Derived (modeling bridge): the same first-match half-open lookup and frame-by-frame handler search, mechanized; Jinja has no register restoration from unwind rows, no 'entry without landing pad' outcome and no terminate-on-uncovered-PC outcome.

**Design question:** What does exception propagation through several frames rely on beyond per-function table correctness?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM libc++abi (llvm/llvm-project 701f926a): lookupScan mirrors this scan with unit-size toy addresses and frameAction mirrors the three outcomes.
- LLVM libunwind (llvm/llvm-project 701f926a): the toy rowAt? applies every instruction located at an address <= pc, whereas this loop stops before instructions located exactly at pcoffset; how that interacts with the caller-side PC adjustment was not examined.
- Klein and Nipkow (2006) / AFP Jinja: the same first-match half-open lookup and frame-by-frame handler search, mechanized; Jinja has no register restoration from unwind rows, no 'entry without landing pad' outcome and no terminate-on-uncovered-PC outcome.

### R6c: `unwind_caught_at_first_handler_frame_of_sorted_unique_lsda`

- **Kind:** theorem.  **Tier:** T1 (folklore made precise).  **Depth:** shallow.
- **Plain claim:** Let frames 0..j (innermost first) be suspended at call operations, and let their true states form a call chain: for each i <= j, frame i's true state is reachable at its call PC when its function is called from frame i+1's true state, or from the outermost caller top if there is none (ChainUpTo); let st0 be frame 0's true state (truth[0]? = some st0), let frj and stj be frame j and its true state (frames[j]? = some frj, truth[j]? = some stj), and let the CFI programs of frames 0..j be TableCorrect for their functions (TablesUpTo). Suppose that the call-site tables of frames 0..j are sorted by start address and have at most one distinct entry value containing the frame's call PC (LsdaWellFormedUpTo); each of frames 0..j-1 has no call-site table or an entry containing its call PC without a landing pad (DeclarativeSkippedBelow); frame j's table has an entry containing its call PC with landing pad lp (DeclarativeCatch); the call-site rows of frames 1..j use sp or a callee-saved register as CFA base (BaseSafeUpTo); and the throw-time memory st0.mem still holds the save slots read by the call-site rows of frames 1..j-1 (SlotsPreservedBelow). Then unwinding from st0 with the toy personality routine frameAction (an early-exit scan lookupScan of each frame's call-site table; no table means skip) stops at frame j with landing pad lp, in a state st that agrees with frame j's true state on sp and the callee-saved registers and whose memory is st0.mem (frame 0's throw-time memory, not frame j's pre-call memory); frame j's CFI program has a row R at frame j's call PC, and in st that row computes frame j's true CFA and hence the frame base CFA - frameSize.
- **Key definitions:** `LsdaWellFormedUpTo`, `DeclarativeSkip`, `DeclarativeSkippedBelow`, `DeclarativeCatch`, plus `Frame`, `frameAction`, `unwind`, `ChainUpTo`, `TablesUpTo`, `BaseSafeUpTo`, `SlotsPreservedBelow`, `CaughtWithCallerState`.

Lean statement (proof elided as `…`):

`Toy.CFI.unwind_caught_at_first_handler_frame_of_sorted_unique_lsda` (`lean/ToyCFI/MultiFrame.lean:359-375`):

```lean
-- lean/ToyCFI/MultiFrame.lean:359-375
/-- **Multi-frame composition with declarative call-site tables.** As
`unwind_caught_at_first_handler_frame_with_caller_registers`, but with the
personality outcomes replaced by conditions on the tables themselves: the
call-site tables of frames `0, …, j` are sorted by start and have at most one
distinct entry value containing the call PC (`LsdaWellFormedUpTo`); each of
frames `0, …, j-1` has no table or an entry containing its call PC without a
landing pad (`DeclarativeSkippedBelow`); frame `j`'s table has an entry containing its
call PC with landing pad `lp` (`DeclarativeCatch`). -/
theorem unwind_caught_at_first_handler_frame_of_sorted_unique_lsda
    (frames : List Frame) (truth : List MState) (top : Caller) (st0 : MState)
    (j lp : Nat) (frj : Frame) (stj : MState)
    (hchain : ChainUpTo frames truth top j) (htab : TablesUpTo frames j)
    (hlsda : LsdaWellFormedUpTo frames j)
    (h0 : truth[0]? = some st0) (hj : frames[j]? = some frj) (htj : truth[j]? = some stj)
    (hskip : DeclarativeSkippedBelow frames j) (hcatch : DeclarativeCatch frj lp)
    (hbase : BaseSafeUpTo frames j) (hslots : SlotsPreservedBelow frames truth st0.mem j) :
    CaughtWithCallerState frames truth top st0 j lp frj stj := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hchain : ChainUpTo frames truth top j` | ties the claimed true states to executions of each frame's function called from the next frame | tight: counterexample `multiFrameDecl_fails_without_chainUpTo`; witness class: a concrete 2-frame instance (`frames2`; j = 1, so `SlotsPreservedBelow` holds vacuously) whose claimed innermost true state and starting state `innerStBad` (`innerSt` with `fp` set to 900) is not reachable at `innerFn`'s call from the caller context of `outerSt`, so `ChainUpTo` fails |
| `htab : TablesUpTo frames j` | each frame's row at its call site must recover its caller | tight: counterexample `multiFrameDecl_fails_without_tablesUpTo`; witness class: a concrete 2-frame instance (j = 1, so `SlotsPreservedBelow` holds vacuously) whose inner frame `innerFrameBad` has the empty CFI program (the initial row at every PC), so its table is not correct |
| `hlsda : LsdaWellFormedUpTo frames j` | the early-exit scan returns the outcome of the entry containing the call PC (lookupScan_eq_result_of_sorted_uniqueAt); without it an unsorted table with a handler entry can make the personality routine terminate | tight: counterexample `multiFrameDecl_fails_without_lsdaWellFormed`; witness class: a concrete 2-frame instance (j = 1, so `SlotsPreservedBelow` holds vacuously) whose outer frame `outerFrameUnsorted` has the unsorted table [10,20) ↦ 1, [1,2) ↦ 7; the early-exit scan stops at the first entry and the personality routine terminates |
| `h0 : truth[0]? = some st0` | ties the starting state st0 to frame 0's true state | tight: counterexample `multiFrameDecl_fails_without_h0`; witness class: a concrete 2-frame instance (`frames2`, `truth2`; j = 1, so `SlotsPreservedBelow` holds vacuously) started from `innerStBad` (`innerSt` with `fp` set to 900) instead of `truth[0] = innerSt` |
| `hj : frames[j]? = some frj` | names frame j and carries j < frames.length | tight: counterexample `multiFrameDecl_fails_without_hj`; witness class: degenerate boundary instance: the empty frame list `[]` with `j = 1` and the 2-state truth list `truth2`; `ChainUpTo`, `TablesUpTo`, `LsdaWellFormedUpTo`, `DeclarativeSkippedBelow`, `BaseSafeUpTo` and `SlotsPreservedBelow` hold vacuously, and unwinding escapes |
| `htj : truth[j]? = some stj` | names frame j's true state and carries j < truth.length (otherwise ChainUpTo does not constrain frame j) | tight: counterexample `multiFrameDecl_fails_without_htj`; witness class: degenerate boundary instance: `frames2` at `j = 1` with the truncated 1-state truth list `[innerSt]` and top caller `ctxOf outerSt`, so `ChainUpTo` does not constrain frame 1; `stj` is the arbitrary state `innerStBad` |
| `hskip : DeclarativeSkippedBelow frames j` | each of frames 0..j-1 has no call-site table or an entry containing its call PC without a landing pad | tight: counterexample `multiFrameDecl_fails_without_declarativeSkippedBelow`; witness class: a concrete 2-frame instance (j = 1, so `SlotsPreservedBelow` holds vacuously) whose inner frame `innerFrameTerm` has the empty call-site table (no entry covers its call PC), so the personality routine terminates at depth 0 |
| `hcatch : DeclarativeCatch frj lp` | frame j's call-site table has an entry containing its call PC with landing pad lp | tight: counterexample `multiFrameDecl_fails_without_declarativeCatch`; witness class: a concrete 2-frame instance (j = 1, so `SlotsPreservedBelow` holds vacuously) whose outer frame `outerFrameNoLsda` has no call-site table; unwinding escapes |
| `hbase : BaseSafeUpTo frames j` | a reconstructed state is only right on sp and callee-saved registers, so CFA rules must not read scratch registers | tight: counterexample `multiFrameDecl_fails_without_baseSafeUpTo`; witness class: a concrete 2-frame instance (`innerT1Frame`, `outerT1Frame`; j = 1, so `SlotsPreservedBelow` holds vacuously) in which the outer frame's correct hand-written table `outerT1CFI` anchors the CFA in the scratch register `t1`, which the inner frame overwrites |
| `hslots : SlotsPreservedBelow frames truth st0.mem j` | inner frames must not have overwritten the save slots that outer rows read | tight: counterexample `multiFrameDecl_fails_without_slotsPreservedBelow`; witness class: a concrete 3-frame instance (`frames3`, `truth3`; `j = 2`, so the index range 0 < i < j is non-empty) in which the innermost frame `clobberFrame` stores `t1` into the middle frame's save slot for `fp` |

**Depth:** shallow. Derives `SkippedBelow` and the handler outcome from the declarative conditions with the scan lemma `lookupScan_eq_result_of_sorted_uniqueAt`, then applies `unwind_caught_at_first_handler_frame_with_caller_registers`.

**Non-vacuity witness:** The two-frame chain (inner frame without call-site table, outer frame whose table [1,2) -> 7 covers its call PC) satisfies every hypothesis with j = 1. At j = 1 the index range 0 < i < j of SlotsPreservedBelow is empty, so that hypothesis holds vacuously (slotsPreservedBelow_one); and frame 0 has no call-site table (lsda = none), so only the first disjunct of DeclarativeSkip is exercised, not the second (a covering entry without landing pad). No instance in the package satisfies all hypotheses with j >= 2 (the 3-frame, j = 2 instance multiFrameDecl_fails_without_slotsPreservedBelow is one in which SlotsPreservedBelow fails). (`multiFrame_declarative_hypotheses_hold`)

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.multiFrameDecl_fails_without_chainUpTo` (`lean/ToyCFI/MultiFrameExamples.lean:691-701`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:691-701
/-- Tightness of `ChainUpTo` for the declarative theorem (same instance as for
the operational one). -/
theorem multiFrameDecl_fails_without_chainUpTo :
    ¬ ChainUpTo frames2 [innerStBad, outerSt] topCaller 1 ∧ TablesUpTo frames2 1 ∧
      LsdaWellFormedUpTo frames2 1 ∧
      [innerStBad, outerSt][0]? = some innerStBad ∧ frames2[1]? = some outerFrame ∧
      [innerStBad, outerSt][1]? = some outerSt ∧ DeclarativeSkippedBelow frames2 1 ∧
      DeclarativeCatch outerFrame 7 ∧ BaseSafeUpTo frames2 1 ∧
      SlotsPreservedBelow frames2 [innerStBad, outerSt] innerStBad.mem 1 ∧
      ¬ CaughtWithCallerState frames2 [innerStBad, outerSt] topCaller innerStBad 1 7 outerFrame
        outerSt := …
```

`Toy.CFI.multiFrameDecl_fails_without_tablesUpTo` (`lean/ToyCFI/MultiFrameExamples.lean:706-715`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:706-715
/-- Tightness of `TablesUpTo` for the declarative theorem. -/
theorem multiFrameDecl_fails_without_tablesUpTo :
    ChainUpTo [innerFrameBad, outerFrame] truth2 topCaller 1 ∧
      ¬ TablesUpTo [innerFrameBad, outerFrame] 1 ∧ LsdaWellFormedUpTo [innerFrameBad, outerFrame] 1 ∧
      truth2[0]? = some innerSt ∧ [innerFrameBad, outerFrame][1]? = some outerFrame ∧
      truth2[1]? = some outerSt ∧ DeclarativeSkippedBelow [innerFrameBad, outerFrame] 1 ∧
      DeclarativeCatch outerFrame 7 ∧ BaseSafeUpTo [innerFrameBad, outerFrame] 1 ∧
      SlotsPreservedBelow [innerFrameBad, outerFrame] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [innerFrameBad, outerFrame] truth2 topCaller innerSt 1 7 outerFrame
        outerSt := …
```

`Toy.CFI.multiFrameDecl_fails_without_lsdaWellFormed` (`lean/ToyCFI/MultiFrameExamples.lean:613-626`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:613-626
/-- Tightness of `LsdaWellFormedUpTo`: the outer frame's table is unsorted; it
has an entry covering the call PC with landing pad `7`, so the declarative
catch condition holds, but the early-exit scan stops at the first entry and the
personality routine terminates. -/
theorem multiFrameDecl_fails_without_lsdaWellFormed :
    ChainUpTo [innerFrame, outerFrameUnsorted] truth2 topCaller 1 ∧
      TablesUpTo [innerFrame, outerFrameUnsorted] 1 ∧
      ¬ LsdaWellFormedUpTo [innerFrame, outerFrameUnsorted] 1 ∧
      truth2[0]? = some innerSt ∧ [innerFrame, outerFrameUnsorted][1]? = some outerFrameUnsorted ∧
      truth2[1]? = some outerSt ∧ DeclarativeSkippedBelow [innerFrame, outerFrameUnsorted] 1 ∧
      DeclarativeCatch outerFrameUnsorted 7 ∧ BaseSafeUpTo [innerFrame, outerFrameUnsorted] 1 ∧
      SlotsPreservedBelow [innerFrame, outerFrameUnsorted] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [innerFrame, outerFrameUnsorted] truth2 topCaller innerSt 1 7
        outerFrameUnsorted outerSt := …
```

`Toy.CFI.multiFrameDecl_fails_without_h0` (`lean/ToyCFI/MultiFrameExamples.lean:725-732`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:725-732
/-- Tightness of `h0` for the declarative theorem. -/
theorem multiFrameDecl_fails_without_h0 :
    ChainUpTo frames2 truth2 topCaller 1 ∧ TablesUpTo frames2 1 ∧ LsdaWellFormedUpTo frames2 1 ∧
      truth2[0]? ≠ some innerStBad ∧ frames2[1]? = some outerFrame ∧
      truth2[1]? = some outerSt ∧ DeclarativeSkippedBelow frames2 1 ∧
      DeclarativeCatch outerFrame 7 ∧ BaseSafeUpTo frames2 1 ∧
      SlotsPreservedBelow frames2 truth2 innerStBad.mem 1 ∧
      ¬ CaughtWithCallerState frames2 truth2 topCaller innerStBad 1 7 outerFrame outerSt := …
```

`Toy.CFI.multiFrameDecl_fails_without_hj` (`lean/ToyCFI/MultiFrameExamples.lean:737-744`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:737-744
/-- Tightness of `hj` for the declarative theorem. -/
theorem multiFrameDecl_fails_without_hj :
    ChainUpTo [] truth2 topCaller 1 ∧ TablesUpTo [] 1 ∧ LsdaWellFormedUpTo [] 1 ∧
      truth2[0]? = some innerSt ∧ ([] : List Frame)[1]? ≠ some outerFrame ∧
      truth2[1]? = some outerSt ∧ DeclarativeSkippedBelow [] 1 ∧
      DeclarativeCatch outerFrame 7 ∧ BaseSafeUpTo [] 1 ∧
      SlotsPreservedBelow [] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [] truth2 topCaller innerSt 1 7 outerFrame outerSt := …
```

`Toy.CFI.multiFrameDecl_fails_without_htj` (`lean/ToyCFI/MultiFrameExamples.lean:749-757`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:749-757
/-- Tightness of `htj` for the declarative theorem. -/
theorem multiFrameDecl_fails_without_htj :
    ChainUpTo frames2 [innerSt] (ctxOf outerSt) 1 ∧ TablesUpTo frames2 1 ∧
      LsdaWellFormedUpTo frames2 1 ∧
      [innerSt][0]? = some innerSt ∧ frames2[1]? = some outerFrame ∧
      ([innerSt][1]? : Option MState) ≠ some innerStBad ∧ DeclarativeSkippedBelow frames2 1 ∧
      DeclarativeCatch outerFrame 7 ∧ BaseSafeUpTo frames2 1 ∧
      SlotsPreservedBelow frames2 [innerSt] innerSt.mem 1 ∧
      ¬ CaughtWithCallerState frames2 [innerSt] (ctxOf outerSt) innerSt 1 7 outerFrame innerStBad := …
```

`Toy.CFI.multiFrameDecl_fails_without_declarativeSkippedBelow` (`lean/ToyCFI/MultiFrameExamples.lean:644-655`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:644-655
/-- Tightness of `DeclarativeSkippedBelow`: the inner frame has an empty table
(no entry covers its call PC); every other hypothesis holds and the personality
routine terminates at depth 0. -/
theorem multiFrameDecl_fails_without_declarativeSkippedBelow :
    ChainUpTo [innerFrameTerm, outerFrame] truth2 topCaller 1 ∧
      TablesUpTo [innerFrameTerm, outerFrame] 1 ∧ LsdaWellFormedUpTo [innerFrameTerm, outerFrame] 1 ∧
      truth2[0]? = some innerSt ∧ [innerFrameTerm, outerFrame][1]? = some outerFrame ∧
      truth2[1]? = some outerSt ∧ ¬ DeclarativeSkippedBelow [innerFrameTerm, outerFrame] 1 ∧
      DeclarativeCatch outerFrame 7 ∧ BaseSafeUpTo [innerFrameTerm, outerFrame] 1 ∧
      SlotsPreservedBelow [innerFrameTerm, outerFrame] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [innerFrameTerm, outerFrame] truth2 topCaller innerSt 1 7 outerFrame
        outerSt := …
```

`Toy.CFI.multiFrameDecl_fails_without_declarativeCatch` (`lean/ToyCFI/MultiFrameExamples.lean:671-682`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:671-682
/-- Tightness of `DeclarativeCatch`: the outer frame has no table; every other
hypothesis holds and unwinding escapes. -/
theorem multiFrameDecl_fails_without_declarativeCatch :
    ChainUpTo [innerFrame, outerFrameNoLsda] truth2 topCaller 1 ∧
      TablesUpTo [innerFrame, outerFrameNoLsda] 1 ∧
      LsdaWellFormedUpTo [innerFrame, outerFrameNoLsda] 1 ∧
      truth2[0]? = some innerSt ∧ [innerFrame, outerFrameNoLsda][1]? = some outerFrameNoLsda ∧
      truth2[1]? = some outerSt ∧ DeclarativeSkippedBelow [innerFrame, outerFrameNoLsda] 1 ∧
      ¬ DeclarativeCatch outerFrameNoLsda 7 ∧ BaseSafeUpTo [innerFrame, outerFrameNoLsda] 1 ∧
      SlotsPreservedBelow [innerFrame, outerFrameNoLsda] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [innerFrame, outerFrameNoLsda] truth2 topCaller innerSt 1 7
        outerFrameNoLsda outerSt := …
```

`Toy.CFI.multiFrameDecl_fails_without_baseSafeUpTo` (`lean/ToyCFI/MultiFrameExamples.lean:762-773`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:762-773
/-- Tightness of `BaseSafeUpTo` for the declarative theorem. -/
theorem multiFrameDecl_fails_without_baseSafeUpTo :
    ChainUpTo [innerT1Frame, outerT1Frame] [innerT1St, outerT1St] topCaller 1 ∧
      TablesUpTo [innerT1Frame, outerT1Frame] 1 ∧ LsdaWellFormedUpTo [innerT1Frame, outerT1Frame] 1 ∧
      [innerT1St, outerT1St][0]? = some innerT1St ∧
      [innerT1Frame, outerT1Frame][1]? = some outerT1Frame ∧
      [innerT1St, outerT1St][1]? = some outerT1St ∧
      DeclarativeSkippedBelow [innerT1Frame, outerT1Frame] 1 ∧ DeclarativeCatch outerT1Frame 7 ∧
      ¬ BaseSafeUpTo [innerT1Frame, outerT1Frame] 1 ∧
      SlotsPreservedBelow [innerT1Frame, outerT1Frame] [innerT1St, outerT1St] innerT1St.mem 1 ∧
      ¬ CaughtWithCallerState [innerT1Frame, outerT1Frame] [innerT1St, outerT1St] topCaller innerT1St
        1 7 outerT1Frame outerT1St := …
```

`Toy.CFI.multiFrameDecl_fails_without_slotsPreservedBelow` (`lean/ToyCFI/MultiFrameExamples.lean:783-789`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:783-789
/-- Tightness of `SlotsPreservedBelow` for the declarative theorem. -/
theorem multiFrameDecl_fails_without_slotsPreservedBelow :
    ChainUpTo frames3 truth3 topCaller 2 ∧ TablesUpTo frames3 2 ∧ LsdaWellFormedUpTo frames3 2 ∧
      truth3[0]? = some clobberSt ∧ frames3[2]? = some outerFrame ∧ truth3[2]? = some outerSt ∧
      DeclarativeSkippedBelow frames3 2 ∧ DeclarativeCatch outerFrame 7 ∧ BaseSafeUpTo frames3 2 ∧
      ¬ SlotsPreservedBelow frames3 truth3 clobberSt.mem 2 ∧
      ¬ CaughtWithCallerState frames3 truth3 topCaller clobberSt 2 7 outerFrame outerSt := …
```

`Toy.CFI.multiFrame_declarative_hypotheses_hold` (`lean/ToyCFI/MultiFrameExamples.lean:596-602`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:596-602
/-- **Non-vacuity** of the declarative composition theorem: the two-frame chain
satisfies all of its hypotheses with `j = 1`. -/
theorem multiFrame_declarative_hypotheses_hold :
    ChainUpTo frames2 truth2 topCaller 1 ∧ TablesUpTo frames2 1 ∧ LsdaWellFormedUpTo frames2 1 ∧
      truth2[0]? = some innerSt ∧ frames2[1]? = some outerFrame ∧ truth2[1]? = some outerSt ∧
      DeclarativeSkippedBelow frames2 1 ∧ DeclarativeCatch outerFrame 7 ∧
      BaseSafeUpTo frames2 1 ∧ SlotsPreservedBelow frames2 truth2 innerSt.mem 1 := …
```

</details>

**Prior art.**

- Itanium C++ ABI: Exception Handling ($Revision: 1.22 $), https://itanium-cxx-abi.github.io/cxx-abi/abi-eh.html: two-phase unwinding (the search phase calls the personality routine frame by frame and, if it reports failure, terminate() is called instead of phase 2; the cleanup phase restores the register state at the handler frame); the personality routine is language- and vendor-specific; _Unwind_GetLanguageSpecificData returns the frame's LSDA. The call-site table layout is not specified in that document.
- LLVM libc++abi, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, libcxxabi/src/cxa_personality.cpp, scan_eh_tab: no LSDA gives _URC_CONTINUE_UNWIND (lines 684-688); 'uintptr_t ip = _Unwind_GetIP(context) - 1' (line 698); comments 'The call sites are non-overlapping in [start, start+length)' and 'The call sites are ordered in increasing value of start' (lines 747-748); match condition 'start <= ipOffset && ipOffset < start + length' (line 753); landingPad == 0 gives _URC_CONTINUE_UNWIND (lines 763-768); 'else if (ipOffset < start)' calls call_terminate (lines 899-905); falling off the end of the table calls call_terminate (lines 910-911). Derived (modeling bridge): lookupScan mirrors this scan with unit-size toy addresses and frameAction mirrors the three outcomes.
- LLVM libunwind, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc. libunwind/src/DwarfParser.hpp: struct PrologInfo (lines 95-100: cfaRegister, cfaRegisterOffset, savedRegisters); parseFDEInstructions loop 'while ((p < instructionsEnd) && (codeOffset < pcoffset))' (line 503); DW_CFA_remember_state pushes a copy of the whole PrologInfo ('entry->info = *results', lines 606-621); DW_CFA_restore_state pops it ('*results = top->info') and returns false on an empty stack (lines 622-632); DW_CFA_def_cfa_register sets only cfaRegister and DW_CFA_def_cfa_offset only cfaRegisterOffset (lines 646-661). libunwind/src/DwarfInstructions.hpp: getCFA returns register value + cfaRegisterOffset (lines 66-76); kRegisterInCFA reads memory at cfa + value (lines 107-108); the caller's SP is set to the CFA (line 284). Derived (modeling bridge): the toy rowAt? applies every instruction located at an address <= pc, whereas this loop stops before instructions located exactly at pcoffset; how that interacts with the caller-side PC adjustment was not examined.
- DWARF Debugging Information Format Committee, DWARF Debugging Information Format, Version 5 (February 13, 2017), https://dwarfstd.org/doc/DWARF5.pdf. §2.5.1.2 DW_OP_fbreg (an offset from the address given by DW_AT_frame_base); §2.5.1.3 item 15 (printed page 33; PDF page 51) DW_OP_call_frame_cfa (pushes the CFA obtained from the call frame information; computing DW_AT_frame_base from registers would 'in some cases ... require an extensive location list because the values of the registers used in computing the CFA change during a subroutine'). §6.4.2.4 (printed page 181; PDF page 199) DW_CFA_remember_state / DW_CFA_restore_state ('push the set of rules for every register onto an implicit stack' / 'pop the set of rules off the implicit stack and place them in the current row') in the wording quoted by DWARF issue 230103.1. The toy's register rules and CFA-definition instructions are modeled on the pinned LLVM libunwind implementation (libunwind/src/DwarfParser.hpp and DwarfInstructions.hpp at llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc) rather than on the text of §6.4.1 and §6.4.2.2.
- G. Klein, T. Nipkow, 'A machine-checked model for a Java-like language, virtual machine, and compiler', ACM TOPLAS 28(4):619-695, 2006, doi:10.1145/1146809.1146811; Isabelle AFP entry Jinja (https://www.isa-afp.org/entries/Jinja.html), theory JVM/JVMExceptions.thy: matches_ex_entry tests the half-open range 's <= pc < e' plus a class check, match_ex_table returns the first matching entry's handler (None if no entry matches), and find_handler pops frames until some frame's exception table matches. Derived (modeling bridge): the same first-match half-open lookup and frame-by-frame handler search, mechanized; Jinja has no register restoration from unwind rows, no 'entry without landing pad' outcome and no terminate-on-uncovered-PC outcome.

**Design question:** What does exception propagation through several frames rely on beyond per-function table correctness?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM libc++abi (llvm/llvm-project 701f926a): lookupScan mirrors this scan with unit-size toy addresses and frameAction mirrors the three outcomes.
- LLVM libunwind (llvm/llvm-project 701f926a): the toy rowAt? applies every instruction located at an address <= pc, whereas this loop stops before instructions located exactly at pcoffset; how that interacts with the caller-side PC adjustment was not examined.
- Klein and Nipkow (2006) / AFP Jinja: the same first-match half-open lookup and frame-by-frame handler search, mechanized; Jinja has no register restoration from unwind rows, no 'entry without landing pad' outcome and no terminate-on-uncovered-PC outcome.

### R6b: `recovers_of_reads_agree`

- **Kind:** theorem.  **Tier:** T0 (re-derivation of a known result).  **Depth:** shallow.
- **Plain claim:** A row that recovers caller c from a state σ also recovers c from any state that agrees with σ on the row's CFA base register, on the callee-saved registers whose rule is 'same', and on the memory at the save slots of the callee-saved registers whose rule is 'offset'.
- **Key definitions:** `Recovers`, `cfaOf`, `ruleVal`, `calleeSaved`.

Lean statement (proof elided as `…`):

`Toy.CFI.recovers_of_reads_agree` (`lean/ToyCFI/MultiFrame.lean:179-186`):

```lean
-- lean/ToyCFI/MultiFrame.lean:179-186
/-- **Frame lemma.** A row that recovers caller `c` from the true state `σ` also
recovers it from any state agreeing with `σ` on what the row reads. -/
theorem recovers_of_reads_agree {R : Row} {c : Caller} {σ st : MState} (hrec : Recovers R c σ)
    (hcfa : st.regs.get R.cfaReg = σ.regs.get R.cfaReg)
    (hsame : ∀ r ∈ calleeSaved, R.rules.get r = .same → st.regs.get r = σ.regs.get r)
    (hslot : ∀ r ∈ calleeSaved, ∀ k, R.rules.get r = .offset k →
      st.mem (cfaOf R σ + k) = σ.mem (cfaOf R σ + k)) :
    Recovers R c st := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hrec : Recovers R c σ` | the row recovers the caller from the true state | tight: counterexample `recovers_of_reads_agree_fails_without_rec`; witness class: a single concrete state σ (sp = 99, fp = 5, s1 = 6, t1 = 0, zero memory) with `st = σ`, the caller `flCaller` (CFA 100) and the initial row CFA = sp + 0; the agreement hypotheses hold trivially |
| `hcfa : st.regs.get R.cfaReg = σ.regs.get R.cfaReg` | agreement on the CFA base register | tight: counterexample `recovers_of_reads_agree_fails_without_cfa`; witness class: concrete caller `flCaller` (CFA 100), true state `flSigma` (sp = 100) and the initial row, with `st` differing from `flSigma` only in sp = 101 |
| `hsame : ∀ r ∈ calleeSaved, R.rules.get r = .same → st.regs.get r = σ.regs.get r` | agreement on callee-saved registers whose rule is same | tight: counterexample `recovers_of_reads_agree_fails_without_same`; witness class: concrete caller `flCaller`, true state `flSigma` and the initial row (rule `same` for `fp`), with `st` differing from `flSigma` only in fp = 9 instead of 5 |
| `hslot : ∀ r ∈ calleeSaved, ∀ k, R.rules.get r = .offset k → st.mem (cfaOf R σ + k) = σ.mem (cfaOf R σ + k)` | agreement on the save slots read by offset rules | tight: counterexample `recovers_of_reads_agree_fails_without_slot`; witness class: concrete row `flRowSaved` (`fp` saved at CFA - 1), true state `flSigmaSaved` whose slot 99 holds the caller's `fp` = 5, and `st` with the same registers and all-zero memory |

**Depth:** shallow. Unfolding `Recovers` and `ruleVal`.

**Non-vacuity witness:** A state differing from the true state in the scratch register and in unread memory but agreeing on the CFA base, s1 and the read save slot. (`recovers_of_reads_agree_nonvacuity`)

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.recovers_of_reads_agree_fails_without_rec` (`lean/ToyCFI/MultiFrame.lean:440-449`):

```lean
-- lean/ToyCFI/MultiFrame.lean:440-449
/-- Tightness of `hrec` in the frame lemma: a row that does not recover the
caller from `σ` (its CFA rule `sp + 0` gives `99`, not `100`); every agreement
hypothesis holds trivially for `st = σ`, and the conclusion fails. -/
theorem recovers_of_reads_agree_fails_without_rec :
    let σ : MState := ⟨⟨99, 5, 6, 0⟩, fun _ => 0⟩
    ¬ Recovers initRow flCaller σ ∧ σ.regs.get initRow.cfaReg = σ.regs.get initRow.cfaReg ∧
      (∀ r ∈ calleeSaved, initRow.rules.get r = .same → σ.regs.get r = σ.regs.get r) ∧
      (∀ r ∈ calleeSaved, ∀ k, initRow.rules.get r = .offset k →
        σ.mem (cfaOf initRow σ + k) = σ.mem (cfaOf initRow σ + k)) ∧
      ¬ Recovers initRow flCaller σ := …
```

`Toy.CFI.recovers_of_reads_agree_fails_without_cfa` (`lean/ToyCFI/MultiFrame.lean:396-403`):

```lean
-- lean/ToyCFI/MultiFrame.lean:396-403
/-- Without agreement on the CFA base register the conclusion fails. -/
theorem recovers_of_reads_agree_fails_without_cfa :
    let st : MState := ⟨⟨101, 5, 6, 0⟩, fun _ => 0⟩
    Recovers initRow flCaller flSigma ∧ st.regs.get initRow.cfaReg ≠ flSigma.regs.get initRow.cfaReg ∧
      (∀ r ∈ calleeSaved, initRow.rules.get r = .same → st.regs.get r = flSigma.regs.get r) ∧
      (∀ r ∈ calleeSaved, ∀ k, initRow.rules.get r = .offset k →
        st.mem (cfaOf initRow flSigma + k) = flSigma.mem (cfaOf initRow flSigma + k)) ∧
      ¬ Recovers initRow flCaller st := …
```

`Toy.CFI.recovers_of_reads_agree_fails_without_same` (`lean/ToyCFI/MultiFrame.lean:411-418`):

```lean
-- lean/ToyCFI/MultiFrame.lean:411-418
/-- Without agreement on a callee-saved register with rule `same` the conclusion fails. -/
theorem recovers_of_reads_agree_fails_without_same :
    let st : MState := ⟨⟨100, 9, 6, 0⟩, fun _ => 0⟩
    Recovers initRow flCaller flSigma ∧ st.regs.get initRow.cfaReg = flSigma.regs.get initRow.cfaReg ∧
      ¬ (∀ r ∈ calleeSaved, initRow.rules.get r = .same → st.regs.get r = flSigma.regs.get r) ∧
      (∀ r ∈ calleeSaved, ∀ k, initRow.rules.get r = .offset k →
        st.mem (cfaOf initRow flSigma + k) = flSigma.mem (cfaOf initRow flSigma + k)) ∧
      ¬ Recovers initRow flCaller st := …
```

`Toy.CFI.recovers_of_reads_agree_fails_without_slot` (`lean/ToyCFI/MultiFrame.lean:424-432`):

```lean
-- lean/ToyCFI/MultiFrame.lean:424-432
/-- Without agreement on a read save slot the conclusion fails. -/
theorem recovers_of_reads_agree_fails_without_slot :
    let st : MState := ⟨flSigmaSaved.regs, fun _ => 0⟩
    Recovers flRowSaved flCaller flSigmaSaved ∧
      st.regs.get flRowSaved.cfaReg = flSigmaSaved.regs.get flRowSaved.cfaReg ∧
      (∀ r ∈ calleeSaved, flRowSaved.rules.get r = .same → st.regs.get r = flSigmaSaved.regs.get r) ∧
      ¬ (∀ r ∈ calleeSaved, ∀ k, flRowSaved.rules.get r = .offset k →
        st.mem (cfaOf flRowSaved flSigmaSaved + k) = flSigmaSaved.mem (cfaOf flRowSaved flSigmaSaved + k)) ∧
      ¬ Recovers flRowSaved flCaller st := …
```

`Toy.CFI.recovers_of_reads_agree_nonvacuity` (`lean/ToyCFI/MultiFrame.lean:454-463`):

```lean
-- lean/ToyCFI/MultiFrame.lean:454-463
/-- Non-vacuity of the frame lemma: a state that differs from the true state in
the scratch register and in unread memory, but agrees on what the row reads. -/
theorem recovers_of_reads_agree_nonvacuity :
    let st : MState := ⟨⟨100, 0, 6, 77⟩, fun a => if a = 99 then 5 else 42⟩
    Recovers flRowSaved flCaller flSigmaSaved ∧
      st.regs.get flRowSaved.cfaReg = flSigmaSaved.regs.get flRowSaved.cfaReg ∧
      (∀ r ∈ calleeSaved, flRowSaved.rules.get r = .same → st.regs.get r = flSigmaSaved.regs.get r) ∧
      (∀ r ∈ calleeSaved, ∀ k, flRowSaved.rules.get r = .offset k →
        st.mem (cfaOf flRowSaved flSigmaSaved + k) = flSigmaSaved.mem (cfaOf flRowSaved flSigmaSaved + k)) ∧
      st ≠ flSigmaSaved := …
```

</details>

**Prior art.**

- LLVM libunwind, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc. libunwind/src/DwarfParser.hpp: struct PrologInfo (lines 95-100: cfaRegister, cfaRegisterOffset, savedRegisters); parseFDEInstructions loop 'while ((p < instructionsEnd) && (codeOffset < pcoffset))' (line 503); DW_CFA_remember_state pushes a copy of the whole PrologInfo ('entry->info = *results', lines 606-621); DW_CFA_restore_state pops it ('*results = top->info') and returns false on an empty stack (lines 622-632); DW_CFA_def_cfa_register sets only cfaRegister and DW_CFA_def_cfa_offset only cfaRegisterOffset (lines 646-661). libunwind/src/DwarfInstructions.hpp: getCFA returns register value + cfaRegisterOffset (lines 66-76); kRegisterInCFA reads memory at cfa + value (lines 107-108); the caller's SP is set to the CFA (line 284). Derived (modeling bridge): the toy rowAt? applies every instruction located at an address <= pc, whereas this loop stops before instructions located exactly at pcoffset; how that interacts with the caller-side PC adjustment was not examined.
- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107-115, 2009, doi:10.1145/1538788.1538814; CompCert (AbsInt/CompCert commit 2685140bf72c959446981fb99b5e44a8975021bc) backend/Stackingproof.v, Lemma save_callee_save_correct (line 1007): after the prologue's callee-save sequence the frame's callee-save area contains the callee-saved values (agree_callee_save relates the caller's and callee's register states). Derived (modeling bridge): this is a mechanized counterpart of the toy's save-slot reasoning, but CompCert returns through its own verified epilogues and has no DWARF-style unwinder or row semantics.

**Design question:** What does exception propagation through several frames rely on beyond per-function table correctness?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM libunwind (llvm/llvm-project 701f926a): the toy rowAt? applies every instruction located at an address <= pc, whereas this loop stops before instructions located exactly at pcoffset; how that interacts with the caller-side PC adjustment was not examined.
- Leroy (2009) / CompCert 2685140b: this is a mechanized counterpart of the toy's save-slot reasoning, but CompCert returns through its own verified epilogues and has no DWARF-style unwinder or row semantics.

### R7: `checkCFI_sound`

- **Kind:** theorem.  **Tier:** T1 (folklore made precise).  **Depth:** substantive.
- **Plain claim:** If the decidable checker checkCFI accepts a CFI program for a function - it infers one abstract entry state per block by forward propagation with join, re-checks the entry state and every CFG edge, and checks that the program's row at the linear address of every PC of every annotated block is entailed by the abstract state there - then the program is TableCorrect.
- **Key definitions:** `checkCFI`, `checkWith`, `inferEntries`, `annSoundB`, `rowsOK`, `entails`, `TableCorrect`.

Lean statement (proof elided as `…`):

`Toy.CFI.checkCFI_sound` (`lean/ToyCFI/Checker.lean:178-181`):

```lean
-- lean/ToyCFI/Checker.lean:178-181
/-- **Checker soundness.** If `checkCFI f prog = true` then the CFI program is
correct at every reachable PC of every CFG path, for every caller and memory. -/
theorem checkCFI_sound {f : Func} {prog : List CFIInst} (h : checkCFI f prog = true) :
    TableCorrect f prog := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `h : checkCFI f prog = true` | the checker accepts the program | tight: counterexample `checkCFI_sound_fails_without_check`; witness class: a single concrete program, `naiveCFI coldFn (inferredAnn coldFn)` for the 3-block function `coldFn` in layout 0, 1, 2, which `checkCFI` rejects and which is not `TableCorrect` |

**Depth:** substantive. Soundness of the transfer function, of `leqA` and of `entails` with respect to `Inv`, combined by `reach_inv_of_annSound` and `checkWith_sound`.

**Non-vacuity witness:** checkCFI accepts the generator's program for coldFn and rejects the naive one. (`checkCFI_examples`)

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.checkCFI_sound_fails_without_check` (`lean/ToyCFI/Examples.lean:184-188`):

```lean
-- lean/ToyCFI/Examples.lean:184-188
/-- Tightness of `h : checkCFI f prog = true` in checker soundness: the naive
program for `coldFn` is rejected and is incorrect. -/
theorem checkCFI_sound_fails_without_check :
    checkCFI coldFn (naiveCFI coldFn (inferredAnn coldFn)) = false ∧
      ¬ TableCorrect coldFn (naiveCFI coldFn (inferredAnn coldFn)) := …
```

`Toy.CFI.checkCFI_examples` (`lean/ToyCFI/Examples.lean:180-182`):

```lean
-- lean/ToyCFI/Examples.lean:180-182
theorem checkCFI_examples :
    checkCFI coldFn (genCFI coldFn (inferredAnn coldFn)) = true ∧
      checkCFI coldFn (naiveCFI coldFn (inferredAnn coldFn)) = false := …
```

</details>

**Prior art.**

- T. Bastian, S. Kell, F. Zappa Nardelli, 'Reliable and fast DWARF-based stack unwinding', Proc. ACM Program. Lang. 3(OOPSLA), Article 146, October 2019, doi:10.1145/3360572. §2.2 (pp. 146:8-146:12; the passages summarized here are on pp. 146:9-146:11): unwind rows are synthesized by forward propagation along CFG edges, relying on stack offsets being invariant at merge points; with variable-size stack allocation compilers fall back to a base-pointer register; if different rows reach a merge point the tool aborts (a lossy merge is enabled only for terminal blocks). Appendix A (pp. 146:21-146:23): remember_state pushes 'the state of all the registers of this row', and restore(reg) is not supported (p. 146:21); the formal interpretation keeps a state-saving stack of rows (Row*, p. 146:22; Table 5, p. 146:23). The paper contains no mechanized proof.
- LLVM CFIInstrInserter pass, llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, llvm/lib/CodeGen/CFIInstrInserter.cpp: header comment (lines 9-17) - verifies that the outgoing CFA information of predecessors matches the incoming information of successors and inserts CFI instructions at block beginnings when 'a non-linear layout of blocks' leaves an incorrect rule. Besides the CFA offset and register it tracks callee-saved register save locations (CSRSavedLocation with kinds Register and CFAOffset, CSRLocMap, IncomingCSRSaved/OutgoingCSRSaved; lines 64-162; propagated along CFG edges, line 408), repairs them at block beginnings with .cfi_restore, .cfi_offset and .cfi_register (insertCFIInstrs, lines 415-511; a block that begins a new section gets a full def_cfa plus the callee-saved moves, lines 431-470), and reports CFG-edge CFA and callee-saved mismatches in verify (lines 545-571; CFA mismatches into blocks with no successors that are not return blocks are exempt, lines 553-557). It requires a single save location per callee-saved register ('Different saved locations for the same CSR', lines 366-369). In builds with assertions (#ifndef NDEBUG) it accepts cfi_remember_state/cfi_restore_state only as balanced depth-1 pairs inside one basic block and otherwise reports 'Support for cfi_remember_state not implemented!' (lines 316-339, 375-381); in builds without assertions its analysis ignores both instructions. Derived (modeling bridge): this is the explicit re-definition alternative; like the toy genCFI it repairs both the CFA rule and callee-saved register rules at layout boundaries, but it never places a remember/restore pair across blocks. It was not compared against the toy's output.
- DWARF Debugging Information Format Committee, DWARF Debugging Information Format, Version 5 (February 13, 2017), https://dwarfstd.org/doc/DWARF5.pdf. §2.5.1.2 DW_OP_fbreg (an offset from the address given by DW_AT_frame_base); §2.5.1.3 item 15 (printed page 33; PDF page 51) DW_OP_call_frame_cfa (pushes the CFA obtained from the call frame information; computing DW_AT_frame_base from registers would 'in some cases ... require an extensive location list because the values of the registers used in computing the CFA change during a subroutine'). §6.4.2.4 (printed page 181; PDF page 199) DW_CFA_remember_state / DW_CFA_restore_state ('push the set of rules for every register onto an implicit stack' / 'pop the set of rules off the implicit stack and place them in the current row') in the wording quoted by DWARF issue 230103.1. The toy's register rules and CFA-definition instructions are modeled on the pinned LLVM libunwind implementation (libunwind/src/DwarfParser.hpp and DwarfInstructions.hpp at llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc) rather than on the text of §6.4.1 and §6.4.2.2.
- G. A. Kildall, 'A unified approach to global program optimization', Proc. 1st ACM SIGACT-SIGPLAN Symposium on Principles of Programming Languages (POPL 1973), pp. 194-206, doi:10.1145/512927.512945: iterative dataflow analysis over a semilattice along CFG edges until a fixed point. Derived (modeling bridge): annSoundB is a post-fixpoint check of this kind for the toy's abstract frame-state domain; the toy does not use Kildall's algorithm for the soundness argument, only the post-fixpoint property.
- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107-115, 2009, doi:10.1145/1538788.1538814; CompCert (AbsInt/CompCert commit 2685140bf72c959446981fb99b5e44a8975021bc) backend/Kildall.v mechanizes generic Kildall-style dataflow solvers in Coq: Theorem fixpoint_solution (line 661) states that the solver's result satisfies the dataflow inequations along every CFG edge, and Theorem fixpoint_invariant (line 741) that a property preserved by join and transfer holds of the result. Derived (modeling bridge): reach_inv_of_annSound is the corresponding 'post-fixpoint annotation over-approximates every reachable state' step, which CompCert proves separately inside each client analysis rather than in Kildall.v.

**Design question:** What must a CFI emitter guarantee for a linear layout of a CFG whose blocks are not placed in control-flow order, and which checks of the emitted table are sound?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- LLVM CFIInstrInserter (llvm/llvm-project 701f926a): this is the explicit re-definition alternative; like the toy genCFI it repairs both the CFA rule and callee-saved register rules at layout boundaries, but it never places a remember/restore pair across blocks. It was not compared against the toy's output.
- Kildall (1973): annSoundB is a post-fixpoint check of this kind for the toy's abstract frame-state domain; the toy does not use Kildall's algorithm for the soundness argument, only the post-fixpoint property.
- Leroy (2009) / CompCert 2685140b: reach_inv_of_annSound is the corresponding 'post-fixpoint annotation over-approximates every reachable state' step, which CompCert proves separately inside each client analysis rather than in Kildall.v.

### R7b: `checkCFI_incomplete`

- **Kind:** counterexample.  **Tier:** T1 (folklore made precise).  **Depth:** shallow.
- **Plain claim:** For incFn (t1 anchors the CFA, a loop moves sp, then fp is stored to and reloaded from [sp]) the table incCFI (CFA = t1 + 0, all registers same) is TableCorrect, yet checkCFI rejects it.
- **Key definitions:** `incFn`, `incCFI`, `checkCFI`, `TableCorrect`.

Lean statement (proof elided as `…`):

`Toy.CFI.checkCFI_incomplete` (`lean/ToyCFI/Incomplete.lean:30-33`):

```lean
-- lean/ToyCFI/Incomplete.lean:30-33
/-- **Incompleteness witness.** `incCFI` is correct for `incFn`, yet `checkCFI`
rejects it: after `restore fp 0` through an unknown `sp`, the abstract state
records `fp` as unknown although it still holds the caller's value. -/
theorem checkCFI_incomplete : TableCorrect incFn incCFI ∧ checkCFI incFn incCFI = false := …
```

**Hypothesis ledger.**

No hypotheses: the statement is about concrete objects.

**Depth:** shallow. Correctness of `incCFI` over all reachable states of `incFn` plus a concrete evaluation of `checkCFI`.

**Non-vacuity witness:** The statement itself exhibits both facts. (`checkCFI_incomplete`)

**Prior art.**

- T. Bastian, S. Kell, F. Zappa Nardelli, 'Reliable and fast DWARF-based stack unwinding', Proc. ACM Program. Lang. 3(OOPSLA), Article 146, October 2019, doi:10.1145/3360572. §2.2 (pp. 146:8-146:12; the passages summarized here are on pp. 146:9-146:11): unwind rows are synthesized by forward propagation along CFG edges, relying on stack offsets being invariant at merge points; with variable-size stack allocation compilers fall back to a base-pointer register; if different rows reach a merge point the tool aborts (a lossy merge is enabled only for terminal blocks). Appendix A (pp. 146:21-146:23): remember_state pushes 'the state of all the registers of this row', and restore(reg) is not supported (p. 146:21); the formal interpretation keeps a state-saving stack of rows (Row*, p. 146:22; Table 5, p. 146:23). The paper contains no mechanized proof.

**Design question:** What must a CFI emitter guarantee for a linear layout of a CFG whose blocks are not placed in control-flow order, and which checks of the emitted table are sound?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- General: a checker of real unwind tables built on the same abstract domain would reject tables that rely on store-to-load forwarding through untracked addresses (derived from the single toy instance `checkCFI_incomplete`; not proved here for other tables).

### R7c: `reach_inv_of_annSound`

- **Kind:** theorem.  **Tier:** T0 (re-derivation of a known result).  **Depth:** shallow.
- **Plain claim:** Under a sound block annotation, every state reachable at offset k of block b satisfies the abstract state obtained by running the abstract transfer function over the first k operations from b's annotated entry state; the CFI program plays no role.
- **Key definitions:** `annSoundB`, `absAt`, `absRun`, `xfer`, `Inv`, `Reach`.

Lean statement (proof elided as `…`):

`Toy.CFI.reach_inv_of_annSound` (`lean/ToyCFI/Checker.lean:115-119`):

```lean
-- lean/ToyCFI/Checker.lean:115-119
/-- Under a sound annotation, every reachable state satisfies the abstract state
of its PC.  (The CFI program plays no role here.) -/
theorem reach_inv_of_annSound {f : Func} {ann : Ann} (hs : annSoundB f ann = true)
    {c : Caller} {m : Int → Int} {b k : Nat} {st : MState} (h : Reach f c m b k st) :
    ∃ A, ann b = some A ∧ Inv (absAt f A b k) c st := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hs : annSoundB f ann = true` | entry and edge consistency | tight: counterexample `reach_inv_fails_without_annSound`; witness class: the concrete 3-block function `coldFn` with the hand-written unsound annotation `coldBadAnn`; a reachable state at the cold block's first PC (2, 0) violates the annotated abstract state |
| `h : Reach f c m b k st` | the state is actually reachable at (b, k) along a CFG path | tight: counterexample `reach_inv_fails_without_reach`; witness class: an unreachable concrete state at `coldFn`'s entry PC (0, 0) (caller CFA 100, sp = 99), with the sound inferred annotation `inferredAnn coldFn`, which that state violates |

**Depth:** shallow. Induction over `Reach` using transfer-function soundness and `leqA` soundness.

**Non-vacuity witness:** coldFn with its inferred (sound) annotation and the reachable state at the cold block's entry satisfy both hypotheses. (`reach_inv_of_annSound_nonvacuity`)

<details><summary>Counterexample, witness and control statements (verbatim)</summary>

`Toy.CFI.reach_inv_fails_without_annSound` (`lean/ToyCFI/Generic.lean:365-371`):

```lean
-- lean/ToyCFI/Generic.lean:365-371
/-- Tightness of soundness for `reach_inv_of_annSound`: with the unsound
`coldBadAnn`, a reachable state at the cold block violates the annotated
abstract state. -/
theorem reach_inv_fails_without_annSound :
    annSoundB coldFn coldBadAnn = false ∧
      ∃ c m st A, Reach coldFn c m 2 0 st ∧ coldBadAnn 2 = some A ∧
        ¬ Inv (absAt coldFn A 2 0) c st := …
```

`Toy.CFI.reach_inv_fails_without_reach` (`lean/ToyCFI/Examples.lean:197-204`):

```lean
-- lean/ToyCFI/Examples.lean:197-204
/-- Tightness of `h : Reach f c m b k st` in `reach_inv_of_annSound`: with the
sound inferred annotation of `coldFn`, a state at the entry PC whose `sp` is not
the CFA is not reachable, and it violates the annotated abstract state. -/
theorem reach_inv_fails_without_reach :
    let c : Caller := ⟨100, ⟨0, 0, 0, 0⟩⟩
    let st : MState := ⟨⟨99, 0, 0, 0⟩, fun _ => 0⟩
    annSoundB coldFn (inferredAnn coldFn) = true ∧ ¬ Reach coldFn c (fun _ => 0) 0 0 st ∧
      ¬ (∃ A, inferredAnn coldFn 0 = some A ∧ Inv (absAt coldFn A 0 0) c st) := …
```

`Toy.CFI.reach_inv_of_annSound_nonvacuity` (`lean/ToyCFI/Examples.lean:191-194`):

```lean
-- lean/ToyCFI/Examples.lean:191-194
/-- Non-vacuity of `reach_inv_of_annSound`: both hypotheses (a sound annotation
and a reachable state) hold for `coldFn` at the cold block's entry. -/
theorem reach_inv_of_annSound_nonvacuity (c : Caller) (m : Int → Int) :
    annSoundB coldFn (inferredAnn coldFn) = true ∧ Reach coldFn c m 2 0 (coldStCold c m) := …
```

</details>

**Prior art.**

- G. A. Kildall, 'A unified approach to global program optimization', Proc. 1st ACM SIGACT-SIGPLAN Symposium on Principles of Programming Languages (POPL 1973), pp. 194-206, doi:10.1145/512927.512945: iterative dataflow analysis over a semilattice along CFG edges until a fixed point. Derived (modeling bridge): annSoundB is a post-fixpoint check of this kind for the toy's abstract frame-state domain; the toy does not use Kildall's algorithm for the soundness argument, only the post-fixpoint property.
- X. Leroy, 'Formal verification of a realistic compiler', Commun. ACM 52(7):107-115, 2009, doi:10.1145/1538788.1538814; CompCert (AbsInt/CompCert commit 2685140bf72c959446981fb99b5e44a8975021bc) backend/Kildall.v mechanizes generic Kildall-style dataflow solvers in Coq: Theorem fixpoint_solution (line 661) states that the solver's result satisfies the dataflow inequations along every CFG edge, and Theorem fixpoint_invariant (line 741) that a property preserved by join and transfer holds of the result. Derived (modeling bridge): reach_inv_of_annSound is the corresponding 'post-fixpoint annotation over-approximates every reachable state' step, which CompCert proves separately inside each client analysis rather than in Kildall.v; this mechanization is why reach_inv_of_annSound is tiered T0 (re-derivation).
- T. Bastian, S. Kell, F. Zappa Nardelli, 'Reliable and fast DWARF-based stack unwinding', Proc. ACM Program. Lang. 3(OOPSLA), Article 146, October 2019, doi:10.1145/3360572. §2.2 (pp. 146:8-146:12; the passages summarized here are on pp. 146:9-146:11): unwind rows are synthesized by forward propagation along CFG edges, relying on stack offsets being invariant at merge points; with variable-size stack allocation compilers fall back to a base-pointer register; if different rows reach a merge point the tool aborts (a lossy merge is enabled only for terminal blocks). Appendix A (pp. 146:21-146:23): remember_state pushes 'the state of all the registers of this row', and restore(reg) is not supported (p. 146:21); the formal interpretation keeps a state-saving stack of rows (Row*, p. 146:22; Table 5, p. 146:23). The paper contains no mechanized proof.

**Design question:** What must a CFI emitter guarantee for a linear layout of a CFG whose blocks are not placed in control-flow order, and which checks of the emitted table are sound?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge)

Each item below is reasoning that connects the toy statement to a real system; none of it is kernel-checked. The source is named first; its exact record is under **Evidence**.

- Kildall (1973): annSoundB is a post-fixpoint check of this kind for the toy's abstract frame-state domain; the toy does not use Kildall's algorithm for the soundness argument, only the post-fixpoint property.
- Leroy (2009) / CompCert 2685140b: reach_inv_of_annSound is the corresponding 'post-fixpoint annotation over-approximates every reachable state' step, which CompCert proves separately inside each client analysis rather than in Kildall.v; this mechanization is why reach_inv_of_annSound is tiered T0 (re-derivation).
- General: this is the standard post-fixpoint soundness step of forward dataflow analysis (Kildall, 1973), here for the toy's frame-state domain.

### Auxiliary lemmas, examples and objects cited by name

Every package-local declaration that this report cites by name and does not quote elsewhere is quoted here
verbatim, grouped by file in source order (each theorem's complete statement up to its top-level proof `:=`, the proof elided as `:= …`). None of these declarations is a card
result; their statements are given so that each citation can be read without the sources.

<details><summary>Auxiliary statements (verbatim)</summary>

**`lean/ToyCFI/Abstract.lean`**

`Toy.CFI.xfer_sound` (`lean/ToyCFI/Abstract.lean:175-177`):

```lean
-- lean/ToyCFI/Abstract.lean:175-177
/-- The abstract transfer function is sound for the concrete step. -/
theorem xfer_sound {A : AState} {c : Caller} {st : MState} (op : Op) (h : Inv A c st) :
    Inv (xfer A op) c (step st op) := …
```

`Toy.CFI.absInit_sound` (`lean/ToyCFI/Abstract.lean:210-210`):

```lean
-- lean/ToyCFI/Abstract.lean:210-210
theorem absInit_sound (c : Caller) (m : Int → Int) : Inv absInit c (entryState c m) := …
```

`Toy.CFI.leqA_refl` (`lean/ToyCFI/Abstract.lean:247-248`):

```lean
-- lean/ToyCFI/Abstract.lean:247-248
/-- `leqA` is reflexive. -/
theorem leqA_refl (A : AState) : leqA A A = true := …
```

**`lean/ToyCFI/Checker.lean`**

`Toy.CFI.checkWith_sound` (`lean/ToyCFI/Checker.lean:156-158`):

```lean
-- lean/ToyCFI/Checker.lean:156-158
/-- Soundness of the checker relative to any annotation. -/
theorem checkWith_sound {f : Func} {prog : List CFIInst} {ann : Ann}
    (h : checkWith f prog ann = true) : TableCorrect f prog := …
```

**`lean/ToyCFI/ColdBlock.lean`**

`Toy.CFI.coldFn_reach_ret` (`lean/ToyCFI/ColdBlock.lean:26-26`):

```lean
-- lean/ToyCFI/ColdBlock.lean:26-26
theorem coldFn_reach_ret (c : Caller) (m : Int → Int) : Reach coldFn c m 1 2 (coldStRet c m) := …
```

`Toy.CFI.coldStCold_regs` (`lean/ToyCFI/ColdBlock.lean:40-41`):

```lean
-- lean/ToyCFI/ColdBlock.lean:40-41
theorem coldStCold_regs (c : Caller) (m : Int → Int) :
    (coldStCold c m).regs = ⟨c.cfa - 1, c.cfa - 1, c.regs.s1, c.regs.t1⟩ := …
```

`Toy.CFI.coldFn_annSound` (`lean/ToyCFI/ColdBlock.lean:102-103`):

```lean
-- lean/ToyCFI/ColdBlock.lean:102-103
/-- The inferred annotation of `coldFn` is sound. -/
theorem coldFn_annSound : annSoundB coldFn (inferredAnn coldFn) = true := …
```

`Toy.CFI.naiveCFI_coldFn_not_tableCorrect` (`lean/ToyCFI/ColdBlock.lean:127-127`):

```lean
-- lean/ToyCFI/ColdBlock.lean:127-127
theorem naiveCFI_coldFn_not_tableCorrect : ¬ TableCorrect coldFn (naiveCFI coldFn (inferredAnn coldFn)) := …
```

`Toy.CFI.naiveCFI_coldFnFallthrough_tableCorrect` (`lean/ToyCFI/ColdBlock.lean:130-133`):

```lean
-- lean/ToyCFI/ColdBlock.lean:130-133
/-- Positive control (layout): with the CFG-order layout `0, 2, 1` the same naive
emitter is correct. -/
theorem naiveCFI_coldFnFallthrough_tableCorrect :
    TableCorrect coldFnFallthrough (naiveCFI coldFnFallthrough (inferredAnn coldFnFallthrough)) := …
```

`Toy.CFI.genCFI_coldFn_tableCorrect` (`lean/ToyCFI/ColdBlock.lean:136-139`):

```lean
-- lean/ToyCFI/ColdBlock.lean:136-139
/-- Positive control (compensation): for the layout `0, 1, 2`, the generator's
program, which remembers the row at the start of the epilogue block and restores
it at the start of the cold block, is correct. -/
theorem genCFI_coldFn_tableCorrect : TableCorrect coldFn (genCFI coldFn (inferredAnn coldFn)) := …
```

`Toy.CFI.genCFI_coldFn_eq` (`lean/ToyCFI/ColdBlock.lean:142-146`):

```lean
-- lean/ToyCFI/ColdBlock.lean:142-146
/-- The generator's program for `coldFn`, verbatim. -/
theorem genCFI_coldFn_eq : genCFI coldFn (inferredAnn coldFn) =
    [.advanceLoc 1, .defCfaOffset 1, .advanceLoc 1, .defCfaRegister .fp, .offset .fp (-1),
     .advanceLoc 1, .rememberState, .advanceLoc 1, .advanceLoc 1, .defCfa .sp 0, .restore .fp,
     .advanceLoc 1, .restoreState, .advanceLoc 1] := …
```

`Toy.CFI.coldExplicitCFI_tableCorrect` (`lean/ToyCFI/ColdBlock.lean:163-163`):

```lean
-- lean/ToyCFI/ColdBlock.lean:163-163
theorem coldExplicitCFI_tableCorrect : TableCorrect coldFn coldExplicitCFI := …
```

**`lean/ToyCFI/Examples.lean`**

`Toy.CFI.step_push_example` (`lean/ToyCFI/Examples.lean:16-19`):

```lean
-- lean/ToyCFI/Examples.lean:16-19
/-- `push fp` decrements `sp` and stores the old `fp` at the new `sp`. -/
theorem step_push_example :
    let st : MState := ⟨⟨100, 7, 0, 0⟩, fun _ => 0⟩
    (step st (.push .fp)).regs.get .sp = 99 ∧ (step st (.push .fp)).mem 99 = 7 := …
```

`Toy.CFI.step_push_moves_sp` (`lean/ToyCFI/Examples.lean:21-24`):

```lean
-- lean/ToyCFI/Examples.lean:21-24
/-- Negative: `push` is not frame-neutral. -/
theorem step_push_moves_sp :
    let st : MState := ⟨⟨100, 7, 0, 0⟩, fun _ => 0⟩
    (step st (.push .fp)).regs.get .sp ≠ st.regs.get .sp := …
```

`Toy.CFI.pcOf_cold_block_example` (`lean/ToyCFI/Examples.lean:28-28`):

```lean
-- lean/ToyCFI/Examples.lean:28-28
theorem pcOf_cold_block_example : coldFn.pcOf 2 0 = some 6 := …
```

`Toy.CFI.pcOf_missing_block_example` (`lean/ToyCFI/Examples.lean:29-30`):

```lean
-- lean/ToyCFI/Examples.lean:29-30
/-- Negative: a block absent from the layout has no address. -/
theorem pcOf_missing_block_example : coldFnMissing.pcOf 2 0 = none := …
```

`Toy.CFI.not_reach_coldFn_cold_with_sp_eq_cfa` (`lean/ToyCFI/Examples.lean:34-36`):

```lean
-- lean/ToyCFI/Examples.lean:34-36
/-- Negative: at the cold block's first PC, `sp` is never the CFA. -/
theorem not_reach_coldFn_cold_with_sp_eq_cfa (c : Caller) (m : Int → Int) (st : MState)
    (hsp : st.regs.get .sp = c.cfa) : ¬ Reach coldFn c m 2 0 st := …
```

`Toy.CFI.rowAt_example` (`lean/ToyCFI/Examples.lean:48-53`):

```lean
-- lean/ToyCFI/Examples.lean:48-53
/-- Instructions before the first `advanceLoc` apply at address 0; those after
`advanceLoc 1` apply from address 1 on. -/
theorem rowAt_example :
    rowAt? [.defCfaOffset 2, .advanceLoc 1, .defCfaRegister .fp] 0 = some ⟨.sp, 2, RegFile.const .same⟩ ∧
      rowAt? [.defCfaOffset 2, .advanceLoc 1, .defCfaRegister .fp] 1 =
        some ⟨.fp, 2, RegFile.const .same⟩ := …
```

`Toy.CFI.rowAt_restoreState_restores_cfa` (`lean/ToyCFI/Examples.lean:55-58`):

```lean
-- lean/ToyCFI/Examples.lean:55-58
/-- `restoreState` restores the CFA rule as well as the register rules. -/
theorem rowAt_restoreState_restores_cfa :
    rowAt? [.defCfa .fp 1, .offset .fp (-1), .rememberState, .defCfa .sp 0, .restore .fp,
      .restoreState] 0 = some ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ := …
```

`Toy.CFI.rowAt_underflow_none` (`lean/ToyCFI/Examples.lean:60-61`):

```lean
-- lean/ToyCFI/Examples.lean:60-61
/-- Negative: `restoreState` on an empty stack has no row. -/
theorem rowAt_underflow_none : rowAt? [.restoreState] 0 = none := …
```

`Toy.CFI.recovers_cold_entry_example` (`lean/ToyCFI/Examples.lean:65-67`):

```lean
-- lean/ToyCFI/Examples.lean:65-67
/-- Positive: the frame-on row recovers the caller at the cold block's first PC. -/
theorem recovers_cold_entry_example (c : Caller) (m : Int → Int) :
    Recovers ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ c (coldStCold c m) := …
```

`Toy.CFI.not_recovers_cold_entry_initRow` (`lean/ToyCFI/Examples.lean:77-79`):

```lean
-- lean/ToyCFI/Examples.lean:77-79
/-- Negative: the post-epilogue row does not recover the caller there. -/
theorem not_recovers_cold_entry_initRow (c : Caller) (m : Int → Int) :
    ¬ Recovers initRow c (coldStCold c m) := …
```

`Toy.CFI.not_inv_absInit_example` (`lean/ToyCFI/Examples.lean:87-89`):

```lean
-- lean/ToyCFI/Examples.lean:87-89
/-- Negative: the entry abstract state rejects a state whose `sp` is not the CFA. -/
theorem not_inv_absInit_example :
    ¬ Inv absInit ⟨100, ⟨0, 0, 0, 0⟩⟩ ⟨⟨99, 0, 0, 0⟩, fun _ => 0⟩ := …
```

`Toy.CFI.entails_example` (`lean/ToyCFI/Examples.lean:100-101`):

```lean
-- lean/ToyCFI/Examples.lean:100-101
theorem entails_example : entails coldEntryA ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ = true ∧
    entails coldEntryA ⟨.sp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ = true := …
```

`Toy.CFI.not_entails_example` (`lean/ToyCFI/Examples.lean:103-105`):

```lean
-- lean/ToyCFI/Examples.lean:103-105
/-- Negative: the post-epilogue row, and a row claiming `fp` is unchanged. -/
theorem not_entails_example : entails coldEntryA initRow = false ∧
    entails coldEntryA ⟨.fp, 1, RegFile.const .same⟩ = false := …
```

`Toy.CFI.leqA_example` (`lean/ToyCFI/Examples.lean:109-110`):

```lean
-- lean/ToyCFI/Examples.lean:109-110
theorem leqA_example :
    leqA coldEntryA { coldEntryA with regs := coldEntryA.regs.set .sp .unknown } = true := …
```

`Toy.CFI.not_leqA_example` (`lean/ToyCFI/Examples.lean:112-114`):

```lean
-- lean/ToyCFI/Examples.lean:112-114
/-- Negative: the less precise state does not entail the more precise one. -/
theorem not_leqA_example :
    leqA { coldEntryA with regs := coldEntryA.regs.set .sp .unknown } coldEntryA = false := …
```

`Toy.CFI.leqA_shadowed_examples` (`lean/ToyCFI/Examples.lean:122-126`):

```lean
-- lean/ToyCFI/Examples.lean:122-126
/-- `leqA` ignores shadowed entries: it is reflexive on `shadowedInit` and
`absInit` and `shadowedInit` are mutually `leqA`-related. -/
theorem leqA_shadowed_examples :
    leqA shadowedInit shadowedInit = true ∧ leqA absInit shadowedInit = true ∧
      leqA shadowedInit absInit = true := …
```

`Toy.CFI.stateRecoverableB_examples` (`lean/ToyCFI/Examples.lean:130-136`):

```lean
-- lean/ToyCFI/Examples.lean:130-136
/-- Positive: the cold block's entry state is recoverable (`fp` is CFA-relative,
`fp`'s caller value is saved at `CFA - 1`).  Negative: with `sp` and `fp`
unknown no register is CFA-relative. -/
theorem stateRecoverableB_examples :
    stateRecoverableB coldEntryA = true ∧
      stateRecoverableB { coldEntryA with regs := ⟨.unknown, .unknown, .callerOf .s1, .callerOf .t1⟩ }
        = false := …
```

`Toy.CFI.ruleChoice_shadowed_example` (`lean/ToyCFI/Examples.lean:145-147`):

```lean
-- lean/ToyCFI/Examples.lean:145-147
/-- `ruleChoice` skips shadowed entries: it picks offset `-2` for `fp`, not the
stale `-1`. -/
theorem ruleChoice_shadowed_example : ruleChoice shadowedB .fp = .offset (-2) := …
```

`Toy.CFI.genCFI_shadowedClobberFn_tableCorrect` (`lean/ToyCFI/Examples.lean:161-169`):

```lean
-- lean/ToyCFI/Examples.lean:161-169
/-- Positive instance of generator correctness on a user-supplied annotation
with shadowed slot entries: the hypotheses hold, and the generated table (which
recovers `fp` from `CFA - 2`) is correct. -/
theorem genCFI_shadowedClobberFn_tableCorrect :
    LayoutCovers shadowedClobberFn ∧ annSoundB shadowedClobberFn shadowedAnn = true ∧
      annRecoverableB shadowedClobberFn shadowedAnn = true ∧
      rowAt? (genCFI shadowedClobberFn shadowedAnn) 4 =
        some ⟨.fp, 2, ⟨.same, .offset (-2), .same, .same⟩⟩ ∧
      TableCorrect shadowedClobberFn (genCFI shadowedClobberFn shadowedAnn) := …
```

`Toy.CFI.contains_examples` (`lean/ToyCFI/Examples.lean:215-216`):

```lean
-- lean/ToyCFI/Examples.lean:215-216
theorem contains_examples : (⟨0, 4, some 1⟩ : CallSite).contains 3 ∧
    ¬ (⟨0, 4, some 1⟩ : CallSite).contains 4 := …
```

`Toy.CFI.uniqueAt_examples` (`lean/ToyCFI/Examples.lean:218-218`):

```lean
-- lean/ToyCFI/Examples.lean:218-218
theorem uniqueAt_examples : UniqueAt lsdaAdjacent 4 ∧ ¬ UniqueAt lsdaOverlap 7 := …
```

`Toy.CFI.nonOverlapping_examples` (`lean/ToyCFI/Examples.lean:222-222`):

```lean
-- lean/ToyCFI/Examples.lean:222-222
theorem nonOverlapping_examples : NonOverlapping lsdaAdjacent ∧ ¬ NonOverlapping lsdaOverlap := …
```

`Toy.CFI.sortedByStart_examples` (`lean/ToyCFI/Examples.lean:226-226`):

```lean
-- lean/ToyCFI/Examples.lean:226-226
theorem sortedByStart_examples : SortedByStart lsdaAdjacent ∧ ¬ SortedByStart lsdaUnsorted := …
```

`Toy.CFI.frameAction_examples` (`lean/ToyCFI/Examples.lean:231-234`):

```lean
-- lean/ToyCFI/Examples.lean:231-234
theorem frameAction_examples :
    frameAction outerFrame = .handle 7 ∧ frameAction innerFrame = .skip ∧
      frameAction innerFrameTerm = .terminate ∧
      frameAction { outerFrame with lsda := some [⟨1, 2, none⟩] } = .skip := …
```

`Toy.CFI.cfaBaseSafe_examples` (`lean/ToyCFI/Examples.lean:236-238`):

```lean
-- lean/ToyCFI/Examples.lean:236-238
theorem cfaBaseSafe_examples :
    CfaBaseSafe ⟨.sp, 2, RegFile.const .same⟩ ∧ CfaBaseSafe ⟨.fp, 1, RegFile.const .same⟩ ∧
      ¬ CfaBaseSafe ⟨.t1, 0, RegFile.const .same⟩ := …
```

`Toy.CFI.agree_examples` (`lean/ToyCFI/Examples.lean:242-242`):

```lean
-- lean/ToyCFI/Examples.lean:242-242
theorem agree_examples : Agree innerSt innerSt ∧ ¬ Agree innerStBad innerSt := …
```

`Toy.CFI.slotsPreserved_examples` (`lean/ToyCFI/Examples.lean:248-252`):

```lean
-- lean/ToyCFI/Examples.lean:248-252
/-- `SlotsPreserved`: the middle frame's slot survives when nothing overwrites
it, and is reported clobbered in the three-frame counterexample. -/
theorem slotsPreserved_examples :
    SlotsPreserved ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ middleSt.mem middleSt ∧
      ¬ SlotsPreserved ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ clobberSt.mem middleSt := …
```

**`lean/ToyCFI/Generator.lean`**

`Toy.CFI.entails_rowOf_of_stateRecoverableB` (`lean/ToyCFI/Generator.lean:195-198`):

```lean
-- lean/ToyCFI/Generator.lean:195-198
/-- `rowOf` is complete for recoverability: a recoverable state entails its
derived row. -/
theorem entails_rowOf_of_stateRecoverableB {A : AState} (hs : stateRecoverableB A = true) :
    entails A (rowOf A) = true := …
```

`Toy.CFI.stateRecoverableB_iff_exists_entails` (`lean/ToyCFI/Generator.lean:209-212`):

```lean
-- lean/ToyCFI/Generator.lean:209-212
/-- **Recoverability is emitter-independent.** `stateRecoverableB A` holds iff
some row is entailed by `A`. -/
theorem stateRecoverableB_iff_exists_entails (A : AState) :
    stateRecoverableB A = true ↔ ∃ R, entails A R = true := …
```

`Toy.CFI.annRecoverableB_iff` (`lean/ToyCFI/Generator.lean:232-237`):

```lean
-- lean/ToyCFI/Generator.lean:232-237
/-- Unfolded meaning of `annRecoverableB`: at every PC of every annotated
in-range block, some row is entailed by the abstract state there. -/
theorem annRecoverableB_iff (f : Func) (ann : Ann) :
    annRecoverableB f ann = true ↔
      ∀ b < f.blocks.length, ∀ A, ann b = some A → ∀ k < (f.blockOps b).length,
        ∃ R, entails (absAt f A b k) R = true := …
```

**`lean/ToyCFI/Generic.lean`**

`Toy.CFI.rowAt_genCFI_eq_rowOf` (`lean/ToyCFI/Generic.lean:261-266`):

```lean
-- lean/ToyCFI/Generic.lean:261-266
/-- **Encoder lemma.** At the linear address of every PC of every annotated
block that appears in the layout, the program emitted by `genCFI` has exactly
the row derived from the abstract state at that PC. -/
theorem rowAt_genCFI_eq_rowOf {f : Func} {ann : Ann} {b k pc0 : Nat} {A : AState}
    (hst : f.blockStart b = some pc0) (hA : ann b = some A) (hk : k < (f.blockOps b).length) :
    rowAt? (genCFI f ann) (pc0 + k) = some (rowOf (absAt f A b k)) := …
```

`Toy.CFI.coldFn_layoutCovers` (`lean/ToyCFI/Generic.lean:303-303`):

```lean
-- lean/ToyCFI/Generic.lean:303-303
theorem coldFn_layoutCovers : LayoutCovers coldFn := …
```

**`lean/ToyCFI/LSDA.lean`**

`Toy.CFI.lookupScan_eq_notFound_of_none_contains` (`lean/ToyCFI/LSDA.lean:135-138`):

```lean
-- lean/ToyCFI/LSDA.lean:135-138
/-- The early-exit scan reports "not found" when no entry contains `pc` (no
hypothesis on the table). -/
theorem lookupScan_eq_notFound_of_none_contains (t : LSDA) (pc : Nat)
    (h : ∀ e ∈ t, ¬ e.contains pc) : lookupScan t pc = .notFound := …
```

`Toy.CFI.duplicate_entries_uniqueAt_not_nonOverlapping` (`lean/ToyCFI/LSDA.lean:244-249`):

```lean
-- lean/ToyCFI/LSDA.lean:244-249
/-- `UniqueAt` compares values: a table holding the same entry twice is
`UniqueAt` at every `pc` but not `NonOverlapping`, so even
`∀ pc, UniqueAt t pc` does not imply `NonOverlapping t`. -/
theorem duplicate_entries_uniqueAt_not_nonOverlapping :
    let e : CallSite := ⟨0, 4, some 1⟩
    (∀ pc, UniqueAt [e, e] pc) ∧ ¬ NonOverlapping [e, e] := …
```

**`lean/ToyCFI/Machine.lean`**

`Toy.CFI.Reach.layout_irrelevant` (`lean/ToyCFI/Machine.lean:205-209`):

```lean
-- lean/ToyCFI/Machine.lean:205-209
/-- Reachability ignores the layout: it depends only on the blocks (operations
and successors). -/
theorem Reach.layout_irrelevant (bs : List Block) (l₁ l₂ : List Nat)
    {c : Caller} {m : Int → Int} {b k : Nat} {st : MState} :
    Reach ⟨bs, l₁⟩ c m b k st ↔ Reach ⟨bs, l₂⟩ c m b k st := …
```

**`lean/ToyCFI/Merge.lean`**

`Toy.CFI.mergeFn_reach_via1` (`lean/ToyCFI/Merge.lean:21-21`):

```lean
-- lean/ToyCFI/Merge.lean:21-21
theorem mergeFn_reach_via1 (c : Caller) (m : Int → Int) : Reach mergeFn c m 3 0 (mergeStVia1 c m) := …
```

`Toy.CFI.mergeFn_reach_via2` (`lean/ToyCFI/Merge.lean:25-25`):

```lean
-- lean/ToyCFI/Merge.lean:25-25
theorem mergeFn_reach_via2 (c : Caller) (m : Int → Int) : Reach mergeFn c m 3 0 (mergeStVia2 c m) := …
```

`Toy.CFI.mergeFn_no_tableCorrect` (`lean/ToyCFI/Merge.lean:81-82`):

```lean
-- lean/ToyCFI/Merge.lean:81-82
/-- The concrete instance: no CFI program is correct for `mergeFn`. -/
theorem mergeFn_no_tableCorrect (prog : List CFIInst) : ¬ TableCorrect mergeFn prog := …
```

`Toy.CFI.mergeFn_inferred_sound_not_recoverable` (`lean/ToyCFI/Merge.lean:91-95`):

```lean
-- lean/ToyCFI/Merge.lean:91-95
/-- The inferred annotation of `mergeFn` is sound but not recoverable (the join
at block 3 loses the CFA). -/
theorem mergeFn_inferred_sound_not_recoverable :
    annSoundB mergeFn (inferredAnn mergeFn) = true ∧
      annRecoverableB mergeFn (inferredAnn mergeFn) = false := …
```

**`lean/ToyCFI/MultiFrameExamples.lean`**

`Toy.CFI.outerT1Fn_tableCorrect` (`lean/ToyCFI/MultiFrameExamples.lean:45-45`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:45-45
theorem outerT1Fn_tableCorrect : TableCorrect outerT1Fn outerT1CFI := …
```

`Toy.CFI.slotsPreservedBelow_one` (`lean/ToyCFI/MultiFrameExamples.lean:110-111`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:110-111
theorem slotsPreservedBelow_one (frames : List Frame) (truth : List MState) (M : Int → Int) :
    SlotsPreservedBelow frames truth M 1 := …
```

`Toy.CFI.multiFrame_outcome` (`lean/ToyCFI/MultiFrameExamples.lean:170-177`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:170-177
/-- The concrete outcome: caught at depth 1 with landing pad 7; the reconstructed
state has the outer frame's `sp = 998`, `fp = 11`, `s1 = 22`. -/
theorem multiFrame_outcome :
    unwind frames2 innerSt = .caught 1 7 (unwindRegs
      ((rowAt? innerFrame.prog innerFrame.callPC).getD initRow) innerSt) ∧
    (unwindRegs ((rowAt? innerFrame.prog innerFrame.callPC).getD initRow) innerSt).regs.sp = 998 ∧
    (unwindRegs ((rowAt? innerFrame.prog innerFrame.callPC).getD initRow) innerSt).regs.fp = 11 ∧
    (unwindRegs ((rowAt? innerFrame.prog innerFrame.callPC).getD initRow) innerSt).regs.s1 = 22 := …
```

`Toy.CFI.caughtWithCallerState_examples` (`lean/ToyCFI/MultiFrameExamples.lean:547-556`):

```lean
-- lean/ToyCFI/MultiFrameExamples.lean:547-556
/-- `CaughtWithCallerState` examples: it holds for the two-frame witness, and it
fails when the handler frame's program has no row at its call site, even though
unwinding itself reports `caught 1 7` there (the personality routine does not
consult the handler frame's row). -/
theorem caughtWithCallerState_examples :
    CaughtWithCallerState frames2 truth2 topCaller innerSt 1 7 outerFrame outerSt ∧
      rowAt? outerFrameMalformed.prog outerFrameMalformed.callPC = none ∧
      (∃ st, unwind [innerFrame, outerFrameMalformed] innerSt = .caught 1 7 st) ∧
      ¬ CaughtWithCallerState [innerFrame, outerFrameMalformed] truth2 topCaller innerSt 1 7
        outerFrameMalformed outerSt := …
```

**`lean/ToyCFI/ProbeLoop.lean`**

`Toy.CFI.probeAnn_sound` (`lean/ToyCFI/ProbeLoop.lean:25-25`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:25-25
theorem probeAnn_sound (page : Nat) : annSoundB (probeFn page) probeAnn = true := …
```

`Toy.CFI.genCFI_probeFn_eq` (`lean/ToyCFI/ProbeLoop.lean:37-38`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:37-38
/-- The anchor-relative program is what the generator emits. -/
theorem genCFI_probeFn_eq (page : Nat) : genCFI (probeFn page) probeAnn = probeAnchorCFI := …
```

`Toy.CFI.probeLoopState_reach` (`lean/ToyCFI/ProbeLoop.lean:45-47`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:45-47
/-- Every iteration's state is reachable at the loop PC (block 1, offset 0). -/
theorem probeLoopState_reach (page : Nat) (c : Caller) (m : Int → Int) (n : Nat) :
    Reach (probeFn page) c m 1 0 (probeLoopState page c m n) := …
```

`Toy.CFI.probeAnchorCFI_tableCorrect` (`lean/ToyCFI/ProbeLoop.lean:108-109`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:108-109
/-- The anchor-relative table is correct for every `page`. -/
theorem probeAnchorCFI_tableCorrect (page : Nat) : TableCorrect (probeFn page) probeAnchorCFI := …
```

`Toy.CFI.probeSpCFI_not_tableCorrect` (`lean/ToyCFI/ProbeLoop.lean:112-114`):

```lean
-- lean/ToyCFI/ProbeLoop.lean:112-114
/-- The SP-relative table is incorrect for every `page > 0`. -/
theorem probeSpCFI_not_tableCorrect (page : Nat) (hpage : 0 < page) :
    ¬ TableCorrect (probeFn page) probeSpCFI := …
```

</details>

## Boundaries

Non-claims come first, per result, exactly as recorded in `results.json`. Two non-claims apply to every result: it is a statement about the toy model and neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and every connection to a real system is a separate *derived (modeling bridge)* claim stated under **Findings**.

### Non-claims, per result

#### R1: `genCFI_tableCorrect_of_sound_recoverable_annotation`

- Does not say every correct table is produced by genCFI, nor that genCFI's output is minimal.
- annSoundB/annRecoverableB are checks over the package's abstract domain (CFA-relative registers and CFA-relative stack slots); whether every function that has a correct table also has a sound recoverable annotation in this domain is not established (not proved here). The related checker gap checkCFI_incomplete concerns checkCFI, which uses the inferred annotation inferredAnn: it proves that checkCFI rejects the correct table incCFI for incFn, not that incFn has no sound recoverable annotation.
- Rows are emitted at every PC (one address unit per operation); real emitters only emit at frame-affecting instructions and encode advances in bytes.
- The return-address column, DW_CFA_def_cfa_expression and register rules other than same/offset are not modeled.
- annRecoverableB only requires that some row is entailed at each PC; that genCFI's own derived row is then entailed is the separate lemma entails_rowOf_of_stateRecoverableB (completeness of rowOf for the toy's entailment), and the encoder lemma rowAt_genCFI_eq_rowOf states which row genCFI emits at each PC.
- Op.call is modeled as a state-preserving no-op in both step and xfer (the caller-saved scratch register t1 and all stack memory are unchanged across a call), and cfaChoice/entails allow t1 as a CFA base. checkCFI can therefore accept tables that anchor the CFA in t1 across a call: outerT1Fn_tableCorrect proves the hand-written table outerT1CFI (CFA = t1 + 0 from address 1 on, across the call at address 2) TableCorrect for outerT1Fn, and its one-line proof checkCFI_sound (by decide) has the kernel evaluate checkCFI outerT1Fn outerT1CFI to true, i.e. checkCFI accepts it. genCFI itself chooses t1 only at a PC where none of fp, sp, s1 is CFA-relative in the abstract state (cfaChoice takes the first CFA-relative register in the order fp, sp, s1, t1); that genCFI can emit a t1-anchored call-site row is not proved here. A t1-anchored call-site row violates the CFA-base hypothesis BaseSafeUpTo of the multi-frame theorem unwind_caught_at_first_handler_frame_with_caller_registers (the call-site rows of outer frames must use sp or a callee-saved register as CFA base); in the toy multi-frame setting an inner frame that overwrites t1 makes the reconstructed state wrong (multiFrame_fails_without_baseSafeUpTo), and the same is expected after a real call that clobbers caller-saved registers (derived, not proved here).
- Reach requires 0 < (f.blockOps b).length at function entry and on every CFG edge, so empty basic blocks (ops = []) are unenterable dead ends rather than frame-neutral pass-through blocks; projecting a real CFG to frame-affecting operations without contracting or padding frame-neutral blocks makes TableCorrect vacuously true on paths through empty blocks (and for the whole function if block 0 is empty).
- genCFI emits rememberState/restoreState only across a single immediately preceding layout block whose entry row equals the current block's entry row (otherwise it re-defines the row explicitly); it encodes rule 'same' with CFIInst.restore r, which is correct only because initRow sets every register to 'same' (unlike CIEs that initialize a return-address column to an offset rule); and it places row changes before advanceLoc 1, relying on rowAt?'s convention that instructions located at addresses <= pc apply at pc. No claim is made that a real unwinder uses the same boundary convention: LLVM libunwind's parseFDEInstructions (llvm/llvm-project commit 701f926aebef9d992746680f00548cff3703a7dc, libunwind/src/DwarfParser.hpp line 503, 'while ((p < instructionsEnd) && (codeOffset < pcoffset))') stops before instructions located exactly at the looked-up code offset.
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R2: `no_tableCorrect_of_conflictingCfaOffsetsAt`

- ConflictingCfaOffsetsAt is sufficient for impossibility; it is not claimed to be necessary. A function might have no correct table because a callee-saved register is unrecoverable even though some register keeps a fixed CFA offset (not proved here: the package exhibits no such function).
- The abstract-domain version ('a merge point whose incoming abstract frame states join to an unrecoverable state admits no correct table') is not claimed: joins may lose information that a table can still exploit (not proved here; compare checkCFI_incomplete, a correct table that checkCFI, which works in this abstract domain, rejects).
- Escape hatches (each defeats the hypothesis or changes the setting): agreeing frame states at the merge (positive control mergeFnBalanced); a register that holds a CFA-relative anchor on every incoming path; tail-duplicating or splitting the merge block so that each incoming path has its own PC; mutually exclusive branch conditions that make one incoming path infeasible (Reach ignores branch predicates); requiring correctness only at call sites (synchronous unwinding) when the merge block contains no call (mergeFn's merge block contains only ret); or a CFA rule more expressive than register+offset (DW_CFA_def_cfa_expression, not modeled).
- Says nothing about remember/restore: no linear encoding helps, because both paths reach the same PC.
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R3: `coldBlocks_no_row_recovers_at_both_epilogue_ret_and_cold_entry`

- Shown for one CFG; it does not characterize in general which pairs of program points admit a common row.
- Holds for every layout, including the CFG-order layout 0, 2, 1; that the naive emitter is correct for that layout (naiveCFI_coldFnFallthrough_tableCorrect) is because there the two program points get different addresses and different rows, not because one row serves both. The positive control shows that a different pair of program points (the epilogue's first PC and the cold entry) does share a row.
- Escape hatches for a concrete layout: give the cold block's address its own row - an instruction located there (restoreState, or an explicit re-definition: genCFI_coldFn_tableCorrect, coldExplicitCFI_tableCorrect) or a layout in which the cold block does not follow the epilogue's ret; place the cold block in a separate code section with its own FDE initialized from the CIE plus cloned prologue instructions (not modeled: one FDE covers the whole toy function); or require correctness only at call sites (synchronous unwinding), under which the row at the epilogue's ret, which cannot throw, is irrelevant.
- Does not establish expressive necessity of rememberState/restoreState: the explicit re-definition program coldExplicitCFI, which contains neither rememberState nor restoreState, is also TableCorrect for coldFn (coldExplicitCFI_tableCorrect); that its per-PC rows coincide with those of genCFI's program is not claimed.
- Real-world consequences (e.g. an unwinder computing a wrong CFA or failing) are derived (modeling bridge) only: they follow if the real table's row at the cold block is the post-epilogue row.
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R3b: `coldFn_not_tableCorrect_of_cold_entry_row_eq_epilogue_ret_row`

- Reference point: the program-level form, for the single layout 0, 1, 2, of the layout-independent fact that no single row recovers the caller both at the epilogue's ret and at the cold block's entry (coldBlocks_no_row_recovers_at_both_epilogue_ret_and_cold_entry); it adds no generality beyond coldFn.
- The hypothesis is row equality, not 'no instruction at address 6'; the latter implies the former in the toy semantics (rowAt? stops at the first advanceLoc past pc), but that implication is not stated as a Lean lemma.
- Escape hatches: an instruction at address 6 that changes the row (restoreState after a rememberState in the epilogue, or an explicit re-definition; genCFI_coldFn_rows_differ_and_tableCorrect, coldExplicitCFI_tableCorrect); a layout in which the cold block does not follow the epilogue's ret (naiveCFI_coldFnFallthrough_tableCorrect); a separate FDE for the cold block (not modeled); or requiring correctness only at call sites (synchronous unwinding), which this TableCorrect does not model.
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R3c: `naiveCFI_coldFn_cold_entry_cfa_is_true_cfa_minus_one`

- Reference point: a concrete evaluation quantifying the CFA error of a table whose row at the cold block is inherited from the epilogue, the situation ruled out by coldBlocks_no_row_recovers_at_both_epilogue_ret_and_cold_entry and coldFn_not_tableCorrect_of_cold_entry_row_eq_epilogue_ret_row; it is not a general statement.
- The size of the error (one address unit) is specific to this toy prologue (one push).
- The callee-saved fp rule of that row ('same') is also wrong there for every caller whose fp differs from CFA - 1, i.e. whenever c.regs.fp ≠ c.cfa - 1: in the state coldStCold c m, which is reachable at that PC for every caller c and memory m (coldFn_reach_cold), fp holds c.cfa - 1 (coldStCold_regs), so there the rule yields c.cfa - 1 instead of the caller's fp. That consequence is not proved here as a Lean lemma; this theorem states only the CFA error.
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R4: `probeLoop_cfa_correct_at_every_iteration_iff_fp_anchor`

- The iff characterizes the CFA rule (R.cfaReg, R.cfaOff) and says nothing about the register rules R.rules. For register rules the package proves sufficiency for one concrete table: probeAnchorCFI, whose row at the loop PC saves fp at CFA - 1 and keeps s1 same, is TableCorrect for every page (probeAnchorCFI_tableCorrect). Whether every row that recovers the caller at the loop PC must use these register rules is not proved here.
- One loop shape with one anchor (fp); other anchors (e.g. a scratch register holding the old sp) are not examined; a scratch anchor is unsafe at call sites when the callee may clobber it: in the toy multi-frame setting an inner frame that overwrites the outer frame's t1 anchor makes the reconstructed state wrong (multiFrame_fails_without_baseSafeUpTo), and the multi-frame theorem unwind_caught_at_first_handler_frame_with_caller_registers accordingly requires sp or a callee-saved register as the CFA base of outer frames' call-site rows (BaseSafeUpTo).
- Within the loop body there are no calls or stores, so the claim says nothing about stack probes that touch memory.
- Restricted to register+offset CFA rules at one loop PC shared by all iterations: unrolling a bounded probe gives each iteration its own PC with a static sp offset (no base switch needed), and DW_CFA_def_cfa_expression (not modeled) can compute the CFA without a dedicated anchor register.
- The table-level consequence for the SP-relative program probeSpCFI (not TableCorrect for page > 0) is the separate theorem spRelative_cfa_right_on_entry_wrong_after_first_iteration_of_pos_page.
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R4b: `spRelative_cfa_right_on_entry_wrong_after_first_iteration_of_pos_page`

- Concerns one fixed offset; that no SP-relative rule with any fixed offset works at every iteration when page > 0 is the content of the separate characterization probeLoop_cfa_correct_at_every_iteration_iff_fp_anchor (for page > 0 a row computes the correct CFA at every iteration iff its CFA rule is fp + 1), not of this theorem.
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R5a: `lookupFirst_eq_result_of_uniqueAt`

- UniqueAt is pointwise; NonOverlapping (pairwise disjoint ranges) implies it for every pc (uniqueAt_of_nonOverlapping) but is not needed: a table holding the same entry twice is UniqueAt at every pc without being NonOverlapping (duplicate_entries_uniqueAt_not_nonOverlapping).
- Says nothing about what a personality routine does with 'no landing pad' or 'not found'; the toy personality frameAction skips the frame on the first and terminates on the second, a modeling choice that mirrors the C++ personality cited below.
- UniqueAt t pc equates entries as values (e1 = e2), not table positions: duplicate identical entries are permitted, and even 'forall pc, UniqueAt t pc' does not imply NonOverlapping t (duplicate_entries_uniqueAt_not_nonOverlapping).
- CallSite models only an optional landing-pad address and omits the LSDA action and type tables; in the cited Itanium C++ personality (libc++abi scan_eh_tab, cxa_personality.cpp lines 774-778 and 884-892), a matching entry with a non-zero landing pad but actionEntry == 0 (a cleanup-only scope), or whose catch clauses do not match the exception type, continues unwinding in the search phase rather than catching.
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R5b: `lookupFirst_eq_notFound_iff`

- Reference point: a generic property of first-match list search; it uses no interval structure.
- 'Not found' is distinct from 'entry without landing pad': in the C++ personality cited below the first terminates, the second continues unwinding (derived (modeling bridge)).
- CallSite models only an optional landing-pad address and omits the LSDA action and type tables; in the cited Itanium C++ personality (libc++abi scan_eh_tab, cxa_personality.cpp lines 774-778 and 884-892), a matching entry with a non-zero landing pad but actionEntry == 0 (a cleanup-only scope), or whose catch clauses do not match the exception type, continues unwinding in the search phase rather than catching.
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R5c: `lookupScan_eq_result_of_sorted_uniqueAt`

- The companion lookupScan_eq_notFound_of_none_contains (no hypotheses) covers the 'not found' direction.
- Off-by-one conventions are separate counterexamples: an inclusive end (lookupIncl_wrong_on_adjacent_ranges) and looking up the return address instead of return address - 1 (lookup_at_return_address_misses_last_call_in_range).
- UniqueAt t pc equates entries as values (e1 = e2), not table positions: duplicate identical entries are permitted, and even 'forall pc, UniqueAt t pc' does not imply NonOverlapping t (duplicate_entries_uniqueAt_not_nonOverlapping).
- CallSite models only an optional landing-pad address and omits the LSDA action and type tables; in the cited Itanium C++ personality (libc++abi scan_eh_tab, cxa_personality.cpp lines 774-778 and 884-892), a matching entry with a non-zero landing pad but actionEntry == 0 (a cleanup-only scope), or whose catch clauses do not match the exception type, continues unwinding in the search phase rather than catching.
- Without SortedByStart the converse of lookupScan_eq_notFound_of_none_contains fails: the early-exit scan can return notFound although a later entry covers pc (lookupScan_wrong_without_sorted), which frameAction turns into terminate.
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R5d: `uniqueAt_of_nonOverlapping`

- Reference point: a supporting lemma connecting the global well-formedness condition to the pointwise hypothesis UniqueAt t pc of lookupFirst_eq_result_of_uniqueAt and lookupScan_eq_result_of_sorted_uniqueAt.
- The converse fails even in its strongest form: 'forall pc, UniqueAt t pc' does not imply NonOverlapping t, because UniqueAt compares entries as values and a table may contain the same entry twice (duplicate_entries_uniqueAt_not_nonOverlapping); a fortiori UniqueAt t pc at a single pc does not imply it.
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R5e: `lookupIncl_wrong_on_adjacent_ranges`, `lookup_at_return_address_misses_last_call_in_range`

- Reference point: two concrete evaluations, not general statements.
- Concerns the toy's unit-size addresses; real tables use byte offsets.
- CallSite models only an optional landing-pad address and omits the LSDA action and type tables; in the cited Itanium C++ personality (libc++abi scan_eh_tab, cxa_personality.cpp lines 774-778 and 884-892), a matching entry with a non-zero landing pad but actionEntry == 0 (a cleanup-only scope), or whose catch clauses do not match the exception type, continues unwinding in the search phase rather than catching.
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R6: `unwind_caught_at_first_handler_frame_with_caller_registers`

- Scratch registers (t1) of the handler frame are not recovered and are not claimed.
- The frame-base claim is about the address CFA - frameSize; the theorem says nothing about the values stored at the local slots, whose preservation is not a hypothesis here (that inner frames can overwrite them is not proved here).
- Models a single pass that stops at the handler; the two-phase search/cleanup protocol, cleanups (landing pads that resume unwinding), catch-clause type matching and the personality's register setup are not modeled.
- The toy personality terminates when a frame has a call-site table that does not cover its call PC; this mirrors the cited C++ personality and is a modeling choice, not a property of DWARF unwinding.
- Lookups use the call instruction's own address; real unwinders look up return address - 1.
- Callee effects are not modeled by Reach (call is a no-op); the link between a frame and its callee is only the chain hypothesis plus save-slot preservation.
- hskip and hcatch constrain the outcome of the operational lookup (lookupScan inside frameAction), not the call-site table's contents: without SortedByStart a frame whose table contains a handler entry for its call PC can terminate instead (multiFrameDecl_fails_without_lsdaWellFormed: an unsorted table whose second entry covers the call PC); without UniqueAt the scan can return the outcome of a different covering entry (lookupScan_wrong_without_uniqueAt, a statement about tables, not frames); that such a frame can instead be skipped is not proved here. The declarative form, with sorted unique tables and entries containing the call PCs, is the separate theorem unwind_caught_at_first_handler_frame_of_sorted_unique_lsda, which combines this theorem with the scan lemma lookupScan_eq_result_of_sorted_uniqueAt.
- Frame pre-supplies fn, prog, lsda and callPC for every outer frame as an external list rather than recovering each caller's return address from memory or a link register through a return-address column; corruption of return-address stack slots by inner frames is therefore not modeled.
- Row carries a rule for sp, but Recovers and unwindRegs ignore Row.rules.sp and set the caller's sp to the computed CFA unconditionally (an unwinder in which an explicit sp register rule overrides the CFA is not modeled).
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R6c: `unwind_caught_at_first_handler_frame_of_sorted_unique_lsda`

- LsdaWellFormedUpTo is required for frames 0..j only; frames beyond j are never consulted.
- UniqueAt t pc equates entries as values (e1 = e2), not table positions: duplicate identical entries are permitted, and even 'forall pc, UniqueAt t pc' does not imply NonOverlapping t (duplicate_entries_uniqueAt_not_nonOverlapping).
- CallSite models only an optional landing-pad address and omits the LSDA action and type tables; in the cited Itanium C++ personality (libc++abi scan_eh_tab, cxa_personality.cpp lines 774-778 and 884-892), a matching entry with a non-zero landing pad but actionEntry == 0 (a cleanup-only scope), or whose catch clauses do not match the exception type, continues unwinding in the search phase rather than catching.
- Scratch registers (t1) of the handler frame are not recovered and are not claimed; BaseSafeUpTo forbids t1 as the CFA base of the call-site rows of frames 1..j.
- The frame-base claim is about the address CFA - frameSize; the theorem says nothing about the values stored at frame j's local slots, whose preservation is not a hypothesis here (that inner frames can overwrite them is not proved here).
- Models a single pass that stops at the handler; the two-phase search/cleanup protocol, cleanups (landing pads that resume unwinding), catch-clause type matching and the personality's register setup are not modeled.
- The toy personality frameAction terminates when a frame has a call-site table that does not cover its call PC; DeclarativeSkippedBelow and DeclarativeCatch exclude this for frames 0..j. This mirrors the cited C++ personality and is a modeling choice, not a property of DWARF unwinding.
- Lookups use the call instruction's own address (callPC); real unwinders look up return address - 1.
- Callee effects are not modeled by Reach (call is a no-op); the link between a frame and its callee is only the chain hypothesis ChainUpTo plus the save-slot hypothesis SlotsPreservedBelow.
- Frame pre-supplies fn, prog, lsda and callPC for every outer frame as an external list rather than recovering each caller's return address from memory or a link register through a return-address column; corruption of return-address stack slots by inner frames is therefore not modeled.
- Row carries a rule for sp, but Recovers and unwindRegs ignore Row.rules.sp and set the caller's sp to the computed CFA unconditionally (an unwinder in which an explicit sp register rule overrides the CFA is not modeled).
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R6b: `recovers_of_reads_agree`

- A frame (locality) lemma about one row; it says nothing about how the agreeing state is obtained (obtaining such a state across several frames is the subject of the multi-frame unwinding theorems, e.g. unwind_caught_at_first_handler_frame_with_caller_registers).
- Recovers reads only the CFA base register, the callee-saved registers with rule 'same' and the save slots of callee-saved registers with rule 'offset'; Row.rules.sp and the scratch register t1 are never read, so agreement on them is neither required nor established.
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R7: `checkCFI_sound`

- Not complete: checkCFI_incomplete exhibits a correct table it rejects (a store and reload through an unknown address). Completeness is not claimed.
- The soundness proof is relative to the toy semantics (Reach, step, rowAt?); the checker is not a verifier of real .eh_frame data.
- Inference may run out of fuel, in which case checkCFI returns false (still sound).
- Op.call is modeled as a state-preserving no-op in both step and xfer (the caller-saved scratch register t1 and all stack memory are unchanged across a call), and cfaChoice/entails allow t1 as a CFA base. checkCFI can therefore accept tables that anchor the CFA in t1 across a call: outerT1Fn_tableCorrect proves the hand-written table outerT1CFI (CFA = t1 + 0 from address 1 on, across the call at address 2) TableCorrect for outerT1Fn, and its one-line proof checkCFI_sound (by decide) has the kernel evaluate checkCFI outerT1Fn outerT1CFI to true, i.e. checkCFI accepts it. genCFI itself chooses t1 only at a PC where none of fp, sp, s1 is CFA-relative in the abstract state (cfaChoice takes the first CFA-relative register in the order fp, sp, s1, t1); that genCFI can emit a t1-anchored call-site row is not proved here. A t1-anchored call-site row violates the CFA-base hypothesis BaseSafeUpTo of the multi-frame theorem unwind_caught_at_first_handler_frame_with_caller_registers (the call-site rows of outer frames must use sp or a callee-saved register as CFA base); in the toy multi-frame setting an inner frame that overwrites t1 makes the reconstructed state wrong (multiFrame_fails_without_baseSafeUpTo), and the same is expected after a real call that clobbers caller-saved registers (derived, not proved here).
- Reach requires 0 < (f.blockOps b).length at function entry and on every CFG edge, so empty basic blocks (ops = []) are unenterable dead ends rather than frame-neutral pass-through blocks; projecting a real CFG to frame-affecting operations without contracting or padding frame-neutral blocks makes TableCorrect vacuously true on paths through empty blocks (and for the whole function if block 0 is empty).
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R7b: `checkCFI_incomplete`

- One source of incompleteness; others (joins, fuel) are not catalogued.
- Clearing AState.slots on a store through an address that is not CFA-relative (storeSlot) is part of the transfer function whose soundness is proved (xfer_sound); it accounts for a store that may overwrite a CFA-relative save slot. That a variant without the clearing would be unsound whenever offset rules are in use is not proved here. In incFn the reload of fp from the address [sp + 0] just written restores the caller's value (store-to-load forwarding through an address that AState does not track), and incCFI uses 'same' for every register; the package proves that incCFI is TableCorrect and rejected (checkCFI_incomplete), not that these are the only reasons.
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

#### R7c: `reach_inv_of_annSound`

- Reference point: the standard post-fixpoint soundness step of forward abstract interpretation, re-derived for the toy domain as a supporting lemma of the generator theorem genCFI_tableCorrect_of_sound_recoverable_annotation and the checker theorem checkCFI_sound.
- Says nothing about rows or about semantic table correctness (Recovers, TableCorrect). On top of annotation soundness, the checkers checkWith and checkCFI additionally check that the row at each PC is entailed by the abstract state there (rowsOK, entails); checkWith_sound and checkCFI_sound prove that passing this check is sufficient for TableCorrect. The check is not necessary: checkCFI_incomplete proves TableCorrect incFn incCFI together with checkCFI incFn incCFI = false.
- Reach requires 0 < (f.blockOps b).length at function entry and on every CFG edge, so empty basic blocks (ops = []) are unenterable dead ends rather than frame-neutral pass-through blocks; projecting a real CFG to frame-affecting operations without contracting or padding frame-neutral blocks makes TableCorrect vacuously true on paths through empty blocks (and for the whole function if block 0 is empty).
- This is a statement about the toy model; it neither establishes nor refutes the corresponding claim about a real unwinder, compiler or ABI, and connections to real systems are separate derived (modeling bridge) claims.

### Attractive stronger conclusions that are not established

- **Checker completeness is false** (known not to apply): `checkCFI_incomplete` exhibits a `TableCorrect` table that
  `checkCFI` rejects. Only soundness (`checkCFI_sound`) is claimed.
- **Merge-point impossibility stated over the abstract domain** ("if the join of the incoming abstract frame states is
  unrecoverable, no correct table exists") is not established; it may fail in general because joins can lose
  information that a concrete table can exploit (not proved here). The proved impossibility is the semantic condition
  `ConflictingCfaOffsetsAt`, which is sufficient; its necessity is not claimed, and its non-necessity is not proved
  here.
- **The probing-loop characterization without `page > 0`** is false: for `page = 0` the SP-relative rule is also correct
  at every iteration (`probeLoop_characterization_fails_for_page_zero`,
  `spRelative_wrong_after_first_iteration_fails_for_page_zero`).
- **Pointwise uniqueness for every pc does not imply disjointness**: `duplicate_entries_uniqueAt_not_nonOverlapping`
  (a table that contains the same entry twice). Only `NonOverlapping → UniqueAt` is proved.
- **The early-exit scan without sortedness** can return `notFound` although a later entry covers the PC
  (`lookupScan_wrong_without_sorted`); the toy personality then terminates.
- **A conditional form of the multi-frame conclusion** ("if frame j has a row at its call PC, it computes the true
  CFA") holds vacuously when the handler frame has no row; `CaughtWithCallerState` therefore asserts the row's
  existence, and `caughtWithCallerState_examples` shows a frame list where unwinding reports `caught` but
  `CaughtWithCallerState` fails.
- **Expressive necessity of the state stack** is not established: the explicit re-definition program `coldExplicitCFI`,
  which uses neither `remember_state` nor `restore_state`, is also `TableCorrect` for `coldFn`
  (`coldExplicitCFI_tableCorrect`); that its per-PC rows coincide with those of `genCFI`'s program is not claimed.
- **Real-system consequences** (an unwinder computing a wrong CFA, a C++ program terminating, LLVM emitting a
  particular table) are not established by any theorem; they are derived claims and none was observed by execution.

### Escape hatches for the impossibility and counterexample results

- **R2 (`no_tableCorrect_of_conflictingCfaOffsetsAt`)** is defeated by dropping `ConflictingCfaOffsetsAt`
  (`no_tableCorrect_fails_without_conflictingCfaOffsetsAt`, `mergeFnBalanced`): agreeing frame states at the merge, a
  register that holds a CFA-relative anchor on every incoming path, tail duplication or splitting of the merge block so
  that each path has its own PC, infeasible paths (branch predicates, which `Reach` ignores), correctness required only
  at call sites, or a CFA rule more expressive than register + offset (`DW_CFA_def_cfa_expression`, not modeled).
- **R3 / R3b (`coldBlocks_no_row_recovers_at_both_epilogue_ret_and_cold_entry`,
  `coldFn_not_tableCorrect_of_cold_entry_row_eq_epilogue_ret_row`)** are defeated by giving the cold block's address its
  own row (`restoreState` after a `rememberState` in the epilogue, or an explicit re-definition:
  `genCFI_coldFn_tableCorrect`, `coldExplicitCFI_tableCorrect`), by a layout in which the cold block does not follow the
  epilogue's `ret` (`naiveCFI_coldFnFallthrough_tableCorrect`), by a separate FDE for the cold block (not modeled), or by
  requiring correctness only at call sites.
- **R4b (`spRelative_cfa_right_on_entry_wrong_after_first_iteration_of_pos_page`)** is defeated by `page = 0` or by an
  anchor-relative CFA rule (`probeAnchorCFI_tableCorrect`).
- **R5e and R3c** are concrete evaluations; they are defeated by the correct conventions (half-open ranges, lookup at
  return address - 1) and by emitting a row at the cold block, respectively.

### Hypotheses with `unknown` tightness

None. All 41 hypotheses across the 18 results are `tight`, each with a kernel-checked counterexample in which all other
hypotheses hold and the conclusion fails. Each ledger entry records the class of its counterexample. Several are
degenerate boundary instances rather than failures inside well-formed executions: the empty frame list (`hj` of R6
and R6c), a truth list shorter than the frame list (`htj` of R6 and R6c), the empty call-site table (`he` of R5a and
R5c) and the zero-size probe `page = 0` (`hpage` of R4 and R4b). Others use a state that is not reachable in the given
context (`hchain` of R6 and R6c, `h` of R7c) or a starting state that differs from frame 0's true state (`h0` of R6
and R6c). Every 2-frame multi-frame counterexample has `j = 1`, where `SlotsPreservedBelow` holds vacuously.

### Disproved or dropped statements

None of the 18 results was dropped or found false; every stated result is proved as stated. The stronger forms listed
above as false are recorded with their kernel-checked counterexamples; the other items there are only marked as not
established, and every refutation-style remark in this report that cites no theorem is marked (not proved here).

### Not examined

- No real compiler output, unwinder or personality routine was executed; no comparison was made between `genCFI` and
  LLVM's CFIFixup/CFIInstrInserter output, or between `rowAt?` and libunwind's handling of instructions located exactly
  at the looked-up PC together with the caller-side PC adjustment.
- Expression-based CFA and register rules, `undefined`/`register`/`val_offset` rules, the return-address column,
  hot/cold section splitting with multiple FDEs, two-phase unwinding, cleanups, catch-clause type matching, and
  non-deterministic callee effects on caller-saved registers and memory are outside the model.

## Evidence

All results were kernel-checked with `leanprover/lean4:v4.34.1` (tag `v4.34.1` of `leanprover/lean4`, commit `5045d0056413266e57c625dcd7c365b10e377c52`) on 2026-11-20. For every Lean name referenced by `results.json`, the table gives its role, the axioms it depends on (`Lean.collectAxioms`), the SHA-256 of its statement (the Lean `repr` of its type) and the SHA-256 of its definition closure (sorted lines `name : repr type [:= repr value]` for every package-local constant reachable from the statement, theorem bodies excluded, joined by newlines; the closure size is the number of such constants). The same values are recorded in `audit/statements.json`; the per-declaration axioms for all package declarations are in `audit/axioms.json`.

### Kernel-check record

| Lean name | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.CFI.genCFI_tableCorrect_of_sound_recoverable_annotation` | R1 result | `Quot.sound`, `propext` | `e694b7fc31d9866cd6b73b6cae2fdb1838331412c2422ccd6518bc38f1c1f903` | `9625c75e293bcca059163560b01677c6eb1e1040aeeab29febda89922ecf3260` (206) |
| `Toy.CFI.genCFI_incorrect_without_layoutCovers` | R1 counterexample (hcover) | `Quot.sound`, `propext` | `76a9dcffddf09c67d3de62904c1dfa3c8f378cc817c7edda717db41604b6ee6b` | `1d31cbf76d82476233bf50131a83b0215e79c2be9675ac48d512862cc7e33e98` (224) |
| `Toy.CFI.genCFI_incorrect_without_annSound` | R1 counterexample (hsound) | `Quot.sound`, `propext` | `5de8beba04f11fa8aa5f3c25afed816f88f0617fa68f2e516d86f19d63bc75ce` | `d84c8ed53908bb2324bdb2f9c39c858e7ea1662acb319619f95f9890efa48f90` (226) |
| `Toy.CFI.genCFI_incorrect_without_annRecoverable` | R1 counterexample (hrec) | `Quot.sound`, `propext` | `764006d6fa580f64c8e16f4a79ff3707aeed2042024bd995ea7b154d507823f7` | `643ae7d045b32d368a15236c21bfa88377d4bc6afabd123cdafb12c9a6f0ffa5` (223) |
| `Toy.CFI.genCFI_hypotheses_hold_coldFn` | R1 non-vacuity | `Quot.sound`, `propext` | `446ae1f9c4c2286c539da88336b2528af350893c44c8f8b7423e805addacc8ba` | `560bb8a9558f13fa50204c77c885fb41eac7633b5838ce583bf4f250ede617d1` (125) |
| `Toy.CFI.no_tableCorrect_of_conflictingCfaOffsetsAt` | R2 result | `Quot.sound`, `propext` | `536849f6409810afb25b8b3efa7f37533b6b719ecd68b2c5f10074b6df73bb8b` | `65478ea9ac8bc26eaa063d58a3cde467ba2d6a36341c14cdf9666ca1a99bbd6a` (107) |
| `Toy.CFI.no_tableCorrect_fails_without_conflictingCfaOffsetsAt` | R2 counterexample (hconf) | `Quot.sound`, `propext` | `749e1b2c7932002d6731ac30f4c7aea12caa32227e9d79b2c19a2a906ab21b8b` | `2b707386e1c8298d1121a2472f8081ba4cabe145506809527d6e2e8c6e7eca9b` (108) |
| `Toy.CFI.mergeFn_conflictingCfaOffsetsAt` | R2 non-vacuity | `Quot.sound`, `propext` | `10aa3488f2d61dc6ec180278cf7230ee57a28cefd08e0ac67f905c6171163a1a` | `657d36cde4ecb130b2afec6900d0fecee547d0e27e42bc0a378ce2e2b0990266` (57) |
| `Toy.CFI.genCFI_mergeFnBalanced_tableCorrect` | R2 positive control | `Quot.sound`, `propext` | `c0be63b83d6b26ec6a2cf4d2fe8f4c093f224b6976d6521aa37a275da19bd6e2` | `393eb41bd91c8a1635440c9ded5d748329e09f6cba529505138823fc291d4f52` (214) |
| `Toy.CFI.coldBlocks_no_row_recovers_at_both_epilogue_ret_and_cold_entry` | R3 result | `Quot.sound`, `propext` | `833d368318500651c69f60f346564b2abd1f01068e8a7b5a49f879d3794c54c6` | `12b6e40d913fe194b9791c52d65ad1f883a96dfa3069c5fe386425bc1d1c784f` (71) |
| `Toy.CFI.coldFn_both_pcs_reachable` | R3 non-vacuity | `Quot.sound`, `propext` | `7175193f0a53d9cecdd2903364a6d7cdeb441f72dddfcfe85255548d30cbad44` | `4b0879559dd438761f2f17c1f67c6ff1546fc633e969bcc00a38e2aee54a06f7` (60) |
| `Toy.CFI.coldBlocks_one_row_recovers_at_epilogue_entry_and_cold_entry` | R3 positive control | `Quot.sound`, `propext` | `d50045c6250dc54603e026e16a86db02b919ed42a889686dc7458ea032edf568` | `12b6e40d913fe194b9791c52d65ad1f883a96dfa3069c5fe386425bc1d1c784f` (71) |
| `Toy.CFI.coldFn_not_tableCorrect_of_cold_entry_row_eq_epilogue_ret_row` | R3b result | `Quot.sound`, `propext` | `b43f8e564b3441fb1f7bf06d2a22be206bf477d654be903ff6d5b5a306773a85` | `724c5bdaa709924dd8711a6b02ae799f7c50a405bd905c996cca01d378079ebf` (108) |
| `Toy.CFI.genCFI_coldFn_rows_differ_and_tableCorrect` | R3b positive control; R3b counterexample (hinh) | `Quot.sound`, `propext` | `a123fe1af50ed169d4b5a2442830d021ff86180556b1ac50194f0d6bdb053466` | `a256bc025c24645d4ee5b3b6e4cedf78bfb297320a2bd30af48e30bcac9267b4` (215) |
| `Toy.CFI.naiveCFI_coldFn_rows_equal` | R3b non-vacuity | `propext` | `5821785eea7e5c313e24089dfccfcdc2e38bb280825d6ab3bec263d845872230` | `013c1037527e15f2c579f76aac69a66f00210d62d1fd4007ad76a306c1f7963c` (174) |
| `Toy.CFI.naiveCFI_coldFn_cold_entry_cfa_is_true_cfa_minus_one` | R3c result | `Quot.sound`, `propext` | `601a8f0e9df129f9dfb9ebdcc0e28d4f327ac74cc53b5c8ab10c1a568effb124` | `fdd140f9f0c8c9a13988915cf425c30c06d4555b97a1ab4f84cb2da9c1f17675` (192) |
| `Toy.CFI.coldFn_reach_cold` | R3c non-vacuity | `Quot.sound`, `propext` | `9827d378bcc093eebbbb729cb10843bd679bc83b2421a98901bf409ee55ad07b` | `5859b01d6680ef3fc3ffec1408b8899f59c310b7f49eb3b22fe368d58a283a9f` (59) |
| `Toy.CFI.probeLoop_cfa_correct_at_every_iteration_iff_fp_anchor` | R4 result | `Quot.sound`, `propext` | `3801c6374f3727038e42cd0b9f2e4015054c826769c8212eb7274e75fa04796f` | `048f252cd0689e97c04afe37e374b346506347c6ee5f2c3b83135bd099bedf42` (64) |
| `Toy.CFI.probeLoop_characterization_fails_for_page_zero` | R4 counterexample (hpage) | `Quot.sound`, `propext` | `21939ef168abbf107b4c7977aa13c2e21ea9468ad65996122e6b1ff4b5fbf2ab` | `048f252cd0689e97c04afe37e374b346506347c6ee5f2c3b83135bd099bedf42` (64) |
| `Toy.CFI.probeLoop_characterization_nonvacuity` | R4 non-vacuity | `Quot.sound`, `propext` | `15c014f1468be98efc4223a694ae8b557aa1dd42bfbc2502a5391370d8607d75` | `048f252cd0689e97c04afe37e374b346506347c6ee5f2c3b83135bd099bedf42` (64) |
| `Toy.CFI.spRelative_cfa_right_on_entry_wrong_after_first_iteration_of_pos_page` | R4b result | `Classical.choice`, `Quot.sound`, `propext` | `c03b6bbab66cb1485a40eab32fced9a184cf121d307abbf00de6c154e42b3715` | `0446e11edec71d942b869702db840406c35677f4d006d9ae9a8846bd0dce36f2` (111) |
| `Toy.CFI.spRelative_wrong_after_first_iteration_fails_for_page_zero` | R4b counterexample (hpage) | `Classical.choice`, `Quot.sound`, `propext` | `8346c0b45d6a9cfbbaf0891923893cb8a5bb66e20f8c161c7ffcb760c2d8fb3a` | `0446e11edec71d942b869702db840406c35677f4d006d9ae9a8846bd0dce36f2` (111) |
| `Toy.CFI.spRelative_wrong_after_first_iteration_nonvacuity` | R4b non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `f31eef1fd861bcea3bd1286e8dcceaf03e059a10d8d0373e6db41b583d25bf48` | `37d66cc8dbac873ae7f3e6a82f1544ccfeba84a8cc2d669a0d0f54f89132f0b1` (108) |
| `Toy.CFI.lookupFirst_eq_result_of_uniqueAt` | R5a result | `propext` | `1034b5fa30d6c51194520e6b87dfec287221b005ba7c88e80aac3b2d1147c299` | `ca45e65b0104f22a7ded49ab0a5398ed9833ea9dc9399d69ee8514ee309838cd` (19) |
| `Toy.CFI.lookupFirst_wrong_without_uniqueAt` | R5a counterexample (hu) | `propext` | `ae3d641f1e6055c400406531e74b81169c55821ed2ce4fa4d2e7f282f6006e92` | `7e3eb47c191d19aa3faae64b4e2254ced22b7cbddbc067716639dfacc6e64c6e` (20) |
| `Toy.CFI.lookup_eq_result_fails_without_mem` | R5a counterexample (he); R5c counterexample (he) | `propext` | `bbaa2b5ca9fc27824f72548e786e41dc0fd48bc4bc15cb96c8c5965c9f2feb88` | `25342203e9eda453f90eb750b3aa65265ca4396e67c30fe6a08ccbdc725f4a07` (22) |
| `Toy.CFI.lookup_eq_result_fails_without_contains` | R5a counterexample (hc); R5c counterexample (hc) | `Quot.sound`, `propext` | `6c672693e9036ec222be72f5323e3de626179608fdf6e72a1817f52670e786dd` | `25342203e9eda453f90eb750b3aa65265ca4396e67c30fe6a08ccbdc725f4a07` (22) |
| `Toy.CFI.lookupFirst_nonvacuity` | R5a non-vacuity | `Quot.sound`, `propext` | `8d5335a044c34ba1091c1ace231a359a7573ac666d17605e7654f9d1abd80ee2` | `2e61b8b457b95b22d1ef43d3557342465dd8165511f8af0b82b807b2754bc592` (20) |
| `Toy.CFI.lookupFirst_eq_notFound_iff` | R5b result | `Quot.sound`, `propext` | `3339cad1b28c6dedea929fa82dadffac0705f0f6c8b79f30c0dc6663eae9214a` | `aa2d5668c10c4cc70074a637e13b85315a3f1d427fc85faa1952062d3f57a754` (18) |
| `Toy.CFI.lookupIncl_wrong_on_adjacent_ranges` | R5b non-vacuity; R5e result | none | `41d912c67f47258e4f8e98d064681d2faec7303f623c83f37abf2a8e40a0c207` | `f25b4845a01ea2a82f36107ba38ae72e17338ee639087be7a735a262e7c12a25` (21) |
| `Toy.CFI.lookupScan_eq_result_of_sorted_uniqueAt` | R5c result | `propext` | `151d19edd054519cbcfb2e28461b24ec1ce898d813f60e41eef68d2b77947bb4` | `5999de0a6043428d54cbb019d240f41677ff28e68debd2a92e1997d416ea281c` (18) |
| `Toy.CFI.lookupScan_wrong_without_sorted` | R5c counterexample (hs) | `Quot.sound`, `propext` | `34fcc046a7127787c05b7059ecccef160f0727eac03a9ed75ead269be0ee66ec` | `3f8ad0da8b77508feda4f7c1b406d34a97e0ab51bf6107d78aab83e2d4740db0` (19) |
| `Toy.CFI.lookupScan_wrong_without_uniqueAt` | R5c counterexample (hu) | `Quot.sound`, `propext` | `ee4eb4d3ec70646a2d86b485ce7c1e3af449c4cce8e832355a6219ecd4da1a8e` | `078a3a5ff05ce6cd9298ca50e7365c53452403c704b24eda02a454ddb20f3453` (19) |
| `Toy.CFI.lookupScan_nonvacuity` | R5c non-vacuity | `Quot.sound`, `propext` | `d6fa1f5d449802f9faa5b633600acafd6cfa7cd85e6a5aba09b58e0d86b0f5a8` | `c2997f02895011e60ca764c576d053b406d8062a5ee4170394d6b788638975a7` (19) |
| `Toy.CFI.uniqueAt_of_nonOverlapping` | R5d result | `propext` | `033e9b9315f9aec0d95bb7575bbfc68368cfcbb2d6a35c39b878d195593f2d48` | `83309316f19ff87d920352664867197af6295d86759cb5cfb5331ba119a11f33` (8) |
| `Toy.CFI.uniqueAt_fails_without_nonOverlapping` | R5d counterexample (h) | `propext` | `a77f57ed30e60b049cadd87da0ae718c25fcdb2cedae5d2575bd990f9e7b0c11` | `ed5a4ce5fde159c88abc899154842b0c1deb6408edfca614efb96fcded25bcc2` (9) |
| `Toy.CFI.lsdaAdjacent_wellFormed` | R5d non-vacuity; R5e non-vacuity | `Quot.sound`, `propext` | `926a62d6a0e876b9a1faf90411402644ac5073ec8b40816af3f7fcba1a693244` | `d4786cf17bfffb228d098fbdf068ff378c45785365a041834170f7142578d7b0` (9) |
| `Toy.CFI.lookup_at_return_address_misses_last_call_in_range` | R5e result | none | `33245e77c83ce15e319923f557a79565f0557f26d1204342fdd1eaa5ad6788b0` | `ef07a495af739f387d1c5c6716807e1e040e36b5b44c486cb5ccdaca4245e7cd` (19) |
| `Toy.CFI.unwind_caught_at_first_handler_frame_with_caller_registers` | R6 result | `Quot.sound`, `propext` | `5cb0b5e1a419cac61aaf864864286558ce28489f5d16705e45d779ce1e104b2c` | `abb39f81ccc3e0a05b6374d083ce01edcc53aa64bebeb7835d6fe9c74d9f4c3d` (164) |
| `Toy.CFI.multiFrame_fails_without_chainUpTo` | R6 counterexample (hchain) | `Classical.choice`, `Quot.sound`, `propext` | `238653906e0f78b61211b53d7edcd2b7a18f91a3c0d59969d4c0932ec20a42d2` | `c0a6541ca2f0093000b8cc87ce78143b16ba474a6cdced8c69e0b36e943aa16e` (282) |
| `Toy.CFI.multiFrame_fails_without_tablesUpTo` | R6 counterexample (htab) | `Quot.sound`, `propext` | `54dc7d1915f77f202a122dce3e7729faab5dc24388b9f8b2fcbf9420aa14c55c` | `5ad36e142ff2a58b42b0310198fb083efcd9f4cb3b233f06334082dad3318876` (282) |
| `Toy.CFI.multiFrame_fails_without_h0` | R6 counterexample (h0) | `Quot.sound`, `propext` | `898e9b781a6283c75330d846dc0294ba2d4c2eb8a9356d6e266d0a73404260c0` | `e7f0547c75d05a19596e7faf31c810a45ec2b242a1526a86b5f776a323e007f5` (283) |
| `Toy.CFI.multiFrame_fails_without_hj` | R6 counterexample (hj) | `propext` | `2c61b8858a44adf12255fc0c646cc8a4c8b6308f65f077d86831d9ff17e576bd` | `176fefb7d2c0424ac2bec5f8eba1acf1fcabf8a18b434add16dd1c02fbdc2a80` (279) |
| `Toy.CFI.multiFrame_fails_without_htj` | R6 counterexample (htj) | `Quot.sound`, `propext` | `e54085e4bc09e4fae5de5bb8b5e91df3c9ae9df0481a5fb1ca503703643c363b` | `c0a6541ca2f0093000b8cc87ce78143b16ba474a6cdced8c69e0b36e943aa16e` (282) |
| `Toy.CFI.multiFrame_fails_without_skippedBelow` | R6 counterexample (hskip) | `Quot.sound`, `propext` | `9b2291e8d38ac56affae2b78ad8012551296ca7dbc8e746cf3998e4e7923e803` | `7ed5beba02618af90032977f41108b60940ccdfc32d0a921f9047aca776a59e5` (282) |
| `Toy.CFI.multiFrame_fails_without_handler` | R6 counterexample (hcatch) | `Quot.sound`, `propext` | `6add8556eaa7f92ff21372bcc6ee1ca3b8bcfea0981eb056fb5eea64c2e07be0` | `75988e87c13c9ee044a161fd6087c7768336f388dbd64bbd9d50ef7e87c438b3` (282) |
| `Toy.CFI.multiFrame_fails_without_baseSafeUpTo` | R6 counterexample (hbase) | `Quot.sound`, `propext` | `6060248a66327c7afa04dac6fa96144b44076dc74cc8e329fe64050f771482f9` | `60173056f83f63f26e2b768ffe7d8f49cea4535c0118e7af0f30e1f7b7b517a5` (281) |
| `Toy.CFI.multiFrame_fails_without_slotsPreservedBelow` | R6 counterexample (hslots) | `Quot.sound`, `propext` | `8726c5f929718e0f8ae7e28fa61b1fceef77db58ea54ea3f0f6308ce2336e0d2` | `69226f031728af4e110bb6193477f9e5ca1e139f768161d8a699bbd940708119` (287) |
| `Toy.CFI.multiFrame_hypotheses_hold` | R6 non-vacuity | `Quot.sound`, `propext` | `9165cf2c35e62270bf6de1ffa28b7b821248c156fc849c5ede2fca4632c3fc47` | `a7b55bb193efd42687c14c885ee3d2ff7f716da4af621d594a48361d85c5043d` (264) |
| `Toy.CFI.unwind_caught_at_first_handler_frame_of_sorted_unique_lsda` | R6c result | `Quot.sound`, `propext` | `5816d2a8200a1171c8ab10eb5546145320e572f1e6e5751ee9669ce83764f63b` | `8136fbb04505bc205240cd8d38dc7d3861e7a2733c51d4915451d6dc839bc6e4` (170) |
| `Toy.CFI.multiFrameDecl_fails_without_chainUpTo` | R6c counterexample (hchain) | `Classical.choice`, `Quot.sound`, `propext` | `30a6b6a66fd22df65b341dd8a51ae1d74f221d4087294e8a21964bbda538c29d` | `69a538ee78fa7762c1ce3ca7272b035f10274d1062c5e2235325891b3b652625` (288) |
| `Toy.CFI.multiFrameDecl_fails_without_tablesUpTo` | R6c counterexample (htab) | `Quot.sound`, `propext` | `7bd3ae4a572902b85c601155cc17258389672da08cce6c0fdf2b507775853b47` | `5c19b15ed1524379037fda9a81a2a6c84e29771cd414f82e3b1f591f5eba689c` (288) |
| `Toy.CFI.multiFrameDecl_fails_without_lsdaWellFormed` | R6c counterexample (hlsda) | `Quot.sound`, `propext` | `179a8d3388c0df620a1e15d4b38b8d763b91539b9bfaf023f96fd00555f42752` | `2a03bbbd480a0e8eaf086a877841e6e21c84af35e15dbfb97f0016f39af851a5` (288) |
| `Toy.CFI.multiFrameDecl_fails_without_h0` | R6c counterexample (h0) | `Quot.sound`, `propext` | `f9002c810e06f46039ad660d98aadcedf5b8b960a9c3bc0d8e860f3c24abfb56` | `2f537fbb69da8dea3a55cf1cef7f6b32a28b26aa180b994f6204138023a74149` (289) |
| `Toy.CFI.multiFrameDecl_fails_without_hj` | R6c counterexample (hj) | `propext` | `7956145f2aab3345acf3dd232c8fa87f89594903bb6f412f673343aa7f2a63f9` | `15c3ea8c3a78fbb9175ccd7247e225d1dfaea734fa4fa802a82adb6eaf58993e` (285) |
| `Toy.CFI.multiFrameDecl_fails_without_htj` | R6c counterexample (htj) | `Quot.sound`, `propext` | `1b21c0231a06dc37d585b2ff0385231a61dbe9c363fe25c2904495d172dfbea0` | `69a538ee78fa7762c1ce3ca7272b035f10274d1062c5e2235325891b3b652625` (288) |
| `Toy.CFI.multiFrameDecl_fails_without_declarativeSkippedBelow` | R6c counterexample (hskip) | `Quot.sound`, `propext` | `90b510e004294f5cf49ea8590080af90b4095f92ce6c0293edc6d14c51a5e754` | `c12ca8450a882dbfb3b0eddd3dcf3733f471a935b49cdacaa4c6ff5f148a7d34` (288) |
| `Toy.CFI.multiFrameDecl_fails_without_declarativeCatch` | R6c counterexample (hcatch) | `Quot.sound`, `propext` | `58859e9a89cd4c827ae0ec57a8c56ba3615e5f3548807aa5827d0c4c7b22df10` | `476e3d1af9c13aa0327488f2546cc144fd14e7fe58d3fc150ff16ca5c11212e1` (288) |
| `Toy.CFI.multiFrameDecl_fails_without_baseSafeUpTo` | R6c counterexample (hbase) | `Quot.sound`, `propext` | `cda196e770a272541295e50a073d9877b8277ff917db2e71c8f9c490d2db981b` | `861825907b371e37ed83137a87d4d19c92c68e259817d32116700cc0552c6547` (287) |
| `Toy.CFI.multiFrameDecl_fails_without_slotsPreservedBelow` | R6c counterexample (hslots) | `Quot.sound`, `propext` | `25a6e996b244b2dc447f98d97c53e05fbd24537856c2545ff9db67daf7da65ee` | `8c949e740c55659a89870a3f38a60a0120db4ab56bb56071258c73ea3bc913d2` (293) |
| `Toy.CFI.multiFrame_declarative_hypotheses_hold` | R6c non-vacuity | `Quot.sound`, `propext` | `f217045269233bad483830e25b4b5935a28f96ccb73ea32d0248bb09954c93ca` | `1d527af9c92bc64e80ec8c68cd1dd65ed6c2699f5c4c6b2d2b976fbc8b2b4a93` (252) |
| `Toy.CFI.recovers_of_reads_agree` | R6b result | `propext` | `2993219ca5eb7e2fe40dc1b1a210c597faf0f5f1f357be8599b13de873be4acc` | `6d2b591f2ca30d796df7f0686586f4c2167eb52ceba742c10ca0e7043acefc93` (38) |
| `Toy.CFI.recovers_of_reads_agree_fails_without_rec` | R6b counterexample (hrec) | none | `ba8f586ed76da9fd1bb3fa740a83a8268dd7e38157185abf23cff85389ae2e02` | `86001a2bd75335d979fe9c06510d4a079ee10939d16835c0a67bdf7936e3bd95` (41) |
| `Toy.CFI.recovers_of_reads_agree_fails_without_cfa` | R6b counterexample (hcfa) | `propext` | `114cf0cff459a7c5b2656d44b9fca9c0f9e685ed5f3e451950057783abc3dfb5` | `b9e2c319af7588c6f541e8c7571dbd3403b0bcdd8d0894d5a5f0a700d1c61f34` (42) |
| `Toy.CFI.recovers_of_reads_agree_fails_without_same` | R6b counterexample (hsame) | `propext` | `42bfff40b5a75726c8bfb9cf679cad8225dae490bf11c58da3f17d1f2448dffd` | `b9e2c319af7588c6f541e8c7571dbd3403b0bcdd8d0894d5a5f0a700d1c61f34` (42) |
| `Toy.CFI.recovers_of_reads_agree_fails_without_slot` | R6b counterexample (hslot) | `propext` | `dfbebf4174943fd94c6ff7bb86d3ad7ca70efd451824841d339fa89b2cb6315f` | `c2f982816240482be722bc9553e3fa1199a905d8f4f3543757668a95e96ae06d` (41) |
| `Toy.CFI.recovers_of_reads_agree_nonvacuity` | R6b non-vacuity | `propext` | `5c8667295cb802f9565d46dcc2df609425ac23d44ab459e413fa6e3ce341acf2` | `c2f982816240482be722bc9553e3fa1199a905d8f4f3543757668a95e96ae06d` (41) |
| `Toy.CFI.checkCFI_sound` | R7 result | `Quot.sound`, `propext` | `e43777031b689aa4a1438569720a3e6cc75f5cff5448d323161c97a5546c0957` | `1150597678d4a751dacad1fdb8076b2677525bff0baa04af8f84d38425db7713` (190) |
| `Toy.CFI.checkCFI_sound_fails_without_check` | R7 counterexample (h) | `Quot.sound`, `propext` | `cd129df119032fc21c472daad8a0ff53194a455640fccb2a35526bb883b6b03b` | `33e7c308e3f09e8987e7074f3a6e46478329b3e732c0eb18db9ecfbecdc43c3e` (216) |
| `Toy.CFI.checkCFI_examples` | R7 non-vacuity | `propext` | `f4576ca70e73b3f1641aaffe502c99a9415f20ae3cc6d1a60eb8feff5816affc` | `e013ad2ff6e96b9af8dae1cb6e187d74210ef324394290ec2bc19e3f1db9a2c6` (208) |
| `Toy.CFI.checkCFI_incomplete` | R7b result; R7b non-vacuity | `Quot.sound`, `propext` | `a2cc87c8edae3d025955072d3dc5bde3760ee1a07d6126716f658c7e4ce2b4c1` | `c503135ee949b717cb686a88c4c8bb3fb067e5c40aa98e0c2d9450a744709be5` (192) |
| `Toy.CFI.reach_inv_of_annSound` | R7c result | `Quot.sound`, `propext` | `928406c15c62ff2a240e46adadb91c7236b55492ee0fd780522fd1e6fc0a12af` | `429326cadab472bc481133200ee5edaf623cb7283a605327642e95c42b789b6b` (108) |
| `Toy.CFI.reach_inv_fails_without_annSound` | R7c counterexample (hs) | `Quot.sound`, `propext` | `1d4bd28821fbe9200d3abcbc7daa52c0a72475a2e24725b75a2913d06c406718` | `aee5d68e8dd46b68a41569383969235551aae5fc5b1a14a57767a89fa1f4de35` (138) |
| `Toy.CFI.reach_inv_fails_without_reach` | R7c counterexample (h) | `Quot.sound`, `propext` | `e1e26001250b742f7da8d1836eb3130cb14e6f2f51bb092f8f04a92db03f236b` | `13a4cf289c35ae2bdf48f1976e2f26177b7209e2cfb347d851fb548ef359fcde` (136) |
| `Toy.CFI.reach_inv_of_annSound_nonvacuity` | R7c non-vacuity | `Quot.sound`, `propext` | `7e810498315091ba6c5e61c273f90c05a9bfa09d55a0b194a48ddb4b028f65e9` | `6c891a1b619a804a2d691d4a5e05b9b258b6b9513f99ff6e7e42458c93c7cb34` (134) |

Axiom audit: 1005 package declarations were audited; the union of their axioms is `Classical.choice`, `Quot.sound`, `propext`, all within the allowed set `propext`, `Classical.choice`, `Quot.sound`. The sources contain no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC`. 75 statement hashes are recorded.

### Primary sources

All web sources below were consulted on 2026-11-20; the DWARF 5 page locations, the USENIX WOOT 2011 page and paper
PDF, and the `v4.34.1` tag ref were re-checked on 2026-11-21.

- **Lean 4 toolchain**: `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` (tag
  ref resolved through the GitHub REST API: `refs/tags/v4.34.1` is a lightweight tag whose object is this commit, type
  `commit`).
- **T. Bastian, S. Kell, F. Zappa Nardelli**, "Reliable and fast DWARF-based stack unwinding", *Proc. ACM Program.
  Lang.* 3(OOPSLA), Article 146, October 2019, 24 pages, doi:10.1145/3360572. Bibliographic metadata checked against
  the Crossref record for the DOI; passages cited from the author-hosted full text
  https://fzn.fr/projects/frdwarf/frdwarf-oopsla19.pdf, whose page numbers (146:N) are used: §2.2 "Synthesis of
  .eh_frame Tables" begins on p. 146:8, the merge-point abort is on p. 146:11, and in Appendix A `remember_state` and
  `restore(reg)` are on p. 146:21, the state-saving stack `Row*` on p. 146:22 and Table 5 on p. 146:23.
- **G. Klein, T. Nipkow**, "A machine-checked model for a Java-like language, virtual machine, and compiler", *ACM
  TOPLAS* 28(4):619-695, 2006, doi:10.1145/1146809.1146811 (Crossref record checked). Isabelle AFP entry *Jinja*,
  https://www.isa-afp.org/entries/Jinja.html; theory `JVM/JVMExceptions.thy`, browsed at
  https://www.isa-afp.org/browser_info/current/AFP/Jinja/JVMExceptions.html (`matches_ex_entry`, `match_ex_table`,
  `find_handler`). The browser URL tracks the current AFP release and is not immutable.
- **X. Leroy**, "Formal verification of a realistic compiler", *Commun. ACM* 52(7):107-115, 2009,
  doi:10.1145/1538788.1538814 (Crossref record checked). CompCert, repository `AbsInt/CompCert`, commit
  `2685140bf72c959446981fb99b5e44a8975021bc`: `backend/Kildall.v` line 661 (`Theorem fixpoint_solution`), line 741
  (`Theorem fixpoint_invariant`); `backend/Stackingproof.v` line 800 (`Lemma agree_locs_return`), line 1007
  (`Lemma save_callee_save_correct`).
- **G. A. Kildall**, "A unified approach to global program optimization", *POPL 1973*, pp. 194-206,
  doi:10.1145/512927.512945 (Crossref record checked).
- **J. Oakley, S. Bratus**, "Exploiting the Hard-Working DWARF: Trojan and Exploit Techniques with No Native Executable
  Code", USENIX WOOT 2011,
  https://www.usenix.org/conference/woot11/exploiting-hard-working-dwarf-trojan-and-exploit-techniques-no-native-executable.
  The conference page gives the title and venue but lists only James Oakley (Dartmouth College) and shows no abstract.
  The second author, Sergey Bratus, and the abstract were read from the paper PDF linked from that page,
  https://www.usenix.org/events/woot11/tech/final_files/Oakley.pdf, whose author line is "James Oakley, Sergey Bratus"
  and whose abstract states that the data structures used to store exception handling information "actually contain
  Turing-complete bytecode, which is executed by a virtual machine during the course of exception unwinding and
  handling".
- **DWARF Debugging Information Format, Version 5** (DWARF Debugging Information Format Committee, February 13, 2017),
  https://dwarfstd.org/doc/DWARF5.pdf: §2.5.1.2 (`DW_OP_fbreg`) and §2.5.1.3 item 15 on printed page 33 (PDF page 51)
  (`DW_OP_call_frame_cfa`, including the "extensive location list" sentence) were read in the PDF. Page numbers in this
  report are the printed "Page N" footers of the document; the PDF begins with 18 front-matter pages numbered i-xviii,
  so printed page N is PDF page N + 18. The §6.4.2.4 wording of `DW_CFA_remember_state`/`DW_CFA_restore_state` is
  taken from the verbatim quotation in DWARF issue 230103.1; the same two phrases appear in §6.4.2.4 of the PDF
  (section beginning on printed page 181, PDF page 199). The register-rule definitions (§6.4.1) and CFA-definition
  instructions (§6.4.2.2) are not relied upon.
- **DWARF issue 230103.1**, "Clarify that DW_CFA_remember_state includes the current CFA" (Fangrui Song; submitted
  2023-01-03; accepted 2023-07-24), https://dwarfstd.org/issues/230103.1.html.
- **Itanium C++ ABI: Exception Handling**, `$Revision: 1.22 $`, https://itanium-cxx-abi.github.io/cxx-abi/abi-eh.html.
  This page carries a revision string but no immutable URL; its call-site table layout is not specified there.
- **LLVM**, repository `llvm/llvm-project`, commit `701f926aebef9d992746680f00548cff3703a7dc`. Files and line ranges as
  quoted in the prior-art entries: `llvm/lib/CodeGen/CFIFixup.cpp` (header comment lines 10-66, precondition line 21,
  `insertRememberRestorePair` line 195, `fixupBlock` line 245, first-block-of-section cloning lines 290-294);
  `llvm/lib/CodeGen/CFIInstrInserter.cpp` (header lines 9-17; remember/restore handling lines 316-339 and 375-381;
  "Different saved locations for the same CSR" lines 366-369; `verify` lines 545-571); `libunwind/src/DwarfParser.hpp`
  (`PrologInfo` lines 95-100; instruction loop line 503; `DW_CFA_remember_state`/`DW_CFA_restore_state` lines 606-632);
  `libunwind/src/DwarfInstructions.hpp` (`getCFA` lines 66-76; `kRegisterInCFA` lines 107-108; caller SP := CFA line
  284); `libcxxabi/src/cxa_personality.cpp` (`scan_eh_tab`: lines 684-688, 698, 747-748, 753, 763-768, 774-778,
  884-892, 899-905, 910-911). These line references were checked against the files at that commit.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`.
No network access is needed after the toolchain is installed; the project has no dependencies.

**Primary check.** From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package: it copies `lean/` to a temporary directory and then (1) runs
`lake build`; (2) rejects any Lean source containing `sorry`, `admit`, `native_decide` or an `axiom` declaration; (3)
runs an inline Lean program that computes, with `Lean.collectAxioms`, the axioms of every declaration of the `ToyCFI`
library and fails if any lies outside `propext`, `Classical.choice`, `Quot.sound`; and (4) for every Lean name
referenced by `results.json` (fields `lean`, `nonvacuity_witness_lean`, `positive_control_lean` and every hypothesis
`counterexample`) and every name recorded in `audit/statements.json`, recomputes the SHA-256 of the statement (the
string `toString (repr ci.type)`) and of the definition closure (for each package-local constant reachable from the
statement type, following types, definition values and inductive constructors but not theorem proofs, the line
`name : repr type` with ` := repr value` appended for non-theorems; lines sorted and joined with newlines), and
compares both, plus the closure size, with `audit/statements.json`. It prints `REVALIDATED` and exits 0 iff every
check passes. A matching closure hash means that neither the statement nor any package definition it depends on has
changed.

**Narrow manual checks.** Build and print the axioms of selected results:

```sh
cd lean
lake build
cat > /tmp/toycfi_axioms.lean <<'EOF'
import ToyCFI
#print axioms Toy.CFI.genCFI_tableCorrect_of_sound_recoverable_annotation
#print axioms Toy.CFI.no_tableCorrect_of_conflictingCfaOffsetsAt
#print axioms Toy.CFI.coldBlocks_no_row_recovers_at_both_epilogue_ret_and_cold_entry
#print axioms Toy.CFI.probeLoop_cfa_correct_at_every_iteration_iff_fp_anchor
#print axioms Toy.CFI.lookupScan_eq_result_of_sorted_uniqueAt
#print axioms Toy.CFI.unwind_caught_at_first_handler_frame_with_caller_registers
#print axioms Toy.CFI.unwind_caught_at_first_handler_frame_of_sorted_unique_lsda
#print axioms Toy.CFI.checkCFI_sound
#print axioms Toy.CFI.checkCFI_incomplete
EOF
lake env lean /tmp/toycfi_axioms.lean
```

Each line must report a subset of `[propext, Classical.choice, Quot.sound]`. At the recorded toolchain, eight of these
nine lines report `[propext, Quot.sound]` and the line for `lookupScan_eq_result_of_sorted_uniqueAt` reports
`[propext]`. The table under **Evidence** records the axioms of every Lean name referenced by `results.json`; they
vary by theorem (for example, `spRelative_cfa_right_on_entry_wrong_after_first_iteration_of_pos_page` also uses
`Classical.choice`, and `lookup_at_return_address_misses_last_call_in_range` uses none).

**After a change.** If a definition in `lean/ToyCFI/` changes, rerun `python3 support/revalidate.py .`: any result
whose statement or definition closure is affected fails the hash comparison, and its card must be re-examined before
it is relied on. For a different Lean toolchain, edit `lean/lean-toolchain` in a copy and rerun the same command; the
`repr`-based hashes may change across toolchains even when the mathematics does not, so a hash mismatch after a
toolchain change calls for re-reading the affected statements rather than implying that a result is false. The
derived (modeling bridge) claims are revalidated separately by re-reading the cited lines at a newer
`llvm/llvm-project` revision.
