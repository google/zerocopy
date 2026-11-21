# Panic safety in a toy model (Lean 4): unwinding through broken invariants, leak amplification, drop guards and safe `forget`

## Summary

This package is a Lean 4 toy model of the panic-safety obligations of unsafe collection code. A container owns a buffer of cells and a `len` field, and its drop glue drops the first `len` cells. Library operations temporarily break the container's invariant `Inv` and call user code (callbacks standing for closures, `clone` or comparisons, and element destructors) in between. Under `unwind`, the library frame's live locals and drop guards are cleaned up and the owner then drops the container; under `abort`, nothing runs after a panic. Drop guards in the program language `Prog` are pure fix-ups of `(buf, len)`: their drop glue cannot run element destructors, panic, read or change the drop log, or reach UB. A separate client language, whose programs neither panic nor run panicking destructors, models safe `forget`. The package contains 15 results (R0–R9, R11–R15), all kernel-checked with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. Every statement that quantifies over runs quantifies over the runs that the deterministic interpreter `exec` (through `run`, `sites` and `harness`) or `clientRun` produces from the given callback table and destructor table.

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program. Every connection to Rust is a separate claim labelled `derived (modeling bridge)`.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

One sentence per result. Each restates the result's plain claim with whole conclusions dropped and every hypothesis, domain and qualifier kept:

- **R0** (characterization, T0): For every toy state, `Inv` holds iff the container's drop glue, run with non-panicking destructors, does not reach UB; and for every frame (whose guards are pure `(buf, len)` fix-ups) and every state, `DropSafe` holds iff unwinding the frame with non-panicking destructors ends (`.ok`) in a state satisfying `Inv`.
- **R1** (counterexample, T1): On the two-element container `ceMem2` (which satisfies `Inv`), with the callback table "remove element `0`, then panic" and non-panicking destructors, raw-move retain under `unwind` unwinds to a state violating `Inv`, and the owner's drop of that state reaches UB.
- **R2** (theorem, T1): For every callback table, destructor table and entry state satisfying `Inv`, raw-move retain under `abort` returns the abstract retain result if and only if the abstract run finishes, aborts otherwise, and never reaches UB.
- **R3** (characterization, T1): For every callback table, destructor table and entry state satisfying `Inv`, if raw-move retain under `unwind` unwinds, the unwound state satisfies `Inv` iff the abstract retain removed no element up to and including the panic (a removed element whose destructor panics counts as removed).
- **R4** (characterization, T1): For every toy program `p` (programs start with an empty frame, and guard fix-ups are pure `(buf, len)` functions), `p` is panic-safe under `unwind` iff it is panic-safe under `abort` and, from every entry state satisfying `Inv` under every callback table and every destructor table, every callback site and every element-destructor site reached by `p` (as produced by `exec` through `sites`) satisfies `DropSafe`.
- **R5** (counterexample, T1): `truncateLate` is panic-safe under `abort` and satisfies `CallbackSitesDropSafe`, yet it fails `CallSitesDropSafe` and is not panic-safe under `unwind`; from every state, under every callback table and every destructor table, every user-code site it reaches is an element-destructor site; and on `ceMem1` (which satisfies `Inv`) with the destructor table `dtPanicsOn0`, under `unwind` and every callback table, it unwinds to the state `⟨[some 0], 1, [0], 0, 0⟩`, in which `len` still covers the dropped value `0` and which violates `Inv`.
- **R6** (theorem, T1): For every callback table, every destructor table (panicking destructors included) and every entry state satisfying `Inv`, leak-amplified retain under `unwind` returns the abstract result if and only if the abstract run finishes, otherwise unwinds to a state with `len = 0` and with exactly the removed values added to the drop log, and never aborts or reaches UB.
- **R7** (theorem, T1): For every callback table, every destructor table (panicking destructors included) and every entry state satisfying `Inv`, back-shift-guard retain with the guard (a pure `(buf, len)` fix-up) updated before each destructor, under `unwind`, returns the abstract result if and only if the abstract run finishes, otherwise unwinds to a container holding exactly the kept values followed by the unprocessed values and satisfying `Inv`, and never aborts or reaches UB.
- **R8** (theorem, T1): For every callback table, every destructor table and every entry state satisfying `Inv`, whenever back-shift-guard retain (guard updated before each destructor; a pure `(buf, len)` fix-up) unwinds, every value of the entry container is in the drop log or held by the first `len` cells of the unwound container.
- **R9** (theorem, T1): For every callback table, every destructor table in which no destructor panics, and every entry state satisfying `Inv`, back-shift-guard retain with the guard (a pure `(buf, len)` fix-up) updated after each destructor, run under `unwind`, reaches no UB, and a return or an unwind leaves `Inv`.
- **R11** (counterexample, T1): In the toy client language (no panics, non-panicking destructors), the four-instruction client `forgetClient`, all of whose instructions are safe operations (among them `forgetGuard`), reaches UB when run against the destructor-reliant drain on the one-element container `ceMem1` (which satisfies `Inv`).
- **R12** (theorem, T1): In the toy client language, for every client program and every entry state satisfying `Inv`, running the program against the leak-amplified drain does not reach UB.
- **R13** (theorem, T1): In the toy client language, for every client program that does not contain `forgetGuard` and every entry state satisfying `Inv`, running the program against the destructor-reliant drain does not reach UB.
- **R14** (theorem, T1): For every callback table (callbacks may drop or forget each element they receive, or panic while owning it), every destructor table and every entry state satisfying `Inv`, the closure-scoped drain `drainWith`, which keeps its guard (a pure `(buf, len)` fix-up) in the library frame, run under `unwind`, reaches no UB, and a return or an unwind leaves `Inv`.
- **R15** (theorem, T0, reference point): For every callback table, destructor table and entry state satisfying `Inv`, `bumpBoth` run under `unwind` reaches no UB, and a return or an unwind leaves `Inv`; and there are a callback table, a destructor table and a state satisfying `Inv` and `CountersAgree` from which the run of `bumpBoth` under `unwind` unwinds to a state violating `CountersAgree`.

What these results do not show is listed per result, first, under **Boundaries**; read it before relying on any result. The identifiers R10 and R16 are not used.

## Applicability

### Model fidelity

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program. Every connection to Rust below is a separate claim labelled `derived (modeling bridge)`.

The toy model is meant to capture the shape of the panic-safety obligations of unsafe collection code:

- a container owns a buffer of cells and a `len` field, and its drop glue drops the first `len` cells;
- library operations temporarily break the container's invariant and call user code (closures, `clone`, comparisons, element destructors) in between;
- under unwinding, the library frame's drop glue (live locals, drop guards) runs and the caller (who owns the container) later drops the container;
- `mem::forget` is a safe operation.

The design question the package informs: unsafe library code breaks a container's safety invariant temporarily and calls user code in between, and under unwinding drop glue then runs on the broken state. What must hold at each user-code call site, which repair patterns (drop guards, leak amplification, abort-on-panic) are sound in the toy and what each costs, and what a safe API can never rely on once leaking is safe?

Known gaps:

- Guards in `Prog` are pure `(buf, len)` fix-ups (`Guard.fix : List Cell → Nat → List Cell × Nat`): a guard cannot run element destructors, panic, read or change the drop log, or reach UB. Drop guards that drop elements (as a drain's drop guard does), destructor panics inside such a guard, UB inside a guard, and interactions between the drop order of guards and locals are not modelled in `Prog`. Every result about `Prog` (R0–R9, R14, R15) is stated for this class of guards.
- The client language of R11–R13 has non-panicking destructors and no panics or unwinding; its drain guard drops the remaining elements and then sets `len := 0`.
- No type system, no borrow checker beyond the rejection rules of the client language, no allocator, no concurrency, no re-entrant callbacks, no catch boundary (after an unwind the owner drops the container), no non-terminating operations, no foreign-function boundaries, no user code that mutates the container or element contents, no `Rc` cycles (safe `forget` stands in for every safe way to leak), element values are opaque tokens, and real standard-library source is not modelled.
- A destructor that panics still counts as having dropped its value, and a destructor panic during unwinding or during the owner's drop aborts. Both are definitions of the toy (`unwindEntries`, `dropCells`), not theorems; the std 1.85.0 `Drop` documentation says such a double panic "will likely abort the program", and the Rust Reference at the commit cited under **Evidence** states no such rule.
- A program that returns with live frame entries is counted as UB (malformed).

Truncating operations. The loops and guards use truncated natural-number subtraction: `n - del` and `i - del` in `rawLoop`; `p - d` in `guardLoop` and `guardLoopLate`; `n - p`, `p - d` and `n - d` in `backshift`; `n - c` in `tailFix`; `e - c` in `cstep` (`dropGuard`) and `cend`. The loops maintain `del ≤ i ≤ n` (resp. `d ≤ p ≤ n`, `c ≤ n`), and the client language keeps `c ≤ e`, so the truncation is not exercised on the paths the results describe. Degenerate edges: on an empty container (`len = 0`) every retain variant performs no callback and returns with `len = 0`, and `drainWith` returns with `len = 0`; `copy`, `dropCell`, `readOut` and `writeBack` at an index outside the buffer are UB; guard fix-ups (`copyRange`) ignore writes outside the buffer and read uninitialized (`none`) outside it. Buffer cells at index `len` and beyond are unconstrained by `Inv`.

Bounded checks. Theorems whose names end in `_upTo3`, `_upTo4` or `_bounded`, and `characterization_bounded_samples`, are fully proved by `decide` over an explicitly listed finite family (sizes, entry states, and all behaviour tables determined by their first few entries). They are labelled `[bounded search]`; each establishes its property on the listed family and neither establishes nor refutes the corresponding unbounded statement. Each bounded check accompanies an unbounded theorem quoted in the same card (for `characterization_bounded_samples`, the theorem of R4; for `guardRetain_unwound_leakFree_noInv_bounded`, `guardRetain_unwound_leakFree_noInv`), and no card depends on a bounded check.

Generated runs. Statements that quantify over runs quantify over the outputs of the deterministic interpreter `exec` (through `run`, `sites` and `harness`) or of `clientRun`, for every callback table and every destructor table. Because the interpreter is deterministic and each value's destructor runs at most once on a UB-free run, a return-or-panic strategy of user code that adapts to the history determines one run, and that run is the run of some pair of tables (derived; not a Lean theorem). Behaviours of user code other than return and panic are not modelled.

### Lean environment and subjects

Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), Lean core library, with no Mathlib and no other dependency. Lake package `toy_panic_safety`, library `PanicSafety` (directory `lean/`), namespace `Toy.PanicSafety`. The Lean toolchain is the subject on which every theorem was checked. The other subjects in `REPORT.json` (Rust 1.85.0 source, the Rustonomicon, the Rust Reference, RFCs, MiniRust, and papers) are the sources of the documented Rust behaviour and prior art that the `derived (modeling bridge)` claims cite; none of them was executed, and no Rust code was compiled or run.

### Definitions (verbatim)

Every definition below is quoted from the package's Lean sources with its `file:line` range. Positive and negative examples for each definition are proved in `lean/PanicSafety/Examples.lean` (and next to some definitions) and quoted under **Evidence** (auxiliary declarations).

#### Values, memory, and the invariant

```lean
-- lean/PanicSafety/Basic.lean:30
abbrev Tok := Nat
```

```lean
-- lean/PanicSafety/Basic.lean:33
abbrev Cell := Option Tok
```

```lean
-- lean/PanicSafety/Basic.lean:36
def toks (cs : List Cell) : List Tok := cs.filterMap id
```

```lean
-- lean/PanicSafety/Basic.lean:41-47
structure Mem where
  buf : List Cell
  len : Nat
  dropped : List Tok
  ctrA : Nat
  ctrB : Nat
deriving DecidableEq, Repr
```

```lean
-- lean/PanicSafety/Basic.lean:50
def Mem.elems (m : Mem) : List Cell := m.buf.take m.len
```

```lean
-- lean/PanicSafety/Basic.lean:56-57
def OwnsUniquely (d : List Tok) (cs : List Cell) : Prop :=
  (∀ c ∈ cs, c ≠ none) ∧ (toks cs).Nodup ∧ ∀ t ∈ toks cs, t ∉ d
```

```lean
-- lean/PanicSafety/Basic.lean:65
def Inv (m : Mem) : Prop := m.len ≤ m.buf.length ∧ OwnsUniquely m.dropped m.elems
```

Unfolded (prose): `Inv m` holds when `m.len ≤ m.buf.length`, every one of the first `m.len` cells is `some t`, the tokens of those cells are pairwise distinct, and none of them is in `m.dropped`. The counters `ctrA`, `ctrB` and the cells at index `m.len` and beyond are unconstrained.

Examples: `inv_pos`, `inv_pos_staleTail`, `inv_pos_countersDisagree` (admitted); `inv_neg_lenPastBuffer`, `inv_neg_duplicate`, `inv_neg_dropped`, `inv_neg_uninit` (rejected); `ownsUniquely_pos`, `ownsUniquely_neg_duplicate`, `ownsUniquely_neg_dropped`, `ownsUniquely_neg_uninit`.

#### User code

```lean
-- lean/PanicSafety/Basic.lean:70-73
inductive Beh where
  | ret (b : Bool)
  | panic
deriving DecidableEq, Repr
```

```lean
-- lean/PanicSafety/Basic.lean:77
abbrev Callback := Nat → Beh
```

```lean
-- lean/PanicSafety/Basic.lean:81
abbrev DtorTable := Tok → Bool
```

```lean
-- lean/PanicSafety/Basic.lean:84
def noPanicDtors : DtorTable := fun _ => false
```

```lean
-- lean/PanicSafety/Basic.lean:87
def NoPanickingDtors (dt : DtorTable) : Prop := ∀ t, dt t = false
```

Examples: `noPanickingDtors_pos` (`noPanicDtors`), `noPanickingDtors_neg` (`dtPanicsOn0`).

Why tables are general: the interpreter is deterministic, so for every adaptive user strategy that chooses return-or-panic outcomes, the run it produces is the run of some callback table and destructor table (each value's destructor runs at most once on a UB-free run). Behaviours other than return/panic are not modelled.

#### Programs, frames, and the interpreter

```lean
-- lean/PanicSafety/Basic.lean:92-93
structure Guard where
  fix : List Cell → Nat → List Cell × Nat
```

The doc comment of `Guard` (lean/PanicSafety/Basic.lean:92-93 and the three lines above it) reads: "A drop guard. Its drop glue is a fix-up of the container's buffer and `len` (memory moves and a `len` update, as in a back-shift guard or a set-len-on-drop guard). By construction a fix-up cannot run destructors and cannot read or change the drop log." A fix-up is a total function; it cannot panic or reach UB (`copyRange` ignores out-of-range writes and reads `none` out of range). Guards that drop elements are therefore not expressible in `Prog`; destructor-running cleanup in `Prog` is written with locals (`Entry.value`), and the drain guard of the client language below does drop elements.

```lean
-- lean/PanicSafety/Basic.lean:96-100
inductive Entry where
  /-- A live local owning value `t` (for instance the result of `ptr::read`). -/
  | value (t : Tok)
  /-- A live drop guard. -/
  | guard (g : Guard)
```

```lean
-- lean/PanicSafety/Basic.lean:104-136
inductive Prog where
  /-- Return to the caller. Returning with live frame entries is malformed (counted as UB);
  scope-exit drop glue is written explicitly with `dropVal` / `popGuard`. -/
  | done
  /-- Read the container's `len` field. -/
  | getLen (k : Nat → Prog)
  /-- Invoke the user callback (a closure, `clone`, comparison, ...). -/
  | call (k : Bool → Prog)
  /-- `ptr::copy` of one cell (bits only; the source keeps its bits). UB if out of bounds. -/
  | copy (src dst : Nat) (k : Prog)
  /-- `ptr::drop_in_place(&mut buf[i])`: run the destructor of the value in cell `i`. -/
  | dropCell (i : Nat) (k : Prog)
  /-- `set_len(n)`. -/
  | setLen (n : Nat) (k : Prog)
  /-- `let x = ptr::read(&buf[i])`: push a live local owning the value of cell `i`. -/
  | readOut (i : Nat) (k : Prog)
  /-- `ptr::write(&mut buf[i], x)`: move the top local into cell `i` (no drop). -/
  | writeBack (i : Nat) (k : Prog)
  /-- `drop(x)` for the top local. -/
  | dropVal (k : Prog)
  /-- `mem::forget(x)` for the top local. -/
  | forgetVal (k : Prog)
  /-- Create a drop guard. -/
  | pushGuard (g : Guard) (k : Prog)
  /-- Update the fields of the top guard (for instance `g.processed += 1`). -/
  | setGuard (g : Guard) (k : Prog)
  /-- End of the top guard's scope: its fix-up runs. -/
  | popGuard (k : Prog)
  /-- `mem::forget` of the top guard. -/
  | forgetGuard (k : Prog)
  /-- Increment counter `ctrA` / `ctrB` (no drop glue). -/
  | bumpA (k : Prog)
  | bumpB (k : Prog)
```

```lean
-- lean/PanicSafety/Basic.lean:139-142
inductive Mode where
  | abort
  | unwind
deriving DecidableEq, Repr
```

```lean
-- lean/PanicSafety/Basic.lean:146-151
inductive Res where
  | ret (m : Mem)
  | unwound (m : Mem)
  | abort
  | ub
deriving DecidableEq, Repr
```

```lean
-- lean/PanicSafety/Basic.lean:154-158
inductive URes where
  | ok (m : Mem)
  | abort
  | ub
deriving DecidableEq, Repr
```

```lean
-- lean/PanicSafety/Basic.lean:163-170
def unwindEntries (dt : DtorTable) : List Entry → Mem → URes
  | [], m => .ok m
  | .value t :: es, m =>
      if t ∈ m.dropped then .ub
      else if dt t then .abort
      else unwindEntries dt es { m with dropped := t :: m.dropped }
  | .guard g :: es, m =>
      unwindEntries dt es { m with buf := (g.fix m.buf m.len).1, len := (g.fix m.buf m.len).2 }
```

```lean
-- lean/PanicSafety/Basic.lean:173-180
def panicFrom (mode : Mode) (dt : DtorTable) (es : List Entry) (m : Mem) : Res :=
  match mode with
  | .abort => .abort
  | .unwind =>
    match unwindEntries dt es m with
    | .ok m' => .unwound m'
    | .abort => .abort
    | .ub => .ub
```

```lean
-- lean/PanicSafety/Basic.lean:183-186
inductive SiteKind where
  | callback
  | destructor
deriving DecidableEq, Repr
```

```lean
-- lean/PanicSafety/Basic.lean:190-193
structure Site where
  kind : SiteKind
  entries : List Entry
  mem : Mem
```

```lean
-- lean/PanicSafety/Basic.lean:198-264
def exec (mode : Mode) (cb : Callback) (dt : DtorTable) :
    Prog → Nat → List Entry → Mem → Res × List Site
  | .done, _, es, m => (if es.isEmpty then .ret m else .ub, [])
  | .getLen k, j, es, m => exec mode cb dt (k m.len) j es m
  | .call k, j, es, m =>
      match cb j with
      | .ret b =>
        let r := exec mode cb dt (k b) (j + 1) es m
        (r.1, ⟨.callback, es, m⟩ :: r.2)
      | .panic => (panicFrom mode dt es m, [⟨.callback, es, m⟩])
  | .copy s d k, j, es, m =>
      if s < m.buf.length ∧ d < m.buf.length then
        exec mode cb dt k j es { m with buf := m.buf.set d (m.buf.getD s none) }
      else (.ub, [])
  | .dropCell i k, j, es, m =>
      match m.buf[i]? with
      | some (some t) =>
        if t ∈ m.dropped then (.ub, [])
        else
          let m' := { m with dropped := t :: m.dropped }
          if dt t then (panicFrom mode dt es m', [⟨.destructor, es, m'⟩])
          else
            let r := exec mode cb dt k j es m'
            (r.1, ⟨.destructor, es, m'⟩ :: r.2)
      | _ => (.ub, [])
  | .setLen n k, j, es, m => exec mode cb dt k j es { m with len := n }
  | .readOut i k, j, es, m =>
      match m.buf[i]? with
      | some (some t) => exec mode cb dt k j (.value t :: es) m
      | _ => (.ub, [])
  | .writeBack i k, j, es, m =>
      match es with
      | .value t :: es' =>
        if i < m.buf.length then exec mode cb dt k j es' { m with buf := m.buf.set i (some t) }
        else (.ub, [])
      | _ => (.ub, [])
  | .dropVal k, j, es, m =>
      match es with
      | .value t :: es' =>
        if t ∈ m.dropped then (.ub, [])
        else
          let m' := { m with dropped := t :: m.dropped }
          if dt t then (panicFrom mode dt es' m', [⟨.destructor, es', m'⟩])
          else
            let r := exec mode cb dt k j es' m'
            (r.1, ⟨.destructor, es', m'⟩ :: r.2)
      | _ => (.ub, [])
  | .forgetVal k, j, es, m =>
      match es with
      | .value _ :: es' => exec mode cb dt k j es' m
      | _ => (.ub, [])
  | .pushGuard g k, j, es, m => exec mode cb dt k j (.guard g :: es) m
  | .setGuard g k, j, es, m =>
      match es with
      | .guard _ :: es' => exec mode cb dt k j (.guard g :: es') m
      | _ => (.ub, [])
  | .popGuard k, j, es, m =>
      match es with
      | .guard g :: es' =>
        exec mode cb dt k j es' { m with buf := (g.fix m.buf m.len).1, len := (g.fix m.buf m.len).2 }
      | _ => (.ub, [])
  | .forgetGuard k, j, es, m =>
      match es with
      | .guard _ :: es' => exec mode cb dt k j es' m
      | _ => (.ub, [])
  | .bumpA k, j, es, m => exec mode cb dt k j es { m with ctrA := m.ctrA + 1 }
  | .bumpB k, j, es, m => exec mode cb dt k j es { m with ctrB := m.ctrB + 1 }
```

```lean
-- lean/PanicSafety/Basic.lean:267-268
def run (mode : Mode) (cb : Callback) (dt : DtorTable) (p : Prog) (m : Mem) : Res :=
  (exec mode cb dt p 0 [] m).1
```

```lean
-- lean/PanicSafety/Basic.lean:272-273
def sites (cb : Callback) (dt : DtorTable) (p : Prog) (m : Mem) : List Site :=
  (exec .unwind cb dt p 0 [] m).2
```

Examples: `unwindEntries_example`, `unwindEntries_example_abort`, `backshift_example`, `truncateThenCall_sites_example`.

#### Panic safety

```lean
-- lean/PanicSafety/Basic.lean:277-281
def ResOk : Res → Prop
  | .ret m => Inv m
  | .unwound m => Inv m
  | .abort => True
  | .ub => False
```

```lean
-- lean/PanicSafety/Basic.lean:288-289
def PanicSafe (mode : Mode) (p : Prog) : Prop :=
  ∀ (cb : Callback) (dt : DtorTable) (m : Mem), Inv m → ResOk (run mode cb dt p m)
```

```lean
-- lean/PanicSafety/Basic.lean:292-294
def PanicSafeAssumingNoDtorPanic (mode : Mode) (p : Prog) : Prop :=
  ∀ (cb : Callback) (dt : DtorTable) (m : Mem), NoPanickingDtors dt → Inv m →
    ResOk (run mode cb dt p m)
```

Unfolded (prose): `PanicSafe mode p` holds when, for every callback table `cb`, every destructor table `dt` and every state `m` with `Inv m`, the run `run mode cb dt p m` is not `ub`, and if it is `ret m'` or `unwound m'` then `Inv m'`. `PanicSafeAssumingNoDtorPanic` adds the hypothesis `NoPanickingDtors dt`.

Examples: `panicSafe_pos` (`truncateThenCall`), `panicSafe_neg` (`truncateLate`), `panicSafe_neg_rawRetain`; `panicSafeAssumingNoDtorPanic_pos` (`truncateLate`), `panicSafeAssumingNoDtorPanic_neg` (`rawRetain`).

#### The owner's drop glue

```lean
-- lean/PanicSafety/Basic.lean:299-303
inductive DRes where
  | ok (d : List Tok)
  | abort
  | ub
deriving DecidableEq, Repr
```

```lean
-- lean/PanicSafety/Basic.lean:307-313
def dropCells (dt : DtorTable) : List Cell → List Tok → DRes
  | [], d => .ok d
  | none :: _, _ => .ub
  | some t :: cs, d =>
      if t ∈ d then .ub
      else if dt t then .abort
      else dropCells dt cs (t :: d)
```

```lean
-- lean/PanicSafety/Basic.lean:317-318
def containerDrop (dt : DtorTable) (m : Mem) : DRes :=
  if m.len ≤ m.buf.length then dropCells dt m.elems m.dropped else .ub
```

```lean
-- lean/PanicSafety/Basic.lean:323-328
inductive Final where
  | returned (m : Mem)
  | panicked (d : List Tok)
  | aborted
  | ub
deriving DecidableEq, Repr
```

```lean
-- lean/PanicSafety/Basic.lean:331-340
def harness (mode : Mode) (cb : Callback) (dt : DtorTable) (p : Prog) (m : Mem) : Final :=
  match run mode cb dt p m with
  | .ret m' => .returned m'
  | .unwound m' =>
    match containerDrop dt m' with
    | .ok d => .panicked d
    | .abort => .aborted
    | .ub => .ub
  | .abort => .aborted
  | .ub => .ub
```

Examples: `containerDrop_pos`, `containerDrop_neg_doubleDrop`, `containerDrop_neg_lenPastBuffer`, `guardRetain_ownerDrop_doublePanic_aborts_example` (a destructor panic during the owner's drop gives `.aborted` by the definition of `dropCells`).

#### The unwinding footprint

```lean
-- lean/PanicSafety/Basic.lean:345-348
def applyGuards : List Entry → List Cell × Nat → List Cell × Nat
  | [], bl => bl
  | .value _ :: es, bl => applyGuards es bl
  | .guard g :: es, bl => applyGuards es (g.fix bl.1 bl.2)
```

```lean
-- lean/PanicSafety/Basic.lean:351-354
def valueToks : List Entry → List Tok
  | [] => []
  | .value t :: es => t :: valueToks es
  | .guard _ :: es => valueToks es
```

```lean
-- lean/PanicSafety/Basic.lean:361-365
def DropSafe (es : List Entry) (m : Mem) : Prop :=
  (applyGuards es (m.buf, m.len)).2 ≤ (applyGuards es (m.buf, m.len)).1.length ∧
  OwnsUniquely m.dropped
    ((valueToks es).map some ++
      (applyGuards es (m.buf, m.len)).1.take (applyGuards es (m.buf, m.len)).2)
```

Unfolded (prose): `DropSafe es m` holds when, after applying every guard fix-up of `es` (most recent first) to `(m.buf, m.len)` to obtain `(b, l)`, we have `l ≤ b.length` and the list "values of the live locals of `es`, followed by the first `l` cells of `b`" is uniquely owned with respect to `m.dropped`.

Examples: `dropSafe_pos_guardRepairs` (a guard repairs a container whose own fields violate `Inv`), `dropSafe_neg_localDuplicates` (a live local duplicates a value the container still owns), `dropSafe_neg_lenPastBuffer` (the length bound is a separate conjunct).

#### Retain variants and the abstract specification

```lean
-- lean/PanicSafety/Retain.lean:20-25
def rawLoop (n : Nat) : Nat → Nat → Nat → Prog
  | 0, _, del => .setLen (n - del) .done
  | r + 1, i, del => .call fun keep =>
      if keep then
        (if 0 < del then .copy i (i - del) (rawLoop n r (i + 1) del) else rawLoop n r (i + 1) del)
      else .dropCell i (rawLoop n r (i + 1) (del + 1))
```

```lean
-- lean/PanicSafety/Retain.lean:28
def rawRetain : Prog := .getLen fun n => rawLoop n n 0 0
```

```lean
-- lean/PanicSafety/Retain.lean:31
def leakRetain : Prog := .getLen fun n => .setLen 0 (rawLoop n n 0 0)
```

```lean
-- lean/PanicSafety/Retain.lean:35-37
def copyRange : Nat → List Cell → Nat → Nat → List Cell
  | 0, b, _, _ => b
  | c + 1, b, s, d => copyRange c (b.set d (b.getD s none)) (s + 1) (d + 1)
```

```lean
-- lean/PanicSafety/Retain.lean:42
def backshift (p d n : Nat) : Guard := ⟨fun b _ => (copyRange (n - p) b p (p - d), n - d)⟩
```

```lean
-- lean/PanicSafety/Retain.lean:45-51
def guardLoop (n : Nat) : Nat → Nat → Nat → Prog
  | 0, _, _ => .popGuard .done
  | r + 1, p, d => .call fun keep =>
      if keep then
        (if 0 < d then .copy p (p - d) (.setGuard (backshift (p + 1) d n) (guardLoop n r (p + 1) d))
         else .setGuard (backshift (p + 1) d n) (guardLoop n r (p + 1) d))
      else .setGuard (backshift (p + 1) (d + 1) n) (.dropCell p (guardLoop n r (p + 1) (d + 1)))
```

```lean
-- lean/PanicSafety/Retain.lean:54
def guardRetain : Prog := .getLen fun n => .pushGuard (backshift 0 0 n) (guardLoop n n 0 0)
```

```lean
-- lean/PanicSafety/Retain.lean:57-63
def guardLoopLate (n : Nat) : Nat → Nat → Nat → Prog
  | 0, _, _ => .popGuard .done
  | r + 1, p, d => .call fun keep =>
      if keep then
        (if 0 < d then .copy p (p - d) (.setGuard (backshift (p + 1) d n) (guardLoopLate n r (p + 1) d))
         else .setGuard (backshift (p + 1) d n) (guardLoopLate n r (p + 1) d))
      else .dropCell p (.setGuard (backshift (p + 1) (d + 1) n) (guardLoopLate n r (p + 1) (d + 1)))
```

```lean
-- lean/PanicSafety/Retain.lean:66-67
def guardRetainLate : Prog :=
  .getLen fun n => .pushGuard (backshift 0 0 n) (guardLoopLate n n 0 0)
```

`guardLoop` and `guardLoopLate` differ in one line: on removal, `guardLoop` updates the guard (`setGuard (backshift (p + 1) (d + 1) n)`) before `dropCell p`; `guardLoopLate` runs `dropCell p` first.

```lean
-- lean/PanicSafety/Retain.lean:72-76
inductive Ending where
  | finished
  | callbackPanic
  | dtorPanic
deriving DecidableEq, Repr
```

```lean
-- lean/PanicSafety/Retain.lean:80-85
structure AbsOut where
  kept : List Tok
  rejected : List Tok
  rest : List Tok
  ending : Ending
deriving DecidableEq, Repr
```

```lean
-- lean/PanicSafety/Retain.lean:89-97
def absRetain (cb : Callback) (dt : DtorTable) : List Tok → Nat → List Tok → List Tok → AbsOut
  | [], _, kept, rej => ⟨kept, rej, [], .finished⟩
  | x :: xs, j, kept, rej =>
    match cb j with
    | .panic => ⟨kept, rej, x :: xs, .callbackPanic⟩
    | .ret true => absRetain cb dt xs (j + 1) (kept ++ [x]) rej
    | .ret false =>
      if dt x then ⟨kept, x :: rej, xs, .dtorPanic⟩
      else absRetain cb dt xs (j + 1) kept (x :: rej)
```

```lean
-- lean/PanicSafety/Retain.lean:100-101
def specRetain (cb : Callback) (dt : DtorTable) (xs : List Tok) : AbsOut :=
  absRetain cb dt xs 0 [] []
```

```lean
-- lean/PanicSafety/RetainResults.lean:29-30
def RetainReturns (o : AbsOut) (m m' : Mem) : Prop :=
  o.ending = .finished ∧ toks m'.elems = o.kept ∧ m'.dropped = o.rejected ++ m.dropped ∧ Inv m'
```

```lean
-- lean/PanicSafety/RetainResults.lean:37
def LeakFree (m m' : Mem) : Prop := ∀ t ∈ toks m.elems, t ∈ m'.dropped ∨ t ∈ toks m'.elems
```

```lean
-- lean/PanicSafety/RetainResults.lean:44-48
def RawAbortExact (cb : Callback) (dt : DtorTable) (m : Mem) : Prop :=
  match run .abort cb dt rawRetain m with
  | .ret m' => RetainReturns (specRetain cb dt (toks m.elems)) m m'
  | .abort => (specRetain cb dt (toks m.elems)).ending ≠ .finished
  | _ => False
```

```lean
-- lean/PanicSafety/RetainResults.lean:57-64
def LeakUnwindExact (cb : Callback) (dt : DtorTable) (m : Mem) : Prop :=
  match run .unwind cb dt leakRetain m with
  | .ret m' => RetainReturns (specRetain cb dt (toks m.elems)) m m'
  | .unwound m' =>
    (specRetain cb dt (toks m.elems)).ending ≠ .finished ∧ m'.len = 0 ∧
    m'.dropped = (specRetain cb dt (toks m.elems)).rejected ++ m.dropped ∧
    m'.buf.length = m.buf.length ∧ m'.ctrA = m.ctrA ∧ m'.ctrB = m.ctrB
  | _ => False
```

```lean
-- lean/PanicSafety/RetainResults.lean:73-80
def GuardUnwindExact (cb : Callback) (dt : DtorTable) (m : Mem) : Prop :=
  match run .unwind cb dt guardRetain m with
  | .ret m' => RetainReturns (specRetain cb dt (toks m.elems)) m m'
  | .unwound m' =>
    (specRetain cb dt (toks m.elems)).ending ≠ .finished ∧
    toks m'.elems = (specRetain cb dt (toks m.elems)).kept ++ (specRetain cb dt (toks m.elems)).rest ∧
    m'.dropped = (specRetain cb dt (toks m.elems)).rejected ++ m.dropped ∧ Inv m'
  | _ => False
```

Examples: `specRetain_example`, `specRetain_example_dtorPanic`, `retainReturns_pos`, `retainReturns_neg_wrongDropLog`, `leakFree_pos`, `leakFree_neg`, `rawAbortExact_pos`, `leakUnwindExact_pos`, `guardUnwindExact_pos` (panic branch), `rawAbortExact_return_pos`, `leakUnwindExact_return_pos`, `guardUnwindExact_return_pos` (return branch, callback table `ceCbRemoveFirst`); the negative examples for the three exact specifications are `rawRetain_abort_exact_needs_inv`, `leakRetain_unwind_exact_needs_inv`, `guardRetain_unwind_exact_needs_inv`.

#### Call-site conditions and small programs

```lean
-- lean/PanicSafety/Characterization.lean:25-27
def CallSitesDropSafe (p : Prog) : Prop :=
  ∀ (cb : Callback) (dt : DtorTable) (m : Mem), Inv m →
    ∀ s ∈ sites cb dt p m, DropSafe s.entries s.mem
```

```lean
-- lean/PanicSafety/Characterization.lean:30-32
def CallbackSitesDropSafe (p : Prog) : Prop :=
  ∀ (cb : Callback) (dt : DtorTable) (m : Mem), Inv m →
    ∀ s ∈ sites cb dt p m, s.kind = .callback → DropSafe s.entries s.mem
```

```lean
-- lean/PanicSafety/Characterization.lean:799
def badSetLen : Prog := .getLen fun n => .setLen (n + 1) .done
```

```lean
-- lean/PanicSafety/Characterization.lean:820-823
def truncateLate : Prog := .getLen fun n =>
  match n with
  | 0 => .done
  | k + 1 => .dropCell k (.setLen k .done)
```

```lean
-- lean/PanicSafety/Characterization.lean:884-887
def truncateThenCall : Prog := .getLen fun n =>
  match n with
  | 0 => .call fun _ => .done
  | k + 1 => .setLen k (.dropCell k (.call fun _ => .done))
```

Examples: `callSitesDropSafe_pos`, `callSitesDropSafe_neg`, `callbackSitesDropSafe_pos`, `callbackSitesDropSafe_neg`.

#### Client language for safe leaking

```lean
-- lean/PanicSafety/Forget.lean:29-32
inductive DrainApi where
  | destructorReliant
  | leakAmplified
deriving DecidableEq, Repr
```

```lean
-- lean/PanicSafety/Forget.lean:35-50
inductive CInstr where
  /-- Create a drain guard over the whole container (the container is then mutably
  borrowed until the guard is dropped or forgotten). -/
  | drain
  /-- Take the next element out of the guard as a client-owned value (no-op when the
  guard is exhausted). -/
  | next
  /-- Drop the most recently obtained value. -/
  | dropVal
  /-- `mem::forget` the most recently obtained value. -/
  | forgetVal
  /-- Drop the guard (its destructor runs). -/
  | dropGuard
  /-- `mem::forget` the guard. -/
  | forgetGuard
deriving DecidableEq, Repr
```

```lean
-- lean/PanicSafety/Forget.lean:54-58
structure CState where
  mem : Mem
  vals : List Tok
  guard : Option (Nat × Nat)
deriving DecidableEq, Repr
```

```lean
-- lean/PanicSafety/Forget.lean:63-67
inductive COut where
  | ok (s : CState)
  | ub
  | rejected
deriving DecidableEq, Repr
```

```lean
-- lean/PanicSafety/Forget.lean:71-76
def dropIdxRange (buf : List Cell) : Nat → Nat → List Tok → Option (List Tok)
  | 0, _, d => some d
  | k + 1, i, d =>
    match buf[i]? with
    | some (some t) => if t ∈ d then none else dropIdxRange buf k (i + 1) (t :: d)
    | _ => none
```

```lean
-- lean/PanicSafety/Forget.lean:79-81
def dropToks : List Tok → List Tok → Option (List Tok)
  | [], d => some d
  | t :: ts, d => if t ∈ d then none else dropToks ts (t :: d)
```

```lean
-- lean/PanicSafety/Forget.lean:84-120
def cstep (api : DrainApi) (s : CState) : CInstr → COut
  | .drain =>
    match s.guard with
    | some _ => .rejected
    | none =>
      .ok { s with guard := some (0, s.mem.len),
                   mem := if api = .leakAmplified then { s.mem with len := 0 } else s.mem }
  | .next =>
    match s.guard with
    | none => .rejected
    | some (c, e) =>
      if c < e then
        match s.mem.buf[c]? with
        | some (some t) => .ok { s with vals := t :: s.vals, guard := some (c + 1, e) }
        | _ => .ub
      else .ok s
  | .dropVal =>
    match s.vals with
    | [] => .rejected
    | t :: vs =>
      if t ∈ s.mem.dropped then .ub
      else .ok { s with vals := vs, mem := { s.mem with dropped := t :: s.mem.dropped } }
  | .forgetVal =>
    match s.vals with
    | [] => .rejected
    | _ :: vs => .ok { s with vals := vs }
  | .dropGuard =>
    match s.guard with
    | none => .rejected
    | some (c, e) =>
      match dropIdxRange s.mem.buf (e - c) c s.mem.dropped with
      | none => .ub
      | some d => .ok { s with guard := none, mem := { s.mem with dropped := d, len := 0 } }
  | .forgetGuard =>
    match s.guard with
    | none => .rejected
    | some _ => .ok { s with guard := none }
```

```lean
-- lean/PanicSafety/Forget.lean:124-137
def cend (s : CState) : COut :=
  match dropToks s.vals s.mem.dropped with
  | none => .ub
  | some d1 =>
    let afterGuard : Option (List Tok × Nat) :=
      match s.guard with
      | none => some (d1, s.mem.len)
      | some (c, e) => (dropIdxRange s.mem.buf (e - c) c d1).map fun d => (d, 0)
    match afterGuard with
    | none => .ub
    | some (d2, l) =>
      match containerDrop noPanicDtors { s.mem with dropped := d2, len := l } with
      | .ok d3 => .ok ⟨{ s.mem with dropped := d3, len := l }, [], none⟩
      | _ => .ub
```

```lean
-- lean/PanicSafety/Forget.lean:140-145
def crun (api : DrainApi) : List CInstr → CState → COut
  | [], s => cend s
  | i :: is, s =>
    match cstep api s i with
    | .ok s' => crun api is s'
    | o => o
```

```lean
-- lean/PanicSafety/Forget.lean:148-149
def clientRun (api : DrainApi) (prog : List CInstr) (m : Mem) : COut :=
  crun api prog ⟨m, [], none⟩
```

```lean
-- lean/PanicSafety/Forget.lean:152
def forgetClient : List CInstr := [.drain, .next, .dropVal, .forgetGuard]
```

```lean
-- lean/PanicSafety/Forget.lean:522
def tailFix (c n : Nat) : Guard := ⟨fun b _ => (copyRange (n - c) b c 0, n - c)⟩
```

```lean
-- lean/PanicSafety/Forget.lean:527-531
def drainWithLoop (n : Nat) : Nat → Nat → Prog
  | 0, _ => .popGuard .done
  | r + 1, c => .setGuard (tailFix (c + 1) n) (.readOut c (.call fun dropIt =>
      if dropIt then .dropVal (drainWithLoop n r (c + 1))
      else .forgetVal (drainWithLoop n r (c + 1))))
```

```lean
-- lean/PanicSafety/Forget.lean:535
def drainWith : Prog := .getLen fun n => .pushGuard (tailFix 0 n) (drainWithLoop n n 0)
```

Examples: `clientRun_rejected_example`, `clientRun_drainTwice_rejected`, `destructorReliantDrain_noForget_example`, `destructorReliantDrain_forgetVal_example`, `leakAmplifiedDrain_forgetClient_ok`.

#### Logical invariant

```lean
-- lean/PanicSafety/Logical.lean:18
def bumpBoth : Prog := .bumpA (.call fun _ => .bumpB .done)
```

```lean
-- lean/PanicSafety/Logical.lean:21
def CountersAgree (m : Mem) : Prop := m.ctrA = m.ctrB
```

Examples: `countersAgree_pos`, `countersAgree_neg`.

#### Concrete instances and bounded-check families

```lean
-- lean/PanicSafety/RetainResults.lean:1008
def ceMem1 : Mem := ⟨[some 0], 1, [], 0, 0⟩
```

```lean
-- lean/PanicSafety/RetainResults.lean:750
def ceMem2 : Mem := ⟨[some 0, some 1], 2, [], 0, 0⟩
```

```lean
-- lean/PanicSafety/RetainResults.lean:786
def ceMem3 : Mem := ⟨[some 0, some 1, some 2], 3, [], 0, 0⟩
```

```lean
-- lean/PanicSafety/RetainResults.lean:1142
def dupMem : Mem := ⟨[some 0, some 0], 2, [], 0, 0⟩
```

```lean
-- lean/PanicSafety/RetainResults.lean:770
def ceCbRemoveThenPanic : Callback := tableOf [.ret false, .panic]
```

```lean
-- lean/PanicSafety/RetainResults.lean:798
def ceCbRemoveKeepPanic : Callback := tableOf [.ret false, .ret true, .panic]
```

```lean
-- lean/PanicSafety/RetainResults.lean:1011
def ceCbRemove : Callback := tableOf [.ret false]
```

```lean
-- lean/PanicSafety/Examples.lean:164
def ceCbRemoveFirst : Callback := tableOf [.ret false, .ret true, .ret true]
```

```lean
-- lean/PanicSafety/RetainResults.lean:1014
def dtPanicsOn0 : DtorTable := dtOf [true]
```

```lean
-- lean/PanicSafety/Bounded.lean:17-19
def allBehs : Nat → List (List Beh)
  | 0 => [[]]
  | k + 1 => (allBehs k).flatMap fun l => [Beh.ret true :: l, Beh.ret false :: l, Beh.panic :: l]
```

```lean
-- lean/PanicSafety/Bounded.lean:22-24
def allBools : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 => (allBools k).flatMap fun l => [true :: l, false :: l]
```

```lean
-- lean/PanicSafety/Bounded.lean:27
def tableOf (bs : List Beh) : Callback := fun j => bs.getD j (.ret true)
```

```lean
-- lean/PanicSafety/Bounded.lean:30
def dtOf (ds : List Bool) : DtorTable := fun t => ds.getD t false
```

```lean
-- lean/PanicSafety/Bounded.lean:35-37
def testMems (n : Nat) : List Mem :=
  [⟨(List.range n).map some, n, [], 0, 0⟩,
   ⟨(List.range n).map some ++ [some 99], n, [99], 0, 0⟩]
```

```lean
-- lean/PanicSafety/RetainResults.lean:978-980
def smallBufs : List (List Cell) :=
  let cs : List Cell := [none, some 0, some 1]
  [[]] ++ cs.map (fun a => [a]) ++ cs.flatMap (fun a => cs.map fun b => [a, b])
```

```lean
-- lean/PanicSafety/RetainResults.lean:984-985
def smallMems : List Mem :=
  smallBufs.flatMap fun b => [0, 1, 2, 3].flatMap fun l => [[], [0]].map fun d => ⟨b, l, d, 0, 0⟩
```

```lean
-- lean/PanicSafety/Forget.lean:187-190
def allClients : Nat → List (List CInstr)
  | 0 => [[]]
  | k + 1 => (allClients k).flatMap fun p =>
      [.drain :: p, .next :: p, .dropVal :: p, .forgetVal :: p, .dropGuard :: p, .forgetGuard :: p]
```

```lean
-- lean/PanicSafety/Forget.lean:193
def clientTestMems : List Mem := testMems 0 ++ testMems 1 ++ testMems 2
```

```lean
-- lean/PanicSafety/Logical.lean:60-62
def charFamily : List (Callback × DtorTable × Mem) :=
  [0, 1, 2].flatMap fun n => (testMems n).flatMap fun m =>
    (allBehs (n + 1)).flatMap fun bs => (allBools n).map fun ds => (tableOf bs, dtOf ds, m)
```

```lean
-- lean/PanicSafety/Logical.lean:65-66
def BoundedPanicSafe (mode : Mode) (p : Prog) : Prop :=
  ∀ x ∈ charFamily, ResOk (run mode x.1 x.2.1 p x.2.2)
```

```lean
-- lean/PanicSafety/Logical.lean:72-73
def BoundedCallSitesDropSafe (p : Prog) : Prop :=
  ∀ x ∈ charFamily, ∀ s ∈ sites x.1 x.2.1 p x.2.2, DropSafe s.entries s.mem
```

```lean
-- lean/PanicSafety/Logical.lean:79-81
def samplePrograms : List Prog :=
  [rawRetain, leakRetain, guardRetain, guardRetainLate, drainWith, truncateLate,
   truncateThenCall, badSetLen, bumpBoth]
```

## Findings

Status legend: `[proved]` fully kernel-checked; `[bounded search]` a fully proved check over an explicitly listed finite family. Every card below is `[proved]`. Each card gives the Lean statement as a verbatim source quote with its `file:line` range (proofs elided), the plain-language claim, the hypothesis ledger, the depth label, the non-vacuity witness, prior art and the design question it informs, then two separate basis lines: the kernel-checked statement (`execution (Lean kernel check)`) and the connection to Rust (`derived (modeling bridge)`). Non-claims for every card are under **Boundaries**.

### R0. Adequacy of the drop-safety predicates `[proved]`

```lean
-- lean/PanicSafety/Facts.lean:57-58
theorem inv_iff_containerDrop_noPanic_ne_ub (m : Mem) :
    Inv m ↔ containerDrop noPanicDtors m ≠ .ub := by …
```

```lean
-- lean/PanicSafety/Facts.lean:103-104
theorem unwindEntries_noPanic_ok_inv_iff_dropSafe (es : List Entry) (m : Mem) :
    (∃ m', unwindEntries noPanicDtors es m = .ok m' ∧ Inv m') ↔ DropSafe es m := by …
```

- **Kind:** characterization. **Tier:** T0. **Depth:** shallow (inductions over lists).
- **Plain claim:** For every toy state `m`: `Inv m` holds iff the container's drop glue run with non-panicking destructors (`containerDrop noPanicDtors m`) does not reach UB. For every frame `es` and state `m`: `DropSafe es m` holds iff unwinding `es` from `m` with non-panicking destructors (`unwindEntries noPanicDtors es m`) ends in `.ok m'` for some `m'` satisfying `Inv`.
- **Hypothesis ledger:**
  - destructor table fixed to `noPanicDtors` (part of both statements) — With panicking destructors, drop glue can abort before reaching UB, and unwinding a drop-safe frame can abort. Tight (witness class: a two-cell state holding one value twice, and a one-local frame, with the destructor table `dtPanicsOn0`): counterexample `dropSafety_adequacy_fails_with_panickingDtors` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
- **Non-vacuity:** Both sides true: `containerDrop_pos` (on `ceMem2`, which satisfies `Inv`) and `dropSafe_pos_guardRepairs`; both sides false: `containerDrop_neg_doubleDrop` and `dropSafe_neg_localDuplicates`.
- **Prior art:**
  - The Rustonomicon, rust-lang/nomicon b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/exception-safety.md L25: 'We need only guarantee that it's a *safe* state.' derived (modeling bridge): `Inv` and `DropSafe` are the toy's 'safe state' predicates.
- **Design question:** What exactly must hold of the state that drop glue will see.
- **Non-claims:** see **Boundaries**, R0.

Basis: execution (Lean kernel check) — `inv_iff_containerDrop_noPanic_ne_ub`, `unwindEntries_noPanic_ok_inv_iff_dropSafe`.

Basis: derived (modeling bridge) — `Inv` and `DropSafe` play the role of the Rustonomicon's "safe state" (rust-lang/nomicon `b0bb5698`, src/exception-safety.md L25): the states on which drop glue may run without memory unsafety. The correspondence holds by construction of the toy (a container's drop glue drops its first `len` cells; a frame's drop glue applies guard fix-ups and drops live locals); no relation to Rust's semantics is proved.

### R1. Unwinding exposes the raw-move intermediate state `[proved]`

```lean
-- lean/PanicSafety/RetainResults.lean:776-782
theorem rawRetain_unwind_doubleDrop :
    Inv ceMem2 ∧
    run .unwind ceCbRemoveThenPanic noPanicDtors rawRetain ceMem2 =
      .unwound ⟨[some 0, some 1], 2, [0], 0, 0⟩ ∧
    ¬ Inv ⟨[some 0, some 1], 2, [0], 0, 0⟩ ∧
    harness .unwind ceCbRemoveThenPanic noPanicDtors rawRetain ceMem2 = .ub ∧
    run .abort ceCbRemoveThenPanic noPanicDtors rawRetain ceMem2 = .abort := by …
```

Second instance:

```lean
-- lean/PanicSafety/RetainResults.lean:802-806
theorem rawRetain_unwind_duplicate :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveKeepPanic noPanicDtors rawRetain ceMem3 =
      .unwound ⟨[some 1, some 1, some 2], 3, [0], 0, 0⟩ ∧
    harness .unwind ceCbRemoveKeepPanic noPanicDtors rawRetain ceMem3 = .ub := by …
```

- **Kind:** counterexample. **Tier:** T1. **Depth:** shallow (`decide` on one run).
- **Plain claim:** Under `unwind`, `rawRetain` run on the container `ceMem2` (values `0`, `1`; it satisfies `Inv`) with callback table `ceCbRemoveThenPanic` (remove element `0`, then panic) and non-panicking destructors unwinds to a state whose `len` still covers the dropped value `0`, which violates `Inv`, and the owner's drop of the container (`harness`) then reaches UB (value `0` dropped twice); under `abort` the same run aborts.
- **Hypothesis ledger:** none (a concrete instance).
- **Non-vacuity:** The instance itself; `rawRetain_unwind_duplicate` is a second instance in which a moved-out slot duplicates value `1`.
- **Prior art:**
  - Y. Bae, Y. Kim, A. Askar, J. Lim, T. Kim, 'Rudra: Finding Memory Safety Bugs in Rust at the Ecosystem Scale', SOSP 2021, pp. 84-99, doi:10.1145/3477132.3483570, Definition 3.1: 'A function F has a panic safety bug if it drops a value v of type T such that v ∉ safe-value(T) during unwinding and causes a memory safety violation.' derived (modeling bridge): the toy run has the shape 'invariant bypassed, user code panics before the fix-up, drop glue sees the inconsistent state'.
  - CVE-2020-36317, https://nvd.nist.gov/vuln/detail/CVE-2020-36317; rust-lang/rust issue 78498, https://github.com/rust-lang/rust/issues/78498; rust-lang/rust pull request 78499, https://github.com/rust-lang/rust/pull/78499. Cited by URL for context and described no further here; the toy does not model `String`.
  - The Rustonomicon, rust-lang/nomicon b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/exception-safety.md L20-22: 'Code that transiently creates unsound states must be careful that a panic does not cause that state to be used.'
- **Design question:** What must hold at each user-code call site (answered by R4).
- **Non-claims:** see **Boundaries**, R1.

Basis: execution (Lean kernel check) — `rawRetain_unwind_doubleDrop`, `rawRetain_unwind_duplicate`.

Basis: derived (modeling bridge) — The run has the shape of the panic-safety bug pattern of Rudra (SOSP 2021, Definition 3.1): an invariant is bypassed, user code panics before the fix-up, and drop glue runs on the inconsistent state. This is a correspondence of shape; no statement about any Rust standard-library function is made.

### R2. Raw moves are exactly correct under `abort` `[proved]`

```lean
-- lean/PanicSafety/RetainResults.lean:708-709
theorem rawRetain_abort_exact (cb : Callback) (dt : DtorTable) (m : Mem) (hm : Inv m) :
    RawAbortExact cb dt m := by …
```

Corollary:

```lean
-- lean/PanicSafety/RetainResults.lean:722
theorem rawRetain_panicSafe_abort : PanicSafe .abort rawRetain := by …
```

Bounded check `[bounded search]`:

```lean
-- lean/PanicSafety/RetainResults.lean:812-814
theorem rawRetain_abort_exact_upTo3 :
    ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, ∀ bs ∈ allBehs n, ∀ ds ∈ allBools n,
      RawAbortExact (tableOf bs) (dtOf ds) m := by …
```

- **Kind:** theorem. **Tier:** T1. **Depth:** substantive (loop invariant over the meta-level recursion of `rawLoop`).
- **Plain claim:** For every callback table `cb`, every destructor table `dt` and every entry state `m` satisfying `Inv`: `rawRetain` run under `abort` returns a state `m'` with `RetainReturns (specRetain cb dt (toks m.elems)) m m'` (the first `len` cells hold exactly the kept values in order, the removed values are prepended to the drop log, and `Inv m'` holds) if and only if the abstract run `specRetain` finishes; otherwise it aborts; it never reaches UB. Consequently (`rawRetain_panicSafe_abort`) `rawRetain` is panic-safe under `abort`.
- **Hypothesis ledger:**
  - `hm : Inv m` — The entry container is well-formed. Tight (witness class: a two-cell state holding one value twice, with a keep-everything callback): counterexample `rawRetain_abort_exact_needs_inv` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
  - panic mode `.abort` (fixed in `rawRetain_abort_exact`; the mode parameter of the corollary `rawRetain_panicSafe_abort`) — Under `abort` no drop glue runs after a panic, so the broken intermediate state is never observed. Tight (witness class: the same operation under `unwind` on a two-element container): counterexample `panicSafe_neg_rawRetain` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
- **Non-vacuity:** Abort branch: `rawAbortExact_pos` (three elements: remove, keep, panic). Return branch: `rawAbortExact_return_pos` (remove `0`, keep `1` and `2`). Both include `Inv ceMem3`.
- **Prior art:**
  - Rust std 1.85.0, std::panic::catch_unwind (https://doc.rust-lang.org/1.85.0/std/panic/fn.catch_unwind.html): 'This function only catches unwinding panics, not those that abort the process.' derived (modeling bridge).
  - RFC 1513, rust-lang/rfcs f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/1513-less-unwinding.md L9: 'Stabilize implementing panics as aborts.' and L143-144: 'For a final product (outputs that aren't rlibs) the `-C panic` mode of the panic runtime must match the final product itself.' derived (modeling bridge): in Rust the abort strategy is chosen for a whole build, not by a library; the toy's `abort` mode is a property of the run.
- **Design question:** Whether any repair pattern is needed under abort-on-panic: for `rawRetain`, no.
- **Non-claims:** see **Boundaries**, R2.

Basis: execution (Lean kernel check) — `rawRetain_abort_exact`, `rawRetain_panicSafe_abort`, `rawRetain_abort_exact_upTo3`.

Basis: derived (modeling bridge) — Under Rust's abort-on-panic strategy no drop glue runs after a panic, and `catch_unwind` does not catch aborting panics (std 1.85.0 `catch_unwind` documentation), so the broken intermediate state is not observed. RFC 1513 (L143-144) makes the strategy a property of the whole build rather than of a library, whereas the toy's `abort` mode is a property of one run.

### R3. Which panics expose the raw-move state `[proved]`

```lean
-- lean/PanicSafety/RetainResults.lean:734-736
theorem rawRetain_unwound_inv_iff_rejected_nil (cb : Callback) (dt : DtorTable) (m m' : Mem)
    (hm : Inv m) (h : run .unwind cb dt rawRetain m = .unwound m') :
    Inv m' ↔ (specRetain cb dt (toks m.elems)).rejected = [] := by …
```

Bounded check `[bounded search]`:

```lean
-- lean/PanicSafety/RetainResults.lean:764-766
theorem rawRetain_unwound_inv_iff_upTo3 :
    ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, ∀ bs ∈ allBehs n, ∀ ds ∈ allBools n,
      RawUnwoundIff (tableOf bs) (dtOf ds) m := by …
```

- **Kind:** characterization. **Tier:** T1. **Depth:** substantive (counting argument: after a removal, the `len` cells hold values of the entry container and cannot all be distinct and live).
- **Plain claim:** For every callback table, every destructor table and every entry state `m` satisfying `Inv`: if `rawRetain` under `unwind` unwinds to `m'`, then `m'` satisfies `Inv` iff the abstract retain removed no element up to and including the panic, i.e. `(specRetain cb dt (toks m.elems)).rejected = []` (a removed element whose destructor panics counts as removed).
- **Hypothesis ledger:**
  - `hm : Inv m` — The entry container is well-formed. Tight (witness class: a two-cell state holding one value twice, with a panic before any removal): counterexample `rawRetain_unwound_iff_needs_inv` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
  - `h : run .unwind cb dt rawRetain m = .unwound m'` — Binds `m'` to the unwound state of the run. Harmless.
- **Non-vacuity:** Right-hand side true and `Inv m'`: `rawRetain_unwind_noRemoval_example`; removal and `¬ Inv m'`: `rawRetain_unwind_doubleDrop`. Both start from states satisfying `Inv`.
- **Prior art:**
  - As R1 (Rudra Definition 3.1; CVE-2020-36317 cited by URL). derived (modeling bridge).
- **Design question:** Which user-code call sites in a raw-move loop are dangerous.
- **Non-claims:** see **Boundaries**, R3.

Basis: execution (Lean kernel check) — `rawRetain_unwound_inv_iff_rejected_nil`, `rawRetain_unwound_inv_iff_upTo3`.

Basis: derived (modeling bridge) — In a raw-move loop, the panics that expose the broken state are those that occur after a removal; this is the toy counterpart of Rudra's bug pattern (Definition 3.1) restricted to one loop shape. No statement about any Rust function is made.

### R4. Call-site characterization `[proved]`

```lean
-- lean/PanicSafety/Characterization.lean:637-638
theorem panicSafe_unwind_iff_abort_and_callSitesDropSafe (p : Prog) :
    PanicSafe .unwind p ↔ PanicSafe .abort p ∧ CallSitesDropSafe p := by …
```

Definitions of the right-hand side:

```lean
-- lean/PanicSafety/Characterization.lean:25-27
def CallSitesDropSafe (p : Prog) : Prop :=
  ∀ (cb : Callback) (dt : DtorTable) (m : Mem), Inv m →
    ∀ s ∈ sites cb dt p m, DropSafe s.entries s.mem
```

```lean
-- lean/PanicSafety/Basic.lean:361-365
def DropSafe (es : List Entry) (m : Mem) : Prop :=
  (applyGuards es (m.buf, m.len)).2 ≤ (applyGuards es (m.buf, m.len)).1.length ∧
  OwnsUniquely m.dropped
    ((valueToks es).map some ++
      (applyGuards es (m.buf, m.len)).1.take (applyGuards es (m.buf, m.len)).2)
```

Equivalent form of the destructor-table quantifier:

```lean
-- lean/PanicSafety/Characterization.lean:786-789
theorem callSitesDropSafe_iff_noPanicDtors (p : Prog) :
    CallSitesDropSafe p ↔
      ∀ (cb : Callback) (m : Mem), Inv m →
        ∀ s ∈ sites cb noPanicDtors p m, DropSafe s.entries s.mem := by …
```

Bounded check `[bounded search]`:

```lean
-- lean/PanicSafety/Logical.lean:86-88
theorem characterization_bounded_samples :
    ∀ p ∈ samplePrograms,
      (BoundedPanicSafe .unwind p ↔ BoundedPanicSafe .abort p ∧ BoundedCallSitesDropSafe p) := by …
```

- **Kind:** characterization. **Tier:** T1. **Depth:** substantive (right to left by induction on `Prog`; left to right by table surgery at the site (a panicking callback invocation, or a destructor that panics on exactly one value)).
- **Plain claim:** For every toy program `p`: `p` is panic-safe under `unwind` (for every callback table, destructor table and entry state satisfying `Inv`, the run `run .unwind cb dt p m` reaches no UB and a return or an unwind leaves `Inv`) iff (a) `p` is panic-safe under `abort`, and (b) for every callback table, destructor table and entry state satisfying `Inv`, every user-code site reached by `p` (callback invocations and element-destructor invocations, as produced by the interpreter `exec` through `sites`) satisfies `DropSafe`: after the frame's guard fix-ups are applied to `(buf, len)`, the fixed-up `len` is at most the buffer length, and the values of the live locals together with the first `len` cells of the fixed-up buffer are initialized, pairwise distinct and not in the drop log. `run` and `sites` start the interpreter with an empty frame, and guard fix-ups are pure functions of `(buf, len)`.
- **Hypothesis ledger:**
  - `PanicSafe .abort p (right-hand-side conjunct)` — The normal-execution path must itself be correct; call sites do not see it. Tight (witness class: a program with no user-code site (`badSetLen`)): counterexample `badSetLen_callSitesDropSafe_not_panicSafe` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
  - `CallSitesDropSafe p, including destructor sites (right-hand-side conjunct)` — Unwinding may start at any user-code call, including element destructors. Tight (witness class: a two-instruction program with one destructor site (`truncateLate`) and a one-element container): counterexample `truncateLate_counterexample` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
  - `entry precondition Inv m inside CallSitesDropSafe` — Sites reached from states violating `Inv` are irrelevant to panic safety, which also assumes `Inv` on entry. Tight (witness class: a two-cell entry state holding one value twice): counterexample `truncateThenCall_sites_need_inv` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
  - `quantifier over all destructor tables inside CallSitesDropSafe` — Readability; equivalent to fixing `noPanicDtors` (`callSitesDropSafe_iff_noPanicDtors`). Harmless.
- **Non-vacuity:** Both sides hold: `truncateThenCall_satisfies_both_sides` (with one destructor site and one callback site, `truncateThenCall_sites_example`). Both sides fail: `rawRetain_not_callSitesDropSafe` and `panicSafe_neg_rawRetain`.
- **Prior art:**
  - The Rustonomicon, rust-lang/nomicon b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/exception-safety.md L20-22: 'Code that transiently creates unsound states must be careful that a panic does not cause that state to be used.' derived (modeling bridge).
  - Rudra (SOSP 2021, doi:10.1145/3477132.3483570), section 3.1, describes the same obligation as a bug pattern (Definition 3.1). derived (modeling bridge).
  - RustBelt (R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, PACMPL 2(POPL) article 66, 2018, doi:10.1145/3158154), section 9: 'We do not model … (3) stack unwinding when a panic occurs'.
  - RefinedRust (L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer, PACMPL 8(PLDI), 2024, doi:10.1145/3656422): an overflowing addition that would 'trigger a panic and abort program execution', and 'RefinedRust also verifies that no panics occur'; the text extracted from the paper PDF contains no occurrence of 'unwind'.
  - Aeneas (S. Ho, J. Protzenko, PACMPL 6(ICFP), 2022, doi:10.1145/3547647, arXiv:2206.07185): a panic is an 'unrecoverable error', and 'First, we ignore the drop nodes from MIR'; the text extracted from the arXiv PDF contains no occurrence of 'unwind'.
  - MiniRust, minirust/minirust 063d784186d3252bee242217f218223205c0b568, spec/lang/step/terminators.md: an executable operational semantics that models unwinding with the terminators `StartUnwind`, `StopUnwind` and `ResumeUnwind`.
  - The Rust Reference, rust-lang/reference c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/behavior-considered-undefined.md L56: 'unwinding past a stack frame that does not allow unwinding' is listed as undefined behaviour.
- **Design question:** What exactly must hold at each user-code call site: drop-safety of the frame's unwinding footprint, at destructor calls as well as closure calls.
- **Non-claims:** see **Boundaries**, R4.

Basis: execution (Lean kernel check) — `panicSafe_unwind_iff_abort_and_callSitesDropSafe`, `callSitesDropSafe_iff_noPanicDtors`, `characterization_bounded_samples`.

Basis: derived (modeling bridge) — The Rustonomicon requires that transiently unsound states not be used after a panic (src/exception-safety.md L20-22); R4 states the toy version of this obligation per user-code call site. Element destructors count as call sites because Rust drop glue runs user `Drop` implementations. The characterization is proved for toy programs with pure guard fix-ups; whether it transfers to Rust is not proved.

### R5. Destructor sites count as call sites `[proved]`

```lean
-- lean/PanicSafety/Characterization.lean:867-869
theorem truncateLate_counterexample :
    PanicSafe .abort truncateLate ∧ CallbackSitesDropSafe truncateLate ∧
    ¬ CallSitesDropSafe truncateLate ∧ ¬ PanicSafe .unwind truncateLate := by …
```

Companion facts: the site structure of `truncateLate` and the destructor-panic run used in the proof above (they do not change its statement):

```lean
-- lean/PanicSafety/Witnesses.lean:19-20
theorem truncateLate_sites_destructor (cb : Callback) (dt : DtorTable) (m : Mem) :
    ∀ s ∈ sites cb dt truncateLate m, s.kind = .destructor := by …
```

```lean
-- lean/PanicSafety/Witnesses.lean:45-48
theorem truncateLate_dtorPanic_unwound (cb : Callback) :
    Inv ceMem1 ∧
    run .unwind cb dtPanicsOn0 truncateLate ceMem1 = .unwound ⟨[some 0], 1, [0], 0, 0⟩ ∧
    ¬ Inv ⟨[some 0], 1, [0], 0, 0⟩ := …
```

- **Kind:** counterexample. **Tier:** T1. **Depth:** shallow.
- **Plain claim:** The program `truncateLate` (drop the last element, then decrement `len`) is panic-safe under `abort` and satisfies `CallbackSitesDropSafe`, yet it fails `CallSitesDropSafe` and is not panic-safe under `unwind` (`truncateLate_counterexample`). From every state (not only states satisfying `Inv`), under every callback table and every destructor table, every user-code site that `truncateLate` reaches (as produced by `exec` through `sites`) is an element-destructor site, so it reaches no callback site (`truncateLate_sites_destructor`). On the one-element container `ceMem1`, which satisfies `Inv`, with the destructor table `dtPanicsOn0`, under `unwind` and every callback table, `truncateLate` unwinds to the state `⟨[some 0], 1, [0], 0, 0⟩` (buffer `[some 0]`, `len = 1`, drop log `[0]`): the panicking destructor leaves `len` covering the cell of the dropped value `0`, and that state violates `Inv` (`truncateLate_dtorPanic_unwound`).
- **Hypothesis ledger:** none (`truncateLate_counterexample` is a statement about one program; the companion facts quantify over callback tables, destructor tables and states without hypotheses).
- **Non-vacuity:** The statement has no hypotheses. The destructor-panic run behind its `¬ PanicSafe .unwind truncateLate` conjunct, on `ceMem1` (which satisfies `Inv`) with `dtPanicsOn0`, is stated by `truncateLate_dtorPanic_unwound`.
- **Prior art:**
  - Rust 1.85.0 (rust-lang/rust 4d91de4e48198da2e33413efdcd9cd2cc0c46688), library/alloc/src/vec/mod.rs L1528-1530, `Vec::truncate` comment: 'the `len` of the vector is shrunk before calling `drop_in_place`, such that no value will be dropped twice in case `drop_in_place` were to panic once (if it panics twice, the program aborts).' derived (modeling bridge).
- **Design question:** Which user-code calls count as call sites: element destructors do.
- **Non-claims:** see **Boundaries**, R5.

Basis: execution (Lean kernel check) — `truncateLate_counterexample`, `truncateLate_sites_destructor`, `truncateLate_dtorPanic_unwound`.

Basis: derived (modeling bridge) — The std 1.85.0 `Vec::truncate` comment (rust-lang/rust `4d91de4e`, library/alloc/src/vec/mod.rs L1528-1530) shrinks `len` before `drop_in_place` for the reason the toy exhibits: a panicking destructor must not leave the dropped value inside `len`.

### R6. Leak amplification is sound but leaks `[proved]`

```lean
-- lean/PanicSafety/RetainResults.lean:821-822
theorem leakRetain_unwind_exact (cb : Callback) (dt : DtorTable) (m : Mem) (hm : Inv m) :
    LeakUnwindExact cb dt m := by …
```

Corollaries:

```lean
-- lean/PanicSafety/RetainResults.lean:839
theorem leakRetain_panicSafe_unwind : PanicSafe .unwind leakRetain := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:858-861
theorem leakRetain_unwound_leaks (cb : Callback) (dt : DtorTable) (m m' : Mem) (hm : Inv m)
    (h : run .unwind cb dt leakRetain m = .unwound m') :
    toks m'.elems = [] ∧
    ∀ t ∈ toks m.elems, (t ∈ m'.dropped ↔ t ∈ (specRetain cb dt (toks m.elems)).rejected) := by …
```

Bounded check `[bounded search]`:

```lean
-- lean/PanicSafety/RetainResults.lean:885-887
theorem leakRetain_unwind_exact_upTo3 :
    ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, ∀ bs ∈ allBehs n, ∀ ds ∈ allBools n,
      LeakUnwindExact (tableOf bs) (dtOf ds) m := by …
```

- **Kind:** theorem. **Tier:** T1. **Depth:** substantive (the raw-move loop invariant with `len = 0` throughout).
- **Plain claim:** For every callback table, every destructor table (panicking destructors included) and every entry state `m` satisfying `Inv`: `leakRetain` (set `len := 0`, run the raw loop, restore `len`) under `unwind` returns a state satisfying `RetainReturns (specRetain cb dt (toks m.elems)) m` if and only if `specRetain` finishes; otherwise it unwinds to a state with `len = 0`, drop log equal to the abstract `rejected` list prepended to the entry drop log, and unchanged buffer length and counters; it never aborts or reaches UB. Consequently it is panic-safe under `unwind` (`leakRetain_panicSafe_unwind`), and (`leakRetain_unwound_leaks`, same hypotheses, for an unwound state `m'`) the first `len` cells of `m'` hold no value and an entry value is in the drop log of `m'` iff the abstract retain removed it; so every entry value that was not removed is leaked (neither in the drop log nor held by the container).
- **Hypothesis ledger:**
  - `hm : Inv m (leakRetain_unwind_exact)` — The entry container is well-formed. Tight (witness class: a two-cell state holding one value twice, with a keep-everything callback): counterexample `leakRetain_unwind_exact_needs_inv` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
  - `hm : Inv m (leakRetain_unwound_leaks)` — Entry values must not already be in the drop log. Tight (witness class: a one-element container whose value is already in the drop log, with a panic before any removal): counterexample `leakRetain_unwound_leaks_needs_inv` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
  - `h : run .unwind cb dt leakRetain m = .unwound m' (leakRetain_unwound_leaks)` — Binds `m'` to the unwound state of the run. Harmless.
- **Non-vacuity:** Unwind branch: `leakRetain_unwind_example` (remove, keep, panic; values `1` and `2` leaked) and `leakUnwindExact_pos`; return branch: `leakUnwindExact_return_pos`. All include `Inv ceMem3`.
- **Prior art:**
  - The Rustonomicon, rust-lang/nomicon b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/leaking.md L98-100: 'set the Vec's len to be 0 when we start the iteration, and fix it up if necessary in the destructor'; L104-105: 'We call leaks causing more leaks a *leak amplification*.'
  - rust-lang/rust pull request 78499, https://github.com/rust-lang/rust/pull/78499, cited by URL for context (compare R1).
  - 'Pre-Pooping Your Pants With Rust', blog post dated April 27, 2015, https://faultlore.com/blah/everyone-poops/ (author credited on the page as Aria Desires; unpinned page).
  - Rust 1.85.0 (rust-lang/rust 4d91de4e48198da2e33413efdcd9cd2cc0c46688), library/alloc/src/vec/mod.rs L2132-2134 (`retain_mut`): '// Avoid double drop if the drop guard is not executed,' / '// since we may make some holes during the process.' followed by `unsafe { self.set_len(0) };`. derived (modeling bridge).
- **Design question:** What leak amplification costs: every kept and unprocessed element is lost on panic.
- **Non-claims:** see **Boundaries**, R6.

Basis: execution (Lean kernel check) — `leakRetain_unwind_exact`, `leakRetain_panicSafe_unwind`, `leakRetain_unwound_leaks`, `leakRetain_unwind_exact_upTo3`.

Basis: derived (modeling bridge) — The Rustonomicon's leak amplification (src/leaking.md L98-100, L104-105) and the `set_len(0)` in std 1.85.0 `retain_mut` (library/alloc/src/vec/mod.rs L2132-2134) set `len` to 0 before running user code, as `leakRetain` does. The toy result says what this costs in the toy: every kept and unprocessed value is lost on a panic.

### R7. A drop guard updated before each destructor is exact on unwind `[proved]`

```lean
-- lean/PanicSafety/RetainResults.lean:895-896
theorem guardRetain_unwind_exact (cb : Callback) (dt : DtorTable) (m : Mem) (hm : Inv m) :
    GuardUnwindExact cb dt m := by …
```

Corollary:

```lean
-- lean/PanicSafety/RetainResults.lean:931
theorem guardRetain_panicSafe_unwind : PanicSafe .unwind guardRetain := by …
```

Bounded check `[bounded search]`:

```lean
-- lean/PanicSafety/RetainResults.lean:940-942
theorem guardRetain_unwind_exact_upTo3 :
    ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, ∀ bs ∈ allBehs n, ∀ ds ∈ allBools n,
      GuardUnwindExact (tableOf bs) (dtOf ds) m := by …
```

- **Kind:** theorem. **Tier:** T1. **Depth:** substantive (loop invariant plus a memmove lemma for `copyRange`).
- **Plain claim:** For every callback table, every destructor table (panicking destructors included) and every entry state `m` satisfying `Inv`: `guardRetain` (a back-shift guard whose fields are updated before each removed element's destructor runs) under `unwind` returns a state satisfying `RetainReturns (specRetain cb dt (toks m.elems)) m` if and only if `specRetain` finishes; otherwise it unwinds to a state `m'` whose first `len` cells hold exactly the kept values followed by the unprocessed values (`toks m'.elems = kept ++ rest`), with drop log `rejected ++ m.dropped` and `Inv m'`; it never aborts or reaches UB.
- **Hypothesis ledger:**
  - `hm : Inv m` — The entry container is well-formed. Tight (witness class: a two-cell state holding one value twice, with a keep-everything callback): counterexample `guardRetain_unwind_exact_needs_inv` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
- **Non-vacuity:** Unwind branch: `guardRetain_unwind_example` (callback panic after a removal and a move) and `guardRetain_dtorPanic_example` (destructor panic); return branch: `guardUnwindExact_return_pos`. All include `Inv` of the entry state.
- **Prior art:**
  - Rust 1.85.0 (rust-lang/rust 4d91de4e48198da2e33413efdcd9cd2cc0c46688), library/alloc/src/vec/mod.rs L2147-2190 (`retain_mut`, `BackshiftOnDrop`): the guard's `Drop` copies the unprocessed tail down by `deleted_cnt` and sets `len` to `original_len - deleted_cnt`; L2186: 'Advance early to avoid double drop if `drop_in_place` panicked.'; L2187-2190 advance the counters and then call `ptr::drop_in_place(cur)`. derived (modeling bridge).
  - Rust std 1.85.0, `Drop` documentation (https://doc.rust-lang.org/1.85.0/std/ops/trait.Drop.html): 'if the drop() panics in that situation (a “double panic”), this will likely abort the program', and 'Note that even if this panics, the value is considered to be dropped'. derived (modeling bridge), hedged ('likely'); the Rust Reference at rust-lang/reference c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c states no such rule in src/panic.md or src/destructors.md.
- **Design question:** Whether drop guards are sound under unwinding, and under what hypothesis on destructors.
- **Non-claims:** see **Boundaries**, R7.

Basis: execution (Lean kernel check) — `guardRetain_unwind_exact`, `guardRetain_panicSafe_unwind`, `guardRetain_unwind_exact_upTo3`.

Basis: derived (modeling bridge) — The `BackshiftOnDrop` guard of std 1.85.0 `retain_mut` (library/alloc/src/vec/mod.rs L2147-2171) copies the unprocessed tail down and sets `len` on drop, and the loop advances the guard's counter before `drop_in_place` (L2186), as `guardRetain` updates its guard before each destructor. The toy guard omits the `set_len(0)` that `retain_mut` also performs (see Boundaries).

### R8. The guard is leak-free on unwind `[proved]`

```lean
-- lean/PanicSafety/RetainResults.lean:948-949
theorem guardRetain_unwound_leakFree (cb : Callback) (dt : DtorTable) (m m' : Mem)
    (hm : Inv m) (h : run .unwind cb dt guardRetain m = .unwound m') : LeakFree m m' := by …
```

The same conclusion without `Inv m` (it makes the hypothesis `hm` harmless; see the ledger):

```lean
-- lean/PanicSafety/LeakFreeNoInv.lean:182-183
theorem guardRetain_unwound_leakFree_noInv (cb : Callback) (dt : DtorTable) (m m' : Mem)
    (h : run .unwind cb dt guardRetain m = .unwound m') : LeakFree m m' := …
```

Bounded checks `[bounded search]` (the second one omits `Inv m`):

```lean
-- lean/PanicSafety/RetainResults.lean:972-974
theorem guardRetain_unwound_leakFree_upTo3 :
    ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, ∀ bs ∈ allBehs n, ∀ ds ∈ allBools n,
      GuardUnwoundLeakFree (tableOf bs) (dtOf ds) m := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:992-994
theorem guardRetain_unwound_leakFree_noInv_bounded :
    ∀ m ∈ smallMems, ∀ bs ∈ allBehs 3, ∀ ds ∈ allBools 2,
      GuardUnwoundLeakFree (tableOf bs) (dtOf ds) m := by …
```

- **Kind:** theorem. **Tier:** T1. **Depth:** shallow (corollary of R7 plus the fact that the abstract retain loses no element (`grd_absRetain_mem`)).
- **Plain claim:** For every callback table, every destructor table and every entry state `m` satisfying `Inv`: if `guardRetain` under `unwind` unwinds to `m'`, then every value held by the first `len` cells of `m` is in the drop log of `m'` or held by the first `len` cells of `m'` (`LeakFree m m'`).
- **Hypothesis ledger:**
  - `hm : Inv m` — Retained for meaning, not needed for the implication: `guardRetain_unwound_leakFree_noInv` proves the same conclusion for every entry state. Without `Inv m`, `LeakFree` no longer expresses 'no element is lost': a value already in the entry drop log, or one of two copies of a duplicated value, satisfies it trivially. Harmless.
  - `h : run .unwind cb dt guardRetain m = .unwound m'` — Binds `m'` to the unwound state of the run. Harmless.
- **Non-vacuity:** `guardRetain_unwind_example` (entry `ceMem3` satisfies `Inv`; callback panic after a removal and a move).
- **Prior art:**
  - D. Abrahams, 'Exception-Safety in Generic Components', in Generic Programming, LNCS 1766, Springer 2000, pp. 69-79, doi:10.1007/3-540-39953-4_6 (full text not inspected). The guarantee wording is quoted from the version hosted by Boost, boostorg/website 5946dc4e147a8a7738ac5f2be7c84c4c4762112e, community/exception_safety.html L224-225: 'The *basic* guarantee: that the invariants of the component are preserved, and no resources are leaked.' (identity with the LNCS wording not verified). derived (modeling bridge): R7 with R8 is the toy analogue of the basic guarantee for this operation.
- **Design question:** What drop guards cost compared with leak amplification: no element is lost.
- **Non-claims:** see **Boundaries**, R8.

Basis: execution (Lean kernel check) — `guardRetain_unwound_leakFree`, `guardRetain_unwound_leakFree_noInv`, `guardRetain_unwound_leakFree_upTo3`, `guardRetain_unwound_leakFree_noInv_bounded`.

Basis: derived (modeling bridge) — R7 together with R8 is the toy analogue, for this operation, of Abrahams' basic guarantee ("the invariants of the component are preserved, and no resources are leaked"); the correspondence is informal.

### R9. A guard updated after each destructor is panic-safe when no destructor panics `[proved]`

```lean
-- lean/PanicSafety/RetainResults.lean:1098-1099
theorem guardRetainLate_panicSafe_unwind_of_noPanickingDtors :
    PanicSafeAssumingNoDtorPanic .unwind guardRetainLate := by …
```

Bounded check `[bounded search]`:

```lean
-- lean/PanicSafety/RetainResults.lean:1124-1126
theorem guardRetainLate_panicSafe_upTo3 :
    ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, ∀ bs ∈ allBehs n,
      ResOk (run .unwind (tableOf bs) noPanicDtors guardRetainLate m) := by …
```

- **Kind:** theorem. **Tier:** T1. **Depth:** shallow (with non-panicking destructors the late loop has the same outcome as the early loop (`guardLoopLate_eq_guardLoop_of_noPanickingDtors`), then R7).
- **Plain claim:** For every callback table, every destructor table in which no destructor panics (`NoPanickingDtors dt`), and every entry state satisfying `Inv`: `guardRetainLate` (the back-shift guard updated after each removed element's destructor returns) under `unwind` reaches no UB, and a return or an unwind leaves `Inv`.
- **Hypothesis ledger:**
  - `NoPanickingDtors dt (inside PanicSafeAssumingNoDtorPanic)` — A destructor panic between the drop and the guard update leaves the guard's fields stale. Tight (witness class: a one-element container whose destructor panics (`dtPanicsOn0`)): counterexample `guardRetainLate_dtorPanic_counterexample` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
  - `Inv m (inside PanicSafeAssumingNoDtorPanic)` — The entry container is well-formed. Tight (witness class: a two-cell state holding one value twice, with non-panicking destructors): counterexample `guardRetainLate_needs_inv` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
- **Non-vacuity:** `guardRetainLate_noPanic_example` (non-panicking table, entry `ceMem3` satisfying `Inv`, callback panic after a removal).
- **Prior art:**
  - CVE-2021-31162, https://nvd.nist.gov/vuln/detail/CVE-2021-31162; rust-lang/rust issue 83618, https://github.com/rust-lang/rust/issues/83618; rust-lang/rust pull request 83629, https://github.com/rust-lang/rust/pull/83629. Cited by URL for context and described no further here.
- **Design question:** Element destructors are user code: updating guard bookkeeping before them suffices (R7); updating it after them suffices when no destructor panics (R9) and fails for the destructor table `dtPanicsOn0`.
- **Non-claims:** see **Boundaries**, R9.

Basis: execution (Lean kernel check) — `guardRetainLate_panicSafe_unwind_of_noPanickingDtors`, `guardRetainLate_panicSafe_upTo3`.

Basis: derived (modeling bridge) — Element destructors are user code and may panic (std 1.85.0 `Drop` documentation: "Note that even if this panics, the value is considered to be dropped"); a guard whose bookkeeping is updated after the destructor returns relies on destructors not panicking. No standard-library code path is identified.

### R11. The toy destructor-reliant drain reaches UB once `forgetGuard` is available `[proved]`

```lean
-- lean/PanicSafety/Forget.lean:157-159
theorem destructorReliantDrain_forget_reachesUB :
    Inv ceMem1 ∧ CInstr.forgetGuard ∈ forgetClient ∧
    clientRun .destructorReliant forgetClient ceMem1 = .ub := by …
```

Same client, leak-amplified drain:

```lean
-- lean/PanicSafety/Forget.lean:164-166
theorem leakAmplifiedDrain_forgetClient_ok :
    Inv ceMem1 ∧
    clientRun .leakAmplified forgetClient ceMem1 = .ok ⟨⟨[some 0], 0, [0], 0, 0⟩, [], none⟩ := by …
```

- **Kind:** counterexample. **Tier:** T1. **Depth:** shallow (`decide` on one run).
- **Plain claim:** In the toy client language, all of whose instructions are safe operations, the client `forgetClient` = `[.drain, .next, .dropVal, .forgetGuard]` (drain, take one value, drop it, forget the guard) run against the destructor-reliant drain on the one-element container `ceMem1` (which satisfies `Inv`) reaches UB (the owner's drop drops value `0` a second time).
- **Hypothesis ledger:** none (a concrete instance).
- **Non-vacuity:** The instance itself; `leakAmplifiedDrain_forgetClient_ok` runs the same client against the leak-amplified drain without UB.
- **Positive controls (nearby settings where the conclusion fails):** `leakAmplifiedDrain_noUB`, `destructorReliantDrain_noUB_withoutForgetGuard`, `closureScopedDrain_panicSafe_unwind` (R12, R13, R14). R12 and R13 are about the client language; R14 is about `drainWith`, a program of `Prog` (not of the client language), in which user code is a callback table and has no instruction that reaches the library's guard.
- **Prior art:**
  - RFC 1066, rust-lang/rfcs f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/1066-safe-mem-forget.md L9-10: 'Explicitly state that it is not considered unsafe behavior to not run destructors.'
  - rust-lang/rust issue 24292, https://github.com/rust-lang/rust/issues/24292 (2015), cited by URL for context.
  - The Rustonomicon, rust-lang/nomicon b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/leaking.md L36-37: 'However *unsafe* code cannot rely on destructors to be run in order to be safe.'
  - The Rust Reference, rust-lang/reference c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/behavior-not-considered-unsafe.md L6: 'Leaks of memory and other resources' and L7: 'Exiting without calling destructors'.
  - Rust std 1.85.0, `std::mem::forget` documentation (source rust-lang/rust 4d91de4e48198da2e33413efdcd9cd2cc0c46688, library/core/src/mem/mod.rs L52-53): 'Because forgetting a value is allowed, any `unsafe` code you write must allow for this possibility.' derived (modeling bridge).
  - Rust std 1.85.0, std::pin module documentation, section 'Drop guarantee' (https://doc.rust-lang.org/1.85.0/std/pin/index.html): 'in any situation where we may want to overwrite a pinned value, that value’s drop must be called beforehand' and 'leaking memory in such a way that its underlying storage will never get invalidated or re-used is still fine'.
  - J. A. Tov, R. Pucella, 'Practical affine types', POPL 2011, pp. 447-458, doi:10.1145/1926385.1926436 (metadata verified; full text not inspected); A. Desires, 'The Pain Of Real Linear Types in Rust', blog post dated May 8, 2017, https://faultlore.com/blah/linear-rust/ (unpinned page).
- **Design question:** What a safe API can never rely on: that a destructor of a value handed to safe code runs.
- **Non-claims:** see **Boundaries**, R11.

Basis: execution (Lean kernel check) — `destructorReliantDrain_forget_reachesUB`, `leakAmplifiedDrain_forgetClient_ok`.

Basis: derived (modeling bridge) — RFC 1066 (text/1066-safe-mem-forget.md L9-10), the Rust Reference (src/behavior-not-considered-unsafe.md L6-7) and the Rustonomicon (src/leaking.md L36-37) state that not running destructors is not unsafe in Rust; `forgetGuard` is the toy's safe way to skip a guard's destructor. The toy run is one client of one toy API.

### R12. The leak-amplified drain reaches no UB under safe `forget` `[proved]`

```lean
-- lean/PanicSafety/Forget.lean:507-508
theorem leakAmplifiedDrain_noUB (prog : List CInstr) (m : Mem) (hm : Inv m) :
    clientRun .leakAmplified prog m ≠ .ub := …
```

Bounded check `[bounded search]`:

```lean
-- lean/PanicSafety/Forget.lean:198-200
theorem leakAmplifiedDrain_noUB_upTo4 :
    ∀ k ∈ [0, 1, 2, 3, 4], ∀ prog ∈ allClients k, ∀ m ∈ clientTestMems,
      clientRun .leakAmplified prog m ≠ .ub := by …
```

Leak witness (cited in the non-claims):

```lean
-- lean/PanicSafety/Witnesses.lean:55-59
theorem leakAmplifiedDrain_forgetGuard_leaks :
    Inv ceMem1 ∧
    clientRun .leakAmplified [.drain, .forgetGuard] ceMem1 =
      .ok ⟨⟨[some 0], 0, [], 0, 0⟩, [], none⟩ ∧
    ¬ LeakFree ceMem1 ⟨[some 0], 0, [], 0, 0⟩ := by …
```

- **Kind:** theorem. **Tier:** T1. **Depth:** substantive (client-state invariant `DrainClientInv` preserved by every instruction).
- **Plain claim:** For every client program `prog` and every entry state `m` satisfying `Inv`: running `prog` against the leak-amplified drain (`clientRun .leakAmplified prog m`) does not reach UB; the run completes (`.ok`) or is rejected as ill-typed (`.rejected`, a compile error in the toy).
- **Hypothesis ledger:**
  - `hm : Inv m` — The entry container is well-formed. Tight (witness class: the empty program on a two-cell state holding one value twice): counterexample `drainClients_need_inv` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
- **Non-vacuity:** `leakAmplifiedDrain_forgetClient_ok` (entry `ceMem1` satisfies `Inv`; the program completes).
- **Prior art:**
  - As R6 and R11 (Rustonomicon 'Leaking', drain). derived (modeling bridge).
- **Design question:** Which repair makes a guard-returning API sound under safe leaking.
- **Non-claims:** see **Boundaries**, R12.

Basis: execution (Lean kernel check) — `leakAmplifiedDrain_noUB`, `leakAmplifiedDrain_noUB_upTo4`; the leak witness `leakAmplifiedDrain_forgetGuard_leaks`.

Basis: derived (modeling bridge) — The leak-amplified drain corresponds to the Rustonomicon's `Vec::drain` design (src/leaking.md L98-100): `len` is set to 0 before the guard is handed out, so forgetting the guard leaks values but cannot cause a double drop. In the toy, `leakAmplifiedDrain_noUB` excludes UB (a double drop included), and `leakAmplifiedDrain_forgetGuard_leaks` exhibits one run in which forgetting the guard leaks a value; a general statement about which values leak is not proved here.

### R13. Without `forgetGuard`, the destructor-reliant drain reaches no UB `[proved]`

```lean
-- lean/PanicSafety/Forget.lean:513-515
theorem destructorReliantDrain_noUB_withoutForgetGuard (prog : List CInstr) (m : Mem) (hm : Inv m)
    (hforget : CInstr.forgetGuard ∉ prog) :
    clientRun .destructorReliant prog m ≠ .ub := …
```

Bounded check `[bounded search]`:

```lean
-- lean/PanicSafety/Forget.lean:207-209
theorem destructorReliantDrain_noUB_withoutForgetGuard_upTo4 :
    ∀ k ∈ [0, 1, 2, 3, 4], ∀ prog ∈ allClients k, ∀ m ∈ clientTestMems,
      CInstr.forgetGuard ∉ prog → clientRun .destructorReliant prog m ≠ .ub := by …
```

- **Kind:** theorem. **Tier:** T1. **Depth:** substantive (the client-state invariant of R12, with the `forgetGuard` case excluded).
- **Plain claim:** For every client program `prog` that does not contain `forgetGuard` (it may contain `forgetVal`) and every entry state `m` satisfying `Inv`: running `prog` against the destructor-reliant drain does not reach UB; the run completes or is rejected as ill-typed.
- **Hypothesis ledger:**
  - `hm : Inv m` — The entry container is well-formed. Tight (witness class: the empty program on a two-cell state holding one value twice): counterexample `drainClients_need_inv` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
  - `hforget : CInstr.forgetGuard ∉ prog` — Forgetting the guard skips the destructor the API relies on. Tight (witness class: a four-instruction client on a one-element container): counterexample `destructorReliantDrain_forget_reachesUB` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
- **Non-vacuity:** `destructorReliantDrain_noForget_example` (entry `ceMem1` satisfies `Inv`; the program has no `forgetGuard`); `destructorReliantDrain_forgetVal_example` (a program using `forgetVal`).
- **Prior art:**
  - The Rustonomicon, rust-lang/nomicon b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/leaking.md L31-33: 'there are many ways to fail to call a destructor in safe code. The most famous example is creating a cycle of reference-counted pointers using interior mutability.' and L36-37: 'However *unsafe* code cannot rely on destructors to be run in order to be safe.' derived (modeling bridge).
  - Rust std 1.85.0, `std::mem::forget` documentation (source rust-lang/rust 4d91de4e48198da2e33413efdcd9cd2cc0c46688, library/core/src/mem/mod.rs L41-44), section 'Safety'. derived (modeling bridge).
  - rust-lang/rust issue 24292, https://github.com/rust-lang/rust/issues/24292, cited by URL for context.
- **Design question:** Confirms that, in the toy, the guard-forgetting operation is what breaks destructor-reliant soundness.
- **Non-claims:** see **Boundaries**, R13.

Basis: execution (Lean kernel check) — `destructorReliantDrain_noUB_withoutForgetGuard`, `destructorReliantDrain_noUB_withoutForgetGuard_upTo4`.

Basis: derived (modeling bridge) — The result isolates guard-forgetting as the operation that breaks destructor-reliant soundness in the toy. In Rust a value can be leaked without `mem::forget` (std 1.85.0 `mem::forget` documentation, library/core/src/mem/mod.rs L41-44; Rustonomicon src/leaking.md L31-33), so excluding one function would not restore the guarantee in Rust; this is not proved here.

### R14. A closure-scoped drain is panic-safe under unwinding `[proved]`

```lean
-- lean/PanicSafety/Forget.lean:691
theorem closureScopedDrain_panicSafe_unwind : PanicSafe .unwind drainWith := by …
```

Bounded check `[bounded search]`:

```lean
-- lean/PanicSafety/Forget.lean:698-700
theorem closureScopedDrain_panicSafe_unwind_upTo3 :
    ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, ∀ bs ∈ allBehs n, ∀ ds ∈ allBools n,
      ResOk (run .unwind (tableOf bs) (dtOf ds) drainWith m) := by …
```

- **Kind:** theorem. **Tier:** T1. **Depth:** substantive (loop invariant: the buffer is never modified, and every value added to the drop log comes from an index below the cursor).
- **Plain claim:** For every callback table (callbacks may drop or forget each element they receive, or panic while owning it), every destructor table, and every entry state satisfying `Inv`: the closure-scoped drain `drainWith`, which keeps its guard in the library frame, run under `unwind`, reaches no UB, and a return or an unwind leaves `Inv` (`PanicSafe .unwind drainWith`).
- **Hypothesis ledger:**
  - `Inv m (inside PanicSafe)` — The entry container is well-formed. Tight (witness class: a two-cell state holding one value twice (unwinds to a non-`Inv` state), and a one-cell container with an uninitialized cell (UB)): counterexample `drainWith_needs_inv` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
- **Non-vacuity:** `closureScopedDrain_example` (entry `ceMem3` satisfies `Inv`; forget one element, panic while holding the next; the unprocessed element stays in the container).
- **Prior art:**
  - Rust std 1.85.0, std::thread::scope (https://doc.rust-lang.org/1.85.0/std/thread/fn.scope.html): 'All threads spawned within the scope that haven’t been manually joined will be automatically joined before this function returns.' derived (modeling bridge).
  - RFC 3151, rust-lang/rfcs f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/3151-scoped-threads.md L32-33: 'the old scoped threads could be fixed by relying on closures rather than guards to ensure spawned threads get automatically joined'.
  - The Rust Reference, rust-lang/reference c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/behavior-considered-undefined.md L67: 'The runtime assumes that a Rust stack frame is not deallocated without executing destructors for local variables owned by the stack frame. This assumption can be violated by C functions like `longjmp`.'
  - Without Boats, 'The Scoped Task trilemma', blog post dated April 8, 2023, https://without.boats/blog/the-scoped-task-trilemma/ (unpinned page): 'every object in Rust can be leaked without running its destructor'.
- **Design question:** Which API shape survives safe leaking: cleanup run by the library's own frame.
- **Non-claims:** see **Boundaries**, R14.

Basis: execution (Lean kernel check) — `closureScopedDrain_panicSafe_unwind`, `closureScopedDrain_panicSafe_unwind_upTo3`.

Basis: derived (modeling bridge) — RFC 3151 (text/3151-scoped-threads.md L32-33) and std 1.85.0 `std::thread::scope` replace a guard-returning API with a closure-scoped one whose cleanup runs in the library's own frame; `drainWith` has this shape. The toy result is panic safety for one closure-scoped drain.

### R15. Memory panic safety does not imply preservation of a logical invariant on unwind `[proved]`

```lean
-- lean/PanicSafety/Logical.lean:27-31
theorem panicSafe_unwind_but_countersAgree_broken :
    PanicSafe .unwind bumpBoth ∧
    ∃ (cb : Callback) (dt : DtorTable) (m m' : Mem),
      Inv m ∧ CountersAgree m ∧ run .unwind cb dt bumpBoth m = .unwound m' ∧
      ¬ CountersAgree m' := by …
```

- **Kind:** theorem. **Tier:** T0. **Depth:** shallow (`Inv` ignores the counters by definition; reference point).
- **Plain claim:** For every callback table, destructor table and entry state satisfying `Inv`, `bumpBoth` (increment `ctrA`, call user code, increment `ctrB`) run under `unwind` reaches no UB, and a return or an unwind leaves `Inv` (`PanicSafe .unwind bumpBoth`); and there are a callback table, a destructor table and a state satisfying `Inv` and `CountersAgree` for which the run `run .unwind cb dt bumpBoth m` unwinds to a state violating `CountersAgree`.
- **Hypothesis ledger:**
  - `Inv m (inside PanicSafe .unwind bumpBoth)` — The entry container is well-formed. Tight (witness class: a two-cell state holding one value twice): counterexample `bumpBoth_needs_inv` satisfies all the other hypotheses and refutes the statement with this hypothesis dropped.
- **Non-vacuity:** `bumpBoth_unwind_example`.
- **Prior art:**
  - Rust std 1.85.0, std::panic::UnwindSafe (https://doc.rust-lang.org/1.85.0/std/panic/trait.UnwindSafe.html): 'in the absence of unsafe code, a panic cannot lead to memory unsafety'; 'this is not an unsafe trait, so there is not a succinct contract that this trait is providing'; 'the lack of unsafe means it is mostly an advisory. The AssertUnwindSafe wrapper struct can be used to force this trait to be implemented for any closed over variables passed to catch_unwind.' derived (modeling bridge).
  - RFC 1236, rust-lang/rfcs f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, text/1236-stabilize-catch-panic.md L135-138: 'panic safety in Rust is not solely limited to memory safety. *Logical invariants* are often just as critical to keep correct during execution and no `unsafe` code in Rust is needed to break a logical invariant.'
  - The Rust Reference, rust-lang/reference c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/behavior-not-considered-unsafe.md L26 (section 'Logic errors'): 'If a program breaks such a constraint, the behavior may be unspecified but will not result in undefined behavior.'
- **Design question:** Which invariants must be restored on unwind: memory-safety ones; logical ones need not be (reference point).
- **Non-claims:** see **Boundaries**, R15.

Basis: execution (Lean kernel check) — `panicSafe_unwind_but_countersAgree_broken`.

Basis: derived (modeling bridge) — RFC 1236 (text/1236-stabilize-catch-panic.md L135-138) and the std 1.85.0 `UnwindSafe` documentation distinguish logical invariants from memory safety, and the Rust Reference (src/behavior-not-considered-unsafe.md L26) says that breaking a logical constraint does not result in undefined behavior. `CountersAgree` is a toy logical invariant.

## Boundaries

Non-claims come first: the common ones, then those of each result. They record what the results do **not** show.

### Non-claims common to every result

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program. No Rust code was compiled, run or verified.
- Every result about `Prog` (R0–R9, R14, R15) is stated for guards whose drop glue is a pure fix-up of `(buf, len)` (`Guard.fix`): such a guard cannot run element destructors, panic, read or change the drop log, or reach UB. Guards that drop elements (for instance a drain's drop guard) are not programs of `Prog`, and these results say nothing about them.
- The client language of R11–R13 has no panics and its destructors do not panic; its `.rejected` outcome (an ill-typed program, a compile error in the toy) is neither UB nor a successful run.
- A `[bounded search]` theorem establishes its property on the listed finite family and neither establishes nor refutes the unbounded statement; each bounded check accompanies an unbounded theorem of the same card, and no card depends on a bounded check.
- "Panic-safe" (`PanicSafe mode p`) means: for every callback table, every destructor table and every entry state satisfying `Inv`, the run of `p` in that mode reaches no UB, and `Inv` holds on a returned or unwound state. An abort counts as an acceptable outcome (`ResOk .abort`). Panic safety is not freedom from leaks (R6) and not preservation of a logical invariant (R15).

### Non-claims per result

#### R0 (Adequacy of the drop-safety predicates)

- Says nothing about panicking destructors; with the table `dtPanicsOn0` both characterizations fail (`dropSafety_adequacy_fails_with_panickingDtors`).
- Says nothing about the counters `ctrA` and `ctrB`, which `Inv` ignores.
- `DropSafe` treats the frame's guards as pure `(buf, len)` fix-ups; that guard fix-ups and local drops can be applied in either order is a consequence of this restriction of the model. Guard fix-ups (`Guard.fix`) are pure functions of `(buf, len)`: a guard cannot run element destructors, panic, read or change the drop log, or reach UB. Guards that drop elements (for instance a drain's drop guard) are not programs of `Prog`; this result says nothing about them.
- Does not say that `Inv` is the right invariant for any real container. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

#### R1 (Unwinding exposes the raw-move intermediate state)

- Does not say every callback panic breaks `rawRetain`: by R3, an unwound state satisfies `Inv` when nothing was removed up to and including the panic (example: `rawRetain_unwind_noRemoval_example`).
- Does not claim that any version of the Rust standard library's `retain` or `String::retain` has this behaviour.
- The UB in the toy is a double drop of a value. The toy does not model `String`; this result is not a statement about CVE-2020-36317 (https://nvd.nist.gov/vuln/detail/CVE-2020-36317), which is cited for context. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

#### R2 (Raw moves are exactly correct under `abort`)

- Buffer cells at index `len` and beyond after return are unspecified.
- Says nothing about `unwind` (R1, R3).
- The toy's `abort` mode is a property of one run. In Rust the panic strategy is chosen for a whole build: RFC 1513 (text/1513-less-unwinding.md L143-144) requires the `-C panic` mode of the panic runtime to match the final product (outputs that are not rlibs), so library code cannot choose abort-on-panic for itself. derived (modeling bridge); not proved here.
- 'Panic-safe under abort' holds because an abort is counted as an acceptable outcome (`ResOk .abort`), not because the state at the panic is consistent. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

#### R3 (Which panics expose the raw-move state)

- The informal phrasing 'a callback that panics at step i causes a double drop' is false for panics before any removal (`rawRetain_unwind_noRemoval_example`).
- By R3, a destructor panic on the first removed element already yields an unwound state violating `Inv`, because that element counts as removed (`specRetain_example_dtorPanic` shows the abstract result of such a run).
- With panicking destructors, the owner's later drop of a state violating `Inv` may abort instead of reaching UB (`dropSafety_adequacy_fails_with_panickingDtors`); R0 covers non-panicking destructors. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

#### R4 (Call-site characterization)

- Guard fix-ups (`Guard.fix`) are pure functions of `(buf, len)`: a guard cannot run element destructors, panic, read or change the drop log, or reach UB. Guards that drop elements (for instance a drain's drop guard) are not programs of `Prog`; this result says nothing about them.
- Says nothing about callers that hold guards or locals with drop glue over the same container; whether the characterization would then need the caller's frame as well is not proved here.
- The model has no catch boundary: after an unwind the state is handed to the owner, whose drop glue runs (`harness`); reuse of the container after a caught panic is not modelled.
- Says nothing about concurrency, re-entrant callbacks, user code with effects other than return or panic, non-terminating operations (every `Prog` run terminates), or unwinding across a foreign-function boundary (which the Rust Reference lists as undefined behaviour; not modelled).
- `DropSafe` is a memory-safety condition in the toy; it says nothing about logical invariants (R15).
- The bounded check covers nine sample programs on a finite family of tables and states; the unbounded statement is the theorem. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

#### R5 (Destructor sites count as call sites)

- `truncateLate_dtorPanic_unwound` describes one entry state (`ceMem1`) and one destructor table (`dtPanicsOn0`); it states nothing about other entry states or destructor tables.
- Does not say that dropping before updating `len` is unsafe when destructors cannot panic (`truncateLate_panicSafeAssumingNoDtorPanic`). Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

#### R6 (Leak amplification is sound but leaks)

- 'Panic-safe' does not mean 'no loss': after a panic the container is empty and values are leaked (`leakRetain_unwind_example` shows `¬ LeakFree`).
- Buffer contents after an unwind are unspecified.
- Leak amplification does not give the 'no resources are leaked' clause of Abrahams' basic guarantee (see R8 for the guard). Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

#### R7 (A drop guard updated before each destructor is exact on unwind)

- No hypothesis on element destructors is needed for this guard ordering; this does not extend to guards updated after the destructor (R9).
- Does not cover the owner's later drop of the container while the panic propagates. In the toy, a destructor that panics there makes `containerDrop` return `.abort` by definition (`guardRetain_ownerDrop_doublePanic_aborts_example`: the guard has repaired the container, then the owner's drop aborts); that is a modelling choice, not a theorem about Rust.
- `GuardUnwindExact` does not state that the buffer length and the counters are unchanged (unlike `LeakUnwindExact`); buffer cells at index `len` and beyond are unspecified.
- The back-shift guard runs no destructor (its fix-up is a memory move and a `len` update); the toy guard omits the `set_len(0)` that std's `retain_mut` also performs. Omitting it relies on the guard staying in the library frame, where no instruction of user code can forget it (in `Prog`, user code is a callback table); a guard that safe code could forget is the situation of R11, and what `guardRetain` would then need is not proved here. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

#### R8 (The guard is leak-free on unwind)

- Leak-freedom is about the unwound state, before the owner drops the container.
- The statement without `Inv m` is proved (`guardRetain_unwound_leakFree_noInv`, and on a finite family by `guardRetain_unwound_leakFree_noInv_bounded`), but off `Inv` its conclusion is weak: it does not say that no element is lost, because a value already in the entry drop log, or one of two copies of a duplicated value, satisfies `LeakFree` trivially.
- Says nothing about `leakRetain`, which is not leak-free (`leakRetain_unwind_example`). Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

#### R9 (A guard updated after each destructor is panic-safe when no destructor panics)

- Does not say every guard needs non-panicking destructors: the ordering of R7 does not.
- The tightness witness is one destructor table (`dtPanicsOn0`); which other panicking tables break `guardRetainLate` is not characterized here.
- Does not identify the code path of any standard-library defect. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

#### R11 (The toy destructor-reliant drain reaches UB once `forgetGuard` is available)

- A statement about one API and one client in one toy client language; it does not prove that every destructor-reliant API is unsound.
- Of the positive controls, R12 and R13 are about the client language; R14 (`closureScopedDrain_panicSafe_unwind`) is about `drainWith`, a program of `Prog`, in which user code is a callback table and has no instruction that reaches the library's guard. R14 therefore does not run the client `forgetClient` or any other client program.
- The toy shows a sequential double drop and has no threads; it is not a statement about rust-lang/rust issue 24292 (https://github.com/rust-lang/rust/issues/24292), which is cited for context.
- `Rc` cycles are not modelled; safe `forget` stands in for every safe way to leak.
- The client language has no panics and non-panicking destructors.
- Escape hatches not modelled: types that cannot be leaked (linear rather than affine types), and the `Pin` drop guarantee, which requires `drop` to run before the memory of a pinned value is invalidated or reused (std 1.85.0 `std::pin` documentation) while still allowing pinned values to be leaked. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

#### R12 (The leak-amplified drain reaches no UB under safe `forget`)

- Says nothing about leaks. Forgetting the guard can leak the elements not yet taken out: `leakAmplifiedDrain_forgetGuard_leaks` exhibits one such run (on `ceMem1`, which satisfies `Inv`, the program `[.drain, .forgetGuard]` completes with value `0` neither dropped nor within `len`); a general statement about which elements leak is not proved here.
- The client language has no panics and its destructors do not panic; nothing is said about a drain guard whose destructor panics part-way.
- `.rejected` outcomes are not UB but are not successful runs either. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

#### R13 (Without `forgetGuard`, the destructor-reliant drain reaches no UB)

- Excluding `forgetGuard` is a property of the toy language. In Rust a value can be leaked without `mem::forget`: the std 1.85.0 `mem::forget` documentation (rust-lang/rust 4d91de4e48198da2e33413efdcd9cd2cc0c46688, library/core/src/mem/mod.rs L43-44, where `Rc` and `process::exit` are written as intra-doc links) says that 'a program can create a reference cycle using `Rc`, or call `process::exit` to exit without running destructors'. That excluding one function would therefore not restore the guarantee in Rust is derived (modeling bridge) and not proved here.
- The client language has no panics and its destructors do not panic. The destructor-reliant guard drops the remaining elements before it sets `len := 0`; with a destructor that could panic part-way, the already-dropped cells would still be within `len` (not proved here; compare R5 and R9).
- `.rejected` outcomes are not UB but are not successful runs either. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

#### R14 (A closure-scoped drain is panic-safe under unwinding)

- `drainWith` is a program of `Prog`, not of the client language of R11-R13; user code in `Prog` has no instruction that reaches the library's guard, so 'the guard cannot be forgotten' holds by construction. The callbacks can forget elements (`forgetVal`).
- The theorem is panic safety (`ResOk`); it gives no functional specification of `drainWith`.
- On unwind the toy guard moves the unprocessed elements back to the front of the container; it does not model guards that drop them. Guard fix-ups (`Guard.fix`) are pure functions of `(buf, len)`: a guard cannot run element destructors, panic, read or change the drop log, or reach UB. Guards that drop elements (for instance a drain's drop guard) are not programs of `Prog`; this result says nothing about them.
- Not modelled: asynchronous closure-scoped APIs, where a suspended future can be leaked; and deallocating a stack frame without running its destructors (for instance with C `longjmp`), which the Rust Reference says the runtime assumes does not happen.
- Not a proof about `std::thread::scope`. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

#### R15 (Memory panic safety does not imply preservation of a logical invariant on unwind)

- Shows one direction: memory panic safety does not imply that a logical invariant is preserved on unwind. The converse question is not addressed here.
- `catch_unwind`, `UnwindSafe` and `AssertUnwindSafe` are not modelled. The std documentation describes `UnwindSafe` as 'mostly an advisory'; no statement here depends on it.
- Does not say logical invariants never matter for soundness: if unsafe code relied on `CountersAgree` it would be a memory-safety invariant and R4 would apply to it. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, its standard library, or any Rust program.

### Escape hatches

- From R11 (the destructor-reliant drain reaches UB once `forgetGuard` is available), inside the toy: forbid the guard-forgetting instruction (R13), make the API leak-amplified (R12), or keep the guard in the library frame (R14, a program of `Prog`). Outside the toy, not modelled: types that cannot be leaked (linear rather than affine types) and the `Pin` drop guarantee.
- From R1 and R3 (raw moves expose a state violating `Inv` on unwind): run under `abort` (R2), set `len := 0` first (leak amplification, R6), or keep a drop guard updated before each destructor (R7, R8).
- From R5 and the tightness witness of R9 (destructor panics): update `len` or the guard's fields before running the destructor (R7); or assume that no destructor panics (`NoPanickingDtors`, R9; `truncateLate_panicSafeAssumingNoDtorPanic`).

### Hypotheses whose tightness is unknown

None. The hypothesis `hm : Inv m` of `guardRetain_unwound_leakFree` (R8) is harmless, because `guardRetain_unwound_leakFree_noInv` proves the same conclusion without it; it is retained because off `Inv` the conclusion `LeakFree m m'` does not express that no element is lost.

### Unknown

- Whether the call-site characterization (R4) extends to callers whose frames hold guards or locals with drop glue over the same container.
- Which panicking destructor tables other than `dtPanicsOn0` make `guardRetainLate` fail (R9).

### Not examined

Guards that drop elements, or that can panic or reach UB, inside `Prog`; panicking destructors and unwinding in the client language; concurrency; catch boundaries and reuse of a container after a caught panic; `catch_unwind`, `UnwindSafe` and `AssertUnwindSafe`; asynchronous code; foreign-function boundaries; `Rc` cycles; non-terminating user code.

### Known not to apply (by construction of the toy)

That a destructor panic during the owner's drop aborts (`guardRetain_ownerDrop_doublePanic_aborts_example`) is the definition of `dropCells`/`containerDrop`, not a derived fact. The std 1.85.0 `Drop` documentation says that such a double panic "will likely abort the program", and the Rust Reference at the commit cited under **Evidence** states no such rule.

### Attractive stronger conclusions not established

- "Every destructor-reliant API is unsound once `forget` is safe." R11 is one counterexample for one toy API and one client.
- "A late-updated guard is unsafe for every panicking destructor table." R9's tightness witness is one table.
- "Leak amplification satisfies Abrahams' basic guarantee." It leaks (R6).
- "`drainWith` behaves like `Vec::drain`." R14 is panic safety; the toy guard restores unprocessed elements instead of dropping them.
- "A panic-safe operation preserves every invariant on unwind." R15 shows that a logical invariant can be broken.
- Any statement about a specific Rust standard-library version or function.

### Disproved, dropped or retired statements

No statement was disproved, and every result in this package is fully proved. Two identifiers are retired. R10 (a destructor panic during the owner's drop aborts) is not a result: it holds by the definition of `dropCells`, and it is recorded as a definition example (`guardRetain_ownerDrop_doublePanic_aborts_example`) and as a non-claim of R7. R16 (a toy `UnwindSafe` marker) is not part of the package: a marker verdict that is not computed from the closure body, consulted by a `catch_unwind` that ignores it, would make any conclusion about it hold by definition. The advisory status of `UnwindSafe` is recorded as documentation in R15.

## Evidence

### Kernel-check record

All evidence was acquired on 2026-11-21 with Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), from a fresh build of `lean/` with Lake's artifact cache disabled, so that every proof was re-elaborated and re-checked by the kernel. Basis: execution (Lean kernel check).

- Banned tokens: no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC` in the Lean sources.
- Axioms: `Lean.collectAxioms` was computed for every declaration of the library's modules (the full per-declaration record is `audit/axioms.json`); each depends on at most `propext`, `Classical.choice` and `Quot.sound`.
- Statement and closure hashes (`audit/statements.json`): for each Lean name referenced by `results.json`, the statement SHA-256 is the SHA-256 of `toString (repr type)` of the constant's type, and the closure SHA-256 is the SHA-256 of the newline-joined, sorted list of entries `name : repr type [:= repr value]` for every package constant reachable from the statement's type (through types, the values of definitions, and the constructors of inductive types; theorem bodies are excluded). A change to any definition in a statement's closure changes its closure hash.

The tables list every Lean name referenced by `results.json`, grouped by the first card that references it, with the axioms it depends on and its hashes from `audit/statements.json`. Names are in namespace `Toy.PanicSafety`.

#### R0 (Adequacy of the drop-safety predicates)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `inv_iff_containerDrop_noPanic_ne_ub` | Quot.sound, propext | `a8db9ee947d9c2f48f36d40cb08922379ed23916d0fcf98f30b4bd0a35ae59ad` | `ccf8e2766c7f6e64f6ae0bcccf36c1d107e751fc16279bd88f1dd2e39a763281` |
| `unwindEntries_noPanic_ok_inv_iff_dropSafe` | Quot.sound, propext | `2f7aeaf86ce3d5da3918ffc558c7b168e7ad1ac3069029f406f72590bd67f8d7` | `d3b6ac428ae4d87bd2675d0967ca7177ed9240478770a59b17c6fab88fc93bfb` |
| `dropCells_noPanic_ne_ub_iff` | Quot.sound, propext | `ecad446a79b47fb6f1d0d72f81e42b5e5700cec33a9530907ac2d02dc4a5a177` | `d555be10fc23a35bd8b3164473a6f1824b0d854b04fb1605ec764ba7deb62049` |
| `dropSafe_nil_iff_inv` | propext | `a1eb346a2b87dd486d8bd58ebfd2dd6124a9105ea1ac9500faad7763333ef68b` | `acd585ecfd87f3aca40b71f9c11eb70f9fb5206dc8ccd6e6c7c120ddd99f2df0` |
| `exec_sites_mode_indep` | Quot.sound, propext | `fe3fa6a6b99d0d7abde772b82cb3200c7143d7605a5c3b5d487ee4e084ee2a1c` | `79ffffa818c36785b28101d7cd895988915fc5267e787a7728e7a79f221077a7` |
| `inv_pop` | Quot.sound, propext | `fdd19979b67401d85389dcfd440816ab9882829b57c7ae8862cf4bb8e0a0f1f3` | `90145b0ce25259bd553ef3d9bc106dbbacffb148d888cd5f779c697ab237bec8` |
| `ownsUniquely_cons_some_iff` | propext | `8b4d7eec2a2f0b8c0714ba81c56a684e791273ad5c897a30a0461d4aad619f63` | `eaa74813a102524efa01a7f48386a32a76d53873be44d5acb435cd7927069754` |
| `ownsUniquely_append_singleton_iff` | Quot.sound, propext | `13f67a0d4102e0ff4b267a98ad4abe2abeff87497f291c23301c29fe7c8828b3` | `eaa74813a102524efa01a7f48386a32a76d53873be44d5acb435cd7927069754` |
| `toks_cons_some` | none | `a538a3a9cfafa62c5a8160a0546b647e1069515b1e87349f45e354610ab6ec60` | `2aa73d30658389271e5518665e5560714f53ebc7382c7875a0913b2f67cdf1c3` |
| `toks_append` | propext | `ba2f6e9f8cffb82eff0cbb47fec6935ab9c8ccc269d6dbb02c998b99d38f09c2` | `2aa73d30658389271e5518665e5560714f53ebc7382c7875a0913b2f67cdf1c3` |
| `dropSafety_adequacy_fails_with_panickingDtors` | Quot.sound, propext | `442b9a26e07b5f831fa2ebcd1ee38947b189af763e059d803c57e82207b3ef7d` | `d7bc73195bed75d03e8c803d1717818fef5000b764a1623606714e551492339f` |
| `Inv` | none | `977b62e744fb93d2e08a276ba6f36f1cd996e9b9e1e1b3985f2518d719cc879b` | `c1b50fc287f2903b82340a64425a7e94036b53b7a82f8e6f7c30deb168905302` |
| `containerDrop_pos` | Quot.sound, propext | `0c8ab1212dd282c5a1f611a9f8e9dad5e5d23b94f111b9accf14f6fe743ba1dc` | `b4d5b44e6256fb82154d04d7fb90266e4731244dac47321463d5680a115c72db` |
| `ceMem2` | none | `1672b993b8f2d09873edb9f6e6d6aa3432cdecfb106ece319f5cb0e7d1312d95` | `c1b50fc287f2903b82340a64425a7e94036b53b7a82f8e6f7c30deb168905302` |
| `dropSafe_pos_guardRepairs` | Quot.sound, propext | `c677f2d7eee5dd8b6bee21febb5c6c3c7c3678499f2d8edb2eccf8f86636baef` | `c78fb80bc2a51587c0491c8d63fbd813d4b700cf629a42d807b40c6aa0119a06` |
| `containerDrop_neg_doubleDrop` | Quot.sound, propext | `f1b60b4833e849f3ff2e796cf444ca00fdaa756570f6ffd27e6ea5aab257e219` | `0d4493f15ca329f2d3e8452a832bceef30a71ca95ab6843fd222dec37d8ebafb` |
| `dropSafe_neg_localDuplicates` | Quot.sound, propext | `ce020b9537693031e2d270f4dce0bb2659f2f5c693a42d3f5aa328c1397360bc` | `ddacf04a2e38b2511e6cfd9c1b7a394e82eb9e8eb2fc56bc802b103f9b9c91ad` |
| `dtPanicsOn0` | propext | `89c90ef3e2ff7ff1e7faad440ae263417e545b0af600d3c44b07625aad30ba54` | `fc7540626dbb54d2dcc1ac7529879f86798c8767a093d94e558bd55b7e6d94c9` |
| `DropSafe` | none | `3ae715b40981602383177f55788c3c017ea24f700e2175827253419c0c710c51` | `574fcc773450b9317d79df8253f45e34e173be54705b939bc242f6bc68acb5d8` |
| `Prog` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `noPanicDtors` | none | `89c90ef3e2ff7ff1e7faad440ae263417e545b0af600d3c44b07625aad30ba54` | `fc7540626dbb54d2dcc1ac7529879f86798c8767a093d94e558bd55b7e6d94c9` |
| `inv_pos` | Quot.sound, propext | `5892d915ae4516baad9cbe6018104ddb8ad189da4dc1adb0650bb39bc94d302e` | `ac91d531feb15b1a107efaf4acd8fa94ac2111e383449042c24b033855eebafa` |
| `inv_pos_staleTail` | Quot.sound, propext | `1c6eda227cb3ac17af8c5bec6bce52163d1dfd2fe291aa7464e6aebcbe49b322` | `ac91d531feb15b1a107efaf4acd8fa94ac2111e383449042c24b033855eebafa` |
| `inv_pos_countersDisagree` | Quot.sound, propext | `a392aa061aeca1ff50827767a03744c3aba427c457f8e34822887a7c1c98629c` | `ac91d531feb15b1a107efaf4acd8fa94ac2111e383449042c24b033855eebafa` |
| `inv_neg_lenPastBuffer` | Quot.sound, propext | `644d629a6fb032bb09b4dad888feb42518db05e8e43910dbb47f409aa2982ac9` | `ac91d531feb15b1a107efaf4acd8fa94ac2111e383449042c24b033855eebafa` |
| `inv_neg_duplicate` | Quot.sound, propext | `6088ed229db25e2d876703ef5124b1d53dba86024098d7f900a3df99e6fda1b2` | `ac91d531feb15b1a107efaf4acd8fa94ac2111e383449042c24b033855eebafa` |
| `inv_neg_dropped` | Quot.sound, propext | `dce1cbe08e5e47f82db04c7f0b74d16a4e144f38d742b6be1a1c54173107fa7a` | `ac91d531feb15b1a107efaf4acd8fa94ac2111e383449042c24b033855eebafa` |
| `inv_neg_uninit` | Quot.sound, propext | `1dce9115283ab592494facbdae5c382b27a2c1bca335fb57a0a1d6c041874af5` | `ac91d531feb15b1a107efaf4acd8fa94ac2111e383449042c24b033855eebafa` |
| `ownsUniquely_pos` | Quot.sound, propext | `ae259fc0851aefb4480fc8912a174928e196bfaa4e436bb91c787703d2e4a48c` | `eaa74813a102524efa01a7f48386a32a76d53873be44d5acb435cd7927069754` |
| `ownsUniquely_neg_duplicate` | Quot.sound, propext | `5b26ca8ef1da76249129886e89ba6944d381036d7eb959feea1dd55da31bce9c` | `eaa74813a102524efa01a7f48386a32a76d53873be44d5acb435cd7927069754` |
| `ownsUniquely_neg_dropped` | Quot.sound, propext | `b6e6218a5a01ed28d99742db256520b9ad3bbd2f75022806d079ceff32e1e560` | `eaa74813a102524efa01a7f48386a32a76d53873be44d5acb435cd7927069754` |
| `ownsUniquely_neg_uninit` | Quot.sound, propext | `cfcd1b333275b567a6f9f80826014db76b1e004ecdcbbc27a97d73be8f38c384` | `eaa74813a102524efa01a7f48386a32a76d53873be44d5acb435cd7927069754` |
| `noPanickingDtors_pos` | none | `0a559ae1f8b81fd55fd678e2ecc020f0e43ca7579a6d57c872107c233e0d6cdb` | `ef0313927dcd2aad9cf6e34050705734514a2cf3b0b3f40587c4ca5455af71d5` |
| `noPanickingDtors_neg` | propext | `20655511c4760bb02afa47925a6f53a48f2d7e20dca75785560dd40a01352c6f` | `d5ecd680207c6037dc0a21ecaf1e8c59389b63870bf3d13c2e731c1a61b5e5cf` |
| `Guard` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `unwindEntries_example` | Quot.sound, propext | `704ae92ab21c8aed9a45fb99a7f6b2d0a0635090552f2de94e66dc3d84614a21` | `4dd81e7faaf23499da54b6b7125cb26d9526440271bf3920766e15574a81b463` |
| `unwindEntries_example_abort` | Quot.sound, propext | `ad6a38006c3609dcfe1c4a2ec4fc47e01a61ae5190a866341a548460cea46657` | `b3c8ca2ff138a2eeb5c2ab9d7dbea931e201915a500d464978e0c99f9c7d98c2` |
| `backshift_example` | propext | `4e90f147d4f6cb214e26c53eb69c71f55b737da8f48613e6997a6967edf6ddd3` | `5156efd7f3ae261b47b7ff15caecea1f1782f0e3df0a248057a79ef3ed6ffacf` |
| `panicSafe_pos` | Quot.sound, propext | `cdfe5ea70c625f9b9e948cf9a033c7c4a1b9f5ecf2759e30eeb5b667e09d6f36` | `286b6f4944c01117892173eb8ea246fec13509d4edfb3bb558c7b6f3560f0e55` |
| `truncateThenCall` | none | `e5d2849fc004c5be1ac629651ee30d4e1b2740458bf0bbf96642861f199ac39a` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `panicSafe_neg` | Quot.sound, propext | `4a8d6f2d0a8e3e2feeaee52e2a4af0cc07499c74247d89589387900869891cc4` | `ed60552e122b2f828df8237c228769a9eded33326954cc65d1c3f2cf4a54a7b2` |
| `panicSafeAssumingNoDtorPanic_pos` | Quot.sound, propext | `546fc189e76d4af44afa660d08a0c30f32ab9c39afabd32db70e643dc3395e9f` | `a48cfe8e43907412e8012dac27c7842fd9ce2b798c260ebe09c47a0f966a4ed1` |
| `panicSafeAssumingNoDtorPanic_neg` | Quot.sound, propext | `b2f09163db672d0eb830f63683bd17273ba10116857b85af8ac0d3766bfae032` | `1bc50eeeccf448fed9a65ecd0a57653285df0fb139e7d8775361fc61fab8a83e` |
| `containerDrop_neg_lenPastBuffer` | Quot.sound, propext | `983b9d98e7cee6e7417eeb443110f93c751f765bc38d91d5d8a32c8d62760e28` | `0d4493f15ca329f2d3e8452a832bceef30a71ca95ab6843fd222dec37d8ebafb` |
| `dropCells` | Quot.sound, propext | `025b7f8534e22a297d9057143f9b1330cd9a0c55660cbc13ed32e6e3de1a150d` | `1b121074d0718cbe6ca61368e6f85d970665f6a2c23c1ddcf83c878a20b6b72a` |
| `specRetain_example` | propext | `6ce2738d40e2b33b8a44bac1415dad051a26d8c8d8919418251af5b6ea949428` | `4f969efdceed15cbce054eab21c436748a1c6a0c5e6b9d976fe9fdcac4db6a6e` |
| `retainReturns_pos` | Quot.sound, propext | `c1f9ef10f92f7544f09d354585cc7d10b08949310907ccdc4fd1f00f643acbdd` | `a31ff6a0bcc7c99b454770fa817b8d6553d3a15ced07f8daf0661f617a0af3bb` |
| `retainReturns_neg_wrongDropLog` | Quot.sound, propext | `eae6d818e6a08983d14c6c0a2970034053a5cd772d5506129300ed3eb49dee73` | `a31ff6a0bcc7c99b454770fa817b8d6553d3a15ced07f8daf0661f617a0af3bb` |
| `leakFree_pos` | Quot.sound, propext | `2fac32271905b87a4cdce14327eb45e706adace5d7b2f50d16a18491876003b1` | `ea32211ae388298b40522cf1ff11e99623ac32c1bd1d4c00cf6195b64419e14c` |
| `leakFree_neg` | Quot.sound, propext | `472cd61a079a13d1d963b84fdf3968fe53a1646ee1ab0f8c9c5a5aa0001426f1` | `ea32211ae388298b40522cf1ff11e99623ac32c1bd1d4c00cf6195b64419e14c` |
| `guardUnwindExact_pos` | Quot.sound, propext | `033fd1b4bf92b3a52f174f3316a03f0a846739f3134bc321f8dbfbcf7c4ad2ae` | `868730ad00bb2c9e4377b21dae8647abed8be87e156336e8b7a4796c78834f17` |
| `ceCbRemoveFirst` | propext | `9c8c0831adccd039f8e6f7ce00e4885221ecce1854985fce9e3a05cff7068591` | `5dc1fc998ec81cb6409b202e2a7323947c78319b156b7c71a89a541de1227379` |
| `callSitesDropSafe_pos` | Quot.sound, propext | `beb0bc4b13c8073b31305246c60fac4590b840eeb5ce1a8c68a41553b57dbeb1` | `d28e28ab3e7ad1d269e4b34ceda4fd3b00f4960e027d37a7f9d6e0d28f604cb1` |
| `callSitesDropSafe_neg` | Quot.sound, propext | `8c8b98148896b038ea8e2140c365f8b7dacb07fe04219f73f696abe7ba2ba535` | `781f1f361ab81ae3b88f6cd176afdd17ba1a6c834324fbc6493037f49488c420` |
| `callbackSitesDropSafe_pos` | Quot.sound, propext | `ed6c72653eb914047982cc0f51629725768dc19b0629283f3dd9db5a13262c66` | `da9690a79e3d81c94e8e38d5a990b03932368b321aedd34fc4f6a789fc9026f0` |
| `callbackSitesDropSafe_neg` | Quot.sound, propext | `b45f530ee351427ea6a98b85cad154306ca8162652be3a48d484f24fb7fef2ce` | `ea648f764d43b17204477b5b4a1ca5d199044caa3e4ae40b900b38d0a6aee81e` |
| `clientRun_rejected_example` | Quot.sound, propext | `ebe4713e1ea429a7a3693b4dced1ed726646b973cfa3ab3c04b58fc3b184a96a` | `5bbd04c32f59a647de64fe77aa6bd0030e244b8cb8149bc837066fe6e23725f8` |
| `clientRun_drainTwice_rejected` | Quot.sound, propext | `94e7570443f89e7c4e7e9d92860a03d5d02009229203945da979f7fb65e299f4` | `5bbd04c32f59a647de64fe77aa6bd0030e244b8cb8149bc837066fe6e23725f8` |
| `countersAgree_pos` | none | `7c73be98fa5241a139e9aab2af327fcc89fc85ed666d4b28ebc14a17b7790e01` | `e69a4f1a1d8532491f60a756bb0f6564f5c683add0c60317cfeec84ee16bd526` |
| `countersAgree_neg` | none | `857c149341d38a2898c7f20a95735075b6f974f0a28b6c726d82cb63e7fbb11d` | `e69a4f1a1d8532491f60a756bb0f6564f5c683add0c60317cfeec84ee16bd526` |
| `panicFrom` | Quot.sound, propext | `9e7bf8c4d20d085dfb19bbb5812aa2de6a562736ebdaef381d534ea1fc9dedb9` | `b8fef91993bc1e6815f07d26f70c2a4d45fc3ce74b8689403bbc8435da185988` |
| `Tok` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Cell` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `toks` | none | `0f1fa4993b1e23c4fa27ce5c0688c72a268fddce145ebc9eb5001e86ae7ea5e4` | `173abd5377880f62f080f2e29f93bfd193ff1499dbd18e73f5ebf5bac4e22b36` |
| `Mem` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Mem.elems` | none | `39080f11753cd57d16f221b8964e9378bf2e2bea954f212d81f4feba68e34918` | `c1b50fc287f2903b82340a64425a7e94036b53b7a82f8e6f7c30deb168905302` |
| `OwnsUniquely` | none | `99c783e0176599c4b784176274a09f3dc7fdf2fc45a30bdd0734e8993ace7994` | `173abd5377880f62f080f2e29f93bfd193ff1499dbd18e73f5ebf5bac4e22b36` |
| `Beh` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Callback` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `DtorTable` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Entry` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Mode` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Res` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `URes` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `unwindEntries` | Quot.sound, propext | `10e7975e069d755152a246fcaa6a3024ce683e8f5b2267314f57b151712a88a9` | `9069ed735f04bcdfb2e2e4576876612139f3d7808cd81cb65fba08d5c566b44b` |
| `SiteKind` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Site` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `DRes` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Final` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Ending` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `AbsOut` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `DrainApi` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `CInstr` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `CState` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `dupMem` | none | `1672b993b8f2d09873edb9f6e6d6aa3432cdecfb106ece319f5cb0e7d1312d95` | `c1b50fc287f2903b82340a64425a7e94036b53b7a82f8e6f7c30deb168905302` |
| `ceCbRemoveKeepPanic` | propext | `9c8c0831adccd039f8e6f7ce00e4885221ecce1854985fce9e3a05cff7068591` | `5dc1fc998ec81cb6409b202e2a7323947c78319b156b7c71a89a541de1227379` |
| `ceCbRemove` | propext | `9c8c0831adccd039f8e6f7ce00e4885221ecce1854985fce9e3a05cff7068591` | `5dc1fc998ec81cb6409b202e2a7323947c78319b156b7c71a89a541de1227379` |
| `allBehs` | none | `77b75dcfb969617ed9276250e36932ba250c9011baf1725236069e06964148c9` | `3aaaae2a70e56cd7cf2e7918b3a2b004f59b5162f15e063ec14909b03c6e1c61` |
| `allBools` | none | `d885b867a28badaf14cf9a8f6ff964b3c57811ad37879a1090fdb4f0905be873` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `tableOf` | propext | `03c8418394535ab230223979c06f1069d7bc81ea1fdbf380bf5a64f278ebdd60` | `5dc1fc998ec81cb6409b202e2a7323947c78319b156b7c71a89a541de1227379` |
| `dtOf` | propext | `0911215d150969e0bbf0b7e721d718d04acfe6e1b28db787127e624a0a4bcc47` | `fc7540626dbb54d2dcc1ac7529879f86798c8767a093d94e558bd55b7e6d94c9` |
| `testMems` | none | `bf4426fc046afe3120222b57e7aeb3a31cced79b99cd4e630dcb76596a7d4e46` | `c1b50fc287f2903b82340a64425a7e94036b53b7a82f8e6f7c30deb168905302` |
| `allClients` | none | `89c546f9b3faffa2ddbb51815a88a88c9bf353a70164292cd9d40e56d711ff4e` | `f982ccfe02f8f0249fe2856edc443fa2a3328558afdad5005ae7ca7eb29ae886` |
| `clientTestMems` | none | `adbb93b4e4e9736f787212de326d49920f06a264f007162281c005297fb5d500` | `c1b50fc287f2903b82340a64425a7e94036b53b7a82f8e6f7c30deb168905302` |
| `charFamily` | propext | `238a81002d7224cadff88e843697e6d1a516e5331e5fee949f4ce38775641c64` | `14238b784397554c18fa0a43ba6266e567dce2e532e93cdd1c156b8fb2f1e537` |
| `BoundedPanicSafe` | Quot.sound, propext | `389a9d1708807fd8d1e12de35bda9ccd4cdd03b9c3658a6806eb09eacfed14c3` | `0db8e9a64478441b2fcad1c047fc6223ef8c11faf213997ddd6b2beecc6793ea` |
| `BoundedCallSitesDropSafe` | Quot.sound, propext | `28056e52160a69ed05d1dbfcd413cdcb7dc7394f28c658a313a42cd470eb9d5c` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `samplePrograms` | propext | `e57153df888ce07014e5c512e218ef1a037526932e042ff840b28da0f37921a8` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |

#### R1 (Unwinding exposes the raw-move intermediate state)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `rawRetain_unwind_doubleDrop` | Quot.sound, propext | `ff1de2edb434122a448861a476beebced3bb4ccb92b84a34a0bb99cd94ad3db7` | `c4fecfbc31e9a57856df3b41eaae6a143984f3cb1ae85e51e46d029660131750` |
| `rawRetain_unwind_duplicate` | Quot.sound, propext | `055bd6c0a20678349c010c322008d877317c22e53021169d6dba809123806215` | `63719f610f4852683ed6c22cd82eda47c7cb258a530727aec57d3b88df0f8ad7` |
| `rawRetain` | none | `e5d2849fc004c5be1ac629651ee30d4e1b2740458bf0bbf96642861f199ac39a` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `ceCbRemoveThenPanic` | propext | `9c8c0831adccd039f8e6f7ce00e4885221ecce1854985fce9e3a05cff7068591` | `5dc1fc998ec81cb6409b202e2a7323947c78319b156b7c71a89a541de1227379` |
| `harness` | Quot.sound, propext | `d90fd5d05a55033beee2b9b5a1f19e0a726d4b2ae5a2c5d4c2477c793ebbe86a` | `bea0c7c99119050bc8d188b2f5990c4c3bce46d02d9f2a746f90bb9f4a6914d6` |
| `rawRetain_unwind_noRemoval_example` | Quot.sound, propext | `4c87fe62deebcee6bcab59edb54ef97fc4c7d5be62b9d9c9e13e20c3febde60a` | `0f4fce80f3d7d561c9a8962e4f68533ffb85fbfb4ea5f785bce7ee8b811e3b0a` |

#### R2 (Raw moves are exactly correct under `abort`)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `rawRetain_abort_exact` | Classical.choice, Quot.sound, propext | `7cdd6a166506ff162b5d84adfc9426f1c8a19f37f7d68500b50bde382fd77cd0` | `9172744f549dca23a571402fd9290200d9796574b35f4396dfd2d6847bcaf78e` |
| `rawRetain_panicSafe_abort` | Classical.choice, Quot.sound, propext | `7f3bfd4a54b8940f137b96ac7e11bcdf1f3ef7d946cee9603355d04d2013654a` | `1d6188d2ee5d01e8ce85fc8da004a614d91534eaa8e30d5f6d742941637cc7e3` |
| `rawRetain_abort_exact_upTo3` | Quot.sound, propext | `c603ab9ace0bc43779462232df05d06f2e97c21b3bdc671ee5a42c6b8889a0fb` | `ae473862a8571d0dc1000751549ba3d02f4e9bd8ef697068962145a49c018037` |
| `RawAbortExact` | Quot.sound, propext | `90b7a446f844ef5d496733ce302a3c2ec8a3f2c4bb6c780ca9bdb5a699b60d93` | `14238b784397554c18fa0a43ba6266e567dce2e532e93cdd1c156b8fb2f1e537` |
| `RetainReturns` | none | `cb27b172e39da9d130ed77c0e20048c371f4dcce9e137c6c3c220aa0e6e43e64` | `3d4dec21b48ca25b30493d27d643ede5582a7ab40eee6c4822b885bc9a285900` |
| `specRetain` | none | `6705c3adf51c49ed31b885a5b4811e064d0c125409d0fb08e5b5507f6b5b9001` | `c3d4f9261b87d8226ca73f26b824e8df9a4a0ab9b9d81ca0e0dafa78a6d7fedb` |
| `absRetain` | none | `3f8e292cc95228707a5005f1d13e21dd27c4683a8c10d99eb5de618735dfebf3` | `c3d4f9261b87d8226ca73f26b824e8df9a4a0ab9b9d81ca0e0dafa78a6d7fedb` |
| `rawAbortExact_pos` | Quot.sound, propext | `87016cbc0660eddd4e2152c261b0eb1c66e5285a7e927364ee9ebc9c32ddacb1` | `276f4a6efbce176a4f0242defd97939558a273c7686d6a2a9a1cb23780eeffbc` |
| `rawAbortExact_return_pos` | Quot.sound, propext | `6ee698d364fddc8a5218694f656d5cbc2bcba940bb95f12fa67bf433e45a89fe` | `315c11cb8aa4ba5453c9bf4f354200f4289c7eaa82b097835298626efa35a093` |
| `rawLoop` | none | `9aa46649f9c6d07b4ec575a9b20c6bd3aac9924cc761c9c8f99870db74886bcf` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `rawRetain_abort_exact_needs_inv` | Quot.sound, propext | `8f7900b864227ff91b9bd046931962f3e9027e3506bbf72fcab4f2096872f9c2` | `213b9ae55a35f1eeff47419e434077851e9c4f7e91dcbae77b6cd15bb441d590` |
| `panicSafe_neg_rawRetain` | Quot.sound, propext | `3a468852f6aa1417c4713063d35fd37858e9de48851eee573a432ca4d4afe344` | `1d6188d2ee5d01e8ce85fc8da004a614d91534eaa8e30d5f6d742941637cc7e3` |

#### R3 (Which panics expose the raw-move state)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `rawRetain_unwound_inv_iff_rejected_nil` | Classical.choice, Quot.sound, propext | `a367de402064acb1a78753201d73ce35fc4f8258908b498df77236e54976813f` | `e19e2cee9e813c0d6031194df5a9f1f70d9e7b124375ed419f34d772ea2d2b7a` |
| `rawRetain_unwound_inv_iff_upTo3` | Quot.sound, propext | `7c03afcdf5fe4f95bdc3527822ce923e4e8afcca013b1b3e99da4665b80f1532` | `4f13a6b09eede4effde90c83c1a03d497bcc8cd621d6a4174e9233fce2ac149a` |
| `RawUnwoundIff` | Quot.sound, propext | `90b7a446f844ef5d496733ce302a3c2ec8a3f2c4bb6c780ca9bdb5a699b60d93` | `14238b784397554c18fa0a43ba6266e567dce2e532e93cdd1c156b8fb2f1e537` |
| `specRetain_example_dtorPanic` | propext | `10b0cefb03f0c0cbabfaa0fe1eebd30acffa041911507a2fe4bf501e8f23e76f` | `37b8cd2e84cbd3d38ea2e795c42ece0f8c3b9dbc7e187f810d4e8772edf39d93` |
| `rawRetain_unwound_iff_needs_inv` | Quot.sound, propext | `f72269aac91ca3a7df57d470d4e0757fcee992a12c440de2e14798ca621d465f` | `2d9389dcf574bcac5ac90e0083dc21082f0f41b72ef96c6d87f4f4a01e0f9f83` |

#### R4 (Call-site characterization)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `panicSafe_unwind_iff_abort_and_callSitesDropSafe` | Quot.sound, propext | `d922d97234a120a2d93ddf63ae6158fb4ce269c5ca299b9228b0862af41e8ede` | `5bb5f9ee1c866898a10dc88a683bb26973945e7c0a04c2ac0701611dbefa158b` |
| `CallSitesDropSafe` | Quot.sound, propext | `28056e52160a69ed05d1dbfcd413cdcb7dc7394f28c658a313a42cd470eb9d5c` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `callSitesDropSafe_iff_noPanicDtors` | Quot.sound, propext | `ea5300093f88ea4d0ee5bf8cf0ac8bb5480c0f28999f9762b094d5bd09a017f9` | `6df25617e345ce825a53755a02b5f711da1a89f29c2894c369ddc86caee99cb1` |
| `characterization_bounded_samples` | Quot.sound, propext | `6f2c0ac0c1eff668e4c839edac60c1db551d82bfcd788a401357c7c9fcf32e17` | `49faea5925c64cc31cf80055a88ba4ae8b4d8ea39fcb081a123a382f7469943c` |
| `characterization_bounded_samples_nontrivial` | Quot.sound, propext | `0f42efbe310817965c98168301ad7bb6ca113887134274ceb8ef5d3cde8b288c` | `f3d2aab11c7235e8fb58a1c5df7ce9abe254e36a32060a02401deb60247750ea` |
| `exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe` | Quot.sound, propext | `73590c6b55eb29757ab186f992a635cd052239ef0deb6289a54b35579e7184bc` | `26878e61d9817e4f8823406c21174231b0ebbfa623f9822f2659b5ce4be193ce` |
| `exec_abort_resOk_of_unwind_resOk` | Quot.sound, propext | `9587abf3d4087d485dbd99273fc859dab82cac90f6ab4f0db2c176b7a26d21e5` | `50e5557de52ad0ced0a657a113b1ab31d7f63d8eb2251601e8ae0bb0d7b3b0a6` |
| `exec_callback_site_surgery` | Quot.sound, propext | `ecb167fe4a3f4d0e4e827f99ffd8d67a94a4991c0f54814c14dffb86089424e2` | `42b39a0a20bd4120782f1b6e02297391857c451f18058e2b70fa42f07b6e4ae3` |
| `exec_destructor_site_surgery` | Quot.sound, propext | `2f01a2755b606ebe758844e5d96831e35276a4df1742e5f1fe4bcd95b03aabe2` | `201deffb45c30943fe2834f95ad4fd2350ae153072df612b4c128228577cf726` |
| `dropSafe_of_resOk_panicFrom_noPanic` | Quot.sound, propext | `9bca234a314f64b177e9acbeff1ada82fa3eb58083b5dbdfe17ae29f93c86448` | `ac0e9b403a8733aa1e6120141e4d64a465d52731c931c424b9b16e3bbb50c268` |
| `resOk_panicFrom_of_dropSafe` | Quot.sound, propext | `e107c86f97e14b4ca66a20ecb1ce8bde5ddd776e2e6b0c97e2942bfd43bf4041` | `dfce7c65b7a579dc6cd1ca80c1547fc625a57bf9dc5256295dae56e5b2d9ec3c` |
| `unwindEntries_ok_noPanic_imp_ok_or_abort` | Quot.sound, propext | `fe3af12212d2e5d0b851adbd42234b97c2e7209ffd7e967dd5b89479183b1cbc` | `80d5b5dd7cdf6834ae1dee0418fa6aadbe21f46b3580989dfb6aba3744f93cc6` |
| `unwindEntries_eq_noPanic_of_panickers_dropped` | Quot.sound, propext | `8f49f4058069f5f6cd35a6fc7619650d0341f0e0f3dce4d82c3ff5c5149b41de` | `80d5b5dd7cdf6834ae1dee0418fa6aadbe21f46b3580989dfb6aba3744f93cc6` |
| `exec_sites_subset_noPanicDtors` | Quot.sound, propext | `f02059fe71b37409538b9621a98c88852ba7288727c29cb42e06ba501470aeb9` | `c03aa0c8bd3b276a10049e0caef5959aeebd8a27cc6863df805dec9cfd325101` |
| `sites` | Quot.sound, propext | `bb602d96174e90a5a7bf83822f0434df8e395ddde536915bd64ebb29fe7a7706` | `7d0ef4ce724aebaac03a89d4420cdb567b7d90aecc815aeb43da62316b1314ee` |
| `exec` | Quot.sound, propext | `5635e705fdbf8a50ac87a9064cfa69836f485510ed3bdc17588cf69990588eed` | `c313e16febc5c072d9aec96401518b89481e2dda58a7f63cf67b2e2a8350dcc1` |
| `run` | Quot.sound, propext | `9b1cfe32ba026e7cc053ffae56134af929d149870e94c96152779b3a8c7e26ab` | `25be175e8541a1ccee6f1521334e7fb5518d7e14c79596813867ab835414266a` |
| `PanicSafe` | Quot.sound, propext | `389a9d1708807fd8d1e12de35bda9ccd4cdd03b9c3658a6806eb09eacfed14c3` | `0db8e9a64478441b2fcad1c047fc6223ef8c11faf213997ddd6b2beecc6793ea` |
| `applyGuards` | none | `ffef063f07bfc43eee8500a0c69bf8e53eb496fe17f954dea8bc395b38f255b1` | `91e69d5582dc7e5a6a648e25a674899200e7189773ed19957e9cbd0e2084b257` |
| `valueToks` | none | `75f9b9febb3bbd84a3fc54b565acd36d2b09d01b7e4250c40f66b85f1d15ee8b` | `91e69d5582dc7e5a6a648e25a674899200e7189773ed19957e9cbd0e2084b257` |
| `dropSafe_neg_lenPastBuffer` | Quot.sound, propext | `1c0dac79c100787888470b6376f1cbaad00e02afa4c13367f2e624bb375477dc` | `e875e3fbc441eda44f82a5573e664d87e23812f8f6b171b170f57f9ad0963842` |
| `truncateThenCall_satisfies_both_sides` | Quot.sound, propext | `44bc3250d7d254385d284ea77c779b243f63bdd8684aa54b9e05610b30546e65` | `66802b7ab570fc9f0736b99d435bc74931e26fac76abf063ffa02e2ea02713ff` |
| `truncateThenCall_sites_example` | Quot.sound, propext | `209cf027d3c0129a212836b740420614e8f7a6ffa357f8dedff8bdfae98a8ec3` | `8e4448175d3d43f9253c88d16b73dcb5c387b4522ae7d1a62e532ea7034ffe10` |
| `rawRetain_not_callSitesDropSafe` | Quot.sound, propext | `8c8b98148896b038ea8e2140c365f8b7dacb07fe04219f73f696abe7ba2ba535` | `781f1f361ab81ae3b88f6cd176afdd17ba1a6c834324fbc6493037f49488c420` |
| `badSetLen` | none | `e5d2849fc004c5be1ac629651ee30d4e1b2740458bf0bbf96642861f199ac39a` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `truncateLate` | none | `e5d2849fc004c5be1ac629651ee30d4e1b2740458bf0bbf96642861f199ac39a` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `badSetLen_callSitesDropSafe_not_panicSafe` | Quot.sound, propext | `b6dfff20757355b72a1bbc5957ce8a904f69c2744ca0626a54d873ab57f48c42` | `2f59b936cd2c2ccc1d0c13ffce70f19681e323526b9f3bb4e011e2cd2084b2a8` |
| `truncateLate_counterexample` | Quot.sound, propext | `b11953e852671fd88a31fca0d4fc214e145190b0be3e6b0ed0d915c7b44d312a` | `e0e0639046541c11561ea954d7b02f1b70d20a41e10d28c726f7721c28be2422` |
| `truncateThenCall_sites_need_inv` | Quot.sound, propext | `a0deb3031d40ad4b57dde8fee09715522160514bc7dfd76ae764f1b25ad18780` | `85e90c0ef94bc96e0289105ae1d6d631cd51998d823099a490b273722b28bd19` |

#### R5 (Destructor sites count as call sites)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `truncateLate_panicSafe_abort` | Quot.sound, propext | `43d946cfc1db6faaad804aef855a24ccd4521c341b926d45171871f995a5f099` | `ed60552e122b2f828df8237c228769a9eded33326954cc65d1c3f2cf4a54a7b2` |
| `truncateLate_callbackSitesDropSafe` | Quot.sound, propext | `ed6c72653eb914047982cc0f51629725768dc19b0629283f3dd9db5a13262c66` | `da9690a79e3d81c94e8e38d5a990b03932368b321aedd34fc4f6a789fc9026f0` |
| `truncateLate_panicSafeAssumingNoDtorPanic` | Quot.sound, propext | `546fc189e76d4af44afa660d08a0c30f32ab9c39afabd32db70e643dc3395e9f` | `a48cfe8e43907412e8012dac27c7842fd9ce2b798c260ebe09c47a0f966a4ed1` |
| `CallbackSitesDropSafe` | Quot.sound, propext | `28056e52160a69ed05d1dbfcd413cdcb7dc7394f28c658a313a42cd470eb9d5c` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `ceMem1` | none | `1672b993b8f2d09873edb9f6e6d6aa3432cdecfb106ece319f5cb0e7d1312d95` | `c1b50fc287f2903b82340a64425a7e94036b53b7a82f8e6f7c30deb168905302` |
| `truncateLate_sites_destructor` | Quot.sound, propext | `bc87dcf85c0a627f8e8f741f4b0064c48972d24b3cecf2232dc80a1d6d1fc8df` | `112332270280dac964caa14a7e37a24e502ba633bbe7e4e694b971884c8538a4` |
| `truncateLate_dtorPanic_unwound` | Quot.sound, propext | `d786ba9131cb1fd4410896c4c6b7ff4aa7e37c644aa4d4b9aeb623c1d05f6306` | `7c02c4fc38f9d9bfc9162b4f2d25293adb784e35fcf8c43cab7f0eebe5157d1e` |

#### R6 (Leak amplification is sound but leaks)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `leakRetain_unwind_exact` | Classical.choice, Quot.sound, propext | `60036b2bc5bce6bd3f0a80508fac8ef559c88f88a374a23c6fa325d623a2a9d0` | `1fe25ff109cf7610620f7b7db6f1b35d81db5bc68a07e1e269c6c4de20e578d9` |
| `leakRetain_panicSafe_unwind` | Classical.choice, Quot.sound, propext | `83835d0645ae0fd493237ed35a3071c2143f9b73a511f407b991f5f1940c80a1` | `e145820c4562867a9aa6d83fb96cf682ba1d87cb1c6c033f36355af2dac7e075` |
| `leakRetain_unwound_leaks` | Classical.choice, Quot.sound, propext | `782475c9226122b16c8cb538622f71a6c1b22abfbfb5f42f78096b95ef7d3149` | `72f35fc8c14bd218ea7edb7a6024ce8ff0734543ea17ecedc0c8b688dd87d31a` |
| `leakRetain_unwind_exact_upTo3` | Quot.sound, propext | `a6cff67f28d47ba1798daaee508ae60ca5a0842723da489172c597359818087c` | `549bec64cc3d546520e69b96ceaaf8e72ed1736ac7aa8759a0b09d648aa46563` |
| `LeakUnwindExact` | Quot.sound, propext | `90b7a446f844ef5d496733ce302a3c2ec8a3f2c4bb6c780ca9bdb5a699b60d93` | `14238b784397554c18fa0a43ba6266e567dce2e532e93cdd1c156b8fb2f1e537` |
| `LeakFree` | none | `a19c85496cecffafcc9415ab0777517aba2a5da6c4b646d769a05702d9874670` | `c1b50fc287f2903b82340a64425a7e94036b53b7a82f8e6f7c30deb168905302` |
| `leakRetain` | none | `e5d2849fc004c5be1ac629651ee30d4e1b2740458bf0bbf96642861f199ac39a` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `leakRetain_unwind_example` | Quot.sound, propext | `1e9bef96ba80055e3605f2e40d5322f570f1422f04db2cf038d59496832bcbe2` | `c94e1ddbf4788b7047d938170dd5d1878d429e246edc13817106699b771958c1` |
| `leakUnwindExact_pos` | Quot.sound, propext | `4e1feea03da7da57fc2b74a01887b2db7b82c9d1bb8354401fc73a1ef737a1f3` | `2d3c8ae72fac38379434ac1c62b30293631cffc6bd8be16bd19610da62558869` |
| `leakUnwindExact_return_pos` | Quot.sound, propext | `104ef4e380108014f6f9536c6e1f2d204b0f898893d727da1a92fd947eaac846` | `55dee31d8e779bd6f0c2d506c74a5e04fb7831e47fbe7171a568a974d5060ccd` |
| `leakRetain_unwind_exact_needs_inv` | Quot.sound, propext | `80412abf05c2c68df5858595cd1b9681bd7f48a58ceeb83cb22f9784749ac2ed` | `ed916ede76ef68535296c7549a8e6d508187bcb3c52d29823413149e130c15a8` |
| `leakRetain_unwound_leaks_needs_inv` | Quot.sound, propext | `2b2e8b8b9a95f1d4985403cb4669349c29e8ce19c378a0d0310540abf95eb513` | `f9c2e41f9c1020dee1866ee46b7ebca3aff4cf732f6ee1c40904ffc8d9271666` |

#### R7 (A drop guard updated before each destructor is exact on unwind)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `guardRetain_unwind_exact` | Quot.sound, propext | `adae3356a11c6b221112900c79f324f112122718f50ac178baa4f224debb5ff9` | `b44216ba616914b6951e2edaf564d7bfba86664a576e54af3357c3b6e51d4cb1` |
| `guardRetain_panicSafe_unwind` | Quot.sound, propext | `c773025b0631f88ebdc30b7892e4332bc68dedea0ec0ed27f639c876709a5445` | `919c4d3cf3d53ebfdf2a6be96dac67390052ccd1678dc609e658c4bbb0b9e01b` |
| `guardRetain_unwind_exact_upTo3` | Quot.sound, propext | `01b0a14776a8a458558ef70a385e1372296ee9e176597fc3cd658c365d48db43` | `0504f3646cc1e53ab592df2332e8efab8bc61daa2fae603d820371428d8924d1` |
| `GuardUnwindExact` | Quot.sound, propext | `90b7a446f844ef5d496733ce302a3c2ec8a3f2c4bb6c780ca9bdb5a699b60d93` | `14238b784397554c18fa0a43ba6266e567dce2e532e93cdd1c156b8fb2f1e537` |
| `backshift` | propext | `07719b5828d6b0980599c3e751603a69dda87c986e55e9eeefe9fb217e4544d3` | `cdd257e0e0e9c751f32ceb847b9e272302ea17845dde834818a647705f326b25` |
| `copyRange` | propext | `e8e89e4ca7d910cd42ecf22058d03a6642dff2b129cb5bf7644850ed06809387` | `173abd5377880f62f080f2e29f93bfd193ff1499dbd18e73f5ebf5bac4e22b36` |
| `guardLoop` | propext | `9aa46649f9c6d07b4ec575a9b20c6bd3aac9924cc761c9c8f99870db74886bcf` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `guardRetain` | propext | `e5d2849fc004c5be1ac629651ee30d4e1b2740458bf0bbf96642861f199ac39a` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `guardRetain_ownerDrop_doublePanic_aborts_example` | Quot.sound, propext | `56ee24169a0fa551ecc75bb48a3df87e047956fedb549e8e1ae8ef58341b97c8` | `d8344c1f971c77ddda922df91cd92963ffa3eaa681d623c651cabe1c8e9a7524` |
| `guardRetain_unwind_example` | Quot.sound, propext | `4bc4fd07a2b6594bc9e70f0afc2cd847f807793b348eb96b4a9c9087000a4741` | `a56e9ea8a0edc496ad7261d5a458a3c68bd3803db94ee39b31701ad18a37dc78` |
| `guardRetain_dtorPanic_example` | Quot.sound, propext | `9939f655199596a7904a8bd4914c12627f77940585abe8cceab22a1ad9c328be` | `71625f1ec110fa6ab60963452505db3093ba7f3821f052cb2d7fcb1b33ff8e6d` |
| `guardUnwindExact_return_pos` | Quot.sound, propext | `630f84b0b1142789272cefcc3af925a7f4d98979f346718f03823d9b006016fc` | `c48152f63f317d61a8fffc2c61209e6e049f650bdb394e097590634279e5242f` |
| `containerDrop` | Quot.sound, propext | `54bcaceab515da453ab1b0d35d2f724e5a99a896ba9e9e11b8d1717c2816f986` | `5c4dc765d86b21010ccafe8aa66429b02340779de815a147f4bd1b7482d8f8d1` |
| `guardRetain_unwind_exact_needs_inv` | Quot.sound, propext | `ff215b0749c10383944f661508053c68c6b695dbc35666b7e136f74502bff815` | `40b6ece2e2eb4361dba389f2de4de5aa55b34424333d15ebde51c1be07a7d295` |

#### R8 (The guard is leak-free on unwind)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `guardRetain_unwound_leakFree` | Quot.sound, propext | `f0bd22f3cfa3258f17d2e5bd65d78f1f9b651064740edfa579e5540ce7667634` | `a601f13c0f9f1d8ef268890345722b3b2538e0f8f4216d3b73d77dcf5378078e` |
| `guardRetain_unwound_leakFree_upTo3` | Quot.sound, propext | `c9bcb99c21df6ace77925dce102f4b08ed39bb278cca7caf2291ef3e9d8bd3c1` | `2aff3361e1042fda1126a1ba36ece76ed4d69d73c178c936852585d6d9070349` |
| `guardRetain_unwound_leakFree_noInv_bounded` | Quot.sound, propext | `f8b41cd080ec39bfe3e7f598c6a7f189010ec02eea39775ebec8a581ea1f3d83` | `86b4c5da3c8bad621460644cab42b63edf81ba7675e58cd3edb4b9bd20c929f1` |
| `GuardUnwoundLeakFree` | Quot.sound, propext | `90b7a446f844ef5d496733ce302a3c2ec8a3f2c4bb6c780ca9bdb5a699b60d93` | `14238b784397554c18fa0a43ba6266e567dce2e532e93cdd1c156b8fb2f1e537` |
| `smallMems` | none | `adbb93b4e4e9736f787212de326d49920f06a264f007162281c005297fb5d500` | `c1b50fc287f2903b82340a64425a7e94036b53b7a82f8e6f7c30deb168905302` |
| `smallBufs` | none | `01202662f00d29b1ea256c8876b67b7f71dd7cc2e0915314e713e84690bb48e4` | `173abd5377880f62f080f2e29f93bfd193ff1499dbd18e73f5ebf5bac4e22b36` |
| `ceMem3` | none | `1672b993b8f2d09873edb9f6e6d6aa3432cdecfb106ece319f5cb0e7d1312d95` | `c1b50fc287f2903b82340a64425a7e94036b53b7a82f8e6f7c30deb168905302` |
| `grd_absRetain_mem` | propext | `423dceb4731057628f5e0645b814ddf3e1bafa8ec965651baae98c6b0d043caa` | `f5be248d222d18acf5f2160f4c19552068807e364763294538b6c066c304cb55` |
| `guardRetain_unwound_leakFree_noInv` | Quot.sound, propext | `75f348d00b98a00f780c6c545a1e8c13e0c5638c6be1c5ddc0ec65c486502732` | `30c7cc70519eb11646d06844a89c8a997ca2e87d6d74d0620b4b062f1c26d39d` |

#### R9 (A guard updated after each destructor is panic-safe when no destructor panics)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `guardRetainLate_panicSafe_unwind_of_noPanickingDtors` | Quot.sound, propext | `353ef74192ca9eff1852bcbe47670a9bd14a8352229b6246147986b9158b6807` | `0af364836dd978620009500451aa191acb8e7370fbd2bb1c9cd878ba5532c26d` |
| `guardRetainLate_panicSafe_upTo3` | Quot.sound, propext | `bf57e62906598bbdaae7134548e03b63d1b42f6934611b9045fc4989c927dcbe` | `a143ebf1d3b636d1d3d76651568c0e22c4e581fbd352fa83b806ba30610aa08b` |
| `guardLoopLate_eq_guardLoop_of_noPanickingDtors` | Quot.sound, propext | `f2877af165fb77770ed1e5effb441e164b0abec87b9c2a7cf7f9a90ed493cca2` | `ae76e7251184e448350d2e808742bdca22a4134855feb4a2b539b40ebc891499` |
| `PanicSafeAssumingNoDtorPanic` | Quot.sound, propext | `389a9d1708807fd8d1e12de35bda9ccd4cdd03b9c3658a6806eb09eacfed14c3` | `0db8e9a64478441b2fcad1c047fc6223ef8c11faf213997ddd6b2beecc6793ea` |
| `NoPanickingDtors` | none | `c1d95f37a06a475c0a448e12cad80e85be9b3cf3c9e241f47a7328285923af6f` | `fc7540626dbb54d2dcc1ac7529879f86798c8767a093d94e558bd55b7e6d94c9` |
| `guardRetainLate` | propext | `e5d2849fc004c5be1ac629651ee30d4e1b2740458bf0bbf96642861f199ac39a` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `guardLoopLate` | propext | `9aa46649f9c6d07b4ec575a9b20c6bd3aac9924cc761c9c8f99870db74886bcf` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `guardRetainLate_noPanic_example` | Quot.sound, propext | `ed016fc4c26cd73f19c1c6740eeec4243c4305b964d70def541a6282e25c68e7` | `ee5bd33db1375352031149ff2202bf268f5dbad2b1307656811f0d8c6131d424` |
| `guardRetainLate_dtorPanic_counterexample` | Quot.sound, propext | `2600833e7e08d565f482924f34e7e4577b13f13bfd630373f1715420bc028dc5` | `37c19cb2895c904220a3330393b5d77ac8a8e24e993261b4d732ad430caec27e` |
| `guardRetainLate_needs_inv` | Quot.sound, propext | `34f0ef1410d93168582191d17d0c1103a304f88b5aedc6a72d21c2fb28ce5307` | `1bac90f4b3dd6ad3e747d28b194ad4323d16495aacf27b78b17b90b4aac4983a` |

#### R11 (The toy destructor-reliant drain reaches UB once `forgetGuard` is available)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `destructorReliantDrain_forget_reachesUB` | Quot.sound, propext | `386b02527276781816f2461e96294d4769f71a703f96a1f69aa6eac30085ea6b` | `c8e57bd21fe9ca8ca992289cb35e99b1fd018c741ab8aa0915fc2d5da298b1ef` |
| `leakAmplifiedDrain_forgetClient_ok` | Quot.sound, propext | `e3a93377b6bf6d25844b740d03bd7b959dd2142ce2a09b776f4400de05cf6374` | `c8e57bd21fe9ca8ca992289cb35e99b1fd018c741ab8aa0915fc2d5da298b1ef` |
| `forgetClient` | none | `24ea0a355d856ae38ae524c8b67c853e4323016e9764060040bea3d25a1c2d67` | `f982ccfe02f8f0249fe2856edc443fa2a3328558afdad5005ae7ca7eb29ae886` |
| `clientRun` | Quot.sound, propext | `334e5995ad462583fedc8392bf42083fee994c00563f0d89d6d513b22c41876c` | `e9fcefee5347b1fe408d82d3a5ae36177f55e4d7227f16c9be99ed78ecaddf4b` |
| `crun` | Quot.sound, propext | `8b0a3687c92d5aa9cb66a9855e2ee8b09a5e93fda49270a683809d61bd67341d` | `e9fcefee5347b1fe408d82d3a5ae36177f55e4d7227f16c9be99ed78ecaddf4b` |
| `cstep` | Quot.sound, propext | `d1aa4b266ea370d0684bdb8205c627e0c7d357fc3dfb835ffc85da1224fd20cc` | `e9fcefee5347b1fe408d82d3a5ae36177f55e4d7227f16c9be99ed78ecaddf4b` |
| `cend` | Quot.sound, propext | `f8ccfc682c4b336d330966e0f00d299b61ed639b48dce8951ccda31fcba6f72c` | `4469a9021d3e4c1ca4f69cba39cee1405a786b99217116f43d805de7e75fa7d8` |
| `leakAmplifiedDrain_noUB` | Quot.sound, propext | `fafad13cc4d03e912e52e359b63d963c531761bce38b2aabcbf9ef148723c620` | `2e5259b930781fdc8524b0a021bac909c6d43b8dc68114f00a51c499ae91b73d` |
| `destructorReliantDrain_noUB_withoutForgetGuard` | Quot.sound, propext | `7e5e431154209a92a6ae3584e319423a861d6f3732ad8ec372de4dcfba2643db` | `2e5259b930781fdc8524b0a021bac909c6d43b8dc68114f00a51c499ae91b73d` |
| `closureScopedDrain_panicSafe_unwind` | Classical.choice, Quot.sound, propext | `2acc407819f6e94da9fe77a54f982f945029d5dbfd0d11998938c84c746c86ea` | `c511b8f86bdf8da421147a9889827a10b5d8ba22fec14d89c19d5448ba1cc7f7` |

#### R12 (The leak-amplified drain reaches no UB under safe `forget`)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `leakAmplifiedDrain_noUB_upTo4` | Quot.sound, propext | `88eaa77a2e0be658b5219d5f0b84150e981ae3c54d2ae8d28789bc24dbf3e935` | `d6274e7731f2d60305b9f4f0c1ed34992f9c69c658e3c2d9fb5ba868540b6d26` |
| `DrainClientInv` | none | `0d737a4b1b8f52fe7fb8b08f7558c2237df52a1d1bd14f247858160c47317e9e` | `bae9c8f045038d0dec7f42d60d6b91342f41eaad890ffe908ece150edaa1c5a6` |
| `cl_crun_ne_ub` | Quot.sound, propext | `62bb6370a91d7912a1b2e40049d8431b8f842cc6422269dd108f2da62a2c1b4a` | `c51a49c36e512cd46ef45476437f441d75877bb669f0fe493e778d566dd2f1c4` |
| `cl_clientInv_init` | none | `5fc67bf906f42e9738e2082bbe18ae75c51b2c56b240a4abc0d2799aa72071be` | `101df57f85024c01808c061921e52972bd9456a7a28549db3adef164f4278312` |
| `dropIdxRange` | Quot.sound, propext | `74133d6e7fdaee1498266f4843a65af23f159700665287c4e81be8dea3be24df` | `173abd5377880f62f080f2e29f93bfd193ff1499dbd18e73f5ebf5bac4e22b36` |
| `dropToks` | Quot.sound, propext | `6d58f9e1fc96fa5307acdb67fa3cabd11a943494d3a0416264c4ac69b58d80d5` | `9c7a0cad53124f08c212f508728f8a6f0d3896b24e68f02be598298c18a6494a` |
| `COut` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `drainClients_need_inv` | Quot.sound, propext | `85b5a926e6d7e617d45270bfd4284424e02a1c3d987d06bf910136ca8c5eaffa` | `728e13b2d3af14cd90e69d2ade8bec6e64b67d717ecebb5ea5b6ac6e4061c954` |
| `leakAmplifiedDrain_forgetGuard_leaks` | Quot.sound, propext | `0bbb0228428d51db345ecc79a081cec97541f37145dcc09442544eae102f1a04` | `4a5340741540302fa1f0a863bf08cb338ea1e8f585395921529910d89e391335` |

#### R13 (Without `forgetGuard`, the destructor-reliant drain reaches no UB)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `destructorReliantDrain_noUB_withoutForgetGuard_upTo4` | Quot.sound, propext | `9bf33abf6d6c766527378ece92de91e1b170083f6209ddc4bf369ee6bf75b10c` | `d6274e7731f2d60305b9f4f0c1ed34992f9c69c658e3c2d9fb5ba868540b6d26` |
| `destructorReliantDrain_forgetVal_example` | Quot.sound, propext | `7fd75cfa0c1549a1a0e18c63634350c4c810be81cb4084d66aaae3475be045f1` | `94bba00852b6c4b1cdcd95463e1ce7ae59acadef636591daf44250818dfff5cd` |
| `destructorReliantDrain_noForget_example` | Quot.sound, propext | `0d723630a32a86b899c4627138b2f8297c49eec0eeba449a542127b931412e31` | `94bba00852b6c4b1cdcd95463e1ce7ae59acadef636591daf44250818dfff5cd` |

#### R14 (A closure-scoped drain is panic-safe under unwinding)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `closureScopedDrain_panicSafe_unwind_upTo3` | Quot.sound, propext | `c3e2239c8f4681ea25448a9fce0d6659cc63d391f3dae75361adb7e76408e142` | `4e10e5d9ce00948f5eb2ecd1f3be6be6e94480747dde52f8b3e988e42631c90d` |
| `tailFix` | propext | `ef95eb1ba11e24745221bff9ba1c9ff4b2261e954c9fd6363fe76d6d52209d81` | `cdd257e0e0e9c751f32ceb847b9e272302ea17845dde834818a647705f326b25` |
| `drainWithLoop` | propext | `f4abca05398c6c553c574ea021a3ababf1445b5d1b49f12e3063ba21fbc0bbc1` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `drainWith` | propext | `e5d2849fc004c5be1ac629651ee30d4e1b2740458bf0bbf96642861f199ac39a` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `dw_loop` | Classical.choice, Quot.sound, propext | `4b32c00a14b25774d20b46b26cc5c87d4be4ac6720458d7cf9e2e34100559e84` | `a36c21d43841ec5268eccb9ff78d14d5b7bccd994a9964c27f1e3082ea2dba93` |
| `dw_inv_fix` | Classical.choice, Quot.sound, propext | `bc699a3d8abfa814241428e6a13f868f318fdf60169910af7caded59e0c3aada` | `6cd1c01e7b9fc04f9889653975d3868679c5844e7eea18e01e80add5fbefa1ec` |
| `dw_copyRange_getElem?_shift` | Quot.sound, propext | `0c388c9fa1ae6774171d0384416dbf09f77651fb64a73f9acd84900afd46006b` | `6ba4924a123a1130464b071748a973dc069e82821b3a6a716c49d6576b6eda56` |
| `closureScopedDrain_example` | Quot.sound, propext | `72606c1cca2164b771c838787b3009a7c35b6478e354242c5ec87f0ae159d0e0` | `e67481856cc233ed86b3a3c4cff78c63f599637d701f7b70c153703081d270bc` |
| `ResOk` | none | `141f4a078c5a24fc9fb0e60d09357eadf7aad7473811fcc2fdab2f65b163837d` | `562eb0dd4dda9c3a7626181840627e254e4f6274449e4ddcaff4acae45bcb452` |
| `drainWith_needs_inv` | Quot.sound, propext | `4c429fbf6191867b430388d320196931190ca38e8588e5d3494af59487aa1718` | `04ea59e942fa99ad9127fc9123874512afb21ca2ae76b905f1b50a16b592a1b2` |

#### R15 (Memory panic safety does not imply preservation of a logical invariant on unwind)

| Lean name (namespace `Toy.PanicSafety`) | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `panicSafe_unwind_but_countersAgree_broken` | Quot.sound, propext | `dbb6941e376af381a863d83ac7db83e8c2f7f9e85fc7d31a8fa8757d0d4d08e9` | `3753e1813fb3ce7acfdaaf0ae790ec4a4ffd69053693747ffbc8a749d8a1bfdf` |
| `bumpBoth` | none | `e5d2849fc004c5be1ac629651ee30d4e1b2740458bf0bbf96642861f199ac39a` | `2462d65f20b393bf2463cc6d395ef641e84f3b323388b3e065179f23de082154` |
| `CountersAgree` | none | `977b62e744fb93d2e08a276ba6f36f1cd996e9b9e1e1b3985f2518d719cc879b` | `c1b50fc287f2903b82340a64425a7e94036b53b7a82f8e6f7c30deb168905302` |
| `bumpBoth_needs_inv` | Quot.sound, propext | `7e38bd0d33e50fa08679fa95012d6c5045264ccfded297c1d0a202b631183d03` | `c591d6f4b294b18aa045c1ce638e9968256db74615338635e71ddab8f4bc6163` |
| `bumpBoth_unwind_example` | Quot.sound, propext | `a1f2cc94115d4c2d0e3804531dc558c586898e71b77dfac189ba8914c9b9d495` | `d2b455e9b1415315ea7934024cc1e6ce7f554545897f0cb94a6b38ecfbcedb3c` |

### Auxiliary declarations cited by name

Every package-local declaration that this report mentions by name and that is not quoted under **Applicability** (definitions) or in a card statement block under **Findings** is quoted here verbatim, with its `file:line` range; proofs are elided, and equation-style declarations are quoted up to the end of their signature.

```lean
-- lean/PanicSafety/Examples.lean:18
theorem inv_pos : Inv ⟨[some 0, some 1], 2, [], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:20
theorem inv_pos_staleTail : Inv ⟨[some 0, some 0], 1, [], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:22
theorem inv_pos_countersDisagree : Inv ⟨[], 0, [], 1, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:23
theorem inv_neg_lenPastBuffer : ¬ Inv ⟨[some 0], 2, [], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:24
theorem inv_neg_duplicate : ¬ Inv ⟨[some 0, some 0], 2, [], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:25
theorem inv_neg_dropped : ¬ Inv ⟨[some 0, some 1], 2, [0], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:26
theorem inv_neg_uninit : ¬ Inv ⟨[none], 1, [], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:13
theorem ownsUniquely_pos : OwnsUniquely [] [some 0, some 1] := by …
```

```lean
-- lean/PanicSafety/Examples.lean:14
theorem ownsUniquely_neg_duplicate : ¬ OwnsUniquely [] [some 0, some 0] := by …
```

```lean
-- lean/PanicSafety/Examples.lean:15
theorem ownsUniquely_neg_dropped : ¬ OwnsUniquely [0] [some 0] := by …
```

```lean
-- lean/PanicSafety/Examples.lean:16
theorem ownsUniquely_neg_uninit : ¬ OwnsUniquely [] [none] := by …
```

```lean
-- lean/PanicSafety/Examples.lean:30
theorem noPanickingDtors_pos : NoPanickingDtors noPanicDtors := …
```

```lean
-- lean/PanicSafety/Examples.lean:31
theorem noPanickingDtors_neg : ¬ NoPanickingDtors dtPanicsOn0 := …
```

```lean
-- lean/PanicSafety/Examples.lean:40-42
theorem unwindEntries_example :
    unwindEntries noPanicDtors [.value 5, .guard (backshift 1 1 2)] ⟨[some 0, some 1], 2, [0], 0, 0⟩ =
      .ok ⟨[some 1, some 1], 1, [5, 0], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:44-45
theorem unwindEntries_example_abort :
    unwindEntries dtPanicsOn0 [.value 0] ⟨[], 0, [], 0, 0⟩ = .abort := by …
```

```lean
-- lean/PanicSafety/Examples.lean:37-38
theorem backshift_example :
    (backshift 1 1 3).fix [some 9, some 1, some 2] 3 = ([some 1, some 2, some 2], 2) := by …
```

```lean
-- lean/PanicSafety/Characterization.lean:931-933
theorem truncateThenCall_sites_example :
    (sites (tableOf []) noPanicDtors truncateThenCall ceMem1).map (·.kind) =
      [.destructor, .callback] := by …
```

```lean
-- lean/PanicSafety/Examples.lean:95
theorem panicSafe_pos : PanicSafe .unwind truncateThenCall := …
```

```lean
-- lean/PanicSafety/Examples.lean:97
theorem panicSafe_neg : ¬ PanicSafe .unwind truncateLate := …
```

```lean
-- lean/PanicSafety/Examples.lean:99
theorem panicSafe_neg_rawRetain : ¬ PanicSafe .unwind rawRetain := by …
```

```lean
-- lean/PanicSafety/Examples.lean:105-106
theorem panicSafeAssumingNoDtorPanic_pos :
    PanicSafeAssumingNoDtorPanic .unwind truncateLate := …
```

```lean
-- lean/PanicSafety/Examples.lean:108
theorem panicSafeAssumingNoDtorPanic_neg : ¬ PanicSafeAssumingNoDtorPanic .unwind rawRetain := by …
```

```lean
-- lean/PanicSafety/Examples.lean:47
theorem containerDrop_pos : containerDrop noPanicDtors ceMem2 = .ok [1, 0] := by …
```

```lean
-- lean/PanicSafety/Examples.lean:48-49
theorem containerDrop_neg_doubleDrop :
    containerDrop noPanicDtors ⟨[some 0, some 1], 2, [0], 0, 0⟩ = .ub := by …
```

```lean
-- lean/PanicSafety/Examples.lean:50-51
theorem containerDrop_neg_lenPastBuffer :
    containerDrop noPanicDtors ⟨[some 0], 2, [], 0, 0⟩ = .ub := by …
```

```lean
-- lean/PanicSafety/Examples.lean:68-73
theorem guardRetain_ownerDrop_doublePanic_aborts_example :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveKeepPanic (dtOf [false, true]) guardRetain ceMem3 =
      .unwound ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    Inv ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    harness .unwind ceCbRemoveKeepPanic (dtOf [false, true]) guardRetain ceMem3 = .aborted := by …
```

```lean
-- lean/PanicSafety/Examples.lean:79-81
theorem dropSafe_pos_guardRepairs :
    ¬ Inv ⟨[some 0, some 1], 2, [0], 0, 0⟩ ∧
    DropSafe [.guard (backshift 1 1 2)] ⟨[some 0, some 1], 2, [0], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:84
theorem dropSafe_neg_localDuplicates : ¬ DropSafe [.value 0] ceMem1 := by …
```

```lean
-- lean/PanicSafety/Examples.lean:88-91
theorem dropSafe_neg_lenPastBuffer :
    OwnsUniquely [] ((valueToks []).map some ++
      (applyGuards [] ([some 0], 2)).1.take (applyGuards [] ([some 0], 2)).2) ∧
    ¬ DropSafe [] ⟨[some 0], 2, [], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:130-131
theorem specRetain_example :
    specRetain ceCbRemoveKeepPanic noPanicDtors [0, 1, 2] = ⟨[1], [0], [2], .callbackPanic⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:134-135
theorem specRetain_example_dtorPanic :
    specRetain ceCbRemove dtPanicsOn0 [0, 1] = ⟨[], [0], [1], .dtorPanic⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:137-138
theorem retainReturns_pos :
    RetainReturns ⟨[1], [0], [], .finished⟩ ceMem2 ⟨[some 1, some 1], 1, [0], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:139-140
theorem retainReturns_neg_wrongDropLog :
    ¬ RetainReturns ⟨[1], [0], [], .finished⟩ ceMem2 ⟨[some 1, some 1], 1, [], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:142
theorem leakFree_pos : LeakFree ceMem2 ⟨[some 1], 1, [0], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:143
theorem leakFree_neg : ¬ LeakFree ceMem2 ⟨[some 1], 0, [0], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:149-151
theorem rawAbortExact_pos :
    Inv ceMem3 ∧ run .abort ceCbRemoveKeepPanic noPanicDtors rawRetain ceMem3 = .abort ∧
    RawAbortExact ceCbRemoveKeepPanic noPanicDtors ceMem3 := by …
```

```lean
-- lean/PanicSafety/Examples.lean:152-156
theorem leakUnwindExact_pos :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveKeepPanic noPanicDtors leakRetain ceMem3 =
      .unwound ⟨[some 1, some 1, some 2], 0, [0], 0, 0⟩ ∧
    LeakUnwindExact ceCbRemoveKeepPanic noPanicDtors ceMem3 := by …
```

```lean
-- lean/PanicSafety/Examples.lean:157-161
theorem guardUnwindExact_pos :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveKeepPanic noPanicDtors guardRetain ceMem3 =
      .unwound ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    GuardUnwindExact ceCbRemoveKeepPanic noPanicDtors ceMem3 := by …
```

```lean
-- lean/PanicSafety/Examples.lean:168-172
theorem rawAbortExact_return_pos :
    Inv ceMem3 ∧
    run .abort ceCbRemoveFirst noPanicDtors rawRetain ceMem3 =
      .ret ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    RawAbortExact ceCbRemoveFirst noPanicDtors ceMem3 := by …
```

```lean
-- lean/PanicSafety/Examples.lean:173-177
theorem leakUnwindExact_return_pos :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveFirst noPanicDtors leakRetain ceMem3 =
      .ret ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    LeakUnwindExact ceCbRemoveFirst noPanicDtors ceMem3 := by …
```

```lean
-- lean/PanicSafety/Examples.lean:178-182
theorem guardUnwindExact_return_pos :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveFirst noPanicDtors guardRetain ceMem3 =
      .ret ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    GuardUnwindExact ceCbRemoveFirst noPanicDtors ceMem3 := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:1145-1146
theorem rawRetain_abort_exact_needs_inv :
    ¬ Inv dupMem ∧ ¬ RawAbortExact (tableOf []) noPanicDtors dupMem := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:1149-1150
theorem leakRetain_unwind_exact_needs_inv :
    ¬ Inv dupMem ∧ ¬ LeakUnwindExact (tableOf []) noPanicDtors dupMem := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:1153-1154
theorem guardRetain_unwind_exact_needs_inv :
    ¬ Inv dupMem ∧ ¬ GuardUnwindExact (tableOf []) noPanicDtors dupMem := by …
```

```lean
-- lean/PanicSafety/Examples.lean:114
theorem callSitesDropSafe_pos : CallSitesDropSafe truncateThenCall := …
```

```lean
-- lean/PanicSafety/Examples.lean:117
theorem callSitesDropSafe_neg : ¬ CallSitesDropSafe rawRetain := …
```

```lean
-- lean/PanicSafety/Examples.lean:119
theorem callbackSitesDropSafe_pos : CallbackSitesDropSafe truncateLate := …
```

```lean
-- lean/PanicSafety/Examples.lean:122
theorem callbackSitesDropSafe_neg : ¬ CallbackSitesDropSafe rawRetain := by …
```

```lean
-- lean/PanicSafety/Examples.lean:191
theorem clientRun_rejected_example : clientRun .leakAmplified [.next] ceMem1 = .rejected := by …
```

```lean
-- lean/PanicSafety/Examples.lean:194-195
theorem clientRun_drainTwice_rejected :
    clientRun .destructorReliant [.drain, .drain] ceMem1 = .rejected := by …
```

```lean
-- lean/PanicSafety/Forget.lean:171-174
theorem destructorReliantDrain_noForget_example :
    Inv ceMem1 ∧ CInstr.forgetGuard ∉ ([.drain, .next, .dropVal] : List CInstr) ∧
    clientRun .destructorReliant [.drain, .next, .dropVal] ceMem1 =
      .ok ⟨⟨[some 0], 0, [0], 0, 0⟩, [], none⟩ := by …
```

```lean
-- lean/PanicSafety/Forget.lean:180-183
theorem destructorReliantDrain_forgetVal_example :
    Inv ceMem1 ∧ CInstr.forgetGuard ∉ ([.drain, .next, .forgetVal] : List CInstr) ∧
    clientRun .destructorReliant [.drain, .next, .forgetVal] ceMem1 =
      .ok ⟨⟨[some 0], 0, [], 0, 0⟩, [], none⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:186
theorem countersAgree_pos : CountersAgree ⟨[], 0, [], 2, 2⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:187
theorem countersAgree_neg : ¬ CountersAgree ⟨[], 0, [], 1, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Examples.lean:57-60
theorem dropSafety_adequacy_fails_with_panickingDtors :
    (¬ Inv dupMem ∧ containerDrop dtPanicsOn0 dupMem = .abort) ∧
    (DropSafe [.value 0] ⟨[], 0, [], 0, 0⟩ ∧
      unwindEntries dtPanicsOn0 [.value 0] ⟨[], 0, [], 0, 0⟩ = .abort) := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:791-794
theorem rawRetain_unwind_noRemoval_example :
    run .unwind (tableOf [.ret true, .panic]) noPanicDtors rawRetain ceMem2 = .unwound ceMem2 ∧
    Inv ceMem2 ∧
    (specRetain (tableOf [.ret true, .panic]) noPanicDtors (toks ceMem2.elems)).rejected = [] := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:1160-1164
theorem rawRetain_unwound_iff_needs_inv :
    ¬ Inv dupMem ∧
    run .unwind (tableOf [.panic]) noPanicDtors rawRetain dupMem = .unwound dupMem ∧
    ¬ (Inv dupMem ↔
      (specRetain (tableOf [.panic]) noPanicDtors (toks dupMem.elems)).rejected = []) := by …
```

```lean
-- lean/PanicSafety/Characterization.lean:804-806
theorem badSetLen_callSitesDropSafe_not_panicSafe :
    CallSitesDropSafe badSetLen ∧ ¬ PanicSafe .abort badSetLen ∧
    ¬ PanicSafe .unwind badSetLen := by …
```

```lean
-- lean/PanicSafety/Characterization.lean:950-952
theorem truncateThenCall_sites_need_inv :
    PanicSafe .unwind truncateThenCall ∧ ¬ Inv dupMem ∧
    ∃ s ∈ sites (tableOf []) noPanicDtors truncateThenCall dupMem, ¬ DropSafe s.entries s.mem := by …
```

```lean
-- lean/PanicSafety/Characterization.lean:924-926
theorem truncateThenCall_satisfies_both_sides :
    PanicSafe .unwind truncateThenCall ∧ PanicSafe .abort truncateThenCall ∧
    CallSitesDropSafe truncateThenCall := …
```

```lean
-- lean/PanicSafety/Characterization.lean:940
theorem rawRetain_not_callSitesDropSafe : ¬ CallSitesDropSafe rawRetain := by …
```

```lean
-- lean/PanicSafety/Characterization.lean:840-841
theorem truncateLate_panicSafeAssumingNoDtorPanic :
    PanicSafeAssumingNoDtorPanic .unwind truncateLate := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:1170-1178
theorem leakRetain_unwound_leaks_needs_inv :
    ¬ Inv ⟨[some 0], 1, [0], 0, 0⟩ ∧
    run .unwind (tableOf [.panic]) noPanicDtors leakRetain ⟨[some 0], 1, [0], 0, 0⟩ =
      .unwound ⟨[some 0], 0, [0], 0, 0⟩ ∧
    ¬ (toks (Mem.elems ⟨[some 0], 0, [0], 0, 0⟩) = [] ∧
      ∀ t ∈ toks (Mem.elems ⟨[some 0], 1, [0], 0, 0⟩),
        (t ∈ (⟨[some 0], 0, [0], 0, 0⟩ : Mem).dropped ↔
          t ∈ (specRetain (tableOf [.panic]) noPanicDtors
            (toks (Mem.elems ⟨[some 0], 1, [0], 0, 0⟩))).rejected)) := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:877-881
theorem leakRetain_unwind_example :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveKeepPanic noPanicDtors leakRetain ceMem3 =
      .unwound ⟨[some 1, some 1, some 2], 0, [0], 0, 0⟩ ∧
    ¬ LeakFree ceMem3 ⟨[some 1, some 1, some 2], 0, [0], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:999-1004
theorem guardRetain_unwind_example :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveKeepPanic noPanicDtors guardRetain ceMem3 =
      .unwound ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    Inv ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    LeakFree ceMem3 ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:1018-1021
theorem guardRetain_dtorPanic_example :
    Inv ceMem1 ∧
    run .unwind ceCbRemove dtPanicsOn0 guardRetain ceMem1 = .unwound ⟨[some 0], 0, [0], 0, 0⟩ ∧
    Inv ⟨[some 0], 0, [0], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:651-654
theorem grd_absRetain_mem (cb : Callback) (dt : DtorTable) :
    ∀ (xs : List Tok) (j : Nat) (kept rej : List Tok) (t : Tok), t ∈ xs ∨ t ∈ kept ∨ t ∈ rej →
      t ∈ (absRetain cb dt xs j kept rej).kept ∨ t ∈ (absRetain cb dt xs j kept rej).rejected ∨
        t ∈ (absRetain cb dt xs j kept rej).rest := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:1025-1029
theorem guardLoopLate_eq_guardLoop_of_noPanickingDtors (cb : Callback) (dt : DtorTable)
    (hdt : NoPanickingDtors dt) (n : Nat) :
    ∀ (r p d j : Nat) (es : List Entry) (m : Mem),
      (exec .unwind cb dt (guardLoopLate n r p d) j es m).1 =
      (exec .unwind cb dt (guardLoop n r p d) j es m).1
```

```lean
-- lean/PanicSafety/RetainResults.lean:1113-1118
theorem guardRetainLate_dtorPanic_counterexample :
    Inv ceMem1 ∧ ¬ NoPanickingDtors dtPanicsOn0 ∧
    run .unwind ceCbRemove dtPanicsOn0 guardRetainLate ceMem1 =
      .unwound ⟨[some 0], 1, [0], 0, 0⟩ ∧
    ¬ Inv ⟨[some 0], 1, [0], 0, 0⟩ ∧
    harness .unwind ceCbRemove dtPanicsOn0 guardRetainLate ceMem1 = .ub := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:1184-1186
theorem guardRetainLate_needs_inv :
    ¬ Inv dupMem ∧ NoPanickingDtors noPanicDtors ∧
    ¬ ResOk (run .unwind (tableOf []) noPanicDtors guardRetainLate dupMem) := …
```

```lean
-- lean/PanicSafety/RetainResults.lean:1132-1136
theorem guardRetainLate_noPanic_example :
    NoPanickingDtors noPanicDtors ∧ Inv ceMem3 ∧
    run .unwind ceCbRemoveKeepPanic noPanicDtors guardRetainLate ceMem3 =
      .unwound ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    Inv ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Forget.lean:304-310
def DrainClientInv (api : DrainApi) (s : CState) : Prop :=
  match s.guard with
  | none => s.mem.len ≤ s.mem.buf.length ∧
      OwnsUniquely s.mem.dropped (s.vals.map some ++ s.mem.elems)
  | some (c, e) => c ≤ e ∧ e ≤ s.mem.buf.length ∧
      OwnsUniquely s.mem.dropped (s.vals.map some ++ (s.mem.buf.drop c).take (e - c)) ∧
      (api = .leakAmplified → s.mem.len = 0)
```

```lean
-- lean/PanicSafety/Forget.lean:215-217
theorem drainClients_need_inv :
    ¬ Inv dupMem ∧ CInstr.forgetGuard ∉ ([] : List CInstr) ∧
    clientRun .leakAmplified [] dupMem = .ub ∧ clientRun .destructorReliant [] dupMem = .ub := by …
```

```lean
-- lean/PanicSafety/Forget.lean:717-720
theorem drainWith_needs_inv :
    (¬ Inv dupMem ∧ ¬ ResOk (run .unwind (tableOf [.panic]) noPanicDtors drainWith dupMem)) ∧
    (¬ Inv ⟨[none], 1, [], 0, 0⟩ ∧
      run .unwind (tableOf []) noPanicDtors drainWith ⟨[none], 1, [], 0, 0⟩ = .ub) := by …
```

```lean
-- lean/PanicSafety/Forget.lean:706-710
theorem closureScopedDrain_example :
    Inv ceMem3 ∧
    run .unwind (tableOf [.ret false, .panic]) noPanicDtors drainWith ceMem3 =
      .unwound ⟨[some 2, some 1, some 2], 1, [1], 0, 0⟩ ∧
    Inv ⟨[some 2, some 1, some 2], 1, [1], 0, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Logical.lean:51-52
theorem bumpBoth_needs_inv :
    ¬ Inv dupMem ∧ ¬ ResOk (run .unwind (tableOf []) noPanicDtors bumpBoth dupMem) := by …
```

```lean
-- lean/PanicSafety/Logical.lean:41-45
theorem bumpBoth_unwind_example :
    Inv ceMem1 ∧ CountersAgree ceMem1 ∧
    run .unwind (tableOf [.panic]) noPanicDtors bumpBoth ceMem1 =
      .unwound ⟨[some 0], 1, [], 1, 0⟩ ∧
    Inv ⟨[some 0], 1, [], 1, 0⟩ ∧ ¬ CountersAgree ⟨[some 0], 1, [], 1, 0⟩ := by …
```

```lean
-- lean/PanicSafety/Facts.lean:40-41
theorem dropCells_noPanic_ne_ub_iff (cs : List Cell) (d : List Tok) :
    dropCells noPanicDtors cs d ≠ .ub ↔ OwnsUniquely d cs := by …
```

```lean
-- lean/PanicSafety/Facts.lean:98
theorem dropSafe_nil_iff_inv (m : Mem) : DropSafe [] m ↔ Inv m := by …
```

```lean
-- lean/PanicSafety/Facts.lean:129-131
theorem exec_sites_mode_indep (cb : Callback) (dt : DtorTable) (p : Prog) (j : Nat)
    (es : List Entry) (m : Mem) :
    (exec .abort cb dt p j es m).2 = (exec .unwind cb dt p j es m).2 := by …
```

```lean
-- lean/PanicSafety/Facts.lean:80-82
theorem inv_pop (m : Mem) (k : Nat) (hm : Inv m) (hl : m.len = k + 1) :
    ∃ t, m.buf[k]? = some (some t) ∧ t ∉ m.dropped ∧
      Inv { m with len := k, dropped := t :: m.dropped } := by …
```

```lean
-- lean/PanicSafety/Facts.lean:16-17
theorem ownsUniquely_cons_some_iff (d : List Tok) (t : Tok) (cs : List Cell) :
    OwnsUniquely d (some t :: cs) ↔ t ∉ d ∧ OwnsUniquely (t :: d) cs := by …
```

```lean
-- lean/PanicSafety/Facts.lean:65-66
theorem ownsUniquely_append_singleton_iff (d : List Tok) (a : List Cell) (c : Cell) :
    OwnsUniquely d (a ++ [c]) ↔ OwnsUniquely d (c :: a) := by …
```

```lean
-- lean/PanicSafety/Facts.lean:11
theorem toks_cons_some (t : Tok) (cs : List Cell) : toks (some t :: cs) = t :: toks cs := …
```

```lean
-- lean/PanicSafety/Facts.lean:13
theorem toks_append (a b : List Cell) : toks (a ++ b) = toks a ++ toks b := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:754-757
def RawUnwoundIff (cb : Callback) (dt : DtorTable) (m : Mem) : Prop :=
  match run .unwind cb dt rawRetain m with
  | .unwound m' => (Inv m' ↔ (specRetain cb dt (toks m.elems)).rejected = [])
  | _ => True
```

```lean
-- lean/PanicSafety/Logical.lean:95-98
theorem characterization_bounded_samples_nontrivial :
    BoundedPanicSafe .abort rawRetain ∧ ¬ BoundedCallSitesDropSafe rawRetain ∧
    ¬ BoundedPanicSafe .abort badSetLen ∧ BoundedCallSitesDropSafe badSetLen ∧
    BoundedPanicSafe .unwind guardRetain ∧ BoundedCallSitesDropSafe guardRetain := by …
```

```lean
-- lean/PanicSafety/Characterization.lean:82-86
theorem exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe (cb : Callback) (dt : DtorTable) :
    ∀ (p : Prog) (j : Nat) (es : List Entry) (m : Mem),
      ResOk (exec .abort cb dt p j es m).1 →
      (∀ s ∈ (exec .unwind cb dt p j es m).2, DropSafe s.entries s.mem) →
      ResOk (exec .unwind cb dt p j es m).1
```

```lean
-- lean/PanicSafety/Characterization.lean:208-211
theorem exec_abort_resOk_of_unwind_resOk (cb : Callback) (dt : DtorTable) :
    ∀ (p : Prog) (j : Nat) (es : List Entry) (m : Mem),
      ResOk (exec .unwind cb dt p j es m).1 →
      ResOk (exec .abort cb dt p j es m).1
```

```lean
-- lean/PanicSafety/Characterization.lean:320-326
theorem exec_callback_site_surgery (cb : Callback) (dt : DtorTable) :
    ∀ (p : Prog) (j : Nat) (es : List Entry) (m : Mem) (s : Site),
      s ∈ (exec .unwind cb dt p j es m).2 →
      s.kind = .callback →
      ∃ k ≥ j,
        (exec .unwind (fun i => if i = k then .panic else cb i) noPanicDtors p j es m).1 =
          panicFrom .unwind noPanicDtors s.entries s.mem
```

```lean
-- lean/PanicSafety/Characterization.lean:463-469
theorem exec_destructor_site_surgery (cb : Callback) (dt : DtorTable) :
    ∀ (p : Prog) (j : Nat) (es : List Entry) (m : Mem) (s : Site),
      s ∈ (exec .unwind cb dt p j es m).2 →
      s.kind = .destructor →
      ∃ t, t ∉ m.dropped ∧ t ∈ s.mem.dropped ∧
        (exec .unwind cb (fun u => decide (u = t)) p j es m).1 =
          panicFrom .unwind (fun u => decide (u = t)) s.entries s.mem
```

```lean
-- lean/PanicSafety/Characterization.lean:608-609
theorem dropSafe_of_resOk_panicFrom_noPanic (es : List Entry) (m : Mem)
    (h : ResOk (panicFrom .unwind noPanicDtors es m)) : DropSafe es m := by …
```

```lean
-- lean/PanicSafety/Characterization.lean:75-76
theorem resOk_panicFrom_of_dropSafe (dt : DtorTable) (es : List Entry) (m : Mem)
    (hds : DropSafe es m) : ResOk (panicFrom .unwind dt es m) := by …
```

```lean
-- lean/PanicSafety/Characterization.lean:35-38
theorem unwindEntries_ok_noPanic_imp_ok_or_abort (dt : DtorTable) :
    ∀ (es : List Entry) (m m' : Mem),
      unwindEntries noPanicDtors es m = .ok m' →
      unwindEntries dt es m = .ok m' ∨ unwindEntries dt es m = .abort
```

```lean
-- lean/PanicSafety/Characterization.lean:54-57
theorem unwindEntries_eq_noPanic_of_panickers_dropped (dt : DtorTable) :
    ∀ (es : List Entry) (m : Mem),
      (∀ u, dt u = true → u ∈ m.dropped) →
      unwindEntries dt es m = unwindEntries noPanicDtors es m
```

```lean
-- lean/PanicSafety/Characterization.lean:667-670
theorem exec_sites_subset_noPanicDtors (cb : Callback) (dt : DtorTable) :
    ∀ (p : Prog) (j : Nat) (es : List Entry) (m : Mem) (s : Site),
      s ∈ (exec .unwind cb dt p j es m).2 →
      s ∈ (exec .unwind cb noPanicDtors p j es m).2
```

```lean
-- lean/PanicSafety/Characterization.lean:826
theorem truncateLate_panicSafe_abort : PanicSafe .abort truncateLate := by …
```

```lean
-- lean/PanicSafety/Characterization.lean:853
theorem truncateLate_callbackSitesDropSafe : CallbackSitesDropSafe truncateLate := by …
```

```lean
-- lean/PanicSafety/RetainResults.lean:961-964
def GuardUnwoundLeakFree (cb : Callback) (dt : DtorTable) (m : Mem) : Prop :=
  match run .unwind cb dt guardRetain m with
  | .unwound m' => LeakFree m m'
  | _ => True
```

```lean
-- lean/PanicSafety/Forget.lean:483-485
theorem cl_crun_ne_ub (api : DrainApi) (is : List CInstr) (s : CState)
    (hs : DrainClientInv api s) (hf : api = .destructorReliant → CInstr.forgetGuard ∉ is) :
    crun api is s ≠ .ub := by …
```

```lean
-- lean/PanicSafety/Forget.lean:499-500
theorem cl_clientInv_init (api : DrainApi) (m : Mem) (hm : Inv m) :
    DrainClientInv api ⟨m, [], none⟩ := by …
```

```lean
-- lean/PanicSafety/Forget.lean:647-651
theorem dw_loop (cb : Callback) (dt : DtorTable) (m : Mem) (hm : Inv m) :
    ∀ (r c j : Nat) (m' : Mem) (D : List Tok), c + r = m.len → m'.buf = m.buf →
      m'.len = m.len → m'.dropped = D ++ m.dropped →
      (∀ t ∈ D, t ∈ toks (m.buf.take c)) →
      ResOk (exec .unwind cb dt (drainWithLoop m.len r c) j [.guard (tailFix c m.len)] m').1 := by …
```

```lean
-- lean/PanicSafety/Forget.lean:608-611
theorem dw_inv_fix (m : Mem) (hm : Inv m) (c : Nat) (hc : c ≤ m.len) (D : List Tok)
    (hD : ∀ t ∈ D, t ∈ toks (m.buf.take c)) (x : Mem)
    (hbuf : x.buf = copyRange (m.len - c) m.buf c 0) (hlen : x.len = m.len - c)
    (hdrop : x.dropped = D ++ m.dropped) : Inv x := by …
```

```lean
-- lean/PanicSafety/Forget.lean:555-557
theorem dw_copyRange_getElem?_shift (k : Nat) (b : List Cell) (s d : Nat) (hds : d ≤ s)
    (hk : s + k ≤ b.length) (i : Nat) (hi : i < k) :
    (copyRange k b s d)[d + i]? = b[s + i]? := by …
```

### Primary sources

All sources were inspected on 2026-11-21; Git revisions were resolved through the GitHub API on that date. Basis: documentation and normative sources, used for the `derived (modeling bridge)` claims and for prior art; none of them is evidence for a kernel-checked statement.

1. The Rustonomicon, `rust-lang/nomicon` commit `b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6`: `src/exception-safety.md` L20-22, L25; `src/leaking.md` L31-33, L36-37, L98-100, L104-105.
2. The Rust Reference, `rust-lang/reference` commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`: `src/behavior-not-considered-unsafe.md` L6 ("Leaks of memory and other resources"), L7 ("Exiting without calling destructors"), L24-26 ("Logic errors"); `src/behavior-considered-undefined.md` L56 (unwinding past a frame that does not allow unwinding) and L67 (stack frames deallocated without running destructors, `longjmp`). `src/panic.md` and `src/destructors.md` at this commit contain no rule that a destructor panic during unwinding aborts.
3. RFCs, `rust-lang/rfcs` commit `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`: `text/1066-safe-mem-forget.md` L9-10; `text/1236-stabilize-catch-panic.md` L135-138; `text/1513-less-unwinding.md` L9 and L143-144; `text/3151-scoped-threads.md` L32-33. RFC 2349 (`text/2349-pin.md`) is not cited for the `Pin` drop guarantee: there (L399-403, under "Unresolved questions") the sentence about destructors always running is a possible future strengthening; the std 1.85.0 `std::pin` "Drop guarantee" section is cited instead.
4. Rust 1.85.0, `rust-lang/rust` tag `1.85.0` = commit `4d91de4e48198da2e33413efdcd9cd2cc0c46688`: `library/alloc/src/vec/mod.rs` (`Vec::truncate` comment L1528-1530; `retain_mut` L2121-2218, with the `set_len(0)` comment L2132-2134, `BackshiftOnDrop` L2147-2171, the comment at L2186, and the counter updates and `ptr::drop_in_place` at L2187-2190); `library/core/src/mem/mod.rs` (`mem::forget` documentation, L41-44, with the sentence quoted under R13 at L43-44, and L52-53).
5. Rust std 1.85.0 rendered documentation (https://doc.rust-lang.org/1.85.0/std/), generated from the commit in item 4: `std::panic::UnwindSafe`, `std::panic::catch_unwind`, `std::thread::scope`, `std::mem::forget`, `std::ops::Drop`, `std::pin` (section "Drop guarantee"). Quotes from these pages are cited by URL.
6. Y. Bae, Y. Kim, A. Askar, J. Lim, T. Kim, "Rudra: Finding Memory Safety Bugs in Rust at the Ecosystem Scale", SOSP 2021, pp. 84-99, doi:10.1145/3477132.3483570 (§3.1, Definition 3.1).
7. R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, "RustBelt: Securing the Foundations of the Rust Programming Language", PACMPL 2(POPL), article 66, 2018, doi:10.1145/3158154 (§9).
8. L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer, "RefinedRust: A Type System for High-Assurance Verification of Rust Programs", PACMPL 8(PLDI), 2024, doi:10.1145/3656422.
9. S. Ho, J. Protzenko, "Aeneas: Rust Verification by Functional Translation", PACMPL 6(ICFP), 2022, doi:10.1145/3547647, arXiv:2206.07185.
10. MiniRust, `minirust/minirust` commit `063d784186d3252bee242217f218223205c0b568`, `spec/lang/step/terminators.md`.
11. D. Abrahams, "Exception-Safety in Generic Components", Generic Programming, LNCS 1766, Springer 2000, pp. 69-79, doi:10.1007/3-540-39953-4_6 (full text not inspected); the guarantee wording is quoted from the version hosted by Boost, `boostorg/website` commit `5946dc4e147a8a7738ac5f2be7c84c4c4762112e`, `community/exception_safety.html` L224-225 (identity with the LNCS wording not verified).
12. J. A. Tov, R. Pucella, "Practical affine types", POPL 2011, pp. 447-458, doi:10.1145/1926385.1926436 (bibliographic metadata verified; full text not inspected).
13. Web pages without an immutable identity (no revision or checksum was recorded): "Pre-Pooping Your Pants With Rust" (dated April 27, 2015), https://faultlore.com/blah/everyone-poops/; "The Pain Of Real Linear Types in Rust" (dated May 8, 2017), https://faultlore.com/blah/linear-rust/; "The Scoped Task trilemma" (dated April 8, 2023), https://without.boats/blog/the-scoped-task-trilemma/. They are cited as prior art and are not listed as subjects.
14. Public advisories and issues, cited by URL for context and described no further here: CVE-2020-36317 (https://nvd.nist.gov/vuln/detail/CVE-2020-36317; https://github.com/rust-lang/rust/issues/78498; https://github.com/rust-lang/rust/pull/78499); CVE-2021-31162 (https://nvd.nist.gov/vuln/detail/CVE-2021-31162; https://github.com/rust-lang/rust/issues/83618; https://github.com/rust-lang/rust/pull/83629); https://github.com/rust-lang/rust/issues/24292.

Novelty: none claimed (tiers T0 and T1). A web search on 2026-11-21 for a mechanized model relating call-site invariants, leak amplification and safe `forget` found none. RustBelt states that it does not model stack unwinding (item 7, §9); the RefinedRust paper treats a panic as aborting execution and the Aeneas paper treats it as an "unrecoverable error", and the text of neither paper mentions unwinding (items 8-9); MiniRust models unwinding operationally (item 10). The search was not exhaustive.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, rejects `sorry`, `admit`, `native_decide` and `axiom` in the Lean sources, computes `collectAxioms` for every declaration of the library (allowed: `propext`, `Classical.choice`, `Quot.sound`), and recomputes, for every Lean name referenced by `results.json` and every name recorded in `audit/statements.json`, the SHA-256 of the statement (`repr` of its type) and of its definition closure (types and values of every package constant reachable from the statement; theorem bodies excluded), comparing them with `audit/statements.json`. The script's header documents exactly what is hashed. Exit status 0 iff every check passes.

A narrower manual check of the main results (in a fresh copy of the package, `lake build` re-checks every proof):

```sh
cd lean
lake build
cat > /tmp/PanicSafetyAxioms.lean <<'EOF'
import PanicSafety
#print axioms Toy.PanicSafety.inv_iff_containerDrop_noPanic_ne_ub
#print axioms Toy.PanicSafety.unwindEntries_noPanic_ok_inv_iff_dropSafe
#print axioms Toy.PanicSafety.rawRetain_unwind_doubleDrop
#print axioms Toy.PanicSafety.rawRetain_abort_exact
#print axioms Toy.PanicSafety.rawRetain_unwound_inv_iff_rejected_nil
#print axioms Toy.PanicSafety.panicSafe_unwind_iff_abort_and_callSitesDropSafe
#print axioms Toy.PanicSafety.truncateLate_counterexample
#print axioms Toy.PanicSafety.truncateLate_sites_destructor
#print axioms Toy.PanicSafety.truncateLate_dtorPanic_unwound
#print axioms Toy.PanicSafety.leakRetain_unwind_exact
#print axioms Toy.PanicSafety.leakRetain_unwound_leaks
#print axioms Toy.PanicSafety.guardRetain_unwind_exact
#print axioms Toy.PanicSafety.guardRetain_unwound_leakFree
#print axioms Toy.PanicSafety.guardRetain_unwound_leakFree_noInv
#print axioms Toy.PanicSafety.guardRetainLate_panicSafe_unwind_of_noPanickingDtors
#print axioms Toy.PanicSafety.destructorReliantDrain_forget_reachesUB
#print axioms Toy.PanicSafety.leakAmplifiedDrain_noUB
#print axioms Toy.PanicSafety.leakAmplifiedDrain_forgetGuard_leaks
#print axioms Toy.PanicSafety.destructorReliantDrain_noUB_withoutForgetGuard
#print axioms Toy.PanicSafety.closureScopedDrain_panicSafe_unwind
#print axioms Toy.PanicSafety.panicSafe_unwind_but_countersAgree_broken
EOF
lake env lean /tmp/PanicSafetyAxioms.lean
```

Each `#print axioms` line must list at most `propext`, `Classical.choice` and `Quot.sound` (or report no axioms). To check whether the findings still hold after a change to the model, rerun both commands: a change to any definition in a statement's closure changes its closure hash, and `support/revalidate.py` then names the affected statements. The kernel checks establish the statements about the toy model; they do not revalidate any `derived (modeling bridge)` claim, which must be rechecked against the cited sources (pinned under **Evidence**) if those sources change.
