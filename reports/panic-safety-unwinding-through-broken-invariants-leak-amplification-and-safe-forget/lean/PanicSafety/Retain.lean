import PanicSafety.Bounded

/-!
# Retain-like operations: raw moves, leak amplification, drop guards

Four implementations of a toy `retain` over the container's first `len` cells. The `j`-th
callback invocation decides whether element `j` is kept (`true`) or removed (`false`);
removed elements are dropped in place and kept elements are moved down over the holes.

* `rawRetain`: moves elements with a bitwise copy and updates `len` only at the end.
* `leakRetain`: the same loop, preceded by `set_len(0)` ("leak amplification").
* `guardRetain`: a back-shift drop guard whose fields are updated *before* each removed
  element's destructor runs.
* `guardRetainLate`: the same guard, with the fields updated *after* the destructor runs.
-/

namespace Toy.PanicSafety

/-- The raw loop. `n` is the initial `len`; `i` the next index; `del` the number removed. -/
def rawLoop (n : Nat) : Nat → Nat → Nat → Prog
  | 0, _, del => .setLen (n - del) .done
  | r + 1, i, del => .call fun keep =>
      if keep then
        (if 0 < del then .copy i (i - del) (rawLoop n r (i + 1) del) else rawLoop n r (i + 1) del)
      else .dropCell i (rawLoop n r (i + 1) (del + 1))

/-- Retain with raw moves and `len` updated only at the end. -/
def rawRetain : Prog := .getLen fun n => rawLoop n n 0 0

/-- Retain with leak amplification: `set_len(0)` before the loop, `len` restored at the end. -/
def leakRetain : Prog := .getLen fun n => .setLen 0 (rawLoop n n 0 0)

/-- `copyRange count b src dst`: copy `count` cells from `src..` to `dst..`, front to back
(a correct `memmove` when `dst ≤ src`). Out-of-range writes are ignored. -/
def copyRange : Nat → List Cell → Nat → Nat → List Cell
  | 0, b, _, _ => b
  | c + 1, b, s, d => copyRange c (b.set d (b.getD s none)) (s + 1) (d + 1)

/-- A back-shift guard with fields `processed = p`, `deleted = d`, `original_len = n`: on
drop it moves the unprocessed cells `[p, n)` down by `d` and sets `len := n - d`
(truncated subtraction; the loops keep `d ≤ p ≤ n`). -/
def backshift (p d n : Nat) : Guard := ⟨fun b _ => (copyRange (n - p) b p (p - d), n - d)⟩

/-- Guarded loop, guard fields updated before a removed element's destructor runs. -/
def guardLoop (n : Nat) : Nat → Nat → Nat → Prog
  | 0, _, _ => .popGuard .done
  | r + 1, p, d => .call fun keep =>
      if keep then
        (if 0 < d then .copy p (p - d) (.setGuard (backshift (p + 1) d n) (guardLoop n r (p + 1) d))
         else .setGuard (backshift (p + 1) d n) (guardLoop n r (p + 1) d))
      else .setGuard (backshift (p + 1) (d + 1) n) (.dropCell p (guardLoop n r (p + 1) (d + 1)))

/-- Retain with a back-shift drop guard (fields updated before each destructor). -/
def guardRetain : Prog := .getLen fun n => .pushGuard (backshift 0 0 n) (guardLoop n n 0 0)

/-- Guarded loop, guard fields updated after a removed element's destructor returns. -/
def guardLoopLate (n : Nat) : Nat → Nat → Nat → Prog
  | 0, _, _ => .popGuard .done
  | r + 1, p, d => .call fun keep =>
      if keep then
        (if 0 < d then .copy p (p - d) (.setGuard (backshift (p + 1) d n) (guardLoopLate n r (p + 1) d))
         else .setGuard (backshift (p + 1) d n) (guardLoopLate n r (p + 1) d))
      else .dropCell p (.setGuard (backshift (p + 1) (d + 1) n) (guardLoopLate n r (p + 1) (d + 1)))

/-- Retain with a back-shift drop guard whose fields are updated after each destructor. -/
def guardRetainLate : Prog :=
  .getLen fun n => .pushGuard (backshift 0 0 n) (guardLoopLate n n 0 0)

/-! ## Abstract specification -/

/-- How an abstract retain run ended. -/
inductive Ending where
  | finished
  | callbackPanic
  | dtorPanic
deriving DecidableEq, Repr

/-- Result of the abstract retain: elements kept (in order), elements removed (most recent
first, i.e. in drop-log order), elements not yet processed, and how the run ended. -/
structure AbsOut where
  kept : List Tok
  rejected : List Tok
  rest : List Tok
  ending : Ending
deriving DecidableEq, Repr

/-- Abstract retain over a list of values, with `j` callback invocations so far. A removed
element whose destructor panics counts as removed (its destructor ran) and ends the run. -/
def absRetain (cb : Callback) (dt : DtorTable) : List Tok → Nat → List Tok → List Tok → AbsOut
  | [], _, kept, rej => ⟨kept, rej, [], .finished⟩
  | x :: xs, j, kept, rej =>
    match cb j with
    | .panic => ⟨kept, rej, x :: xs, .callbackPanic⟩
    | .ret true => absRetain cb dt xs (j + 1) (kept ++ [x]) rej
    | .ret false =>
      if dt x then ⟨kept, x :: rej, xs, .dtorPanic⟩
      else absRetain cb dt xs (j + 1) kept (x :: rej)

/-- The abstract retain from the start. -/
def specRetain (cb : Callback) (dt : DtorTable) (xs : List Tok) : AbsOut :=
  absRetain cb dt xs 0 [] []

end Toy.PanicSafety
