import ToyViews.Laws

/-!
# Named concrete states used by the examples, counterexamples and witnesses

Notation in comments: `A`, `B`, `C` are the views with ids `0`, `1`, `2`; every state has a single
address `0` unless stated otherwise.
-/

namespace Toy.Views
namespace Ex

/-- `s0`: one active exclusive root `A` that owns address `0` (byte `0`), writable. -/
def s0 : State := ⟨[{ parent := none, mode := .excl, active := true, cells := [some (.own 0 0)] }]⟩

/-- `s1`: `A` has lent address `0` exclusively to its child `B`. -/
def s1 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.own 0 0)] }]⟩

/-- `s2`: nested exclusive reborrow — `A` lent `0` to `B`, which lent it on to its child `C`. -/
def s2 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.loaned 2)] },
  { parent := some 1, mode := .excl, active := true, cells := [some (.own 0 0)] }]⟩

/-- `s3 b`: the result of ending `B` in `s2` by the naive rule, with `A`'s cell restored to byte
`b`: `A` is writable again while `C` is still active and writable. -/
def s3 (b : Byte) : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 0 b)] },
  { parent := some 0, mode := .excl, active := false, cells := [some (.loaned 2)] },
  { parent := some 1, mode := .excl, active := true, cells := [some (.own 0 0)] }]⟩

/-- `s1e b`: ending `B` in `s1` (no nested reborrow), `A` restored to byte `b`. -/
def s1e (b : Byte) : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 0 b)] },
  { parent := some 0, mode := .excl, active := false, cells := [some (.own 0 0)] }]⟩

/-- `s2e b`: ending the innermost view `C` in `s2`, `B` restored to byte `b`. -/
def s2e (b : Byte) : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.own 0 b)] },
  { parent := some 1, mode := .excl, active := false, cells := [some (.own 0 0)] }]⟩

/-- `t1`: `A` has lent address `0` to a shared child `B` (`A` at depth `1`, `B` at baseline `1`). -/
def t1 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] }]⟩

/-- `t2`: nested shared reborrow — `B` has itself lent `0` to a shared child `C` (`B` at depth
`2`). -/
def t2 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 2 0)] },
  { parent := some 1, mode := .shared, active := true, cells := [some (.own 1 0)] }]⟩

/-- `t3`: ending `B` in `t2` by the naive rule: `A` back at depth `0` (writable) while `C` still
reads. -/
def t3 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := some 0, mode := .shared, active := false, cells := [some (.own 2 0)] },
  { parent := some 1, mode := .shared, active := true, cells := [some (.own 1 0)] }]⟩

/-- `t1e`: ending `B` in `t1` (no nested reborrow). -/
def t1e : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := some 0, mode := .shared, active := false, cells := [some (.own 1 0)] }]⟩

/-- `u2`: `A` has two shared children `B` and `C` (`A` at depth `2`). -/
def u2 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 2 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] }]⟩

/-- `u2e`: ending `B` in `u2`: `A` drops to depth `1` and stays read-only because `C` still
reads. -/
def u2e : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := false, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] }]⟩

/-- `w2`: two addresses; `A` owns `0` and `1`, has lent `0` exclusively to `B` and `1` to a shared
child `C`. -/
def w2 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1), some (.own 1 7)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.own 0 5), none] },
  { parent := some 0, mode := .shared, active := true, cells := [none, some (.own 1 7)] }]⟩

/-- `weExclChildLoaned`: an active exclusive child `B` whose parent `A` still holds the cell as
`own 0 0` instead of `loaned 1` (violates `ExclChildLoaned`; `A` and `B` both write). -/
def weExclChildLoaned : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.own 0 0)] }]⟩

/-- `t2flat`: like `t2`, but the shared view `B` holds address `0` at its own baseline depth `1`
although its shared child `C` is active (violates `DepthCounts` at `B`). -/
def t2flat : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] },
  { parent := some 1, mode := .shared, active := true, cells := [some (.own 1 0)] }]⟩

/-- `aS0`: `A` lent `0` to `B`, `B` lent it to `C`, and `C` is retired while `B` still records the
loan to `C` (`B` holds `loaned 2`). Not reachable from `s0` by the operations of this model. -/
def aS0 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.loaned 2)] },
  { parent := some 1, mode := .excl, active := false, cells := [some (.own 0 0)] }]⟩

end Ex
end Toy.Views
