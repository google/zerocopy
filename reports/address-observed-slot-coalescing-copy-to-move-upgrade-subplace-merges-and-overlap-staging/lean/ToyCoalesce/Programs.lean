import ToyCoalesce.VC
import ToyCoalesce.Tactics
import ToyCoalesce.PfCompose

/-!
# Concrete programs used by the counterexamples, positive controls and non-vacuity theorems

Locals are numbered from `0`; `⟨b, o, l⟩` is the place of width `l` at offset `o` of local `b`.
-/

namespace Toy.Coalesce

/-- A fixed layout: local `x` at address `10 * x + 10`. -/
def A0 : Layout := fun x => 10 * x + 10

/-! ## Upgrades -/

/-- Destructor load: `x` (local 0) := 7; `p` (local 1) := &x; `y` (local 2) := copy x (the
upgrade site, body index 5); out y; the destructor block loads through `p`. -/
def pDtor : Prog where
  sizes := [1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .storageLive 2,
    .assign ⟨0, 0, 1⟩ [.lit 7], .assign ⟨1, 0, 1⟩ [.addrOf ⟨0, 0, 1⟩],
    .assign ⟨2, 0, 1⟩ [.copy ⟨0, 0, 1⟩], .out (.copy ⟨2, 0, 1⟩)]
  dtors := [.out (.load ⟨1, 0, 1⟩ 1)]
  fns := []

/-- The same program without the destructor block (positive control). -/
def pNoDtor : Prog := { pDtor with dtors := [] }

/-- A caller with `x` (local 0) := 1, an escaped pointer `g` (local 1) := &x, and the call
`call 0 (copy x)` at body index 4 to a callee with parameter local 2 and body `cb`; `tail` runs
after the call. -/
def pCall (cb tail : List Stmt) : Prog where
  sizes := [1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1],
    .assign ⟨1, 0, 1⟩ [.addrOf ⟨0, 0, 1⟩], .call 0 (.copy ⟨0, 0, 1⟩)] ++ tail
  dtors := []
  fns := [⟨2, cb⟩]

/-- `pCall` with the call argument upgraded to `move x`. -/
def pCallMv (cb tail : List Stmt) : Prog where
  sizes := [1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1],
    .assign ⟨1, 0, 1⟩ [.addrOf ⟨0, 0, 1⟩], .call 0 (.move ⟨0, 0, 1⟩)] ++ tail
  dtors := []
  fns := [⟨2, cb⟩]

theorem pCall_upgradeAt (cb tail : List Stmt) : (pCall cb tail).upgradeAt 4 = pCallMv cb tail := by
  simp [pCall, pCallMv, Prog.upgradeAt, modifyAt, Stmt.upgradeCopy]

/-- The callee writes its parameter, then loads through the escaped pointer to `x`. -/
def pIPLoad : Prog := pCall [.assign ⟨2, 0, 1⟩ [.lit 2], .out (.load ⟨1, 0, 1⟩ 1)] []

/-- The callee stores through the escaped pointer to `x`, then reads its parameter. -/
def pIPStore : Prog := pCall [.store ⟨1, 0, 1⟩ (.lit 2), .out (.copy ⟨2, 0, 1⟩)] []

/-- The callee compares the address of its parameter with the escaped pointer to `x`. -/
def pIPAddr : Prog := pCall [.ptrEq (.addrOf ⟨2, 0, 1⟩) (.copy ⟨1, 0, 1⟩)] []

/-- The callee writes its parameter; the caller reads `x` after the call. -/
def pIPAfter : Prog := pCall [.assign ⟨2, 0, 1⟩ [.lit 2]] [.out (.copy ⟨0, 0, 1⟩)]

/-- The callee reads its parameter and does nothing else (non-vacuity of the in-place conditions). -/
def pIPOk : Prog := pCall [.out (.copy ⟨2, 0, 1⟩)] []

/-- `x` (local 0) := 1; `y` (local 1) := copy x (body index 3); out x. -/
def pReuse : Prog where
  sizes := [1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1],
    .assign ⟨1, 0, 1⟩ [.copy ⟨0, 0, 1⟩], .out (.copy ⟨0, 0, 1⟩)]
  dtors := []
  fns := []

/-- `pDtor` with the upgrade at body index 5. -/
def pDtorMv : Prog := { pDtor with body := [.storageLive 0, .storageLive 1, .storageLive 2,
    .assign ⟨0, 0, 1⟩ [.lit 7], .assign ⟨1, 0, 1⟩ [.addrOf ⟨0, 0, 1⟩],
    .assign ⟨2, 0, 1⟩ [.move ⟨0, 0, 1⟩], .out (.copy ⟨2, 0, 1⟩)] }

theorem pDtor_upgradeAt : pDtor.upgradeAt 5 = pDtorMv := by
  simp [pDtor, pDtorMv, Prog.upgradeAt, modifyAt, Stmt.upgradeCopy]

theorem pNoDtor_upgradeAt : pNoDtor.upgradeAt 5 = { pDtorMv with dtors := [] } := by
  simp [pNoDtor, pDtor, pDtorMv, Prog.upgradeAt, modifyAt, Stmt.upgradeCopy]

/-- `pReuse` with the upgrade at body index 3. -/
def pReuseMv : Prog := { pReuse with body := [.storageLive 0, .storageLive 1,
    .assign ⟨0, 0, 1⟩ [.lit 1], .assign ⟨1, 0, 1⟩ [.move ⟨0, 0, 1⟩], .out (.copy ⟨0, 0, 1⟩)] }

theorem pReuse_upgradeAt : pReuse.upgradeAt 3 = pReuseMv := by
  simp [pReuse, pReuseMv, Prog.upgradeAt, modifyAt, Stmt.upgradeCopy]

/-- The place `x`. -/
def qx : Place := ⟨0, 0, 1⟩

end Toy.Coalesce

namespace Toy.Coalesce

/-! ## Coalescing -/

/-- `x` (local 0, one cell) and `y` (local 1, two cells): `y.1 := 5`, `x := 7`, out x,
`y.0 := 9`, then `ptrInRange(&x, &y, 2)`, out y. Merge `x ↦ y.0`. -/
def p3 : Prog where
  sizes := [1, 2]
  body := [.storageLive 0, .storageLive 1, .assign ⟨1, 1, 1⟩ [.lit 5], .assign ⟨0, 0, 1⟩ [.lit 7],
    .out (.copy ⟨0, 0, 1⟩), .assign ⟨1, 0, 1⟩ [.lit 9],
    .ptrInRange (.addrOf ⟨0, 0, 1⟩) (.addrOf ⟨1, 0, 2⟩) 2, .out (.copy ⟨1, 0, 2⟩)]
  dtors := []
  fns := []

/-- As `p3`, but the address of `x` is printed instead of compared; `y` is never address-taken. -/
def p3x : Prog where
  sizes := [1, 2]
  body := [.storageLive 0, .storageLive 1, .assign ⟨1, 1, 1⟩ [.lit 5], .assign ⟨0, 0, 1⟩ [.lit 7],
    .out (.copy ⟨0, 0, 1⟩), .assign ⟨1, 0, 1⟩ [.lit 9], .out (.addrOf ⟨0, 0, 1⟩),
    .out (.copy ⟨1, 0, 2⟩)]
  dtors := []
  fns := []

/-- No address observation; `y.0` is written while `x` still holds a value that is read later. -/
def pClobber : Prog where
  sizes := [1, 2]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 7], .assign ⟨1, 0, 1⟩ [.lit 9],
    .assign ⟨1, 1, 1⟩ [.lit 5], .out (.copy ⟨0, 0, 1⟩), .out (.copy ⟨1, 0, 2⟩)]
  dtors := []
  fns := []

/-- Transitive merges `x ↦ y.1` and `y ↦ z.1` (so `x ↦ z.2`): `x` (local 0, one cell) and `z`
(local 2, three cells) are allocated together and `ptrInRange(&x, &z, 3)` is observed; `y`
(local 1, two cells) lives later, after both are deallocated. -/
def pChain : Prog where
  sizes := [1, 2, 3]
  body := [.storageLive 0, .storageLive 2, .assign ⟨0, 0, 1⟩ [.lit 4], .out (.copy ⟨0, 0, 1⟩),
    .assign ⟨2, 0, 3⟩ [.lit 1, .lit 2, .lit 3],
    .ptrInRange (.addrOf ⟨0, 0, 1⟩) (.addrOf ⟨2, 0, 3⟩) 3, .out (.copy ⟨2, 0, 3⟩),
    .storageDead 0, .storageDead 2, .storageLive 1, .assign ⟨1, 0, 2⟩ [.lit 5, .lit 6],
    .out (.copy ⟨1, 0, 2⟩), .out (.addrOf ⟨1, 0, 2⟩), .storageDead 1]
  dtors := []
  fns := []

/-- The forest `x ↦ y.1`, `y ↦ z.1`. -/
def μChain : Forest := [⟨0, 1, 1⟩, ⟨1, 2, 1⟩]

/-- `pChain` without the range comparison (no address of `x` is observed). -/
def pChainOk : Prog where
  sizes := [1, 2, 3]
  body := [.storageLive 0, .storageLive 2, .assign ⟨0, 0, 1⟩ [.lit 4], .out (.copy ⟨0, 0, 1⟩),
    .assign ⟨2, 0, 3⟩ [.lit 1, .lit 2, .lit 3], .out (.copy ⟨2, 0, 3⟩),
    .storageDead 0, .storageDead 2, .storageLive 1, .assign ⟨1, 0, 2⟩ [.lit 5, .lit 6],
    .out (.copy ⟨1, 0, 2⟩), .out (.addrOf ⟨1, 0, 2⟩), .storageDead 1]
  dtors := []
  fns := []

/-- Sibling merges `x1 ↦ y.0` and `x2 ↦ y.0`: `x1` (local 0) and `x2` (local 1) are allocated
together, hold values at different times, and `ptrEq(&x1, &x2)` is observed; `y` (local 2)
lives later. -/
def pSib : Prog where
  sizes := [1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1], .out (.copy ⟨0, 0, 1⟩),
    .assign ⟨1, 0, 1⟩ [.lit 2], .out (.copy ⟨1, 0, 1⟩),
    .ptrEq (.addrOf ⟨0, 0, 1⟩) (.addrOf ⟨1, 0, 1⟩), .storageDead 0, .storageDead 1,
    .storageLive 2, .assign ⟨2, 0, 1⟩ [.lit 3], .out (.copy ⟨2, 0, 1⟩),
    .out (.addrOf ⟨2, 0, 1⟩), .storageDead 2]
  dtors := []
  fns := []

/-- The forest `x1 ↦ y.0`, `x2 ↦ y.0`. -/
def μSib : Forest := [⟨0, 2, 0⟩, ⟨1, 2, 0⟩]

/-- `x` (local 0) and `y` (local 1) are allocated together and both address-taken; their
values are live at disjoint times (precisely disjoint, lexically overlapping); `ptrEq(&x, &y)` is
observed. Merge `y ↦ x.0`. -/
def pPrecise : Prog where
  sizes := [1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1], .out (.copy ⟨0, 0, 1⟩),
    .assign ⟨1, 0, 1⟩ [.lit 2], .out (.copy ⟨1, 0, 1⟩),
    .ptrEq (.addrOf ⟨0, 0, 1⟩) (.addrOf ⟨1, 0, 1⟩), .storageDead 0, .storageDead 1]
  dtors := []
  fns := []

/-- `pPrecise` without the comparison (no address observation). -/
def pPreciseOk : Prog where
  sizes := [1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1], .out (.copy ⟨0, 0, 1⟩),
    .assign ⟨1, 0, 1⟩ [.lit 2], .out (.copy ⟨1, 0, 1⟩), .storageDead 0, .storageDead 1]
  dtors := []
  fns := []

/-- `y` (local 0, two cells) := (1, 2); `y'` (local 1, two cells) := (y.1, y.0); out y'. Merge
`y' ↦ y.0`. -/
def pSwap : Prog where
  sizes := [2, 2]
  body := [.storageLive 0, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2], .storageLive 1,
    .assign ⟨1, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩], .out (.copy ⟨1, 0, 2⟩)]
  dtors := []
  fns := []

/-- `x` (local 0) := 5; `x` deallocated; `y` (local 1) allocated and read uninitialized. Merge
`x ↦ y.0`. -/
def pUBRemoved : Prog where
  sizes := [1, 1]
  body := [.storageLive 0, .assign ⟨0, 0, 1⟩ [.lit 5], .storageDead 0, .storageLive 1,
    .out (.copy ⟨1, 0, 1⟩)]
  dtors := []
  fns := []


/-! ## Programs exercising callee parameters, absent callees and in-place aliasing -/

/-- The callee's parameter local (local 3) is a local of the caller's frame: the caller saves
`pz := &z`, allocates `x`, calls `call 0 (copy x)` (empty callee with parameter 3), deallocates
`z` and `x`, allocates local 3 and compares `pz` with `&local 3`. -/
def pPrmConflict : Prog where
  sizes := [1, 1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨1, 0, 1⟩ [.addrOf ⟨0, 0, 1⟩],
    .storageLive 2, .assign ⟨2, 0, 1⟩ [.lit 42], .call 0 (.copy ⟨2, 0, 1⟩), .storageDead 0,
    .storageDead 2, .storageLive 3, .ptrEq (.copy ⟨1, 0, 1⟩) (.addrOf ⟨3, 0, 1⟩)]
  dtors := []
  fns := [⟨3, []⟩]

/-- A layout that puts locals 0 and 3 at the same address. -/
def A_eq03 : Layout := fun
  | 0 => 100
  | 1 => 200
  | 2 => 300
  | 3 => 100
  | n => 1000 + 10 * n

/-- The caller takes `pp := &p` of the callee's parameter local `p` (local 2) before the call and
deallocates `p`; the callee prints `load pp 1`. -/
def pPrmEscaped : Prog where
  sizes := [1, 1, 1]
  body := [.storageLive 2, .storageLive 1, .assign ⟨1, 0, 1⟩ [.addrOf ⟨2, 0, 1⟩], .storageDead 2,
    .storageLive 0, .assign ⟨0, 0, 1⟩ [.lit 7], .call 0 (.copy ⟨0, 0, 1⟩)]
  dtors := []
  fns := [⟨2, [.out (.load ⟨1, 0, 1⟩ 1)]⟩]

/-- A call to an absent callee (`fns = []`), which the semantics runs as `⟨0, []⟩`. -/
def pOobCall : Prog where
  sizes := [1, 1]
  body := [.storageLive 1, .assign ⟨1, 0, 1⟩ [.lit 7], .out (.copy ⟨1, 0, 1⟩), .call 0 (.lit 9)]
  dtors := []
  fns := []

/-- The callee (parameter local 2) writes `y` (local 1) and then reads `x` (local 0); neither
`x` nor `y` is address-taken. -/
def pCalleeReorder : Prog where
  sizes := [1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 1⟩ [.lit 1], .call 0 (.lit 0),
    .out (.copy ⟨1, 0, 1⟩)]
  dtors := []
  fns := [⟨2, [.assign ⟨1, 0, 1⟩ [.lit 99], .out (.copy ⟨0, 0, 1⟩)]⟩]

/-- In-place aliasing inside a callee: `x` (local 0, two cells) is passed by `move` to a callee
with parameter local 1, which assigns `prm := (x.1, x.0)` and prints `prm`. -/
def pAliasSwap : Prog where
  sizes := [2, 2]
  body := [.storageLive 0, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2], .call 0 (.move ⟨0, 0, 2⟩)]
  dtors := []
  fns := [⟨1, [.assign ⟨1, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩], .out (.copy ⟨1, 0, 2⟩)]⟩]

/-- `x := (1, 2)` (local 0) and `call 0 (move y)` (local 1) to a callee with parameter local 2
that assigns `prm := (x.1, x.0)` and prints `prm`. Merge `x ↦ y.0`. -/
def pAliasCoalSwap : Prog where
  sizes := [2, 2, 2]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2],
    .call 0 (.move ⟨1, 0, 2⟩)]
  dtors := []
  fns := [⟨2, [.assign ⟨2, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩], .out (.copy ⟨2, 0, 2⟩)]⟩]

/-- A callee whose parameter (local 1) does not exist, an assignment that needs staging, and an
in-place call passing a width-0 place. -/
def pStageOobPrm : Prog where
  sizes := [2]
  body := [.storageLive 0, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2],
    .assign ⟨0, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩], .call 0 (.move ⟨0, 0, 0⟩)]
  dtors := []
  fns := [⟨1, []⟩]

/-- A callee assignment `y' := (y.1, y.0)` that needs no staging in the source (callee parameter
local 2). Merge `y' ↦ y.0`. -/
def pCalleeCoalSwap : Prog where
  sizes := [2, 2, 1]
  body := [.storageLive 0, .storageLive 1, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2], .call 0 (.lit 0),
    .out (.copy ⟨1, 0, 2⟩)]
  dtors := []
  fns := [⟨2, [.assign ⟨1, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩]]⟩]

/-- A two-cell local (local 1) and a one-cell local (local 0) that the two-cell one does not fit
into. -/
def pSmallParent : Prog where
  sizes := [1, 2]
  body := [.storageLive 1, .assign ⟨1, 0, 2⟩ [.lit 1, .lit 2], .out (.copy ⟨1, 0, 2⟩)]
  dtors := []
  fns := []

/-- `pSwap` followed by an in-place call passing a width-0 place to a callee whose parameter
(local 2) does not exist in the program. Merge `y' ↦ y.0`. -/
def pSwapPrm : Prog where
  sizes := [2, 2]
  body := [.storageLive 0, .assign ⟨0, 0, 2⟩ [.lit 1, .lit 2], .storageLive 1,
    .assign ⟨1, 0, 2⟩ [.copy ⟨0, 1, 1⟩, .copy ⟨0, 0, 1⟩], .out (.copy ⟨1, 0, 2⟩),
    .call 0 (.move ⟨0, 0, 0⟩)]
  dtors := []
  fns := [⟨2, []⟩]

/-- `x` (local 0) := 7 and `z` (local 3) := 3; `p` (local 1) := `&x`, then `p := &z`; the upgrade
site `y := copy x` (local 2, body index 8); then `out (load p 1)` (which reads `z`) and `out y`. -/
def pLoadOther : Prog where
  sizes := [1, 1, 1, 1]
  body := [.storageLive 0, .storageLive 1, .storageLive 2, .storageLive 3,
    .assign ⟨0, 0, 1⟩ [.lit 7], .assign ⟨3, 0, 1⟩ [.lit 3], .assign ⟨1, 0, 1⟩ [.addrOf ⟨0, 0, 1⟩],
    .assign ⟨1, 0, 1⟩ [.addrOf ⟨3, 0, 1⟩], .assign ⟨2, 0, 1⟩ [.copy ⟨0, 0, 1⟩],
    .out (.load ⟨1, 0, 1⟩ 1), .out (.copy ⟨2, 0, 1⟩)]
  dtors := []
  fns := []

end Toy.Coalesce
