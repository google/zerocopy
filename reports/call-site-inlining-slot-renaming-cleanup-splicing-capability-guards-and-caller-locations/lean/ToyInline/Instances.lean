import ToyInline.Build

/-!
# Concrete programs used by examples, non-vacuity witnesses and counterexamples

Convention: function `0` is the caller `F`, function `1` the callee `G`, the inlined call ends
block `0` of `F` (except where stated), and `abiC s := s.contains 1` is the ABI map.
-/

namespace Toy.Inline

/-- `abi` map used by the capability instances: the ABI depends on whether capability `1`
is enabled. -/
def abiC (s : CapSet) : Bool := s.contains 1

/-! ## A caller with cleanup and a callee that panics on argument `0` -/

/-- Callee: returns `x + 1` after emitting `x`; on `x = 0` panics into its cleanup, which emits
`100` and resumes. -/
def gP : Fn := mkFn 2 [blk [] (.branch (.var 1) 1 2), blk [] (.panic (.cleanup 3)),
  blk [.emit (.var 1), .assign 0 (.add (.var 1) (.const 1))] .ret,
  blk [.emit (.const 100)] .resume true]

/-- Caller: calls `gP` with its own argument into local `1`; on unwind emits `200` (a drop) and
resumes; on return emits the result. -/
def fP : Fn := mkFn 2 [blk [] (mkCall 1 [.var 1] 1 (some 1) (.cleanup 2)),
  blk [.emit (.var 1)] .ret, blk [.emit (.const 200)] .resume true]

def ciP : CallInfo := mkCallInfo 1 [.var 1] 1 (some 1) (.cleanup 2)
def progP : Program := mkProg [fP, gP]
def cfgP : InlineCfg := InlineCfg.canonical 2
def cfgPd : InlineCfg := { cfgP with ret := .dest }

/-! ## Unredirected `continue` and `resume` to the normal continuation -/

def kPanic : Fn := mkFn 1 [blk [] (.panic .continue)]
def contF : Fn := mkFn 2 [blk [] (mkCall 1 [] 1 (some 1) (.cleanup 2)), blk [] .ret,
  blk [.emit (.const 200)] .resume true]
def contCi : CallInfo := mkCallInfo 1 [] 1 (some 1) (.cleanup 2)
/-- Callee whose inner call (to a panicking function) continues unwinding. -/
def contG : Fn := mkFn 1 [blk [] (mkCall 2 [] 0 (some 1) .continue), blk [] .ret]
def contP : Program := mkProg [contF, contG, kPanic]
def contCfg : InlineCfg := cfgWith 2 (redirect := false)

/-- Callee that panics into its own cleanup, which emits `100` and resumes. -/
def resG : Fn := mkFn 1 [blk [] (.panic (.cleanup 1)), blk [.emit (.const 100)] .resume true]
def resP : Program := mkProg [contF, resG]
def resCfg : InlineCfg := cfgWith 2 (rm := .normal)

/-! ## Slot renaming -/

/-- Caller local `1` is live across the call. -/
def freshF : Fn := mkFn 2 [blk [.assign 1 (.use (.const 5))]
  (mkCall 1 [.const 9] 0 (some 1) .continue), blk [.emit (.var 1)] .ret]
def freshCi : CallInfo := mkCallInfo 1 [.const 9] 0 (some 1) .continue
def freshG : Fn := mkFn 2 [blk [.emit (.var 1)] .ret]
def freshP : Program := mkProg [freshF, freshG]
/-- Callee local `i` goes to host local `i`: the slot range overlaps the caller's locals. -/
def freshCfg : InlineCfg := cfgWith 2 (slot := some (fun i => i))

def injF : Fn := mkFn 1 [blk [] (mkCall 1 [.const 1, .const 2] 0 (some 1) .continue),
  blk [] .ret]
def injCi : CallInfo := mkCallInfo 1 [.const 1, .const 2] 0 (some 1) .continue
def injG : Fn := mkFn 3 [blk [.emit (.var 1), .emit (.var 2)] .ret]
def injP : Program := mkProg [injF, injG]
/-- Both callee arguments go to host local `5`. -/
def injCfg : InlineCfg := cfgWith 1 (slot := some (fun _ => 5))

def tempF : Fn := mkFn 1 [blk [] (mkCall 1 [.const 3] 0 (some 1) .continue), blk [] .ret]
def tempCi : CallInfo := mkCallInfo 1 [.const 3] 0 (some 1) .continue
/-- Callee that writes its return place before reading its argument. -/
def tempG : Fn := mkFn 2 [blk [.assign 0 (.use (.const 7)), .emit (.var 1)] .ret]
def tempP : Program := mkProg [tempF, tempG]
/-- The return temporary `2` coincides with the slot of callee argument `1`. -/
def tempCfg : InlineCfg := cfgWith 1 (slot := some (fun i => 1 + i)) (ret := some (.temp 2))

/-! ## Well-formedness of bodies -/

/-- Declares one local but keeps local `1` live across the call. -/
def locFF : Fn := mkFn 1 [blk [.assign 1 (.use (.const 5))]
  (mkCall 1 [] 0 (some 1) .continue), blk [.emit (.var 1)] .ret]
def locFCi : CallInfo := mkCallInfo 1 [] 0 (some 1) .continue
def locFG : Fn := mkFn 2 [blk [.assign 1 (.use (.const 9))] .ret]
def locFP : Program := mkProg [locFF, locFG]
def locFCfg : InlineCfg := cfgWith 1 (slot := some (fun i => i)) (ret := some (.temp 2))

def locGF : Fn := mkFn 1 [blk [] (mkCall 1 [.const 4] 0 (some 1) .continue), blk [] .ret]
def locGCi : CallInfo := mkCallInfo 1 [.const 4] 0 (some 1) .continue
/-- Declares one local but reads its argument (local `1`). -/
def locGG : Fn := mkFn 1 [blk [.emit (.var 1)] .ret]
def locGP : Program := mkProg [locGF, locGG]

/-- Its block `1` jumps to the missing block `4`. -/
def blkFF : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue), blk [] (.goto 4)]
def blkFCi : CallInfo := mkCallInfo 1 [] 0 (some 1) .continue
def blkFG : Fn := mkFn 1 [blk [.emit (.const 42)] .ret, blk [] .abort]
def blkFP : Program := mkProg [blkFF, blkFG]

def plainCi : CallInfo := mkCallInfo 1 [] 0 (some 1) .continue
def spanCi : CallInfo := mkCallInfo 1 [] 0 (some 1) .continue (span := 77)
/-- Its `loc` names the missing scope `1`. -/
def scFF : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue (span := 77)),
  blk [.loc 5 1] .ret]
def scFG : Fn := mkFn 1 [blk [] .ret] (tc := true)
def scFP : Program := mkProg [scFF, scFG]

def scGF : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue (span := 77)), blk [] .ret]
/-- A tracked callee whose `loc` names the missing scope `1`. -/
def scGG : Fn := mkFn 1 [blk [.loc 5 1] .ret] (tc := true)
def scGP : Program := mkProg [scGF, scGG]

/-- A function with no locals and no blocks (used as a mismatched `F`). -/
def emptyF : Fn := mkFn 0 []

/-! ## Scope-link rule across two levels of inlining -/

/-- Untracked outer function: calls `linkG` (span `10`). -/
def linkF : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue (span := 10)), blk [] .ret]
/-- Tracked middle function with a nested scope `1`; calls `linkK` from that scope (span `20`). -/
def linkG : Fn := mkFn 1 [blk [] (mkCall 2 [] 0 (some 1) .continue (span := 20) (scope := 1)),
  blk [] .ret] (tc := true) (scopes := [⟨none, none⟩, ⟨none, none⟩])
/-- Tracked inner function: reports its caller location. -/
def linkK : Fn := mkFn 1 [blk [.loc 30 0] .ret] (tc := true)
def linkP0 : Program := mkProg [linkF, linkG, linkK]
def linkCi0 : CallInfo := mkCallInfo 1 [] 0 (some 1) .continue (span := 10)
/-- `linkF` after inlining `linkG` with the canonical configuration. -/
def linkF1 : Fn := inlineFn linkF 0 (blk [] (.call linkCi0)) linkCi0 linkG (InlineCfg.canonical 1)
def linkP1 : Program := mkProg [linkF1, linkG, linkK]
/-- The copied call to `linkK`, now ending block `3` of `linkF1`, in scope `2`. -/
def linkCi1 : CallInfo := mkCallInfo 2 [] 1 (some 4) .continue (span := 20) (scope := 2)
def linkCfg : InlineCfg := cfgWith 2 (link := .ignoreParent)

theorem linkP1_eq : inlineCanon linkP0 0 0 = linkP1 := rfl

/-! ## Capabilities and ABI -/

def capF (caps : CapSet) : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue),
  blk [] .ret] (caps := caps)

/-- Callee (no capabilities) making an ABI-sensitive call to `abiK`. -/
def abiG : Fn := mkFn 1 [blk [] (mkCall 2 [.const 5] 0 (some 1) .continue (abiSens := true)),
  blk [] .ret]
def abiK : Fn := mkFn 2 [blk [.emit (.var 1)] .ret]
def abiP : Program := mkProg [capF [1], abiG, abiK] (abi := abiC)
/-- Same program with an ABI map that ignores capabilities (positive control). -/
def abiPc : Program := mkProg [capF [1], abiG, abiK] (abi := fun _ => false)

/-- Callee holding capability `3` and using it. -/
def needG : Fn := mkFn 1 [blk [.needCap 3, .emit (.const 1)] .ret] (caps := [3])
def needP : Program := mkProg [capF [], needG] (abi := abiC)

/-- Callee using capability `3` without holding it. -/
def legalG : Fn := mkFn 1 [blk [.needCap 3, .emit (.const 1)] .ret]
def legalP : Program := mkProg [capF [3], legalG] (abi := abiC)

/-- Caller (capability `1`) whose call to the callee is ABI-sensitive. -/
def cabF : Fn := mkFn 1 [blk [] (mkCall 1 [.const 5] 0 (some 1) .continue (abiSens := true)),
  blk [] .ret] (caps := [1])
def cabCi : CallInfo := mkCallInfo 1 [.const 5] 0 (some 1) .continue (abiSens := true)
def cabG : Fn := mkFn 2 [blk [.emit (.var 1)] .ret]
def cabP : Program := mkProg [cabF, cabG] (abi := abiC)

/-! ## Destination mode -/

/-- Callee that writes its return place and then panics. -/
def dG : Fn := mkFn 1 [blk [.assign 0 (.use (.const 9))] (.panic .continue)]
/-- Cleanup block `1` jumps to the normal block `2`, which reads the destination `1`. -/
def clF : Fn := mkFn 2 [blk [.assign 1 (.use (.const 5))] (mkCall 1 [] 1 (some 3) (.cleanup 1)),
  blk [] (.goto 2) true, blk [.emit (.var 1)] .resume, blk [] .ret]
def clCi : CallInfo := mkCallInfo 1 [] 1 (some 3) (.cleanup 1)
def clP : Program := mkProg [clF, dG]
/-- Cleanup block `1` reads the destination `1`. -/
def dcF : Fn := mkFn 2 [blk [.assign 1 (.use (.const 5))] (mkCall 1 [] 1 (some 2) (.cleanup 1)),
  blk [.emit (.var 1)] .resume true, blk [] .ret]
def dcCi : CallInfo := mkCallInfo 1 [] 1 (some 2) (.cleanup 1)
def dcP : Program := mkProg [dcF, dG]

/-! ## Two-level tracked chains for the caller-location policies -/

def chainF : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue (span := 10)), blk [] .ret]
def chainG (tc : Bool) : Fn :=
  mkFn 1 [blk [] (mkCall 2 [] 0 (some 1) .continue (span := 20)), blk [] .ret] (tc := tc)
def chainK : Fn := mkFn 1 [blk [.loc 30 0] .ret] (tc := true)
/-- `chainP true`: tracked `k` called by tracked `g` called by untracked `f`;
`chainP false`: the middle function `g` is an untracked wrapper. -/
def chainP (tc : Bool) : Program := mkProg [chainF, chainG tc, chainK]
/-- Inline `g` into `f`, then the copied call to `k` (block `3` of the new `f`). -/
def chainQ (tc : Bool) : Program := inlineCanon (inlineCanon (chainP tc) 0 0) 0 3

end Toy.Inline
