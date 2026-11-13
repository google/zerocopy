-- Reproducible Lean 4.34.1 probe of @[implemented_by], @[csimp], @[extern],
-- Lean.ofReduceBool, and Lean.Meta.nativeEqTrue (native_decide) trust boundaries.

set_option linter.deprecated false

namespace NativeTrustProbe

-- 1. @[implemented_by]: kernel sees safeSpec (false), compiler/interpreter sees badImpl (true)
def badImpl (_ : Nat) : Bool := true

@[implemented_by badImpl]
def safeSpec (_ : Nat) : Bool := false

def safeSpec0 : Bool := safeSpec 0

theorem kernel_sees_safeSpec0 : safeSpec0 = false := rfl

-- 2. @[csimp]: kernel sees slowSpec (false), compiler replaces constant with fastReplacement (true).
-- Note that CSimp.replaceConstant (src/Lean/Compiler/CSimpAttr.lean:128-134) replaces `@slowSpec`
-- with `@fastReplacement` during LCNF lowering (ToDecl.replaceLogicConstants / ToLCNF) without
-- recording `unsound_csimp_ax` in the kernel expression of `callerOfCsimp`.
def slowSpec (n : Nat) : Bool := n == 1
def fastReplacement (n : Nat) : Bool := n == 0

axiom unsound_csimp_ax : @slowSpec = @fastReplacement
attribute [csimp] unsound_csimp_ax

def callerOfCsimp (n : Nat) : Bool := slowSpec n
def callerOfCsimp0 : Bool := callerOfCsimp 0

theorem kernel_sees_callerOfCsimp0 : callerOfCsimp0 = false := rfl

-- 3. Legacy in-kernel reduction via Lean.ofReduceBool / Lean.reduceBool:
-- Invokes `ir::run_boxed_kernel` in `src/kernel/type_checker.cpp:614-635` when applied to a 0-ary constant.
-- Records `[Lean.ofReduceBool, Lean.trustCompiler]` in `#print axioms` (and does NOT record `unsound_csimp_ax`!).
theorem native_via_ofReduceBool : safeSpec0 = true :=
  Lean.ofReduceBool safeSpec0 true rfl

theorem csimp_via_ofReduceBool : callerOfCsimp0 = true :=
  Lean.ofReduceBool callerOfCsimp0 true rfl

-- 4. Lean 4.34.1 `native_decide` via `Lean.Meta.nativeEqTrue` (`src/Lean/Meta/Native.lean:29-78`):
-- Evaluates a temporary `meta` declaration via `evalConst Bool` and emits a per-goal axiom
-- `_native.native_decide.ax_*` instead of `Lean.ofReduceBool`.
theorem native_via_native_decide : safeSpec0 = true := by
  native_decide

theorem csimp_via_native_decide : callerOfCsimp0 = true := by
  native_decide

-- 5. Combining kernel reduction (`rfl`) with native evaluation (`ofReduceBool` or `native_decide`)
-- derives `False` when `@[implemented_by]` or `@[csimp]` diverges from the logical definition:
theorem false_from_implemented_by_and_ofReduceBool : False := by
  have h1 : safeSpec0 = false := kernel_sees_safeSpec0
  have h2 : safeSpec0 = true := native_via_ofReduceBool
  rw [h1] at h2
  contradiction

theorem false_from_csimp_and_ofReduceBool : False := by
  have h1 : callerOfCsimp0 = false := kernel_sees_callerOfCsimp0
  have h2 : callerOfCsimp0 = true := csimp_via_ofReduceBool
  rw [h1] at h2
  contradiction

#print axioms kernel_sees_safeSpec0
#print axioms kernel_sees_callerOfCsimp0
#print axioms native_via_ofReduceBool
#print axioms csimp_via_ofReduceBool
#print axioms native_via_native_decide
#print axioms csimp_via_native_decide
#print axioms false_from_implemented_by_and_ofReduceBool
#print axioms false_from_csimp_and_ofReduceBool

end NativeTrustProbe

def main (args : List String) : IO UInt32 := do
  IO.println s!"safeSpec0 (compiled): {NativeTrustProbe.safeSpec0}"
  IO.println s!"callerOfCsimp0 (compiled): {NativeTrustProbe.callerOfCsimp0}"
  IO.println s!"args count: {args.length}"
  return 0
