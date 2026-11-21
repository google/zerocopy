import MonoShim.SourceOnly

/-!
# Omitting any one of four edge kinds can break closure

Each counterexample below uses a collector edge function that omits one runtime reference kind.
All other hypotheses of the closure and adequacy theorems hold (roots in `T`, `T` closed under the
collector's edges, synthesizer totality and agreement, source definedness, canonical keys and
references), yet the target is not closed and the collected program calls an undefined symbol on
a run from the root, while the source semantics runs to completion or unwinds normally.
-/

namespace Toy.MonoShim

/-- The empty initial state. -/
def st0 : St := ⟨[], 0⟩

/-- One differing run refutes the conclusion of the adequacy theorem for a one-root list. -/
theorem not_forall_runM_eq_runS_of_ne {P : Program} {cfg : MonoCfg} {T : List Key} {r : Key}
    {n : Nat} {st : St} (hne : runM P cfg T n r st ≠ runS P n r st) :
    ¬ (∀ r' ∈ [r], ∀ (n : Nat) (st : St), runM P cfg T n r' st = runS P n r' st) :=
  fun h => hne (h r (by simp) n st)

/-- Edge function that ignores cleanup paths (the cleanup of `onUnwind`, and the drops of an
aggregate clone). -/
def refsNoCleanup (sig : Sig) : Stmt → List Key
  | .seq a b => refsNoCleanup sig a ++ refsNoCleanup sig b
  | .onUnwind a _ => refsNoCleanup sig a
  | .cloneAgg ts => ts.map cloneKey
  | .guard s => refsNoCleanup sig s
  | s => refs sig s

/-- Edge function that records the drop entry of a vtable but none of its method entries (a method
then enters the target through a syntactic method call, if there is one). -/
def refsNoVtable (sig : Sig) : Stmt → List Key
  | .seq a b => refsNoVtable sig a ++ refsNoVtable sig b
  | .onUnwind a b => refsNoVtable sig a ++ refsNoVtable sig b
  | .guard s => refsNoVtable sig s
  | .unsize _ t _ => [.dropGlue t]
  | s => refs sig s

/-- Edge function that ignores functions used in operand position (reified to pointers). -/
def refsNoOperand (sig : Sig) : Stmt → List Key
  | .seq a b => refsNoOperand sig a ++ refsNoOperand sig b
  | .onUnwind a b => refsNoOperand sig a ++ refsNoOperand sig b
  | .guard s => refsNoOperand sig s
  | .reify _ _ _ => []
  | s => refs sig s

/-- Edge function that records a reified function as its plain instance, ignoring the reify shim
a `trackCaller` function needs. -/
def refsNoReifyShim (sig : Sig) : Stmt → List Key
  | .seq a b => refsNoReifyShim sig a ++ refsNoReifyShim sig b
  | .onUnwind a b => refsNoReifyShim sig a ++ refsNoReifyShim sig b
  | .guard s => refsNoReifyShim sig s
  | .reify _ f τs => [.inst f τs]
  | s => refs sig s

/-! ## (a) A type dropped on a cleanup path and on no normal path -/

/-- `main` holds a value of `base 1` (whose `Drop` emits 7) across a call to `g`, which panics;
on the normal path the value would be moved away, so its one drop is on the cleanup path. -/
def P2a : Program where
  fns := [⟨false, .onUnwind (.call 1 []) (.drop (.base 1))⟩, ⟨false, .panic⟩]
  methods := []
  impls := []
  dropImpls := [(1, .emit 7)]
  cloneImpls := []
  assoc := []

def cfg2a : MonoCfg := ⟨refsNoCleanup P2a.sig, synthStd P2a⟩
def T2a : List Key := [.inst 1 [], .inst 0 []]

theorem cleanup_edges_missing_break_closure :
    ¬ CoversRefs P2a.sig cfg2a.E ∧
    collect (edgesM P2a cfg2a) fifo [.inst 0 []] 10 = some T2a ∧
    RootsIn [.inst 0 []] T2a ∧ EdgesIn (edgesM P2a cfg2a) T2a ∧ SynthAgrees P2a cfg2a T2a ∧
    SynthTotal cfg2a T2a ∧ InstDefined P2a T2a ∧
    CanonicalKeys P2a T2a ∧ CanonicalRefs P2a cfg2a T2a ∧
    ¬ Closed P2a.sig (tableM P2a cfg2a T2a) T2a ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM P2a cfg2a T2a n r st = runS P2a n r st) ∧
    runM P2a cfg2a T2a 3 (.inst 0 []) st0 = (.link (.dropGlue (.base 1)), st0) ∧
    runS P2a 3 (.inst 0 []) st0 = (.unwind, ⟨[7], 0⟩) := by
  refine ⟨?_, by decide, by decide, by decide, fun k _ hk => synthStd_optEquiv P2a k hk,
    by decide, by decide, by decide, by decide, by decide,
    not_forall_runM_eq_runS_of_ne (n := 3) (st := st0) (by decide), by decide, by decide⟩
  intro h
  have := h (.onUnwind (.call 1 []) (.drop (.base 1))) (.dropGlue (.base 1)) (by decide)
  revert this; decide

/-! ## (b) Vtable methods that are never called syntactically -/

/-- `main` unsizes a `base 2` to `dyn 0` (trait 0 has method 0, implemented for `base 2` by
emitting 5) and calls method 0 through the trait object; no syntactic call to
`<base 2 as 0>::0` exists. -/
def P2b : Program where
  fns := [⟨false, .seq (.unsize 0 (.base 2) 0) (.callDyn 0 0)⟩]
  methods := [(0, [0])]
  impls := [⟨0, 0, .base 2, .emit 5⟩]
  dropImpls := []
  cloneImpls := []
  assoc := []

def cfg2b : MonoCfg := ⟨refsNoVtable P2b.sig, synthStd P2b⟩
def T2b : List Key := [.dropGlue (.base 2), .inst 0 []]

theorem vtable_edges_missing_break_closure :
    ¬ CoversRefs P2b.sig cfg2b.E ∧
    collect (edgesM P2b cfg2b) fifo [.inst 0 []] 10 = some T2b ∧
    RootsIn [.inst 0 []] T2b ∧ EdgesIn (edgesM P2b cfg2b) T2b ∧ SynthAgrees P2b cfg2b T2b ∧
    SynthTotal cfg2b T2b ∧ InstDefined P2b T2b ∧
    CanonicalKeys P2b T2b ∧ CanonicalRefs P2b cfg2b T2b ∧
    ¬ Closed P2b.sig (tableM P2b cfg2b T2b) T2b ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM P2b cfg2b T2b n r st = runS P2b n r st) ∧
    runM P2b cfg2b T2b 3 (.inst 0 []) st0 = (.link (.meth 0 0 (.base 2)), st0) ∧
    runS P2b 3 (.inst 0 []) st0 = (.ok, ⟨[5], 0⟩) := by
  refine ⟨?_, by decide, by decide, by decide, fun k _ hk => synthStd_optEquiv P2b k hk,
    by decide, by decide, by decide, by decide, by decide,
    not_forall_runM_eq_runS_of_ne (n := 3) (st := st0) (by decide), by decide, by decide⟩
  intro h
  have := h (.unsize 0 (.base 2) 0) (.meth 0 0 (.base 2)) (by decide)
  revert this; decide

/-! ## (c) A function used in operand position and never called directly -/

/-- `main` reifies `f` (function 1, which emits 3) to a pointer and calls through it. -/
def P2c : Program where
  fns := [⟨false, .seq (.reify 0 1 []) (.callPtr 0)⟩, ⟨false, .emit 3⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []

def cfg2c : MonoCfg := ⟨refsNoOperand P2c.sig, synthStd P2c⟩
def T2c : List Key := [.inst 0 []]

theorem operand_edges_missing_break_closure :
    ¬ CoversRefs P2c.sig cfg2c.E ∧
    collect (edgesM P2c cfg2c) fifo [.inst 0 []] 10 = some T2c ∧
    RootsIn [.inst 0 []] T2c ∧ EdgesIn (edgesM P2c cfg2c) T2c ∧ SynthAgrees P2c cfg2c T2c ∧
    SynthTotal cfg2c T2c ∧ InstDefined P2c T2c ∧
    CanonicalKeys P2c T2c ∧ CanonicalRefs P2c cfg2c T2c ∧
    ¬ Closed P2c.sig (tableM P2c cfg2c T2c) T2c ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM P2c cfg2c T2c n r st = runS P2c n r st) ∧
    runM P2c cfg2c T2c 3 (.inst 0 []) st0 = (.link (.inst 1 []), st0) ∧
    runS P2c 3 (.inst 0 []) st0 = (.ok, ⟨[3], 0⟩) := by
  refine ⟨?_, by decide, by decide, by decide, fun k _ hk => synthStd_optEquiv P2c k hk,
    by decide, by decide, by decide, by decide, by decide,
    not_forall_runM_eq_runS_of_ne (n := 3) (st := st0) (by decide), by decide, by decide⟩
  intro h
  have := h (.reify 0 1 []) (.inst 1 []) (by decide)
  revert this; decide

/-! ## (d) A `trackCaller` function reified to a pointer needs its reify shim -/

/-- As `P2c`, but function 1 is `trackCaller`, so its pointer designates the reify shim. -/
def P2d : Program where
  fns := [⟨false, .seq (.reify 0 1 []) (.callPtr 0)⟩, ⟨true, .emit 4⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []

def cfg2d : MonoCfg := ⟨refsNoReifyShim P2d.sig, synthStd P2d⟩
def T2d : List Key := [.inst 1 [], .inst 0 []]

theorem reify_shim_edges_missing_break_closure :
    ¬ CoversRefs P2d.sig cfg2d.E ∧
    collect (edgesM P2d cfg2d) fifo [.inst 0 []] 10 = some T2d ∧
    RootsIn [.inst 0 []] T2d ∧ EdgesIn (edgesM P2d cfg2d) T2d ∧ SynthAgrees P2d cfg2d T2d ∧
    SynthTotal cfg2d T2d ∧ InstDefined P2d T2d ∧
    CanonicalKeys P2d T2d ∧ CanonicalRefs P2d cfg2d T2d ∧
    ¬ Closed P2d.sig (tableM P2d cfg2d T2d) T2d ∧
    ¬ (∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St),
      runM P2d cfg2d T2d n r st = runS P2d n r st) ∧
    runM P2d cfg2d T2d 3 (.inst 0 []) st0 = (.link (.reifyShim 1 []), st0) ∧
    runS P2d 3 (.inst 0 []) st0 = (.ok, ⟨[4], 0⟩) := by
  refine ⟨?_, by decide, by decide, by decide, fun k _ hk => synthStd_optEquiv P2d k hk,
    by decide, by decide, by decide, by decide, by decide,
    not_forall_runM_eq_runS_of_ne (n := 3) (st := st0) (by decide), by decide, by decide⟩
  intro h
  have := h (.reify 0 1 []) (.reifyShim 1 []) (by decide)
  revert this; decide

/-! ## Positive controls: the full edge function closes each example -/

/-- With the full edge function `refs` and the standard synthesizer, the collector's output for
each of the four programs is a closed target. -/
theorem full_edges_close_missing_edge_examples :
    collect (edgesM P2a (stdCfg P2a)) fifo [.inst 0 []] 10 =
      some [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    Closed P2a.sig (tableM P2a (stdCfg P2a) [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []])
      [.userDrop 1, .dropGlue (.base 1), .inst 1 [], .inst 0 []] ∧
    collect (edgesM P2b (stdCfg P2b)) fifo [.inst 0 []] 10 =
      some [.dropGlue (.base 2), .meth 0 0 (.base 2), .inst 0 []] ∧
    Closed P2b.sig (tableM P2b (stdCfg P2b) [.dropGlue (.base 2), .meth 0 0 (.base 2), .inst 0 []])
      [.dropGlue (.base 2), .meth 0 0 (.base 2), .inst 0 []] ∧
    collect (edgesM P2c (stdCfg P2c)) fifo [.inst 0 []] 10 = some [.inst 1 [], .inst 0 []] ∧
    Closed P2c.sig (tableM P2c (stdCfg P2c) [.inst 1 [], .inst 0 []]) [.inst 1 [], .inst 0 []] ∧
    collect (edgesM P2d (stdCfg P2d)) fifo [.inst 0 []] 10 =
      some [.inst 1 [], .reifyShim 1 [], .inst 0 []] ∧
    Closed P2d.sig (tableM P2d (stdCfg P2d) [.inst 1 [], .reifyShim 1 [], .inst 0 []])
      [.inst 1 [], .reifyShim 1 [], .inst 0 []] := by
  decide

end Toy.MonoShim
