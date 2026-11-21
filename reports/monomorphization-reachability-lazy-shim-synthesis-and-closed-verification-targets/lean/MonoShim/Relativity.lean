import MonoShim.Canonical

/-!
# Over-approximation, and closure relative to the available bodies
-/

namespace Toy.MonoShim

/-! ## The collected set can contain keys that never run -/

/-- `main` panics before it would call function 1 (which emits 1): the call is dead code. -/
def P7a : Program where
  fns := [⟨false, .seq .panic (.call 1 [])⟩, ⟨false, .emit 1⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []

def T7a : List Key := [.inst 1 [], .inst 0 []]

/-- Every key list that contains the roots and is closed under an edge function contains every
reachable key; with `collect_mem_iff_reach`, a key list the collector returns when run with an admissible scheduler is therefore the least such set (static minimality). -/
theorem reach_subset_of_rootsIn_edgesIn (edges : Key → List Key) (roots T : List Key)
    (hR : RootsIn roots T) (hE : EdgesIn edges T) : ∀ k, Reach edges roots k → k ∈ T := by
  intro k hk
  induction hk with
  | root h => exact hR _ h
  | step _ he ih => exact hE _ ih _ he

/-- **The collected set is not dynamically minimal.** The collector includes the dead-code
instance `inst 1 []`, yet dropping it from the table changes no run from the root (at any fuel
and state); the smaller set is not closed under the collector's edges, so no collector run with
an admissible scheduler returns it (by `collect_mem_iff_reach`). -/
theorem collected_set_includes_dead_code_not_minimal :
    collect (edgesM P7a (stdCfg P7a)) fifo [.inst 0 []] 10 = some T7a ∧
    Key.inst 1 [] ∈ T7a ∧ ¬ EdgesIn (edgesM P7a (stdCfg P7a)) [.inst 0 []] ∧
    ∀ (n : Nat) (st : St),
      runM P7a (stdCfg P7a) T7a n (.inst 0 []) st = runM P7a (stdCfg P7a) [.inst 0 []] n (.inst 0 []) st := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro n st
  cases n with
  | zero => rfl
  | succ n => rfl

/-! ## Closure is relative to the bodies available -/

/-- `main` (local) calls `ext`, a non-generic function of another crate (function 1) that drops a
`base 0`; `base 0` has a destructor emitting 3. -/
def P7b : Program where
  fns := [⟨false, .call 1 []⟩, ⟨false, .drop (.base 0)⟩]
  methods := []
  impls := []
  dropImpls := [(0, .emit 3)]
  cloneImpls := []
  assoc := []

/-- A per-crate collector that sees the bodies `avail` marks available and no others: it creates no node
for an unavailable key (the key is assumed to be linked from elsewhere). -/
def edgesAvail (P : Program) (cfg : MonoCfg) (avail : Key → Bool) (k : Key) : List Key :=
  (edgesM P cfg k).filter avail

/-- The local crate does not have the body of `ext` (as for a non-generic, non-inline function of
another crate). -/
def availLocal : Key → Bool
  | .inst 1 _ => false
  | _ => true

/-- The whole-program target of `P7b`. -/
def T7b : List Key := [.userDrop 0, .dropGlue (.base 0), .inst 1 [], .inst 0 []]

/-- **A per-crate closed set has holes at external instances whose bodies are absent**, while
the whole-program collection of the same program is closed and agrees with the source at every
fuel and state. -/
theorem per_crate_collection_has_holes :
    collect (edgesAvail P7b (stdCfg P7b) availLocal) fifo [.inst 0 []] 10 = some [.inst 0 []] ∧
    ¬ Closed P7b.sig (tableM P7b (stdCfg P7b) [.inst 0 []]) [.inst 0 []] ∧
    runM P7b (stdCfg P7b) [.inst 0 []] 4 (.inst 0 []) st0 = (.link (.inst 1 []), st0) ∧
    runS P7b 4 (.inst 0 []) st0 = (.ok, ⟨[3], 0⟩) ∧
    collect (edgesM P7b (stdCfg P7b)) fifo [.inst 0 []] 10 = some T7b ∧
    Closed P7b.sig (tableM P7b (stdCfg P7b) T7b) T7b ∧
    ∀ (n : Nat) (st : St), runM P7b (stdCfg P7b) T7b n (.inst 0 []) st = runS P7b n (.inst 0 []) st := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro n st
  exact runM_eq_runS_of_rootsIn_edgesIn_covering_agreeing_canonical P7b (stdCfg P7b)
    [.inst 0 []] T7b (by decide) (by decide) (fun _ _ h => h) (synthStd_agrees P7b _)
    (by decide) (by decide) _ (by simp) n st

end Toy.MonoShim
