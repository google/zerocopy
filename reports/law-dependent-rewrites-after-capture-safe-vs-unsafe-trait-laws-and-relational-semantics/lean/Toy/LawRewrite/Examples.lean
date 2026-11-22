import Toy.LawRewrite.Basic
import Toy.LawRewrite.Lemmas

/-!
# Concrete instances and definition examples

Concrete impls, environments and rewrites used throughout, and for each core
definition at least one proved positive example (an instance it must admit) and one
proved negative example (an instance it must reject).
-/

namespace Toy.LawRewrite

/-! ## Concrete impls, environments, rewrites -/

/-- A non-trivial `Clone` for a `Copy` type: it emits the value `9` (for example, a
log line) and returns its argument. -/
def loggingClone : Impl := fun v => ([9], v)

/-- An effect-free `Clone` that violates the copy law: it returns its argument plus
one. -/
def succClone : Impl := fun v => ([], v + 1)

/-- Every instance belongs to a safe trait, has the logging clone as impl, and has a
copy as contract. -/
def envSafeLog : Env :=
  { impl := fun _ => loggingClone, contract := fun _ => copyImpl, safety := fun _ => .safeTrait }

/-- As `envSafeLog`, but every instance belongs to an unsafe trait. -/
def envUnsafeLog : Env :=
  { impl := fun _ => loggingClone, contract := fun _ => copyImpl, safety := fun _ => .unsafeTrait }

/-- Every instance belongs to a safe trait and its impl is a copy (the law holds). -/
def envSafeTriv : Env :=
  { impl := fun _ => copyImpl, contract := fun _ => copyImpl, safety := fun _ => .safeTrait }

/-- Every instance belongs to an unsafe trait and its impl is a copy (the law holds). -/
def envUnsafeTriv : Env :=
  { impl := fun _ => copyImpl, contract := fun _ => copyImpl, safety := fun _ => .unsafeTrait }

/-- Every instance belongs to a safe trait and its impl is `succClone`. -/
def envSafeSucc : Env :=
  { impl := fun _ => succClone, contract := fun _ => copyImpl, safety := fun _ => .safeTrait }

/-- Every instance belongs to an unsafe trait and its impl is `succClone` (effect-free,
returns its argument plus one, violating the copy contract). -/
def envUnsafeSucc : Env :=
  { impl := fun _ => succClone, contract := fun _ => copyImpl, safety := fun _ => .unsafeTrait }

/-- Every instance belongs to an unsafe trait; its impl agrees with `copyImpl` at
argument `5` and emits `9` (violating the copy contract) at every other argument. -/
def envUnsafeSelective : Env :=
  { impl := fun _ v => if v = 5 then ([], 5) else ([9], v)
    contract := fun _ => copyImpl
    safety := fun _ => .unsafeTrait }

/-- clone→copy on instance `0`: every call of instance `0` becomes a copy. -/
def cloneToCopy : Rewrite := { targets := fun i => i == 0, repl := fun _ => copyImpl }

/-- clone→copy on instance `1`. -/
def cloneToCopy1 : Rewrite := { targets := fun i => i == 1, repl := fun _ => copyImpl }

/-- A rewrite of instance `0`'s calls into `succClone`, which is not the contract
(`copyImpl`). -/
def succRewrite : Rewrite := { targets := fun i => i == 0, repl := fun _ => succClone }

/-- The store with every variable `0`. -/
def σ0 : Store := fun _ => 0

/-- Call instance `0` twice on the value `5`; emit nothing directly. -/
def twoCalls : Prog := [.set 0 5, .call 0 1 0, .call 0 1 0]

/-- Call instance `0` on the value `5` and never use the result. -/
def deadCall : Prog := [.set 0 5, .call 0 1 0]

/-! ## Definition examples -/

/-- `LawAt` admits a copy impl under clone→copy. -/
theorem lawAt_pos : LawAt envSafeTriv cloneToCopy 0 5 := rfl

/-- `LawAt` rejects the logging clone under clone→copy. -/
theorem lawAt_neg : ¬ LawAt envSafeLog cloneToCopy 0 5 := by
  unfold LawAt; decide

/-- `ImprovesPP` admits a target that extends the trace before the source's UB. -/
theorem improvesPP_pos : ImprovesPP (.done [1, 2]) (.ub [1]) := by decide

/-- `ImprovesPP` rejects a target that does not preserve the events before the
source's UB. -/
theorem improvesPP_neg : ¬ ImprovesPP (.done [2]) (.ub [1]) := by decide

/-- `ImprovesWT` admits any target behaviour against source UB, even one that does
not preserve the events before it. -/
theorem improvesWT_pos : ImprovesWT (.done [2]) (.ub [1]) := by decide

/-- `ImprovesWT` rejects a different normal behaviour. -/
theorem improvesWT_neg : ¬ ImprovesWT (.done [1]) (.done [2]) := by decide

/-- `RefinesPP` admits a target whose behaviours all improve a source behaviour. -/
theorem refinesPP_pos : RefinesPP [.ub [1]] [.done [1, 2], .ub [1, 3]] := by decide

/-- `RefinesPP` rejects a target with an extra normal behaviour. -/
theorem refinesPP_neg : ¬ RefinesPP [.done [1]] [.done [1], .done [2]] := by decide

/-- `RefinesWT` admits a target that drops the events before the source's UB. -/
theorem refinesWT_pos : RefinesWT [.ub [1]] [.done [2]] := by decide

/-- `RefinesWT` rejects a target with an extra normal behaviour. -/
theorem refinesWT_neg : ¬ RefinesWT [.done [1]] [.done [2]] := by decide

/-- `Sat` admits a list all of whose behaviours satisfy the specification. -/
theorem sat_pos : Sat [.done [1], .ub [1]] (fun b => b.trace = [1]) := by decide

/-- `Sat` rejects a list with one violating behaviour. -/
theorem sat_neg : ¬ Sat [.done [1], .done [2]] (fun b => b.trace = [1]) := by decide

/-- `UBFreeSpec` admits "terminates normally". -/
theorem ubFreeSpec_pos : UBFreeSpec (fun b => ∃ t, b = .done t) := by
  intro t ⟨u, hu⟩; cases hu

/-- `UBFreeSpec` rejects the trivial specification. -/
theorem ubFreeSpec_neg : ¬ UBFreeSpec (fun _ => True) := fun h => h [] trivial

/-- `capDirect`, safe instance: the logging clone's effect `9`, then the result `5`. -/
theorem capDirect_safe_example : capDirect envSafeLog .before (probe 0 5) σ0 = [.done [9, 5]] := by
  decide

/-- `capDirect`, unsafe instance violating the contract, relies point before the impl:
UB before any event. -/
theorem capDirect_before_example : capDirect envUnsafeLog .before (probe 0 5) σ0 = [.ub []] := by
  decide

/-- `capDirect`, unsafe instance violating the contract, relies point after the impl:
UB after the impl's effect `9`. -/
theorem capDirect_after_example : capDirect envUnsafeLog .after (probe 0 5) σ0 = [.ub [9]] := by
  decide

/-- `capDirect`, unsafe instance satisfying the contract: no UB. -/
theorem capDirect_unsafe_lawful_example :
    capDirect envUnsafeTriv .before (probe 0 5) σ0 = [.done [5]] := by
  decide

/-- `compiled` runs the impl and checks no law, even for an unsafe instance. -/
theorem compiled_example : compiled envUnsafeLog (probe 0 5) σ0 = [.done [9, 5]] := by decide

/-- `capRel` for clone→copy: the call may run the logging clone or the copy. -/
theorem capRel_example :
    capRel envSafeLog [cloneToCopy] (probe 0 5) σ0 = [.done [9, 5], .done [5]] := by
  decide

/-- `capRel` with no rewrite has exactly the compiled behaviours here. -/
theorem capRel_nil_example : capRel envSafeLog [] (probe 0 5) σ0 = [.done [9, 5]] := by decide

/-- `capRel` ignores `env.safety` and `env.contract`: on `envUnsafeLog`, `capDirect` is UB
whereas `capRel` returns normal behaviours from the impl and replacement. -/
theorem capRel_unsafe_ignores_contract_example :
    capDirect envUnsafeLog .before (probe 0 5) σ0 = [.ub []] ∧
      capRel envUnsafeLog [cloneToCopy] (probe 0 5) σ0 = [.done [9, 5], .done [5]] := by
  decide

/-- `Rewrite.apply` replaces a call of a targeted instance by its replacement code. -/
theorem apply_pos :
    cloneToCopy.apply (probe 0 5) = [.set 0 5, .prim copyImpl 1 0, .out 1] := rfl

/-- `Rewrite.apply` leaves a call of an untargeted instance unchanged. -/
theorem apply_neg : cloneToCopy.apply [.call 1 1 0] = [.call 1 1 0] := rfl

/-- `Rewrite.applyAt` rewrites the selected site (statement `1`) and leaves the other call. -/
theorem applyAt_example :
    cloneToCopy.applyAt (fun k => k == 1) 0 twoCalls =
      [.set 0 5, .prim copyImpl 1 0, .call 0 1 0] := rfl

/-- `applySeq` applies the rewrites in order. -/
theorem applySeq_example :
    applySeq [cloneToCopy, cloneToCopy1] [.call 0 1 0, .call 1 1 0] =
      [.prim copyImpl 1 0, .prim copyImpl 1 0] := rfl

/-- `Reaches` admits the call of the probe at the probed argument. -/
theorem reaches_pos : Reaches envSafeLog (probe 0 5) σ0 0 5 := by
  simp [Reaches, probe, Store.upd]

/-- `Reaches` rejects another argument. -/
theorem reaches_neg_arg : ¬ Reaches envSafeLog (probe 0 5) σ0 0 4 := by
  simp [Reaches, probe, Store.upd]

/-- `Reaches` rejects a call after `ub`. -/
theorem reaches_neg_after_ub : ¬ Reaches envSafeLog [.ub, .call 0 1 0] σ0 0 0 := by
  simp [Reaches]

/-- `LawOnReached` admits a copy impl. -/
theorem lawOnReached_pos : LawOnReached envSafeTriv cloneToCopy (probe 0 5) σ0 :=
  fun _ _ _ _ => rfl

/-- `LawOnReached` rejects the logging clone on the probe. -/
theorem lawOnReached_neg : ¬ LawOnReached envSafeLog cloneToCopy (probe 0 5) σ0 :=
  fun h => lawAt_neg (h 0 5 rfl reaches_pos)

/-- `LawOnReached` holds vacuously when the targeted call is unreachable. -/
theorem lawOnReached_unreached : LawOnReached envSafeLog cloneToCopy [.ub, .call 0 1 0] σ0 := by
  intro i v _ h
  simp [Reaches] at h

/-- `LawOnTargets` admits a copy impl. -/
theorem lawOnTargets_pos : LawOnTargets envSafeTriv cloneToCopy := fun _ _ _ => rfl

/-- `LawOnTargets` rejects the logging clone. -/
theorem lawOnTargets_neg : ¬ LawOnTargets envSafeLog cloneToCopy :=
  fun h => lawAt_neg (h 0 rfl 5)

/-- `ContextSafeAt` admits an unsafe contract violation with the relies point before
the impl. -/
theorem contextSafeAt_pos : ContextSafeAt envUnsafeLog .before cloneToCopy 0 5 := by
  refine Or.inr ⟨rfl, ?_, Or.inl rfl⟩
  decide

/-- `ContextSafeAt` rejects a safe law violation. -/
theorem contextSafeAt_neg_safe : ¬ ContextSafeAt envSafeLog .before cloneToCopy 0 5 := by
  rintro (h | ⟨hs, _, _⟩)
  · exact lawAt_neg h
  · cases hs

/-- `ContextSafeAt` rejects an unsafe contract violation whose relies point follows an
effect (`9`) that the replacement does not emit. -/
theorem contextSafeAt_neg_after : ¬ ContextSafeAt envUnsafeLog .after cloneToCopy 0 5 := by
  rintro (h | ⟨_, _, hp | hp⟩)
  · exact lawAt_neg h
  · cases hp
  · exact absurd hp (by decide)

/-- `ContextSafeAt` admits an unsafe contract violation under relies point `after` when
the impl's effects (`[]`) are a prefix of the replacement's effects (`[]`), even though
`LawAt` fails (`succClone` returns `6`, `copyImpl` returns `5`). -/
theorem contextSafeAt_pos_after_prefix :
    ¬ LawAt envUnsafeSucc cloneToCopy 0 5 ∧
      ContextSafeAt envUnsafeSucc .after cloneToCopy 0 5 := by
  refine ⟨by unfold LawAt; decide, Or.inr ⟨rfl, ?_, Or.inr List.nil_prefix⟩⟩
  decide

/-- `ContextSafeAt` rejects a non-contract replacement on an unsafe instance whose impl
obeys its contract (`impl = contract ≠ repl`), even with the relies point `before`. -/
theorem contextSafeAt_neg_unsafe_lawful_noncontract :
    envUnsafeTriv.safety 0 = .unsafeTrait ∧
      ¬ ContextSafeAt envUnsafeTriv .before succRewrite 0 5 := by
  refine ⟨rfl, ?_⟩
  rintro (hlaw | ⟨_, hne, _⟩)
  · unfold LawAt at hlaw
    simp [envUnsafeTriv, succRewrite, copyImpl, succClone] at hlaw
  · exact hne rfl

/-- `TargetsUnsafe` admits clone→copy over unsafe instances. -/
theorem targetsUnsafe_pos : TargetsUnsafe envUnsafeLog cloneToCopy := fun _ _ => rfl

/-- `TargetsUnsafe` rejects clone→copy over safe instances. -/
theorem targetsUnsafe_neg : ¬ TargetsUnsafe envSafeLog cloneToCopy :=
  fun h => by cases h 0 rfl

/-- `ReplIsContract` admits clone→copy when the contract is a copy. -/
theorem replIsContract_pos : ReplIsContract envUnsafeLog cloneToCopy := fun _ _ => rfl

/-- `ReplIsContract` rejects a replacement other than the contract. -/
theorem replIsContract_neg : ¬ ReplIsContract envUnsafeTriv succRewrite := by
  intro h
  have := congrFun (h 0 rfl) 0
  simp [succRewrite, succClone, envUnsafeTriv, copyImpl] at this

/-- `TargetsDisjoint` admits rewrites of different instances. -/
theorem targetsDisjoint_pos : TargetsDisjoint cloneToCopy cloneToCopy1 := by
  intro i h
  simp [cloneToCopy] at h
  subst h
  rfl

/-- `TargetsDisjoint` rejects two rewrites of instance `0`. -/
theorem targetsDisjoint_neg : ¬ TargetsDisjoint cloneToCopy succRewrite :=
  fun h => by cases h 0 rfl

/-- `CoveredBy` admits a rewrite listed in the list. -/
theorem coveredBy_pos : CoveredBy [cloneToCopy] cloneToCopy :=
  fun _ h => ⟨cloneToCopy, List.mem_singleton.mpr rfl, h, rfl⟩

/-- `CoveredBy` rejects a targeting rewrite against the empty list. -/
theorem coveredBy_neg : ¬ CoveredBy [] cloneToCopy := by
  intro h
  obtain ⟨_, hm, _⟩ := h 0 rfl
  cases hm

/-- `callsSome` finds the call in the probe. -/
theorem callsSome_pos : callsSome cloneToCopy.targets (probe 0 5) = true := by decide

/-- `callsSome` finds no call in a program without calls. -/
theorem callsSome_neg : callsSome cloneToCopy.targets [.set 0 1, .out 0] = false := by decide

/-- `callsSome` ignores calls of untargeted instances. -/
theorem callsSome_neg_untargeted : callsSome cloneToCopy.targets [.call 1 1 0] = false := by
  decide

/-- `firstMatch` targets an instance matched in the list and selects the first matching
rewrite's replacement (`cloneToCopy` before `succRewrite`). -/
theorem firstMatch_pos :
    (firstMatch [cloneToCopy, succRewrite]).targets 0 = true ∧
      (firstMatch [cloneToCopy, succRewrite]).repl 0 = copyImpl :=
  ⟨rfl, rfl⟩

/-- `firstMatch` does not target an instance matched by no rewrite in the list. -/
theorem firstMatch_neg : (firstMatch [cloneToCopy]).targets 1 = false := rfl

end Toy.LawRewrite
