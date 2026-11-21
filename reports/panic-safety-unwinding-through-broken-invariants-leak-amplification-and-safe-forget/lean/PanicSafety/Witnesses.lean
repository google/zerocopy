import PanicSafety.Forget

/-!
# Concrete runs of `truncateLate` and of the leak-amplified drain

Three companion facts. `truncateLate_sites_destructor` and `truncateLate_dtorPanic_unwound`
state the site structure and the destructor-panic run used in the proof of
`truncateLate_counterexample`; `leakAmplifiedDrain_forgetGuard_leaks` exhibits a client run of
the leak-amplified drain that leaks a value. None of them changes a definition or another
statement.
-/

namespace Toy.PanicSafety

/-- Every user-code site that `truncateLate` reaches, from every state (not only states
satisfying `Inv`) under every callback table and every destructor table, is an
element-destructor site. In particular `truncateLate` reaches no callback site, so
`CallbackSitesDropSafe truncateLate` holds vacuously. -/
theorem truncateLate_sites_destructor (cb : Callback) (dt : DtorTable) (m : Mem) :
    ∀ s ∈ sites cb dt truncateLate m, s.kind = .destructor := by
  intro s hs
  unfold sites at hs
  rcases hlen : m.len with _ | k
  · simp [exec, truncateLate, hlen] at hs
  · simp only [exec, truncateLate, hlen] at hs
    split at hs
    · split at hs
      · simp at hs
      · split at hs
        · simp only [List.mem_singleton] at hs
          subst hs
          rfl
        · simp only [List.mem_cons] at hs
          rcases hs with hs | hs
          · subst hs
            rfl
          · simp at hs
    · simp at hs

/-- The destructor-panic run of `truncateLate`: on the one-element container `ceMem1`
(which satisfies `Inv`) with the destructor table `dtPanicsOn0`, under `unwind` and under
every callback table, the run unwinds to the state with buffer `[some 0]`, `len = 1` and
drop log `[0]`. In that state `len` still covers the cell holding the dropped value `0`, and
the state violates `Inv`. -/
theorem truncateLate_dtorPanic_unwound (cb : Callback) :
    Inv ceMem1 ∧
    run .unwind cb dtPanicsOn0 truncateLate ceMem1 = .unwound ⟨[some 0], 1, [0], 0, 0⟩ ∧
    ¬ Inv ⟨[some 0], 1, [0], 0, 0⟩ :=
  ⟨by decide, rfl, by decide⟩

/-- Forgetting the guard of the leak-amplified drain can leak a value: on `ceMem1` (which
satisfies `Inv`), the client program `[.drain, .forgetGuard]` completes in the state with
buffer `[some 0]`, `len = 0` and an empty drop log, so value `0` is neither dropped nor held
by the first `len` cells, and `LeakFree ceMem1` fails for that state. -/
theorem leakAmplifiedDrain_forgetGuard_leaks :
    Inv ceMem1 ∧
    clientRun .leakAmplified [.drain, .forgetGuard] ceMem1 =
      .ok ⟨⟨[some 0], 0, [], 0, 0⟩, [], none⟩ ∧
    ¬ LeakFree ceMem1 ⟨[some 0], 0, [], 0, 0⟩ := by
  decide

end Toy.PanicSafety
