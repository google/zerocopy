import ToyTailCall.Counterexamples

/-!
# The converse of the call-site splice theorem is false (all fully proved)

An outcome other than `ub` and `stackOverflow` that the corrected call-site splice observes
need not be observed by the original program.
-/

namespace Toy.TailCall

/-- With bound `1`, the corrected call-site splice of `plainCall` returns `0` with trace
`[out 1]`, while `plainCall` itself does not (it overflows at the call). -/
theorem correctedSplice_converse_fails_plainCall :
    Observes .frameReuse (some 1) (inlineCallSite .corrected plainCall 0 0) (.returned 0)
        [.out 1] ∧
      ¬ Observes .frameReuse (some 1) plainCall (.returned 0) [.out 1] := by
  have h1 : RunsTo .frameReuse (some 1) plainCall ⟨.stackOverflow, [], 1, 0⟩ := ⟨20, by decide⟩
  have h2 : RunsTo .frameReuse (some 1) (inlineCallSite .corrected plainCall 0 0)
      ⟨.returned 0, [.out 1], 1, 0⟩ := ⟨20, by decide⟩
  refine ⟨⟨_, h2, rfl, rfl⟩, ?_⟩
  rw [observes_iff_of_runsTo h1]
  decide

/-- Unbounded, the corrected call-site splice of `borrowProg` returns `5` with an empty trace,
while `borrowProg` itself does not (it halts with `ub`). -/
theorem correctedSplice_converse_fails_borrowProg :
    Observes .frameReuse none (inlineCallSite .corrected borrowProg 0 0) (.returned 5) [] ∧
      ¬ Observes .frameReuse none borrowProg (.returned 5) [] := by
  refine ⟨correctedSplice_masks_borrow_ub_borrowProg.2, ?_⟩
  rw [observes_iff_of_runsTo borrowProg_frameReuse]
  decide

/-- The converse of `correctedCallSiteSplice_preserves_frameReuse_of_ne_ub_of_ne_stackOverflow`
is false: `borrowProg`, unbounded, with outcome `returned 5` and an empty trace, is an instance. -/
theorem correctedCallSiteSplice_converse_false :
    ¬ ∀ (p : Prog) (ci k : Nat) (D : Option Nat) (o : Outcome) (es : List Event),
        o ≠ .ub → o ≠ .stackOverflow →
        Observes .frameReuse D (inlineCallSite .corrected p ci k) o es →
          Observes .frameReuse D p o es := by
  intro h
  exact correctedSplice_converse_fails_borrowProg.2
    (h borrowProg 0 0 none (.returned 5) [] (by decide) (by decide)
      correctedSplice_converse_fails_borrowProg.1)

end Toy.TailCall
