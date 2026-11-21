import DoubleFetch.Results

/-!
# Positive and negative examples for every definition

Each definition is tested on at least one instance it must admit (or one computation it must
produce) and one instance it must reject.
-/

namespace Toy.DoubleFetch

/-! ### `Prog.exec`, `Prog.eval`, `Prog.obs`: time advances by one per access -/

/-- Read address `0` twice; return both bytes. -/
def readTwice : Prog 1 (Byte × Byte) := .read 0 fun a => .read 0 fun b => .ret (a, b)

/-- The writer showing `7` at time `0` and `9` afterwards. -/
def sevenNine : Adversary 1 := fun t _ => if t = 0 then 7 else 9

/-- Positive: the second access observes the state at time `1`. -/
theorem exec_example : readTwice.exec sevenNine = (7, 9) := by decide

/-- Negative: `exec` against a changing writer is not the private-memory result on the initial
state. -/
theorem exec_ne_eval_example : readTwice.exec sevenNine ≠ readTwice.eval (sevenNine 0) := by
  decide

/-- Positive: private-memory evaluation sees one state throughout. -/
theorem eval_example : readTwice.eval (fun _ => 7) = (7, 7) := by decide

/-- Positive: observable-read semantics records both reads with the bytes seen. -/
theorem obs_example :
    (readTwice.obs sevenNine).1.length = 2 ∧ (readTwice.obs sevenNine).2 = (7, 9) := by
  constructor <;> decide

/-! ### `SingleRead` and `NoSnap` -/

/-- Positive: the single-read length parser. Negative: the double-fetch length parser. -/
theorem singleRead_examples : SingleRead (lenOnce 0 4) ∧ ¬ SingleRead (lenReread 0 4) := by
  refine ⟨(lenOnce_singleRead_implements 0 4).1, fun h => ?_⟩
  obtain ⟨_, h2⟩ := h
  have := h2 0
  simp [lenCheck, CheckUse.pure, Prog.SingleReadFrom] at this

/-- Negative: reading address `0` and then snapshotting reads address `0` twice. -/
theorem singleRead_read_then_snap_rejected :
    ¬ SingleRead (.read 0 fun _ => .snap fun s => .ret (s 0) : Prog 1 Byte) := by
  intro h
  obtain ⟨_, h2⟩ := h
  obtain ⟨h3, _⟩ := h2 0
  simpa using h3 0

/-- Positive: `readFst` uses one-byte reads and no snapshot. Negative: a snapshot parser. -/
theorem noSnap_examples : readFst.NoSnap ∧ ¬ (snapParse pairSpec).NoSnap :=
  ⟨fun _ => trivial, fun h => h⟩

/-! ### `Prog.assemble` -/

/-- Positive: bytes as read at the read addresses, the filler elsewhere. -/
theorem assemble_example :
    (Prog.read 0 fun a => .ret a : Prog 2 Byte).assemble (fun _ => reg2 5 6) (fun _ => 3) 0 = 5 ∧
      (Prog.read 0 fun a => .ret a : Prog 2 Byte).assemble (fun _ => reg2 5 6) (fun _ => 3) 1
        = 3 := by
  constructor <;> decide

/-! ### Robustness notions -/

/-- `RSafe`: positive `lenOnce`, negative `lenReread` (for `cap = 4`). -/
theorem rsafe_examples :
    RSafe (CopyInBounds 4) (lenOnce 0 4) ∧ ¬ RSafe (CopyInBounds 4) (lenReread 0 4) :=
  ⟨(lenOnce_rsafe_rvalid 0 4).1, (lenReread_not_rsafe_not_rvalid 0 4 (by decide)).1⟩

/-- `RValid`: positive the byte-copy parser, negative `lenReread` (for `cap = 4`). -/
theorem rvalid_examples :
    RValid pairSpec (copyParse pairSpec) ∧ ¬ RValid (lpParse 4) (lenReread 0 4) :=
  ⟨(copyParse_exec_eq_diagonal_and_rvalid pairSpec).2,
    (lenReread_not_rsafe_not_rvalid 0 4 (by decide)).2⟩

/-- `RState`: positive the snapshot parser, negative the byte-copy parser. -/
theorem rstate_examples :
    RState pairSpec (snapParse pairSpec) ∧ ¬ RState pairSpec (copyParse pairSpec) :=
  ⟨(snapParse_exec_eq_and_rstate pairSpec).2, copyParse_pair_torn_not_rstate.2.2⟩

/-- `RStateUnder` with the trivial constraint is `RState`. -/
theorem rstateUnder_true_iff {n : Nat} {α : Type} (spec : Region n → α) (p : Prog n α) :
    RStateUnder (fun _ => True) spec p ↔ RState spec p :=
  ⟨fun h adv => h adv trivial, fun h adv _ => h adv⟩

/-- `RStateUnder`: positive the seqlock reader under one-step protocol writers, negative under
two-step protocol writers. -/
theorem rstateUnder_examples :
    RStateUnder OneStepVersionWriter seqSpec seqlockReader ∧
      ¬ RStateUnder TwoStepVersionWriter seqSpec seqlockReader :=
  ⟨seqlock_rstateUnder_oneStepVersionWriter,
    seqlock_not_rstateUnder_twoStepVersionWriter.2.2.2.2⟩

/-- `Implements`: positive `lenOnce 0 4` implements `lpParse 4`; negative it does not implement
`lpParse 5` (they differ on the byte `5`). -/
theorem implements_examples :
    Implements (lenOnce 0 4) (lpParse 4) ∧ ¬ Implements (lenOnce 0 4) (lpParse 5) := by
  refine ⟨(lenOnce_singleRead_implements 0 4).2, fun h => ?_⟩
  have := h (fun _ => 5)
  revert this
  decide

/-- `PrivRefines`: positive rematerialization; negative two length parsers with different
capacities. -/
theorem privRefines_examples :
    PrivRefines (lenReread 0 4) (lenOnce 0 4) ∧ ¬ PrivRefines (lenOnce 0 5) (lenOnce 0 4) := by
  refine ⟨remat_privRefines_compile _, fun h => ?_⟩
  have := h (fun _ => 5)
  revert this
  decide

/-- `ObsRefines`: positive every program refines itself; negative rematerialization (which
differs from the original as a parser). -/
theorem obsRefines_examples :
    ObsRefines (lenOnce 0 4) (lenOnce 0 4) ∧ ¬ ObsRefines (lenReread 0 4) (lenOnce 0 4) := by
  refine ⟨fun adv => ⟨adv, rfl⟩, fun h => ?_⟩
  have e := (obsRefines_iff_eq _ _).mp h
  exact singleRead_examples.2 (e ▸ singleRead_examples.1)

/-- `RobustRefines`: positive the re-read-and-compare parser robustly refines the single-read
`bool` parser (a distinct parser); negative rematerialization of the length check. -/
theorem robustRefines_examples :
    RobustRefines rereadCompare (tagOnce 0) ∧ ¬ RobustRefines (lenReread 0 4) (lenOnce 0 4) :=
  ⟨robustRefines_rereadCompare_tagOnce_not_preserves_rstate.2.1,
    (remat_lenCheck_privRefines_not_robustRefines 0 4 (by decide)).2⟩

/-! ### Specs and safety predicates -/

/-- `lpParse`: accepts a length within capacity, rejects one above. -/
theorem lpParse_examples : lpParse 4 (fun _ : Fin 1 => 3) = some 3 ∧
    lpParse 4 (fun _ : Fin 1 => 5) = none := by
  constructor <;> decide

/-- `CopyInBounds`: positive `some 3` and `none` for capacity `4`; negative `some 5`. -/
theorem copyInBounds_examples :
    CopyInBounds 4 (some 3) ∧ CopyInBounds 4 none ∧ ¬ CopyInBounds 4 (some 5) := by
  refine ⟨?_, trivial, ?_⟩ <;> simp [CopyInBounds]

/-- `boolParse`: accepts `1`, rejects `2`. -/
theorem boolParse_examples : boolParse (fun _ : Fin 1 => 1) = some 1 ∧
    boolParse (fun _ : Fin 1 => 2) = none := by
  constructor <;> decide

/-- `ValidBoolOut`: positive `some 1`; negative `some 2`. -/
theorem validBoolOut_examples : ValidBoolOut (some 1) ∧ ¬ ValidBoolOut (some 2) := by
  constructor <;> simp [ValidBoolOut]

/-- `ckParse`: accepts `(1, 2, 3)`, rejects `(1, 2, 4)`; the checksum wraps: `(2, 255, 1)` is
accepted. -/
theorem ckParse_examples : ckParse (reg3 1 2 3) = some (1, 2) ∧ ckParse (reg3 1 2 4) = none ∧
    ckParse (reg3 2 255 1) = some (2, 255) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- `NoByteDeterminesOutput`: positive the pair spec, negative the first-byte spec. -/
theorem noByteDeterminesOutput_examples :
    NoByteDeterminesOutput pairSpec ∧ ¬ NoByteDeterminesOutput fstSpec := by
  refine ⟨pairSpec_noByteDeterminesOutput, fun h => ?_⟩
  obtain ⟨σ, h1, h2⟩ := h 0 0 0
  exact h2 h1

/-- `NoByteDeterminesOutput` is not implied by "depends on two addresses": `seqSpec` depends on
all three bytes, yet an odd version byte alone determines the output `none`. -/
theorem seqSpec_not_noByteDeterminesOutput : ¬ NoByteDeterminesOutput seqSpec := by
  intro h
  obtain ⟨σ, h1, h2⟩ := h 0 1 none
  apply h2
  simp [seqSpec, h1]

/-- `HasUndeterminedState`: positive the pair spec, the seqlock spec and the tagged-value spec;
negative the first-byte spec. -/
theorem hasUndeterminedState_examples :
    HasUndeterminedState pairSpec ∧ HasUndeterminedState seqSpec ∧
      HasUndeterminedState (viewSpec 1) ∧ ¬ HasUndeterminedState fstSpec :=
  ⟨pairSpec_hasUndeterminedState, seqSpec_hasUndeterminedState, viewSpec_hasUndeterminedState 1,
    readFst_rstate_counterexample.1⟩

/-- `andSpec`: `true` exactly on `(1, 1)`. -/
theorem andSpec_examples : andSpec (reg2 1 1) = true ∧ andSpec (reg2 1 0) = false ∧
    andSpec (reg2 0 1) = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### Version protocol -/

/-- `VersionStep`: positive beginning a write; negative changing data under an even version. -/
theorem versionStep_examples :
    VersionStep (reg3 0 5 5) (reg3 1 5 5) ∧ ¬ VersionStep (reg3 0 5 5) (reg3 0 6 6) := by
  refine ⟨Or.inr (Or.inl ⟨by decide, by decide, by decide, by decide⟩), fun h => ?_⟩
  rcases h with h | ⟨_, h, _, _⟩ | ⟨h, _⟩ | ⟨h, _, _, _⟩
  · have := congrFun h 1; revert this; decide
  · revert h; decide
  · revert h; decide
  · revert h; decide

/-- `OneStepVersionWriter`: positive the writer that never writes; negative `seqTwoStepAdv` (two
protocol steps between two accesses). -/
theorem oneStepVersionWriter_examples :
    OneStepVersionWriter (Adversary.const (reg3 0 5 5)) ∧ ¬ OneStepVersionWriter seqTwoStepAdv :=
  ⟨fun _ => Or.inl rfl, seqlock_not_rstateUnder_twoStepVersionWriter.2.1⟩

/-- `TwoStepVersionWriter`: positive `seqTwoStepAdv`; negative `seqRogueAdv` (it changes the data
under an even version). -/
theorem twoStepVersionWriter_examples :
    TwoStepVersionWriter seqTwoStepAdv ∧ ¬ TwoStepVersionWriter seqRogueAdv := by
  refine ⟨seqlock_not_rstateUnder_twoStepVersionWriter.1, fun h => ?_⟩
  obtain ⟨mid, h1, h2⟩ := h 0
  have hv1 := versionStep_val _ _ h1
  have hv2 := versionStep_val _ _ h2
  have hs0 : (seqRogueAdv 0 0).val = 0 := rfl
  have hs1 : (seqRogueAdv 1 0).val = 0 := rfl
  rw [hs0] at hv1
  rw [hs1] at hv2
  have hmid0 : (mid 0).val = 0 := by
    have bm := (mid 0).isLt
    rcases hv1 with hv1 | hv1 <;> rcases hv2 with hv2 | hv2 <;> omega
  have emid : mid = seqRogueAdv 0 :=
    versionStep_eq_of_even_of_same _ _ h1 (by decide) hmid0
  rw [emid] at h2
  have e1 : seqRogueAdv 1 = seqRogueAdv 0 :=
    versionStep_eq_of_even_of_same _ _ h2 (by decide) (by decide)
  have := congrFun e1 1
  revert this
  decide

/-- `VersionPath`: positive beginning a write is a path with one increment; negative a data change
under an even version is not a path without increments. -/
theorem versionPath_examples :
    VersionPath 1 (reg3 0 5 5) (reg3 1 5 5) ∧ ¬ VersionPath 0 (reg3 0 5 5) (reg3 0 6 6) := by
  refine ⟨VersionPath.bump (s' := reg3 1 5 5) (Or.inr (Or.inl ⟨by decide, rfl, rfl, rfl⟩)) rfl
    (VersionPath.refl _), fun h => ?_⟩
  have e := versionPath_zero_eq h rfl (by decide)
  have := congrFun e 1
  revert this
  decide

/-- `IncrementBoundedWriter`: positive the writer that never writes (bound `1`); negative
`seqWrapAdv` at bound `256`. -/
theorem incrementBoundedWriter_examples :
    IncrementBoundedWriter 1 (Adversary.const (reg3 0 5 5)) ∧
      ¬ IncrementBoundedWriter 256 seqWrapAdv :=
  ⟨⟨0, 0, 0, VersionPath.refl _, VersionPath.refl _, VersionPath.refl _, by decide⟩,
    seqlock_accepted_torn_of_256Increments.2.1⟩

/-! ### Tagged values and views -/

/-- `ValidE`: positive `(0, 7)` and `(1, 1)`; negative `(1, 2)` and `(2, 0)`. -/
theorem validE_examples :
    ValidE 0 7 ∧ ValidE 1 1 ∧ ¬ ValidE 1 2 ∧ ¬ ValidE 2 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `ViewOK`: positive `some [(0, 0)]` and `none`; negative `some [(1, 2)]`. -/
theorem viewOK_examples :
    ViewOK (some [(0, 0)]) ∧ ViewOK none ∧ ¬ ViewOK (some [(1, 2)]) := by
  refine ⟨?_, trivial, ?_⟩
  · intro x hx
    simp at hx
    rw [hx]
    decide
  · intro h
    have := h (1, 2) (by simp)
    revert this
    decide

/-- Positive: with no writer the view program returns `k` copies of the validated value. -/
theorem viewProg_example : (viewProg 2).eval (reg2 1 0) = some [(1, 0), (1, 0)] := by decide

/-- `viewSpec`: positive `(1, 0)` gives two decodes; negative the invalid `(1, 2)` gives the error
result. -/
theorem viewSpec_examples :
    viewSpec 2 (reg2 1 0) = some [(1, 0), (1, 0)] ∧ viewSpec 2 (reg2 1 2) = none := by
  constructor <;> decide

/-- `copyOutProg`: against the writer that never writes it returns the private-memory result;
it reads address `0` then address `1`, one byte at a time. -/
theorem copyOutProg_example :
    (copyOutProg 1).exec (Adversary.const (reg2 1 1)) = some [(1, 1)] := by
  rw [Prog.exec_const]; decide

/-- `ownedProg`: positive the valid `(1, 1)` gives one decode; negative the invalid tag `2` gives
the error result after a single access. -/
theorem ownedProg_examples :
    (ownedProg 1).eval (reg2 1 1) = some [(1, 1)] ∧ (ownedProg 1).eval (reg2 2 0) = none ∧
      ((ownedProg 1).obs (Adversary.const (reg2 2 0))).1.length = 1 := by
  refine ⟨by decide, by decide, ?_⟩
  rw [(copyOutProg_ownedProg_access_counts 1 _).2]
  decide

/-- `dataDepProg`: the second address depends on the first byte. -/
theorem dataDepProg_examples :
    dataDepProg.eval (reg3 0 7 9) = 7 ∧ dataDepProg.eval (reg3 1 7 9) = 9 := by
  constructor <;> decide

end Toy.DoubleFetch
