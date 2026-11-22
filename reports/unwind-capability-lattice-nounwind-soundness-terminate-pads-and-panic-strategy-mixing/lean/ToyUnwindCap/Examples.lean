import ToyUnwindCap.Decide
import ToyUnwindCap.Results
import ToyUnwindCap.ChainResults

/-!
# Concrete settings, programs and chains; definition examples

Every theorem in this file is fully proved, by kernel evaluation (`decide`) of concrete
classifications, executable checkers (`ToyUnwindCap.Decide`) and runs, or from proved results.
-/

namespace Toy.UnwindCap

/-! ## Settings and static facts -/

/-- A crate with strategy `unwind` and panic-in-drop `unwind`. -/
def unwindCfg : CrateCfg := ⟨.unwind, .unwind⟩

/-- A crate with strategy `unwind` and panic-in-drop `abort`. -/
def pidAbortCfg : CrateCfg := ⟨.unwind, .abort⟩

/-- A Rust-defined `extern "C"` function (`c` ABI, not foreign). -/
def cFn : FnInfo := ⟨.c, false, false, false⟩

/-- A foreign `"C-unwind"` import. -/
def foreignCUnwind : FnInfo := ⟨.cUnwind, true, false, false⟩

/-- A foreign `"C"` import. -/
def foreignC : FnInfo := ⟨.c, true, false, false⟩

/-- A Rust function with the never-unwind attribute. -/
def attrFn : FnInfo := ⟨.rust, false, true, false⟩

/-! ## Example programs -/

/-- One `abort` crate; function 0 (Rust) calls function 1, a foreign `"C-unwind"` import that
may unwind, through a terminate pad; panic handler `abort`. -/
def progAbortImportPadded : Prog :=
  ⟨[abortCfg], [⟨rustInfo, 0, [.call 1 .terminate], false⟩, ⟨foreignCUnwind, 0, [], true⟩],
    .abort⟩

/-- As `progAbortImportPadded`, but the call is a plain call. -/
def progAbortImportPlain : Prog :=
  ⟨[abortCfg], [⟨rustInfo, 0, [.call 1 .none], false⟩, ⟨foreignCUnwind, 0, [], true⟩], .abort⟩

/-- One `unwind` crate; function 0 (a Rust-defined `extern "C"` function, non-unwinding) calls
function 1 (Rust, which panics) with a plain call; panic handler `unwind`. -/
def progPlainCallFromNounwind : Prog :=
  ⟨[unwindCfg], [⟨cFn, 0, [.call 1 .none], false⟩, ⟨rustInfo, 0, [.raise .none], false⟩],
    .unwind⟩

/-- One `unwind` crate declaring a foreign `"C"` import that unwinds. -/
def progThrowingC : Prog := ⟨[unwindCfg], [⟨foreignC, 0, [], true⟩], .unwind⟩

/-- Crate 0 uses `abort`, crate 1 uses `unwind`; function 0 (crate 0, Rust) calls function 1
(crate 1, Rust, which panics) with a plain call; panic handler `unwind`. -/
def progAbortCallsUnwind : Prog :=
  ⟨[abortCfg, unwindCfg],
    [⟨rustInfo, 0, [.call 1 .none], false⟩, ⟨rustInfo, 1, [.raise .none], false⟩], .unwind⟩

/-- A foreign `"C-unwind"` function flagged as drop glue, in a crate with panic-in-drop
`abort`, that unwinds. -/
def progForeignGlue : Prog := ⟨[pidAbortCfg], [⟨⟨.cUnwind, true, false, true⟩, 0, [], true⟩], .unwind⟩

/-- The drop-glue mismatch: the caller's crate has panic-in-drop `abort`, the glue instance's
crate has panic-in-drop `unwind`, the call is plain, and the glue panics. -/
def progGlueMismatch : Prog := glueProg pidAbortCfg unwindCfg .none [.raise .none]

/-- Mixed strategies under the linking restriction: crate 0 uses `abort`, crate 1 uses
`unwind`. Function 0 (crate 0, Rust) calls function 2 (a foreign `"C-unwind"` import declared
in crate 0, which may unwind) through a terminate pad, then calls function 3 (crate 1, Rust,
which panics) with a plain call; function 1 (crate 1, Rust) calls function 0 with a plain call.
Panic handler `abort`. -/
def progMixedLinkOK : Prog :=
  ⟨[abortCfg, unwindCfg],
    [⟨rustInfo, 0, [.call 2 .terminate, .call 3 .none], false⟩,
      ⟨rustInfo, 1, [.call 0 .none], false⟩, ⟨foreignCUnwind, 0, [], true⟩,
      ⟨rustInfo, 1, [.raise .none], false⟩], .abort⟩

/-- One `unwind` crate: function 0 calls function 1 inside a catch pad; function 1 calls
function 2 with a cleanup pad dropping local 7; function 2 panics. Panic handler `unwind`. -/
def progUnwindCatch : Prog :=
  ⟨[unwindCfg],
    [⟨rustInfo, 0, [.call 1 .catchPad], false⟩, ⟨rustInfo, 0, [.call 2 (.cleanup [7])], false⟩,
      ⟨rustInfo, 0, [.raise .none], false⟩], .unwind⟩

/-! ## Examples: precedence functions -/

/-- `stdCanUnwind` admits the intended "may unwind" verdicts: a Rust function in an `unwind`
crate, and a foreign `"C-unwind"` import seen from an `abort` crate. -/
theorem stdCanUnwind_positive :
    stdCanUnwind unwindCfg rustInfo = true ∧ stdCanUnwind abortCfg foreignCUnwind = true := by
  decide

/-- `stdCanUnwind` returns the intended "non-unwinding" verdicts: a Rust-defined
`extern "C-unwind"` function in an `abort` crate, a Rust-defined `extern "C"` function, drop
glue under panic-in-drop `abort`, and a function with the never-unwind attribute. -/
theorem stdCanUnwind_negative :
    stdCanUnwind abortCfg rustDefinedCUnwind = false ∧ stdCanUnwind unwindCfg cFn = false ∧
    stdCanUnwind pidAbortCfg glueInfo = false ∧ stdCanUnwind unwindCfg attrFn = false := by
  decide

/-- `abiFirstCanUnwind` classifies a Rust-defined `extern "C-unwind"` function in an `abort`
crate as possibly unwinding, and a Rust function in an `abort` crate as non-unwinding. -/
theorem abiFirstCanUnwind_examples :
    abiFirstCanUnwind abortCfg rustDefinedCUnwind = true ∧
    abiFirstCanUnwind abortCfg rustInfo = false := by
  decide

/-- `abortAllCanUnwind` classifies a foreign `"C-unwind"` import seen from an `abort` crate as
non-unwinding (the mistake), and a Rust function in an `unwind` crate as possibly unwinding. -/
theorem abortAllCanUnwind_examples :
    abortAllCanUnwind abortCfg foreignCUnwind = false ∧
    abortAllCanUnwind unwindCfg rustInfo = true := by
  decide

/-! ## Examples: semantics -/

/-- A run of `progUnwindCatch`: the panic in function 2 unwinds through function 1, whose
cleanup pad drops local 7, and is caught by function 0, which then returns. -/
theorem exec_progUnwindCatch :
    Exec stdCanUnwind progUnwindCatch 0 [.drop 1 7, .caught 0] .ret := ⟨4, by decide⟩

/-- Function 1 of `progUnwindCatch` unwinds after dropping local 7. -/
theorem exec_progUnwindCatch_fn1 :
    Exec stdCanUnwind progUnwindCatch 1 [.drop 1 7] .unwind := ⟨3, by decide⟩

/-- The terminate pad of `progAbortImportPadded` aborts when the import unwinds. -/
theorem exec_progAbortImportPadded_abort :
    Exec stdCanUnwind progAbortImportPadded 0 [] .abort := ⟨2, by decide⟩

/-- The plain call of `progAbortImportPlain` is undefined behaviour when the import unwinds. -/
theorem exec_progAbortImportPlain_ub :
    Exec stdCanUnwind progAbortImportPlain 0 [] .ub := ⟨2, by decide⟩

/-! ## Examples: hypotheses -/

theorem enforced_progAbortImportPadded : Enforced stdCanUnwind progAbortImportPadded :=
  enforced_of_enforcedB _ _ (by decide)

/-- `progAbortImportPlain` is not `Enforced` under `stdCanUnwind`: its function 0 is
non-unwinding and calls a possibly-unwinding import without a stopping pad. -/
theorem not_enforced_progAbortImportPlain : ¬ Enforced stdCanUnwind progAbortImportPlain := by
  intro h
  have := (h 0 (by decide) (by decide)).2 1 .none (by decide) (by decide)
  exact absurd this (by decide)

theorem foreignCovered_progAbortImportPadded :
    ForeignCovered stdCanUnwind progAbortImportPadded :=
  foreignCovered_of_foreignCoveredB _ _ (by decide)

/-- `progThrowingC` is not `ForeignCovered` under `stdCanUnwind`: its `"C"` import unwinds and is
classified as non-unwinding. -/
theorem not_foreignCovered_progThrowingC : ¬ ForeignCovered stdCanUnwind progThrowingC := by
  intro h
  exact absurd (h 0 (by decide) (by decide)) (by decide)

theorem siteAgreement_progUnwindCatch : SiteAgreement stdCanUnwind progUnwindCatch :=
  siteAgreement_of_siteAgreementB _ _ (by decide)

/-- `progAbortCallsUnwind` violates `SiteAgreement` under `stdCanUnwind`: the `abort` crate
classifies the callee as non-unwinding, the callee's `unwind` crate does not. -/
theorem not_siteAgreement_progAbortCallsUnwind :
    ¬ SiteAgreement stdCanUnwind progAbortCallsUnwind := by
  intro h
  exact absurd (h 0 1 .none (by decide) (by decide) (by decide) (by decide)) (by decide)

theorem foreignHonest_progAbortImportPadded : ForeignHonest progAbortImportPadded :=
  foreignHonest_of_foreignHonestB _ (by decide)

theorem not_foreignHonest_progThrowingC : ¬ ForeignHonest progThrowingC := by
  intro h
  exact absurd (h 0 (by decide) (by decide)).1 (by decide)

theorem foreignNotGlue_progAbortImportPadded : ForeignNotGlue progAbortImportPadded :=
  foreignNotGlue_of_foreignNotGlueB _ (by decide)

theorem not_foreignNotGlue_progForeignGlue : ¬ ForeignNotGlue progForeignGlue := by
  intro h
  exact absurd (h 0 (by decide)) (by decide)

/-- `progUnwindCatch` is potentially unwinding (it uses the `unwind` handler). -/
theorem potentiallyUnwinding_progUnwindCatch : PotentiallyUnwinding progUnwindCatch :=
  Or.inl rfl

/-- An `unwind`-strategy crate calling a `"C-unwind"` function makes an artifact with the
`abort` handler potentially unwinding. -/
theorem potentiallyUnwinding_unwindCrateCallsCUnwind :
    PotentiallyUnwinding
      ⟨[unwindCfg], [⟨rustInfo, 0, [.call 1 .terminate], false⟩, ⟨foreignCUnwind, 0, [], true⟩],
        .abort⟩ :=
  Or.inr ⟨0, 1, .terminate, by decide, by decide, by decide, by decide⟩

theorem not_potentiallyUnwinding_progMixedLinkOK : ¬ PotentiallyUnwinding progMixedLinkOK :=
  not_potentiallyUnwinding_of_B _ (by decide)

theorem linkOK_progMixedLinkOK : LinkOK progMixedLinkOK :=
  linkOK_of_notPotentiallyUnwindingB _ (by decide)

/-- `progAbortCallsUnwind` violates `LinkOK`: it uses the `unwind` handler but contains an
`abort` crate. -/
theorem not_linkOK_progAbortCallsUnwind : ¬ LinkOK progAbortCallsUnwind := by
  intro h
  exact absurd (h (Or.inl rfl) abortCfg (by decide)) (by decide)

theorem glueAgreement_matching : GlueAgreement (glueProg pidAbortCfg pidAbortCfg .none []) :=
  glueAgreement_of_glueAgreementB _ (by decide)

theorem not_glueAgreement_progGlueMismatch : ¬ GlueAgreement progGlueMismatch := by
  intro h
  exact absurd (h 0 1 .none (by decide) (by decide) (by decide) (by decide) (by decide))
    (by decide)

/-- `PrecForeignSound` admits `stdCanUnwind` and rejects `abortAllCanUnwind`. -/
theorem precForeignSound_examples :
    PrecForeignSound stdCanUnwind ∧ ¬ PrecForeignSound abortAllCanUnwind :=
  ⟨std_and_abiFirst_foreignSound_but_differ.1, abortAllCanUnwind_not_foreignSound⟩

/-! ## Examples: codegen and backends -/

/-- `insertPads` adds the terminate pad to `progAbortImportPlain`. -/
theorem insertPads_progAbortImportPlain :
    insertPads stdCanUnwind progAbortImportPlain = progAbortImportPadded := by decide

/-- `insertPads` leaves `progAbortCallsUnwind` unchanged: the caller's crate classifies the
callee as non-unwinding, so no pad is inserted. -/
theorem insertPads_progAbortCallsUnwind :
    insertPads stdCanUnwind progAbortCallsUnwind = progAbortCallsUnwind := by decide

/-- Backend assignment compiling function 0 with `pads = none` and every other function with
`pads = full`. -/
def padsNoneAt0 : Nat → Pads := fun g => if g = 0 then .none else .full

/-- `withPads` removes the landing pads of function 0 of `progUnwindCatch` (compiled with
`pads = none`) and leaves functions 1 and 2 (compiled with `pads = full`) unchanged. -/
theorem withPads_progUnwindCatch :
    (progUnwindCatch.withPads padsNoneAt0).fns.head? =
      some ⟨rustInfo, 0, [.call 1 .none], false⟩ ∧
    (progUnwindCatch.withPads padsNoneAt0).fns.tail = progUnwindCatch.fns.tail := by decide

/-- An ordinary program with the `abort` panic handler whose Rust function contains a panic
point without a landing pad. -/
def progAbortHandlerRaisePlain : Prog :=
  ⟨[abortCfg], [⟨rustInfo, 0, [.raise .none], false⟩], .abort⟩

/-- `Enforced` does not constrain panic points under the `abort` handler: it admits
`progAbortHandlerRaisePlain` (handler `abort`), and rejects the same program with the handler
changed to `unwind`. -/
theorem enforced_handler_examples :
    Enforced stdCanUnwind progAbortHandlerRaisePlain ∧
    ¬ Enforced stdCanUnwind { progAbortHandlerRaisePlain with handler := .unwind } := by
  refine ⟨enforced_of_enforcedB _ _ (by decide), fun h => ?_⟩
  exact absurd ((h 0 (by decide) (by decide)).1 rfl .none (by decide)) (by decide)

/-- `padStmt` on panic points: under the `abort` handler a plain panic point is unchanged; under the
`unwind` handler a panic point with a cleanup pad gets a terminate pad, and its drop list is
lost. -/
theorem padStmt_raise_examples :
    padStmt stdCanUnwind progAbortHandlerRaisePlain 0 (.raise .none) = .raise .none ∧
    padStmt stdCanUnwind progPlainCallFromNounwind 0 (.raise (.cleanup [7])) =
      .raise .terminate := by
  decide

/-- `GlueSiteSound` holds when both crates have panic-in-drop `abort` and fails for the
mismatch configuration. -/
theorem glueSiteSound_examples :
    GlueSiteSound pidAbortCfg pidAbortCfg .none ∧ ¬ GlueSiteSound pidAbortCfg unwindCfg .none := by
  refine ⟨(glueSiteSound_iff _ _ _).2 (fun _ => Or.inl (by decide)), fun h => ?_⟩
  rcases (glueSiteSound_iff _ _ _).1 h (by decide) with h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-! ## Examples: chain model -/

/-- The identity ABI. -/
def idCodec : AbiCodec := ⟨id, id⟩

/-- A self-consistent ABI that encodes `v` as `v + 1` and decodes with truncated subtraction. -/
def shiftCodec : AbiCodec := ⟨fun v => v + 1, fun w => w - 1⟩

/-- An ABI whose encoding keeps the value modulo 256 (floor-division remainder) and whose
decoding is the identity. -/
def truncCodec : AbiCodec := ⟨fun v => v % 256, id⟩

theorem lawful_examples : idCodec.Lawful ∧ shiftCodec.Lawful ∧ ¬ truncCodec.Lawful := by
  refine ⟨fun _ => rfl, fun v => by simp [shiftCodec], fun h => ?_⟩
  have := h 300
  simp [truncCodec] at this

theorem conforms_examples : Conforms idCodec idCodec ∧ ¬ Conforms shiftCodec idCodec := by
  refine ⟨⟨rfl, rfl⟩, fun h => ?_⟩
  have := congrFun h.1 0
  simp [shiftCodec, idCodec] at this

/-- In the chain `[⟨full, cleanup [1]⟩, ⟨none, none⟩, ⟨full, catchPad⟩]` the compiled and
specified unwinds agree. -/
theorem unwind_chain_example :
    compUnwind [⟨.full, .cleanup [1]⟩, ⟨.none, .none⟩, ⟨.full, .catchPad⟩] =
      ([.drop 0 1, .caught 2], .caught 2) ∧
    specUnwind [⟨.full, .cleanup [1]⟩, ⟨.none, .none⟩, ⟨.full, .catchPad⟩] =
      ([.drop 0 1, .caught 2], .caught 2) := by decide

/-- A `pads = none` frame with a cleanup pad skips its destructor in the compiled unwind. -/
theorem unwind_chain_skip_example :
    compUnwind [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] = ([.caught 1], .caught 1) ∧
    specUnwind [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] = ([.drop 0 1, .caught 1], .caught 1) := by
  decide

theorem obligationsFull_examples :
    ObligationsFull [⟨.full, .cleanup [1]⟩, ⟨.none, .none⟩, ⟨.full, .catchPad⟩, ⟨.none, .catchPad⟩] ∧
    ¬ ObligationsFull [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] := by
  refine ⟨?_, ?_⟩ <;> simp [ObligationsFull, Action.obligation, Action.Stops]

theorem shielded_examples :
    Shielded [⟨.full, .catchPad⟩, ⟨.none, .none⟩] ∧ ¬ Shielded [⟨.none, .none⟩] ∧
    TerminateShielded [⟨.full, .none⟩, ⟨.full, .terminate⟩, ⟨.none, .none⟩] ∧
    ¬ TerminateShielded [⟨.full, .catchPad⟩, ⟨.none, .none⟩] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Shielded, TerminateShielded, Action.Stops]

/-- `NoReachedNoneTerminate` admits a chain whose `pads = none` terminate frame lies after a
stopping frame, and rejects a chain whose first frame is a `pads = none` terminate frame. -/
theorem noReachedNoneTerminate_examples :
    NoReachedNoneTerminate [⟨.full, .catchPad⟩, ⟨.none, .terminate⟩] ∧
    ¬ NoReachedNoneTerminate [⟨.none, .terminate⟩, ⟨.full, .terminate⟩] := by
  refine ⟨⟨by decide, fun h => by cases h⟩, fun h => h.1 rfl rfl⟩

theorem sameShape_examples :
    SameShape [⟨.full, .catchPad⟩, ⟨.none, .none⟩] [⟨.full, .catchPad⟩, ⟨.none, .terminate⟩] ∧
    ¬ SameShape [⟨.full, .catchPad⟩] [⟨.full, .terminate⟩] := by
  refine ⟨?_, ?_⟩ <;> simp [SameShape]

end Toy.UnwindCap
