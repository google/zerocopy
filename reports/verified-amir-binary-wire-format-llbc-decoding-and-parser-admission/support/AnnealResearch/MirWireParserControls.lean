import AnnealResearch.MirWireParser

set_option Elab.async false

/-!
FE-08 and FE-09 Module 2 (`MirWireParserControls.lean`):
Discriminating negative controls for wire framing (trailing bytes), unsupported version/tag
vs. malformed input classification, integer constant truncation and float NaN bit normalization,
JSON-AST proof boundaries (duplicate object keys before JSON AST construction), exporter body
substitution / wrong-compilation binding, and self-restating exporter checks.
-/

namespace AnnealResearch.MirWireParserControls

open AnnealResearch.MirWireParser

/-- Wire packet with an appended trailing word `0` after `validPacketBytes`. -/
noncomputable def trailingBytesPacket : List Nat :=
  [1, 42, 4, 2, 1, 1, 0]

/-- Defective prefix-only parser that ignores trailing wire words after the 6-word frame. -/
noncomputable def parsePrefixOnly (bytes : List Nat) : ParseOutcome :=
  match bytes with
  | v :: owner :: locals :: tag :: arg :: u :: _ =>
    parsePacket [v, owner, locals, tag, arg, u]
  | _ => rejectedMalformed

/-- Control 1 (`FE-08`): `parsePacket` rejects `trailingBytesPacket` as `rejectedMalformed`,
whereas `parsePrefixOnly` accepts it as `validAst` and conflates it with `validPacketBytes`. -/
theorem trailing_bytes_rejected_control :
    trailingBytesPacket ≠ validPacketBytes ∧
    parsePacket trailingBytesPacket = rejectedMalformed ∧
    parsePrefixOnly trailingBytesPacket = accepted validAst ∧
    parsePrefixOnly trailingBytesPacket = parsePrefixOnly validPacketBytes := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro hEq
  have hFst : (parsePacket trailingBytesPacket).1 = (parsePacket validPacketBytes).1 :=
    congrArg (fun b => (parsePacket b).1) hEq
  exact Nat.noConfusion hFst

/-- Unsupported wire version `2 ≠ 1`. -/
noncomputable def unsupportedVersionPacket : List Nat :=
  [2, 42, 4, 2, 1, 1]

/-- Unknown opcode tag `9 ≥ 4`. -/
noncomputable def unknownOpcodePacket : List Nat :=
  [1, 42, 4, 9, 1, 1]

/-- Truncated 4-word wire frame. -/
noncomputable def truncatedPacket : List Nat :=
  [1, 42, 4, 2]

/-- Malformed 6-word frame with non-boolean unwind flag `5 ≥ 2`. -/
noncomputable def malformedUnwindPacket : List Nat :=
  [1, 42, 4, 2, 1, 5]

/-- Control 2 (`FE-08`): Unsupported version and unknown opcode tag are classified as
`rejectedUnsupportedVersionOrTag`, whereas truncated frames and invalid boolean words are
classified as `rejectedMalformed`, and the two rejection outcomes are distinct. -/
theorem unknown_tag_and_version_classified_unsupported_control :
    parsePacket unsupportedVersionPacket = rejectedUnsupportedVersionOrTag ∧
    parsePacket unknownOpcodePacket = rejectedUnsupportedVersionOrTag ∧
    parsePacket truncatedPacket = rejectedMalformed ∧
    parsePacket malformedUnwindPacket = rejectedMalformed ∧
    rejectedUnsupportedVersionOrTag ≠ rejectedMalformed := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro hEq
  have hFst : 2 = 1 := congrArg Prod.fst hEq
  exact Nat.noConfusion (Nat.succ.inj hFst)

/-- Two distinct `returnScalar` packets with constants `10` and `266` (`10 + 256`). -/
noncomputable def astConst10 : MirPacketAst :=
  (1, 42, 4, 3, 10, true)

noncomputable def astConst266 : MirPacketAst :=
  (1, 42, 4, 3, 266, true)

/-- Lossy encoder that truncates `266` to `10` (`266 mod 256`) and normalizes signaling vs.
quiet IEEE-754 NaN payload bits to a single canonical word `0x7fc00000`. -/
noncomputable def encodeLossy (ast : MirPacketAst) (_nanSignalingBit : Bool) : List Nat :=
  [ast.1, ast.2.1, ast.2.2.1, ast.2.2.2.1,
   if ast.2.2.2.2.1 == 266 then 10 else ast.2.2.2.2.1,
   0x7fc00000]

/-- Control 3 (`FE-08`): Lossy integer truncation and float NaN bit normalization collapse
distinct ASTs and bit patterns onto the same wire packet, whereas `encodePacket` preserves
them injectively. -/
theorem integer_truncation_and_float_bit_alteration_control :
    astConst10 ≠ astConst266 ∧
    encodeLossy astConst10 false = encodeLossy astConst266 true ∧
    parsePacket (encodePacket astConst10) = accepted astConst10 ∧
    parsePacket (encodePacket astConst266) = accepted astConst266 ∧
    encodePacket astConst10 ≠ encodePacket astConst266 := by
  have hNeAst : astConst10 ≠ astConst266 := by
    intro hEq
    have hBeq : (astConst10.2.2.2.2.1 == 10) = (astConst266.2.2.2.2.1 == 10) :=
      congrArg (fun a : MirPacketAst => a.2.2.2.2.1 == 10) hEq
    exact Bool.noConfusion hBeq
  refine ⟨hNeAst, rfl, rfl, rfl, ?_⟩
  intro hEncEq
  have hAcc : accepted astConst10 = accepted astConst266 :=
    congrArg parsePacket hEncEq
  exact hNeAst (Option.some.inj (congrArg Prod.snd hAcc))

/-- Raw JSON object payload `{"owner": 42, "opArg": 1, "opArg": 0}` with duplicate `"opArg"` keys. -/
noncomputable def rawDupJsonBytes : Nat × Nat × Nat :=
  (42, 1, 0)

noncomputable def parseJsonFirstKeyWins (raw : Nat × Nat × Nat) : Nat × Nat :=
  (raw.1, raw.2.1)

noncomputable def parseJsonLastKeyWins (raw : Nat × Nat × Nat) : Nat × Nat :=
  (raw.1, raw.2.2)

noncomputable def jsonTreeToAst (tree : Nat × Nat) : MirPacketAst :=
  (1, tree.1, 4, 2, tree.2, true)

noncomputable def faultingAst : MirPacketAst :=
  (1, 42, 4, 2, 0, true)

/-- Control 4 (`FE-08`): Even when `jsonTreeToAst` is proved injective from parsed JSON trees
to `MirPacketAst`, duplicate JSON keys in `rawDupJsonBytes` yield `Execution.NoUB` under
first-key-wins JSON lexing and reach UB (`¬ Execution.NoUB`) under RFC-8259 last-key-wins
JSON lexing, demonstrating that starting the proof at a parsed `Json` AST leaves
`RawBytes -> Json` outside the theorem. -/
theorem json_ast_start_leaves_bytes_to_json_unproved_control :
    (∀ t1 t2 : Nat × Nat, jsonTreeToAst t1 = jsonTreeToAst t2 → t1 = t2) ∧
    jsonTreeToAst (parseJsonFirstKeyWins rawDupJsonBytes) = validAst ∧
    jsonTreeToAst (parseJsonLastKeyWins rawDupJsonBytes) = faultingAst ∧
    AdmissibleAst faultingAst ∧
    Execution.NoUB (PacketStep (jsonTreeToAst (parseJsonFirstKeyWins rawDupJsonBytes)))
      PacketBad initPacketState ∧
    ¬ Execution.NoUB (PacketStep (jsonTreeToAst (parseJsonLastKeyWins rawDupJsonBytes)))
      PacketBad initPacketState := by
  have hInj : ∀ t1 t2 : Nat × Nat, jsonTreeToAst t1 = jsonTreeToAst t2 → t1 = t2 := by
    intro t1 t2 hEq
    exact Prod.ext (congrArg (fun a : MirPacketAst => a.2.1) hEq)
      (congrArg (fun a : MirPacketAst => a.2.2.2.2.1) hEq)
  have hAdmFault : AdmissibleAst faultingAst := ⟨⟨rfl, by decide⟩, by decide, rfl⟩
  have hNotGuard : ¬ PacketExecSafeGuard faultingAst := by
    rintro ⟨_, hNe2 | hEq1⟩
    · exact hNe2 rfl
    · exact Nat.noConfusion hEq1
  have hReachBad : Execution.Reach (PacketStep faultingAst) initPacketState (true, 2, 0) :=
    Execution.Reach.tail (Execution.Reach.refl initPacketState)
      (Or.inr ⟨rfl, hNotGuard, rfl⟩)
  have hNotNoUB : ¬ Execution.NoUB (PacketStep faultingAst) PacketBad initPacketState :=
    Execution.bad_prefix_not_noUB (Bad := PacketBad) hReachBad rfl
  exact ⟨hInj, rfl, rfl, hAdmFault, (positive_valid_packet_decoded_and_safe).2.2.2.1, hNotNoUB⟩

/-- Faulting compiler subject (`ownerId = 42`, `opArg = 0`, so `constOk = false`) and
wrong-compilation compiler subject (`ownerId = 99`). -/
noncomputable def faultingSubject : CompilerSubject :=
  (42, 4, 2, 0, true)

noncomputable def wrongOwnerSubject : CompilerSubject :=
  (99, 4, 2, 1, true)

/-- Control 5 (`FE-09`): If an unverified exporter emits `validPacketBytes` for
`faultingSubject` (body substitution) or `wrongOwnerSubject` (wrong compilation),
`parsePacket`, `AdmissibleAst`, and `Execution.NoUB` on `validAst` all succeed while
`SubjectSafe faultingSubject` is false and `ExporterCorrespondence` rejects both. -/
theorem exporter_body_substitution_and_wrong_compilation_control :
    parsePacket validPacketBytes = accepted validAst ∧
    AdmissibleAst validAst ∧
    Execution.NoUB (PacketStep validAst) PacketBad initPacketState ∧
    ¬ SubjectSafe faultingSubject ∧
    ¬ ExporterCorrespondence faultingSubject validPacketBytes ∧
    ¬ ExporterCorrespondence wrongOwnerSubject validPacketBytes := by
  have hPos := positive_valid_packet_decoded_and_safe
  have hNotSafeFault : ¬ SubjectSafe faultingSubject :=
    (json_ast_start_leaves_bytes_to_json_unproved_control).2.2.2.2.2
  refine ⟨hPos.1, hPos.2.2.1, hPos.2.2.2.1, hNotSafeFault, ?_, ?_⟩
  · intro hCorrFault
    have hTrans := end_to_end_exporter_plus_proved_parser_transfers_noUB
      faultingSubject validPacketBytes validAst hCorrFault hPos.1 hPos.2.2.1 hPos.2.2.2.1
    exact hNotSafeFault hTrans.2.2
  · intro hCorrWrong
    have hTrans := end_to_end_exporter_plus_proved_parser_transfers_noUB
      wrongOwnerSubject validPacketBytes validAst hCorrWrong hPos.1 hPos.2.2.1 hPos.2.2.2.1
    have hOwner : (validAst.2.1 == 42) = ((subjectToAst wrongOwnerSubject).2.1 == 42) :=
      congrArg (fun a : MirPacketAst => a.2.1 == 42) hTrans.1
    exact Bool.noConfusion hOwner

/-- Unverified buggy exporter that silently overwrites `opArg := 1` and `hasUnwindEdge := true`. -/
noncomputable def buggyExporter (subj : CompilerSubject) : List Nat :=
  [1, subj.1, subj.2.1, subj.2.2.1, 1, 1]

/-- A correspondence check that merely restates `buggyExporter` against itself. -/
def SelfRestatingExporterCheck (subj : CompilerSubject) (bytes : List Nat) : Prop :=
  bytes = buggyExporter subj

/-- Control 6 (`FE-09`): `SelfRestatingExporterCheck` holds trivially on `faultingSubject`
even as `buggyExporter` erases its fault and produces `validPacketBytes`, whereas the
independent `ExporterCorrespondence` obligation rejects the corrupted export. -/
theorem self_restating_exporter_check_control :
    SelfRestatingExporterCheck faultingSubject (buggyExporter faultingSubject) ∧
    parsePacket (buggyExporter faultingSubject) = accepted validAst ∧
    AdmissibleAst validAst ∧
    Execution.NoUB (PacketStep validAst) PacketBad initPacketState ∧
    ¬ SubjectSafe faultingSubject ∧
    ¬ ExporterCorrespondence faultingSubject (buggyExporter faultingSubject) := by
  have hSub := exporter_body_substitution_and_wrong_compilation_control
  exact ⟨rfl, hSub.1, hSub.2.1, hSub.2.2.1, hSub.2.2.2.1, hSub.2.2.2.2.1⟩

#print axioms trailing_bytes_rejected_control
#print axioms unknown_tag_and_version_classified_unsupported_control
#print axioms integer_truncation_and_float_bit_alteration_control
#print axioms json_ast_start_leaves_bytes_to_json_unproved_control
#print axioms exporter_body_substitution_and_wrong_compilation_control
#print axioms self_restating_exporter_check_control

end AnnealResearch.MirWireParserControls
