import AnnealResearch.Execution

set_option Elab.async false

/-!
FE-08 and FE-09 Module 1 (`MirWireParser.lean`):
Canonical fixed-tag MIR wire format specification (`encodePacket`), total untrusted parser
(`parsePacket`), round-trip completeness, parser soundness and injectivity (removing
`parsePacket` from the TCB), three-layer post-parse separation (`parsePacket`,
`AdmissibleAst`, `ExporterCorrespondence`), and end-to-end `Execution.NoUB` transfer.
-/

namespace AnnealResearch.MirWireParser

/-- Canonical MIR body packet AST:
`(magicVer, ownerId, localCount, opTag, opArg, hasUnwindEdge)` where
`magicVer = 1` is the canonical wire version and `opTag ∈ {0, 1, 2, 3}` encodes
`0 = assignWrite`, `1 = checkedDrop`, `2 = callChecked`, `3 = returnScalar`. -/
abbrev MirPacketAst : Type :=
  Nat × Nat × Nat × Nat × Nat × Bool

/-- Total parser outcome over raw wire words:
`(0, some ast)` = `accepted ast`,
`(1, none)` = `rejectedMalformed`,
`(2, none)` = `rejectedUnsupportedVersionOrTag`. -/
abbrev ParseOutcome : Type :=
  Nat × Option MirPacketAst

noncomputable def accepted (ast : MirPacketAst) : ParseOutcome :=
  (0, some ast)

noncomputable def rejectedMalformed : ParseOutcome :=
  (1, none)

noncomputable def rejectedUnsupportedVersionOrTag : ParseOutcome :=
  (2, none)

/-- Canonical wire well-formedness (`magicVer = 1` and `opTag < 4`). -/
def WellFormedAst (ast : MirPacketAst) : Prop :=
  ast.1 = 1 ∧ ast.2.2.2.1 < 4

/-- Trusted wire format specification: canonical 6-word frame
`[magicVer, ownerId, localCount, opTag, opArg, unwindBit]`. -/
noncomputable def encodePacket (ast : MirPacketAst) : List Nat :=
  [ast.1, ast.2.1, ast.2.2.1, ast.2.2.2.1, ast.2.2.2.2.1,
   if ast.2.2.2.2.2 then 1 else 0]

/-- Untrusted total wire parser over raw word streams `List Nat`.
Rejects wrong-length frames (including truncated frames and trailing bytes) and
non-boolean unwind flags (`u ≥ 2`) as `rejectedMalformed`, and rejects unsupported
version (`v ≠ 1`) or unknown opcode tag (`tag ≥ 4`) as `rejectedUnsupportedVersionOrTag`. -/
noncomputable def parsePacket (bytes : List Nat) : ParseOutcome :=
  match bytes with
  | [v, owner, locals, tag, arg, u] =>
    if !(decide (v = 1)) then rejectedUnsupportedVersionOrTag
    else if !(decide (tag < 4)) then rejectedUnsupportedVersionOrTag
    else match u with
      | 0 => accepted (1, owner, locals, tag, arg, false)
      | 1 => accepted (1, owner, locals, tag, arg, true)
      | _ => rejectedMalformed
  | _ => rejectedMalformed

/-- Layer 2 structural admission on a decoded `MirPacketAst`:
requires wire well-formedness, a positive local slot count (`0 < localCount`),
and a preserved unwind cleanup edge (`hasUnwindEdge = true`). -/
def AdmissibleAst (ast : MirPacketAst) : Prop :=
  WellFormedAst ast ∧ 0 < ast.2.2.1 ∧ ast.2.2.2.2.2 = true

/-- Operational execution state `(isBad, pc, retVal)`. -/
abbrev PacketState : Type :=
  Bool × Nat × Nat

noncomputable def initPacketState : PacketState :=
  (false, 0, 0)

def PacketBad (s : PacketState) : Prop :=
  s.1 = true

/-- Execution safety guard: structural admission holds, and if the opcode is
`callChecked` (`opTag = 2`), its checked-call/const guard `opArg = 1` succeeds. -/
def PacketExecSafeGuard (ast : MirPacketAst) : Prop :=
  AdmissibleAst ast ∧ (ast.2.2.2.1 ≠ 2 ∨ ast.2.2.2.2.1 = 1)

/-- Operational step relation for a decoded `MirPacketAst`. -/
def PacketStep (ast : MirPacketAst) (s t : PacketState) : Prop :=
  (s = (false, 0, 0) ∧ PacketExecSafeGuard ast ∧
    t = (false, 1, ast.2.1 + ast.2.2.2.2.1)) ∨
  (s = (false, 0, 0) ∧ ¬ PacketExecSafeGuard ast ∧
    t = (true, 2, 0))

/-- Concrete positive wire packet `[1, 42, 4, 2, 1, 1]` and its decoded AST. -/
noncomputable def validPacketBytes : List Nat :=
  [1, 42, 4, 2, 1, 1]

noncomputable def validAst : MirPacketAst :=
  (1, 42, 4, 2, 1, true)

/-- Identified compiler subject `(ownerId, localCount, opTag, opArg, hasUnwindEdge)`. -/
abbrev CompilerSubject : Type :=
  Nat × Nat × Nat × Nat × Bool

noncomputable def subjectToAst (subj : CompilerSubject) : MirPacketAst :=
  (1, subj.1, subj.2.1, subj.2.2.1, subj.2.2.2.1, subj.2.2.2.2)

/-- Layer 3 exporter-to-compiler correspondence obligation: the compiler subject is
well-formed and the emitted wire bytes equal its canonical wire encoding. -/
def ExporterCorrespondence (subj : CompilerSubject) (bytes : List Nat) : Prop :=
  WellFormedAst (subjectToAst subj) ∧ bytes = encodePacket (subjectToAst subj)

/-- Semantic safety (`Execution.NoUB`) of the identified compiler subject itself. -/
def SubjectSafe (subj : CompilerSubject) : Prop :=
  Execution.NoUB (PacketStep (subjectToAst subj)) PacketBad initPacketState

/-- Theorem 1 (`FE-08`): Round-trip completeness of `parsePacket` over `encodePacket`. -/
theorem parsePacket_complete_roundtrip (ast : MirPacketAst)
    (hWf : WellFormedAst ast) :
    parsePacket (encodePacket ast) = accepted ast := by
  rcases ast with ⟨v, owner, locals, tag, arg, b⟩
  rcases hWf with ⟨hVer, hTag⟩
  subst hVer
  have hTagDec : decide (tag < 4) = true := decide_eq_true hTag
  cases b
  · change (if !(decide (1 = 1)) then rejectedUnsupportedVersionOrTag
      else if !(decide (tag < 4)) then rejectedUnsupportedVersionOrTag
      else accepted (1, owner, locals, tag, arg, false)) =
      accepted (1, owner, locals, tag, arg, false)
    rw [hTagDec]
    rfl
  · change (if !(decide (1 = 1)) then rejectedUnsupportedVersionOrTag
      else if !(decide (tag < 4)) then rejectedUnsupportedVersionOrTag
      else accepted (1, owner, locals, tag, arg, true)) =
      accepted (1, owner, locals, tag, arg, true)
    rw [hTagDec]
    rfl

/-- Theorem 3 (`FE-08`): Determinism and total three-way classification of `parsePacket`. -/
theorem parsePacket_deterministic_total (bytes1 bytes2 : List Nat) :
    (bytes1 = bytes2 → parsePacket bytes1 = parsePacket bytes2) ∧
    ((∃ ast, parsePacket bytes1 = accepted ast ∧
        WellFormedAst ast ∧ encodePacket ast = bytes1) ∨
      parsePacket bytes1 = rejectedMalformed ∨
      parsePacket bytes1 = rejectedUnsupportedVersionOrTag) := by
  refine ⟨fun hEq => congrArg parsePacket hEq, ?_⟩
  rcases bytes1 with
    _ | ⟨v, _ | ⟨owner, _ | ⟨locals, _ | ⟨tag, _ | ⟨arg, _ | ⟨u, _ | ⟨extra, rest⟩⟩⟩⟩⟩⟩⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)
  · cases hv : decide (v = 1)
    · apply Or.inr; apply Or.inr
      change (if !(decide (v = 1)) then rejectedUnsupportedVersionOrTag
        else if !(decide (tag < 4)) then rejectedUnsupportedVersionOrTag
        else match u with
          | 0 => accepted (1, owner, locals, tag, arg, false)
          | 1 => accepted (1, owner, locals, tag, arg, true)
          | _ => rejectedMalformed) = rejectedUnsupportedVersionOrTag
      rw [hv]
      rfl
    · have hvEq : v = 1 := of_decide_eq_true hv
      subst hvEq
      cases htag : decide (tag < 4)
      · apply Or.inr; apply Or.inr
        change (if !(decide (1 = 1)) then rejectedUnsupportedVersionOrTag
          else if !(decide (tag < 4)) then rejectedUnsupportedVersionOrTag
          else match u with
            | 0 => accepted (1, owner, locals, tag, arg, false)
            | 1 => accepted (1, owner, locals, tag, arg, true)
            | _ => rejectedMalformed) = rejectedUnsupportedVersionOrTag
        rw [htag]
        rfl
      · have htagLt : tag < 4 := of_decide_eq_true htag
        rcases u with _ | _ | u'
        · apply Or.inl
          refine ⟨(1, owner, locals, tag, arg, false), ?_, ⟨rfl, htagLt⟩, rfl⟩
          change (if !(decide (1 = 1)) then rejectedUnsupportedVersionOrTag
            else if !(decide (tag < 4)) then rejectedUnsupportedVersionOrTag
            else accepted (1, owner, locals, tag, arg, false)) =
            accepted (1, owner, locals, tag, arg, false)
          rw [htag]
          rfl
        · apply Or.inl
          refine ⟨(1, owner, locals, tag, arg, true), ?_, ⟨rfl, htagLt⟩, rfl⟩
          change (if !(decide (1 = 1)) then rejectedUnsupportedVersionOrTag
            else if !(decide (tag < 4)) then rejectedUnsupportedVersionOrTag
            else accepted (1, owner, locals, tag, arg, true)) =
            accepted (1, owner, locals, tag, arg, true)
          rw [htag]
          rfl
        · apply Or.inr; apply Or.inl
          change (if !(decide (1 = 1)) then rejectedUnsupportedVersionOrTag
            else if !(decide (tag < 4)) then rejectedUnsupportedVersionOrTag
            else rejectedMalformed) = rejectedMalformed
          rw [htag]
          rfl
  · exact Or.inr (Or.inl rfl)

/-- Theorem 2 (`FE-08`): Soundness and injectivity of `parsePacket` and `encodePacket`,
removing `parsePacket` from the Trusted Computing Base. -/
theorem parsePacket_sound_injective (bytes bytes2 : List Nat) (ast ast2 : MirPacketAst)
    (hParse : parsePacket bytes = accepted ast) :
    WellFormedAst ast ∧
    encodePacket ast = bytes ∧
    (parsePacket bytes2 = accepted ast → bytes = bytes2) ∧
    (WellFormedAst ast2 → encodePacket ast = encodePacket ast2 → ast = ast2) := by
  have hCore : WellFormedAst ast ∧ encodePacket ast = bytes := by
    rcases (parsePacket_deterministic_total bytes bytes).2 with
      ⟨ast', hAcc', hWf', hEnc'⟩ | hMal | hUnsup
    · have hAstEq : ast' = ast :=
        Option.some.inj (congrArg Prod.snd (hAcc'.symm.trans hParse))
      subst hAstEq
      exact ⟨hWf', hEnc'⟩
    · exact False.elim (Nat.noConfusion (congrArg Prod.fst (hMal.symm.trans hParse)))
    · exact False.elim (Nat.noConfusion (congrArg Prod.fst (hUnsup.symm.trans hParse)))
  refine ⟨hCore.1, hCore.2, ?_, ?_⟩
  · intro hParse2
    rcases (parsePacket_deterministic_total bytes2 bytes2).2 with
      ⟨ast', hAcc', _, hEnc'⟩ | hMal | hUnsup
    · have hAstEq : ast' = ast :=
        Option.some.inj (congrArg Prod.snd (hAcc'.symm.trans hParse2))
      subst hAstEq
      exact hCore.2.symm.trans hEnc'
    · exact False.elim (Nat.noConfusion (congrArg Prod.fst (hMal.symm.trans hParse2)))
    · exact False.elim (Nat.noConfusion (congrArg Prod.fst (hUnsup.symm.trans hParse2)))
  · intro hWf2 hEncEq
    have h1 := parsePacket_complete_roundtrip ast hCore.1
    have h2 := parsePacket_complete_roundtrip ast2 hWf2
    rw [hEncEq] at h1
    exact Option.some.inj (congrArg Prod.snd (h1.symm.trans h2))

/-- Theorem 4 (`FE-08`): Concrete positive wire specimen `[1, 42, 4, 2, 1, 1]` decodes to
`validAst`, passes `AdmissibleAst`, satisfies `Execution.NoUB`, and reaches `(false, 1, 43)`. -/
theorem positive_valid_packet_decoded_and_safe :
    parsePacket validPacketBytes = accepted validAst ∧
    encodePacket validAst = validPacketBytes ∧
    AdmissibleAst validAst ∧
    Execution.NoUB (PacketStep validAst) PacketBad initPacketState ∧
    Execution.Reach (PacketStep validAst) initPacketState (false, 1, 43) := by
  have hWf : WellFormedAst validAst := ⟨rfl, by decide⟩
  have hAdm : AdmissibleAst validAst := ⟨hWf, by decide, rfl⟩
  have hGuard : PacketExecSafeGuard validAst := ⟨hAdm, Or.inr rfl⟩
  have hNoUB : Execution.NoUB (PacketStep validAst) PacketBad initPacketState := by
    apply Execution.invariant_noUB (Invariant := fun s : PacketState => s.1 = false)
    · rfl
    · intro s t _ hStep
      rcases hStep with ⟨_, _, ht⟩ | ⟨_, hNotGuard, _⟩
      · subst ht; rfl
      · exact False.elim (hNotGuard hGuard)
    · intro s hs hBad
      exact Bool.noConfusion (hs.symm.trans hBad)
  have hReach : Execution.Reach (PacketStep validAst) initPacketState (false, 1, 43) :=
    Execution.Reach.tail (Execution.Reach.refl initPacketState)
      (Or.inl ⟨rfl, hGuard, rfl⟩)
  exact ⟨rfl, rfl, hAdm, hNoUB, hReach⟩

/-- Theorem 5 (`FE-09`): End-to-end transfer of `Execution.NoUB` from the parsed AST to the
identified compiler subject using `ExporterCorrespondence` and `parsePacket_complete_roundtrip`,
without trusting `parsePacket`. -/
theorem end_to_end_exporter_plus_proved_parser_transfers_noUB
    (subj : CompilerSubject) (bytes : List Nat) (ast : MirPacketAst)
    (hCorr : ExporterCorrespondence subj bytes)
    (hParse : parsePacket bytes = accepted ast)
    (hAdm : AdmissibleAst ast)
    (hNoUB : Execution.NoUB (PacketStep ast) PacketBad initPacketState) :
    ast = subjectToAst subj ∧
    AdmissibleAst (subjectToAst subj) ∧
    SubjectSafe subj := by
  rcases hCorr with ⟨hWfSubj, hBytes⟩
  have hRound := parsePacket_complete_roundtrip (subjectToAst subj) hWfSubj
  rw [← hBytes] at hRound
  have hAstEq : ast = subjectToAst subj :=
    Option.some.inj (congrArg Prod.snd (hParse.symm.trans hRound))
  subst hAstEq
  exact ⟨rfl, hAdm, hNoUB⟩

#print axioms parsePacket_complete_roundtrip
#print axioms parsePacket_sound_injective
#print axioms parsePacket_deterministic_total
#print axioms positive_valid_packet_decoded_and_safe
#print axioms end_to_end_exporter_plus_proved_parser_transfers_noUB

end AnnealResearch.MirWireParser
