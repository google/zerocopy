import Std

/-!
Owned finite codec/admission experiment. Manual binding: MiniRust
d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed, representation.md Bool and enum
branches, and well-formed.md's selected one-byte enum checks. See docs/rust-opsem/codec-admission.md.

Each enum payload is an empty tuple with a one-byte all-padding layout. A tagger
writes one u8 at offset zero; its discriminator is one of the named trees below.
Nat is only an abstract optional provenance label. This is neither a MiniRust
import theorem, rustc-image result, frontend theorem, nor general codec solver.

Structural shape, codec coherence, dispatched instance identity, and explicit
required-const evidence are separate propositions. No premise asserts NoUB.
The const certificate is an owned arithmetic admission obligation, not a claim
that a source Rust const expression was evaluated by an actual compiler.
-/

namespace AnnealResearch.CodecAdmission

inductive Byte where
  | uninit
  | init (data : Fin 256) (provenance : Option Nat)
  deriving DecidableEq, Repr

/-- Selected source definedness order, including provenance stripping. -/
def ByteLE : Byte → Byte → Prop
  | .uninit, _ => True
  | .init first none, .init second _ => first = second
  | .init first (some p), .init second (some q) => first = second ∧ p = q
  | _, _ => False

/-- Pointwise byte definedness with equal lengths, including the empty list. -/
inductive BytesLE : List Byte → List Byte → Prop where
  | nil : BytesLE [] []
  | cons {first second : Byte} {firstRest secondRest : List Byte}
      (head : ByteLE first second) (tail : BytesLE firstRest secondRest) :
      BytesLE (first :: firstRest) (second :: secondRest)

inductive Variant where
  | zero | one
  deriving DecidableEq, Repr

def swap : Variant → Variant
  | .zero => .one | .one => .zero

def tagEncode : Variant → Byte
  | .zero => .init 0 none | .one => .init 1 none

def decodeTag : Byte → Option Variant
  | .uninit => none
  | .init data _ =>
      if data.val = 0 then some .zero
      else if data.val = 1 then some .one else none

structure Branch where
  lower : Nat
  upper : Nat
  variant : Variant
  deriving DecidableEq, Repr

/-- One-level source decision tree: children have Known leaves; fallback is
Known or Invalid. Nested branches are outside the selected fragment. -/
inductive Discriminator where
  | known (variant : Variant)
  | invalid
  | branch (children : List Branch) (fallback : Option Variant)
  deriving DecidableEq, Repr

def decodeDiscriminator : Discriminator → Byte → Option Variant
  | .known variant, _ => some variant
  | .invalid, _ => none
  | .branch children fallback, byte =>
      match byte with
      | .uninit => none
      | .init data _ =>
          match children.find? (fun child => decide (child.lower ≤ data.val ∧ data.val < child.upper)) with
          | some child => some child.variant
          | none => fallback

def normalTree : Discriminator := .branch [⟨0, 1, .zero⟩, ⟨1, 2, .one⟩] none
def swappedTree : Discriminator := .branch [⟨0, 1, .one⟩, ⟨1, 2, .zero⟩] none

/-- Selected structural checks: u8-representable nonempty half-open ranges and
pairwise nonoverlap. Variant membership is built into the finite Variant type. -/
def branchesFit : List Branch → Bool
  | [] => true
  | child :: rest =>
      decide (child.lower < child.upper ∧ child.upper ≤ 256) &&
      rest.all (fun other => decide (child.upper ≤ other.lower ∨ other.upper ≤ child.lower)) &&
      branchesFit rest

def discriminatorFits : Discriminator → Bool
  | .known _ | .invalid => true
  | .branch children _ => branchesFit children

theorem normal_tree_decode (byte : Byte) :
    decodeDiscriminator normalTree byte = decodeTag byte := by
  cases byte with
  | uninit => rfl
  | init data provenance =>
    by_cases zero : data.val = 0
    · have dataEq : data = 0 := Fin.ext zero
      subst data
      rfl
    · by_cases one : data.val = 1
      · have dataEq : data = 1 := Fin.ext one
        subst data
        rfl
      · have secondMiss : ¬ (1 ≤ data.val ∧ data.val < 2) := by omega
        simp [decodeDiscriminator, normalTree, decodeTag, List.find?, zero, one, secondMiss]

theorem swapped_tree_decode (byte : Byte) :
    decodeDiscriminator swappedTree byte = (decodeTag byte).map swap := by
  cases byte with
  | uninit => rfl
  | init data provenance =>
    by_cases zero : data.val = 0
    · have dataEq : data = 0 := Fin.ext zero
      subst data
      rfl
    · by_cases one : data.val = 1
      · have dataEq : data = 1 := Fin.ext one
        subst data
        rfl
      · have secondMiss : ¬ (1 ≤ data.val ∧ data.val < 2) := by omega
        simp [decodeDiscriminator, swappedTree, decodeTag, List.find?, zero, one, secondMiss]

structure EnumDefinition where
  size : Nat
  align : Nat
  tagOffset : Nat
  tagZero : Fin 256
  tagOne : Fin 256
  discriminator : Discriminator

/-- All remaining source geometry is built into this tag-only fragment:
two discriminants, no payload fields, one in-bounds u8 write per variant. -/
def EnumShape (definition : EnumDefinition) : Prop :=
  definition.size = 1 ∧ definition.align = 1 ∧ definition.tagOffset = 0 ∧
  discriminatorFits definition.discriminator = true

instance (definition : EnumDefinition) : Decidable (EnumShape definition) := by
  unfold EnumShape
  infer_instance

def enumEncodeOne (definition : EnumDefinition) : Variant → Byte
  | .zero => .init definition.tagZero none
  | .one => .init definition.tagOne none

def enumDecodeOne (definition : EnumDefinition) (byte : Byte) : Option Variant :=
  decodeDiscriminator definition.discriminator byte

def enumEncode (definition : EnumDefinition) (value : Variant) : List Byte :=
  [enumEncodeOne definition value]

/-- Outside the admitted length this total owned helper returns none; the
operation dispatcher below distinguishes that shape failure from runtime UB. -/
def enumDecode (definition : EnumDefinition) (bytes : List Byte) : Option Variant :=
  if bytes.length = definition.size then enumDecodeOne definition (bytes.getD 0 .uninit)
  else none

/-- A direct constraint on tagger/discriminator DATA, not the desired laws.
Only these two declared singleton-interval trees are certified by this finite
predicate. Other coherent codecs may exist outside its declared domain. -/
def EnumCoherent (definition : EnumDefinition) : Prop :=
  (definition.tagZero = 0 ∧ definition.tagOne = 1 ∧ definition.discriminator = normalTree) ∨
  (definition.tagZero = 1 ∧ definition.tagOne = 0 ∧ definition.discriminator = swappedTree)

def normalEnum : EnumDefinition := ⟨1, 1, 0, 0, 1, normalTree⟩
def swappedEnum : EnumDefinition := ⟨1, 1, 0, 1, 0, swappedTree⟩
/-- Exact retained discriminator failure: taggers write 0/1, Known(0) ignores
the tag and selects the existing variant zero, including on Uninit. -/
def incoherentEnum : EnumDefinition := ⟨1, 1, 0, 0, 1, .known .zero⟩

theorem normal_coherent : EnumCoherent normalEnum := Or.inl ⟨rfl, rfl, rfl⟩
theorem swapped_coherent : EnumCoherent swappedEnum := Or.inr ⟨rfl, rfl, rfl⟩

theorem tag_deflation (byte : Byte) (value : Variant) (decoded : decodeTag byte = some value) :
    ByteLE (tagEncode value) byte := by
  cases byte with
  | uninit => cases decoded
  | init data provenance =>
    by_cases zero : data.val = 0
    · have chosen : Variant.zero = value := by simpa [decodeTag, zero] using decoded
      cases chosen
      change (0 : Fin 256) = data
      exact Fin.ext zero.symm
    · by_cases one : data.val = 1
      · have chosen : Variant.one = value := by simpa [decodeTag, zero, one] using decoded
        cases chosen
        change (1 : Fin 256) = data
        exact Fin.ext one.symm
      · simp [decodeTag, zero, one] at decoded

theorem coherent_roundtrip {definition : EnumDefinition} (coherent : EnumCoherent definition)
    (value : Variant) :
    enumDecodeOne definition (enumEncodeOne definition value) = some value := by
  rcases coherent with ⟨zero, one, tree⟩ | ⟨zero, one, tree⟩
  · cases value <;> simp [enumDecodeOne, enumEncodeOne, zero, one, tree,
      normal_tree_decode, decodeTag]
  · cases value <;> simp [enumDecodeOne, enumEncodeOne, zero, one, tree,
      swapped_tree_decode, decodeTag, swap]

theorem coherent_deflation {definition : EnumDefinition} (coherent : EnumCoherent definition)
    (byte : Byte) (value : Variant) (decoded : enumDecodeOne definition byte = some value) :
    ByteLE (enumEncodeOne definition value) byte := by
  rcases coherent with ⟨zero, one, tree⟩ | ⟨zero, one, tree⟩
  · have tagDecoded : decodeTag byte = some value := by
      simpa only [enumDecodeOne, tree, normal_tree_decode] using decoded
    have deflated := tag_deflation byte value tagDecoded
    cases value <;> simpa [enumEncodeOne, zero, one, tagEncode] using deflated
  · have tagged : (decodeTag byte).map swap = some value := by
      simpa only [enumDecodeOne, tree, swapped_tree_decode] using decoded
    cases selected : decodeTag byte with
    | none => simp [selected] at tagged
    | some original =>
      have chosen : swap original = value := by simpa [selected] using tagged
      cases chosen
      have deflated := tag_deflation byte original selected
      cases original <;> simpa [enumEncodeOne, zero, one, tagEncode, swap] using deflated

/-- Conditional source-style roundtrip, for this exact one-byte fragment. -/
theorem enum_roundtrip {definition : EnumDefinition} (shape : EnumShape definition)
    (coherent : EnumCoherent definition) (value : Variant) :
    enumDecode definition (enumEncode definition value) = some value := by
  simpa [enumDecode, enumEncode, shape.1] using coherent_roundtrip coherent value

theorem enum_deflation {definition : EnumDefinition} (shape : EnumShape definition)
    (coherent : EnumCoherent definition) (bytes : List Byte) (value : Variant)
    (length : bytes.length = definition.size) (decoded : enumDecode definition bytes = some value) :
    BytesLE (enumEncode definition value) bytes := by
  have singleton : bytes.length = 1 := length.trans shape.1
  cases bytes with
  | nil => simp at singleton
  | cons byte rest =>
    cases rest with
    | nil =>
      have oneDecoded : enumDecodeOne definition byte = some value := by
        simpa [enumDecode, shape.1] using decoded
      exact BytesLE.cons (coherent_deflation coherent byte value oneDecoded) BytesLE.nil
    | cons next rest => simp at singleton

def boolEncodeOne (value : Bool) : Byte :=
  .init (if value then 1 else 0) none

def boolDecodeOne (byte : Byte) : Option Bool :=
  (decodeTag byte).map (fun value => match value with | .zero => false | .one => true)

def boolEncode (value : Bool) : List Byte := [boolEncodeOne value]
def boolDecode (bytes : List Byte) : Option Bool :=
  if bytes.length = 1 then boolDecodeOne (bytes.getD 0 .uninit) else none

structure BoolLaws : Prop where
  roundtrip : ∀ value, boolDecodeOne (boolEncodeOne value) = some value
  deflation : ∀ byte value, boolDecodeOne byte = some value → ByteLE (boolEncodeOne value) byte

theorem bool_codec_laws : BoolLaws := by
  constructor
  · intro value
    cases value <;> rfl
  · intro byte value decoded
    cases selected : decodeTag byte with
    | none => simp [boolDecodeOne, selected] at decoded
    | some original =>
      have deflated := tag_deflation byte original selected
      cases original <;> cases value <;>
        simp_all [boolDecodeOne, boolEncodeOne, tagEncode]

theorem bool_roundtrip (value : Bool) : boolDecode (boolEncode value) = some value := by
  cases value <;> rfl

theorem bool_deflation (bytes : List Byte) (value : Bool) (length : bytes.length = 1)
    (decoded : boolDecode bytes = some value) : BytesLE (boolEncode value) bytes := by
  cases bytes with
  | nil => simp at length
  | cons byte rest =>
    cases rest with
    | nil =>
      have oneDecoded : boolDecodeOne byte = some value := by simpa [boolDecode] using decoded
      exact BytesLE.cons (bool_codec_laws.deflation byte value oneDecoded) BytesLE.nil
    | cons next rest => simp at length

inductive Definition where
  | enumeration (definition : EnumDefinition)
  | boolean

def DefinitionShape : Definition → Prop
  | .enumeration definition => EnumShape definition
  | .boolean => True

instance (definition : Definition) : Decidable (DefinitionShape definition) := by
  cases definition with
  | enumeration definition => exact inferInstanceAs (Decidable (EnumShape definition))
  | boolean => exact isTrue True.intro

def DefinitionCoherent : Definition → Prop
  | .enumeration definition => EnumCoherent definition
  | .boolean => True

inductive InstanceId where
  | normal | swapped | incoherent | boolean
  deriving DecidableEq, Repr

/-- The actual finite dispatch table, not an arbitrary implementation family. -/
def lookup : InstanceId → Definition
  | .normal => .enumeration normalEnum
  | .swapped => .enumeration swappedEnum
  | .incoherent => .enumeration incoherentEnum
  | .boolean => .boolean

/-- Owned required-const certificate: the supplied evaluation result equals the
concrete argument and passes its u8 bound. No source CTFE execution is inferred. -/
structure ConstCertificate (argument : Nat) where
  result : Nat
  evaluates : result = argument
  requiredCheck : result < 256

structure Binding where
  advertised : InstanceId
  selected : InstanceId
  constArgument : Nat
  constEvidence : Option (ConstCertificate constArgument)

structure StaticAdmission (binding : Binding) : Prop where
  shape : DefinitionShape (lookup binding.advertised)
  selected_eq : binding.selected = binding.advertised
  required_const : ∃ evidence, binding.constEvidence = some evidence

/-- The arithmetic fact comes from the stored certificate's evidence, not its
mere mention. This illustrative obligation is orthogonal to scalar codec laws. -/
theorem const_argument_bound {binding : Binding} (admitted : StaticAdmission binding) :
    binding.constArgument < 256 := by
  obtain ⟨evidence, _⟩ := admitted.required_const
  have bounded := evidence.requiredCheck
  rw [evidence.evaluates] at bounded
  exact bounded

structure Admitted (binding : Binding) : Prop extends StaticAdmission binding where
  coherent : DefinitionCoherent (lookup binding.advertised)

inductive Operation where
  | encodeEnum (value : Variant)
  | decodeEnum (bytes : List Byte)
  | encodeBool (value : Bool)
  | decodeBool (bytes : List Byte)

/-- Instruction kind and buffer length, with no runtime-validity requirement. -/
def OperationShape : Definition → Operation → Prop
  | .enumeration _, .encodeEnum _ => True
  | .enumeration definition, .decodeEnum bytes => bytes.length = definition.size
  | .boolean, .encodeBool _ => True
  | .boolean, .decodeBool bytes => bytes.length = 1
  | _, _ => False

inductive UB where
  | invalidEnum | invalidBoolean
  deriving DecidableEq, Repr

inductive SpecFailure where
  | layout | wrongKind | wrongLength
  deriving DecidableEq, Repr

inductive Outcome where
  | encoded (bytes : List Byte)
  | enumValue (value : Variant)
  | boolValue (value : Bool)
  | ub (diagnostic : UB)
  | specFailure (failure : SpecFailure)
  deriving DecidableEq, Repr

def finishEnum : Option Variant → Outcome
  | some value => .enumValue value | none => .ub .invalidEnum
def finishBool : Option Bool → Outcome
  | some value => .boolValue value | none => .ub .invalidBoolean

def runDefinition (definition : Definition) (operation : Operation) : Outcome :=
  if DefinitionShape definition then
    match definition, operation with
    | .enumeration definition, .encodeEnum value => .encoded (enumEncode definition value)
    | .enumeration definition, .decodeEnum bytes =>
        if bytes.length = definition.size then finishEnum (enumDecode definition bytes)
        else .specFailure .wrongLength
    | .boolean, .encodeBool value => .encoded (boolEncode value)
    | .boolean, .decodeBool bytes =>
        if bytes.length = 1 then finishBool (boolDecode bytes) else .specFailure .wrongLength
    | _, _ => .specFailure .wrongKind
  else .specFailure .layout

def run (binding : Binding) (operation : Operation) : Outcome :=
  runDefinition (lookup binding.selected) operation

def Classified : Outcome → Prop
  | .specFailure _ => False
  | _ => True

theorem definition_classified {definition : Definition} (shape : DefinitionShape definition)
    (operation : Operation) (operationShape : OperationShape definition operation) :
    Classified (runDefinition definition operation) := by
  unfold runDefinition
  simp only [ite_eq_left shape]
  cases definition with
  | enumeration definition =>
    cases operation with
    | encodeEnum value => exact True.intro
    | decodeEnum bytes =>
      change bytes.length = definition.size at operationShape
      simp only [ite_eq_left operationShape]
      cases enumDecode definition bytes <;> exact True.intro
    | encodeBool value => exact False.elim operationShape
    | decodeBool bytes => exact False.elim operationShape
  | boolean =>
    cases operation with
    | encodeEnum value => exact False.elim operationShape
    | decodeEnum bytes => exact False.elim operationShape
    | encodeBool value => exact True.intro
    | decodeBool bytes =>
      change bytes.length = 1 at operationShape
      simp only [ite_eq_left operationShape]
      cases boolDecode bytes <;> exact True.intro

/-- Dispatch identity binds the advertised semantic evidence to actual code. -/
theorem admitted_dispatch {binding : Binding} (admitted : Admitted binding) (operation : Operation) :
    run binding operation = runDefinition (lookup binding.advertised) operation := by
  unfold run
  rw [admitted.selected_eq]

/-- Dispatch identity, structural shape, and ordinary instruction shape exclude
specification failure. The composite admission also packages coherence and const
evidence, but those fields are not needed by this classifier. No NoUB premise. -/
theorem admitted_operation_classified {binding : Binding} (admitted : Admitted binding)
    (operation : Operation) (shape : OperationShape (lookup binding.advertised) operation) :
    Classified (run binding operation) := by
  rw [admitted_dispatch admitted operation]
  exact definition_classified admitted.shape operation shape

def zeroConst : ConstCertificate 0 := ⟨0, rfl, by decide⟩
def normalBinding : Binding := ⟨.normal, .normal, 0, some zeroConst⟩
def swappedBinding : Binding := ⟨.swapped, .swapped, 0, some zeroConst⟩
def booleanBinding : Binding := ⟨.boolean, .boolean, 0, some zeroConst⟩
def incoherentBinding : Binding := ⟨.incoherent, .incoherent, 0, some zeroConst⟩
def wrongBinding : Binding := ⟨.normal, .swapped, 0, some zeroConst⟩
def missingConstBinding : Binding := ⟨.normal, .normal, 0, none⟩
def argument256Binding : Binding := ⟨.normal, .normal, 256, none⟩

theorem named_instances_admitted :
    Admitted normalBinding ∧ Admitted swappedBinding ∧ Admitted booleanBinding := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨⟨⟨rfl, rfl, rfl, rfl⟩, rfl, ⟨zeroConst, rfl⟩⟩, normal_coherent⟩
  · exact ⟨⟨⟨rfl, rfl, rfl, rfl⟩, rfl, ⟨zeroConst, rfl⟩⟩, swapped_coherent⟩
  · exact ⟨⟨True.intro, rfl, ⟨zeroConst, rfl⟩⟩, True.intro⟩

theorem actual_admitted_values :
    run normalBinding (.encodeEnum .one) = .encoded [.init 1 none] ∧
    run normalBinding (.decodeEnum [.init 1 none]) = .enumValue .one ∧
    run booleanBinding (.encodeBool true) = .encoded [.init 1 none] ∧
    run booleanBinding (.decodeBool [.init 0 (some 9)]) = .boolValue false :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem incoherent_control :
    StaticAdmission incoherentBinding ∧
    run incoherentBinding (.encodeEnum .one) = .encoded [.init 1 none] ∧
    run incoherentBinding (.decodeEnum [.init 1 none]) = .enumValue .zero ∧
    ¬ EnumCoherent incoherentEnum := by
  refine ⟨⟨⟨rfl, rfl, rfl, rfl⟩, rfl, ⟨zeroConst, rfl⟩⟩, rfl, rfl, ?_⟩
  intro coherent
  have impossible := coherent_roundtrip coherent .one
  cases impossible

/-- Both codecs are coherent. Substituting the coherent swapped instance still
violates the normal instance's advertised decode(1)=variant-one contract. -/
theorem wrong_selected_instance_control :
    DefinitionCoherent (lookup wrongBinding.advertised) ∧
    DefinitionCoherent (lookup wrongBinding.selected) ∧
    run normalBinding (.decodeEnum [.init 1 none]) = .enumValue .one ∧
    run wrongBinding (.decodeEnum [.init 1 none]) = .enumValue .zero ∧
    ¬ Admitted wrongBinding := by
  refine ⟨normal_coherent, swapped_coherent, rfl, rfl, ?_⟩
  intro admitted
  have impossible : InstanceId.swapped = .normal := admitted.selected_eq
  cases impossible

theorem absent_const_evidence_control :
    DefinitionShape (lookup missingConstBinding.advertised) ∧
    DefinitionCoherent (lookup missingConstBinding.advertised) ∧
    ¬ StaticAdmission missingConstBinding := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, normal_coherent, ?_⟩
  intro admitted
  obtain ⟨evidence, impossible⟩ := admitted.required_const
  cases impossible

/-- No certificate can satisfy the owned illustrative bound at argument 256,
even though the selected codec's shape and coherence data are unchanged. -/
theorem argument256_const_control :
    DefinitionShape (lookup argument256Binding.advertised) ∧
    DefinitionCoherent (lookup argument256Binding.advertised) ∧
    ¬ Nonempty (ConstCertificate 256) ∧ ¬ StaticAdmission argument256Binding := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, normal_coherent, ?_, ?_⟩
  · rintro ⟨evidence⟩
    have bounded := evidence.requiredCheck
    rw [evidence.evaluates] at bounded
    exact (Nat.lt_irrefl 256) bounded
  · intro admitted
    have bounded := const_argument_bound admitted
    exact (Nat.lt_irrefl 256) bounded

/-- Byte 2 is initialized and has the admitted length. Admission proves the
coherent Boolean codec's law on Boolean values, not validity of arbitrary bytes. -/
theorem admitted_invalid_boolean_UB :
    Admitted booleanBinding ∧
    OperationShape (lookup booleanBinding.advertised) (.decodeBool [.init 2 none]) ∧
    run booleanBinding (.decodeBool [.init 2 none]) = .ub .invalidBoolean ∧
    Classified (run booleanBinding (.decodeBool [.init 2 none])) :=
  ⟨named_instances_admitted.2.2, rfl, rfl, True.intro⟩

theorem provenance_deflation_is_not_equality :
    boolDecode [.init 1 (some 9)] = some true ∧
    BytesLE (boolEncode true) [.init 1 (some 9)] ∧
    boolEncode true ≠ [.init 1 (some 9)] := by
  refine ⟨rfl, BytesLE.cons rfl BytesLE.nil, ?_⟩
  decide

#print axioms normal_tree_decode
#print axioms swapped_tree_decode
#print axioms coherent_roundtrip
#print axioms coherent_deflation
#print axioms enum_roundtrip
#print axioms enum_deflation
#print axioms bool_codec_laws
#print axioms bool_roundtrip
#print axioms bool_deflation
#print axioms definition_classified
#print axioms const_argument_bound
#print axioms admitted_dispatch
#print axioms admitted_operation_classified
#print axioms named_instances_admitted
#print axioms actual_admitted_values
#print axioms incoherent_control
#print axioms wrong_selected_instance_control
#print axioms absent_const_evidence_control
#print axioms argument256_const_control
#print axioms admitted_invalid_boolean_UB
#print axioms provenance_deflation_is_not_equality

end AnnealResearch.CodecAdmission
