import AnnealResearch.Execution

set_option Elab.async false

/-!
R-ADEV-05 Module 1: Non-circular modular fact reuse vs. fresh reconstruction.
-/

namespace AnnealResearch.FactReuseValidation

abbrev LayoutSpec : Type := Nat × Nat × Nat × Nat

noncomputable def boolSlotLayout : LayoutSpec := (1, 1, 0, 1)

def StructuralLayoutCert (layout : LayoutSpec) : Prop :=
  layout.1 = 1 ∧ layout.2.1 = 1 ∧ layout.2.2.1 = 0 ∧ layout.2.2.2 = 1

def ValidBoolByte (byte : Nat) : Prop :=
  byte = 0 ∨ byte = 1

def CallerValidityPremise (requireValidByte : Bool) (byte : Nat) : Prop :=
  requireValidByte = false ∨ (requireValidByte = true ∧ ValidBoolByte byte)

def CodecProducesOk (byte : Nat) (b : Bool) : Prop :=
  (byte = 0 ∧ b = false) ∨ (byte = 1 ∧ b = true)

def CodecProducesReject (impl : Nat) (cfg : Bool) (byte : Nat) : Prop :=
  (byte ≠ 0 ∧ byte ≠ 1) ∧ (impl = 0 ∨ impl = 1 ∨ (impl = 3 ∧ cfg = true))

def CodecProducesUB (impl : Nat) (cfg : Bool) (byte : Nat) : Prop :=
  (byte ≠ 0 ∧ byte ≠ 1) ∧ (impl = 2 ∨ (impl = 3 ∧ cfg = false))

def CodecSemanticsCert (impl : Nat) (cfg : Bool) (requireValidByte : Bool) : Prop :=
  ∀ byte : Nat, CallerValidityPremise requireValidByte byte →
    ¬ CodecProducesUB impl cfg byte

abbrev DecodeState : Type := Bool × Nat × LayoutSpec × Nat × Bool

noncomputable def initState (layout : LayoutSpec) (byte : Nat) : DecodeState :=
  (false, 0, layout, byte, false)

def DecodeBad (s : DecodeState) : Prop :=
  s.1 = true

def DecodeStepFull (impl : Nat) (cfg : Bool) (consumeMode : Bool)
    (s t : DecodeState) : Prop :=
  (∃ layout byte,
    s = (false, 0, layout, byte, false) ∧
    StructuralLayoutCert layout ∧
    t = (false, 1, layout, byte, false)) ∨
  (∃ layout byte,
    s = (false, 0, layout, byte, false) ∧
    ¬ StructuralLayoutCert layout ∧
    t = (true, 6, layout, byte, false)) ∨
  (∃ layout byte val,
    s = (false, 1, layout, byte, false) ∧
    CodecProducesOk byte val ∧
    t = (false, 2, layout, byte, val)) ∨
  (∃ layout byte,
    s = (false, 1, layout, byte, false) ∧
    CodecProducesReject impl cfg byte ∧
    t = (false, 5, layout, byte, false)) ∨
  (∃ layout byte,
    s = (false, 1, layout, byte, false) ∧
    CodecProducesUB impl cfg byte ∧
    t = (true, 7, layout, byte, false)) ∨
  (∃ layout byte val,
    s = (false, 2, layout, byte, val) ∧
    consumeMode = true ∧
    t = (false, 3, layout, byte, val)) ∨
  (∃ layout byte val,
    s = (false, 2, layout, byte, val) ∧
    consumeMode = false ∧
    t = (false, 4, layout, byte, false))

def DecodeStep (impl : Nat) (cfg : Bool) : DecodeState → DecodeState → Prop :=
  DecodeStepFull impl cfg true

def EndpointSafeAndTyped (layout : LayoutSpec) (impl : Nat)
    (cfg : Bool) (byte : Nat) : Prop :=
  Execution.NoUB (DecodeStep impl cfg) DecodeBad (initState layout byte) ∧
  (∀ b : Bool, CodecProducesOk byte b →
    Execution.Reach (DecodeStep impl cfg) (initState layout byte) (false, 3, layout, byte, b)) ∧
  (CodecProducesReject impl cfg byte →
    Execution.Reach (DecodeStep impl cfg) (initState layout byte) (false, 5, layout, byte, false))

def FreshReconstructionConditions (layout : LayoutSpec) (impl : Nat)
    (cfg : Bool) (byte : Nat) : Prop :=
  StructuralLayoutCert layout ∧ ¬ CodecProducesUB impl cfg byte

theorem fresh_reconstruction_endpoint
    {layout : LayoutSpec} {impl : Nat} {cfg : Bool} {byte : Nat}
    (hFresh : FreshReconstructionConditions layout impl cfg byte) :
    EndpointSafeAndTyped layout impl cfg byte := by
  rcases hFresh with ⟨hLayout, hNoUBOut⟩
  have hNoUB : Execution.NoUB (DecodeStep impl cfg) DecodeBad (initState layout byte) := by
    apply Execution.invariant_noUB
      (Invariant := fun s : DecodeState =>
        s.1 = false ∧ s.2.2.1 = layout ∧ s.2.2.2.1 = byte)
    · exact ⟨rfl, rfl, rfl⟩
    · intro s t hs edge
      rcases edge with
        ⟨_, _, hs_eq, _, ht_eq⟩ |
        ⟨l, _, hs_eq, hNotL, _⟩ |
        ⟨_, _, _, hs_eq, _, ht_eq⟩ |
        ⟨_, _, hs_eq, _, ht_eq⟩ |
        ⟨_, b, hs_eq, hUB, _⟩ |
        ⟨_, _, _, hs_eq, _, ht_eq⟩ |
        ⟨_, _, _, hs_eq, _, ht_eq⟩
      · subst hs_eq; subst ht_eq; exact hs
      · subst hs_eq
        have hL : l = layout := hs.2.1
        subst hL
        exact False.elim (hNotL hLayout)
      · subst hs_eq; subst ht_eq; exact hs
      · subst hs_eq; subst ht_eq; exact hs
      · subst hs_eq
        have hB : b = byte := hs.2.2
        subst hB
        exact False.elim (hNoUBOut hUB)
      · subst hs_eq; subst ht_eq; exact hs
      · subst hs_eq; subst ht_eq; exact hs
    · intro _ hs hBad
      exact Bool.noConfusion (hs.1.symm.trans hBad)
  refine ⟨hNoUB, ?_, ?_⟩
  · intro b hOk
    apply Execution.Reach.tail
    · apply Execution.Reach.tail
      · apply Execution.Reach.tail
        · exact Execution.Reach.refl (initState layout byte)
        · exact Or.inl ⟨layout, byte, rfl, hLayout, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨layout, byte, b, rfl, hOk, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨layout, byte, b, rfl, rfl, rfl⟩)))))
  · intro hRej
    apply Execution.Reach.tail
    · apply Execution.Reach.tail
      · exact Execution.Reach.refl (initState layout byte)
      · exact Or.inl ⟨layout, byte, rfl, hLayout, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨layout, byte, rfl, hRej, rfl⟩)))

theorem modular_fact_reuse_endpoint
    {layout : LayoutSpec} {impl : Nat} {cfg : Bool}
    {requireValidByte : Bool} {byte : Nat}
    (layoutCert : StructuralLayoutCert layout)
    (codecCert : CodecSemanticsCert impl cfg requireValidByte)
    (callerPremise : CallerValidityPremise requireValidByte byte) :
    EndpointSafeAndTyped layout impl cfg byte :=
  fresh_reconstruction_endpoint ⟨layoutCert, codecCert byte callerPremise⟩

theorem fresh_and_reused_endpoints_equivalent
    (layout : LayoutSpec) (impl : Nat) (cfg : Bool)
    (requireValidByte : Bool) (byte : Nat)
    (layoutCert : StructuralLayoutCert layout)
    (codecCert : CodecSemanticsCert impl cfg requireValidByte)
    (callerPremise : CallerValidityPremise requireValidByte byte) :
    FreshReconstructionConditions layout impl cfg byte ∧
    (FreshReconstructionConditions layout impl cfg byte ↔
      EndpointSafeAndTyped layout impl cfg byte) ∧
    EndpointSafeAndTyped layout impl cfg byte := by
  refine ⟨⟨layoutCert, codecCert byte callerPremise⟩, ?_,
    modular_fact_reuse_endpoint layoutCert codecCert callerPremise⟩
  constructor
  · exact fresh_reconstruction_endpoint
  · rintro ⟨hNoUB, _, _⟩
    refine ⟨layoutCert, ?_⟩
    intro hUB
    have hReachUB : Execution.Reach (DecodeStep impl cfg)
        (initState layout byte) (true, 7, layout, byte, false) := by
      apply Execution.Reach.tail
      · apply Execution.Reach.tail
        · exact Execution.Reach.refl (initState layout byte)
        · exact Or.inl ⟨layout, byte, rfl, layoutCert, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨layout, byte, rfl, hUB, rfl⟩))))
    exact Execution.bad_prefix_not_noUB (Bad := DecodeBad) hReachUB rfl hNoUB

theorem checked_decoder_safe_for_all_bytes_via_reuse
    (cfg : Bool) (byte : Nat) :
    EndpointSafeAndTyped boolSlotLayout 0 cfg byte ∧
    EndpointSafeAndTyped boolSlotLayout 0 cfg 2 ∧
    Execution.Reach (DecodeStep 0 cfg) (initState boolSlotLayout 2)
      (false, 5, boolSlotLayout, 2, false) := by
  have hLayout : StructuralLayoutCert boolSlotLayout := ⟨rfl, rfl, rfl, rfl⟩
  have hCodec : CodecSemanticsCert 0 cfg false := by
    rintro _ _ ⟨_, h2 | ⟨h3, _⟩⟩
    · exact Nat.noConfusion h2
    · exact Nat.noConfusion h3
  have hEndByte := modular_fact_reuse_endpoint (byte := byte) hLayout hCodec (Or.inl rfl)
  have hEnd2 := modular_fact_reuse_endpoint (byte := 2) hLayout hCodec (Or.inl rfl)
  rcases hEnd2 with ⟨hNoUB2, hOk2, hRejReach2⟩
  have hRej2 : CodecProducesReject 0 cfg 2 :=
    ⟨⟨fun h => Nat.noConfusion h, fun h => Nat.noConfusion (Nat.succ.inj h)⟩, Or.inl rfl⟩
  exact ⟨hEndByte, ⟨hNoUB2, hOk2, hRejReach2⟩, hRejReach2 hRej2⟩

theorem unchecked_decoder_safe_under_validBoolByte_via_reuse
    (cfg : Bool) (byte : Nat) (hValid : ValidBoolByte byte) :
    CallerValidityPremise true byte ∧
    EndpointSafeAndTyped boolSlotLayout 2 cfg byte := by
  have hLayout : StructuralLayoutCert boolSlotLayout := ⟨rfl, rfl, rfl, rfl⟩
  have hCodec : CodecSemanticsCert 2 cfg true := by
    rintro _ (hFalse | ⟨_, h0 | h1⟩) ⟨⟨hNe0, hNe1⟩, _⟩
    · exact Bool.noConfusion hFalse
    · exact hNe0 h0
    · exact hNe1 h1
  exact ⟨Or.inr ⟨rfl, hValid⟩,
    modular_fact_reuse_endpoint hLayout hCodec (Or.inr ⟨rfl, hValid⟩)⟩

theorem implementation_swap_reuses_layout_cert
    {layout : LayoutSpec} (layoutCert : StructuralLayoutCert layout)
    (cfg : Bool) (byte : Nat) :
    EndpointSafeAndTyped layout 0 cfg byte ∧
    EndpointSafeAndTyped layout 1 cfg byte ∧
    (CodecProducesReject 1 cfg byte ↔ CodecProducesReject 0 cfg byte) ∧
    (CodecProducesUB 1 cfg byte ↔ CodecProducesUB 0 cfg byte) := by
  have hCodec0 : CodecSemanticsCert 0 cfg false := by
    rintro _ _ ⟨_, h2 | ⟨h3, _⟩⟩
    · exact Nat.noConfusion h2
    · exact Nat.noConfusion h3
  have hCodec1 : CodecSemanticsCert 1 cfg false := by
    rintro _ _ ⟨_, h2 | ⟨h3, _⟩⟩
    · exact Nat.noConfusion (Nat.succ.inj h2)
    · exact Nat.noConfusion (Nat.succ.inj h3)
  refine ⟨modular_fact_reuse_endpoint layoutCert hCodec0 (Or.inl rfl),
    modular_fact_reuse_endpoint layoutCert hCodec1 (Or.inl rfl),
    ⟨fun ⟨hNe, _⟩ => ⟨hNe, Or.inl rfl⟩, fun ⟨hNe, _⟩ => ⟨hNe, Or.inr (Or.inl rfl)⟩⟩,
    ⟨fun h => False.elim (hCodec1 byte (Or.inl rfl) h),
     fun h => False.elim (hCodec0 byte (Or.inl rfl) h)⟩⟩

theorem client_edit_reuses_layout_and_codec_certs
    {layout : LayoutSpec} (layoutCert : StructuralLayoutCert layout)
    (cfg : Bool)
    (codecCert : CodecSemanticsCert 2 cfg true)
    {byteOld byteNew : Nat}
    (hOld : ValidBoolByte byteOld) (hNew : ValidBoolByte byteNew) :
    EndpointSafeAndTyped layout 2 cfg byteOld ∧
    EndpointSafeAndTyped layout 2 cfg byteNew :=
  ⟨modular_fact_reuse_endpoint layoutCert codecCert (Or.inr ⟨rfl, hOld⟩),
   modular_fact_reuse_endpoint layoutCert codecCert (Or.inr ⟨rfl, hNew⟩)⟩

#print axioms fresh_and_reused_endpoints_equivalent
#print axioms checked_decoder_safe_for_all_bytes_via_reuse
#print axioms unchecked_decoder_safe_under_validBoolByte_via_reuse
#print axioms implementation_swap_reuses_layout_cert
#print axioms client_edit_reuses_layout_and_codec_certs

end AnnealResearch.FactReuseValidation
