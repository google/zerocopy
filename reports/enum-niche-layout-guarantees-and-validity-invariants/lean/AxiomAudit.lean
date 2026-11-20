/-
# Axiom audit (not part of the library target)

Prints the axioms used by every declaration that `results.json` references: the main results
first, then their non-vacuity witnesses, tightness counterexamples and positive controls.
Expected output for each: `[propext]`, `[propext, Quot.sound]`, `[propext, Classical.choice, Quot.sound]`,
a subset of these, or "does not depend on any axioms".

Run from this directory after `lake build`:

    lake env lean AxiomAudit.lean
-/
import Toy

#print axioms Toy.Niche.nicheLayout_lawful_iff_isNiche
#print axioms Toy.Niche.isNiche_enc_none_of_decSomeTransparent_of_decEnc
#print axioms Toy.Niche.someTransparent_lawful_iff_eq_nicheLayout
#print axioms Toy.Niche.opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc
#print axioms Toy.Niche.dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_decEnc_of_canonical
#print axioms Toy.Niche.dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_size_eq_of_numInvalid_le_one_of_decEnc
#print axioms Toy.Niche.opt_fromBytes_and_zero_iff_none_of_nichePinned_zero_of_numInvalid_le_one_of_decEnc
#print axioms Toy.Niche.nonePinned_zero_of_nonZero_of_decSomeTransparent_of_decEnc
#print axioms Toy.Niche.nonZero_layout_eq_nicheLayout_zero_of_decSomeTransparent_of_decEnc
#print axioms Toy.Niche.opt_bool_lawful_layouts_in_one_and_two_bytes
#print axioms Toy.Niche.opt_bool_none_pattern_not_forced_by_someTransparent_lawful
#print axioms Toy.Niche.nicheLayoutK_lawful_iff_injective_and_isNiche
#print axioms Toy.Niche.le_numInvalid_of_decEnc_of_size_le
#print axioms Toy.Niche.le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches
#print axioms Toy.Niche.opt_opt_nonZero_no_decEnc_layout_in_payload_size

#print axioms Toy.Niche.ce_canonical_fromBytes_drop_decEnc
#print axioms Toy.Niche.ce_canonical_fromBytes_drop_numInvalid
#print axioms Toy.Niche.ce_canonical_fromBytes_drop_size
#print axioms Toy.Niche.ce_documented_drop_decEnc
#print axioms Toy.Niche.ce_documented_drop_none_pin
#print axioms Toy.Niche.ce_documented_drop_numInvalid
#print axioms Toy.Niche.ce_documented_drop_size_pin
#print axioms Toy.Niche.ce_isNiche_enc_none_drop_decEnc
#print axioms Toy.Niche.ce_isNiche_enc_none_drop_decSomeTransparent
#print axioms Toy.Niche.ce_layout_determined_drop_decEnc
#print axioms Toy.Niche.ce_layout_determined_drop_decSomeTransparent
#print axioms Toy.Niche.ce_le_numInvalid_drop_decEnc
#print axioms Toy.Niche.ce_le_numInvalid_drop_size
#print axioms Toy.Niche.ce_nonePinned_zero_drop_decEnc
#print axioms Toy.Niche.ce_nonePinned_zero_drop_decSomeTransparent
#print axioms Toy.Niche.ce_zero_iff_none_drop_canonical
#print axioms Toy.Niche.ce_zero_iff_none_drop_decEnc
#print axioms Toy.Niche.ce_zero_iff_none_drop_nonePinned
#print axioms Toy.Niche.ce_zero_iff_none_drop_numInvalid
#print axioms Toy.Niche.ce_zero_iff_none_drop_size
#print axioms Toy.Niche.nv_decSomeTransparent_decEnc
#print axioms Toy.Niche.nv_documented
#print axioms Toy.Niche.nv_isNiche_enc_none
#print axioms Toy.Niche.nv_le_numInvalid
#print axioms Toy.Niche.nv_le_numInvalid_iff
#print axioms Toy.Niche.nv_nicheLayoutK
#print axioms Toy.Niche.nv_nicheLayout_lawful_iff_isNiche
#print axioms Toy.Niche.nv_opt_bool_none_pattern_not_forced
#print axioms Toy.Niche.nv_opt_canonical_and_fromBytes
#print axioms Toy.Niche.nv_opt_opt_nonZero
#print axioms Toy.Niche.nv_someTransparent_lawful_iff_eq_nicheLayout
#print axioms Toy.Niche.nv_zero_iff_none_lawful
#print axioms Toy.Niche.nv_zero_iff_none_size_numInvalid
#print axioms Toy.Niche.pc_isNiche_enc_none
#print axioms Toy.Niche.pc_le_numInvalid
#print axioms Toy.Niche.pc_nonZero_none_pattern_forced
#print axioms Toy.Niche.pc_opt_opt_nonZero
