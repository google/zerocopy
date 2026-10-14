import CapturedModule
open Aeneas Aeneas.Std Result
namespace ZerocopyCapture
 theorem bool_all (byte : U8) :
  zerocopy_probe.util.validity.bool_encoding byte = ok (decide (byte.val = 0 ∨ byte.val = 1)) := by
  unfold zerocopy_probe.util.validity.bool_encoding
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [UScalar.lt_equiv, UScalar.ofNatCore_val_eq, decide_eq_true_eq]
  omega
 theorem nonzero_all (n : Usize) :
  zerocopy_probe.util.validity.nonzero_encoding n = ok (decide (n.val ≠ 0)) := by
  unfold zerocopy_probe.util.validity.nonzero_encoding
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [bne_iff_ne, UScalar.eq_equiv]
#print axioms bool_all
#print axioms nonzero_all
end ZerocopyCapture
