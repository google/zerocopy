module
import all Init.Data.Array.QSort.Basic
public section
namespace Miri.Memory.QSortProof
set_option autoImplicit false
theorem singleton {A : Type} (value : A) (less : A → A → Bool) :
    (#[value]).qsort less 0 0 = #[value] := by
  simp [Array.qsort,Array.qsort.sort]
end Miri.Memory.QSortProof
