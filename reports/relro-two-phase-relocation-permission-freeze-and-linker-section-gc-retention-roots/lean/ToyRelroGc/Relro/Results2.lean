import ToyRelroGc.Relro.Basic
import ToyRelroGc.Relro.Examples

/-!
Results 4 (page rounding of the protected range) and 5 (relocation order).
-/
namespace Toy.RelroGc

/-! ## Arithmetic helpers (floor division by the page size) -/

theorem alignDown_le (P a : Nat) : alignDown P a ≤ a := Nat.div_mul_le_self a P

theorem le_alignUp (P a : Nat) (hP : 0 < P) : a ≤ alignUp P a := by
  unfold alignUp
  have h1 := Nat.div_add_mod (a + P - 1) P
  have h2 := Nat.mod_lt (a + P - 1) hP
  rw [Nat.mul_comm] at h1
  generalize (a + P - 1) / P * P = X at *
  omega

theorem alignUp_eq_self_of_mod_eq_zero (P a : Nat) (hP : 0 < P) (h : a % P = 0) :
    alignUp P a = a := by
  unfold alignUp
  have ha : a = P * (a / P) := by have := Nat.div_add_mod a P; omega
  have e : a + P - 1 = (P - 1) + P * (a / P) := by omega
  rw [e, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt (by omega), Nat.zero_add, Nat.mul_comm]
  exact ha.symm

/-- Addresses between `alignDown P a` and `a` lie on `a`'s page. -/
theorem div_eq_of_alignDown_le (P a b : Nat) (hP : 0 < P) (h1 : alignDown P a ≤ b) (h2 : b ≤ a) :
    b / P = a / P := by
  apply Nat.le_antisymm
  · exact Nat.div_le_div_right h2
  · exact (Nat.le_div_iff_mul_le hP).mpr h1

/-- For `a ≥ 1`, addresses in `[a, alignUp P a)` lie on the page of `a - 1`. -/
theorem div_eq_of_lt_alignUp (P a b : Nat) (hP : 0 < P) (ha : 1 ≤ a) (h1 : a ≤ b)
    (h2 : b < alignUp P a) : b / P = (a - 1) / P := by
  have e : (a + P - 1) / P = (a - 1) / P + 1 := by
    rw [show a + P - 1 = (a - 1) + P from by omega, Nat.add_div_right _ hP]
  unfold alignUp at h2
  rw [e] at h2
  apply Nat.le_antisymm
  · have := (Nat.div_lt_iff_lt_mul hP).mpr h2
    omega
  · exact Nat.div_le_div_right (by omega)

/-- An address on the page of some `a' ≥ a` is at least `alignDown P a`. -/
theorem alignDown_le_of_div_ge (P a b : Nat) (h : a / P ≤ b / P) : alignDown P a ≤ b :=
  Nat.le_trans (Nat.mul_le_mul_right P h) (Nat.div_mul_le_self b P)

/-- An address on the page of some `a' < a` is below `alignUp P a`. -/
theorem lt_alignUp_of_div_le (P a b : Nat) (hP : 0 < P) (ha : 1 ≤ a) (h : b / P ≤ (a - 1) / P) :
    b < alignUp P a := by
  have e : (a + P - 1) / P = (a - 1) / P + 1 := by
    rw [show a + P - 1 = (a - 1) + P from by omega, Nat.add_div_right _ hP]
  unfold alignUp
  rw [e]
  have h1 : b < (b / P + 1) * P := by
    have := Nat.div_add_mod b P
    have := Nat.mod_lt b hP
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega
  exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right P (by omega))

/-! ## Result 4: page granularity -/

/-- **Down-down rounding never covers a mutable byte, given a clean first page.** If the RELRO
bytes are exactly `[rs, re)` and no mutable byte lies in `[alignDown P rs, rs)` (the bytes of
the page of address `rs` below `rs`, with `alignDown` by floor division; for `P > 0` this range
is empty when `rs % P = 0`, for `P = 0` it is `[0, rs)`, and it is defined also when `rs = re`),
then the down-down mask covers no mutable byte. -/
theorem downDown_avoidsMut_of_firstPage_noMut (P rs re : Nat) (L : List Kind)
    (hR : RelroIs L rs re) (hFirst : NoMutIn L (alignDown P rs) rs) :
    AvoidsMut L (roundedMask .downDown P rs re) := by
  intro a ha hk
  simp only [roundedMask, rangeMask, decide_eq_false_iff_not, not_and, Nat.not_lt]
  intro hlo
  apply Nat.le_of_not_lt
  intro hhi
  have hhi' : a < re := Nat.lt_of_lt_of_le hhi (alignDown_le P re)
  have hnr : ¬ (rs ≤ a ∧ a < re) := by
    rw [← hR.2.2 a ha, hk]; simp
  have has : a < rs := by omega
  exact hFirst a has hlo hk

/-- **Down-down rounding covers all RELRO bytes iff the RELRO end is page-aligned.** If the
RELRO bytes are exactly the non-empty range `[rs, re)`, the down-down mask (ends rounded down by
floor division) covers every RELRO byte iff `re % P = 0` (Nat modulo, with `re % 0 = re`; for
`P = 0` both sides are false). -/
theorem downDown_coversRelro_iff_end_aligned (P rs re : Nat) (L : List Kind)
    (hR : RelroIs L rs re) (hne : rs < re) :
    CoversRelro L (roundedMask .downDown P rs re) ↔ re % P = 0 := by
  obtain ⟨_, hle, hiff⟩ := hR
  constructor
  · intro h
    have hlast : L[re - 1]? = some .relro := (hiff (re - 1) (by omega)).mpr ⟨by omega, by omega⟩
    have := h (re - 1) (by omega) hlast
    simp only [roundedMask, rangeMask, decide_eq_true_eq] at this
    have h1 := Nat.div_add_mod re P
    have h2 := alignDown_le P re
    unfold alignDown at this h2
    rw [Nat.mul_comm] at h1
    generalize re / P * P = X at *
    omega
  · intro hmod a ha hk
    have ⟨h1, h2⟩ := (hiff a ha).mp hk
    have hal : alignDown P re = re := by
      unfold alignDown
      have := Nat.div_add_mod re P
      rw [Nat.mul_comm] at this
      omega
    simp only [roundedMask, rangeMask, hal, decide_eq_true_eq]
    exact ⟨Nat.le_trans (alignDown_le P rs) h1, h2⟩

/-- **Down-up rounding covers all RELRO bytes.** For page size `P > 0` and RELRO bytes exactly
`[rs, re)`, the down-up mask covers every RELRO byte (for an empty range `rs = re` there is no
RELRO byte to cover). -/
theorem downUp_coversRelro (P rs re : Nat) (L : List Kind) (hP : 0 < P)
    (hR : RelroIs L rs re) : CoversRelro L (roundedMask .downUp P rs re) := by
  intro a ha hk
  have ⟨h1, h2⟩ := (hR.2.2 a ha).mp hk
  have hne : rs < re := by omega
  simp only [roundedMask, hne, ite_true, rangeMask, decide_eq_true_eq]
  exact ⟨Nat.le_trans (alignDown_le P rs) h1, Nat.lt_of_lt_of_le h2 (le_alignUp P re hP)⟩

/-- **Down-up rounding covers no mutable byte iff the partial first and last pages hold no
mutable byte.** For page size `P > 0` and RELRO bytes exactly the non-empty range `[rs, re)`:
the down-up mask avoids every mutable byte iff no mutable byte lies in `[alignDown P rs, rs)` or
in `[re, alignUp P re)` (`alignDown`, `alignUp` by floor division). -/
theorem downUp_avoidsMut_iff_partialPages_noMut (P rs re : Nat) (L : List Kind) (hP : 0 < P)
    (hR : RelroIs L rs re) (hne : rs < re) :
    AvoidsMut L (roundedMask .downUp P rs re) ↔
      NoMutIn L (alignDown P rs) rs ∧ NoMutIn L re (alignUp P re) := by
  obtain ⟨hrsre, _, hiff⟩ := hR
  have hm : roundedMask .downUp P rs re = rangeMask (alignDown P rs) (alignUp P re) := by
    simp [roundedMask, hne]
  rw [hm]
  constructor
  · intro h
    refine ⟨fun a ha hlo hk => ?_, fun a ha hlo hk => ?_⟩
    · have hlen : a < L.length := (List.getElem?_eq_some_iff.mp hk).1
      have := h a hlen hk
      simp only [rangeMask, decide_eq_false_iff_not, not_and, Nat.not_lt] at this
      have := this hlo
      have := le_alignUp P re hP
      omega
    · have hlen : a < L.length := (List.getElem?_eq_some_iff.mp hk).1
      have := h a hlen hk
      simp only [rangeMask, decide_eq_false_iff_not, not_and, Nat.not_lt] at this
      have := this (Nat.le_trans (alignDown_le P rs) (by omega))
      omega
  · rintro ⟨hF, hL⟩ a ha hk
    simp only [rangeMask, decide_eq_false_iff_not, not_and, Nat.not_lt]
    intro hlo
    apply Nat.le_of_not_lt
    intro hhi'
    have hnr : ¬ (rs ≤ a ∧ a < re) := by
      rw [← hiff a ha, hk]; simp
    by_cases has : a < rs
    · exact hF a has hlo hk
    · exact hL a hhi' (by omega) hk

/-- **Page-granular protection with integrity and no spurious fault exists iff no page holds
both a RELRO byte and a mutable byte.** For any layout and page size `P` (for `P = 0` every
address is on page `0`): some page-granular mask covers every RELRO byte and no mutable byte
iff `NoSharedPage P L`. -/
theorem exists_pageGranular_covers_avoids_iff_noSharedPage (P : Nat) (L : List Kind) :
    (∃ m, PageGranular P m ∧ CoversRelro L m ∧ AvoidsMut L m) ↔ NoSharedPage P L := by
  constructor
  · rintro ⟨m, hg, hc, ha⟩ a hal b hbl hab hka hkb
    have h1 := hc a hal hka
    have h2 := ha b hbl hkb
    rw [hg a b hab] at h1
    rw [h1] at h2
    exact Bool.noConfusion h2
  · intro h
    refine ⟨fun a => decide (∃ b, b < L.length ∧ b / P = a / P ∧ L[b]? = some .relro),
      ?_, ?_, ?_⟩
    · intro a a' haa
      simp only [haa]
    · intro a hal hka
      simp only [decide_eq_true_eq]
      exact ⟨a, hal, rfl, hka⟩
    · intro b hbl hkb
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro a hal hab hka
      exact h a hal b hbl hab hka hkb

/-- **Interval form.** For page size `P > 0` and RELRO bytes exactly the non-empty range
`[rs, re)`: no page holds both a RELRO and a mutable byte iff no mutable byte lies in
`[alignDown P rs, rs)` or in `[re, alignUp P re)`. -/
theorem noSharedPage_iff_partialPages_noMut (P rs re : Nat) (L : List Kind) (hP : 0 < P)
    (hR : RelroIs L rs re) (hne : rs < re) :
    NoSharedPage P L ↔ NoMutIn L (alignDown P rs) rs ∧ NoMutIn L re (alignUp P re) := by
  obtain ⟨_, hle, hiff⟩ := hR
  constructor
  · intro h
    refine ⟨fun b hb hlo hk => ?_, fun b hb hlo hk => ?_⟩
    · have hbl : b < L.length := (List.getElem?_eq_some_iff.mp hk).1
      have hrs : L[rs]? = some .relro := (hiff rs (by omega)).mpr ⟨Nat.le_refl _, hne⟩
      exact h rs (by omega) b hbl (div_eq_of_alignDown_le P rs b hP hlo (by omega)).symm hrs hk
    · have hbl : b < L.length := (List.getElem?_eq_some_iff.mp hk).1
      have hre : L[re - 1]? = some .relro := (hiff (re - 1) (by omega)).mpr ⟨by omega, by omega⟩
      exact h (re - 1) (by omega) b hbl
        (div_eq_of_lt_alignUp P re b hP (by omega) hlo hb).symm hre hk
  · rintro ⟨hF, hL⟩ a hal b hbl hab hka hkb
    have ⟨h1, h2⟩ := (hiff a hal).mp hka
    have hnr : ¬ (rs ≤ b ∧ b < re) := by
      rw [← hiff b hbl, hkb]; simp
    by_cases hb : b < rs
    · exact hF b hb (alignDown_le_of_div_ge P rs b (hab ▸ Nat.div_le_div_right h1)) hkb
    · exact hL b (lt_alignUp_of_div_le P re b hP (by omega)
        (hab ▸ Nat.div_le_div_right (by omega))) (by omega) hkb

/-- **Corrected page-exact RELRO characterization.** For page size `P > 0` and RELRO bytes
exactly the non-empty range `[rs, re)`: some page-granular mask covers every RELRO byte and no
mutable byte iff no mutable byte lies in `[alignDown P rs, rs)` and none lies in
`[re, alignUp P re)`. (When `re % P = 0`, the second range is empty:
`alignUp_eq_self_of_mod_eq_zero`.) -/
theorem exists_pageGranular_covers_avoids_iff_partialPages_noMut (P rs re : Nat) (L : List Kind)
    (hP : 0 < P) (hR : RelroIs L rs re) (hne : rs < re) :
    (∃ m, PageGranular P m ∧ CoversRelro L m ∧ AvoidsMut L m) ↔
      NoMutIn L (alignDown P rs) rs ∧ NoMutIn L re (alignUp P re) :=
  (exists_pageGranular_covers_avoids_iff_noSharedPage P L).trans
    (noSharedPage_iff_partialPages_noMut P rs re L hP hR hne)

/-- An empty or inverted RELRO range (`re ≤ rs`) protects nothing under every rounding policy. -/
theorem roundedMask_eq_false_of_le (pol : Rounding) (P rs re : Nat) (h : re ≤ rs) (a : Nat) :
    roundedMask pol P rs re a = false := by
  cases pol with
  | downDown =>
    have hal : alignDown P re ≤ alignDown P rs := by
      unfold alignDown; exact Nat.mul_le_mul_right P (Nat.div_le_div_right h)
    simp only [roundedMask, rangeMask, decide_eq_false_iff_not, not_and, Nat.not_lt]
    intro h1
    omega
  | downUp =>
    simp [roundedMask, Nat.not_lt.mpr h]
  | exact =>
    simp only [roundedMask, rangeMask, decide_eq_false_iff_not, not_and, Nat.not_lt]
    omega

/-- The down-down mask is page-granular for every page size, including `P = 0`. -/
theorem roundedMask_downDown_pageGranular (P rs re : Nat) :
    PageGranular P (roundedMask .downDown P rs re) := by
  intro a b hab
  simp only [roundedMask, rangeMask, alignDown]
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · simp
  · have h1 : rs / P * P ≤ a ↔ rs / P ≤ a / P := (Nat.le_div_iff_mul_le hP).symm
    have h2 : rs / P * P ≤ b ↔ rs / P ≤ b / P := (Nat.le_div_iff_mul_le hP).symm
    have h3 : a < re / P * P ↔ a / P < re / P := (Nat.div_lt_iff_lt_mul hP).symm
    have h4 : b < re / P * P ↔ b / P < re / P := (Nat.div_lt_iff_lt_mul hP).symm
    simp [h1, h2, h3, h4, hab]

/-- The down-up mask is page-granular for every page size, including `P = 0`. -/
theorem roundedMask_downUp_pageGranular (P rs re : Nat) :
    PageGranular P (roundedMask .downUp P rs re) := by
  intro a b hab
  by_cases hne : rs < re
  · simp only [roundedMask, hne, ite_true, rangeMask, alignDown, alignUp]
    rcases Nat.eq_zero_or_pos P with rfl | hP
    · simp
    · have h1 : rs / P * P ≤ a ↔ rs / P ≤ a / P := (Nat.le_div_iff_mul_le hP).symm
      have h2 : rs / P * P ≤ b ↔ rs / P ≤ b / P := (Nat.le_div_iff_mul_le hP).symm
      have h3 : a < (re + P - 1) / P * P ↔ a / P < (re + P - 1) / P :=
        (Nat.div_lt_iff_lt_mul hP).symm
      have h4 : b < (re + P - 1) / P * P ↔ b / P < (re + P - 1) / P :=
        (Nat.div_lt_iff_lt_mul hP).symm
      simp [h1, h2, h3, h4, hab]
  · simp [roundedMask, hne]

/-- **Down-up rounding is optimal among page-granular masks.** For page size `P > 0` and RELRO
bytes exactly the non-empty range `[rs, re)`: the single interval `roundedMask .downUp P rs re`
covers every RELRO byte and no mutable byte iff some page-granular mask does. -/
theorem downUp_covers_avoids_iff_exists_pageGranular (P rs re : Nat) (L : List Kind)
    (hP : 0 < P) (hR : RelroIs L rs re) (hne : rs < re) :
    (CoversRelro L (roundedMask .downUp P rs re) ∧ AvoidsMut L (roundedMask .downUp P rs re)) ↔
      ∃ m, PageGranular P m ∧ CoversRelro L m ∧ AvoidsMut L m := by
  rw [exists_pageGranular_covers_avoids_iff_partialPages_noMut P rs re L hP hR hne,
    ← downUp_avoidsMut_iff_partialPages_noMut P rs re L hP hR hne]
  exact ⟨fun h => h.2, fun h => ⟨downUp_coversRelro P rs re L hP hR, h⟩⟩

/-- **`NoSharedPage` does not give a single protected interval for non-contiguous RELRO.**
With `P = 1` and layout `[relro, mutable, relro]`, no page holds both a RELRO and a mutable
byte, yet no interval `[lo, hi)` covers both RELRO bytes without covering the mutable byte. -/
theorem noncontiguous_relro_noSharedPage_no_single_interval :
    NoSharedPage 1 [.relro, .mutable, .relro] ∧
      ¬ ∃ lo hi : Nat, CoversRelro [.relro, .mutable, .relro] (rangeMask lo hi) ∧
        AvoidsMut [.relro, .mutable, .relro] (rangeMask lo hi) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨lo, hi, hc, ha⟩
  have h0 := hc 0 (by decide) rfl
  have h2 := hc 2 (by decide) rfl
  have h1 := ha 1 (by decide) rfl
  simp only [rangeMask, decide_eq_true_eq, decide_eq_false_iff_not] at h0 h2 h1
  omega

/-! ### Result 4: concrete witnesses (page size 2) -/

/-- Three RELRO bytes `[0, 3)`. -/
def layoutRelro3 : List Kind := [.relro, .relro, .relro]
/-- Three RELRO bytes `[0, 3)` followed by a mutable byte sharing the second page. -/
def layoutRelro3Mut : List Kind := [.relro, .relro, .relro, .mutable]
/-- A mutable byte followed by one RELRO byte `[1, 2)`; the RELRO end `2` is page-aligned. -/
def layoutMutRelro : List Kind := [.mutable, .relro]

/-- Loader input protecting `layout` with mask `m` (no relocations). -/
def protCfg (layout : List Kind) (m : Nat → Bool) : Cfg :=
  ⟨layout, fun _ => 0, [], m, [], 0⟩

/-- **Down-down leaves an unpadded RELRO tail writable.** RELRO is `[0, 3)` with `P = 2`
(end not aligned): the down-down mask misses RELRO byte 2, and a program write to byte 2
succeeds. -/
theorem downDown_unpaddedEnd_tail_write_succeeds :
    RelroIs layoutRelro3 0 3 ∧ 3 % 2 ≠ 0 ∧
      ¬ CoversRelro layoutRelro3 (roundedMask .downDown 2 0 3) ∧
      (trace (protCfg layoutRelro3 (roundedMask .downDown 2 0 3)) sa0
        (twoPhase (protCfg layoutRelro3 (roundedMask .downDown 2 0 3)) [.write 2 9])).opOuts =
        [.ok] := by
  decide

/-- **Down-up faults a legal write to a mutable byte sharing the last RELRO page.** RELRO is
`[0, 3)` with `P = 2` and byte 3 mutable: the down-up mask covers all RELRO bytes and also
byte 3, and a program write to byte 3 faults. -/
theorem downUp_sharedLastPage_mut_write_faults :
    RelroIs layoutRelro3Mut 0 3 ∧ CoversRelro layoutRelro3Mut (roundedMask .downUp 2 0 3) ∧
      ¬ AvoidsMut layoutRelro3Mut (roundedMask .downUp 2 0 3) ∧
      (trace (protCfg layoutRelro3Mut (roundedMask .downUp 2 0 3)) sa0
        (twoPhase (protCfg layoutRelro3Mut (roundedMask .downUp 2 0 3)) [.write 3 9])).opOuts =
        [.fault] := by
  decide

/-- **End alignment and a clean last page do not suffice (start-of-region effect).** RELRO is
`[1, 2)` with `P = 2`: the RELRO end is page-aligned and `[re, alignUp P re)` is empty, yet a
mutable byte shares the first RELRO page, so no page-granular mask covers every RELRO byte and
no mutable byte; concretely the down-down mask covers RELRO but also mutable byte 0, and a
program write to byte 0 faults. -/
theorem endAligned_firstPage_mut_no_pageGranular_protection :
    RelroIs layoutMutRelro 1 2 ∧ 2 % 2 = 0 ∧ NoMutIn layoutMutRelro 2 (alignUp 2 2) ∧
      ¬ (∃ m, PageGranular 2 m ∧ CoversRelro layoutMutRelro m ∧ AvoidsMut layoutMutRelro m) ∧
      CoversRelro layoutMutRelro (roundedMask .downDown 2 1 2) ∧
      ¬ AvoidsMut layoutMutRelro (roundedMask .downDown 2 1 2) ∧
      (trace (protCfg layoutMutRelro (roundedMask .downDown 2 1 2)) sa0
        (twoPhase (protCfg layoutMutRelro (roundedMask .downDown 2 1 2)) [.write 0 9])).opOuts =
        [.fault] := by
  refine ⟨by decide, by decide, by decide, ?_, by decide, by decide, by decide⟩
  rintro ⟨m, hg, hc, ha⟩
  have h1 := hc 1 (by decide) rfl
  have h0 := ha 0 (by decide) rfl
  rw [hg 0 1 (by decide), h1] at h0
  exact Bool.noConfusion h0

/-- `downDown_avoidsMut_of_firstPage_noMut`: its first-page hypothesis is tight
(`layoutMutRelro`: RELRO is exactly `[1, 2)`, the first page holds mutable byte 0, and the
down-down mask covers byte 0). -/
theorem downDown_avoidsMut_cex_firstPage :
    RelroIs layoutMutRelro 1 2 ∧ ¬ NoMutIn layoutMutRelro (alignDown 2 1) 1 ∧
      ¬ AvoidsMut layoutMutRelro (roundedMask .downDown 2 1 2) := by
  decide

/-- `downDown_coversRelro_iff_end_aligned`: non-emptiness is tight (empty RELRO at `[1, 1)`
over `[mutable]`, `P = 2`: `RelroIs` holds, `1 < 1` fails, the mask covers all (zero) RELRO bytes
but `1 % 2 ≠ 0`). -/
theorem downDown_coversRelro_iff_cex_empty :
    RelroIs [.mutable] 1 1 ∧ ¬ ((1 : Nat) < 1) ∧
      ¬ (CoversRelro [.mutable] (roundedMask .downDown 2 1 1) ↔ 1 % 2 = 0) := by
  decide

/-- `downDown_coversRelro_iff_end_aligned`: `RelroIs` is tight (the range `[0, 2)` is claimed
but byte 2 is also RELRO: the end is aligned yet byte 2 is not covered). -/
theorem downDown_coversRelro_iff_cex_relroIs :
    ¬ RelroIs layoutRelro3 0 2 ∧ (0 : Nat) < 2 ∧
      ¬ (CoversRelro layoutRelro3 (roundedMask .downDown 2 0 2) ↔ 2 % 2 = 0) := by
  decide

/-- `downUp_coversRelro`: `0 < P` is tight (`P = 0` gives the empty mask). -/
theorem downUp_coversRelro_cex_pageZero :
    ¬ ((0 : Nat) < 0) ∧ RelroIs layoutRelro3 0 3 ∧
      ¬ CoversRelro layoutRelro3 (roundedMask .downUp 0 0 3) := by
  decide

/-- `downUp_avoidsMut_iff_partialPages_noMut`: `0 < P` is tight. -/
theorem downUp_avoidsMut_iff_cex_pageZero :
    ¬ ((0 : Nat) < 0) ∧ RelroIs layoutMutRelro 1 2 ∧ (1 : Nat) < 2 ∧
      ¬ (AvoidsMut layoutMutRelro (roundedMask .downUp 0 1 2) ↔
        NoMutIn layoutMutRelro (alignDown 0 1) 1 ∧ NoMutIn layoutMutRelro 2 (alignUp 0 2)) := by
  decide

/-- `downUp_avoidsMut_iff_partialPages_noMut`: non-emptiness is tight (empty RELRO `[1, 1)` over
`[mutable]` with `P = 2`: the guarded down-up mask is empty and avoids the mutable byte, but the
mutable byte 0 lies in `[alignDown 2 1, 1)`). -/
theorem downUp_avoidsMut_iff_cex_empty :
    (0 : Nat) < 2 ∧ RelroIs [.mutable] 1 1 ∧ ¬ ((1 : Nat) < 1) ∧
      ¬ (AvoidsMut [.mutable] (roundedMask .downUp 2 1 1) ↔
        NoMutIn [.mutable] (alignDown 2 1) 1 ∧ NoMutIn [.mutable] 1 (alignUp 2 1)) := by
  decide

/-- `noSharedPage_iff_partialPages_noMut`: non-emptiness is tight. -/
theorem noSharedPage_iff_cex_empty :
    (0 : Nat) < 2 ∧ RelroIs [.mutable] 1 1 ∧ ¬ ((1 : Nat) < 1) ∧
      ¬ (NoSharedPage 2 [.mutable] ↔
        NoMutIn [.mutable] (alignDown 2 1) 1 ∧ NoMutIn [.mutable] 1 (alignUp 2 1)) := by
  decide

/-- `noSharedPage_iff_partialPages_noMut`: `0 < P` is tight. -/
theorem noSharedPage_iff_cex_pageZero :
    ¬ ((0 : Nat) < 0) ∧ RelroIs [.relro, .mutable] 0 1 ∧ (0 : Nat) < 1 ∧
      ¬ (NoSharedPage 0 [.relro, .mutable] ↔
        NoMutIn [.relro, .mutable] (alignDown 0 0) 0 ∧
          NoMutIn [.relro, .mutable] 1 (alignUp 0 1)) := by
  decide

/-- Instance of the page-rounding results: RELRO `[0, 2)` over `[relro, relro, mutable]` with
`P = 2` satisfies every hypothesis, and both rounding policies give protection without a
spurious fault. -/
theorem pageRounding_nonvacuity :
    0 < 2 ∧ RelroIs [.relro, .relro, .mutable] 0 2 ∧ 0 < 2 ∧
      NoMutIn [.relro, .relro, .mutable] (alignDown 2 0) 0 ∧
      CoversRelro [.relro, .relro, .mutable] (roundedMask .downDown 2 0 2) ∧
      AvoidsMut [.relro, .relro, .mutable] (roundedMask .downDown 2 0 2) ∧
      CoversRelro [.relro, .relro, .mutable] (roundedMask .downUp 2 0 2) ∧
      AvoidsMut [.relro, .relro, .mutable] (roundedMask .downUp 2 0 2) := by
  decide

/-! ## Result 5: relocation order -/

/-- Two relocations that read only `S`, write outside `S`, and write different slots commute. -/
theorem applyReloc_comm (sa : SymTab) (S : Nat → Prop) (x y : Reloc)
    (hx : x.ReadsOnly S) (hy : y.ReadsOnly S) (hxs : ¬ S x.slot) (hys : ¬ S y.slot)
    (hne : x.slot ≠ y.slot) (m : Mem) :
    applyReloc sa (applyReloc sa m x) y = applyReloc sa (applyReloc sa m y) x := by
  have e1 : y.val sa (upd m x.slot (x.val sa m)) = y.val sa m := by
    apply hy sa
    intro a ha
    have : a ≠ x.slot := fun h => hxs (h ▸ ha)
    simp [upd, this]
  have e2 : x.val sa (upd m y.slot (y.val sa m)) = x.val sa m := by
    apply hx sa
    intro a ha
    have : a ≠ y.slot := fun h => hys (h ▸ ha)
    simp [upd, this]
  funext b
  simp only [applyReloc, upd, e1, e2]
  by_cases h1 : b = y.slot <;> by_cases h2 : b = x.slot <;> simp_all

/-- Order independence for relocations that read only `S`, write outside `S`, and write
pairwise distinct slots: any two orders that are permutations of each other give the same
image. -/
theorem applyAll_perm_of_readsOnly_of_slots_outside (sa : SymTab) (S : Nat → Prop)
    {rs rs' : List Reloc} (p : rs.Perm rs') :
    (∀ r ∈ rs, r.ReadsOnly S) → (∀ r ∈ rs, ¬ S r.slot) → (rs.map Reloc.slot).Nodup →
      ∀ m, applyAll sa rs m = applyAll sa rs' m := by
  induction p with
  | nil => intros; rfl
  | cons x p ih =>
    intro hR hS hN m
    simp only [applyAll, List.foldl_cons]
    exact ih (fun r hr => hR r (List.mem_cons_of_mem _ hr))
      (fun r hr => hS r (List.mem_cons_of_mem _ hr)) (List.nodup_cons.mp hN).2 _
  | swap x y l =>
    intro hR hS hN m
    simp only [applyAll, List.foldl_cons]
    have hne : y.slot ≠ x.slot := by
      have := (List.nodup_cons.mp hN).1
      simp only [List.map_cons, List.mem_cons, not_or] at this
      exact this.1
    rw [applyReloc_comm sa S y x (hR y (by simp)) (hR x (by simp)) (hS y (by simp))
      (hS x (by simp)) hne m]
  | trans p1 p2 ih1 ih2 =>
    intro hR hS hN m
    rw [ih1 hR hS hN m]
    exact ih2 (fun r hr => hR r (p1.mem_iff.mpr hr)) (fun r hr => hS r (p1.mem_iff.mpr hr))
      ((p1.map Reloc.slot).nodup_iff.mp hN) m

/-- **Order independence of address-only relocations.** If every relocation's value depends
only on symbol addresses and the relocations write pairwise distinct slots, then every
permutation of the application order yields the same image. -/
theorem applyAll_perm_of_addressOnly_of_nodup_slots (sa : SymTab) {rs rs' : List Reloc}
    (p : rs.Perm rs') (hA : ∀ r ∈ rs, r.AddressOnly) (hN : (rs.map Reloc.slot).Nodup)
    (m : Mem) : applyAll sa rs m = applyAll sa rs' m :=
  applyAll_perm_of_readsOnly_of_slots_outside sa (fun _ => False) p
    (fun r hr sa m m' _ => hA r hr sa m m') (fun _ _ h => h) hN m

/-- **Resolvers after address-only relocations.** Let `A` be address-only relocations with
pairwise distinct slots, and `R` resolver relocations with pairwise distinct slots, each reading
memory only at addresses that no relocation of `R` writes (it may read any slot of `A` that no
relocation of `R` writes, and any other memory not written by `R`). Then permuting `A` and `R`
separately and applying all of `A` before any of `R` (`A' ++ R'`) gives the image of `A ++ R`. -/
theorem applyAll_append_perm_of_resolvers_read_no_resolver_slot (sa : SymTab)
    (A R A' R' : List Reloc) (hA : ∀ r ∈ A, r.AddressOnly) (hNA : (A.map Reloc.slot).Nodup)
    (hR : ∀ r ∈ R, r.ReadsOnly (fun a => a ∉ R.map Reloc.slot))
    (hNR : (R.map Reloc.slot).Nodup) (pA : A'.Perm A) (pR : R'.Perm R) (m : Mem) :
    applyAll sa (A' ++ R') m = applyAll sa (A ++ R) m := by
  have e1 : applyAll sa A' m = applyAll sa A m :=
    (applyAll_perm_of_addressOnly_of_nodup_slots sa pA.symm hA hNA m).symm
  have hout : ∀ r ∈ R, ¬ (r.slot ∉ R.map Reloc.slot) :=
    fun r hr hn => hn (List.mem_map_of_mem hr)
  have e2 : ∀ x, applyAll sa R' x = applyAll sa R x := fun x =>
    (applyAll_perm_of_readsOnly_of_slots_outside sa _ pR.symm hR hout hNR x).symm
  simp only [applyAll, List.foldl_append] at e1 e2 ⊢
  rw [e1, e2]

/-! ### Result 5: concrete witnesses -/

/-- Address-only relocation: slot 0 gets the address of symbol 0. -/
def rAddr0 : Reloc := symReloc 0 0
/-- Resolver relocation: slot 1 gets the current contents of slot 0. -/
def rRes1 : Reloc := ⟨1, fun _ m => m 0⟩

/-- **A resolver that reads a not-yet-relocated slot is order-dependent.** The two orders of
`rAddr0` and `rRes1` are permutations of each other with distinct slots, `rRes1` is not
address-only, and slot 1 ends up `100` in one order and `0` in the other. -/
theorem resolver_reads_unrelocated_slot_order_dependent :
    [rAddr0, rRes1].Perm [rRes1, rAddr0] ∧ ([rAddr0, rRes1].map Reloc.slot).Nodup ∧
      ¬ (∀ r ∈ [rAddr0, rRes1], r.AddressOnly) ∧
      applyAll sa0 [rAddr0, rRes1] (fun _ => 0) ≠ applyAll sa0 [rRes1, rAddr0] (fun _ => 0) ∧
      applyAll sa0 [rAddr0, rRes1] (fun _ => 0) 1 = 100 ∧
      applyAll sa0 [rRes1, rAddr0] (fun _ => 0) 1 = 0 := by
  refine ⟨List.Perm.swap _ _ _, by decide, fun h => ?_, fun h => ?_, by decide, by decide⟩
  · have := h rRes1 (by simp) sa0 (fun _ => 0) (fun _ => 1)
    simp [rRes1] at this
  · have := congrFun h 1
    revert this
    decide

/-- `applyAll_perm_of_addressOnly_of_nodup_slots`: the distinct-slot hypothesis is tight (two
address-only relocations of slot 0 with different values: the last one wins). -/
theorem addressOnly_same_slot_order_dependent :
    [symReloc 0 0, symReloc 0 1].Perm [symReloc 0 1, symReloc 0 0] ∧
      (∀ r ∈ [symReloc 0 0, symReloc 0 1], r.AddressOnly) ∧
      ¬ ([symReloc 0 0, symReloc 0 1].map Reloc.slot).Nodup ∧
      applyAll sa0 [symReloc 0 0, symReloc 0 1] (fun _ => 0) ≠
        applyAll sa0 [symReloc 0 1, symReloc 0 0] (fun _ => 0) := by
  refine ⟨List.Perm.swap _ _ _, ?_, by decide, fun h => ?_⟩
  · intro r hr sa m m'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  · have := congrFun h 0
    revert this
    decide

/-- Second resolver: slot 2 gets the current contents of slot 1. -/
def rRes2of1 : Reloc := ⟨2, fun _ m => m 1⟩

/-- `applyAll_append_perm_of_resolvers_read_no_resolver_slot`: the read restriction `hR` is tight.
With `A = []` and `R = [symReloc 1 0, rRes2of1]` (the second resolver reads slot 1, written by
`R`), every other hypothesis holds and the two orders of `R` differ. -/
theorem resolvers_read_resolver_slot_order_dependent :
    (∀ r ∈ ([] : List Reloc), r.AddressOnly) ∧ (([] : List Reloc).map Reloc.slot).Nodup ∧
      ¬ (∀ r ∈ [symReloc 1 0, rRes2of1],
          r.ReadsOnly (fun a => a ∉ [symReloc 1 0, rRes2of1].map Reloc.slot)) ∧
      ([symReloc 1 0, rRes2of1].map Reloc.slot).Nodup ∧
      ([] : List Reloc).Perm [] ∧ [rRes2of1, symReloc 1 0].Perm [symReloc 1 0, rRes2of1] ∧
      applyAll sa0 ([] ++ [rRes2of1, symReloc 1 0]) (fun _ => 0) ≠
        applyAll sa0 ([] ++ [symReloc 1 0, rRes2of1]) (fun _ => 0) := by
  refine ⟨by simp, by decide, fun h => ?_, by decide, List.Perm.refl _, List.Perm.swap _ _ _,
    fun h => ?_⟩
  · have := h rRes2of1 (by simp) sa0 (fun _ => 0) (fun a => if a = 1 then 1 else 0)
      (by intro a ha; simp [symReloc, rRes2of1] at ha; simp [ha.1])
    simp [rRes2of1] at this
  · have := congrFun h 2
    revert this
    decide

/-- Resolver that overwrites slot 0 with a constant. -/
def rConst0 : Reloc := ⟨0, fun _ _ => 5⟩

/-- `applyAll_append_perm_of_resolvers_read_no_resolver_slot`: a second witness for `hR`. With
`A = [rAddr0]` and `R = [rConst0, rRes1]` (`rConst0` overwrites slot 0, which `rRes1` reads),
every other hypothesis holds and the two orders of `R` differ. -/
theorem resolver_overwrites_addressOnly_slot_order_dependent :
    (∀ r ∈ [rAddr0], r.AddressOnly) ∧ ([rAddr0].map Reloc.slot).Nodup ∧
      ¬ (∀ r ∈ [rConst0, rRes1], r.ReadsOnly (fun a => a ∉ [rConst0, rRes1].map Reloc.slot)) ∧
      ([rConst0, rRes1].map Reloc.slot).Nodup ∧
      [rAddr0].Perm [rAddr0] ∧ [rRes1, rConst0].Perm [rConst0, rRes1] ∧
      applyAll sa0 ([rAddr0] ++ [rRes1, rConst0]) (fun _ => 0) ≠
        applyAll sa0 ([rAddr0] ++ [rConst0, rRes1]) (fun _ => 0) := by
  refine ⟨?_, by decide, fun h => ?_, by decide, List.Perm.refl _, List.Perm.swap _ _ _,
    fun h => ?_⟩
  · intro r hr sa m m'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; rfl
  · have := h rRes1 (by simp) sa0 (fun _ => 0) (fun a => if a = 0 then 1 else 0)
      (by intro a ha; simp [rConst0, rRes1] at ha; simp [ha.1])
    simp [rRes1] at this
  · have := congrFun h 1
    revert this
    decide

/-- `applyAll_append_perm_of_resolvers_read_no_resolver_slot`: the distinct-slot hypothesis on
`R` is tight (two resolvers of slot 0 with different values, `A = []`). -/
theorem resolvers_same_slot_order_dependent :
    (∀ r ∈ ([] : List Reloc), r.AddressOnly) ∧ (([] : List Reloc).map Reloc.slot).Nodup ∧
      (∀ r ∈ [symReloc 0 0, symReloc 0 1],
        r.ReadsOnly (fun a => a ∉ [symReloc 0 0, symReloc 0 1].map Reloc.slot)) ∧
      ¬ ([symReloc 0 0, symReloc 0 1].map Reloc.slot).Nodup ∧
      ([] : List Reloc).Perm [] ∧ [symReloc 0 1, symReloc 0 0].Perm [symReloc 0 0, symReloc 0 1] ∧
      applyAll sa0 ([] ++ [symReloc 0 1, symReloc 0 0]) (fun _ => 0) ≠
        applyAll sa0 ([] ++ [symReloc 0 0, symReloc 0 1]) (fun _ => 0) := by
  refine ⟨by simp, by decide, ?_, by decide, List.Perm.refl _, List.Perm.swap _ _ _, fun h => ?_⟩
  · intro r hr sa m m' _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  · have := congrFun h 0
    revert this
    decide

/-- `applyAll_append_perm_of_resolvers_read_no_resolver_slot`: the hypothesis `hA` (the
relocations applied first are address-only) is tight: with `A = [rAddr0, rRes1]` and `R = []`,
every other hypothesis holds and the two orders of `A` differ. -/
theorem nonAddressOnly_first_group_order_dependent :
    ¬ (∀ r ∈ [rAddr0, rRes1], r.AddressOnly) ∧ ([rAddr0, rRes1].map Reloc.slot).Nodup ∧
      (∀ r ∈ ([] : List Reloc), r.ReadsOnly (fun a => a ∉ ([] : List Reloc).map Reloc.slot)) ∧
      (([] : List Reloc).map Reloc.slot).Nodup ∧
      [rRes1, rAddr0].Perm [rAddr0, rRes1] ∧ ([] : List Reloc).Perm [] ∧
      applyAll sa0 ([rRes1, rAddr0] ++ []) (fun _ => 0) ≠
        applyAll sa0 ([rAddr0, rRes1] ++ []) (fun _ => 0) := by
  refine ⟨resolver_reads_unrelocated_slot_order_dependent.2.2.1, by decide, by simp, by decide,
    List.Perm.swap _ _ _, List.Perm.refl _, fun h => ?_⟩
  have := congrFun h 1
  revert this
  decide

/-- `applyAll_append_perm_of_resolvers_read_no_resolver_slot`: the distinct-slot hypothesis on
`A` is tight (`A = [symReloc 0 0, symReloc 0 1]`, `R = []`). -/
theorem addressOnly_first_group_same_slot_order_dependent :
    (∀ r ∈ [symReloc 0 0, symReloc 0 1], r.AddressOnly) ∧
      ¬ ([symReloc 0 0, symReloc 0 1].map Reloc.slot).Nodup ∧
      (∀ r ∈ ([] : List Reloc), r.ReadsOnly (fun a => a ∉ ([] : List Reloc).map Reloc.slot)) ∧
      (([] : List Reloc).map Reloc.slot).Nodup ∧
      [symReloc 0 1, symReloc 0 0].Perm [symReloc 0 0, symReloc 0 1] ∧ ([] : List Reloc).Perm [] ∧
      applyAll sa0 ([symReloc 0 1, symReloc 0 0] ++ []) (fun _ => 0) ≠
        applyAll sa0 ([symReloc 0 0, symReloc 0 1] ++ []) (fun _ => 0) := by
  refine ⟨addressOnly_same_slot_order_dependent.2.1, by decide, by simp, by decide,
    List.Perm.swap _ _ _, List.Perm.refl _, fun h => ?_⟩
  have := congrFun h 0
  revert this
  decide

/-- Resolver relocation: slot 3 gets the current contents of slot 2. -/
def rRes3of2 : Reloc := ⟨3, fun _ m => m 2⟩
/-- Resolver relocation reading an address no relocation writes: slot 4 gets the contents of
address 9. -/
def rRes4of9 : Reloc := ⟨4, fun _ m => m 9⟩

/-- Instance of `applyAll_perm_of_addressOnly_of_nodup_slots`: all its hypotheses hold for
`[rAddr0, symReloc 2 1]` and its reversal. -/
theorem addressOnlyOrder_nonvacuity :
    [rAddr0, symReloc 2 1].Perm [symReloc 2 1, rAddr0] ∧
      (∀ r ∈ [rAddr0, symReloc 2 1], r.AddressOnly) ∧
      ([rAddr0, symReloc 2 1].map Reloc.slot).Nodup := by
  refine ⟨List.Perm.swap _ _ _, ?_, by decide⟩
  intro r hr sa m m'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rfl

/-- Instance of `applyAll_append_perm_of_resolvers_read_no_resolver_slot`: `A = [rAddr0, symReloc 2
1]` (address-only) and `R = [rRes1, rRes3of2, rRes4of9]` (resolvers reading slots 0 and 2 of `A`
and the address 9 that no relocation writes), with `A'` and `R'` the reversals. -/
theorem relocationOrder_nonvacuity :
    (∀ r ∈ [rAddr0, symReloc 2 1], r.AddressOnly) ∧
      ([rAddr0, symReloc 2 1].map Reloc.slot).Nodup ∧
      (∀ r ∈ [rRes1, rRes3of2, rRes4of9],
        r.ReadsOnly (fun a => a ∉ [rRes1, rRes3of2, rRes4of9].map Reloc.slot)) ∧
      ([rRes1, rRes3of2, rRes4of9].map Reloc.slot).Nodup ∧
      [symReloc 2 1, rAddr0].Perm [rAddr0, symReloc 2 1] ∧
      [rRes4of9, rRes3of2, rRes1].Perm [rRes1, rRes3of2, rRes4of9] := by
  refine ⟨addressOnlyOrder_nonvacuity.2.1, by decide, ?_, by decide, List.Perm.swap _ _ _,
    List.reverse_perm [rRes1, rRes3of2, rRes4of9]⟩
  intro r hr sa m m' hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hm 0 (by simp [rRes1, rRes3of2, rRes4of9])
  · exact hm 2 (by simp [rRes1, rRes3of2, rRes4of9])
  · exact hm 9 (by simp [rRes1, rRes3of2, rRes4of9])


end Toy.RelroGc
