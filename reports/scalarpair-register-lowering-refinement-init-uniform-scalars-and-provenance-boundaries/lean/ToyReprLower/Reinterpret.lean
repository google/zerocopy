import ToyReprLower.Lemmas

/-!
# Register-level reinterpretation versus the byte-level transmute through memory

`regCast σ τ` reinterprets lowered registers of representation `σ` as registers of `τ` without
going through memory: a bitcast that keeps register contents and asserts nothing (no
initialization check, no range check). The byte-level transmute through memory raises the
`σ` registers to bytes and lowers them at `τ` (`lower τ ∘ raise n σ`).
-/

namespace Toy.ReprLower

/-- Register-level reinterpretation of one register value from scalar `s` to scalar `t`: a
bitcast that keeps the register contents and asserts nothing about them.
* Into a `union` scalar: the source register's contents as abstract bytes (`raw`).
* Into an `initialized` scalar: `poison` stays `poison`; an integer or pointer register keeps its
  data bytes; an integer target drops provenance and a pointer target from an integer has none.
* A `raw` union register cast into an `initialized` target keeps its bytes as they are,
  uninitialized bytes and provenance fragments included: no initialization, range or provenance
  check is made, so the result is a register value that lowering at `t` never produces. -/
def regCastScalar (s t : Scalar) (v : RVal) : RVal :=
  match t with
  | .union _ => .raw (raiseScalar s v)
  | .initialized q _ =>
    match v, q with
    | .poison, _ => .poison
    | .int ds, .int _ => .int ds
    | .int ds, .ptr _ => .ptr none ds
    | .ptr _ ds, .int _ => .int ds
    | .ptr pr ds, .ptr _ => .ptr pr ds
    | .raw bs, _ => .raw bs

/-- Register-level reinterpretation between representations.
* `Scalar` to `Scalar`, and `ScalarPair` to `ScalarPair`: componentwise (`a` to `a'`, `b` to
  `b'`), ignoring offsets.
* `ScalarPair` to a `union` `Scalar`: the two registers' contents concatenated, `a`'s then
  `b`'s, with no gap for padding, as one `raw` register.
* Every other combination (memory, a pair into an `initialized` scalar, a scalar into a pair) is
  not a register reinterpretation modelled here: the lowered value is passed on unchanged, and
  raising a lowered value of the wrong shape gives `n` uninitialized bytes. -/
def regCast : BRepr → BRepr → Lowered → Lowered
  | .scalar s, .scalar t, .one v => .one (regCastScalar s t v)
  | .pair a b _, .pair a' b' _, .two va vb => .two (regCastScalar a a' va) (regCastScalar b b' vb)
  | .pair a b _, .scalar (.union _), .two va vb => .one (.raw (raiseScalar a va ++ raiseScalar b vb))
  | _, _, l => l

/-- Exact agreement of the register-level reinterpretation from `σ` to `τ` with the byte-level
transmute through memory, on the `σ`-lowered form of every byte-level value `x` of length `n`:
both paths start from `lower σ x`; the register path applies `regCast σ τ`, the memory path raises
at `σ` and lowers at `τ`; the raised bytes at `τ` must be equal. -/
def CastAgrees (n : Nat) (σ τ : BRepr) : Prop :=
  ∀ x : List AByte, x.length = n →
    raise n τ (regCast σ τ (lower σ x)) = raise n τ (lower τ (raise n σ (lower σ x)))

/-- One-sided refinement of the byte-level transmute through memory by the register-level
reinterpretation: on the `σ`-lowered form of every byte-level value `x` of length `n`, the raised
bytes of the register path are at least as defined (`BytesLe`) as those of the memory path. -/
def CastRefines (n : Nat) (σ τ : BRepr) : Prop :=
  ∀ x : List AByte, x.length = n →
    BytesLe (raise n τ (lower τ (raise n σ (lower σ x)))) (raise n τ (regCast σ τ (lower σ x)))

/-- Initialization-discipline compatibility of a source scalar `s` with a target scalar `t`:
a `union` target accepts any source; an `initialized` target needs an `initialized` source
whose range, on data vectors of exactly the source width, is included in the target's range. -/
def DisciplineCompat (s t : Scalar) : Prop :=
  match s, t with
  | _, .union _ => True
  | .initialized p r1, .initialized _ r2 =>
      ∀ ds : List Nat, ds.length = p.size → r1 ds = true → r2 ds = true
  | .union _, .initialized _ _ => False

/-- `DisciplineCompat` with range inclusion required on data vectors of every length (for ranges
that do not depend on the length of the data, the two coincide). -/
def DisciplineCompatAnyLen (s t : Scalar) : Prop :=
  match s, t with
  | _, .union _ => True
  | .initialized _ r1, .initialized _ r2 => ∀ ds : List Nat, r1 ds = true → r2 ds = true
  | .union _, .initialized _ _ => False

/-! ## Auxiliary lemmas -/

theorem ext_getD {x y : List AByte} (hl : x.length = y.length)
    (h : ∀ i, x.getD i .uninit = y.getD i .uninit) : x = y := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := h i
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2] using this

theorem getD_eq_uninit_of_le {x : List AByte} {i : Nat} (h : x.length ≤ i) :
    x.getD i .uninit = .uninit := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem seg_place_one {n w : Nat} {rs : List AByte} (hl : rs.length = w) (hn : w ≤ n) :
    seg (place n [(0, rs)]) 0 w = rs := by
  apply ext_getD (by rw [length_seg, length_place]; omega)
  intro k
  rw [getD_seg]
  split
  · rw [getD_place, ite_eq_left (by omega), chunkAt_one, ite_eq_left (by omega)]; simp
  · rw [getD_eq_uninit_of_le (by omega)]

theorem seg_place_two_a {n wa wb o : Nat} {ra rb : List AByte} (hla : ra.length = wa)
    (hab : wa ≤ o) (hbn : o + wb ≤ n) :
    seg (place n [(0, ra), (o, rb)]) 0 wa = ra := by
  apply ext_getD (by rw [length_seg, length_place]; omega)
  intro k
  rw [getD_seg]
  split
  · rw [getD_place, ite_eq_left (by omega), chunkAt_two, ite_eq_left (by omega)]; simp
  · rw [getD_eq_uninit_of_le (by omega)]

theorem seg_place_two_b {n wa wb o : Nat} {ra rb : List AByte} (hla : ra.length = wa)
    (hlb : rb.length = wb) (hab : wa ≤ o) (hbn : o + wb ≤ n) :
    seg (place n [(0, ra), (o, rb)]) o wb = rb := by
  apply ext_getD (by rw [length_seg, length_place]; omega)
  intro k
  rw [getD_seg]
  split
  · rw [getD_place, ite_eq_left (by omega), chunkAt_two, ite_eq_right (by omega), ite_eq_left (by omega),
      Nat.add_sub_cancel_left]
  · rw [getD_eq_uninit_of_le (by omega)]

theorem place_one_inj {n : Nat} {A B : List AByte} (hA : A.length ≤ n) (hAB : A.length = B.length)
    (h : place n [(0, A)] = place n [(0, B)]) : A = B := by
  apply ext_getD hAB
  intro i
  by_cases hi : i < A.length
  · have := congrArg (fun l => l.getD i .uninit) h
    simp only [getD_place, ite_eq_left (show i < n by omega), chunkAt_one, Nat.zero_le, true_and,
      Nat.zero_add, Nat.sub_zero, ite_eq_left hi, ite_eq_left (show i < B.length by omega)] at this
    exact this
  · rw [getD_eq_uninit_of_le (by omega), getD_eq_uninit_of_le (by omega)]

theorem allInit_map_bits (ds : List Nat) : allInit (ds.map .bits) = true := by
  simp [allInit, AByte.isInit]

theorem allBits_map_bits (ds : List Nat) : allBits (ds.map .bits) = true := by
  simp [allBits, AByte.isBits]

theorem datas_map_bits (ds : List Nat) : datas (ds.map .bits) = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simpa [datas, AByte.data] using ih

theorem ptrProv_map_bits (ds : List Nat) : ptrProv (ds.map .bits) = none := by
  cases ds <;> simp [ptrProv, fragProv]

theorem ptrLower_map_bits (ds : List Nat) : ptrLower (ds.map .bits) = .ptr none ds := by
  simp [ptrLower, ptrProv_map_bits, datas_map_bits]

theorem allInit_replicate_uninit {w : Nat} (hw : 1 ≤ w) :
    allInit (List.replicate w .uninit) = false := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp [allInit, List.replicate_succ, AByte.isInit]

/-- Raising after lowering an all-`uninit` byte list of a scalar's width gives it back. -/
theorem raise_lower_replicate_uninit (t : Scalar) :
    raiseScalar t (lowerScalar t (List.replicate t.size .uninit)) =
      List.replicate t.size .uninit := by
  cases t with
  | union q => rfl
  | initialized q r =>
    by_cases h0 : (Scalar.initialized q r).size = 0
    · rw [h0]
      simp only [List.replicate_zero, lowerScalar]
      split
      · cases q <;> simp [raiseScalar, datas, ptrLower, ptrProv, fragProv]
      · simp [raiseScalar, h0]
    · simp [lowerScalar, allInit_replicate_uninit (show 1 ≤ (Scalar.initialized q r).size by omega),
        raiseScalar]

/-- Per-scalar agreement under discipline compatibility. -/
theorem raise_regCast_eq_raise_lower_raise (s t : Scalar) (bs : List AByte)
    (hbs : bs.length = s.size) (hw : s.size = t.size) (hc : DisciplineCompat s t) :
    raiseScalar t (regCastScalar s t (lowerScalar s bs)) =
      raiseScalar t (lowerScalar t (raiseScalar s (lowerScalar s bs))) := by
  cases t with
  | union q => simp [regCastScalar, lowerScalar, raiseScalar]
  | initialized q r2 =>
    cases s with
    | union p => exact absurd hc (by simp [DisciplineCompat])
    | initialized p r1 =>
      simp only [DisciplineCompat] at hc
      have hpois : raiseScalar (.initialized q r2)
          (lowerScalar (.initialized q r2) (raiseScalar (.initialized p r1) .poison)) =
          raiseScalar (.initialized q r2) .poison := by
        show raiseScalar (.initialized q r2) (lowerScalar (.initialized q r2)
          (List.replicate (Scalar.initialized p r1).size .uninit)) =
          List.replicate (Scalar.initialized q r2).size .uninit
        rw [hw]; exact raise_lower_replicate_uninit _
      have hdl : (datas bs).length = p.size := by
        simp only [datas, List.length_map]; exact hbs
      -- the data case, shared by integers and provenance-free pointers
      have hdata : ∀ v, (v = RVal.int (datas bs) ∨ v = RVal.ptr none (datas bs)) →
          r1 (datas bs) = true →
          raiseScalar (.initialized q r2) (regCastScalar (.initialized p r1) (.initialized q r2) v) =
          raiseScalar (.initialized q r2) (lowerScalar (.initialized q r2)
            (raiseScalar (.initialized p r1) v)) := by
        intro v hv hr1
        have hr2 := hc _ hdl hr1
        rcases hv with rfl | rfl <;> cases q <;>
          simp [regCastScalar, raiseScalar, lowerScalar, allInit_map_bits, datas_map_bits, hr2,
            ptrLower_map_bits]
      by_cases h : (allInit bs && r1 (datas bs)) = true
      · have h' := h
        simp only [Bool.and_eq_true] at h'
        cases p with
        | int w =>
          have hlow : lowerScalar (.initialized (.int w) r1) bs = .int (datas bs) := by
            simp only [lowerScalar, ite_eq_left h]
          rw [hlow]; exact hdata _ (Or.inl rfl) h'.2
        | ptr w =>
          have hlow : lowerScalar (.initialized (.ptr w) r1) bs = ptrLower bs := by
            simp only [lowerScalar, ite_eq_left h]
          rw [hlow]
          rcases ptrProv_cases bs with h1 | ⟨pr, hf, h1⟩
          · have hpl : ptrLower bs = .ptr none (datas bs) := by simp [ptrLower, h1]
            rw [hpl]; exact hdata _ (Or.inr rfl) h'.2
          · have hpl : ptrLower bs = .ptr (some pr) (datas bs) := by simp [ptrLower, h1]
            rw [hpl]
            have hr2 := hc _ hdl h'.2
            have hraise : raiseScalar (.initialized (.ptr w) r1) (.ptr (some pr) (datas bs)) = bs :=
              fragsList_datas hf
            rw [hraise]
            cases q <;>
              simp [regCastScalar, raiseScalar, lowerScalar, h'.1, hr2, ptrLower, h1,
                fragsList_datas hf]
      · have hlow : lowerScalar (.initialized p r1) bs = .poison := by
          simp only [lowerScalar, ite_eq_right h]
        rw [hlow, hpois]; rfl

theorem length_raiseScalar_regCastScalar (s t : Scalar) (bs : List AByte)
    (hbs : bs.length = s.size) (hw : s.size = t.size) :
    (raiseScalar t (regCastScalar s t (lowerScalar s bs))).length = s.size := by
  have hl := length_raiseScalar_lowerScalar s bs hbs
  cases t with
  | union q => simpa [regCastScalar, raiseScalar, hbs] using hl
  | initialized q r2 =>
    cases s with
    | union p => simpa [lowerScalar, regCastScalar, raiseScalar] using hbs
    | initialized p r1 =>
      simp only [lowerScalar] at hl ⊢
      split
      · rename_i h
        rw [ite_eq_left h] at hl
        cases p with
        | int w => cases q <;> simpa [regCastScalar, raiseScalar, hbs] using hl
        | ptr w =>
          rcases ptrProv_cases bs with h1 | ⟨pr, _, h1⟩ <;>
            cases q <;>
            simp_all [ptrLower, regCastScalar, raiseScalar, length_fragsList, Scalar.size,
              Scalar.prim, datas]
      · simp [regCastScalar, raiseScalar, hw]

/-- Agreement on a single scalar reduces to agreement of the raised register contents. -/
theorem castAgrees_scalar_iff (n : Nat) (s t : Scalar) (hw : s.size = t.size) (hn : s.size ≤ n) :
    CastAgrees n (.scalar s) (.scalar t) ↔ ∀ bs : List AByte, bs.length = s.size →
      raiseScalar t (regCastScalar s t (lowerScalar s bs)) =
        raiseScalar t (lowerScalar t (raiseScalar s (lowerScalar s bs))) := by
  unfold CastAgrees
  simp only [raise, lower, regCast]
  have key : ∀ bs : List AByte, bs.length = s.size →
      seg (place n [(0, raiseScalar s (lowerScalar s bs))]) 0 t.size =
        raiseScalar s (lowerScalar s bs) := fun bs hbs =>
    seg_place_one (by rw [length_raiseScalar_lowerScalar s bs hbs, hbs, hw]) (by omega)
  constructor
  · intro h bs hbs
    have hx : (bs ++ List.replicate (n - s.size) AByte.uninit).length = n := by simp [hbs]; omega
    have hseg : seg (bs ++ List.replicate (n - s.size) AByte.uninit) 0 s.size = bs := by
      simp [seg, ← hbs]
    have := h _ hx
    rw [hseg, key bs hbs] at this
    have hlB : (raiseScalar t (lowerScalar t (raiseScalar s (lowerScalar s bs)))).length =
        s.size := by
      rw [length_raiseScalar_lowerScalar t _ (by rw [length_raiseScalar_lowerScalar s bs hbs, hbs, hw]),
        length_raiseScalar_lowerScalar s bs hbs, hbs]
    exact place_one_inj (by rw [length_raiseScalar_regCastScalar s t bs hbs hw]; omega)
      (by rw [length_raiseScalar_regCastScalar s t bs hbs hw, hlB]) this
  · intro h x hx
    have hsl : (seg x 0 s.size).length = s.size := by rw [length_seg]; omega
    rw [key _ hsl, h _ hsl]

theorem getD_zero_raiseScalar_ne_frag1 (t : Scalar) (v : RVal) (hv : ∀ bs, v ≠ .raw bs)
    (b p : Nat) : (raiseScalar t v).getD 0 .uninit ≠ .ptrFrag b p 1 := by
  cases v with
  | poison =>
    simp only [raiseScalar]
    generalize t.size = m
    cases m <;> simp [List.replicate_succ]
  | int ds => cases ds <;> simp [raiseScalar]
  | ptr pr ds => cases pr <;> cases ds <;> simp [raiseScalar, fragsList]
  | raw bs => exact absurd rfl (hv bs)

theorem lowerScalar_initialized_ne_raw (q : Prim) (r : List Nat → Bool) (bs cs : List AByte) :
    lowerScalar (.initialized q r) bs ≠ .raw cs := by
  simp only [lowerScalar]
  split
  · cases q with
    | int w => simp
    | ptr w => simp [ptrLower]
  · simp

/-! ## Results -/

/-- **Scalar-to-scalar reinterpretation agrees exactly with the memory transmute iff the
disciplines are compatible.** For scalars `s`, `t` of equal width `w` with `1 ≤ w ≤ n`, the
register-level reinterpretation `regCast` from `Scalar s` to `Scalar t` and the byte-level
transmute through memory give equal raised bytes, on the `s`-lowered form of every byte-level
value of length `n` (`CastAgrees`), iff `t` is a `union` scalar, or both are `initialized` and
`s`'s range is included in `t`'s on data vectors of length exactly `w`. (The primitives may
differ: integer-to-pointer and pointer-to-integer reinterpretations are included.) -/
theorem regCast_scalar_agrees_iff_disciplineCompat (n : Nat) (s t : Scalar)
    (hw : s.size = t.size) (hpos : 1 ≤ s.size) (hn : s.size ≤ n) :
    CastAgrees n (.scalar s) (.scalar t) ↔ DisciplineCompat s t := by
  rw [castAgrees_scalar_iff n s t hw hn]
  refine ⟨fun h => ?_, fun hc bs hbs => raise_regCast_eq_raise_lower_raise s t bs hbs hw hc⟩
  cases t with
  | union q => trivial
  | initialized q r2 =>
    cases s with
    | union p =>
      exfalso
      obtain ⟨k, hk⟩ : ∃ k, (Scalar.union p).size = k + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      have := congrArg (fun l => l.getD 0 AByte.uninit)
        (h (.ptrFrag 0 0 1 :: List.replicate k .uninit) (by simp [hk]))
      simp only [lowerScalar, raiseScalar, regCastScalar, List.getD_cons_zero] at this
      exact getD_zero_raiseScalar_ne_frag1 _ _ (lowerScalar_initialized_ne_raw q r2 _) 0 0
        this.symm
    | initialized p r1 =>
      intro ds hl hr1
      cases hr2 : r2 ds
      · exfalso
        have hbs : (ds.map AByte.bits).length = (Scalar.initialized p r1).size := by
          simp only [List.length_map]; exact hl
        have := congrArg (fun l => l.getD 0 AByte.uninit) (h _ hbs)
        have hL : raiseScalar (.initialized q r2) (regCastScalar (.initialized p r1)
            (.initialized q r2) (lowerScalar (.initialized p r1) (ds.map .bits))) =
            ds.map .bits := by
          cases p <;> cases q <;>
            simp [lowerScalar, allInit_map_bits, datas_map_bits, hr1, ptrLower_map_bits,
              regCastScalar, raiseScalar]
        have hR : raiseScalar (.initialized q r2) (lowerScalar (.initialized q r2)
            (raiseScalar (.initialized p r1) (lowerScalar (.initialized p r1) (ds.map .bits)))) =
            List.replicate (Scalar.initialized q r2).size .uninit := by
          cases p <;> cases q <;>
            simp [lowerScalar, allInit_map_bits, datas_map_bits, hr1, hr2, ptrLower_map_bits,
              raiseScalar]
        simp only [hL, hR] at this
        have ht : 1 ≤ (Scalar.initialized q r2).size := hw ▸ hpos
        obtain ⟨k, hk⟩ : ∃ k, (Scalar.initialized q r2).size = k + 1 :=
          ⟨_, (Nat.succ_pred_eq_of_pos ht).symm⟩
        rw [hk] at this
        cases ds with
        | nil => simp [Scalar.size, Scalar.prim] at hl hpos; omega
        | cons d ds' => simp [List.replicate_succ] at this
      · rfl

/-- **Pair-to-pair reinterpretation agrees exactly with the memory transmute when offsets
coincide and disciplines are compatible.** For pairs `(a, b)` and `(a', b')` at the same `b`
offset `bOff`, with `a.size = a'.size`, `b.size = b'.size`, disjoint extents (`a.size ≤ bOff`)
inside the value (`bOff + b.size ≤ n`), and `DisciplineCompat a a'` and `DisciplineCompat b b'`,
the componentwise register-level reinterpretation and the byte-level transmute through memory
give equal raised bytes on the `(a, b)`-lowered form of every byte-level value of length `n`. -/
theorem regCast_pair_agrees_of_offsetEq_disciplineCompat (n : Nat) (a b a' b' : Scalar)
    (bOff : Nat) (hwa : a.size = a'.size) (hwb : b.size = b'.size) (hab : a.size ≤ bOff)
    (hbn : bOff + b.size ≤ n) (hca : DisciplineCompat a a') (hcb : DisciplineCompat b b') :
    CastAgrees n (.pair a b bOff) (.pair a' b' bOff) := by
  intro x hx
  simp only [raise, lower, regCast]
  have hal : (seg x 0 a.size).length = a.size := by rw [length_seg]; omega
  have hbl : (seg x bOff b.size).length = b.size := by rw [length_seg]; omega
  have hra := length_raiseScalar_lowerScalar a _ hal
  have hrb := length_raiseScalar_lowerScalar b _ hbl
  rw [hal] at hra
  rw [hbl] at hrb
  rw [← hwa, ← hwb, seg_place_two_a hra hab hbn, seg_place_two_b hra hrb hab hbn,
    raise_regCast_eq_raise_lower_raise a a' _ hal hwa hca,
    raise_regCast_eq_raise_lower_raise b b' _ hbl hwb hcb]

/-- The `←` direction of `regCast_scalar_agrees_iff_disciplineCompat` needs no positive width:
for scalars of equal width at most `n` with compatible disciplines, the reinterpretation agrees
with the memory transmute (width `0` included). -/
theorem regCast_scalar_agrees_of_disciplineCompat (n : Nat) (s t : Scalar)
    (hw : s.size = t.size) (hn : s.size ≤ n) (hc : DisciplineCompat s t) :
    CastAgrees n (.scalar s) (.scalar t) :=
  (castAgrees_scalar_iff n s t hw hn).2 (fun bs hbs => raise_regCast_eq_raise_lower_raise s t bs hbs hw hc)

/-! ## One-sided refinement -/

theorem bytesLeb_map_bits_datas_left {bs : List AByte} (h : allInit bs = true) :
    bytesLeb ((datas bs).map .bits) bs = true := by
  induction bs with
  | nil => rfl
  | cons a as ih =>
    simp only [allInit, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨ha, h2⟩ := h
    have := ih h2
    simp only [datas, List.map_cons, bytesLeb] at this ⊢
    rw [this]
    cases a <;> simp_all [AByte.leb, AByte.data, AByte.isInit]

theorem bytesLeb_replicate_uninit_left (bs : List AByte) :
    bytesLeb (List.replicate bs.length .uninit) bs = true := by
  induction bs with
  | nil => rfl
  | cons a as ih => simp [List.replicate_succ, bytesLeb, ih]

/-- Lowering a byte list of the scalar's width and raising it again never makes it more
defined. -/
theorem raise_lower_bytesLe_self (t : Scalar) (bs : List AByte) (h : bs.length = t.size) :
    BytesLe (raiseScalar t (lowerScalar t bs)) bs := by
  unfold BytesLe
  cases t with
  | union q => simp [lowerScalar, raiseScalar, bytesLeb_refl]
  | initialized q r =>
    simp only [lowerScalar]
    split
    · rename_i hc
      have hi : allInit bs = true := by
        simp only [Bool.and_eq_true] at hc; exact hc.1
      cases q with
      | int w => exact bytesLeb_map_bits_datas_left hi
      | ptr w =>
        rcases raiseScalar_ptrLower_cases (.initialized (.ptr w) r) bs with ⟨_, h1⟩ | ⟨_, _, _, h1⟩
        · rw [h1]; exact bytesLeb_map_bits_datas_left hi
        · rw [h1]; exact bytesLeb_refl bs
    · simp only [raiseScalar]
      rw [← h]
      exact bytesLeb_replicate_uninit_left bs

/-- Per-scalar one-sided refinement: for scalars of equal width, the raised register-level
reinterpretation is at least as defined as the raised memory transmute (any disciplines). -/
theorem raise_lower_raise_bytesLe_raise_regCast (s t : Scalar) (bs : List AByte)
    (hbs : bs.length = s.size) (hw : s.size = t.size) :
    BytesLe (raiseScalar t (lowerScalar t (raiseScalar s (lowerScalar s bs))))
      (raiseScalar t (regCastScalar s t (lowerScalar s bs))) := by
  cases t with
  | union q => simp [regCastScalar, lowerScalar, raiseScalar]; exact bytesLe_refl _
  | initialized q r2 =>
    cases s with
    | union p =>
      have h1 : lowerScalar (.union p) bs = .raw bs := rfl
      rw [h1]
      have h2 : raiseScalar (.initialized q r2) (regCastScalar (.union p) (.initialized q r2) (.raw bs))
          = bs := by cases q <;> rfl
      rw [h2]
      exact raise_lower_bytesLe_self _ bs (hbs.trans hw)
    | initialized p r1 =>
      have hdl : ((datas bs).map AByte.bits).length = (Scalar.initialized q r2).size := by
        simp [datas, hbs, ← hw]
      by_cases h : (allInit bs && r1 (datas bs)) = true
      · cases p with
        | int w =>
          have hlow : lowerScalar (.initialized (.int w) r1) bs = .int (datas bs) := by
            simp only [lowerScalar, ite_eq_left h]
          rw [hlow]
          have hR : raiseScalar (.initialized q r2)
              (regCastScalar (.initialized (.int w) r1) (.initialized q r2) (.int (datas bs))) =
              (datas bs).map .bits := by cases q <;> rfl
          rw [hR]
          exact raise_lower_bytesLe_self _ _ hdl
        | ptr w =>
          have hlow : lowerScalar (.initialized (.ptr w) r1) bs = ptrLower bs := by
            simp only [lowerScalar, ite_eq_left h]
          rw [hlow]
          rcases ptrProv_cases bs with h1 | ⟨pr, hf, h1⟩
          · have hpl : ptrLower bs = .ptr none (datas bs) := by simp [ptrLower, h1]
            rw [hpl]
            have hR : raiseScalar (.initialized q r2)
                (regCastScalar (.initialized (.ptr w) r1) (.initialized q r2)
                  (.ptr none (datas bs))) = (datas bs).map .bits := by cases q <;> rfl
            rw [hR]
            exact raise_lower_bytesLe_self _ _ hdl
          · have hpl : ptrLower bs = .ptr (some pr) (datas bs) := by simp [ptrLower, h1]
            rw [hpl]
            have hraise : raiseScalar (.initialized (.ptr w) r1) (.ptr (some pr) (datas bs)) = bs :=
              fragsList_datas hf
            rw [hraise]
            have hbt : bs.length = (Scalar.initialized q r2).size := by rw [hbs, hw]
            have hi : allInit bs = true := by
              simp only [Bool.and_eq_true] at h; exact h.1
            cases q with
            | ptr w' =>
              have hR : raiseScalar (.initialized (.ptr w') r2)
                  (regCastScalar (.initialized (.ptr w) r1) (.initialized (.ptr w') r2)
                    (.ptr (some pr) (datas bs))) = bs := fragsList_datas hf
              rw [hR]
              exact raise_lower_bytesLe_self _ _ hbt
            | int w' =>
              have hR : raiseScalar (.initialized (.int w') r2)
                  (regCastScalar (.initialized (.ptr w) r1) (.initialized (.int w') r2)
                    (.ptr (some pr) (datas bs))) = (datas bs).map .bits := rfl
              rw [hR]
              unfold BytesLe
              simp only [lowerScalar]
              split
              · exact bytesLeb_refl _
              · simp only [raiseScalar]
                have : (Scalar.initialized (.int w') r2).size = ((datas bs).map AByte.bits).length := by
                  rw [hdl]
                rw [this]
                exact bytesLeb_replicate_uninit_left _
      · have hlow : lowerScalar (.initialized p r1) bs = .poison := by
          simp only [lowerScalar, ite_eq_right h]
        rw [hlow]
        show BytesLe (raiseScalar (.initialized q r2) (lowerScalar (.initialized q r2)
          (List.replicate (Scalar.initialized p r1).size .uninit)))
          (List.replicate (Scalar.initialized q r2).size .uninit)
        rw [hw, raise_lower_replicate_uninit]
        exact bytesLe_refl _

theorem bytesLe_place_one {n : Nat} {A B : List AByte} (h : BytesLe A B) :
    BytesLe (place n [(0, A)]) (place n [(0, B)]) := by
  have ⟨hl, hp⟩ := (bytesLeb_iff_getD A B).1 h
  unfold BytesLe
  rw [bytesLeb_iff_getD]
  refine ⟨by simp [length_place], fun i hi => ?_⟩
  rw [length_place] at hi
  rw [getD_place, ite_eq_left hi, getD_place, ite_eq_left hi, chunkAt_one, chunkAt_one]
  by_cases hA : i < A.length
  · rw [ite_eq_left ⟨Nat.zero_le _, by omega⟩, ite_eq_left ⟨Nat.zero_le _, by omega⟩]
    simpa using hp i hA
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rfl

/-! ## One-sided refinement for every pair of scalars -/

theorem allInit_seg_place_one_le {n : Nat} {R : List AByte} {w : Nat}
    (h : allInit (seg (place n [(0, R)]) 0 w) = true) :
    (seg (place n [(0, R)]) 0 w).length ≤ R.length := by
  apply Classical.byContradiction
  intro hgt
  have hlt : R.length < (seg (place n [(0, R)]) 0 w).length := Nat.lt_of_not_le hgt
  have hseg_len : (seg (place n [(0, R)]) 0 w).length = min w n := by
    rw [length_seg, length_place]; omega
  have hi_w : R.length < w := by omega
  have hi_n : R.length < n := by omega
  have hget : (seg (place n [(0, R)]) 0 w).getD R.length .uninit = .uninit := by
    rw [getD_seg, ite_eq_left hi_w, getD_place, Nat.zero_add, ite_eq_left hi_n, chunkAt_one,
      ite_eq_right (by omega)]
  have hall : ∀ k, k < (seg (place n [(0, R)]) 0 w).length →
      ((seg (place n [(0, R)]) 0 w).getD k .uninit).isInit = true := by
    intro k hk
    have hmem : (seg (place n [(0, R)]) 0 w)[k]'hk ∈ seg (place n [(0, R)]) 0 w :=
      List.getElem_mem hk
    have his := List.all_eq_true.1 h _ hmem
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using his
  have := hall R.length hlt
  rw [hget] at this
  contradiction

theorem seg_place_one_eq_take_of_le {n : Nat} {R : List AByte} {w : Nat}
    (hle : min w n ≤ R.length) :
    seg (place n [(0, R)]) 0 w = R.take (min w n) := by
  apply ext_getD
  · rw [length_seg, length_place, List.length_take]; omega
  · intro k
    by_cases hk : k < min w n
    · rw [getD_seg, ite_eq_left (by omega), getD_place, Nat.zero_add, ite_eq_left (by omega),
        chunkAt_one, ite_eq_left (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk,
        List.getElem?_eq_getElem (show k < R.length by omega)]
    · have h1 : (seg (place n [(0, R)]) 0 w).length ≤ k := by
        rw [length_seg, length_place]; omega
      have h2 : (R.take (min w n)).length ≤ k := by simp [List.length_take]; omega
      rw [getD_eq_uninit_of_le h1, getD_eq_uninit_of_le h2]

theorem getD_map_bits (ds : List Nat) (i : Nat) (hi : i < ds.length) :
    (ds.map AByte.bits).getD i .uninit = .bits (ds[i]'hi) := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_fragsList_data (pr k : Nat) (ds : List Nat) (i : Nat) (hi : i < ds.length) :
    ((fragsList pr k ds).getD i .uninit).data = ds[i]'hi := by
  induction ds generalizing k i with
  | nil => cases hi
  | cons d ds ih =>
    cases i with
    | zero => simp [fragsList, AByte.data]
    | succ j =>
      have hj : j < ds.length := by simpa using hi
      simpa [fragsList] using ih (k + 1) j hj

theorem getD_raise_regCast_nonpoison (s : Scalar) (q : Prim) (r2 : List Nat → Bool) (v : RVal)
    (hv : v ≠ .poison) (i : Nat) (hi : i < (raiseScalar s v).length) :
    i < (raiseScalar (.initialized q r2) (regCastScalar s (.initialized q r2) v)).length ∧
    (((raiseScalar (.initialized q r2) (regCastScalar s (.initialized q r2) v)).getD i .uninit =
        (raiseScalar s v).getD i .uninit) ∨
     (∃ w', q = .int w' ∧
        (raiseScalar (.initialized q r2) (regCastScalar s (.initialized q r2) v)).getD i .uninit =
          .bits ((raiseScalar s v).getD i .uninit).data)) := by
  cases v with
  | poison => exact absurd rfl hv
  | raw bs =>
    refine ⟨?_, Or.inl ?_⟩
    · cases q <;> exact hi
    · cases q <;> rfl
  | int ds =>
    refine ⟨?_, Or.inl ?_⟩
    · cases q <;> simpa [regCastScalar, raiseScalar] using hi
    · cases q <;> rfl
  | ptr pr ds =>
    cases pr with
    | none =>
      refine ⟨?_, Or.inl ?_⟩
      · cases q <;> simpa [regCastScalar, raiseScalar] using hi
      · cases q <;> rfl
    | some pr0 =>
      have hids : i < ds.length := by simpa [raiseScalar, length_fragsList] using hi
      cases q with
      | ptr w' =>
        exact ⟨by simp [regCastScalar, raiseScalar, length_fragsList, hids], Or.inl rfl⟩
      | int w' =>
        refine ⟨by simp [regCastScalar, raiseScalar, hids], Or.inr ⟨w', rfl, ?_⟩⟩
        simp only [regCastScalar, raiseScalar]
        rw [getD_map_bits ds i hids, getD_fragsList_data pr0 0 ds i hids]

theorem bits_data_leb_of_isInit {b : AByte} (h : b.isInit = true) :
    (AByte.bits b.data).leb b = true := by
  cases b <;> simp_all [AByte.isInit, AByte.data, AByte.leb]

/-- **Scalar-to-scalar reinterpretation refines the memory transmute (one-sided), for every pair
of scalars.** For every `n` and all scalars `s`, `t`, of any widths, initialization disciplines
and ranges, the register-level reinterpretation `regCast` is at least as defined (`BytesLe`) as
the byte-level transmute through memory, on the `s`-lowered form of every byte-level value of
length `n`. Unequal widths are included: `regCastScalar` keeps the register payload without
truncating or padding it to `t.size`. -/
theorem regCast_scalar_refines_transmute (n : Nat) (s t : Scalar) :
    CastRefines n (.scalar s) (.scalar t) := by
  intro x _
  simp only [raise, lower, regCast]
  let bs := seg x 0 s.size
  let v := lowerScalar s bs
  let R := raiseScalar s v
  let M := place n [(0, R)]
  let bst := seg M 0 t.size
  change BytesLe (place n [(0, raiseScalar t (lowerScalar t bst))])
    (place n [(0, raiseScalar t (regCastScalar s t v))])
  unfold BytesLe
  rw [bytesLeb_iff_getD]
  refine ⟨by simp [length_place], fun i hi => ?_⟩
  rw [length_place] at hi
  rw [getD_place, ite_eq_left hi, getD_place, ite_eq_left hi, chunkAt_one, chunkAt_one]
  simp only [Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero]
  cases t with
  | union q =>
    change (if i < bst.length then bst.getD i .uninit else .uninit).leb
      (if i < R.length then R.getD i .uninit else .uninit) = true
    have hbst_len : bst.length = min q.size n := by
      simp [bst, M, length_seg, length_place, Scalar.size, Scalar.prim]
    by_cases hib : i < bst.length
    · rw [ite_eq_left hib]
      have hiq : i < (Scalar.union q).size := by simp [Scalar.size, Scalar.prim]; omega
      have hbst_i : bst.getD i .uninit = if i < R.length then R.getD i .uninit else .uninit := by
        simp only [bst, M]
        rw [getD_seg, ite_eq_left hiq, getD_place, Nat.zero_add, ite_eq_left hi, chunkAt_one]
        simp
      rw [hbst_i]
      exact AByte.leb_refl _
    · rw [ite_eq_right hib]; exact AByte.uninit_leb _
  | initialized q r2 =>
    by_cases hcond : (allInit bst && r2 (datas bst)) = true
    · have hcond' := hcond
      simp only [Bool.and_eq_true] at hcond'
      have hbst_le_R : bst.length ≤ R.length := allInit_seg_place_one_le hcond'.1
      have hbst_len : bst.length = min (Scalar.initialized q r2).size n := by
        simp [bst, M, length_seg, length_place]
      have hbst_eq : bst = R.take bst.length := by
        rw [hbst_len]; exact seg_place_one_eq_take_of_le (hbst_len ▸ hbst_le_R)
      by_cases hib : i < bst.length
      · have hiR : i < R.length := Nat.lt_of_lt_of_le hib hbst_le_R
        have hbst_i : bst.getD i .uninit = R.getD i .uninit := by
          rw [hbst_eq]
          simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hib]
        have hRi_init : (R.getD i .uninit).isInit = true := by
          rw [← hbst_i]
          have hmem : bst[i]'hib ∈ bst := List.getElem_mem hib
          have his := List.all_eq_true.1 hcond'.1 _ hmem
          simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hib] using his
        have hv_not_poison : v ≠ .poison := by
          intro hp
          have hRpois : R = List.replicate s.size .uninit := by simp [R, hp, raiseScalar]
          have hget : R.getD i .uninit = .uninit := by
            rw [hRpois]
            have hisz : i < s.size := by rw [hRpois, List.length_replicate] at hiR; exact hiR
            simp [List.getD_eq_getElem?_getD, hisz]
          rw [hget] at hRi_init
          contradiction
        obtain ⟨hiCreg, hCreg⟩ := getD_raise_regCast_nonpoison s q r2 v hv_not_poison i hiR
        rw [ite_eq_left hiCreg]
        have hl_eq : (raiseScalar (.initialized q r2)
            (lowerScalar (.initialized q r2) bst)).length = bst.length := by
          simp only [lowerScalar, ite_eq_left hcond]
          cases q with
          | int w' => simp [raiseScalar, datas]
          | ptr w' => exact length_raiseScalar_ptrLower _ bst
        rw [ite_eq_left (hl_eq ▸ hib)]
        have hdatas_i : ((datas bst).map AByte.bits).getD i .uninit =
            .bits (R.getD i .uninit).data := by
          have hid : i < (datas bst).length := by simp [datas, hib]
          rw [getD_map_bits (datas bst) i hid]
          have hgetd : (datas bst)[i]'hid = (bst[i]'hib).data := by simp [datas]
          rw [hgetd]
          have hbe : bst[i]'hib = bst.getD i .uninit := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hib]
          rw [hbe, hbst_i]
        rcases hCreg with heq | ⟨w', rfl, heq⟩
        · rw [heq]
          simp only [lowerScalar, ite_eq_left hcond]
          cases q with
          | int w' =>
            simp only [raiseScalar, hdatas_i]
            exact bits_data_leb_of_isInit hRi_init
          | ptr w' =>
            rcases raiseScalar_ptrLower_cases (.initialized (.ptr w') r2) bst with
              ⟨_, hr⟩ | ⟨_, _, _, hr⟩
            · rw [hr, hdatas_i]; exact bits_data_leb_of_isInit hRi_init
            · rw [hr, hbst_i]; exact AByte.leb_refl _
        · rw [heq]
          simp only [lowerScalar, ite_eq_left hcond, raiseScalar, hdatas_i]
          exact AByte.leb_refl _
      · have hl_eq : (raiseScalar (.initialized q r2)
            (lowerScalar (.initialized q r2) bst)).length = bst.length := by
          simp only [lowerScalar, ite_eq_left hcond]
          cases q with
          | int w' => simp [raiseScalar, datas]
          | ptr w' => exact length_raiseScalar_ptrLower _ bst
        rw [hl_eq, ite_eq_right hib]
        exact AByte.uninit_leb _
    · have hlow : lowerScalar (.initialized q r2) bst = .poison := by
        simp only [lowerScalar, ite_eq_right hcond]
      rw [hlow]
      simp only [raiseScalar, List.length_replicate]
      split
      · rename_i hisz
        have : (List.replicate (Scalar.initialized q r2).size AByte.uninit).getD i .uninit =
            .uninit := by
          simp [List.getD_eq_getElem?_getD, hisz]
        rw [this]; exact AByte.uninit_leb _
      · exact AByte.uninit_leb _

/-! ## Pair reinterpretation without the in-bounds hypothesis, for length-independent ranges -/

theorem take_raise_regCast_eq_of_anyLen (s t : Scalar) (bs : List AByte) (m : Nat)
    (hbs : bs.length = m) (hm : m ≤ s.size) (hc : DisciplineCompatAnyLen s t) :
    (raiseScalar t (regCastScalar s t (lowerScalar s bs))).take m =
      (raiseScalar t (lowerScalar t ((raiseScalar s (lowerScalar s bs)).take m))).take m := by
  cases t with
  | union q =>
    simp [regCastScalar, lowerScalar, raiseScalar, List.take_take]
  | initialized q r2 =>
    cases s with
    | union p => exact absurd hc (by simp [DisciplineCompatAnyLen])
    | initialized p r1 =>
      simp only [DisciplineCompatAnyLen] at hc
      have hpois : (raiseScalar (.initialized q r2)
          (lowerScalar (.initialized q r2) ((raiseScalar (.initialized p r1) .poison).take m))).take m =
          (raiseScalar (.initialized q r2) .poison).take m := by
        have htr : (raiseScalar (.initialized p r1) .poison).take m = List.replicate m .uninit := by
          simp [raiseScalar, List.take_replicate, Nat.min_eq_left hm]
        rw [htr]
        cases m with
        | zero => simp
        | succ k =>
          have hall : allInit (List.replicate (k + 1) .uninit) = false :=
            allInit_replicate_uninit (by omega)
          simp [lowerScalar, hall]
      have hdata : ∀ v, (v = RVal.int (datas bs) ∨ v = RVal.ptr none (datas bs)) →
          r1 (datas bs) = true →
          (raiseScalar (.initialized q r2) (regCastScalar (.initialized p r1) (.initialized q r2) v)).take m =
          (raiseScalar (.initialized q r2) (lowerScalar (.initialized q r2)
            ((raiseScalar (.initialized p r1) v).take m))).take m := by
        intro v hv hr1
        have hr2 := hc _ hr1
        have hlen : ((datas bs).map AByte.bits).length = m := by simp [datas, hbs]
        have htake : ((datas bs).map AByte.bits).take m = (datas bs).map AByte.bits :=
          List.take_of_length_le (Nat.le_of_eq hlen)
        rcases hv with rfl | rfl <;> cases q <;>
          simp [regCastScalar, raiseScalar, lowerScalar, htake, allInit_map_bits, datas_map_bits,
            hr2, ptrLower_map_bits]
      by_cases h : (allInit bs && r1 (datas bs)) = true
      · have h' := h
        simp only [Bool.and_eq_true] at h'
        cases p with
        | int w =>
          have hlow : lowerScalar (.initialized (.int w) r1) bs = .int (datas bs) := by
            simp only [lowerScalar, ite_eq_left h]
          rw [hlow]; exact hdata _ (Or.inl rfl) h'.2
        | ptr w =>
          have hlow : lowerScalar (.initialized (.ptr w) r1) bs = ptrLower bs := by
            simp only [lowerScalar, ite_eq_left h]
          rw [hlow]
          rcases ptrProv_cases bs with h1 | ⟨pr, hf, h1⟩
          · have hpl : ptrLower bs = .ptr none (datas bs) := by simp [ptrLower, h1]
            rw [hpl]; exact hdata _ (Or.inr rfl) h'.2
          · have hpl : ptrLower bs = .ptr (some pr) (datas bs) := by simp [ptrLower, h1]
            rw [hpl]
            have hr2 := hc _ h'.2
            have hraise : raiseScalar (.initialized (.ptr w) r1) (.ptr (some pr) (datas bs)) = bs :=
              fragsList_datas hf
            have htake : bs.take m = bs := List.take_of_length_le (Nat.le_of_eq hbs)
            rw [hraise, htake]
            cases q <;>
              simp [regCastScalar, raiseScalar, lowerScalar, h'.1, hr2, ptrLower, h1,
                fragsList_datas hf]
      · have hlow : lowerScalar (.initialized p r1) bs = .poison := by
          simp only [lowerScalar, ite_eq_right h]
        rw [hlow]
        exact hpois.symm

theorem length_ge_regCastScalar (s t : Scalar) (bs : List AByte)
    (hbs : bs.length ≤ s.size) (hw : s.size = t.size) :
    bs.length ≤ (raiseScalar t (regCastScalar s t (lowerScalar s bs))).length := by
  have hl := length_le_raiseScalar_lowerScalar s bs hbs
  cases t with
  | union q => simpa [regCastScalar, raiseScalar] using hl
  | initialized q r2 =>
    cases s with
    | union p => simp [lowerScalar, regCastScalar, raiseScalar]
    | initialized p r1 =>
      simp only [lowerScalar] at hl ⊢
      split
      · rename_i h
        rw [ite_eq_left h] at hl
        cases p with
        | int w => cases q <;> simpa [regCastScalar, raiseScalar] using hl
        | ptr w =>
          rcases ptrProv_cases bs with h1 | ⟨pr, _, h1⟩ <;>
            cases q <;>
            simp_all [ptrLower, regCastScalar, raiseScalar, length_fragsList, datas]
      · simp [regCastScalar, raiseScalar]; omega

theorem length_le_regCastScalar (s t : Scalar) (bs : List AByte)
    (hbs : bs.length ≤ s.size) (hw : s.size = t.size) :
    (raiseScalar t (regCastScalar s t (lowerScalar s bs))).length ≤ s.size := by
  have hl := length_raiseScalar_lowerScalar_le s bs hbs
  cases t with
  | union q => simpa [regCastScalar, raiseScalar] using hl
  | initialized q r2 =>
    cases s with
    | union p => simpa [lowerScalar, regCastScalar, raiseScalar] using hbs
    | initialized p r1 =>
      simp only [lowerScalar] at hl ⊢
      split
      · rename_i h
        rw [ite_eq_left h] at hl
        cases p with
        | int w => cases q <;> simpa [regCastScalar, raiseScalar] using hl
        | ptr w =>
          rcases ptrProv_cases bs with h1 | ⟨pr, _, h1⟩ <;>
            cases q <;>
            simp_all [ptrLower, regCastScalar, raiseScalar, length_fragsList, datas]
      · simp [regCastScalar, raiseScalar]; omega

/-- **For length-independent range inclusion, pair reinterpretation needs no in-bounds
hypothesis.** For pairs `(a, b)` and `(a', b')` at the same `b` offset `bOff`, with equal
component widths, disjoint extents (`a.size ≤ bOff`), and `DisciplineCompatAnyLen` for both
components (range inclusion on data vectors of every length), the componentwise reinterpretation
agrees with the memory transmute on every byte-level value of length `n`, whether or not `b`'s
extent lies inside the value. -/
theorem regCast_pair_agrees_of_offsetEq_disciplineCompatAnyLen (n : Nat) (a b a' b' : Scalar)
    (bOff : Nat) (hwa : a.size = a'.size) (hwb : b.size = b'.size) (hab : a.size ≤ bOff)
    (hca : DisciplineCompatAnyLen a a') (hcb : DisciplineCompatAnyLen b b') :
    CastAgrees n (.pair a b bOff) (.pair a' b' bOff) := by
  intro x hx
  simp only [raise, lower, regCast]
  let bsa := seg x 0 a.size
  let bsb := seg x bOff b.size
  have hal_eq : bsa.length = min a.size n := by simp [bsa, length_seg, hx]
  have hbl_eq : bsb.length = min b.size (n - bOff) := by simp [bsb, length_seg, hx]
  have hal_le : bsa.length ≤ a.size := by omega
  have hbl_le : bsb.length ≤ b.size := by omega
  let ra := raiseScalar a (lowerScalar a bsa)
  let rb := raiseScalar b (lowerScalar b bsb)
  have hra_ge : bsa.length ≤ ra.length := length_le_raiseScalar_lowerScalar a bsa hal_le
  have hra_le : ra.length ≤ a.size := length_raiseScalar_lowerScalar_le a bsa hal_le
  have hrb_ge : bsb.length ≤ rb.length := length_le_raiseScalar_lowerScalar b bsb hbl_le
  have hrb_le : rb.length ≤ b.size := length_raiseScalar_lowerScalar_le b bsb hbl_le
  have hsegA : seg (place n [(0, ra), (bOff, rb)]) 0 a'.size = ra.take bsa.length := by
    apply ext_getD
    · rw [length_seg, length_place, List.length_take, Nat.min_eq_left hra_ge]; omega
    · intro k
      rw [getD_seg]
      by_cases hk : k < bsa.length
      · rw [ite_eq_left (by omega), getD_place, ite_eq_left (by omega), chunkAt_two,
          ite_eq_left (by omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
      · by_cases hk2 : k < a'.size
        · rw [ite_eq_left hk2, getD_place, ite_eq_right (by omega),
            getD_eq_uninit_of_le (by simp [List.length_take]; omega)]
        · rw [ite_eq_right hk2, getD_eq_uninit_of_le (by simp [List.length_take]; omega)]
  have hsegB : seg (place n [(0, ra), (bOff, rb)]) bOff b'.size = rb.take bsb.length := by
    apply ext_getD
    · rw [length_seg, length_place, List.length_take, Nat.min_eq_left hrb_ge]; omega
    · intro k
      rw [getD_seg]
      by_cases hk : k < bsb.length
      · rw [ite_eq_left (by omega), getD_place, ite_eq_left (by omega), chunkAt_two,
          ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]
        simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
      · by_cases hk2 : k < b'.size
        · rw [ite_eq_left hk2, getD_place, ite_eq_right (by omega),
            getD_eq_uninit_of_le (by simp [List.length_take]; omega)]
        · rw [ite_eq_right hk2, getD_eq_uninit_of_le (by simp [List.length_take]; omega)]
  change place n [(0, raiseScalar a' (regCastScalar a a' (lowerScalar a bsa))),
      (bOff, raiseScalar b' (regCastScalar b b' (lowerScalar b bsb)))] =
    place n [(0, raiseScalar a' (lowerScalar a' (seg (place n [(0, ra), (bOff, rb)]) 0 a'.size))),
      (bOff, raiseScalar b' (lowerScalar b' (seg (place n [(0, ra), (bOff, rb)]) bOff b'.size)))]
  rw [hsegA, hsegB]
  have heqA := take_raise_regCast_eq_of_anyLen a a' bsa bsa.length rfl hal_le hca
  have heqB := take_raise_regCast_eq_of_anyLen b b' bsb bsb.length rfl hbl_le hcb
  have hlAL := length_ge_regCastScalar a a' bsa hal_le hwa
  have hlAL_le := length_le_regCastScalar a a' bsa hal_le hwa
  have hlBL := length_ge_regCastScalar b b' bsb hbl_le hwb
  have hlBL_le := length_le_regCastScalar b b' bsb hbl_le hwb
  have htakeA_len : (ra.take bsa.length).length ≤ a'.size := by
    rw [List.length_take, Nat.min_eq_left hra_ge]; omega
  have htakeB_len : (rb.take bsb.length).length ≤ b'.size := by
    rw [List.length_take, Nat.min_eq_left hrb_ge]; omega
  have hlAR := length_le_raiseScalar_lowerScalar a' (ra.take bsa.length) htakeA_len
  have hlAR_le := length_raiseScalar_lowerScalar_le a' (ra.take bsa.length) htakeA_len
  have hlBR := length_le_raiseScalar_lowerScalar b' (rb.take bsb.length) htakeB_len
  have hlBR_le := length_raiseScalar_lowerScalar_le b' (rb.take bsb.length) htakeB_len
  rw [List.length_take, Nat.min_eq_left hra_ge] at hlAR
  rw [List.length_take, Nat.min_eq_left hrb_ge] at hlBR
  apply ext_getD (by simp [length_place])
  intro i
  by_cases hi : i < n
  · rw [getD_place, ite_eq_left hi, getD_place, ite_eq_left hi, chunkAt_two, chunkAt_two]
    simp only [Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero]
    by_cases h1 : i < a.size
    · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      have hi_bsa : i < bsa.length := by omega
      have hcon := congrArg (fun l => l.getD i AByte.uninit) heqA
      simpa [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi_bsa] using hcon
    · have hnotL : ¬ i < (raiseScalar a' (regCastScalar a a' (lowerScalar a bsa))).length := by omega
      have hnotR : ¬ i < (raiseScalar a' (lowerScalar a' (ra.take bsa.length))).length := by omega
      rw [ite_eq_right hnotL, ite_eq_right hnotR]
      by_cases h2 : bOff ≤ i ∧ i < bOff + b.size
      · have hL2 : bOff ≤ i ∧ i < bOff + (raiseScalar b' (regCastScalar b b' (lowerScalar b bsb))).length := by omega
        have hR2 : bOff ≤ i ∧ i < bOff + (raiseScalar b' (lowerScalar b' (rb.take bsb.length))).length := by omega
        rw [ite_eq_left hL2, ite_eq_left hR2]
        have hi_bsb : i - bOff < bsb.length := by omega
        have hcon := congrArg (fun l => l.getD (i - bOff) AByte.uninit) heqB
        simpa [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi_bsb] using hcon
      · have hnotL2 : ¬ (bOff ≤ i ∧ i < bOff + (raiseScalar b' (regCastScalar b b' (lowerScalar b bsb))).length) := by omega
        have hnotR2 : ¬ (bOff ≤ i ∧ i < bOff + (raiseScalar b' (lowerScalar b' (rb.take bsb.length))).length) := by omega
        rw [ite_eq_right hnotL2, ite_eq_right hnotR2]
  · rw [getD_place, ite_eq_right hi, getD_place, ite_eq_right hi]

/-! ## Pair to `union` scalar without padding -/

theorem seg_place_two_concat {n wa wb : Nat} {ra rb : List AByte} (hla : ra.length = wa)
    (hlb : rb.length = wb) (hn : wa + wb ≤ n) :
    seg (place n [(0, ra), (wa, rb)]) 0 (wa + wb) = ra ++ rb := by
  apply ext_getD (by rw [length_seg, length_place]; simp [hla, hlb]; omega)
  intro k
  rw [getD_seg]
  by_cases hk : k < wa + wb
  · rw [ite_eq_left hk, getD_place, ite_eq_left (by omega), chunkAt_two]
    simp only [Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero]
    by_cases ha : k < ra.length
    · rw [ite_eq_left ha]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left ha]
    · rw [ite_eq_right ha, ite_eq_left ⟨by omega, by omega⟩]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : ra.length ≤ k), hla]
  · rw [ite_eq_right hk, getD_eq_uninit_of_le (by simp [hla, hlb]; omega)]

/-- **Without padding, concatenating a pair into a `union` scalar agrees with the memory
transmute.** For a pair `(a, b)` with `b` at offset exactly `a.size` (no padding between the
scalars) and a `union` scalar of width exactly `a.size + b.size` that fits in the value
(`a.size + b.size ≤ n`), the concatenating register-level reinterpretation and the byte-level
transmute through memory give equal raised bytes, both starting from the `(a, b)`-lowered form
of every byte-level value of length `n`. -/
theorem regCast_pair_to_union_scalar_agrees_of_no_padding (n : Nat) (a b : Scalar) (q : Prim)
    (hq : q.size = a.size + b.size) (hn : a.size + b.size ≤ n) :
    CastAgrees n (.pair a b a.size) (.scalar (.union q)) := by
  intro x hx
  simp only [raise, lower, regCast]
  have hal : (seg x 0 a.size).length = a.size := by rw [length_seg]; omega
  have hbl : (seg x a.size b.size).length = b.size := by rw [length_seg]; omega
  have hra := length_raiseScalar_lowerScalar a _ hal
  have hrb := length_raiseScalar_lowerScalar b _ hbl
  rw [hal] at hra
  rw [hbl] at hrb
  have hqs : (Scalar.union q).size = a.size + b.size := hq
  rw [hqs, seg_place_two_concat hra hrb hn]
  rfl

end Toy.ReprLower
