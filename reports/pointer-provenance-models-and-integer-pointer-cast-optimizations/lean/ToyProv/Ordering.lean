import ToyProv.OnePast
import ToyProv.RoundTrip
import ToyProv.Forwarding
import ToyProv.FlatInv
import ToyProv.DeadCast
import ToyProv.Erasure
import ToyProv.MonoSim

/-!
# R6 — Model ordering and which optimizations transfer

Semantically the models are ordered by definedness: `flat` is the most defined, `strict` the
least, `exposed` in between (R6a, R6b; both orderings are strict, R6d). The ordering R6a rests on
provenance monotonicity (more provenance never introduces UB; `ToyProv.Monotone`), which fails for
a decoder that makes mixed-provenance pointer bytes UB (`ToyProv.EqProvDecode`).

Soundness of an optimization does **not** transfer along this ordering in either direction in
general (R6g): `DropUnusedPtr2int` is sound in `strict` and unsound in `exposed`, and
`CopyToInt2ptrIfCand` is sound in `exposed` and unsound in `strict`. R6e gives transfer
principles for individual rewrites: a refinement moves from `strict` to `exposed` when the
source's `strict` behaviour is also an `exposed` behaviour, and from `exposed` to `strict` when the
target's is.

Optimization table (`✓` = a theorem `Sound m T`; `✗` = a concrete counterexample):

| transformation `T`              | flat | strict | exposed |
|---------------------------------|------|--------|---------|
| `SubstAddrEq`                   | ✓    | ✗      | ✗       |
| `SubstAddrEqInBounds`           | ✓    | ✓      | ✓       |
| `SubstIntEq`                    | ✓    | ✗      | ✗       |
| `SubstSameVal`                  | ✓    | ✓      | ✓       |
| `Int2ptrToCopy` (fold)          | ✓    | ✓      | ✗       |
| `CopyToInt2ptr` (introduce)     | ✓    | ✗      | ✗       |
| `CopyToInt2ptrIfCand`           | ✓ (every matching source is UB) | ✗ | ✓ |
| `DropUnusedPtr2int`             | ✓    | ✓      | ✗       |
| `ForwardAcrossCast`             | ✗    | ✓ (every matching source is UB) | ✗ |
| `DSEAcrossCast`                 | ✗    | ✓ (every matching source is UB) | ✗ |

Three `✓` cells are vacuous: every program pair in the relation has a source that is UB in that
model (`copyToInt2ptrIfCand_flat_src_ub`, `forwardAcrossCast_strict_src_ub`,
`dseAcrossCast_strict_src_ub`), so those soundness theorems say nothing about defined programs.
Every other `✓` cell is inhabited by a pair whose source is defined
(`soundness_table_nonvacuous`).
-/

namespace Toy.Prov

/-! ### R6a–R6d — the semantic ordering -/

/-- **R6a.** For every program, the exposed model's behaviour refines the strict model's:
either the program has UB in `strict`, or every `exposed` behaviour is a `strict` behaviour.
("`strict` has more UB.") -/
theorem exposed_semRefines_strict (P : Prog) : SemRefines .exposed .strict P := by
  rw [SemRefines, beh_eq_of_after, beh_eq_of_after]
  cases ha : after .strict P with
  | nil => left; simp
  | cons s rest =>
    right
    have hs : s ∈ execOk .strict P init := by rw [← after_eq_execOk, ha]; simp
    obtain ⟨t, ht, hle⟩ := execOk_mono (m₁ := .strict) (m₂ := .exposed)
      (by decide) (by decide) (by decide) (stLE_refl init) hs
    have hsl : after .strict P = [s] := by
      have hlen := execOk_det_length (Or.inr rfl) P init
      rw [← after_eq_execOk, ha] at hlen
      simp only [List.length_cons] at hlen
      have : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; exact ha
    have hcongr := exposed_beh_elements_equal P
    rw [beh_eq_of_after] at hcongr
    have ht_mem : Outcome.done s.out ∈
        (if (after .exposed P).isEmpty then [.ub]
         else (after .exposed P).map (fun st => .done st.out)) := by
      cases hta : after .exposed P with
      | nil => rw [← after_eq_execOk, hta] at ht; simp at ht
      | cons t₀ trest =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.mem_map]
        exact ⟨t, by rwa [← hta, after_eq_execOk], congrArg Outcome.done hle.2.2.1.symm⟩
    intro o ho
    have hoeq : o = Outcome.done s.out := hcongr o ho (.done s.out) ht_mem
    simp [hoeq]

/-- **R6b.** For every program, the flat model's behaviour refines the exposed model's. -/
theorem flat_semRefines_exposed (P : Prog) : SemRefines .flat .exposed P := by
  rw [SemRefines, beh_eq_of_after, beh_eq_of_after]
  cases ha : after .exposed P with
  | nil => left; simp
  | cons s rest =>
    right
    have hs : s ∈ after .exposed P := by rw [ha]; simp
    obtain ⟨f, hf, hrel⟩ := after_eraseRel P hs
    have hfl : after .flat P = [f] := by
      have hlen := execOk_det_length (Or.inl rfl) P init
      cases hfa : after .flat P with
      | nil => rw [hfa] at hf; simp at hf
      | cons f₀ frest =>
        rw [← after_eq_execOk, hfa] at hlen
        simp only [List.length_cons] at hlen
        have : frest = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst this
        rw [hfa, List.mem_singleton] at hf
        subst hf; rfl
    intro o ho
    simp only [hfl, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.map_cons,
      List.map_nil, List.mem_singleton] at ho
    subst ho
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.mem_cons]
    left
    rw [hrel.2.2.2.1]

/- R6c (`exposed_beh_elements_equal`) is stated and proved in `ToyProv.Erasure`. -/

/-- A and B adjacent and both exposed; `int2ptr` of B's start has two resolutions with the same
output. -/
def dupBehProg : Prog := [.alloc 0 2, .alloc 1 2, .ptr2int 2 0, .ptr2int 3 1, .int2ptr 4 3, .obs 4]

/-- **R6c, multiplicity.** `beh` keeps one entry per UB-free resolution, so the list can have
length 2 with equal elements; R6c bounds the number of *distinct* outcomes, not the length. -/
theorem exposed_beh_may_repeat :
    beh .exposed dupBehProg = [.done [18], .done [18]] ∧ beh .strict dupBehProg = [.done [18]] := by
  decide

/-- Round trip of A's address, store 7 through it, read A back. -/
def r6StrictUB : Prog :=
  [.alloc 0 2, .ptr2int 1 0, .int2ptr 2 1, .const 3 7, .store 2 3, .load 4 .int 0, .obs 4]
/-- Store 7 through the one-past-the-end pointer of A, read B back. -/
def r6ExposedUB : Prog :=
  [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .const 3 7, .store 2 3, .load 4 .int 1, .obs 4]

/-- **R6d.** Both orderings are strict: a program defined in `exposed` but UB in `strict`, and a
program defined in `flat` but UB in `exposed`. Neither reverse ordering holds. -/
theorem model_orderings_strict :
    beh .exposed r6StrictUB = [.done [7]] ∧ beh .strict r6StrictUB = [.ub] ∧
      ¬ SemRefines .strict .exposed r6StrictUB ∧
      beh .flat r6ExposedUB = [.done [7]] ∧ beh .exposed r6ExposedUB = [.ub] ∧
      ¬ SemRefines .exposed .flat r6ExposedUB := by
  decide

/-! ### R6e — transfer principles -/

/-- **R6e core (strict → exposed).** Order-theoretic step: if `tgt` refines `src` in `strict`,
`src`'s `strict` behaviours are `exposed` behaviours (`hsrc`), and `exposed` refines `strict` on
`tgt` (`hord`, an instance of R6a), then `tgt` refines `src` in `exposed`. -/
theorem refines_exposed_of_refines_strict_core (tgt src : Prog)
    (h : Refines .strict tgt src) (hsrc : SemRefines .strict .exposed src)
    (hord : SemRefines .exposed .strict tgt) : Refines .exposed tgt src := by
  rcases hsrc with hsrc | hsrc
  · exact Or.inl hsrc
  · rcases h with h | h
    · exact Or.inl (hsrc _ h)
    · rcases hord with ht | ht
      · exact Or.inl (hsrc _ (h _ ht))
      · exact Or.inr (fun o ho => hsrc _ (h _ (ht _ ho)))

/-- **R6e core (exposed → strict).** If `tgt` refines `src` in `exposed`, `tgt`'s `strict`
behaviours are `exposed` behaviours (`htgt`), and `exposed` refines `strict` on `src` (`hord`, an
instance of R6a), then `tgt` refines `src` in `strict`. -/
theorem refines_strict_of_refines_exposed_core (tgt src : Prog)
    (h : Refines .exposed tgt src) (htgt : SemRefines .strict .exposed tgt)
    (hord : SemRefines .exposed .strict src) : Refines .strict tgt src := by
  rcases hord with hs | hs
  · exact Or.inl hs
  · rcases h with h | h
    · exact Or.inl (hs _ h)
    · rcases htgt with ht | ht
      · exact Or.inl (hs _ (h _ ht))
      · exact Or.inr (fun o ho => hs _ (h _ (ht _ ho)))

/-- **R6e (strict → exposed).** A refinement in `strict` is a refinement in `exposed` whenever
every `strict` behaviour of the source is an `exposed` behaviour of it (or the source is UB in
`exposed`): `SemRefines .strict .exposed src`. Together with R6a this says the source behaves the
same in both models. (Uses R6a for the target.) -/
theorem refines_exposed_of_refines_strict_of_src_semRefines (tgt src : Prog)
    (h : Refines .strict tgt src) (hsrc : SemRefines .strict .exposed src) :
    Refines .exposed tgt src :=
  refines_exposed_of_refines_strict_core tgt src h hsrc (exposed_semRefines_strict tgt)

/-- **R6e (exposed → strict).** A refinement in `exposed` is a refinement in `strict` whenever
every `strict` behaviour of the target is an `exposed` behaviour of it (or the target is UB in
`exposed`): `SemRefines .strict .exposed tgt`. (Uses R6a for the source.) -/
theorem refines_strict_of_refines_exposed_of_tgt_semRefines (tgt src : Prog)
    (h : Refines .exposed tgt src) (htgt : SemRefines .strict .exposed tgt) :
    Refines .strict tgt src :=
  refines_strict_of_refines_exposed_core tgt src h htgt (exposed_semRefines_strict src)

/-- **R6e, `h` needed (both principles).** Two cast-free programs with different outputs: each
behaves the same in both models, yet neither refines the other. -/
theorem transfer_refines_needed :
    SemRefines .strict .exposed [.const 0 1, .obs 0] ∧ SemRefines .strict .exposed [.const 0 2, .obs 0] ∧
      ¬ Refines .exposed [.const 0 2, .obs 0] [.const 0 1, .obs 0] ∧
      ¬ Refines .strict [.const 0 2, .obs 0] [.const 0 1, .obs 0] := by
  decide

/-- **R6e, `hsrc` needed.** The boundary fold of R3b: a refinement in `strict` (the source is UB
there), not in `exposed`; the source's `strict` behaviour `[ub]` is not an `exposed` behaviour. -/
theorem transfer_to_exposed_src_agreement_needed :
    Refines .strict (r2bPreRT ++ .copy 4 2 :: r2bPostRT) (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) ∧
      ¬ SemRefines .strict .exposed (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) ∧
      ¬ Refines .exposed (r2bPreRT ++ .copy 4 2 :: r2bPostRT) (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) := by
  decide

/-- **R6e, `htgt` needed.** The round-trip introduction of R3c: a refinement in `exposed`, not in
`strict`; the target's `strict` behaviour `[ub]` is not an `exposed` behaviour. -/
theorem transfer_to_strict_tgt_agreement_needed :
    Refines .exposed (r3Pre ++ .int2ptr 2 1 :: r3Post) (r3Pre ++ .copy 2 0 :: r3Post) ∧
      ¬ SemRefines .strict .exposed (r3Pre ++ .int2ptr 2 1 :: r3Post) ∧
      ¬ Refines .strict (r3Pre ++ .int2ptr 2 1 :: r3Post) (r3Pre ++ .copy 2 0 :: r3Post) := by
  decide

/-- A cast-free pair: substitute an identical copy of A's pointer for A. -/
def r6dSrc : Prog := [.alloc 0 2, .copy 1 0, .const 2 7, .store 1 2, .load 3 .int 0, .obs 3]
def r6dTgt : Prog := [.alloc 0 2, .copy 1 0, .const 2 7, .store 0 2, .load 3 .int 0, .obs 3]

/-- **R6e non-vacuity.** A cast-free pair satisfies the hypotheses of both principles (and of the
core lemmas, including the R6a instances). -/
theorem transfer_nonvacuous :
    Refines .strict r6dTgt r6dSrc ∧ SemRefines .strict .exposed r6dSrc ∧
      Refines .exposed r6dTgt r6dSrc ∧ SemRefines .strict .exposed r6dTgt ∧
      SemRefines .exposed .strict r6dTgt ∧ SemRefines .exposed .strict r6dSrc ∧
      beh .strict r6dSrc = [.done [7]] := by
  decide

/-- **R6e, list equality is stronger than needed.** `dupBehProg` behaves the same in both models
in the sense of `SemRefines` in both directions, although the behaviour lists differ (length 2 vs
1). -/
theorem transfer_hyp_weaker_than_list_eq :
    SemRefines .strict .exposed dupBehProg ∧ SemRefines .exposed .strict dupBehProg ∧
      beh .exposed dupBehProg ≠ beh .strict dupBehProg := by
  decide

/-! ### R6f, R6g — table entries not already stated in R1–R4 -/

/- Table: `substAddrEq_sound_flat` is stated and proved in `ToyProv.FlatInv`. -/

/-- Table: `SubstIntEq` is sound in `flat`. -/
theorem substIntEq_sound_flat : Sound .flat SubstIntEq := by
  rintro src tgt ⟨pre, i, post, q, p, rfl, rfl, hc⟩
  apply substAddrEq_sound_flat
  refine ⟨pre, i, post, q, p, rfl, rfl, fun s hs => ?_⟩
  have h := hc s hs
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- Table: the cast fold is sound in `flat`. -/
theorem int2ptrToCopy_sound_flat : Sound .flat Int2ptrToCopy := by
  rintro src tgt ⟨pre, post, d, k, p, rfl, rfl, hk⟩
  apply refines_of_beh_eq
  apply beh_replace_of_step_eq
  intro s hs
  have hflat := after_flat_flatSt pre s hs
  have hkp := hk s hs
  simp only [intIsAddrOfC] at hkp
  cases hk' : s.regs k with
  | none => simp [hk'] at hkp
  | some vk =>
    cases vk with
    | ptr _ => simp [hk'] at hkp
    | int a =>
      cases hp' : s.regs p with
      | none => simp [hk', hp'] at hkp
      | some vp =>
        cases vp with
        | int _ => simp [hk', hp'] at hkp
        | ptr x =>
          simp only [hk', hp', beq_iff_eq] at hkp
          have hx : x.prov = none := hflat.1 p (.ptr x) hp'
          cases x; simp only at hkp hx; subst hkp; subst hx
          simp [step, hk', hp', castToPtr]

/-- Table: the cast fold is sound in `strict` (it only adds provenance to a pointer that had
none; by provenance monotonicity this never introduces UB). -/
theorem int2ptrToCopy_sound_strict : Sound .strict Int2ptrToCopy := by
  rintro src tgt ⟨pre, post, d, k, p, rfl, rfl, hk⟩
  rw [Refines, beh_eq_of_after, beh_eq_of_after]
  cases hsrc : after .strict (pre ++ .int2ptr d k :: post) with
  | nil => left; simp
  | cons s_end s_rest =>
    right
    have hs_end : s_end ∈ execOk .strict (pre ++ .int2ptr d k :: post) init := by
      rw [← after_eq_execOk, hsrc]; simp
    rw [execOk_append, List.mem_flatMap] at hs_end
    rcases hs_end with ⟨s, hs, hs_step⟩
    rw [execOk_cons, List.mem_flatMap] at hs_step
    rcases hs_step with ⟨s₁, hs₁, hs_post⟩
    have hkp := hk s hs
    simp only [intIsAddrOfC] at hkp
    cases hkreg : s.regs k with
    | none => simp [hkreg] at hkp
    | some vk =>
      cases vk with
      | ptr _ => simp [hkreg] at hkp
      | int a =>
        cases hpreg : s.regs p with
        | none => simp [hkreg, hpreg] at hkp
        | some vp =>
          cases vp with
          | int _ => simp [hkreg, hpreg] at hkp
          | ptr x =>
            simp only [hkreg, hpreg, beq_iff_eq] at hkp
            subst hkp
            have hs₁_eq : s₁ = s.setReg d (.ptr ⟨none, x.addr⟩) := by
              rw [List.mem_filterMap] at hs₁
              rcases hs₁ with ⟨o, ho, ho_eq⟩
              cases o with
              | none => simp at ho_eq
              | some st =>
                simp only [id_eq, Option.some.injEq] at ho_eq; subst ho_eq
                simp [step, hkreg, castToPtr] at ho; exact ho
            subst hs₁_eq
            have hle₁ : StLE (s.setReg d (.ptr ⟨none, x.addr⟩)) (s.setReg d (.ptr x)) :=
              stLE_setReg (stLE_refl s) d ⟨rfl, Or.inl rfl⟩
            obtain ⟨t_end, ht_post, hle_end⟩ :=
              execOk_mono (m₁ := .strict) (m₂ := .strict) (by decide) (by decide) (by decide) hle₁ hs_post
            have ht_end_mem : t_end ∈ after .strict (pre ++ .copy d p :: post) := by
              rw [after_eq_execOk, execOk_append, List.mem_flatMap]
              refine ⟨s, hs, ?_⟩
              rw [execOk_cons, List.mem_flatMap]
              refine ⟨s.setReg d (.ptr x), ?_, ht_post⟩
              simp [step, hpreg]
            have htl : after .strict (pre ++ .copy d p :: post) = [t_end] := by
              have hlen := execOk_det_length (Or.inr rfl) (pre ++ .copy d p :: post) init
              cases hta : after .strict (pre ++ .copy d p :: post) with
              | nil => rw [hta] at ht_end_mem; simp at ht_end_mem
              | cons t₀ trest =>
                rw [← after_eq_execOk, hta] at hlen
                simp only [List.length_cons] at hlen
                have : trest = [] := List.eq_nil_of_length_eq_zero (by omega)
                subst this
                rw [hta, List.mem_singleton] at ht_end_mem; subst ht_end_mem; rfl
            intro o ho
            simp only [htl, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.map_cons,
              List.map_nil, List.mem_singleton] at ho
            subst ho
            simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.mem_map]
            exact ⟨s_end, by simp, congrArg Outcome.done hle_end.2.2.1⟩

/-- Table, non-vacuity of the `strict` fold on a defined program: the source has no UB, and
folding the cast (which gives `d` A's provenance in a mixed-provenance byte copy) preserves the
output. -/
theorem int2ptrToCopy_strict_nonvacuous :
    Int2ptrToCopy .strict (r2bPreTorn ++ .int2ptr 5 3 :: r2bPostTorn) (r2bPreTorn ++ .copy 5 0 :: r2bPostTorn) ∧
      beh .strict (r2bPreTorn ++ .int2ptr 5 3 :: r2bPostTorn) = [.done [16]] ∧
      Refines .strict (r2bPreTorn ++ .copy 5 0 :: r2bPostTorn) (r2bPreTorn ++ .int2ptr 5 3 :: r2bPostTorn) :=
  ⟨⟨r2bPreTorn, r2bPostTorn, 5, 3, 0, rfl, rfl, by decide⟩, by decide, by decide⟩

/-- Table: the cast introduction is sound in `flat`. -/
theorem copyToInt2ptr_sound_flat : Sound .flat CopyToInt2ptr := by
  rintro src tgt ⟨pre, post, d, k, p, rfl, rfl, hk⟩
  apply refines_of_beh_eq
  apply beh_replace_of_step_eq
  intro s hs
  have hflat := after_flat_flatSt pre s hs
  have hkp := hk s hs
  simp only [intIsAddrOfC] at hkp
  cases hk' : s.regs k with
  | none => simp [hk'] at hkp
  | some vk =>
    cases vk with
    | ptr _ => simp [hk'] at hkp
    | int a =>
      cases hp' : s.regs p with
      | none => simp [hk', hp'] at hkp
      | some vp =>
        cases vp with
        | int _ => simp [hk', hp'] at hkp
        | ptr x =>
          simp only [hk', hp', beq_iff_eq] at hkp
          have hx : x.prov = none := hflat.1 p (.ptr x) hp'
          cases x; simp only at hkp hx; subst hkp; subst hx
          simp [step, hk', hp', castToPtr]

/-- A at 16 (not exposed), `k := 16`. -/
def r6PreU : Prog := [.alloc 0 2, .const 1 16]

/-- Table: the cast introduction is unsound in `exposed` when `p`'s allocation is not exposed. -/
theorem copyToInt2ptr_counterexample_exposed :
    CopyToInt2ptr .exposed (r6PreU ++ .copy 2 0 :: r3Post) (r6PreU ++ .int2ptr 2 1 :: r3Post) ∧
      ¬ Refines .exposed (r6PreU ++ .int2ptr 2 1 :: r3Post) (r6PreU ++ .copy 2 0 :: r3Post) :=
  ⟨⟨r6PreU, r3Post, 2, 1, 0, rfl, rfl, by decide⟩, by decide⟩

theorem copyToInt2ptr_not_sound_exposed : ¬ Sound .exposed CopyToInt2ptr :=
  fun h => copyToInt2ptr_counterexample_exposed.2 (h _ _ copyToInt2ptr_counterexample_exposed.1)

/-- **R6f.** In `exposed`, the cast introduction `d := p` ⟶ `d := int2ptr k` is a refinement if in
every reachable state at that point (`hk`) `k` holds `p`'s address and (`hc`) `p`'s allocation is
an `int2ptr` candidate for it (exposed, live, address in its closed range). Uniqueness is not
needed in this direction. -/
theorem copyToInt2ptr_refines_exposed_of_intIsAddrOf_of_provIsCand
    (pre post : Prog) (d k p : Reg)
    (hk : AllAfter .exposed pre (intIsAddrOfC k p))
    (hc : AllAfter .exposed pre (provIsCandC p)) :
    Refines .exposed (pre ++ .int2ptr d k :: post) (pre ++ .copy d p :: post) := by
  let src := pre ++ .copy d p :: post
  let tgt := pre ++ .int2ptr d k :: post
  rw [Refines, beh_eq_of_after .exposed src, beh_eq_of_after .exposed tgt]
  cases hsrc : after .exposed src with
  | nil => left; simp
  | cons s_end s_rest =>
    right
    have hs_end : s_end ∈ after .exposed src := by rw [hsrc]; simp
    rw [after_eq_execOk, execOk_append, List.mem_flatMap] at hs_end
    rcases hs_end with ⟨s, hs, hs_step⟩
    rw [execOk_cons, List.mem_flatMap] at hs_step
    rcases hs_step with ⟨s₁, hs₁, hs_post⟩
    have hkp := hk s hs
    have hcp := hc s hs
    simp only [intIsAddrOfC] at hkp
    simp only [provIsCandC] at hcp
    cases hkreg : s.regs k with
    | none => simp [hkreg] at hkp
    | some vk =>
      cases vk with
      | ptr _ => simp [hkreg] at hkp
      | int a =>
        cases hpreg : s.regs p with
        | none => simp [hkreg, hpreg] at hkp
        | some vp =>
          cases vp with
          | int _ => simp [hkreg, hpreg] at hkp
          | ptr x =>
            simp only [hkreg, hpreg, beq_iff_eq] at hkp
            subst hkp
            cases hxprov : x.prov with
            | none => simp [hpreg, hxprov] at hcp
            | some A =>
              simp only [hpreg, hxprov, List.contains_iff_mem] at hcp
              have hs₁_eq : s₁ = s.setReg d (.ptr x) := by
                rw [List.mem_filterMap] at hs₁
                rcases hs₁ with ⟨o, ho, ho_eq⟩
                cases o with
                | none => simp at ho_eq
                | some st =>
                  simp only [id_eq, Option.some.injEq] at ho_eq; subst ho_eq
                  simp [step, hpreg] at ho; exact ho
              subst hs₁_eq
              have hs₁_in_int : s.setReg d (.ptr x) ∈ (step .exposed s (.int2ptr d k)).filterMap id := by
                rw [List.mem_filterMap]
                refine ⟨some (s.setReg d (.ptr x)), ?_, rfl⟩
                simp only [step, hkreg, castToPtr]
                cases hcand : candidates s x.addr with
                | nil => rw [hcand] at hcp; simp at hcp
                | cons c cs =>
                  simp only [List.mem_map, Option.some.injEq]
                  refine ⟨A, ?_, ?_⟩
                  · rw [← hcand]; exact hcp
                  · cases x; simp only at hxprov; subst hxprov; rfl
              have ht_end : s_end ∈ after .exposed tgt := by
                rw [after_eq_execOk, execOk_append, List.mem_flatMap]
                refine ⟨s, hs, ?_⟩
                rw [execOk_cons, List.mem_flatMap]
                exact ⟨s.setReg d (.ptr x), hs₁_in_int, hs_post⟩
              have hsrc_mem : Outcome.done s_end.out ∈
                  (if (after .exposed src).isEmpty then [.ub]
                   else (after .exposed src).map (fun st => .done st.out)) := by
                rw [hsrc]; simp
              have hcongr := exposed_beh_elements_equal tgt
              rw [beh_eq_of_after] at hcongr
              have ht_mem : Outcome.done s_end.out ∈
                  (if (after .exposed tgt).isEmpty then [.ub]
                   else (after .exposed tgt).map (fun st => .done st.out)) := by
                cases hta : after .exposed tgt with
                | nil => rw [hta] at ht_end; simp at ht_end
                | cons t₀ trest =>
                  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.mem_map]
                  exact ⟨s_end, by rwa [← hta], rfl⟩
              intro o ho
              have hoeq : o = Outcome.done s_end.out := hcongr o ho (.done s_end.out) ht_mem
              rw [hoeq]
              simp

/-- **R6f, `hc` needed:** A not exposed (the table's `✗`). -/
theorem copyToInt2ptr_provIsCand_needed :
    AllAfter .exposed r6PreU (intIsAddrOfC 1 0) ∧
      ¬ Refines .exposed (r6PreU ++ .int2ptr 2 1 :: r3Post) (r6PreU ++ .copy 2 0 :: r3Post) :=
  ⟨by decide, by decide⟩

/-- **R6f, `hk` needed:** A and B exposed, `p` = A's start but `k` = B's address. -/
theorem copyToInt2ptr_intIsAddrOf_needed :
    AllAfter .exposed r2bPreK (provIsCandC 0) ∧
      ¬ Refines .exposed (r2bPreK ++ .int2ptr 3 2 :: [.const 4 7, .store 3 4, .load 5 .int 0, .obs 5])
        (r2bPreK ++ .copy 3 0 :: [.const 4 7, .store 3 4, .load 5 .int 0, .obs 5]) :=
  ⟨by decide, by decide⟩

/-- **R6f non-vacuity:** after `k := (int)A`, both hypotheses hold; the pair is the one of R3c. -/
theorem copyToInt2ptr_refines_exposed_nonvacuous :
    AllAfter .exposed r3Pre (intIsAddrOfC 1 0) ∧ AllAfter .exposed r3Pre (provIsCandC 0) ∧
      Refines .exposed (r3Pre ++ .int2ptr 2 1 :: r3Post) (r3Pre ++ .copy 2 0 :: r3Post) :=
  ⟨by decide, by decide, by decide⟩

/-- Table: dead-cast elimination is sound in `flat`. -/
theorem dropUnusedPtr2int_sound_flat : Sound .flat DropUnusedPtr2int :=
  dropUnusedPtr2int_sound_det (Or.inl rfl)

/-- Table: dead-cast elimination is sound in `strict`. -/
theorem dropUnusedPtr2int_sound_strict : Sound .strict DropUnusedPtr2int :=
  dropUnusedPtr2int_sound_det (Or.inr rfl)

/-- A at 16; after the rewrite point, A's address is guessed as 16, cast back, and stored
through. -/
def r6PostP : Prog := [.const 2 16, .int2ptr 3 2, .const 4 7, .store 3 4, .load 5 .int 0, .obs 5]

/-- Table: dead-cast elimination is unsound in `exposed`: the unused cast is what exposes A. -/
theorem dropUnusedPtr2int_counterexample_exposed :
    DropUnusedPtr2int .exposed ([.alloc 0 2] ++ .ptr2int 1 0 :: r6PostP) ([.alloc 0 2] ++ r6PostP) ∧
      ¬ Refines .exposed ([.alloc 0 2] ++ r6PostP) ([.alloc 0 2] ++ .ptr2int 1 0 :: r6PostP) :=
  ⟨⟨[.alloc 0 2], r6PostP, 1, 0, rfl, rfl, by decide, by decide⟩, by decide⟩

theorem dropUnusedPtr2int_not_sound_exposed : ¬ Sound .exposed DropUnusedPtr2int :=
  fun h => dropUnusedPtr2int_counterexample_exposed.2 (h _ _ dropUnusedPtr2int_counterexample_exposed.1)

/-- Table: forwarding across a store through a freshly cast pointer is sound in `strict`, and only
vacuously: every matching source is UB (`forwardAcrossCast_strict_src_ub`). -/
theorem forwardAcrossCast_sound_strict : Sound .strict ForwardAcrossCast := by
  intro src tgt h
  left
  rw [(forwardAcrossCast_strict_src_ub src tgt h).1]
  simp

/-- Table: dead-store elimination across a load through a freshly cast pointer is sound in
`strict`, and only vacuously: every matching source is UB (`dseAcrossCast_strict_src_ub`). -/
theorem dseAcrossCast_sound_strict : Sound .strict DSEAcrossCast := by
  intro src tgt h
  left
  rw [(dseAcrossCast_strict_src_ub src tgt h).1]
  simp

/-- Table: in-bounds address-equality substitution is sound in every model (R1c). -/
theorem substAddrEqInBounds_sound_all : ∀ m, Sound m SubstAddrEqInBounds :=
  substAddrEqInBounds_sound

/-- Table: the cast introduction with a candidate is sound in `exposed` (R6f). -/
theorem copyToInt2ptrIfCand_sound_exposed : Sound .exposed CopyToInt2ptrIfCand := by
  rintro src tgt ⟨pre, post, d, k, p, rfl, rfl, hk, hc⟩
  exact copyToInt2ptr_refines_exposed_of_intIsAddrOf_of_provIsCand pre post d k p hk hc

/-- **Vacuity of `CopyToInt2ptrIfCand` in `flat`.** In `flat` no reachable pointer has a
provenance (`FlatSt`), so `provIsCandC p` (which requires `p`'s provenance to be `some A`) holds
in no reachable state. Hence the side condition forces `after .flat pre = []`, and both the source
and the target of every pair in the relation are UB in `flat`. -/
theorem copyToInt2ptrIfCand_flat_src_ub (src tgt : Prog)
    (h : CopyToInt2ptrIfCand .flat src tgt) :
    beh .flat src = [.ub] ∧ beh .flat tgt = [.ub] := by
  rcases h with ⟨pre, post, d, k, p, rfl, rfl, -, hc⟩
  have hpre : after .flat pre = [] := by
    cases ha : after .flat pre with
    | nil => rfl
    | cons s rest =>
      have hs : s ∈ after .flat pre := by rw [ha]; simp
      have hflat := after_flat_flatSt pre s hs
      have hpc := hc s hs
      simp only [provIsCandC] at hpc
      cases hr : s.regs p with
      | none => simp [hr] at hpc
      | some v =>
        cases v with
        | int _ => simp [hr] at hpc
        | ptr x =>
          have hx : x.prov = none := hflat.1 p (.ptr x) hr
          simp [hr, hx] at hpc
  have hempty : ∀ W : Prog, beh .flat (pre ++ W) = [.ub] := by
    intro W
    rw [beh_eq_of_after, after_eq_execOk, execOk_append, ← after_eq_execOk, hpre]
    rfl
  exact ⟨hempty _, hempty _⟩

/-- The pair of R3c, defined in `flat`, is not in `CopyToInt2ptrIfCand .flat` (although it is in
`CopyToInt2ptr .flat` and in `CopyToInt2ptrIfCand .exposed`). -/
theorem not_copyToInt2ptrIfCand_flat_r3 :
    ¬ CopyToInt2ptrIfCand .flat (r3Pre ++ .copy 2 0 :: r3Post) (r3Pre ++ .int2ptr 2 1 :: r3Post) := by
  intro h
  have hub := (copyToInt2ptrIfCand_flat_src_ub _ _ h).1
  have hne : beh .flat (r3Pre ++ .copy 2 0 :: r3Post) ≠ [.ub] := by decide
  exact hne hub

/-- Table: the cast introduction with a candidate is sound in `flat`, and only vacuously: every
matching source is UB (`copyToInt2ptrIfCand_flat_src_ub`). The informative flat statement is
`copyToInt2ptr_sound_flat`, which has no candidate condition. -/
theorem copyToInt2ptrIfCand_sound_flat : Sound .flat CopyToInt2ptrIfCand := by
  intro src tgt h
  left
  rw [(copyToInt2ptrIfCand_flat_src_ub src tgt h).1]
  simp

/-- Table: the cast introduction with a candidate is unsound in `strict`: R3c's pair satisfies the
side conditions (`ptr2int` records exposure in every model). -/
theorem copyToInt2ptrIfCand_counterexample_strict :
    CopyToInt2ptrIfCand .strict (r3Pre ++ .copy 2 0 :: r3Post) (r3Pre ++ .int2ptr 2 1 :: r3Post) ∧
      ¬ Refines .strict (r3Pre ++ .int2ptr 2 1 :: r3Post) (r3Pre ++ .copy 2 0 :: r3Post) :=
  ⟨⟨r3Pre, r3Post, 2, 1, 0, rfl, rfl, by decide, by decide⟩, by decide⟩

theorem copyToInt2ptrIfCand_not_sound_strict : ¬ Sound .strict CopyToInt2ptrIfCand :=
  fun h => copyToInt2ptrIfCand_counterexample_strict.2 (h _ _ copyToInt2ptrIfCand_counterexample_strict.1)

/-- **R6g, soundness does not transfer in either direction.** `DropUnusedPtr2int` is sound in
`strict` and unsound in `exposed`; `CopyToInt2ptrIfCand` is sound in `exposed` and unsound in
`strict`. (Uses the table theorems `dropUnusedPtr2int_sound_strict` and R6f.) -/
theorem soundness_does_not_transfer_either_way :
    (Sound .strict DropUnusedPtr2int ∧ ¬ Sound .exposed DropUnusedPtr2int) ∧
      (Sound .exposed CopyToInt2ptrIfCand ∧ ¬ Sound .strict CopyToInt2ptrIfCand) :=
  ⟨⟨dropUnusedPtr2int_sound_strict, dropUnusedPtr2int_not_sound_exposed⟩,
   ⟨copyToInt2ptrIfCand_sound_exposed, copyToInt2ptrIfCand_not_sound_strict⟩⟩

/-- **R6g, the same on single rewrites (fully evaluated).** A `DropUnusedPtr2int` rewrite that is
a refinement in `strict` and not in `exposed`, and a `CopyToInt2ptrIfCand` rewrite that is a
refinement in `exposed` and not in `strict`. -/
theorem refines_does_not_transfer_either_way :
    (DropUnusedPtr2int .strict ([.alloc 0 2] ++ .ptr2int 1 0 :: r6PostP) ([.alloc 0 2] ++ r6PostP) ∧
      Refines .strict ([.alloc 0 2] ++ r6PostP) ([.alloc 0 2] ++ .ptr2int 1 0 :: r6PostP) ∧
      ¬ Refines .exposed ([.alloc 0 2] ++ r6PostP) ([.alloc 0 2] ++ .ptr2int 1 0 :: r6PostP)) ∧
    (CopyToInt2ptrIfCand .exposed (r3Pre ++ .copy 2 0 :: r3Post) (r3Pre ++ .int2ptr 2 1 :: r3Post) ∧
      Refines .exposed (r3Pre ++ .int2ptr 2 1 :: r3Post) (r3Pre ++ .copy 2 0 :: r3Post) ∧
      ¬ Refines .strict (r3Pre ++ .int2ptr 2 1 :: r3Post) (r3Pre ++ .copy 2 0 :: r3Post)) :=
  ⟨⟨⟨[.alloc 0 2], r6PostP, 1, 0, rfl, rfl, by decide, by decide⟩, by decide, by decide⟩,
   ⟨r3Pre, r3Post, 2, 1, 0, rfl, rfl, by decide, by decide⟩, by decide, by decide⟩

/-- Code before the rewrite point for the `SubstSameVal` witness: A and an identical copy (register
1) of A's pointer. -/
def r6gSameValPre : Prog := [.alloc 0 2, .copy 1 0, .const 2 7]
/-- Read A back and observe it. -/
def r6gReadPost : Prog := [.load 3 .int 0, .obs 3]
/-- After an unused `ptr2int`: store 7 into A, read it back. -/
def r6gDropPost : Prog := [.const 2 7, .store 0 2, .load 3 .int 0, .obs 3]

/-- **R6g non-vacuity.** Every `✓` cell of the table other than the three vacuous ones
(`soundness_table_vacuous_cells`) is inhabited by a pair in the relation whose source is
defined in that model, with the stated output. -/
theorem soundness_table_nonvacuous :
    (SubstAddrEq .flat r1Src r1Tgt ∧ beh .flat r1Src = [.done [1, 7]]) ∧
    (∀ m, SubstAddrEqInBounds m (r1cPreNV ++ .store 1 3 :: [.load 4 .int 0, .obs 4])
        (r1cPreNV ++ (Instr.store 1 3).substUse 1 2 :: [.load 4 .int 0, .obs 4]) ∧
      beh m (r1cPreNV ++ .store 1 3 :: [.load 4 .int 0, .obs 4]) = [.done [7]]) ∧
    (SubstIntEq .flat r2Src r2Tgt ∧ beh .flat r2Src = [.done [1, 7]]) ∧
    (∀ m, SubstSameVal m (r6gSameValPre ++ .store 1 2 :: r6gReadPost)
        (r6gSameValPre ++ (Instr.store 1 2).substUse 1 0 :: r6gReadPost) ∧
      beh m (r6gSameValPre ++ .store 1 2 :: r6gReadPost) = [.done [7]]) ∧
    (∀ m, m ≠ .exposed →
      Int2ptrToCopy m (r2bPreTorn ++ .int2ptr 5 3 :: r2bPostTorn) (r2bPreTorn ++ .copy 5 0 :: r2bPostTorn) ∧
        beh m (r2bPreTorn ++ .int2ptr 5 3 :: r2bPostTorn) = [.done [16]]) ∧
    (CopyToInt2ptr .flat (r3Pre ++ .copy 2 0 :: r3Post) (r3Pre ++ .int2ptr 2 1 :: r3Post) ∧
      beh .flat (r3Pre ++ .copy 2 0 :: r3Post) = [.done [7]]) ∧
    (CopyToInt2ptrIfCand .exposed (r3Pre ++ .copy 2 0 :: r3Post) (r3Pre ++ .int2ptr 2 1 :: r3Post) ∧
      beh .exposed (r3Pre ++ .copy 2 0 :: r3Post) = [.done [7]]) ∧
    (∀ m, m ≠ .exposed →
      DropUnusedPtr2int m ([.alloc 0 2] ++ .ptr2int 1 0 :: r6gDropPost) ([.alloc 0 2] ++ r6gDropPost) ∧
        beh m ([.alloc 0 2] ++ .ptr2int 1 0 :: r6gDropPost) = [.done [7]]) := by
  refine ⟨⟨⟨r1Pre, _, r1Post, 1, 2, rfl, rfl, by decide⟩, by decide⟩, ?_,
    ⟨⟨r2Pre, _, r2Post, 1, 2, rfl, rfl, by decide⟩, by decide⟩, ?_, ?_,
    ⟨⟨r3Pre, r3Post, 2, 1, 0, rfl, rfl, by decide⟩, by decide⟩,
    ⟨⟨r3Pre, r3Post, 2, 1, 0, rfl, rfl, by decide, by decide⟩, by decide⟩, ?_⟩
  · intro m
    cases m <;> exact ⟨⟨_, _, _, 1, 2, rfl, rfl, by decide⟩, by decide⟩
  · intro m
    cases m <;> exact ⟨⟨_, _, _, 1, 0, rfl, rfl, by decide⟩, by decide⟩
  · intro m hm
    cases m
    · exact ⟨⟨r2bPreTorn, r2bPostTorn, 5, 3, 0, rfl, rfl, by decide⟩, by decide⟩
    · exact ⟨⟨r2bPreTorn, r2bPostTorn, 5, 3, 0, rfl, rfl, by decide⟩, by decide⟩
    · exact absurd rfl hm
  · intro m hm
    cases m
    · exact ⟨⟨[.alloc 0 2], r6gDropPost, 1, 0, rfl, rfl, by decide, by decide⟩, by decide⟩
    · exact ⟨⟨[.alloc 0 2], r6gDropPost, 1, 0, rfl, rfl, by decide, by decide⟩, by decide⟩
    · exact absurd rfl hm

/-- **R6g, the vacuous `✓` cells.** In these three cells every pair in the relation has a source
that is UB in that model, so the corresponding `Sound` theorems hold only vacuously. -/
theorem soundness_table_vacuous_cells :
    (∀ src tgt, CopyToInt2ptrIfCand .flat src tgt → beh .flat src = [.ub]) ∧
    (∀ src tgt, ForwardAcrossCast .strict src tgt → beh .strict src = [.ub]) ∧
    (∀ src tgt, DSEAcrossCast .strict src tgt → beh .strict src = [.ub]) :=
  ⟨fun src tgt h => (copyToInt2ptrIfCand_flat_src_ub src tgt h).1,
   fun src tgt h => (forwardAcrossCast_strict_src_ub src tgt h).1,
   fun src tgt h => (dseAcrossCast_strict_src_ub src tgt h).1⟩

end Toy.Prov
