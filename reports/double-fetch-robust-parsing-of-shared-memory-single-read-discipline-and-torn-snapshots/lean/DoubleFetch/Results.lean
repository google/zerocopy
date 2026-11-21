import DoubleFetch.Theory

/-!
# Results

Every result is quantified over all writers (`Adversary`) unless a writer constraint is named in
its hypotheses. These are statements about the toy model; they neither establish nor refute the
corresponding claims about real parsers, compilers, kernels or hypervisors.
Model–system relation: none proved.
-/

namespace Toy.DoubleFetch

/-! ## 1. Snapshots and byte-by-byte copies -/

section Snapshots

variable {n : Nat} {α : Type}

/-- Parsing an atomic snapshot returns the spec of the state at the snapshot's time (time `0`)
against every writer; in particular it is R-state. -/
theorem snapParse_exec_eq_and_rstate (spec : Region n → α) :
    (∀ adv : Adversary n, (snapParse spec).exec adv = spec (adv 0)) ∧
      RState spec (snapParse spec) :=
  ⟨fun _ => rfl, fun _ => ⟨0, rfl⟩⟩

/-- Parsing a byte-by-byte copy returns the spec of the diagonal vector `fun j => adv j.val j`
(address `j` as the writer had it at time `j`) against every writer; in particular it is
R-valid. -/
theorem copyParse_exec_eq_diagonal_and_rvalid (spec : Region n → α) :
    (∀ adv : Adversary n, (copyParse spec).exec adv = spec (fun j => adv j.val j)) ∧
      RValid spec (copyParse spec) := by
  have h : ∀ adv : Adversary n, (copyParse spec).exec adv = spec (fun j => adv j.val j) := by
    intro adv
    simp only [copyParse, byteCopy, Prog.exec]
    rw [readSeq_execFrom, fillSeq_finRange]
    rfl
  exact ⟨h, fun adv => ⟨_, h adv⟩⟩

/-- The byte-by-byte copy parser is single-read and implements its spec in private memory. -/
theorem copyParse_singleRead_implements (spec : Region n → α) :
    SingleRead (copyParse spec) ∧ Implements (copyParse spec) spec := by
  refine ⟨?_, fun s => ?_⟩
  · exact readSeq_singleReadFrom _ (List.nodup_finRange n) _ _ _ (fun _ _ => rfl)
      (fun _ _ => trivial)
  · rw [← Prog.exec_const, (copyParse_exec_eq_diagonal_and_rvalid spec).1]
    rfl

end Snapshots

/-- Torn copy: against the writer `pairTornAdv` (`(0,0)` at time `0`, `(1,1)` afterwards), parsing
a byte-by-byte copy of the pair returns `(0, 1)`, the pair of no state the writer produced; so the
byte-by-byte copy parser is not R-state. -/
theorem copyParse_pair_torn_not_rstate :
    (copyParse pairSpec).exec pairTornAdv = (0, 1) ∧
      (∀ t : Nat, (copyParse pairSpec).exec pairTornAdv ≠ pairSpec (pairTornAdv t)) ∧
      ¬ RState pairSpec (copyParse pairSpec) := by
  have h1 : (copyParse pairSpec).exec pairTornAdv = (0, 1) := by
    rw [(copyParse_exec_eq_diagonal_and_rvalid pairSpec).1]
    decide
  have h2 : ∀ t : Nat, (copyParse pairSpec).exec pairTornAdv ≠ pairSpec (pairTornAdv t) := by
    intro t
    rw [h1]
    by_cases ht : t = 0
    · subst ht; decide
    · simp only [pairTornAdv, ht, ite_false]; decide
  exact ⟨h1, h2, fun hR => by obtain ⟨t, ht⟩ := hR pairTornAdv; exact h2 t ht⟩

/-! ## 2. Single-read sufficiency -/

section SingleReadSection

variable {n : Nat} {α : Type}

/-- Single-read sufficiency, exact form: if `p` reads each address at most once on every path,
then against every writer `adv` and for every filler `d`, the run returns the private-memory
result on the assembled vector `p.assemble adv d` (bytes as read; unread addresses from `d`). -/
theorem singleRead_exec_eq_eval_assemble (p : Prog n α) (hp : SingleRead p)
    (adv : Adversary n) (d : Region n) : p.exec adv = p.eval (p.assemble adv d) :=
  Prog.execFrom_eq_eval_assembleFrom p _ hp adv 0 d

/-- Single-read sufficiency for R-valid: a single-read parser that implements `spec` in private
memory is R-valid for `spec`. -/
theorem rvalid_of_singleRead_of_implements (spec : Region n → α) (p : Prog n α)
    (hp : SingleRead p) (himpl : Implements p spec) : RValid spec p := fun adv =>
  ⟨p.assemble adv (fun _ => 0), by rw [singleRead_exec_eq_eval_assemble p hp adv _, himpl]⟩

/-- Single-read sufficiency for R-safe: if a single-read parser's private-memory result satisfies
the state-independent predicate `safe` on every region, it satisfies `safe` against every
writer. -/
theorem rsafe_of_singleRead_of_staticSafe (safe : α → Prop) (p : Prog n α)
    (hp : SingleRead p) (hsafe : ∀ s : Region n, safe (p.eval s)) : RSafe safe p := fun adv => by
  rw [singleRead_exec_eq_eval_assemble p hp adv (fun _ => 0)]
  exact hsafe _

end SingleReadSection

/-! ## 3. Robust result refinement -/

section Robust

variable {n : Nat} {α : Type}

/-- Robust result refinement is exactly preservation of R-safety: `q` robustly refines `p` iff
every state-independent predicate `safe` on results that holds for `p` against every writer holds
for `q` against every writer. -/
theorem robustRefines_iff_preserves_rsafe (q p : Prog n α) :
    RobustRefines q p ↔ ∀ safe : α → Prop, RSafe safe p → RSafe safe q := by
  constructor
  · intro hqp safe hp adv
    obtain ⟨adv', h⟩ := hqp adv
    rw [h]
    exact hp adv'
  · intro h adv
    obtain ⟨adv', h'⟩ := h (fun a => ∃ adv' : Adversary n, p.exec adv' = a) (fun adv => ⟨adv, rfl⟩) adv
    exact ⟨adv', h'.symm⟩

/-- Robust result refinement transfers R-safe. -/
theorem rsafe_of_robustRefines (safe : α → Prop) (q p : Prog n α) (hqp : RobustRefines q p)
    (hp : RSafe safe p) : RSafe safe q :=
  (robustRefines_iff_preserves_rsafe q p).mp hqp safe hp

/-- Robust result refinement transfers R-valid. -/
theorem rvalid_of_robustRefines (spec : Region n → α) (q p : Prog n α) (hqp : RobustRefines q p)
    (hp : RValid spec p) : RValid spec q :=
  rsafe_of_robustRefines (fun a => ∃ s' : Region n, a = spec s') q p hqp hp

/-- Observable-access refinement implies robust result refinement. -/
theorem robustRefines_of_obsRefines (q p : Prog n α) (h : ObsRefines q p) : RobustRefines q p :=
  fun adv => by
    obtain ⟨adv', e⟩ := h adv
    exact ⟨adv', by rw [← Prog.obs_snd, e, Prog.obs_snd]⟩

theorem obsFrom_shift (p : Prog n α) (adv : Adversary n) (t : Nat) :
    p.obsFrom adv (t + 1) = p.obsFrom (fun k => adv (k + 1)) t := by
  induction p generalizing t with
  | ret a => rfl
  | read i k ih =>
    simp only [Prog.obsFrom]
    rw [ih (adv (t + 1) i) (t + 1)]
  | snap k ih =>
    simp only [Prog.obsFrom]
    rw [ih (adv (t + 1)) (t + 1)]

/-- Observable-access refinement is equality: when every memory access is an observable event
(with the bytes seen), `q` observably refines `p` iff `q` and `p` are the same parser. -/
theorem obsRefines_iff_eq (q p : Prog n α) : ObsRefines q p ↔ q = p := by
  constructor
  · intro hobs
    induction q generalizing p with
    | ret a =>
      obtain ⟨adv', h⟩ := hobs (fun _ _ => 0)
      cases p with
      | ret a' =>
        simp only [Prog.obs, Prog.obsFrom, Prod.mk.injEq] at h
        rw [h.2]
      | read i kp => simp [Prog.obs, Prog.obsFrom] at h
      | snap kp => simp [Prog.obs, Prog.obsFrom] at h
    | read i kq ih =>
      obtain ⟨adv0', h0⟩ := hobs (fun _ _ => 0)
      cases p with
      | ret a' => simp [Prog.obs, Prog.obsFrom] at h0
      | snap kp => simp [Prog.obs, Prog.obsFrom] at h0
      | read j kp =>
        simp only [Prog.obs, Prog.obsFrom, Prod.mk.injEq, List.cons.injEq,
          Event.rd.injEq] at h0
        obtain ⟨⟨⟨hij, _⟩, _⟩, _⟩ := h0
        subst hij
        congr 1
        funext b
        apply ih b (kp b)
        intro adv1
        let adv : Adversary n := fun t => if t = 0 then (fun _ => b) else adv1 (t - 1)
        obtain ⟨adv', h⟩ := hobs adv
        simp only [Prog.obs, Prog.obsFrom, Prod.mk.injEq, List.cons.injEq,
          Event.rd.injEq] at h
        have hadv0 : adv 0 i = b := rfl
        rw [hadv0] at h
        obtain ⟨⟨⟨_, hb'⟩, htl⟩, hres⟩ := h
        have hb : adv' 0 i = b := hb'.symm
        rw [hb] at htl hres
        have hpair : (kq b).obsFrom adv 1 = (kp b).obsFrom adv' 1 := Prod.ext htl hres
        rw [obsFrom_shift, obsFrom_shift] at hpair
        have hshift : (fun k => adv (k + 1)) = adv1 := by
          funext k
          simp [adv]
        rw [hshift] at hpair
        exact ⟨fun k => adv' (k + 1), hpair⟩
    | snap kq ih =>
      obtain ⟨adv0', h0⟩ := hobs (fun _ _ => 0)
      cases p with
      | ret a' => simp [Prog.obs, Prog.obsFrom] at h0
      | read j kp => simp [Prog.obs, Prog.obsFrom] at h0
      | snap kp =>
        congr 1
        funext s
        apply ih s (kp s)
        intro adv1
        let adv : Adversary n := fun t => if t = 0 then s else adv1 (t - 1)
        obtain ⟨adv', h⟩ := hobs adv
        simp only [Prog.obs, Prog.obsFrom, Prod.mk.injEq, List.cons.injEq,
          Event.sn.injEq] at h
        have hadv0 : adv 0 = s := rfl
        rw [hadv0] at h
        obtain ⟨⟨hs', htl⟩, hres⟩ := h
        have hs : adv' 0 = s := hs'.symm
        rw [hs] at htl hres
        have hpair : (kq s).obsFrom adv 1 = (kp s).obsFrom adv' 1 := Prod.ext htl hres
        rw [obsFrom_shift, obsFrom_shift] at hpair
        have hshift : (fun k => adv (k + 1)) = adv1 := by
          funext k
          simp [adv]
        rw [hshift] at hpair
        exact ⟨fun k => adv' (k + 1), hpair⟩
  · rintro rfl adv
    exact ⟨adv, rfl⟩

/-- R-valid characterized by refinement: `p` is R-valid for `spec` iff `p` robustly refines some
single-read parser that implements `spec` in private memory (for example `copyParse spec`). -/
theorem rvalid_iff_robustRefines_singleRead_implementation (spec : Region n → α) (p : Prog n α) :
    RValid spec p ↔ ∃ q : Prog n α, SingleRead q ∧ Implements q spec ∧ RobustRefines p q := by
  constructor
  · intro hp
    obtain ⟨hs, hi⟩ := copyParse_singleRead_implements spec
    refine ⟨copyParse spec, hs, hi, fun adv => ?_⟩
    obtain ⟨s', hs'⟩ := hp adv
    exact ⟨Adversary.const s', by rw [Prog.exec_const, hi, hs']⟩
  · rintro ⟨q, hq, hi, href⟩
    exact rvalid_of_robustRefines spec p q href (rvalid_of_singleRead_of_implements spec q hq hi)

/-- The single-read implementation in `rvalid_iff_robustRefines_singleRead_implementation` can
always be taken to be the byte-by-byte copy parser: `p` is R-valid for `spec` iff `p` robustly
refines `copyParse spec`. -/
theorem rvalid_iff_robustRefines_copyParse (spec : Region n → α) (p : Prog n α) :
    RValid spec p ↔ RobustRefines p (copyParse spec) := by
  obtain ⟨hs, hi⟩ := copyParse_singleRead_implements spec
  constructor
  · intro hp adv
    obtain ⟨s', hs'⟩ := hp adv
    exact ⟨Adversary.const s', by rw [Prog.exec_const, hi, hs']⟩
  · intro href
    exact rvalid_of_robustRefines spec p _ href (rvalid_of_singleRead_of_implements spec _ hs hi)

end Robust

/-! ## 4. Re-read and compare -/

/-- The re-read-and-compare parser implements `boolParse` in private memory. -/
theorem rereadCompare_implements : Implements rereadCompare boolParse := by
  intro s
  simp only [rereadCompare, Prog.eval, ite_true]
  congr 1
  funext j
  have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
  subst hj
  rfl

/-- Single read is not necessary: the re-read-and-compare parser implements `boolParse` in private
memory and reads its one address twice, yet it is R-valid for `boolParse` and its results are
valid `bool` representations against every writer; it is not R-state. -/
theorem rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate :
    Implements rereadCompare boolParse ∧ RValid boolParse rereadCompare ∧
      RSafe ValidBoolOut rereadCompare ∧ ¬ SingleRead rereadCompare ∧
      ¬ RState boolParse rereadCompare := by
  refine ⟨rereadCompare_implements, fun adv => ?_, fun adv => ?_, fun h => ?_, fun hR => ?_⟩
  · simp only [rereadCompare, Prog.exec, Prog.execFrom]
    by_cases hb : adv 0 0 = adv 1 0
    · exact ⟨fun _ => adv 0 0, by simp [hb]⟩
    · exact ⟨fun _ => 2, by simp [hb, boolParse]⟩
  · simp only [rereadCompare, Prog.exec, Prog.execFrom]
    by_cases hb : adv 0 0 = adv 1 0
    · simp only [hb, ite_true, boolParse]
      split
      · assumption
      · trivial
    · simp [hb, ValidBoolOut]
  · obtain ⟨_, h2⟩ := h
    obtain ⟨h3, _⟩ := h2 0
    simp at h3
  · obtain ⟨t, ht⟩ := hR (fun t _ => if t = 0 then 0 else 1)
    simp only [rereadCompare, Prog.exec, Prog.execFrom] at ht
    by_cases h : t = 0
    · subst h; simp [boolParse] at ht
    · simp [boolParse, h] at ht

/-- Re-read with a fallback works for every spec on a one-byte region, including specs without an
error result: it implements the spec, is R-valid for it, and is not single-read. -/
theorem rereadFallback_implements_rvalid_not_singleRead {α : Type} (spec : Region 1 → α) :
    Implements (rereadFallback spec) spec ∧ RValid spec (rereadFallback spec) ∧
      ¬ SingleRead (rereadFallback spec) := by
  refine ⟨fun s => ?_, fun adv => ?_, fun h => ?_⟩
  · simp only [rereadFallback, Prog.eval, ite_true]
    congr 1
    funext j
    rw [Subsingleton.elim j 0]
  · simp only [rereadFallback, Prog.exec, Prog.execFrom]
    by_cases hb : adv 0 0 = adv 1 0
    · exact ⟨fun _ => adv 0 0, by simp [hb]⟩
    · exact ⟨fun _ => 0, by simp [hb]⟩
  · obtain ⟨_, h2⟩ := h
    obtain ⟨h3, _⟩ := h2 0
    simp at h3

/-- On a one-byte region, a single-read parser's result depends only on the writer's state at
time `0`. -/
theorem singleRead_oneByte_exec_congr {β : Type} (q : Prog 1 β) (hq : SingleRead q)
    (adv adv' : Adversary 1) (h : adv 0 = adv' 0) : q.exec adv = q.exec adv' := by
  cases q with
  | ret a => rfl
  | read i k =>
    obtain ⟨_, hk⟩ := hq
    simp only [Prog.exec, Prog.execFrom]
    rw [Prog.execFrom_eq_eval_of_allRead _ _ (fun j => by simp [Subsingleton.elim j i]) (hk _)
        adv 1 (adv 0),
      Prog.execFrom_eq_eval_of_allRead _ _ (fun j => by simp [Subsingleton.elim j i]) (hk _)
        adv' 1 (adv 0), h]
  | snap k =>
    obtain ⟨_, hk⟩ := hq
    simp only [Prog.exec, Prog.execFrom]
    rw [Prog.execFrom_eq_eval_of_allRead _ _ (fun _ => rfl) (hk _) adv 1 (adv 0),
      Prog.execFrom_eq_eval_of_allRead _ _ (fun _ => rfl) (hk _) adv' 1 (adv 0), h]

/-- No single-read parser on a one-byte region returns the same result as the re-read-and-compare
parser against every writer. -/
theorem rereadCompare_not_advEquiv_singleRead :
    ¬ ∃ q : Prog 1 (Option Byte), SingleRead q ∧ ∀ adv, q.exec adv = rereadCompare.exec adv := by
  rintro ⟨q, hq, heq⟩
  have e := singleRead_oneByte_exec_congr q hq (Adversary.const (fun _ => 0))
    (fun t _ => if t = 0 then 0 else 1) rfl
  rw [heq, heq] at e
  simp [rereadCompare, Prog.exec, Prog.execFrom, Adversary.const, boolParse] at e

/-! ## 5. Double-fetch counterexamples -/

section Length

/-- The single-read length parser is single-read and implements `lpParse cap` in private
memory. -/
theorem lenOnce_singleRead_implements (m cap : Nat) :
    SingleRead (lenOnce m cap) ∧ Implements (lenOnce m cap) (lpParse cap) := by
  refine ⟨⟨rfl, fun b => ?_⟩, fun s => ?_⟩
  · by_cases h : b.val ≤ cap <;> simp [lenCheck, CheckUse.pure, h, Prog.SingleReadFrom]
  · simp only [lenOnce, lenCheck, CheckUse.compile, CheckUse.pure, Prog.eval, lpParse]
    by_cases h : (s 0).val ≤ cap <;> simp [h, Prog.eval]

/-- The single-read length parser is R-safe (no out-of-bounds copy) and R-valid. -/
theorem lenOnce_rsafe_rvalid (m cap : Nat) :
    RSafe (CopyInBounds cap) (lenOnce m cap) ∧ RValid (lpParse cap) (lenOnce m cap) := by
  obtain ⟨hs, hi⟩ := lenOnce_singleRead_implements m cap
  refine ⟨rsafe_of_singleRead_of_staticSafe _ _ hs fun s => ?_,
    rvalid_of_singleRead_of_implements _ _ hs hi⟩
  rw [hi s]
  simp only [lpParse]
  split
  · simp only [CopyInBounds]; assumption
  · trivial

/-- The double-fetch length parser also implements `lpParse cap` in private memory. -/
theorem lenReread_implements (m cap : Nat) : Implements (lenReread m cap) (lpParse cap) := by
  intro s
  simp only [lenReread, lenCheck, CheckUse.remat, CheckUse.pure, Prog.eval, lpParse]
  by_cases h : (s 0).val ≤ cap <;> simp [h, Prog.eval]

/-- Length re-read: for `cap < 255`, against `lenFlipAdv` the double-fetch length parser copies
`cap + 1` bytes into the buffer of capacity `cap` (out of bounds), and its result equals
`lpParse cap s'` for no byte vector `s'`. -/
theorem lenReread_flip_out_of_bounds_and_invalid (m cap : Nat) (hcap : cap < 255) :
    (lenReread m cap).exec (lenFlipAdv m cap) = some (cap + 1) ∧
      ¬ CopyInBounds cap ((lenReread m cap).exec (lenFlipAdv m cap)) ∧
      ∀ s' : Region (m + 1), (lenReread m cap).exec (lenFlipAdv m cap) ≠ lpParse cap s' := by
  have h1 : (lenReread m cap).exec (lenFlipAdv m cap) = some (cap + 1) := by
    have e0 : cap % 256 = cap := Nat.mod_eq_of_lt (by omega)
    have e1 : (cap + 1) % 256 = cap + 1 := Nat.mod_eq_of_lt (by omega)
    simp [lenReread, lenCheck, CheckUse.remat, CheckUse.pure, Prog.exec, Prog.execFrom,
      lenFlipAdv, e0, e1]
  refine ⟨h1, ?_, ?_⟩
  · rw [h1]; simp [CopyInBounds]
  · intro s' h
    rw [h1] at h
    simp only [lpParse] at h
    split at h
    · simp at h; omega
    · simp at h

/-- For `cap < 255` the double-fetch length parser is neither R-safe nor R-valid. -/
theorem lenReread_not_rsafe_not_rvalid (m cap : Nat) (hcap : cap < 255) :
    ¬ RSafe (CopyInBounds cap) (lenReread m cap) ∧ ¬ RValid (lpParse cap) (lenReread m cap) := by
  obtain ⟨_, h2, h3⟩ := lenReread_flip_out_of_bounds_and_invalid m cap hcap
  exact ⟨fun h => h2 (h _), fun h => by obtain ⟨s', hs'⟩ := h (lenFlipAdv m cap); exact h3 s' hs'⟩

/-- Degenerate edge: for `cap ≥ 255` every byte passes the length check, and the double-fetch
length parser is R-safe and R-valid. -/
theorem lenReread_rsafe_rvalid_of_255_le_cap (m cap : Nat) (hcap : 255 ≤ cap) :
    RSafe (CopyInBounds cap) (lenReread m cap) ∧ RValid (lpParse cap) (lenReread m cap) := by
  have hle : ∀ b : Byte, b.val ≤ cap := fun b => by have := b.isLt; omega
  have hex : ∀ adv : Adversary (m + 1),
      (lenReread m cap).exec adv = some (adv 1 0).val := by
    intro adv
    simp [lenReread, lenCheck, CheckUse.remat, CheckUse.pure, Prog.exec, Prog.execFrom, hle]
  refine ⟨fun adv => ?_, fun adv => ⟨fun _ => adv 1 0, ?_⟩⟩
  · rw [hex]; exact hle _
  · rw [hex]; simp [lpParse, hle]

/-- Tightness of `cap < 255` for the length re-read results, in canonical form: with `m = 0` and
`cap = 255` the hypothesis fails and the double-fetch length parser is R-safe and R-valid. -/
theorem lenReread_cap255_counterexample :
    ¬ (255 < 255) ∧ RSafe (CopyInBounds 255) (lenReread 0 255) ∧
      RValid (lpParse 255) (lenReread 0 255) :=
  ⟨by decide, lenReread_rsafe_rvalid_of_255_le_cap 0 255 (by decide)⟩

/-- Non-vacuity of the hypothesis `cap < 255`: at `m = 0` and `cap = 4` it holds, and the
double-fetch length parser then returns `some 5` against `lenFlipAdv 0 4`. -/
theorem lenReread_cap_lt_255_nonvacuous :
    (4 : Nat) < 255 ∧ (lenReread 0 4).exec (lenFlipAdv 0 4) = some 5 :=
  ⟨by decide, (lenReread_flip_out_of_bounds_and_invalid 0 4 (by decide)).1⟩

end Length

/-- The two equivalence readings of "R-valid iff equivalent to a single-read parser" fail.
(i) Agreement against every writer: `rereadCompare` is R-valid for `boolParse`, but no single-read
parser on a one-byte region returns its result against every writer. (ii) Agreement in private
memory: for `cap < 255`, the double-fetch length parser agrees in private memory with the
single-read, R-valid `lenOnce m cap`, yet it is not R-valid. -/
theorem rvalid_equivalence_readings_refuted (m cap : Nat) (hcap : cap < 255) :
    (RValid boolParse rereadCompare ∧
      ¬ ∃ q : Prog 1 (Option Byte), SingleRead q ∧ ∀ adv, q.exec adv = rereadCompare.exec adv) ∧
    (SingleRead (lenOnce m cap) ∧ RValid (lpParse cap) (lenOnce m cap) ∧
      PrivRefines (lenReread m cap) (lenOnce m cap) ∧ ¬ RValid (lpParse cap) (lenReread m cap)) :=
  ⟨⟨rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate.2.1,
      rereadCompare_not_advEquiv_singleRead⟩,
    ⟨(lenOnce_singleRead_implements m cap).1, (lenOnce_rsafe_rvalid m cap).2,
      fun s => by rw [lenReread_implements, (lenOnce_singleRead_implements m cap).2],
      (lenReread_not_rsafe_not_rvalid m cap hcap).2⟩⟩

section Tag

/-- The single-read `bool` parser is single-read and implements `boolParse` in private memory. -/
theorem tagOnce_singleRead_implements (m : Nat) :
    SingleRead (tagOnce m) ∧ Implements (tagOnce m) boolParse := by
  refine ⟨⟨rfl, fun b => ?_⟩, fun s => ?_⟩
  · by_cases h : b.val ≤ 1 <;> simp [tagCheck, CheckUse.pure, h, Prog.SingleReadFrom]
  · simp only [tagOnce, tagCheck, CheckUse.compile, CheckUse.pure, Prog.eval, boolParse]
    by_cases h : (s 0).val ≤ 1 <;> simp [h, Prog.eval]

/-- The single-read `bool` parser is R-safe (valid `bool` representations only) and R-valid. -/
theorem tagOnce_rsafe_rvalid (m : Nat) :
    RSafe ValidBoolOut (tagOnce m) ∧ RValid boolParse (tagOnce m) := by
  obtain ⟨hs, hi⟩ := tagOnce_singleRead_implements m
  refine ⟨rsafe_of_singleRead_of_staticSafe _ _ hs fun s => ?_,
    rvalid_of_singleRead_of_implements _ _ hs hi⟩
  rw [hi s]
  simp only [boolParse]
  split
  · simp only [ValidBoolOut]; assumption
  · trivial

/-- The double-fetch `bool` parser also implements `boolParse` in private memory. -/
theorem tagReread_implements (m : Nat) : Implements (tagReread m) boolParse := by
  intro s
  simp only [tagReread, tagCheck, CheckUse.remat, CheckUse.pure, Prog.eval, boolParse]
  by_cases h : (s 0).val ≤ 1 <;> simp [h, Prog.eval]

/-- Tag re-read: against `tagFlipAdv` (`1` then `2`), the double-fetch `bool` parser validates
`1` and hands on the re-read byte `2`, which is not a valid `bool` representation and equals
`boolParse s'` for no byte vector `s'`. -/
theorem tagReread_flip_invalid_bool (m : Nat) :
    (tagReread m).exec (tagFlipAdv m) = some 2 ∧
      ¬ ValidBoolOut ((tagReread m).exec (tagFlipAdv m)) ∧
      ∀ s' : Region (m + 1), (tagReread m).exec (tagFlipAdv m) ≠ boolParse s' := by
  have h1 : (tagReread m).exec (tagFlipAdv m) = some 2 := by
    simp [tagReread, tagCheck, CheckUse.remat, CheckUse.pure, Prog.exec, Prog.execFrom,
      tagFlipAdv]
  refine ⟨h1, ?_, ?_⟩
  · rw [h1]; simp [ValidBoolOut]
  · intro s' h
    rw [h1] at h
    simp only [boolParse] at h
    split at h
    · rename_i hle
      simp only [Option.some.injEq] at h
      rw [← h] at hle
      simp at hle
    · simp at h

/-- The double-fetch `bool` parser is neither R-safe for `ValidBoolOut` nor R-valid for
`boolParse`. -/
theorem tagReread_not_rsafe_not_rvalid (m : Nat) :
    ¬ RSafe ValidBoolOut (tagReread m) ∧ ¬ RValid boolParse (tagReread m) := by
  obtain ⟨_, h2, h3⟩ := tagReread_flip_invalid_bool m
  exact ⟨fun h => h2 (h _), fun h => by obtain ⟨s', hs'⟩ := h (tagFlipAdv m); exact h3 s' hs'⟩

end Tag

/-! ## 6. Torn values: single read is not a consistent snapshot -/

/-- Checksum tearing: every state of the writer `ckTornAdv` passes the checksum, yet the
byte-by-byte copy parser returns `some (0, 1)`, which is `ckParse` of the byte vector `(0, 1, 1)`
and passes the checksum, but is `ckParse` of no state the writer produced. -/
theorem ckParse_torn_passes_checksum_matches_no_state :
    (∀ t : Nat, ckParse (ckTornAdv t) ≠ none) ∧
      (copyParse ckParse).exec ckTornAdv = some (0, 1) ∧
      (copyParse ckParse).exec ckTornAdv = ckParse (reg3 0 1 1) ∧
      ∀ t : Nat, (copyParse ckParse).exec ckTornAdv ≠ ckParse (ckTornAdv t) := by
  have h1 : (copyParse ckParse).exec ckTornAdv = some (0, 1) := by
    rw [(copyParse_exec_eq_diagonal_and_rvalid ckParse).1]
    decide
  have hcases : ∀ t : Nat, ckTornAdv t = reg3 0 0 0 ∨ ckTornAdv t = reg3 1 1 2 ∨
      ckTornAdv t = reg3 2 255 1 := by
    intro t
    simp only [ckTornAdv]
    by_cases h0 : t = 0
    · simp [h0]
    · by_cases h1 : t = 1 <;> simp [h0, h1]
  refine ⟨fun t => ?_, h1, by rw [h1]; decide, fun t => ?_⟩
  · rcases hcases t with h | h | h <;> rw [h] <;> decide
  · rw [h1]
    rcases hcases t with h | h | h <;> rw [h] <;> decide

theorem byte_add_one_ne (x : Byte) : x + 1 ≠ x := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_add] at this
  have := x.isLt
  simp at this
  omega

theorem byte_add_left_cancel {a b c : Byte} (h : a + b = a + c) : b = c := by
  apply Fin.ext
  have h' := congrArg Fin.val h
  rw [Fin.val_add, Fin.val_add] at h'
  have := a.isLt; have := b.isLt; have := c.isLt
  omega

theorem byte_add_right_cancel {a b c : Byte} (h : a + c = b + c) : a = b := by
  apply Fin.ext
  have h' := congrArg Fin.val h
  rw [Fin.val_add, Fin.val_add] at h'
  have := a.isLt; have := b.isLt; have := c.isLt
  omega

/-- Two checksum-passing states give no torn mismatch: if every state of the writer is one of two
regions `A` and `B` that both pass the checksum, then every checksum-passing result of the
byte-by-byte copy parser equals `ckParse A` or `ckParse B`. -/
theorem copyParse_ckParse_twoValidStates (A B : Region 3) (hA : A 2 = A 0 + A 1)
    (hB : B 2 = B 0 + B 1) (adv : Adversary 3) (hadv : ∀ t, adv t = A ∨ adv t = B)
    (hpass : (copyParse ckParse).exec adv ≠ none) :
    (copyParse ckParse).exec adv = ckParse A ∨ (copyParse ckParse).exec adv = ckParse B := by
  rw [(copyParse_exec_eq_diagonal_and_rvalid ckParse).1] at hpass ⊢
  have eA : ckParse A = some (A 0, A 1) := by simp [ckParse, hA]
  have eB : ckParse B = some (B 0, B 1) := by simp [ckParse, hB]
  rw [eA, eB]
  have hd : ckParse (fun j : Fin 3 => adv j.val j) =
      if adv 2 2 = adv 0 0 + adv 1 1 then some (adv 0 0, adv 1 1) else none := rfl
  rw [hd] at hpass ⊢
  by_cases hc : adv 2 2 = adv 0 0 + adv 1 1
  · rw [ite_eq_left hc]
    simp only [Option.some.injEq, Prod.mk.injEq]
    rcases hadv 0 with e0 | e0 <;> rcases hadv 1 with e1 | e1 <;> rcases hadv 2 with e2 | e2 <;>
      rw [e0, e1, e2] at hc <;> rw [e0, e1]
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, byte_add_left_cancel (hc.symm.trans hA)⟩
    · exact Or.inr ⟨byte_add_right_cancel (hc.symm.trans hB), rfl⟩
    · exact Or.inl ⟨byte_add_right_cancel (hc.symm.trans hA), rfl⟩
    · exact Or.inr ⟨rfl, byte_add_left_cancel (hc.symm.trans hB)⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd (ite_eq_right hc) hpass

/-- Tightness of `hA` (and, with `A` and `B` exchanged, of `hB`) in
`copyParse_ckParse_twoValidStates`: with `A = (1,1,1)` (fails the checksum) and `B = (0,0,0)`
(passes), the writer `ckMixAdv` (`B` at time `0`, `A` afterwards) shows only these two states, and
the byte-by-byte copy parser returns the checksum-passing `some (0, 1)`, which is neither
`ckParse A` nor `ckParse B`. -/
theorem copyParse_ckParse_twoValidStates_hA_counterexample :
    ¬ ((reg3 1 1 1) 2 = (reg3 1 1 1) 0 + (reg3 1 1 1) 1) ∧
      (reg3 0 0 0) 2 = (reg3 0 0 0) 0 + (reg3 0 0 0) 1 ∧
      (∀ t, ckMixAdv t = reg3 1 1 1 ∨ ckMixAdv t = reg3 0 0 0) ∧
      (copyParse ckParse).exec ckMixAdv = some (0, 1) ∧
      (copyParse ckParse).exec ckMixAdv ≠ ckParse (reg3 1 1 1) ∧
      (copyParse ckParse).exec ckMixAdv ≠ ckParse (reg3 0 0 0) := by
  have h1 : (copyParse ckParse).exec ckMixAdv = some (0, 1) := by
    rw [(copyParse_exec_eq_diagonal_and_rvalid ckParse).1]
    decide
  refine ⟨by decide, by decide, fun t => ?_, h1, by rw [h1]; decide, by rw [h1]; decide⟩
  by_cases ht : t = 0
  · right; simp [ckMixAdv, ht]
  · left; simp [ckMixAdv, ht]

/-- Tightness of `hadv` in `copyParse_ckParse_twoValidStates`: `ckTornAdv` shows the two
checksum-passing states `(0,0,0)` and `(1,1,2)` and a third one, and the byte-by-byte copy parser
returns the checksum-passing `some (0, 1)`, which is neither `ckParse` of `(0,0,0)` nor of
`(1,1,2)`. -/
theorem copyParse_ckParse_twoValidStates_hadv_counterexample :
    (reg3 0 0 0) 2 = (reg3 0 0 0) 0 + (reg3 0 0 0) 1 ∧
      (reg3 1 1 2) 2 = (reg3 1 1 2) 0 + (reg3 1 1 2) 1 ∧
      ¬ (∀ t, ckTornAdv t = reg3 0 0 0 ∨ ckTornAdv t = reg3 1 1 2) ∧
      (copyParse ckParse).exec ckTornAdv = some (0, 1) ∧
      (copyParse ckParse).exec ckTornAdv ≠ ckParse (reg3 0 0 0) ∧
      (copyParse ckParse).exec ckTornAdv ≠ ckParse (reg3 1 1 2) := by
  have h1 := ckParse_torn_passes_checksum_matches_no_state.2.1
  refine ⟨by decide, by decide, fun h => ?_, h1, by rw [h1]; decide, by rw [h1]; decide⟩
  rcases h 2 with e | e
  · have := congrFun e 0; revert this; decide
  · have := congrFun e 0; revert this; decide

/-- Tightness of `hpass` in `copyParse_ckParse_twoValidStates`: against the writer showing
`(0,0,0)` at time `0` and `(1,1,2)` afterwards (both pass the checksum), the byte-by-byte copy
parser returns the error result, which is neither `ckParse` of `(0,0,0)` nor of `(1,1,2)`. -/
theorem copyParse_ckParse_twoValidStates_hpass_counterexample :
    (reg3 0 0 0) 2 = (reg3 0 0 0) 0 + (reg3 0 0 0) 1 ∧
      (reg3 1 1 2) 2 = (reg3 1 1 2) 0 + (reg3 1 1 2) 1 ∧
      (∀ t, (fun t => if t = 0 then reg3 0 0 0 else reg3 1 1 2 : Adversary 3) t = reg3 0 0 0 ∨
        (fun t => if t = 0 then reg3 0 0 0 else reg3 1 1 2 : Adversary 3) t = reg3 1 1 2) ∧
      (copyParse ckParse).exec (fun t => if t = 0 then reg3 0 0 0 else reg3 1 1 2) = none ∧
      (none : Option (Byte × Byte)) ≠ ckParse (reg3 0 0 0) ∧
      (none : Option (Byte × Byte)) ≠ ckParse (reg3 1 1 2) := by
  refine ⟨by decide, by decide, fun t => ?_, ?_, by decide, by decide⟩
  · by_cases ht : t = 0
    · left; simp [ht]
    · right; simp [ht]
  · rw [(copyParse_exec_eq_diagonal_and_rvalid ckParse).1]
    decide

/-- Non-vacuity of `copyParse_ckParse_twoValidStates`: the passing states `(0,0,0)` and `(1,1,2)`,
a writer that shows the first until time `2` and the second afterwards, and a checksum-passing
result. -/
theorem copyParse_ckParse_twoValidStates_nonvacuous :
    (reg3 0 0 0) 2 = (reg3 0 0 0) 0 + (reg3 0 0 0) 1 ∧
      (reg3 1 1 2) 2 = (reg3 1 1 2) 0 + (reg3 1 1 2) 1 ∧
      (∀ t, (fun t => if t < 3 then reg3 0 0 0 else reg3 1 1 2 : Adversary 3) t = reg3 0 0 0 ∨
        (fun t => if t < 3 then reg3 0 0 0 else reg3 1 1 2 : Adversary 3) t = reg3 1 1 2) ∧
      (copyParse ckParse).exec (fun t => if t < 3 then reg3 0 0 0 else reg3 1 1 2) ≠ none := by
  refine ⟨by decide, by decide, fun t => ?_, ?_⟩
  · by_cases ht : t < 3
    · left; simp [ht]
    · right; simp [ht]
  · rw [(copyParse_exec_eq_diagonal_and_rvalid ckParse).1]
    decide

section Impossibility

variable {n : Nat} {α : Type}

/-- Torn-value impossibility: if the spec has a region state none of whose bytes determines the
output (`HasUndeterminedState spec`), then no parser built from one-byte reads alone (no atomic
snapshot) is R-state for that spec. The parser need not implement the spec. -/
theorem not_rstate_of_noSnap_of_hasUndeterminedState (spec : Region n → α)
    (hspec : HasUndeterminedState spec) (p : Prog n α) (hp : p.NoSnap) : ¬ RState spec p := by
  classical
  obtain ⟨s0, hglob, hcoord⟩ := hspec
  intro hR
  let r : α := p.eval s0
  let adv : Adversary n := fun t =>
    match p.addrAt s0 t with
    | some i => Classical.choose (hcoord i r)
    | none => Classical.choose (hglob r)
  have hexec : p.exec adv = r := by
    apply Prog.execFrom_eq_eval_of_agree p s0 adv 0 hp
    intro m i hm
    simp only [Nat.zero_add, adv, hm]
    exact (Classical.choose_spec (hcoord i r)).1
  obtain ⟨t, ht⟩ := hR adv
  rw [hexec] at ht
  have hne : spec (adv t) ≠ r := by
    simp only [adv]
    cases p.addrAt s0 t with
    | some i => exact (Classical.choose_spec (hcoord i r)).2
    | none => exact Classical.choose_spec (hglob r)
  exact hne ht.symm

private def FixesByte (spec : Region n → α) (i : Fin n) (b : Byte) : Prop :=
  ∃ r : α, ∀ σ : Region n, σ i = b → spec σ = r

private noncomputable def buildRStateProg (spec : Region n → α)
    (hdet : ∀ s : Region n, ∃ i : Fin n, FixesByte spec i (s i)) :
    (l : List (Fin n)) → (acc : Region n) →
    (∀ j : Fin n, j ∉ l → ¬ FixesByte spec j (acc j)) → Prog n α
  | [], acc, hacc =>
    False.elim (by
      obtain ⟨i, hi⟩ := hdet acc
      exact hacc i (by simp) hi)
  | i :: rest, acc, hacc =>
    .read i fun b =>
      open Classical in
      if hb : FixesByte spec i b then
        .ret (Classical.choose hb)
      else
        buildRStateProg spec hdet rest (fun j => if j = i then b else acc j) (by
          intro j hj
          by_cases hji : j = i
          · subst hji; simpa using hb
          · simp only [hji, ite_false]
            exact hacc j (by simp [List.mem_cons, hji, hj]))

private theorem buildRStateProg_noSnap (spec : Region n → α)
    (hdet : ∀ s : Region n, ∃ i : Fin n, FixesByte spec i (s i))
    (l : List (Fin n)) (acc : Region n)
    (hacc : ∀ j : Fin n, j ∉ l → ¬ FixesByte spec j (acc j)) :
    (buildRStateProg spec hdet l acc hacc).NoSnap := by
  induction l generalizing acc with
  | nil =>
    exfalso
    obtain ⟨i, hi⟩ := hdet acc
    exact hacc i (by simp) hi
  | cons i rest ih =>
    intro b
    dsimp only
    split
    · trivial
    · exact ih _ _

private theorem buildRStateProg_rstateFrom (spec : Region n → α)
    (hdet : ∀ s : Region n, ∃ i : Fin n, FixesByte spec i (s i))
    (l : List (Fin n)) (acc : Region n)
    (hacc : ∀ j : Fin n, j ∉ l → ¬ FixesByte spec j (acc j))
    (adv : Adversary n) (t : Nat) :
    ∃ t' : Nat, (buildRStateProg spec hdet l acc hacc).execFrom adv t = spec (adv t') := by
  induction l generalizing acc t with
  | nil =>
    exfalso
    obtain ⟨i, hi⟩ := hdet acc
    exact hacc i (by simp) hi
  | cons i rest ih =>
    simp only [buildRStateProg, Prog.execFrom]
    split
    · rename_i hb
      exact ⟨t, (Classical.choose_spec hb (adv t) rfl).symm⟩
    · exact ih _ _ (t + 1)

/-- Exact characterization of the torn-value impossibility: for every region size `n` (including
`0` and `1`) and every spec, no snapshot-free parser is R-state for `spec` iff `spec` has a region
state none of whose bytes determines the output. When no such state exists, some snapshot-free
parser (reading bytes one at a time until one byte determines the output) is R-state. -/
theorem hasUndeterminedState_iff_no_noSnap_rstate (spec : Region n → α) :
    HasUndeterminedState spec ↔ ∀ p : Prog n α, p.NoSnap → ¬ RState spec p := by
  classical
  constructor
  · intro h p hp
    exact not_rstate_of_noSnap_of_hasUndeterminedState spec h p hp
  · intro hno
    exact Classical.byContradiction fun hnot => by
      by_cases hconst : ∃ r : α, ∀ σ : Region n, spec σ = r
      · obtain ⟨r, hr⟩ := hconst
        exact hno (Prog.ret r) trivial (fun adv => ⟨0, (hr (adv 0)).symm⟩)
      · have hglob : ∀ r : α, ∃ σ : Region n, spec σ ≠ r := fun r =>
          Classical.byContradiction fun h =>
            hconst ⟨r, fun σ => Classical.byContradiction fun hne => h ⟨σ, hne⟩⟩
        have hdet : ∀ s : Region n, ∃ i : Fin n, FixesByte spec i (s i) := fun s =>
          Classical.byContradiction fun h =>
            hnot ⟨s, hglob, fun i r =>
              Classical.byContradiction fun hall =>
                h ⟨i, r, fun σ hσ => Classical.byContradiction fun hne => hall ⟨σ, hσ, hne⟩⟩⟩
        let p := buildRStateProg spec hdet (List.finRange n) (fun _ => 0)
          (fun j hj => False.elim (hj (List.mem_finRange j)))
        exact hno p (buildRStateProg_noSnap _ _ _ _ _)
          (fun adv => buildRStateProg_rstateFrom _ _ _ _ _ adv 0)

/-- On a nonempty region, "no single byte value determines the output" implies
`HasUndeterminedState`. -/
theorem hasUndeterminedState_of_pos_of_noByteDeterminesOutput (hn : 0 < n) (spec : Region n → α)
    (hspec : NoByteDeterminesOutput spec) : HasUndeterminedState spec := by
  refine ⟨fun _ => 0, fun r => ?_, fun i r => hspec i 0 r⟩
  obtain ⟨σ, _, hne⟩ := hspec ⟨0, hn⟩ 0 r
  exact ⟨σ, hne⟩

end Impossibility

/-- Degenerate edge `n = 0`: no spec on the empty region has an undetermined state. -/
theorem not_hasUndeterminedState_of_region_zero {α : Type} (spec : Region 0 → α) :
    ¬ HasUndeterminedState spec := by
  rintro ⟨s0, hglob, _⟩
  obtain ⟨σ, hσ⟩ := hglob (spec s0)
  exact hσ (congrArg spec (funext fun j => j.elim0))

/-- Degenerate edge `n = 1`: no spec on a one-byte region has an undetermined state. -/
theorem not_hasUndeterminedState_of_region_one {α : Type} (spec : Region 1 → α) :
    ¬ HasUndeterminedState spec := by
  rintro ⟨s0, _, hcoord⟩
  obtain ⟨σ, hσ, hne⟩ := hcoord 0 (spec s0)
  apply hne
  congr 1
  funext j
  rw [Subsingleton.elim j 0]
  exact hσ

/-- The pair spec satisfies the hypothesis "no single byte value determines the output". -/
theorem pairSpec_noByteDeterminesOutput : NoByteDeterminesOutput pairSpec := by
  intro i v r
  match i with
  | ⟨0, _⟩ =>
    refine ⟨reg2 v (r.2 + 1), rfl, fun h => ?_⟩
    have := congrArg Prod.snd h
    exact byte_add_one_ne r.2 this
  | ⟨1, _⟩ =>
    refine ⟨reg2 (r.1 + 1) v, rfl, fun h => ?_⟩
    have := congrArg Prod.fst h
    exact byte_add_one_ne r.1 this

/-- The checksum spec satisfies the hypothesis "no single byte value determines the output". -/
theorem ckParse_noByteDeterminesOutput : NoByteDeterminesOutput ckParse := by
  intro i v r
  have hv : ∃ σ : Region 3, σ i = v ∧ ckParse σ ≠ none := by
    match i with
    | ⟨0, _⟩ => exact ⟨reg3 v 0 v, rfl, by simp [ckParse, reg3]⟩
    | ⟨1, _⟩ => exact ⟨reg3 0 v v, rfl, by simp [ckParse, reg3]⟩
    | ⟨2, _⟩ => exact ⟨reg3 0 v v, rfl, by simp [ckParse, reg3]⟩
  have hi : ∃ σ : Region 3, σ i = v ∧ ckParse σ = none := by
    match i with
    | ⟨0, _⟩ => exact ⟨reg3 v 0 (v + 1), rfl, by simp [ckParse, reg3, byte_add_one_ne]⟩
    | ⟨1, _⟩ => exact ⟨reg3 0 v (v + 1), rfl, by simp [ckParse, reg3, byte_add_one_ne]⟩
    | ⟨2, _⟩ => exact ⟨reg3 0 (v + 1) v, rfl, by
        simp only [ckParse, reg3]; simp [Ne.symm (byte_add_one_ne v)]⟩
  cases r with
  | none => obtain ⟨σ, h1, h2⟩ := hv; exact ⟨σ, h1, h2⟩
  | some x => obtain ⟨σ, h1, h2⟩ := hi; exact ⟨σ, h1, by rw [h2]; simp⟩

/-- The pair spec has an undetermined state. -/
theorem pairSpec_hasUndeterminedState : HasUndeterminedState pairSpec :=
  hasUndeterminedState_of_pos_of_noByteDeterminesOutput (by decide) pairSpec
    pairSpec_noByteDeterminesOutput

/-- The checksum spec has an undetermined state. -/
theorem ckParse_hasUndeterminedState : HasUndeterminedState ckParse :=
  hasUndeterminedState_of_pos_of_noByteDeterminesOutput (by decide) ckParse
    ckParse_noByteDeterminesOutput

/-- The seqlock spec has an undetermined state (the even-version state `(0,0,0)`), although an odd
version byte alone determines the output `none`. -/
theorem seqSpec_hasUndeterminedState : HasUndeterminedState seqSpec := by
  refine ⟨reg3 0 0 0, fun r => ?_, fun i r => ?_⟩
  · cases r with
    | none => exact ⟨reg3 0 0 0, by decide⟩
    | some _ => exact ⟨reg3 1 0 0, by simp [seqSpec, reg3]⟩
  · match i with
    | ⟨0, _⟩ =>
      cases r with
      | none => exact ⟨reg3 0 0 0, rfl, by decide⟩
      | some p =>
        refine ⟨reg3 0 (p.1 + 1) 0, rfl, fun h => ?_⟩
        have h' : (p.1 + 1, (0 : Byte)) = p := by
          simpa [seqSpec, reg3] using h
        have hf : p.1 + 1 = p.1 := congrArg Prod.fst h'
        exact byte_add_one_ne p.1 hf
    | ⟨1, _⟩ =>
      cases r with
      | none => exact ⟨reg3 0 0 0, rfl, by decide⟩
      | some _ => exact ⟨reg3 1 0 0, rfl, by simp [seqSpec, reg3]⟩
    | ⟨2, _⟩ =>
      cases r with
      | none => exact ⟨reg3 0 0 0, rfl, by decide⟩
      | some _ => exact ⟨reg3 1 0 0, rfl, by simp [seqSpec, reg3]⟩

/-- Two-byte boolean AND has an undetermined state (`(1,1)`), although the byte value `0` at
either address alone determines the output `false`. -/
theorem andSpec_hasUndeterminedState : HasUndeterminedState andSpec := by
  refine ⟨reg2 1 1, fun r => ?_, fun i r => ?_⟩
  · cases r
    · exact ⟨reg2 1 1, by decide⟩
    · exact ⟨reg2 0 0, by decide⟩
  · match i with
    | ⟨0, _⟩ =>
      cases r
      · exact ⟨reg2 1 1, rfl, by decide⟩
      · exact ⟨reg2 1 0, rfl, by decide⟩
    | ⟨1, _⟩ =>
      cases r
      · exact ⟨reg2 1 1, rfl, by decide⟩
      · exact ⟨reg2 0 1, rfl, by decide⟩

/-- The tagged-value spec has an undetermined state (`(1, 0)`), for every number `k` of decodes,
although an invalid tag byte alone determines the output `none`. -/
theorem viewSpec_hasUndeterminedState (k : Nat) : HasUndeterminedState (viewSpec k) := by
  refine ⟨reg2 1 0, fun r => ?_, fun i r => ?_⟩
  · cases r with
    | none => exact ⟨reg2 0 0, by simp [viewSpec, ValidE, reg2]⟩
    | some _ => exact ⟨reg2 2 0, by simp [viewSpec, ValidE, reg2]⟩
  · match i with
    | ⟨0, _⟩ =>
      cases r with
      | none => exact ⟨reg2 1 0, rfl, by simp [viewSpec, ValidE, reg2]⟩
      | some _ => exact ⟨reg2 1 2, rfl, by simp [viewSpec, ValidE, reg2]⟩
    | ⟨1, _⟩ =>
      cases r with
      | none => exact ⟨reg2 0 0, rfl, by simp [viewSpec, ValidE, reg2]⟩
      | some _ => exact ⟨reg2 2 0, rfl, by simp [viewSpec, ValidE, reg2]⟩

/-- Tightness of "no snapshot": the snapshot parser of the pair spec satisfies every other
hypothesis of the impossibility and is R-state. -/
theorem snapParse_pair_rstate_counterexample :
    HasUndeterminedState pairSpec ∧ ¬ (snapParse pairSpec).NoSnap ∧
      RState pairSpec (snapParse pairSpec) :=
  ⟨pairSpec_hasUndeterminedState, fun h => h, (snapParse_exec_eq_and_rstate pairSpec).2⟩

/-- The spec that returns byte `0` of a two-byte region. -/
def fstSpec (s : Region 2) : Byte := s 0

/-- Read byte `0` and return it. -/
def readFst : Prog 2 Byte := .read 0 .ret

/-- Tightness of the spec hypothesis: for a spec determined by one byte, a snapshot-free parser
satisfies every other hypothesis of the impossibility and is R-state. -/
theorem readFst_rstate_counterexample :
    ¬ HasUndeterminedState fstSpec ∧ readFst.NoSnap ∧ RState fstSpec readFst := by
  refine ⟨?_, fun _ => trivial, fun adv => ⟨0, rfl⟩⟩
  rintro ⟨s0, _, hcoord⟩
  obtain ⟨σ, h1, h2⟩ := hcoord 0 (s0 0)
  exact h2 h1

theorem readSeq_noSnap {n : Nat} {α : Type} (l : List (Fin n)) (acc : Region n)
    (k : Region n → Prog n α) (hk : ∀ acc', (k acc').NoSnap) : (readSeq l acc k).NoSnap := by
  induction l generalizing acc with
  | nil => exact hk acc
  | cons i is ih => exact fun _ => ih _

/-- Non-vacuity of the torn-value impossibility: the pair spec has an undetermined state, and the
byte-by-byte copy parser is snapshot-free. -/
theorem torn_impossibility_nonvacuous :
    HasUndeterminedState pairSpec ∧ (copyParse pairSpec).NoSnap :=
  ⟨pairSpec_hasUndeterminedState, readSeq_noSnap _ _ _ fun _ => trivial⟩

/-! ## 7. Seqlock-style version check -/

theorem seqlockReader_exec (adv : Adversary 3) :
    seqlockReader.exec adv =
      if (adv 0 0).val % 2 = 0 then
        (if adv 3 0 = adv 0 0 then some (adv 1 1, adv 2 2) else none)
      else none := by
  simp only [seqlockReader, Prog.exec, Prog.execFrom]
  split <;> rfl

/-- The seqlock reader implements `seqSpec` in private memory. -/
theorem seqlock_implements : Implements seqlockReader seqSpec := by
  intro s
  rw [← Prog.exec_const, seqlockReader_exec]
  simp only [Adversary.const, seqSpec]
  split <;> simp

/-- The seqlock reader uses one-byte reads and no snapshot. -/
theorem seqlockReader_noSnap : seqlockReader.NoSnap := by
  intro v1
  dsimp only
  split
  · exact fun _ _ _ => trivial
  · trivial

theorem versionStep_val (s s' : Region 3) (h : VersionStep s s') :
    (s' 0).val = (s 0).val ∨ (s' 0).val = ((s 0).val + 1) % 256 := by
  rcases h with h | ⟨_, h, _, _⟩ | ⟨_, h⟩ | ⟨_, h, _, _⟩
  · left; rw [h]
  · right; rw [h, Fin.val_add]; rfl
  · left; rw [h]
  · right; rw [h, Fin.val_add]; rfl

theorem versionStep_eq_of_even_of_same (s s' : Region 3) (h : VersionStep s s')
    (he : (s 0).val % 2 = 0) (hv : (s' 0).val = (s 0).val) : s' = s := by
  have := (s 0).isLt
  rcases h with h | ⟨_, h, _, _⟩ | ⟨ho, _⟩ | ⟨ho, _, _, _⟩
  · exact h
  · rw [h, Fin.val_add] at hv
    simp at hv
    omega
  · omega
  · omega

/-- Seqlock positive control: against every writer that follows the version protocol and takes at
most one protocol step between consecutive reader accesses, the seqlock reader returns
`seqSpec (adv t)` for some time `t ≤ 3` (inside its access window). -/
theorem seqlock_rstate_of_oneStepVersionWriter (adv : Adversary 3)
    (hW : OneStepVersionWriter adv) :
    ∃ t : Nat, t ≤ 3 ∧ seqlockReader.exec adv = seqSpec (adv t) := by
  rw [seqlockReader_exec]
  have A0 := versionStep_val (adv 0) (adv 1) (hW 0)
  have A1 := versionStep_val (adv 1) (adv 2) (hW 1)
  have A2 := versionStep_val (adv 2) (adv 3) (hW 2)
  have b0 := (adv 0 0).isLt
  have b1 := (adv 1 0).isLt
  have b2 := (adv 2 0).isLt
  have b3 := (adv 3 0).isLt
  have hneq : ∀ a b : Byte, a.val ≠ b.val → a ≠ b := fun a b h e => h (congrArg Fin.val e)
  by_cases h0 : (adv 0 0).val % 2 = 0
  · rw [ite_eq_left h0]
    by_cases h01 : (adv 1 0).val = (adv 0 0).val
    · have e1 : adv 1 = adv 0 := versionStep_eq_of_even_of_same (adv 0) (adv 1) (hW 0) h0 h01
      by_cases h12 : (adv 2 0).val = (adv 1 0).val
      · have e2 : adv 2 = adv 1 :=
          versionStep_eq_of_even_of_same (adv 1) (adv 2) (hW 1) (by omega) h12
        by_cases h23 : (adv 3 0).val = (adv 2 0).val
        · refine ⟨0, by omega, ?_⟩
          have e30 : adv 3 0 = adv 0 0 := Fin.ext (by omega)
          rw [ite_eq_left e30, e2, e1]
          simp [seqSpec, h0]
        · refine ⟨3, by omega, ?_⟩
          rw [ite_eq_right (hneq _ _ (by omega))]
          simp only [seqSpec]
          rw [ite_eq_right (by omega)]
      · refine ⟨2, by omega, ?_⟩
        rw [ite_eq_right (hneq _ _ (by omega))]
        simp only [seqSpec]
        rw [ite_eq_right (by omega)]
    · refine ⟨1, by omega, ?_⟩
      rw [ite_eq_right (hneq _ _ (by omega))]
      simp only [seqSpec]
      rw [ite_eq_right (by omega)]
  · refine ⟨0, by omega, ?_⟩
    rw [ite_eq_right h0]
    simp only [seqSpec]
    rw [ite_eq_right h0]

/-- The same result in `RStateUnder` form. -/
theorem seqlock_rstateUnder_oneStepVersionWriter :
    RStateUnder OneStepVersionWriter seqSpec seqlockReader := fun adv hW => by
  obtain ⟨t, _, ht⟩ := seqlock_rstate_of_oneStepVersionWriter adv hW
  exact ⟨t, ht⟩

/-- Positive control for the torn-value impossibility: the seqlock spec has an undetermined state
and the seqlock reader is snapshot-free, yet against every one-step protocol writer the reader is
R-state; the writer constraint is the one change. -/
theorem seqlock_positive_control :
    HasUndeterminedState seqSpec ∧ seqlockReader.NoSnap ∧
      RStateUnder OneStepVersionWriter seqSpec seqlockReader :=
  ⟨seqSpec_hasUndeterminedState, seqlockReader_noSnap, seqlock_rstateUnder_oneStepVersionWriter⟩

/-- Without the protocol: `seqRogueAdv` (data changes while the version stays `0`) is not a
one-step protocol writer, and the seqlock reader returns `some (1, 2)` against it, which is
`seqSpec` of no state the writer produced. -/
theorem seqlock_not_rstate_rogueWriter :
    ¬ OneStepVersionWriter seqRogueAdv ∧ seqlockReader.exec seqRogueAdv = some (1, 2) ∧
      (∀ t : Nat, seqlockReader.exec seqRogueAdv ≠ seqSpec (seqRogueAdv t)) ∧
      ¬ RState seqSpec seqlockReader := by
  have h1 : seqlockReader.exec seqRogueAdv = some (1, 2) := by
    rw [seqlockReader_exec]; decide
  have h2 : ∀ t : Nat, seqlockReader.exec seqRogueAdv ≠ seqSpec (seqRogueAdv t) := by
    intro t h
    rw [h1] at h
    simp only [seqSpec, seqRogueAdv, reg3] at h
    simp at h
    have e := h.1.trans h.2.symm
    simp at e
  have hn : ¬ OneStepVersionWriter seqRogueAdv := by
    intro h
    have e := versionStep_eq_of_even_of_same _ _ (h 0) (by decide) (by decide)
    have := congrFun e 1
    revert this
    decide
  exact ⟨hn, h1, h2, fun hR => by obtain ⟨t, ht⟩ := hR seqRogueAdv; exact h2 t ht⟩

/-- Two protocol steps between accesses already break R-state, with no wraparound and no data
change: `seqTwoStepAdv` (version `0` to `2` between the first two accesses) is a two-step but not a
one-step protocol writer, and the reader returns the error result, which is `seqSpec` of no state
the writer produced. -/
theorem seqlock_not_rstateUnder_twoStepVersionWriter :
    TwoStepVersionWriter seqTwoStepAdv ∧ ¬ OneStepVersionWriter seqTwoStepAdv ∧
      seqlockReader.exec seqTwoStepAdv = none ∧
      (∀ t : Nat, seqlockReader.exec seqTwoStepAdv ≠ seqSpec (seqTwoStepAdv t)) ∧
      ¬ RStateUnder TwoStepVersionWriter seqSpec seqlockReader := by
  have hW : TwoStepVersionWriter seqTwoStepAdv := by
    intro t
    by_cases ht : t = 0
    · subst ht
      refine ⟨reg3 1 0 0, ?_, ?_⟩
      · exact Or.inr (Or.inl ⟨by decide, by decide, by decide, by decide⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨by decide, by decide, by decide, by decide⟩))
    · refine ⟨reg3 2 0 0, ?_, ?_⟩
      · left; simp [seqTwoStepAdv, ht]
      · left; simp [seqTwoStepAdv]
  have hn : ¬ OneStepVersionWriter seqTwoStepAdv := by
    intro h
    have := versionStep_val _ _ (h 0)
    revert this
    decide
  have h1 : seqlockReader.exec seqTwoStepAdv = none := by rw [seqlockReader_exec]; decide
  have h2 : ∀ t : Nat, seqlockReader.exec seqTwoStepAdv ≠ seqSpec (seqTwoStepAdv t) := by
    intro t
    rw [h1]
    by_cases ht : t = 0
    · subst ht; decide
    · simp only [seqTwoStepAdv, ht, ite_false]; decide
  exact ⟨hW, hn, h1, h2, fun hR => by obtain ⟨t, ht⟩ := hR seqTwoStepAdv hW; exact h2 t ht⟩

theorem VersionPath.trans {c d : Nat} {s s' s'' : Region 3} (h1 : VersionPath c s s')
    (h2 : VersionPath d s' s'') : VersionPath (c + d) s s'' := by
  induction h1 with
  | refl _ => simpa using h2
  | stay hs he _ ih => exact VersionPath.stay hs he (ih h2)
  | bump hs he _ ih =>
    rw [Nat.add_right_comm]
    exact VersionPath.bump hs he (ih h2)

/-- Along a protocol path with `c` increments, the version advances by `c` modulo 256. -/
theorem versionPath_val {c : Nat} {s s' : Region 3} (h : VersionPath c s s') :
    (s' 0).val = ((s 0).val + c) % 256 := by
  induction h with
  | refl s => have := (s 0).isLt; omega
  | stay _ he _ ih => rw [ih, he]
  | bump _ he _ ih =>
    rw [ih, he, Fin.val_add]
    simp only [Fin.val_one]
    omega

/-- A protocol path with no increment that starts at an even version changes nothing. -/
theorem versionPath_zero_eq {c : Nat} {s s' : Region 3} (h : VersionPath c s s') (hc : c = 0)
    (he : (s 0).val % 2 = 0) : s' = s := by
  revert hc he
  induction h with
  | refl _ => intro _ _; rfl
  | stay hs heq _ ih =>
    intro hc he
    have e := versionStep_eq_of_even_of_same _ _ hs he (by rw [heq])
    subst e
    exact ih hc he
  | bump _ _ _ _ => intro hc; omega

/-- `incr k v` adds one to the version `v`, `k` times (modulo 256). -/
def incr : Nat → Byte → Byte
  | 0, v => v
  | k + 1, v => incr k (v + 1)

theorem incr_val (k : Nat) (v : Byte) : (incr k v).val = (v.val + k) % 256 := by
  induction k generalizing v with
  | zero => simp [incr, Nat.mod_eq_of_lt v.isLt]
  | succ k ih =>
    simp only [incr]
    rw [ih, Fin.val_add]
    simp
    omega

/-- `k` protocol steps, each incrementing the version, keep the data. -/
theorem versionPath_incr (k : Nat) (v a b : Byte) :
    VersionPath k (reg3 v a b) (reg3 (incr k v) a b) := by
  induction k generalizing v with
  | zero => exact VersionPath.refl _
  | succ k ih =>
    refine VersionPath.bump (s' := reg3 (v + 1) a b) ?_ rfl (ih (v + 1))
    by_cases hv : v.val % 2 = 0
    · exact Or.inr (Or.inl ⟨hv, rfl, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨by simp [reg3]; omega, rfl, rfl, rfl⟩))

theorem reg3_eta (s : Region 3) : reg3 (s 0) (s 1) (s 2) = s := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

/-- Without a bound on increments the protocol constrains nothing: with a version byte that wraps
modulo 256, any region state reaches any other by a protocol path (begin a write if needed, set the
data, then increment the version until it matches). -/
theorem versionPath_any (s s' : Region 3) : ∃ c : Nat, VersionPath c s s' := by
  have hodd : ∃ v : Byte, ∃ c : Nat, v.val % 2 = 1 ∧ VersionPath c s (reg3 v (s 1) (s 2)) := by
    by_cases h : (s 0).val % 2 = 0
    · refine ⟨s 0 + 1, 1, ?_, ?_⟩
      · rw [Fin.val_add]; have := (s 0).isLt; simp; omega
      · exact VersionPath.bump (s' := reg3 (s 0 + 1) (s 1) (s 2))
          (Or.inr (Or.inl ⟨h, rfl, rfl, rfl⟩)) rfl (VersionPath.refl _)
    · refine ⟨s 0, 0, by omega, ?_⟩
      rw [reg3_eta]
      exact VersionPath.refl _
  obtain ⟨v, c, hv, h1⟩ := hodd
  have h2 : VersionPath 0 (reg3 v (s 1) (s 2)) (reg3 v (s' 1) (s' 2)) :=
    VersionPath.stay (s' := reg3 v (s' 1) (s' 2)) (Or.inr (Or.inr (Or.inl ⟨hv, rfl⟩))) rfl
      (VersionPath.refl _)
  have h3 := versionPath_incr ((s' 0).val + 256 - v.val) v (s' 1) (s' 2)
  have e : incr ((s' 0).val + 256 - v.val) v = s' 0 := Fin.ext (by
    rw [incr_val]; have := v.isLt; have := (s' 0).isLt; omega)
  rw [e, reg3_eta] at h3
  exact ⟨_, h1.trans (h2.trans h3)⟩

/-- Accepted results are consistent under fewer than 256 version increments: against every
protocol writer that increments the version fewer than 256 times from time `0` to time `3` (with
any number of protocol steps between accesses), every accepted result `some d` of the seqlock
reader is `seqSpec` of the state at time `0`. -/
theorem seqlock_accepted_eq_seqSpec_adv0_of_incrementBound (adv : Adversary 3)
    (hW : IncrementBoundedWriter 256 adv) (d : Byte × Byte)
    (hacc : seqlockReader.exec adv = some d) : seqSpec (adv 0) = some d := by
  obtain ⟨c0, c1, c2, p0, p1, p2, hlt⟩ := hW
  rw [seqlockReader_exec] at hacc
  split at hacc
  · rename_i h0
    split at hacc
    · rename_i h30
      have v1 := versionPath_val p0
      have v2 := versionPath_val p1
      have v3 := versionPath_val p2
      have hv : (adv 3 0).val = (adv 0 0).val := congrArg Fin.val h30
      have b0 := (adv 0 0).isLt
      have hz : c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by omega
      obtain ⟨rfl, rfl, rfl⟩ := hz
      have e1 : adv 1 = adv 0 := versionPath_zero_eq p0 rfl h0
      have e2 : adv 2 = adv 1 := versionPath_zero_eq p1 rfl (by rw [e1]; exact h0)
      rw [e2, e1] at hacc
      simpa [seqSpec, h0] using hacc
    · simp at hacc
  · simp at hacc

/-- Tightness of the bound 256: `seqWrapAdv` takes 256 version increments between the reader's read
of the first data byte (time `1`) and of the second (time `2`), so it is bounded by 257 but not by
256. The reader accepts the torn pair `some (0, 1)`: the first data byte of the old state and the
second of the new one. It is not `seqSpec` of the state at time `0`, nor of the state at any
time. -/
theorem seqlock_accepted_torn_of_256Increments :
    IncrementBoundedWriter 257 seqWrapAdv ∧ ¬ IncrementBoundedWriter 256 seqWrapAdv ∧
      seqlockReader.exec seqWrapAdv = some (0, 1) ∧ seqSpec (seqWrapAdv 0) ≠ some (0, 1) ∧
      ∀ t : Nat, seqSpec (seqWrapAdv t) ≠ some (0, 1) := by
  have hex : seqlockReader.exec seqWrapAdv = some (0, 1) := by rw [seqlockReader_exec]; decide
  have hall : ∀ t : Nat, seqSpec (seqWrapAdv t) ≠ some (0, 1) := by
    intro t
    by_cases ht : t < 2
    · simp only [seqWrapAdv, ht, ite_true]; decide
    · simp only [seqWrapAdv, ht, ite_false]; decide
  have hne : seqSpec (seqWrapAdv 0) ≠ some (0, 1) := hall 0
  have p1 : VersionPath 256 (seqWrapAdv 1) (seqWrapAdv 2) := by
    have a : VersionPath 1 (reg3 0 0 0) (reg3 1 0 0) :=
      VersionPath.bump (s' := reg3 1 0 0) (Or.inr (Or.inl ⟨by decide, rfl, rfl, rfl⟩)) rfl
        (VersionPath.refl _)
    have b : VersionPath 0 (reg3 1 0 0) (reg3 1 1 1) :=
      VersionPath.stay (s' := reg3 1 1 1) (Or.inr (Or.inr (Or.inl ⟨by decide, rfl⟩))) rfl
        (VersionPath.refl _)
    have c := versionPath_incr 255 1 1 1
    have e : incr 255 (1 : Byte) = 0 := by decide +kernel
    rw [e] at c
    have := a.trans (b.trans c)
    simpa [seqWrapAdv] using this
  have hW : IncrementBoundedWriter 257 seqWrapAdv := by
    refine ⟨0, 256, 0, ?_, p1, ?_, by decide⟩
    · simp only [seqWrapAdv]; exact VersionPath.refl _
    · simp only [seqWrapAdv]; exact VersionPath.refl _
  exact ⟨hW, fun h => hne (seqlock_accepted_eq_seqSpec_adv0_of_incrementBound _ h _ hex), hex, hne,
    hall⟩

/-- Tightness of "the result is accepted" in
`seqlock_accepted_eq_seqSpec_adv0_of_incrementBound`: the writer that never writes and shows the
odd version `1` is increment-bounded, the reader does not return `some (0, 0)`, and `seqSpec` of
its state is not `some (0, 0)`. -/
theorem seqlock_accepted_hacc_counterexample :
    IncrementBoundedWriter 256 (Adversary.const (reg3 1 0 0)) ∧
      seqlockReader.exec (Adversary.const (reg3 1 0 0)) ≠ some (0, 0) ∧
      seqSpec (Adversary.const (reg3 1 0 0) 0) ≠ some (0, 0) :=
  ⟨⟨0, 0, 0, VersionPath.refl _, VersionPath.refl _, VersionPath.refl _, by decide⟩,
    by rw [seqlockReader_exec]; decide, by decide⟩

/-- A one-step protocol writer that performs a whole write: `(0,0,0)`, then `(1,0,0)` (begin),
then `(1,5,5)` (data), then `(2,5,5)` (end) from time `3` on. -/
def seqSlowAdv : Adversary 3 := fun t =>
  if t = 0 then reg3 0 0 0 else if t = 1 then reg3 1 0 0 else if t = 2 then reg3 1 5 5
  else reg3 2 5 5

/-- Non-vacuity of the seqlock positive control: `seqSlowAdv` is a one-step protocol writer that
writes during the read; the reader returns the error result, which is `seqSpec` of the state at
time `1` (a write in progress). -/
theorem seqlock_oneStep_nonvacuous :
    OneStepVersionWriter seqSlowAdv ∧ seqlockReader.exec seqSlowAdv = none ∧
      seqSpec (seqSlowAdv 1) = none := by
  refine ⟨fun t => ?_, by rw [seqlockReader_exec]; decide, by decide⟩
  match t with
  | 0 => exact Or.inr (Or.inl ⟨by decide, by decide, by decide, by decide⟩)
  | 1 => exact Or.inr (Or.inr (Or.inl ⟨by decide, by decide⟩))
  | 2 => exact Or.inr (Or.inr (Or.inr ⟨by decide, by decide, by decide, by decide⟩))
  | t + 3 =>
    left
    simp only [seqSlowAdv]
    simp

/-- Non-vacuity of the increment-bounded result: the writer that never writes is bounded by `256`
(indeed by `1`), and the reader accepts `some (5, 5)` against it. -/
theorem seqlock_incrementBound_nonvacuous :
    IncrementBoundedWriter 256 (Adversary.const (reg3 0 5 5)) ∧
      seqlockReader.exec (Adversary.const (reg3 0 5 5)) = some (5, 5) :=
  ⟨⟨0, 0, 0, VersionPath.refl _, VersionPath.refl _, VersionPath.refl _, by decide⟩,
    by rw [seqlockReader_exec]; decide⟩

/-! ## 8. Compiler-introduced double fetch: read rematerialization -/

section Remat

variable {n : Nat} {α : Type}

/-- Read rematerialization is a refinement in the private-memory semantics: for every
check-then-use fragment, the rematerialized program returns the same result as the original on
every region nobody else writes. -/
theorem remat_privRefines_compile (c : CheckUse n α) : PrivRefines c.remat c.compile := by
  intro s
  simp only [CheckUse.remat, CheckUse.compile, Prog.eval]
  split <;> rfl

/-- Which rematerializations are robust, for a fragment whose use and failure branch perform no
further reads: the rematerialized fragment robustly refines the original iff, whenever the check
accepts some byte, every use value `u b'` (for every byte `b'`, including bytes the check rejects)
is a result of the original: `u b` for an accepted `b`, or the failure value `e` when some byte is
rejected. -/
theorem remat_pure_robustRefines_iff (a : Fin n) (check : Byte → Bool) (u : Byte → α) (e : α) :
    RobustRefines (CheckUse.pure a check u e).remat (CheckUse.pure a check u e).compile ↔
      ((∃ b, check b = true) →
        ∀ b', ∃ b, (check b = true ∧ u b = u b') ∨ (check b = false ∧ e = u b')) := by
  constructor
  · rintro h ⟨b0, hb0⟩ b'
    let adv : Adversary n := fun t => if t = 0 then (fun _ => b0) else (fun _ => b')
    obtain ⟨adv', h'⟩ := h adv
    have hq : (CheckUse.pure a check u e).remat.exec adv = u b' := by
      simp [CheckUse.remat, CheckUse.pure, Prog.exec, Prog.execFrom, adv, hb0]
    rw [hq] at h'
    refine ⟨adv' 0 a, ?_⟩
    by_cases hc : check (adv' 0 a) = true
    · left
      refine ⟨hc, ?_⟩
      simp [CheckUse.compile, CheckUse.pure, Prog.exec, Prog.execFrom, hc] at h'
      exact h'.symm
    · right
      have hc' : check (adv' 0 a) = false := by simpa using hc
      refine ⟨hc', ?_⟩
      simp [CheckUse.compile, CheckUse.pure, Prog.exec, Prog.execFrom, hc'] at h'
      exact h'.symm
  · intro h adv
    by_cases hc : check (adv 0 a) = true
    · obtain ⟨b, hb⟩ := h ⟨_, hc⟩ (adv 1 a)
      refine ⟨Adversary.const (fun _ => b), ?_⟩
      have hq : (CheckUse.pure a check u e).remat.exec adv = u (adv 1 a) := by
        simp [CheckUse.remat, CheckUse.pure, Prog.exec, Prog.execFrom, hc]
      rw [hq]
      rcases hb with ⟨hbc, hbu⟩ | ⟨hbc, hbe⟩
      · simp [CheckUse.compile, CheckUse.pure, Prog.exec, Prog.execFrom, Adversary.const, hbc, hbu]
      · simp [CheckUse.compile, CheckUse.pure, Prog.exec, Prog.execFrom, Adversary.const, hbc, hbe]
    · have hc' : check (adv 0 a) = false := by simpa using hc
      refine ⟨adv, ?_⟩
      simp [CheckUse.remat, CheckUse.compile, CheckUse.pure, Prog.exec, Prog.execFrom, hc']

end Remat

/-- Robustness is not preserved by private-memory refinement (toy analogue of a
compiler-introduced double fetch): for `cap < 255`, the length check-then-use fragment compiles to
a single-read parser that is R-safe and R-valid, its read rematerialization is a private-memory
refinement of it, and the rematerialized parser is neither R-safe nor R-valid. -/
theorem remat_lenCheck_singleRead_robust_to_not_rsafe_not_rvalid (m cap : Nat)
    (hcap : cap < 255) :
    SingleRead (lenCheck m cap).compile ∧ RSafe (CopyInBounds cap) (lenCheck m cap).compile ∧
      RValid (lpParse cap) (lenCheck m cap).compile ∧
      PrivRefines (lenCheck m cap).remat (lenCheck m cap).compile ∧
      ¬ RSafe (CopyInBounds cap) (lenCheck m cap).remat ∧
      ¬ RValid (lpParse cap) (lenCheck m cap).remat :=
  ⟨(lenOnce_singleRead_implements m cap).1, (lenOnce_rsafe_rvalid m cap).1,
    (lenOnce_rsafe_rvalid m cap).2, remat_privRefines_compile _,
    (lenReread_not_rsafe_not_rvalid m cap hcap).1, (lenReread_not_rsafe_not_rvalid m cap hcap).2⟩

/-- For `cap < 255`, rematerializing the length check is a private-memory refinement but not a
robust result refinement. -/
theorem remat_lenCheck_privRefines_not_robustRefines (m cap : Nat) (hcap : cap < 255) :
    PrivRefines (lenCheck m cap).remat (lenCheck m cap).compile ∧
      ¬ RobustRefines (lenCheck m cap).remat (lenCheck m cap).compile :=
  ⟨remat_privRefines_compile _, fun h =>
    (lenReread_not_rsafe_not_rvalid m cap hcap).2
      (rvalid_of_robustRefines _ _ _ h (lenOnce_rsafe_rvalid m cap).2)⟩

/-- Tightness of `cap < 255` in `remat_lenCheck_privRefines_not_robustRefines`: with `m = 0` and
`cap = 255` every byte passes the check, and the rematerialized length check robustly refines the
original. -/
theorem remat_lenCheck_cap255_robustRefines :
    ¬ (255 < 255) ∧ RobustRefines (lenCheck 0 255).remat (lenCheck 0 255).compile :=
  ⟨by decide, (remat_pure_robustRefines_iff _ _ _ _).mpr fun _ b' =>
    ⟨b', Or.inl ⟨decide_eq_true (Nat.le_of_lt_succ b'.isLt), rfl⟩⟩⟩

/-- Robust refinement relates distinct parsers and does not transfer R-state: the
re-read-and-compare parser differs from the single-read `tagOnce 0`, robustly refines it, and is
not R-state for `boolParse`, while `tagOnce 0` is. -/
theorem robustRefines_rereadCompare_tagOnce_not_preserves_rstate :
    rereadCompare ≠ tagOnce 0 ∧ RobustRefines rereadCompare (tagOnce 0) ∧
      RState boolParse (tagOnce 0) ∧ ¬ RState boolParse rereadCompare := by
  obtain ⟨_, hrv, _, hns, hnr⟩ := rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate
  refine ⟨fun heq => hns (heq ▸ (tagOnce_singleRead_implements 0).1), fun adv => ?_,
    fun adv => ⟨0, ?_⟩, hnr⟩
  · obtain ⟨s', hs'⟩ := hrv adv
    exact ⟨Adversary.const s', by rw [hs', Prog.exec_const, (tagOnce_singleRead_implements 0).2]⟩
  · simp only [tagOnce, tagCheck, CheckUse.compile, CheckUse.pure, Prog.exec, Prog.execFrom,
      boolParse]
    by_cases h : (adv 0 0).val ≤ 1 <;> simp [h, Prog.execFrom]

/-- Tightness of `RobustRefines q p` in `rvalid_of_robustRefines` and `rsafe_of_robustRefines`:
the rematerialized length parser (`cap = 0`) is a private-memory refinement of an R-valid, R-safe
parser, is not a robust refinement of it, and is neither R-valid nor R-safe. -/
theorem robustRefines_hqp_counterexample :
    PrivRefines (lenCheck 0 0).remat (lenCheck 0 0).compile ∧
      ¬ RobustRefines (lenCheck 0 0).remat (lenCheck 0 0).compile ∧
      RValid (lpParse 0) (lenCheck 0 0).compile ∧ RSafe (CopyInBounds 0) (lenCheck 0 0).compile ∧
      ¬ RValid (lpParse 0) (lenCheck 0 0).remat ∧ ¬ RSafe (CopyInBounds 0) (lenCheck 0 0).remat :=
  ⟨remat_privRefines_compile _, (remat_lenCheck_privRefines_not_robustRefines 0 0 (by decide)).2,
    (lenOnce_rsafe_rvalid 0 0).2, (lenOnce_rsafe_rvalid 0 0).1,
    (lenReread_not_rsafe_not_rvalid 0 0 (by decide)).2,
    (lenReread_not_rsafe_not_rvalid 0 0 (by decide)).1⟩

/-- Tightness of the source hypothesis (R-valid or R-safe source) in `rvalid_of_robustRefines` and
`rsafe_of_robustRefines`: a parser robustly refines itself, and the double-fetch length parser
with `cap = 0` is neither R-valid nor R-safe (here the source and the refined parser coincide, so
the failed hypothesis and the failed conclusion are the same statement). -/
theorem robustRefines_source_counterexample :
    RobustRefines (lenReread 0 0) (lenReread 0 0) ∧ ¬ RValid (lpParse 0) (lenReread 0 0) ∧
      ¬ RSafe (CopyInBounds 0) (lenReread 0 0) :=
  ⟨fun adv => ⟨adv, rfl⟩, (lenReread_not_rsafe_not_rvalid 0 0 (by decide)).2,
    (lenReread_not_rsafe_not_rvalid 0 0 (by decide)).1⟩

/-- Non-vacuity of `rvalid_of_robustRefines` and `rsafe_of_robustRefines` with distinct parsers:
`rereadCompare` robustly refines `tagOnce 0`, which is R-valid for `boolParse` and R-safe for
`ValidBoolOut`. -/
theorem robustRefines_transfer_nonvacuous :
    rereadCompare ≠ tagOnce 0 ∧ RobustRefines rereadCompare (tagOnce 0) ∧
      RValid boolParse (tagOnce 0) ∧ RSafe ValidBoolOut (tagOnce 0) :=
  ⟨robustRefines_rereadCompare_tagOnce_not_preserves_rstate.1,
    robustRefines_rereadCompare_tagOnce_not_preserves_rstate.2.1,
    (tagOnce_rsafe_rvalid 0).2, (tagOnce_rsafe_rvalid 0).1⟩

/-- Non-vacuity of the remat characterization in a robust case: when the use ignores its byte
(`u = fun _ => e'`), the rematerialization is a robust refinement. -/
theorem remat_pure_robustRefines_const_use :
    RobustRefines (CheckUse.pure (0 : Fin 1) (fun b => decide (b.val ≤ 0)) (fun _ => (1 : Nat)) 2).remat
      (CheckUse.pure (0 : Fin 1) (fun b => decide (b.val ≤ 0)) (fun _ => (1 : Nat)) 2).compile :=
  (remat_pure_robustRefines_iff _ _ _ _).mpr fun ⟨b, hb⟩ _ => ⟨b, Or.inl ⟨hb, rfl⟩⟩

/-! ## 9. Validated typed views -/

theorem viewUses_eval (k : Nat) (acc : List (Byte × Byte)) (s : Region 2) :
    (viewUses k acc).eval s = some (List.replicate k (s 0, s 1) ++ acc) := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
    simp only [viewUses, Prog.eval]
    rw [ih]
    simp [List.replicate_succ']

theorem viewUses_execFrom_of_window (k : Nat) (acc : List (Byte × Byte)) (adv : Adversary 2)
    (s : Region 2) (t0 : Nat) (h : ∀ t, t0 ≤ t → t < t0 + 2 * k → adv t = s) :
    (viewUses k acc).execFrom adv t0 = (viewUses k acc).eval s := by
  induction k generalizing acc t0 with
  | zero => rfl
  | succ k ih =>
    simp only [viewUses, Prog.execFrom, Prog.eval]
    rw [h t0 (by omega) (by omega), h (t0 + 1) (by omega) (by omega)]
    exact ih _ (t0 + 1 + 1) (fun t h1 h2 => h t (by omega) (by omega))

/-- The view program implements `viewSpec k` in private memory. -/
theorem viewProg_implements (k : Nat) : Implements (viewProg k) (viewSpec k) := by
  intro s
  simp only [viewProg, Prog.eval, viewSpec]
  split
  · rw [viewUses_eval]; simp
  · rfl

/-- Validate once, sound without foreign writes: if the writer changes nothing during the run of
the view program (`adv t = adv 0` for every `t < 2 + 2 * k`), every one of the `k` later decodes
through the view is a valid tagged value. -/
theorem viewProg_viewOK_of_noForeignWrites (k : Nat) (adv : Adversary 2)
    (hno : ∀ t, t < 2 + 2 * k → adv t = adv 0) : ViewOK ((viewProg k).exec adv) := by
  have h1 : adv 1 = adv 0 := hno 1 (by omega)
  simp only [viewProg, Prog.exec, Prog.execFrom, h1]
  split
  · rename_i hv
    rw [viewUses_execFrom_of_window k [] adv (adv 0) 2 (fun t _ h2 => hno t (by omega)),
      viewUses_eval]
    intro x hx
    simp only [List.append_nil, List.mem_replicate] at hx
    rw [hx.2]
    exact hv
  · trivial

/-- Validate once, unsound with a concurrent writer: `viewFlipAdv` (tag flips from `0` to `1`
after validation, payload `2`) writes during the run, and the one later decode through the view is
`(1, 2)`, which is not a valid tagged value. -/
theorem viewProg_tagFlip_invalid :
    ¬ (∀ t, t < 2 + 2 * 1 → viewFlipAdv t = viewFlipAdv 0) ∧
      (viewProg 1).exec viewFlipAdv = some [(1, 2)] ∧ ¬ ViewOK ((viewProg 1).exec viewFlipAdv) := by
  have h1 : (viewProg 1).exec viewFlipAdv = some [(1, 2)] := by
    simp only [viewProg, Prog.exec, Prog.execFrom]
    decide
  refine ⟨fun h => ?_, h1, ?_⟩
  · have := congrFun (h 2 (by omega)) 0
    revert this
    decide
  · rw [h1]
    intro h
    have := h (1, 2) (by simp)
    revert this
    decide

/-- Validate once, unsound even against a writer whose every state is valid: `validSwitchAdv`
switches once, atomically, from the valid `(1, 1)` to the valid `(0, 2)` between the view's read of
the tag (time `2`) and of the payload (time `3`) in the later decode, which is `(1, 2)`, not a
valid tagged value. -/
theorem viewProg_validSwitch_breaks_viewOK :
    (∀ t : Nat, ValidE (validSwitchAdv t 0) (validSwitchAdv t 1)) ∧
      (viewProg 1).exec validSwitchAdv = some [(1, 2)] ∧
      ¬ ViewOK ((viewProg 1).exec validSwitchAdv) := by
  have h1 : (viewProg 1).exec validSwitchAdv = some [(1, 2)] := by
    simp only [viewProg, Prog.exec, Prog.execFrom]
    decide
  refine ⟨fun t => ?_, h1, ?_⟩
  · by_cases ht : t < 3
    · simp only [validSwitchAdv, ht, ite_true]; decide
    · simp only [validSwitchAdv, ht, ite_false]; decide
  · rw [h1]
    intro h
    have := h (1, 2) (by simp)
    revert this
    decide

/-- Degenerate edge `k = 0`: with no later decodes the view program satisfies `ViewOK` against
every writer. -/
theorem viewProg_zero_rsafe : RSafe ViewOK (viewProg 0) := by
  intro adv
  simp only [viewProg, Prog.exec, Prog.execFrom]
  split
  · intro x hx; cases hx
  · trivial

theorem viewOK_viewSpec (k : Nat) (s : Region 2) : ViewOK (viewSpec k s) := by
  simp only [viewSpec]
  split
  · rename_i hv
    intro x hx
    rw [(List.mem_replicate.mp hx).2]
    exact hv
  · trivial

/-- Byte-by-byte copy-out is sound for validity: the copy-out program is single-read, implements
`viewSpec k` and agrees with the view program in private memory, and against every writer its
result is `viewSpec k s'` for some byte vector `s'` and all its decodes are valid tagged
values. -/
theorem copyOutProg_singleRead_implements_rvalid_rsafe_viewOK (k : Nat) :
    SingleRead (copyOutProg k) ∧ Implements (copyOutProg k) (viewSpec k) ∧
      PrivRefines (copyOutProg k) (viewProg k) ∧ RValid (viewSpec k) (copyOutProg k) ∧
      RSafe ViewOK (copyOutProg k) := by
  obtain ⟨hs, hi⟩ := copyParse_singleRead_implements (viewSpec k)
  refine ⟨hs, hi, fun s => ?_, rvalid_of_singleRead_of_implements _ _ hs hi,
    rsafe_of_singleRead_of_staticSafe _ _ hs fun s => ?_⟩
  · show (copyOutProg k).eval s = (viewProg k).eval s
    rw [viewProg_implements]
    exact hi s
  · show ViewOK ((copyOutProg k).eval s)
    rw [show (copyOutProg k).eval s = viewSpec k s from hi s]
    exact viewOK_viewSpec k s

/-- Single-read decoding into an owned value is sound for validity: the owned-value program is
single-read, implements `viewSpec k` and agrees with the view program in private memory, and
against every writer its result is `viewSpec k s'` for some byte vector `s'` and all its decodes
are valid tagged values. -/
theorem ownedProg_singleRead_implements_rvalid_rsafe_viewOK (k : Nat) :
    SingleRead (ownedProg k) ∧ Implements (ownedProg k) (viewSpec k) ∧
      PrivRefines (ownedProg k) (viewProg k) ∧ RValid (viewSpec k) (ownedProg k) ∧
      RSafe ViewOK (ownedProg k) := by
  have hs : SingleRead (ownedProg k) := by
    refine ⟨rfl, fun t => ?_⟩
    by_cases ht : 1 < t.val
    · simp [ht, Prog.SingleReadFrom]
    · simp only [ht, ite_false]
      refine ⟨by decide, fun p => ?_⟩
      by_cases hv : ValidE t p <;> simp [hv, Prog.SingleReadFrom]
  have hi : Implements (ownedProg k) (viewSpec k) := by
    intro s
    simp only [ownedProg, Prog.eval, viewSpec]
    by_cases ht : 1 < (s 0).val
    · have hv : ¬ ValidE (s 0) (s 1) := by unfold ValidE; omega
      simp [ht, hv, Prog.eval]
    · simp only [ht, ite_false, Prog.eval]
      split <;> rfl
  refine ⟨hs, hi, fun s => ?_, rvalid_of_singleRead_of_implements _ _ hs hi,
    rsafe_of_singleRead_of_staticSafe _ _ hs fun s => ?_⟩
  · rw [hi s, viewProg_implements]
  · rw [hi s]
    exact viewOK_viewSpec k s

/-- Copy-out is not a consistent snapshot: against `copyTornAdv` (`(0, 2)` at time `0`, `(1, 1)`
afterwards; both valid) the byte-by-byte copy-out program returns `some [(0, 1)]`, a valid decode
that is `viewSpec 1` of no state the writer produced; so it is not R-state. -/
theorem copyOutProg_torn_valid_not_rstate :
    (copyOutProg 1).exec copyTornAdv = some [(0, 1)] ∧
      ViewOK ((copyOutProg 1).exec copyTornAdv) ∧
      (∀ t : Nat, (copyOutProg 1).exec copyTornAdv ≠ viewSpec 1 (copyTornAdv t)) ∧
      ¬ RState (viewSpec 1) (copyOutProg 1) := by
  have h1 : (copyOutProg 1).exec copyTornAdv = some [(0, 1)] := by
    rw [copyOutProg, (copyParse_exec_eq_diagonal_and_rvalid (viewSpec 1)).1]
    decide
  have h2 : ∀ t : Nat, (copyOutProg 1).exec copyTornAdv ≠ viewSpec 1 (copyTornAdv t) := by
    intro t
    rw [h1]
    by_cases ht : t = 0
    · subst ht; decide
    · simp only [copyTornAdv, ht, ite_false]; decide
  refine ⟨h1, ?_, h2, fun hR => by obtain ⟨t, ht⟩ := hR copyTornAdv; exact h2 t ht⟩
  rw [h1]
  intro x hx
  simp at hx
  rw [hx]
  decide

/-- Owned decoding and copy-out return the same result against every writer: both decode the tag
read at time `0` together with the payload read at time `1`; owned decoding skips the payload read
when the tag alone makes the value invalid, and then both return the error result. -/
theorem ownedProg_exec_eq_copyOutProg_exec (k : Nat) (adv : Adversary 2) :
    (ownedProg k).exec adv = (copyOutProg k).exec adv := by
  rw [copyOutProg, (copyParse_exec_eq_diagonal_and_rvalid (viewSpec k)).1]
  simp only [ownedProg, Prog.exec, Prog.execFrom, viewSpec]
  by_cases ht : 1 < (adv 0 0).val
  · have hv : ¬ ValidE (adv 0 0) (adv 1 1) := by unfold ValidE; omega
    simp [ht, hv, Prog.execFrom]
  · simp only [ht, ite_false, Prog.execFrom]
    by_cases hv : ValidE (adv 0 0) (adv 1 1) <;> simp [hv, Prog.execFrom]

/-- Copy-out reads two bytes against every writer; owned decoding reads one byte when the tag it
reads at time `0` exceeds `1`, and two bytes otherwise. -/
theorem copyOutProg_ownedProg_access_counts (k : Nat) (adv : Adversary 2) :
    ((copyOutProg k).obs adv).1.length = 2 ∧
      ((ownedProg k).obs adv).1.length = (if 1 < (adv 0 0).val then 1 else 2) := by
  have hf : List.finRange 2 = [0, 1] := by decide
  constructor
  · simp only [copyOutProg, copyParse, byteCopy, hf, readSeq, Prog.obs, Prog.obsFrom]
    rfl
  · simp only [ownedProg, Prog.obs, Prog.obsFrom]
    by_cases ht : 1 < (adv 0 0).val
    · simp [ht, Prog.obsFrom]
    · simp only [ht, ite_false, Prog.obsFrom]
      split <;> rfl

/-- Owned decoding and copy-out are different parsers for every `k` (they differ on the writer
that never writes and shows the invalid tag `2`); equivalently, neither observably refines the
other (`obsRefines_iff_eq`). -/
theorem ownedProg_ne_copyOutProg (k : Nat) :
    ownedProg k ≠ copyOutProg k ∧ ¬ ObsRefines (ownedProg k) (copyOutProg k) ∧
      ¬ ObsRefines (copyOutProg k) (ownedProg k) := by
  have hne : ownedProg k ≠ copyOutProg k := by
    intro h
    have hc := copyOutProg_ownedProg_access_counts k (Adversary.const (reg2 2 0))
    rw [h, hc.1] at hc
    have h2 := hc.2
    revert h2
    decide
  exact ⟨hne, fun h => hne ((obsRefines_iff_eq _ _).mp h),
    fun h => hne ((obsRefines_iff_eq _ _).mp h).symm⟩

/-- Owned decoding is not a consistent snapshot either: against `copyTornAdv` it returns the same
torn valid decode `some [(0, 1)]` as copy-out, which is `viewSpec 1` of no state the writer
produced; so it is not R-state. -/
theorem ownedProg_torn_valid_not_rstate :
    (ownedProg 1).exec copyTornAdv = some [(0, 1)] ∧
      ViewOK ((ownedProg 1).exec copyTornAdv) ∧
      (∀ t : Nat, (ownedProg 1).exec copyTornAdv ≠ viewSpec 1 (copyTornAdv t)) ∧
      ¬ RState (viewSpec 1) (ownedProg 1) := by
  obtain ⟨h1, h2, h3, _⟩ := copyOutProg_torn_valid_not_rstate
  rw [ownedProg_exec_eq_copyOutProg_exec]
  refine ⟨h1, h2, h3, fun hR => ?_⟩
  obtain ⟨t, ht⟩ := hR copyTornAdv
  rw [ownedProg_exec_eq_copyOutProg_exec] at ht
  exact h3 t ht

/-! ## Hypothesis counterexamples and non-vacuity witnesses -/

/-- Tightness of `SingleRead` in `singleRead_exec_eq_eval_assemble`: for `cap < 255`, the
double-fetch length parser is not single-read, and against `lenFlipAdv` its result differs from
the private-memory result on the assembled vector, for every filler. -/
theorem lenReread_exec_ne_eval_assemble (m cap : Nat) (hcap : cap < 255) :
    ¬ SingleRead (lenReread m cap) ∧
      ∀ d : Region (m + 1), (lenReread m cap).exec (lenFlipAdv m cap) ≠
        (lenReread m cap).eval ((lenReread m cap).assemble (lenFlipAdv m cap) d) := by
  refine ⟨fun h => ?_, fun d => ?_⟩
  · obtain ⟨_, h2⟩ := h
    have h3 := h2 0
    simp [lenCheck, CheckUse.pure, Prog.SingleReadFrom] at h3
  · rw [lenReread_implements]
    exact (lenReread_flip_out_of_bounds_and_invalid m cap hcap).2.2 _

/-- Tightness of `SingleRead` in `rvalid_of_singleRead_of_implements`: the double-fetch length
parser with `cap = 0` implements `lpParse 0`, is not single-read, and is not R-valid. -/
theorem singleRead_hyp_counterexample_rvalid :
    Implements (lenReread 0 0) (lpParse 0) ∧ ¬ SingleRead (lenReread 0 0) ∧
      ¬ RValid (lpParse 0) (lenReread 0 0) :=
  ⟨lenReread_implements 0 0, (lenReread_exec_ne_eval_assemble 0 0 (by decide)).1,
    (lenReread_not_rsafe_not_rvalid 0 0 (by decide)).2⟩

/-- Tightness of `Implements` in `rvalid_of_singleRead_of_implements`: the constant parser
returning `some 1` is single-read, does not implement `lpParse 0`, and is not R-valid for it. -/
theorem implements_hyp_counterexample_rvalid :
    SingleRead (Prog.ret (some 1) : Prog 1 (Option Nat)) ∧
      ¬ Implements (Prog.ret (some 1) : Prog 1 (Option Nat)) (lpParse 0) ∧
      ¬ RValid (lpParse 0) (Prog.ret (some 1) : Prog 1 (Option Nat)) := by
  have hne : ∀ s' : Region 1, (some 1 : Option Nat) ≠ lpParse 0 s' := by
    intro s' h
    simp only [lpParse] at h
    split at h
    · simp at h; omega
    · simp at h
  refine ⟨trivial, fun h => hne (fun _ => 0) (h _), fun h => ?_⟩
  obtain ⟨s', hs'⟩ := h (fun _ _ => 0)
  exact hne s' hs'

/-- Tightness of `SingleRead` in `rsafe_of_singleRead_of_staticSafe`: the double-fetch length
parser with `cap = 0` is safe in private memory, is not single-read, and is not R-safe. -/
theorem singleRead_hyp_counterexample_rsafe :
    (∀ s : Region 1, CopyInBounds 0 ((lenReread 0 0).eval s)) ∧ ¬ SingleRead (lenReread 0 0) ∧
      ¬ RSafe (CopyInBounds 0) (lenReread 0 0) := by
  refine ⟨fun s => ?_, (lenReread_exec_ne_eval_assemble 0 0 (by decide)).1,
    (lenReread_not_rsafe_not_rvalid 0 0 (by decide)).1⟩
  rw [lenReread_implements]
  simp only [lpParse]
  split
  · simp only [CopyInBounds]; assumption
  · trivial

/-- Tightness of private-memory safety in `rsafe_of_singleRead_of_staticSafe`: the constant parser
returning `some 1` is single-read, unsafe in private memory for capacity `0`, and not R-safe. -/
theorem staticSafe_hyp_counterexample_rsafe :
    SingleRead (Prog.ret (some 1) : Prog 1 (Option Nat)) ∧
      ¬ (∀ s : Region 1, CopyInBounds 0 ((Prog.ret (some 1) : Prog 1 (Option Nat)).eval s)) ∧
      ¬ RSafe (CopyInBounds 0) (Prog.ret (some 1) : Prog 1 (Option Nat)) := by
  refine ⟨trivial, fun h => ?_, fun h => ?_⟩
  · have := h (fun _ => 0); simp [CopyInBounds, Prog.eval] at this
  · have := h (fun _ _ => 0); simp [CopyInBounds, Prog.exec, Prog.execFrom] at this

/-- Non-vacuity of `rsafe_of_singleRead_of_staticSafe`: both hypotheses hold for the single-read
length parser with capacity `4`. -/
theorem rsafe_of_singleRead_hyps_nonvacuous :
    SingleRead (lenOnce 0 4) ∧ ∀ s : Region 1, CopyInBounds 4 ((lenOnce 0 4).eval s) := by
  refine ⟨(lenOnce_singleRead_implements 0 4).1, fun s => ?_⟩
  rw [← Prog.exec_const]
  exact (lenOnce_rsafe_rvalid 0 4).1 _

/-- A data-dependent single-read parser: `dataDepProg` chooses its second address from the first
byte and is single-read. -/
theorem dataDepProg_singleRead : SingleRead dataDepProg := by
  refine ⟨rfl, fun b => ?_⟩
  by_cases h : b.val = 0
  · simp only [h, ite_true, Prog.SingleReadFrom]
    exact ⟨by decide, fun _ => trivial⟩
  · simp only [h, ite_false, Prog.SingleReadFrom]
    exact ⟨by decide, fun _ => trivial⟩

/-- Degenerate edge `n = 0`: on the empty region two snapshots in a row are single-read, because a
snapshot of the empty region reads no address. -/
theorem singleRead_zero_double_snap :
    SingleRead (.snap fun _ => .snap fun _ => .ret () : Prog 0 Unit) :=
  ⟨fun j => j.elim0, fun _ => ⟨fun j => j.elim0, fun _ => trivial⟩⟩

/-- Non-vacuity of `viewProg_viewOK_of_noForeignWrites`: the writer that never writes satisfies
its hypothesis, and the view program then returns two valid decodes. -/
theorem viewProg_nonvacuous :
    (∀ t, t < 2 + 2 * 2 → Adversary.const (reg2 1 0) t = Adversary.const (reg2 1 0) 0) ∧
      (viewProg 2).exec (Adversary.const (reg2 1 0)) = some [(1, 0), (1, 0)] :=
  ⟨fun _ _ => rfl, by rw [Prog.exec_const]; decide⟩

end Toy.DoubleFetch
