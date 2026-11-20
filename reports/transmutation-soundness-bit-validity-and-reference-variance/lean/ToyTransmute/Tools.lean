import ToyTransmute.Basic

/-!
# Proof tools (all fully proved)

* `sound_of_invariant`: the generic sufficiency tool. A predicate on region contents that
  holds initially, is re-established by every permitted well-typed write, and implies the
  validity demanded by every permitted read, guarantees the safety contract.
* `not_sound_of_read_dst` and `not_sound_of_write_dst_read_src`: the two explicit
  violating runs. They expose the concrete witnesses behind every necessity claim of the
  package: *read through the cast view* (needs `T ⊆ U`), and *write through the cast view,
  then read through the original view* (needs `U ⊆ T`).
* Membership of those two runs in each discipline.
-/

namespace Toy.Transmute

variable {B : Type} {n : Nat}

/-- What it means for a region invariant `I` to be compatible with one operation, under
source type `T` and destination type `U`: a read requires `I` to imply validity at the
reader's type; a well-typed write must re-establish `I`. -/
def Op.Preserves (T U : Validity B n) (I : Bytes B n → Prop) : Op B n → Prop
  | .read s => ∀ m, I m → s.ty T U m
  | .write s v => s.ty T U v → I v

/-- Invariant reasoning for a single run. -/
theorem noInvalidRead_of_invariant {T U : Validity B n} (I : Bytes B n → Prop) :
    ∀ (tr : List (Op B n)) (m : Bytes B n), I m → (∀ op ∈ tr, op.WellTyped T U) →
      (∀ op ∈ tr, op.Preserves T U I) → NoInvalidRead T U m tr := by
  intro tr
  induction tr with
  | nil => intro _ _ _ _; trivial
  | cons op rest ih =>
    intro m hm hwt hp
    have hwt' : ∀ o ∈ rest, o.WellTyped T U := fun o h => hwt o (List.mem_cons_of_mem _ h)
    have hp' : ∀ o ∈ rest, o.Preserves T U I := fun o h => hp o (List.mem_cons_of_mem _ h)
    have hop := hp op (by simp)
    have hwop := hwt op (by simp)
    cases op with
    | read s =>
      exact ⟨hop m hm, ih m hm hwt' hp'⟩
    | write s v =>
      exact ih v (hop hwop) hwt' hp'

/-- **Sufficiency tool.** If `I` holds on every `T`-valid initial value and every operation
of every permitted run is compatible with `I`, the discipline is sound. -/
theorem sound_of_invariant {P : Protocol B n} {T U : Validity B n} (I : Bytes B n → Prop)
    (hinit : ∀ m, T m → I m)
    (hops : ∀ tr, P tr → ∀ op ∈ tr, op.Preserves T U I) : Sound P T U := by
  intro m hm tr htr hwt
  exact noInvalidRead_of_invariant I tr m (hinit m hm) hwt (hops tr htr)

/-- Every discipline is sound for the identity cast `T → T` (invariant: `T`). -/
theorem sound_refl (P : Protocol B n) (T : Validity B n) : Sound P T T := by
  apply sound_of_invariant T (fun _ h => h)
  intro _ _ op _
  cases op with
  | read s => cases s <;> exact fun _ h => h
  | write s v => cases s <;> exact fun h => h

/-- The run "read once through the cast view". -/
def readDst : List (Op B n) := [.read .dst]

/-- The run "write `u` through the cast view, then read through the original view". -/
def writeDstReadSrc (u : Bytes B n) : List (Op B n) := [.write .dst u, .read .src]

/-- **Witness (reads).** If some `T`-valid `m` is not `U`-valid, the run `readDst` from `m`
reads invalid bytes. -/
theorem readDst_violates {T U : Validity B n} {m : Bytes B n} (hU : ¬ U m) :
    ¬ NoInvalidRead T U m readDst := by
  intro h
  exact hU h.1

/-- **Witness (writes).** If `u` is not `T`-valid, the run `writeDstReadSrc u` (from any
contents) reads invalid bytes. -/
theorem writeDstReadSrc_violates {T U : Validity B n} (m : Bytes B n) {u : Bytes B n}
    (hu : ¬ T u) : ¬ NoInvalidRead T U m (writeDstReadSrc u) := by
  intro h
  exact hu h.1

/-- `writeDstReadSrc u` is well typed exactly when `u` is `U`-valid. -/
theorem writeDstReadSrc_wellTyped {T U : Validity B n} {u : Bytes B n} (hu : U u) :
    ∀ op ∈ (writeDstReadSrc u : List (Op B n)), op.WellTyped T U := by
  intro op hop
  simp only [writeDstReadSrc, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl
  · exact hu
  · trivial

/-- `readDst` is well typed. -/
theorem readDst_wellTyped {T U : Validity B n} :
    ∀ op ∈ (readDst : List (Op B n)), op.WellTyped T U := by
  intro op hop
  simp only [readDst, List.mem_cons, List.not_mem_nil, or_false] at hop
  subst hop
  trivial

/-- **Generic necessity of reads.** If a discipline permits `readDst` and some `T`-valid
byte sequence is not `U`-valid, the discipline is unsound for `T → U`. -/
theorem not_sound_of_read_dst {P : Protocol B n} {T U : Validity B n}
    (hP : P readDst) {m : Bytes B n} (hT : T m) (hU : ¬ U m) : ¬ Sound P T U := by
  intro hs
  exact readDst_violates hU (hs m hT readDst hP readDst_wellTyped)

/-- **Generic necessity of writes.** If a discipline permits `writeDstReadSrc u` for a
`U`-valid `u` that is not `T`-valid, and `T` is satisfiable, the discipline is unsound for
`T → U`. -/
theorem not_sound_of_write_dst_read_src {P : Protocol B n} {T U : Validity B n}
    {u : Bytes B n} (hP : P (writeDstReadSrc u)) {m : Bytes B n} (hT : T m) (hUu : U u)
    (hTu : ¬ T u) : ¬ Sound P T U := by
  intro hs
  exact writeDstReadSrc_violates m hTu (hs m hT _ hP (writeDstReadSrc_wellTyped hUu))

/-- `readDst` is a value-transmute run. -/
theorem valueProtocol_readDst : (valueProtocol : Protocol B n) readDst := by
  intro op hop
  simp only [readDst, List.mem_cons, List.not_mem_nil, or_false] at hop
  subst hop; rfl

/-- `readDst` is a shared-cast run. -/
theorem sharedProtocol_readDst : (sharedProtocol : Protocol B n) readDst := by
  intro op hop
  simp only [readDst, List.mem_cons, List.not_mem_nil, or_false] at hop
  subst hop; trivial

/-- `readDst` is a mutable-cast run (it lies entirely in the exclusive period). -/
theorem mutProtocol_readDst : (mutProtocol : Protocol B n) readDst := by
  refine ⟨readDst, [], by simp, ?_, by simp⟩
  intro op hop
  simp only [readDst, List.mem_cons, List.not_mem_nil, or_false] at hop
  subst hop; rfl

/-- `readDst` is permitted by every interior-mutability discipline. -/
theorem sharedIMProtocol_readDst (srcWrites dstWrites : Bool) :
    (sharedIMProtocol srcWrites dstWrites : Protocol B n) readDst := by
  intro op hop
  simp only [readDst, List.mem_cons, List.not_mem_nil, or_false] at hop
  subst hop; trivial

/-- `writeDstReadSrc u` is a mutable-cast run: the write happens while the cast reference is
live, the read after the original owner regains access. -/
theorem mutProtocol_writeDstReadSrc (u : Bytes B n) :
    (mutProtocol : Protocol B n) (writeDstReadSrc u) := by
  refine ⟨[.write .dst u], [.read .src], rfl, ?_, ?_⟩
  · intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    subst hop; rfl
  · intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    subst hop; rfl

/-- `writeDstReadSrc u` is permitted by an interior-mutability discipline whose destination
side may write. -/
theorem sharedIMProtocol_writeDstReadSrc (srcWrites : Bool) (u : Bytes B n) :
    (sharedIMProtocol srcWrites true : Protocol B n) (writeDstReadSrc u) := by
  intro op hop
  simp only [writeDstReadSrc, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl
  · rfl
  · trivial

/-- With no writes permitted, the interior-mutability discipline is the plain shared
discipline. -/
theorem sharedIMProtocol_false_false :
    (sharedIMProtocol false false : Protocol B n) = sharedProtocol := by
  funext tr
  apply propext
  constructor
  · intro h op hop
    have := h op hop
    cases op with
    | read s => trivial
    | write s v => cases s <;> simp [Op.PermittedIM] at this
  · intro h op hop
    have := h op hop
    cases op with
    | read s => trivial
    | write s v => exact absurd this id

/-- An operation of a value-transmute run goes through the destination view. -/
theorem valueProtocol_side {tr : List (Op B n)} (h : (valueProtocol : Protocol B n) tr)
    {op : Op B n} (hop : op ∈ tr) : op.side = .dst := h op hop

/-! ## Per-discipline invariant tools

Each tool specialises `sound_of_invariant` to one discipline, listing exactly the
operations that discipline permits. They are sufficient conditions only. -/

/-- Invariant tool for value transmutes (only the destination view acts). -/
theorem valueSound_of_invariant {T U : Validity B n} (I : Bytes B n → Prop)
    (hinit : ∀ m, T m → I m) (hread : ∀ m, I m → U m) (hwrite : ∀ v, U v → I v) :
    ValueSound T U := by
  apply sound_of_invariant I hinit
  intro tr htr op hop
  have hs := htr op hop
  cases op with
  | read s => cases s
              · simp [Op.side] at hs
              · exact hread
  | write s v => cases s
                 · simp [Op.side] at hs
                 · exact hwrite v

/-- Invariant tool for shared casts without interior mutability (reads only). -/
theorem sharedSound_of_invariant {T U : Validity B n} (I : Bytes B n → Prop)
    (hinit : ∀ m, T m → I m) (hsrc : ∀ m, I m → T m) (hdst : ∀ m, I m → U m) :
    SharedSound T U := by
  apply sound_of_invariant I hinit
  intro tr htr op hop
  have hs := htr op hop
  cases op with
  | read s => cases s
              · exact hsrc
              · exact hdst
  | write s v => exact False.elim hs

/-- Invariant tool for mutable casts, using one invariant for both periods. -/
theorem mutSound_of_invariant {T U : Validity B n} (I : Bytes B n → Prop)
    (hinit : ∀ m, T m → I m) (hsrc : ∀ m, I m → T m) (hdst : ∀ m, I m → U m)
    (hwsrc : ∀ v, T v → I v) (hwdst : ∀ v, U v → I v) : MutSound T U := by
  apply sound_of_invariant I hinit
  intro _ _ op _
  cases op with
  | read s => cases s
              · exact hsrc
              · exact hdst
  | write s v => cases s
                 · exact hwsrc v
                 · exact hwdst v

/-- Invariant tool for shared casts with interior mutability. -/
theorem sharedIMSound_of_invariant {srcWrites dstWrites : Bool} {T U : Validity B n}
    (I : Bytes B n → Prop)
    (hinit : ∀ m, T m → I m) (hsrc : ∀ m, I m → T m) (hdst : ∀ m, I m → U m)
    (hwsrc : srcWrites = true → ∀ v, T v → I v)
    (hwdst : dstWrites = true → ∀ v, U v → I v) : SharedIMSound srcWrites dstWrites T U := by
  apply sound_of_invariant I hinit
  intro tr htr op hop
  have hs := htr op hop
  cases op with
  | read s => cases s
              · exact hsrc
              · exact hdst
  | write s v => cases s
                 · exact hwsrc hs v
                 · exact hwdst hs v

/-- Every discipline is sound between extensionally equal validities (invariant: `T`). -/
theorem sound_of_validityEq (P : Protocol B n) {T U : Validity B n} (h : ValidityEq T U) :
    Sound P T U := by
  apply sound_of_invariant T (fun _ hm => hm)
  intro _ _ op _
  cases op with
  | read s => cases s
              · exact fun _ hm => hm
              · exact fun m hm => (h m).1 hm
  | write s v => cases s
                 · exact fun hv => hv
                 · exact fun hv => (h v).2 hv

/-- Every discipline is vacuously sound from an unsatisfiable source type: there is no
valid initial value to start from. -/
theorem sound_of_not_satisfiable (P : Protocol B n) {T : Validity B n}
    (hT : ¬ Satisfiable T) (U : Validity B n) : Sound P T U := by
  intro m hm
  exact absurd ⟨m, hm⟩ hT

/-! ## Two-phase invariant reasoning and checked casts -/

/-- Invariant reasoning for a run made of two consecutive segments: invariant `I` on the
first segment, `J` on the second, with `I` implying `J` at the switch. -/
theorem noInvalidRead_append_of_invariants {T U : Validity B n} (I J : Bytes B n → Prop)
    (hIJ : ∀ m, I m → J m) :
    ∀ (l₁ l₂ : List (Op B n)) (m : Bytes B n), I m →
      (∀ op ∈ l₁, op.WellTyped T U) → (∀ op ∈ l₂, op.WellTyped T U) →
      (∀ op ∈ l₁, op.Preserves T U I) → (∀ op ∈ l₂, op.Preserves T U J) →
      NoInvalidRead T U m (l₁ ++ l₂) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ m hm _ hwt₂ _ hp₂
    exact noInvalidRead_of_invariant J l₂ m (hIJ m hm) hwt₂ hp₂
  | cons op rest ih =>
    intro l₂ m hm hwt₁ hwt₂ hp₁ hp₂
    have hwt' : ∀ o ∈ rest, o.WellTyped T U := fun o h => hwt₁ o (List.mem_cons_of_mem _ h)
    have hp' : ∀ o ∈ rest, o.Preserves T U I := fun o h => hp₁ o (List.mem_cons_of_mem _ h)
    have hop := hp₁ op (by simp)
    have hwop := hwt₁ op (by simp)
    cases op with
    | read s => exact ⟨hop m hm, ih l₂ m hm hwt' hwt₂ hp' hp₂⟩
    | write s v => exact ih l₂ v (hop hwop) hwt' hwt₂ hp' hp₂

/-- Unchecked soundness implies checked soundness: a check at cast time only removes
initial contents. -/
theorem checkedSound_of_sound {P : Protocol B n} {T U : Validity B n} (h : Sound P T U) :
    CheckedSound P T U := fun m hm _ => h m hm

/-- **Sufficiency tool for checked casts.** The invariant must hold on every contents that
pass the check (valid at both types) and be compatible with every permitted operation. -/
theorem checkedSound_of_invariant {P : Protocol B n} {T U : Validity B n}
    (I : Bytes B n → Prop) (hinit : ∀ m, T m → U m → I m)
    (hops : ∀ tr, P tr → ∀ op ∈ tr, op.Preserves T U I) : CheckedSound P T U := by
  intro m hT hU tr htr hwt
  exact noInvalidRead_of_invariant I tr m (hinit m hT hU) hwt (hops tr htr)

/-- Two-phase invariant tool for checked mutable casts: invariant `I` while the cast
reference is used, `J` afterwards, with `I → J` at the switch. -/
theorem checkedSound_mut_of_invariants {T U : Validity B n} (I J : Bytes B n → Prop)
    (hinit : ∀ m, T m → U m → I m) (hIJ : ∀ m, I m → J m)
    (hdst : ∀ m, I m → U m) (hwdst : ∀ v, U v → I v)
    (hsrc : ∀ m, J m → T m) (hwsrc : ∀ v, T v → J v) : CheckedSound mutProtocol T U := by
  rintro m hT hU tr ⟨d, a, rfl, hd, ha⟩ hwt
  refine noInvalidRead_append_of_invariants I J hIJ d a m (hinit m hT hU)
    (fun op h => hwt op (List.mem_append_left _ h))
    (fun op h => hwt op (List.mem_append_right _ h)) ?_ ?_
  · intro op hop
    have hs := hd op hop
    cases op with
    | read s => cases s
                · simp [Op.side] at hs
                · exact hdst
    | write s v => cases s
                   · simp [Op.side] at hs
                   · exact hwdst v
  · intro op hop
    have hs := ha op hop
    cases op with
    | read s => cases s
                · exact hsrc
                · simp [Op.side] at hs
    | write s v => cases s
                   · exact hwsrc v
                   · simp [Op.side] at hs

/-- A checked cast is vacuously sound when no byte sequence is valid at both types: the
check never succeeds. -/
theorem checkedSound_of_not_satisfiable_meet (P : Protocol B n) {T U : Validity B n}
    (h : ¬ Satisfiable (T.meet U)) : CheckedSound P T U := by
  intro m hT hU
  exact absurd ⟨m, hT, hU⟩ h

/-- The run "write `v` through the original view, then read through the cast view". -/
def writeSrcReadDst (v : Bytes B n) : List (Op B n) := [.write .src v, .read .dst]

/-- `writeSrcReadDst v` is well typed exactly when `v` is `T`-valid. -/
theorem writeSrcReadDst_wellTyped {T U : Validity B n} {v : Bytes B n} (hv : T v) :
    ∀ op ∈ (writeSrcReadDst v : List (Op B n)), op.WellTyped T U := by
  intro op hop
  simp only [writeSrcReadDst, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl
  · exact hv
  · trivial

/-- `writeSrcReadDst v` is permitted by an interior-mutability discipline whose source side
may write. -/
theorem sharedIMProtocol_writeSrcReadDst (dstWrites : Bool) (v : Bytes B n) :
    (sharedIMProtocol true dstWrites : Protocol B n) (writeSrcReadDst v) := by
  intro op hop
  simp only [writeSrcReadDst, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl
  · rfl
  · trivial

/-- **Generic necessity of destination writes for checked casts.** If some contents pass the
check and the discipline permits `writeDstReadSrc u` for a `U`-valid `u` that is not
`T`-valid, the checked cast is unsound. -/
theorem not_checkedSound_of_write_dst_read_src {P : Protocol B n} {T U : Validity B n}
    {u : Bytes B n} (hP : P (writeDstReadSrc u)) {m : Bytes B n} (hT : T m) (hU : U m)
    (hUu : U u) (hTu : ¬ T u) : ¬ CheckedSound P T U := by
  intro hs
  exact writeDstReadSrc_violates m hTu (hs m hT hU _ hP (writeDstReadSrc_wellTyped hUu))

/-- **Generic necessity of source writes for checked casts.** If some contents pass the
check and the discipline permits `writeSrcReadDst v` for a `T`-valid `v` that is not
`U`-valid, the checked cast is unsound. -/
theorem not_checkedSound_of_write_src_read_dst {P : Protocol B n} {T U : Validity B n}
    {v : Bytes B n} (hP : P (writeSrcReadDst v)) {m : Bytes B n} (hT : T m) (hU : U m)
    (hTv : T v) (hUv : ¬ U v) : ¬ CheckedSound P T U := by
  intro hs
  have h := hs m hT hU _ hP (writeSrcReadDst_wellTyped hTv)
  exact hUv h.1

/-- Invariant tool for checked value transmutes (only the destination view acts). -/
theorem checkedSound_value_of_invariant {T U : Validity B n} (I : Bytes B n → Prop)
    (hinit : ∀ m, T m → U m → I m) (hread : ∀ m, I m → U m) (hwrite : ∀ v, U v → I v) :
    CheckedSound valueProtocol T U := by
  apply checkedSound_of_invariant I hinit
  intro tr htr op hop
  have hs := htr op hop
  cases op with
  | read s => cases s
              · simp [Op.side] at hs
              · exact hread
  | write s v => cases s
                 · simp [Op.side] at hs
                 · exact hwrite v

/-- Invariant tool for checked shared casts without interior mutability (reads only). -/
theorem checkedSound_shared_of_invariant {T U : Validity B n} (I : Bytes B n → Prop)
    (hinit : ∀ m, T m → U m → I m) (hsrc : ∀ m, I m → T m) (hdst : ∀ m, I m → U m) :
    CheckedSound sharedProtocol T U := by
  apply checkedSound_of_invariant I hinit
  intro tr htr op hop
  have hs := htr op hop
  cases op with
  | read s => cases s
              · exact hsrc
              · exact hdst
  | write s v => exact False.elim hs

/-- Invariant tool for checked shared casts with interior mutability. -/
theorem checkedSound_sharedIM_of_invariant {srcWrites dstWrites : Bool} {T U : Validity B n}
    (I : Bytes B n → Prop)
    (hinit : ∀ m, T m → U m → I m) (hsrc : ∀ m, I m → T m) (hdst : ∀ m, I m → U m)
    (hwsrc : srcWrites = true → ∀ v, T v → I v)
    (hwdst : dstWrites = true → ∀ v, U v → I v) :
    CheckedSound (sharedIMProtocol srcWrites dstWrites) T U := by
  apply checkedSound_of_invariant I hinit
  intro tr htr op hop
  have hs := htr op hop
  cases op with
  | read s => cases s
              · exact hsrc
              · exact hdst
  | write s v => cases s
                 · exact hwsrc hs v
                 · exact hwdst hs v

end Toy.Transmute
