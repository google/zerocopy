import ToyBackward.Translate

/-!
# The aliasing discipline and liveness-respecting region ends

* `AliasingDiscipline P` — the safety contract of `as_mut` in this fragment, restricted to
  ordering: every use of a reference created by `asMut p` happens before the next access to the
  cell `p` by any other path (a raw read/write of `p`, or a new `asMut p`). It says nothing about
  reference *scoping*: a program that uses a reference name no earlier `asMut` created satisfies it
  (and is stuck in every semantics of this package).
* `EndsAfterCreation`, `EndsAfterLastUse`, `EndsAfterLastWrite`, `EndsByNextOwnerAccess`,
  `EndsByProgramEnd` — separate conditions on a `Placement` of region ends: "after the region's
  creation", "after the last use (or write) through the reference", "no later than the owner's
  next access" (the owner being the cell, reached through the raw pointer), and "no later than the
  end of the program".

All quantifiers range over program indices `< P.length`; the bounds are implied by the
`Bool` conditions and are written out only so that the properties are decidable on concrete
programs.
-/

namespace Toy.Backward

/-- Statement reads or writes through reference `r`. -/
def Stmt.usesRef (r : Nat) : Stmt → Bool
  | .read _ r' => r' == r
  | .write r' _ => r' == r
  | _ => false

/-- Statement writes through reference `r`. -/
def Stmt.writesRef (r : Nat) : Stmt → Bool
  | .write r' _ => r' == r
  | _ => false

/-- Statement accesses the cell `p` other than through an existing reference:
`asMut p`, `rawRead _ p`, or `rawWrite p _`. -/
def Stmt.touchesOwner (p : Ptr) : Stmt → Bool
  | .asMut q => q == p
  | .rawRead _ q => q == p
  | .rawWrite q _ => q == p
  | _ => false

/-- `usesAt P j i`: statement `j` of `P` reads or writes through the reference created at `i`. -/
def usesAt (P : Prog) (j i : Nat) : Bool :=
  match P[j]? with
  | some c => c.usesRef i
  | none => false

/-- `writesAt P j i`: statement `j` of `P` writes through the reference created at `i`. -/
def writesAt (P : Prog) (j i : Nat) : Bool :=
  match P[j]? with
  | some c => c.writesRef i
  | none => false

/-- `ownerAccessAfter P i k`: statement `i` is `asMut p`, `i < k`, and statement `k` accesses the
cell `p` by another path (the *owner* — the raw pointer — accesses the cell again). -/
def ownerAccessAfter (P : Prog) (i k : Nat) : Bool :=
  match P[i]?, P[k]? with
  | some (.asMut p), some c => decide (i < k) && c.touchesOwner p
  | _, _ => false

/-- **Aliasing discipline.** Every use of the reference created at `i` precedes every later owner
access to its cell. This paraphrases the `as_mut` safety requirement (while the returned reference
is in use, the memory is not accessed through any other pointer), specialised to this fragment and
to *uses* of the reference rather than its existence. It is a property of the program only, not of
any translation. It does **not** check reference scoping (that every used reference name is an
earlier `asMut`): ill-scoped programs such as `[read 0 0]` satisfy it and are stuck in every
semantics of this package. -/
def AliasingDiscipline (P : Prog) : Prop :=
  ∀ i, i < P.length → ∀ j, j < P.length → ∀ k, k < P.length →
    usesAt P j i = true → ownerAccessAfter P i k = true → j < k

/-- **Region `i` ends after its creation**: its backward call is scheduled strictly after the
`asMut` statement that creates it. -/
def EndsAfterCreation (P : Prog) (π : Placement) : Prop :=
  ∀ i, i < P.length → isRegion P i = true → i < π i

/-- **Region `i` ends after its last use** (read or write) through its reference: every statement
that uses the reference precedes the region's backward call. (Says nothing about regions without
uses; see `EndsAfterCreation`.) -/
def EndsAfterLastUse (P : Prog) (π : Placement) : Prop :=
  ∀ i, i < P.length → isRegion P i = true →
    ∀ j, j < P.length → usesAt P j i = true → j < π i

/-- **Region `i` ends after its last write** through its reference (reads may follow the end). -/
def EndsAfterLastWrite (P : Prog) (π : Placement) : Prop :=
  ∀ i, i < P.length → isRegion P i = true →
    ∀ j, j < P.length → writesAt P j i = true → j < π i

/-- **Region `i` ends no later than the owner's next access** to its cell: for every later
statement `k` that accesses the cell by another path, the backward call of `i` is scheduled
at or before `k` (backward calls scheduled at `k` run before statement `k`). -/
def EndsByNextOwnerAccess (P : Prog) (π : Placement) : Prop :=
  ∀ i, i < P.length → ∀ k, k < P.length → ownerAccessAfter P i k = true → π i ≤ k

/-- **Region `i` ends no later than the end of the program**, where the final heap is observed
(the final observation is the owner's last access). -/
def EndsByProgramEnd (P : Prog) (π : Placement) : Prop :=
  ∀ i, i < P.length → isRegion P i = true → π i ≤ P.length

instance (P : Prog) : Decidable (AliasingDiscipline P) := by
  unfold AliasingDiscipline; infer_instance
instance (P : Prog) (π : Placement) : Decidable (EndsAfterCreation P π) := by
  unfold EndsAfterCreation; infer_instance
instance (P : Prog) (π : Placement) : Decidable (EndsAfterLastUse P π) := by
  unfold EndsAfterLastUse; infer_instance
instance (P : Prog) (π : Placement) : Decidable (EndsAfterLastWrite P π) := by
  unfold EndsAfterLastWrite; infer_instance
instance (P : Prog) (π : Placement) : Decidable (EndsByNextOwnerAccess P π) := by
  unfold EndsByNextOwnerAccess; infer_instance
instance (P : Prog) (π : Placement) : Decidable (EndsByProgramEnd P π) := by
  unfold EndsByProgramEnd; infer_instance

/-! ## Basic facts -/

theorem ownerAccessAfter_lt {P : Prog} {i k : Nat} (h : ownerAccessAfter P i k = true) : i < k := by
  unfold ownerAccessAfter at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  · simp at h

theorem ownerAccessAfter_isRegion {P : Prog} {i k : Nat} (h : ownerAccessAfter P i k = true) :
    isRegion P i = true := by
  unfold ownerAccessAfter at h
  unfold isRegion
  split at h
  · rename_i p c hi hk
    rw [hi]
  · simp at h

theorem usesAt_of_writesAt {P : Prog} {j i : Nat} (h : writesAt P j i = true) : usesAt P j i = true := by
  unfold writesAt at h
  unfold usesAt
  split at h
  · rename_i c hc
    cases c <;> simp_all [Stmt.writesRef, Stmt.usesRef]
  · simp at h

theorem lt_length_of_usesAt {P : Prog} {j i : Nat} (h : usesAt P j i = true) : j < P.length := by
  unfold usesAt at h
  split at h
  · rename_i c hc
    exact (List.getElem?_eq_some_iff.mp hc).1
  · simp at h

/-! ## Searching for first/last indices -/

/-- Least `j < n` with `f j`, or `n` if there is none. -/
def firstBelow (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let m := firstBelow f n
    if m < n then m else if f n then n else n + 1

/-- Largest `j < n` with `f j`, or the default `d` if there is none. -/
def lastBelow (f : Nat → Bool) (d : Nat) : Nat → Nat
  | 0 => d
  | n + 1 => if f n then n else lastBelow f d n

theorem firstBelow_le (f : Nat → Bool) (n : Nat) : firstBelow f n ≤ n := by
  induction n with
  | zero => simp [firstBelow]
  | succ n ih =>
    simp only [firstBelow]
    split
    · omega
    · split <;> omega

theorem firstBelow_spec (f : Nat → Bool) (n : Nat) (h : firstBelow f n < n) :
    f (firstBelow f n) = true := by
  induction n with
  | zero => simp [firstBelow] at h
  | succ n ih =>
    simp only [firstBelow] at h ⊢
    split
    · rename_i hm
      exact ih hm
    · rename_i hm
      split
      · assumption
      · rename_i hf
        simp only [hm, ↓reduceIte, hf, Bool.false_eq_true] at h
        omega

theorem firstBelow_min (f : Nat → Bool) (n j : Nat) (hj : j < n) (hf : f j = true) :
    firstBelow f n ≤ j := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [firstBelow]
    split
    · rename_i hm
      by_cases hjn : j < n
      · exact ih hjn
      · omega
    · rename_i hm
      have hle := firstBelow_le f n
      by_cases hjn : j < n
      · have := ih hjn
        omega
      · have hjeq : j = n := by omega
        subst hjeq
        simp [hf]

theorem le_lastBelow (f : Nat → Bool) (d n j : Nat) (hj : j < n) (hf : f j = true) :
    j ≤ lastBelow f d n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [lastBelow]
    split
    · omega
    · rename_i hfn
      by_cases hjn : j < n
      · exact ih hjn
      · have hjeq : j = n := by omega
        subst hjeq
        simp_all

theorem lastBelow_cases (f : Nat → Bool) (d n : Nat) :
    lastBelow f d n = d ∨ (lastBelow f d n < n ∧ f (lastBelow f d n) = true) := by
  induction n with
  | zero => simp [lastBelow]
  | succ n ih =>
    simp only [lastBelow]
    split
    · rename_i hfn
      exact Or.inr ⟨by omega, hfn⟩
    · rcases ih with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨by omega, h2⟩

/-! ## Two canonical placements -/

/-- **Lazy placement**: end region `i` exactly at the owner's next access to its cell, or at the end
of the program if there is none ("end a borrow only when the owner needs the value back"). -/
def lazyPlacement (P : Prog) : Placement :=
  fun i => firstBelow (ownerAccessAfter P i) P.length

/-- **Eager placement**: end region `i` immediately after the later of its creation and its last
use, `max i (last use) + 1` (so after its last use if that use follows the creation, and right
after its creation if the region has no use after it). Uses that precede the creation (a scoping
error) do not pull the end before the creation. Approximately where non-lexical lifetimes would
end the region. -/
def eagerPlacement (P : Prog) : Placement :=
  fun i => max i (lastBelow (fun j => usesAt P j i) i P.length) + 1

theorem lazyPlacement_endsByNextOwnerAccess (P : Prog) :
    EndsByNextOwnerAccess P (lazyPlacement P) :=
  fun i _ k hk ho => firstBelow_min (ownerAccessAfter P i) P.length k hk ho

theorem lazyPlacement_endsByProgramEnd (P : Prog) : EndsByProgramEnd P (lazyPlacement P) :=
  fun _ _ _ => firstBelow_le _ _

theorem lazyPlacement_endsAfterCreation (P : Prog) : EndsAfterCreation P (lazyPlacement P) := by
  intro i hi _
  simp only [lazyPlacement]
  by_cases hm : firstBelow (ownerAccessAfter P i) P.length < P.length
  · exact ownerAccessAfter_lt (firstBelow_spec _ _ hm)
  · have hle := firstBelow_le (ownerAccessAfter P i) P.length
    omega

theorem lazyPlacement_endsAfterLastUse_of_aliasingDiscipline {P : Prog}
    (had : AliasingDiscipline P) : EndsAfterLastUse P (lazyPlacement P) := by
  intro i hi _ j hj hu
  simp only [lazyPlacement]
  by_cases hm : firstBelow (ownerAccessAfter P i) P.length < P.length
  · exact had i hi j hj _ hm hu (firstBelow_spec _ _ hm)
  · have hle := firstBelow_le (ownerAccessAfter P i) P.length
    omega

theorem eagerPlacement_endsAfterCreation (P : Prog) : EndsAfterCreation P (eagerPlacement P) := by
  intro i _ _
  simp only [eagerPlacement]
  omega

theorem eagerPlacement_endsAfterLastUse (P : Prog) : EndsAfterLastUse P (eagerPlacement P) := by
  intro i _ _ j hj hu
  simp only [eagerPlacement]
  have := le_lastBelow (fun j => usesAt P j i) i P.length j hj hu
  omega

theorem eagerPlacement_endsByProgramEnd (P : Prog) : EndsByProgramEnd P (eagerPlacement P) := by
  intro i hi _
  simp only [eagerPlacement]
  rcases lastBelow_cases (fun j => usesAt P j i) i P.length with hL | ⟨hL1, _⟩
  · rw [hL]; omega
  · omega

theorem eagerPlacement_endsByNextOwnerAccess_of_aliasingDiscipline {P : Prog}
    (had : AliasingDiscipline P) : EndsByNextOwnerAccess P (eagerPlacement P) := by
  intro i hi k hk ho
  simp only [eagerPlacement]
  have h1 := ownerAccessAfter_lt ho
  rcases lastBelow_cases (fun j => usesAt P j i) i P.length with hL | ⟨hL1, hL2⟩
  · rw [hL]; omega
  · have h2 := had i hi _ hL1 k hk hL2 ho
    omega

/-! ## Derivable hypotheses -/

/-- The aliasing discipline is **derivable** from two placement conditions: if some placement
ends every region after its last use and no later than the owner's next access, every use precedes
every later owner access. (`EndsAfterCreation` and `EndsByProgramEnd` are not needed.) -/
theorem aliasingDiscipline_of_endsAfterLastUse_of_endsByNextOwnerAccess {P : Prog} {π : Placement}
    (hu : EndsAfterLastUse P π) (ho : EndsByNextOwnerAccess P π) : AliasingDiscipline P := by
  intro i hi j hj k hk huse hown
  have hreg := ownerAccessAfter_isRegion hown
  have h1 := hu i hi hreg j hj huse
  have h2 := ho i hi k hk hown
  omega

/-- Ending after the last use implies ending after the last write. -/
theorem endsAfterLastWrite_of_endsAfterLastUse {P : Prog} {π : Placement}
    (hu : EndsAfterLastUse P π) : EndsAfterLastWrite P π :=
  fun i hi hreg j hj hw => hu i hi hreg j hj (usesAt_of_writesAt hw)

/-- **Liveness-respecting placement**: every region ends after its creation, after its last use,
no later than the owner's next access to its cell, and no later than the end of the program. A
named conjunction of four separate conditions, for prose and for the characterization below; the
main theorems list the conditions separately. -/
def RespectsLiveness (P : Prog) (π : Placement) : Prop :=
  EndsAfterCreation P π ∧ EndsAfterLastUse P π ∧ EndsByNextOwnerAccess P π ∧ EndsByProgramEnd P π

instance (P : Prog) (π : Placement) : Decidable (RespectsLiveness P π) := by
  unfold RespectsLiveness; infer_instance

theorem lazyPlacement_respectsLiveness_of_aliasingDiscipline {P : Prog}
    (had : AliasingDiscipline P) : RespectsLiveness P (lazyPlacement P) :=
  ⟨lazyPlacement_endsAfterCreation P, lazyPlacement_endsAfterLastUse_of_aliasingDiscipline had,
    lazyPlacement_endsByNextOwnerAccess P, lazyPlacement_endsByProgramEnd P⟩

theorem eagerPlacement_respectsLiveness_of_aliasingDiscipline {P : Prog}
    (had : AliasingDiscipline P) : RespectsLiveness P (eagerPlacement P) :=
  ⟨eagerPlacement_endsAfterCreation P, eagerPlacement_endsAfterLastUse P,
    eagerPlacement_endsByNextOwnerAccess_of_aliasingDiscipline had, eagerPlacement_endsByProgramEnd P⟩

/-- **Characterization (witnesses exposed).** For every program, the aliasing discipline holds
iff the lazy placement is liveness-respecting, iff the eager placement is liveness-respecting, iff
some placement is liveness-respecting. For the right-to-left directions only `EndsAfterLastUse`
and `EndsByNextOwnerAccess` are used
(`aliasingDiscipline_of_endsAfterLastUse_of_endsByNextOwnerAccess`). -/
theorem aliasingDiscipline_iff_respectsLiveness_lazyPlacement (P : Prog) :
    (AliasingDiscipline P ↔ RespectsLiveness P (lazyPlacement P)) ∧
    (AliasingDiscipline P ↔ RespectsLiveness P (eagerPlacement P)) ∧
    (AliasingDiscipline P ↔ ∃ π, RespectsLiveness P π) :=
  ⟨⟨lazyPlacement_respectsLiveness_of_aliasingDiscipline,
      fun ⟨_, hu, ho, _⟩ => aliasingDiscipline_of_endsAfterLastUse_of_endsByNextOwnerAccess hu ho⟩,
    ⟨eagerPlacement_respectsLiveness_of_aliasingDiscipline,
      fun ⟨_, hu, ho, _⟩ => aliasingDiscipline_of_endsAfterLastUse_of_endsByNextOwnerAccess hu ho⟩,
    ⟨fun had => ⟨_, lazyPlacement_respectsLiveness_of_aliasingDiscipline had⟩,
      fun ⟨_, _, hu, ho, _⟩ => aliasingDiscipline_of_endsAfterLastUse_of_endsByNextOwnerAccess hu ho⟩⟩

/-! ## Pure backward functions are never-ending regions -/

/-- A placement that never schedules any backward call of `P`. -/
def neverEndPlacement (P : Prog) : Placement := fun _ => P.length + 1

theorem backsAt_neverEndPlacement (P : Prog) (k : Nat) (hk : k ≤ P.length) :
    backsAt P (neverEndPlacement P) k = [] := by
  simp only [backsAt, neverEndPlacement, List.map_eq_nil_iff, List.filter_eq_nil_iff,
    Bool.and_eq_true, beq_iff_eq, not_and]
  intro i _ _ h
  omega

theorem translateFrom_neverEndPlacement (P : Prog) :
    ∀ (cs : List Stmt) (k : Nat), k + cs.length ≤ P.length →
      translateFrom P (neverEndPlacement P) k cs = translatePureBack k cs := by
  intro cs
  induction cs with
  | nil => intro k _; rfl
  | cons c cs ih =>
    intro k hk
    simp only [List.length_cons] at hk
    simp only [translateFrom, translatePureBack]
    rw [backsAt_neverEndPlacement P k (by omega), ih (k + 1) (by omega)]
    rfl

/-- The pure-backward translation is the effectful translation with a placement that never ends
any region. -/
theorem translate_neverEndPlacement (P : Prog) :
    translate P (neverEndPlacement P) = translatePureBack 0 P := by
  simp only [translate]
  rw [translateFrom_neverEndPlacement P P 0 (by omega),
    backsAt_neverEndPlacement P P.length (Nat.le_refl _), List.append_nil]

theorem pureBackSem_eq_effSem_neverEndPlacement (P : Prog) (h : Heap) :
    pureBackSem P h = effSem P (neverEndPlacement P) h := by
  simp only [pureBackSem, effSem, translate_neverEndPlacement]

/-! ## Stateless targets cannot observe backward calls -/

/-- Whether a target statement is a backward call. -/
def TStmt.isBack : TStmt → Bool
  | .back _ => true
  | _ => false

theorem trStmt_isBack (k : Nat) (c : Stmt) : (trStmt k c).isBack = false := by
  cases c <;> rfl

theorem backsAt_filter_not_isBack (P : Prog) (π : Placement) (k : Nat) :
    (backsAt P π k).filter (fun c => !c.isBack) = [] := by
  simp [backsAt, List.filter_map, Function.comp_def, TStmt.isBack]

theorem translateFrom_filter_not_isBack (P : Prog) (π : Placement) :
    ∀ (cs : List Stmt) (k : Nat),
      (translateFrom P π k cs).filter (fun c => !c.isBack) = translatePureBack k cs := by
  intro cs
  induction cs with
  | nil => intro k; rfl
  | cons c cs ih =>
    intro k
    simp only [translateFrom, translatePureBack, List.filter_append, backsAt_filter_not_isBack,
      List.nil_append, List.filter_cons, trStmt_isBack, Bool.not_false, ↓reduceIte, ih]

/-- Erasing the backward calls from any effectful translation gives the pure-backward translation. -/
theorem translate_filter_not_isBack (P : Prog) (π : Placement) :
    (translate P π).filter (fun c => !c.isBack) = translatePureBack 0 P := by
  simp only [translate, List.filter_append, translateFrom_filter_not_isBack,
    backsAt_filter_not_isBack, List.append_nil]

theorem sstep_back_eq {F : Ptr → Option Int} {B : Ptr → Int → Bool} {s s₁ : SState} {i : Nat}
    (h : sstep F B s (.back i) = some s₁) : s₁ = s := by
  simp only [sstep] at h
  split at h
  · split at h
    · exact (Option.some.inj h).symm
    · cases h
  · cases h

/-- In a stateless target a successful run is unchanged by deleting its backward calls: they can
only fail, never influence later values. -/
theorem srun_filter_not_isBack (F : Ptr → Option Int) (B : Ptr → Int → Bool) :
    ∀ (L : List TStmt) (s s' : SState), srun F B L s = some s' →
      srun F B (L.filter (fun c => !c.isBack)) s = some s' := by
  intro L
  induction L with
  | nil => intro s s' h; exact h
  | cons c cs ih =>
    intro s s' h
    simp only [srun] at h
    split at h
    · rename_i s₁ hs
      cases c with
      | back i =>
        have := sstep_back_eq hs
        subst this
        rw [List.filter_cons]
        simp only [TStmt.isBack, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact ih _ _ h
      | _ =>
        rw [List.filter_cons]
        simp only [TStmt.isBack, Bool.not_false, ↓reduceIte, srun, hs]
        exact ih _ _ h
    · cases h

end Toy.Backward
