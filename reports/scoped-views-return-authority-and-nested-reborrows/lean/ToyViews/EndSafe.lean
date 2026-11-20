import ToyViews.EndSafeLemmas

/-!
# Result 2: ending a view under return authority preserves the safety invariant

The safety invariant is the loan-tree invariant `LoanTreeInv` (seven structural laws), which
implies write exclusivity (`writeExclusive_of_loanTree_laws`), together with the step property
`NoResurrection`. Of the seven laws, the two global ones (`ParentLt`, `RootsDisjoint`) are preserved
by every raw end (`endRaw_preserves_parentLt`, `endRaw_preserves_rootsDisjoint`); preservation of
the five tree-local laws (`LocalLoanLaws`) is what return authority buys.
-/

namespace Toy.Views

/-- **R2a (main).** If a state satisfies the five tree-local laws and view `c` has return
authority (no active proper descendant of `c` covers a cell of `c`), then the raw end of `c` (for
any bytes `r` handed back) yields a state that again satisfies the five tree-local laws, and the
step resurrects no access under an active descendant. Neither `ParentLt` nor `RootsDisjoint` is
assumed. -/
theorem endRaw_preserves_localLoanLaws_and_noResurrection_of_returnAuthority
    {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hpc : ParentCoversActive s) (hecl : ExclChildLoaned s)
    (hscb : SharedChildBelowOwn s) (hscs : SharedChildrenShared s) (hdc : DepthCounts s)
    (hauth : ReturnAuthority s c) (hend : endRaw s c r = some s') :
    LocalLoanLaws s' ∧ NoResurrection s s' :=
  ProofLemmas.endRaw_preserves_localLoanLaws_and_noResurrection ⟨hpc, hecl, hscb, hscs, hdc⟩
    hauth hend

/-- **R2a, full-invariant form (corollary of R2a and the two frame lemmas).** Under the full
loan-tree invariant and return authority, the raw end of `c` preserves the full invariant and
resurrects nothing. -/
theorem endRaw_preserves_loanTreeInv_and_noResurrection_of_returnAuthority
    {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hinv : LoanTreeInv s) (hauth : ReturnAuthority s c) (hend : endRaw s c r = some s') :
    LoanTreeInv s' ∧ NoResurrection s s' := by
  have ⟨hl, hnr⟩ := endRaw_preserves_localLoanLaws_and_noResurrection_of_returnAuthority
    hinv.parentCoversActive hinv.exclChildLoaned hinv.sharedChildBelowOwn
    hinv.sharedChildrenShared hinv.depthCounts hauth hend
  exact ⟨⟨endRaw_preserves_parentLt hinv.parentLt hend, hl.parentCoversActive,
    hl.exclChildLoaned, hl.sharedChildBelowOwn, hl.sharedChildrenShared, hl.depthCounts,
    endRaw_preserves_rootsDisjoint hinv.rootsDisjoint hend⟩, hnr⟩

/-- **R2b (derivable safety).** The seven loan-tree laws imply write exclusivity. (So write
exclusivity need not be assumed separately anywhere in this package.) -/
theorem writeExclusive_of_loanTree_laws {s : State}
    (hlt : ParentLt s) (hpc : ParentCoversActive s) (hecl : ExclChildLoaned s)
    (hscb : SharedChildBelowOwn s) (hscs : SharedChildrenShared s) (hdc : DepthCounts s)
    (hrd : RootsDisjoint s) :
    WriteExclusive s :=
  ProofLemmas.writeExclusive_of_loanTree_laws_proved hlt hpc hecl hscb hscs hdc hrd

/-- **R2c (corollary of R2a, the two frame lemmas, and R2b).** Under the seven loan-tree laws and
return authority, the raw end of `c` leaves a write-exclusive state. Each of the seven laws is
needed (the counterexamples `Ex.endRaw_inv_needs_*` and `Ex.endRaw_writeExclusive_needs_*` start
from write-exclusive states). -/
theorem endRaw_writeExclusive_of_loanTree_laws_of_returnAuthority
    {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hlt : ParentLt s) (hpc : ParentCoversActive s) (hecl : ExclChildLoaned s)
    (hscb : SharedChildBelowOwn s) (hscs : SharedChildrenShared s) (hdc : DepthCounts s)
    (hrd : RootsDisjoint s)
    (hauth : ReturnAuthority s c) (hend : endRaw s c r = some s') :
    WriteExclusive s' := by
  have ⟨hi, _⟩ := endRaw_preserves_loanTreeInv_and_noResurrection_of_returnAuthority
    ⟨hlt, hpc, hecl, hscb, hscs, hdc, hrd⟩ hauth hend
  exact writeExclusive_of_loanTree_laws hi.parentLt hi.parentCoversActive hi.exclChildLoaned
    hi.sharedChildBelowOwn hi.sharedChildrenShared hi.depthCounts hi.rootsDisjoint

/-- **R2d (a local check suffices for return authority).** Under the three tree-local laws
`ParentCoversActive`, `ExclChildLoaned` and `DepthCounts`, if view `c` holds every cell it covers
as an `own` cell at its own mode baseline (`LocalReturnCheck`: it has lent nothing onward), then
`c` has return authority. So in this model, where every reborrow is an explicit view, return
authority can be established by inspecting only `c`'s own cells, without traversing `c`'s
descendants. The local check alone does not suffice: each of the three laws is needed
(`Ex.localCheck_needs_parentCoversActive`, `Ex.localCheck_needs_exclChildLoaned`,
`Ex.localCheck_needs_depthCounts`). -/
theorem returnAuthority_of_localReturnCheck_of_parentCoversActive_exclChildLoaned_depthCounts
    {s : State} {c : ViewId}
    (hpc : ParentCoversActive s) (hecl : ExclChildLoaned s) (hdc : DepthCounts s)
    (hloc : LocalReturnCheck s c) : ReturnAuthority s c :=
  ProofLemmas.returnAuthority_of_localReturnCheck_proved hpc hecl hdc hloc

/-- **R2d, end form (corollary with R2a).** Under all five tree-local laws (the three above plus
`SharedChildBelowOwn` and `SharedChildrenShared`, which return authority does not need but the end
step does: `Ex.localCheck_end_needs_sharedChildBelowOwn`,
`Ex.localCheck_end_needs_sharedChildrenShared`), the raw end of a view that passes the local return
check, when it succeeds, preserves the five tree-local laws and resurrects nothing. -/
theorem endRaw_preserves_localLoanLaws_and_noResurrection_of_localReturnCheck
    {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hpc : ParentCoversActive s) (hecl : ExclChildLoaned s)
    (hscb : SharedChildBelowOwn s) (hscs : SharedChildrenShared s) (hdc : DepthCounts s)
    (hloc : LocalReturnCheck s c) (hend : endRaw s c r = some s') :
    LocalLoanLaws s' ∧ NoResurrection s s' :=
  endRaw_preserves_localLoanLaws_and_noResurrection_of_returnAuthority hpc hecl hscb hscs hdc
    (returnAuthority_of_localReturnCheck_of_parentCoversActive_exclChildLoaned_depthCounts
      hpc hecl hdc hloc) hend

namespace Ex

/-! ## Non-vacuity -/

/-- **R2 non-vacuity (nested).** In the nested state `s2` all laws hold, the innermost view `C`
has return authority, and its raw end succeeds. -/
theorem endRaw_inv_nonvacuous_nested (r : Addr → Byte) :
    LoanTreeInv s2 ∧ ReturnAuthority s2 2 ∧ endRaw s2 2 r = some (s2e (r 0)) :=
  ⟨by decide, returnAuthority_s2_C, rfl⟩

/-- **R2 non-vacuity (shared, two readers).** In `u2` all laws hold, `B` has return authority,
and its raw end succeeds; `A` stays read-only because `C` still reads. -/
theorem endRaw_inv_nonvacuous_shared (r : Addr → Byte) :
    LoanTreeInv u2 ∧ ReturnAuthority u2 1 ∧ endRaw u2 1 r = some u2e ∧ LoanTreeInv u2e ∧
      u2e.canWrite 0 0 = false :=
  ⟨by decide, returnAuthority_of_closed [] (by decide) (by decide), rfl, by decide, by decide⟩

/-- **R2b non-vacuity.** The two-address state `w2` (one exclusive and one shared loan) satisfies
all seven laws. -/
theorem loanTree_laws_nonvacuous : LoanTreeInv w2 ∧ WriteExclusive w2 := by decide

/-! ## Counterexample states for the seven laws (each violates exactly one law)

Each state below is write-exclusive and satisfies the other six laws; ending the indicated view
under return authority breaks write exclusivity (and hence the invariant). -/

/-- Violates only `ParentLt`: `C` is its own parent (an unrooted shared reader). End `B`. -/
def cxParentLt : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] },
  { parent := some 2, mode := .shared, active := true, cells := [some (.own 2 0)] }]⟩

/-- Violates only `ParentCoversActive`: `Y` (id 4) is active under the retired `X` (id 3). End
`B`. -/
def cxParentCoversActive : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.loaned 2)] },
  { parent := some 1, mode := .excl, active := false, cells := [some (.own 0 0)] },
  { parent := some 0, mode := .excl, active := false, cells := [some (.loaned 4)] },
  { parent := some 3, mode := .excl, active := true, cells := [some (.own 0 0)] }]⟩

/-- Violates only `ExclChildLoaned`: `D` (id 3) is an active exclusive child of `A` but `A`'s cell
records the loan to `B`. End `B`. -/
def cxExclChildLoaned : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.loaned 2)] },
  { parent := some 1, mode := .excl, active := false, cells := [some (.own 0 0)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.own 0 0)] }]⟩

/-- Violates only `SharedChildBelowOwn`: `D` (id 3) is an active shared child of `A` while `A`'s
cell is loaned to `B`. End `B`. -/
def cxSharedChildBelowOwn : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.loaned 2)] },
  { parent := some 1, mode := .excl, active := false, cells := [some (.own 0 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] }]⟩

/-- Violates only `SharedChildrenShared`: the shared view `B` has an active exclusive child `C`.
End `C`. -/
def cxSharedChildrenShared : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.loaned 2)] },
  { parent := some 1, mode := .excl, active := true, cells := [some (.loaned 3)] },
  { parent := some 2, mode := .excl, active := false, cells := [some (.own 0 0)] }]⟩

/-- Violates only `DepthCounts`: `A` is at depth `1` but has two active shared children. End
`B`. -/
def cxDepthCounts : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] }]⟩

/-- Violates only `RootsDisjoint`: a second active (read-only) root `R` covers `A`'s cell. End
`B` (id 2). -/
def cxRootsDisjoint : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 0)] },
  { parent := none, mode := .shared, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] }]⟩

/-! ## Tightness counterexamples for R2a and R2c (canonical form)

Each theorem below exhibits one of the counterexample states: the named law fails, all other
hypotheses of R2a (for the five local laws) and of R2c (for all seven laws) hold — the other laws,
return authority, and success of the raw end — and the pre-state is even write-exclusive, while the
post-state is not write-exclusive (R2c's conclusion fails). For the five local laws, R2a's
conclusion fails as well, and not merely because the dropped law is still false afterwards: the
step itself breaks `NoResurrection` or a law that held before. For `ParentLt` and `RootsDisjoint`
the step breaks write exclusivity while all five local laws and `NoResurrection` survive: these two
laws are needed for R2b/R2c, not for R2a. -/

theorem endRaw_writeExclusive_needs_parentLt :
    ¬ ParentLt cxParentLt ∧ ParentCoversActive cxParentLt ∧ ExclChildLoaned cxParentLt ∧
    SharedChildBelowOwn cxParentLt ∧ SharedChildrenShared cxParentLt ∧ DepthCounts cxParentLt ∧
    RootsDisjoint cxParentLt ∧ WriteExclusive cxParentLt ∧ ReturnAuthority cxParentLt 1 ∧
    ∃ s', endRaw cxParentLt 1 (fun _ => 0) = some s' ∧ LocalLoanLaws s' ∧
      NoResurrection cxParentLt s' ∧ ¬ WriteExclusive s' :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   returnAuthority_of_closed [] (by decide) (by decide), _, rfl, by decide,
   noResurrection_of_closed (fun u => if u = 0 then [1] else if u = 2 then [2] else [])
     (by decide) (by decide), by decide⟩

theorem endRaw_inv_needs_parentCoversActive :
    ParentLt cxParentCoversActive ∧ ¬ ParentCoversActive cxParentCoversActive ∧
    ExclChildLoaned cxParentCoversActive ∧ SharedChildBelowOwn cxParentCoversActive ∧
    SharedChildrenShared cxParentCoversActive ∧ DepthCounts cxParentCoversActive ∧
    RootsDisjoint cxParentCoversActive ∧ WriteExclusive cxParentCoversActive ∧
    ReturnAuthority cxParentCoversActive 1 ∧
    ∃ s', endRaw cxParentCoversActive 1 (fun _ => 0) = some s' ∧
      ¬ NoResurrection cxParentCoversActive s' ∧ ¬ LocalLoanLaws s' ∧ ¬ WriteExclusive s' :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   returnAuthority_of_closed [2] (by decide) (by decide), _, rfl,
   fun h => absurd (h 0 (by decide) 0 (by decide) (by decide) 4
     (.step (x := 3) rfl (.child rfl)) rfl) (by decide), by decide, by decide⟩

theorem endRaw_inv_needs_exclChildLoaned :
    ParentLt cxExclChildLoaned ∧ ParentCoversActive cxExclChildLoaned ∧
    ¬ ExclChildLoaned cxExclChildLoaned ∧ SharedChildBelowOwn cxExclChildLoaned ∧
    SharedChildrenShared cxExclChildLoaned ∧ DepthCounts cxExclChildLoaned ∧
    RootsDisjoint cxExclChildLoaned ∧ WriteExclusive cxExclChildLoaned ∧
    ReturnAuthority cxExclChildLoaned 1 ∧
    ∃ s', endRaw cxExclChildLoaned 1 (fun _ => 0) = some s' ∧
      ¬ NoResurrection cxExclChildLoaned s' ∧ ¬ LocalLoanLaws s' ∧ ¬ WriteExclusive s' :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   returnAuthority_of_closed [2] (by decide) (by decide), _, rfl,
   fun h => absurd (h 0 (by decide) 0 (by decide) (by decide) 3 (.child rfl) rfl) (by decide),
   by decide, by decide⟩

theorem endRaw_inv_needs_sharedChildBelowOwn :
    ParentLt cxSharedChildBelowOwn ∧ ParentCoversActive cxSharedChildBelowOwn ∧
    ExclChildLoaned cxSharedChildBelowOwn ∧ ¬ SharedChildBelowOwn cxSharedChildBelowOwn ∧
    SharedChildrenShared cxSharedChildBelowOwn ∧ DepthCounts cxSharedChildBelowOwn ∧
    RootsDisjoint cxSharedChildBelowOwn ∧ WriteExclusive cxSharedChildBelowOwn ∧
    ReturnAuthority cxSharedChildBelowOwn 1 ∧
    ∃ s', endRaw cxSharedChildBelowOwn 1 (fun _ => 0) = some s' ∧
      ¬ DepthCounts s' ∧ ¬ LocalLoanLaws s' ∧ ¬ WriteExclusive s' :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   returnAuthority_of_closed [2] (by decide) (by decide), _, rfl, by decide, by decide, by decide⟩

theorem endRaw_inv_needs_sharedChildrenShared :
    ParentLt cxSharedChildrenShared ∧ ParentCoversActive cxSharedChildrenShared ∧
    ExclChildLoaned cxSharedChildrenShared ∧ SharedChildBelowOwn cxSharedChildrenShared ∧
    ¬ SharedChildrenShared cxSharedChildrenShared ∧ DepthCounts cxSharedChildrenShared ∧
    RootsDisjoint cxSharedChildrenShared ∧ WriteExclusive cxSharedChildrenShared ∧
    ReturnAuthority cxSharedChildrenShared 2 ∧
    ∃ s', endRaw cxSharedChildrenShared 2 (fun _ => 0) = some s' ∧
      ¬ DepthCounts s' ∧ ¬ LocalLoanLaws s' ∧ ¬ WriteExclusive s' :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   returnAuthority_of_closed [3] (by decide) (by decide), _, rfl, by decide, by decide, by decide⟩

theorem endRaw_inv_needs_depthCounts :
    ParentLt cxDepthCounts ∧ ParentCoversActive cxDepthCounts ∧ ExclChildLoaned cxDepthCounts ∧
    SharedChildBelowOwn cxDepthCounts ∧ SharedChildrenShared cxDepthCounts ∧
    ¬ DepthCounts cxDepthCounts ∧ RootsDisjoint cxDepthCounts ∧ WriteExclusive cxDepthCounts ∧
    ReturnAuthority cxDepthCounts 1 ∧
    ∃ s', endRaw cxDepthCounts 1 (fun _ => 0) = some s' ∧
      ¬ SharedChildBelowOwn s' ∧ ¬ LocalLoanLaws s' ∧ ¬ WriteExclusive s' :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   returnAuthority_of_closed [] (by decide) (by decide), _, rfl, by decide, by decide, by decide⟩

theorem endRaw_writeExclusive_needs_rootsDisjoint :
    ParentLt cxRootsDisjoint ∧ ParentCoversActive cxRootsDisjoint ∧
    ExclChildLoaned cxRootsDisjoint ∧ SharedChildBelowOwn cxRootsDisjoint ∧
    SharedChildrenShared cxRootsDisjoint ∧ DepthCounts cxRootsDisjoint ∧
    ¬ RootsDisjoint cxRootsDisjoint ∧ WriteExclusive cxRootsDisjoint ∧
    ReturnAuthority cxRootsDisjoint 2 ∧
    ∃ s', endRaw cxRootsDisjoint 2 (fun _ => 0) = some s' ∧ LocalLoanLaws s' ∧
      NoResurrection cxRootsDisjoint s' ∧ ¬ WriteExclusive s' :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   returnAuthority_of_closed [] (by decide) (by decide), _, rfl, by decide,
   noResurrection_of_closed (fun u => if u = 0 then [2] else []) (by decide) (by decide),
   by decide⟩

/-- Return authority is necessary (for R2a, the full-invariant corollary, and R2c): R1a's nested
state `s2` satisfies all seven laws, and ending `B` there (without authority) breaks the local
laws, the full invariant, write exclusivity, and no-resurrection. -/
theorem endRaw_inv_needs_returnAuthority :
    LoanTreeInv s2 ∧ ¬ ReturnAuthority s2 1 ∧
    ∃ s', endRaw s2 1 (fun _ => 0) = some s' ∧ ¬ LocalLoanLaws s' ∧ ¬ LoanTreeInv s' ∧
      ¬ WriteExclusive s' ∧ ¬ NoResurrection s2 s' :=
  ⟨by decide, not_returnAuthority_s2_B, _, rfl, by decide, by decide, by decide,
   not_noResurrection_s2_end_B⟩

/-- The local check is strictly stronger than return authority: in `aS0` (all seven laws hold) `B`
has return authority — its only child `C` is retired — but `B` still records the loan to `C`, so it
fails the local check. -/
theorem localReturnCheck_strictly_stronger_than_returnAuthority :
    LoanTreeInv aS0 ∧ ReturnAuthority aS0 1 ∧ ¬ LocalReturnCheck aS0 1 :=
  ⟨by decide, returnAuthority_of_closed [2] (by decide) (by decide), by decide⟩

/-! ## What the invariant and the end operation do not cover -/

/-- `byteIncoherent`: an exclusive root `A` at depth `1` with one shared child `B`; the two views
store different bytes for address `0`. -/
def byteIncoherent : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 42)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 99)] }]⟩

/-- `LoanTreeInv` and write exclusivity constrain permissions only: two concurrent readers of the
same address may read different bytes. -/
theorem loanTreeInv_allows_reader_byte_disagreement :
    LoanTreeInv byteIncoherent ∧ WriteExclusive byteIncoherent ∧
    read byteIncoherent 0 0 = some 42 ∧ read byteIncoherent 1 0 = some 99 := by decide

/-- `e2`: `s1` after `B` borrows the *empty* address list: an active exclusive child `C` of `B`
that covers no address. -/
def e2 : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := some 1, mode := .excl, active := true, cells := [none] }]⟩

/-- `e3 b`: ending `B` in `e2`, `A` restored to byte `b`; `C` is still active. -/
def e3 (b : Byte) : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 0 b)] },
  { parent := some 0, mode := .excl, active := false, cells := [some (.own 0 0)] },
  { parent := some 1, mode := .excl, active := true, cells := [none] }]⟩

/-- `ReturnAuthority` is cell-wise: `B` may be ended in `e2` although its child `C` is active
(`C` covers no cell). The result satisfies all seven laws, and `C` stays active under the retired
`B`. -/
theorem returnAuthority_ignores_active_empty_descendants (r : Addr → Byte) :
    borrow s1 1 [] = some e2 ∧ LoanTreeInv e2 ∧ ReturnAuthority e2 1 ∧
    endRaw e2 1 r = some (e3 (r 0)) ∧ LoanTreeInv (e3 (r 0)) ∧ (e3 (r 0)).isActive 1 = false ∧
    (e3 (r 0)).isActive 2 = true ∧ (e3 (r 0)).parentOf 2 = some 1 :=
  ⟨by decide, by decide, returnAuthority_of_closed [2] (by decide) (by decide), rfl,
   of_decide_eq_true rfl, rfl, rfl, rfl⟩

/-! ## Tightness counterexamples for R2b (each violates exactly one law and is not
write-exclusive) -/

/-- Two active exclusive roots on the same cell. -/
def weRootsDisjoint : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := none, mode := .excl, active := true, cells := [some (.own 0 0)] }]⟩

/-- A self-parented shared reader beside a writer root. -/
def weParentLt : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := some 1, mode := .shared, active := true, cells := [some (.own 2 0)] }]⟩

/-- A shared child below its baseline depth (depth `0`, so it writes) beside its reading
parent. -/
def weDepthCounts : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 0 0)] }]⟩

/-- An active writer below a retired view, beside a writer root. -/
def weParentCoversActive : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := some 0, mode := .excl, active := false, cells := [some (.loaned 2)] },
  { parent := some 1, mode := .excl, active := true, cells := [some (.own 0 0)] }]⟩

/-- A shared view that lent exclusively: its exclusive child writes while the root reads. -/
def weSharedChildrenShared : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.loaned 2)] },
  { parent := some 1, mode := .excl, active := true, cells := [some (.own 0 0)] }]⟩

/-- A shared child reading a cell its parent has lent exclusively to a writer. -/
def weSharedChildBelowOwn : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] }]⟩

theorem writeExclusive_needs_parentLt :
    ¬ ParentLt weParentLt ∧ ParentCoversActive weParentLt ∧ ExclChildLoaned weParentLt ∧
    SharedChildBelowOwn weParentLt ∧ SharedChildrenShared weParentLt ∧ DepthCounts weParentLt ∧
    RootsDisjoint weParentLt ∧ ¬ WriteExclusive weParentLt := by decide

theorem writeExclusive_needs_parentCoversActive :
    ParentLt weParentCoversActive ∧ ¬ ParentCoversActive weParentCoversActive ∧
    ExclChildLoaned weParentCoversActive ∧ SharedChildBelowOwn weParentCoversActive ∧
    SharedChildrenShared weParentCoversActive ∧ DepthCounts weParentCoversActive ∧
    RootsDisjoint weParentCoversActive ∧ ¬ WriteExclusive weParentCoversActive := by decide

theorem writeExclusive_needs_exclChildLoaned :
    ParentLt weExclChildLoaned ∧ ParentCoversActive weExclChildLoaned ∧
    ¬ ExclChildLoaned weExclChildLoaned ∧ SharedChildBelowOwn weExclChildLoaned ∧
    SharedChildrenShared weExclChildLoaned ∧ DepthCounts weExclChildLoaned ∧
    RootsDisjoint weExclChildLoaned ∧ ¬ WriteExclusive weExclChildLoaned := by decide

theorem writeExclusive_needs_sharedChildBelowOwn :
    ParentLt weSharedChildBelowOwn ∧ ParentCoversActive weSharedChildBelowOwn ∧
    ExclChildLoaned weSharedChildBelowOwn ∧ ¬ SharedChildBelowOwn weSharedChildBelowOwn ∧
    SharedChildrenShared weSharedChildBelowOwn ∧ DepthCounts weSharedChildBelowOwn ∧
    RootsDisjoint weSharedChildBelowOwn ∧ ¬ WriteExclusive weSharedChildBelowOwn := by decide

theorem writeExclusive_needs_sharedChildrenShared :
    ParentLt weSharedChildrenShared ∧ ParentCoversActive weSharedChildrenShared ∧
    ExclChildLoaned weSharedChildrenShared ∧ SharedChildBelowOwn weSharedChildrenShared ∧
    ¬ SharedChildrenShared weSharedChildrenShared ∧ DepthCounts weSharedChildrenShared ∧
    RootsDisjoint weSharedChildrenShared ∧ ¬ WriteExclusive weSharedChildrenShared := by decide

theorem writeExclusive_needs_depthCounts :
    ParentLt weDepthCounts ∧ ParentCoversActive weDepthCounts ∧ ExclChildLoaned weDepthCounts ∧
    SharedChildBelowOwn weDepthCounts ∧ SharedChildrenShared weDepthCounts ∧
    ¬ DepthCounts weDepthCounts ∧ RootsDisjoint weDepthCounts ∧
    ¬ WriteExclusive weDepthCounts := by decide

theorem writeExclusive_needs_rootsDisjoint :
    ParentLt weRootsDisjoint ∧ ParentCoversActive weRootsDisjoint ∧
    ExclChildLoaned weRootsDisjoint ∧ SharedChildBelowOwn weRootsDisjoint ∧
    SharedChildrenShared weRootsDisjoint ∧ DepthCounts weRootsDisjoint ∧
    ¬ RootsDisjoint weRootsDisjoint ∧ ¬ WriteExclusive weRootsDisjoint := by decide

/-! ## R2d: non-vacuity and tightness counterexamples (canonical form)

The two R2d statements share the hypotheses `hpc`, `hecl`, `hdc` and `hloc`; the end form adds
`hscb`, `hscs` and `hend`. Each witness for a shared hypothesis refutes both statements: the named
hypothesis fails; every other hypothesis of both statements holds, including the two extra laws and
success of the raw end of `c`; `c` has no return authority; and the end step breaks
`NoResurrection`, so the conclusion of the end form fails. The witnesses for `hscb` and `hscs`
refute the end form only: there `c` does have return authority, and the end step breaks
`DepthCounts`. (Four of the five counterexample states of R2a cannot be reused here, because the
ended view fails the local check there.) -/

/-- **R2d non-vacuity (both statements).** In `s1` (exclusive child `B`) and `t1` (shared child
`B`) all five tree-local laws hold, `B` passes the local return check, and the raw end of `B`
succeeds. -/
theorem localCheck_nonvacuous (r : Addr → Byte) :
    (ParentCoversActive s1 ∧ ExclChildLoaned s1 ∧ SharedChildBelowOwn s1 ∧
      SharedChildrenShared s1 ∧ DepthCounts s1 ∧ LocalReturnCheck s1 1 ∧
      ∃ s', endRaw s1 1 r = some s') ∧
    (ParentCoversActive t1 ∧ ExclChildLoaned t1 ∧ SharedChildBelowOwn t1 ∧
      SharedChildrenShared t1 ∧ DepthCounts t1 ∧ LocalReturnCheck t1 1 ∧
      ∃ s', endRaw t1 1 r = some s') :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, _, rfl⟩,
   ⟨by decide, by decide, by decide, by decide, by decide, by decide, _, rfl⟩⟩

/-- In R2a's counterexample states for `ParentCoversActive`, `ExclChildLoaned`,
`SharedChildBelowOwn` and `SharedChildrenShared`, the ended view fails the local check (it still
records a loan), so those states cannot witness tightness for R2d. -/
theorem endRaw_inv_counterexamples_fail_localReturnCheck :
    ¬ LocalReturnCheck cxParentCoversActive 1 ∧ ¬ LocalReturnCheck cxExclChildLoaned 1 ∧
    ¬ LocalReturnCheck cxSharedChildBelowOwn 1 ∧ ¬ LocalReturnCheck cxSharedChildrenShared 2 :=
  by decide

/-- An active exclusive view `D` (id 3) still covers address `0` under the retired view `C`
(id 2), which is a child of `B`; `B` itself holds the cell as `own 0 0`. Violates only
`ParentCoversActive` among the five local laws. -/
def rdParentCoversActive : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := some 1, mode := .excl, active := false, cells := [some (.loaned 3)] },
  { parent := some 2, mode := .excl, active := true, cells := [some (.own 0 0)] }]⟩

/-- `B` (id 1) holds its cell as `own 0 0` although it has an active exclusive child `C` (id 2)
covering that cell: the loan to `C` is not recorded. Violates only `ExclChildLoaned` among the five
local laws. -/
def rdExclChildLoaned : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.loaned 1)] },
  { parent := some 0, mode := .excl, active := true, cells := [some (.own 0 0)] },
  { parent := some 1, mode := .excl, active := true, cells := [some (.own 0 0)] }]⟩

/-- The shared view `B` (id 1) is at its baseline depth `1` although it has an active shared
child `C` (id 2) reading the same cell. Violates only `DepthCounts` (at `B`) among the five local
laws. -/
def rdDepthCounts : State := ⟨[
  { parent := none, mode := .excl, active := true, cells := [some (.own 1 0)] },
  { parent := some 0, mode := .shared, active := true, cells := [some (.own 1 0)] },
  { parent := some 1, mode := .shared, active := true, cells := [some (.own 1 0)] }]⟩

theorem localCheck_needs_parentCoversActive :
    ¬ ParentCoversActive rdParentCoversActive ∧ ExclChildLoaned rdParentCoversActive ∧
    SharedChildBelowOwn rdParentCoversActive ∧ SharedChildrenShared rdParentCoversActive ∧
    DepthCounts rdParentCoversActive ∧ LocalReturnCheck rdParentCoversActive 1 ∧
    ¬ ReturnAuthority rdParentCoversActive 1 ∧
    ∃ s', endRaw rdParentCoversActive 1 (fun _ => 0) = some s' ∧
      ¬ NoResurrection rdParentCoversActive s' ∧
      ¬ (LocalLoanLaws s' ∧ NoResurrection rdParentCoversActive s') :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
   fun h => absurd (h 3 (.step (x := 2) rfl (.child rfl)) rfl 0 rfl) (by decide), _, rfl,
   fun h => absurd (h 0 (by decide) 0 (by decide) (by decide) 3
     (.step (x := 2) rfl (.step (x := 1) rfl (.child rfl))) rfl) (by decide),
   fun h => absurd h.1 (by decide)⟩

theorem localCheck_needs_exclChildLoaned :
    ParentCoversActive rdExclChildLoaned ∧ ¬ ExclChildLoaned rdExclChildLoaned ∧
    SharedChildBelowOwn rdExclChildLoaned ∧ SharedChildrenShared rdExclChildLoaned ∧
    DepthCounts rdExclChildLoaned ∧ LocalReturnCheck rdExclChildLoaned 1 ∧
    ¬ ReturnAuthority rdExclChildLoaned 1 ∧
    ∃ s', endRaw rdExclChildLoaned 1 (fun _ => 0) = some s' ∧
      ¬ NoResurrection rdExclChildLoaned s' ∧
      ¬ (LocalLoanLaws s' ∧ NoResurrection rdExclChildLoaned s') :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
   fun h => absurd (h 2 (.child rfl) rfl 0 rfl) (by decide), _, rfl,
   fun h => absurd (h 0 (by decide) 0 (by decide) (by decide) 2
     (.step (x := 1) rfl (.child rfl)) rfl) (by decide),
   fun h => absurd h.1 (by decide)⟩

theorem localCheck_needs_depthCounts :
    ParentCoversActive rdDepthCounts ∧ ExclChildLoaned rdDepthCounts ∧
    SharedChildBelowOwn rdDepthCounts ∧ SharedChildrenShared rdDepthCounts ∧
    ¬ DepthCounts rdDepthCounts ∧ LocalReturnCheck rdDepthCounts 1 ∧
    ¬ ReturnAuthority rdDepthCounts 1 ∧
    ∃ s', endRaw rdDepthCounts 1 (fun _ => 0) = some s' ∧
      ¬ NoResurrection rdDepthCounts s' ∧
      ¬ (LocalLoanLaws s' ∧ NoResurrection rdDepthCounts s') :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
   fun h => absurd (h 2 (.child rfl) rfl 0 rfl) (by decide), _, rfl,
   fun h => absurd (h 0 (by decide) 0 (by decide) (by decide) 2
     (.step (x := 1) rfl (.child rfl)) rfl) (by decide),
   fun h => absurd h.1 (by decide)⟩

/-- The local check itself is needed: in `s2` all five local laws hold, `B` (whose cell is
`loaned 2`) fails the check and has no return authority, and its raw end succeeds and breaks the
local laws and `NoResurrection`. -/
theorem localCheck_needs_localReturnCheck :
    ParentCoversActive s2 ∧ ExclChildLoaned s2 ∧ SharedChildBelowOwn s2 ∧
    SharedChildrenShared s2 ∧ DepthCounts s2 ∧ ¬ LocalReturnCheck s2 1 ∧
    ¬ ReturnAuthority s2 1 ∧
    ∃ s', endRaw s2 1 (fun _ => 0) = some s' ∧ ¬ NoResurrection s2 s' ∧
      ¬ (LocalLoanLaws s' ∧ NoResurrection s2 s') :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, not_returnAuthority_s2_B,
   _, rfl, not_noResurrection_s2_end_B, fun h => not_noResurrection_s2_end_B h.2⟩

/-- `SharedChildBelowOwn` is needed by the end form, not by return authority: in
`weSharedChildBelowOwn` `B` (id 1) passes the local check and has return authority (it has no
descendants), and the other four local laws hold, but `A` has an active shared child `C` on the
cell it lent exclusively to `B`; ending `B` makes `A` writable at depth `0` while `C` still reads,
breaking `DepthCounts`. -/
theorem localCheck_end_needs_sharedChildBelowOwn :
    ParentCoversActive weSharedChildBelowOwn ∧ ExclChildLoaned weSharedChildBelowOwn ∧
    ¬ SharedChildBelowOwn weSharedChildBelowOwn ∧ SharedChildrenShared weSharedChildBelowOwn ∧
    DepthCounts weSharedChildBelowOwn ∧ LocalReturnCheck weSharedChildBelowOwn 1 ∧
    ReturnAuthority weSharedChildBelowOwn 1 ∧
    ∃ s', endRaw weSharedChildBelowOwn 1 (fun _ => 0) = some s' ∧ ¬ DepthCounts s' ∧
      ¬ (LocalLoanLaws s' ∧ NoResurrection weSharedChildBelowOwn s') :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
   returnAuthority_of_closed [] (by decide) (by decide), _, rfl, by decide,
   fun h => absurd h.1 (by decide)⟩

/-- `SharedChildrenShared` is needed by the end form, not by return authority: in
`weSharedChildrenShared` the shared view `B` lent its cell exclusively to `C` (id 2); `C` passes the
local check and has return authority, and the other four local laws hold; ending `C` gives `B` an
`own` cell at depth `0`, below its shared baseline, breaking `DepthCounts`. -/
theorem localCheck_end_needs_sharedChildrenShared :
    ParentCoversActive weSharedChildrenShared ∧ ExclChildLoaned weSharedChildrenShared ∧
    SharedChildBelowOwn weSharedChildrenShared ∧ ¬ SharedChildrenShared weSharedChildrenShared ∧
    DepthCounts weSharedChildrenShared ∧ LocalReturnCheck weSharedChildrenShared 2 ∧
    ReturnAuthority weSharedChildrenShared 2 ∧
    ∃ s', endRaw weSharedChildrenShared 2 (fun _ => 0) = some s' ∧ ¬ DepthCounts s' ∧
      ¬ (LocalLoanLaws s' ∧ NoResurrection weSharedChildrenShared s') :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
   returnAuthority_of_closed [] (by decide) (by decide), _, rfl, by decide,
   fun h => absurd h.1 (by decide)⟩

/-- The local check does not make the end enabled: it holds for the retired view `B` of `s1e 0`
(whose cell is still `own 0 0`) and, vacuously, for the nonexistent view `99` of `s0`, and neither
can be ended. So the end form of R2d says nothing about views whose raw end fails. -/
theorem localReturnCheck_does_not_enable_end :
    LocalReturnCheck (s1e 0) 1 ∧ (s1e 0).isActive 1 = false ∧
      endRaw (s1e 0) 1 (fun _ => 0) = none ∧
    LocalReturnCheck s0 99 ∧ endRaw s0 99 (fun _ => 0) = none :=
  ⟨by decide, rfl, rfl, by decide, rfl⟩

/-! ## Definition examples for the laws (positive: the intended states; negative: the
counterexample states above) -/

theorem laws_hold_on_intended_states :
    LoanTreeInv s0 ∧ LoanTreeInv s1 ∧ LoanTreeInv s2 ∧ LoanTreeInv t1 ∧ LoanTreeInv t2 ∧
    LoanTreeInv u2 ∧ LoanTreeInv w2 ∧ ParentsExist s2 := by decide

/-- `LocalLoanLaws`: positive on the intended state `s2` and on `cxParentLt` (a self-parented reader:
the local laws do not imply `ParentLt`); negative on `cxDepthCounts` (a wrong depth counter). -/
theorem localLoanLaws_examples :
    LocalLoanLaws s2 ∧ LocalLoanLaws cxParentLt ∧ ¬ ParentLt cxParentLt ∧
      ¬ LocalLoanLaws cxDepthCounts := by decide

theorem parentsExist_example_neg : ¬ ParentsExist ⟨[
    { parent := some 3, mode := .excl, active := true, cells := [] }]⟩ := by decide

theorem writeExclusive_examples : WriteExclusive s2 ∧ WriteExclusive t2 ∧ ¬ WriteExclusive t3 :=
  by decide

end Ex
end Toy.Views
