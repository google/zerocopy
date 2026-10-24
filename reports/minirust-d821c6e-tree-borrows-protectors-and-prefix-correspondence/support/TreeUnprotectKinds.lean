import AnnealResearch.TreeReleaseKinds

/-!
Actual unprotect produces the flag-clear query required by successful release.
The conversion theorem observes the executed whole-list map and selected-path
reconstruction; it assumes neither matching nor successful future traversal.
The final local composition uses actual unprotect/traversal output equations.
No width, valid-path, matching, reachability or NoUB admission is introduced.

This is a tree bridge for the live traversal branch, not a claim that release
always succeeds or that all terminal/dead residuals match. Full memory-level
RunningKinds is a subsequent boundary theorem.
-/

namespace AnnealResearch.TreeUnprotectKinds

open TreePermissions
open TreeReleaseKinds (kindsAfterClear childrenAfterClear kindsAfterClear_none)

theorem childrenAfterClear_before (children : List TreeReference.Node) (selected start : Nat)
    (path : TreeReference.Path) (earlier : selected < start) :
    childrenAfterClear children (some (selected :: path)) start =
      TreeReference.childrenMatch children := by
  induction children generalizing start with
  | nil => simp only [childrenAfterClear, TreeReference.childrenMatch]
  | cons child rest ih =>
    have different : selected ≠ start := by omega
    simp only [childrenAfterClear, TreeReference.childrenMatch, TreeReference.childPath,
      ite_eq_right different]
    rw [kindsAfterClear_none child, ih (start + 1) (by omega)]

/-- Only the selected child uses the flag-clear query. Earlier/later siblings
use ordinary matching, with their complete ordered subtrees retained. -/
theorem childrenAfterClear_replace (children : List TreeReference.Node) (relative start : Nat)
    (before after : TreeReference.Node) (path : TreeReference.Path)
    (found : children[relative]? = some before)
    (restored : kindsAfterClear after (some path) = TreeReference.kindsMatch before) :
    childrenAfterClear (TreeReference.replaceNth children relative after)
        (some ((start + relative) :: path)) start = TreeReference.childrenMatch children := by
  induction relative generalizing children start with
  | zero =>
    cases children with
    | nil => simp at found
    | cons child rest =>
      have same : child = before := Option.some.inj found
      subst before
      have selectedPath : TreeReference.childPath (some (start :: path)) start = some path := by
        simp [TreeReference.childPath]
      simp only [Nat.add_zero, TreeReference.replaceNth, childrenAfterClear,
        TreeReference.childrenMatch, selectedPath]
      rw [restored, childrenAfterClear_before rest start (start + 1) path (by omega)]
  | succ relative ih =>
    cases children with
    | nil => simp at found
    | cons child rest =>
      have below : rest[relative]? = some before := found
      have different : start + (relative + 1) ≠ start := by omega
      have selectedPath : TreeReference.childPath
          (some ((start + (relative + 1)) :: path)) start = none := by
        simp only [TreeReference.childPath, ite_eq_right different]
      have position : start + (relative + 1) = start + 1 + relative := by omega
      simp only [TreeReference.replaceNth, childrenAfterClear,
        TreeReference.childrenMatch, selectedPath]
      rw [kindsAfterClear_none child, position, ih rest (start + 1) below]

/-- A selected callback's local query law lifts through actual successful
modifyAt reconstruction. It imposes no law on callback failures. -/
theorem modifyAt_restores {A : Type} (callback : TreeReference.Node → TreeReference.Result A TreeReference.Node)
    (localLaw : ∀ selected value changed, callback selected = .ok value changed →
      kindsAfterClear changed (some []) = TreeReference.kindsMatch selected)
    (node : TreeReference.Node) (path : TreeReference.Path) (value : A)
    (after : TreeReference.Node) (success : TreeReference.modifyAt node path callback = .ok value after) :
    kindsAfterClear after (some path) = TreeReference.kindsMatch node := by
  induction path generalizing node value after with
  | nil => exact localLaw node value after success
  | cons index rest ih =>
    cases node with
    | mk permissions protection children =>
      cases found : children[index]? with
      | none =>
        simp only [TreeReference.modifyAt, found] at success
        cases success
      | some child =>
        have expanded :
            (TreeReference.modifyAt child rest callback).mapState
              (fun changed => TreeReference.Node.mk permissions protection
                (TreeReference.replaceNth children index changed)) = .ok value after := by
          simpa only [TreeReference.modifyAt, found] using success
        obtain ⟨changed, childOK, same⟩ := TreeReleaseKinds.mapState_ok
          (TreeReference.modifyAt child rest callback)
          (fun changed => TreeReference.Node.mk permissions protection
            (TreeReference.replaceNth children index changed)) value after expanded
        have restored := ih child value changed childOK
        have childrenQuery := childrenAfterClear_replace children index 0 child changed rest found restored
        simp only [Nat.zero_add] at childrenQuery
        rw [← same]
        simp [kindsAfterClear, TreeReference.kindsMatch]
        rw [childrenQuery]

/-- Successful executed conversion proves old Prot/new Unprot constructors.
No initial matching or protector flag is assumed by this list fact. -/
theorem unprotectPermissions_kinds (permissions changed : List Permission)
    (accesses : List (Option AccessKind))
    (converted : TreeReference.unprotectPermissions permissions = .ok (changed, accesses)) :
    permissions.all (fun permission => permission.matchesProtector .strong) = true ∧
      changed.all (fun permission => permission.matchesProtector .no) = true := by
  induction permissions generalizing changed accesses with
  | nil =>
    simp only [TreeReference.unprotectPermissions] at converted
    have same : ([] : List Permission) = changed := congrArg Prod.fst (Except.ok.inj converted)
    rw [← same]
    exact ⟨rfl, rfl⟩
  | cons permission rest ih =>
    cases permission with
    | unprot original =>
      simp only [TreeReference.unprotectPermissions, Permission.unprotect] at converted
      cases converted
    | prot original =>
      cases tail : TreeReference.unprotectPermissions rest with
      | error fault =>
        simp only [TreeReference.unprotectPermissions, Permission.unprotect, tail] at converted
        cases converted
      | ok pair =>
        rcases pair with ⟨next, more⟩
        have expanded := converted
        simp only [TreeReference.unprotectPermissions, Permission.unprotect, tail] at expanded
        have same : (.unprot original.unprotect.1 :: next) = changed :=
          congrArg Prod.fst (Except.ok.inj expanded)
        obtain ⟨oldTail, newTail⟩ := ih next more tail
        constructor
        · change ((Permission.prot original).matchesProtector .strong &&
            rest.all (fun entry => entry.matchesProtector .strong)) = true
          rw [oldTail]
          rfl
        · rw [← same]
          change ((Permission.unprot original.unprotect.1).matchesProtector .no &&
            next.all (fun entry => entry.matchesProtector .no)) = true
          rw [newTail]
          rfl

theorem unprotect_root_query (node : TreeReference.Node)
    (accesses : List (Option AccessKind)) (converted : TreeReference.Node)
    (success : TreeReference.unprotectAt node [] = .ok accesses converted) :
    kindsAfterClear converted (some []) = TreeReference.kindsMatch node := by
  cases node with
  | mk permissions protection children =>
    simp only [TreeReference.unprotectAt, TreeReference.modifyAt] at success
    split at success
    · cases success
    · have flagYes : protection.yes = true := by
        cases protection <;> simp_all [Protected.yes]
      cases listResult : TreeReference.unprotectPermissions permissions with
      | error fault =>
        simp only [listResult] at success
        cases success
      | ok pair =>
        rcases pair with ⟨changed, returned⟩
        have expanded : TreeReference.Result.ok returned
            (.mk changed protection children) = .ok accesses converted := by
          simpa only [listResult] using success
        have same : TreeReference.Node.mk changed protection children = converted :=
          (TreeReference.Result.ok.inj expanded).2
        have queries := unprotectPermissions_kinds permissions changed returned listResult
        have oldQuery : permissions.all (fun entry => entry.matchesProtector protection) = true := by
          have pointwise : (fun entry : Permission => entry.matchesProtector protection) =
              (fun entry => entry.matchesProtector .strong) := by
            funext entry
            unfold Permission.matchesProtector
            rw [flagYes]
            rfl
          rw [pointwise]
          exact queries.1
        rw [← same]
        simp [kindsAfterClear, TreeReference.kindsMatch, queries.2, oldQuery]

theorem unprotectAt_as_modify (node : TreeReference.Node) (path : TreeReference.Path) :
    TreeReference.unprotectAt node path = TreeReference.modifyAt node path
      (fun selected => TreeReference.unprotectAt selected []) := rfl

/-- The actual conversion establishes this equality at an arbitrary selected
path. No desired round-trip law is assumed as a conversion invariant. -/
theorem unprotectAt_success_query (node : TreeReference.Node) (path : TreeReference.Path)
    (accesses : List (Option AccessKind)) (converted : TreeReference.Node)
    (success : TreeReference.unprotectAt node path = .ok accesses converted) :
    kindsAfterClear converted (some path) = TreeReference.kindsMatch node := by
  rw [unprotectAt_as_modify] at success
  exact modifyAt_restores (fun selected => TreeReference.unprotectAt selected [])
    (fun selected value changed observed => unprotect_root_query selected value changed observed)
    node path accesses converted success

/-- Local equations for the actual conversion and public traversal compose.
These are the tree stages of the successful live branch, not an assertion that
an arbitrary public memory release succeeds. -/
theorem unprotect_release_success_matching (node : TreeReference.Node) (path : TreeReference.Path)
    (accesses : List (Option AccessKind)) (converted after : TreeReference.Node)
    (unprotected : TreeReference.unprotectAt node path = .ok accesses converted)
    (released : TreeReference.releaseTraverse converted (some path) accesses = .ok () after) :
    TreeReference.kindsMatch after = TreeReference.kindsMatch node := by
  exact (TreeReleaseKinds.releaseTraverse_success_matching converted (some path) accesses after released).trans
    (unprotectAt_success_query node path accesses converted unprotected)

theorem unprotect_release_preserves_matching (node : TreeReference.Node) (path : TreeReference.Path)
    (accesses : List (Option AccessKind)) (converted after : TreeReference.Node)
    (unprotected : TreeReference.unprotectAt node path = .ok accesses converted)
    (released : TreeReference.releaseTraverse converted (some path) accesses = .ok () after)
    (matching : TreeReference.kindsMatch node = true) : TreeReference.kindsMatch after = true :=
  (unprotect_release_success_matching node path accesses converted after unprotected released).trans matching

#print axioms childrenAfterClear_before
#print axioms childrenAfterClear_replace
#print axioms modifyAt_restores
#print axioms unprotectPermissions_kinds
#print axioms unprotect_root_query
#print axioms unprotectAt_as_modify
#print axioms unprotectAt_success_query
#print axioms unprotect_release_success_matching
#print axioms unprotect_release_preserves_matching

end AnnealResearch.TreeUnprotectKinds
