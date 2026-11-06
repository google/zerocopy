import AnnealResearch.TreeEncoding
import AnnealResearch.TreeLookup
import AnnealResearch.TreeQueries

/-!
Opposite round trip for the unrestricted factored representation. Encoding a
reified tree retains its ordered topology and every actually found entry, but
normalizes all absent paths to the encoder's explicit default. There is no
width, kind, success, NoUB or source-reachability premise. This first checkpoint
states represented-entry recovery using actual findTopology, rather than
claiming literal equality of unrestricted total stores.

The runners are unchanged. Query equalities below follow exact full recursive
reification, not permission-kind admission or successful execution. This is an
owned representation result; helper/generated-code and Rust adequacy remain
separate obligations.
-/

namespace AnnealResearch.TreeEncodingNormalization

open TreeFactored (Path Topology State)

def normalize (state : State) : State :=
  TreeEncoding.encode (TreeCorrespondence.reify state)

/-- The support is determined by actual recursive topology lookup. No condition
is imposed on entries at paths that return none. -/
def FoundEntriesAgree (first second : State) : Prop :=
  first.topology = second.topology ∧
    ∀ path child, TreeFactored.findTopology first.topology path = some child →
      first.store path = second.store path

theorem normalize_topology (state : State) :
    (normalize state).topology = state.topology := by
  exact TreeCorrespondence.topologyOf_reifyTree state.topology [] state.store

theorem normalize_found (state : State) (path : Path) (child : Topology)
    (found : TreeFactored.findTopology state.topology path = some child) :
    (normalize state).store path = state.store path := by
  change TreeEncoding.lookupEntry (TreeCorrespondence.reify state) path = state.store path
  have selected := TreeLookup.findNode_found state.topology child [] state.store path found
  have recovered := TreeEncoding.lookupEntry_found (TreeCorrespondence.reify state)
    (TreeCorrespondence.reifyTree child ([] ++ path) state.store) path selected
  simpa only [List.nil_append, TreeNodeUpdate.entryOf_reifyTree] using recovered

theorem normalize_missing (state : State) (path : Path)
    (missing : TreeFactored.findTopology state.topology path = none) :
    (normalize state).store path = TreeEncoding.defaultEntry := by
  change TreeEncoding.lookupEntry (TreeCorrespondence.reify state) path = _
  exact TreeEncoding.lookupEntry_missing (TreeCorrespondence.reify state) path
    ((TreeLookup.findNode_missing_iff state.topology [] state.store path).mpr missing)

theorem normalize_foundEntries (state : State) :
    FoundEntriesAgree (normalize state) state := by
  refine ⟨normalize_topology state, ?_⟩
  intro path child found
  rw [normalize_topology] at found
  exact normalize_found state path child found

/-- Exact recursive reconstruction, including every ordered child and entry.
It does not require equality at semantically absent total-store cells. -/
theorem normalize_reify (state : State) :
    TreeCorrespondence.reify (normalize state) = TreeCorrespondence.reify state :=
  TreeEncoding.reify_encode (TreeCorrespondence.reify state)

theorem normalize_idempotent (state : State) :
    normalize (normalize state) = normalize state := by
  unfold normalize
  rw [TreeEncoding.reify_encode]

theorem normalize_arrayLengthsTree (state : State) (width : Nat) :
    TreeFactored.arrayLengthsTree (normalize state).topology [] (normalize state).store width =
      TreeFactored.arrayLengthsTree state.topology [] state.store width := by
  rw [← TreeQueries.arraysSized_reify (normalize state) width,
    normalize_reify, TreeQueries.arraysSized_reify]

theorem normalize_containsStrong (state : State) :
    TreeFactored.containsStrong (normalize state) = TreeFactored.containsStrong state := by
  rw [← TreeQueries.containsStrong_reify, normalize_reify,
    TreeQueries.containsStrong_reify]

theorem normalize_matchesProtectors (state : State) :
    TreeFactored.matchesProtectors (normalize state) = TreeFactored.matchesProtectors state := by
  rw [← TreeQueries.kindsMatch_reify, normalize_reify, TreeQueries.kindsMatch_reify]

#print axioms normalize_topology
#print axioms normalize_found
#print axioms normalize_missing
#print axioms normalize_foundEntries
#print axioms normalize_reify
#print axioms normalize_idempotent
#print axioms normalize_arrayLengthsTree
#print axioms normalize_containsStrong
#print axioms normalize_matchesProtectors

end AnnealResearch.TreeEncodingNormalization
