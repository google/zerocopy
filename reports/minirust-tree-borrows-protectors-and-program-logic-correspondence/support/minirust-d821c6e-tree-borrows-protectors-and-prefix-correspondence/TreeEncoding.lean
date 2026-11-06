import AnnealResearch.TreeNodeUpdate

/-!
Generic coverage of the owned recursive tree representation. The existing
topologyOf preserves the full ordered shape. Present entries come from actual
reference findNode; only absent paths use the explicit default. Reconstruction
has no width, permission/protector matching, reachability, access-success or
NoUB premise. This is a representation result, not source/helper adequacy.

The generic reconstruction lemma takes lookup-entry agreement and discharges it
for the actual encoder below. It does not impose a new admission condition on
the arbitrary node in reify_encode. Optional memory and the opposite round trip
are separate checkpoints.
-/

namespace AnnealResearch.TreeEncoding

open TreeFactored (Path Entry Store State)

/-- This value is read only when the actual reference lookup returns none. -/
def defaultEntry : Entry := ⟨[], .no⟩

def lookupEntry (node : TreeReference.Node) (path : Path) : Entry :=
  match TreeReference.findNode node path with
  | none => defaultEntry
  | some child => TreeNodeUpdate.entryOf child

def encode (node : TreeReference.Node) : State :=
  ⟨TreeCorrespondence.topologyOf node, lookupEntry node⟩

theorem lookupEntry_found (node child : TreeReference.Node) (path : Path)
    (found : TreeReference.findNode node path = some child) :
    lookupEntry node path = TreeNodeUpdate.entryOf child := by
  simp only [lookupEntry, found]

theorem lookupEntry_missing (node : TreeReference.Node) (path : Path)
    (missing : TreeReference.findNode node path = none) :
    lookupEntry node path = defaultEntry := by
  simp only [lookupEntry, missing]

theorem lookupEntry_root (node : TreeReference.Node) :
    lookupEntry node [] = TreeNodeUpdate.entryOf node := rfl

/-- Entries at an absolute base agree with every actually found descendant.
No requirement is placed on a missing path or on permission contents. -/
def EntriesAt (node : TreeReference.Node) (here : Path) (store : Store) : Prop :=
  ∀ path child, TreeReference.findNode node path = some child →
    store (here ++ path) = TreeNodeUpdate.entryOf child

mutual
  /-- Reconstruction of every represented node from its actual lookup entries.
  This helper permits any store values outside the represented subtree. -/
  theorem reifyTree_of_entries (node : TreeReference.Node) (here : Path) (store : Store)
      (entries : EntriesAt node here store) :
      TreeCorrespondence.reifyTree (TreeCorrespondence.topologyOf node) here store = node :=
    match node, entries with
    | .mk permissions protection children, entries => by
      have rootEntry : store here = ⟨permissions, protection⟩ := by
        simpa only [List.append_nil, TreeNodeUpdate.entryOf,
          TreeReference.Node.permissions, TreeReference.Node.protection] using
          entries [] (.mk permissions protection children) rfl
      have childEntries : ∀ relative child, children[relative]? = some child →
          EntriesAt child (here ++ [0 + relative]) store := by
        intro relative child found path selected below
        have inRoot : TreeReference.findNode (.mk permissions protection children)
            (relative :: path) = some selected := by
          change (match children[relative]? with
            | none => none
            | some selectedChild => TreeReference.findNode selectedChild path) = some selected
          rw [found]
          exact below
        simpa only [Nat.zero_add, List.append_assoc, List.singleton_append] using
          entries (relative :: path) selected inRoot
      simp only [TreeCorrespondence.topologyOf, TreeCorrespondence.reifyTree]
      rw [rootEntry, reifyForest_of_entries children here 0 store childEntries]
  termination_by sizeOf node
  decreasing_by all_goals simp_wf <;> omega

  /-- Child indices remain their original ordered indices as the forest tail
  is traversed; no sibling or descendant is omitted. -/
  theorem reifyForest_of_entries (children : List TreeReference.Node) (parent : Path)
      (index : Nat) (store : Store)
      (entries : ∀ relative child, children[relative]? = some child →
        EntriesAt child (parent ++ [index + relative]) store) :
      TreeCorrespondence.reifyForest (TreeCorrespondence.forestOf children)
        parent index store = children :=
    match children, entries with
    | [], _ => by simp only [TreeCorrespondence.forestOf, TreeCorrespondence.reifyForest]
    | child :: rest, entries => by
      have firstEntries : EntriesAt child (parent ++ [index]) store := by
        simpa only [Nat.add_zero] using entries 0 child rfl
      have laterEntries : ∀ relative selected, rest[relative]? = some selected →
          EntriesAt selected (parent ++ [index + 1 + relative]) store := by
        intro relative selected found
        have atOriginal : (child :: rest)[relative + 1]? = some selected := by
          change rest[relative]? = some selected
          exact found
        have shifted := entries (relative + 1) selected atOriginal
        have position : index + (relative + 1) = index + 1 + relative := by omega
        simpa only [position] using shifted
      simp only [TreeCorrespondence.forestOf, TreeCorrespondence.reifyForest]
      rw [reifyTree_of_entries child (parent ++ [index]) store firstEntries,
        reifyForest_of_entries rest parent (index + 1) store laterEntries]
  termination_by sizeOf children
  decreasing_by all_goals simp_wf <;> omega
end

theorem encode_entries (node : TreeReference.Node) : EntriesAt node [] (lookupEntry node) := by
  intro path child found
  simpa only [List.nil_append] using lookupEntry_found node child path found

/-- Every finite recursive reference tree is covered, including mismatched
widths or permission/protector constructors and states admitting later UB. -/
theorem reify_encode (node : TreeReference.Node) :
    TreeCorrespondence.reify (encode node) = node := by
  change TreeCorrespondence.reifyTree (TreeCorrespondence.topologyOf node) []
    (lookupEntry node) = node
  exact reifyTree_of_entries node [] (lookupEntry node) (encode_entries node)

theorem related_encode (node : TreeReference.Node) :
    TreeCorrespondence.Related node (encode node) := (reify_encode node).symm

#print axioms lookupEntry_found
#print axioms lookupEntry_missing
#print axioms lookupEntry_root
#print axioms reifyTree_of_entries
#print axioms reifyForest_of_entries
#print axioms encode_entries
#print axioms reify_encode
#print axioms related_encode

end AnnealResearch.TreeEncoding
