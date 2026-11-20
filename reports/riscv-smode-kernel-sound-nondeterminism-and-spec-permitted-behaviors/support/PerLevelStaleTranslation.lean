/-
Probe: the RISC-V priv spec (riscv-isa-manual @ c05f1725, src/priv/supervisor.adoc)
contains two characterisations of stale address translation:

 (A) [[norm:sfence_vma_ordering_semantics]] L1285-1288:
     "An implicit read of the memory-management data structures may return any translation
      for an address that was valid at any time since the most recent SFENCE.VMA that
      subsumes that address."
 (B) [[sv32algorithm]] L1769-1775:
     "The results of implicit address-translation reads in step 2 may be held in a read-only,
      incoherent address-translation cache ... Entries in the address-translation cache may
      then satisfy subsequent step 2 reads ..."

Reading (B) literally caches *each level's* step-2 PTE read independently, so a walk can combine
a stale non-leaf PTE with a fresh read of the (now repurposed) old next-level table.  This file
exhibits a 2-level history in which (B) yields a translation that was never valid at any single
instant, i.e. (B) admits strictly more behaviours than (A).  Core Lean only; `decide`.
-/

namespace PerLevelStale

/-- Memory of PTE slots: slot 0 = root non-leaf PTE (holds table id 1=A or 2=B);
    slot 1 = leaf PTE in table A; slot 2 = leaf PTE in table B. Values = page ids. -/
abbrev Mem := Nat → Nat

def mkMem (root a b : Nat) : Mem := fun i => if i = 0 then root else if i = 1 then a else b

/-- Table id → address of its (single) leaf slot. -/
def leafSlot (tbl : Nat) : Nat := tbl

/-- A full, atomic 2-level walk against one memory snapshot. -/
def walk (m : Mem) : Nat := m (leafSlot (m 0))

/-- History since the last subsuming SFENCE.VMA:
    m0: root→A, A→P(10), B→Q(20)
    m1: software retargets root→B
    m2: software repurposes A's slot (e.g. frame reuse) → R(30). -/
def m0 : Mem := mkMem 1 10 20
def m1 : Mem := mkMem 2 10 20
def m2 : Mem := mkMem 2 30 20
def hist : List Mem := [m0, m1, m2]

/-- Reading (A): translations valid at some instant in the history. -/
def validAtSomeTime : List Nat := hist.map walk

/-- Reading (B): each step-2 read independently returns any historical value of that slot
    (the root read picks a table; the leaf read of that table's slot picks any snapshot). -/
def perLevel : List Nat :=
  hist.flatMap (fun mr => hist.map (fun ml => ml (leafSlot (mr 0))))

theorem validAtSomeTime_eq : validAtSomeTime = [10, 20, 20] := by decide

theorem perLevel_admits_never_valid :
    perLevel.contains 30 = true ∧ validAtSomeTime.contains 30 = false := by decide

/-- Discipline that collapses the gap: SFENCE.VMA rs1=x0 between retargeting a non-leaf PTE
    and repurposing the old table frame resets the history to start at m1. -/
def histFenced : List Mem := [m1, m2]
def perLevelFenced : List Nat :=
  histFenced.flatMap (fun mr => histFenced.map (fun ml => ml (leafSlot (mr 0))))
def validFenced : List Nat := histFenced.map walk

theorem fenced_no_gap : perLevelFenced = [20, 20, 20, 20] ∧ validFenced = [20, 20] := by decide

end PerLevelStale
