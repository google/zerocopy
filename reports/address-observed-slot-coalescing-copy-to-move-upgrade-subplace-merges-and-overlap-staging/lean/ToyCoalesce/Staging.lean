import ToyCoalesce.Merge

/-!
# Staging overlapping assignments

After coalescing, an aggregate assignment can read places that its own left side overwrites. With
in-order field writes this changes its result. Staging rewrites such an assignment
`lhs := rhs` into `storageLive tmp; tmp := rhs; lhs := move tmp; storageDead tmp` with a fresh
local `tmp`.
-/

namespace Toy.Coalesce

/-- Operand `o` may read a cell of `lhs`: a `copy`/`move` of a place whose window intersects
`lhs`, or any `load`. -/
def Operand.mayOverlap (lhs : Place) : Operand → Bool
  | .copy q => !decide (WindowsDisjoint lhs q)
  | .move q => !decide (WindowsDisjoint lhs q)
  | .load _ _ => true
  | _ => false

/-- A top-level assignment *needs staging*: it has at least two operands and one of them may read
a cell of its left side. -/
def NeedsStaging (lhs : Place) (rhs : List Operand) : Bool :=
  decide (2 ≤ rhs.length) && rhs.any (Operand.mayOverlap lhs)

/-- A top-level statement list contains no assignment that needs staging. -/
def stmtsNoStaging (sts : List Stmt) : Bool :=
  sts.all fun st => match st with
    | .assign lhs rhs => !NeedsStaging lhs rhs
    | _ => true

/-- Exactly one of the two places is based at the parameter local `prm`. Inside a callee run with
an in-place argument, places based at `prm` resolve into the argument place and the others resolve
to themselves, so two such places may share cells whatever their syntactic windows. -/
def Place.paramSplit (prm : Nat) (a b : Place) : Bool := (a.base == prm) != (b.base == prm)

/-- Operand `o` of an assignment in a callee with parameter `prm` may read a cell of `lhs`: a
`copy`/`move` of a place whose window intersects `lhs`, or of which exactly one of it and `lhs`
is based at `prm`; or any `load`. -/
def Operand.mayOverlapParam (prm : Nat) (lhs : Place) : Operand → Bool
  | .copy q => !decide (WindowsDisjoint lhs q) || Place.paramSplit prm lhs q
  | .move q => !decide (WindowsDisjoint lhs q) || Place.paramSplit prm lhs q
  | .load _ _ => true
  | _ => false

/-- An assignment of a callee with parameter `prm` needs staging: at least two operands, one of
which may read a cell of the left side under the in-place binding of `prm`. -/
def NeedsStagingParam (prm : Nat) (lhs : Place) (rhs : List Operand) : Bool :=
  decide (2 ≤ rhs.length) && rhs.any (Operand.mayOverlapParam prm lhs)

/-- No assignment of callee `c` needs staging (checked against its parameter `c.prm`). -/
def calleeNoStaging (c : Callee) : Bool :=
  c.body.all fun st => match st with
    | .assign lhs rhs => !NeedsStagingParam c.prm lhs rhs
    | _ => true

/-- No assignment of the body, the destructors or a callee needs staging. -/
def NoStagingNeeded (P : Prog) : Prop :=
  (stmtsNoStaging P.code && P.fns.all calleeNoStaging) = true

instance (P : Prog) : Decidable (NoStagingNeeded P) := by unfold NoStagingNeeded; infer_instance

/-- No callee assignment needs staging. -/
def CalleesNoStaging (P : Prog) : Prop := P.fns.all calleeNoStaging = true

instance (P : Prog) : Decidable (CalleesNoStaging P) := by
  unfold CalleesNoStaging; infer_instance

/-- Stage a statement list, numbering fresh temporaries from `next`; also return the sizes of the
temporaries in order. -/
def stageList (next : Nat) : List Stmt → List Stmt × List Nat
  | [] => ([], [])
  | st :: sts =>
    match st with
    | .assign lhs rhs =>
      if NeedsStaging lhs rhs then
        let r := stageList (next + 1) sts
        ([.storageLive next, .assign ⟨next, 0, lhs.len⟩ rhs,
          .assign lhs [.move ⟨next, 0, lhs.len⟩], .storageDead next] ++ r.1, lhs.len :: r.2)
      else
        let r := stageList next sts
        (st :: r.1, r.2)
    | _ =>
      let r := stageList next sts
      (st :: r.1, r.2)

/-- Stage the body and the destructor block; fresh temporaries are new locals appended after the
existing ones (callee bodies are left unchanged). -/
def stage (P : Prog) : Prog :=
  let b := stageList P.nloc P.body
  let d := stageList (P.nloc + b.2.length) P.dtors
  { P with sizes := P.sizes ++ b.2 ++ d.2, body := b.1, dtors := d.1 }

/-- Every local mentioned by the body, the destructors or a callee exists (`< P.nloc`). -/
def Operand.locals : Operand → List Nat
  | .copy q => [q.base]
  | .move q => [q.base]
  | .lit _ => []
  | .addrOf q => [q.base]
  | .load p _ => [p.base]

def Stmt.locals (P : Prog) : Stmt → List Nat
  | .storageLive x => [x]
  | .storageDead x => [x]
  | .assign lhs rhs => lhs.base :: rhs.flatMap Operand.locals
  | .store p v => p.base :: v.locals
  | .ptrEq a b => a.locals ++ b.locals
  | .ptrInRange a b _ => a.locals ++ b.locals
  | .out o => o.locals
  | .call fn a => (P.fn fn).prm :: a.locals
  | .nop => []

def LocalsInRange (P : Prog) : Prop :=
  ((P.code ++ P.fns.flatMap (·.body)).all fun st => (st.locals P).all (· < P.nloc)) = true

instance (P : Prog) : Decidable (LocalsInRange P) := by unfold LocalsInRange; infer_instance

/-- Every callee's parameter local exists (`c.prm < P.nloc`). -/
def ParamsInRange (P : Prog) : Prop := P.fns.all (fun c => decide (c.prm < P.nloc)) = true

instance (P : Prog) : Decidable (ParamsInRange P) := by unfold ParamsInRange; infer_instance

/-! ## Coalescing preserves the absence of staging needs, backwards -/

/-- Following edges from `x` ends at `x` itself or at the parent of some edge. -/
theorem Forest.resolveF_fst_eq_or_parent (μ : Forest) (n x : Nat) :
    (μ.resolveF n x).1 = x ∨ ∃ e ∈ μ, e.parent = (μ.resolveF n x).1 := by
  induction n generalizing x with
  | zero => exact Or.inl rfl
  | succ n ih =>
    simp only [Forest.resolveF]
    cases hp : μ.parentOf x with
    | none => exact Or.inl rfl
    | some e =>
      have he : e ∈ μ := List.mem_of_find?_eq_some hp
      rcases ih e.parent with h | ⟨e', he', h'⟩
      · exact Or.inr ⟨e, he, h.symm⟩
      · exact Or.inr ⟨e', he', h'⟩

/-- A local in no edge is its own root, at offset `0`. -/
theorem Forest.resolve_of_not_inClass (μ : Forest) (x : Nat) (h : μ.inClass x = false) :
    μ.resolve x = (x, 0) := by
  have hp : μ.parentOf x = none := by
    simp only [Forest.parentOf, List.find?_eq_none, beq_iff_eq]
    intro e he hc
    have : μ.inClass x = true := by
      simp only [Forest.inClass, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
      exact ⟨e, he, Or.inl (by simpa using hc)⟩
    simp [this] at h
  unfold Forest.resolve
  cases μ.length with
  | zero => rfl
  | succ n => simp [Forest.resolveF, hp]

/-- No local other than `p` has root `p` when `p` is in no edge. -/
theorem Forest.root_ne_of_not_inClass (μ : Forest) (p x : Nat) (h : μ.inClass p = false)
    (hx : x ≠ p) : μ.root x ≠ p := by
  intro hr
  rcases μ.resolveF_fst_eq_or_parent μ.length x with h1 | ⟨e, he, h1⟩
  · exact hx (h1.symm.trans hr)
  · have : μ.inClass p = true := by
      simp only [Forest.inClass, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
      exact ⟨e, he, Or.inr (h1.trans hr)⟩
    simp [this] at h

theorem windowsDisjoint_of_mapPlace (μ : Forest) (a b : Place)
    (h : WindowsDisjoint (μ.mapPlace a) (μ.mapPlace b)) : WindowsDisjoint a b := by
  unfold WindowsDisjoint Forest.mapPlace at h
  unfold WindowsDisjoint
  by_cases heq : a.base = b.base
  · simp only [heq, ne_eq, not_true_eq_false, false_or] at h
    rcases h with h | h
    · right; left; omega
    · right; right; omega
  · exact Or.inl heq

theorem paramSplit_mapPlace (μ : Forest) (prm : Nat) (hp : μ.inClass prm = false) (a b : Place) :
    Place.paramSplit prm (μ.mapPlace a) (μ.mapPlace b) = Place.paramSplit prm a b := by
  have key : ∀ x, (μ.root x == prm) = (x == prm) := by
    intro x
    by_cases hx : x = prm
    · subst hx
      simp [Forest.root, Forest.resolve_of_not_inClass μ x hp]
    · have h1 := Forest.root_ne_of_not_inClass μ prm x hp hx
      rw [show (μ.root x == prm) = false from by simpa using h1,
        show (x == prm) = false from by simpa using hx]
  simp [Place.paramSplit, Forest.mapPlace, key]

theorem mayOverlap_mapPlace (μ : Forest) (lhs : Place) (o : Operand)
    (h : o.mayOverlap lhs = true) :
    (o.mapPlaces μ.mapPlace).mayOverlap (μ.mapPlace lhs) = true := by
  cases o with
  | copy q =>
    simp only [Operand.mayOverlap, Operand.mapPlaces, Bool.not_eq_true',
      decide_eq_false_iff_not] at h ⊢
    exact fun hd => h (windowsDisjoint_of_mapPlace μ lhs q hd)
  | move q =>
    simp only [Operand.mayOverlap, Operand.mapPlaces, Bool.not_eq_true',
      decide_eq_false_iff_not] at h ⊢
    exact fun hd => h (windowsDisjoint_of_mapPlace μ lhs q hd)
  | load p l => simp [Operand.mayOverlap, Operand.mapPlaces]
  | lit n => simp [Operand.mayOverlap] at h
  | addrOf q => simp [Operand.mayOverlap] at h

theorem mayOverlapParam_mapPlace (μ : Forest) (prm : Nat) (hp : μ.inClass prm = false)
    (lhs : Place) (o : Operand) (h : o.mayOverlapParam prm lhs = true) :
    (o.mapPlaces μ.mapPlace).mayOverlapParam prm (μ.mapPlace lhs) = true := by
  cases o with
  | copy q =>
    simp only [Operand.mayOverlapParam, Operand.mapPlaces, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, paramSplit_mapPlace μ prm hp] at h ⊢
    rcases h with h | h
    · exact Or.inl fun hd => h (windowsDisjoint_of_mapPlace μ lhs q hd)
    · exact Or.inr h
  | move q =>
    simp only [Operand.mayOverlapParam, Operand.mapPlaces, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, paramSplit_mapPlace μ prm hp] at h ⊢
    rcases h with h | h
    · exact Or.inl fun hd => h (windowsDisjoint_of_mapPlace μ lhs q hd)
    · exact Or.inr h
  | load p l => simp [Operand.mayOverlapParam, Operand.mapPlaces]
  | lit n => simp [Operand.mayOverlapParam] at h
  | addrOf q => simp [Operand.mayOverlapParam] at h

theorem stmtsNoStaging_of_map_coalesceStmt (μ : Forest) (sts : List Stmt)
    (h : stmtsNoStaging (sts.map μ.coalesceStmt) = true) : stmtsNoStaging sts = true := by
  induction sts with
  | nil => rfl
  | cons st rest ih =>
    simp only [List.map, stmtsNoStaging, List.all_cons, Bool.and_eq_true] at h ⊢
    refine ⟨?_, ih h.2⟩
    cases st with
    | assign lhs rhs =>
      have h1 := h.1
      simp only [Forest.coalesceStmt, Stmt.mapPlaces, NeedsStaging, Bool.not_eq_true',
        Bool.and_eq_false_iff, decide_eq_false_iff_not, List.any_eq_false, List.length_map] at h1 ⊢
      rcases h1 with hlen | hno
      · exact Or.inl hlen
      · right
        intro o ho hmo
        exact hno (o.mapPlaces μ.mapPlace) (List.mem_map.2 ⟨o, ho, rfl⟩)
          (mayOverlap_mapPlace μ lhs o hmo)
    | _ => rfl

theorem calleeNoStaging_of_map_coalesceStmt (μ : Forest) (c : Callee)
    (hp : μ.inClass c.prm = false)
    (h : calleeNoStaging { c with body := c.body.map μ.coalesceStmt } = true) :
    calleeNoStaging c = true := by
  obtain ⟨prm, body⟩ := c
  replace hp : μ.inClass prm = false := hp
  simp only [calleeNoStaging] at h ⊢
  induction body with
  | nil => rfl
  | cons st rest ih =>
    simp only [List.map, List.all_cons, Bool.and_eq_true] at h ⊢
    refine ⟨?_, ih h.2⟩
    cases st with
    | assign lhs rhs =>
      have h1 := h.1
      simp only [Forest.coalesceStmt, Stmt.mapPlaces, NeedsStagingParam, Bool.not_eq_true',
        Bool.and_eq_false_iff, decide_eq_false_iff_not, List.any_eq_false, List.length_map] at h1 ⊢
      rcases h1 with hlen | hno
      · exact Or.inl hlen
      · right
        intro o ho hmo
        exact hno (o.mapPlaces μ.mapPlace) (List.mem_map.2 ⟨o, ho, rfl⟩)
          (mayOverlapParam_mapPlace μ prm hp lhs o hmo)
    | _ => rfl

/-- For a well-formed forest, if no assignment of the coalesced program needs staging, none of
the source does. -/
theorem noStagingNeeded_of_noStagingNeeded_coalesce (P : Prog) (μ : Forest) (hwf : ForestWF P μ)
    (hnc : NoStagingNeeded (coalesce μ P)) : NoStagingNeeded P := by
  have hprm := hwf.2.2.2.1
  unfold NoStagingNeeded at hnc ⊢
  simp only [coalesce, Prog.code, Bool.and_eq_true, stmtsNoStaging, List.all_append,
    List.all_map, List.all_eq_true] at hnc ⊢
  obtain ⟨⟨⟨_, hb⟩, hd⟩, hf⟩ := hnc
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have := stmtsNoStaging_of_map_coalesceStmt μ P.body
      (by simpa [stmtsNoStaging, List.all_map] using hb)
    simpa [stmtsNoStaging] using this
  · have := stmtsNoStaging_of_map_coalesceStmt μ P.dtors
      (by simpa [stmtsNoStaging, List.all_map] using hd)
    simpa [stmtsNoStaging] using this
  · intro c hc
    exact calleeNoStaging_of_map_coalesceStmt μ c (hprm c hc) (hf c hc)

/-! ## Main statements -/

/-- Refinement is transitive. -/
theorem Refines.trans {s1 s2 s3 : Sem} {P1 P2 P3 : Prog} (h12 : Refines s1 P1 s2 P2)
    (h23 : Refines s2 P2 s3 P3) : Refines s1 P1 s3 P3 := by
  intro o ho
  rcases h12 o ho with h | h
  · rcases h23 .ub h with h' | h'
    · exact Or.inl h'
    · exact Or.inl h'
  · exact h23 o h

/-- Outcome equality on every layout gives a refinement. -/
theorem refines_of_outcome_eq {semT semS : Sem} {T S : Prog}
    (h : ∀ A, outcome semT T A = outcome semS S A) : Refines semT T semS S := by
  intro o ⟨A, hA, hb⟩
  exact Or.inr ⟨A, (h A).symm.trans hA, hb⟩

/-- Coalescing does not change local sizes or callee parameters. -/
theorem paramsInRange_coalesce (μ : Forest) (P : Prog) (h : ParamsInRange P) :
    ParamsInRange (coalesce μ P) := by
  unfold ParamsInRange at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro c hc
  simp only [coalesce, List.mem_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  exact h c' hc'

end Toy.Coalesce
