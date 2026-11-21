import ToySlotCompact.Basic

/-!
# Liveness certificates: path liveness and a Boolean checker
-/

namespace Toy.SlotCompact

variable {N : Nat}

/-- Syntactic path liveness (the classical live-variables notion): slot `i` is live at `pc` iff
some control-flow path from `pc` reaches an instruction that uses `i`, and no instruction before
that use on the path (including the one at `pc`) overwrites `i`. Uses are semantic reads and `halt`
outputs; debug reads are not uses. Paths follow every syntactic successor (including successors of
a branch that can never be taken), and an operand of an assignment counts as a use even when the
assigned slot is itself dead afterwards; so this is neither strong (non-faint) liveness nor
dynamic liveness. -/
inductive PathLive (p : Prog N) : Nat → Fin N → Prop
  | use {pc : Nat} {ins : Instr N} {i : Fin N} :
      p[pc]? = some ins → ins.uses i = true → PathLive p pc i
  | pass {pc : Nat} {ins : Instr N} {s : Nat} {i : Fin N} :
      p[pc]? = some ins → s ∈ ins.succs pc → ins.defs i = false → PathLive p s i →
      PathLive p pc i

/-- **Certificates over-approximate path liveness.** A mask satisfying the gen inequality
(`ReadsLive`) and the transfer inequality (`TransferClosed`) contains every path-live slot. -/
theorem pathLive_imp_mask_of_cert {p : Prog N} {L : Ann N} (hR : ReadsLive p L)
    (hT : TransferClosed p L) {pc : Nat} {i : Fin N} (h : PathLive p pc i) : L pc i = true := by
  induction h with
  | use hins hu => exact hR _ _ hins _ hu
  | pass hins hs hd _ ih => exact hT _ _ hins _ hs _ ih hd

/-- Boolean check of the gen inequality (`ReadsLive`) at every program point. -/
def checkReads (p : Prog N) (L : Ann N) : Bool :=
  (List.range p.length).all fun pc =>
    match p[pc]? with
    | none => true
    | some ins => (List.finRange N).all fun i => !ins.uses i || L pc i

/-- Boolean check of the transfer inequality (`TransferClosed`) at every program point. -/
def checkTransfer (p : Prog N) (L : Ann N) : Bool :=
  (List.range p.length).all fun pc =>
    match p[pc]? with
    | none => true
    | some ins => (List.finRange N).all fun i =>
        (ins.succs pc).all (fun s => !L s i || ins.defs i || L pc i)

/-- The Boolean liveness-certificate checker: at every program point it checks the gen inequality
and the transfer inequality for every slot. -/
def checkLive (p : Prog N) (L : Ann N) : Bool := checkReads p L && checkTransfer p L

/-- Pointwise unfolding of a per-instruction Boolean check over all program points. -/
theorem all_points_iff (p : Prog N) (f : Nat → Instr N → Bool) :
    ((List.range p.length).all fun pc =>
      match p[pc]? with
      | none => true
      | some ins => f pc ins) = true ↔ ∀ pc ins, p[pc]? = some ins → f pc ins = true := by
  constructor
  · intro h pc ins hins
    have hlt : pc < p.length := (List.getElem?_eq_some_iff.mp hins).1
    have h1 := List.all_eq_true.mp h pc (List.mem_range.mpr hlt)
    rw [hins] at h1
    exact h1
  · intro h
    apply List.all_eq_true.mpr
    intro pc _
    cases hins : p[pc]? with
    | none => rfl
    | some ins => exact h pc ins hins

theorem checkReads_eq_true_iff (p : Prog N) (L : Ann N) :
    checkReads p L = true ↔ ReadsLive p L := by
  unfold checkReads ReadsLive
  rw [all_points_iff p (fun pc ins => (List.finRange N).all fun i => !ins.uses i || L pc i)]
  constructor
  · intro h pc ins hins i hu
    have := List.all_eq_true.mp (h pc ins hins) i (List.mem_finRange i)
    simpa [hu] using this
  · intro h pc ins hins
    apply List.all_eq_true.mpr
    intro i _
    cases hu : ins.uses i
    · rfl
    · simp [h pc ins hins i hu]

theorem checkTransfer_eq_true_iff (p : Prog N) (L : Ann N) :
    checkTransfer p L = true ↔ TransferClosed p L := by
  unfold checkTransfer TransferClosed
  rw [all_points_iff p (fun pc ins => (List.finRange N).all fun i =>
    (ins.succs pc).all (fun s => !L s i || ins.defs i || L pc i))]
  constructor
  · intro h pc ins hins s hs i hl hd
    have := List.all_eq_true.mp (List.all_eq_true.mp (h pc ins hins) i (List.mem_finRange i)) s hs
    simpa [hl, hd] using this
  · intro h pc ins hins
    apply List.all_eq_true.mpr
    intro i _
    apply List.all_eq_true.mpr
    intro s hs
    cases hl : L s i
    · rfl
    · cases hd : ins.defs i
      · simp [h pc ins hins s hs i hl hd]
      · simp

/-- The checker accepts exactly the masks satisfying both certificate inequalities. -/
theorem checkLive_eq_true_iff (p : Prog N) (L : Ann N) :
    checkLive p L = true ↔ ReadsLive p L ∧ TransferClosed p L := by
  rw [checkLive, Bool.and_eq_true, checkReads_eq_true_iff, checkTransfer_eq_true_iff]

/-- **Checker soundness.** An accepted mask contains every path-live slot. -/
theorem checkLive_sound {p : Prog N} {L : Ann N} (h : checkLive p L = true) {pc : Nat}
    {i : Fin N} (hl : PathLive p pc i) : L pc i = true :=
  have ⟨hR, hT⟩ := (checkLive_eq_true_iff p L).mp h
  pathLive_imp_mask_of_cert hR hT hl

/-- **Under-approximations are rejected.** If a mask omits a path-live slot, the checker
returns `false`. -/
theorem checkLive_eq_false_of_missing {p : Prog N} {L : Ann N} {pc : Nat} {i : Fin N}
    (hl : PathLive p pc i) (hL : L pc i = false) : checkLive p L = false := by
  cases h : checkLive p L
  · rfl
  · rw [checkLive_sound h hl] at hL
    exact absurd hL (by simp)

/-- Path liveness as a mask (noncomputable). -/
noncomputable def pathLiveMask (p : Prog N) : Ann N :=
  fun pc i => @decide (PathLive p pc i) (Classical.propDecidable _)

theorem pathLiveMask_eq_true {p : Prog N} {pc : Nat} {i : Fin N} :
    pathLiveMask p pc i = true ↔ PathLive p pc i := by
  simp [pathLiveMask]

/-- Path liveness satisfies both certificate inequalities. -/
theorem pathLiveMask_cert (p : Prog N) :
    ReadsLive p (pathLiveMask p) ∧ TransferClosed p (pathLiveMask p) := by
  constructor
  · intro pc ins hins i hu
    exact pathLiveMask_eq_true.mpr (PathLive.use hins hu)
  · intro pc ins hins s hs i hl hd
    exact pathLiveMask_eq_true.mpr (PathLive.pass hins hs hd (pathLiveMask_eq_true.mp hl))

/-- The checker accepts the path-liveness mask. -/
theorem checkLive_pathLiveMask (p : Prog N) : checkLive p (pathLiveMask p) = true :=
  (checkLive_eq_true_iff p _).mpr (pathLiveMask_cert p)

/-- **Path liveness is the least certificate.** The path-liveness mask satisfies both certificate
inequalities, and it is pointwise below every mask that satisfies both. -/
theorem pathLiveMask_least_cert (p : Prog N) :
    (ReadsLive p (pathLiveMask p) ∧ TransferClosed p (pathLiveMask p)) ∧
      ∀ L : Ann N, ReadsLive p L → TransferClosed p L →
        ∀ pc i, pathLiveMask p pc i = true → L pc i = true :=
  ⟨pathLiveMask_cert p, fun _ hR hT _ _ hm =>
    pathLive_imp_mask_of_cert hR hT (pathLiveMask_eq_true.mp hm)⟩

end Toy.SlotCompact
