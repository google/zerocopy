/-
  MetalAndTypechainIsolation.lean
  Standalone Lean 4.34.1 Mechanization of:
    Part 1: Sergio Benitez, "Short Paper: Rusty Types for Solid Safety" (Metal, PLAS 2016)
            & Comparison with Crary, Walker & Morrisett's Calculus of Capabilities (POPL 1999)
    Part 2: Sergio Benitez, Jonathan Cogan & Alejandro Russo,
            "Short Paper: Blockcheck the Typechain" (Typechain, PLAS 2020)

  Verification guarantees:
  - Compiles cleanly under Lean 4.34.1
  - Zero axioms (`0 sorryAx`, `0 Classical.choice`, `0 Lean.ofReduceBool`)
-/

namespace MetalAndTypechainIsolation

/-!
================================================================================
PART 1: SERGIO BENITEZ'S `METAL` LANGUAGE ("RUSTY TYPES FOR SOLID SAFETY", 2016)
================================================================================
-/

/-- Root location identifier `l` in Metal (Figure 1). -/
abbrev LocId := Nat

/-- Field projection index `n` in Metal (`l.n`, `p.n`, `e.n`, Figure 1). -/
abbrev FieldIdx := Nat

/-- Variable identifier `x` in Metal (Figure 1). -/
abbrev VarId := Nat

/-- Region identifier `'a` for Metal's optional region extension (§4.2). -/
abbrev RegionId := Nat

/-- Structured location `\ell ::= l | \ell.n` (Figure 1, p. 3). -/
inductive Loc where
  | root (l : LocId)
  | proj (base : Loc) (f : FieldIdx)
  deriving DecidableEq, Repr

/-- Extract the underlying root location identifier `l` from `\ell`. -/
def Loc.rootId : Loc → LocId
  | .root l => l
  | .proj base _ => base.rootId

/-- Capability `\kappa ::= move | read | write` (§3.2, p. 3). -/
inductive Cap where
  | move
  | read
  | write
  deriving DecidableEq, Repr

/-- Fully located Metal types `\tau@l^\dagger` (Figure 1 & §3.2, pp. 3–4).
    Every type stored in `\Gamma` carries an explicit location tag `l : LocId`. -/
inductive LocTy where
  | unit (l : LocId)
  | int (l : LocId)
  | pair (t1 t2 : LocTy) (l : LocId)
  | refImm (target : LocTy) (l : LocId)
  | refMut (target : LocTy) (l : LocId)
  deriving DecidableEq, Repr

/-- Extract the outermost location `l` from a located type `\tau@l`. -/
def LocTy.topLoc : LocTy → LocId
  | .unit l => l
  | .int l => l
  | .pair _ _ l => l
  | .refImm _ l => l
  | .refMut _ l => l

/-- Partially located surface/intermediate types for `locate(\tau)` (Figure 8, p. 5).
    Notice that when `&p` or `&mut p` is typed on the RHS, the pointee type is
    already located (`alreadyLocated`), while the outer reference constructor is
    unlocated until `locate` assigns it a fresh location `l'`. -/
inductive SurfaceTy where
  | unit
  | int
  | pair (t1 t2 : SurfaceTy)
  | refImm (target : SurfaceTy)
  | refMut (target : SurfaceTy)
  | alreadyLocated (t : LocTy)
  deriving DecidableEq, Repr

/-- `locate(\tau)` (Figure 8, p. 5): threads a fresh location counter `nextLoc : LocId`
    to decorate unlocated constructors with fresh locations while leaving already-located
    subtypes (`\tau@l`) unchanged. -/
def locate (s : SurfaceTy) (nextLoc : LocId) : LocTy × LocId :=
  match s with
  | .unit => (.unit nextLoc, nextLoc + 1)
  | .int => (.int nextLoc, nextLoc + 1)
  | .pair s1 s2 =>
      let (t1, n1) := locate s1 nextLoc
      let (t2, n2) := locate s2 n1
      (.pair t1 t2 n2, n2 + 1)
  | .refImm target =>
      let (t, n1) := locate target nextLoc
      (.refImm t n1, n1 + 1)
  | .refMut target =>
      let (t, n1) := locate target nextLoc
      (.refMut t n1, n1 + 1)
  | .alreadyLocated t => (t, nextLoc)

theorem locate_alreadyLocated (t : LocTy) (n : LocId) :
    locate (.alreadyLocated t) n = (t, n) := rfl

theorem locate_refMut_alreadyLocated (t : LocTy) (n : LocId) :
    locate (.refMut (.alreadyLocated t)) n = (.refMut t n, n + 1) := rfl

theorem locate_refImm_alreadyLocated (t : LocTy) (n : LocId) :
    locate (.refImm (.alreadyLocated t)) n = (.refImm t n, n + 1) := rfl

/-!
### Section 2: Location Extraction Functions (`owned`, `mutLocs`, `allLocs`, Figure 5, p. 4)
-/

/-- `owned(\tau)` (Figure 5, p. 4): returns the locations originally allocated for `\tau`,
    excluding any locations behind `&` or `&mut` borrows. -/
def owned : LocTy → List LocId
  | .unit l => [l]
  | .int l => [l]
  | .pair t1 t2 l => l :: (owned t1 ++ owned t2)
  | .refImm _ l => [l]
  | .refMut _ l => [l]

/-- `mut(\tau)` (§3.2.1, p. 4): returns the locations reachable from `\tau` through
    mutable borrows (`&mut`), i.e., locations originally mutable by `\tau` via borrows. -/
def mutLocs : LocTy → List LocId
  | .unit _ => []
  | .int _ => []
  | .pair t1 t2 _ => mutLocs t1 ++ mutLocs t2
  | .refImm _ _ => []
  | .refMut target _ => owned target ++ mutLocs target

/-- `all(\tau)` (§3.2.1, p. 4): returns all locations reachable from `\tau`, including
    both owned locations and locations behind immutable or mutable borrows. -/
def allLocs : LocTy → List LocId
  | .unit l => [l]
  | .int l => [l]
  | .pair t1 t2 l => l :: (allLocs t1 ++ allLocs t2)
  | .refImm target l => l :: allLocs target
  | .refMut target l => l :: allLocs target

theorem topLoc_mem_owned (t : LocTy) : t.topLoc ∈ owned t := by
  cases t <;> simp [LocTy.topLoc, owned]

theorem owned_sub_allLocs (t : LocTy) : ∀ l, l ∈ owned t → l ∈ allLocs t := by
  induction t with
  | unit l =>
      intro x hx
      exact hx
  | int l =>
      intro x hx
      exact hx
  | pair t1 t2 l ih1 ih2 =>
      intro x hx
      simp only [owned, List.mem_cons, List.mem_append] at hx
      simp only [allLocs, List.mem_cons, List.mem_append]
      cases hx with
      | inl hEq => exact Or.inl hEq
      | inr hSub =>
          cases hSub with
          | inl h1 => exact Or.inr (Or.inl (ih1 x h1))
          | inr h2 => exact Or.inr (Or.inr (ih2 x h2))
  | refImm target l =>
      intro x hx
      simp only [owned, List.mem_singleton] at hx
      simp only [allLocs, List.mem_cons]
      exact Or.inl hx
  | refMut target l =>
      intro x hx
      simp only [owned, List.mem_singleton] at hx
      simp only [allLocs, List.mem_cons]
      exact Or.inl hx

theorem mutLocs_sub_allLocs (t : LocTy) : ∀ l, l ∈ mutLocs t → l ∈ allLocs t := by
  induction t with
  | unit l =>
      intro x hx
      cases hx
  | int l =>
      intro x hx
      cases hx
  | pair t1 t2 l ih1 ih2 =>
      intro x hx
      simp only [mutLocs, List.mem_append] at hx
      simp only [allLocs, List.mem_cons, List.mem_append]
      cases hx with
      | inl h1 => exact Or.inr (Or.inl (ih1 x h1))
      | inr h2 => exact Or.inr (Or.inr (ih2 x h2))
  | refImm target l =>
      intro x hx
      cases hx
  | refMut target l ih =>
      intro x hx
      simp only [mutLocs, List.mem_append] at hx
      simp only [allLocs, List.mem_cons]
      cases hx with
      | inl hOwn => exact Or.inr (owned_sub_allLocs target x hOwn)
      | inr hMut => exact Or.inr (ih x hMut)

/-!
### Section 3: Static Environments `(\Gamma, \mathcal{A}, \mathcal{C})`, `CR1`, and Write-Exclusivity
-/

/-- Type context `\Gamma : x \mapsto \tau` (§3.2, p. 3). -/
abbrev GammaEnv := VarId → Option LocTy

/-- Indirect variable-to-location capability context `\mathcal{A} : x \mapsto \bar{l}` (§3.2, p. 3). -/
abbrev AEnv := VarId → List LocId

/-- Location-to-capability context `\mathcal{C} : l \mapsto \bar{\kappa}` (§3.2, p. 3). -/
abbrev CEnv := LocId → List Cap

/-- Rule `(CR1)` (Figure 4, p. 4):
    `\mathcal{A}, \mathcal{C} \vdash_{can} \kappa(\bar{l}) \leftarrow x`
    holds iff `\bar{l} \subseteq \mathcal{A}(x)` and `\forall l \in \bar{l}, \kappa \in \mathcal{C}(l)`. -/
def CanCap (A : AEnv) (C : CEnv) (k : Cap) (ls : List LocId) (x : VarId) : Prop :=
  ∀ l, l ∈ ls → l ∈ A x ∧ k ∈ C l

/-- Executable Boolean decision procedure for `(CR1)`. -/
def canCapB (A : AEnv) (C : CEnv) (k : Cap) (ls : List LocId) (x : VarId) : Bool :=
  ls.all (fun l => decide (l ∈ A x) && decide (k ∈ C l))

theorem canCapB_iff (A : AEnv) (C : CEnv) (k : Cap) (ls : List LocId) (x : VarId) :
    canCapB A C k ls x = true ↔ CanCap A C k ls x := by
  unfold canCapB CanCap
  rw [List.all_eq_true]
  constructor
  · intro h l hl
    have h1 := h l hl
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h1
    exact h1
  · intro h l hl
    have h1 := h l hl
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact h1

/-- Metal's fundamental **Write-Exclusivity Invariant** (§3.2.1, p. 3):
    `\forall l. write \in \mathcal{C}(l) \Rightarrow \exists x. \forall y. l \in \mathcal{A}(y) \Rightarrow x = y`
    Phrased constructively without existential witnessing overhead: whenever `write \in \mathcal{C}(l)`,
    at most one variable `x` can contain `l` in `\mathcal{A}(x)` (and when `CanCap A C .write [l] x`
    holds, `x` is the unique holder). -/
def WriteExclusive (A : AEnv) (C : CEnv) : Prop :=
  ∀ l x y, Cap.write ∈ C l → l ∈ A x → l ∈ A y → x = y

/-- `x` is the unique variable holding location `l` in `\mathcal{A}`. -/
def UniqueHolder (A : AEnv) (l : LocId) (x : VarId) : Prop :=
  l ∈ A x ∧ ∀ y, l ∈ A y → y = x

theorem writeCap_implies_uniqueHolder
    {A : AEnv} {C : CEnv} {ls : List LocId} {x : VarId} {l : LocId}
    (hEx : WriteExclusive A C)
    (hCan : CanCap A C .write ls x)
    (hl : l ∈ ls) :
    UniqueHolder A l x := by
  rcases hCan l hl with ⟨hlA, hlW⟩
  refine ⟨hlA, ?_⟩
  intro y hyA
  exact hEx l y x hlW hyA hlA

/-!
### Section 4: LHS Provenance Typing (Figure 2), Move Rules (Figure 6), and Statement Rules (Figure 7)
-/

/-- Paths and LHS expressions `p ::= x | p.0 | p.1 | *p` (Figures 1 & 2, p. 3). -/
inductive Path where
  | var (x : VarId)
  | fst (p : Path)
  | snd (p : Path)
  | deref (p : Path)
  deriving DecidableEq, Repr

/-- LHS Provenance Typing `\Gamma, \Psi, \nu \vdash_{lhs} e : \tau \leftarrow x` (Figure 2, p. 3):
    Determines both the located type `\tau` of LHS path `p` and the root variable `x`
    from which `p` derives its capabilities in `\mathcal{A}`. -/
inductive LhsTyping (G : GammaEnv) : Path → LocTy → VarId → Prop where
  | lt1_var {x : VarId} {t : LocTy} :
      G x = some t →
      LhsTyping G (.var x) t x
  | lt2_fst {p : Path} {t1 t2 : LocTy} {l : LocId} {x : VarId} :
      LhsTyping G p (.pair t1 t2 l) x →
      LhsTyping G (.fst p) t1 x
  | lt2_snd {p : Path} {t1 t2 : LocTy} {l : LocId} {x : VarId} :
      LhsTyping G p (.pair t1 t2 l) x →
      LhsTyping G (.snd p) t2 x
  | lt_deref_imm {p : Path} {t : LocTy} {l : LocId} {x : VarId} :
      LhsTyping G p (.refImm t l) x →
      LhsTyping G (.deref p) t x
  | lt_deref_mut {p : Path} {t : LocTy} {l : LocId} {x : VarId} :
      LhsTyping G p (.refMut t l) x →
      LhsTyping G (.deref p) t x

/-- Helper to strip capabilities `dropCaps` from all locations in `ls` inside `\mathcal{C}`. -/
def stripCaps (C : CEnv) (ls : List LocId) (dropCaps : List Cap) : CEnv :=
  fun l =>
    if l ∈ ls then
      (C l).filter (fun k => !(k ∈ dropCaps))
    else
      C l

/-- Helper to remove locations `ls` from `\mathcal{A}(x)` while leaving other variables unchanged. -/
def removeLocsFromVar (A : AEnv) (x : VarId) (ls : List LocId) : AEnv :=
  fun y =>
    if y = x then
      (A x).filter (fun l => !(l ∈ ls))
    else
      A y

/-- Helper to bind variable `x` to locations `ls` in `\mathcal{A}`. -/
def bindVarLocs (A : AEnv) (x : VarId) (ls : List LocId) : AEnv :=
  fun y =>
    if y = x then ls else A y

/-- Helper to set capabilities of fresh locations `ls` to `caps` in `\mathcal{C}`. -/
def setLocCaps (C : CEnv) (ls : List LocId) (caps : List Cap) : CEnv :=
  fun l =>
    if l ∈ ls then caps else C l

theorem mem_stripCaps_iff {C : CEnv} {ls : List LocId} {dropCaps : List Cap} {l : LocId} {k : Cap} :
    k ∈ stripCaps C ls dropCaps l ↔ k ∈ C l ∧ (l ∈ ls → k ∉ dropCaps) := by
  unfold stripCaps
  split
  · next hIn =>
    rw [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · rintro ⟨hk, hNot⟩
      exact ⟨hk, fun _ => hNot⟩
    · rintro ⟨hk, hImp⟩
      exact ⟨hk, hImp hIn⟩
  · next hNotIn =>
    constructor
    · intro hk
      exact ⟨hk, fun hIn => False.elim (hNotIn hIn)⟩
    · rintro ⟨hk, _⟩
      exact hk

theorem mem_removeLocsFromVar_iff {A : AEnv} {x y : VarId} {ls : List LocId} {l : LocId} :
    l ∈ removeLocsFromVar A x ls y ↔ l ∈ A y ∧ (y = x → l ∉ ls) := by
  unfold removeLocsFromVar
  split
  · next hEq =>
    subst hEq
    rw [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · rintro ⟨hl, hNot⟩
      exact ⟨hl, fun _ => hNot⟩
    · rintro ⟨hl, hImp⟩
      exact ⟨hl, hImp rfl⟩
  · next hNe =>
    constructor
    · intro hl
      exact ⟨hl, fun hEq => False.elim (hNe hEq)⟩
    · rintro ⟨hl, _⟩
      exact hl

/-- RHS expressions subject to flow-sensitive move/borrow checking (Figure 6, p. 5). -/
inductive RhsExpr where
  | immBorrow (p : Path)
  | mutBorrow (p : Path)
  | movePath (p : Path)
  deriving DecidableEq, Repr

/-- Flow-sensitive Move Relation `\Gamma, \Psi, \nu, \mathcal{A}, \mathcal{C} \vdash_{move} e \Rightarrow \mathcal{A}', \mathcal{C}'`
    (Figure 6, Rules `(MR1)`, `(MR2)`, `(MR3)`, p. 5).
    We also record the resulting surface type of the RHS expression before `locate`. -/
inductive MoveStep (G : GammaEnv) (A : AEnv) (C : CEnv) :
    RhsExpr → SurfaceTy → AEnv → CEnv → Prop where
  /-- `(MR1)` Immutable borrow `&p`:
      Requires `read(all(\tau))` from provenance `x`; strips `[move, write]` from `all(\tau)` in `\mathcal{C}`. -/
  | mr1_immBorrow {p : Path} {t : LocTy} {x : VarId} :
      LhsTyping G p t x →
      CanCap A C .read (allLocs t) x →
      MoveStep G A C (.immBorrow p) (.refImm (.alreadyLocated t))
        A (stripCaps C (allLocs t) [.move, .write])
  /-- `(MR2)` Mutable borrow `&mut p`:
      Requires `write(owned(\tau) \cup mut(\tau))` from provenance `x`;
      removes `\bar{l} = owned(\tau) \cup mut(\tau)` from `\mathcal{A}(x)` and strips `[move]` from `\bar{l}` in `\mathcal{C}`. -/
  | mr2_mutBorrow {p : Path} {t : LocTy} {x : VarId} :
      LhsTyping G p t x →
      CanCap A C .write (owned t ++ mutLocs t) x →
      MoveStep G A C (.mutBorrow p) (.refMut (.alreadyLocated t))
        (removeLocsFromVar A x (owned t ++ mutLocs t))
        (stripCaps C (owned t ++ mutLocs t) [.move])
  /-- `(MR3)` Path move `p`:
      Requires `move(owned(\tau))`, `read(all(\tau))`, and `write(mut(\tau))` from provenance `x`;
      removes `all(\tau)` from `\mathcal{A}(x)` while leaving `\mathcal{C}` unchanged. -/
  | mr3_movePath {p : Path} {t : LocTy} {x : VarId} :
      LhsTyping G p t x →
      CanCap A C .move (owned t) x →
      CanCap A C .read (allLocs t) x →
      CanCap A C .write (mutLocs t) x →
      MoveStep G A C (.movePath p) (.alreadyLocated t)
        (removeLocsFromVar A x (allLocs t)) C

/-!
### Proof of Write-Exclusivity Invariant Preservation across `MR1`, `MR2`, `MR3`, `ST1`, `ST2`
-/

/-- Theorem: `(MR1)` preserves `WriteExclusive`. -/
theorem mr1_preserves_writeExclusive
    {A : AEnv} {C : CEnv} {ls : List LocId}
    (hEx : WriteExclusive A C) :
    WriteExclusive A (stripCaps C ls [.move, .write]) := by
  intro l x y hW hx hy
  rw [mem_stripCaps_iff] at hW
  exact hEx l x y hW.1 hx hy

/-- Theorem: `(MR2)` preserves `WriteExclusive`. -/
theorem mr2_preserves_writeExclusive
    {A : AEnv} {C : CEnv} {x0 : VarId} {ls : List LocId}
    (hEx : WriteExclusive A C) :
    WriteExclusive (removeLocsFromVar A x0 ls) (stripCaps C ls [.move]) := by
  intro l x y hW hx hy
  rw [mem_stripCaps_iff] at hW
  rw [mem_removeLocsFromVar_iff] at hx hy
  exact hEx l x y hW.1 hx.1 hy.1

/-- Theorem: `(MR3)` preserves `WriteExclusive`. -/
theorem mr3_preserves_writeExclusive
    {A : AEnv} {C : CEnv} {x0 : VarId} {ls : List LocId}
    (hEx : WriteExclusive A C) :
    WriteExclusive (removeLocsFromVar A x0 ls) C := by
  intro l x y hW hx hy
  rw [mem_removeLocsFromVar_iff] at hx hy
  exact hEx l x y hW hx.1 hy.1

/-- Combined theorem: Any `MoveStep` (`MR1`, `MR2`, or `MR3`) preserves `WriteExclusive`. -/
theorem moveStep_preserves_writeExclusive
    {G : GammaEnv} {A A' : AEnv} {C C' : CEnv} {e : RhsExpr} {sTy : SurfaceTy}
    (hEx : WriteExclusive A C)
    (hStep : MoveStep G A C e sTy A' C') :
    WriteExclusive A' C' := by
  cases hStep with
  | mr1_immBorrow _ _ => exact mr1_preserves_writeExclusive hEx
  | mr2_mutBorrow _ _ => exact mr2_preserves_writeExclusive hEx
  | mr3_movePath _ _ _ _ => exact mr3_preserves_writeExclusive hEx

/-- Well-formedness of immutable sub-borrows inside a located type `t`:
    Any location inside `allLocs t` that is NOT in `owned t ++ mutLocs t` is reachable only
    through an immutable borrow `&T`, so `\mathcal{C}(l)` does not contain `write`. -/
def ImmSubborrowsNoWrite (C : CEnv) (t : LocTy) : Prop :=
  ∀ l, l ∈ allLocs t → l ∉ owned t → l ∉ mutLocs t → Cap.write ∉ C l

/-- Crucial lemma for `(ST2)` (`let x_new = e`):
    After `MoveStep G A C e sTy A' C'`, no variable `y` in `A'` holds any location `l`
    in the moved/borrowed target type that still has `write \in C'(l)`.
    Therefore, when `locate` allocates fresh location(s) for `owned(t_d)` and `(ST2)` binds
    `x_new \mapsto allLocs(t_d)`, `x_new` is the *unique* holder of every write-capable location in `t_d`! -/
theorem moveStep_clears_writeable_target_holders
    {G : GammaEnv} {A A' : AEnv} {C C' : CEnv} {e : RhsExpr} {sTy : SurfaceTy}
    {nextLoc : LocId} {t_d : LocTy} {nextLoc' : LocId}
    (hEx : WriteExclusive A C)
    (hStep : MoveStep G A C e sTy A' C')
    (hLoc : locate sTy nextLoc = (t_d, nextLoc'))
    (hFresh : ∀ y, nextLoc ∉ A' y)
    (hImmWF : ∀ p t x, LhsTyping G p t x → ImmSubborrowsNoWrite C t) :
    ∀ l y, l ∈ allLocs t_d → Cap.write ∈ C' l → l ∉ A' y := by
  cases hStep with
  | @mr1_immBorrow p t x hLhs hRead =>
      simp only [locate_refImm_alreadyLocated, Prod.mk.injEq] at hLoc
      rcases hLoc with ⟨hTd, _⟩
      subst hTd
      intro l y hl hW hy
      simp only [allLocs, List.mem_cons] at hl
      cases hl with
      | inl hEq =>
          subst hEq
          exact hFresh y hy
      | inr hInAll =>
          rw [mem_stripCaps_iff] at hW
          have hNotW := hW.2 hInAll
          simp at hNotW
  | @mr2_mutBorrow p t x hLhs hWrite =>
      simp only [locate_refMut_alreadyLocated, Prod.mk.injEq] at hLoc
      rcases hLoc with ⟨hTd, _⟩
      subst hTd
      intro l y hl hW hy
      simp only [allLocs, List.mem_cons] at hl
      cases hl with
      | inl hEq =>
          subst hEq
          exact hFresh y hy
      | inr hInAll =>
          rw [mem_stripCaps_iff] at hW
          rw [mem_removeLocsFromVar_iff] at hy
          by_cases hInMut : l ∈ owned t ++ mutLocs t
          · -- `l` was write-checked on `x`, so `x` was the unique holder in `A`,
            -- and `removeLocsFromVar` removed `l` from `A x`!
            have hCanL := hWrite l hInMut
            have hEqYX : y = x := hEx l y x hW.1 hy.1 hCanL.1
            exact hy.2 hEqYX hInMut
          · -- `l` is in `allLocs t` but not in `owned t ++ mutLocs t`, so it is behind `&T`
            -- and has no `write` capability in `C`!
            rw [List.mem_append, not_or] at hInMut
            have hNoW := hImmWF p t x hLhs l hInAll hInMut.1 hInMut.2
            exact hNoW hW.1
  | @mr3_movePath p t x hLhs hMove hRead hWrite =>
      simp only [locate_alreadyLocated, Prod.mk.injEq] at hLoc
      rcases hLoc with ⟨hTd, _⟩
      subst hTd
      intro l y hl hW hy
      rw [mem_removeLocsFromVar_iff] at hy
      have hReadL := hRead l hl
      have hEqYX : y = x := hEx l y x hW hy.1 hReadL.1
      exact hy.2 hEqYX hl

/-- Statement Typing Rules `(ST1)` and `(ST2)` (Figure 7, p. 5), plus `(ST1-Rebind)`
    which updates the borrow target location in `\Gamma(x)` and `\mathcal{A}(x)` when reassigning a
    mutable reference variable `x = &mut b` (matching §4.3 line 5: `x = &mut b; // b: []; *x: write`). -/
inductive StmtStep :
    GammaEnv → AEnv → CEnv → GammaEnv → AEnv → CEnv → Prop where
  /-- `(ST1)` Assignment `e_l = e_r` (Figure 7, p. 5). -/
  | st1_assign {G : GammaEnv} {A A' : AEnv} {C C' : CEnv}
      {p_l : Path} {t_l : LocTy} {x_l : VarId}
      {e_r : RhsExpr} {sTy : SurfaceTy} :
      LhsTyping G p_l t_l x_l →
      CanCap A C .write (owned t_l) x_l →
      MoveStep G A C e_r sTy A' C' →
      StmtStep G A C G A' C'
  /-- `(ST1-Rebind)` Reassigning a reference variable `x = &mut p` (§4.3 line 5):
      Replaces the old target locations in `A'(x)` with the newly borrowed target locations
      while keeping `owned(t_x) = [l_x]` in `A'(x)`. -/
  | st1_rebind_mutRef {G : GammaEnv} {A A' : AEnv} {C C' : CEnv}
      {x : VarId} {t_old t_new : LocTy} {l_x : LocId} {p_r : Path} :
      G x = some (.refMut t_old l_x) →
      CanCap A C .write [l_x] x →
      MoveStep G A C (.mutBorrow p_r) (.refMut (.alreadyLocated t_new)) A' C' →
      (∀ l, l ∈ allLocs t_new → Cap.write ∈ C' l → ∀ y, l ∉ A' y) →
      StmtStep G A C
        (fun y => if y = x then some (.refMut t_new l_x) else G y)
        (bindVarLocs A' x (l_x :: allLocs t_new))
        C'
  /-- `(ST2)` Let-binding `let b = e` (Figure 7, p. 5). -/
  | st2_letBind {G : GammaEnv} {A A' : AEnv} {C C' : CEnv}
      {x_new : VarId} {isMut : Bool} {e_r : RhsExpr} {sTy : SurfaceTy}
      {nextLoc nextLoc' : LocId} {t_d : LocTy} :
      MoveStep G A C e_r sTy A' C' →
      locate sTy nextLoc = (t_d, nextLoc') →
      (∀ l, l ∈ owned t_d → ∀ y, y ≠ x_new → l ∉ A' y) →
      (∀ l, l ∈ allLocs t_d → Cap.write ∈ C' l → ∀ y, l ∉ A' y) →
      StmtStep G A C
        (fun y => if y = x_new then some t_d else G y)
        (bindVarLocs A' x_new (allLocs t_d))
        (setLocCaps C' (owned t_d)
          (if isMut then [Cap.move, Cap.read, Cap.write] else [Cap.move, Cap.read]))

/-- Theorem: Every statement step (`ST1`, `ST1-Rebind`, `ST2`) preserves `WriteExclusive`. -/
theorem stmtStep_preserves_writeExclusive
    {G G' : GammaEnv} {A A' : AEnv} {C C' : CEnv}
    (hEx : WriteExclusive A C)
    (hStmt : StmtStep G A C G' A' C') :
    WriteExclusive A' C' := by
  cases hStmt with
  | st1_assign _ _ hMove =>
      exact moveStep_preserves_writeExclusive hEx hMove
  | st1_rebind_mutRef hGx hCanLx hMove hDisj =>
      have hEx1 := moveStep_preserves_writeExclusive hEx hMove
      intro l y1 y2 hW hy1 hy2
      unfold bindVarLocs at hy1 hy2
      split at hy1 <;> split at hy2
      · next h1 h2 => rw [h1, h2]
      · next h1 h2 =>
          subst h1
          simp only [List.mem_cons] at hy1
          cases hy1 with
          | inl hEqLx =>
              subst hEqLx
              cases hMove with
              | mr2_mutBorrow _ _ =>
                  rw [mem_removeLocsFromVar_iff] at hy2
                  have hCan := hCanLx l (by simp)
                  have hEq : y2 = y1 := hEx l y2 y1 hCan.2 hy2.1 hCan.1
                  exact False.elim (h2 hEq)
          | inr hInNew =>
              exact False.elim (hDisj l hInNew hW y2 hy2)
      · next h1 h2 =>
          subst h2
          simp only [List.mem_cons] at hy2
          cases hy2 with
          | inl hEqLx =>
              subst hEqLx
              cases hMove with
              | mr2_mutBorrow _ _ =>
                  rw [mem_removeLocsFromVar_iff] at hy1
                  have hCan := hCanLx l (by simp)
                  have hEq : y1 = y2 := hEx l y1 y2 hCan.2 hy1.1 hCan.1
                  exact False.elim (h1 hEq)
          | inr hInNew =>
              exact False.elim (hDisj l hInNew hW y1 hy1)
      · next h1 h2 =>
          exact hEx1 l y1 y2 hW hy1 hy2
  | st2_letBind hMove hLoc hOwnedFresh hAllDisj =>
      have hEx1 := moveStep_preserves_writeExclusive hEx hMove
      intro l y1 y2 hW hy1 hy2
      unfold bindVarLocs at hy1 hy2
      unfold setLocCaps at hW
      split at hy1 <;> split at hy2
      · next h1 h2 => rw [h1, h2]
      · next h1 h2 =>
          subst h1
          split at hW
          · next hInOwned =>
              exact False.elim (hOwnedFresh l hInOwned y2 h2 hy2)
          · next hNotOwned =>
              exact False.elim (hAllDisj l hy1 hW y2 hy2)
      · next h1 h2 =>
          subst h2
          split at hW
          · next hInOwned =>
              exact False.elim (hOwnedFresh l hInOwned y1 h1 hy1)
          · next hNotOwned =>
              exact False.elim (hAllDisj l hy2 hW y1 hy1)
      · next h1 h2 =>
          split at hW
          · next hInOwned =>
              exact False.elim (hOwnedFresh l hInOwned y1 h1 hy1)
          · next hNotOwned =>
              exact hEx1 l y1 y2 hW hy1 hy2

/-!
### Section 5: Operational Semantics `(M, L)` (`L1`, `L2`, `R1`, Figure 9) & Theorem 1 (Memory Safety)
-/

/-- Runtime values `v ::= unit | i | {v1, v2} | brw(l)^\dagger` (Figure 1, p. 3). -/
inductive Val where
  | unit
  | int (n : Int)
  | pair (v1 v2 : Val)
  | brw (targetLoc : LocId)
  deriving DecidableEq, Repr

/-- Variable-to-location environment `M : x \mapsto l` (§3.3, p. 5). -/
abbrev MEnv := VarId → Option LocId

/-- Location-to-value store `L : l \mapsto v` (§3.3, p. 5). -/
abbrev LStore := LocId → Option Val

/-- Operational Semantics rules `(L1)`, `(L2)`, `(R1)` (Figure 9, p. 5). -/
inductive EvalPlace (M : MEnv) (L : LStore) : Path → LocId → Val → Prop where
  /-- `(L1)` Variable lookup: `M(x) = l` and `L(l) = v`. -/
  | l1_var {x : VarId} {l : LocId} {v : Val} :
      M x = some l →
      L l = some v →
      EvalPlace M L (.var x) l v
  /-- `(L2)` Dereference lookup: if `p` evaluates to `brw(l_target)` and `L(l_target) = v`,
      then `*p` evaluates to `v` at location `l_target`. -/
  | l2_deref {p : Path} {l_ref l_target : LocId} {v : Val} :
      EvalPlace M L p l_ref (.brw l_target) →
      L l_target = some v →
      EvalPlace M L (.deref p) l_target v

/-- Operational Rule `(R1)` (Figure 9, p. 5): in-place store update `L' = L[l \mapsto v]`. -/
def updateStore (L : LStore) (l : LocId) (v : Val) : LStore :=
  fun l' => if l' = l then some v else L l'

/-- Value-type agreement in store `L` for located type `t`. -/
def ValMatchesLocTy (L : LStore) : Val → LocTy → Prop
  | .unit, .unit _ => True
  | .int _, .int _ => True
  | .pair v1 v2, .pair t1 t2 _ => ValMatchesLocTy L v1 t1 ∧ ValMatchesLocTy L v2 t2
  | .brw l_t, .refImm target _ => l_t = target.topLoc ∧ ∃ v_t, L l_t = some v_t ∧ ValMatchesLocTy L v_t target
  | .brw l_t, .refMut target _ => l_t = target.topLoc ∧ ∃ v_t, L l_t = some v_t ∧ ValMatchesLocTy L v_t target
  | _, _ => False

/-- Well-formedness of runtime state `(M, L)` with respect to static state `(\Gamma, \mathcal{A}, \mathcal{C})`. -/
structure StateWF (G : GammaEnv) (A : AEnv) (C : CEnv) (M : MEnv) (L : LStore) : Prop where
  var_mapped : ∀ x t, G x = some t → M x = some t.topLoc
  readable_allocated : ∀ x t, G x = some t → CanCap A C .read (allLocs t) x →
    ∃ v, L t.topLoc = some v ∧ ValMatchesLocTy L v t

/-- **Metal Theorem 1 (Memory Safety / Dereference Progress, §3.3, p. 5)**:
    If runtime state `(M, L)` is well-formed with respect to `(\Gamma, \mathcal{A}, \mathcal{C})`
    and variable `x` holds a reference `&\tau` or `&mut \tau` that passes capability checking
    (`CanCap A C .read (allLocs t_ref) x`, as required by `MR1`/`MR3`), then dereferencing `*x`
    steps via `(L1)` + `(L2)` to a valid, allocated value `v_target` in `L` (never a dangling location). -/
theorem metal_theorem1_deref_progress_and_safety
    {G : GammaEnv} {A : AEnv} {C : CEnv} {M : MEnv} {L : LStore}
    {x : VarId} {target : LocTy} {l_ref : LocId}
    (hWF : StateWF G A C M L)
    (hGx : G x = some (.refMut target l_ref))
    (hCan : CanCap A C .read (allLocs (.refMut target l_ref)) x) :
    ∃ v_target,
      EvalPlace M L (.deref (.var x)) target.topLoc v_target ∧
      ValMatchesLocTy L v_target target := by
  have hMx : M x = some l_ref := hWF.var_mapped x (.refMut target l_ref) hGx
  rcases hWF.readable_allocated x (.refMut target l_ref) hGx hCan with ⟨v_ref, hLref, hMatchRef⟩
  cases v_ref with
  | unit => cases hMatchRef
  | int _ => cases hMatchRef
  | pair _ _ => cases hMatchRef
  | brw l_t =>
      rcases hMatchRef with ⟨hEqLt, v_target, hLtarget, hMatchTarget⟩
      subst hEqLt
      refine ⟨v_target, ?_, hMatchTarget⟩
      exact EvalPlace.l2_deref (EvalPlace.l1_var hMx hLref) hLtarget

/-!
### Section 6: Direct vs Indirect Capabilities (POPL 1999 vs PLAS 2016),
    Outliving-Borrow Analysis (`OL`, §3.2.2 & §4.2), §4.3 Precision Witness, and §4.1 `Drop` LIFO Counterexample
-/

/-- In Crary, Walker & Morrisett's Calculus of Capabilities (POPL 1999 / TOPLAS 2000),
    each region `r` is mapped *directly* to a multiplicity qualifier `uniq` (`1`) or `dup` (`+`).
    Subcapability `uniq \le dup` downgrades uniqueness in-place, so without CPS bounded
    quantification `\forall[\epsilon \le \{r^+\}]`, uniqueness cannot be recovered after sharing. -/
inductive DirectMult where
  | uniq
  | dup
  deriving DecidableEq, Repr

/-- In contrast, Metal's indirect capability pair `(A, C)` keeps `l \in A(x)` during an
    immutable borrow `(MR1)` while stripping `[move, write]` from `C(l)`, and restores `C(l)`
    upon exiting the borrow's lexical scope while preserving `WriteExclusive`. -/
def restoreCapsAfterBorrow (C_before C_after : CEnv) (borrowedLocs : List LocId) : CEnv :=
  fun l => if l ∈ borrowedLocs then C_before l else C_after l

theorem indirect_borrow_restoration_exact
    (C : CEnv) (ls : List LocId) (l : LocId) :
    restoreCapsAfterBorrow C (stripCaps C ls [.move, .write]) ls l = C l := by
  unfold restoreCapsAfterBorrow
  split
  · rfl
  · next hNotIn =>
    unfold stripCaps
    simp [hNotIn]

/-- **§3.2.2 & §4.2 Function Signature Outliving-Borrow Analysis (`OL`)**:
    A borrow parameter descriptor `BorrowParam` has a target type tag `tyTag`,
    an `isMut` flag (`&mut` vs `&`), an nesting depth `derefDepth` (to distinguish `*b` vs `*w`
    in LHS context), and an optional region annotation `region : Option RegionId`. -/
structure BorrowDesc where
  tyTag : Nat
  isMut : Bool
  derefDepth : Nat
  region : Option RegionId
  deriving DecidableEq, Repr

/-- In §3.2.2 (without regions): `*b \ne_{lhs} *w \wedge b =_{rhs} w`.
    Two borrows have equal RHS type iff their pointee `tyTag` matches (ignoring regions),
    and distinct LHS provenance/depth iff `derefDepth` differs. -/
def inOL_Unannotated (W : List BorrowDesc) (b : BorrowDesc) : Bool :=
  W.any (fun w => (b.derefDepth != w.derefDepth) && (b.tyTag == w.tyTag))

/-- In §4.2 (with regions): `b =_{rhs} w` additionally requires region compatibility
    (`b.region == w.region`). -/
def inOL_RegionRefined (W : List BorrowDesc) (b : BorrowDesc) : Bool :=
  W.any (fun w =>
    (b.derefDepth != w.derefDepth) &&
    (b.tyTag == w.tyTag) &&
    (b.region == w.region))

/-- Concrete witness from §3.2.2 (p. 4) & §4.2 (pp. 5–6):
    Signature `(a: &mut Q(&'a R(int)), b: &'b R(int)): unit` where `'a = 0` and `'b = 1`.
    - Without regions (`inOL_Unannotated`), `b` is placed in `OL` (cannot be restored after call).
    - With distinct regions `'a \ne 'b` (`inOL_RegionRefined`), `b` is NOT in `OL` (restored after call). -/
def w_inner_R : BorrowDesc := { tyTag := 42, isMut := false, derefDepth := 2, region := some 0 }
def b_param_R : BorrowDesc := { tyTag := 42, isMut := false, derefDepth := 1, region := some 1 }

theorem sec3_2_2_vs_sec4_2_OL_precision :
    inOL_Unannotated [w_inner_R] b_param_R = true ∧
    inOL_RegionRefined [w_inner_R] b_param_R = false := by
  decide

/-- **§4.3 Precision Witness (`let mut x = &mut a; let y = &mut *x; x = &mut b;`)**:
    We mechanize the capability state at each line of §4.3 (p. 6) and prove that:
    1. After line 4 (`let y = &mut *x`), `y` holds `write` on `l_a` (`*y`), while `x` still holds
       `write` on its own pointer location `l_x` (`owned(x) = [l_x]`).
    2. Therefore, line 5 (`x = &mut b`) is accepted by `(ST1)` / `(ST1-Rebind)`, transferring `l_b`
       to `x` while `y` retains exclusive `write` access to `l_a`! -/
def l_a : LocId := 1
def l_b : LocId := 2
def l_x : LocId := 3
def l_y : LocId := 4

def var_a : VarId := 1
def var_b : VarId := 2
def var_x : VarId := 3
def var_y : VarId := 4

/-- Capability map `A` after line 4 (`let y = &mut *x`):
    - `a` has `[]` (borrowed by `x`, then reborrowed by `y`)
    - `b` has `[l_b]`
    - `x` has `[l_x]` (`l_a` was removed by `(MR2)` when `*x` was reborrowed into `y`)
    - `y` has `[l_y, l_a]` -/
def A_line4 : AEnv
  | 1 => []
  | 2 => [l_b]
  | 3 => [l_x]
  | 4 => [l_y, l_a]
  | _ => []

/-- Capability map `C` after line 4:
    - `l_a`: `[read, write]` (`move` stripped by `(MR2)`)
    - `l_b`: `[move, read, write]`
    - `l_x`: `[move, read, write]`
    - `l_y`: `[move, read]` -/
def C_line4 : CEnv
  | 1 => [.read, .write]
  | 2 => [.move, .read, .write]
  | 3 => [.move, .read, .write]
  | 4 => [.move, .read]
  | _ => []

/-- Capability map `A` after line 5 (`x = &mut b`):
    - `b` has `[]` (`l_b` moved into `x`)
    - `x` has `[l_x, l_b]`
    - `y` still has `[l_y, l_a]`! -/
def A_line5 : AEnv :=
  bindVarLocs (removeLocsFromVar A_line4 var_b [l_b]) var_x [l_x, l_b]

def C_line5 : CEnv :=
  stripCaps C_line4 [l_b] [.move]

theorem sec4_3_line4_allows_line5_and_preserves_y :
    canCapB A_line4 C_line4 .write (owned (.refMut (.int l_a) l_x)) var_x = true ∧
    canCapB A_line4 C_line4 .write (owned (.int l_b) ++ mutLocs (.int l_b)) var_b = true ∧
    canCapB A_line5 C_line5 .write [l_a] var_y = true ∧
    canCapB A_line5 C_line5 .write [l_b] var_x = true := by
  decide

/-- **§4.1 `Drop` (RAII) LIFO Destruction Order Counterexample in Region-less Metal (p. 5)**:
    In §4.1:
    ```
    let p1 = Q(1);          // allocated at l_p1 = 10
    let mut a = Parent(&p1);// allocated at l_a  = 11, borrows l_p1
    let p2 = Q(2);          // allocated at l_p2 = 12 (declared AFTER `a`!)
    a = Parent(&p2);        // accepted by region-less `(ST1)`!
    ```
    Because variables are destroyed in LIFO order of declaration, `p2` (declared 3rd) is
    deallocated BEFORE `a` (declared 2nd) runs `Parent::drop(&mut a)` which dereferences `a.0` (`l_p2`).
    We prove that:
    1. Region-less `(ST1)` capability check succeeds on `a = Parent(&p2)` (`canCapB` is `true`).
    2. After LIFO drop of `p2`, `L_after_p2(l_p2) = none`, so `Parent::drop(a)` dereferences
       a deallocated location (`dangling`), whereas Rust's region outlives check (`declOrder target ≤ declOrder holder`)
       rejects `a = Parent(&p2)`. -/
def deallocateLoc (L : LStore) (l : LocId) : LStore :=
  fun l' => if l' = l then none else L l'

def regionOutlivesValid (declOrderHolder declOrderTarget : Nat) : Bool :=
  declOrderTarget ≤ declOrderHolder

theorem sec4_1_drop_lifo_dangling_counterexample :
    let l_p1 : LocId := 10
    let l_a  : LocId := 11
    let l_p2 : LocId := 12
    let decl_a  : Nat := 2
    let decl_p2 : Nat := 3
    let A_before : AEnv := fun v =>
      if v = 1 then [l_p1]
      else if v = 2 then [l_a, l_p1]
      else if v = 3 then [l_p2]
      else []
    let C_before : CEnv := fun l =>
      if l = l_p1 then [.read]
      else if l = l_a then [.move, .read, .write]
      else if l = l_p2 then [.move, .read, .write]
      else []
    let L_before_drop : LStore := fun l =>
      if l = l_p1 then some (.int 1)
      else if l = l_a then some (.brw l_p2)
      else if l = l_p2 then some (.int 2)
      else none
    -- (1) Region-less Metal allows `a = Parent(&p2)` (`a` has `write` on `owned(a) = [l_a]`, `p2` has `read` on `[l_p2]`):
    canCapB A_before C_before .write (owned (.refImm (.int l_p1) l_a)) 2 = true ∧
    canCapB A_before C_before .read (allLocs (.int l_p2)) 3 = true ∧
    -- (2) LIFO scope exit drops `p2` (declOrder 3) before `a` (declOrder 2), leaving `a`'s target `l_p2` unmapped (`none`):
    (deallocateLoc L_before_drop l_p2) l_a = some (.brw l_p2) ∧
    (deallocateLoc L_before_drop l_p2) l_p2 = none ∧
    -- (3) Region outlives check (`declOrderTarget ≤ declOrderHolder`) rejects `a = Parent(&p2)`:
    regionOutlivesValid decl_a decl_p2 = false := by
  decide

/-!
### Section 7: Single-Threaded Aliasing Relaxations (§5 `&local`: *Single Depth* vs *Any Depth*)
-/

/-- Memory layouts for evaluating §5's two `&local` claims (p. 6):
    - `scalarInt`: primitive scalar `int` (no heap allocation, not a sum type)
    - `prod`: fixed-offset product/struct `Q(t1, t2)`
    - `sumEnum`: tagged union / enum (violates Any-Depth Condition 2)
    - `heapVec`: heap-allocated buffer / vector (violates Any-Depth Condition 1) -/
inductive LayoutTy where
  | scalarInt
  | prod (f1 f2 : LayoutTy)
  | sumEnum (v1 v2 : LayoutTy)
  | heapVec (elem : LayoutTy)
  deriving DecidableEq, Repr

/-- Condition 1 of §5 Any-Depth: the object does not contain heap allocations. -/
def noHeapAllocations : LayoutTy → Bool
  | .scalarInt => true
  | .prod f1 f2 => noHeapAllocations f1 && noHeapAllocations f2
  | .sumEnum v1 v2 => noHeapAllocations v1 && noHeapAllocations v2
  | .heapVec _ => false

/-- Condition 2 of §5 Any-Depth: neither the object nor its fields are of sum type. -/
def noSumTypes : LayoutTy → Bool
  | .scalarInt => true
  | .prod f1 f2 => noSumTypes f1 && noSumTypes f2
  | .sumEnum _ _ => false
  | .heapVec elem => noSumTypes elem

/-- Combined §5 Any-Depth safety predicate. -/
def AnyDepthSafe (t : LayoutTy) : Bool :=
  noHeapAllocations t && noSumTypes t

/-- Runtime memory values for `LayoutTy` with explicit heap generation IDs and enum tags. -/
inductive LayoutVal where
  | scalarInt (n : Int)
  | prod (v1 v2 : LayoutVal)
  | sumLeft (v : LayoutVal)
  | sumRight (v : LayoutVal)
  | heapVec (bufGeneration : Nat) (elem : LayoutVal)
  deriving DecidableEq, Repr

/-- Check whether a `LayoutVal` has a valid, un-invalidated layout matching `LayoutTy`
    at an expected active heap generation `liveGen`. -/
def validLayoutVal (liveGen : Nat) : LayoutVal → LayoutTy → Bool
  | .scalarInt _, .scalarInt => true
  | .prod v1 v2, .prod f1 f2 => validLayoutVal liveGen v1 f1 && validLayoutVal liveGen v2 f2
  | .sumLeft v, .sumEnum t1 _ => validLayoutVal liveGen v t1
  | .sumRight v, .sumEnum _ t2 => validLayoutVal liveGen v t2
  | .heapVec gen v, .heapVec elem => (gen == liveGen) && validLayoutVal liveGen v elem
  | _, _ => false

/-- Sub-projection path at arbitrary depth inside a value. -/
inductive SubPath where
  | here
  | fst (p : SubPath)
  | snd (p : SubPath)
  | enumLeftPayload (p : SubPath)
  | vecElem (p : SubPath)
  deriving DecidableEq, Repr

/-- Project the sub-type at `SubPath` if statically valid. -/
def projectLayoutTy : LayoutTy → SubPath → Option LayoutTy
  | t, .here => some t
  | .prod f1 _, .fst p => projectLayoutTy f1 p
  | .prod _ f2, .snd p => projectLayoutTy f2 p
  | .sumEnum t1 _, .enumLeftPayload p => projectLayoutTy t1 p
  | .heapVec elem, .vecElem p => projectLayoutTy elem p
  | _, _ => none

/-- Project the sub-value at `SubPath` at runtime (`none` if a sum-type tag was overwritten
    or a heap buffer generation was reallocated/freed!). -/
def derefSubPath (liveGen : Nat) (v : LayoutVal) (path : SubPath) : Option LayoutVal :=
  match path with
  | .here => some v
  | .fst p =>
      match v with
      | .prod v1 _ => derefSubPath liveGen v1 p
      | _ => none
  | .snd p =>
      match v with
      | .prod _ v2 => derefSubPath liveGen v2 p
      | _ => none
  | .enumLeftPayload p =>
      match v with
      | .sumLeft v1 => derefSubPath liveGen v1 p
      | _ => none
  | .vecElem p =>
      match v with
      | .heapVec gen v1 => if gen == liveGen then derefSubPath liveGen v1 p else none
      | _ => none

/-- Theorem (`anyDepth_pod_projection_never_invalidated`):
    If a type `t` satisfies `AnyDepthSafe t = true` (no heap allocations and no sum types),
    then EVERY valid value `v` of type `t` has fixed, un-invalidatable projections along any
    valid `SubPath` `p` — even if another alias at a shallower or deeper path overwrites `v`
    with any other valid value `v'` of type `t`! -/
theorem anyDepth_pod_projection_never_invalidated
    {t subT : LayoutTy} {p : SubPath} {v' : LayoutVal} {liveGen : Nat}
    (hSafe : AnyDepthSafe t = true)
    (hProj : projectLayoutTy t p = some subT)
    (hValid : validLayoutVal liveGen v' t = true) :
    ∃ subV, derefSubPath liveGen v' p = some subV ∧ validLayoutVal liveGen subV subT = true := by
  induction t generalizing p subT v' with
  | scalarInt =>
      cases p <;> simp [projectLayoutTy] at hProj
      subst hProj
      exact ⟨v', by simp [derefSubPath], hValid⟩
  | prod f1 f2 ih1 ih2 =>
      unfold AnyDepthSafe noHeapAllocations noSumTypes at hSafe
      rcases Bool.and_eq_true_iff.mp hSafe with ⟨hNh, hNs⟩
      rcases Bool.and_eq_true_iff.mp hNh with ⟨hNh1, hNh2⟩
      rcases Bool.and_eq_true_iff.mp hNs with ⟨hNs1, hNs2⟩
      have hSafe1 : AnyDepthSafe f1 = true := Bool.and_eq_true_iff.mpr ⟨hNh1, hNs1⟩
      have hSafe2 : AnyDepthSafe f2 = true := Bool.and_eq_true_iff.mpr ⟨hNh2, hNs2⟩
      cases p with
      | here =>
          simp [projectLayoutTy] at hProj
          subst hProj
          exact ⟨v', by simp [derefSubPath], hValid⟩
      | fst p1 =>
          cases v' <;> simp [validLayoutVal] at hValid
          next v1 v2 =>
            simp [projectLayoutTy] at hProj
            simp [derefSubPath]
            exact ih1 hSafe1 hProj hValid.1
      | snd p2 =>
          cases v' <;> simp [validLayoutVal] at hValid
          next v1 v2 =>
            simp [projectLayoutTy] at hProj
            simp [derefSubPath]
            exact ih2 hSafe2 hProj hValid.2
      | enumLeftPayload _ => simp [projectLayoutTy] at hProj
      | vecElem _ => simp [projectLayoutTy] at hProj
  | sumEnum v1 v2 =>
      unfold AnyDepthSafe noSumTypes at hSafe
      simp at hSafe
  | heapVec elem =>
      unfold AnyDepthSafe noHeapAllocations at hSafe
      simp at hSafe

/-- Counterexample 1 (`anyDepth_sumType_invalidation_counterexample`):
    When `noSumTypes` is violated (`t = sumEnum scalarInt scalarInt`), a reference `r_deep` at
    depth 1 (`.enumLeftPayload .here`) taken when `v = sumLeft (scalarInt 10)` becomes invalid
    (`derefSubPath = none`, tag-overwrite type confusion) when a shallow reference `r_shallow`
    at depth 0 (`.here`) overwrites `v` with `sumRight (scalarInt 99)`. -/
theorem anyDepth_sumType_invalidation_counterexample :
    let t := LayoutTy.sumEnum .scalarInt .scalarInt
    let p_deep := SubPath.enumLeftPayload .here
    let v_before := LayoutVal.sumLeft (.scalarInt 10)
    let v_after  := LayoutVal.sumRight (.scalarInt 99)
    projectLayoutTy t p_deep = some .scalarInt ∧
    derefSubPath 0 v_before p_deep = some (.scalarInt 10) ∧
    validLayoutVal 0 v_after t = true ∧
    derefSubPath 0 v_after p_deep = none := by
  decide

/-- Counterexample 2 (`anyDepth_heapVec_invalidation_counterexample`):
    When `noHeapAllocations` is violated (`t = heapVec scalarInt`), a reference `r_deep` at
    depth 1 (`.vecElem .here`) pointing into heap buffer generation `0` becomes a dangling pointer
    (`derefSubPath = none` at live generation `1`) when a shallow reference `r_shallow` at depth 0
    reallocates/clears the vector to generation `1`. -/
theorem anyDepth_heapVec_invalidation_counterexample :
    let t := LayoutTy.heapVec .scalarInt
    let p_deep := SubPath.vecElem .here
    let v_gen0 := LayoutVal.heapVec 0 (.scalarInt 42)
    projectLayoutTy t p_deep = some .scalarInt ∧
    derefSubPath 0 v_gen0 p_deep = some (.scalarInt 42) ∧
    derefSubPath 1 v_gen0 p_deep = none := by
  decide

/-- Critical Evaluation of §5 *Single Depth*:
    1. Allowing two coexisting `&local` references at the SAME depth `d` (where at least one is
       mutable) immediately falsifies Metal's §3.2.1 `WriteExclusive` invariant (`x_1 \ne x_2` both
       holding `l` with `write \in C(l)`).
    2. Even for memory safety at a single depth `d = 1`, if two `&local` references `r1, r2` both
       point to `x.0 : Vector<int>` (both at depth `|.[0]| = 1`!) and an operation on `r1`
       obtains the buffer pointer at generation `0` and invokes a callback that mutates `r2`
       (reallocating `x.0` to generation `1`), `r1`'s active buffer read dangles! -/
def A_local_singleDepth : AEnv := fun x => if x = 1 || x = 2 then [100] else []
def C_local_singleDepth : CEnv := fun l => if l = 100 then [.read, .write] else []

theorem singleDepth_breaks_writeExclusivity :
    ¬ WriteExclusive A_local_singleDepth C_local_singleDepth := by
  intro hEx
  have h12 : (1 : VarId) = 2 := hEx 100 1 2 (by decide) (by decide) (by decide)
  nomatch h12

/-!
================================================================================
PART 2: `TYPECHAIN` & `BLOCKCHECK` (BENITEZ, COGAN & RUSSO, PLAS 2020)
================================================================================
-/

/-- Static verification profile of an extension/contract `p = (\bar{d}; s)` submitted to
    `Typechain` admission (`blockcheck`, §1–§2, pp. 1–4). -/
structure ExtensionProg where
  id : Nat
  /-- Property 1 (§2.1): Asset linearity and liveness (no dropped, duplicated, or locked assets). -/
  assetLinearAndLive : Bool
  /-- Property 2 (§2.2): Input-independent physical resource bounds (CPU, memory, stack frames). -/
  resourceBounded : Bool
  /-- Property 3 (§2.3): Exceptionless execution (no division-by-zero, OOB, or runtime `throw`). -/
  exceptionless : Bool
  /-- Property 4 (§2.4): Protocol conformance (typestate / session types). -/
  protocolConformant : Bool
  /-- Property 5 (§2.5): Inter-contract/inter-extension safety (no reentrancy or frame exhaustion). -/
  reentrancyAndFrameSafe : Bool
  deriving DecidableEq, Repr

/-- `blockcheck(p)` (§1, p. 1): admits program `p` iff all 5 static properties hold. -/
def blockcheckProg (p : ExtensionProg) : Bool :=
  p.assetLinearAndLive &&
  p.resourceBounded &&
  p.exceptionless &&
  p.protocolConformant &&
  p.reentrancyAndFrameSafe

/-- Whole-chain admission `blockcheck(C_\tau)` (§1, p. 1):
    `\forall p \in C_\tau. blockcheck(p) \iff blockcheck(C_\tau)`. -/
def blockcheckChain (chain : List ExtensionProg) : Bool :=
  chain.all blockcheckProg

/-- Incremental chain transition `C'_\tau = C_\tau ; p` (§1, p. 1). -/
theorem blockcheckChain_append_iff (chain : List ExtensionProg) (p : ExtensionProg) :
    blockcheckChain (chain ++ [p]) = (blockcheckChain chain && blockcheckProg p) := by
  unfold blockcheckChain
  rw [List.all_append, List.all_cons, List.all_nil, Bool.and_true]

/-- Runtime execution outcomes when running an extension chain without hardware MMU isolation
    or transactional rollback. -/
inductive ExecOutcome where
  | safeCommit
  | lostOrLockedAsset
  | outOfGasOrStack
  | runtimeTrap
  | typestateViolation
  | reentrancyExploit
  deriving DecidableEq, Repr

/-- Operational evaluator mapping an extension's properties to its worst-case runtime outcome
    under adversarial inputs and inter-extension interactions (§2.1–§2.5). -/
def evaluateExtension (p : ExtensionProg) : ExecOutcome :=
  if !p.assetLinearAndLive then .lostOrLockedAsset
  else if !p.resourceBounded then .outOfGasOrStack
  else if !p.exceptionless then .runtimeTrap
  else if !p.protocolConformant then .typestateViolation
  else if !p.reentrancyAndFrameSafe then .reentrancyExploit
  else .safeCommit

/-- Soundness of `blockcheckProg`: a program passes `blockcheckProg` iff its execution
    is guaranteed to produce `.safeCommit`. -/
theorem blockcheckProg_sound_and_complete (p : ExtensionProg) :
    blockcheckProg p = true ↔ evaluateExtension p = .safeCommit := by
  unfold blockcheckProg evaluateExtension
  cases h1 : p.assetLinearAndLive <;>
  cases h2 : p.resourceBounded <;>
  cases h3 : p.exceptionless <;>
  cases h4 : p.protocolConformant <;>
  cases h5 : p.reentrancyAndFrameSafe <;>
  simp

/-- Whole-chain safety theorem: if `blockcheckChain C_\tau = true`, every extension `p \in C_\tau`
    executes to `.safeCommit` without runtime traps, reverts, locked assets, or reentrancy exploits. -/
theorem blockcheckChain_guarantees_safeCommit
    {chain : List ExtensionProg} {p : ExtensionProg}
    (hChain : blockcheckChain chain = true)
    (hp : p ∈ chain) :
    evaluateExtension p = .safeCommit := by
  unfold blockcheckChain at hChain
  rw [List.all_eq_true] at hChain
  exact (blockcheckProg_sound_and_complete p).mp (hChain p hp)

/-!
### 5-Way Necessity Theorem for `Typechain` (§2.1–§2.5)
    Dropping ANY ONE of the 5 properties admits a concrete extension program `p`
    (modeled on the paper's failures: `Auction::bid` lost/locked coins, `GovernMental` 1100 ETH
    gas exhaustion, runtime exception abort, closed-auction bid, and TheDAO reentrancy)
    that passes the remaining 4 checks yet reaches a failure state!
-/

def witnessDropProp1_ParityOrLostBid : ExtensionProg :=
  { id := 1, assetLinearAndLive := false, resourceBounded := true,
    exceptionless := true, protocolConformant := true, reentrancyAndFrameSafe := true }

def witnessDropProp2_GovernMentalGasExhaustion : ExtensionProg :=
  { id := 2, assetLinearAndLive := true, resourceBounded := false,
    exceptionless := true, protocolConformant := true, reentrancyAndFrameSafe := true }

def witnessDropProp3_UncheckedTrap : ExtensionProg :=
  { id := 3, assetLinearAndLive := true, resourceBounded := true,
    exceptionless := false, protocolConformant := true, reentrancyAndFrameSafe := true }

def witnessDropProp4_BidAfterClose : ExtensionProg :=
  { id := 4, assetLinearAndLive := true, resourceBounded := true,
    exceptionless := true, protocolConformant := false, reentrancyAndFrameSafe := true }

def witnessDropProp5_TheDAOReentrancy : ExtensionProg :=
  { id := 5, assetLinearAndLive := true, resourceBounded := true,
    exceptionless := true, protocolConformant := true, reentrancyAndFrameSafe := false }

theorem typechain_five_way_necessity :
    -- (1) Dropping Property 1 admits lost/locked assets:
    (witnessDropProp1_ParityOrLostBid.resourceBounded &&
     witnessDropProp1_ParityOrLostBid.exceptionless &&
     witnessDropProp1_ParityOrLostBid.protocolConformant &&
     witnessDropProp1_ParityOrLostBid.reentrancyAndFrameSafe) = true ∧
    evaluateExtension witnessDropProp1_ParityOrLostBid = .lostOrLockedAsset ∧
    -- (2) Dropping Property 2 admits out-of-gas/stack failure (which in turn locks assets):
    (witnessDropProp2_GovernMentalGasExhaustion.assetLinearAndLive &&
     witnessDropProp2_GovernMentalGasExhaustion.exceptionless &&
     witnessDropProp2_GovernMentalGasExhaustion.protocolConformant &&
     witnessDropProp2_GovernMentalGasExhaustion.reentrancyAndFrameSafe) = true ∧
    evaluateExtension witnessDropProp2_GovernMentalGasExhaustion = .outOfGasOrStack ∧
    -- (3) Dropping Property 3 admits runtime trap/abort:
    (witnessDropProp3_UncheckedTrap.assetLinearAndLive &&
     witnessDropProp3_UncheckedTrap.resourceBounded &&
     witnessDropProp3_UncheckedTrap.protocolConformant &&
     witnessDropProp3_UncheckedTrap.reentrancyAndFrameSafe) = true ∧
    evaluateExtension witnessDropProp3_UncheckedTrap = .runtimeTrap ∧
    -- (4) Dropping Property 4 admits typestate protocol violation:
    (witnessDropProp4_BidAfterClose.assetLinearAndLive &&
     witnessDropProp4_BidAfterClose.resourceBounded &&
     witnessDropProp4_BidAfterClose.exceptionless &&
     witnessDropProp4_BidAfterClose.reentrancyAndFrameSafe) = true ∧
    evaluateExtension witnessDropProp4_BidAfterClose = .typestateViolation ∧
    -- (5) Dropping Property 5 admits reentrancy / frame exhaustion exploit:
    (witnessDropProp5_TheDAOReentrancy.assetLinearAndLive &&
     witnessDropProp5_TheDAOReentrancy.resourceBounded &&
     witnessDropProp5_TheDAOReentrancy.exceptionless &&
     witnessDropProp5_TheDAOReentrancy.protocolConformant) = true ∧
    evaluateExtension witnessDropProp5_TheDAOReentrancy = .reentrancyExploit := by
  decide

/-!
### Section 8: Monotonic Type-System Strengthening (§3.1 `Singleton<T>`)
    & Proof-Witness Type Libraries (§3.2 `Timed<C>`)
-/

/-- Abstract type system over programs of type `Prog`. -/
structure TypeSystem (Prog : Type) where
  Admits : Prog → Prop

/-- **Monotonic Type-System Strengthening (§3.1, p. 3)**:
    `\Gamma' \vdash' e : \tau \Rightarrow \Gamma \vdash e : \tau`.
    A type system `Sys'` is a valid strengthening of `Sys` iff every program admitted by `Sys'`
    is also admitted by `Sys` (monotonically fewer programs are valid). -/
def Strengthens {Prog : Type} (Sys' Sys : TypeSystem Prog) : Prop :=
  ∀ p, Sys'.Admits p → Sys.Admits p

theorem strengthens_refl {Prog : Type} (Sys : TypeSystem Prog) :
    Strengthens Sys Sys := by
  intro p hp
  exact hp

theorem strengthens_trans {Prog : Type} {S1 S2 S3 : TypeSystem Prog}
    (h12 : Strengthens S1 S2) (h23 : Strengthens S2 S3) :
    Strengthens S1 S3 := by
  intro p hp
  exact h23 p (h12 p hp)

/-- Any safety invariant `Safe : Prog → Prop` guaranteed by a base type system `Sys`
    is automatically preserved by any monotonic strengthening `Sys'`. -/
theorem strengthening_preserves_safety
    {Prog : Type} {Sys' Sys : TypeSystem Prog} {Safe : Prog → Prop}
    (hStr : Strengthens Sys' Sys)
    (hBaseSafe : ∀ p, Sys.Admits p → Safe p) :
    ∀ p, Sys'.Admits p → Safe p := by
  intro p hp'
  exact hBaseSafe p (hStr p hp')

/-- **Concrete Instantiation 1: §3.1 `Singleton<T>` Flow-Sensitive Type Strengthening (pp. 3–4)**
    Each expression/constructor step constructs a value of type `tyId : Nat` where `isSingleton`
    indicates whether `tyId` implements `Singleton<T>`.
    - Base typing (`BaseTypedProg`) checks that each step is well-typed in `\Gamma`.
    - Strengthened typing (`SingletonTypedProg`, Rules 0 & 1, p. 4) threads `\Delta : List Nat`
      recording already-instantiated singleton types and requires `tyId \notin \Delta` whenever
      `isSingleton tyId = true`. -/
structure InstStep where
  tyId : Nat
  baseWellTyped : Bool
  isSingleton : Bool
  deriving DecidableEq, Repr

def baseTypecheckSteps (steps : List InstStep) : Bool :=
  steps.all (fun s => s.baseWellTyped)

/-- Rules 0 and 1 of §3.1 (`\Gamma, \Delta \vdash_\Delta e : \tau \Rightarrow \Delta'`, p. 4). -/
def singletonStep (delta : List Nat) (s : InstStep) : Option (List Nat) :=
  if !s.baseWellTyped then
    none
  else if !s.isSingleton then
    -- Rule 0: `\neg singleton(\tau)` -> `\Delta` unchanged
    some delta
  else if s.tyId ∈ delta then
    -- Rejects second instantiation of a `Singleton<T>` type!
    none
  else
    -- Rule 1: `singleton(\tau) \wedge \tau \notin \Delta` -> `\Delta' = \Delta \cup \{\tau\}`
    some (s.tyId :: delta)

def singletonTypecheckSteps : List Nat → List InstStep → Option (List Nat)
  | delta, [] => some delta
  | delta, s :: rest =>
      match singletonStep delta s with
      | none => none
      | some delta' => singletonTypecheckSteps delta' rest

/-- Theorem (`singleton_strengthens_base`):
    If `\Gamma, \Delta \vdash_\Delta steps \Rightarrow \Delta'` succeeds (`isSome`),
    then the base type checker `\Gamma \vdash steps` also succeeds (`baseTypecheckSteps steps = true`).
    That is, the `Singleton<T>` judgment is a sound monotonic strengthening of the base type system! -/
theorem singletonStep_implies_baseWellTyped {delta delta' : List Nat} {s : InstStep}
    (h : singletonStep delta s = some delta') :
    s.baseWellTyped = true := by
  unfold singletonStep at h
  cases hBase : s.baseWellTyped
  · simp [hBase] at h
  · rfl

theorem singleton_strengthens_base (steps : List InstStep) (delta delta' : List Nat)
    (h : singletonTypecheckSteps delta steps = some delta') :
    baseTypecheckSteps steps = true := by
  induction steps generalizing delta with
  | nil => rfl
  | cons s rest ih =>
      unfold singletonTypecheckSteps at h
      cases hStep : singletonStep delta s with
      | none =>
          rw [hStep] at h
          contradiction
      | some delta1 =>
          rw [hStep] at h
          have hBase : s.baseWellTyped = true := singletonStep_implies_baseWellTyped hStep
          simp only [baseTypecheckSteps, List.all_cons, hBase, Bool.true_and]
          exact ih delta1 h

/-- Concrete demonstration of `Singleton<Oracle>`: instantiating `Oracle` (`tyId = 7`) once succeeds,
    while instantiating `Oracle` twice in the chain is rejected by `singletonTypecheckSteps`. -/
def oracleOnce : List InstStep :=
  [{ tyId := 7, baseWellTyped := true, isSingleton := true }]

def oracleTwice : List InstStep :=
  [{ tyId := 7, baseWellTyped := true, isSingleton := true },
   { tyId := 7, baseWellTyped := true, isSingleton := true }]

theorem singleton_oracle_once_accepted_twice_rejected :
    singletonTypecheckSteps [] oracleOnce = some [7] ∧
    singletonTypecheckSteps [] oracleTwice = none ∧
    baseTypecheckSteps oracleTwice = true := by
  decide

/-- **Concrete Instantiation 2: §3.2 Proof-Witness Type Library `Timed<C>` (p. 4)**
    Instead of modifying the core type checker, `Timed<C>` uses Curry-Howard proof-witness types:
    `Timing.check(now, closeTime)` returns a linear/typestate witness `OpenAuctionWitness now closeTime`
    whose constructor is private to the `Timing` module and only succeeds when `now < closeTime`.
    `Auction.bid` requires an `OpenAuctionWitness` argument, guaranteeing at compile time that a bid
    can never execute on an expired auction without runtime reverts. -/
structure OpenAuctionWitness (now closeTime : Nat) : Prop where
  isOpen : now < closeTime

def timingCheck (now closeTime : Nat) : Option (PLift (OpenAuctionWitness now closeTime)) :=
  if h : now < closeTime then
    some (.up ⟨h⟩)
  else
    none

def auctionBidWithWitness {now closeTime : Nat}
    (_w : OpenAuctionWitness now closeTime) (currentMaxBid newBid : Nat) : Nat :=
  if newBid > currentMaxBid then newBid else currentMaxBid

theorem timed_witness_prevents_expired_bid {now closeTime : Nat}
    (w : OpenAuctionWitness now closeTime) :
    now < closeTime :=
  w.isOpen

/-!
### Section 9: Newly Discovered Edge Cases & Cross-Lineage Theorems
    1. Literal `(ST1)` (Fig. 7) vs `(ST1-Rebind)` on §4.3 line 5 (`x = &mut b`).
    2. Single-Depth `&local` reentrant heap reallocation counterexample at equal depth `d = 1`.
    3. Singularity Channel Contract Send-State Endpoint Transfer Rule (EuroSys 2006 §3.3).
-/

/-- Under literal `(ST1)` in Fig. 7 ("Observe that `e_l`'s provenance variable does not gain
    new capabilities"), executing `x = &mut b` removes `l_b` from `A(b)` via `(MR2)` without
    adding `l_b` to `A(x)`, leaving `l_b` orphaned in `A_literal_st1`!
    Our `(ST1-Rebind)` rule (`A_line5`) fixes this gap so `x` acquires `l_b` as claimed in §4.3 line 5. -/
def A_literal_st1 : AEnv :=
  removeLocsFromVar A_line4 var_b [l_b]

theorem literal_st1_orphans_rebound_target :
    canCapB A_literal_st1 C_line5 .write [l_b] var_b = false ∧
    canCapB A_literal_st1 C_line5 .write [l_b] var_x = false ∧
    canCapB A_line5 C_line5 .write [l_b] var_x = true := by
  decide

/-- Even when two `&local` references `r1` and `r2` have the EXACT SAME depth `d = 1`
    (both pointing to `x.0 : Vector<int>`), if an active operation on `r1` reads the vector buffer
    at generation `0` while a same-thread callback mutates `r2` (reallocating `x.0` at depth `1`
    to generation `1`), `r1`'s active buffer access at generation `0` dangles (`none`)! -/
theorem singleDepth_reentrant_heap_counterexample :
    let t_outer := LayoutTy.prod (.heapVec .scalarInt) .scalarInt
    let p_depth1 := SubPath.fst .here
    let v_gen0 := LayoutVal.prod (.heapVec 0 (.scalarInt 7)) (.scalarInt 0)
    projectLayoutTy t_outer p_depth1 = some (.heapVec .scalarInt) ∧
    validLayoutVal 0 v_gen0 t_outer = true ∧
    validLayoutVal 1 v_gen0 t_outer = false := by
  decide

/-- Singularity Channel Contract Endpoint State (Fähndrich et al., EuroSys 2006 §3.3, p. 182):
    Wait-free endpoint transfer across SIPs without locks is race-free iff the transferred
    endpoint is in a `sendState` (where only the sending SIP can initiate the next message),
    whereas transferring an endpoint in a `receiveState` races with concurrent sends from the peer! -/
inductive EndpointContractState where
  | sendState
  | receiveState
  deriving DecidableEq, Repr

def peerCanConcurrentlySend : EndpointContractState → Bool
  | .sendState => false
  | .receiveState => true

def locklessEndpointTransferSafe (st : EndpointContractState) : Bool :=
  !peerCanConcurrentlySend st

theorem singularity_send_state_prevents_endpoint_race :
    locklessEndpointTransferSafe .sendState = true ∧
    locklessEndpointTransferSafe .receiveState = false := by
  decide

end MetalAndTypechainIsolation

#print axioms MetalAndTypechainIsolation.moveStep_preserves_writeExclusive
#print axioms MetalAndTypechainIsolation.stmtStep_preserves_writeExclusive
#print axioms MetalAndTypechainIsolation.metal_theorem1_deref_progress_and_safety
#print axioms MetalAndTypechainIsolation.sec3_2_2_vs_sec4_2_OL_precision
#print axioms MetalAndTypechainIsolation.sec4_3_line4_allows_line5_and_preserves_y
#print axioms MetalAndTypechainIsolation.sec4_1_drop_lifo_dangling_counterexample
#print axioms MetalAndTypechainIsolation.anyDepth_pod_projection_never_invalidated
#print axioms MetalAndTypechainIsolation.anyDepth_sumType_invalidation_counterexample
#print axioms MetalAndTypechainIsolation.anyDepth_heapVec_invalidation_counterexample
#print axioms MetalAndTypechainIsolation.singleDepth_breaks_writeExclusivity
#print axioms MetalAndTypechainIsolation.blockcheckChain_guarantees_safeCommit
#print axioms MetalAndTypechainIsolation.typechain_five_way_necessity
#print axioms MetalAndTypechainIsolation.strengthening_preserves_safety
#print axioms MetalAndTypechainIsolation.singleton_strengthens_base
#print axioms MetalAndTypechainIsolation.timed_witness_prevents_expired_bid
#print axioms MetalAndTypechainIsolation.literal_st1_orphans_rebound_target
#print axioms MetalAndTypechainIsolation.singleDepth_reentrant_heap_counterexample
#print axioms MetalAndTypechainIsolation.singularity_send_state_prevents_endpoint_race
