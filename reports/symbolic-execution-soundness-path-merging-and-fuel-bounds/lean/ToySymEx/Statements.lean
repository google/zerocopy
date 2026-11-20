import ToySymEx.Basic
import ToySymEx.Lemmas
import ToySymEx.Proofs

/-!
Main statements of the package. Proof infrastructure lives in
`ToySymEx.Proofs`.
-/

namespace Toy.SymEx

/-! ## Symbolic evaluation of expressions -/

/-- Symbolic evaluation of a program expression (`e.subst σ`) interpreted under
`ρ` agrees with concrete evaluation of `e` in the instantiated store `σ.inst ρ`. -/
theorem eval_subst (σ : SymStore) (ρ : Valuation) (e : Term) :
    (e.subst σ).eval ρ = e.eval (σ.inst ρ) := by
  exact Proofs.eval_subst_core σ ρ e

/-! ## Per-path soundness -/

/-- Per-path soundness: for every leaf produced by `symExec p f` and every
valuation `ρ` satisfying the leaf's path condition, the concrete run of `p` from
the `ρ`-instantiated initial store with the same fuel `f` has exactly the leaf's
outcome instantiated at `ρ` (same final store, or panic at the same location,
or fuel exhaustion). -/
theorem symExec_leaf_sound (p : Cfg) (f : Nat) (l : Leaf) (hl : l ∈ symExec p f)
    (ρ : Valuation) (hpc : holds l.pc ρ) :
    exec p f (SymStore.init.inst ρ) = l.res.inst ρ := by
  exact Proofs.symExec_leaf_sound_core p f l hl ρ hpc

/-! ## Path coverage -/

/-- Exhaustiveness: at every fuel, every valuation satisfies the path condition
of at least one leaf of `symExec p f`. -/
theorem symExec_exhaustive (p : Cfg) (f : Nat) (ρ : Valuation) :
    ∃ l ∈ symExec p f, holds l.pc ρ := by
  exact Proofs.symExec_exhaustive_core p f ρ

/-- Pairwise disjointness: at every fuel, the path conditions of any two leaves
at distinct positions of `symExec p f` are never true together. -/
theorem symExec_pairwise_disjoint (p : Cfg) (f : Nat) :
    (symExec p f).Pairwise (fun l₁ l₂ => Disjoint l₁.pc l₂.pc) := by
  exact Proofs.symExec_pairwise_disjoint_core p f

/-! ## From leaf checks to concrete runs -/

/-- Strict transfer: if a leaf list `L` is per-leaf sound for `p` at fuel `f`,
exhaustive, and every leaf passes the strict check for `Q`, then every concrete
run of `p` at fuel `f` returns with a final store satisfying `Q`. -/
theorem exec_okWith_of_leavesSound_of_exhaustive_of_leavesProve (p : Cfg) (f : Nat)
    (L : List Leaf) (Q : Store → Prop)
    (hsound : LeavesSound p f L) (hexh : LeavesExhaustive L) (hprove : LeavesProve L Q)
    (ρ : Valuation) :
    OkWith Q (exec p f (SymStore.init.inst ρ)) := by
  exact Proofs.transfer_strict p f L Q hsound hexh hprove ρ

/-- Lax transfer: as above, but with the lax check (out-of-fuel leaves accepted);
the conclusion weakens to "returns with `Q`, or runs out of fuel". -/
theorem exec_okWithOrOutOfFuel_of_leavesSound_of_exhaustive_of_leavesProveLax (p : Cfg)
    (f : Nat) (L : List Leaf) (Q : Store → Prop)
    (hsound : LeavesSound p f L) (hexh : LeavesExhaustive L) (hprove : LeavesProveLax L Q)
    (ρ : Valuation) :
    OkWithOrOutOfFuel Q (exec p f (SymStore.init.inst ρ)) := by
  exact Proofs.transfer_lax p f L Q hsound hexh hprove ρ

/-- Lax symbolic success at fuel `f` (every leaf of `symExec p f`, under every
valuation satisfying its path condition, returns with `Q` or is out of fuel;
panic leaves are rejected) holds if and only if every concrete run at the same
fuel `f` returns with `Q` or runs out of fuel (bounded safety at fuel `f`). -/
theorem provesLax_iff_forall_exec_okWithOrOutOfFuel (p : Cfg) (f : Nat) (Q : Store → Prop) :
    ProvesLax p f Q ↔ ∀ ρ, OkWithOrOutOfFuel Q (exec p f (SymStore.init.inst ρ)) := by
  constructor
  · exact Proofs.transfer_lax p f (symExec p f) Q
      (Proofs.symExec_leaf_sound_core p f) (Proofs.symExec_exhaustive_core p f)
  · intro H l hl ρ hpc
    exact Proofs.symExec_leaf_sound_core p f l hl ρ hpc ▸ H ρ

/-- Erasing path conditions only strengthens the strict leaf check: if the
leaves with every path condition replaced by `true` pass, the original leaves
pass. -/
theorem leavesProve_of_leavesProve_dropPcs (L : List Leaf) (Q : Store → Prop)
    (h : LeavesProve (dropPcs L) Q) : LeavesProve L Q := by
  exact Proofs.dropPcs_core L Q h

/-! ## Merging -/

/-- Guarded merge soundness: if `(c₁, σ₁)` and `(c₂, σ₂)` are both sound for the
same reference `R` and the same continuation `K`, then
`(c₁ ∨ c₂, x ↦ ite c₁ (σ₁ x) (σ₂ x))` is sound for `R` and `K`. No disjointness
of `c₁` and `c₂` is assumed; the merged store selects `σ₁` wherever `c₁` holds,
so the overlap is resolved by the `ite` guard. -/
theorem guardedMerge_sound {α : Type} (R : Valuation → α) (K : Store → α)
    (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (σ₂ : SymStore)
    (h₁ : GuardedSound R K c₁ σ₁) (h₂ : GuardedSound R K c₂ σ₂) :
    GuardedSound R K (Term.or c₁ c₂) (mergeStore c₁ σ₁ σ₂) := by
  exact Proofs.guardedMerge_sound_core R K c₁ σ₁ c₂ σ₂ h₁ h₂

/-- Merging two successful leaves at the front of a per-leaf sound leaf list
keeps it per-leaf sound. (The converse fails: `mergeLeaf_leavesSound_converse_fails`.) -/
theorem mergeLeaf_preserves_leavesSound (p : Cfg) (f : Nat) (c₁ : Term) (σ₁ : SymStore)
    (c₂ : Term) (σ₂ : SymStore) (rest : List Leaf)
    (hs : LeavesSound p f (⟨c₁, .ok σ₁⟩ :: ⟨c₂, .ok σ₂⟩ :: rest)) :
    LeavesSound p f (mergeLeaf c₁ σ₁ c₂ σ₂ :: rest) := by
  exact Proofs.mergeLeaf_sound_core p f c₁ σ₁ c₂ σ₂ rest hs

/-- Merging two successful leaves at the front of a leaf list neither gains nor
loses exhaustiveness. -/
theorem mergeLeaf_leavesExhaustive_iff (c₁ : Term) (σ₁ : SymStore) (c₂ : Term)
    (σ₂ : SymStore) (rest : List Leaf) :
    LeavesExhaustive (mergeLeaf c₁ σ₁ c₂ σ₂ :: rest) ↔
      LeavesExhaustive (⟨c₁, .ok σ₁⟩ :: ⟨c₂, .ok σ₂⟩ :: rest) := by
  constructor
  · intro hm ρ
    obtain ⟨l, hl, hpc⟩ := hm ρ
    rcases List.mem_cons.1 hl with rfl | hrest
    · rcases (holds_or c₁ c₂ ρ).1 hpc with h1 | h2
      · exact ⟨⟨c₁, .ok σ₁⟩, List.mem_cons_self .., h1⟩
      · exact ⟨⟨c₂, .ok σ₂⟩, List.mem_cons_of_mem _ (List.mem_cons_self ..), h2⟩
    · exact ⟨l, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hrest), hpc⟩
  · exact Proofs.mergeLeaf_exhaustive_core c₁ σ₁ c₂ σ₂ rest

/-- Coverage under merging: for a possibly many-valued behaviour relation `B`,
merging the first two guarded states of a covering list keeps it covering
provided the two states agree (through `K`) wherever both guards hold. -/
theorem guardedMerge_preserves_covers_of_agree_on_overlap {α : Type}
    (B : Valuation → α → Prop) (K : Store → α) (c₁ : Term) (σ₁ : SymStore) (c₂ : Term)
    (σ₂ : SymStore) (rest : List (Term × SymStore))
    (hcov : Covers B K ((c₁, σ₁) :: (c₂, σ₂) :: rest))
    (hagree : ∀ ρ, holds c₁ ρ → holds c₂ ρ → K (σ₂.inst ρ) = K (σ₁.inst ρ)) :
    Covers B K ((Term.or c₁ c₂, mergeStore c₁ σ₁ σ₂) :: rest) := by
  exact Proofs.covers_merge_core B K c₁ σ₁ c₂ σ₂ rest hcov hagree

/-! ## Fuel -/

/-- Concrete fuel monotonicity: a run that does not exhaust fuel `f` has the
same outcome at every larger fuel. -/
theorem exec_fuel_mono (p : Cfg) (f f' : Nat) (st : Store)
    (hne : exec p f st ≠ .outOfFuel) (hle : f ≤ f') :
    exec p f' st = exec p f st := by
  exact Proofs.exec_fuel_mono_core p f f' st hne hle

/-- Strict symbolic success is monotone in fuel: if it holds at fuel `f`, it
holds at every fuel `f' ≥ f`. -/
theorem provesStrict_mono (p : Cfg) (f f' : Nat) (Q : Store → Prop)
    (h : ProvesStrict p f Q) (hle : f ≤ f') :
    ProvesStrict p f' Q := by
  exact (Proofs.provesStrict_iff_core p f' Q).2
    (Proofs.exec_okWith_le_core p f f' Q h hle)

/-- Strict symbolic success at fuel `f` implies concrete success (return with
`Q`) at every fuel `f' ≥ f`, from every input. -/
theorem exec_okWith_of_provesStrict_of_le (p : Cfg) (f f' : Nat) (Q : Store → Prop)
    (h : ProvesStrict p f Q) (hle : f ≤ f') (ρ : Valuation) :
    OkWith Q (exec p f' (SymStore.init.inst ρ)) := by
  exact Proofs.exec_okWith_le_core p f f' Q h hle ρ

/-- For acyclic CFGs, fuel `fuelBound p = #statements + #blocks` suffices: no
run exhausts it. -/
theorem acyclic_exec_ne_outOfFuel_of_fuelBound_le (p : Cfg) (f : Nat) (st : Store)
    (hacyc : Acyclic p) (hf : fuelBound p ≤ f) :
    exec p f st ≠ .outOfFuel := by
  exact Proofs.acyclic_fuel_core p f st hacyc hf

/-- For straight-line CFGs, a run that returns needs at least
`fuelBound p = #statements + #blocks` fuel. -/
theorem straightLine_fuelBound_le_of_exec_ok (p : Cfg) (f : Nat) (st s : Store)
    (hsl : StraightLine p) (hok : exec p f st = .ok s) :
    fuelBound p ≤ f := by
  exact Proofs.straightLine_min_core p f st s hsl hok

/-- For straight-line CFGs, `fuelBound p` is the exact minimal fuel of every run
that returns: a run returns `s` at some fuel if and only if it returns `s` at
fuel `fuelBound p` and runs out of fuel at every smaller fuel. -/
theorem straightLine_exec_ok_iff_fuelBound_minimal (p : Cfg) (st s : Store)
    (hsl : StraightLine p) :
    (∃ f, exec p f st = .ok s) ↔
      (exec p (fuelBound p) st = .ok s ∧ ∀ f' < fuelBound p, exec p f' st = .outOfFuel) := by
  constructor
  · rintro ⟨f, hok⟩
    have hle : fuelBound p ≤ f := Proofs.straightLine_min_core p f st s hsl hok
    have hne : exec p (fuelBound p) st ≠ .outOfFuel :=
      Proofs.acyclic_fuel_core p (fuelBound p) st (acyclic_of_straightLine p hsl) (Nat.le_refl _)
    have hfb : exec p (fuelBound p) st = .ok s := by
      rw [← Proofs.exec_fuel_mono_core p (fuelBound p) f st hne hle]; exact hok
    refine ⟨hfb, fun f' hf' => ?_⟩
    cases ho : exec p f' st with
    | outOfFuel => rfl
    | ok s' =>
        have := Proofs.straightLine_min_core p f' st s' hsl ho
        omega
    | panic loc =>
        have heq := Proofs.exec_fuel_mono_core p f' (fuelBound p) st
          (by rw [ho]; intro h; nomatch h) (by omega)
        rw [hfb, ho] at heq
        nomatch heq
  · exact fun ⟨hfb, _⟩ => ⟨fuelBound p, hfb⟩

/-! ## Simplification -/

/-- A term simplifier `S` is sound under path condition `c` (preserves
interpretation under every valuation satisfying `c`) if and only if rewriting
every term of a guarded state with `S` preserves guarded soundness for every
result type, reference and continuation. The path condition itself is not
rewritten. -/
theorem simpSoundUnder_iff_preserves_guardedSound (c : Term) (S : Term → Term) :
    SimpSoundUnder c S ↔
      ∀ (α : Type) (R : Valuation → α) (K : Store → α) (σ : SymStore),
        GuardedSound R K c σ → GuardedSound R K c (fun x => S (σ x)) := by
  exact Proofs.simpSoundUnder_iff_core c S

/-! ## Completeness -/

/-- At a fixed fuel, strict symbolic success is equivalent to concrete success
(return with `Q`) from every input at that same fuel. No acyclicity needed. -/
theorem provesStrict_iff_forall_exec_okWith (p : Cfg) (f : Nat) (Q : Store → Prop) :
    ProvesStrict p f Q ↔ ∀ ρ, OkWith Q (exec p f (SymStore.init.inst ρ)) := by
  exact Proofs.provesStrict_iff_core p f Q

/-- For acyclic CFGs, strict symbolic success at fuel `fuelBound p` is
equivalent to: every input has some fuel at which the concrete run returns with
`Q`. -/
theorem acyclic_provesStrict_fuelBound_iff_forall_exists_fuel (p : Cfg) (Q : Store → Prop)
    (hacyc : Acyclic p) :
    ProvesStrict p (fuelBound p) Q ↔
      ∀ ρ, ∃ f, OkWith Q (exec p f (SymStore.init.inst ρ)) := by
  rw [Proofs.provesStrict_iff_core]
  constructor
  · exact fun H ρ => ⟨fuelBound p, H ρ⟩
  · intro H ρ
    obtain ⟨f, hf⟩ := H ρ
    have hne_fb : exec p (fuelBound p) (SymStore.init.inst ρ) ≠ .outOfFuel :=
      Proofs.acyclic_fuel_core p (fuelBound p) _ hacyc (Nat.le_refl _)
    by_cases hle : fuelBound p ≤ f
    · rwa [← Proofs.exec_fuel_mono_core p (fuelBound p) f _ hne_fb hle]
    · have hne_f : exec p f (SymStore.init.inst ρ) ≠ .outOfFuel := by
        intro heq; rw [heq] at hf; exact hf
      rwa [Proofs.exec_fuel_mono_core p f (fuelBound p) _ hne_f (by omega)]

/-- For acyclic CFGs at any fuel `f ≥ fuelBound p`, the lax check (out-of-fuel
leaves accepted) and the strict check coincide: no satisfiable out-of-fuel leaf
remains. -/
theorem acyclic_provesLax_iff_provesStrict_of_fuelBound_le (p : Cfg) (f : Nat)
    (Q : Store → Prop) (hacyc : Acyclic p) (hf : fuelBound p ≤ f) :
    ProvesLax p f Q ↔ ProvesStrict p f Q := by
  rw [provesStrict_iff_forall_exec_okWith, provesLax_iff_forall_exec_okWithOrOutOfFuel]
  constructor
  · intro H ρ
    have hne := Proofs.acyclic_fuel_core p f (SymStore.init.inst ρ) hacyc hf
    have h := H ρ
    revert hne h
    cases exec p f (SymStore.init.inst ρ) <;> simp [OkWith, OkWithOrOutOfFuel]
  · intro H ρ
    have h := H ρ
    revert h
    cases exec p f (SymStore.init.inst ρ) <;> simp [OkWith, OkWithOrOutOfFuel]

end Toy.SymEx
