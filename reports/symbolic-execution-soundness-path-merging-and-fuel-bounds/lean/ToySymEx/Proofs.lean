import ToySymEx.Basic
import ToySymEx.Lemmas

/-!
Proof infrastructure for the main statements in `ToySymEx.Statements`.

Everything here is used only inside proofs: per-block invariants of `symBlock`
(path-condition implication, per-leaf soundness, exhaustiveness, pairwise
disjointness), fuel monotonicity of `runBlock`, and the fuel-accounting
functions `tailCost` and `blkCost` behind the `fuelBound` results. No
definition that a main statement mentions is introduced or changed here.
-/

namespace Toy.SymEx.Proofs

open Toy.SymEx Term

theorem eval_subst_core (σ : SymStore) (ρ : Valuation) (e : Term) :
    (e.subst σ).eval ρ = e.eval (σ.inst ρ) := by
  induction e with
  | var x => rfl
  | lit v => rfl
  | add a b iha ihb => simp [Term.subst, Term.eval, iha, ihb]
  | eq a b iha ihb => simp [Term.subst, Term.eval, iha, ihb]
  | ite c t e ihc iht ihe => simp [Term.subst, Term.eval, ihc, iht, ihe]

theorem holds_and_iff (a b : Term) (ρ : Valuation) :
    holds (Term.and a b) ρ ↔ holds a ρ ∧ holds b ρ := by
  unfold holds Term.and
  show (if (a.eval ρ).toBool = true then b.eval ρ else Term.ff.eval ρ).toBool = true ↔ _
  cases ha : (a.eval ρ).toBool
  · constructor
    · intro h; nomatch h
    · rintro ⟨h, _⟩; nomatch h
  · exact ⟨fun h => ⟨rfl, h⟩, fun ⟨_, h⟩ => h⟩

theorem holds_not_iff (a : Term) (ρ : Valuation) :
    holds (Term.not a) ρ ↔ ¬ holds a ρ := by
  unfold holds Term.not
  show (if (a.eval ρ).toBool = true then Term.ff.eval ρ else Term.tt.eval ρ).toBool = true ↔
    ¬ ((a.eval ρ).toBool = true)
  cases ha : (a.eval ρ).toBool
  · constructor
    · intro _ h; nomatch h
    · intro _; rfl
  · constructor
    · intro h; nomatch h
    · intro h; exact absurd rfl h

theorem holds_eq_lit_iff (s : Term) (v : Val) (ρ : Valuation) :
    holds (Term.eq s (Term.lit v)) ρ ↔ s.eval ρ = v := by
  show decide (s.eval ρ = v) = true ↔ s.eval ρ = v
  exact @decide_eq_true_iff (s.eval ρ = v) _

theorem symStore_set_inst (σ : SymStore) (x : Var) (e : Term) (ρ : Valuation) :
    (σ.set x (e.subst σ)).inst ρ = (σ.inst ρ).set x (e.eval (σ.inst ρ)) := by
  funext y
  by_cases hy : y = x <;> simp [SymStore.inst, SymStore.set, Store.set, hy, eval_subst_core]

theorem forkSwitch_pc_imp (s : Term) :
    ∀ (tgts : List (Val × Nat)) (d : Nat) (c : Term) (cb : Term × Nat),
      cb ∈ forkSwitch s tgts d c → ∀ ρ, holds cb.1 ρ →
        holds c ρ ∧ cb.2 = select (s.eval ρ) tgts d
  | [], d, c, cb, hmem, ρ, hpc => by
      simp [forkSwitch] at hmem
      subst hmem
      exact ⟨hpc, rfl⟩
  | (v, b) :: rest, d, c, cb, hmem, ρ, hpc => by
      simp [forkSwitch] at hmem
      rcases hmem with rfl | hmem
      · obtain ⟨hc, hv⟩ := (holds_and_iff _ _ ρ).1 hpc
        have hveq : s.eval ρ = v := (holds_eq_lit_iff s v ρ).1 hv
        simp [select, hveq, hc]
      · obtain ⟨hc', hsel⟩ := forkSwitch_pc_imp s rest d _ cb hmem ρ hpc
        obtain ⟨hc, hnv⟩ := (holds_and_iff _ _ ρ).1 hc'
        have hvne : s.eval ρ ≠ v := fun h => ((holds_not_iff _ ρ).1 hnv) ((holds_eq_lit_iff s v ρ).2 h)
        simp [select, hvne, hc, hsel]

theorem forkSwitch_exhaustive (s : Term) :
    ∀ (tgts : List (Val × Nat)) (d : Nat) (c : Term) (ρ : Valuation),
      holds c ρ → ∃ cb ∈ forkSwitch s tgts d c, holds cb.1 ρ
  | [], d, c, ρ, hc => ⟨(c, d), by simp [forkSwitch], hc⟩
  | (v, b) :: rest, d, c, ρ, hc => by
      by_cases hv : s.eval ρ = v
      · refine ⟨(Term.and c (Term.eq s (Term.lit v)), b), by simp [forkSwitch], ?_⟩
        exact (holds_and_iff _ _ ρ).2 ⟨hc, (holds_eq_lit_iff s v ρ).2 hv⟩
      · have hc' : holds (Term.and c (Term.not (Term.eq s (Term.lit v)))) ρ :=
          (holds_and_iff _ _ ρ).2 ⟨hc, (holds_not_iff _ ρ).2 (fun h => hv ((holds_eq_lit_iff s v ρ).1 h))⟩
        obtain ⟨cb, hmem, hcb⟩ := forkSwitch_exhaustive s rest d _ ρ hc'
        exact ⟨cb, List.mem_cons_of_mem _ hmem, hcb⟩

theorem forkSwitch_pairwise_disjoint (s : Term) :
    ∀ (tgts : List (Val × Nat)) (d : Nat) (c : Term),
      (forkSwitch s tgts d c).Pairwise (fun cb₁ cb₂ => Disjoint cb₁.1 cb₂.1)
  | [], d, c => List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  | (v, b) :: rest, d, c => by
      refine List.Pairwise.cons ?_ (forkSwitch_pairwise_disjoint s rest d _)
      intro cb₂ hmem ρ ⟨h1, h2⟩
      have hv : s.eval ρ = v := (holds_eq_lit_iff s v ρ).1 ((holds_and_iff _ _ ρ).1 h1).2
      have hc' : holds (Term.and c (Term.not (Term.eq s (Term.lit v)))) ρ :=
        (forkSwitch_pc_imp s rest d _ cb₂ hmem ρ h2).1
      exact ((holds_not_iff _ ρ).1 ((holds_and_iff _ _ ρ).1 hc').2) ((holds_eq_lit_iff s v ρ).2 hv)

theorem symBlock_pc_imp (p : Cfg) :
    ∀ (f b i : Nat) (ss : List Stmt) (t : Terminator) (c : Term) (σ : SymStore) (l : Leaf),
      l ∈ symBlock p f b i ss t c σ → ∀ ρ, holds l.pc ρ → holds c ρ
  | 0, _, _, _, _, c, _, l, hl, _, hpc => by
      simp [symBlock] at hl; subst hl; exact hpc
  | f + 1, b, i, .assign _ e :: ss, t, c, σ, l, hl, ρ, hpc =>
      symBlock_pc_imp p f b (i + 1) ss t c (σ.set _ (e.subst σ)) l hl ρ hpc
  | f + 1, b, i, .assert e :: ss, t, c, σ, l, hl, ρ, hpc => by
      simp [symBlock] at hl
      rcases hl with rfl | hl
      · exact ((holds_and_iff _ _ ρ).1 hpc).1
      · exact ((holds_and_iff _ _ ρ).1 (symBlock_pc_imp p f b (i + 1) ss t (Term.and c (e.subst σ)) σ l hl ρ hpc)).1
  | _ + 1, _, _, [], .ret, _, _, l, hl, _, hpc => by
      simp [symBlock] at hl; subst hl; exact hpc
  | f + 1, _, _, [], .goto b', c, σ, l, hl, ρ, hpc => by
      simp only [symBlock] at hl
      cases hb' : p[b']? <;> simp [hb'] at hl
      · subst hl; exact hpc
      · exact symBlock_pc_imp p f b' 0 _ _ c σ l hl ρ hpc
  | f + 1, _, _, [], .switchInt x tgts d, c, σ, l, hl, ρ, hpc => by
      simp only [symBlock, List.mem_flatMap] at hl
      obtain ⟨cb, hcb, hl'⟩ := hl
      have hcb_ρ : holds cb.1 ρ := by
        cases hblk : p[cb.2]? <;> simp [hblk] at hl'
        · subst hl'; exact hpc
        · exact symBlock_pc_imp p f cb.2 0 _ _ cb.1 σ l hl' ρ hpc
      exact (forkSwitch_pc_imp (σ x) tgts d c cb hcb ρ hcb_ρ).1

theorem symBlock_sound (p : Cfg) :
    ∀ (f b i : Nat) (ss : List Stmt) (t : Terminator) (c : Term) (σ : SymStore) (l : Leaf),
      l ∈ symBlock p f b i ss t c σ → ∀ ρ, holds l.pc ρ →
        runBlock p f b i ss t (σ.inst ρ) = l.res.inst ρ
  | 0, _, _, _, _, _, _, l, hl, _, _ => by
      simp [symBlock] at hl; subst hl; rfl
  | f + 1, b, i, .assign x e :: ss, t, c, σ, l, hl, ρ, hpc => by
      simp only [symBlock] at hl
      simp only [runBlock, ← symStore_set_inst]
      exact symBlock_sound p f b (i + 1) ss t c _ l hl ρ hpc
  | f + 1, b, i, .assert e :: ss, t, c, σ, l, hl, ρ, hpc => by
      simp only [symBlock, List.mem_cons] at hl
      rcases hl with rfl | hl
      · have hne : ¬ holds (e.subst σ) ρ := (holds_not_iff _ ρ).1 ((holds_and_iff _ _ ρ).1 hpc).2
        have hfalse : (e.eval (σ.inst ρ)).toBool = false := by
          rw [← eval_subst_core]
          cases hb : ((e.subst σ).eval ρ).toBool
          · rfl
          · exact absurd hb hne
        simp [runBlock, hfalse, SymOutcome.inst]
      · have hce : holds (Term.and c (e.subst σ)) ρ :=
          symBlock_pc_imp p f b (i + 1) ss t _ σ l hl ρ hpc
        have htrue : (e.eval (σ.inst ρ)).toBool = true := by
          rw [← eval_subst_core]
          exact ((holds_and_iff _ _ ρ).1 hce).2
        simp only [runBlock, htrue, ↓reduceIte]
        exact symBlock_sound p f b (i + 1) ss t _ σ l hl ρ hpc
  | _ + 1, _, _, [], .ret, _, _, l, hl, _, _ => by
      simp [symBlock] at hl; subst hl; rfl
  | f + 1, _, _, [], .goto b', c, σ, l, hl, ρ, hpc => by
      simp only [symBlock, runBlock] at hl ⊢
      cases hb' : p[b']? <;> simp [hb'] at hl ⊢
      · subst hl; rfl
      · exact symBlock_sound p f b' 0 _ _ c σ l hl ρ hpc
  | f + 1, _, _, [], .switchInt x tgts d, c, σ, l, hl, ρ, hpc => by
      simp only [symBlock, List.mem_flatMap] at hl
      obtain ⟨cb, hcb, hl'⟩ := hl
      have hcb_ρ : holds cb.1 ρ := by
        cases hblk : p[cb.2]? <;> simp [hblk] at hl'
        · subst hl'; exact hpc
        · exact symBlock_pc_imp p f cb.2 0 _ _ cb.1 σ l hl' ρ hpc
      have hsel : cb.2 = select ((σ.inst ρ) x) tgts d :=
        (forkSwitch_pc_imp (σ x) tgts d c cb hcb ρ hcb_ρ).2
      simp only [runBlock, ← hsel]
      cases hblk : p[cb.2]? <;> simp [hblk] at hl' ⊢
      · subst hl'; rfl
      · exact symBlock_sound p f cb.2 0 _ _ cb.1 σ l hl' ρ hpc

theorem symExec_leaf_sound_core (p : Cfg) (f : Nat) (l : Leaf) (hl : l ∈ symExec p f)
    (ρ : Valuation) (hpc : holds l.pc ρ) :
    exec p f (SymStore.init.inst ρ) = l.res.inst ρ := by
  unfold symExec exec at *
  cases h0 : p[0]? <;> simp [h0] at hl ⊢
  · subst hl; rfl
  · exact symBlock_sound p f 0 0 _ _ Term.tt SymStore.init l hl ρ hpc

theorem symBlock_exhaustive (p : Cfg) :
    ∀ (f b i : Nat) (ss : List Stmt) (t : Terminator) (c : Term) (σ : SymStore) (ρ : Valuation),
      holds c ρ → ∃ l ∈ symBlock p f b i ss t c σ, holds l.pc ρ
  | 0, _, _, _, _, c, _, _, hc => ⟨⟨c, .outOfFuel⟩, by simp [symBlock], hc⟩
  | f + 1, b, i, .assign _ e :: ss, t, c, σ, ρ, hc =>
      symBlock_exhaustive p f b (i + 1) ss t c (σ.set _ (e.subst σ)) ρ hc
  | f + 1, b, i, .assert e :: ss, t, c, σ, ρ, hc => by
      by_cases he : holds (e.subst σ) ρ
      · obtain ⟨l, hl, hpc⟩ := symBlock_exhaustive p f b (i + 1) ss t (Term.and c (e.subst σ)) σ ρ
          ((holds_and_iff _ _ ρ).2 ⟨hc, he⟩)
        exact ⟨l, List.mem_cons_of_mem _ hl, hpc⟩
      · exact ⟨⟨Term.and c (Term.not (e.subst σ)), .panic ⟨b, i⟩⟩, List.mem_cons_self ..,
          (holds_and_iff _ _ ρ).2 ⟨hc, (holds_not_iff _ ρ).2 he⟩⟩
  | _ + 1, _, _, [], .ret, c, σ, _, hc => ⟨⟨c, .ok σ⟩, by simp [symBlock], hc⟩
  | f + 1, _, _, [], .goto b', c, σ, ρ, hc => by
      simp only [symBlock]
      cases p[b']?
      · exact ⟨⟨c, .panic ⟨b', 0⟩⟩, by simp, hc⟩
      · exact symBlock_exhaustive p f b' 0 _ _ c σ ρ hc
  | f + 1, _, _, [], .switchInt x tgts d, c, σ, ρ, hc => by
      simp only [symBlock, List.mem_flatMap]
      obtain ⟨cb, hcb, hcb_ρ⟩ := forkSwitch_exhaustive (σ x) tgts d c ρ hc
      cases hblk : p[cb.2]? with
      | none => exact ⟨⟨cb.1, .panic ⟨cb.2, 0⟩⟩, ⟨cb, hcb, by simp [hblk]⟩, hcb_ρ⟩
      | some blk =>
        obtain ⟨l, hl, hpc⟩ := symBlock_exhaustive p f cb.2 0 blk.stmts blk.term cb.1 σ ρ hcb_ρ
        exact ⟨l, ⟨cb, hcb, by simp [hblk, hl]⟩, hpc⟩

theorem symExec_exhaustive_core (p : Cfg) (f : Nat) (ρ : Valuation) :
    ∃ l ∈ symExec p f, holds l.pc ρ := by
  unfold symExec
  cases p[0]?
  · exact ⟨⟨Term.tt, .panic ⟨0, 0⟩⟩, by simp, rfl⟩
  · exact symBlock_exhaustive p f 0 0 _ _ Term.tt SymStore.init ρ rfl

theorem pairwise_flatMap {α β : Type} (R : β → β → Prop) (xs : List α) (g : α → List β)
    (hxs : xs.Pairwise (fun a₁ a₂ => ∀ b₁ ∈ g a₁, ∀ b₂ ∈ g a₂, R b₁ b₂))
    (hg : ∀ a ∈ xs, (g a).Pairwise R) :
    (xs.flatMap g).Pairwise R := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons a xs ih =>
      simp only [List.flatMap_cons, List.pairwise_append]
      obtain ⟨ha_xs, hxs'⟩ := List.pairwise_cons.1 hxs
      refine ⟨hg a (List.mem_cons_self ..), ih hxs' (fun x hx => hg x (List.mem_cons_of_mem _ hx)), ?_⟩
      intro b₁ hb₁ b₂ hb₂
      rw [List.mem_flatMap] at hb₂
      obtain ⟨a₂, ha₂, hb₂'⟩ := hb₂
      exact ha_xs a₂ ha₂ b₁ hb₁ b₂ hb₂'

theorem symBlock_pairwise_disjoint (p : Cfg) :
    ∀ (f b i : Nat) (ss : List Stmt) (t : Terminator) (c : Term) (σ : SymStore),
      (symBlock p f b i ss t c σ).Pairwise (fun l₁ l₂ => Disjoint l₁.pc l₂.pc)
  | 0, _, _, _, _, _, _ => List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  | f + 1, b, i, .assign _ e :: ss, t, c, σ =>
      symBlock_pairwise_disjoint p f b (i + 1) ss t c (σ.set _ (e.subst σ))
  | f + 1, b, i, .assert e :: ss, t, c, σ => by
      refine List.Pairwise.cons ?_ (symBlock_pairwise_disjoint p f b (i + 1) ss t _ σ)
      intro l₂ hl₂ ρ ⟨h1, h2⟩
      have hne : ¬ holds (e.subst σ) ρ := (holds_not_iff _ ρ).1 ((holds_and_iff _ _ ρ).1 h1).2
      have he : holds (e.subst σ) ρ :=
        ((holds_and_iff _ _ ρ).1 (symBlock_pc_imp p f b (i + 1) ss t _ σ l₂ hl₂ ρ h2)).2
      exact hne he
  | _ + 1, _, _, [], .ret, _, _ => List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  | f + 1, _, _, [], .goto b', c, σ => by
      simp only [symBlock]
      cases p[b']?
      · exact List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
      · exact symBlock_pairwise_disjoint p f b' 0 _ _ c σ
  | f + 1, _, _, [], .switchInt x tgts d, c, σ => by
      simp only [symBlock]
      apply pairwise_flatMap
      · refine List.Pairwise.imp ?_ (forkSwitch_pairwise_disjoint (σ x) tgts d c)
        intro cb₁ cb₂ hdisj l₁ hl₁ l₂ hl₂ ρ ⟨h1, h2⟩
        have hc1 : holds cb₁.1 ρ := by
          cases hblk : p[cb₁.2]? <;> simp [hblk] at hl₁
          · subst hl₁; exact h1
          · exact symBlock_pc_imp p f cb₁.2 0 _ _ cb₁.1 σ l₁ hl₁ ρ h1
        have hc2 : holds cb₂.1 ρ := by
          cases hblk : p[cb₂.2]? <;> simp [hblk] at hl₂
          · subst hl₂; exact h2
          · exact symBlock_pc_imp p f cb₂.2 0 _ _ cb₂.1 σ l₂ hl₂ ρ h2
        exact hdisj ρ ⟨hc1, hc2⟩
      · intro cb _
        cases p[cb.2]?
        · exact List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
        · exact symBlock_pairwise_disjoint p f cb.2 0 _ _ cb.1 σ

theorem symExec_pairwise_disjoint_core (p : Cfg) (f : Nat) :
    (symExec p f).Pairwise (fun l₁ l₂ => Disjoint l₁.pc l₂.pc) := by
  unfold symExec
  cases p[0]?
  · exact List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  · exact symBlock_pairwise_disjoint p f 0 0 _ _ Term.tt SymStore.init

/-! ## From leaf checks to concrete runs -/

theorem transfer_strict (p : Cfg) (f : Nat) (L : List Leaf) (Q : Store → Prop)
    (hsound : LeavesSound p f L) (hexh : LeavesExhaustive L) (hprove : LeavesProve L Q)
    (ρ : Valuation) : OkWith Q (exec p f (SymStore.init.inst ρ)) :=
  let ⟨l, hl, hpc⟩ := hexh ρ
  hsound l hl ρ hpc ▸ hprove l hl ρ hpc

theorem transfer_lax (p : Cfg) (f : Nat) (L : List Leaf) (Q : Store → Prop)
    (hsound : LeavesSound p f L) (hexh : LeavesExhaustive L) (hprove : LeavesProveLax L Q)
    (ρ : Valuation) : OkWithOrOutOfFuel Q (exec p f (SymStore.init.inst ρ)) :=
  let ⟨l, hl, hpc⟩ := hexh ρ
  hsound l hl ρ hpc ▸ hprove l hl ρ hpc

theorem dropPcs_core (L : List Leaf) (Q : Store → Prop)
    (h : LeavesProve (dropPcs L) Q) : LeavesProve L Q :=
  fun l hl ρ _ => h ⟨Term.tt, l.res⟩ (List.mem_map_of_mem hl) ρ rfl

theorem guardedMerge_sound_core {α : Type} (R : Valuation → α) (K : Store → α)
    (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (σ₂ : SymStore)
    (h₁ : GuardedSound R K c₁ σ₁) (h₂ : GuardedSound R K c₂ σ₂) :
    GuardedSound R K (Term.or c₁ c₂) (mergeStore c₁ σ₁ σ₂) := by
  intro ρ hor
  by_cases hc₁ : holds c₁ ρ
  · rw [mergeStore_inst_of_holds _ _ _ _ hc₁]; exact h₁ ρ hc₁
  · rw [mergeStore_inst_of_not_holds _ _ _ _ hc₁]
    exact h₂ ρ (((holds_or c₁ c₂ ρ).1 hor).resolve_left hc₁)

theorem mergeLeaf_sound_core (p : Cfg) (f : Nat) (c₁ : Term) (σ₁ : SymStore)
    (c₂ : Term) (σ₂ : SymStore) (rest : List Leaf)
    (hs : LeavesSound p f (⟨c₁, .ok σ₁⟩ :: ⟨c₂, .ok σ₂⟩ :: rest)) :
    LeavesSound p f (mergeLeaf c₁ σ₁ c₂ σ₂ :: rest) := by
  intro l hl ρ hpc
  rcases List.mem_cons.1 hl with rfl | hrest
  · exact guardedMerge_sound_core (fun ρ => exec p f (SymStore.init.inst ρ)) Outcome.ok c₁ σ₁ c₂ σ₂
      (fun ρ h => hs _ (List.mem_cons_self ..) ρ h)
      (fun ρ h => hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ρ h) ρ hpc
  · exact hs l (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hrest)) ρ hpc

theorem mergeLeaf_exhaustive_core (c₁ : Term) (σ₁ : SymStore) (c₂ : Term)
    (σ₂ : SymStore) (rest : List Leaf)
    (he : LeavesExhaustive (⟨c₁, .ok σ₁⟩ :: ⟨c₂, .ok σ₂⟩ :: rest)) :
    LeavesExhaustive (mergeLeaf c₁ σ₁ c₂ σ₂ :: rest) := by
  intro ρ
  obtain ⟨l, hl, hpc⟩ := he ρ
  rcases List.mem_cons.1 hl with rfl | hl'
  · exact ⟨_, List.mem_cons_self .., (holds_or c₁ c₂ ρ).2 (Or.inl hpc)⟩
  · rcases List.mem_cons.1 hl' with rfl | hrest
    · exact ⟨_, List.mem_cons_self .., (holds_or c₁ c₂ ρ).2 (Or.inr hpc)⟩
    · exact ⟨l, List.mem_cons_of_mem _ hrest, hpc⟩

theorem covers_merge_core {α : Type}
    (B : Valuation → α → Prop) (K : Store → α) (c₁ : Term) (σ₁ : SymStore) (c₂ : Term)
    (σ₂ : SymStore) (rest : List (Term × SymStore))
    (hcov : Covers B K ((c₁, σ₁) :: (c₂, σ₂) :: rest))
    (hagree : ∀ ρ, holds c₁ ρ → holds c₂ ρ → K (σ₂.inst ρ) = K (σ₁.inst ρ)) :
    Covers B K ((Term.or c₁ c₂, mergeStore c₁ σ₁ σ₂) :: rest) := by
  intro ρ a hB
  obtain ⟨cs, hcs, hpc, hK⟩ := hcov ρ a hB
  rcases List.mem_cons.1 hcs with rfl | hcs'
  · refine ⟨_, List.mem_cons_self .., (holds_or c₁ c₂ ρ).2 (Or.inl hpc), ?_⟩
    rw [mergeStore_inst_of_holds _ _ _ _ hpc]; exact hK
  · rcases List.mem_cons.1 hcs' with rfl | hrest
    · refine ⟨_, List.mem_cons_self .., (holds_or c₁ c₂ ρ).2 (Or.inr hpc), ?_⟩
      by_cases hc₁ : holds c₁ ρ
      · rw [mergeStore_inst_of_holds _ _ _ _ hc₁, ← hagree ρ hc₁ hpc]; exact hK
      · rw [mergeStore_inst_of_not_holds _ _ _ _ hc₁]; exact hK
    · exact ⟨cs, List.mem_cons_of_mem _ hrest, hpc, hK⟩

theorem runBlock_fuel_mono (p : Cfg) :
    ∀ (f f' b i : Nat) (ss : List Stmt) (t : Terminator) (st : Store),
      runBlock p f b i ss t st ≠ .outOfFuel → f ≤ f' →
        runBlock p f' b i ss t st = runBlock p f b i ss t st
  | 0, _, _, _, _, _, _, hne, _ => absurd rfl hne
  | _ + 1, 0, _, _, _, _, _, _, hle => by omega
  | f + 1, f' + 1, b, i, .assign x e :: ss, t, st, hne, hle =>
      runBlock_fuel_mono p f f' b (i + 1) ss t (st.set x (e.eval st)) hne (by omega)
  | f + 1, f' + 1, b, i, .assert e :: ss, t, st, hne, hle => by
      simp only [runBlock] at hne ⊢
      split at hne <;> simp_all
      exact runBlock_fuel_mono p f f' b (i + 1) ss t st hne (by omega)
  | _ + 1, _ + 1, _, _, [], .ret, _, _, _ => rfl
  | f + 1, f' + 1, _, _, [], .goto b', st, hne, hle => by
      simp only [runBlock] at hne ⊢
      cases hb' : p[b']? <;> simp_all
      exact runBlock_fuel_mono p f f' b' 0 _ _ st hne (by omega)
  | f + 1, f' + 1, _, _, [], .switchInt x tgts d, st, hne, hle => by
      simp only [runBlock] at hne ⊢
      cases hblk : p[select (st x) tgts d]? <;> simp_all
      exact runBlock_fuel_mono p f f' _ 0 _ _ st hne (by omega)

theorem exec_fuel_mono_core (p : Cfg) (f f' : Nat) (st : Store)
    (hne : exec p f st ≠ .outOfFuel) (hle : f ≤ f') :
    exec p f' st = exec p f st := by
  unfold exec at hne ⊢
  cases h0 : p[0]? <;> simp_all
  exact runBlock_fuel_mono p f f' 0 0 _ _ st hne hle

theorem exec_okWith_le_core (p : Cfg) (f f' : Nat) (Q : Store → Prop)
    (h : ProvesStrict p f Q) (hle : f ≤ f') (ρ : Valuation) :
    OkWith Q (exec p f' (SymStore.init.inst ρ)) := by
  have hok : OkWith Q (exec p f (SymStore.init.inst ρ)) :=
    transfer_strict p f (symExec p f) Q
      (symExec_leaf_sound_core p f) (symExec_exhaustive_core p f) h ρ
  have hne : exec p f (SymStore.init.inst ρ) ≠ .outOfFuel := by
    intro heq; rw [heq] at hok; exact hok
  rw [exec_fuel_mono_core p f f' _ hne hle]
  exact hok

theorem select_mem_targets (v : Val) :
    ∀ (tgts : List (Val × Nat)) (d : Nat), select v tgts d ∈ tgts.map Prod.snd ++ [d]
  | [], d => by simp [select]
  | (w, b) :: rest, d => by
      simp only [select]
      split
      · simp
      · exact List.mem_cons_of_mem _ (select_mem_targets v rest d)

def tailCost (p : Cfg) (b : Nat) : Nat :=
  ((p.drop b).map (fun blk => blk.stmts.length + 1)).sum

theorem tailCost_zero_eq_fuelBound : ∀ (p : Cfg), tailCost p 0 = fuelBound p
  | [] => rfl
  | blk :: rest => by
      have ih := tailCost_zero_eq_fuelBound rest
      simp only [tailCost, List.drop, List.map_cons, List.sum_cons, fuelBound, List.length_cons] at ih ⊢
      omega

theorem tailCost_step (p : Cfg) (b : Nat) (hb : b < p.length) :
    tailCost p b = (p[b]'hb).stmts.length + 1 + tailCost p (b + 1) := by
  induction p generalizing b with
  | nil => simp at hb
  | cons _ rest ih =>
      cases b with
      | zero => simp [tailCost]
      | succ b =>
          simp only [List.length_cons] at hb
          simpa [tailCost] using ih b (by omega)

theorem tailCost_anti (p : Cfg) : ∀ {b b' : Nat}, b ≤ b' → tailCost p b' ≤ tailCost p b
  | b, b', hle => by
      induction hle with
      | refl => exact Nat.le_refl _
      | @step m _ ih =>
          change tailCost p (m + 1) ≤ tailCost p b
          by_cases hm : m < p.length
          · rw [tailCost_step p m hm] at ih; omega
          · have hdrop : p.drop (m + 1) = [] := List.drop_eq_nil_of_le (by omega)
            simp [tailCost, hdrop]

theorem runBlock_ok_le_of_straightLine (p : Cfg) (hsl : StraightLine p) :
    ∀ (f b i : Nat) (hb : b < p.length) (ss : List Stmt) (st s : Store),
      runBlock p f b i ss (p[b]'hb).term st = .ok s →
        ss.length + 1 + tailCost p (b + 1) ≤ f
  | 0, _, _, _, _, _, _, hok => nomatch hok
  | f + 1, b, i, hb, .assign x e :: ss, st, s, hok => by
      have ih := runBlock_ok_le_of_straightLine p hsl f b (i + 1) hb ss (st.set x (e.eval st)) s hok
      simp only [List.length_cons]; omega
  | f + 1, b, i, hb, .assert e :: ss, st, s, hok => by
      simp only [runBlock] at hok
      split at hok
      · have ih := runBlock_ok_le_of_straightLine p hsl f b (i + 1) hb ss st s hok
        simp only [List.length_cons]; omega
      · nomatch hok
  | f + 1, b, _, hb, [], st, s, hok => by
      have hterm := hsl.2 b hb
      by_cases hnext : b + 1 < p.length
      · simp only [hnext, ↓reduceIte] at hterm
        have hget : p[b + 1]? = some (p[b + 1]'hnext) := List.getElem?_eq_getElem hnext
        simp only [runBlock, hterm, hget] at hok
        have ih := runBlock_ok_le_of_straightLine p hsl f (b + 1) 0 hnext (p[b + 1]'hnext).stmts st s hok
        rw [tailCost_step p (b + 1) hnext]
        simp only [List.length_nil]; omega
      · simp only [hnext, ↓reduceIte] at hterm
        have hdrop : p.drop (b + 1) = [] := List.drop_eq_nil_of_le (by omega)
        simp [tailCost, hdrop]

theorem straightLine_min_core (p : Cfg) (f : Nat) (st s : Store)
    (hsl : StraightLine p) (hok : exec p f st = .ok s) :
    fuelBound p ≤ f := by
  unfold exec at hok
  cases h0 : p[0]? with
  | none => rw [h0] at hok; nomatch hok
  | some blk =>
      rw [h0] at hok
      obtain ⟨h0_lt, hblk⟩ := List.getElem?_eq_some_iff.1 h0
      subst hblk
      have h := runBlock_ok_le_of_straightLine p hsl f 0 0 h0_lt _ st s hok
      have hstep := tailCost_step p 0 h0_lt
      rw [tailCost_zero_eq_fuelBound] at hstep
      omega

theorem simpSoundUnder_iff_core (c : Term) (S : Term → Term) :
    SimpSoundUnder c S ↔
      ∀ (α : Type) (R : Valuation → α) (K : Store → α) (σ : SymStore),
        GuardedSound R K c σ → GuardedSound R K c (fun x => S (σ x)) := by
  constructor
  · intro hS α R K σ hG ρ hc
    have heq : SymStore.inst (fun x => S (σ x)) ρ = σ.inst ρ := by
      funext x; exact hS (σ x) ρ hc
    rw [heq]; exact hG ρ hc
  · intro H t ρ hc
    exact (H Val (fun ρ' => t.eval ρ') (fun st => st 0) (fun _ => t) (fun _ _ => rfl) ρ hc).symm

theorem provesStrict_iff_core (p : Cfg) (f : Nat) (Q : Store → Prop) :
    ProvesStrict p f Q ↔ ∀ ρ, OkWith Q (exec p f (SymStore.init.inst ρ)) := by
  constructor
  · exact transfer_strict p f (symExec p f) Q
      (symExec_leaf_sound_core p f) (symExec_exhaustive_core p f)
  · intro H l hl ρ hpc
    exact symExec_leaf_sound_core p f l hl ρ hpc ▸ H ρ

/-- Per-block fuel cost used to prove `fuelBound` suffices for every `Acyclic` CFG. -/
def blkCost (p : Cfg) (k : Nat) : Nat :=
  match p[k]? with
  | some blk => blk.stmts.length + 1
  | none => 0

theorem sum_map_erase (g : Nat → Nat) :
    ∀ (l : List Nat) {b : Nat}, b ∈ l → g b + ((l.erase b).map g).sum = (l.map g).sum
  | [], _, h => nomatch h
  | a :: rest, b, h => by
      simp only [List.erase_cons]
      by_cases hab : a = b
      · subst hab; simp
      · have hbeq : (a == b) = false := beq_false_of_ne hab
        have hmem : b ∈ rest := (List.mem_cons.1 h).resolve_left (Ne.symm hab)
        have ih := sum_map_erase g rest hmem
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
        omega

theorem range_blkCost_add_tailCost (p : Cfg) :
    ∀ (k : Nat), k ≤ p.length →
      ((List.range k).map (blkCost p)).sum + tailCost p k = fuelBound p
  | 0, _ => by simpa [List.range_zero] using tailCost_zero_eq_fuelBound p
  | k + 1, hk => by
      have ih := range_blkCost_add_tailCost p k (by omega)
      have hk_lt : k < p.length := by omega
      have hstep := tailCost_step p k hk_lt
      have hbc : blkCost p k = (p[k]'hk_lt).stmts.length + 1 := by
        simp [blkCost, List.getElem?_eq_getElem hk_lt]
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hbc]
      omega

theorem range_blkCost_eq_fuelBound (p : Cfg) :
    ((List.range p.length).map (blkCost p)).sum = fuelBound p := by
  have h := range_blkCost_add_tailCost p p.length (Nat.le_refl _)
  have hdrop : p.drop p.length = [] := List.drop_eq_nil_of_le (Nat.le_refl _)
  simpa [tailCost, hdrop] using h

theorem runBlock_ne_outOfFuel_of_acyclic (p : Cfg) (rank : Nat → Nat)
    (hrank : ∀ i (h : i < p.length), ∀ b ∈ (p[i]'h).term.targetsOf, b < p.length → rank i < rank b) :
    ∀ (f b i : Nat) (hb : b < p.length) (ss : List Stmt) (avail : List Nat) (st : Store),
      (∀ k < p.length, rank b < rank k → k ∈ avail) →
      ss.length + 1 + (avail.map (blkCost p)).sum ≤ f →
        runBlock p f b i ss (p[b]'hb).term st ≠ .outOfFuel
  | 0, _, _, _, _, _, _, _, hf => by omega
  | f + 1, b, i, hb, .assign x e :: ss, avail, st, havail, hf => by
      simp only [List.length_cons] at hf
      exact runBlock_ne_outOfFuel_of_acyclic p rank hrank f b (i + 1) hb ss avail
        (st.set x (e.eval st)) havail (by omega)
  | f + 1, b, i, hb, .assert e :: ss, avail, st, havail, hf => by
      simp only [List.length_cons] at hf
      simp only [runBlock]
      split
      · exact runBlock_ne_outOfFuel_of_acyclic p rank hrank f b (i + 1) hb ss avail st havail (by omega)
      · intro h; nomatch h
  | f + 1, b, _, hb, [], avail, st, havail, hf => by
      cases ht : (p[b]'hb).term with
      | ret => simp [runBlock]
      | goto b' =>
          simp only [runBlock]
          cases hb' : p[b']? with
          | none => intro h; nomatch h
          | some blk =>
              obtain ⟨hb'_lt, hblk_eq⟩ := List.getElem?_eq_some_iff.1 hb'
              subst hblk_eq
              have hlt : rank b < rank b' := hrank b hb b' (by simp [ht, Terminator.targetsOf]) hb'_lt
              have hb'_mem : b' ∈ avail := havail b' hb'_lt hlt
              have herase := sum_map_erase (blkCost p) avail hb'_mem
              have hbc : blkCost p b' = (p[b']'hb'_lt).stmts.length + 1 := by
                simp [blkCost, List.getElem?_eq_getElem hb'_lt]
              have havail' : ∀ k < p.length, rank b' < rank k → k ∈ avail.erase b' := by
                intro k hk hrk
                exact (List.mem_erase_of_ne (fun heq : k = b' => by subst heq; omega)).2 (havail k hk (by omega))
              exact runBlock_ne_outOfFuel_of_acyclic p rank hrank f b' 0 hb'_lt _ (avail.erase b') st
                havail' (by omega)
      | switchInt x tgts d =>
          simp only [runBlock]
          let b' := select (st x) tgts d
          cases hb' : p[b']? with
          | none => intro h; nomatch h
          | some blk =>
              obtain ⟨hb'_lt, hblk_eq⟩ := List.getElem?_eq_some_iff.1 hb'
              subst hblk_eq
              have hmem : b' ∈ tgts.map Prod.snd ++ [d] := select_mem_targets (st x) tgts d
              have hlt : rank b < rank b' :=
                hrank b hb b' (by simpa [ht, Terminator.targetsOf] using hmem) hb'_lt
              have hb'_mem : b' ∈ avail := havail b' hb'_lt hlt
              have herase := sum_map_erase (blkCost p) avail hb'_mem
              have hbc : blkCost p b' = (p[b']'hb'_lt).stmts.length + 1 := by
                simp [blkCost, List.getElem?_eq_getElem hb'_lt]
              have havail' : ∀ k < p.length, rank b' < rank k → k ∈ avail.erase b' := by
                intro k hk hrk
                exact (List.mem_erase_of_ne (fun heq : k = b' => by subst heq; omega)).2 (havail k hk (by omega))
              exact runBlock_ne_outOfFuel_of_acyclic p rank hrank f b' 0 hb'_lt _ (avail.erase b') st
                havail' (by omega)

theorem acyclic_fuel_core (p : Cfg) (f : Nat) (st : Store)
    (hac : Acyclic p) (hf : fuelBound p ≤ f) :
    exec p f st ≠ .outOfFuel := by
  obtain ⟨rank, hrank⟩ := hac
  unfold exec
  cases h0 : p[0]? with
  | none => intro h; nomatch h
  | some blk =>
      simp only []
      obtain ⟨h0_lt, hblk⟩ := List.getElem?_eq_some_iff.1 h0
      subst hblk
      have h0_mem : 0 ∈ List.range p.length := List.mem_range.2 h0_lt
      have herase := sum_map_erase (blkCost p) (List.range p.length) h0_mem
      rw [range_blkCost_eq_fuelBound p] at herase
      have hbc0 : blkCost p 0 = (p[0]'h0_lt).stmts.length + 1 := by
        simp [blkCost, List.getElem?_eq_getElem h0_lt]
      apply runBlock_ne_outOfFuel_of_acyclic p rank hrank f 0 0 h0_lt _ ((List.range p.length).erase 0) st
      · intro k hk hrk
        exact (List.mem_erase_of_ne (fun heq : k = 0 => by subst heq; omega)).2 (List.mem_range.2 hk)
      · omega

end Toy.SymEx.Proofs
