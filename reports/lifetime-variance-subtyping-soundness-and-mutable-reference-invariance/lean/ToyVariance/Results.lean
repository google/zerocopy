import ToyVariance.Basic
import ToyVariance.Alg
import ToyVariance.Lang
import ToyVariance.Programs
import ToyVariance.Examples
import ToyVariance.Soundness
import ToyVariance.Maximality

/-!
# Results

These are statements about the toy model of this package; they neither establish nor refute the
corresponding claims about Rust or rustc.
-/

namespace Toy.Variance

/-! ## General lemmas -/

/-- Soundness is antitone in the subtyping relation. -/
theorem Sound.of_sub {R₁ R₂ : Ty → Ty → Prop} (h : ∀ S T, R₁ S T → R₂ S T) (hs : Sound R₂) :
    Sound R₁ :=
  fun P ⟨sub, hsub, hc⟩ => hs P ⟨sub, fun S T h' => h S T (hsub S T h'), hc⟩

/-- Typing is monotone in the subtyping relation. -/
theorem Typed.mono {R₁ R₂ : Ty → Ty → Prop} (h : ∀ S T, R₁ S T → R₂ S T) {P : List Stmt}
    (ht : Typed R₁ P) : Typed R₂ P :=
  let ⟨sub, hsub, hc⟩ := ht
  ⟨sub, fun S T h' => h S T (hsub S T h'), hc⟩

theorem AdmitsDanglingAccess.mono {R₁ R₂ : Ty → Ty → Prop} (h : ∀ S T, R₁ S T → R₂ S T)
    (ha : AdmitsDanglingAccess R₁) : AdmitsDanglingAccess R₂ :=
  let ⟨P, ht, hd⟩ := ha
  ⟨P, ht.mono h, hd⟩

/-- A dangling access refutes soundness. -/
theorem AdmitsDanglingAccess.not_sound {R : Ty → Ty → Prop} (ha : AdmitsDanglingAccess R) :
    ¬ Sound R :=
  let ⟨_, ht, fuel, hd⟩ := ha
  not_sound_of_stuck ht fuel (isStuck_of_isDangling hd)

theorem Sound.not_admitsDanglingAccess {R : Ty → Ty → Prop} (hs : Sound R) :
    ¬ AdmitsDanglingAccess R :=
  fun ha => ha.not_sound hs

theorem Variance.le_bi (v : Variance) : v.le .bi = true := by cases v <;> rfl

theorem Variance.Rel.mono {α : Type} {v w : Variance} {R : α → α → Prop} {a b : α}
    (h : v.le w = true) (hr : Variance.Rel v R a b) : Variance.Rel w R a b :=
  ⟨fun hw => hr.1 (Variance.le_fwd h hw), fun hw => hr.2 (Variance.le_bwd h hw)⟩

theorem Table.le_set_of_le {t : Table} {p : Pos} {v w : Variance} (h : v.le w = true) :
    Table.le (t.set p v) (t.set p w) := by
  intro q
  by_cases hq : q = p
  · subst hq; simp [Table.set, h]
  · simp only [Table.set, hq, ite_false]; exact Table.le_refl t q

/-- Dangling accesses propagate to more permissive tables. -/
theorem admitsDanglingAccess_of_table_le {t₁ t₂ : Table} (h : Table.le t₁ t₂)
    (ha : AdmitsDanglingAccess (SubGen t₁ NoAx)) : AdmitsDanglingAccess (SubGen t₂ NoAx) :=
  ha.mono (fun _ _ h' => SubGen.lift h (fun _ _ h => h.elim) h')

/-! ## R1: soundness of tables bounded by `safeTable` -/

/-- **R1.** Every variance table that is pointwise at most as permissive as `safeTable`
(`rustTable` with `PhantomData` bivariant) yields a sound type system: every program accepted
with the generated subtyping (reflexivity, transitivity, table congruences) never reaches a
dangling access or any other stuck state. -/
theorem table_le_safeTable_typing_sound (tbl : Table) (h : Table.le tbl safeTable) :
    Sound (SubGen tbl NoAx) :=
  Sound.of_sub (fun _ _ hs => MSub.of_safeTable (SubGen.lift h (fun _ _ hx => hx.elim) hs))
    MSub_sound

/-- The Rust table itself is sound (instance of R1). -/
theorem rustTable_typing_sound : Sound (SubGen rustTable NoAx) :=
  table_le_safeTable_typing_sound rustTable rustTable_le_safeTable

/-- Non-vacuity of R1: `rustTable` satisfies the hypothesis, and a program whose copy uses the
proper coercion `&'static nat ≤ &'sh nat` is typed with the generated relation. -/
theorem table_le_safeTable_typing_sound_nonvacuous :
    Table.le rustTable safeTable ∧ Typed (SubGen rustTable NoAx) progCoerceShrink :=
  ⟨rustTable_le_safeTable, progCoerceShrink_typed⟩

/-- Positive example of `Sound` beyond the Rust table: `safeTable` itself. -/
theorem safeTable_typing_sound : Sound (SubGen safeTable NoAx) :=
  table_le_safeTable_typing_sound safeTable (Table.le_refl _)

/-- Negative example of `Sound`. -/
theorem not_sound_example : ¬ Sound (SubGen (rustTable.set .refMutTy .co) NoAx) :=
  admitsDanglingAccess_example.not_sound

/-- A table whose lifetime positions (and `PhantomData`) are invariant and whose other positions
are all covariant. -/
def rigidLftTable : Table
  | .refLft => .inv
  | .refMutLft => .inv
  | .phantom => .inv
  | _ => .co

theorem Lft.eq_of_outlives_of_outlives {a b : Lft} (h₁ : a.outlives b = true)
    (h₂ : b.outlives a = true) : a = b := by
  cases a <;> cases b <;> simp_all [Lft.outlives] <;> omega

/-- Under `rigidLftTable` the generated relation is equality. -/
theorem rigidLftTable_subGen_eq {S T : Ty} (h : SubGen rigidLftTable NoAx S T) : S = T := by
  induction h with
  | refl => rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | base h => exact h.elim
  | ref hl _ _ ihf _ =>
    rw [Lft.eq_of_outlives_of_outlives (hl.1 rfl) (hl.2 rfl), ihf rfl]
  | refMut hl _ _ ihf _ =>
    rw [Lft.eq_of_outlives_of_outlives (hl.1 rfl) (hl.2 rfl), ihf rfl]
  | cell _ _ ihf _ => rw [ihf rfl]
  | fn _ _ _ _ iha _ ihc _ => rw [iha rfl, ihc rfl]
  | prod _ _ _ _ iha _ ihc _ => rw [iha rfl, ihc rfl]
  | phantom _ _ ihf _ => rw [ihf rfl]

/-- Counterexample for the converse of R1: `rigidLftTable` violates the hypothesis of R1
(`&mut` and `Cell` are covariant and the `fn` argument is covariant) and is sound. -/
theorem rigidLftTable_not_le_safeTable_sound :
    ¬ Table.le rigidLftTable safeTable ∧ Sound (SubGen rigidLftTable NoAx) :=
  ⟨fun h => Bool.noConfusion (h .refMutTy),
    Sound.of_sub (fun S T h => by rw [rigidLftTable_subGen_eq h]; exact SubGen.refl _)
      rustTable_typing_sound⟩

/-- Under `safeTable`, invariance is mutual subtyping, not syntactic equality:
`&'static mut PhantomData<nat> ≤ &'static mut PhantomData<()>`. -/
theorem safeTable_refMut_phantom_coerce :
    SubGen safeTable NoAx (.refMut .static (.phantom .nat)) (.refMut .static (.phantom .unit)) :=
  (subGen_iff_subAlg _ _ _).2 (by decide)

/-! ## R1-sem: syntactic subtyping implies semantic subtyping -/

/-- **R1-sem.** Syntactic subtyping under `rustTable` implies semantic subtyping. -/
theorem rustTable_subGen_implies_semSub {S T : Ty} (h : SubGen rustTable NoAx S T) :
    SemSub S T :=
  Sound.of_sub (fun _ _ hxy => SubGen.lift (Table.le_refl _)
    (fun A B hab => by obtain ⟨rfl, rfl⟩ := hab; exact h) hxy) rustTable_typing_sound

/-- Non-vacuity of R1-sem: a proper pair satisfies the hypothesis, and a program using it as
the extra generator is typed. -/
theorem rustTable_subGen_implies_semSub_nonvacuous :
    SubGen rustTable NoAx rs rsh ∧ rs ≠ rsh ∧
      Typed (SubGen rustTable (fun A B => A = rs ∧ B = rsh)) progR1Sem :=
  ⟨subGen_rust_rs_rsh, by decide, typed_of_checks_one (SubGen.base ⟨rfl, rfl⟩) 20 (by decide)⟩

/-- Positive example of `SemSub`. -/
theorem semSub_rs_rsh : SemSub rs rsh := rustTable_subGen_implies_semSub subGen_rust_rs_rsh

/-- Counterexample for the hypothesis of R1-sem (and negative example of `SemSub`): the
coercion `&'static mut &'static nat ≤ &'sh mut &'sh nat` is not derivable under `rustTable`,
and it is not a semantic subtyping (adding it admits `progRefMutCo`). -/
theorem not_semSub_refMut_shrink :
    ¬ SubGen rustTable NoAx (.refMut .static rs) (.refMut sh rsh) ∧
      ¬ SemSub (.refMut .static rs) (.refMut sh rsh) := by
  refine ⟨by rw [subGen_iff_subAlg]; decide, ?_⟩
  exact not_sound_of_stuck (typed_of_checks_one (SubGen.base ⟨rfl, rfl⟩) 40 (by decide)) 40
    (P := progRefMutCo) (by decide)

/-- The converse of R1-sem fails: `PhantomData<&'sh nat> ≤ PhantomData<&'static nat>` is a
semantic subtyping but is not derivable under `rustTable`. -/
theorem semSub_phantom_not_subGen :
    SemSub (.phantom rsh) (.phantom rs) ∧ ¬ SubGen rustTable NoAx (.phantom rsh) (.phantom rs) := by
  refine ⟨?_, by rw [subGen_iff_subAlg]; decide⟩
  refine Sound.of_sub (fun _ _ h => ?_) MSub_sound
  exact MSub.of_safeTable (SubGen.lift rustTable_le_safeTable
    (fun A B hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact SubGen.phantom (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h)) h)

/-! ## R2: `&mut T` must be invariant in `T` -/

/-- **R2.** With `&mut` covariant in `T` (all other entries as in `rustTable`), the program
`progRefMutCo` (`r : &'static mut &'static nat`, `*r = s` through a covariant alias,
`s : &'sh nat`, end `'sh`, read `**r`) is accepted and reaches the dangling-access state. -/
theorem refMut_covariant_in_T_admits_dangling_read :
    Typed (SubGen (rustTable.set .refMutTy .co) NoAx) progRefMutCo ∧
      (exec 40 St.init Env.empty progRefMutCo).isDangling = true :=
  ⟨typed_of_checks 40 (by decide), by decide⟩

theorem refMut_covariant_in_T_admits_dangling :
    AdmitsDanglingAccess (SubGen (rustTable.set .refMutTy .co) NoAx) :=
  ⟨_, refMut_covariant_in_T_admits_dangling_read.1, 40,
    refMut_covariant_in_T_admits_dangling_read.2⟩

theorem refMut_covariant_in_T_unsound : ¬ Sound (SubGen (rustTable.set .refMutTy .co) NoAx) :=
  refMut_covariant_in_T_admits_dangling.not_sound

/-- Positive control for R2: under `rustTable` the coercion the program relies on is not
derivable, and the program is not typed (for every oracle contained in the relation and every
checker fuel). -/
theorem rustTable_rejects_refMut_covariant_coercion :
    ¬ SubGen rustTable NoAx (.refMut .static rs) (.refMut sh rsh) ∧
      ¬ Typed (SubGen rustTable NoAx) progRefMutCo :=
  ⟨by rw [subGen_iff_subAlg]; decide, not_typed_of_checks_false 40 (by decide) (by decide)⟩

/-- Counterexample for the hypothesis of R1, in canonical form: the table of R2 is not at most
as permissive as `safeTable`, and it is unsound. -/
theorem refMut_co_table_not_le_safeTable_unsound :
    ¬ Table.le (rustTable.set .refMutTy .co) safeTable ∧
      ¬ Sound (SubGen (rustTable.set .refMutTy .co) NoAx) :=
  ⟨fun h => Bool.noConfusion (h .refMutTy), refMut_covariant_in_T_unsound⟩

/-! ## R3: `fn` must be contravariant in its argument -/

/-- **R3.** With `fn` covariant in its argument, the identity `f : fn(&'static nat) ->
&'static nat` is accepted at `fn(&'sh nat) -> &'static nat`; applying it to `s : &'sh nat`,
ending `'sh` and reading the result reaches the dangling-access state. -/
theorem fn_covariant_in_arg_admits_dangling_read :
    Typed (SubGen (rustTable.set .fnArg .co) NoAx) progFnArgCo ∧
      (exec 40 St.init Env.empty progFnArgCo).isDangling = true :=
  ⟨typed_of_checks 40 (by decide), by decide⟩

theorem fn_covariant_in_arg_admits_dangling :
    AdmitsDanglingAccess (SubGen (rustTable.set .fnArg .co) NoAx) :=
  ⟨_, fn_covariant_in_arg_admits_dangling_read.1, 40, fn_covariant_in_arg_admits_dangling_read.2⟩

theorem fn_covariant_in_arg_unsound : ¬ Sound (SubGen (rustTable.set .fnArg .co) NoAx) :=
  fn_covariant_in_arg_admits_dangling.not_sound

/-- Positive control for R3. -/
theorem rustTable_rejects_fn_covariant_arg_coercion :
    ¬ SubGen rustTable NoAx (.fn rs rs) (.fn rsh rs) ∧
      ¬ Typed (SubGen rustTable NoAx) progFnArgCo :=
  ⟨by rw [subGen_iff_subAlg]; decide, not_typed_of_checks_false 40 (by decide) (by decide)⟩

/-! ## R4: `Cell<T>` must be invariant -/

/-- **R4.** With `Cell` covariant, `c : &'static Cell<&'static nat>` is accepted at
`&'static Cell<&'sh nat>`; setting it to `s : &'sh nat` through that alias, ending `'sh`, and
reading `*c.get()` reaches the dangling-access state. -/
theorem cell_covariant_admits_dangling_read :
    Typed (SubGen (rustTable.set .cell .co) NoAx) progCellCo ∧
      (exec 40 St.init Env.empty progCellCo).isDangling = true :=
  ⟨typed_of_checks 40 (by decide), by decide⟩

theorem cell_covariant_admits_dangling :
    AdmitsDanglingAccess (SubGen (rustTable.set .cell .co) NoAx) :=
  ⟨_, cell_covariant_admits_dangling_read.1, 40, cell_covariant_admits_dangling_read.2⟩

theorem cell_covariant_unsound : ¬ Sound (SubGen (rustTable.set .cell .co) NoAx) :=
  cell_covariant_admits_dangling.not_sound

/-- Positive control for R4. -/
theorem rustTable_rejects_cell_covariant_coercion :
    ¬ SubGen rustTable NoAx (.ref .static (.cell rs)) (.ref .static (.cell rsh)) ∧
      ¬ Typed (SubGen rustTable NoAx) progCellCo :=
  ⟨by rw [subGen_iff_subAlg]; decide, not_typed_of_checks_false 40 (by decide) (by decide)⟩

/-! ## Remaining base counterexamples -/

theorem refMut_contravariant_in_T_admits_dangling :
    AdmitsDanglingAccess (SubGen (rustTable.set .refMutTy .contra) NoAx) :=
  ⟨progRefMutContra, typed_of_checks 40 (by decide), 40, by decide⟩

theorem cell_contravariant_admits_dangling :
    AdmitsDanglingAccess (SubGen (rustTable.set .cell .contra) NoAx) :=
  ⟨progCellContra, typed_of_checks 40 (by decide), 40, by decide⟩

theorem fn_contravariant_in_result_admits_dangling :
    AdmitsDanglingAccess (SubGen (rustTable.set .fnRes .contra) NoAx) :=
  ⟨progFnResContra, typed_of_checks 40 (by decide), 40, by decide⟩

theorem ref_contravariant_in_lifetime_admits_dangling :
    AdmitsDanglingAccess (SubGen (rustTable.set .refLft .contra) NoAx) :=
  ⟨progRefLftContra, typed_of_checks 40 (by decide), 40, by decide⟩

theorem ref_contravariant_in_T_admits_dangling :
    AdmitsDanglingAccess (SubGen (rustTable.set .refTy .contra) NoAx) :=
  ⟨progRefTyContra, typed_of_checks 40 (by decide), 40, by decide⟩

theorem refMut_contravariant_in_lifetime_admits_dangling :
    AdmitsDanglingAccess (SubGen (rustTable.set .refMutLft .contra) NoAx) :=
  ⟨progRefMutLftContra, typed_of_checks 40 (by decide), 40, by decide⟩

theorem prod_contravariant_left_admits_dangling :
    AdmitsDanglingAccess (SubGen (rustTable.set .prodL .contra) NoAx) :=
  ⟨progProdLContra, typed_of_checks 40 (by decide), 40, by decide⟩

theorem prod_contravariant_right_admits_dangling :
    AdmitsDanglingAccess (SubGen (rustTable.set .prodR .contra) NoAx) :=
  ⟨progProdRContra, typed_of_checks 40 (by decide), 40, by decide⟩

/-! ## R-forced: every non-`PhantomData` entry of the Rust table is forced -/

/-- **R-forced.** For every position other than `PhantomData`, replacing the Rust entry by any
variance that is not at most as permissive as it (a strictly more permissive one, or an
incomparable one such as a covariant `fn` argument) yields a table that admits a dangling
access. -/
theorem rustTable_entry_not_le_admits_dangling (p : Pos) (hp : p ≠ .phantom) (v : Variance)
    (hv : v.le (rustTable p) = false) :
    AdmitsDanglingAccess (SubGen (rustTable.set p v) NoAx) := by
  cases p <;> cases v <;> first
    | exact absurd hv (by decide)
    | exact absurd rfl hp
    | exact ref_contravariant_in_lifetime_admits_dangling
    | exact ref_contravariant_in_T_admits_dangling
    | exact refMut_contravariant_in_lifetime_admits_dangling
    | exact refMut_covariant_in_T_admits_dangling
    | exact refMut_contravariant_in_T_admits_dangling
    | exact cell_covariant_admits_dangling
    | exact cell_contravariant_admits_dangling
    | exact fn_covariant_in_arg_admits_dangling
    | exact fn_contravariant_in_result_admits_dangling
    | exact prod_contravariant_left_admits_dangling
    | exact prod_contravariant_right_admits_dangling
    | exact admitsDanglingAccess_of_table_le (Table.le_set_of_le rfl)
        ref_contravariant_in_lifetime_admits_dangling
    | exact admitsDanglingAccess_of_table_le (Table.le_set_of_le rfl)
        ref_contravariant_in_T_admits_dangling
    | exact admitsDanglingAccess_of_table_le (Table.le_set_of_le rfl)
        refMut_contravariant_in_lifetime_admits_dangling
    | exact admitsDanglingAccess_of_table_le (Table.le_set_of_le rfl)
        refMut_covariant_in_T_admits_dangling
    | exact admitsDanglingAccess_of_table_le (Table.le_set_of_le rfl)
        cell_covariant_admits_dangling
    | exact admitsDanglingAccess_of_table_le (Table.le_set_of_le rfl)
        fn_covariant_in_arg_admits_dangling
    | exact admitsDanglingAccess_of_table_le (Table.le_set_of_le rfl)
        fn_contravariant_in_result_admits_dangling
    | exact admitsDanglingAccess_of_table_le (Table.le_set_of_le rfl)
        prod_contravariant_left_admits_dangling
    | exact admitsDanglingAccess_of_table_le (Table.le_set_of_le rfl)
        prod_contravariant_right_admits_dangling

theorem rustTable_entry_not_le_unsound (p : Pos) (hp : p ≠ .phantom) (v : Variance)
    (hv : v.le (rustTable p) = false) : ¬ Sound (SubGen (rustTable.set p v) NoAx) :=
  (rustTable_entry_not_le_admits_dangling p hp v hv).not_sound

/-- Non-vacuity of R-forced: `&mut` made covariant in `T` satisfies its hypotheses. -/
theorem rustTable_entry_not_le_admits_dangling_nonvacuous :
    Pos.refMutTy ≠ .phantom ∧ Variance.co.le (rustTable .refMutTy) = false :=
  ⟨by decide, rfl⟩

/-- The hypothesis `hv` of R-forced also covers incomparable variances. -/
theorem rustTable_entry_not_le_covers_incomparable :
    Variance.co.le (rustTable .fnArg) = false ∧ (rustTable .fnArg).le .co = false :=
  ⟨rfl, rfl⟩

/-- Counterexample for the hypothesis `p ≠ phantom` of R-forced, in canonical form: making
`PhantomData` bivariant satisfies `hv`, and the resulting table is sound, so it admits no
dangling access. -/
theorem phantom_bi_not_le_and_sound :
    Variance.bi.le (rustTable .phantom) = false ∧
      Sound (SubGen (rustTable.set .phantom .bi) NoAx) ∧
      ¬ AdmitsDanglingAccess (SubGen (rustTable.set .phantom .bi) NoAx) :=
  ⟨rfl, safeTable_typing_sound, safeTable_typing_sound.not_admitsDanglingAccess⟩

/-- Counterexample for the hypothesis `hv` of R-forced, in canonical form: the Rust entry
itself (`p = refMutTy`, `v = inv`) gives a table that admits no dangling access. -/
theorem rustTable_entry_le_no_dangling :
    Pos.refMutTy ≠ .phantom ∧ Variance.inv.le (rustTable .refMutTy) = true ∧
      ¬ AdmitsDanglingAccess (SubGen (rustTable.set .refMutTy .inv) NoAx) := by
  refine ⟨by decide, rfl, Sound.not_admitsDanglingAccess ?_⟩
  apply table_le_safeTable_typing_sound
  intro q
  cases q <;> rfl

/-- Positive control for R-forced: every coercion used by the base counterexample programs
is rejected under `rustTable`. -/
theorem rustTable_rejects_all_forcing_coercions :
    subAlg rustTable true rsh rs = false ∧
    subAlg rustTable true (.ref .static rsh) (.ref .static rs) = false ∧
    subAlg rustTable true (.refMut sh .nat) (.refMut .static .nat) = false ∧
    subAlg rustTable true (.refMut .static rs) (.refMut sh rsh) = false ∧
    subAlg rustTable true (.refMut .static rsh) (.refMut .static rs) = false ∧
    subAlg rustTable true (.ref .static (.cell rs)) (.ref .static (.cell rsh)) = false ∧
    subAlg rustTable true (.ref .static (.cell rsh)) (.ref .static (.cell rs)) = false ∧
    subAlg rustTable true (.fn rs rs) (.fn rsh rs) = false ∧
    subAlg rustTable true (.fn rsh rsh) (.fn rsh rs) = false ∧
    subAlg rustTable true (.prod rsh .unit) (.prod rs .unit) = false ∧
    subAlg rustTable true (.prod .unit rsh) (.prod .unit rs) = false := by
  decide

/-! ## R-iff -/

/-- **R-iff.** For every position other than `PhantomData`, the modified table is sound iff
the new variance is at most as permissive as the Rust entry. -/
theorem rustTable_entry_sound_iff (p : Pos) (hp : p ≠ .phantom) (v : Variance) :
    Sound (SubGen (rustTable.set p v) NoAx) ↔ v.le (rustTable p) = true := by
  constructor
  · intro hs
    cases h : v.le (rustTable p)
    · exact absurd hs (rustTable_entry_not_le_unsound p hp v h)
    · rfl
  · intro h
    apply table_le_safeTable_typing_sound
    intro q
    by_cases hq : q = p
    · subst hq
      simp only [Table.set, ite_true, safeTable, hp, ite_false]
      exact h
    · simp only [Table.set, hq, ite_false]
      exact rustTable_le_safeTable q

theorem rustTable_entry_sound_iff_nonvacuous :
    Pos.cell ≠ .phantom ∧ Variance.inv.le (rustTable .cell) = true :=
  ⟨by decide, rfl⟩

/-! ## R-phantom -/

/-- **R-phantom.** For every variance `v` (including bivariant), replacing the `PhantomData`
entry of `rustTable` by `v` gives a sound toy type system. Instance of R1. -/
theorem phantom_entry_any_variance_sound (v : Variance) :
    Sound (SubGen (rustTable.set .phantom v) NoAx) := by
  apply table_le_safeTable_typing_sound
  intro q
  by_cases hq : q = .phantom
  · subst hq; simp only [Table.set, ite_true, safeTable]; exact Variance.le_bi v
  · simp only [Table.set, hq, ite_false]; exact rustTable_le_safeTable q

/-- `PhantomData` made bivariant can coerce between `PhantomData` of any two types. -/
theorem phantom_bivariant_derives_any_phantom_coercion (A B : Ty) :
    SubGen (rustTable.set .phantom .bi) NoAx (.phantom A) (.phantom B) :=
  SubGen.phantom (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h)

/-- Non-vacuity of R-phantom at `v = bi`: a program that coerces
`PhantomData<&'sh nat>` to `PhantomData<&'static nat>` is typed under the bivariant entry and
not typed under `rustTable` (so the instance is not covered by the Rust table). -/
theorem phantom_entry_any_variance_sound_nonvacuous :
    Typed (SubGen (rustTable.set .phantom .bi) NoAx) progPhantomBi ∧
      ¬ Typed (SubGen rustTable NoAx) progPhantomBi :=
  ⟨typed_of_checks 20 (by decide), not_typed_of_checks_false 20 (by decide) (by decide)⟩

/-! ## R5: variance inference for struct bodies -/

theorem Variance.rel_of_rel_comp {α : Type} {R : α → α → Prop} {A B : α} (u w : Variance)
    (h : Variance.Rel (u.comp w) R A B) :
    (u.fwd = true → Variance.Rel w R A B) ∧ (u.bwd = true → Variance.Rel w R B A) := by
  obtain ⟨h₁, h₂⟩ := h
  cases u <;> cases w <;>
    simp_all [Variance.Rel, Variance.comp, Variance.ofDirs, Variance.fwd, Variance.bwd]

theorem Variance.rel_of_rel_meet {α : Type} {R : α → α → Prop} {A B : α} (v w : Variance)
    (h : Variance.Rel (v.meet w) R A B) : Variance.Rel v R A B ∧ Variance.Rel w R A B := by
  obtain ⟨h₁, h₂⟩ := h
  cases v <;> cases w <;>
    simp_all [Variance.Rel, Variance.meet, Variance.ofDirs, Variance.fwd, Variance.bwd]

theorem LRel.refl (v : Variance) (a : Lft) : LRel v a a :=
  ⟨fun _ => Lft.outlives_refl a, fun _ => Lft.outlives_refl a⟩

/-- **R5a.** Inferred variance is admissible: if `A` and `B` are related along the inferred
variance of `F`, then `F[A] ≤ F[B]` is derivable (for any table). -/
theorem inferVar_admissible (tbl : Table) (F A B : Ty)
    (h : Variance.Rel (inferVar tbl F) (SubGen tbl NoAx) A B) :
    SubGen tbl NoAx (F.subst A) (F.subst B) := by
  induction F generalizing A B with
  | unit => exact SubGen.refl _
  | nat => exact SubGen.refl _
  | param => exact h.1 rfl
  | ref l T ih =>
    have hc := Variance.rel_of_rel_comp _ _ h
    exact SubGen.ref (LRel.refl _ l) (fun hf => ih A B (hc.1 hf)) (fun hb => ih B A (hc.2 hb))
  | refMut l T ih =>
    have hc := Variance.rel_of_rel_comp _ _ h
    exact SubGen.refMut (LRel.refl _ l) (fun hf => ih A B (hc.1 hf)) (fun hb => ih B A (hc.2 hb))
  | cell T ih =>
    have hc := Variance.rel_of_rel_comp _ _ h
    exact SubGen.cell (fun hf => ih A B (hc.1 hf)) (fun hb => ih B A (hc.2 hb))
  | phantom T ih =>
    have hc := Variance.rel_of_rel_comp _ _ h
    exact SubGen.phantom (fun hf => ih A B (hc.1 hf)) (fun hb => ih B A (hc.2 hb))
  | fn T U ihT ihU =>
    obtain ⟨h₁, h₂⟩ := Variance.rel_of_rel_meet _ _ h
    have c₁ := Variance.rel_of_rel_comp _ _ h₁
    have c₂ := Variance.rel_of_rel_comp _ _ h₂
    exact SubGen.fn (fun hf => ihT A B (c₁.1 hf)) (fun hb => ihT B A (c₁.2 hb))
      (fun hf => ihU A B (c₂.1 hf)) (fun hb => ihU B A (c₂.2 hb))
  | prod T U ihT ihU =>
    obtain ⟨h₁, h₂⟩ := Variance.rel_of_rel_meet _ _ h
    have c₁ := Variance.rel_of_rel_comp _ _ h₁
    have c₂ := Variance.rel_of_rel_comp _ _ h₂
    exact SubGen.prod (fun hf => ihT A B (c₁.1 hf)) (fun hb => ihT B A (c₁.2 hb))
      (fun hf => ihU A B (c₂.1 hf)) (fun hb => ihU B A (c₂.2 hb))

/-- Non-vacuity of R5a with a proper pair: for `F = (&'static T, ())` (inferred covariant),
`A = &'static nat` and `B = &'sh nat` are distinct and related along the inferred variance. -/
theorem inferVar_admissible_nonvacuous :
    rs ≠ rsh ∧
      Variance.Rel (inferVar rustTable (.prod (.ref .static .param) .unit))
        (SubGen rustTable NoAx) rs rsh :=
  ⟨by decide, fun _ => subGen_rust_rs_rsh, fun h => Bool.noConfusion h⟩

/-- Counterexample for the hypothesis of R5a, in canonical form: for `F = Cell<T>` (inferred
invariant), `A = &'static nat` and `B = &'sh nat` are not related along `inv`, and
`F[A] ≤ F[B]` is not derivable. -/
theorem inferVar_admissible_rel_counterexample :
    ¬ Variance.Rel (inferVar rustTable (.cell .param)) (SubGen rustTable NoAx) rs rsh ∧
      ¬ SubGen rustTable NoAx ((Ty.cell .param).subst rs) ((Ty.cell .param).subst rsh) := by
  refine ⟨fun h => not_subGen_rust_rsh_rs (h.2 rfl), ?_⟩
  rw [subGen_iff_subAlg]; decide

/-- **R5b.** The schematic body rule at any declared variance at most as permissive as the
inferred one adds no subtyping pairs: the generated relation equals the Rust-table relation. -/
theorem bodyAx_le_inferVar_iff (F : Ty) (v : Variance) (hv : v.le (inferVar rustTable F) = true)
    (S T : Ty) : SubGen rustTable (BodyAx F v) S T ↔ SubGen rustTable NoAx S T := by
  constructor
  · intro h
    refine SubGen.lift (Table.le_refl _) (fun S T hst => ?_) h
    obtain ⟨A, B, _, _, hS, hT, hrel⟩ := hst
    subst hS; subst hT
    exact inferVar_admissible rustTable F A B (hrel.mono hv)
  · exact SubGen.lift (Table.le_refl _) (fun _ _ h => h.elim)

theorem Variance.le_refl (v : Variance) : v.le v = true := by cases v <;> rfl

/-- R5b at the inferred variance itself. -/
theorem bodyAx_inferVar_iff (F S T : Ty) :
    SubGen rustTable (BodyAx F (inferVar rustTable F)) S T ↔ SubGen rustTable NoAx S T :=
  bodyAx_le_inferVar_iff F _ (Variance.le_refl _) S T

/-- Corollary of R5b and R1: the body rule at a variance at most as permissive as the inferred
one is sound. -/
theorem bodyRule_le_inferVar_sound (F : Ty) (v : Variance)
    (hv : v.le (inferVar rustTable F) = true) : Sound (SubGen rustTable (BodyAx F v)) :=
  Sound.of_sub (fun S T h => (bodyAx_le_inferVar_iff F v hv S T).1 h) rustTable_typing_sound

/-- Non-vacuity of R5b: for `F = (T, ())` at the inferred variance (`co`), the rule contains the
proper pair `(&'static nat, ()) ≤ (&'sh nat, ())`, and a program using it is typed. -/
theorem bodyAx_le_inferVar_iff_nonvacuous :
    Variance.co.le (inferVar rustTable (.prod .param .unit)) = true ∧
      BodyAx (.prod .param .unit) .co (.prod rs .unit) (.prod rsh .unit) ∧ rs ≠ rsh ∧
      Typed (SubGen rustTable (BodyAx (.prod .param .unit) .co)) progBodyCov :=
  ⟨rfl, bodyAx_example, by decide, typed_of_checks_one (SubGen.base bodyAx_example) 30 (by decide)⟩

/-- Counterexample for the hypothesis `hv` of R5b, in canonical form: for `F = param` at
`contra` (not at most as permissive as the inferred `co`), the rule derives
`&'sh nat ≤ &'static nat`, which the Rust-table relation does not derive. -/
theorem bodyAx_param_contra_adds_pair :
    Variance.contra.le (inferVar rustTable .param) = false ∧
      SubGen rustTable (BodyAx .param .contra) rsh rs ∧ ¬ SubGen rustTable NoAx rsh rs :=
  ⟨rfl, SubGen.base ⟨rsh, rs, rfl, rfl, rfl, rfl, fun h => Bool.noConfusion h,
    fun _ => subGen_rust_rs_rsh⟩, not_subGen_rust_rsh_rs⟩

/-- A declared variance stricter than the inferred one does not remove built-in structural
coercions between the unfolded body types (the rule is not nominal). -/
theorem bodyAx_inv_still_covariant :
    SubGen rustTable (BodyAx (.prod .param .unit) .inv)
      ((Ty.prod .param .unit).subst rs) ((Ty.prod .param .unit).subst rsh) :=
  SubGen.prod (fun _ => SubGen.lift (Table.le_refl _) (fun _ _ h => h.elim) subGen_rust_rs_rsh)
    (fun h => Bool.noConfusion h) (fun _ => SubGen.refl _) (fun h => Bool.noConfusion h)

/-- A declared variance more permissive than the inferred one adds coercions between ordinary
built-in types: for `F = param` at `contra`, `&'sh nat ≤ &'static nat`. -/
theorem bodyAx_param_contra_coerces_bare_refs :
    Typed (SubGen rustTable (BodyAx .param .contra)) progRefLftContra := by
  have hax : SubGen rustTable (BodyAx .param .contra) rsh rs :=
    SubGen.base ⟨rsh, rs, rfl, rfl, rfl, rfl, fun h => Bool.noConfusion h,
      fun _ => subGen_rust_rs_rsh⟩
  exact typed_of_checks_one hax 40 (by decide)

/-- **R5c.** Maximality of inferred variance for first-order data bodies: for a body `F` built
from `unit`, `nat`, `param`, tuples, `&`, `&mut`, and `&Cell` (`F.dataBody`), the schematic body
rule at any variance `v` that is not at most as permissive as the inferred one admits a dangling
access. -/
theorem bodyRule_not_le_inferVar_admits_dangling_of_dataBody (F : Ty) (hF : F.dataBody = true)
    (v : Variance) (hv : v.le (inferVar rustTable F) = false) :
    AdmitsDanglingAccess (SubGen rustTable (BodyAx F v)) :=
  admitsDanglingAccess_of_dataBody_not_le F hF v hv

theorem bodyRule_not_le_inferVar_unsound_of_dataBody (F : Ty) (hF : F.dataBody = true)
    (v : Variance) (hv : v.le (inferVar rustTable F) = false) :
    ¬ Sound (SubGen rustTable (BodyAx F v)) :=
  (bodyRule_not_le_inferVar_admits_dangling_of_dataBody F hF v hv).not_sound

/-- R5c instance, `F = &'static Cell<T>` at `co` (inferred `inv`): the witness is `progCellCo`. -/
theorem bodyRule_refCell_co_admits_dangling :
    (Ty.ref .static (.cell .param)).dataBody = true ∧
      Variance.co.le (inferVar rustTable (.ref .static (.cell .param))) = false ∧
      Typed (SubGen rustTable (BodyAx (.ref .static (.cell .param)) .co)) progCellCo ∧
      (exec 40 St.init Env.empty progCellCo).isDangling = true := by
  refine ⟨rfl, rfl, ?_, by decide⟩
  exact typed_of_checks_one (SubGen.base ⟨rs, rsh, rfl, rfl, rfl, rfl,
    fun _ => subGen_rust_rs_rsh, fun h => Bool.noConfusion h⟩) 40 (by decide)

/-- R5c instance, `F = &'static mut T` at `co` (inferred `inv`). -/
theorem bodyRule_refMut_co_admits_dangling :
    (Ty.refMut .static .param).dataBody = true ∧
      Variance.co.le (inferVar rustTable (.refMut .static .param)) = false ∧
      Typed (SubGen rustTable (BodyAx (.refMut .static .param) .co)) progRefMutCoStatic ∧
      (exec 40 St.init Env.empty progRefMutCoStatic).isDangling = true := by
  refine ⟨rfl, rfl, ?_, by decide⟩
  exact typed_of_checks_one (SubGen.base ⟨rs, rsh, rfl, rfl, rfl, rfl,
    fun _ => subGen_rust_rs_rsh, fun h => Bool.noConfusion h⟩) 40 (by decide)

/-- R5c instance, `F = (T, ())` at `contra` (inferred `co`). -/
theorem bodyRule_prod_contra_admits_dangling :
    (Ty.prod .param .unit).dataBody = true ∧
      Variance.contra.le (inferVar rustTable (.prod .param .unit)) = false ∧
      Typed (SubGen rustTable (BodyAx (.prod .param .unit) .contra)) progProdLContra ∧
      (exec 40 St.init Env.empty progProdLContra).isDangling = true := by
  refine ⟨rfl, rfl, ?_, by decide⟩
  exact typed_of_checks_one (SubGen.base ⟨rsh, rs, rfl, rfl, rfl, rfl,
    fun h => Bool.noConfusion h, fun _ => subGen_rust_rs_rsh⟩) 40 (by decide)

/-- Non-vacuity of R5c. -/
theorem bodyRule_not_le_inferVar_admits_dangling_of_dataBody_nonvacuous :
    (Ty.ref .static (.cell .param)).dataBody = true ∧
      Variance.co.le (inferVar rustTable (.ref .static (.cell .param))) = false :=
  ⟨rfl, rfl⟩

/-- Counterexample for the hypothesis `hv` of R5c, in canonical form: for the data body
`&'static mut T`, the declared variance `inv` is at most as permissive as the inferred one, and
the rule admits no dangling access. -/
theorem bodyRule_refMut_inv_no_dangling :
    (Ty.refMut .static .param).dataBody = true ∧
      Variance.inv.le (inferVar rustTable (.refMut .static .param)) = true ∧
      ¬ AdmitsDanglingAccess (SubGen rustTable (BodyAx (.refMut .static .param) .inv)) :=
  ⟨rfl, rfl, (bodyRule_le_inferVar_sound _ _ rfl).not_admitsDanglingAccess⟩

/-- Counterexample for the hypothesis `hF` of R5c, in canonical form (bare `Cell` field): for
`F = (Cell<T>, ())` (inferred `inv`) the declared variance `co` is not at most as permissive as
the inferred one, yet the rule is sound, since a bare `Cell` value is an immutable copy and
there is no shared projection from `&(A, B)` to `&A`. -/
theorem bodyRule_prod_cell_co_sound :
    (Ty.prod (.cell .param) .unit).phantomFree = true ∧
      (Ty.prod (.cell .param) .unit).dataBody = false ∧
      Variance.co.le (inferVar rustTable (.prod (.cell .param) .unit)) = false ∧
      Sound (SubGen rustTable (BodyAx (.prod (.cell .param) .unit) .co)) ∧
      ¬ AdmitsDanglingAccess (SubGen rustTable (BodyAx (.prod (.cell .param) .unit) .co)) :=
  have hs : Sound (SubGen rustTable (BodyAx (.prod (.cell .param) .unit) .co)) :=
    Sound.of_sub (fun _ _ h => MSub.of_prodCellAx h) MSub_sound
  ⟨rfl, rfl, rfl, hs, hs.not_admitsDanglingAccess⟩

/-- Counterexample for the hypothesis `hF` of R5c, in canonical form (higher-order body,
no `Cell`, no `PhantomData`): for `F = fn(fn(T) -> ()) -> ()` (inferred `co`) the declared
variance `contra` is not at most as permissive as the inferred one, yet the rule is sound:
every closure captures only `'static`-typed data and allocates only in `'static`, so a
`fn(T) -> ()` argument passed through a `fn(fn(T) -> ()) -> ()` cannot leak a short-lived
reference, whatever the lifetimes in `T`. -/
theorem bodyRule_fn_fn_contra_sound :
    (Ty.fn (.fn .param .unit) .unit).phantomFree = true ∧
      (Ty.fn (.fn .param .unit) .unit).dataBody = false ∧
      Variance.contra.le (inferVar rustTable (.fn (.fn .param .unit) .unit)) = false ∧
      Sound (SubGen rustTable (BodyAx (.fn (.fn .param .unit) .unit) .contra)) ∧
      ¬ AdmitsDanglingAccess (SubGen rustTable (BodyAx (.fn (.fn .param .unit) .unit) .contra)) :=
  have hs : Sound (SubGen rustTable (BodyAx (.fn (.fn .param .unit) .unit) .contra)) :=
    Sound.of_sub (fun _ _ h => MSub.of_fnFnAx h) MSub_sound
  ⟨rfl, rfl, rfl, hs, hs.not_admitsDanglingAccess⟩

/-- Counterexample for the hypothesis `hF` of R5c, in canonical form (`PhantomData`): for
`F = PhantomData<T>` (inferred `co`) the bivariant rule is sound. -/
theorem bodyRule_phantom_bi_sound :
    (Ty.phantom .param).dataBody = false ∧
      Variance.bi.le (inferVar rustTable (.phantom .param)) = false ∧
      Sound (SubGen rustTable (BodyAx (.phantom .param) .bi)) ∧
      ¬ AdmitsDanglingAccess (SubGen rustTable (BodyAx (.phantom .param) .bi)) := by
  have hs : Sound (SubGen rustTable (BodyAx (.phantom .param) .bi)) := by
    apply Sound.of_sub _ safeTable_typing_sound
    intro X Y hxy
    refine SubGen.lift rustTable_le_safeTable (fun S T hst => ?_) hxy
    obtain ⟨A, B, _, _, hS, hT, _⟩ := hst
    subst hS; subst hT
    exact SubGen.phantom (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h)
  exact ⟨rfl, rfl, hs, hs.not_admitsDanglingAccess⟩

/-- The maximality statement over all `PhantomData`-free bodies is false (refuted by
`bodyRule_prod_cell_co_sound`; `bodyRule_fn_fn_contra_sound` refutes it as well). -/
theorem not_bodyRule_not_le_inferVar_unsound_of_phantomFree :
    ¬ (∀ (F : Ty), F.phantomFree = true → ∀ (v : Variance),
        v.le (inferVar rustTable F) = false → ¬ Sound (SubGen rustTable (BodyAx F v))) := by
  intro h
  obtain ⟨hF, _, hv, hs, _⟩ := bodyRule_prod_cell_co_sound
  exact h _ hF .co hv hs

/-- A non-data body that is still unsound beyond the inferred variance: the bare-`Cell` body
`Cell<T>` at `co`, used under `&` (`&'static Cell<&'static nat> ≤ &'static Cell<&'sh nat>`). -/
theorem bodyRule_cell_co_admits_dangling :
    (Ty.cell .param).dataBody = false ∧
      Variance.co.le (inferVar rustTable (.cell .param)) = false ∧
      Typed (SubGen rustTable (BodyAx (.cell .param) .co)) progCellCo ∧
      (exec 40 St.init Env.empty progCellCo).isDangling = true := by
  refine ⟨rfl, rfl, ?_, by decide⟩
  have hax : SubGen rustTable (BodyAx (.cell .param) .co)
      (.ref .static (.cell rs)) (.ref .static (.cell rsh)) :=
    SubGen.ref ⟨fun _ => rfl, fun h => Bool.noConfusion h⟩
      (fun _ => SubGen.base ⟨rs, rsh, rfl, rfl, rfl, rfl,
        fun _ => subGen_rust_rs_rsh, fun h => Bool.noConfusion h⟩)
      (fun h => Bool.noConfusion h)
  exact typed_of_checks_one hax 40 (by decide)

/-- **R5c-ho.** A higher-order non-data body beyond the inferred variance: for
`F = fn() -> T` (inferred `co`) declared `contra`, the program `progStructFnUnitContra` (a thunk
returning a function that stashes its `&'static nat` argument in a `'static` cell is re-typed as
returning a function that accepts `&'sh nat`) is typed and reaches the dangling-access state. -/
theorem bodyRule_fnUnit_contra_admits_dangling_read :
    (Ty.fn .unit .param).dataBody = false ∧
      Variance.contra.le (inferVar rustTable (.fn .unit .param)) = false ∧
      Typed (SubGen rustTable (BodyAx (.fn .unit .param) .contra)) progStructFnUnitContra ∧
      (exec 60 St.init Env.empty progStructFnUnitContra).isDangling = true := by
  refine ⟨rfl, rfl, ?_, by decide⟩
  have hax : SubGen rustTable (BodyAx (.fn .unit .param) .contra)
      (.fn .unit (.fn rs .unit)) (.fn .unit (.fn rsh .unit)) :=
    SubGen.base ⟨.fn rs .unit, .fn rsh .unit, rfl, rfl, rfl, rfl,
      fun h => Bool.noConfusion h, fun _ => subGen_rust_fn_contra⟩
  exact typed_of_checks_one hax 60 (by decide)

/-- With `v = bi` on `fn(fn(T) -> ()) -> ()` the rule is unsound through an ill-shaped value
(`Res.wrong`): this program reaches `Res.wrong`, not the dangling-access state. -/
theorem bodyRule_fn_fn_bi_wrong_not_dangling :
    Typed (SubGen rustTable (BodyAx (.fn (.fn .param .unit) .unit) .bi)) progFnFnBiWrong ∧
      exec 30 St.init Env.empty progFnFnBiWrong = .wrong ∧
      (exec 30 St.init Env.empty progFnFnBiWrong).isDangling = false := by
  have hax : SubGen rustTable (BodyAx (.fn (.fn .param .unit) .unit) .bi)
      (.fn (.fn .nat .unit) .unit) (.fn (.fn rs .unit) .unit) :=
    SubGen.base ⟨.nat, rs, rfl, rfl, rfl, rfl, fun h => Bool.noConfusion h,
      fun h => Bool.noConfusion h⟩
  exact ⟨typed_of_checks_one hax 30 (by decide), rfl, rfl⟩

/-- Positive control for R5c: at the inferred variance (`inv`) of `&'static Cell<T>`, the
coercion used by `progCellCo` is not derivable. -/
theorem bodyRule_refCell_at_inferVar_rejects_coercion :
    ¬ SubGen rustTable (BodyAx (.ref .static (.cell .param))
        (inferVar rustTable (.ref .static (.cell .param))))
      (.ref .static (.cell rs)) (.ref .static (.cell rsh)) := by
  intro h
  exact rustTable_rejects_cell_covariant_coercion.1 ((bodyAx_inferVar_iff _ _ _).1 h)

end Toy.Variance
