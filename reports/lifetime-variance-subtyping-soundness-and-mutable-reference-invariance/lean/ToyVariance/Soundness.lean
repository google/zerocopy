import ToyVariance.Basic
import ToyVariance.Alg
import ToyVariance.Lang
import ToyVariance.Programs
import ToyVariance.Examples

/-!
# Type soundness of the toy language

`MSub` is an auxiliary relation on types that contains `SubGen safeTable NoAx` (lemma
`MSub.of_safeTable`) and two further families of pairs used by the boundary results for the
schematic body rule (`MSub.of_prodCellAx`, `MSub.of_fnFnAx`). `MSub_sound` proves that every
program accepted with copies along `MSub` never reaches a stuck state. The proof is a syntactic
heap-typing argument:

* a heap typing `htys : List (Lft × Ty)` that only grows (`HeapExt`), with `HeapOk` relating it
  to the runtime heap; `&mut` and `Cell` contents are typed invariantly, `&` and tuples
  covariantly, `PhantomData` values are `()`;
* closures are typed by `BodyChecked` (their body is accepted in body mode for some fuel) and
  capture only `'static`-typed values;
* at top level every variable whose type is live at the current time points only to live
  locations (`EnvTopOk`); inside a call a monotone set of live locations (`LiveSetOk`) plays that
  role, since bodies allocate only in `'static` and cannot end regions.

The second part (`hasEnoughFuel`, `chk_fuel_irrel`, `chk_mono_sub`, `not_typed_of_checks_false`)
shows that the checker's verdict is monotone in the oracle and stable in the fuel, so a rejection
by the complete oracle `subAlg tbl true` at sufficient fuel refutes `Typed (SubGen tbl NoAx)`
for every oracle and every fuel.
-/

set_option linter.unusedVariables false

namespace Toy.Variance
/-! ## Elementary List Helpers -/

theorem get_append_left {α : Type} : ∀ (xs ys : List α) (p : Nat) {v : α},
    xs[p]? = some v → (xs ++ ys)[p]? = some v
  | [], _, _, _, h => by simp at h
  | _ :: _, _, 0, _, h => h
  | _ :: xs, ys, p + 1, _, h => get_append_left xs ys p h

theorem get_append_len {α : Type} : ∀ (xs : List α) (v : α),
    (xs ++ [v])[xs.length]? = some v
  | [], _ => rfl
  | _ :: xs, v => get_append_len xs v

theorem get_some_of_lt {α : Type} : ∀ (xs : List α) (p : Nat),
    p < xs.length → ∃ v, xs[p]? = some v
  | [], _, h => nomatch h
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, p + 1, h => get_some_of_lt xs p (Nat.lt_of_succ_lt_succ h)

theorem len_set {α : Type} : ∀ (xs : List α) (p : Nat) (v : α),
    (xs.set p v).length = xs.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: xs, p + 1, v => congrArg Nat.succ (len_set xs p v)

theorem get_set_eq {α : Type} : ∀ (xs : List α) (p : Nat) (v : α),
    p < xs.length → (xs.set p v)[p]? = some v
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, _ => rfl
  | _ :: xs, p + 1, v, h => get_set_eq xs p v (Nat.lt_of_succ_lt_succ h)

theorem get_set_ne {α : Type} : ∀ (xs : List α) (p q : Nat) (v : α),
    p ≠ q → (xs.set p v)[q]? = xs[q]?
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, hne => absurd rfl hne
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: xs, p + 1, q + 1, v, hne => get_set_ne xs p q v (fun h => hne (congrArg Nat.succ h))

theorem lt_len_of_get_some {α : Type} : ∀ (xs : List α) (p : Nat) {v : α},
    xs[p]? = some v → p < xs.length
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: xs, p + 1, _, h => Nat.succ_lt_succ (lt_len_of_get_some xs p h)

/-! ## 1. Type skeleton erasure, staticization, and the auxiliary relation `MSub` -/

inductive ETy where
  | unit | nat | ref (T : ETy) | refMut (T : ETy) | cell (T : ETy)
  | fn (T U : ETy) | prod (T U : ETy) | phantom | param
  deriving DecidableEq, Repr

def erase : Ty → ETy
  | .unit => .unit | .nat => .nat | .ref _ T => .ref (erase T)
  | .refMut _ T => .refMut (erase T) | .cell T => .cell (erase T)
  | .fn T U => .fn (erase T) (erase U) | .prod T U => .prod (erase T) (erase U)
  | .phantom _ => .phantom | .param => .param

def toStatic : Ty → Ty
  | .unit => .unit | .nat => .nat | .ref _ T => .ref .static (toStatic T)
  | .refMut _ T => .refMut .static (toStatic T) | .cell T => .cell (toStatic T)
  | .fn T U => .fn (toStatic T) (toStatic U) | .prod T U => .prod (toStatic T) (toStatic U)
  | .phantom T => .phantom (toStatic T) | .param => .param

theorem erase_toStatic (T : Ty) : erase (toStatic T) = erase T := by
  induction T <;> simp_all [toStatic, erase]

theorem toStatic_id_of_allStatic {T : Ty} (h : T.allStatic = true) : toStatic T = T := by
  induction T with
  | unit | nat | param => rfl
  | ref l T ih =>
    simp [Ty.allStatic, Ty.liveIn] at h; obtain ⟨rfl, hT⟩ := h; simp [toStatic, ih hT]
  | refMut l T ih =>
    simp [Ty.allStatic, Ty.liveIn] at h; obtain ⟨rfl, hT⟩ := h; simp [toStatic, ih hT]
  | cell T ih => simp [Ty.allStatic, Ty.liveIn] at h; simp [toStatic, ih h]
  | fn T U ihT ihU =>
    simp [Ty.allStatic, Ty.liveIn] at h; simp [toStatic, ihT h.1, ihU h.2]
  | prod T U ihT ihU =>
    simp [Ty.allStatic, Ty.liveIn] at h; simp [toStatic, ihT h.1, ihU h.2]
  | phantom T ih => simp [Ty.allStatic, Ty.liveIn] at h; simp [toStatic, ih h]

theorem allStatic_toStatic (T : Ty) : (toStatic T).allStatic = true := by
  induction T <;> simp_all [toStatic, Ty.allStatic, Ty.liveIn]

inductive MSub : Ty → Ty → Prop where
  | unit : MSub .unit .unit
  | nat : MSub .nat .nat
  | param : MSub .param .param
  | phantom (S T : Ty) : MSub (.phantom S) (.phantom T)
  | ref {a b : Lft} {S T : Ty} : a.outlives b = true → MSub S T → MSub (.ref a S) (.ref b T)
  | refMut {a b : Lft} {S T : Ty} :
      a.outlives b = true → MSub S T → MSub T S → MSub (.refMut a S) (.refMut b T)
  | cell {S T : Ty} : MSub S T → MSub T S → MSub (.cell S) (.cell T)
  | fn {S S' U U' : Ty} : MSub S' S → MSub U U' → MSub (.fn S U) (.fn S' U')
  | fnFn {A B : Ty} : erase A = erase B → MSub (.fn (.fn A .unit) .unit) (.fn (.fn B .unit) .unit)
  | prod {S S' U U' : Ty} : MSub S S' → MSub U U' → MSub (.prod S U) (.prod S' U')
  | prodCell {S S' U U' : Ty} : MSub S S' → MSub U U' → MSub (.prod (.cell S) U) (.prod (.cell S') U')

theorem MSub.erase_eq {S T : Ty} (h : MSub S T) : erase S = erase T := by
  induction h with
  | unit | nat | param | phantom => rfl
  | ref _ _ ih => exact congrArg ETy.ref ih
  | refMut _ _ _ ih _ => exact congrArg ETy.refMut ih
  | cell _ _ ih _ => exact congrArg ETy.cell ih
  | fn _ _ ihS ihU => simp [erase, ihS, ihU]
  | fnFn h => simp [erase, h]
  | prod _ _ ihS ihU => simp [erase, ihS, ihU]
  | prodCell _ _ ihS ihU => simp [erase, ihS, ihU]

theorem erase_eq_unit {T : Ty} (h : erase T = .unit) : T = .unit := by
  cases T <;> simp [erase] at h; rfl

theorem erase_eq_fn {T : Ty} {E₁ E₂ : ETy} (h : erase T = .fn E₁ E₂) :
    ∃ A B, T = .fn A B ∧ erase A = E₁ ∧ erase B = E₂ := by
  cases T <;> simp [erase] at h; exact ⟨_, _, rfl, h⟩

theorem MSub.of_erase_toStatic : ∀ {S T : Ty}, erase S = erase T →
    MSub (toStatic S) (toStatic T) ∧ MSub (toStatic T) (toStatic S) := by
  intro S
  induction S with
  | unit => intro T h; cases T <;> simp [erase] at h; exact ⟨.unit, .unit⟩
  | nat => intro T h; cases T <;> simp [erase] at h; exact ⟨.nat, .nat⟩
  | param => intro T h; cases T <;> simp [erase] at h; exact ⟨.param, .param⟩
  | phantom S _ => intro T h; cases T <;> simp [erase] at h; exact ⟨.phantom _ _, .phantom _ _⟩
  | ref a S ih =>
    intro T h; cases T <;> simp [erase] at h
    obtain ⟨h1, h2⟩ := ih h; exact ⟨.ref rfl h1, .ref rfl h2⟩
  | refMut a S ih =>
    intro T h; cases T <;> simp [erase] at h
    obtain ⟨h1, h2⟩ := ih h; exact ⟨.refMut rfl h1 h2, .refMut rfl h2 h1⟩
  | cell S ih =>
    intro T h; cases T <;> simp [erase] at h
    obtain ⟨h1, h2⟩ := ih h; exact ⟨.cell h1 h2, .cell h2 h1⟩
  | fn S U ihS ihU =>
    intro T h; cases T <;> simp [erase] at h
    obtain ⟨s1, s2⟩ := ihS h.1; obtain ⟨u1, u2⟩ := ihU h.2
    exact ⟨.fn s2 u1, .fn s1 u2⟩
  | prod S U ihS ihU =>
    intro T h; cases T <;> simp [erase] at h
    obtain ⟨s1, s2⟩ := ihS h.1; obtain ⟨u1, u2⟩ := ihU h.2
    exact ⟨.prod s1 u1, .prod s2 u2⟩

theorem MSub.refl (T : Ty) : MSub T T := by
  induction T with
  | unit => exact .unit | nat => exact .nat | param => exact .param
  | phantom S => exact .phantom S S
  | ref a S ih => exact .ref (Lft.outlives_refl a) ih
  | refMut a S ih => exact .refMut (Lft.outlives_refl a) ih ih
  | cell S ih => exact .cell ih ih
  | fn S U ihS ihU => exact .fn ihS ihU
  | prod S U ihS ihU => exact .prod ihS ihU

theorem MSub.inv_fnFn_left {A Y : Ty} (h : MSub (.fn (.fn A .unit) .unit) Y) :
    ∃ B, Y = .fn (.fn B .unit) .unit ∧ erase A = erase B := by
  have he := h.erase_eq; simp [erase] at he
  obtain ⟨X, U, rfl, hX, hU⟩ := erase_eq_fn he.symm
  obtain rfl := erase_eq_unit hU
  obtain ⟨B, V, rfl, hB, hV⟩ := erase_eq_fn hX
  obtain rfl := erase_eq_unit hV
  exact ⟨B, rfl, hB.symm⟩

theorem MSub.inv_fnFn_right {X B : Ty} (h : MSub X (.fn (.fn B .unit) .unit)) :
    ∃ A, X = .fn (.fn A .unit) .unit ∧ erase A = erase B := by
  have he := h.erase_eq; simp [erase] at he
  obtain ⟨Y, U, rfl, hY, hU⟩ := erase_eq_fn he
  obtain rfl := erase_eq_unit hU
  obtain ⟨A, V, rfl, hA, hV⟩ := erase_eq_fn hY
  obtain rfl := erase_eq_unit hV
  exact ⟨A, rfl, hA⟩

theorem MSub.trans : ∀ (T : Ty) {S U : Ty}, MSub S T → MSub T U → MSub S U
  | .unit, _, _, .unit, h₂ => h₂
  | .nat, _, _, .nat, h₂ => h₂
  | .param, _, _, .param, h₂ => h₂
  | .phantom _, _, _, .phantom S _, .phantom _ W => .phantom S W
  | .ref _ T, _, _, .ref ha h₁, .ref hb h₂ => .ref (Lft.outlives_trans ha hb) (MSub.trans T h₁ h₂)
  | .refMut _ T, _, _, .refMut ha h₁ h₁', .refMut hb h₂ h₂' =>
    .refMut (Lft.outlives_trans ha hb) (MSub.trans T h₁ h₂) (MSub.trans T h₂' h₁')
  | .cell T, _, _, .cell h₁ h₁', .cell h₂ h₂' =>
    .cell (MSub.trans T h₁ h₂) (MSub.trans T h₂' h₁')
  | .fn T V, _, _, .fn h₁ h₂, .fn h₃ h₄ =>
    .fn (MSub.trans T h₃ h₁) (MSub.trans V h₂ h₄)
  | .fn (.fn _ .unit) .unit, _, _, h₁, .fnFn hB => by
    obtain ⟨A, rfl, hA⟩ := MSub.inv_fnFn_right h₁; exact .fnFn (hA.trans hB)
  | .fn (.fn _ .unit) .unit, _, _, .fnFn hA, h₂ => by
    obtain ⟨C, rfl, hC⟩ := MSub.inv_fnFn_left h₂; exact .fnFn (hA.trans hC)
  | .prod T V, _, _, .prod h₁ h₂, .prod h₃ h₄ =>
    .prod (MSub.trans T h₁ h₃) (MSub.trans V h₂ h₄)
  | .prod (.cell T) V, _, _, .prod (.cell h₁ _) h₂, .prodCell h₃ h₄ =>
    .prodCell (MSub.trans T h₁ h₃) (MSub.trans V h₂ h₄)
  | .prod (.cell T) V, _, _, .prodCell h₁ h₂, .prod (.cell h₃ _) h₄ =>
    .prodCell (MSub.trans T h₁ h₃) (MSub.trans V h₂ h₄)
  | .prod (.cell T) V, _, _, .prodCell h₁ h₂, .prodCell h₃ h₄ =>
    .prodCell (MSub.trans T h₁ h₃) (MSub.trans V h₂ h₄)
termination_by T => sizeOf T

theorem MSub.of_safeTable {S T : Ty} (h : SubGen safeTable NoAx S T) : MSub S T := by
  induction h with
  | refl T => exact MSub.refl T
  | trans _ _ ih₁ ih₂ => exact MSub.trans _ ih₁ ih₂
  | base h => exact h.elim
  | ref hl _ _ ihf _ => exact .ref (hl.1 rfl) (ihf rfl)
  | refMut hl _ _ ihf ihb => exact .refMut (hl.1 rfl) (ihf rfl) (ihb rfl)
  | cell _ _ ihf ihb => exact .cell (ihf rfl) (ihb rfl)
  | fn _ _ _ _ _ ihb ihc _ => exact .fn (ihb rfl) (ihc rfl)
  | prod _ _ _ _ iha _ ihc _ => exact .prod (iha rfl) (ihc rfl)
  | phantom _ _ _ _ => exact .phantom _ _

theorem MSub.of_prodCellAx {S T : Ty}
    (h : SubGen rustTable (BodyAx (.prod (.cell .param) .unit) .co) S T) : MSub S T := by
  induction h with
  | refl T => exact MSub.refl T
  | trans _ _ ih₁ ih₂ => exact MSub.trans _ ih₁ ih₂
  | base hax =>
    obtain ⟨A, B, _, _, rfl, rfl, hrel⟩ := hax
    have hs : SubGen safeTable NoAx A B :=
      SubGen.lift rustTable_le_safeTable (fun _ _ h => h.elim) (hrel.1 rfl)
    exact .prodCell (MSub.of_safeTable hs) .unit
  | ref hl _ _ ihf _ => exact .ref (hl.1 rfl) (ihf rfl)
  | refMut hl _ _ ihf ihb => exact .refMut (hl.1 rfl) (ihf rfl) (ihb rfl)
  | cell _ _ ihf ihb => exact .cell (ihf rfl) (ihb rfl)
  | fn _ _ _ _ _ ihb ihc _ => exact .fn (ihb rfl) (ihc rfl)
  | prod _ _ _ _ iha _ ihc _ => exact .prod (iha rfl) (ihc rfl)
  | phantom _ _ _ _ => exact .phantom _ _

theorem MSub.of_fnFnAx {S T : Ty}
    (h : SubGen rustTable (BodyAx (.fn (.fn .param .unit) .unit) .contra) S T) : MSub S T := by
  induction h with
  | refl T => exact MSub.refl T
  | trans _ _ ih₁ ih₂ => exact MSub.trans _ ih₁ ih₂
  | base hax =>
    obtain ⟨A, B, _, _, rfl, rfl, hrel⟩ := hax
    have hs : SubGen safeTable NoAx B A :=
      SubGen.lift rustTable_le_safeTable (fun _ _ h => h.elim) (hrel.2 rfl)
    exact .fnFn (MSub.of_safeTable hs).erase_eq.symm
  | ref hl _ _ ihf _ => exact .ref (hl.1 rfl) (ihf rfl)
  | refMut hl _ _ ihf ihb => exact .refMut (hl.1 rfl) (ihf rfl) (ihb rfl)
  | cell _ _ ihf ihb => exact .cell (ihf rfl) (ihb rfl)
  | fn _ _ _ _ _ ihb ihc _ => exact .fn (ihb rfl) (ihc rfl)
  | prod _ _ _ _ iha _ ihc _ => exact .prod (iha rfl) (ihc rfl)
  | phantom _ _ _ _ => exact .phantom _ _

/-! ## 2. Semantic Heap & Value Invariants -/

def semLive (t : Nat) : Ty → Bool
  | .unit | .nat | .param | .phantom _ | .fn _ _ => true
  | .cell A => semLive t A
  | .prod A B => semLive t A && semLive t B
  | .ref l A | .refMut l A => l.live t && semLive t A

theorem semLive_of_liveIn {t : Nat} {T : Ty} (h : T.liveIn (Lft.live t) = true) :
    semLive t T = true := by
  induction T <;> simp_all [Ty.liveIn, semLive]

theorem semLive_of_allStatic (t : Nat) {T : Ty} (h : T.allStatic = true) :
    semLive t T = true := by
  induction T <;> simp_all [Ty.allStatic, Ty.liveIn, semLive, Lft.live]

theorem MSub.semLive_anti {t : Nat} {S T : Ty} (h : MSub S T) (ht : semLive t T = true) :
    semLive t S = true := by
  induction h with
  | unit | nat | param | phantom | fn | fnFn => rfl
  | cell _ _ ih _ => exact ih ht
  | prod _ _ ihS ihU =>
    simp only [semLive, Bool.and_eq_true] at ht ⊢; exact ⟨ihS ht.1, ihU ht.2⟩
  | prodCell _ _ ihS ihU =>
    simp only [semLive, Bool.and_eq_true] at ht ⊢; exact ⟨ihS ht.1, ihU ht.2⟩
  | ref ha _ ih =>
    simp only [semLive, Bool.and_eq_true] at ht ⊢
    exact ⟨(Lft.outlives_iff_live_imp _ _).1 ha t ht.1, ih ht.2⟩
  | refMut ha _ _ ih _ =>
    simp only [semLive, Bool.and_eq_true] at ht ⊢
    exact ⟨(Lft.outlives_iff_live_imp _ _).1 ha t ht.1, ih ht.2⟩

def BodyChecked (f : Nat) (T₀ U₀ C : Ty) (body : List Stmt) : Prop :=
  ∃ sub t₀, (∀ X Y, sub X Y = true → MSub X Y) ∧
    match chk f sub ⟨t₀, true⟩ (Ctx.frame T₀ C) body with
    | some none => True
    | some (some Γb) => Γb 2 = some U₀
    | none => False

inductive ValOk (htys : List (Lft × Ty)) : Val → Ty → Prop where
  | unit : ValOk htys .unit .unit
  | nat (n : Nat) : ValOk htys (.nat n) .nat
  | phantom (T : Ty) : ValOk htys .unit (.phantom T)
  | cell {v : Val} {T : Ty} : ValOk htys v T → ValOk htys v (.cell T)
  | prod {a b : Val} {A B : Ty} : ValOk htys a A → ValOk htys b B → ValOk htys (.pair a b) (.prod A B)
  | ref {p : Nat} {r l : Lft} {H T : Ty} :
      htys[p]? = some (r, H) → r.outlives l = true → MSub H T → ValOk htys (.ptr p) (.ref l T)
  | refMut {p : Nat} {r l : Lft} {H T : Ty} :
      htys[p]? = some (r, H) → r.outlives l = true → MSub H T → MSub T H → ValOk htys (.ptr p) (.refMut l T)
  | clo {body : List Stmt} {cap : Val} {T₀ U₀ C T U : Ty} {f : Nat} :
      MSub (.fn T₀ U₀) (.fn T U) → C.allStatic = true →
      ValOk htys cap C → BodyChecked f T₀ U₀ C body → ValOk htys (.clo body cap) (.fn T U)
  | cloStatic {body : List Stmt} {cap : Val} {T₀ U₀ C T U : Ty} {f : Nat} :
      MSub (.fn (toStatic T₀) (toStatic U₀)) (.fn T U) → C.allStatic = true →
      ValOk htys cap C → BodyChecked f T₀ U₀ C body → ValOk htys (.clo body cap) (.fn T U)

theorem ValOk.weaken_sub : ∀ (S : Ty) {htys : List (Lft × Ty)} {v : Val} {T : Ty},
    ValOk htys v S → MSub S T → ValOk htys v T
  | .unit, _, _, _, .unit, .unit => .unit
  | .nat, _, _, _, .nat n, .nat => .nat n
  | .param, _, _, _, hv, _ => nomatch hv
  | .phantom _, _, _, _, .phantom _, .phantom _ T => .phantom T
  | .cell S, _, _, _, .cell hv, .cell hST _ => .cell (ValOk.weaken_sub S hv hST)
  | .prod A B, _, _, _, .prod ha hb, .prod hA hB =>
    .prod (ValOk.weaken_sub A ha hA) (ValOk.weaken_sub B hb hB)
  | .prod (.cell S) B, _, _, _, .prod (.cell hs) hb, .prodCell hS hB =>
    .prod (.cell (ValOk.weaken_sub S hs hS)) (ValOk.weaken_sub B hb hB)
  | .ref _ _, _, _, _, .ref hp hr hHS, .ref hab hST =>
    .ref hp (Lft.outlives_trans hr hab) (MSub.trans _ hHS hST)
  | .refMut _ _, _, _, _, .refMut hp hr hHS hSH, .refMut hab hST hTS =>
    .refMut hp (Lft.outlives_trans hr hab) (MSub.trans _ hHS hST) (MSub.trans _ hTS hSH)
  | .fn _ _, _, _, _, .clo hfn hC hcap hb, hsub => by
    obtain ⟨T', U', rfl, _⟩ := erase_eq_fn hsub.erase_eq.symm
    exact .clo (MSub.trans _ hfn hsub) hC hcap hb
  | .fn _ _, _, _, _, .cloStatic hfn hC hcap hb, hsub => by
    obtain ⟨T', U', rfl, _⟩ := erase_eq_fn hsub.erase_eq.symm
    exact .cloStatic (MSub.trans _ hfn hsub) hC hcap hb
termination_by S => sizeOf S

theorem ValOk.as_cloStatic {htys : List (Lft × Ty)} {v : Val} {X Y T' U' : Ty}
    (hv : ValOk htys v (.fn X Y))
    (hX : erase X = erase T') (hY : erase Y = erase U') :
    ValOk htys v (.fn (toStatic T') (toStatic U')) := by
  cases hv with
  | clo hfn hC hcap hb =>
    have he := hfn.erase_eq; simp [erase] at he
    have hsT := (MSub.of_erase_toStatic (he.1.trans hX)).2
    have hsU := (MSub.of_erase_toStatic (he.2.trans hY)).1
    exact .cloStatic (.fn hsT hsU) hC hcap hb
  | cloStatic hfn hC hcap hb =>
    have he := hfn.erase_eq; simp [erase, erase_toStatic] at he
    have hsT := (MSub.of_erase_toStatic (he.1.trans hX)).2
    have hsU := (MSub.of_erase_toStatic (he.2.trans hY)).1
    exact .cloStatic (.fn hsT hsU) hC hcap hb

def HeapExt (htys htys' : List (Lft × Ty)) : Prop :=
  ∀ (p : Nat) (x : Lft × Ty), htys[p]? = some x → htys'[p]? = some x

theorem HeapExt.refl (htys : List (Lft × Ty)) : HeapExt htys htys := fun _ _ h => h
theorem HeapExt.trans {htys₁ htys₂ htys₃ : List (Lft × Ty)}
    (h₁ : HeapExt htys₁ htys₂) (h₂ : HeapExt htys₂ htys₃) : HeapExt htys₁ htys₃ :=
  fun p x h => h₂ p x (h₁ p x h)
theorem HeapExt.snoc (htys : List (Lft × Ty)) (e : Lft × Ty) : HeapExt htys (htys ++ [e]) :=
  fun p _ h => get_append_left htys [e] p h

theorem ValOk.mono {htys htys' : List (Lft × Ty)} (hext : HeapExt htys htys') {v : Val} {T : Ty}
    (hv : ValOk htys v T) : ValOk htys' v T := by
  induction hv with
  | unit => exact .unit | nat n => exact .nat n | phantom T => exact .phantom T
  | cell _ ih => exact .cell ih
  | prod _ _ iha ihb => exact .prod iha ihb
  | ref hp hr hHT => exact .ref (hext _ _ hp) hr hHT
  | refMut hp hr hHT hTH => exact .refMut (hext _ _ hp) hr hHT hTH
  | clo hfn hC _ hb ih => exact .clo hfn hC ih hb
  | cloStatic hfn hC _ hb ih => exact .cloStatic hfn hC ih hb

def HeapOk (htys : List (Lft × Ty)) (heap : List (Lft × Val)) : Prop :=
  heap.length = htys.length ∧
  ∀ (p : Nat) (r : Lft) (H : Ty), htys[p]? = some (r, H) → ∃ v, heap[p]? = some (r, v) ∧ ValOk htys v H

theorem HeapOk.alloc {htys : List (Lft × Ty)} {heap : List (Lft × Val)}
    (hh : HeapOk htys heap) (l : Lft) (T : Ty) {v : Val} (hv : ValOk htys v T) :
    HeapOk (htys ++ [(l, T)]) (heap ++ [(l, v)]) := by
  refine ⟨by simp [hh.1], ?_⟩
  intro p r H hp
  have hext := HeapExt.snoc htys (l, T)
  by_cases hlt : p < htys.length
  · obtain ⟨⟨r₀, H₀⟩, hp₀⟩ := get_some_of_lt htys p hlt
    have hp' := get_append_left htys [(l, T)] p hp₀
    rw [hp] at hp'; cases hp'
    obtain ⟨w, hw, hvw⟩ := hh.2 p r H hp₀
    exact ⟨w, get_append_left heap [(l, v)] p hw, hvw.mono hext⟩
  · have hlen : (htys ++ [(l, T)]).length = htys.length + 1 := by simp
    have hplen := lt_len_of_get_some (htys ++ [(l, T)]) p hp
    have hpeq : p = htys.length := by omega
    subst hpeq
    have hp' := get_append_len htys (l, T)
    rw [hp] at hp'; cases hp'
    have hw : (heap ++ [(l, v)])[htys.length]? = some (l, v) := by
      rw [← hh.1]; exact get_append_len heap (l, v)
    exact ⟨v, hw, hv.mono hext⟩

theorem HeapOk.update {htys : List (Lft × Ty)} {heap : List (Lft × Val)}
    (hh : HeapOk htys heap) {p : Nat} {r : Lft} {H : Ty} {v : Val}
    (hp : htys[p]? = some (r, H)) (hv : ValOk htys v H) :
    HeapOk htys (heap.set p (r, v)) := by
  refine ⟨by rw [len_set, hh.1], ?_⟩
  intro q r' H' hq
  by_cases hpq : p = q
  · subst hpq
    rw [hp] at hq; cases hq
    have hlt : p < heap.length := by rw [hh.1]; exact lt_len_of_get_some htys p hp
    exact ⟨v, get_set_eq heap p (r, v) hlt, hv⟩
  · rw [get_set_ne heap p q (r, v) hpq]
    exact hh.2 q r' H' hq

def ValInL (L : Nat → Prop) : Val → Prop
  | .unit | .nat _ | .clo _ _ => True
  | .pair a b => ValInL L a ∧ ValInL L b
  | .ptr p => L p

theorem ValInL.mono {L₁ L₂ : Nat → Prop} (h : ∀ p, L₁ p → L₂ p) {v : Val} (hv : ValInL L₁ v) :
    ValInL L₂ v := by
  induction v with
  | unit | nat _ | clo _ _ => trivial
  | pair a b iha ihb => exact ⟨iha hv.1, ihb hv.2⟩
  | ptr p => exact h p hv

def Lsem (t : Nat) (htys : List (Lft × Ty)) (p : Nat) : Prop :=
  ∃ r H, htys[p]? = some (r, H) ∧ r.live t = true ∧ semLive t H = true

theorem valInL_lsem {t : Nat} {htys : List (Lft × Ty)} {v : Val} {T : Ty}
    (hv : ValOk htys v T) (ht : semLive t T = true) : ValInL (Lsem t htys) v := by
  induction hv with
  | unit | nat _ | phantom _ | clo _ _ _ _ | cloStatic _ _ _ _ => trivial
  | cell _ ih => exact ih ht
  | prod _ _ iha ihb =>
    simp only [semLive, Bool.and_eq_true] at ht; exact ⟨iha ht.1, ihb ht.2⟩
  | ref hp hr hHT =>
    simp only [semLive, Bool.and_eq_true] at ht
    exact ⟨_, _, hp, (Lft.outlives_iff_live_imp _ _).1 hr t ht.1, hHT.semLive_anti ht.2⟩
  | refMut hp hr hHT _ =>
    simp only [semLive, Bool.and_eq_true] at ht
    exact ⟨_, _, hp, (Lft.outlives_iff_live_imp _ _).1 hr t ht.1, hHT.semLive_anti ht.2⟩

def LiveSetOk (t : Nat) (htys : List (Lft × Ty)) (heap : List (Lft × Val)) (L : Nat → Prop) : Prop :=
  (∀ p, Lsem t htys p → L p) ∧
  (∀ p, L p → ∃ r v, heap[p]? = some (r, v) ∧ r.live t = true ∧ ValInL L v)

theorem liveSetOk_lsem (t : Nat) {htys : List (Lft × Ty)} {heap : List (Lft × Val)}
    (hh : HeapOk htys heap) : LiveSetOk t htys heap (Lsem t htys) := by
  refine ⟨fun _ h => h, ?_⟩
  rintro p ⟨r, H, hp, hr, hsem⟩
  obtain ⟨v, hvp, hvok⟩ := hh.2 p r H hp
  exact ⟨r, v, hvp, hr, valInL_lsem hvok hsem⟩

theorem valInL_of_semLive {t : Nat} {htys : List (Lft × Ty)} {heap : List (Lft × Val)} {L : Nat → Prop}
    (hL : LiveSetOk t htys heap L) {v : Val} {T : Ty}
    (hv : ValOk htys v T) (ht : semLive t T = true) : ValInL L v :=
  (valInL_lsem hv ht).mono hL.1

theorem LiveSetOk.alloc_static {t : Nat} {htys : List (Lft × Ty)} {heap : List (Lft × Val)} {L : Nat → Prop}
    (hh : HeapOk htys heap) (hL : LiveSetOk t htys heap L) (T : Ty) {v : Val} (hv : ValInL L v) :
    LiveSetOk t (htys ++ [(Lft.static, T)]) (heap ++ [(Lft.static, v)]) (fun q => L q ∨ q = htys.length) := by
  refine ⟨?_, ?_⟩
  · rintro q ⟨r, H, hq, hr, hsem⟩
    by_cases hlt : q < htys.length
    · obtain ⟨⟨r₀, H₀⟩, hq₀⟩ := get_some_of_lt htys q hlt
      have hq' := get_append_left htys [(.static, T)] q hq₀
      rw [hq] at hq'; cases hq'
      exact Or.inl (hL.1 q ⟨r, H, hq₀, hr, hsem⟩)
    · have hplen := lt_len_of_get_some (htys ++ [(Lft.static, T)]) q hq
      have hlen : (htys ++ [(Lft.static, T)]).length = htys.length + 1 := by simp
      exact Or.inr (by omega)
  · rintro q (hqL | rfl)
    · obtain ⟨r, w, hwp, hr, hwin⟩ := hL.2 q hqL
      exact ⟨r, w, get_append_left heap [(.static, v)] q hwp, hr, hwin.mono (fun _ => Or.inl)⟩
    · have hw : (heap ++ [(Lft.static, v)])[htys.length]? = some (.static, v) := by
        rw [← hh.1]; exact get_append_len heap (.static, v)
      exact ⟨.static, v, hw, rfl, hv.mono (fun _ => Or.inl)⟩

theorem LiveSetOk.update {t : Nat} {htys : List (Lft × Ty)} {heap : List (Lft × Val)} {L : Nat → Prop}
    (_hh : HeapOk htys heap) (hL : LiveSetOk t htys heap L) {p : Nat} {r : Lft} {v : Val}
    (hpL : L p) (hr : r.live t = true) (hv : ValInL L v) :
    LiveSetOk t htys (heap.set p (r, v)) L := by
  refine ⟨hL.1, ?_⟩
  intro q hqL
  by_cases hpq : p = q
  · subst hpq
    obtain ⟨r₀, _, hwp, _, _⟩ := hL.2 p hpL
    have hlt := lt_len_of_get_some heap p hwp
    exact ⟨r, v, get_set_eq heap p (r, v) hlt, hr, hv⟩
  · obtain ⟨r', w, hwp, hr', hwin⟩ := hL.2 q hqL
    exact ⟨r', w, (get_set_ne heap p q (r, v) hpq).trans hwp, hr', hwin⟩

/-! ## 3. Three-Part Execution Preservation (`exec_static_ok`, `exec_body_ok`, `exec_top_ok`) -/

def EnvStaticOk (htys : List (Lft × Ty)) (env : Env) (Γ : Ctx) : Prop :=
  ∀ (x : Nat) (T : Ty), Γ x = some T → ∃ v, env x = some v ∧ ValOk htys v (toStatic T)

theorem EnvStaticOk.mono {htys htys' : List (Lft × Ty)} (hext : HeapExt htys htys')
    {env : Env} {Γ : Ctx} (he : EnvStaticOk htys env Γ) : EnvStaticOk htys' env Γ :=
  fun x T hx => let ⟨v, hv, hok⟩ := he x T hx; ⟨v, hv, hok.mono hext⟩

theorem EnvStaticOk.set {htys : List (Lft × Ty)} {env : Env} {Γ : Ctx}
    (he : EnvStaticOk htys env Γ) (x : Nat) (v : Val) (T : Ty) (hv : ValOk htys v (toStatic T)) :
    EnvStaticOk htys (env.set x v) (Γ.set x T) := by
  intro k T' hk
  by_cases hkx : k = x
  · subst hkx; simp [Ctx.set] at hk; subst hk; exact ⟨v, by simp [Env.set], hv⟩
  · simp [Ctx.set, hkx] at hk; simp [Env.set, hkx]; exact he k T' hk

theorem mode_get_inBody {t₀ : Nat} {Γ : Ctx} {y : Nat} {T : Ty}
    (h : Mode.get ⟨t₀, true⟩ Γ y = some T) : Γ y = some T := by
  simp [Mode.get] at h
  cases hgy : Γ y with
  | none => simp [hgy] at h
  | some T' => simp [hgy] at h; exact congrArg some h.2

theorem mode_get_top {t : Nat} {Γ : Ctx} {y : Nat} {T : Ty}
    (h : Mode.get ⟨t, false⟩ Γ y = some T) : Γ y = some T ∧ T.liveIn (Lft.live t) = true := by
  simp [Mode.get] at h
  cases hgy : Γ y with
  | none => simp [hgy] at h
  | some T' =>
    simp [hgy] at h
    obtain ⟨hlv, rfl⟩ := h
    exact ⟨rfl, hlv⟩

def StaticChanged (htys : List (Lft × Ty)) (h₁ h₂ : List (Lft × Val)) : Prop :=
  ∀ (p : Nat), p < htys.length → h₂[p]? ≠ h₁[p]? →
    ∃ H, htys[p]? = some (.static, H) ∧ ∀ t, semLive t H = true

theorem StaticChanged.refl (htys : List (Lft × Ty)) (h : List (Lft × Val)) :
    StaticChanged htys h h := fun _ _ hne => absurd rfl hne

theorem StaticChanged.trans {htys htys' : List (Lft × Ty)} {h₁ h₂ h₃ : List (Lft × Val)}
    (hext : HeapExt htys htys') (c₁ : StaticChanged htys h₁ h₂) (c₂ : StaticChanged htys' h₂ h₃) :
    StaticChanged htys h₁ h₃ := by
  intro p hlt hne
  by_cases h12 : h₂[p]? = h₁[p]?
  · have h23 : h₃[p]? ≠ h₂[p]? := by rw [h12]; exact hne
    obtain ⟨x₀, hp₀⟩ := get_some_of_lt htys p hlt
    have hlt' : p < htys'.length := lt_len_of_get_some htys' p (hext p x₀ hp₀)
    obtain ⟨H, hp', hsem⟩ := c₂ p hlt' h23
    rw [hext p x₀ hp₀] at hp'; cases hp'
    exact ⟨H, hp₀, hsem⟩
  · exact c₁ p hlt h12

theorem LiveSetOk.after_static {t : Nat} {htys htys' : List (Lft × Ty)}
    {h₁ h₂ : List (Lft × Val)} {L : Nat → Prop}
    (hext : HeapExt htys htys') (hh₁ : HeapOk htys h₁) (hh₂ : HeapOk htys' h₂)
    (hL : LiveSetOk t htys h₁ L) (hchg : StaticChanged htys h₁ h₂) :
    LiveSetOk t htys' h₂ (fun p => L p ∨ Lsem t htys' p) := by
  refine ⟨fun p hp => Or.inr hp, ?_⟩
  rintro p (hpL | ⟨r, H, hp', hr, hsem⟩)
  · by_cases hlt : p < htys.length
    · by_cases heq : h₂[p]? = h₁[p]?
      · obtain ⟨r, v, hvp, hr, hvin⟩ := hL.2 p hpL
        exact ⟨r, v, heq.trans hvp, hr, hvin.mono (fun _ => Or.inl)⟩
      · obtain ⟨H, hp₀, hsem⟩ := hchg p hlt heq
        have hp' := hext p (.static, H) hp₀
        obtain ⟨v, hvp, hvok⟩ := hh₂.2 p .static H hp'
        exact ⟨.static, v, hvp, rfl, (valInL_lsem hvok (hsem t)).mono (fun _ => Or.inr)⟩
    · obtain ⟨r, v, hvp, _, _⟩ := hL.2 p hpL
      have hlt_h := lt_len_of_get_some h₁ p hvp
      rw [hh₁.1] at hlt_h
      exact absurd hlt_h hlt
  · obtain ⟨v, hvp, hvok⟩ := hh₂.2 p r H hp'
    exact ⟨r, v, hvp, hr, (valInL_lsem hvok hsem).mono (fun _ => Or.inr)⟩

theorem envStatic_frame {htys : List (Lft × Ty)} {va vc : Val} {T₀ C : Ty}
    (ha : ValOk htys va (toStatic T₀)) (hc : ValOk htys vc C) (hC : C.allStatic = true) :
    EnvStaticOk htys (Env.frame va vc) (Ctx.frame T₀ C) := by
  have hc' : ValOk htys vc (toStatic C) := by rw [toStatic_id_of_allStatic hC]; exact hc
  intro k T hk
  by_cases hk1 : k = 1
  · subst hk1; simp [Ctx.frame, Ctx.set] at hk; subst hk; exact ⟨vc, by simp [Env.frame, Env.set], hc'⟩
  · by_cases hk0 : k = 0
    · subst hk0; simp [Ctx.frame, Ctx.set] at hk; subst hk; exact ⟨va, by simp [Env.frame, Env.set], ha⟩
    · simp [Ctx.frame, Ctx.set, hk1, hk0, Ctx.empty] at hk

theorem exec_static_ok : ∀ (fuel : Nat) {cfuel : Nat} {sub : Ty → Ty → Bool}
    (hsub : ∀ X Y, sub X Y = true → MSub X Y)
    {t₀ : Nat} {Γ : Ctx} {P : List Stmt} {res : Option Ctx}
    (hchk : chk cfuel sub ⟨t₀, true⟩ Γ P = some res)
    {st : St} {env : Env} {htys : List (Lft × Ty)}
    (hh : HeapOk htys st.heap) (he : EnvStaticOk htys env Γ),
    (exec fuel st env P).isStuck = false ∧
    (∀ st' env', exec fuel st env P = .done st' env' →
      st'.time = st.time ∧
      ∃ htys' Γ', res = some Γ' ∧ HeapExt htys htys' ∧ HeapOk htys' st'.heap ∧
        StaticChanged htys st.heap st'.heap ∧ EnvStaticOk htys' env' Γ') := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _
    exact ⟨rfl, fun _ _ h => nomatch h⟩
  | succ f ih =>
    intro cfuel sub hsub t₀ Γ P res hchk st env htys hh he
    cases cfuel with
    | zero => simp [chk] at hchk
    | succ cf =>
      cases P with
      | nil =>
        simp [chk] at hchk; subst hchk
        refine ⟨rfl, fun st' env' hd => ?_⟩
        simp [exec] at hd; obtain ⟨rfl, rfl⟩ := hd
        exact ⟨rfl, htys, Γ, rfl, HeapExt.refl htys, hh, StaticChanged.refl htys st.heap, he⟩
      | cons s rest =>
        cases s with
        | nat x n =>
          simp [chk] at hchk
          exact ih hsub hchk hh (he.set x (.nat n) .nat (.nat n))
        | unit x =>
          simp [chk] at hchk
          exact ih hsub hchk hh (he.set x .unit .unit .unit)
        | copy x y T =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some S =>
            simp only [hgy, Bool.and_eq_true] at hchk
            split at hchk <;> try simp at hchk
            rename_i hcond
            obtain ⟨_, hST⟩ := hcond
            obtain ⟨v, hvy, hvok⟩ := he y S (mode_get_inBody hgy)
            have hvT := hvok.weaken_sub _ (MSub.of_erase_toStatic (hsub S T hST).erase_eq).1
            simp only [exec, hvy]
            exact ih hsub hchk hh (he.set x v T hvT)
        | alloc x l y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some T =>
            simp only [hgy] at hchk
            split at hchk <;> try simp at hchk
            rename_i hcond
            simp [Mode.lv] at hcond; subst hcond
            obtain ⟨v, hvy, hvok⟩ := he y T (mode_get_inBody hgy)
            simp only [exec, hvy, Lft.live, ite_true]
            let st1 : St := { st with heap := st.heap ++ [(.static, v)] }
            have hh' : HeapOk (htys ++ [(.static, toStatic T)]) st1.heap := hh.alloc .static (toStatic T) hvok
            have hext := HeapExt.snoc htys (.static, toStatic T)
            have hp : (htys ++ [(.static, toStatic T)])[st.heap.length]? = some (.static, toStatic T) := by
              rw [hh.1]; exact get_append_len htys (.static, toStatic T)
            have hptr : ValOk (htys ++ [(.static, toStatic T)]) (.ptr st.heap.length) (toStatic (.refMut .static T)) :=
              .refMut hp rfl (MSub.refl _) (MSub.refl _)
            have ⟨hns, hdone⟩ := ih hsub hchk (st := st1) hh' ((he.mono hext).set x (.ptr st.heap.length) (.refMut .static T) hptr)
            refine ⟨hns, fun st' env' hd => ?_⟩
            obtain ⟨ht, htys', Γ', rfl, hext', hh'', hchg, he'⟩ := hdone st' env' hd
            have hchg0 : StaticChanged htys st.heap st1.heap := by
              intro p hlt hne
              have hlt_h : p < st.heap.length := by rw [hh.1]; exact hlt
              obtain ⟨val, hvp⟩ := get_some_of_lt st.heap p hlt_h
              exact absurd ((get_append_left st.heap [(.static, v)] p hvp).trans hvp.symm) hne
            exact ⟨ht, htys', Γ', rfl, hext.trans hext', hh'', StaticChanged.trans hext hchg0 hchg, he'⟩
        | share x y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            cases Y with
            | refMut l T =>
              simp only [hgy] at hchk
              obtain ⟨v, hvy, hvok⟩ := he y (.refMut l T) (mode_get_inBody hgy)
              cases hvok with
              | refMut hp hr hHT _ =>
                simp only [exec, hvy]
                exact ih hsub hchk hh (he.set x _ (.ref l T) (.ref hp hr hHT))
            | _ => simp [hgy] at hchk
        | newCell x l y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some T =>
            simp only [hgy] at hchk
            split at hchk <;> try simp at hchk
            rename_i hcond
            simp [Mode.lv] at hcond; subst hcond
            obtain ⟨v, hvy, hvok⟩ := he y T (mode_get_inBody hgy)
            simp only [exec, hvy, Lft.live, ite_true]
            let st1 : St := { st with heap := st.heap ++ [(.static, v)] }
            have hh' : HeapOk (htys ++ [(.static, .cell (toStatic T))]) st1.heap :=
              hh.alloc .static (.cell (toStatic T)) (.cell hvok)
            have hext := HeapExt.snoc htys (.static, .cell (toStatic T))
            have hp : (htys ++ [(.static, .cell (toStatic T))])[st.heap.length]? = some (.static, .cell (toStatic T)) := by
              rw [hh.1]; exact get_append_len htys (.static, .cell (toStatic T))
            have hptr : ValOk (htys ++ [(.static, .cell (toStatic T))]) (.ptr st.heap.length) (toStatic (.ref .static (.cell T))) :=
              .ref hp rfl (MSub.refl _)
            have ⟨hns, hdone⟩ := ih hsub hchk (st := st1) hh' ((he.mono hext).set x (.ptr st.heap.length) (.ref .static (.cell T)) hptr)
            refine ⟨hns, fun st' env' hd => ?_⟩
            obtain ⟨ht, htys', Γ', rfl, hext', hh'', hchg, he'⟩ := hdone st' env' hd
            have hchg0 : StaticChanged htys st.heap st1.heap := by
              intro p hlt hne
              have hlt_h : p < st.heap.length := by rw [hh.1]; exact hlt
              obtain ⟨val, hvp⟩ := get_some_of_lt st.heap p hlt_h
              exact absurd ((get_append_left st.heap [(.static, v)] p hvp).trans hvp.symm) hne
            exact ⟨ht, htys', Γ', rfl, hext.trans hext', hh'', StaticChanged.trans hext hchg0 hchg, he'⟩
        | read x y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            cases Y with
            | ref l T =>
              simp only [hgy] at hchk
              obtain ⟨v, hvy, hvok⟩ := he y (.ref l T) (mode_get_inBody hgy)
              cases hvok with
              | @ref p r0 _ H0 _ hp hr hHT =>
                have hrstat : r0 = .static := by cases r0 <;> simp [Lft.outlives] at hr; rfl
                subst hrstat
                obtain ⟨w, hwp, hwok⟩ := hh.2 p .static H0 hp
                simp only [exec, hvy, hwp, Lft.live, ite_true]
                exact ih hsub hchk hh (he.set x w T (hwok.weaken_sub _ hHT))
            | refMut l T =>
              simp only [hgy] at hchk
              obtain ⟨v, hvy, hvok⟩ := he y (.refMut l T) (mode_get_inBody hgy)
              cases hvok with
              | @refMut p r0 _ H0 _ hp hr hHT _ =>
                have hrstat : r0 = .static := by cases r0 <;> simp [Lft.outlives] at hr; rfl
                subst hrstat
                obtain ⟨w, hwp, hwok⟩ := hh.2 p .static H0 hp
                simp only [exec, hvy, hwp, Lft.live, ite_true]
                exact ih hsub hchk hh (he.set x w T (hwok.weaken_sub _ hHT))
            | _ => simp [hgy] at hchk
        | write y z =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            cases Y with
            | refMut l T =>
              cases hgz : Mode.get ⟨t₀, true⟩ Γ z with
              | none => simp [hgy, hgz] at hchk
              | some Z =>
                simp only [hgy, hgz] at hchk
                split at hchk <;> try simp at hchk
                rename_i hZT; simp at hZT; subst Z
                obtain ⟨vy, hvy, hyok⟩ := he y (.refMut l T) (mode_get_inBody hgy)
                obtain ⟨vz, hvz, hzok⟩ := he z T (mode_get_inBody hgz)
                cases hyok with
                | @refMut p r0 _ H0 _ hp hr hHT hTH =>
                  have hrstat : r0 = .static := by cases r0 <;> simp [Lft.outlives] at hr; rfl
                  subst hrstat
                  obtain ⟨w, hwp, _⟩ := hh.2 p .static H0 hp
                  simp only [exec, hvy, hvz, hwp, Lft.live, ite_true]
                  let st1 : St := { st with heap := st.heap.set p (.static, vz) }
                  have hh' : HeapOk htys st1.heap := hh.update hp (hzok.weaken_sub _ hTH)
                  have ⟨hns, hdone⟩ := ih hsub hchk (st := st1) hh' he
                  refine ⟨hns, fun st' env' hd => ?_⟩
                  obtain ⟨ht, htys', Γ', rfl, hext', hh'', hchg, he'⟩ := hdone st' env' hd
                  have hchg0 : StaticChanged htys st.heap st1.heap := by
                    intro q _ hne
                    by_cases hpq : p = q
                    · subst hpq
                      exact ⟨H0, hp, fun t => hHT.semLive_anti (semLive_of_allStatic t (allStatic_toStatic T))⟩
                    · exact absurd (get_set_ne st.heap p q (.static, vz) hpq) hne
                  exact ⟨ht, htys', Γ', rfl, hext', hh'', StaticChanged.trans (HeapExt.refl htys) hchg0 hchg, he'⟩
            | _ => simp [hgy] at hchk
        | cellGet x c =>
          simp only [chk] at hchk
          cases hgc : Mode.get ⟨t₀, true⟩ Γ c with
          | none => simp [hgc] at hchk
          | some Y =>
            cases Y with
            | ref l C =>
              cases C with
              | cell T =>
                simp only [hgc] at hchk
                obtain ⟨vc, hvc, hcok⟩ := he c (.ref l (.cell T)) (mode_get_inBody hgc)
                cases hcok with
                | @ref p r0 _ H0 _ hp hr hHC =>
                  have hrstat : r0 = .static := by cases r0 <;> simp [Lft.outlives] at hr; rfl
                  subst hrstat
                  obtain ⟨w, hwp, hwok⟩ := hh.2 p .static H0 hp
                  have hcell := hwok.weaken_sub _ hHC
                  cases hcell with
                  | cell hwt =>
                    simp only [exec, hvc, hwp, Lft.live, ite_true]
                    exact ih hsub hchk hh (he.set x w T hwt)
              | _ => simp [hgc] at hchk
            | _ => simp [hgc] at hchk
        | cellSet c z =>
          simp only [chk] at hchk
          cases hgc : Mode.get ⟨t₀, true⟩ Γ c with
          | none => simp [hgc] at hchk
          | some Y =>
            cases Y with
            | ref l C =>
              cases C with
              | cell T =>
                cases hgz : Mode.get ⟨t₀, true⟩ Γ z with
                | none => simp [hgc, hgz] at hchk
                | some Z =>
                  simp only [hgc, hgz] at hchk
                  split at hchk <;> try simp at hchk
                  rename_i hZT; simp at hZT; subst Z
                  obtain ⟨vc, hvc, hcok⟩ := he c (.ref l (.cell T)) (mode_get_inBody hgc)
                  obtain ⟨vz, hvz, hzok⟩ := he z T (mode_get_inBody hgz)
                  cases hcok with
                  | @ref p r0 _ H0 _ hp hr hHC =>
                    have hrstat : r0 = .static := by cases r0 <;> simp [Lft.outlives] at hr; rfl
                    subst hrstat
                    obtain ⟨w, hwp, _⟩ := hh.2 p .static H0 hp
                    cases hHC with
                    | @cell S0 _ hSH hTH =>
                      simp only [exec, hvc, hvz, hwp, Lft.live, ite_true]
                      let st1 : St := { st with heap := st.heap.set p (.static, vz) }
                      have hh' : HeapOk htys st1.heap := hh.update hp (.cell (hzok.weaken_sub _ hTH))
                      have ⟨hns, hdone⟩ := ih hsub hchk (st := st1) hh' he
                      refine ⟨hns, fun st' env' hd => ?_⟩
                      obtain ⟨ht, htys', Γ', rfl, hext', hh'', hchg, he'⟩ := hdone st' env' hd
                      have hchg0 : StaticChanged htys st.heap st1.heap := by
                        intro q _ hne
                        by_cases hpq : p = q
                        · subst hpq
                          exact ⟨.cell S0, hp, fun t => hSH.semLive_anti (semLive_of_allStatic t (allStatic_toStatic T))⟩
                        · exact absurd (get_set_ne st.heap p q (.static, vz) hpq) hne
                      exact ⟨ht, htys', Γ', rfl, hext', hh'', StaticChanged.trans (HeapExt.refl htys) hchg0 hchg, he'⟩
              | _ => simp [hgc] at hchk
            | _ => simp [hgc] at hchk
        | pair x y z =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some A =>
            cases hgz : Mode.get ⟨t₀, true⟩ Γ z with
            | none => simp [hgy, hgz] at hchk
            | some B =>
              simp only [hgy, hgz] at hchk
              obtain ⟨va, hva, haok⟩ := he y A (mode_get_inBody hgy)
              obtain ⟨vb, hvb, hbok⟩ := he z B (mode_get_inBody hgz)
              simp only [exec, hva, hvb]
              exact ih hsub hchk hh (he.set x (.pair va vb) (.prod A B) (.prod haok hbok))
        | fst x y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            cases Y with
            | prod A B =>
              simp only [hgy] at hchk
              obtain ⟨vp, hvp, hpok⟩ := he y (.prod A B) (mode_get_inBody hgy)
              cases hpok with
              | prod haok _ =>
                simp only [exec, hvp]
                exact ih hsub hchk hh (he.set x _ A haok)
            | _ => simp [hgy] at hchk
        | snd x y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            cases Y with
            | prod A B =>
              simp only [hgy] at hchk
              obtain ⟨vp, hvp, hpok⟩ := he y (.prod A B) (mode_get_inBody hgy)
              cases hpok with
              | prod _ hbok =>
                simp only [exec, hvp]
                exact ih hsub hchk hh (he.set x _ B hbok)
            | _ => simp [hgy] at hchk
        | phantom x T =>
          simp only [chk] at hchk
          split at hchk <;> try simp at hchk
          simp only [exec]
          exact ih hsub hchk hh (he.set x .unit (.phantom T) (.phantom (toStatic T)))
        | lam x T U c body =>
          simp only [chk] at hchk
          cases hgc : Mode.get ⟨t₀, true⟩ Γ c with
          | none => simp [hgc] at hchk
          | some C =>
            simp only [hgc] at hchk
            split at hchk <;> try simp at hchk
            rename_i hcond
            have hC : C.allStatic = true := by simp [Bool.and_eq_true] at hcond; exact hcond.1.1.1.1
            obtain ⟨vc, hvc, hcok⟩ := he c C (mode_get_inBody hgc)
            rw [toStatic_id_of_allStatic hC] at hcok
            simp only [exec, hvc]
            cases hbchk : chk cf sub ⟨t₀, true⟩ (Ctx.frame T C) body with
            | none => simp [hbchk] at hchk
            | some bres =>
              cases bres with
              | none =>
                simp only [hbchk] at hchk
                have hbc : BodyChecked cf T U C body := ⟨sub, t₀, hsub, by simp [hbchk]⟩
                exact ih hsub hchk hh (he.set x (.clo body vc) (.fn T U) (.cloStatic (MSub.refl _) hC hcok hbc))
              | some Γb =>
                simp only [hbchk] at hchk
                split at hchk <;> try simp at hchk
                rename_i hret
                have hbc : BodyChecked cf T U C body := ⟨sub, t₀, hsub, by simp [hbchk, hret]⟩
                exact ih hsub hchk hh (he.set x (.clo body vc) (.fn T U) (.cloStatic (MSub.refl _) hC hcok hbc))
        | call x g y =>
          simp only [chk] at hchk
          cases hgg : Mode.get ⟨t₀, true⟩ Γ g with
          | none => simp [hgg] at hchk
          | some G =>
            cases G with
            | fn T U =>
              cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
              | none => simp [hgg, hgy] at hchk
              | some A =>
                simp only [hgg, hgy] at hchk
                split at hchk <;> try simp at hchk
                rename_i hAT; simp at hAT; subst A
                obtain ⟨vg, hvg, hgok⟩ := he g (.fn T U) (mode_get_inBody hgg)
                obtain ⟨vy, hvy, hyok⟩ := he y T (mode_get_inBody hgy)
                have hclo : ∃ body cap T₀ U₀ C f₀, vg = .clo body cap ∧
                    erase T₀ = erase T ∧ erase U₀ = erase U ∧ C.allStatic = true ∧
                    ValOk htys cap C ∧ BodyChecked f₀ T₀ U₀ C body := by
                  cases hgok with
                  | @clo body cap T₀ U₀ C _ _ f₀ hfn hC hcap hb =>
                    have heq := hfn.erase_eq; simp [erase] at heq; repeat rw [erase_toStatic] at heq
                    exact ⟨body, cap, T₀, U₀, C, f₀, rfl, heq.1, heq.2, hC, hcap, hb⟩
                  | @cloStatic body cap T₀ U₀ C _ _ f₀ hfn hC hcap hb =>
                    have heq := hfn.erase_eq; simp [erase] at heq; repeat rw [erase_toStatic] at heq
                    exact ⟨body, cap, T₀, U₀, C, f₀, rfl, heq.1, heq.2, hC, hcap, hb⟩
                obtain ⟨body, cap, T₀, U₀, C, f₀, rfl, heT, heU, hC, hcap, sub₀, tb₀, hsub₀, hbchk⟩ := hclo
                have hyT₀ := hyok.weaken_sub _ (MSub.of_erase_toStatic heT).2
                have hframe := envStatic_frame hyT₀ hcap hC
                simp only [exec, hvg, hvy]
                cases hbres : chk f₀ sub₀ ⟨tb₀, true⟩ (Ctx.frame T₀ C) body with
                | none => simp [hbres] at hbchk
                | some bres =>
                  have ⟨hbns, hbdone⟩ := ih hsub₀ hbres hh hframe
                  cases hexec : exec f st (Env.frame vy cap) body with
                  | halted | outOfFuel => exact ⟨rfl, fun _ _ hd => nomatch hd⟩
                  | dangling | wrong => simp [hexec, Res.isStuck] at hbns
                  | done st1 env1 =>
                    obtain ⟨ht1, htys1, Γb, hbopt, hext1, hh1, hchg1, he1⟩ := hbdone st1 env1 hexec
                    cases bres with
                    | none => nomatch hbopt
                    | some Γb' =>
                      cases hbopt
                      simp [hbres] at hbchk
                      obtain ⟨vr, hvr, hvru⟩ := he1 2 U₀ hbchk
                      simp only [hvr]
                      have hvrU := hvru.weaken_sub _ (MSub.of_erase_toStatic heU).1
                      have ⟨hrns, hrdone⟩ := ih hsub hchk hh1 ((he.mono hext1).set x vr U hvrU)
                      refine ⟨hrns, fun st' env' hd => ?_⟩
                      obtain ⟨ht2, htys', Γ', rfl, hext2, hh2, hchg2, he2⟩ := hrdone st' env' hd
                      exact ⟨ht2.trans ht1, htys', Γ', rfl, hext1.trans hext2, hh2, StaticChanged.trans hext1 hchg1 hchg2, he2⟩
            | _ => simp [hgg] at hchk
        | endRegion n => simp [chk] at hchk
        | abort =>
          simp [chk] at hchk; subst hchk
          exact ⟨rfl, fun _ _ hd => nomatch hd⟩


/-! ### Step B: `exec_body_ok` (general `inBody = true` calls with live set `L`) -/

def EnvBodyOk (htys : List (Lft × Ty)) (L : Nat → Prop) (env : Env) (Γ : Ctx) : Prop :=
  ∀ (x : Nat) (T : Ty), Γ x = some T → ∃ v, env x = some v ∧ ValOk htys v T ∧ ValInL L v

theorem EnvBodyOk.mono {htys htys' : List (Lft × Ty)} {L L' : Nat → Prop}
    (hext : HeapExt htys htys') (hL : ∀ p, L p → L' p)
    {env : Env} {Γ : Ctx} (he : EnvBodyOk htys L env Γ) : EnvBodyOk htys' L' env Γ :=
  fun x T hx => let ⟨v, hv, hok, hin⟩ := he x T hx; ⟨v, hv, hok.mono hext, hin.mono hL⟩

theorem EnvBodyOk.set {htys : List (Lft × Ty)} {L : Nat → Prop} {env : Env} {Γ : Ctx}
    (he : EnvBodyOk htys L env Γ) (x : Nat) (v : Val) (T : Ty)
    (hv : ValOk htys v T) (hin : ValInL L v) :
    EnvBodyOk htys L (env.set x v) (Γ.set x T) := by
  intro k T' hk
  by_cases hkx : k = x
  · subst hkx; simp [Ctx.set] at hk; subst hk; exact ⟨v, by simp [Env.set], hv, hin⟩
  · simp [Ctx.set, hkx] at hk; simp [Env.set, hkx]; exact he k T' hk

theorem envBody_frame {htys : List (Lft × Ty)} {L : Nat → Prop} {va vc : Val} {T₀ C : Ty}
    (ha : ValOk htys va T₀) (hain : ValInL L va)
    (hc : ValOk htys vc C) (hcin : ValInL L vc) :
    EnvBodyOk htys L (Env.frame va vc) (Ctx.frame T₀ C) := by
  intro k T hk
  by_cases hk1 : k = 1
  · subst hk1; simp [Ctx.frame, Ctx.set] at hk; subst hk; exact ⟨vc, by simp [Env.frame, Env.set], hc, hcin⟩
  · by_cases hk0 : k = 0
    · subst hk0; simp [Ctx.frame, Ctx.set] at hk; subst hk; exact ⟨va, by simp [Env.frame, Env.set], ha, hain⟩
    · simp [Ctx.frame, Ctx.set, hk1, hk0, Ctx.empty] at hk

theorem cloStatic_call_step {htys : List (Lft × Ty)} {vy : Val} {T₀ U₀ T U : Ty}
    (hfn : MSub (.fn (toStatic T₀) (toStatic U₀)) (.fn T U))
    (hyok : ValOk htys vy T) :
    ValOk htys vy (toStatic T₀) ∧ MSub (toStatic U₀) U := by
  generalize hL : Ty.fn (toStatic T₀) (toStatic U₀) = L at hfn
  cases hfn with
  | fn hT hU =>
    injection hL with h1 h2; rw [h1]; rw [h2]
    exact ⟨hyok.weaken_sub _ hT, hU⟩
  | @fnFn A₀ B₀ hAB =>
    injection hL with h1 h2
    have he1 : erase T₀ = .fn (erase A₀) .unit := by
      rw [← erase_toStatic T₀, h1]; rfl
    obtain ⟨A₁, U₁, rfl, hA₁, hU₁⟩ := erase_eq_fn he1
    obtain rfl := erase_eq_unit hU₁
    have he2 : erase U₀ = .unit := by rw [← erase_toStatic U₀, h2]; rfl
    obtain rfl := erase_eq_unit he2
    exact ⟨hyok.as_cloStatic (hAB.symm.trans hA₁.symm) rfl, .unit⟩

theorem exec_body_ok : ∀ (fuel : Nat) {cfuel : Nat} {sub : Ty → Ty → Bool}
    (hsub : ∀ X Y, sub X Y = true → MSub X Y)
    {t₀ : Nat} {Γ : Ctx} {P : List Stmt} {res : Option Ctx}
    (hchk : chk cfuel sub ⟨t₀, true⟩ Γ P = some res)
    {st : St} {env : Env} {htys : List (Lft × Ty)} {L : Nat → Prop}
    (hh : HeapOk htys st.heap) (hL : LiveSetOk st.time htys st.heap L)
    (he : EnvBodyOk htys L env Γ),
    (exec fuel st env P).isStuck = false ∧
    (∀ st' env', exec fuel st env P = .done st' env' →
      st'.time = st.time ∧
      ∃ htys' L' Γ', res = some Γ' ∧ HeapExt htys htys' ∧ (∀ p, L p → L' p) ∧
        HeapOk htys' st'.heap ∧ LiveSetOk st.time htys' st'.heap L' ∧
        EnvBodyOk htys' L' env' Γ') := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact ⟨rfl, fun _ _ h => nomatch h⟩
  | succ f ih =>
    intro cfuel sub hsub t₀ Γ P res hchk st env htys L hh hL he
    cases cfuel with
    | zero => simp [chk] at hchk
    | succ cf =>
      cases P with
      | nil =>
        simp [chk] at hchk; subst hchk
        refine ⟨rfl, fun st' env' hd => ?_⟩
        simp [exec] at hd; obtain ⟨rfl, rfl⟩ := hd
        exact ⟨rfl, htys, L, Γ, rfl, HeapExt.refl htys, fun _ h => h, hh, hL, he⟩
      | cons s rest =>
        cases s with
        | nat x n =>
          simp [chk] at hchk
          exact ih hsub hchk hh hL (he.set x (.nat n) .nat (.nat n) trivial)
        | unit x =>
          simp [chk] at hchk
          exact ih hsub hchk hh hL (he.set x .unit .unit .unit trivial)
        | copy x y T =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some S =>
            simp only [hgy, Bool.and_eq_true] at hchk
            split at hchk <;> try simp at hchk
            rename_i hcond
            obtain ⟨v, hvy, hvok, hvin⟩ := he y S (mode_get_inBody hgy)
            simp only [exec, hvy]
            exact ih hsub hchk hh hL (he.set x v T (hvok.weaken_sub _ (hsub S T hcond.2)) hvin)
        | alloc x l y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some T =>
            simp only [hgy] at hchk
            split at hchk <;> try simp at hchk
            rename_i hcond; simp [Mode.lv] at hcond; subst hcond
            obtain ⟨v, hvy, hvok, hvin⟩ := he y T (mode_get_inBody hgy)
            simp only [exec, hvy, Lft.live, ite_true]
            let st1 : St := { st with heap := st.heap ++ [(.static, v)] }
            have hh' : HeapOk (htys ++ [(.static, T)]) st1.heap := hh.alloc .static T hvok
            have hL' : LiveSetOk st1.time (htys ++ [(.static, T)]) st1.heap (fun q => L q ∨ q = htys.length) :=
              hL.alloc_static hh T hvin
            have hext := HeapExt.snoc htys (.static, T)
            have hp : (htys ++ [(.static, T)])[st.heap.length]? = some (.static, T) := by
              rw [hh.1]; exact get_append_len htys (.static, T)
            have hptr : ValOk (htys ++ [(.static, T)]) (.ptr st.heap.length) (.refMut .static T) :=
              .refMut hp rfl (MSub.refl _) (MSub.refl _)
            have hpin : ValInL (fun q => L q ∨ q = htys.length) (.ptr st.heap.length) := Or.inr hh.1
            have ⟨hns, hdone⟩ := ih hsub hchk (st := st1) hh' hL'
              ((he.mono hext (fun _ => Or.inl)).set x (.ptr st.heap.length) (.refMut .static T) hptr hpin)
            refine ⟨hns, fun st' env' hd => ?_⟩
            obtain ⟨ht, htys', L'', Γ', rfl, hext', hLmono, hh'', hL'', he'⟩ := hdone st' env' hd
            exact ⟨ht, htys', L'', Γ', rfl, hext.trans hext', fun p hp0 => hLmono p (Or.inl hp0), hh'', hL'', he'⟩
        | share x y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            cases Y with
            | refMut l T =>
              simp only [hgy] at hchk
              obtain ⟨v, hvy, hvok, hvin⟩ := he y (.refMut l T) (mode_get_inBody hgy)
              cases hvok with
              | refMut hp hr hHT _ =>
                simp only [exec, hvy]
                exact ih hsub hchk hh hL (he.set x _ (.ref l T) (.ref hp hr hHT) hvin)
            | _ => simp [hgy] at hchk
        | newCell x l y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some T =>
            simp only [hgy] at hchk
            split at hchk <;> try simp at hchk
            rename_i hcond; simp [Mode.lv] at hcond; subst hcond
            obtain ⟨v, hvy, hvok, hvin⟩ := he y T (mode_get_inBody hgy)
            simp only [exec, hvy, Lft.live, ite_true]
            let st1 : St := { st with heap := st.heap ++ [(.static, v)] }
            have hh' : HeapOk (htys ++ [(.static, .cell T)]) st1.heap := hh.alloc .static (.cell T) (.cell hvok)
            have hL' : LiveSetOk st1.time (htys ++ [(.static, .cell T)]) st1.heap (fun q => L q ∨ q = htys.length) :=
              hL.alloc_static hh (.cell T) hvin
            have hext := HeapExt.snoc htys (.static, .cell T)
            have hp : (htys ++ [(.static, .cell T)])[st.heap.length]? = some (.static, .cell T) := by
              rw [hh.1]; exact get_append_len htys (.static, .cell T)
            have hptr : ValOk (htys ++ [(.static, .cell T)]) (.ptr st.heap.length) (.ref .static (.cell T)) :=
              .ref hp rfl (MSub.refl _)
            have hpin : ValInL (fun q => L q ∨ q = htys.length) (.ptr st.heap.length) := Or.inr hh.1
            have ⟨hns, hdone⟩ := ih hsub hchk (st := st1) hh' hL'
              ((he.mono hext (fun _ => Or.inl)).set x (.ptr st.heap.length) (.ref .static (.cell T)) hptr hpin)
            refine ⟨hns, fun st' env' hd => ?_⟩
            obtain ⟨ht, htys', L'', Γ', rfl, hext', hLmono, hh'', hL'', he'⟩ := hdone st' env' hd
            exact ⟨ht, htys', L'', Γ', rfl, hext.trans hext', fun p hp0 => hLmono p (Or.inl hp0), hh'', hL'', he'⟩
        | read x y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            cases Y with
            | ref l T =>
              simp only [hgy] at hchk
              obtain ⟨v, hvy, hvok, hvin⟩ := he y (.ref l T) (mode_get_inBody hgy)
              cases hvok with
              | @ref p r0 _ H0 _ hp _ hHT =>
                obtain ⟨r1, w1, hwp1, hrlive, hwin⟩ := hL.2 p hvin
                obtain ⟨w, hwp, hwok⟩ := hh.2 p r0 H0 hp
                rw [hwp] at hwp1; cases hwp1
                simp only [exec, hvy, hwp, hrlive, ite_true]
                exact ih hsub hchk hh hL (he.set x w1 T (hwok.weaken_sub _ hHT) hwin)
            | refMut l T =>
              simp only [hgy] at hchk
              obtain ⟨v, hvy, hvok, hvin⟩ := he y (.refMut l T) (mode_get_inBody hgy)
              cases hvok with
              | @refMut p r0 _ H0 _ hp _ hHT _ =>
                obtain ⟨r1, w1, hwp1, hrlive, hwin⟩ := hL.2 p hvin
                obtain ⟨w, hwp, hwok⟩ := hh.2 p r0 H0 hp
                rw [hwp] at hwp1; cases hwp1
                simp only [exec, hvy, hwp, hrlive, ite_true]
                exact ih hsub hchk hh hL (he.set x w1 T (hwok.weaken_sub _ hHT) hwin)
            | _ => simp [hgy] at hchk
        | write y z =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            cases Y with
            | refMut l T =>
              cases hgz : Mode.get ⟨t₀, true⟩ Γ z with
              | none => simp [hgy, hgz] at hchk
              | some Z =>
                simp only [hgy, hgz] at hchk
                split at hchk <;> try simp at hchk
                rename_i hZT; simp at hZT; subst Z
                obtain ⟨vy, hvy, hyok, hyin⟩ := he y (.refMut l T) (mode_get_inBody hgy)
                obtain ⟨vz, hvz, hzok, hzin⟩ := he z T (mode_get_inBody hgz)
                cases hyok with
                | @refMut p r0 _ H0 _ hp _ _ hTH =>
                  obtain ⟨r1, w1, hwp1, hrlive, _⟩ := hL.2 p hyin
                  obtain ⟨w, hwp, _⟩ := hh.2 p r0 H0 hp
                  rw [hwp] at hwp1; cases hwp1
                  simp only [exec, hvy, hvz, hwp, hrlive, ite_true]
                  let st1 : St := { st with heap := st.heap.set p (r0, vz) }
                  have hh' : HeapOk htys st1.heap := hh.update hp (hzok.weaken_sub _ hTH)
                  have hL' : LiveSetOk st1.time htys st1.heap L := hL.update hh hyin hrlive hzin
                  exact ih hsub hchk (st := st1) hh' hL' he
            | _ => simp [hgy] at hchk
        | cellGet x c =>
          simp only [chk] at hchk
          cases hgc : Mode.get ⟨t₀, true⟩ Γ c with
          | none => simp [hgc] at hchk
          | some Y =>
            cases Y with
            | ref l C =>
              cases C with
              | cell T =>
                simp only [hgc] at hchk
                obtain ⟨vc, hvc, hcok, hcin⟩ := he c (.ref l (.cell T)) (mode_get_inBody hgc)
                cases hcok with
                | @ref p r0 _ H0 _ hp _ hHC =>
                  obtain ⟨r1, w1, hwp1, hrlive, hwin⟩ := hL.2 p hcin
                  obtain ⟨w, hwp, hwok⟩ := hh.2 p r0 H0 hp
                  rw [hwp] at hwp1; cases hwp1
                  have hcell := hwok.weaken_sub _ hHC
                  cases hcell with
                  | cell hwt =>
                    simp only [exec, hvc, hwp, hrlive, ite_true]
                    exact ih hsub hchk hh hL (he.set x w1 T hwt hwin)
              | _ => simp [hgc] at hchk
            | _ => simp [hgc] at hchk
        | cellSet c z =>
          simp only [chk] at hchk
          cases hgc : Mode.get ⟨t₀, true⟩ Γ c with
          | none => simp [hgc] at hchk
          | some Y =>
            cases Y with
            | ref l C =>
              cases C with
              | cell T =>
                cases hgz : Mode.get ⟨t₀, true⟩ Γ z with
                | none => simp [hgc, hgz] at hchk
                | some Z =>
                  simp only [hgc, hgz] at hchk
                  split at hchk <;> try simp at hchk
                  rename_i hZT; simp at hZT; subst Z
                  obtain ⟨vc, hvc, hcok, hcin⟩ := he c (.ref l (.cell T)) (mode_get_inBody hgc)
                  obtain ⟨vz, hvz, hzok, hzin⟩ := he z T (mode_get_inBody hgz)
                  cases hcok with
                  | @ref p r0 _ H0 _ hp _ hHC =>
                    obtain ⟨r1, w1, hwp1, hrlive, _⟩ := hL.2 p hcin
                    obtain ⟨w, hwp, _⟩ := hh.2 p r0 H0 hp
                    rw [hwp] at hwp1; cases hwp1
                    cases hHC with
                    | cell _ hTH =>
                      simp only [exec, hvc, hvz, hwp, hrlive, ite_true]
                      let st1 : St := { st with heap := st.heap.set p (r0, vz) }
                      have hh' : HeapOk htys st1.heap := hh.update hp (.cell (hzok.weaken_sub _ hTH))
                      have hL' : LiveSetOk st1.time htys st1.heap L := hL.update hh hcin hrlive hzin
                      exact ih hsub hchk (st := st1) hh' hL' he
              | _ => simp [hgc] at hchk
            | _ => simp [hgc] at hchk
        | pair x y z =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some A =>
            cases hgz : Mode.get ⟨t₀, true⟩ Γ z with
            | none => simp [hgy, hgz] at hchk
            | some B =>
              simp only [hgy, hgz] at hchk
              obtain ⟨va, hva, haok, hain⟩ := he y A (mode_get_inBody hgy)
              obtain ⟨vb, hvb, hbok, hbin⟩ := he z B (mode_get_inBody hgz)
              simp only [exec, hva, hvb]
              exact ih hsub hchk hh hL (he.set x (.pair va vb) (.prod A B) (.prod haok hbok) ⟨hain, hbin⟩)
        | fst x y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            cases Y with
            | prod A B =>
              simp only [hgy] at hchk
              obtain ⟨vp, hvp, hpok, hpin⟩ := he y (.prod A B) (mode_get_inBody hgy)
              cases hpok with
              | prod haok _ =>
                simp only [exec, hvp]
                exact ih hsub hchk hh hL (he.set x _ A haok hpin.1)
            | _ => simp [hgy] at hchk
        | snd x y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            cases Y with
            | prod A B =>
              simp only [hgy] at hchk
              obtain ⟨vp, hvp, hpok, hpin⟩ := he y (.prod A B) (mode_get_inBody hgy)
              cases hpok with
              | prod _ hbok =>
                simp only [exec, hvp]
                exact ih hsub hchk hh hL (he.set x _ B hbok hpin.2)
            | _ => simp [hgy] at hchk
        | phantom x T =>
          simp only [chk] at hchk
          split at hchk <;> try simp at hchk
          simp only [exec]
          exact ih hsub hchk hh hL (he.set x .unit (.phantom T) (.phantom T) trivial)
        | lam x T U c body =>
          simp only [chk] at hchk
          cases hgc : Mode.get ⟨t₀, true⟩ Γ c with
          | none => simp [hgc] at hchk
          | some C =>
            simp only [hgc] at hchk
            split at hchk <;> try simp at hchk
            rename_i hcond
            have hC : C.allStatic = true := by simp [Bool.and_eq_true] at hcond; exact hcond.1.1.1.1
            obtain ⟨vc, hvc, hcok, _⟩ := he c C (mode_get_inBody hgc)
            simp only [exec, hvc]
            cases hbchk : chk cf sub ⟨t₀, true⟩ (Ctx.frame T C) body with
            | none => simp [hbchk] at hchk
            | some bres =>
              cases bres with
              | none =>
                simp only [hbchk] at hchk
                have hbc : BodyChecked cf T U C body := ⟨sub, t₀, hsub, by simp [hbchk]⟩
                exact ih hsub hchk hh hL (he.set x (.clo body vc) (.fn T U) (.clo (MSub.refl _) hC hcok hbc) trivial)
              | some Γb =>
                simp only [hbchk] at hchk
                split at hchk <;> try simp at hchk
                rename_i hret
                have hbc : BodyChecked cf T U C body := ⟨sub, t₀, hsub, by simp [hbchk, hret]⟩
                exact ih hsub hchk hh hL (he.set x (.clo body vc) (.fn T U) (.clo (MSub.refl _) hC hcok hbc) trivial)
        | call x g y =>
          simp only [chk] at hchk
          cases hgg : Mode.get ⟨t₀, true⟩ Γ g with
          | none => simp [hgg] at hchk
          | some G =>
            cases G with
            | fn T U =>
              cases hgy : Mode.get ⟨t₀, true⟩ Γ y with
              | none => simp [hgg, hgy] at hchk
              | some A =>
                simp only [hgg, hgy] at hchk
                split at hchk <;> try simp at hchk
                rename_i hAT; simp at hAT; subst A
                obtain ⟨vg, hvg, hgok, _⟩ := he g (.fn T U) (mode_get_inBody hgg)
                obtain ⟨vy, hvy, hyok, hyin⟩ := he y T (mode_get_inBody hgy)
                cases hgok with
                | @clo body cap T₀ U₀ C _ _ f₀ hfn hC hcap hb =>
                  cases hfn with
                  | fn hTT₀ hU₀U =>
                    obtain ⟨sub₀, tb₀, hsub₀, hbchk⟩ := hb
                    have hcapin := valInL_of_semLive hL hcap (semLive_of_allStatic st.time hC)
                    have hframe := envBody_frame (hyok.weaken_sub _ hTT₀) hyin hcap hcapin
                    simp only [exec, hvg, hvy]
                    cases hbres : chk f₀ sub₀ ⟨tb₀, true⟩ (Ctx.frame T₀ C) body with
                    | none => simp [hbres] at hbchk
                    | some bres =>
                      have ⟨hbns, hbdone⟩ := ih hsub₀ hbres hh hL hframe
                      cases hexec : exec f st (Env.frame vy cap) body with
                      | halted | outOfFuel => exact ⟨rfl, fun _ _ hd => nomatch hd⟩
                      | dangling | wrong => simp [hexec, Res.isStuck] at hbns
                      | done st1 env1 =>
                        obtain ⟨ht1, htys1, L1, Γb, hbopt, hext1, hLmono1, hh1, hL1, he1⟩ := hbdone st1 env1 hexec
                        cases bres with
                        | none => nomatch hbopt
                        | some Γb' =>
                          cases hbopt; simp [hbres] at hbchk
                          obtain ⟨vr, hvr, hvru, hvrin⟩ := he1 2 U₀ hbchk
                          simp only [hvr]
                          have hL1' : LiveSetOk st1.time htys1 st1.heap L1 := by rw [ht1]; exact hL1
                          have ⟨hrns, hrdone⟩ := ih hsub hchk (st := st1) hh1 hL1'
                            ((he.mono hext1 hLmono1).set x vr U (hvru.weaken_sub _ hU₀U) hvrin)
                          refine ⟨hrns, fun st' env' hd => ?_⟩
                          obtain ⟨ht2, htys', L', Γ', rfl, hext2, hLmono2, hh2, hL2, he2⟩ := hrdone st' env' hd
                          rw [ht1] at ht2 hL2
                          exact ⟨ht2, htys', L', Γ', rfl, hext1.trans hext2, fun p hp0 => hLmono2 p (hLmono1 p hp0), hh2, hL2, he2⟩
                  | @fnFn A₀ B₀ hAB =>
                    obtain ⟨sub₀, tb₀, hsub₀, hbchk⟩ := hb
                    have hyStat : ValOk htys vy (toStatic (.fn A₀ .unit)) :=
                      hyok.as_cloStatic hAB.symm rfl
                    have hframe := envStatic_frame (T₀ := .fn A₀ .unit) hyStat hcap hC
                    simp only [exec, hvg, hvy]
                    cases hbres : chk f₀ sub₀ ⟨tb₀, true⟩ (Ctx.frame (.fn A₀ .unit) C) body with
                    | none => simp [hbres] at hbchk
                    | some bres =>
                      have ⟨hbns, hbdone⟩ := exec_static_ok f hsub₀ hbres hh hframe
                      cases hexec : exec f st (Env.frame vy cap) body with
                      | halted | outOfFuel => exact ⟨rfl, fun _ _ hd => nomatch hd⟩
                      | dangling | wrong => simp [hexec, Res.isStuck] at hbns
                      | done st1 env1 =>
                        obtain ⟨ht1, htys1, Γb, hbopt, hext1, hh1, hchg1, he1⟩ := hbdone st1 env1 hexec
                        cases bres with
                        | none => nomatch hbopt
                        | some Γb' =>
                          cases hbopt; simp [hbres] at hbchk
                          obtain ⟨vr, hvr, hvru⟩ := he1 2 .unit hbchk
                          simp only [hvr]
                          have hL1 : LiveSetOk st1.time htys1 st1.heap (fun p => L p ∨ Lsem st.time htys1 p) := by
                            rw [ht1]; exact LiveSetOk.after_static hext1 hh hh1 hL hchg1
                          have hvrin : ValInL (fun p => L p ∨ Lsem st.time htys1 p) vr := by
                            cases hvru; trivial
                          have ⟨hrns, hrdone⟩ := ih hsub hchk (st := st1) hh1 hL1
                            ((he.mono hext1 (fun _ => Or.inl)).set x vr .unit hvru hvrin)
                          refine ⟨hrns, fun st' env' hd => ?_⟩
                          obtain ⟨ht2, htys', L', Γ', rfl, hext2, hLmono2, hh2, hL2, he2⟩ := hrdone st' env' hd
                          rw [ht1] at ht2 hL2
                          exact ⟨ht2, htys', L', Γ', rfl, hext1.trans hext2, fun p hp0 => hLmono2 p (Or.inl hp0), hh2, hL2, he2⟩
                | @cloStatic body cap T₀ U₀ C _ _ f₀ hfn hC hcap hb =>
                  obtain ⟨sub₀, tb₀, hsub₀, hbchk⟩ := hb
                  obtain ⟨hyStat, hUsub⟩ := cloStatic_call_step hfn hyok
                  have hframe := envStatic_frame hyStat hcap hC
                  simp only [exec, hvg, hvy]
                  cases hbres : chk f₀ sub₀ ⟨tb₀, true⟩ (Ctx.frame T₀ C) body with
                  | none => simp [hbres] at hbchk
                  | some bres =>
                    have ⟨hbns, hbdone⟩ := exec_static_ok f hsub₀ hbres hh hframe
                    cases hexec : exec f st (Env.frame vy cap) body with
                    | halted | outOfFuel => exact ⟨rfl, fun _ _ hd => nomatch hd⟩
                    | dangling | wrong => simp [hexec, Res.isStuck] at hbns
                    | done st1 env1 =>
                      obtain ⟨ht1, htys1, Γb, hbopt, hext1, hh1, hchg1, he1⟩ := hbdone st1 env1 hexec
                      cases bres with
                      | none => nomatch hbopt
                      | some Γb' =>
                        cases hbopt; simp [hbres] at hbchk
                        obtain ⟨vr, hvr, hvru⟩ := he1 2 U₀ hbchk
                        simp only [hvr]
                        have hL1 : LiveSetOk st1.time htys1 st1.heap (fun p => L p ∨ Lsem st.time htys1 p) := by
                          rw [ht1]; exact LiveSetOk.after_static hext1 hh hh1 hL hchg1
                        have hvrin : ValInL (fun p => L p ∨ Lsem st.time htys1 p) vr :=
                          (valInL_lsem hvru (semLive_of_allStatic st.time (allStatic_toStatic U₀))).mono (fun _ => Or.inr)
                        have ⟨hrns, hrdone⟩ := ih hsub hchk (st := st1) hh1 hL1
                          ((he.mono hext1 (fun _ => Or.inl)).set x vr U (hvru.weaken_sub _ hUsub) hvrin)
                        refine ⟨hrns, fun st' env' hd => ?_⟩
                        obtain ⟨ht2, htys', L', Γ', rfl, hext2, hLmono2, hh2, hL2, he2⟩ := hrdone st' env' hd
                        rw [ht1] at ht2 hL2
                        exact ⟨ht2, htys', L', Γ', rfl, hext1.trans hext2, fun p hp0 => hLmono2 p (Or.inl hp0), hh2, hL2, he2⟩
            | _ => simp [hgg] at hchk
        | endRegion n => simp [chk] at hchk
        | abort =>
          simp [chk] at hchk; subst hchk
          exact ⟨rfl, fun _ _ hd => nomatch hd⟩

/-! ### Step C: `exec_top_ok` and `MSub_sound` -/

def EnvTopOk (htys : List (Lft × Ty)) (env : Env) (Γ : Ctx) : Prop :=
  ∀ (x : Nat) (T : Ty), Γ x = some T → ∃ v, env x = some v ∧ ValOk htys v T

theorem EnvTopOk.mono {htys htys' : List (Lft × Ty)} (hext : HeapExt htys htys')
    {env : Env} {Γ : Ctx} (he : EnvTopOk htys env Γ) : EnvTopOk htys' env Γ :=
  fun x T hx => let ⟨v, hv, hok⟩ := he x T hx; ⟨v, hv, hok.mono hext⟩

theorem EnvTopOk.set {htys : List (Lft × Ty)} {env : Env} {Γ : Ctx}
    (he : EnvTopOk htys env Γ) (x : Nat) (v : Val) (T : Ty) (hv : ValOk htys v T) :
    EnvTopOk htys (env.set x v) (Γ.set x T) := by
  intro k T' hk
  by_cases hkx : k = x
  · subst hkx; simp [Ctx.set] at hk; subst hk; exact ⟨v, by simp [Env.set], hv⟩
  · simp [Ctx.set, hkx] at hk; simp [Env.set, hkx]; exact he k T' hk

theorem exec_top_ok : ∀ (fuel : Nat) {cfuel : Nat} {sub : Ty → Ty → Bool}
    (hsub : ∀ X Y, sub X Y = true → MSub X Y)
    {Γ : Ctx} {P : List Stmt} {res : Option Ctx}
    {st : St} {env : Env} {htys : List (Lft × Ty)}
    (hchk : chk cfuel sub ⟨st.time, false⟩ Γ P = some res)
    (hh : HeapOk htys st.heap) (he : EnvTopOk htys env Γ),
    (exec fuel st env P).isStuck = false := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ f ih =>
    intro cfuel sub hsub Γ P res st env htys hchk hh he
    cases cfuel with
    | zero => simp [chk] at hchk
    | succ cf =>
      cases P with
      | nil => rfl
      | cons s rest =>
        cases s with
        | nat x n =>
          simp [chk] at hchk
          exact ih hsub hchk hh (he.set x (.nat n) .nat (.nat n))
        | unit x =>
          simp [chk] at hchk
          exact ih hsub hchk hh (he.set x .unit .unit .unit)
        | copy x y T =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨st.time, false⟩ Γ y with
          | none => simp [hgy] at hchk
          | some S =>
            simp only [hgy, Bool.and_eq_true] at hchk
            split at hchk <;> try simp at hchk
            rename_i hcond
            obtain ⟨v, hvy, hvok⟩ := he y S (mode_get_top hgy).1
            simp only [exec, hvy]
            exact ih hsub hchk hh (he.set x v T (hvok.weaken_sub _ (hsub S T hcond.2)))
        | alloc x l y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨st.time, false⟩ Γ y with
          | none => simp [hgy] at hchk
          | some T =>
            simp only [hgy] at hchk
            split at hchk <;> try simp at hchk
            rename_i hcond; simp [Mode.lv] at hcond
            obtain ⟨v, hvy, hvok⟩ := he y T (mode_get_top hgy).1
            simp only [exec, hvy, hcond, ite_true]
            let st1 : St := { st with heap := st.heap ++ [(l, v)] }
            have hh' : HeapOk (htys ++ [(l, T)]) st1.heap := hh.alloc l T hvok
            have hext := HeapExt.snoc htys (l, T)
            have hp : (htys ++ [(l, T)])[st.heap.length]? = some (l, T) := by
              rw [hh.1]; exact get_append_len htys (l, T)
            have hptr : ValOk (htys ++ [(l, T)]) (.ptr st.heap.length) (.refMut l T) :=
              .refMut hp (Lft.outlives_refl l) (MSub.refl _) (MSub.refl _)
            exact ih hsub hchk (st := st1) hh' ((he.mono hext).set x (.ptr st.heap.length) (.refMut l T) hptr)
        | share x y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨st.time, false⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            cases Y with
            | refMut l T =>
              simp only [hgy] at hchk
              obtain ⟨v, hvy, hvok⟩ := he y (.refMut l T) (mode_get_top hgy).1
              cases hvok with
              | refMut hp hr hHT _ =>
                simp only [exec, hvy]
                exact ih hsub hchk hh (he.set x _ (.ref l T) (.ref hp hr hHT))
            | _ => simp [hgy] at hchk
        | newCell x l y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨st.time, false⟩ Γ y with
          | none => simp [hgy] at hchk
          | some T =>
            simp only [hgy] at hchk
            split at hchk <;> try simp at hchk
            rename_i hcond; simp [Mode.lv] at hcond
            obtain ⟨v, hvy, hvok⟩ := he y T (mode_get_top hgy).1
            simp only [exec, hvy, hcond, ite_true]
            let st1 : St := { st with heap := st.heap ++ [(l, v)] }
            have hh' : HeapOk (htys ++ [(l, .cell T)]) st1.heap := hh.alloc l (.cell T) (.cell hvok)
            have hext := HeapExt.snoc htys (l, .cell T)
            have hp : (htys ++ [(l, .cell T)])[st.heap.length]? = some (l, .cell T) := by
              rw [hh.1]; exact get_append_len htys (l, .cell T)
            have hptr : ValOk (htys ++ [(l, .cell T)]) (.ptr st.heap.length) (.ref l (.cell T)) :=
              .ref hp (Lft.outlives_refl l) (MSub.refl _)
            exact ih hsub hchk (st := st1) hh' ((he.mono hext).set x (.ptr st.heap.length) (.ref l (.cell T)) hptr)
        | read x y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨st.time, false⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            have ⟨hgy0, hliveY⟩ := mode_get_top hgy
            cases Y with
            | ref l T =>
              simp only [hgy] at hchk
              simp [Ty.liveIn] at hliveY
              obtain ⟨v, hvy, hvok⟩ := he y (.ref l T) hgy0
              cases hvok with
              | @ref p r0 _ H0 _ hp hr hHT =>
                have hrlive := (Lft.outlives_iff_live_imp _ _).1 hr st.time hliveY.1
                obtain ⟨w, hwp, hwok⟩ := hh.2 p r0 H0 hp
                simp only [exec, hvy, hwp, hrlive, ite_true]
                exact ih hsub hchk hh (he.set x w T (hwok.weaken_sub _ hHT))
            | refMut l T =>
              simp only [hgy] at hchk
              simp [Ty.liveIn] at hliveY
              obtain ⟨v, hvy, hvok⟩ := he y (.refMut l T) hgy0
              cases hvok with
              | @refMut p r0 _ H0 _ hp hr hHT _ =>
                have hrlive := (Lft.outlives_iff_live_imp _ _).1 hr st.time hliveY.1
                obtain ⟨w, hwp, hwok⟩ := hh.2 p r0 H0 hp
                simp only [exec, hvy, hwp, hrlive, ite_true]
                exact ih hsub hchk hh (he.set x w T (hwok.weaken_sub _ hHT))
            | _ => simp [hgy] at hchk
        | write y z =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨st.time, false⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            have ⟨hgy0, hliveY⟩ := mode_get_top hgy
            cases Y with
            | refMut l T =>
              cases hgz : Mode.get ⟨st.time, false⟩ Γ z with
              | none => simp [hgy, hgz] at hchk
              | some Z =>
                simp only [hgy, hgz] at hchk
                split at hchk <;> try simp at hchk
                rename_i hZT; simp at hZT; subst Z
                simp [Ty.liveIn] at hliveY
                obtain ⟨vy, hvy, hyok⟩ := he y (.refMut l T) hgy0
                obtain ⟨vz, hvz, hzok⟩ := he z T (mode_get_top hgz).1
                cases hyok with
                | @refMut p r0 _ H0 _ hp hr _ hTH =>
                  have hrlive := (Lft.outlives_iff_live_imp _ _).1 hr st.time hliveY.1
                  obtain ⟨w, hwp, _⟩ := hh.2 p r0 H0 hp
                  simp only [exec, hvy, hvz, hwp, hrlive, ite_true]
                  let st1 : St := { st with heap := st.heap.set p (r0, vz) }
                  exact ih hsub hchk (st := st1) (hh.update hp (hzok.weaken_sub _ hTH)) he
            | _ => simp [hgy] at hchk
        | cellGet x c =>
          simp only [chk] at hchk
          cases hgc : Mode.get ⟨st.time, false⟩ Γ c with
          | none => simp [hgc] at hchk
          | some Y =>
            have ⟨hgc0, hliveY⟩ := mode_get_top hgc
            cases Y with
            | ref l C =>
              cases C with
              | cell T =>
                simp only [hgc] at hchk
                simp [Ty.liveIn] at hliveY
                obtain ⟨vc, hvc, hcok⟩ := he c (.ref l (.cell T)) hgc0
                cases hcok with
                | @ref p r0 _ H0 _ hp hr hHC =>
                  have hrlive := (Lft.outlives_iff_live_imp _ _).1 hr st.time hliveY.1
                  obtain ⟨w, hwp, hwok⟩ := hh.2 p r0 H0 hp
                  have hcell := hwok.weaken_sub _ hHC
                  cases hcell with
                  | cell hwt =>
                    simp only [exec, hvc, hwp, hrlive, ite_true]
                    exact ih hsub hchk hh (he.set x w T hwt)
              | _ => simp [hgc] at hchk
            | _ => simp [hgc] at hchk
        | cellSet c z =>
          simp only [chk] at hchk
          cases hgc : Mode.get ⟨st.time, false⟩ Γ c with
          | none => simp [hgc] at hchk
          | some Y =>
            have ⟨hgc0, hliveY⟩ := mode_get_top hgc
            cases Y with
            | ref l C =>
              cases C with
              | cell T =>
                cases hgz : Mode.get ⟨st.time, false⟩ Γ z with
                | none => simp [hgc, hgz] at hchk
                | some Z =>
                  simp only [hgc, hgz] at hchk
                  split at hchk <;> try simp at hchk
                  rename_i hZT; simp at hZT; subst Z
                  simp [Ty.liveIn] at hliveY
                  obtain ⟨vc, hvc, hcok⟩ := he c (.ref l (.cell T)) hgc0
                  obtain ⟨vz, hvz, hzok⟩ := he z T (mode_get_top hgz).1
                  cases hcok with
                  | @ref p r0 _ H0 _ hp hr hHC =>
                    have hrlive := (Lft.outlives_iff_live_imp _ _).1 hr st.time hliveY.1
                    obtain ⟨w, hwp, _⟩ := hh.2 p r0 H0 hp
                    cases hHC with
                    | cell _ hTH =>
                      simp only [exec, hvc, hvz, hwp, hrlive, ite_true]
                      let st1 : St := { st with heap := st.heap.set p (r0, vz) }
                      exact ih hsub hchk (st := st1) (hh.update hp (.cell (hzok.weaken_sub _ hTH))) he
              | _ => simp [hgc] at hchk
            | _ => simp [hgc] at hchk
        | pair x y z =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨st.time, false⟩ Γ y with
          | none => simp [hgy] at hchk
          | some A =>
            cases hgz : Mode.get ⟨st.time, false⟩ Γ z with
            | none => simp [hgy, hgz] at hchk
            | some B =>
              simp only [hgy, hgz] at hchk
              obtain ⟨va, hva, haok⟩ := he y A (mode_get_top hgy).1
              obtain ⟨vb, hvb, hbok⟩ := he z B (mode_get_top hgz).1
              simp only [exec, hva, hvb]
              exact ih hsub hchk hh (he.set x (.pair va vb) (.prod A B) (.prod haok hbok))
        | fst x y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨st.time, false⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            cases Y with
            | prod A B =>
              simp only [hgy] at hchk
              obtain ⟨vp, hvp, hpok⟩ := he y (.prod A B) (mode_get_top hgy).1
              cases hpok with
              | prod haok _ =>
                simp only [exec, hvp]
                exact ih hsub hchk hh (he.set x _ A haok)
            | _ => simp [hgy] at hchk
        | snd x y =>
          simp only [chk] at hchk
          cases hgy : Mode.get ⟨st.time, false⟩ Γ y with
          | none => simp [hgy] at hchk
          | some Y =>
            cases Y with
            | prod A B =>
              simp only [hgy] at hchk
              obtain ⟨vp, hvp, hpok⟩ := he y (.prod A B) (mode_get_top hgy).1
              cases hpok with
              | prod _ hbok =>
                simp only [exec, hvp]
                exact ih hsub hchk hh (he.set x _ B hbok)
            | _ => simp [hgy] at hchk
        | phantom x T =>
          simp only [chk] at hchk
          split at hchk <;> try simp at hchk
          simp only [exec]
          exact ih hsub hchk hh (he.set x .unit (.phantom T) (.phantom T))
        | lam x T U c body =>
          simp only [chk] at hchk
          cases hgc : Mode.get ⟨st.time, false⟩ Γ c with
          | none => simp [hgc] at hchk
          | some C =>
            simp only [hgc] at hchk
            split at hchk <;> try simp at hchk
            rename_i hcond
            have hC : C.allStatic = true := by simp [Bool.and_eq_true] at hcond; exact hcond.1.1.1.1
            obtain ⟨vc, hvc, hcok⟩ := he c C (mode_get_top hgc).1
            simp only [exec, hvc]
            cases hbchk : chk cf sub ⟨st.time, true⟩ (Ctx.frame T C) body with
            | none => simp [hbchk] at hchk
            | some bres =>
              cases bres with
              | none =>
                simp only [hbchk] at hchk
                have hbc : BodyChecked cf T U C body := ⟨sub, st.time, hsub, by simp [hbchk]⟩
                exact ih hsub hchk hh (he.set x (.clo body vc) (.fn T U) (.clo (MSub.refl _) hC hcok hbc))
              | some Γb =>
                simp only [hbchk] at hchk
                split at hchk <;> try simp at hchk
                rename_i hret
                have hbc : BodyChecked cf T U C body := ⟨sub, st.time, hsub, by simp [hbchk, hret]⟩
                exact ih hsub hchk hh (he.set x (.clo body vc) (.fn T U) (.clo (MSub.refl _) hC hcok hbc))
        | call x g y =>
          simp only [chk] at hchk
          cases hgg : Mode.get ⟨st.time, false⟩ Γ g with
          | none => simp [hgg] at hchk
          | some G =>
            cases G with
            | fn T U =>
              cases hgy : Mode.get ⟨st.time, false⟩ Γ y with
              | none => simp [hgg, hgy] at hchk
              | some A =>
                simp only [hgg, hgy] at hchk
                split at hchk <;> try simp at hchk
                rename_i hAT; simp at hAT; subst A
                obtain ⟨hgy0, hliveT⟩ := mode_get_top hgy
                obtain ⟨vg, hvg, hgok⟩ := he g (.fn T U) (mode_get_top hgg).1
                obtain ⟨vy, hvy, hyok⟩ := he y T hgy0
                have hL0 := liveSetOk_lsem st.time hh
                have hyin0 := valInL_lsem hyok (semLive_of_liveIn hliveT)
                cases hgok with
                | @clo body cap T₀ U₀ C _ _ f₀ hfn hC hcap hb =>
                  cases hfn with
                  | fn hTT₀ hU₀U =>
                    obtain ⟨sub₀, tb₀, hsub₀, hbchk⟩ := hb
                    have hcapin := valInL_lsem hcap (semLive_of_allStatic st.time hC)
                    have hframe := envBody_frame (hyok.weaken_sub _ hTT₀) hyin0 hcap hcapin
                    simp only [exec, hvg, hvy]
                    cases hbres : chk f₀ sub₀ ⟨tb₀, true⟩ (Ctx.frame T₀ C) body with
                    | none => simp [hbres] at hbchk
                    | some bres =>
                      have ⟨hbns, hbdone⟩ := exec_body_ok f hsub₀ hbres hh hL0 hframe
                      cases hexec : exec f st (Env.frame vy cap) body with
                      | halted | outOfFuel => rfl
                      | dangling | wrong => simp [hexec, Res.isStuck] at hbns
                      | done st1 env1 =>
                        obtain ⟨ht1, htys1, _, Γb, hbopt, hext1, _, hh1, _, he1⟩ := hbdone st1 env1 hexec
                        cases bres with
                        | none => nomatch hbopt
                        | some Γb' =>
                          cases hbopt; simp [hbres] at hbchk
                          obtain ⟨vr, hvr, hvru, _⟩ := he1 2 U₀ hbchk
                          simp only [hvr]
                          have hchk1 : chk cf sub ⟨st1.time, false⟩ (Γ.set x U) rest = some res := by
                            rw [ht1]; exact hchk
                          exact ih hsub hchk1 hh1 ((he.mono hext1).set x vr U (hvru.weaken_sub _ hU₀U))
                  | @fnFn A₀ B₀ hAB =>
                    obtain ⟨sub₀, tb₀, hsub₀, hbchk⟩ := hb
                    have hyStat := hyok.as_cloStatic hAB.symm rfl
                    have hframe := envStatic_frame (T₀ := .fn A₀ .unit) hyStat hcap hC
                    simp only [exec, hvg, hvy]
                    cases hbres : chk f₀ sub₀ ⟨tb₀, true⟩ (Ctx.frame (.fn A₀ .unit) C) body with
                    | none => simp [hbres] at hbchk
                    | some bres =>
                      have ⟨hbns, hbdone⟩ := exec_static_ok f hsub₀ hbres hh hframe
                      cases hexec : exec f st (Env.frame vy cap) body with
                      | halted | outOfFuel => rfl
                      | dangling | wrong => simp [hexec, Res.isStuck] at hbns
                      | done st1 env1 =>
                        obtain ⟨ht1, htys1, Γb, hbopt, hext1, hh1, _, he1⟩ := hbdone st1 env1 hexec
                        cases bres with
                        | none => nomatch hbopt
                        | some Γb' =>
                          cases hbopt; simp [hbres] at hbchk
                          obtain ⟨vr, hvr, hvru⟩ := he1 2 .unit hbchk
                          simp only [hvr]
                          have hchk1 : chk cf sub ⟨st1.time, false⟩ (Γ.set x .unit) rest = some res := by
                            rw [ht1]; exact hchk
                          exact ih hsub hchk1 hh1 ((he.mono hext1).set x vr .unit hvru)
                | @cloStatic body cap T₀ U₀ C _ _ f₀ hfn hC hcap hb =>
                  obtain ⟨sub₀, tb₀, hsub₀, hbchk⟩ := hb
                  obtain ⟨hyStat, hUsub⟩ := cloStatic_call_step hfn hyok
                  have hframe := envStatic_frame hyStat hcap hC
                  simp only [exec, hvg, hvy]
                  cases hbres : chk f₀ sub₀ ⟨tb₀, true⟩ (Ctx.frame T₀ C) body with
                  | none => simp [hbres] at hbchk
                  | some bres =>
                    have ⟨hbns, hbdone⟩ := exec_static_ok f hsub₀ hbres hh hframe
                    cases hexec : exec f st (Env.frame vy cap) body with
                    | halted | outOfFuel => rfl
                    | dangling | wrong => simp [hexec, Res.isStuck] at hbns
                    | done st1 env1 =>
                      obtain ⟨ht1, htys1, Γb, hbopt, hext1, hh1, _, he1⟩ := hbdone st1 env1 hexec
                      cases bres with
                      | none => nomatch hbopt
                      | some Γb' =>
                        cases hbopt; simp [hbres] at hbchk
                        obtain ⟨vr, hvr, hvru⟩ := he1 2 U₀ hbchk
                        simp only [hvr]
                        have hchk1 : chk cf sub ⟨st1.time, false⟩ (Γ.set x U) rest = some res := by
                          rw [ht1]; exact hchk
                        exact ih hsub hchk1 hh1 ((he.mono hext1).set x vr U (hvru.weaken_sub _ hUsub))
            | _ => simp [hgg] at hchk
        | endRegion n =>
          simp only [chk, Bool.not_false, Bool.true_and, decide_eq_true_eq] at hchk
          split at hchk <;> try simp at hchk
          rename_i htn
          simp only [exec, htn, ite_true]
          exact ih hsub (st := { st with time := n + 1 }) hchk hh he
        | abort => rfl

/-- Full soundness of `MSub`. -/
theorem MSub_sound : Sound MSub := by
  rintro P ⟨sub, hsub, cfuel, hchk⟩ fuel
  simp only [Checks, Option.isSome_iff_exists] at hchk
  obtain ⟨res, hres⟩ := hchk
  have hh0 : HeapOk [] St.init.heap := ⟨rfl, fun _ _ _ h => by simp at h⟩
  have he0 : EnvTopOk [] Env.empty Ctx.empty := fun _ _ h => nomatch h
  exact exec_top_ok fuel hsub hres hh0 he0

/-! ## 4. Monotonicity and fuel stability of `chk` (refuting `Typed` for every oracle and fuel) -/

def hasEnoughFuel : Nat → List Stmt → Bool
  | 0, _ => false
  | _ + 1, [] => true
  | k + 1, .lam _ _ _ _ body :: rest => hasEnoughFuel k body && hasEnoughFuel k rest
  | k + 1, _ :: rest => hasEnoughFuel k rest

theorem chk_eq_of_hasEnoughFuel : ∀ (B : Nat) {f : Nat} (sub : Ty → Ty → Bool) (m : Mode)
    (Γ : Ctx) (P : List Stmt),
    hasEnoughFuel B P = true → B ≤ f → chk B sub m Γ P = chk f sub m Γ P := by
  intro B
  induction B with
  | zero => intros _ _ _ _ hB _; nomatch hB
  | succ k ih =>
    intro f sub m Γ P hB hle
    cases f with
    | zero => nomatch hle
    | succ f' =>
      have hle' : k ≤ f' := Nat.le_of_succ_le_succ hle
      cases P with
      | nil => rfl
      | cons s rest =>
        cases s with
        | abort => rfl
        | lam x T U c body =>
          simp only [hasEnoughFuel, Bool.and_eq_true] at hB
          have eq1 : ∀ m' Γ', chk k sub m' Γ' body = chk f' sub m' Γ' body :=
            fun m' Γ' => ih sub m' Γ' body hB.1 hle'
          have eq2 : ∀ m' Γ', chk k sub m' Γ' rest = chk f' sub m' Γ' rest :=
            fun m' Γ' => ih sub m' Γ' rest hB.2 hle'
          simp only [chk, eq1, eq2]
        | _ =>
          have eq2 : ∀ m' Γ', chk k sub m' Γ' rest = chk f' sub m' Γ' rest :=
            fun m' Γ' => ih sub m' Γ' rest hB hle'
          simp only [chk, eq2]

theorem chk_fuel_irrel : ∀ (f₁ : Nat) {f₂ : Nat} (sub : Ty → Ty → Bool) (m : Mode)
    (Γ : Ctx) (P : List Stmt) {res : Option Ctx},
    chk f₁ sub m Γ P = some res → f₁ ≤ f₂ → chk f₂ sub m Γ P = some res := by
  intro f₁
  induction f₁ with
  | zero => intros _ _ _ _ _ _ h _; nomatch h
  | succ k ih =>
    intro f₂ sub m Γ P res h hle
    cases f₂ with
    | zero => omega
    | succ f' =>
      have hle' : k ≤ f' := Nat.le_of_succ_le_succ hle
      cases P with
      | nil => exact h
      | cons s rest =>
        cases s with
        | abort => exact h
        | lam x T U c body =>
          revert h; simp only [chk]
          cases m.get Γ c with
          | none => exact id
          | some C =>
            dsimp only
            split
            · cases hb : chk k sub ⟨m.time, true⟩ (Ctx.frame T C) body with
              | none => intro h; nomatch h
              | some bres =>
                rw [ih sub ⟨m.time, true⟩ (Ctx.frame T C) body hb hle']
                cases bres with
                | none => dsimp only; intro h; exact ih sub m _ rest h hle'
                | some Γb =>
                  dsimp only
                  split
                  · intro h; exact ih sub m _ rest h hle'
                  · exact id
            · exact id
        | _ =>
          revert h; simp only [chk]
          repeat split
          all_goals first | exact id | (intro h; exact ih sub _ _ rest h hle')

theorem chk_mono_sub : ∀ (fuel : Nat) {sub₁ sub₂ : Ty → Ty → Bool}
    (hsub : ∀ X Y, sub₁ X Y = true → sub₂ X Y = true)
    (m : Mode) (Γ : Ctx) (P : List Stmt) {res : Option Ctx},
    chk fuel sub₁ m Γ P = some res → chk fuel sub₂ m Γ P = some res := by
  intro fuel
  induction fuel with
  | zero => intros _ _ _ _ _ _ _ h; nomatch h
  | succ k ih =>
    intro sub₁ sub₂ hsub m Γ P res h
    cases P with
    | nil => exact h
    | cons s rest =>
      cases s with
      | abort => exact h
      | copy x y T =>
        revert h; simp only [chk]
        cases m.get Γ y with
        | none => exact id
        | some S =>
          dsimp only
          intro h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            have hc2 : (T.closed && T.liveIn m.lv && sub₂ S T) = true := by
              simp [hc.1.1, hc.1.2, hsub S T hc.2]
            simp only [hc2, ite_true]
            exact ih hsub m _ rest h
          · nomatch h
      | lam x T U c body =>
        revert h; simp only [chk]
        cases m.get Γ c with
        | none => exact id
        | some C =>
          dsimp only
          split
          · cases hb : chk k sub₁ ⟨m.time, true⟩ (Ctx.frame T C) body with
            | none => intro h; nomatch h
            | some bres =>
              rw [ih hsub ⟨m.time, true⟩ (Ctx.frame T C) body hb]
              cases bres with
              | none => dsimp only; intro h; exact ih hsub m _ rest h
              | some Γb =>
                dsimp only
                split
                · intro h; exact ih hsub m _ rest h
                · exact id
          · exact id
      | _ =>
        revert h; simp only [chk]
        repeat split
        all_goals first | exact id | (intro h; exact ih hsub _ _ rest h)

theorem not_typed_of_checks_false {tbl : Table} {P : List Stmt} (B : Nat)
    (hB : hasEnoughFuel B P = true) (hfalse : Checks (subAlg tbl true) B P = false) :
    ¬ Typed (SubGen tbl NoAx) P := by
  rintro ⟨sub, hsub, fuel, hchk⟩
  simp only [Checks, Option.isSome_iff_exists] at hchk
  obtain ⟨res, hres⟩ := hchk
  have hsub' : ∀ X Y, sub X Y = true → subAlg tbl true X Y = true :=
    fun X Y h => subAlg_of_subGen (hsub X Y h)
  have hres' := chk_mono_sub fuel hsub' ⟨0, false⟩ Ctx.empty P hres
  have hresB : chk B (subAlg tbl true) ⟨0, false⟩ Ctx.empty P = some res := by
    by_cases hle : fuel ≤ B
    · exact chk_fuel_irrel fuel _ _ _ P hres' hle
    · have hge : B ≤ fuel := by omega
      rw [chk_eq_of_hasEnoughFuel B _ _ _ P hB hge]; exact hres'
  simp [Checks, hresB] at hfalse
end Toy.Variance
