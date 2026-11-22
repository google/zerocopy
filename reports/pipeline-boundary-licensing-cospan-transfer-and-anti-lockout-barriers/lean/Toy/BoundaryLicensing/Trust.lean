set_option autoImplicit false

namespace Toy.BoundaryLicensing

/-! ## Positive TCB Allowlist vs. Finite Denylist & Certificate Trust-Triple Independence -/

universe u v w

/-- Extensible supply of axiom/trust-assumption identifiers. -/
abbrev AxiomId := Nat

/-- Positive allowlist check: accepts `used` iff every axiom in `used` belongs to `allow`. -/
def allowlistAccepts (allow : List AxiomId) (used : List AxiomId) : Bool :=
  used.all (fun a => allow.contains a)

/-- Finite denylist check: accepts `used` iff no axiom in `used` belongs to `deny`. -/
def denylistAccepts (deny : List AxiomId) (used : List AxiomId) : Bool :=
  used.all (fun a => !deny.contains a)

/-- Semantic TCB policy: every used axiom belongs to the declared allowlist `allow`. -/
def OnlyDeclaredAxioms (allow : List AxiomId) (used : List AxiomId) : Prop :=
  ∀ a ∈ used, a ∈ allow

/-- Explicit fresh axiom constructor strictly exceeding every identifier in `allow ++ deny`. -/
def freshAxiomOutside (allow deny : List AxiomId) : AxiomId :=
  (allow ++ deny).foldl Nat.max 0 + 1

private theorem foldl_max_ge_acc (l : List Nat) (acc : Nat) :
    acc ≤ l.foldl Nat.max acc := by
  induction l generalizing acc with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left acc x) (ih (Nat.max acc x))

private theorem le_foldl_max_of_mem {l : List Nat} {a : Nat} (acc : Nat) (h : a ∈ l) :
    a ≤ l.foldl Nat.max acc := by
  induction l generalizing acc with
  | nil => cases h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | hxs
    · exact Nat.le_trans (Nat.le_max_right acc a) (foldl_max_ge_acc xs (Nat.max acc a))
    · exact ih (Nat.max acc x) hxs

theorem freshAxiomOutside_not_mem (allow deny : List AxiomId) :
    freshAxiomOutside allow deny ∉ allow ∧ freshAxiomOutside allow deny ∉ deny := by
  refine ⟨?_, ?_⟩
  · intro h
    have hle := le_foldl_max_of_mem 0 (List.mem_append_left deny h)
    unfold freshAxiomOutside at hle
    omega
  · intro h
    have hle := le_foldl_max_of_mem 0 (List.mem_append_right allow h)
    unfold freshAxiomOutside at hle
    omega

/-- Exactness of positive allowlist checking. -/
theorem allowlistAccepts_iff_onlyDeclaredAxioms (allow used : List AxiomId) :
    allowlistAccepts allow used = true ↔ OnlyDeclaredAxioms allow used := by
  simp [allowlistAccepts, OnlyDeclaredAxioms]

/-- Explicit fail-open separation: for every finite `allow` and finite `deny`,
`freshAxiomOutside allow deny` is undeclared (`∉ allow`), rejected by `allowlistAccepts allow`,
and accepted by `denylistAccepts deny`. -/
theorem freshAxiomOutside_accepted_by_denylist_rejected_by_allowlist
    (allow deny : List AxiomId) :
    let a := freshAxiomOutside allow deny
    ¬ OnlyDeclaredAxioms allow [a] ∧
    allowlistAccepts allow [a] = false ∧
    denylistAccepts deny [a] = true := by
  intro a
  obtain ⟨hna, hnd⟩ := freshAxiomOutside_not_mem allow deny
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact hna (h a (List.mem_singleton.2 rfl))
  · cases h : allowlistAccepts allow [a]
    · rfl
    · have hdecl := (allowlistAccepts_iff_onlyDeclaredAxioms allow [a]).1 h
      exact False.elim (hna (hdecl a (List.mem_singleton.2 rfl)))
  · simp [denylistAccepts]
    exact hnd

/-- Impossibility of enforcing any finite allowlist over `AxiomId` with a finite denylist. -/
theorem no_finite_denylist_enforces_allowlist (allow : List AxiomId) :
    ¬ ∃ deny : List AxiomId, ∀ used : List AxiomId,
        denylistAccepts deny used = true → OnlyDeclaredAxioms allow used := by
  rintro ⟨deny, hsound⟩
  have h := freshAxiomOutside_accepted_by_denylist_rejected_by_allowlist allow deny
  exact h.1 (hsound [freshAxiomOutside allow deny] h.2.2)

/-- Positive control for `no_finite_denylist_enforces_allowlist`: over a finite closed universe
`univ` (`OnlyDeclaredAxioms univ used`), the complement denylist `univ.filter (!allow.contains ·)`
soundly enforces `OnlyDeclaredAxioms allow used`. -/
theorem denylist_complement_sound_on_closed_universe (univ allow used : List AxiomId)
    (hclosed : OnlyDeclaredAxioms univ used)
    (hacc : denylistAccepts (univ.filter (fun a => !allow.contains a)) used = true) :
    OnlyDeclaredAxioms allow used := by
  intro a ha
  have hu : a ∈ univ := hclosed a ha
  simp [denylistAccepts] at hacc
  rcases hacc a ha with hnu | hal
  · exact False.elim (hnu hu)
  · exact hal

/-! ### Certificate/Rule-Table/Statement-Table Trust Triple & Mutual Independence -/

/-- Abstract universe-polymorphic certificate verifier parameterized by rule derivability,
semantic validity, decidable proof checking, and an official statement table. -/
structure CertVerifier (Stmt : Type u) (Rule : Type v) (Cert : Type w) where
  derivable : Rule → Stmt → Prop
  valid : Stmt → Prop
  check : Rule → Cert → Stmt → Bool
  official : Nat → Option Stmt

/-- Checker faithfulness: accepted certificates witness rule derivability. -/
def CertFaithful {Stmt : Type u} {Rule : Type v} {Cert : Type w}
    (V : CertVerifier Stmt Rule Cert) (R : Rule) : Prop :=
  ∀ c φ, V.check R c φ = true → V.derivable R φ

/-- Semantic soundness of rule table `R`: every `R`-derivable statement is semantically valid. -/
def CertSemSound {Stmt : Type u} {Rule : Type v} {Cert : Type w}
    (V : CertVerifier Stmt Rule Cert) (R : Rule) : Prop :=
  ∀ φ, V.derivable R φ → V.valid φ

/-- Statement-table pinning at `name`: shipped and official tables resolve `name` to the same statement. -/
def TablePinned {Stmt : Type u} (official shipped : Nat → Option Stmt) (name : Nat) : Prop :=
  ∃ φ, official name = some φ ∧ shipped name = some φ

/-- Named-theorem check resolving `name` in `shipped` before invoking `V.check`. -/
def acceptsNamed {Stmt : Type u} {Rule : Type v} {Cert : Type w}
    (V : CertVerifier Stmt Rule Cert) (R : Rule) (shipped : Nat → Option Stmt)
    (c : Cert) (name : Nat) : Bool :=
  match shipped name with
  | some φ => V.check R c φ
  | none => false

/-- End-to-end trust-triple soundness: `CertFaithful`, `CertSemSound`, and `TablePinned`
together ensure every accepted `name` has a valid official statement. -/
theorem cert_trust_triple_sound {Stmt : Type u} {Rule : Type v} {Cert : Type w}
    (V : CertVerifier Stmt Rule Cert) (R : Rule) (shipped : Nat → Option Stmt)
    (c : Cert) (name : Nat)
    (hfaith : CertFaithful V R)
    (hsem : CertSemSound V R)
    (hpin : TablePinned V.official shipped name)
    (hacc : acceptsNamed V R shipped c name = true) :
    ∃ φ, V.official name = some φ ∧ V.valid φ := by
  rcases hpin with ⟨φ, hoff, hship⟩
  simp only [acceptsNamed, hship] at hacc
  exact ⟨φ, hoff, hsem φ (hfaith c φ hacc)⟩

/-- Concrete sound certificate verifier over `Bool` statements (`true` valid, `false` invalid). -/
def boolHonestVerifier : CertVerifier Bool Bool Unit where
  derivable := fun r φ => if r then φ = true else True
  valid := fun φ => φ = true
  check := fun r _ φ => if r then φ else true
  official := fun n => if n == 0 then some false else some true

/-- Unfaithful verifier that accepts every statement regardless of rules. -/
def boolUnfaithfulVerifier : CertVerifier Bool Unit Unit where
  derivable := fun _ φ => φ = true
  valid := fun φ => φ = true
  check := fun _ _ _ => true
  official := fun _ => some false

/-- Tightness & independence counterexample 1 (`CertFaithful` dropped): `CertSemSound` and `TablePinned`
hold, `acceptsNamed = true`, yet the official statement at `0` is invalid. -/
theorem cex_trust_triple_without_faithful :
    CertSemSound boolUnfaithfulVerifier () ∧
    TablePinned boolUnfaithfulVerifier.official boolUnfaithfulVerifier.official 0 ∧
    acceptsNamed boolUnfaithfulVerifier () boolUnfaithfulVerifier.official () 0 = true ∧
    ¬ ∃ φ, boolUnfaithfulVerifier.official 0 = some φ ∧ boolUnfaithfulVerifier.valid φ := by
  refine ⟨fun _ h => h, ⟨false, rfl, rfl⟩, rfl, ?_⟩
  rintro ⟨φ, hoff, hval⟩
  simp [boolUnfaithfulVerifier] at hoff hval
  subst hoff
  cases hval

/-- Tightness & independence counterexample 2 (`CertSemSound` dropped): `CertFaithful` and `TablePinned`
hold for unsound rule flag `false`, `acceptsNamed = true`, yet the official statement at `0` is invalid. -/
theorem cex_trust_triple_without_semSound :
    CertFaithful boolHonestVerifier false ∧
    TablePinned boolHonestVerifier.official boolHonestVerifier.official 0 ∧
    acceptsNamed boolHonestVerifier false boolHonestVerifier.official () 0 = true ∧
    ¬ ∃ φ, boolHonestVerifier.official 0 = some φ ∧ boolHonestVerifier.valid φ := by
  refine ⟨fun _ _ _ => trivial, ⟨false, rfl, rfl⟩, rfl, ?_⟩
  rintro ⟨φ, hoff, hval⟩
  simp [boolHonestVerifier] at hoff hval
  subst hoff
  cases hval

/-- Tightness & independence counterexample 3 (`TablePinned` dropped): `CertFaithful` and `CertSemSound`
hold for sound rule flag `true`, `shipped` remaps `0 ↦ some true` while `official 0 = some false`. -/
theorem cex_trust_triple_without_pinned :
    let shipped : Nat → Option Bool := fun _ => some true
    CertFaithful boolHonestVerifier true ∧
    CertSemSound boolHonestVerifier true ∧
    acceptsNamed boolHonestVerifier true shipped () 0 = true ∧
    ¬ ∃ φ, boolHonestVerifier.official 0 = some φ ∧ boolHonestVerifier.valid φ := by
  intro shipped
  refine ⟨fun _ φ h => by simpa [boolHonestVerifier] using h,
    fun _ h => by simpa [boolHonestVerifier] using h, rfl, ?_⟩
  rintro ⟨φ, hoff, hval⟩
  simp [boolHonestVerifier] at hoff hval
  subst hoff
  cases hval

/-- Tightness counterexample 4 (`hacc` dropped): `CertFaithful`, `CertSemSound`, and `TablePinned` hold,
the checker rejects `0` (`acceptsNamed = false`), and the official statement at `0` is invalid. -/
theorem cex_trust_triple_without_accepted :
    CertFaithful boolHonestVerifier true ∧
    CertSemSound boolHonestVerifier true ∧
    TablePinned boolHonestVerifier.official boolHonestVerifier.official 0 ∧
    ¬ ∃ φ, boolHonestVerifier.official 0 = some φ ∧ boolHonestVerifier.valid φ := by
  refine ⟨fun _ φ h => by simpa [boolHonestVerifier] using h,
    fun _ h => by simpa [boolHonestVerifier] using h, ⟨false, rfl, rfl⟩, ?_⟩
  rintro ⟨φ, hoff, hval⟩
  simp [boolHonestVerifier] at hoff hval
  subst hoff
  cases hval

/-! ### Proved Positive and Negative Examples & Non-Vacuity Witnesses for `Trust.lean` -/

theorem allowlistAccepts_pos : allowlistAccepts [0, 1] [1, 0] = true := rfl
theorem allowlistAccepts_neg : allowlistAccepts [0, 1] [1, 2] = false := rfl

theorem denylistAccepts_pos : denylistAccepts [2, 3] [0, 1] = true := rfl
theorem denylistAccepts_neg : denylistAccepts [2, 3] [0, 2] = false := rfl

theorem onlyDeclaredAxioms_pos : OnlyDeclaredAxioms [0, 1] [1] :=
  (allowlistAccepts_iff_onlyDeclaredAxioms [0, 1] [1]).1 rfl

theorem onlyDeclaredAxioms_neg : ¬ OnlyDeclaredAxioms [0, 1] [2] := by
  rw [← allowlistAccepts_iff_onlyDeclaredAxioms]
  decide

theorem freshAxiomOutside_pos : freshAxiomOutside [1, 4] [2] = 5 := rfl
theorem freshAxiomOutside_neg : freshAxiomOutside [1, 4] [2] ≠ 4 := by decide

/-- Unified non-vacuity witness for allowlist exactness and fresh-axiom denylist separation. -/
theorem nonvacuity_allowlist_vs_denylist :
    allowlistAccepts [0, 1] [1, 0] = true ∧
    OnlyDeclaredAxioms [0, 1] [1, 0] ∧
    freshAxiomOutside [1, 4] [2] = 5 ∧
    5 ∉ ([1, 4] : List AxiomId) ∧
    5 ∉ ([2] : List AxiomId) ∧
    denylistAccepts [2] [5] = true ∧
    allowlistAccepts [1, 4] [5] = false := by
  refine ⟨rfl, (allowlistAccepts_iff_onlyDeclaredAxioms [0, 1] [1, 0]).1 rfl, ?_⟩
  decide

theorem certFaithful_pos : CertFaithful boolHonestVerifier true :=
  fun _ φ h => by simpa [boolHonestVerifier] using h

theorem certFaithful_neg : ¬ CertFaithful boolUnfaithfulVerifier () := by
  intro h
  exact Bool.noConfusion (h () false rfl)

theorem certSemSound_pos : CertSemSound boolHonestVerifier true :=
  fun _ h => by simpa [boolHonestVerifier] using h

theorem certSemSound_neg : ¬ CertSemSound boolHonestVerifier false := by
  intro h
  exact Bool.noConfusion (h false trivial)

theorem tablePinned_pos :
    TablePinned boolHonestVerifier.official boolHonestVerifier.official 1 :=
  ⟨true, rfl, rfl⟩

theorem tablePinned_neg :
    ¬ TablePinned boolHonestVerifier.official (fun _ => some true) 0 := by
  rintro ⟨φ, h1, h2⟩
  simp [boolHonestVerifier] at h1 h2
  subst h1
  cases h2

theorem acceptsNamed_pos :
    acceptsNamed boolHonestVerifier true boolHonestVerifier.official () 1 = true := rfl

theorem acceptsNamed_neg :
    acceptsNamed boolHonestVerifier true boolHonestVerifier.official () 0 = false := rfl

/-- Non-vacuity witness for `cert_trust_triple_sound`. -/
theorem nonvacuity_cert_trust_triple :
    CertFaithful boolHonestVerifier true ∧
    CertSemSound boolHonestVerifier true ∧
    TablePinned boolHonestVerifier.official boolHonestVerifier.official 1 ∧
    acceptsNamed boolHonestVerifier true boolHonestVerifier.official () 1 = true :=
  ⟨certFaithful_pos, certSemSound_pos, tablePinned_pos, rfl⟩

end Toy.BoundaryLicensing
