import ToyUnwindCap.Basic

/-!
# Main results: classification soundness, terminate pads, strategy and drop-glue mixing,
# mixed backends (program level)
-/

namespace Toy.UnwindCap

/-! ## Auxiliary lemmas -/

theorem ite_pos {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

theorem mem_prependRuns {t : List Event} {rs : List Run} {r : Run} (h : r ∈ prependRuns t rs) :
    ∃ r' ∈ rs, r = (t ++ r'.1, r'.2) := by
  unfold prependRuns at h
  obtain ⟨r', h1, h2⟩ := List.mem_map.1 h
  exact ⟨r', h1, h2.symm⟩

/-- Body invariant behind the soundness theorem: if every callee run is free of `ub` and
unwinds only out of a function classified as possibly unwinding by its own crate, the same
holds for the runs of any statement list drawn from the body of a non-foreign function `g`,
with respect to `g`'s own classification. -/
theorem execBody_good (cu : Prec) (p : Prog) (callee : Nat → List Run) (g : Nat)
    (hcallee : ∀ f, ∀ r ∈ callee f, r.2 ≠ .ub ∧ (r.2 = .unwind → p.selfMay cu f = true))
    (hg : (p.fn g).info.foreign = false) (henf : Enforced cu p) (hsa : SiteAgreement cu p) :
    ∀ l : List Stmt, (∀ s ∈ l, s ∈ (p.fn g).body) →
      ∀ r ∈ execBody cu p callee g l, r.2 ≠ .ub ∧ (r.2 = .unwind → p.selfMay cu g = true) := by
  intro l
  induction l with
  | nil =>
    intro _ r hr
    simp only [execBody, List.mem_singleton] at hr
    subst hr
    exact ⟨by simp, by simp⟩
  | cons s rest ih =>
    intro hsub r hr
    have hrest : ∀ s ∈ rest, s ∈ (p.fn g).body := fun s hs => hsub s (List.mem_cons_of_mem _ hs)
    have hs : s ∈ (p.fn g).body := hsub s List.mem_cons_self
    -- an unwind that escapes `g` from a statement with a non-stopping action
    have hesc : ∀ act : Action, act.Stops = false →
        (p.selfMay cu g = false → act.Stops = true) → p.selfMay cu g = true := by
      intro act hst himp
      cases hsg : p.selfMay cu g
      · have := himp hsg
        rw [hst] at this
        exact absurd this (by decide)
      · rfl
    cases s with
    | raise act =>
      simp only [execBody] at hr
      cases hh : p.handler with
      | abort =>
        rw [hh] at hr
        simp only [List.mem_singleton] at hr
        subst hr
        exact ⟨by simp, by simp⟩
      | unwind =>
        rw [hh] at hr
        cases act with
        | terminate =>
          simp only [onUnwind, List.mem_singleton] at hr
          subst hr
          exact ⟨by simp, by simp⟩
        | catchPad =>
          simp only [onUnwind] at hr
          obtain ⟨r', hr', rfl⟩ := mem_prependRuns hr
          exact ih hrest r' hr'
        | none =>
          simp only [onUnwind, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hr
          subst hr
          refine ⟨by simp, fun _ => ?_⟩
          exact hesc .none rfl (fun hsg => (henf g hg hsg).1 hh .none hs)
        | cleanup ds =>
          simp only [onUnwind, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hr
          subst hr
          refine ⟨by simp, fun _ => ?_⟩
          exact hesc (.cleanup ds) rfl (fun hsg => (henf g hg hsg).1 hh (.cleanup ds) hs)
    | call f act =>
      simp only [execBody, List.mem_flatMap] at hr
      obtain ⟨⟨t0, o0⟩, h0, hr⟩ := hr
      have hc := hcallee f _ h0
      cases o0 with
      | ret =>
        obtain ⟨r', hr', rfl⟩ := mem_prependRuns hr
        exact ih hrest r' hr'
      | unwind =>
        obtain ⟨r', hr', rfl⟩ := mem_prependRuns hr
        have hfm : p.selfMay cu f = true := hc.2 rfl
        have hview : act.Stops = false → p.viewMay cu g f = true := by
          intro hst
          cases hv : p.viewMay cu g f
          · have := hsa g f act hg hs hst hv
            rw [hfm] at this
            exact absurd this (by decide)
          · rfl
        cases act with
        | terminate =>
          simp only [onUnwind, List.mem_singleton] at hr'
          subst hr'
          exact ⟨by simp, by simp⟩
        | catchPad =>
          simp only [onUnwind] at hr'
          obtain ⟨r'', hr'', rfl⟩ := mem_prependRuns hr'
          exact ih hrest r'' hr''
        | none =>
          have hv := hview rfl
          simp only [onUnwind, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            List.mem_singleton] at hr'
          subst hr'
          refine ⟨by simp, fun _ => ?_⟩
          exact hesc .none rfl (fun hsg => (henf g hg hsg).2 f .none hs hv)
        | cleanup ds =>
          have hv := hview rfl
          simp only [onUnwind, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            List.mem_singleton] at hr'
          subst hr'
          refine ⟨by simp, fun _ => ?_⟩
          exact hesc (.cleanup ds) rfl (fun hsg => (henf g hg hsg).2 f (.cleanup ds) hs hv)
      | abort =>
        simp only [List.mem_singleton] at hr
        subst hr
        exact ⟨by simp, by simp⟩
      | ub => exact absurd rfl hc.1

/-- Fuel-indexed form of the soundness invariant. -/
theorem runFn_good (cu : Prec) (p : Prog) (henf : Enforced cu p) (hfc : ForeignCovered cu p)
    (hsa : SiteAgreement cu p) :
    ∀ n f, ∀ r ∈ runFn cu p n f, r.2 ≠ .ub ∧ (r.2 = .unwind → p.selfMay cu f = true) := by
  intro n
  induction n with
  | zero => intro f r hr; simp [runFn] at hr
  | succ n ih =>
    intro f r hr
    unfold runFn at hr
    by_cases hfor : (p.fn f).info.foreign = true
    · rw [ite_pos hfor] at hr
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨by simp, by simp⟩
      · by_cases hth : (p.fn f).throws = true
        · rw [ite_pos hth, List.mem_singleton] at hr
          subst hr
          have := hfc f hfor hth
          simp [boundary, this]
        · rw [ite_neg hth] at hr
          simp at hr
    · rw [ite_neg hfor] at hr
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      have hfor' : (p.fn f).info.foreign = false := by simpa using hfor
      have h := execBody_good cu p (runFn cu p n) f ih hfor' henf hsa _ (fun s hs => hs) r' hr'
      obtain ⟨t', o'⟩ := r'
      cases o' with
      | unwind =>
        have hm := h.2 rfl
        simp [boundary, hm]
      | ret => simp [boundary]
      | abort => simp [boundary]
      | ub => exact absurd rfl h.1

/-- The soundness invariant, for every finite run: no `ub`, and an unwind leaves only a function
that its own crate classifies as possibly unwinding. -/
theorem exec_inv_of_enforced (cu : Prec) (p : Prog) (henf : Enforced cu p)
    (hfc : ForeignCovered cu p) (hsa : SiteAgreement cu p) {f : Nat} {t : List Event}
    {o : Outcome} (h : Exec cu p f t o) : o ≠ .ub ∧ (o = .unwind → p.selfMay cu f = true) := by
  obtain ⟨n, hn⟩ := h
  exact runFn_good cu p henf hfc hsa n f _ hn

/-! ## Item 1: soundness of a precedence function, given enforcement -/

/-- **Soundness given enforcement.** For every precedence function `cu` and every program `p`:
if `p` satisfies `Enforced cu p`, `ForeignCovered cu p` and `SiteAgreement cu p`, then no
finite run of any function of `p` has outcome `ub`. -/
theorem noUB_of_enforced_of_foreignCovered_of_siteAgreement (cu : Prec) (p : Prog)
    (henf : Enforced cu p) (hfc : ForeignCovered cu p) (hsa : SiteAgreement cu p) :
    ∀ f t o, Exec cu p f t o → o ≠ .ub := by
  intro f t o h
  exact (exec_inv_of_enforced cu p henf hfc hsa h).1

/-- `stdCanUnwind` classifies a foreign `cUnwind` function without the never-unwind attribute
that is not drop glue as possibly unwinding, whatever the classifying crate's settings. -/
theorem stdCanUnwind_foreign_cUnwind (c : CrateCfg) (i : FnInfo) (h1 : i.foreign = true)
    (h2 : i.abi = .cUnwind) (h3 : i.neverUnwind = false) (h4 : i.dropGlue = false) :
    stdCanUnwind c i = true := by
  simp [stdCanUnwind, stdOrder, evalRules, ruleAttr, ruleAbortNonForeign, ruleDropGlue, ruleAbi,
    abiCanUnwind, h1, h2, h3, h4]

/-- **The standard order covers honest foreign code.** In every program satisfying
`ForeignHonest` and `ForeignNotGlue`, `stdCanUnwind` classifies every foreign function that may
unwind as possibly unwinding. -/
theorem foreignCovered_std_of_foreignHonest_of_foreignNotGlue (p : Prog)
    (hh : ForeignHonest p) (hng : ForeignNotGlue p) : ForeignCovered stdCanUnwind p := by
  intro f hfor hth
  obtain ⟨habi, hnu⟩ := hh f hfor hth
  exact stdCanUnwind_foreign_cUnwind _ _ hfor habi hnu (hng f hfor)

/-- **Characterization of foreign soundness.** A precedence function `cu` satisfies
`PrecForeignSound cu` iff it returns `true` on every foreign `cUnwind` function without the
never-unwind attribute that is not drop glue, for every classifying crate. -/
theorem precForeignSound_iff (cu : Prec) :
    PrecForeignSound cu ↔
      ∀ c i, i.foreign = true → i.abi = .cUnwind → i.neverUnwind = false → i.dropGlue = false →
        cu c i = true := by
  constructor
  · intro h c i h1 h2 h3 h4
    let p : Prog := ⟨[c], [⟨i, 0, [], true⟩], .unwind⟩
    have hh : ForeignHonest p := by
      intro f hf _
      cases f with
      | zero => exact ⟨h2, h3⟩
      | succ f => simp [p, Prog.fn, FnDef.dummy] at hf
    have hng : ForeignNotGlue p := by
      intro f hf
      cases f with
      | zero => exact h4
      | succ f => simp [p, Prog.fn, FnDef.dummy] at hf
    have := h p hh hng 0 h1 rfl
    simpa [Prog.selfMay, Prog.crateOf, Prog.fn, p] using this
  · intro h p hh hng f hfor hth
    obtain ⟨habi, hnu⟩ := hh f hfor hth
    exact h _ _ hfor habi hnu (hng f hfor)

/-! ## Item 1: rule order -/

/-- Settings of a crate with the `abort` strategy and panic-in-drop `unwind`. -/
def abortCfg : CrateCfg := ⟨.abort, .unwind⟩

/-- Static facts of a Rust-defined `extern "C-unwind"` function (`cUnwind` ABI, not foreign). -/
def rustDefinedCUnwind : FnInfo := ⟨.cUnwind, false, false, false⟩

/-- **Two foreign-sound orders that differ.** `stdCanUnwind` and `abiFirstCanUnwind` both
satisfy `PrecForeignSound`; every "non-unwinding" verdict of `abiFirstCanUnwind` is also a
verdict of `stdCanUnwind`; and on `rustDefinedCUnwind` classified from `abortCfg` the standard
order returns `false` while the ABI-first order returns `true`. -/
theorem std_and_abiFirst_foreignSound_but_differ :
    PrecForeignSound stdCanUnwind ∧ PrecForeignSound abiFirstCanUnwind ∧
    (∀ c i, abiFirstCanUnwind c i = false → stdCanUnwind c i = false) ∧
    stdCanUnwind abortCfg rustDefinedCUnwind = false ∧
    abiFirstCanUnwind abortCfg rustDefinedCUnwind = true := by
  refine ⟨(precForeignSound_iff _).2 (fun c i h1 h2 h3 h4 =>
      stdCanUnwind_foreign_cUnwind c i h1 h2 h3 h4), (precForeignSound_iff _).2 ?_, ?_,
    by decide, by decide⟩
  · intro c i _ h2 h3 _
    simp [abiFirstCanUnwind, abiFirstOrder, evalRules, ruleAttr, ruleAbi, abiCanUnwind, h2, h3]
  · intro c i
    obtain ⟨cp, cd⟩ := c
    obtain ⟨abi, fo, nu, dg⟩ := i
    cases cp <;> cases cd <;> cases abi <;> cases fo <;> cases nu <;> cases dg <;> decide

/-- **The abort-strategy rule without the foreign check is unsound.** `abortAllCanUnwind` does
not satisfy `PrecForeignSound`. -/
theorem abortAllCanUnwind_not_foreignSound : ¬ PrecForeignSound abortAllCanUnwind := by
  intro h
  have := (precForeignSound_iff _).1 h abortCfg ⟨.cUnwind, true, false, false⟩ rfl rfl rfl rfl
  exact absurd this (by decide)

/-! ## Item 2: terminate-pad placement by the toy codegen -/

theorem insertPads_fn (cu : Prec) (p : Prog) (g : Nat) :
    (insertPads cu p).fn g = padFn cu p g (p.fn g) := by
  simp only [Prog.fn, insertPads, List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  cases h : p.fns[g]? with
  | none => simp [padFn, FnDef.dummy]
  | some d => simp

theorem insertPads_crateOf (cu : Prec) (p : Prog) (g : Nat) :
    (insertPads cu p).crateOf g = p.crateOf g := by
  simp only [Prog.crateOf, insertPads_fn]
  unfold padFn
  split <;> rfl

theorem insertPads_info (cu : Prec) (p : Prog) (g : Nat) :
    ((insertPads cu p).fn g).info = (p.fn g).info := by
  rw [insertPads_fn]; unfold padFn; split <;> rfl

theorem insertPads_throws (cu : Prec) (p : Prog) (g : Nat) :
    ((insertPads cu p).fn g).throws = (p.fn g).throws := by
  rw [insertPads_fn]; unfold padFn; split <;> rfl

/-- **Where the toy codegen inserts pads.** The body of function `g` after `insertPads` is
`g`'s body with `padStmt` applied to every statement when `g` is non-foreign and classified as
non-unwinding by its own crate, and is unchanged otherwise. -/
theorem insertPads_body (cu : Prec) (p : Prog) (g : Nat) :
    ((insertPads cu p).fn g).body =
      if (p.fn g).info.foreign = false ∧ p.selfMay cu g = false then
        (p.fn g).body.map (padStmt cu p g)
      else (p.fn g).body := by
  rw [insertPads_fn]
  unfold padFn
  by_cases h : (p.fn g).info.foreign = false ∧ p.selfMay cu g = false
  · rw [ite_pos h]
    have h2 : cu (p.crates.getD (p.fn g).crate CrateCfg.dflt) (p.fn g).info = false := h.2
    have : (!(p.fn g).info.foreign && !cu (p.crates.getD (p.fn g).crate CrateCfg.dflt)
        (p.fn g).info) = true := by
      rw [h.1, h2]; rfl
    rw [ite_pos this]
  · rw [ite_neg h]
    have : ¬ (!(p.fn g).info.foreign && !cu (p.crates.getD (p.fn g).crate CrateCfg.dflt)
        (p.fn g).info) = true := by
      simp only [Prog.selfMay, Prog.crateOf] at h
      intro hc
      apply h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact hc
    rw [ite_neg this]

/-- `padStmt` on a call: the action is replaced by `terminate` if the caller's crate classifies the
callee as possibly unwinding and the action is not a stopping pad, and is left unchanged
otherwise. -/
theorem padStmt_call (cu : Prec) (p : Prog) (g f : Nat) (act : Action) :
    padStmt cu p g (.call f act) =
      .call f (if p.viewMay cu g f = true ∧ act.Stops = false then .terminate else act) := by
  simp only [padStmt]
  by_cases h : p.viewMay cu g f = true ∧ act.Stops = false
  · rw [ite_pos h, ite_pos (by simp [h.1, h.2])]
  · rw [ite_neg h]
    have : ¬ (p.viewMay cu g f && !act.Stops) = true := by
      intro hc; apply h; simpa using hc
    rw [ite_neg this]

/-- `padStmt` on a panic point: the action is replaced by `terminate` if the panic handler is
`unwind` and the action is not a stopping pad, and is left unchanged otherwise. -/
theorem padStmt_raise (cu : Prec) (p : Prog) (g : Nat) (act : Action) :
    padStmt cu p g (.raise act) =
      .raise (if p.handler = .unwind ∧ act.Stops = false then .terminate else act) := by
  simp only [padStmt]
  cases hh : p.handler <;> cases act <;> simp [Strategy.unwinds, Action.Stops]

/-- `padStmt` changes a call site exactly when the caller's crate classifies the callee as
possibly unwinding and the action does not stop unwinding. -/
theorem padStmt_call_ne_iff (cu : Prec) (p : Prog) (g f : Nat) (act : Action) :
    padStmt cu p g (.call f act) ≠ .call f act ↔
      (p.viewMay cu g f = true ∧ act.Stops = false) := by
  rw [padStmt_call]
  cases hv : p.viewMay cu g f <;> cases act <;> simp [Action.Stops]

/-- `padStmt` changes a panic point exactly when the panic handler is `unwind` and the action
does not stop unwinding. -/
theorem padStmt_raise_ne_iff (cu : Prec) (p : Prog) (g : Nat) (act : Action) :
    padStmt cu p g (.raise act) ≠ .raise act ↔
      (p.handler = .unwind ∧ act.Stops = false) := by
  rw [padStmt_raise]
  cases hh : p.handler <;> cases act <;> simp [Action.Stops]

theorem map_ne_self_iff {α : Type} (f : α → α) :
    ∀ l : List α, l.map f ≠ l ↔ ∃ x ∈ l, f x ≠ x
  | [] => by simp
  | x :: xs => by
    have ih := map_ne_self_iff f xs
    simp only [List.map_cons, ne_eq, List.cons.injEq, List.mem_cons, exists_eq_or_imp] at ih ⊢
    rw [← ih]
    constructor
    · intro h
      by_cases hx : f x = x
      · exact Or.inr (fun h2 => h ⟨hx, h2⟩)
      · exact Or.inl hx
    · rintro (h | h) ⟨h1, h2⟩
      · exact h h1
      · exact h h2

/-- **When the toy codegen changes a body.** `insertPads` changes the body of function `g` exactly
when `g` is non-foreign, its own crate classifies it as non-unwinding, and `padStmt` changes at
least one statement of its body. -/
theorem insertPads_body_ne_iff (cu : Prec) (p : Prog) (g : Nat) :
    ((insertPads cu p).fn g).body ≠ (p.fn g).body ↔
      ((p.fn g).info.foreign = false ∧ p.selfMay cu g = false) ∧
        ∃ s ∈ (p.fn g).body, padStmt cu p g s ≠ s := by
  rw [insertPads_body]
  by_cases h : (p.fn g).info.foreign = false ∧ p.selfMay cu g = false
  · rw [ite_pos h, map_ne_self_iff]
    exact ⟨fun hx => ⟨h, hx⟩, fun hx => hx.2⟩
  · rw [ite_neg h]
    exact ⟨fun hx => absurd rfl hx, fun hx => absurd hx.1 h⟩

/-- **The toy codegen enforces.** For every precedence function `cu` and program `p`,
`insertPads cu p` satisfies `Enforced cu`. -/
theorem insertPads_enforced (cu : Prec) (p : Prog) : Enforced cu (insertPads cu p) := by
  intro g hfor hself
  have hfor' : (p.fn g).info.foreign = false := by rwa [insertPads_info] at hfor
  have hself' : p.selfMay cu g = false := by
    simpa [Prog.selfMay, insertPads_crateOf, insertPads_info] using hself
  rw [insertPads_body, ite_pos ⟨hfor', hself'⟩]
  constructor
  · intro hh act h
    have hh' : p.handler = .unwind := hh
    obtain ⟨s, hs, hst⟩ := List.mem_map.1 h
    cases s with
    | raise a =>
      rw [padStmt_raise] at hst
      simp only [Stmt.raise.injEq] at hst
      subst hst
      by_cases ha : a.Stops = true
      · have : ¬ (p.handler = .unwind ∧ a.Stops = false) := by simp [ha]
        rw [ite_neg this]; exact ha
      · rw [ite_pos ⟨hh', by simpa using ha⟩]; rfl
    | call f a => simp [padStmt] at hst
  · intro f act h hv
    have hv' : p.viewMay cu g f = true := by
      simpa [Prog.viewMay, insertPads_crateOf, insertPads_info] using hv
    obtain ⟨s, hs, hst⟩ := List.mem_map.1 h
    cases s with
    | raise a => simp [padStmt] at hst
    | call f' a =>
      rw [padStmt_call] at hst
      simp only [Stmt.call.injEq] at hst
      obtain ⟨rfl, hst⟩ := hst
      subst hst
      by_cases ha : a.Stops = true
      · have : ¬ (p.viewMay cu g f' = true ∧ a.Stops = false) := by simp [ha]
        rw [ite_neg this]; exact ha
      · have : p.viewMay cu g f' = true ∧ a.Stops = false := ⟨hv', by simpa using ha⟩
        rw [ite_pos this]; rfl

/-- `insertPads` preserves `ForeignCovered`. -/
theorem insertPads_foreignCovered (cu : Prec) (p : Prog) (h : ForeignCovered cu p) :
    ForeignCovered cu (insertPads cu p) := by
  intro f hfor hth
  rw [insertPads_info] at hfor
  rw [insertPads_throws] at hth
  simpa [Prog.selfMay, insertPads_crateOf, insertPads_info] using h f hfor hth

/-- `insertPads` preserves `SiteAgreement`. -/
theorem insertPads_siteAgreement (cu : Prec) (p : Prog) (h : SiteAgreement cu p) :
    SiteAgreement cu (insertPads cu p) := by
  intro g f act hfor hmem hst hv
  rw [insertPads_info] at hfor
  have hv' : p.viewMay cu g f = false := by
    simpa [Prog.viewMay, insertPads_crateOf, insertPads_info] using hv
  have hgoal : p.selfMay cu f = false → (insertPads cu p).selfMay cu f = false := by
    intro hh; simpa [Prog.selfMay, insertPads_crateOf, insertPads_info] using hh
  apply hgoal
  rw [insertPads_body] at hmem
  split at hmem
  · obtain ⟨s, hs, hst'⟩ := List.mem_map.1 hmem
    cases s with
    | raise a => simp [padStmt] at hst'
    | call f' a =>
      rw [padStmt_call] at hst'
      simp only [Stmt.call.injEq] at hst'
      obtain ⟨rfl, hst'⟩ := hst'
      have : ¬ (p.viewMay cu g f' = true ∧ a.Stops = false) := by simp [hv']
      rw [ite_neg this] at hst'
      subst hst'
      exact h g f' a hfor hs hst hv'
  · exact h g f act hfor hmem hst hv'

/-- **Codegen soundness** (a corollary of `noUB_of_enforced_of_foreignCovered_of_siteAgreement`
and the `insertPads` lemmas). If `p` satisfies `ForeignCovered cu p` and `SiteAgreement cu p`,
then no finite run of any function of `insertPads cu p` has outcome `ub`. -/
theorem noUB_insertPads_of_foreignCovered_of_siteAgreement (cu : Prec) (p : Prog)
    (hfc : ForeignCovered cu p) (hsa : SiteAgreement cu p) :
    ∀ f t o, Exec cu (insertPads cu p) f t o → o ≠ .ub :=
  noUB_of_enforced_of_foreignCovered_of_siteAgreement cu _ (insertPads_enforced cu p)
    (insertPads_foreignCovered cu p hfc) (insertPads_siteAgreement cu p hsa)

/-- **A missing stopping pad is undefined behaviour once the callee unwinds.** Let `g` be a
non-foreign function classified as non-unwinding by its own crate whose body starts with a call
to `f` whose action does not stop unwinding. If `f` has a finite run with trace `t` that
unwinds, then `g` has a finite run with outcome `ub`; this holds whichever way `g`'s crate
classifies `f`. -/
theorem ub_of_selfNonUnwinding_of_unguarded_head_call_of_callee_unwinds (cu : Prec) (p : Prog)
    (g f : Nat) (act : Action)
    (rest : List Stmt) (t : List Event) (hg : (p.fn g).info.foreign = false)
    (hgself : p.selfMay cu g = false) (hbody : (p.fn g).body = .call f act :: rest)
    (hact : act.Stops = false) (hf : Exec cu p f t .unwind) : ∃ t', Exec cu p g t' .ub := by
  obtain ⟨n, hn⟩ := hf
  have key : ∃ t', (t', Outcome.unwind) ∈ prependRuns t (onUnwind g (!p.viewMay cu g f) act
      (execBody cu p (runFn cu p n) g rest)) ∨
      (t', Outcome.ub) ∈ prependRuns t (onUnwind g (!p.viewMay cu g f) act
      (execBody cu p (runFn cu p n) g rest)) := by
    cases act with
    | catchPad => simp [Action.Stops] at hact
    | terminate => simp [Action.Stops] at hact
    | none =>
      cases p.viewMay cu g f
      · exact ⟨t ++ [], Or.inr (by simp [onUnwind, prependRuns])⟩
      · exact ⟨t ++ [], Or.inl (by simp [onUnwind, prependRuns])⟩
    | cleanup ds =>
      cases p.viewMay cu g f
      · exact ⟨t ++ [], Or.inr (by simp [onUnwind, prependRuns])⟩
      · exact ⟨t ++ ds.map (Event.drop g), Or.inl (by simp [onUnwind, prependRuns])⟩
  obtain ⟨t', ht'⟩ := key
  refine ⟨t', n + 1, ?_⟩
  unfold runFn
  rw [ite_neg (by simp [hg]), hbody]
  apply List.mem_map.2
  rcases ht' with ht' | ht'
  · refine ⟨(t', .unwind), ?_, by simp [boundary, Prog.selfMay] at hgself ⊢; simp [hgself]⟩
    simp only [execBody, List.mem_flatMap]
    exact ⟨(t, .unwind), hn, ht'⟩
  · refine ⟨(t', .ub), ?_, by simp [boundary]⟩
    simp only [execBody, List.mem_flatMap]
    exact ⟨(t, .unwind), hn, ht'⟩

/-! ## Item 3: mixing panic strategies across crates -/

theorem crateOf_mem_or_dflt (p : Prog) (g : Nat) :
    p.crateOf g ∈ p.crates ∨ p.crateOf g = CrateCfg.dflt := by
  simp only [Prog.crateOf, List.getD_eq_getElem?_getD]
  cases h : p.crates[(p.fn g).crate]? with
  | none => exact Or.inr rfl
  | some c => exact Or.inl (List.mem_of_getElem? h)

/-- Let both crates use the `unwind` strategy, and let the drop-glue settings agree for `i` (if
`i` is drop glue and the caller's crate has panic-in-drop `abort`, so does the callee's crate).
Then a "non-unwinding" verdict of `stdCanUnwind` from the caller's crate carries over to the
callee's crate. -/
theorem std_agree_of_unwind (cg cf : CrateCfg) (i : FnInfo) (hcg : cg.panic = .unwind)
    (hcf : cf.panic = .unwind)
    (hglue : i.dropGlue = true → cg.panicInDrop = .abort → cf.panicInDrop = .abort) :
    stdCanUnwind cg i = false → stdCanUnwind cf i = false := by
  obtain ⟨cgp, cgd⟩ := cg
  obtain ⟨cfp, cfd⟩ := cf
  obtain ⟨abi, fo, nu, dg⟩ := i
  simp only at hcg hcf hglue
  subst hcg hcf
  cases abi <;> cases fo <;> cases nu <;> cases dg <;> cases cgd <;> cases cfd <;>
    simp_all [stdCanUnwind, stdOrder, evalRules, ruleAttr, ruleAbortNonForeign, ruleDropGlue,
      ruleAbi, abiCanUnwind, Strategy.unwinds]

/-- `stdCanUnwind` classifies every non-foreign function as non-unwinding from a crate with
the `abort` strategy. -/
theorem std_abort_nonForeign (c : CrateCfg) (i : FnInfo) (hc : c.panic = .abort)
    (hi : i.foreign = false) : stdCanUnwind c i = false := by
  obtain ⟨cp, cd⟩ := c
  obtain ⟨abi, fo, nu, dg⟩ := i
  simp only at hc hi
  subst hc hi
  cases nu <;> simp [stdCanUnwind, stdOrder, evalRules, ruleAttr, ruleAbortNonForeign,
    Strategy.unwinds]

/-- Body invariant when the artifact is not potentially unwinding: no run of a body of a
non-foreign function unwinds or has outcome `ub`. -/
theorem execBody_noPU (p : Prog) (callee : Nat → List Run) (g : Nat)
    (hhand : p.handler = .abort)
    (hno : ∀ g f act, (p.fn g).info.foreign = false → Stmt.call f act ∈ (p.fn g).body →
      (p.fn f).info.abi = .cUnwind → (p.crateOf g).panic = .abort)
    (henf : Enforced stdCanUnwind p) (hng : ForeignNotGlue p)
    (hcallee : ∀ f, ∀ r ∈ callee f, r.2 ≠ .ub ∧ (r.2 = .unwind →
      (p.fn f).info.foreign = true ∧ (p.fn f).info.abi = .cUnwind ∧
        (p.fn f).info.neverUnwind = false))
    (hg : (p.fn g).info.foreign = false) :
    ∀ l : List Stmt, (∀ s ∈ l, s ∈ (p.fn g).body) →
      ∀ r ∈ execBody stdCanUnwind p callee g l, r.2 ≠ .ub ∧ r.2 ≠ .unwind := by
  intro l
  induction l with
  | nil =>
    intro _ r hr
    simp only [execBody, List.mem_singleton] at hr
    subst hr
    exact ⟨by simp, by simp⟩
  | cons s rest ih =>
    intro hsub r hr
    have hrest : ∀ s ∈ rest, s ∈ (p.fn g).body := fun s hs => hsub s (List.mem_cons_of_mem _ hs)
    have hs : s ∈ (p.fn g).body := hsub s List.mem_cons_self
    cases s with
    | raise act =>
      simp only [execBody, hhand, List.mem_singleton] at hr
      subst hr
      exact ⟨by simp, by simp⟩
    | call f act =>
      simp only [execBody, List.mem_flatMap] at hr
      obtain ⟨⟨t0, o0⟩, h0, hr⟩ := hr
      have hc := hcallee f _ h0
      cases o0 with
      | ret =>
        obtain ⟨r', hr', rfl⟩ := mem_prependRuns hr
        exact ih hrest r' hr'
      | unwind =>
        obtain ⟨r', hr', rfl⟩ := mem_prependRuns hr
        obtain ⟨hfor, habi, hnu⟩ := hc.2 rfl
        have hab := hno g f act hg hs habi
        have hself : p.selfMay stdCanUnwind g = false := std_abort_nonForeign _ _ hab hg
        have hview : p.viewMay stdCanUnwind g f = true :=
          stdCanUnwind_foreign_cUnwind _ _ hfor habi hnu (hng f hfor)
        have hst := (henf g hg hself).2 f act hs hview
        cases act with
        | terminate =>
          simp only [onUnwind, List.mem_singleton] at hr'
          subst hr'
          exact ⟨by simp, by simp⟩
        | catchPad =>
          simp only [onUnwind] at hr'
          obtain ⟨r'', hr'', rfl⟩ := mem_prependRuns hr'
          exact ih hrest r'' hr''
        | none => simp [Action.Stops] at hst
        | cleanup ds => simp [Action.Stops] at hst
      | abort =>
        simp only [List.mem_singleton] at hr
        subst hr
        exact ⟨by simp, by simp⟩
      | ub => exact absurd rfl hc.1

/-- Fuel-indexed invariant when the artifact is not potentially unwinding: no run has outcome
`ub`, and only foreign `cUnwind` functions without the never-unwind attribute unwind. -/
theorem runFn_good_noPU (p : Prog) (hhand : p.handler = .abort)
    (hno : ∀ g f act, (p.fn g).info.foreign = false → Stmt.call f act ∈ (p.fn g).body →
      (p.fn f).info.abi = .cUnwind → (p.crateOf g).panic = .abort)
    (henf : Enforced stdCanUnwind p) (hh : ForeignHonest p) (hng : ForeignNotGlue p) :
    ∀ n f, ∀ r ∈ runFn stdCanUnwind p n f, r.2 ≠ .ub ∧ (r.2 = .unwind →
      (p.fn f).info.foreign = true ∧ (p.fn f).info.abi = .cUnwind ∧
        (p.fn f).info.neverUnwind = false) := by
  intro n
  induction n with
  | zero => intro f r hr; simp [runFn] at hr
  | succ n ih =>
    intro f r hr
    unfold runFn at hr
    by_cases hfor : (p.fn f).info.foreign = true
    · rw [ite_pos hfor] at hr
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨by simp, by simp⟩
      · by_cases hth : (p.fn f).throws = true
        · rw [ite_pos hth, List.mem_singleton] at hr
          subst hr
          obtain ⟨habi, hnu⟩ := hh f hfor hth
          have hm : p.selfMay stdCanUnwind f = true :=
            stdCanUnwind_foreign_cUnwind _ _ hfor habi hnu (hng f hfor)
          simp [boundary, hm, hfor, habi, hnu]
        · rw [ite_neg hth] at hr
          simp at hr
    · rw [ite_neg hfor] at hr
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      have hfor' : (p.fn f).info.foreign = false := by simpa using hfor
      have h := execBody_noPU p (runFn stdCanUnwind p n) f hhand hno henf hng ih hfor' _
        (fun s hs => hs) r' hr'
      obtain ⟨t', o'⟩ := r'
      cases o' with
      | unwind => exact absurd rfl h.2
      | ret => simp [boundary]
      | abort => simp [boundary]
      | ub => exact absurd rfl h.1

/-- If `p` satisfies `LinkOK` and is potentially unwinding, the crate settings of every function
index (including out-of-range indices, which denote `CrateCfg.dflt`) use the `unwind`
strategy. -/
theorem crateOf_unwind_of_linkOK_of_potentiallyUnwinding (p : Prog) (hlink : LinkOK p)
    (hpu : PotentiallyUnwinding p) (g : Nat) : (p.crateOf g).panic = .unwind := by
  rcases crateOf_mem_or_dflt p g with h | h
  · exact hlink hpu _ h
  · rw [h]; rfl

/-- **Mixed strategies under the linking restriction.** For `stdCanUnwind` and every program
`p`: if `p` satisfies `LinkOK`, `Enforced stdCanUnwind`, `ForeignHonest` and `ForeignNotGlue`,
and satisfies `GlueAgreement` in case it is potentially unwinding, then no finite run of any
function of `p` has outcome `ub`. -/
theorem noUB_std_of_linkOK_of_enforced_of_foreignHonest_of_foreignNotGlue_of_glueAgreement
    (p : Prog) (hlink : LinkOK p) (henf : Enforced stdCanUnwind p) (hh : ForeignHonest p)
    (hng : ForeignNotGlue p) (hglue : PotentiallyUnwinding p → GlueAgreement p) :
    ∀ f t o, Exec stdCanUnwind p f t o → o ≠ .ub := by
  by_cases hpu : PotentiallyUnwinding p
  · -- every crate unwinds: call-site agreement follows, and item 1 applies
    have hcr := crateOf_unwind_of_linkOK_of_potentiallyUnwinding p hlink hpu
    have hga := hglue hpu
    have hsa : SiteAgreement stdCanUnwind p := by
      intro g f act hgfor hmem hst hv
      exact std_agree_of_unwind _ _ _ (hcr g) (hcr f)
        (fun hdg hpid => hga g f act hgfor hmem hdg hst hpid) hv
    exact noUB_of_enforced_of_foreignCovered_of_siteAgreement _ p henf
      (foreignCovered_std_of_foreignHonest_of_foreignNotGlue p hh hng) hsa
  · -- the artifact is not potentially unwinding: only foreign `cUnwind` functions unwind
    have hhand : p.handler = .abort := by
      cases hx : p.handler
      · exact absurd (Or.inl hx) hpu
      · rfl
    have hno : ∀ g f act, (p.fn g).info.foreign = false → Stmt.call f act ∈ (p.fn g).body →
        (p.fn f).info.abi = .cUnwind → (p.crateOf g).panic = .abort := by
      intro g f act hg hmem habi
      cases hx : (p.crateOf g).panic
      · exact absurd (Or.inr ⟨g, f, act, hg, hx, hmem, habi⟩) hpu
      · rfl
    intro f t o h
    obtain ⟨n, hn⟩ := h
    exact (runFn_good_noPU p hhand hno henf hh hng n f _ hn).1

/-! ## Item 4: drop glue under per-crate panic-in-drop -/

/-- Static facts of a drop-glue instance (Rust ABI, not foreign, no attribute). -/
def glueInfo : FnInfo := { abi := .rust, foreign := false, neverUnwind := false, dropGlue := true }

/-- Static facts of an ordinary Rust function. -/
def rustInfo : FnInfo := { abi := .rust, foreign := false, neverUnwind := false, dropGlue := false }

/-- The two-crate drop-glue program: crate 0 (settings `cc`) holds the caller, function 0, whose
body is one call to function 1 with action `act`; crate 1 (settings `cg`) compiled the
drop-glue instance, function 1, whose body is `body`. The panic handler is `unwind`. -/
def glueProg (cc cg : CrateCfg) (act : Action) (body : List Stmt) : Prog :=
  { crates := [cc, cg],
    fns := [{ info := rustInfo, crate := 0, body := [.call 1 act], throws := false },
            { info := glueInfo, crate := 1, body := body, throws := false }],
    handler := .unwind }

/-- The glue call site of `glueProg cc cg act` is sound: for every glue body (any statement list,
including calls) for which the program satisfies `Enforced stdCanUnwind`, no finite run of the
caller has outcome `ub`. -/
def GlueSiteSound (cc cg : CrateCfg) (act : Action) : Prop :=
  ∀ body, Enforced stdCanUnwind (glueProg cc cg act body) →
    ∀ t o, Exec stdCanUnwind (glueProg cc cg act body) 0 t o → o ≠ .ub

/-- If `stdCanUnwind cg glueInfo = true`, then `cg` is the all-`unwind` setting. -/
theorem cfg_of_std_glue_true (cg : CrateCfg) (h : stdCanUnwind cg glueInfo = true) :
    cg = ⟨.unwind, .unwind⟩ := by
  obtain ⟨gp, gd⟩ := cg
  cases gp <;> cases gd <;>
    simp_all [stdCanUnwind, stdOrder, evalRules, ruleAttr, ruleAbortNonForeign,
      ruleDropGlue, ruleAbi, abiCanUnwind, glueInfo, Strategy.unwinds]

/-- **Drop-glue call sites.** For all caller-crate settings `cc`, glue-crate settings `cg` and
actions `act`: `GlueSiteSound cc cg act` holds iff, whenever the caller's crate classifies the
glue as non-unwinding (`stdCanUnwind cc glueInfo = false`), the glue instance's own crate also
classifies it as non-unwinding or the call site has a stopping pad (`catchPad` or `terminate`). -/
theorem glueSiteSound_iff (cc cg : CrateCfg) (act : Action) :
    GlueSiteSound cc cg act ↔
      (stdCanUnwind cc glueInfo = false →
        stdCanUnwind cg glueInfo = false ∨ act.Stops = true) := by
  constructor
  · intro h hcc
    cases hcg : stdCanUnwind cg glueInfo
    · exact Or.inl rfl
    · right
      cases hst : act.Stops
      · exfalso
        have henf : Enforced stdCanUnwind (glueProg cc cg act [.raise .none]) := by
          intro g hfor hself
          match g with
          | 0 =>
            refine ⟨fun _ a ha => by simp [glueProg, Prog.fn] at ha, fun f a ha hv => ?_⟩
            simp only [glueProg, Prog.fn, List.getD_cons_zero, List.mem_singleton,
              Stmt.call.injEq] at ha
            obtain ⟨rfl, rfl⟩ := ha
            have : stdCanUnwind cc glueInfo = true := hv
            rw [hcc] at this
            exact absurd this (by decide)
          | 1 =>
            have : stdCanUnwind cg glueInfo = false := hself
            rw [hcg] at this
            exact absurd this (by decide)
          | g + 2 =>
            exact ⟨fun _ a ha => by simp [glueProg, Prog.fn, FnDef.dummy] at ha,
              fun f a ha => by simp [glueProg, Prog.fn, FnDef.dummy] at ha⟩
        have hsg : (glueProg cc cg act [.raise .none]).selfMay stdCanUnwind 1 = true := hcg
        have hvw : (glueProg cc cg act [.raise .none]).viewMay stdCanUnwind 0 1 = false := hcc
        have hub : Exec stdCanUnwind (glueProg cc cg act [.raise .none]) 0 [] .ub := by
          refine ⟨2, ?_⟩
          cases act with
          | catchPad => simp [Action.Stops] at hst
          | terminate => simp [Action.Stops] at hst
          | none =>
            have hf0 : (glueProg cc cg .none [.raise .none]).fn 0 =
                ⟨rustInfo, 0, [.call 1 .none], false⟩ := rfl
            have hf1 : (glueProg cc cg .none [.raise .none]).fn 1 =
                ⟨glueInfo, 1, [.raise .none], false⟩ := rfl
            have hhd : (glueProg cc cg .none [.raise .none]).handler = .unwind := rfl
            simp [runFn, execBody, onUnwind, boundary, prependRuns, hsg, hvw, hf0, hf1, hhd,
              rustInfo, glueInfo]
          | cleanup ds =>
            have hf0 : (glueProg cc cg (.cleanup ds) [.raise .none]).fn 0 =
                ⟨rustInfo, 0, [.call 1 (.cleanup ds)], false⟩ := rfl
            have hf1 : (glueProg cc cg (.cleanup ds) [.raise .none]).fn 1 =
                ⟨glueInfo, 1, [.raise .none], false⟩ := rfl
            have hhd : (glueProg cc cg (.cleanup ds) [.raise .none]).handler = .unwind := rfl
            simp [runFn, execBody, onUnwind, boundary, prependRuns, hsg, hvw, hf0, hf1, hhd,
              rustInfo, glueInfo]
        exact h _ henf [] .ub hub rfl
      · rfl
  · intro hr body henf t o hex
    let q := glueProg cc cg act body
    cases hcg : stdCanUnwind cg glueInfo with
    | false =>
      -- the glue is non-unwinding in its own crate: no function of `q` unwinds or has `ub`
      have hno : ∀ n f, ∀ r ∈ runFn stdCanUnwind q n f, r.2 ≠ .ub ∧ r.2 ≠ .unwind := by
        intro n
        induction n with
        | zero => intro f r hr'; simp [runFn] at hr'
        | succ n ih =>
          intro f r hr'
          have hbody_no : ∀ g l, (∀ s ∈ l, (∃ k a, s = .call k a) ∨
              (∃ a, s = .raise a ∧ a.Stops = true)) →
              ∀ r' ∈ execBody stdCanUnwind q (runFn stdCanUnwind q n) g l,
                r'.2 ≠ .ub ∧ r'.2 ≠ .unwind := by
            intro g l
            induction l with
            | nil =>
              intro _ r' hmem
              simp only [execBody, List.mem_singleton] at hmem
              subst hmem; exact ⟨by decide, by decide⟩
            | cons s rest ihl =>
              intro hl r' hmem
              have hrest := ihl (fun s' hs' => hl s' (List.mem_cons_of_mem _ hs'))
              rcases hl s List.mem_cons_self with ⟨k, a, rfl⟩ | ⟨a, rfl, hst⟩
              · simp only [execBody, List.mem_flatMap] at hmem
                obtain ⟨⟨t0, o0⟩, h0, hmem⟩ := hmem
                have hc := ih k _ h0
                cases o0 with
                | ret =>
                  obtain ⟨r'', hr'', rfl⟩ := mem_prependRuns hmem
                  exact hrest r'' hr''
                | unwind => exact absurd rfl hc.2
                | abort =>
                  simp only [List.mem_singleton] at hmem; subst hmem; exact ⟨by simp, by simp⟩
                | ub => exact absurd rfl hc.1
              · have hhd : q.handler = .unwind := rfl
                simp only [execBody, hhd] at hmem
                cases a with
                | terminate =>
                  simp only [onUnwind, List.mem_singleton] at hmem
                  subst hmem; exact ⟨by simp, by simp⟩
                | catchPad =>
                  simp only [onUnwind] at hmem
                  obtain ⟨r'', hr'', rfl⟩ := mem_prependRuns hmem
                  exact hrest r'' hr''
                | none => simp [Action.Stops] at hst
                | cleanup _ => simp [Action.Stops] at hst
          match f with
          | 0 =>
            have hf0 : q.fn 0 = ⟨rustInfo, 0, [.call 1 act], false⟩ := rfl
            unfold runFn at hr'
            rw [hf0] at hr'
            simp only [rustInfo, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hr'
            obtain ⟨⟨t', o'⟩, hmem, rfl⟩ := hr'
            have hb := hbody_no 0 [.call 1 act]
              (fun s hs => by simp at hs; subst hs; exact Or.inl ⟨1, act, rfl⟩) _ hmem
            cases o' with
            | ret => exact ⟨by simp [boundary], by simp [boundary]⟩
            | abort => exact ⟨by simp [boundary], by simp [boundary]⟩
            | unwind => exact absurd rfl hb.2
            | ub => exact absurd rfl hb.1
          | 1 =>
            have hf1 : q.fn 1 = ⟨glueInfo, 1, body, false⟩ := rfl
            have hself1 : q.selfMay stdCanUnwind 1 = false := hcg
            have henf1 := (henf 1 (by rw [hf1]; rfl) hself1).1 rfl
            unfold runFn at hr'
            rw [hf1] at hr'
            simp only [glueInfo, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hr'
            obtain ⟨⟨t', o'⟩, hmem, rfl⟩ := hr'
            have hb := hbody_no 1 body (fun s hs => by
              cases s with
              | call k a => exact Or.inl ⟨k, a, rfl⟩
              | raise a => exact Or.inr ⟨a, rfl, henf1 a (by rw [hf1]; exact hs)⟩) _ hmem
            cases o' with
            | ret => exact ⟨by simp [boundary], by simp [boundary]⟩
            | abort => exact ⟨by simp [boundary], by simp [boundary]⟩
            | unwind => exact absurd rfl hb.2
            | ub => exact absurd rfl hb.1
          | m + 2 =>
            have hfm : q.fn (m + 2) = FnDef.dummy := rfl
            unfold runFn at hr'
            rw [hfm] at hr'
            simp [FnDef.dummy, execBody, boundary] at hr'
            rcases hr' with ⟨rfl, rfl⟩
            exact ⟨by decide, by decide⟩
      obtain ⟨n, hn⟩ := hex
      exact (hno n 0 _ hn).1
    | true =>
      -- the glue's own crate is all-`unwind`, so it classifies every Rust callee of the glue as
      -- possibly unwinding, and `SiteAgreement` holds
      have hcg_cfg := cfg_of_std_glue_true cg hcg
      have hfc : ForeignCovered stdCanUnwind q := by
        intro f hfor _
        match f with
        | 0 => simp [q, glueProg, Prog.fn, rustInfo] at hfor
        | 1 => simp [q, glueProg, Prog.fn, glueInfo] at hfor
        | m + 2 => simp [q, glueProg, Prog.fn, FnDef.dummy] at hfor
      have hsa : SiteAgreement stdCanUnwind q := by
        intro g f a _ hmem hst hv
        match g with
        | 0 =>
          simp only [q, glueProg, Prog.fn, List.getD_cons_zero, List.mem_singleton,
            Stmt.call.injEq] at hmem
          obtain ⟨rfl, rfl⟩ := hmem
          have hv' : stdCanUnwind cc glueInfo = false := hv
          rcases hr hv' with h | h
          · rw [hcg] at h; exact absurd h (by decide)
          · rw [hst] at h; exact absurd h (by decide)
        | 1 =>
          exfalso
          have hv_true : q.viewMay stdCanUnwind 1 f = true := by
            subst hcg_cfg
            have hc1 : q.crateOf 1 = ⟨.unwind, .unwind⟩ := rfl
            match f with
            | 0 =>
              have hfm : q.fn 0 = ⟨rustInfo, 0, [.call 1 act], false⟩ := rfl
              simp [Prog.viewMay, hfm, hc1, rustInfo, stdCanUnwind, stdOrder, evalRules,
                ruleAttr, ruleAbortNonForeign, ruleDropGlue, ruleAbi, abiCanUnwind,
                Strategy.unwinds]
            | 1 =>
              have hfm : q.fn 1 = ⟨glueInfo, 1, body, false⟩ := rfl
              simp [Prog.viewMay, hfm, hc1, glueInfo, stdCanUnwind, stdOrder, evalRules,
                ruleAttr, ruleAbortNonForeign, ruleDropGlue, ruleAbi, abiCanUnwind,
                Strategy.unwinds]
            | m + 2 =>
              have hfm : q.fn (m + 2) = FnDef.dummy := rfl
              simp [Prog.viewMay, hfm, hc1, FnDef.dummy, stdCanUnwind, stdOrder, evalRules,
                ruleAttr, ruleAbortNonForeign, ruleDropGlue, ruleAbi, abiCanUnwind,
                Strategy.unwinds]
          rw [hv_true] at hv
          exact absurd hv (by decide)
        | m + 2 => simp [q, glueProg, Prog.fn, FnDef.dummy] at hmem
      exact noUB_of_enforced_of_foreignCovered_of_siteAgreement _ q henf hfc hsa 0 t o hex

/-- **Drop glue, per-crate panic-in-drop form.** If the caller's crate treats drop glue as
non-unwinding (its panic strategy or its panic-in-drop setting is `abort`) and the glue
instance's crate has panic strategy `unwind`, then `GlueSiteSound cc cg act` holds iff the glue
instance's crate has panic-in-drop `abort` or the call site has a stopping pad (`catchPad` or
`terminate`). -/
theorem glueSiteSound_iff_panicInDrop (cc cg : CrateCfg) (act : Action)
    (hview : cc.panic = .abort ∨ cc.panicInDrop = .abort) (hcg : cg.panic = .unwind) :
    GlueSiteSound cc cg act ↔ (cg.panicInDrop = .abort ∨ act.Stops = true) := by
  rw [glueSiteSound_iff]
  obtain ⟨cp, cd⟩ := cc
  obtain ⟨gp, gd⟩ := cg
  simp only at hview hcg
  subst hcg
  cases cp <;> cases cd <;> cases gd <;> simp_all [stdCanUnwind, stdOrder, evalRules, ruleAttr,
    ruleAbortNonForeign, ruleDropGlue, ruleAbi, abiCanUnwind, glueInfo, Strategy.unwinds]

/-! ## Item 5 (program level): functions compiled without landing pads -/

theorem withPads_fn (p : Prog) (pads : Nat → Pads) (g : Nat) :
    (p.withPads pads).fn g =
      match pads g with
      | .full => p.fn g
      | .none => { p.fn g with body := (p.fn g).body.map Stmt.unpadded } := by
  simp only [Prog.fn, Prog.withPads, List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  cases h : p.fns[g]? with
  | none => cases pads g <;> simp [FnDef.dummy]
  | some d => cases pads g <;> simp

theorem withPads_info (p : Prog) (pads : Nat → Pads) (g : Nat) :
    ((p.withPads pads).fn g).info = (p.fn g).info := by
  rw [withPads_fn]; cases pads g <;> rfl

theorem withPads_throws (p : Prog) (pads : Nat → Pads) (g : Nat) :
    ((p.withPads pads).fn g).throws = (p.fn g).throws := by
  rw [withPads_fn]; cases pads g <;> rfl

theorem withPads_crateOf (p : Prog) (pads : Nat → Pads) (g : Nat) :
    (p.withPads pads).crateOf g = p.crateOf g := by
  simp only [Prog.crateOf, withPads_fn]
  cases pads g <;> rfl

theorem withPads_selfMay (cu : Prec) (p : Prog) (pads : Nat → Pads) (g : Nat) :
    (p.withPads pads).selfMay cu g = p.selfMay cu g := by
  simp only [Prog.selfMay, withPads_crateOf, withPads_info]

theorem withPads_viewMay (cu : Prec) (p : Prog) (pads : Nat → Pads) (g f : Nat) :
    (p.withPads pads).viewMay cu g f = p.viewMay cu g f := by
  simp only [Prog.viewMay, withPads_crateOf, withPads_info]

/-- `execBody` depends on the program only through its handler and its classifications. -/
theorem execBody_congr_prog (cu : Prec) (p q : Prog) (hh : q.handler = p.handler)
    (hv : ∀ g f, q.viewMay cu g f = p.viewMay cu g f) (callee : Nat → List Run) (g : Nat) :
    ∀ l, execBody cu q callee g l = execBody cu p callee g l := by
  intro l
  induction l with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | raise act => simp only [execBody, hh, ih]
    | call f act => simp only [execBody, hv, ih]

theorem flatMap_congr_mem {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Removing the landing pads of a statement list changes nothing when the list has no panic
points and no callee it calls has an unwinding run. -/
theorem execBody_unpadded (cu : Prec) (p : Prog) (callee : Nat → List Run) (g : Nat) :
    ∀ l : List Stmt, (∀ s ∈ l, ∃ f a, s = .call f a ∧ ∀ r ∈ callee f, r.2 ≠ .unwind) →
      execBody cu p callee g (l.map Stmt.unpadded) = execBody cu p callee g l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    obtain ⟨f, a, rfl, hf⟩ := h s List.mem_cons_self
    have ih' := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
    simp only [List.map_cons, Stmt.unpadded, execBody, ih']
    apply flatMap_congr_mem
    intro r hr
    obtain ⟨t, o⟩ := r
    cases o with
    | unwind => exact absurd rfl (hf _ hr)
    | ret => rfl
    | abort => rfl
    | ub => rfl

/-- An unwinding run leaves only a function classified as possibly unwinding by its own crate
(this holds by construction of `boundary`, with no hypothesis). -/
theorem runFn_unwind_selfMay (cu : Prec) (p : Prog) :
    ∀ n f, ∀ r ∈ runFn cu p n f, r.2 = .unwind → p.selfMay cu f = true := by
  intro n f r hr hu
  cases n with
  | zero => simp [runFn] at hr
  | succ n =>
    unfold runFn at hr
    by_cases hfor : (p.fn f).info.foreign = true
    · rw [ite_pos hfor] at hr
      rcases List.mem_cons.1 hr with rfl | hr
      · cases hu
      · by_cases hth : (p.fn f).throws = true
        · rw [ite_pos hth, List.mem_singleton] at hr
          subst hr
          cases hm : p.selfMay cu f
          · simp [boundary, hm] at hu
          · rfl
        · rw [ite_neg hth] at hr; simp at hr
    · rw [ite_neg hfor] at hr
      obtain ⟨⟨t', o'⟩, _, rfl⟩ := List.mem_map.1 hr
      cases o' <;> cases hm : p.selfMay cu f <;> simp_all [boundary]

/-- **Backends without landing pads: a local sufficient condition.** Let every function of `p` be
compiled by a backend with capability `pads g`. Suppose that, in every non-foreign function
`g < p.fns.length` with `pads g = none` (reachable or not), every panic point has an action without
an obligation (`Action.obligation`) when the panic handler is `unwind` (`hraise`), and every call
whose action has an obligation calls a callee classified as non-unwinding by the callee's own
crate (`hcall`). Then every function has exactly the same finite runs in `p.withPads pads` as in
`p`. -/
theorem withPads_exec_iff_of_padsNone_obligationFreeRaises_of_obligationCalleesNonUnwinding
    (cu : Prec) (p : Prog) (pads : Nat → Pads)
    (hraise : ∀ g, g < p.fns.length → pads g = .none → (p.fn g).info.foreign = false →
      p.handler = .unwind → ∀ a, Stmt.raise a ∈ (p.fn g).body → a.obligation = false)
    (hcall : ∀ g, g < p.fns.length → pads g = .none → (p.fn g).info.foreign = false →
      ∀ f a, Stmt.call f a ∈ (p.fn g).body → a.obligation = true → p.selfMay cu f = false) :
    ∀ f t o, Exec cu (p.withPads pads) f t o ↔ Exec cu p f t o := by
  have heq : ∀ n f, runFn cu (p.withPads pads) n f = runFn cu p n f := by
    intro n
    induction n with
    | zero => intro f; rfl
    | succ n ih =>
      intro f
      have hcal : runFn cu (p.withPads pads) n = runFn cu p n := funext ih
      have hbd : boundary cu (p.withPads pads) f = boundary cu p f := by
        funext r; simp only [boundary, withPads_selfMay]
      have hcong := execBody_congr_prog cu p (p.withPads pads) rfl
        (withPads_viewMay cu p pads) (runFn cu p n) f
      unfold runFn
      rw [withPads_info, withPads_throws, hbd, hcal, hcong]
      split
      · rfl
      · rename_i hfor
        have hfor' : (p.fn f).info.foreign = false := by simpa using hfor
        congr 1
        rw [withPads_fn]
        cases hp : pads f with
        | full => rfl
        | none =>
          show execBody cu p (runFn cu p n) f ((p.fn f).body.map Stmt.unpadded) = _
          by_cases hlt : f < p.fns.length
          · have hbody_eq : ∀ l : List Stmt, (∀ s ∈ l, s ∈ (p.fn f).body) →
                execBody cu p (runFn cu p n) f (l.map Stmt.unpadded) =
                  execBody cu p (runFn cu p n) f l := by
              intro l
              induction l with
              | nil => intro _; rfl
              | cons s rest ihl =>
                intro hsub
                have hs := hsub s List.mem_cons_self
                have ih' := ihl (fun s' hs' => hsub s' (List.mem_cons_of_mem _ hs'))
                cases s with
                | raise a =>
                  cases hh : p.handler with
                  | abort => simp [Stmt.unpadded, execBody, hh]
                  | unwind =>
                    have hobl := hraise f hlt hp hfor' hh a hs
                    cases a with
                    | none => simp [Stmt.unpadded, execBody, onUnwind, hh]
                    | cleanup ds =>
                      cases ds with
                      | nil => simp [Stmt.unpadded, execBody, onUnwind, hh]
                      | cons _ _ => simp [Action.obligation] at hobl
                    | catchPad => simp [Action.obligation] at hobl
                    | terminate => simp [Action.obligation] at hobl
                | call g a =>
                  simp only [List.map_cons, Stmt.unpadded, execBody, ih']
                  apply flatMap_congr_mem
                  intro ⟨t0, o0⟩ hrm
                  cases o0 with
                  | unwind =>
                    cases ha : a.obligation with
                    | false =>
                      cases a with
                      | none => rfl
                      | cleanup ds =>
                        cases ds with
                        | nil => simp [onUnwind]
                        | cons _ _ => simp [Action.obligation] at ha
                      | catchPad => simp [Action.obligation] at ha
                      | terminate => simp [Action.obligation] at ha
                    | true =>
                      have hsm := runFn_unwind_selfMay cu p n g (t0, .unwind) hrm rfl
                      rw [hcall f hlt hp hfor' g a hs ha] at hsm
                      exact absurd hsm (by decide)
                  | ret => rfl
                  | abort => rfl
                  | ub => rfl
            exact hbody_eq _ (fun s hs => hs)
          · rw [p.fn_of_ge (Nat.le_of_not_lt hlt)]
            rfl
  intro f t o
  constructor <;> (rintro ⟨n, hn⟩; exact ⟨n, by simpa [heq n f] using hn⟩)

/-- **Backends without landing pads, made sound by non-unwinding classification.** Let every
function of `p` be compiled by a backend with capability `pads g`. Suppose every non-foreign
function `g < p.fns.length` with `pads g = none` is classified as non-unwinding by its own
crate (`hnone`), and the compiled program `p.withPads pads` satisfies `EnforcedAt cu` (`henf`)
and `SiteAgreementAt cu` (`hsa`) at every function index `g` with `pads g = none`, reachable or
not. Then every function has exactly the same finite runs in `p.withPads pads` as in `p`. -/
theorem withPads_exec_iff_of_padsNone_nonunwinding_of_enforcedAt_of_siteAgreementAt (cu : Prec)
    (p : Prog) (pads : Nat → Pads)
    (hnone : ∀ g, g < p.fns.length → pads g = .none → (p.fn g).info.foreign = false →
      p.selfMay cu g = false)
    (henf : ∀ g, pads g = .none → EnforcedAt cu (p.withPads pads) g)
    (hsa : ∀ g, pads g = .none → SiteAgreementAt cu (p.withPads pads) g) :
    ∀ f t o, Exec cu (p.withPads pads) f t o ↔ Exec cu p f t o := by
  have hq : ∀ g, pads g = .none → (p.fn g).info.foreign = false →
      ((p.withPads pads).fn g).info.foreign = false ∧
      ((p.withPads pads).fn g).body = (p.fn g).body.map Stmt.unpadded := by
    intro g hp hfor
    exact ⟨by rw [withPads_info]; exact hfor, by rw [withPads_fn, hp]⟩
  apply withPads_exec_iff_of_padsNone_obligationFreeRaises_of_obligationCalleesNonUnwinding cu p pads
  · intro g hlt hp hfor hh a ha
    obtain ⟨hforq, hbody⟩ := hq g hp hfor
    have hselfq : (p.withPads pads).selfMay cu g = false := by
      rw [withPads_selfMay]; exact hnone g hlt hp hfor
    have hm : Stmt.raise .none ∈ ((p.withPads pads).fn g).body := by
      rw [hbody]; exact List.mem_map.2 ⟨_, ha, rfl⟩
    exact absurd ((henf g hp hforq hselfq).1 hh .none hm) (by decide)
  · intro g hlt hp hfor f a ha _
    obtain ⟨hforq, hbody⟩ := hq g hp hfor
    have hselfq : (p.withPads pads).selfMay cu g = false := by
      rw [withPads_selfMay]; exact hnone g hlt hp hfor
    have hm : Stmt.call f .none ∈ ((p.withPads pads).fn g).body := by
      rw [hbody]; exact List.mem_map.2 ⟨_, ha, rfl⟩
    have hv : (p.withPads pads).viewMay cu g f = false := by
      cases hx : (p.withPads pads).viewMay cu g f
      · rfl
      · exact absurd ((henf g hp hforq hselfq).2 f .none hm hx) (by decide)
    have := hsa g hp f .none hforq hm rfl hv
    rwa [withPads_selfMay] at this

/-! ## Item 2 (continued): the toy codegen preserves every run that is not `ub` -/

/-- **The toy codegen preserves every run that is not `ub`.** For every precedence function `cu`,
every program `p` and every finite run of a function `f` of `p` whose outcome `o` is not `ub`,
`f` has the same run (same trace `t`, same outcome `o`) in `insertPads cu p`. -/
theorem exec_insertPads_of_exec_of_ne_ub (cu : Prec) (p : Prog) :
    ∀ f t o, o ≠ .ub → Exec cu p f t o → Exec cu (insertPads cu p) f t o := by
  have hrun : ∀ n f t o, o ≠ .ub → (t, o) ∈ runFn cu p n f →
      (t, o) ∈ runFn cu (insertPads cu p) n f := by
    intro n
    induction n with
    | zero => intro f t o _ hr; simp [runFn] at hr
    | succ n ih =>
      intro f t o hnoub hr
      have hbd : boundary cu (insertPads cu p) f = boundary cu p f := by
        funext r
        simp only [boundary, Prog.selfMay, insertPads_crateOf, insertPads_info]
        rfl
      unfold runFn at hr ⊢
      rw [insertPads_info, insertPads_throws, hbd]
      by_cases hfor : (p.fn f).info.foreign = true
      · rw [ite_pos hfor] at hr ⊢; exact hr
      · rw [ite_neg hfor] at hr ⊢
        obtain ⟨⟨t', o'⟩, hmem, hb_eq⟩ := List.mem_map.1 hr
        apply List.mem_map.2
        refine ⟨(t', o'), ?_, hb_eq⟩
        have hcong := execBody_congr_prog cu p (insertPads cu p) rfl
          (fun g h => by simp [Prog.viewMay, insertPads_crateOf, insertPads_info])
          (runFn cu (insertPads cu p) n) f
        rw [hcong, insertPads_body]
        have hlift_unchanged : ∀ l : List Stmt, ∀ t1 o1, o1 ≠ .ub →
            (t1, o1) ∈ execBody cu p (runFn cu p n) f l →
            (t1, o1) ∈ execBody cu p (runFn cu (insertPads cu p) n) f l := by
          intro l
          induction l with
          | nil => intro t1 o1 _ hm; exact hm
          | cons s rest ihl =>
            intro t1 o1 hno1 hm
            cases s with
            | raise a =>
              simp only [execBody] at hm ⊢
              cases hh : p.handler with
              | abort => rw [hh] at hm; exact hm
              | unwind =>
                rw [hh] at hm
                cases a with
                | terminate => exact hm
                | none => exact hm
                | cleanup _ => exact hm
                | catchPad =>
                  simp only [onUnwind] at hm ⊢
                  obtain ⟨⟨t2, o2⟩, hm2, heq2⟩ := mem_prependRuns hm
                  have ho2 : o2 ≠ .ub := by intro h; subst h; simp at heq2; exact hno1 heq2.2
                  apply List.mem_map.2
                  exact ⟨(t2, o2), ihl t2 o2 ho2 hm2, heq2.symm⟩
            | call g a =>
              simp only [execBody, List.mem_flatMap] at hm ⊢
              obtain ⟨⟨t0, o0⟩, h0, hm⟩ := hm
              cases o0 with
              | ub => simp at hm; exact absurd hm.2 hno1
              | abort =>
                exact ⟨(t0, .abort), ih g t0 .abort (by decide) h0, hm⟩
              | ret =>
                obtain ⟨⟨t2, o2⟩, hm2, heq2⟩ := mem_prependRuns hm
                have ho2 : o2 ≠ .ub := by intro h; subst h; simp at heq2; exact hno1 heq2.2
                refine ⟨(t0, .ret), ih g t0 .ret (by decide) h0, ?_⟩
                apply List.mem_map.2
                exact ⟨(t2, o2), ihl t2 o2 ho2 hm2, heq2.symm⟩
              | unwind =>
                obtain ⟨⟨t2, o2⟩, hm2, heq2⟩ := mem_prependRuns hm
                have ho2 : o2 ≠ .ub := by intro h; subst h; simp at heq2; exact hno1 heq2.2
                refine ⟨(t0, .unwind), ih g t0 .unwind (by decide) h0, ?_⟩
                apply List.mem_map.2
                cases a with
                | terminate => exact ⟨(t2, o2), hm2, heq2.symm⟩
                | none => exact ⟨(t2, o2), hm2, heq2.symm⟩
                | cleanup _ => exact ⟨(t2, o2), hm2, heq2.symm⟩
                | catchPad =>
                  simp only [onUnwind] at hm2 ⊢
                  obtain ⟨⟨t3, o3⟩, hm3, heq3⟩ := mem_prependRuns hm2
                  have ho3 : o3 ≠ .ub := by intro h; subst h; simp at heq3; exact ho2 heq3.2
                  refine ⟨(t2, o2), List.mem_map.2 ⟨(t3, o3), ihl t3 o3 ho3 hm3, heq3.symm⟩,
                    heq2.symm⟩
        by_cases hcond : (p.fn f).info.foreign = false ∧ p.selfMay cu f = false
        · rw [ite_pos hcond]
          have ho' : o' ≠ .ub ∧ o' ≠ .unwind := by
            cases o' with
            | ret => exact ⟨by decide, by decide⟩
            | abort => exact ⟨by decide, by decide⟩
            | unwind =>
              simp only [boundary, hcond.2, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hb_eq
              exact absurd hb_eq.2.symm hnoub
            | ub =>
              simp only [boundary, Prod.mk.injEq] at hb_eq
              exact absurd hb_eq.2.symm hnoub
          have hlift_padded : ∀ l : List Stmt, ∀ t1 o1, o1 ≠ .ub → o1 ≠ .unwind →
              (t1, o1) ∈ execBody cu p (runFn cu p n) f l →
              (t1, o1) ∈ execBody cu p (runFn cu (insertPads cu p) n) f
                (l.map (padStmt cu p f)) := by
            intro l
            induction l with
            | nil => intro t1 o1 _ _ hm; exact hm
            | cons s rest ihl =>
              intro t1 o1 hno1 hnu1 hm
              cases s with
              | raise a =>
                simp only [List.map_cons, padStmt_raise, execBody] at hm ⊢
                cases hh : p.handler with
                | abort => rw [hh] at hm; exact hm
                | unwind =>
                  rw [hh] at hm
                  cases a with
                  | terminate => simp [Action.Stops] at hm ⊢; exact hm
                  | catchPad =>
                    simp only [Action.Stops, onUnwind] at hm ⊢
                    obtain ⟨⟨t2, o2⟩, hm2, heq2⟩ := mem_prependRuns hm
                    simp only [Prod.mk.injEq] at heq2
                    obtain ⟨rfl, rfl⟩ := heq2
                    simp only [Bool.true_eq_false, and_false, ↓reduceIte]
                    exact List.mem_map.2 ⟨(t2, o1), ihl t2 o1 hno1 hnu1 hm2, rfl⟩
                  | none => simp [onUnwind] at hm; rcases hm with ⟨_, rfl⟩; exact absurd rfl hnu1
                  | cleanup _ =>
                    simp [onUnwind] at hm; rcases hm with ⟨_, rfl⟩; exact absurd rfl hnu1
              | call g a =>
                simp only [List.map_cons, padStmt_call, execBody, List.mem_flatMap] at hm ⊢
                obtain ⟨⟨t0, o0⟩, h0, hm⟩ := hm
                cases o0 with
                | ub => simp at hm; rcases hm with ⟨_, rfl⟩; exact absurd rfl hno1
                | abort =>
                  exact ⟨(t0, .abort), ih g t0 .abort (by decide) h0, hm⟩
                | ret =>
                  obtain ⟨⟨t2, o2⟩, hm2, heq2⟩ := mem_prependRuns hm
                  simp only [Prod.mk.injEq] at heq2
                  obtain ⟨rfl, rfl⟩ := heq2
                  exact ⟨(t0, .ret), ih g t0 .ret (by decide) h0,
                    List.mem_map.2 ⟨(t2, o1), ihl t2 o1 hno1 hnu1 hm2, rfl⟩⟩
                | unwind =>
                  obtain ⟨⟨t2, o2⟩, hm2, heq2⟩ := mem_prependRuns hm
                  simp only [Prod.mk.injEq] at heq2
                  obtain ⟨rfl, rfl⟩ := heq2
                  cases a with
                  | terminate =>
                    have hnc : ¬ (p.viewMay cu f g = true ∧ Action.terminate.Stops = false) := by
                      simp [Action.Stops]
                    rw [ite_neg hnc]
                    exact ⟨(t0, .unwind), ih g t0 .unwind (by decide) h0,
                      List.mem_map.2 ⟨(t2, o1), hm2, rfl⟩⟩
                  | catchPad =>
                    have hnc : ¬ (p.viewMay cu f g = true ∧ Action.catchPad.Stops = false) := by
                      simp [Action.Stops]
                    rw [ite_neg hnc]
                    simp only [onUnwind] at hm2
                    obtain ⟨⟨t3, o3⟩, hm3, heq3⟩ := mem_prependRuns hm2
                    simp only [Prod.mk.injEq] at heq3
                    obtain ⟨rfl, rfl⟩ := heq3
                    refine ⟨(t0, .unwind), ih g t0 .unwind (by decide) h0, ?_⟩
                    apply List.mem_map.2
                    exact ⟨([Event.caught f] ++ t3, o1),
                      List.mem_map.2 ⟨(t3, o1), ihl t3 o1 hno1 hnu1 hm3, rfl⟩, rfl⟩
                  | none =>
                    cases hv : p.viewMay cu f g <;>
                      simp [hv, onUnwind] at hm2 <;> rcases hm2 with ⟨_, rfl⟩
                    · exact absurd rfl hno1
                    · exact absurd rfl hnu1
                  | cleanup _ =>
                    cases hv : p.viewMay cu f g <;>
                      simp [hv, onUnwind] at hm2 <;> rcases hm2 with ⟨_, rfl⟩
                    · exact absurd rfl hno1
                    · exact absurd rfl hnu1
          exact hlift_padded _ t' o' ho'.1 ho'.2 hmem
        · rw [ite_neg hcond]
          have ho' : o' ≠ .ub := by
            intro h; subst h; simp [boundary] at hb_eq; exact hnoub hb_eq.2.symm
          exact hlift_unchanged _ t' o' ho' hmem
  intro f t o hno ⟨n, hn⟩
  exact ⟨n, hrun n f t o hno hn⟩

end Toy.UnwindCap
