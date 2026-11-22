import Toy.LawRewrite.Basic
import Toy.LawRewrite.CaptureBridge
import Toy.LawRewrite.Lemmas

/-!
# Main statements

Every statement compares the compiled program, produced by a law-dependent rewrite
that runs after the capture point, with the captured semantics of the program before
the rewrite.
-/

namespace Toy.LawRewrite

open CaptureBridge (Den DenIncl VerifierSound TransferSound failClosed)

/-! ## Private proof helpers -/

private theorem beh_trace_prepend (e : List Val) (b : Beh) :
    (Beh.prepend e b).trace = e ++ b.trace := by
  cases b <;> rfl

private theorem improvesPP_prepend (e : List Val) {bt bs : Beh} (h : ImprovesPP bt bs) :
    ImprovesPP (Beh.prepend e bt) (Beh.prepend e bs) := by
  rcases h with rfl | ⟨t, rfl, rest, hrest⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨e ++ t, rfl, rest, ?_⟩
    rw [beh_trace_prepend, List.append_assoc, hrest]

private theorem refinesPP_map_prepend (e : List Val) {src tgt : List Beh} (h : RefinesPP src tgt) :
    RefinesPP (src.map (Beh.prepend e)) (tgt.map (Beh.prepend e)) := by
  intro bt hbt
  rcases List.mem_map.mp hbt with ⟨bt0, hbt0, rfl⟩
  rcases h bt0 hbt0 with ⟨bs0, hbs0, himp⟩
  exact ⟨Beh.prepend e bs0, List.mem_map.mpr ⟨bs0, hbs0, rfl⟩, improvesPP_prepend e himp⟩

private theorem improvesWT_prepend (e : List Val) {bt bs : Beh} (h : ImprovesWT bt bs) :
    ImprovesWT (Beh.prepend e bt) (Beh.prepend e bs) := by
  rcases h with rfl | ⟨t, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨e ++ t, rfl⟩

private theorem refinesWT_map_prepend (e : List Val) {src tgt : List Beh} (h : RefinesWT src tgt) :
    RefinesWT (src.map (Beh.prepend e)) (tgt.map (Beh.prepend e)) := by
  intro bt hbt
  rcases List.mem_map.mp hbt with ⟨bt0, hbt0, rfl⟩
  rcases h bt0 hbt0 with ⟨bs0, hbs0, himp⟩
  exact ⟨Beh.prepend e bs0, List.mem_map.mpr ⟨bs0, hbs0, rfl⟩, improvesWT_prepend e himp⟩

private theorem refinesPP_ub_of_prefix {e₁ e₂ : List Val} (hp : e₁ <+: e₂) (tgt : List Beh) :
    RefinesPP [.ub e₁] (tgt.map (Beh.prepend e₂)) := by
  intro bt hbt
  rcases List.mem_map.mp hbt with ⟨bt0, _, rfl⟩
  refine ⟨.ub e₁, List.mem_singleton.mpr rfl, Or.inr ⟨e₁, rfl, ?_⟩⟩
  rw [beh_trace_prepend]
  rcases hp with ⟨rest, rfl⟩
  exact ⟨rest ++ bt0.trace, (List.append_assoc e₁ rest bt0.trace).symm⟩

private theorem list_snoc_inj {α : Type} {l₁ l₂ : List α} {x₁ x₂ : α}
    (h : l₁ ++ [x₁] = l₂ ++ [x₂]) : l₁ = l₂ ∧ x₁ = x₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => simp at h; exact ⟨rfl, h⟩
    | cons b l₂ => have hlen := congrArg List.length h; simp at hlen
  | cons a l₁ ih =>
    cases l₂ with
    | nil => have hlen := congrArg List.length h; simp at hlen
    | cons b l₂ =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, htail⟩ := h
      obtain ⟨rfl, rfl⟩ := ih htail
      exact ⟨rfl, rfl⟩

private theorem find?_pred {α : Type} (p : α → Bool) :
    ∀ (l : List α) {a : α}, l.find? p = some a → p a = true
  | [], _, h => by cases h
  | x :: xs, a, h => by
    cases hpx : p x with
    | true => simp [hpx] at h; subst h; exact hpx
    | false => simp [hpx] at h; exact find?_pred p xs h

private theorem lawAt_of_refinesPP_probe_aux (env : Env) (pos : RelyPos) (ρ : Rewrite)
    (i : Inst) (v : Val) (σ : Store) (hsafe : env.safety i = .safeTrait)
    (ht : ρ.targets i = true)
    (href : RefinesPP (capDirect env pos (probe i v) σ)
      (compiled env (ρ.apply (probe i v)) σ)) :
    LawAt env ρ i v := by
  have hsrc : capDirect env pos (probe i v) σ =
      [.done ((env.impl i v).1 ++ [(env.impl i v).2])] := by
    simp [capDirect, probe, exec, directCalls, hsafe, Store.upd, Beh.prepend]
  have htgt : compiled env (ρ.apply (probe i v)) σ =
      [.done ((ρ.repl i v).1 ++ [(ρ.repl i v).2])] := by
    simp [compiled, probe, Rewrite.apply, Rewrite.rwStmt, ht, exec, Store.upd, Beh.prepend]
  rw [hsrc, htgt] at href
  rcases href (.done ((ρ.repl i v).1 ++ [(ρ.repl i v).2])) (List.mem_singleton.mpr rfl) with ⟨bs, hbs, himp⟩
  rw [List.mem_singleton] at hbs; subst hbs
  rcases himp with heq | ⟨t, hbad, _⟩
  · injection heq with htr
    obtain ⟨heff, hret⟩ := list_snoc_inj htr.symm
    exact Prod.ext heff hret
  · cases hbad

/-! ## Direct capture: when a post-capture rewrite refines it -/

/-- **The law at the reached calls suffices.** For every environment (any safety marks)
and relies position: if the law of `ρ` holds at every call of a targeted instance that
the execution of `p` from `σ` reaches, then the compiled rewritten program refines the
direct capture of `p` (prefix-preserving). -/
theorem refinesPP_capDirect_apply_of_lawOnReached (env : Env) (pos : RelyPos)
    (ρ : Rewrite) (p : Prog) (σ : Store) (hlaw : LawOnReached env ρ p σ) :
    RefinesPP (capDirect env pos p σ) (compiled env (ρ.apply p) σ) := by
  induction p generalizing σ with
  | nil => exact refinesPP_refl _
  | cons s p ih =>
    cases s with
    | set x v => exact ih (σ.upd x v) (fun i w ht hr => hlaw i w ht hr)
    | out x => exact refinesPP_map_prepend [σ x] (ih σ (fun i w ht hr => hlaw i w ht hr))
    | prim f dst src =>
      exact refinesPP_map_prepend (f (σ src)).1
        (ih (σ.upd dst (f (σ src)).2) (fun i w ht hr => hlaw i w ht hr))
    | ub => exact refinesPP_refl _
    | call j dst src =>
      have htail : LawOnReached env ρ p (σ.upd dst (env.impl j (σ src)).2) :=
        fun i w ht hr => hlaw i w ht (Or.inr hr)
      have hrhs : compiled env (ρ.apply (.call j dst src :: p)) σ =
          (compiled env (ρ.apply p) (σ.upd dst (env.impl j (σ src)).2)).map
            (Beh.prepend (env.impl j (σ src)).1) := by
        cases ht : ρ.targets j with
        | false => simp [Rewrite.apply, Rewrite.rwStmt, ht, compiled, exec, compiledCalls]
        | true =>
          have hj : env.impl j (σ src) = ρ.repl j (σ src) := hlaw j (σ src) ht (Or.inl ⟨rfl, rfl⟩)
          simp [Rewrite.apply, Rewrite.rwStmt, ht, compiled, exec, ← hj]
      rw [hrhs]; unfold capDirect; simp only [exec, directCalls]
      cases hs : env.safety j with
      | safeTrait =>
        simp only [List.flatMap_singleton]
        exact refinesPP_map_prepend (env.impl j (σ src)).1 (ih _ htail)
      | unsafeTrait =>
        by_cases hc : env.impl j (σ src) = env.contract j (σ src)
        · simp only [ite_eq_left_iff.mpr (fun hne => absurd hc hne), List.flatMap_singleton]
          exact refinesPP_map_prepend (env.impl j (σ src)).1 (ih _ htail)
        · simp only [ite_eq_right_iff.mpr (fun heq => absurd heq hc)]
          cases pos with
          | before => simp only [List.flatMap_singleton]; exact refinesPP_ub_of_prefix List.nil_prefix _
          | after => simp only [List.flatMap_singleton]; exact refinesPP_ub_of_prefix (List.prefix_refl _) _

/-- **Exactly when, over all contexts.** The rewrite `ρ` refines the direct capture on
every program and every initial store iff `ContextSafeAt env pos ρ i v` holds at every
targeted instance `i` and every argument `v`: the law holds at `v`, or `i` is unsafe,
its impl violates the contract at `v`, and the relies point precedes every divergence
(`before`, or `after` with the impl's effects a prefix of the replacement's). -/
theorem refinesPP_every_context_iff_contextSafeAt (env : Env) (pos : RelyPos)
    (ρ : Rewrite) :
    (∀ (p : Prog) (σ : Store),
        RefinesPP (capDirect env pos p σ) (compiled env (ρ.apply p) σ)) ↔
      ∀ i, ρ.targets i = true → ∀ v, ContextSafeAt env pos ρ i v := by
  constructor
  · intro hall i ht v
    let σ₀ : Store := fun _ => 0
    cases hs : env.safety i with
    | safeTrait => exact Or.inl (lawAt_of_refinesPP_probe_aux env pos ρ i v σ₀ hs ht (hall (probe i v) σ₀))
    | unsafeTrait =>
      by_cases hc : env.impl i v = env.contract i v
      · have hprobe := hall (probe i v) σ₀
        have hsrc : capDirect env pos (probe i v) σ₀ =
            [.done ((env.impl i v).1 ++ [(env.impl i v).2])] := by
          simp [capDirect, probe, exec, directCalls, hs, hc, Store.upd, Beh.prepend]
        have htgt : compiled env (ρ.apply (probe i v)) σ₀ =
            [.done ((ρ.repl i v).1 ++ [(ρ.repl i v).2])] := by
          simp [compiled, probe, Rewrite.apply, Rewrite.rwStmt, ht, exec, Store.upd, Beh.prepend]
        rw [hsrc, htgt] at hprobe
        rcases hprobe _ (List.mem_singleton.mpr rfl) with ⟨bs, hbs, himp⟩
        rw [List.mem_singleton] at hbs; subst hbs
        rcases himp with heq | ⟨t, hbad, _⟩
        · injection heq with htr
          obtain ⟨heff, hret⟩ := list_snoc_inj htr.symm
          exact Or.inl (Prod.ext heff hret)
        · cases hbad
      · cases pos with
        | before => exact Or.inr ⟨hs, hc, Or.inl rfl⟩
        | after =>
          have hdead := hall [.set 0 v, .call i 1 0] σ₀
          have hsrc : capDirect env .after [.set 0 v, .call i 1 0] σ₀ = [.ub (env.impl i v).1] := by
            simp [capDirect, exec, directCalls, hs, hc, Store.upd]
          have htgt : compiled env (ρ.apply [.set 0 v, .call i 1 0]) σ₀ = [.done (ρ.repl i v).1] := by
            simp [compiled, Rewrite.apply, Rewrite.rwStmt, ht, exec, Store.upd, Beh.prepend]
          rw [hsrc, htgt] at hdead
          rcases hdead (.done (ρ.repl i v).1) (List.mem_singleton.mpr rfl) with ⟨bs, hbs, himp⟩
          rw [List.mem_singleton] at hbs; subst hbs
          rcases himp with heq | ⟨t, hub, hp⟩
          · cases heq
          · injection hub with hteq; subst hteq; exact Or.inr ⟨hs, hc, Or.inr hp⟩
  · intro hctx p
    induction p with
    | nil => intro σ; exact refinesPP_refl _
    | cons s p ih =>
      intro σ
      cases s with
      | set x v => exact ih (σ.upd x v)
      | out x => exact refinesPP_map_prepend [σ x] (ih σ)
      | prim f dst src => exact refinesPP_map_prepend (f (σ src)).1 (ih _)
      | ub => exact refinesPP_refl _
      | call j dst src =>
        cases ht : ρ.targets j with
        | false =>
          have hrhs : compiled env (ρ.apply (.call j dst src :: p)) σ =
              (compiled env (ρ.apply p) (σ.upd dst (env.impl j (σ src)).2)).map
                (Beh.prepend (env.impl j (σ src)).1) := by
            simp [Rewrite.apply, Rewrite.rwStmt, ht, compiled, exec, compiledCalls]
          rw [hrhs]; unfold capDirect; simp only [exec, directCalls]
          cases hs : env.safety j with
          | safeTrait => simp only [List.flatMap_singleton]; exact refinesPP_map_prepend _ (ih _)
          | unsafeTrait =>
            by_cases hc : env.impl j (σ src) = env.contract j (σ src)
            · simp only [ite_eq_left_iff.mpr (fun hne => absurd hc hne), List.flatMap_singleton]
              exact refinesPP_map_prepend _ (ih _)
            · simp only [ite_eq_right_iff.mpr (fun heq => absurd heq hc)]
              cases pos with
              | before => simp only [List.flatMap_singleton]; exact refinesPP_ub_of_prefix List.nil_prefix _
              | after => simp only [List.flatMap_singleton]; exact refinesPP_ub_of_prefix (List.prefix_refl _) _
        | true =>
          have hrhs : compiled env (ρ.apply (.call j dst src :: p)) σ =
              (compiled env (ρ.apply p) (σ.upd dst (ρ.repl j (σ src)).2)).map
                (Beh.prepend (ρ.repl j (σ src)).1) := by
            simp [Rewrite.apply, Rewrite.rwStmt, ht, compiled, exec]
          rw [hrhs]; unfold capDirect; simp only [exec, directCalls]
          rcases hctx j ht (σ src) with hlaw | ⟨hs, hc, hpos⟩
          · rw [← hlaw]
            cases env.safety j with
            | safeTrait => simp only [List.flatMap_singleton]; exact refinesPP_map_prepend _ (ih _)
            | unsafeTrait =>
              by_cases hci : env.impl j (σ src) = env.contract j (σ src)
              · simp only [ite_eq_left_iff.mpr (fun hne => absurd hci hne), List.flatMap_singleton]
                exact refinesPP_map_prepend _ (ih _)
              · simp only [ite_eq_right_iff.mpr (fun heq => absurd heq hci)]
                cases pos with
                | before => simp only [List.flatMap_singleton]; exact refinesPP_ub_of_prefix List.nil_prefix _
                | after => simp only [List.flatMap_singleton]; exact refinesPP_ub_of_prefix (List.prefix_refl _) _
          · simp only [hs, ite_eq_right_iff.mpr (fun heq => absurd heq hc)]
            rcases hpos with rfl | hpref
            · simp only [List.flatMap_singleton]; exact refinesPP_ub_of_prefix List.nil_prefix _
            · cases pos with
              | before => simp only [List.flatMap_singleton]; exact refinesPP_ub_of_prefix List.nil_prefix _
              | after => simp only [List.flatMap_singleton]; exact refinesPP_ub_of_prefix hpref _

/-- **Safe trait: refinement on the probe forces the law.** For a targeted instance `i`
of a safe trait, if the rewrite refines the direct capture on the probe context
`probe i v` from some store, then the law holds at `v`. -/
theorem lawAt_of_refinesPP_probe_of_safe_of_targets (env : Env) (pos : RelyPos)
    (ρ : Rewrite) (i : Inst) (v : Val) (σ : Store) (hsafe : env.safety i = .safeTrait)
    (ht : ρ.targets i = true)
    (href : RefinesPP (capDirect env pos (probe i v) σ)
      (compiled env (ρ.apply (probe i v)) σ)) :
    LawAt env ρ i v :=
  lawAt_of_refinesPP_probe_aux env pos ρ i v σ hsafe ht href

/-- **Unsafe trait, relies point before the impl: no law hypothesis.** If every
instance `ρ` targets belongs to an unsafe trait and `ρ` substitutes exactly the
contract's behaviour, then for every program and store the compiled rewritten program
refines the direct capture with the relies point `before` (prefix-preserving). -/
theorem refinesPP_capDirect_before_apply_of_targetsUnsafe_of_replIsContract (env : Env)
    (ρ : Rewrite) (p : Prog) (σ : Store) (hunsafe : TargetsUnsafe env ρ)
    (hrepl : ReplIsContract env ρ) :
    RefinesPP (capDirect env .before p σ) (compiled env (ρ.apply p) σ) := by
  apply (refinesPP_every_context_iff_contextSafeAt env .before ρ).mpr
  intro i ht v
  by_cases hc : env.impl i v = env.contract i v
  · exact Or.inl (by rw [LawAt, hc, hrepl i ht])
  · exact Or.inr ⟨hunsafe i ht, hc, Or.inl rfl⟩

/-- **Unsafe trait under whole-trace UB: no law hypothesis, either relies position.**
Under the same hypotheses, for either relies position, the compiled rewritten program
refines the direct capture in the whole-trace sense. -/
theorem refinesWT_capDirect_apply_of_targetsUnsafe_of_replIsContract (env : Env)
    (pos : RelyPos) (ρ : Rewrite) (p : Prog) (σ : Store) (hunsafe : TargetsUnsafe env ρ)
    (hrepl : ReplIsContract env ρ) :
    RefinesWT (capDirect env pos p σ) (compiled env (ρ.apply p) σ) := by
  induction p generalizing σ with
  | nil => exact fun b hb => ⟨b, hb, Or.inl rfl⟩
  | cons s p ih =>
    cases s with
    | set x v => exact ih (σ.upd x v)
    | out x => exact refinesWT_map_prepend [σ x] (ih σ)
    | prim f dst src => exact refinesWT_map_prepend (f (σ src)).1 (ih _)
    | ub => exact fun b hb => ⟨b, hb, Or.inl rfl⟩
    | call j dst src =>
      cases ht : ρ.targets j with
      | false =>
        have hrhs : compiled env (ρ.apply (.call j dst src :: p)) σ =
            (compiled env (ρ.apply p) (σ.upd dst (env.impl j (σ src)).2)).map
              (Beh.prepend (env.impl j (σ src)).1) := by
          simp [Rewrite.apply, Rewrite.rwStmt, ht, compiled, exec, compiledCalls]
        rw [hrhs]; unfold capDirect; simp only [exec, directCalls]
        cases hs : env.safety j with
        | safeTrait => simp only [List.flatMap_singleton]; exact refinesWT_map_prepend _ (ih _)
        | unsafeTrait =>
          by_cases hc : env.impl j (σ src) = env.contract j (σ src)
          · simp only [ite_eq_left_iff.mpr (fun hne => absurd hc hne), List.flatMap_singleton]
            exact refinesWT_map_prepend _ (ih _)
          · simp only [ite_eq_right_iff.mpr (fun heq => absurd heq hc)]
            cases pos <;> exact fun bt _ => ⟨_, List.mem_singleton.mpr rfl, Or.inr ⟨_, rfl⟩⟩
      | true =>
        have hs := hunsafe j ht; have hr := hrepl j ht
        have hrhs : compiled env (ρ.apply (.call j dst src :: p)) σ =
            (compiled env (ρ.apply p) (σ.upd dst (env.contract j (σ src)).2)).map
              (Beh.prepend (env.contract j (σ src)).1) := by
          simp [Rewrite.apply, Rewrite.rwStmt, ht, hr, compiled, exec]
        rw [hrhs]; unfold capDirect; simp only [exec, directCalls, hs]
        by_cases hc : env.impl j (σ src) = env.contract j (σ src)
        · simp only [ite_eq_left_iff.mpr (fun hne => absurd hc hne), List.flatMap_singleton]
          rw [hc]; exact refinesWT_map_prepend _ (ih _)
        · simp only [ite_eq_right_iff.mpr (fun heq => absurd heq hc)]
          cases pos <;> exact fun bt _ => ⟨_, List.mem_singleton.mpr rfl, Or.inr ⟨_, rfl⟩⟩

/-! ## Verification of the direct capture of unsafe calls -/

/-- **UB-free verification transfers through an unsafe-contract rewrite.** If every
instance `ρ` targets belongs to an unsafe trait, `ρ` substitutes exactly the contract's
behaviour, and `spec` is satisfied by no UB behaviour, then `spec` verified of the
direct capture of `p` (either relies position) holds of the compiled rewritten
program. -/
theorem sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect
    (env : Env) (pos : RelyPos) (ρ : Rewrite) (p : Prog) (σ : Store) (spec : Beh → Prop)
    (hunsafe : TargetsUnsafe env ρ) (hrepl : ReplIsContract env ρ)
    (hub : UBFreeSpec spec) (hsat : Sat (capDirect env pos p σ) spec) :
    Sat (compiled env (ρ.apply p) σ) spec := by
  intro bt hbt
  rcases refinesWT_capDirect_apply_of_targetsUnsafe_of_replIsContract env pos ρ p σ hunsafe hrepl bt hbt with
    ⟨bs, hbs, rfl | ⟨t, rfl⟩⟩
  · exact hsat bt hbs
  · exact absurd (hsat (.ub t) hbs) (hub t)

/-- **UB-free verification discharges the contract at every reached unsafe call.** For
any instance `i` and argument `v`, if `i` belongs to an unsafe trait, the law-free
execution of `p` from `σ` reaches a call of `i` with argument `v`, `spec` is satisfied
by no UB behaviour, and `spec` holds of the direct capture of `p` from `σ` (either
relies position), then the impl of `i` agrees with the contract at `v`. -/
theorem contract_at_reached_unsafe_of_sat_capDirect_of_ubFreeSpec (env : Env)
    (pos : RelyPos) (p : Prog) (σ : Store) (spec : Beh → Prop) (i : Inst) (v : Val)
    (hunsafe : env.safety i = .unsafeTrait) (hreach : Reaches env p σ i v)
    (hub : UBFreeSpec spec) (hsat : Sat (capDirect env pos p σ) spec) :
    env.impl i v = env.contract i v := by
  induction p generalizing σ spec with
  | nil => cases hreach
  | cons s p ih =>
    have map_step : ∀ (e : List Val) (σ' : Store),
        Sat ((capDirect env pos p σ').map (Beh.prepend e)) spec →
        Reaches env p σ' i v → env.impl i v = env.contract i v := by
      intro e σ' hsat' hr'
      refine ih σ' (fun b => spec (Beh.prepend e b)) hr' (fun t => hub (e ++ t)) ?_
      intro b hb
      exact hsat' (Beh.prepend e b) (List.mem_map.mpr ⟨b, hb, rfl⟩)
    cases s with
    | set x w => exact ih (σ.upd x w) spec hreach hub hsat
    | out x => exact map_step [σ x] σ hsat hreach
    | prim f dst src => exact map_step (f (σ src)).1 (σ.upd dst (f (σ src)).2) hsat hreach
    | ub => cases hreach
    | call j dst src =>
      unfold capDirect at hsat; simp only [exec, directCalls] at hsat
      cases hs : env.safety j with
      | safeTrait =>
        simp only [hs, List.flatMap_singleton] at hsat
        rcases hreach with ⟨rfl, rfl⟩ | hr'
        · rw [hs] at hunsafe; cases hunsafe
        · exact map_step (env.impl j (σ src)).1 (σ.upd dst (env.impl j (σ src)).2) hsat hr'
      | unsafeTrait =>
        simp only [hs] at hsat
        by_cases hc : env.impl j (σ src) = env.contract j (σ src)
        · simp only [ite_eq_left_iff.mpr (fun hne => absurd hc hne), List.flatMap_singleton] at hsat
          rcases hreach with ⟨rfl, rfl⟩ | hr'
          · exact hc
          · exact map_step (env.impl j (σ src)).1 (σ.upd dst (env.impl j (σ src)).2) hsat hr'
        · simp only [ite_eq_right_iff.mpr (fun heq => absurd heq hc)] at hsat
          cases pos with
          | before => exact absurd (hsat (.ub []) (List.mem_singleton.mpr rfl)) (hub [])
          | after => exact absurd (hsat (.ub _) (List.mem_singleton.mpr rfl)) (hub _)

/-! ## Relational capture -/

private theorem applyAt_congr_ge (ρ : Rewrite) {S₁ S₂ : Nat → Bool} (k : Nat) (p : Prog)
    (h : ∀ n, k ≤ n → S₁ n = S₂ n) :
    ρ.applyAt S₁ k p = ρ.applyAt S₂ k p := by
  induction p generalizing k with
  | nil => rfl
  | cons s p ih =>
    simp only [Rewrite.applyAt, h k (Nat.le_refl k)]
    congr 1
    exact ih (k + 1) (fun n hn => h n (Nat.le_of_succ_le hn))

private theorem mem_capRel_iff_exists_applyAt_at (env : Env) (ρ : Rewrite) :
    ∀ (p : Prog) (k : Nat) (σ : Store) (b : Beh),
      b ∈ capRel env [ρ] p σ ↔
        ∃ S : Nat → Bool, b ∈ compiled env (ρ.applyAt S k p) σ := by
  intro p
  induction p with
  | nil => intro k σ b; exact ⟨fun hb => ⟨fun _ => false, hb⟩, fun ⟨_, hb⟩ => hb⟩
  | cons s p ih =>
    intro k σ b
    have non_call : ∀ (hnc : ∀ c : Bool, (if c then ρ.rwStmt s else s) = s),
        (b ∈ capRel env [ρ] (s :: p) σ ↔
          ∃ S : Nat → Bool, b ∈ compiled env (ρ.applyAt S k (s :: p)) σ) := by
      intro hnc
      cases s with
      | set x v => simp only [capRel, compiled, Rewrite.applyAt, hnc, exec]; exact ih (k + 1) (σ.upd x v) b
      | out x =>
        simp only [capRel, compiled, Rewrite.applyAt, hnc, exec, List.mem_map]
        exact ⟨fun ⟨b0, hb0, h⟩ => let ⟨S, hS⟩ := (ih (k + 1) σ b0).mp hb0; ⟨S, b0, hS, h⟩,
          fun ⟨S, b0, hS, h⟩ => ⟨b0, (ih (k + 1) σ b0).mpr ⟨S, hS⟩, h⟩⟩
      | prim f dst src =>
        simp only [capRel, compiled, Rewrite.applyAt, hnc, exec, List.mem_map]
        exact ⟨fun ⟨b0, hb0, h⟩ => let ⟨S, hS⟩ := (ih (k + 1) _ b0).mp hb0; ⟨S, b0, hS, h⟩,
          fun ⟨S, b0, hS, h⟩ => ⟨b0, (ih (k + 1) _ b0).mpr ⟨S, hS⟩, h⟩⟩
      | ub => simp only [capRel, compiled, Rewrite.applyAt, hnc, exec]; exact ⟨fun hb => ⟨fun _ => false, hb⟩, fun ⟨_, hb⟩ => hb⟩
      | call j dst src =>
        have ht : ρ.targets j = false := by
          cases ht : ρ.targets j with
          | false => rfl
          | true => have := hnc true; simp [Rewrite.rwStmt, ht] at this
        simp only [capRel, compiled, Rewrite.applyAt, hnc, exec, relCalls, List.filterMap_cons,
          List.filterMap_nil, ht, Bool.false_eq_true, ↓reduceIte, compiledCalls,
          List.flatMap_singleton, List.mem_map]
        exact ⟨fun ⟨b0, hb0, h⟩ => let ⟨S, hS⟩ := (ih (k + 1) _ b0).mp hb0; ⟨S, b0, hS, h⟩,
          fun ⟨S, b0, hS, h⟩ => ⟨b0, (ih (k + 1) _ b0).mpr ⟨S, hS⟩, h⟩⟩
    cases s with
    | set x v => exact non_call (fun c => by cases c <;> rfl)
    | out x => exact non_call (fun c => by cases c <;> rfl)
    | prim f dst src => exact non_call (fun c => by cases c <;> rfl)
    | ub => exact non_call (fun c => by cases c <;> rfl)
    | call j dst src =>
      cases ht : ρ.targets j with
      | false => exact non_call (fun c => by cases c <;> simp [Rewrite.rwStmt, ht])
      | true =>
        simp only [capRel, exec, relCalls, List.filterMap_cons, List.filterMap_nil, ht, ↓reduceIte,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, List.mem_map]
        constructor
        · rintro (⟨b0, hb0, rfl⟩ | ⟨b0, hb0, rfl⟩)
          · obtain ⟨S', hS'⟩ := (ih (k + 1) (σ.upd dst (env.impl j (σ src)).2) b0).mp hb0
            let S : Nat → Bool := fun n => if n = k then false else S' n
            refine ⟨S, ?_⟩
            have htail : ρ.applyAt S (k + 1) p = ρ.applyAt S' (k + 1) p :=
              applyAt_congr_ge ρ (k + 1) p (fun n hn => ite_eq_right_iff.mpr (fun heq => absurd heq (Nat.ne_of_gt hn)))
            have hhead : S k = false := ite_eq_left_iff.mpr (fun hne => absurd rfl hne)
            simp only [Rewrite.applyAt, hhead, Bool.false_eq_true, ↓reduceIte, htail,
              compiled, exec, compiledCalls, List.flatMap_singleton, List.mem_map]
            exact ⟨b0, hS', rfl⟩
          · obtain ⟨S', hS'⟩ := (ih (k + 1) (σ.upd dst (ρ.repl j (σ src)).2) b0).mp hb0
            let S : Nat → Bool := fun n => if n = k then true else S' n
            refine ⟨S, ?_⟩
            have htail : ρ.applyAt S (k + 1) p = ρ.applyAt S' (k + 1) p :=
              applyAt_congr_ge ρ (k + 1) p (fun n hn => ite_eq_right_iff.mpr (fun heq => absurd heq (Nat.ne_of_gt hn)))
            have hhead : S k = true := ite_eq_left_iff.mpr (fun hne => absurd rfl hne)
            simp only [Rewrite.applyAt, hhead, ↓reduceIte, Rewrite.rwStmt, ht, htail,
              compiled, exec, List.mem_map]
            exact ⟨b0, hS', rfl⟩
        · rintro ⟨S, hS⟩
          cases hSk : S k with
          | false =>
            simp only [compiled, Rewrite.applyAt, hSk, Bool.false_eq_true, ↓reduceIte,
              exec, compiledCalls, List.flatMap_singleton, List.mem_map] at hS
            obtain ⟨b0, hb0, rfl⟩ := hS
            exact Or.inl ⟨b0, (ih (k + 1) _ b0).mpr ⟨S, hb0⟩, rfl⟩
          | true =>
            simp only [compiled, Rewrite.applyAt, hSk, ↓reduceIte, Rewrite.rwStmt, ht,
              exec, List.mem_map] at hS
            obtain ⟨b0, hb0, rfl⟩ := hS
            exact Or.inr ⟨b0, (ih (k + 1) _ b0).mpr ⟨S, hb0⟩, rfl⟩

/-- **Relational capture is sound for every partial application.** For every site
selection `S`, a specification verified of the relational capture of `p` for `[ρ]`
holds of the compiled program with `ρ` applied at exactly the selected sites. No law
is assumed. -/
theorem sat_compiled_applyAt_of_sat_capRel (env : Env) (ρ : Rewrite) (p : Prog)
    (σ : Store) (spec : Beh → Prop) (hsat : Sat (capRel env [ρ] p σ) spec)
    (S : Nat → Bool) :
    Sat (compiled env (ρ.applyAt S 0 p) σ) spec :=
  fun b hb => hsat b ((mem_capRel_iff_exists_applyAt_at env ρ p 0 σ b).mpr ⟨S, hb⟩)

/-- The two extreme selections of `sat_compiled_applyAt_of_sat_capRel`: a specification
verified of the relational capture holds of the compiled program whether `ρ` is not
applied or applied at every site. -/
theorem sat_compiled_and_apply_of_sat_capRel (env : Env) (ρ : Rewrite) (p : Prog)
    (σ : Store) (spec : Beh → Prop) (hsat : Sat (capRel env [ρ] p σ) spec) :
    Sat (compiled env p σ) spec ∧ Sat (compiled env (ρ.apply p) σ) spec := by
  constructor
  · have h := sat_compiled_applyAt_of_sat_capRel env ρ p σ spec hsat (fun _ => false)
    rwa [applyAt_const_false] at h
  · have h := sat_compiled_applyAt_of_sat_capRel env ρ p σ spec hsat (fun _ => true)
    rwa [applyAt_const_true] at h

/-- **Relational capture is the union of the per-site partial applications.** A
behaviour belongs to the relational capture of `p` for `[ρ]` iff it is a behaviour of
the compiled program with `ρ` applied at the sites of some selection `S`. -/
theorem mem_capRel_iff_exists_applyAt (env : Env) (ρ : Rewrite) (p : Prog) (σ : Store)
    (b : Beh) :
    b ∈ capRel env [ρ] p σ ↔ ∃ S : Nat → Bool, b ∈ compiled env (ρ.applyAt S 0 p) σ :=
  mem_capRel_iff_exists_applyAt_at env ρ p 0 σ b

/-- **Relational capture is the weakest semantics sound for per-site rewriting.** Every
behaviour set `D` such that each specification true of all of `D` holds of the
compiled program under every site selection contains every behaviour of the
relational capture. -/
theorem capRel_subset_of_sound_for_every_applyAt (env : Env) (ρ : Rewrite) (p : Prog)
    (σ : Store) (D : Beh → Prop)
    (hD : ∀ spec : Beh → Prop, (∀ b, D b → spec b) →
      ∀ S : Nat → Bool, Sat (compiled env (ρ.applyAt S 0 p) σ) spec) :
    ∀ b ∈ capRel env [ρ] p σ, D b :=
  fun b hb =>
    let ⟨S, hS⟩ := (mem_capRel_iff_exists_applyAt env ρ p σ b).mp hb
    hD D (fun _ h => h) S b hS

/-! ## Fail-closed rejection of rewritable calls -/

/-- The compiled semantics as a denotation over runs `(initial store, behaviour)`. -/
def compiledDen (env : Env) (p : Prog) : Den (Store × Beh) :=
  fun r => r.2 ∈ compiled env p r.1

/-- The direct-capture semantics as a denotation over runs `(initial store, behaviour)`. -/
def capDirectDen (env : Env) (pos : RelyPos) (p : Prog) : Den (Store × Beh) :=
  fun r => r.2 ∈ capDirect env pos p r.1

/-- The fail-closed capture that rejects every program containing a call of an
instance `i` with `R i = true`, and captures every other program unchanged. -/
def capRejectRewritable (R : Inst → Bool) : Prog → Except Unit Prog :=
  failClosed (fun p => callsSome R p = false) id ()

private theorem apply_eq_self_of_callsSome_false (R : Inst → Bool) (ρ : Rewrite)
    (hR : ∀ i, ρ.targets i = true → R i = true) (p : Prog) (hp : callsSome R p = false) :
    ρ.apply p = p := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    cases s with
    | call i dst src =>
      simp only [callsSome, List.any_cons, Bool.or_eq_false_iff] at hp
      have ht : ρ.targets i = false := by
        cases ht : ρ.targets i with
        | false => rfl
        | true => rw [hR i ht] at hp; cases hp.1
      simp only [Rewrite.apply, List.map_cons, Rewrite.rwStmt, ht, Bool.false_eq_true, ↓reduceIte]
      exact congrArg (List.cons _) (ih hp.2)
    | set _ _ | out _ | prim _ _ _ | ub =>
      simp only [callsSome, List.any_cons, Bool.false_or] at hp
      exact congrArg (List.cons _) (ih hp)

/-- **Rejecting rewritable calls at capture is sound for `compiledDen`.** If every
instance `ρ` targets satisfies `R`, then for every verifier sound for the law-free
direct semantics (`compiledDen env`), verification transfers through
`capRejectRewritable R` to the compiled program rewritten by `ρ` (instantiating
`CaptureBridge`'s `semS` with `fun p => compiledDen env (ρ.apply p)` and `semV` with
`compiledDen env`). -/
theorem capRejectRewritable_compiledDen_transferSound (env : Env) (R : Inst → Bool)
    (ρ : Rewrite) (hR : ∀ i, ρ.targets i = true → R i = true)
    (verified : Prog → (Store × Beh → Prop) → Prop)
    (hV : VerifierSound (compiledDen env) verified) :
    TransferSound (fun p => compiledDen env (ρ.apply p)) (capRejectRewritable R) verified := by
  intro p q spec hok hver
  have hover := (CaptureBridge.failClosed_overApproxOnOk_iff
    (fun p => compiledDen env (ρ.apply p)) (compiledDen env)
    (fun p => callsSome R p = false) id ()).mpr (by
      intro p0 hp0 r hr; rw [apply_eq_self_of_callsSome_false R ρ hR p0 hp0] at hr; exact hr)
  exact CaptureBridge.transfer_to_capture_input _ _ _ _ hV hover hok hver

/-! ## Sequences of rewrites -/

/-- **A sequence refines when each law holds at its reached calls.** If, for every
rewrite of the list `ρs`, its law holds at every call of a targeted instance that the
execution of `p` from `σ` reaches, then the compiled program obtained by applying the
rewrites in order refines the direct capture of `p` (either relies position). -/
theorem refinesPP_capDirect_applySeq_of_lawOnReached (env : Env) (pos : RelyPos)
    (ρs : List Rewrite) (p : Prog) (σ : Store) (hlaw : ∀ ρ ∈ ρs, LawOnReached env ρ p σ) :
    RefinesPP (capDirect env pos p σ) (compiled env (applySeq ρs p) σ) := by
  rw [applySeq_eq_firstMatch]
  apply refinesPP_capDirect_apply_of_lawOnReached env pos (firstMatch ρs) p σ
  intro i v hfm hr
  simp only [firstMatch, List.any_eq_true] at hfm
  rcases hfn : ρs.find? (fun ρ => ρ.targets i) with _ | ρ₀
  · exfalso; obtain ⟨ρ₁, hmem, ht₁⟩ := hfm; exact List.find?_eq_none.mp hfn ρ₁ hmem ht₁
  · have hmem : ρ₀ ∈ ρs := List.mem_of_find?_eq_some hfn
    have ht₀ : ρ₀.targets i = true := find?_pred (fun ρ => ρ.targets i) ρs hfn
    have hrepl : (firstMatch ρs).repl i = ρ₀.repl i := by simp [firstMatch, hfn]
    unfold LawAt; rw [hrepl]; exact hlaw ρ₀ hmem i v ht₀ hr

private theorem find?_eq_of_pairwise_disjoint {ρs : List Rewrite}
    (hdisj : ρs.Pairwise TargetsDisjoint) {ρ : Rewrite} (hmem : ρ ∈ ρs) {i : Inst}
    (ht : ρ.targets i = true) : ρs.find? (fun r => r.targets i) = some ρ := by
  induction hdisj with
  | nil => cases hmem
  | @cons a l hrel _ ih =>
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · simp [ht]
    · have ha : a.targets i = false := by
        cases ha : a.targets i with
        | false => rfl
        | true => have := hrel ρ hmem' i ha; rw [ht] at this; cases this
      simp [ha, ih hmem']

/-- **Disjoint sequences: exactly when, over all contexts.** If no two rewrites of `ρs`
target a common instance, the sequence refines the direct capture on every program and
store iff every rewrite of the list satisfies `ContextSafeAt` at every instance it
targets and every argument. -/
theorem refinesPP_every_context_applySeq_iff_of_pairwise_disjoint (env : Env)
    (pos : RelyPos) (ρs : List Rewrite) (hdisj : ρs.Pairwise TargetsDisjoint) :
    (∀ (p : Prog) (σ : Store),
        RefinesPP (capDirect env pos p σ) (compiled env (applySeq ρs p) σ)) ↔
      ∀ ρ ∈ ρs, ∀ i, ρ.targets i = true → ∀ v, ContextSafeAt env pos ρ i v := by
  simp only [applySeq_eq_firstMatch, refinesPP_every_context_iff_contextSafeAt]
  constructor
  · intro h ρ hmem i ht v
    have hfn := find?_eq_of_pairwise_disjoint hdisj hmem ht
    have hfm_t : (firstMatch ρs).targets i = true := List.any_eq_true.mpr ⟨ρ, hmem, ht⟩
    have hrepl : (firstMatch ρs).repl i = ρ.repl i := by simp [firstMatch, hfn]
    have hctx := h i hfm_t v; unfold ContextSafeAt LawAt at hctx ⊢; rwa [hrepl] at hctx
  · intro h i hfm_t v
    rcases hfn : ρs.find? (fun r => r.targets i) with _ | ρ₀
    · exfalso; simp only [firstMatch, List.any_eq_true] at hfm_t
      obtain ⟨ρ₁, hmem, ht₁⟩ := hfm_t; exact List.find?_eq_none.mp hfn ρ₁ hmem ht₁
    · have hmem : ρ₀ ∈ ρs := List.mem_of_find?_eq_some hfn
      have ht₀ : ρ₀.targets i = true := find?_pred (fun r => r.targets i) ρs hfn
      have hrepl : (firstMatch ρs).repl i = ρ₀.repl i := by simp [firstMatch, hfn]
      have hctx := h ρ₀ hmem i ht₀ v; unfold ContextSafeAt LawAt at hctx ⊢; rwa [hrepl]

/-- **Relational capture of a list of rewrites covers every covered sequence.** If every
replacement of every rewrite in `ρs'` is the replacement of some rewrite of `ρs` at the
same instance, then every compiled behaviour of `applySeq ρs' p` is a behaviour of the
relational capture of `p` for `ρs`. -/
theorem mem_capRel_of_mem_compiled_applySeq_of_coveredBy (env : Env)
    (ρs ρs' : List Rewrite) (p : Prog) (σ : Store) (hcov : ∀ ρ ∈ ρs', CoveredBy ρs ρ) :
    ∀ b ∈ compiled env (applySeq ρs' p) σ, b ∈ capRel env ρs p σ := by
  rw [applySeq_eq_firstMatch]
  have hcov_fm : CoveredBy ρs (firstMatch ρs') := by
    intro i hfm_t
    rcases hfn : ρs'.find? (fun r => r.targets i) with _ | ρ₀
    · exfalso; simp only [firstMatch, List.any_eq_true] at hfm_t
      obtain ⟨ρ₁, hmem, ht₁⟩ := hfm_t; exact List.find?_eq_none.mp hfn ρ₁ hmem ht₁
    · have ht₀ : ρ₀.targets i = true := find?_pred (fun r => r.targets i) ρs' hfn
      obtain ⟨ρ', hmem', ht', hrepl'⟩ := hcov ρ₀ (List.mem_of_find?_eq_some hfn) i ht₀
      exact ⟨ρ', hmem', ht', by simp [firstMatch, hfn, hrepl']⟩
  induction p generalizing σ with
  | nil => intro b hb; exact hb
  | cons s p ih =>
    intro b hb
    cases s with
    | set x v => exact ih (σ.upd x v) b hb
    | out x => rcases List.mem_map.mp hb with ⟨b0, hb0, rfl⟩; exact List.mem_map.mpr ⟨b0, ih σ b0 hb0, rfl⟩
    | prim f dst src => rcases List.mem_map.mp hb with ⟨b0, hb0, rfl⟩; exact List.mem_map.mpr ⟨b0, ih _ b0 hb0, rfl⟩
    | ub => exact hb
    | call i dst src =>
      cases ht : (firstMatch ρs').targets i with
      | false =>
        simp only [Rewrite.apply, List.map_cons, Rewrite.rwStmt, ht, Bool.false_eq_true,
          ↓reduceIte, compiled, exec, compiledCalls, List.flatMap_singleton, List.mem_map] at hb
        obtain ⟨b0, hb0, rfl⟩ := hb
        simp only [capRel, exec, relCalls, List.flatMap_cons, List.mem_append, List.mem_map]
        exact Or.inl ⟨b0, ih _ b0 hb0, rfl⟩
      | true =>
        simp only [Rewrite.apply, List.map_cons, Rewrite.rwStmt, ht, ↓reduceIte,
          compiled, exec, List.mem_map] at hb
        obtain ⟨b0, hb0, rfl⟩ := hb
        obtain ⟨ρ', hmem', ht', hrepl'⟩ := hcov_fm i ht
        simp only [capRel, exec, relCalls, List.flatMap_cons, List.mem_append]
        refine Or.inr (List.mem_flatMap.mpr ⟨.ret ((firstMatch ρs').repl i (σ src)), ?_, ?_⟩)
        · rw [List.mem_filterMap]; exact ⟨ρ', hmem', by simp [ht', hrepl']⟩
        · exact List.mem_map.mpr ⟨b0, ih _ b0 hb0, rfl⟩

end Toy.LawRewrite
