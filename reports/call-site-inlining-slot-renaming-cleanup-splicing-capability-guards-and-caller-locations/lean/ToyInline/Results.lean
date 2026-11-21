import ToyInline.Simulation

/-!
# Main results (statements)

Each statement names its hypotheses separately. All statements in this file are proved. The
four whole-program inlining theorems (`inline_behEquiv_retTemp_of_capsEq`,
`inline_behEquiv_retDest_of_destUnobservedOnUnwind`,
`inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive`,
`inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree`) are proved by the stuttering forward
simulation in `ToyInline/Simulation.lean` (`InlineSim.Site.behEquiv_of_hyps`): every step of the
original program is matched by one or more steps of the inlined program with the same events.

These are statements about the toy model; they neither establish nor refute the corresponding
claims about any real compiler. Model–system relation: none proved.
-/

namespace Toy.Inline

/-! ## Slot renaming and return-place substitution -/

/-- **Frame relation, one statement step (store level).** If the renaming `ρ` is injective on
the callee locals below `n` and avoids the caller locals `L` that are live across the call, the
statement mentions only callee locals below `n`, and the frame relation holds before the step,
then executing the statement on the callee store and its renaming on the merged store with the
auxiliary store-level function `stmtStore` preserves the frame relation and produces the same
list of emitted values. `stmtStore` ignores `needCap` faults and `loc` events; the scope shift
`ns` only affects `loc` statements, so the statement holds for every `ns`. -/
theorem frameRel_step_of_injective_of_avoids
    (ρ : Nat → Local) (n : Nat) (L : List Local) (C G M : Local → Nat) (s : Stmt) (ns : Nat)
    (hinj : RenameInjectiveOn ρ n) (havoid : RenameAvoids ρ n L)
    (hs : StmtLocalsLt n s) (hR : FrameRel ρ n L C G M) :
    FrameRel ρ n L C (stmtStore G s).1 (stmtStore M (s.rename ρ ns)).1 ∧
      (stmtStore M (s.rename ρ ns)).2 = (stmtStore G s).2 := by
  have evalOp_eq : ∀ o : Operand, (∀ x ∈ o.locals, x < n) → evalOp M (o.rename ρ) = evalOp G o := by
    intro o ho; cases o with
    | const _ => rfl
    | var x => exact hR.2 x (ho x (by simp [Operand.locals]))
  have evalRv_eq : ∀ rv : Rvalue, (∀ x ∈ rv.locals, x < n) → evalRv M (rv.rename ρ) = evalRv G rv := by
    intro rv hrv; cases rv with
    | use o => exact evalOp_eq o hrv
    | add a b =>
      simp only [evalRv, Rvalue.rename]
      rw [evalOp_eq a (fun x hx => hrv x (by simp [Rvalue.locals, hx])),
          evalOp_eq b (fun x hx => hrv x (by simp [Rvalue.locals, hx]))]
  cases s with
  | needCap _ => exact ⟨hR, rfl⟩
  | loc _ _ => exact ⟨hR, rfl⟩
  | emit o => exact ⟨hR, by simp only [stmtStore, Stmt.rename]; rw [evalOp_eq o hs]⟩
  | assign x rv =>
    have hx : x < n := hs x (by simp [Stmt.locals])
    have hrv : ∀ y ∈ rv.locals, y < n := fun y hy => hs y (by simp [Stmt.locals, hy])
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · intro y hy
      simp only [stmtStore, Stmt.rename, upd]
      have hne : y ≠ ρ x := fun h => havoid x hx (h ▸ hy)
      simp [hne, hR.1 y hy]
    · intro i hi
      simp only [stmtStore, Stmt.rename, upd]
      by_cases hix : i = x
      · subst hix; simp [evalRv_eq rv hrv]
      · have hne : ρ i ≠ ρ x := fun h => hix (hinj i hi x hx h)
        simp [hix, hne, hR.2 i hi]

/-! ## Control splicing (temporary return place) under equal capabilities -/

/-- **Splicing is a behavioural equivalence (temp mode, equal capabilities).** At a call site `IsCallSite p f b F ci G`, if both bodies are well formed (locals,
blocks of `F`, scope tables and scope references), the callee slots are fresh and injective, the
return place goes to a fresh temporary `t` distinct from every callee slot, the three rewriting
rules are the intended ones, and caller and callee have equal capability lists, then
`inline p f b cfg` is behaviourally equivalent to `p` from every entry: same events (including
`out` events of cleanup code, in the same order, and caller-location events) and same outcome,
on normal and unwinding runs. -/
theorem inline_behEquiv_retTemp_of_capsEq
    (p : Program) (f b : Nat) (F : Fn) (ci : CallInfo) (G : Fn) (cfg : InlineCfg) (t : Local)
    (hsite : IsCallSite p f b F ci G)
    (hlocF : LocalsBounded F) (hlocG : LocalsBounded G) (hblkF : BlocksBounded F)
    (hscF : ScopesWF F) (hscG : ScopesWF G)
    (hfresh : SlotsFresh cfg F G) (hinj : SlotsInjective cfg G)
    (hret : cfg.ret = .temp t) (htemp : TempFresh t cfg F G)
    (hcont : cfg.redirectContinue = true) (hres : cfg.resumeMap = .unwind)
    (hlink : cfg.link = .rustc)
    (hcaps : F.caps = G.caps) :
    BehEquiv p (inline p f b cfg) := by
  obtain ⟨B, hB, hBt⟩ := InlineSim.callSite_block hsite
  exact InlineSim.Site.behEquiv_of_hyps
    (InlineSim.hyps_temp p f b F B ci G cfg t hsite.1 hB hBt hsite.2.2 hlocF hlocG hblkF hscF hscG
      hfresh hinj hret htemp hcont hres hlink (fun _ _ c _ => by rw [hcaps])
      (by simp [hcaps]) (fun _ _ _ _ _ => by rw [hcaps]))

/-- **Return place mapped to the destination.** As
`inline_behEquiv_retTemp_of_capsEq`, but with `cfg.ret = .dest` (the callee's return place is
the call's destination `ci.dest`) instead of a temporary, and with two extra hypotheses making
the destination unobservable on the unwind path: cleanup code of `F` is closed, and no cleanup
block of `F` reads `ci.dest`. -/
theorem inline_behEquiv_retDest_of_destUnobservedOnUnwind
    (p : Program) (f b : Nat) (F : Fn) (ci : CallInfo) (G : Fn) (cfg : InlineCfg)
    (hsite : IsCallSite p f b F ci G)
    (hlocF : LocalsBounded F) (hlocG : LocalsBounded G) (hblkF : BlocksBounded F)
    (hscF : ScopesWF F) (hscG : ScopesWF G)
    (hfresh : SlotsFresh cfg F G) (hinj : SlotsInjective cfg G)
    (hret : cfg.ret = .dest)
    (hclosed : CleanupClosed F) (hdest : DestNotReadInCleanup F ci.dest)
    (hcont : cfg.redirectContinue = true) (hres : cfg.resumeMap = .unwind)
    (hlink : cfg.link = .rustc)
    (hcaps : F.caps = G.caps) :
    BehEquiv p (inline p f b cfg) := by
  obtain ⟨B, hB, hBt⟩ := InlineSim.callSite_block hsite
  exact InlineSim.Site.behEquiv_of_hyps
    (InlineSim.hyps_dest p f b F B ci G cfg hsite.1 hB hBt hsite.2.2 hlocF hlocG hblkF hscF hscG
      hfresh hinj hret hclosed hdest hcont hres hlink (fun _ _ c _ => by rw [hcaps])
      (by simp [hcaps]) (fun _ _ _ _ _ => by rw [hcaps]))

/-! ## What verification conditions transfer -/

/-- **Terminal properties transfer.** If `p` and `q` are behaviourally equivalent from entry `e`,
then a property `P` of halted observations (a normal or exceptional postcondition over the
event sequence and outcome) holds of every halted run of `p` from `e` iff it holds of every
halted run of `q` from `e`. -/
theorem terminalHolds_iff_of_behEquivAt (P : Obs → Prop) (p q : Program) (e : Entry)
    (h : BehEquivAt p q e) :
    TerminalHolds P p e ↔ TerminalHolds P q e := by
  constructor
  · intro hp m hm
    obtain ⟨n, hn⟩ := h.2 m
    have heq : run p n (init p e) = run q m (init q e) := hn.2 hm
    rw [← heq]; exact hp n (heq.symm ▸ hm)
  · intro hq n hn
    obtain ⟨m, hm⟩ := h.1 n
    have heq : run q m (init q e) = run p n (init p e) := hm.2 hn
    rw [← heq]; exact hq m (heq.symm ▸ hn)

/-- **Prefix-closed safety properties transfer.** If `p` and `q` are behaviourally equivalent from
`e` and `S` is closed under observation prefixes, then `S` holds of every finite observation
of `p` from `e` iff it holds of every finite observation of `q` from `e`. -/
theorem safetyHolds_iff_of_behEquivAt_of_prefixClosed (S : Obs → Prop) (p q : Program)
    (e : Entry) (h : BehEquivAt p q e) (hS : PrefixClosed S) :
    SafetyHolds S p e ↔ SafetyHolds S q e :=
  ⟨fun hp m => let ⟨n, hn⟩ := h.2 m; hS _ _ hn (hp n),
   fun hq n => let ⟨m, hm⟩ := h.1 n; hS _ _ hm (hq m)⟩

/-! ## Capability guards -/

/-- **Subset guard, ABI-insensitive callee.** As
`inline_behEquiv_retTemp_of_capsEq` (temp mode), with the equal-capabilities hypothesis replaced
by: caller capabilities include the callee's, every `needCap` in the callee names a capability
the callee holds, no block of the callee (reachable or not) terminates in an ABI-sensitive
call, and the inlined call itself is not ABI-sensitive. -/
theorem inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive
    (p : Program) (f b : Nat) (F : Fn) (ci : CallInfo) (G : Fn) (cfg : InlineCfg) (t : Local)
    (hsite : IsCallSite p f b F ci G)
    (hlocF : LocalsBounded F) (hlocG : LocalsBounded G) (hblkF : BlocksBounded F)
    (hscF : ScopesWF F) (hscG : ScopesWF G)
    (hfresh : SlotsFresh cfg F G) (hinj : SlotsInjective cfg G)
    (hret : cfg.ret = .temp t) (htemp : TempFresh t cfg F G)
    (hcont : cfg.redirectContinue = true) (hres : cfg.resumeMap = .unwind)
    (hlink : cfg.link = .rustc)
    (hsub : CapsSubset G F) (hlegal : CapLegal G) (habi : AbiInsensitive G)
    (hcs : ci.abiSensitive = false) :
    BehEquiv p (inline p f b cfg) := by
  obtain ⟨B, hB, hBt⟩ := InlineSim.callSite_block hsite
  exact InlineSim.Site.behEquiv_of_hyps
    (InlineSim.hyps_temp p f b F B ci G cfg t hsite.1 hB hBt hsite.2.2 hlocF hlocG hblkF hscF hscG
      hfresh hinj hret htemp hcont hres hlink (InlineSim.capsOk_of_subset_legal hsub hlegal)
      (by simp [hcs])
      (fun BG hBG ci2 hT ha => by
        have h := habi BG hBG
        rw [hT] at h
        simp [Term.abiSensitive, ha] at h))

/-- **Subset guard with ABI agreement.** As
`inline_behEquiv_retTemp_of_capsEq` (temp mode), with the equal-capabilities hypothesis replaced
by: caller capabilities include the callee's, every `needCap` in the callee names a capability
the callee holds, and `p.abi` agrees on the two capability lists. ABI-sensitive calls are
allowed. -/
theorem inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree
    (p : Program) (f b : Nat) (F : Fn) (ci : CallInfo) (G : Fn) (cfg : InlineCfg) (t : Local)
    (hsite : IsCallSite p f b F ci G)
    (hlocF : LocalsBounded F) (hlocG : LocalsBounded G) (hblkF : BlocksBounded F)
    (hscF : ScopesWF F) (hscG : ScopesWF G)
    (hfresh : SlotsFresh cfg F G) (hinj : SlotsInjective cfg G)
    (hret : cfg.ret = .temp t) (htemp : TempFresh t cfg F G)
    (hcont : cfg.redirectContinue = true) (hres : cfg.resumeMap = .unwind)
    (hlink : cfg.link = .rustc)
    (hsub : CapsSubset G F) (hlegal : CapLegal G) (hagree : AbiAgree p F G) :
    BehEquiv p (inline p f b cfg) := by
  obtain ⟨B, hB, hBt⟩ := InlineSim.callSite_block hsite
  have hab : p.abi F.caps = p.abi G.caps := hagree
  exact InlineSim.Site.behEquiv_of_hyps
    (InlineSim.hyps_temp p f b F B ci G cfg t hsite.1 hB hBt hsite.2.2 hlocF hlocG hblkF hscF hscG
      hfresh hinj hret htemp hcont hres hlink (InlineSim.capsOk_of_subset_legal hsub hlegal)
      (by simp [hab]) (fun _ _ _ _ _ => hab))

/-! ## Caller locations across inlining -/

/-- **The caller-location value inside an inlined callee equals the implicit-argument value.**
With the `rustc` link rule, host `inlinedParent` links pointing to smaller indices
(`ScopeParentsBelow F.scopes`) and a well-formed callee scope table (clean outermost scope and
links pointing to smaller indices), the caller-location value `locValue` at callee scope `s`
(shifted into the merged table) in a frame with implicit location `il` equals the value at scope
`s` of the callee's own table in a frame whose implicit location is what the call passes: the
call site's caller-location value if the callee is tracked, none otherwise. -/
theorem locValue_inline_calleeScope (tr : FnId → Bool) (link : LinkRule) (F : Fn)
    (ci : CallInfo) (G : Fn) (s : ScopeId) (sp : Span) (il : Option Span)
    (hF : ScopeParentsBelow F.scopes) (hG : ScopeTreeWF G.scopes) (hs : s < G.scopes.length)
    (hlink : link = .rustc) :
    locValue tr (F.scopes ++ linkScopes link F ci G) (F.scopes.length + s) sp il =
      locValue tr G.scopes s sp
        (if tr ci.callee then some (locValue tr F.scopes ci.scope ci.span il) else none) := by
  subst hlink
  simp only [locValue]
  have hlen : (F.scopes ++ linkScopes .rustc F ci G).length = F.scopes.length + G.scopes.length := by
    simp [linkScopes, mapIdxFrom_length]
  rw [walk_callee_aux tr F ci G hF hG s sp _ _ hs (by rw [hlen]; dsimp [ScopeId] at *; omega) hs]
  cases walk tr G.scopes G.scopes.length s sp with
  | stop sp' => rfl
  | top sp' =>
    cases htr : tr ci.callee with
    | false => rfl
    | true => simp only [↓reduceIte, Option.getD_some]

/-- **Caller scopes are unaffected.** For a host scope `s` of a table whose `inlinedParent`
links point to smaller indices, appending linked callee scopes (under any link rule) does not
change the caller-location value `locValue`. -/
theorem locValue_inline_callerScope (tr : FnId → Bool) (link : LinkRule) (F : Fn)
    (ci : CallInfo) (G : Fn) (s : ScopeId) (sp : Span) (il : Option Span)
    (hF : ScopeParentsBelow F.scopes) (hs : s < F.scopes.length) :
    locValue tr (F.scopes ++ linkScopes link F ci G) s sp il = locValue tr F.scopes s sp il := by
  simp only [locValue]
  have h1 : s < (F.scopes ++ linkScopes link F ci G).length := by
    simp only [List.length_append]; exact Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  rw [walk_prefix_eq tr F.scopes (linkScopes link F ci G) hF s sp _ _ hs h1 hs]

/-- **Scope well-formedness is preserved by inlining** (under any configuration and any call
data `ci`). If block `b` of `F` is `B`, `F` satisfies `ScopesWF`, and the callee's
`inlinedParent` links point to smaller indices and its scope references are in range, then the
new body satisfies `ScopesWF`, so the two caller-location theorems apply again at the next
inlining step. It does not check that the link rule or `ci` is the intended one. -/
theorem scopesWF_inlineFn (F : Fn) (b : BlockId) (B : Block) (ci : CallInfo) (G : Fn)
    (cfg : InlineCfg) (hB : nth? F.blocks b = some B) (hF : ScopesWF F)
    (hGpb : ScopeParentsBelow G.scopes) (hGref : ScopeRefsBounded G) :
    ScopesWF (inlineFn F b B ci G cfg) := by
  have hFlen : 0 < F.scopes.length := by
    cases h : F.scopes with
    | nil => have := hF.1.1; rw [h] at this; cases this
    | cons _ _ => exact Nat.zero_lt_succ _
  have hlen : (F.scopes ++ linkScopes cfg.link F ci G).length = F.scopes.length + G.scopes.length := by
    simp [linkScopes, mapIdxFrom_length]
  constructor
  · constructor
    · show nth? (F.scopes ++ linkScopes cfg.link F ci G) 0 = some ⟨none, none⟩
      rw [nth?_append_left F.scopes _ 0 hFlen]
      exact hF.1.1
    · intro i hi
      change i < (F.scopes ++ linkScopes cfg.link F ci G).length at hi
      show (nth? (F.scopes ++ linkScopes cfg.link F ci G) i).all (·.parentBelow i) = true
      rw [hlen] at hi
      by_cases hlt : i < F.scopes.length
      · rw [nth?_append_left F.scopes _ i hlt]
        exact hF.1.2 i hlt
      · obtain ⟨j, rfl⟩ : ∃ j, i = F.scopes.length + j := ⟨i - F.scopes.length, by omega⟩
        have hj : j < G.scopes.length := by omega
        rw [nth?_append_right F.scopes (linkScopes cfg.link F ci G) j]
        simp only [linkScopes, nth?_mapIdxFrom, Nat.zero_add]
        have hGpbj := hGpb j hj
        cases hsc : nth? G.scopes j with
        | none => rfl
        | some sc =>
          rw [hsc] at hGpbj
          simp only [Option.map_some, Option.all_some, linkScope, Scope.parentBelow] at hGpbj ⊢
          by_cases hj0 : j = 0
          · subst hj0
            simp only [↓reduceIte, Nat.add_zero]
            cases hcs : nth? F.scopes ci.scope with
            | none => rfl
            | some c =>
              have hci : ci.scope < F.scopes.length := nth?_lt_length F.scopes ci.scope c hcs
              by_cases hc : c.inlined.isSome = true
              · simp [hc, hci]
              · simp only [hc, Bool.false_eq_true, ↓reduceIte]
                cases cfg.link with
                | ignoreParent => rfl
                | rustc =>
                  have hFpb := hF.1.2 ci.scope hci
                  rw [hcs] at hFpb
                  simp only [Option.all_some, Scope.parentBelow] at hFpb
                  cases hp : c.inlinedParent with
                  | none => rfl
                  | some t =>
                    rw [hp] at hFpb
                    have ht : t < ci.scope := of_decide_eq_true hFpb
                    exact decide_eq_true (Nat.lt_trans ht hci)
          · simp only [hj0, ↓reduceIte]
            cases hp : sc.inlinedParent with
            | none => exact decide_eq_true (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hj0))
            | some t =>
              rw [hp] at hGpbj
              have ht : t < j := of_decide_eq_true hGpbj
              exact decide_eq_true (by dsimp [ScopeId] at *; omega)
  · intro B' hB' s hs
    show s < (F.scopes ++ linkScopes cfg.link F ci G).length
    rw [hlen]
    simp only [inlineFn, List.mem_append] at hB'
    rcases hB' with (h1 | h2) | h3
    · rcases mem_of_mem_set F.blocks b _ B' h1 with hFmem | rfl
      · exact Nat.lt_of_lt_of_le (hF.2 B' hFmem s hs) (Nat.le_add_right _ _)
      · have hBmem : B ∈ F.blocks := nth?_mem F.blocks b B hB
        simp only [Block.scopeRefs, List.mem_append, List.flatMap_append, List.mem_flatMap, Term.scopes,
          List.not_mem_nil, or_false] at hs
        rcases hs with ⟨st, hst, hss⟩ | ⟨st, hstP, hss⟩
        · have hsB : s ∈ B.scopeRefs := by
            simp only [Block.scopeRefs, List.mem_append, List.mem_flatMap]
            exact Or.inl ⟨st, hst, hss⟩
          exact Nat.lt_of_lt_of_le (hF.2 B hBmem s hsB) (Nat.le_add_right _ _)
        · simp only [prologue, List.mem_append, List.mem_map] at hstP
          rcases hstP with ⟨_, _, rfl⟩ | h0
          · simp [Stmt.scopes] at hss
          · split at h0 <;> simp at h0
            subst h0; simp [Stmt.scopes] at hss
    · cases ht : ci.target with
      | none => rw [ht] at h2; cases h2
      | some tgt =>
        rw [ht] at h2; simp only [List.mem_singleton] at h2; subst h2
        simp only [Block.scopeRefs, Term.scopes, List.append_nil, List.mem_flatMap] at hs
        rcases hs with ⟨st, hst, hss⟩
        cases hret : cfg.ret <;> simp [retStmts, hret] at hst
        subst hst; simp [Stmt.scopes] at hss
    · simp only [List.mem_map] at h3
      rcases h3 with ⟨BG, hBG, rfl⟩
      simp only [SpliceCtx.block, Block.scopeRefs, List.mem_append, List.mem_flatMap] at hs
      rcases hs with ⟨st, hst, hss⟩ | hterm
      · simp only [List.mem_map] at hst
        rcases hst with ⟨st0, hst0, rfl⟩
        cases st0 with
        | assign _ _ => simp [Stmt.rename, Stmt.scopes] at hss
        | emit _ => simp [Stmt.rename, Stmt.scopes] at hss
        | needCap _ => simp [Stmt.rename, Stmt.scopes] at hss
        | loc sp sc =>
          simp only [Stmt.rename, Stmt.scopes, List.mem_singleton] at hss
          subst hss
          have hlt : sc < G.scopes.length := hGref BG hBG sc (by
            simp only [Block.scopeRefs, List.mem_append, List.mem_flatMap]
            exact Or.inl ⟨.loc sp sc, hst0, by simp [Stmt.scopes]⟩)
          dsimp [ScopeId] at *; omega
      · cases hbt : BG.term with
        | call ci2 =>
          rw [hbt] at hterm
          simp only [SpliceCtx.term, Term.scopes, List.mem_singleton] at hterm
          subst hterm
          have hlt : ci2.scope < G.scopes.length := hGref BG hBG ci2.scope (by
            simp only [Block.scopeRefs, List.mem_append, hbt, Term.scopes, List.mem_singleton]
            exact Or.inr trivial)
          dsimp [ScopeId] at *; omega
        | ret =>
          rw [hbt] at hterm; simp only [SpliceCtx.term] at hterm
          split at hterm <;> simp [Term.scopes] at hterm
        | resume =>
          rw [hbt] at hterm; simp only [SpliceCtx.term] at hterm
          split at hterm
          · split at hterm <;> simp [Term.scopes] at hterm
          · split at hterm <;> simp [Term.scopes] at hterm
        | goto _ => rw [hbt] at hterm; simp [SpliceCtx.term, Term.scopes] at hterm
        | branch _ _ _ => rw [hbt] at hterm; simp [SpliceCtx.term, Term.scopes] at hterm
        | panic _ => rw [hbt] at hterm; simp [SpliceCtx.term, Term.scopes] at hterm
        | unreachable => rw [hbt] at hterm; simp [SpliceCtx.term, Term.scopes] at hterm
        | abort => rw [hbt] at hterm; simp [SpliceCtx.term, Term.scopes] at hterm

/-! ## Composition -/

/-- **Behavioural equivalence is transitive.** A structural reference point: it composes
equivalences, but it does not re-establish the hypotheses of the inlining theorems on an
intermediate program. -/
theorem behEquiv_trans {p q r : Program} (h₁ : BehEquiv p q) (h₂ : BehEquiv q r) :
    BehEquiv p r := fun e =>
  ⟨fun n => let ⟨m, h1⟩ := (h₁ e).1 n; let ⟨k, h2⟩ := (h₂ e).1 m; ⟨k, h1.trans h2⟩,
   fun k => let ⟨m, h2⟩ := (h₂ e).2 k; let ⟨n, h1⟩ := (h₁ e).2 m; ⟨n, h2.trans h1⟩⟩

end Toy.Inline
