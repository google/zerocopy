/-!
# `#[track_caller]`: scope walk, MIR inlining, implicit-argument ABI and reify shims

A self-contained Lean 4 development (prelude only, no imports) that models the parts of `rustc`
which decide what `core::panic::Location::caller()` returns:

* `resolveChain` and `findOutermostTrackedCallSite` transcribe
  `rustc_middle::mir::Body::caller_location_span`, on an abstract list of enclosing inlined
  callees and on a pointer-linked `SourceScopeData` table respectively;
* `remapScopesOnInline` transcribes the scope rewriting done by the MIR inliner
  (`Integrator::visit_source_scope_data` in `rustc_mir_transform::inline`);
* `Node.observations` gives the meaning of a call tree in which every call has either been left
  as a real call or been replaced by its inlined body;
* `stackWalkLocation` transcribes the interpreter's `find_closest_untracked_caller_location`;
* `lowerFnAbiTrackCaller`, `reifyToFnPtrShim` and `vtableMethodDispatch` model the trailing
  implicit argument of `FnAbi`, the `ReifyShim` body, and vtable slot selection in
  `Instance::expect_resolve_for_vtable`.

Every recursive definition is structurally recursive and every proof is by induction, case
analysis and rewriting. The recursive definitions are marked `noncomputable`: they are
specifications that only the kernel ever evaluates, and without the marker Lean's code generator
would add an unsafe compiled helper constant for each of them. The file ends with an axiom audit
of the main theorems; `EnvironmentAudit.lean` audits every constant of the compiled module.
-/

namespace TrackCaller

noncomputable section

/-- A source span. `TyCtxt::span_as_caller_location` maps a span to a `Location` constant, so two
reported locations are equal exactly when the spans are. -/
abbrev Span := Nat

/-- One enclosing MIR-inlined callee, as far as caller-location resolution can see it:
`(callee.def.requires_caller_location(tcx), call-site span)`. -/
abbrev InlinedEntry := Bool × Span

/-! ## 1. The walk on a chain of enclosing inlined callees -/

/-- `Body::caller_location_span` on the list of enclosing inlined callees, innermost first.

* an untracked inlined callee ends the walk with the span reached so far;
* a tracked inlined callee replaces the span by its call-site span and the walk continues;
* when the list is exhausted the function's own implicit argument is used if it has one. -/
noncomputable def resolveChain : List InlinedEntry → Option Span → Span → Span
  | [], implicit, span => implicit.getD span
  | (false, _) :: _, _, span => span
  | (true, callsite) :: rest, implicit, _ => resolveChain rest implicit callsite

/-- The composition law behind every inlining result below: a chain that continues through an
inlined callee into its call site resolves like the callee's own chain, run with the implicit
argument that the call site would have passed (or none, for an untracked callee). -/
theorem resolveChain_append (inner : List InlinedEntry) (tracked : Bool) (callsite : Span)
    (outer : List InlinedEntry) (implicit : Option Span) (span : Span) :
    resolveChain (inner ++ (tracked, callsite) :: outer) implicit span
      = resolveChain inner
          (if tracked then some (resolveChain outer implicit callsite) else none) span := by
  induction inner generalizing span with
  | nil => cases tracked <;> rfl
  | cons entry rest ih =>
    obtain ⟨t, cs⟩ := entry
    cases t
    · rfl
    · exact ih cs

/-- An untracked inlined callee shields everything outside it. -/
theorem resolveChain_stops_at_untracked (inner : List InlinedEntry) (callsite : Span)
    (outer₁ outer₂ : List InlinedEntry) (implicit₁ implicit₂ : Option Span) (span : Span) :
    resolveChain (inner ++ (false, callsite) :: outer₁) implicit₁ span
      = resolveChain (inner ++ (false, callsite) :: outer₂) implicit₂ span := by
  rw [resolveChain_append, resolveChain_append]
  rfl

/-! ## 2. The walk on `SourceScopeData`, and the inliner's scope rewriting -/

/-- The fields of `rustc_middle::mir::SourceScopeData` read by the inliner and by
`caller_location_span`. `inlined` is `Some` exactly on the root scope of an inlined body;
`inlinedParentScope` points to the nearest enclosing such root. -/
structure ScopeData (σ : Type) where
  parentScope : Option σ
  inlined : Option InlinedEntry
  inlinedParentScope : Option σ

/-- `Body::source_scopes`, indexed by scope identifier. -/
abbrev ScopeTree (σ : Type) := σ → ScopeData σ

/-- What one scope's `inlined` field does to the walk: `none` means "stop and report the current
span", `some span'` means "continue with `span'`". -/
def stepInlined : Option InlinedEntry → Span → Option Span
  | some (false, _), _ => none
  | some (true, callsite), _ => some callsite
  | none, span => some span

/-- `Body::caller_location_span`, transcribed on the pointer-linked table. `fuel` bounds the
number of loop iterations; `none` is returned only when it runs out. -/
noncomputable def findOutermostTrackedCallSite {σ : Type} (tree : ScopeTree σ)
    (implicit : Option Span) : Nat → σ → Span → Option Span
  | 0, _, _ => none
  | fuel + 1, scope, span =>
    match stepInlined (tree scope).inlined span with
    | none => some span
    | some span' =>
      match (tree scope).inlinedParentScope with
      | some parent => findOutermostTrackedCallSite tree implicit fuel parent span'
      | none => some (implicit.getD span')

/-- Unfolding of one loop iteration. -/
theorem findOutermostTrackedCallSite_succ {σ : Type} (tree : ScopeTree σ) (implicit : Option Span)
    (fuel : Nat) (scope : σ) (span : Span) :
    findOutermostTrackedCallSite tree implicit (fuel + 1) scope span
      = match stepInlined (tree scope).inlined span with
        | none => some span
        | some span' =>
          match (tree scope).inlinedParentScope with
          | some parent => findOutermostTrackedCallSite tree implicit fuel parent span'
          | none => some (implicit.getD span') := rfl

/-- The `inlined` field as a chain fragment. -/
def entryList : Option InlinedEntry → List InlinedEntry
  | some entry => [entry]
  | none => []

/-- `HasChain tree scope chain`: following `inlined_parent_scope` from `scope` terminates, and
the `inlined` entries met on the way are exactly `chain`. -/
inductive HasChain {σ : Type} (tree : ScopeTree σ) : σ → List InlinedEntry → Prop
  | root {scope : σ} {chain : List InlinedEntry} :
      (tree scope).inlinedParentScope = none →
      chain = entryList (tree scope).inlined →
      HasChain tree scope chain
  | step {scope parent : σ} {rest chain : List InlinedEntry} :
      (tree scope).inlinedParentScope = some parent →
      HasChain tree parent rest →
      chain = entryList (tree scope).inlined ++ rest →
      HasChain tree scope chain

theorem resolveChain_entryList (entry : Option InlinedEntry) (rest : List InlinedEntry)
    (implicit : Option Span) (span : Span) :
    resolveChain (entryList entry ++ rest) implicit span
      = match stepInlined entry span with
        | none => span
        | some span' => resolveChain rest implicit span' := by
  cases entry with
  | none => rfl
  | some entry =>
    obtain ⟨t, cs⟩ := entry
    cases t <;> rfl

/-- The pointer walk computes `resolveChain` of the scope's chain, for every sufficiently large
fuel. -/
theorem find_of_hasChain {σ : Type} (tree : ScopeTree σ) (implicit : Option Span)
    {scope : σ} {chain : List InlinedEntry} (h : HasChain tree scope chain) :
    ∃ fuel, ∀ extra span,
      findOutermostTrackedCallSite tree implicit (fuel + extra) scope span
        = some (resolveChain chain implicit span) := by
  induction h with
  | @root scope chain hParent hChain =>
    refine ⟨1, fun extra span => ?_⟩
    have key := resolveChain_entryList (tree scope).inlined [] implicit span
    rw [List.append_nil] at key
    rw [Nat.add_comm 1 extra, hChain, key, findOutermostTrackedCallSite_succ, hParent]
    cases stepInlined (tree scope).inlined span <;> rfl
  | @step scope parent rest chain hParent _ hChain ih =>
    obtain ⟨fuel, hFuel⟩ := ih
    refine ⟨fuel + 1, fun extra span => ?_⟩
    rw [Nat.add_right_comm fuel 1 extra, hChain, resolveChain_entryList,
      findOutermostTrackedCallSite_succ, hParent]
    cases stepInlined (tree scope).inlined span with
    | none => rfl
    | some span' => exact hFuel extra span'

/-- `inlined_parent_scope` given to the callee's outermost scope: the call-site scope if that is
itself the root of an inlined body, otherwise the call-site scope's own `inlined_parent_scope`. -/
def rootInlinedParent {σ τ : Type} (callsiteScope : σ) :
    Option InlinedEntry → Option σ → Option (Sum σ τ)
  | some _, _ => some (.inl callsiteScope)
  | none, parent => parent.map Sum.inl

/-- `inlined_parent_scope` of any other callee scope: renumbered if present, else the remapped
outermost callee scope. -/
def innerInlinedParent {σ τ : Type} (calleeRoot : τ) : Option τ → Option (Sum σ τ)
  | some q => some (.inr q)
  | none => some (.inr calleeRoot)

/-- The rewritten data of callee scope `k`, by whether it had a `parent_scope`. -/
def remapCalleeScope {σ τ : Type} (caller : ScopeTree σ) (callsiteScope : σ)
    (callsiteSpan : Span) (calleeTracked : Bool) (callee : ScopeTree τ) (calleeRoot : τ) (k : τ) :
    Option τ → ScopeData (Sum σ τ)
  | none =>
    { parentScope := some (.inl callsiteScope)
      inlined := some (calleeTracked, callsiteSpan)
      inlinedParentScope :=
        rootInlinedParent callsiteScope (caller callsiteScope).inlined
          (caller callsiteScope).inlinedParentScope }
  | some p =>
    { parentScope := some (.inr p)
      inlined := (callee k).inlined
      inlinedParentScope := innerInlinedParent calleeRoot (callee k).inlinedParentScope }

/-- The scope rewriting performed when a callee body is spliced into a caller body.

The caller keeps its scopes (`Sum.inl`); the callee's scopes are appended under fresh identifiers
(`Sum.inr`, standing for `new_scopes.start + scope.index()`). Mirroring
`Integrator::visit_source_scope_data`:

* a callee scope without `parent_scope` (the callee's outermost scope) is attached below the
  call-site scope, marked `inlined = Some((callee, callsite_span))`, and its
  `inlined_parent_scope` becomes the call-site scope if that is itself an inlined root, else the
  call-site scope's `inlined_parent_scope`;
* any other callee scope without `inlined_parent_scope` gets the remapped outermost callee scope;
* everything else is only renumbered. -/
def remapScopesOnInline {σ τ : Type} (caller : ScopeTree σ) (callsiteScope : σ)
    (callsiteSpan : Span) (calleeTracked : Bool) (callee : ScopeTree τ) (calleeRoot : τ) :
    ScopeTree (Sum σ τ)
  | .inl s =>
    { parentScope := (caller s).parentScope.map Sum.inl
      inlined := (caller s).inlined
      inlinedParentScope := (caller s).inlinedParentScope.map Sum.inl }
  | .inr k =>
    remapCalleeScope caller callsiteScope callsiteSpan calleeTracked callee calleeRoot k
      (callee k).parentScope

/-- The two `assert_eq!`s in `visit_source_scope_data`, plus the fact that the designated root
has no parent: a callee scope without `parent_scope` carries neither `inlined` nor
`inlined_parent_scope` before the splice. -/
structure CalleeRootWellFormed {τ : Type} (callee : ScopeTree τ) (calleeRoot : τ) : Prop where
  rootHasNoParent : (callee calleeRoot).parentScope = none
  parentlessIsFresh : ∀ k, (callee k).parentScope = none →
    (callee k).inlined = none ∧ (callee k).inlinedParentScope = none

section Remap

variable {σ τ : Type} {caller : ScopeTree σ} {callsiteScope : σ} {callsiteSpan : Span}
  {calleeTracked : Bool} {callee : ScopeTree τ} {calleeRoot : τ}

theorem remap_root_inlined {k : τ} (h : (callee k).parentScope = none) :
    (remapScopesOnInline caller callsiteScope callsiteSpan calleeTracked callee calleeRoot
      (.inr k)).inlined = some (calleeTracked, callsiteSpan) :=
  congrArg (fun o => (remapCalleeScope caller callsiteScope callsiteSpan calleeTracked callee
    calleeRoot k o).inlined) h

theorem remap_root_inlinedParent {k : τ} (h : (callee k).parentScope = none) :
    (remapScopesOnInline caller callsiteScope callsiteSpan calleeTracked callee calleeRoot
      (.inr k)).inlinedParentScope
      = rootInlinedParent callsiteScope (caller callsiteScope).inlined
          (caller callsiteScope).inlinedParentScope :=
  congrArg (fun o => (remapCalleeScope caller callsiteScope callsiteSpan calleeTracked callee
    calleeRoot k o).inlinedParentScope) h

theorem remap_inner_inlined {k p : τ} (h : (callee k).parentScope = some p) :
    (remapScopesOnInline caller callsiteScope callsiteSpan calleeTracked callee calleeRoot
      (.inr k)).inlined = (callee k).inlined :=
  congrArg (fun o => (remapCalleeScope caller callsiteScope callsiteSpan calleeTracked callee
    calleeRoot k o).inlined) h

theorem remap_inner_inlinedParent {k p : τ} (h : (callee k).parentScope = some p) :
    (remapScopesOnInline caller callsiteScope callsiteSpan calleeTracked callee calleeRoot
      (.inr k)).inlinedParentScope = innerInlinedParent calleeRoot (callee k).inlinedParentScope :=
  congrArg (fun o => (remapCalleeScope caller callsiteScope callsiteSpan calleeTracked callee
    calleeRoot k o).inlinedParentScope) h

/-- Scopes of the caller keep their chain: statements that were already in the caller resolve as
before. -/
theorem hasChain_remap_caller {s : σ} {chain : List InlinedEntry} (h : HasChain caller s chain) :
    HasChain (remapScopesOnInline caller callsiteScope callsiteSpan calleeTracked callee calleeRoot)
      (.inl s) chain := by
  induction h with
  | @root scope chain hParent hChain =>
    refine HasChain.root ?_ hChain
    show (caller scope).inlinedParentScope.map Sum.inl = none
    rw [hParent]
    rfl
  | @step scope parent rest chain hParent _ hChain ih =>
    refine HasChain.step (parent := .inl parent) ?_ ih hChain
    show (caller scope).inlinedParentScope.map Sum.inl = some (.inl parent)
    rw [hParent]
    rfl

/-- A callee scope without `parent_scope` becomes an inlined root whose chain is the new entry
followed by the call-site scope's chain. -/
theorem hasChain_remap_calleeRoot {k : τ} (hRoot : (callee k).parentScope = none)
    {outer : List InlinedEntry} (hOuter : HasChain caller callsiteScope outer) :
    HasChain (remapScopesOnInline caller callsiteScope callsiteSpan calleeTracked callee calleeRoot)
      (.inr k) ((calleeTracked, callsiteSpan) :: outer) := by
  cases hInl : (caller callsiteScope).inlined with
  | some entry =>
    refine HasChain.step (parent := .inl callsiteScope) (rest := outer) ?_
      (hasChain_remap_caller hOuter) ?_
    · rw [remap_root_inlinedParent hRoot, hInl]
      rfl
    · rw [remap_root_inlined hRoot]
      rfl
  | none =>
    cases hOuter with
    | root hParent hChain =>
      rw [hInl] at hChain
      refine HasChain.root ?_ ?_
      · rw [remap_root_inlinedParent hRoot, hInl, hParent]
        rfl
      · rw [remap_root_inlined hRoot, hChain]
        rfl
    | @step _ parent rest _ hParent hRest hChain =>
      rw [hInl] at hChain
      refine HasChain.step (parent := .inl parent) (rest := rest) ?_
        (hasChain_remap_caller hRest) ?_
      · rw [remap_root_inlinedParent hRoot, hInl, hParent]
        rfl
      · rw [remap_root_inlined hRoot, hChain]
        rfl

/-- Every callee scope's chain is extended by the new inlined entry and the call-site scope's
chain. -/
theorem hasChain_remap_callee (wf : CalleeRootWellFormed callee calleeRoot)
    {outer : List InlinedEntry} (hOuter : HasChain caller callsiteScope outer)
    {k : τ} {inner : List InlinedEntry} (hInner : HasChain callee k inner) :
    HasChain (remapScopesOnInline caller callsiteScope callsiteSpan calleeTracked callee calleeRoot)
      (.inr k) (inner ++ (calleeTracked, callsiteSpan) :: outer) := by
  induction hInner with
  | @root scope chain hParent hChain =>
    cases hP : (callee scope).parentScope with
    | none =>
      rw [(wf.parentlessIsFresh scope hP).1] at hChain
      rw [hChain]
      exact hasChain_remap_calleeRoot hP hOuter
    | some p =>
      refine HasChain.step (parent := .inr calleeRoot)
        (rest := (calleeTracked, callsiteSpan) :: outer) ?_
        (hasChain_remap_calleeRoot wf.rootHasNoParent hOuter) ?_
      · rw [remap_inner_inlinedParent hP, hParent]
        rfl
      · rw [remap_inner_inlined hP, hChain]
  | @step scope parent rest chain hParent _ hChain ih =>
    cases hP : (callee scope).parentScope with
    | none =>
      rw [(wf.parentlessIsFresh scope hP).2] at hParent
      cases hParent
    | some p =>
      refine HasChain.step (parent := .inr parent) ?_ ih ?_
      · rw [remap_inner_inlinedParent hP, hParent]
        rfl
      · rw [remap_inner_inlined hP, hChain, List.append_assoc]

/-- **One inlining step is exact.** After the splice, a statement that came from the callee
(scope `k`, span `span`) resolves to exactly what it resolved to in the stand-alone callee, run
with the implicit argument the call site passes: the call site's own resolution if the callee is
tracked, nothing otherwise. -/
theorem remapScopesOnInline_exact (wf : CalleeRootWellFormed callee calleeRoot)
    {outer : List InlinedEntry} (hOuter : HasChain caller callsiteScope outer)
    {k : τ} {inner : List InlinedEntry} (hInner : HasChain callee k inner)
    (implicit : Option Span) :
    ∃ fuel, ∀ extra span,
      findOutermostTrackedCallSite
          (remapScopesOnInline caller callsiteScope callsiteSpan calleeTracked callee calleeRoot)
          implicit (fuel + extra) (.inr k) span
        = findOutermostTrackedCallSite callee
            (if calleeTracked then
              findOutermostTrackedCallSite caller implicit (fuel + extra) callsiteScope callsiteSpan
             else none)
            (fuel + extra) k span := by
  obtain ⟨f₁, h₁⟩ := find_of_hasChain
    (remapScopesOnInline caller callsiteScope callsiteSpan calleeTracked callee calleeRoot) implicit
    (hasChain_remap_callee wf hOuter hInner)
  obtain ⟨f₂, h₂⟩ := find_of_hasChain caller implicit hOuter
  obtain ⟨f₃, h₃⟩ := find_of_hasChain callee
    (if calleeTracked then some (resolveChain outer implicit callsiteSpan) else none) hInner
  refine ⟨f₁ + f₂ + f₃, fun extra span => ?_⟩
  have e₁ : f₁ + f₂ + f₃ + extra = f₁ + (f₂ + f₃ + extra) := by
    simp only [Nat.add_assoc]
  have e₂ : f₁ + f₂ + f₃ + extra = f₂ + (f₁ + f₃ + extra) := by
    simp only [Nat.add_assoc, Nat.add_left_comm]
  have e₃ : f₁ + f₂ + f₃ + extra = f₃ + (f₁ + f₂ + extra) := by
    simp only [Nat.add_left_comm, Nat.add_comm]
  have post := h₁ (f₂ + f₃ + extra) span
  have callerWalk := h₂ (f₁ + f₃ + extra) callsiteSpan
  have calleeWalk := h₃ (f₁ + f₂ + extra) span
  rw [← e₁] at post
  rw [← e₂] at callerWalk
  rw [← e₃] at calleeWalk
  rw [post, callerWalk, calleeWalk, resolveChain_append]

/-- Statements that were already in the caller are unaffected by the splice. -/
theorem remapScopesOnInline_caller_unchanged {s : σ} {chain : List InlinedEntry}
    (h : HasChain caller s chain) (implicit : Option Span) :
    ∃ fuel, ∀ extra span,
      findOutermostTrackedCallSite
          (remapScopesOnInline caller callsiteScope callsiteSpan calleeTracked callee calleeRoot)
          implicit (fuel + extra) (.inl s) span
        = findOutermostTrackedCallSite caller implicit (fuel + extra) s span := by
  obtain ⟨f₁, h₁⟩ := find_of_hasChain
    (remapScopesOnInline caller callsiteScope callsiteSpan calleeTracked callee calleeRoot) implicit
    (hasChain_remap_caller (callsiteScope := callsiteScope) (callsiteSpan := callsiteSpan)
      (calleeTracked := calleeTracked) (callee := callee) (calleeRoot := calleeRoot) h)
  obtain ⟨f₂, h₂⟩ := find_of_hasChain caller implicit h
  refine ⟨f₁ + f₂, fun extra span => ?_⟩
  have e₂ : f₁ + f₂ + extra = f₂ + (f₁ + extra) := by
    simp only [Nat.add_assoc, Nat.add_left_comm]
  rw [Nat.add_assoc f₁ f₂ extra, h₁ (f₂ + extra) span, ← Nat.add_assoc f₁ f₂ extra, e₂,
    h₂ (f₁ + extra) span]

end Remap

/-! ## 3. Call trees: real calls versus inlined calls -/

mutual
/-- One step of a dynamic call tree. A call to a callee with body `body` at call-site span `span`
is either still a real call (`call`: the callee runs in its own frame and, if tracked, receives an
implicit argument) or has been replaced by the callee's body (`inl`: the body runs in the
caller's frame under a scope marked `inlined = Some((callee, span))`). -/
inductive Node where
  | observe (span : Span) : Node
  | call (span : Span) (tracked : Bool) (body : Nodes) : Node
  | inl (span : Span) (tracked : Bool) (body : Nodes) : Node
/-- A function body: a sequence of nodes. -/
inductive Nodes where
  | nil : Nodes
  | cons (head : Node) (tail : Nodes) : Nodes
end

mutual
/-- Every value produced by the `caller_location` intrinsic while running a node, in order.
`chain` is the inlined-scope chain of the node's position and `implicit` the enclosing frame's
implicit argument. -/
noncomputable def Node.observations (chain : List InlinedEntry) (implicit : Option Span) :
    Node → List Span
  | .observe span => [resolveChain chain implicit span]
  | .call span tracked body =>
    Nodes.observations [] (if tracked then some (resolveChain chain implicit span) else none) body
  | .inl span tracked body => Nodes.observations ((tracked, span) :: chain) implicit body
/-- Observations of a body. -/
noncomputable def Nodes.observations (chain : List InlinedEntry) (implicit : Option Span) :
    Nodes → List Span
  | .nil => []
  | .cons head tail =>
    Node.observations chain implicit head ++ Nodes.observations chain implicit tail
end

mutual
theorem Node.observations_append (inner : List InlinedEntry) (tracked : Bool) (callsite : Span)
    (outer : List InlinedEntry) (implicit : Option Span) :
    ∀ node : Node,
      Node.observations (inner ++ (tracked, callsite) :: outer) implicit node
        = Node.observations inner
            (if tracked then some (resolveChain outer implicit callsite) else none) node
  | .observe span => by simp only [Node.observations, resolveChain_append]
  | .call span t body => by simp only [Node.observations, resolveChain_append]
  | .inl span t body =>
    Nodes.observations_append ((t, span) :: inner) tracked callsite outer implicit body
theorem Nodes.observations_append (inner : List InlinedEntry) (tracked : Bool) (callsite : Span)
    (outer : List InlinedEntry) (implicit : Option Span) :
    ∀ nodes : Nodes,
      Nodes.observations (inner ++ (tracked, callsite) :: outer) implicit nodes
        = Nodes.observations inner
            (if tracked then some (resolveChain outer implicit callsite) else none) nodes
  | .nil => rfl
  | .cons head tail => by
    simp only [Nodes.observations]
    rw [Node.observations_append inner tracked callsite outer implicit head,
      Nodes.observations_append inner tracked callsite outer implicit tail]
end

/-- Inlining one call does not change a single observation: the inlined body produces exactly
what the real call produced. This holds for tracked and for untracked callees alike. -/
theorem Node.inl_observations_eq_call (chain : List InlinedEntry) (implicit : Option Span)
    (span : Span) (tracked : Bool) (body : Nodes) :
    Node.observations chain implicit (.inl span tracked body)
      = Node.observations chain implicit (.call span tracked body) :=
  Nodes.observations_append [] tracked span chain implicit body

mutual
/-- Undo every inlining decision. -/
noncomputable def Node.uninline : Node → Node
  | .observe span => .observe span
  | .call span tracked body => .call span tracked (Nodes.uninline body)
  | .inl span tracked body => .call span tracked (Nodes.uninline body)
/-- Undo every inlining decision in a body. -/
noncomputable def Nodes.uninline : Nodes → Nodes
  | .nil => .nil
  | .cons head tail => .cons (Node.uninline head) (Nodes.uninline tail)
end

mutual
theorem Node.observations_uninline (chain : List InlinedEntry) (implicit : Option Span) :
    ∀ node : Node,
      Node.observations chain implicit (Node.uninline node) = Node.observations chain implicit node
  | .observe _ => rfl
  | .call span tracked body => by
    simp only [Node.uninline, Node.observations]
    exact Nodes.observations_uninline [] _ body
  | .inl span tracked body => by
    simp only [Node.uninline, Node.observations]
    rw [Nodes.observations_uninline [] _ body]
    exact (Nodes.observations_append [] tracked span chain implicit body).symm
theorem Nodes.observations_uninline (chain : List InlinedEntry) (implicit : Option Span) :
    ∀ nodes : Nodes,
      Nodes.observations chain implicit (Nodes.uninline nodes)
        = Nodes.observations chain implicit nodes
  | .nil => rfl
  | .cons head tail => by
    simp only [Nodes.uninline, Nodes.observations]
    rw [Node.observations_uninline chain implicit head,
      Nodes.observations_uninline chain implicit tail]
end

/-- One inlining decision somewhere in a body: a call node, tracked or untracked, at any nesting
depth and below real or inlined calls, is replaced by its inlined body. -/
inductive InlineStep : Nodes → Nodes → Prop
  | here (span : Span) (tracked : Bool) (body tail : Nodes) :
      InlineStep (.cons (.call span tracked body) tail) (.cons (.inl span tracked body) tail)
  | underCall (span : Span) (tracked : Bool) {body body' : Nodes} (tail : Nodes) :
      InlineStep body body' →
      InlineStep (.cons (.call span tracked body) tail) (.cons (.call span tracked body') tail)
  | underInl (span : Span) (tracked : Bool) {body body' : Nodes} (tail : Nodes) :
      InlineStep body body' →
      InlineStep (.cons (.inl span tracked body) tail) (.cons (.inl span tracked body') tail)
  | later (head : Node) {tail tail' : Nodes} :
      InlineStep tail tail' → InlineStep (.cons head tail) (.cons head tail')

/-- Any finite sequence of inlining decisions. -/
inductive InlineSeq : Nodes → Nodes → Prop
  | done (body : Nodes) : InlineSeq body body
  | next {a b c : Nodes} : InlineStep a b → InlineSeq b c → InlineSeq a c

theorem InlineStep.uninline_eq {a b : Nodes} (h : InlineStep a b) :
    Nodes.uninline a = Nodes.uninline b := by
  induction h with
  | here => rfl
  | underCall _ _ _ _ ih => simp only [Nodes.uninline, Node.uninline, ih]
  | underInl _ _ _ _ ih => simp only [Nodes.uninline, Node.uninline, ih]
  | later _ _ ih => simp only [Nodes.uninline, ih]

theorem InlineSeq.uninline_eq {a b : Nodes} (h : InlineSeq a b) :
    Nodes.uninline a = Nodes.uninline b := by
  induction h with
  | done => rfl
  | next step _ ih => exact step.uninline_eq.trans ih

/-- **Exact `Location::caller()` invariance.** Any sequence of inlinings of tracked and untracked
callees, in any order and at any depth, leaves every observed location unchanged, in every
context (`chain`) and for every implicit argument of the enclosing frame. -/
theorem location_caller_invariant_under_inlining {a b : Nodes} (h : InlineSeq a b)
    (chain : List InlinedEntry) (implicit : Option Span) :
    Nodes.observations chain implicit a = Nodes.observations chain implicit b := by
  rw [← Nodes.observations_uninline chain implicit a,
    ← Nodes.observations_uninline chain implicit b, h.uninline_eq]

/-- Two inlining states of the same call tree agree, however they were reached. -/
theorem observations_eq_of_uninline_eq {a b : Nodes} (h : Nodes.uninline a = Nodes.uninline b)
    (chain : List InlinedEntry) (implicit : Option Span) :
    Nodes.observations chain implicit a = Nodes.observations chain implicit b := by
  rw [← Nodes.observations_uninline chain implicit a,
    ← Nodes.observations_uninline chain implicit b, h]

/-! ## 4. Stack walk versus implicit argument -/

/-- A stack frame as seen by caller-location resolution. -/
structure Frame where
  /-- `frame.instance.def.requires_caller_location(tcx)`. -/
  tracked : Bool
  /-- The implicit argument actually received, if any. -/
  received : Option Span
  /-- Inlined-scope chain of the frame's current statement. -/
  chain : List InlinedEntry
  /-- Span of the current statement (`fn_span` when it is a call terminator). -/
  span : Span

/-- What code generation computes in a frame: `caller_location_span(source_info, received)`. -/
def Frame.codegenLocation (frame : Frame) : Span :=
  resolveChain frame.chain frame.received frame.span

/-- The inlined-scope part of the walk on its own: `(true, s)` when it stopped inside an
untracked inlined callee with answer `s`, `(false, s)` when the chain ran out carrying `s`. -/
noncomputable def chainOutcome : List InlinedEntry → Span → Bool × Span
  | [], span => (false, span)
  | (false, _) :: _, span => (true, span)
  | (true, callsite) :: rest, _ => chainOutcome rest callsite

theorem resolveChain_eq_chainOutcome (chain : List InlinedEntry) (implicit : Option Span)
    (span : Span) :
    resolveChain chain implicit span
      = match chainOutcome chain span with
        | (true, s) => s
        | (false, s) => implicit.getD s := by
  induction chain generalizing span with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨t, cs⟩ := entry
    cases t
    · rfl
    · exact ih cs

/-- The interpreter's `find_closest_untracked_caller_location`: walk the stack from the innermost
frame; a frame answers unless it is tracked and all its enclosing inlined callees are tracked, in
which case the next outer frame is asked at its current (call) statement. -/
noncomputable def stackWalkLocation : List Frame → Option Span
  | [] => none
  | frame :: outer =>
    match chainOutcome frame.chain frame.span with
    | (true, span) => some span
    | (false, span) => if frame.tracked then stackWalkLocation outer else some span

theorem stackWalkLocation_cons (frame : Frame) (outer : List Frame) :
    stackWalkLocation (frame :: outer)
      = match chainOutcome frame.chain frame.span with
        | (true, span) => some span
        | (false, span) => if frame.tracked then stackWalkLocation outer else some span := rfl

/-- The calling discipline that code generation maintains: an untracked frame received nothing,
a tracked frame received what its caller computed at the call statement, and the outermost frame
is untracked. -/
inductive Disciplined : List Frame → Prop
  | bottom (frame : Frame) :
      frame.tracked = false → frame.received = none → Disciplined [frame]
  | pushUntracked (frame caller : Frame) (rest : List Frame) :
      frame.tracked = false → frame.received = none →
      Disciplined (caller :: rest) → Disciplined (frame :: caller :: rest)
  | pushTracked (frame caller : Frame) (rest : List Frame) :
      frame.tracked = true → frame.received = some caller.codegenLocation →
      Disciplined (caller :: rest) → Disciplined (frame :: caller :: rest)

theorem stackWalk_untracked_frame (frame : Frame) (outer : List Frame)
    (hTracked : frame.tracked = false) (hReceived : frame.received = none) :
    stackWalkLocation (frame :: outer) = some frame.codegenLocation := by
  show _ = some (resolveChain frame.chain frame.received frame.span)
  rw [stackWalkLocation_cons, resolveChain_eq_chainOutcome, hTracked, hReceived]
  cases chainOutcome frame.chain frame.span with
  | mk stopped s => cases stopped <;> rfl

/-- **The stack walk and the implicit argument agree** on every stack built under the calling
discipline. -/
theorem stackWalk_eq_codegen {stack : List Frame} (h : Disciplined stack) :
    stackWalkLocation stack = stack.head?.map Frame.codegenLocation := by
  induction h with
  | bottom frame hTracked hReceived => exact stackWalk_untracked_frame frame [] hTracked hReceived
  | pushUntracked frame caller rest hTracked hReceived _ _ =>
    exact stackWalk_untracked_frame frame (caller :: rest) hTracked hReceived
  | pushTracked frame caller rest hTracked hReceived _ ih =>
    show _ = some (resolveChain frame.chain frame.received frame.span)
    rw [stackWalkLocation_cons, resolveChain_eq_chainOutcome, hTracked, hReceived]
    cases chainOutcome frame.chain frame.span with
    | mk stopped s =>
      cases stopped
      · exact ih
      · rfl

/-- A tracked definition reached through a declaration without the attribute: the callee frame
is tracked but its caller passed nothing, so the callee reads whatever its argument slot holds. -/
def mismatchedStack (callSite junk : Span) : List Frame :=
  [ { tracked := true, received := some junk, chain := [], span := 0 },
    { tracked := false, received := none, chain := [], span := callSite } ]

/-- Outside the discipline the two mechanisms part ways: the stack walk reports the call site
while the implicit-argument read returns the stale slot contents. -/
theorem mismatched_declaration_diverges (callSite junk : Span) (h : junk ≠ callSite) :
    stackWalkLocation (mismatchedStack callSite junk) = some callSite ∧
    (mismatchedStack callSite junk).head?.map Frame.codegenLocation = some junk ∧
    ¬ Disciplined (mismatchedStack callSite junk) := by
  refine ⟨rfl, rfl, fun hDisciplined => ?_⟩
  have agree : some callSite = some junk := stackWalk_eq_codegen hDisciplined
  exact h (Option.some.inj agree).symm

/-! ## 5. The implicit argument in `FnAbi`, argument slots, and the reify shim -/

/-- What an entry of `FnAbi::args` stands for. -/
inductive ArgClass where
  /-- An explicit argument of the MIR signature (after untupling). -/
  | value
  /-- The implicit `&'static Location<'static>`. -/
  | location
  deriving DecidableEq

/-- `FnAbi::args` as built by `fn_abi_new_uncached`: the explicit arguments, then the caller
location if and only if `instance.def.requires_caller_location(tcx)`. -/
def lowerFnAbiTrackCaller (mirArity : Nat) (requiresCallerLocation : Bool) : List ArgClass :=
  List.replicate mirArity ArgClass.value
    ++ (if requiresCallerLocation then [ArgClass.location] else [])

/-- `FnAbiDesc::for_fn_ptr` sets `caller_location: None`: a function pointer type never has the
implicit argument. -/
def fnPtrAbi (arity : Nat) : List ArgClass := lowerFnAbiTrackCaller arity false

theorem length_replicate_append {α : Type} (n : Nat) (a : α) (tail : List α) :
    (List.replicate n a ++ tail).length = n + tail.length := by
  rw [List.length_append, List.length_replicate]

/-- ABI arity: one more than the MIR arity exactly for tracked instances. -/
theorem lowerFnAbiTrackCaller_length (mirArity : Nat) (requiresCallerLocation : Bool) :
    (lowerFnAbiTrackCaller mirArity requiresCallerLocation).length
      = mirArity + (if requiresCallerLocation then 1 else 0) := by
  cases requiresCallerLocation
  · exact length_replicate_append mirArity ArgClass.value []
  · exact length_replicate_append mirArity ArgClass.value [ArgClass.location]

/-- A pointer of arity `N` and a tracked callee of MIR arity `N` disagree on ABI arity. -/
theorem tracked_abi_arity_is_fnPtr_arity_succ (arity : Nat) :
    (lowerFnAbiTrackCaller arity true).length = (fnPtrAbi arity).length + 1 := by
  rw [lowerFnAbiTrackCaller_length, fnPtrAbi, lowerFnAbiTrackCaller_length]
  rfl

/-- Contents of an argument slot. -/
inductive Word where
  /-- An explicit argument value. -/
  | val (v : Nat)
  /-- The address of the `Location` constant for a span. -/
  | loc (span : Span)
  /-- Whatever an earlier computation left behind. -/
  | stale (junk : Nat)
  deriving DecidableEq

def Word.hasClass : Word → ArgClass → Bool
  | .val _, .value => true
  | .loc _, .location => true
  | _, _ => false

/-- Argument slots in ABI order (on x86-64 with integer-class arguments: `%rdi`, `%rsi`, `%rdx`,
`%rcx`, `%r8`, `%r9`, then stack slots). -/
abbrev Regs := Nat → Word

/-- Drop slot 0. -/
def Regs.tail (regs : Regs) : Regs := fun i => regs (i + 1)

/-- Put a word in front. -/
def Regs.cons (word : Word) (regs : Regs) : Regs
  | 0 => word
  | i + 1 => regs i

/-- A call that passes exactly the explicit arguments `vals`: slots `0 .. vals.length - 1` are
written, every later slot keeps its previous contents. -/
noncomputable def writeArgs : List Nat → Regs → Regs
  | [], stale => stale
  | v :: rest, stale => Regs.cons (Word.val v) (writeArgs rest stale.tail)

/-- Write the address of the `Location` for `span` into slot `n`, leaving all other slots alone:
what a caller of a tracked instance with `n` explicit arguments does after writing them. -/
noncomputable def writeLocationSlot : Nat → Span → Regs → Regs
  | 0, span, regs => Regs.cons (Word.loc span) regs.tail
  | n + 1, span, regs => Regs.cons (regs 0) (writeLocationSlot n span regs.tail)

/-- The body that `build_call_shim` produces for a reify shim of a tracked function with `n`
explicit arguments: forward them and call the function directly, with `fn_span = def_span`, so
that the definition span is passed as the caller location. -/
def reifyToFnPtrShim (n : Nat) (defSpan : Span) (regs : Regs) : Regs :=
  writeLocationSlot n defSpan regs

/-- Slot `i` holds a word of class `abi[i]`, for every entry of `abi`. -/
noncomputable def WellTyped : List ArgClass → Regs → Prop
  | [], _ => True
  | cls :: rest, regs => (regs 0).hasClass cls = true ∧ WellTyped rest regs.tail

theorem writeLocationSlot_slot : ∀ (n : Nat) (span : Span) (regs : Regs),
    writeLocationSlot n span regs n = Word.loc span
  | 0, _, _ => rfl
  | n + 1, span, regs => writeLocationSlot_slot n span regs.tail

theorem writeLocationSlot_below : ∀ (n : Nat) (span : Span) (regs : Regs) (i : Nat),
    i < n → writeLocationSlot n span regs i = regs i
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, _, 0, _ => rfl
  | n + 1, span, regs, i + 1, h =>
    writeLocationSlot_below n span regs.tail i (Nat.lt_of_succ_lt_succ h)

theorem writeLocationSlot_wellTyped : ∀ (n : Nat) (span : Span) (regs : Regs),
    WellTyped (fnPtrAbi n) regs →
    WellTyped (lowerFnAbiTrackCaller n true) (writeLocationSlot n span regs)
  | 0, _, _, _ => ⟨rfl, trivial⟩
  | n + 1, span, regs, h => ⟨h.1, writeLocationSlot_wellTyped n span regs.tail h.2⟩

theorem writeArgs_wellTyped : ∀ (vals : List Nat) (stale : Regs),
    WellTyped (fnPtrAbi vals.length) (writeArgs vals stale)
  | [], _ => trivial
  | _ :: rest, stale => ⟨rfl, writeArgs_wellTyped rest stale.tail⟩

theorem writeArgs_next_slot : ∀ (vals : List Nat) (stale : Regs),
    writeArgs vals stale vals.length = stale vals.length
  | [], _ => rfl
  | _ :: rest, stale => writeArgs_next_slot rest stale.tail

theorem wellTyped_tracked_slot : ∀ (n : Nat) (regs : Regs),
    WellTyped (lowerFnAbiTrackCaller n true) regs → (regs n).hasClass ArgClass.location = true
  | 0, _, h => h.1
  | n + 1, regs, h => wellTyped_tracked_slot n regs.tail h.2

/-- **ABI arity and slot typing of the reify shim.** An indirect caller through a pointer of
arity `N` writes `N` explicit arguments. The shim turns that into a slot assignment that is
well-typed for the tracked callee's `N + 1`-entry ABI, forwards the explicit arguments unchanged,
and puts the definition-site `Location` into slot `N`, whatever that slot held before. -/
theorem reifyToFnPtrShim_abi_safe (vals : List Nat) (defSpan : Span) (stale : Regs) :
    (lowerFnAbiTrackCaller vals.length true).length = (fnPtrAbi vals.length).length + 1 ∧
    WellTyped (fnPtrAbi vals.length) (writeArgs vals stale) ∧
    WellTyped (lowerFnAbiTrackCaller vals.length true)
      (reifyToFnPtrShim vals.length defSpan (writeArgs vals stale)) ∧
    (∀ i, i < vals.length →
      reifyToFnPtrShim vals.length defSpan (writeArgs vals stale) i = writeArgs vals stale i) ∧
    reifyToFnPtrShim vals.length defSpan (writeArgs vals stale) vals.length = Word.loc defSpan :=
  ⟨tracked_abi_arity_is_fnPtr_arity_succ vals.length,
   writeArgs_wellTyped vals stale,
   writeLocationSlot_wellTyped vals.length defSpan _ (writeArgs_wellTyped vals stale),
   fun i h => writeLocationSlot_below vals.length defSpan _ i h,
   writeLocationSlot_slot vals.length defSpan _⟩

theorem writeArgs_all_locations_wellTyped (other : Span) : ∀ (vals : List Nat),
    WellTyped (lowerFnAbiTrackCaller vals.length true) (writeArgs vals (fun _ => Word.loc other))
  | [] => ⟨rfl, trivial⟩
  | _ :: rest => ⟨rfl, writeArgs_all_locations_wellTyped other rest⟩

/-- **Sharpness 1: without the reify shim the implicit slot is not under the program's control.**
If a pointer of arity `N` led straight to the tracked function, the callee would read slot `N`,
which the caller never wrote:

1. the value read is whatever the slot held before the call;
2. the slot assignment can be ill-typed for the callee's ABI;
3. it can also be well-typed and name an arbitrary, unrelated location;
4. with the shim the value read is the definition-site location for every prior state. -/
theorem ce1_omitting_reify_shim_corrupts_implicit_location_register_abi
    (vals : List Nat) (defSpan : Span) :
    (∀ stale : Regs, writeArgs vals stale vals.length = stale vals.length) ∧
    (∃ stale : Regs,
      ¬ WellTyped (lowerFnAbiTrackCaller vals.length true) (writeArgs vals stale)) ∧
    (∀ other : Span, ∃ stale : Regs,
      WellTyped (lowerFnAbiTrackCaller vals.length true) (writeArgs vals stale) ∧
      writeArgs vals stale vals.length = Word.loc other) ∧
    (∀ stale : Regs,
      reifyToFnPtrShim vals.length defSpan (writeArgs vals stale) vals.length
        = Word.loc defSpan) := by
  refine ⟨writeArgs_next_slot vals, ⟨fun _ => Word.stale 0, fun h => ?_⟩,
    fun other => ⟨fun _ => Word.loc other, writeArgs_all_locations_wellTyped other vals,
      writeArgs_next_slot vals _⟩,
    fun stale => writeLocationSlot_slot vals.length defSpan _⟩
  have bad := wellTyped_tracked_slot vals.length _ h
  rw [writeArgs_next_slot] at bad
  cases bad

/-! ## 6. Vtable slots: attribute on the trait declaration versus on the impl only -/

/-- Where `#[track_caller]` was written for one trait method and one implementation. -/
structure MethodAttrs where
  /-- On the method in the trait (bodiless declaration or provided body). -/
  declTracked : Bool
  /-- On the method in the `impl` block. -/
  implTracked : Bool
  /-- The implementation is the trait's provided body, not an `impl` override. -/
  provided : Bool

/-- `should_inherit_track_caller`: the item is a method of a trait impl and the corresponding
trait method carries the flag. -/
def shouldInheritTrackCaller (attrs : MethodAttrs) : Bool :=
  !attrs.provided && attrs.declTracked

/-- `requires_caller_location` of the implementing item: its own attribute or an inherited one;
for a provided body the item is the trait method itself. -/
def implRequiresCallerLocation (attrs : MethodAttrs) : Bool :=
  if attrs.provided then attrs.declTracked else attrs.implTracked || attrs.declTracked

/-- `requires_caller_location` of `InstanceKind::Virtual(trait_method, _)`: the trait method's
flag. This is what the virtual call site knows. -/
def virtualRequiresCallerLocation (attrs : MethodAttrs) : Bool := attrs.declTracked

/-- `needs_track_caller_shim` in `Instance::expect_resolve_for_vtable`. -/
def needsTrackCallerShim (attrs : MethodAttrs) : Bool :=
  implRequiresCallerLocation attrs && !shouldInheritTrackCaller attrs && !attrs.provided

inductive VtableSlot where
  /-- The slot holds the implementing item itself. -/
  | direct
  /-- The slot holds a reify shim in front of the implementing item. -/
  | reifyShim
  deriving DecidableEq

def vtableSlot (attrs : MethodAttrs) : VtableSlot :=
  if needsTrackCallerShim attrs then VtableSlot.reifyShim else VtableSlot.direct

/-- ABI assumed by a virtual call site. -/
def virtualCallerAbi (attrs : MethodAttrs) (arity : Nat) : List ArgClass :=
  lowerFnAbiTrackCaller arity (virtualRequiresCallerLocation attrs)

/-- ABI of the function the vtable slot points to. -/
def vtableSlotAbi (attrs : MethodAttrs) (arity : Nat) : List ArgClass :=
  match vtableSlot attrs with
  | .direct => lowerFnAbiTrackCaller arity (implRequiresCallerLocation attrs)
  | .reifyShim => lowerFnAbiTrackCaller arity false

/-- The shim is inserted exactly when it is needed: for every placement of the attribute, the
virtual call site and the vtable slot agree on the ABI. -/
theorem vtable_abi_agreement (attrs : MethodAttrs) (arity : Nat) :
    virtualCallerAbi attrs arity = vtableSlotAbi attrs arity := by
  obtain ⟨declTracked, implTracked, provided⟩ := attrs
  cases declTracked <;> cases implTracked <;> cases provided <;> rfl

/-- A dynamic call `receiver.method(vals)` through a vtable: what the implementation's
`caller_location` reads (`none` when the implementation is not tracked). The call site writes
the explicit arguments and, if the trait declaration is tracked, its own location; a reify shim
in the slot then overwrites the implicit slot with the implementation's definition span. -/
def vtableMethodDispatch (attrs : MethodAttrs) (vals : List Nat) (callSite implDef : Span)
    (stale : Regs) : Option Word :=
  let atCallSite : Regs :=
    if virtualRequiresCallerLocation attrs then
      writeLocationSlot vals.length callSite (writeArgs vals stale)
    else writeArgs vals stale
  let atImpl : Regs :=
    match vtableSlot attrs with
    | .direct => atCallSite
    | .reifyShim => reifyToFnPtrShim vals.length implDef atCallSite
  if implRequiresCallerLocation attrs then some (atImpl vals.length) else none

/-- **Attribute on the trait declaration:** no shim, and the implementation sees the location of
the dynamic call itself. This covers impls with or without their own attribute and provided
bodies. -/
theorem vtable_decl_tracked_reports_call_site (attrs : MethodAttrs)
    (hDecl : attrs.declTracked = true) (vals : List Nat) (callSite implDef : Span)
    (stale : Regs) :
    vtableSlot attrs = VtableSlot.direct ∧
    vtableMethodDispatch attrs vals callSite implDef stale = some (Word.loc callSite) := by
  obtain ⟨declTracked, implTracked, provided⟩ := attrs
  cases hDecl
  cases implTracked <;> cases provided <;>
    exact ⟨rfl, congrArg some (writeLocationSlot_slot vals.length callSite _)⟩

/-- **Attribute on the impl only:** the slot holds a reify shim, and the implementation sees its
own definition span, not the call site. -/
theorem vtable_impl_only_reports_impl_definition (attrs : MethodAttrs)
    (hDecl : attrs.declTracked = false) (hImpl : attrs.implTracked = true)
    (hProvided : attrs.provided = false) (vals : List Nat) (callSite implDef : Span)
    (stale : Regs) :
    vtableSlot attrs = VtableSlot.reifyShim ∧
    vtableMethodDispatch attrs vals callSite implDef stale = some (Word.loc implDef) := by
  obtain ⟨declTracked, implTracked, provided⟩ := attrs
  cases hDecl
  cases hImpl
  cases hProvided
  exact ⟨rfl, congrArg some (writeLocationSlot_slot vals.length implDef _)⟩

/-- **No attribute anywhere:** no shim and nothing is read. -/
theorem vtable_untracked_reads_nothing (attrs : MethodAttrs)
    (hDecl : attrs.declTracked = false) (hImpl : attrs.implTracked = false)
    (vals : List Nat) (callSite implDef : Span) (stale : Regs) :
    vtableSlot attrs = VtableSlot.direct ∧
    vtableMethodDispatch attrs vals callSite implDef stale = none := by
  obtain ⟨declTracked, implTracked, provided⟩ := attrs
  cases hDecl
  cases hImpl
  cases provided <;> exact ⟨rfl, rfl⟩

/-- In every case the result is independent of what the slots held before the call. -/
theorem vtableMethodDispatch_ignores_stale (attrs : MethodAttrs) (vals : List Nat)
    (callSite implDef : Span) (stale₁ stale₂ : Regs) :
    vtableMethodDispatch attrs vals callSite implDef stale₁
      = vtableMethodDispatch attrs vals callSite implDef stale₂ := by
  obtain ⟨declTracked, implTracked, provided⟩ := attrs
  cases declTracked
  · cases implTracked
    · rw [(vtable_untracked_reads_nothing ⟨false, false, provided⟩ rfl rfl vals callSite implDef
          stale₁).2,
        (vtable_untracked_reads_nothing ⟨false, false, provided⟩ rfl rfl vals callSite implDef
          stale₂).2]
    · cases provided
      · rw [(vtable_impl_only_reports_impl_definition ⟨false, true, false⟩ rfl rfl rfl vals callSite
            implDef stale₁).2,
          (vtable_impl_only_reports_impl_definition ⟨false, true, false⟩ rfl rfl rfl vals callSite
            implDef stale₂).2]
      · rfl
  · rw [(vtable_decl_tracked_reports_call_site ⟨true, implTracked, provided⟩ rfl vals callSite
        implDef stale₁).2,
      (vtable_decl_tracked_reports_call_site ⟨true, implTracked, provided⟩ rfl vals callSite
        implDef stale₂).2]

/-! ## 7. Sharpness 2: the scope of an untracked inlined callee must be kept -/

/-- A variant of the inliner that records no scope for an untracked callee: its entry is missing
from every chain. -/
def collapseUntracked (chain : List InlinedEntry) : List InlinedEntry :=
  chain.filter (fun entry => entry.1)

/-- A variant of the walk that does not stop at an untracked callee. -/
def markAllTracked (chain : List InlinedEntry) : List InlinedEntry :=
  chain.map (fun entry => (true, entry.2))

/-- Whenever tracked callees are inlined into an untracked wrapper that is itself inlined into a
tracked function, dropping the wrapper's scope replaces the wrapper-internal call site `site` by
the enclosing function's own implicit location `enclosing`. -/
theorem collapsing_untracked_scope_leaks_enclosing_location (site wrapperCall enclosing : Span) :
    ∀ (innerSites : List Span) (span : Span),
      resolveChain (innerSites.map (fun s => (true, s)) ++ [(true, site), (false, wrapperCall)])
          (some enclosing) span = site ∧
      resolveChain
          (collapseUntracked
            (innerSites.map (fun s => (true, s)) ++ [(true, site), (false, wrapperCall)]))
          (some enclosing) span = enclosing
  | [], _ => ⟨rfl, rfl⟩
  | s :: rest, _ =>
    collapsing_untracked_scope_leaks_enclosing_location site wrapperCall enclosing rest s

/-- From here on "the probe" is the program `probe_src/track_caller_probe.rs` shipped next to
this file, and its spans are encoded as `line * 1000 + column`. Scope chain of the
`caller_location` call in the optimised body of the probe's `tracked_outer_site`, innermost
first: `Location::caller`, `leaf_tracked`, `mid_tracked`, `top_tracked` (all tracked), the
untracked `untracked_wrapper`, and the tracked `tracked_outer_via_wrapper`. -/
def trackedOuterSiteChain : List InlinedEntry :=
  [(true, 26009), (true, 32005), (true, 38005), (true, 49005), (false, 61005), (true, 66005)]

/-- Scope chain of the same call in the optimised body of the probe's `wrapper_site`. -/
def wrapperSiteChain : List InlinedEntry :=
  [(true, 26009), (true, 32005), (true, 38005), (true, 49005), (false, 54005)]

/-- Scope chain of the same call in the optimised body of the probe's `direct_site`. -/
def directSiteChain : List InlinedEntry :=
  [(true, 26009), (true, 32005), (true, 38005), (true, 43005)]

/-- **Sharpness 2.** On the scope chain of the probe's `tracked_outer_site`, the walk reports the
call inside the untracked wrapper (line 49), as executed. With the untracked scope collapsed it
would report the call site of the outer tracked function instead (line 66), a location that the
real compiler never reports for this program. -/
theorem ce2_collapsing_untracked_inline_scope_leaks_outer_caller_location :
    resolveChain trackedOuterSiteChain none 181009 = 49005 ∧
    resolveChain (collapseUntracked trackedOuterSiteChain) none 181009 = 66005 ∧
    (49005 : Span) ≠ 66005 :=
  ⟨rfl, rfl, by decide⟩

/-- Companion: not stopping at the untracked wrapper reports the wrapper's own call site
(line 54) for the probe's `wrapper_site`, instead of the executed answer (line 49). -/
theorem walking_through_untracked_scope_reports_wrapper_call_site :
    resolveChain wrapperSiteChain none 181009 = 49005 ∧
    resolveChain (markAllTracked wrapperSiteChain) none 181009 = 54005 ∧
    (49005 : Span) ≠ 54005 :=
  ⟨rfl, rfl, by decide⟩

/-! ## 8. The probe's scope tables, executed -/

/-- `source_scopes` of the probe's `direct_site` after MIR inlining, restricted to the scopes on
the path of the `caller_location` call (scope 4). -/
def directSiteScopes : ScopeTree Nat
  | 1 => { parentScope := some 0, inlined := some (true, 43005), inlinedParentScope := none }
  | 2 => { parentScope := some 1, inlined := some (true, 38005), inlinedParentScope := some 1 }
  | 3 => { parentScope := some 2, inlined := some (true, 32005), inlinedParentScope := some 2 }
  | 4 => { parentScope := some 3, inlined := some (true, 26009), inlinedParentScope := some 3 }
  | _ => { parentScope := none, inlined := none, inlinedParentScope := none }

/-- The same for the probe's `wrapper_site` (the call is in scope 5). -/
def wrapperSiteScopes : ScopeTree Nat
  | 1 => { parentScope := some 0, inlined := some (false, 54005), inlinedParentScope := none }
  | 2 => { parentScope := some 1, inlined := some (true, 49005), inlinedParentScope := some 1 }
  | 3 => { parentScope := some 2, inlined := some (true, 38005), inlinedParentScope := some 2 }
  | 4 => { parentScope := some 3, inlined := some (true, 32005), inlinedParentScope := some 3 }
  | 5 => { parentScope := some 4, inlined := some (true, 26009), inlinedParentScope := some 4 }
  | _ => { parentScope := none, inlined := none, inlinedParentScope := none }

/-- The same for the probe's `tracked_outer_site` (the call is in scope 6). -/
def trackedOuterSiteScopes : ScopeTree Nat
  | 1 => { parentScope := some 0, inlined := some (true, 66005), inlinedParentScope := none }
  | 2 => { parentScope := some 1, inlined := some (false, 61005), inlinedParentScope := some 1 }
  | 3 => { parentScope := some 2, inlined := some (true, 49005), inlinedParentScope := some 2 }
  | 4 => { parentScope := some 3, inlined := some (true, 38005), inlinedParentScope := some 3 }
  | 5 => { parentScope := some 4, inlined := some (true, 32005), inlinedParentScope := some 4 }
  | 6 => { parentScope := some 5, inlined := some (true, 26009), inlinedParentScope := some 5 }
  | _ => { parentScope := none, inlined := none, inlinedParentScope := none }

/-- The transcribed walk reproduces the three executed answers: `DIRECT=43:5`, `WRAPPER=49:5`,
`TRACKED_OUTER_WRAPPER=49:5`. -/
theorem probe_scope_tables_reproduce_executed_locations :
    findOutermostTrackedCallSite directSiteScopes none 8 4 181009 = some 43005 ∧
    findOutermostTrackedCallSite wrapperSiteScopes none 8 5 181009 = some 49005 ∧
    findOutermostTrackedCallSite trackedOuterSiteScopes none 8 6 181009 = some 49005 :=
  ⟨rfl, rfl, rfl⟩

/-- Body of the probe's `untracked_wrapper` once its own callees are inlined: scope 0 is its
outermost scope and the `caller_location` call sits in scope 4. -/
def untrackedWrapperScopes : ScopeTree Nat
  | 1 => { parentScope := some 0, inlined := some (true, 49005), inlinedParentScope := none }
  | 2 => { parentScope := some 1, inlined := some (true, 38005), inlinedParentScope := some 1 }
  | 3 => { parentScope := some 2, inlined := some (true, 32005), inlinedParentScope := some 2 }
  | 4 => { parentScope := some 3, inlined := some (true, 26009), inlinedParentScope := some 3 }
  | _ => { parentScope := none, inlined := none, inlinedParentScope := none }

/-- A body with a single scope and nothing inlined yet. -/
def singleScope : ScopeTree Nat :=
  fun _ => { parentScope := none, inlined := none, inlinedParentScope := none }

/-- Splicing `untracked_wrapper` into a fresh `wrapper_site` (call at line 54) with the
transcribed rewriting gives the executed answer for the spliced `caller_location` call, both
when the wrapper is recorded as untracked (as it is) and, counterfactually, as tracked. -/
theorem probe_remap_reproduces_executed_location :
    findOutermostTrackedCallSite
        (remapScopesOnInline singleScope 0 54005 false untrackedWrapperScopes 0)
        none 8 (.inr 4) 181009 = some 49005 ∧
    findOutermostTrackedCallSite
        (remapScopesOnInline singleScope 0 54005 true untrackedWrapperScopes 0)
        none 8 (.inr 4) 181009 = some 54005 :=
  ⟨rfl, rfl⟩

/-- The chain of the probe's `wrapper_site` table at the scope of the `caller_location` call is
the chain used in section 7: the hypotheses of the general theorems are met by real tables. -/
theorem probe_wrapper_site_hasChain : HasChain wrapperSiteScopes 5 wrapperSiteChain :=
  .step (parent := 4) rfl
    (.step (parent := 3) rfl
      (.step (parent := 2) rfl
        (.step (parent := 1) rfl (.root rfl rfl) rfl) rfl) rfl) rfl

/-- The stand-alone `untracked_wrapper` table satisfies the inliner's assertions. -/
theorem probe_untrackedWrapper_wellFormed : CalleeRootWellFormed untrackedWrapperScopes 0 where
  rootHasNoParent := rfl
  parentlessIsFresh := fun k h =>
    match k, h with
    | 0, _ => ⟨rfl, rfl⟩
    | 1, h => absurd h (by decide)
    | 2, h => absurd h (by decide)
    | 3, h => absurd h (by decide)
    | 4, h => absurd h (by decide)
    | _ + 5, _ => ⟨rfl, rfl⟩

/-! ## Axiom audit -/

#print axioms resolveChain_append
#print axioms find_of_hasChain
#print axioms hasChain_remap_callee
#print axioms remapScopesOnInline_exact
#print axioms remapScopesOnInline_caller_unchanged
#print axioms Node.inl_observations_eq_call
#print axioms location_caller_invariant_under_inlining
#print axioms observations_eq_of_uninline_eq
#print axioms stackWalk_eq_codegen
#print axioms mismatched_declaration_diverges
#print axioms lowerFnAbiTrackCaller_length
#print axioms reifyToFnPtrShim_abi_safe
#print axioms ce1_omitting_reify_shim_corrupts_implicit_location_register_abi
#print axioms vtable_abi_agreement
#print axioms vtable_decl_tracked_reports_call_site
#print axioms vtable_impl_only_reports_impl_definition
#print axioms vtable_untracked_reads_nothing
#print axioms vtableMethodDispatch_ignores_stale
#print axioms collapsing_untracked_scope_leaks_enclosing_location
#print axioms ce2_collapsing_untracked_inline_scope_leaks_outer_caller_location
#print axioms walking_through_untracked_scope_reports_wrapper_call_site
#print axioms probe_scope_tables_reproduce_executed_locations
#print axioms probe_remap_reproduces_executed_location
#print axioms probe_wrapper_site_hasChain
#print axioms probe_untrackedWrapper_wellFormed

end

end TrackCaller
