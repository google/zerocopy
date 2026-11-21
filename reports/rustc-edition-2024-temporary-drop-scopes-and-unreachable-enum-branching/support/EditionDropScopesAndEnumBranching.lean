/-!
# Edition-indexed temporary drop scopes and `UnreachableEnumBranching`

Self-contained Lean 4 development (core library only, no imports beyond the
prelude). It has two independent parts.

**Part A** transcribes the two rustc mechanisms that determine when a temporary
with a destructor is dropped:

* `ScopeTree::default_temporary_scope`
  (`compiler/rustc_middle/src/middle/region.rs`), which walks the parent chain
  of region scopes built by `resolve_block` / `resolve_expr`
  (`compiler/rustc_hir_analysis/src/check/region.rs`). Those two functions are
  the only places where the edition is consulted: a block tail expression gets
  a `Destruction` scope iff the edition is at least 2024, and an `if` gets an
  `IfThenRescope` scope instead of an `IfThen` scope iff the edition is at
  least 2024.
* the MIR-building scope stack (`compiler/rustc_mir_build/src/builder/scope.rs`):
  `schedule_drop` appends a drop to the stack entry whose region scope equals
  the requested scope, `pop_scope` emits the scheduled drops of the innermost
  entry in reverse scheduling order, and `break_for_else` emits the drops of
  every entry nested inside the `if` condition scope on the pattern-failure
  path.

`compileBlockTail`, `compileIfLetElse` and `compileMatch` run these two
mechanisms on three source shapes and return the linear event trace of the
normal (non-unwinding) path.

**Part B** models `Rvalue::Discriminant` followed by `SwitchInt` for a
direct-tagged enum, the `UnreachableEnumBranching` rewrite
(`compiler/rustc_mir_transform/src/unreachable_enum_branching.rs`), and three
candidate semantics for reading a discriminant.

Modeling limits (also listed in the accompanying report): unwinding paths,
storage markers, drop flags, moves out of locals, lifetime extension,
let-else, let chains and match guards are not modeled; enum payloads and niche
encodings are not modeled; block bodies after the switch are abstracted to an
arbitrary outcome function.

Every definition is marked `noncomputable`: nothing here is meant to be run,
and skipping code generation keeps compiler-only auxiliary constants out of
the environment, so the module consists of ordinary definitions, inductive
types and theorems only.
-/

namespace EditionDropScopesAndEnumBranching

/-! ## Part A.1: region scopes and `default_temporary_scope` -/

/-- Language edition of the span that contains the construct. -/
inductive Edition where
  | ed2021
  | ed2024

/-- `Span::at_least_rust_2024` / `Edition::at_least_rust_2024`. -/
noncomputable def Edition.atLeastRust2024 : Edition → Bool
  | .ed2021 => false
  | .ed2024 => true

/-- `rustc_middle::middle::region::ScopeData`. -/
inductive ScopeData where
  | node
  | callSite
  | arguments
  | destruction
  | ifThen
  | ifThenRescope
  | matchGuard
  | remainder (firstStatementIndex : Nat)

noncomputable def ScopeData.beq : ScopeData → ScopeData → Bool
  | .node, .node => true
  | .callSite, .callSite => true
  | .arguments, .arguments => true
  | .destruction, .destruction => true
  | .ifThen, .ifThen => true
  | .ifThenRescope, .ifThenRescope => true
  | .matchGuard, .matchGuard => true
  | .remainder i, .remainder j => Nat.beq i j
  | _, _ => false

noncomputable def ScopeData.isRemainder : ScopeData → Bool
  | .remainder _ => true
  | _ => false

/-- `rustc_middle::middle::region::Scope`: an HIR item-local id plus scope data. -/
structure Scope where
  localId : Nat
  data : ScopeData

noncomputable def Scope.beq (a b : Scope) : Bool :=
  Nat.beq a.localId b.localId && a.data.beq b.data

theorem ScopeData.beq_refl : ∀ d : ScopeData, d.beq d = true
  | .node => rfl
  | .callSite => rfl
  | .arguments => rfl
  | .destruction => rfl
  | .ifThen => rfl
  | .ifThenRescope => rfl
  | .matchGuard => rfl
  | .remainder i => Nat.beq_refl i

theorem Scope.beq_refl (s : Scope) : s.beq s = true := by
  unfold Scope.beq
  rw [Nat.beq_refl, ScopeData.beq_refl]
  rfl

theorem ScopeData.beq_false_of_isRemainder :
    ∀ a b : ScopeData, a.isRemainder = true → b.isRemainder = false → a.beq b = false
  | .remainder _, .node, _, _ => rfl
  | .remainder _, .callSite, _, _ => rfl
  | .remainder _, .arguments, _, _ => rfl
  | .remainder _, .destruction, _, _ => rfl
  | .remainder _, .ifThen, _, _ => rfl
  | .remainder _, .ifThenRescope, _, _ => rfl
  | .remainder _, .matchGuard, _, _ => rfl
  | .remainder _, .remainder _, _, hb => Bool.noConfusion hb
  | .node, _, ha, _ => Bool.noConfusion ha
  | .callSite, _, ha, _ => Bool.noConfusion ha
  | .arguments, _, ha, _ => Bool.noConfusion ha
  | .destruction, _, ha, _ => Bool.noConfusion ha
  | .ifThen, _, ha, _ => Bool.noConfusion ha
  | .ifThenRescope, _, ha, _ => Bool.noConfusion ha
  | .matchGuard, _, ha, _ => Bool.noConfusion ha

/-- The chain of enclosing region scopes (`ScopeTree::parent_map`), innermost
first. -/
abbrev Chain := List Scope

/-- `ScopeTree::default_temporary_scope`. `inner` is the scope the walk
currently stands on and the list is its parent chain. The walk stops below a
`Destruction` scope (returning the child) or at an `IfThenRescope` /
`MatchGuard` scope (returning that scope); every other scope kind, including
the Edition 2021 `IfThen`, is passed through. `none` models the compiler's
`span_bug!("no enclosing temporary scope")`. -/
noncomputable def defaultTemporaryScope : Scope → Chain → Option Scope
  | _, [] => none
  | inner, p :: rest =>
    match p.data with
    | .destruction => some inner
    | .ifThenRescope => some p
    | .matchGuard => some p
    | .node => defaultTemporaryScope p rest
    | .callSite => defaultTemporaryScope p rest
    | .arguments => defaultTemporaryScope p rest
    | .ifThen => defaultTemporaryScope p rest
    | .remainder _ => defaultTemporaryScope p rest

/-- `ScopeTree::temporary_scope` for an expression without a recorded extended
temporary scope: start from the expression's own `Node` scope. -/
noncomputable def temporaryScope (exprId : Nat) (parents : Chain) : Option Scope :=
  defaultTemporaryScope ⟨exprId, .node⟩ parents

/-- `ScopeResolutionVisitor::enter_node_scope_with_dtor`: a terminating node
gets a `Destruction` scope as the parent of its `Node` scope. -/
noncomputable def enterNodeScopeWithDtor (id : Nat) (terminating : Bool) (cx : Chain) : Chain :=
  match terminating with
  | true => ⟨id, .node⟩ :: ⟨id, .destruction⟩ :: cx
  | false => ⟨id, .node⟩ :: cx

/-- `resolve_stmt`: every statement is terminating. -/
noncomputable def resolveStmt (id : Nat) (cx : Chain) : Chain := enterNodeScopeWithDtor id true cx

/-- `resolve_expr` for an expression that the caller did not mark terminating
(`visit_expr` passes `false`). -/
noncomputable def resolveExpr (id : Nat) (cx : Chain) : Chain := enterNodeScopeWithDtor id false cx

/-- `resolve_block`, tail-expression case: the tail expression is resolved with
`terminating = edition.at_least_rust_2024()`. -/
noncomputable def resolveBlockTail (ed : Edition) (tailId : Nat) (cx : Chain) : Chain :=
  enterNodeScopeWithDtor tailId ed.atLeastRust2024 cx

/-- `resolve_expr`, `hir::ExprKind::If` case: the scope entered around the
condition and the `then` block. -/
noncomputable def ifThenScope (ed : Edition) (thenId : Nat) : Scope :=
  match ed.atLeastRust2024 with
  | true => ⟨thenId, .ifThenRescope⟩
  | false => ⟨thenId, .ifThen⟩

/-- `resolve_block`, `let` statement case, iterated: statement `i` of block
`blockId` enters `Remainder(i)` as a child of the previous remainder scope. -/
noncomputable def remainderChain (blockId : Nat) : Nat → List Nat → Chain → Chain
  | _, [], cx => cx
  | i, _ :: ls, cx => remainderChain blockId (i + 1) ls (⟨blockId, .remainder i⟩ :: cx)

/-! ## Part A.2: the MIR-building scope stack -/

/-- A MIR local that holds a value with a destructor. -/
abbrev Local := Nat

/-- Events on the normal path of the lowered MIR. -/
inductive Event where
  /-- a value with a destructor is written into the local -/
  | init (l : Local)
  /-- `drop(_l)` -/
  | drop (l : Local)
  /-- the body of a `then` block, `else` block or match arm runs -/
  | body (tag : Nat)

/-- One entry of `rustc_mir_build::builder::scope::Scopes::scopes`. `drops`
is kept in scheduling order (oldest first), like `Scope::drops`. -/
structure BuildScope where
  region : Scope
  drops : List Local

/-- The part of the MIR builder state the model needs: the scope stack
(innermost first) and the events emitted so far (oldest first). -/
structure Builder where
  scopes : List BuildScope
  events : List Event

noncomputable def initEvents (ls : List Local) : List Event := ls.map Event.init

/-- Drops of one scope in emission order: reverse scheduling order
(`build_scope_drops` iterates `scope.drops.iter().rev()`). -/
noncomputable def dropEvents (ls : List Local) : List Event := ls.reverse.map Event.drop

/-- `Builder::push_scope`. -/
noncomputable def Builder.pushScope (s : Scope) (b : Builder) : Builder :=
  ⟨⟨s, []⟩ :: b.scopes, b.events⟩

noncomputable def Builder.emit (e : Event) (b : Builder) : Builder :=
  ⟨b.scopes, b.events ++ [e]⟩

/-- The search loop of `Builder::schedule_drop`: from the innermost entry
outward, push the drop onto the first entry whose region scope equals
`target`. `none` models `span_bug!("region scope .. not in scope to drop ..")`. -/
noncomputable def scheduleIn (target : Scope) (l : Local) : List BuildScope → Option (List BuildScope)
  | [] => none
  | sc :: rest =>
    match sc.region.beq target with
    | true => some (⟨sc.region, sc.drops ++ [l]⟩ :: rest)
    | false =>
      match scheduleIn target l rest with
      | some rest' => some (sc :: rest')
      | none => none

noncomputable def Builder.scheduleDrop (target : Scope) (l : Local) (b : Builder) : Option Builder :=
  match scheduleIn target l b.scopes with
  | some scopes => some ⟨scopes, b.events⟩
  | none => none

/-- `Builder::pop_scope`: the innermost entry must be the named scope; its
drops are emitted in reverse scheduling order. -/
noncomputable def Builder.popScope (s : Scope) (b : Builder) : Option Builder :=
  match b.scopes with
  | [] => none
  | sc :: rest =>
    match sc.region.beq s with
    | true => some ⟨rest, b.events ++ dropEvents sc.drops⟩
    | false => none

/-- `Builder::as_temp` for a temporary with a destructor: write the value and
schedule its drop in the temporary scope computed by `temporary_scope`. -/
noncomputable def Builder.asTemp (tempScope : Option Scope) (l : Local) (b : Builder) : Option Builder :=
  match tempScope with
  | some s => (b.emit (.init l)).scheduleDrop s l
  | none => none

noncomputable def Builder.asTemps (tempScope : Option Scope) : List Local → Builder → Option Builder
  | [], b => some b
  | l :: ls, b =>
    match b.asTemp tempScope l with
    | some b' => Builder.asTemps tempScope ls b'
    | none => none

/-- The else path built by `Builder::break_for_else` + `build_exit_tree`:
leave every entry nested inside `target` (innermost first), emitting each
entry's drops in reverse scheduling order; `target` itself stays on the
stack. -/
noncomputable def exitScopesInside (target : Scope) : List BuildScope → List Event → Option Builder
  | [], _ => none
  | sc :: rest, ev =>
    match sc.region.beq target with
    | true => some ⟨sc :: rest, ev⟩
    | false => exitScopesInside target rest (ev ++ dropEvents sc.drops)

noncomputable def Builder.breakForElse (target : Scope) (b : Builder) : Option Builder :=
  exitScopesInside target b.scopes b.events

/-- `ast_block_stmts` for a run of `let` statements that each bind one local
with a destructor: push the statement's remainder scope, initialize the local,
schedule its drop there, lower the rest of the block, then pop the remainder
scope (`let_scope_stack` is popped in reverse). -/
noncomputable def lowerBlockStmts (blockId : Nat) (tail : Builder → Option Builder) :
    Nat → List Local → Builder → Option Builder
  | _, [], b => tail b
  | i, l :: ls, b =>
    match ((b.pushScope ⟨blockId, .remainder i⟩).emit (.init l)).scheduleDrop
        ⟨blockId, .remainder i⟩ l with
    | none => none
    | some b1 =>
      match lowerBlockStmts blockId tail (i + 1) ls b1 with
      | none => none
      | some b2 => b2.popScope ⟨blockId, .remainder i⟩

/-! ### Stack lemmas -/

noncomputable def noneIs (target : Scope) : List BuildScope → Bool
  | [] => true
  | sc :: rest => !(sc.region.beq target) && noneIs target rest

noncomputable def allRemainder : List BuildScope → Bool
  | [] => true
  | sc :: rest => sc.region.data.isRemainder && allRemainder rest

theorem noneIs_append (target : Scope) :
    ∀ xs ys : List BuildScope,
      noneIs target xs = true → noneIs target ys = true → noneIs target (xs ++ ys) = true
  | [], _, _, hy => hy
  | x :: xs, ys, hx, hy => by
    cases hb : x.region.beq target with
    | true => simp [noneIs, hb] at hx
    | false =>
      have hxs : noneIs target xs = true := by
        simpa [noneIs, hb] using hx
      simp [noneIs, hb, noneIs_append target xs ys hxs hy]

theorem noneIs_of_allRemainder (target : Scope) (ht : target.data.isRemainder = false) :
    ∀ pre : List BuildScope, allRemainder pre = true → noneIs target pre = true
  | [], _ => rfl
  | sc :: pre, h => by
    cases hr : sc.region.data.isRemainder with
    | false => simp [allRemainder, hr] at h
    | true =>
      have hpre : allRemainder pre = true := by
        simpa [allRemainder, hr] using h
      have hne : sc.region.beq target = false := by
        unfold Scope.beq
        rw [ScopeData.beq_false_of_isRemainder _ _ hr ht]
        exact Bool.and_false _
      simp [noneIs, hne, noneIs_of_allRemainder target ht pre hpre]

theorem scheduleIn_split (target : Scope) (l : Local) (ds : List Local)
    (post : List BuildScope) :
    ∀ pre : List BuildScope, noneIs target pre = true →
      scheduleIn target l (pre ++ ⟨target, ds⟩ :: post)
        = some (pre ++ ⟨target, ds ++ [l]⟩ :: post)
  | [], _ => by
    simp [scheduleIn, Scope.beq_refl]
  | sc :: pre, h => by
    cases hb : sc.region.beq target with
    | true => simp [noneIs, hb] at h
    | false =>
      have hpre : noneIs target pre = true := by
        simpa [noneIs, hb] using h
      simp [scheduleIn, hb, scheduleIn_split target l ds post pre hpre]

theorem asTemps_split (target : Scope) (post pre : List BuildScope)
    (hpre : noneIs target pre = true) :
    ∀ (ls ds : List Local) (ev : List Event),
      Builder.asTemps (some target) ls ⟨pre ++ ⟨target, ds⟩ :: post, ev⟩
        = some ⟨pre ++ ⟨target, ds ++ ls⟩ :: post, ev ++ initEvents ls⟩
  | [], ds, ev => by
    simp [Builder.asTemps, initEvents]
  | l :: ls, ds, ev => by
    have step : Builder.asTemp (some target) l ⟨pre ++ ⟨target, ds⟩ :: post, ev⟩
        = some ⟨pre ++ ⟨target, ds ++ [l]⟩ :: post, ev ++ [Event.init l]⟩ := by
      simp [Builder.asTemp, Builder.emit, Builder.scheduleDrop,
        scheduleIn_split target l ds post pre hpre]
    simp [Builder.asTemps, step,
      asTemps_split target post pre hpre ls (ds ++ [l]) (ev ++ [Event.init l]),
      initEvents, List.append_assoc]

/-- Frame lemma for `lowerBlockStmts`: if lowering the tail only changes the
stack below the remainder scopes from `base` to `base'` and appends `te`, then
lowering `n` `let` statements around it initializes the locals in order before
the tail and drops them in reverse order after it. -/
theorem lowerBlockStmts_frame (blockId : Nat) (tail : Builder → Option Builder)
    (base base' : List BuildScope) (te : List Event)
    (htail : ∀ (pre : List BuildScope) (ev : List Event), allRemainder pre = true →
      tail ⟨pre ++ base, ev⟩ = some ⟨pre ++ base', ev ++ te⟩) :
    ∀ (ls : List Local) (i : Nat) (pre : List BuildScope) (ev : List Event),
      allRemainder pre = true →
      lowerBlockStmts blockId tail i ls ⟨pre ++ base, ev⟩
        = some ⟨pre ++ base', ev ++ initEvents ls ++ te ++ dropEvents ls⟩
  | [], _, pre, ev, hpre => by
    simp [lowerBlockStmts, htail pre ev hpre, initEvents, dropEvents]
  | l :: ls, i, pre, ev, hpre => by
    have hpre' : allRemainder (⟨⟨blockId, .remainder i⟩, [l]⟩ :: pre) = true := by
      simp [allRemainder, ScopeData.isRemainder, hpre]
    have ih := lowerBlockStmts_frame blockId tail base base' te htail ls (i + 1)
      (⟨⟨blockId, .remainder i⟩, [l]⟩ :: pre) (ev ++ [Event.init l]) hpre'
    simp only [List.cons_append] at ih
    simp [lowerBlockStmts, Builder.pushScope, Builder.emit, Builder.scheduleDrop,
      scheduleIn, Scope.beq_refl, ih, Builder.popScope, initEvents, dropEvents,
      List.append_assoc]

/-- Walking `default_temporary_scope` through remainder scopes forgets where
the walk started. -/
theorem defaultTemporaryScope_remainderChain (blockId : Nat) (rest : Chain) :
    ∀ (ls : List Nat) (i : Nat) (cx : Chain) (inner : Scope),
      (∀ inner' : Scope, defaultTemporaryScope inner' cx
        = defaultTemporaryScope ⟨blockId, .node⟩ rest) →
      defaultTemporaryScope inner (remainderChain blockId i ls cx)
        = defaultTemporaryScope ⟨blockId, .node⟩ rest
  | [], _, _, inner, h => h inner
  | _ :: ls, i, cx, inner, h =>
    defaultTemporaryScope_remainderChain blockId rest ls (i + 1)
      (⟨blockId, .remainder i⟩ :: cx) inner
      (fun _ => h ⟨blockId, .remainder i⟩)

/-! ## Part A.3: the three source shapes

Item-local ids of the HIR nodes involved. Their numeric values are irrelevant;
they only need to be pairwise distinct inside one shape. -/

/-- Region chain of the enclosing function body at the statement: the function
body block, the body expression (terminating), the argument and call-site
scopes (`visit_body`). -/
noncomputable def fnChain : Chain :=
  [⟨1, .node⟩, ⟨0, .node⟩, ⟨0, .destruction⟩, ⟨0, .arguments⟩, ⟨0, .callSite⟩]

/-- The statement that contains the construct. -/
abbrev stmtId : Nat := 2
/-- Block expression `{ let ..; tail }` (expression node and block node). -/
abbrev blockExprId : Nat := 3
abbrev blockId : Nat := 4
/-- The block's tail expression and the sub-expression that creates temporaries. -/
abbrev tailId : Nat := 5
abbrev tempExprId : Nat := 6
/-- `if let` expression, its `then` block, its `let` condition and scrutinee. -/
abbrev ifId : Nat := 7
abbrev thenId : Nat := 8
abbrev letCondId : Nat := 9
abbrev scrutId : Nat := 10
/-- `match` expression and one arm. -/
abbrev matchId : Nat := 11
abbrev armId : Nat := 12

/-- Temporary scope of a temporary created inside the tail expression of
`let x = { let l₁ = ..; ..; let lₙ = ..; tail };`. -/
noncomputable def blockTailTempScope (ed : Edition) (locals : List Local) : Option Scope :=
  temporaryScope tempExprId
    (resolveBlockTail ed tailId
      (remainderChain blockId 0 locals
        (resolveExpr blockId (resolveExpr blockExprId (resolveStmt stmtId fnChain)))))

/-- Lowering of the tail expression: `in_scope(Node(tail))` around the
temporaries it creates. -/
noncomputable def lowerTail (tempScope : Option Scope) (temps : List Local) (b : Builder) : Option Builder :=
  match Builder.asTemps tempScope temps (b.pushScope ⟨tailId, .node⟩) with
  | some b1 => b1.popScope ⟨tailId, .node⟩
  | none => none

/-- `let x = { let l₁ = ..; ..; let lₙ = ..; tail };` where each `lᵢ` holds a
value with a destructor and evaluating `tail` creates the temporaries `temps`
(in creation order), each with a destructor. Returns the event trace of the
normal path up to and including the end of the enclosing statement. -/
noncomputable def compileBlockTail (ed : Edition) (locals temps : List Local) : Option (List Event) :=
  match lowerBlockStmts blockId (lowerTail (blockTailTempScope ed locals) temps) 0 locals
      ⟨[⟨⟨blockId, .node⟩, []⟩, ⟨⟨blockExprId, .node⟩, []⟩, ⟨⟨stmtId, .node⟩, []⟩], []⟩ with
  | none => none
  | some b1 =>
    match b1.popScope ⟨blockId, .node⟩ with
    | none => none
    | some b2 =>
      match b2.popScope ⟨blockExprId, .node⟩ with
      | none => none
      | some b3 =>
        match b3.popScope ⟨stmtId, .node⟩ with
        | none => none
        | some b4 => some b4.events

/-- Temporary scope of a temporary created by the scrutinee of
`if let PAT = scrutinee { .. } else { .. }` used as an expression statement. -/
noncomputable def ifLetTempScope (ed : Edition) : Option Scope :=
  temporaryScope tempExprId
    (resolveExpr scrutId
      (resolveExpr letCondId
        (ifThenScope ed thenId :: resolveExpr ifId (resolveStmt stmtId fnChain))))

/-- `if let PAT = scrutinee { then } else { else }` as an expression
statement. Evaluating the scrutinee creates the temporaries `scrutTemps`;
`matched` says whether the pattern matches; the block bodies are not modeled and
are recorded as `Event.body thenTag` / `Event.body elseTag`. -/
noncomputable def compileIfLetElse (ed : Edition) (scrutTemps : List Local) (matched : Bool)
    (thenTag elseTag : Nat) : Option (List Event) :=
  -- `in_scope(Node(stmt))`, `in_scope(Node(if))`, `in_scope(if_then_scope)`,
  -- then the `let` condition and its scrutinee.
  match Builder.asTemps (ifLetTempScope ed) scrutTemps
      ⟨[⟨⟨scrutId, .node⟩, []⟩, ⟨⟨letCondId, .node⟩, []⟩, ⟨ifThenScope ed thenId, []⟩,
        ⟨⟨ifId, .node⟩, []⟩, ⟨⟨stmtId, .node⟩, []⟩], []⟩ with
  | none => none
  | some b1 =>
    match b1.popScope ⟨scrutId, .node⟩ with
    | none => none
    | some b2 =>
      match matched with
      | true =>
        match b2.popScope ⟨letCondId, .node⟩ with
        | none => none
        | some b3 =>
          match (b3.emit (.body thenTag)).popScope (ifThenScope ed thenId) with
          | none => none
          | some b4 =>
            match b4.popScope ⟨ifId, .node⟩ with
            | none => none
            | some b5 =>
              match b5.popScope ⟨stmtId, .node⟩ with
              | none => none
              | some b6 => some b6.events
      | false =>
        -- `break_for_else` targets the condition scope, which is the scope
        -- that was innermost when the `if` was reached: `Node(if)`.
        match b2.breakForElse ⟨ifId, .node⟩ with
        | none => none
        | some b3 =>
          match (b3.emit (.body elseTag)).popScope ⟨ifId, .node⟩ with
          | none => none
          | some b4 =>
            match b4.popScope ⟨stmtId, .node⟩ with
            | none => none
            | some b5 => some b5.events

/-- Temporary scope of a temporary created by a `match` scrutinee. When
`scrutIsBlock` is true the scrutinee is `{ e }` (or `unsafe { e }`) and the
temporary is created inside the block's tail expression `e`. -/
noncomputable def matchTempScope (ed : Edition) (scrutIsBlock : Bool) : Option Scope :=
  match scrutIsBlock with
  | false =>
    temporaryScope tempExprId
      (resolveExpr scrutId (resolveExpr matchId (resolveStmt stmtId fnChain)))
  | true =>
    temporaryScope tempExprId
      (resolveBlockTail ed tailId
        (resolveExpr blockId
          (resolveExpr blockExprId (resolveExpr matchId (resolveStmt stmtId fnChain)))))

/-- `match scrutinee { .. => arm }` as an expression statement. Evaluating the
scrutinee creates the temporaries `scrutTemps`; the selected arm's body is
recorded as `Event.body armTag`. -/
noncomputable def compileMatch (ed : Edition) (scrutIsBlock : Bool) (scrutTemps : List Local)
    (armTag : Nat) : Option (List Event) :=
  let afterScrutinee : Option Builder :=
    match scrutIsBlock with
    | false =>
      match Builder.asTemps (matchTempScope ed false) scrutTemps
          ⟨[⟨⟨scrutId, .node⟩, []⟩, ⟨⟨matchId, .node⟩, []⟩, ⟨⟨stmtId, .node⟩, []⟩], []⟩ with
      | none => none
      | some b1 => b1.popScope ⟨scrutId, .node⟩
    | true =>
      match lowerTail (matchTempScope ed true) scrutTemps
          ⟨[⟨⟨blockId, .node⟩, []⟩, ⟨⟨blockExprId, .node⟩, []⟩, ⟨⟨matchId, .node⟩, []⟩,
            ⟨⟨stmtId, .node⟩, []⟩], []⟩ with
      | none => none
      | some b1 =>
        match b1.popScope ⟨blockId, .node⟩ with
        | none => none
        | some b2 => b2.popScope ⟨blockExprId, .node⟩
  match afterScrutinee with
  | none => none
  | some b2 =>
    match ((b2.pushScope ⟨armId, .node⟩).emit (.body armTag)).popScope ⟨armId, .node⟩ with
    | none => none
    | some b3 =>
      match b3.popScope ⟨matchId, .node⟩ with
      | none => none
      | some b4 =>
        match b4.popScope ⟨stmtId, .node⟩ with
        | none => none
        | some b5 => some b5.events

/-! ### Temporary scopes chosen in each edition -/

theorem blockTailTempScope_ed2021 (locals : List Local) :
    blockTailTempScope .ed2021 locals = some ⟨stmtId, .node⟩ := by
  unfold blockTailTempScope temporaryScope resolveBlockTail enterNodeScopeWithDtor
  show defaultTemporaryScope ⟨tailId, .node⟩ (remainderChain blockId 0 locals _) = _
  rw [defaultTemporaryScope_remainderChain blockId
    (resolveExpr blockExprId (resolveStmt stmtId fnChain)) locals 0 _ _ (fun _ => rfl)]
  rfl

theorem blockTailTempScope_ed2024 (locals : List Local) :
    blockTailTempScope .ed2024 locals = some ⟨tailId, .node⟩ := rfl

theorem ifLetTempScope_ed2021 : ifLetTempScope .ed2021 = some ⟨stmtId, .node⟩ := rfl

theorem ifLetTempScope_ed2024 : ifLetTempScope .ed2024 = some ⟨thenId, .ifThenRescope⟩ := rfl

theorem matchTempScope_plain (ed : Edition) :
    matchTempScope ed false = some ⟨stmtId, .node⟩ := rfl

theorem matchTempScope_block_ed2021 : matchTempScope .ed2021 true = some ⟨stmtId, .node⟩ := rfl

theorem matchTempScope_block_ed2024 : matchTempScope .ed2024 true = some ⟨tailId, .node⟩ := rfl

/-! ### Exact event traces -/

/-- Edition 2021: block locals are dropped (in reverse declaration order)
before the tail-expression temporaries (in reverse creation order). -/
theorem compileBlockTail_ed2021 (locals temps : List Local) :
    compileBlockTail .ed2021 locals temps
      = some (initEvents locals ++ initEvents temps ++ dropEvents locals ++ dropEvents temps) := by
  have htail : ∀ (pre : List BuildScope) (ev : List Event), allRemainder pre = true →
      lowerTail (some ⟨stmtId, .node⟩) temps
        ⟨pre ++ [⟨⟨blockId, .node⟩, []⟩, ⟨⟨blockExprId, .node⟩, []⟩, ⟨⟨stmtId, .node⟩, []⟩], ev⟩
      = some ⟨pre ++ [⟨⟨blockId, .node⟩, []⟩, ⟨⟨blockExprId, .node⟩, []⟩,
          ⟨⟨stmtId, .node⟩, temps⟩], ev ++ initEvents temps⟩ := by
    intro pre ev hpre
    have hinner : noneIs ⟨stmtId, .node⟩
        (pre ++ [⟨⟨blockId, .node⟩, []⟩, ⟨⟨blockExprId, .node⟩, []⟩]) = true :=
      noneIs_append ⟨stmtId, .node⟩ pre _ (noneIs_of_allRemainder _ rfl pre hpre) rfl
    have hnone : noneIs ⟨stmtId, .node⟩
        (⟨⟨tailId, .node⟩, []⟩ :: (pre ++ [⟨⟨blockId, .node⟩, []⟩, ⟨⟨blockExprId, .node⟩, []⟩]))
        = true := hinner
    have h := asTemps_split ⟨stmtId, .node⟩ []
      (⟨⟨tailId, .node⟩, []⟩ :: (pre ++ [⟨⟨blockId, .node⟩, []⟩, ⟨⟨blockExprId, .node⟩, []⟩]))
      hnone temps [] ev
    simp only [List.cons_append, List.append_assoc, List.nil_append] at h
    simp [lowerTail, Builder.pushScope, h, Builder.popScope, Scope.beq_refl, dropEvents]
  have hframe := lowerBlockStmts_frame blockId (lowerTail (some ⟨stmtId, .node⟩) temps)
    _ _ (initEvents temps) htail locals 0 [] [] rfl
  simp only [List.nil_append] at hframe
  unfold compileBlockTail
  rw [blockTailTempScope_ed2021, hframe]
  simp [Builder.popScope, Scope.beq, ScopeData.beq, dropEvents, List.append_assoc]

/-- Edition 2024: the tail-expression temporaries are dropped (in reverse
creation order) before the block locals (in reverse declaration order). -/
theorem compileBlockTail_ed2024 (locals temps : List Local) :
    compileBlockTail .ed2024 locals temps
      = some (initEvents locals ++ initEvents temps ++ dropEvents temps ++ dropEvents locals) := by
  have htail : ∀ (pre : List BuildScope) (ev : List Event), allRemainder pre = true →
      lowerTail (some ⟨tailId, .node⟩) temps
        ⟨pre ++ [⟨⟨blockId, .node⟩, []⟩, ⟨⟨blockExprId, .node⟩, []⟩, ⟨⟨stmtId, .node⟩, []⟩], ev⟩
      = some ⟨pre ++ [⟨⟨blockId, .node⟩, []⟩, ⟨⟨blockExprId, .node⟩, []⟩,
          ⟨⟨stmtId, .node⟩, []⟩], ev ++ (initEvents temps ++ dropEvents temps)⟩ := by
    intro pre ev _
    have h := asTemps_split ⟨tailId, .node⟩
      (pre ++ [⟨⟨blockId, .node⟩, []⟩, ⟨⟨blockExprId, .node⟩, []⟩, ⟨⟨stmtId, .node⟩, []⟩])
      [] rfl temps [] ev
    simp only [List.nil_append] at h
    simp [lowerTail, Builder.pushScope, h, Builder.popScope, Scope.beq_refl, List.append_assoc]
  have hframe := lowerBlockStmts_frame blockId (lowerTail (some ⟨tailId, .node⟩) temps)
    _ _ (initEvents temps ++ dropEvents temps) htail locals 0 [] [] rfl
  simp only [List.nil_append] at hframe
  unfold compileBlockTail
  rw [blockTailTempScope_ed2024, hframe]
  simp [Builder.popScope, Scope.beq, ScopeData.beq, dropEvents, List.append_assoc]

/-- Edition 2021, pattern fails: the `else` body runs before the scrutinee
temporaries are dropped. -/
theorem compileIfLetElse_else_ed2021 (scrutTemps : List Local) (thenTag elseTag : Nat) :
    compileIfLetElse .ed2021 scrutTemps false thenTag elseTag
      = some (initEvents scrutTemps ++ [Event.body elseTag] ++ dropEvents scrutTemps) := by
  have h := asTemps_split ⟨stmtId, .node⟩ []
    [⟨⟨scrutId, .node⟩, []⟩, ⟨⟨letCondId, .node⟩, []⟩, ⟨ifThenScope .ed2021 thenId, []⟩,
      ⟨⟨ifId, .node⟩, []⟩] rfl scrutTemps [] []
  simp only [List.cons_append, List.nil_append] at h
  unfold compileIfLetElse
  rw [ifLetTempScope_ed2021, h]
  simp [Builder.popScope, Builder.breakForElse, exitScopesInside, Builder.emit, Scope.beq,
    ScopeData.beq, ifThenScope, Edition.atLeastRust2024, dropEvents]

/-- Edition 2024, pattern fails: the scrutinee temporaries are dropped before
the `else` body runs. -/
theorem compileIfLetElse_else_ed2024 (scrutTemps : List Local) (thenTag elseTag : Nat) :
    compileIfLetElse .ed2024 scrutTemps false thenTag elseTag
      = some (initEvents scrutTemps ++ dropEvents scrutTemps ++ [Event.body elseTag]) := by
  have h := asTemps_split ⟨thenId, .ifThenRescope⟩
    [⟨⟨ifId, .node⟩, []⟩, ⟨⟨stmtId, .node⟩, []⟩]
    [⟨⟨scrutId, .node⟩, []⟩, ⟨⟨letCondId, .node⟩, []⟩] rfl scrutTemps [] []
  simp only [List.cons_append, List.nil_append] at h
  unfold compileIfLetElse
  rw [ifLetTempScope_ed2024]
  show (match Builder.asTemps (some ⟨thenId, .ifThenRescope⟩) scrutTemps
      ⟨[⟨⟨scrutId, .node⟩, []⟩, ⟨⟨letCondId, .node⟩, []⟩, ⟨⟨thenId, .ifThenRescope⟩, []⟩,
        ⟨⟨ifId, .node⟩, []⟩, ⟨⟨stmtId, .node⟩, []⟩], []⟩ with
    | none => none
    | some b1 => _) = _
  rw [h]
  simp [Builder.popScope, Builder.breakForElse, exitScopesInside, Builder.emit, Scope.beq,
    ScopeData.beq, dropEvents]

/-- Pattern matches: in both editions the `then` body runs before the
scrutinee temporaries are dropped. -/
theorem compileIfLetElse_then (ed : Edition) (scrutTemps : List Local) (thenTag elseTag : Nat) :
    compileIfLetElse ed scrutTemps true thenTag elseTag
      = some (initEvents scrutTemps ++ [Event.body thenTag] ++ dropEvents scrutTemps) := by
  cases ed with
  | ed2021 =>
    have h := asTemps_split ⟨stmtId, .node⟩ []
      [⟨⟨scrutId, .node⟩, []⟩, ⟨⟨letCondId, .node⟩, []⟩, ⟨ifThenScope .ed2021 thenId, []⟩,
        ⟨⟨ifId, .node⟩, []⟩] rfl scrutTemps [] []
    simp only [List.cons_append, List.nil_append] at h
    unfold compileIfLetElse
    rw [ifLetTempScope_ed2021, h]
    simp [Builder.popScope, Builder.emit, Scope.beq, ScopeData.beq, ifThenScope,
      Edition.atLeastRust2024, dropEvents]
  | ed2024 =>
    have h := asTemps_split ⟨thenId, .ifThenRescope⟩
      [⟨⟨ifId, .node⟩, []⟩, ⟨⟨stmtId, .node⟩, []⟩]
      [⟨⟨scrutId, .node⟩, []⟩, ⟨⟨letCondId, .node⟩, []⟩] rfl scrutTemps [] []
    simp only [List.cons_append, List.nil_append] at h
    unfold compileIfLetElse
    rw [ifLetTempScope_ed2024]
    show (match Builder.asTemps (some ⟨thenId, .ifThenRescope⟩) scrutTemps
        ⟨[⟨⟨scrutId, .node⟩, []⟩, ⟨⟨letCondId, .node⟩, []⟩, ⟨⟨thenId, .ifThenRescope⟩, []⟩,
          ⟨⟨ifId, .node⟩, []⟩, ⟨⟨stmtId, .node⟩, []⟩], []⟩ with
      | none => none
      | some b1 => _) = _
    rw [h]
    simp [Builder.popScope, Builder.emit, Scope.beq, ScopeData.beq, ifThenScope,
      Edition.atLeastRust2024, dropEvents]

/-- A `match` whose scrutinee is not a block: in both editions the arm body
runs before the scrutinee temporaries are dropped. -/
theorem compileMatch_plain (ed : Edition) (scrutTemps : List Local) (armTag : Nat) :
    compileMatch ed false scrutTemps armTag
      = some (initEvents scrutTemps ++ [Event.body armTag] ++ dropEvents scrutTemps) := by
  have h := asTemps_split ⟨stmtId, .node⟩ []
    [⟨⟨scrutId, .node⟩, []⟩, ⟨⟨matchId, .node⟩, []⟩] rfl scrutTemps [] []
  simp only [List.cons_append, List.nil_append] at h
  unfold compileMatch
  simp [matchTempScope_plain, h, Builder.popScope, Builder.pushScope, Builder.emit, Scope.beq,
    ScopeData.beq, dropEvents]

/-- A `match` whose scrutinee is a block, Edition 2021: same order as the
plain `match`. -/
theorem compileMatch_block_ed2021 (scrutTemps : List Local) (armTag : Nat) :
    compileMatch .ed2021 true scrutTemps armTag
      = some (initEvents scrutTemps ++ [Event.body armTag] ++ dropEvents scrutTemps) := by
  have h := asTemps_split ⟨stmtId, .node⟩ []
    [⟨⟨tailId, .node⟩, []⟩, ⟨⟨blockId, .node⟩, []⟩, ⟨⟨blockExprId, .node⟩, []⟩,
      ⟨⟨matchId, .node⟩, []⟩] rfl scrutTemps [] []
  simp only [List.cons_append, List.nil_append] at h
  unfold compileMatch
  simp [matchTempScope_block_ed2021, lowerTail, h, Builder.popScope, Builder.pushScope,
    Builder.emit, Scope.beq, ScopeData.beq, dropEvents]

/-- A `match` whose scrutinee is a block, Edition 2024: the temporaries created
inside the block are dropped before any arm runs. -/
theorem compileMatch_block_ed2024 (scrutTemps : List Local) (armTag : Nat) :
    compileMatch .ed2024 true scrutTemps armTag
      = some (initEvents scrutTemps ++ dropEvents scrutTemps ++ [Event.body armTag]) := by
  have h := asTemps_split ⟨tailId, .node⟩
    [⟨⟨blockId, .node⟩, []⟩, ⟨⟨blockExprId, .node⟩, []⟩, ⟨⟨matchId, .node⟩, []⟩,
      ⟨⟨stmtId, .node⟩, []⟩] [] rfl scrutTemps [] []
  simp only [List.nil_append] at h
  unfold compileMatch
  simp [matchTempScope_block_ed2024, lowerTail, h, Builder.popScope, Builder.pushScope,
    Builder.emit, Scope.beq, ScopeData.beq, dropEvents]

/-! ### Observable order -/

/-- What a destructor log observes: drops and body executions, in order. -/
inductive Obs where
  | dropped (l : Local)
  | ran (tag : Nat)

noncomputable def observe : List Event → List Obs
  | [] => []
  | .init _ :: rest => observe rest
  | .drop l :: rest => .dropped l :: observe rest
  | .body t :: rest => .ran t :: observe rest

/-- The locals dropped on the normal path, in order. -/
noncomputable def dropTrace : List Event → List Local
  | [] => []
  | .drop l :: rest => l :: dropTrace rest
  | _ :: rest => dropTrace rest

theorem dropTrace_append : ∀ xs ys : List Event, dropTrace (xs ++ ys) = dropTrace xs ++ dropTrace ys
  | [], _ => rfl
  | .init _ :: xs, ys => dropTrace_append xs ys
  | .drop l :: xs, ys => congrArg (l :: ·) (dropTrace_append xs ys)
  | .body _ :: xs, ys => dropTrace_append xs ys

theorem dropTrace_initEvents : ∀ ls : List Local, dropTrace (initEvents ls) = []
  | [] => rfl
  | _ :: ls => dropTrace_initEvents ls

theorem dropTrace_map_drop : ∀ ls : List Local, dropTrace (ls.map Event.drop) = ls
  | [] => rfl
  | l :: ls => congrArg (l :: ·) (dropTrace_map_drop ls)

theorem dropTrace_dropEvents (ls : List Local) : dropTrace (dropEvents ls) = ls.reverse :=
  dropTrace_map_drop ls.reverse

/-- General drop traces of the block-tail shape for any number of locals and
tail temporaries. -/
theorem blockTail_dropTrace_ed2021 (locals temps : List Local) :
    (compileBlockTail .ed2021 locals temps).map dropTrace
      = some (locals.reverse ++ temps.reverse) := by
  rw [compileBlockTail_ed2021]
  simp [dropTrace_append, dropTrace_initEvents, dropTrace_dropEvents]

theorem blockTail_dropTrace_ed2024 (locals temps : List Local) :
    (compileBlockTail .ed2024 locals temps).map dropTrace
      = some (temps.reverse ++ locals.reverse) := by
  rw [compileBlockTail_ed2024]
  simp [dropTrace_append, dropTrace_initEvents, dropTrace_dropEvents]

/-- The edition is unobservable in the block-tail shape when the block has no
local with a destructor or the tail creates no temporary with a destructor. -/
theorem blockTail_edition_invisible_of_nil (locals temps : List Local)
    (h : locals = [] ∨ temps = []) :
    (compileBlockTail .ed2021 locals temps).map dropTrace
      = (compileBlockTail .ed2024 locals temps).map dropTrace := by
  rw [blockTail_dropTrace_ed2021, blockTail_dropTrace_ed2024]
  cases h with
  | inl h => subst h; simp
  | inr h => subst h; simp

/-- The edition is observable as soon as the block has a local with a
destructor and the tail creates a temporary with a destructor (distinct MIR
locals). -/
theorem blockTail_edition_visible_of_cons (l t : Local) (ls ts : List Local)
    (hdisj : ∀ x, x ∈ l :: ls → x ∈ t :: ts → False) :
    (compileBlockTail .ed2021 (l :: ls) (t :: ts)).map dropTrace
      ≠ (compileBlockTail .ed2024 (l :: ls) (t :: ts)).map dropTrace := by
  rw [blockTail_dropTrace_ed2021, blockTail_dropTrace_ed2024]
  intro h
  have h' := congrArg List.reverse (Option.some.inj h)
  simp only [List.reverse_append, List.reverse_reverse, List.cons_append] at h'
  have hhead : t = l := (List.cons.inj h').1
  exact hdisj l (List.Mem.head ls) (hhead ▸ List.Mem.head ts)

/-! ### Theorem 1: exact reversal between the editions, and `match` invariance -/

/-- **Exact drop-trace reversal and `match` edition invariance.**

For one block local `l` and one tail temporary `t`, Edition 2021 drops
`[l, t]` and Edition 2024 drops `[t, l]`. For one scrutinee temporary `g` of an
`if let` whose pattern fails, Edition 2021 observes `[else body, drop g]` and
Edition 2024 observes `[drop g, else body]`. Each Edition 2024 sequence is the
reverse of the Edition 2021 sequence. A `match` whose scrutinee is not a block
lowers to the same event trace in both editions, for any scrutinee temporaries. -/
theorem dropTrace_reversal_and_match_invariance (l t g thenTag elseTag armTag : Nat)
    (scrutTemps : List Local) :
    (compileBlockTail .ed2021 [l] [t]).map dropTrace = some [l, t]
    ∧ (compileBlockTail .ed2024 [l] [t]).map dropTrace = some [t, l]
    ∧ (compileBlockTail .ed2024 [l] [t]).map dropTrace
        = ((compileBlockTail .ed2021 [l] [t]).map dropTrace).map List.reverse
    ∧ (compileIfLetElse .ed2021 [g] false thenTag elseTag).map observe
        = some [Obs.ran elseTag, Obs.dropped g]
    ∧ (compileIfLetElse .ed2024 [g] false thenTag elseTag).map observe
        = some [Obs.dropped g, Obs.ran elseTag]
    ∧ (compileIfLetElse .ed2024 [g] false thenTag elseTag).map observe
        = ((compileIfLetElse .ed2021 [g] false thenTag elseTag).map observe).map List.reverse
    ∧ compileMatch .ed2021 false scrutTemps armTag = compileMatch .ed2024 false scrutTemps armTag := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [compileBlockTail_ed2021]; rfl
  · rw [compileBlockTail_ed2024]; rfl
  · rw [compileBlockTail_ed2021, compileBlockTail_ed2024]; rfl
  · rw [compileIfLetElse_else_ed2021]; rfl
  · rw [compileIfLetElse_else_ed2024]; rfl
  · rw [compileIfLetElse_else_ed2021, compileIfLetElse_else_ed2024]; rfl
  · rw [compileMatch_plain, compileMatch_plain]

/-- Boundary of the `match` invariance: wrapping the scrutinee in a block makes
the edition observable again. -/
theorem match_block_scrutinee_is_edition_sensitive (g armTag : Nat) :
    (compileMatch .ed2021 true [g] armTag).map observe = some [Obs.ran armTag, Obs.dropped g]
    ∧ (compileMatch .ed2024 true [g] armTag).map observe = some [Obs.dropped g, Obs.ran armTag] := by
  refine ⟨?_, ?_⟩
  · rw [compileMatch_block_ed2021]; rfl
  · rw [compileMatch_block_ed2024]; rfl

/-- The `then` path of `if let` is edition-invariant. -/
theorem ifLet_then_path_invariant (scrutTemps : List Local) (thenTag elseTag : Nat) :
    compileIfLetElse .ed2021 scrutTemps true thenTag elseTag
      = compileIfLetElse .ed2024 scrutTemps true thenTag elseTag := by
  rw [compileIfLetElse_then, compileIfLetElse_then]

/-! ### Instances matching the executed probe program

The probe program gives the block local id 1, tail temporary id 2, scrutinee
temporary id 1, and logs 8 / 9 for `then` / `else` (or first / second arm). -/

noncomputable def Obs.digit : Obs → Nat
  | .dropped l => l
  | .ran t => t

theorem probe_tail_ed2021 :
    (compileBlockTail .ed2021 [1] [2]).map dropTrace = some [1, 2] := by
  rw [compileBlockTail_ed2021]; rfl

theorem probe_tail_ed2024 :
    (compileBlockTail .ed2024 [1] [2]).map dropTrace = some [2, 1] := by
  rw [compileBlockTail_ed2024]; rfl

theorem probe_if_let_else_ed2021 :
    (compileIfLetElse .ed2021 [1] false 8 9).map (fun tr => (observe tr).map Obs.digit)
      = some [9, 1] := by
  rw [compileIfLetElse_else_ed2021]; rfl

theorem probe_if_let_else_ed2024 :
    (compileIfLetElse .ed2024 [1] false 8 9).map (fun tr => (observe tr).map Obs.digit)
      = some [1, 9] := by
  rw [compileIfLetElse_else_ed2024]; rfl

theorem probe_if_let_then (ed : Edition) :
    (compileIfLetElse ed [1] true 8 9).map (fun tr => (observe tr).map Obs.digit)
      = some [8, 1] := by
  rw [compileIfLetElse_then]; rfl

theorem probe_match (ed : Edition) :
    (compileMatch ed false [1] 9).map (fun tr => (observe tr).map Obs.digit) = some [9, 1] := by
  rw [compileMatch_plain]; rfl

theorem probe_match_block_scrutinee_ed2021 :
    (compileMatch .ed2021 true [1] 9).map (fun tr => (observe tr).map Obs.digit)
      = some [9, 1] := by
  rw [compileMatch_block_ed2021]; rfl

theorem probe_match_block_scrutinee_ed2024 :
    (compileMatch .ed2024 true [1] 9).map (fun tr => (observe tr).map Obs.digit)
      = some [1, 9] := by
  rw [compileMatch_block_ed2024]; rfl

/-! ### Counterexample 1: a tail temporary that borrows a block local -/

/-- `true` iff the trace drops `holder` after `referent` has been dropped.
Read `holder` as a temporary whose destructor reads through a borrow of
`referent` (for example `std::cell::Ref` borrowing a `RefCell` local). -/
noncomputable def dropsHolderAfterReferent (holder referent : Local) : Bool → List Event → Bool
  | _, [] => false
  | referentDead, .drop l :: rest =>
    match Nat.beq l holder && referentDead with
    | true => true
    | false => dropsHolderAfterReferent holder referent (referentDead || Nat.beq l referent) rest
  | referentDead, .init _ :: rest => dropsHolderAfterReferent holder referent referentDead rest
  | referentDead, .body _ :: rest => dropsHolderAfterReferent holder referent referentDead rest

theorem natBeq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

/-- **Counterexample 1.** With a block local `l` and a tail temporary `t` whose
destructor reads `l`, the Edition 2021 drop order destroys `l` first and then
runs `t`'s destructor (a use of a dead local, which is why the borrow checker
rejects such programs in Edition 2021), while the Edition 2024 order runs
`t`'s destructor while `l` is still alive. -/
theorem ce1_ed2021_tail_temp_borrow_of_local_dangling_vs_ed2024_safe (l t : Local) (h : l ≠ t) :
    (compileBlockTail .ed2021 [l] [t]).map (dropsHolderAfterReferent t l false) = some true
    ∧ (compileBlockTail .ed2024 [l] [t]).map (dropsHolderAfterReferent t l false) = some false := by
  have hlt : Nat.beq l t = false := natBeq_false_of_ne h
  have htl : Nat.beq t l = false := natBeq_false_of_ne (fun e => h e.symm)
  refine ⟨?_, ?_⟩
  · rw [compileBlockTail_ed2021]
    simp [initEvents, dropEvents, dropsHolderAfterReferent, hlt, Nat.beq_refl]
  · rw [compileBlockTail_ed2024]
    simp [initEvents, dropEvents, dropsHolderAfterReferent, hlt, htl, Nat.beq_refl]

/-! ### Counterexample 2: a lock guard in an `if let` scrutinee -/

inductive LockOutcome where
  | completed
  | deadlock

/-- Runs a trace against one non-reentrant mutex. Initializing `guard`
acquires the mutex, dropping `guard` releases it, and the body tagged
`relockTag` tries to acquire the same mutex. -/
noncomputable def lockRun (guard : Local) (relockTag : Nat) : Bool → List Event → LockOutcome
  | _, [] => .completed
  | held, .init l :: rest =>
    match Nat.beq l guard with
    | true =>
      match held with
      | true => .deadlock
      | false => lockRun guard relockTag true rest
    | false => lockRun guard relockTag held rest
  | held, .drop l :: rest => lockRun guard relockTag (held && !(Nat.beq l guard)) rest
  | held, .body t :: rest =>
    match Nat.beq t relockTag && held with
    | true => .deadlock
    | false => lockRun guard relockTag held rest

/-- **Counterexample 2.** `if let PAT = *mutex.lock() { .. } else { mutex.lock() .. }`
with a failing pattern: in Edition 2021 the guard temporary `g` is still alive
when the `else` body locks again (deadlock); in Edition 2024 the guard has
been dropped before the `else` body runs. -/
theorem ce2_ed2021_if_let_mutex_guard_deadlocks_in_else_vs_ed2024_released
    (g thenTag elseTag : Nat) :
    (compileIfLetElse .ed2021 [g] false thenTag elseTag).map (lockRun g elseTag false)
      = some LockOutcome.deadlock
    ∧ (compileIfLetElse .ed2024 [g] false thenTag elseTag).map (lockRun g elseTag false)
      = some LockOutcome.completed := by
  refine ⟨?_, ?_⟩
  · rw [compileIfLetElse_else_ed2021]
    simp [initEvents, dropEvents, lockRun, Nat.beq_refl]
  · rw [compileIfLetElse_else_ed2024]
    simp [initEvents, dropEvents, lockRun, Nat.beq_refl]

/-- The same re-locking arm body under `match` deadlocks in both editions:
rewriting `if let` as `match` preserves the Edition 2021 behavior. -/
theorem match_arm_relock_deadlocks_in_both_editions (ed : Edition) (g armTag : Nat) :
    (compileMatch ed false [g] armTag).map (lockRun g armTag false)
      = some LockOutcome.deadlock := by
  rw [compileMatch_plain]
  simp [initEvents, dropEvents, lockRun, Nat.beq_refl]

/-! ## Part B: discriminant reads and `UnreachableEnumBranching` -/

/-- One enum variant: its discriminant value and whether the variant is
inhabited (its layout is not uninhabited). -/
structure Variant where
  discr : Nat
  inhabited : Bool

/-- An enum declaration: its variants in declaration order. The enum is
direct-tagged with the tag storing the discriminant, as for `#[repr(u8)]`. -/
abbrev EnumDecl := List Variant

/-- `adt.discriminants(tcx).find(|(_, var)| var.val == discr_bits)`. -/
noncomputable def findVariant (d : Nat) : EnumDecl → Option Variant
  | [] => none
  | v :: vs =>
    match Nat.beq v.discr d with
    | true => some v
    | false => findVariant d vs

/-- A semantics for `Rvalue::Discriminant` on a place whose tag field holds
`tag`: `none` is undefined behavior, `some d` is the discriminant value. -/
abbrev DiscrSem := EnumDecl → Nat → Option Nat

/-- The interpreter's semantics (`InterpCx::read_discriminant` followed by
`discriminant_for_variant`): a tag that matches no declared variant is
undefined behavior (`InvalidTag`), and so is a tag that selects an uninhabited
variant (`UninhabitedEnumVariantRead`). -/
noncomputable def evalDiscriminantStrict : DiscrSem := fun e tag =>
  match findVariant tag e with
  | none => none
  | some v =>
    match v.inhabited with
    | true => some v.discr
    | false => none

/-- An intermediate semantics: undeclared tags are undefined behavior, but the
inhabitedness of the selected variant is not checked. -/
noncomputable def evalDiscriminantDeclaredTag : DiscrSem := fun e tag =>
  match findVariant tag e with
  | none => none
  | some v => some v.discr

/-- A raw-tag semantics: the discriminant is whatever the tag field holds; no
validity check at all. -/
noncomputable def evalDiscriminantRawTag : DiscrSem := fun _ tag => some tag

/-- `SwitchTargets`: `(value, target block)` pairs plus the `otherwise`
target. -/
structure SwitchTargets where
  cases : List (Nat × Nat)
  otherwise : Nat

/-- `SwitchTargets::target_for_value`: first matching value, else the
fallback. -/
noncomputable def targetForValue (d : Nat) : List (Nat × Nat) → Nat → Nat
  | [], other => other
  | (v, t) :: rest, other =>
    match Nat.beq v d with
    | true => t
    | false => targetForValue d rest other

/-- Observable result of continuing at a block. -/
inductive Outcome where
  | ub
  | ret (value : Nat)

/-- Behavior of each successor block, abstracting its body. -/
abbrev BlockEnv := Nat → Outcome

/-- `_d = discriminant(place); switchInt(move _d) -> targets` under a given
discriminant semantics, for a place whose tag field holds `tag`. -/
noncomputable def runSwitch (sem : DiscrSem) (e : EnumDecl) (env : BlockEnv) (sw : SwitchTargets)
    (tag : Nat) : Outcome :=
  match sem e tag with
  | none => .ub
  | some d => env (targetForValue d sw.cases sw.otherwise)

/-- `variant_discriminants` for `Variants::Multiple`: the discriminants of the
inhabited variants. The compiler keeps them in a hash set; the list has no
duplicates whenever the declared discriminants are pairwise distinct, which
Rust requires. -/
noncomputable def allowedVariants : EnumDecl → List Nat
  | [] => []
  | v :: vs =>
    match v.inhabited with
    | true => v.discr :: allowedVariants vs
    | false => allowedVariants vs

noncomputable def memb (d : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => Nat.beq x d || memb d xs

/-- `FxHashSet::remove` on the list representation. -/
noncomputable def eraseFirst (d : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
    match Nat.beq x d with
    | true => xs
    | false => x :: eraseFirst d xs

/-- The loop over the explicit switch cases: a case whose value can be removed
from the allowed set is kept; every other case is redirected to the
unreachable block `ub`. Returns the rewritten cases and the allowed values
that no case claimed. -/
noncomputable def pruneCases (ub : Nat) : List (Nat × Nat) → List Nat → List (Nat × Nat) × List Nat
  | [], allowed => ([], allowed)
  | (v, t) :: rest, allowed =>
    match memb v allowed with
    | true =>
      let r := pruneCases ub rest (eraseFirst v allowed)
      ((v, t) :: r.1, r.2)
    | false =>
      let r := pruneCases ub rest allowed
      ((v, ub) :: r.1, r.2)

/-- `UnreachableEnumBranching::run_pass` on one `SwitchInt` whose operand was
just assigned from `Rvalue::Discriminant` of an enum-typed place.

* `otherwiseIsEmptyUnreachable` is
  `body.basic_blocks[targets.otherwise()].is_empty_unreachable()`;
* `ub` is the block returned by `patch.unreachable_no_cleanup_block()`.

If at most one allowed value is left unclaimed and the `otherwise` block is
not already an empty unreachable block, the `otherwise` edge becomes `ub`, and
when exactly one value is left it first gets an explicit case that jumps to
the old `otherwise` block (`targets.add_target(last_variant, targets.otherwise())`). -/
noncomputable def unreachableEnumBranching (e : EnumDecl) (otherwiseIsEmptyUnreachable : Bool) (ub : Nat)
    (sw : SwitchTargets) : SwitchTargets :=
  let r := pruneCases ub sw.cases (allowedVariants e)
  match Nat.ble r.2.length 1 && !otherwiseIsEmptyUnreachable with
  | true =>
    match r.2 with
    | [last] => ⟨r.1 ++ [(last, sw.otherwise)], ub⟩
    | _ => ⟨r.1, ub⟩
  | false => ⟨r.1, sw.otherwise⟩

/-! ### Lemmas about the rewrite -/

theorem targetForValue_append (d : Nat) :
    ∀ (xs ys : List (Nat × Nat)) (o : Nat),
      targetForValue d (xs ++ ys) o = targetForValue d xs (targetForValue d ys o)
  | [], _, _ => rfl
  | (v, t) :: xs, ys, o => by
    cases hv : Nat.beq v d with
    | true => simp [targetForValue, hv]
    | false => simp [targetForValue, hv, targetForValue_append d xs ys o]

theorem memb_eraseFirst_of_ne (d v : Nat) (hne : Nat.beq v d = false) :
    ∀ allowed : List Nat, memb d allowed = true → memb d (eraseFirst v allowed) = true
  | [], h => by simp [memb] at h
  | x :: xs, h => by
    cases hxv : Nat.beq x v with
    | true =>
      have hxeq : x = v := Nat.eq_of_beq_eq_true hxv
      have hxd : Nat.beq x d = false := by rw [hxeq]; exact hne
      simpa [eraseFirst, hxv, memb, hxd] using h
    | false =>
      cases hxd : Nat.beq x d with
      | true => simp [eraseFirst, hxv, memb, hxd]
      | false =>
        have hxs : memb d xs = true := by simpa [memb, hxd] using h
        simp [eraseFirst, hxv, memb, hxd, memb_eraseFirst_of_ne d v hne xs hxs]

/-- For a value that is still allowed, pruning does not change which target
the explicit cases select (for any fallback). -/
theorem pruneCases_target (ub d : Nat) :
    ∀ (cases : List (Nat × Nat)) (allowed : List Nat) (o : Nat), memb d allowed = true →
      targetForValue d (pruneCases ub cases allowed).1 o = targetForValue d cases o
  | [], _, _, _ => rfl
  | (v, t) :: rest, allowed, o, h => by
    cases hvd : Nat.beq v d with
    | true =>
      have hveq : v = d := Nat.eq_of_beq_eq_true hvd
      have hmem : memb v allowed = true := by rw [hveq]; exact h
      simp [pruneCases, hmem, targetForValue, hvd]
    | false =>
      cases hmem : memb v allowed with
      | true =>
        simp [pruneCases, hmem, targetForValue, hvd,
          pruneCases_target ub d rest (eraseFirst v allowed) o
            (memb_eraseFirst_of_ne d v hvd allowed h)]
      | false =>
        simp [pruneCases, hmem, targetForValue, hvd, pruneCases_target ub d rest allowed o h]

/-- `true` iff some explicit case has value `d`. -/
noncomputable def hasCase (d : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | (v, _) :: rest => Nat.beq v d || hasCase d rest

theorem targetForValue_of_hasCase (d : Nat) :
    ∀ (cases : List (Nat × Nat)) (o o' : Nat), hasCase d cases = true →
      targetForValue d cases o = targetForValue d cases o'
  | [], _, _, h => by simp [hasCase] at h
  | (v, t) :: rest, o, o', h => by
    cases hvd : Nat.beq v d with
    | true => simp [targetForValue, hvd]
    | false =>
      have hrest : hasCase d rest = true := by simpa [hasCase, hvd] using h
      simp [targetForValue, hvd, targetForValue_of_hasCase d rest o o' hrest]

theorem targetForValue_of_not_hasCase (d : Nat) :
    ∀ (cases : List (Nat × Nat)) (o : Nat), hasCase d cases = false →
      targetForValue d cases o = o
  | [], _, _ => rfl
  | (v, t) :: rest, o, h => by
    cases hvd : Nat.beq v d with
    | true => simp [hasCase, hvd] at h
    | false =>
      have hrest : hasCase d rest = false := by simpa [hasCase, hvd] using h
      simp [targetForValue, hvd, targetForValue_of_not_hasCase d rest o hrest]

/-- An allowed value that no explicit case claims is still in the allowed set
after the loop. -/
theorem pruneCases_keeps_unclaimed (ub d : Nat) :
    ∀ (cases : List (Nat × Nat)) (allowed : List Nat), memb d allowed = true →
      hasCase d cases = false → memb d (pruneCases ub cases allowed).2 = true
  | [], _, h, _ => h
  | (v, t) :: rest, allowed, h, hc => by
    cases hvd : Nat.beq v d with
    | true => simp [hasCase, hvd] at hc
    | false =>
      have hrest : hasCase d rest = false := by simpa [hasCase, hvd] using hc
      cases hmem : memb v allowed with
      | true =>
        simp [pruneCases, hmem,
          pruneCases_keeps_unclaimed ub d rest (eraseFirst v allowed)
            (memb_eraseFirst_of_ne d v hvd allowed h) hrest]
      | false =>
        simp [pruneCases, hmem, pruneCases_keeps_unclaimed ub d rest allowed h hrest]

theorem ble_zero_one : Nat.ble 0 1 = true := rfl

theorem ble_one_one : Nat.ble 1 1 = true := rfl

theorem ble_add_two_one (n : Nat) : Nat.ble (n + 1 + 1) 1 = false := rfl

/-- For every discriminant of an inhabited variant, the rewritten switch
selects the same block as the original switch. -/
theorem unreachableEnumBranching_target (e : EnumDecl) (oeu : Bool) (ub : Nat)
    (sw : SwitchTargets) (d : Nat) (hd : memb d (allowedVariants e) = true) :
    targetForValue d (unreachableEnumBranching e oeu ub sw).cases
        (unreachableEnumBranching e oeu ub sw).otherwise
      = targetForValue d sw.cases sw.otherwise := by
  have hT := pruneCases_target ub d sw.cases (allowedVariants e)
  have hK := pruneCases_keeps_unclaimed ub d sw.cases (allowedVariants e) hd
  simp only [unreachableEnumBranching]
  cases hr : (pruneCases ub sw.cases (allowedVariants e)).2 with
  | nil =>
    cases oeu with
    | true => simp [ble_zero_one, hT _ hd]
    | false =>
      cases hc : hasCase d sw.cases with
      | true =>
        -- an explicit case claims `d`: the fallback is irrelevant
        simp [ble_zero_one, hT _ hd, targetForValue_of_hasCase d sw.cases ub sw.otherwise hc]
      | false =>
        -- impossible: `d` would still be in the (empty) unclaimed set
        have hkeep := hK hc
        rw [hr] at hkeep
        simp [memb] at hkeep
  | cons x xs =>
    cases xs with
    | nil =>
      cases oeu with
      | true => simp [ble_one_one, hT _ hd]
      | false =>
        cases hc : hasCase d sw.cases with
        | true =>
          simp [ble_one_one, targetForValue_append, hT _ hd,
            targetForValue_of_hasCase d sw.cases
              (targetForValue d [(x, sw.otherwise)] ub) sw.otherwise hc]
        | false =>
          -- `d` is the single unclaimed value, so it gets the new explicit case
          have hkeep := hK hc
          rw [hr] at hkeep
          have hxd : Nat.beq x d = true := by simpa [memb] using hkeep
          simp [ble_one_one, targetForValue_append, hT _ hd, targetForValue, hxd,
            targetForValue_of_not_hasCase d sw.cases sw.otherwise hc]
    | cons y ys =>
      simp [ble_add_two_one, hT _ hd]

theorem findVariant_discr (tag : Nat) :
    ∀ (e : EnumDecl) (v : Variant), findVariant tag e = some v → v.discr = tag
  | [], _, h => by simp [findVariant] at h
  | w :: ws, v, h => by
    cases hw : Nat.beq w.discr tag with
    | true =>
      have hv : w = v := by simpa [findVariant, hw] using h
      rw [← hv]; exact Nat.eq_of_beq_eq_true hw
    | false =>
      have hrest : findVariant tag ws = some v := by simpa [findVariant, hw] using h
      exact findVariant_discr tag ws v hrest

theorem memb_allowedVariants_of_find (tag : Nat) :
    ∀ (e : EnumDecl) (v : Variant), findVariant tag e = some v → v.inhabited = true →
      memb v.discr (allowedVariants e) = true
  | [], _, h, _ => by simp [findVariant] at h
  | w :: ws, v, h, hv => by
    cases hw : Nat.beq w.discr tag with
    | true =>
      have hwv : w = v := by simpa [findVariant, hw] using h
      subst hwv
      simp [allowedVariants, hv, memb, Nat.beq_refl]
    | false =>
      have hrest : findVariant tag ws = some v := by simpa [findVariant, hw] using h
      have ih := memb_allowedVariants_of_find tag ws v hrest hv
      cases hwi : w.inhabited with
      | true => simp [allowedVariants, hwi, memb, ih]
      | false => simp [allowedVariants, hwi, ih]

/-! ### Theorem 2: soundness under the strict semantics -/

/-- `tgt` refines `src`: whenever the source has defined behavior, the target
has the same behavior. -/
noncomputable def Refines (src tgt : Outcome) : Prop := src = Outcome.ub ∨ tgt = src

/-- Whenever the strict semantics yields a discriminant, it is the
discriminant of an inhabited variant. -/
theorem strict_some_mem_allowed (e : EnumDecl) (tag d : Nat)
    (h : evalDiscriminantStrict e tag = some d) : memb d (allowedVariants e) = true := by
  unfold evalDiscriminantStrict at h
  cases hf : findVariant tag e with
  | none => simp [hf] at h
  | some v =>
    cases hv : v.inhabited with
    | false => simp [hf, hv] at h
    | true =>
      have hdv : v.discr = d := by simpa [hf, hv] using h
      rw [← hdv]
      exact memb_allowedVariants_of_find tag e v hf hv

/-- Whenever the strict semantics yields a discriminant, it equals the tag. -/
theorem strict_some_eq_tag (e : EnumDecl) (tag d : Nat)
    (h : evalDiscriminantStrict e tag = some d) : d = tag := by
  unfold evalDiscriminantStrict at h
  cases hf : findVariant tag e with
  | none => simp [hf] at h
  | some v =>
    cases hv : v.inhabited with
    | false => simp [hf, hv] at h
    | true =>
      have hdv : v.discr = d := by simpa [hf, hv] using h
      rw [← hdv]
      exact findVariant_discr tag e v hf

/-- **Behavior preservation for any semantics that only yields inhabited
discriminants.** If a discriminant semantics never returns a value outside
the discriminants of the inhabited variants of `e`, then for every switch,
replacement block `ub`, block environment and tag value the rewritten switch
has exactly the behavior of the original one. No assumption about `ub` is
needed: no execution with defined behavior reaches a redirected edge. -/
theorem unreachableEnumBranching_preserves_of_allowed_only (sem : DiscrSem) (e : EnumDecl)
    (hsem : ∀ tag d, sem e tag = some d → memb d (allowedVariants e) = true)
    (oeu : Bool) (ub : Nat) (sw : SwitchTargets) (env : BlockEnv) (tag : Nat) :
    runSwitch sem e env (unreachableEnumBranching e oeu ub sw) tag
      = runSwitch sem e env sw tag := by
  cases hs : sem e tag with
  | none => simp [runSwitch, hs]
  | some d =>
    simp [runSwitch, hs, unreachableEnumBranching_target e oeu ub sw d (hsem tag d hs)]

/-- **Behavior preservation under the strict semantics.** -/
theorem unreachableEnumBranching_preserves_strict (e : EnumDecl) (oeu : Bool) (ub : Nat)
    (sw : SwitchTargets) (env : BlockEnv) (tag : Nat) :
    runSwitch evalDiscriminantStrict e env (unreachableEnumBranching e oeu ub sw) tag
      = runSwitch evalDiscriminantStrict e env sw tag :=
  unreachableEnumBranching_preserves_of_allowed_only evalDiscriminantStrict e
    (strict_some_mem_allowed e) oeu ub sw env tag

/-- **Refinement soundness of `unreachableEnumBranching` under
`evalDiscriminantStrict`.** -/
theorem unreachableEnumBranching_refines_strict (e : EnumDecl) (oeu : Bool) (ub : Nat)
    (sw : SwitchTargets) (env : BlockEnv) (tag : Nat) :
    Refines (runSwitch evalDiscriminantStrict e env sw tag)
      (runSwitch evalDiscriminantStrict e env (unreachableEnumBranching e oeu ub sw) tag) :=
  Or.inr (unreachableEnumBranching_preserves_strict e oeu ub sw env tag)

/-- If every variant is inhabited, the declared-tag semantics and the strict
semantics agree, so the rewrite needs only the invalid-tag rule there. -/
theorem declaredTag_eq_strict_of_all_inhabited :
    ∀ (e : EnumDecl), (∀ v, v ∈ e → v.inhabited = true) →
      ∀ tag, evalDiscriminantDeclaredTag e tag = evalDiscriminantStrict e tag
  | [], _, _ => rfl
  | w :: ws, h, tag => by
    have hw : w.inhabited = true := h w (List.Mem.head ws)
    have ih := declaredTag_eq_strict_of_all_inhabited ws
      (fun v hv => h v (List.Mem.tail w hv)) tag
    unfold evalDiscriminantDeclaredTag evalDiscriminantStrict at ih ⊢
    cases hd : Nat.beq w.discr tag with
    | true => simp [findVariant, hd, hw]
    | false => simpa [findVariant, hd] using ih

theorem unreachableEnumBranching_preserves_declaredTag_of_all_inhabited (e : EnumDecl)
    (hall : ∀ v, v ∈ e → v.inhabited = true) (oeu : Bool) (ub : Nat) (sw : SwitchTargets)
    (env : BlockEnv) (tag : Nat) :
    runSwitch evalDiscriminantDeclaredTag e env (unreachableEnumBranching e oeu ub sw) tag
      = runSwitch evalDiscriminantDeclaredTag e env sw tag := by
  have h := unreachableEnumBranching_preserves_strict e oeu ub sw env tag
  unfold runSwitch at h ⊢
  rw [declaredTag_eq_strict_of_all_inhabited e hall tag]
  exact h

/-! ### The inhabited-only rule is also necessary -/

/-- A switch that names every value of `vs` explicitly, all jumping to `o`. -/
noncomputable def namedCases (o : Nat) : List Nat → List (Nat × Nat)
  | [] => []
  | v :: vs => (v, o) :: namedCases o vs

theorem pruneCases_namedCases (ub o : Nat) :
    ∀ xs : List Nat, pruneCases ub (namedCases o xs) xs = (namedCases o xs, [])
  | [] => rfl
  | v :: vs => by
    simp [namedCases, pruneCases, memb, eraseFirst, Nat.beq_refl, pruneCases_namedCases ub o vs]

theorem targetForValue_namedCases (d o : Nat) :
    ∀ xs : List Nat, targetForValue d (namedCases o xs) o = o
  | [] => rfl
  | v :: vs => by
    cases hv : Nat.beq v d with
    | true => simp [namedCases, targetForValue, hv]
    | false => simp [namedCases, targetForValue, hv, targetForValue_namedCases d o vs]

theorem targetForValue_namedCases_of_not_memb (d o fb : Nat) :
    ∀ xs : List Nat, memb d xs = false → targetForValue d (namedCases o xs) fb = fb
  | [], _ => rfl
  | v :: vs, h => by
    cases hv : Nat.beq v d with
    | true => simp [memb, hv] at h
    | false =>
      have hvs : memb d vs = false := by simpa [memb, hv] using h
      simp [namedCases, targetForValue, hv, targetForValue_namedCases_of_not_memb d o fb vs hvs]

/-- Block 0 returns 0; every other block is `unreachable`. -/
noncomputable def necessityEnv : BlockEnv := fun b =>
  match b with
  | 0 => .ret 0
  | _ => .ub

/-- **Necessity.** For every enum `e`: if a discriminant semantics can return,
for some tag, a value `d` that is not the discriminant of an inhabited
variant, then the switch that names every inhabited discriminant and sends
everything (including the fallback) to block 0 is miscompiled: the original
returns 0 on that tag, the rewritten switch reaches the `unreachable` block. -/
theorem inhabited_only_rule_is_necessary (sem : DiscrSem) (e : EnumDecl) (tag d : Nat)
    (hsem : sem e tag = some d) (hd : memb d (allowedVariants e) = false) :
    runSwitch sem e necessityEnv ⟨namedCases 0 (allowedVariants e), 0⟩ tag = Outcome.ret 0
    ∧ runSwitch sem e necessityEnv
        (unreachableEnumBranching e false 1 ⟨namedCases 0 (allowedVariants e), 0⟩) tag
      = Outcome.ub := by
  have hU : unreachableEnumBranching e false 1 ⟨namedCases 0 (allowedVariants e), 0⟩
      = ⟨namedCases 0 (allowedVariants e), 1⟩ := by
    simp [unreachableEnumBranching, pruneCases_namedCases, ble_zero_one]
  refine ⟨?_, ?_⟩
  · unfold runSwitch
    rw [hsem]
    show necessityEnv (targetForValue d (namedCases 0 (allowedVariants e)) 0) = _
    rw [targetForValue_namedCases]
    rfl
  · rw [hU]
    unfold runSwitch
    rw [hsem]
    show necessityEnv (targetForValue d (namedCases 0 (allowedVariants e)) 1) = _
    rw [targetForValue_namedCases_of_not_memb d 0 1 _ hd]
    rfl

/-- **Exact characterization.** For a fixed enum, the rewrite refines every
switch (for every replacement block that behaves as `unreachable`) if and only
if the discriminant semantics never yields a value outside the discriminants
of the inhabited variants. -/
theorem unreachableEnumBranching_sound_iff_allowed_only (sem : DiscrSem) (e : EnumDecl) :
    (∀ (oeu : Bool) (ub : Nat) (sw : SwitchTargets) (env : BlockEnv) (tag : Nat),
        env ub = Outcome.ub →
        Refines (runSwitch sem e env sw tag)
          (runSwitch sem e env (unreachableEnumBranching e oeu ub sw) tag))
    ↔ (∀ tag d, sem e tag = some d → memb d (allowedVariants e) = true) := by
  constructor
  · intro h tag d hsem
    cases hm : memb d (allowedVariants e) with
    | true => rfl
    | false =>
      have hw := inhabited_only_rule_is_necessary sem e tag d hsem hm
      have hr := h false 1 ⟨namedCases 0 (allowedVariants e), 0⟩ necessityEnv tag rfl
      rw [hw.1, hw.2] at hr
      cases hr with
      | inl hsrc => exact Outcome.noConfusion hsrc
      | inr htgt => exact Outcome.noConfusion htgt
  · intro hsem oeu ub sw env tag _
    exact Or.inr (unreachableEnumBranching_preserves_of_allowed_only sem e hsem oeu ub sw env tag)

/-! ### Theorem 3 and counterexample 3: unsoundness under raw-tag reads

The witness is the executed probe program:

```text
#[repr(u8)] enum Tri { A(u32), B(Never), C }      // Never has no values
unsafe { match *p { Tri::A(v) => v + 1, _ => 77 } }
```

whose MIR before the pass is `switchInt(move _2) -> [0: bb2, otherwise: bb1]`
and after the pass is `switchInt(move _2) -> [0: bb2, 2: bb1, otherwise: bb4]`
with `bb4: unreachable`. -/

/-- `Tri`: variant `B` (discriminant 1) is uninhabited. -/
noncomputable def tri : EnumDecl := [⟨0, true⟩, ⟨1, false⟩, ⟨2, true⟩]

/-- `switchInt(move _2) -> [0: bb2, otherwise: bb1]`. -/
noncomputable def triWildcardSwitch : SwitchTargets := ⟨[(0, 2)], 1⟩

/-- `bb1` returns 77 (the wildcard arm), `bb2` returns the payload plus one
(42 for payload 41), every other block (in particular the new `bb4`) is
`unreachable`. -/
noncomputable def triEnv : BlockEnv := fun b =>
  match b with
  | 1 => .ret 77
  | 2 => .ret 42
  | _ => .ub

/-- The model reproduces the rewrite observed in the compiler's MIR dump. -/
theorem tri_rewrite_matches_observed_mir :
    unreachableEnumBranching tri false 4 triWildcardSwitch = ⟨[(0, 2), (2, 1)], 4⟩ := rfl

/-- All-variants-named switch through a reference, as observed:
`[0: bb4, 1: bb3, 2: bb2, otherwise: bb1]` with `bb1` an empty unreachable
block becomes `[0: bb4, 1: bb1, 2: bb2, otherwise: bb1]`. -/
theorem tri_exhaustive_rewrite_matches_observed_mir :
    unreachableEnumBranching tri true 1 ⟨[(0, 4), (1, 3), (2, 2)], 1⟩
      = ⟨[(0, 4), (1, 1), (2, 2)], 1⟩ := rfl

/-- Valid tags behave identically before and after the rewrite under every
semantics considered. -/
theorem tri_valid_tags_unchanged (sem : DiscrSem)
    (h0 : sem tri 0 = some 0) (h2 : sem tri 2 = some 2) :
    runSwitch sem tri triEnv triWildcardSwitch 0 = Outcome.ret 42
    ∧ runSwitch sem tri triEnv (unreachableEnumBranching tri false 4 triWildcardSwitch) 0
        = Outcome.ret 42
    ∧ runSwitch sem tri triEnv triWildcardSwitch 2 = Outcome.ret 77
    ∧ runSwitch sem tri triEnv (unreachableEnumBranching tri false 4 triWildcardSwitch) 2
        = Outcome.ret 77 := by
  rw [tri_rewrite_matches_observed_mir]
  unfold runSwitch
  rw [h0, h2]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Under the strict semantics the source program already has undefined
behavior on tag 1, which is what the interpreter reports. -/
theorem tri_tag1_is_ub_under_strict :
    runSwitch evalDiscriminantStrict tri triEnv triWildcardSwitch 1 = Outcome.ub := rfl

/-- Tag 3 matches no declared variant: undefined behavior under both the
strict and the declared-tag semantics (the interpreter's `InvalidTag`). -/
theorem tri_tag3_is_ub_under_strict_and_declaredTag :
    runSwitch evalDiscriminantStrict tri triEnv triWildcardSwitch 3 = Outcome.ub
    ∧ runSwitch evalDiscriminantDeclaredTag tri triEnv triWildcardSwitch 3 = Outcome.ub :=
  ⟨rfl, rfl⟩

/-- **Counterexample 3.** If reading a discriminant returned the raw tag, the
source program would return 77 on tag 1 (the wildcard arm), while the
rewritten program reaches `unreachable`: the rewrite would turn defined
behavior into undefined behavior. The same holds for the declared-tag
semantics, so the invalid-tag rule alone does not justify the rewrite. -/
theorem ce3_raw_tag_discriminant_semantics_makes_unreachable_enum_branching_unsound :
    runSwitch evalDiscriminantRawTag tri triEnv triWildcardSwitch 1 = Outcome.ret 77
    ∧ runSwitch evalDiscriminantRawTag tri triEnv
        (unreachableEnumBranching tri false 4 triWildcardSwitch) 1 = Outcome.ub
    ∧ runSwitch evalDiscriminantDeclaredTag tri triEnv triWildcardSwitch 1 = Outcome.ret 77
    ∧ runSwitch evalDiscriminantDeclaredTag tri triEnv
        (unreachableEnumBranching tri false 4 triWildcardSwitch) 1 = Outcome.ub :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Unsoundness of `unreachableEnumBranching` under `evalDiscriminantRawTag`.**
The refinement statement that holds for the strict semantics is false for the
raw-tag semantics. -/
theorem unreachableEnumBranching_unsound_rawTag :
    ¬ (∀ (e : EnumDecl) (oeu : Bool) (ub : Nat) (sw : SwitchTargets) (env : BlockEnv)
        (tag : Nat), env ub = Outcome.ub →
        Refines (runSwitch evalDiscriminantRawTag e env sw tag)
          (runSwitch evalDiscriminantRawTag e env (unreachableEnumBranching e oeu ub sw) tag)) := by
  intro h
  have h1 := h tri false 4 triWildcardSwitch triEnv 1 rfl
  cases h1 with
  | inl hsrc => exact Outcome.noConfusion hsrc
  | inr htgt => exact Outcome.noConfusion htgt

/-- The same refinement statement is false for the declared-tag semantics. -/
theorem unreachableEnumBranching_unsound_declaredTag :
    ¬ (∀ (e : EnumDecl) (oeu : Bool) (ub : Nat) (sw : SwitchTargets) (env : BlockEnv)
        (tag : Nat), env ub = Outcome.ub →
        Refines (runSwitch evalDiscriminantDeclaredTag e env sw tag)
          (runSwitch evalDiscriminantDeclaredTag e env
            (unreachableEnumBranching e oeu ub sw) tag)) := by
  intro h
  have h1 := h tri false 4 triWildcardSwitch triEnv 1 rfl
  cases h1 with
  | inl hsrc => exact Outcome.noConfusion hsrc
  | inr htgt => exact Outcome.noConfusion htgt

end EditionDropScopesAndEnumBranching

open EditionDropScopesAndEnumBranching in
#print axioms dropTrace_reversal_and_match_invariance
open EditionDropScopesAndEnumBranching in
#print axioms compileBlockTail_ed2021
open EditionDropScopesAndEnumBranching in
#print axioms compileBlockTail_ed2024
open EditionDropScopesAndEnumBranching in
#print axioms blockTail_edition_visible_of_cons
open EditionDropScopesAndEnumBranching in
#print axioms blockTail_edition_invisible_of_nil
open EditionDropScopesAndEnumBranching in
#print axioms compileIfLetElse_else_ed2021
open EditionDropScopesAndEnumBranching in
#print axioms compileIfLetElse_else_ed2024
open EditionDropScopesAndEnumBranching in
#print axioms compileIfLetElse_then
open EditionDropScopesAndEnumBranching in
#print axioms compileMatch_plain
open EditionDropScopesAndEnumBranching in
#print axioms match_block_scrutinee_is_edition_sensitive
open EditionDropScopesAndEnumBranching in
#print axioms ifLet_then_path_invariant
open EditionDropScopesAndEnumBranching in
#print axioms probe_tail_ed2021
open EditionDropScopesAndEnumBranching in
#print axioms probe_tail_ed2024
open EditionDropScopesAndEnumBranching in
#print axioms probe_if_let_else_ed2021
open EditionDropScopesAndEnumBranching in
#print axioms probe_if_let_else_ed2024
open EditionDropScopesAndEnumBranching in
#print axioms probe_if_let_then
open EditionDropScopesAndEnumBranching in
#print axioms probe_match
open EditionDropScopesAndEnumBranching in
#print axioms probe_match_block_scrutinee_ed2021
open EditionDropScopesAndEnumBranching in
#print axioms probe_match_block_scrutinee_ed2024
open EditionDropScopesAndEnumBranching in
#print axioms ce1_ed2021_tail_temp_borrow_of_local_dangling_vs_ed2024_safe
open EditionDropScopesAndEnumBranching in
#print axioms ce2_ed2021_if_let_mutex_guard_deadlocks_in_else_vs_ed2024_released
open EditionDropScopesAndEnumBranching in
#print axioms match_arm_relock_deadlocks_in_both_editions
open EditionDropScopesAndEnumBranching in
#print axioms unreachableEnumBranching_preserves_strict
open EditionDropScopesAndEnumBranching in
#print axioms unreachableEnumBranching_refines_strict
open EditionDropScopesAndEnumBranching in
#print axioms unreachableEnumBranching_preserves_declaredTag_of_all_inhabited
open EditionDropScopesAndEnumBranching in
#print axioms tri_rewrite_matches_observed_mir
open EditionDropScopesAndEnumBranching in
#print axioms tri_exhaustive_rewrite_matches_observed_mir
open EditionDropScopesAndEnumBranching in
#print axioms tri_valid_tags_unchanged
open EditionDropScopesAndEnumBranching in
#print axioms tri_tag1_is_ub_under_strict
open EditionDropScopesAndEnumBranching in
#print axioms ce3_raw_tag_discriminant_semantics_makes_unreachable_enum_branching_unsound
open EditionDropScopesAndEnumBranching in
#print axioms unreachableEnumBranching_unsound_rawTag
open EditionDropScopesAndEnumBranching in
#print axioms unreachableEnumBranching_unsound_declaredTag
open EditionDropScopesAndEnumBranching in
#print axioms unreachableEnumBranching_preserves_of_allowed_only
open EditionDropScopesAndEnumBranching in
#print axioms inhabited_only_rule_is_necessary
open EditionDropScopesAndEnumBranching in
#print axioms unreachableEnumBranching_sound_iff_allowed_only
open EditionDropScopesAndEnumBranching in
#print axioms tri_tag3_is_ub_under_strict_and_declaredTag
open EditionDropScopesAndEnumBranching in
#print axioms blockTail_dropTrace_ed2021
open EditionDropScopesAndEnumBranching in
#print axioms blockTail_dropTrace_ed2024
open EditionDropScopesAndEnumBranching in
#print axioms compileMatch_block_ed2021
open EditionDropScopesAndEnumBranching in
#print axioms compileMatch_block_ed2024
