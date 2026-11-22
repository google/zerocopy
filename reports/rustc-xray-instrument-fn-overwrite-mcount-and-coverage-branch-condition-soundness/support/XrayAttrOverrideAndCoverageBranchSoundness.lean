/-!
# XRay attribute override and coverage branch soundness

A self-contained model (prelude only, no imports) of two `rustc` mechanisms.

Part A. Function-entry instrumentation attributes.
* LLVM's attribute builder keeps one entry per string key: adding an attribute
  whose key is already present replaces the old value (`addAttr`).
* `rustc`'s XRay attribute selection keeps two independent booleans
  (`never`, `always`), lets `#[instrument_fn = "on" | "off"]` set one of them
  without clearing the other, and pushes `xray-never` before `xray-always`
  (`pushesNeverFirst`). The surviving attribute is therefore `xray-always`
  whenever `always` is set.
* The intended meaning is "the attribute overrides the command line"
  (`resolve`). The theorems state exactly where the two-boolean encoding
  departs from it, for either push order, and that a single three-valued mode
  agrees everywhere.
* A fuel-indexed model of an XRay handler that calls a helper whose entry sled
  is patched: the call never returns.

Part B. Coverage instrumentation levels.
* Branch mappings are kept only for branch spans whose syntax context is the
  function body's context, and only if that context is the root expansion
  (`extractBranchMappings`).
* The `!`-chain bookkeeping (`NotInfo`) places the true marker in the arm that
  runs exactly when the whole source expression `!^k e` is true.
* The condition-level diamond conserves flow, and the number of branch spans
  per level is characterised for lazy boolean value expressions.

Every recursive definition is marked `noncomputable`, so no executable
auxiliary definitions are generated; all results are checked by the kernel.
-/

namespace XrayCov

/-! ## Part A.1 — attribute builder: replace on equal key -/

section AttrBuilder

variable {K V : Type} [DecidableEq K]

/-- `AttrBuilder::addAttribute` for one attribute: if an entry with the same key
exists its value is replaced, otherwise the attribute is inserted. (LLVM keeps
the entries sorted by key; ordering does not affect lookup and is not modelled.) -/
noncomputable def addAttr (b : List (K × V)) (k : K) (v : V) : List (K × V) :=
  match b with
  | [] => [(k, v)]
  | (k', v') :: rest => if k' = k then (k, v) :: rest else (k', v') :: addAttr rest k v

/-- Attribute lookup by key. -/
noncomputable def getAttr (b : List (K × V)) (k : K) : Option V :=
  match b with
  | [] => none
  | (k', v') :: rest => if k' = k then some v' else getAttr rest k

/-- The loop `for (Attr : Attrs) B.addAttribute(Attr)`: pushes applied left to right. -/
noncomputable def addAll (b : List (K × V)) (pushes : List (K × V)) : List (K × V) :=
  match pushes with
  | [] => b
  | (k, v) :: rest => addAll (addAttr b k v) rest

/-- The value carried by the last push with key `k`, if any push has that key. -/
noncomputable def lastPush (pushes : List (K × V)) (k : K) : Option V :=
  match pushes with
  | [] => none
  | (k', v') :: rest =>
    match lastPush rest k with
    | some v => some v
    | none => if k' = k then some v' else none

theorem getAttr_addAttr_same (b : List (K × V)) (k : K) (v : V) :
    getAttr (addAttr b k v) k = some v := by
  induction b with
  | nil => simp [addAttr, getAttr]
  | cons hd tl ih =>
    cases hd with
    | mk k' v' =>
      by_cases h : k' = k
      · simp [addAttr, getAttr, h]
      · simp [addAttr, getAttr, h, ih]

theorem getAttr_addAttr_other (b : List (K × V)) (k k₂ : K) (v : V) (hne : k ≠ k₂) :
    getAttr (addAttr b k v) k₂ = getAttr b k₂ := by
  induction b with
  | nil => simp [addAttr, getAttr, hne]
  | cons hd tl ih =>
    cases hd with
    | mk k' v' =>
      by_cases h : k' = k
      · simp [addAttr, getAttr, h, hne]
      · by_cases h3 : k' = k₂
        · subst h3
          simp [addAttr, getAttr, h]
        · simp [addAttr, getAttr, h, h3, ih]

/-- **Last push wins.** After a sequence of pushes, the value stored for key `k`
is the value of the last push with that key; keys never pushed keep their
previous value. -/
theorem getAttr_addAll (pushes : List (K × V)) (b : List (K × V)) (k : K) :
    getAttr (addAll b pushes) k =
      match lastPush pushes k with
      | some v => some v
      | none => getAttr b k := by
  induction pushes generalizing b with
  | nil => simp [addAll, lastPush]
  | cons hd tl ih =>
    cases hd with
    | mk k' v' =>
      simp only [addAll, lastPush]
      rw [ih]
      cases hl : lastPush tl k with
      | some v => rfl
      | none =>
        by_cases h : k' = k
        · subst h
          simp [getAttr_addAttr_same]
        · simp [h, getAttr_addAttr_other _ _ _ _ h]

end AttrBuilder

/-! ## Part A.2 — `rustc`'s XRay attribute selection -/

/-- LLVM string-attribute keys pushed by the XRay branch. -/
inductive AttrKey where
  /-- `"function-instrument"` -/
  | functionInstrument
  /-- `"xray-instruction-threshold"` -/
  | xrayInstructionThreshold
  deriving DecidableEq

/-- Values of those attributes. -/
inductive AttrVal where
  /-- `"xray-never"` -/
  | xrayNever
  /-- `"xray-always"` -/
  | xrayAlways
  /-- the decimal instruction threshold -/
  | threshold (n : Nat)
  deriving DecidableEq

/-- One pushed attribute. -/
abbrev Push := AttrKey × AttrVal

/-- The `always` / `never` fields of the parsed `-Z instrument-xray` settings. -/
structure XRayOptions where
  always : Bool
  never : Bool

/-- `#[instrument_fn = "on"]` / `#[instrument_fn = "off"]`. -/
inductive InstrumentFnAttr where
  | on
  | off
  deriving DecidableEq

/-- The comma-separated words of `-Z instrument-xray=...`, as far as they touch
`always` / `never`. -/
inductive XRayWord where
  | always
  | never
  | other

/-- Option parser: `"always"` sets `always` and clears `never`; `"never"` does
the reverse; other words leave both alone. -/
def applyWord (o : XRayOptions) : XRayWord → XRayOptions
  | .always => { always := true, never := false }
  | .never => { always := false, never := true }
  | .other => o

/-- The command line never yields both flags at once. -/
def WellFormed (o : XRayOptions) : Prop := ¬ (o.always = true ∧ o.never = true)

instance (o : XRayOptions) : Decidable (WellFormed o) :=
  inferInstanceAs (Decidable (¬ (o.always = true ∧ o.never = true)))

theorem applyWord_wellFormed (o : XRayOptions) (w : XRayWord) (h : WellFormed o) :
    WellFormed (applyWord o w) := by
  cases w with
  | always => intro hc; cases hc.2
  | never => intro hc; cases hc.1
  | other => exact h

/-- Any sequence of words, over any number of `-Z instrument-xray=` arguments,
preserves well-formedness: the double push below cannot come from the command
line alone. -/
theorem parse_wellFormed (ws : List XRayWord) (o : XRayOptions) (h : WellFormed o) :
    WellFormed (ws.foldl applyWord o) := by
  induction ws generalizing o with
  | nil => exact h
  | cons w tl ih => exact ih (applyWord o w) (applyWord_wellFormed o w h)

/-- `let mut never = options.never; ... Some(Off) => { never = true; }` -/
def effNever (o : XRayOptions) (a : Option InstrumentFnAttr) : Bool :=
  match a with
  | some .off => true
  | _ => o.never

/-- `let mut always = options.always; ... Some(On) => { always = true; }` -/
def effAlways (o : XRayOptions) (a : Option InstrumentFnAttr) : Bool :=
  match a with
  | some .on => true
  | _ => o.always

def neverPush : List Push := [(.functionInstrument, .xrayNever)]
def alwaysPush : List Push := [(.functionInstrument, .xrayAlways)]
def thresholdPush : List Push := [(.xrayInstructionThreshold, .threshold 200)]

/-- Source order once `#[instrument_fn]` exists:
`if never { push xray-never }  if always { push xray-always }`, then the threshold. -/
def pushesNeverFirst (o : XRayOptions) (a : Option InstrumentFnAttr) : List Push :=
  (if effNever o a then neverPush else []) ++ (if effAlways o a then alwaysPush else [])
    ++ thresholdPush

/-- The same two booleans pushed in the opposite order (the order used before
`#[instrument_fn]` existed). -/
def pushesAlwaysFirst (o : XRayOptions) (a : Option InstrumentFnAttr) : List Push :=
  (if effAlways o a then alwaysPush else []) ++ (if effNever o a then neverPush else [])
    ++ thresholdPush

/-- `"function-instrument"` on the function after the pushes went through the builder. -/
noncomputable def finalOf (pushes : List Push) : Option AttrVal :=
  getAttr (addAll [] pushes) .functionInstrument

noncomputable def finalNeverFirst (o : XRayOptions) (a : Option InstrumentFnAttr) :
    Option AttrVal :=
  finalOf (pushesNeverFirst o a)

noncomputable def finalAlwaysFirst (o : XRayOptions) (a : Option InstrumentFnAttr) :
    Option AttrVal :=
  finalOf (pushesAlwaysFirst o a)

/-- With `xray-never` pushed first, `always` dominates. -/
theorem finalNeverFirst_eq (o : XRayOptions) (a : Option InstrumentFnAttr) :
    finalNeverFirst o a =
      if effAlways o a then some .xrayAlways
      else if effNever o a then some .xrayNever else none := by
  unfold finalNeverFirst pushesNeverFirst
  cases effNever o a <;> cases effAlways o a <;> rfl

/-- With `xray-always` pushed first, `never` dominates. -/
theorem finalAlwaysFirst_eq (o : XRayOptions) (a : Option InstrumentFnAttr) :
    finalAlwaysFirst o a =
      if effNever o a then some .xrayNever
      else if effAlways o a then some .xrayAlways else none := by
  unfold finalAlwaysFirst pushesAlwaysFirst
  cases effNever o a <;> cases effAlways o a <;> rfl

/-! ### Intended meaning: the attribute overrides the command line -/

/-- The three mutually exclusive XRay modes of a function. -/
inductive XRayMode where
  | threshold
  | always
  | never
  deriving DecidableEq

/-- Mode selected by the command line. -/
def XRayOptions.mode (o : XRayOptions) : XRayMode :=
  if o.always then .always else if o.never then .never else .threshold

/-- A per-function attribute replaces the command-line mode. -/
def resolve (cli : XRayMode) (a : Option InstrumentFnAttr) : XRayMode :=
  match a with
  | some .on => .always
  | some .off => .never
  | none => cli

/-- The `"function-instrument"` value that expresses a mode. -/
def modeAttr : XRayMode → Option AttrVal
  | .always => some .xrayAlways
  | .never => some .xrayNever
  | .threshold => none

/-- Reference result for a function. -/
def spec (o : XRayOptions) (a : Option InstrumentFnAttr) : Option AttrVal :=
  modeAttr (resolve o.mode a)

/-- **The overwrite.** Under `-Z instrument-xray=always`, a function marked
`#[instrument_fn = "off"]` ends up with `"function-instrument"="xray-always"`. -/
theorem off_overwritten_under_always (o : XRayOptions) (h : o.always = true) :
    finalNeverFirst o (some .off) = some .xrayAlways := by
  rw [finalNeverFirst_eq]
  simp [effAlways, h]

/-- What `#[instrument_fn = "off"]` is meant to produce, for every command line. -/
theorem off_spec (o : XRayOptions) : spec o (some .off) = some .xrayNever := rfl

/-- `#[instrument_fn = "on"]` yields `xray-always` for every command line with
the never-first order ... -/
theorem on_survives_never_first (o : XRayOptions) :
    finalNeverFirst o (some .on) = some .xrayAlways := by
  rw [finalNeverFirst_eq]
  rfl

/-- ... and is lost under `-Z instrument-xray=never` if the two pushes are swapped:
the `on` override works only because of the push order. -/
theorem on_lost_always_first (o : XRayOptions) (h : o.never = true) :
    finalAlwaysFirst o (some .on) = some .xrayNever := by
  rw [finalAlwaysFirst_eq]
  simp [effNever, h]

/-- Exact disagreement set of the never-first order: precisely
(`always` on the command line, `off` on the function). -/
theorem neverFirst_agrees_iff (o : XRayOptions) (a : Option InstrumentFnAttr)
    (wf : WellFormed o) :
    finalNeverFirst o a = spec o a ↔ ¬ (o.always = true ∧ a = some .off) := by
  cases o with
  | mk al ne =>
    cases al <;> cases ne <;> first
      | exact absurd ⟨rfl, rfl⟩ wf
      | (cases a with
         | none => decide
         | some x => cases x <;> decide)

/-- Exact disagreement set of the always-first order: precisely
(`never` on the command line, `on` on the function). -/
theorem alwaysFirst_agrees_iff (o : XRayOptions) (a : Option InstrumentFnAttr)
    (wf : WellFormed o) :
    finalAlwaysFirst o a = spec o a ↔ ¬ (o.never = true ∧ a = some .on) := by
  cases o with
  | mk al ne =>
    cases al <;> cases ne <;> first
      | exact absurd ⟨rfl, rfl⟩ wf
      | (cases a with
         | none => decide
         | some x => cases x <;> decide)

/-- Neither order of two independent pushes implements the override. -/
theorem no_push_order_implements_override :
    (∃ o a, WellFormed o ∧ finalNeverFirst o a ≠ spec o a) ∧
    (∃ o a, WellFormed o ∧ finalAlwaysFirst o a ≠ spec o a) :=
  ⟨⟨⟨true, false⟩, some .off, by decide, by decide⟩,
   ⟨⟨false, true⟩, some .on, by decide, by decide⟩⟩

/-- The replay table measured by the probe (rows: command line threshold,
always, never; columns: no attribute, `on`, `off`), never-first order. -/
theorem table_neverFirst :
    [[finalNeverFirst ⟨false, false⟩ none, finalNeverFirst ⟨false, false⟩ (some .on),
      finalNeverFirst ⟨false, false⟩ (some .off)],
     [finalNeverFirst ⟨true, false⟩ none, finalNeverFirst ⟨true, false⟩ (some .on),
      finalNeverFirst ⟨true, false⟩ (some .off)],
     [finalNeverFirst ⟨false, true⟩ none, finalNeverFirst ⟨false, true⟩ (some .on),
      finalNeverFirst ⟨false, true⟩ (some .off)]]
    = [[none, some .xrayAlways, some .xrayNever],
       [some .xrayAlways, some .xrayAlways, some .xrayAlways],
       [some .xrayNever, some .xrayAlways, some .xrayNever]] := by
  decide

/-- The same table for the always-first order. -/
theorem table_alwaysFirst :
    [[finalAlwaysFirst ⟨false, false⟩ none, finalAlwaysFirst ⟨false, false⟩ (some .on),
      finalAlwaysFirst ⟨false, false⟩ (some .off)],
     [finalAlwaysFirst ⟨true, false⟩ none, finalAlwaysFirst ⟨true, false⟩ (some .on),
      finalAlwaysFirst ⟨true, false⟩ (some .off)],
     [finalAlwaysFirst ⟨false, true⟩ none, finalAlwaysFirst ⟨false, true⟩ (some .on),
      finalAlwaysFirst ⟨false, true⟩ (some .off)]]
    = [[none, some .xrayAlways, some .xrayNever],
       [some .xrayAlways, some .xrayAlways, some .xrayNever],
       [some .xrayNever, some .xrayNever, some .xrayNever]] := by
  decide

/-! ## Part A.3 — repairs -/

/-- Repair 1: a single three-valued mode; at most one push. -/
def pushesThreeState (cli : XRayMode) (a : Option InstrumentFnAttr) : List Push :=
  (match resolve cli a with
    | .always => alwaysPush
    | .never => neverPush
    | .threshold => []) ++ thresholdPush

noncomputable def finalThreeState (cli : XRayMode) (a : Option InstrumentFnAttr) :
    Option AttrVal :=
  finalOf (pushesThreeState cli a)

theorem threeState_agrees (cli : XRayMode) (a : Option InstrumentFnAttr) :
    finalThreeState cli a = modeAttr (resolve cli a) := by
  unfold finalThreeState pushesThreeState
  cases resolve cli a <;> rfl

theorem threeState_at_most_one_push (cli : XRayMode) (a : Option InstrumentFnAttr) :
    ((pushesThreeState cli a).filter (fun p => p.1 = .functionInstrument)).length ≤ 1 := by
  unfold pushesThreeState
  cases resolve cli a <;> decide

/-- The override is idempotent ... -/
theorem resolve_idempotent (cli : XRayMode) (a : Option InstrumentFnAttr) :
    resolve (resolve cli a) a = resolve cli a := by
  cases a with
  | none => rfl
  | some x => cases x <;> rfl

/-- ... ignores the command line when an attribute is present ... -/
theorem resolve_override (c₁ c₂ : XRayMode) (x : InstrumentFnAttr) :
    resolve c₁ (some x) = resolve c₂ (some x) := by
  cases x <;> rfl

/-- ... and is the identity without an attribute. -/
theorem resolve_none (cli : XRayMode) : resolve cli none = cli := rfl

/-- Repair 2: keep the two booleans but let the attribute set both
(`on ↦ (never, always) = (false, true)`, `off ↦ (true, false)`). -/
def fixedPair (o : XRayOptions) (a : Option InstrumentFnAttr) : Bool × Bool :=
  match a with
  | some .on => (false, true)
  | some .off => (true, false)
  | none => (o.never, o.always)

def pushesFixed (neverFirst : Bool) (o : XRayOptions) (a : Option InstrumentFnAttr) :
    List Push :=
  (if neverFirst then
      (if (fixedPair o a).1 then neverPush else []) ++
        (if (fixedPair o a).2 then alwaysPush else [])
    else
      (if (fixedPair o a).2 then alwaysPush else []) ++
        (if (fixedPair o a).1 then neverPush else [])) ++ thresholdPush

theorem fixedPair_exclusive (o : XRayOptions) (a : Option InstrumentFnAttr)
    (wf : WellFormed o) : ¬ ((fixedPair o a).1 = true ∧ (fixedPair o a).2 = true) := by
  cases a with
  | none => exact fun h => wf ⟨h.2, h.1⟩
  | some x =>
    cases x with
    | on => exact fun h => Bool.noConfusion h.1
    | off => exact fun h => Bool.noConfusion h.2

/-- With both booleans set by the attribute the result is the reference result,
and it no longer depends on the push order. -/
theorem fixed_agrees (neverFirst : Bool) (o : XRayOptions) (a : Option InstrumentFnAttr)
    (wf : WellFormed o) : finalOf (pushesFixed neverFirst o a) = spec o a := by
  cases o with
  | mk al ne =>
    cases al <;> cases ne <;> first
      | exact absurd ⟨rfl, rfl⟩ wf
      | (cases neverFirst <;>
          (cases a with
           | none => decide
           | some x => cases x <;> decide))

/-! ## Part A.4 — what the back end does with the attribute; mcount parity -/

/-- LLVM's XRay machine pass: `xray-always` instruments unconditionally,
`xray-never` skips the function, and without either the instruction-count /
loop heuristic (abstracted as a boolean) decides. -/
def xraySleds (fi : Option AttrVal) (heuristic : Bool) : Bool :=
  match fi with
  | some .xrayAlways => true
  | some .xrayNever => false
  | _ => heuristic

/-- mcount / fentry selection: `Some(On) | None => true, Some(Off) => false`. -/
def mcountEntry (a : Option InstrumentFnAttr) : Bool :=
  match a with
  | some .off => false
  | _ => true

/-- The excluded function receives sleds, whatever the heuristic says. -/
theorem off_gets_sleds_under_always (o : XRayOptions) (h : o.always = true)
    (heuristic : Bool) :
    xraySleds (finalNeverFirst o (some .off)) heuristic = true := by
  rw [off_overwritten_under_always o h]
  rfl

theorem mcount_off_not_instrumented : mcountEntry (some .off) = false := rfl

/-- XRay honours an explicit attribute exactly like mcount does, except in the
overwrite cell. -/
theorem neverFirst_parity_with_mcount_iff (o : XRayOptions) (x : InstrumentFnAttr)
    (heuristic : Bool) (wf : WellFormed o) :
    xraySleds (finalNeverFirst o (some x)) heuristic = mcountEntry (some x) ↔
      ¬ (o.always = true ∧ x = .off) := by
  cases o with
  | mk al ne =>
    cases al <;> cases ne <;> first
      | exact absurd ⟨rfl, rfl⟩ wf
      | (cases x <;> cases heuristic <;> decide)

/-- With the three-valued mode XRay and mcount agree on every explicit attribute. -/
theorem threeState_parity_with_mcount (cli : XRayMode) (x : InstrumentFnAttr)
    (heuristic : Bool) :
    xraySleds (finalThreeState cli (some x)) heuristic = mcountEntry (some x) := by
  rw [threeState_agrees]
  cases x <;> rfl

/-! ## Part A.5 — a handler that calls an instrumented helper -/

/-- One call of a helper function from inside the XRay handler, with a step
budget. If the helper's entry sled is patched, entering the helper transfers to
the handler, which calls the helper again. `none` means the budget ran out with
the call still in progress; `some n` means it returned after `n` nested handler
activations. Assumptions made by this model: the sleds are patched, the handler
calls the helper on every activation, and the handler has no re-entrancy guard. -/
noncomputable def callHelper (patchedSled : Bool) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if patchedSled then
      match callHelper patchedSled fuel with
      | some n => some (n + 1)
      | none => none
    else some 0

theorem callHelper_patched_never_returns (fuel : Nat) : callHelper true fuel = none := by
  induction fuel with
  | zero => rfl
  | succ n ih => simp [callHelper, ih]

theorem callHelper_unpatched_returns (fuel : Nat) : callHelper false (fuel + 1) = some 0 := by
  simp [callHelper]

/-- Handler nesting depth after `n` steps. -/
noncomputable def handlerDepth (patchedSled : Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if patchedSled then handlerDepth patchedSled n + 1 else 0

theorem handlerDepth_patched (n : Nat) : handlerDepth true n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [handlerDepth, ih]

/-- The nesting depth exceeds every bound. -/
theorem handlerDepth_unbounded (bound : Nat) : ∃ n, bound < handlerDepth true n :=
  ⟨bound + 1, by rw [handlerDepth_patched]; exact Nat.lt_succ_self bound⟩

/-- **Re-entrancy.** Under `-Z instrument-xray=always`, a helper marked
`#[instrument_fn = "off"]` that the handler calls makes the call diverge. -/
theorem handler_reentrancy_diverges (o : XRayOptions) (h : o.always = true)
    (heuristic : Bool) (fuel : Nat) :
    callHelper (xraySleds (finalNeverFirst o (some .off)) heuristic) fuel = none := by
  rw [off_gets_sleds_under_always o h]
  exact callHelper_patched_never_returns fuel

/-- With the three-valued mode the same helper returns immediately. -/
theorem handler_returns_with_three_state (cli : XRayMode) (heuristic : Bool) (fuel : Nat) :
    callHelper (xraySleds (finalThreeState cli (some .off)) heuristic) (fuel + 1) = some 0 := by
  rw [threeState_agrees]
  exact callHelper_unpatched_returns fuel

/-! ## Part B.1 — branch mappings and expansion contexts -/

/-- The kinds of expansion a syntax context can come from. -/
inductive ExpnKind where
  | root
  | macroExpn
  | astPass
  | desugaring
  deriving DecidableEq

/-- A syntax context, reduced to what branch-mapping extraction reads: an
identity and the kind of its outermost expansion. -/
structure Ctxt where
  id : Nat
  kind : ExpnKind
  deriving DecidableEq

/-- A branch span recorded while building MIR: a condition site and the syntax
context of the condition expression's span. -/
structure BranchSpan where
  site : Nat
  ctxt : Ctxt
  deriving DecidableEq

/-- Branch-mapping extraction: nothing at all unless the function body's context
is the root expansion; otherwise exactly the spans bucketed under the body's
context. -/
def extractBranchMappings (body : Ctxt) (spans : List BranchSpan) : List BranchSpan :=
  match body.kind with
  | .root => spans.filter (fun s => s.ctxt = body)
  | _ => []

theorem length_filter_add_length_filter_not {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.filter_cons, List.filter_cons]
    cases p a with
    | false =>
      show (List.filter p t).length + (a :: List.filter (fun x => !p x) t).length
        = (a :: t).length
      rw [List.length_cons, List.length_cons, ← Nat.add_assoc, ih]
    | true =>
      show (a :: List.filter p t).length + (List.filter (fun x => !p x) t).length
        = (a :: t).length
      rw [List.length_cons, List.length_cons, Nat.add_right_comm, ih]

theorem extract_of_root (body : Ctxt) (spans : List BranchSpan) (h : body.kind = .root) :
    extractBranchMappings body spans = spans.filter (fun s => decide (s.ctxt = body)) := by
  unfold extractBranchMappings
  rw [h]

/-- A function whose body span comes from an expansion gets no branch mappings,
whatever was recorded. -/
theorem expansion_body_erases_everything (body : Ctxt) (spans : List BranchSpan)
    (h : body.kind ≠ .root) : extractBranchMappings body spans = [] := by
  unfold extractBranchMappings
  cases hk : body.kind with
  | root => exact absurd hk h
  | macroExpn => rfl
  | astPass => rfl
  | desugaring => rfl

/-- Exact characterisation of what survives. -/
theorem mem_extractBranchMappings (body : Ctxt) (spans : List BranchSpan) (s : BranchSpan) :
    s ∈ extractBranchMappings body spans ↔ body.kind = .root ∧ s ∈ spans ∧ s.ctxt = body := by
  by_cases h : body.kind = .root
  · rw [extract_of_root body spans h, List.mem_filter]
    constructor
    · intro hm
      exact ⟨h, hm.1, of_decide_eq_true hm.2⟩
    · intro hm
      exact ⟨hm.2.1, decide_eq_true hm.2.2⟩
  · rw [expansion_body_erases_everything body spans h]
    constructor
    · intro hm
      cases hm
    · intro hm
      exact absurd hm.1 h

/-- Every emitted branch mapping lies in the root expansion. -/
theorem kept_span_is_root (body : Ctxt) (spans : List BranchSpan) (s : BranchSpan)
    (h : s ∈ extractBranchMappings body spans) : s.ctxt.kind = .root := by
  have hm := (mem_extractBranchMappings body spans s).1 h
  rw [hm.2.2]
  exact hm.1

/-- A condition whose span belongs to an expansion is never reported. -/
theorem expansion_span_erased (body : Ctxt) (spans : List BranchSpan) (s : BranchSpan)
    (h : s.ctxt.kind ≠ .root) : s ∉ extractBranchMappings body spans :=
  fun hm => h (kept_span_is_root body spans s hm)

/-- A condition whose span is in the (root) body context is reported unchanged. -/
theorem body_context_span_kept (body : Ctxt) (spans : List BranchSpan) (s : BranchSpan)
    (hroot : body.kind = .root) (hs : s ∈ spans) (hc : s.ctxt = body) :
    s ∈ extractBranchMappings body spans :=
  (mem_extractBranchMappings body spans s).2 ⟨hroot, hs, hc⟩

/-- Loss accounting for a root body: reported plus foreign-context spans is
everything that was recorded. -/
theorem erasure_accounting (body : Ctxt) (spans : List BranchSpan)
    (hroot : body.kind = .root) :
    (extractBranchMappings body spans).length
      + (spans.filter (fun s => !decide (s.ctxt = body))).length = spans.length := by
  rw [extract_of_root body spans hroot]
  exact length_filter_add_length_filter_not (fun s => decide (s.ctxt = body)) spans

/-- The projection never invents or duplicates a span. -/
theorem extract_length_le (body : Ctxt) (spans : List BranchSpan) :
    (extractBranchMappings body spans).length ≤ spans.length := by
  by_cases h : body.kind = .root
  · rw [extract_of_root body spans h]
    exact List.length_filter_le _ _
  · rw [expansion_body_erases_everything body spans h]
    exact Nat.zero_le _

/-- The root context and one macro expansion context. -/
def rootCtxt : Ctxt := ⟨0, .root⟩
def macroCtxt : Ctxt := ⟨1, .macroExpn⟩

/-- Probe case: `if` written in a macro body, used inside an ordinary function. -/
theorem probe_def_site_condition_erased :
    extractBranchMappings rootCtxt [⟨7, macroCtxt⟩] = [] := by decide

/-- Probe case: condition tokens written at the macro call site. -/
theorem probe_call_site_condition_kept :
    extractBranchMappings rootCtxt [⟨7, rootCtxt⟩] = [⟨7, rootCtxt⟩] := by decide

/-- Probe case: the whole function, body included, produced by a macro. -/
theorem probe_macro_generated_fn_erased :
    extractBranchMappings macroCtxt [⟨7, macroCtxt⟩] = [] := by decide

/-- Probe case: function item produced by a macro, body block written at the call site. -/
theorem probe_call_site_body_kept :
    extractBranchMappings rootCtxt [⟨7, rootCtxt⟩, ⟨8, macroCtxt⟩] = [⟨7, rootCtxt⟩] := by
  decide

/-! ## Part B.2 — `!` chains and marker polarity -/

/-- `NotInfo { enclosing_not, is_flipped }`. In the chain `!^k e`, an expression
is identified by the number of `!` operators at or below it: `k` is the
outermost `!`, `0` is `e` itself. -/
structure NotInfo where
  enclosingNot : Nat
  isFlipped : Bool
  deriving DecidableEq

/-- The `nots` map. -/
abbrev NotTable := List (Nat × NotInfo)

/-- `visit_with_not_info`: return at once if the expression already has an entry
(`Entry::Occupied`); otherwise insert, and if the expression is a `!` descend
into its operand with `is_flipped` inverted. -/
noncomputable def visitWithNotInfo (t : NotTable) (info : NotInfo) : Nat → NotTable
  | 0 =>
    match getAttr t 0 with
    | some _ => t
    | none => (0, info) :: t
  | e + 1 =>
    match getAttr t (e + 1) with
    | some _ => t
    | none => visitWithNotInfo ((e + 1, info) :: t) ⟨info.enclosingNot, !info.isFlipped⟩ e

/-- `visit_unary_not` on the `!` identified by `e + 1`: the `!` itself is entered
with `is_flipped: false`. -/
noncomputable def visitUnaryNot (t : NotTable) (e : Nat) : NotTable :=
  visitWithNotInfo t ⟨e + 1, false⟩ (e + 1)

/-- Lowering `!^k e` as a condition visits each `!`, outermost first. -/
noncomputable def lowerNots (t : NotTable) : Nat → NotTable
  | 0 => t
  | e + 1 => lowerNots (visitUnaryNot t e) e

/-- Parity of the number of `!` operators. -/
noncomputable def parity : Nat → Bool
  | 0 => false
  | n + 1 => !parity n

theorem getAttr_cons_of_vacant (t : NotTable) (k j : Nat) (x v : NotInfo)
    (hk : getAttr t k = none) (hj : getAttr t j = some v) :
    getAttr ((k, x) :: t) j = some v := by
  by_cases h : k = j
  · subst h
    rw [hk] at hj
    cases hj
  · simp [getAttr, h, hj]

/-- A visit never removes or overwrites an existing entry. -/
theorem visit_preserves (e : Nat) (t : NotTable) (info : NotInfo) (j : Nat) (v : NotInfo)
    (hj : getAttr t j = some v) : getAttr (visitWithNotInfo t info e) j = some v := by
  induction e generalizing t info with
  | zero =>
    unfold visitWithNotInfo
    cases h0 : getAttr t 0 with
    | some w => exact hj
    | none => exact getAttr_cons_of_vacant t 0 j info v h0 hj
  | succ e ih =>
    unfold visitWithNotInfo
    cases h1 : getAttr t (e + 1) with
    | some w => exact hj
    | none => exact ih _ _ (getAttr_cons_of_vacant t (e + 1) j info v h1 hj)

/-- A visit that starts above vacant entries records, for the innermost
expression, the starting `enclosing_not` and a flag inverted once per `!`. -/
theorem visit_fills_leaf (e : Nat) (t : NotTable) (info : NotInfo)
    (hv : ∀ j, j ≤ e → getAttr t j = none) :
    getAttr (visitWithNotInfo t info e) 0
      = some ⟨info.enclosingNot, Bool.xor info.isFlipped (parity e)⟩ := by
  induction e generalizing t info with
  | zero =>
    unfold visitWithNotInfo
    rw [hv 0 (Nat.le_refl 0)]
    cases info with
    | mk enc fl => cases fl <;> rfl
  | succ e ih =>
    unfold visitWithNotInfo
    rw [hv (e + 1) (Nat.le_refl (e + 1))]
    have hv' : ∀ j, j ≤ e → getAttr ((e + 1, info) :: t) j = none := by
      intro j hj
      have hne : ¬ (e + 1 = j) := by
        intro heq
        subst heq
        exact Nat.not_succ_le_self e hj
      simp [getAttr, hne, hv j (Nat.le_succ_of_le hj)]
    rw [ih _ _ hv']
    cases info with
    | mk enc fl =>
      show some (NotInfo.mk enc (Bool.xor (!fl) (parity e)))
        = some (NotInfo.mk enc (Bool.xor fl (!parity e)))
      cases fl <;> cases parity e <;> rfl

theorem lower_preserves (e : Nat) (t : NotTable) (v : NotInfo)
    (h : getAttr t 0 = some v) : getAttr (lowerNots t e) 0 = some v := by
  induction e generalizing t with
  | zero => exact h
  | succ e ih =>
    unfold lowerNots
    exact ih _ (visit_preserves (e + 1) t _ 0 v h)

/-- After lowering `!^(k+1) e`, the entry for `e` names the outermost `!` and is
flipped exactly when the number of `!` is odd; later visits of the inner `!`
operators find their entries occupied and change nothing. -/
theorem leaf_notInfo (k : Nat) :
    getAttr (lowerNots [] (k + 1)) 0 = some ⟨k + 1, parity (k + 1)⟩ := by
  unfold lowerNots
  apply lower_preserves
  unfold visitUnaryNot
  rw [visit_fills_leaf (k + 1) [] ⟨k + 1, false⟩ (fun _ _ => rfl)]
  cases parity (k + 1) <;> rfl

/-- Without any `!` there is no entry. -/
theorem leaf_notInfo_zero : getAttr (lowerNots [] 0) 0 = none := rfl

/-- The two successors of the innermost condition's branch. -/
inductive Arm where
  | whenLeafTrue
  | whenLeafFalse
  deriving DecidableEq

/-- Branch-condition registration: the true marker goes to the innermost
condition's true block, unless the entry says `is_flipped`, in which case the
two blocks are swapped first. -/
def trueMarkerArm (info : Option NotInfo) : Arm :=
  match info with
  | some ⟨_, true⟩ => .whenLeafFalse
  | _ => .whenLeafTrue

/-- The arm executed for a given value of the innermost condition. -/
def armTaken (leaf : Bool) : Arm := if leaf then .whenLeafTrue else .whenLeafFalse

/-- Source-level value of `!^k e`. -/
noncomputable def evalNots : Nat → Bool → Bool
  | 0, v => v
  | k + 1, v => !evalNots k v

theorem evalNots_eq (k : Nat) (v : Bool) : evalNots k v = Bool.xor v (parity k) := by
  induction k with
  | zero => cases v <;> rfl
  | succ k ih =>
    show (!evalNots k v) = Bool.xor v (!parity k)
    rw [ih]
    cases v <;> cases parity k <;> rfl

/-- **Polarity.** The true marker is executed exactly when the source expression
`!^k e` evaluates to true, for every `k`. -/
theorem true_marker_hit (k : Nat) (leaf : Bool) :
    decide (trueMarkerArm (getAttr (lowerNots [] k) 0) = armTaken leaf) = evalNots k leaf := by
  cases k with
  | zero =>
    rw [leaf_notInfo_zero]
    cases leaf <;> rfl
  | succ k =>
    rw [leaf_notInfo, evalNots_eq]
    cases leaf <;> cases parity (k + 1) <;> rfl

theorem true_marker_hit_iff (k : Nat) (leaf : Bool) :
    trueMarkerArm (getAttr (lowerNots [] k) 0) = armTaken leaf ↔ evalNots k leaf = true := by
  rw [← true_marker_hit]
  exact ⟨decide_eq_true, of_decide_eq_true⟩

/-- `true_count` and `false_count` reported for the `!^k e` span over a list of
runs, each run given by the value of `e`. -/
noncomputable def trueCount (k : Nat) (leaves : List Bool) : Nat :=
  (leaves.filter
    (fun v => decide (trueMarkerArm (getAttr (lowerNots [] k) 0) = armTaken v))).length

noncomputable def falseCount (k : Nat) (leaves : List Bool) : Nat :=
  (leaves.filter
    (fun v => !decide (trueMarkerArm (getAttr (lowerNots [] k) 0) = armTaken v))).length

/-- The reported counts are the source truth counts of `!^k e`. -/
theorem trueCount_eq (k : Nat) (leaves : List Bool) :
    trueCount k leaves = (leaves.filter (fun v => evalNots k v)).length := by
  unfold trueCount
  exact congrArg List.length (List.filter_congr (fun v _ => true_marker_hit k v))

theorem falseCount_eq (k : Nat) (leaves : List Bool) :
    falseCount k leaves = (leaves.filter (fun v => !evalNots k v)).length := by
  unfold falseCount
  exact congrArg List.length
    (List.filter_congr (fun v _ => congrArg (fun b => !b) (true_marker_hit k v)))

theorem counts_partition (k : Nat) (leaves : List Bool) :
    trueCount k leaves + falseCount k leaves = leaves.length := by
  unfold trueCount falseCount
  exact length_filter_add_length_filter_not _ leaves

/-- Without the `is_flipped` swap the true marker would always sit in the
innermost condition's true block; for an odd number of `!` the reported true
count would then be the source false count. -/
theorem uncompensated_counts_are_swapped (k : Nat) (leaves : List Bool)
    (hodd : parity k = true) :
    (leaves.filter (fun v => decide (Arm.whenLeafTrue = armTaken v))).length
      = (leaves.filter (fun v => !evalNots k v)).length := by
  apply congrArg List.length
  apply List.filter_congr
  intro v _
  rw [evalNots_eq, hodd]
  cases v <;> rfl

/-- Two more `!` change nothing: the bookkeeping is an involution. -/
theorem parity_add_two (k : Nat) : parity (k + 2) = parity k := by
  show (!(!parity k)) = parity k
  cases parity k <;> rfl

theorem evalNots_add_two (k : Nat) (v : Bool) : evalNots (k + 2) v = evalNots k v := by
  show (!(!evalNots k v)) = evalNots k v
  cases evalNots k v <;> rfl

/-- Probe runs. `!(x > 100)` with `x = 1, 2, 3, 4, 200`. -/
theorem probe_not_once :
    (trueCount 1 [false, false, false, false, true],
     falseCount 1 [false, false, false, false, true]) = (4, 1) := by decide

/-- `!!(y < 50)` with `y = 10, 20, 60, 70, 80`. -/
theorem probe_not_twice :
    (trueCount 2 [true, true, false, false, false],
     falseCount 2 [true, true, false, false, false]) = (2, 3) := by decide

/-- `!!!(z == 0)` with `z = 0, 0, 0, 0, 5`. -/
theorem probe_not_thrice :
    (trueCount 3 [true, true, true, true, false],
     falseCount 3 [true, true, true, true, false]) = (1, 4) := by decide

/-! ## Part B.3 — the condition-level diamond -/

/-- Blocks of the diamond built around an already computed boolean. -/
inductive DBlock where
  | entry
  | trueBlock
  | falseBlock
  | join
  deriving DecidableEq

/-- Blocks executed by one run in which the boolean has value `v`. -/
def diamondPath (v : Bool) : List DBlock :=
  [.entry, if v then .trueBlock else .falseBlock, .join]

/-- Execution count of a block over a list of runs. -/
noncomputable def visits (b : DBlock) : List Bool → Nat
  | [] => 0
  | v :: vs => (diamondPath v).count b + visits b vs

/-- **Flow conservation.** `true_count + false_count = entry_count`. -/
theorem diamond_conserves (vs : List Bool) :
    visits .trueBlock vs + visits .falseBlock vs = visits .entry vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show ((diamondPath v).count .trueBlock + visits .trueBlock vs)
        + ((diamondPath v).count .falseBlock + visits .falseBlock vs)
      = (diamondPath v).count .entry + visits .entry vs
    rw [Nat.add_add_add_comm, ih]
    cases v <;> rfl

/-- Every run that enters the diamond leaves through the join block. -/
theorem diamond_join (vs : List Bool) : visits .join vs = visits .entry vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show (diamondPath v).count .join + visits .join vs
      = (diamondPath v).count .entry + visits .entry vs
    rw [ih]
    cases v <;> rfl

theorem diamond_entry (vs : List Bool) : visits .entry vs = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show (diamondPath v).count .entry + visits .entry vs = vs.length + 1
    rw [ih, Nat.add_comm]
    cases v <;> rfl

/-- Runs of the right operand of `l && r`: only those where `l` was true. -/
def rhsRunsAnd (runs : List (Bool × Bool)) : List Bool :=
  (runs.filter (fun r => r.1)).map (fun r => r.2)

/-- Runs of the right operand of `l || r`: only those where `l` was false. -/
def rhsRunsOr (runs : List (Bool × Bool)) : List Bool :=
  (runs.filter (fun r => !r.1)).map (fun r => r.2)

/-- The right operand's two counts add up to the left operand's true count. -/
theorem and_rhs_flow (runs : List (Bool × Bool)) :
    visits .trueBlock (rhsRunsAnd runs) + visits .falseBlock (rhsRunsAnd runs)
      = (runs.filter (fun r => r.1)).length := by
  rw [diamond_conserves, diamond_entry]
  exact List.length_map _

/-- The right operand's two counts add up to the left operand's false count. -/
theorem or_rhs_flow (runs : List (Bool × Bool)) :
    visits .trueBlock (rhsRunsOr runs) + visits .falseBlock (rhsRunsOr runs)
      = (runs.filter (fun r => !r.1)).length := by
  rw [diamond_conserves, diamond_entry]
  exact List.length_map _

/-- Probe runs of `(x > 10) && (y < 50)` on
`(20,10) (20,60) (5,10) (200,3) (20,0) (0,0)`: right operand 3 true, 1 false,
left operand true 4 times. -/
theorem probe_and_rhs :
    (visits .trueBlock (rhsRunsAnd
        [(true, true), (true, false), (false, true), (true, true), (true, true), (false, true)]),
     visits .falseBlock (rhsRunsAnd
        [(true, true), (true, false), (false, true), (true, true), (true, true), (false, true)]))
      = (3, 1) := by decide

/-! ### Branch spans per coverage level -/

/-- `-Z coverage-options` levels. -/
inductive CoverageLevel where
  | block
  | branch
  | condition
  deriving DecidableEq

/-- Shapes of boolean expressions: opaque atoms, `!`, `&&`, `||`. -/
inductive BExp where
  | atom
  | not (e : BExp)
  | and (l r : BExp)
  | or (l r : BExp)

/-- Is the expression a lazy boolean operator? -/
def BExp.isLazy : BExp → Bool
  | .and _ _ => true
  | .or _ _ => true
  | _ => false

/-- Two-way branches registered when the expression is lowered as an `if`
condition at branch level or above: one per innermost condition. -/
noncomputable def condBranches : BExp → Nat
  | .atom => 1
  | .not e => condBranches e
  | .and l r => condBranches l + condBranches r
  | .or l r => condBranches l + condBranches r

/-- Two-way branches registered when the expression is lowered as a value into
a destination. The left operand of a lazy operator is lowered as a condition;
the right operand is lowered as a value and, at condition level, wrapped in a
diamond unless it is itself a lazy operator. -/
noncomputable def valueBranches (conditionLevel : Bool) : BExp → Nat
  | .atom => 0
  | .not e => valueBranches conditionLevel e
  | .and l r =>
    condBranches l + valueBranches conditionLevel r
      + (if conditionLevel && !r.isLazy then 1 else 0)
  | .or l r =>
    condBranches l + valueBranches conditionLevel r
      + (if conditionLevel && !r.isLazy then 1 else 0)

/-- Number of diamonds synthesised at condition level. -/
noncomputable def standaloneDiamonds : BExp → Nat
  | .atom => 0
  | .not e => standaloneDiamonds e
  | .and _ r => standaloneDiamonds r + (if r.isLazy then 0 else 1)
  | .or _ r => standaloneDiamonds r + (if r.isLazy then 0 else 1)

/-- Branch spans of a value expression at a level. -/
noncomputable def branchSpans (lvl : CoverageLevel) (e : BExp) : Nat :=
  match lvl with
  | .block => 0
  | .branch => valueBranches false e
  | .condition => valueBranches true e

/-- Condition level adds exactly one branch span per synthesised diamond. -/
theorem condition_adds_diamonds (e : BExp) :
    valueBranches true e = valueBranches false e + standaloneDiamonds e := by
  induction e with
  | atom => rfl
  | not e ih => exact ih
  | and l r _ ihr =>
    show condBranches l + valueBranches true r + (if true && !r.isLazy then 1 else 0)
      = condBranches l + valueBranches false r + (if false && !r.isLazy then 1 else 0)
        + (standaloneDiamonds r + (if r.isLazy then 0 else 1))
    rw [ihr]
    cases r.isLazy <;> simp [Nat.add_assoc]
  | or l r _ ihr =>
    show condBranches l + valueBranches true r + (if true && !r.isLazy then 1 else 0)
      = condBranches l + valueBranches false r + (if false && !r.isLazy then 1 else 0)
        + (standaloneDiamonds r + (if r.isLazy then 0 else 1))
    rw [ihr]
    cases r.isLazy <;> simp [Nat.add_assoc]

theorem branchSpans_condition (e : BExp) :
    branchSpans .condition e = branchSpans .branch e + standaloneDiamonds e :=
  condition_adds_diamonds e

theorem branchSpans_monotone (e : BExp) :
    branchSpans .block e ≤ branchSpans .branch e ∧
    branchSpans .branch e ≤ branchSpans .condition e :=
  ⟨Nat.zero_le _, by rw [branchSpans_condition]; exact Nat.le_add_right _ _⟩

/-- The four `let` initialisers of the probe function, in source order:
`(x > 10) && (y < 50)`, `x > 10`, `(x > 100) || (y < 5)`,
`(x > 1) && ((y > 1) || (x > 2))`. -/
def probeInitialisers : List BExp :=
  [.and .atom .atom, .atom, .or .atom .atom, .and .atom (.or .atom .atom)]

/-- Branch spans per level for the probe function: 0, 4 and 7. -/
theorem probe_branch_spans :
    (probeInitialisers.map (branchSpans .block),
     probeInitialisers.map (branchSpans .branch),
     probeInitialisers.map (branchSpans .condition))
      = ([0, 0, 0, 0], [1, 0, 1, 2], [2, 0, 2, 3]) := by decide

/-- Three diamonds, hence three extra `switchInt` terminators and nine extra
basic blocks (true, false and join block each) in built MIR. -/
theorem probe_diamonds :
    probeInitialisers.map standaloneDiamonds = [1, 0, 1, 1] := by decide

end XrayCov

/-! ## Axiom report (printed when this file is checked) -/

#print axioms XrayCov.getAttr_addAttr_same
#print axioms XrayCov.getAttr_addAttr_other
#print axioms XrayCov.getAttr_addAll
#print axioms XrayCov.parse_wellFormed
#print axioms XrayCov.finalNeverFirst_eq
#print axioms XrayCov.finalAlwaysFirst_eq
#print axioms XrayCov.off_overwritten_under_always
#print axioms XrayCov.on_survives_never_first
#print axioms XrayCov.on_lost_always_first
#print axioms XrayCov.neverFirst_agrees_iff
#print axioms XrayCov.alwaysFirst_agrees_iff
#print axioms XrayCov.no_push_order_implements_override
#print axioms XrayCov.table_neverFirst
#print axioms XrayCov.table_alwaysFirst
#print axioms XrayCov.threeState_agrees
#print axioms XrayCov.threeState_at_most_one_push
#print axioms XrayCov.resolve_idempotent
#print axioms XrayCov.resolve_override
#print axioms XrayCov.fixedPair_exclusive
#print axioms XrayCov.fixed_agrees
#print axioms XrayCov.off_gets_sleds_under_always
#print axioms XrayCov.neverFirst_parity_with_mcount_iff
#print axioms XrayCov.threeState_parity_with_mcount
#print axioms XrayCov.callHelper_patched_never_returns
#print axioms XrayCov.handlerDepth_unbounded
#print axioms XrayCov.handler_reentrancy_diverges
#print axioms XrayCov.handler_returns_with_three_state
#print axioms XrayCov.expansion_body_erases_everything
#print axioms XrayCov.mem_extractBranchMappings
#print axioms XrayCov.kept_span_is_root
#print axioms XrayCov.expansion_span_erased
#print axioms XrayCov.body_context_span_kept
#print axioms XrayCov.erasure_accounting
#print axioms XrayCov.extract_length_le
#print axioms XrayCov.probe_def_site_condition_erased
#print axioms XrayCov.probe_call_site_condition_kept
#print axioms XrayCov.probe_macro_generated_fn_erased
#print axioms XrayCov.probe_call_site_body_kept
#print axioms XrayCov.visit_preserves
#print axioms XrayCov.visit_fills_leaf
#print axioms XrayCov.leaf_notInfo
#print axioms XrayCov.true_marker_hit
#print axioms XrayCov.true_marker_hit_iff
#print axioms XrayCov.trueCount_eq
#print axioms XrayCov.falseCount_eq
#print axioms XrayCov.counts_partition
#print axioms XrayCov.uncompensated_counts_are_swapped
#print axioms XrayCov.parity_add_two
#print axioms XrayCov.evalNots_add_two
#print axioms XrayCov.probe_not_once
#print axioms XrayCov.probe_not_twice
#print axioms XrayCov.probe_not_thrice
#print axioms XrayCov.diamond_conserves
#print axioms XrayCov.diamond_join
#print axioms XrayCov.diamond_entry
#print axioms XrayCov.and_rhs_flow
#print axioms XrayCov.or_rhs_flow
#print axioms XrayCov.probe_and_rhs
#print axioms XrayCov.condition_adds_diamonds
#print axioms XrayCov.branchSpans_condition
#print axioms XrayCov.branchSpans_monotone
#print axioms XrayCov.probe_branch_spans
#print axioms XrayCov.probe_diamonds
