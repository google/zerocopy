/-
  Tail-call frame reuse, pre-jump drop order, call-site inlining, and
  backreference-compressed type mangling.

  Self-contained: only the Lean core prelude is used (no imports).

  Part A  A frame-stack machine with ordinary calls (`call`: push a frame) and
          explicit tail calls (`tailcall`: replace the active frame).
  Part B  Three manglers for binary type trees: naive tree serialization, a
          fixed-width digest, and a memoized backreference encoding with a decoder.

  The machine and the manglers are abstract models written for this development.
  They are not rustc's MIR semantics and not rustc's symbol mangler; each section
  header states what is modelled and what is abstracted away.
-/

set_option autoImplicit false

namespace TailCallMangle

/-! ## Generic list helpers (kept local so that no library lemma about `Nodup`,
`erase`, or `flatten` is relied upon) -/

/-- No element occurs twice. -/
noncomputable def Distinct {α : Type} : List α → Prop
  | [] => True
  | a :: l => a ∉ l ∧ Distinct l

/-- Remove the first occurrence of `a`. -/
noncomputable def removeFirst {α : Type} [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | x :: xs => if x = a then xs else x :: removeFirst a xs

theorem length_removeFirst {α : Type} [DecidableEq α] (a : α) :
    ∀ (m : List α), a ∈ m → (removeFirst a m).length + 1 = m.length
  | [], h => by cases h
  | x :: xs, h => by
    unfold removeFirst
    split
    · rfl
    · rename_i hne
      cases h with
      | head => exact absurd rfl hne
      | tail _ h' =>
        show (removeFirst a xs).length + 1 + 1 = xs.length + 1
        rw [length_removeFirst a xs h']

theorem mem_removeFirst {α : Type} [DecidableEq α] (a x : α) (hne : x ≠ a) :
    ∀ (m : List α), x ∈ m → x ∈ removeFirst a m
  | [], h => by cases h
  | y :: ys, h => by
    unfold removeFirst
    split
    · rename_i hy
      cases h with
      | head => exact absurd hy hne
      | tail _ h' => exact h'
    · cases h with
      | head => exact List.Mem.head _
      | tail _ h' => exact List.Mem.tail _ (mem_removeFirst a x hne ys h')

/-- A duplicate-free list whose elements all lie in `m` is no longer than `m`. -/
theorem distinct_length_le {α : Type} [DecidableEq α] :
    ∀ (l m : List α), Distinct l → (∀ x, x ∈ l → x ∈ m) → l.length ≤ m.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, m, hd, hsub => by
    have ha : a ∈ m := hsub a (List.Mem.head _)
    have hsub' : ∀ x, x ∈ l → x ∈ removeFirst a m := fun x hx =>
      mem_removeFirst a x (fun e => hd.1 (by rw [← e]; exact hx)) m
        (hsub x (List.Mem.tail _ hx))
    have ih := distinct_length_le l (removeFirst a m) hd.2 hsub'
    rw [← length_removeFirst a m ha]
    exact Nat.succ_le_succ ih

theorem distinct_append {α : Type} : ∀ (a b : List α),
    Distinct a → Distinct b → (∀ x, x ∈ a → x ∉ b) → Distinct (a ++ b)
  | [], _, _, hb, _ => hb
  | x :: a, b, ha, hb, hab => by
    refine ⟨?_, distinct_append a b ha.2 hb (fun y hy => hab y (List.Mem.tail _ hy))⟩
    intro hx
    cases List.mem_append.mp hx with
    | inl h => exact ha.1 h
    | inr h => exact hab x (List.Mem.head _) h

/-! ## Part A — frame-stack machine

A function body is a list of statements. A frame holds the statements still to be
executed by one activation, a unique activation id, and at most one pointer
argument (the id of the activation whose stack memory it points into).

* `call f` pushes a frame for `f` on top of the caller's frame.
* `tailcall f` discards the caller's frame and puts a frame for `f` in its place;
  whatever followed the `tailcall` in the caller is never executed.
* `useRef` dereferences the pointer argument; this is undefined behaviour
  (`none`) when the pointee activation is no longer on the stack.

Abstracted away: values, branching, unwinding, argument passing other than the
single optional pointer, and the contents of stack memory. -/

inductive Event where
  | emit (n : Nat)
  | drop (r : Nat)
  deriving DecidableEq

inductive Stmt where
  | eff (e : Event)
  | call (f : Nat) (byRef : Bool)
  | tailcall (f : Nat) (byRef : Bool)
  | useRef
  | ret
  deriving DecidableEq

structure Frame where
  id : Nat
  code : List Stmt
  ref : Option Nat
  deriving DecidableEq

structure State where
  stack : List Frame
  next : Nat
  trace : List Event
  deriving DecidableEq

abbrev Prog := Nat → List Stmt

/-- The pointer argument handed to a callee: a pointer into the caller's frame, or none. -/
noncomputable def refArg (byRef : Bool) (callerId : Nat) : Option Nat :=
  match byRef with
  | true => some callerId
  | false => none

noncomputable def stepFrame (P : Prog) (fr : Frame) (rest : List Frame) (nx : Nat) (tr : List Event) :
    Option State :=
  match fr.code with
  | [] => some ⟨rest, nx, tr⟩
  | .ret :: _ => some ⟨rest, nx, tr⟩
  | .eff e :: k => some ⟨⟨fr.id, k, fr.ref⟩ :: rest, nx, tr ++ [e]⟩
  | .call f b :: k =>
      some ⟨⟨nx, P f, refArg b fr.id⟩ :: ⟨fr.id, k, fr.ref⟩ :: rest, nx + 1, tr⟩
  | .tailcall f b :: _ => some ⟨⟨nx, P f, refArg b fr.id⟩ :: rest, nx + 1, tr⟩
  | .useRef :: k =>
      match fr.ref with
      | none => some ⟨⟨fr.id, k, none⟩ :: rest, nx, tr⟩
      | some p =>
          if p ∈ fr.id :: rest.map Frame.id then some ⟨⟨fr.id, k, some p⟩ :: rest, nx, tr⟩
          else none

/-- One machine step. `none` is undefined behaviour; an empty stack is a fixed point. -/
noncomputable def step (P : Prog) (s : State) : Option State :=
  match s.stack with
  | [] => some s
  | fr :: rest => stepFrame P fr rest s.next s.trace

noncomputable def run (P : Prog) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => (step P s).bind (run P n)

section StepEquations
variable (P : Prog) (i : Nat) (k : List Stmt) (r : Option Nat) (rest : List Frame) (nx : Nat)
  (tr : List Event)

theorem step_eff (e : Event) :
    step P ⟨⟨i, .eff e :: k, r⟩ :: rest, nx, tr⟩ = some ⟨⟨i, k, r⟩ :: rest, nx, tr ++ [e]⟩ := rfl

theorem step_call (f : Nat) (b : Bool) :
    step P ⟨⟨i, .call f b :: k, r⟩ :: rest, nx, tr⟩
      = some ⟨⟨nx, P f, refArg b i⟩ :: ⟨i, k, r⟩ :: rest, nx + 1, tr⟩ := rfl

theorem step_tailcall (f : Nat) (b : Bool) :
    step P ⟨⟨i, .tailcall f b :: k, r⟩ :: rest, nx, tr⟩
      = some ⟨⟨nx, P f, refArg b i⟩ :: rest, nx + 1, tr⟩ := rfl

theorem step_useRef_some (p : Nat) :
    step P ⟨⟨i, .useRef :: k, some p⟩ :: rest, nx, tr⟩
      = if p ∈ i :: rest.map Frame.id then some ⟨⟨i, k, some p⟩ :: rest, nx, tr⟩ else none := rfl

end StepEquations

theorem run_succ (P : Prog) (n : Nat) (s : State) :
    run P (n + 1) s = (step P s).bind (run P n) := rfl

theorem run_add (P : Prog) (m n : Nat) (s : State) :
    run P (m + n) s = (run P m s).bind (run P n) := by
  induction m generalizing s with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
    rw [Nat.add_right_comm, run_succ, run_succ]
    cases h : step P s with
    | none => rfl
    | some s1 => exact ih s1

theorem run_halted (P : Prog) (n nx : Nat) (tr : List Event) :
    run P n ⟨[], nx, tr⟩ = some ⟨[], nx, tr⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ]; exact ih

/-- A straight-line block of observable statements. -/
noncomputable def effs (es : List Event) : List Stmt := es.map Stmt.eff

theorem run_effs (P : Prog) (es : List Event) (k : List Stmt) (i : Nat) (r : Option Nat)
    (rest : List Frame) (nx : Nat) (tr : List Event) :
    run P es.length ⟨⟨i, effs es ++ k, r⟩ :: rest, nx, tr⟩
      = some ⟨⟨i, k, r⟩ :: rest, nx, tr ++ es⟩ := by
  induction es generalizing tr with
  | nil => rw [List.append_nil]; rfl
  | cons e es ih =>
    show run P (es.length + 1) ⟨⟨i, Stmt.eff e :: (effs es ++ k), r⟩ :: rest, nx, tr⟩ = _
    rw [run_succ, step_eff]
    show run P es.length ⟨⟨i, effs es ++ k, r⟩ :: rest, nx, tr ++ [e]⟩ = _
    rw [ih, List.append_assoc]
    rfl

/-! ### A.1  Lowering of `become` and the pre-jump drop order

`Scopes` lists the droppable variables that are live at a `become`: the by-value
parameters (the outermost scope) and the enclosing block scopes, outermost first,
each in declaration order. `lowerBecome` mirrors the shape of the MIR-building
routine: walk the scopes innermost-first, emit the still-owned variables of each
scope in reverse declaration order, then emit the tail call. `lifoDrops` is the
specification: all still-owned variables in reverse declaration order. -/

noncomputable def flat : List (List Nat) → List Nat
  | [] => []
  | s :: ss => s ++ flat ss

theorem flat_append (a b : List (List Nat)) : flat (a ++ b) = flat a ++ flat b := by
  induction a with
  | nil => rfl
  | cons s ss ih =>
    show s ++ flat (ss ++ b) = (s ++ flat ss) ++ flat b
    rw [ih, List.append_assoc]

structure Scopes where
  params : List Nat
  blocks : List (List Nat)

noncomputable def Scopes.declOrder (sc : Scopes) : List Nat := sc.params ++ flat sc.blocks

/-- `r` has not been moved into the callee's arguments. -/
noncomputable def owned (moved : List Nat) (r : Nat) : Bool := !moved.contains r

noncomputable def lifoDrops (sc : Scopes) (moved : List Nat) : List Nat :=
  (sc.declOrder.reverse).filter (owned moved)

noncomputable def scopeWalk (moved : List Nat) : List (List Nat) → List Nat
  | [] => []
  | s :: ss => (s.reverse).filter (owned moved) ++ scopeWalk moved ss

noncomputable def lowerBecome (sc : Scopes) (moved : List Nat) (f : Nat) (byRef : Bool) : List Stmt :=
  effs ((scopeWalk moved (sc.blocks.reverse ++ [sc.params])).map Event.drop)
    ++ [Stmt.tailcall f byRef]

theorem scopeWalk_eq (moved : List Nat) (ss : List (List Nat)) :
    scopeWalk moved ss = (flat (ss.map List.reverse)).filter (owned moved) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show (s.reverse).filter (owned moved) ++ scopeWalk moved ss
        = (s.reverse ++ flat (ss.map List.reverse)).filter (owned moved)
    rw [ih, List.filter_append]

theorem flat_reverse_map_reverse (bs : List (List Nat)) :
    flat (bs.reverse.map List.reverse) = (flat bs).reverse := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show flat ((b :: bs).reverse.map List.reverse) = (b ++ flat bs).reverse
    rw [List.reverse_cons, List.map_append, flat_append, ih, List.reverse_append]
    show (flat bs).reverse ++ (b.reverse ++ []) = (flat bs).reverse ++ b.reverse
    rw [List.append_nil]

/-- Walking scopes innermost-first is the same as one global reverse-declaration-order pass. -/
theorem scopeWalk_eq_lifo (sc : Scopes) (moved : List Nat) :
    scopeWalk moved (sc.blocks.reverse ++ [sc.params]) = lifoDrops sc moved := by
  rw [scopeWalk_eq, List.map_append, flat_append, flat_reverse_map_reverse]
  show ((flat sc.blocks).reverse ++ (sc.params.reverse ++ [])).filter (owned moved)
      = ((sc.params ++ flat sc.blocks).reverse).filter (owned moved)
  rw [List.append_nil, List.reverse_append]

/-- **Theorem 1 (frame reuse and pre-jump drop order).**
Executing the lowering of `become f(..)` from any state takes exactly
`(number of drops) + 1` steps and ends in a state where

* the callee's frame sits where the caller's frame was (the frames below are untouched,
  so the stack depth is unchanged),
* the trace has been extended by exactly the caller's still-owned variables in reverse
  declaration order, and
* the callee has not executed anything yet (its frame holds its whole body), so every
  one of those drops precedes every effect of the callee.

Statements following the tail call in the caller (`junk`) play no role. -/
theorem become_frame_reuse_and_lifo_drops (P : Prog) (sc : Scopes) (moved : List Nat) (f : Nat)
    (byRef : Bool) (junk : List Stmt) (i : Nat) (r : Option Nat) (rest : List Frame) (nx : Nat)
    (tr : List Event) :
    run P ((lifoDrops sc moved).length + 1)
        ⟨⟨i, lowerBecome sc moved f byRef ++ junk, r⟩ :: rest, nx, tr⟩
      = some ⟨⟨nx, P f, refArg byRef i⟩ :: rest, nx + 1,
              tr ++ (lifoDrops sc moved).map Event.drop⟩ := by
  unfold lowerBecome
  rw [scopeWalk_eq_lifo, List.append_assoc, run_add]
  have h := run_effs P ((lifoDrops sc moved).map Event.drop)
    ([Stmt.tailcall f byRef] ++ junk) i r rest nx tr
  rw [List.length_map] at h
  rw [h]
  rfl

/-- Depth corollary of Theorem 1. -/
theorem become_preserves_depth (P : Prog) (sc : Scopes) (moved : List Nat) (f : Nat)
    (byRef : Bool) (junk : List Stmt) (i : Nat) (r : Option Nat) (rest : List Frame) (nx : Nat)
    (tr : List Event) :
    ∃ s', run P ((lifoDrops sc moved).length + 1)
            ⟨⟨i, lowerBecome sc moved f byRef ++ junk, r⟩ :: rest, nx, tr⟩ = some s'
      ∧ s'.stack.length = (⟨i, lowerBecome sc moved f byRef ++ junk, r⟩ :: rest).length :=
  ⟨_, become_frame_reuse_and_lifo_drops P sc moved f byRef junk i r rest nx tr, rfl⟩

/-! ### A.2  Stack depth: programs without ordinary calls never grow the stack -/

def NoCall (c : List Stmt) : Prop := ∀ (f : Nat) (b : Bool), Stmt.call f b ∉ c

def ProgNoCall (P : Prog) : Prop := ∀ g, NoCall (P g)

def StackNoCall (st : List Frame) : Prop := ∀ fr, fr ∈ st → NoCall fr.code

theorem noCall_tail {st : Stmt} {k : List Stmt} (h : NoCall (st :: k)) : NoCall k :=
  fun f b hm => h f b (List.Mem.tail _ hm)

theorem stackNoCall_cons {fr : Frame} {rest : List Frame} (h1 : NoCall fr.code)
    (h2 : StackNoCall rest) : StackNoCall (fr :: rest) := by
  intro g hg
  cases hg with
  | head => exact h1
  | tail _ hg' => exact h2 g hg'

theorem step_depth_le (P : Prog) (hP : ProgNoCall P) (s s' : State)
    (hs : StackNoCall s.stack) (h : step P s = some s') :
    s'.stack.length ≤ s.stack.length ∧ StackNoCall s'.stack := by
  cases s with
  | mk stack nx tr =>
  cases stack with
  | nil =>
    have h' : some (⟨[], nx, tr⟩ : State) = some s' := h
    cases h'
    exact ⟨Nat.le_refl _, hs⟩
  | cons fr rest =>
    cases fr with
    | mk i code r =>
    have hrest : StackNoCall rest := fun g hg => hs g (List.Mem.tail _ hg)
    have hcode : NoCall code := hs ⟨i, code, r⟩ (List.Mem.head _)
    cases code with
    | nil =>
      have h' : some (⟨rest, nx, tr⟩ : State) = some s' := h
      cases h'
      exact ⟨Nat.le_succ _, hrest⟩
    | cons st k =>
      have hk : NoCall k := noCall_tail hcode
      cases st with
      | eff e =>
        rw [step_eff] at h
        cases h
        exact ⟨Nat.le_refl _, stackNoCall_cons hk hrest⟩
      | call f b => exact absurd (List.Mem.head _) (hcode f b)
      | tailcall f b =>
        rw [step_tailcall] at h
        cases h
        exact ⟨Nat.le_refl _, stackNoCall_cons (hP f) hrest⟩
      | useRef =>
        cases r with
        | none =>
          have h' : some (⟨⟨i, k, none⟩ :: rest, nx, tr⟩ : State) = some s' := h
          cases h'
          exact ⟨Nat.le_refl _, stackNoCall_cons hk hrest⟩
        | some p =>
          rw [step_useRef_some] at h
          split at h
          · cases h
            exact ⟨Nat.le_refl _, stackNoCall_cons hk hrest⟩
          · cases h
      | ret =>
        have h' : some (⟨rest, nx, tr⟩ : State) = some s' := h
        cases h'
        exact ⟨Nat.le_succ _, hrest⟩

/-- **Theorem 1' (constant stack bound).** If neither the program nor any frame on the
stack contains an ordinary `call` — every inter-procedural transfer is a `tailcall` —
then no execution of any length ever has more frames than it started with. -/
theorem run_depth_le (P : Prog) (hP : ProgNoCall P) :
    ∀ (n : Nat) (s s' : State), StackNoCall s.stack → run P n s = some s' →
      s'.stack.length ≤ s.stack.length
  | 0, s, s', _, h => by
    have h' : some s = some s' := h
    cases h'
    exact Nat.le_refl _
  | n + 1, s, s', hs, h => by
    rw [run_succ] at h
    cases hstep : step P s with
    | none =>
      rw [hstep] at h
      have h' : (none : Option State) = some s' := h
      cases h'
    | some s1 =>
      rw [hstep] at h
      have h' : run P n s1 = some s' := h
      have h1 := step_depth_le P hP s s1 hs hstep
      exact Nat.le_trans (run_depth_le P hP n s1 s' h1.2 h') h1.1

/-- The one-statement program in which every function's body is `st`. -/
noncomputable def loopProg (st : Stmt) : Prog := fun _ => [st]

/-- A self tail call runs forever at the depth it started with. -/
theorem tail_loop_depth_const (n : Nat) :
    ∀ (i : Nat) (r : Option Nat) (rest : List Frame) (nx : Nat) (tr : List Event),
      ∃ s', run (loopProg (.tailcall 0 false)) n ⟨⟨i, [.tailcall 0 false], r⟩ :: rest, nx, tr⟩
              = some s'
        ∧ s'.stack.length = rest.length + 1 := by
  induction n with
  | zero => intro i r rest nx tr; exact ⟨_, rfl, rfl⟩
  | succ n ih =>
    intro i r rest nx tr
    rw [run_succ, step_tailcall]
    exact ih nx none rest (nx + 1) tr

/-- The same loop written with an ordinary call gains one frame per step. -/
theorem call_loop_depth_linear (n : Nat) :
    ∀ (i : Nat) (r : Option Nat) (rest : List Frame) (nx : Nat) (tr : List Event),
      ∃ s', run (loopProg (.call 0 false)) n ⟨⟨i, [.call 0 false], r⟩ :: rest, nx, tr⟩
              = some s'
        ∧ s'.stack.length = rest.length + 1 + n := by
  induction n with
  | zero => intro i r rest nx tr; exact ⟨_, rfl, rfl⟩
  | succ n ih =>
    intro i r rest nx tr
    rw [run_succ, step_call]
    obtain ⟨s', h1, h2⟩ := ih nx none (⟨i, [], r⟩ :: rest) (nx + 1) tr
    refine ⟨s', h1, ?_⟩
    rw [h2]
    show rest.length + 1 + 1 + n = rest.length + 1 + (n + 1)
    rw [Nat.add_assoc (rest.length + 1) 1 n, Nat.add_comm 1 n]

theorem progNoCall_tail_loop : ProgNoCall (loopProg (.tailcall 0 false)) := by
  intro g f b hm
  cases hm with
  | tail _ h => cases h

/-- The hypotheses of `run_depth_le` are satisfiable: the self tail call loop, started in
a single frame, never has more than one frame, for every number of steps. -/
theorem tail_loop_never_grows (n : Nat) (s' : State)
    (h : run (loopProg (.tailcall 0 false)) n ⟨[⟨0, [.tailcall 0 false], none⟩], 1, []⟩ = some s') :
    s'.stack.length ≤ 1 :=
  run_depth_le (loopProg (.tailcall 0 false)) progNoCall_tail_loop n _ s'
    (fun fr hfr => by
      cases hfr with
      | head => exact progNoCall_tail_loop 0
      | tail _ h' => cases h')
    h

/-! ### A.3  Call-site inlining of a callee that ends in a tail call

The caller executes `pre`, calls `f`, then continues with `post`. The body of `f` is
`fpre` followed by `tailcall g`. Three versions of the caller's frame are compared:

* original:        `pre ++ [call f] ++ post`
* naive splice:    `pre ++ (fpre ++ [tailcall g]) ++ post`   (callee body copied verbatim)
* demoted splice:  `pre ++ fpre ++ [call g] ++ post`         (tail call turned into a call
                                                              that returns to `post`) -/

theorem original_reaches (P : Prog) (f g : Nat) (pre fpre : List Event) (post : List Stmt)
    (hf : P f = effs fpre ++ [Stmt.tailcall g false]) (i : Nat) (r : Option Nat)
    (rest : List Frame) (nx : Nat) (tr : List Event) :
    run P (pre.length + 1 + (fpre.length + 1))
        ⟨⟨i, effs pre ++ (Stmt.call f false :: post), r⟩ :: rest, nx, tr⟩
      = some ⟨⟨nx + 1, P g, none⟩ :: ⟨i, post, r⟩ :: rest, nx + 1 + 1, tr ++ pre ++ fpre⟩ := by
  rw [run_add, run_add, run_effs]
  show (run P 1 ⟨⟨i, Stmt.call f false :: post, r⟩ :: rest, nx, tr ++ pre⟩).bind
      (run P (fpre.length + 1)) = _
  rw [run_succ, step_call, hf]
  show run P (fpre.length + 1)
      ⟨⟨nx, effs fpre ++ [Stmt.tailcall g false], none⟩ :: ⟨i, post, r⟩ :: rest, nx + 1,
        tr ++ pre⟩ = _
  rw [run_add, run_effs]
  rfl

theorem naive_splice_reaches (P : Prog) (g : Nat) (pre fpre : List Event) (post : List Stmt)
    (i : Nat) (r : Option Nat) (rest : List Frame) (nx : Nat) (tr : List Event) :
    run P (pre.length + (fpre.length + 1))
        ⟨⟨i, effs pre ++ ((effs fpre ++ [Stmt.tailcall g false]) ++ post), r⟩ :: rest, nx, tr⟩
      = some ⟨⟨nx, P g, none⟩ :: rest, nx + 1, tr ++ pre ++ fpre⟩ := by
  rw [run_add, run_effs]
  show run P (fpre.length + 1)
      ⟨⟨i, (effs fpre ++ [Stmt.tailcall g false]) ++ post, r⟩ :: rest, nx, tr ++ pre⟩ = _
  rw [List.append_assoc, run_add, run_effs]
  rfl

theorem demoted_splice_reaches (P : Prog) (g : Nat) (pre fpre : List Event) (post : List Stmt)
    (i : Nat) (r : Option Nat) (rest : List Frame) (nx : Nat) (tr : List Event) :
    run P (pre.length + (fpre.length + 1))
        ⟨⟨i, effs pre ++ (effs fpre ++ (Stmt.call g false :: post)), r⟩ :: rest, nx, tr⟩
      = some ⟨⟨nx, P g, none⟩ :: ⟨i, post, r⟩ :: rest, nx + 1, tr ++ pre ++ fpre⟩ := by
  rw [run_add, run_effs]
  show run P (fpre.length + 1)
      ⟨⟨i, effs fpre ++ (Stmt.call g false :: post), r⟩ :: rest, nx, tr ++ pre⟩ = _
  rw [run_add, run_effs]
  rfl

/-- **Theorem 2a (what the naive splice loses).** At the moment `g` is entered, the
original and the demoted splice have the same frames (same remaining code in the same
order) and the same trace, while the naive splice has exactly one frame fewer: the
caller's continuation `post` is no longer anywhere on the stack. -/
theorem inline_configurations (P : Prog) (f g : Nat) (pre fpre : List Event) (post : List Stmt)
    (hf : P f = effs fpre ++ [Stmt.tailcall g false]) (i : Nat) (r : Option Nat)
    (rest : List Frame) (nx : Nat) (tr : List Event) :
    ∃ so sn sd,
      run P (pre.length + 1 + (fpre.length + 1))
          ⟨⟨i, effs pre ++ (Stmt.call f false :: post), r⟩ :: rest, nx, tr⟩ = some so ∧
      run P (pre.length + (fpre.length + 1))
          ⟨⟨i, effs pre ++ ((effs fpre ++ [Stmt.tailcall g false]) ++ post), r⟩ :: rest, nx, tr⟩
            = some sn ∧
      run P (pre.length + (fpre.length + 1))
          ⟨⟨i, effs pre ++ (effs fpre ++ (Stmt.call g false :: post)), r⟩ :: rest, nx, tr⟩
            = some sd ∧
      so.stack.map Frame.code = P g :: post :: rest.map Frame.code ∧
      sd.stack.map Frame.code = P g :: post :: rest.map Frame.code ∧
      sn.stack.map Frame.code = P g :: rest.map Frame.code ∧
      so.trace = sd.trace ∧ so.trace = sn.trace ∧
      so.stack.length = sn.stack.length + 1 :=
  ⟨_, _, _, original_reaches P f g pre fpre post hf i r rest nx tr,
    naive_splice_reaches P g pre fpre post i r rest nx tr,
    demoted_splice_reaches P g pre fpre post i r rest nx tr, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `Halts P s tr`: from `s` the machine reaches the empty stack with trace `tr`. -/
def Halts (P : Prog) (s : State) (tr : List Event) : Prop :=
  ∃ n nx, run P n s = some ⟨[], nx, tr⟩

theorem run_halted_extend (P : Prog) (n m : Nat) (s : State) (nx : Nat) (tr : List Event)
    (h : run P n s = some ⟨[], nx, tr⟩) : run P (n + m) s = some ⟨[], nx, tr⟩ := by
  rw [run_add, h]
  exact run_halted P m nx tr

/-- The machine is deterministic: a state halts with at most one trace. -/
theorem halts_deterministic (P : Prog) (s : State) (tr₁ tr₂ : List Event)
    (h₁ : Halts P s tr₁) (h₂ : Halts P s tr₂) : tr₁ = tr₂ := by
  obtain ⟨n₁, nx₁, e₁⟩ := h₁
  obtain ⟨n₂, nx₂, e₂⟩ := h₂
  have a := run_halted_extend P n₁ n₂ s nx₁ tr₁ e₁
  have b := run_halted_extend P n₂ n₁ s nx₂ tr₂ e₂
  rw [Nat.add_comm n₂ n₁, a] at b
  exact congrArg State.trace (Option.some.inj b)

/-- **Theorem 2b (the naive splice is observably wrong).** For every straight-line `pre`
and `fpre` and every effect `x` that the caller performs after the call: the original
program halts with trace `pre ++ fpre ++ [x]`; the naively spliced caller halts with
trace `pre ++ fpre` and cannot produce the original trace — the tail call returned
past the caller, so `x` never happens. -/
theorem naive_inline_of_tailcall_unsound (P : Prog) (f g : Nat) (pre fpre : List Event)
    (x : Event) (hf : P f = effs fpre ++ [Stmt.tailcall g false]) (hg : P g = []) :
    Halts P ⟨[⟨0, effs pre ++ (Stmt.call f false :: [Stmt.eff x]), none⟩], 1, []⟩
        (pre ++ fpre ++ [x]) ∧
    Halts P ⟨[⟨0, effs pre ++ ((effs fpre ++ [Stmt.tailcall g false]) ++ [Stmt.eff x]), none⟩],
        1, []⟩ (pre ++ fpre) ∧
    ¬ Halts P ⟨[⟨0, effs pre ++ ((effs fpre ++ [Stmt.tailcall g false]) ++ [Stmt.eff x]), none⟩],
        1, []⟩ (pre ++ fpre ++ [x]) := by
  have h1 : Halts P ⟨[⟨0, effs pre ++ (Stmt.call f false :: [Stmt.eff x]), none⟩], 1, []⟩
      (pre ++ fpre ++ [x]) := by
    refine ⟨pre.length + 1 + (fpre.length + 1) + 3, 3, ?_⟩
    rw [run_add, original_reaches P f g pre fpre [Stmt.eff x] hf, hg]
    rfl
  have h2 : Halts P
      ⟨[⟨0, effs pre ++ ((effs fpre ++ [Stmt.tailcall g false]) ++ [Stmt.eff x]), none⟩], 1, []⟩
      (pre ++ fpre) := by
    refine ⟨pre.length + (fpre.length + 1) + 1, 2, ?_⟩
    rw [run_add, naive_splice_reaches P g pre fpre [Stmt.eff x], hg]
    rfl
  refine ⟨h1, h2, ?_⟩
  intro h3
  have e := congrArg List.length (halts_deterministic P _ _ _ h3 h2)
  rw [List.length_append] at e
  exact Nat.succ_ne_self _ e

/-! ### A.4  Activation-id freshness and the dangling borrow -/

/-- Every activation on the stack has an id below the allocation counter, and no two
activations share an id. Holds initially for a single frame and is preserved by `step`. -/
def Fresh (s : State) : Prop :=
  (∀ fr, fr ∈ s.stack → fr.id < s.next) ∧ Distinct (s.stack.map Frame.id)

theorem not_mem_ids_of_lt (st : List Frame) (nx : Nat) (h : ∀ fr, fr ∈ st → fr.id < nx) :
    nx ∉ st.map Frame.id := by
  intro hm
  obtain ⟨fr, hfr, e⟩ := List.mem_map.mp hm
  have := h fr hfr
  rw [e] at this
  exact Nat.lt_irrefl _ this

theorem step_fresh (P : Prog) (s s' : State) (hs : Fresh s) (h : step P s = some s') :
    Fresh s' := by
  cases s with
  | mk stack nx tr =>
  cases stack with
  | nil =>
    have h' : some (⟨[], nx, tr⟩ : State) = some s' := h
    cases h'
    exact hs
  | cons fr rest =>
    cases fr with
    | mk i code r =>
    have hlt : ∀ g, g ∈ rest → g.id < nx := fun g hg => hs.1 g (List.Mem.tail _ hg)
    have hi : i < nx := hs.1 ⟨i, code, r⟩ (List.Mem.head _)
    have hd : i ∉ rest.map Frame.id ∧ Distinct (rest.map Frame.id) := hs.2
    have popped : Fresh ⟨rest, nx, tr⟩ := ⟨hlt, hd.2⟩
    have same : ∀ (k : List Stmt) (r' : Option Nat), Fresh ⟨⟨i, k, r'⟩ :: rest, nx, tr⟩ :=
      fun k r' => ⟨fun g hg => by
        cases hg with
        | head => exact hi
        | tail _ hg' => exact hlt g hg', hd⟩
    cases code with
    | nil =>
      have h' : some (⟨rest, nx, tr⟩ : State) = some s' := h
      cases h'
      exact popped
    | cons st k =>
      cases st with
      | eff e =>
        rw [step_eff] at h
        cases h
        exact same k r
      | call f b =>
        rw [step_call] at h
        cases h
        refine ⟨fun g hg => ?_, ?_, hd⟩
        · cases hg with
          | head => exact Nat.lt_succ_self _
          | tail _ hg' =>
            cases hg' with
            | head => exact Nat.lt_succ_of_lt hi
            | tail _ hg'' => exact Nat.lt_succ_of_lt (hlt g hg'')
        · exact not_mem_ids_of_lt (⟨i, k, r⟩ :: rest) nx (same k r).1
      | tailcall f b =>
        rw [step_tailcall] at h
        cases h
        refine ⟨fun g hg => ?_, not_mem_ids_of_lt rest nx hlt, hd.2⟩
        cases hg with
        | head => exact Nat.lt_succ_self _
        | tail _ hg' => exact Nat.lt_succ_of_lt (hlt g hg')
      | useRef =>
        cases r with
        | none =>
          have h' : some (⟨⟨i, k, none⟩ :: rest, nx, tr⟩ : State) = some s' := h
          cases h'
          exact same k none
        | some p =>
          rw [step_useRef_some] at h
          split at h
          · cases h
            exact same k (some p)
          · cases h
      | ret =>
        have h' : some (⟨rest, nx, tr⟩ : State) = some s' := h
        cases h'
        exact popped

/-- **Counterexample 1 (dangling stack borrow across a tail call).**
In every `Fresh` state: handing the callee a pointer into the caller's frame and then
dereferencing it is undefined behaviour when the transfer is a `tailcall` (the pointee
frame was replaced), and is well defined when the transfer is a `call` (the pointee
frame is still below the callee). -/
theorem ce1_dangling_stack_borrow_across_tailcall_frame_reuse_ub (P : Prog) (f : Nat)
    (k k' : List Stmt) (hf : P f = Stmt.useRef :: k') (i : Nat) (r : Option Nat)
    (rest : List Frame) (nx : Nat) (tr : List Event)
    (hfresh : Fresh ⟨⟨i, Stmt.tailcall f true :: k, r⟩ :: rest, nx, tr⟩) :
    run P 2 ⟨⟨i, Stmt.tailcall f true :: k, r⟩ :: rest, nx, tr⟩ = none ∧
    run P 2 ⟨⟨i, Stmt.call f true :: k, r⟩ :: rest, nx, tr⟩
      = some ⟨⟨nx, k', some i⟩ :: ⟨i, k, r⟩ :: rest, nx + 1, tr⟩ := by
  have hi : i < nx := hfresh.1 _ (List.Mem.head _)
  have hu : i ∉ rest.map Frame.id := hfresh.2.1
  constructor
  · rw [run_succ, step_tailcall, hf]
    show run P 1 ⟨⟨nx, Stmt.useRef :: k', some i⟩ :: rest, nx + 1, tr⟩ = none
    rw [run_succ, step_useRef_some, ite_eq_right]
    · rfl
    · intro hm
      cases hm with
      | head => exact Nat.lt_irrefl _ hi
      | tail _ hm' => exact hu hm'
  · rw [run_succ, step_call, hf]
    show run P 1 ⟨⟨nx, Stmt.useRef :: k', some i⟩ :: ⟨i, k, r⟩ :: rest, nx + 1, tr⟩ = _
    rw [run_succ, step_useRef_some, ite_eq_left]
    · rfl
    · exact List.Mem.tail _ (List.Mem.head _)

/-- `Fresh` holds along every execution, so Counterexample 1 applies to every state
reachable from a `Fresh` one. -/
theorem run_fresh (P : Prog) :
    ∀ (n : Nat) (s s' : State), Fresh s → run P n s = some s' → Fresh s'
  | 0, s, s', hs, h => by
    have h' : some s = some s' := h
    cases h'
    exact hs
  | n + 1, s, s', hs, h => by
    rw [run_succ] at h
    cases hstep : step P s with
    | none =>
      rw [hstep] at h
      have h' : (none : Option State) = some s' := h
      cases h'
    | some s1 =>
      rw [hstep] at h
      have h' : run P n s1 = some s' := h
      exact run_fresh P n s1 s' (step_fresh P s s1 hs hstep) h'

/-- A single initial frame is `Fresh`. -/
theorem fresh_single (code : List Stmt) : Fresh ⟨[⟨0, code, none⟩], 1, []⟩ :=
  ⟨(fun fr h => by
      cases h with
      | head => exact Nat.lt_succ_self 0
      | tail _ h' => cases h'),
    ⟨(fun h => by cases h), trivial⟩⟩

/-- Function 1 dereferences its pointer argument; everything else is empty. -/
noncomputable def refProg : Prog := fun g =>
  match g with
  | 1 => [.useRef]
  | _ => []

/-- Closed instance of Counterexample 1, computed directly by the machine. -/
theorem ce1_instance :
    run refProg 2 ⟨[⟨0, [.tailcall 1 true], none⟩], 1, []⟩ = none ∧
    run refProg 2 ⟨[⟨0, [.call 1 true], none⟩], 1, []⟩
      = some ⟨[⟨1, [], some 0⟩, ⟨0, [], none⟩], 2, []⟩ :=
  ⟨rfl, rfl⟩

/-- Function 1 emits `5` and tail-calls the empty function 2. -/
noncomputable def inlineProg : Prog := fun g =>
  match g with
  | 1 => [.eff (.emit 5), .tailcall 2 false]
  | _ => []

/-- Closed instance of Theorem 2b (so its hypotheses are satisfiable): the original
caller logs `4, 5, 7`; the naively spliced caller logs only `4, 5`. -/
theorem naive_inline_instance :
    Halts inlineProg ⟨[⟨0, [.eff (.emit 4), .call 1 false, .eff (.emit 7)], none⟩], 1, []⟩
        [.emit 4, .emit 5, .emit 7] ∧
    Halts inlineProg
        ⟨[⟨0, [.eff (.emit 4), .eff (.emit 5), .tailcall 2 false, .eff (.emit 7)], none⟩], 1, []⟩
        [.emit 4, .emit 5] ∧
    ¬ Halts inlineProg
        ⟨[⟨0, [.eff (.emit 4), .eff (.emit 5), .tailcall 2 false, .eff (.emit 7)], none⟩], 1, []⟩
        [.emit 4, .emit 5, .emit 7] :=
  naive_inline_of_tailcall_unsound inlineProg 1 2 [.emit 4] [.emit 5] (.emit 7) rfl rfl

/-! ### A.5  Concrete scenarios (the three programs measured by the Rust probe)

Resource ids and the callee-body marker `9` are the digits used by the probe, and
`logNumber` folds a trace into the decimal number the probe prints. -/

noncomputable def digit : Event → Nat
  | .emit n => n
  | .drop r => r

noncomputable def logNumber (tr : List Event) : Nat := tr.foldl (fun acc e => acc * 10 + digit e) 0

/-- Stack depth before each of the first `n` steps, and after the last. -/
noncomputable def depths (P : Prog) : Nat → State → List Nat
  | 0, s => [s.stack.length]
  | n + 1, s =>
      s.stack.length :: (match step P s with
        | some s' => depths P n s'
        | none => [])

noncomputable def summary (o : Option State) : Option (Nat × Nat) :=
  o.map (fun s => (s.stack.length, logNumber s.trace))

/-- Function 1: one guard parameter `3`; function 2: two guard parameters `6`, `7`;
function 3: one guard parameter `1` (the caller's own parameter, forwarded).
A callee body logs `9`; its parameters are dropped in reverse order on exit. -/
noncomputable def scenarioProg : Prog := fun g =>
  match g with
  | 1 => [.eff (.emit 9), .eff (.drop 3)]
  | 2 => [.eff (.emit 9), .eff (.drop 7), .eff (.drop 6)]
  | 3 => [.eff (.emit 9), .eff (.drop 1)]
  | _ => []

noncomputable def frame0 (code : List Stmt) : State := ⟨[⟨0, code, none⟩], 1, []⟩

noncomputable def s1Become : State := frame0 (lowerBecome ⟨[1], [[2]]⟩ [] 1 false)
noncomputable def s1Plain : State := frame0 [.call 1 false, .eff (.drop 2), .eff (.drop 1)]
noncomputable def s1DropsAfterTailcall : State := frame0 [.tailcall 1 false, .eff (.drop 2), .eff (.drop 1)]
noncomputable def s2Become : State := frame0 (lowerBecome ⟨[1, 2], [[3], [4, 5]]⟩ [] 2 false)
noncomputable def s2Plain : State :=
  frame0 [.call 2 false, .eff (.drop 5), .eff (.drop 4), .eff (.drop 3), .eff (.drop 2),
    .eff (.drop 1)]
noncomputable def s3Forward : State := frame0 (lowerBecome ⟨[1], [[2]]⟩ [1] 3 false)

/-- **Counterexample 2 (dropping the caller's variables after the transfer).**
Scenario 1 under three lowerings:

* `become` lowering — final log `2193`, and the stack never exceeds one frame;
* drops placed after an ordinary call — final log `9321` (the callee body runs before the
  caller's drops) and the stack reaches two frames, so the call is not in tail position;
* drops placed after a `tailcall` in the same frame — final log `93`: the drops of `2`
  and `1` are never executed at all. -/
theorem ce2_post_tailcall_caller_drop_violates_tail_position_and_order :
    summary (run scenarioProg 6 s1Become) = some (0, 2193) ∧
    depths scenarioProg 6 s1Become = [1, 1, 1, 1, 1, 1, 0] ∧
    summary (run scenarioProg 7 s1Plain) = some (0, 9321) ∧
    depths scenarioProg 7 s1Plain = [1, 2, 2, 2, 1, 1, 1, 0] ∧
    summary (run scenarioProg 6 s1DropsAfterTailcall) = some (0, 93) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Scenarios 2 and 3 reproduce the remaining logs printed by the probe. -/
theorem scenario_logs :
    summary (run scenarioProg 10 s2Become) = some (0, 54321976) ∧
    summary (run scenarioProg 11 s2Plain) = some (0, 97654321) ∧
    summary (run scenarioProg 6 s3Forward) = some (0, 291) :=
  ⟨rfl, rfl, rfl⟩

/-! ## Part B — mangling of type trees

`TyTree` is a binary type tree: `leaf n` is a basic type and `node c l r` a generic
constructor `c` applied to two type arguments.

* `naive` spells every occurrence of every subtree.
* `legacyMangle` keeps an item path and a digest of the type.
* `enc` / `encodeV0Dag` spell a compound subtree the first time it is met and emit a
  backreference on every later occurrence; `dec` / `decodeV0Dag` invert it.

Abstraction: a backreference here is an index into the table of compound subtrees
completed so far. rustc's `v0` scheme instead stores the byte offset at which the
earlier occurrence started, written in base 62. Sizes below are therefore token
counts, not bytes. -/

inductive TyTree where
  | leaf (n : Nat)
  | node (c : Nat) (l r : TyTree)

noncomputable def TyTree.decEqTree : (a b : TyTree) → Decidable (a = b)
  | .leaf n, .leaf m =>
    match Nat.decEq n m with
    | .isTrue h => .isTrue (by rw [h])
    | .isFalse h => .isFalse (fun e => by cases e; exact h rfl)
  | .leaf _, .node _ _ _ => .isFalse (fun e => by cases e)
  | .node _ _ _, .leaf _ => .isFalse (fun e => by cases e)
  | .node c₁ l₁ r₁, .node c₂ l₂ r₂ =>
    match Nat.decEq c₁ c₂, TyTree.decEqTree l₁ l₂, TyTree.decEqTree r₁ r₂ with
    | .isTrue hc, .isTrue hl, .isTrue hr => .isTrue (by rw [hc, hl, hr])
    | .isFalse hc, _, _ => .isFalse (fun e => by cases e; exact hc rfl)
    | _, .isFalse hl, _ => .isFalse (fun e => by cases e; exact hl rfl)
    | _, _, .isFalse hr => .isFalse (fun e => by cases e; exact hr rfl)

noncomputable instance : DecidableEq TyTree := TyTree.decEqTree

inductive Tok where
  | leaf (n : Nat)
  | node (c : Nat)
  | ref (i : Nat)
  deriving DecidableEq

noncomputable def naive : TyTree → List Tok
  | .leaf n => [.leaf n]
  | .node c l r => .node c :: (naive l ++ naive r)

noncomputable def findIdx (t : TyTree) : List TyTree → Option Nat
  | [] => none
  | x :: xs => if x = t then some 0 else (findIdx t xs).map (· + 1)

noncomputable def nth : List TyTree → Nat → Option TyTree
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i + 1 => nth xs i

/-- Encode `t` given the table `d` of compound subtrees already emitted; returns the
tokens and the extended table. -/
noncomputable def enc : TyTree → List TyTree → List Tok × List TyTree
  | .leaf n, d => ([.leaf n], d)
  | .node c l r, d =>
    match findIdx (.node c l r) d with
    | some i => ([.ref i], d)
    | none =>
      (.node c :: ((enc l d).1 ++ (enc r (enc l d).2).1),
        (enc r (enc l d).2).2 ++ [.node c l r])

/-- Decode one tree from the front of the token list, maintaining the same table. -/
noncomputable def dec : Nat → List Tok → List TyTree → Option (TyTree × List Tok × List TyTree)
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | _ + 1, .leaf n :: ts, d => some (.leaf n, ts, d)
  | _ + 1, .ref i :: ts, d =>
    match nth d i with
    | some t => some (t, ts, d)
    | none => none
  | fuel + 1, .node c :: ts, d =>
    match dec fuel ts d with
    | none => none
    | some (l, ts1, d1) =>
      match dec fuel ts1 d1 with
      | none => none
      | some (r, ts2, d2) => some (.node c l r, ts2, d2 ++ [.node c l r])

noncomputable def encodeV0Dag (t : TyTree) : List Tok := (enc t []).1

noncomputable def decodeV0Dag (ts : List Tok) : Option TyTree :=
  match dec ts.length ts [] with
  | some (t, [], _) => some t
  | _ => none

theorem enc_hit (c : Nat) (l r : TyTree) (d : List TyTree) (i : Nat)
    (h : findIdx (.node c l r) d = some i) : enc (.node c l r) d = ([.ref i], d) := by
  simp only [enc, h]

theorem enc_miss (c : Nat) (l r : TyTree) (d : List TyTree)
    (h : findIdx (.node c l r) d = none) :
    enc (.node c l r) d
      = (.node c :: ((enc l d).1 ++ (enc r (enc l d).2).1),
          (enc r (enc l d).2).2 ++ [.node c l r]) := by
  simp only [enc, h]

theorem nth_of_findIdx (t : TyTree) :
    ∀ (d : List TyTree) (i : Nat), findIdx t d = some i → nth d i = some t
  | [], _, h => by cases h
  | x :: xs, i, h => by
    unfold findIdx at h
    split at h
    · rename_i hx
      cases h
      rw [hx]
      rfl
    · cases hj : findIdx t xs with
      | none => rw [hj] at h; cases h
      | some j =>
        rw [hj] at h
        cases h
        exact nth_of_findIdx t xs j hj

theorem not_mem_of_findIdx_none (t : TyTree) :
    ∀ (d : List TyTree), findIdx t d = none → t ∉ d
  | [], _ => by intro h; cases h
  | x :: xs, h => by
    unfold findIdx at h
    split at h
    · cases h
    · rename_i hx
      intro hm
      cases hm with
      | head => exact hx rfl
      | tail _ hm' =>
        cases hj : findIdx t xs with
        | none => exact not_mem_of_findIdx_none t xs hj hm'
        | some j => rw [hj] at h; cases h

theorem dec_node_of (f c : Nat) (ts : List Tok) (d : List TyTree) (l : TyTree)
    (ts1 : List Tok) (d1 : List TyTree) (r : TyTree) (ts2 : List Tok) (d2 : List TyTree)
    (h1 : dec f ts d = some (l, ts1, d1)) (h2 : dec f ts1 d1 = some (r, ts2, d2)) :
    dec (f + 1) (.node c :: ts) d = some (.node c l r, ts2, d2 ++ [.node c l r]) := by
  simp only [dec, h1, h2]

/-- Decoding the encoding of `t` (followed by arbitrary further tokens) returns `t`, the
untouched remainder, and the encoder's table — given fuel at least the token count. -/
theorem dec_enc (t : TyTree) :
    ∀ (d : List TyTree) (rest : List Tok) (fuel : Nat), (enc t d).1.length ≤ fuel →
      dec fuel ((enc t d).1 ++ rest) d = some (t, rest, (enc t d).2) := by
  induction t with
  | leaf n =>
    intro d rest fuel h
    cases fuel with
    | zero => exact absurd h (Nat.not_succ_le_zero 0)
    | succ f => rfl
  | node c l r ihl ihr =>
    intro d rest fuel h
    cases hfi : findIdx (.node c l r) d with
    | some i =>
      rw [enc_hit c l r d i hfi] at h ⊢
      cases fuel with
      | zero => exact absurd h (Nat.not_succ_le_zero 0)
      | succ f =>
        show (match nth d i with
          | some t => some (t, rest, d)
          | none => none) = some (TyTree.node c l r, rest, d)
        rw [nth_of_findIdx _ d i hfi]
    | none =>
      rw [enc_miss c l r d hfi] at h ⊢
      cases fuel with
      | zero => exact absurd h (Nat.not_succ_le_zero _)
      | succ f =>
        have hlen : (enc l d).1.length + (enc r (enc l d).2).1.length ≤ f := by
          have h' := Nat.le_of_succ_le_succ h
          rw [List.length_append] at h'
          exact h'
        have hl : (enc l d).1.length ≤ f := Nat.le_trans (Nat.le_add_right _ _) hlen
        have hr : (enc r (enc l d).2).1.length ≤ f := Nat.le_trans (Nat.le_add_left _ _) hlen
        have e1 := ihl d ((enc r (enc l d).2).1 ++ rest) f hl
        have e2 := ihr (enc l d).2 rest f hr
        show dec (f + 1) (Tok.node c :: (((enc l d).1 ++ (enc r (enc l d).2).1) ++ rest)) d = _
        rw [List.append_assoc]
        exact dec_node_of f c _ d l _ _ r rest _ e1 e2

/-- **Theorem 3a (lossless round trip).** -/
theorem decode_encode (t : TyTree) : decodeV0Dag (encodeV0Dag t) = some t := by
  have h := dec_enc t [] [] (enc t []).1.length (Nat.le_refl _)
  rw [List.append_nil] at h
  unfold decodeV0Dag encodeV0Dag
  rw [h]

/-- **Theorem 3b (injectivity).** Distinct type trees have distinct encodings. -/
theorem encodeV0Dag_injective (a b : TyTree) (h : encodeV0Dag a = encodeV0Dag b) : a = b := by
  have ha := decode_encode a
  rw [h, decode_encode b] at ha
  exact (Option.some.inj ha).symm

/-! ### B.1  Size: linear in the number of distinct compound subtrees -/

/-- Every compound subtree of `t`, once per occurrence. -/
noncomputable def subterms : TyTree → List TyTree
  | .leaf _ => []
  | .node c l r => .node c l r :: (subterms l ++ subterms r)

noncomputable def size : TyTree → Nat
  | .leaf _ => 1
  | .node _ l r => size l + size r + 1

theorem size_le_of_mem_subterms (t : TyTree) : ∀ x, x ∈ subterms t → size x ≤ size t := by
  induction t with
  | leaf n => intro x hx; cases hx
  | node c l r ihl ihr =>
    intro x hx
    cases hx with
    | head => exact Nat.le_refl _
    | tail _ hx' =>
      cases List.mem_append.mp hx' with
      | inl h =>
        exact Nat.le_trans (ihl x h) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _))
      | inr h =>
        exact Nat.le_trans (ihr x h) (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_succ _))

/-- The table grows by a duplicate-free list `new` of compound subtrees of `t`, none of
which was in the table before, and the token count is `2 * new.length + 1`. -/
theorem enc_spec (t : TyTree) :
    ∀ (d : List TyTree), ∃ new : List TyTree,
      (enc t d).2 = d ++ new ∧
      (enc t d).1.length = new.length + new.length + 1 ∧
      (∀ x, x ∈ new → x ∈ subterms t) ∧
      (∀ x, x ∈ new → x ∉ d) ∧
      Distinct new := by
  induction t with
  | leaf n =>
    intro d
    exact ⟨[], (List.append_nil d).symm, rfl, (fun x hx => by cases hx),
      (fun x hx => by cases hx), trivial⟩
  | node c l r ihl ihr =>
    intro d
    cases hfi : findIdx (.node c l r) d with
    | some i =>
      rw [enc_hit c l r d i hfi]
      exact ⟨[], (List.append_nil d).symm, rfl, (fun x hx => by cases hx),
        (fun x hx => by cases hx), trivial⟩
    | none =>
      rw [enc_miss c l r d hfi]
      obtain ⟨n1, hd1, hl1, hs1, hn1, hD1⟩ := ihl d
      obtain ⟨n2, hd2, hl2, hs2, hn2, hD2⟩ := ihr (enc l d).2
      have ht : TyTree.node c l r ∉ d := not_mem_of_findIdx_none _ d hfi
      have hsmall : ∀ x, x ∈ n1 ++ n2 → x ≠ TyTree.node c l r := by
        intro x hx e
        have hlt : size x < size (TyTree.node c l r) := by
          cases List.mem_append.mp hx with
          | inl h =>
            exact Nat.lt_succ_of_le
              (Nat.le_trans (size_le_of_mem_subterms l x (hs1 x h)) (Nat.le_add_right _ _))
          | inr h =>
            exact Nat.lt_succ_of_le
              (Nat.le_trans (size_le_of_mem_subterms r x (hs2 x h)) (Nat.le_add_left _ _))
        rw [e] at hlt
        exact Nat.lt_irrefl _ hlt
      have h21 : ∀ x, x ∈ n2 → x ∉ n1 := by
        intro x hx h1
        have := hn2 x hx
        rw [hd1] at this
        exact this (List.mem_append.mpr (Or.inr h1))
      refine ⟨n1 ++ n2 ++ [TyTree.node c l r], ?_, ?_, ?_, ?_, ?_⟩
      · show (enc r (enc l d).2).2 ++ [TyTree.node c l r] = d ++ (n1 ++ n2 ++ [TyTree.node c l r])
        rw [hd2, hd1, List.append_assoc, List.append_assoc, List.append_assoc]
      · show ((enc l d).1 ++ (enc r (enc l d).2).1).length + 1
            = (n1 ++ n2 ++ [TyTree.node c l r]).length
              + (n1 ++ n2 ++ [TyTree.node c l r]).length + 1
        rw [List.length_append, hl1, hl2, List.length_append, List.length_append]
        show n1.length + n1.length + 1 + (n2.length + n2.length + 1) + 1
            = n1.length + n2.length + 1 + (n1.length + n2.length + 1) + 1
        simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · intro x hx
        cases List.mem_append.mp hx with
        | inl h =>
          cases List.mem_append.mp h with
          | inl h1 =>
            exact List.Mem.tail _ (List.mem_append.mpr (Or.inl (hs1 x h1)))
          | inr h2 =>
            exact List.Mem.tail _ (List.mem_append.mpr (Or.inr (hs2 x h2)))
        | inr h =>
          cases h with
          | head => exact List.Mem.head _
          | tail _ h' => cases h'
      · intro x hx
        cases List.mem_append.mp hx with
        | inl h =>
          cases List.mem_append.mp h with
          | inl h1 => exact hn1 x h1
          | inr h2 =>
            intro hxd
            have := hn2 x h2
            rw [hd1] at this
            exact this (List.mem_append.mpr (Or.inl hxd))
        | inr h =>
          cases h with
          | head => exact ht
          | tail _ h' => cases h'
      · refine distinct_append (n1 ++ n2) [TyTree.node c l r] ?_ ⟨(fun h => by cases h), trivial⟩ ?_
        · exact distinct_append n1 n2 hD1 hD2 (fun x h1 h2 => h21 x h2 h1)
        · intro x hx hm
          cases hm with
          | head => exact hsmall _ hx rfl
          | tail _ h' => cases h'

/-- **Theorem 3c (linear size).** If `m` lists every compound subtree of `t` — in
particular if `m` is a duplicate-free enumeration of the *distinct* compound subtrees —
then the encoding has at most `2 * m.length + 1` tokens. -/
theorem encodeV0Dag_length_le (t : TyTree) (m : List TyTree)
    (hm : ∀ x, x ∈ subterms t → x ∈ m) :
    (encodeV0Dag t).length ≤ 2 * m.length + 1 := by
  obtain ⟨new, _, hlen, hsub, _, hdist⟩ := enc_spec t []
  have hle : new.length ≤ m.length :=
    distinct_length_le new m hdist (fun x hx => hm x (hsub x hx))
  show (enc t []).1.length ≤ 2 * m.length + 1
  rw [hlen, Nat.two_mul]
  exact Nat.succ_le_succ (Nat.add_le_add hle hle)

/-! ### B.2  The shared-children tower: exponential tree, linear encoding -/

/-- `tower 0` is a basic type; `tower (n+1)` applies constructor `0` to two copies of
`tower n`. This is the `Pair<T, T>` family measured by the Rust probe. -/
noncomputable def tower : Nat → TyTree
  | 0 => .leaf 0
  | n + 1 => .node 0 (tower n) (tower n)

noncomputable def leaves : TyTree → Nat
  | .leaf _ => 1
  | .node _ l r => leaves l + leaves r

theorem leaves_tower (n : Nat) : leaves (tower n) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show leaves (tower n) + leaves (tower n) = 2 ^ (n + 1)
    rw [ih, Nat.pow_succ, Nat.mul_two]

theorem naive_length_tower (n : Nat) : (naive (tower n)).length + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (naive (tower n) ++ naive (tower n)).length + 1 + 1 = 2 ^ (n + 1 + 1)
    rw [List.length_append, Nat.pow_succ 2 (n + 1), ← ih, Nat.mul_two]
    simp only [Nat.add_comm, Nat.add_left_comm]

theorem findIdx_append_self (t : TyTree) :
    ∀ (d : List TyTree), ∃ i, findIdx t (d ++ [t]) = some i
  | [] => ⟨0, by show (if t = t then some 0 else _) = some 0; rw [ite_eq_left rfl]⟩
  | x :: xs => by
    obtain ⟨i, hi⟩ := findIdx_append_self t xs
    show ∃ i, (if x = t then some 0 else (findIdx t (xs ++ [t])).map (· + 1)) = some i
    cases (inferInstance : Decidable (x = t)) with
    | isTrue hx => exact ⟨0, by rw [ite_eq_left hx]⟩
    | isFalse hx => exact ⟨i + 1, by rw [ite_eq_right hx, hi]; rfl⟩

theorem enc_node_in_table (c : Nat) (l r : TyTree) (d : List TyTree) :
    ∃ i, findIdx (.node c l r) (enc (.node c l r) d).2 = some i := by
  cases h : findIdx (.node c l r) d with
  | some i => rw [enc_hit c l r d i h]; exact ⟨i, h⟩
  | none => rw [enc_miss c l r d h]; exact findIdx_append_self _ _

theorem enc_tower_again (n : Nat) : (enc (tower n) (enc (tower n) []).2).1.length = 1 := by
  cases n with
  | zero => rfl
  | succ k =>
    obtain ⟨i, hi⟩ := enc_node_in_table 0 (tower k) (tower k) []
    show (enc (.node 0 (tower k) (tower k)) (enc (.node 0 (tower k) (tower k)) []).2).1.length = 1
    rw [enc_hit 0 (tower k) (tower k) _ i hi]
    rfl

theorem encodeV0Dag_tower_length (n : Nat) : (encodeV0Dag (tower n)).length = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (enc (.node 0 (tower n) (tower n)) []).1.length = 2 * (n + 1) + 1
    rw [enc_miss 0 (tower n) (tower n) [] rfl]
    show ((enc (tower n) []).1 ++ (enc (tower n) (enc (tower n) []).2).1).length + 1
        = 2 * (n + 1) + 1
    rw [List.length_append, enc_tower_again n]
    have ih' : (enc (tower n) []).1.length = 2 * n + 1 := ih
    rw [ih', Nat.mul_add, Nat.mul_one]

/-- **Counterexample 3 (naive tree mangling is exponential; backreferences are linear).**
For the tower of depth `n`: the naive serialization has `2^(n+1) - 1` tokens while the
backreference encoding has `2n + 1`. At depth 10 the type has 1024 leaves, the naive
serialization 2047 tokens, and the backreference encoding 21 tokens. -/
theorem ce3_naive_tree_mangling_exponential_vs_v0_dag_linear :
    (∀ n, (naive (tower n)).length + 1 = 2 ^ (n + 1)) ∧
    (∀ n, (encodeV0Dag (tower n)).length = 2 * n + 1) ∧
    (∀ n, leaves (tower n) = 2 ^ n) ∧
    (naive (tower 10)).length + 1 = 2048 ∧
    (encodeV0Dag (tower 10)).length = 21 ∧
    leaves (tower 10) = 1024 :=
  ⟨naive_length_tower, encodeV0Dag_tower_length, leaves_tower, naive_length_tower 10,
    encodeV0Dag_tower_length 10, leaves_tower 10⟩

/-- The distinct compound subtrees of `tower n`: `tower n, …, tower 1`. -/
noncomputable def towerList : Nat → List TyTree
  | 0 => []
  | n + 1 => tower (n + 1) :: towerList n

theorem length_towerList (n : Nat) : (towerList n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => show (towerList n).length + 1 = n + 1; rw [ih]

theorem subterms_tower_mem (n : Nat) : ∀ x, x ∈ subterms (tower n) → x ∈ towerList n := by
  induction n with
  | zero => intro x hx; cases hx
  | succ n ih =>
    intro x hx
    cases hx with
    | head => exact List.Mem.head _
    | tail _ hx' =>
      cases List.mem_append.mp hx' with
      | inl h => exact List.Mem.tail _ (ih x h)
      | inr h => exact List.Mem.tail _ (ih x h)

theorem subterms_tower_length (n : Nat) : (subterms (tower n)).length + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (subterms (tower n) ++ subterms (tower n)).length + 1 + 1 = 2 ^ (n + 1)
    rw [List.length_append, Nat.pow_succ, ← ih, Nat.mul_two]
    simp only [Nat.add_comm, Nat.add_left_comm]

/-- The bound of Theorem 3c is attained on the tower: with `m` the `n` distinct compound
subtrees, the encoding has exactly `2 * m.length + 1` tokens, although the tree has
`2^n - 1` compound subtree occurrences. -/
theorem tower_bound_is_tight (n : Nat) :
    (∀ x, x ∈ subterms (tower n) → x ∈ towerList n) ∧
    (encodeV0Dag (tower n)).length = 2 * (towerList n).length + 1 ∧
    (subterms (tower n)).length + 1 = 2 ^ n := by
  refine ⟨subterms_tower_mem n, ?_, subterms_tower_length n⟩
  rw [length_towerList]
  exact encodeV0Dag_tower_length n

/-! ### B.3  Digest mangling is lossy for every digest of bounded range -/

/-- Digest-style mangling: an item path plus a digest of the type argument. -/
noncomputable def legacyMangle (h : TyTree → Nat) (path : Nat) (t : TyTree) : Nat × Nat := (path, h t)

theorem find_or_none {α : Type} (h : α → Nat) (v : Nat) :
    ∀ (l : List α), (∃ x, x ∈ l ∧ h x = v) ∨ (∀ x, x ∈ l → h x ≠ v)
  | [] => Or.inr (fun _ hx => by cases hx)
  | a :: l => by
    cases Nat.decEq (h a) v with
    | isTrue ha => exact Or.inl ⟨a, List.Mem.head _, ha⟩
    | isFalse ha =>
      cases find_or_none h v l with
      | inl hex =>
        obtain ⟨x, hx, e⟩ := hex
        exact Or.inl ⟨x, List.Mem.tail _ hx, e⟩
      | inr hall =>
        refine Or.inr (fun x hx => ?_)
        cases hx with
        | head => exact ha
        | tail _ hx' => exact hall x hx'

/-- Pigeonhole: more distinct inputs than available digests forces a collision. -/
theorem collision_of_small_range {α : Type} (h : α → Nat) :
    ∀ (ts : List α) (m : List Nat), Distinct ts → (∀ t, t ∈ ts → h t ∈ m) →
      m.length < ts.length → ∃ a b, a ∈ ts ∧ b ∈ ts ∧ a ≠ b ∧ h a = h b
  | [], _, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | t :: ts, m, hd, hin, hlt => by
    cases find_or_none h (h t) ts with
    | inl hex =>
      obtain ⟨x, hx, e⟩ := hex
      exact ⟨t, x, List.Mem.head _, List.Mem.tail _ hx,
        fun eq => hd.1 (by rw [eq]; exact hx), e.symm⟩
    | inr hall =>
      have hin' : ∀ x, x ∈ ts → h x ∈ removeFirst (h t) m := fun x hx =>
        mem_removeFirst (h t) (h x) (hall x hx) m (hin x (List.Mem.tail _ hx))
      have hlen := length_removeFirst (h t) m (hin t (List.Mem.head _))
      have hlt' : (removeFirst (h t) m).length < ts.length := by
        rw [← hlen] at hlt
        exact Nat.lt_of_succ_lt_succ hlt
      obtain ⟨a, b, ha, hb, hne, e⟩ :=
        collision_of_small_range h ts (removeFirst (h t) m) hd.2 hin' hlt'
      exact ⟨a, b, List.Mem.tail _ ha, List.Mem.tail _ hb, hne, e⟩

noncomputable def leafList : Nat → List TyTree
  | 0 => []
  | k + 1 => .leaf k :: leafList k

noncomputable def below : Nat → List Nat
  | 0 => []
  | k + 1 => k :: below k

theorem length_leafList (k : Nat) : (leafList k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => show (leafList k).length + 1 = k + 1; rw [ih]

theorem length_below (k : Nat) : (below k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => show (below k).length + 1 = k + 1; rw [ih]

theorem mem_below (k x : Nat) (h : x < k) : x ∈ below k := by
  induction k with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with
    | inl e => rw [e]; exact List.Mem.head _
    | inr hlt => exact List.Mem.tail _ (ih hlt)

theorem mem_leafList (k : Nat) : ∀ t, t ∈ leafList k → ∃ j, j < k ∧ t = TyTree.leaf j := by
  induction k with
  | zero => intro t h; cases h
  | succ k ih =>
    intro t h
    cases h with
    | head => exact ⟨k, Nat.lt_succ_self k, rfl⟩
    | tail _ h' =>
      obtain ⟨j, hj, e⟩ := ih t h'
      exact ⟨j, Nat.lt_succ_of_lt hj, e⟩

theorem distinct_leafList (k : Nat) : Distinct (leafList k) := by
  induction k with
  | zero => trivial
  | succ k ih =>
    refine ⟨?_, ih⟩
    intro hm
    obtain ⟨j, hj, e⟩ := mem_leafList k _ hm
    have : k = j := by injection e
    rw [this] at hj
    exact Nat.lt_irrefl _ hj

/-- **Theorem 4a.** For every digest `h` whose values lie below some bound `n` (any
fixed-width hash), two different types receive the same digest-mangled name. -/
theorem digest_mangling_not_injective (n : Nat) (h : TyTree → Nat) (hb : ∀ t, h t < n)
    (path : Nat) : ∃ a b, a ≠ b ∧ legacyMangle h path a = legacyMangle h path b := by
  obtain ⟨a, b, _, _, hne, e⟩ :=
    collision_of_small_range h (leafList (n + 1)) (below n) (distinct_leafList _)
      (fun t _ => mem_below n (h t) (hb t))
      (by rw [length_below, length_leafList]; exact Nat.lt_succ_self n)
  exact ⟨a, b, hne, by unfold legacyMangle; rw [e]⟩

/-- **Theorem 4b.** Consequently no function can recover the type from a digest-mangled
name, whereas `decodeV0Dag` does so for the backreference encoding (`decode_encode`). -/
theorem digest_mangling_has_no_decoder (n : Nat) (h : TyTree → Nat) (hb : ∀ t, h t < n)
    (path : Nat) :
    ¬ ∃ decode : Nat × Nat → Option TyTree, ∀ t, decode (legacyMangle h path t) = some t := by
  intro ⟨decode, hdec⟩
  obtain ⟨a, b, hne, e⟩ := digest_mangling_not_injective n h hb path
  have ha := hdec a
  rw [e, hdec b] at ha
  exact hne (Option.some.inj ha).symm

/-- 64-bit instance of Theorem 4a: whatever function is truncated to 64 bits, two
different types collide. -/
theorem digest64_mangling_collides (h : TyTree → Nat) (path : Nat) :
    ∃ a b, a ≠ b ∧
      legacyMangle (fun t => h t % 2 ^ 64) path a = legacyMangle (fun t => h t % 2 ^ 64) path b :=
  digest_mangling_not_injective (2 ^ 64) (fun t => h t % 2 ^ 64)
    (fun _ => Nat.mod_lt _ (Nat.two_pow_pos 64)) path

end TailCallMangle

/-! ## Axiom audit -/

#print axioms TailCallMangle.become_frame_reuse_and_lifo_drops
#print axioms TailCallMangle.become_preserves_depth
#print axioms TailCallMangle.scopeWalk_eq_lifo
#print axioms TailCallMangle.run_depth_le
#print axioms TailCallMangle.tail_loop_depth_const
#print axioms TailCallMangle.call_loop_depth_linear
#print axioms TailCallMangle.inline_configurations
#print axioms TailCallMangle.halts_deterministic
#print axioms TailCallMangle.naive_inline_of_tailcall_unsound
#print axioms TailCallMangle.step_fresh
#print axioms TailCallMangle.ce1_dangling_stack_borrow_across_tailcall_frame_reuse_ub
#print axioms TailCallMangle.run_fresh
#print axioms TailCallMangle.ce1_instance
#print axioms TailCallMangle.naive_inline_instance
#print axioms TailCallMangle.tail_loop_never_grows
#print axioms TailCallMangle.ce2_post_tailcall_caller_drop_violates_tail_position_and_order
#print axioms TailCallMangle.scenario_logs
#print axioms TailCallMangle.decode_encode
#print axioms TailCallMangle.encodeV0Dag_injective
#print axioms TailCallMangle.encodeV0Dag_length_le
#print axioms TailCallMangle.ce3_naive_tree_mangling_exponential_vs_v0_dag_linear
#print axioms TailCallMangle.digest_mangling_not_injective
#print axioms TailCallMangle.digest_mangling_has_no_decoder
#print axioms TailCallMangle.tower_bound_is_tight
#print axioms TailCallMangle.digest64_mangling_collides
