-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.List.Basic
import Trusted
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics
import Anneal.Core.SepPCM

namespace Anneal.PromisingReductionProof

/-!
# Operational Capped-Promise Relaxed Semantics, Invariant Reduction, and TSO

Kernel-checked theorems connecting `Ordering::Relaxed` load-buffering
(`LB+rlx`), Promising 2.0 (`PS2`) capped-memory certification, modular pure
invariant preservation without user certification proofs, release-write
promise-free reduction, and `TargetMemModel` (`portableCpp20` vs. `x86Tso`):

1. `promiseFree_forbids_lb_rlx_1_1`: Promise-free operational interleaving
   (`acyclic(sb ∪ rf)` / `ORC11`) forbids `(obs₀ = 1, obs₁ = 1)` on `LB+rlx`,
   which `rustc -O` emits as `ldr; str` on `aarch64` and `lw; sw` on
   `riscv64gc` where hardware admits `(1, 1)`.
2. `ps2_allows_lb_rlx_1_1` & `ps2_allows_lb_cond_overwrite_1_2`: Operational
   Promising 2.0 (`PS2`) over half-open intervals `(fromTs, toTs]` with
   capped-memory certification (`capMem`) admits `(1, 1)` on `LB+rlx` and
   `(1, 2)` under conditional dead-store overwrite, while `capMem` blocks
   stealable RMW certification (`ps2_cap_blocks_stealable_rmw_promise`) and
   release-fence promise draining forbids `(1, 1)` on `LB+frel+acq`
   (`ps2_forbids_lb_frel_acq_1_1`).
3. `ps2_pure_relaxed_invariant_preserved` & `ps2_forbids_oota_lb_data_dep`:
   Every promised or fulfilled message preserves any thread-inductive value
   invariant `Φ : Loc → Nat → Prop` without user certification proofs,
   immediately ruling out Out-Of-Thin-Air `(1, 1)` on `LB+data_dep`.
4. `releaseOnly_exact_bisimulation`: Programs whose shared writes all carry
   release semantics (`Release`, `AcqRel`, `SeqCst`) cannot certify any
   unfulfilled promise and are step-bisimilar to promise-free execution.
5. `tso_xchg_forbids_0_0_and_portable_allows_0_0`: `TargetMemModel.portableCpp20`
   admits `(0, 0)` on `xchg(SeqCst); compiler_fence(SeqCst); load(Acquire)`
   (matching `ARMv8.3 +rcpc` `swpal; ldapr`), whereas `TargetMemModel.x86Tso`
   drains the store buffer on `xchgq` and forbids `(0, 0)`.
-/

abbrev Tid := Nat
abbrev Loc := Nat

/-- Atomic memory ordering. -/
inductive MemOrd where
  | relaxed
  | acquire
  | release
  | acqRel
  | seqCst

/-- True iff a write or RMW ordering carries release semantics (`Release`,
`AcqRel`, `SeqCst`) and therefore cannot be promised ahead of execution. -/
def MemOrd.hasRelease (o : MemOrd) : Bool :=
  match o with
  | .relaxed => false
  | .acquire => false
  | .release => true
  | .acqRel => true
  | .seqCst => true

/-- True iff a fence ordering drains outstanding thread promises. -/
def MemOrd.drainsPromisesOnFence (o : MemOrd) : Bool :=
  match o with
  | .relaxed => false
  | .acquire => false
  | .release => true
  | .acqRel => true
  | .seqCst => true

/-- Target memory-model profile attached to a verified compilation unit. -/
inductive TargetMemModel where
  | portableCpp20
  | x86Tso

/-- Timestamped message over half-open interval `(fromTs, toTs]` (`[0, 0]` for
initial memory). `promisedBy = some tid` marks an unfulfilled `Relaxed` promise
owned by `tid`; `isCap = true` marks a synthetic `PS 2.0` cap block present only
during thread-local certification. -/
structure Msg where
  loc : Loc
  fromTs : Nat
  toTs : Nat
  val : Nat
  releasedLoc0Ts : Nat
  releasedLoc1Ts : Nat
  promisedBy : Option Tid
  isCap : Bool

def optTidBeq (a b : Option Tid) : Bool :=
  match a, b with
  | none, none => true
  | some x, some y => Nat.beq x y
  | _, _ => false

def boolBeq (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | false, false => true
  | _, _ => false

def Msg.beq (a b : Msg) : Bool :=
  Nat.beq a.loc b.loc &&
  Nat.beq a.fromTs b.fromTs &&
  Nat.beq a.toTs b.toTs &&
  Nat.beq a.val b.val &&
  Nat.beq a.releasedLoc0Ts b.releasedLoc0Ts &&
  Nat.beq a.releasedLoc1Ts b.releasedLoc1Ts &&
  optTidBeq a.promisedBy b.promisedBy &&
  boolBeq a.isCap b.isCap

/-- Two positive-length half-open intervals `(a₁, b₁]` and `(a₂, b₂]` are
disjoint iff `b₁ ≤ a₂ ∨ b₂ ≤ a₁`. -/
def IntervalsDisjoint (a₁ b₁ a₂ b₂ : Nat) : Prop :=
  b₁ ≤ a₂ ∨ b₂ ≤ a₁

/-- Thread command language covering loads, stores, RMW exchanges, and
hardware/compiler fences. -/
inductive Cmd where
  | halt
  | load (ord : MemOrd) (loc : Loc) (k : Nat → Cmd)
  | store (ord : MemOrd) (loc : Loc) (val : Nat) (next : Cmd)
  | rmwXchg (ord : MemOrd) (loc : Loc) (val : Nat) (k : Nat → Cmd)
  | fence (ord : MemOrd) (next : Cmd)
  | compilerFenceSeqCst (next : Cmd)

/-- Two-location timestamp view (`t0` for location `0`, `t1` for location `1`). -/
structure View2 where
  t0 : Nat
  t1 : Nat

def View2.bot : View2 := { t0 := 0, t1 := 0 }

def View2.get (v : View2) (loc : Loc) : Nat :=
  match loc with
  | 0 => v.t0
  | 1 => v.t1
  | _ => 0

def natMax (a b : Nat) : Nat :=
  if Nat.ble a b then b else a

def View2.bump (v : View2) (loc : Loc) (ts : Nat) : View2 :=
  match loc with
  | 0 => { v with t0 := natMax v.t0 ts }
  | 1 => { v with t1 := natMax v.t1 ts }
  | _ => v

def View2.join (a b : View2) : View2 :=
  { t0 := natMax a.t0 b.t0, t1 := natMax a.t1 b.t1 }

/-- Per-thread operational state. -/
structure ThreadState where
  cmd : Cmd
  obs : Nat
  cur : View2
  acq : View2
  rel : View2

def initThread (c : Cmd) : ThreadState :=
  { cmd := c, obs := 0, cur := View2.bot, acq := View2.bot, rel := View2.bot }

/-- True iff `m` is an unfulfilled promise owned by `tid`. -/
def Msg.isPromiseOf (m : Msg) (tid : Tid) : Bool :=
  match m.promisedBy with
  | some owner => Nat.beq owner tid
  | none => false

/-- True iff `mem` contains at least one unfulfilled promise owned by `tid`.
Defined via `List.foldr` so zero `_unsafe_rec` compiler auxiliaries are
emitted. -/
def hasPromiseBy (tid : Tid) (mem : List Msg) : Bool :=
  mem.foldr (fun m acc => m.isPromiseOf tid || acc) false

/-- Maximum `toTs` across all messages on `loc` in `mem`. -/
def maxToTs (mem : List Msg) (loc : Loc) : Nat :=
  mem.foldr (fun m acc => if Nat.beq m.loc loc then natMax acc m.toTs else acc) 0

/-- `PS 2.0` memory cap for locations `0` and `1`: attaches an adjacent cap
block `(M_max, M_max + 1]` at the current maximum timestamp on each location so
thread-local certification cannot rely on an RMW slot at `M_max` that another
thread could concurrently steal. -/
def capMem (mem : List Msg) : List Msg :=
  let m0 := maxToTs mem 0
  let m1 := maxToTs mem 1
  let c0 : Msg :=
    { loc := 0, fromTs := m0, toTs := m0 + 1, val := 0
      releasedLoc0Ts := 0, releasedLoc1Ts := 0
      promisedBy := none, isCap := true }
  let c1 : Msg :=
    { loc := 1, fromTs := m1, toTs := m1 + 1, val := 0
      releasedLoc0Ts := 0, releasedLoc1Ts := 0
      promisedBy := none, isCap := true }
  c0 :: c1 :: mem

/-- Replace every occurrence of `target` in `mem` with `promisedBy := none`. -/
def fulfillMsgInPool (target : Msg) (mem : List Msg) : List Msg :=
  mem.foldr
    (fun m acc =>
      match Msg.beq m target with
      | true => { m with promisedBy := none } :: acc
      | false => m :: acc)
    []

/-- True iff `(fromTs, toTs]` is strictly ordered and disjoint from every
non-initial interval on `loc` in `mem`. -/
def slotAvailable (mem : List Msg) (loc fromTs toTs : Nat) : Prop :=
  fromTs < toTs ∧
  ∀ m, m ∈ mem → m.loc = loc →
    (m.fromTs = 0 ∧ m.toTs = 0) ∨ IntervalsDisjoint m.fromTs m.toTs fromTs toTs

def initMsg0 : Msg :=
  { loc := 0, fromTs := 0, toTs := 0, val := 0
    releasedLoc0Ts := 0, releasedLoc1Ts := 0
    promisedBy := none, isCap := false }

def initMsg1 : Msg :=
  { loc := 1, fromTs := 0, toTs := 0, val := 0
    releasedLoc0Ts := 0, releasedLoc1Ts := 0
    promisedBy := none, isCap := false }

def initMem2 : List Msg := [initMsg0, initMsg1]

def stepLoadState (ord : MemOrd) (loc : Loc) (k : Nat → Cmd)
    (cur acq rel : View2) (m : Msg) : ThreadState :=
  let msgRel : View2 := { t0 := m.releasedLoc0Ts, t1 := m.releasedLoc1Ts }
  let cur1 := cur.bump loc m.toTs
  let cur2 :=
    match ord with
    | .acquire | .acqRel | .seqCst => cur1.join msgRel
    | _ => cur1
  let acq2 := (acq.bump loc m.toTs).join msgRel
  { cmd := k m.val, obs := m.val, cur := cur2, acq := acq2, rel := rel }

def stepStoreState (loc toTs : Nat) (next : Cmd)
    (obs : Nat) (cur acq rel : View2) : ThreadState :=
  { cmd := next, obs := obs, cur := cur.bump loc toTs, acq := acq.bump loc toTs, rel := rel }

def stepStoreMsg (ord : MemOrd) (loc val fromTs toTs : Nat)
    (cur rel : View2) : Msg :=
  let cur' := cur.bump loc toTs
  let exported := if ord.hasRelease then cur' else rel.bump loc toTs
  { loc := loc, fromTs := fromTs, toTs := toTs, val := val
    releasedLoc0Ts := exported.t0, releasedLoc1Ts := exported.t1
    promisedBy := none, isCap := false }

def stepRmwState (ord : MemOrd) (loc toTs : Nat) (k : Nat → Cmd)
    (cur acq rel : View2) (base : Msg) : ThreadState :=
  let baseRel : View2 := { t0 := base.releasedLoc0Ts, t1 := base.releasedLoc1Ts }
  let curRead :=
    match ord with
    | .acquire | .acqRel | .seqCst => (cur.bump loc base.toTs).join baseRel
    | _ => cur.bump loc base.toTs
  let cur' := curRead.bump loc toTs
  let acq' := ((acq.bump loc base.toTs).join baseRel).bump loc toTs
  { cmd := k base.val, obs := base.val, cur := cur', acq := acq', rel := rel }

def stepRmwMsg (ord : MemOrd) (loc val toTs : Nat)
    (cur rel : View2) (base : Msg) : Msg :=
  let baseRel : View2 := { t0 := base.releasedLoc0Ts, t1 := base.releasedLoc1Ts }
  let curRead :=
    match ord with
    | .acquire | .acqRel | .seqCst => (cur.bump loc base.toTs).join baseRel
    | _ => cur.bump loc base.toTs
  let cur' := curRead.bump loc toTs
  let exported :=
    if ord.hasRelease then cur'.join baseRel else (rel.bump loc toTs).join baseRel
  { loc := loc, fromTs := base.toTs, toTs := toTs, val := val
    releasedLoc0Ts := exported.t0, releasedLoc1Ts := exported.t1
    promisedBy := none, isCap := false }

def stepFenceState (ord : MemOrd) (next : Cmd)
    (obs : Nat) (cur acq rel : View2) : ThreadState :=
  let cur' :=
    match ord with
    | .acquire | .acqRel | .seqCst => acq
    | _ => cur
  let rel' :=
    match ord with
    | .release | .acqRel | .seqCst => cur'
    | _ => rel
  { cmd := next, obs := obs, cur := cur', acq := acq, rel := rel' }

/-! ## 1. Promise-Free Operational Execution Forbids `LB+rlx` `(1, 1)` -/

inductive PromiseFreeThreadStep (tid : Tid) :
    ThreadState → List Msg → ThreadState → List Msg → Prop where
  | load (ord : MemOrd) (loc : Loc) (k : Nat → Cmd)
      (obs : Nat) (cur acq rel : View2) (mem : List Msg) (m : Msg) :
      m ∈ mem →
      m.loc = loc →
      m.isCap = false →
      m.promisedBy = none →
      cur.get loc ≤ m.toTs →
      PromiseFreeThreadStep tid
        { cmd := Cmd.load ord loc k, obs := obs, cur := cur, acq := acq, rel := rel }
        mem
        (stepLoadState ord loc k cur acq rel m)
        mem
  | store (ord : MemOrd) (loc val : Nat) (next : Cmd)
      (obs : Nat) (cur acq rel : View2) (mem : List Msg) (fromTs toTs : Nat) :
      slotAvailable mem loc fromTs toTs →
      cur.get loc ≤ fromTs →
      PromiseFreeThreadStep tid
        { cmd := Cmd.store ord loc val next, obs := obs, cur := cur, acq := acq, rel := rel }
        mem
        (stepStoreState loc toTs next obs cur acq rel)
        (stepStoreMsg ord loc val fromTs toTs cur rel :: mem)
  | rmwXchg (ord : MemOrd) (loc val : Nat) (k : Nat → Cmd)
      (obs : Nat) (cur acq rel : View2) (mem : List Msg) (base : Msg) (toTs : Nat) :
      base ∈ mem →
      base.loc = loc →
      base.isCap = false →
      base.promisedBy = none →
      cur.get loc ≤ base.toTs →
      slotAvailable mem loc base.toTs toTs →
      PromiseFreeThreadStep tid
        { cmd := Cmd.rmwXchg ord loc val k, obs := obs, cur := cur, acq := acq, rel := rel }
        mem
        (stepRmwState ord loc toTs k cur acq rel base)
        (stepRmwMsg ord loc val toTs cur rel base :: mem)
  | fence (ord : MemOrd) (next : Cmd) (obs : Nat) (cur acq rel : View2) (mem : List Msg) :
      PromiseFreeThreadStep tid
        { cmd := Cmd.fence ord next, obs := obs, cur := cur, acq := acq, rel := rel }
        mem
        (stepFenceState ord next obs cur acq rel)
        mem
  | compilerFenceSeqCst (next : Cmd) (obs : Nat) (cur acq rel : View2) (mem : List Msg) :
      PromiseFreeThreadStep tid
        { cmd := Cmd.compilerFenceSeqCst next, obs := obs, cur := cur, acq := acq, rel := rel }
        mem
        { cmd := next, obs := obs, cur := cur, acq := acq, rel := rel }
        mem

structure PFConfig2 where
  t0 : ThreadState
  t1 : ThreadState
  mem : List Msg

inductive PFStep2 : PFConfig2 → PFConfig2 → Prop where
  | step0 {s0 s0' s1 mem mem'} :
      PromiseFreeThreadStep 0 s0 mem s0' mem' →
      PFStep2 { t0 := s0, t1 := s1, mem := mem } { t0 := s0', t1 := s1, mem := mem' }
  | step1 {s0 s1 s1' mem mem'} :
      PromiseFreeThreadStep 1 s1 mem s1' mem' →
      PFStep2 { t0 := s0, t1 := s1, mem := mem } { t0 := s0, t1 := s1', mem := mem' }

inductive PFReachable2 : PFConfig2 → PFConfig2 → Prop where
  | refl (c : PFConfig2) : PFReachable2 c c
  | tail {a b c : PFConfig2} : PFReachable2 a b → PFStep2 b c → PFReachable2 a c

def lbStoreTail (writeLoc : Loc) : Cmd :=
  Cmd.store .relaxed writeLoc 1 Cmd.halt

def lbRlxThread (readLoc writeLoc : Loc) : Cmd :=
  Cmd.load .relaxed readLoc (fun _ => lbStoreTail writeLoc)

def lbRlxInitPF : PFConfig2 :=
  { t0 := initThread (lbRlxThread 0 1)
    t1 := initThread (lbRlxThread 1 0)
    mem := initMem2 }

def lbRlxPFInv (c : PFConfig2) : Prop :=
  (c.t0.cmd = lbRlxThread 0 1 ∧ c.t1.cmd = lbRlxThread 1 0 ∧
    c.t0.obs = 0 ∧ c.t1.obs = 0 ∧
    ∀ m, m ∈ c.mem → m.val = 0) ∨
  ((c.t0.cmd = lbStoreTail 1 ∨ c.t0.cmd = Cmd.halt) ∧ c.t0.obs = 0 ∧
    (c.t1.cmd = lbRlxThread 1 0 ∨ c.t1.cmd = lbStoreTail 0 ∨ c.t1.cmd = Cmd.halt)) ∨
  ((c.t1.cmd = lbStoreTail 0 ∨ c.t1.cmd = Cmd.halt) ∧ c.t1.obs = 0 ∧
    (c.t0.cmd = lbRlxThread 0 1 ∨ c.t0.cmd = lbStoreTail 1 ∨ c.t0.cmd = Cmd.halt))

private theorem initMem2_vals_zero : ∀ m, m ∈ initMem2 → m.val = 0 := by
  intro m hm
  cases hm with
  | head _ => rfl
  | tail _ hm2 =>
    cases hm2 with
    | head _ => rfl
    | tail _ hnil => nomatch hnil

private theorem step_lb_cmd_progress {tid : Tid} {rl wl : Loc} {s s' : ThreadState}
    {mem mem' : List Msg}
    (hc : s.cmd = lbRlxThread rl wl ∨ s.cmd = lbStoreTail wl ∨ s.cmd = Cmd.halt)
    (hs : PromiseFreeThreadStep tid s mem s' mem') :
    s'.cmd = lbRlxThread rl wl ∨ s'.cmd = lbStoreTail wl ∨ s'.cmd = Cmd.halt := by
  cases hc with
  | inl hload =>
    cases s with
    | mk cmd obs cur acq rel =>
      dsimp at hload
      subst hload
      cases hs with
      | load _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact Or.inr (Or.inl rfl)
  | inr hrest =>
    cases hrest with
    | inl hstore =>
      cases s with
      | mk cmd obs cur acq rel =>
        dsimp at hstore
        subst hstore
        cases hs with
        | store _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          exact Or.inr (Or.inr rfl)
    | inr hhalt =>
      cases s with
      | mk cmd obs cur acq rel =>
        dsimp at hhalt
        subst hhalt
        nomatch hs

private theorem step_postload_obs_preserved {tid : Tid} {wl : Loc} {s s' : ThreadState}
    {mem mem' : List Msg}
    (hc : s.cmd = lbStoreTail wl ∨ s.cmd = Cmd.halt)
    (hs : PromiseFreeThreadStep tid s mem s' mem') :
    (s'.cmd = lbStoreTail wl ∨ s'.cmd = Cmd.halt) ∧ s'.obs = s.obs := by
  cases hc with
  | inl hstore =>
    cases s with
    | mk cmd obs cur acq rel =>
      dsimp at hstore
      subst hstore
      cases hs with
      | store _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact ⟨Or.inr rfl, rfl⟩
  | inr hhalt =>
    cases s with
    | mk cmd obs cur acq rel =>
      dsimp at hhalt
      subst hhalt
      nomatch hs

theorem lbRlxPFInv_step {c c' : PFConfig2}
    (hinv : lbRlxPFInv c) (hstep : PFStep2 c c') : lbRlxPFInv c' := by
  cases hstep with
  | step0 hs0 =>
    cases hinv with
    | inl hinit =>
      let ⟨ht0, ht1, _, _, hall0⟩ := hinit
      cases hs0 with
      | load _ _ _ _ _ _ _ _ m hm _ _ _ _ =>
        dsimp [lbRlxThread] at ht0
        injection ht0 with _ _ hk
        subst hk
        have hm0 : m.val = 0 := hall0 m hm
        exact Or.inr (Or.inl ⟨Or.inl rfl, hm0, Or.inl ht1⟩)
      | store _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        dsimp [lbRlxThread] at ht0; nomatch ht0
      | rmwXchg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        dsimp [lbRlxThread] at ht0; nomatch ht0
      | fence _ _ _ _ _ _ _ =>
        dsimp [lbRlxThread] at ht0; nomatch ht0
      | compilerFenceSeqCst _ _ _ _ _ _ =>
        dsimp [lbRlxThread] at ht0; nomatch ht0
    | inr hrest =>
      cases hrest with
      | inl hb =>
        let ⟨ht0_post, hobs0, ht1_any⟩ := hb
        let ⟨ht0', hobs0'⟩ := step_postload_obs_preserved ht0_post hs0
        rw [hobs0] at hobs0'
        exact Or.inr (Or.inl ⟨ht0', hobs0', ht1_any⟩)
      | inr hc =>
        let ⟨ht1_post, hobs1, ht0_any⟩ := hc
        have ht0' := step_lb_cmd_progress ht0_any hs0
        exact Or.inr (Or.inr ⟨ht1_post, hobs1, ht0'⟩)
  | step1 hs1 =>
    cases hinv with
    | inl hinit =>
      let ⟨ht0, ht1, _, _, hall0⟩ := hinit
      cases hs1 with
      | load _ _ _ _ _ _ _ _ m hm _ _ _ _ =>
        dsimp [lbRlxThread] at ht1
        injection ht1 with _ _ hk
        subst hk
        have hm0 : m.val = 0 := hall0 m hm
        exact Or.inr (Or.inr ⟨Or.inl rfl, hm0, Or.inl ht0⟩)
      | store _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        dsimp [lbRlxThread] at ht1; nomatch ht1
      | rmwXchg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        dsimp [lbRlxThread] at ht1; nomatch ht1
      | fence _ _ _ _ _ _ _ =>
        dsimp [lbRlxThread] at ht1; nomatch ht1
      | compilerFenceSeqCst _ _ _ _ _ _ =>
        dsimp [lbRlxThread] at ht1; nomatch ht1
    | inr hrest =>
      cases hrest with
      | inl hb =>
        let ⟨ht0_post, hobs0, ht1_any⟩ := hb
        have ht1' := step_lb_cmd_progress ht1_any hs1
        exact Or.inr (Or.inl ⟨ht0_post, hobs0, ht1'⟩)
      | inr hc =>
        let ⟨ht1_post, hobs1, ht0_any⟩ := hc
        let ⟨ht1', hobs1'⟩ := step_postload_obs_preserved ht1_post hs1
        rw [hobs1] at hobs1'
        exact Or.inr (Or.inr ⟨ht1', hobs1', ht0_any⟩)

/-- **Theorem 1 (`promiseFree_forbids_lb_rlx_1_1`):** Every reachable state of
`LB+rlx` under promise-free execution forbids `(obs₀ = 1, obs₁ = 1)`. -/
theorem promiseFree_forbids_lb_rlx_1_1 (c : PFConfig2)
    (hreach : PFReachable2 lbRlxInitPF c) :
    ¬ (c.t0.obs = 1 ∧ c.t1.obs = 1) := by
  have hinv : lbRlxPFInv c := by
    induction hreach with
    | refl => exact Or.inl ⟨rfl, rfl, rfl, rfl, initMem2_vals_zero⟩
    | tail _ hstep ih => exact lbRlxPFInv_step ih hstep
  intro ⟨h0, h1⟩
  cases hinv with
  | inl hinit =>
    let ⟨_, _, hobs0, _, _⟩ := hinit
    rw [hobs0] at h0; nomatch h0
  | inr hrest =>
    cases hrest with
    | inl hb =>
      let ⟨_, hobs0, _⟩ := hb
      rw [hobs0] at h0; nomatch h0
    | inr hc =>
      let ⟨_, hobs1, _⟩ := hc
      rw [hobs1] at h1; nomatch h1

/-! ## 2. Operational Promising 2.0 (`PS2`) with Capped-Memory Certification -/

/-- Single thread-local physical or certification execution step for `tid`.
Reads forbid reading synthetic caps (`isCap = false`) and `tid`'s own
unfulfilled promises (`m.isPromiseOf tid = false`). Release/AcqRel/SeqCst fences
require draining `tid`'s promises (`hasPromiseBy tid mem = false`). -/
inductive CertStep (tid : Tid) :
    ThreadState → List Msg → ThreadState → List Msg → Prop where
  | load (ord : MemOrd) (loc : Loc) (k : Nat → Cmd)
      (obs : Nat) (cur acq rel : View2) (mem : List Msg) (m : Msg) :
      m ∈ mem →
      m.loc = loc →
      m.isCap = false →
      m.isPromiseOf tid = false →
      cur.get loc ≤ m.toTs →
      CertStep tid
        { cmd := Cmd.load ord loc k, obs := obs, cur := cur, acq := acq, rel := rel }
        mem
        (stepLoadState ord loc k cur acq rel m)
        mem
  | storeFresh (ord : MemOrd) (loc val : Nat) (next : Cmd)
      (obs : Nat) (cur acq rel : View2) (mem : List Msg) (fromTs toTs : Nat) :
      slotAvailable mem loc fromTs toTs →
      cur.get loc ≤ fromTs →
      CertStep tid
        { cmd := Cmd.store ord loc val next, obs := obs, cur := cur, acq := acq, rel := rel }
        mem
        (stepStoreState loc toTs next obs cur acq rel)
        (stepStoreMsg ord loc val fromTs toTs cur rel :: mem)
  | fulfillStore (loc val : Nat) (next : Cmd)
      (obs : Nat) (cur acq rel : View2) (mem : List Msg) (target : Msg) :
      target ∈ mem →
      target.loc = loc →
      target.val = val →
      target.isCap = false →
      target.promisedBy = some tid →
      cur.get loc ≤ target.fromTs →
      target.releasedLoc0Ts = (rel.bump loc target.toTs).t0 →
      target.releasedLoc1Ts = (rel.bump loc target.toTs).t1 →
      CertStep tid
        { cmd := Cmd.store .relaxed loc val next, obs := obs, cur := cur, acq := acq, rel := rel }
        mem
        (stepStoreState loc target.toTs next obs cur acq rel)
        (fulfillMsgInPool target mem)
  | rmwXchg (ord : MemOrd) (loc val : Nat) (k : Nat → Cmd)
      (obs : Nat) (cur acq rel : View2) (mem : List Msg) (base : Msg) (toTs : Nat) :
      base ∈ mem →
      base.loc = loc →
      base.isCap = false →
      base.isPromiseOf tid = false →
      cur.get loc ≤ base.toTs →
      slotAvailable mem loc base.toTs toTs →
      CertStep tid
        { cmd := Cmd.rmwXchg ord loc val k, obs := obs, cur := cur, acq := acq, rel := rel }
        mem
        (stepRmwState ord loc toTs k cur acq rel base)
        (stepRmwMsg ord loc val toTs cur rel base :: mem)
  | fence (ord : MemOrd) (next : Cmd) (obs : Nat) (cur acq rel : View2) (mem : List Msg) :
      (ord.drainsPromisesOnFence = false ∨ hasPromiseBy tid mem = false) →
      CertStep tid
        { cmd := Cmd.fence ord next, obs := obs, cur := cur, acq := acq, rel := rel }
        mem
        (stepFenceState ord next obs cur acq rel)
        mem
  | compilerFenceSeqCst (next : Cmd) (obs : Nat) (cur acq rel : View2) (mem : List Msg) :
      CertStep tid
        { cmd := Cmd.compilerFenceSeqCst next, obs := obs, cur := cur, acq := acq, rel := rel }
        mem
        { cmd := next, obs := obs, cur := cur, acq := acq, rel := rel }
        mem

/-- Finite thread-local execution sequence for certification. -/
inductive CertSteps (tid : Tid) :
    ThreadState → List Msg → ThreadState → List Msg → Prop where
  | refl (s : ThreadState) (mem : List Msg) : CertSteps tid s mem s mem
  | head {s₁ s₂ s₃ : ThreadState} {m₁ m₂ m₃ : List Msg} :
      CertStep tid s₁ m₁ s₂ m₂ →
      CertSteps tid s₂ m₂ s₃ m₃ →
      CertSteps tid s₁ m₁ s₃ m₃

/-- `PS 2.0` capped-memory certification predicate: starting from `(s, capMem mem)`,
`tid` can fulfill all of its outstanding promises in finitely many thread-local
steps. -/
def Certified (tid : Tid) (s : ThreadState) (mem : List Msg) : Prop :=
  ∃ sEnd memEnd,
    CertSteps tid s (capMem mem) sEnd memEnd ∧
    hasPromiseBy tid memEnd = false

def makePromiseMsg (tid : Tid) (s : ThreadState) (loc val fromTs toTs : Nat) : Msg :=
  let exp := s.rel.bump loc toTs
  { loc := loc, fromTs := fromTs, toTs := toTs, val := val
    releasedLoc0Ts := exp.t0, releasedLoc1Ts := exp.t1
    promisedBy := some tid, isCap := false }

/-- Operational `PS2` per-thread step: either allocate a certified `Relaxed`
write promise, or take a real execution step whose post-state either holds zero
promises or remains `Certified`. -/
inductive PS2ThreadStep (tid : Tid) :
    ThreadState → List Msg → ThreadState → List Msg → Prop where
  | promise {s : ThreadState} {mem : List Msg} (loc val fromTs toTs : Nat) :
      slotAvailable mem loc fromTs toTs →
      s.cur.get loc ≤ fromTs →
      Certified tid s (makePromiseMsg tid s loc val fromTs toTs :: mem) →
      PS2ThreadStep tid s mem s (makePromiseMsg tid s loc val fromTs toTs :: mem)
  | exec {s s' : ThreadState} {mem mem' : List Msg} :
      CertStep tid s mem s' mem' →
      (hasPromiseBy tid mem' = false ∨ Certified tid s' mem') →
      PS2ThreadStep tid s mem s' mem'

structure PS2Config2 where
  t0 : ThreadState
  t1 : ThreadState
  mem : List Msg

inductive PS2Step2 : PS2Config2 → PS2Config2 → Prop where
  | step0 {s0 s0' s1 mem mem'} :
      PS2ThreadStep 0 s0 mem s0' mem' →
      PS2Step2 { t0 := s0, t1 := s1, mem := mem } { t0 := s0', t1 := s1, mem := mem' }
  | step1 {s0 s1 s1' mem mem'} :
      PS2ThreadStep 1 s1 mem s1' mem' →
      PS2Step2 { t0 := s0, t1 := s1, mem := mem } { t0 := s0, t1 := s1', mem := mem' }

inductive PS2Reachable2 : PS2Config2 → PS2Config2 → Prop where
  | refl (c : PS2Config2) : PS2Reachable2 c c
  | tail {a b c : PS2Config2} : PS2Reachable2 a b → PS2Step2 b c → PS2Reachable2 a c

def lbRlxInitPS2 : PS2Config2 :=
  { t0 := initThread (lbRlxThread 0 1)
    t1 := initThread (lbRlxThread 1 0)
    mem := initMem2 }

def promY1 : Msg :=
  { loc := 1, fromTs := 2, toTs := 4, val := 1
    releasedLoc0Ts := 0, releasedLoc1Ts := 4
    promisedBy := some 0, isCap := false }

def msgX1 : Msg :=
  { loc := 0, fromTs := 2, toTs := 4, val := 1
    releasedLoc0Ts := 4, releasedLoc1Ts := 0
    promisedBy := none, isCap := false }

private theorem slot_promY1_initMem2 : slotAvailable initMem2 1 2 4 := by
  refine ⟨by decide, ?_⟩
  intro m hm hloc
  cases hm with
  | head _ => nomatch hloc
  | tail _ hm2 =>
    cases hm2 with
    | head _ => exact Or.inl ⟨rfl, rfl⟩
    | tail _ hnil => nomatch hnil

private theorem slot_msgX1_after_promY1 : slotAvailable (promY1 :: initMem2) 0 2 4 := by
  refine ⟨by decide, ?_⟩
  intro m hm hloc
  cases hm with
  | head _ => nomatch hloc
  | tail _ hm1 =>
    cases hm1 with
    | head _ => exact Or.inl ⟨rfl, rfl⟩
    | tail _ hm2 =>
      cases hm2 with
      | head _ => nomatch hloc
      | tail _ hnil => nomatch hnil

/-- **Theorem 2a (`ps2_allows_lb_rlx_1_1`):** Operational `PS2` admits a
promise-fulfilled terminal state of `LB+rlx` with `(obs₀ = 1, obs₁ = 1)`
(`hasPromiseBy 0 mem = false ∧ hasPromiseBy 1 mem = false`), matching `ARMv8`
and `RVWMO` hardware. -/
theorem ps2_allows_lb_rlx_1_1 :
    ∃ c : PS2Config2,
      PS2Reachable2 lbRlxInitPS2 c ∧
      c.t0.cmd = Cmd.halt ∧
      c.t1.cmd = Cmd.halt ∧
      hasPromiseBy 0 c.mem = false ∧
      hasPromiseBy 1 c.mem = false ∧
      c.t0.obs = 1 ∧
      c.t1.obs = 1 := by
  -- Step 1: Thread 0 promises `promY1` (`loc = 1, (2, 4], val = 1`).
  have hcert1 : Certified 0 (initThread (lbRlxThread 0 1)) (promY1 :: initMem2) := by
    let memC := capMem (promY1 :: initMem2)
    have hm0_in : initMsg0 ∈ memC :=
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hs_load : CertStep 0 (initThread (lbRlxThread 0 1)) memC
        { cmd := lbStoreTail 1, obs := 0, cur := View2.bot, acq := View2.bot, rel := View2.bot }
        memC :=
      CertStep.load .relaxed 0 (fun _ => lbStoreTail 1) 0 View2.bot View2.bot View2.bot
        memC initMsg0 hm0_in rfl rfl rfl (by decide)
    have hp_in : promY1 ∈ memC :=
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    have hs_fulfill : CertStep 0
        { cmd := lbStoreTail 1, obs := 0, cur := View2.bot, acq := View2.bot, rel := View2.bot }
        memC
        { cmd := Cmd.halt, obs := 0, cur := { t0 := 0, t1 := 4 }
          acq := { t0 := 0, t1 := 4 }, rel := View2.bot }
        (fulfillMsgInPool promY1 memC) :=
      CertStep.fulfillStore 1 1 Cmd.halt 0 View2.bot View2.bot View2.bot
        memC promY1 hp_in rfl rfl rfl rfl (by decide) rfl rfl
    exact ⟨_, _, CertSteps.head hs_load (CertSteps.head hs_fulfill (CertSteps.refl _ _)), rfl⟩
  have hstep1 : PS2Step2 lbRlxInitPS2
      { t0 := initThread (lbRlxThread 0 1)
        t1 := initThread (lbRlxThread 1 0)
        mem := promY1 :: initMem2 } :=
    PS2Step2.step0 (PS2ThreadStep.promise 1 1 2 4 slot_promY1_initMem2 (by decide) hcert1)
  -- Step 2: Thread 1 reads `promY1` (`obs₁ := 1`).
  let mem1 := promY1 :: initMem2
  let t1AfterLoad : ThreadState :=
    { cmd := lbStoreTail 0, obs := 1, cur := { t0 := 0, t1 := 4 }
      acq := { t0 := 0, t1 := 4 }, rel := View2.bot }
  have hs2 : CertStep 1 (initThread (lbRlxThread 1 0)) mem1 t1AfterLoad mem1 :=
    CertStep.load .relaxed 1 (fun _ => lbStoreTail 0) 0 View2.bot View2.bot View2.bot
      mem1 promY1 (List.Mem.head _) rfl rfl rfl (by decide)
  have hstep2 : PS2Step2
      { t0 := initThread (lbRlxThread 0 1), t1 := initThread (lbRlxThread 1 0), mem := mem1 }
      { t0 := initThread (lbRlxThread 0 1), t1 := t1AfterLoad, mem := mem1 } :=
    PS2Step2.step1 (PS2ThreadStep.exec hs2 (Or.inl rfl))
  -- Step 3: Thread 1 stores `msgX1` (`loc = 0, (2, 4], val = 1`).
  let mem2 := msgX1 :: mem1
  let t1Halted : ThreadState :=
    { cmd := Cmd.halt, obs := 1, cur := { t0 := 4, t1 := 4 }
      acq := { t0 := 4, t1 := 4 }, rel := View2.bot }
  have hs3 : CertStep 1 t1AfterLoad mem1 t1Halted mem2 :=
    CertStep.storeFresh .relaxed 0 1 Cmd.halt 1 { t0 := 0, t1 := 4 } { t0 := 0, t1 := 4 }
      View2.bot mem1 2 4 slot_msgX1_after_promY1 (by decide)
  have hstep3 : PS2Step2
      { t0 := initThread (lbRlxThread 0 1), t1 := t1AfterLoad, mem := mem1 }
      { t0 := initThread (lbRlxThread 0 1), t1 := t1Halted, mem := mem2 } :=
    PS2Step2.step1 (PS2ThreadStep.exec hs3 (Or.inl rfl))
  -- Step 4: Thread 0 reads `msgX1` (`obs₀ := 1`) and certifies remaining `promY1`.
  let t0AfterLoad : ThreadState :=
    { cmd := lbStoreTail 1, obs := 1, cur := { t0 := 4, t1 := 0 }
      acq := { t0 := 4, t1 := 0 }, rel := View2.bot }
  have hs4 : CertStep 0 (initThread (lbRlxThread 0 1)) mem2 t0AfterLoad mem2 :=
    CertStep.load .relaxed 0 (fun _ => lbStoreTail 1) 0 View2.bot View2.bot View2.bot
      mem2 msgX1 (List.Mem.head _) rfl rfl rfl (by decide)
  have hcert4 : Certified 0 t0AfterLoad mem2 := by
    let mem2C := capMem mem2
    have hp2_in : promY1 ∈ mem2C :=
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hs_f : CertStep 0 t0AfterLoad mem2C
        { cmd := Cmd.halt, obs := 1, cur := { t0 := 4, t1 := 4 }
          acq := { t0 := 4, t1 := 4 }, rel := View2.bot }
        (fulfillMsgInPool promY1 mem2C) :=
      CertStep.fulfillStore 1 1 Cmd.halt 1 { t0 := 4, t1 := 0 } { t0 := 4, t1 := 0 }
        View2.bot mem2C promY1 hp2_in rfl rfl rfl rfl (by decide) rfl rfl
    exact ⟨_, _, CertSteps.head hs_f (CertSteps.refl _ _), rfl⟩
  have hstep4 : PS2Step2
      { t0 := initThread (lbRlxThread 0 1), t1 := t1Halted, mem := mem2 }
      { t0 := t0AfterLoad, t1 := t1Halted, mem := mem2 } :=
    PS2Step2.step0 (PS2ThreadStep.exec hs4 (Or.inr hcert4))
  -- Step 5: Thread 0 fulfills `promY1` (`hasPromiseBy 0 mem3 = false`).
  let mem3 := fulfillMsgInPool promY1 mem2
  let t0Halted : ThreadState :=
    { cmd := Cmd.halt, obs := 1, cur := { t0 := 4, t1 := 4 }
      acq := { t0 := 4, t1 := 4 }, rel := View2.bot }
  have hs5 : CertStep 0 t0AfterLoad mem2 t0Halted mem3 :=
    CertStep.fulfillStore 1 1 Cmd.halt 1 { t0 := 4, t1 := 0 } { t0 := 4, t1 := 0 }
      View2.bot mem2 promY1 (List.Mem.tail _ (List.Mem.head _)) rfl rfl rfl rfl (by decide) rfl rfl
  have hstep5 : PS2Step2
      { t0 := t0AfterLoad, t1 := t1Halted, mem := mem2 }
      { t0 := t0Halted, t1 := t1Halted, mem := mem3 } :=
    PS2Step2.step0 (PS2ThreadStep.exec hs5 (Or.inl rfl))
  have hreach : PS2Reachable2 lbRlxInitPS2 { t0 := t0Halted, t1 := t1Halted, mem := mem3 } :=
    PS2Reachable2.tail
      (PS2Reachable2.tail
        (PS2Reachable2.tail
          (PS2Reachable2.tail
            (PS2Reachable2.tail (PS2Reachable2.refl _) hstep1)
            hstep2)
          hstep3)
        hstep4)
      hstep5
  exact ⟨_, hreach, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Conditional dead-store overwrite (`LB+cond_overwrite`):
Thread 0: `r0 = load(0, Rlx); if r0 == 0 { store(1, 1, Rlx) }; store(1, 2, Rlx)`
Thread 1: `r1 = load(1, Rlx); if r1 == 2 { store(0, 1, Rlx) }`.
Tests dense interval splitting `(1, 3]` below an unfulfilled promise `(4, 6]`. -/
def lbCondOverwriteT0 : Cmd :=
  Cmd.load .relaxed 0 (fun r =>
    if Nat.beq r 0 then
      Cmd.store .relaxed 1 1 (Cmd.store .relaxed 1 2 Cmd.halt)
    else
      Cmd.store .relaxed 1 2 Cmd.halt)

def lbCondOverwriteT1 : Cmd :=
  Cmd.load .relaxed 1 (fun r =>
    if Nat.beq r 2 then
      Cmd.store .relaxed 0 1 Cmd.halt
    else
      Cmd.halt)

def promY2 : Msg :=
  { loc := 1, fromTs := 4, toTs := 6, val := 2
    releasedLoc0Ts := 0, releasedLoc1Ts := 6
    promisedBy := some 0, isCap := false }

def msgX1FromCond : Msg :=
  { loc := 0, fromTs := 2, toTs := 4, val := 1
    releasedLoc0Ts := 4, releasedLoc1Ts := 0
    promisedBy := none, isCap := false }

/-- **Theorem 2b (`ps2_allows_lb_cond_overwrite_1_2`):** `PS2` admits `(obs₀ = 1,
obs₁ = 2)` on `LB+cond_overwrite`: during initial certification (`r0 = 0`),
Thread 0 inserts the intermediate store `val = 1` into the open sub-interval
`(1, 3]` strictly below promised `(4, 6]`, and in real execution (`r0 = 1`)
skips the `if` branch and fulfills `(4, 6]` directly. -/
theorem ps2_allows_lb_cond_overwrite_1_2 :
    ∃ c : PS2Config2,
      PS2Reachable2
        { t0 := initThread lbCondOverwriteT0
          t1 := initThread lbCondOverwriteT1
          mem := initMem2 } c ∧
      c.t0.cmd = Cmd.halt ∧
      c.t1.cmd = Cmd.halt ∧
      hasPromiseBy 0 c.mem = false ∧
      hasPromiseBy 1 c.mem = false ∧
      c.t0.obs = 1 ∧
      c.t1.obs = 2 := by
  have hslot_prom : slotAvailable initMem2 1 4 6 := by
    refine ⟨by decide, ?_⟩
    intro m hm hloc
    cases hm with
    | head _ => nomatch hloc
    | tail _ hm2 =>
      cases hm2 with
      | head _ => exact Or.inl ⟨rfl, rfl⟩
      | tail _ hnil => nomatch hnil
  have hcert1 : Certified 0 (initThread lbCondOverwriteT0) (promY2 :: initMem2) := by
    let memC := capMem (promY2 :: initMem2)
    have hm0_in : initMsg0 ∈ memC :=
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hs_load : CertStep 0 (initThread lbCondOverwriteT0) memC
        { cmd := Cmd.store .relaxed 1 1 (Cmd.store .relaxed 1 2 Cmd.halt)
          obs := 0, cur := View2.bot, acq := View2.bot, rel := View2.bot }
        memC :=
      CertStep.load .relaxed 0 _ 0 View2.bot View2.bot View2.bot
        memC initMsg0 hm0_in rfl rfl rfl (by decide)
    have hslot_split : slotAvailable memC 1 1 3 := by
      refine ⟨by decide, ?_⟩
      intro m hm hloc
      dsimp [memC, capMem, initMem2] at hm
      cases hm with
      | head _ => nomatch hloc
      | tail _ hm1 =>
        cases hm1 with
        | head _ =>
          -- Top cap on loc 1 is `(6, 7]`; `3 ≤ 6`!
          exact Or.inr (Or.inr (by decide))
        | tail _ hm2 =>
          cases hm2 with
          | head _ =>
            -- `promY2` is `(4, 6]`; `3 ≤ 4`!
            exact Or.inr (Or.inr (by decide))
          | tail _ hm3 =>
            cases hm3 with
            | head _ => nomatch hloc
            | tail _ hm4 =>
              cases hm4 with
              | head _ => exact Or.inl ⟨rfl, rfl⟩
              | tail _ hnil => nomatch hnil
    let msgSplit : Msg :=
      { loc := 1, fromTs := 1, toTs := 3, val := 1
        releasedLoc0Ts := 0, releasedLoc1Ts := 3
        promisedBy := none, isCap := false }
    have hs_store1 : CertStep 0
        { cmd := Cmd.store .relaxed 1 1 (Cmd.store .relaxed 1 2 Cmd.halt)
          obs := 0, cur := View2.bot, acq := View2.bot, rel := View2.bot }
        memC
        { cmd := Cmd.store .relaxed 1 2 Cmd.halt
          obs := 0, cur := { t0 := 0, t1 := 3 }, acq := { t0 := 0, t1 := 3 }, rel := View2.bot }
        (msgSplit :: memC) :=
      CertStep.storeFresh .relaxed 1 1 (Cmd.store .relaxed 1 2 Cmd.halt) 0
        View2.bot View2.bot View2.bot memC 1 3 hslot_split (by decide)
    have hp_in : promY2 ∈ (msgSplit :: memC) :=
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hs_fulfill : CertStep 0
        { cmd := Cmd.store .relaxed 1 2 Cmd.halt
          obs := 0, cur := { t0 := 0, t1 := 3 }, acq := { t0 := 0, t1 := 3 }, rel := View2.bot }
        (msgSplit :: memC)
        { cmd := Cmd.halt
          obs := 0, cur := { t0 := 0, t1 := 6 }, acq := { t0 := 0, t1 := 6 }, rel := View2.bot }
        (fulfillMsgInPool promY2 (msgSplit :: memC)) :=
      CertStep.fulfillStore 1 2 Cmd.halt 0 { t0 := 0, t1 := 3 } { t0 := 0, t1 := 3 }
        View2.bot (msgSplit :: memC) promY2 hp_in rfl rfl rfl rfl (by decide) rfl rfl
    exact ⟨_, _,
      CertSteps.head hs_load (CertSteps.head hs_store1 (CertSteps.head hs_fulfill (CertSteps.refl _ _))),
      rfl⟩
  let mem1 := promY2 :: initMem2
  have hstep1 : PS2Step2
      { t0 := initThread lbCondOverwriteT0, t1 := initThread lbCondOverwriteT1, mem := initMem2 }
      { t0 := initThread lbCondOverwriteT0, t1 := initThread lbCondOverwriteT1, mem := mem1 } :=
    PS2Step2.step0 (PS2ThreadStep.promise 1 2 4 6 hslot_prom (by decide) hcert1)
  let t1AfterLoad : ThreadState :=
    { cmd := Cmd.store .relaxed 0 1 Cmd.halt, obs := 2
      cur := { t0 := 0, t1 := 6 }, acq := { t0 := 0, t1 := 6 }, rel := View2.bot }
  have hs2 : CertStep 1 (initThread lbCondOverwriteT1) mem1 t1AfterLoad mem1 :=
    CertStep.load .relaxed 1 _ 0 View2.bot View2.bot View2.bot
      mem1 promY2 (List.Mem.head _) rfl rfl rfl (by decide)
  have hstep2 : PS2Step2
      { t0 := initThread lbCondOverwriteT0, t1 := initThread lbCondOverwriteT1, mem := mem1 }
      { t0 := initThread lbCondOverwriteT0, t1 := t1AfterLoad, mem := mem1 } :=
    PS2Step2.step1 (PS2ThreadStep.exec hs2 (Or.inl rfl))
  have hslot_x1 : slotAvailable mem1 0 2 4 := by
    refine ⟨by decide, ?_⟩
    intro m hm hloc
    dsimp [mem1, initMem2] at hm
    cases hm with
    | head _ => nomatch hloc
    | tail _ hm1 =>
      cases hm1 with
      | head _ => exact Or.inl ⟨rfl, rfl⟩
      | tail _ hm2 =>
        cases hm2 with
        | head _ => nomatch hloc
        | tail _ hnil => nomatch hnil
  let mem2 := msgX1FromCond :: mem1
  let t1Halted : ThreadState :=
    { cmd := Cmd.halt, obs := 2, cur := { t0 := 4, t1 := 6 }
      acq := { t0 := 4, t1 := 6 }, rel := View2.bot }
  have hs3 : CertStep 1 t1AfterLoad mem1 t1Halted mem2 :=
    CertStep.storeFresh .relaxed 0 1 Cmd.halt 2 { t0 := 0, t1 := 6 } { t0 := 0, t1 := 6 }
      View2.bot mem1 2 4 hslot_x1 (by decide)
  have hstep3 : PS2Step2
      { t0 := initThread lbCondOverwriteT0, t1 := t1AfterLoad, mem := mem1 }
      { t0 := initThread lbCondOverwriteT0, t1 := t1Halted, mem := mem2 } :=
    PS2Step2.step1 (PS2ThreadStep.exec hs3 (Or.inl rfl))
  let t0AfterLoad : ThreadState :=
    { cmd := Cmd.store .relaxed 1 2 Cmd.halt, obs := 1
      cur := { t0 := 4, t1 := 0 }, acq := { t0 := 4, t1 := 0 }, rel := View2.bot }
  have hs4 : CertStep 0 (initThread lbCondOverwriteT0) mem2 t0AfterLoad mem2 :=
    CertStep.load .relaxed 0 _ 0 View2.bot View2.bot View2.bot
      mem2 msgX1FromCond (List.Mem.head _) rfl rfl rfl (by decide)
  have hcert4 : Certified 0 t0AfterLoad mem2 := by
    let mem2C := capMem mem2
    have hp2_in : promY2 ∈ mem2C :=
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hs_f : CertStep 0 t0AfterLoad mem2C
        { cmd := Cmd.halt, obs := 1, cur := { t0 := 4, t1 := 6 }
          acq := { t0 := 4, t1 := 6 }, rel := View2.bot }
        (fulfillMsgInPool promY2 mem2C) :=
      CertStep.fulfillStore 1 2 Cmd.halt 1 { t0 := 4, t1 := 0 } { t0 := 4, t1 := 0 }
        View2.bot mem2C promY2 hp2_in rfl rfl rfl rfl (by decide) rfl rfl
    exact ⟨_, _, CertSteps.head hs_f (CertSteps.refl _ _), rfl⟩
  have hstep4 : PS2Step2
      { t0 := initThread lbCondOverwriteT0, t1 := t1Halted, mem := mem2 }
      { t0 := t0AfterLoad, t1 := t1Halted, mem := mem2 } :=
    PS2Step2.step0 (PS2ThreadStep.exec hs4 (Or.inr hcert4))
  let mem3 := fulfillMsgInPool promY2 mem2
  let t0Halted : ThreadState :=
    { cmd := Cmd.halt, obs := 1, cur := { t0 := 4, t1 := 6 }
      acq := { t0 := 4, t1 := 6 }, rel := View2.bot }
  have hs5 : CertStep 0 t0AfterLoad mem2 t0Halted mem3 :=
    CertStep.fulfillStore 1 2 Cmd.halt 1 { t0 := 4, t1 := 0 } { t0 := 4, t1 := 0 }
      View2.bot mem2 promY2 (List.Mem.tail _ (List.Mem.head _)) rfl rfl rfl rfl (by decide) rfl rfl
  have hstep5 : PS2Step2
      { t0 := t0AfterLoad, t1 := t1Halted, mem := mem2 }
      { t0 := t0Halted, t1 := t1Halted, mem := mem3 } :=
    PS2Step2.step0 (PS2ThreadStep.exec hs5 (Or.inl rfl))
  have hreach :=
    PS2Reachable2.tail
      (PS2Reachable2.tail
        (PS2Reachable2.tail
          (PS2Reachable2.tail
            (PS2Reachable2.tail (PS2Reachable2.refl _) hstep1)
            hstep2)
          hstep3)
        hstep4)
      hstep5
  exact ⟨_, hreach, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `PS 2.0` cap non-vacuity witness: Thread 0 attempts to promise `y = 1`
relying on winning an RMW (`rmwXchg`) on `loc = 0` at `initMsg0` (`toTs = 0`).
Because `capMem` places an adjacent cap `(0, 1]` on `loc = 0`, no `CertStep`
exists from `initThread stealableRmwCmd` over `capMem (mProm :: initMem2)`! -/
def stealableRmwCmd : Cmd :=
  Cmd.rmwXchg .relaxed 0 1 (fun r =>
    if Nat.beq r 0 then Cmd.store .relaxed 1 1 Cmd.halt else Cmd.halt)

theorem ps2_cap_blocks_stealable_rmw_promise (fromTs toTs : Nat) :
    let mProm : Msg :=
      { loc := 1, fromTs := fromTs, toTs := toTs, val := 1
        releasedLoc0Ts := 0, releasedLoc1Ts := toTs
        promisedBy := some 0, isCap := false }
    ¬ Certified 0 (initThread stealableRmwCmd) (mProm :: initMem2) := by
  intro mProm hcert
  let ⟨sEnd, memEnd, hsteps, hnone⟩ := hcert
  cases hsteps with
  | refl _ _ =>
    -- `hasPromiseBy 0 (capMem (mProm :: initMem2)) = true`, contradicting `hnone`!
    dsimp [capMem, hasPromiseBy, List.foldr, Msg.isPromiseOf] at hnone
    nomatch hnone
  | head hs _ =>
    cases hs with
    | rmwXchg _ _ _ _ _ _ _ _ _ base toRmw hbase hloc hcap hnp _ hslot =>
      -- Every non-cap message on `loc = 0` in `capMem (mProm :: initMem2)` is
      -- `initMsg0` (`toTs = 0`)!
      have hbase_eq : base = initMsg0 := by
        cases hbase with
        | head _ => nomatch hcap
        | tail _ hb1 =>
          cases hb1 with
          | head _ => nomatch hcap
          | tail _ hb2 =>
            cases hb2 with
            | head _ => nomatch hloc
            | tail _ hb3 =>
              cases hb3 with
              | head _ => rfl
              | tail _ hb4 =>
                cases hb4 with
                | head _ => nomatch hloc
                | tail _ hnil => nomatch hnil
      subst hbase_eq
      -- `capMem` placed cap `c0` (`loc = 0, fromTs = 0, toTs = 1`) at head!
      let ⟨hlt, hdisj_all⟩ := hslot
      have hc0 := hdisj_all
        { loc := 0, fromTs := 0, toTs := 1, val := 0
          releasedLoc0Ts := 0, releasedLoc1Ts := 0
          promisedBy := none, isCap := true }
        (List.Mem.head _) rfl
      cases hc0 with
      | inl h00 =>
        let ⟨_, h10⟩ := h00
        nomatch h10
      | inr hdisj =>
        cases hdisj with
        | inl h1le0 => nomatch h1le0
        | inr htole0 =>
          have h0lt0 : 0 < 0 := Nat.lt_of_lt_of_le hlt htole0
          exact Nat.lt_irrefl 0 h0lt0

/-! ## 3. Universal Pure `Relaxed` Invariant Preservation & OOTA Freedom -/

/-- Structural predicate stating that whenever every read on `loc` returns a
value satisfying `Φ loc v`, every value written by `Cmd` to `loc'` satisfies
`Φ loc' w`. -/
inductive CmdRespectsValInv (Φ : Loc → Nat → Prop) : Cmd → Prop where
  | halt : CmdRespectsValInv Φ Cmd.halt
  | load (ord : MemOrd) (loc : Loc) (k : Nat → Cmd) :
      (∀ v, Φ loc v → CmdRespectsValInv Φ (k v)) →
      CmdRespectsValInv Φ (Cmd.load ord loc k)
  | store (ord : MemOrd) (loc val : Nat) (next : Cmd) :
      Φ loc val →
      CmdRespectsValInv Φ next →
      CmdRespectsValInv Φ (Cmd.store ord loc val next)
  | rmwXchg (ord : MemOrd) (loc val : Nat) (k : Nat → Cmd) :
      Φ loc val →
      (∀ v, Φ loc v → CmdRespectsValInv Φ (k v)) →
      CmdRespectsValInv Φ (Cmd.rmwXchg ord loc val k)
  | fence (ord : MemOrd) (next : Cmd) :
      CmdRespectsValInv Φ next →
      CmdRespectsValInv Φ (Cmd.fence ord next)
  | compilerFenceSeqCst (next : Cmd) :
      CmdRespectsValInv Φ next →
      CmdRespectsValInv Φ (Cmd.compilerFenceSeqCst next)

/-- All non-cap messages not currently promised by `tid` satisfy `Φ`. -/
def NonSelfMessagesRespect (Φ : Loc → Nat → Prop) (tid : Tid) (mem : List Msg) : Prop :=
  ∀ m, m ∈ mem → m.isCap = false → m.isPromiseOf tid = false → Φ m.loc m.val

/-- All non-cap messages (both promised and fulfilled!) satisfy `Φ`. -/
def AllMessagesRespect (Φ : Loc → Nat → Prop) (mem : List Msg) : Prop :=
  ∀ m, m ∈ mem → m.isCap = false → Φ m.loc m.val

private theorem nat_beq_eq {a b : Nat} (h : Nat.beq a b = true) : a = b := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => nomatch h
  | succ n ih =>
    intro b h
    cases b with
    | zero => nomatch h
    | succ m =>
      have heq : n = m := ih h
      rw [heq]

private theorem bool_and_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a with
  | false => nomatch h
  | true =>
    cases b with
    | false => nomatch h
    | true => exact ⟨rfl, rfl⟩

private theorem msg_beq_loc_val {a b : Msg} (h : Msg.beq a b = true) :
    a.loc = b.loc ∧ a.val = b.val := by
  dsimp [Msg.beq] at h
  let ⟨h1234567, _⟩ := bool_and_true h
  let ⟨h123456, _⟩ := bool_and_true h1234567
  let ⟨h12345, _⟩ := bool_and_true h123456
  let ⟨h1234, _⟩ := bool_and_true h12345
  let ⟨h123, hval⟩ := bool_and_true h1234
  let ⟨h12, _⟩ := bool_and_true h123
  let ⟨hloc, _⟩ := bool_and_true h12
  exact ⟨nat_beq_eq hloc, nat_beq_eq hval⟩

private theorem fulfill_mem_nonSelf {Φ : Loc → Nat → Prop} {tid : Tid}
    {target : Msg} {mem : List Msg}
    (hns : NonSelfMessagesRespect Φ tid mem)
    (htarget : Φ target.loc target.val) :
    NonSelfMessagesRespect Φ tid (fulfillMsgInPool target mem) := by
  induction mem with
  | nil =>
    intro m hm
    nomatch hm
  | cons hd tl ih =>
    have htl : NonSelfMessagesRespect Φ tid tl :=
      fun m hm hc hp => hns m (List.Mem.tail _ hm) hc hp
    dsimp [fulfillMsgInPool, List.foldr]
    cases hbeq : Msg.beq hd target with
    | true =>
      let ⟨hloc, hval⟩ := msg_beq_loc_val hbeq
      intro m hm hcap hnp
      cases hm with
      | head _ =>
        dsimp
        rw [hloc, hval]
        exact htarget
      | tail _ hrest =>
        exact ih htl m hrest hcap hnp
    | false =>
      intro m hm hcap hnp
      cases hm with
      | head _ =>
        exact hns hd (List.Mem.head _) hcap hnp
      | tail _ hrest =>
        exact ih htl m hrest hcap hnp

private theorem fulfill_mem_all {Φ : Loc → Nat → Prop} {target : Msg} {mem : List Msg}
    (hall : AllMessagesRespect Φ mem) :
    AllMessagesRespect Φ (fulfillMsgInPool target mem) := by
  induction mem with
  | nil =>
    intro m hm
    nomatch hm
  | cons hd tl ih =>
    have htl : AllMessagesRespect Φ tl :=
      fun m hm hc => hall m (List.Mem.tail _ hm) hc
    dsimp [fulfillMsgInPool, List.foldr]
    cases hbeq : Msg.beq hd target with
    | true =>
      intro m hm hcap
      cases hm with
      | head _ =>
        exact hall hd (List.Mem.head _) hcap
      | tail _ hrest =>
        exact ih htl m hrest hcap
    | false =>
      intro m hm hcap
      cases hm with
      | head _ =>
        exact hall hd (List.Mem.head _) hcap
      | tail _ hrest =>
        exact ih htl m hrest hcap

private theorem certStep_preserves_nonSelf {Φ : Loc → Nat → Prop} {tid : Tid}
    {s s' : ThreadState} {mem mem' : List Msg}
    (hcmd : CmdRespectsValInv Φ s.cmd)
    (hns : NonSelfMessagesRespect Φ tid mem)
    (hs : CertStep tid s mem s' mem') :
    CmdRespectsValInv Φ s'.cmd ∧ NonSelfMessagesRespect Φ tid mem' := by
  cases hs with
  | load ord loc k obs cur acq rel mem m hm hloc hcap hnp _ =>
    cases hcmd with
    | load _ _ _ hk =>
      have hm_phi : Φ loc m.val := by
        have h1 := hns m hm hcap hnp
        rw [hloc] at h1
        exact h1
      exact ⟨hk m.val hm_phi, hns⟩
  | storeFresh ord loc val next obs cur acq rel mem fromTs toTs _ _ =>
    cases hcmd with
    | store _ _ _ _ hval hnext =>
      refine ⟨hnext, ?_⟩
      intro m hm hcap hnp
      cases hm with
      | head _ => exact hval
      | tail _ hrest => exact hns m hrest hcap hnp
  | fulfillStore loc val next obs cur acq rel mem target _ hloc hval _ _ _ _ _ =>
    cases hcmd with
    | store _ _ _ _ hphi hnext =>
      have ht_phi : Φ target.loc target.val := by
        rw [hloc, hval]
        exact hphi
      exact ⟨hnext, fulfill_mem_nonSelf hns ht_phi⟩
  | rmwXchg ord loc val k obs cur acq rel mem base toTs hbase hloc hcap hnp _ _ =>
    cases hcmd with
    | rmwXchg _ _ _ _ hval hk =>
      have hb_phi : Φ loc base.val := by
        have h1 := hns base hbase hcap hnp
        rw [hloc] at h1
        exact h1
      refine ⟨hk base.val hb_phi, ?_⟩
      intro m hm hmc hmnp
      cases hm with
      | head _ => exact hval
      | tail _ hrest => exact hns m hrest hmc hmnp
  | fence _ _ _ _ _ _ _ _ =>
    cases hcmd with
    | fence _ _ hnext => exact ⟨hnext, hns⟩
  | compilerFenceSeqCst _ _ _ _ _ _ =>
    cases hcmd with
    | compilerFenceSeqCst _ hnext => exact ⟨hnext, hns⟩

private theorem certSteps_preserves_nonSelf {Φ : Loc → Nat → Prop} {tid : Tid}
    {s s' : ThreadState} {mem mem' : List Msg}
    (hcmd : CmdRespectsValInv Φ s.cmd)
    (hns : NonSelfMessagesRespect Φ tid mem)
    (hsteps : CertSteps tid s mem s' mem') :
    CmdRespectsValInv Φ s'.cmd ∧ NonSelfMessagesRespect Φ tid mem' := by
  induction hsteps with
  | refl _ _ => exact ⟨hcmd, hns⟩
  | head hs _ ih =>
    let ⟨hcmd2, hns2⟩ := certStep_preserves_nonSelf hcmd hns hs
    exact ih hcmd2 hns2

/-- Key lemma: every message `m ∈ mem` survives in `memEnd` across `CertSteps`
with identical `(loc, val, isCap)` (either untouched or with `promisedBy`
switched to `none`). -/
private theorem fulfill_preserves_loc_val {target m : Msg} {mem : List Msg}
    (hm : m ∈ mem) :
    ∃ m', m' ∈ fulfillMsgInPool target mem ∧
      m'.loc = m.loc ∧ m'.val = m.val ∧ m'.isCap = m.isCap := by
  induction mem with
  | nil => nomatch hm
  | cons hd tl ih =>
    dsimp [fulfillMsgInPool, List.foldr]
    cases hm with
    | head _ =>
      cases Msg.beq m target with
      | true => exact ⟨{ m with promisedBy := none }, List.Mem.head _, rfl, rfl, rfl⟩
      | false => exact ⟨m, List.Mem.head _, rfl, rfl, rfl⟩
    | tail _ htl =>
      let ⟨m', hm', hl, hv, hc⟩ := ih htl
      cases Msg.beq hd target with
      | true => exact ⟨m', List.Mem.tail _ hm', hl, hv, hc⟩
      | false => exact ⟨m', List.Mem.tail _ hm', hl, hv, hc⟩

private theorem certStep_preserves_msg_loc_val {tid : Tid}
    {s s' : ThreadState} {mem mem' : List Msg} {m : Msg}
    (hm : m ∈ mem) (hs : CertStep tid s mem s' mem') :
    ∃ m', m' ∈ mem' ∧ m'.loc = m.loc ∧ m'.val = m.val ∧ m'.isCap = m.isCap := by
  cases hs with
  | load _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨m, hm, rfl, rfl, rfl⟩
  | storeFresh _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨m, List.Mem.tail _ hm, rfl, rfl, rfl⟩
  | fulfillStore _ _ _ _ _ _ _ _ target _ _ _ _ _ _ _ _ =>
    exact fulfill_preserves_loc_val hm
  | rmwXchg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨m, List.Mem.tail _ hm, rfl, rfl, rfl⟩
  | fence _ _ _ _ _ _ _ _ =>
    exact ⟨m, hm, rfl, rfl, rfl⟩
  | compilerFenceSeqCst _ _ _ _ _ _ =>
    exact ⟨m, hm, rfl, rfl, rfl⟩

private theorem certSteps_preserves_msg_loc_val {tid : Tid}
    {s s' : ThreadState} {mem mem' : List Msg} {m : Msg}
    (hm : m ∈ mem) (hsteps : CertSteps tid s mem s' mem') :
    ∃ m', m' ∈ mem' ∧ m'.loc = m.loc ∧ m'.val = m.val ∧ m'.isCap = m.isCap := by
  induction hsteps generalizing m with
  | refl _ _ => exact ⟨m, hm, rfl, rfl, rfl⟩
  | head hs _ ih =>
    let ⟨m₁, hm₁, hl₁, hv₁, hc₁⟩ := certStep_preserves_msg_loc_val hm hs
    let ⟨m₂, hm₂, hl₂, hv₂, hc₂⟩ := ih hm₁
    rw [hl₁] at hl₂
    rw [hv₁] at hv₂
    rw [hc₁] at hc₂
    exact ⟨m₂, hm₂, hl₂, hv₂, hc₂⟩

private theorem no_self_promise_when_hasPromiseBy_false {tid : Tid} {mem : List Msg}
    (hnone : hasPromiseBy tid mem = false) :
    ∀ m, m ∈ mem → m.isPromiseOf tid = false := by
  induction mem with
  | nil =>
    intro m hm
    nomatch hm
  | cons hd tl ih =>
    dsimp [hasPromiseBy, List.foldr] at hnone
    cases hp : hd.isPromiseOf tid with
    | true =>
      rw [hp] at hnone
      nomatch hnone
    | false =>
      rw [hp] at hnone
      intro m hm
      cases hm with
      | head _ => exact hp
      | tail _ htl => exact ih hnone m htl

private theorem nat_beq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

/-- **Theorem 3a (`ps2_pure_relaxed_invariant_preserved`):** Any pure value
invariant `Φ : Loc → Nat → Prop` respected by thread commands is preserved
inductively across all `PS2` steps—including `Relaxed` write promises! User
proofs never need to construct certification traces to rely on `Φ`. -/
theorem ps2_threadStep_preserves_valInv {Φ : Loc → Nat → Prop} {tid : Tid}
    {s s' : ThreadState} {mem mem' : List Msg}
    (hcmd : CmdRespectsValInv Φ s.cmd)
    (hall : AllMessagesRespect Φ mem)
    (hstep : PS2ThreadStep tid s mem s' mem') :
    CmdRespectsValInv Φ s'.cmd ∧ AllMessagesRespect Φ mem' := by
  cases hstep with
  | promise loc val fromTs toTs _ _ hcert =>
    refine ⟨hcmd, ?_⟩
    let mProm : Msg := makePromiseMsg tid s loc val fromTs toTs
    let ⟨sEnd, memEnd, hsteps, hnone⟩ := hcert
    have hns_cap : NonSelfMessagesRespect Φ tid (capMem (mProm :: mem)) := by
      intro m hm hcap hnp
      cases hm with
      | head _ => nomatch hcap
      | tail _ hm1 =>
        cases hm1 with
        | head _ => nomatch hcap
        | tail _ hm2 =>
          cases hm2 with
          | head _ =>
            -- `mProm.isPromiseOf tid = Nat.beq tid tid = true`, contradicting `hnp`!
            dsimp [mProm, makePromiseMsg, Msg.isPromiseOf] at hnp
            rw [nat_beq_refl tid] at hnp
            nomatch hnp
          | tail _ hrest =>
            exact hall m hrest hcap
    let ⟨_, hns_end⟩ := certSteps_preserves_nonSelf hcmd hns_cap hsteps
    have hmProm_in_cap : mProm ∈ capMem (mProm :: mem) :=
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    let ⟨mFulf, hmFulf_in, hlocF, hvalF, hcapF⟩ :=
      certSteps_preserves_msg_loc_val hmProm_in_cap hsteps
    have hnpF : mFulf.isPromiseOf tid = false :=
      no_self_promise_when_hasPromiseBy_false hnone mFulf hmFulf_in
    have hphiF : Φ mFulf.loc mFulf.val := hns_end mFulf hmFulf_in hcapF hnpF
    rw [hlocF, hvalF] at hphiF
    intro m hm hcap
    cases hm with
    | head _ => exact hphiF
    | tail _ hrest => exact hall m hrest hcap
  | exec hs _ =>
    have hns : NonSelfMessagesRespect Φ tid mem :=
      fun m hm hc _ => hall m hm hc
    cases hs with
    | load ord loc k obs cur acq rel mem m hm hloc hcap _ _ =>
      cases hcmd with
      | load _ _ _ hk =>
        have hm_phi : Φ loc m.val := by
          have h1 := hall m hm hcap
          rw [hloc] at h1
          exact h1
        exact ⟨hk m.val hm_phi, hall⟩
    | storeFresh _ _ val _ _ _ _ _ _ _ _ _ _ =>
      cases hcmd with
      | store _ _ _ _ hval hnext =>
        refine ⟨hnext, ?_⟩
        intro m hm hcap
        cases hm with
        | head _ => exact hval
        | tail _ hrest => exact hall m hrest hcap
    | fulfillStore _ _ _ _ _ _ _ _ target _ _ _ _ _ _ _ _ =>
      cases hcmd with
      | store _ _ _ _ _ hnext =>
        exact ⟨hnext, fulfill_mem_all hall⟩
    | rmwXchg _ loc val k _ _ _ _ _ base _ hbase hloc hcap _ _ _ =>
      cases hcmd with
      | rmwXchg _ _ _ _ hval hk =>
        have hb_phi : Φ loc base.val := by
          have h1 := hall base hbase hcap
          rw [hloc] at h1
          exact h1
        refine ⟨hk base.val hb_phi, ?_⟩
        intro m hm hmc
        cases hm with
        | head _ => exact hval
        | tail _ hrest => exact hall m hrest hmc
    | fence _ _ _ _ _ _ _ _ =>
      cases hcmd with
      | fence _ _ hnext => exact ⟨hnext, hall⟩
    | compilerFenceSeqCst _ _ _ _ _ _ =>
      cases hcmd with
      | compilerFenceSeqCst _ hnext => exact ⟨hnext, hall⟩

theorem ps2_pure_relaxed_invariant_preserved (Φ : Loc → Nat → Prop)
    (cInit c : PS2Config2)
    (hc0 : CmdRespectsValInv Φ cInit.t0.cmd)
    (hc1 : CmdRespectsValInv Φ cInit.t1.cmd)
    (hmem : AllMessagesRespect Φ cInit.mem)
    (hreach : PS2Reachable2 cInit c) :
    CmdRespectsValInv Φ c.t0.cmd ∧
    CmdRespectsValInv Φ c.t1.cmd ∧
    AllMessagesRespect Φ c.mem := by
  induction hreach with
  | refl => exact ⟨hc0, hc1, hmem⟩
  | tail _ hstep ih =>
    let ⟨ic0, ic1, imem⟩ := ih
    cases hstep with
    | step0 hs0 =>
      let ⟨nc0, nmem⟩ := ps2_threadStep_preserves_valInv ic0 imem hs0
      exact ⟨nc0, ic1, nmem⟩
    | step1 hs1 =>
      let ⟨nc1, nmem⟩ := ps2_threadStep_preserves_valInv ic1 imem hs1
      exact ⟨ic0, nc1, nmem⟩

/-- Data-dependent load-buffering (`LB+data_dep` / canonical OOTA test):
`r = load(readLoc, Relaxed); store(writeLoc, r, Relaxed)`. -/
def lbDataDepThread (readLoc writeLoc : Loc) : Cmd :=
  Cmd.load .relaxed readLoc (fun r => Cmd.store .relaxed writeLoc r Cmd.halt)

def lbDataDepInitPS2 : PS2Config2 :=
  { t0 := initThread (lbDataDepThread 0 1)
    t1 := initThread (lbDataDepThread 1 0)
    mem := initMem2 }

/-- **Theorem 3b (`ps2_forbids_oota_lb_data_dep`):** Across ALL reachable `PS2`
states of `LB+data_dep` (with arbitrary promise attempts), every message in
memory has `val = 0` and both `obs₀ = 0` and `obs₁ = 0`, ruling out
Out-Of-Thin-Air `(1, 1)`. -/
theorem ps2_forbids_oota_lb_data_dep (c : PS2Config2)
    (hreach : PS2Reachable2 lbDataDepInitPS2 c) :
    c.t0.obs = 0 ∧ c.t1.obs = 0 ∧ ¬ (c.t0.obs = 1 ∧ c.t1.obs = 1) := by
  let Φ : Loc → Nat → Prop := fun _ v => v = 0
  have hinv : CmdRespectsValInv Φ c.t0.cmd ∧
      CmdRespectsValInv Φ c.t1.cmd ∧
      AllMessagesRespect Φ c.mem ∧
      c.t0.obs = 0 ∧ c.t1.obs = 0 := by
    induction hreach with
    | refl =>
      refine ⟨?_, ?_, ?_, rfl, rfl⟩
      · exact CmdRespectsValInv.load .relaxed 0 _ (fun v hv =>
          CmdRespectsValInv.store .relaxed 1 v Cmd.halt hv CmdRespectsValInv.halt)
      · exact CmdRespectsValInv.load .relaxed 1 _ (fun v hv =>
          CmdRespectsValInv.store .relaxed 0 v Cmd.halt hv CmdRespectsValInv.halt)
      · intro m hm _
        exact initMem2_vals_zero m hm
    | tail _ hstep ih =>
      let ⟨ic0, ic1, imem, io0, io1⟩ := ih
      cases hstep with
      | @step0 s0 s0' s1 mem mem' hs0 =>
        let ⟨nc0, nmem⟩ := ps2_threadStep_preserves_valInv ic0 imem hs0
        have no0 : s0'.obs = 0 := by
          cases hs0 with
          | promise _ _ _ _ _ _ _ => exact io0
          | exec hcs _ =>
            cases hcs with
            | load _ _ _ _ _ _ _ _ m hm _ hcap _ _ => exact imem m hm hcap
            | storeFresh _ _ _ _ _ _ _ _ _ _ _ _ _ => exact io0
            | fulfillStore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact io0
            | rmwXchg _ _ _ _ _ _ _ _ _ base _ hbase _ hcap _ _ _ => exact imem base hbase hcap
            | fence _ _ _ _ _ _ _ _ => exact io0
            | compilerFenceSeqCst _ _ _ _ _ _ => exact io0
        exact ⟨nc0, ic1, nmem, no0, io1⟩
      | @step1 s0 s1 s1' mem mem' hs1 =>
        let ⟨nc1, nmem⟩ := ps2_threadStep_preserves_valInv ic1 imem hs1
        have no1 : s1'.obs = 0 := by
          cases hs1 with
          | promise _ _ _ _ _ _ _ => exact io1
          | exec hcs _ =>
            cases hcs with
            | load _ _ _ _ _ _ _ _ m hm _ hcap _ _ => exact imem m hm hcap
            | storeFresh _ _ _ _ _ _ _ _ _ _ _ _ _ => exact io1
            | fulfillStore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact io1
            | rmwXchg _ _ _ _ _ _ _ _ _ base _ hbase _ hcap _ _ _ => exact imem base hbase hcap
            | fence _ _ _ _ _ _ _ _ => exact io1
            | compilerFenceSeqCst _ _ _ _ _ _ => exact io1
        exact ⟨ic0, nc1, nmem, io0, no1⟩
  let ⟨_, _, _, ho0, ho1⟩ := hinv
  refine ⟨ho0, ho1, ?_⟩
  intro ⟨h1, _⟩
  rw [ho0] at h1
  nomatch h1

/-- Release-fence load-buffering (`LB+frel+acq`):
`r = load(readLoc, Acquire); fence(Release); store(writeLoc, 1, Relaxed)`. -/
def lbFrelFenceTail (writeLoc : Loc) : Cmd :=
  Cmd.fence .release (lbStoreTail writeLoc)

def lbFrelAcqThread (readLoc writeLoc : Loc) : Cmd :=
  Cmd.load .acquire readLoc (fun _ => lbFrelFenceTail writeLoc)

def lbFrelAcqInitPS2 : PS2Config2 :=
  { t0 := initThread (lbFrelAcqThread 0 1)
    t1 := initThread (lbFrelAcqThread 1 0)
    mem := initMem2 }

private theorem no_cert_before_release_fence {tid : Tid} {rl wl : Loc}
    {s sEnd : ThreadState} {mem memEnd : List Msg}
    (hcmd : s.cmd = lbFrelAcqThread rl wl ∨ s.cmd = lbFrelFenceTail wl)
    (hp : hasPromiseBy tid mem = true)
    (hsteps : CertSteps tid s mem sEnd memEnd) :
    hasPromiseBy tid memEnd = true := by
  induction hsteps with
  | refl _ _ => exact hp
  | head hs _ ih =>
    cases hcmd with
    | inl hload =>
      cases hs with
      | load _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        dsimp [lbFrelAcqThread] at hload
        injection hload with _ _ hk
        subst hk
        exact ih (Or.inr rfl) hp
      | storeFresh _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        dsimp [lbFrelAcqThread] at hload; nomatch hload
      | fulfillStore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        dsimp [lbFrelAcqThread] at hload; nomatch hload
      | rmwXchg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        dsimp [lbFrelAcqThread] at hload; nomatch hload
      | fence _ _ _ _ _ _ _ _ =>
        dsimp [lbFrelAcqThread] at hload; nomatch hload
      | compilerFenceSeqCst _ _ _ _ _ _ =>
        dsimp [lbFrelAcqThread] at hload; nomatch hload
    | inr hfence =>
      cases hs with
      | load _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        dsimp [lbFrelFenceTail] at hfence; nomatch hfence
      | storeFresh _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        dsimp [lbFrelFenceTail] at hfence; nomatch hfence
      | fulfillStore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        dsimp [lbFrelFenceTail] at hfence; nomatch hfence
      | rmwXchg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        dsimp [lbFrelFenceTail] at hfence; nomatch hfence
      | fence ord _ _ _ _ _ _ hdrain =>
        dsimp [lbFrelFenceTail] at hfence
        injection hfence with hord _
        subst hord
        cases hdrain with
        | inl hf => nomatch hf
        | inr hpf =>
          rw [hp] at hpf
          nomatch hpf
      | compilerFenceSeqCst _ _ _ _ _ _ =>
        dsimp [lbFrelFenceTail] at hfence; nomatch hfence

/-- **Theorem 3c (`ps2_forbids_lb_frel_acq_1_1`):** Because `fence(Release)`
requires `hasPromiseBy tid mem = false`, neither thread in `LB+frel+acq` can
certify a promise of `store(writeLoc, 1, Relaxed)` before executing its
`load(Acquire)` and `fence(Release)`, so `PS2` forbids `(1, 1)` on `LB+frel+acq`
(matching C++20 `[atomics.fences]`). -/
theorem ps2_forbids_lb_frel_acq_1_1 (c : PS2Config2)
    (hreach : PS2Reachable2 lbFrelAcqInitPS2 c) :
    ¬ (c.t0.obs = 1 ∧ c.t1.obs = 1) := by
  let Inv (st : PS2Config2) : Prop :=
    (st.t0.cmd = lbFrelAcqThread 0 1 ∧
      st.t1.cmd = lbFrelAcqThread 1 0 ∧
      st.t0.obs = 0 ∧ st.t1.obs = 0 ∧
      ∀ m, m ∈ st.mem → m.val = 0) ∨
    ((st.t0.cmd = lbFrelFenceTail 1 ∨ st.t0.cmd = lbStoreTail 1 ∨ st.t0.cmd = Cmd.halt) ∧
      st.t0.obs = 0 ∧
      (st.t1.cmd = lbFrelAcqThread 1 0 ∨ st.t1.cmd = lbFrelFenceTail 0 ∨
        st.t1.cmd = lbStoreTail 0 ∨ st.t1.cmd = Cmd.halt)) ∨
    ((st.t1.cmd = lbFrelFenceTail 0 ∨ st.t1.cmd = lbStoreTail 0 ∨ st.t1.cmd = Cmd.halt) ∧
      st.t1.obs = 0 ∧
      (st.t0.cmd = lbFrelAcqThread 0 1 ∨ st.t0.cmd = lbFrelFenceTail 1 ∨
        st.t0.cmd = lbStoreTail 1 ∨ st.t0.cmd = Cmd.halt))
  have hno_prom : ∀ (tid : Tid) (rl wl : Loc) (s : ThreadState) (mem : List Msg)
      (loc val fromTs toTs : Nat),
      s.cmd = lbFrelAcqThread rl wl →
      ¬ Certified tid s
        ({ loc := loc, fromTs := fromTs, toTs := toTs, val := val
           releasedLoc0Ts := (s.rel.bump loc toTs).t0
           releasedLoc1Ts := (s.rel.bump loc toTs).t1
           promisedBy := some tid, isCap := false } :: mem) := by
    intro tid rl wl s mem loc val fromTs toTs hc hcert
    let ⟨sEnd, memEnd, hsteps, hnone⟩ := hcert
    have hp_cap : hasPromiseBy tid
        (capMem ({ loc := loc, fromTs := fromTs, toTs := toTs, val := val
                   releasedLoc0Ts := (s.rel.bump loc toTs).t0
                   releasedLoc1Ts := (s.rel.bump loc toTs).t1
                   promisedBy := some tid, isCap := false } :: mem)) = true := by
      dsimp [capMem, hasPromiseBy, List.foldr, Msg.isPromiseOf]
      rw [nat_beq_refl tid]
      rfl
    have htrue := no_cert_before_release_fence (Or.inl hc) hp_cap hsteps
    rw [htrue] at hnone
    nomatch hnone
  have hprog_any : ∀ {tid rl wl} {s s' : ThreadState} {mem mem' : List Msg},
      (s.cmd = lbFrelAcqThread rl wl ∨ s.cmd = lbFrelFenceTail wl ∨
        s.cmd = lbStoreTail wl ∨ s.cmd = Cmd.halt) →
      PS2ThreadStep tid s mem s' mem' →
      (s'.cmd = lbFrelAcqThread rl wl ∨ s'.cmd = lbFrelFenceTail wl ∨
        s'.cmd = lbStoreTail wl ∨ s'.cmd = Cmd.halt) := by
    intro tid rl wl s s' mem mem' hc hs
    cases hs with
    | promise _ _ _ _ _ _ _ => exact hc
    | exec hcs _ =>
      cases hc with
      | inl h1 =>
        cases s with
        | mk cmd obs cur acq rel =>
          dsimp at h1; subst h1
          cases hcs with
          | load _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact Or.inr (Or.inl rfl)
      | inr hr1 =>
        cases hr1 with
        | inl h2 =>
          cases s with
          | mk cmd obs cur acq rel =>
            dsimp at h2; subst h2
            cases hcs with
            | fence _ _ _ _ _ _ _ _ => exact Or.inr (Or.inr (Or.inl rfl))
        | inr hr2 =>
          cases hr2 with
          | inl h3 =>
            cases s with
            | mk cmd obs cur acq rel =>
              dsimp at h3; subst h3
              cases hcs with
              | storeFresh _ _ _ _ _ _ _ _ _ _ _ _ _ => exact Or.inr (Or.inr (Or.inr rfl))
              | fulfillStore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact Or.inr (Or.inr (Or.inr rfl))
          | inr h4 =>
            cases s with
            | mk cmd obs cur acq rel =>
              dsimp at h4; subst h4; nomatch hcs
  have hpost_obs : ∀ {tid wl} {s s' : ThreadState} {mem mem' : List Msg},
      (s.cmd = lbFrelFenceTail wl ∨ s.cmd = lbStoreTail wl ∨ s.cmd = Cmd.halt) →
      PS2ThreadStep tid s mem s' mem' →
      (s'.cmd = lbFrelFenceTail wl ∨ s'.cmd = lbStoreTail wl ∨ s'.cmd = Cmd.halt) ∧
      s'.obs = s.obs := by
    intro tid wl s s' mem mem' hc hs
    cases hs with
    | promise _ _ _ _ _ _ _ => exact ⟨hc, rfl⟩
    | exec hcs _ =>
      cases hc with
      | inl h2 =>
        cases s with
        | mk cmd obs cur acq rel =>
          dsimp at h2; subst h2
          cases hcs with
          | fence _ _ _ _ _ _ _ _ => exact ⟨Or.inr (Or.inl rfl), rfl⟩
      | inr hr =>
        cases hr with
        | inl h3 =>
          cases s with
          | mk cmd obs cur acq rel =>
            dsimp at h3; subst h3
            cases hcs with
            | storeFresh _ _ _ _ _ _ _ _ _ _ _ _ _ => exact ⟨Or.inr (Or.inr rfl), rfl⟩
            | fulfillStore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact ⟨Or.inr (Or.inr rfl), rfl⟩
        | inr h4 =>
          cases s with
          | mk cmd obs cur acq rel =>
            dsimp at h4; subst h4; nomatch hcs
  have hinv : Inv c := by
    induction hreach with
    | refl => exact Or.inl ⟨rfl, rfl, rfl, rfl, initMem2_vals_zero⟩
    | tail _ hstep ih =>
      cases hstep with
      | step0 hs0 =>
        cases ih with
        | inl ha =>
          let ⟨ht0, ht1, _, _, hall0⟩ := ha
          cases hs0 with
          | promise loc val fromTs toTs _ _ hcert =>
            exact False.elim (hno_prom 0 0 1 _ _ loc val fromTs toTs ht0 hcert)
          | exec hcs _ =>
            cases hcs with
            | load _ _ _ _ _ _ _ _ m hm _ _ _ _ =>
              dsimp [lbFrelAcqThread] at ht0
              injection ht0 with _ _ hk
              subst hk
              have hm0 : m.val = 0 := hall0 m hm
              exact Or.inr (Or.inl ⟨Or.inl rfl, hm0, Or.inl ht1⟩)
            | storeFresh _ _ _ _ _ _ _ _ _ _ _ _ _ =>
              dsimp [lbFrelAcqThread] at ht0; nomatch ht0
            | fulfillStore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
              dsimp [lbFrelAcqThread] at ht0; nomatch ht0
            | rmwXchg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
              dsimp [lbFrelAcqThread] at ht0; nomatch ht0
            | fence _ _ _ _ _ _ _ _ =>
              dsimp [lbFrelAcqThread] at ht0; nomatch ht0
            | compilerFenceSeqCst _ _ _ _ _ _ =>
              dsimp [lbFrelAcqThread] at ht0; nomatch ht0
        | inr hbc =>
          cases hbc with
          | inl hb =>
            let ⟨ht0_p, ho0, ht1_a⟩ := hb
            let ⟨ht0', ho0'⟩ := hpost_obs ht0_p hs0
            rw [ho0] at ho0'
            exact Or.inr (Or.inl ⟨ht0', ho0', ht1_a⟩)
          | inr hc =>
            let ⟨ht1_p, ho1, ht0_a⟩ := hc
            exact Or.inr (Or.inr ⟨ht1_p, ho1, hprog_any ht0_a hs0⟩)
      | step1 hs1 =>
        cases ih with
        | inl ha =>
          let ⟨ht0, ht1, _, _, hall0⟩ := ha
          cases hs1 with
          | promise loc val fromTs toTs _ _ hcert =>
            exact False.elim (hno_prom 1 1 0 _ _ loc val fromTs toTs ht1 hcert)
          | exec hcs _ =>
            cases hcs with
            | load _ _ _ _ _ _ _ _ m hm _ _ _ _ =>
              dsimp [lbFrelAcqThread] at ht1
              injection ht1 with _ _ hk
              subst hk
              have hm0 : m.val = 0 := hall0 m hm
              exact Or.inr (Or.inr ⟨Or.inl rfl, hm0, Or.inl ht0⟩)
            | storeFresh _ _ _ _ _ _ _ _ _ _ _ _ _ =>
              dsimp [lbFrelAcqThread] at ht1; nomatch ht1
            | fulfillStore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
              dsimp [lbFrelAcqThread] at ht1; nomatch ht1
            | rmwXchg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
              dsimp [lbFrelAcqThread] at ht1; nomatch ht1
            | fence _ _ _ _ _ _ _ _ =>
              dsimp [lbFrelAcqThread] at ht1; nomatch ht1
            | compilerFenceSeqCst _ _ _ _ _ _ =>
              dsimp [lbFrelAcqThread] at ht1; nomatch ht1
        | inr hbc =>
          cases hbc with
          | inl hb =>
            let ⟨ht0_p, ho0, ht1_a⟩ := hb
            exact Or.inr (Or.inl ⟨ht0_p, ho0, hprog_any ht1_a hs1⟩)
          | inr hc =>
            let ⟨ht1_p, ho1, ht0_a⟩ := hc
            let ⟨ht1', ho1'⟩ := hpost_obs ht1_p hs1
            rw [ho1] at ho1'
            exact Or.inr (Or.inr ⟨ht1', ho1', ht0_a⟩)
  intro ⟨h0, h1⟩
  cases hinv with
  | inl ha =>
    let ⟨_, _, ho0, _, _⟩ := ha
    rw [ho0] at h0; nomatch h0
  | inr hbc =>
    cases hbc with
    | inl hb =>
      let ⟨_, ho0, _⟩ := hb
      rw [ho0] at h0; nomatch h0
    | inr hc =>
      let ⟨_, ho1, _⟩ := hc
      rw [ho1] at h1; nomatch h1

/-! ## 4. Exact Promise-Free Reduction When Shared Writes Carry Release -/

/-- Structural predicate characterizing thread commands whose shared writes
(`store` and `rmwXchg`) all carry release semantics (`Release`, `AcqRel`, or
`SeqCst`), while permitting arbitrary `Relaxed`/`Acquire`/`SeqCst` loads and
fences. -/
inductive CmdAllWritesRelease : Cmd → Prop where
  | halt : CmdAllWritesRelease Cmd.halt
  | load (ord : MemOrd) (loc : Loc) (k : Nat → Cmd) :
      (∀ v, CmdAllWritesRelease (k v)) →
      CmdAllWritesRelease (Cmd.load ord loc k)
  | store (ord : MemOrd) (loc val : Nat) (next : Cmd) :
      ord.hasRelease = true →
      CmdAllWritesRelease next →
      CmdAllWritesRelease (Cmd.store ord loc val next)
  | rmwXchg (ord : MemOrd) (loc val : Nat) (k : Nat → Cmd) :
      ord.hasRelease = true →
      (∀ v, CmdAllWritesRelease (k v)) →
      CmdAllWritesRelease (Cmd.rmwXchg ord loc val k)
  | fence (ord : MemOrd) (next : Cmd) :
      CmdAllWritesRelease next →
      CmdAllWritesRelease (Cmd.fence ord next)
  | compilerFenceSeqCst (next : Cmd) :
      CmdAllWritesRelease next →
      CmdAllWritesRelease (Cmd.compilerFenceSeqCst next)

private theorem certStep_releaseOnly_preserves_promiseFlag {tid : Tid}
    {s s' : ThreadState} {mem mem' : List Msg}
    (hrel : CmdAllWritesRelease s.cmd)
    (hs : CertStep tid s mem s' mem') :
    CmdAllWritesRelease s'.cmd ∧ hasPromiseBy tid mem' = hasPromiseBy tid mem := by
  cases hs with
  | load _ _ _ _ _ _ _ _ m _ _ _ _ _ =>
    cases hrel with
    | load _ _ _ hk => exact ⟨hk m.val, rfl⟩
  | storeFresh _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases hrel with
    | store _ _ _ _ _ hnext => exact ⟨hnext, rfl⟩
  | fulfillStore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases hrel with
    | store _ _ _ _ hhas _ => nomatch hhas
  | rmwXchg _ _ _ _ _ _ _ _ _ base _ _ _ _ _ _ _ =>
    cases hrel with
    | rmwXchg _ _ _ _ _ hk => exact ⟨hk base.val, rfl⟩
  | fence _ _ _ _ _ _ _ _ =>
    cases hrel with
    | fence _ _ hnext => exact ⟨hnext, rfl⟩
  | compilerFenceSeqCst _ _ _ _ _ _ =>
    cases hrel with
    | compilerFenceSeqCst _ hnext => exact ⟨hnext, rfl⟩

private theorem certSteps_releaseOnly_preserves_promiseFlag {tid : Tid}
    {s sEnd : ThreadState} {mem memEnd : List Msg}
    (hrel : CmdAllWritesRelease s.cmd)
    (hsteps : CertSteps tid s mem sEnd memEnd) :
    hasPromiseBy tid memEnd = hasPromiseBy tid mem := by
  induction hsteps with
  | refl _ _ => rfl
  | head hs _ ih =>
    let ⟨hrel2, heq1⟩ := certStep_releaseOnly_preserves_promiseFlag hrel hs
    have heq2 := ih hrel2
    rw [heq1] at heq2
    exact heq2

private theorem no_promise_when_allWritesRelease {tid : Tid}
    {s : ThreadState} {mem : List Msg} {mProm : Msg}
    (hrel : CmdAllWritesRelease s.cmd)
    (howner : mProm.promisedBy = some tid) :
    ¬ Certified tid s (mProm :: mem) := by
  intro hcert
  let ⟨sEnd, memEnd, hsteps, hnone⟩ := hcert
  have heq := certSteps_releaseOnly_preserves_promiseFlag hrel hsteps
  have hp_cap : hasPromiseBy tid (capMem (mProm :: mem)) = true := by
    dsimp [capMem, hasPromiseBy, List.foldr, Msg.isPromiseOf]
    rw [howner]
    dsimp
    rw [nat_beq_refl tid]
    rfl
  rw [hp_cap] at heq
  rw [heq] at hnone
  nomatch hnone

private theorem hasPromiseBy_false_of_all_unpromised (tid : Tid) {mem : List Msg}
    (hunp : ∀ m, m ∈ mem → m.promisedBy = none) :
    hasPromiseBy tid mem = false := by
  induction mem with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : hd.promisedBy = none := hunp hd (List.Mem.head _)
    have htl : ∀ m, m ∈ tl → m.promisedBy = none :=
      fun m hm => hunp m (List.Mem.tail _ hm)
    dsimp [hasPromiseBy, List.foldr, Msg.isPromiseOf]
    rw [hhd]
    exact ih htl

/-- **Theorem 4 (`releaseOnly_exact_bisimulation`):** Whenever a thread's
commands satisfy `CmdAllWritesRelease` and memory contains zero unfulfilled
promises, `PS2ThreadStep` is step-for-step equivalent to `PromiseFreeThreadStep`
and preserves `∀ m ∈ mem', m.promisedBy = none`! -/
theorem releaseOnly_exact_bisimulation {tid : Tid}
    {s s' : ThreadState} {mem mem' : List Msg}
    (hrel : CmdAllWritesRelease s.cmd)
    (hunp : ∀ m, m ∈ mem → m.promisedBy = none) :
    (PS2ThreadStep tid s mem s' mem' ∧ (∀ m, m ∈ mem' → m.promisedBy = none)) ↔
    PromiseFreeThreadStep tid s mem s' mem' := by
  constructor
  · intro ⟨hps, _⟩
    cases hps with
    | promise loc val fromTs toTs _ _ hcert =>
      exact False.elim (no_promise_when_allWritesRelease hrel rfl hcert)
    | exec hcs _ =>
      cases hcs with
      | load ord loc k obs cur acq rel mem m hm hloc hcap _ hcur =>
        exact PromiseFreeThreadStep.load ord loc k obs cur acq rel mem m
          hm hloc hcap (hunp m hm) hcur
      | storeFresh ord loc val next obs cur acq rel mem fromTs toTs hslot hcur =>
        exact PromiseFreeThreadStep.store ord loc val next obs cur acq rel mem
          fromTs toTs hslot hcur
      | fulfillStore _ _ _ _ _ _ _ mem target htin _ _ _ hp _ _ _ =>
        have hnone := hunp target htin
        rw [hnone] at hp
        nomatch hp
      | rmwXchg ord loc val k obs cur acq rel mem base toTs hbin hloc hcap _ hcur hslot =>
        exact PromiseFreeThreadStep.rmwXchg ord loc val k obs cur acq rel mem base toTs
          hbin hloc hcap (hunp base hbin) hcur hslot
      | fence ord next obs cur acq rel mem _ =>
        exact PromiseFreeThreadStep.fence ord next obs cur acq rel mem
      | compilerFenceSeqCst next obs cur acq rel mem =>
        exact PromiseFreeThreadStep.compilerFenceSeqCst next obs cur acq rel mem
  · intro hpf
    have hnone_mem : hasPromiseBy tid mem = false :=
      hasPromiseBy_false_of_all_unpromised tid hunp
    cases hpf with
    | load ord loc k obs cur acq rel mem m hm hloc hcap hpnone hcur =>
      have hnp : m.isPromiseOf tid = false := by
        dsimp [Msg.isPromiseOf]; rw [hpnone]
      refine ⟨PS2ThreadStep.exec
        (CertStep.load ord loc k obs cur acq rel mem m hm hloc hcap hnp hcur)
        (Or.inl hnone_mem), hunp⟩
    | store ord loc val next obs cur acq rel mem fromTs toTs hslot hcur =>
      have hunp' : ∀ (m : Msg),
          m ∈ (stepStoreMsg ord loc val fromTs toTs cur rel :: mem) →
          m.promisedBy = none := by
        intro m hm
        cases hm with
        | head _ => rfl
        | tail _ htl => exact hunp m htl
      refine ⟨PS2ThreadStep.exec
        (CertStep.storeFresh ord loc val next obs cur acq rel mem fromTs toTs hslot hcur)
        (Or.inl (hasPromiseBy_false_of_all_unpromised tid hunp')), hunp'⟩
    | rmwXchg ord loc val k obs cur acq rel mem base toTs hbin hloc hcap hpnone hcur hslot =>
      have hnp : base.isPromiseOf tid = false := by
        dsimp [Msg.isPromiseOf]; rw [hpnone]
      have hunp' : ∀ (m : Msg),
          m ∈ (stepRmwMsg ord loc val toTs cur rel base :: mem) →
          m.promisedBy = none := by
        intro m hm
        cases hm with
        | head _ => rfl
        | tail _ htl => exact hunp m htl
      refine ⟨PS2ThreadStep.exec
        (CertStep.rmwXchg ord loc val k obs cur acq rel mem base toTs hbin hloc hcap hnp hcur hslot)
        (Or.inl (hasPromiseBy_false_of_all_unpromised tid hunp')), hunp'⟩
    | fence ord next obs cur acq rel mem =>
      refine ⟨PS2ThreadStep.exec
        (CertStep.fence ord next obs cur acq rel mem (Or.inr hnone_mem))
        (Or.inl hnone_mem), hunp⟩
    | compilerFenceSeqCst next obs cur acq rel mem =>
      refine ⟨PS2ThreadStep.exec
        (CertStep.compilerFenceSeqCst next obs cur acq rel mem)
        (Or.inl hnone_mem), hunp⟩

/-! ## 5. `TargetMemModel`: `x86Tso` vs. `portableCpp20` on `xchg + compiler_fence` -/

/-- Configuration parameterized by `TargetMemModel`, tracking global `tsoSynced`
timestamps drained by `x86` `LOCK`/`xchgq` operations under `.x86Tso` vs.
per-location `P0668R5` / `ARMv8.3 +rcpc` (`swpal; ldapr`) views under
`.portableCpp20`. -/
structure TargetConfig2 where
  t0 : ThreadState
  t1 : ThreadState
  mem : List Msg
  tsoSynced : View2

def targetXchgCur (model : TargetMemModel) (loc toTs : Nat)
    (cur tso : View2) (base : Msg) : View2 :=
  let baseRel : View2 := { t0 := base.releasedLoc0Ts, t1 := base.releasedLoc1Ts }
  let tso' := tso.bump loc toTs
  let curBase := ((cur.bump loc base.toTs).join baseRel).bump loc toTs
  match model with
  | .portableCpp20 => curBase
  | .x86Tso => curBase.join tso'

def targetXchgState (model : TargetMemModel) (loc toTs : Nat) (k : Nat → Cmd)
    (obs : Nat) (cur rel tso : View2) (base : Msg) : ThreadState :=
  let cur' := targetXchgCur model loc toTs cur tso base
  { cmd := k base.val, obs := obs, cur := cur', acq := cur', rel := rel }

def targetXchgMsg (model : TargetMemModel) (loc val toTs : Nat)
    (cur tso : View2) (base : Msg) : Msg :=
  let cur' := targetXchgCur model loc toTs cur tso base
  { loc := loc, fromTs := base.toTs, toTs := toTs, val := val
    releasedLoc0Ts := cur'.t0, releasedLoc1Ts := cur'.t1
    promisedBy := none, isCap := false }

inductive TargetThreadStep (model : TargetMemModel) (tid : Tid) :
    ThreadState → List Msg → View2 → ThreadState → List Msg → View2 → Prop where
  | rmwXchgSeqCst (loc val : Nat) (k : Nat → Cmd)
      (obs : Nat) (cur acq rel : View2) (mem : List Msg) (tso : View2)
      (base : Msg) (toTs : Nat) :
      base ∈ mem →
      base.loc = loc →
      base.isCap = false →
      base.promisedBy = none →
      cur.get loc ≤ base.toTs →
      slotAvailable mem loc base.toTs toTs →
      TargetThreadStep model tid
        { cmd := Cmd.rmwXchg .seqCst loc val k, obs := obs, cur := cur, acq := acq, rel := rel }
        mem tso
        (targetXchgState model loc toTs k obs cur rel tso base)
        (targetXchgMsg model loc val toTs cur tso base :: mem)
        (tso.bump loc toTs)
  | compilerFenceSeqCst (next : Cmd)
      (obs : Nat) (cur acq rel : View2) (mem : List Msg) (tso : View2) :
      TargetThreadStep model tid
        { cmd := Cmd.compilerFenceSeqCst next, obs := obs, cur := cur, acq := acq, rel := rel }
        mem tso
        { cmd := next, obs := obs, cur := cur, acq := acq, rel := rel }
        mem tso
  | loadAcquire (loc : Loc) (k : Nat → Cmd)
      (obs : Nat) (cur acq rel : View2) (mem : List Msg) (tso : View2) (m : Msg) :
      m ∈ mem →
      m.loc = loc →
      m.isCap = false →
      m.promisedBy = none →
      cur.get loc ≤ m.toTs →
      TargetThreadStep model tid
        { cmd := Cmd.load .acquire loc k, obs := obs, cur := cur, acq := acq, rel := rel }
        mem tso
        (stepLoadState .acquire loc k cur acq rel m)
        mem tso

inductive TargetStep2 (model : TargetMemModel) : TargetConfig2 → TargetConfig2 → Prop where
  | step0 {s0 s0' s1 mem mem' tso tso'} :
      TargetThreadStep model 0 s0 mem tso s0' mem' tso' →
      TargetStep2 model
        { t0 := s0, t1 := s1, mem := mem, tsoSynced := tso }
        { t0 := s0', t1 := s1, mem := mem', tsoSynced := tso' }
  | step1 {s0 s1 s1' mem mem' tso tso'} :
      TargetThreadStep model 1 s1 mem tso s1' mem' tso' →
      TargetStep2 model
        { t0 := s0, t1 := s1, mem := mem, tsoSynced := tso }
        { t0 := s0, t1 := s1', mem := mem', tsoSynced := tso' }

inductive TargetReachable2 (model : TargetMemModel) :
    TargetConfig2 → TargetConfig2 → Prop where
  | refl (c : TargetConfig2) : TargetReachable2 model c c
  | tail {a b c : TargetConfig2} :
      TargetReachable2 model a b → TargetStep2 model b c → TargetReachable2 model a c

def crossbeamCfenceTail (readLoc : Loc) : Cmd :=
  Cmd.compilerFenceSeqCst (Cmd.load .acquire readLoc (fun _ => Cmd.halt))

def crossbeamXchgPattern (writeLoc readLoc : Loc) : Cmd :=
  Cmd.rmwXchg .seqCst writeLoc 1 (fun _ => crossbeamCfenceTail readLoc)

def crossbeamInitTarget : TargetConfig2 :=
  { t0 := initThread (crossbeamXchgPattern 0 1)
    t1 := initThread (crossbeamXchgPattern 1 0)
    mem := initMem2
    tsoSynced := View2.bot }

/-- Under `portableCpp20`, `(obs₀ = 0, obs₁ = 0)` IS reachable at `Cmd.halt`
(`ARMv8.3 +rcpc` `swpal; ldapr` and C++20 `P0668R5` `SB+sc_acq`). -/
theorem portableCpp20_allows_xchg_cfence_acq_0_0 :
    ∃ c : TargetConfig2,
      TargetReachable2 .portableCpp20 crossbeamInitTarget c ∧
      c.t0.cmd = Cmd.halt ∧
      c.t1.cmd = Cmd.halt ∧
      c.t0.obs = 0 ∧
      c.t1.obs = 0 := by
  have hslot0 : slotAvailable initMem2 0 0 2 := by
    refine ⟨by decide, ?_⟩
    intro m hm hloc
    cases hm with
    | head _ => exact Or.inl ⟨rfl, rfl⟩
    | tail _ hm2 =>
      cases hm2 with
      | head _ => nomatch hloc
      | tail _ hnil => nomatch hnil
  let mX1 : Msg :=
    { loc := 0, fromTs := 0, toTs := 2, val := 1
      releasedLoc0Ts := 2, releasedLoc1Ts := 0
      promisedBy := none, isCap := false }
  let mem1 := mX1 :: initMem2
  let t0_1 : ThreadState :=
    { cmd := crossbeamCfenceTail 1, obs := 0
      cur := { t0 := 2, t1 := 0 }, acq := { t0 := 2, t1 := 0 }, rel := View2.bot }
  have s1 : TargetStep2 .portableCpp20 crossbeamInitTarget
      { t0 := t0_1, t1 := initThread (crossbeamXchgPattern 1 0)
        mem := mem1, tsoSynced := { t0 := 2, t1 := 0 } } :=
    TargetStep2.step0
      (TargetThreadStep.rmwXchgSeqCst 0 1 _ 0 View2.bot View2.bot View2.bot
        initMem2 View2.bot initMsg0 2 (List.Mem.head _) rfl rfl rfl (by decide) hslot0)
  let t0_2 : ThreadState :=
    { cmd := Cmd.load .acquire 1 (fun _ => Cmd.halt), obs := 0
      cur := { t0 := 2, t1 := 0 }, acq := { t0 := 2, t1 := 0 }, rel := View2.bot }
  have s2 : TargetStep2 .portableCpp20
      { t0 := t0_1, t1 := initThread (crossbeamXchgPattern 1 0)
        mem := mem1, tsoSynced := { t0 := 2, t1 := 0 } }
      { t0 := t0_2, t1 := initThread (crossbeamXchgPattern 1 0)
        mem := mem1, tsoSynced := { t0 := 2, t1 := 0 } } :=
    TargetStep2.step0 (TargetThreadStep.compilerFenceSeqCst _ _ _ _ _ _ _)
  let t0_3 : ThreadState :=
    { cmd := Cmd.halt, obs := 0
      cur := { t0 := 2, t1 := 0 }, acq := { t0 := 2, t1 := 0 }, rel := View2.bot }
  have hm1_in_mem1 : initMsg1 ∈ mem1 :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have s3 : TargetStep2 .portableCpp20
      { t0 := t0_2, t1 := initThread (crossbeamXchgPattern 1 0)
        mem := mem1, tsoSynced := { t0 := 2, t1 := 0 } }
      { t0 := t0_3, t1 := initThread (crossbeamXchgPattern 1 0)
        mem := mem1, tsoSynced := { t0 := 2, t1 := 0 } } :=
    TargetStep2.step0
      (TargetThreadStep.loadAcquire 1 _ 0 { t0 := 2, t1 := 0 } { t0 := 2, t1 := 0 }
        View2.bot mem1 { t0 := 2, t1 := 0 } initMsg1 hm1_in_mem1 rfl rfl rfl (by decide))
  have hslot1 : slotAvailable mem1 1 0 2 := by
    refine ⟨by decide, ?_⟩
    intro m hm hloc
    dsimp [mem1, initMem2] at hm
    cases hm with
    | head _ => nomatch hloc
    | tail _ hm2 =>
      cases hm2 with
      | head _ => nomatch hloc
      | tail _ hm3 =>
        cases hm3 with
        | head _ => exact Or.inl ⟨rfl, rfl⟩
        | tail _ hnil => nomatch hnil
  let mY1 : Msg :=
    { loc := 1, fromTs := 0, toTs := 2, val := 1
      releasedLoc0Ts := 0, releasedLoc1Ts := 2
      promisedBy := none, isCap := false }
  let mem2 := mY1 :: mem1
  let t1_1 : ThreadState :=
    { cmd := crossbeamCfenceTail 0, obs := 0
      cur := { t0 := 0, t1 := 2 }, acq := { t0 := 0, t1 := 2 }, rel := View2.bot }
  have s4 : TargetStep2 .portableCpp20
      { t0 := t0_3, t1 := initThread (crossbeamXchgPattern 1 0)
        mem := mem1, tsoSynced := { t0 := 2, t1 := 0 } }
      { t0 := t0_3, t1 := t1_1, mem := mem2, tsoSynced := { t0 := 2, t1 := 2 } } :=
    TargetStep2.step1
      (TargetThreadStep.rmwXchgSeqCst 1 1 _ 0 View2.bot View2.bot View2.bot
        mem1 { t0 := 2, t1 := 0 } initMsg1 2 hm1_in_mem1 rfl rfl rfl (by decide) hslot1)
  let t1_2 : ThreadState :=
    { cmd := Cmd.load .acquire 0 (fun _ => Cmd.halt), obs := 0
      cur := { t0 := 0, t1 := 2 }, acq := { t0 := 0, t1 := 2 }, rel := View2.bot }
  have s5 : TargetStep2 .portableCpp20
      { t0 := t0_3, t1 := t1_1, mem := mem2, tsoSynced := { t0 := 2, t1 := 2 } }
      { t0 := t0_3, t1 := t1_2, mem := mem2, tsoSynced := { t0 := 2, t1 := 2 } } :=
    TargetStep2.step1 (TargetThreadStep.compilerFenceSeqCst _ _ _ _ _ _ _)
  let t1_3 : ThreadState :=
    { cmd := Cmd.halt, obs := 0
      cur := { t0 := 0, t1 := 2 }, acq := { t0 := 0, t1 := 2 }, rel := View2.bot }
  have hm0_in_mem2 : initMsg0 ∈ mem2 :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have s6 : TargetStep2 .portableCpp20
      { t0 := t0_3, t1 := t1_2, mem := mem2, tsoSynced := { t0 := 2, t1 := 2 } }
      { t0 := t0_3, t1 := t1_3, mem := mem2, tsoSynced := { t0 := 2, t1 := 2 } } :=
    TargetStep2.step1
      (TargetThreadStep.loadAcquire 0 _ 0 { t0 := 0, t1 := 2 } { t0 := 0, t1 := 2 }
        View2.bot mem2 { t0 := 2, t1 := 2 } initMsg0 hm0_in_mem2 rfl rfl rfl (by decide))
  have hreach :=
    TargetReachable2.tail
      (TargetReachable2.tail
        (TargetReachable2.tail
          (TargetReachable2.tail
            (TargetReachable2.tail
              (TargetReachable2.tail (TargetReachable2.refl _) s1)
              s2)
            s3)
          s4)
        s5)
      s6
  exact ⟨_, hreach, rfl, rfl, rfl, rfl⟩

private theorem natMax_ge_left (a b : Nat) : a ≤ natMax a b := by
  dsimp [natMax]
  cases h : Nat.ble a b with
  | true => exact Nat.le_of_ble_eq_true h
  | false => exact Nat.le_refl a

private theorem natMax_ge_right (a b : Nat) : b ≤ natMax a b := by
  dsimp [natMax]
  cases h : Nat.ble a b with
  | true => exact Nat.le_refl b
  | false =>
    -- Prove `b ≤ a` from `Nat.ble a b = false` by structural induction!
    revert b
    induction a with
    | zero =>
      intro b hb
      nomatch hb
    | succ n ih =>
      intro b hb
      cases b with
      | zero => exact Nat.zero_le _
      | succ m =>
        dsimp [Nat.ble] at hb
        exact Nat.succ_le_succ (ih m hb)

/-- Under `x86Tso`, every reachable halted configuration of
`crossbeamInitTarget` satisfies `¬ (obs₀ = 0 ∧ obs₁ = 0)` (`obs₀ = 1 ∨ obs₁ = 1`). -/
theorem x86Tso_forbids_xchg_cfence_acq_0_0 (c : TargetConfig2)
    (hreach : TargetReachable2 .x86Tso crossbeamInitTarget c) :
    c.t0.cmd = Cmd.halt →
    c.t1.cmd = Cmd.halt →
    ¬ (c.t0.obs = 0 ∧ c.t1.obs = 0) := by
  let loadTail (rl : Loc) : Cmd := Cmd.load .acquire rl (fun _ => Cmd.halt)
  -- Track positive timestamp invariant:
  -- Every message in `mem` with `toTs > 0` has `val = 1`, AND:
  -- Case 0: Neither thread has executed `rmwXchg` yet (`tsoSynced = bot`).
  -- Case 1: Thread 0 executed `rmwXchg` (`1 ≤ tsoSynced.t0`), and either
  --   Thread 1 has not executed `rmwXchg` yet, OR Thread 1 executed `rmwXchg`
  --   SECOND (so `1 ≤ t1.cur.t0`, forcing `t1.obs = 1` once `t1` halts!).
  -- Case 2: Symmetric (`1 ≤ tsoSynced.t1` and once Thread 0 executes `rmwXchg`
  --   second, `1 ≤ t0.cur.t1`, forcing `t0.obs = 1` once `t0` halts!).
  let PosMsgsOne (mem : List Msg) : Prop :=
    ∀ m, m ∈ mem → 1 ≤ m.toTs → m.val = 1
  let PostXchgCmd (rl : Loc) (cmd : Cmd) : Prop :=
    cmd = crossbeamCfenceTail rl ∨ cmd = loadTail rl ∨ cmd = Cmd.halt
  let EnforcedObs (rl : Loc) (s : ThreadState) : Prop :=
    ((s.cmd = crossbeamCfenceTail rl ∨ s.cmd = loadTail rl) ∧ 1 ≤ s.cur.get rl) ∨
    (s.cmd = Cmd.halt ∧ s.obs = 1)
  let Inv (st : TargetConfig2) : Prop :=
    PosMsgsOne st.mem ∧
    ((st.t0.cmd = crossbeamXchgPattern 0 1 ∧ st.t1.cmd = crossbeamXchgPattern 1 0) ∨
     (PostXchgCmd 1 st.t0.cmd ∧ 1 ≤ st.tsoSynced.t0 ∧
       (st.t1.cmd = crossbeamXchgPattern 1 0 ∨ EnforcedObs 0 st.t1)) ∨
     (PostXchgCmd 0 st.t1.cmd ∧ 1 ≤ st.tsoSynced.t1 ∧
       (st.t0.cmd = crossbeamXchgPattern 0 1 ∨ EnforcedObs 1 st.t0)))
  have hpos_init : PosMsgsOne initMem2 := by
    intro m hm hge1
    cases hm with
    | head _ => nomatch hge1
    | tail _ hm2 =>
      cases hm2 with
      | head _ => nomatch hge1
      | tail _ hnil => nomatch hnil
  have hpost_step : ∀ {tid rl} {s s' : ThreadState} {mem mem' : List Msg} {tso tso' : View2},
      PostXchgCmd rl s.cmd →
      PosMsgsOne mem →
      TargetThreadStep .x86Tso tid s mem tso s' mem' tso' →
      PostXchgCmd rl s'.cmd ∧ mem' = mem ∧ tso' = tso := by
    intro tid rl s s' mem mem' tso tso' hpc _ hs
    cases hpc with
    | inl hcf =>
      cases s with
      | mk cmd obs cur acq rel =>
        dsimp at hcf; subst hcf
        cases hs with
        | compilerFenceSeqCst _ _ _ _ _ _ _ =>
          exact ⟨Or.inr (Or.inl rfl), rfl, rfl⟩
    | inr hr =>
      cases hr with
      | inl hld =>
        cases s with
        | mk cmd obs cur acq rel =>
          dsimp at hld; subst hld
          cases hs with
          | loadAcquire _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
            exact ⟨Or.inr (Or.inr rfl), rfl, rfl⟩
      | inr hh =>
        cases s with
        | mk cmd obs cur acq rel =>
          dsimp at hh; subst hh; nomatch hs
  have henf_step : ∀ {tid rl} {s s' : ThreadState} {mem mem' : List Msg} {tso tso' : View2},
      EnforcedObs rl s →
      PosMsgsOne mem →
      TargetThreadStep .x86Tso tid s mem tso s' mem' tso' →
      EnforcedObs rl s' ∧ mem' = mem ∧ tso' = tso := by
    intro tid rl s s' mem mem' tso tso' henf hpos hs
    cases henf with
    | inl hpre =>
      let ⟨hcmd, hcur1⟩ := hpre
      cases hcmd with
      | inl hcf =>
        cases s with
        | mk cmd obs cur acq rel =>
          dsimp at hcf; subst hcf
          cases hs with
          | compilerFenceSeqCst _ _ _ _ _ _ _ =>
            exact ⟨Or.inl ⟨Or.inr rfl, hcur1⟩, rfl, rfl⟩
      | inr hld =>
        cases s with
        | mk cmd obs cur acq rel =>
          dsimp at hld; subst hld
          cases hs with
          | loadAcquire _ _ _ _ _ _ _ _ m hm _ _ _ hle =>
            have h1_le_m : 1 ≤ m.toTs := Nat.le_trans hcur1 hle
            have hm1 : m.val = 1 := hpos m hm h1_le_m
            exact ⟨Or.inr ⟨rfl, hm1⟩, rfl, rfl⟩
    | inr hdone =>
      let ⟨hh, _⟩ := hdone
      cases s with
      | mk cmd obs cur acq rel =>
        dsimp at hh; subst hh; nomatch hs
  have hinv : Inv c := by
    induction hreach with
    | refl => exact ⟨hpos_init, Or.inl ⟨rfl, rfl⟩⟩
    | tail _ hstep ih =>
      let ⟨hpos, hcases⟩ := ih
      cases hstep with
      | @step0 _ _ _ _ _ tso _ hs0 =>
        cases hcases with
        | inl h00 =>
          let ⟨ht0, ht1⟩ := h00
          cases hs0 with
          | rmwXchgSeqCst loc val k obs cur acq rel mem tso base toTs _ _ _ _ _ hslot =>
            dsimp [crossbeamXchgPattern] at ht0
            injection ht0 with _ hloc hval hk
            subst hloc; subst hval; subst hk
            let ⟨hlt, _⟩ := hslot
            have h1_le_to : 1 ≤ toTs := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
            have htso1 : 1 ≤ (tso.bump 0 toTs).t0 :=
              Nat.le_trans h1_le_to (natMax_ge_right tso.t0 toTs)
            refine ⟨?_, Or.inr (Or.inl ⟨Or.inl rfl, htso1, Or.inl ht1⟩)⟩
            intro m hm hge1
            cases hm with
            | head _ => rfl
            | tail _ htl => exact hpos m htl hge1
          | compilerFenceSeqCst _ _ _ _ _ _ _ =>
            dsimp [crossbeamXchgPattern] at ht0; nomatch ht0
          | loadAcquire _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
            dsimp [crossbeamXchgPattern] at ht0; nomatch ht0
        | inr h12 =>
          cases h12 with
          | inl h1_first =>
            let ⟨hpc0, htso0, ht1_or⟩ := h1_first
            let ⟨hpc0', hmem_eq, htso_eq⟩ := hpost_step hpc0 hpos hs0
            rw [hmem_eq, htso_eq]
            exact ⟨hpos, Or.inr (Or.inl ⟨hpc0', htso0, ht1_or⟩)⟩
          | inr h2_first =>
            let ⟨hpc1, htso1, ht0_or⟩ := h2_first
            cases ht0_or with
            | inl ht0_init =>
              cases hs0 with
              | rmwXchgSeqCst loc val k obs cur acq rel mem tso base toTs _ _ _ _ _ hslot =>
                dsimp [crossbeamXchgPattern] at ht0_init
                injection ht0_init with _ hloc hval hk
                subst hloc; subst hval; subst hk
                -- `(tso.bump 0 toTs).t1 = tso.t1 ≥ 1`, and `cur'` joins `tso'`!
                have hcur_t1 : 1 ≤
                    ((((cur.bump 0 base.toTs).join
                        { t0 := base.releasedLoc0Ts, t1 := base.releasedLoc1Ts }).bump 0 toTs).join
                      (tso.bump 0 toTs)).get 1 := by
                  dsimp [View2.bump, View2.join, View2.get]
                  exact Nat.le_trans htso1 (natMax_ge_right _ tso.t1)
                refine ⟨?_, Or.inr (Or.inr ⟨hpc1, htso1, Or.inr (Or.inl ⟨Or.inl rfl, hcur_t1⟩)⟩)⟩
                intro m hm hge1
                cases hm with
                | head _ => rfl
                | tail _ htl => exact hpos m htl hge1
              | compilerFenceSeqCst _ _ _ _ _ _ _ =>
                dsimp [crossbeamXchgPattern] at ht0_init; nomatch ht0_init
              | loadAcquire _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                dsimp [crossbeamXchgPattern] at ht0_init; nomatch ht0_init
            | inr henf0 =>
              let ⟨henf0', hmem_eq, htso_eq⟩ := henf_step henf0 hpos hs0
              rw [hmem_eq, htso_eq]
              exact ⟨hpos, Or.inr (Or.inr ⟨hpc1, htso1, Or.inr henf0'⟩)⟩
      | @step1 _ _ _ _ _ tso _ hs1 =>
        cases hcases with
        | inl h00 =>
          let ⟨ht0, ht1⟩ := h00
          cases hs1 with
          | rmwXchgSeqCst loc val k obs cur acq rel mem tso base toTs _ _ _ _ _ hslot =>
            dsimp [crossbeamXchgPattern] at ht1
            injection ht1 with _ hloc hval hk
            subst hloc; subst hval; subst hk
            let ⟨hlt, _⟩ := hslot
            have h1_le_to : 1 ≤ toTs := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
            have htso1 : 1 ≤ (tso.bump 1 toTs).t1 :=
              Nat.le_trans h1_le_to (natMax_ge_right tso.t1 toTs)
            refine ⟨?_, Or.inr (Or.inr ⟨Or.inl rfl, htso1, Or.inl ht0⟩)⟩
            intro m hm hge1
            cases hm with
            | head _ => rfl
            | tail _ htl => exact hpos m htl hge1
          | compilerFenceSeqCst _ _ _ _ _ _ _ =>
            dsimp [crossbeamXchgPattern] at ht1; nomatch ht1
          | loadAcquire _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
            dsimp [crossbeamXchgPattern] at ht1; nomatch ht1
        | inr h12 =>
          cases h12 with
          | inl h1_first =>
            let ⟨hpc0, htso0, ht1_or⟩ := h1_first
            cases ht1_or with
            | inl ht1_init =>
              cases hs1 with
              | rmwXchgSeqCst loc val k obs cur acq rel mem tso base toTs _ _ _ _ _ hslot =>
                dsimp [crossbeamXchgPattern] at ht1_init
                injection ht1_init with _ hloc hval hk
                subst hloc; subst hval; subst hk
                have hcur_t0 : 1 ≤
                    ((((cur.bump 1 base.toTs).join
                        { t0 := base.releasedLoc0Ts, t1 := base.releasedLoc1Ts }).bump 1 toTs).join
                      (tso.bump 1 toTs)).get 0 := by
                  dsimp [View2.bump, View2.join, View2.get]
                  exact Nat.le_trans htso0 (natMax_ge_right _ tso.t0)
                refine ⟨?_, Or.inr (Or.inl ⟨hpc0, htso0, Or.inr (Or.inl ⟨Or.inl rfl, hcur_t0⟩)⟩)⟩
                intro m hm hge1
                cases hm with
                | head _ => rfl
                | tail _ htl => exact hpos m htl hge1
              | compilerFenceSeqCst _ _ _ _ _ _ _ =>
                dsimp [crossbeamXchgPattern] at ht1_init; nomatch ht1_init
              | loadAcquire _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                dsimp [crossbeamXchgPattern] at ht1_init; nomatch ht1_init
            | inr henf1 =>
              let ⟨henf1', hmem_eq, htso_eq⟩ := henf_step henf1 hpos hs1
              rw [hmem_eq, htso_eq]
              exact ⟨hpos, Or.inr (Or.inl ⟨hpc0, htso0, Or.inr henf1'⟩)⟩
          | inr h2_first =>
            let ⟨hpc1, htso1, ht0_or⟩ := h2_first
            let ⟨hpc1', hmem_eq, htso_eq⟩ := hpost_step hpc1 hpos hs1
            rw [hmem_eq, htso_eq]
            exact ⟨hpos, Or.inr (Or.inr ⟨hpc1', htso1, ht0_or⟩)⟩
  intro hh0 hh1 ⟨ho0, ho1⟩
  let ⟨_, hcases⟩ := hinv
  cases hcases with
  | inl h00 =>
    let ⟨ht0, _⟩ := h00
    rw [hh0] at ht0; nomatch ht0
  | inr h12 =>
    cases h12 with
    | inl h1_first =>
      let ⟨_, _, ht1_or⟩ := h1_first
      cases ht1_or with
      | inl ht1_init =>
        rw [hh1] at ht1_init; nomatch ht1_init
      | inr henf1 =>
        cases henf1 with
        | inl hpre =>
          let ⟨hcmd, _⟩ := hpre
          cases hcmd with
          | inl hcf => rw [hh1] at hcf; nomatch hcf
          | inr hld => rw [hh1] at hld; nomatch hld
        | inr hdone =>
          let ⟨_, hobs1_1⟩ := hdone
          rw [ho1] at hobs1_1; nomatch hobs1_1
    | inr h2_first =>
      let ⟨_, _, ht0_or⟩ := h2_first
      cases ht0_or with
      | inl ht0_init =>
        rw [hh0] at ht0_init; nomatch ht0_init
      | inr henf0 =>
        cases henf0 with
        | inl hpre =>
          let ⟨hcmd, _⟩ := hpre
          cases hcmd with
          | inl hcf => rw [hh0] at hcf; nomatch hcf
          | inr hld => rw [hh0] at hld; nomatch hld
        | inr hdone =>
          let ⟨_, hobs0_1⟩ := hdone
          rw [ho0] at hobs0_1; nomatch hobs0_1

/-- **Theorem 5 (`tso_xchg_forbids_0_0_and_portable_allows_0_0`):** Combines
both halves of the `TargetMemModel` separation on `crossbeamInitTarget`. -/
theorem tso_xchg_forbids_0_0_and_portable_allows_0_0 :
    (∃ c : TargetConfig2,
      TargetReachable2 .portableCpp20 crossbeamInitTarget c ∧
      c.t0.cmd = Cmd.halt ∧ c.t1.cmd = Cmd.halt ∧
      c.t0.obs = 0 ∧ c.t1.obs = 0) ∧
    (∀ c : TargetConfig2,
      TargetReachable2 .x86Tso crossbeamInitTarget c →
      c.t0.cmd = Cmd.halt → c.t1.cmd = Cmd.halt →
      ¬ (c.t0.obs = 0 ∧ c.t1.obs = 0)) :=
  ⟨portableCpp20_allows_xchg_cfence_acq_0_0, x86Tso_forbids_xchg_cfence_acq_0_0⟩

end Anneal.PromisingReductionProof

