/-
  Mechanized Lean 4 Probe: Multicore Relaxed-TLB Shootdowns, Page-Table Frame
  Recycling Use-After-Free, AArch64 Break-Before-Make (BBM), and ASID Rollover.

  Toolchain: leanprover/lean4:v4.34.1
  Audit profile: Constructive Type 0, `prelude` + `Init.*` only, zero `sorry`,
  zero custom `axiom`, zero `unsafe`/`partial`/`opaque`, zero `Classical.choice`,
  zero `Lean.ofReduceBool`, zero `._unsafe_rec`.
-/
prelude
import Init.Core
import Init.Tactics
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace MulticoreTlbShootdown

/-! ## 0. Minimal Constructive List Utilities (zero axioms) -/

theorem not_mem_filter_of_pred_false {α : Type} (p : α → Bool) {x : α} :
    ∀ {xs : List α}, p x = false → x ∉ List.filter p xs
  | [], _, hMem => by cases hMem
  | y :: ys, hpx, hMem => by
    unfold List.filter at hMem
    cases hpy : p y with
    | true =>
      rw [hpy] at hMem
      cases hMem with
      | head _ =>
        rw [hpx] at hpy
        cases hpy
      | tail _ hTail =>
        exact not_mem_filter_of_pred_false p hpx hTail
    | false =>
      rw [hpy] at hMem
      exact not_mem_filter_of_pred_false p hpx hMem

theorem mem_of_mem_filter {α : Type} (p : α → Bool) {x : α} :
    ∀ {xs : List α}, x ∈ List.filter p xs → x ∈ xs
  | [], hMem => by cases hMem
  | y :: ys, hMem => by
    unfold List.filter at hMem
    cases hpy : p y with
    | true =>
      rw [hpy] at hMem
      cases hMem with
      | head _ => exact List.Mem.head _
      | tail _ hTail => exact List.Mem.tail _ (mem_of_mem_filter p hTail)
    | false =>
      rw [hpy] at hMem
      exact List.Mem.tail _ (mem_of_mem_filter p hMem)

theorem pred_of_mem_filter {α : Type} (p : α → Bool) {x : α} :
    ∀ {xs : List α}, x ∈ List.filter p xs → p x = true
  | [], hMem => by cases hMem
  | y :: ys, hMem => by
    unfold List.filter at hMem
    cases hpy : p y with
    | true =>
      rw [hpy] at hMem
      cases hMem with
      | head _ => exact hpy
      | tail _ hTail => exact pred_of_mem_filter p hTail
    | false =>
      rw [hpy] at hMem
      exact pred_of_mem_filter p hMem

/-! ## 1. 2-Hart Relaxed-TLB & Speculative PWC Machine Model -/

/-- Two-hart identifier (`h0` = unmapping/reclaiming core, `h1` = remote core). -/
inductive HartId : Type where
  | h0 : HartId
  | h1 : HartId
  deriving DecidableEq

def HartId.beq : HartId → HartId → Bool
  | .h0, .h0 => true
  | .h1, .h1 => true
  | _,   _   => false

theorem HartId.eq_of_beq_true : ∀ {a b : HartId}, HartId.beq a b = true → a = b
  | .h0, .h0, _ => rfl
  | .h1, .h1, _ => rfl

/-- Physical frame ownership role in the kernel frame allocator. -/
inductive FrameRole : Type where
  | ptLeaf       : FrameRole   -- Live L0 leaf page-table page owned by VSpace
  | quarantined  : FrameRole   -- Unmapped PT page awaiting shootdown completion (immutable)
  | userData     : FrameRole   -- Recycled frame writable by untrusted user/domain
  | kernelSecret : FrameRole   -- Privileged kernel memory (must never be mapped to user)
  deriving DecidableEq

/-- A 64-bit page-table entry (decoded word). -/
structure LeafPte where
  valid  : Bool
  target : Nat      -- Target physical frame number
  deriving DecidableEq

/-- Non-leaf directory entry pointing to a child L0 page-table frame. -/
structure DirPte where
  valid   : Bool
  ptFrame : Nat
  deriving DecidableEq

/-- Cached non-leaf Page-Walk Cache (PWC) entry on a hart. -/
structure PwcEntry where
  asid    : Nat
  dirIdx  : Nat
  ptFrame : Nat
  deriving DecidableEq

/-- Physical page-table / data RAM cell: each frame holds an indexed word array
    modeled as a total function `slot -> LeafPte` (when read by a hardware PT walker,
    raw bytes in a recycled `userData` frame decode as arbitrary `LeafPte` values). -/
structure McVmState where
  rootDir     : Nat → Nat → DirPte          -- rootDir asid dirIdx
  frameRole   : Nat → FrameRole             -- physical frame allocator state
  frameWords  : Nat → Nat → LeafPte         -- physical frame contents (PTE view)
  pwc         : HartId → List PwcEntry      -- per-hart non-leaf Page-Walk Cache
  shootAck    : Nat → HartId → Bool         -- per-frame remote shootdown ACK mask

def updateHart {α : Type} (f : HartId → α) (h : HartId) (v : α) : HartId → α :=
  fun h' => match HartId.beq h' h with | true => v | false => f h'

def updateNat {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α :=
  fun k' => match Nat.beq k' k with | true => v | false => f k'

def updateNat2 {α : Type} (f : Nat → Nat → α) (k1 k2 : Nat) (v : α) : Nat → Nat → α :=
  fun a b => match Nat.beq a k1 && Nat.beq b k2 with | true => v | false => f a b

/-- Speculative or architectural PWC fill on hart `h` from a valid root directory PTE. -/
def fillPwc (st : McVmState) (h : HartId) (asid dirIdx : Nat) : McVmState :=
  let d := st.rootDir asid dirIdx
  match d.valid with
  | true  => { st with pwc := updateHart st.pwc h ({ asid := asid, dirIdx := dirIdx, ptFrame := d.ptFrame } :: st.pwc h) }
  | false => st

/-- Translate `(asid, dirIdx, leafIdx)` on hart `h` via a cached PWC entry `e ∈ st.pwc h`.
    The hardware walker skips the root directory lookup and directly dereferences
    `st.frameWords e.ptFrame leafIdx` in physical RAM. -/
def walkViaPwc (st : McVmState) (e : PwcEntry) (leafIdx : Nat) : Option Nat :=
  let pte := st.frameWords e.ptFrame leafIdx
  match pte.valid with
  | true  => some pte.target
  | false => none

/-- Local-only PWC flush on hart `h` for `asid` (models `SFENCE.VMA x0, asid`
    on hart `h` ONLY — leaves the other hart's PWC untouched). -/
def localFlushPwcAsid (st : McVmState) (h : HartId) (asid : Nat) : McVmState :=
  let kept := List.filter (fun e => !Nat.beq e.asid asid) (st.pwc h)
  { st with pwc := updateHart st.pwc h kept }

/-! ## 2. Counterexample (a): 2-Hart Stale-PWC Use-After-Free on Premature PT Recycle -/

/-- Unsanitized (buggy) page-table unmap on `h0`: clears root PTE, executes ONLY
    local flush on `h0` (skipping remote IPI / `DSB ISH` completion on `h1`),
    immediately recycles `ptFrame` to `userData`, and lets an attacker write a
    forged PTE word pointing to `secretFrame`. -/
def buggyUnmapAndRecycle (st : McVmState) (asid dirIdx ptFrame leafIdx secretFrame : Nat) : McVmState :=
  let st1 : McVmState :=
    { st with rootDir := updateNat2 st.rootDir asid dirIdx { valid := false, ptFrame := 0 } }
  let st2 := localFlushPwcAsid st1 .h0 asid
  let forgedWords := updateNat (st2.frameWords ptFrame) leafIdx { valid := true, target := secretFrame }
  { st2 with
    frameRole  := updateNat st2.frameRole ptFrame .userData
    frameWords := updateNat st2.frameWords ptFrame forgedWords }

/-- Concrete initial 2-hart state:
    - Frame 10 is a valid L0 page-table page (`ptLeaf`) for `(asid=1, dirIdx=0)`.
    - Frame 20 is ordinary user data (`userData`) legitimately mapped at `leafIdx=0`.
    - Frame 99 is privileged `kernelSecret`, NOT mapped anywhere in the page tables. -/
def initUafState : McVmState :=
  { rootDir := fun a d =>
      match Nat.beq a 1 && Nat.beq d 0 with
      | true  => { valid := true, ptFrame := 10 }
      | false => { valid := false, ptFrame := 0 }
    frameRole := fun f =>
      match Nat.beq f 10 with
      | true  => .ptLeaf
      | false =>
        match Nat.beq f 99 with
        | true  => .kernelSecret
        | false => .userData
    frameWords := fun f idx =>
      match Nat.beq f 10 && Nat.beq idx 0 with
      | true  => { valid := true, target := 20 }
      | false => { valid := false, target := 0 }
    pwc      := fun _ => []
    shootAck := fun _ _ => false }

/-- **Theorem (a) — Concrete 2-Hart Stale-Walk Use-After-Free Counterexample:**
    1. Remote hart `h1` speculatively/architecturally fills its PWC for `(asid=1, dirIdx=0)`
       pointing to `ptFrame = 10`.
    2. Core `h0` unmaps `(asid=1, dirIdx=0)`, performs only a local flush on `h0` (no remote
       shootdown completion on `h1`), recycles frame `10` to `userData`, and user code writes
       bytes at `leafIdx=0` decoding as a valid PTE targeting `kernelSecret` (frame `99`).
    3. Even though `rootDir 1 0` is now invalid AND `frameRole 10 = .userData`,
       `h1` still holds the stale PWC entry `e` pointing to frame `10`, and walking via `e`
       resolves to `some 99` (`kernelSecret`)! -/
theorem stale_pwc_uaf_on_premature_pt_recycle :
    let stAfterFill := fillPwc initUafState .h1 1 0
    let stBuggy     := buggyUnmapAndRecycle stAfterFill 1 0 10 0 99
    let staleEntry : PwcEntry := { asid := 1, dirIdx := 0, ptFrame := 10 }
    stBuggy.rootDir 1 0 = { valid := false, ptFrame := 0 } ∧
    stBuggy.frameRole 10 = .userData ∧
    stBuggy.frameRole 99 = .kernelSecret ∧
    staleEntry ∈ stBuggy.pwc .h1 ∧
    walkViaPwc stBuggy staleEntry 0 = some 99 := by
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  exact List.Mem.head _

/-! ## 3. Ghost-State / TCB Contract Hooks & Shootdown Safety Invariant (b) -/

/-- **TCB Contract Hook 1 (`NoStalePwc` / `PtWalkSafeInv`):**
    1. Every valid leaf PTE in any `ptLeaf` or `quarantined` frame targets a non-secret frame.
    2. Every valid root directory entry points to a live `ptLeaf` frame.
    3. Every PWC entry cached on any hart `h` points ONLY to a frame that is either
       `ptLeaf` or `quarantined` (NEVER a recycled `userData` frame!).
    4. If `shootAck f h = true` for a quarantined frame `f`, then hart `h` has NO PWC entry
       pointing to `f` (`NoStalePwcForFrame`). -/
def NoStalePwcForFrame (st : McVmState) (h : HartId) (f : Nat) : Prop :=
  ∀ e : PwcEntry, e ∈ st.pwc h → e.ptFrame ≠ f

def PtSafeInv (st : McVmState) : Prop :=
  (∀ f idx, (st.frameRole f = .ptLeaf ∨ st.frameRole f = .quarantined) →
      (st.frameWords f idx).valid = true →
      st.frameRole (st.frameWords f idx).target ≠ .kernelSecret) ∧
  (∀ a d, (st.rootDir a d).valid = true →
      st.frameRole (st.rootDir a d).ptFrame = .ptLeaf) ∧
  (∀ h e, e ∈ st.pwc h →
      st.frameRole e.ptFrame = .ptLeaf ∨ st.frameRole e.ptFrame = .quarantined) ∧
  (∀ f h, st.frameRole f = .quarantined → st.shootAck f h = true →
      NoStalePwcForFrame st h f)

/-- **TCB Contract Hook 2 (`ShootdownBarrier`):**
    A frame `f` may be recycled to `userData` only after every hart has acknowledged
    PWC invalidation for `f`. -/
def ShootdownComplete (st : McVmState) (f : Nat) : Prop :=
  st.frameRole f = .quarantined ∧ ∀ h : HartId, st.shootAck f h = true

/-- Safe Phase 1: Clear all root directory entries pointing to `ptFrame` and transition
    `ptFrame` from `ptLeaf` to `quarantined` with `shootAck ptFrame _ = false`
    (contents of `ptFrame` remain frozen while quarantined). -/
def safeUnmapAndQuarantine (st : McVmState) (ptFrame : Nat) : McVmState :=
  { st with
    rootDir := fun a d =>
      let cur := st.rootDir a d
      match cur.valid && Nat.beq cur.ptFrame ptFrame with
      | true  => { valid := false, ptFrame := 0 }
      | false => cur
    frameRole := updateNat st.frameRole ptFrame .quarantined
    shootAck  := updateNat st.shootAck ptFrame (fun _ => false) }

/-- Safe Phase 2: Hart `h` executes remote/local PWC invalidation (`SFENCE.VMA x0, ...` /
    `TLBI ASIDE1IS` + `DSB ISH` / `INVPCID`) clearing any PWC entry pointing to `ptFrame`,
    then records `shootAck ptFrame h := true`. -/
def safeHartAckShootdown (st : McVmState) (h : HartId) (ptFrame : Nat) : McVmState :=
  let kept := List.filter (fun e => !Nat.beq e.ptFrame ptFrame) (st.pwc h)
  { st with
    pwc      := updateHart st.pwc h kept
    shootAck := updateNat st.shootAck ptFrame (updateHart (st.shootAck ptFrame) h true) }

/-- Safe Phase 3: Recycle `ptFrame` to `userData` and allow arbitrary user/attacker writes
    `newWords` to `ptFrame`, guarded by `ShootdownComplete st ptFrame`. -/
def safeRecycleAfterShootdown (st : McVmState) (ptFrame : Nat) (newWords : Nat → LeafPte) : McVmState :=
  { st with
    frameRole  := updateNat st.frameRole ptFrame .userData
    frameWords := updateNat st.frameWords ptFrame newWords }

theorem fillPwc_preserves_PtSafeInv (st : McVmState) (h : HartId) (asid dirIdx : Nat)
    (hInv : PtSafeInv st) :
    PtSafeInv (fillPwc st h asid dirIdx) := by
  have ⟨hWords, hRoot, hPwc, hAck⟩ := hInv
  unfold fillPwc
  dsimp
  cases hd : (st.rootDir asid dirIdx).valid with
  | false =>
    exact ⟨hWords, hRoot, hPwc, hAck⟩
  | true =>
    refine ⟨hWords, hRoot, ?_, ?_⟩
    { intro h' e hMem
      dsimp [updateHart] at hMem
      cases hEq : HartId.beq h' h with
      | false =>
        rw [hEq] at hMem
        exact hPwc h' e hMem
      | true =>
        rw [hEq] at hMem
        cases hMem with
        | head _ =>
          exact Or.inl (hRoot asid dirIdx hd)
        | tail _ hTail =>
          exact hPwc h e hTail }
    { intro f h' hQuar hAckTrue e hMem
      dsimp [updateHart] at hMem
      cases hEq : HartId.beq h' h with
      | false =>
        rw [hEq] at hMem
        exact hAck f h' hQuar hAckTrue e hMem
      | true =>
        have hh : h' = h := HartId.eq_of_beq_true hEq
        subst hh
        rw [hEq] at hMem
        cases hMem with
        | head _ =>
          intro hFrameEq
          dsimp at hFrameEq hQuar
          have hLive : st.frameRole (st.rootDir asid dirIdx).ptFrame = .ptLeaf := hRoot asid dirIdx hd
          rw [hFrameEq] at hLive
          rw [hLive] at hQuar
          cases hQuar
        | tail _ hTail =>
          exact hAck f h' hQuar hAckTrue e hTail }

theorem safeUnmapAndQuarantine_preserves_PtSafeInv (st : McVmState) (ptFrame : Nat)
    (hWasPt : st.frameRole ptFrame = .ptLeaf)
    (hInv : PtSafeInv st) :
    PtSafeInv (safeUnmapAndQuarantine st ptFrame) := by
  have ⟨hWords, hRoot, hPwc, hAck⟩ := hInv
  unfold safeUnmapAndQuarantine
  refine ⟨?_, ?_, ?_, ?_⟩
  { intro f idx hRole hVal
    dsimp [updateNat] at hRole ⊢
    cases hEq : Nat.beq f ptFrame with
    | true =>
      have hf : f = ptFrame := Nat.eq_of_beq_eq_true hEq
      subst hf
      have hNotSec : st.frameRole (st.frameWords f idx).target ≠ .kernelSecret :=
        hWords f idx (Or.inl hWasPt) hVal
      cases hT : Nat.beq (st.frameWords f idx).target f with
      | true => intro hK; cases hK
      | false => exact hNotSec
    | false =>
      rw [hEq] at hRole
      have hNotSec : st.frameRole (st.frameWords f idx).target ≠ .kernelSecret :=
        hWords f idx hRole hVal
      cases hT : Nat.beq (st.frameWords f idx).target ptFrame with
      | true => intro hK; cases hK
      | false => exact hNotSec }
  { intro a d hVal
    dsimp [updateNat] at hVal ⊢
    cases hMatch : ((st.rootDir a d).valid && Nat.beq (st.rootDir a d).ptFrame ptFrame) with
    | true =>
      rw [hMatch] at hVal
      cases hVal
    | false =>
      rw [hMatch] at hVal
      have hLive := hRoot a d hVal
      cases hEq : Nat.beq (st.rootDir a d).ptFrame ptFrame with
      | true =>
        rw [hVal, hEq] at hMatch
        cases hMatch
      | false =>
        exact hLive }
  { intro h e hMem
    dsimp [updateNat]
    cases hEq : Nat.beq e.ptFrame ptFrame with
    | true  => exact Or.inr rfl
    | false => exact hPwc h e hMem }
  { intro f h hQuar hAckTrue
    dsimp [updateNat] at hQuar hAckTrue
    cases hEq : Nat.beq f ptFrame with
    | true =>
      rw [hEq] at hAckTrue
      cases hAckTrue
    | false =>
      rw [hEq] at hQuar hAckTrue
      exact hAck f h hQuar hAckTrue }

theorem safeHartAckShootdown_preserves_PtSafeInv (st : McVmState) (h : HartId) (ptFrame : Nat)
    (hInv : PtSafeInv st) :
    PtSafeInv (safeHartAckShootdown st h ptFrame) := by
  have ⟨hWords, hRoot, hPwc, hAck⟩ := hInv
  unfold safeHartAckShootdown
  refine ⟨hWords, hRoot, ?_, ?_⟩
  { intro h' e hMem
    dsimp [updateHart] at hMem
    cases hEq : HartId.beq h' h with
    | false =>
      rw [hEq] at hMem
      exact hPwc h' e hMem
    | true =>
      rw [hEq] at hMem
      exact hPwc h e (mem_of_mem_filter _ hMem) }
  { intro f h' hQuar hAckTrue e hMem
    dsimp [updateNat, updateHart] at hAckTrue hMem
    cases hFeq : Nat.beq f ptFrame with
    | true =>
      have hf : f = ptFrame := Nat.eq_of_beq_eq_true hFeq
      subst hf
      rw [hFeq] at hAckTrue
      dsimp [updateHart] at hAckTrue
      cases hHeq : HartId.beq h' h with
      | true =>
        rw [hHeq] at hMem
        intro hPtEq
        have hPredFalse : (!Nat.beq e.ptFrame f) = false := by
          rw [hPtEq, Nat.beq_refl]; rfl
        exact not_mem_filter_of_pred_false (fun x : PwcEntry => !Nat.beq x.ptFrame f) hPredFalse hMem
      | false =>
        rw [hHeq] at hAckTrue hMem
        exact hAck f h' hQuar hAckTrue e hMem
    | false =>
      rw [hFeq] at hAckTrue
      cases hHeq : HartId.beq h' h with
      | true =>
        have hh : h' = h := HartId.eq_of_beq_true hHeq
        subst hh
        rw [hHeq] at hMem
        exact hAck f h' hQuar hAckTrue e (mem_of_mem_filter _ hMem)
      | false =>
        rw [hHeq] at hMem
        exact hAck f h' hQuar hAckTrue e hMem }

/-- **Theorem (b1) — Shootdown Barrier Preserves `PtSafeInv` Across Arbitrary Recycling:**
    Once `ShootdownComplete st ptFrame` holds (every hart has ACKed PWC invalidation),
    recycling `ptFrame` to `userData` and overwriting it with arbitrary attacker words
    `newWords` (even forged PTEs pointing to `kernelSecret`!) preserves `PtSafeInv`. -/
theorem safeRecycleAfterShootdown_preserves_PtSafeInv
    (st : McVmState) (ptFrame : Nat) (newWords : Nat → LeafPte)
    (hDone : ShootdownComplete st ptFrame)
    (hInv : PtSafeInv st) :
    PtSafeInv (safeRecycleAfterShootdown st ptFrame newWords) := by
  have ⟨hQuar, hAllAck⟩ := hDone
  have ⟨hWords, hRoot, hPwc, hAck⟩ := hInv
  unfold safeRecycleAfterShootdown
  refine ⟨?_, ?_, ?_, ?_⟩
  { intro f idx hRole hVal
    dsimp [updateNat] at hRole hVal ⊢
    cases hEq : Nat.beq f ptFrame with
    | true =>
      rw [hEq] at hRole
      cases hRole with
      | inl h1 => cases h1
      | inr h2 => cases h2
    | false =>
      rw [hEq] at hRole hVal
      have hNotSec := hWords f idx hRole hVal
      cases hT : Nat.beq (st.frameWords f idx).target ptFrame with
      | true  => intro hK; cases hK
      | false => exact hNotSec }
  { intro a d hVal
    dsimp [updateNat]
    have hLive := hRoot a d hVal
    cases hEq : Nat.beq (st.rootDir a d).ptFrame ptFrame with
    | true =>
      have hSame := Nat.eq_of_beq_eq_true hEq
      rw [hSame, hQuar] at hLive
      cases hLive
    | false => exact hLive }
  { intro h e hMem
    dsimp [updateNat]
    cases hEq : Nat.beq e.ptFrame ptFrame with
    | true =>
      have hSame := Nat.eq_of_beq_eq_true hEq
      exact False.elim (hAck ptFrame h hQuar (hAllAck h) e hMem hSame)
    | false =>
      exact hPwc h e hMem }
  { intro f h hFQuar hFAck
    dsimp [updateNat] at hFQuar
    cases hEq : Nat.beq f ptFrame with
    | true =>
      rw [hEq] at hFQuar
      cases hFQuar
    | false =>
      rw [hEq] at hFQuar
      exact hAck f h hFQuar hFAck }

/-- **Theorem (b2) — Zero Stale-Walk Privilege Escalation:**
    Under `PtSafeInv st`, NO hart `h` can walk through ANY cached PWC entry `e ∈ st.pwc h`
    and resolve to a `kernelSecret` frame (nor ever touch a recycled `userData` PT page). -/
theorem ptSafeInv_excludes_uaf_and_secret_access
    (st : McVmState) (hInv : PtSafeInv st) (h : HartId) (e : PwcEntry) (leafIdx target : Nat)
    (hMem : e ∈ st.pwc h)
    (hWalk : walkViaPwc st e leafIdx = some target) :
    st.frameRole e.ptFrame ≠ .userData ∧ st.frameRole target ≠ .kernelSecret := by
  have ⟨hWords, _, hPwc, _⟩ := hInv
  have hRole := hPwc h e hMem
  refine ⟨?_, ?_⟩
  { intro hU
    cases hRole with
    | inl h1 => rw [hU] at h1; cases h1
    | inr h2 => rw [hU] at h2; cases h2 }
  { unfold walkViaPwc at hWalk
    dsimp at hWalk
    cases hv : (st.frameWords e.ptFrame leafIdx).valid with
    | false => rw [hv] at hWalk; cases hWalk
    | true =>
      rw [hv] at hWalk
      cases hWalk
      exact hWords e.ptFrame leafIdx hRole hv }

/-! ## 4. AArch64 Break-Before-Make (BBM) & TLB Conflict Mechanization -/

inductive BlockGranule : Type where
  | page4K  : BlockGranule
  | block2M : BlockGranule
  deriving DecidableEq

structure TlbEntry where
  asid    : Nat
  va      : Nat
  granule : BlockGranule
  oa      : Nat
  deriving DecidableEq

structure BbmState where
  liveDesc : Nat → Nat → Option (BlockGranule × Nat)
  tlb      : HartId → List TlbEntry

def TlbEntry.matchesAddr (e : TlbEntry) (asid va : Nat) : Bool :=
  Nat.beq e.asid asid && Nat.beq e.va va

/-- Two TLB entries on the same hart conflict if they match the same `(asid, va)`
    with differing granule or output address (Arm DDI 0487 BBM violation ->
    TLB conflict abort or CONSTRAINED UNPREDICTABLE amalgamation). -/
def HasTlbConflict (st : BbmState) (h : HartId) (asid va : Nat) : Prop :=
  Exists fun e1 : TlbEntry =>
    Exists fun e2 : TlbEntry =>
      e1 ∈ st.tlb h ∧ e2 ∈ st.tlb h ∧
      e1.asid = asid ∧ e1.va = va ∧
      e2.asid = asid ∧ e2.va = va ∧
      (e1.granule ≠ e2.granule ∨ e1.oa ≠ e2.oa)

/-- **TCB Contract Hook (`NoStaleTlb` / `NoTlbConflict`):**
    Every cached TLB entry on every hart matches the current live descriptor
    (which immediately excludes multi-hit TLB conflicts). -/
def TlbMatchesLive (st : BbmState) : Prop :=
  ∀ h e, e ∈ st.tlb h → st.liveDesc e.asid e.va = some (e.granule, e.oa)

def tlbFill (st : BbmState) (h : HartId) (asid va : Nat) : BbmState :=
  match st.liveDesc asid va with
  | none => st
  | some (g, oa) =>
    { st with tlb := updateHart st.tlb h ({ asid := asid, va := va, granule := g, oa := oa } :: st.tlb h) }

/-- Direct overwrite without Break-Before-Make (violates Arm DDI 0487 BBM Level 0). -/
def overwriteWithoutBbm (st : BbmState) (asid va : Nat) (g : BlockGranule) (oa : Nat) : BbmState :=
  { st with liveDesc := updateNat2 st.liveDesc asid va (some (g, oa)) }

/-- **Theorem (a2) — Concrete BBM Violation Counterexample:**
    Overwriting a valid 2 MiB block mapping with a 4 KiB mapping without `Break -> TLBI IS -> DSB ISH`
    allows `h1` to cache both entries simultaneously, producing a TLB conflict. -/
theorem bbm_violation_creates_tlb_conflict :
    let st0 : BbmState :=
      { liveDesc := fun a v =>
          match Nat.beq a 1 && Nat.beq v 0x200000 with
          | true  => some (.block2M, 0x4000)
          | false => none
        tlb := fun _ => [] }
    let st1 := tlbFill st0 .h1 1 0x200000
    let st2 := overwriteWithoutBbm st1 1 0x200000 .page4K 0x5000
    let st3 := tlbFill st2 .h1 1 0x200000
    HasTlbConflict st3 .h1 1 0x200000 := by
  refine ⟨{ asid := 1, va := 0x200000, granule := .page4K, oa := 0x5000 },
          { asid := 1, va := 0x200000, granule := .block2M, oa := 0x4000 },
          List.Mem.head _, List.Mem.tail _ (List.Mem.head _),
          rfl, rfl, rfl, rfl, Or.inl (fun h => by cases h)⟩

/-- Canonical Break-Before-Make sequence across all harts:
    1. Break (`liveDesc asid va := none`)
    2. Broadcast invalidate + completion barrier (`TLBI VAE1IS` + `DSB ISH` / IPI-ACK)
    3. Make (`liveDesc asid va := some (g, oa)`). -/
def bbmBreak (st : BbmState) (asid va : Nat) : BbmState :=
  { st with liveDesc := updateNat2 st.liveDesc asid va none }

def bbmTlbiIshDsb (st : BbmState) (asid va : Nat) : BbmState :=
  { st with tlb := fun h => List.filter (fun e => !e.matchesAddr asid va) (st.tlb h) }

def bbmMake (st : BbmState) (asid va : Nat) (g : BlockGranule) (oa : Nat) : BbmState :=
  { st with liveDesc := updateNat2 st.liveDesc asid va (some (g, oa)) }

/-- **Theorem (b3) — Canonical BBM Protocol Preserves `TlbMatchesLive` and Excludes TLB Conflicts:** -/
theorem bbm_update_preserves_no_conflict
    (st : BbmState) (asid va : Nat) (g : BlockGranule) (oa : Nat)
    (hInv : TlbMatchesLive st) :
    let stFinal := bbmMake (bbmTlbiIshDsb (bbmBreak st asid va) asid va) asid va g oa
    TlbMatchesLive stFinal ∧ ∀ h a v, ¬HasTlbConflict stFinal h a v := by
  have hFinalInv : TlbMatchesLive (bbmMake (bbmTlbiIshDsb (bbmBreak st asid va) asid va) asid va g oa) := by
    intro h e hMem
    unfold bbmMake bbmTlbiIshDsb bbmBreak at hMem ⊢
    dsimp [updateNat2] at hMem ⊢
    have hOrigMem : e ∈ st.tlb h := mem_of_mem_filter (fun x => !TlbEntry.matchesAddr x asid va) hMem
    have hPred : (!TlbEntry.matchesAddr e asid va) = true := pred_of_mem_filter (fun x => !TlbEntry.matchesAddr x asid va) hMem
    unfold TlbEntry.matchesAddr at hPred
    cases hMatch : (Nat.beq e.asid asid && Nat.beq e.va va) with
    | true =>
      rw [hMatch] at hPred
      cases hPred
    | false =>
      exact hInv h e hOrigMem
  refine ⟨hFinalInv, ?_⟩
  intro h a v hConf
  have ⟨e1, e2, hm1, hm2, ha1, hv1, ha2, hv2, hDiff⟩ := hConf
  have h1 := hFinalInv h e1 hm1
  have h2 := hFinalInv h e2 hm2
  rw [ha1, hv1] at h1
  rw [ha2, hv2] at h2
  have hEqOpt : some (e1.granule, e1.oa) = some (e2.granule, e2.oa) := Eq.trans h1.symm h2
  have hPair : (e1.granule, e1.oa) = (e2.granule, e2.oa) := Option.some.inj hEqOpt
  cases hDiff with
  | inl hg  => exact hg (congrArg Prod.fst hPair)
  | inr hoa => exact hoa (congrArg Prod.snd hPair)

/-! ## 5. Multicore ASID Generation Rollover Contract (`AsidGen`) -/

/-- Per-hart TLB tag associating a cached hardware ASID with the domain `mmId`
    that populated it. -/
structure AsidTlbTag where
  hwAsid : Nat
  mmId   : Nat
  deriving DecidableEq

/-- Minimal multicore ASID generation state (`AsidGen` ghost contract):
    models Linux `arch/arm64/mm/context.c` / `arch/riscv/mm/context.c` rollover. -/
structure AsidGenState where
  curGen       : Nat
  mmAsid       : Nat → Nat × Nat          -- mmId -> (hwAsid, gen)
  activeMm     : HartId → Nat             -- currently running mmId on hart
  reservedAsid : HartId → Nat             -- hardware ASID reserved during rollover
  flushPending : HartId → Bool            -- pending local TLB flush flag
  hartTlb      : HartId → List AsidTlbTag -- cached (hwAsid, originating mmId) entries

/-- **TCB Contract Hook 3 (`AsidGenInv`):**
    On every hart `h` whose `flushPending h = false`, every cached TLB tag matching
    the hardware ASID of `h`'s active `mm` belongs strictly to `activeMm h` (no cross-domain aliasing).
    Moreover, across the current generation `curGen`, distinct domains have distinct hardware ASIDs
    whenever both are stamped with `curGen`. -/
def AsidGenInv (st : AsidGenState) : Prop :=
  (∀ h tag, st.flushPending h = false → tag ∈ st.hartTlb h →
      tag.hwAsid = (st.mmAsid (st.activeMm h)).1 → tag.mmId = st.activeMm h) ∧
  (∀ m1 m2, (st.mmAsid m1).2 = st.curGen → (st.mmAsid m2).2 = st.curGen →
      (st.mmAsid m1).1 = (st.mmAsid m2).1 → m1 = m2)

/-- Generation rollover (models `flush_context` in Linux `arch/arm64/mm/context.c:104-132`):
    bumps `curGen := curGen + 1`, snapshots each hart's active hardware ASID into
    `reservedAsid`, and sets `flushPending h := true` for ALL harts. -/
def asidRollover (st : AsidGenState) : AsidGenState :=
  { st with
    curGen       := st.curGen + 1
    reservedAsid := fun h => (st.mmAsid (st.activeMm h)).1
    flushPending := fun _ => true }

/-- Context switch on hart `h` to `nextMm` when `flushPending h = true`:
    executes `local_flush_tlb_all()` (clearing `hartTlb h := []`), clears `flushPending h`,
    and installs `activeMm h := nextMm`. -/
def switchWithPendingFlush (st : AsidGenState) (h : HartId) (nextMm : Nat) : AsidGenState :=
  { st with
    activeMm     := updateHart st.activeMm h nextMm
    flushPending := updateHart st.flushPending h false
    hartTlb      := updateHart st.hartTlb h [] }

/-- **Theorem (a3) — Concrete ASID Rollover Aliasing Without Pending Flush:**
    If `curGen` advances and `hwAsid = 1` is reassigned from `mm = 10` to `mm = 20`
    while `h1` keeps `hartTlb .h1 = [{ hwAsid := 1, mmId := 10 }]` and switches to
    `mm = 20` without flushing, `h1`'s TLB aliases `hwAsid = 1` to the wrong domain (`10 ≠ 20`). -/
theorem asid_rollover_without_flush_aliases_domains :
    let tag : AsidTlbTag := { hwAsid := 1, mmId := 10 }
    let stAliased : AsidGenState :=
      { curGen       := 1
        mmAsid       := fun m => match Nat.beq m 20 with | true => (1, 1) | false => (1, 0)
        activeMm     := fun _ => 20
        reservedAsid := fun _ => 0
        flushPending := fun _ => false
        hartTlb      := fun h => match h with | .h1 => [tag] | .h0 => [] }
    tag ∈ stAliased.hartTlb .h1 ∧
    tag.hwAsid = (stAliased.mmAsid (stAliased.activeMm .h1)).1 ∧
    tag.mmId ≠ stAliased.activeMm .h1 := by
  refine ⟨List.Mem.head _, rfl, fun h => by cases h⟩

/-- **Theorem (b4) — Generation Rollover + Pending Local Flush Preserves Domain Isolation:**
    After `asidRollover` sets `flushPending _ = true`, any hart `h` performing
    `switchWithPendingFlush` clears its stale TLB entries and restores the no-aliasing
    invariant for `h` (while other harts remain safely fenced behind `flushPending = true`). -/
theorem asid_rollover_flush_preserves_isolation
    (st : AsidGenState) (h : HartId) (nextMm : Nat)
    (hNoStaleGen : ∀ m, (st.mmAsid m).2 ≠ st.curGen + 1) :
    let stRolled := asidRollover st
    let stSwitched := switchWithPendingFlush stRolled h nextMm
    AsidGenInv stSwitched := by
  refine ⟨?_, ?_⟩
  { intro h' tag hNoPend hMem _
    unfold switchWithPendingFlush asidRollover at hNoPend hMem
    dsimp [updateHart] at hNoPend hMem
    cases hEq : HartId.beq h' h with
    | true =>
      rw [hEq] at hMem
      cases hMem
    | false =>
      rw [hEq] at hNoPend
      cases hNoPend }
  { intro m1 m2 hG1 _ _
    unfold switchWithPendingFlush asidRollover at hG1
    dsimp at hG1
    exact False.elim (hNoStaleGen m1 hG1) }

end MulticoreTlbShootdown

-- Axiom closure verification (must contain zero sorryAx, zero Classical.choice, zero custom axioms)
#print axioms MulticoreTlbShootdown.stale_pwc_uaf_on_premature_pt_recycle
#print axioms MulticoreTlbShootdown.fillPwc_preserves_PtSafeInv
#print axioms MulticoreTlbShootdown.safeUnmapAndQuarantine_preserves_PtSafeInv
#print axioms MulticoreTlbShootdown.safeHartAckShootdown_preserves_PtSafeInv
#print axioms MulticoreTlbShootdown.safeRecycleAfterShootdown_preserves_PtSafeInv
#print axioms MulticoreTlbShootdown.ptSafeInv_excludes_uaf_and_secret_access
#print axioms MulticoreTlbShootdown.bbm_violation_creates_tlb_conflict
#print axioms MulticoreTlbShootdown.bbm_update_preserves_no_conflict
#print axioms MulticoreTlbShootdown.asid_rollover_without_flush_aliases_domains
#print axioms MulticoreTlbShootdown.asid_rollover_flush_preserves_isolation
