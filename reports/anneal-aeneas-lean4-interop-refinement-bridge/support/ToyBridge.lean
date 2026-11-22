/-!
# Toy Zero-TCB `Anneal ↔ Aeneas` Bridge Witness (Mathlib-free, Lean v4.34.1+)

Self-contained miniature witness demonstrating the exact refinement predicates,
outcome-transfer theorems (`WP.spec` and `WP.dspec`), disjoint `&mut` framing,
empty-slice (`len = 0`) dangling-pointer handling, backward-function / prophecy
equivalence (`split_at_mut`), and two negative counterexamples (aliasing and
frame violation).

**Honest scope label:** `[kernel-checked proof]` `[toy model]`.
The operational semantics (`AnnealMini`) and monad (`AeneasMini`) are compact,
Mathlib-free miniatures of `Trusted.MirModel`/`Trusted.MirSemantics.Boundary`
(`google/zerocopy:main`) and `Aeneas.Std.{Primitives,WP,SliceDef}`
(`AeneasVerif/aeneas`), not the full MIR interpreter or full `ITree` library.
-/

set_option autoImplicit false

namespace ToyAnnealAeneasBridge

/-! ## 1. Miniature Anneal Operational Boundary (`AnnealMini`) -/

namespace AnnealMini

inductive FaultKind where
  | undefined
  | unsupported
  deriving DecidableEq

inductive Mutability where
  | shared
  | mut
  deriving DecidableEq

inductive AllocByte where
  | uninit
  | init (byte : UInt8) (prov : Option Nat := none)
  deriving DecidableEq

structure Allocation where
  allocId : Nat
  alignLog2 : Nat
  mutability : Mutability
  bytes : List AllocByte
  live : Bool := true

structure CallerMemory where
  allocations : List Allocation := []

structure PtrVal where
  allocId : Option Nat
  offsetBytes : Nat
  deriving DecidableEq

inductive Val where
  | u8 (v : BitVec 8)
  | u64 (v : BitVec 64)
  | ptr (p : PtrVal)
  | slice (p : PtrVal) (len : Nat)
  | unit
  | pair (a b : Val)
  deriving DecidableEq

structure Query where
  args : List Val
  callerMem : CallerMemory := ⟨[]⟩

structure Out where
  ret : Val
  callerMem : CallerMemory := ⟨[]⟩

/-- Four-way observable execution partition (extending `Trusted.MirModel.TerminalOut`
    with explicit `aborted` alongside `returned`, `unwound`, and `Diverges`). -/
inductive TerminalOut where
  | returned (out : Out)
  | unwound (callerMem : CallerMemory := ⟨[]⟩)
  | aborted (callerMem : CallerMemory := ⟨[]⟩)

inductive StepResult (State OutT : Type) where
  | step (next : State)
  | done (out : OutT)
  | fault (kind : FaultKind)

/-- Abstract small-step machine with single-step deterministic or relational semantics. -/
structure Machine where
  State : Type
  initState : Query → Except FaultKind State
  step : State → StepResult State TerminalOut

inductive Reaches (m : Machine) : m.State → m.State → Prop where
  | refl (s : m.State) : Reaches m s s
  | tail {s₁ s₂ s₃ : m.State} :
      Reaches m s₁ s₂ →
      m.step s₂ = .step s₃ →
      Reaches m s₁ s₃

def ReachesResult (m : Machine) (q : Query) (res : StepResult m.State TerminalOut) : Prop :=
  match m.initState q with
  | .error k => res = .fault k
  | .ok s₀ => ∃ s, Reaches m s₀ s ∧ m.step s = res

def WellFormed (m : Machine) (q : Query) : Prop :=
  (∃ s₀, m.initState q = .ok s₀) ∧
  (∀ k, ¬ ReachesResult m q (.fault k))

def Behavior (m : Machine) (q : Query) (out : TerminalOut) : Prop :=
  ReachesResult m q (.done out)

def Diverges (m : Machine) (q : Query) : Prop :=
  ∃ s₀, m.initState q = .ok s₀ ∧
    ∃ trace : Nat → m.State,
      trace 0 = s₀ ∧
      ∀ n, m.step (trace n) = .step (trace (n + 1))

/-- Memory lookup and byte-range update helpers. -/
def findAlloc (aid : Nat) : List Allocation → Option Allocation
  | [] => none
  | a :: rest => if a.allocId == aid then some a else findAlloc aid rest

def replaceAlloc (a' : Allocation) : List Allocation → List Allocation
  | [] => []
  | a :: rest => if a.allocId == a'.allocId then a' :: rest else a :: replaceAlloc a' rest

def readSliceBytes (mem : CallerMemory) (ptr : PtrVal) (len : Nat) :
    Except FaultKind (List UInt8) :=
  if len == 0 then
    if ptr.offsetBytes == 0 then .error .undefined else .ok []
  else
    match ptr.allocId with
    | none => .error .undefined
    | some aid =>
      match findAlloc aid mem.allocations with
      | none => .error .undefined
      | some a =>
        if !a.live || !(ptr.offsetBytes + len ≤ a.bytes.length) then
          .error .undefined
        else
          let raw := (a.bytes.drop ptr.offsetBytes).take len
          let rec extractInit : List AllocByte → Except FaultKind (List UInt8)
            | [] => .ok []
            | .uninit :: _ => .error .undefined
            | .init b _ :: bs =>
              match extractInit bs with
              | .ok rest => .ok (b :: rest)
              | .error k => .error k
          extractInit raw

def writeSliceBytes (mem : CallerMemory) (ptr : PtrVal) (bs : List UInt8) :
    Except FaultKind CallerMemory :=
  if bs.length == 0 then
    if ptr.offsetBytes == 0 then .error .undefined else .ok mem
  else
    match ptr.allocId with
    | none => .error .undefined
    | some aid =>
      match findAlloc aid mem.allocations with
      | none => .error .undefined
      | some a =>
        if !a.live || a.mutability != .mut || !(ptr.offsetBytes + bs.length ≤ a.bytes.length) then
          .error .undefined
        else
          let written := bs.map (fun b => AllocByte.init b none)
          let bytes' := a.bytes.take ptr.offsetBytes ++ written ++
            a.bytes.drop (ptr.offsetBytes + bs.length)
          .ok ⟨replaceAlloc { a with bytes := bytes' } mem.allocations⟩

/-- Construct a single-step leaf machine directly from a total transition function. -/
def singleStepMachine (eval : Query → StepResult Unit TerminalOut) : Machine where
  State := Query
  initState := fun q => .ok q
  step := fun q =>
    match eval q with
    | .step () => .step q
    | .done o => .done o
    | .fault k => .fault k

theorem singleStep_done_wf (eval : Query → StepResult Unit TerminalOut) (q : Query)
    (out : TerminalOut) (h : eval q = .done out) :
    WellFormed (singleStepMachine eval) q ∧
    ¬ Diverges (singleStepMachine eval) q ∧
    (∀ o, Behavior (singleStepMachine eval) q o → o = out) := by
  have hstep : (singleStepMachine eval).step q = .done out := by
    simp [singleStepMachine, h]
  have hreach : ∀ s, Reaches (singleStepMachine eval) q s → s = q := by
    intro s hr
    induction hr with
    | refl => rfl
    | tail _ hst ih =>
      subst ih
      rw [hstep] at hst
      cases hst
  refine ⟨⟨⟨q, rfl⟩, ?_⟩, ?_, ?_⟩
  · intro k hk
    simp only [ReachesResult, singleStepMachine] at hk
    rcases hk with ⟨s, hr, hs⟩
    have hsq := hreach s hr
    subst hsq
    rw [h] at hs
    cases hs
  · intro hdiv
    rcases hdiv with ⟨s₀, hinit, trace, h0, htr⟩
    simp only [singleStepMachine] at hinit
    injection hinit with hq
    subst hq
    have htr0 := htr 0
    rw [h0, hstep] at htr0
    cases htr0
  · intro o ho
    simp only [Behavior, ReachesResult, singleStepMachine] at ho
    rcases ho with ⟨s, hr, hs⟩
    have hsq := hreach s hr
    subst hsq
    rw [h] at hs
    injection hs with ho'
    exact ho'.symm

end AnnealMini

/-! ## 2. Miniature Aeneas Standard Library & WP (`AeneasMini`) -/

namespace AeneasMini

inductive Error where
  | assertionFailure
  | integerOverflow
  | divisionByZero
  | arrayOutOfBounds
  | maximumSizeExceeded
  | panic
  | undef
  deriving DecidableEq

/-- Miniature of `Aeneas.Std.Result α := ITree RustEffect α` with `.ok`, `.fail`, `.div`. -/
inductive Result (α : Type) where
  | ok (a : α)
  | fail (e : Error)
  | div
  deriving DecidableEq

namespace WP

/-- Miniature of `Aeneas.Std.WP.spec` (`DWP`: total correctness + panic-freedom). -/
def spec {α : Type} (m : Result α) (P : α → Prop) : Prop :=
  match m with
  | .ok a => P a
  | .fail _ => False
  | .div => False

/-- Miniature of `Aeneas.Std.WP.dspec` (`DWLP`: partial correctness + panic-freedom). -/
def dspec {α : Type} (m : Result α) (P : α → Prop) : Prop :=
  match m with
  | .ok a => P a
  | .fail _ => False
  | .div => True

theorem spec_dspec {α : Type} (m : Result α) (P : α → Prop) :
    spec m P → dspec m P := by
  cases m <;> simp [spec, dspec]

theorem spec_ok {α : Type} (a : α) (P : α → Prop) : spec (.ok a) P ↔ P a := Iff.rfl
theorem spec_fail {α : Type} (e : Error) (P : α → Prop) : spec (.fail e) P ↔ False := Iff.rfl
theorem spec_div {α : Type} (P : α → Prop) : spec .div P ↔ False := Iff.rfl

end WP

structure U8 where
  bv : BitVec 8
  deriving DecidableEq

structure U64 where
  bv : BitVec 64
  deriving DecidableEq

def usizeMax64 : Nat := 2^64 - 1
def isizeMax64 : Nat := 2^63 - 1

/-- Miniature of `Aeneas.Std.Slice U8` on 64-bit targets. -/
structure ByteSlice where
  val : List U8
  bound : val.length ≤ usizeMax64

end AeneasMini

/-! ## 3. Zero-TCB Bridge Predicates & Outcome-Transfer Theorems (`Bridge`) -/

namespace Bridge

open AnnealMini AeneasMini

/-- Exact 64-bit unsigned scalar refinement. -/
def ValRefinesU64 (v : Val) (x : U64) : Prop :=
  v = .u64 x.bv

/-- Exact byte-slice refinement (`&[u8]`), handling BOTH:
    - `len = 0`: valid Rust empty slice permits a dangling non-null pointer (`offsetBytes ≠ 0`),
      requiring no live allocation;
    - `len > 0`: requires `len ≤ isize::MAX`, a live allocation matching `ptr.allocId`,
      in-bounds `[offset, offset + len)`, and every byte initialized (`AllocByte.init b _`). -/
def MemRefinesByteSlice (ptr : PtrVal) (len : Nat) (mem : CallerMemory)
    (s : ByteSlice) : Prop :=
  len = s.val.length ∧
  len ≤ isizeMax64 ∧
  if len = 0 then
    ptr.offsetBytes ≠ 0
  else
    ∃ aid a,
      ptr.allocId = some aid ∧
      findAlloc aid mem.allocations = some a ∧
      a.live = true ∧
      ptr.offsetBytes + len ≤ a.bytes.length ∧
      ∀ (i : Nat) (hi : i < s.val.length),
        ∃ prov,
          a.bytes[ptr.offsetBytes + i]? =
            some (.init (UInt8.ofBitVec (s.val[i]'hi).bv) prov)

/-- Mutable byte-slice refinement (`&mut [u8]`): adds `a.mutability = .mut` on non-empty slices. -/
def MemRefinesByteSliceMut (ptr : PtrVal) (len : Nat) (mem : CallerMemory)
    (s : ByteSlice) : Prop :=
  MemRefinesByteSlice ptr len mem s ∧
  (len > 0 →
    ∃ aid a,
      ptr.allocId = some aid ∧
      findAlloc aid mem.allocations = some a ∧
      a.mutability = .mut)

/-- Byte footprint containment predicate for spatial disjointness & framing. -/
def InFootprint (ptr : PtrVal) (len : Nat) (aid off : Nat) : Prop :=
  len > 0 ∧ ptr.allocId = some aid ∧ ptr.offsetBytes ≤ off ∧ off < ptr.offsetBytes + len

def DisjointFootprints (p1 : PtrVal) (l1 : Nat) (p2 : PtrVal) (l2 : Nat) : Prop :=
  ∀ aid off, ¬ (InFootprint p1 l1 aid off ∧ InFootprint p2 l2 aid off)

/-- Frame preservation: every allocation and byte outside the mutable footprint `(mutPtr, mutLen)`
    is completely unchanged between `mem0` and `mem1`. -/
def FramePreserved (mutPtr : PtrVal) (mutLen : Nat)
    (mem0 mem1 : CallerMemory) : Prop :=
  ∀ aid,
    match findAlloc aid mem0.allocations, findAlloc aid mem1.allocations with
    | none, none => True
    | some a0, some a1 =>
      a1.allocId = a0.allocId ∧
      a1.alignLog2 = a0.alignLog2 ∧
      a1.mutability = a0.mutability ∧
      a1.live = a0.live ∧
      a1.bytes.length = a0.bytes.length ∧
      ∀ off, ¬ InFootprint mutPtr mutLen aid off →
        a1.bytes[off]? = a0.bytes[off]?
    | _, _ => False

/-- Unified three-way outcome-preserving refinement between an Anneal MIR machine `m`
    and an Aeneas pure functional model `aeneasFn : α → Result β`.
    - On all `SafetyPre a ∧ R_in a q` inputs (including panicking inputs for safe-API leaves!),
      the Rust machine MUST be `WellFormed` (zero UB).
    - When `aeneasFn a = .ok b`: the machine terminates without unwinding or aborting, and every
      normal return `o` refines `b` via `R_out a b q o`.
    - When `aeneasFn a = .div`: the machine never unwinds, aborts, or returns a spurious value.
    - When `aeneasFn a = .fail _`: the machine never returns a spurious normal value (catching
      missing bounds/assertion checks in unsafe leaves). -/
def AnnealRefinesAeneas
    {α β : Type}
    (m : Machine)
    (aeneasFn : α → Result β)
    (SafetyPre : α → Prop)
    (R_in : α → Query → Prop)
    (R_out : α → β → Query → Out → Prop) : Prop :=
  ∀ a q, SafetyPre a → R_in a q →
    WellFormed m q ∧
    match aeneasFn a with
    | .ok b =>
        ¬ Diverges m q ∧
        (∀ cm, ¬ Behavior m q (.unwound cm)) ∧
        (∀ cm, ¬ Behavior m q (.aborted cm)) ∧
        (∀ o, Behavior m q (.returned o) → R_out a b q o)
    | .div =>
        (∀ cm, ¬ Behavior m q (.unwound cm)) ∧
        (∀ cm, ¬ Behavior m q (.aborted cm)) ∧
        (∀ o, ¬ Behavior m q (.returned o))
    | .fail _ =>
        ∀ o, ¬ Behavior m q (.returned o)

/-- Partial-correctness refinement (drops `¬ Diverges` on `.ok b`, matching `WP.dspec`). -/
def AnnealRefinesAeneasPartial
    {α β : Type}
    (m : Machine)
    (aeneasFn : α → Result β)
    (SafetyPre : α → Prop)
    (R_in : α → Query → Prop)
    (R_out : α → β → Query → Out → Prop) : Prop :=
  ∀ a q, SafetyPre a → R_in a q →
    WellFormed m q ∧
    match aeneasFn a with
    | .ok b =>
        (∀ cm, ¬ Behavior m q (.unwound cm)) ∧
        (∀ cm, ¬ Behavior m q (.aborted cm)) ∧
        (∀ o, Behavior m q (.returned o) → R_out a b q o)
    | .div =>
        (∀ cm, ¬ Behavior m q (.unwound cm)) ∧
        (∀ cm, ¬ Behavior m q (.aborted cm)) ∧
        (∀ o, ¬ Behavior m q (.returned o))
    | .fail _ =>
        ∀ o, ¬ Behavior m q (.returned o)

theorem refines_implies_partial
    {α β : Type} {m : Machine} {aeneasFn : α → Result β}
    {SafetyPre : α → Prop} {R_in : α → Query → Prop} {R_out : α → β → Query → Out → Prop}
    (h : AnnealRefinesAeneas m aeneasFn SafetyPre R_in R_out) :
    AnnealRefinesAeneasPartial m aeneasFn SafetyPre R_in R_out := by
  intro a q hpre hin
  have h1 := h a q hpre hin
  refine ⟨h1.1, ?_⟩
  cases hres : aeneasFn a with
  | ok b =>
    have h2 := h1.2
    rw [hres] at h2
    exact ⟨h2.2.1, h2.2.2.1, h2.2.2.2⟩
  | div =>
    have h2 := h1.2
    rw [hres] at h2
    exact h2
  | fail e =>
    have h2 := h1.2
    rw [hres] at h2
    exact h2

/-- **Total-Correctness Transfer Theorem (`WP.spec` → Anneal):**
    If an Anneal leaf refines `aeneasFn` and an Aeneas caller proves `WP.spec (aeneasFn a) P`,
    then the Rust MIR execution is UB-free, terminates, never unwinds or aborts, and every
    normal return refines some `b` satisfying `P b`. -/
theorem transfer_wp_spec
    {α β : Type} {m : Machine} {aeneasFn : α → Result β}
    {SafetyPre : α → Prop} {R_in : α → Query → Prop} {R_out : α → β → Query → Out → Prop}
    {P : β → Prop} {a : α} {q : Query}
    (href : AnnealRefinesAeneas m aeneasFn SafetyPre R_in R_out)
    (hpre : SafetyPre a) (hin : R_in a q)
    (hspec : WP.spec (aeneasFn a) P) :
    WellFormed m q ∧
    ¬ Diverges m q ∧
    (∀ cm, ¬ Behavior m q (.unwound cm)) ∧
    (∀ cm, ¬ Behavior m q (.aborted cm)) ∧
    (∀ o, Behavior m q (.returned o) → ∃ b, P b ∧ R_out a b q o) := by
  have h1 := href a q hpre hin
  cases hres : aeneasFn a with
  | ok b =>
    rw [hres] at hspec
    have h2 := h1.2
    rw [hres] at h2
    refine ⟨h1.1, h2.1, h2.2.1, h2.2.2.1, fun o ho => ⟨b, hspec, h2.2.2.2 o ho⟩⟩
  | fail e =>
    rw [hres] at hspec
    exact False.elim hspec
  | div =>
    rw [hres] at hspec
    exact False.elim hspec

/-- **Partial-Correctness Transfer Theorem (`WP.dspec` → Anneal):**
    Under `AnnealRefinesAeneasPartial` and `WP.dspec (aeneasFn a) P`, the Rust MIR execution
    is UB-free, never unwinds or aborts, and if it returns `o`, it refines some `b` satisfying `P b`. -/
theorem transfer_wp_dspec
    {α β : Type} {m : Machine} {aeneasFn : α → Result β}
    {SafetyPre : α → Prop} {R_in : α → Query → Prop} {R_out : α → β → Query → Out → Prop}
    {P : β → Prop} {a : α} {q : Query}
    (href : AnnealRefinesAeneasPartial m aeneasFn SafetyPre R_in R_out)
    (hpre : SafetyPre a) (hin : R_in a q)
    (hdspec : WP.dspec (aeneasFn a) P) :
    WellFormed m q ∧
    (∀ cm, ¬ Behavior m q (.unwound cm)) ∧
    (∀ cm, ¬ Behavior m q (.aborted cm)) ∧
    (∀ o, Behavior m q (.returned o) → ∃ b, P b ∧ R_out a b q o) := by
  have h1 := href a q hpre hin
  cases hres : aeneasFn a with
  | ok b =>
    rw [hres] at hdspec
    have h2 := h1.2
    rw [hres] at h2
    refine ⟨h1.1, h2.1, h2.2.1, fun o ho => ⟨b, hdspec, h2.2.2 o ho⟩⟩
  | div =>
    have h2 := h1.2
    rw [hres] at h2
    refine ⟨h1.1, h2.1, h2.2.1, fun o ho => False.elim (h2.2.2 o ho)⟩
  | fail e =>
    rw [hres] at hdspec
    exact False.elim hdspec

/-! ## 4. Concrete Leaf 1: Little-Endian `read_u64` (Modeled on `jxl-proofs` `FunsExternal.lean`) -/

def packLe64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : BitVec 64 :=
  BitVec.ofNat 64
    (b0.toNat + b1.toNat * 2^8 + b2.toNat * 2^16 + b3.toNat * 2^24 +
     b4.toNat * 2^32 + b5.toNat * 2^40 + b6.toNat * 2^48 + b7.toNat * 2^56)

/-- Aeneas constructive model in `FunsExternal.lean` (cf. `AeneasVerif/jxl-proofs`). -/
def aeneas_read_u64 (s : ByteSlice) : Result U64 :=
  match s.val with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: _ =>
    .ok ⟨packLe64 (UInt8.ofBitVec b0.bv) (UInt8.ofBitVec b1.bv)
                  (UInt8.ofBitVec b2.bv) (UInt8.ofBitVec b3.bv)
                  (UInt8.ofBitVec b4.bv) (UInt8.ofBitVec b5.bv)
                  (UInt8.ofBitVec b6.bv) (UInt8.ofBitVec b7.bv)⟩
  | _ => .fail .panic

/-- Aeneas `@[step]` Hoare triple consumed by safe callers (e.g., `BitReader::refill`). -/
theorem aeneas_read_u64_spec (s : ByteSlice) (hlen : s.val.length ≥ 8) :
    WP.spec (aeneas_read_u64 s) (fun _ => True) := by
  cases h : s.val with
  | nil => simp [h] at hlen
  | cons b0 t0 =>
    cases t0 with
    | nil => simp [h] at hlen
    | cons b1 t1 =>
      cases t1 with
      | nil => simp [h] at hlen
      | cons b2 t2 =>
        cases t2 with
        | nil => simp [h] at hlen
        | cons b3 t3 =>
          cases t3 with
          | nil => simp [h] at hlen
          | cons b4 t4 =>
            cases t4 with
            | nil => simp [h] at hlen
            | cons b5 t5 =>
              cases t5 with
              | nil => simp [h] at hlen
              | cons b6 t6 =>
                cases t6 with
                | nil => simp [h] at hlen
                | cons b7 t7 =>
                  simp [aeneas_read_u64, h, WP.spec]

/-- Miniature Anneal MIR machine for `read_u64(buf: &[u8]) -> u64`. -/
def mir_read_u64_eval (q : Query) : StepResult Unit TerminalOut :=
  match q.args with
  | [.slice ptr len] =>
    if len < 8 then
      .done (.unwound q.callerMem)
    else
      match readSliceBytes q.callerMem ptr 8 with
      | .error k => .fault k
      | .ok [b0, b1, b2, b3, b4, b5, b6, b7] =>
        .done (.returned ⟨.u64 (packLe64 b0 b1 b2 b3 b4 b5 b6 b7), q.callerMem⟩)
      | .ok _ => .fault .unsupported
  | _ => .fault .unsupported

def mir_read_u64 : Machine := singleStepMachine mir_read_u64_eval

private theorem drop_take_8_eq {α : Type} (xs : List α) (off : Nat) (h : off + 8 ≤ xs.length) :
    (xs.drop off).take 8 =
      [xs[off]'(by omega), xs[off + 1]'(by omega), xs[off + 2]'(by omega),
       xs[off + 3]'(by omega), xs[off + 4]'(by omega), xs[off + 5]'(by omega),
       xs[off + 6]'(by omega), xs[off + 7]'(by omega)] := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop]
    have hi : i < 8 := by simpa using h2
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · omega

/-- Helper: reading 8 bytes from a slice satisfying `MemRefinesByteSlice` with `len ≥ 8`
    always succeeds with the exact first 8 `UInt8` bytes of `s.val`. -/
private theorem readSliceBytes_8_of_refines
    (ptr : PtrVal) (len : Nat) (mem : CallerMemory) (s : ByteSlice)
    (href : MemRefinesByteSlice ptr len mem s)
    (b0 b1 b2 b3 b4 b5 b6 b7 : U8) (rest : List U8)
    (hs : s.val = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) :
    readSliceBytes mem ptr 8 =
      .ok [UInt8.ofBitVec b0.bv, UInt8.ofBitVec b1.bv, UInt8.ofBitVec b2.bv,
           UInt8.ofBitVec b3.bv, UInt8.ofBitVec b4.bv, UInt8.ofBitVec b5.bv,
           UInt8.ofBitVec b6.bv, UInt8.ofBitVec b7.bv] := by
  rcases href with ⟨hlen, _, hmem⟩
  have hlen8 : len ≥ 8 := by rw [hlen, hs]; simp
  have hne0 : len ≠ 0 := by omega
  simp only [hne0, ↓reduceIte] at hmem
  rcases hmem with ⟨aid, a, hpid, hfind, hlive, hbound, hbytes⟩
  have hbound8 : ptr.offsetBytes + 8 ≤ a.bytes.length := by omega
  have hget : ∀ (k : Nat) (hk : k < 8),
      ∃ prov, a.bytes[ptr.offsetBytes + k]'(by omega) =
        .init (UInt8.ofBitVec (s.val[k]'(by rw [hs]; simp; omega)).bv) prov := by
    intro k hk
    rcases hbytes k (by rw [hs]; simp; omega) with ⟨prov, hp⟩
    rw [List.getElem?_eq_getElem (by omega)] at hp
    exact ⟨prov, Option.some.inj hp⟩
  rcases hget 0 (by omega) with ⟨p0, hg0⟩
  rcases hget 1 (by omega) with ⟨p1, hg1⟩
  rcases hget 2 (by omega) with ⟨p2, hg2⟩
  rcases hget 3 (by omega) with ⟨p3, hg3⟩
  rcases hget 4 (by omega) with ⟨p4, hg4⟩
  rcases hget 5 (by omega) with ⟨p5, hg5⟩
  rcases hget 6 (by omega) with ⟨p6, hg6⟩
  rcases hget 7 (by omega) with ⟨p7, hg7⟩
  simp only [hs, List.getElem_cons_zero, List.getElem_cons_succ] at hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7
  unfold readSliceBytes
  have h8ne0 : (8 == 0) = false := rfl
  simp only [h8ne0, Bool.false_eq_true, ↓reduceIte, hpid, hfind, hlive, Bool.not_true,
    Bool.false_or, hbound8, decide_true]
  rw [drop_take_8_eq a.bytes ptr.offsetBytes hbound8]
  simp only [Nat.add_zero] at hg0
  rw [hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7]
  rfl

/-- **End-to-End Refinement Theorem for `read_u64` (including BOTH `len ≥ 8` AND `len < 8` panics!):** -/
theorem read_u64_refines :
    AnnealRefinesAeneas
      mir_read_u64
      aeneas_read_u64
      (fun _ => True) -- Safe Rust API: UB-free on ALL valid slices, even `len < 8`!
      (fun s q => ∃ ptr len, q.args = [.slice ptr len] ∧ MemRefinesByteSlice ptr len q.callerMem s)
      (fun _ b q o => ValRefinesU64 o.ret b ∧ o.callerMem = q.callerMem) := by
  intro s q _ ⟨ptr, len, hargs, href⟩
  have hlen := href.1
  cases hs : s.val with
  | nil =>
    have hlt : len < 8 := by rw [hlen, hs]; simp
    have heval : mir_read_u64_eval q = .done (.unwound q.callerMem) := by
      simp [mir_read_u64_eval, hargs, hlt]
    have hss := singleStep_done_wf mir_read_u64_eval q (.unwound q.callerMem) heval
    refine ⟨hss.1, ?_⟩
    simp only [aeneas_read_u64, hs]
    intro o ho
    have := hss.2.2 (.returned o) ho
    cases this
  | cons b0 t0 =>
    cases t0 with
    | nil =>
      have hlt : len < 8 := by rw [hlen, hs]; simp
      have heval : mir_read_u64_eval q = .done (.unwound q.callerMem) := by
        simp [mir_read_u64_eval, hargs, hlt]
      have hss := singleStep_done_wf mir_read_u64_eval q (.unwound q.callerMem) heval
      refine ⟨hss.1, ?_⟩; simp only [aeneas_read_u64, hs]; intro o ho; cases hss.2.2 _ ho
    | cons b1 t1 =>
      cases t1 with
      | nil =>
        have hlt : len < 8 := by rw [hlen, hs]; simp
        have heval : mir_read_u64_eval q = .done (.unwound q.callerMem) := by
          simp [mir_read_u64_eval, hargs, hlt]
        have hss := singleStep_done_wf mir_read_u64_eval q (.unwound q.callerMem) heval
        refine ⟨hss.1, ?_⟩; simp only [aeneas_read_u64, hs]; intro o ho; cases hss.2.2 _ ho
      | cons b2 t2 =>
        cases t2 with
        | nil =>
          have hlt : len < 8 := by rw [hlen, hs]; simp
          have heval : mir_read_u64_eval q = .done (.unwound q.callerMem) := by
            simp [mir_read_u64_eval, hargs, hlt]
          have hss := singleStep_done_wf mir_read_u64_eval q (.unwound q.callerMem) heval
          refine ⟨hss.1, ?_⟩; simp only [aeneas_read_u64, hs]; intro o ho; cases hss.2.2 _ ho
        | cons b3 t3 =>
          cases t3 with
          | nil =>
            have hlt : len < 8 := by rw [hlen, hs]; simp
            have heval : mir_read_u64_eval q = .done (.unwound q.callerMem) := by
              simp [mir_read_u64_eval, hargs, hlt]
            have hss := singleStep_done_wf mir_read_u64_eval q (.unwound q.callerMem) heval
            refine ⟨hss.1, ?_⟩; simp only [aeneas_read_u64, hs]; intro o ho; cases hss.2.2 _ ho
          | cons b4 t4 =>
            cases t4 with
            | nil =>
              have hlt : len < 8 := by rw [hlen, hs]; simp
              have heval : mir_read_u64_eval q = .done (.unwound q.callerMem) := by
                simp [mir_read_u64_eval, hargs, hlt]
              have hss := singleStep_done_wf mir_read_u64_eval q (.unwound q.callerMem) heval
              refine ⟨hss.1, ?_⟩; simp only [aeneas_read_u64, hs]; intro o ho; cases hss.2.2 _ ho
            | cons b5 t5 =>
              cases t5 with
              | nil =>
                have hlt : len < 8 := by rw [hlen, hs]; simp
                have heval : mir_read_u64_eval q = .done (.unwound q.callerMem) := by
                  simp [mir_read_u64_eval, hargs, hlt]
                have hss := singleStep_done_wf mir_read_u64_eval q (.unwound q.callerMem) heval
                refine ⟨hss.1, ?_⟩; simp only [aeneas_read_u64, hs]; intro o ho; cases hss.2.2 _ ho
              | cons b6 t6 =>
                cases t6 with
                | nil =>
                  have hlt : len < 8 := by rw [hlen, hs]; simp
                  have heval : mir_read_u64_eval q = .done (.unwound q.callerMem) := by
                    simp [mir_read_u64_eval, hargs, hlt]
                  have hss := singleStep_done_wf mir_read_u64_eval q (.unwound q.callerMem) heval
                  refine ⟨hss.1, ?_⟩; simp only [aeneas_read_u64, hs]; intro o ho; cases hss.2.2 _ ho
                | cons b7 t7 =>
                  have hge : ¬ (len < 8) := by rw [hlen, hs]; simp
                  have hread := readSliceBytes_8_of_refines ptr len q.callerMem s href
                    b0 b1 b2 b3 b4 b5 b6 b7 t7 hs
                  let outVal := packLe64 (UInt8.ofBitVec b0.bv) (UInt8.ofBitVec b1.bv)
                    (UInt8.ofBitVec b2.bv) (UInt8.ofBitVec b3.bv)
                    (UInt8.ofBitVec b4.bv) (UInt8.ofBitVec b5.bv)
                    (UInt8.ofBitVec b6.bv) (UInt8.ofBitVec b7.bv)
                  have heval : mir_read_u64_eval q = .done (.returned ⟨.u64 outVal, q.callerMem⟩) := by
                    simp [mir_read_u64_eval, hargs, hge, hread, outVal]
                  have hss := singleStep_done_wf mir_read_u64_eval q (.returned ⟨.u64 outVal, q.callerMem⟩) heval
                  refine ⟨hss.1, ?_⟩
                  simp only [aeneas_read_u64, hs]
                  refine ⟨hss.2.1, ?_, ?_, ?_⟩
                  · intro cm hcm; cases hss.2.2 _ hcm
                  · intro cm hcm; cases hss.2.2 _ hcm
                  · intro o ho
                    have heq := hss.2.2 _ ho
                    injection heq with ho'
                    subst ho'
                    exact ⟨rfl, rfl⟩

/-- **Composed Safe-Caller + Unsafe-Leaf Theorem:**
    Combines Aeneas's caller proof (`aeneas_read_u64_spec` for `s.val.length ≥ 8`) with
    Anneal's leaf refinement (`read_u64_refines`) via `transfer_wp_spec`. -/
theorem bitreader_refill_leaf_composed
    (s : ByteSlice) (q : Query) (ptr : PtrVal) (len : Nat)
    (hlen : s.val.length ≥ 8)
    (hargs : q.args = [.slice ptr len])
    (href : MemRefinesByteSlice ptr len q.callerMem s) :
    WellFormed mir_read_u64 q ∧
    ¬ Diverges mir_read_u64 q ∧
    (∀ cm, ¬ Behavior mir_read_u64 q (.unwound cm)) ∧
    (∀ cm, ¬ Behavior mir_read_u64 q (.aborted cm)) ∧
    (∀ o, Behavior mir_read_u64 q (.returned o) →
      ∃ b, ValRefinesU64 o.ret b ∧ o.callerMem = q.callerMem) := by
  have ht := transfer_wp_spec read_u64_refines trivial ⟨ptr, len, hargs, href⟩
    (aeneas_read_u64_spec s hlen)
  exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1,
    fun o ho => let ⟨b, _, hrout⟩ := ht.2.2.2.2 o ho; ⟨b, hrout⟩⟩

/-! ## 5. Concrete Leaf 2: Mutable Borrow Backward-Function / Prophecy Equivalence (`split_at_mut`) -/

/-- Aeneas pure model of `split_at_mut` on byte slices (cf. `Aeneas/Std/Slice.lean:740-755`). -/
def aeneas_split_at_mut (s : ByteSlice) (mid : Nat) :
    Result ((ByteSlice × ByteSlice) × ((ByteSlice × ByteSlice) → ByteSlice)) :=
  if h : mid ≤ s.val.length then
    let s0 : ByteSlice := ⟨s.val.take mid, by have := s.bound; simp; omega⟩
    let s1 : ByteSlice := ⟨s.val.drop mid, by have := s.bound; simp; omega⟩
    let back (p : ByteSlice × ByteSlice) : ByteSlice :=
      if hlen : p.1.val.length = mid ∧ p.2.val.length = s.val.length - mid then
        ⟨p.1.val ++ p.2.val, by have := s.bound; simp; omega⟩
      else s
    .ok ((s0, s1), back)
  else
    .fail .panic

/-- **Prophecy / Backward-Function Soundness Theorem for `split_at_mut`:**
    Given a live mutable byte slice `(ptr, len)` refining `s` and `mid ≤ len`, the two
    sub-slice pointers `p0 := ptr` (length `mid`) and `p1 := ⟨ptr.allocId, ptr.offsetBytes + mid⟩`
    (length `len - mid`) have:
    1. Pairwise disjoint footprints (`DisjointFootprints p0 mid p1 (len - mid)`);
    2. For ANY future memory `memAfter` in which a safe caller has mutated the two disjoint
       sub-slices to arbitrary valid byte slices `(s0', s1')` of matching lengths `(mid, len - mid)`
       (preserving the rest of the parent slice allocation), the parent slice `(ptr, len)` in
       `memAfter` refines **`back (s0', s1')`**! -/
theorem split_at_mut_prophecy_sound
    (ptr : PtrVal) (len mid : Nat) (mem0 memAfter : CallerMemory)
    (s s0' s1' : ByteSlice)
    (hmid : mid ≤ s.val.length)
    (hinit : MemRefinesByteSliceMut ptr len mem0 s)
    (hs0Len : s0'.val.length = mid)
    (hs1Len : s1'.val.length = len - mid)
    -- Caller mutated `p0` to `s0'` and `p1` to `s1'` in the same parent allocation:
    (hsub0 : MemRefinesByteSliceMut ptr mid memAfter s0')
    (hsub1 : MemRefinesByteSliceMut ⟨ptr.allocId, ptr.offsetBytes + mid⟩ (len - mid) memAfter s1')
    (hparentAlive : len > 0 → ∃ aid a,
      ptr.allocId = some aid ∧ findAlloc aid memAfter.allocations = some a ∧
      a.live = true ∧ a.mutability = .mut ∧ ptr.offsetBytes + len ≤ a.bytes.length) :
    DisjointFootprints ptr mid ⟨ptr.allocId, ptr.offsetBytes + mid⟩ (len - mid) ∧
    match aeneas_split_at_mut s mid with
    | .ok (_, back) => MemRefinesByteSliceMut ptr len memAfter (back (s0', s1'))
    | _ => False := by
  have hlen : len = s.val.length := hinit.1.1
  have hbound : len ≤ isizeMax64 := hinit.1.2.1
  refine ⟨?_, ?_⟩
  · intro aid off ⟨⟨_, _, _, hlt⟩, ⟨_, _, hge, _⟩⟩
    dsimp only at hge
    omega
  · simp only [aeneas_split_at_mut, hmid, ↓reduceDIte]
    have hbackLen : s0'.val.length = mid ∧ s1'.val.length = s.val.length - mid := by
      exact ⟨hs0Len, by rw [← hlen]; exact hs1Len⟩
    split
    · refine ⟨⟨by simp [hs0Len, hs1Len]; omega, hbound, ?_⟩, ?_⟩
      · split
        · next h0 =>
          have hnz := hinit.1.2.2
          simp only [h0, ↓reduceIte] at hnz
          exact hnz
        · next hne =>
          have hpos : len > 0 := by omega
          rcases hparentAlive hpos with ⟨aid, a, hpid, hfind, hlive, hmut, hlenA⟩
          refine ⟨aid, a, hpid, hfind, hlive, hlenA, ?_⟩
          intro i hi
          dsimp only at hi
          rw [List.length_append] at hi
          by_cases hlt : i < mid
          · have hmidPos : mid ≠ 0 := by omega
            have hm0 := hsub0.1.2.2
            simp only [hmidPos, ↓reduceIte] at hm0
            rcases hm0 with ⟨aid0, a0, hpid0, hfind0, _, _, hbytes0⟩
            rw [hpid] at hpid0
            injection hpid0 with haid
            subst haid
            rw [hfind] at hfind0
            injection hfind0 with ha
            subst ha
            have hi0 : i < s0'.val.length := by omega
            rcases hbytes0 i hi0 with ⟨prov, hp⟩
            refine ⟨prov, ?_⟩
            rw [hp]
            dsimp only
            rw [List.getElem_append_left hi0]
          · have hremPos : len - mid ≠ 0 := by omega
            have hm1 := hsub1.1.2.2
            simp only [hremPos, ↓reduceIte] at hm1
            rcases hm1 with ⟨aid1, a1, hpid1, hfind1, _, _, hbytes1⟩
            rw [hpid] at hpid1
            injection hpid1 with haid
            subst haid
            rw [hfind] at hfind1
            injection hfind1 with ha
            subst ha
            have hi1 : i - mid < s1'.val.length := by omega
            rcases hbytes1 (i - mid) hi1 with ⟨prov, hp⟩
            refine ⟨prov, ?_⟩
            have hoff : ptr.offsetBytes + mid + (i - mid) = ptr.offsetBytes + i := by omega
            rw [hoff] at hp
            rw [hp]
            dsimp only
            have hge0 : s0'.val.length ≤ i := by omega
            rw [List.getElem_append_right hge0]
            simp only [hs0Len]
      · intro hpos
        rcases hparentAlive hpos with ⟨aid, a, hpid, hfind, _, hmut, _⟩
        exact ⟨aid, a, hpid, hfind, hmut⟩
    · next hnot => exact False.elim (hnot hbackLen)

/-! ## 6. Negative Counterexamples (Refuting Missing Frame / Missing Disjointness) -/

/-- Counterexample 1: Mutating even 1 byte outside `(mutPtr, mutLen)` refutes `FramePreserved`. -/
theorem frame_violation_refuted :
    let a0 : Allocation := ⟨1, 0, .mut, [.init 0 none, .init 42 none], true⟩
    let a1 : Allocation := ⟨1, 0, .mut, [.init 0 none, .init 99 none], true⟩
    ¬ FramePreserved ⟨some 1, 0⟩ 1 ⟨[a0]⟩ ⟨[a1]⟩ := by
  intro a0 a1 hf
  have h1 := hf 1
  simp only [a0, a1, findAlloc, beq_self_eq_true, ↓reduceIte] at h1
  have hbyte := h1.2.2.2.2.2 1 (by
    intro ⟨_, _, _, hlt⟩
    dsimp only at hlt
    omega)
  simp at hbyte

/-- Counterexample 2: Overlapping `dst` and `src` fail `DisjointFootprints`. -/
theorem overlapping_slices_fail_disjointness :
    ¬ DisjointFootprints ⟨some 1, 0⟩ 1 ⟨some 1, 0⟩ 1 := by
  intro hd
  exact hd 1 0 ⟨⟨by decide, rfl, Nat.le_refl 0, by decide⟩,
                ⟨by decide, rfl, Nat.le_refl 0, by decide⟩⟩

end Bridge

end ToyAnnealAeneasBridge

#print axioms ToyAnnealAeneasBridge.Bridge.transfer_wp_spec
#print axioms ToyAnnealAeneasBridge.Bridge.transfer_wp_dspec
#print axioms ToyAnnealAeneasBridge.Bridge.read_u64_refines
#print axioms ToyAnnealAeneasBridge.Bridge.bitreader_refill_leaf_composed
#print axioms ToyAnnealAeneasBridge.Bridge.split_at_mut_prophecy_sound
#print axioms ToyAnnealAeneasBridge.Bridge.frame_violation_refuted
#print axioms ToyAnnealAeneasBridge.Bridge.overlapping_slices_fail_disjointness
