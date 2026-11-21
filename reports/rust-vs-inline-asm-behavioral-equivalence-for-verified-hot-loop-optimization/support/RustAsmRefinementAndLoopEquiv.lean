prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic

/-!
Pass-1 Lean 4 (`v4.34.1`) mechanization of cross-level Rust MIR <-> inline/naked
assembly relational contracts, pointer/padding invariants, software pipelining
(Tristan & Leroy POPL 2010), prolog/unroll/epilog loop decomposition, SWAR
borrow-isolation vs borrow-corruption witnesses, and opt-in 2-safety constant-time
preservation.

Conforms strictly to Anneal Pass-1 syntax rules: `prelude` + locked `Init.*`
only; zero `sorry`, zero custom `axiom`, zero `partial`/`unsafe`/`._unsafe_rec`,
zero `omega`/`bv_decide`/`native_decide`/`Lean.ofReduceBool`.
-/

namespace RustAsmEquiv

-- ============================================================================
-- 1. Cross-Level MIR <-> ISA Relational Contracts & Panic-Refinement Loopholes
-- ============================================================================

/-- Observable outcomes of a Rust MIR reference function. -/
inductive MirOut (V M : Type) where
  | returned (v : V) (mem : M)
  | panicked (mem : M)
  | ub
  | diverges

/-- Observable outcomes of an inline/naked ISA routine. -/
inductive IsaOut (V M : Type) where
  | halted (v : V) (mem : M)
  | panicked (mem : M)
  | trap
  | diverges

/-- Total panic-exact cross-level equivalence: on every valid input `q`,
    neither side faults/traps and normal returns, panic caller memory, and
    divergence match identically. -/
def TotalMirAsmEquiv {Q V M : Type}
    (ref : Q → MirOut V M) (asm : Q → IsaOut V M) : Prop :=
  ∀ q,
    ref q ≠ MirOut.ub ∧
    asm q ≠ IsaOut.trap ∧
    (∀ v m, asm q = IsaOut.halted v m ↔ ref q = MirOut.returned v m) ∧
    (∀ m, asm q = IsaOut.panicked m ↔ ref q = MirOut.panicked m) ∧
    (asm q = IsaOut.diverges ↔ ref q = MirOut.diverges)

/-- Precondition-gated cross-level equivalence: on inputs satisfying `Pre q`,
    `asm` never traps and matches `ref` on returns, panics, and divergence.
    Inputs outside `Pre` MUST be handled by a checked Rust wrapper before
    entering `asm!`. -/
def PrecondMirAsmEquiv {Q V M : Type}
    (Pre : Q → Prop) (ref : Q → MirOut V M) (asm : Q → IsaOut V M) : Prop :=
  ∀ q, Pre q →
    ref q ≠ MirOut.ub ∧
    asm q ≠ IsaOut.trap ∧
    (∀ v m, asm q = IsaOut.halted v m ↔ ref q = MirOut.returned v m) ∧
    (∀ m, asm q = IsaOut.panicked m ↔ ref q = MirOut.panicked m) ∧
    (asm q = IsaOut.diverges ↔ ref q = MirOut.diverges)

/-- NAIVE (UNSOUND) weak panic-refinement: constrains `asm` ONLY when `ref`
    returns normally, silently permitting `asm` to trap/UB or corrupt memory
    when `ref` panics on out-of-bounds or overflowing inputs. -/
def NaiveWeakPanicRefines {Q V M : Type}
    (ref : Q → MirOut V M) (asm : Q → IsaOut V M) : Prop :=
  ∀ q v m, ref q = MirOut.returned v m → asm q = IsaOut.halted v m

def refCheckedSliceHead (len : Nat) : MirOut Nat Nat :=
  match len with
  | 0 => MirOut.panicked 7
  | _ + 1 => MirOut.returned 42 7

def badAsmUncheckedLoad (len : Nat) : IsaOut Nat Nat :=
  match len with
  | 0 => IsaOut.trap
  | _ + 1 => IsaOut.halted 42 7

/-- Refutation 1: Naive panic-refinement silently accepts turning a safe Rust
    bounds panic (`len = 0`) into an unchecked hardware trap / UB, whereas
    `TotalMirAsmEquiv` rejects it. -/
theorem naive_panic_refinement_admits_panic_to_ub :
    NaiveWeakPanicRefines refCheckedSliceHead badAsmUncheckedLoad ∧
    ¬ TotalMirAsmEquiv refCheckedSliceHead badAsmUncheckedLoad :=
  And.intro
    (fun q v m h =>
      match q, h with
      | 0, h => by cases h
      | _ + 1, h => by cases h; rfl)
    (fun hTot => (hTot 0).2.1 rfl)

/-- Checked wrapper around a precondition-gated `asm!` kernel: runs `guard q`;
    if true dispatches to `asm`, else falls back to the safe reference `ref`
    (embedded in `IsaOut` via `embedSafe`). -/
def embedSafe {V M : Type} (o : MirOut V M) : IsaOut V M :=
  match o with
  | MirOut.returned v m => IsaOut.halted v m
  | MirOut.panicked m => IsaOut.panicked m
  | MirOut.ub => IsaOut.trap
  | MirOut.diverges => IsaOut.diverges

def checkedDispatch {Q V M : Type}
    (guard : Q → Bool) (ref : Q → MirOut V M) (asm : Q → IsaOut V M)
    (q : Q) : IsaOut V M :=
  match guard q with
  | true => asm q
  | false => embedSafe (ref q)

/-- Theorem 1 (Safe-Wrapper Lifting): Wrapping a `PrecondMirAsmEquiv` assembly
    fast path behind a runtime check `guard` satisfying `guard q = true → Pre q`
    (with safe fallback `ref` when `guard q = false`) recovers full
    `TotalMirAsmEquiv` for the exported Rust API. -/
theorem checked_wrapper_recovers_total_equiv {Q V M : Type}
    (Pre : Q → Prop) (guard : Q → Bool)
    (ref : Q → MirOut V M) (asm : Q → IsaOut V M)
    (hRefSafe : ∀ q, ref q ≠ MirOut.ub)
    (hGuard : ∀ q, guard q = true → Pre q)
    (hAsm : PrecondMirAsmEquiv Pre ref asm) :
    TotalMirAsmEquiv ref (checkedDispatch guard ref asm) := by
  intro q
  dsimp [checkedDispatch]
  cases hg : guard q with
  | true =>
    exact hAsm q (hGuard q hg)
  | false =>
    have hNoUb := hRefSafe q
    cases hr : ref q with
    | returned v0 m0 =>
      dsimp [embedSafe]
      exact And.intro (fun h => by cases h)
        (And.intro (fun h => by cases h)
          (And.intro (fun v m => Iff.intro (fun h => by cases h; rfl) (fun h => by cases h; rfl))
            (And.intro (fun m => Iff.intro (fun h => by cases h) (fun h => by cases h))
              (Iff.intro (fun h => by cases h) (fun h => by cases h)))))
    | panicked m0 =>
      dsimp [embedSafe]
      exact And.intro (fun h => by cases h)
        (And.intro (fun h => by cases h)
          (And.intro (fun v m => Iff.intro (fun h => by cases h) (fun h => by cases h))
            (And.intro (fun m => Iff.intro (fun h => by cases h; rfl) (fun h => by cases h; rfl))
              (Iff.intro (fun h => by cases h) (fun h => by cases h)))))
    | ub =>
      exact False.elim (hNoUb hr)
    | diverges =>
      dsimp [embedSafe]
      exact And.intro (fun h => by cases h)
        (And.intro (fun h => by cases h)
          (And.intro (fun v m => Iff.intro (fun h => by cases h) (fun h => by cases h))
            (And.intro (fun m => Iff.intro (fun h => by cases h) (fun h => by cases h))
              (Iff.intro (fun _ => rfl) (fun _ => rfl)))))

-- ============================================================================
-- 2. Pointer Provenance, `MaybeUninit` Padding, and Output-Slice Invariant
-- ============================================================================

/-- Abstract byte matching MiniRust's `Init(u8, Option<Prov>) | Uninit`. -/
inductive AByte where
  | uninit
  | init (byte : Nat) (prov : Option Nat)

/-- Relational output-byte refinement: `asmByte` is valid for Rust consumers
    expecting `refByte` when:
    - if `refByte = .uninit` (struct padding / `MaybeUninit`), any concrete
      byte or `.uninit` in `asmByte` is safe (cannot make valid Rust UB);
    - if `refByte = .init b p`, `asmByte` MUST match BOTH value `b` and
      provenance `p` (never stripping pointer provenance or returning uninit!). -/
def OutputByteRefines (refByte asmByte : AByte) : Prop :=
  match refByte with
  | AByte.uninit => True
  | AByte.init b p => asmByte = AByte.init b p

/-- Concrete machine-level `MaybeUninit` over-read independence:
    if an `asm!` SIMD load reads both initialized prefix `initPrefix` and
    arbitrary concrete bytes `pad` from a `MaybeUninit` tail, writing initialized
    output bytes is sound iff the output is invariant across all pad bit patterns. -/
def PadIndependent {I P O : Type} (kernel : I → P → O) : Prop :=
  ∀ x p1 p2, kernel x p1 = kernel x p2

/-- Provenance-preserving subslice pointer: returning `&mut buf[k..]` requires
    preserving the caller's `allocId` and staying within `[0, bufLen]`. -/
structure DerivedPtr where
  allocId : Nat
  offset : Nat

def SubslicePtrSound (callerAlloc callerLen : Nat) (refPtr asmPtr : DerivedPtr) : Prop :=
  refPtr.allocId = callerAlloc ∧
  asmPtr.allocId = callerAlloc ∧
  asmPtr.offset = refPtr.offset ∧
  asmPtr.offset ≤ callerLen

theorem outputByteRefines_rejects_uninit_for_init :
    ¬ OutputByteRefines (AByte.init 99 none) AByte.uninit :=
  fun h => by cases h

theorem outputByteRefines_rejects_provenance_strip :
    ¬ OutputByteRefines (AByte.init 16 (some 7)) (AByte.init 16 none) :=
  fun h => by cases h

theorem outputByteRefines_allows_concrete_padding_write :
    OutputByteRefines AByte.uninit (AByte.init 0 none) :=
  True.intro

-- ============================================================================
-- 3. Software Pipelining Commutation Theorem (Tristan & Leroy, POPL 2010)
-- ============================================================================

/-- Bounded structural iteration via `Nat.rec` (Pass-1 compliant, no `._unsafe_rec`). -/
def iterN {α : Type} (f : α → α) (n : Nat) (x : α) : α :=
  @Nat.rec (fun _ => α) x (fun _ acc => f acc) n

theorem iterN_zero {α : Type} (f : α → α) (x : α) :
    iterN f 0 x = x := rfl

theorem iterN_succ {α : Type} (f : α → α) (n : Nat) (x : α) :
    iterN f (n + 1) x = f (iterN f n x) := rfl

theorem iterN_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iterN f (a + b) x = iterN f b (iterN f a x) := by
  induction b with
  | zero => rfl
  | succ k ih =>
    rw [Nat.add_succ]
    exact congrArg f ih

/-- Theorem 2 (Software Pipelining Algebraic Commutation, Tristan & Leroy POPL 2010):
    For any source loop step `B : S → S`, pipelined prologue `P : S → T`,
    overlapped kernel `K : T → T`, and drain epilogue `E : T → S`:
    if `E (P s) = iterN B mu s` and `E (K t) = iterN B delta (E t)` for all `s, t`,
    then executing prologue + `k` kernel iterations + epilogue equals `mu + k * delta`
    iterations of the scalar Rust reference loop `B`! -/
theorem software_pipelining_equiv {S T : Type}
    (B : S → S) (P : S → T) (K : T → T) (E : T → S)
    (mu delta : Nat)
    (h_pe : ∀ s, E (P s) = iterN B mu s)
    (h_ke : ∀ t, E (K t) = iterN B delta (E t)) :
    ∀ k s, E (iterN K k (P s)) = iterN B (mu + k * delta) s := by
  intro k
  induction k with
  | zero =>
    intro s
    have hmul : mu + 0 * delta = mu := by
      rw [Nat.zero_mul, Nat.add_zero]
    rw [hmul]
    exact h_pe s
  | succ n ih =>
    intro s
    rw [iterN_succ K n (P s)]
    rw [h_ke (iterN K n (P s))]
    rw [ih s]
    have hidx : mu + (n + 1) * delta = (mu + n * delta) + delta := by
      rw [Nat.succ_mul, Nat.add_assoc]
    rw [hidx]
    rw [iterN_add B (mu + n * delta) delta s]

/-- Concrete instantiation: 2-stage software-pipelined multiply-accumulate loop.
    Source body `B`: reads `arr i`, multiplies by `c`, adds to `acc`, increments `i`.
    Pipelined state `T`: carries prefetched `prod = arr i * c` one stage ahead!
    - Prologue `P`: computes `prod_0 = arr i * c` without updating `acc` yet.
    - Kernel `K`: folds previous `prod` into `acc` while simultaneously prefetching
      and multiplying `arr (i + 1) * c` for the next iteration.
    - Epilogue `E`: folds the final in-flight `prod` into `acc` and advances `i + 1`. -/
structure MacSrc where
  idx : Nat
  acc : Nat

structure MacPipe where
  idx : Nat
  acc : Nat
  inflightProd : Nat

def macBody (arr : Nat → Nat) (c : Nat) (s : MacSrc) : MacSrc :=
  MacSrc.mk (s.idx + 1) (s.acc + arr s.idx * c)

def macProlog (arr : Nat → Nat) (c : Nat) (s : MacSrc) : MacPipe :=
  MacPipe.mk s.idx s.acc (arr s.idx * c)

def macKernel (arr : Nat → Nat) (c : Nat) (t : MacPipe) : MacPipe :=
  MacPipe.mk (t.idx + 1) (t.acc + t.inflightProd) (arr (t.idx + 1) * c)

def macEpilog (t : MacPipe) : MacSrc :=
  MacSrc.mk (t.idx + 1) (t.acc + t.inflightProd)

theorem mac_software_pipelined_exact (arr : Nat → Nat) (c k : Nat) (s : MacSrc) :
    macEpilog (iterN (macKernel arr c) k (macProlog arr c s)) =
    iterN (macBody arr c) (1 + k * 1) s :=
  software_pipelining_equiv
    (macBody arr c) (macProlog arr c) (macKernel arr c) macEpilog 1 1
    (fun _ => rfl)
    (fun _ => rfl)
    k s

-- ============================================================================
-- 4. Alignment Prolog + Arbitrary U-Unrolled Aligned Kernel + Epilog Theorem
-- ============================================================================

/-- Theorem 3 (Prolog + U-Unrolled Main Loop + Epilog):
    Any optimization partitioning `n = p + k * U + e` steps into an alignment
    prolog `runProlog`, `k` iterations of a `U`-unrolled kernel `stepTile`, and
    a scalar/masked epilog `runEpilog` preserves relational invariant `R` linearly
    with zero quadratic path-product blowup. -/
theorem prolog_unroll_epilog_equiv {S T : Type}
    (R : S → T → Prop)
    (stepS : S → S)
    (runProlog : S → T → T) (stepTile : T → T) (runEpilog : T → T)
    (p U e : Nat)
    (hProlog : ∀ s t, R s t → R (iterN stepS p s) (runProlog s t))
    (hTile : ∀ s t, R s t → R (iterN stepS U s) (stepTile t))
    (hEpilog : ∀ s t, R s t → R (iterN stepS e s) (runEpilog t)) :
    ∀ k s t, R s t →
      R (iterN stepS (p + k * U + e) s)
        (runEpilog (iterN stepTile k (runProlog s t))) := by
  intro k s t h0
  rw [iterN_add stepS (p + k * U) e s]
  apply hEpilog
  rw [iterN_add stepS p (k * U) s]
  have hP := hProlog s t h0
  have hMain : ∀ m s1 t1, R s1 t1 → R (iterN stepS (m * U) s1) (iterN stepTile m t1) := by
    intro m
    induction m with
    | zero =>
      intro s1 t1 h1
      rw [Nat.zero_mul]
      exact h1
    | succ r ih =>
      intro s1 t1 h1
      rw [Nat.succ_mul]
      rw [iterN_add stepS (r * U) U s1]
      rw [iterN_succ stepTile r t1]
      exact hTile _ _ (ih s1 t1 h1)
  exact hMain k (iterN stepS p s) (runProlog s t) hP

-- ============================================================================
-- 5. SWAR Borrow-Corruption Witness (BurntSushi/memchr `\x0b\n` Counterexample)
-- ============================================================================

/-- 16-bit two-byte word `(b0, b1)` packed little-endian: `b0 + 256 * b1`. -/
def pack2 (b0 b1 : Nat) : Nat := b0 + 256 * b1

/-- Classic Mycroft SWAR zero-byte mask on 16-bit word:
    `((w - 0x0101) mod 65536) & (~w) & 0x8080`. -/
def swarMycroft16 (w : Nat) : Nat :=
  let sub := (w + 65536 - 0x0101) % 65536
  let notW := 65535 - (w % 65536)
  Nat.land (Nat.land sub notW) 0x8080

/-- Borrow-isolated SWAR zero-byte mask on 16-bit word:
    `(~(((w & 0x7F7F) + 0x7F7F) | w | 0x7F7F)) & 0x8080`. -/
def swarBorrowFree16 (w : Nat) : Nat :=
  let low := Nat.land w 0x7F7F
  let hasNonZeroLow := Nat.lor (low + 0x7F7F) w
  let notMask := 65535 - (Nat.lor hasNonZeroLow 0x7F7F % 65536)
  Nat.land notMask 0x8080

/-- Witness reproducing `BurntSushi/memchr` `regression_count_new_lines` (`\n\x0b`):
    searching for `\n` (`0x0A`) in `[0x0A, 0x0B]` XORs to `[0x00, 0x01]` (`0x0100`).
    Mycroft's formula sets BOTH high bits (`0x8080`, false positive in byte 1!),
    whereas borrow-free SWAR sets ONLY byte 0's high bit (`0x0080`). -/
theorem swar_memchr_borrow_corruption_witness :
    swarMycroft16 (pack2 (Nat.xor 0x0A 0x0A) (Nat.xor 0x0B 0x0A)) = 0x8080 ∧
    swarBorrowFree16 (pack2 (Nat.xor 0x0A 0x0A) (Nat.xor 0x0B 0x0A)) = 0x0080 :=
  And.intro rfl rfl

-- ============================================================================
-- 6. Opt-In 2-Safety Constant-Time Preservation Across MIR <-> ASM
-- ============================================================================

inductive CtObs where
  | branch (taken : Bool)
  | memLoad (addr : Nat)

def CtEquiv {Pub Sec : Type}
    (leak : Pub → Sec → List CtObs) : Prop :=
  ∀ p s1 s2, leak p s1 = leak p s2

def asmBranchFast (pub sec : Nat) : Nat × List CtObs :=
  match Nat.beq sec 0 with
  | true => (pub, [CtObs.branch true, CtObs.memLoad 0])
  | false => (pub + 1, [CtObs.branch false, CtObs.memLoad 8])

def asmCmovFast (pub sec : Nat) : Nat × List CtObs :=
  let bit := match Nat.beq sec 0 with | true => 0 | false => 1
  (pub + bit, [CtObs.memLoad 0])

/-- Functional outputs of `asmBranchFast` and `asmCmovFast` are identical for all
    `(pub, sec)`, yet `asmCmovFast` satisfies 2-safety constant-time while
    `asmBranchFast` violates it (McLean's Refinement Paradox across ASM optimization). -/
theorem functional_equiv_vs_ct_2safety :
    (∀ pub sec, (asmBranchFast pub sec).1 = (asmCmovFast pub sec).1) ∧
    CtEquiv (fun p s => (asmCmovFast p s).2) ∧
    ¬ CtEquiv (fun p s => (asmBranchFast p s).2) :=
  And.intro
    (fun pub sec => by
      dsimp [asmBranchFast, asmCmovFast]
      cases Nat.beq sec 0 with
      | true => rfl
      | false => rfl)
    (And.intro
      (fun _ _ _ => rfl)
      (fun hCt => by
        have h01 := hCt 0 0 1
        dsimp [asmBranchFast] at h01
        cases h01))

end RustAsmEquiv

#print axioms RustAsmEquiv.naive_panic_refinement_admits_panic_to_ub
#print axioms RustAsmEquiv.checked_wrapper_recovers_total_equiv
#print axioms RustAsmEquiv.outputByteRefines_rejects_uninit_for_init
#print axioms RustAsmEquiv.outputByteRefines_rejects_provenance_strip
#print axioms RustAsmEquiv.outputByteRefines_allows_concrete_padding_write
#print axioms RustAsmEquiv.software_pipelining_equiv
#print axioms RustAsmEquiv.mac_software_pipelined_exact
#print axioms RustAsmEquiv.prolog_unroll_epilog_equiv
#print axioms RustAsmEquiv.swar_memchr_borrow_corruption_witness
#print axioms RustAsmEquiv.functional_equiv_vs_ct_2safety
