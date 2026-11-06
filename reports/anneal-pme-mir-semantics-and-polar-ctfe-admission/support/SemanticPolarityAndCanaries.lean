-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Four-Quadrant Semantic Polarity Matrix & x86-64 Hardware Conformance Canaries

This standalone Lean 4 file mechanizes the semantic polarity matrix for Anneal's
trusted semantics (`trusted-core` @ `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`
and `mir-to-x86` @ `4f45f0a391a921ced9c9dc773b9a040dbc215d14`):

1. **The Four-Quadrant Semantic Polarity Matrix**:
   - **Quadrant 1** (`L_src.sem s ≤ spec` with an unverified compiler in the
     TCB, as in `trusted-core`): Omitting UB or demonic nondeterminism in
     `L_src.sem` is *fail-open* (unsound), whereas adding spurious UB is
     *fail-closed* (blocks verification).
   - **Quadrant 2** (`L_tgt.sem t ≤ spec_tgt` on the target ISA, as in
     `mir-to-x86`): Omitting a hardware fault/trap (`#DE`, `#GP`, `#UD`, or
     out-of-bounds stack-slot clobber) or under-approximating undefined
     register/flag bits is *fail-open* (unsound). Includes concrete divergence
     theorems against `Trusted/X86Semantics.lean`'s unbounded `Nat` `evalX86BinOp`.
   - **Quadrant 3** (`L_src` / `L_mid` on the RHS of `Compiles L_src L_tgt π_c s t`,
     i.e., `L_tgt.sem t ≤ π_c (L_src.sem s)`):
     - **Spurious-UB Codegen Exploit**: If `L_src.sem s` declares spurious UB
       (`defined = False`, the top element `⊤`) at a query, then `Compiles`
       holds for *every arbitrary broken target program `t`* (including `ud2`).
     - **Two-Sided Sandwich Theorem**: Enforcing *both*
       `Compiles L_src L_tgt π_c s t` and `L_src.sem s ≤ L_src.SpecOn pre post`
       forces `(L_src.sem s q).defined` to hold on `pre`, neutralizing the
       Quadrant-3 exploit and transporting `SpecOn` to `L_tgt`.
   - **Quadrant 4** (Negative-polarity premise language, `ConstMirMachine` /
     `MonoAdmitted` inside `initMirState` or `effectivePre`): Adding a spurious
     CTFE failure (`¬ ConstSucceeds`) shrinks the initial-state/precondition
     set to `⊥` and *vacuously verifies* runtime-UB programs (fail-open),
     whereas omitting a CTFE panic is *fail-closed* for caller verification.
2. **Positive & Negative x86-64 Hardware Conformance Canaries**:
   - Faithful `BitVec 64` model of sub-register writes (`w8`/`w16` merge vs.
     `w32` zero-extension), 64-bit modular ALU (`add`, `sub`, `imul`), shift
     count masking (`count &&& 63` / `count &&& 31`) and `RFlags` (`count = 0`
     flag invariance, `count > 1` demonic `OF`), `inc`/`dec` `CF` preservation,
     and `div`/`idiv` `#DE` traps (`0` and `INT64_MIN / -1`), paired with
     negative mutation canaries refuting defective models.
-/

namespace Anneal.SemanticPolarity

/-! ## Section 1: Core Refinement & StepMachine Lattice (from `Trusted/Refinement.lean`) -/

/-- A demonic-nondeterministic partial computation over `Out`. -/
structure Partial (Out : Type u) where
  defined : Prop
  outcomes : Out → Prop

namespace Partial

/-- Refinement order: `a ≤ b` iff whenever `b` is defined, `a` is defined and
every outcome of `a` is permitted by `b`. -/
def le (a b : Partial Out) : Prop :=
  b.defined → a.defined ∧ ∀ o, a.outcomes o → b.outcomes o

instance : LE (Partial Out) := ⟨Partial.le⟩

theorem le_refl (a : Partial Out) : a ≤ a :=
  fun hd => ⟨hd, fun _ ho => ho⟩

theorem le_trans {a b c : Partial Out} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  intro hc
  obtain ⟨hb, hbc_out⟩ := hbc hc
  obtain ⟨ha, hab_out⟩ := hab hb
  exact ⟨ha, fun o hoa => hbc_out o (hab_out o hoa)⟩

/-- Top element `⊤` of the refinement lattice: Undefined Behavior (`defined = False`). -/
def ub : Partial Out where
  defined := False
  outcomes := fun _ => True

/-- Bottom element `⊥` of the refinement lattice: miraculous vacuity (`defined = True, outcomes = ∅`). -/
def magic : Partial Out where
  defined := True
  outcomes := fun _ => False

/-- Every partial behavior refines `Partial.ub` (`⊤`). -/
theorem le_ub (a : Partial Out) : a ≤ Partial.ub := by
  intro h
  exact False.elim h

end Partial

/-- Pointwise query-indexed semantics. -/
def Sem (Q : Type u) (Out : Type v) := Q → Partial Out

namespace Sem

def le (f g : Sem Q Out) : Prop := ∀ q, (f q).le (g q)

instance : LE (Sem Q Out) := ⟨Sem.le⟩

theorem le_refl (f : Sem Q Out) : f ≤ f :=
  fun q => Partial.le_refl (f q)

theorem le_trans {f g h : Sem Q Out} (hfg : f ≤ g) (hgh : g ≤ h) : f ≤ h :=
  fun q => Partial.le_trans (hfg q) (hgh q)

end Sem

/-- Language with program syntax, queries, outcomes, and operational semantics. -/
structure Language where
  Prog : Type u
  Query : Type v
  Out : Type w
  sem : Prog → Sem Query Out

/-- Partial specification over precondition `pre` and postcondition `post`. -/
def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : Sem L.Query L.Out :=
  fun q => {
    defined := pre q
    outcomes := fun o => pre q → post q o
  }

/-- Well-formedness (absence of UB) on queries satisfying `pre`. -/
def Language.WellFormedOn (L : Language) (pre : L.Query → Prop) :
    Sem L.Query L.Out :=
  L.SpecOn pre (fun _ _ => True)

theorem Language.specOn_le_wellFormedOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) :
    L.SpecOn pre post ≤ L.WellFormedOn pre := by
  intro q hpre
  exact ⟨hpre, fun _ _ _ => trivial⟩

/-- Compiler refinement obligation: target semantics refines translated source semantics. -/
def Compiles (L₁ L₂ : Language)
    (π_c : Sem L₁.Query L₁.Out → Sem L₂.Query L₂.Out)
    (p₁ : L₁.Prog) (p₂ : L₂.Prog) : Prop :=
  L₂.sem p₂ ≤ π_c (L₁.sem p₁)

/-- Pullback translation morphism along query decompilation `decompileQ` and
outcome decompilation `decompileOut` (matching `π_stage0` in
`theory/Anneal/Compiler/NaiveCodegen.lean:155-158`). -/
def pullbackMorphism {Q₁ Out₁ Q₂ Out₂ : Type}
    (decompileQ : Q₂ → Q₁) (decompileOut : Out₂ → Out₁)
    (srcSem : Sem Q₁ Out₁) : Sem Q₂ Out₂ :=
  fun q₂ => {
    defined := (srcSem (decompileQ q₂)).defined
    outcomes := fun o₂ => (srcSem (decompileQ q₂)).outcomes (decompileOut o₂)
  }

/-- Small-step outcome matching `Trusted/StepResult.lean`. -/
inductive FailureKind where
  | ub
  | unmodeled
  deriving DecidableEq, Repr

inductive StepResult (S V : Type) where
  | step (next : S)
  | terminated (val : V)
  | failed (kind : FailureKind)
  | stuck
  deriving DecidableEq, Repr

structure StepMachine (Prog Q S Out : Type) where
  initState : Prog → Q → S → Prop
  step : Prog → S → StepResult S Out

inductive Reaches {Prog Q S Out : Type} (M : StepMachine Prog Q S Out)
    (p : Prog) : Nat → S → StepResult S Out → Prop where
  | zero (s : S) :
      Reaches M p 0 s (M.step p s)
  | succ (n : Nat) (s s' : S) (r : StepResult S Out) :
      M.step p s = .step s' →
      Reaches M p n s' r →
      Reaches M p (n + 1) s r

def BehaviorOf {Prog Q S Out : Type} (M : StepMachine Prog Q S Out)
    (p : Prog) : Sem Q Out :=
  fun q => {
    defined :=
      ∀ s₀, M.initState p q s₀ →
        ∀ n k, Reaches M p n s₀ (.failed k) → False
    outcomes := fun o =>
      ∃ s₀, M.initState p q s₀ ∧
        ∃ n, Reaches M p n s₀ (.terminated o)
  }

/-! ## Section 2: Quadrant 1 — Source Language on LHS (`L_src.sem s ≤ spec` + Unverified Compiler) -/

/-- **Quadrant 1A (Fail-Open / Unsoundness of Omitting UB in `L_src`)**:
If `L_real` has UB (`defined = False`) at `q_bad`, an unverified optimizing
compiler in `hTcb` may legally exploit that UB to emit target code producing
`o_exploit ∉ post q_bad` (since `L_tgt.sem t ≤ L_real.sem s` holds trivially
at `q_bad` via `Partial.le_ub`). If `L_buggy` omits that UB and steps `q_bad`
to a safe value `o_safe ∈ post q_bad`, then `L_buggy` verifies the program
(`L_buggy.sem s ≤ L_buggy.SpecOn pre post`) while the compiled binary produces
`o_exploit ∉ post q_bad`. -/
theorem q1_omitting_ub_is_fail_open
    {Q Out : Type} (q_bad : Q) (o_safe o_exploit : Out)
    (pre : Q → Prop) (post : Q → Out → Prop)
    (h_pre : pre q_bad)
    (h_safe : post q_bad o_safe)
    (h_exploit_bad : ¬ post q_bad o_exploit) :
    let L_real : Language := {
      Prog := Unit, Query := Q, Out := Out,
      sem := fun _ q => {
        defined := q ≠ q_bad
        outcomes := fun o => q = q_bad ∨ o = o_safe
      }
    }
    let L_buggy : Language := {
      Prog := Unit, Query := Q, Out := Out,
      sem := fun _ _ => { defined := True, outcomes := fun o => o = o_safe }
    }
    let tgt_sem : Sem Q Out := fun q => {
      defined := True
      outcomes := fun o => (q = q_bad ∧ o = o_exploit) ∨ (q ≠ q_bad ∧ o = o_safe)
    }
    -- (1) The buggy source model verifies the program on `q_bad`:
    (L_buggy.sem () q_bad).le (L_buggy.SpecOn pre post q_bad) ∧
    -- (2) The real compiler legally compiles `()` to `tgt_sem` (refining `L_real`):
    Sem.le tgt_sem (L_real.sem ()) ∧
    -- (3) Yet the compiled target program violates `SpecOn pre post` at `q_bad`!
    ¬ (tgt_sem q_bad).le (L_real.SpecOn pre post q_bad) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact ⟨trivial, fun o ho => fun _ => ho ▸ h_safe⟩
  · intro q h_neq
    refine ⟨trivial, fun o h_out => ?_⟩
    rcases h_out with ⟨h_eq, _⟩ | ⟨_, h_o⟩
    · exact False.elim (h_neq h_eq)
    · exact Or.inr h_o
  · intro h_le
    obtain ⟨_, h_out⟩ := h_le h_pre
    exact h_exploit_bad (h_out o_exploit (Or.inl ⟨rfl, rfl⟩) h_pre)

/-- **Quadrant 1B (Fail-Open / Unsoundness of Omitting Nondeterminism in `L_src`)**:
If `L_real` permits two outcomes `{o_good, o_bad}` (e.g., exposed pointer
provenance / uninitialized padding byte choice) and `L_buggy` collapses this to
deterministic `{o_good}`, then `L_buggy` verifies `SpecOn pre post` while
`L_real` violates it. -/
theorem q1_omitting_nondet_is_fail_open
    {Q Out : Type} (q₀ : Q) (o_good o_bad : Out)
    (pre : Q → Prop) (post : Q → Out → Prop)
    (h_pre : pre q₀)
    (h_good : post q₀ o_good)
    (h_bad : ¬ post q₀ o_bad) :
    let L_real : Language := {
      Prog := Unit, Query := Q, Out := Out,
      sem := fun _ _ => { defined := True, outcomes := fun o => o = o_good ∨ o = o_bad }
    }
    let L_buggy : Language := {
      Prog := Unit, Query := Q, Out := Out,
      sem := fun _ _ => { defined := True, outcomes := fun o => o = o_good }
    }
    (L_buggy.sem () q₀).le (L_buggy.SpecOn pre post q₀) ∧
    ¬ (L_real.sem () q₀).le (L_real.SpecOn pre post q₀) := by
  refine ⟨?_, ?_⟩
  · intro _
    exact ⟨trivial, fun o ho _ => ho ▸ h_good⟩
  · intro h_le
    obtain ⟨_, h_out⟩ := h_le h_pre
    exact h_bad (h_out o_bad (Or.inr rfl) h_pre)

/-- **Quadrant 1C (Fail-Closed Safety of Adding Spurious UB in `L_src`)**:
When `L_src` sits on the LHS of `L_src.sem s ≤ L_src.SpecOn pre post`, adding
spurious UB (`defined = False`) at any query `q₀` satisfying `pre q₀` makes
verification fail-closed: `L_src.sem s ≤ L_src.SpecOn pre post` is refutable. -/
theorem q1_spurious_ub_is_fail_closed
    (L : Language) (s : L.Prog) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) (q₀ : L.Query)
    (h_pre : pre q₀)
    (h_spurious_ub : ¬ (L.sem s q₀).defined) :
    ¬ (L.sem s ≤ L.SpecOn pre post) := by
  intro h_le
  obtain ⟨h_def, _⟩ := h_le q₀ h_pre
  exact h_spurious_ub h_def

/-! ## Section 3: Quadrant 2 — Target ISA on LHS (`L_tgt.sem t ≤ spec_tgt`) -/

/-- **Quadrant 2A (Fail-Open / Unsoundness of Omitting a Hardware Trap in `L_tgt`)**:
When `L_tgt` is the trusted target ISA (as in `mir-to-x86`), omitting a
hardware trap (so `L_tgt_model` has `defined = True` where real silicon
`L_silicon` faults with `defined = False`) allows a faulting binary `t` to pass
`L_tgt_model.sem t ≤ spec_tgt` while faulting on real hardware. -/
theorem q2_omitting_hw_trap_is_fail_open
    {Q Out : Type} (q_trap : Q) (o_fake : Out)
    (pre : Q → Prop) (post : Q → Out → Prop)
    (h_pre : pre q_trap)
    (h_fake_ok : post q_trap o_fake) :
    let L_tgt_model : Language := {
      Prog := Unit, Query := Q, Out := Out,
      sem := fun _ _ => { defined := True, outcomes := fun o => o = o_fake }
    }
    let L_silicon : Language := {
      Prog := Unit, Query := Q, Out := Out,
      sem := fun _ q => { defined := q ≠ q_trap, outcomes := fun o => o = o_fake }
    }
    (L_tgt_model.sem () q_trap).le (L_tgt_model.SpecOn pre post q_trap) ∧
    ¬ (L_silicon.sem () q_trap).le (L_silicon.SpecOn pre post q_trap) := by
  refine ⟨?_, ?_⟩
  · intro _
    exact ⟨trivial, fun o ho _ => ho ▸ h_fake_ok⟩
  · intro h_le
    obtain ⟨h_def, _⟩ := h_le h_pre
    exact h_def rfl

/-- **Quadrant 2B (Fail-Open / Unsoundness of Under-Approximating Undefined Flags in `L_tgt`)**:
If an x86-64 instruction leaves a flag (`OF` after multi-bit shift `shl rax, 2`)
architecturally undefined (`outcomes = {false, true}` on silicon) and
`L_tgt_model` models it as deterministic `false`, then a program reading that
flag verifies against `post := (o = false)` in `L_tgt_model` while failing on
silicon when the processor sets `OF = true`. -/
theorem q2_underapproximating_undef_flag_is_fail_open :
    let model_of : Partial Bool := { defined := True, outcomes := fun b => b = false }
    let silicon_of : Partial Bool := { defined := True, outcomes := fun _ => True }
    let spec_false : Partial Bool := { defined := True, outcomes := fun b => b = false }
    model_of.le spec_false ∧ ¬ silicon_of.le spec_false := by
  refine ⟨?_, ?_⟩
  · intro _
    exact ⟨trivial, fun _ hb => hb⟩
  · intro h_le
    obtain ⟨_, h_out⟩ := h_le trivial
    have h_eq : true = false := h_out true trivial
    cases h_eq

/-! ### Concrete Quadrant-2 Divergences in `mir-to-x86`'s `Trusted/X86Semantics.lean` -/

/-- Exact mirror of `X86BinOp` and `evalX86BinOp` from
`mir-to-x86/trusted/lean/Trusted/X86Semantics.lean:207-230` at commit
`4f45f0a391a921ced9c9dc773b9a040dbc215d14`. -/
inductive ModelX86BinOp where
  | add | sub | mul | shl | shr
  deriving DecidableEq, Repr

def modelEvalX86BinOp (op : ModelX86BinOp) (a b : Nat) : Nat :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b
  | .shl => a <<< b
  | .shr => a >>> b

/-- Faithful 64-bit hardware ALU execution on `BitVec 64` (matching x86-64
`addq`, `subq`, `imulq`, `shlq`, `shrq` where shift counts are masked to
`b &&& 63`). -/
def hwEvalX86BinOp64 (op : ModelX86BinOp) (a b : BitVec 64) : BitVec 64 :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b
  | .shl => a <<< (b &&& 63#64)
  | .shr => a >>> (b &&& 63#64)

/-- **Concrete Bug 2A-1 (`sub` underflow truncation vs. 64-bit two's-complement wraparound)**:
In `Trusted/X86Semantics.lean:213`, `0 - 1` evaluates to `0` (`Nat` truncating
subtraction), whereas `subq $1, %rax` on `rax = 0` produces
`0xffffffffffffffff = 2^64 - 1`. -/
theorem x86sem_nat_sub_diverges_from_hw64 :
    modelEvalX86BinOp .sub 0 1 = 0 ∧
    (hwEvalX86BinOp64 .sub 0#64 1#64).toNat = 2 ^ 64 - 1 ∧
    modelEvalX86BinOp .sub 0 1 ≠ (hwEvalX86BinOp64 .sub 0#64 1#64).toNat := by
  decide

/-- **Concrete Bug 2A-2 (`add` overflow unbounded `Nat` vs. 64-bit modular wraparound)**:
In `Trusted/X86Semantics.lean:212`, `(2^64 - 1) + 1` evaluates to `2^64`,
whereas `addq $1, %rax` on `rax = 0xffffffffffffffff` wraps to `0`. -/
theorem x86sem_nat_add_diverges_from_hw64 :
    modelEvalX86BinOp .add (2 ^ 64 - 1) 1 = 2 ^ 64 ∧
    (hwEvalX86BinOp64 .add (BitVec.ofNat 64 (2 ^ 64 - 1)) 1#64).toNat = 0 ∧
    modelEvalX86BinOp .add (2 ^ 64 - 1) 1 ≠
      (hwEvalX86BinOp64 .add (BitVec.ofNat 64 (2 ^ 64 - 1)) 1#64).toNat := by
  decide

/-- **Concrete Bug 2A-3 (`shl` unmasked shift count & unbounded `Nat` vs. `cl & 0x3f`)**:
In `Trusted/X86Semantics.lean:221`, `1 <<< 64` evaluates to `2^64`, whereas
`shlq %cl, %rax` with `rax = 1, cl = 64` masks `cl` to `64 & 63 = 0` and
produces `1`. -/
theorem x86sem_nat_shl_diverges_from_hw64 :
    modelEvalX86BinOp .shl 1 64 = 2 ^ 64 ∧
    (hwEvalX86BinOp64 .shl 1#64 64#64).toNat = 1 ∧
    modelEvalX86BinOp .shl 1 64 ≠ (hwEvalX86BinOp64 .shl 1#64 64#64).toNat := by
  decide

/-- **Concrete Bug 2A-4 (`shr` unmasked shift count vs. `cl & 0x3f`)**:
In `Trusted/X86Semantics.lean:222`, `1 >>> 64` evaluates to `0`, whereas
`shrq %cl, %rax` with `rax = 1, cl = 64` masks `cl` to `64 & 63 = 0` and
produces `1`. -/
theorem x86sem_nat_shr_diverges_from_hw64 :
    modelEvalX86BinOp .shr 1 64 = 0 ∧
    (hwEvalX86BinOp64 .shr 1#64 64#64).toNat = 1 ∧
    modelEvalX86BinOp .shr 1 64 ≠ (hwEvalX86BinOp64 .shr 1#64 64#64).toNat := by
  decide

/-! ## Section 4: Quadrant 3 — Source / Intermediate Language on RHS of `Compiles` -/

/-- **Quadrant 3A (The Spurious-UB Codegen Exploit)**:
Suppose `L_src` sits on the RHS of `Compiles L_src L_tgt π_c s t`
(`L_tgt.sem t ≤ π_c (L_src.sem s)`), where `π_c = pullbackMorphism decompileQ decompileOut`.
If `L_src.sem s` declares *spurious UB* (`defined = False`) at `decompileQ q`,
then `(L_tgt.sem t q).le (π_c (L_src.sem s) q)` holds for **every arbitrary
target program `t`**—even if `t` is `ud2` (`defined = False`) or writes
arbitrary corrupted values! -/
theorem q3_spurious_ub_codegen_exploit
    (L_src L_tgt : Language)
    (decompileQ : L_tgt.Query → L_src.Query)
    (decompileOut : L_tgt.Out → L_src.Out)
    (s : L_src.Prog) (t_broken : L_tgt.Prog) (q : L_tgt.Query)
    (h_spurious_ub : ¬ (L_src.sem s (decompileQ q)).defined) :
    (L_tgt.sem t_broken q).le
      (pullbackMorphism decompileQ decompileOut (L_src.sem s) q) := by
  intro h_def
  exact False.elim (h_spurious_ub h_def)

/-- **Quadrant 3B (Two-Sided Sandwich — Neutralizing Spurious UB)**:
When the verification pipeline requires *both*:
1. `Compiles L_src L_tgt (pullbackMorphism decompileQ decompileOut) s t`
   (`L_tgt.sem t ≤ π_c (L_src.sem s)`), AND
2. `L_src.sem s ≤ L_src.SpecOn pre post`,
then for every target query `q` whose decompilation satisfies `pre (decompileQ q)`:
- `(L_src.sem s (decompileQ q)).defined` is **forced to hold** (making the
  Quadrant-3 spurious-UB exploit impossible on `pre`), and
- `L_tgt.sem t` refines the pullback specification
  `L_tgt.SpecOn (fun q => pre (decompileQ q)) (fun q o => post (decompileQ q) (decompileOut o))`. -/
theorem q3_two_sided_sandwich_soundness
    (L_src L_tgt : Language)
    (decompileQ : L_tgt.Query → L_src.Query)
    (decompileOut : L_tgt.Out → L_src.Out)
    (pre : L_src.Query → Prop)
    (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) (t : L_tgt.Prog)
    (h_compiles : Compiles L_src L_tgt (pullbackMorphism decompileQ decompileOut) s t)
    (h_src_spec : L_src.sem s ≤ L_src.SpecOn pre post) :
    (∀ q, pre (decompileQ q) → (L_src.sem s (decompileQ q)).defined) ∧
    (L_tgt.sem t ≤
      L_tgt.SpecOn (fun q => pre (decompileQ q))
        (fun q o => post (decompileQ q) (decompileOut o))) := by
  refine ⟨?_, ?_⟩
  · intro q h_pre
    exact (h_src_spec (decompileQ q) h_pre).1
  · intro q h_pre
    obtain ⟨h_src_def, h_src_out⟩ := h_src_spec (decompileQ q) h_pre
    obtain ⟨h_tgt_def, h_tgt_out⟩ := h_compiles q h_src_def
    refine ⟨h_tgt_def, fun o h_o _ => ?_⟩
    exact h_src_out (decompileOut o) (h_tgt_out o h_o) h_pre

/-! ## Section 5: Quadrant 4 — Negative-Polarity Premise Language (`ConstMirMachine` / `MonoAdmitted`) -/

/-- **Quadrant 4A (Fail-Open / Unsoundness of Spurious CTFE Failure in `initMirState`, `trusted-core`)**:
In `trusted-core` (`Trusted/MirSemantics.lean:611-612`), `initMirState` is
`initEntryState body s ∧ MonoAdmitted s.tySizes body`. Because `M.initState` sits
on the **left-hand side of an implication** inside `(BehaviorOf M prog q).defined`,
any spurious failure in `ConstMirMachine` that causes `¬ MonoAdmitted q` on a
monomorphization `q` that `rustc` actually compiles makes `M.initState prog q s₀`
always `False`. Consequently, `BehaviorOf M prog q` equals `Partial.magic` (`⊥`)
and vacuously satisfies *every* specification `SpecOn pre post`—even if the
runtime step function immediately triggers `.failed .ub` (`unreachable_unchecked`
or size-mismatched `transmute_copy`)! -/
theorem q4_spurious_ctfe_failure_vacuously_verifies_ub_in_initState
    {Q S Out : Type}
    (initEntry : Q → S → Prop)
    (MonoAdmitted : Q → Prop)
    (s_entry : S) (q_valid : Q)
    (pre : Q → Prop) (post : Q → Out → Prop)
    (h_entry : initEntry q_valid s_entry)
    (h_spurious_ctfe_fail : ¬ MonoAdmitted q_valid) :
    let M_runtime_ub : StepMachine Unit Q S Out := {
      initState := fun _ q s => initEntry q s ∧ MonoAdmitted q
      step := fun _ _ => .failed .ub
    }
    let L : Language := {
      Prog := Unit, Query := Q, Out := Out,
      sem := BehaviorOf M_runtime_ub
    }
    -- Even though `s_entry` satisfies `initEntry q_valid` and `M_runtime_ub.step`
    -- unconditionally steps to `.failed .ub`, `L.sem ()` vacuously refines
    -- `L.SpecOn pre post` at `q_valid`!
    initEntry q_valid s_entry ∧
    Reaches M_runtime_ub () 0 s_entry (.failed .ub) ∧
    (L.sem () q_valid).le (L.SpecOn pre post q_valid) := by
  refine ⟨h_entry, Reaches.zero s_entry, ?_⟩
  intro _
  refine ⟨?_, ?_⟩
  · intro s₀ ⟨_, h_mono⟩ _ _ _
    exact h_spurious_ctfe_fail h_mono
  · intro o ⟨s₀, ⟨_, h_mono⟩, _⟩
    exact False.elim (h_spurious_ctfe_fail h_mono)

/-- **Quadrant 4B (Fail-Open / Unsoundness of Spurious CTFE Failure in `effectivePre`, `mir-to-x86`)**:
In `mir-to-x86` (`Trusted/X86Semantics.lean:821-823`), `MonoAdmitted` sits inside
`effectivePre q := MonoAdmitted q.tySizes prog ∧ pre q`. A spurious CTFE failure
(`¬ MonoAdmitted`) makes `effectivePre q_valid` false, so even a program whose
semantics is `Partial.ub` (`ud2`) vacuously satisfies `SpecOn effectivePre post`
at `q_valid`. -/
theorem q4_spurious_ctfe_failure_vacuously_verifies_ub_in_effectivePre
    (L : Language) (prog_ub : L.Prog) (q_valid : L.Query)
    (MonoAdmitted : L.Query → Prop) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop)
    (h_ub : L.sem prog_ub q_valid = Partial.ub)
    (h_spurious_ctfe_fail : ¬ MonoAdmitted q_valid) :
    L.sem prog_ub q_valid = Partial.ub ∧
    (L.sem prog_ub q_valid).le
      (L.SpecOn (fun q => MonoAdmitted q ∧ pre q) post q_valid) := by
  refine ⟨h_ub, ?_⟩
  intro ⟨h_mono, _⟩
  exact False.elim (h_spurious_ctfe_fail h_mono)

/-- **Quadrant 4C (Fail-Closed Direction of Omitting a CTFE Panic)**:
Conversely, if a CTFE model `MonoAdmitted_loose` omits a CTFE failure so that
it admits a superset of monomorphizations (`∀ q, MonoAdmitted_true q → MonoAdmitted_loose q`),
then any proof of `L.sem prog ≤ L.SpecOn (fun q => MonoAdmitted_loose q ∧ pre q) post`
soundly implies `L.sem prog ≤ L.SpecOn (fun q => MonoAdmitted_true q ∧ pre q) post`. -/
theorem q4_omitting_ctfe_panic_is_fail_closed
    (L : Language) (prog : L.Prog)
    (MonoAdmitted_true MonoAdmitted_loose pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop)
    (h_superset : ∀ q, MonoAdmitted_true q → MonoAdmitted_loose q)
    (h_verified_loose :
      L.sem prog ≤ L.SpecOn (fun q => MonoAdmitted_loose q ∧ pre q) post) :
    L.sem prog ≤ L.SpecOn (fun q => MonoAdmitted_true q ∧ pre q) post := by
  intro q ⟨h_true, h_pre⟩
  have h_loose : MonoAdmitted_loose q ∧ pre q := ⟨h_superset q h_true, h_pre⟩
  obtain ⟨h_def, h_out⟩ := h_verified_loose q h_loose
  exact ⟨h_def, fun o ho _ => h_out o ho h_loose⟩

/-! ## Section 6: Faithful x86-64 ISA Semantics vs. Negative Mutation Canaries -/

/-- Sub-register operand widths on x86-64. -/
inductive RegWidth where
  | w8
  | w16
  | w32
  | w64
  deriving DecidableEq, Repr

/-- Faithful x86-64 destination register write rule (Intel SDM Vol. 1 §3.4.1.1):
- 8-bit (`al`) and 16-bit (`ax`) writes merge into the low 8 or 16 bits of the
  64-bit general-purpose register, preserving bits `[63:8]` or `[63:16]`.
- 32-bit (`eax`) writes **zero-extend** to 64 bits, clearing bits `[63:32]`.
- 64-bit (`rax`) writes replace all 64 bits. -/
def writeRegSub (oldVal newVal : BitVec 64) (w : RegWidth) : BitVec 64 :=
  match w with
  | .w8  => (oldVal &&& 0xffffffffffffff00#64) ||| (newVal &&& 0x00000000000000ff#64)
  | .w16 => (oldVal &&& 0xffffffffffff0000#64) ||| (newVal &&& 0x000000000000ffff#64)
  | .w32 => newVal &&& 0x00000000ffffffff#64
  | .w64 => newVal

/-- Buggy sub-register write model that zero-extends `w8`/`w16` or merges `w32`. -/
def buggyWriteRegSub (oldVal newVal : BitVec 64) (w : RegWidth) : BitVec 64 :=
  match w with
  | .w8  => newVal &&& 0x00000000000000ff#64
  | .w16 => newVal &&& 0x000000000000ffff#64
  | .w32 => (oldVal &&& 0xffffffff00000000#64) ||| (newVal &&& 0x00000000ffffffff#64)
  | .w64 => newVal

/-- **Positive Canary 1**: `writeRegSub` matches the exact values observed on
`x86_64-unknown-linux-gnu` silicon in `x86_conformance_probe.c` (`[TEST 1]`). -/
theorem canary_pos_subregister_writes :
    let seed := 0x1122334455667788#64
    writeRegSub seed 0xaa#64 .w8 = 0x11223344556677aa#64 ∧
    writeRegSub seed 0xbbcc#64 .w16 = 0x112233445566bbcc#64 ∧
    writeRegSub seed 0xddeeff00#64 .w32 = 0x00000000ddeeff00#64 := by
  decide

/-- **Negative Canary 1**: `buggyWriteRegSub` is refuted on all three sub-register widths. -/
theorem canary_neg_subregister_writes :
    let seed := 0x1122334455667788#64
    buggyWriteRegSub seed 0xaa#64 .w8 ≠ writeRegSub seed 0xaa#64 .w8 ∧
    buggyWriteRegSub seed 0xbbcc#64 .w16 ≠ writeRegSub seed 0xbbcc#64 .w16 ∧
    buggyWriteRegSub seed 0xddeeff00#64 .w32 ≠ writeRegSub seed 0xddeeff00#64 .w32 := by
  decide

/-- Arithmetic status flags in `RFLAGS`. -/
structure RFlags where
  cf : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving DecidableEq, Repr

/-- Faithful `incq` / `decq` semantics (Intel SDM Vol. 2A "INC"/"DEC"):
updates `ZF`, `SF`, `OF` while **preserving `CF`**. -/
def execInc64 (x : BitVec 64) (flags : RFlags) : BitVec 64 × RFlags :=
  let res := x + 1#64
  (res, {
    cf := flags.cf
    zf := res == 0#64
    sf := res.msb
    of := x == 0x7fffffffffffffff#64
  })

def execDec64 (x : BitVec 64) (flags : RFlags) : BitVec 64 × RFlags :=
  let res := x - 1#64
  (res, {
    cf := flags.cf
    zf := res == 0#64
    sf := res.msb
    of := x == 0x8000000000000000#64
  })

/-- Buggy `incq` model that treats `inc rax` as `add rax, 1` (clobbering `CF`). -/
def buggyExecInc64ClobberCF (x : BitVec 64) (_flags : RFlags) : BitVec 64 × RFlags :=
  let res := x + 1#64
  (res, {
    cf := x == 0xffffffffffffffff#64
    zf := res == 0#64
    sf := res.msb
    of := x == 0x7fffffffffffffff#64
  })

/-- **Positive Canary 2**: `execInc64` and `execDec64` preserve `CF` across
`UINT64_MAX + 1` and `0 - 1`, matching `x86_conformance_probe.c` (`[TEST 4]`). -/
theorem canary_pos_inc_dec_preserve_cf (flags : RFlags) :
    (execInc64 0xffffffffffffffff#64 flags).2.cf = flags.cf ∧
    (execInc64 0xffffffffffffffff#64 flags).2.zf = true ∧
    (execDec64 0#64 flags).2.cf = flags.cf ∧
    (execDec64 0#64 flags).2.sf = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Negative Canary 2**: Modeling `incq` as `addq $1` fails when `x = UINT64_MAX`
and incoming `CF = false`. -/
theorem canary_neg_inc_clobbers_cf :
    let flags0 : RFlags := { cf := false, zf := false, sf := false, of := false }
    (buggyExecInc64ClobberCF 0xffffffffffffffff#64 flags0).2.cf ≠
      (execInc64 0xffffffffffffffff#64 flags0).2.cf := by
  decide

/-- Faithful 64-bit `shlq` semantics with demonic nondeterminism for undefined
flags (Intel SDM Vol. 2B "SAL/SAR/SHL/SHR"):
- The shift count is masked to 6 bits: `c := (count &&& 63#64).toNat`.
- If `c = 0`, the value and **all** flags (`CF`, `ZF`, `SF`, `OF`) are unchanged.
- If `c = 1`, `CF` is the last bit shifted out, `ZF`/`SF` reflect the result,
  and `OF = res.msb ^^ cf`.
- If `c > 1`, `CF` is the last bit shifted out, `ZF`/`SF` reflect the result,
  and `OF` is architecturally undefined (demonic choice over all `Bool`). -/
def execShl64 (x count : BitVec 64) (flags : RFlags) : Partial (BitVec 64 × RFlags) :=
  let c := (count &&& 63#64).toNat
  if c == 0 then
    { defined := True, outcomes := fun out => out = (x, flags) }
  else
    let res := x <<< (count &&& 63#64)
    let cf := x.getLsbD (64 - c)
    let zf := res == 0#64
    let sf := res.msb
    if c == 1 then
      let of_bit := xor res.msb cf
      { defined := True,
        outcomes := fun out => out = (res, { cf, zf, sf, of := of_bit }) }
    else
      { defined := True,
        outcomes := fun out =>
          ∃ of_nd : Bool, out = (res, { cf, zf, sf, of := of_nd }) }

/-- **Positive Canary 3**: Shifting by `64` masks to `0` and preserves both value
and incoming flags (`[TEST 3]`), while shifting by `2` permits both `OF = true`
and `OF = false`. -/
theorem canary_pos_shl64_mask_and_flags (flags : RFlags) :
    (execShl64 1#64 64#64 flags).outcomes (1#64, flags) ∧
    (∃ f_true : RFlags, f_true.of = true ∧
      (execShl64 1#64 2#64 flags).outcomes (4#64, f_true)) ∧
    (∃ f_false : RFlags, f_false.of = false ∧
      (execShl64 1#64 2#64 flags).outcomes (4#64, f_false)) := by
  refine ⟨rfl, ?_, ?_⟩
  · refine ⟨{ cf := (1#64).getLsbD 62, zf := (4#64 == 0#64), sf := (4#64).msb, of := true }, rfl, ?_⟩
    exact ⟨true, rfl⟩
  · refine ⟨{ cf := (1#64).getLsbD 62, zf := (4#64 == 0#64), sf := (4#64).msb, of := false }, rfl, ?_⟩
    exact ⟨false, rfl⟩

/-- Faithful 64-bit signed division `idivq` semantics (Intel SDM Vol. 2A "IDIV"):
Raises `#DE` (`defined = False`, i.e., `Partial.ub`) when `divisor == 0` OR
when `dividend == INT64_MIN (0x8000000000000000)` and `divisor == -1 (0xffffffffffffffff)`
because the signed quotient `+2^63` overflows a 64-bit signed register. -/
def execIdiv64 (dividend divisor : BitVec 64) : Partial (BitVec 64 × BitVec 64) :=
  if divisor == 0#64 || (dividend == 0x8000000000000000#64 && divisor == 0xffffffffffffffff#64) then
    Partial.ub
  else
    { defined := True,
      outcomes := fun out => out = (dividend.sdiv divisor, dividend.srem divisor) }

/-- Buggy `idivq` model that only checks `divisor == 0` and forgets `INT64_MIN / -1`. -/
def buggyExecIdiv64NoOverflowTrap (dividend divisor : BitVec 64) :
    Partial (BitVec 64 × BitVec 64) :=
  if divisor == 0#64 then
    Partial.ub
  else
    { defined := True,
      outcomes := fun out => out = (dividend.sdiv divisor, dividend.srem divisor) }

/-- **Positive & Negative Canary 4**: `execIdiv64` traps (`defined = False`) on
both `divisor = 0` and `INT64_MIN / -1` (matching `SIGFPE` in `[TEST 5]`),
whereas `buggyExecIdiv64NoOverflowTrap` is fail-open (`defined = True`) on
`INT64_MIN / -1`. -/
theorem canary_idiv64_traps_vs_buggy :
    ¬ (execIdiv64 42#64 0#64).defined ∧
    ¬ (execIdiv64 0x8000000000000000#64 0xffffffffffffffff#64).defined ∧
    (buggyExecIdiv64NoOverflowTrap 0x8000000000000000#64 0xffffffffffffffff#64).defined := by
  refine ⟨?_, ?_, trivial⟩
  · change ¬ (if (0#64 == 0#64 || (42#64 == 0x8000000000000000#64 && 0#64 == 0xffffffffffffffff#64)) = true then False else True)
    decide
  · change ¬ (if (0xffffffffffffffff#64 == 0#64 || (0x8000000000000000#64 == 0x8000000000000000#64 && 0xffffffffffffffff#64 == 0xffffffffffffffff#64)) = true then False else True)
    decide

end Anneal.SemanticPolarity

#print axioms Anneal.SemanticPolarity.q1_omitting_ub_is_fail_open
#print axioms Anneal.SemanticPolarity.q1_omitting_nondet_is_fail_open
#print axioms Anneal.SemanticPolarity.q1_spurious_ub_is_fail_closed
#print axioms Anneal.SemanticPolarity.q2_omitting_hw_trap_is_fail_open
#print axioms Anneal.SemanticPolarity.q2_underapproximating_undef_flag_is_fail_open
#print axioms Anneal.SemanticPolarity.x86sem_nat_sub_diverges_from_hw64
#print axioms Anneal.SemanticPolarity.x86sem_nat_add_diverges_from_hw64
#print axioms Anneal.SemanticPolarity.x86sem_nat_shl_diverges_from_hw64
#print axioms Anneal.SemanticPolarity.x86sem_nat_shr_diverges_from_hw64
#print axioms Anneal.SemanticPolarity.q3_spurious_ub_codegen_exploit
#print axioms Anneal.SemanticPolarity.q3_two_sided_sandwich_soundness
#print axioms Anneal.SemanticPolarity.q4_spurious_ctfe_failure_vacuously_verifies_ub_in_initState
#print axioms Anneal.SemanticPolarity.q4_spurious_ctfe_failure_vacuously_verifies_ub_in_effectivePre
#print axioms Anneal.SemanticPolarity.q4_omitting_ctfe_panic_is_fail_closed
#print axioms Anneal.SemanticPolarity.canary_pos_subregister_writes
#print axioms Anneal.SemanticPolarity.canary_neg_subregister_writes
#print axioms Anneal.SemanticPolarity.canary_pos_inc_dec_preserve_cf
#print axioms Anneal.SemanticPolarity.canary_neg_inc_clobbers_cf
#print axioms Anneal.SemanticPolarity.canary_pos_shl64_mask_and_flags
#print axioms Anneal.SemanticPolarity.canary_idiv64_traps_vs_buggy
