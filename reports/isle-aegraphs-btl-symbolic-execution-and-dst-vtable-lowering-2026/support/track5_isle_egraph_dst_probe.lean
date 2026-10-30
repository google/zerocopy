/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# Track 5 Probe: Instruction Selection, E-Graph Certificates, and DST Lowering

This standalone Lean 4.34.1 file mechanizes the core mathematical and compiler
structures analyzed in Track 5:

1. **Universal Algebraic `BitVec 64` Rewrite Rules (Mechanism 1):**
   Proves parametric bitvector identities used by Cranelift's mid-end `opts/`
   and target `lower.isle` backends (strength reduction of multiplication to
   shifts, RISC-V `Zba` `sh1add`/`sh2add`/`sh3add` scaled-index addition,
   RISC-V `Zbb` `andn` bitclear and alignment-mask equivalence, and RISC-V
   flagless `AddWithOverflow` / `SubWithOverflow` vs. AArch64 `ADDS`/`SUBS`
   carry/borrow flags) without `bv_decide` or `Lean.ofReduceBool`.
2. **ISLE-Style Term-Rewriting Instruction Selector & `subsume` Dominance:**
   Models a total pattern-matching instruction selector (`lowerISLE`) lowering
   MIR arithmetic and addressing expressions to RISC-V (`RV64GC` + `Zba` +
   `Zbb`) operations, proves its semantic preservation over all 64-bit register
   environments, and models why Cranelift's acyclic e-graph (`aegraphs`)
   requires `(subsume ...)` for dependency-erasing rewrites.
3. **E-Graph Equational Rewrite Certificate Checker (Mechanism 2):**
   Implements an untrusted-oracle equational proof certificate verifier
   (`checkRewriteTrace`, inspired by `lean-egg`) that checks sequences of local
   subterm rewrites by `rfl` and proves its soundness.
4. **Superblock Symbolic Execution Validator (Mechanism 3):**
   Implements a `BTL`-style (Chamois-CompCert) symbolic execution engine and
   canonical expression normalizer over straight-line trap-guarded superblocks,
   proving that `validateSuperblock` implies exact behavioral simulation.
5. **Rust VTable Layouts, `PointerCoercion::Unsize`, and Dynamic DST Offsets:**
   Models Rust's `[drop_in_place, size, align, methods..., trait_vptrs...]`
   vtable layout, Rust 1.86 trait upcasting via `VtblEntry::TraitVPtr`, dynamic
   DST tail offset and total size computation (`size_and_align_of_dst`),
   `rustc`'s algebraic alignment simplification, and a negative canary theorem
   demonstrating how using static header alignment instead of dynamic vtable
   alignment miscomputes DST tail offsets and produces unaligned pointers.
-/

namespace Track5Probe

/-!
## Section 1: Universal Algebraic `BitVec 64` Rewrite Rules (Mechanism 1)

Anneal's `TrustedBoundary.lean` forbids `Lean.ofReduceBool`, ruling out
`bv_decide` and `native_decide`. We prove universal 64-bit bitvector identities
using algebraic reduction to `Nat` arithmetic (`BitVec.eq_of_toNat_eq` and
`bv_omega`) and bitwise structural lemmas.
-/

/-- Multiplication by 2 equals left shift by 1 for all 64-bit bitvectors. -/
theorem bv64_mul_two_eq_shl_one (x : BitVec 64) :
    x * 2#64 = x <<< 1#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_shiftLeft]
  omega

/-- Multiplication by 4 equals left shift by 2 for all 64-bit bitvectors. -/
theorem bv64_mul_four_eq_shl_two (x : BitVec 64) :
    x * 4#64 = x <<< 2#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_shiftLeft]
  omega

/-- Multiplication by 8 equals left shift by 3 for all 64-bit bitvectors. -/
theorem bv64_mul_eight_eq_shl_three (x : BitVec 64) :
    x * 8#64 = x <<< 3#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_shiftLeft]
  omega

/-- Multiplication by 2 equals self-addition (`x + x`) for all 64-bit
bitvectors (`cranelift/codegen/src/opts/arithmetic.isle`). -/
theorem bv64_mul_two_eq_add_self (x : BitVec 64) :
    x * 2#64 = x + x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_add]
  omega

/-- Two's-complement identity relating `rustc_codegen_ssa`'s alignment mask
`~~~(align - 1)` and `rustc_codegen_cranelift`'s `0 - align` (`-align`). -/
theorem bv64_not_sub_one_eq_neg (align : BitVec 64) :
    ~~~(align - 1#64) = 0#64 - align := by
  bv_omega

/-- Bitwise De Morgan identity `(x &&& ~~~y) &&& ~~~z = x &&& ~~~(y ||| z)`
used in Cranelift's `opts/bitops.isle` to fuse chained `andn` masks. -/
theorem bv64_and_not_and_not_eq_and_not_or (x y z : BitVec 64) :
    (x &&& ~~~y) &&& ~~~z = x &&& ~~~(y ||| z) := by
  rw [BitVec.and_assoc, ← BitVec.not_or]

/-- Mathematical specification of 64-bit unsigned addition overflow: the exact
65-bit sum `a.toNat + b.toNat` is at least `2^64`. On AArch64 (`ADDS`) and
x86-64 (`ADD`), this is the hardware carry flag (`C = 1` / `CF = 1`). -/
def uaddOverflowSpec (a b : BitVec 64) : Bool :=
  decide (a.toNat + b.toNat ≥ 2 ^ 64)

/-- RISC-V flagless `uadd_overflow` lowering
(`cranelift/codegen/src/isa/riscv64/lower.isle:326` and
`rustc_codegen_cranelift/src/num.rs:221`): computes `sum = a + b` and sets the
overflow boolean via `sltu sum, a` (`(a + b) <ᵤ a`). -/
def riscvUaddOverflow (a b : BitVec 64) : BitVec 64 × Bool :=
  let sum := a + b
  (sum, BitVec.ult sum a)

/-- Universal soundness of RISC-V's flagless unsigned addition overflow check:
for all 64-bit bitvectors `a` and `b`, `(a + b) <ᵤ a` is true if and only if
the 65-bit mathematical sum overflows `2^64`. Proved purely via `Nat` modular
arithmetic without `bv_decide`. -/
theorem riscv_uadd_overflow_iff_spec (a b : BitVec 64) :
    (riscvUaddOverflow a b).2 = uaddOverflowSpec a b := by
  simp only [riscvUaddOverflow, uaddOverflowSpec, BitVec.ult]
  apply decide_eq_decide.mpr
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  rw [BitVec.toNat_add]
  by_cases h : a.toNat + b.toNat ≥ 2 ^ 64
  · have hmod : (a.toNat + b.toNat) % 2 ^ 64 = a.toNat + b.toNat - 2 ^ 64 := by
      rw [Nat.mod_eq_sub_mod h]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    omega
  · have hmod : (a.toNat + b.toNat) % 2 ^ 64 = a.toNat + b.toNat :=
      Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    omega

/-- Mathematical specification of 64-bit unsigned subtraction overflow (borrow):
`a.toNat < b.toNat`. On x86-64 (`SUB`), this is `CF = 1`; on AArch64 (`SUBS`),
this is inverted carry `C = 0` (`CC.LO`). -/
def usubOverflowSpec (a b : BitVec 64) : Bool :=
  decide (a.toNat < b.toNat)

/-- `rustc_codegen_cranelift/src/num.rs:235` lowers unsigned `SubWithOverflow`
by computing `diff = a - b` and testing `diff >ᵤ a` (`ult a diff`). We prove
that this test is universally equivalent to `usubOverflowSpec a b` (`a <ᵤ b`).
-/
theorem cg_clif_usub_overflow_iff_spec (a b : BitVec 64) :
    BitVec.ult a (a - b) = usubOverflowSpec a b := by
  simp only [usubOverflowSpec, BitVec.ult]
  apply decide_eq_decide.mpr
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  rw [BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat
  · have hmod : (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 =
        2 ^ 64 - b.toNat + a.toNat :=
      Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    omega
  · have hmod : (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 = a.toNat - b.toNat := by
      have hge : 2 ^ 64 - b.toNat + a.toNat ≥ 2 ^ 64 := by omega
      rw [Nat.mod_eq_sub_mod hge]
      have hsub : 2 ^ 64 - b.toNat + a.toNat - 2 ^ 64 = a.toNat - b.toNat := by
        omega
      rw [hsub]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    omega

/-!
## Section 2: ISLE-Style Instruction Selection & Acyclic E-Graph `subsume`

We define a unified 64-bit expression AST containing both high-level MIR
operators (`add`, `sub`, `mul`, `and_`, `or_`, `not_`, `shl`, `ult`) and
lowered RISC-V (`RV64GC` + `Zba` + `Zbb`) machine operators (`sh1add`,
`sh2add`, `sh3add`, `andn`, `amodeAddImm`).
-/

abbrev Reg := Nat

/-- Unified 64-bit expression tree spanning MIR and lowered RISC-V (`RV64GC` +
`Zba` + `Zbb`) operations. -/
inductive Expr where
  | var (r : Reg)
  | const (c : BitVec 64)
  | not_ (x : Expr)
  | add (x y : Expr)
  | sub (x y : Expr)
  | mul (x y : Expr)
  | and_ (x y : Expr)
  | or_ (x y : Expr)
  | shl (x y : Expr)
  | ult (x y : Expr)
  /-- RISC-V `Zba` `sh1add rd, rs1, rs2`: `rs2 + (rs1 <<< 1)`. -/
  | sh1add (idx base : Expr)
  /-- RISC-V `Zba` `sh2add rd, rs1, rs2`: `rs2 + (rs1 <<< 2)`. -/
  | sh2add (idx base : Expr)
  /-- RISC-V `Zba` `sh3add rd, rs1, rs2`: `rs2 + (rs1 <<< 3)`. -/
  | sh3add (idx base : Expr)
  /-- RISC-V `Zbb` `andn rd, rs1, rs2`: `rs1 &&& ~~~rs2`. -/
  | andn (x y : Expr)
  /-- RISC-V `AMode::RegOffset(base, disp)` address calculation `base + disp`.
  -/
  | amodeAddImm (base : Expr) (disp : BitVec 64)
  deriving DecidableEq, Repr

/-- Register environment mapping register indices to 64-bit values. -/
abbrev RegEnv := Reg → BitVec 64

/-- Denotational semantics of `Expr` in a register environment `env`. -/
def Expr.eval (env : RegEnv) : Expr → BitVec 64
  | .var r => env r
  | .const c => c
  | .not_ x => ~~~(x.eval env)
  | .add x y => x.eval env + y.eval env
  | .sub x y => x.eval env - y.eval env
  | .mul x y => x.eval env * y.eval env
  | .and_ x y => x.eval env &&& y.eval env
  | .or_ x y => x.eval env ||| y.eval env
  | .shl x y => x.eval env <<< y.eval env
  | .ult x y => if BitVec.ult (x.eval env) (y.eval env) then 1#64 else 0#64
  | .sh1add idx base => base.eval env + (idx.eval env <<< 1#64)
  | .sh2add idx base => base.eval env + (idx.eval env <<< 2#64)
  | .sh3add idx base => base.eval env + (idx.eval env <<< 3#64)
  | .andn x y => x.eval env &&& ~~~(y.eval env)
  | .amodeAddImm base disp => base.eval env + disp

/-- Helper implementing ISLE rules for `iadd` lowering on RISC-V (`Zba`
`match_shnadd` in `cranelift/codegen/src/isa/riscv64/lower.isle:68-82` and
constant offset folding in `inst.isle:2428-2441`). -/
def lowerAddRule (lhs rhs : Expr) : Expr :=
  match lhs, rhs with
  | x, .shl y (.const 1#64) => .sh1add y x
  | x, .shl y (.const 2#64) => .sh2add y x
  | x, .shl y (.const 3#64) => .sh3add y x
  | .shl x (.const 1#64), y => .sh1add x y
  | .shl x (.const 2#64), y => .sh2add x y
  | .shl x (.const 3#64), y => .sh3add x y
  | x, .const disp => .amodeAddImm x disp
  | lhs, rhs => .add lhs rhs

theorem lowerAddRule_sound (env : RegEnv) (lhs rhs : Expr) :
    (lowerAddRule lhs rhs).eval env = lhs.eval env + rhs.eval env := by
  unfold lowerAddRule
  split <;> simp [Expr.eval, BitVec.add_comm]

/-- Helper implementing ISLE rules for `band` lowering on RISC-V (`Zbb`
`rv_andn` in `cranelift/codegen/src/isa/riscv64/lower.isle:749-756` and
two's-complement alignment-mask lowering `x &&& (0 - align) => andn x (align - 1)`).
-/
def lowerAndRule (lhs rhs : Expr) : Expr :=
  match lhs, rhs with
  | x, .not_ y => .andn x y
  | .not_ y, x => .andn x y
  | x, .sub (.const 0#64) align => .andn x (.sub align (.const 1#64))
  | lhs, rhs => .and_ lhs rhs

theorem lowerAndRule_sound (env : RegEnv) (lhs rhs : Expr) :
    (lowerAndRule lhs rhs).eval env = (lhs.eval env &&& rhs.eval env) := by
  unfold lowerAndRule
  split
  · rfl
  · simp [Expr.eval, BitVec.and_comm]
  · simp [Expr.eval, bv64_not_sub_one_eq_neg]
  · rfl

/-- Helper implementing mid-end strength reduction for `imul` by small powers
of two (`cranelift/codegen/src/opts/arithmetic.isle`). -/
def lowerMulRule (lhs rhs : Expr) : Expr :=
  match lhs, rhs with
  | x, .const 2#64 => .shl x (.const 1#64)
  | x, .const 4#64 => .shl x (.const 2#64)
  | x, .const 8#64 => .shl x (.const 3#64)
  | lhs, rhs => .mul lhs rhs

theorem lowerMulRule_sound (env : RegEnv) (lhs rhs : Expr) :
    (lowerMulRule lhs rhs).eval env = lhs.eval env * rhs.eval env := by
  unfold lowerMulRule
  split
  · simp [Expr.eval, bv64_mul_two_eq_shl_one]
  · simp [Expr.eval, bv64_mul_four_eq_shl_two]
  · simp [Expr.eval, bv64_mul_eight_eq_shl_three]
  · rfl

/-- Bottom-up ISLE-style term-rewriting instruction selector combining mid-end
strength reduction with RISC-V (`Zba` + `Zbb`) instruction selection. -/
def lowerISLE : Expr → Expr
  | .var r => .var r
  | .const c => .const c
  | .not_ x => .not_ (lowerISLE x)
  | .add x y => lowerAddRule (lowerISLE x) (lowerISLE y)
  | .sub x y => .sub (lowerISLE x) (lowerISLE y)
  | .mul x y => lowerMulRule (lowerISLE x) (lowerISLE y)
  | .and_ x y => lowerAndRule (lowerISLE x) (lowerISLE y)
  | .or_ x y => .or_ (lowerISLE x) (lowerISLE y)
  | .shl x y => .shl (lowerISLE x) (lowerISLE y)
  | .ult x y => .ult (lowerISLE x) (lowerISLE y)
  | .sh1add idx base => .sh1add (lowerISLE idx) (lowerISLE base)
  | .sh2add idx base => .sh2add (lowerISLE idx) (lowerISLE base)
  | .sh3add idx base => .sh3add (lowerISLE idx) (lowerISLE base)
  | .andn x y => .andn (lowerISLE x) (lowerISLE y)
  | .amodeAddImm base disp => .amodeAddImm (lowerISLE base) disp

/-- Universal soundness of `lowerISLE` over all register environments. -/
theorem lowerISLE_sound (env : RegEnv) (e : Expr) :
    (lowerISLE e).eval env = e.eval env := by
  induction e with
  | var r => rfl
  | const c => rfl
  | not_ x ih => simp [lowerISLE, Expr.eval, ih]
  | add x y ihx ihy =>
    simp only [lowerISLE, lowerAddRule_sound, ihx, ihy, Expr.eval]
  | sub x y ihx ihy => simp [lowerISLE, Expr.eval, ihx, ihy]
  | mul x y ihx ihy =>
    simp only [lowerISLE, lowerMulRule_sound, ihx, ihy, Expr.eval]
  | and_ x y ihx ihy =>
    simp only [lowerISLE, lowerAndRule_sound, ihx, ihy, Expr.eval]
  | or_ x y ihx ihy => simp [lowerISLE, Expr.eval, ihx, ihy]
  | shl x y ihx ihy => simp [lowerISLE, Expr.eval, ihx, ihy]
  | ult x y ihx ihy => simp [lowerISLE, Expr.eval, ihx, ihy]
  | sh1add idx base ih1 ih2 => simp [lowerISLE, Expr.eval, ih1, ih2]
  | sh2add idx base ih1 ih2 => simp [lowerISLE, Expr.eval, ih1, ih2]
  | sh3add idx base ih1 ih2 => simp [lowerISLE, Expr.eval, ih1, ih2]
  | andn x y ih1 ih2 => simp [lowerISLE, Expr.eval, ih1, ih2]
  | amodeAddImm base disp ih => simp [lowerISLE, Expr.eval, ih]

/-- Free register variables referenced by an `Expr` (used to formalize
Cranelift `aegraphs` Rule 2 on `subsume` and SSA dominance). -/
def Expr.vars : Expr → List Reg
  | .var r => [r]
  | .const _ => []
  | .not_ x | .amodeAddImm x _ => x.vars
  | .add x y | .sub x y | .mul x y | .and_ x y | .or_ x y
  | .shl x y | .ult x y | .sh1add x y | .sh2add x y | .sh3add x y
  | .andn x y => x.vars ++ y.vars

/-- An expression is well-scoped at a CFG block if every register it references
is in the set `avail` of registers dominating that block. -/
def Expr.wellScoped (avail : List Reg) (e : Expr) : Bool :=
  e.vars.all (fun r => avail.contains r)

/-- Demonstrates Cranelift `opts/README.md` Rule 2 (`subsume` for dependency-
erasing rules): when `band (var 1) (const 0)` is rewritten to `const 0` in
block `B1` where `avail = [0, 1]`, unioning both nodes into a shared e-class
`[band (var 1) (const 0), const 0]` allows GVN to share that e-class with an
earlier block `B0` where `avail = [0]` (because `const 0` is available at root).
If extraction at `B0` inspects the un-subsumed `band (var 1) (const 0)` node, it
violates SSA dominance (`wellScoped [0] = false`), whereas `subsume` replaces
the e-class with `[const 0]`, which remains well-scoped at `B0` (`true`). -/
theorem aegraph_unsubsumed_union_violates_dominance :
    let orig := Expr.and_ (.var 1) (.const 0#64)
    let rewritten := Expr.const 0#64
    let rootAvail : List Reg := [0]
    (∀ env, orig.eval env = rewritten.eval env) ∧
    rewritten.wellScoped rootAvail = true ∧
    orig.wellScoped rootAvail = false := by
  refine ⟨?_, rfl, rfl⟩
  intro env
  simp [Expr.eval]

/-!
## Section 3: E-Graph Equational Certificate Checker (Mechanism 2)

In an equality-saturation optimizer (`lean-egg` / `egg`), the untrusted search
engine finds a path of oriented or symmetric rewrite rules between the source
term and the extracted minimum-cost term. Rather than verifying the e-graph
engine or calling an external SMT solver (`Lean.ofReduceBool`), the optimizer
emits a `List RewriteStep` trace that the Lean kernel checks by `rfl`.
-/

/-- Primitive algebraic rewrite rules supported by the certificate checker. -/
inductive RewriteRule where
  | mul2ToShl1
  | mul4ToShl2
  | mul8ToShl3
  | addShl2RhsToSh2add
  | addShl2LhsToSh2add
  | addConstToAmode
  | andNotToAndn
  | andNegToAndnSubOne
  | andnAndnToAndnOr
  | addComm
  | addAssocLtoR
  deriving DecidableEq, Repr

/-- Applies a single primitive `RewriteRule` at the root of an expression,
returning `none` if the pattern does not match. -/
def applyRuleRoot (rule : RewriteRule) (e : Expr) : Option Expr :=
  match rule, e with
  | .mul2ToShl1, .mul x (.const 2#64) => some (.shl x (.const 1#64))
  | .mul4ToShl2, .mul x (.const 4#64) => some (.shl x (.const 2#64))
  | .mul8ToShl3, .mul x (.const 8#64) => some (.shl x (.const 3#64))
  | .addShl2RhsToSh2add, .add x (.shl y (.const 2#64)) => some (.sh2add y x)
  | .addShl2LhsToSh2add, .add (.shl x (.const 2#64)) y => some (.sh2add x y)
  | .addConstToAmode, .add x (.const disp) => some (.amodeAddImm x disp)
  | .andNotToAndn, .and_ x (.not_ y) => some (.andn x y)
  | .andNegToAndnSubOne, .and_ x (.sub (.const 0#64) align) =>
      some (.andn x (.sub align (.const 1#64)))
  | .andnAndnToAndnOr, .andn (.andn x y) z =>
      some (.andn x (.or_ y z))
  | .addComm, .add x y => some (.add y x)
  | .addAssocLtoR, .add (.add x y) z => some (.add x (.add y z))
  | _, _ => none

/-- Soundness of root-level rule application over all register environments. -/
theorem applyRuleRoot_sound (env : RegEnv) (rule : RewriteRule) (e e' : Expr)
    (h : applyRuleRoot rule e = some e') :
    e'.eval env = e.eval env := by
  unfold applyRuleRoot at h
  split at h
  · injection h with h'; subst h'; simp [Expr.eval, bv64_mul_two_eq_shl_one]
  · injection h with h'; subst h'; simp [Expr.eval, bv64_mul_four_eq_shl_two]
  · injection h with h'; subst h'; simp [Expr.eval, bv64_mul_eight_eq_shl_three]
  · injection h with h'; subst h'; simp [Expr.eval]
  · injection h with h'; subst h'; simp [Expr.eval, BitVec.add_comm]
  · injection h with h'; subst h'; simp [Expr.eval]
  · injection h with h'; subst h'; simp [Expr.eval]
  · injection h with h'; subst h'; simp [Expr.eval, bv64_not_sub_one_eq_neg]
  · injection h with h'; subst h'
    simp [Expr.eval, bv64_and_not_and_not_eq_and_not_or]
  · injection h with h'; subst h'; simp [Expr.eval, BitVec.add_comm]
  · injection h with h'; subst h'; simp [Expr.eval, BitVec.add_assoc]
  · contradiction

/-- Path addressing a subterm inside an `Expr` tree. -/
inductive SubtermPos where
  | here
  | unaryArg (p : SubtermPos)
  | binLhs (p : SubtermPos)
  | binRhs (p : SubtermPos)
  deriving DecidableEq, Repr

/-- One step in an e-graph equational certificate: apply `rule` at `pos`. -/
structure RewriteStep where
  pos : SubtermPos
  rule : RewriteRule
  deriving DecidableEq, Repr

/-- Applies a `RewriteRule` at subterm position `pos` inside `e`. -/
def applyAtPos (pos : SubtermPos) (rule : RewriteRule) (e : Expr) :
    Option Expr :=
  match pos, e with
  | .here, e => applyRuleRoot rule e
  | .unaryArg p, .not_ x => (.not_ ·) <$> applyAtPos p rule x
  | .unaryArg p, .amodeAddImm x d => (.amodeAddImm · d) <$> applyAtPos p rule x
  | .binLhs p, .add x y => (·.add y) <$> applyAtPos p rule x
  | .binRhs p, .add x y => (.add x ·) <$> applyAtPos p rule y
  | .binLhs p, .sub x y => (·.sub y) <$> applyAtPos p rule x
  | .binRhs p, .sub x y => (.sub x ·) <$> applyAtPos p rule y
  | .binLhs p, .mul x y => (·.mul y) <$> applyAtPos p rule x
  | .binRhs p, .mul x y => (.mul x ·) <$> applyAtPos p rule y
  | .binLhs p, .and_ x y => (·.and_ y) <$> applyAtPos p rule x
  | .binRhs p, .and_ x y => (.and_ x ·) <$> applyAtPos p rule y
  | .binLhs p, .or_ x y => (·.or_ y) <$> applyAtPos p rule x
  | .binRhs p, .or_ x y => (.or_ x ·) <$> applyAtPos p rule y
  | .binLhs p, .shl x y => (·.shl y) <$> applyAtPos p rule x
  | .binRhs p, .shl x y => (.shl x ·) <$> applyAtPos p rule y
  | .binLhs p, .ult x y => (·.ult y) <$> applyAtPos p rule x
  | .binRhs p, .ult x y => (.ult x ·) <$> applyAtPos p rule y
  | .binLhs p, .sh1add x y => (·.sh1add y) <$> applyAtPos p rule x
  | .binRhs p, .sh1add x y => (.sh1add x ·) <$> applyAtPos p rule y
  | .binLhs p, .sh2add x y => (·.sh2add y) <$> applyAtPos p rule x
  | .binRhs p, .sh2add x y => (.sh2add x ·) <$> applyAtPos p rule y
  | .binLhs p, .sh3add x y => (·.sh3add y) <$> applyAtPos p rule x
  | .binRhs p, .sh3add x y => (.sh3add x ·) <$> applyAtPos p rule y
  | .binLhs p, .andn x y => (·.andn y) <$> applyAtPos p rule x
  | .binRhs p, .andn x y => (.andn x ·) <$> applyAtPos p rule y
  | _, _ => none

/-- Soundness of applying a rewrite rule at any subterm position `pos`. -/
theorem applyAtPos_sound (env : RegEnv) (pos : SubtermPos) (rule : RewriteRule)
    (e e' : Expr) (h : applyAtPos pos rule e = some e') :
    e'.eval env = e.eval env := by
  induction pos generalizing e e' with
  | here =>
    exact applyRuleRoot_sound env rule e e' h
  | unaryArg p ih =>
    cases e <;> simp [applyAtPos] at h
    all_goals (
      rcases h with ⟨x', hx', rfl⟩
      simp [Expr.eval, ih _ _ hx']
    )
  | binLhs p ih =>
    cases e <;> simp [applyAtPos] at h
    all_goals (
      rcases h with ⟨x', hx', rfl⟩
      simp [Expr.eval, ih _ _ hx']
    )
  | binRhs p ih =>
    cases e <;> simp [applyAtPos] at h
    all_goals (
      rcases h with ⟨y', hy', rfl⟩
      simp [Expr.eval, ih _ _ hy']
    )

/-- Runs a sequence of `RewriteStep`s starting from `e`. -/
def runRewriteTrace : Expr → List RewriteStep → Option Expr
  | e, [] => some e
  | e, step :: rest =>
    match applyAtPos step.pos step.rule e with
    | some e' => runRewriteTrace e' rest
    | none => none

/-- Boolean certificate checker verifying that `trace` rewrites `src` to `dst`.
-/
def checkRewriteTrace (src : Expr) (trace : List RewriteStep) (dst : Expr) :
    Bool :=
  match runRewriteTrace src trace with
  | some final => final == dst
  | none => false

theorem runRewriteTrace_sound (env : RegEnv) (src : Expr)
    (trace : List RewriteStep) (dst : Expr)
    (h : runRewriteTrace src trace = some dst) :
    dst.eval env = src.eval env := by
  induction trace generalizing src with
  | nil =>
    injection h with h'
    subst h'
    rfl
  | cons step rest ih =>
    unfold runRewriteTrace at h
    split at h
    · rename_i e' he'
      have h1 := ih e' h
      have h2 := applyAtPos_sound env step.pos step.rule src e' he'
      rw [h1, h2]
    · contradiction

/-- Main soundness theorem for Mechanism 2: if `checkRewriteTrace src trace dst`
returns `true`, then `src` and `dst` evaluate to the same 64-bit value under
every register environment `env`. -/
theorem checkRewriteTrace_sound (env : RegEnv) (src : Expr)
    (trace : List RewriteStep) (dst : Expr)
    (h : checkRewriteTrace src trace dst = true) :
    src.eval env = dst.eval env := by
  unfold checkRewriteTrace at h
  split at h
  · rename_i final hrun
    have h_eq : final = dst := eq_of_beq h
    subst h_eq
    exact (runRewriteTrace_sound env src trace final hrun).symm
  · contradiction

/-- Concrete example of an e-graph equational certificate optimizing a DST slice
element address calculation:
`((base + ((hdr + (align - 1)) &&& (0 - align))) + (idx * 4)) + 16`
into RISC-V `Zba` + `Zbb` + `AMode` form:
`amodeAddImm (sh2add idx (base + andn (hdr + (align - 1)) (align - 1))) 16`,
checked purely by `rfl`. -/
def dstSliceAddrSrc : Expr :=
  let hdr := Expr.const 4#64
  let align := Expr.var 1
  let base := Expr.var 0
  let idx := Expr.var 2
  let alignedOff := Expr.and_ (.add hdr (.sub align (.const 1#64)))
    (.sub (.const 0#64) align)
  .add (.add (.add base alignedOff) (.mul idx (.const 4#64))) (.const 16#64)

def dstSliceAddrOpt : Expr :=
  let hdr := Expr.const 4#64
  let align := Expr.var 1
  let base := Expr.var 0
  let idx := Expr.var 2
  let alignedOff := Expr.andn (.add hdr (.sub align (.const 1#64)))
    (.sub align (.const 1#64))
  .amodeAddImm (.sh2add idx (.add base alignedOff)) 16#64

def dstSliceAddrTrace : List RewriteStep :=
  [ { pos := .binLhs (.binLhs (.binRhs .here)), rule := .andNegToAndnSubOne },
    { pos := .binLhs (.binRhs .here), rule := .mul4ToShl2 },
    { pos := .binLhs .here, rule := .addShl2RhsToSh2add },
    { pos := .here, rule := .addConstToAmode } ]

theorem dstSliceAddr_verified (env : RegEnv) :
    dstSliceAddrSrc.eval env = dstSliceAddrOpt.eval env :=
  checkRewriteTrace_sound env dstSliceAddrSrc dstSliceAddrTrace dstSliceAddrOpt
    rfl

/-!
## Section 4: Superblock Symbolic Execution Validator (`BTL` Style, Mechanism 3)

Chamois-CompCert's `BTL` pass (`scheduling/BTL_SEsimuref.v`) validates
superblock instruction scheduling, common subexpression elimination (CSE), and
strength reduction by symbolically executing both superblocks with canonical
expression normalization and comparing their final symbolic states.
-/

/-- Canonicalizes an `Expr` by expanding fused target instructions (`sh1add`,
`sh2add`, `sh3add`, `andn`, `amodeAddImm`) and strength-reducible `mul` nodes
into a uniform normal form so that unoptimized MIR superblocks and lowered/CSE'd
RISC-V superblocks reduce to identical symbolic trees. -/
def normExpr : Expr → Expr
  | .var r => .var r
  | .const c => .const c
  | .not_ x => .not_ (normExpr x)
  | .add x y => .add (normExpr x) (normExpr y)
  | .sub x y => .sub (normExpr x) (normExpr y)
  | .mul x y =>
    let nx := normExpr x
    let ny := normExpr y
    match ny with
    | .const 2#64 => .shl nx (.const 1#64)
    | .const 4#64 => .shl nx (.const 2#64)
    | .const 8#64 => .shl nx (.const 3#64)
    | _ => .mul nx ny
  | .and_ x y =>
    let nx := normExpr x
    let ny := normExpr y
    match ny with
    | .sub (.const 0#64) align =>
      .and_ nx (.not_ (.sub align (.const 1#64)))
    | _ => .and_ nx ny
  | .or_ x y => .or_ (normExpr x) (normExpr y)
  | .shl x y => .shl (normExpr x) (normExpr y)
  | .ult x y => .ult (normExpr x) (normExpr y)
  | .sh1add idx base => .add (normExpr base) (.shl (normExpr idx) (.const 1#64))
  | .sh2add idx base => .add (normExpr base) (.shl (normExpr idx) (.const 2#64))
  | .sh3add idx base => .add (normExpr base) (.shl (normExpr idx) (.const 3#64))
  | .andn x y => .and_ (normExpr x) (.not_ (normExpr y))
  | .amodeAddImm base disp => .add (normExpr base) (.const disp)

/-- Universal soundness of the canonical expression normalizer `normExpr`. -/
theorem normExpr_sound (env : RegEnv) (e : Expr) :
    (normExpr e).eval env = e.eval env := by
  induction e with
  | var r => rfl
  | const c => rfl
  | not_ x ih => simp [normExpr, Expr.eval, ih]
  | add x y ihx ihy => simp [normExpr, Expr.eval, ihx, ihy]
  | sub x y ihx ihy => simp [normExpr, Expr.eval, ihx, ihy]
  | mul x y ihx ihy =>
    simp only [normExpr]
    split
    · rename_i heq
      have hy : (normExpr y).eval env = 2#64 := by rw [heq]; rfl
      simp [Expr.eval, ihx, ← ihy, hy, bv64_mul_two_eq_shl_one]
    · rename_i heq
      have hy : (normExpr y).eval env = 4#64 := by rw [heq]; rfl
      simp [Expr.eval, ihx, ← ihy, hy, bv64_mul_four_eq_shl_two]
    · rename_i heq
      have hy : (normExpr y).eval env = 8#64 := by rw [heq]; rfl
      simp [Expr.eval, ihx, ← ihy, hy, bv64_mul_eight_eq_shl_three]
    · simp [Expr.eval, ihx, ihy]
  | and_ x y ihx ihy =>
    simp only [normExpr]
    split
    · rename_i align heq
      have hy : (Expr.sub (.const 0#64) align).eval env = y.eval env := by
        rw [← heq, ihy]
      simp only [Expr.eval] at hy ⊢
      rw [ihx, ← hy, bv64_not_sub_one_eq_neg]
    · simp [Expr.eval, ihx, ihy]
  | or_ x y ihx ihy => simp [normExpr, Expr.eval, ihx, ihy]
  | shl x y ihx ihy => simp [normExpr, Expr.eval, ihx, ihy]
  | ult x y ihx ihy => simp [normExpr, Expr.eval, ihx, ihy]
  | sh1add idx base ih1 ih2 => simp [normExpr, Expr.eval, ih1, ih2]
  | sh2add idx base ih1 ih2 => simp [normExpr, Expr.eval, ih1, ih2]
  | sh3add idx base ih1 ih2 => simp [normExpr, Expr.eval, ih1, ih2]
  | andn x y ih1 ih2 => simp [normExpr, Expr.eval, ih1, ih2]
  | amodeAddImm base disp ih => simp [normExpr, Expr.eval, ih]

/-- Substitutes symbolic register mapping `sregs : Reg → Expr` into `e`. -/
def substExpr (sregs : Reg → Expr) : Expr → Expr
  | .var r => sregs r
  | .const c => .const c
  | .not_ x => .not_ (substExpr sregs x)
  | .add x y => .add (substExpr sregs x) (substExpr sregs y)
  | .sub x y => .sub (substExpr sregs x) (substExpr sregs y)
  | .mul x y => .mul (substExpr sregs x) (substExpr sregs y)
  | .and_ x y => .and_ (substExpr sregs x) (substExpr sregs y)
  | .or_ x y => .or_ (substExpr sregs x) (substExpr sregs y)
  | .shl x y => .shl (substExpr sregs x) (substExpr sregs y)
  | .ult x y => .ult (substExpr sregs x) (substExpr sregs y)
  | .sh1add idx base => .sh1add (substExpr sregs idx) (substExpr sregs base)
  | .sh2add idx base => .sh2add (substExpr sregs idx) (substExpr sregs base)
  | .sh3add idx base => .sh3add (substExpr sregs idx) (substExpr sregs base)
  | .andn x y => .andn (substExpr sregs x) (substExpr sregs y)
  | .amodeAddImm base disp => .amodeAddImm (substExpr sregs base) disp

theorem substExpr_eval (initEnv : RegEnv) (sregs : Reg → Expr) (e : Expr) :
    (substExpr sregs e).eval initEnv =
      e.eval (fun r => (sregs r).eval initEnv) := by
  induction e <;> simp [substExpr, Expr.eval, *]

/-- Superblock instructions: register assignment (`assign`) and trap assertion
(`assertNonZero`, modeling bounds/overflow/division-by-zero checks). -/
inductive SBInstr where
  | assign (dst : Reg) (rhs : Expr)
  | assertNonZero (cond : Expr)
  deriving DecidableEq, Repr

/-- Concrete execution of a superblock from register state `env`. Returns
`none` if a trap assertion fails, or `some env'` on normal completion. -/
def execSuperblock (env : RegEnv) : List SBInstr → Option RegEnv
  | [] => some env
  | .assign dst rhs :: rest =>
    let val := rhs.eval env
    execSuperblock (fun r => if r = dst then val else env r) rest
  | .assertNonZero cond :: rest =>
    if cond.eval env == 0#64 then none
    else execSuperblock env rest

/-- Symbolic state of a superblock: maps each register to a normalized symbolic
expression over initial register values, paired with an ordered list of
normalized non-zero trap guards (`guards`). -/
structure SymState where
  sregs : Reg → Expr
  guards : List Expr

def initSymState : SymState :=
  { sregs := Expr.var, guards := [] }

/-- Symbolic execution of a superblock with on-the-fly canonical normalization.
-/
def symExecSuperblock (st : SymState) : List SBInstr → SymState
  | [] => st
  | .assign dst rhs :: rest =>
    let symVal := normExpr (substExpr st.sregs rhs)
    let sregs' := fun r => if r = dst then symVal else st.sregs r
    symExecSuperblock { st with sregs := sregs' } rest
  | .assertNonZero cond :: rest =>
    let symCond := normExpr (substExpr st.sregs cond)
    symExecSuperblock { st with guards := st.guards ++ [symCond] } rest

/-- Evaluates a symbolic state under initial register environment `initEnv`. -/
def evalSymState (initEnv : RegEnv) (st : SymState) : Option RegEnv :=
  if st.guards.any (fun g => g.eval initEnv == 0#64) then none
  else some (fun r => (st.sregs r).eval initEnv)

/-- Simulation lemma connecting concrete execution (`execSuperblock`) to
symbolic execution (`symExecSuperblock`). -/
theorem symExecSuperblock_correct (initEnv : RegEnv) (st : SymState)
    (block : List SBInstr) :
    evalSymState initEnv (symExecSuperblock st block) =
      match evalSymState initEnv st with
      | none => none
      | some env => execSuperblock env block := by
  induction block generalizing st with
  | nil =>
    unfold symExecSuperblock execSuperblock
    cases evalSymState initEnv st <;> rfl
  | cons instr rest ih =>
    cases instr with
    | assign dst rhs =>
      simp only [symExecSuperblock, ih]
      unfold evalSymState
      by_cases hg : (st.guards.any fun g => g.eval initEnv == 0#64) = true
      · simp [hg]
      · simp only [hg, Bool.false_eq_true, ↓reduceIte, execSuperblock]
        congr 1
        funext r
        split
        · rw [normExpr_sound, substExpr_eval]
        · rfl
    | assertNonZero cond =>
      simp only [symExecSuperblock, ih]
      unfold evalSymState
      simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
      by_cases hg : (st.guards.any fun g => g.eval initEnv == 0#64) = true
      · simp [hg]
      · simp only [hg, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
          execSuperblock, normExpr_sound, substExpr_eval]
        by_cases hc :
            (cond.eval (fun r => (st.sregs r).eval initEnv) == 0#64) = true
        · simp [hc]
        · simp [hc]

/-- Superblock translation validator: symbolically executes `src` and `opt` and
checks that their trap guard lists are identical and that all `liveOut`
registers map to syntactically identical canonical expressions. -/
def validateSuperblock (src opt : List SBInstr) (liveOut : List Reg) : Bool :=
  let stSrc := symExecSuperblock initSymState src
  let stOpt := symExecSuperblock initSymState opt
  (stSrc.guards == stOpt.guards) &&
    liveOut.all (fun r => stSrc.sregs r == stOpt.sregs r)

/-- Main soundness theorem for Mechanism 3 (`BTL`-style symbolic execution):
if `validateSuperblock src opt liveOut = true`, then for every initial register
environment `initEnv`, `src` traps if and only if `opt` traps, and whenever
`src` succeeds with `envSrc`, `opt` succeeds with `envOpt` agreeing on every
register `r ∈ liveOut`. -/
theorem validateSuperblock_sound (initEnv : RegEnv) (src opt : List SBInstr)
    (liveOut : List Reg) (hval : validateSuperblock src opt liveOut = true) :
    match execSuperblock initEnv src, execSuperblock initEnv opt with
    | none, none => True
    | some envSrc, some envOpt => ∀ r ∈ liveOut, envSrc r = envOpt r
    | _, _ => False := by
  have hInit : evalSymState initEnv initSymState = some initEnv := rfl
  have hSrc := symExecSuperblock_correct initEnv initSymState src
  have hOpt := symExecSuperblock_correct initEnv initSymState opt
  rw [hInit] at hSrc hOpt
  dsimp only at hSrc hOpt
  rw [← hSrc, ← hOpt]
  unfold validateSuperblock at hval
  rcases Bool.and_eq_true_iff.mp hval with ⟨hGuards, hRegs⟩
  have hGuardsEq :
      (symExecSuperblock initSymState src).guards =
      (symExecSuperblock initSymState opt).guards :=
    eq_of_beq hGuards
  unfold evalSymState
  rw [hGuardsEq]
  by_cases hg :
      ((symExecSuperblock initSymState opt).guards.any
        fun g => g.eval initEnv == 0#64) = true
  · simp [hg]
  · simp only [hg, Bool.false_eq_true, ↓reduceIte]
    intro r hr
    have hrBeq :
        ((symExecSuperblock initSymState src).sregs r ==
         (symExecSuperblock initSymState opt).sregs r) = true :=
      List.all_eq_true.mp hRegs r hr
    have hrEq := eq_of_beq hrBeq
    rw [hrEq]

/-!
## Section 5: Rust VTable Layouts, `PointerCoercion::Unsize`, and Dynamic DSTs

We now model the Rust compiler's vtable representation (`rustc_middle/src/ty/vtable.rs`
and `rustc_trait_selection/src/traits/vtable.rs`), wide-pointer unsizing and
Rust 1.86 trait upcasting (`rustc_codegen_cranelift/src/unsize.rs`), and dynamic
DST field projection and total size calculation (`rustc_codegen_ssa/src/mir/place.rs`).
-/

/-- Entries in a Rust vtable (`rustc_middle/src/ty/vtable.rs:12-52`).
Slots 0, 1, and 2 of every vtable having a principal trait are fixed by
`COMMON_VTABLE_ENTRIES = [MetadataDropInPlace, MetadataSize, MetadataAlign]`. -/
inductive VtblEntry where
  | metadataDropInPlace (fnPtr : BitVec 64)
  | metadataSize (sizeBytes : BitVec 64)
  | metadataAlign (alignBytes : BitVec 64)
  | vacant
  | method (fnPtr : BitVec 64)
  /-- Embedded sub-vtable pointer for secondary supertrait upcasting (Rust 1.86
  `feature(trait_upcasting)`). -/
  | traitVPtr (subVtableAddr : BitVec 64)
  deriving DecidableEq, Repr

/-- Encodes a `VtblEntry` as a 64-bit machine word in read-only memory. -/
def VtblEntry.toWord : VtblEntry → BitVec 64
  | .metadataDropInPlace fnPtr => fnPtr
  | .metadataSize s => s
  | .metadataAlign a => a
  | .vacant => 0#64
  | .method fnPtr => fnPtr
  | .traitVPtr subVtableAddr => subVtableAddr

/-- Abstract 64-bit word-addressed memory mapping addresses to 64-bit words. -/
abbrev WordMem := BitVec 64 → BitVec 64

/-- Predicate stating that `mem` contains the serialized `entries` starting at
64-bit aligned base address `vtableAddr`. -/
def vtableStoredAt (mem : WordMem) (vtableAddr : BitVec 64)
    (entries : List VtblEntry) : Prop :=
  ∀ (idx : Nat) (entry : VtblEntry),
    entries[idx]? = some entry →
    mem (vtableAddr + BitVec.ofNat 64 (idx * 8)) = entry.toWord

/-- Wide pointer (`ScalarPair`) representation of `&T` / `*const T` for an
unsized type `T: ?Sized`. For `[U]`, `metadata` is the element count; for
`dyn Trait` or a custom DST `Packet<dyn Trait>`, `metadata` is the vtable
address. -/
structure WidePtr where
  dataPtr : BitVec 64
  metadata : BitVec 64
  deriving DecidableEq, Repr

/-- Rust 1.86 trait-upcasting coercion (`rustc_codegen_cranelift/src/unsize.rs:20-70`
`unsized_info`):
- When `supertrait_vtable_slot` is `none` (the target supertrait is a prefix of
  the source vtable along the primary first-supertrait chain, or drops the
  principal trait to an auto trait), the vtable pointer is returned unchanged
  (zero-cost NOP cast).
- When `supertrait_vtable_slot` is `some entryIdx` (a secondary supertrait in a
  multiple-inheritance hierarchy), the coercion loads the `TraitVPtr` word at
  byte offset `entryIdx * 8` from the source vtable. -/
def coerceDynUpcast (mem : WordMem) (src : WidePtr)
    (supertraitVtableSlot : Option Nat) : WidePtr :=
  match supertraitVtableSlot with
  | none => src
  | some entryIdx =>
    let newVptr := mem (src.metadata + BitVec.ofNat 64 (entryIdx * 8))
    { dataPtr := src.dataPtr, metadata := newVptr }

/-- Proves that `coerceDynUpcast` preserves the data pointer and, when a
secondary supertrait slot `some entryIdx` points to a `VtblEntry.traitVPtr
targetVtableAddr`, extracts `targetVtableAddr` as the new metadata. -/
theorem coerceDynUpcast_loads_traitVPtr (mem : WordMem) (src : WidePtr)
    (entries : List VtblEntry) (entryIdx : Nat) (targetVtableAddr : BitVec 64)
    (hStored : vtableStoredAt mem src.metadata entries)
    (hSlot : entries[entryIdx]? = some (.traitVPtr targetVtableAddr)) :
    coerceDynUpcast mem src (some entryIdx) =
      { dataPtr := src.dataPtr, metadata := targetVtableAddr } := by
  have hLoad := hStored entryIdx (.traitVPtr targetVtableAddr) hSlot
  simp only [VtblEntry.toWord] at hLoad
  simp only [coerceDynUpcast, hLoad]

/-- Bitwise upward alignment of `offset` to a power-of-two `align`:
`(offset + (align - 1)) &&& ~~~(align - 1)`
(`rustc_codegen_ssa/src/mir/place.rs:442-449`). -/
def alignToBV (offset align : BitVec 64) : BitVec 64 :=
  (offset + (align - 1#64)) &&& ~~~(align - 1#64)

/-- `rustc_codegen_cranelift/src/value_and_place.rs:46-52` computes upward
alignment using two's-complement negation `(offset + (align - 1)) &&& (0 - align)`.
We prove that both codegen backends compute the exact same 64-bit offset for all
inputs, and both lower to a single RISC-V `Zbb` `andn` instruction after `add`.
-/
theorem alignToBV_eq_cg_clif_formula (offset align : BitVec 64) :
    alignToBV offset align =
      ((offset + (align - 1#64)) &&& (0#64 - align)) := by
  unfold alignToBV
  rw [bv64_not_sub_one_eq_neg]

/-- Dynamic DST tail field offset calculation (`rustc_codegen_ssa/src/mir/place.rs:195-258`
and `rustc_codegen_cranelift/src/value_and_place.rs:31-54`): given the static
unaligned offset `unalignedOffset` of the unsized tail field (equals the size of
the sized header prefix) and a vtable pointer `vptr`, loads `unsizedAlign` from
vtable slot 2 (byte offset 16) and aligns `unalignedOffset` upward to
`unsizedAlign`. -/
def dstTailOffsetDyn (mem : WordMem) (vptr : BitVec 64)
    (unalignedOffset : BitVec 64) : BitVec 64 :=
  let unsizedAlign := mem (vptr + 16#64)
  alignToBV unalignedOffset unsizedAlign

/-- Mathematical `Nat` upward alignment of `offset` to a positive multiple of
`align`: `((offset + align - 1) / align) * align`. -/
def alignToNat (offset align : Nat) : Nat :=
  ((offset + align - 1) / align) * align

/-- Key number-theoretic lemma underlying `rustc`'s DST size optimization
(`rustc_codegen_cranelift/src/unsize.rs:264-272` and
`rustc_codegen_ssa/src/mir/place.rs:321-334`):
Because a DST tail's dynamic `size` is always a multiple of its dynamic `align`
(`size = k * align`), adding `size` to `offset + align - 1` shifts the dividend
by an exact multiple of `align`:
`alignToNat offset align + k * align = alignToNat (offset + k * align) align`. -/
theorem alignToNat_add_mul (offset align k : Nat) (hAlign : align > 0) :
    alignToNat offset align + k * align =
      alignToNat (offset + k * align) align := by
  unfold alignToNat
  have hmul : k * align = align * k := Nat.mul_comm k align
  rw [hmul]
  have hRewrite : offset + align * k + align - 1 =
      (offset + align - 1) + align * k := by
    omega
  rw [hRewrite, Nat.add_mul_div_left _ _ hAlign, Nat.right_distrib,
    Nat.mul_comm k align]

/-- Upward alignment `alignToNat` is idempotent for any positive alignment
`align > 0`. -/
theorem alignToNat_idem (x align : Nat) (hAlign : align > 0) :
    alignToNat (alignToNat x align) align = alignToNat x align := by
  unfold alignToNat
  have hRewrite :
      (x + align - 1) / align * align + align - 1 =
        (align - 1) + align * ((x + align - 1) / align) := by
    rw [Nat.mul_comm ((x + align - 1) / align) align]
    omega
  rw [hRewrite, Nat.add_mul_div_left _ _ hAlign]
  have hDivZero : (align - 1) / align = 0 :=
    Nat.div_eq_of_lt (by omega)
  rw [hDivZero, Nat.zero_add]

/-- Full `rustc` DST total-size theorem
(`rustc_codegen_cranelift/src/unsize.rs:264-272`):
For a custom DST `struct Packet<T: ?Sized>` whose sized prefix has byte length
`unalignedOffset`, whose dynamic tail has size `dynSize = k * align` and
alignment `align > 0` dominating the struct alignment, the two-stage
specification
`alignToNat (alignToNat unalignedOffset align + dynSize) align`
is identically equal to the single-alignment formula
`alignToNat (unalignedOffset + dynSize) align`. -/
theorem rustc_dst_total_size_optimization (unalignedOffset align k : Nat)
    (hAlign : align > 0) :
    let dynSize := k * align
    alignToNat (alignToNat unalignedOffset align + dynSize) align =
      alignToNat (unalignedOffset + dynSize) align := by
  intro dynSize
  rw [alignToNat_add_mul unalignedOffset align k hAlign]
  exact alignToNat_idem (unalignedOffset + dynSize) align hAlign

/-!
## Section 5.1: Negative Canary Theorem — Static Header Alignment Bug on DSTs

Consider `struct Packet<T: ?Sized> { header: u32, payload: T }` where
`headerSize = 4` and `headerAlign = 4`. Suppose `T` is unsized to `dyn Trait`
from a concrete type containing a `u64` (`payloadSize = 8`, `payloadAlign = 8`).
- The true tail field offset uses `vtable.align = 8` (loaded from vtable slot 2
  at byte offset 16): `alignToBV 4 8 = 8`.
- A buggy compiler backend that uses the static `headerAlign = 4` instead of the
  dynamic `vtable.align = 8` computes `alignToBV 4 4 = 4`.
- At base address `base = 0x1000` (which is 8-byte aligned), the buggy tail
  address `0x1004` is **not** 8-byte aligned (`0x1004 % 8 = 4 ≠ 0`), causing an
  unaligned access fault / undefined behavior in Rust's memory model and
  reading the 4 bytes of padding instead of the `u64` payload!
-/

/-- Concrete vtable for a `u64` payload implementing `Trait`:
slot 0 = `drop_in_place` (`0x4000`), slot 1 = `size` (`8`), slot 2 = `align`
(`8`), slot 3 = `method` (`0x4010`). -/
def u64DynVtable : List VtblEntry :=
  [ .metadataDropInPlace 0x4000#64,
    .metadataSize 8#64,
    .metadataAlign 8#64,
    .method 0x4010#64 ]

/-- Concrete memory containing `u64DynVtable` at `vptr = 0x2000`. -/
def sampleVtableMem : WordMem := fun addr =>
  if addr == 0x2000#64 then 0x4000#64
  else if addr == 0x2008#64 then 8#64
  else if addr == 0x2010#64 then 8#64
  else if addr == 0x2018#64 then 0x4010#64
  else 0#64

/-- Buggy DST tail offset calculation that uses `staticHeaderAlign` instead of
loading `vtable.align` from slot 2 of the vtable. -/
def buggyDstTailOffsetStatic (staticHeaderAlign unalignedOffset : BitVec 64) :
    BitVec 64 :=
  alignToBV unalignedOffset staticHeaderAlign

/-- **Negative Canary Theorem:** For `Packet<dyn Trait>` with `header: u32`
(`unalignedOffset = 4`, `staticHeaderAlign = 4`) backed by a `u64` payload
(`vtable.align = 8` at `vptr = 0x2000`):
1. The correct dynamic calculation `dstTailOffsetDyn` yields offset `8`.
2. The buggy static calculation `buggyDstTailOffsetStatic` yields offset `4`.
3. The two offsets disagree (`4 ≠ 8`), and for an 8-byte-aligned base pointer
   `base = 0x1000`, the buggy field address `0x1004` violates the payload's
   8-byte alignment requirement (`(0x1000 + 4) % 8 = 4 ≠ 0`), whereas the
   correct dynamic field address `0x1008` is 8-byte aligned (`(0x1000 + 8) % 8 = 0`).
-/
theorem static_header_align_miscomputes_dst_tail_offset :
    let vptr := 0x2000#64
    let base := 0x1000#64
    let unalignedOffset := 4#64
    let staticHeaderAlign := 4#64
    let payloadAlign := 8#64
    let correctOff := dstTailOffsetDyn sampleVtableMem vptr unalignedOffset
    let buggyOff := buggyDstTailOffsetStatic staticHeaderAlign unalignedOffset
    correctOff = 8#64 ∧
    buggyOff = 4#64 ∧
    buggyOff ≠ correctOff ∧
    (base + correctOff) % payloadAlign = 0#64 ∧
    (base + buggyOff) % payloadAlign ≠ 0#64 := by
  refine ⟨rfl, rfl, by decide, rfl, by decide⟩

/-!
## Section 6: Axiom Footprint Verification (`TrustedBoundary.lean` Compliance)

We verify with `#guard_msgs in #print axioms` that none of our theorems depend
on `Lean.ofReduceBool` or `sorryAx`. Only standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) appear.
-/

/-- info: 'Track5Probe.riscv_uadd_overflow_iff_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms riscv_uadd_overflow_iff_spec

/-- info: 'Track5Probe.cg_clif_usub_overflow_iff_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cg_clif_usub_overflow_iff_spec

/-- info: 'Track5Probe.lowerISLE_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowerISLE_sound

/-- info: 'Track5Probe.checkRewriteTrace_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkRewriteTrace_sound

/-- info: 'Track5Probe.dstSliceAddr_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dstSliceAddr_verified

/-- info: 'Track5Probe.validateSuperblock_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms validateSuperblock_sound

/-- info: 'Track5Probe.coerceDynUpcast_loads_traitVPtr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms coerceDynUpcast_loads_traitVPtr

/-- info: 'Track5Probe.rustc_dst_total_size_optimization' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rustc_dst_total_size_optimization

/-- info: 'Track5Probe.static_header_align_miscomputes_dst_tail_offset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms static_header_align_miscomputes_dst_tail_offset

end Track5Probe
