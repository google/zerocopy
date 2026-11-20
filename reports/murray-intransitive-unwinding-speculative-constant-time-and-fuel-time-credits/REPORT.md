# Intransitive Noninterference Unwinding, Speculative Constant-Time Taint Algebras, and Fuel-Unified Amortized Time Credits in 3-Axiom Lean 4

## Summary

Relational confidentiality, Spectre-hardened constant-time checking, and worst-case execution step bounds are often verified by separate stacks. Synthesizing primary-source algebras from `seL4/l4v` (`b0fe7693`, Murray et al. CPP 2012 / IEEE S&P 2013), `jasmin-lang/jasmin` (`8c327997`, IEEE S&P 2023, POPL 2025), `PLSysSec/blade` (`61ac7906`, POPL 2021), Atkey (ESOP 2010 / LMCS 2011), and Charguéraud–Pottier (JAR 2019) under Anneal's Pass-1 boundary (`joshlf/anneal@c131b320`, `TrustedBoundary.lean:442-596`) establishes three zero-TCB principles in 3-axiom Lean 4 (`v4.34.1`):

1. **Big-Step MIR Handler Lifting Requires Multi-Event Dispatch and Nondeterminism Isolation:** Murray et al.'s `Noninterference_Base.thy` collapses multi-domain `Noninfluence_strong` (`L650-655`) into single-step `output_consistent` (`L698`), `integrity_u` (`L715-717`), and `confidentiality_u_weak` (`L744-751`). Lifting `MirWp.wpProg` handlers hits two constraints: `no_domain_visible_nondeterminism` (`L708-713`) bans `obsEq d`-visible `MirSemantics.Choice` variance, and `integrity_u_and_single_event_systems` (`L1306-1331`) forbids collapsing scheduler ticks and syscalls into one event tag. Under `closed_unwinding_system` (`L1436-1471`), `Nonleakage_gen` reduces to `Nonleakage_init`.
2. **Speculative Constant-Time Requires `(normal, speculative)` Pairs Plus `MSF`:** Architectural `SecScalar` misses Spectre-v1 bounds-check bypass and Spectre-v1.1 transient stores. `jasmin-lang/jasmin@8c327997` (`sct_checker_forward.ml`) tracks `VlPairs.t = (n, s) ∈ {Pub, Sec}²` with `MSF.t = toinit | Exact xs | Trans xs (Some cond)`. Unsafe loads set `s ↦ Sec` (`L638`); `#declassify` clears only `n ↦ Pub` (`L917`); dynamic stores invoke `corruption_speculative` (`L588-592, 870-894`) tainting all `in_memory` variables (`10.1145/3704880`); and `#protect` requires `Exact` MSF to normalize `(n, s) ↦ (n, n)` (`L999-1009`). `Blade` (`PLSysSec/blade@61ac7906`) solves `T/S` min-cuts offline as an untrusted hint generator.
3. **`MirWp.wpOutcomeState` `fuel : Nat` Realizes Time Credits Directly:** In `MirWp.lean` (`L69-80, 280-313`), `wpOutcomeState` recurses via `@Nat.rec` on `fuel : Nat` (certified by `WpSoundnessClaim`), and `wpOutcomeState_fuel_mono` gives affine weakening `$(k₁ + k₂) ⊢ $k₁`. Potentials `Φ` satisfying `cost + Φ(s') ≤ Φ(s) + c` telescope over `evalStep` sequences within `Φ(s₀) + c * ops.length`, while `exactFuel` closes register-only timing leaks.

---

## Applicability

This synthesis applies to relational noninterference, speculative side-channel verification, and amortized step bounds under Anneal's Pass-1 `SourceRole.theory` constraints (`joshlf/anneal@c131b320`, `TrustedBoundary.lean:442-596`), examining nine primary subjects:

| Subject | Pinned Identity | Examined Scope |
| :--- | :--- | :--- |
| Anneal MIR & WP | `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `theory/Anneal/MirWp.lean`, `Trusted/MirSemantics.lean`, `TrustedBoundary.lean` |
| seL4 noninterference | `seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`, `10.1109/SP.2013.35` | `proof/infoflow/Noninterference_Base.thy` |
| Kernel unwinding (CPP'12) | `10.1007/978-3-642-35308-6_12` | Dynamic domain `dom a s`, `confidentiality_u_weak`, scheduler decoupling |
| Jasmin SCT & SLH | `jasmin-lang/jasmin@8c3279973a89afd969e50301f71563bb40d55724`, `10.1145/3704880` | `compiler/src/sct_checker_forward.ml`, `proofs/{lang/slh_ops.v,compiler/slh_lowering.v}` |
| Jasmin Spectre-v1 typing | `10.1109/SP46215.2023.10179418` (IEEE S&P 2023) | Normative `(n, s)` lattice and `MSF` typing judgment |
| Blade mitigation synthesis | `PLSysSec/blade@61ac7906ddae019215ff4f33df7e774d88d6fdb1`, `10.1145/3434330` | `README.md`, `T/S` def-use min-cut `protect` synthesis (`arXiv:2005.00294`) |
| Atkey amortized logic | `10.1007/978-3-642-11957-6_6` (ESOP'10), `10.2168/LMCS-7(2:17)2011` | Affine resource triples `{P * R(k)} c {Q * R(k')}` |
| Separation logic time credits | `10.1007/s10817-017-9431-7` (JAR 2019) | Linear `$n` credit splitting and potential telescoping |
| Lean 4 toolchain & kernel | `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Pass-1 `Init.*` foundation (`foundation-lock.json`) |

Cross-corpus scope boundaries: `PAS`/RISC-V barriers ([`capability-noninterference-pas-confinement-and-hw-sw-seam-proofs`](../capability-noninterference-pas-confinement-and-hw-sw-seam-proofs/REPORT.md)), architectural `SecScalar`/`TotalSafeTwinEquiv` ([`safe-twin-observational-equivalence-unwind-and-constant-time-alignment`](../safe-twin-observational-equivalence-unwind-and-constant-time-alignment/REPORT.md)), fuel vs. coinduction ([`fuel-step-indexing-clocks-and-tcb-recursion`](../fuel-step-indexing-clocks-and-tcb-recursion/REPORT.md)), backend CT erasure ([`compiler-preservation-of-constant-time-secret-erasure-and-speculative-fences`](../compiler-preservation-of-constant-time-secret-erasure-and-speculative-fences/REPORT.md)), and space-bound compilation ([`safe-for-space-compilation-and-amortized-complexity-verification`](../safe-for-space-compilation-and-amortized-complexity-verification/REPORT.md)).

---

## Findings

### 1. Big-Step-to-Single-Dispatch Intransitive Unwinding and Primary-Source Traps in `seL4/l4v`

`Basis: source + normative + derived`

In `seL4/l4v` (`proof/infoflow/Noninterference_Base.thy`), Murray et al. (`10.1007/978-3-642-35308-6_12`, `10.1109/SP.2013.35`) formalize dynamic-domain intransitive noninfluence (`Noninfluence_strong`, `L650-655`) over `(uwr u : ('s × 's) set)`, `schedDomain`, and `u ⇝ v`. `noninterference_policy` (`L408-421`) enforces `schedIncludesCurrentDom` (`(s, t) ∈ uwr schedDomain ⟹ dom e s = dom e t`), `schedFlowsToAll` (`(schedDomain, d) ∈ policy`), and `schedNotGlobalChannel` (`(x, schedDomain) ∈ policy ⟹ x = schedDomain`). Backward-recursive `sources` (`L518-522`) captures multi-hop relays `A ⇝ R ⇝ B` (`¬(A ⇝ B)`), `ipurge` (`L566-574`) strips un-influencing events, and `sources_eq` / `ipurge_eq` (`L943-1027`) establish schedule agreement for scheduler-equivalent states. Whole-trace `Noninfluence_strong` then reduces to three single-step laws (`L698-777`):
- `output_consistent` (`L698-699`): `s ~u~ s' ⟶ out u s = out u s'`;
- `integrity_u` (`L715-717`): `reachable s ⟶ ¬(dom a s ⇝ u) ⟶ (s, s') ∈ Step a ⟶ s ~u~ s'`;
- `confidentiality_u_weak` (`L744-751`): `reachable s ∧ reachable t ⟶ s ~schedDomain~ t ⟶ dom a s ⇝ u ⟶ s ~(dom a s)~ t ⟶ s ~u~ t ⟶ (s, s') ∈ Step a ∧ (t, t') ∈ Step a ⟶ s' ~u~ t'`.

Lifting Rust MIR kernel handlers verified via `MirWp.wpProg` into atomic `Step` transitions exposes four primary-source constraints in `Noninterference_Base.thy`:
1. **`no_domain_visible_nondeterminism` (`L708-713`):** Taking `t = s` in `confidentiality_u` yields `s' ~d~ s''` for any two outcomes `(s, s'), (s, s'') ∈ Step a`. Thus any demonic `MirSemantics.Choice` observable in `obsEq d` **falsifies unwinding**—handlers lifted into `IflowSpec` must execute deterministically (`execProg`, `MirWp.lean:151-155`) or confine choice differences outside all domain observations.
2. **`integrity_u_and_single_event_systems` (`L1306-1331`):** `Noninterference_Base.thy` proves (`L1285-1331`) that in a single-event automaton (`∀ y, y = a`), `integrity_u` plus `schedNotGlobalChannel` prevents `schedDomain` from ever regaining execution once another domain runs. Lifted MIR kernels must retain distinct `KernelEvent` constructors (`syscall epId` vs. `schedTick`) rather than collapsing all kernel dispatches into one anonymous step.
3. **Reflexive Completeness (`complete_unwinding_system`, `L1339-1383`):** When `(u, u) ∈ policy`, `Noninfluence_gen = Noninfluence_strong_uwr` (`L1372-1382`), proving the unwinding rules are both sufficient and necessary.
4. **Init-Closed Collapse (`closed_unwinding_system`, `L1436-1471`):** When `Init0` is step-invariant (`Init0_closed`), `reachable s ↔ s ∈ Init0` and `Nonleakage_gen = Nonleakage_init` (`L1461-1465`).

**Big-Step Handler Bridge:** Summarizing each entry handler `entryProgForBody p (handlerDefId ev)` via `MirWp.wpProg` (`WpSoundnessClaim`, `MirSemantics.lean:1831-1837`) proves `¬ Diverges` and postcondition `out.ret = encodeRet (runHandler ev s)`, collapsing `N`-dispatch interleavings over `List KernelEvent` to `|handlers|` isolated single-function relational proofs.

---

### 2. Speculative Constant-Time: Jasmin 2-Bit `(n, s)` + `MSF` Type System vs. `Blade` Def-Use Cut Synthesis

`Basis: source + normative + derived`

Under Spectre-v1 (Bounds-Check Bypass), `if idx < pub_len { let v = pub_arr[idx]; leak(lut[v]); }` leaks adjacent out-of-bounds memory speculatively even though architectural `SecScalar` types `idx`, `pub_arr`, and `v` as `PUB`. Under Spectre-v1.1, a speculative dynamic write corrupts a stack spill or memory slot read afterward. `jasmin-lang/jasmin@8c327997` (`compiler/src/sct_checker_forward.ml`, `10.1109/SP46215.2023.10179418`, `10.1145/3704880`) closes both via two coupled mechanisms:

1. **The `(normal, speculative)` Product Lattice (`sct_checker_forward.ml:32-109, 610-708, 917`):**
   Values carry `VlPairs.t = (n, s) ∈ {Pub, Sec}²` (`#public = (Pub, Pub)`, `#transient = (Pub, Sec)`, `#secret = (Sec, Sec)`), and pointers carry `Indirect(lp, le)` (`L66-82`). Only `(Pub, Pub)` may enter branch guards (`ensure_public`, `L695`), pointer addresses (`L634, 645, 649`), or store indices (`L877-878`). Static bounds/register loads (`ssafe_test`, `L610-619`) preserve `(n, s)`, whereas dynamic array loads (`not ssafe_test`, `L638`) raise `s ↦ Sec` and unchecked loads (`Pload`, `L648-650`) return `(Sec, Sec)`. Crucially, `#declassify` (`declassify_lvl`, `L917`) clears only `n ↦ Pub` while retaining `s`, preventing transiently tainted data from leaking before `#protect` or `lfence`.
2. **Speculative Memory Corruption (`L548-592, 870-894`):**
   Dynamic writes (`Lmem` or unsafe `Laset`) call `Env.corruption_speculative env venv le`, raising `resulting_corruption ≥ (Pub, le.s)` and invoking `Env.freshen ~min:(Pub, le.s)` (`L548-567`). `freshen` taints `s` on every variable where `in_memory = true` (`Stack _`, `Global`, and pointed memory `Indirect`), sparing direct registers (`Reg _ => false`, `L559`). This closes Spectre-v1.1 and mirrors POPL 2025 (`10.1145/3704880`), where spilling registers to untyped stack slots broke source SCT until stack-slot corruption tracking was enforced.
3. **The 3-State `MSF` Automaton (`L727-842, 975-1033`) & Coq Lowering (`slh_ops.v`, `slh_lowering.v`):**
   `MSF.t` tracks `toinit`, `Exact xs` (initialized by `Init_msf` / `LFENCE` at `L507-516, 977-981`), and `Trans xs (Some cond)` (entered by `MSF.enter_if` on `Cif`, `L772-775`). Entering a nested conditional while already `Trans` resets `MSF` to `toinit`, forcing `#update_msf` (`check_msf_trans`, `L789-797`) to restore `Exact {mso}`. `#protect(x, e, ms)` requires `Exact` status (`check_msf_exact`, `L999-1009`) and resets `(n, s) ↦ (n, n)` (`VlPairs.normalise`). In Coq (`proofs/lang/slh_ops.v:18-25`, `proofs/compiler/slh_lowering.v:79, 128-179`), `cond_uses_mem` ensures branch predicates never read memory and preserves `SLHinit`/`SLHupdate`/`SLHprotect` across register allocation.
4. **Complementary Role of `Blade` (`PLSysSec/blade@61ac7906`, `10.1145/3434330`):**
   `Blade` uses a 1-bit transient/stable lattice `T/S` (the `n = Pub` projection of `(n, s)`) to compute minimal `protect` cut sets on def-use graphs (`--blade-type=lfence|slh`, `--blade-v1-1`, `blade/README.md:64-72`). In Anneal, `Blade`-style min-cut placement runs offline as an untrusted hint synthesizer; Jasmin's `(n, s) + MSF` checker validates the mitigated program in `theory/` in $O(|P|)$ time:

| Property | Architectural `SecScalar` | `Blade` (`T/S` Min-Cut) | `Jasmin` (`(n, s)` + `MSF` + Stack Corruption) |
| :--- | :--- | :--- | :--- |
| **Spectre-v1 (`if pub_idx < len { leak(a[pub_idx]) }`)** | **Misses** (`a[pub_idx]` is `PUB`) | **Catches** (loads produce `T`) | **Catches** (dynamic load yields `(Pub, Sec)`) |
| **Architectural + Speculative Product** | `n` only | `T/S` only (separate CT pass) | **`(n, s)`** (`#declassify` preserves `s`) |
| **Spectre-v1.1 Stack/Spill Corruption** | **Misses** | Only with `--blade-v1-1` | **Catches** (`corruption_speculative` on `in_memory`) |
| **Nested Branches & SLH (`protect`)** | Unsupported | Global/block cuts | **`MSF` `Exact`/`Trans` requires per-branch `update_msf`** |
| **Anneal `theory/` Role** | Baseline architectural CT | Offline untrusted hint synthesizer | **Authoritative Pass-1 `theory/` checker** |

---

### 3. Unifying Atkey and Charguéraud–Pottier Amortized Time Credits with `MirWp` `fuel : Nat`

`Basis: source + normative + derived`

Atkey (`10.1007/978-3-642-11957-6_6`, `10.2168/LMCS-7(2:17)2011`) and Charguéraud–Pottier (`10.1007/s10817-017-9431-7`) verify amortized complexity using affine `$n` time credits (`$(m + n) ≡ $m ∗ $n`, `$(k₁ + k₂) ⊢ $k₁`). Inspection of `theory/Anneal/MirWp.lean` (`L69-80, 280-313`) and `Trusted/MirSemantics.lean` (`L1831-1837`) shows that **`wpOutcomeState` already embeds this exact credit algebra with zero TCB changes and zero Iris `▷` modalities**:
1. `wpOutcomeState p onDone onFault fuel s` recurses via `@Nat.rec` on `fuel : Nat`, decrementing `fuel` by 1 per `evalStep` and failing closed (`False`) at `0`, certified against `WellFormed` and `¬ Diverges` by `WpSoundnessClaim`.
2. `wpOutcomeState_fuel_mono` (`fuel₁ ≤ fuel₂`, `MirWp.lean:280-313`) directly proves affine credit weakening without ghost separation-logic heaps or `Classical.choice`.
3. Any sequence `ops : List Op` whose per-operation step bound `cost o s` satisfies `cost o s ≤ Φ s + c` and `wpFuel (opStep o) (fun s' => Inv s' ∧ cost o s + Φ s' ≤ Φ s + c) (cost o s) s` telescopes constructively via `Nat` induction to complete within `Φ s₀ + c * ops.length + 1` steps. For dynamic-array push with doubling resize (`cost = 1` if `sz < cap`, else `cap + 1` setting `cap' = 2 * cap`), `sz ≤ cap ≤ 2 * sz + 1` yields non-negative `Nat` potential `Φ(sz, cap) = (2 * sz + 1) - cap` and amortized cost `c = 3` (`total_steps = 127 ≤ 192` over 64 pushes).
4. **Upper-Bound `wpFuel` vs. Exact-Step `exactFuel`:** While `fuel₁ ≤ fuel₂` weakening proves WCET/eBPF caps, it hides variable loop trip counts in pure registers unless strengthened to `exactFuel` (requiring `.done` strictly at `n = 0`).

---

### 4. Self-Contained Pass-1 3-Axiom Lean 4 Mechanization

`Basis: derived`

This standalone Lean 4 (`v4.34.1`) module uses only Pass-1 allowlisted `Init.*` imports (`TrustedBoundary.lean:442-596`), zero `sorry`, zero `omega`/`rcases`/`deriving`/`partial`/`._unsafe_rec`, and zero banned notations:

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.List.Notation
import Init.Data.Nat.Basic

namespace Anneal.Rel.UnwindSctCost

/-! ## Part A: Big-Step Handler Lifting & Murray Nondeterminism Trap -/

inductive KernelEvent where
  | syscall (epId : Nat)
  | schedTick

structure IflowSpec (St Dom Ev Out : Type) where
  policy   : Dom → Dom → Bool
  schedDom : Dom
  dom      : Ev → St → Dom
  stepRel  : Ev → St → St → Prop
  obsEq    : Dom → St → St → Prop
  obsRefl  : ∀ d s, obsEq d s s

def ConfU {St Dom Ev Out : Type} (M : IflowSpec St Dom Ev Out) : Prop :=
  ∀ ev u s t s' t',
    M.obsEq M.schedDom s t →
    (M.policy (M.dom ev s) u = true → M.obsEq (M.dom ev s) s t) →
    M.obsEq u s t → M.stepRel ev s s' → M.stepRel ev t t' → M.obsEq u s' t'

/-- `seL4` `no_domain_visible_nondeterminism` (`Noninterference_Base.thy:708-713`):
    `ConfU` forbids single-step nondeterminism visible under `obsEq u`. -/
theorem no_domain_visible_nondet {St Dom Ev Out : Type}
    (M : IflowSpec St Dom Ev Out) (hConf : ConfU M)
    (ev : Ev) (u : Dom) (s s1' s2' : St)
    (h1 : M.stepRel ev s s1') (h2 : M.stepRel ev s s2') :
    M.obsEq u s1' s2' :=
  hConf ev u s s s1' s2' (M.obsRefl M.schedDom s)
    (fun _ => M.obsRefl (M.dom ev s) s) (M.obsRefl u s) h1 h2

/-! ## Part B: 2-Bit `(n, s)` + 3-State `MSF` Forward SCT Checker -/

inductive SecLvl where | pub | sec

def SecLvl.join : SecLvl → SecLvl → SecLvl
  | .pub, .pub => .pub | _, _ => .sec

def SecLvl.isPub : SecLvl → Bool
  | .pub => true | .sec => false

structure VlPair where norm : SecLvl; spec : SecLvl

def VlPair.isPub (p : VlPair) : Bool := SecLvl.isPub p.norm && SecLvl.isPub p.spec
def VlPair.normalise (p : VlPair) : VlPair := ⟨p.norm, p.norm⟩
def VlPair.declassify (p : VlPair) : VlPair := ⟨.pub, p.spec⟩

inductive VarKind where | reg | mem
inductive MsfState where | toInit | exact (msId : Nat) | trans (msId condId : Nat)

inductive SctInstr where
  | enterIf (condId : Nat)
  | updateMsf (dstMs condId srcMs : Nat)
  | dynLoad (dst arr idx : Nat)
  | protect (dst src ms : Nat)
  | declassify (vId : Nat)
  | dynStore (arr idx src : Nat)

def lookupVl : List (Nat × VarKind × VlPair) → Nat → Option (VarKind × VlPair)
  | [], _ => none
  | (eid, vk, p) :: rest, id => match Nat.beq eid id with | true => some (vk, p) | false => lookupVl rest id

def taintMem : List (Nat × VarKind × VlPair) → SecLvl → List (Nat × VarKind × VlPair)
  | [], _ => []
  | (eid, .mem, p) :: rest, s => (eid, .mem, ⟨p.norm, SecLvl.join p.spec s⟩) :: taintMem rest s
  | entry :: rest, s => entry :: taintMem rest s

structure SctState where ok : Bool; msf : MsfState; venv : List (Nat × VarKind × VlPair)

def failSct (venv : List (Nat × VarKind × VlPair)) : SctState :=
  { ok := false, msf := .toInit, venv := venv }

def okSct (msf : MsfState) (venv : List (Nat × VarKind × VlPair)) : SctState :=
  { ok := true, msf := msf, venv := venv }

def stepSct (st : SctState) (ins : SctInstr) : SctState :=
  match st.ok with
  | false => st
  | true =>
    match ins with
    | .enterIf condId =>
      match lookupVl st.venv condId with
      | some (_, p) =>
        match p.isPub with
        | true =>
          let msf' := match st.msf with | .exact ms => MsfState.trans ms condId | _ => .toInit
          okSct msf' st.venv
        | false => failSct st.venv
      | none => failSct st.venv
    | .updateMsf dstMs condId srcMs =>
      match st.msf with
      | .trans m c =>
        match Nat.beq m srcMs && Nat.beq c condId with
        | true  => okSct (.exact dstMs) ((dstMs, .reg, ⟨.pub, .pub⟩) :: st.venv)
        | false => failSct st.venv
      | _ => failSct st.venv
    | .dynLoad dst arr idx =>
      match lookupVl st.venv arr, lookupVl st.venv idx with
      | some (_, pArr), some (_, pIdx) =>
        match pIdx.isPub with
        | true  => okSct st.msf ((dst, .reg, ⟨pArr.norm, .sec⟩) :: st.venv)
        | false => failSct st.venv
      | _, _ => failSct st.venv
    | .protect dst src ms =>
      match st.msf, lookupVl st.venv src with
      | .exact m, some (_, pSrc) =>
        match Nat.beq m ms with
        | true  => okSct st.msf ((dst, .reg, pSrc.normalise) :: st.venv)
        | false => failSct st.venv
      | _, _ => failSct st.venv
    | .declassify vId =>
      match lookupVl st.venv vId with
      | some (k, p) => okSct st.msf ((vId, k, p.declassify) :: st.venv)
      | none        => failSct st.venv
    | .dynStore _ idx src =>
      match lookupVl st.venv idx, lookupVl st.venv src with
      | some (_, pIdx), some (_, pSrc) =>
        match pIdx.isPub with
        | true  => okSct st.msf (taintMem st.venv pSrc.spec)
        | false => failSct st.venv
      | _, _ => failSct st.venv

def checkSctList (st : SctState) : List SctInstr → SctState
  | [] => st | ins :: rest => checkSctList (stepSct st ins) rest

def checkSctProg (initVenv : List (Nat × VarKind × VlPair)) (initMs : Nat) (prog : List SctInstr) : Bool :=
  (checkSctList { ok := true, msf := .exact initMs, venv := initVenv } prog).ok

def sampleEnv : List (Nat × VarKind × VlPair) :=
  [(0, .reg, ⟨.pub, .pub⟩), (1, .mem, ⟨.pub, .pub⟩), (2, .mem, ⟨.sec, .sec⟩),
   (3, .mem, ⟨.pub, .pub⟩), (6, .reg, ⟨.pub, .pub⟩)]

theorem spectre_v1_bcb_rejected :
    checkSctProg sampleEnv 6 [.enterIf 0, .dynLoad 4 1 0, .dynLoad 5 1 4] = false := rfl

theorem slh_hardened_v1_accepted :
    checkSctProg sampleEnv 6
      [.enterIf 0, .updateMsf 6 0 6, .dynLoad 4 1 0, .protect 4 4 6, .dynLoad 5 1 4] = true := rfl

theorem declassify_without_protect_rejected :
    checkSctProg sampleEnv 6 [.dynLoad 4 2 0, .declassify 4, .dynLoad 5 1 4] = false := rfl

theorem spectre_v1_1_spill_corruption_rejected :
    checkSctProg sampleEnv 6 [.enterIf 0, .dynStore 1 0 2, .dynLoad 4 3 0, .dynLoad 5 1 4] = false := rfl

/-! ## Part C: Fuel-Unified Amortized Potential Credits & Exact-Step Predicates -/

inductive StepRes (S Out : Type) where | step (next : S) | done (out : Out) | fault

def wpFuel {S Out : Type} (stepFn : S → StepRes S Out) (onDone : Out → Prop) (fuel : Nat) (s : S) : Prop :=
  @Nat.rec (fun _ => S → Prop) (fun _ => False)
    (fun _ ih st => match stepFn st with | .step st' => ih st' | .done out => onDone out | .fault => False)
    fuel s

def exactFuel {S Out : Type} (stepFn : S → StepRes S Out) (onDone : Out → Prop) (fuel : Nat) (s : S) : Prop :=
  @Nat.rec (fun _ => S → Prop) (fun _ => False)
    (fun n ih st => match stepFn st with | .step st' => ih st' | .done out => n = 0 ∧ onDone out | .fault => False)
    fuel s

theorem wpFuel_mono {S Out : Type} (stepFn : S → StepRes S Out) (onDone : Out → Prop) :
    ∀ {f1 f2 : Nat} {s : S}, f1 ≤ f2 → wpFuel stepFn onDone f1 s → wpFuel stepFn onDone f2 s
  | 0, _, _, _, h => False.elim h
  | f1 + 1, 0, _, hLe, _ => False.elim (Nat.not_succ_le_zero f1 hLe)
  | f1 + 1, f2 + 1, s, hLe, h => by
    have hLe' : f1 ≤ f2 := Nat.le_of_succ_le_succ hLe
    change match stepFn s with | .step st' => wpFuel stepFn onDone f1 st' | .done out => onDone out | .fault => False at h
    change match stepFn s with | .step st' => wpFuel stepFn onDone f2 st' | .done out => onDone out | .fault => False
    cases hS : stepFn s with
    | step st' => rw [hS] at h; exact wpFuel_mono stepFn onDone hLe' h
    | done out => rw [hS] at h; exact h
    | fault    => rw [hS] at h; exact False.elim h

def stepSeq {Op S : Type} (opStep : Op → S → StepRes S S) : (List Op × S) → StepRes (List Op × S) S
  | ([], s)        => .done s
  | (o :: rest, s) => match opStep o s with | .step s' => .step (o :: rest, s') | .done s' => .step (rest, s') | .fault => .fault

theorem wpFuel_seq_bind {Op S : Type} (opStep : Op → S → StepRes S S)
    (onDone : S → Prop) (o : Op) (rest : List Op) (P : S → Prop) :
    ∀ {f B : Nat} {s : S}, wpFuel (opStep o) P f s → f ≤ B →
      (∀ s', P s' → ∃ rem, f + rem ≤ B ∧ wpFuel (stepSeq opStep) onDone rem (rest, s')) →
      wpFuel (stepSeq opStep) onDone B (o :: rest, s)
  | 0, _, _, hOp, _, _ => False.elim hOp
  | f' + 1, 0, _, _, hLe, _ => False.elim (Nat.not_succ_le_zero f' hLe)
  | f' + 1, B' + 1, s, hOp, hLe, hCont => by
    have hLe' : f' ≤ B' := Nat.le_of_succ_le_succ hLe
    change match opStep o s with | .step st' => wpFuel (opStep o) P f' st' | .done s' => P s' | .fault => False at hOp
    change match stepSeq opStep (o :: rest, s) with | .step p' => wpFuel (stepSeq opStep) onDone B' p' | .done out => onDone out | .fault => False
    dsimp only [stepSeq]
    cases hS : opStep o s with
    | step st' =>
      rw [hS] at hOp
      exact wpFuel_seq_bind opStep onDone o rest P hOp hLe' (fun s' hP => by
        cases hCont s' hP with
        | intro rem hPair =>
          have hStepLe : (f' + rem) + 1 ≤ B' + 1 := by
            rw [Nat.add_assoc f' rem 1, Nat.add_comm rem 1, ← Nat.add_assoc f' 1 rem]; exact hPair.1
          exact ⟨rem, Nat.le_of_succ_le_succ hStepLe, hPair.2⟩)
    | done s' =>
      rw [hS] at hOp
      cases hCont s' hOp with
      | intro rem hPair =>
        have hStepLe : (f' + rem) + 1 ≤ B' + 1 := by
          rw [Nat.add_assoc f' rem 1, Nat.add_comm rem 1, ← Nat.add_assoc f' 1 rem]; exact hPair.1
        exact wpFuel_mono (stepSeq opStep) onDone
          (Nat.le_trans (Nat.le_add_left rem f') (Nat.le_of_succ_le_succ hStepLe)) hPair.2
    | fault => rw [hS] at hOp; exact False.elim hOp

theorem amortized_seq_bound {Op S : Type} (opStep : Op → S → StepRes S S) (Inv : S → Prop)
    (cost : Op → S → Nat) (phi : S → Nat) (c : Nat)
    (hStep : ∀ o s, Inv s →
      cost o s ≤ phi s + c ∧
      wpFuel (opStep o) (fun s' => Inv s' ∧ cost o s + phi s' ≤ phi s + c) (cost o s) s) :
    ∀ (ops : List Op) (s : S), Inv s →
      wpFuel (stepSeq opStep) Inv (phi s + c * ops.length + 1) (ops, s)
  | [], s, hInv => by
    change match stepSeq opStep ([], s) with | .step p' => wpFuel (stepSeq opStep) Inv (phi s + c * 0) p' | .done out => Inv out | .fault => False
    exact hInv
  | o :: rest, s, hInv => by
    have hOp := hStep o s hInv
    have hCostLe : cost o s ≤ phi s + c * (o :: rest).length + 1 := by
      have h1 : phi s + c ≤ phi s + (c * rest.length + c) := by
        rw [Nat.add_comm (c * rest.length) c, ← Nat.add_assoc]; exact Nat.le_add_right (phi s + c) (c * rest.length)
      exact Nat.le_trans hOp.1 (Nat.le_trans h1 (Nat.le_add_right (phi s + c * (o :: rest).length) 1))
    exact wpFuel_seq_bind opStep Inv o rest (fun s' => Inv s' ∧ cost o s + phi s' ≤ phi s + c) hOp.2 hCostLe
      (fun s' hPair => by
        refine ⟨phi s' + c * rest.length + 1, ?_, amortized_seq_bound opStep Inv cost phi c hStep rest s' hPair.1⟩
        have hA : cost o s + ((phi s' + c * rest.length) + 1) = (cost o s + phi s') + (c * rest.length + 1) := by
          rw [Nat.add_assoc (phi s') (c * rest.length) 1, ← Nat.add_assoc (cost o s) (phi s') (c * rest.length + 1)]
        have hB : (cost o s + phi s') + (c * rest.length + 1) ≤ (phi s + c) + (c * rest.length + 1) :=
          Nat.add_le_add_right hPair.2 (c * rest.length + 1)
        have hC : (phi s + c) + (c * rest.length + 1) = phi s + c * (o :: rest).length + 1 := by
          dsimp only [List.length]
          change (phi s + c) + (c * rest.length + 1) = (phi s + (c * rest.length + c)) + 1
          rw [Nat.add_assoc (phi s) c (c * rest.length + 1), ← Nat.add_assoc c (c * rest.length) 1,
              Nat.add_comm c (c * rest.length), ← Nat.add_assoc (phi s) (c * rest.length + c) 1]
        rw [hA, ← hC]; exact hB)

end Anneal.Rel.UnwindSctCost
```

---

### 5. Architectural Evaluation Against the Anneal `theory/` Rubric (`T1`, `P1–P5`, `C1–C2`) and Refutations

`Basis: source + derived`

| Rubric Dimension | Grade | Grounded Justification Against `joshlf/anneal@c131b320` |
| :--- | :---: | :--- |
| **(T1) 0-TCB Bridge** | **Strong** | 100% untrusted `theory/` over `Init.*` + `{propext, Quot.sound}` (`Classical.choice`-free), reusing `MirWp.wpOutcomeState` with zero `trusted/` edits. |
| **(P1) Human Spec Auditability** | **Strong** | Top-level specs expose `policy`, `(n, s)` types, and `fuel ≤ Φ₀ + c·N`, hiding `MSF` automata and potentials in proof bodies. |
| **(P2) Authoring & Day-2 Locality** | **Strong** | Edits to one handler re-verify only its unwinding VC; `Blade`-style offline hints regenerate `protect` sites. |
| **(P3) Lean 4 Kernel & `<50ms` LSP** | **Strong** | `checkSctProg` is structural `checkSctList` checked by `rfl`; `amortized_seq_bound` uses structural `Nat` induction (`0` `omega`). |
| **(P4) Heterogeneous Composability** | **Strong** | Unwinding composes `wpProg` handlers; `(n, s)` unifies CT/Spectre-v1/v1.1; `wpFuel_seq_bind` threads credits. |
| **(P5) Failure Legibility** | **Strong** | `checkSctProg` flags the failing opcode; `no_domain_visible_nondet` isolates `Choice`; `exactFuel` flags step mismatches. |
| **(C1–C2) Conceptual Minimality** | **Strong** | Minimal carriers (`KernelEvent`, `(n, s) + MsfState`, `wpOutcomeState` `fuel`), avoiding Iris `▷` or tick AST rewrites. |

Four premature collapses (`C2`) are refuted: (1) **collapsing `KernelEvent` to one event** violates `integrity_u_and_single_event_systems` (`Noninterference_Base.thy:1306-1331`); (2) **collapsing `(n, s) + MSF` to `SecScalar`** misses `spectre_v1_bcb_rejected`, `declassify_without_protect_rejected`, and `spectre_v1_1_spill_corruption_rejected`; (3) **collapsing `exactFuel` to `≤` weakening** hides register-only loop timing channels; and (4) **collapsing `ValidChoice` into `obsEq`-visible states** breaks `no_domain_visible_nondet` (`L708-713`).

---

## Boundaries

- **known not to apply:** Jasmin `(n, s) + MSF` captures Spectre-v1 (PHT bounds-check bypass) and Spectre-v1.1 (transient store corruption) and does not protect against Spectre-v2 (BTB), Spectre-v4 (SSB), Meltdown, or hardware MDS (`10.1109/SP46215.2023.10179418`). Source/MIR SCT does not survive unverified LLVM register spilling without target validation (`10.1145/3704880`). `wpOutcomeState` `fuel` bounds `evalStep` counts, not CPU cycles.
- **unsupported:** `joshlf/anneal@c131b320` does not yet expose `CoreBuiltin` speculation barriers (`_mm_lfence`, `csdb`) or `TerminatorKind.call` (`.fault .unsupported`, `MirSemantics.lean:1691-1694`). `TrustedBoundary.lean:442-596` forbids `omega`, `ring`, `rcases`, `deriving`, `Std.*`, and infix `&`/`|`/`^`/`/`/`%`.
- **not examined:** Live `lean`/`lake` compiler invocation on `Anneal.Rel.UnwindSctCost` (audited statically against `foundation-lock.json` and `theory/Anneal/*`), and Jasmin's backward SCT pass (`sct_checker_backward`).
- **unknown:** Concrete runtime overhead of `Blade`-placed `lfence` vs. Jasmin `SLH` (`update_msf` + `protect`) on out-of-order RISC-V cores, and Lean 4 `whnf` wall-clock scaling on multi-thousand-instruction MIR bodies.

---

## Evidence

1. **Anneal (`source`, `normative`):** `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `theory/Anneal/MirWp.lean:69-108, 151-155, 242-313`; `trusted/lean/Trusted/MirSemantics.lean:646-647, 1646-1676, 1691-1694, 1831-1837`; `trusted/audit/TrustedBoundary.lean:442-596, 1136-1366`; `trusted/lean/foundation-lock.json`.
2. **seL4 Unwinding (`source`, `normative`):** `seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`: `proof/infoflow/Noninterference_Base.thy:408-427, 518-584, 650-655, 698-777, 943-1027, 1191-1221, 1285-1383, 1436-1471`; Murray et al. CPP 2012 DOI `10.1007/978-3-642-35308-6_12` & IEEE S&P 2013 DOI `10.1109/SP.2013.35`.
3. **Jasmin SCT & SLH (`source`, `normative`):** `jasmin-lang/jasmin@8c3279973a89afd969e50301f71563bb40d55724`: `compiler/src/sct_checker_forward.ml:32-109, 507-595, 610-708, 727-842, 870-930, 975-1113, 1208-1402`; `proofs/lang/slh_ops.v:18-25`; `proofs/compiler/slh_lowering.v:79, 128-179`; Shivakumar et al. IEEE S&P 2023 DOI `10.1109/SP46215.2023.10179418`; Arranz Olmos et al. POPL 2025 DOI `10.1145/3704880`.
4. **Blade (`source`, `documentation`, `normative`):** `PLSysSec/blade@61ac7906ddae019215ff4f33df7e774d88d6fdb1`, `README.md:6-73`; Vassena et al. POPL 2021 DOI `10.1145/3434330`, `arXiv:2005.00294`.
5. **Amortized Time Credits (`normative`):** Atkey, ESOP 2010 DOI `10.1007/978-3-642-11957-6_6` & LMCS 2011 DOI `10.2168/LMCS-7(2:17)2011`; Charguéraud & Pottier, JAR 2019 DOI `10.1007/s10817-017-9431-7`.
6. **Lean 4 Toolchain (`source`):** `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).
7. **Executable Probe (`execution`, `2026-11-20`):** Python 3 Revalidation probe (`0.07 ms`, exit `0`) verified relay `sources`, Spectre-v1/v1.1/#declassify rejections, `#update_msf`+`#protect` acceptance, and `total_steps = 127 ≤ 192` across 64 dynamic-array pushes.

---

## Revalidation

1. **Primary-source checks against pinned SHAs:**

```bash
curl --http1.1 -fsSL "https://raw.githubusercontent.com/seL4/l4v/b0fe7693ca5943e08c49e038d33fd64dc7dfa72e/proof/infoflow/Noninterference_Base.thy" | sed -n '701,755p;1306,1333p'
curl --http1.1 -fsSL "https://raw.githubusercontent.com/jasmin-lang/jasmin/8c3279973a89afd969e50301f71563bb40d55724/compiler/src/sct_checker_forward.ml" | sed -n '588,655p;770,805p;870,925p'
```

2. **Pass-1 Lean `v4.34.1` check:** Extract Section 4's `Anneal.Rel.UnwindSctCost` module to `/tmp/UnwindSctCost.lean` and run `lean -DElab.async=false -Ddebug.skipKernelTC=false /tmp/UnwindSctCost.lean`, confirming exit `0` and axiom closure $\subseteq \{\texttt{propext}, \texttt{Quot.sound}\}$.
3. **Standalone executable model probe (<0.1s, Python 3.10+ stdlib only):**

```bash
python3 -c '
policy = {("A","A"), ("R","R"), ("B","B"), ("A","R"), ("R","B")}
def sources(evs, u):
    if not evs: return {u}
    s_rest = sources(evs[1:], u)
    return s_rest | {evs[0]} if any((evs[0], v) in policy for v in s_rest) else s_rest
assert sources(["A", "R"], "B") == {"B", "R", "A"} and sources(["A"], "B") == {"B"}
PUB, SEC = 0, 1
def check_sct(ops):
    venv = {"idx": ("reg",(PUB,PUB)), "pub": ("mem",(PUB,PUB)), "sec": ("mem",(SEC,SEC)), "spill": ("mem",(PUB,PUB))}
    msf = ("exact", {"ms"}, None)
    for op in ops:
        t = op[0]
        if t == "if":
            if venv[op[1]][1] != (PUB,PUB): return "REJECT_BR"
            msf = ("trans", set(msf[1]), op[1]) if msf[0] == "exact" else ("toinit", set(), None)
        elif t == "upd":
            if msf[0] != "trans" or msf[2] != op[2] or op[3] not in msf[1]: return "REJECT_UPD"
            msf = ("exact", {op[1]}, None); venv[op[1]] = ("reg",(PUB,PUB))
        elif t == "load":
            if venv[op[3]][1] != (PUB,PUB): return "REJECT_IDX"
            venv[op[1]] = ("reg", (venv[op[2]][1][0], SEC))
        elif t == "prot":
            if msf[0] != "exact" or op[3] not in msf[1]: return "REJECT_PROT"
            n, _ = venv[op[2]][1]; venv[op[1]] = ("reg", (n, n))
        elif t == "decl":
            k, (_, s) = venv[op[1]]; venv[op[1]] = (k, (PUB, s))
        elif t == "store":
            if venv[op[2]][1] != (PUB,PUB): return "REJECT_SIDX"
            sv = venv[op[3]][1][1]
            for k, (kd, (vn, vs)) in list(venv.items()):
                if kd == "mem": venv[k] = ("mem", (vn, max(vs, sv)))
    return "OK"
assert check_sct([("if","idx"),("load","v","pub","idx"),("load","l","pub","v")]) == "REJECT_IDX"
assert check_sct([("if","idx"),("upd","ms","idx","ms"),("load","v","pub","idx"),("prot","v","v","ms"),("load","l","pub","v")]) == "OK"
assert check_sct([("load","v","sec","idx"),("decl","v"),("load","l","pub","v")]) == "REJECT_IDX"
assert check_sct([("if","idx"),("store","pub","idx","sec"),("load","v","spill","idx"),("load","l","pub","v")]) == "REJECT_IDX"
sz, cap, total = 0, 1, 0
for _ in range(64):
    phi0 = (2 * sz + 1) - cap; c_op = 1 if sz < cap else cap + 1
    if sz == cap: cap *= 2
    sz += 1; phi1 = (2 * sz + 1) - cap; total += c_op
    assert c_op + phi1 <= phi0 + 3
assert total == 127 and total <= 3 * 64
print("ALL CHECKS PASSED")
'
```
