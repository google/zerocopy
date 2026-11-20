# Capability Noninterference, PAS Confinement, and Coupled Hardware-Software Seam Proofs

## Summary

End-to-end verification of separation microkernels and security monitors decomposes whole-system confidentiality, integrity, and isolation into single-step obligations across **seL4** (`seL4/l4v`, Murray et al. S&P 2013, Sewell et al. ITP 2011), **CertiKOS / Komodo** (`microsoft/komodo`, Ferraiuolo et al. SOSP 2017, Costanzo et al. PLDI 2016), and **Serval** (`uw-unsat/serval-sosp19`, Nelson et al. SOSP 2019), grounded in RISC-V ISA semantics (`opencompl/sail-riscv-lean`). Adapting these designs into modular, `Type 0`, 3-axiom Lean 4 `theory/` libraries under Anneal's Pass 1 boundary (`joshlf/anneal` commit `c131b320eeeb26ef692e5afd5ec8db49ee518613`) establishes five invariants:

1. **Scheduler-Decoupled Intransitive Unwinding:** Murray et al.'s three unwinding laws (`outputConsistent`, `locallyRespects`, `weakStepConsistent`) with an independent `SchedState` projection (`sched_step`) block scheduler channels and reduce whole-trace noninterference to single-step proofs.
2. **PAS Confinement Bridges `locallyRespects` to Framing:** Sewell et al.'s `PAS` invariant (`state_objs_to_policy s ⊆ pasPolicy`) shows domains lacking `Write`/`Control` authority cannot modify observer objects, discharging `locallyRespects` via single-trace framing while preserving `CapRights.attenuate` and `RevokeSelfDelete`.
3. **Out-of-TCB ISA Placement:** Generated Sail models (`LeanRV64D`, `175,711` LOC using `noncomputable section`, `do`, `maxRecDepth 1_000_000`) fail Pass 1 `TrustedBoundary` checks and belong in target crate `Spec/` contracts rather than Anneal's `trusted/` TCB.
4. **`Sv39` PWC & `Zifencei` Ghost Barriers:** Unlike `sail-riscv-lean` (`VmemTlb.lean`, caching leaf/superpage `TLB_Entry` items only and preserving `global` entries on ASID flush), normative RISC-V hardware caches non-leaf directory PTEs (`level > 0`) in page-walk caches and separates I-cache from D-cache. Ghost dirty sets (`BarrierGhostState`) catch missing `sfence.vma(x0, asid)` and `fence.i` barriers statically.
5. **Single-Fetch Oracles & S-Mode SFI Checkers:** Generation-indexed `SharedFetchOracle` enforces single-read bounded copies into private snapshots, while a `List.foldr` SFI checker rejects `SYSTEM` (`0x73`), unguarded `JALR` (`0x67`), reserved register writes, and bad branches in `rfl`.

## Applicability

This synthesis connects five pinned repositories and peer-reviewed specifications for Lean 4 `v4.34.1` Pass 1 `theory/` libraries:

- **`seL4/l4v` (`b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`):** Intransitive noninterference (`proof/infoflow/Noninterference_Base.thy`, `Noninterference.thy`), `PAS` capability confinement (`proof/access-control/Access.thy`), and abstract RISC-V `Sv39` VSpace specs (`spec/abstract/RISCV64/ArchVSpace_A.thy`).
- **`opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`):** Sail-generated `LeanRV64D` ISA semantics (`README.md`, `lakefile.toml`, `LeanRV64D.lean`, `LeanRV64D/VmemTlb.lean`, `LeanRV64D/Vmem.lean`, `LeanRV64D/Step.lean`).
- **`uw-unsat/serval-sosp19` (`175c42660fad84b44e4c9f6f723fd3c9450d65d4`):** Rosette/SMT unwinding harnesses for CertiKOS (`monitors/certikos/verif/ni.rkt`) and Komodo (`monitors/komodo/verif/ni.rkt`).
- **`microsoft/komodo` (`de1865c8bd0d85cdfd9a980ad7131448acfaf136`):** Dafny ARM hardware-software refinement specs (`verified/ARMdef.s.dfy`, `verified/kom_common.s.dfy`, `verified/ptables.s.dfy`).
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Pass 1 syntactic/replay gates (`trusted/audit/TrustedBoundary.lean`, `trusted/lean/foundation-lock.json`), threat model (`THREAT_MODEL.md`, `docs/trust-model.md`), and `Trusted.MirSemantics`.

Cross-corpus scope: compiler pass composition appears in `compcert-sel4-everest-pass-composition-and-proof-maintenance`; ISA scaling appears in `lean-large-isa-and-compiler-semantics-scaling` and `anneal-acceptance-frontier-isa-roadmap-and-verifier-bibliography`; OS/concurrency surveys in `anneal-concurrency-weak-memory-kernels-and-storage-survey`; binary sandboxes in `anneal-backend-codegen-binaries-lifters-and-sandboxes-survey`.

## Findings

### 1. Intransitive Noninterference and Scheduler-Decoupled Rushby/Murray Unwinding (`seL4/l4v` vs. `Serval`)

Basis: source + derived

In `seL4/l4v` (`proof/infoflow/Noninterference_Base.thy`), Murray et al. (CPP 2012 DOI `10.1007/978-3-642-35308-6_12`; IEEE S&P 2013 DOI `10.1109/SP.2013.35`) adapt Rushby's 1992 intransitive unwinding theorem (SRI `CSL-92-02`) to OS kernels with state-dependent domain assignment (`dom : 'e ⇒ 's ⇒ 'd`):

1. **Backward-Recursive `sources` and `ipurge` (`L518–585`):** `sources [] s u = {u}`, while `sources (a # as) s u` adds `dom a s` iff `dom a s ⇝ v` for some future `v ∈ sources as s' u`. `Noninterference` (`L602`) relates traces over `as` vs `ipurge u as {s}`; `Noninfluence` (`L642–647`) adds `Nonleakage` (`L537–541`).
2. **Explicit `schedDomain` (`L539, L703, L800–818`):** Unwinding requires and preserves `s ~schedDomain~ t` (`sched_equiv_preserved` `L799–812`), closing scheduler covert channels (`sources_eq` `L920–946`, `ipurge_eq` `L1024–1027`).
3. **Three Unwinding Laws (`L698–777`):** `output_consistent` (`L698–699`), `integrity_u` (`L715–717`), and `confidentiality_u_weak` (`L744–751`, assuming both `s ~u~ t` and `s ~(dom a s)~ t` when `dom a s ⇝ u`) imply `confidentiality_u` (`L763–777`) and `Noninterference`/`Noninfluence` (`L1191–1213`).
4. **Comparison with `Serval` (`uw-unsat/serval-sosp19`):** `monitors/certikos/verif/ni.rkt` (`L17–50, L102–250`) checks symbolic unwinding (`check-observe-consistency`, `verify-confidentiality`, `verify-integrity`, `buggy-yield`); `monitors/komodo/verif/ni.rkt` (`L41–107`) uses `loweq-pdb` over `PageDb` for cross-enclave integrity.

The `Type 0`, `prelude`-only Pass 1 module below mechanizes Murray et al.'s theorem with zero `Classical.choice`, zero `._unsafe_rec`, and zero external list lemmas:

```lean
prelude
import Init.Core
import Init.Data.List.Basic

namespace AnnealNoninterference

def listAny {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  List.foldr (fun x acc => if p x then true else acc) false xs

theorem listAny_of_mem {α : Type} {p : α → Bool} {a : α} :
    ∀ (xs : List α), a ∈ xs → p a = true → listAny p xs = true
  | [], hMem, _ => by cases hMem
  | x :: tl, hMem, hPa => by
    unfold listAny; dsimp only
    cases hMem with
    | head _ => rw [hPa]; exact rfl
    | tail _ hIn =>
      have hSub := listAny_of_mem tl hIn hPa
      cases hPx : p x with
      | true => exact rfl
      | false => unfold listAny at hSub; exact hSub

structure FlowPolicy (Dom : Type) where
  canFlow      : Dom → Dom → Bool
  canFlow_refl : ∀ d : Dom, canFlow d d = true

/-- Separate scheduler state (`schedOf`) so `sched_step` enforces scheduler independence. -/
structure IflowMachine (St Sc Dom Ev Out : Type) where
  domains     : List Dom
  domains_mem : ∀ d : Dom, d ∈ domains
  policy      : FlowPolicy Dom
  activeDom   : Sc → Dom
  schedOf     : St → Sc
  stepSched   : Sc → Ev → Sc
  step        : St → Ev → St
  output      : St → Ev → Out
  obsEq       : Dom → St → St → Prop
  obsEq_refl  : ∀ d s, obsEq d s s
  obsEq_symm  : ∀ d s1 s2, obsEq d s1 s2 → obsEq d s2 s1
  obsEq_trans : ∀ d s1 s2 s3, obsEq d s1 s2 → obsEq d s2 s3 → obsEq d s1 s3
  sched_step  : ∀ s ev, schedOf (step s ev) = stepSched (schedOf s) ev

def runTrace {S Sc D E O : Type} (M : IflowMachine S Sc D E O) (s0 : S) (evs : List E) : S :=
  List.foldr (fun ev rest s => rest (M.step s ev)) (fun s => s) evs s0

theorem runTrace_cons {S Sc D E O : Type} (M : IflowMachine S Sc D E O)
    (s0 : S) (ev : E) (rest : List E) :
    runTrace M s0 (ev :: rest) = runTrace M (M.step s0 ev) rest := rfl

def inSources {S Sc D E O : Type} (M : IflowMachine S Sc D E O)
    (domEq : D → D → Bool) (sc0 : Sc) (evs : List E) (u d : D) : Bool :=
  List.foldr
    (fun ev rest sc dTgt =>
      let cur := M.activeDom sc; let sc' := M.stepSched sc ev
      if rest sc' dTgt then true
      else domEq dTgt cur && listAny (fun v => rest sc' v && M.policy.canFlow cur v) M.domains)
    (fun _ dTgt => domEq dTgt u) evs sc0 d

theorem inSources_cons {S Sc D E O : Type} (M : IflowMachine S Sc D E O)
    (domEq : D → D → Bool) (sc0 : Sc) (ev : E) (rest : List E) (u d : D) :
    inSources M domEq sc0 (ev :: rest) u d =
      if inSources M domEq (M.stepSched sc0 ev) rest u d then true
      else domEq d (M.activeDom sc0) &&
        listAny (fun v => inSources M domEq (M.stepSched sc0 ev) rest u v &&
          M.policy.canFlow (M.activeDom sc0) v) M.domains := rfl

def agreeOnSources {S Sc D E O : Type} (M : IflowMachine S Sc D E O)
    (domEq : D → D → Bool) (sc : Sc) (evs : List E) (u : D) (s1 s2 : S) : Prop :=
  ∀ d : D, inSources M domEq sc evs u d = true → M.obsEq d s1 s2

structure UnwindingLaws {S Sc D E O : Type} (M : IflowMachine S Sc D E O) : Prop where
  outputConsistent : ∀ s1 s2 ev,
    M.obsEq (M.activeDom (M.schedOf s1)) s1 s2 →
    M.schedOf s1 = M.schedOf s2 → M.output s1 ev = M.output s2 ev
  locallyRespects : ∀ s ev u,
    M.policy.canFlow (M.activeDom (M.schedOf s)) u = false → M.obsEq u s (M.step s ev)
  weakStepConsistent : ∀ s1 s2 ev u,
    M.schedOf s1 = M.schedOf s2 → M.obsEq u s1 s2 →
    M.obsEq (M.activeDom (M.schedOf s1)) s1 s2 →
    M.policy.canFlow (M.activeDom (M.schedOf s1)) u = true →
    M.obsEq u (M.step s1 ev) (M.step s2 ev)

theorem step_preserves_agreeOnSources {S Sc D E O : Type}
    (M : IflowMachine S Sc D E O) (domEq : D → D → Bool) (domEqRefl : ∀ d, domEq d d = true)
    (hUnw : UnwindingLaws M) (ev : E) (rest : List E) (u : D) (s1 s2 : S)
    (hSched : M.schedOf s1 = M.schedOf s2)
    (hAgree : agreeOnSources M domEq (M.schedOf s1) (ev :: rest) u s1 s2) :
    agreeOnSources M domEq (M.schedOf (M.step s1 ev)) rest u (M.step s1 ev) (M.step s2 ev) := by
  intro d hSrcRest; rw [M.sched_step] at hSrcRest
  have hSrcHere : inSources M domEq (M.schedOf s1) (ev :: rest) u d = true := by
    rw [inSources_cons, hSrcRest]; exact rfl
  have hEqD := hAgree d hSrcHere
  cases hFlow : M.policy.canFlow (M.activeDom (M.schedOf s1)) d with
  | false =>
    have h1 := hUnw.locallyRespects s1 ev d hFlow
    have hFl2 : M.policy.canFlow (M.activeDom (M.schedOf s2)) d = false := by rw [← hSched]; exact hFlow
    exact M.obsEq_trans d (M.step s1 ev) s1 (M.step s2 ev)
      (M.obsEq_symm d s1 (M.step s1 ev) h1) (M.obsEq_trans d s1 s2 (M.step s2 ev) hEqD (hUnw.locallyRespects s2 ev d hFl2))
  | true =>
    have hWit : listAny (fun v => inSources M domEq (M.stepSched (M.schedOf s1) ev) rest u v &&
        M.policy.canFlow (M.activeDom (M.schedOf s1)) v) M.domains = true := by
      apply listAny_of_mem M.domains (M.domains_mem d); rw [hSrcRest, hFlow]; exact rfl
    have hSrcCur : inSources M domEq (M.schedOf s1) (ev :: rest) u (M.activeDom (M.schedOf s1)) = true := by
      rw [inSources_cons]
      cases hR : inSources M domEq (M.stepSched (M.schedOf s1) ev) rest u (M.activeDom (M.schedOf s1)) with
      | true => exact rfl
      | false => rw [domEqRefl]; exact hWit
    exact hUnw.weakStepConsistent s1 s2 ev d hSched hEqD (hAgree _ hSrcCur) hFlow

theorem unwinding_implies_intransitive_ni {S Sc D E O : Type}
    (M : IflowMachine S Sc D E O) (domEq : D → D → Bool) (domEqRefl : ∀ d, domEq d d = true)
    (hUnw : UnwindingLaws M) (u : D) :
    ∀ (evs : List E) (s1 s2 : S),
      M.schedOf s1 = M.schedOf s2 →
      agreeOnSources M domEq (M.schedOf s1) evs u s1 s2 →
      M.obsEq u (runTrace M s1 evs) (runTrace M s2 evs)
  | [], s1, s2, _, hAgree =>
    hAgree u (by unfold inSources; dsimp only; exact domEqRefl u)
  | ev :: rest, s1, s2, hSched, hAgree => by
    rw [runTrace_cons, runTrace_cons]
    have hSched' : M.schedOf (M.step s1 ev) = M.schedOf (M.step s2 ev) := by
      rw [M.sched_step, M.sched_step, hSched]
    have hAgree' := step_preserves_agreeOnSources M domEq domEqRefl hUnw ev rest u s1 s2 hSched hAgree
    exact unwinding_implies_intransitive_ni M domEq domEqRefl hUnw u rest
      (M.step s1 ev) (M.step s2 ev) hSched' hAgree'

end AnnealNoninterference
```

Naive `stepConsistent` (omitting `M.obsEq (M.activeDom (M.schedOf s1)) s1 s2`) fails on valid relays `A ⇝ Relay ⇝ B` (`A ⇝ B = false`): `s₁, s₂` may agree on `B` while differing in `Relay`'s buffered payload, diverging once `Relay` forwards to `B`. Because `inSources` includes `Relay` whenever `Relay ⇝ B`, `weakStepConsistent` succeeds cleanly.

### 2. PAS Authority Confinement and Discharging `locallyRespects` via Single-Trace Framing

Basis: source + derived

In `seL4/l4v` (`proof/access-control/Access.thy`; Sewell et al. ITP 2011 DOI `10.1007/978-3-642-22863-7_25`), capability integrity couples a static authority graph (`pasPolicy`, `policy_wellformed` `L63–82`) with `state_objs_to_policy` (`L225–254`), projecting capabilities, TCB blocking state, untyped memory ranges, CDT edges, and VM mappings to edges `(srcAgent, auth, tgtObj)`:
- **`cap_rights_to_auth` & `cap_auth_conferred` (`L107–131`):** Maps `{AllowRead, AllowWrite, AllowGrant, AllowGrantReply}` to `{Receive, SyncSend, Notify, Call, Grant, Reset}` (`AllowGrant` confers `UNIV`; non-endpoint objects confer `Control`).
- **`sbta_cdt` (`L238–243`):** Distinguishes `Control` from `DeleteDerived` across CDT parent-child edges so `Revoke` / `RevokeSelfDelete` clears derived slots without breaking root ownership.
- **Bounded Batch Invariant:** Fixed-capacity frame-zeroing/revocation arenas must enforce `n ≤ cap` or chunked termination so frames `cap .. n - 1` are never silently dropped.

Because `locallyRespects` is a **single-trace** property, `PasConfinement` discharges it via single-execution arena framing rather than 2-trace simulation. The Pass 1 module below verifies `CapRights.attenuate`, `RevokeSelfDelete`, and `locallyRespects_of_pasFrame` using decidable `Nat.beq` with zero `Classical.choice`:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic

namespace AnnealAuthorityPas

structure CapRights where
  allowRead  : Bool
  allowWrite : Bool
  allowGrant : Bool

def CapRights.attenuate (src mask : CapRights) : CapRights :=
  { allowRead  := src.allowRead && mask.allowRead
    allowWrite := src.allowWrite && mask.allowWrite
    allowGrant := src.allowGrant && mask.allowGrant }

structure PasPolicy (Subj : Type) where
  mayRead    : Subj → Subj → Bool
  mayWrite   : Subj → Subj → Bool
  mayGrant   : Subj → Subj → Bool
  write_refl : ∀ s, mayWrite s s = true

structure CapSlot (ObjId : Type) where
  valid  : Bool
  target : ObjId
  rights : CapRights

def slotRespectsPas {Subj ObjId : Type} (pas : PasPolicy Subj)
    (labelOf : ObjId → Subj) (owner : Subj) (slot : CapSlot ObjId) : Prop :=
  slot.valid = true →
    let dst := labelOf slot.target
    (slot.rights.allowRead = true → pas.mayRead owner dst = true) ∧
    (slot.rights.allowWrite = true → pas.mayWrite owner dst = true) ∧
    (slot.rights.allowGrant = true → pas.mayGrant owner dst = true)

theorem attenuate_respectsPas {Subj ObjId : Type} (pas : PasPolicy Subj)
    (labelOf : ObjId → Subj) (owner : Subj) (slot : CapSlot ObjId) (mask : CapRights)
    (hSrc : slotRespectsPas pas labelOf owner slot) :
    slotRespectsPas pas labelOf owner
      { slot with rights := CapRights.attenuate slot.rights mask } := by
  intro hValid
  have h := hSrc hValid
  refine ⟨?_, ?_, ?_⟩
  · intro hR
    cases hSrcR : slot.rights.allowRead with
    | false => dsimp only [CapRights.attenuate] at hR; rw [hSrcR] at hR; cases hR
    | true => exact h.1 hSrcR
  · intro hW
    cases hSrcW : slot.rights.allowWrite with
    | false => dsimp only [CapRights.attenuate] at hW; rw [hSrcW] at hW; cases hW
    | true => exact h.2.1 hSrcW
  · intro hG
    cases hSrcG : slot.rights.allowGrant with
    | false => dsimp only [CapRights.attenuate] at hG; rw [hSrcG] at hG; cases hG
    | true => exact h.2.2 hSrcG

/-- Clearing `valid := false` during `RevokeSelfDelete` preserves `slotRespectsPas`. -/
theorem nullSlot_respectsPas {Subj ObjId : Type} (pas : PasPolicy Subj)
    (labelOf : ObjId → Subj) (owner : Subj) (obj : ObjId) (r : CapRights) :
    slotRespectsPas pas labelOf owner ⟨false, obj, r⟩ := by
  intro h; dsimp only at h; cases h

/-- Single-trace `locallyRespects` bridge using decidable `Nat.beq` (zero `Classical.choice`). -/
theorem locallyRespects_of_pasFrame {State Dom ObjId : Type}
    (canFlow : Dom → Dom → Bool) (labelOf : ObjId → Dom)
    (readObj : State → ObjId → Nat) (obsEq : Dom → State → State → Prop)
    (obsEqOfObjAgree : ∀ u s1 s2,
      (∀ oid, labelOf oid = u → readObj s1 oid = readObj s2 oid) → obsEq u s1 s2)
    (cur u : Dom) (s s' : State) (hNoFlow : canFlow cur u = false)
    (hAuthorizedWrites : ∀ oid, readObj s oid ≠ readObj s' oid →
      canFlow cur (labelOf oid) = true) :
    obsEq u s s' := by
  apply obsEqOfObjAgree u s s'
  intro oid hLbl
  cases hCmp : Nat.beq (readObj s oid) (readObj s' oid) with
  | true => exact Nat.eq_of_beq_eq_true hCmp
  | false =>
    have hNe : readObj s oid ≠ readObj s' oid := by
      intro hEq
      rw [hEq, Nat.beq_refl] at hCmp
      cases hCmp
    have hFl := hAuthorizedWrites oid hNe
    rw [hLbl, hNoFlow] at hFl
    cases hFl

end AnnealAuthorityPas
```

### 3. Coupled `(SoftwareState × MachineState)` Refinement and Out-of-TCB ISA Placement

Basis: source + derived

Inspecting `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`) and `microsoft/komodo` (`de1865c8bd0d85cdfd9a980ad7131448acfaf136`) establishes two architectural rules for hardware-software seams:

1. **Why Sail Models Fail Pass 1 `theory/` / `trusted/` Gates:** `LeanRV64D` (`README.md` L8–10, L101–111) totals `175,711` lines (`4,779` defs, `206` inductives), wraps definitions in `noncomputable section` (`LeanRV64D.lean` L28), depends on `rems-project/lean-sail` (`lakefile.toml` L10–13), sets `maxHeartbeats 1_000_000_000`, `maxRecDepth 1_000_000`, `--tstack=400000` (`lakefile.toml` L3; `LeanRV64D.lean` L27–28), and uses `do` in `SailM`/`SailME` (`Step.lean` L332–441)—all rejected by `TrustedBoundary.lean` (`L442–575`).
2. **Placement in Crate `Spec/` vs. Language TCB `trusted/`:** Under `THREAT_MODEL.md` and `docs/trust-model.md`, `trusted/lean/` (`MirAst`, `MirSemantics`) is the **language-level** TCB validated in Pass 2 against `vendor/lean-miri`. Hardware ISA assumptions (`RV64D`, trap CSR layout) are **target-crate domain assumptions** belonging inside the reviewed crate specification surface (`Spec/`), isolated via Statement-Origin Separation while reusable seam combinators stay in `0-TCB` `theory/`.

In `Komodo` (`verified/ARMdef.s.dfy` L24–62, `verified/kom_common.s.dfy` L55–88) and `LeanRV64D/Step.lean` (`L241–450`), coupled execution alternates between `.user dom` (`userStep` until `trapTriggered` on `ecall`, fault, or interrupt) and `.supervisor` (trap save/restore matching `TrapFrame`, while Rust MIR runs via `Trusted.MirSemantics.Behavior` over `(Sw × TrapFrame)`).

### 4. `Sv39` MMU/TLB/PWC and `Zifencei` Barrier Coherence — Source-vs-Normative Analysis

Basis: normative + source + derived

Comparing three authorities reveals a **source-vs-normative discrepancy** in `Sv39` translation and instruction-fetch caching:

| Source | TLB / Page-Walk Cache Model | `sfence.vma` / Global Entry Handling | `fence.i` / I-Cache Handling |
| :--- | :--- | :--- | :--- |
| **`seL4/l4v`** (`ArchVSpace_A.thy` L85–190) | Functional `pt_walk` over `ptes_of` (`vs_lookup_table` L152–162) | `setVSpaceRoot` (`L94`), `hwASIDFlush` (`L128`), `do_machine_op sfence` (`L143, L189`) | Abstracted in `ArchVSpace_A`; coherent across user step |
| **`sail-riscv-lean`** (`VmemTlb.lean` L246–351, `Vmem.lean` L406–559) | 64-entry `tlb` storing resolved `TLB_Entry` (`add_to_TLB` caches leaf/superpage only) | `flush_TLB_Entry` (`L276–289`): ASID flush checks `ent.asid == a && !ent.global` (`L279`), preserving `global` | Unified memory `fetch ()` (`Step.lean` L336); no dirty I-cache |
| **Normative RISC-V Privileged Spec** (`Sv39`, `SFENCE.VMA`, `Zifencei`; Syeda & Klein JAR 2020 `10.1007/s10817-019-09539-7`) | TLBs AND non-leaf **Page-Walk Caches (PWCs)** may cache intermediate PTEs (`V=1, R=W=X=0`, `level ∈ {1, 2}`) | `sfence.vma(va, asid)` need **not** flush non-leaf PWC entries (`level > 0`); `sfence.vma(x0, asid)` preserves `G=1` globals | Fetches may observe stale I-cache lines until `fence.i` synchronizes I-cache with D-cache |

Two soundness hazards result: (1) unmapping a directory PTE (`unmap_page_table`) followed only by single-VA `sfence.vma(va, asid)` leaves stale non-leaf PWC entries (`sfence.vma(x0, asid)` is required, and `sfence.vma(x0, x0)` for `G=1` globals); (2) installing executable text without `fence.i` exposes stale instructions. Generalizing `Komodo`'s `tlb_consistent : bool` (`ARMdef.s.dfy` L24, L228–229, L1022–1024) into `BarrierGhostState` yields Pass 1 positive and negative barrier theorems:

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace AnnealHwSeamCoherence

structure DirtyPteEntry where
  asid     : Nat
  vaPage   : Nat
  level    : Nat    -- `0` = leaf 4 KiB PTE; `1`/`2` = directory / superpage PTEs
  isGlobal : Bool

structure BarrierGhostState where
  tlbDirty    : List DirtyPteEntry
  icacheDirty : List Nat    -- frames modified without `fence.i`

def listFilter {α : Type} (p : α → Bool) (xs : List α) : List α :=
  List.foldr (fun x acc => if p x then x :: acc else acc) [] xs

theorem listFilter_mem_iff {α : Type} (p : α → Bool) (x : α) :
    ∀ xs : List α, x ∈ listFilter p xs ↔ x ∈ xs ∧ p x = true
  | [] => by constructor <;> intro h <;> first | exact (by unfold listFilter at h; cases h) | cases h.1
  | hd :: tl => by
    unfold listFilter; dsimp only
    have ih := listFilter_mem_iff p x tl
    unfold listFilter at ih
    cases hPhd : p hd with
    | false =>
      constructor
      · intro hIn; have hSub := ih.mp hIn; exact ⟨.tail hd hSub.1, hSub.2⟩
      · intro hP; cases hP.1 with | head _ => rw [hPhd] at hP; cases hP.2 | tail _ hTl => exact ih.mpr ⟨hTl, hP.2⟩
    | true =>
      constructor
      · intro hIn; cases hIn with | head _ => exact ⟨.head tl, hPhd⟩ | tail _ hS => have hP := ih.mp hS; exact ⟨.tail hd hP.1, hP.2⟩
      · intro hP; cases hP.1 with | head _ => exact .head _ | tail _ hTl => exact .tail hd (ih.mpr ⟨hTl, hP.2⟩)

def dirtyKeptAfterSfence (va? asid? : Option Nat) (e : DirtyPteEntry) : Bool :=
  match va?, asid? with
  | none, none     => false
  | none, some a   => e.isGlobal || !Nat.beq e.asid a
  | some v, some a => e.isGlobal || !(Nat.beq e.level 0 && Nat.beq e.asid a && Nat.beq e.vaPage v)
  | some _, none   => !(Nat.beq e.level 0)

def applySfenceVma (va? asid? : Option Nat) (b : BarrierGhostState) : BarrierGhostState :=
  { b with tlbDirty := listFilter (dirtyKeptAfterSfence va? asid?) b.tlbDirty }

def applyFenceI (b : BarrierGhostState) : BarrierGhostState :=
  { b with icacheDirty := [] }

def pteWellFormed (inKernel : Nat → Bool) (u _ w x : Bool) (ppn : Nat) : Bool :=
  !(w && x) && (!u || !inKernel ppn)

/-- Negative canary: single-VA `sfence.vma(va, asid)` misses `level = 1` directory entries. -/
theorem leafSfence_misses_dirPte (v a asid va : Nat) (g : Bool) (b : BarrierGhostState)
    (hMem : DirtyPteEntry.mk asid va 1 g ∈ b.tlbDirty) :
    DirtyPteEntry.mk asid va 1 g ∈ (applySfenceVma (some v) (some a) b).tlbDirty := by
  unfold applySfenceVma; dsimp only
  apply (listFilter_mem_iff (dirtyKeptAfterSfence (some v) (some a)) _ b.tlbDirty).mpr
  refine ⟨hMem, ?_⟩
  unfold dirtyKeptAfterSfence; dsimp only; cases g <;> exact rfl

/-- Positive guarantee: `sfence.vma(x0, a)` clears every non-global entry for ASID `a`. -/
theorem asidSfence_clears_nonGlobal_asid (a : Nat) (b : BarrierGhostState)
    (e : DirtyPteEntry) (hNg : e.isGlobal = false)
    (hMem : e ∈ (applySfenceVma none (some a) b).tlbDirty) :
    e.asid ≠ a := by
  unfold applySfenceVma at hMem; dsimp only at hMem
  have hKept := ((listFilter_mem_iff (dirtyKeptAfterSfence none (some a)) e b.tlbDirty).mp hMem).2
  unfold dirtyKeptAfterSfence at hKept; dsimp only at hKept
  rw [hNg] at hKept
  intro hEq; rw [hEq, Nat.beq_refl] at hKept; cases hKept

end AnnealHwSeamCoherence
```

Supervisor-to-user return requires `b.tlbDirty = [] ∧ b.icacheDirty = []`, ensuring TLB hits and fetches agree with `pteWellFormed`.

### 5. Single-Fetch Shared-Memory TOCTOU Oracles and Domain-Guarded Zero-Copy Loans

Basis: documentation + source + derived

Reading untrusted user rings or DMA buffers risks double-fetch TOCTOU bugs if concurrent writers mutate memory between validation and use (Wang et al., USENIX Security 2017). Modeling shared words via a generation-keyed adversarial oracle `readAt : Nat → Nat → Nat` forces `readOnceSnapshot` to validate `rawLen ≤ maxCap` via `Nat.ble` (`Nat.le_of_ble_eq_true`) and copy `[0 .. rawLen)` once into private `PrivateSnapshot` memory (`allowZeroCopyLoan` permits direct zero-copy loans only when `sender == recv` or `writerQuiescent sender = true`):

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace AnnealSharedFetchOracle

structure SharedFetchOracle where
  readAt : Nat → Nat → Nat   -- `(addr, fetchGen) -> word64`

structure PrivateSnapshot where
  checkedLen : Nat
  payload    : List Nat

def snapshotValid (maxCap : Nat) (s : PrivateSnapshot) : Prop :=
  s.checkedLen ≤ maxCap ∧ s.payload.length = s.checkedLen

def fetchPayloadAux (ora : SharedFetchOracle) (baseAddr : Nat) : Nat → Nat → List Nat :=
  @Nat.rec (fun _ => Nat → List Nat) (fun _ => [])
    (fun _ rec idx => ora.readAt (Nat.add baseAddr idx) 0 :: rec (Nat.add idx 1))

theorem fetchPayloadAux_length (ora : SharedFetchOracle) (baseAddr : Nat) :
    ∀ n idx : Nat, (fetchPayloadAux ora baseAddr n idx).length = n
  | 0, _ => rfl
  | n + 1, idx => by
    have ih := fetchPayloadAux_length ora baseAddr n (Nat.add idx 1)
    change (fetchPayloadAux ora baseAddr n (Nat.add idx 1)).length + 1 = n + 1
    rw [ih]

def optSnapshotAux (ora : SharedFetchOracle) (baseAddr rawLen : Nat) :
    Bool → Option PrivateSnapshot
  | true  => some ⟨rawLen, fetchPayloadAux ora baseAddr rawLen 0⟩
  | false => none

def readOnceSnapshot (ora : SharedFetchOracle) (hdrAddr baseAddr maxCap : Nat) :
    Option PrivateSnapshot :=
  let rawLen := ora.readAt hdrAddr 0
  optSnapshotAux ora baseAddr rawLen (Nat.ble rawLen maxCap)

theorem readOnceSnapshot_valid (ora : SharedFetchOracle) (hdr base maxCap : Nat)
    (snap : PrivateSnapshot) (hOk : readOnceSnapshot ora hdr base maxCap = some snap) :
    snapshotValid maxCap snap := by
  unfold readOnceSnapshot at hOk; dsimp only at hOk
  cases hBle : Nat.ble (ora.readAt hdr 0) maxCap with
  | false => rw [hBle] at hOk; unfold optSnapshotAux at hOk; cases hOk
  | true =>
    rw [hBle] at hOk; unfold optSnapshotAux at hOk
    injection hOk with hEq; subst hEq
    exact ⟨Nat.le_of_ble_eq_true hBle, fetchPayloadAux_length ora base _ 0⟩

def toctouMutatedOracle : SharedFetchOracle where
  readAt _ gen := if Nat.beq gen 0 then 64 else 1024

theorem doubleFetch_unsound_witness :
    toctouMutatedOracle.readAt 0 0 ≤ 256 ∧ ¬ (toctouMutatedOracle.readAt 0 1 ≤ 256) := by
  refine ⟨?_, ?_⟩ <;> decide

def allowZeroCopyLoan {Dom : Type} (domEq : Dom → Dom → Bool)
    (writerQuiescent : Dom → Bool) (sender recv : Dom) : Bool :=
  domEq sender recv || writerQuiescent sender

end AnnealSharedFetchOracle
```

### 6. S-Mode Binary-Extension SFI Certificate Checkers in Pure 3-Axiom `theory/`

Basis: normative + source + derived

In-kernel S-mode extensions require static RISC-V 32-bit binary validation before dispatch: blocking `SYSTEM` (`0x73`: `ECALL`, `SRET`, `SFENCE.VMA`, `CSRR*`), restricting indirect `JALR` (`0x67`) to canonical returns (`jalr x0, 0(x1)` = `0x00008067`), blocking writes (`bits[11:7]`) to reserved `sp`/`gp`/`tp` (`x2`–`x4`), and checking all direct `BRANCH` (`0x63`) / `JAL` (`0x6f`) targets land inside `[0, progLen)` (and strictly forward when `acyclicOnly = true`). Using `List.foldr`, C++ GMP `Nat.land`/`Nat.shiftRight`/`Nat.beq`, and `Int.toNat?`, `checkSfiProgram` runs directly in `rfl`:

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Int.Basic

namespace AnnealSfiCert

def opcodeOf (insn : Nat) : Nat := Nat.land insn 127
def rdOf     (insn : Nat) : Nat := Nat.land (Nat.shiftRight insn 7) 31

def checkInsnMasked (insn : Nat) : Bool :=
  let low2 := Nat.land insn 3
  let op   := opcodeOf insn
  let rd   := rdOf insn
  let rdSafe := !Nat.beq rd 2 && !Nat.beq rd 3 && !Nat.beq rd 4
  let opSafe :=
    if Nat.beq op 115 then false                 -- reject `0x73` SYSTEM
    else if Nat.beq op 103 then Nat.beq insn 32871 -- allow ONLY `0x00008067` (`ret`)
    else
      Nat.beq op 51 || Nat.beq op 19 || Nat.beq op 55 || Nat.beq op 23 ||
      Nat.beq op 3  || Nat.beq op 35 || Nat.beq op 99 || Nat.beq op 111
  Nat.beq low2 3 && rdSafe && opSafe

def checkBranchTarget (acyclicOnly : Bool) (progLen idx : Nat) (insn : Nat)
    (relWordOff : Int) : Bool :=
  let op := opcodeOf insn
  if Nat.beq op 99 || Nat.beq op 111 then
    match Int.toNat? (Int.add (Int.ofNat idx) relWordOff) with
    | none => false
    | some tgt => Nat.blt tgt progLen && (!acyclicOnly || Nat.blt idx tgt)
  else true

def checkSfiProgram (acyclicOnly : Bool) (insns : List (Nat × Int)) : Bool :=
  let len := insns.length
  (List.foldr (fun (p : Nat × Int) acc (i : Nat) =>
      checkInsnMasked p.1 && checkBranchTarget acyclicOnly len i p.1 p.2 && acc (i + 1))
    (fun _ => true) insns) 0

theorem privileged_csr_rejected : checkInsnMasked 0x18029073 = false := rfl

end AnnealSfiCert
```

## Boundaries

- **Direct Pass 1 `theory/` import of `opencompl/sail-riscv-lean` (`unsupported`):** `LeanRV64D` relies on `set_option`, `noncomputable section`, `do`, and `rems-project/lean-sail`, violating `TrustedBoundary.lean` (`L442–575`) and `foundation-lock.json` (51 `Init.*` modules). Sail specs must sit inside crate `Spec/` contracts or outside `theory/`.
- **Microarchitectural timing channels and naive `stepConsistent` (`known not to apply`):** Neither `Noninterference_Base.thy` nor `AnnealNoninterference` models cache-timing or speculative channels unless projected into `obsEq`/`Out`. Naive `stepConsistent` fails on authorized relays, leaf `sfence.vma(va, asid)` leaves `level > 0` PWC entries dirty, ASID flushes keep `G=1` entries active (`VmemTlb.lean` L279), and unquiesced cross-domain reads break TOCTOU freedom.
- **Weak-memory PTW races, H-extension, IOMMU, and live Lean execution (`not examined`):** Concurrent `RVWMO` walks, `hgatp`/`hfence.gvma`, `riscv-iommu`, and live compilation of the five distilled Lean modules were not executed in this turn (`derived` from sources and `TrustedBoundary.lean`).
- **Upstream Sail Lean backend stabilization (`unknown`):** Whether future `rems-project/sail` releases emit executable, `set_option`-free Lean without `noncomputable section` (`README.md` L8–9) is unknown at `51c635c460125ac87955d061fcd902ce03b8011f`.

## Evidence

| Subject / Reference | Inspected Files / Citations | Exact Verified Details |
| :--- | :--- | :--- |
| `seL4/l4v` (`b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`) | `proof/infoflow/Noninterference_Base.thy` L518–777, L800–818, L920–1027, L1191–1213; `Noninterference.thy` L1–96 | `sources`, `ipurge`, `schedDomain` equivalence, `output_consistent`, `integrity_u`, `confidentiality_u_weak` (`weakStepConsistent`), `Noninterference` |
| `seL4/l4v` (`b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`) | `proof/access-control/Access.thy` L63–82, L107–158, L225–254; `spec/abstract/RISCV64/ArchVSpace_A.thy` L85–190 | `policy_wellformed`, `cap_rights_to_auth`, `sbta_cdt`, `DeleteDerived`, `set_vm_root`, `delete_asid`, `unmap_page_table`, `unmap_page` |
| `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`) | `README.md` L1–111; `lakefile.toml` L1–13; `LeanRV64D.lean` L1–40; `VmemTlb.lean` L219–351; `Vmem.lean` L406–559; `Step.lean` L241–450 | `175,711` LOC; `maxRecDepth 1_000_000`; `noncomputable section`; 64-entry `tlb`, `flush_TLB_Entry` preserving `ent.global`, `add_to_TLB` `levelMask` |
| `uw-unsat/serval-sosp19` (`175c42660fad84b44e4c9f6f723fd3c9450d65d4`) | `monitors/certikos/verif/ni.rkt` L17–257; `monitors/komodo/verif/ni.rkt` L41–153 | Symbolic unwinding (`check-observe-consistency`, `verify-integrity`, `buggy-yield`), Komodo `loweq-pdb` |
| `microsoft/komodo` (`de1865c8bd0d85cdfd9a980ad7131448acfaf136`) | `verified/ARMdef.s.dfy` L24, L228–229, L1020–1025; `verified/kom_common.s.dfy` L55–88; `verified/ptables.s.dfy` L1–91 | `tlb_consistent : bool` cleared on `ttbr0`/page-table writes and restored on `TLBIALL`; monitor PTE separation |
| `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) | `THREAT_MODEL.md`; `docs/trust-model.md`; `trusted/audit/TrustedBoundary.lean` L442–575, L1136–1265; `trusted/lean/foundation-lock.json` | Statement-Origin Separation; Pass 1 allowlist excluding `set_option`, `do`, `by_cases`, `._unsafe_rec`; 51 `Init.*` lock |
| Peer-Reviewed Literature & Specs | Murray et al. CPP 2012 (`10.1007/978-3-642-35308-6_12`) & S&P 2013 (`10.1109/SP.2013.35`); Sewell et al. ITP 2011 (`10.1007/978-3-642-22863-7_25`); Rushby 1992 (`CSL-92-02`); Syeda & Klein JAR 2020 (`10.1007/s10817-019-09539-7`); Gu et al. OSDI 2016; Costanzo et al. PLDI 2016 (`10.1145/2908080.2908100`); Ferraiuolo et al. SOSP 2017 (`10.1145/3132747.3132782`); Nelson et al. SOSP 2019 (`10.1145/3341301.3359641`); Armstrong et al. POPL 2019 (`10.1145/3290384`); Wang et al. USENIX Security 2017 | Unwinding theorems, `PAS` confinement, cached-TLB refinement, CertiKOS/Komodo/Serval designs, Sail semantics, TOCTOU taxonomy |

## Revalidation

1. **Diff Upstream Barrier/Unwinding Definitions:** Re-inspect `Noninterference_Base.thy` (`confidentiality_u_weak`, `integrity_u`), `Access.thy` (`state_bits_to_policy`), `ArchVSpace_A.thy` (`unmap_page_table`), and `LeanRV64D/VmemTlb.lean` (`flush_TLB_Entry`, `add_to_TLB`) for any change to global-entry flushing or PWC modeling.
2. **Typecheck and Axiom-Audit All Five Distilled Lean Modules:** Extract `AnnealNoninterference`, `AnnealAuthorityPas`, `AnnealHwSeamCoherence`, `AnnealSharedFetchOracle`, and `AnnealSfiCert` into `/tmp/pass1_ni_seam_test.lean`, append `#print axioms` on `unwinding_implies_intransitive_ni`, `attenuate_respectsPas`, `locallyRespects_of_pasFrame`, `asidSfence_clears_nonGlobal_asid`, `readOnceSnapshot_valid`, and `privileged_csr_rejected`, and run:
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true /tmp/pass1_ni_seam_test.lean
   ```
   Confirm exit `0`, zero `Classical.choice` (`{propext}` or `{}` only), zero `._unsafe_rec`, and zero `sorryAx`.
