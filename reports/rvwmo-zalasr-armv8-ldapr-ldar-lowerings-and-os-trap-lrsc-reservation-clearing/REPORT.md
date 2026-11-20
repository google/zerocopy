# Cross-ISA RC11 Atomic Compilation and Privileged Trap Boundaries: RISC-V RVWMO/Zalasr/Zacas, ARMv8 LDAR/STLR versus LDAPR, PPO Rule 11, and Context-Switch LR/SC Reservation Clearing

## Summary

Soundly compiling C++20 and Rust `RC11` atomics to `RISC-V RVWMO` and `ARMv8-A` (`AArch64`) requires maintaining both user-mode axiomatic ordering invariants (`ppo` and `bob`) across mixed extension ABIs and privileged-mode exclusive-reservation invariants across traps and context switches. Primary-source inspection of `riscv/riscv-isa-manual`, `riscv-non-isa/riscv-elf-psabi-doc`, `riscv/sail-riscv`, `herd/herdtools7`, `llvm/llvm-project`, and `torvalds/linux` establishes five normative invariants:

1. **RISC-V `RV64A` Table A.5/A.6 vs. `psABI` Trailing Fence and `Zalasr` v1.0 (`SB` Interoperability Hazard):** Unprivileged specification Table A.5 (v2.2 numbering; Table A.6 in v20191213+, `mm-explanatory.adoc:1457–1529`) lowered `store(SeqCst)` to `fence rw,w; s{b|h|w|d}` without a trailing fence. When linked against ratified `Zalasr` (`zalasr.adoc:32–136`, lowering `load(SeqCst)` to `l{b|h|w|d}.aq` and `store(SeqCst)` to `s{b|h|w|d}.rl`), a Table A.5/A.6 `store(SeqCst)` followed by `Zalasr` `lw.aq` triggers **zero** RVWMO Preserved Program Order (`ppo`) rules (`rvwmo.adoc:284–290`), permitting Store-Buffering (`SB`) `0/0`. `riscv-atomic.adoc:83–87` and LLVM (`RISCVISelLowering.cpp:30567–30569`) therefore mandate a trailing `fence rw,rw` (`fence rw,w; s*; fence rw,rw`) when `Zalasr` is absent.
2. **Failed `SeqCst` CAS Store-Buffering Hazards (`Zalrsc` `lr.aq` vs. `lr.aqrl` and `Zacas` `amocas.aqrl`):** On `compare_exchange(..., SeqCst, SeqCst)` failure, `Zalrsc` branches forward over `sc.rl` (`RISCVExpandPseudoAtomics.cpp:848–867`; moreover, failed `sc` generates zero RVWMO memory events, `rvwmo.adoc:82`), and `Zacas` (`zacas.adoc:150–152` `norm:Zacas_amocas_mem_op_fail_aq_rl`) **strips `.rl` release semantics on failure regardless of the `rl` bit**. Against Table A.5/A.6 `store(SeqCst)`, both `lr.{w|d}.aq` and bare failed `amocas.{w|d}.aqrl` violate `SB`; ABI-safe codegen requires **`lr.{w|d}.aqrl`** (firing PPO Rule 6 via `.rl`) and **`fence rw,rw; amocas.{w|d}.aqrl`** (`RISCVZacasABIFix.cpp:58–68`, `riscv-atomic.adoc:130, 152–155`).
3. **RVWMO `PPO Rule 11` Syntactic Control Dependency Asymmetry:** `rvwmo.adoc:242–246, 295` (`riscv-defs.cat:55`, `[M]; ctrl; [W]`) orders a load before a program-order-later **store** across a dependent conditional branch (forbidding `LB+ctrl` and ordering `Relaxed` CAS loads before post-branch stores), but **excludes dependent loads** (permitting speculative load hoisting in `MP+ctrl`) and vanishes if compiler passes replace the branch with `Zicond` (`czero.*`) or `Zacas` (`amocas`).
4. **ARMv8-A `STLR`/`LDAR` (`RCsc`) vs. `ARMv8.3` `LDAPR` (`RCpc`) Incompatibility With `SeqCst`:** In the official Arm `.cat` model (`aarch64hwreqs.cat:118–121`), Barrier-Ordered-Before (`bob`) includes `[Exp & W & L]; po; [Exp & R & A]` (`STLR` $\to$ `LDAR`), discharging `RC11` `psc_base` on `SB` without `DMB ISH`. ARMv8.3 `FEAT_LRCPC` `LDAPR` (`Q`) includes `[(Exp & R & A) | (Exp & R & Q)]; po; [Exp & M]` but **omits `[Exp & W & L]; po; [Exp & R & Q]`**, allowing `LDAPR` to reorder ahead of an earlier `STLR` to a distinct address via store-buffer forwarding. LLVM (`AArch64InstrAtomics.td:38–82`) therefore restricts `LDAPR*` strictly to `IsAtomicOrderingAcquire` (`== Acquire`) while keeping `LDAR*` for `SeqCst`, and lowers `fence(Release)` to `DMB ISH` (`0xb`) rather than store-only `DMB ISHST`.
5. **OS Trap and Context-Switch `LR/SC` Reservation Clearing (`sret`/`mret` vs. `ERET`):** Unlike ARMv8 `ERET` (which hardware-clears the PE's local exclusive monitor via `ClearExclusiveLocal`), RISC-V Privileged ISA `norm:xret_clr_lr_resv` (`machine.adoc:2667–2676`) **permits `sret`/`mret` to leave `LR` reservations active** to support debugger single-stepping. Combined with coarse reservation granules (up to 4 KiB physical pages under `supervisor.adoc:1701–1705`) and dangling reservations left by kernel failed-CAS forward branches, omitting an explicit dummy `SC` (`REG_SC x0, a2, PT_EPC(sp)` in Linux `arch/riscv/kernel/entry.S:286–305`) enables **cross-domain `SC` reservation forgery** upon returning to user mode.

## Applicability

These findings govern verified compiler backends, inline assembly primitives, and OS kernel trap/context-switch handlers across the eleven subjects in `REPORT.json`:

- **RISC-V Architecture, psABI, and Formal Sail/Herd Models:** `riscv/riscv-isa-manual` @ `c05f1725f25526dd8463bac6ca75cfcfbee17d05` (`src/unpriv/{rvwmo.adoc, mm-explanatory.adoc, zalrsc.adoc, zaamo.adoc, zalasr.adoc, zacas.adoc}`, `src/priv/{supervisor.adoc, machine.adoc}`), `riscv-non-isa/riscv-elf-psabi-doc` @ `56561cb3e7330fe99a98fd27457229707b2786ae` (`riscv-atomic.adoc`), `riscv/sail-riscv` @ `76f1ce3c184797178864b9869963e8b44465889e` (`model/extensions/A/zalrsc_insts.sail`, `model/sys/{sys_reservation.sail, sys_control.sail}`), and `herd/herdtools7` @ `1ae595498c7af7d9d2f00e29aea328b36663104c` (`herd/libdir/{riscv.cat, riscv-defs.cat, aarch64.cat, aarch64hwreqs.cat}`).
- **ARMv8-A / ARMv9-A Architecture and Compilation Proofs:** Arm DDI 0487 (`ARMv8.0-A` `LDAR`/`STLR`/`LDAXR`/`STLXR`/`ERET`/`CLREX`, `FEAT_LSE` atomics, `FEAT_LRCPC` `LDAPR*`, `FEAT_LRCPC2` `LDAPUR*`/`STLUR*`, `FEAT_LRCPC3`), Pulte et al. (POPL 2018, DOI `10.1145/3158107`), Lahav et al. (PLDI 2017, DOI `10.1145/3062341.3062352`), and Podkopaev, Lahav, & Vafeiadis (POPL 2019, DOI `10.1145/3290382`).
- **Production Compiler and Kernel Implementations:** `llvm/llvm-project` @ `ef02d46bb33d10383f6ba5a5d9a5511416ee790c` (`llvm/lib/Target/RISCV/{RISCVISelLowering.cpp, RISCVInstrInfoA.td, RISCVInstrInfoZalasr.td, RISCVExpandPseudoAtomics.cpp, RISCVZacasABIFix.cpp}` and `llvm/lib/Target/AArch64/{AArch64ISelLowering.cpp, AArch64InstrInfo.td, AArch64InstrAtomics.td}`), `rust-lang/rust` @ `ec65cd52bba13d491ff65c9d218b39753755c84a`, and `torvalds/linux` @ `65e4fd942f72a9dba0e4e257290c4fa1aa756854` (`arch/riscv/kernel/entry.S`).

**Relationship to Existing Corpus Coverage:** Prior packages survey general LLVM atomic lowering (`tier1-atomics-and-fences-instruction-lowering`, `weak-memory-concurrency-models-hardware-mappings-and-optimizations`), x86/AArch64 user-space litmus harnesses (`weak-memory-hardware-litmus-testing-x86-and-aarch64`), and high-level `RC11` compilation tables (`c20-seqcst-fences-release-sequences-thin-air-and-rc11-to-rvwmo-arm-compilation-soundness`). This report provides the **exact ISA-level axiomatic `.cat` and LLVM TableGen/pass mechanics** for `Zalasr`/`Zacas`/`Zalrsc`, `PPO Rule 11`, and `LDAPR` vs. `LDAR`, and couples user-mode `LR/SC` lowering with **privileged trap-return reservation clearing** (`sret` vs. `ERET`).

## Findings

### 1. Normative C++20/Rust `RC11` Lowering Matrix: RISC-V (`RV64A`, `psABI`, `Zalasr`, `Zacas`) and `ARMv8-A`

`Basis: normative + source + derived`

In `riscv-non-isa/riscv-elf-psabi-doc` (`riscv-atomic.adoc:25–48`), historical Unprivileged ISA Manual v2.2 "Table A.5" (renumbered "Table A.6" in 2019+, `mm-explanatory.adoc:1457–1529`) is superseded by the ABI-compatible default mapping (strengthening `store(SeqCst)` with a trailing `fence rw,rw`) so object files link safely with ratified `Zalasr` v1.0 ("Table A.7", `zalasr.adoc:32–136`) and `Zacas` (`zacas.adoc:10–167`):

| Rust / C++20 Construct | `RV64A` Historical Table A.5/A.6 *(ABI-broken w/ `Zalasr`)* | `RV64A` Normative `psABI` (`RISCVISelLowering.cpp`) | `RV64` + `Zalasr` + `Zacas` (`RISCVInstrInfoZalasr.td`) | `ARMv8.0-A` / `v8.1 LSE` + `v8.3 FEAT_LRCPC` (`AArch64InstrAtomics.td`) |
| :--- | :--- | :--- | :--- | :--- |
| **`load(Relaxed)`** | `l{b\|h\|w\|d}` | `l{b\|h\|w\|d}` | `l{b\|h\|w\|d}` | `ldr{b,h,,}` |
| **`load(Acquire)`** | `l{b\|h\|w\|d}; fence r,rw` | `l{b\|h\|w\|d}; fence r,rw` | `l{b\|h\|w\|d}.aq` | `ldar{b,h,,}` *(or v8.3 **`ldapr{b,h,,}`**)* |
| **`load(SeqCst)`** | `fence rw,rw; l*; fence r,rw` | `fence rw,rw; l*; fence r,rw` | **`l{b\|h\|w\|d}.aq`** *(Note 3)* | **`ldar{b,h,,}`** *(**NEVER** `ldapr`!)* |
| **`store(Relaxed)`** | `s{b\|h\|w\|d}` | `s{b\|h\|w\|d}` | `s{b\|h\|w\|d}` | `str{b,h,,}` |
| **`store(Release)`** | `fence rw,w; s{b\|h\|w\|d}` | `fence rw,w; s{b\|h\|w\|d}` | `s{b\|h\|w\|d}.rl` | `stlr{b,h,,}` *(or v8.4 `stlur*`)* |
| **`store(SeqCst)`** | `fence rw,w; s*` *(missing fence!)* | **`fence rw,w; s*; fence rw,rw`** | **`s{b\|h\|w\|d}.rl`** | **`stlr{b,h,,}`** |
| **`fence(Acquire)`** | `fence r,rw` | `fence r,rw` | `fence r,rw` | `dmb ishld` (`0x9`) |
| **`fence(Release)`** | `fence rw,w` | `fence rw,w` | `fence rw,w` | **`dmb ish` (`0xb`)** *(**NEVER** `dmb ishst`!)* |
| **`fence(AcqRel)`** | `fence.tso` | `fence.tso` | `fence.tso` | `dmb ish` (`0xb`) |
| **`fence(SeqCst)`** | `fence rw,rw` | `fence rw,rw` | `fence rw,rw` | `dmb ish` (`0xb`) |
| **`fetch_<op>(SeqCst)`** | `amo<op>.{w\|d}.aqrl` | `amo<op>.{w\|d}.aqrl` | `amo<op>.{w\|d}.aqrl` | `ld<op>al` (`LSE`) or `ldaxr`/`stlxr` |
| **`cas(SeqCst, SeqCst)`** | `1: lr.*.aqrl; bne 2f; sc.*.rl; bnez 1b; 2:` | `1: lr.*.aqrl; bne 2f; sc.*.rl; bnez 1b; 2:` | **`fence rw,rw; amocas.*.aqrl`** *(ABI-safe; bare `amocas.aqrl` is Note 3)* | `casal` (`LSE`) or `1: ldaxr; cmp; b.ne 2f; stlxr; cbnz 1b; 2:` |

In LLVM (`RISCVISelLowering.cpp:30540–30571, 31474–31501`), `shouldInsertFencesForAtomic` returns `false` when `Subtarget.hasStdExtZalasr()` (without `Ztso`), delegating directly to `RISCVInstrInfoZalasr.td:80–115` where both `acquiring_load` and `seq_cst_load` select `LB_AQ`/`LH_AQ`/`LW_AQ`/`LD_AQ` (`.aq`, not `.aqrl`), and both `releasing_store` and `seq_cst_store` select `SB_RL`/`SH_RL`/`SW_RL`/`SD_RL` (`.rl`, not `.aqrl`). When `Zalasr` is absent, `emitLeadingFence` + `emitTrailingFence` emit the full `psABI` fences whenever `Subtarget.enableTrailingSeqCstFence()` is enabled (`L30567`).

---

### 2. RISC-V RVWMO `SeqCst` Store-Buffering Hazards: `Zalasr` Interoperability and Failed CAS (`Zalrsc` vs. `Zacas`)

`Basis: normative + source + execution + derived`

RVWMO (`rvwmo.adoc:284–290`, formalized in `herd/herdtools7` `riscv-defs.cat:46–51`) defines explicit-synchronization Preserved Program Order (`ppo`) between distinct-address operations $a \to_{\text{po}} b$ via five rules:
- **Rule 4 (`r4 = fence`):** An intervening `fence` orders $a$'s access type (`r`/`w`) before $b$'s access type (`r`/`w`).
- **Rule 5 (`r5 = [AQ]; po; [M]`):** $a$ carries an `.aq` acquire annotation.
- **Rule 6 (`r6 = [M]; po; [RL]`):** $b$ carries an `.rl` release annotation.
- **Rule 7 (`r7 = [RCsc]; po; [RCsc]`):** Both $a$ and $b$ carry `RCsc` annotations (which hold on `AMO`/`LR`/`SC` with `.aq`/`.rl`, and on `Zalasr` `l*.aq` and `s*.rl` per `zalasr.adoc:69, 123`: `norm:ldaq_rcsc_semantics` and `norm:sdrl_rcsc_semantics`).
- **Rule 8 (`r8 = rmw`):** $a$ and $b$ are a paired `lr` and **successful** `sc`.

Evaluating Store Buffering (`SB`: Hart 0 writes $x := 1$ (`SeqCst`) then reads $y$ (`SeqCst`); Hart 1 writes $y := 1$ (`SeqCst`) then reads $x$ (`SeqCst`), forbidding $r_0 = 0 \wedge r_1 = 0$) exposes **three distinct ABI traps** whenever a translation unit compiled with historical Table A.5/A.6 (`store(SeqCst) -> fence rw,w; sw x, 1`) is paired with a `SeqCst` load or failed `SeqCst` CAS on $y$:

1. **Trap 1 — Table A.5/A.6 `store(SeqCst)` + `Zalasr` `lw.aq` (`mm-explanatory.adoc:1451–1456`, `riscv-atomic.adoc:28–39, 73, 146–148`):**
   In `fence rw,w; sw x, 1; lw.aq y`, let $a = \texttt{sw x, 1}$ and $b = \texttt{lw.aq y}$:
   - Rule 4 fails: `fence rw,w` precedes $a$; **zero** fence lies between $a$ and $b$.
   - Rule 5 fails: $a$ (`sw`) has no `.aq`.
   - Rule 6 fails: $b$ (`lw.aq`) has `.aq` (`RCsc`), **not `.rl`**.
   - Rule 7 fails: $b$ is `RCsc`, **but $a$ (`sw`) is an ordinary store without `RCsc`**.
   Thus $(a, b) \notin \mathsf{ppo}$, permitting `lw.aq y` to execute before `sw x, 1` becomes globally visible (`SB` returns `0/0`). Conversely, pure `Zalasr` (`sw.rl x, 1; lw.aq y`) satisfies **Rule 7** (`sw.rl` is release-`RCsc` and `lw.aq` is acquire-`RCsc`), and `psABI` (`fence rw,w; sw x, 1; fence rw,rw`) satisfies **Rule 4** against every load lowering.

2. **Trap 2 — Failed `Zalrsc` `SeqCst` CAS Using `lr.aq` Instead of `lr.aqrl` (`riscv-atomic.adoc:129–134`, `RISCVExpandPseudoAtomics.cpp:224–226, 268–270, 848–867`):**
   LLVM expands `PseudoCmpXchg32`/`64` (`RISCVExpandPseudoAtomics.cpp:848–866`) to:
   ```asm
   .loophead:
     lr.w.aqrl dest, (addr)         # getLRForRMW(SequentiallyConsistent) -> LR_W_AQRL
     bne       dest, cmpval, .done  # comparison failure skips sc.w.rl completely!
   .looptail:
     sc.w.rl   scratch, newval, (addr)
     bnez      scratch, .loophead
   .done:
   ```
   When `dest != cmpval` (for example, `y.compare_exchange(1, 2, SeqCst, SeqCst)` when `y == 0`), control jumps directly to `.done` without executing `sc.w.rl` (and even if an `sc` executed and failed, `rvwmo.adoc:82` specifies that failed `sc` produces no memory operation). If `.loophead` used `lr.w.aq` (`riscv-atomic.adoc:133`, Note 3), then after a Table A.5/A.6 `fence rw,w; sw x, 1`, `a = sw` and `b = lr.w.aq` fail Rules 4–7 identically to Trap 1. Using **`lr.w.aqrl`** (`L225`) attaches **`.rl`** directly to the load-reserved instruction, firing **PPO Rule 6 (`[M]; po; [RL]`)** even on the failure branch.

3. **Trap 3 — Failed `Zacas` `amocas.aqrl` Stripping `.rl` (`zacas.adoc:148–152`, `RISCVZacasABIFix.cpp:58–68`):**
   Unlike `lr.w.aqrl`, `Zacas` defines asymmetrical success/failure ordering in `zacas.adoc:150–152` (`norm:Zacas_amocas_mem_op_fail_aq_rl`):
   > *"The memory operation performed by an `amocas.w/d/q`, when not successful, has acquire semantics if `aq` bit is 1 but **does not have release semantics, regardless of `rl`**."*
   Consequently, an unsuccessful `amocas.w.aqrl` retains `.aq` (`RCsc`)—which orders it after `Zalasr` `sw.rl` via Rule 7 and after `psABI` `fence rw,rw` via Rule 4—but **loses `.rl`**, breaking Rule 6 after a legacy Table A.5/A.6 `fence rw,w; sw` (`riscv-atomic.adoc:152–155`, Note 5). LLVM's dedicated pass `RISCVZacasABIFix.cpp:61–68` therefore prepends `fence rw,rw` whenever `I.getFailureOrdering() == AtomicOrdering::SequentiallyConsistent`.

---

### 3. RVWMO `PPO Rule 11` Syntactic Control Dependencies and Branchless Optimization Hazards

`Basis: normative + source + execution + derived`

In `rvwmo.adoc:242–246, 295` (`riscv-defs.cat:53–55`), RVWMO's three syntactic dependency rules are:
- **Rule 9 (`[M]; addr; [M]`):** Syntactic address dependency from load $a$ to load or store $b$.
- **Rule 10 (`[M]; data; [W]`):** Syntactic data dependency from load $a$ to store $b$.
- **Rule 11 (`[M]; ctrl; [W]`):** *$b$ is a store*, and there exists a branch or indirect jump $m$ with $a \to_{\text{po}} m \to_{\text{po}} b$ such that $m$ has a syntactic dependency on $a$.

Three sharp boundaries govern compiler and inline-assembly reliance on `PPO Rule 11`:
1. **Load-to-Store Ordering Only (`LB+ctrl` Forbidden, `MP+ctrl` Allowed):** Because Rule 11 requires $b \in W$, `r0 = x.load(Relaxed); if r0 == 1 { y.store(1, Relaxed); }` enforces `x.load ->_ppo y.store` on RVWMO (and identically on ARMv8 via `dob = ... | ctrl; [Exp & W]`, `aarch64hwreqs.cat:65`), preventing hardware Load-Buffering cycles through conditional branches. Conversely, if $b$ is a **load** (`if y.load(Relaxed) == 1 { r = x.load(Relaxed); }`), Rule 11 **does not apply**: out-of-order cores may speculatively execute `x.load` before resolving the branch on `y`, requiring `.aq`, `fence r,r`, or `ISB`/`IFB-ob` (`aarch64hwreqs.cat:47–48` `ctrl; [IFB]; po` on ARMv8; RVWMO has no `ctrl; fence.i` load barrier and requires `fence r,r`).
2. **Syntactic Fragility Under Compiler Select-Conversion (`Zicond` / `Zacas`):** Rule 11 tracks *machine-level* branch instructions, not source-level `if` expressions. If LLVM converts `if (x.load(Relaxed)) { y = 1; }` or a `Relaxed` `compare_exchange` guard into branchless conditional operations (`czero.eqz`/`czero.nez` under `Zicond` when the store itself becomes unconditional, or `amocas` without a `bne`), the intervening branch $m$ disappears; unless a data/address dependency (Rules 9–10) remains, `ppo` is lost. C++20 and Rust therefore never expose control dependencies as a substitute for `Ordering::Acquire` / `Ordering::Release`.
3. **Successful `sc` Destination Register Dependency (`rvwmo.adoc:250–256`):** Unlike unconditional `sw`/`sd`, a successful `sc` writes `0` to `rd` (`zalrsc.adoc:14`), creating a genuine syntactic control dependency from `sc` to every store after `bnez rd, .loophead`! A `Relaxed` `lr.w; ...; sc.w scratch, ...; bnez scratch, .loop` therefore orders its successful `sc.w` before subsequent **stores** (though *not* subsequent loads!) via Rule 11.

---

### 4. `ARMv8-A` Multicopy-Atomic Lowerings: `STLR`/`LDAR` (`RCsc`) versus `ARMv8.3` `LDAPR` (`RCpc`) and `DMB` Traps

`Basis: normative + source + execution + derived`

Under ARMv8-A's multicopy-atomic model (Pulte et al., POPL 2018; `herd/herdtools7` `aarch64.cat:155–161` `irreflexive ob as external`), explicit synchronization is governed by `bob` (`Barrier-ordered-before`, `aarch64hwreqs.cat:110–121`):

```ocaml
(* herd/herdtools7 @ 1ae595498c7af7d9: herd/libdir/aarch64hwreqs.cat:110-121 *)
let bob =
   [Exp & M | Imp & Tag & R]; po; [dmb.full]; po; [Exp & M | Imp & Tag & R | MMU & FAULT]
 | ...
 | [(Exp & R) \ NoRet | ...]; po; [dmb.ld]; po; [Exp & M | Imp & Tag & R | MMU & FAULT]
 | [Exp & W]; po; [dmb.st]; po; [Exp & W | MMU & FAULT]
 | [range([Exp & R & A]; amo; [Exp & W & L])]; po; [Exp & M | Imp & Tag & R | MMU & FAULT]
 | [Exp & W & L]; po; [Exp & R & A]
 | [(Exp & R & A) | (Exp & R & Q)]; po; [Exp & M | Imp & Tag & R | MMU & FAULT]
 | [Exp & M | Imp & Tag & R]; po; [Exp & W & L]
```

Two exact architectural distinctions control AArch64 `RC11` compilation soundness (Podkopaev et al., POPL 2019, §4):

1. **Why `LDAPR` (`FEAT_LRCPC`, Tag `Q`) Is Sound for `Acquire` Yet Unsound for `SeqCst`:**
   - **ARMv8.0 `LDAR` (Tag `A`, `RCsc`) + `STLR` (Tag `L`):** Line 119 of `aarch64hwreqs.cat` (`[Exp & W & L]; po; [Exp & R & A]`) directly orders any `STLR` before any program-order-later `LDAR`, even to unrelated addresses. On `SB` (`STLR [x], #1; LDAR W0, [y]` $\parallel$ `STLR [y], #1; LDAR W1, [x]`), reading $0$ on both cores yields `fr` (`ca & ext`) edges `LDAR(y) ->_ob STLR(y)` and `LDAR(x) ->_ob STLR(x)`, closing an `ob` cycle `STLR(x) ->_bob LDAR(y) ->_obs STLR(y) ->_bob LDAR(x) ->_obs STLR(x)` forbidden by `irreflexive ob`—**without any `DMB ISH`**.
   - **ARMv8.3 `LDAPR` / v8.4 `LDAPUR` / v8.9 `LDIAPP` (Tag `Q`, `RCpc`):** Line 120 (`[(Exp & R & A) | (Exp & R & Q)]; po; [Exp & M]`) orders `LDAPR` before all subsequent memory accesses (preserving `MP` when paired with `STLR` via `STLR ->_rfe LDAPR ->_bob LDR`), **but `[Exp & W & L]; po; [Exp & R & Q]` is absent from `bob`**. Microarchitecturally, `STLR [x], #1; LDAPR W0, [y]` allows `LDAPR` to issue before `STLR [x]` drains from the core's store buffer (and if `x == y`, `LDAPR` forwards `1` locally from the store buffer while other cores have not yet observed `STLR [x]`, breaking IRIW-like `SeqCst` visibility chains if mixed). On `SB`, `STLR` + `LDAPR` legally produces `W0 == 0 && W1 == 0`, violating `RC11` `psc_base`.
   - **LLVM Enforcement (`AArch64InstrAtomics.td:38–82`):** `acquiring_load` sets `IsAtomicOrderingAcquire = 1` (matching `AtomicOrdering::Acquire` *only*), mapping `Acquire` loads under `Predicates = [HasRCPC]` to `LDAPRB`/`LDAPRH`/`LDAPRW`/`LDAPRX` (`L65–75`), whereas `seq_cst_load` (`IsAtomicOrderingSequentiallyConsistent = 1`) unconditionally selects `LDARB`/`LDARH`/`LDARW`/`LDARX` (`L78, 94`). Moreover, if a translation unit mixes `store(SeqCst) -> STLR` with a subsequent `load(Acquire) -> LDAPR`, C++20 `[atomics.order]` already permits `store(SeqCst)` followed by `load(Acquire)` to reorder (`psc` applies only between `SeqCst` operations); only `load(SeqCst)` itself must remain `LDAR`.
2. **Why `DMB ISHST` Is Unsound for `fence(Release)` (`AArch64InstrAtomics.td:18–19`, `aarch64hwreqs.cat:116–117`):**
   `dmb.st` (`DMB ISHST`, imm `0xa`) contributes only `[Exp & W]; po; [dmb.st]; po; [Exp & W]`, leaving prior **loads** (`[Exp & R]`) unordered before subsequent release writes (breaking `SpinLock::unlock` or `SeqLock` patterns using `load(Relaxed); fence(Release); store(Relaxed)`). LLVM therefore maps `atomic_fence` with `Acquire` (`4`) to `DMB (i32 0x9)` (`DMB ISHLD`, ordering `[R] -> [M]`) and **all** of `Release` (`5`), `AcqRel` (`6`), and `SeqCst` (`7`) to full `DMB (i32 0xb)` (`DMB ISH`, ordering `[M] -> [M]`).

---

### 5. Privileged OS Trap and Context-Switch Boundaries: `LR/SC` Reservation-Set Forgery (`sret`/`mret` vs. `ERET`)

`Basis: normative + source + execution + derived`

User-mode proofs of `Zalrsc` (`lr.{w|d}` / `sc.{w|d}`) and ARMv8 exclusives (`ldxr`/`stxr`) assume a single contiguous thread controls the hart's exclusive monitor. Across OS traps, interrupts, and preemptive context switches, **RISC-V and ARMv8 enforce opposite architectural contracts**:

| Architectural Property | `RISC-V` (`Zalrsc` + Privileged ISA) | `ARMv8-A` (`DDI 0487` Exclusives) |
| :--- | :--- | :--- |
| **State Representation** | Hidden per-hart reservation set (cannot be read/saved via CSRs, `entry.S:287–290`) | Per-PE Local Exclusive Monitor (`Open` / `Exclusive`) + Global Monitor |
| **Permitted Reservation Granule** | Arbitrarily large (`zalrsc.adoc:91–93`); $\le 4\text{ KiB}$ base physical page if paged VM enabled (`supervisor.adoc:1701–1705`, `norm:lr_sc_rsrv_set_page`) | Exclusive reservation granule (`ERG`, 16 B–2 KiB, `CTR_EL0.ERG`) |
| **Exception Return (`sret`/`mret` vs. `ERET`)** | **NOT required to clear reservation!** (`machine.adoc:2667–2676`, `norm:xret_clr_lr_resv`; configurable `invalidate_on_xret` in `sys_reservation.sail:16–17`) | **Hardware-mandated clear:** `ERET` unconditionally executes `ClearExclusiveLocal(ProcessorID())` |
| **Explicit Clear Instruction** | No dedicated `clrex`; **must execute dummy `sc.{w\|d}`** (`zalrsc.adoc:23–24, 137–141`, `zalrsc_insts.sail:76`) | Dedicated barrier-free `CLREX` instruction (used for intra-EL switches) |
| **Constrained Loop Progress** | $\le 16$ sequential `I`/`E`/`Zca`/`Zcb` insts, no loads/stores/FP/mul/div/fences/system/backward branches (`zalrsc.adoc:185–242`) | Implementation-defined constrained unpredictable rules on intervening memory/FP ops |

#### Two Concrete Reservation-Forgery Vectors on RISC-V When Dummy `SC` Is Omitted

In `riscv/riscv-isa-manual` (`src/priv/machine.adoc:2667–2676`), `norm:xret_clr_lr_resv` states:
> *"If the Zalrsc extension is supported, the `xRET` instruction is allowed to clear any outstanding LR address reservation **but is not required to**. Trap handlers should explicitly clear the reservation if required (e.g., by using a dummy SC) before executing the `xRET`. [NOTE: If `xRET` instructions always cleared LR reservations, it would be impossible to single-step through LR/SC sequences using a debugger.]"*

If an OS kernel returns from `handle_exception` via `sret` without executing `sc.{w|d}` (`zalrsc.adoc:23–24`, `norm:sc_reservation_invalidate`: *"Regardless of success or failure, executing an `sc.w` instruction invalidates any reservation held by this hart"*), **two distinct cross-domain hazards** arise (`torvalds/linux` `arch/riscv/kernel/entry.S:286–305`):

1. **Cross-Thread User Preemption Forgery (`User A` $\to$ Kernel $\to$ `User B`):**
   Task A executes `lr.d a0, (s0)` on physical page $P$, then takes a timer interrupt before `sc.d`. The kernel switches `sp`/`satp` to Task B (without executing any `sc` during scheduling) and executes `sret`. Under `norm:lr_sc_rsrv_set_page` (`supervisor.adoc:1701–1705`) and `zalrsc.adoc:105–108` (which permits `sc` to match physical addresses across distinct virtual aliases and up to the entire 4 KiB page—or the entire address space in M-mode/nommu systems!), if Task B executes an unpaired `sc.d` to a shared/CoW/remapped physical granule within $P$ (or resumes at an `sc.d` whose prior `lr.d` had failed/aborted), Task B's `sc.d` **erroneously succeeds**, corrupting memory without a valid atomic read-modify-write!
2. **Kernel Failed-CAS Dangling Reservation Leak (Kernel $\to$ `User`):**
   As documented directly in `arch/riscv/kernel/entry.S:295–302`, kernel C/Rust code compiled with `Zalrsc` implements `cmpxchg` via `lr.d; bne ..., .done; sc.d` (`RISCVExpandPseudoAtomics.cpp:848–856`). Whenever a kernel `cmpxchg` **fails its comparison**, the taken forward branch `bne` skips `sc.d`, **leaving an active kernel `LR` reservation armed on the hart**! On implementations with wide reservation sets (or shared user/kernel physical pages such as `vdso`/futex pages), returning via `sret` leaks that active reservation into user mode unless cleared on trap exit:

```assembly
/* torvalds/linux @ 65e4fd942f72a9dba0e4e257290c4fa1aa756854: arch/riscv/kernel/entry.S:303-321 */
	REG_L  a2, PT_EPC(sp)
	REG_SC x0, a2, PT_EPC(sp)   /* Dummy sc.{w|d} to kernel stack pt_regs unconditionally clears hart reservation */

	csrw CSR_STATUS, a0
	csrw CSR_EPC, a2
	...
	sret
```

Note why `REG_SC x0, a2, PT_EPC(sp)` is safe as well as sufficient: `PT_EPC(sp)` just held `a2` (`sepc`) at `L196, 303`, so if a lingering kernel reservation happened to cover `PT_EPC(sp)` and the dummy `SC` succeeded, writing `a2` back to `PT_EPC(sp)` is idempotent; if it fails (the common case), memory is untouched, `x0` discards the status bit, and `norm:sc_reservation_invalidate` (`zalrsc_insts.sail:76` `cancel_reservation()`) guarantees the hart enters user mode with **zero active reservation**.

## Boundaries

- **ARMv8.3 `LDAPR` (`FEAT_LRCPC`) for `Ordering::SeqCst` Loads and `DMB ISHST` for `fence(Release)`:** **known not to apply** (architecturally unsound: `[L]; po; [Q] ∉ bob` admits `SB` `0/0`, and `DMB ISHST` omits `[R]; po; [dmb.st]; po; [W]`, `aarch64hwreqs.cat:116–121`).
- **Automatic `LR` Reservation Clearing on RISC-V `sret` / `mret`:** **known not to apply** as a portable architectural guarantee (`machine.adoc:2667–2670` `norm:xret_clr_lr_resv`), unlike ARMv8 `ERET`.
- **Floating-Point, Multiply/Divide, Fences, or Extra Memory Ops Inside Constrained `LR/SC` Loops:** **unsupported** for eventual forward progress on RISC-V (`zalrsc.adoc:185–210` `norm:unconstrained_lrsc_no_progress`, `RISCVISelLowering.cpp:30575–30583`).
- **8-Bit and 16-Bit Native `Zaamo`/`Zalrsc` Instructions Without `Zabha`:** **unsupported** in base `RV64A` (`riscv-atomic.adoc:150` Note 4; sub-word RMWs require aligned 32-bit masked `lr.w`/`sc.w` loops, `RISCVISelLowering.cpp:30598–30599`, whereas `Zalasr` supports byte/halfword `lb.aq`/`lh.aq`/`sb.rl`/`sh.rl` natively).
- **Hardware Adoption of Optional `xRET` Reservation Invalidation Across Commercial RISC-V Cores:** Which specific silicon implementations enable `platform.reservation.invalidate_on_xret` (`sys_reservation.sail:17`) vs. retaining reservations across `sret`/`mret` is microarchitecture-dependent and **unknown** without per-SoC RTL/errata inspection; OS kernels must unconditionally emit the dummy `sc`.
- **Device MMIO Ordering (`fence io,io` / `nGnRnE`), Instruction-Cache Shootdowns (`fence.i` / `IC IVAU` + `ISB`), and TLB Maintenance (`sfence.vma` / `TLBI`):** Non-main-memory I/O regions (`rvwmo.adoc:273–274`) and self-modifying code / page-table shootdown barriers were **not examined**.

## Evidence

- **`riscv/riscv-isa-manual` @ `c05f1725f25526dd8463bac6ca75cfcfbee17d05`:** `src/unpriv/rvwmo.adoc` (`L82` failed `sc`, `L242–257` syntactic control dependency & `sc` `rd`, `L267–345` PPO Rules 1–13 & Atomicity Axiom), `src/unpriv/mm-explanatory.adoc` (`L1444–1592` Table A.5/A.6 & hypothetical `Zalasr` Table A.6/A.7), `src/unpriv/zalasr.adoc` (`L20–137` `lb/lh/lw/ld.aq` & `sb/sh/sw/sd.rl` `RCsc` semantics), `src/unpriv/zacas.adoc` (`L146–166` `norm:Zacas_amocas_mem_op_fail_aq_rl`), `src/unpriv/zalrsc.adoc` (`L8–27, 91–150, 183–242` reservation sets, `sc` invalidation, constrained loops), `src/priv/supervisor.adoc` (`L1701–1705` `norm:lr_sc_rsrv_set_page`), `src/priv/machine.adoc` (`L2667–2676` `norm:xret_clr_lr_resv`).
- **`riscv-non-isa/riscv-elf-psabi-doc` @ `56561cb3e7330fe99a98fd27457229707b2786ae`:** `riscv-atomic.adoc` (`L20–156` normative mappings, trailing `SeqCst` store fence, `lr.aqrl`, and `Zacas` Note 5).
- **`riscv/sail-riscv` @ `76f1ce3c184797178864b9869963e8b44465889e`:** `model/extensions/A/zalrsc_insts.sail` (`L32–81` `LOADRES` & `STORECON` `cancel_reservation()`), `model/sys/sys_reservation.sail` (`L9–24` `invalidate_on_xret`), `model/sys/sys_control.sail` (`L575–577`).
- **`herd/herdtools7` @ `1ae595498c7af7d9d2f00e29aea328b36663104c`:** `herd/libdir/riscv.cat` (`L21–28`), `herd/libdir/riscv-defs.cat` (`L31–73` PPO `r1`–`r13`), `herd/libdir/aarch64.cat` (`L148–172`), `herd/libdir/aarch64hwreqs.cat` (`L62–71` `dob`, `L104–121` `aob` and `bob`).
- **`llvm/llvm-project` @ `ef02d46bb33d10383f6ba5a5d9a5511416ee790c`:** `llvm/lib/Target/RISCV/RISCVISelLowering.cpp` (`L30540–30602, 31474–31501`), `RISCVInstrInfoZalasr.td` (`L18–115`), `RISCVInstrInfoA.td` (`L71–85, 428–468`), `RISCVExpandPseudoAtomics.cpp` (`L210–293, 809–916`), `RISCVZacasABIFix.cpp` (`L58–68`), and `llvm/lib/Target/AArch64/AArch64InstrAtomics.td` (`L16–105`).
- **`torvalds/linux` @ `65e4fd942f72a9dba0e4e257290c4fa1aa756854`:** `arch/riscv/kernel/entry.S` (`L252–324` `ret_from_exception` `REG_SC x0, a2, PT_EPC(sp)` before `sret`/`mret`).
- **Literature & Manuals:** Arm DDI 0487 (`ERET` `ClearExclusiveLocal`, `CLREX`, `LDAR`/`STLR`/`LDAPR`); Lahav et al., PLDI 2017 (`10.1145/3062341.3062352`); Pulte et al., POPL 2018 (`10.1145/3158107`); Podkopaev, Lahav, & Vafeiadis, POPL 2019 (`10.1145/3290382`).
- **Local Execution Verification (`2026-11-20`):** Python 3.13 axiomatic and trap-state checker verifying the $3 \times 6$ RVWMO `SB` matrix, `PPO Rule 11` asymmetry, ARMv8 `bob` (`LDAR` vs. `LDAPR` and `DMB ISH` vs. `DMB ISHST`), and RISC-V/ARMv8 context-switch reservation-forgery invariants.

## Revalidation

1. **Upstream Compiler & Kernel Diffs (< 1 minute):**
   - Diff `emitLeadingFence`, `emitTrailingFence`, and `shouldInsertFencesForAtomic` in `llvm/lib/Target/RISCV/RISCVISelLowering.cpp`, `RISCVZacasABIFix.cpp`, and `acquiring_load`/`seq_cst_load` in `llvm/lib/Target/AArch64/AArch64InstrAtomics.td`.
   - Check `ret_from_exception` in `torvalds/linux` (`arch/riscv/kernel/entry.S`) to confirm `REG_SC x0, ..., PT_EPC(sp)` precedes `sret`/`mret`.
2. **Standalone Executable Verification Probe (`python3` stdlib, < 0.1s):**
   Run the following self-contained script to verify (a) the exact 3 unsound RVWMO `SB` combinations across Table A.5/A.6, `psABI`, `Zalasr`, `Zalrsc`, and `Zacas`, (b) `PPO Rule 11` store-only control ordering, (c) ARMv8 `LDAPR` and `DMB ISHST` `bob` omissions, and (d) cross-domain `LR/SC` reservation forgery with vs. without dummy `sc` before `sret`:

```python
#!/usr/bin/env python3
"""Verify RVWMO/Zalasr/Zacas SB matrix, PPO Rule 11, ARMv8 LDAPR bob, and trap LR/SC clearing."""
from dataclasses import dataclass

@dataclass(frozen=True)
class RvOp:
    kind: str
    addr: str = ""
    aq: bool = False
    rl: bool = False
    rcsc: bool = False
    fpred: str = ""
    fsucc: str = ""
    ctrl_dep: bool = False

def rvwmo_ppo(seq: list[RvOp], i: int, j: int) -> bool:
    a, b = seq[i], seq[j]
    ar, aw, br, bw = "R" in a.kind, "W" in a.kind, "R" in b.kind, "W" in b.kind
    for k in range(i + 1, j):
        f = seq[k]
        if f.kind == "F" and ((ar and "r" in f.fpred) or (aw and "w" in f.fpred)) and (
            (br and "r" in f.fsucc) or (bw and "w" in f.fsucc)
        ):
            return True
    return a.aq or b.rl or (a.rcsc and b.rcsc) or (bw and ar and b.ctrl_dep)

stores = {
    "TableA5_A6": [RvOp("F", fpred="rw", fsucc="w"), RvOp("W", addr="x")],
    "psABI": [RvOp("F", fpred="rw", fsucc="w"), RvOp("W", addr="x"), RvOp("F", fpred="rw", fsucc="rw")],
    "Zalasr": [RvOp("W", addr="x", rl=True, rcsc=True)],
}
loads = {
    "TableA5_A6": [RvOp("F", fpred="rw", fsucc="rw"), RvOp("R", addr="y"), RvOp("F", fpred="r", fsucc="rw")],
    "Zalasr_lw_aq": [RvOp("R", addr="y", aq=True, rcsc=True)],
    "Zalrsc_fail_lr_aq": [RvOp("R", addr="y", aq=True, rcsc=True)],
    "Zalrsc_fail_lr_aqrl": [RvOp("R", addr="y", aq=True, rl=True, rcsc=True)],
    "Zacas_fail_bare": [RvOp("R", addr="y", aq=True, rl=False, rcsc=True)],
    "Zacas_ABIFix": [RvOp("F", fpred="rw", fsucc="rw"), RvOp("R", addr="y", aq=True, rl=False, rcsc=True)],
}
unsound = {
    (sn, ln) for sn, ss in stores.items() for ln, ls in loads.items()
    if not rvwmo_ppo(ss + ls, next(i for i, o in enumerate(ss + ls) if o.addr == "x"),
                     next(i for i, o in enumerate(ss + ls) if o.addr == "y"))
}
assert unsound == {
    ("TableA5_A6", "Zalasr_lw_aq"),
    ("TableA5_A6", "Zalrsc_fail_lr_aq"),
    ("TableA5_A6", "Zacas_fail_bare"),
}
assert rvwmo_ppo([RvOp("R", "x"), RvOp("W", "y", ctrl_dep=True)], 0, 1)
assert not rvwmo_ppo([RvOp("R", "x"), RvOp("R", "y", ctrl_dep=True)], 0, 1)

def armv8_bob(a: str, b: str, dmb: str = "") -> bool:
    if dmb == "ISH": return True
    if dmb == "ISHST": return a in ("STR", "STLR") and b in ("STR", "STLR")
    return (a == "STLR" and b == "LDAR") or a in ("LDAR", "LDAPR") or b == "STLR"

assert armv8_bob("STLR", "LDAR") and not armv8_bob("STLR", "LDAPR")
assert not armv8_bob("LDR", "STR", "ISHST") and armv8_bob("LDR", "STR", "ISH")

def trap_forgery(isa: str, dummy_sc: bool, granule: int) -> bool:
    rsrv = 0x8000_1000 & ~(granule - 1)
    if isa == "armv8" or dummy_sc:
        rsrv = -1
    return rsrv == (0x8000_1020 & ~(granule - 1))

assert trap_forgery("riscv", False, 64) and trap_forgery("riscv", False, 4096)
assert not trap_forgery("riscv", True, 4096) and not trap_forgery("armv8", False, 4096)
print("OK")
```
