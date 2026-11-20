# C++20/Rust Weak-Memory Atomics: P0982R1 Release Sequences, Split-View Fences, SeqCst Total Order, Thin-Air Prevention, Torn Reads, and RC11-to-Hardware Compilation Soundness

## Summary

Formalizing Rust atomics (`core::sync::atomic`) and compiling them soundly to `x86-TSO`, `ARMv8` (`AArch64`), and `RISC-V RVWMO` requires resolving sharp divergences across C++11, `RC11` (Lahav et al., PLDI 2017), `Promising Semantics 2.0` (Lee et al., PLDI 2020), C++20 (`P0982R1` and `P0668R5`), Miri (`rust-lang/miri`), and processor psABI specifications. Primary-source inspection across fourteen repositories, standards, and Coq mechanizations establishes six results:

1. **Three-Era Release-Sequence Narrowing (`C++11` vs. `RC11`/`Promising` vs. `C++20 P0982R1` & Miri):**
   - *C++11 (`[intro.races]` §1.10p7):* Defined release sequences as maximal `mo`-contiguous chains of same-thread stores and any-thread RMWs; an intervening third-thread `store(Relaxed)` broke synchronization even for subsequent same-thread stores.
   - *`RC11` (`qladevez/rc11` `rc11.v:29–30`) and `Promising 2.0` (`snu-sf/promising2-coq` `TView.v:198–209`):* Defined $\mathsf{rs} \triangleq [W] \cdot (\mathsf{sb} \cap {=_{\text{loc}}})^? \cdot [W] \cdot (\mathsf{rf} \cdot \mathsf{rmw})^*$, retaining same-thread `Relaxed` stores via per-location `rel : Loc → View` while rejecting third-thread non-RMW stores.
   - *C++20 `P0982R1` (`[intro.races]` p5) and Rust (`miri/src/concurrency/data_race.rs:7–10, 603–651`):* **Deleted $(\mathsf{sb} \cap {=_{\text{loc}}})^?$ completely**, restricting release sequences strictly to $\mathsf{rs}_{\text{C++20}} \triangleq [W] \cdot (\mathsf{rf} \cdot \mathsf{rmw})^*$ (the initial release write plus contiguous RMW chains). Every non-RMW `store(Relaxed)`—by a third thread *or* the **same thread**—overwrites `sync_vector := fence_release`, making unmodified `ORC11`/`Promising` `rel : Loc → View` **unsound** for Rust verification.
2. **Split-View Operational Semantics for Standalone Fences (`cur`, `acq`, `frel`, `sc`):** Dropping `rel : Loc → View` leaves three per-thread views $(V_{\text{cur}}, V_{\text{acq}}, V_{\text{frel}})$ plus global $V_{\text{sc}}$. `fence(Acquire)` sets $V_{\text{cur}} \leftarrow V_{\text{cur}} \sqcup V_{\text{acq}}$; `fence(Release)` sets $V_{\text{frel}} \leftarrow V_{\text{cur}}$; `fence(AcqRel)` applies both; and `fence(SeqCst)` enforces `RC11` `psc_fence` (`[F_sc] · (hb ⊔ hb · eco · hb) · [F_sc]`, `rc11.v:242–243`), which is strictly weaker than Miri's global-RMW `last_sc_fence` (`data_race.rs:1859–1873`).
3. **`SeqCst` Partial-SC (`psc`) Litmus Separation:** `RC11`'s `acyclic (psc_base ⊔ psc_fence)` (`rc11.v:232–249`, adopted in C++20 `P0668R5`) repairs C11's unsound total order $S$, forbidding `SB` (`0/0`) and `IRIW` when all participating accesses/fences are `SeqCst`, while permitting `IRIW` under `Release`/`Acquire`—even though `x86-TSO`, `ARMv8`, and `RVWMO` hardware forbid `IRIW` due to *other-multi-copy atomicity*.
4. **Thin-Air (`LB`) Prevention (`RC11` vs. `Promising 2.0`):** `RC11` enforces `acyclic (sb ⊔ rf)` (`rc11.v:442–443`), avoiding speculative execution in proofs while forbidding independent `LB` ($r_0 = r_1 = 1$) and `Relaxed` load-to-store reordering. `Promising 2.0` (`Thread.v:73–105, 202–210`) admits independent `LB` and `Relaxed` load-store reordering via capped-memory (`Memory.cap`) promise certification while fixing `Promising 1.0`'s global register-promotion bug.
5. **Access-Based Atomics, Mixed-Size UB, and Torn-Read Soundness (`r[undefined.race]`):** Rust permits unsynchronized `atomic.load(Relaxed)` + non-atomic reads (`atomic.rs:38–42, 78–84`), but treats unsynchronized conflicting mixed-size atomics and racy `ptr::read_volatile` as immediate UB (`data_race.rs:526–545, 1143–1172`). Sound optimistic readers (`SeqLock<T>`) must read uniform-width `Relaxed` atomics into `[MaybeUninit<usize>; K]` before `fence(Acquire)` revalidation.
6. **Hardware Compilation Soundness (`RC11 → x86-TSO, ARMv8, RISC-V RVWMO`):** Soundness ($\mathsf{Beh}_{\text{ISA}}(\llbracket P \rrbracket) \subseteq \mathsf{Beh}_{\text{RC11}}(P)$) hinges on four backend invariants: (a) on `ARMv8`, `STLR`/`LDAR` satisfies `psc_base`, whereas ARMv8.3 `LDAPR` is unsound for `load(SeqCst)` and `DMB ISHST` is unsound for `fence(Release)` (requires `DMB ISH`); (b) on `RISC-V RVWMO`, ISA Manual "Table A.6" (`store_sc -> fence rw,w; sw`) **breaks `SB` when linked with `Zalasr` (`lw.aq`)** unless strengthened per `riscv-elf-psabi-doc` (`riscv-atomic.adoc:83–87`) with trailing `fence rw,rw` (`fence rw,w; s{b|h|w|d}; fence rw,rw` or `amoswap.rl`); (c) `LR/SC(SeqCst)` requires `lr.{w|d}.aqrl` (`L130`); and (d) `amocas` with `SeqCst` failure requires leading `fence rw,rw` (`L152–155`).

## Applicability

These findings govern operational MIR/LLVM concurrency semantics, `unsafe` Rust verification, and verified code generation across the fourteen subjects in `REPORT.json`:

- **Rust Specifications, Miri, and MiniRust:** `rust-lang/rust` @ `ec65cd52bba13d491ff65c9d218b39753755c84a` (`library/core/src/sync/atomic.rs`), `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`src/behavior-considered-undefined.md`, `src/memory-model.md`), `rust-lang/miri` @ `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3` (`src/concurrency/{data_race.rs, weak_memory.rs}`), and `minirust/minirust` @ `063d784186d3252bee242217f218223205c0b568` (`spec/mem/concurrent.md`).
- **Coq Weak-Memory Models:** `qladevez/rc11` @ `fad08ae4c6f41c4268e11140e551b5c42ce07224` (`rc11.v`), `snu-sf/promising-coq` @ `fd9796ede251a2edf0ebf8c938443a30d5eadee9`, and `snu-sf/promising2-coq` @ `6b70a57d10666ec66bfa96b7801dd870f9054da9` (`src/lang/{TView.v, Thread.v}`).
- **ISA Manuals and Standards:** `riscv/riscv-isa-manual` @ `c05f1725f25526dd8463bac6ca75cfcfbee17d05` (`src/unpriv/{rvwmo.adoc, mm-explanatory.adoc, zalasr.adoc}`), `riscv-non-isa/riscv-elf-psabi-doc` @ `56561cb3e7330fe99a98fd27457229707b2786ae` (`riscv-atomic.adoc`), WG21 `P0982R1`, Lahav et al. PLDI 2017 (`10.1145/3062341.3062352`), Kang et al. POPL 2017 (`10.1145/3009837.3009850`), Lee et al. PLDI 2020 (`10.1145/3385412.3386010`), and Pulte et al. POPL 2018 (`10.1145/3158107`).

**Prior Corpus Coverage:** Companion package `owicki-gries-fsl-gps-cosmo-and-first-order-view-logics-for-weak-memory-rust` covers weak-memory program logics (`OGRA` through `iRC11`/`Cosmo`), and `rc11-gps-fsl-timestamp-view-pcms-and-miri-store-buffer-completeness-gaps` proves Miri's 128-entry `StoreBuffer` completeness gaps. Earlier packages (`weak-memory-concurrency-models-hardware-mappings-and-optimizations`, `tier1-atomics-and-fences-instruction-lowering`, `rust-atomics-weak-memory-and-aliasing-operational-models`) survey LLVM atomic lowering broadly; this package establishes exact formal semantics and cross-model proofs for `P0982R1`, split-view fences, `psc` litmus boundaries, `RC11` vs. `Promising 2.0`, mixed-size/torn-read UB, and `x86-TSO`/`ARMv8`/`RVWMO`+`Zalasr` compilation soundness.

## Findings

### 1. C++20 `P0982R1` Release-Sequence Narrowing vs. C++11, `RC11`, and `Promising 2.0`

`Basis: normative + source + execution + derived`

| Specification / Model | Release Sequence $\mathsf{rs}(w_{\text{rel}})$ | Same-Thread `store(Rlx)` | Third-Thread `store(Rlx)` | Contiguous Any-Thread RMW Chain | Per-Thread Release State |
| :--- | :--- | :---: | :---: | :---: | :--- |
| **C++11** (`[intro.races]` §1.10p7) | Maximal `mo`-contiguous chain of (same-thread writes $\lor$ RMWs) | Extends *unless* 3rd-thread `mo` write intervened | Breaks $\mathsf{rs}$ | Extends $\mathsf{rs}$ | Per-thread write-seq map (`tsan11`) |
| **`RC11`** (`rc11.v:29–30`) & **`Promising 2.0`** (`TView.v:198–209`) | $[W] \cdot (\mathsf{sb} \cap {=_{\text{loc}}})^? \cdot [W] \cdot [\sqsupseteq \mathsf{Rlx}] \cdot (\mathsf{rf} \cdot \mathsf{rmw})^*$ | **Always** extends $\mathsf{rs}$ | Fails $(\mathsf{rf} \cdot \mathsf{rmw})^*$ (breaks $\mathsf{rs}$) | Extends $\mathsf{rs}$ | `rel : Loc → View` + `frel : View` |
| **C++20 (`P0982R1`) & Rust / Miri** (`data_race.rs:7–10, 603–651`) | $[W] \cdot (\mathsf{rf} \cdot \mathsf{rmw})^*$ (`mo`-contiguous RMW chain only) | **Breaks $\mathsf{rs}$** | **Breaks $\mathsf{rs}$** | **Extends $\mathsf{rs}$** (`fetch_*`, `swap`, `CAS` ok) | Scalar `frel : View` only |

`qladevez/rc11` (`rc11.v:29–30`) and `snu-sf/promising2-coq` (`TView.v:198–209`) both preserve pre-2019 same-thread write extension (`V' := rel[loc] ⊔ Vra`):
```coq
(* qladevez/rc11 @ fad08ae4c6f4: rc11.v:29-30, 88-89 *)
Definition rs := [W] ⋅ (res_eq_loc (sb ex)) ? ⋅ [W] ⋅ [Mse Rlx] ⋅ ((rf ex) ⋅ (rmw ex)) ^*.
Definition sw := [Mse Rel] ⋅ ([F] ⋅ (sb ex)) ? ⋅ rs ⋅ (rf ex) ⋅ [R] ⋅ [Mse Rlx] ⋅ ((sb ex) ⋅ [F]) ? ⋅ [Mse Acq].
```
WG21 **`P0982R1`** (*Weaken Release Sequences*, adopted into ISO C++20 `[intro.races]` p5) removed same-thread non-RMW writes because work-stealing/fiber migration across OS threads silently invalidated "same-thread" assumptions. Rust adopts C++20 `[intro.races]` (`atomic.rs:27–28`), and Miri (`src/concurrency/data_race.rs:7–10, 611–618, 631–650`) implements `P0982R1` by overwriting `atomic.sync_vector.clone_from(&thread_clocks.fence_release)` on `store_relaxed`, while joining `sync_vector.join(&clock)` on `rmw_release` and `sync_vector.join(&fence_release)` on `rmw_relaxed` (failed `compare_exchange` performs no write, `data_race.rs:950–957`).

**Polarity Trap:** On `DATA = 42; X.store(1, Release); X.store(2, Relaxed)` $\parallel$ `if X.load(Acquire) == 2 { read(DATA) }`, `RC11` and `Promising 2.0` prove `read(DATA)` race-free, whereas C++20/`P0982R1` and Miri flag **immediate `DataRace` UB**. Deductive Rust models must omit per-location `rel : Loc → View`.

---

### 2. Split-View Operational Semantics for Standalone Fences and `SeqCst`

`Basis: normative + source + derived`

Under `P0982R1`, standalone fences (`atomic.rs:4814–4825`, where `fence(Relaxed)` panics at `L4822`) act on three per-thread views $(V_{\text{cur}}, V_{\text{acq}}, V_{\text{frel}})$ ($V_{\text{frel}} \sqsubseteq V_{\text{cur}} \sqsubseteq V_{\text{acq}}$) plus global $V_{\text{sc}}$ (`TView.v:168–225`, `data_race.rs:154–194, 556–651, 1843–1884`):

| Operation (`Ordering`) | Coherence Guard | Emitted $V_{\text{msg}}$ | Post-Step Thread Views $(V'_{\text{cur}}, V'_{\text{acq}}, V'_{\text{frel}})$ & Global $V'_{\text{sc}}$ |
| :--- | :--- | :--- | :--- |
| **`load(Relaxed)`** $(\ell, v, t, V_m)$ | $t \ge V_{\text{cur}}(\ell)$ | — | $V'_{\text{cur}} = V_{\text{cur}}[\ell \sqcup t]$, $\; V'_{\text{acq}} = V_{\text{acq}} \sqcup V_m[\ell \sqcup t]$, $\; V'_{\text{frel}} = V_{\text{frel}}$ |
| **`load(Acquire / SeqCst)`** | $t \ge V_{\text{cur}}(\ell)$ (+ SC bound) | — | $V'_{\text{cur}} = V_{\text{cur}} \sqcup V_m[\ell \sqcup t]$, $\; V'_{\text{acq}} = V_{\text{acq}} \sqcup V_m[\ell \sqcup t]$, $\; V'_{\text{frel}} = V_{\text{frel}}$ |
| **`store(Relaxed)`** $(\ell, v, t)$ | $t > V_{\text{cur}}(\ell)$, $t \notin \mathsf{dom}(M_\ell)$ | $V_{\text{frel}}[\ell \mapsto t]$ | $V'_{\text{cur}} = V_{\text{cur}}[\ell \mapsto t]$, $\; V'_{\text{acq}} = V_{\text{acq}}[\ell \mapsto t]$, $\; V'_{\text{frel}} = V_{\text{frel}}$ |
| **`store(Release / SeqCst)`** | $t > V_{\text{cur}}(\ell)$ (+ SC bound) | $V_{\text{cur}}[\ell \mapsto t]$ | $V'_{\text{cur}} = V_{\text{cur}}[\ell \mapsto t]$, $\; V'_{\text{acq}} = V_{\text{acq}}[\ell \mapsto t]$, $\; V'_{\text{frel}} = V_{\text{frel}}$ |
| **`rmw(ord)`** $(\ell, t_0, V_0) \to t_1$ | $t_0 \ge V_{\text{cur}}(\ell)$, $\mathsf{adj}_{M_\ell}(t_0, t_1)$ | $V_0 \sqcup V_{\text{w}}(\text{ord})$ | Read half updates $(V_{\text{cur}}, V_{\text{acq}})$; write half emits $V_0 \sqcup (V_{\text{cur}} \text{ if } \mathsf{Rel} \sqsubseteq \text{ord else } V_{\text{frel}})$ |
| **`fence(Acquire)`** | — | — | $V'_{\text{cur}} = V_{\text{cur}} \sqcup V_{\text{acq}}$, $\; V'_{\text{acq}} = V_{\text{acq}}$, $\; V'_{\text{frel}} = V_{\text{frel}}$ |
| **`fence(Release)`** | — | — | $V'_{\text{cur}} = V_{\text{cur}}$, $\; V'_{\text{acq}} = V_{\text{acq}}$, $\; V'_{\text{frel}} = V_{\text{cur}}$ |
| **`fence(AcqRel)`** | — | — | $V'_{\text{cur}} = V_{\text{cur}} \sqcup V_{\text{acq}}$, $\; V'_{\text{acq}} = V_{\text{acq}}$, $\; V'_{\text{frel}} = V_{\text{cur}} \sqcup V_{\text{acq}}$ |
| **`fence(SeqCst)`** (`ORC11`) | — | — | $V'_{\text{sc}} = V_{\text{sc}} \sqcup V_{\text{acq}}$, $\; V'_{\text{cur}} = V'_{\text{acq}} = V'_{\text{frel}} = V'_{\text{sc}}$ |

- **Placement Asymmetry:** `fence(Release)` must *precede* `store(Relaxed)` (so $V_{\text{msg}} = V_{\text{frel}}$ captures prior writes), whereas `fence(Acquire)` must *follow* `load(Relaxed)` (promoting $V_{\text{acq}}$ into $V_{\text{cur}}$). `compiler_fence(ord)` (`atomic.rs:4899–4910`) emits zero hardware instructions and synchronizes only with same-core signal/interrupt handlers.
- **Miri `last_sc_fence` Over-Synchronization (`data_race.rs:1859–1873`, `weak_memory.rs:25–27`):** Operational $V'_{\text{sc}} = V_{\text{sc}} \sqcup V_{\text{acq}}; V'_{\text{cur}} = V'_{\text{sc}}$ (and Miri's global-RMW `last_sc_fence`) creates direct happens-before between naked `fence(SeqCst)` pairs even without shared atomic accesses, whereas declarative `RC11` (`psc_fence := [F_sc] · (hb ⊔ hb · eco · hb) · [F_sc]`, `rc11.v:242–243`) orders `F_sc` pairs *only* across an intervening `hb` or `eco` edge.

---

### 3. `SeqCst` Partial-SC (`psc`) and Canonical Litmus Separation

`Basis: normative + source + derived`

C++11's single total order $S$ over `SeqCst` events broke PowerPC and ARMv8 compilation when `SeqCst` accesses mixed with `SeqCst` fences (`Lahav et al., PLDI 2017`, §3). `RC11` (`rc11.v:134–136, 232–249`, adopted into C++20 `P0668R5`; see `weak_memory.rs:14–21` for C++20's minor `SC`-load coherence tightening) enforces `acyclic (psc_base ⊔ psc_fence)` over $\mathsf{scb} \triangleq \mathsf{sb} \cup (\mathsf{sb}_{\neq\text{loc}} \cdot \mathsf{hb} \cdot \mathsf{sb}_{\neq\text{loc}}) \cup \mathsf{hb}_{=\text{loc}} \cup \mathsf{mo} \cup \mathsf{rb}$:

| Litmus Test ($x = y = 0$) | Weak Outcome | `Rlx` / `RA` (`RC11`) | Mixed `SC` + `RA` / `F(AcqRel)` | All-`SC` or `F(SeqCst)` (`RC11`) | `x86-TSO` / `ARMv8` / `RVWMO` Hardware |
| :--- | :--- | :---: | :---: | :---: | :--- |
| **`MP`** ($W(x,1); W(y,1) \parallel R(y)=1; R(x)=0$) | $1, 0$ | Allowed (`Rlx`); **Forbidden** (`RA` / `F_rel`+`F_acq`) | Forbidden if $y$ is `Rel`+`Acq` | **Forbidden** (`sw ⊆ hb`) | Forbidden on `x86-TSO`; requires `STLR`/`LDAR` or `fence` on ARMv8/RVWMO |
| **`SB`** ($W(x,1); R(y)=0 \parallel W(y,1); R(x)=0$) | $0, 0$ | **Allowed** (even under `Rel`+`Acq`!) | **Allowed** under `F(AcqRel)` (`fence.tso`) or `W(SC)`+`R(Acq)` | **Forbidden** (`psc_base` via `rb`, or `psc_fence`) | Allowed under TSO/RA; forbidden only via `XCHG`/`MFENCE`, `STLR`+`LDAR`, or `fence rw,rw` |
| **`IRIW`** ($W(x,1) \parallel W(y,1) \parallel R_x=1;R_y=0 \parallel R_y=1;R_x=0$) | $1,0 \;\wedge\; 1,0$ | **Allowed** under `W(Rel)` + `R(Acq)`! | Allowed if a reader lacks `SC` / `F(SC)` | **Forbidden** (`psc_base` / `psc_fence`) | **Forbidden even under `RA`** on `x86-TSO`, `ARMv8`, `RVWMO` (*multi-copy atomic*), allowed on POWER |
| **`2+2W`** ($W(x,1); W(y,2) \parallel W(y,1); W(x,2)$) | $x=1 \wedge y=1$ final | **Allowed** under `Rlx` and `Rel` | Allowed under `F(AcqRel)` | **Forbidden** (`All-SC` / `F(SC)`) | Forbidden on `x86-TSO`; allowed on ARMv8/RVWMO `STR`/`sw`, forbidden on `STLR`/`fence rw,rw` |

**MIR Portability Trap:** Although `x86-TSO`, `ARMv8` (Pulte et al., POPL 2018), and `RVWMO` (`mm-explanatory.adoc:1621–1630`) are *other-multi-copy atomic* and never exhibit `IRIW` under `Release`/`Acquire` on silicon, portable C++20/`RC11` MIR permits `IRIW` under `RA` (realizable via compiler thread-inlining); multi-observer transitivity proofs must require `SeqCst`.

---

### 4. Out-of-Thin-Air (`LB`) Prevention: `RC11` vs. `Promising Semantics 2.0`

`Basis: normative + source + derived`

On Load-Buffering (`r0 = x.load(Rlx); y.store(e1(r0), Rlx) || r1 = y.load(Rlx); x.store(e2(r1), Rlx)`, initial $x = y = 0$), dependent `LB+deps` ($e_i(v) = v$) must forbid $r_0 = r_1 = 42$ (which forges values/provenance out of thin air), whereas independent `LB` ($e_i(\_) = 1$) is observable on ARMv8 (`LDR; STR`) and RVWMO (`lw; sw`) and under compiler `Relaxed` load-store reordering:

- **`RC11` (`rc11.v:442–443`):** Enforces `acyclic ((sb ex) ⊔ (rf ex))`, forbidding *all* $(\mathsf{sb} \cup \mathsf{rf})^+$ cycles including independent `LB`. This keeps operational verification free of speculative lookahead and proves DRF-SC (`rc11.v:691–713`, `drf.v`), **but** as Lahav et al. (PLDI 2017, §§5–6) establish, compiling `RC11` soundly to ARMv8/POWER/RVWMO requires preserving load-to-store ordering on `Relaxed` loads (e.g., bogus branch dependency or `fence r,w`) unless `Relaxed` load-store cycles cannot arise.
- **`Promising 1.0` (`snu-sf/promising-coq`, POPL 2017) -> `Promising 2.0` (`snu-sf/promising2-coq`, PLDI 2020):** Lets threads speculatively *promise* future `Relaxed` writes (`Thread.promise_step`, `Thread.v:73–82`) iff immediately **certified** (`Thread.consistent`, `Thread.v:202–210`) by thread-local silent execution (`rtc tau_step`) fulfilling `Local.promises = Memory.bot` (`L209`). Independent `LB` certifies $y := 1$ unconditionally (validating plain `LDR`/`STR`, `lw`/`sw`, and load-store reordering!), while `LB+deps` cannot certify `42`. Because `Promising 1.0`'s quantification over *all* future memories broke global value-range invariants and register promotion, `Promising 2.0` evaluates certification strictly against deterministic **capped memory** `Memory.cap` (`Thread.v:204–205`) with promise-free (`pf = true`, `L79–80`) lower/cancel steps.
- **Verification Invariance:** Monotone separation logics (`iRC11`, `ViewPCM`, `FSL`, `GPS`) rely exclusively on `hb` and `mo`—never on `acyclic (sb ∪ rf)` over `Relaxed` cycles—so library proofs hold simultaneously under `RC11`, `Promising 2.0`, and unthrottled `LDR`/`STR` and `lw`/`sw` codegen; only *compiler backend* proofs reordering `Relaxed` loads past stores require `Promising 2.0`.

---

### 5. Optimistic Torn Reads, Access-Based Mixed-Size Atomics, and `r[undefined.race]`

`Basis: normative + source + derived`

1. **Access-Based Rust vs. Object-Based C++20 (`atomic.rs:28–113`, `data_race.rs:520–550, 1143–1172`):** Rust attaches atomicity to individual *accesses* (`weak_memory.rs:48–65`). Concurrent `atomic.load(Relaxed)` and non-atomic `*ptr` reads (or differently-sized atomic loads) are **defined** (`atomic.rs:38–42, 78–84`; `data_race.rs:537–542`). Conversely, any unsynchronized conflicting pair with a write where (a) either access is non-atomic (`r[undefined.race]`, `behavior-considered-undefined.md:15–16`), OR (b) both are atomic with unequal `(addr, size)` spans (`atomic.rs:51–54, 94–101`, `data_race.rs:529–544`), is **immediate UB**. *(Note: `minirust/minirust` `spec/mem/concurrent.md:4, 15–21, 164–175` currently models only SC `Atomicity::Atomic` vs. `None` and omits mixed-size atomic write races.)*
2. **UB-Free Optimistic Torn Reads (`SeqLock<T>`):** Neither non-atomic reads, `ptr::read_volatile` (`r[undefined.race]`), nor typed `Relaxed` loads of validity-constrained types (`bool`, `char`, `NonZero*`, enums; `r[undefined.invalid]`, `behavior-considered-undefined.md:58–60, 121–169`) are sound during concurrent writes. Optimistic readers must load uniform-width `AtomicUsize`/`AtomicU8` chunks (`Ordering::Relaxed`) matching the writer's exact store width into `[MaybeUninit<usize>; K]` (`r[undefined.validity.maybe-uninit]`, `L148–150`), execute `fence(Acquire)`, verify `s1 == s2 && (s1 & 1) == 0`, and materialize `T: Copy` *only inside the validated branch*.

---

### 6. Compilation Soundness: `RC11` / `Promising 2.0` to `x86-TSO`, `ARMv8`, and `RISC-V RVWMO`

`Basis: normative + source + execution + derived`

| Rust Operation | `x86-TSO` (`x86_64`) | `ARMv8.0` / `v8.1 LSE` (`AArch64`) | `RISC-V RVWMO` (`psABI A6S`: `Zaamo`+`Zalrsc`) | `RISC-V` + `Zalasr` ("Table A.7") |
| :--- | :--- | :--- | :--- | :--- |
| **`load(Relaxed)`** | `mov` | `ldr` | `l{b\|h\|w\|d}` | `l{b\|h\|w\|d}` |
| **`load(Acquire)`** | `mov` | `ldar` *(or v8.3 `ldapr`)* | `l{b\|h\|w\|d}; fence r,rw` | `l{b\|h\|w\|d}.aq` |
| **`load(SeqCst)`** | `mov` | **`ldar`** *(NEVER `ldapr`!)* | `fence rw,rw; l{b\|h\|w\|d}; fence r,rw` | `l{b\|h\|w\|d}.aq` *(Note 3)* |
| **`store(Relaxed)`** | `mov` | `str` | `s{b\|h\|w\|d}` | `s{b\|h\|w\|d}` |
| **`store(Release)`** | `mov` | `stlr` | `fence rw,w; s{b\|h\|w\|d}` | `s{b\|h\|w\|d}.rl` |
| **`store(SeqCst)`** | **`xchg`** *(or `mov; mfence`)* | **`stlr`** | **`fence rw,w; s{b\|h\|w\|d}; fence rw,rw`** *(or `amoswap.rl`)* | `s{b\|h\|w\|d}.rl` |
| **`fence(Acquire)`** | *(compiler barrier)* | `dmb ishld` | `fence r,rw` | `fence r,rw` |
| **`fence(Release)`** | *(compiler barrier)* | **`dmb ish`** *(NEVER `dmb ishst`!)* | `fence rw,w` | `fence rw,w` |
| **`fence(AcqRel)`** | *(compiler barrier)* | `dmb ish` | `fence.tso` | `fence.tso` |
| **`fence(SeqCst)`** | **`mfence`** *(or `lock or [rsp],0`)* | `dmb ish` | `fence rw,rw` | `fence rw,rw` |
| **`fetch_<op>(ord)`** | `lock <op>` / `cmpxchg` | `ld{,a}xr`/`st{,l}xr` or LSE `ld<op>{,a,l,al}` | `amo<op>.{w\|d}{,.aq,.rl,.aqrl,.aqrl}` | Same (`amo<op>`) |
| **`compare_exchange(SC)`** | `lock cmpxchg` | `ldaxr; cmp; b.ne; stlxr` or `casal` | `loop: lr.{w\|d}.aqrl; bne; sc.{w\|d}.rl; bnez` | `lr.{w\|d}.aq[rl]; bne; sc.{w\|d}.rl` |

Four ISA-specific invariants govern backend soundness:
1. **`x86-TSO`:** Hardware preserves $R \to RW$ and $W \to W$, collapsing `Acquire`/`Release`/`AcqRel` fences to compiler barriers (identical to RISC-V `Ztso` in `riscv-atomic.adoc:185–190`). All TUs must drain the store buffer on the same side of `SeqCst` (`xchg` on `store(SeqCst)` + `mov` on `load(SeqCst)`), and `fence(SeqCst)` requires `mfence` when ordering non-temporal stores (`movnt*`).
2. **`ARMv8` (`LDAPR` and `DMB ISHST` Traps):** Under multicopy-atomic ARMv8 (Pulte et al., POPL 2018), $[L] \cdot \mathsf{po} \cdot [A] \subseteq \mathsf{bob}$ orders `STLR` before `LDAR`, discharging `psc_base` on `SB` without `DMB ISH`. However, ARMv8.3 `LDAPR` ($Q$) omits $[L] \cdot \mathsf{po} \cdot [Q]$ (re-admitting `SB` `0/0` if used for `load(SeqCst)`!), and `DMB ISHST` orders *only* $W \to W$ (allowing prior loads to sink past `fence(Release)`—`fence(Release)` **must** emit `DMB ISH`).
3. **`RISC-V RVWMO` Table A.6 vs. `psABI` Trailing Fence and `Zalasr` (`mm-explanatory.adoc:1444–1579`, `zalasr.adoc:32–136`, `riscv-atomic.adoc:25–87`):** Unprivileged Manual "Table A.6" mapped `store(SeqCst)` to `fence rw,w; sw` (no trailing fence), relying on `load(SeqCst)`'s leading `fence rw,rw`. When linked with `Zalasr` ("Table A.7", `load(SeqCst) -> lw.aq`, `store(SeqCst) -> sw.rl`), a Table A.6 `fence rw,w; sw x, 1` followed by a `Zalasr` `lw.aq y` violates *all* RVWMO PPO Rules 4–7 (`rvwmo.adoc:284–290`: `sw` lacks `.rl`/RCsc, `lw.aq` lacks `.rl`, and no `fence rw,rw` intervenes)—**reordering to break `SB`!** `riscv-elf-psabi-doc` (`riscv-atomic.adoc:83–87`) therefore mandates trailing `fence rw,rw` (`fence rw,w; s{b|h|w|d}; fence rw,rw` or `amoswap.rl`).
4. **`RISC-V` `lr.aqrl`, `Zacas` Note 5, and FP Progress (`riscv-atomic.adoc:130, 152–155, 256–269`):** Table A.6 interoperability requires `lr.{w|d}.aqrl` (`L130`, ordering prior stores via `.rl` PPO Rule 6 even when `sc` fails and emits zero memory ops, `rvwmo.adoc:82`) and a leading `fence rw,rw; amocas.{w|d}.aqrl` when `compare_exchange` has `SeqCst` failure ordering (`Note 5`, `L152–155`). Floating-point instructions are forbidden inside `lr`/`sc` loops to preserve `RsrvEventual` progress (`L256–269`).

## Boundaries

- **`Ordering::Consume` (`memory_order_consume`):** **known not to apply** in Rust (`atomic.rs:28, 465–526`).
- **Same-Thread `Relaxed` Store Extension of Release Sequences:** **known not to apply** in C++20 and Rust (`P0982R1`, `data_race.rs:7–10, 611–618`).
- **Normative Rust Resolution of Independent `LB` (`RC11` vs. `Promising 2.0`):** Whether Rust's future specification (`memory-model.md:5–6`) will permit independent `LB` ($r_0 = r_1 = 1$) via a Promising-style model or restrict `Relaxed` load-store reordering remains **unknown** (`weak_memory.rs:31–37`).
- **Unsynchronized Mixed-Size Atomic Writes:** Overlapping unsynchronized atomic writes of differing widths are **unsupported** (immediate UB in Rust/C++20, `atomic.rs:51–54`, `data_race.rs:529–544`; under-specified in RVWMO, `rvwmo.adoc:34–39`).
- **MMIO, Instruction-Fetch Coherence (`fence.i` / `ISB`), and TLB Shootdowns (`sfence.vma` / `TLBI`):** Device I/O and privileged address-translation barriers (`rvwmo.adoc:28–32`) were **not examined**.

## Evidence

- **`rust-lang/miri` @ `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3`:** `src/concurrency/data_race.rs` (`L7–10, 154–208, 520–651, 946–958, 1123–1178, 1843–1884`), `src/concurrency/weak_memory.rs` (`L9–65`).
- **`rust-lang/rust` @ `ec65cd52bba13d491ff65c9d218b39753755c84a` & `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:** `library/core/src/sync/atomic.rs` (`L25–113, 465–526, 4814–4910`), `src/behavior-considered-undefined.md` (`L15–16, 58–60, 121–169`), `src/memory-model.md` (`L1–27`).
- **`minirust/minirust` @ `063d784186d3252bee242217f218223205c0b568`:** `spec/mem/concurrent.md` (`L1–36, 134–176`).
- **`qladevez/rc11` @ `fad08ae4c6f41c4268e11140e551b5c42ce07224`, `snu-sf/promising-coq` @ `fd9796ede251a2edf0ebf8c938443a30d5eadee9`, & `snu-sf/promising2-coq` @ `6b70a57d10666ec66bfa96b7801dd870f9054da9`:** `rc11.v` (`L29–30, 88–136, 232–452, 691–713`), `drf.v`, `src/lang/TView.v` (`L21–38, 168–225`), `src/lang/Thread.v` (`L73–105, 202–210`).
- **`riscv/riscv-isa-manual` @ `c05f1725f25526dd8463bac6ca75cfcfbee17d05` & `riscv-non-isa/riscv-elf-psabi-doc` @ `56561cb3e7330fe99a98fd27457229707b2786ae`:** `src/unpriv/rvwmo.adoc` (`L65–155, 259–352`), `src/unpriv/mm-explanatory.adoc` (`L1444–1592, 1621–1643`), `src/unpriv/zalasr.adoc` (`L1–137`), `riscv-atomic.adoc` (`L20–269`).
- **Papers & Proposals:** WG21 `P0982R1` (2018-10-07); Lahav et al., PLDI 2017 (`10.1145/3062341.3062352`); Kang et al., POPL 2017 (`10.1145/3009837.3009850`); Lee et al., PLDI 2020 (`10.1145/3385412.3386010`); Pulte et al., POPL 2018 (`10.1145/3158107`).

## Revalidation

1. **Upstream Diffs (< 1 minute):** Diff `store_relaxed`, `rmw_relaxed`, `atomic_fence`, and `atomic_access` in `rust-lang/miri` (`src/concurrency/data_race.rs`) and `riscv-atomic.adoc` in `riscv-non-isa/riscv-elf-psabi-doc`.
2. **Executable Model Probe (`python3` stdlib, < 0.2s):** Verify (a) `P0982R1` vs. `RC11`/`Promising` release-sequence narrowing on same-thread `store(Relaxed)` vs. `fetch_add(Relaxed)`, and (b) RVWMO PPO Rules 4–7 showing why Table A.6 `store_sc` + `Zalasr` `load_sc` breaks `SB` while psABI `A6S` trailing `fence rw,rw` and pure `Zalasr` preserve `ppo`:
   ```python
   #!/usr/bin/env python3
   """Verify P0982R1 release-sequence narrowing and RVWMO Table A.6 vs psABI/Zalasr SB soundness."""
   def syncs_after_write_chain(p0982r1: bool, second_op_is_rmw: bool) -> bool:
       t1_cur, t1_frel, t1_rel_x = 1, 0, 1
       msg1_sync = t1_cur
       if second_op_is_rmw:
           msg2_sync = max(msg1_sync, t1_frel)   # RMW joins prior sync_vector with fence_release
       elif p0982r1:
           msg2_sync = t1_frel                   # C++20/Miri overwrites sync_vector := fence_release (0)
       else:
           msg2_sync = max(t1_rel_x, t1_frel)    # RC11/Promising inherits same-thread rel['X'] (1)
       return msg2_sync >= 1

   def rvwmo_ppo_orders_sb_pair(store_seq: tuple[str, ...], load_seq: tuple[str, ...]) -> bool:
       seq = store_seq + load_seq
       s_idx = next(i for i, op in enumerate(seq) if op.startswith("sw"))
       l_idx = next(i for i, op in enumerate(seq) if op.startswith("lw"))
       s_op, l_op = seq[s_idx], seq[l_idx]
       return (
           "fence_rw_rw" in seq[s_idx + 1 : l_idx]                                     # PPO Rule 4
           or ".aq" in s_op                                                            # PPO Rule 5
           or ".rl" in l_op                                                            # PPO Rule 6
           or ((".aq" in s_op or ".rl" in s_op) and (".aq" in l_op or ".rl" in l_op))  # PPO Rule 7
       )

   assert syncs_after_write_chain(p0982r1=False, second_op_is_rmw=False) is True
   assert syncs_after_write_chain(p0982r1=True,  second_op_is_rmw=False) is False
   assert syncs_after_write_chain(p0982r1=True,  second_op_is_rmw=True)  is True
   a6_st, a6s_st, z_st = ("fence_rw_w", "sw"), ("fence_rw_w", "sw", "fence_rw_rw"), ("sw.rl",)
   a6_ld, z_ld = ("fence_rw_rw", "lw", "fence_r_rw"), ("lw.aq",)
   assert rvwmo_ppo_orders_sb_pair(a6_st,  a6_ld) is True
   assert rvwmo_ppo_orders_sb_pair(a6_st,  z_ld)  is False  # Unsound cross-TU mix!
   assert rvwmo_ppo_orders_sb_pair(a6s_st, z_ld)  is True   # psABI trailing fence fixes it!
   assert rvwmo_ppo_orders_sb_pair(z_st,   z_ld)  is True   # Pure Zalasr PPO Rule 7!
   print("OK: P0982R1 narrowing and RVWMO A6 vs psABI/Zalasr SB checks verified.")
   ```
