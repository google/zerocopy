# Vector-Length-Agnostic SIMD: RISC-V RVV 1.0, ARM SVE/SVE2, and Portable Lane Proof Abstractions

## Summary

Vector-length-agnostic (VLA) SIMD instruction sets—principally **RISC-V Vector Extension (RVV) 1.0** and **ARM Scalable Vector Extension (SVE/SVE2)**—parameterize register capacity dynamically at runtime rather than fixing lane widths in instruction encodings like AVX2, NEON, or Rust's `core::simd::Simd<T, N>`. Formalizing their semantics across the RVV 1.0 specification, `sail-riscv`, Arm ACLE, LLVM IR/RISC-V codegen, `rust-lang/rust`, `Alive2`, and primary hardware papers establishes five foundational distinctions:

1. **CSR-Stateful Stripmining (RVV) vs. Predicate-Driven Lanes (SVE) vs. Fixed Widths (`core::simd`):** RVV 1.0 configures 32 architectural vector registers through CSRs (`vtype` `{vill, vma, vta, vsew[2:0], vlmul[2:0]}`, `vl <= VLMAX = LMUL * VLEN / SEW`, and `vstart`) with power-of-two `VLEN` and `LMUL ∈ {1/8..8}`. ARM SVE/SVE2 keeps vector width implicit (`128..2048` bits in arbitrary `128`-bit multiples, including non-power-of-two `384`/`640`/`768` bits), governs lanes via `P0–P15` byte-granularity predicates (`VLEN / 8` bits), and loops via `WHILELT`/`INCB` without any `vl` CSR.
2. **RVV `vsetvli` Non-Determinism and `vta`/`vma` Agnosticism:** Contrary to `min(AVL, VLMAX)`, RVV 1.0 and `sail-riscv` allow any deterministic `ceil(AVL / 2) <= vl <= VLMAX` when `VLMAX < AVL < 2 * VLMAX` (`vl_use_ceil`). Moreover, `vta = 1` / `vma = 1` permit each tail (`i >= vl`) or masked (`mask[i] == 0`) lane independently to retain prior state or become `0xFF..FF`, requiring active-prefix equivalence $\equiv_{(vl, m)}$ and exposing unmasked reductions (`vredsum.vs` after widening `vl`) to `-1` / `NaN` contamination—whereas SVE binds `/z` or `/m` directly on instructions and predicates reductions via `Pg`.
3. **Fault-Suppression Algebra (`vle<eew>ff.v` vs. SVE `LDFF1*` + `FFR`):** Speculative unit-stride loads trap synchronously only on the first active lane and suppress traps thereafter. RVV mutates architectural `vl := fault_idx` directly (and allows fault-free trimming down to `1` when `vstart == 0`), whereas SVE clears trailing bits in a cumulative `FFR` predicate governed by ACLE's `FFRT` dependency tokens (`SETFFR`/`RDFFR`).
4. **Type-System and Compiler IR Encodings (`sizeless`, `#[rustc_scalable_vector]`, `vscale`, `llvm.vp.*`):** ACLE classifies SVE vectors as *sizeless definite types* (valid on automatic stacks/parameters, banned from `sizeof`, structs, statics, and pointer arithmetic); Rust mirrors this with `#[rustc_scalable_vector]` primitives (`sve_tuple_create2..4`) that are `!Sized` yet retain thin `()` pointer metadata because `vscale` is ambient rather than per-object. LLVM encodes symbolic widths via `<vscale x N x T>`, two-dimensional `StackOffset = Fixed + vscale * Scalable`, partial-order `TypeSize` inequalities assuming `vscale >= 1`, `llvm.vp.*` explicit-EVL intrinsics, and `RISCVInsertVSETVLI` dataflow synthesis.
5. **Overcoming Fixed-`vscale` Validation Limits via Parametric Lane Abstractions:** `Alive2` rejects scalable-offset structs and pins `<vscale x N x T>` to one concrete `util::config::vscale_value`, missing width-dependent wraps like `u8` `vid.v` at `VLEN = 512, LMUL = 8` (`512 > 256` lanes) or SVE `vscale = 3`. A portable abstraction `VlaVecSpec(vscale, evl, mask)` separates `Fin (vscale * N)` indexing from ISA-specific `vscale` constraints and reduces loop proofs to four width-independent obligations: stripmining conservation, pointwise scalar-equivalent lane correctness, inactive/tail non-interference, and ordered-vs-associative reduction partitioning.

---

## Applicability

This report relates formal ISA specifications, hardware architectures, compiler IRs, language type systems, and translation-validation engines across nine pinned subjects:

- **RISC-V RVV 1.0 Normative & Formal Semantics:** `riscvarchive/riscv-v-spec` (`2f68ef7256d6ec53e4d2bd7cb12862f406d64e34`, v1.0), `riscv/riscv-isa-manual` (`c05f1725f25526dd8463bac6ca75cfcfbee17d05`), and the official Sail specification `riscv/sail-riscv` (`76f1ce3c184797178864b9869963e8b44465889e`, `model/extensions/V/*`), paired with the Ara RVV silicon implementation (Cavalcante et al., `10.1109/TVLSI.2019.2950087`).
- **ARM SVE / SVE2 Specification & Language Bindings:** Stephens, Reid, et al., *The ARM Scalable Vector Extension* (`10.1109/MM.2017.35`, arXiv `1803.06185`, IEEE Micro 2017) and `ARM-software/acle` (`74fa229b09d1c5af533a88e387e470c26494953f`, `main/acle.md`).
- **Compiler Lowering, Rust Intrinsics, and Verification:** `llvm/llvm-project` (`7583443aeb22dfe52bd581ce7e5294313dd33449`: `TypeSize.h`, `VPIntrinsics.def`, `RISCVInsertVSETVLI.cpp`), `rust-lang/rust` (`ec65cd52bba13d491ff65c9d218b39753755c84a`: `library/core/src/intrinsics/simd/scalable.rs`), and `AliveToolkit/alive2` (`3bdd4f5e1cefa47057e93110e707acd11cfe08e4`: `llvm_util/utils.cpp`, `ir/type.h`).

**Target constraints and prior corpus coverage:** RVV 1.0 requires power-of-two `VLEN >= ELEN` (`Zve32x`/`Zve64x`/`V` up to `Zvl65536b`, `sail_vext_control.sail:9-30`), whereas SVE/SVE2 permits any `128 * k` bit vector (`1 <= k <= 16`, i.e., `128..2048` bits). Fixed-width `#[repr(simd)]` / `core::simd::Simd<T, N>` legalization (`Split2`/`Split4`, cross-half shuffles, and `x86_64`/`aarch64` vendor cost models) is covered in `portable-simd-repr-simd-legalization-and-cross-arch-cost-certificates`; IEEE-754 ordered vs `reassoc` reductions are covered in `ordered-floating-point-simd-reductions-and-rfc3514-reassoc-certificates`; vendor `std::arch` sources are inventoried in `rustc-intrinsics-simd-and-arch-semantic-sources` and `vendor-intrinsic-specifications-stdarch-verification-and-lean-generation`; and general RV64GC ABI lowering appears in `rustc-codegen-backend-abi-intrinsics-and-rv64gc-cross-compilation`.

---

## Findings

### 1. Architectural State Models: RVV 1.0 CSRs vs. SVE Predicates vs. Fixed-Width SIMD

**Basis:** normative (`riscvarchive/riscv-v-spec` `v-spec.adoc:86-520`, `1265-1325`) + source (`riscv/sail-riscv` `model/extensions/V/vext_vset_insts.sail:15-216`, `vext_control.sail:9-49`, `vext_regs.sail:52-177`) + literature (`10.1109/MM.2017.35`, `10.1109/TVLSI.2019.2950087`).

The architectural state surfaces across VLA and fixed-width SIMD targets differ as follows:

| Dimension | RISC-V RVV 1.0 (`V` / `Zve*`) | ARM SVE / SVE2 | Fixed-Width (`core::simd` / AVX2 / NEON) |
| :--- | :--- | :--- | :--- |
| **Vector Width (`VLEN`)** | Power of `2` in `32..65536` bits (`VLEN >= ELEN`); `v0–v31` | Multiple of `128` in `128..2048` bits (**`384`/`640`/`768` legal**); `Z0–Z31` | Static (`128b` NEON/SSE2, `256b` AVX2, `512b` AVX-512) |
| **Register Grouping** | `LMUL ∈ {1/8..8}` (`vlmul[2:0]`, `0b100` reserved); `EMUL = (EEW/SEW)*LMUL` | `1×` single `Zn` or register tuples `SVecTup` (`LD2..LD4`) | Legalized statically (`Split2`/`Split4` or `WidenVecCert`) |
| **Lane Capacity (`VLMAX`)** | Dynamic CSR ratio `VLMAX = LMUL * VLEN / SEW` (`v-spec.adoc:345-362`) | Implicit `VLEN / esize` (`CNTW`/`CNTD`) | Compile-time constant `N` |
| **Active-Count Control** | Mutable `vl` CSR (`0 <= vl <= VLMAX`) set by `vset{i}vl{i}` / `vle*ff.v` | **No `vl` CSR**; predicates via `WHILELT`/`WHILELO` and `INCB`..`INCD` | Scalar tail loop or `k`-mask / `vp` blend |
| **Predicates / Masks** | Vector reg `v0` (1 bit/element at `0..vl-1`, `v0.t`) | `P0–P15` (`VLEN/8` bits: 1 bit per **byte**, spaced every `esize/8`!) | `i1` mask vectors or AVX-512 `k0–k7` |
| **Fault / Restart State** | `vstart` CSR (trap/interrupt element index, reset to `0` on completion) | `FFR` cumulative predicate (`SETFFR`/`RDFFR`/`WRFFR`) | Scalar faulting or explicit `masked_load` |

#### 1.1 RVV `vtype` Encoding and `vset{i}vl{i}` Semantics (`vext_vset_insts.sail:58-216`)
RVV encodes configuration in `vtype` (`v-spec.adoc:172-205`): bit `XLEN-1` is `vill` (forcing `vtype[XLEN-2:0] = 0` and `vl = 0`), `XLEN-2:8` are reserved zero, bit `7` is `vma`, bit `6` is `vta`, bits `5:3` are `vsew[2:0]` (`000=8..011=64`, `1xx` reserved), and bits `2:0` are signed `vlmul[2:0]` (`-3..3`, `100` reserved). `execute_vsetvl_type` (`vext_vset_insts.sail:103-147`) traps via `handle_illegal_vtype` (`vill = 1`) whenever `SEW > ELEN`, `SEW > LMUL * ELEN`, or `requires_fixed_vlmax` (`rd == x0 && rs1 == x0`) alters `LMUL_pow - SEW_pow` or sees prior `vill`. Notice the three `(rd, rs1)` modes (`lines 160-167`):
- `rs1 != x0`: `AVL = X[rs1]`, updating `vl` and `X[rd]`.
- `rs1 == x0 && rd != x0`: `AVL = ~0`, pinning `vl = VLMAX`.
- `rs1 == x0 && rd == x0`: preserves `AVL = vl` *iff* `VLMAX` is invariant (`v-spec.adoc:1265-1280`).

Critically, `calculate_new_vl(AVL, VLMAX)` (`vext_vset_insts.sail:82-92`, `v-spec.adoc:1292-1325`) is **not** `min(AVL, VLMAX)`: for `AVL <= VLMAX`, `vl = AVL`; for `AVL >= 2 * VLMAX`, `vl = VLMAX`; but for **`VLMAX < AVL < 2 * VLMAX`**, hardware may deterministically pick any **`ceil(AVL / 2) <= vl <= VLMAX`** (`sail-riscv` parameterizes `(AVL + 1) / 2` vs `VLMAX` via `vl_use_ceil`), enabling balanced splitting (`5 + 4` for `AVL = 9, VLMAX = 8`) on designs like Ara (`10.1109/TVLSI.2019.2950087`) and breaking any proof that assumes `vl == VLMAX` whenever `AVL > VLMAX`.

---

### 2. Tail Predication, Inactive-Lane Policies, and Observational Equivalence Algebras

**Basis:** normative (`v-spec.adoc:381-489`) + source (`sail-riscv` `vext_regs.sail:158-177`, `vext_mem_insts.sail:75-93`, `vext_red_insts.sail:102-148`, `ARM-software/acle` `main/acle.md`) + execution (`verify_probes.py` Probe B) + derived.

Both RVV and SVE distinguish **inactive masked elements** ($i < vl \land \neg m_i$) from **tail elements** ($i \ge vl$ in RVV, or inactive elements beyond loop bound $n$ in SVE), yet expose contrasting modification semantics:

| Operation Class | RVV `tu`/`mu` (`0`) | RVV `ta`/`ma` (`1`) | ARM SVE `/m` vs. `/z` vs. `_x` |
| :--- | :--- | :--- | :--- |
| **Vector ALU / Load** | Retains previous `vd[i]` bit-for-bit (`undisturbed`) | Each element independently retains prior `vd[i]` **or** becomes `0xFF..FF` (`all-1s`), nondeterministically per granule/hart (`v-spec.adoc:409-447`) | Explicit instruction encoding: merging (`/m`) preserves `Zd[i]`; zeroing (`/z`) writes `0`; ACLE `_x` ("don't care") permits compiler choice of `/z`, `/m`, or unpredicated op |
| **Mask-Producing Ops** | Tail bits always agnostic (`vta` ignored, `v-spec.adoc:402-403`) | Tail bits may hold prior value, `0xFF..FF`, or result computed up to `VLMAX` (or `VLEN` for `vm*` mask-logical ops, except mask loads!) (`v-spec.adoc:449-465`) | Predicate instructions (`AND`, `BRKA`, `WHILELT`) update `N` flags (`P0–P15`); inactive/unused byte bits are zeroed or undisturbed per instruction |
| **Horizontal Reductions** | Scalar output written at `vd[0]`; `vd[1..]` treated as tail (`vext_red_insts.sail:143-145`) | `vd[1..]` may become `0xFF..FF`! Input `vs2` reads active `0 <= i < vl` where `v0.mask[i] == 1` | Scalar result written to SIMD scalar register (`V0` / GPR); takes explicit `Pg` predicate on **every** reduction (`UADDV`, `FADDA`) |

#### 2.1 Active-Prefix Observational Equivalence and the Unmasked-Reduction Trap
To verify `ta`/`ma` code cleanly (essential on out-of-order renamed cores that avoid false read-dependencies on old `vd`, `v-spec.adoc:417-422`), define **active-lane observational equivalence** at $(vl, m)$:

$$u \equiv_{(vl, m)} w \iff \forall i < vl,\ m_i = 1 \implies u_i = w_i$$

Under `vta = 1, vma = 1`, any RVV instruction $op$ satisfies the relational nondeterministic soundness law: if $s \equiv_{(vl, m)} s'$, all post-states $t \in \llbracket op \rrbracket(s)$ satisfy $t \equiv_{(vl, m)} t_{\text{ideal}}$. However, **widening `vl` without re-masking breaks observational equivalence**:
- **Concrete Counterexample (Probe B):** Suppose a `u8` loop writes 2 active elements `[10, 20]` at `vl = 2, vta = 1` into `v1` (whose prior tail `[2..4)` was `[0, 0]`). Hardware legally overwrites tail lanes `[2..4)` with `[0xFF, 0xFF]`. If a subsequent `vredsum.vs` executes after resetting `vl = 4` without an explicit mask (`v0.t`), the sum mod `256` drops from `30` to `(10 + 20 + 255 + 255) mod 256 = 28`! Sound `vta = 1` compilation must keep `vl` monotonically non-increasing across producer-consumer chains or mask consumers explicitly with `v0.t`.

---

### 3. Speculative Vectorization and Fault-First Memory Semantics

**Basis:** normative (`v-spec.adoc:1724-1785`, `10.1109/MM.2017.35`) + source (`sail-riscv` `model/extensions/V/vext_mem_insts.sail:102-183`, `ARM-software/acle` `main/acle.md:8604-8706`) + execution (`verify_probes.py` Probe B) + derived.

Vectorizing `while` loops (`strlen`, `memchr`, pointer-chasing filters) with unknown trip counts risks page faults when reading past buffer ends. Both ISAs solve this with fault-suppressing unit-stride loads, yet encode fault witnesses differently:

1. **RVV `VLSEGFFTYPE` (`vle<eew>ff.v` / `vlseg<nf>e<eew>ff.v`, `vext_mem_insts.sail:110-180`):**
   - Computes effective register multiplier `EMUL_pow = EEW_pow - SEW_pow + LMUL_pow` (requiring `-3 <= EMUL_pow <= 3`, line `118`).
   - Iterates segments `i = 0 .. num_elem - 1` while `not(trimmed)`. On `mask[i] == 1`, any memory read error at `i == 0` returns synchronous trap `Err(e)` (`vl` unmodified, `v-spec.adoc:1729-1731`).
   - On any memory read error at **`i > 0`**, hardware suppresses the trap, sets architectural **`vl := i`**, sets `trimmed = true` (treating lanes `>= i` as tail elements under `vta`, lines `152-175`), and resets `vstart = 0`. Exception: a hardware debug watchpoint `PendingTrigger` at `i > 0` traps at `vstart = i` so watchpoints are not silently dropped (lines `143-151`).
   - Furthermore, `v-spec.adoc:1737-1744, 1775-1777` allow `vle*ff.v` to speculatively write garbage into trimmed active lanes `>= i` (forbidding non-idempotent MMIO reads!) and allow implementations to trim `vl` conservatively even *without* a fault, subject only to **`vl >= 1` whenever `vstart == 0` and initial `vl > 0`**.
2. **ARM SVE `LDFF1*` + `FFR` (`acle.md:8604-8706`, `10.1109/MM.2017.35`):**
   - SVE stores fault status in a separate cumulative **First-Fault Register (`FFR`)** predicate (`SETFFR` initializes all bits to `1`; `LDNF1*` suppresses faults even at the first active lane!).
   - On a potential fault at active lane `i > first_active`, `LDFF1*` clears `FFR[k] = 0` for all `k >= i` and marks result lanes `k >= i` in `Zd` as **unknown** (also unknown if `FFR[i]` was *already* `0` before the load!).
   - Because C/C++ optimizers would otherwise reorder normal-looking loads past `SETFFR`/`RDFFR`, ACLE (`acle.md:8647-8692`) introduces a conceptual global **`FFRT` (First-Fault Register Token)** `(nwrite, lastwrite, nread)`: explicit writes (`svsetffr`/`svwrffr`) increment `nwrite`, `svrdffr` increments `nread`, and `svldff1*`/`svldnf1*` read `FFRT` without mutating it—forming "FFR groups" inside which compilers may freely reorder or dead-eliminate unused loads while preserving group boundaries.

#### 3.1 Fault-First Bisimulation Theorem (Verified Across `1,785` Cases in Probe B)
When comparing single-load or chained speculative loops starting at an active prefix `[0..vl0)` with zero leading masked-off elements (`first_active == 0`), RVV's `vsetvli + vle8ff.v` and SVE's `WHILELT P0 + SETFFR + LDFF1B + RDFFR P1 + AND P1, P0, P1 + CNTP` compute **identical processed element counts `k` and identical safe memory reads** on every iteration up to the exact `valid_len` boundary (ignoring spurious fault-free `vl` shrinkage permitted by RVV hardware, which merely splits one iteration into smaller progress steps while preserving `vl >= 1`). Crucially, if SVE `P0` has leading false bits (`active[0] == 0, active[1] == 1`), `LDFF1` faults only if lane `1` (the *first active* lane) faults (`10.1109/MM.2017.35`), whereas RVV `vle8ff.v` checks `i == 0` in `vext_mem_insts.sail:152` (`if i == 0 then return e`)—meaning if `mask[0] == 0`, RVV never traps on `mask[1] == 1` and instead trims `vl := 1` (producing zero active loaded lanes!). Loop generators using non-prefix masks (`v0[0] == 0`) must therefore verify `vl_active > 0` to avoid livelock!

---

### 4. Type-System and Compiler IR Lowering: Sizeless Types, `vscale`, VP Intrinsics, and `RISCVInsertVSETVLI`

**Basis:** normative (`ARM-software/acle` `main/acle.md:7110-7270`) + source (`rust-lang/rust` `library/core/src/intrinsics/simd/scalable.rs:1-66`, `llvm/include/llvm/Support/TypeSize.h:30-442`, `llvm/include/llvm/IR/VPIntrinsics.def:128-320`, `llvm/lib/Target/RISCV/RISCVInsertVSETVLI.cpp:13-220`) + derived.

#### 4.1 Sizeless Definite Types (ACLE) vs. `#[rustc_scalable_vector]` vs. Rust `?Sized` DSTs
Because VLA registers vary dynamically by hardware implementation, C/C++ ACLE (`acle.md:7114-7270`) splits C types into *sized* vs. *sizeless* and *definite* vs. *indefinite*: SVE vectors (`svint32_t`, `svbool_t`) are **sizeless definite** object types—legal as locals, function arguments/returns, compound literals, and pointer targets, yet banned from `sizeof`, `_Alignof`, struct/union fields, arrays, statics/TLS, `new`/`delete`, and pointer arithmetic (`+`, `-`, `++`).

In `rust-lang/rust`, `library/core/src/intrinsics/simd/scalable.rs:1-66` defines unstable compiler intrinsics (`sve_tuple_create2..4`, `sve_tuple_get`, `sve_tuple_set`) over `#[rustc_scalable_vector]` and `#[rustc_scalable_vector(N)]` types. Conceptually, scalable vector types occupy a distinct fourth point in Rust's size model: unlike `core::simd::Simd<T, N>` (which is `Sized` and storable inside `#[repr(C)]` structs), scalable vectors are `!Sized` (no compile-time byte size), **yet pointers `*const svint32_t` must remain thin (`()` metadata)** rather than wide `?Sized` DST pointers, because `vscale` is an invariant execution-environment constant rather than per-allocation metadata.

#### 4.2 LLVM `TypeSize`, `StackOffset`, and `llvm.vp.*` Predication
LLVM IR represents VLA vectors as `<vscale x N x elty>` (optionally bounded by `vscale_range(min, max)` function attributes) and models sizes/offsets in `llvm/include/llvm/Support/TypeSize.h`:
- **`StackOffset` (`TypeSize.h:31-81`):** Represents frame offsets as two-component linear polynomials `Fixed + vscale * Scalable`, enabling coexistence of fixed scalar spills and scalable `Z`/`v` vector spills on the stack.
- **`FixedOrScalableQuantity<LeafTy, ValueTy>` (`TypeSize.h:86-285`):** Unifies `ElementCount` and `TypeSize` as `(Quantity, Scalable)`. Implicit `operator uint64_t()` on `TypeSize` aborts via `reportFatalInternalError` if `isScalable()` (`TypeSize.h:384-391`). Inequalities (`isKnownLT`, `isKnownLE`, `isKnownGT`, `isKnownGE`, lines `217-243`) rely strictly on **`vscale >= 1`**:
  - `isKnownLE(LHS, RHS)` returns `LHS.Quantity <= RHS.Quantity` iff `!LHS.Scalable || RHS.Scalable`, and **`false` unconditionally** when comparing a scalable LHS (`vscale * a`, $a > 0$) against a fixed RHS (`b`), because without a `vscale_range` upper bound, `vscale` may exceed `b / a`!
- **LLVM Vector Predication (`VPIntrinsics.def:128-320`):** Standard `<vscale x N x T>` ops lack an active-length scalar, so LLVM uses `@llvm.vp.*(args..., mask, evl)`—covering integer/FP ALU (`vp_sdiv`, `vp_udiv`), masked/strided/fault-first memory (`vp_load`, `vp_store`, `vp_load_ff`, `experimental_vp_strided_{load,store}`, `vp_gather`, `vp_scatter`), and reductions (`HELPER_REGISTER_REDUCTION_SEQ_VP` distinguishing strict left-to-right sequential reductions from `reassoc` parallelizable reductions).
- **`RISCVInsertVSETVLI` Dataflow Synthesis (`RISCVInsertVSETVLI.cpp:13-24, 160-220`):** On RISC-V, machine pseudo-instructions carry virtual `AVL` and `vtype` operands; a three-step dataflow pass collects per-block `VL`/`VTYPE` demands, propagates incoming `BlockData.Pred`/`Exit` across the CFG, inserts minimal `PseudoVSET(I)VLI`, and uses `PseudoVSETVLIX0X0` (`vsetvli x0, x0, vtypei`) whenever `hasSameAVL(PrevInfo) && hasSameVLMAX(PrevInfo)` (`lines 169-203`), eliminating redundant `vl` mutations across `SEW`/`LMUL`-preserving transitions.

---

### 5. Translation Validation Limits (`Alive2`) and Parametric Lane Proof Abstractions

**Basis:** source (`AliveToolkit/alive2@3bdd4f5e1cefa47057e93110e707acd11cfe08e4` `llvm_util/utils.cpp:173-232`, `ir/type.h:271-360`) + execution (`verify_probes.py` Probe B) + derived.

Bounded SMT translation validators struggle with VLA vectors because SMT bitvectors require fixed static widths. Inspecting `AliveToolkit/alive2` (`llvm_util/utils.cpp:173-232`) reveals two hard architectural boundaries:
1. **Scalable Struct Rejection (`utils.cpp:179-194`):** In `llvm_type2alive`, `StructType` conversion explicitly aborts (`// TODO: support vscale; if (ofs.isScalable() || sz.isScalable()) return nullptr;`) whenever any struct field offset or size is scalable.
2. **Concrete `vscale` Specialization (`utils.cpp:213-232`):** When converting `llvm::Type::ScalableVectorTyID`, `Alive2` reads `elems = vty->getElementCount().getKnownMinValue()` and multiplies `count = elems * util::config::vscale_value` (checking `count <= max_vector_elements = 65535` from `ir/type.h:21`). Thus `Alive2` validates scalable IR **only at one fixed concrete `vscale_value` at a time**, never universally across all valid `vscale`!

#### 5.1 Why Bounded `vscale` Instantiation Misses Real VLA Bugs
Validating an optimization at `vscale = 1` or `2` is unsound as a general VLA theorem for three reasons:
1. **Index Bitwidth Saturation (`vid.v` / `INDEX` Wrap-Around):** At `vscale = 1` (`VLEN = 128`) or `vscale = 2` (`VLEN = 256`) with `LMUL = 8` and `SEW = 8`, `VLMAX` is `128` or `256`—so an unsigned 8-bit lane-index vector (`0, 1, ..., vl-1`) fits without wrapping. At `vscale = 4` (`VLEN = 512, LMUL = 8`), `VLMAX = 512 > 256`, causing `u8` lane indices to wrap modulo `256` (Probe B)! Any compiler pass rewriting `u8` index checks assuming injectivity fails silently at `VLEN >= 512`.
2. **Non-Power-of-Two SVE Widths:** ARM SVE allows `vscale = 3` (`384`-bit), `5` (`640`-bit), `6` (`768`-bit), etc. Passes relying on `vscale` being a power of two (such as log-tree reductions or bit-mask `ElementCount::isPowerOf2()`, which `TypeSize.h:324-327` explicitly assumes!) are sound for RVV 1.0 yet unsound on general SVE hardware unless explicitly restricted.
3. **Stripmining `ceil(AVL / 2)` Split Shifts:** At `vscale = 1` (`VLMAX = 4`), `AVL = 6` lies inside `(VLMAX, 2*VLMAX)`, triggering non-deterministic `ceil(AVL/2) = 3` vs `4` splitting, whereas at `vscale = 2` (`VLMAX = 8`), `AVL = 6 <= VLMAX` executes in one step with zero tail-splitting.

#### 5.2 Portable Parametric Lane Proof Abstraction (`VlaVecSpec`)
To verify VLA vector algorithms and IR transformations independently of `VLEN`, deductive verifiers (e.g., Lean 4 or Rocq) can parameterize machine states over a bounded symbolic multiplier `(vscale : Nat) (h_lo : vmin <= vscale) (h_hi : vscale <= vmax)` (with `h_pow2 : exists k, vscale = 2^k` isolated as an **RVV-only** hypothesis, omitted for SVE!). Represent any predicated vector register state as a triple `(data : Fin (vscale * N) -> Val, mask : Fin (vscale * N) -> Bool, evl : Nat)` with `evl <= vscale * N` (`evl = vscale * N` for SVE where only `mask` disables lanes). Correctness reduces to four **finite, `vscale`-independent proof obligations**:

1. **Stripmining Progress & Conservation ($\mathbf{O_1}$):** Given remaining elements $r > 0$, any valid step picks $1 \le \text{evl} \le \min(r, \text{VLMAX}(vscale))$, preserving $r' = r - \text{evl} < r$ and $\sum_t \text{evl}_t = N_{\text{total}}$ regardless of whether hardware selects `ceil(r/2)` or `VLMAX`.
2. **Pointwise Lane Locality ($\mathbf{O_2}$):** For any lane-wise operation $f$, proving $\forall k < \text{evl},\ m(k) \implies P(\text{out}[k], \text{in}[k])$ eliminates the `vscale` quantifier by universal instantiation on an arbitrary index $k$, reducing the theorem to a **single fixed-width scalar bitvector obligation** (discharged by `bv_decide` or SMT in $O(1)$ independent of `vscale`)!
3. **Inactive/Tail Non-Interference ($\mathbf{O_3}$):** For operations with side effects or lane-local UB (`vp_load`, `vp_store`, `vp_sdiv`, `vp_shl`), prove that lanes satisfying $k \ge \text{evl} \lor \neg m(k)$ trigger no memory access, fault, or division-by-zero, and that downstream consumers depend only on active values up to $\equiv_{(\text{evl}, m)}$ (or store explicit `vta = 0` undisturbed invariants for sliding/cross-lane reuse).
4. **Monoid vs. Ordered Reduction Partitioning ($\mathbf{O_4}$):** For integer associative-commutative monoids (`+`, `&`, `|`, `^`, `min`, `max`), tree reductions (`vredsum.vs` / `UADDV`) commute with arbitrary `evl` splits across iterations. For non-associative IEEE-754 floating-point reductions (`vfredosum.vs` / `FADDA` / non-`reassoc` `VP_REDUCE_FADD`), prove left-to-right sequential fold preservation: $\text{foldl}(\oplus, acc, \text{concat}_{t} \text{active}_t) = \text{foldl}(\lambda a\ x_t.\ \text{foldl}(\oplus, a, x_t), acc, [x_0, x_1, \dots])$.

---

### 6. Executable Verification of Stripmining, Agnosticism, and Fault-First Bisimulation

**Basis:** execution (`verify_probes.py` Probe B, Python `3.x` stdlib) + source (`sail-riscv` `vext_vset_insts.sail`, `vext_mem_insts.sail`, `TypeSize.h`) + derived.

Executing the self-contained reference model below verified:
- **RVV `vsetvli` Parameter Space (`14,512` checks across `VLEN ∈ {128, 256, 512, 1024}`, `SEW ∈ {8,16,32,64}`, `LMUL ∈ {1/8..8}`):** Verified `vill` legality rejection (`SEW > LMUL * ELEN`) and discovered `6,904` explicit `(vl_ceil < vl_greedy)` non-determinism witnesses in `VLMAX < AVL < 2 * VLMAX`.
- **Stripmining Conservation (`1,592` runs across `total ∈ 1..199`, `VLMAX ∈ {4,8,16,32}`):** Verified exact termination and $\sum_t \text{vl}_t = \text{total}$ under both `vl_use_ceil = True` and `vl_use_ceil = False`.
- **Counterexamples (`vta=1` & `vid.v`):** Confirmed `(10+20) mod 256 = 30 != 28 = (10+20+255+255) mod 256` on unmasked widened `vredsum`, and confirmed `u8` `vid.v` distinctness holds for `vscale ∈ {1, 2}` (`<= 256` lanes) yet fails at `vscale = 4, LMUL = 8` (`512` lanes).
- **Fault-First Bisimulation (`1,785` traces) & `TypeSize::isKnownLE` Soundness:** Verified identical cumulative element counts across RVV `vle8ff.v` and SVE `SETFFR + LDFF1B + RDFFR + CNTP` across all valid buffer/fault splits, and verified `llvm_is_known_le` over `vscale ∈ 1..31`:

```python
import math

def sail_calculate_new_vl(avl: int, vlmax: int, vl_use_ceil: bool) -> int:
    if avl <= vlmax:
        return avl
    elif avl < 2 * vlmax:
        return (avl + 1) // 2 if vl_use_ceil else vlmax
    return vlmax

def verify_vla_invariants() -> None:
    # 1. Stripmining conservation under both ceil and greedy vsetvli policies
    for total in range(1, 100):
        for vlmax in (4, 8, 16):
            for ceil_mode in (False, True):
                rem, acc = total, 0
                while rem > 0:
                    vl = sail_calculate_new_vl(rem, vlmax, ceil_mode)
                    assert 1 <= vl <= min(rem, vlmax)
                    rem -= vl
                    acc += vl
                assert acc == total
    # 2. vta=1 unmasked reduction trap and u8 vid.v vscale=4 wraparound
    assert ((10 + 20 + 0xFF + 0xFF) & 0xFF) == 28 != 30
    assert len({i & 0xFF for i in range(128 * 2 * 8 // 8)}) == 256
    assert len({i & 0xFF for i in range(128 * 4 * 8 // 8)}) == 256 < 512
    # 3. LLVM FixedOrScalableQuantity::isKnownLE soundness across vscale >= 1
    for lq in range(0, 12):
        for ls in (False, True):
            for rq in range(0, 12):
                for rs in (False, True):
                    known_le = ((not ls) or rs) and (lq <= rq)
                    if known_le:
                        assert all(lq * (vs if ls else 1) <= rq * (vs if rs else 1)
                                   for vs in range(1, 32))
```

---

## Boundaries

- **unsupported:** In Arm ACLE (`acle.md:7139-7172`), `sizeof`, `_Alignof`, struct/union/class fields, static or thread-local storage, arrays, `new`/`delete`, and pointer arithmetic on sizeless SVE types (`svint32_t`, `svbool_t`) are **unsupported**. In `AliveToolkit/alive2` (`llvm_util/utils.cpp:179-194`), LLVM structs containing scalable-size or scalable-offset fields are **unsupported** (`llvm_type2alive` returns `nullptr`). In RISC-V RVV 1.0 (`v-spec.adoc`), non-power-of-two `VLEN` implementations and `vlmul = 0b100` / `vsew >= 0b100` encodings are **unsupported**.
- **known not to apply:** Fixed-`vscale` bounded translation validation (`Alive2` `util::config::vscale_value`, `utils.cpp:222-227`) is **known not to apply** as a universal proof over arbitrary VLA widths for width-dependent overflow idioms (`u8` `vid.v` at `VLEN = 512, LMUL = 8`) or non-power-of-two SVE widths (`vscale = 3`, `384`-bit). The equation `vl = min(AVL, VLMAX)` is **known not to apply** to RVV 1.0 when `VLMAX < AVL < 2 * VLMAX` (`sail_calculate_new_vl` permits `ceil(AVL/2) <= vl <= VLMAX`). Treating `vta = 1` tail elements as preserved zeros is **known not to apply** (`v-spec.adoc:409-426` permits arbitrary per-granule `0xFF..FF` overwrites). Tree-reduction associativity is **known not to apply** to strict IEEE-754 ordered float reductions (`vfredosum.vs` / `FADDA`).
- **unknown:** Whether Rust's unstable `#[rustc_scalable_vector]` (`library/core/src/intrinsics/simd/scalable.rs`) will unify under a cross-architecture `core::simd` scalable trait or remain confined to `core::arch` vendor intrinsics is **unknown** at `rust-lang/rust@ec65cd52bba13d491ff65c9d218b39753755c84a`.
- **not examined:** ARM SME / SME2 2D matrix tile storage (`ZA` array and `SMSTART`/`SMSTOP` streaming-mode `SVL` transitions), RISC-V vector cryptography extensions (`Zvbb`, `Zvbc`, `Zvkned`, `Zvknhab`), and cycle-level microarchitectures beyond Ara (`10.1109/TVLSI.2019.2950087`) were **not examined**.

---

## Evidence

Verified on `2026-11-20`:

| Subject / Artifact | Immutable Identity | Inspected Paths & Anchors | Claims Grounded |
| :--- | :--- | :--- | :--- |
| `riscvarchive/riscv-v-spec` | `2f68ef7256d6ec53e4d2bd7cb12862f406d64e34` (`v1.0`) | `v-spec.adoc:86-520,1265-1325,1724-1785` | `vtype` layout, `VLMAX`, `vta`/`vma` all-1s nondeterminism, `vill`, `vsetvli` `ceil(AVL/2)` rule, `vle*ff.v` trap/spurious-write rules |
| `riscv/sail-riscv` | `76f1ce3c184797178864b9869963e8b44465889e` | `model/extensions/V/{vext_types,vext_control,vext_regs,vext_vset_insts,vext_mem_insts,vext_red_insts}.sail` | Executable `calculate_new_vl` (`vl_use_ceil`), `execute_vsetvl_type`, `VLSEGFFTYPE`, `RMVVTYPE` (`vredsum.vs`) |
| `riscv/riscv-isa-manual` | `c05f1725f25526dd8463bac6ca75cfcfbee17d05` | Vector ISA integration baseline | RVV 1.0 profile alignment (`Zve32x`/`Zve64x`/`V`) |
| `ARM-software/acle` | `74fa229b09d1c5af533a88e387e470c26494953f` | `main/acle.md:625-645,1992-2013,7110-7270,8604-8724,9092-9115` | Sizeless definite C/C++ types, `LDFF1*`/`LDNF1*`, `FFR` & conceptual `FFRT` dependency tokens |
| `llvm/llvm-project` | `7583443aeb22dfe52bd581ce7e5294313dd33449` | `llvm/include/llvm/Support/TypeSize.h:30-467`; `llvm/include/llvm/IR/VPIntrinsics.def:128-320`; `llvm/lib/Target/RISCV/RISCVInsertVSETVLI.cpp:13-220` | `StackOffset`, `FixedOrScalableQuantity::isKnownLE`, `@llvm.vp.*` (`vp_load_ff`, sequential vs `reassoc` reductions), `RISCVInsertVSETVLI` |
| `rust-lang/rust` | `ec65cd52bba13d491ff65c9d218b39753755c84a` | `library/core/src/intrinsics/simd/scalable.rs:1-66` | `#[rustc_scalable_vector]` & `sve_tuple_{create2..4,get,set}` |
| `AliveToolkit/alive2` | `3bdd4f5e1cefa47057e93110e707acd11cfe08e4` | `llvm_util/utils.cpp:173-232`; `ir/type.h:21,271-360` | Scalable struct rejection (`nullptr`) & single concrete `vscale_value` specialization |
| Peer-reviewed IEEE papers | DOI `10.1109/MM.2017.35` (`arXiv:1803.06185`); DOI `10.1109/TVLSI.2019.2950087` | Stephens, Reid, et al. (IEEE Micro 2017); Cavalcante et al. (IEEE TVLSI 2020) | SVE variable 128b-multiple `VLEN`, byte-indexed predicates, `FFR`; Ara RVV hardware scaling |
| Algebraic Probe | Python 3 stdlib (`2026-11-20`) | Inline model in **Findings §6** | `PROBE_B PASS: vset_checks=14512, nondet_witnesses=6904, stripmine_runs=1592, ff_bisim_cases=1785, vta_bug=(30!=28), vid_u8_wrap=(vscale2=True,vscale4=False)` |

---

## Revalidation

Run the following lightweight source and Python 3 algebraic check (`< 1 s`, stdlib only) to verify the pinned `sail-riscv`, `Alive2`, `llvm`, and `rust` semantics and re-check stripmining, `TypeSize::isKnownLE`, and `vid.v` wraparound invariants:

```bash
SAIL_SHA="76f1ce3c184797178864b9869963e8b44465889e"
ALIVE_SHA="3bdd4f5e1cefa47057e93110e707acd11cfe08e4"
LLVM_SHA="7583443aeb22dfe52bd581ce7e5294313dd33449"
curl --http1.1 -fsSL "https://raw.githubusercontent.com/riscv/sail-riscv/${SAIL_SHA}/model/extensions/V/vext_vset_insts.sail" | grep -n -A 10 "function calculate_new_vl"
curl --http1.1 -fsSL "https://raw.githubusercontent.com/AliveToolkit/alive2/${ALIVE_SHA}/llvm_util/utils.cpp" | grep -n -A 12 "ScalableVectorTyID"
curl --http1.1 -fsSL "https://raw.githubusercontent.com/llvm/llvm-project/${LLVM_SHA}/llvm/include/llvm/Support/TypeSize.h" | grep -n -A 6 "isKnownLE("

python3 - <<'PY'
def new_vl(avl, vlmax, ceil_mode):
    return avl if avl <= vlmax else (((avl + 1) // 2 if ceil_mode else vlmax) if avl < 2 * vlmax else vlmax)
for tot in range(1, 65):
    for m in (False, True):
        r, s = tot, 0
        while r > 0:
            v = new_vl(r, 8, m); assert 1 <= v <= min(r, 8); r -= v; s += v
        assert s == tot
assert ((10 + 20 + 0xFF + 0xFF) & 0xFF) == 28
assert len({i & 0xFF for i in range(512)}) == 256
print("Revalidation OK")
PY
```
