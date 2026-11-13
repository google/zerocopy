# Five-Link End-to-End Verified MIR-to-x86-64 Machine-Code Refinement Chain and Definitional Seams Catalog

## Summary

Carrying an already-verified Anneal Rust function (`add_bounded(x: usize, y: usize) -> usize` from `theory/Anneal/FunctionalTranslation.lean` @ `a7ac073219f4ec3c813431be8239a0405014d5c1`, alongside `alloc_passthrough` from `tests/fixtures/refs.rs` @ `b1f15f743c423c42c47d674a113519882b6d3738`) through every link of a **5-link end-to-end Lean `v4.34.1` mechanization** (`support/lean_s16_chain/`, `642` total lines / `495` code lines, built in **`4.27` seconds** under `anneal-lean-run` with **zero `sorry`** and **zero `native_decide`**) down to the exact **29-byte x86-64 machine-code sequence** emitted by `rustc 1.99.1 -C opt-level=3` (`support/fixture_objdump.txt`) exposes and bridges **five fundamental definitional seams** (`support/seams_catalog.json`):

1. **`SEAM-1` — Value Representation Seam (Mathematical `Nat` vs. Modular `BitVec 64`):**
   - Anneal's `MirSemantics.lean` / `FunctionalTranslation.lean` evaluates `usize` locals in mathematical `Nat` with explicit overflow assertions (`x + y ≤ usizeMax`), whereas optimized SSA (`Link2W6Opt.lean`) and x86-64 (`Link4X86Isa.lean`) compute over modular two's-complement `BitVec 64`. Bridging this seam requires `wordRepresentsNat` (`28` LOC) and discharging `(BitVec.ofNat 64 (x + y)).toNat = x + y` under the pre-branch bounds `x ≤ 1000 ∧ y ≤ 1000`.
2. **`SEAM-2` — Memory Model & Provenance-Erasing Injection Seam (`AllocId` Store vs. SSA Registers & Flat Bytes):**
   - MIR local references (`let r = &x; *r` in `alloc_passthrough`) index a typed logical store (`AllocId → Option MirVal`) with storage-generation tags, whereas `-O3` promotes stack slots to SSA registers (`W6`'s `promoteSlotToAssign`) and lowers remaining stack accesses to flat byte addresses (`BitVec 64 → UInt8`, `18` LOC bridge).
3. **`SEAM-3` — Control-Flow, Fuel, and Variable-Length Instruction Fetch Seam (`BlockId` CFG vs. Byte-Indexed `rip`):**
   - MIR and SSA index control flow by structured basic-block IDs (`bb0..bb5`), whereas concrete x86-64 execution (`runX86 k m_init`) fetches variable-length instructions (`4, 2, 7, 4, 7, 4, 1` bytes = `29` bytes) from `m.codeMem` at byte offsets `codeBase + 0#64 .. codeBase + 28#64`. Crucially, coupling the instruction decoder `decodeX86At` to the full `X86State` record prevents `simp` from reusing decode hypotheses after register mutations; decoupling `decodeX86At (codeMem : BitVec 64 → UInt8) (rip : BitVec 64)` (`64` LOC bridge) makes multi-instruction symbolic stepping linear (`797 ms` build time).
4. **`SEAM-4` — Calling Convention, Flag Dataflow, and Stack Frame Seam (Positional Locals vs. System V AMD64 ABI):**
   - MIR passes arguments in `_1, _2` and returns in `_0`, whereas System V AMD64 passes `arg0` in `rdi`, `arg1` in `rsi`, routes range comparisons through the hardware Carry Flag (`cmpq $0x3e9, %rsi` setting `CF := rsi <u 1001` followed by `cmovaeq %rcx, %rax`), pops `retAddr` from `readStack64 (regs .rsp)`, increments `rsp` by `8#64`, and preserves `rbx, rbp, r12..r15` (`sysvEntryState` + `calleeSavedPreserved`, `42` LOC bridge).
5. **`SEAM-5` — Observable Events and Termination Seam (`MirOutcome.returned` vs. Halting at `retAddr`):**
   - MIR terminates by constructing the algebraic sum value `MirOutcome.returned v`, whereas a hardware machine state has no `.returned` tag and instead signals normal return by `m_final.rip = retAddr` with the result in `m_final.regs .rax` (`HighLevelPost`, `24` LOC bridge).

## Applicability

- **Extends:** `anneal-mir-to-x86-compiler-vcgen-and-variable-step-refinement`, `compiler-correctness-theorem-shapes-and-end-to-end-chains`, `lean-derivation-checker-soundness-and-completeness-prototype`, `tier1-calling-conventions-fnabi-and-llvm-lowering`, `formal-isa-models-x86-64-i386-and-aarch64-coverage`
- **Subjects:** Evaluated on Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), and `joshlf/anneal` (`a7ac073219f4ec3c813431be8239a0405014d5c1` and `b1f15f743c423c42c47d674a113519882b6d3738`).

## Findings

### 1. The Verified Fixture Through `rustc 1.99.1` (`MIR` -> `-O3` LLVM IR -> 29-Byte x86-64 Machine Code)

**Basis: source + execution**

In `joshlf/anneal` (`theory/Anneal/FunctionalTranslation.lean#L9534-L9585` @ `a7ac073219f4ec3c813431be8239a0405014d5c1`), `add_bounded` has the 6-block `Runtime(PostCleanup)` MIR body (`support/fixture.mir`):
- `bb0`: `_3 = Le(copy _1, const 1000_usize); switchInt(move _3) -> [0: bb4, otherwise: bb1]`
- `bb1`: `_4 = Le(copy _2, const 1000_usize); switchInt(move _4) -> [0: bb4, otherwise: bb2]`
- `bb2`: `_5 = AddWithOverflow(copy _1, copy _2); assert(!move (_5.1: bool)) -> [success: bb3, unwind continue]`
- `bb3`: `_0 = move (_5.0: usize); goto -> bb5`
- `bb4`: `_0 = const 0_usize; goto -> bb5`
- `bb5`: `return`

When compiled with `rustc +1.99.1-x86_64-unknown-linux-gnu -C opt-level=3 --emit=llvm-ir,obj` (`support/fixture_o3.ll`, `support/fixture_objdump.txt`):
1. **Optimized LLVM IR (`6` instructions in `1` basic block):**
   ```llvm
   define noundef range(i64 0, 2001) i64 @add_bounded(i64 noundef %x, i64 noundef %y) {
   start:
     %_3 = icmp ult i64 %x, 1001
     %_4 = icmp ult i64 %y, 1001
     %or.cond = and i1 %_3, %_4
     %0 = add nuw nsw i64 %y, %x
     %_0.sroa.0.0 = select i1 %or.cond, i64 %0, i64 0
     ret i64 %_0.sroa.0.0
   }
   ```
2. **Assembled x86-64 Machine Code (`29` bytes across `7` instructions):**
   ```text
   0000000000000000 <add_bounded>:
      0: 48 8d 04 3e                   leaq    (%rsi,%rdi), %rax
      4: 31 c9                         xorl    %ecx, %ecx
      6: 48 81 fe e9 03 00 00          cmpq    $0x3e9, %rsi
      d: 48 0f 43 c1                   cmovaeq %rcx, %rax
     11: 48 81 ff e9 03 00 00          cmpq    $0x3e9, %rdi
     18: 48 0f 43 c1                   cmovaeq %rcx, %rax
     1c: c3                            retq
   ```

---

### 2. Five-Link Lean 4.34.1 Chain Architecture and Module Metrics

**Basis: source + execution**

The formal chain in `support/lean_s16_chain/S16Chain/` carries `add_bounded` (and `alloc_passthrough`) across all five links and bridges all five seams without a single `sorry` (`support/seams_catalog.json`):

| Link | Module (`S16Chain/`) | Total Lines | Code Lines | Build Time (`ms`) | `.olean` Size (`B`) | Key Theorem & Role in Chain |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Link 1** | `Link1Mir.lean` | `97` | `66` | `379` | `292,504` | `link1_anneal_mir_add_bounded_verified`: proves the 6-block MIR body with `AddWithOverflow` assertion satisfies `evalMirAddBounded st = .returned (HighLevelAddBoundedSpec x y)` |
| **Link 2** | `Link2W6Opt.lean` | `124` | `93` | `362` | `327,760` | `seam1_mir_to_ssa_pre_bridge` + `link2_w6_opt_ssa_sound`: bridges `Nat` to `BitVec 64` and proves the `-O3` branchless `ult 1001#64` + `select` optimization equals pre-opt SSA |
| **Link 3** | `Link3AbiLowering.lean` | `96` | `69` | `717` | `383,168` | `link3_abi_lowering_sound`: proves the 7-instruction System V AMD64 assembly sequence (`leaq`, `xorl`, `cmpq`, `cmovaeq`) computes `evalSsaPostO3 (st.regs .rdi) (st.regs .rsi)` in `rax` and preserves `rsp, rbx, rbp, r12..r15` |
| **Link 4** | `Link4X86Isa.lean` | `215` | `181` | `797` | `434,536` | `link4_x86_decode_and_run_7_steps`: proves that fetching and decoding the exact 29 machine bytes (`fixtureMachineBytes`) from `codeBase` executes `7` variable-length steps (`+4, +2, +7, +4, +7, +4, retq`) in `runX86 7 m_init` |
| **Link 5** | `TopTheorem.lean` | `110` | `86` | `1,000` | `322,624` | **`end_to_end_x86_correct`**: composes Links 1–4 and Seams 1–5 into one closed theorem over `X86State` |
| **Total** | **`S16Chain` (5 links)** | **`642`** | **`495`** | **`4,270` ms** | **`1,760,592`** | **Zero `sorry`, zero `native_decide`; axioms: `[propext, Classical.choice, Quot.sound]`** |

The top-level closed theorem verified in `S16Chain/TopTheorem.lean` is:

```lean
theorem end_to_end_x86_correct
    (m_init : X86State) (codeBase retAddr arg0 arg1 : BitVec 64)
    (h_code : loadedAt m_init codeBase fixtureMachineBytes)
    (h_abi  : sysvEntryState m_init codeBase retAddr arg0 arg1)
    (_h_pre : HighLevelPre arg0 arg1) :
    ∃ (k : Nat) (m_final : X86State),
      runX86 k m_init = some m_final ∧
      m_final.rip = retAddr ∧
      m_final.regs .rsp = m_init.regs .rsp + 8#64 ∧
      HighLevelPost arg0 arg1 (m_final.regs .rax) ∧
      calleeSavedPreserved m_init m_final
```

---

### 3. Complete Taxonomy of Definitional Seams and TCB Placement

**Basis: source + execution + derived**

Every boundary where Link $i$'s conclusion is not syntactically identical to Link $i+1$'s premise is cataloged below (`support/seams_catalog.json`):

| Seam ID | Link Boundary | Left-Hand Conclusion Type | Right-Hand Premise Type | Exact Definitional Mismatch | Bridge Adapter & Proof Cost (`LOC`) | Production TCB Placement (`trusted/` vs. `theory/`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`SEAM-1`** | Link 1 (`MIR`) $\to$ Link 2 (`SSALike`) | `MirVal.usize (n : Nat)` with `n ≤ usizeMax` | `BitVec 64` (plus `MaskedWord 64` poison mask in `AnLLVM`) | Mathematical `Nat` addition vs. modular $2^{64}$ ring arithmetic; requires proving `BitVec.toNat (x + y) = x.toNat + y.toNat` under range guard | `wordRepresentsNat` + `seam1_mir_to_ssa_pre_bridge` (`28` LOC) | Value correspondence relation in `trusted/lean/Trusted/`; bridge proof in untrusted `theory/` |
| **`SEAM-2`** | Link 1 (`MIR` Allocs) $\to$ Link 2/3 (`SSA` / Stack) | `allocs : AllocId → Option Nat` (`localGens`, `frameId`) | `regs : RegId → BitVec 64` and flat `mem : BitVec 64 → UInt8` | Logical per-local allocations (`&x`) disappear completely under `SROA`/`mem2reg` or map to `[rsp + disp]` in flat address space | `promoteSlotToAssign` (`W6`) + frame disjointness (`18` LOC) | Untrusted `theory/` for `mem2reg`; `trusted/lean/Trusted/` only for initial stack-vs-code disjointness |
| **`SEAM-3`** | Link 2 (`CFG` SSA) $\to$ Link 4 (`X86State` Fetch) | `evalSsaPostO3 : BitVec 64 → BitVec 64 → MirOutcome (BitVec 64)` | `runX86 : Nat → X86State → Option X86State` over byte-indexed `rip` | Abstract block IDs vs. variable-length (`1..7` byte) instruction fetch at `codeBase + off#64`; state-coupled `decodeX86At` blocks `simp` reuse | `loadedAt` + state-decoupled `decodeX86At codeMem rip` (`64` LOC) | `X86State`, `stepX86`, `runX86`, and `loadedAt` in `trusted/lean/Trusted/`; 7-step trace proof in `theory/` |
| **`SEAM-4`** | Link 2 (`_0, _1, _2`) $\to$ Link 3/4 (System V ABI) | Positional MIR locals `st.locals 1`, `st.locals 2`, `st.locals 0` | Physical `rdi`, `rsi`, `rax`, `CF` flag, `readStack64 rsp`, `rsp + 8#64`, `rbx..r15` | MIR has no physical registers, condition flags (`CF`), or return-address stack pop (`retq`) | `sysvEntryState` + `calleeSavedPreserved` + `link3_abi_lowering_sound` (`42` LOC) | `sysvEntryState` and `calleeSavedPreserved` in `trusted/lean/Trusted/`; lowering lemma in `theory/` |
| **`SEAM-5`** | Link 1 (`MirOutcome`) $\to$ Link 5 (`X86State` Halt) | Algebraic sum `.returned v \| .panic \| .ub` | Concrete machine state `m_final.rip = retAddr` | Hardware state has no `.returned` sum tag; termination is reaching `retAddr` with `rsp = rsp_0 + 8` | `HighLevelPost` relating `m_final.regs .rax` back to `evalMirAddBounded` (`24` LOC) | Root theorem statement in `trusted/lean/Trusted/` |

## Boundaries

- **Leaf Function Without Callee Stack Allocation (`not examined` for multi-frame recursive calls with stack probes):** `add_bounded` and `alloc_passthrough` are leaf functions that execute in caller-saved registers without modifying stack memory below `rsp`; functions with stack spills (`t07_regalloc_with_spills` in `llvm-o3-derivation-formats-expressiveness-and-checking-cost`) require adding a byte-level stack-frame separation conjunct (`rsp - frameSize` disjoint from `codeMem`) to `sysvEntryState`.

## Evidence

- **`support/fixture.rs`, `support/fixture.mir`, `support/fixture_o3.ll`, `support/fixture_objdump.txt`:** Exact Rust source, `Runtime(PostCleanup)` MIR dump, `-O3` LLVM IR, and 29-byte `llvm-objdump -d` disassembly.
- **`support/lean_s16_chain/`:** Complete 5-link Lean `v4.34.1` Lake package (`Link1Mir.lean`, `Link2W6Opt.lean`, `Link3AbiLowering.lean`, `Link4X86Isa.lean`, `TopTheorem.lean`).
- **`support/seams_catalog.json`:** Machine-readable catalog of all 5 definitional seams, bridge adapters, LOC costs, and TCB placement rules.

## Revalidation

Build and kernel-verify the 5-link chain using `anneal-lean-run`:

```bash
cd support/lean_s16_chain
anneal-lean-run --mode build --concurrency 4 -- lake build
```
