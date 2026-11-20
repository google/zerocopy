# Release-Fingerprinted Multi-Target Rust `FnAbi` Bit-Exact Marshaling, Linker-Symbol Compatibility, and Physical-Frame Adapter-Shim Refinement

## Summary

Empirical measurement across `9` targets and `3` `rustc` releases (`1.99.1`, `1.100.0`, `1.102.0-nightly`) in `rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting` (`google/zerocopy@120889696dc131f0fc7cf814e898ee72cd04a19e`) established that **every target architecture experiences cross-release binary or `.o` linker-symbol ABI drift**, including staggered `x86`/`x86_64` vs. `aarch64` `extern "Rust"` SIMD transitions (`D1`, `D2`), a Windows `x86_64` `extern "C"` non-`#[repr(C)]` ZST register-shift break (`D3`), and an `x86_64` `vectorcall` `.o` linker-symbol byte-count break (`@@16 -> @@24`, `D4`) that leaves LLVM IR parameter modes unchanged.

This report documents the standalone, locked-`Init.*`-only Lean 4 mechanization **`VrustcFormal.F1_3`** (`support/RustFnAbiBitExactLowering.lean`, `3,388` lines, `158,677` bytes, SHA-256 `8f79d62a6ead93d1013b4cbb0f9989bd79570091f60416adfefea599c57d0cde`, `0` `sorry`, axioms strictly **`[propext]`**—zero `Classical.choice`, zero `Quot.sound`, zero `unsafe`/`partial`/`_unsafe_rec`, zero `Anneal.*` imports), proving **4 universal theorems** and **9 concrete empirical witnesses/canaries**:

1. **Same-Fingerprint Bit-Exact Call-Boundary Roundtrip (`same_abi_marshal_roundtrip`, `[kernel-checked proof]`):** Under the finite-frame bound `sig.args.length + 2 < 2^64`, for every `(target, release, sig)` in the modeled `4`-target × `3`-release × `3`-convention × `9`-type universe and every well-typed `(vals, retVal)`, marshaling `vals` into a word-serialized `PhysFrame` (allocating any caller `sret` buffer at token `1` strictly disjoint from argument indirect tokens `>= 2`) and unmarshaling recovers `vals` bit-for-bit; threaded return marshaling into the **same** call frame `fCall` recovers `retVal` bit-for-bit whenever either `isX87RetMode abi.retMode = false` or `isNonSignalingRet retVal`.
2. **Release-Fingerprinted Direct Call-Boundary Preservation (`fullAbiCompatible_preserves_call_boundary`, `[kernel-checked proof]`):** Whenever `fullAbiCompatible` holds across two compilations `(t₁, rel₁)` and `(t₂, rel₂)` of `sig`, they agree on target, calling convention, `sret` location, canonical pass modes, and `.o` linker `symbolRule` (eliminating `0` vs. `@@0` sentinel collisions), and preserve direct caller-to-callee marshaling/unmarshaling bit-for-bit without an adapter shim.
3. **Non-Tautological `AbiVal`-Free Physical-Frame Adapter-Shim Refinement (`phys_shim_bridge_restores_equivalence`, `[kernel-checked proof]`):** For **any** same-target release pair `(t, rel₁, rel₂)` and signature `sig`, the statically compiled `PhysShim` IR (`compileShimPlan`, `execArgShim`, `execRetShim`—mechanically verified over `669` kernel constants to contain **`0` references** to `AbiVal`, `encodeValWords`/`decodeValWords`, or `marshal*`/`unmarshal*`) bridges `fCaller` to `fCallee` and `fCalleeOut` back to `fCallerOut` bit-exact using raw `BitVec 64` word transfers (outside x87 signaling-NaN returns), and accurately flags `plan.needsLinkerAlias = true ↔ abi₁.symbolRule ≠ abi₂.symbolRule`.
4. **IR-Only Fingerprint Incompleteness & Universal `i686` x87 sNaN Sharpness (`fingerprint_and_universal_x87_sharpness`, `[kernel-checked proof]`):** Proves (a) IR-only fingerprinting (`irOnlyCompatible = true`) misses the real `x86_64` `vectorcall` `(HfaF32x4, f32) -> HfaF32x4` `.o` linker break (`@@16 ≠ @@24`), and (b) **every** IEEE-754 `f32` and `f64` signaling NaN is strictly altered by the modeled `i686SysV` `extern "C"` x87 return while preserved bit-for-bit by `extern "Rust"`.
5. **Nine Kernel-`rfl` Empirical Witnesses & Positive Canaries (`ce_d1`–`ce_d6`, `canary_p1`–`canary_p3`, `[kernel-checked proof]`):** Directly reproduce `D1` (`x86_64`/`i686` SIMD `1.99.1 -> 1.100.0` `.missingReg`), `D2` (`aarch64` NEON `x8` `sret` `1.100.0 -> 1.102.0`), `D3` (Win64 non-`#[repr(C)]` ZST `1.100.0 -> 1.102.0` silent register-shift corruption replacing `0xCAFEBABE` with token `1` vs. `#[repr(C)]` ZST stability), `D4` (`@@16 -> @@24` vs. `i686` `@@20` and `bigStruct 3` `@@8 -> @@24`), `D5` (`undecorated` vs. `@@0` non-collision), `D6` (`i686` `0x7f800001 -> 0x7fc00001` vs. bit-exact `extern "Rust"`), `P1` (`sysv64` `(Option<NonNull<u8>>, hfa2F64, u32)` cross-release stability + `f64` sNaN preservation), `P2` (end-to-end `PhysShim` recovery across Win64 `D3` and `sysv64` `D1` including `sret` population), and `P3` (`abi_vec_many6_simd` `@@112` stack overflow, `sysv64` `vectorcall` `hfa2F64` `@@8 -> @@16` & ZST `@@16 -> @@8`, and `i686` `byval` `bigStruct 3` `@@24`).
6. **Three-Kernel + Unmodified Anneal `TrustedBoundary.lean` Verification (`[real measurement]`):** All `13` public user theorems (`204` source declarations, `1,756` kernel constants) pass fresh synchronous Lean `v4.34.1` (`17.103 s`, `478.79 MB` RSS, `0` warnings/errors), unmodified `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` `TrustedBoundary.lean` `"preflight"` (`4.099 s`; negative `sorry` probe rejected `rc = 1`) + full Pass 1 `"audit"` (`7.526 s`, `replay = true`, `3,337` replayed decls, `axioms = ["propext"]`) + standalone Pass 1 `"audit"` (`5.438 s`, `1,756` replayed decls), fresh Lean `v4.35.0` (`17.614 s`, `446.23 MB` RSS), and `lean4export 3.1.0` (`0.916 s`, `9,543,273 B`) + **`nanoda_bin 0.4.19`** (**`Checked 1256 declarations with no typechecker errors` in `0.535 s` / `43.34 MB` RSS**; negative `permitted_axioms = []` probe rejected `rc = 1`).

> **Scope Caution:** `VrustcFormal.F1_3` models an abstract functional `PhysFrame` and two-frame `PhysShim` IR over a closed `4`-target × `3`-release × `3`-convention × `9`-type epoch table. It does **not** verify native machine-code register sequentialization, caller-saved `sret` spilling across hardware `call`, LLVM `SelectionDAG`/`GlobalISel` lowering, ELF/PE/Mach-O linking, or a mechanical bridge to `joshlf/anneal` `Trusted.MirAst`/`Trusted.MirSemantics`. See `## Boundaries`.

---

## Applicability

### Subject Relationships and Exact Configuration Scope

This report characterizes `support/RustFnAbiBitExactLowering.lean` (namespace `VrustcFormal.F1_3`, `3,388` lines, `158,677` bytes, SHA-256 `8f79d62a6ead93d1013b4cbb0f9989bd79570091f60416adfefea599c57d0cde`) against the empirical compiler ground truth, upstream causal `rust-lang/rust` commits, and multi-kernel verification stack pinned in `REPORT.json`:

- **Pinned `rust-lang/rust` release epochs (`1.99.1` `58cf8f9c35b355199727627d07ae34a4e2846d67`, `1.100.0` `0ef1bc386059596dada8fb65b50425aab2ea637a`, `1.102.0-nightly` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`):** Define the exact three-point `RustcRelease` epoch table grounded in `rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting` (`google/zerocopy@120889696dc131f0fc7cf814e898ee72cd04a19e`).
- **Four causal `rust-lang/rust` ABI commits:**
  - `429c1c18ca616ec5a097019c6071dc8ca75585be` (merged `498b89dd40af107a23c13a009345a0dea224248c`): `D1` (`x86`/`x86_64` `extern "Rust"` `<= 128`-bit `#[repr(simd)]` `Indirect + sret -> Direct(Vector)` between `1.99.1` and `1.100.0`).
  - `a654a240456566a313e53698f42c70ad7366676d` (merged `e3c3417ff6499548c5ab52767489ab262f9a2ac0`): `D2` (`aarch64` `extern "Rust"` `<= 128`-bit NEON `Indirect + sret(x8) -> Direct(Vector)` between `1.100.0` and `1.102.0-nightly`).
  - `916dda0c26e7736748e2ef8233f1fd1477e1be1e`: `D3` (Win64 `extern "C"` and `x86_64` `vectorcall` non-`#[repr(C)]` ZST `Indirect -> Ignore` between `1.100.0` and `1.102.0-nightly`, retaining `Indirect` for `#[repr(C)]` ZSTs via `LayoutData.repr_c`).
  - `d11b3f4d61c50f4149ea34a89302cf24a0c52b86` (merged `62746359572280748adec7b4add65f0a1c26d1a9`): `D4` (pre-lowering Rust `FnAbi` `vectorcall` `@@N` byte-count decoration in `declare_rust_fn`, shifting `x86_64` `abi_vec_hfa4` `.o` symbols from `@@16` to `@@24` between `1.100.0` and `1.102.0-nightly`).
- **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:** Supplies unmodified `trusted/audit/TrustedBoundary.lean` and `trusted/lean/foundation-lock.json` (`schema: 1`, `51` locked Lean `v4.34.1` `Init.*` sysroot modules), plus `Trusted.{MirAst,MirSemantics}` and `Anneal.MirWp` for full Pass 1 `"audit"` co-verification. `VrustcFormal.F1_3` itself imports strictly `4` locked `Init.*` modules (`0` imports from `Trusted.*` or `Anneal.*`).
- **`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):** Locked primary toolchain executing synchronous compilation (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`), `TrustedBoundary.lean` `"preflight"`/`"audit"`, standalone replay, `#print axioms`, and kernel dependency-closure checks.
- **`leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`), `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`3.1.0`), and `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`nanoda_bin 0.4.19`):** Independent cross-version Lean kernel and independent Rust external typechecker verifying all `13` exported public theorems (`1,256` exported declarations).

### Shared vs. Release-Specific Behavior Across Covered Epochs

- **Shared across `{1.99.1, 1.100.0, 1.102.0-nightly}`:** Scalar integer (`1`/`2`/`4`/`8` B), `Option<NonNull<u8>>`, scalar `f32`/`f64` (including `i686SysV` `extern "C"` x87 `st(0)` return vs. `extern "Rust"` bit-preserving GPR return), `hfa2F64`, `hfa4F32` pass modes, `bigStruct (wordCount > 2)`, `extern "C"`/`vectorcall` `simd4F32` direct-vector passing, Win64 `#[repr(C)]` ZST indirect passing, and `i686SysV` `vectorcall` `@@20` / `abi_vec_many6_simd` `@@112` symbol counts.
- **Release-specific transitions:**
  - `1.99.1 -> 1.100.0`: `simdDirectEnabled` flips `false -> true` for `extern "Rust"` `simd4F32` on `sysv64`, `win64Msvc`, and `i686SysV` (`D1`), while `aapcs64` remains `false` (staggered cross-architecture divergence window).
  - `1.100.0 -> 1.102.0-nightly`: `simdDirectEnabled` flips `false -> true` for `aapcs64` `extern "Rust"` (`D2`); `win64ZstIndirect` flips `true -> false` for `reprC = false` ZSTs on `win64Msvc` `extern "C"` and `x86_64` `vectorcall` (`D3`); and `vectorcallArgDecorBytes` switches non-`byval` indirect arguments from post-lowering pointer width (`ptrBytes`) to pre-lowering `nextMultipleOf (tyByteSize ty) ptrBytes` (`D4`).

### Frozen Contract Integrity & Generalization Envelope

Stripping only the strictly `private` helper block (`L1477–L2967`: `2 private def`, `78 private theorem`) from `support/RustFnAbiBitExactLowering.lean` and replacing the `4` Part VI theorem proof bodies (`L2994`, `L3036`, `L3076`, `L3173`) with `  sorry` reconstructs the pre-proof frozen statement (`1,794` lines, `81,568` bytes, SHA-256 `7b13cd7b8d86fc602ce21ac95d8c639f9dd063e9e04cc500222d64fd9f838535`) **byte-for-byte**.

Claims apply strictly to the `4` modeled targets (`sysv64`, `win64Msvc`, `aapcs64`, `i686SysV`), `3` pinned releases (`1.99.1`, `1.100.0`, `1.102.0-nightly`), `3` calling conventions (`rust`, `c`, `vectorcall`), and `9` `AbiTy` constructors under `sig.args.length + 2 < 2^64`. Do **not** infer ABI stability or classifier accuracy for unprobed `rustc` commits, adjacent releases, or unmodeled targets/types without probing them directly.

---

## Findings

### 1. Release-Fingerprinted Multi-Target `FnAbi` Model and Alignment With Empirical Drift (`Parts I–III`)

`Basis: source + execution (support/RustFnAbiBitExactLowering.lean, L98–L705; rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting @ 120889696dc131f0fc7cf814e898ee72cd04a19e; rust-lang/rust commits 429c1c18, a654a240, 916dda0c, d11b3f4d)`

`VrustcFormal.F1_3` organizes the Rust-compiler-specific ABI classifier into three transparent, tactic-free, locked-`Init.*`-only sections (`L98–L705`):

| Model Component (`RustFnAbiBitExactLowering.lean`) | Exact Constructors / Definitions | Grounded Compiler / Empirical Semantics |
| :--- | :--- | :--- |
| **Universe (`Part I`, `L98–L195`)** | `AbiTarget` (`sysv64`, `win64Msvc`, `aapcs64`, `i686SysV`), `RustcRelease` (`r1_99_1`, `r1_100_0`, `r1_102_0`), `CallConv` (`rust`, `c`, `vectorcall`), `AbiTy` (`zst reprC`, `intScalar bytes`, `float32`, `float64`, `nicheNonNull`, `hfa2F64`, `hfa4F32`, `simd4F32`, `bigStruct wordCount`), `AbiVal`, `valHasTy`, inductive `valsHaveTys`, `checkValHasTy`. | `zst (reprC : Bool)` carries `LayoutData.repr_c` explicitly (commit `916dda0c`). `valsHaveTys` is defined as `inductive` (`L175–L177`) so Lean `v4.34.1` emits zero `isPartial` `._unsafe_rec` auxiliaries under `TrustedBoundary.lean`. |
| **x87 sNaN Model (`Part II`, `L196–L237`)** | `isF32SignalingNaN`, `isF64SignalingNaN`, `x87TransferF32` (`+ 0x00400000`), `x87TransferF64` (`+ 0x0008000000000000`), `isNonSignalingRet`. | Models `i686` `extern "C"` x87 `st(0)` return quietening bit 22 (`f32`) / bit 51 (`f64`) vs. `extern "Rust"` `<4/8 x i8>` GPR return preserving all IEEE-754 bits. Uses prefix `Nat.div`/`Nat.mod` only (`0` banned infix `^`/`/`/`%` syntax). |
| **Register & Epoch Predicates (`Part III`, `L240–L454`)** | `ArgPassMode` (10 modes incl. `directPairF64`, `directQuadF32`, `directVec128`, `indirectGpr`, `indirectStack byval`, `directStack`), `SretLoc` (`none`, `gpr0`, `gpr8`, `stack0`), `RetPassMode`, `LinkerSymbolRule` (`undecorated \| vectorcallAtAt bytes`), `maxGprArgs`, `maxFloatXmmArgs`, `maxVecXmmArgs`, `simdDirectEnabled`, `win64ZstIndirect`, `usesWin64PositionalSlots`. | `simdDirectEnabled` encodes `D1` (`x86_64`/`i686` `1.99.1 -> 1.100.0`) and `D2` (`aapcs64` `1.100.0 -> 1.102.0`). `win64ZstIndirect` encodes `D3` (`win64Msvc` `extern "C"` and `x86_64` `vectorcall` flipping `reprC = false` to `Ignore` in `1.102.0` while keeping `reprC = true` `Indirect`). `maxVecXmmArgs` separates `i686SysV` SSE2 vector registers (`xmm0..xmm2`, cap `3`) from stack-passed scalar floats (`maxFloatXmmArgs = 0`). |
| **Classification & `sret` Allocation (`L456–L606`)** | `classifyOneArg`, `classifyArgsLoop`, `targetSretLoc`, `classifyRet`, `classifyFnAbi`. | `targetSretLoc .aapcs64 = .gpr8` (`x8`) keeps `initGpr = 0` (`x0..x7` unshifted), whereas `sysv64`/`win64Msvc` consume `gpr0` (`rdi`/`rcx`, advancing `initXmm = 1` under Win64 synchronized positional slots) and `i686SysV` consumes `stack0`. Direct-SIMD overflow spills to `.directStack stkIdx .simd4F32` (`stkIdx + 2`), preserving `abi_vec_many6_simd` `@@112`. `hfa4F32` reproduces the 4-way `extern "C"` split vs. universal `extern "Rust"` `sret + indirect`. |
| **Formulaic `.o` Symbol Decoration & Fingerprints (`L608–L705`)** | `tyByteSize`, `targetPtrBytes`, `nextMultipleOf`, `vectorcallArgDecorBytes`, `computeSymbolRule`, `irOnlyCompatible`, `fullAbiCompatible`. | `vectorcallArgDecorBytes` derives `D4` formulaically with zero magic constants: pre-`1.102.0` LLVM MC sums `ptrBytes` for non-`byval` indirect args vs. `1.102.0` `rustc` summing `nextMultipleOf (tyByteSize ty) ptrBytes` (`abi_vec_hfa4`: `8 + 8 = 16 -> 16 + 8 = 24` on `x86_64`, `16 + 4 = 20` on `i686` `byval`; `bigStruct 3`: `8 -> 24` on `x86_64`, `24 -> 24` on `i686`). `LinkerSymbolRule` separates `undecorated` from `vectorcallAtAt 0` (`D5`), and `ComputedFnAbi` includes `conv`. |

---

### 2. Word-Serialized `PhysFrame` Marshaling (`Part IV`) and Mechanically `AbiVal`-Free `PhysShim` IR (`Part V`)

`Basis: source + execution (support/RustFnAbiBitExactLowering.lean, L708–L1476; Lean v4.34.1 kernel dependency-closure audit)`

#### Word-Serialized Physical Frame and Disjoint `sret` Threading (`Part IV`, `L708–L1144`)

`PhysFrame` (`L723–L731`) stores registers (`gprs`, `xmms`), stack slots (`stack`), x87 return slots (`x87F32`, `x87F64`), an allocation counter (`nextTok`, initialized to `1`), and indirect memory **`mem : List (Nat × List (BitVec 64))`** containing **raw 64-bit machine words**—never unserialized `AbiVal` ASTs.

- **Bit-exact word codecs (`L759–L827`):** `encodeValWords` and `decodeValWords` pack and unpack every `AbiVal` (`f32`, `f64`, `intScalar`, `nicheNonNull`, `hfa2F64`, `hfa4F32` via `pack2x32`/`unpackLo32`/`unpackHi32`, `simd4F32` via `pack2x64`/`trunc128To64`/`hi64Of128`, and `bigStruct ws`) strictly via prefix `Nat.div`/`Nat.mod`, enforcing `checkValHasTy` and exact word lengths on both marshaling and decoding.
- **Disjoint caller-allocated `sret` buffer (`L829–L848`, `L1010–L1069`):** `marshalArgs` invokes `initSretBuffer abi.sretLoc emptyFrame` **before** marshaling arguments, allocating any `sret` buffer at token `1` in `gpr0`, `gpr8`, or `stack0` so subsequent indirect argument buffers receive disjoint tokens `>= 2`. `marshalRet fCall abi.retMode retVal` then writes `.indirectSret` return words directly into `fCall`'s caller-allocated token (`writeMemWords`), preventing argument/return token aliasing.

#### Non-Tautological `AbiVal`-Free `PhysShim` IR (`Part V`, `L1145–L1476`)

To guarantee that cross-release adapter refinement is **not** a tautological `unmarshal >>= marshal` roundtrip smuggling typed `AbiVal`s through the shim:

- `compileShimPlan (abiCaller abiCallee : ComputedFnAbi) (sig : FnSig) : CompiledShimPlan` (`L1283–L1294`) compiles two-phase raw-word register/stack/memory read and write op lists (`PhysReadOp`, `PhysWriteOp`, `PhysRetReadOp`, `PhysRetWriteOp`) plus explicit `needsLinkerAlias := !symbolRuleEq abiCaller.symbolRule abiCallee.symbolRule` strictly from static ABI metadata.
- `execArgShim` (`L1396–L1402`) executes Phase 1 (`execPhysReads fCaller plan.argReads`) into a raw `List (List (BitVec 64))` scratch buffer, allocates any callee `sret` buffer via `initSretBuffer plan.calleeSretLoc emptyFrame`, and executes Phase 2 (`execPhysWrites`) into `fCallee`.
- `execRetShim` (`L1471–L1475`) reads raw words from `fCalleeOut` (`execRetRead`) and writes them into `fCallerIn` (`execRetWrite`), populating `fCallerIn`'s caller-allocated `sret` buffer when `plan.retWrite = .writeIndirectSret loc`.
- **Mechanized kernel isolation receipt (`[real measurement]`):** Computing the transitive kernel dependency closure over all **`20` `PhysShim` declarations** (`PhysReadOp`, `PhysWriteOp`, `PhysRetReadOp`, `PhysRetWriteOp`, `CompiledShimPlan`, `compileArgReadOp`, `compileArgWriteOp`, `compileArgReads`, `compileArgWrites`, `compileRetReadOp`, `compileRetWriteOp`, `compileShimPlan`, `execPhysRead`, `execPhysWrite`, `execPhysReads`, `execPhysWrites`, `execArgShim`, `execRetRead`, `execRetWrite`, `execRetShim`) visits **`669` kernel constants** and confirms **`0` references (`bannedHits = []`)** to `AbiVal`, `encodeValWords`, `decodeValWords`, `marshalOneArg`, `unmarshalOneArg`, `marshalArgs`, `unmarshalArgs`, `marshalRet`, `unmarshalRet`, `valHasTy`, `valsHaveTys`, or `checkValHasTy`.

---

### 3. Four Core Kernel-Checked Theorems (`Part VI`) and Constructive Proof Architecture

`Basis: source + execution (support/RustFnAbiBitExactLowering.lean, L1477–L3189; [kernel-checked proof])`

#### Verbatim Public Signatures of the Four Core Theorems (`L2983–L3173`)

All four theorem types originate strictly from `VrustcFormal.F1_3` and `Init.{Prelude,Core}` (`0` `Trusted.*` or `Anneal.*` references, axioms strictly `[propext]`):

```lean
theorem same_abi_marshal_roundtrip
    (t : AbiTarget) (rel : RustcRelease) (sig : FnSig)
    (hArity : sig.args.length + 2 < Nat.pow 2 64)
    (vals : List AbiVal) (hVals : valsHaveTys vals sig.args)
    (retVal : AbiVal) (hRet : valHasTy retVal sig.ret) :
    let abi := classifyFnAbi t rel sig
    ∃ fCall,
      marshalArgs abi vals = .ok fCall ∧
      unmarshalArgs abi sig.args fCall = .ok vals ∧
      ((isX87RetMode abi.retMode = false ∨ isNonSignalingRet retVal) →
        ∃ fOut, marshalRet fCall abi.retMode retVal = .ok fOut ∧
                unmarshalRet abi.retMode sig.ret fOut = .ok retVal)

theorem fullAbiCompatible_preserves_call_boundary
    (t₁ t₂ : AbiTarget) (rel₁ rel₂ : RustcRelease) (sig : FnSig)
    (hArity : sig.args.length + 2 < Nat.pow 2 64)
    (hCompat : fullAbiCompatible (classifyFnAbi t₁ rel₁ sig) (classifyFnAbi t₂ rel₂ sig) = true)
    (vals : List AbiVal) (hVals : valsHaveTys vals sig.args)
    (retVal : AbiVal) (hRet : valHasTy retVal sig.ret) :
    let abi₁ := classifyFnAbi t₁ rel₁ sig
    let abi₂ := classifyFnAbi t₂ rel₂ sig
    abi₁.symbolRule = abi₂.symbolRule ∧
    abi₁.conv = abi₂.conv ∧
    ∃ fCall,
      marshalArgs abi₁ vals = .ok fCall ∧
      unmarshalArgs abi₂ sig.args fCall = .ok vals ∧
      ((isX87RetMode abi₂.retMode = false ∨ isNonSignalingRet retVal) →
        ∃ fOut, marshalRet fCall abi₂.retMode retVal = .ok fOut ∧
                unmarshalRet abi₁.retMode sig.ret fOut = .ok retVal)

theorem phys_shim_bridge_restores_equivalence
    (t : AbiTarget) (rel₁ rel₂ : RustcRelease) (sig : FnSig)
    (hArity : sig.args.length + 2 < Nat.pow 2 64)
    (vals : List AbiVal) (hVals : valsHaveTys vals sig.args)
    (retVal : AbiVal) (hRet : valHasTy retVal sig.ret) :
    let abi₁ := classifyFnAbi t rel₁ sig
    let abi₂ := classifyFnAbi t rel₂ sig
    let plan := compileShimPlan abi₁ abi₂ sig
    (plan.needsLinkerAlias = true ↔ abi₁.symbolRule ≠ abi₂.symbolRule) ∧
    ∃ fCaller fCallee,
      marshalArgs abi₁ vals = .ok fCaller ∧
      execArgShim plan fCaller = .ok fCallee ∧
      unmarshalArgs abi₂ sig.args fCallee = .ok vals ∧
      (((isX87RetMode abi₁.retMode = false ∧ isX87RetMode abi₂.retMode = false) ∨
        isNonSignalingRet retVal) →
        ∃ fCalleeOut fCallerOut,
          marshalRet fCallee abi₂.retMode retVal = .ok fCalleeOut ∧
          execRetShim plan fCaller fCalleeOut = .ok fCallerOut ∧
          unmarshalRet abi₁.retMode sig.ret fCallerOut = .ok retVal)

theorem fingerprint_and_universal_x87_sharpness :
    (∃ t rel₁ rel₂ sig,
      irOnlyCompatible (classifyFnAbi t rel₁ sig) (classifyFnAbi t rel₂ sig) = true ∧
      fullAbiCompatible (classifyFnAbi t rel₁ sig) (classifyFnAbi t rel₂ sig) = false) ∧
    (∀ b : BitVec 32, isF32SignalingNaN b = true →
      let cAbi := classifyFnAbi .i686SysV .r1_99_1 { conv := .c, args := [], ret := .float32 }
      let rAbi := classifyFnAbi .i686SysV .r1_99_1 { conv := .rust, args := [], ret := .float32 }
      (∃ fC out, marshalRet emptyFrame cAbi.retMode (.float32 b) = .ok fC ∧
                 unmarshalRet cAbi.retMode .float32 fC = .ok (.float32 out) ∧
                 out ≠ b ∧ isF32SignalingNaN out = false) ∧
      (∃ fR, marshalRet emptyFrame rAbi.retMode (.float32 b) = .ok fR ∧
             unmarshalRet rAbi.retMode .float32 fR = .ok (.float32 b))) ∧
    (∀ b : BitVec 64, isF64SignalingNaN b = true →
      let cAbi := classifyFnAbi .i686SysV .r1_99_1 { conv := .c, args := [], ret := .float64 }
      let rAbi := classifyFnAbi .i686SysV .r1_99_1 { conv := .rust, args := [], ret := .float64 }
      (∃ fC out, marshalRet emptyFrame cAbi.retMode (.float64 b) = .ok fC ∧
                 unmarshalRet cAbi.retMode .float64 fC = .ok (.float64 out) ∧
                 out ≠ b ∧ isF64SignalingNaN out = false) ∧
      (∃ fR, marshalRet emptyFrame rAbi.retMode (.float64 b) = .ok fR ∧
             unmarshalRet rAbi.retMode .float64 fR = .ok (.float64 b)))
```

#### Constructive Private Proof Architecture (`L1477–L2967`: `2 private def`, `78 private theorem`)

Every proof step is constructive (`0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`):

| Proof Layer | Lines | Core Private Definitions & Theorems | Mathematical Role |
| :--- | :---: | :--- | :--- |
| **Bit-Packing & Nat Arithmetic** | `L1482–L1710` | `nat_eq_of_beq`, `nat_lt_of_blt`, `bv_eq_of_toNat`, `trunc64To32_zext32To64`, `unpackLo32_pack2x32`, `unpackHi32_pack2x32`, `trunc128To64_pack2x64`, `hi64Of128_pack2x64`, `pack2x64_trunc_hi` | Proves exact bit-level invertibility of 32/64/128-bit packing and zero-extension using only `Init.Data.Nat.Div.Basic` and `Init.Data.BitVec.BasicAux`. |
| **Structural Reflection** | `L1711–L1793` | `targetEq_eq`, `convEq_eq`, `abiTyEq_eq`, `argModeListEq_eq`, `retModeEq_eq`, `symbolRuleEq_iff`, `fullAbiCompatible_eq` | Reflects boolean compatibility checks into propositional equality (`fullAbiCompatible a b = true → a = b`), discharging Theorem 2 in 4 lines from Theorem 1 and the `needsLinkerAlias` biconditional of Theorem 3. |
| **Word Codec & `assocLookup`** | `L1794–L1880` | `checkValHasTy_of_valHasTy`, `decodeValWords_encodeValWords`, `assocLookup_same`, `assocLookup_ne` | Proves every well-typed `AbiVal` survives `encodeValWords` -> `decodeValWords` bit-exact and establishes frame lookup non-interference. |
| **Cursor Monotonicity & Slot Disjointness** | `L1881–L2097` | `private def ModeBounded`, `maxGprArgs_le_8`, `classifyOneArg_bounded` | Bounds every register index, stack slot, and indirect token written by `classifyOneArg` strictly within `[gIdx, g')`, `[xIdx, x')`, `[stkIdx, s')`, proving GPR indices stay `< 8` (never clobbering AAPCS64 `gpr8` = `x8`!). |
| **Unified Argument Master Theorem** | `L2098–L2541` | `private def FramePreserves`, `marshalOneArg_step`, `marshalArgsLoop_master` | Simultaneously proves `marshalArgs` success, `execPhysWrites` equality, `FramePreserves` (preserving earlier slots + `sret` register/token), `unmarshalArgs` exactness, and `execPhysReads` returning `vals.map encodeValWords`. |
| **Threaded `sret` & Return Master Theorem** | `L2542–L2828` | `initSretBuffer_spec`, `framePreserves_readSretTok`, `classifyRet_sretLoc_consistent`, `marshalRet_step` | Proves `f0.nextTok ≤ 2`, preserves caller `sretTok = 1` across `marshalArgs`, and discharges `marshalRet`/`unmarshalRet`/`execRetRead`/`execRetWrite` equivalence simultaneously. |
| **Universal x87 sNaN Quietening** | `L2829–L2965` | `nat_div_add_exact`, `nat_mod_2_add1_of_eq0`, `x87_f32_snan_quietens`, `x87_f64_snan_quietens` | Proves universally over `BitVec 32` and `BitVec 64` that setting bit 22 / bit 51 strictly changes the bitvector (`out ≠ b`) and clears `isF{32,64}SignalingNaN` to `false`. |

---

### 4. Complete Inventory of All `13` Public User Theorems (`4` Core + `9` Empirical Witnesses/Canaries)

`Basis: source + execution (support/RustFnAbiBitExactLowering.lean, L2983–L3386; Lean v4.34.1 #print axioms and DAG closure; [kernel-checked proof])`

Every public user theorem depends **solely on `[propext]`** (`0` `Classical.choice`, `0` `Quot.sound`), and all `9` empirical witnesses and canaries (`L3199–L3386`) discharge cleanly via kernel `rfl`:

| # | Public Theorem (`VrustcFormal.F1_3`) | Role | Exact Property Established | Axioms | Reachable Decls | Type Origin Modules |
| :-: | :--- | :--- | :--- | :--- | ---: | :--- |
| 1 | `same_abi_marshal_roundtrip` | Core 1 | Bit-exact `marshalArgs`/`unmarshalArgs` + threaded `sret` `marshalRet`/`unmarshalRet` for all `(t, rel, sig)` under `sig.args.length + 2 < 2^64`. | `[propext]` | `1,086` | `F1_3`, `Init.{Prelude,Core}` |
| 2 | `fullAbiCompatible_preserves_call_boundary` | Core 2 | `fullAbiCompatible = true` guarantees equal `symbolRule`, equal `conv`, and direct bit-exact call/return boundary preservation without a shim. | `[propext]` | `1,159` | `F1_3`, `Init.{Prelude,Core}` |
| 3 | `phys_shim_bridge_restores_equivalence` | Core 3 | Statically compiled, `AbiVal`-free `PhysShim` restores bit-exact argument & return transport for any `(t, rel₁, rel₂, sig)` and flags `needsLinkerAlias ↔ symbolRule` mismatch. | `[propext]` | `1,110` | `F1_3`, `Init.{Prelude,Core}` |
| 4 | `fingerprint_and_universal_x87_sharpness` | Core 4 | Witnesses `D4` (`irOnlyCompatible = true ∧ fullAbiCompatible = false`) and proves universal `f32`/`f64` sNaN alteration on `i686SysV` `extern "C"` vs. bit-exact preservation on `extern "Rust"`. | `[propext]` | `892` | `F1_3`, `Init.{Prelude,Core}` |
| 5 | `ce_d1_x86_64_and_i686_simd_1_99_1_vs_1_100_0` | Witness `D1` | `sysv64` and `i686SysV` `extern "Rust"` `simd4F32` break `1.99.1 -> 1.100.0` (`.error .missingReg`), while `win64Msvc` `extern "C"` SIMD stays stable across `1.99.1..1.102.0`. | `[propext]` | `758` | `F1_3`, `Init.Prelude` |
| 6 | `ce_d2_aarch64_neon_x8_sret_and_1_100_0_vs_1_102_0` | Witness `D2` | `aapcs64` `extern "Rust"` NEON uses `sretLoc = .gpr8` (`x8`) with `argModes = [.indirectGpr 0 .simd4F32]` (`x0`), stable `1.99.1 = 1.100.0`, breaking `1.100.0 -> 1.102.0` (`.missingReg`). | `[propext]` | `757` | `F1_3`, `Init.Prelude` |
| 7 | `ce_d3_win64_zst_non_repr_c_1_100_0_vs_1_102_0` | Witness `D3` | `win64Msvc` `extern "C"` non-`#[repr(C)]` ZST (`reprC = false`) stays stable `1.99.1 = 1.100.0`, breaks `1.100.0 -> 1.102.0` with silent shift corruption (`0xCAFEBABE` replaced by ZST token `1` in `rcx`), while `reprC = true` stays compatible across `1.99.1..1.102.0`. | `[propext]` | `758` | `F1_3`, `Init.Prelude` |
| 8 | `ce_d4_vectorcall_hfa4_and_bigstruct_linker_breaks` | Witness `D4` | 2-arg `vectorcall` `(HfaF32x4, f32) -> HfaF32x4` has `irOnlyCompatible = true` yet `fullAbiCompatible = false` (`@@16 -> @@24` on `sysv64`, `@@20 -> @@20` on `i686SysV`); `bigStruct 3` breaks `@@8 -> @@24` on `sysv64`. | `[propext]` | `598` | `F1_3`, `Init.Prelude` |
| 9 | `ce_d5_no_undecorated_vs_vectorcall_at0_collision` | Witness `D5` | `0`-arg `extern "C"` (`undecorated`) vs. `extern "vectorcall"` (`vectorcallAtAt 0`) yields `fullAbiCompatible = false` (zero sentinel collision). | `[propext]` | `596` | `F1_3`, `Init.Prelude` |
| 10 | `ce_d6_i686_x87_snan_quietening_vs_rust_bit_exact` | Witness `D6` | `i686SysV` `extern "C"` quietens `f32` sNaN `0x7f800001 -> 0x7fc00001`; `extern "Rust"` preserves `0x7f800001` bit-for-bit. | `[propext]` | `695` | `F1_3`, `Init.Prelude` |
| 11 | `canary_p1_sysv64_niche_hfa2_cross_release_stable` | Canary `P1` | `sysv64` `extern "Rust"` `(nicheNonNull, hfa2F64, u32) -> hfa2F64` stays `fullAbiCompatible = true` across `1.99.1 -> 1.100.0 -> 1.102.0` and preserves `f64` sNaN `0x7ff0000000000001`. | `[propext]` | `757` | `F1_3`, `Init.Prelude` |
| 12 | `canary_p2_phys_shim_fixes_d3_and_d1_end_to_end` | Canary `P2` | `PhysShim` recovers `0xCAFEBABE` across Win64 `D3` (`1.100.0 -> 1.102.0`) and bridges `sysv64` `D1` (`1.99.1 <-> 1.100.0`) end-to-end including caller `sret` return buffer population. | `[propext]` | `826` | `F1_3`, `Init.Prelude` |
| 13 | `canary_p3_vectorcall_many6_hfa2_zst_and_i686_byval` | Canary `P3` | `abi_vec_many6_simd` (`7 × F32x4`) stays `@@112 -> @@112` on `sysv64`/`win64Msvc`/`i686SysV`; `sysv64` `vectorcall` `hfa2F64` breaks `@@8 -> @@16`; `sysv64` `vectorcall` ZST (`reprC = false` & `true`) breaks `@@16 -> @@8`; `i686SysV` `vectorcall` `bigStruct 3` (`byval`) stays `@@24 -> @@24`. | `[propext]` | `601` | `F1_3`, `Init.Prelude` |

---

### 5. Multi-Kernel Verification, Unmodified `TrustedBoundary.lean` Pass 1 Audit & Replay, and `nanoda_bin 0.4.19` Receipts

`Basis: execution (recorded 2026-11-20 across unmodified joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613, Lean v4.34.1, Lean v4.35.0, lean4export 3.1.0, and nanoda_bin 0.4.19; [real measurement])`

Every theorem in `support/RustFnAbiBitExactLowering.lean` was independently verified across **three distinct kernel implementations/versions** (Lean `v4.34.1` C++ kernel + unmodified Anneal `TrustedBoundary.lean` Pass 1 replay, Lean `v4.35.0` C++ kernel, and the independent Rust external typechecker `nanoda_bin 0.4.19`):

| Verification Step / Checker | Pinned Revision | Mode & Configuration | Exit | Wall (s) | User / Sys (s) | Peak RSS (MB) | Measured Outcome |
| :--- | :--- | :--- | :---: | ---: | :---: | ---: | :--- |
| **1. `foundation-lock.json` integrity** | `anneal@c131b320e` | Verify `51/51` `v4.34.1` sysroot modules (`.lean`, `.olean*`, `.ir*`) + `bin/lean` binary SHA-256 (`e8baaa71...`) | `0` | — | — | — | **`51 / 51` matched (`0` SHA-256 mismatches)** |
| **2a. Lean `v4.34.1` Run A (direct)** | `lean4@5045d005` | `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` | `0` | `17.103` | `17.88 / 0.36` | `478.79` | `0` errs/warns/`sorry`; `.olean` = `13,532,816 B` (`20.673 s` / `468.90 MB` on contended run) |
| **2b. Lean `v4.34.1` Run B (`--setup`)** | `lean4@5045d005` | `anneal-audit`-style `--setup` as `Anneal.F1_3_Proof` (`-j1 -M2048 -t0`) | `0` | `19.854` | — | `467.73` | `0` errs/warns/`sorry`; `.olean` = `13,538,304 B` |
| **3a. `TrustedBoundary` `"preflight"`** | `anneal@c131b320e` | `SourceRole.theory`, `4` locked `Init.*` imports, explicit `prelude` | `0` | `4.099` | — | `798.36` | **`ok = true`**, `trustTier = null` |
| **3b. `"preflight"` negative probe** | `anneal@c131b320e` | Frozen pre-proof file containing `4` `sorry` stubs | `1` | `3.775` | — | `780.86` | Fail-closed: `policy:unsupported syntax kind Lean.Parser.Tactic.tacticSorry` |
| **4a. `TrustedBoundary` Full Pass 1 `"audit"`** | `anneal@c131b320e` | `trustLevel := 0`, `plugins := #[]`, `loadExts := false`, `requireMirWp = true`, merged foundation + preflight-header DAG (`Trusted`, `Trusted.MirAst`, `Trusted.MirSemantics`, `Anneal.MirWp`, `Anneal.F1_3_Proof`) | **`0`** | `7.526` | `8.12 / 0.41` | `882.89` | **`ok = true`, `replay = true`**, `kernelDeclarations = 1,324`, **`replayedDeclarations = 3,337`**, `checkedAlternateProofs = 0`, `compilerOnlyNames = 281`, `reachableDeclarations = 4,184`, **`axioms = ["propext"]`** |
| **4b. `TrustedBoundary` Standalone Pass 1 `"audit"`** | `anneal@c131b320e` | `trustLevel := 0`, `plugins := #[]`, `loadExts := false`, `requireMirWp = false`, `theory = [Anneal.F1_3_Proof]` | **`0`** | `5.438` | `6.30 / 0.39` | `851.02` | **`ok = true`, `replay = true`**, **`replayedDeclarations = 1,756`**, `reachableDeclarations = 2,396`, **`axioms = ["propext"]`** |
| **5. Deep kernel scan + standalone replay + `PhysShim` closure** | `lean4@5045d005` | Replay `1,756` decls onto locked `51`-module foundation + inspect all `20` `PhysShim` decls | `0` | `0.863` (`#print axioms`) | — | — | **`1,756 / 1,756` replayed (`OK`)**; `0` forbidden constructs; **`0 / 669` `AbiVal` refs in `PhysShim`** |
| **6. Lean `v4.35.0` (unmodified)** | `lean4@eb6cafb7` | `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` | **`0`** | `17.614` | `18.37 / —` | `446.23` | `0` errs/warns; `.olean` = `13,502,544 B` |
| **7. `lean4export 3.1.0`** | `lean4export@5a9a355d` | Export all `13` public user theorems to NDJSON | **`0`** | `0.916` | `0.71 / —` | `434.85` | **`9,543,273 B`** (`183,552` lines; `62` inductives, `642` defs, `329` thms, `1` axiom = `propext`) |
| **8a. `nanoda_bin 0.4.19` (positive)** | `nanoda_lib@0da9f98f` | `permitted_axioms = ["propext"]`, `unpermitted_axiom_hard_error = true`, `nat_extension = true`, `string_extension = true` | **`0`** | **`0.535`** | **`0.49 / —`** | **`43.34`** | **`Checked 1256 declarations with no typechecker errors`** *(1 cosmetic note `"Unable to print axioms"`)* |
| **8b. `nanoda_bin` (negative probe)** | `nanoda_lib@0da9f98f` | `permitted_axioms = []`, `unpermitted_axiom_hard_error = true` | **`1`** | `0.010` | `0.00 / —` | `3.89` | Fail-closed: `Error: export file declares unpermitted axiom "propext"` |
| *(Note) `lean4lean`* | Host binary | Attempted on compiled `v4.35.0` `.olean` | `1` | `0.214` | `0.10 / —` | `80.92` | **Not exercised:** older `.olean` format (`incompatible header`). |

**Zero-Hit Hygiene Scan (`[real measurement]`):** Across all `1,756` module constants (`1,316` public, `440` private, `335` `extraConstNames`) and `2,396` transitively visited declarations: `0` `isUnsafe`, `0` `isPartial`, `0` `._unsafe_rec`, `0` `opaqueInfo`/`axiomInfo`/`quotInfo`, `0` `sorryAx`/`Expr.hasSorry`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `Lean.ofReduceBool`/`ofReduceNat`/`trustCompiler`/`reduceBool`/`reduceNat`, `0` `Trusted` root-namespace declarations, `0` `Anneal.*` references, `0` banned infix `^`/`/`/`%` syntax hits, and `0` CRLF or bidi/invisible/control Unicode anomalies.

**`TrustedBoundary.lean` Pass 1 DAG Merge Requirement (`[real measurement]`):** In `TrustedBoundary.lean:2282–2292`, `"preflight"` returns `"graph"` containing only the `51` foundation `Init.*` modules while emitting repository module imports separately in `"headers"`, whereas `"audit"` (`TrustedBoundary.lean:432–435`, `1524`) checks the compiled environment's full import DAG against `j["graph"]`. Matching production `anneal-audit` (`trusted/audit/src/lib.rs:2738`) by merging preflight `"headers"` into the foundation graph before invoking `"audit"` passes both full Anneal (`3,337` replayed decls) and standalone (`1,756` replayed decls) replay cleanly.

**External-Checker Efficiency (`[real measurement]`):** `nanoda_bin 0.4.19` re-verifies the entire `1,256`-declaration exported closure in **`0.535 s` and `43.34 MB` peak RSS**—**`32.0×` faster / `11.0×` leaner** than Lean `v4.34.1` (`17.103 s` / `478.79 MB`) and **`32.9×` faster / `10.3×` leaner** than Lean `v4.35.0` (`17.614 s` / `446.23 MB`).

---

### 6. Analytical Dimensions Scorecard (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

`Basis: execution + source + derived ([real measurement] and [kernel-checked proof])`

| Dim | Category | Measured Status / Assessment |
| :-: | :--- | :--- |
| **`L1`** | Authoring & proof velocity | `[real measurement]` `1,794`-line (`81,568 B`) frozen statement + `1,491`-line strictly `private` proof (`3,388` lines, `158,677 B`, `204` source decls, `91` theorems) proved (`0` `sorry`) and 3-kernel + `TrustedBoundary.lean` verified on `2026-11-20`. |
| **`L2`** | Toolchain / TCB build time | `[real measurement]` Zero external Lean packages beyond locked `Init.*` (`4` imports); standalone compile takes `17.103 s` (`v4.34.1`) / `17.614 s` (`v4.35.0`). |
| **`L3`** | Pass / shim synthesis latency | `[derived]` `compileShimPlan` is a single linear pass ($O(|\text{args}|)$) over `ComputedFnAbi`, but marked `noncomputable`; native executable synthesis latency is **`not measured`**. |
| **`L4`** | Generated code performance | **`not measured`** — Models abstract functional `PhysFrame` / `PhysShim` IR only; emits no native machine code or ELF/PE/Mach-O object files. |
| **`L5`** | Checking latency & throughput | `[real measurement]` Lean kernel: `17.103–20.673 s` (`v4.34.1`) / `17.614 s` (`v4.35.0`); `TrustedBoundary.lean`: `4.099 s` preflight + `7.526 s` full audit (`3,337` decls) / `5.438 s` standalone (`1,756` decls); `lean4export`: `0.916 s`; **`nanoda_bin 0.4.19`: `0.535 s` (`1,256` decls, `~2,348` decls/s).** |
| **`L6`** | RAM & artifact footprint | `[real measurement]` Source `158,677 B`; `.olean` `13.53 MB` (`v4.34.1`) / `13.50 MB` (`v4.35.0`); NDJSON `9.54 MB`; peak RSS `468.90–478.79 MB` (`v4.34.1`), `446.23 MB` (`v4.35.0`), `434.85 MB` (`lean4export`), `798.36–882.89 MB` (`TrustedBoundary.lean`), **`43.34 MB` (`nanoda_bin`)**. |
| **`C1`** | Spec & assumption auditability | `[real measurement]` `1,476`-line specification/classifier/`PhysShim` prefix + `4` theorem types referencing only `Init.{Prelude,Core}` (`0` `Trusted.*`/`Anneal.*`, `[propext]` only); exact `81,568`-byte frozen SHA-256 reconstruction; `0 / 669` `AbiVal` refs in `PhysShim`. |
| **`C2`** | Orthogonality & simplicity | `[derived]` One unified master argument theorem (`marshalArgsLoop_master`) and one unified return theorem (`marshalRet_step`) discharge both `same_abi_marshal_roundtrip` and `phys_shim_bridge_restores_equivalence`; formulaic `vectorcallArgDecorBytes` captures `D4` without hardcoded per-signature sizes. |
| **`V1`** | Adequacy, mutation & non-vacuity | `[kernel-checked proof]` + `[real measurement]` `9` kernel-`rfl` witnesses/canaries (`D1`–`D6`, `P1`–`P3`) grounded in `rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting`, live `rustc +1.100.0` adversarial probe on Win64 `HfaF64x2`, and paired fail-closed probes on `TrustedBoundary.lean` (`sorry`) and `nanoda_bin` (`permitted_axioms = []`). |
| **`V2`** | Differential fuzzing | **`not measured`** — Validated against the `9`-target × `3`-release deterministic matrix (`2,499` compiled instances) and targeted live `rustc` probes, not randomized ABI fuzzing. |
| **`V3`** | Weak-memory / crash / silicon | **`known not to apply`** — Pure sequential call-boundary marshaling model (no concurrency, atomics, traps, or hardware FPU status/control registers). |
| **`V4`** | Held-out ecosystem replay | **`not examined`** — Not mechanically extracted from or replayed over arbitrary crate `FnAbi` tables emitted by `rustc_target::callconv`. |

---

## Boundaries

### Honest Scope & Non-Claims (`VrustcFormal.F1_3`)

**What `VrustcFormal.F1_3` proves (`[kernel-checked proof]`):** Over a standalone, locked-`Init.*`-only Lean 4 formalization grounded in the `rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting` `9`-target × `3`-release (`rustc 1.99.1`, `1.100.0`, `1.102.0-nightly`) empirical ABI matrix—using **only `propext`** (`0` `Classical.choice`, `0` `Quot.sound`, `0` `sorry`, `0` `unsafe`/`partial`/`_unsafe_rec`; independently kernel-checked by Lean `v4.34.1` + unmodified Anneal `TrustedBoundary.lean` Pass 1 replay, Lean `v4.35.0`, and the Rust external typechecker `nanoda_bin 0.4.19` over `1,256` exported declarations)—`VrustcFormal.F1_3` mechanizes:
1. **Same-fingerprint bit-exact call-boundary roundtrip** (`same_abi_marshal_roundtrip`): under the finite-frame bound `sig.args.length + 2 < 2^64`, for every `(target, release, sig)` in the modeled `4`-target × `3`-release × `3`-convention × `9`-type universe and every well-typed `(vals, retVal)`, marshaling into word-serialized `PhysFrame` registers/stack/indirect-memory (allocating any caller `sret` buffer at token `1` disjoint from argument tokens `≥ 2`) and unmarshaling recovers `vals` bit-for-bit, and threaded return marshaling into the same call frame recovers `retVal` bit-for-bit whenever either `isX87RetMode abi.retMode = false` or `isNonSignalingRet retVal`.
2. **Fingerprinted compatibility preservation** (`fullAbiCompatible_preserves_call_boundary`): whenever `fullAbiCompatible` holds on two classifications of `sig`, they share identical `(target, conv, argModes, retMode, sretLoc, symbolRule)` (with no `0` vs. `@@0` sentinel collision) and preserve the call boundary directly without an adapter shim (established by structural reflection over the 6-field `ComputedFnAbi` tuple + Theorem 1).
3. **Non-tautological `AbiVal`-free physical-frame adapter-shim refinement** (`phys_shim_bridge_restores_equivalence`): for any same-target release pair `(t, rel₁, rel₂)`, the statically compiled `PhysShim` IR (`compileShimPlan`, `execArgShim`, `execRetShim` — mechanically verified to contain `0` references to `AbiVal`, `encodeValWords`/`decodeValWords`, or `marshal*`/`unmarshal*`) bridges `fCaller` to `fCallee` and `fCalleeOut` back to `fCallerOut` bit-exact via raw `BitVec 64` word transfers (outside x87 sNaN returns), and flags `plan.needsLinkerAlias = true ↔ abi₁.symbolRule ≠ abi₂.symbolRule`.
4. **Sharpness & empirical witnesses** (`fingerprint_and_universal_x87_sharpness` + `9` kernel-`rfl` witnesses `ce_d1`–`ce_d6`, `canary_p1`–`canary_p3`): proves that IR-only fingerprinting misses `rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting`'s real `D4` `x86_64` `vectorcall` `.o` linker break (`@@16 -> @@24`), proves universally that *every* `f32`/`f64` signaling NaN is altered by the modeled `i686` `extern "C"` x87 return while preserved bit-for-bit by `extern "Rust"`, and witnesses `D1` (`x86_64` & `i686` SIMD `1.99.1 -> 1.100.0`), `D2` (`aarch64` NEON `x8` `sret` `1.100.0 -> 1.102.0`), `D3` (Win64 non-`#[repr(C)]` ZST `1.100.0 -> 1.102.0` silent shift vs. `#[repr(C)]` ZST stability), `D4` (`@@16 -> @@24` vs. `i686` `@@20` & `bigStruct 3` `@@8 -> @@24`), `D5` (`undecorated` vs. `@@0`), and `P1`–`P3` (including `abi_vec_many6_simd` `@@112` stack overflow and `x86_64` `vectorcall` `hfa2F64`/ZST rules).

**Explicit Non-Claims & Trust Boundaries:**
- **Abstract `PhysFrame` / functional `PhysShim`, not native machine code or in-place register sequentialization:** `PhysFrame` models abstract register maps, stack slots, and token-indexed `List (BitVec 64)` buffers. `execArgShim` buffers into an unbounded functional scratch list and writes into a fresh `emptyFrame` (no in-place parallel-move cycle breaking, no shared-memory pointer aliasing, no callee-saved register preservation, no 16-byte `rsp` alignment, Win64 32-byte shadow space, SysV64 128-byte red zone, or `i686` 32-bit/4-byte slot granularity). `execRetShim` receives the caller's untouched `fCaller` directly as a functional continuation, abstracting away the hardware requirement to spill volatile/caller-saved `sret` pointers (`rdi`/`rcx`) across a real `call`.
- **Strict subset of `rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting` & `rustc_abi::Layout`, total epoch table:** Covers `4` targets (`sysv64`, `win64Msvc`, `aapcs64`, `i686SysV`), `3` pinned releases (`1.99.1`, `1.100.0`, `1.102.0`), `3` calling conventions (`rust`, `c`, `vectorcall`), and `9` `AbiTy` constructors. Explicitly omits `i686-pc-windows-msvc` (and `D4a` `stdcall`/`fastcall`/`system` `@N` / callee-pop), `u128`/`i128` (and AAPCS64 odd-register alignment), `PairU64`/`MixedIntFloat`/fat pointers, `#[repr(C, packed)]`/`align(N)`, `#[target_feature]` wide AVX/AVX-512 SIMD, `extern "efiapi"`/`"C-unwind"`, integer `signext`/`zeroext`, partial-niche invalid discriminants, struct padding bytes (`undef`/`poison`), and `f16`/`f128`/`riscv64` (`not examined` in `rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting`). `classifyFnAbi` is total (no `.unknownCompilerEpoch`/`.unsupported` error branch; e.g., it does not reject `aapcs64` + `vectorcall`), treats `maxGprArgs` per-target only, and spills `win64Msvc` `extern "Rust"` `hfa2F64` all-or-nothing at `xIdx = 3` rather than splitting `ScalarPair(f64, f64)` across `xmm3` + stack.
- **Stipulated x87 model, metadata-only linker flag, and unbridged compiler pipeline:** `x87TransferF32`/`F64` models sNaN quietening axiomatically without 80-bit extended-precision double-rounding, FPU exception flags/traps, or LLVM `SelectionDAG`/`GlobalISel` backend verification (`rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting` Boundary #4). `needsLinkerAlias` is a boolean flag only (no ELF/PE/Mach-O symbol-table or PLT/GOT verification). All classifiers/shims are `noncomputable` Lean definitions (not executable native binaries), and `VrustcFormal.F1_3` is not yet mechanically bridged to `joshlf/anneal` `Trusted.MirAst`/`Trusted.MirSemantics` or verified against `rustc`'s Rust source implementation beyond the empirical matrix.

---

### Eight Highest-Risk Over-Readings and Concrete Counterexamples

`Basis: source + derived + execution (line-by-line adversarial audit of support/RustFnAbiBitExactLowering.lean and live rustc +1.100.0 probe)`

1. **Abstract functional `PhysFrame` & two-frame `PhysShim` — NOT in-place hardware register sequentialization, stack framing, or volatile-register preservation across `call` (`known not to apply` to machine-code shims):**
   - *Citations:* `PhysFrame` (`L723–L731`), `execArgShim` (`L1396–L1402`), `execRetShim` (`L1471–L1475`), `phys_shim_bridge_restores_equivalence` (`L3058–L3143`).
   - *Counterexamples:*
     - **`execRetShim` bypasses caller-saved `sret` clobbering:** `execRetShim plan fCaller fCalleeOut` receives the caller's untouched pre-call `fCaller` as a functional argument and reads `readSretTok loc fCaller` directly (`L1466`). On real x86-64 hardware (`sysv64` `rdi`, `win64Msvc` `rcx`), the `sret` register is **caller-saved** and is freely clobbered by a direct-return callee (`D1` `1.100.0` callee does not even know an `sret` pointer existed). A real machine-code shim must spill `rdi`/`rcx` onto its own stack frame or a callee-saved register before `call` and restore it afterward; `VrustcFormal.F1_3` proves nothing about stack-frame allocation or register spilling.
     - **`execArgShim` writes into a fresh `emptyFrame` via an unbounded functional `scratch` list:** It never sequentializes parallel register moves in-place on one hardware register file (no register-cycle breaking via temp register/`xchg`), deep-copies indirect memory buffers into newly allocated tokens rather than aliasing shared virtual memory, and models zero callee-saved registers (`rbx`/`rbp`/`r12`–`r15`/`x19`–`x28`), `rsp`/`sp` 16-byte alignment, Win64 32-byte shadow space, SysV64 128-byte red zone, or `i686` 32-bit GPR / 4-byte stack-slot granularity (abstracting `eax:edx` 64-bit returns as a single 64-bit `gpr0`).

2. **Closed `9`-type × `4`-target × `3`-convention × `3`-release universe with a total (non-fail-closed) classifier (`unsupported` / `not examined` outside closed universe):**
   - *Citations:* `AbiTarget` (`L99–L103`), `RustcRelease` (`L106–L109`), `CallConv` (`L112–L115`), `AbiTy` (`L118–L136`), `classifyFnAbi` (`L665–L688`).
   - *Counterexamples:*
     - **Unmodeled empirically measured features:** Omits the 5th ABI family (`i686-pc-windows-msvc`, including `eax:edx` 8-byte `extern "C"` struct returns vs. `i686-linux` `sret` and `stdcall`/`fastcall`/`system` `@12`/`@20` migrations), `u128`/`i128` (3-way split + AAPCS64 odd-register alignment skipping `x0 -> x2`), `PairU64`/`MixedIntFloat`/`*const [u8]` fat pointers, `#[repr(C, packed)]`, `#[repr(C, align(N))]`, `#[target_feature]` 256/512-bit AVX/AVX-512 vectors, `extern "efiapi"`, `extern "C-unwind"`, partial-niche invalid discriminants (e.g., `Option<bool>` bits `2..255`), struct padding bytes (`undef`/`poison`), and `f16`/`f128`/`riscv64`.
     - **Total classifier without `.unknownCompilerEpoch`/`.unsupported` error channel:** Unlike the fail-closed `-> Except AbiUnsupported` design recommended in `rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting`, `classifyFnAbi` is total over the 3-release enum and silently classifies invalid combinations such as `classifyFnAbi .aapcs64 .r1_100_0 { conv := .vectorcall, ... }` as `.undecorated` even though `rustc` rejects `extern "vectorcall"` on `aarch64`.

3. **Concrete classifier idealizations inside the modeled universe (`known not to apply` to Win64 `hfa2F64` register-boundary splitting, `vectorcall` GPR caps, or `signext`/`zeroext`):**
   - *Citations:* `maxGprArgs` (`L377–L381`), `classifyOneArg | .hfa2F64` (`L498–L503`), `valHasTy` (`L158–L162`), `marshalOneArg`/`unmarshalOneArg` (`L855–L858`, `L903–L910`).
   - *Counterexamples (including `[real measurement]` `rustc +1.100.0` probe):*
     - **Win64 `extern "Rust"` `HfaF64x2` at `xIdx = 3`:** Live `rustc +1.100.0 --target x86_64-pc-windows-msvc` emits `define { double, double } @p_rust_hfa2(double %x.0, double %x.1)` (two independent `ScalarPair` parameters: when 1 XMM register `xmm3` remains, `%x.0` takes `xmm3` and `%x.1` spills to the stack), whereas `L500–L503` checks `Nat.blt (xIdx + 1) maxFX` and spills *both* `f64`s all-or-nothing to `.directStack`.
     - **`vectorcall` GPR caps:** `maxGprArgs` ignores `conv`, giving `sysv64` `vectorcall` 6 GPRs (instead of Win64's 4) and `i686SysV` `vectorcall` 0 GPRs (instead of `ecx`/`edx` 2-GPR fast-pass).
     - **No integer signedness or upper-bit register masking:** `intScalar (bytes : Nat)` carries no `signed : Bool` (`signext`/`zeroext`), and `valHasTy` enforces zero-extension (`bits < 2^(8*bytes)`), rejecting upper-bit register garbage via `.error .typeMismatch` instead of modeling target-specific caller extension vs. callee truncation.

4. **Stipulated x87 sNaN-quietening model (`x87TransferF32`/`x87TransferF64`) — NOT an x86/x87 ISA semantics or LLVM backend proof (`not examined` for 80-bit rounding, FPU traps, and `SelectionDAG`):**
   - *Citations:* `isF32SignalingNaN`..`x87TransferF64` (`L198–L236`), `marshalRet` (`L1048–L1051`), `fingerprint_and_universal_x87_sharpness` (`L3158–L3188`).
   - *Counterexample:* `x87TransferF32`/`F64` axiomatically models x87 `fld`+`fstp` as setting bit 22 / bit 51 on sNaNs and identity on all other bit patterns. It does **not** verify Intel SDM Vol. 1 §4.8.3.5 / §8.2, x87 80-bit extended-precision double-rounding, subnormal flushing / `#D` denormal or `#I` Invalid Operation FPU status-word flags (or unmasked `SIGFPE` traps on sNaN), x87 control-word precision settings, or whether LLVM `SelectionDAG` lowers `i686` `extern "Rust"` `<4 x i8>`/`<8 x i8>` bit-identically across `LLVM 23.1.1` vs. `LLVM 23.1.5`.

5. **Theorem 2 (`fullAbiCompatible_preserves_call_boundary`) is a 4-line structural-equality corollary of Theorem 1 forcing `t₁ = t₂`, NOT completeness over unmodeled ABI attributes (`known not to apply` across unmodeled attributes):**
   - *Citations:* `irOnlyCompatible` / `fullAbiCompatible` (`L693–L704`), `fullAbiCompatible_eq` (`L1781–L1792`), `fullAbiCompatible_preserves_call_boundary` (`L3021–L3042`).
   - *Counterexample:* Because `fullAbiCompatible a b = true ↔ a = b` over the 6 modeled fields of `ComputedFnAbi`, Theorem 2 reduces in 4 lines to `rw [← heq]; exact same_abi_marshal_roundtrip ...`, and `targetEq` makes `t₁ ≠ t₂` impossible (`fullAbiCompatible` is always `false` across distinct targets). Any unmodeled ABI attribute (`align N`, `signext`/`zeroext`, `#[target_feature]`, `callee-pop` stack cleanup, `stdcall`/`fastcall` `_` vs. `@` symbol prefix) is invisible to `ComputedFnAbi` and therefore invisible to `fullAbiCompatible`.

6. **`CompiledShimPlan.needsLinkerAlias` is a boolean metadata flag — NOT verified linker execution, object-file emission, or PLT/GOT aliasing (`not examined`):**
   - *Citations:* `LinkerSymbolRule` (`L278–L280`), `CompiledShimPlan` (`L1209–L1217`), `compileShimPlan` (`L1291–L1293`), `phys_shim_bridge_restores_equivalence` (`L3066`, `L3082–L3093`).
   - *Counterexample:* On `D4` (`sigD4VectorcallHfa4`, `1.100.0` `@@16` vs. `1.102.0` `@@24`), Theorem 3 proves `plan.needsLinkerAlias = true` and proves register/stack/memory transport equivalence *given* that control reaches the shim and callee. It does **not** verify ELF/PE/Mach-O symbol-table encoding, `\01` LLVM IR literal-name emission, `.def`/alias directives, or dynamic linker PLT/GOT resolution.

7. **Standalone `Init.*`-only formalization — NOT mechanically bridged to `joshlf/anneal` `Trusted.MirAst`/`Trusted.MirSemantics` or `rustc`'s Rust source (`not examined`):**
   - *Citations:* Imports (`L9–L13`: `Init.NotationExtra`, `Init.Data.BitVec.BasicAux`, `Init.Data.Nat.Div.Basic`, `Init.Control.Except`); `0` references to `Trusted.*` or `Anneal.*`.
   - *Counterexample:* Unlike `anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge` (which proves theorems directly over `Trusted.MirAst` and `Trusted.MirSemantics`), `VrustcFormal.F1_3` defines standalone `AbiTy`, `FnSig`, and `PhysFrame`. There is no mechanized translation from `Trusted.MirAst.MirTy` / `Trusted.MirSemantics.Query` into `VrustcFormal.F1_3.FnSig` (which cannot yet represent `MirTy.float` or `#[repr(simd)]` in `Trusted.MirAst@c131b320e`), nor a mechanized proof that `classifyFnAbi` matches `rustc_target::callconv` beyond empirical validation.

8. **`noncomputable` Lean kernel definitions, finite-arity precondition, and Win64 `#[repr(C)]` ZST provenance (`unsupported` for direct Lean codegen):**
   - *Citations:* `noncomputable def` across `L181–L1475`; `hArity : sig.args.length + 2 < Nat.pow 2 64` (`L2985`, `L3023`, `L3060`); `rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting` Boundary #2.
   - *Impact:* All `92` public value definitions are marked `noncomputable` to prevent Lean `v4.34.1` from generating `isPartial` `._unsafe_rec` auxiliaries rejected by `TrustedBoundary.lean`; consequently, `classifyFnAbi` and `compileShimPlan` cannot be compiled directly into native binaries without a separate executable extractor/correspondence proof. The `hArity` bound is mathematically necessary to prevent 64-bit indirect-token wrap-around. Retention of Win64 `#[repr(C)]` ZST `Indirect` passing in `1.102.0-nightly` was `source`-verified from `916dda0c26e7736748e2ef8233f1fd1477e1be1e` in `rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting` Boundary #2 and separately confirmed via a live `rustc +nightly` probe (not present as a 4th ZST function in the published 9-target × 3-release matrix dataset).

### Tooling Boundary: `lean4lean`

- **`lean4lean` (`unsupported` on current host):** Running the host `lean4lean` binary against compiled Lean `v4.35.0` `.olean` output failed with `rc = 1` (`incompatible header`). Independent external typechecking is established by `lean4export 3.1.0` + `nanoda_bin 0.4.19`, not `lean4lean`.

---

## Evidence

### Preserved Artifacts & Primary Sources (`2026-11-20`)

| Artifact / Upstream Subject | Pin / Path | Size / Scope | SHA-256 / Exact Coordinates |
| :--- | :--- | ---: | :--- |
| `support/RustFnAbiBitExactLowering.lean` | Package artifact (verbatim proof) | `3,388` lines / `158,677 B` | `8f79d62a6ead93d1013b4cbb0f9989bd79570091f60416adfefea599c57d0cde` |
| Frozen pre-proof statement reconstruction target | Strip `L1477–L2967` + `4` Part VI proofs -> `  sorry` | `1,794` lines / `81,568 B` | `7b13cd7b8d86fc602ce21ac95d8c639f9dd063e9e04cc500222d64fd9f838535` |
| Companion empirical ground-truth report | `reports/rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting/` (`google/zerocopy@120889696dc131f0fc7cf814e898ee72cd04a19e`) | `9` targets × `3` releases (`2,499` fns) | `78 / 833` IR drifts (`55 / 833` binary/linker breaks, `23 / 833` IR-only symbol migrations) |
| `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` | `rustc 1.99.1` (`LLVM 23.1.1`) | Release epoch `r1_99_1` | Baseline pre-`D1`/`D2`/`D3`/`D4` release |
| `rust-lang/rust@0ef1bc386059596dada8fb65b50425aab2ea637a` | `rustc 1.100.0` (`LLVM 23.1.5`) | Release epoch `r1_100_0` | Post-`D1` (x86/x86_64 SIMD direct), pre-`D2`/`D3`/`D4` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `rustc 1.102.0-nightly` (`LLVM 23.1.5`) | Release epoch `r1_102_0` | Post-`D1`/`D2`/`D3`/`D4` release |
| `rust-lang/rust@429c1c18ca616ec5a097019c6071dc8ca75585be` | `compiler/rustc_target/src/callconv/mod.rs` (merged `498b89dd40af107a23c13a009345a0dea224248c`) | Causal commit `D1` | x86/x86_64 `extern "Rust"` `<= 128`-bit SIMD direct vector passing |
| `rust-lang/rust@a654a240456566a313e53698f42c70ad7366676d` | `compiler/rustc_target/src/callconv/mod.rs:833-839` (merged `e3c3417ff6499548c5ab52767489ab262f9a2ac0`) | Causal commit `D2` | AArch64 `extern "Rust"` `<= 128`-bit NEON direct vector passing |
| `rust-lang/rust@916dda0c26e7736748e2ef8233f1fd1477e1be1e` | `compiler/rustc_abi/src/layout.rs`, `compiler/rustc_target/src/callconv/x86_win64.rs:44-68` | Causal commit `D3` | Adds `LayoutData.repr_c`; flips Win64 non-`#[repr(C)]` ZSTs to `Ignore` |
| `rust-lang/rust@d11b3f4d61c50f4149ea34a89302cf24a0c52b86` | `compiler/rustc_codegen_llvm/src/declare.rs:169-185`, `compiler/rustc_codegen_ssa/src/common.rs:179-225` (merged `62746359572280748adec7b4add65f0a1c26d1a9`) | Causal commit `D4` | Pre-lowering Rust `FnAbi` `vectorcall` / MSVC byte-count decoration |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/audit/TrustedBoundary.lean` (`L432-435, 1524, 2282-2292`), `trusted/lean/foundation-lock.json`, `trusted/lean/Trusted*.lean`, `theory/Anneal/MirWp.lean` | Unmodified TCB & lock | `TrustedBoundary.lean` `6f19cc602cf931522d61efb320eae3ca60d7759db20ba6304c912bf372f2fc6a`; `foundation-lock.json` `37f780b6257d0bc99fd5d7d3d0a1f16d168ef066a2a01466f4076f080d3425d2`; `Trusted.lean` `8316581d84c50b8e6234e493780e30b05e5a3b02328c12ef6c6c82cbae7755dd`; `MirAst.lean` `71b57539fa1d462e1e856db4d7b0c7a260f7c39255c05cf489cfe87edc1a77c8`; `MirSemantics.lean` `b8378127ea7b81b473a5f86cd164df430feb56296cbbbe57457cc2b125316c0a`; `MirWp.lean` `3c5458c796b0f477a689bbee116632b0a79d0f9b021120dfceec0ccacd67e6dc` |
| `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` | `v4.34.1` (`x86_64-unknown-linux-gnu` Release) | Primary kernel | `bin/lean` SHA-256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` (`17.103 s`, `478.79 MB`) |
| `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` | `v4.35.0` (`x86_64-unknown-linux-gnu` Release) | Cross-version kernel | `17.614 s`, `446.23 MB`, `13,502,544 B` `.olean` |
| `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` | `leanexport 3.1.0` | Export format `3.1.0` | `13` public theorems (`9,543,273 B`, `183,552` lines, `0.916 s`) |
| `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` | `nanoda_bin 0.4.19` | Rust external kernel | `Checked 1256 declarations with no typechecker errors` (`0.535 s`, `43.34 MB`) |

### Source vs. Compiled Declaration Inventory (`[real measurement]`)

| Scope | `inductive` | `structure` | `def` | `theorem` | Source Total | Kernel `ConstantInfo` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| Public (`VrustcFormal.F1_3`) | `15` | `4` | `92` | `13` | `124` | `1,316` *(incl. `549` auto-gen eq/rec/`sizeOf_spec` thms)* |
| Private (`L1477–L2967`) | `0` | `0` | `2` | `78` | `80` | `440` |
| **Module Total** | **`15`** | **`4`** | **`94`** | **`91`** | **`204`** | **`1,756`** *(plus `335` `extraConstNames`)* |
| Standalone `TrustedBoundary.lean` Pass 1 Replay | — | — | — | — | — | **`1,756`** (`2,396` reachable) |
| Full Anneal `TrustedBoundary.lean` Pass 1 Replay (`requireMirWp = true`) | — | — | — | — | — | **`3,337`** (`1,324` kernel decls, `4,184` reachable) |
| Exported `nanoda_bin 0.4.19` Closure (`13` public theorems) | `62` | — | `642` | `329` (`+1` axiom) | — | **`1,256`** checked decls |

---

## Revalidation

All checks run self-contained in a fresh temporary directory (`BUILD_DIR="$(mktemp -d)"`) using only the preserved package artifact and the pinned GitHub commits:

1. **Proof Digest & Frozen Contract Reconstruction (~0.1 s):**
   ```bash
   sha256sum support/RustFnAbiBitExactLowering.lean
   # Expected: 8f79d62a6ead93d1013b4cbb0f9989bd79570091f60416adfefea599c57d0cde (3,388 lines, 158,677 bytes)
   ```
   Verify that stripping `L1477–L2967` (strictly `private` helpers) and replacing the indented proof bodies of the `4` Part VI theorems (`L2994`, `L3036`, `L3076`, `L3173`) with `  sorry` produces exactly `81,568` bytes with SHA-256 `7b13cd7b8d86fc602ce21ac95d8c639f9dd063e9e04cc500222d64fd9f838535`.

2. **Fresh Synchronous Lean `v4.34.1` Build & Axiom Census (~18 s):**
   ```bash
   BUILD_DIR="$(mktemp -d)"
   LEAN434="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
   "$LEAN434" -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     -R support \
     -o "$BUILD_DIR/RustFnAbiBitExactLowering.olean" \
     support/RustFnAbiBitExactLowering.lean
   ```
   Confirm `rc = 0`, `0` errors/warnings, and `#print axioms` returning `[propext]` on all `13` public theorems (`same_abi_marshal_roundtrip`, `fullAbiCompatible_preserves_call_boundary`, `phys_shim_bridge_restores_equivalence`, `fingerprint_and_universal_x87_sharpness`, `ce_d1_*`..`ce_d6_*`, `canary_p1_*`..`canary_p3_*`).

3. **Unmodified Anneal `TrustedBoundary.lean` Preflight & Pass 1 Audit (~12 s):**
   Check out `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` into `$BUILD_DIR/anneal`, verify all `51 / 51` `foundation-lock.json` sysroot digests, compile `support/RustFnAbiBitExactLowering.lean` as `Anneal.F1_3_Proof` (via `--setup` with `-j1 -M2048 -t0 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`), and run `trusted/audit/TrustedBoundary.lean`:
   - `"preflight"` (`SourceRole.theory`): confirm `rc = 0`, `ok = true`, and confirm a negative probe substituting `sorry` fails closed with `rc = 1` (`policy:unsupported syntax kind Lean.Parser.Tactic.tacticSorry`).
   - `"audit"` (`trustLevel := 0`, `plugins := #[]`, `loadExts := false`, merging preflight `"headers"` into the foundation `"graph"` per `trusted/audit/src/lib.rs:2738`): confirm `rc = 0`, `ok = true`, `replay = true`, `axioms = ["propext"]`, and `replayedDeclarations = 1,756` (standalone) / `3,337` (full Anneal with `Trusted`, `Trusted.MirAst`, `Trusted.MirSemantics`, `Anneal.MirWp`).

4. **Independent Cross-Version & Rust External Kernel Verification (~19 s):**
   Repeat Step 2 with `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`), export all `13` public theorems via `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`3.1.0`), and verify with `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`nanoda_bin 0.4.19`) using `permitted_axioms = ["propext"]`, `unpermitted_axiom_hard_error = true`, `nat_extension = true`, `string_extension = true`. Confirm `Checked 1256 declarations with no typechecker errors` (`rc = 0`) and confirm `permitted_axioms = []` fails closed (`rc = 1`).

5. **Drift Triggers Requiring Re-Audit:** Re-run the `9`-target empirical matrix from `rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting` and update `RustcRelease`/`classifyFnAbi` whenever pinning a new `rustc` commit; re-prove `VrustcFormal.F1_3` whenever adding unmodeled targets (`i686-pc-windows-msvc`, `riscv64`), types (`u128`/`i128`, `f16`/`f128`, wide AVX/AVX-512 SIMD, packed/aligned aggregates), Win64 `hfa2F64` `ScalarPair` boundary splitting, in-place hardware register sequentialization + `sret` spilling, or a mechanical translation from `joshlf/anneal` `Trusted.MirAst`.
