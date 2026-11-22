# Fuchsia AArch64 `PT_INTERP`-Free `ET_DYN` Relocations, EL1 `softfloat` / `+reserve-x20` Codegen, `DT_GNU_HASH` vDSO Resolution, and ZST Closure Synthesis

## Summary

Building and formally verifying standalone `#![no_std]` Rust binaries on Fuchsia AArch64—both `PT_INTERP`-free (`ld.so.1`-less) userspace `ET_DYN` components entered directly from `zx_process_start(x0 = bootstrap_handle, x1 = vdso_base)` and pure/cryptographic leaf crates linked into Zircon EL1—exposes five concrete ABI, relocation, and MIR-validity boundaries across `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`) and upstream Fuchsia (`273f473fa9ac7d81e2e476d67e800c98df0fa117`):

1. **`aarch64-unknown-fuchsia` injects `x18` ShadowCallStack prologues that fault in bare `_start` processes, whereas `aarch64-unknown-none -C relocation-model=pic -Z fixed-x18` preserves `x18` without an SCS VMO.** Compiling non-leaf functions for `aarch64-unknown-fuchsia` emits `str x30, [x18], #8` / `ldr x30, [x18, #-8]!`, which faults immediately (`x18 = 0`) when bypassing `ld.so.1`. Compiling for `aarch64-unknown-none` with `-C relocation-model=pic -Z fixed-x18` suppresses SCS instrumentation while forbidding LLVM register allocation of `x18`/`w18`, keeping compiled objects ABI-compatible with both bare processes and standard Fuchsia ShadowCallStack callers.
2. **Four PIC constructs silently emit dynamic relocations, `memset` libcalls, or `.rodata` `br` jump tables in `PT_INTERP`-free `ET_DYN` binaries.** Under `-C relocation-model=pic`: (a) taking the address of an `extern "C"` symbol emits `R_AARCH64_ADR_GOT_PAGE` + `R_AARCH64_LD64_GOT_LO12_NC`, producing an un-relocated `.got` `R_AARCH64_RELATIVE` entry under `ld.lld -pie`, whereas wrapping the call in a module-private `extern "C"` trampoline emits static PC-relative `adrp + add` (`0` dynamic relocations); (b) storing `const [*const u8; N]` byte-slice pointer tables promotes the constant to `.data.rel.ro` with `N` `R_AARCH64_RELATIVE` relocations; (c) aggregate zeroing `*dst = Big { words: [0; 32] }` tail-calls `b memset` unless lowered through `volatile_store` or verified `compiler_builtins`; and (d) dense integer `match` arms emit PC-relative `.LJTI` byte-offset tables using `br x10`.
3. **Zircon EL1 kernel Rust requires `aarch64-unknown-none-softfloat` (`rustc` `#162235` rejects `-C target-feature=-neon` on `aarch64-unknown-none`) plus `+reserve-x20`, `+tpidr-el1`, and `+outline-atomics`.** In `zircon/kernel/arch/arm64/BUILD.gn:45-91`, Zircon disables all FP/SIMD registers (`x20` holds `percpu_ptr` and `v0..v31` retain unsaved user-mode state). On `rustc 1.102.0-nightly`, passing `-C target-feature=-neon,-fp-armv8` to hard-float `aarch64-unknown-none` is a hard error (`target feature 'neon' must be enabled`); EL1 crates must target `aarch64-unknown-none-softfloat` and pass `+reserve-x20,+tpidr-el1,+strict-align` via `-Z llvm-target-feature` (avoiding `#162235` `-C target-feature` phase-out warnings).
4. **Runtime ELF64 `DT_GNU_HASH` vDSO symbol resolution depends on four structural invariants.** Resolving `zx_*` entrypoints directly from `x1 = vdso_base` requires computing `load_bias = vdso_base - trunc_page(first_PT_LOAD.p_vaddr)` (zero-offset indexing holds only when `first_PT_LOAD.p_vaddr == 0`, as in Zircon's `build/config/zircon/rodso.ld:34`), rejecting `STB_LOCAL` (`(st_info >> 4) == 0`) in addition to `SHN_UNDEF`, bounds-checking all `24` bytes of `Elf64_Sym`, and deriving readable image bounds from ELF program headers rather than hardcoded `1 MiB` constants.
5. **Type-erased C-ABI callback dispatch via `MaybeUninit::<F>::zeroed().assume_init()` is valid under Miri iff `size_of::<F>() == 0`, `F: Copy + 'static`, an inhabited value witness `_handler: F` was evaluated at registration, and the container stays `!Send` unless `F: Send`.** Passing an uninhabited ZST (`struct UninhabitedZst(Void)`) without a value witness is immediate UB in Miri; conversely, with a call-by-value witness and `F: Copy + 'static`, the only remaining soundness obligation is preventing cross-thread transfer of `!Send` ZST capability tokens when `F: Send` is not bound.

## Applicability

This report applies to `#![no_std]` / `#![no_main]` Rust binaries, static libraries, and post-link binary auditors targeting AArch64 Fuchsia userspace (`ET_DYN` position-independent executables with and without `PT_INTERP = ld.so.1`) and Zircon EL1 kernel environments, examined across:

- **`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, `2026-11-11`, LLVM `23.1.5` + Miri + `lld`):** Inspected via `--emit=obj,asm`, `readelf -h -l -d -r`, and `cargo miri run`.
- **Fuchsia / Zircon (`https://fuchsia.googlesource.com/fuchsia` @ `273f473fa9ac7d81e2e476d67e800c98df0fa117`):** Inspected for `zircon/kernel/arch/arm64/BUILD.gn`, `build/config/zircon/rodso.ld`, and `zircon/kernel/lib/userabi/vdso.rs`.
- **Anneal (`google/zerocopy` @ `ffd1023db9c6014fa117b84710d5c3e336eb684f`):** Contextualizes MIR capture (`anneal/trusted/rustc-capture/`), `Trusted.MirAst` (`MirTy`, `TerminatorKind`, `Rvalue`), and post-link binary verification gates.

General relocation-invariant proofs, AArch64 PAC/MTE/SVE ABI seams, and general `rustc` ELF64 post-link relocations are covered in sibling packages `relocation-invariant-binary-verification-pc-relative-elf-proofs-and-address-shift-resilience`, `aarch64-pac-mte-tbi-provenance-sve-clobbers-and-outlined-atomics-ffi-seams`, `post-link-executable-validator-relocations-veneers-erratum-843419-and-gcs`, and `rustc-elf64-postlink-relocation-tls-relaxation-and-ehframe-ground-truth`.

## Findings

### 1. Fuchsia AArch64 Userspace vs. Zircon EL1 Target & Register Discipline

Basis: source + execution

Direct compilation of identical `#![no_core]` Rust functions across `aarch64-unknown-fuchsia`, `aarch64-unknown-none`, and `aarch64-unknown-none-softfloat` on `rustc 1.102.0-nightly (3ef0c22cd)` demonstrates three distinct register and ABI regimes:

| Regime | Target & Required Flags | `x18` (ShadowCallStack) | `x20` (`percpu_ptr`) | FP / NEON (`v0..v31`) | Failure Mode If Misconfigured |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Standard Fuchsia (`ld.so.1`) | `--target aarch64-unknown-fuchsia` | `str x30, [x18], #8` / `ldr x30, [x18, #-8]!` emitted in every non-leaf fn | Allocatable callee-saved GPR | Enabled | Crashes immediately (`x18 = 0` page fault) if linked without `ld.so.1` SCS allocation |
| Bare Userspace (`PT_INTERP`-free `ET_DYN`) | `--target aarch64-unknown-none -C relocation-model=pic -Z fixed-x18` | `0` SCS prologues; `x18`/`w18` never allocated | Allocatable callee-saved GPR | Enabled (unless `-softfloat`) | Omitting `-Z fixed-x18` lets LLVM clobber `x18` if linked into an SCS-enabled host |
| Zircon EL1 Kernel Leaf | `--target aarch64-unknown-none-softfloat -C relocation-model=pic -Z fixed-x18 -Z llvm-target-feature=+strict-align,+reserve-x20,+tpidr-el1,+outline-atomics -C unsafe-allow-abi-mismatch=fixed-x18,llvm-target-feature` | `x18` reserved | `x20` reserved (`BUILD.gn:80-83`) | Strictly disabled (`BUILD.gn:50-76`) | Passing `-neon` on `aarch64-unknown-none` fails with hard ABI error; touching `v0..v31` corrupts unsaved EL0 user SIMD state; touching `x20` corrupts EL1 `percpu_ptr` |

In `zircon/kernel/arch/arm64/BUILD.gn:52-76`, Zircon explicitly sets `"abi": "softfloat"` and `"rustc-abi": "softfloat"` on its custom kernel target alongside `-fp-armv8, -neon, -sve, -sve2, -aes, -sha2`. On stock `rustc 1.102.0-nightly`, `--target aarch64-unknown-none -C target-feature=-fp-armv8,-neon` aborts compilation (`error: target feature 'neon' must be enabled to ensure that the ABI of the current target can be implemented correctly`), whereas `--target aarch64-unknown-none-softfloat` already enforces the integer-only ABI and compiles cleanly (`exit 0`). Passing `strict-align` or `reserve-x20` via `-C target-feature` triggers `rust-lang/rust#162235` phase-out warnings (`will become a hard error in a future release`), which `-Z llvm-target-feature` avoids.

### 2. Four PIC Relocation & Codegen Traps in `PT_INTERP`-Free `ET_DYN` Executables

Basis: execution + derived

When Zircon starts a bare process via `zx_process_start(proc, thread, entry, sp, arg1 = bootstrap_chan, arg2 = vdso_base)` without `PT_INTERP` (`ld.so.1`), the ELF loader maps `PT_LOAD` segments at an ASLR `load_bias` and jumps directly to `load_bias + e_entry` **without processing `.rela.dyn` dynamic relocations**. Linking with:

```text
ld.lld -m aarch64elf -pie -z now -z relro -z separate-loadable-segments \
  -z max-page-size=4096 --hash-style=gnu -e _start --no-undefined
```

produces a valid `ET_DYN` binary with `"There are no relocations in this file"` (`readelf -r`) **if and only if** four Rust/LLVM PIC codegen patterns are controlled:

1. **External vs. internal function-pointer materialization:**
   - Taking a function pointer to an external symbol (`pub extern "C" fn take_ext() -> unsafe extern "C" fn(u32) -> u32 { ext_handler }`) compiles to:
     ```asm
     adrp x0, :got:ext_handler          // R_AARCH64_ADR_GOT_PAGE
     ldr  x0, [x0, :got_lo12:ext_handler] // R_AARCH64_LD64_GOT_LO12_NC
     ```
     Under `ld.lld -pie`, this allocates an 8-byte `.got` slot backed by a dynamic `R_AARCH64_RELATIVE` relocation. Without `ld.so.1`, `.got` holds the un-relocated link-time offset (`0x1...`) rather than `load_bias + offset`, faulting on `blr`!
   - Wrapping the callee in a **module-private** trampoline (`unsafe extern "C" fn priv_handler(x: u32) -> u32 { ext_handler(x) }`) changes the symbol binding to local, compiling `take_priv` to:
     ```asm
     adrp x0, priv_handler              // R_AARCH64_ADR_PREL_PG_HI21
     add  x0, x0, :lo12:priv_handler    // R_AARCH64_ADD_ABS_LO12_NC
     ```
     and `priv_handler`'s body to `b ext_handler` (`R_AARCH64_JUMP26`), all resolved completely at static link time with **zero `.got` and zero dynamic relocations**.
2. **`const` pointer arrays in `.data.rel.ro`:** Defining `const NAMES: [*const u8; 12] = [b"zx_a\0".as_ptr(), ...]` and passing `NAMES.as_ptr()` forces LLVM PIC lowering to place `NAMES` in writable `.section .data.rel.ro,"aw"` with `12` `R_AARCH64_RELATIVE` relocations. Storing `(offset: u16, len: u8)` indices into a single concatenated `const BLOB: &[u8]` (addressed via PC-relative `adrp + add`) eliminates all `.data.rel.ro` relocations.
3. **Implicit `memset` / `memcpy` libcall synthesis:** Even under `#![no_core]`, `*dst = BigBuf { words: [0; 32] }` (`256` bytes) lowers at `-C opt-level=2` to `mov w1, wzr; mov w2, #256; b memset`. A `PT_INTERP`-free binary must either link verified `memset`/`memcpy`/`memcmp`/`memmove` symbols or use explicit `volatile_store` / small word loops.
4. **PC-relative `.LJTI` jump tables (`br xN`) in binary CFG auditors:** On `call_ext_and_spill` (11-arm `match` over `u32`), LLVM `23.1.5` `-C relocation-model=pic -C opt-level=2` emits a relocation-free compressed jump table:
   ```asm
   cmp  w0, #10
   b.hi .LBB1_13
   mov  w8, w0
   adrp x9, .LJTI1_0
   add  x9, x9, :lo12:.LJTI1_0
   adr  x10, .LBB1_2
   ldrb w11, [x9, x8]
   add  x10, x10, x11, lsl #2
   br   x10
   ```
   Post-link binary CFG / stack-depth / WCET auditors cannot reject all `br xN` instructions unconditionally unless `-C llvm-args=-aarch64-min-jump-table-entries=999999` (or verified `.LJTI` bounds recovery) is applied.

### 3. ELF64 `DT_GNU_HASH` vDSO Symbol Resolution Invariants

Basis: source + derived

Resolving Zircon syscalls directly from the memory-mapped `libzircon.so` vDSO image at `x1 = vdso_base` via `PT_DYNAMIC` (`DT_GNU_HASH = 0x6ffffef5`, `DT_SYMTAB`, `DT_STRTAB`, `DT_STRSZ`, `DT_SYMENT = 24`) requires four invariants beyond basic DJB2 (`h = h * 33 + c`, seed `5381`) chain traversal:

1. **Load-bias normalization (`load_bias` vs. `vdso_base`):** In Zircon's `build/config/zircon/rodso.ld:34, 61-63`, the first `PT_LOAD` segment starts at `p_vaddr = 0` and `.dynamic` is read-only (unrelocated), so `load_bias == vdso_base`. For arbitrary `ET_DYN` images where the lowest `PT_LOAD` has `p_vaddr = v_0 \neq 0`, `PT_DYNAMIC.p_vaddr`, `DT_*` table addresses, and returned `st_value` offsets must be resolved relative to `load_bias = vdso_base.wrapping_sub(v_0 & !0xfff)`, not raw `vdso_base`.
2. **Symbol binding check (`STB_LOCAL` exclusion):** `Elf64_Sym.st_info` (`soff + 4`) encodes binding in `st_info >> 4`. Checking only `st_shndx != SHN_UNDEF` (`soff + 6`) without `(st_info >> 4) != 0` (`STB_LOCAL`) erroneously resolves local symbols if present in `.dynsym`.
3. **Full 24-byte `Elf64_Sym` bounds check:** Even if `st_size` (`soff + 16..24`) is unused by the caller, validating `DT_SYMENT == 24` requires checking `fits(mapped_len, soff, 0, 24)` rather than `16` so truncated symbol tables cannot read past the mapped VMO end.
4. **Header-derived readable span (`mapped_len`):** Passing an arbitrary `max_len = 0x10_0000` (1 MiB) violates pointer-readability preconditions whenever the vDSO VMO is smaller (typically `32–64 KiB`) and followed by unmapped VMAR pages; `mapped_len` should be bounded from the initial 4 KiB ELF header page (`e_phoff + e_phnum * 56 <= 4096`) and the maximum `p_vaddr + p_memsz` across `PT_LOAD` headers.

### 4. ZST Closure Synthesis (`MaybeUninit::<F>::zeroed().assume_init()`) Across C-ABI Trampolines

Basis: execution + derived

To register stateless Rust request closures `F: Fn(Req, Control) -> Result<(), Status> + Copy + 'static` into a `#![no_std]`, heap-free C-ABI callback slot `unsafe extern "C" fn(port: u32, slot: usize, chan: u32, signals: u32, ctx: *mut u8) -> u32` without heap-allocating `F` or introducing dynamic relocations, a monomorphized private trampoline `trampoline::<P, F>` can synthesize `F` on the stack:

```rust
pub fn register<F>(&mut self, _witness: F)
where
    F: Fn(u32) -> u32 + Copy + 'static,
{
    const { assert!(core::mem::size_of::<F>() == 0); }
    self.cb = Some(trampoline::<F>);
}

unsafe extern "C" fn trampoline<F>(x: u32) -> u32
where
    F: Fn(u32) -> u32 + Copy + 'static,
{
    let f: F = unsafe { core::mem::MaybeUninit::<F>::zeroed().assume_init() };
    f(x)
}
```

Testing under Miri (`rustc 1.102.0-nightly`) and analyzing Rust's validity and library-safety rules establishes the exact four-part soundness condition:

1. **Zero-byte layout (`size_of::<F>() == 0`):** Enforced at monomorphization via `const { assert!(size_of::<F>() == 0); }`. Note that references (`&'static ()`) and `NonNull<()>` have `size_of == 8` on 64-bit targets (`[real measurement]`), so niche-carrying non-null pointers are automatically rejected at compile time.
2. **Runtime inhabitedness witness (`_witness: F` by value):** In Rust, `MaybeUninit::<T>::zeroed().assume_init()` on a 0-byte type is UB if `T` is uninhabited (`enum Void {}`, `struct UninhabitedZst(Void)` — Miri exits `1` with `Undefined Behavior: constructing invalid value: encountered uninhabited type`). Because `trampoline::<F>` is module-private and stored *only* inside `register(_witness: F)`, call-by-value evaluation of `_witness` proves `F` is inhabited before `trampoline::<F>` can ever be invoked, and witnesses prior valid construction of any private ZST capability token captured by `F`.
3. **`F: Copy + 'static`:** Forbids linear/move-only ZST tokens, `Drop` side effects, and lifetime-branded ghost tokens (`GhostToken<'brand>`).
4. **Container `!Send` (or `F: Send`):** If `register` omits `F: Send`, `F` may capture a `Copy + 'static + !Send` thread-local ZST token (e.g., `PhantomData<*const ()>` guarding thread-local state). Synthesizing `F` inside `trampoline::<F>` is sound **only** if the callback registry itself is `!Send + !Sync` so `trampoline::<F>` can only be invoked on the registering thread; otherwise `register` must require `F: Send + Sync`.

## Boundaries

- **Initial 4 KiB stack budget before guarded VMO stack switch (`known not to apply` to deep frames):** Bare `_start` / `ld.so.1` entry supplies a small initial stack (typically `4 KiB`); components allocating large stack buffers (e.g., `64 KiB` maximum Zircon channel messages) must either switch `sp` onto a `zx_vmo_create` + `zx_vmar_map` stack with unmapped guard pages via a verified naked assembly trampoline (`and sp, x0, #-16; ...; br x3`) or cap static call-graph `.stack_sizes` strictly below the initial stack size.
- **Uninhabited dead-code instantiation (`unsupported`):** Taking `trampoline::<F> as unsafe extern "C" fn(u32) -> u32` in a generic `const` without a live runtime `_witness: F` value is unsound because `const { assert!(size_of::<F>() == 0) }` passes on uninhabited ZSTs (`size_of::<Void>() == 0`).
- **AArch64 PAC/BTI (`bti c`, `paciasp`) on bare binaries (`not examined`):** All measurements used default AArch64 codegen without `-Z branch-protection=bti,pac-ret`.

## Evidence

- **Compiler & linker measurements (`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `rustc 1.102.0-nightly (2026-11-11)`, LLVM `23.1.5`, observed `2026-11-22`):**
  - `--target aarch64-unknown-fuchsia -C opt-level=2`: emitted `str x30, [x18], #8` prologue on `call_ext_and_spill`, `R_AARCH64_ADR_GOT_PAGE` + `R_AARCH64_LD64_GOT_LO12_NC` on `take_ext_fn_ptr`, `R_AARCH64_ADR_PREL_PG_HI21` + `R_AARCH64_ADD_ABS_LO12_NC` on `take_priv_fn_ptr`, `.LJTI1_0` `br x10` jump table on 11-arm `match`, and `b memset` on 256-byte `BigBuf` zeroing vs. `str xzr, [x0]` on `volatile_store`.
  - `--target aarch64-unknown-none -C target-feature=-fp-armv8,-neon`: failed (`exit 1`) with `error: target feature 'neon' must be enabled to ensure that the ABI of the current target can be implemented correctly`.
  - `--target aarch64-unknown-none-softfloat -C relocation-model=pic -Z fixed-x18` + `ld.lld -m aarch64elf -pie -z now -z relro -z separate-loadable-segments -z max-page-size=4096 --hash-style=gnu -e _start --no-undefined`: produced `ET_DYN` ELF64 (`e_entry = 0x1000`, 3 page-aligned `LOAD` segments `R`, `R E`, `RW`) with `0` relocations (`There are no relocations in this file`).
  - `cargo +nightly miri run`: passed (`exit 0`) on `call_synthesized(|x| x + 1, 41)` and `CapToken(())`-capturing ZST closures; failed (`exit 1`) on uninhabited `UninhabitedZst(Void)`.
- **Fuchsia Zircon primary sources (`https://fuchsia.googlesource.com/fuchsia` @ `273f473fa9ac7d81e2e476d67e800c98df0fa117`, observed `2026-11-22`):**
  - `zircon/kernel/arch/arm64/BUILD.gn:45-91` (`outline-atomics`, `integer-register-abi` `softfloat`, `percpu-abi` `+reserve-x20`, `thread-pointer-abi` `+tpidr-el1`).
  - `build/config/zircon/rodso.ld:34, 61-63` (`p_vaddr = 0` first `PT_LOAD` and read-only unrelocated `.dynamic`).
- **Anneal MIR baseline (`google/zerocopy` @ `ffd1023db9c6014fa117b84710d5c3e336eb684f`):**
  - `anneal/trusted/lean/Trusted/MirAst/Types.lean`, `Terminators.lean`, `Rvalues.lean` (admitted vs. `.unsupported` `Union`, indirect `Call`, `InlineAsm`, and pointer/function-pointer coercions).

## Revalidation

1. **Re-test AArch64 PIC relocation & EL1 `softfloat` behavior on a newer `rustc`:**
   Compile a minimal `#![no_core]` file exporting `take_ext_fn_ptr` and `take_priv_fn_ptr` with `rustc --target aarch64-unknown-none -C relocation-model=pic -Z fixed-x18 --emit=obj` and `rustc --target aarch64-unknown-none-softfloat -C relocation-model=pic -Z fixed-x18 -Z llvm-target-feature=+strict-align,+reserve-x20 -C unsafe-allow-abi-mismatch=fixed-x18,llvm-target-feature --emit=obj`, then run `readelf -r -W` and link with `ld.lld -m aarch64elf -pie --no-undefined` to confirm `0` dynamic relocations.
2. **Re-test ZST closure synthesis under Miri:**
   Run `cargo +nightly miri run` on `MaybeUninit::<F>::zeroed().assume_init()` with both an inhabited ZST closure witness (`exit 0`) and an uninhabited `enum Void {}` wrapper (`exit 1`).
