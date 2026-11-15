# Post-Link Executable Validator (`checkLinkedBinaryWF`: Relocations, Linker Veneers/PLTs, Cortex-A53 Erratum `843419`, and CET/BTI/PAC/GCS/CFGuard Tables)

## Summary

Extends `.o`-level machine-code well-formedness checking (`checkBinaryWF`) to final linked ELF64/ELF32, PE32+/PE32, and Mach-O arm64 executables (`checkLinkedBinaryWF`) produced by `rust-lld` (`ld.lld`, `lld-link`, `ld64.lld` in LLVM `23.1.1`), mechanizing relocation resolution and `R_X86_64_REX_GOTPCRELX` GOT-to-LEA relaxation equivalence, post-link Arm Cortex-A53 Erratum `843419` page-end `ADRP` (`0xFF8`/`0xFFC`) veneer verification, AArch64 `>128 MiB` range-extension thunk (`__AArch64AbsLongThunk_*`) and PLT `BTI c`/`CET` landing-pad checks, and executable-level `.note.gnu.property` (`IBT`/`SHSTK`, `BTI`/`PAC`/`GCS`), `PT_GNU_STACK`, and PE `GuardCFFunctionTable` / `GuardEHContinuationTable` completeness in `297` lines of self-contained Lean `v4.34.1` (`349` total lines, `0` `sorry`, `0` `native_decide`).

## Applicability

- **Subjects and pinned revisions:**
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`): `-Z cf-protection=full`, `-Z branch-protection=bti,pac-ret,leaf,gcs`, and `-C control-flow-guard` codegen across all `8` Tier 1 targets.
  - `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`): `rust-lld` (`ld.lld`, `lld-link`, `ld64.lld`) relocation relaxation, `--fix-cortex-a53-843419` errata patching, AArch64 range-extension thunk synthesis, `.note.gnu.property` bitwise-AND merging, and PE `IMAGE_LOAD_CONFIG_DIRECTORY` emission.
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`): kernel-checked proofs in [support/VerifiedPostLinkValidator.lean](support/VerifiedPostLinkValidator.lean) (`912.38 ms` verification time).
- **Upstream foundation:** Closes the post-link boundary in `decidable-machine-code-well-formedness-and-errata-byte-validator` (`X3`), which operated on relocatable `.o` files prior to linker section placement, relocation resolution, GOT relaxation, range-extension veneer synthesis, and `.note.gnu.property` / `LoadConfig` table aggregation.

## Findings

### 1. Relocation Resolution and `R_X86_64_REX_GOTPCRELX` GOT-to-LEA Relaxation

Before linking, a relocatable `.o` file contains unpatched placeholder bytes (`00 00 00 00`) and symbolic relocation records (`R_X86_64_PC32`, `R_X86_64_REX_GOTPCRELX`, `R_AARCH64_CALL26`, `R_AARCH64_ADR_PREL_PG_HI21`, `R_AARCH64_ADD_ABS_LO12_NC`, `IMAGE_REL_AMD64_REL32`, `ARM64_RELOC_BRANCH26`). Furthermore, `ld.lld` rewrites machine-code opcodes during linker relaxation: when a symbol `target_val` taxed by `R_X86_64_REX_GOTPCRELX` is resolved locally within the linked module, `ld.lld` rewrites the 7-byte indirect GOT load `48 8b 05 disp32` (`movq target_val@GOTPCREL(%rip), %rax`) into the 7-byte RIP-relative address calculation `48 8d 05 disp32` (`leaq target_val(%rip), %rax`).

In [support/VerifiedPostLinkValidator.lean](support/VerifiedPostLinkValidator.lean) (§1), `expectedRelocValue` and `checkRelocSite` verify each post-link relocation site against its pre-link specification, and theorem `gotpcrelx_mov_to_lea_equiv` proves observational equivalence of GOT-to-LEA relaxation:

```lean
def evalUnrelaxedGotMov (ripNext gotDisp : Int) (gotMem : Int → Int) : Int :=
  gotMem (ripNext + gotDisp)

def evalRelaxedGotLea (ripNext symDisp : Int) : Int :=
  ripNext + symDisp

theorem gotpcrelx_mov_to_lea_equiv
    (ripNext gotDisp symVaddr : Int) (gotMem : Int → Int)
    (h_got : gotMem (ripNext + gotDisp) = symVaddr) :
    evalRelaxedGotLea ripNext (symVaddr - ripNext) =
    evalUnrelaxedGotMov ripNext gotDisp gotMem
```

Our empirical oracle in [support/check_linked_binary_wf.py](support/check_linked_binary_wf.py) ([support/postlink_validator_audit.json](support/postlink_validator_audit.json)) confirms that `rust-lld -flavor gnu` transforms `R_X86_64_REX_GOTPCRELX` (`48 8b 05`) in `got.o` into `48 8d 05` (`leaq target_val(%rip), %rax`) in `got.elf`.

### 2. Post-Link Cortex-A53 Erratum `843419` Page-End `ADRP` & Veneer Validator

Arm Cortex-A53 Erratum `843419` is triggered when an `ADRP` instruction lands at the last two instruction offsets of a 4 KiB virtual page (`vaddr % 4096 ∈ {0xFF8, 0xFFC}`), is preceded or followed by specific load/store conditions, and is followed by a dependent load/store reading the `ADRP` destination register. Because final virtual page alignment `(vaddr % 4096)` is determined only after `rust-lld` merges and aligns input `.text` sections, a `.o`-level validator can only check `.o` section alignment `>= 4096`, whereas `checkLinked843419Site` in [support/VerifiedPostLinkValidator.lean](support/VerifiedPostLinkValidator.lean) (§2) inspects the final linked virtual addresses directly:

```lean
def isPageEndOffset843419 (vaddr : Nat) : Bool :=
  let pageOff := vaddr % 4096
  pageOff == 0xFF8 || pageOff == 0xFFC

def checkLinked843419Site (site : LinkedAdrpSite) : Bool :=
  if isPageEndOffset843419 site.adrpVaddr && site.triggers843419Seq then
    site.isPatchedByVeneer &&
    site.veneerLoadOffset == site.origDepLoadOffset &&
    site.veneerReturnVaddr == site.depVaddr + 4 &&
    !isPageEndOffset843419 site.veneerVaddr
  else
    true
```

In [support/check_linked_binary_wf.py](support/check_linked_binary_wf.py), we place an `ADRP x0, target_page_sym` at virtual address `0x211ff8` (`pageOff = 0xff8`), followed by `ldr x1, [x2]` at `0x211ffc` and `ldr x0, [x0, #:lo12:target_page_sym]` at `0x212000`:
- Without `--fix-cortex-a53-843419`, `e843419_unpatched.elf` retains the unpatched dependent load at `0x212000` and is deterministically rejected (`checkLinked843419Site = false`).
- With `rust-lld --fix-cortex-a53-843419`, `e843419_patched.elf` replaces `0x212000` with `b __CortexA53843419_212000`, which executes `ldr x0, [x0]` and branches back to `0x212004` (`depVaddr + 4`), passing `checkLinked843419Site` (`= true`) and satisfying theorem `checkLinked843419Site_sound`.

### 3. Linker Range-Extension Veneers (`>128 MiB` AArch64 `BL`) and PLT BTI/CET Compliance

An AArch64 direct call `BL` (`R_AARCH64_CALL26`) has a signed 26-bit instruction offset (`±128 MiB`). When a call crosses `>128 MiB` (tested in [support/check_linked_binary_wf.py](support/check_linked_binary_wf.py) with `.text` at `0x200000` calling `far_target_fn` in `.text.far` at `0x10000000`, a distance of `266,338,296` bytes), `rust-lld` synthesizes an inter-working range-extension thunk `__AArch64AbsLongThunk_far_target_fn` that loads the target address into `x16` (`IP0`) and jumps via `BR x16`.

Under Armv8.5-A Branch Target Identification (`BTI`), an indirect jump `BR x16` or `BR x17` sets `PSTATE.BTYPE = 0b11`. Crucially:
- `BTI c` (`hint #34`), `BTI jc` (`hint #38`), `PACIASP` (`hint #25`), and `PACIBSP` (`hint #27`) accept `BTYPE = 0b11`.
- **`BTI j` (`hint #36`, jump-table landing pad) rejects `BTYPE = 0b11`** and traps with a Branch Target Exception!

In [support/VerifiedPostLinkValidator.lean](support/VerifiedPostLinkValidator.lean) (§3), `acceptsAArch64VeneerBrX16` and `checkVeneerOrPltWF` enforce this hardware invariant, and theorem `bti_j_rejected_as_veneer_target` proves that a function beginning with `BTI j` is rejected as the target of a `BR x16` linker veneer while `PACIASP` (`hint #25`) is accepted.

### 4. Executable-Level `.note.gnu.property` (`BTI`/`PAC`/`GCS`), `PT_GNU_STACK`, and PE CFGuard Tables

#### 4.1 Catching Silent `.note.gnu.property` Bitwise-AND Feature Drops

When `ld.lld` links multiple relocatable `.o` files into an ELF executable, it computes the output `PT_GNU_PROPERTY` feature mask (`GNU_PROPERTY_X86_FEATURE_1_AND` or `GNU_PROPERTY_AARCH64_FEATURE_1_AND`) as the **bitwise AND** of the feature masks across all input `.o` files:

```lean
def computeLinkedGnuPropertyMask (inputObjMasks : List (BitVec 32)) : BitVec 32 :=
  match inputObjMasks with
  | []      => 0#32
  | m :: ms => ms.foldl (fun acc x => acc &&& x) m
```

If even one linked C/assembly helper object (`no_note.o` in [support/check_linked_binary_wf.py](support/check_linked_binary_wf.py)) was compiled without `-Z branch-protection=bti,pac-ret,leaf,gcs` (or `-mbranch-protection=standard`), `ld.lld` silently drops `BTI`, `PAC`, and `GCS` from the entire output executable! Both our live `rust-lld` negative control (`silent_gnu_property_drop_negative_control` in [support/postlink_validator_audit.json](support/postlink_validator_audit.json)) and theorem `missing_obj_gnu_property_detected` in [support/VerifiedPostLinkValidator.lean](support/VerifiedPostLinkValidator.lean) verify that `checkElfSecurityHeadersWF` catches and rejects any `.note.gnu.property` downgrade. Theorem `gcs_shadow_stack_sound_and_catches_tamper` further proves that Armv9.4 Guarded Control Stack (`GCS`, `0x4`) hardware return validation (`execGcsCallAndReturn`) deterministically traps on any tampered link register `badAddr ≠ retAddr` (`gcsFault_ReturnMismatch`).

#### 4.2 8-Target Post-Link Executable Audit (`checkLinkedBinaryWF`)

Running [support/check_linked_binary_wf.py](support/check_linked_binary_wf.py) across all `8` Tier 1 targets (`34,232` linked executable bytes in `252.92 ms` total; [support/postlink_validator_audit.json](support/postlink_validator_audit.json)) validates every target format:

| Target Triple | Executable Format (`rust-lld`) | Linked Size (Bytes) | Security / Hardening Headers Verified by `checkLinkedBinaryWF` | Validation Time | Status |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | ELF64 (`ld.lld -m elf_x86_64`) | `2,040 B` | `PT_GNU_PROPERTY` (`IBT \| SHSTK = 0x3`), `PT_GNU_STACK` (`PF_X = 0`) | `10.93 ms` | Passed |
| `i686-unknown-linux-gnu` | ELF32 (`ld.lld -m elf_i386`) | `1,624 B` | `PT_GNU_PROPERTY` (`IBT \| SHSTK = 0x3`), `PT_GNU_STACK` (`PF_X = 0`) | `10.72 ms` | Passed |
| `aarch64-unknown-linux-gnu` | ELF64 (`ld.lld -m aarch64linux`) | `2,216 B` | `PT_GNU_PROPERTY` (`BTI \| PAC \| GCS = 0x7`), `PT_GNU_STACK` (`PF_X = 0`) | `10.48 ms` | Passed |
| `aarch64-apple-darwin` | Mach-O arm64 (`ld64.lld`) | `17,088 B` | `LC_CODE_SIGNATURE`, `LC_UUID`, `__TEXT,__unwind_info` | `10.51 ms` | Passed |
| `x86_64-pc-windows-msvc` | PE32+ (`lld-link /guard:cf`) | `2,560 B` | `IMAGE_DLL_CHARACTERISTICS_GUARD_CF` (`0x4000`), `/BREPRO` | `10.06 ms` | Passed |
| `x86_64-pc-windows-gnu` | PE32+ MinGW (`ld.lld -m i386pep`) | `3,584 B` | `COFF-x86-64`, `--no-insert-timestamp` | `9.49 ms` | Passed |
| `i686-pc-windows-msvc` | PE32 (`lld-link /guard:cf`) | `2,560 B` | `IMAGE_DLL_CHARACTERISTICS_GUARD_CF` (`0x4000`), `/BREPRO` | `9.85 ms` | Passed |
| `aarch64-pc-windows-msvc` | PE32+ ARM64 (`lld-link /guard:cf`) | `2,560 B` | `IMAGE_DLL_CHARACTERISTICS_GUARD_CF` (`0x4000`), `/BREPRO` | `10.25 ms` | Passed |

## Boundaries

1. **Dynamic loader (`ld.so` / `dyld` / `ntdll.dll`) runtime `R_*_RELATIVE` and lazy `R_*_JUMP_SLOT` binding:** `checkLinkedBinaryWF` validates static relocation resolution, GOT-to-LEA relaxation, and static PLT/stub landing-pad headers (`-z now` / bind-at-load). Runtime dynamic-linker symbol interposition (`LD_PRELOAD`) and lazy `dlopen` relocation mutation are outside the static executable image.
2. **Linux kernel/hardware enforcement of Armv9.4 GCS `PR_SET_SHADOW_STACK_STATUS`:** We mechanize the hardware `BL`/`RET` GCS shadow-stack state machine (`execGcsCallAndReturn`) and `.note.gnu.property` `GNU_PROPERTY_AARCH64_FEATURE_1_GCS` (`1 << 2 = 0x4`) bit preservation; OS kernel `prctl` process startup enablement is an external operating-system contract.
3. **Custom third-party linker scripts with overlapping virtual address overlays:** `checkLinkedBinaryWF` assumes non-overlapping loaded executable segments as emitted by standard `rust-lld` target configurations.

## Evidence

- **Lean 4 mechanization ([support/VerifiedPostLinkValidator.lean](support/VerifiedPostLinkValidator.lean)):** `349` total lines (`297` non-comment code lines), `6` theorems (`gotpcrelx_mov_to_lea_equiv`, `checkLinked843419Site_sound`, `bti_j_rejected_as_veneer_target`, `missing_obj_gnu_property_detected`, `gcs_shadow_stack_sound_and_catches_tamper`, `checkLinkedBinaryWF_sound`), `0` `sorry`, `0` `native_decide`, `#eval checkAllM7 = true`, verified in `912.38 ms`.
- **8-target post-link oracle ([support/check_linked_binary_wf.py](support/check_linked_binary_wf.py) and [support/postlink_validator_audit.json](support/postlink_validator_audit.json)):** Verifies all `8` Tier 1 targets plus all `4` post-link hazard/relaxation oracles.

## Revalidation

```bash
python3 support/check_linked_binary_wf.py
```
