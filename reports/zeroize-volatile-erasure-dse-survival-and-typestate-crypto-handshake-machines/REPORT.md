# Volatile Secret Erasure Across LLVM Dead Store Elimination and Linear Cryptographic Handshake Typestate Machines

## Summary

Standard Rust MIR memory-safety models—including conservative move deinitialization (`deinitMovedPlace = true` in `joshlf/anneal`'s `Trusted.MirSemantics.evalOperandToSlot`, which resets moved non-ZST locals to `.live none`)—cannot verify cryptographic secret erasure or protocol-state linearity. Two orthogonal semantic gaps separate UB-freedom from cryptographic correctness:

1. **Physical Secret Residue vs. Logical Move Deinitialization and Dead Store Elimination (DSE)**: Marking a moved MIR local `.live none` soundly faults subsequent *program reads*, yet in compiled code `Operand::Move` copies secret bytes to the destination while leaving physical secret bits intact in the source stack slot. Conversely, an ordinary non-volatile overwrite `key = [0u8; 32]` before `StorageDead` / `return` sets the MIR slot to zeros, yet optimizing backends (`LLVM` DSE and CompCert's `backend/Deadcode.v` at `Ireturn`) delete non-volatile stores to dead stack frames. `RustCrypto/utils`'s `zeroize` (`0feca06cf87e61567033a333feb79ecf3c427fea`) defeats DSE via a split backend—`core::ptr::write_volatile` for scalars/SIMD and non-`asm!` targets, paired with vectorized `core::ptr::write_bytes` + `core::arch::asm!("# {}", in(reg) ptr, options(readonly, preserves_flags, nostack))` on nine `HAS_ASM` architectures—having retired its historical `atomic::compiler_fence(Ordering::SeqCst)` barrier (leaving only an orphaned rustdoc link at `zeroize/src/lib.rs:211`). Under `cfg(miri)` on `HAS_ASM` hosts, however, `bulk.rs` still takes the `write_bytes` branch while `barrier.rs` degrades to best-effort `core::hint::black_box`, and `zeroize_flat_type` causes immediate UB on `NonZero*` (which `Zeroize` instead overwrites with `1`), references, or non-zero-tag enums.
2. **Affine Handshake Typestates and Key/Nonce Ratchets**: Production Rust protocols—`rustls` TLS 1.3 (`ExpectServerHello` $\to$ `ExpectEncryptedExtensions`, `KeySchedulePreHandshake` $\to$ `KeyScheduleHandshakeStart`, RFC 9849 `SelectedPskWithRejectedEch`, and `HandshakeAlignedProof`), `snow` Noise (`HandshakeState::into_transport_mode` and `CipherState` reserving nonce `u64::MAX` for rekey), and `openmls` MLS (`KeySchedule` `Initial` $\to$ `Context` $\to$ `Done`, `SecretTree` path deletion, and `RatchetSecret` `u32::MAX` generation bounds)—enforce security via affine value-consuming transitions and monotonic per-epoch counters whose violation causes nonce reuse or transcript confusion without Rust UB.

Formalizing both properties in Pass-1 Lean 4 (`v4.34.1`, `prelude` + locked `Init.*` only) requires: (a) a minimal `Trusted.MirSemantics` trace witness (`ObsEvent.volatileScrub`, mirroring CompCert's `EF_vstore` trace preservation) distinguishing observable erasures from DSE-eliminable stores; and (b) two zero-TCB `theory/` abstractions—a three-point physical taint lattice `SecResidue` (`clean | dirtySecret | scrubbed`) checked on both `.returned` and `.unwound` exits, and a deterministic `SessionTypestate` + `NonceGenerationRatchet` machine.

## Applicability

This report applies to Rust cryptographic primitives, key wrappers, and stateful transport/group-messaging machines verified at post-borrowck MIR and lowered through optimizing backends (`rustc`/LLVM, CompCert, Jasmin, or FaCT).

### Pass-1 Lean 4 Verification Context

In `joshlf/anneal` (`20aa204315cd36aaf944778b7d33c0d609ced8e8`, `docs/trust-model.md`, `trusted/audit/TrustedBoundary.lean`, `trusted/lean/foundation-lock.json`), **Pass 1** is the standalone Lean 4 (`v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`) kernel audit over 51 locked `Init.*` modules with `{Classical.choice, Quot.sound, propext}`, explicit `prelude` headers, closed pure syntax (`allowedTheorySyntaxKinds`), and zero `partial`/`._unsafe_rec` or `Lean.ofReduceBool` constants.

### Relationships Among Examined Subjects

1. **Rust Secret-Erasure Crate (`RustCrypto/utils` at `0feca06cf87e61567033a333feb79ecf3c427fea`)**: defines `zeroize` (`zeroize/src/{lib,barrier,bulk,stack,x86,aarch64}.rs`), governed by `HAS_ASM` (`aarch64`, `arm`, `arm64ec`, `loongarch64`, `riscv32`, `riscv64`, `s390x`, `x86`, `x86_64`), `cfg(miri)`, and Cargo features `alloc`/`std`.
2. **MIR Move Semantics (`rust-lang/rust` at `8144389c895da997dbdecaa635e41d6a50be6ffd` and `joshlf/anneal` at `20aa204315cd36aaf944778b7d33c0d609ced8e8`)**: define `Operand::Move` (`compiler/rustc_middle/src/mir/syntax.rs`) and `Trusted.MirSemantics.evalOperandToSlot` (`trusted/lean/Trusted/MirSemantics.lean:140–148, 934–975`).
3. **Compiler Side-Channel Bridges (`AbsInt/CompCert` at `2685140bf72c959446981fb99b5e44a8975021bc`, `jasmin-lang/jasmin` at `8c3279973a89afd969e50301f71563bb40d55724`, and `PLSysSec/fact` at `b3daa03f48447285117f426129dbf539a7f32f4a`)**: ground DSE stack deletion (`Deadcode.v`), volatile/inline-asm survival (`EF_vstore`, `FaCT` `SMemset` + `SelectAsm`), and post-regalloc spill scrubbing (`Jasmin` `StackZeroization`).
4. **Protocol Typestate Machines (`rustls/rustls` at `836e411eccaf7331f4c289aabef0de32474de3b8`, `mcginty/snow` at `8ac60f51cfe3e010c84f0a454cc575ad9204fa12`, and `openmls/openmls` at `ba267737b9511e538a77a41f4480fbed28ff4e83`)**: ground TLS 1.3 (RFC 8446 / RFC 9846 / RFC 9849), Noise Protocol Framework (Revision 34, 2018), and MLS (RFC 9420) invariants.

Source observations apply to the exact pinned revisions; the Pass-1 Lean 4 formalization in Finding 4 is **derived** from those primary implementations and specifications.

## Findings

### 1. `RustCrypto/utils` `zeroize`: `write_volatile`, `asm!` Barriers, Move Residue, and Validity Hazards

Basis: normative + documentation + source

Inspection of `zeroize/src/{lib,barrier,bulk,stack,x86,aarch64}.rs` (`RustCrypto/utils` `0feca06cf87e61567033a333feb79ecf3c427fea`) establishes five core properties:

1. **Scalar `write_volatile` vs. Bulk `write_bytes` + `asm!` Barrier (and Retirement of `compiler_fence`)**:
   - *Scalars & SIMD (`lib.rs:278–300, 798–801`, `x86.rs:10–25`, `aarch64.rs:7–30`)*: `DefaultIsZeroes` primitives and x86/NEON SIMD registers (`__m128*`–`__m512*`, `uint8x8_t`–`uint64x2_t`) call `unsafe { ptr::write_volatile(dst, src) }`. Historical `atomic::compiler_fence(Ordering::SeqCst)` calls have been completely removed (leaving only an unused doc link `//! [`Ordering::SeqCst`]: core::sync::atomic::Ordering::SeqCst` at `lib.rs:211`), because LLVM `store volatile` is itself an observable side effect immune to DSE, whereas `compiler_fence` only orders intra-thread memory operations relative to signal handlers without making dead stack stores live past `ret`.
   - *Bulk Erasure (`bulk.rs:6–95`, `barrier.rs:52–89`)*: On the nine `HAS_ASM` architectures (`bulk.rs:7–17`), `fill_slice` (`L21–32`) and `zeroize_byte_ptr` (`L44–60`) execute non-volatile `dst.fill(src)` or `core::ptr::write_bytes(dst, 0, len)` (enabling vectorized `memset` / `rep stosb`) followed by `optimization_barrier`:
     `core::arch::asm!("# {}", in(reg) core::ptr::from_ref::<T>(val).cast::<()>(), options(readonly, preserves_flags, nostack))` (`barrier.rs:68–72`). Passing the pointer with `readonly` (omitting `nomem`/`pure`) forces LLVM MemorySSA/DSE to treat the empty assembly block as reading all bytes reachable from `val`'s provenance. On non-`HAS_ASM` targets, `volatile_fill_slice` (`bulk.rs:64–94`) splits slices via `as_chunks_mut` into 16-byte chunks (`[[T; 16/8/4/2]]`) and loops `volatile_write`.
2. **The `HAS_ASM` vs. `cfg(miri)` Discrepancy (`bulk.rs:7` vs. `barrier.rs:53–55, 88`)**:
   `bulk.rs:7–17` defines `HAS_ASM` without checking `not(miri)`, whereas `barrier.rs:53–55` gates `asm!` on `#[cfg(all(not(miri), any(target_arch = ...)))]` and falls back at `L88` to `core::hint::black_box(val)`. Under Miri on `x86_64`/`aarch64`, `zeroize_byte_ptr` therefore executes non-volatile `write_bytes` + `black_box` rather than `volatile_fill_slice`. Because Rust specifies `black_box` as best-effort only, formal models must reject `black_box` as a normative DSE barrier.
3. **Type-Validity Preservation (`NonZero*`, `Option<Z>`) vs. `zeroize_flat_type` UB Traps**:
   - `impl_zeroize_for_non_zero!` (`lib.rs:307–336`) overwrites `NonZeroI8`–`NonZeroUsize` via `volatile_write(self, ONE)` (`1`), avoiding niche-validity UB from writing `0`.
   - `Option<Z>::zeroize` (`lib.rs:371–407`) runs four steps: if `Some(v)`, `v.zeroize()` then `self.take()` (dropping inner heap allocations); `zeroize_byte_ptr` across `size_of::<Self>()` (wiping payload bytes from previously moved/copied `Some` states); and `ptr::write_volatile(self, None)` (restoring a valid `None` discriminant).
   - `zeroize_flat_type<F: Sized>(data: *mut F)` (`lib.rs:733–795`) raw-zeroes `size_of::<F>()` bytes; calling it on `&T`/`&mut T`, `NonNull<T>`, `NonZero*`, non-zero-tag enums, or `Drop`/heap types (`Vec`, `Box`, `String`, `Arc`) causes immediate invalidity UB or memory leaks (`L748–758`).
4. **Container & Stack Caveats (`Vec`, `CString`, `zeroize_stack`)**:
   `Vec<Z>::zeroize` (`lib.rs:497–518`) zeroes `spare_capacity_mut()` *before* `iter_mut().zeroize()` and `clear()`, leaving any prior reallocation buffers un-scrubbed (`Box<[Z]>` at `L524–533` avoids reallocation); `CString::zeroize` (`L553–575`) allocates a 1-byte `\0` buffer via `mem::take`; and `zeroize_stack::<N>()` (`stack.rs:14–45`) fails if the sensitive callee is inlined into the caller.
5. **Why `Operand.move` Deinitialization (`deinitMovedPlace`) Misses Physical Move Residue**:
   In `rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`, `compiler/rustc_middle/src/mir/syntax.rs`), `Operand::Move` performs no runtime memory overwrite in codegen. `joshlf/anneal` (`20aa204315cd36aaf944778b7d33c0d609ced8e8`, `trusted/lean/Trusted/MirSemantics.lean:140–148, 942–964`) sets moved non-ZST locals to `.live none`, which catches *post-move reads* but masks stack duplication: `let z = Zeroizing::new(secret_arr);` copies `secret_arr` into `z`, and `Zeroizing::drop` (`lib.rs:682–689`) scrubs only `z`, leaving all secret bytes intact in `secret_arr`'s physical stack frame!

### 2. Compiler-Preserved Erasure and Constant-Time Lowering Bridges: `CompCert`, `Jasmin`, and `FaCT`

Basis: normative + source

1. **Mechanized DSE Deletion of Non-Volatile Stack Zeroing (`AbsInt/CompCert` `2685140bf72c959446981fb99b5e44a8975021bc`)**:
   In CompCert's RTL neededness pass (`backend/Deadcode.v:90–236`), `transfer` sets post-state memory demand at `Ireturn optarg` (`L173–175`) and `Itailcall` (`L163–165`) to `nmem_dead_stack f.(fn_stacksize)`. Any preceding non-volatile `Istore` (`L147–153, 209–213`) or `EF_memcpy` (`L104–110, 222–225`) to `Stk ofs` fails `nmem_contains` and rewrites to `Inop s`! Conversely, `EF_vstore chunk` (`L99–103, 233–234`) survives untouched because CompCert's `common/Events.v` records `Event_vstore` in the observable trace `t` preserved across simulation (`CompCert-CT`, Barthe et al., POPL 2020; cf. Simon et al., EuroS&P 2018 on LLVM/GCC DSE).
2. **Post-Linearization Spill Erasure in `Jasmin` (`jasmin-lang/jasmin` `8c3279973a89afd969e50301f71563bb40d55724`)**:
   Source/MIR `write_volatile` cannot name anonymous spill slots introduced by register allocation (`zeroize/src/lib.rs:169–170`). In `proofs/compiler/compiler.v:126–161`, `compiler_step_list` places `StackZeroization` (#31) **after** `LowerSpill`, `StackAllocation`, `RegAllocation`, `DeadCode_RegAllocation`, and `Linearization` (just before `Tunneling` and `Assembly`). `stack_zeroization_lfd_body` (`proofs/compiler/stack_zeroization.v:75–128`) verifies `is_align frame_size ws_align`, `is_align stk_max ws`, `ws <= ws_align`, `~~ Sv.mem (vid rspn) vars`, and `disjoint vars (Sv.union callee_saved (sv_of_list v_var lfd.(lfd_res)))` before appending the scrub loop to export functions.
3. **Hardening LLVM Lowering in `FaCT` (`PLSysSec/fact` `b3daa03f48447285117f426129dbf539a7f32f4a`)**:
   In `src/intrinsics.ml:5–208`, `SMemset sz` (`L106–124`) calls `llvm.memset.p0i8.i64` with `isvolatile = const_int i1ty 1` (vs. `Memset sz` `isvolatile = 0` at `L98`), while `SelectAsm`/`CmovAsm` (`L20–21, 174–195`) emit inline x86 assembly `"testb $1, $1; mov $3, $0; cmovnz $2, $0"` (`"=&r,r,r,r,~{flags}"`) instead of `build_select` (`L203`) so LLVM `SelectionDAG` cannot re-introduce secret-dependent branches.

### 3. Linear Handshake Typestate Machines and Key/Nonce Ratchets in `rustls`, `snow`, and `OpenMLS`

Basis: normative + source

| Subject & Pinned Revision | Typestate / Ratchet Carrier | Linear Transition & Counter Update | Critical Protocol Guard & Error |
| :--- | :--- | :--- | :--- |
| **`rustls/rustls`** (`836e411eccaf`) | `ExpectServerHello` $\to$ `ExpectEncryptedExtensions`; `KeySchedulePreHandshake` $\to$ `KeyScheduleHandshakeStart` | `handle_server_hello(..., mut st: ExpectServerHello, ...)` (`client/tls13.rs:74–309`); `into_handshake(self, ...)` (`key_schedule.rs:218–225`) | `SelectedPskWithRejectedEch` (`tls13.rs:236–238`), `EarlyDataOfferedWithVariedCipherSuite` (`L168–171`), `check_aligned_handshake() -> HandshakeAlignedProof` (`L247, 269`) |
| **`mcginty/snow`** (`8ac60f51cfe3`) | `HandshakeState` $\to$ `TransportState`; `CipherState { cipher, n: u64, has_key }` | `into_transport_mode(self)` when `pattern_position == message_patterns.len()` (`handshakestate.rs:496–524`); `self.n += 1` (`cipherstate.rs:45, 68`) | `!self.has_key` $\to$ `MissingKeyMaterial` (`cipherstate.rs:37–39`); `validate_nonce` rejecting `u64::MAX` $\to$ `StateProblem::Exhausted` (`L171–180`) |
| **`openmls/openmls`** (`ba267737b951`) | `KeySchedule` (`Initial` $\to$ `Context` $\to$ `Done`), `SecretTree`, `RatchetSecret { secret, generation: u32 }` | `.take()` on `intermediate_secret` (`schedule/mod.rs:491`) & `epoch_secret` (`L526`); `ratchet_forward` (`sender_ratchet.rs:187–200`) | `InvalidState` (`L486, 522`); `SecretReuseError` (`secret_tree.rs:34–35`); `RatchetTypeError` (`L37–38`); `generation == u32::MAX` $\to$ `RatchetTooLong` (`sender_ratchet.rs:196–198`) |

1. **`rustls` TLS 1.3 (`rustls/src/client/tls13.rs:83–277`, `tls13/key_schedule.rs:27–318`)**:
   On non-resumption (`L190–196`), `handle_server_hello` discards `early_data_key_schedule`, clears `resuming_session.take()`, and resets `in_early_traffic = false` so client handshake flights use handshake keys (`L271–276`). Under Encrypted Client Hello (`L203–243`, RFC 9849 §6.1.2), `Some(accepted)` swaps `transcript`, `randoms.client`, and `hello.sent_extensions` to `ClientHelloInner` (`L225–233`), whereas `None if server_hello.preshared_key.is_some()` aborts with `PeerMisbehaved::SelectedPskWithRejectedEch` (`L236–238`) because `ClientHelloOuter` offered only a GREASE PSK. `input.check_aligned_handshake()?` (`L247`) yields a `HandshakeAlignedProof` token required by `set_record_decrypter` (`L269`) to prevent coalesced record-fragment key confusion.
2. **`snow` Noise (`src/handshakestate.rs:494–534`, `src/cipherstate.rs:31–186`)**:
   `CipherState` enforces `validate_nonce(self.n)?` (`n < u64::MAX`, reserving $2^{64}-1$ for Noise §4.2 `rekey()`) before incrementing `self.n += 1`. By contrast, `From<CipherState> for StatelessCipherState` (`cipherstate.rs:182–186`) discards `self.n` and exposes `encrypt_ad(&self, nonce: u64, ...)` (`L124–138`), shifting nonce uniqueness from Rust's borrow checker to caller verification preconditions.
3. **`OpenMLS` (`openmls/src/schedule/mod.rs:476–595`, `tree/{secret_tree,sender_ratchet}.rs`)**:
   `SecretTree::new` (`secret_tree.rs:197–229`) consumes `EncryptionSecret` (`consume_secret()`), derives direct-path secrets (`derive_child_secrets`, `L119–139`), deletes consumed tree nodes (`SecretReuseError`), separates own `EncryptionRatchet` from peer `DecryptionRatchet` (`SenderRatchetConfiguration` default `out_of_order_tolerance = 5`, `maximum_forward_distance = 1000`, `sender_ratchet.rs:36–64`), and rejects `self.generation == u32::MAX` (`RatchetTooLong`, `L196–198`).

### 4. Formalizing `SecResidue` and `SessionTypestate` in Pass-1 Lean 4

Basis: source + derived

Adding one minimal trace event `ObsEvent.volatileScrub (allocId offset byteLen : Nat)` (~35 LOC) to `Trusted.MirSemantics` on `CoreBuiltin.writeVolatile` and non-`nomem` `readonly` `InlineAsm` suffices to anchor DSE-immune erasure in the TCB. All taint propagation across `Operand.move`, `NonZero` validity checks, unwind-exit checks, and protocol typestates reside in Pass-1 `theory/` (`prelude`, locked `Init.*` only, zero `Array`/`._unsafe_rec`/`ofReduceBool`):

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic

namespace Pass1ZeroizeTypestate

-- 1. Radix-2 `Trie` for Stack/Heap Slot Residue
inductive Trie (α : Type) where
  | empty
  | node (val : Option α) (ev od : Trie α)

def Trie.get {α : Type} (depth : Nat) (t : Trie α) (k : Nat) : Option α :=
  @Nat.rec (fun _ => Trie α → Nat → Option α)
    (fun _ _ => none)
    (fun _ ih cur idx =>
      match cur with
      | .empty => none
      | .node v ev od =>
        match idx with
        | 0 => v
        | _ =>
          match Nat.beq (Nat.land idx 1) 0 with
          | true  => ih ev (Nat.shiftRight idx 1)
          | false => ih od (Nat.shiftRight idx 1))
    depth t k

def Trie.set {α : Type} (depth : Nat) (t : Trie α) (k : Nat) (v : Option α) : Trie α :=
  @Nat.rec (fun _ => Trie α → Nat → Trie α)
    (fun cur _ => cur)
    (fun _ ih cur idx =>
      let (v0, ev0, od0) := match cur with
        | .empty => (none, Trie.empty, Trie.empty)
        | .node old ev od => (old, ev, od)
      match idx with
      | 0 => .node v ev0 od0
      | _ =>
        match Nat.beq (Nat.land idx 1) 0 with
        | true  => .node v0 (ih ev0 (Nat.shiftRight idx 1)) od0
        | false => .node v0 ev0 (ih od0 (Nat.shiftRight idx 1)))
    depth t k

-- 2. `SecResidue`: Physical Secret-Residue Lattice Orthogonal to `logicalInit`
inductive SecResidue where
  | clean
  | dirtySecret
  | scrubbed

structure DualSlot where
  logicalInit : Bool        -- `false` after `Operand.move` (`deinitMovedPlace = true`)
  residue     : SecResidue  -- Physical stack/heap residue

def stepMoveSlot (depth srcId dstId : Nat) (frame : Trie DualSlot) : Option (Trie DualSlot) :=
  match Trie.get depth frame srcId with
  | none => none
  | some src =>
    match src.logicalInit with
    | false => none
    | true =>
      -- `Operand.move` marks `src` logically uninit YET leaves `src.residue` on stack!
      let f1 := Trie.set depth frame srcId (some ⟨false, src.residue⟩)
      some (Trie.set depth f1 dstId (some ⟨true, src.residue⟩))

inductive ZeroizeTargetKind where
  | flatAllZeroValid
  | nonZeroScalar
  | hasInvalidAllZeroTag

inductive StoreBarrierKind where
  | nonVolatile
  | hintBlackBoxMiri
  | volatileWriteScalar
  | writeBytesAsmBarrier

def isNormativeDseBarrier (b : StoreBarrierKind) : Bool :=
  match b with
  | .volatileWriteScalar | .writeBytesAsmBarrier => true
  | .nonVolatile | .hintBlackBoxMiri => false

def stepPublicWipe (depth slotId : Nat) (kind : ZeroizeTargetKind)
    (barrier : StoreBarrierKind) (writesAllZeroBytes : Bool)
    (frame : Trie DualSlot) : Option (Trie DualSlot) :=
  let typeValid := match writesAllZeroBytes, kind with
    | true, .flatAllZeroValid => true
    | false, .nonZeroScalar => true
    | false, .flatAllZeroValid => true
    | _, _ => false
  match typeValid with
  | false => none
  | true =>
    let prevRes := match Trie.get depth frame slotId with | some s => s.residue | none => .clean
    let nextRes := match prevRes, isNormativeDseBarrier barrier with
      | .dirtySecret, true  => .scrubbed
      | .dirtySecret, false => .dirtySecret
      | .scrubbed, _        => .scrubbed
      | .clean, _           => .clean
    some (Trie.set depth frame slotId (some ⟨true, nextRes⟩))

def frameExitZeroized (depth : Nat) (slotIds : List Nat) (frame : Trie DualSlot) : Bool :=
  slotIds.foldr
    (fun sid ok =>
      ok && match Trie.get depth frame sid with
        | none => true
        | some s => match s.residue with | .dirtySecret => false | .clean | .scrubbed => true)
    true

-- 3. `SessionTypestate` & `NonceGenerationRatchet` (`rustls`, `snow`, `openmls`)
inductive Tls13Phase where
  | expectServerHello (echOffered hasEarlyKeySched : Bool)
  | expectEncryptedExts (echAccepted inEarlyTraffic : Bool)
  | waitFinished
  | applicationTraffic (epoch nextNonce : Nat)
  | aborted

structure ServerHelloCtx where
  plaintextExtsAllowed : Bool
  sessionIdMatched     : Bool
  keyShareGroupOffered : Bool
  pskSelected          : Option Nat
  resumingSuiteCompat  : Bool
  earlyDataSuiteSame   : Bool
  echAcceptedByServer  : Bool
  handshakeAligned     : Bool

def stepTls13ServerHello (st : Tls13Phase) (ctx : ServerHelloCtx) : Tls13Phase :=
  match st with
  | .expectServerHello echOffered hasEarly =>
    match ctx.plaintextExtsAllowed && ctx.sessionIdMatched &&
          ctx.keyShareGroupOffered && ctx.handshakeAligned with
    | false => .aborted
    | true =>
      let echPskIllegal := echOffered && (!ctx.echAcceptedByServer) &&
        match ctx.pskSelected with | some _ => true | none => false
      match echPskIllegal with
      | true => .aborted
      | false =>
        match ctx.pskSelected, hasEarly with
        | some idx, true =>
          match Nat.beq idx 0 && ctx.resumingSuiteCompat && ctx.earlyDataSuiteSame with
          | true  => .expectEncryptedExts ctx.echAcceptedByServer true
          | false => .aborted
        | some _, false => .aborted
        | none, _ => .expectEncryptedExts ctx.echAcceptedByServer false
  | _ => .aborted

def stepNoiseNonce (hasKey : Bool) (curNonce maxReservedNonce : Nat) : Option Nat :=
  match hasKey && Nat.blt curNonce maxReservedNonce with
  | true  => some (curNonce + 1)
  | false => none

inductive MlsSchedulePhase where
  | initial (hasIntermediate : Bool)
  | context (hasEpochSecret : Bool)
  | done (generation maxGen : Nat)
  | invalid

def stepMlsSenderRatchet (st : MlsSchedulePhase) : MlsSchedulePhase :=
  match st with
  | .done gen maxGen =>
    match Nat.blt gen maxGen with
    | true  => .done (gen + 1) maxGen
    | false => .invalid
  | _ => .invalid

-- Concrete Kernel `rfl` Canaries
theorem dse_and_miri_blackbox_caught :
    let f0 := Trie.set 4 Trie.empty 1 (some ⟨true, .dirtySecret⟩)
    (match stepPublicWipe 4 1 .flatAllZeroValid .nonVolatile true f0 with
     | some f1 => frameExitZeroized 4 [1] f1 | none => false) = false ∧
    (match stepPublicWipe 4 1 .flatAllZeroValid .hintBlackBoxMiri true f0 with
     | some f1 => frameExitZeroized 4 [1] f1 | none => false) = false ∧
    (match stepPublicWipe 4 1 .flatAllZeroValid .writeBytesAsmBarrier true f0 with
     | some f1 => frameExitZeroized 4 [1] f1 | none => false) = true := ⟨rfl, ⟨rfl, rfl⟩⟩

theorem move_residue_leak_caught :
    let f0 := Trie.set 4 Trie.empty 1 (some ⟨true, .dirtySecret⟩)
    (match stepMoveSlot 4 1 2 f0 with
     | none => false
     | some fMoved =>
       match stepPublicWipe 4 2 .flatAllZeroValid .writeBytesAsmBarrier true fMoved with
       | none => false
       | some fScrubbedDst => frameExitZeroized 4 [1, 2] fScrubbedDst) = false := rfl

theorem nonzero_flat_zeroize_ub_caught :
    let f0 := Trie.set 4 Trie.empty 1 (some ⟨true, .dirtySecret⟩)
    stepPublicWipe 4 1 .nonZeroScalar .writeBytesAsmBarrier true f0 = none ∧
    (match stepPublicWipe 4 1 .nonZeroScalar .volatileWriteScalar false f0 with
     | some f1 => frameExitZeroized 4 [1] f1 | none => false) = true := ⟨rfl, rfl⟩

theorem tls13_ech_psk_and_noise_max_nonce_caught :
    stepTls13ServerHello (.expectServerHello true true)
      ⟨true, true, true, some 0, true, true, false, true⟩ = .aborted ∧
    stepNoiseNonce true 18446744073709551615 18446744073709551615 = none := ⟨rfl, rfl⟩

end Pass1ZeroizeTypestate
```

## Boundaries

- **Known not to apply — `zeroize` scrubbing CPU registers, register-allocator stack spills, or prior `Vec` heap reallocations**: `Zeroize` (`zeroize/src/lib.rs:169–180, 192–195, 503–504`) scrubs only addressable `&mut self` memory. Without a post-regalloc pass like `Jasmin`'s `StackZeroization` (`proofs/compiler/compiler.v:158`) or compiler support (`rust-lang/rust#17046`), LLVM may leave secrets in registers or anonymous spill slots, and `Vec::zeroize` cannot scrub freed buffers from earlier reallocations.
- **Known not to apply — `core::hint::black_box` (`cfg(miri)`) as a normative DSE barrier**: On `HAS_ASM` targets under Miri, `bulk.rs:7–17` + `barrier.rs:88` executes non-volatile `write_bytes` + `black_box`, which provides no normative guarantee against compiler DSE.
- **Known not to apply — `StatelessCipherState` (`mcginty/snow`) enforcing nonce uniqueness via Rust types**: `StatelessCipherState::encrypt_ad(&self, nonce: u64, ...)` (`snow/src/cipherstate.rs:124–138`) checks only `nonce != u64::MAX`; caller-level linear ghost capabilities are required to prevent nonce reuse.
- **Unsupported — `zeroize_flat_type` on references, `NonNull`, `NonZero*`, non-zero-tag enums, and `Drop`/heap types**: Explicitly disallowed by `zeroize/src/lib.rs:748–758` due to bit-validity UB and heap leaks.
- **Unknown — Mechanized end-to-end preservation of `asm!(..., options(readonly, preserves_flags, nostack))` across future LLVM IPO passes**: Unlike CompCert's `EF_vstore` (`Deadcode.v`), stock LLVM lacks a mechanized trace-preservation theorem over inline-assembly pointer provenance.
- **Not examined — Microarchitectural transient-execution/cache covert channels (`Spectre`/`Meltdown`) and computational game-hopping proofs**: Hardware side channels after architectural memory scrubbing (`zeroize/src/lib.rs:160–163`) and IND-CCA/TreeKEM reductions are outside scope.

## Evidence

### Primary Repository Sources (Observed 2026-11-20)

- **`RustCrypto/utils`** at `0feca06cf87e61567033a333feb79ecf3c427fea`: `zeroize/src/lib.rs:148–212, 252–336, 371–453, 497–575, 582–689, 728–801`; `zeroize/src/barrier.rs:52–89`; `zeroize/src/bulk.rs:6–114`; `zeroize/src/stack.rs:14–45`; `zeroize/src/x86.rs:10–25`; `zeroize/src/aarch64.rs:7–30`.
- **`rustls/rustls`** at `836e411eccaf7331f4c289aabef0de32474de3b8`: `rustls/src/client/tls13.rs:74–309`; `rustls/src/tls13/key_schedule.rs:21–318`.
- **`mcginty/snow`** at `8ac60f51cfe3e010c84f0a454cc575ad9204fa12`: `src/handshakestate.rs:494–534`; `src/cipherstate.rs:10–194`.
- **`openmls/openmls`** at `ba267737b9511e538a77a41f4480fbed28ff4e83`: `openmls/src/schedule/mod.rs:476–595`; `openmls/src/tree/secret_tree.rs:23–51, 119–166, 183–300`; `openmls/src/tree/sender_ratchet.rs:21–90, 159–200`.
- **`AbsInt/CompCert`** at `2685140bf72c959446981fb99b5e44a8975021bc`: `backend/Deadcode.v:90–236`; `common/Events.v`.
- **`jasmin-lang/jasmin`** at `8c3279973a89afd969e50301f71563bb40d55724`: `proofs/compiler/compiler.v:126–162`; `proofs/compiler/stack_zeroization.v:50–141`.
- **`PLSysSec/fact`** at `b3daa03f48447285117f426129dbf539a7f32f4a`: `src/intrinsics.ml:5–208`.
- **`rust-lang/rust`** at `8144389c895da997dbdecaa635e41d6a50be6ffd` & **`joshlf/anneal`** at `20aa204315cd36aaf944778b7d33c0d609ced8e8`: `trusted/lean/Trusted/MirSemantics.lean:126–148, 934–975`; `trusted/audit/TrustedBoundary.lean:442–574, 1108–1125`.

### Normative Specifications and Peer-Reviewed Literature

- Laurent Simon, David Chisnall, and Ross Anderson, *"What You Get Is What You C: Controlling Side Effects in Mainstream C Compilers,"* IEEE EuroS&P 2018, pp. 1–15, 2018. DOI: `10.1109/eurosp.2018.00009`.
- José Bacelar Almeida, Manuel Barbosa, Gilles Barthe, Arthur Blot, Benjamin Grégoire, Vincent Laporte, Tiago Oliveira, Hugo Pacheco, Benedikt Schmidt, and Pierre-Yves Strub, *"Jasmin: High-Assurance and High-Speed Cryptography,"* ACM CCS 2017, pp. 1807–1823, 2017. DOI: `10.1145/3133956.3134078`.
- Gilles Barthe, Sandrine Blazy, Benjamin Grégoire, Rémi Hutin, Vincent Laporte, David Pichardie, and Alix Trieu, *"Formal Verification of a Constant-Time Preserving C Compiler,"* *Proc. ACM Program. Lang.* 4 (POPL), Article 7, 2020. DOI: `10.1145/3371075`.
- Sunjay Cauligi, Gary Soeller, Brian Johannesmeyer, Fraser Brown, Riad S. Wahby, John Renner, Benjamin Grégoire, Gilles Barthe, Ranjit Jhala, and Deian Stefan, *"FaCT: A DSL for Timing-Sensitive Computation,"* ACM PLDI 2019, pp. 174–189, 2019. DOI: `10.1145/3314221.3314605`.
- IETF RFC 8446 / RFC 9846 (*TLS 1.3*), RFC 9849 (*TLS Encrypted Client Hello*), RFC 9420 (*Messaging Layer Security*), and Trevor Perrin, *The Noise Protocol Framework*, Revision 34 (2018).

## Revalidation

1. **`zeroize` Barrier & Intrinsics Diff (`RustCrypto/utils`)**: Diff `zeroize/src/{lib,barrier,bulk}.rs` to check whether `bulk.rs` `HAS_ASM` adds `not(miri)` or migrates to `volatile_set_memory`, whether `barrier.rs` keeps `options(readonly, preserves_flags, nostack)`, and whether `Option<Z>::zeroize` and `NonZero*` retain their four-step and `ONE`-write invariants.
2. **Protocol Typestate Guards (`rustls`, `snow`, `openmls`)**: Diff `rustls/src/client/tls13.rs` (`SelectedPskWithRejectedEch`, `early_data_key_schedule`, `check_aligned_handshake`), `snow/src/cipherstate.rs` (`validate_nonce` `u64::MAX`), and `openmls/src/schedule/mod.rs` + `tree/sender_ratchet.rs` (`State::{Initial, Context, Done}`, `u32::MAX`).
3. **Pass-1 Kernel Check (`joshlf/anneal`)**: Run Pass-1 `"preflight"` and standalone `lean` `v4.34.1` replay on `Pass1ZeroizeTypestate` in Finding 4.
