# Double-Fetch TOCTOU Verification over Shared Userspace/DMA Rings and Single-Fetch Logics

## Summary

A **double-fetch time-of-check-to-time-of-use (TOCTOU)** defect arises whenever a privileged execution context (OS kernel, hypervisor, or trusted driver) reads memory concurrently writable by an untrusted actor (userspace thread, peer protection domain, or bus-master DMA peripheral) more than once across a validation-and-use dependency. Soundly verifying Rust and C systems code over shared submission/completion rings (`io_uring`, Fuchsia `IOBuffer`, virtio/NVMe DMA queues) and syscall buffers (`copy_from_user`, `UserSlice`, Zircon `user_in_ptr`) requires discharging **two distinct obligations** that single-thread separation logics conflate:

1. **Language-Level Aliasing and Tear-Freedom (Compiler UB Barrier):** Forming a shared Rust reference (`&[u8]` or `zerocopy::Ref<&[u8], T>` for `T: FromBytes + Immutable`) over memory subject to concurrent external mutation without `UnsafeCell` is immediate undefined behavior in Rust and LLVM (`readonly`/`dereferenceable`), permitting compiler load-widening, CSE elimination, or post-check reload synthesis even when source code reads a field syntactically once. Untrusted shared memory must be accessed strictly through opaque untyped handles (`UserSliceReader`, `VmReader`, volatile `READ_ONCE`, or `copy_from_user`) until copied or quiesced.
2. **Logical Single-Fetch Stability (Adversarial Environment Barrier):** Even when every load is UB-free and non-tearing, two sequential fetches from the same shared address can observe unrelated byte values injected by a racing thread or DMA engine. In Iris-style logics, an unconstrained shared invariant $\text{inv}(N, \exists v.\, a \mapsto v)$ yields fresh, unlinked existentials $v_1, v_2$ on consecutive openings. In constructive 3-axiom Lean 4 (`{propext, Quot.sound, Classical.choice}`) verification libraries such as `Anneal`'s `theory/` layer, this concurrent environment reduces without step-indexing or `Classical.choice` to a **deterministic demonic fetch oracle** (`DemonicOracle : Addr → Gen → Word` paired with a strictly monotonic per-address generation counter):
   - **Copy-in Promotion (`OpaqueDma → PrivateSnapshot`):** Reading an untrusted header/length at generation $0$, checking `rawLen ≤ maxCap`, and copying `rawLen` elements *once* into an exclusively owned local buffer (`PrivateSnapshot` / `SpatialBlock`) isolates all downstream parsing and `zerocopy` casts from generations $g \ge 1$.
   - **Zero-Copy Promotion (`OpaqueDma → LoanFrame`):** Elevating a shared physical frame directly to a stable typed borrow without copying is sound **if and only if** active bus-master DMA to the frame is quiesced **and** either (a) sender and receiver share a single-threaded execution domain, or (b) all writable mappings in untrusted domains have been unmapped *and* cross-CPU TLB shootdowns have completed.

## Applicability

This report governs formal specification, deductive verification, and `unsafe` Rust API design for code that ingests descriptors, headers, or bulk payloads across shared-memory trust boundaries:

- **Concrete OS Ring and Untrusted-Copy Substrates (`torvalds/linux` at `65e4fd942f72a9dba0e4e257290c4fa1aa756854`, `asterinas/asterinas` at `7fecb4ffabc72d0767277a9ffb66168bc512034c`, and Fuchsia RFC-0218 / Zircon):** Characterize production memory-ordering, single-copy, and untyped-reader contracts in Linux `io_uring`, Rust-for-Linux `kernel::uaccess::UserSlice`, Asterinas OSTD (`VmReader`, `PodOnce`, `DmaStream`, `DmaCoherent`), and Fuchsia `IOBuffer` / `zx_vmo`.
- **Safe Byte-Parsing Consumer (`google/zerocopy` at `ec133ce4d7993775413d852f91c9e3eb2a2a0897`):** Establishes the aliasing boundary at which `FromBytes`, `Immutable`, and `Ref<&[u8], T>` become sound (valid over `PrivateSnapshot` and quiesced `LoanFrame`, unsound directly over `OpaqueDma`), extending static layout coverage in `zerocopy-validity-predicates-projection-layout-and-ffi-intrinsics` to concurrent external writers.
- **Mechanized Program-Logic Baselines (`AbsInt/CompCert` at `2685140bf72c959446981fb99b5e44a8975021bc`, `PrincetonUniversity/VST` at `d50ac1969f9f6586621895eb043ccf08a165f731`, `mit-pdos/perennial` at `c44b7487179b2e88e9f4dd8b0155c893406571ef` and `c3b7ecff27c1a6e8ed058d5aca362df1e2f63311`, `leanprover-community/iris-lean` at `5540ef0110fc8f6d8e495c10c2f238c3ede14f3b`):** Contrast trace-event volatile loads, external world specifications, and higher-order concurrent separation logic invariants against pure functional fetch oracles.
- **Constructive Lean 4 Realization (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `leanprover/lean4` `v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52`):** Integrates single-fetch and zero-copy loan obligations with Anneal's `TrustedBoundary` (`prelude`-only `Init.*` imports, zero `noncomputable` definitions, axiom closure within `{propext, Quot.sound, Classical.choice}`, and `Anneal.PureLift.SpatialPin` heaplets).

Scope covers sequential or lock-serialized consumers running concurrently against adversarial external writers. Optimistic seqlock retry loops and lock-free multi-consumer ring stealing are bounded under **Boundaries**.

## Findings

### 1. Double-Fetch Failure Taxonomy and the Two-Layer Soundness Gap

`Basis: documentation + source + derived`

Empirical kernel vulnerability analysis by Wang et al. (*How Double-Fetch Situations Turn into Double-Fetch Vulnerabilities*, USENIX Security 2017, pp. 1–16; 90 Linux sites, 57 in drivers) and symbolic multi-read pair checking by Xu et al. (**Deadline**, *Precise and Scalable Detection of Double-Fetch Bugs in OS Kernels*, IEEE S&P 2018, DOI `10.1109/SP.2018.00017`) classify exploitable double-fetch bugs into three dependence patterns between an initial read $r_1$ and a subsequent read $r_2$ of overlapping untrusted addresses:

| Pattern | First Fetch ($r_1$: Check / Sizing) | Adversarial Mutation | Second Fetch ($r_2$: Use / Dispatch) | Resulting Exploit Primitive |
| :--- | :--- | :--- | :--- | :--- |
| **1. Shallow Length Check-vs-Use** | Reads `hdr->len` ($= 64$), checks `len <= MAX_BUF` ($256$), or allocates `kmalloc(len)`. | Racing thread or DMA engine overwrites `hdr->len := 512`. | Re-reads `hdr->len` from shared memory as the `memcpy` / `copy_from_user` byte count. | Kernel heap/stack buffer overflow (`512 > 256`). |
| **2. Overlapping Header-Payload Copy** | Copies header `copy_from_user(&k_hdr, u_ptr, sizeof(hdr))` and validates `k_hdr.msg_type` and `k_hdr.total_size`. | Adversary mutates `u_ptr->msg_type` or `u_ptr->total_size` during allocation. | Copies full message `copy_from_user(k_msg, u_ptr, k_hdr.total_size)`, **overwriting** the validated header prefix inside `k_msg` without re-checking or restoring `k_hdr`. | Validated header invariants in `k_msg` clobbered by unvalidated second-fetch bytes. |
| **3. Discriminant / Index Confusion** | Reads `req->opcode` or `desc->idx` to check permissions and select a dispatch arm. | Adversary flips `req->opcode` or `desc->idx` mid-check. | Handler reloads `req->opcode` or `desc->idx` from the shared ring slot to index a table or capability slot. | Out-of-bounds table dispatch, type confusion, or unauthorized capability use. |

Eliminating all three patterns in verified Rust and C requires separating two distinct semantic layers:

1. **Compiler-Synthesized Reloads (Language UB Layer):** In C without `volatile` (`READ_ONCE`) and in Rust whenever `&T` or `&[u8]` (without `UnsafeCell`) aliases concurrently mutated memory, the abstract machine assumes **byte stability** for the reference's lifetime. Even if source code reads `ring_ref.opcode` once into a local binding, LLVM may legally spill that binding by reloading `ring_ref.opcode` from memory after a bounds check, synthesizing a machine-code double fetch. Because `zerocopy::Immutable` (`zerocopy/src/lib.rs:1729`) certifies absence of `UnsafeCell`, constructing `zerocopy::Ref<&[u8], SqEntry>` (`zerocopy/src/lib.rs:4358–4372`) over a live userspace-mapped or DMA-writable ring is immediate language UB.
2. **Source-Level Multi-Reads (Logical Environment Layer):** Using UB-free untyped copy/volatile primitives (`copy_from_user`, `READ_ONCE`, `ptr::read_volatile`) prevents compiler reload synthesis, **but leaves repeated source-level reads unconstrained**. A sound logic must prevent unifying the return values of two UB-free fetches from the same untrusted address unless the region was copied into private memory or external writers were quiesced.

### 2. Primary-Source Contracts in Linux `io_uring`, Rust `uaccess`, Asterinas OSTD, and Zircon

`Basis: source + documentation`

#### 2.1 Linux `io_uring` Submission Ring Single-Fetch Protocol
In `torvalds/linux` (`65e4fd942f72a9dba0e4e257290c4fa1aa756854`), `io_uring` maps the index ring (`struct io_rings`) and Submission Queue Entry array (`struct io_uring_sqe`, `include/uapi/linux/io_uring.h`) into shared memory concurrently writable by userspace (`io_uring/io_uring.c:5–28`):
- **Private Head Cursor & `sq_array` Single Read (`io_uring/io_uring.c:2145–2169`):** `io_get_sqe` tracks `ctx->cached_sq_head` privately in kernel memory (`lines 2148, 2161–2168`) rather than trusting `rings->sq.head`. When `sq_array` indirection is enabled, it reads the slot index **once** via `head = READ_ONCE(ctx->sq_array[head]);` (`line 2152`, lowered via `include/asm-generic/rwonce.h`), checks `head >= ctx->sq_entries`, and applies `array_index_nospec(head, ctx->sq_entries)` (`line 2158`).
- **SQE Snapshot into `io_kiocb` (`io_uring/io_uring.c:1875–1900, 2063–2066`):** `io_init_req` copies shared `sqe` fields once via `READ_ONCE` into kernel-owned `struct io_kiocb *req` (`req->opcode = READ_ONCE(sqe->opcode); sqe_flags = READ_ONCE(sqe->flags); req->cqe.user_data = READ_ONCE(sqe->user_data);`), bounds-checks `req->opcode >= IORING_OP_LAST`, and masks `req->opcode` with `array_index_nospec`. Downstream BPF filters (`line 2049`) and async link preparation (`io_req_sqe_copy`, `line 2065`) operate exclusively on `req`.

#### 2.2 Rust-for-Linux `UserSlice` and Linear `UserSliceReader`
In `torvalds/linux` (`rust/kernel/uaccess.rs:66–75, 259–291`), `UserSlice` explicitly permits concurrent userspace data races over `bindings::copy_from_user` while prohibiting value-stability assumptions (`lines 69–75`):
> *"Concurrent access, \*including data races to/from userspace memory\*, is permitted... In the presence of a race, the exact byte values read/written are unspecified but the operation is well-defined. Kernelspace code should validate its copy of data after completing a read, and not expect that multiple reads of the same address will return the same value."*

Structurally, `UserSliceReader::read_raw(&mut self, out: &mut [MaybeUninit<u8>])` (`lines 265–280`) advances `self.ptr` and decrements `self.length` on every call and **omits `Clone`**, so Rust's borrow checker prevents sequential re-reads through the same `UserSliceReader` unless unsafe code reconstructs a fresh `UserSlice` over the raw pointer.

#### 2.3 Asterinas OSTD Untyped Memory (`VmReader`, `PodOnce`, `DmaStream`, `DmaCoherent`)
Asterinas (`asterinas/asterinas` at `7fecb4ffabc72d0767277a9ffb66168bc512034c`) isolates untrusted user and DMA pages as *untyped memory* inside `ostd`:
- `DmaCoherent::reader(&self)` (`ostd/src/mm/dma/dma_coherent.rs:170–182`) and `DmaStream` (`ostd/src/mm/dma/dma_stream.rs:81–86, 201–215`) never expose `&[u8]`; they yield `VmReader<'_, Infallible>` (`ostd/src/mm/io/mod.rs:309–313`).
- `VmReader::read_once<T: PodOnce>(&mut self)` (`ostd/src/mm/io/mod.rs:457–473`) statically enforces `is_non_tearing::<T>()` (`line 465`) and executes `cursor.read_volatile()` (`line 470`). Crucially, however, **`VmReader` implements `Clone`** (`ostd/src/mm/io/mod.rs:319–325`), and `VmIoOnce::read_val_once` accepts arbitrary offsets on `&self`. Consequently, OSTD's type system prevents **Layer 1 compiler UB**, but drivers can still clone a `VmReader` or re-read an offset and trigger a **Layer 2 logical double-fetch bug** without writing `unsafe`!
- For non-coherent streaming DMA, `DmaStream::sync_from_device(byte_range)` (`dma_stream.rs:201–210`) must invalidate CPU D-cache lines *after* device completion and *before* `VmReader` reads, coupling single-fetch discipline with cache coherence.

#### 2.4 Fuchsia Zircon `user_in_ptr`, `zx_vmo`, and RFC-0218 `IOBuffer`
Fuchsia's Zircon kernel enforces copy-in discipline on syscall pointers via `user_in_ptr<const T>`, while high-rate IPC uses `zx_vmo` Virtual Memory Objects and RFC-0218 `IOBuffer` (`Ep0`/`Ep1` peered shared regions with kernel-mediated ring access). Whenever a `zx_vmo` or `IOBuffer` page remains mapped writable in a peer process, direct `zerocopy::Ref<&[u8], T>` borrowing in the receiver is unsound; zero-copy borrowing requires page-loan unmapping or VMO lock/pinning with completed TLB shootdowns.

### 3. Program-Logic Encodings: Trace Oracles vs. Iris Invariants vs. Functional Fetch Oracles

`Basis: source + documentation + derived`

| Framework & Primary Source | Shared-Memory Encoding | Mechanism Preventing Unsound Read Unification | Proof & TCB Overhead |
| :--- | :--- | :--- | :--- |
| **CompCert + VST** (`AbsInt/CompCert` `common/Events.v:64–75, 698–703`; `PrincetonUniversity/VST` `veric/juicy_extspec.v`) | `volatile` loads emit trace events `Event_vload chunk id ofs v` (`volatile_load_sem`); VST threads external state `Z` via `external_specification`. | Consecutive `Event_vload` steps produce distinct universally quantified values `v1`, `v2` unless constrained by `ext_spec_post`. | No step-indexing for volatile loads, but bulk `copy_from_user` requires word-level trace induction or external call axioms. |
| **RGSep** (Vafeiadis, CONCUR 2007, DOI `10.1007/978-3-540-74407-8_33`) | Heap split into private state $L$ (rely $= \text{Id}$) and shared state $S$ under rely $R \subseteq S \times S$. | Under $R_{\text{demonic}} = S \times S$, shared assertions $S[a] = v_1$ fail stability $\text{stable}(P, R_{\text{demonic}})$ across steps; copied private assertions $L[k] = v_1$ remain stable. | Explicit stability side conditions on every rule over shared regions. |
| **Iris / Perennial** (`mit-pdos/perennial` `Perennial/GooseLang/Lang.lean:10–25`, `Slice.lean`; `iris-lean` `5540ef01...`; JFP 2018 DOI `10.1017/S0956796818000151`) | Shared location wrapped in invariant $\text{inv}(N, \exists v.\, l \mapsto v)$ opened only around atomic steps. | Opening $\text{inv}(N, \exists v.\, l \mapsto v)$ around two separate loads yields unrelated witnesses $v_1$ and $v_2$ unless tethered to monotone ghost state. | Step-indexed `▷` modalities, mask accounting, and (in `GooseLang/Lang.lean:24`) classical syntax decidability. |
| **Demonic Fetch Oracle + Generation Map** (3-axiom Lean 4 / `Anneal` `theory/`) | Pure `SharedRingState` pairing `oracle : Addr → Gen → Word` with monotonic per-address `gens` (`OpaqueDma`). | Fetch 1 at `addr` yields `oracle addr 0` (`gens := 1`); Fetch 2 yields `oracle addr 1`. Quantifying over all `oracle` leaves generations deductively independent. | **Zero TCB growth**, `Type 0` monomorphic, `0` `Classical.choice`, and constructive `rfl` counterexamples. |

**Environment Subsumption (`derived`):** For any sequential or lock-serialized consumer (`io_init_req` under `ctx->uring_lock` in `io_uring.c:1877`, or a syscall thread in `UserSliceReader::read_raw`), any concrete concurrent execution $\tau$ with arbitrary external writer interleavings induces an oracle $\Omega_\tau(a, g)$ returning the word present at address $a$ at the consumer's $g$-th load. Running the deterministic `SharedRingState` transitions on $\Omega_\tau$ reproduces $\tau$'s exact load values. Thus $\forall \Omega,\, \text{Safe}(\Omega)$ entails safety against all concurrent writer schedules, while any double-fetch bug admits a finite witness $\Omega_{\text{bad}}$ decidable by kernel reduction.

### 4. Three-State Region Lifecycle for `SpatialPin` and `zerocopy`

`Basis: source + derived`

In `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `theory/Anneal/PureLift/SpatialPin.lean:16–58` exports pure loans into `SpatialBlock Val` cells (`freezeToSpatialInState` / `reabsorbFromSpatialInState`), assuming **single-writer cell stability**. Untrusted rings integrate cleanly at `0-TCB` cost via a three-state promotion discipline:

```text
  ┌─────────────────────────────────────────────────────────────────────┐
  │ State 0: OpaqueDma / SharedRingState (Untrusted Shared Memory)      │
  │ • Backed by `DemonicOracle` (addr -> gen -> word) + `gens` counter  │
  │ • Rust `&[u8]` / `zerocopy::Ref` FORBIDDEN (aliasing UB)            │
  │ • Access restricted to `fetchWord` / `fetchSliceOnce` (`READ_ONCE`, │
  │   `UserSliceReader::read_raw`, `VmReader::read_once`)               │
  └───────────────┬─────────────────────────────────────┬───────────────┘
                  │ Rule A: Copy-In                     │ Rule B: Zero-Copy Loan
                  │ (`copyDescriptorOnce`)              │ (`canPromoteLoanFrame`)
                  ▼                                     ▼
  ┌───────────────────────────────┐     ┌───────────────────────────────┐
  │ State 1A: PrivateSnapshot     │     │ State 1B: Quiesced LoanFrame  │
  │ • Header length fetched ONCE  │     │ • `dmaEngineQuiesced = true`  │
  │   at gen g0; checked <= cap   │     │ • AND (`sameDom ∧ singleThr`  │
  │ • Payload [0..len) copied ONCE│     │   OR `unmapped ∧ tlbFlushed`) │
  │   into private `List` / stack │     │ • Frame frozen against races  │
  └───────────────┬───────────────┘     └───────────────┬───────────────┘
                  └──────────────────┬──────────────────┘
                                     ▼
  ┌─────────────────────────────────────────────────────────────────────┐
  │ State 2: Pure / SpatialPin & `zerocopy::Ref<&[u8], T>` Parsing      │
  │ • Byte stability guaranteed; multi-pass validation, `FromBytes +    │
  │   Immutable` casts, and `SpatialCodec` reabsorption are sound.      │
  └─────────────────────────────────────────────────────────────────────┘
```

**Cross-Layer Stale-TLB Trap in Rule B:** Unmapping a zero-copy loaned page from `senderDom`'s page tables (`senderUnmapped = true`) without completing synchronous cross-hart TLB shootdown (`tlbShootdownDone = true`) and IOMMU/DMA quiescence (`dmaEngineQuiesced = true`) is **unsound**: a concurrent thread in `senderDom` can continue mutating the physical frame through a stale writable TLB entry while `receiverDom` holds `&[u8]`.

### 5. Kernel-Checked Lean 4 (`v4.34.1`) Mechanization and Counterexamples

`Basis: execution + derived`

The self-contained Lean 4 (`v4.34.1`) module below mechanizes `DemonicOracle`, generation monotonicity (`lookupGen_bumpGen_self`), single-fetch snapshot soundness (`copyDescriptorOnce_sound`), a constructive exploit witness against Pattern 1/2 double-fetch (`doubleFetch_overflow_witness`), zero-copy `LoanFrame` promotion soundness (`promoteLoanFrame_excludes_concurrent_mutation`), and the stale-TLB zero-copy bug witness (`unmapped_without_tlbShootdown_unsound`), using strictly `prelude` + `Init.*` with zero `sorry` and zero `Classical.choice`:

```lean
-- Verified on Lean 4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52)
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace SharedDmaSingleFetch

structure DemonicOracle where
  sample : Nat → Nat → Nat

def lookupGen : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (k, g) :: rest, addr =>
    match Nat.beq k addr with
    | true  => g
    | false => lookupGen rest addr

def bumpGen : List (Nat × Nat) → Nat → List (Nat × Nat)
  | [], addr => [(addr, 1)]
  | (k, g) :: rest, addr =>
    match Nat.beq k addr with
    | true  => (k, g + 1) :: rest
    | false => (k, g) :: bumpGen rest addr

theorem lookupGen_bumpGen_self (gens : List (Nat × Nat)) (addr : Nat) :
    lookupGen (bumpGen gens addr) addr = lookupGen gens addr + 1 := by
  induction gens with
  | nil =>
    unfold bumpGen lookupGen
    rw [Nat.beq_refl]
  | cons hd tl ih =>
    cases hd with
    | mk k g =>
      unfold bumpGen lookupGen
      cases hEq : Nat.beq k addr with
      | true  => dsimp; rw [hEq]
      | false => dsimp; rw [hEq]; exact ih

structure SharedRingState where
  oracle : DemonicOracle
  gens   : List (Nat × Nat)

def fetchWord (st : SharedRingState) (addr : Nat) : Nat × SharedRingState :=
  let g := lookupGen st.gens addr
  (st.oracle.sample addr g, { st with gens := bumpGen st.gens addr })

def fetchSliceOnce : Nat → Nat → SharedRingState → List Nat × SharedRingState
  | _, 0, st => ([], st)
  | baseAddr, n + 1, st =>
    let r1 := fetchWord st baseAddr
    let r2 := fetchSliceOnce (baseAddr + 1) n r1.2
    (r1.1 :: r2.1, r2.2)

theorem fetchSliceOnce_length :
    ∀ (baseAddr count : Nat) (st : SharedRingState),
      (fetchSliceOnce baseAddr count st).1.length = count
  | _, 0, _ => rfl
  | baseAddr, n + 1, st => by
    unfold fetchSliceOnce
    dsimp
    rw [fetchSliceOnce_length (baseAddr + 1) n (fetchWord st baseAddr).2]

structure PrivateSnapshot where
  checkedLen : Nat
  payload    : List Nat

def SnapshotBoundedValid (maxCap : Nat) (snap : PrivateSnapshot) : Prop :=
  snap.checkedLen ≤ maxCap ∧ snap.payload.length = snap.checkedLen

def copyDescriptorOnce (st : SharedRingState) (hdrAddr payloadBase maxCap : Nat) :
    Option (PrivateSnapshot × SharedRingState) :=
  let rHdr := fetchWord st hdrAddr
  match Nat.ble rHdr.1 maxCap with
  | true =>
    let rBuf := fetchSliceOnce payloadBase rHdr.1 rHdr.2
    some ({ checkedLen := rHdr.1, payload := rBuf.1 }, rBuf.2)
  | false =>
    none

theorem copyDescriptorOnce_sound (st st' : SharedRingState)
    (hdrAddr payloadBase maxCap : Nat) (snap : PrivateSnapshot)
    (hOk : copyDescriptorOnce st hdrAddr payloadBase maxCap = some (snap, st')) :
    SnapshotBoundedValid maxCap snap := by
  unfold copyDescriptorOnce at hOk
  dsimp at hOk
  cases hBle : Nat.ble (fetchWord st hdrAddr).1 maxCap with
  | false => rw [hBle] at hOk; cases hOk
  | true =>
    rw [hBle] at hOk
    dsimp at hOk
    injection hOk with hPair
    injection hPair with hSnap _
    rw [← hSnap]
    exact ⟨Nat.le_of_ble_eq_true hBle,
           fetchSliceOnce_length payloadBase (fetchWord st hdrAddr).1 (fetchWord st hdrAddr).2⟩

theorem privateSnapshot_immune_to_later_races
    (P : PrivateSnapshot → Prop) (snap : PrivateSnapshot)
    (_laterOracle : DemonicOracle) (hChecked : P snap) :
    P snap :=
  hChecked

def vulnerableDoubleFetch (st : SharedRingState) (hdrAddr payloadBase maxCap : Nat) :
    Option (List Nat × SharedRingState) :=
  let r1 := fetchWord st hdrAddr
  match Nat.ble r1.1 maxCap with
  | true =>
    let r2 := fetchWord r1.2 hdrAddr
    let rBuf := fetchSliceOnce payloadBase r2.1 r2.2
    some (rBuf.1, rBuf.2)
  | false =>
    none

def adversarialToctouOracle : DemonicOracle where
  sample addr gen :=
    match Nat.beq addr 0 with
    | true =>
      match Nat.beq gen 0 with
      | true  => 64
      | false => 512
    | false => 0

theorem doubleFetch_overflow_witness :
    Exists fun (buf : List Nat) =>
      Exists fun (st' : SharedRingState) =>
        vulnerableDoubleFetch { oracle := adversarialToctouOracle, gens := [] } 0 16 256 =
          some (buf, st') ∧
        Nat.lt 256 buf.length := by
  let initSt : SharedRingState := { oracle := adversarialToctouOracle, gens := [] }
  let afterTwo := (fetchWord (fetchWord initSt 0).2 0)
  let copied := fetchSliceOnce 16 afterTwo.1 afterTwo.2
  refine ⟨copied.1, copied.2, rfl, ?_⟩
  have hLen : copied.1.length = 512 := fetchSliceOnce_length 16 512 afterTwo.2
  rw [hLen]
  exact Nat.le_of_ble_eq_true rfl

structure FrameMappingState where
  senderDom          : Nat
  receiverDom        : Nat
  senderSingleThread : Bool
  senderUnmapped     : Bool
  tlbShootdownDone   : Bool
  dmaEngineQuiesced  : Bool

def canPromoteLoanFrame (m : FrameMappingState) : Bool :=
  m.dmaEngineQuiesced &&
    ((Nat.beq m.senderDom m.receiverDom && m.senderSingleThread) ||
     (m.senderUnmapped && m.tlbShootdownDone))

def externalWriterCanMutate (m : FrameMappingState) : Bool :=
  (!m.dmaEngineQuiesced) ||
    ((!m.senderUnmapped || !m.tlbShootdownDone) &&
     !(Nat.beq m.senderDom m.receiverDom && m.senderSingleThread))

theorem promoteLoanFrame_excludes_concurrent_mutation (m : FrameMappingState) :
    canPromoteLoanFrame m = true →
    externalWriterCanMutate m = false := by
  cases m with
  | mk sDom rDom sSingle sUnmap tlbDone dmaQuiet =>
    unfold canPromoteLoanFrame externalWriterCanMutate
    dsimp
    cases hEq : Nat.beq sDom rDom <;>
      cases sSingle <;> cases sUnmap <;> cases tlbDone <;> cases dmaQuiet <;>
      intro hGuard <;> first | rfl | cases hGuard

theorem unmapped_without_tlbShootdown_unsound :
    let m : FrameMappingState := {
      senderDom := 1, receiverDom := 2, senderSingleThread := false,
      senderUnmapped := true, tlbShootdownDone := false, dmaEngineQuiesced := true
    }
    canPromoteLoanFrame m = false ∧ externalWriterCanMutate m = true :=
  ⟨rfl, rfl⟩

end SharedDmaSingleFetch
```

When `hdrAddr` overlaps `[payloadBase .. payloadBase + rawLen)` (Pattern 2 overlapping header-payload copy), retaining `checkedLen := rHdr.1` from generation `0` rather than re-parsing length out of `rBuf.1` structurally prevents second-fetch header clobbering.

## Boundaries

- **`known not to apply` — Direct `&[u8]` / `zerocopy::Ref` over live shared rings even with single-read syntax:** Forming `&[u8]` or `zerocopy::Ref<&[u8], T>` (`T: FromBytes + Immutable`) over memory mapped writable in userspace or accessible to active DMA is **known not to apply** as a sound single-fetch defense, because Rust/LLVM `dereferenceable` and `readonly` attributes license compiler-synthesized reloads.
- **`known not to apply` — `VmReader` / `READ_ONCE` alone as proof of logical single-fetch:** `READ_ONCE` (`torvalds/linux`) and `VmReader::read_once` (`asterinas`) eliminate compiler data-race UB, but are **known not to apply** as sufficient guarantees against logical TOCTOU because `VmReader` implements `Clone` (`ostd/src/mm/io/mod.rs:319–325`) and permits repeated offset reads.
- **`known not to apply` — Unmapping sender PTEs without TLB and IOMMU shootdown for zero-copy loans:** Clearing a sender PTE without completing remote-hart TLB invalidation and DMA quiescence is **known not to apply** as a sound `LoanFrame` guard (`unmapped_without_tlbShootdown_unsound`).
- **`unsupported` — Raw volatile/foreign-copy intrinsics in `joshlf/anneal` `Trusted.MirSemantics` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:** `Trusted.MirSemantics` currently evaluates pure value-typed MIR locals and classifies raw volatile pointer reads and foreign `copy_from_user` calls as `FaultKind.unsupported`, requiring `SharedRingState` to be threaded explicitly at the specification/adapter boundary until intrinsic support is added.
- **`not examined` — Optimistic seqlocks and lock-free multi-consumer ring stealing:** Intentional multi-read retry protocols (e.g., Linux `read_seqbegin` / `read_seqretry` and `IORING_SETUP_SQPOLL` wakeup flags) were **not examined**; verifying seqlock convergence requires constraining the writer rely relation by even/odd sequence numbers rather than an unconstrained `DemonicOracle`.
- **`unknown` — Microarchitectural speculative prefetcher interactions with live DMA rings:** While Linux `io_uring` pairs `READ_ONCE` with `array_index_nospec` (`io_uring.c:1898, 2158`), whether software index masking suffices against transient cache-fill side channels under concurrent PCIe DMA writes across all out-of-order RISC-V/ARMv9 cores remains **unknown** from architectural ISA manuals alone.

## Evidence

| Subject / Artifact | Exact Coordinates | Role & Key Fact Verified |
| :--- | :--- | :--- |
| `torvalds/linux` | `65e4fd942f72a9dba0e4e257290c4fa1aa756854`, `io_uring/io_uring.c:5–28, 746–755, 1875–1900, 2063–2066, 2145–2202` | `source`: `smp_load_acquire` ring ordering, private `cached_sq_head`, single-fetch `READ_ONCE` + `array_index_nospec` into `struct io_kiocb`. |
| `torvalds/linux` | `65e4fd942f72a9dba0e4e257290c4fa1aa756854`, `rust/kernel/uaccess.rs:66–75, 259–291` | `normative + source`: `UserSlice` contract permitting userspace data races via `copy_from_user` while warning repeated reads may differ; non-`Clone` linear `UserSliceReader::read_raw`. |
| `asterinas/asterinas` | `7fecb4ffabc72d0767277a9ffb66168bc512034c`, `ostd/src/mm/io/mod.rs:208–218, 301–325, 457–473`; `dma_stream.rs:70–86, 201–215`; `dma_coherent.rs:29–34, 170–182` | `source`: Untyped `VmReader`, `PodOnce` `read_volatile()`, `Clone` on `VmReader` allowing logical double-fetches, and `DmaStream::sync_from_device`. |
| `google/zerocopy` | `ec133ce4d7993775413d852f91c9e3eb2a2a0897`, `zerocopy/src/lib.rs:1729–1736, 4358–4375` | `source`: `Immutable` (`no UnsafeCell`) and `FromBytes` reference byte-stability requirements. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/audit/TrustedBoundary.lean:469–483, 640–655`; `theory/Anneal/PureLift/SpatialPin.lean:16–58` | `source`: `prelude` + `Init.*` 3-axiom boundary and `SpatialPin` single-writer heaplet framing. |
| `AbsInt/CompCert` & `VST` | CompCert `2685140bf72c959446981fb99b5e44a8975021bc` (`common/Events.v:64–78, 698–715`); VST `d50ac1969f9f6586621895eb043ccf08a165f731` (`veric/juicy_extspec.v`) | `source`: `Event_vload` / `volatile_load_sem` trace non-determinism and `external_specification` world state. |
| `mit-pdos/perennial` & `iris-lean` | Perennial `c44b7487179b2e88e9f4dd8b0155c893406571ef` (`Perennial/GooseLang/Lang.lean:10–25, 211–229`, `Slice.lean`) & Rocq `c3b7ecff27c1a6e8ed058d5aca362df1e2f63311`; `iris-lean` `5540ef0110fc8f6d8e495c10c2f238c3ede14f3b`; DOI `10.1145/3341301.3359632` | `source + documentation`: Concurrent/crash separation logic over `iris-lean` (`state × GlobalState`, classical syntax equality). |
| Wang et al. & Xu et al. | USENIX Security 2017 (ISBN `978-1-931971-40-9`, pp. 1–16); IEEE S&P 2018 (DOI `10.1109/SP.2018.00017`) | `documentation`: Empirical 3-scenario kernel double-fetch taxonomy and **Deadline** multi-read symbolic analysis. |
| `leanprover/lean4` (`v4.34.1`) Probe | Commit `5045d0056413266e57c625dcd7c365b10e377c52` (`x86_64-unknown-linux-gnu`), `2026-11-20` | `execution`: `lean -DElab.async=false -Ddebug.skipKernelTC=false -M2048` checked all theorems (`exit 0`, `< 0.8s`); `copyDescriptorOnce_sound`, `doubleFetch_overflow_witness`, `promoteLoanFrame_excludes_concurrent_mutation`, and `unmapped_without_tlbShootdown_unsound` use **zero axioms**, and `lookupGen_bumpGen_self` uses only `[propext]`. |

## Revalidation

1. **Re-run the Standalone Lean 4 Kernel Probe (`< 1s`):** Save the Lean 4 code from **Findings §5** to `/tmp/reval_toctou.lean`, append `#print axioms` for `SharedDmaSingleFetch.copyDescriptorOnce_sound`, `SharedDmaSingleFetch.doubleFetch_overflow_witness`, `SharedDmaSingleFetch.promoteLoanFrame_excludes_concurrent_mutation`, and `SharedDmaSingleFetch.unmapped_without_tlbShootdown_unsound`, and run:
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false -M2048 /tmp/reval_toctou.lean
   ```
   Verify exit code `0`, zero `sorryAx`, and zero `Classical.choice`.
2. **Diff Upstream Rust Untrusted-Memory Wrappers (`torvalds/linux` & `asterinas/asterinas`):** Check `rust/kernel/uaccess.rs` (`UserSliceReader`) in `torvalds/linux` and `ostd/src/mm/io/mod.rs` (`impl Clone for VmReader`, `read_once`) in `asterinas/asterinas` to see whether linear single-fetch tracking or `Clone` restrictions change.
3. **Check `Anneal` MIR Intrinsic Coverage (`joshlf/anneal`):** Inspect `trusted/lean/Trusted/MirSemantics.lean` and `theory/Anneal/PureLift/SpatialPin.lean` for volatile/copy-in intrinsics that can bind directly to `SharedRingState.fetchWord`.
