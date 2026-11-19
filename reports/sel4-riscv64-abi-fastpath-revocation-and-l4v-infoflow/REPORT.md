# seL4 on RISC-V 64: user ABI, IPC fastpath guards, revocation side effects, and the l4v access-control and information-flow model

## Summary

This report examines upstream `seL4/seL4` and its proof repository `seL4/l4v`
at two pinned commits across four areas central to RISC-V 64 capability-kernel
design and verification: the user-visible ABI, the exact conditions under which
the IPC fastpath is a sound shortcut, the kernel and hardware state that
capability deletion must clean up eagerly, and the state partitioning and
channel restrictions behind the l4v integrity and noninterference proofs.

Key findings:

1. **The ABI is five generated tables, not the capability representation.**
   On RV64 a system call is `ecall` with the syscall number in `a7`
   (`-1 … -8` in the non-MCS API), the capability pointer in `a0`, the
   message-info word in `a1`, and message registers `a2 … a5`. The
   message-info word packs `label[63:12] | capsUnwrapped[11:9] |
   extraCaps[8:7] | length[6:0]`. Invocation labels, object-type numbers
   and syscall numbers are *positional enumerations generated from XML and
   headers*, so they differ between kernel configurations and revisions.
   The two-word `cap_t` layout is kernel-internal and can be replaced
   freely.
2. **Capability-pointer resolution has two acceptance rules.** Syscall
   lookups resolve 64 bits and accept a slot reached early (a non-CNode
   capability with bits left over); CNode invocations take an explicit depth
   and reject leftover bits. The fastpath lookup must agree with the first
   rule.
3. **The fastpath has nine `Call` guards and nine `ReplyRecv` guards on
   non-MCS RV64**, including a same-domain check and a priority check that
   mirrors the scheduler. l4v proves the fastpath equal to the slowpath
   only on ARM, ARM_HYP and AARCH64, and only under entry invariants that
   include `ksSchedulerAction = ResumeCurrentThread` and, for `Call`,
   `ksDomainTime ≠ 0`. **On RISCV64 the verified configuration enables the
   fastpath but the C refinement theorem is stated for `fp = False`**; the
   RISCV64 fastpath is unverified.
4. **seL4 never relies on lazy invalidation for state that hardware or the
   scheduler can still reach.** Deleting a capability eagerly unmaps the
   PTE and flushes the TLB, removes the ASID-table entry and re-evaluates
   the running address space, dequeues the thread from endpoint,
   notification and run queues, forces a reschedule if the thread is
   current, and removes the IRQ-to-notification binding. Lazy validation
   appears only on the *capability side* (stale mapping fields in a frame
   capability are compared against the live PTE before use), after the
   hardware side was already cleared.
5. **On RISC-V, seL4 flushes the whole TLB on every address-space switch**
   (`setVSpaceRoot` writes `satp` and then executes a global
   `sfence.vma`), including in the fastpath. Several correctness arguments
   (ASID-pool deletion without per-ASID flush, ASID reuse) lean on that
   flush, and l4v models neither the TLB nor the flush.
6. **l4v's information-flow theorem is nonleakage, proved for a
   restricted system shape**: each partition is a scheduler domain, the
   domain schedule is static, no partition holds interrupt-control,
   interrupt-handler or domain capabilities, the only enabled interrupt is
   the timer, capabilities are never transferred between partitions, and
   the machine model has no TLB, cache or timing.

Section map:

| Topic | Section |
| --- | --- |
| RV64 user ABI, invocation wire format, and compatibility seam | [1](#1-user-abi-on-rv64) |
| `fastpath_call` / `fastpath_reply_recv` guards and proof coverage | [2](#2-ipc-fastpath-exact-guards-and-what-is-proved) |
| Deletion, revocation, self-destruction, and eager hardware cleanup | [3](#3-deletion-revocation-and-state-that-must-be-cleaned-eagerly) |
| l4v access control and information-flow model | [4](#4-l4v-access-control-and-information-flow) |

## Applicability

Subjects examined (both are the tips of `master` on the observation date):

| Subject | Repository | Commit | Role |
| --- | --- | --- | --- |
| seL4 kernel and `libsel4` | `seL4/seL4` | `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7` (`VERSION` = `17.0.0-dev`) | implementation examined |
| l4v specifications and proofs | `seL4/l4v` | `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e` | proofs about that implementation |

The two commits were not checked against `seL4/verification-manifest` for
being a proved pair; l4v `master` tracks seL4 `master`, but the pairing is
an assumption here.

Scope of the kernel-side findings:

- Architecture `riscv64`, three page-table levels (Sv39). The bitfield
  declaration for RV64 is `base 64(39,1)`: 39 significant pointer bits,
  sign-extended. Other page-table depths are rejected at build time
  (`seL4:include/arch/riscv/arch/64/mode/object/structures.bf:L10-L15`).
- The **non-MCS** API (`CONFIG_KERNEL_MCS` unset), single core, no FPU.
  This matches the verified RISCV64 configuration, which sets
  `KernelFastpath ON`, `KernelNumDomains 16`, `KernelMaxNumNodes "1"`,
  `KernelPTLevels "3"` and both FPU extensions off
  (`seL4:configs/include/RISCV64_verified_include.cmake:L11-L29`). Where
  MCS changes an answer the text says so; MCS behaviour was otherwise not
  examined.
- Numbering tables assume no debug, benchmark or hardware-debug options.

Findings about l4v apply to the theories as written at the pinned commit.
No Isabelle session was built or checked; statements about what is proved
are statements about theorem text and about which theories exist.

The findings are stated for seL4. Sentences beginning "A new kernel …"
are derived consequences for a clean-slate RV64 capability kernel that
keeps seL4's user ABI but replaces its internals; they are not findings
about seL4.

## Findings

Evidence roles follow each citation or paragraph: **source** (read in the
pinned tree), **execution** (output of a preserved script over the pinned
tree), **documentation**, **derived** (inference, with the reasoning
given). Citations have the form `repo:path:Lstart-Lend` and are
machine-checked (see [Revalidation](#revalidation)).

### 1. User ABI on RV64

#### 1.1 System-call numbers

Syscall numbers are not written in any header. The generator assigns `-1,
-2, …` in document order of `libsel4/include/api/syscall.xml`, API block
first and debug block after it, with one running counter
(`seL4:libsel4/tools/syscall_header_gen.py:L194-L201`, **source**). The API
block is `api-master` for non-MCS and `api-mcs` for MCS
(`seL4:libsel4/include/api/syscall.xml:L11-L37`, **source**).

| Syscall | non-MCS | MCS |
| --- | --- | --- |
| `Call` | -1 | -1 |
| `ReplyRecv` | -2 | -2 |
| `Send` | -3 | -5 |
| `NBSend` | -4 | -6 |
| `Recv` | -5 | -7 |
| `Reply` | -6 | (none) |
| `Yield` | -7 | -11 |
| `NBRecv` | -8 | -8 |
| `NBSendRecv`, `NBSendWait`, `Wait`, `NBWait` | (none) | -3, -4, -9, -10 |

Basis: **execution** of `support/abi_numbers.py` over the pinned tree, which
re-implements the numbering rule; **source** for the rule.

Consequences that are easy to miss:

- `Call` and `ReplyRecv` are deliberately first, so the trap stub can test
  for them with two compares before any C code runs
  (`seL4:src/arch/riscv/traps.S:L114-L134`, **source**). Every other number
  differs between the two APIs. A kernel must pick one API flavour; the
  non-MCS numbers are the ones the verified RISCV64 configuration uses.
- `SYSCALL_MIN` is minus the number of API syscalls
  (`seL4:libsel4/tools/syscall_header_gen.py:L216-L219`), so `-8` for
  non-MCS. The slowpath treats anything outside `[SYSCALL_MIN, -1]` as an
  unknown syscall (`seL4:src/arch/riscv/c_traps.c:L144-L163`, **source**).
- Debug and benchmark syscalls occupy fixed numbers `-9 … -30` whether or
  not they are compiled in, because the kernel enum is generated from
  `api + debug` with explicit values
  (`seL4:libsel4/tools/syscall_header_gen.py:L216-L219`, **source**;
  listing by **execution**). With those options off, such a number reaches
  `handleUnknownSyscall`, which raises an `UnknownSyscall` fault to the
  thread's fault handler (`seL4:src/api/syscall.c:L260-L261`, **source**).

#### 1.2 Register convention and trap entry

| Register | On entry | On return from a receive |
| --- | --- | --- |
| `a7` | syscall number | unchanged |
| `a0` | capability pointer (`capRegister`) | badge (`badgeRegister`) |
| `a1` | message-info word (`msgInfoRegister`) | message-info word |
| `a2 … a5` | message registers 0 … 3 | message registers 0 … 3 |
| `a6` | MCS only: reply capability pointer | — |
| `t0` | MCS only: destination for `NBSendRecv` | — |

Basis: the `libsel4` stubs bind `a0`, `a1`, `a2 … a5`, `a7` by name
(`seL4:libsel4/arch_include/riscv/sel4/arch/syscalls.h:L25-L45`,
`seL4:libsel4/arch_include/riscv/sel4/arch/syscalls.h:L84-L112`), and the
kernel's register enumeration gives `a0` the names `capRegister` and
`badgeRegister`, `a1` the name `msgInfoRegister`, and lists the message
registers as `a2, a3, a4, a5`
(`seL4:include/arch/riscv/arch/machine/registerset.h:L18-L73`,
`seL4:src/arch/riscv/machine/registerset.c:L11-L17`). **source**.

Message words beyond the fourth live in the IPC buffer. `n_msgRegisters`
is 4 and the fastpath has a compile-time assertion that it is exactly 4
(`seL4:include/arch/riscv/arch/machine/registerset.h:L77-L82`,
`seL4:include/arch/riscv/arch/fastpath/fastpath.h:L85-L95`). **source**.

The IPC buffer is a 128-word (1024-byte) structure aligned to its own
size: `tag` (1 word), `msg[120]`, `userData`, `caps_or_badges[3]`,
`receiveCNode`, `receiveIndex`, `receiveDepth`
(`seL4:libsel4/include/sel4/shared_types.h:L11-L19`,
`seL4:libsel4/include/sel4/constants.h:L52-L58`). **source**; the word
count is **derived** by adding the field sizes.

Trap entry facts that bear on a verified trap path
(`seL4:src/arch/riscv/traps.S:L24-L134`, **source**):

- The stub swaps `t0` with `sscratch` to find the current thread's
  register save area, so `sscratch` must hold that pointer whenever user
  code runs; both exit paths write it back.
- All 31 general-purpose registers, `sstatus`, `scause` and `sepc` are
  saved before any dispatch. A syscall is recognised by `scause == 8`, and
  the saved next-PC is `sepc + 4`.
- The saved context has exactly 35 slots; a comment notes that other
  user-visible CSRs are omitted and may need to be saved to prevent
  covert channels
  (`seL4:include/arch/riscv/arch/machine/registerset.h:L64-L73`).
- The slowpath exit clears the LR/SC reservation with a dummy `sc.w`
  (`seL4:src/arch/riscv/c_traps.c:L45-L48`). The fastpath exit,
  `fastpath_restore`, does not: a search of `include/arch/riscv` and
  `src/arch/riscv` for `sc.w` finds only the slowpath line
  (`seL4:include/arch/riscv/arch/fastpath/fastpath.h:L116-L190`,
  **source** for the function, **execution** for the search). A reservation
  made by one thread therefore survives a fastpath switch to another
  thread. Whether a given hart lets the second thread's `sc` succeed is
  implementation-defined; this was not tested.

#### 1.3 Message-info, rights and guard words

The bitfield generator allocates fields from the most significant end of a
block in declaration order: it starts with `offset` equal to the block
size and subtracts each field's size
(`seL4:tools/bitfield_gen.py:L2450-L2476`, **source**). For multi-word
blocks the first 64 declared bits are therefore `words[N-1]` and the last
are `words[0]`.

| Word | Layout (bit ranges) | Declared at |
| --- | --- | --- |
| `seL4_MessageInfo` | `label[63:12]`, `capsUnwrapped[11:9]`, `extraCaps[8:7]`, `length[6:0]` | `seL4:libsel4/mode_include/64/sel4/shared_types.bf:L11-L16` |
| `seL4_CapRights` | `GrantReply[3]`, `Grant[2]`, `Read[1]`, `Write[0]` | `seL4:libsel4/mode_include/64/sel4/shared_types.bf:L18-L26` |
| `seL4_CNode_CapData` | `guard[63:6]`, `guardSize[5:0]` | `seL4:libsel4/mode_include/64/sel4/shared_types.bf:L28-L32` |

Basis: **execution** of `support/bf_layout.py` (a re-implementation of the
layout rule) plus two independent **source** cross-checks: the fastpath
tests the low `7 + 2` bits of the raw word to check length and extra caps
together (`seL4:include/arch/riscv/arch/fastpath/fastpath.h:L85-L95`), and
hand-written fastpath setters assemble `words[0]` and `words[1]` of
capabilities, endpoints and MDB nodes at exactly the computed positions
(`seL4:include/fastpath/fastpath.h:L123-L146`,
`seL4:include/arch/riscv/arch/fastpath/fastpath.h:L57-L67`).

Limits: `length ≤ 120`, at most 3 extra capabilities
(`seL4:libsel4/include/sel4/constants.h:L52-L58`). The slowpath clamps an
oversized `length` to 120 rather than rejecting it
(`seL4:include/api/types.h:L83-L96`), and truncates to 4 when the thread
has no IPC buffer (`seL4:src/api/syscall.c:L345-L354`). **source**.

`capsUnwrapped` is output-only: bit *i* is set when extra capability *i*
was an endpoint capability for the very endpoint the message travelled
over, in which case the receiver gets that capability's badge instead of
the capability. Otherwise at most one capability is copied into the
receiver's single receive slot
(`seL4:src/kernel/thread.c:L245-L298`, **source**).

#### 1.4 Invocation dispatch

Every system call that names a capability goes through one path
(`seL4:src/api/syscall.c:L302-L386`, **source**):

1. Resolve `a0` in the caller's CSpace at depth 64. On failure raise a
   capability fault, delivered to the fault handler **only for blocking
   calls**; a failed `NBSend` is silent.
2. Resolve up to three extra capability pointers from the IPC buffer.
3. Dispatch on the capability's type with `(label, length)`
   (`seL4:src/object/objecttype.c:L630-L783`, **source**).
4. On a syscall error, write an error reply **only if the syscall was
   `Call`**; `Send` to an object that fails decoding is silent. The error
   reply carries the error code in `label`
   (`seL4:src/object/endpoint.c:L299-L318`); error codes are
   `seL4_NoError = 0` … `seL4_NotEnoughMemory = 10`
   (`seL4:libsel4/include/sel4/errors.h:L9-L27`). **source**.
5. The invoking thread is put in `Restart` before any operation that can
   be preempted; if it is still `Restart` afterwards the kernel writes the
   success reply and makes it `Running`. A preempted operation instead
   leaves the thread in `Restart` so the syscall re-executes.

Dispatch by capability type: endpoint capabilities send the message (the
kernel does not interpret `label`); notification capabilities signal;
reply capabilities reply; null and zombie capabilities are an error; all
other types decode `label` as an operation selector
(`seL4:src/object/objecttype.c:L630-L783`, **source**).

Labels are a C enumeration generated in three layers: generic methods
from `object-api.xml` starting after `InvalidInvocation = 0`, then
`sel4_arch` methods continuing from `nInvocationLabels`, then `arch`
methods continuing from `nSeL4ArchInvocationLabels`
(`seL4:libsel4/tools/invocation_header_gen.py:L36-L117`, **source**). The
values are implicit, so a method excluded by its `<condition>` shifts all
later labels. For non-MCS RV64 at the pinned commit (**execution** of
`support/abi_numbers.py`):

| Label | Method | Label | Method |
| --- | --- | --- | --- |
| 1 | `UntypedRetype` | 21 | `CNodeMint` |
| 2 | `TCBReadRegisters` | 22 | `CNodeMove` |
| 3 | `TCBWriteRegisters` | 23 | `CNodeMutate` |
| 4 | `TCBCopyRegisters` | 24 | `CNodeRotate` |
| 5 | `TCBConfigure` | 25 | `CNodeSaveCaller` |
| 6 | `TCBSetPriority` | 26 | `IRQIssueIRQHandler` |
| 7 | `TCBSetMCPriority` | 27 | `IRQAckIRQ` |
| 8 | `TCBSetSchedParams` | 28 | `IRQSetIRQHandler` |
| 9 | `TCBSetIPCBuffer` | 29 | `IRQClearIRQHandler` |
| 10 | `TCBSetSpace` | 30 | `DomainSetSet` |
| 11 | `TCBSuspend` | 31 | `DomainScheduleConfigure` |
| 12 | `TCBResume` | 32 | `DomainScheduleSetStart` |
| 13 | `TCBBindNotification` | 33 | `RISCVPageTableMap` |
| 14 | `TCBUnbindNotification` | 34 | `RISCVPageTableUnmap` |
| 15 | `TCBSetTLSBase` | 35 | `RISCVPageMap` |
| 16 | `TCBSetFlags` | 36 | `RISCVPageUnmap` |
| 17 | `CNodeRevoke` | 37 | `RISCVPageGetAddress` |
| 18 | `CNodeDelete` | 38 | `RISCVASIDControlMakePool` |
| 19 | `CNodeCancelBadgedSends` | 39 | `RISCVASIDPoolAssign` |
| 20 | `CNodeCopy` | 40 | `RISCVIRQIssueIRQHandlerTrigger` |

`nInvocationLabels = nSeL4ArchInvocationLabels = 33` (the riscv64
`sel4_arch` layer is empty) and `nArchInvocationLabels = 41`. With MCS the
generic count is 39 and the arch labels start at 39.

Two properties matter for compatibility:

- **Label order is semantically load-bearing.** The CNode decoder selects
  operations by range comparison on the label
  (`seL4:src/object/cnode.c:L53-L57`, `seL4:src/object/cnode.c:L74-L74`),
  so the XML order cannot be permuted. **source**.
- **Labels are not stable across revisions.** The pinned tree contains
  `TCBSetFlags` and two domain-schedule methods; each insertion renumbers
  everything after it. Compatibility with `libsel4` therefore means
  agreement with the headers generated from the same XML rather than
  hard-coding a fixed integer table. **derived** from the generation rule.

Object-type numbers passed to `Untyped_Retype` are built the same way:
generic types, then mode types, then arch types
(`seL4:libsel4/include/sel4/objecttype.h:L8-L19`,
`seL4:libsel4/sel4_arch_include/riscv64/sel4/sel4_arch/objecttype.h:L12-L18`,
`seL4:libsel4/arch_include/riscv/sel4/arch/objecttype.h:L12-L17`,
**source**). For non-MCS Sv39: `Untyped = 0`, `TCB = 1`, `Endpoint = 2`,
`Notification = 3`, `CapTable = 4`, `RISCV_Giga_Page = 5`, `RISCV_4K_Page
= 6`, `RISCV_Mega_Page = 7`, `RISCV_PageTableObject = 8`,
`seL4_ObjectTypeCount = 9` (**derived** by counting the enumerators). There
is no separate address-space-root object: a page table at any level is a
`PageTableObject`, and ASID pools are made by an `ASIDControl` invocation,
not by `Retype`.

#### 1.5 Capability-pointer resolution

`resolveAddressBits(nodeCap, capptr, n_bits)`
(`seL4:src/kernel/cspace.c:L126-L193`, **source**) consumes `capptr` from
its most significant *remaining* bit downwards:

```text
fail InvalidRoot unless nodeCap is a CNode capability
loop:
  radix, guardSize, guard := fields of nodeCap;  level := radix + guardSize
  (kernel assertion: level != 0)
  g := (capptr >> ((n_bits - guardSize) & 63)) & mask(guardSize)
  fail GuardMismatch  if guardSize > n_bits or g != guard
  fail DepthMismatch  if level > n_bits
  slot := cnode[(capptr >> (n_bits - level)) & mask(radix)]
  if n_bits == level: return (slot, bitsRemaining = 0)
  n_bits := n_bits - level;  nodeCap := slot.cap
  if nodeCap is not a CNode capability: return (slot, bitsRemaining = n_bits)
```

Edge cases:

- **Two acceptance rules.** `lookupSlot`, used for the invoked capability,
  the receive capability and extra capabilities, calls the resolver with
  `n_bits = 64` and ignores `bitsRemaining`
  (`seL4:src/kernel/cspace.c:L51-L63`). `lookupSlotForCNodeOp`, used for
  CNode invocation arguments, takes a user depth in `[1, 64]` and fails
  with `DepthMismatch` when `bitsRemaining != 0`
  (`seL4:src/kernel/cspace.c:L65-L109`). **source**. The same pointer value
  can therefore name a slot in a syscall and fail in a CNode operation.
- **The `& 63` on the guard shift** exists only to avoid a 64-bit shift
  when `n_bits = 64` and `guardSize = 0`; the masked result is then
  discarded by `mask(0)`.
- **Termination and the `level != 0` assertion** depend on every CNode
  capability resolving at least one bit. `updateCapData` enforces only
  `guardSize + radix ≤ 64` (`seL4:src/object/objecttype.c:L416-L434`), so
  the lower bound comes from radix ≥ 1 at creation. **source** for the
  check; **derived** for where the lower bound comes from (the creation
  check was not located in the examined code).
- **Fastpath lookup.** `lookup_fp` shifts the pointer left as bits are
  consumed, skips the guard comparison when `guardSize = 0`, stops at the
  first non-CNode capability or when 64 bits are consumed, and returns a
  null capability if it overshoots 64 bits
  (`seL4:include/fastpath/fastpath.h:L64-L108`, **source**). It returns the
  same capability as `lookupSlot` whenever it returns a non-null one, and
  null in every case where the slowpath would fault. **derived** by
  comparing the two loops; this equivalence is what the fastpath proofs
  establish on the architectures that have them.

#### 1.6 Capability representation (kernel-internal)

A capability is two 64-bit words. The 5-bit type tag is `words[0][63:59]`
for every type; odd tags are architecture capabilities
(`seL4:include/object/structures.h:L430-L434`). Tags
(`seL4:include/arch/riscv/arch/64/mode/object/structures.bf:L66-L90`,
**source**): `null 0`, `untyped 2`, `endpoint 4`, `notification 6`,
`reply 8`, `cnode 10`, `thread 12`, `irq_control 14`, `irq_handler 16`,
`zombie 18`, `domain 20`, `frame 1`, `page_table 3`, `asid_control 11`,
`asid_pool 13` (MCS adds `sched_context 22`, `sched_control 24`).

Fields other than the tag (**execution** of `support/bf_layout.py`;
declarations at `seL4:include/object/structures_64.bf:L7-L120` and
`seL4:include/arch/riscv/arch/64/mode/object/structures.bf:L22-L64`).
"ptr" means a 39-bit sign-extended kernel pointer with the stated low bits
implied zero:

| Capability | `words[1]` | `words[0]` below the tag |
| --- | --- | --- |
| `untyped` | `capFreeIndex[63:25]`, `capIsDevice[6]`, `capBlockSize[5:0]` | `capPtr[38:0]` ptr |
| `endpoint` | `capEPBadge[63:0]` | `GrantReply[58]`, `Grant[57]`, `Receive[56]`, `Send[55]`, `capEPPtr[38:0]` ptr |
| `notification` | `capNtfnBadge[63:0]` | `Receive[58]`, `Send[57]`, `capNtfnPtr[38:0]` ptr |
| `reply` (non-MCS) | `capTCBPtr[63:0]` | `capReplyCanGrant[1]`, `capReplyMaster[0]` |
| `cnode` | `capCNodeGuard[63:0]` | `GuardSize[58:53]`, `Radix[52:47]`, `capCNodePtr[37:0]` ptr (bit 0 implied) |
| `thread` | — | `capTCBPtr[38:0]` ptr |
| `irq_handler` | `capIRQ[11:0]` | — |
| `zombie` | `capZombieID[63:0]` | `capZombieType[6:0]` |
| `frame` | `capFMappedASID[63:48]`, `capFBasePtr[47:9]` ptr | `capFSize[58:57]`, `capFVMRights[56:55]`, `capFIsDevice[54]`, `capFMappedAddress[38:0]` |
| `page_table` | `capPTMappedASID[63:48]`, `capPTBasePtr[47:9]` ptr | `capPTIsMapped[39]`, `capPTMappedAddress[38:0]` |
| `asid_pool` | — | `capASIDBase[58:43]`, `capASIDPool[36:0]` ptr (bits 1:0 implied) |
| `null`, `irq_control`, `domain`, `asid_control` | — | — |

Semantics worth carrying into any redesign, independent of the encoding:

- Badges are a full 64 bits. A badge can be set only once: minting onto an
  already-badged endpoint or notification capability yields a null
  capability (`seL4:src/object/objecttype.c:L401-L414`, **source**).
- Rights are per capability type: four on endpoints (send, receive, grant,
  grant-reply), two on notifications, one on reply capabilities, VM rights
  on frames; `maskCapRights` leaves all other types unchanged
  (`seL4:src/object/objecttype.c:L441-L506`,
  `seL4:src/arch/riscv/object/objecttype.c:L58-L69`, **source**).
- **A frame capability records its own single mapping** (`ASID`, virtual
  address). Copying a frame capability clears those fields, so every
  mapping has exactly one capability that names it; a page-table
  capability can be copied only once it is mapped, and the copies share
  one mapping (`seL4:src/arch/riscv/object/objecttype.c:L22-L38`,
  **source**). This capability-side reverse map is what lets deletion find
  the PTE without a per-frame mapping list (section 3).
- A new thread inherits the creator's current scheduling domain
  (`seL4:src/object/objecttype.c:L524-L530`, **source**).

#### 1.7 Compatibility seam for new object classes

All **derived** from 1.1 – 1.6. A new kernel that wants unmodified
`libsel4` clients to keep working, and wants to add its own object classes
(for example verified loadable kernel modules, loanable frames for
zero-copy IPC, or asynchronous I/O rings), is constrained as follows:

1. **What must match:** syscall numbers and the trap register convention
   (1.1, 1.2); the message-info, rights and CNode-data words and the IPC
   buffer layout (1.3); the invocation path's observable rules — which
   failures fault, which reply, which are silent (1.4); the label and
   object-type enumerations *as generated from the same interface XML*
   (1.4); the resolution algorithm including both acceptance rules (1.5);
   badge, rights and derivation semantics (1.6).
2. **What need not match:** the two-word capability encoding, the MDB
   linked list, zombie capabilities, and the pointer casts behind them.
   None is observable except through debug syscalls.
3. **Do not add syscall numbers.** `-1 … -8` are taken, `-9 … -30` are
   reserved by upstream's debug list, and anything else is by contract an
   `UnknownSyscall` fault that user-level emulation layers may depend on.
   New kernel services fit the existing shape: a new capability type whose
   invocations are `(capability, label, message)`.
4. **Do not number extension labels or object types by continuing the
   upstream enumerations.** Upstream insertions renumber them (1.4), and
   inserting an extension file in the empty riscv64 `sel4_arch` layer
   would itself shift every architecture label by the number of extension
   methods. Extension labels and object types need a range upstream cannot
   reach — the label field is 52 bits wide and upstream uses fewer than 64
   values — declared in a separate interface file so the existing stub
   generator can still emit client stubs.
5. **Extension invocations inherit the generic rules** unless specified
   otherwise: errors are reported only to `Call`; arguments beyond four
   words require an IPC buffer and are silently truncated without one;
   capability arguments arrive as extra capabilities resolved with the
   syscall acceptance rule; long-running operations must fit the
   `Restart`-and-re-execute preemption protocol.
6. **Pin the API flavour.** Non-MCS and MCS differ in syscall numbers,
   labels, the reply mechanism and the TCB slot layout
   (`seL4:include/object/structures.h:L173-L202`). The verified RISCV64
   configuration and the proofs examined here are non-MCS.

### 2. IPC fastpath: exact guards and what is proved

#### 2.1 Where the fastpath sits

With `CONFIG_FASTPATH`, the trap stub jumps straight to
`c_handle_fastpath_call` when `a7` is the `Call` number and to
`c_handle_fastpath_reply_recv` when it is the `ReplyRecv` number; everything
else goes to the slowpath (`seL4:src/arch/riscv/traps.S:L114-L134`,
`seL4:src/arch/riscv/c_traps.c:L165-L203`, **source**). The fastpath
functions either commit and return to user mode themselves, or call
`slowpath(syscall)` before modifying any kernel state. `KernelFastpath`
defaults to on (`seL4:config.cmake:L177-L177`).

There is no RISC-V-specific fastpath source file and no RISC-V virtual-CPU
object at the pinned commit. The generic code is
`src/fastpath/fastpath.c`; the RISC-V parts are inline helpers in
`include/arch/riscv/arch/fastpath/fastpath.h`. **source** (directory
listing of the pinned tree).

#### 2.2 `fastpath_call` guards (non-MCS, single core, RV64)

Checks run in this order; any failure calls `slowpath(SysCall)`
(`seL4:src/fastpath/fastpath.c:L19-L245`, **source**). "current" is the
calling thread and "dest" the thread at the head of the endpoint queue.

| # | Guard (must hold to stay on the fastpath) | Lines |
| --- | --- | --- |
| C1 | `(msgInfo & 0x1ff) ≤ 4`: no extra capabilities and `length ≤ 4`, tested as one compare on the raw word | `seL4:src/fastpath/fastpath.c:L38-L43` |
| C2 | current has no pending fault (`tcbFault` is `NullFault`) | `seL4:src/fastpath/fastpath.c:L38-L43` |
| C3 | `a0` resolves (fastpath lookup) to an endpoint capability with the send right | `seL4:src/fastpath/fastpath.c:L45-L52` |
| C4 | the endpoint is in state `Recv` (a receiver is queued) | `seL4:src/fastpath/fastpath.c:L61-L64` |
| C5 | dest's VSpace-root slot holds a page-table capability that is mapped | `seL4:src/fastpath/fastpath.c:L73-L82` |
| C6 | the ASID recorded in that capability still resolves, through the ASID table, to that same root table | `seL4:src/fastpath/fastpath.c:L122-L130` |
| C7 | `dest.priority ≥ current.priority`, **or** dest's priority is at least the highest priority in the current domain's ready queues | `seL4:src/fastpath/fastpath.c:L132-L138` |
| C8 | the endpoint capability has the grant right or the grant-reply right (a reply capability will be created) | `seL4:src/fastpath/fastpath.c:L140-L145` |
| C9 | `dest.domain == ksCurDomain` (compiled away when there is one domain) | `seL4:src/fastpath/fastpath.c:L153-L156` |

MCS adds: dest has no scheduling context of its own, and dest's thread
state carries a reply object. SMP adds: both threads have the same
affinity. x86 adds a single-step check. **source**, not otherwise
examined.

Not checked, because the slowpath and the kernel invariants make them
unnecessary (**derived** from the code; the corresponding proof
obligations are in 2.5):

- that dest is `BlockedOnReceive` — implied by C4 and the endpoint queue
  invariant;
- `capsUnwrapped` bits in the incoming word — they are cleared on output
  (`seL4:src/fastpath/fastpath.c:L242-L244`);
- the IPC buffers of either thread — with `length ≤ 4` and no extra
  capabilities no buffer is touched;
- whether an interrupt is pending — it is taken after `sret`.

After the final guard (the commit boundary past which slowpath fallback is
no longer taken), the fastpath executes without any further failure path
(`seL4:src/fastpath/fastpath.c:L176-L245`, **source**): dequeue dest from
the endpoint and set the endpoint `Idle` if the queue becomes empty; set
current to `BlockedOnReply`; write a reply capability for current into
dest's caller slot, with `canGrant` taken from dest's blocked-receive
state, and link it under current's reply-master slot in the MDB; copy
`length` message registers; set dest `Running` without enqueueing it;
switch address space and `ksCurThread`; return to dest with `a0 = badge`
of the endpoint capability and `a1 =` the incoming message-info word with
`capsUnwrapped` cleared.

#### 2.3 `fastpath_reply_recv` guards (non-MCS, single core, RV64)

Failure calls `slowpath(SysReplyRecv)`
(`seL4:src/fastpath/fastpath.c:L254-L575`, **source**). "caller" is the
thread named by the reply capability in current's caller slot.

| # | Guard | Lines |
| --- | --- | --- |
| R1 | `(msgInfo & 0x1ff) ≤ 4` and current has no pending fault | `seL4:src/fastpath/fastpath.c:L276-L281` |
| R2 | `a0` resolves to an endpoint capability with the receive right | `seL4:src/fastpath/fastpath.c:L283-L291` |
| R3 | current has no bound notification that is `Active` (otherwise the receive must complete the signal instead of blocking) | `seL4:src/fastpath/fastpath.c:L303-L307` |
| R4 | the endpoint is **not** in state `Send` (no sender is waiting, so the receive will block) | `seL4:src/fastpath/fastpath.c:L312-L315` |
| R5 | current's caller slot holds a reply capability | `seL4:src/fastpath/fastpath.c:L331-L336` |
| R6 | caller has no pending fault (otherwise the reply is a fault reply) | `seL4:src/fastpath/fastpath.c:L349-L357` |
| R7 | caller's VSpace root is a mapped page-table capability whose ASID still resolves to it | `seL4:src/fastpath/fastpath.c:L364-L373`, `seL4:src/fastpath/fastpath.c:L414-L422` |
| R8 | caller's priority is at least the highest priority in the current domain's ready queues | `seL4:src/fastpath/fastpath.c:L424-L428` |
| R9 | `caller.domain == ksCurDomain` | `seL4:src/fastpath/fastpath.c:L437-L440` |

R5 checks only the capability type. The slowpath additionally treats a
reply *master* capability in the caller slot as an error; the fastpath
relies on the invariant that the caller slot never holds one
(`seL4:include/arch/riscv/arch/fastpath/fastpath.h:L110-L113`,
`seL4:src/api/syscall.c:L411-L444`, **source**; the l4v AARCH64 fastpath
specification records the same omission in a comment,
`l4v:proof/crefine/AARCH64/Fastpath_Defs.thy:L119-L125`).

After the guards (`seL4:src/fastpath/fastpath.c:L455-L575`, **source**):
current becomes `BlockedOnReceive` on the endpoint with `canGrant` from the
endpoint capability and is appended to the endpoint queue; the reply
capability is deleted by unlinking it from the MDB and nulling the slot;
`length` message registers are copied; caller becomes `Running`; the
address space and `ksCurThread` switch; caller resumes with `a0 = 0`
(replies carry no badge) and `a1 =` the message-info word with
`capsUnwrapped` cleared.

#### 2.4 Why these guards make the shortcut equal to the slowpath

**derived** by reading the slowpath alongside the guards; each item names
the slowpath behaviour a guard rules out.

- *Message shape (C1, R1).* With more than four words or any extra
  capability the slowpath reads and writes IPC buffers, may fault on them
  and may insert a capability into the receiver's CSpace.
- *Sender fault (C2, R1).* The slowpath transfer inspects the sender's
  saved fault and builds a fault message instead of copying registers
  whenever it is not null (`seL4:src/kernel/thread.c:L114-L128`,
  **source**), so the register copy is valid only for a null fault.
- *Endpoint state (C4, R4).* `Call` on an endpoint without a receiver
  blocks the sender; `Recv` on an endpoint with a sender completes a
  rendezvous instead of blocking.
- *Bound notification (R3).* The slowpath receive first consumes an active
  bound notification and does not touch the endpoint
  (`seL4:src/object/endpoint.c:L159-L163`, **source**).
- *Rights (C3, C8, R2).* Without grant or grant-reply the slowpath `Call`
  transfers the message but creates no reply capability and leaves the
  caller `Inactive` (`seL4:src/object/endpoint.c:L115-L126`, **source**).
- *Receiver fault (R6).* Replying to a faulted thread applies the reply to
  the thread's registers and may restart it.
- *Address space (C5, C6, R7).* The slowpath's `setVMRoot` falls back to
  the kernel's page table when the root capability is not a mapped page
  table or the ASID no longer resolves to it
  (`seL4:src/arch/riscv/kernel/vspace.c:L578-L602`); the fastpath's direct
  `satp` write would install a stale root.
- *Scheduling (C7, R8).* In the slowpath the woken thread becomes the
  scheduler's "switch-to" candidate and `schedule()` switches to it
  directly unless it is of lower priority than the current thread and not
  the highest ready priority, in which case it is enqueued and the
  scheduler chooses again (`seL4:src/kernel/thread.c:L372-L433`). C7 is
  that same test. R8 is stricter in form but equal in effect, because the
  current thread was running and is therefore of the highest ready
  priority. The scheduler comment explains that this check is structured
  to align with the fastpath and to avoid consulting the idle thread's
  priority so that information-flow isolation is preserved
  (`seL4:src/kernel/thread.c:L393-L399`, **source**).
- *Domain (C9, R9).* The slowpath's `possibleSwitchTo` only enqueues a
  thread of another domain and never switches to it
  (`seL4:src/kernel/thread.c:L557-L576`, **source**); the current thread
  then blocks and the scheduler picks another thread of the *current*
  domain or idles. Without C9/R9 the fastpath would run a thread of
  another domain inside the current domain's time slice. That is both a
  functional deviation and a break of the property the noninterference
  proof relies on, that only threads of `ksCurDomain` run.

Two further conditions are not checked in C because they are entry
invariants, but the equivalence proofs need them (2.5):

- the scheduler action is "resume current thread" on entry, so that the
  woken thread becomes the switch-to candidate rather than being enqueued
  behind an earlier candidate; and
- for `Call`, the domain time slice has not expired, because the slowpath
  scheduler would otherwise switch domains.

#### 2.5 What l4v proves, and on which architectures

`Fastpath_C.thy`, `Fastpath_Defs.thy` and `Fastpath_Equiv.thy` exist under
`proof/crefine/` for `ARM`, `ARM_HYP` and `AARCH64` only. `X64` and
`RISCV64` have none. **source** (directory listing of the pinned tree).

Where it exists the proof has two layers (AARCH64 cited; **source**):

- `Fastpath_Defs.thy` defines a specification-level function `fastpaths`
  that performs the guards of 2.2 and 2.3 on the kernel's executable
  specification state and falls back to `callKernel` on any failure
  (`l4v:proof/crefine/AARCH64/Fastpath_Defs.thy:L20-L176`). The guard list
  there is the authoritative statement of the conditions. It matches the
  tables above except for the architecture-specific address-space guard,
  where AARCH64 also requires a valid VMID (message shape and fault at
  `l4v:proof/crefine/AARCH64/Fastpath_Defs.thy:L27-L31`; priority, rights
  and domain at `l4v:proof/crefine/AARCH64/Fastpath_Defs.thy:L53-L61`). The
  specification also contains a nondeterministic `pickFastpath` choice:
  **declining the fastpath is always permitted**, so any implementation
  may bail out more often than the C code without invalidating the
  theorem.
- `Fastpath_Equiv.thy` proves that `callKernel` on the syscall event can
  be rewritten to `fastpaths`, under these preconditions:
  - `Call`: `invs'`, the current thread is `Running`, `ksSchedulerAction =
    ResumeCurrentThread`, `ksDomainTime ≠ 0`, `ready_qs_runnable`
    (`l4v:proof/crefine/AARCH64/Fastpath_Equiv.thy:L593-L599`);
  - `ReplyRecv`: `invs'`, the current thread is `Running`,
    `ksSchedulerAction = ResumeCurrentThread`, `cnode_caps_gsCNodes'`,
    `ready_qs_runnable`
    (`l4v:proof/crefine/AARCH64/Fastpath_Equiv.thy:L1499-L1503`).
- `Fastpath_C.thy` proves the C functions refine `fastpaths`
  (`l4v:proof/crefine/AARCH64/Fastpath_C.thy:L1824-L1833`,
  `l4v:proof/crefine/AARCH64/Fastpath_C.thy:L2709-L2718`).

For RISCV64 (**source**):

- `Refine_C.thy` opens with a note that `Fastpath_C` is left out
  (`l4v:proof/crefine/RISCV64/Refine_C.thy:L11-L14`) and keeps the lemma
  that would connect `callKernel` to the fastpath entry inside a comment
  (`l4v:proof/crefine/RISCV64/Refine_C.thy:L547-L552`).
- The entry-point correspondence and the top-level C refinement statement
  carry the hypothesis `fp = False`, each marked as a fastpath fix-me
  (`l4v:proof/crefine/RISCV64/Refine_C.thy:L633-L638`,
  `l4v:proof/crefine/RISCV64/Refine_C.thy:L907-L911`). `fp` selects
  between the kernel entry with and without the fastpath
  (`l4v:proof/crefine/RISCV64/ADT_C.thy:L159-L166`).
- Meanwhile the verified RISCV64 build configuration sets `KernelFastpath
  ON` (`seL4:configs/include/RISCV64_verified_include.cmake:L21-L21`).

So on RISCV64 the proved statement is about a kernel whose `Call` and
`ReplyRecv` always take the slowpath, while the shipped verified
configuration takes the fastpath. The tree does not say why the RISCV64
fastpath proof is absent beyond the fix-me notes; no architectural
obstacle is recorded. **source** for the facts; the absence of a stated
reason is an observation about the tree, not evidence that none exists.

Even where the fastpath is proved, the two assembly-level pieces are
assumptions of the proof, not theorems: `slowpath` is assumed to behave as
`callKernel`, and `fastpath_restore` is assumed to set the badge and
message-info registers and return to user mode
(`l4v:proof/crefine/RISCV64/Machine_C.thy:L90-L126`, **source**; the same
locale assumptions exist in the RISCV64 tree although unused there).

#### 2.6 RISC-V specifics of the fastpath that a redesign can improve

- **Global TLB flush on every switch.** `switchToThread_fp` calls
  `setVSpaceRoot`, which writes `satp` and then executes an unconditional
  `sfence.vma` with no address or ASID argument on a single core
  (`seL4:include/arch/riscv/arch/fastpath/fastpath.h:L40-L55`,
  `seL4:include/arch/riscv/arch/machine.h:L259-L273`,
  `seL4:include/arch/riscv/arch/machine.h:L139-L142`, **source**). The ASID
  written to `satp` therefore buys no TLB retention. This is the dominant
  avoidable cost on the RV64 IPC path and also the reason several unmap
  paths are correct without targeted flushes (3.4).
- **No reservation clear on the fastpath exit** (1.2).
- **Guard C6/R7 reads two levels of ASID table** in memory on every IPC
  (`seL4:include/arch/riscv/arch/fastpath/fastpath.h:L75-L83`); it exists
  because a root capability can outlive its ASID assignment (3.3).
- **Worst-case execution time.** The fastpath has no loops other than the
  capability lookup (bounded by 64 resolved bits) and the copy of at most
  four registers. **derived** from the code; no timing was measured.

### 3. Deletion, revocation, and state that must be cleaned eagerly

#### 3.1 The mechanism: finalisation on the last capability

seL4's rule is that every kernel or hardware reference to an object is
either a capability in a slot or something a *finaliser* removes when a
capability is deleted. Memory is reused only when no capability to it
remains. The moving parts (**source**):

- `cteDelete(slot)` runs `finaliseSlot`, which loops: compute `final` (no
  other capability in the derivation list names the same object), call
  `finaliseCap(cap, final)`, and stop when the remainder is removable
  (`seL4:src/object/cnode.c:L552-L565`,
  `seL4:src/object/cnode.c:L615-L662`,
  `seL4:src/object/cnode.c:L846-L874`).
- `cteRevoke(slot)` deletes derivation-list successors while they are
  descendants of `slot`, with a preemption point after each
  (`seL4:src/object/cnode.c:L528-L550`).
- `Untyped_Retype` restarts allocation from the base of the region, and
  zeroes the region first, only if the untyped capability has no
  descendants (`seL4:src/object/untyped.c:L171-L189`,
  `seL4:src/object/untyped.c:L234-L271`,
  `seL4:src/object/untyped.c:L273-L306`). Otherwise it allocates only from
  the never-used tail. Zeroing is done in chunks with a preemption point
  between chunks, and the capability's free index is lowered as each chunk
  is cleared so the operation can resume.

So reuse safety is: *revoke* (every descendant capability deleted, every
finaliser run) **then** *retype* (which checks there are no descendants).
The finalisers are where active state is torn down. **derived** from the
three functions above.

#### 3.2 Catalogue: side effects that happen at deletion time

Each row is something a lookup-time validity check cannot substitute for,
because the reference is followed by hardware or by kernel paths that do
not perform a capability lookup.

| Deleted capability | Condition | Eager side effect | Lines |
| --- | --- | --- | --- |
| Frame | **every** deletion of a capability with mapping fields set (not only the last) | walk the page table named by the recorded ASID and address; if the leaf PTE still points at this frame, clear it and `sfence.vma` | `seL4:src/arch/riscv/object/objecttype.c:L75-L84`, `seL4:src/arch/riscv/kernel/vspace.c:L555-L576` |
| Page table (not a root) | last capability, mapped | walk from the ASID's root to the parent entry, clear it, `sfence.vma` | `seL4:src/arch/riscv/object/objecttype.c:L85-L103`, `seL4:src/arch/riscv/kernel/vspace.c:L506-L546` |
| Page table (root of an address space) | last capability, mapped | flush the ASID, clear the ASID-pool entry, then **re-evaluate the current thread's address space** (`setVMRoot(ksCurThread)`), which installs the kernel-only page table if the current thread was using the deleted root | `seL4:src/arch/riscv/object/objecttype.c:L85-L103`, `seL4:src/arch/riscv/kernel/vspace.c:L494-L504` |
| ASID pool | last capability | clear the top-level ASID-table entry, re-evaluate the current thread's address space | `seL4:src/arch/riscv/object/objecttype.c:L104-L111`, `seL4:src/arch/riscv/kernel/vspace.c:L442-L451` |
| Thread (TCB) | last capability | unbind its notification; `suspend`: cancel IPC (below), dequeue from the run queue, set `Inactive`; release FPU ownership; then delete the five capabilities in the TCB's own slots through a zombie | `seL4:src/object/objecttype.c:L183-L216`, `seL4:src/kernel/thread.c:L72-L89`, `seL4:src/arch/riscv/object/objecttype.c:L304-L309` |
| — the thread is blocked on an endpoint | (inside `suspend`) | unlink from the endpoint queue; endpoint becomes `Idle` if the queue empties | `seL4:src/object/endpoint.c:L327-L401` |
| — the thread is blocked on a notification | (inside `suspend`) | unlink from the notification queue | `seL4:src/object/endpoint.c:L327-L401` |
| — the thread is blocked on a reply | (inside `suspend`) | delete the reply capability held by the server, found through the derivation link under the thread's reply-master slot | `seL4:src/object/endpoint.c:L327-L401` |
| — the thread is `ksCurThread` | (inside `suspend`) | the state change sets the scheduler action to "choose new thread", so the kernel does not return to it | `seL4:src/kernel/thread.c:L578-L592` |
| Endpoint | last capability | every queued thread is unlinked, set to `Restart` and enqueued; reschedule | `seL4:src/object/objecttype.c:L113-L120`, `seL4:src/object/endpoint.c:L437-L473` |
| Notification | last capability | unbind the bound thread (both directions), restart all waiters | `seL4:src/object/objecttype.c:L122-L133`, `seL4:src/object/notification.c:L270-L298`, `seL4:src/object/notification.c:L354-L368` |
| IRQ handler | last capability | delete the notification capability stored in the kernel's per-IRQ slot, then mark the IRQ inactive | `seL4:src/object/objecttype.c:L243-L253`, `seL4:src/object/interrupt.c:L186-L198`, `seL4:include/object/objecttype.h:L53-L61` |
| CNode | last capability | becomes a zombie; its slots are deleted one at a time (each running its own finaliser), preemptibly | `seL4:src/object/objecttype.c:L169-L181`, `seL4:src/object/cnode.c:L664-L724` |

All **source**. The four cases a purely lazy scheme is most likely to
miss, restated:

1. **Mapped frame or page table.** The PTE and the TLB entry are followed
   by the MMU, not by the kernel. If `Revoke` only bumped a generation and
   the memory were retyped, user mode would keep read/write access to
   memory that now holds another object. seL4 clears the PTE and flushes
   during deletion, before the untyped can pass the no-descendants check.
2. **Thread in a queue or currently running.** Endpoint, notification and
   run queues hold raw TCB pointers, and `ksCurThread` is a raw pointer.
   Deletion unlinks from all of them and forces a reschedule when the
   thread deletes or suspends itself. A thread *may* delete its own TCB
   capability or suspend itself: the invocation completes in the kernel on
   behalf of an `Inactive` thread, writes no reply (the reply is written
   only if the thread is still `Restart`,
   `seL4:src/api/syscall.c:L377-L383`), and the scheduler picks another
   thread at exit. By contrast reading or writing one's own registers
   through a TCB capability is refused outright
   (`seL4:src/object/tcb.c:L1028-L1033`,
   `seL4:src/object/tcb.c:L1070-L1075`).
3. **Address space active in `satp`.** Both ASID-level finalisers end by
   re-running the address-space selection for the current thread.
4. **IRQ bound to a notification.** The binding is not a pointer in
   interrupt state: it is a *copy of the notification capability* inserted
   into a kernel-owned slot, as a child in the derivation list
   (`seL4:src/object/interrupt.c:L167-L175`). Revoking the notification
   capability therefore deletes the binding by ordinary revocation, and
   interrupt delivery re-reads that slot each time
   (`seL4:src/object/interrupt.c:L215-L226`).

#### 3.3 Where seL4 *is* lazy, and why that is sound

Lazy validation is used only for bookkeeping stored in capabilities, and
only where the hardware-visible state was already removed eagerly
(**source** for each mechanism, **derived** for the characterisation):

- **Stale mapping fields in frame capabilities.** Unmapping or deleting a
  page table clears the parent PTE (and the unmap invocation zeroes the
  table, `seL4:src/arch/riscv/kernel/vspace.c:L1100-L1106`) but does not
  visit the frame capabilities that were mapped beneath it. Their recorded
  ASID and address go stale. When such a capability is later unmapped or
  deleted, `unmapPage` re-walks the tables and does nothing unless the
  leaf PTE still names that frame
  (`seL4:src/arch/riscv/kernel/vspace.c:L555-L576`).
- **Stale ASIDs in root capabilities.** Deleting an ASID pool does not
  visit the address-space roots registered in it. Every user of a root
  capability re-checks that the ASID still resolves to that root:
  `setVMRoot` (`seL4:src/arch/riscv/kernel/vspace.c:L578-L602`), the
  fastpath guards C6/R7, and the page-table finaliser.
- **IPC buffer.** The kernel reaches a thread's IPC buffer through the
  frame capability in the TCB's buffer slot on every access, never through
  a cached pointer (`seL4:src/arch/riscv/kernel/vspace.c:L358-L385`).

The asymmetry is the design rule: **hardware and queue state is cleaned
when authority is removed; capability-side hints may be stale and are
validated against that authoritative state before use.**

#### 3.4 Subtle points around deletion

- **Global TLB flush as a crutch.** Every RISC-V unmap path uses the
  no-argument `sfence.vma`, and so does every address-space switch
  (`seL4:include/arch/riscv/arch/machine.h:L259-L273`). ASID-pool deletion
  flushes nothing per ASID; it is the global flush inside the following
  `setVMRoot` that removes stale translations
  (`seL4:src/arch/riscv/kernel/vspace.c:L442-L451`). A kernel that keeps
  TLB entries across switches by using ASIDs must add an explicit flush of
  every ASID in a deleted pool, and of an ASID before it is reassigned.
  **derived**; l4v cannot confirm or refute it because the flush
  operations have no modelled effect (4.5).
- **Changing one's own address-space root.** In the non-MCS
  thread-control invocation the only reschedule for "target is the current
  thread" is in the IPC-buffer branch
  (`seL4:src/object/tcb.c:L1808-L1854`). Replacing the current thread's
  root capability without also setting the buffer therefore leaves `satp`
  on the old root until the next context switch. This is safe on one core
  because the old root cannot be finalised without `setVMRoot(ksCurThread)`
  running, but it is a window in which `satp` and the capability state
  disagree. **derived** from the code; not confirmed by execution.
- **Re-validation after a preemptible delete.** Thread-control deletes the
  old capability in a TCB slot (preemptible, and able to delete arbitrary
  other capabilities as a side effect) and only then installs the new one,
  after re-checking that the source slot still holds the same object and
  that the TCB capability is unchanged
  (`seL4:src/object/tcb.c:L1808-L1854`). Capability values captured during
  decoding are not trusted across a long-running delete. **source**.
- **Revoking a badge does not cancel sends already in flight.** A blocked
  sender carries its badge and rights in its thread state, not as a
  capability reference (`seL4:include/object/structures_64.bf:L319-L346`).
  Deleting a non-final badged endpoint capability does nothing to queued
  senders; a separate `CNode_CancelBadgedSends` walks the endpoint queue
  and restarts senders with that badge
  (`seL4:src/object/cnode.c:L325-L334`,
  `seL4:src/object/endpoint.c:L489-L540`). **source**.
- **The scheduler's switch-to candidate is a raw thread pointer.**
  `suspend` does not clear it. l4v's scheduler-validity lemma for
  `suspend` requires a `simple_sched_action` precondition (no pending
  switch-to candidate)
  (`l4v:proof/invariant-abstract/DetSchedSchedule_AI.thy:L1763-L1764`),
  and mass wake-ups in finalisers enqueue and request a full reschedule
  instead of nominating a candidate
  (`seL4:src/object/endpoint.c:L437-L473`). **source**; the connection
  between the two is **derived**.
- **Preemption during revocation is observable.** `preemptionPoint` counts
  work units and returns "preempted" only when the count reaches the
  configured threshold *and* an interrupt is pending
  (`seL4:src/model/preemption.c:L16-L40`). The counter is global and is
  reset on a domain switch (`seL4:src/kernel/thread.c:L326-L338`); see
  4.4 for why.
- **Self-revocation can be left incomplete.** If a revocation deletes the
  invoker's own TCB capability and is then preempted, the invoker is
  `Inactive` and never re-executes the syscall. **derived** from the
  restart protocol in 1.4; not confirmed by execution.

### 4. l4v access control and information flow

All statements in this section are about theory text at the pinned l4v
commit (**source** unless marked). Symbols are l4v's; each is defined
where first used.

#### 4.1 What exists and what the top-level statements are

- Access-control and information-flow proofs exist for `ARM`, `AARCH64`
  and `RISCV64` (architecture directories under `proof/access-control/`,
  `proof/infoflow/` and `proof/infoflow/refine/`); there are none for
  `X64` or `ARM_HYP`. **source** (directory listing).
- The header comment of `Noninterference.thy` clarifies that the
  top-level property proved is **nonleakage** rather than full
  noninterference (noting that full noninterference does not hold on the
  kernel despite the file's name), while a partial integrity result is
  proved separately (`l4v:proof/infoflow/Noninterference.thy:L16-L32`).
  The theorems are `nonleakage` and `xnonleakage`
  (`l4v:proof/infoflow/Noninterference.thy:L4179-L4190`).
- A C-level statement `xnonleakage_C` exists
  (`l4v:proof/infoflow/refine/Noninterference_Refinement.thy:L384-L414`),
  but the C automaton it is stated over ignores the fastpath flag: the
  constant `fp` is declared beside a note that `ADT_C_if` currently
  ignores it
  (`l4v:proof/infoflow/refine/Noninterference_Refinement.thy:L12-L16`).
  Together with 2.5, **no l4v statement about RISCV64 covers the IPC
  fastpath**, for refinement or for information flow. **derived** from the
  two notes.
- The C-level statement sits in a locale, `valid_initial_state_C`, that
  adds one assumption to the abstract locale and the C refinement locale:
  the C automaton can always step from a state related to a valid
  specification state
  (`l4v:proof/infoflow/refine/Noninterference_Refinement.thy:L190-L193`).
  Whether the tree instantiates that locale was not examined.
- Satisfiability of the abstract assumptions is shown by one worked
  example system, itself under assumptions about the user transition
  function
  (`l4v:proof/infoflow/RISCV64/Example_Valid_State.thy:L1890-L1900`).
- The RISCV64 instantiation treats FPU and hypervisor state as absent
  (`equiv_fpu` and `equiv_hyp` are `True`,
  `l4v:proof/infoflow/RISCV64/ArchInfoFlow.thy:L59-L71`), matching the
  verified configuration (FPU extensions off).

#### 4.2 Access control: policy, refinement of the policy, integrity

A policy (`PAS` record, `l4v:proof/access-control/Types.thy:L100-L109`)
labels every object, ASID and IRQ (`pasObjectAbs`, `pasASIDAbs`,
`pasIRQAbs`), gives a graph of labelled authority edges (`pasPolicy`),
names the label currently acting (`pasSubject`), maps each scheduler
domain to the labels that may run in it (`pasDomainAbs`), and carries
three switches (`pasMayActivate`, `pasMayEditReadyQueues`,
`pasMaySendIrqs`) that weaken integrity for scheduler steps. Authority
kinds are `Control`, `Receive`, `SyncSend`, `Notify`, `Reset`, `Grant`,
`Call`, `Reply`, `Write`, `Read`, `DeleteDerived`, plus architecture
authorities (`l4v:proof/access-control/Types.thy:L51-L52`); RISCV64 has
one, `ASIDPoolMapsASID`.

Capabilities map to authorities as follows
(`l4v:proof/access-control/Access.thy:L107-L132`,
`l4v:proof/access-control/RISCV64/ArchAccess.thy:L15-L25`):

| Capability | Authority conferred over the target's label |
| --- | --- |
| Untyped, CNode, Thread, Zombie, Domain, IRQControl, IRQHandler, page table, ASID pool, ASID control | `Control` |
| Endpoint | always `Reset`; `Receive` if readable; `SyncSend` if writable; **every authority** if it has the grant right; `Call` if grant-reply and writable |
| Notification | always `Reset`; `Receive` if readable; `Notify` if writable |
| Reply | `Reply`, or every authority if master or grant-capable |
| Frame | `Read` and/or `Write` by its rights (execute confers nothing) |

`pas_refined` says the concrete state is within the policy
(`l4v:proof/access-control/Access.thy:L312-L319`): the policy is
well-formed for the subject; IRQ slots are labelled consistently; every
thread's label is one of the labels of its scheduler domain
(`l4v:proof/access-control/Access.thy:L268-L280`); and every authority
derivable from the state — from capabilities, thread states, bound
notifications, the derivation tree, page-table contents and ASID tables —
is an edge of the policy.

Policy well-formedness is where the structural restrictions live
(`l4v:proof/access-control/Access.thy:L63-L77`). For the acting label:

- `Control` over another label means it *is* that label. Hence an
  untyped, CNode, thread, page-table or ASID-pool capability can never
  point across labels: **memory, CSpaces, threads and address-space
  structures are never shared between labels.**
- `Grant` to an endpoint plus someone's `Receive` on it puts sender and
  receiver in mutual `Control`, hence in one label: **capability transfer
  cannot cross a label boundary.**
- `Call` implies `SyncSend`; a caller and a receiver on the same endpoint
  give the receiver `Reply` to the caller; `Reply` gives the replied-to
  party `DeleteDerived` back, transitively.
- If the subject may send IRQs, it may notify whatever any IRQ may notify.

`integrity` relates the state before and after a step by the acting
subject (`l4v:proof/access-control/Access.thy:L898-L919`). Per object it
allows exactly the changes below
(`l4v:proof/access-control/Access.thy:L418-L531`); these are **the
complete list of kernel-mediated writes one label can cause in another
label's objects**, which is the interface a new kernel's integrity proof
must reproduce or shrink:

| Rule | Change to an object the subject does not own | Authority required |
| --- | --- | --- |
| `troa_lrefl` | anything | the subject owns the object |
| `troa_ntfn` | notification state | `Receive`, `Notify` or `Reset` on it |
| `troa_ep` | endpoint state | `Receive`, `SyncSend` or `Reset` on it |
| `troa_ep_unblock` | endpoint state, when a receiver there is also bound to a notification | `Notify` on that notification |
| `troa_tcb_send` | a blocked receiver gets new registers and becomes `Running` | may send to its endpoint, or notify its bound notification |
| `troa_tcb_call` | as above, plus a reply capability to the subject placed in its caller slot | `Call` on its endpoint |
| `troa_tcb_reply` | a thread awaiting reply gets registers, fault cleared, becomes `Running` (or `Restart`/`Inactive` after a fault) | `Reply` to its label |
| `troa_tcb_receive` | a blocked sender becomes `Running`, `Inactive`, or awaits reply | `Receive` on its endpoint |
| `troa_tcb_restart` | a thread blocked on an object becomes `Restart` | `Reset` on that object |
| `troa_tcb_unbind` | a thread's bound notification is cleared | `Reset` on that notification |
| `troa_tcb_empty_ctable`, `troa_tcb_empty_caller` | a derived reply capability disappears from another thread's slot | reply-capability deletion authority |
| `troa_tcb_activate` | a `Restart` thread is activated | none, if the policy allows activation |
| `troa_tcb_fpu` | architecture state other than registers | none (constrained elsewhere) |
| `troa_cnode` | deletable (reply) capabilities vanish from a CNode | reply-capability deletion authority |
| `troa_arch` | an ASID-pool entry is **cleared** | `Control` over the address space it named (`l4v:proof/access-control/RISCV64/ArchAccess.thy:L131-L150`) |

Beyond objects, `integrity` constrains the derivation tree, interrupt
state, ready queues (editable only when `pasMayEditReadyQueues`), user
memory (writable through `Write` authority or as the IPC buffer of a
thread the subject may deliver to), device memory, and ASID tables.

#### 4.3 Information flow: what a partition may read and affect

- **One label per domain.** `pas_domains_distinct`: every scheduler
  domain maps to exactly one label so that labels cannot leak information
  through scheduling decisions
  (`l4v:proof/infoflow/InfoFlow.thy:L24-L37`). The policy must also be
  well-formed for *every* label, not only the current one
  (`l4v:proof/infoflow/PasUpdates.thy:L22-L26`).
- **`subjectReads`** is the closure of what a label may observe
  (`l4v:proof/infoflow/InfoFlow.thy:L55-L139`). Besides `Read`, it
  contains: any endpoint the label can send to or receive from; from any
  readable synchronous endpoint, **all its senders, callers and
  receivers**; from any readable thread, the pages it can read; from any
  readable page, every thread that can write it; and both ends of every
  `Reply` and `DeleteDerived` edge. Synchronous IPC is therefore
  bidirectional for information flow by definition. The theory comments
  explain the reason in each case: completing a rendezvous observes the
  queue and the blocked partner's state.
- **`subjectAffects`** is what a label may influence
  (`l4v:proof/infoflow/InfoFlow.thy:L306-L350`): targets of `Control`,
  `Write`, `Receive`, `Notify`, `SyncSend`, `Call`, `Reset`; the IPC
  buffers of receivers it can send to; **senders on endpoints it receives
  from** (because synchronous sends expose a back-channel from receiver to
  sender); both directions of `Reply`; `DeleteDerived` targets and
  co-deleters; the owner of any ASID it maps; and an endpoint whose
  receiver is bound to a notification it can signal.
- **`reads_equiv`** — two states look the same to the subject
  (`l4v:proof/infoflow/InfoFlow.thy:L275-L283`) — requires equality on
  everything in `subjectReads` (objects, memory, derivation tree, IRQ
  state, ready queues, ASIDs;
  `l4v:proof/infoflow/InfoFlow.thy:L216-L230`) **and** equality of five
  global values: current thread, current domain, scheduler action,
  `work_units_completed`, and the machine's `irq_state`. Those five are
  public to every partition, so the kernel must keep them independent of
  any other partition's secrets.
- **`affects_equiv`** for a label is equality on everything that label
  reads, required only if the subject can affect something that label
  reads (`l4v:proof/infoflow/InfoFlow.thy:L355-L366`).
- **Globals** every partition may depend on: on RISCV64 the global page
  table pointer and its contents, the idle thread and its saved context,
  and the current thread
  (`l4v:proof/infoflow/InfoFlow.thy:L250-L267`,
  `l4v:proof/infoflow/RISCV64/ArchInfoFlow.thy:L59-L71`).
- **The scheduler is its own partition, `PSched`.** It flows to every
  partition and no partition flows to it
  (`l4v:proof/infoflow/Noninterference.thy:L36-L36`,
  `l4v:proof/infoflow/Noninterference.thy:L252-L273`). Its state is the
  domain fields — current domain, domain time, schedule index, schedule
  start index and the schedule list — plus the idle thread, globals, and
  the IRQ state (`l4v:proof/infoflow/Scheduler_IF.thy:L71-L76`,
  `l4v:proof/infoflow/Scheduler_IF.thy:L185-L188`).

#### 4.4 Invariants and assumptions of the theorem, and the channel each closes

The invariant bundle the system must satisfy forever
(`l4v:proof/infoflow/ADT_IF.thy:L1664-L1671`) and the assumptions on the
initial state and policy (`l4v:proof/infoflow/ADT_IF.thy:L1660-L1685`):

| Requirement | Definition | Channel it closes, or what it assumes away |
| --- | --- | --- |
| No domain capability anywhere | first conjunct of `domain_sep_inv` (`l4v:proof/access-control/DomainSepInv.thy:L26-L35`); domain invocations are treated as unreachable (`l4v:proof/infoflow/ADT_IF.thy:L1739-L1748`) | a partition moving threads between domains or rewriting the schedule would write scheduler-partition state. The specification does contain a run-time schedule (start index and end marker, `l4v:spec/abstract/Schedule_A.thy:L52-L69`); the proof keeps it static by excluding the capability |
| No interrupt-control or interrupt-handler capability; no IRQ in the signalling state; non-kernel IRQs inactive; interrupt states never change | `domain_sep_inv False` (same lines) | an interrupt raised by one partition's device while another runs would preempt the second at a time chosen by the first |
| Only the timer interrupt is enabled, and it recurs | `only_timer_irq_inv` (`l4v:proof/infoflow/CNode_IF.thy:L359-L375`, `l4v:proof/infoflow/CNode_IF.thy:L436-L439`) | same; recurrence also guarantees every kernel big step terminates |
| The policy never lets subjects send IRQs | `pasMaySendIrqs initial_aag = False` | same |
| Interrupt arrival is a fixed function of a counter | machine state has `irq_state :: nat` and an axiomatised `irq_oracle` (`l4v:spec/design/m-skel/RISCV64/MachineTypes.thy:L39-L62`); `irq_state` is in `reads_equiv` | **assumes** interrupt timing does not depend on what user code computed; real time is not modelled |
| Capabilities that point across labels have an undeletable copy | `silc_inv`: every inter-label capability overlaps one held in a CNode of an inert label that nothing has authority over (`l4v:proof/infoflow/FinalCaps.thy:L7-L12`, `l4v:proof/infoflow/FinalCaps.thy:L83-L98`) | deleting the *last* capability to a shared object runs its finaliser (3.2), which restarts the other partition's blocked threads; whether a deletion is "last" would otherwise reveal the other partition's capability holdings |
| Each domain has one label; each thread's label matches its domain; the running thread belongs to the current domain's label | `pas_domains_distinct`, `tcb_domain_map_wellformed`, `guarded_pas_domain` (`l4v:proof/access-control/Syscall_AC.thy:L229-L232`) | a thread running outside its domain's time slice. The fastpath's same-domain guards (2.2 C9, 2.3 R9) are the implementation counterpart |
| Initially: scheduler action is "resume current thread", domain time is positive, the domain schedule is valid | locale assumptions | well-formed start of the first time slice |
| User behaviour is a deterministic function of what the thread can see, and never produces an interrupt event | `utf_det`, `utf_non_interrupt` | **assumes** user programs cannot observe anything outside the modelled state (no clocks, no caches) |
| The preemption-point counter is public and reset at each domain switch | `work_units_completed` is in `reads_equiv`; `preemption_point` increments it and polls for an interrupt only at the limit (`l4v:spec/abstract/Exceptions_A.thy:L60-L69`); `next_domain` zeroes it (`l4v:spec/abstract/Schedule_A.thy:L52-L69`); the C kernel does the same (`seL4:src/kernel/thread.c:L326-L338`) | work done by one domain's long-running operations would otherwise shift where the next domain's operations get preempted |
| The scheduler does not read the idle thread's priority | C comment (`seL4:src/kernel/thread.c:L393-L399`) | idle-thread state is global; reading it on a path that also depends on a partition's state would mix the two |

Restrictions that follow from the policy rules rather than from a named
invariant (**derived** from 4.2 and 4.3):

- **Between partitions, only notifications give one-way flow.** A shared
  synchronous endpoint makes each side a reader of the other.
- **No capability transfer, no shared untyped memory, no shared CNodes,
  page tables or ASID pools across partitions.** Sharing a frame is
  possible and is a `Read`/`Write` edge.
- **Every endpoint or notification capability carries `Reset`**, because
  deleting the last one restarts waiters. That is why shared objects need
  the undeletable copy above.
- **ASID assignment is a flow.** Mapping an ASID affects the label that
  owns it; clearing an ASID-pool entry is permitted to whoever controls
  the address space.

#### 4.5 What the model leaves out

- **Machine state.** The RISCV64 machine record has interrupt masks, the
  interrupt counter, memory bytes, device memory and one opaque field
  (`l4v:spec/design/m-skel/RISCV64/MachineTypes.thy:L39-L62`). There is no
  TLB, no cache, no clock and no CSR other than what the saved user
  context contains.
- **TLB and address-space operations are uninterpreted.** `hwASIDFlush`,
  `sfence` and `setVSpaceRoot` are lifted from constants that act only on
  the opaque field (`l4v:spec/machine/RISCV64/MachineOps.thy:L197-L223`).
  No l4v theorem can therefore depend on, or establish, that a flush
  happens when it should. Stale-translation bugs are outside what the
  functional-correctness, integrity and information-flow proofs can see.
- **Reading the trap-value register is assumed safe.** The RISCV64
  information-flow theory contains an axiom that reading `stval`
  preserves the reads-equivalence
  (`l4v:proof/infoflow/RISCV64/ArchArch_IF.thy:L1246-L1252`). The value
  lives in the opaque machine state, so the proof cannot derive this.
- **User registers.** On kernel entry the user context is stored into the
  current thread's TCB, and on exit the context of whichever thread is
  now current is loaded from its TCB
  (`l4v:proof/infoflow/ADT_IF.thy:L754-L766`,
  `l4v:proof/infoflow/ADT_IF.thy:L1438-L1446`). In the model a switch
  replaces the whole user-visible register state, so nothing needs
  scrubbing. The model's guarantee transfers to hardware only for state
  that the saved context covers; 1.2 lists two things it does not cover
  (the LR/SC reservation and any further user-readable CSRs).
- **Domain switch.** The architecture hook run before a domain switch
  does nothing on RISC-V in the C kernel
  (`seL4:src/arch/riscv/kernel/thread.c:L59-L62`). No flush of any
  hardware state is modelled or performed at a domain switch.
- **Time.** Covert timing channels are outside the model entirely;
  interrupt arrival is the oracle described in 4.4.

#### 4.6 Consequences for a new kernel's information-flow argument

**derived** from 4.1 – 4.5.

1. The seL4 result is conditional on a system shape: static domain
   schedule, one label per domain, polling instead of device interrupts,
   no capability transfer or shared kernel memory between partitions, and
   an undeletable copy of every shared capability. A kernel that wants
   interrupt-driven I/O across partitions, shared rings, or frame loans
   between partitions is outside that shape and needs new flow rules for
   each, not a port of the existing proof.
2. Any mechanism whose behaviour depends on "is this the last reference"
   is a cross-partition channel if the references can be held by more
   than one partition. This applies to generation counters and reference
   counts as much as to seL4's final-capability test.
3. Every piece of global kernel state read on a syscall path must be
   either scheduler-partition state or provably the same in all runs the
   observer cannot distinguish. seL4's list is short: current thread,
   current domain, scheduler action, the preemption counter, the
   interrupt counter, the idle thread, the global page table. Extension
   state (module registries, ring bookkeeping) has to be placed in one of
   these classes or partitioned by label.
4. A proof that models the TLB, the reservation set and the full CSR
   state would cover ground that l4v leaves to assumption. That is the
   concrete sense in which trap-path scrubbing and `sfence.vma`
   discipline can exceed the seL4 guarantees.

## Boundaries

**Not examined**

- The MCS kernel configuration, SMP, the FPU paths, the hypervisor
  configuration, and 32-bit RISC-V. MCS and SMP guards are listed where
  they sit next to examined code, without analysis.
- Fault message formats, boot information, the PLIC driver, and the
  argument marshalling of individual invocations. The report covers the
  generic invocation path and the label enumeration, not each method's
  argument list.
- `seL4/verification-manifest`. Whether the two pinned commits form a
  proved pair was not checked.
- Whether the l4v theories build. No Isabelle session was run; "proved"
  means "stated as a lemma or theorem in the pinned tree".
- Which locale assumptions of the top-level information-flow theorems are
  discharged for RISCV64, and which l4v sessions the upstream test
  configuration runs for each architecture.
- The individual `reads_respects` lemmas for each kernel operation. Section
  4 reports the definitions, invariants and top-level statements, not the
  per-operation proofs.
- The Haskell executable specification and the abstract specification
  beyond the definitions cited. In particular the equivalence argument in
  2.4 is this report's reading of the C code, not a restatement of an l4v
  proof for RISCV64 (none exists).
- Timing. No worst-case execution time or cache behaviour was measured or
  modelled.

**Unknown**

- Why the RISCV64 fastpath refinement proof is absent. The tree records
  only that it is left out.
- Whether a hart's LR/SC reservation actually survives the fastpath exit
  on QEMU or on real cores (1.2). The specification leaves it to the
  implementation.
- Where the lower bound "a CNode capability resolves at least one bit" is
  enforced on the creation path (1.5).
- Whether stale mapping fields can cause harm after an ASID is reused: a
  frame capability whose recorded ASID was deleted and later reassigned to
  another address space will, when deleted, unmap that frame from the new
  address space if it happens to be mapped at the same virtual address
  through a different capability. The code path permits it (3.3); whether
  an invariant excludes it was not determined.
- Whether replacing the current thread's address-space root without a
  reschedule (3.4) is intended behaviour.

**Known not to apply**

- The fastpath proofs for ARM, ARM_HYP and AARCH64 do not transfer to
  RISCV64 by themselves: the address-space guard, the context-switch
  helper and the exit stub are architecture-specific, and the RISCV64 C
  refinement theorem is stated only for the kernel entry without the
  fastpath (2.5).
- The capability bit layouts in 1.6 are not part of the user ABI and
  impose nothing on a kernel that only needs `libsel4` compatibility.
- The l4v noninterference theorem does not cover systems in which a
  partition holds an interrupt-handler, interrupt-control or domain
  capability, or in which a device interrupt other than the timer is
  enabled (section 4).

**Stronger conclusions the evidence does not support**

- "seL4 on RISC-V is verified including its IPC fastpath." The verified
  configuration enables the fastpath; the theorem excludes it.
- "ASIDs make address-space switches cheap on seL4/RISC-V." The global
  flush on every switch removes the benefit.
- "A generation counter checked at capability lookup is enough for
  revocation." It covers none of the rows in 3.2.
- "l4v proves the absence of covert channels." It proves noninterference
  for a model without time, caches or TLB, under the system restrictions
  in section 4.

**Open design premises and follow-up questions**

1. A new kernel that keeps TLB entries across switches needs its own
   proof obligations for ASID lifetime: flush on unmap (per page), on
   address-space deletion (per ASID), on pool deletion (every ASID in the
   pool) and before ASID reuse. seL4 offers no model to adapt.
2. Fastpath soundness depends on two entry invariants that are not
   visible in the C guards: the scheduler action is "resume current
   thread", and the domain time slice has not expired. A new kernel needs
   them as explicit preconditions of its fastpath theorem.
3. The upstream label and syscall numbering is unstable by construction.
   A compatibility claim needs a pinned interface revision, and extension
   labels need a reserved range.
4. A trap path that must not leak between threads has to decide what to
   do with state the saved context omits: the LR/SC reservation and any
   user-readable CSRs beyond the 35 saved slots.
5. Upstream now lets the holder of the domain capability rewrite the
   domain schedule at run time. The noninterference proof excludes domain
   capabilities from partitions; a new kernel must either keep the
   schedule static or treat schedule changes as a scheduler-partition
   action with its own proof.
6. Revocation can be left half-done when the revoker deletes itself. A
   design that promises "revoke completes or the caller observes failure"
   needs a different restart protocol.

## Evidence

**Subjects and acquisition** (observed 2026-11-19)

| Repository | Commit | Acquired as |
| --- | --- | --- |
| `seL4/seL4` | `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7` | `https://codeload.github.com/seL4/seL4/tar.gz/<commit>` |
| `seL4/l4v` | `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e` | `https://codeload.github.com/seL4/l4v/tar.gz/<commit>` |

Both commits were the tips of `master` when fetched. Each archive's
embedded commit identifier (`git get-tar-commit-id`) equals the pin. The
archives are generated by GitHub on request, so their byte hashes are not
a stable identity; the commit identifier is. `support/fetch_subjects.sh`
repeats the acquisition and the check.

GitHub API metadata (commit dates, tags, pull requests) was not collected
during acquisition due to API rate limits; everything in this report comes
directly from the two pinned source trees.

**Source citations.** Every `repo:path:Lstart-Lend` token in this report
has a row in `support/citations_kernel.tsv` or
`support/citations_l4v_infoflow.tsv` naming a literal string that must
occur in that line range of the pinned tree. `support/check_citations.py`
verifies all rows and verifies that no token in the report lacks a row.

**Execution evidence.** Two scripts re-implement upstream generator rules
over the pinned tree, because the upstream generators need Python
packages that were not available:

- `support/abi_numbers.py` — syscall numbers and invocation labels
  (sections 1.1 and 1.4). Rule sources:
  `libsel4/tools/syscall_header_gen.py` and
  `libsel4/tools/invocation_header_gen.py`.
- `support/bf_layout.py` — bit positions of bitfield blocks (sections 1.3
  and 1.6). Rule source: `tools/bitfield_gen.py`, `Block.checks`. The
  result is cross-checked against hand-written word assembly in the
  fastpath headers (1.3).

These are re-implementations, not the upstream tools. Their output is
evidence for the numbering and layout only to the extent that the cited
rule is the whole rule; a kernel build's generated headers are the
authority.

One search result is cited as execution: `grep -rn 'sc\.w'
include/arch/riscv src/arch/riscv` over the pinned seL4 tree prints
exactly one line, `src/arch/riscv/c_traps.c:48` (section 1.2).

**Upstream identifiers and citation anchors.** Prose in `REPORT.md`
paraphrases upstream behaviour and definitions without multi-line verbatim
source extracts. Single-line literal anchor substrings in
`support/citations_kernel.tsv` and `support/citations_l4v_infoflow.tsv`
are retained solely for automated citation verification against the pinned
upstream trees and remain under their upstream licences (seL4 kernel
sources GPL-2.0-only, `libsel4` BSD-2-Clause, l4v per-file GPL-2.0-only or
BSD-2-Clause).

**Derived statements** are marked where they occur, with the reasoning
beside them. The largest are the equivalence argument in 2.4, the
characterisation of lazy versus eager cleanup in 3.3, the TLB-flush
dependence in 3.4, and the compatibility seam in 1.7.

## Revalidation

Cheapest checks, in order of cost:

1. **Same subjects, citations intact.**

   ```console
   reports/sel4-riscv64-abi-fastpath-revocation-and-l4v-infoflow/support/fetch_subjects.sh /tmp/sel4-subjects
   python3 reports/sel4-riscv64-abi-fastpath-revocation-and-l4v-infoflow/support/check_citations.py \
     --sel4 /tmp/sel4-subjects/seL4 --l4v /tmp/sel4-subjects/l4v \
     --report reports/sel4-riscv64-abi-fastpath-revocation-and-l4v-infoflow/REPORT.md \
     reports/sel4-riscv64-abi-fastpath-revocation-and-l4v-infoflow/support/citations_kernel.tsv \
     reports/sel4-riscv64-abi-fastpath-revocation-and-l4v-infoflow/support/citations_l4v_infoflow.tsv
   ```

   Expected: `0 failed` and `0 without a row`. This shows only that the
   cited text is where the report says it is.

2. **ABI numbers and layouts.**

   ```console
   python3 reports/sel4-riscv64-abi-fastpath-revocation-and-l4v-infoflow/support/abi_numbers.py /tmp/sel4-subjects/seL4
   python3 reports/sel4-riscv64-abi-fastpath-revocation-and-l4v-infoflow/support/bf_layout.py /tmp/sel4-subjects/seL4
   ```

   Compare with the tables in 1.1, 1.4, 1.3 and 1.6. Against a newer seL4
   tree the same commands show at once whether labels were renumbered or
   fields moved. A stronger check is to build a RISCV64 kernel and compare
   the generated `invocation.h`, `syscall.h` and bitfield headers.

3. **A newer upstream revision.** Re-run step 1 against the new trees
   after editing the two commit identifiers in `fetch_subjects.sh`. Each
   failing row identifies a region to re-read. The regions that decide
   the main findings are few:
   - fastpath guards: `src/fastpath/fastpath.c` and
     `include/arch/riscv/arch/fastpath/fastpath.h`;
   - fastpath proof status: whether `proof/crefine/RISCV64/Fastpath_C.thy`
     exists and whether `refinement2_both` in
     `proof/crefine/RISCV64/Refine_C.thy` still assumes `fp = False`;
   - TLB behaviour: `setVSpaceRoot` in
     `include/arch/riscv/arch/machine.h`;
   - finalisers: `finaliseCap` in `src/object/objecttype.c` and
     `Arch_finaliseCap` in `src/arch/riscv/object/objecttype.c`;
   - noninterference assumptions: the `Invs` definition and the locale
     assumptions in `proof/infoflow/ADT_IF.thy`, and `domain_sep_inv` in
     `proof/access-control/DomainSepInv.thy`.

4. **Claims marked "not confirmed by execution"** (reservation survival
   across the fastpath exit, the stale-`satp` window, incomplete
   self-revocation) need a running RISCV64 kernel under QEMU with a small
   user-level test each; no cheaper check exists.
