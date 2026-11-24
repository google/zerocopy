# MiniRust atomic memory

This is a wrapper for a memory that distinguishes between non-atomic and atomic memory accesses.
For now atomicity is ignored; this will change in the future.

```rust
pub struct ConcurrentMemory<M: Memory> {
    memory: M,

    /// List of all memory access done by the active thread in the current step.
    accesses: List<Access>,
}

/// The different kinds of atomicity.
pub enum Atomicity {
    /// A sequentially consistent atomic access.
    Atomic,

    /// A non-atomic memory access.
    None,
}

/// Internal type used to track the type of a memory access.
enum AccessType {
    Store,
    Load,
}

/// Access contains all information the data race detection needs about a single access.
pub struct Access {
    ty: AccessType,
    atomicity: Atomicity,
    addr: Address,
    len: Size,
}
```

## Interface

The atomic memory presents a very similar interface to the `Memory`.
It differs in both store and load where we also take the `Atomicity` of an operation.

```rust
impl<M: Memory> ConcurrentMemory<M> {
    pub fn new(params: M::Params) -> Self {
        Self {
            memory: M::new(params),
            accesses: list![],
        }
    }

    /// Create a new allocation.
    /// The initial contents of the allocation are `AbstractByte::Uninit`.
    pub fn allocate(&mut self, kind: AllocationKind, size: Size, align: Align) -> NdResult<ThinPointer<M::Provenance>> {
        self.memory.allocate(kind, size, align)
    }

    /// Remove an allocation.
    pub fn deallocate(&mut self, ptr: ThinPointer<M::Provenance>, kind: AllocationKind, size: Size, align: Align) -> Result {
        self.memory.deallocate(ptr, kind, size, align)
    }

    /// Write some bytes to memory and check for data races.
    pub fn store(&mut self, ptr: ThinPointer<M::Provenance>, bytes: List<AbstractByte<M::Provenance>>, align: Align, atomicity: Atomicity) -> Result {
        let access = Access {
            ty: AccessType::Store,
            atomicity,
            addr: ptr.addr,
            len: Size::from_bytes(bytes.len()).unwrap(),
        };
        self.accesses.push(access);

        self.memory.store(ptr, bytes, align)
    }

    /// Read some bytes from memory and check for data races.
    pub fn load(&mut self, ptr: ThinPointer<M::Provenance>, len: Size, align: Align, atomicity: Atomicity) -> Result<List<AbstractByte<M::Provenance>>> {
        let access = Access {
            ty: AccessType::Load,
            atomicity,
            addr: ptr.addr,
            len,
        };
        self.accesses.push(access);

        self.memory.load(ptr, len, align)
    }

    /// Test whether the given pointer is dereferenceable for the given size.
    /// Raises UB if that is not the case.
    pub fn dereferenceable(&self, ptr: ThinPointer<M::Provenance>, len: Size) -> Result {
        self.memory.dereferenceable(ptr, len)
    }

    /// A derived form of `dereferenceable` that works with a signed notion on "length".
    pub fn signed_dereferenceable(&self, ptr: ThinPointer<M::Provenance>, len: Int) -> Result {
        self.memory.signed_dereferenceable(ptr, len)
    }

    /// Return the retagged pointer.
    pub fn retag_ptr(
        &mut self,
        frame_extra: &mut M::FrameExtra,
        ptr: Pointer<M::Provenance>,
        ptr_type: PtrType,
        fn_entry: bool,
        fn_implicit_writes: bool, // wether implicit_writes are enabled for the currently evaluated function, or not
        vtable_lookup: impl Fn(ThinPointer<M::Provenance>) -> crate::lang::VTable + 'static,
    ) -> Result<Pointer<M::Provenance>> {
        self.memory.retag_ptr(frame_extra, ptr, ptr_type, fn_entry, fn_implicit_writes, vtable_lookup)
    }

    /// Memory model hook invoked at the end of each function call.
    pub fn end_call(&mut self, extra: M::FrameExtra) -> Result {
        self.memory.end_call(extra)
    }

    /// Check if there are any memory leaks.
    pub fn leak_check(&self) -> Result {
        self.memory.leak_check()
    }
}
```

## Data race detection

Here we define the operations needed to make data race detection.
The type `ThreadId` is used to identify threads.

```rust
/// The ID of a thread is an index into the machine's `threads` list.
pub type ThreadId = Int;

impl<M: Memory> ConcurrentMemory<M> {
    /// Given a list of previous accesses, checks if any of the current accesses is in a data race with any of those.
    pub fn check_data_races(
        &self,
        current_thread: ThreadId,
        (prev_sync_threads, prev_accesses): (Set<ThreadId>, List<Access>),
    ) -> Result {
        if prev_sync_threads.contains(current_thread) { return Ok(()) }

        for access in self.accesses {
            if prev_accesses.any(|prev_access| access.races(prev_access)) {
                throw_ub!("Data race");
            }
        }

        Ok(())
    }

    /// Prepare memory to track accesses of next step: reset the internal access list to
    /// be empty, and return the list of previously collected accesses.
    pub fn reset_accesses(&mut self) -> List<Access> {
        let prev_accesses = self.accesses;
        self.accesses = list![];
        prev_accesses
    }
}

impl Access {
    /// Indicates if a races happend between the two given accesses.
    /// We assume they happen on different threads.
    fn races(self, other: Self) -> bool {
        // At least one access modifies the data.
        if self.ty == AccessType::Load && other.ty == AccessType::Load { return false; }

        // At least one access is non atomic
        if self.atomicity == Atomicity::Atomic && other.atomicity == Atomicity::Atomic { return false; }

        // The accesses overlap.
        let end_addr = self.addr + self.len.bytes();
        let other_end_addr = other.addr + other.len.bytes();
        end_addr > other.addr && other_end_addr > self.addr
    }
}
```
