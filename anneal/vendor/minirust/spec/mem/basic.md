# MiniRust basic memory model

This is almost the simplest possible fully-feature implementation of the MiniRust memory model interface.
It does *not* model any kind of aliasing restriction, but otherwise should be enough to explain all the behavior and Undefined Behavior we see in Rust, in particular with respect to bounds-checks for memory accesses and pointer arithmetic.
This demonstrates well how the memory interface works, as well as the basics of "per-allocation provenance".
The full MiniRust memory model will likely be this basic model plus some [extra restrictions][Stacked Borrows] to ensure the program follows the aliasing rules; possibly with some extra tricks to [explain OOM-reducing optimizations](https://github.com/rust-lang/unsafe-code-guidelines/issues/328).

This memory model permits holding some "extra" data in each pointer and each allocation, so that code can be shared with more complicated models.

[Stacked Borrows]: https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md

## Data structures

The provenance tracked by this memory model is just an ID that identifies which allocation the pointer points to.
(We will pretend we can split the `impl ... for` block into multiple smaller blocks.)

```rust
pub struct AllocId(Int);

type Provenance<Extra> = (AllocId, Extra);
```

The data tracked by the memory is fairly simple: for each allocation, we track its data contents, its absolute integer address in memory, the alignment it was created with (the size is implicit in the length of the contents), and whether it is still alive (or has already been deallocated).

```rust
struct Allocation<ProvExtra = (), AllocExtra = ()> {
    /// The data stored in this allocation.
    data: List<AbstractByte<Provenance<ProvExtra>>>,
    /// The address where this allocation starts.
    /// This is never 0, and `addr + data.len()` fits into a `usize`.
    addr: Address,
    /// The alignment that was requested for this allocation.
    /// `addr` will be a multiple of this.
    align: Align,
    /// The kind of this allocation.
    kind: AllocationKind,
    /// Whether this allocation is still live.
    live: bool,
    /// Additional information needed for the memory model
    extra: AllocExtra,
}
```

Memory then consists of a map tracking the allocation for each ID, stored as a list (since we assign IDs consecutively).

```rust
pub struct BasicMemory<T: Target, ProvExtra = (), AllocExtra = ()> {
    allocations: List<Allocation<ProvExtra, AllocExtra>>,

    // FIXME: specr should add this automatically
    _phantom: std::marker::PhantomData<T>,
}

impl<T: Target, ProvExtra, AllocExtra> BasicMemory<T, ProvExtra, AllocExtra> {
    fn new() -> Self {
        Self { allocations: List::new(), _phantom: std::marker::PhantomData }
    }
}
```

## Operations

We start with some helper operations.

```rust
impl<ProvExtra, AllocExtra> Allocation<ProvExtra, AllocExtra> {
    fn size(self) -> Size {
        Size::from_bytes(self.data.len()).unwrap()
    }

    fn overlaps(self, other_addr: Address, other_size: Size) -> bool {
        let end_addr = self.addr + self.size().bytes();
        let other_end_addr = other_addr + other_size.bytes();
        if end_addr <= other_addr || other_end_addr <= self.addr {
            // Our end is before their beginning, or vice versa -- we do not overlap.
            // However, to make sure that each allocation has a unique address, we still
            // report overlap if both allocations have the same address.
            // FIXME: This is not necessarily realistic, e.g. for zero-sized stack variables.
            // OTOH the function pointer logic currently relies on this.
            self.addr == other_addr
        } else {
            true
        }
    }
}
```

Then we implement creating and removing allocations.

```rust
impl<T: Target, ProvExtra, AllocExtra> BasicMemory<T, ProvExtra, AllocExtra> {
    fn allocate(
        &mut self,
        kind: AllocationKind,
        size: Size,
        align: Align,
        prov_extra: ProvExtra,
        alloc_extra: AllocExtra,
    ) -> NdResult<ThinPointer<Provenance<ProvExtra>>> {
        // Reject too large allocations. Size must fit in `isize`.
        if !T::valid_size(size) {
            throw_ub!("asking for a too large allocation");
        }
        // Pick a base address. We use daemonic non-deterministic choice,
        // meaning the program has to cope with every possible choice.
        // FIXME: This makes OOM (when there is no possible choice) into "no behavior",
        // which is not what we want.
        let distr = libspecr::IntDistribution {
            start: Int::ONE,
            end: Int::from(2).pow(T::PTR_SIZE.bits()),
            divisor: align.bytes(),
        };
        let addr = pick(distr, |addr: Address| {
            // Pick a strictly positive integer...
            if addr <= 0 { return false; }
            // ... that is suitably aligned...
            if !align.is_aligned(addr) { return false; }
            // ... such that addr+size is in-bounds of a `usize`...
            if !(addr+size.bytes()).in_bounds(Unsigned, T::PTR_SIZE) { return false; }
            // ... and it does not overlap with any existing live allocation.
            if self.allocations.any(|a| a.live && a.overlaps(addr, size)) { return false; }
            // If all tests pass, we are good!
            true
        })?;

        // Compute allocation.
        let allocation = Allocation {
            addr,
            align,
            kind,
            live: true,
            data: list![AbstractByte::Uninit; size.bytes()],
            extra: alloc_extra,
        };

        // Insert it into list, and remember where.
        let id = AllocId(self.allocations.len());
        self.allocations.push(allocation);

        // And we are done!
        ret(ThinPointer { addr, provenance: Some((id, prov_extra)) })
    }

    fn deallocate(
        &mut self,
        ptr: ThinPointer<Provenance<ProvExtra>>,
        kind: AllocationKind,
        size: Size,
        align: Align,
        handle_extra: impl FnOnce(&mut AllocExtra, ProvExtra) -> Result,
    ) -> Result {
        let Some((id, prov_extra)) = ptr.provenance else {
            throw_ub!("deallocating invalid pointer")
        };
        // This lookup will definitely work, since AllocId cannot be faked.
        let mut allocation = self.allocations[id.0];

        // Check a bunch of things.
        if !allocation.live {
            throw_ub!("double-free");
        }
        if ptr.addr != allocation.addr {
            throw_ub!("deallocating with pointer not to the beginning of its allocation");
        }
        if kind != allocation.kind {
            throw_ub!("deallocating {:?} memory with {:?} deallocation operation", allocation.kind, kind);
        }
        if size != allocation.size() {
            throw_ub!("deallocating with incorrect size information");
        }
        if align != allocation.align {
            throw_ub!("deallocating with incorrect alignment information");
        }

        // Check "extra" things.
        handle_extra(&mut allocation.extra, prov_extra)?;

        // Mark it as dead.
        allocation.live = false;

        // That's it!
        self.allocations.set(id.0, allocation);

        ret(())
    }
}
```

The key operations of a memory model are of course handling loads and stores.
The helper function `check_ptr` we define for them is also used to implement the final part of the memory API, `dereferenceable`.

```rust
impl<T: Target, ProvExtra, AllocExtra> BasicMemory<T, ProvExtra, AllocExtra> {
    /// Check if the given pointer is dereferenceable for an access of the given
    /// length. For dereferenceable, return the allocation ID and
    /// offset; this can be missing for invalid pointers and accesses of size 0.
    fn check_ptr(&self, ptr: ThinPointer<Provenance<ProvExtra>>, len: Size) -> Result<Option<(AllocId, ProvExtra, Size)>> {
        // For zero-sized accesses, there is nothing to check.
        // (Provenance monotonicity says that if we allow zero-sized accesses
        // for `None` provenance we have to allow it for all provenance.)
        if len.is_zero() {
            return ret(None);
        }
        // We do not even have to check for null, since no allocation will ever contain that address.
        // Now try to access the allocation information.
        let Some((id, prov_extra)) = ptr.provenance else {
            // An invalid pointer.
            throw_ub!("dereferencing pointer without provenance");
        };
        let allocation = self.allocations[id.0];
        if !allocation.live {
            throw_ub!("dereferencing pointer to dead allocation");
        }

        // Compute relative offset, and ensure we are in-bounds.
        // We don't need a null ptr check, we just have an invariant that no allocation
        // contains the null address.
        let offset_in_alloc = ptr.addr - allocation.addr;
        if offset_in_alloc < 0 || offset_in_alloc + len.bytes() > allocation.size().bytes() {
            throw_ub!("dereferencing pointer outside the bounds of its allocation");
        }

        // All is good!
        ret(Some((id, prov_extra, Offset::from_bytes(offset_in_alloc).unwrap())))
    }

    fn store(
        &mut self,
        ptr: ThinPointer<Provenance<ProvExtra>>,
        bytes: List<AbstractByte<Provenance<ProvExtra>>>,
        align: Align,
        handle_extra: impl FnOnce(&mut AllocExtra, ProvExtra, Offset) -> Result,
    ) -> Result {
        if !align.is_aligned(ptr.addr) {
            throw_ub!("store to a misaligned pointer");
        }
        let size = Size::from_bytes(bytes.len()).unwrap();
        let Some((id, prov_extra, offset)) = self.check_ptr(ptr, size)? else {
            return ret(());
        };
        let mut allocation = self.allocations[id.0];

        // Check and update "extra" state.
        handle_extra(&mut allocation.extra, prov_extra, offset)?;

        // Slice into the contents, and put the new bytes there.
        allocation.data.write_subslice_at_index(offset.bytes(), bytes);
        self.allocations.set(id.0, allocation);

        ret(())
    }

    fn load(
        &mut self,
        ptr: ThinPointer<Provenance<ProvExtra>>,
        len: Size,
        align: Align,
        handle_extra: impl FnOnce(&mut AllocExtra, ProvExtra, Offset) -> Result,
    ) -> Result<List<AbstractByte<Provenance<ProvExtra>>>> {
        if !align.is_aligned(ptr.addr) {
            throw_ub!("load from a misaligned pointer");
        }
        let Some((id, prov_extra, offset)) = self.check_ptr(ptr, len)? else {
            return ret(list![]);
        };
        let mut allocation = self.allocations[id.0];

        // Check and update "extra" state.
        handle_extra(&mut allocation.extra, prov_extra, offset)?;
        self.allocations.set(id.0, allocation);

        // Slice into the contents, and copy them to a new list.
        ret(allocation.data.subslice_with_length(offset.bytes(), len.bytes()))
    }
}
```

The memory leak check checks if there are any heap allocations left.
Stack allocations are fine; they get automatically cleaned up when a function returns and when the start function calls `exit`, its locals are still around.

```rust
impl<T: Target, ProvExtra, AllocExtra> BasicMemory<T, ProvExtra, AllocExtra> {
    fn leak_check(&self) -> Result {
        use AllocationKind::*;
        for allocation in self.allocations {
            if allocation.live {
                match allocation.kind {
                    // These should all be gone.
                    Heap => throw_memory_leak!(),
                    // These we can still have at the end.
                    Global | Function | Stack | VTable => {}
                }
            }
        }
        ret(())
    }
}
```

## Implementing the interface

The interface is now implemented fairly easily by forwarding to the operations declared above.

```rust
impl<T: Target> Memory for BasicMemory<T> {
    type Provenance = Provenance<()>;

    /// The target is given by the generic parameter.
    type T = T;

    /// The basic memory model does not need any per-frame data,
    /// so we set `FrameExtra` to the unit type.
    type FrameExtra = ();
    /// The basic memory model does not have any configuration parameters.
    type Params = ();

    fn new(_params: ()) -> Self {
        Self::new()
    }

    fn allocate(&mut self, kind: AllocationKind, size: Size, align: Align) -> NdResult<ThinPointer<Self::Provenance>> {
        self.allocate(kind, size, align, (), ())
    }

    fn deallocate(&mut self, ptr: ThinPointer<Self::Provenance>, kind: AllocationKind, size: Size, align: Align) -> Result {
        self.deallocate(ptr, kind, size, align, |(), ()| ret(()))
    }

    fn store(&mut self, ptr: ThinPointer<Self::Provenance>, bytes: List<AbstractByte<Self::Provenance>>, align: Align) -> Result {
        self.store(ptr, bytes, align, |(), (), _offset| ret(()))
    }

    fn load(&mut self, ptr: ThinPointer<Self::Provenance>, len: Size, align: Align) -> Result<List<AbstractByte<Self::Provenance>>> {
        self.load(ptr, len, align, |(), (), _offset| ret(()))
    }

    fn dereferenceable(&self, ptr: ThinPointer<Self::Provenance>, len: Size) -> Result {
        self.check_ptr(ptr, len)?;
        ret(())
    }

    fn new_call() -> Self::FrameExtra {
        ()
    }

    fn leak_check(&self) -> Result {
        self.leak_check()
    }
}
```
