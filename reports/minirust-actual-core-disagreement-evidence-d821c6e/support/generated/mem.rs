#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct IntPtrCast<Provenance: libspecr::hidden::Obj> {
    /// The set of exposed provenance.
    exposed: Set<Provenance>,
}
impl<Provenance: libspecr::hidden::Obj> IntPtrCast<Provenance> {
    pub fn new() -> Self {
        Self { exposed: Set::new() }
    }
    pub fn expose(&mut self, ptr: ThinPointer<Provenance>) {
        if let Some(provenance) = ptr.provenance {
            self.exposed.insert(provenance);
        }
    }
    pub fn int2ptr(&self, addr: Int) -> NdResult<ThinPointer<Provenance>> {
        let provenance = predict(|prov: Option<Provenance>| {
            prov.map_or(true, |p| self.exposed.contains(p))
        })?;
        ret(ThinPointer { addr, provenance })
    }
}
use crate::prelude::*;
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct AllocId(Int);
type Provenance<Extra> = (AllocId, Extra);
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
struct Allocation<
    ProvExtra: libspecr::hidden::Obj = (),
    AllocExtra: libspecr::hidden::Obj = (),
> {
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
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct BasicMemory<
    T: Target + libspecr::hidden::Obj,
    ProvExtra: libspecr::hidden::Obj = (),
    AllocExtra: libspecr::hidden::Obj = (),
> {
    allocations: List<Allocation<ProvExtra, AllocExtra>>,
    _phantom: std::marker::PhantomData<T>,
}
impl<
    T: Target + libspecr::hidden::Obj,
    ProvExtra: libspecr::hidden::Obj,
    AllocExtra: libspecr::hidden::Obj,
> BasicMemory<T, ProvExtra, AllocExtra> {
    fn new() -> Self {
        Self {
            allocations: List::new(),
            _phantom: std::marker::PhantomData,
        }
    }
    fn allocate(
        &mut self,
        kind: AllocationKind,
        size: Size,
        align: Align,
        prov_extra: ProvExtra,
        alloc_extra: AllocExtra,
    ) -> NdResult<ThinPointer<Provenance<ProvExtra>>> {
        if !T::valid_size(size) {
            throw_ub!("asking for a too large allocation");
        }
        let distr = libspecr::IntDistribution {
            start: Int::ONE,
            end: Int::from(2).pow(T::PTR_SIZE.bits()),
            divisor: align.bytes(),
        };
        let addr = pick(
            distr,
            |addr: Address| {
                if addr <= 0 {
                    return false;
                }
                if !align.is_aligned(addr) {
                    return false;
                }
                if !(addr + size.bytes()).in_bounds(Unsigned, T::PTR_SIZE) {
                    return false;
                }
                if self.allocations.any(|a| a.live && a.overlaps(addr, size)) {
                    return false;
                }
                true
            },
        )?;
        let allocation = Allocation {
            addr,
            align,
            kind,
            live: true,
            data: list![AbstractByte::Uninit; size.bytes()],
            extra: alloc_extra,
        };
        let id = AllocId(self.allocations.len());
        self.allocations.push(allocation);
        ret(ThinPointer {
            addr,
            provenance: Some((id, prov_extra)),
        })
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
        let mut allocation = (self.allocations).index_at(id.0);
        if !allocation.live {
            throw_ub!("double-free");
        }
        if ptr.addr != allocation.addr {
            throw_ub!(
                "deallocating with pointer not to the beginning of its allocation"
            );
        }
        if kind != allocation.kind {
            throw_ub!(
                "deallocating {:?} memory with {:?} deallocation operation", allocation
                .kind, kind
            );
        }
        if size != allocation.size() {
            throw_ub!("deallocating with incorrect size information");
        }
        if align != allocation.align {
            throw_ub!("deallocating with incorrect alignment information");
        }
        handle_extra(&mut allocation.extra, prov_extra)?;
        allocation.live = false;
        self.allocations.set(id.0, allocation);
        ret(())
    }
    /// Check if the given pointer is dereferenceable for an access of the given
    /// length. For dereferenceable, return the allocation ID and
    /// offset; this can be missing for invalid pointers and accesses of size 0.
    fn check_ptr(
        &self,
        ptr: ThinPointer<Provenance<ProvExtra>>,
        len: Size,
    ) -> Result<Option<(AllocId, ProvExtra, Size)>> {
        if len.is_zero() {
            return ret(None);
        }
        let Some((id, prov_extra)) = ptr.provenance else {
            throw_ub!("dereferencing pointer without provenance");
        };
        let allocation = (self.allocations).index_at(id.0);
        if !allocation.live {
            throw_ub!("dereferencing pointer to dead allocation");
        }
        let offset_in_alloc = ptr.addr - allocation.addr;
        if offset_in_alloc < 0
            || offset_in_alloc + len.bytes() > allocation.size().bytes()
        {
            throw_ub!("dereferencing pointer outside the bounds of its allocation");
        }
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
        let mut allocation = (self.allocations).index_at(id.0);
        handle_extra(&mut allocation.extra, prov_extra, offset)?;
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
        let mut allocation = (self.allocations).index_at(id.0);
        handle_extra(&mut allocation.extra, prov_extra, offset)?;
        self.allocations.set(id.0, allocation);
        ret(allocation.data.subslice_with_length(offset.bytes(), len.bytes()))
    }
    fn leak_check(&self) -> Result {
        use AllocationKind::*;
        for allocation in self.allocations {
            if allocation.live {
                match allocation.kind {
                    Heap => throw_memory_leak!(),
                    Global | Function | Stack | VTable => {}
                }
            }
        }
        ret(())
    }
}
impl<
    ProvExtra: libspecr::hidden::Obj,
    AllocExtra: libspecr::hidden::Obj,
> Allocation<ProvExtra, AllocExtra> {
    fn size(self) -> Size {
        Size::from_bytes(self.data.len()).unwrap()
    }
    fn overlaps(self, other_addr: Address, other_size: Size) -> bool {
        let end_addr = self.addr + self.size().bytes();
        let other_end_addr = other_addr + other_size.bytes();
        if end_addr <= other_addr || other_end_addr <= self.addr {
            self.addr == other_addr
        } else {
            true
        }
    }
}
impl<
    T: Target + libspecr::hidden::Obj + for<'de> serde::Deserialize<'de>
        + serde::Serialize,
> Memory for BasicMemory<T> {
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
    fn allocate(
        &mut self,
        kind: AllocationKind,
        size: Size,
        align: Align,
    ) -> NdResult<ThinPointer<Self::Provenance>> {
        self.allocate(kind, size, align, (), ())
    }
    fn deallocate(
        &mut self,
        ptr: ThinPointer<Self::Provenance>,
        kind: AllocationKind,
        size: Size,
        align: Align,
    ) -> Result {
        self.deallocate(ptr, kind, size, align, |(), ()| ret(()))
    }
    fn store(
        &mut self,
        ptr: ThinPointer<Self::Provenance>,
        bytes: List<AbstractByte<Self::Provenance>>,
        align: Align,
    ) -> Result {
        self.store(ptr, bytes, align, |(), (), _offset| ret(()))
    }
    fn load(
        &mut self,
        ptr: ThinPointer<Self::Provenance>,
        len: Size,
        align: Align,
    ) -> Result<List<AbstractByte<Self::Provenance>>> {
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
/// An "address" is a location in memory. This corresponds to the actual
/// location in the real program.
/// We make it a mathematical integer, but of course it is bounded by the size
/// of the address space.
pub type Address = Int;
/// A "thin pointer" is an address together with its Provenance.
/// Provenance can be absent; those pointers are
/// invalid for all non-zero-sized accesses.
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct ThinPointer<Provenance: libspecr::hidden::Obj> {
    pub addr: Address,
    pub provenance: Option<Provenance>,
}
/// The runtime metadata that can be stored in a wide pointer.
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub enum PointerMeta<Provenance: libspecr::hidden::Obj> {
    /// The metadata counts the number of elements in the slice.
    ElementCount(Int),
    /// The metadata points to a vtable referred at this location.
    /// This must point to a valid vtable and it is a spec bug if it doesn't.
    VTablePointer(ThinPointer<Provenance>),
}
/// A "pointer" is the thin pointer with optionally some metadata, making it a wide pointer.
/// This corresponds to the Rust raw pointer types, as well as references and boxes.
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct Pointer<Provenance: libspecr::hidden::Obj> {
    pub thin_pointer: ThinPointer<Provenance>,
    pub metadata: Option<PointerMeta<Provenance>>,
}
impl<Provenance: libspecr::hidden::Obj> ThinPointer<Provenance> {
    /// Offsets a pointer in bytes using wrapping arithmetic.
    /// This does not check whether the pointer is still in-bounds of its allocation.
    pub fn wrapping_offset<T: Target + libspecr::hidden::Obj>(
        self,
        offset: Int,
    ) -> Self {
        let addr = self.addr + offset;
        let addr = addr.bring_in_bounds(Unsigned, T::PTR_SIZE);
        ThinPointer { addr, ..self }
    }
    pub fn widen(
        self,
        metadata: Option<PointerMeta<Provenance>>,
    ) -> Pointer<Provenance> {
        Pointer {
            thin_pointer: self,
            metadata,
        }
    }
}
/// Describes what is needed to define the layout of the sized head of a tuple `(head.., tail)`.
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct TupleHeadLayout {
    /// The offset where the head ends and tail starts.
    /// This is the end of the last sized field; it is *not* necessarily aligned to `align`.
    pub end: Offset,
    /// The alignment of the head. This is the maximal alignment of any sized field and capped to the packed alignment.
    pub align: Align,
    /// If this is `Some(a)` the alignment of the tail will be capped at this value.
    /// Must be `None` for sized tuples.
    pub packed_align: Option<Align>,
}
/// Describes how the size and align of the value can be determined.
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub enum LayoutStrategy {
    /// The type is statically `Sized` with the given size and align.
    Sized(Size, Align),
    /// The type contains zero or more elements of the inner layout.
    /// The total size is a multiple of the element size and the align is exactly the element align.
    Slice(Size, Align),
    /// The size of the type must be looked up in the VTable of a wide pointer.
    /// Additionally, the vtable must be for the given trait.
    TraitObject(TraitName),
    /// The type consists of a sized head an unsized tail.
    Tuple { head: TupleHeadLayout, tail: libspecr::hidden::GcCow<LayoutStrategy> },
}
/// Describes where in a potentially unsized type the UnsafeCell are.
/// Separate from `LayoutStrategy` since we must be able to compute `LayoutStrategy` from a
/// MiniRust `Type`, but that does not have enough information for an `UnsafeCellStrategy`.
/// FIXME: maybe it should?
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub enum UnsafeCellStrategy {
    /// List of offsets and sizes of `UnsafeCell`s.
    Sized { cells: List<(Offset, Size)> },
    /// Since the elements of a slice have the same type, we only keep track of the
    /// UnsafeCell's of one element, we can then "repeat" this for the rest of the slice.
    Slice { element_cells: List<(Offset, Size)> },
    /// The bytes for UnsafeCell's must be looked up in the VTable.
    TraitObject,
    /// A Tuple consists of a sized head an unsized tail.
    Tuple {
        head_cells: List<(Offset, Size)>,
        tail_cells: libspecr::hidden::GcCow<UnsafeCellStrategy>,
    },
}
/// Describes what we know about data behind a pointer.
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct PointeeInfo {
    pub layout: LayoutStrategy,
    pub inhabited: bool,
    /// Indicates where the `UnsafeCell` in this type are, which permit interior mutability.
    pub unsafe_cells: UnsafeCellStrategy,
    /// Whether the pointee implements the `Freeze` trait. This is used to determine
    /// whether the bytes "outside" the pointee have interior mutability.
    pub freeze: bool,
    pub unpin: bool,
}
/// A "trait name" is an identifier for the trait a vtable is for.
/// This depends on the defined methods and the marker traits.
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct TraitName(pub libspecr::Name);
/// The statically known kind of metadata stored in a pointer.
/// This determines the type of the metadata, while `Option<PointerMeta>` determines its value.
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub enum PointerMetaKind {
    None,
    ElementCount,
    VTablePointer(TraitName),
}
/// Stores all the information that we need to know about a pointer.
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub enum PtrType {
    Ref {
        /// Indicates a shared vs mutable reference.
        mutbl: Mutability,
        /// Describes what we know about the pointee.
        pointee: PointeeInfo,
    },
    Box { pointee: PointeeInfo },
    Raw {
        /// Indicates what kind of metadata this pointer carries.
        meta_kind: PointerMetaKind,
    },
    FnPtr,
    /// This is a "stand-alone" vtable pointer, something that does not exist in surface Rust.
    VTablePtr(TraitName),
}
impl PtrType {
    /// If this is a safe pointer, return the pointee information.
    pub fn safe_pointee(self) -> Option<PointeeInfo> {
        match self {
            PtrType::Ref { pointee, .. } | PtrType::Box { pointee, .. } => Some(pointee),
            PtrType::Raw { .. } | PtrType::FnPtr | PtrType::VTablePtr(_) => None,
        }
    }
    pub fn meta_kind(self) -> PointerMetaKind {
        match self {
            PtrType::Ref { pointee, .. } | PtrType::Box { pointee, .. } => {
                pointee.layout.meta_kind()
            }
            PtrType::Raw { meta_kind, .. } => meta_kind,
            PtrType::FnPtr | PtrType::VTablePtr(_) => PointerMetaKind::None,
        }
    }
}
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct ConcurrentMemory<M: Memory + libspecr::hidden::Obj> {
    memory: M,
    /// List of all memory access done by the active thread in the current step.
    accesses: List<Access>,
}
/// The different kinds of atomicity.
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub enum Atomicity {
    /// A sequentially consistent atomic access.
    Atomic,
    /// A non-atomic memory access.
    None,
}
/// Internal type used to track the type of a memory access.
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
enum AccessType {
    Store,
    Load,
}
/// Access contains all information the data race detection needs about a single access.
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct Access {
    ty: AccessType,
    atomicity: Atomicity,
    addr: Address,
    len: Size,
}
impl<M: Memory + libspecr::hidden::Obj> ConcurrentMemory<M> {
    pub fn new(params: M::Params) -> Self {
        Self {
            memory: M::new(params),
            accesses: list![],
        }
    }
    /// Create a new allocation.
    /// The initial contents of the allocation are `AbstractByte::Uninit`.
    pub fn allocate(
        &mut self,
        kind: AllocationKind,
        size: Size,
        align: Align,
    ) -> NdResult<ThinPointer<M::Provenance>> {
        self.memory.allocate(kind, size, align)
    }
    /// Remove an allocation.
    pub fn deallocate(
        &mut self,
        ptr: ThinPointer<M::Provenance>,
        kind: AllocationKind,
        size: Size,
        align: Align,
    ) -> Result {
        self.memory.deallocate(ptr, kind, size, align)
    }
    /// Write some bytes to memory and check for data races.
    pub fn store(
        &mut self,
        ptr: ThinPointer<M::Provenance>,
        bytes: List<AbstractByte<M::Provenance>>,
        align: Align,
        atomicity: Atomicity,
    ) -> Result {
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
    pub fn load(
        &mut self,
        ptr: ThinPointer<M::Provenance>,
        len: Size,
        align: Align,
        atomicity: Atomicity,
    ) -> Result<List<AbstractByte<M::Provenance>>> {
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
    pub fn signed_dereferenceable(
        &self,
        ptr: ThinPointer<M::Provenance>,
        len: Int,
    ) -> Result {
        self.memory.signed_dereferenceable(ptr, len)
    }
    /// Return the retagged pointer.
    pub fn retag_ptr(
        &mut self,
        frame_extra: &mut M::FrameExtra,
        ptr: Pointer<M::Provenance>,
        ptr_type: PtrType,
        fn_entry: bool,
        fn_implicit_writes: bool,
        vtable_lookup: impl Fn(
            ThinPointer<M::Provenance>,
        ) -> crate::lang::VTable + 'static,
    ) -> Result<Pointer<M::Provenance>> {
        self.memory
            .retag_ptr(
                frame_extra,
                ptr,
                ptr_type,
                fn_entry,
                fn_implicit_writes,
                vtable_lookup,
            )
    }
    /// Memory model hook invoked at the end of each function call.
    pub fn end_call(&mut self, extra: M::FrameExtra) -> Result {
        self.memory.end_call(extra)
    }
    /// Check if there are any memory leaks.
    pub fn leak_check(&self) -> Result {
        self.memory.leak_check()
    }
    /// Given a list of previous accesses, checks if any of the current accesses is in a data race with any of those.
    pub fn check_data_races(
        &self,
        current_thread: ThreadId,
        (prev_sync_threads, prev_accesses): (Set<ThreadId>, List<Access>),
    ) -> Result {
        if prev_sync_threads.contains(current_thread) {
            return Ok(());
        }
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
/// The ID of a thread is an index into the machine's `threads` list.
pub type ThreadId = Int;
impl Access {
    /// Indicates if a races happend between the two given accesses.
    /// We assume they happen on different threads.
    fn races(self, other: Self) -> bool {
        if self.ty == AccessType::Load && other.ty == AccessType::Load {
            return false;
        }
        if self.atomicity == Atomicity::Atomic && other.atomicity == Atomicity::Atomic {
            return false;
        }
        let end_addr = self.addr + self.len.bytes();
        let other_end_addr = other.addr + other.len.bytes();
        end_addr > other.addr && other_end_addr > self.addr
    }
}
/// A one-byte provenance fragment stores the provenance and which position
/// in the pointer this fragment had.
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct ProvenanceFrag<Provenance: libspecr::hidden::Obj> {
    pub provenance: Provenance,
    pub position: Int,
}
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub enum AbstractByte<Provenance: libspecr::hidden::Obj> {
    /// An uninitialized byte.
    Uninit,
    /// An initialized byte, optionally with some provenance (if it is encoding a pointer).
    Init(u8, Option<ProvenanceFrag<Provenance>>),
}
impl<Provenance: libspecr::hidden::Obj> AbstractByte<Provenance> {
    pub fn data(self) -> Option<u8> {
        match self {
            AbstractByte::Uninit => None,
            AbstractByte::Init(data, _) => Some(data),
        }
    }
    pub fn provenance_frag(self) -> Option<ProvenanceFrag<Provenance>> {
        match self {
            AbstractByte::Uninit => None,
            AbstractByte::Init(_, frag) => frag,
        }
    }
}
/// The "kind" of an allocation is used to distinguish, for instance, stack from heap memory.
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub enum AllocationKind {
    /// Memory for a stack variable.
    Stack,
    /// Memory allocated with the AM heap intrinsics.
    Heap,
    /// Memory for a global variable.
    Global,
    /// Memory for a function.
    Function,
    /// Memory for a vtable.
    VTable,
}
/// *Note*: All memory operations can be non-deterministic, which means that
/// executing the same operation on the same memory can have different results.
/// We also let read operations potentially mutate memory (they actually can
/// change the current state in concurrent memory models and in Stacked Borrows).
pub trait Memory: libspecr::hidden::Obj {
    /// The target information.
    /// This doesn't really belong to the memory, but avoids having to quantify over both
    /// memory and target everywhere.
    type T: Target
        + libspecr::hidden::Obj
        + for<'de> serde::Deserialize<'de>
        + serde::Serialize;
    /// The type of pointer provenance.
    type Provenance: libspecr::hidden::Obj
        + for<'de> serde::Deserialize<'de>
        + serde::Serialize;
    /// Extra information for each stack frame.
    type FrameExtra: libspecr::hidden::Obj
        + for<'de> serde::Deserialize<'de>
        + serde::Serialize;
    /// Parameters controlling memory model behavior, passed at construction time.
    type Params: Default
        + libspecr::hidden::Obj
        + for<'de> serde::Deserialize<'de>
        + serde::Serialize;
    /// Create a new instance of the memory model with the given parameters.
    fn new(params: Self::Params) -> Self;
    /// Create a new allocation.
    /// The initial contents of the allocation are `AbstractByte::Uninit`.
    ///
    /// This is the only non-deterministic operation in the memory interface.
    fn allocate(
        &mut self,
        kind: AllocationKind,
        size: Size,
        align: Align,
    ) -> NdResult<ThinPointer<Self::Provenance>>;
    /// Remove an allocation.
    fn deallocate(
        &mut self,
        ptr: ThinPointer<Self::Provenance>,
        kind: AllocationKind,
        size: Size,
        align: Align,
    ) -> Result;
    /// Write some bytes to memory.
    fn store(
        &mut self,
        ptr: ThinPointer<Self::Provenance>,
        bytes: List<AbstractByte<Self::Provenance>>,
        align: Align,
    ) -> Result;
    /// Read some bytes from memory.
    ///
    /// Needs `&mut self` because in the aliasing model, reading changes the machine state.
    fn load(
        &mut self,
        ptr: ThinPointer<Self::Provenance>,
        len: Size,
        align: Align,
    ) -> Result<List<AbstractByte<Self::Provenance>>>;
    /// Test whether the given pointer is dereferenceable for the given size.
    fn dereferenceable(&self, ptr: ThinPointer<Self::Provenance>, len: Size) -> Result;
    /// A derived form of `dereferenceable` that works with a signed notion of "length".
    fn signed_dereferenceable(
        &self,
        ptr: ThinPointer<Self::Provenance>,
        len: Int,
    ) -> Result {
        if len > 0 {
            self.dereferenceable(ptr, Size::from_bytes(len).unwrap())
        } else {
            let begin_ptr = ThinPointer {
                addr: ptr.addr + len,
                ..ptr
            };
            self.dereferenceable(begin_ptr, Size::from_bytes(-len).unwrap())
        }
    }
    /// Retag the given pointer, which has the given type.
    /// `fn_entry` indicates whether this is one of the special retags that happen
    /// right at the top of each function.
    ///
    /// This can assume the pointer satisfies the language invariant,
    /// in particular, it must be `dereferenceable` for its size.
    /// Violating this or breaking this for the return value is a spec bug.
    ///
    /// The `vtable_lookup` is given, since computing the size and UnsafeCell positions
    /// requires information about vtables.
    ///
    /// Return the retagged pointer.
    fn retag_ptr(
        &mut self,
        _frame_extra: &mut Self::FrameExtra,
        ptr: Pointer<Self::Provenance>,
        _ptr_type: PtrType,
        _fn_entry: bool,
        _fn_implicit_writes: bool,
        _vtable_lookup: impl Fn(
            ThinPointer<Self::Provenance>,
        ) -> crate::lang::VTable + 'static,
    ) -> Result<Pointer<Self::Provenance>> {
        ret(ptr)
    }
    /// Create the extra information for a stack frame.
    fn new_call() -> Self::FrameExtra;
    /// Memory model hook invoked at the end of each function call.
    fn end_call(&mut self, _extra: Self::FrameExtra) -> Result {
        ret(())
    }
    /// Check if there are any memory leaks.
    fn leak_check(&self) -> Result;
}
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
struct ReborrowSettings {
    /// The permissions to set "inside" the data the reference points to (indexed
    /// related to the reference).
    inside: List<Permission>,
    /// The permission to set for the "outside" part.
    outside: Permission,
    /// Whether and which protector to set.
    protected: Protected,
}
/// Converts a list of cell locations into a "freeze mask",
/// where each `bool` indicates whether the byte is frozen (i.e., *outside* all cells).
fn cells_to_freeze_mask(cells: List<(Offset, Size)>, size: Size) -> List<bool> {
    let padded_front = std::iter::once((Offset::ZERO, Size::ZERO)).chain(cells.iter());
    let padded_back = cells.iter().chain(std::iter::once((size, Size::ZERO)));
    let mut mask = List::new();
    for (current, next) in padded_front.zip(padded_back) {
        mask.append(list![false; current.1.bytes()]);
        let no_cell_size = next.0.bytes() - (current.0 + current.1).bytes();
        mask.append(list![true; no_cell_size]);
    }
    assert!(mask.len() == size.bytes());
    mask
}
impl UnsafeCellStrategy {
    /// Converts a list of cell locations into a cell "mask",
    /// where each `bool` indicates whether the byte is inside a cell.
    fn freeze_mask(
        self,
        layout: LayoutStrategy,
        ptr_metadata: Option<PointerMeta<TreeBorrowsProvenance>>,
        vtable_lookup: impl Fn(
            ThinPointer<TreeBorrowsProvenance>,
        ) -> crate::lang::VTable + 'static,
    ) -> List<bool> {
        match (self, layout, ptr_metadata) {
            (
                UnsafeCellStrategy::Sized { cells },
                LayoutStrategy::Sized(size, _align),
                ..,
            ) => cells_to_freeze_mask(cells, size),
            (
                UnsafeCellStrategy::Slice { element_cells },
                LayoutStrategy::Slice(size, _align),
                Some(PointerMeta::ElementCount(count)),
            ) => {
                let element_mask = cells_to_freeze_mask(element_cells, size);
                let mut mask = List::new();
                for _ in Int::ZERO..count {
                    mask.append(element_mask);
                }
                mask
            }
            (
                UnsafeCellStrategy::TraitObject,
                LayoutStrategy::TraitObject(_trait_name),
                Some(PointerMeta::VTablePointer(ptr)),
            ) => {
                let vtable = vtable_lookup(ptr);
                cells_to_freeze_mask(vtable.cells, vtable.size)
            }
            (
                UnsafeCellStrategy::Tuple { head_cells, tail_cells },
                LayoutStrategy::Tuple { head, tail },
                _,
            ) => {
                let tail_cells = tail_cells.extract();
                let tail = tail.extract();
                {
                    let mut mask = cells_to_freeze_mask(head_cells, head.end);
                    mask.append(
                        tail_cells.freeze_mask(tail, ptr_metadata, vtable_lookup),
                    );
                    mask
                }
            }
            _ => panic!("Invalid LayoutStrategy and PointerMeta combination"),
        }
    }
}
impl ReborrowSettings {
    /// Compute the permissions to be assigned when retagging the given pointer.
    /// `None` indicates that no retagging should happen.
    fn new(
        ptr: Pointer<TreeBorrowsProvenance>,
        ptr_type: PtrType,
        fn_entry: bool,
        params: TreeBorrowsParams,
        fn_implicit_writes: bool,
        vtable_lookup: impl Fn(
            ThinPointer<TreeBorrowsProvenance>,
        ) -> crate::lang::VTable + 'static,
    ) -> Option<Self> {
        let Some(pointee_info) = ptr_type.safe_pointee() else {
            return None;
        };
        if matches!(
            ptr_type, PtrType::Ref { mutbl : Mutability::Mutable, pointee } |
            PtrType::Box { pointee } if ! pointee.unpin
        ) {
            return None;
        }
        let protected = if fn_entry {
            match ptr_type {
                PtrType::Box { .. } => Protected::Weak,
                _ => Protected::Strong,
            }
        } else {
            Protected::No
        };
        let implicit_writes_enabled = protected.yes() && params.implicit_writes
            && fn_implicit_writes;
        let perm = |inside: bool, frozen: bool| {
            let mk_perm = |unprot, prot| {
                if protected.yes() {
                    Permission::Prot(prot)
                } else {
                    Permission::Unprot(unprot)
                }
            };
            match ptr_type {
                PtrType::Ref { mutbl: Mutability::Immutable, .. } => {
                    if frozen {
                        mk_perm(
                            PermissionUnprot::Frozen,
                            PermissionProt::Frozen {
                                had_local_read: false,
                            },
                        )
                    } else {
                        mk_perm(PermissionUnprot::Cell, PermissionProt::Cell)
                    }
                }
                PtrType::Ref { mutbl: Mutability::Mutable, .. } | PtrType::Box { .. } => {
                    if implicit_writes_enabled && inside {
                        assert!(protected.yes());
                        Permission::Prot(PermissionProt::Unique)
                    } else {
                        mk_perm(
                            if frozen {
                                PermissionUnprot::Reserved
                            } else {
                                PermissionUnprot::ReservedIm
                            },
                            PermissionProt::Reserved {
                                had_local_read: false,
                                had_foreign_read: false,
                            },
                        )
                    }
                }
                PtrType::Raw { .. } | PtrType::FnPtr | PtrType::VTablePtr(_) => {
                    unreachable!(
                        "safe_pointee() returns None for Raw, FnPtr, and VTablePtr; should have returned early on function entry"
                    )
                }
            }
        };
        let inside = pointee_info
            .unsafe_cells
            .freeze_mask(pointee_info.layout, ptr.metadata, vtable_lookup)
            .map(|freeze| perm(true, freeze));
        let outside = perm(false, pointee_info.freeze);
        Some(ReborrowSettings {
            protected,
            inside,
            outside,
        })
    }
}
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
enum PermissionProt {
    /// Represents a shared reference to interior mutable data.
    Cell,
    /// The various flavours of `Reserved` correspond to a protected/noalias node where no writes happened yet.
    Reserved { had_local_read: bool, had_foreign_read: bool },
    /// Represents an activated (written to) mutable reference, i.e. it must actually be unique right now.
    Unique,
    /// Represents a shared (immutable) reference.
    Frozen { had_local_read: bool },
    /// Represents a reference that experienced a foreign write. It can not be used locally anymore.
    Disabled,
}
impl PermissionProt {
    fn local_read(self) -> Result<PermissionProt> {
        match self {
            PermissionProt::Cell => ret(PermissionProt::Cell),
            PermissionProt::Reserved { had_foreign_read, .. } => {
                ret(PermissionProt::Reserved {
                    had_local_read: true,
                    had_foreign_read,
                })
            }
            PermissionProt::Unique => ret(PermissionProt::Unique),
            PermissionProt::Frozen { .. } => {
                ret(PermissionProt::Frozen {
                    had_local_read: true,
                })
            }
            PermissionProt::Disabled => {
                throw_ub!("Tree Borrows: local read of protected Disabled reference")
            }
        }
    }
    fn local_write(self) -> Result<PermissionProt> {
        match self {
            PermissionProt::Cell => ret(PermissionProt::Cell),
            PermissionProt::Unique => ret(PermissionProt::Unique),
            PermissionProt::Reserved { had_foreign_read: false, .. } => {
                ret(PermissionProt::Unique)
            }
            PermissionProt::Reserved { had_foreign_read: true, .. } => {
                throw_ub!(
                    "Tree Borrows: local write to protected Reserved reference that had a foreign read"
                )
            }
            PermissionProt::Frozen { .. } => {
                throw_ub!("Tree Borrows: local write to protected Frozen reference")
            }
            PermissionProt::Disabled => {
                throw_ub!("Tree Borrows: local write to protected Disabled reference")
            }
        }
    }
    fn foreign_read(self) -> Result<PermissionProt> {
        match self {
            PermissionProt::Cell => ret(PermissionProt::Cell),
            PermissionProt::Unique => {
                throw_ub!("Tree Borrows: foreign read of protected Unique reference")
            }
            PermissionProt::Reserved { had_local_read, .. } => {
                ret(PermissionProt::Reserved {
                    had_local_read,
                    had_foreign_read: true,
                })
            }
            PermissionProt::Frozen { had_local_read } => {
                ret(PermissionProt::Frozen {
                    had_local_read,
                })
            }
            PermissionProt::Disabled => ret(PermissionProt::Disabled),
        }
    }
    fn foreign_write(self) -> Result<PermissionProt> {
        match self {
            PermissionProt::Cell => ret(PermissionProt::Cell),
            PermissionProt::Frozen { had_local_read: true }
            | PermissionProt::Reserved { had_local_read: true, .. } => {
                throw_ub!(
                    "Tree Borrows: foreign write of protected {} reference which had a local read",
                    if matches!(self, PermissionProt::Frozen { .. }) { "Frozen" } else {
                    "Reserved" }
                )
            }
            PermissionProt::Unique => {
                throw_ub!("Tree Borrows: foreign read of protected Unique reference")
            }
            PermissionProt::Frozen { had_local_read: false }
            | PermissionProt::Reserved { had_local_read: false, .. } => {
                ret(PermissionProt::Disabled)
            }
            PermissionProt::Disabled => ret(PermissionProt::Disabled),
        }
    }
    fn transition(
        self,
        access_kind: AccessKind,
        node_relation: NodeRelation,
    ) -> Result<PermissionProt> {
        match (node_relation, access_kind) {
            (NodeRelation::Local, AccessKind::Read) => self.local_read(),
            (NodeRelation::Local, AccessKind::Write) => self.local_write(),
            (NodeRelation::Foreign, AccessKind::Read) => self.foreign_read(),
            (NodeRelation::Foreign, AccessKind::Write) => self.foreign_write(),
        }
    }
    fn init_access(self) -> Option<AccessKind> {
        match self {
            PermissionProt::Cell => None,
            PermissionProt::Unique => Some(AccessKind::Write),
            _ => Some(AccessKind::Read),
        }
    }
    /// When a protector is released, we transition to the unprotected state machine.
    /// Additionally, we might emit a _protector end access_, depending on our current state.
    /// The second state indicates that access, or is `None` when no access should happen.
    fn unprotect(self) -> (PermissionUnprot, Option<AccessKind>) {
        match self {
            PermissionProt::Unique => (PermissionUnprot::Unique, Some(AccessKind::Write)),
            PermissionProt::Reserved { had_local_read: true, .. } => {
                (PermissionUnprot::Reserved, Some(AccessKind::Read))
            }
            PermissionProt::Reserved { had_local_read: false, .. } => {
                (PermissionUnprot::Reserved, None)
            }
            PermissionProt::Frozen { had_local_read: true } => {
                (PermissionUnprot::Frozen, Some(AccessKind::Read))
            }
            PermissionProt::Frozen { had_local_read: false } => {
                (PermissionUnprot::Frozen, None)
            }
            PermissionProt::Disabled => (PermissionUnprot::Disabled, None),
            PermissionProt::Cell => (PermissionUnprot::Cell, None),
        }
    }
    /// Strongly protected nodes can block deallocation, based on their permission.
    /// Specifically, they block allocation iff they would cause UB on a foreign write,
    /// that is, if they have been locally accessed ("used"), with an exception for `Cell`.
    /// The check for whether the protector is actually strong happens elsewhere.
    fn prevents_deallocation(&self) -> bool {
        match self {
            PermissionProt::Unique => true,
            PermissionProt::Reserved { had_local_read, .. }
            | PermissionProt::Frozen { had_local_read } => *had_local_read,
            PermissionProt::Disabled => false,
            PermissionProt::Cell => false,
        }
    }
}
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
enum PermissionUnprot {
    /// Represents a shared reference to interior mutable data.
    Cell,
    /// Represents a two-phase borrow during its reservation phase
    Reserved,
    /// Represents a interior mutable two-phase borrow during its reservation phase
    ReservedIm,
    /// Represents an activated (written to) mutable reference, i.e. it must actually be unique right now
    Unique,
    /// Represents a shared (immutable) reference
    Frozen,
    /// Represents a dead reference
    Disabled,
}
impl PermissionUnprot {
    fn local_read(self) -> Result<PermissionUnprot> {
        ret(
            match self {
                PermissionUnprot::Disabled => {
                    throw_ub!("Tree Borrows: local read of Disabled reference")
                }
                perm => perm,
            },
        )
    }
    fn local_write(self) -> Result<PermissionUnprot> {
        match self {
            PermissionUnprot::Frozen => {
                throw_ub!("Tree Borrows: local write of Frozen reference")
            }
            PermissionUnprot::Disabled => {
                throw_ub!("Tree Borrows: local write of Disabled reference")
            }
            PermissionUnprot::Cell => ret(PermissionUnprot::Cell),
            _ => ret(PermissionUnprot::Unique),
        }
    }
    fn foreign_read(self) -> Result<PermissionUnprot> {
        match self {
            PermissionUnprot::Reserved => ret(PermissionUnprot::Reserved),
            PermissionUnprot::Unique => ret(PermissionUnprot::Frozen),
            perm => ret(perm),
        }
    }
    fn foreign_write(self) -> Result<PermissionUnprot> {
        match self {
            PermissionUnprot::Cell => ret(PermissionUnprot::Cell),
            PermissionUnprot::ReservedIm => ret(PermissionUnprot::ReservedIm),
            _ => ret(PermissionUnprot::Disabled),
        }
    }
    fn transition(
        self,
        access_kind: AccessKind,
        node_relation: NodeRelation,
    ) -> Result<PermissionUnprot> {
        match (node_relation, access_kind) {
            (NodeRelation::Local, AccessKind::Read) => self.local_read(),
            (NodeRelation::Local, AccessKind::Write) => self.local_write(),
            (NodeRelation::Foreign, AccessKind::Read) => self.foreign_read(),
            (NodeRelation::Foreign, AccessKind::Write) => self.foreign_write(),
        }
    }
    /// Strongly protected nodes can block deallocation, based on their permission.
    /// This method is never called because we first check whether there is a strong protector,
    /// but it is here anyways for consistency.
    fn prevents_deallocation(&self) -> bool {
        false
    }
    fn init_access(self) -> Option<AccessKind> {
        match self {
            PermissionUnprot::Cell => None,
            _ => Some(AccessKind::Read),
        }
    }
}
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
struct TreeBorrowsAllocationExtra {
    root: Node,
}
/// The index of a child in the list of child nodes.
type ChildId = Int;
/// A path from the root of a tree to some node inside the tree.
type Path = List<ChildId>;
type TreeBorrowsProvenance = (AllocId, Path);
/// Global parameters controlling Tree Borrows behavior.
#[derive(Default)]
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct TreeBorrowsParams {
    /// Whether implicit writes are enabled or not.
    pub implicit_writes: bool,
}
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct TreeBorrowsMemory<T: Target + libspecr::hidden::Obj> {
    params: TreeBorrowsParams,
    mem: BasicMemory<T, Path, TreeBorrowsAllocationExtra>,
}
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct TreeBorrowsFrameExtra {
    /// Our per-frame state is the list of nodes that are protected by this call.
    protectors: List<TreeBorrowsProvenance>,
}
impl TreeBorrowsFrameExtra {
    fn new() -> Self {
        Self { protectors: List::new() }
    }
}
impl<T: Target + libspecr::hidden::Obj> TreeBorrowsMemory<T> {
    /// Create a new node for a pointer (reborrow)
    fn reborrow(
        &mut self,
        ptr: ThinPointer<TreeBorrowsProvenance>,
        settings: ReborrowSettings,
        frame_extra: &mut TreeBorrowsFrameExtra,
    ) -> Result<ThinPointer<TreeBorrowsProvenance>> {
        let pointee_size = Size::from_bytes(settings.inside.len()).unwrap();
        self.mem.check_ptr(ptr, pointee_size)?;
        let Some((alloc_id, parent_path)) = ptr.provenance else {
            assert!(pointee_size.is_zero());
            return ret(ptr);
        };
        let child_path = self
            .mem
            .allocations
            .mutate_at(
                alloc_id.0,
                |allocation| {
                    let alloc_size = allocation.size();
                    let offset = Offset::from_bytes(ptr.addr - allocation.addr).unwrap();
                    let mut permissions = list![settings.outside; alloc_size.bytes()];
                    if settings.inside.len() > 0 {
                        permissions
                            .write_subslice_at_index(offset.bytes(), settings.inside);
                    }
                    let child_node = Node {
                        children: List::new(),
                        permissions,
                        protected: settings.protected,
                    };
                    assert!(
                        child_node.permissions.all(| x | x.matches_protector(child_node
                        .protected))
                    );
                    let child_path = allocation
                        .extra
                        .root
                        .add_node(parent_path, child_node);
                    for (idx, perm) in settings.inside.iter().enumerate() {
                        let idx = Int::from(idx);
                        let idx = Size::from_bytes(idx).unwrap();
                        if let Some(access) = perm.init_access() {
                            allocation
                                .extra
                                .root
                                .access(
                                    Some(child_path),
                                    access,
                                    offset + idx,
                                    Offset::from_bytes_const(1),
                                )?
                        }
                    }
                    ret::<Result<Path>>(child_path)
                },
            )?;
        if settings.protected.yes() {
            frame_extra.protectors.push((alloc_id, child_path));
        }
        ret(ThinPointer {
            provenance: Some((alloc_id, child_path)),
            ..ptr
        })
    }
    /// Remove the protector.
    /// `provenance` is the provenance of the protector.
    /// Perform a special implicit access on all locations that have been accessed.
    fn release_protector(&mut self, provenance: TreeBorrowsProvenance) -> Result {
        let (alloc_id, path) = provenance;
        self.mem
            .allocations
            .mutate_at(
                alloc_id.0,
                |allocation| {
                    let protector_accesses: List<_> = allocation
                        .extra
                        .root
                        .access_node(
                            path,
                            |node| {
                                assert!(node.protected.yes());
                                let list_of_perms_and_accesses = node
                                    .permissions
                                    .map(|x| x.unprotect());
                                node.permissions = list_of_perms_and_accesses
                                    .map(|(perm, _acc)| perm);
                                list_of_perms_and_accesses.map(|(_perm, acc)| acc)
                            },
                        );
                    if !allocation.live {
                        return ret(());
                    }
                    allocation
                        .extra
                        .root
                        .release_protector(Some(path), &protector_accesses)
                },
            )
    }
}
impl<
    T: Target + libspecr::hidden::Obj + for<'de> serde::Deserialize<'de>
        + serde::Serialize,
> Memory for TreeBorrowsMemory<T> {
    type Provenance = TreeBorrowsProvenance;
    type FrameExtra = TreeBorrowsFrameExtra;
    type T = T;
    type Params = TreeBorrowsParams;
    fn new(params: TreeBorrowsParams) -> Self {
        Self {
            mem: BasicMemory::new(),
            params,
        }
    }
    fn allocate(
        &mut self,
        kind: AllocationKind,
        size: Size,
        align: Align,
    ) -> NdResult<ThinPointer<Self::Provenance>> {
        let root = Node {
            children: List::new(),
            permissions: list![
                Permission::Unprot(PermissionUnprot::Unique); size.bytes()
            ],
            protected: Protected::No,
        };
        let path = Path::new();
        let extra = TreeBorrowsAllocationExtra { root };
        self.mem.allocate(kind, size, align, path, extra)
    }
    fn deallocate(
        &mut self,
        ptr: ThinPointer<Self::Provenance>,
        kind: AllocationKind,
        size: Size,
        align: Align,
    ) -> Result {
        self.mem
            .deallocate(
                ptr,
                kind,
                size,
                align,
                |extra, path| {
                    extra
                        .root
                        .access(Some(path), AccessKind::Write, Offset::ZERO, size)?;
                    if extra.root.contains_strong_protector_preventing_deallocation() {
                        throw_ub!(
                            "Tree Borrows: deallocating strongly protected allocation"
                        )
                    }
                    ret(())
                },
            )
    }
    fn load(
        &mut self,
        ptr: ThinPointer<Self::Provenance>,
        len: Size,
        align: Align,
    ) -> Result<List<AbstractByte<Self::Provenance>>> {
        self.mem
            .load(
                ptr,
                len,
                align,
                |extra, path, offset| {
                    extra.root.access(Some(path), AccessKind::Read, offset, len)
                },
            )
    }
    fn store(
        &mut self,
        ptr: ThinPointer<Self::Provenance>,
        bytes: List<AbstractByte<Self::Provenance>>,
        align: Align,
    ) -> Result {
        let size = Size::from_bytes(bytes.len()).unwrap();
        self.mem
            .store(
                ptr,
                bytes,
                align,
                |extra, path, offset| {
                    extra.root.access(Some(path), AccessKind::Write, offset, size)
                },
            )
    }
    fn dereferenceable(&self, ptr: ThinPointer<Self::Provenance>, len: Size) -> Result {
        self.mem.check_ptr(ptr, len)?;
        ret(())
    }
    fn retag_ptr(
        &mut self,
        frame_extra: &mut Self::FrameExtra,
        ptr: Pointer<Self::Provenance>,
        ptr_type: PtrType,
        fn_entry: bool,
        fn_implicit_writes: bool,
        vtable_lookup: impl Fn(
            ThinPointer<Self::Provenance>,
        ) -> crate::lang::VTable + 'static,
    ) -> Result<Pointer<Self::Provenance>> {
        ret(
            if let Some(perms) = ReborrowSettings::new(
                ptr,
                ptr_type,
                fn_entry,
                self.params,
                fn_implicit_writes,
                vtable_lookup,
            ) {
                self.reborrow(ptr.thin_pointer, perms, frame_extra)?.widen(ptr.metadata)
            } else {
                ptr
            },
        )
    }
    fn new_call() -> Self::FrameExtra {
        Self::FrameExtra::new()
    }
    fn end_call(&mut self, extra: Self::FrameExtra) -> Result {
        extra.protectors.try_map(|provenance| self.release_protector(provenance))?;
        ret(())
    }
    fn leak_check(&self) -> Result {
        self.mem.leak_check()
    }
}
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
enum Protected {
    Strong,
    Weak,
    No,
}
impl Protected {
    /// Check whether the node is either strongly or weakly protected.
    fn yes(self) -> bool {
        self != Protected::No
    }
}
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
struct Node {
    children: List<Node>,
    /// State for each location.
    permissions: List<Permission>,
    /// Indicates whether the node is protected by a function call,
    /// i.e., whether the original reference passed as an argument of a function call.
    /// This will be some kind of protection (weak or strong) if and only if this node is in
    /// some frame's `extra.protectors` list.
    /// There is an invariant between this field and the `permissions`:
    /// If `protected.yes()`, then all states in `permissions` must be `Permission::Prot()`.
    /// If `!protected.yes()`, they must all be `Permission::Unprot()`.
    protected: Protected,
}
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
enum NodeRelation {
    Local,
    Foreign,
}
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
enum AccessKind {
    Read,
    Write,
}
impl Node {
    /// Perform state transition on all locations of `self`.
    /// The `node_relation` indicates whether the accessed node is a local or foreign
    /// *from the perspective of `self`*.
    fn transition(
        &mut self,
        node_relation: NodeRelation,
        access_kind: AccessKind,
        offset_in_alloc: Offset,
        size: Size,
    ) -> Result {
        let offset_start = offset_in_alloc.bytes();
        for offset in offset_start..offset_start + size.bytes() {
            self.permissions
                .mutate_at(
                    offset,
                    |permission| { permission.transition(access_kind, node_relation) },
                )?;
        }
        ret(())
    }
    /// Recusively do state transition on `self` node and all its descendants.
    /// `path` is the path from `self` to the accessed node.
    /// `path` is None when the accessed node is not a descendant of `self`.
    ///
    /// This method will throw UBs, representing the undefined behavior captured by Tree Borrows.
    fn access(
        &mut self,
        path: Option<Path>,
        access_kind: AccessKind,
        offset_in_alloc: Offset,
        size: Size,
    ) -> Result {
        let node_relation = if path.is_some() {
            NodeRelation::Local
        } else {
            NodeRelation::Foreign
        };
        self.transition(node_relation, access_kind, offset_in_alloc, size)?;
        for child_id in Int::ZERO..self.children.len() {
            let sub_path = match path.and_then(|p| p.split_first()) {
                Some((head, tail)) if head == child_id => Some(tail),
                _ => None,
            };
            self.children
                .mutate_at(
                    child_id,
                    |child| {
                        child.access(sub_path, access_kind, offset_in_alloc, size)
                    },
                )?;
        }
        ret(())
    }
    /// Apply `f` to a child node of `self`
    /// `path` is the path from `self` to the target child node.
    fn access_node<O: libspecr::hidden::Obj>(
        &mut self,
        path: Path,
        f: impl FnOnce(&mut Self) -> O,
    ) -> O {
        let Some((sub_root_id, sub_path)) = path.split_first() else {
            return f(self);
        };
        if self.is_leaf() {
            panic!("Node::access_node: invalid node path");
        }
        self.children.mutate_at(sub_root_id, |child| child.access_node(sub_path, f))
    }
    /// Add a new child node to the tree whose root is self
    /// `path` is the path from `self` to the parent of the `node`.
    ///
    /// Return the path from `self` to the `node`
    fn add_node(&mut self, parent_path: Path, child: Node) -> Path {
        let child_idx = self
            .access_node(
                parent_path,
                |node| {
                    let child_idx = node.children.len();
                    node.children.push(child);
                    child_idx
                },
            );
        let mut child_path = parent_path;
        child_path.push(child_idx);
        child_path
    }
    /// Check whether `self` is a leaf.
    fn is_leaf(&self) -> bool {
        self.children.len() == Int::ZERO
    }
    /// Release the protector, and perform a special access for the protector end semantics.
    /// Recusively do state transition on all foreigns of the protected node.
    /// `path` is the path from `self` to the proctected node.
    /// `path` is None when the protected node is not a descendant of `self`.
    /// `accesses` describes which access happens at which offset.
    fn release_protector(
        &mut self,
        path: Option<Path>,
        accesses: &List<Option<AccessKind>>,
    ) -> Result {
        let node_relation = if path.is_some() {
            NodeRelation::Local
        } else {
            NodeRelation::Foreign
        };
        if path.is_some_and(|p| p.is_empty()) {
            self.protected = Protected::No;
            return ret(());
        }
        for (offset, access) in accesses.iter().enumerate() {
            let Some(access) = access else { continue };
            self.permissions
                .mutate_at(
                    Int::from(offset),
                    |permission| { permission.transition(access, node_relation) },
                )?;
        }
        for child_id in Int::ZERO..self.children.len() {
            let sub_path = match path.and_then(|p| p.split_first()) {
                Some((head, tail)) if head == child_id => Some(tail),
                _ => None,
            };
            self.children
                .mutate_at(
                    child_id,
                    |child| { child.release_protector(sub_path, accesses) },
                )?;
        }
        ret(())
    }
    /// Recusively check whether there is a strongly protected node in `self` and all its descendants.
    /// This is used to reject deallocation as long as there's a strong protector anywhere.
    /// Note that not all strongly protected nodes prevent deallocation. Specifically, if all offsets in
    /// the allocation fulfill the following property, the strong protector is not considered:
    /// * the offset has `Cell` permission, i.e. is interior mutable, or
    /// * the offset was not accessed yet, i.e. the protector is not active at this offset.
    /// See `prevents_deallocation` which implements by actually looking at the permission.
    ///
    /// Return true if there is a strongly protected node preventing deallocation.
    fn contains_strong_protector_preventing_deallocation(&self) -> bool {
        (self.protected == Protected::Strong
            && self.permissions.any(|st| st.prevents_deallocation()))
            || self
                .children
                .any(|child| child.contains_strong_protector_preventing_deallocation())
    }
}
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
enum Permission {
    Unprot(PermissionUnprot),
    Prot(PermissionProt),
}
impl Permission {
    fn transition(
        &mut self,
        access_kind: AccessKind,
        node_relation: NodeRelation,
    ) -> Result {
        match self {
            Permission::Unprot(p) => *p = p.transition(access_kind, node_relation)?,
            Permission::Prot(p) => *p = p.transition(access_kind, node_relation)?,
        };
        Ok(())
    }
    /// When a protector is released, we transition to the unprotected state machine.
    /// Additionally, we might emit a _protector end access_, depending on our current state.
    /// The second state indicates that access, or is `None` when no access should happen.
    ///
    /// This method may only be called when a protector is present.
    fn unprotect(self) -> (Permission, Option<AccessKind>) {
        match self {
            Permission::Unprot(_) => unreachable!(),
            Permission::Prot(p) => {
                let (new_perm, access) = p.unprotect();
                (Permission::Unprot(new_perm), access)
            }
        }
    }
    /// Strongly protected nodes can block deallocation, based on their permission.
    /// Specifically, they block allocation iff they would cause UB on a foreign write,
    /// that is, if they have been locally accessed ("used"), with an exception for `Cell`.
    /// The check for whether the protector is actually strong happens elsewhere, before
    /// this method is called.
    fn prevents_deallocation(&self) -> bool {
        match self {
            Permission::Unprot(p) => p.prevents_deallocation(),
            Permission::Prot(p) => p.prevents_deallocation(),
        }
    }
    /// This function checking this node's internal invariant.
    /// It is only used in debug asserts.
    fn matches_protector(&self, protected: Protected) -> bool {
        if protected.yes() {
            matches!(self, Permission::Prot(_))
        } else {
            matches!(self, Permission::Unprot(_))
        }
    }
    fn init_access(self) -> Option<AccessKind> {
        match self {
            Permission::Unprot(p) => p.init_access(),
            Permission::Prot(p) => p.init_access(),
        }
    }
}
