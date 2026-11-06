use crate::prelude::*;
use mem::*;
/// A "value expression" evaluates to a `Value`.
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
pub enum ValueExpr {
    /// Just return a constant value.
    Constant(Constant, Type),
    /// An n-tuple, used for arrays, structs, tuples (including unit).
    Tuple(List<ValueExpr>, Type),
    /// A `Union` value.
    Union {
        /// The union's field which will be initialized.
        field: Int,
        /// The value it will be initialized with.
        expr: libspecr::hidden::GcCow<ValueExpr>,
        /// The union type, needs to be `Type::Union`
        union_ty: Type,
    },
    /// A variant of an enum type.
    Variant {
        /// The discriminant of the variant.
        discriminant: Int,
        /// The `ValueExpr` for the variant.
        data: libspecr::hidden::GcCow<ValueExpr>,
        /// The enum type, needs to be `Type::Enum`.
        enum_ty: Type,
    },
    /// Read the discriminant of an enum type.
    /// As we don't need to know the validity of the inner data
    /// we don't fully load the variant value.
    GetDiscriminant {
        /// The place where the enum is located.
        place: libspecr::hidden::GcCow<PlaceExpr>,
    },
    /// Load a value from memory.
    Load {
        /// The place to load from.
        source: libspecr::hidden::GcCow<PlaceExpr>,
    },
    /// Create a pointer (raw pointer or reference) to a place.
    AddrOf {
        /// The place to create a pointer to.
        target: libspecr::hidden::GcCow<PlaceExpr>,
        /// The type of the created pointer.
        ptr_ty: PtrType,
    },
    /// Unary operators.
    UnOp { operator: UnOp, operand: libspecr::hidden::GcCow<ValueExpr> },
    /// Binary operators.
    BinOp {
        operator: BinOp,
        left: libspecr::hidden::GcCow<ValueExpr>,
        right: libspecr::hidden::GcCow<ValueExpr>,
    },
}
/// Constants are basically values, but cannot have explicit provenance.
/// Currently we do not support Ptr and Union constants.
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
pub enum Constant {
    /// A mathematical integer, used for `i*`/`u*` types.
    Int(Int),
    /// A Boolean value, used for `bool`.
    Bool(bool),
    /// A pointer pointing into a global allocation with a given offset.
    GlobalPointer(Relocation),
    /// A pointer pointing to a function.
    FnPointer(FnName),
    /// A pointer pointing to a vtable.
    VTablePointer(VTableName),
    /// A pointer with constant address, not pointing into any allocation.
    PointerWithoutProvenance(Address),
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
pub enum IntUnOp {
    /// Negate an integer value arithmetically (`x` becomes `-x`).
    Neg,
    /// Bitwise-invert an integer value
    BitNot,
    /// Used for the intrinsic ˋctpopˋ.
    CountOnes,
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
pub enum CastOp {
    /// Argument can be any integer type; returns the given integer type.
    IntToInt(IntType),
    /// Transmute the value to a different type.
    /// The program is well-formed even if the output type has a different size than the
    /// input type, but the operation is UB in that case.
    Transmute(Type),
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
pub enum UnOp {
    /// An operation on an integer; returns an integer of the same type.
    Int(IntUnOp),
    /// A form of cast; the return type is given by the specific cast operation.
    Cast(CastOp),
    /// Returns a raw pointer with same thin pointer as the operand, but without the metadata.
    GetThinPointer,
    /// Returns the metadata of a pointer as a value.
    /// The return type is given by `PointerMetaKind::ty()`, e.g., for a thin pointer this is `()`.
    GetMetadata,
    /// Returns the dynamic size of the type given the pointer metadata.
    /// The operand must be a matching metadata for the type. For sized types this is `()`.
    ComputeSize(Type),
    /// Returns the dynamic alignment of the type given the pointer metadata.
    /// The operand must be a matching metadata for the type. For sized types this is `()`.
    ComputeAlign(Type),
    /// Lookup the function pointer for a trait object method.
    /// The operand must be a pointer to a vtable as returned by `Constant::VTablePointer`.
    /// The parameter specifies which method of the vtable to look up.
    VTableMethodLookup(TraitMethodName),
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
pub enum IntBinOp {
    /// Add two integer values.
    Add,
    /// Add two integer values.
    /// Throws UB on overflow.
    AddUnchecked,
    /// Subtract two integer values.
    Sub,
    /// Subtract two integer values.
    /// Throws UB on overflow.
    SubUnchecked,
    /// Multiply two integer values.
    Mul,
    /// Multiply two integer values.
    /// Throws UB on overflow.
    MulUnchecked,
    /// Divide two integer values.
    /// UB on division by zero and on `int::MIN / -1`.
    Div,
    /// Divide two integer values.
    /// UB on division by zero, on `int::MIN / -1`, and on a non-zero remainder.
    DivExact,
    /// Remainder of a division, the `%` operator.
    /// UB if the modulos (right operand) is zero and on `int::MIN % -1`.
    Rem,
    /// Shift left `<<`
    Shl,
    /// Shift left `<<`
    /// Throws UB if right operand not in range 0..left::BITS.
    ShlUnchecked,
    /// Shift right `>>` (logical shift for unsigned integers, arithmetic shift for signed integers)
    Shr,
    /// Shift right `>>` (logical shift for unsigned integers, arithmetic shift for signed integers)
    /// Throws UB if right operand not in range 0..left::BITS.
    ShrUnchecked,
    /// Bitwise-and two integer values.
    BitAnd,
    /// Bitwise-or two integer values.
    BitOr,
    /// Bitwise-xor two integer values.
    BitXor,
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
pub enum IntBinOpWithOverflow {
    /// Add two integer values, returns a tuple of the result integer
    /// and a bool indicating whether the calculation overflowed.
    Add,
    /// Subtract two integer values, returns a tuple of the result integer
    /// and a bool indicating whether the calculation overflowed.
    Sub,
    /// Multiply two integers, returns a tuple of the result integer
    /// and a bool indicating whether the calculation overflowed.
    Mul,
}
/// A relational operator indicates how two values are to be compared.
/// Unless noted otherwise, these all return a Boolean.
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
pub enum RelOp {
    /// less than
    Lt,
    /// greater than
    Gt,
    /// less than or equal
    Le,
    /// greater than or equal
    Ge,
    /// equal
    Eq,
    /// inequal
    Ne,
    /// The three-way comparison; returns an i8:
    /// * -1 if left <  right
    /// *  0 if left == right
    /// * +1 if left >  right
    Cmp,
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
pub enum BinOp {
    /// An operation on integers (both must have the same type); returns an integer of the same type.
    Int(IntBinOp),
    /// An operation on integers (both must have the same type); returns a tuple of integer of the same type
    /// and a boolean that is true if the result is not equal to the infinite-precision result.
    IntWithOverflow(IntBinOpWithOverflow),
    /// Compares two values according to the given relational operator. Both must have the same type,
    /// and they must both be integers, Booleans, or pointers.
    Rel(RelOp),
    /// Add a byte-offset to a pointer (with or without inbounds requirement).
    /// Takes a pointer as left operand and an integer as right operand;
    /// returns a pointer.
    /// FIXME: should we make this in units of the pointee size? The thing is, for
    /// raw pointers we do not have the pointee type...
    PtrOffset { inbounds: bool },
    /// Compute the distance between two pointers in bytes (with or without inbounds requirement).
    /// Takes two pointers; returns a signed pointer-sized integer.
    /// If `nonneg` is true, it is UB for the result to be negative.
    PtrOffsetFrom { inbounds: bool, nonneg: bool },
    /// This corresponds to `core::ptr::from_raw_parts`
    /// and takes a thin pointer and matching metadata to construct a pointer of the given type.
    /// When the target type is a thin pointer and the metadata is `()`, this is just a pointer cast.
    ConstructWidePointer(PtrType),
}
/// A "place expression" evaluates to a `Place`.
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
pub enum PlaceExpr {
    /// Denotes a local variable.
    Local(LocalName),
    /// Dereference a value (of pointer/reference type).
    Deref { operand: libspecr::hidden::GcCow<ValueExpr>, ty: Type },
    /// Project to a field.
    Field {
        /// The place to base the projection on.
        root: libspecr::hidden::GcCow<PlaceExpr>,
        /// The field to project to.
        field: Int,
    },
    /// Index to an array or slice element.
    Index {
        /// The array or slice to index into.
        root: libspecr::hidden::GcCow<PlaceExpr>,
        /// The index to project to.
        index: libspecr::hidden::GcCow<ValueExpr>,
    },
    /// Enum variant downcast.
    Downcast {
        /// The base enum to project to the specific variant.
        root: libspecr::hidden::GcCow<PlaceExpr>,
        /// The discriminant of the variant to project to.
        discriminant: Int,
    },
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
pub enum Statement {
    /// Copy value from `source` to `destination`.
    Assign { destination: PlaceExpr, source: ValueExpr },
    /// Evaluate a place without accessing it.
    /// This is the result of translating e.g. `let _ = place;`.
    PlaceMention(PlaceExpr),
    /// Set the discriminant of the variant at `destination` to `value`.
    SetDiscriminant { destination: PlaceExpr, value: Int },
    /// Ensure that `place` contains a valid value of its type (else UB).
    /// Also perform retagging and ensure safe pointers are dereferenceable.
    ///
    /// The frontend is generally expected to generate this for all function argument,
    /// and possibly in more places.
    Validate {
        place: PlaceExpr,
        /// Indicates whether this operation occurs as part of the prelude
        /// that we have at the top of each function (which affects retagging).
        fn_entry: bool,
    },
    /// De-initialize a place.
    Deinit { place: PlaceExpr },
    /// Allocate the backing store for this local.
    StorageLive(LocalName),
    /// Deallocate the backing store for this local.
    StorageDead(LocalName),
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
pub enum Terminator {
    /// Just jump to the next block.
    Goto(BbName),
    /// `value` needs to evaluate to a `Value::Int`.
    /// `cases` map those values to blocks to jump to and therefore have to have the equivalent type.
    /// If no value matches we fall back to the block given in `fallback`.
    Switch { value: ValueExpr, cases: Map<Int, BbName>, fallback: BbName },
    /// If this is ever executed, we have UB.
    Unreachable,
    /// Invoke the given intrinsic operation with the given arguments.
    ///
    /// Intrinsics are langauge primitives that can have arbitrary side-effects, including divergence.
    Intrinsic {
        intrinsic: IntrinsicOp,
        /// The arguments to pass.
        arguments: List<ValueExpr>,
        /// The place to put the return value into.
        ret: PlaceExpr,
        /// The block to jump to when this call returns.
        /// If `None`, UB will be raised when the intrinsic returns.
        next_block: Option<BbName>,
    },
    /// Call the given function with the given arguments.
    Call {
        /// What function or method to call.
        /// This must evaluate to a function pointer and for safe behaviour, the functions signature must match the arguments.
        ///
        /// Dynamic dispatch is represented with the callee being the result of `VTableMethodLookup(GetMetadata(self))`,
        /// and the `self` argument appropriately cast to a thin pointer type.
        callee: ValueExpr,
        /// The calling convention to use for this call.
        calling_convention: CallingConvention,
        /// The arguments to pass.
        arguments: List<ArgumentExpr>,
        /// The place to put the return value into.
        ret: PlaceExpr,
        /// The block to jump to when this call returns.
        /// If `None`, UB will be raised when the function returns.
        next_block: Option<BbName>,
        /// The block to jump to when this call unwinds.
        /// If `None`, UB will be raised when the function unwinds.
        /// This comes with a well-formedness requirement: if the current block is a regular block,
        /// `unwind_block` must be either a cleanup block or a catch block;
        /// otherwise, `unwind_block` must be a terminating block.
        unwind_block: Option<BbName>,
    },
    /// Return from the current function.
    Return,
    /// Starts unwinding, jump to the indicated cleanup block.
    StartUnwind {
        /// The unwinding payload. This should evaluate to a thin pointer.
        unwind_payload: ValueExpr,
        /// The cleanup or catch block the execution jumps to.
        unwind_block: BbName,
    },
    /// Stops unwinding, jump to the indicated regular block.
    /// This also removes the topmost unwinding payload.
    /// UB if not currently unwinding.
    StopUnwind(BbName),
    /// Ends this function call. The unwinding should continue at the caller's stack frame.
    ResumeUnwind,
}
/// Function arguments can be passed by-value or in-place.
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
pub enum ArgumentExpr {
    /// Pass a copy of this value to the function.
    ///
    /// Technically this could be encoded by generating a fresh temporary, copying the value there, and doing in-place passing.
    /// FIXME: is it worth providing this mode anyway?
    ByValue(ValueExpr),
    /// Pass the argument value in-place; the contents of this place may be altered arbitrarily by the callee.
    InPlace(PlaceExpr),
}
/// The `CallingConvention` defines how function arguments and return values are passed.
///
/// The assumption is that if caller and callee agree on the calling convention, and all arguments and the return types
/// pass `check_abi_compatibility`, then this implies they are ABI-compatible on real implementations.
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
pub enum CallingConvention {
    Rust,
    C,
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
pub enum IntrinsicLockOp {
    Acquire,
    Release,
    Create,
}
/// The intrinsic operations supported by MiniRust.
/// Generally we only make things intrinsics if they cannot be operands, i.e.
/// they are non-deterministic or mutate the global state.
/// We also make them intrinsic if they return `()`, because an operand that
/// does not return anything is kind of odd.
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
pub enum IntrinsicOp {
    Abort,
    Assume,
    Exit,
    PrintStdout,
    PrintStderr,
    Allocate,
    Deallocate,
    Spawn,
    Join,
    /// Determines whether the raw bytes pointed to by two pointers are equal.
    /// (Can't be an operand because it reads from memory.)
    RawEq,
    AtomicStore,
    AtomicLoad,
    AtomicCompareExchange,
    AtomicFetchAndOp(IntBinOp),
    Lock(IntrinsicLockOp),
    /// 'Expose' the provenance a pointer so that it can later be cast to an integer.
    /// The address part of the pointer is stored in `destination`.
    PointerExposeProvenance,
    /// Create a new pointer from the given address with some previously exposed provenance.
    PointerWithExposedProvenance,
    /// Access the current unwinding payload. UB if not currently unwinding.
    GetUnwindPayload,
}
/// Opaque types of names for functions, vtables, trait methods, and globals.
/// The internal representations of these types do not matter.
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
pub struct FnName(pub libspecr::Name);
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
pub struct GlobalName(pub libspecr::Name);
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
pub struct VTableName(pub libspecr::Name);
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
pub struct TraitMethodName(pub libspecr::Name);
/// A closed MiniRust program.
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
pub struct Program {
    /// Associate a function with each declared function name.
    pub functions: Map<FnName, Function>,
    /// The function where execution starts.
    pub start: FnName,
    /// Associate each global name with the associated global.
    pub globals: Map<GlobalName, Global>,
    /// Stores all traits and method names which are available for dynamic dispatch.
    pub traits: Map<TraitName, Set<TraitMethodName>>,
    /// Store the vtables with method tables and layout information.
    pub vtables: Map<VTableName, VTable>,
}
/// Opaque types of names for local variables and basic blocks.
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
pub struct LocalName(pub libspecr::Name);
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
pub struct BbName(pub libspecr::Name);
/// A MiniRust function.
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
pub struct Function {
    /// The locals of this function, and their type.
    pub locals: Map<LocalName, Type>,
    /// A list of locals that are initially filled with the function arguments.
    pub args: List<LocalName>,
    /// The name of a local that holds the return value when the function returns.
    pub ret: LocalName,
    /// The call calling convention of this function.
    pub calling_convention: CallingConvention,
    /// Associate each basic block name with the associated block.
    pub blocks: Map<BbName, BasicBlock>,
    /// The basic block where execution starts.
    pub start: BbName,
    /// Whether implicit writes are enabled for this function.
    pub implicit_writes: bool,
}
/// A basic block is a sequence of statements followed by a terminator.
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
pub struct BasicBlock {
    pub statements: List<Statement>,
    pub terminator: Terminator,
    pub kind: BbKind,
}
/// The kind of a basic block in the CFG.
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
pub enum BbKind {
    /// Regular blocks may use `Return` and `StartUnwind` but not `ResumeUnwind`.
    Regular,
    /// Cleanup blocks may use `ResumeUnwind` but not `Return` or `StartUnwind`.
    Cleanup,
    /// Catch blocks may use neither `Return` nor `ResumeUnwind` nor `StartUnwind`.
    /// Catch blocks may branch to regular blocks.
    Catch,
    /// `Terminate` blocks may use neither `Return` nor `ResumeUnwind` nor `StartUnwind`.
    Terminate,
}
/// A global allocation.
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
pub struct Global {
    /// The raw bytes of the allocation. `None` represents uninitialized bytes.
    pub bytes: List<Option<u8>>,
    /// Cross-references pointing to other global allocations,
    /// together with an offset, expressing where this allocation should put the pointer.
    /// Note that the pointers created due to relocations overwrite the data given by `bytes`.
    pub relocations: List<(Offset, Relocation)>,
    /// The alignment with which this global shall be allocated.
    pub align: Align,
}
/// A pointer into a global allocation.
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
pub struct Relocation {
    /// The name of the global allocation we are pointing into.
    pub name: GlobalName,
    /// The offset within that allocation.
    pub offset: Offset,
}
/// A vtable for a trait-type pair.
/// This is pointed to by the trait object metadata.
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
pub struct VTable {
    /// What trait this vtable is for.
    /// All vtables for this trait name have implementation for same set of methods.
    pub trait_name: TraitName,
    /// The size of the type.
    pub size: Size,
    /// The alignment of the type.
    pub align: Align,
    /// Offset and sizes of `UnsafeCell` in this vtable.
    pub cells: List<(Offset, Size)>,
    /// The implementations of trait methods.
    pub methods: Map<TraitMethodName, FnName>,
}
/// This type contains everything that needs to be tracked during the execution
/// of a MiniRust program.
#[derive(GcCompat)]
#[derive(Debug)]
pub struct Machine<M: Memory + libspecr::hidden::Obj> {
    /// The program we are executing.
    prog: Program,
    /// The contents of memory.
    mem: ConcurrentMemory<M>,
    /// The state of the integer-pointer cast subsystem.
    intptrcast: IntPtrCast<M::Provenance>,
    /// The threads (in particular, their stacks).
    threads: List<Thread<M>>,
    /// The currently / most recently active thread.
    active_thread: ThreadId,
    /// A set of threads that have been synchronized.
    /// A thread being added here in a given step means that if the very next step is
    /// by that thread, we do *not* do data race detection: there was synchronization
    /// between these two steps, so any potential accesses are not racing.
    synchronized_threads: Set<ThreadId>,
    /// The Locks
    locks: List<LockState>,
    /// Stores a pointer to each of the global allocations, which are all `Sized`.
    global_ptrs: Map<GlobalName, ThinPointer<M::Provenance>>,
    /// Stores a pointer for each function name.
    fn_ptrs: Map<FnName, ThinPointer<M::Provenance>>,
    /// Stores a pointer for each vtable.
    vtable_ptrs: Map<VTableName, ThinPointer<M::Provenance>>,
    /// This is where the `PrintStdout` intrinsic writes to.
    stdout: DynWrite,
    /// This is where the `PrintStderr` intrinsic writes to.
    stderr: DynWrite,
}
/// The data that makes up a stack frame.
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
struct StackFrame<M: Memory + libspecr::hidden::Obj> {
    /// The function this stack frame belongs to.
    func: Function,
    /// For each live local, the location in memory where its value is stored.
    locals: Map<LocalName, ThinPointer<M::Provenance>>,
    /// Expresses what happens after the callee (this function) returns or resumes unwinding.
    stack_pop_action: StackPopAction<M>,
    /// `next_block` and `next_stmt` describe the next statement/terminator to execute (the "program counter").
    /// `next_block` identifies the basic block,
    next_block: BbName,
    /// If `next_stmt` is equal to the number of statements in this block (an
    /// out-of-bounds index in the statement list), it refers to the terminator.
    next_stmt: Int,
    /// The memory model is given the ability to track some extra per-frame data.
    extra: M::FrameExtra,
}
/// Defines the behavior when the function returns or resumes unwinding.
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
enum StackPopAction<M: Memory + libspecr::hidden::Obj> {
    /// This is the bottom of the stack, there is nothing left to do in this thread.
    BottomOfStack,
    /// Go back to the caller.
    BackToCaller {
        /// The basic block to jump to when the callee returns.
        /// If `None`, UB will be raised when the callee returns.
        next_block: Option<BbName>,
        /// The basic block to jump to when the callee resumes unwinding.
        /// If `None`, UB will be raised when the callee resumes unwinding.
        unwind_block: Option<BbName>,
        /// The location where the caller wants to see the return value.
        /// The caller type already been checked to be suitably compatible with the callee return type.
        ret_val_ptr: ThinPointer<M::Provenance>,
    },
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
pub struct Thread<M: Memory + libspecr::hidden::Obj> {
    /// The stack. This is only the "control" part of the stack; the "data" part
    /// lives in memory (and stack and memory are completely disjoint concepts
    /// in the Abstract Machine).
    stack: List<StackFrame<M>>,
    /// Stores whether the thread is ready to run, blocked, or terminated.
    state: ThreadState,
    /// Stores the unwind payloads.
    unwind_payloads: List<ThinPointer<M::Provenance>>,
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
pub enum ThreadState {
    /// The thread is enabled and can get executed.
    Enabled,
    /// The thread is trying to join another thread and is blocked until that thread finishes.
    BlockedOnJoin(ThreadId),
    /// The thread is waiting to acquire a lock.
    BlockedOnLock(LockId),
    /// The thread has terminated.
    Terminated,
}
impl<M: Memory + libspecr::hidden::Obj> Machine<M> {
    pub fn new(
        prog: Program,
        mem_params: M::Params,
        stdout: DynWrite,
        stderr: DynWrite,
    ) -> NdResult<Machine<M>> {
        prog.check_wf::<M::T>()?;
        let mut mem = ConcurrentMemory::<M>::new(mem_params);
        let mut global_ptrs = Map::new();
        let mut fn_ptrs = Map::new();
        let mut vtable_ptrs = Map::new();
        for (global_name, global) in prog.globals {
            let size = Size::from_bytes(global.bytes.len()).unwrap();
            let alloc = mem.allocate(AllocationKind::Global, size, global.align)?;
            global_ptrs.insert(global_name, alloc);
        }
        for (global_name, global) in prog.globals {
            let mut bytes = global
                .bytes
                .map(|b| match b {
                    Some(x) => AbstractByte::Init(x, None),
                    None => AbstractByte::Uninit,
                });
            for (i, relocation) in global.relocations {
                let ptr = (global_ptrs)
                    .index_at(relocation.name)
                    .wrapping_offset::<M::T>(relocation.offset.bytes());
                let encoded_ptr = encode_ptr::<M>(ptr);
                bytes.write_subslice_at_index(i.bytes(), encoded_ptr);
            }
            mem.store(
                    (global_ptrs).index_at(global_name),
                    bytes,
                    global.align,
                    Atomicity::None,
                )
                .unwrap();
        }
        for (fn_name, _function) in prog.functions {
            let alloc = mem.allocate(AllocationKind::Function, Size::ZERO, Align::ONE)?;
            fn_ptrs.insert(fn_name, alloc);
        }
        for (vtable_name, _vtable) in prog.vtables {
            let alloc = mem.allocate(AllocationKind::VTable, Size::ZERO, Align::ONE)?;
            vtable_ptrs.insert(vtable_name, alloc);
        }
        let mut machine = Machine {
            prog,
            mem,
            intptrcast: IntPtrCast::new(),
            global_ptrs,
            fn_ptrs,
            vtable_ptrs,
            threads: list![],
            locks: List::new(),
            active_thread: ThreadId::ZERO,
            synchronized_threads: Set::new(),
            stdout,
            stderr,
        };
        let start_fn = (prog.functions).index_at(prog.start);
        machine.new_thread(start_fn, list![])?;
        ret(machine)
    }
    /// To run a MiniRust program, call this in a loop until it throws an `Err` (UB or termination).
    pub fn step(&mut self) -> NdResult {
        if !self.threads.any(|thread| thread.state == ThreadState::Enabled) {
            throw_deadlock!();
        }
        let prev_step_information = self.reset_data_race_tracking();
        let distr = libspecr::IntDistribution {
            start: Int::ZERO,
            end: Int::from(self.threads.len()),
            divisor: Int::ONE,
        };
        self.active_thread = pick(
            distr,
            |id: ThreadId| {
                let Some(thread) = self.threads.get(id) else {
                    return false;
                };
                thread.state == ThreadState::Enabled
            },
        )?;
        let frame = self.cur_frame();
        let block = &(frame.func.blocks).index_at(frame.next_block);
        if frame.next_stmt == block.statements.len() {
            self.eval_terminator(block.terminator)?;
        } else {
            let stmt = (block.statements).index_at(frame.next_stmt);
            self.eval_statement(stmt)?;
            self.try_mutate_cur_frame(|frame, _mem| {
                frame.next_stmt += 1;
                ret(())
            })?;
        }
        self.mem.check_data_races(self.active_thread, prev_step_information)?;
        ret(())
    }
    fn active_thread(&self) -> Thread<M> {
        (self.threads).index_at(self.active_thread)
    }
    fn mutate_active_thread<O: libspecr::hidden::Obj>(
        &mut self,
        f: impl FnOnce(&mut Thread<M>) -> O,
    ) -> O {
        self.threads.mutate_at(self.active_thread, f)
    }
    fn cur_frame(&self) -> StackFrame<M> {
        self.active_thread().cur_frame()
    }
    fn mutate_cur_frame<O: libspecr::hidden::Obj>(
        &mut self,
        f: impl FnOnce(&mut StackFrame<M>, &mut ConcurrentMemory<M>) -> O,
    ) -> O {
        self.threads
            .mutate_at(
                self.active_thread,
                |thread| thread.mutate_cur_frame(|frame| f(frame, &mut self.mem)),
            )
    }
    fn try_mutate_cur_frame<O: libspecr::hidden::Obj>(
        &mut self,
        f: impl FnOnce(&mut StackFrame<M>, &mut ConcurrentMemory<M>) -> NdResult<O>,
    ) -> NdResult<O> {
        self.threads
            .try_mutate_at(
                self.active_thread,
                |thread| thread.try_mutate_cur_frame(|frame| f(frame, &mut self.mem)),
            )
    }
    fn mutate_cur_stack<O: libspecr::hidden::Obj>(
        &mut self,
        f: impl FnOnce(&mut List<StackFrame<M>>) -> O,
    ) -> O {
        self.threads.mutate_at(self.active_thread, |thread| f(&mut thread.stack))
    }
    /// Create a new thread where the first frame calls the given function with the given arguments.
    fn new_thread(
        &mut self,
        func: Function,
        args: List<(Value<M>, Type)>,
    ) -> NdResult<ThreadId> {
        let init_frame = self
            .create_frame(
                func,
                StackPopAction::BottomOfStack,
                CallingConvention::C,
                unit_type(),
                args,
            )?;
        let thread = Thread {
            state: ThreadState::Enabled,
            stack: list![init_frame],
            unwind_payloads: list![],
        };
        let thread_id = ThreadId::from(self.threads.len());
        self.threads.push(thread);
        ret(thread_id)
    }
    /// Look up a function given a pointer.
    fn fn_from_ptr(&self, ptr: Value<M>) -> Result<Function> {
        if let Value::Ptr(Pointer { thin_pointer: thin_ptr, metadata }) = ptr {
            if metadata.is_some() {
                throw_ub!("invalid pointer for function lookup");
            }
            let Some((func_name, _)) = self
                .fn_ptrs
                .iter()
                .find(|(_, fn_ptr)| *fn_ptr == thin_ptr) else {
                throw_ub!("invalid pointer for function lookup");
            };
            ret((self.prog.functions).index_at(func_name))
        } else {
            throw_ub!("trying to look up a function based on a non-pointer value");
        }
    }
    /// Look up a vtable given a pointer.
    fn vtable_from_ptr(&self, ptr: ThinPointer<M::Provenance>) -> Result<VTable> {
        let Some((vtable_name, _)) = self
            .vtable_ptrs
            .iter()
            .find(|(_, vtable_ptr)| *vtable_ptr == ptr) else {
            throw_ub!("invalid pointer for vtable lookup");
        };
        ret((self.prog.vtables).index_at(vtable_name))
    }
    /// Reset the data race tracking for the next step, and return the information from the previous step.
    ///
    /// The first component of the return value is the set of threads that were synchronized by the previous step,
    /// the second is the list of accesses in the previous step.
    fn reset_data_race_tracking(&mut self) -> (Set<ThreadId>, List<Access>) {
        let mut prev_sync = self.synchronized_threads;
        prev_sync.insert(self.active_thread);
        let prev_accesses = self.mem.reset_accesses();
        (prev_sync, prev_accesses)
    }
    /// All vtable lookups must have well-defined pointers. If this panics it is a spec bug.
    fn vtable_lookup(&self) -> impl Fn(ThinPointer<M::Provenance>) -> VTable + 'static {
        let ptrs = self.vtable_ptrs;
        let vtables = self.prog.vtables;
        move |ptr| {
            let (name, _) = ptrs
                .iter()
                .find(|(_, vtable_ptr)| *vtable_ptr == ptr)
                .unwrap();
            let vtable = (vtables).index_at(name);
            vtable
        }
    }
    /// Helper function to compute the size with the allocated vtables in `self`.
    fn compute_size(
        &self,
        layout: LayoutStrategy,
        meta: Option<PointerMeta<M::Provenance>>,
    ) -> Size {
        let (size, _) = layout.compute_size_and_align(meta, self.vtable_lookup());
        size
    }
    /// Helper function to compute the alignment with the allocated vtables in `self`.
    fn compute_align(
        &self,
        layout: LayoutStrategy,
        meta: Option<PointerMeta<M::Provenance>>,
    ) -> Align {
        let (_, align) = layout.compute_size_and_align(meta, self.vtable_lookup());
        align
    }
    /// Defines well-formedness for pointer metadata for a given kind.
    fn check_ptr_metadata(
        &self,
        meta: Option<PointerMeta<M::Provenance>>,
        kind: PointerMetaKind,
    ) -> Result {
        match (meta, kind) {
            (None, PointerMetaKind::None) => {}
            (Some(PointerMeta::ElementCount(num)), PointerMetaKind::ElementCount) => {
                self.check_value(
                    Value::Int(num),
                    Type::Int(IntType::usize_ty::<M::T>()),
                )?
            }
            (
                Some(PointerMeta::VTablePointer(ptr)),
                PointerMetaKind::VTablePointer(trait_name),
            ) => {
                self.check_ptr(ptr.widen(None), PtrType::VTablePtr(trait_name))?;
            }
            _ => throw_ub!("Value::Ptr: invalid metadata"),
        };
        Ok(())
    }
    /// Checks that a pointer is well-formed.
    fn check_ptr(&self, ptr: Pointer<M::Provenance>, ptr_ty: PtrType) -> Result {
        ensure_else_ub(
            ptr.thin_pointer.addr.in_bounds(Unsigned, M::T::PTR_SIZE),
            "Value::Ptr: pointer out-of-bounds",
        )?;
        self.check_ptr_metadata(ptr.metadata, ptr_ty.meta_kind())?;
        if let Some(pointee) = ptr_ty.safe_pointee() {
            let size = self.compute_size(pointee.layout, ptr.metadata);
            let align = self.compute_align(pointee.layout, ptr.metadata);
            ensure_else_ub(
                size.bytes().in_bounds(Signed, M::T::PTR_SIZE),
                "Value::Ptr: total size exeeds isize::MAX",
            )?;
            ensure_else_ub(ptr.thin_pointer.addr != 0, "Value::Ptr: null safe pointer")?;
            ensure_else_ub(
                align.is_aligned(ptr.thin_pointer.addr),
                "Value::Ptr: unaligned safe pointer",
            )?;
            ensure_else_ub(
                pointee.inhabited,
                "Value::Ptr: safe pointer to uninhabited type",
            )?;
            ensure_else_ub(
                self.mem.dereferenceable(ptr.thin_pointer, size).is_ok(),
                "Value::Ptr: non-dereferenceable safe pointer",
            )?;
        } else if let PtrType::VTablePtr(trait_name) = ptr_ty {
            let vtable = self.vtable_from_ptr(ptr.thin_pointer)?;
            ensure_else_ub(
                vtable.trait_name == trait_name,
                "Value::Ptr: invalid vtable in metadata",
            )?;
        }
        Ok(())
    }
    /// We assume `ty` is itself well-formed and sized and the variant of `value` matches the `ty` variant.
    /// The specification must not call this function otherwise.
    fn check_value(&self, value: Value<M>, ty: Type) -> Result {
        match (value, ty) {
            (Value::Int(i), Type::Int(int_ty)) => {
                ensure_else_ub(
                    int_ty.can_represent(i),
                    "Value::Int: invalid integer value",
                )?;
            }
            (Value::Bool(_), Type::Bool) => {}
            (Value::Ptr(ptr), Type::Ptr(ptr_ty)) => self.check_ptr(ptr, ptr_ty)?,
            (Value::Tuple(vals), Type::Tuple { sized_fields, unsized_field, .. }) => {
                let unsized_field = unsized_field.extract();
                {
                    assert!(
                        unsized_field.is_none(),
                        "Value: unsized structs cannot be represented as values"
                    );
                    ensure_else_ub(
                        vals.len() == sized_fields.len(),
                        "Value::Tuple: invalid number of fields",
                    )?;
                    for (val, (_, ty)) in vals.zip(sized_fields) {
                        self.check_value(val, ty)?;
                    }
                }
            }
            (Value::Tuple(vals), Type::Array { elem, count }) => {
                let elem = elem.extract();
                {
                    ensure_else_ub(
                        vals.len() == count,
                        "Value::Tuple: invalid number of elements",
                    )?;
                    for val in vals {
                        self.check_value(val, elem)?;
                    }
                }
            }
            (Value::Union(chunk_data), Type::Union { chunks, .. }) => {
                ensure_else_ub(
                    chunk_data.len() == chunks.len(),
                    "Value::Union: invalid chunk size",
                )?;
                for (data, (_, size)) in chunk_data.zip(chunks) {
                    ensure_else_ub(
                        data.len() == size.bytes(),
                        "Value::Union: invalid chunk data",
                    )?;
                }
            }
            (Value::Variant { discriminant, data }, Type::Enum { variants, .. }) => {
                let data = data.extract();
                {
                    let Some(variant) = variants.get(discriminant) else {
                        throw_ub!("Value::Variant: invalid discrimant");
                    };
                    self.check_value(data, variant.ty)?;
                }
            }
            (_, Type::Slice { .. }) => {
                panic!("Value: slices cannot be represented as values")
            }
            (_, Type::TraitObject { .. }) => {
                panic!("Value: trait objects cannot be represented as values")
            }
            _ => panic!("Value: value does not match type"),
        }
        ret(())
    }
    fn typed_store(
        &mut self,
        ptr: ThinPointer<M::Provenance>,
        val: Value<M>,
        ty: Type,
        align: Align,
        atomicity: Atomicity,
    ) -> Result {
        assert!(
            self.check_value(val, ty).is_ok(),
            "trying to store {val:?} which is ill-formed for {:#?}", ty
        );
        let bytes = ty.encode::<M>(val);
        self.mem.store(ptr, bytes, align, atomicity)?;
        ret(())
    }
    fn typed_load(
        &mut self,
        ptr: ThinPointer<M::Provenance>,
        ty: Type,
        align: Align,
        atomicity: Atomicity,
    ) -> Result<Value<M>> {
        let bytes = self
            .mem
            .load(
                ptr,
                ty.layout::<M::T>().expect_size("the callers ensure `ty` is sized"),
                align,
                atomicity,
            )?;
        ret(
            match ty.decode::<M>(bytes) {
                Some(val) => {
                    self.check_value(val, ty)?;
                    val
                }
                None => {
                    throw_ub!(
                        "load at type {ty:?} but the data in memory violates the language invariant"
                    )
                }
            },
        )
    }
    /// Transmutes `val` from `type1` to `type2`.
    fn transmute(&self, val: Value<M>, type1: Type, type2: Type) -> Result<Value<M>> {
        assert!(
            type1.layout::< M::T > ().expect_size("WF ensures sized operands") == type2
            .layout::< M::T > ().expect_size("WF ensures sized operands")
        );
        let bytes = type1.encode::<M>(val);
        if let Some(raw_value) = type2.decode::<M>(bytes) {
            self.check_value(raw_value, type2)?;
            ret(raw_value)
        } else {
            throw_ub!("transmuted value is not valid at new type")
        }
    }
    fn eval_intrinsic(
        &mut self,
        intrinsic: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        match intrinsic {
            IntrinsicOp::PointerExposeProvenance => {
                if arguments.len() != 1 {
                    throw_ub!(
                        "invalid number of arguments for `PointerExposeProvenance` intrinsic"
                    );
                }
                let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = (arguments)
                    .index_at(0)
                    .0 else {
                    throw_ub!(
                        "invalid argument for `PointerExposeProvenance` intrinsic: not a thin pointer"
                    );
                };
                if ret_ty
                    != Type::Int(IntType {
                        signed: Unsigned,
                        size: M::T::PTR_SIZE,
                    })
                {
                    throw_ub!(
                        "invalid return type for `PointerExposeProvenance` intrinsic"
                    )
                }
                self.intptrcast.expose(ptr);
                ret(Value::Int(ptr.addr))
            }
            IntrinsicOp::PointerWithExposedProvenance => {
                if arguments.len() != 1 {
                    throw_ub!(
                        "invalid number of arguments for `PointerWithExposedProvenance` intrinsic"
                    );
                }
                let Value::Int(addr) = (arguments).index_at(0).0 else {
                    throw_ub!(
                        "invalid argument for `PointerWithExposedProvenance` intrinsic: not an integer"
                    );
                };
                let Type::Ptr(ret_ptr_ty) = ret_ty else {
                    throw_ub!(
                        "invalid return type for `PointerWithExposedProvenance` intrinsic"
                    );
                };
                if ret_ptr_ty.meta_kind() != PointerMetaKind::None {
                    throw_ub!(
                        "unsized pointee requested for `PointerWithExposedProvenance` intrinsic"
                    );
                }
                let ptr = self.intptrcast.int2ptr(addr)?;
                ret(Value::Ptr(ptr.widen(None)))
            }
            IntrinsicOp::Exit => self.exit()?,
            IntrinsicOp::Abort => {
                throw_abort!();
            }
            IntrinsicOp::Assume => {
                if arguments.len() != 1 {
                    throw_ub!("invalid number of arguments for `Assume` intrinsic");
                }
                let Value::Bool(b) = (arguments).index_at(0).0 else {
                    throw_ub!("invalid argument for `Assume` intrinsic: not a Boolean");
                };
                if ret_ty != unit_type() {
                    throw_ub!("invalid return type for `Assume` intrinsic")
                }
                if !b {
                    throw_ub!("`Assume` intrinsic called on condition that is violated");
                }
                ret(unit_value())
            }
            IntrinsicOp::PrintStdout => {
                if ret_ty != unit_type() {
                    throw_ub!("invalid return type for `PrintStdout` intrinsic")
                }
                self.eval_print(self.stdout, arguments)?;
                ret(unit_value())
            }
            IntrinsicOp::PrintStderr => {
                if ret_ty != unit_type() {
                    throw_ub!("invalid return type for `PrintStderr` intrinsic")
                }
                self.eval_print(self.stderr, arguments)?;
                ret(unit_value())
            }
            IntrinsicOp::Allocate => {
                if arguments.len() != 2 {
                    throw_ub!("invalid number of arguments for `Allocate` intrinsic");
                }
                let Value::Int(size) = (arguments).index_at(0).0 else {
                    throw_ub!(
                        "invalid first argument to `Allocate` intrinsic: not an integer"
                    );
                };
                let Some(size) = Size::from_bytes(size) else {
                    throw_ub!("invalid size for `Allocate` intrinsic: negative size");
                };
                let Value::Int(align) = (arguments).index_at(1).0 else {
                    throw_ub!(
                        "invalid second argument to `Allocate` intrinsic: not an integer"
                    );
                };
                let Some(align) = Align::from_bytes(align) else {
                    throw_ub!(
                        "invalid alignment for `Allocate` intrinsic: not a power of 2"
                    );
                };
                let Type::Ptr(ret_ptr_ty) = ret_ty else {
                    throw_ub!("invalid return type for `Allocate` intrinsic");
                };
                if ret_ptr_ty.meta_kind() != PointerMetaKind::None {
                    throw_ub!("unsized pointee requested for `Allocate` intrinsic");
                }
                let alloc = self.mem.allocate(AllocationKind::Heap, size, align)?;
                ret(Value::Ptr(alloc.widen(None)))
            }
            IntrinsicOp::Deallocate => {
                if arguments.len() != 3 {
                    throw_ub!("invalid number of arguments for `Deallocate` intrinsic");
                }
                let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = (arguments)
                    .index_at(0)
                    .0 else {
                    throw_ub!(
                        "invalid first argument to `Deallocate` intrinsic: not a thin pointer"
                    );
                };
                let Value::Int(size) = (arguments).index_at(1).0 else {
                    throw_ub!(
                        "invalid second argument to `Deallocate` intrinsic: not an integer"
                    );
                };
                let Some(size) = Size::from_bytes(size) else {
                    throw_ub!("invalid size for `Deallocate` intrinsic: negative size");
                };
                let Value::Int(align) = (arguments).index_at(2).0 else {
                    throw_ub!(
                        "invalid third argument to `Deallocate` intrinsic: not an integer"
                    );
                };
                let Some(align) = Align::from_bytes(align) else {
                    throw_ub!(
                        "invalid alignment for `Deallocate` intrinsic: not a power of 2"
                    );
                };
                if ret_ty != unit_type() {
                    throw_ub!("invalid return type for `Deallocate` intrinsic")
                }
                self.mem.deallocate(ptr, AllocationKind::Heap, size, align)?;
                ret(unit_value())
            }
            IntrinsicOp::Spawn => {
                if arguments.len() != 2 {
                    throw_ub!("invalid number of arguments for `Spawn` intrinsic");
                }
                let fn_ptr = (arguments).index_at(0).0;
                let func = self.fn_from_ptr(fn_ptr)?;
                let (data_ptr, data_ptr_ty) = (arguments).index_at(1);
                if !matches!(data_ptr_ty, Type::Ptr(_)) {
                    throw_ub!(
                        "invalid second argument to `Spawn` intrinsic: not a pointer"
                    );
                }
                if !matches!(ret_ty, Type::Int(_)) {
                    throw_ub!("invalid return type for `Spawn` intrinsic")
                }
                let thread_id = self.spawn(func, data_ptr, data_ptr_ty)?;
                ret(Value::Int(thread_id))
            }
            IntrinsicOp::Join => {
                if arguments.len() != 1 {
                    throw_ub!("invalid number of arguments for `Join` intrinsic");
                }
                let Value::Int(thread_id) = (arguments).index_at(0).0 else {
                    throw_ub!(
                        "invalid first argument to `Join` intrinsic: not an integer"
                    );
                };
                if ret_ty != unit_type() {
                    throw_ub!("invalid return type for `Join` intrinsic")
                }
                self.join(thread_id)?;
                ret(unit_value())
            }
            IntrinsicOp::RawEq => {
                if arguments.len() != 2 {
                    throw_ub!("invalid number of arguments for `RawEq` intrinsic");
                }
                if ret_ty != Type::Bool {
                    throw_ub!("invalid return type for `RawEq` intrinsic")
                }
                let (left, l_ty) = (arguments).index_at(0);
                let (right, r_ty) = (arguments).index_at(1);
                if l_ty != r_ty {
                    throw_ub!(
                        "invalid arguments to `RawEq` intrinsic: types of arguments are not identical"
                    );
                }
                let Value::Ptr(left) = left else {
                    throw_ub!(
                        "invalid first argument to `RawEq` intrinsic: not a pointer"
                    );
                };
                let Value::Ptr(right) = right else {
                    throw_ub!(
                        "invalid second argument to `RawEq` intrinsic: not a pointer"
                    );
                };
                let Type::Ptr(l_ty) = l_ty else {
                    throw_ub!(
                        "invalid argument type to `RawEq` intrinsic: not a pointer"
                    );
                };
                let left_data = self.load_raw_data(left, l_ty)?;
                let right_data = self.load_raw_data(right, l_ty)?;
                ret(Value::Bool(left_data == right_data))
            }
            IntrinsicOp::AtomicStore => {
                if arguments.len() != 2 {
                    throw_ub!("invalid number of arguments for `AtomicStore` intrinsic");
                }
                let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = (arguments)
                    .index_at(0)
                    .0 else {
                    throw_ub!(
                        "invalid first argument to `AtomicStore` intrinsic: not a thin pointer"
                    );
                };
                let (val, ty) = (arguments).index_at(1);
                let LayoutStrategy::Sized(size, _) = ty.layout::<M::T>() else {
                    throw_ub!(
                        "invalid second argument to `AtomicStore` intrinsic: unsized type"
                    );
                };
                let Some(align) = Align::from_bytes(size.bytes()) else {
                    throw_ub!(
                        "invalid second argument to `AtomicStore` intrinsic: size not power of two"
                    );
                };
                if size > M::T::MAX_ATOMIC_SIZE {
                    throw_ub!(
                        "invalid second argument to `AtomicStore` intrinsic: size too big"
                    );
                }
                if ret_ty != unit_type() {
                    throw_ub!("invalid return type for `AtomicStore` intrinsic")
                }
                self.typed_store(ptr, val, ty, align, Atomicity::Atomic)?;
                ret(unit_value())
            }
            IntrinsicOp::AtomicLoad => {
                if arguments.len() != 1 {
                    throw_ub!("invalid number of arguments for `AtomicLoad` intrinsic");
                }
                let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = (arguments)
                    .index_at(0)
                    .0 else {
                    throw_ub!(
                        "invalid first argument to `AtomicLoad` intrinsic: not a thin pointer"
                    );
                };
                let size = ret_ty
                    .layout::<M::T>()
                    .expect_size("WF ensures intrinsic return types are sized");
                let Some(align) = Align::from_bytes(size.bytes()) else {
                    throw_ub!(
                        "invalid return type for `AtomicLoad` intrinsic: size not power of two"
                    );
                };
                if size > M::T::MAX_ATOMIC_SIZE {
                    throw_ub!(
                        "invalid return type for `AtomicLoad` intrinsic: size too big"
                    );
                }
                let val = self.typed_load(ptr, ret_ty, align, Atomicity::Atomic)?;
                ret(val)
            }
            IntrinsicOp::AtomicCompareExchange => {
                if arguments.len() != 3 {
                    throw_ub!(
                        "invalid number of arguments for `AtomicCompareExchange` intrinsic"
                    );
                }
                let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = (arguments)
                    .index_at(0)
                    .0 else {
                    throw_ub!(
                        "invalid first argument to `AtomicCompareExchange` intrinsic: not a thin pointer"
                    );
                };
                let (current, curr_ty) = (arguments).index_at(1);
                if curr_ty != ret_ty {
                    throw_ub!(
                        "invalid second argument to `AtomicCompareExchange` intrinsic: not same type as return value"
                    );
                }
                let (next, next_ty) = (arguments).index_at(2);
                if next_ty != ret_ty {
                    throw_ub!(
                        "invalid third argument to `AtomicCompareExchange` intrinsic: not same type as return value"
                    );
                }
                if !matches!(ret_ty, Type::Int(_)) {
                    throw_ub!(
                        "invalid return type for `Intrinis::AtomicCompareExchange`: only works with integers"
                    );
                }
                let size = ret_ty.layout::<M::T>().expect_size("`ret_ty` is an integer");
                let align = Align::from_bytes(size.bytes()).unwrap();
                if size > M::T::MAX_ATOMIC_SIZE {
                    throw_ub!(
                        "invalid return type for `AtomicCompareExchange` intrinsic: size too big"
                    );
                }
                let before = self.typed_load(ptr, ret_ty, align, Atomicity::Atomic)?;
                if current == before {
                    self.typed_store(ptr, next, ret_ty, align, Atomicity::Atomic)?;
                } else {}
                ret(before)
            }
            IntrinsicOp::AtomicFetchAndOp(op) => {
                if arguments.len() != 2 {
                    throw_ub!(
                        "invalid number of arguments for `AtomicFetchAndOp` intrinsic"
                    );
                }
                let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = (arguments)
                    .index_at(0)
                    .0 else {
                    throw_ub!(
                        "invalid first argument to `AtomicFetchAndOp` intrinsic: not a thin pointer"
                    );
                };
                let (other, other_ty) = (arguments).index_at(1);
                if other_ty != ret_ty {
                    throw_ub!(
                        "invalid second argument to `AtomicFetchAndOp` intrinsic: not same type as return value"
                    );
                }
                let Type::Int(int_ty) = ret_ty else {
                    throw_ub!(
                        "invalid return type for `AtomicFetchAndOp` intrinsic: only works with integers"
                    );
                };
                let size = ret_ty.layout::<M::T>().expect_size("`ret_ty` is an integer");
                let align = Align::from_bytes(size.bytes()).unwrap();
                if size > M::T::MAX_ATOMIC_SIZE {
                    throw_ub!(
                        "invalid return type for `AtomicFetchAndOp` intrinsic: size too big"
                    );
                }
                let previous = self.typed_load(ptr, ret_ty, align, Atomicity::Atomic)?;
                let Value::Int(other_int) = other else { unreachable!() };
                let Value::Int(previous_int) = previous else { unreachable!() };
                let next_int = Self::eval_int_bin_op(
                    op,
                    previous_int,
                    other_int,
                    int_ty,
                )?;
                let next = Value::Int(next_int);
                self.typed_store(ptr, next, ret_ty, align, Atomicity::Atomic)?;
                ret(previous)
            }
            IntrinsicOp::GetUnwindPayload => {
                if arguments.len() != 0 {
                    throw_ub!(
                        "invalid number of arguments for `GetUnwindPayload` intrinsic"
                    );
                }
                let Type::Ptr(ret_ptr_ty) = ret_ty else {
                    throw_ub!("invalid return type for `GetUnwindPayload` intrinsic");
                };
                if ret_ptr_ty.meta_kind() != PointerMetaKind::None {
                    throw_ub!("invalid return type for `GetUnwindPayload` intrinsic");
                }
                let Some(thin_pointer) = self.active_thread().unwind_payloads.last()
                else {
                    throw_ub!("GetUnwindPayload: the payload stack is empty");
                };
                let payload_pointer = Value::Ptr(Pointer {
                    thin_pointer,
                    metadata: None,
                });
                ret(payload_pointer)
            }
            IntrinsicOp::Lock(IntrinsicLockOp::Create) => {
                if arguments.len() > 0 {
                    throw_ub!("invalid number of arguments for `Create` lock intrinsic");
                }
                if !matches!(ret_ty, Type::Int(_)) {
                    throw_ub!("invalid return type for `Create` lock intrinsic")
                }
                let lock_id = self.lock_create();
                ret(Value::Int(lock_id))
            }
            IntrinsicOp::Lock(IntrinsicLockOp::Acquire) => {
                if arguments.len() != 1 {
                    throw_ub!(
                        "invalid number of arguments for `Acquire` lock intrinsic"
                    );
                }
                let Value::Int(lock_id) = (arguments).index_at(0).0 else {
                    throw_ub!("invalid first argument to `Acquire` lock intrinsic");
                };
                if ret_ty != unit_type() {
                    throw_ub!("invalid return type for `Acquire` lock intrinsic")
                }
                self.lock_acquire(lock_id)?;
                ret(unit_value())
            }
            IntrinsicOp::Lock(IntrinsicLockOp::Release) => {
                if arguments.len() != 1 {
                    throw_ub!(
                        "invalid number of arguments for `Release` lock intrinsic"
                    );
                }
                let Value::Int(lock_id) = (arguments).index_at(0).0 else {
                    throw_ub!("invalid first argument to `Release` lock intrinsic");
                };
                if ret_ty != unit_type() {
                    throw_ub!("invalid return type for `Release` lock intrinsic")
                }
                self.lock_release(lock_id)?;
                ret(unit_value())
            }
        }
    }
    fn exit(&self) -> NdResult<!> {
        self.mem.leak_check()?;
        throw_machine_stop!();
    }
    fn eval_print(
        &mut self,
        stream: DynWrite,
        arguments: List<(Value<M>, Type)>,
    ) -> Result {
        for (arg, _) in arguments {
            match arg {
                Value::Int(i) => write!(stream, "{}\n", i).unwrap(),
                Value::Bool(b) => write!(stream, "{}\n", b).unwrap(),
                _ => throw_ub!("unsupported value for printing"),
            }
        }
        ret(())
    }
    fn spawn(
        &mut self,
        func: Function,
        data_pointer: Value<M>,
        data_ptr_ty: Type,
    ) -> NdResult<ThreadId> {
        let args = list![(data_pointer, data_ptr_ty)];
        let thread_id = self.new_thread(func, args)?;
        self.synchronized_threads.insert(thread_id);
        ret(thread_id)
    }
    fn join(&mut self, thread_id: ThreadId) -> NdResult {
        let Some(thread) = self.threads.get(thread_id) else {
            throw_ub!("`Join` intrinsic: join non existing thread");
        };
        match thread.state {
            ThreadState::Terminated => {}
            _ => {
                self.threads
                    .mutate_at(
                        self.active_thread,
                        |thread| {
                            thread.state = ThreadState::BlockedOnJoin(thread_id);
                        },
                    );
            }
        };
        ret(())
    }
    fn load_raw_data(
        &mut self,
        ptr: Pointer<<M as Memory>::Provenance>,
        ptr_ty: PtrType,
    ) -> Result<List<u8>> {
        let PtrType::Ref { pointee, .. } = ptr_ty else {
            throw_ub!("invalid argument to `RawEq` intrinsic: not a reference");
        };
        let PointeeInfo { layout: LayoutStrategy::Sized(size, align), .. } = pointee
        else {
            throw_ub!("invalid argument to `RawEq` intrinsic: unsized pointee");
        };
        let bytes = self.mem.load(ptr.thin_pointer, size, align, Atomicity::None)?;
        let Some(data) = bytes.try_map(|byte| byte.data()) else {
            throw_ub!("invalid argument to `RawEq` intrinsic: byte is uninitialized");
        };
        Ok(data)
    }
    fn eval_terminator(&mut self, terminator: Terminator) -> NdResult {
        match terminator {
            Terminator::Goto(block_name) => {
                self.jump_to_block(block_name)?;
                ret(())
            }
            Terminator::Switch { value, cases, fallback } => {
                let Value::Int(value) = self.eval_value(value)?.0 else {
                    panic!("switch on a non-integer");
                };
                let next = cases.get(value).unwrap_or(fallback);
                self.jump_to_block(next)?;
                ret(())
            }
            Terminator::Unreachable => {
                throw_ub!("reached unreachable code");
            }
            Terminator::Call {
                callee,
                calling_convention: caller_conv,
                arguments,
                ret: ret_expr,
                next_block,
                unwind_block,
            } => {
                let (ret_place, ret_ty) = self.eval_place(ret_expr)?;
                self.prepare_for_inplace_passing(ret_place, ret_ty)?;
                let (callee_val, _) = self.eval_value(callee)?;
                let callee = self.fn_from_ptr(callee_val)?;
                let arguments = arguments.try_map(|arg| self.eval_argument(arg))?;
                self.eval_call(
                    callee,
                    caller_conv,
                    arguments,
                    (ret_place, ret_ty),
                    next_block,
                    unwind_block,
                )
            }
            Terminator::Return => {
                let mut frame = self.mutate_cur_stack(|stack| stack.pop().unwrap());
                let callee_ty = (frame.func.locals).index_at(frame.func.ret);
                let align = callee_ty
                    .layout::<M::T>()
                    .expect_align("the return value is a local and thus sized");
                let ret_val = self
                    .typed_load(
                        (frame.locals).index_at(frame.func.ret),
                        callee_ty,
                        align,
                        Atomicity::None,
                    )?;
                while let Some(local) = frame.locals.keys().next() {
                    frame.storage_dead(&mut self.mem, local)?;
                }
                self.mem.end_call(frame.extra)?;
                match frame.stack_pop_action {
                    StackPopAction::BottomOfStack => {
                        self.terminate_active_thread()?;
                    }
                    StackPopAction::BackToCaller {
                        ret_val_ptr: caller_ret_ptr,
                        next_block,
                        ..
                    } => {
                        assert!(self.active_thread().stack.len() > 0);
                        self.typed_store(
                            caller_ret_ptr,
                            ret_val,
                            callee_ty,
                            align,
                            Atomicity::None,
                        )?;
                        if let Some(next_block) = next_block {
                            self.jump_to_block(next_block)?;
                        } else {
                            throw_ub!(
                                "return from a function where caller did not specify next block"
                            );
                        }
                    }
                }
                ret(())
            }
            Terminator::StartUnwind { unwind_payload, unwind_block } => {
                let (
                    Value::Ptr(unwind_payload),
                    Type::Ptr(PtrType::Raw { meta_kind: PointerMetaKind::None }),
                ) = self.eval_value(unwind_payload)? else {
                    panic!("StartUnwind: the unwind payload is not a raw pointer");
                };
                self.mutate_active_thread(|thread| {
                    thread.unwind_payloads.push(unwind_payload.thin_pointer)
                });
                self.jump_to_block(unwind_block)?;
                ret(())
            }
            Terminator::StopUnwind(block_name) => {
                self.mutate_active_thread(|thread| -> Result<()> {
                    let Some(_) = thread.unwind_payloads.pop() else {
                        throw_ub!("StopUnwind: the payload stack is empty");
                    };
                    ret(())
                })?;
                self.jump_to_block(block_name)?;
                ret(())
            }
            Terminator::ResumeUnwind => {
                let mut frame = self.mutate_cur_stack(|stack| stack.pop().unwrap());
                while let Some(local) = frame.locals.keys().next() {
                    frame.storage_dead(&mut self.mem, local)?;
                }
                self.mem.end_call(frame.extra)?;
                match frame.stack_pop_action {
                    StackPopAction::BottomOfStack => {
                        throw_ub!(
                            "the function at the bottom of the stack must not unwind"
                        );
                    }
                    StackPopAction::BackToCaller { unwind_block, .. } => {
                        if let Some(unwind_block) = unwind_block {
                            self.jump_to_block(unwind_block)?;
                        } else {
                            throw_ub!(
                                "unwinding from a function where the caller did not specify an unwind_block"
                            );
                        }
                    }
                }
                ret(())
            }
            Terminator::Intrinsic {
                intrinsic,
                arguments,
                ret: ret_expr,
                next_block,
            } => {
                let (ret_place, ret_ty) = self.eval_place(ret_expr)?;
                let arguments = arguments.try_map(|arg| self.eval_value(arg))?;
                let value = self.eval_intrinsic(intrinsic, arguments, ret_ty)?;
                self.place_store(ret_place, value, ret_ty)?;
                if let Some(next_block) = next_block {
                    self.jump_to_block(next_block)?;
                } else {
                    throw_ub!(
                        "return from an intrinsic where caller did not specify next block"
                    );
                }
                ret(())
            }
        }
    }
    fn jump_to_block(&mut self, block: BbName) -> NdResult {
        self.try_mutate_cur_frame(|frame, _mem| {
            frame.jump_to_block(block);
            ret(())
        })
    }
    /// Prepare a place for being used in-place as a function argument or return value.
    fn prepare_for_inplace_passing(&mut self, place: Place<M>, ty: Type) -> NdResult {
        self.mem
            .deinit(
                place.ptr.thin_pointer,
                ty
                    .layout::<M::T>()
                    .expect_size("WF ensures arguments and return types are sized"),
                ty
                    .layout::<M::T>()
                    .expect_align("WF ensures arguments and return types are sized"),
            )?;
        ret(())
    }
    /// A helper function to deal with `ArgumentExpr`.
    fn eval_argument(&mut self, val: ArgumentExpr) -> NdResult<(Value<M>, Type)> {
        ret(
            match val {
                ArgumentExpr::ByValue(value) => self.eval_value(value)?,
                ArgumentExpr::InPlace(place) => {
                    let (place, ty) = self.eval_place(place)?;
                    let value = self.place_load(place, ty)?;
                    self.prepare_for_inplace_passing(place, ty)?;
                    (value, ty)
                }
            },
        )
    }
    /// Creates a stack frame for the given function, initializes the arguments,
    /// and ensures that calling convention and argument/return value ABIs are all matching up.
    fn create_frame(
        &mut self,
        func: Function,
        stack_pop_action: StackPopAction<M>,
        caller_conv: CallingConvention,
        caller_ret_ty: Type,
        caller_args: List<(Value<M>, Type)>,
    ) -> NdResult<StackFrame<M>> {
        let mut frame = StackFrame {
            func,
            locals: Map::new(),
            stack_pop_action,
            next_block: func.start,
            next_stmt: Int::ZERO,
            extra: M::new_call(),
        };
        frame.storage_live(&mut self.mem, func.ret)?;
        for arg_local in func.args {
            frame.storage_live(&mut self.mem, arg_local)?;
        }
        if caller_conv != func.calling_convention {
            throw_ub!("call ABI violation: calling conventions are not the same");
        }
        if !check_abi_compatibility(caller_ret_ty, (func.locals).index_at(func.ret)) {
            throw_ub!("call ABI violation: return types are not compatible");
        }
        if func.args.len() != caller_args.len() {
            throw_ub!("call ABI violation: number of arguments does not agree");
        }
        for (callee_local, (caller_val, caller_ty)) in func.args.zip(caller_args) {
            if !check_abi_compatibility(
                caller_ty,
                (func.locals).index_at(callee_local),
            ) {
                throw_ub!("call ABI violation: argument types are not compatible");
            }
            let align = caller_ty
                .layout::<M::T>()
                .expect_align("WF ensures function arguments are sized");
            self.typed_store(
                    (frame.locals).index_at(callee_local),
                    caller_val,
                    caller_ty,
                    align,
                    Atomicity::None,
                )
                .unwrap();
        }
        ret(frame)
    }
    fn eval_call(
        &mut self,
        callee: Function,
        caller_conv: CallingConvention,
        arguments: List<(Value<M>, Type)>,
        caller_ret: (Place<M>, Type),
        next_block: Option<BbName>,
        unwind_block: Option<BbName>,
    ) -> NdResult {
        let (caller_ret_place, caller_ret_ty) = caller_ret;
        let stack_pop_action = StackPopAction::BackToCaller {
            next_block,
            unwind_block,
            ret_val_ptr: caller_ret_place.ptr.thin_pointer,
        };
        let frame = self
            .create_frame(
                callee,
                stack_pop_action,
                caller_conv,
                caller_ret_ty,
                arguments,
            )?;
        self.mutate_cur_stack(|stack| stack.push(frame));
        ret(())
    }
    fn terminate_active_thread(&mut self) -> NdResult {
        let active = self.active_thread;
        if active == 0 {
            throw_ub!("the start function must not return");
        }
        self.threads
            .mutate_at(
                active,
                |thread| {
                    assert!(thread.stack.len() == 0);
                    thread.state = ThreadState::Terminated;
                },
            );
        for i in ThreadId::ZERO..self.threads.len() {
            if (self.threads).index_at(i).state == ThreadState::BlockedOnJoin(active) {
                self.synchronized_threads.insert(i);
                self.threads.mutate_at(i, |thread| thread.state = ThreadState::Enabled)
            }
        }
        ret(())
    }
    fn eval_statement(&mut self, statement: Statement) -> NdResult {
        match statement {
            Statement::Assign { destination, source } => {
                let (place, ty) = self.eval_place(destination)?;
                let (val, _) = self.eval_value(source)?;
                self.place_store(place, val, ty)?;
                ret(())
            }
            Statement::PlaceMention(place) => {
                self.eval_place(place)?;
                ret(())
            }
            Statement::SetDiscriminant { destination, value } => {
                let (place, Type::Enum { variants, .. }) = self.eval_place(destination)?
                else {
                    panic!(
                        "setting the discriminant type of a non-enum contradicts well-formedness"
                    );
                };
                if !place.aligned {
                    throw_ub!(
                        "setting the discriminant of a place based on a misaligned pointer"
                    );
                }
                let tagger = match variants.get(value) {
                    Some(Variant { tagger, .. }) => tagger,
                    None => panic!("setting an invalid discriminant ({value})"),
                };
                let accessor = |offset: Offset, bytes| {
                    let ptr = self
                        .ptr_offset_inbounds(place.ptr.thin_pointer, offset.bytes())?;
                    self.mem.store(ptr, bytes, Align::ONE, Atomicity::None)
                };
                encode_discriminant::<M>(accessor, tagger)?;
                ret(())
            }
            Statement::Validate { place, fn_entry } => {
                let (place, ty) = self.eval_place(place)?;
                let val = self.place_load(place, ty)?;
                let val = self.retag_val(val, ty, fn_entry)?;
                self.place_store(place, val, ty)?;
                ret(())
            }
            Statement::Deinit { place } => {
                let (p, ty) = self.eval_place(place)?;
                if !p.aligned {
                    throw_ub!("de-initializing a place based on a misaligned pointer");
                }
                self.mem
                    .deinit(
                        p.ptr.thin_pointer,
                        ty.layout::<M::T>().expect_size("WF ensures deinits are sized"),
                        Align::ONE,
                    )?;
                ret(())
            }
            Statement::StorageLive(local) => {
                self.try_mutate_cur_frame(|frame, mem| {
                    frame.storage_live(mem, local)
                })
            }
            Statement::StorageDead(local) => {
                self.try_mutate_cur_frame(|frame, mem| {
                    frame.storage_dead(mem, local)
                })
            }
        }
    }
    fn place_store(&mut self, place: Place<M>, val: Value<M>, ty: Type) -> Result {
        if !place.aligned {
            throw_ub!("storing to a place based on a misaligned pointer");
        }
        self.typed_store(place.ptr.thin_pointer, val, ty, Align::ONE, Atomicity::None)?;
        ret(())
    }
    /// Find all pointers in this value, ensure they are valid, and retag them.
    fn retag_val(
        &mut self,
        val: Value<M>,
        ty: Type,
        fn_entry: bool,
    ) -> Result<Value<M>> {
        ret(
            match (val, ty) {
                (Value::Int(..) | Value::Bool(..) | Value::Union(..), _) => val,
                (Value::Ptr(ptr), Type::Ptr(ptr_type)) => {
                    let lookup = self.vtable_lookup();
                    let val = self
                        .mutate_cur_frame(|frame, mem| {
                            mem.retag_ptr(
                                &mut frame.extra,
                                ptr,
                                ptr_type,
                                fn_entry,
                                frame.func.implicit_writes,
                                lookup,
                            )
                        })?;
                    Value::Ptr(val)
                }
                (Value::Tuple(vals), Type::Tuple { sized_fields, .. }) => {
                    Value::Tuple(
                        vals
                            .zip(sized_fields)
                            .try_map(|(val, (_offset, ty))| {
                                self.retag_val(val, ty, fn_entry)
                            })?,
                    )
                }
                (Value::Tuple(vals), Type::Array { elem: ty, .. }) => {
                    let ty = ty.extract();
                    Value::Tuple(vals.try_map(|val| self.retag_val(val, ty, fn_entry))?)
                }
                (Value::Variant { discriminant, data }, Type::Enum { variants, .. }) => {
                    let data = data.extract();
                    Value::Variant {
                        discriminant,
                        data: libspecr::hidden::GcCow::new(
                            self
                                .retag_val(
                                    data,
                                    (variants).index_at(discriminant).ty,
                                    fn_entry,
                                )?,
                        ),
                    }
                }
                _ => panic!("this value does not have that type"),
            },
        )
    }
    fn eval_un_op(
        &self,
        operator: UnOp,
        (operand, op_ty): (Value<M>, Type),
    ) -> Result<(Value<M>, Type)> {
        match operator {
            UnOp::Int(op) => {
                let Type::Int(int_ty) = op_ty else {
                    panic!("non-integer input to integer operation")
                };
                let Value::Int(operand) = operand else {
                    panic!("non-integer input to integer operation")
                };
                let ret_ty = match op {
                    IntUnOp::CountOnes => {
                        IntType {
                            signed: Unsigned,
                            size: Size::from_bytes(4).unwrap(),
                        }
                    }
                    _ => int_ty,
                };
                let result = Value::Int(Self::eval_int_un_op(op, operand, int_ty)?);
                self.check_value(result, Type::Int(ret_ty))
                    .expect(
                        "sanity check: result of UnOp::Int does not fit in the return type",
                    );
                ret((result, Type::Int(ret_ty)))
            }
            UnOp::Cast(cast_op) => ret(self.eval_cast_op(cast_op, (operand, op_ty))?),
            UnOp::GetThinPointer => {
                let Value::Ptr(ptr) = operand else {
                    panic!("non-pointer GetThinPointer")
                };
                let thin_ptr = Pointer { metadata: None, ..ptr };
                let thin_ptr_ty = PtrType::Raw {
                    meta_kind: PointerMetaKind::None,
                };
                ret((Value::Ptr(thin_ptr), Type::Ptr(thin_ptr_ty)))
            }
            UnOp::GetMetadata => {
                let Value::Ptr(ptr) = operand else { panic!("non-pointer GetMetadata") };
                let Type::Ptr(ptr_ty) = op_ty else { panic!("non-pointer GetMetadata") };
                let meta_value = ptr_ty.meta_kind().encode_as_value::<M>(ptr.metadata);
                let meta_ty = ptr_ty.meta_kind().ty::<M::T>();
                self.check_value(meta_value, meta_ty)
                    .expect("GetMetadata: sanity check, returned meta is well-formed");
                ret((meta_value, meta_ty))
            }
            UnOp::ComputeSize(ty) => {
                let meta = ty.meta_kind().decode_value::<M>(operand);
                let size = self.compute_size(ty.layout::<M::T>(), meta);
                ret((Value::Int(size.bytes()), Type::Int(IntType::usize_ty::<M::T>())))
            }
            UnOp::ComputeAlign(ty) => {
                let meta = ty.meta_kind().decode_value::<M>(operand);
                let align = self.compute_align(ty.layout::<M::T>(), meta);
                ret((Value::Int(align.bytes()), Type::Int(IntType::usize_ty::<M::T>())))
            }
            UnOp::VTableMethodLookup(method) => {
                let (Value::Ptr(ptr), Type::Ptr(_ptr_ty)) = (operand, op_ty) else {
                    panic!("vtable lookup on non-pointer");
                };
                let vtable = self.vtable_lookup()(ptr.thin_pointer);
                let fn_name = (vtable.methods).index_at(method);
                let fn_ptr = Value::Ptr((self.fn_ptrs).index_at(fn_name).widen(None));
                ret((fn_ptr, Type::Ptr(PtrType::FnPtr)))
            }
        }
    }
    /// Perform the operation on the mathematical integer `operand`,
    /// but correcting for non-pure effects dependent of the `operand_ty`.
    fn eval_int_un_op(op: IntUnOp, operand: Int, operand_ty: IntType) -> Result<Int> {
        use IntUnOp::*;
        ret(
            match op {
                Neg => operand_ty.bring_in_bounds(-operand),
                BitNot => operand_ty.bring_in_bounds(!operand),
                CountOnes => Self::eval_count_ones(operand, operand_ty),
            },
        )
    }
    fn eval_count_ones(operand: Int, int_ty: IntType) -> Int {
        let mut ones = Int::ZERO;
        let mut remaining_bits = operand;
        for _ in Int::ZERO..int_ty.size.bits() {
            ones += remaining_bits & Int::ONE;
            remaining_bits >>= 1;
        }
        ones
    }
    fn eval_cast_op(
        &self,
        cast_op: CastOp,
        (operand, old_ty): (Value<M>, Type),
    ) -> Result<(Value<M>, Type)> {
        use CastOp::*;
        match cast_op {
            IntToInt(int_ty) => {
                let Value::Int(operand) = operand else {
                    panic!("non-integer input to int-to-int cast")
                };
                let result = int_ty.bring_in_bounds(operand);
                ret((Value::Int(result), Type::Int(int_ty)))
            }
            Transmute(new_ty) => {
                if old_ty.layout::<M::T>().expect_size("WF ensures transmutes are sized")
                    != new_ty
                        .layout::<M::T>()
                        .expect_size("WF ensures transmutes are sized")
                {
                    throw_ub!("transmute between types of different size")
                }
                let val = self.transmute(operand, old_ty, new_ty)?;
                ret((val, new_ty))
            }
        }
    }
    fn eval_bin_op(
        &self,
        operator: BinOp,
        (left, l_ty): (Value<M>, Type),
        (right, _r_ty): (Value<M>, Type),
    ) -> Result<(Value<M>, Type)> {
        match operator {
            BinOp::Int(op) => {
                let Type::Int(int_ty) = l_ty else {
                    panic!("non-integer input to integer operation")
                };
                let Value::Int(left) = left else {
                    panic!("non-integer input to integer operation")
                };
                let Value::Int(right) = right else {
                    panic!("non-integer input to integer operation")
                };
                let result = Self::eval_int_bin_op(op, left, right, int_ty)?;
                let result = int_ty.bring_in_bounds(result);
                ret((Value::Int(result), Type::Int(int_ty)))
            }
            BinOp::IntWithOverflow(op) => {
                let Type::Int(int_ty) = l_ty else {
                    panic!("non-integer input to integer operation")
                };
                let Value::Int(left) = left else {
                    panic!("non-integer input to integer operation")
                };
                let Value::Int(right) = right else {
                    panic!("non-integer input to integer operation")
                };
                let result = match op {
                    IntBinOpWithOverflow::Add => left + right,
                    IntBinOpWithOverflow::Sub => left - right,
                    IntBinOpWithOverflow::Mul => left * right,
                };
                let overflow = !int_ty.can_represent(result);
                let result = int_ty.bring_in_bounds(result);
                let value = Value::Tuple(
                    list![Value::Int::< M > (result), Value::Bool::< M > (overflow)],
                );
                let ty = int_ty.with_overflow::<M::T>();
                ret((value, ty))
            }
            BinOp::Rel(rel_op) => {
                let ord = match (l_ty, left, right) {
                    (Type::Int(_), Value::Int(left), Value::Int(right)) => {
                        left.cmp(&right)
                    }
                    (Type::Bool, Value::Bool(left), Value::Bool(right)) => {
                        left.cmp(&right)
                    }
                    (Type::Ptr(_), Value::Ptr(left), Value::Ptr(right)) => {
                        Self::compare_ptr(left, right)
                    }
                    _ => {
                        panic!(
                            "relational operator on incomparable type or value-type mismatch"
                        )
                    }
                };
                ret(Self::eval_rel_op(rel_op, ord))
            }
            BinOp::PtrOffset { inbounds } => {
                let Value::Ptr(Pointer { thin_pointer: left, metadata: None }) = left
                else { panic!("non-thin-pointer left input to `PtrOffset`") };
                let Value::Int(right) = right else {
                    panic!("non-integer right input to `PtrOffset`")
                };
                let offset_ptr = if inbounds {
                    self.ptr_offset_inbounds(left, right)?
                } else {
                    self.ptr_offset_wrapping(left, right)
                };
                ret((Value::Ptr(offset_ptr.widen(None)), l_ty))
            }
            BinOp::PtrOffsetFrom { inbounds, nonneg } => {
                let Value::Ptr(Pointer { thin_pointer: left, metadata: None }) = left
                else { panic!("non-thin-pointer left input to `PtrOffsetFrom`") };
                let Value::Ptr(Pointer { thin_pointer: right, metadata: None }) = right
                else { panic!("non-thin-pointer right input to `PtrOffsetFrom`") };
                let distance = left.addr - right.addr;
                let distance = if inbounds {
                    self.mem.signed_dereferenceable(left, -distance)?;
                    self.mem.signed_dereferenceable(right, distance)?;
                    distance
                } else {
                    distance.bring_in_bounds(Signed, M::T::PTR_SIZE)
                };
                if nonneg && distance < Int::ZERO {
                    throw_ub!("PtrOffsetFrom: negative result with `nonneg` flag set");
                }
                let isize_int = IntType {
                    signed: Signed,
                    size: M::T::PTR_SIZE,
                };
                ret((Value::Int(distance), Type::Int(isize_int)))
            }
            BinOp::ConstructWidePointer(ptr_ty) => {
                let Value::Ptr(Pointer { thin_pointer, metadata: None }) = left else {
                    panic!("non-thin-pointer left input to `ConstructWidePointer`")
                };
                let metadata = ptr_ty.meta_kind().decode_value::<M>(right);
                let wide_ptr = Value::Ptr(Pointer { thin_pointer, metadata });
                self.check_value(wide_ptr, Type::Ptr(ptr_ty))?;
                ret((wide_ptr, Type::Ptr(ptr_ty)))
            }
        }
    }
    fn eval_int_bin_op(
        op: IntBinOp,
        left: Int,
        right: Int,
        left_ty: IntType,
    ) -> Result<Int> {
        use IntBinOp::*;
        ret(
            match op {
                Add => left + right,
                AddUnchecked => {
                    let result = left + right;
                    if !left_ty.can_represent(result) {
                        throw_ub!("overflow in unchecked add");
                    }
                    result
                }
                Sub => left - right,
                SubUnchecked => {
                    let result = left - right;
                    if !left_ty.can_represent(result) {
                        throw_ub!("overflow in unchecked sub");
                    }
                    result
                }
                Mul => left * right,
                MulUnchecked => {
                    let result = left * right;
                    if !left_ty.can_represent(result) {
                        throw_ub!("overflow in unchecked mul");
                    }
                    result
                }
                Div => {
                    if right == 0 {
                        throw_ub!("division by zero");
                    }
                    let result = left / right;
                    if !left_ty.can_represent(result) {
                        throw_ub!("overflow in division");
                    }
                    result
                }
                DivExact => {
                    if right == 0 {
                        throw_ub!("division by zero");
                    }
                    let result = left / right;
                    if !left_ty.can_represent(result) {
                        throw_ub!("overflow in division");
                    }
                    if left % right != 0 {
                        throw_ub!("non-zero remainder in exact division");
                    }
                    result
                }
                Rem => {
                    if right == 0 {
                        throw_ub!("modulus of remainder is zero");
                    }
                    if !left_ty.can_represent(left / right) {
                        throw_ub!("overflow in remainder");
                    }
                    left % right
                }
                Shl | Shr => {
                    let bits = left_ty.size.bits();
                    let offset = right.rem_euclid(bits);
                    match op {
                        Shl => left << offset,
                        Shr => left >> offset,
                        _ => panic!(),
                    }
                }
                ShlUnchecked | ShrUnchecked => {
                    let bits = left_ty.size.bits();
                    if right < 0 || right >= bits {
                        throw_ub!("overflow in unchecked shift");
                    }
                    match op {
                        ShlUnchecked => left << right,
                        ShrUnchecked => left >> right,
                        _ => panic!(),
                    }
                }
                BitAnd => left & right,
                BitOr => left | right,
                BitXor => left ^ right,
            },
        )
    }
    /// Turns the ordering from the comparasion result into a value, depending on the operation.
    fn eval_rel_op(rel: RelOp, ord: std::cmp::Ordering) -> (Value<M>, Type) {
        use RelOp::*;
        match rel {
            Lt => (Value::Bool(ord.is_lt()), Type::Bool),
            Gt => (Value::Bool(ord.is_gt()), Type::Bool),
            Le => (Value::Bool(ord.is_le()), Type::Bool),
            Ge => (Value::Bool(ord.is_ge()), Type::Bool),
            Eq => (Value::Bool(ord.is_eq()), Type::Bool),
            Ne => (Value::Bool(ord.is_ne()), Type::Bool),
            Cmp => {
                let val = match ord {
                    std::cmp::Ordering::Less => -1,
                    std::cmp::Ordering::Equal => 0,
                    std::cmp::Ordering::Greater => 1,
                };
                (Value::Int(Int::from(val)), Type::Int(IntType::I8))
            }
        }
    }
    /// Compares two pointers including their metadata, but ignoring provenance.
    fn compare_ptr(
        left: Pointer<M::Provenance>,
        right: Pointer<M::Provenance>,
    ) -> std::cmp::Ordering {
        let thin_cmp = left.thin_pointer.addr.cmp(&right.thin_pointer.addr);
        let meta_cmp = match (left.metadata, right.metadata) {
            (None, None) => std::cmp::Ordering::Equal,
            (Some(PointerMeta::ElementCount(l)), Some(PointerMeta::ElementCount(r))) => {
                l.cmp(&r)
            }
            (
                Some(PointerMeta::VTablePointer(l)),
                Some(PointerMeta::VTablePointer(r)),
            ) => l.addr.cmp(&r.addr),
            _ => panic!("unmatching metadata in wide pointer comparasion"),
        };
        thin_cmp.then(meta_cmp)
    }
    /// Perform a wrapping offset on the given pointer. (Can never fail.)
    fn ptr_offset_wrapping(
        &self,
        ptr: ThinPointer<M::Provenance>,
        offset: Int,
    ) -> ThinPointer<M::Provenance> {
        ptr.wrapping_offset::<M::T>(offset)
    }
    /// Perform in-bounds arithmetic on the given pointer. This must not wrap,
    /// and the offset must stay in bounds of a single allocation.
    fn ptr_offset_inbounds(
        &self,
        ptr: ThinPointer<M::Provenance>,
        offset: Int,
    ) -> Result<ThinPointer<M::Provenance>> {
        self.mem.signed_dereferenceable(ptr, offset)?;
        assert!(offset.in_bounds(Signed, M::T::PTR_SIZE));
        assert!((ptr.addr + offset).in_bounds(Unsigned, M::T::PTR_SIZE));
        ret(ThinPointer {
            addr: ptr.addr + offset,
            ..ptr
        })
    }
    pub fn lock_create(&mut self) -> LockId {
        let id = self.locks.len();
        self.locks.push(LockState::Unlocked);
        id
    }
    pub fn lock_acquire(&mut self, lock_id: LockId) -> Result {
        let active = self.active_thread;
        let Some(lock) = self.locks.get(lock_id) else {
            throw_ub!("acquiring non-existing lock");
        };
        match lock {
            LockState::Unlocked => {
                self.locks
                    .mutate_at(
                        lock_id,
                        |lock_state| {
                            *lock_state = LockState::LockedBy(active);
                        },
                    );
            }
            LockState::LockedBy(_) => {
                self.threads
                    .mutate_at(
                        active,
                        |thread| {
                            thread.state = ThreadState::BlockedOnLock(lock_id);
                        },
                    );
            }
        }
        ret(())
    }
    pub fn lock_release(&mut self, lock_id: LockId) -> NdResult {
        let active = self.active_thread;
        let Some(lock) = self.locks.get(lock_id) else {
            throw_ub!("releasing non-existing lock");
        };
        match lock {
            LockState::LockedBy(thread_id) if thread_id == active => {
                if self
                    .threads
                    .any(|thread| thread.state == ThreadState::BlockedOnLock(lock_id))
                {
                    let distr = libspecr::IntDistribution {
                        start: Int::ZERO,
                        end: Int::from(self.threads.len()),
                        divisor: Int::ONE,
                    };
                    let acquirer_id: ThreadId = pick(
                        distr,
                        |id: ThreadId| {
                            let Some(thread) = self.threads.get(id) else {
                                return false;
                            };
                            thread.state == ThreadState::BlockedOnLock(lock_id)
                        },
                    )?;
                    self.threads
                        .mutate_at(
                            acquirer_id,
                            |thread| {
                                thread.state = ThreadState::Enabled;
                            },
                        );
                    self.synchronized_threads.insert(acquirer_id);
                    self.locks
                        .mutate_at(
                            lock_id,
                            |lock| {
                                *lock = LockState::LockedBy(acquirer_id);
                            },
                        );
                } else {
                    self.locks
                        .mutate_at(
                            lock_id,
                            |lock| {
                                *lock = LockState::Unlocked;
                            },
                        );
                }
                ret(())
            }
            _ => throw_ub!("releasing non-acquired lock"),
        }
    }
    /// Evaluate a well-formed value expression to a value.
    /// The result value will always be well-formed for the given type.
    /// Calling this with a non-well-formed expression or it returning a non-well-formed value is a spec bug.
    fn eval_value(&mut self, val: ValueExpr) -> Result<(Value<M>, Type)> {
        match val {
            ValueExpr::Constant(constant, ty) => ret((self.eval_constant(constant)?, ty)),
            ValueExpr::Tuple(exprs, ty) => {
                let vals = exprs.try_map(|e| self.eval_value(e))?.map(|e| e.0);
                ret((Value::Tuple(vals), ty))
            }
            ValueExpr::Union { field, expr, union_ty } => {
                let expr = expr.extract();
                {
                    let Type::Union { fields, size, .. } = union_ty else {
                        panic!("ValueExpr::Union requires union type")
                    };
                    let (offset, expr_ty) = (fields).index_at(field);
                    let mut data = list![AbstractByte::Uninit; size.bytes()];
                    let (val, _) = self.eval_value(expr)?;
                    data.write_subslice_at_index(
                        offset.bytes(),
                        expr_ty.encode::<M>(val),
                    );
                    ret((union_ty.decode(data).unwrap(), union_ty))
                }
            }
            ValueExpr::Variant { enum_ty, discriminant, data } => {
                let data = data.extract();
                {
                    ret((
                        Value::Variant {
                            discriminant,
                            data: libspecr::hidden::GcCow::new(self.eval_value(data)?.0),
                        },
                        enum_ty,
                    ))
                }
            }
            ValueExpr::GetDiscriminant { place } => {
                let place = place.extract();
                {
                    let (place, ty) = self.eval_place(place)?;
                    let Type::Enum { discriminator, discriminant_ty, .. } = ty else {
                        panic!("ValueExpr::GetDiscriminant requires enum type");
                    };
                    if !place.aligned {
                        throw_ub!(
                            "Getting the discriminant of a place based on a misaligned pointer."
                        );
                    }
                    let accessor = |idx: Offset, size: Size| {
                        let ptr = self
                            .ptr_offset_inbounds(place.ptr.thin_pointer, idx.bytes())?;
                        self.mem.load(ptr, size, Align::ONE, Atomicity::None)
                    };
                    let Some(discriminant) = decode_discriminant::<
                        M,
                    >(accessor, discriminator)? else {
                        throw_ub!(
                            "ValueExpr::GetDiscriminant encountered invalid discriminant."
                        );
                    };
                    ret((Value::Int(discriminant), Type::Int(discriminant_ty)))
                }
            }
            ValueExpr::Load { source } => {
                let source = source.extract();
                {
                    let (place, ty) = self.eval_place(source)?;
                    let v = self.place_load(place, ty)?;
                    ret((v, ty))
                }
            }
            ValueExpr::AddrOf { target, ptr_ty } => {
                let target = target.extract();
                {
                    let (place, _ty) = self.eval_place(target)?;
                    self.check_value(Value::Ptr(place.ptr), Type::Ptr(ptr_ty))?;
                    let lookup = self.vtable_lookup();
                    let ptr = self
                        .mutate_cur_frame(|frame, mem| {
                            mem.retag_ptr(
                                &mut frame.extra,
                                place.ptr,
                                ptr_ty,
                                false,
                                true,
                                lookup,
                            )
                        })?;
                    ret((Value::Ptr(ptr), Type::Ptr(ptr_ty)))
                }
            }
            ValueExpr::UnOp { operator, operand } => {
                let operand = operand.extract();
                {
                    use lang::UnOp::*;
                    let operand = self.eval_value(operand)?;
                    ret(self.eval_un_op(operator, operand)?)
                }
            }
            ValueExpr::BinOp { operator, left, right } => {
                let right = right.extract();
                let left = left.extract();
                {
                    use lang::BinOp::*;
                    let left = self.eval_value(left)?;
                    let right = self.eval_value(right)?;
                    ret(self.eval_bin_op(operator, left, right)?)
                }
            }
        }
    }
    /// converts `Constant` to their `Value` counterpart.
    fn eval_constant(&mut self, constant: Constant) -> Result<Value<M>> {
        ret(
            match constant {
                Constant::Int(i) => Value::Int(i),
                Constant::Bool(b) => Value::Bool(b),
                Constant::GlobalPointer(relocation) => {
                    let ptr = (self.global_ptrs)
                        .index_at(relocation.name)
                        .wrapping_offset::<M::T>(relocation.offset.bytes());
                    Value::Ptr(ptr.widen(None))
                }
                Constant::FnPointer(fn_name) => {
                    let ptr = (self.fn_ptrs).index_at(fn_name);
                    Value::Ptr(ptr.widen(None))
                }
                Constant::VTablePointer(vtable_name) => {
                    let ptr = (self.vtable_ptrs).index_at(vtable_name);
                    Value::Ptr(ptr.widen(None))
                }
                Constant::PointerWithoutProvenance(addr) => {
                    Value::Ptr(
                        ThinPointer {
                            addr,
                            provenance: None,
                        }
                            .widen(None),
                    )
                }
            },
        )
    }
    fn place_load(&mut self, place: Place<M>, ty: Type) -> Result<Value<M>> {
        if !place.aligned {
            throw_ub!("loading from a place based on a misaligned pointer");
        }
        ret(self.typed_load(place.ptr.thin_pointer, ty, Align::ONE, Atomicity::None)?)
    }
    /// Evaluate a place expression to a place.
    ///
    /// Like a raw pointer, the result can be misaligned or null!
    fn eval_place(&mut self, place: PlaceExpr) -> Result<(Place<M>, Type)> {
        match place {
            PlaceExpr::Local(name) => {
                let ty = (self.cur_frame().func.locals).index_at(name);
                let Some(ptr) = self.cur_frame().locals.get(name) else {
                    throw_ub!("access to a dead local");
                };
                ret((
                    Place {
                        ptr: ptr.widen(None),
                        aligned: true,
                    },
                    ty,
                ))
            }
            PlaceExpr::Deref { operand, ty } => {
                let operand = operand.extract();
                {
                    let (Value::Ptr(ptr), Type::Ptr(ptr_type)) = self
                        .eval_value(operand)? else {
                        panic!("dereferencing a non-pointer")
                    };
                    if let Some(pointee) = ptr_type.safe_pointee() {
                        assert!(
                            self.compute_align(pointee.layout, ptr.metadata)
                            .is_aligned(ptr.thin_pointer.addr)
                        );
                        self.mem
                            .dereferenceable(
                                ptr.thin_pointer,
                                self.compute_size(pointee.layout, ptr.metadata),
                            )?;
                    }
                    let aligned = self
                        .compute_align(ty.layout::<M::T>(), ptr.metadata)
                        .is_aligned(ptr.thin_pointer.addr);
                    ret((Place { ptr, aligned }, ty))
                }
            }
            PlaceExpr::Field { root, field } => {
                let root = root.extract();
                {
                    let (root, ty) = self.eval_place(root)?;
                    let (offset, field_ty) = match ty {
                        Type::Tuple {
                            sized_fields,
                            unsized_field,
                            sized_head_layout,
                        } => {
                            let unsized_field = unsized_field.extract();
                            {
                                if field >= 0 && field < sized_fields.len() {
                                    (sized_fields).index_at(field)
                                } else if field == sized_fields.len() {
                                    let tail_ty = unsized_field
                                        .expect("field projection to non-existing unsized tail");
                                    let tail_align = self
                                        .compute_align(tail_ty.layout::<M::T>(), root.ptr.metadata);
                                    let offset = sized_head_layout.tail_offset(tail_align);
                                    (offset, tail_ty)
                                } else {
                                    panic!("field projection to invalid field");
                                }
                            }
                        }
                        Type::Union { fields, .. } => (fields).index_at(field),
                        _ => panic!("field projection on non-projectable type"),
                    };
                    assert!(
                        offset <= self.compute_size(ty.layout::< M::T > (), root.ptr
                        .metadata)
                    );
                    let ptr = self
                        .ptr_offset_inbounds(root.ptr.thin_pointer, offset.bytes())?;
                    let ptr = if !field_ty.layout::<M::T>().is_sized() {
                        ptr.widen(root.ptr.metadata)
                    } else {
                        ptr.widen(None)
                    };
                    ret((Place { ptr, ..root }, field_ty))
                }
            }
            PlaceExpr::Index { root, index } => {
                let root = root.extract();
                let index = index.extract();
                {
                    let (root, ty) = self.eval_place(root)?;
                    let (Value::Int(index), _) = self.eval_value(index)? else {
                        panic!("non-integer operand for array index")
                    };
                    let (elem_ty, count) = match ty {
                        Type::Array { elem, count } => {
                            let elem = elem.extract();
                            (elem, count)
                        }
                        Type::Slice { elem } => {
                            let elem = elem.extract();
                            {
                                let Some(PointerMeta::ElementCount(count)) = root
                                    .ptr
                                    .metadata else {
                                    panic!(
                                        "eval_place should always return a ptr which matches meta for the LayoutStrategy of ty"
                                    );
                                };
                                (elem, count)
                            }
                        }
                        _ => panic!("index projection on non-indexable type"),
                    };
                    if index < 0 || index >= count {
                        throw_ub!("access to out-of-bounds index");
                    }
                    let elem_size = elem_ty
                        .layout::<M::T>()
                        .expect_size("WF ensures array & slice elements are sized");
                    let offset = index * elem_size;
                    assert!(
                        offset <= self.compute_size(ty.layout::< M::T > (), root.ptr
                        .metadata),
                        "sanity check: the indexed offset should not be outside what the type allows."
                    );
                    let ptr = self
                        .ptr_offset_inbounds(root.ptr.thin_pointer, offset.bytes())?;
                    ret((
                        Place {
                            ptr: ptr.widen(None),
                            ..root
                        },
                        elem_ty,
                    ))
                }
            }
            PlaceExpr::Downcast { root, discriminant } => {
                let root = root.extract();
                {
                    let (root, ty) = self.eval_place(root)?;
                    let var_ty = match ty {
                        Type::Enum { variants, .. } => {
                            (variants).index_at(discriminant).ty
                        }
                        _ => panic!("enum downcast on non-enum"),
                    };
                    ret((root, var_ty))
                }
            }
        }
    }
}
impl<M: Memory + libspecr::hidden::Obj> Thread<M> {
    fn cur_frame(&self) -> StackFrame<M> {
        self.stack.last().unwrap()
    }
    fn mutate_cur_frame<O: libspecr::hidden::Obj>(
        &mut self,
        f: impl FnOnce(&mut StackFrame<M>) -> O,
    ) -> O {
        if self.stack.is_empty() {
            panic!("`mutate_cur_frame` called on empty stack!");
        }
        let last_idx = self.stack.len() - 1;
        self.stack.mutate_at(last_idx, f)
    }
    fn try_mutate_cur_frame<O: libspecr::hidden::Obj>(
        &mut self,
        f: impl FnOnce(&mut StackFrame<M>) -> NdResult<O>,
    ) -> NdResult<O> {
        if self.stack.is_empty() {
            panic!("`try_mutate_cur_frame` called on empty stack!");
        }
        let last_idx = self.stack.len() - 1;
        self.stack.try_mutate_at(last_idx, f)
    }
}
impl<M: Memory + libspecr::hidden::Obj> StackFrame<M> {
    /// jump to the beginning of the given block.
    fn jump_to_block(&mut self, b: BbName) {
        self.next_block = b;
        self.next_stmt = Int::ZERO;
    }
    fn storage_live(
        &mut self,
        mem: &mut ConcurrentMemory<M>,
        local: LocalName,
    ) -> NdResult {
        self.storage_dead(mem, local)?;
        let pointee_size = (self.func.locals)
            .index_at(local)
            .layout::<M::T>()
            .expect_size("WF ensures all locals are sized");
        let pointee_align = (self.func.locals)
            .index_at(local)
            .layout::<M::T>()
            .expect_align("WF ensures all locals are sized");
        let ptr = mem.allocate(AllocationKind::Stack, pointee_size, pointee_align)?;
        self.locals.insert(local, ptr);
        ret(())
    }
    fn storage_dead(
        &mut self,
        mem: &mut ConcurrentMemory<M>,
        local: LocalName,
    ) -> NdResult {
        let pointee_size = (self.func.locals)
            .index_at(local)
            .layout::<M::T>()
            .expect_size("WF ensures all locals are sized");
        let pointee_align = (self.func.locals)
            .index_at(local)
            .layout::<M::T>()
            .expect_align("WF ensures all locals are sized");
        if let Some(ptr) = self.locals.remove(local) {
            mem.deallocate(ptr, AllocationKind::Stack, pointee_size, pointee_align)?;
        }
        ret(())
    }
}
impl Type {
    /// Decode a list of bytes into a value.
    ///
    /// This can fail if `bytes` is not a valid encoding for the type,
    /// which typically means Undefined Behavior.
    /// Assumes `self` is well formed and `bytes.len()` matches the types size (violating this is a spec bug).
    fn decode<M: Memory + libspecr::hidden::Obj>(
        self,
        bytes: List<AbstractByte<M::Provenance>>,
    ) -> Option<Value<M>> {
        match self {
            Type::Bool => {
                if bytes.len() != 1 {
                    panic!("decode of Type::Bool with invalid length");
                }
                ret(
                    match (bytes).index_at(0) {
                        AbstractByte::Init(0, _) => Value::Bool(false),
                        AbstractByte::Init(1, _) => Value::Bool(true),
                        _ => throw!(),
                    },
                )
            }
            Type::Int(IntType { signed, size }) => {
                if bytes.len() != size.bytes() {
                    panic!("decode of Type::Int with invalid length");
                }
                let bytes_data: List<u8> = bytes.try_map(|b| b.data())?;
                ret(Value::Int(M::T::ENDIANNESS.decode(signed, bytes_data)))
            }
            Type::Ptr(ptr_type) => {
                if let Some(pair_ty) = ptr_type.as_wide_pair::<M::T>() {
                    let Value::Tuple(parts) = pair_ty.decode::<M>(bytes)? else {
                        panic!("as_wide_pair always returns a tuple type");
                    };
                    let Value::Ptr(ptr) = (parts).index_at(0) else {
                        panic!(
                            "as_wide_pair always returns tuple with the first field being a thin pointer"
                        );
                    };
                    let meta = ptr_type.meta_kind().decode_value((parts).index_at(1));
                    assert!(
                        meta.is_some(),
                        "as_wide_pair always returns a suitable metadata type"
                    );
                    ret(Value::Ptr(ptr.thin_pointer.widen(meta)))
                } else {
                    let ptr = decode_ptr::<M>(bytes)?;
                    ret(Value::Ptr(ptr.widen(None)))
                }
            }
            Type::Tuple { sized_fields, sized_head_layout, unsized_field } => {
                let unsized_field = unsized_field.extract();
                {
                    assert!(
                        unsized_field.is_none(),
                        "decode of Type::Tuple with unsized field"
                    );
                    let (size, _) = sized_head_layout.head_size_and_align();
                    if bytes.len() != size.bytes() {
                        panic!("decode of Type::Tuple with invalid length");
                    }
                    ret(
                        Value::Tuple(
                            sized_fields
                                .try_map(|(offset, ty)| {
                                    let subslice = bytes
                                        .subslice_with_length(
                                            offset.bytes(),
                                            ty
                                                .layout::<M::T>()
                                                .expect_size("WF ensures all sized tuple fields are sized")
                                                .bytes(),
                                        );
                                    ty.decode::<M>(subslice)
                                })?,
                        ),
                    )
                }
            }
            Type::Array { elem, count } => {
                let elem = elem.extract();
                {
                    let elem_size = elem
                        .layout::<M::T>()
                        .expect_size("WF ensures array element is sized");
                    let full_size = elem_size * count;
                    if bytes.len() != full_size.bytes() {
                        panic!("decode of Type::Array with invalid length");
                    }
                    let chunks: List<_> = (Int::ZERO..count)
                        .map(|i| {
                            bytes
                                .subslice_with_length(
                                    i * elem_size.bytes(),
                                    elem_size.bytes(),
                                )
                        })
                        .collect();
                    ret(
                        Value::Tuple(
                            chunks.try_map(|elem_bytes| elem.decode::<M>(elem_bytes))?,
                        ),
                    )
                }
            }
            Type::Union { size, chunks, .. } => {
                if bytes.len() != size.bytes() {
                    panic!("decode of Type::Union with invalid length");
                }
                let mut chunk_data = list![];
                for (offset, size) in chunks {
                    chunk_data
                        .push(bytes.subslice_with_length(offset.bytes(), size.bytes()));
                }
                ret(Value::Union(chunk_data))
            }
            Type::Enum { variants, discriminator, size, .. } => {
                if bytes.len() != size.bytes() {
                    panic!("decode of Type::Enum with invalid length");
                }
                let discriminant = decode_discriminant::<
                    M,
                >(
                        |offset, size| ret(
                            bytes.subslice_with_length(offset.bytes(), size.bytes()),
                        ),
                        discriminator,
                    )
                    .unwrap()?;
                let Some(value) = (variants).index_at(discriminant).ty.decode(bytes)
                else { return None };
                Some(Value::Variant {
                    discriminant,
                    data: libspecr::hidden::GcCow::new(value),
                })
            }
            Type::Slice { .. } => panic!("decode of Type::Slice"),
            Type::TraitObject(..) => panic!("decode of Type::TraitObject"),
        }
    }
    /// Encode `v` into a list of bytes according to the type `self`.
    ///
    /// Assumes `self` is well formed and `val` is well-formed for this type (violating this is a spec bug)..
    fn encode<M: Memory + libspecr::hidden::Obj>(
        self,
        val: Value<M>,
    ) -> List<AbstractByte<M::Provenance>> {
        match self {
            Type::Bool => {
                let Value::Bool(b) = val else { panic!() };
                list![AbstractByte::Init(if b { 1 } else { 0 }, None)]
            }
            Type::Int(IntType { signed, size }) => {
                let Value::Int(i) = val else { panic!() };
                let bytes_data = M::T::ENDIANNESS.encode(signed, size, i).unwrap();
                bytes_data.map(|b| AbstractByte::Init(b, None))
            }
            Type::Ptr(ptr_type) => {
                let Value::Ptr(ptr) = val else { panic!("val is WF for a pointer") };
                if let Some(pair_ty) = ptr_type.as_wide_pair::<M::T>() {
                    let thin_ptr_value = Value::Ptr(ptr.thin_pointer.widen(None));
                    let meta_data_value = ptr_type
                        .meta_kind()
                        .encode_as_value::<M>(ptr.metadata);
                    let tuple = Value::Tuple(list![thin_ptr_value, meta_data_value]);
                    pair_ty.encode::<M>(tuple)
                } else {
                    assert!(
                        ptr.metadata.is_none(),
                        "ptr_type and value have mismatching metadata"
                    );
                    encode_ptr::<M>(ptr.thin_pointer)
                }
            }
            Type::Tuple { sized_fields, sized_head_layout, unsized_field } => {
                let unsized_field = unsized_field.extract();
                {
                    assert!(
                        unsized_field.is_none(),
                        "encode of Type::Tuple with unsized field"
                    );
                    let (size, _) = sized_head_layout.head_size_and_align();
                    let Value::Tuple(values) = val else { panic!() };
                    assert_eq!(values.len(), sized_fields.len());
                    let mut bytes = list![AbstractByte::Uninit; size.bytes()];
                    for ((offset, ty), value) in sized_fields.zip(values) {
                        bytes
                            .write_subslice_at_index(
                                offset.bytes(),
                                ty.encode::<M>(value),
                            );
                    }
                    bytes
                }
            }
            Type::Array { elem, count } => {
                let elem = elem.extract();
                {
                    let Value::Tuple(values) = val else { panic!() };
                    assert_eq!(values.len(), count);
                    values
                        .flat_map(|value| {
                            let bytes = elem.encode::<M>(value);
                            assert_eq!(
                                bytes.len(), elem.layout::< M::T > ()
                                .expect_size("WF ensures array element is sized").bytes()
                            );
                            bytes
                        })
                }
            }
            Type::Union { size, chunks, .. } => {
                let Value::Union(chunk_data) = val else { panic!() };
                assert_eq!(chunk_data.len(), chunks.len());
                let mut bytes = list![AbstractByte::Uninit; size.bytes()];
                for ((offset, size), data) in chunks.zip(chunk_data) {
                    assert_eq!(size.bytes(), data.len());
                    bytes.write_subslice_at_index(offset.bytes(), data);
                }
                bytes
            }
            Type::Enum { variants, .. } => {
                let (discriminant, data) = match val {
                    Value::Variant { discriminant, data } => {
                        let data = data.extract();
                        (discriminant, data)
                    }
                    _ => panic!(),
                };
                let Variant { ty: variant, tagger } = (variants).index_at(discriminant);
                let mut bytes = variant.encode(data);
                encode_discriminant::<
                    M,
                >(
                        |offset, value_bytes| {
                            bytes.write_subslice_at_index(offset.bytes(), value_bytes);
                            ret(())
                        },
                        tagger,
                    )
                    .unwrap();
                bytes
            }
            Type::Slice { .. } => panic!("encode of Type::Slice"),
            Type::TraitObject(..) => panic!("encode of Type::TraitObject"),
        }
    }
    fn check_wf<T: Target + libspecr::hidden::Obj>(self, prog: Program) -> Result<()> {
        use Type::*;
        match self {
            Int(int_type) => {
                int_type.check_wf()?;
            }
            Bool => {}
            Ptr(ptr_type) => {
                ptr_type.check_wf::<T>(prog)?;
            }
            Tuple { mut sized_fields, unsized_field, sized_head_layout } => {
                let unsized_field = unsized_field.extract();
                {
                    sized_fields.sort_by_key(|(offset, _ty)| offset);
                    let mut last_end = Size::ZERO;
                    for (offset, ty) in sized_fields {
                        ty.check_wf::<T>(prog)?;
                        ensure_wf(
                            offset >= last_end,
                            "Type::Tuple: overlapping fields",
                        )?;
                        ensure_wf(
                            ty.layout::<T>().is_sized(),
                            "Type::Tuple: unsized field type in head",
                        )?;
                        last_end = offset
                            + ty.layout::<T>().expect_size("ensured to be sized above");
                    }
                    if let Some(unsized_field) = unsized_field {
                        unsized_field.check_wf::<T>(prog)?;
                        ensure_wf(
                            !unsized_field.layout::<T>().is_sized(),
                            "Type::Tuple: sized unsized field type",
                        )?;
                    }
                    sized_head_layout.check_wf::<T>()?;
                    ensure_wf(
                        sized_head_layout.end >= last_end,
                        "Type::Tuple: size of fields is bigger than the end of the sized head",
                    )?;
                    if sized_head_layout.packed_align.is_some() {
                        ensure_wf(
                            unsized_field.is_some(),
                            "Type::Tuple: meaningless packed align for sized tuple",
                        )?;
                    }
                }
            }
            Array { elem, count } => {
                let elem = elem.extract();
                {
                    ensure_wf(count >= 0, "Type::Array: negative amount of elements")?;
                    ensure_wf(
                        elem.layout::<T>().is_sized(),
                        "Type::Array: unsized element type",
                    )?;
                    elem.check_wf::<T>(prog)?;
                }
            }
            Slice { elem } => {
                let elem = elem.extract();
                {
                    ensure_wf(
                        elem.layout::<T>().is_sized(),
                        "Type::Slice: unsized element type",
                    )?;
                    elem.check_wf::<T>(prog)?;
                }
            }
            Union { fields, size, chunks, align: _ } => {
                for (offset, ty) in fields {
                    ty.check_wf::<T>(prog)?;
                    ensure_wf(
                        ty.layout::<T>().is_sized(),
                        "Type::Union: unsized field type",
                    )?;
                    ensure_wf(
                        size
                            >= offset
                                + ty.layout::<T>().expect_size("ensured to be sized above"),
                        "Type::Union: field size does not fit union",
                    )?;
                }
                let mut last_end = Size::ZERO;
                for (offset, size) in chunks {
                    ensure_wf(
                        offset >= last_end,
                        "Type::Union: chunks are not stored in ascending order",
                    )?;
                    last_end = offset + size;
                }
                ensure_wf(size >= last_end, "Type::Union: chunks do not fit union")?;
            }
            Enum { variants, size, align, discriminator, discriminant_ty } => {
                for (discriminant, variant) in variants {
                    ensure_wf(
                        discriminant_ty.can_represent(discriminant),
                        "Type::Enum: invalid value for discriminant",
                    )?;
                    variant.ty.check_wf::<T>(prog)?;
                    let LayoutStrategy::Sized(var_size, var_align) = variant
                        .ty
                        .layout::<T>() else {
                        throw_ill_formed!("Type::Enum: variant type is unsized")
                    };
                    ensure_wf(
                        var_size == size,
                        "Type::Enum: variant size is not the same as enum size",
                    )?;
                    ensure_wf(
                        var_align <= align,
                        "Type::Enum: invalid align requirement",
                    )?;
                    for (offset, (value_type, value)) in variant.tagger {
                        value_type.check_wf()?;
                        ensure_wf(
                            value_type.can_represent(value),
                            "Type::Enum: invalid tagger value",
                        )?;
                        ensure_wf(
                            offset + value_type.size <= size,
                            "Type::Enum tagger type size too big for enum",
                        )?;
                    }
                }
                discriminator.check_wf::<T>(size, variants)?;
            }
            TraitObject(trait_name) => {
                ensure_wf(
                    prog.traits.contains_key(trait_name),
                    "Type::TraitObject: trait name doesn't exist",
                )?;
            }
        }
        let layout = self.layout::<T>();
        layout.check_wf::<T>(prog)?;
        layout.check_aligned()?;
        assert_eq!(
            layout.meta_kind(), self.meta_kind(),
            "Type::meta_kind() must match the Type::layout()'s kind"
        );
        ret(())
    }
    /// The layout, i.e. the size and align of the type. For `?Sized` types, this needs to be computed.
    pub fn layout<T: Target + libspecr::hidden::Obj>(self) -> LayoutStrategy {
        use Type::*;
        use LayoutStrategy::Sized;
        match self {
            Int(int_type) => Sized(int_type.size, int_type.align::<T>()),
            Bool => Sized(Size::from_bytes_const(1), Align::ONE),
            Ptr(p) if p.meta_kind() == PointerMetaKind::None => {
                Sized(T::PTR_SIZE, T::PTR_ALIGN)
            }
            Ptr(_) => Sized(libspecr::Int::from(2) * T::PTR_SIZE, T::PTR_ALIGN),
            Union { size, align, .. } | Enum { size, align, .. } => Sized(size, align),
            Tuple { sized_head_layout, unsized_field, .. } => {
                let unsized_field = unsized_field.extract();
                match unsized_field {
                    None => {
                        let (size, align) = sized_head_layout.head_size_and_align();
                        Sized(size, align)
                    }
                    Some(tail_ty) => {
                        LayoutStrategy::Tuple {
                            head: sized_head_layout,
                            tail: libspecr::hidden::GcCow::new(tail_ty.layout::<T>()),
                        }
                    }
                }
            }
            Array { elem, count } => {
                let elem = elem.extract();
                Sized(
                    elem.layout::<T>().expect_size("WF ensures array element is sized")
                        * count,
                    elem.layout::<T>().expect_align("WF ensures array element is sized"),
                )
            }
            Slice { elem } => {
                let elem = elem.extract();
                LayoutStrategy::Slice(
                    elem.layout::<T>().expect_size("WF ensures slice element is sized"),
                    elem.layout::<T>().expect_align("WF ensures array element is sized"),
                )
            }
            TraitObject(trait_name) => LayoutStrategy::TraitObject(trait_name),
        }
    }
    /// Returns the metadata kind when this type is used as a pointee.
    /// This matches the meta kind of the layout, but without needing to specify a target.
    pub fn meta_kind(self) -> PointerMetaKind {
        match self {
            Type::Slice { .. } => PointerMetaKind::ElementCount,
            Type::TraitObject(trait_name) => PointerMetaKind::VTablePointer(trait_name),
            Type::Tuple { unsized_field, .. } => {
                let unsized_field = unsized_field.extract();
                match unsized_field {
                    None => PointerMetaKind::None,
                    Some(ty) => ty.meta_kind(),
                }
            }
            _ => PointerMetaKind::None,
        }
    }
}
fn decode_ptr<M: Memory + libspecr::hidden::Obj>(
    bytes: List<AbstractByte<M::Provenance>>,
) -> Option<ThinPointer<M::Provenance>> {
    if bytes.len() != M::T::PTR_SIZE.bytes() {
        panic!("decode of thin pointer with invalid length");
    }
    let bytes_data = bytes.try_map(|b| b.data())?;
    let addr = M::T::ENDIANNESS.decode(Unsigned, bytes_data);
    let provenance = bytes
        .fold_with_idx(
            (bytes).index_at(0).provenance_frag().map(|frag| frag.provenance),
            |acc, idx, byte| {
                if let Some(frag) = byte.provenance_frag() && frag.position == idx
                    && Some(frag.provenance) == acc
                {
                    acc
                } else {
                    None
                }
            },
        );
    ret(ThinPointer { addr, provenance })
}
fn encode_ptr<M: Memory + libspecr::hidden::Obj>(
    ptr: ThinPointer<M::Provenance>,
) -> List<AbstractByte<M::Provenance>> {
    let bytes_data = M::T::ENDIANNESS
        .encode(Unsigned, M::T::PTR_SIZE, ptr.addr)
        .unwrap();
    bytes_data
        .map_with_idx(|i, b| AbstractByte::Init(
            b,
            ptr
                .provenance
                .map(|provenance| ProvenanceFrag {
                    provenance,
                    position: i,
                }),
        ))
}
impl PointerMetaKind {
    /// Returns the type of the metadata when used as a value.
    pub fn ty<T: Target + libspecr::hidden::Obj>(self) -> Type {
        match self {
            PointerMetaKind::None => unit_type(),
            PointerMetaKind::ElementCount => Type::Int(IntType::usize_ty::<T>()),
            PointerMetaKind::VTablePointer(trait_name) => {
                Type::Ptr(PtrType::VTablePtr(trait_name))
            }
        }
    }
    /// Decodes a value to metadata.
    /// The spec will only call this with values which are well formed for `self.ty()`,
    /// but this may return ill-formed metadata (as defined by `Machine::check_ptr_metadata`), thus needs to be checked.
    fn decode_value<M: Memory + libspecr::hidden::Obj>(
        self,
        value: Value<M>,
    ) -> Option<PointerMeta<M::Provenance>> {
        match (self, value) {
            (PointerMetaKind::None, Value::Tuple(fields)) if fields.is_empty() => None,
            (PointerMetaKind::ElementCount, Value::Int(count)) => {
                Some(PointerMeta::ElementCount(count))
            }
            (
                PointerMetaKind::VTablePointer(_),
                Value::Ptr(ptr),
            ) if ptr.metadata.is_none() => {
                Some(PointerMeta::VTablePointer(ptr.thin_pointer))
            }
            _ => panic!("PointerMeta::decode_value called with invalid value"),
        }
    }
    /// Encodes metadata as a value.
    /// The spec ensures this is only called with well-formed metadata (as defined by `Machine::check_ptr_metadata`).
    fn encode_as_value<M: Memory + libspecr::hidden::Obj>(
        self,
        meta: Option<PointerMeta<M::Provenance>>,
    ) -> Value<M> {
        match (self, meta) {
            (PointerMetaKind::None, None) => unit_value(),
            (PointerMetaKind::ElementCount, Some(PointerMeta::ElementCount(count))) => {
                Value::Int(count)
            }
            (
                PointerMetaKind::VTablePointer(_),
                Some(PointerMeta::VTablePointer(ptr)),
            ) => Value::Ptr(ptr.widen(None)),
            _ => panic!("PointerMeta::encode_as_value called with invalid value"),
        }
    }
}
impl PtrType {
    /// Returns a pair type representing this wide pointer or `None` if it is thin.
    pub fn as_wide_pair<T: Target + libspecr::hidden::Obj>(self) -> Option<Type> {
        if self.meta_kind() == PointerMetaKind::None {
            return None;
        }
        let meta_ty = self.meta_kind().ty::<T>();
        assert_eq!(
            meta_ty.layout::< T > ().expect_size("metadata is always sized"),
            T::PTR_SIZE, "metadata is assumed to be pointer-sized"
        );
        assert_eq!(
            meta_ty.layout::< T > ().expect_align("metadata is always sized"),
            T::PTR_ALIGN, "metadata is assumed to be pointer-aligned"
        );
        let thin_pointer_field = (
            Offset::ZERO,
            Type::Ptr(PtrType::Raw {
                meta_kind: PointerMetaKind::None,
            }),
        );
        let metadata_field = (T::PTR_SIZE, meta_ty);
        ret(Type::Tuple {
            sized_fields: list![thin_pointer_field, metadata_field],
            sized_head_layout: TupleHeadLayout {
                end: Int::from(2) * T::PTR_SIZE,
                align: T::PTR_ALIGN,
                packed_align: None,
            },
            unsized_field: libspecr::hidden::GcCow::new(None),
        })
    }
    fn check_wf<T: Target + libspecr::hidden::Obj>(self, prog: Program) -> Result<()> {
        match self {
            PtrType::Ref { pointee, .. } | PtrType::Box { pointee } => {
                pointee.check_wf::<T>(prog)?;
            }
            PtrType::Raw { .. } | PtrType::FnPtr => {}
            PtrType::VTablePtr(trait_name) => {
                ensure_wf(
                    prog.traits.contains_key(trait_name),
                    "PtrType::VTablePtr: trait name doesn't exist",
                )?;
            }
        }
        ret(())
    }
}
/// Uses the `Discriminator` to decode the discriminant from the tag read out of the value's bytes using the accessor.
/// Returns `Ok(None)` when reaching `Discriminator::Invalid` and when any of the reads
/// for `Discriminator::Branch` encounters uninitialized memory.
/// Returns `Err` only if `accessor` returns `Err`.
///
/// The accessor is given an offset relative to the beginning of the encoded enum value,
/// and it should return the abstract byte at that offset.
/// FIXME: we have multiple quite different fail sources, it would be nice to return more error information.
fn decode_discriminant<M: Memory + libspecr::hidden::Obj>(
    mut accessor: impl FnMut(Offset, Size) -> Result<List<AbstractByte<M::Provenance>>>,
    discriminator: Discriminator,
) -> Result<Option<Int>> {
    match discriminator {
        Discriminator::Known(val) => ret(Some(val)),
        Discriminator::Invalid => ret(None),
        Discriminator::Branch { offset, value_type, children, fallback } => {
            let fallback = fallback.extract();
            {
                let bytes = accessor(offset, value_type.size)?;
                let Some(Value::Int(val)) = Type::Int(value_type).decode::<M>(bytes)
                else {
                    return ret(None);
                };
                let next_discriminator = children
                    .iter()
                    .find_map(|((start, end), child)| {
                        if start <= val && val < end { Some(child) } else { None }
                    })
                    .unwrap_or(fallback);
                decode_discriminant::<M>(accessor, next_discriminator)
            }
        }
    }
}
/// Writes the tag described by the tagger into the bytes accessed using the accessor.
/// Returns `Err` only if `accessor` returns `Err`.
///
/// The accessor is given an offset relative to the beginning of the encoded enum value
/// and the integer value and type to store at that offset.
fn encode_discriminant<M: Memory + libspecr::hidden::Obj>(
    mut accessor: impl FnMut(Offset, List<AbstractByte<M::Provenance>>) -> Result,
    tagger: Map<Offset, (IntType, Int)>,
) -> Result<()> {
    for (offset, (value_type, value)) in tagger.iter() {
        let bytes = Type::Int(value_type).encode::<M>(Value::Int(value));
        accessor(offset, bytes)?;
    }
    ret(())
}
/// Ensures the given boolean is true or else raises UB.
fn ensure_else_ub(b: bool, msg: &str) -> Result<()> {
    if !b {
        throw_ub!("{}", msg);
    }
    ret(())
}
#[allow(unused)]
trait DefinedRelation: libspecr::hidden::Obj {
    /// returns whether `self` is less or as defined as `other`
    fn le_defined(self, other: Self) -> bool;
}
impl<
    Provenance: libspecr::hidden::Obj + for<'de> serde::Deserialize<'de>
        + serde::Serialize,
> DefinedRelation for AbstractByte<Provenance> {
    fn le_defined(self, other: Self) -> bool {
        use AbstractByte::*;
        match (self, other) {
            (Uninit, _) => true,
            (Init(data1, None), Init(data2, _)) => data1 == data2,
            (Init(data1, Some(provenance1)), Init(data2, Some(provenance2))) => {
                data1 == data2 && provenance1 == provenance2
            }
            _ => false,
        }
    }
}
impl<
    Provenance: libspecr::hidden::Obj + for<'de> serde::Deserialize<'de>
        + serde::Serialize,
> DefinedRelation for ThinPointer<Provenance> {
    fn le_defined(self, other: Self) -> bool {
        self.addr == other.addr
            && match (self.provenance, other.provenance) {
                (None, _) => true,
                (Some(prov1), Some(prov2)) => prov1 == prov2,
                _ => false,
            }
    }
}
impl<
    Provenance: libspecr::hidden::Obj + for<'de> serde::Deserialize<'de>
        + serde::Serialize,
> DefinedRelation for PointerMeta<Provenance> {
    fn le_defined(self, other: Self) -> bool {
        match (self, other) {
            (PointerMeta::VTablePointer(ptr1), PointerMeta::VTablePointer(ptr2)) => {
                ptr1.le_defined(ptr2)
            }
            _ => self == other,
        }
    }
}
impl<
    Provenance: libspecr::hidden::Obj + for<'de> serde::Deserialize<'de>
        + serde::Serialize,
> DefinedRelation for Pointer<Provenance> {
    fn le_defined(self, other: Self) -> bool {
        self.thin_pointer.le_defined(other.thin_pointer)
            && self.metadata.le_defined(other.metadata)
    }
}
impl<
    T: DefinedRelation + libspecr::hidden::Obj + for<'de> serde::Deserialize<'de>
        + serde::Serialize,
> DefinedRelation for List<T> {
    fn le_defined(self, other: Self) -> bool {
        self.len() == other.len() && self.zip(other).all(|(l, r)| l.le_defined(r))
    }
}
impl<
    M: Memory + libspecr::hidden::Obj + for<'de> serde::Deserialize<'de>
        + serde::Serialize,
> DefinedRelation for Value<M> {
    fn le_defined(self, other: Self) -> bool {
        use Value::*;
        match (self, other) {
            (Int(i1), Int(i2)) => i1 == i2,
            (Bool(b1), Bool(b2)) => b1 == b2,
            (Ptr(p1), Ptr(p2)) => p1.le_defined(p2),
            (Tuple(vals1), Tuple(vals2)) => vals1.le_defined(vals2),
            (
                Variant { discriminant: discriminant1, data: data1 },
                Variant { discriminant: discriminant2, data: data2 },
            ) => {
                let data1 = data1.extract();
                let data2 = data2.extract();
                discriminant1 == discriminant2 && data1.le_defined(data2)
            }
            (Union(chunks1), Union(chunks2)) => chunks1.le_defined(chunks2),
            _ => false,
        }
    }
}
impl<
    T: DefinedRelation + libspecr::hidden::Obj + for<'de> serde::Deserialize<'de>
        + serde::Serialize,
> DefinedRelation for Option<T> {
    fn le_defined(self, other: Self) -> bool {
        match (self, other) {
            (None, _) => true,
            (Some(l), Some(r)) => l.le_defined(r),
            _ => false,
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
enum Value<M: Memory + libspecr::hidden::Obj> {
    /// A mathematical integer, used for `i*`/`u*` types.
    Int(Int),
    /// A Boolean value, used for `bool`.
    Bool(bool),
    /// A pointer value, used for references and raw pointers.
    Ptr(Pointer<M::Provenance>),
    /// An n-tuple, used for arrays, structs, tuples (including unit).
    Tuple(List<Value<M>>),
    /// A variant of a sum type, used for enums.
    Variant { discriminant: Int, data: libspecr::hidden::GcCow<Value<M>> },
    /// Unions are represented as "lists of chunks", where each chunk is just a raw list of bytes.
    Union(List<List<AbstractByte<M::Provenance>>>),
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
struct Place<M: Memory + libspecr::hidden::Obj> {
    ptr: Pointer<M::Provenance>,
    aligned: bool,
}
fn ensure_wf(b: bool, msg: &str) -> Result<()> {
    if !b {
        throw_ill_formed!("{}", msg);
    }
    ret(())
}
impl IntType {
    fn check_wf(self) -> Result<()> {
        ensure_wf(
            self.size.bytes().is_power_of_two(),
            "IntType: size is not power of two",
        )
    }
    pub fn align<T: Target + libspecr::hidden::Obj>(self) -> Align {
        let size = self.size.bytes();
        let natural_align = Align::from_bytes(size).unwrap();
        natural_align.min(T::INT_MAX_ALIGN)
    }
    pub const I8: IntType = IntType {
        signed: Signedness::Signed,
        size: Size::from_bytes_const(1),
    };
    pub const I32: IntType = IntType {
        signed: Signedness::Signed,
        size: Size::from_bytes_const(4),
    };
    pub fn usize_ty<T: Target + libspecr::hidden::Obj>() -> Self {
        IntType {
            signed: Signedness::Unsigned,
            size: T::PTR_SIZE,
        }
    }
    pub fn can_represent(&self, i: Int) -> bool {
        i.in_bounds(self.signed, self.size)
    }
    pub fn bring_in_bounds(&self, i: Int) -> Int {
        i.bring_in_bounds(self.signed, self.size)
    }
    /// Generate the return type for IntWithOverflow
    pub fn with_overflow<T: Target + libspecr::hidden::Obj>(&self) -> Type {
        let fields = list![(Size::ZERO, Type::Int(* self)), (self.size, Type::Bool)];
        let align = self.align::<T>();
        let size = self.size + Size::from_bytes(align.bytes()).unwrap();
        Type::Tuple {
            sized_fields: fields,
            sized_head_layout: TupleHeadLayout {
                end: size,
                align,
                packed_align: None,
            },
            unsized_field: libspecr::hidden::GcCow::new(None),
        }
    }
}
impl TupleHeadLayout {
    fn check_wf<T: Target + libspecr::hidden::Obj>(self) -> Result<()> {
        ensure_wf(T::valid_size(self.end), "TupleHeadLayout: end not valid")?;
        if let Some(packed) = self.packed_align {
            ensure_wf(
                self.align <= packed,
                "TupleHeadLayout: align bigger than packed attribute",
            )?;
        }
        ret(())
    }
    /// The actual alignment of the tail, considering the packed attribute.
    fn capped_tail_align(self, tail_align: Align) -> Align {
        match self.packed_align {
            Some(packed_align) => tail_align.min(packed_align),
            None => tail_align,
        }
    }
    /// Where the tail starts, given the aligment of the tail type.
    pub fn tail_offset(self, tail_align: Align) -> Offset {
        let capped_tail_align = self.capped_tail_align(tail_align);
        let tail_offset = self.end.align_to(capped_tail_align);
        tail_offset
    }
    /// The size and alignment of the full tuple, including the tail.
    /// Given the size and alignment of the tail type.
    pub fn full_size_and_align(
        self,
        tail_size: Size,
        tail_align: Align,
    ) -> (Size, Align) {
        let capped_tail_align = self.capped_tail_align(tail_align);
        let align = capped_tail_align.max(self.align);
        let tail_offset = self.tail_offset(tail_align);
        let end = tail_offset + tail_size;
        let size = end.align_to(align);
        (size, align)
    }
    /// Returns the size and alignment of the tuple when there is no tail.
    pub fn head_size_and_align(self) -> (Size, Align) {
        (self.end.align_to(self.align), self.align)
    }
}
impl LayoutStrategy {
    /// This does *not* require that size is a multiple of align!
    fn check_wf<T: Target + libspecr::hidden::Obj>(self, prog: Program) -> Result<()> {
        match self {
            LayoutStrategy::Sized(size, _align) => {
                ensure_wf(T::valid_size(size), "LayoutStrategy: size not valid")?;
            }
            LayoutStrategy::Slice(size, _align) => {
                ensure_wf(
                    T::valid_size(size),
                    "LayoutStrategy: element size not valid",
                )?;
            }
            LayoutStrategy::TraitObject(trait_name) => {
                ensure_wf(
                    prog.traits.contains_key(trait_name),
                    "LayoutStrategy: trait name doesn't exist",
                )?;
            }
            LayoutStrategy::Tuple { head, tail } => {
                let tail = tail.extract();
                {
                    head.check_wf::<T>()?;
                    tail.check_wf::<T>(prog)?;
                    ensure_wf(
                        !tail.is_sized(),
                        "LayoutStrategy: tuple with sized tail",
                    )?;
                }
            }
        };
        ret(())
    }
    fn check_aligned(self) -> Result<()> {
        match self {
            LayoutStrategy::Sized(size, align) => {
                ensure_wf(
                    size.bytes() % align.bytes() == 0,
                    "check_aligned: size not a multiple of alignment",
                )?;
            }
            LayoutStrategy::Slice(size, align) => {
                ensure_wf(
                    size.bytes() % align.bytes() == 0,
                    "check_aligned: element size not a multiple of alignment",
                )?;
            }
            LayoutStrategy::TraitObject(..) => {}
            LayoutStrategy::Tuple { tail, .. } => {
                let tail = tail.extract();
                tail.check_aligned()?
            }
        };
        ret(())
    }
    pub fn is_sized(self) -> bool {
        matches!(self, LayoutStrategy::Sized(..))
    }
    /// Returns the size when the type must be statically sized.
    pub fn expect_size(self, msg: &str) -> Size {
        match self {
            LayoutStrategy::Sized(size, _) => size,
            _ => panic!("expect_size called on unsized type: {msg}"),
        }
    }
    /// Returns the alignment when the type must be statically sized.
    pub fn expect_align(self, msg: &str) -> Align {
        match self {
            LayoutStrategy::Sized(_, align) => align,
            _ => panic!("expect_align called on unsized type: {msg}"),
        }
    }
    /// Computes the dynamic size and alignment, but the caller must provide compatible metadata.
    ///
    /// The size and align of unsized structs depend on each other,
    /// thus we must recursively compute them at the same time.
    pub fn compute_size_and_align<Provenance: libspecr::hidden::Obj>(
        self,
        meta: Option<PointerMeta<Provenance>>,
        vtables: impl FnOnce(ThinPointer<Provenance>) -> VTable,
    ) -> (Size, Align) {
        match (self, meta) {
            (LayoutStrategy::Sized(size, align), None) => (size, align),
            (
                LayoutStrategy::Slice(elem_size, align),
                Some(PointerMeta::ElementCount(count)),
            ) => (count * elem_size, align),
            (
                LayoutStrategy::TraitObject(..),
                Some(PointerMeta::VTablePointer(vtable_ptr)),
            ) => {
                let vtable = vtables(vtable_ptr);
                (vtable.size, vtable.align)
            }
            (LayoutStrategy::Tuple { head, tail }, Some(meta)) => {
                let tail = tail.extract();
                {
                    let (tail_size, tail_align) = tail
                        .compute_size_and_align(Some(meta), vtables);
                    head.full_size_and_align(tail_size, tail_align)
                }
            }
            _ => panic!("pointer meta data does not match type"),
        }
    }
    /// Returns the metadata kind which is needed to compute this strategy,
    /// i.e `machine.check_pointer_metadata(meta, self.meta_kind()).is_ok()` implies `machine.compute_*(meta)` is well-defined.
    pub fn meta_kind(self) -> PointerMetaKind {
        match self {
            LayoutStrategy::Sized(..) => PointerMetaKind::None,
            LayoutStrategy::Slice(..) => PointerMetaKind::ElementCount,
            LayoutStrategy::TraitObject(trait_name) => {
                PointerMetaKind::VTablePointer(trait_name)
            }
            LayoutStrategy::Tuple { tail, .. } => {
                let tail = tail.extract();
                tail.meta_kind()
            }
        }
    }
}
impl UnsafeCellStrategy {
    fn check_cells(cells: List<(Offset, Size)>, size: Size) -> Result<()> {
        let mut last_end = Size::ZERO;
        for (start, size) in cells {
            ensure_wf(start >= last_end, "LayoutStrategy: invalid cells")?;
            last_end = start + size;
        }
        ensure_wf(last_end <= size, "LayoutStrategy: invalid cells")?;
        ret(())
    }
    fn check_wf<T: Target + libspecr::hidden::Obj>(
        self,
        layout: LayoutStrategy,
    ) -> Result<()> {
        match (self, layout) {
            (UnsafeCellStrategy::Sized { cells }, LayoutStrategy::Sized(size, _)) => {
                Self::check_cells(cells, size)?;
            }
            (
                UnsafeCellStrategy::Slice { element_cells },
                LayoutStrategy::Slice(size, _),
            ) => {
                Self::check_cells(element_cells, size)?;
            }
            (UnsafeCellStrategy::TraitObject, LayoutStrategy::TraitObject(..)) => {}
            (
                UnsafeCellStrategy::Tuple { head_cells, tail_cells },
                LayoutStrategy::Tuple { head, tail },
            ) => {
                let tail = tail.extract();
                let tail_cells = tail_cells.extract();
                {
                    Self::check_cells(head_cells, head.end)?;
                    tail_cells.check_wf::<T>(tail)?;
                }
            }
            _ => {
                ensure_wf(
                    false,
                    "UnsafeCellStrategy and LayoutStrategy variants do not match",
                )?;
            }
        };
        ret(())
    }
}
impl PointeeInfo {
    fn check_wf<T: Target + libspecr::hidden::Obj>(self, prog: Program) -> Result<()> {
        self.layout.check_wf::<T>(prog)?;
        self.unsafe_cells.check_wf::<T>(self.layout)?;
        ret(())
    }
}
impl Discriminator {
    fn check_wf<T: Target + libspecr::hidden::Obj>(
        self,
        size: Size,
        variants: Map<Int, Variant>,
    ) -> Result<()> {
        match self {
            Discriminator::Known(discriminant) => {
                ensure_wf(
                    variants.get(discriminant).is_some(),
                    "Discriminator: invalid discriminant",
                )
            }
            Discriminator::Invalid => ret(()),
            Discriminator::Branch { offset, value_type, fallback, children } => {
                let fallback = fallback.extract();
                {
                    value_type.check_wf()?;
                    ensure_wf(
                        offset + value_type.size <= size,
                        "Discriminator: branch offset exceeds size",
                    )?;
                    fallback.check_wf::<T>(size, variants)?;
                    for (idx, ((start, end), discriminator)) in children
                        .into_iter()
                        .enumerate()
                    {
                        ensure_wf(
                            value_type.can_represent(start),
                            "Discriminator: invalid branch start bound",
                        )?;
                        ensure_wf(
                            value_type.can_represent(end - Int::ONE),
                            "Discriminator: invalid branch end bound",
                        )?;
                        ensure_wf(start < end, "Discriminator: invalid bound values")?;
                        ensure_wf(
                            children
                                .keys()
                                .enumerate()
                                .all(|(other_idx, (other_start, other_end))| {
                                    other_end <= start || other_start >= end || idx == other_idx
                                }),
                            "Discriminator: branch ranges overlap",
                        )?;
                        discriminator.check_wf::<T>(size, variants)?;
                    }
                    ret(())
                }
            }
        }
    }
}
impl Constant {
    /// Check that the constant has the expected type.
    /// Assumes that `ty` has already been checked.
    fn check_wf<T: Target + libspecr::hidden::Obj>(
        self,
        ty: Type,
        prog: Program,
    ) -> Result<()> {
        match (self, ty) {
            (Constant::Int(i), Type::Int(int_type)) => {
                ensure_wf(
                    int_type.can_represent(i),
                    "Constant::Int: invalid int value",
                )?;
            }
            (Constant::Bool(_), Type::Bool) => {}
            (Constant::GlobalPointer(relocation), Type::Ptr(_)) => {
                relocation.check_wf(prog.globals)?;
            }
            (Constant::FnPointer(fn_name), Type::Ptr(ptr_ty)) => {
                ensure_wf(
                    matches!(ptr_ty, PtrType::FnPtr),
                    "Constant::FnPointer: non function pointer type",
                )?;
                ensure_wf(
                    prog.functions.contains_key(fn_name),
                    "Constant::FnPointer: invalid function name",
                )?;
            }
            (Constant::VTablePointer(vtable_name), Type::Ptr(ptr_ty)) => {
                let Some(vtable) = prog.vtables.get(vtable_name) else {
                    throw_ill_formed!("Constant::VTablePointer: invalid vtable name");
                };
                ensure_wf(
                    ptr_ty == PtrType::VTablePtr(vtable.trait_name),
                    "Constant::VTablePointer: non or wrong vtable pointer type",
                )?;
            }
            (Constant::PointerWithoutProvenance(addr), Type::Ptr(_)) => {
                ensure_wf(
                    addr.in_bounds(Signedness::Unsigned, T::PTR_SIZE),
                    "Constant::PointerWithoutProvenance: pointer out-of-bounds",
                )?;
            }
            _ => throw_ill_formed!("Constant: value does not match type"),
        }
        ret(())
    }
}
impl ValueExpr {
    #[allow(unused_braces)]
    fn check_wf<T: Target + libspecr::hidden::Obj>(
        self,
        locals: Map<LocalName, Type>,
        prog: Program,
    ) -> Result<Type> {
        use ValueExpr::*;
        ret(
            match self {
                Constant(value, ty) => {
                    ty.check_wf::<T>(prog)?;
                    value.check_wf::<T>(ty, prog)?;
                    ty
                }
                Tuple(exprs, t) => {
                    t.check_wf::<T>(prog)?;
                    match t {
                        Type::Tuple { sized_fields, unsized_field, .. } => {
                            let unsized_field = unsized_field.extract();
                            {
                                ensure_wf(
                                    unsized_field.is_none(),
                                    "ValueExpr::Tuple: constructing an unsized tuple value",
                                )?;
                                ensure_wf(
                                    exprs.len() == sized_fields.len(),
                                    "ValueExpr::Tuple: invalid number of tuple fields",
                                )?;
                                for (e, (_offset, ty)) in exprs.zip(sized_fields) {
                                    let checked = e.check_wf::<T>(locals, prog)?;
                                    ensure_wf(
                                        checked == ty,
                                        "ValueExpr::Tuple: invalid tuple field type",
                                    )?;
                                }
                            }
                        }
                        Type::Array { elem, count } => {
                            let elem = elem.extract();
                            {
                                ensure_wf(
                                    exprs.len() == count,
                                    "ValueExpr::Tuple: invalid number of array elements",
                                )?;
                                for e in exprs {
                                    let checked = e.check_wf::<T>(locals, prog)?;
                                    ensure_wf(
                                        checked == elem,
                                        "ValueExpr::Tuple: invalid array element type",
                                    )?;
                                }
                            }
                        }
                        _ => {
                            throw_ill_formed!(
                                "ValueExpr::Tuple: expression does not match type"
                            )
                        }
                    }
                    t
                }
                Union { field, expr, union_ty } => {
                    let expr = expr.extract();
                    {
                        union_ty.check_wf::<T>(prog)?;
                        let Type::Union { fields, .. } = union_ty else {
                            throw_ill_formed!("ValueExpr::Union: invalid type")
                        };
                        ensure_wf(
                            field < fields.len(),
                            "ValueExpr::Union: invalid field length",
                        )?;
                        let (_offset, ty) = (fields).index_at(field);
                        let checked = expr.check_wf::<T>(locals, prog)?;
                        ensure_wf(
                            checked == ty,
                            "ValueExpr::Union: invalid field type",
                        )?;
                        union_ty
                    }
                }
                Variant { discriminant, data, enum_ty } => {
                    let data = data.extract();
                    {
                        let Type::Enum { variants, .. } = enum_ty else {
                            throw_ill_formed!("ValueExpr::Variant: invalid type")
                        };
                        enum_ty.check_wf::<T>(prog)?;
                        let Some(variant) = variants.get(discriminant) else {
                            throw_ill_formed!(
                                "ValueExpr::Variant: invalid discriminant"
                            );
                        };
                        let checked = data.check_wf::<T>(locals, prog)?;
                        ensure_wf(
                            checked == variant.ty,
                            "ValueExpr::Variant: invalid type",
                        )?;
                        enum_ty
                    }
                }
                GetDiscriminant { place } => {
                    let place = place.extract();
                    {
                        let Type::Enum { discriminant_ty, .. } = place
                            .check_wf::<T>(locals, prog)? else {
                            throw_ill_formed!(
                                "ValueExpr::GetDiscriminant: invalid type"
                            );
                        };
                        Type::Int(discriminant_ty)
                    }
                }
                Load { source } => {
                    let source = source.extract();
                    {
                        let val_ty = source.check_wf::<T>(locals, prog)?;
                        ensure_wf(
                            val_ty.layout::<T>().is_sized(),
                            "ValueExpr::Load: unsized value type",
                        )?;
                        val_ty
                    }
                }
                AddrOf { target, ptr_ty } => {
                    let target = target.extract();
                    {
                        ptr_ty.check_wf::<T>(prog)?;
                        let target_ty = target.check_wf::<T>(locals, prog)?;
                        ensure_wf(
                            target_ty.meta_kind() == ptr_ty.meta_kind(),
                            "ValueExpr::AddrOf: mismatched metadata kind",
                        )?;
                        Type::Ptr(ptr_ty)
                    }
                }
                UnOp { operator, operand } => {
                    let operand = operand.extract();
                    {
                        use lang::UnOp::*;
                        let operand = operand.check_wf::<T>(locals, prog)?;
                        match operator {
                            Int(int_op) => {
                                let Type::Int(int_ty) = operand else {
                                    throw_ill_formed!("UnOp::Int: invalid operand");
                                };
                                let ret_ty = match int_op {
                                    IntUnOp::CountOnes => {
                                        IntType {
                                            signed: Unsigned,
                                            size: Size::from_bytes(4).unwrap(),
                                        }
                                    }
                                    _ => int_ty,
                                };
                                Type::Int(ret_ty)
                            }
                            Cast(cast_op) => {
                                use lang::CastOp::*;
                                match cast_op {
                                    IntToInt(int_ty) => {
                                        ensure_wf(
                                            matches!(operand, Type::Int(_)),
                                            "Cast::IntToInt: invalid operand",
                                        )?;
                                        Type::Int(int_ty)
                                    }
                                    Transmute(new_ty) => {
                                        ensure_wf(
                                            operand.layout::<T>().is_sized(),
                                            "Cast::Transmute: unsized source type",
                                        )?;
                                        ensure_wf(
                                            new_ty.layout::<T>().is_sized(),
                                            "Cast::Transmute: unsized target type",
                                        )?;
                                        new_ty
                                    }
                                }
                            }
                            GetThinPointer => {
                                ensure_wf(
                                    matches!(operand, Type::Ptr(_)),
                                    "UnOp::GetThinPointer: invalid operand: not a pointer",
                                )?;
                                Type::Ptr(PtrType::Raw {
                                    meta_kind: PointerMetaKind::None,
                                })
                            }
                            GetMetadata => {
                                let Type::Ptr(ptr_ty) = operand else {
                                    throw_ill_formed!(
                                        "UnOp::GetMetadata: invalid operand: not a pointer"
                                    );
                                };
                                ptr_ty.meta_kind().ty::<T>()
                            }
                            ComputeSize(ty) | ComputeAlign(ty) => {
                                ty.check_wf::<T>(prog)?;
                                let meta_ty = ty.meta_kind().ty::<T>();
                                if operand != meta_ty {
                                    throw_ill_formed!(
                                        "UnOp::ComputeSize|ComputeAlign: invalid operand type: not metadata of type"
                                    );
                                }
                                Type::Int(IntType::usize_ty::<T>())
                            }
                            VTableMethodLookup(method) => {
                                let Type::Ptr(PtrType::VTablePtr(trait_name)) = operand
                                else {
                                    throw_ill_formed!(
                                        "UnOp::VTableMethodLookup: invalid operand: not a vtable pointer"
                                    );
                                };
                                let trait_methods = (prog.traits).index_at(trait_name);
                                ensure_wf(
                                    trait_methods.contains(method),
                                    "UnOp::VTableMethodLookup: invalid operand: method doesn't exist in trait",
                                )?;
                                Type::Ptr(PtrType::FnPtr)
                            }
                        }
                    }
                }
                BinOp { operator, left, right } => {
                    let right = right.extract();
                    let left = left.extract();
                    {
                        use lang::BinOp::*;
                        let left = left.check_wf::<T>(locals, prog)?;
                        let right = right.check_wf::<T>(locals, prog)?;
                        match operator {
                            Int(int_op) => {
                                let Type::Int(left) = left else {
                                    throw_ill_formed!("BinOp::Int: invalid left type");
                                };
                                let Type::Int(right) = right else {
                                    throw_ill_formed!("BinOp::Int: invalid right type");
                                };
                                use IntBinOp::*;
                                if !matches!(
                                    int_op, Shl | Shr | ShlUnchecked | ShrUnchecked
                                ) {
                                    ensure_wf(
                                        left == right,
                                        "BinOp:Int: right and left type are not equal",
                                    )?;
                                }
                                Type::Int(left)
                            }
                            IntWithOverflow(_int_op) => {
                                let Type::Int(int_ty) = left else {
                                    throw_ill_formed!(
                                        "BinOp::IntWithOverflow: invalid left type"
                                    );
                                };
                                ensure_wf(
                                    right == Type::Int(int_ty),
                                    "BinOp::IntWithOverflow: invalid right type",
                                )?;
                                int_ty.with_overflow::<T>()
                            }
                            Rel(rel_op) => {
                                ensure_wf(
                                    matches!(left, Type::Int(_) | Type::Bool | Type::Ptr(_)),
                                    "BinOp::Rel: invalid left type",
                                )?;
                                ensure_wf(right == left, "BinOp::Rel: invalid right type")?;
                                match rel_op {
                                    RelOp::Cmp => Type::Int(IntType::I8),
                                    _ => Type::Bool,
                                }
                            }
                            PtrOffset { inbounds: _ } => {
                                let Type::Ptr(left_ptr_ty) = left else {
                                    throw_ill_formed!(
                                        "BinOp::PtrOffset: invalid left type: not a pointer"
                                    );
                                };
                                if left_ptr_ty.meta_kind() != PointerMetaKind::None {
                                    throw_ill_formed!(
                                        "BinOp::PtrOffset: invalid left type: unsized pointee"
                                    );
                                }
                                ensure_wf(
                                    matches!(right, Type::Int(_)),
                                    "BinOp::PtrOffset: invalid right type",
                                )?;
                                left
                            }
                            PtrOffsetFrom { inbounds: _, nonneg: _ } => {
                                let Type::Ptr(left_ptr_ty) = left else {
                                    throw_ill_formed!(
                                        "BinOp::PtrOffsetFrom: invalid left type: not a pointer"
                                    );
                                };
                                if left_ptr_ty.meta_kind() != PointerMetaKind::None {
                                    throw_ill_formed!(
                                        "BinOp::PtrOffsetFrom: invalid left type: unsized pointee"
                                    );
                                }
                                let Type::Ptr(right_ptr_ty) = right else {
                                    throw_ill_formed!(
                                        "BinOp::PtrOffsetFrom: invalid right type: not a pointer"
                                    );
                                };
                                if right_ptr_ty.meta_kind() != PointerMetaKind::None {
                                    throw_ill_formed!(
                                        "BinOp::PtrOffsetFrom: invalid right type: unsized pointee"
                                    );
                                }
                                let isize_int = IntType {
                                    signed: Signed,
                                    size: T::PTR_SIZE,
                                };
                                Type::Int(isize_int)
                            }
                            ConstructWidePointer(ptr_ty) => {
                                let Type::Ptr(thin_ptr_ty) = left else {
                                    throw_ill_formed!(
                                        "BinOp::ConstructWidePointer: invalid left type: not a pointer"
                                    );
                                };
                                if thin_ptr_ty.meta_kind() != PointerMetaKind::None {
                                    throw_ill_formed!(
                                        "BinOp::ConstructWidePointer: invalid left type: not a thin pointer"
                                    );
                                }
                                let meta_ty = ptr_ty.meta_kind().ty::<T>();
                                if right != meta_ty {
                                    throw_ill_formed!(
                                        "BinOp::ConstructWidePointer: invalid right type: not metadata of target"
                                    );
                                }
                                Type::Ptr(ptr_ty)
                            }
                        }
                    }
                }
            },
        )
    }
}
impl PlaceExpr {
    fn check_wf<T: Target + libspecr::hidden::Obj>(
        self,
        locals: Map<LocalName, Type>,
        prog: Program,
    ) -> Result<Type> {
        use PlaceExpr::*;
        ret(
            match self {
                Local(name) => {
                    match locals.get(name) {
                        None => throw_ill_formed!("PlaceExpr::Local: unknown local name"),
                        Some(local) => local,
                    }
                }
                Deref { operand, ty } => {
                    let operand = operand.extract();
                    {
                        ty.check_wf::<T>(prog)?;
                        let op_ty = operand.check_wf::<T>(locals, prog)?;
                        let Type::Ptr(op_ptr_ty) = op_ty else {
                            throw_ill_formed!("PlaceExpr::Deref: invalid operand type");
                        };
                        ensure_wf(
                            op_ptr_ty.meta_kind() == ty.meta_kind(),
                            "PlaceExpr::Deref: metadata kind of operand and type don't match",
                        )?;
                        ty
                    }
                }
                Field { root, field } => {
                    let root = root.extract();
                    {
                        let root = root.check_wf::<T>(locals, prog)?;
                        let field_ty = match root {
                            Type::Tuple { sized_fields, unsized_field, .. } => {
                                let unsized_field = unsized_field.extract();
                                {
                                    if field >= 0 && field < sized_fields.len() {
                                        (sized_fields).index_at(field).1
                                    } else if field == sized_fields.len() {
                                        let Some(unsized_ty) = unsized_field else {
                                            throw_ill_formed!("PlaceExpr::Field: invalid field");
                                        };
                                        unsized_ty
                                    } else {
                                        throw_ill_formed!("PlaceExpr::Field: invalid field");
                                    }
                                }
                            }
                            Type::Union { fields, .. } => {
                                match fields.get(field) {
                                    None => throw_ill_formed!("PlaceExpr::Field: invalid field"),
                                    Some(field) => field.1,
                                }
                            }
                            _ => {
                                throw_ill_formed!(
                                    "PlaceExpr::Field: expression does not match type"
                                )
                            }
                        };
                        field_ty
                    }
                }
                Index { root, index } => {
                    let root = root.extract();
                    let index = index.extract();
                    {
                        let root = root.check_wf::<T>(locals, prog)?;
                        let index = index.check_wf::<T>(locals, prog)?;
                        ensure_wf(
                            matches!(index, Type::Int(_)),
                            "PlaceExpr::Index: invalid index type",
                        )?;
                        match root {
                            Type::Array { elem, .. } | Type::Slice { elem } => {
                                let elem = elem.extract();
                                elem
                            }
                            _ => {
                                throw_ill_formed!(
                                    "PlaceExpr::Index: expression type is not indexable"
                                )
                            }
                        }
                    }
                }
                Downcast { root, discriminant } => {
                    let root = root.extract();
                    {
                        let root = root.check_wf::<T>(locals, prog)?;
                        match root {
                            Type::Enum { variants, .. } => {
                                let Some(variant) = variants.get(discriminant) else {
                                    throw_ill_formed!(
                                        "PlaceExpr::Downcast: invalid discriminant"
                                    );
                                };
                                variant.ty
                            }
                            _ => {
                                throw_ill_formed!("PlaceExpr::Downcast: invalid root type")
                            }
                        }
                    }
                }
            },
        )
    }
}
impl ArgumentExpr {
    fn check_wf<T: Target + libspecr::hidden::Obj>(
        self,
        locals: Map<LocalName, Type>,
        prog: Program,
    ) -> Result<Type> {
        ret(
            match self {
                ArgumentExpr::ByValue(value) => value.check_wf::<T>(locals, prog)?,
                ArgumentExpr::InPlace(place) => place.check_wf::<T>(locals, prog)?,
            },
        )
    }
}
impl Statement {
    fn check_wf<T: Target + libspecr::hidden::Obj>(
        self,
        func: Function,
        prog: Program,
    ) -> Result<()> {
        use Statement::*;
        match self {
            Assign { destination, source } => {
                let left = destination.check_wf::<T>(func.locals, prog)?;
                let right = source.check_wf::<T>(func.locals, prog)?;
                ensure_wf(
                    left == right,
                    "Statement::Assign: destination and source type differ",
                )?;
                assert!(
                    right.layout::< T > ().is_sized(),
                    "ValueExpr always return sized types"
                );
            }
            PlaceMention(place) => {
                place.check_wf::<T>(func.locals, prog)?;
            }
            SetDiscriminant { destination, value } => {
                let Type::Enum { variants, .. } = destination
                    .check_wf::<T>(func.locals, prog)? else {
                    throw_ill_formed!("Statement::SetDiscriminant: invalid type");
                };
                if variants.get(value) == None {
                    throw_ill_formed!(
                        "Statement::SetDiscriminant: invalid discriminant write"
                    )
                }
            }
            Validate { place, fn_entry: _ } => {
                let ty = place.check_wf::<T>(func.locals, prog)?;
                ensure_wf(
                    ty.layout::<T>().is_sized(),
                    "Statement::Validate: unsized place",
                )?;
            }
            Deinit { place } => {
                let ty = place.check_wf::<T>(func.locals, prog)?;
                ensure_wf(
                    ty.layout::<T>().is_sized(),
                    "Statement::Deinit: unsized place",
                )?;
            }
            StorageLive(local) => {
                ensure_wf(
                    func.locals.contains_key(local),
                    "Statement::StorageLive: invalid local variable",
                )?;
            }
            StorageDead(local) => {
                ensure_wf(
                    func.locals.contains_key(local),
                    "Statement::StorageDead: invalid local variable",
                )?;
                if local == func.ret || func.args.any(|arg_name| local == arg_name) {
                    throw_ill_formed!(
                        "Statement::StorageDead: trying to mark argument or return local as dead"
                    );
                }
            }
        }
        ret(())
    }
}
/// Predicate to indicate if integer bin-op can be used for atomic fetch operations.
/// Needed for atomic fetch operations.
///
/// We limit the binops that are allowed to be atomic based on current LLVM and Rust API exposures.
fn is_atomic_binop(op: IntBinOp) -> bool {
    use IntBinOp as B;
    match op {
        B::Add | B::Sub => true,
        _ => false,
    }
}
impl Terminator {
    /// Check the terminator and the block transitions.
    /// `block_kind` is the kind of the block in which the terminator is used.
    fn check_wf<T: Target + libspecr::hidden::Obj>(
        self,
        block_kind: BbKind,
        func: Function,
        prog: Program,
    ) -> Result<()> {
        use Terminator::*;
        match self {
            Goto(block_name) => {
                func.check_next_block(block_kind, block_name)?;
            }
            Switch { value, cases, fallback } => {
                let ty = value.check_wf::<T>(func.locals, prog)?;
                let Type::Int(switch_ty) = ty else {
                    throw_ill_formed!("Terminator::Switch: switch is not Int")
                };
                for (case, next_block) in cases.iter() {
                    ensure_wf(
                        switch_ty.can_represent(case),
                        "Terminator::Switch: value does not fit in switch type",
                    )?;
                    func.check_next_block(block_kind, next_block)?;
                }
                func.check_next_block(block_kind, fallback)?;
            }
            Unreachable => {}
            Intrinsic { intrinsic, arguments, ret, next_block } => {
                let ret_ty = ret.check_wf::<T>(func.locals, prog)?;
                ensure_wf(
                    ret_ty.layout::<T>().is_sized(),
                    "Terminator::Intrinsic: unsized return type",
                )?;
                for arg in arguments {
                    let arg_ty = arg.check_wf::<T>(func.locals, prog)?;
                    ensure_wf(
                        arg_ty.layout::<T>().is_sized(),
                        "Terminator::Intrinsic: unsized argument type",
                    )?;
                }
                match intrinsic {
                    IntrinsicOp::AtomicFetchAndOp(op) => {
                        if !is_atomic_binop(op) {
                            throw_ill_formed!(
                                "IntrinsicOp::AtomicFetchAndOp: non atomic op"
                            );
                        }
                    }
                    _ => {}
                }
                if let Some(next_block) = next_block {
                    func.check_next_block(block_kind, next_block)?;
                }
            }
            Call {
                callee,
                calling_convention: _,
                arguments,
                ret,
                next_block,
                unwind_block,
            } => {
                let ty = callee.check_wf::<T>(func.locals, prog)?;
                ensure_wf(
                    matches!(ty, Type::Ptr(PtrType::FnPtr)),
                    "Terminator::Call: invalid type",
                )?;
                let ret_ty = ret.check_wf::<T>(func.locals, prog)?;
                ensure_wf(
                    ret_ty.layout::<T>().is_sized(),
                    "Terminator::Call: unsized return type",
                )?;
                for arg in arguments {
                    let arg_ty = arg.check_wf::<T>(func.locals, prog)?;
                    ensure_wf(
                        arg_ty.layout::<T>().is_sized(),
                        "Terminator::Call: unsized argument type",
                    )?;
                }
                if let Some(next_block) = next_block {
                    func.check_next_block(block_kind, next_block)?;
                }
                if let Some(unwind_block) = unwind_block {
                    func.check_unwind_block(block_kind, unwind_block)?;
                }
            }
            Return => {
                ensure_wf(
                    block_kind == BbKind::Regular,
                    "Terminator::Return has to be called in a regular block",
                )?;
            }
            StartUnwind { unwind_payload, unwind_block } => {
                let payload_type = unwind_payload.check_wf::<T>(func.locals, prog)?;
                ensure_wf(
                    payload_type
                        == Type::Ptr(PtrType::Raw {
                            meta_kind: PointerMetaKind::None,
                        }),
                    "Terminator::StartUnwind: the unwind payload should be a raw pointer",
                )?;
                ensure_wf(
                    block_kind == BbKind::Regular,
                    "Terminator::StartUnwind has to be called in a regular block",
                )?;
                func.check_unwind_block(block_kind, unwind_block)?;
            }
            StopUnwind(next_block) => {
                ensure_wf(
                    block_kind == BbKind::Catch,
                    "Terminator::StopUnwind has to be called in a catch block",
                )?;
                func.check_next_block(BbKind::Regular, next_block)?;
            }
            ResumeUnwind => {
                ensure_wf(
                    block_kind == BbKind::Cleanup,
                    "Terminator::ResumeUnwind: has to be called in cleanup block",
                )?;
            }
        }
        ret(())
    }
}
impl Function {
    fn check_wf<T: Target + libspecr::hidden::Obj>(self, prog: Program) -> Result<()> {
        for ty in self.locals.values() {
            ensure_wf(ty.layout::<T>().is_sized(), "Function: unsized local variable")?;
            ty.check_wf::<T>(prog)?;
        }
        let mut start_live: Set<LocalName> = Set::new();
        for arg in self.args {
            ensure_wf(
                self.locals.contains_key(arg),
                "Function: argument local does not exist",
            )?;
            if start_live.try_insert(arg).is_err() {
                throw_ill_formed!("Function: two arguments refer to the same local");
            }
        }
        ensure_wf(
            self.locals.contains_key(self.ret),
            "Function: return local does not exist",
        )?;
        if start_live.try_insert(self.ret).is_err() {
            throw_ill_formed!("Function: return local is also used for an argument");
        }
        for block in self.blocks.values() {
            for statement in block.statements {
                statement.check_wf::<T>(self, prog)?;
            }
            block.terminator.check_wf::<T>(block.kind, self, prog)?;
        }
        ret(())
    }
    /// Checks whether the next block exists and has the correct block kind.
    fn check_next_block(
        self,
        expected_block_kind: BbKind,
        next_block_name: BbName,
    ) -> Result<()> {
        let Some(next_block) = self.blocks.get(next_block_name) else {
            throw_ill_formed!("Terminator: next block does not exist");
        };
        ensure_wf(
            next_block.kind == expected_block_kind,
            "Terminator: next block has the wrong block kind",
        )?;
        ret(())
    }
    /// Checks whether the unwind block exists and has the correct block kind.
    fn check_unwind_block(
        self,
        current_block_kind: BbKind,
        unwind_block_name: BbName,
    ) -> Result<()> {
        let expected_block_kinds = match current_block_kind {
            BbKind::Regular => list![BbKind::Cleanup, BbKind::Catch],
            BbKind::Cleanup | BbKind::Terminate => list![BbKind::Terminate],
            BbKind::Catch => {
                throw_ill_formed!(
                    "Terminator: unwinding is not allowed in a catch block"
                )
            }
        };
        let Some(unwind_block) = self.blocks.get(unwind_block_name) else {
            throw_ill_formed!("Terminator: unwind block does not exist");
        };
        ensure_wf(
            expected_block_kinds.any(|kind| kind == unwind_block.kind),
            "Terminator: unwind block has the wrong block kind",
        )?;
        ret(())
    }
}
impl Relocation {
    fn check_wf(self, globals: Map<GlobalName, Global>) -> Result<()> {
        let Some(global) = globals.get(self.name) else {
            throw_ill_formed!("Relocation: invalid global name");
        };
        let size = Size::from_bytes(global.bytes.len()).unwrap();
        ensure_wf(self.offset <= size, "Relocation: offset out-of-bounds")?;
        ret(())
    }
}
impl Program {
    fn check_wf<T: Target + libspecr::hidden::Obj>(self) -> Result<()> {
        for (_name, vtable) in self.vtables {
            ensure_wf(
                vtable.size.bytes() % vtable.align.bytes() == 0,
                "Program: size stored in vtable not a multiple of alignment",
            )?;
            UnsafeCellStrategy::check_cells(vtable.cells, vtable.size)?;
            let Some(trait_methods) = self.traits.get(vtable.trait_name) else {
                throw_ill_formed!("Program: vtable for unknown trait");
            };
            let methods = vtable.methods.keys().collect::<Set<_>>();
            ensure_wf(
                methods == trait_methods,
                "Program: vtable has not the right set of methods",
            )?;
        }
        for function in self.functions.values() {
            function.check_wf::<T>(self)?;
        }
        let Some(start) = self.functions.get(self.start) else {
            throw_ill_formed!("Program: start function does not exist");
        };
        ensure_wf(
            start.calling_convention == CallingConvention::C,
            "Program: start function has invalid calling convention",
        )?;
        let ret_layout = (start.locals).index_at(start.ret).layout::<T>();
        ensure_wf(
            ret_layout == LayoutStrategy::Sized(Size::ZERO, Align::ONE),
            "Program: start function return local has invalid layout",
        )?;
        ensure_wf(start.args.is_empty(), "Program: start function has arguments")?;
        for (_name, global) in self.globals {
            let size = Size::from_bytes(global.bytes.len()).unwrap();
            for (offset, relocation) in global.relocations {
                ensure_wf(
                    offset + T::PTR_SIZE <= size,
                    "Program: invalid global pointer value",
                )?;
                relocation.check_wf(self.globals)?;
            }
        }
        ret(())
    }
}
/// The types of MiniRust.
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
pub enum Type {
    Int(IntType),
    Bool,
    /// `Ptr` represents all pointer types: references, raw pointers, boxes, function and vtable pointers.
    /// A pointer type does *not* need the full pointee type, since (de)serializing a pointer does not
    /// require knowledge about the pointee. We only track the metadata kind and basic pointee information
    /// like size and alignment that is required to check reference validity. This also means types have a finite
    /// representation even when the Rust type is recursive.
    Ptr(PtrType),
    /// "Tuple" is used for all heterogeneous types, i.e., both Rust tuples and structs.
    Tuple {
        /// Fields must not overlap.
        sized_fields: Fields,
        /// The layout of the sized fiels, i.e., the head.
        sized_head_layout: TupleHeadLayout,
        /// A last field (in terms of offset), i.e., the tail, may contain an unsized type,
        /// then its offset is given by rounding the `end` of `sized_head_layout` up to the alignment of this type.
        unsized_field: libspecr::hidden::GcCow<Option<Type>>,
    },
    Array { elem: libspecr::hidden::GcCow<Type>, count: Int },
    /// Slices, i.e. `[T]` are unsized types which therefore cannot be represented as values.
    /// This type is also used for strings: `str` are treated as `[u8]`.
    Slice { elem: libspecr::hidden::GcCow<Type> },
    Union {
        /// Fields *may* overlap. Fields only exist for field access place projections,
        /// they are irrelevant for the representation relation.
        fields: Fields,
        /// A union can be split into multiple "chunks", where only the data inside those chunks is
        /// preserved, and data between chunks is lost (like padding in a struct).
        /// This is necessary to model the behavior of some `repr(C)` unions, see
        /// <https://github.com/rust-lang/unsafe-code-guidelines/issues/156> for details.
        chunks: List<(Offset, Size)>,
        /// The total size of the union, can indicate padding after the last chunk.
        size: Size,
        /// Total alignment of the union. Due to `repr(packed)` and `repr(align)`,
        /// this is independent of the fields' alignment.
        align: Align,
    },
    Enum {
        /// The map variants, each identified by a discriminant. Each variant is given by a type and its
        /// tag description. All variants are thought to "start at offset 0"; if the
        /// discriminant is encoded as an explicit tag, then that will be put into the
        /// padding of the active variant. (This means it is *not* safe to hand out mutable
        /// references to a variant at that type, as then the tag might be overwritten!)
        /// The Rust type `!` is encoded as an `Enum` with an empty list of variants.
        variants: Map<Int, Variant>,
        /// The `IntType` for the discriminant. This is used for the type of
        /// `GetDiscriminant` and `SetDiscriminant`. It is entirely independent of how
        /// the discriminant is represented in memory (the "tag").
        discriminant_ty: IntType,
        /// The decision tree to decode the discriminant from the tag at runtime.
        discriminator: Discriminator,
        /// The total size of the enum can indicate trailing padding.
        /// Must be large enough to contain all variants.
        size: Size,
        /// Total alignment of the enum. Due to `repr(packed)` and `repr(align)`,
        /// this is independent of the fields' alignment.
        align: Align,
    },
    /// A `dyn TraitName`. Commonly only used behind a pointer.
    TraitObject(TraitName),
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
pub struct IntType {
    pub signed: Signedness,
    pub size: Size,
}
pub type Fields = List<(Offset, Type)>;
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
pub struct Variant {
    /// The actual type of the variant.
    pub ty: Type,
    /// The information on where to store which values to write the tag.
    /// MUST NOT touch any bytes written by the actual type of the variant and vice
    /// versa. This is because we allow references/pointers to (enum) fields which
    /// should be able to dereference without having to deal with the tag.
    pub tagger: Map<Offset, (IntType, Int)>,
}
/// The decision tree that computes the discriminant out of the tag for a specific
/// enum type.
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
pub enum Discriminator {
    /// We know the discriminant.
    Known(Int),
    /// Tag decoding failed, there is no valid discriminant.
    Invalid,
    /// We don't know the discriminant, so we branch on the value of a specific value.
    Branch {
        offset: Offset,
        value_type: IntType,
        fallback: libspecr::hidden::GcCow<Discriminator>,
        /// An left-inclusive right-exclusive range of values that map to some Discriminator.
        children: Map<(Int, Int), Discriminator>,
    },
}
/// Returns the type of a zero-sized, one aligned-tuple.
pub fn unit_ty() -> Type {
    let size = Size::from_bytes(<i32 as Into<Int>>::into(0)).unwrap();
    let align = Align::from_bytes(<i32 as Into<Int>>::into(1)).unwrap();
    Type::Tuple {
        sized_fields: List::new(),
        sized_head_layout: TupleHeadLayout {
            end: size,
            align,
            packed_align: None,
        },
        unsized_field: libspecr::hidden::GcCow::new(None),
    }
}
fn unit_value<M: Memory + libspecr::hidden::Obj>() -> Value<M> {
    Value::Tuple(list![])
}
fn unit_type() -> Type {
    Type::Tuple {
        sized_fields: list![],
        sized_head_layout: TupleHeadLayout {
            end: Size::ZERO,
            align: Align::ONE,
            packed_align: None,
        },
        unsized_field: libspecr::hidden::GcCow::new(None),
    }
}
/// Check whether the two types are compatible in function calls.
///
/// This means *at least* they have the same size and alignment (for on-stack argument passing).
/// However, when arguments get passed in registers, more details become relevant, so we require
/// almost full structural equality.
fn check_abi_compatibility(caller_ty: Type, callee_ty: Type) -> bool {
    match (caller_ty, callee_ty) {
        (Type::Int(caller_ty), Type::Int(callee_ty)) => caller_ty == callee_ty,
        (Type::Bool, Type::Bool) => true,
        (Type::Ptr(caller_ty), Type::Ptr(callee_ty)) => {
            caller_ty.meta_kind() == callee_ty.meta_kind()
        }
        (
            Type::Tuple {
                sized_fields: caller_fields,
                sized_head_layout: caller_head_layout,
                unsized_field: caller_unsized_field,
            },
            Type::Tuple {
                sized_fields: callee_fields,
                sized_head_layout: callee_head_layout,
                unsized_field: callee_unsized_field,
            },
        ) => {
            let callee_unsized_field = callee_unsized_field.extract();
            let caller_unsized_field = caller_unsized_field.extract();
            {
                let (caller_size, caller_align) = caller_head_layout
                    .head_size_and_align();
                let (callee_size, callee_align) = callee_head_layout
                    .head_size_and_align();
                assert!(
                    caller_unsized_field.is_none(), "wf ensures all arugments are sized"
                );
                assert!(
                    callee_unsized_field.is_none(), "wf ensures all arugments are sized"
                );
                caller_fields.len() == callee_fields.len()
                    && caller_fields
                        .zip(callee_fields)
                        .all(|(caller_field, callee_field)| {
                            caller_field.0 == callee_field.0
                                && check_abi_compatibility(caller_field.1, callee_field.1)
                        }) && caller_size == callee_size && caller_align == callee_align
            }
        }
        (
            Type::Array { elem: caller_elem, count: caller_count },
            Type::Array { elem: callee_elem, count: callee_count },
        ) => {
            let callee_elem = callee_elem.extract();
            let caller_elem = caller_elem.extract();
            check_abi_compatibility(caller_elem, callee_elem)
                && caller_count == callee_count
        }
        (
            Type::Union {
                fields: caller_fields,
                chunks: caller_chunks,
                size: caller_size,
                align: caller_align,
            },
            Type::Union {
                fields: callee_fields,
                chunks: callee_chunks,
                size: callee_size,
                align: callee_align,
            },
        ) => {
            caller_fields.len() == callee_fields.len()
                && caller_fields
                    .zip(callee_fields)
                    .all(|(caller_field, callee_field)| {
                        caller_field.0 == callee_field.0
                            && check_abi_compatibility(caller_field.1, callee_field.1)
                    }) && caller_chunks == callee_chunks && caller_size == callee_size
                && caller_align == callee_align
        }
        (
            Type::Enum {
                variants: caller_variants,
                discriminator: caller_discriminator,
                discriminant_ty: caller_discriminant_ty,
                size: caller_size,
                align: caller_align,
            },
            Type::Enum {
                variants: callee_variants,
                discriminator: callee_discriminator,
                discriminant_ty: callee_discriminant_ty,
                size: callee_size,
                align: callee_align,
            },
        ) => {
            caller_variants.len() == callee_variants.len()
                && caller_variants
                    .iter()
                    .all(|(caller_discriminant, caller_variant)| {
                        let Some(callee_variant) = callee_variants
                            .get(caller_discriminant) else {
                            return false;
                        };
                        check_abi_compatibility(caller_variant.ty, callee_variant.ty)
                            && caller_variant.tagger == callee_variant.tagger
                    }) && caller_discriminator == callee_discriminator
                && caller_discriminant_ty == callee_discriminant_ty
                && caller_size == callee_size && caller_align == callee_align
        }
        _ => false,
    }
}
impl<M: Memory + libspecr::hidden::Obj> ConcurrentMemory<M> {
    fn deinit(
        &mut self,
        ptr: ThinPointer<M::Provenance>,
        len: Size,
        align: Align,
    ) -> Result {
        self.store(
            ptr,
            list![AbstractByte::Uninit; len.bytes()],
            align,
            Atomicity::None,
        )?;
        ret(())
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
pub enum LockState {
    Unlocked,
    LockedBy(ThreadId),
}
pub type LockId = Int;
