# MiniRust Abstract Syntax

This defines the abstract syntax of MiniRust programs.

## Expressions

MiniRust has two kinds of expressions:
*value expressions* evaluate to a value and are found, in particular, on the right-hand side of assignments;
*place expressions* evaluate to a place and are found, in particular, in the left-hand side of assignments.

Obviously, these are all quite incomplete still.

### Value expressions

```rust
/// A "value expression" evaluates to a `Value`.
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
        #[specr::indirection]
        expr: ValueExpr,
        /// The union type, needs to be `Type::Union`
        union_ty: Type,
    },
    /// A variant of an enum type.
    Variant {
        /// The discriminant of the variant.
        discriminant: Int,
        /// The `ValueExpr` for the variant.
        #[specr::indirection]
        data: ValueExpr,
        /// The enum type, needs to be `Type::Enum`.
        enum_ty: Type,
    },
    /// Read the discriminant of an enum type.
    /// As we don't need to know the validity of the inner data
    /// we don't fully load the variant value.
    GetDiscriminant {
        /// The place where the enum is located.
        #[specr::indirection]
        place: PlaceExpr,
    },
    /// Load a value from memory.
    Load {
        /// The place to load from.
        #[specr::indirection]
        source: PlaceExpr,
    },
    /// Create a pointer (raw pointer or reference) to a place.
    AddrOf {
        /// The place to create a pointer to.
        #[specr::indirection]
        target: PlaceExpr,
        /// The type of the created pointer.
        ptr_ty: PtrType,
    },
    /// Unary operators.
    UnOp {
        operator: UnOp,
        #[specr::indirection]
        operand: ValueExpr,
    },
    /// Binary operators.
    BinOp {
        operator: BinOp,
        #[specr::indirection]
        left: ValueExpr,
        #[specr::indirection]
        right: ValueExpr,
    },
}

/// Constants are basically values, but cannot have explicit provenance.
/// Currently we do not support Ptr and Union constants.
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

pub enum IntUnOp {
    /// Negate an integer value arithmetically (`x` becomes `-x`).
    Neg,
    /// Bitwise-invert an integer value
    BitNot,
    /// Used for the intrinsic ˋctpopˋ.
    CountOnes,
}
pub enum CastOp {
    /// Argument can be any integer type; returns the given integer type.
    IntToInt(IntType),
    /// Transmute the value to a different type.
    /// The program is well-formed even if the output type has a different size than the
    /// input type, but the operation is UB in that case.
    Transmute(Type),
}
pub enum UnOp {
    /// An operation on an integer; returns an integer of the same type.
    Int(IntUnOp),
    /// A form of cast; the return type is given by the specific cast operation.
    Cast(CastOp),
    // The following 2 operations correspond to the two parts of `<*const T>::to_raw_parts()`.
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
```

### Place expressions

```rust
/// A "place expression" evaluates to a `Place`.
pub enum PlaceExpr {
    /// Denotes a local variable.
    Local(LocalName),
    /// Dereference a value (of pointer/reference type).
    Deref {
        #[specr::indirection]
        operand: ValueExpr,
        // The type of the newly created place.
        ty: Type,
    },
    /// Project to a field.
    Field {
        /// The place to base the projection on.
        #[specr::indirection]
        root: PlaceExpr,
        /// The field to project to.
        field: Int,
    },
    /// Index to an array or slice element.
    Index {
        /// The array or slice to index into.
        #[specr::indirection]
        root: PlaceExpr,
        /// The index to project to.
        #[specr::indirection]
        index: ValueExpr,
    },
    /// Enum variant downcast.
    Downcast {
        /// The base enum to project to the specific variant.
        #[specr::indirection]
        root: PlaceExpr,
        /// The discriminant of the variant to project to.
        discriminant: Int,
    },
}
```

## Statements, terminators

Next, the statements and terminators that MiniRust programs consist of:

```rust
pub enum Statement {
    /// Copy value from `source` to `destination`.
    Assign {
        destination: PlaceExpr,
        source: ValueExpr,
    },
    /// Evaluate a place without accessing it.
    /// This is the result of translating e.g. `let _ = place;`.
    PlaceMention(PlaceExpr),
    /// Set the discriminant of the variant at `destination` to `value`.
    SetDiscriminant {
        destination: PlaceExpr,
        value: Int,
    },
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
    Deinit {
        place: PlaceExpr,
    },
    /// Allocate the backing store for this local.
    StorageLive(LocalName),
    /// Deallocate the backing store for this local.
    StorageDead(LocalName),
}

pub enum Terminator {
    /// Just jump to the next block.
    Goto(BbName),
    /// `value` needs to evaluate to a `Value::Int`.
    /// `cases` map those values to blocks to jump to and therefore have to have the equivalent type.
    /// If no value matches we fall back to the block given in `fallback`.
    Switch {
        value: ValueExpr,
        cases: Map<Int, BbName>,
        fallback: BbName,
    },
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
        unwind_payload:  ValueExpr,
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
pub enum CallingConvention {
    Rust, C,
}

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
```

## Programs and functions

Finally, the general structure of programs and functions:

```rust
/// Opaque types of names for functions, vtables, trait methods, and globals.
/// The internal representations of these types do not matter.
pub struct FnName(pub libspecr::Name);
pub struct GlobalName(pub libspecr::Name);
pub struct VTableName(pub libspecr::Name);
pub struct TraitMethodName(pub libspecr::Name);

/// A closed MiniRust program.
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
pub struct LocalName(pub libspecr::Name);
pub struct BbName(pub libspecr::Name);

/// A MiniRust function.
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
pub struct BasicBlock {
    pub statements: List<Statement>,
    pub terminator: Terminator,
    pub kind: BbKind,
}

/// The kind of a basic block in the CFG.
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
pub struct Relocation {
    /// The name of the global allocation we are pointing into.
    pub name: GlobalName,
    /// The offset within that allocation.
    pub offset: Offset,
}

/// A vtable for a trait-type pair.
/// This is pointed to by the trait object metadata.
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
```
