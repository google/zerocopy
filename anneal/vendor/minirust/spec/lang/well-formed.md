# MiniRust well-formedness requirements

The various syntactic constructs of MiniRust (types, functions, ...) come with well-formedness requirements: certain invariants need to be satisfied for this to be considered a well-formed program.
The idea is that for well-formed programs, the `step` function will never panic.
Those requirements are defined in this file.

Note that `check_wf` functions for testing well-formedness return `Result<()>` to pass information in case an error occured.

We use the following helper function to convert Boolean checks into this form.

```rust
fn ensure_wf(b: bool, msg: &str) -> Result<()> {
    if !b { throw_ill_formed!("{}", msg); }
    ret(())
}
```

## Well-formed layouts and types

```rust
impl IntType {
    fn check_wf(self) -> Result<()> {
        // In particular, this checks that the size is at least one byte.
        ensure_wf(self.size.bytes().is_power_of_two(), "IntType: size is not power of two")
    }
}

impl TupleHeadLayout {
    fn check_wf<T: Target>(self) -> Result<()> {
        ensure_wf(T::valid_size(self.end), "TupleHeadLayout: end not valid")?;
        if let Some(packed) = self.packed_align {
            ensure_wf(self.align <= packed, "TupleHeadLayout: align bigger than packed attribute")?;
        }
        ret(())
    }
}

impl LayoutStrategy {
    /// This does *not* require that size is a multiple of align!
    fn check_wf<T: Target>(self, prog: Program) -> Result<()> {
        // The align type is always well formed.
        match self {
            LayoutStrategy::Sized(size, _align) => {
                ensure_wf(T::valid_size(size), "LayoutStrategy: size not valid")?;
            }
            LayoutStrategy::Slice(size, _align) => {
                ensure_wf(T::valid_size(size), "LayoutStrategy: element size not valid")?;
            }
            LayoutStrategy::TraitObject(trait_name) => {
                ensure_wf(prog.traits.contains_key(trait_name), "LayoutStrategy: trait name doesn't exist")?;
            }
            LayoutStrategy::Tuple { head, tail } => {
                head.check_wf::<T>()?;
                tail.check_wf::<T>(prog)?;
                ensure_wf(!tail.is_sized(), "LayoutStrategy: tuple with sized tail")?;
            }
        };

        ret(())
    }

    fn check_aligned(self) -> Result<()> {
        match self {
            LayoutStrategy::Sized(size, align) => {
                ensure_wf(size.bytes() % align.bytes() == 0, "check_aligned: size not a multiple of alignment")?;
            }
            LayoutStrategy::Slice(size, align) => {
                ensure_wf(size.bytes() % align.bytes() == 0, "check_aligned: element size not a multiple of alignment")?;
            }
            // WF for vtables ensures the size is aligned.
            LayoutStrategy::TraitObject(..) => (),
            // The size and align computation aligns the size of the full tuple.
            LayoutStrategy::Tuple { tail, .. } => tail.check_aligned()?,
        };

        ret(())
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

    fn check_wf<T: Target>(self, layout: LayoutStrategy) -> Result<()> {
        match (self, layout) {
            (UnsafeCellStrategy::Sized { cells }, LayoutStrategy::Sized(size, _)) => {
                Self::check_cells(cells, size)?;
            },
            (UnsafeCellStrategy::Slice { element_cells }, LayoutStrategy::Slice(size, _)) => {
                Self::check_cells(element_cells, size)?;
            },
            (UnsafeCellStrategy::TraitObject, LayoutStrategy::TraitObject(..)) => {},
            (UnsafeCellStrategy::Tuple { head_cells, tail_cells }, LayoutStrategy::Tuple { head, tail }) => {
                Self::check_cells(head_cells, head.end)?;
                tail_cells.check_wf::<T>(tail)?;
            },
            _ => {
                ensure_wf(false, "UnsafeCellStrategy and LayoutStrategy variants do not match")?;
            },
        };
        ret(())
    }
}

impl PointeeInfo {
    fn check_wf<T: Target>(self, prog: Program) -> Result<()> {
        // We do *not* require that size is a multiple of align!
        self.layout.check_wf::<T>(prog)?;
        self.unsafe_cells.check_wf::<T>(self.layout)?;

        ret(())
    }
}

impl PtrType {
    fn check_wf<T: Target>(self, prog: Program) -> Result<()> {
        match self {
            PtrType::Ref { pointee, .. } | PtrType::Box { pointee } => {
                pointee.check_wf::<T>(prog)?;
            }
            PtrType::Raw { .. } | PtrType::FnPtr => (),
            PtrType::VTablePtr(trait_name) => {
                ensure_wf(prog.traits.contains_key(trait_name), "PtrType::VTablePtr: trait name doesn't exist")?;
            }
        }

        ret(())
    }
}

impl Type {
    fn check_wf<T: Target>(self, prog: Program) -> Result<()> {
        use Type::*;

        match self {
            Int(int_type) => {
                int_type.check_wf()?;
            }
            Bool => (),
            Ptr(ptr_type) => {
                ptr_type.check_wf::<T>(prog)?;
            }
            Tuple { mut sized_fields, unsized_field, sized_head_layout } => {
                // The fields must not overlap.
                // We check fields in the order of their (absolute) offsets.
                sized_fields.sort_by_key(|(offset, _ty)| offset);
                let mut last_end = Size::ZERO;
                for (offset, ty) in sized_fields {
                    // Recursively check the field type.
                    ty.check_wf::<T>(prog)?;
                    // Ensure it fits after the one we previously checked.
                    ensure_wf(offset >= last_end, "Type::Tuple: overlapping fields")?;
                    ensure_wf(ty.layout::<T>().is_sized(), "Type::Tuple: unsized field type in head")?;
                    last_end = offset + ty.layout::<T>().expect_size("ensured to be sized above");
                }
                // The unsized field must actually be unsized.
                if let Some(unsized_field) = unsized_field {
                    unsized_field.check_wf::<T>(prog)?;
                    ensure_wf(!unsized_field.layout::<T>().is_sized(), "Type::Tuple: sized unsized field type")?;
                }
                // And they must all fit into the size.
                // The size is in turn checked to be valid for `M`, and hence all offsets are valid, too.
                sized_head_layout.check_wf::<T>()?;
                ensure_wf(sized_head_layout.end >= last_end, "Type::Tuple: size of fields is bigger than the end of the sized head")?;
                if sized_head_layout.packed_align.is_some() {
                    // If the tuple is sized, the packed attribute is already embedded in the offsets and total align.
                    ensure_wf(unsized_field.is_some(), "Type::Tuple: meaningless packed align for sized tuple")?;
                }
            }
            Array { elem, count } => {
                ensure_wf(count >= 0, "Type::Array: negative amount of elements")?;
                ensure_wf(elem.layout::<T>().is_sized(), "Type::Array: unsized element type")?;
                elem.check_wf::<T>(prog)?;
            }
            Slice { elem } => {
                ensure_wf(elem.layout::<T>().is_sized(), "Type::Slice: unsized element type")?;
                elem.check_wf::<T>(prog)?;
            }
            Union { fields, size, chunks, align: _ } => {
                // The fields may overlap, but they must all fit the size.
                for (offset, ty) in fields {
                    ty.check_wf::<T>(prog)?;
                    ensure_wf(ty.layout::<T>().is_sized(), "Type::Union: unsized field type")?;
                    ensure_wf(
                        size >= offset + ty.layout::<T>().expect_size("ensured to be sized above"),
                        "Type::Union: field size does not fit union",
                    )?;
                    // This field may overlap with gaps between the chunks. That's perfectly normal
                    // when there is padding inside the field.
                    // FIXME: should we check that all the non-padding bytes of the field are in some chunk?
                    // But then we'd have to add a definition of "used (non-padding) bytes" in the spec, and then
                    // we may as well remove 'chunks' entirely and just compute the set of used bytes for
                    // encoding/decoding...
                }
                // The chunks must be sorted in their offsets and disjoint.
                // FIXME: should we relax this and allow arbitrary chunk order?
                let mut last_end = Size::ZERO;
                for (offset, size) in chunks {
                    ensure_wf(
                        offset >= last_end,
                        "Type::Union: chunks are not stored in ascending order",
                    )?;
                    last_end = offset + size;
                }
                // And they must all fit into the size.
                ensure_wf(size >= last_end, "Type::Union: chunks do not fit union")?;
            }
            Enum { variants, size, align, discriminator, discriminant_ty } => {
                // All the variants need to be well-formed and be the size of the enum so
                // we don't have to handle different sizes in the memory representation.
                // Also their alignment may not be larger than the total enum alignment and
                // all the values written by the tagger must fit into the variant.
                for (discriminant, variant) in variants {
                    ensure_wf(
                        discriminant_ty.can_represent(discriminant),
                        "Type::Enum: invalid value for discriminant"
                    )?;

                    variant.ty.check_wf::<T>(prog)?;
                    let LayoutStrategy::Sized(var_size, var_align) = variant.ty.layout::<T>() else {
                        throw_ill_formed!("Type::Enum: variant type is unsized")
                    };
                    ensure_wf(var_size == size, "Type::Enum: variant size is not the same as enum size")?;
                    ensure_wf(var_align <= align, "Type::Enum: invalid align requirement")?;
                    for (offset, (value_type, value)) in variant.tagger {
                        value_type.check_wf()?;
                        ensure_wf(value_type.can_represent(value), "Type::Enum: invalid tagger value")?;
                        ensure_wf(offset + value_type.size <= size, "Type::Enum tagger type size too big for enum")?;
                    }
                    // FIXME: check that the values written by the tagger do not overlap.
                }

                // check that all variants reached by the discriminator are valid,
                // that it never performs out-of-bounds accesses and all discriminant values
                // can be represented by the discriminant type.
                discriminator.check_wf::<T>(size, variants)?;
            }
            TraitObject(trait_name) => {
                ensure_wf(prog.traits.contains_key(trait_name), "Type::TraitObject: trait name doesn't exist")?;
            }
        }

        // Now that we know the type is well-formed,
        // we are allowed to call the layout function to check that the layout is valid and its size aligned.
        let layout = self.layout::<T>();
        layout.check_wf::<T>(prog)?;
        layout.check_aligned()?;
        // ensure consistent definitions.
        assert_eq!(layout.meta_kind(), self.meta_kind(), "Type::meta_kind() must match the Type::layout()'s kind");

        ret(())
    }
}

impl Discriminator {
    fn check_wf<T: Target>(self, size: Size, variants: Map<Int, Variant>) -> Result<()>  {
        match self {
            Discriminator::Known(discriminant) => ensure_wf(variants.get(discriminant).is_some(), "Discriminator: invalid discriminant"),
            Discriminator::Invalid => ret(()),
            Discriminator::Branch { offset, value_type, fallback, children } => {
                // Ensure that the value we branch on is stored in bounds and that all children all valid.
                value_type.check_wf()?;
                ensure_wf(offset + value_type.size <= size, "Discriminator: branch offset exceeds size")?;
                fallback.check_wf::<T>(size, variants)?;
                for (idx, ((start, end), discriminator)) in children.into_iter().enumerate() {
                    ensure_wf(value_type.can_represent(start), "Discriminator: invalid branch start bound")?;
                    // Since the end is exclusive we only need to represent the number before the end.
                    ensure_wf(value_type.can_represent(end - Int::ONE), "Discriminator: invalid branch end bound")?;
                    ensure_wf(start < end, "Discriminator: invalid bound values")?;
                    // Ensure that the ranges don't overlap.
                    ensure_wf(children.keys().enumerate().all(|(other_idx, (other_start, other_end))|
                                other_end <= start || other_start >= end || idx == other_idx), "Discriminator: branch ranges overlap")?;
                    discriminator.check_wf::<T>(size, variants)?;
                }
                ret(())
            }
        }
    }
}
```

## Well-formed expressions

```rust
impl Constant {
    /// Check that the constant has the expected type.
    /// Assumes that `ty` has already been checked.
    fn check_wf<T: Target>(self, ty: Type, prog: Program) -> Result<()> {
        // For now, we only support integer and boolean literals and pointers.
        // TODO: add more.
        match (self, ty) {
            (Constant::Int(i), Type::Int(int_type)) => {
                ensure_wf(int_type.can_represent(i), "Constant::Int: invalid int value")?;
            }
            (Constant::Bool(_), Type::Bool) => (),
            (Constant::GlobalPointer(relocation), Type::Ptr(_)) => {
                relocation.check_wf(prog.globals)?;
            }
            (Constant::FnPointer(fn_name), Type::Ptr(ptr_ty)) => {
                ensure_wf(matches!(ptr_ty, PtrType::FnPtr), "Constant::FnPointer: non function pointer type")?;
                ensure_wf(prog.functions.contains_key(fn_name), "Constant::FnPointer: invalid function name")?;
            }
            (Constant::VTablePointer(vtable_name), Type::Ptr(ptr_ty)) => {
                let Some(vtable) = prog.vtables.get(vtable_name) else {
                    throw_ill_formed!("Constant::VTablePointer: invalid vtable name");
                };
                ensure_wf(ptr_ty == PtrType::VTablePtr(vtable.trait_name), "Constant::VTablePointer: non or wrong vtable pointer type")?;
            }
            (Constant::PointerWithoutProvenance(addr), Type::Ptr(_)) => {
                ensure_wf(
                    addr.in_bounds(Signedness::Unsigned, T::PTR_SIZE),
                    "Constant::PointerWithoutProvenance: pointer out-of-bounds"
                )?;
            }
            _ => throw_ill_formed!("Constant: value does not match type"),
        }

        ret(())
    }
}

impl ValueExpr {
    #[allow(unused_braces)]
    fn check_wf<T: Target>(self, locals: Map<LocalName, Type>, prog: Program) -> Result<Type> {
        use ValueExpr::*;
        ret(match self {
            Constant(value, ty) => {
                ty.check_wf::<T>(prog)?;
                value.check_wf::<T>(ty, prog)?;
                ty
            }
            Tuple(exprs, t) => {
                t.check_wf::<T>(prog)?;

                match t {
                    Type::Tuple { sized_fields, unsized_field, .. } => {
                        ensure_wf(unsized_field.is_none(), "ValueExpr::Tuple: constructing an unsized tuple value")?;
                        ensure_wf(exprs.len() == sized_fields.len(), "ValueExpr::Tuple: invalid number of tuple fields")?;
                        for (e, (_offset, ty)) in exprs.zip(sized_fields) {
                            let checked = e.check_wf::<T>(locals, prog)?;
                            ensure_wf(checked == ty, "ValueExpr::Tuple: invalid tuple field type")?;
                        }
                    },
                    Type::Array { elem, count } => {
                        ensure_wf(exprs.len() == count, "ValueExpr::Tuple: invalid number of array elements")?;
                        for e in exprs {
                            let checked = e.check_wf::<T>(locals, prog)?;
                            ensure_wf(checked == elem, "ValueExpr::Tuple: invalid array element type")?;
                        }
                    },
                    _ => throw_ill_formed!("ValueExpr::Tuple: expression does not match type"),
                }

                t
            }
            Union { field, expr, union_ty } => {
                union_ty.check_wf::<T>(prog)?;

                let Type::Union { fields, .. } = union_ty else {
                    throw_ill_formed!("ValueExpr::Union: invalid type")
                };

                ensure_wf(field < fields.len(), "ValueExpr::Union: invalid field length")?;
                let (_offset, ty) = fields[field];

                let checked = expr.check_wf::<T>(locals, prog)?;
                ensure_wf(checked == ty, "ValueExpr::Union: invalid field type")?;

                union_ty
            }
            Variant { discriminant, data, enum_ty } => {
                let Type::Enum { variants, .. } = enum_ty else {
                    throw_ill_formed!("ValueExpr::Variant: invalid type")
                };
                enum_ty.check_wf::<T>(prog)?;
                let Some(variant) = variants.get(discriminant) else {
                    throw_ill_formed!("ValueExpr::Variant: invalid discriminant");
                };

                let checked = data.check_wf::<T>(locals, prog)?;
                ensure_wf(checked == variant.ty, "ValueExpr::Variant: invalid type")?;
                enum_ty
            }
            GetDiscriminant { place } => {
                let Type::Enum { discriminant_ty, .. } = place.check_wf::<T>(locals, prog)? else {
                    throw_ill_formed!("ValueExpr::GetDiscriminant: invalid type");
                };
                Type::Int(discriminant_ty)
            }
            Load { source } => {
                let val_ty = source.check_wf::<T>(locals, prog)?;
                ensure_wf(val_ty.layout::<T>().is_sized(), "ValueExpr::Load: unsized value type")?;
                val_ty
            }
            AddrOf { target, ptr_ty } => {
                ptr_ty.check_wf::<T>(prog)?;
                let target_ty = target.check_wf::<T>(locals, prog)?;
                ensure_wf(target_ty.meta_kind() == ptr_ty.meta_kind(), "ValueExpr::AddrOf: mismatched metadata kind")?;
                // No check of how the alignment changes here -- that is purely a runtime constraint.
                Type::Ptr(ptr_ty)
            }
            UnOp { operator, operand } => {
                use lang::UnOp::*;

                let operand = operand.check_wf::<T>(locals, prog)?;
                match operator {
                    Int(int_op) => {
                        let Type::Int(int_ty) = operand else {
                            throw_ill_formed!("UnOp::Int: invalid operand");
                        };

                        let ret_ty = match int_op {
                            IntUnOp::CountOnes => IntType { signed: Unsigned, size: Size::from_bytes(4).unwrap() },
                            _ => int_ty,
                        };

                        Type::Int(ret_ty)
                    }
                    Cast(cast_op) => {
                        use lang::CastOp::*;
                        match cast_op {
                            IntToInt(int_ty) => {
                                ensure_wf(matches!(operand, Type::Int(_)), "Cast::IntToInt: invalid operand")?;
                                Type::Int(int_ty)
                            }
                            Transmute(new_ty) => {
                                ensure_wf(operand.layout::<T>().is_sized(), "Cast::Transmute: unsized source type")?;
                                ensure_wf(new_ty.layout::<T>().is_sized(), "Cast::Transmute: unsized target type")?;
                                new_ty
                            }
                        }
                    }
                    GetThinPointer => {
                        ensure_wf(matches!(operand, Type::Ptr(_)), "UnOp::GetThinPointer: invalid operand: not a pointer")?;
                        Type::Ptr(PtrType::Raw { meta_kind: PointerMetaKind::None })
                    }
                    GetMetadata => {
                        let Type::Ptr(ptr_ty) = operand else {
                            throw_ill_formed!("UnOp::GetMetadata: invalid operand: not a pointer");
                        };
                        // If the pointer does not have metadata, this will still be well-formed but return the unit type.
                        ptr_ty.meta_kind().ty::<T>()
                    }
                    ComputeSize(ty) | ComputeAlign(ty) => {
                        ty.check_wf::<T>(prog)?;
                        // A thin pointer can also be the target type, with unit metadata.
                        let meta_ty = ty.meta_kind().ty::<T>();
                        if operand != meta_ty {
                            throw_ill_formed!("UnOp::ComputeSize|ComputeAlign: invalid operand type: not metadata of type");
                        }
                        Type::Int(IntType::usize_ty::<T>())
                    }
                    VTableMethodLookup(method) => {
                        let Type::Ptr(PtrType::VTablePtr(trait_name)) = operand else {
                            throw_ill_formed!("UnOp::VTableMethodLookup: invalid operand: not a vtable pointer");
                        };

                        // The trait must exist since the type is well-formed.
                        let trait_methods = prog.traits[trait_name];
                        ensure_wf(trait_methods.contains(method), "UnOp::VTableMethodLookup: invalid operand: method doesn't exist in trait")?;

                        Type::Ptr(PtrType::FnPtr)
                    }
                }
            }
            BinOp { operator, left, right } => {
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
                        // Shift operators allow unequal left and right type
                        if !matches!(int_op, Shl | Shr | ShlUnchecked | ShrUnchecked) {
                            ensure_wf(left == right, "BinOp:Int: right and left type are not equal")?;
                        }
                        Type::Int(left)
                    }
                    IntWithOverflow(_int_op) => {
                        let Type::Int(int_ty) = left else {
                            throw_ill_formed!("BinOp::IntWithOverflow: invalid left type");
                        };
                        ensure_wf(right == Type::Int(int_ty), "BinOp::IntWithOverflow: invalid right type")?;
                        int_ty.with_overflow::<T>()
                    }
                    Rel(rel_op) => {
                        ensure_wf(matches!(left, Type::Int(_) | Type::Bool | Type::Ptr(_)), "BinOp::Rel: invalid left type")?;
                        ensure_wf(right == left, "BinOp::Rel: invalid right type")?;
                        match rel_op {
                            RelOp::Cmp => Type::Int(IntType::I8),
                            _ => Type::Bool,
                        }
                    }
                    PtrOffset { inbounds: _ } => {
                        let Type::Ptr(left_ptr_ty) = left else {
                            throw_ill_formed!("BinOp::PtrOffset: invalid left type: not a pointer");
                        };
                        if left_ptr_ty.meta_kind() != PointerMetaKind::None {
                            throw_ill_formed!("BinOp::PtrOffset: invalid left type: unsized pointee");
                        }
                        ensure_wf(matches!(right, Type::Int(_)), "BinOp::PtrOffset: invalid right type")?;
                        left
                    }
                    PtrOffsetFrom { inbounds: _, nonneg: _ } => {
                        let Type::Ptr(left_ptr_ty) = left else {
                            throw_ill_formed!("BinOp::PtrOffsetFrom: invalid left type: not a pointer");
                        };
                        if left_ptr_ty.meta_kind() != PointerMetaKind::None {
                            throw_ill_formed!("BinOp::PtrOffsetFrom: invalid left type: unsized pointee");
                        }
                        let Type::Ptr(right_ptr_ty) = right else {
                            throw_ill_formed!("BinOp::PtrOffsetFrom: invalid right type: not a pointer");
                        };
                        if right_ptr_ty.meta_kind() != PointerMetaKind::None {
                            throw_ill_formed!("BinOp::PtrOffsetFrom: invalid right type: unsized pointee");
                        }
                        let isize_int = IntType { signed: Signed, size: T::PTR_SIZE };
                        Type::Int(isize_int)
                    }
                    ConstructWidePointer(ptr_ty) => {
                        let Type::Ptr(thin_ptr_ty) = left else {
                            throw_ill_formed!("BinOp::ConstructWidePointer: invalid left type: not a pointer");
                        };
                        if thin_ptr_ty.meta_kind() != PointerMetaKind::None {
                            throw_ill_formed!("BinOp::ConstructWidePointer: invalid left type: not a thin pointer");
                        }

                        // A thin pointer can also be the target type, with unit metadata.
                        let meta_ty = ptr_ty.meta_kind().ty::<T>();
                        if right != meta_ty {
                            throw_ill_formed!("BinOp::ConstructWidePointer: invalid right type: not metadata of target");
                        }

                        Type::Ptr(ptr_ty)
                    }
                }
            }
        })
    }
}

impl PlaceExpr {
    fn check_wf<T: Target>(self, locals: Map<LocalName, Type>, prog: Program) -> Result<Type> {
        use PlaceExpr::*;
        ret(match self {
            Local(name) => {
                match locals.get(name) {
                    None => throw_ill_formed!("PlaceExpr::Local: unknown local name"),
                    Some(local) => local,
                }
            },
            Deref { operand, ty } => {
                ty.check_wf::<T>(prog)?;
                let op_ty = operand.check_wf::<T>(locals, prog)?;
                let Type::Ptr(op_ptr_ty) = op_ty else {
                    throw_ill_formed!("PlaceExpr::Deref: invalid operand type");
                };
                ensure_wf(op_ptr_ty.meta_kind() == ty.meta_kind(), "PlaceExpr::Deref: metadata kind of operand and type don't match")?;
                // No check of how the alignment changes here -- that is purely a runtime constraint.
                ty
            }
            Field { root, field } => {
                let root = root.check_wf::<T>(locals, prog)?;
                let field_ty = match root {
                    Type::Tuple { sized_fields, unsized_field, .. } => {
                        if field >= 0 && field < sized_fields.len() {
                            sized_fields[field].1
                        } else if field == sized_fields.len() {
                            let Some(unsized_ty) = unsized_field else {
                                throw_ill_formed!("PlaceExpr::Field: invalid field");
                            };
                            unsized_ty
                        } else {
                            throw_ill_formed!("PlaceExpr::Field: invalid field");
                        }
                    }
                    Type::Union { fields, .. } => {
                        match fields.get(field) {
                            None => throw_ill_formed!("PlaceExpr::Field: invalid field"),
                            Some(field) => field.1,
                        }
                    }
                    _ => throw_ill_formed!("PlaceExpr::Field: expression does not match type"),
                };
                field_ty
            }
            Index { root, index } => {
                let root = root.check_wf::<T>(locals, prog)?;
                let index = index.check_wf::<T>(locals, prog)?;
                ensure_wf(matches!(index, Type::Int(_)), "PlaceExpr::Index: invalid index type")?;
                match root {
                    Type::Array { elem, .. } | Type::Slice { elem } => elem,
                    _ => throw_ill_formed!("PlaceExpr::Index: expression type is not indexable"),
                }
            }
            Downcast { root, discriminant } => {
                let root = root.check_wf::<T>(locals, prog)?;
                match root {
                    // A valid downcast points to an existing variant.
                    Type::Enum { variants, .. } => {
                        let Some(variant) = variants.get(discriminant) else {
                            throw_ill_formed!("PlaceExpr::Downcast: invalid discriminant");
                        };
                        variant.ty
                    }
                    _ => throw_ill_formed!("PlaceExpr::Downcast: invalid root type"),
                }
            }
        })
    }
}

impl ArgumentExpr {
    fn check_wf<T: Target>(self, locals: Map<LocalName, Type>, prog: Program) -> Result<Type> {
        ret(match self {
            ArgumentExpr::ByValue(value) => value.check_wf::<T>(locals, prog)?,
            ArgumentExpr::InPlace(place) => place.check_wf::<T>(locals, prog)?
        })
    }
}
```

## Well-formed functions and programs

```rust
impl Statement {
    fn check_wf<T: Target>(
        self,
        func: Function,
        prog: Program,
    ) -> Result<()> {
        use Statement::*;
        match self {
            Assign { destination, source } => {
                let left = destination.check_wf::<T>(func.locals, prog)?;
                let right = source.check_wf::<T>(func.locals, prog)?;
                ensure_wf(left == right, "Statement::Assign: destination and source type differ")?;
                assert!(right.layout::<T>().is_sized(), "ValueExpr always return sized types");
            }
            PlaceMention(place) => {
                place.check_wf::<T>(func.locals, prog)?;
            }
            SetDiscriminant { destination, value } => {
                let Type::Enum { variants, .. } = destination.check_wf::<T>(func.locals, prog)? else {
                    throw_ill_formed!("Statement::SetDiscriminant: invalid type");
                };
                // We don't ensure that we can actually represent the discriminant.
                // The well-formedness checks for the type just ensure that every discriminant
                // reached by the discriminator is valid, however there we don't require that every
                // variant is represented. Setting such an unrepresented discriminant would probably
                // result in an invalid value as either the discriminator returns
                // `Discriminator::Invalid` or another variant.
                // This is fine as SetDiscriminant does not guarantee that the enum is a valid value.
                if variants.get(value) == None {
                    throw_ill_formed!("Statement::SetDiscriminant: invalid discriminant write")
                }
            }
            Validate { place, fn_entry: _ } => {
                let ty = place.check_wf::<T>(func.locals, prog)?;
                ensure_wf(ty.layout::<T>().is_sized(), "Statement::Validate: unsized place")?;
            }
            Deinit { place } => {
                let ty = place.check_wf::<T>(func.locals, prog)?;
                ensure_wf(ty.layout::<T>().is_sized(), "Statement::Deinit: unsized place")?;
            }
            StorageLive(local) => {
                ensure_wf(func.locals.contains_key(local), "Statement::StorageLive: invalid local variable")?;
            }
            StorageDead(local) => {
                ensure_wf(func.locals.contains_key(local), "Statement::StorageDead: invalid local variable")?;
                if local == func.ret || func.args.any(|arg_name| local == arg_name) {
                    throw_ill_formed!("Statement::StorageDead: trying to mark argument or return local as dead");
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
        _ => false
    }
}

impl Terminator {
    /// Check the terminator and the block transitions.
    /// `block_kind` is the kind of the block in which the terminator is used.
    fn check_wf<T: Target>(
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
                    // We only switch on integers.
                    // This is in contrast to Rust MIR where switch can work on `char`s and booleans as well.
                    // However since those are trivial casts we chose to only accept integers.
                    throw_ill_formed!("Terminator::Switch: switch is not Int")
                };

                // Ensure the switch cases are all valid.
                for (case, next_block) in cases.iter() {
                    ensure_wf(switch_ty.can_represent(case), "Terminator::Switch: value does not fit in switch type")?;
                    func.check_next_block(block_kind, next_block)?;
                }

                // Ensure the fallback is valid.
                func.check_next_block(block_kind, fallback)?;
            }
            Unreachable => {}
            Intrinsic { intrinsic, arguments, ret, next_block } => {
                // Return and argument expressions must all typecheck with some type.
                let ret_ty = ret.check_wf::<T>(func.locals, prog)?;
                ensure_wf(ret_ty.layout::<T>().is_sized(), "Terminator::Intrinsic: unsized return type")?;
                for arg in arguments {
                    let arg_ty = arg.check_wf::<T>(func.locals, prog)?;
                    ensure_wf(arg_ty.layout::<T>().is_sized(), "Terminator::Intrinsic: unsized argument type")?;
                }

                // Currently only AtomicFetchAndOp has special well-formedness requirements.
                match intrinsic {
                    IntrinsicOp::AtomicFetchAndOp(op) => {
                        if !is_atomic_binop(op) {
                            throw_ill_formed!("IntrinsicOp::AtomicFetchAndOp: non atomic op");
                        }
                    }
                    _ => {}
                }

                if let Some(next_block) = next_block {
                    func.check_next_block(block_kind, next_block)?;
                }
            }
            Call { callee, calling_convention: _, arguments, ret, next_block, unwind_block } => {
                let ty = callee.check_wf::<T>(func.locals, prog)?;
                ensure_wf(matches!(ty, Type::Ptr(PtrType::FnPtr)), "Terminator::Call: invalid type")?;

                // Return and argument expressions must all typecheck with some sized type.
                let ret_ty = ret.check_wf::<T>(func.locals, prog)?;
                ensure_wf(ret_ty.layout::<T>().is_sized(), "Terminator::Call: unsized return type")?;
                for arg in arguments {
                    let arg_ty = arg.check_wf::<T>(func.locals, prog)?;
                    ensure_wf(arg_ty.layout::<T>().is_sized(), "Terminator::Call: unsized argument type")?;
                }

                if let Some(next_block) = next_block {
                    func.check_next_block(block_kind, next_block)?;
                }

                if let Some(unwind_block) = unwind_block {
                    func.check_unwind_block(block_kind, unwind_block)?;
                }
            }
            Return => {
                ensure_wf(block_kind == BbKind::Regular, "Terminator::Return has to be called in a regular block")?;
            }
            StartUnwind { unwind_payload, unwind_block } => {
                let payload_type = unwind_payload.check_wf::<T>(func.locals, prog)?;
                ensure_wf(
                    payload_type == Type::Ptr(PtrType::Raw { meta_kind: PointerMetaKind::None }),
                    "Terminator::StartUnwind: the unwind payload should be a raw pointer",
                )?;
                
                ensure_wf(
                    block_kind == BbKind::Regular,
                    "Terminator::StartUnwind has to be called in a regular block",
                )?;
                func.check_unwind_block(block_kind, unwind_block)?;
            }
            StopUnwind(next_block) => {
                ensure_wf(block_kind == BbKind::Catch, "Terminator::StopUnwind has to be called in a catch block")?;
                func.check_next_block(BbKind::Regular, next_block)?;
            }
            ResumeUnwind => {
                ensure_wf(block_kind == BbKind::Cleanup, "Terminator::ResumeUnwind: has to be called in cleanup block")?;
            }
        }

        ret(())
    }
}

impl Function {
    fn check_wf<T: Target>(self, prog: Program) -> Result<()> {
        // Ensure all locals have a valid type.
        for ty in self.locals.values() {
            ensure_wf(ty.layout::<T>().is_sized(), "Function: unsized local variable")?;
            ty.check_wf::<T>(prog)?;
        }

        // Compute initially live locals: arguments and return values.
        // They must all exist and be distinct.
        let mut start_live: Set<LocalName> = Set::new();
        for arg in self.args {
            ensure_wf(self.locals.contains_key(arg), "Function: argument local does not exist")?;
            if start_live.try_insert(arg).is_err() {
                throw_ill_formed!("Function: two arguments refer to the same local");
            };
        }
        ensure_wf(self.locals.contains_key(self.ret), "Function: return local does not exist")?;
        if start_live.try_insert(self.ret).is_err() {
            throw_ill_formed!("Function: return local is also used for an argument");
        };

        // Check all basic blocks.
        for block in self.blocks.values() {
            for statement in block.statements {
                statement.check_wf::<T>(self, prog)?;
            }
            block.terminator.check_wf::<T>(block.kind, self, prog)?;
        }

        ret(())
    }

    /// Checks whether the next block exists and has the correct block kind.
    fn check_next_block(self, expected_block_kind: BbKind, next_block_name: BbName) -> Result<()> {
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
    fn check_unwind_block(self, current_block_kind: BbKind, unwind_block_name: BbName) -> Result<()> {
        let expected_block_kinds = match current_block_kind {
            BbKind::Regular => list![BbKind::Cleanup, BbKind::Catch],
            BbKind::Cleanup | BbKind::Terminate => list![BbKind::Terminate],
            BbKind::Catch => throw_ill_formed!("Terminator: unwinding is not allowed in a catch block"),
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
    // Checks whether the relocation is within bounds.
    fn check_wf(self, globals: Map<GlobalName, Global>) -> Result<()> {
        // The global we are pointing to needs to exist.
        let Some(global) = globals.get(self.name) else {
            throw_ill_formed!("Relocation: invalid global name");
        };
        let size = Size::from_bytes(global.bytes.len()).unwrap();

        // And the offset needs to be in-bounds of its size.
        ensure_wf(self.offset <= size, "Relocation: offset out-of-bounds")?;

        ret(())
    }
}

impl Program {
    fn check_wf<T: Target>(self) -> Result<()> {
        // Check vtables: All vtables for the same trait must have all trait methods defined.
        for (_name, vtable) in self.vtables {
            ensure_wf(vtable.size.bytes() % vtable.align.bytes() == 0, "Program: size stored in vtable not a multiple of alignment")?;
            UnsafeCellStrategy::check_cells(vtable.cells, vtable.size)?;
            let Some(trait_methods) = self.traits.get(vtable.trait_name) else {
                throw_ill_formed!("Program: vtable for unknown trait");
            };
            let methods = vtable.methods.keys().collect::<Set<_>>();
            ensure_wf(methods == trait_methods, "Program: vtable has not the right set of methods")?;
        }

        // Check all the functions.
        for function in self.functions.values() {
            function.check_wf::<T>(self)?;
        }

        // Ensure the start function exists, has the right ABI, takes no arguments, and returns a 1-ZST.
        let Some(start) = self.functions.get(self.start) else {
            throw_ill_formed!("Program: start function does not exist");
        };
        ensure_wf(start.calling_convention == CallingConvention::C, "Program: start function has invalid calling convention")?;
        let ret_layout = start.locals[start.ret].layout::<T>();
        ensure_wf(
            ret_layout == LayoutStrategy::Sized(Size::ZERO, Align::ONE),
            "Program: start function return local has invalid layout"
        )?;
        ensure_wf(start.args.is_empty(), "Program: start function has arguments")?;

        // Check globals.
        for (_name, global) in self.globals {
            let size = Size::from_bytes(global.bytes.len()).unwrap();
            for (offset, relocation) in global.relocations {
                // A relocation fills `PTR_SIZE` many bytes starting at the offset, those need to fit into the size.
                ensure_wf(offset + T::PTR_SIZE <= size, "Program: invalid global pointer value")?;

                relocation.check_wf(self.globals)?;
            }
        }

        ret(())
    }
}
```
