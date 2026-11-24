# Operators

Here we define the evaluation of unary and binary operators.

## Unary operators

```rust
impl<M: Memory> Machine<M> {
    #[specr::argmatch(operator)]
    fn eval_un_op(&self, operator: UnOp, (operand, op_ty): (Value<M>, Type)) -> Result<(Value<M>, Type)> { .. }
}
```

### Integer operations

```rust
impl<M: Memory> Machine<M> {
    /// Perform the operation on the mathematical integer `operand`,
    /// but correcting for non-pure effects dependent of the `operand_ty`.
    fn eval_int_un_op(op: IntUnOp, operand: Int, operand_ty: IntType) -> Result<Int> {
        use IntUnOp::*;
        ret(match op {
            // Put the result into the right range (in case of overflow).
            Neg => operand_ty.bring_in_bounds(-operand),
            // Put the result into the right range (in case of a unsigned numbers, which `!`
            // makes negative by inverting all the leading zeros).
            BitNot => operand_ty.bring_in_bounds(!operand),
            // This can never overflow, as the total number of bits is below `u32::MAX`.
            CountOnes => Self::eval_count_ones(operand, operand_ty),
        })
    }
    fn eval_un_op(&self, UnOp::Int(op): UnOp, (operand, op_ty): (Value<M>, Type)) -> Result<(Value<M>, Type)> {
        let Type::Int(int_ty) = op_ty else { panic!("non-integer input to integer operation") };
        let Value::Int(operand) = operand else { panic!("non-integer input to integer operation") };

        let ret_ty = match op {
            IntUnOp::CountOnes => IntType { signed: Unsigned, size: Size::from_bytes(4).unwrap() },
            _ => int_ty,
        };

        let result = Value::Int(Self::eval_int_un_op(op, operand, int_ty)?);

        // Sanity-check that the result of `eval_int_un_op` is in-bounds.
        self.check_value(result, Type::Int(ret_ty))
            .expect("sanity check: result of UnOp::Int does not fit in the return type");
        ret((result, Type::Int(ret_ty)))
    }
}
```

`CountOnes` aka `ctpop` is a Rust intrinsic on integer types that always returns a `u32`.
This is not a pure function on mathematical integers,
since the bit representation for non-negative values has infinite zeros,
and infinite ones for negatives values.
Therefore, the bit width is important, and iterating until `remaining_bits = 0` is not correct.

```rust
impl<M: Memory> Machine<M> {
    fn eval_count_ones(operand: Int, int_ty: IntType) -> Int {
        let mut ones = Int::ZERO;
        let mut remaining_bits = operand;
        // Iterate once per bit in the bit width, afterwards the remaining bits are leading bits only.
        for _ in Int::ZERO..int_ty.size.bits() {
            // Extract the least significant bit and update `remaining_bits` to remove that bit.
            ones += remaining_bits & Int::ONE;
            remaining_bits >>= 1;
        }
        ones
    }
}
```

### Casts

```rust
impl<M: Memory> Machine<M> {
    fn eval_cast_op(&self, cast_op: CastOp, (operand, old_ty): (Value<M>, Type)) -> Result<(Value<M>, Type)> {
        use CastOp::*;
        match cast_op {
            IntToInt(int_ty) => {
                let Value::Int(operand) = operand else { panic!("non-integer input to int-to-int cast") };
                let result = int_ty.bring_in_bounds(operand);
                ret((Value::Int(result), Type::Int(int_ty)))
            }
            Transmute(new_ty) => {
                if old_ty.layout::<M::T>().expect_size("WF ensures transmutes are sized")
                    != new_ty.layout::<M::T>().expect_size("WF ensures transmutes are sized")
                {
                    throw_ub!("transmute between types of different size")
                }
                let val = self.transmute(operand, old_ty, new_ty)?;
                ret((val, new_ty))
            }
        }
    }
    fn eval_un_op(&self, UnOp::Cast(cast_op): UnOp, (operand, op_ty): (Value<M>, Type)) -> Result<(Value<M>, Type)> {
        ret(self.eval_cast_op(cast_op, (operand, op_ty))?)
    }
}
```

### Wide pointer operators

```rust
impl<M: Memory> Machine<M> {
    fn eval_un_op(&self, UnOp::GetThinPointer: UnOp, (operand, op_ty): (Value<M>, Type)) -> Result<(Value<M>, Type)> {
        let Value::Ptr(ptr) = operand else { panic!("non-pointer GetThinPointer") };

        let thin_ptr = Pointer { metadata: None, ..ptr };
        let thin_ptr_ty = PtrType::Raw { meta_kind: PointerMetaKind::None };
        ret((Value::Ptr(thin_ptr), Type::Ptr(thin_ptr_ty)))
    }
    
    fn eval_un_op(&self, UnOp::GetMetadata: UnOp, (operand, op_ty): (Value<M>, Type)) -> Result<(Value<M>, Type)> {
        let Value::Ptr(ptr) = operand else { panic!("non-pointer GetMetadata") };
        let Type::Ptr(ptr_ty) = op_ty else { panic!("non-pointer GetMetadata") };

        let meta_value = ptr_ty.meta_kind().encode_as_value::<M>(ptr.metadata);
        let meta_ty = ptr_ty.meta_kind().ty::<M::T>();
        // O(1) sanity check
        self.check_value(meta_value, meta_ty).expect("GetMetadata: sanity check, returned meta is well-formed");
        ret((meta_value, meta_ty))
    }
}
```

### Computing the Size and Alignment

```rust
impl<M: Memory> Machine<M> {
    fn eval_un_op(&self, UnOp::ComputeSize(ty): UnOp, (operand, op_ty): (Value<M>, Type)) -> Result<(Value<M>, Type)> {
        let meta = ty.meta_kind().decode_value::<M>(operand);
        let size = self.compute_size(ty.layout::<M::T>(), meta);
        ret((Value::Int(size.bytes()), Type::Int(IntType::usize_ty::<M::T>())))
    }

    fn eval_un_op(&self, UnOp::ComputeAlign(ty): UnOp, (operand, op_ty): (Value<M>, Type)) -> Result<(Value<M>, Type)> {
        let meta = ty.meta_kind().decode_value::<M>(operand);
        let align = self.compute_align(ty.layout::<M::T>(), meta);
        ret((Value::Int(align.bytes()), Type::Int(IntType::usize_ty::<M::T>())))
    }
}
```

### VTable Lookups

Dynamic dispatch in MiniRust is represented as a `Call` to the result of an explicit `VTableMethodLookup` expression.
This expression works on vtable pointers, which can be extracted by `GetMetadata`.
Which method is invoked is represented by the `method` parameter, which corresponds to a function of the trait.

```rust
impl<M: Memory> Machine<M> {
    fn eval_un_op(&self, UnOp::VTableMethodLookup(method): UnOp, (operand, op_ty): (Value<M>, Type)) -> Result<(Value<M>, Type)> {
        let (Value::Ptr(ptr), Type::Ptr(_ptr_ty)) = (operand, op_ty) else {
            panic!("vtable lookup on non-pointer");
        };
        // It is checked in check_value that the vtable is always valid.
        let vtable = self.vtable_lookup()(ptr.thin_pointer);
        // Well-formedness of values ensures `ptr` points to a vtable of the right trait,
        // and hence the method exists.
        let fn_name = vtable.methods[method];
        let fn_ptr = Value::Ptr(self.fn_ptrs[fn_name].widen(None));
        ret((fn_ptr, Type::Ptr(PtrType::FnPtr)))
    }
}
```

## Binary operators

```rust
impl<M: Memory> Machine<M> {
    #[specr::argmatch(operator)]
    fn eval_bin_op(
        &self,
        operator: BinOp,
        (left, l_ty):
        (Value<M>, Type),
        (right, _r_ty): (Value<M>, Type)
    ) -> Result<(Value<M>, Type)> { .. }
}
```

### Integer operations

```rust
impl<M: Memory> Machine<M> {
    fn eval_int_bin_op(op: IntBinOp, left: Int, right: Int, left_ty: IntType) -> Result<Int> {
        use IntBinOp::*;
        ret(match op {
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
                if !left_ty.can_represent(result) { // `int::MIN / -1` is UB
                    throw_ub!("overflow in division");
                }
                result
            }
            DivExact => {
                if right == 0 {
                    throw_ub!("division by zero");
                }
                let result = left / right;
                if !left_ty.can_represent(result) { // `int::MIN / -1` is UB
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
                if !left_ty.can_represent(left / right) { // `int::MIN % -1` is UB
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
        })
    }
    fn eval_bin_op(
        &self,
        BinOp::Int(op): BinOp,
        (left, l_ty): (Value<M>, Type),
        (right, _r_ty): (Value<M>, Type)
    ) -> Result<(Value<M>, Type)> {
        let Type::Int(int_ty) = l_ty else { panic!("non-integer input to integer operation") };
        let Value::Int(left) = left else { panic!("non-integer input to integer operation") };
        let Value::Int(right) = right else { panic!("non-integer input to integer operation") };

        // Perform the operation.
        let result = Self::eval_int_bin_op(op, left, right, int_ty)?;
        // Put the result into the right range (in case of overflow).
        let result = int_ty.bring_in_bounds(result);
        ret((Value::Int(result), Type::Int(int_ty)))
    }

    fn eval_bin_op(
        &self,
        BinOp::IntWithOverflow(op): BinOp,
        (left, l_ty): (Value<M>, Type),
        (right, _r_ty): (Value<M>, Type)
    ) -> Result<(Value<M>, Type)> {
        let Type::Int(int_ty) = l_ty else { panic!("non-integer input to integer operation") };
        let Value::Int(left) = left else { panic!("non-integer input to integer operation") };
        let Value::Int(right) = right else { panic!("non-integer input to integer operation") };

        // Perform the operation.
        let result = match op {
            IntBinOpWithOverflow::Add => left + right,
            IntBinOpWithOverflow::Sub => left - right,
            IntBinOpWithOverflow::Mul => left * right,
        };
        let overflow = !int_ty.can_represent(result);
        // Put the result into the right range (in case of overflow).
        let result = int_ty.bring_in_bounds(result);
        // Pack result and overflow bool into tuple.
        let value = Value::Tuple(list![Value::Int::<M>(result), Value::Bool::<M>(overflow)]);
        let ty = int_ty.with_overflow::<M::T>();
        ret((value, ty))
    }
}
```

### Relational operators

```rust
impl<M: Memory> Machine<M> {
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
    fn compare_ptr(left: Pointer<M::Provenance>, right: Pointer<M::Provenance>) -> std::cmp::Ordering {
        let thin_cmp = left.thin_pointer.addr.cmp(&right.thin_pointer.addr);
        let meta_cmp = match (left.metadata, right.metadata) {
            (None, None) => std::cmp::Ordering::Equal,
            (Some(PointerMeta::ElementCount(l)), Some(PointerMeta::ElementCount(r))) => l.cmp(&r),
            (Some(PointerMeta::VTablePointer(l)), Some(PointerMeta::VTablePointer(r))) => l.addr.cmp(&r.addr),
            _ => panic!("unmatching metadata in wide pointer comparasion"),
        };
        // Lexicographically compare on first the thin pointer and then the metadata
        thin_cmp.then(meta_cmp)
    }

    fn eval_bin_op(
        &self,
        BinOp::Rel(rel_op): BinOp,
        (left, l_ty): (Value<M>, Type),
        (right, _r_ty): (Value<M>, Type)
    ) -> Result<(Value<M>, Type)> {
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
            _ => panic!("relational operator on incomparable type or value-type mismatch"),
        };

        ret(Self::eval_rel_op(rel_op, ord))
    }
}
```

### Pointer arithmetic

```rust
impl<M: Memory> Machine<M> {
    /// Perform a wrapping offset on the given pointer. (Can never fail.)
    fn ptr_offset_wrapping(&self, ptr: ThinPointer<M::Provenance>, offset: Int) -> ThinPointer<M::Provenance> {
        ptr.wrapping_offset::<M::T>(offset)
    }

    /// Perform in-bounds arithmetic on the given pointer. This must not wrap,
    /// and the offset must stay in bounds of a single allocation.
    fn ptr_offset_inbounds(&self, ptr: ThinPointer<M::Provenance>, offset: Int) -> Result<ThinPointer<M::Provenance>> {
        // Ensure dereferenceability.
        self.mem.signed_dereferenceable(ptr, offset)?;
        // This also ensures that `offset` fits in an `isize`, since no allocation
        // can be bigger than `isize`, and it ensures that the arithmetic does not overflow, since no
        // allocation wraps around the edge of the address space.
        assert!(offset.in_bounds(Signed, M::T::PTR_SIZE));
        assert!((ptr.addr + offset).in_bounds(Unsigned, M::T::PTR_SIZE));
        // All checked!
        ret(ThinPointer { addr: ptr.addr + offset, ..ptr })
    }

    fn eval_bin_op(
        &self,
        BinOp::PtrOffset { inbounds }: BinOp,
        (left, l_ty): (Value<M>, Type),
        (right, _r_ty): (Value<M>, Type)
    ) -> Result<(Value<M>, Type)> {
        let Value::Ptr(Pointer { thin_pointer: left, metadata: None }) = left else {
            panic!("non-thin-pointer left input to `PtrOffset`")
        };
        let Value::Int(right) = right else { panic!("non-integer right input to `PtrOffset`") };

        let offset_ptr = if inbounds {
            self.ptr_offset_inbounds(left, right)?
        } else {
            self.ptr_offset_wrapping(left, right)
        };
        ret((Value::Ptr(offset_ptr.widen(None)), l_ty))
    }

    fn eval_bin_op(
        &self,
        BinOp::PtrOffsetFrom { inbounds, nonneg }: BinOp,
        (left, l_ty): (Value<M>, Type),
        (right, _r_ty): (Value<M>, Type)
    ) -> Result<(Value<M>, Type)> {
        let Value::Ptr(Pointer { thin_pointer: left, metadata: None }) = left else {
            panic!("non-thin-pointer left input to `PtrOffsetFrom`")
        };
        let Value::Ptr(Pointer { thin_pointer: right, metadata: None }) = right else {
            panic!("non-thin-pointer right input to `PtrOffsetFrom`")
        };

        let distance = left.addr - right.addr;
        let distance = if inbounds {
            // The "gap" between the two pointers must be dereferenceable from both of them.
            // This check also ensures that the distance is inbounds of `isize`.
            self.mem.signed_dereferenceable(left, -distance)?;
            self.mem.signed_dereferenceable(right, distance)?;
            // All checked!
            distance
        } else {
            distance.bring_in_bounds(Signed, M::T::PTR_SIZE)
        };

        if nonneg && distance < Int::ZERO {
            throw_ub!("PtrOffsetFrom: negative result with `nonneg` flag set");
        }

        let isize_int = IntType { signed: Signed, size: M::T::PTR_SIZE };
        ret((Value::Int(distance), Type::Int(isize_int)))
    }
}
```

### Wide pointer construction

```rust
impl<M: Memory> Machine<M> {
    fn eval_bin_op(
        &self,
        BinOp::ConstructWidePointer(ptr_ty): BinOp,
        (left, l_ty): (Value<M>, Type),
        (right, _r_ty): (Value<M>, Type)
    ) -> Result<(Value<M>, Type)> {
        let Value::Ptr(Pointer { thin_pointer, metadata: None }) = left else {
            panic!("non-thin-pointer left input to `ConstructWidePointer`")
        };
        let metadata = ptr_ty.meta_kind().decode_value::<M>(right);
        let wide_ptr = Value::Ptr(Pointer { thin_pointer, metadata });

        // check that the decoded pointer is well-formed. Includes size and vtable checks.
        self.check_value(wide_ptr, Type::Ptr(ptr_ty))?;
        ret((wide_ptr, Type::Ptr(ptr_ty)))
    }
}
```
