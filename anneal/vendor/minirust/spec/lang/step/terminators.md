
# Terminators

This defines the evaluation of terminators.
By far the most complex terminators are function calls and returns.

```rust
impl<M: Memory> Machine<M> {
    #[specr::argmatch(terminator)]
    fn eval_terminator(&mut self, terminator: Terminator) -> NdResult { .. }
}
```

## Goto

The simplest terminator: jump to the (beginning of the) given block.

```rust
impl<M: Memory> Machine<M> {
    fn jump_to_block(&mut self, block: BbName) -> NdResult {
        self.try_mutate_cur_frame(|frame, _mem| {
            frame.jump_to_block(block);
            ret(())
        })
    }

    fn eval_terminator(&mut self, Terminator::Goto(block_name): Terminator) -> NdResult {
        self.jump_to_block(block_name)?;
        ret(())
    }
}
```

## Switch

```rust
impl<M: Memory> Machine<M> {
    fn eval_terminator(&mut self, Terminator::Switch { value, cases, fallback }: Terminator) -> NdResult {
        let Value::Int(value) = self.eval_value(value)?.0 else {
            panic!("switch on a non-integer");
        };
        let next = cases.get(value).unwrap_or(fallback);
        self.jump_to_block(next)?;

        ret(())
    }
}
```

## Unreachable

```rust
impl<M: Memory> Machine<M> {
    fn eval_terminator(&mut self, Terminator::Unreachable: Terminator) -> NdResult {
        throw_ub!("reached unreachable code");
    }
}
```

## Call

A lot of things happen when a function is being called!
In particular, we have to ensure caller and callee use the same ABI, we have to evaluate the arguments, and we have to initialize a new stack frame.

```rust
/// Check whether the two types are compatible in function calls.
///
/// This means *at least* they have the same size and alignment (for on-stack argument passing).
/// However, when arguments get passed in registers, more details become relevant, so we require
/// almost full structural equality.
fn check_abi_compatibility(
    caller_ty: Type,
    callee_ty: Type,
) -> bool {
    // FIXME: we probably do not have enough details captured in `Type` to fully implement this.
    // For instance, what about SIMD vectors?
    // FIXME: we also reject too much here, e.g. we do not reflect `repr(transparent)`,
    // let alone `Option<&T>` being compatible with `*const T`.
    match (caller_ty, callee_ty) {
        (Type::Int(caller_ty), Type::Int(callee_ty)) =>
            // The sign *does* matter for some ABIs, so we compare it as well.
            caller_ty == callee_ty,
        (Type::Bool, Type::Bool) =>
            true,
        (Type::Ptr(caller_ty), Type::Ptr(callee_ty)) =>
            // The kind of pointer and pointee details do not matter for ABI,
            // however, the metadata kind does.
            caller_ty.meta_kind() == callee_ty.meta_kind(),
        (Type::Tuple { sized_fields: caller_fields, sized_head_layout: caller_head_layout, unsized_field: caller_unsized_field },
         Type::Tuple { sized_fields: callee_fields, sized_head_layout: callee_head_layout, unsized_field: callee_unsized_field }) => {
            let (caller_size, caller_align) = caller_head_layout.head_size_and_align();
            let (callee_size, callee_align) = callee_head_layout.head_size_and_align();
            assert!(caller_unsized_field.is_none(), "wf ensures all arugments are sized");
            assert!(callee_unsized_field.is_none(), "wf ensures all arugments are sized");
            caller_fields.len() == callee_fields.len() &&
            caller_fields.zip(callee_fields).all(|(caller_field, callee_field)|
                caller_field.0 == callee_field.0 && check_abi_compatibility(caller_field.1, callee_field.1)
            ) &&
            caller_size == callee_size &&
            caller_align == callee_align
        }
        (Type::Array { elem: caller_elem, count: caller_count },
         Type::Array { elem: callee_elem, count: callee_count }) =>
            check_abi_compatibility(caller_elem, callee_elem) && caller_count == callee_count,
        (Type::Union { fields: caller_fields, chunks: caller_chunks, size: caller_size, align: caller_align },
         Type::Union { fields: callee_fields, chunks: callee_chunks, size: callee_size, align: callee_align }) =>
            caller_fields.len() == callee_fields.len() &&
            caller_fields.zip(callee_fields).all(|(caller_field, callee_field)|
                caller_field.0 == callee_field.0 && check_abi_compatibility(caller_field.1, callee_field.1)
            ) &&
            caller_chunks == callee_chunks &&
            caller_size == callee_size &&
            caller_align == callee_align,
        (Type::Enum { variants: caller_variants, discriminator: caller_discriminator, discriminant_ty: caller_discriminant_ty, size: caller_size, align: caller_align },
         Type::Enum { variants: callee_variants, discriminator: callee_discriminator, discriminant_ty: callee_discriminant_ty, size: callee_size, align: callee_align }) =>
            caller_variants.len() == callee_variants.len() &&
            // Both sides must have the same discriminants. Checking only one direction
            // of the mutual inclusion is enough as we checked that they have the same number of key-value pairs.
            caller_variants.iter().all(|(caller_discriminant, caller_variant)| {
                let Some(callee_variant) = callee_variants.get(caller_discriminant) else {
                    return false;
                };
                check_abi_compatibility(caller_variant.ty, callee_variant.ty) &&
                caller_variant.tagger == callee_variant.tagger
            }) &&
            caller_discriminator == callee_discriminator &&
            caller_discriminant_ty == callee_discriminant_ty &&
            caller_size == callee_size &&
            caller_align == callee_align,
        // Different kind of type, definitely incompatible.
        _ =>
            false
    }
}

impl<M: Memory> Machine<M> {
    /// Prepare a place for being used in-place as a function argument or return value.
    fn prepare_for_inplace_passing(
        &mut self,
        place: Place<M>,
        ty: Type,
    ) -> NdResult {
        // Make the old value unobservable because the callee might work on it in-place.
        // This also checks that the memory is dereferenceable, and crucially ensures we are aligned
        // *at the given type* -- the callee does not care about packed field projections or things like that!
        self.mem.deinit(
            place.ptr.thin_pointer,
            ty.layout::<M::T>().expect_size("WF ensures arguments and return types are sized"),
            ty.layout::<M::T>().expect_align("WF ensures arguments and return types are sized")
        )?;
        // FIXME: This also needs aliasing model support.

        ret(())
    }

    /// A helper function to deal with `ArgumentExpr`.
    fn eval_argument(
        &mut self,
        val: ArgumentExpr,
    ) -> NdResult<(Value<M>, Type)> {
        ret(match val {
            ArgumentExpr::ByValue(value) => {
                self.eval_value(value)?
            }
            ArgumentExpr::InPlace(place) => {
                let (place, ty) = self.eval_place(place)?;
                // Fetch the actual value, WF ensures all Call arguments are sized.
                let value = self.place_load(place, ty)?;
                // Make sure we can use it in-place.
                self.prepare_for_inplace_passing(place, ty)?;

                (value, ty)
            }
        })
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

        // Allocate all the initially live locals.
        frame.storage_live(&mut self.mem, func.ret)?;
        for arg_local in func.args {
            frame.storage_live(&mut self.mem, arg_local)?;
        }

        // Check calling convention.
        if caller_conv != func.calling_convention {
            throw_ub!("call ABI violation: calling conventions are not the same");
        }

        // Check return place compatibility.
        if !check_abi_compatibility(caller_ret_ty, func.locals[func.ret]) {
            throw_ub!("call ABI violation: return types are not compatible");
        }

        // Pass arguments and check their compatibility.
        if func.args.len() != caller_args.len() {
            throw_ub!("call ABI violation: number of arguments does not agree");
        }
        for (callee_local, (caller_val, caller_ty)) in func.args.zip(caller_args) {
            // Make sure caller and callee view of this are compatible.
            if !check_abi_compatibility(caller_ty, func.locals[callee_local]) {
                throw_ub!("call ABI violation: argument types are not compatible");
            }
            // Copy the value at caller (source) type -- that's necessary since it is the type we did the load at (in `eval_argument`).
            // We know the types have compatible layout so this will fit into the allocation.
            // The local is freshly allocated so there should be no reason the store can fail.
            let align = caller_ty.layout::<M::T>().expect_align("WF ensures function arguments are sized");
            self.typed_store(frame.locals[callee_local], caller_val, caller_ty, align, Atomicity::None).unwrap();
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

        // Set up the stack frame.
        let stack_pop_action = StackPopAction::BackToCaller {
            next_block,
            unwind_block,
            ret_val_ptr: caller_ret_place.ptr.thin_pointer,
        };
        let frame = self.create_frame(
            callee,
            stack_pop_action,
            caller_conv,
            caller_ret_ty,
            arguments,
        )?;

        // Push new stack frame, so it is executed next.
        self.mutate_cur_stack(|stack| stack.push(frame));
        ret(())
    }

    fn eval_terminator(
        &mut self,
        Terminator::Call { callee, calling_convention: caller_conv, arguments, ret: ret_expr, next_block, unwind_block }: Terminator
    ) -> NdResult {
        // First evaluate the return place. (Left-to-right!)
        let (ret_place, ret_ty) = self.eval_place(ret_expr)?;
        // FIXME: should we care about `caller_ret_place.align`?
        // Make sure we can use it in-place.
        self.prepare_for_inplace_passing(ret_place, ret_ty)?;

        // Then evaluate the function that will be called.
        let (callee_val, _) = self.eval_value(callee)?;
        let callee = self.fn_from_ptr(callee_val)?;

        // Then evaluate the arguments.
        // FIXME: this means if an argument reads from `ret_expr`, the contents
        // of that have already been de-initialized. Is that the intended behavior?
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
}
```

Note that the content of the arguments is entirely controlled by the caller.
The callee should probably start with a bunch of `Validate` statements to ensure that all these arguments match the type the callee thinks they should have.

## Return

```rust
impl<M: Memory> Machine<M> {
    fn terminate_active_thread(&mut self) -> NdResult {
        let active = self.active_thread;
        // The main thread may not terminate, it must call the `Exit` intrinsic.
        if active == 0 {
            throw_ub!("the start function must not return");
        }

        self.threads.mutate_at(active, |thread| {
            assert!(thread.stack.len() == 0);
            thread.state = ThreadState::Terminated;
        });

        // All threads that waited to join this thread get synchronized by this termination
        // and enabled again.
        for i in ThreadId::ZERO..self.threads.len() {
            if self.threads[i].state == ThreadState::BlockedOnJoin(active) {
                self.synchronized_threads.insert(i);
                self.threads.mutate_at(i, |thread| thread.state = ThreadState::Enabled)
            }
        }

        ret(())
    }

    fn eval_terminator(&mut self, Terminator::Return: Terminator) -> NdResult {
        let mut frame = self.mutate_cur_stack(
            |stack| stack.pop().unwrap()
        );

        // Load the return value, which is a local and therefore ensured to be sized.
        // To match `Call`, and since the callee might have written to its return place using a totally different type,
        // we copy at the callee (source) type -- the one place where we ensure the return value matches that type.
        let callee_ty = frame.func.locals[frame.func.ret];
        let align = callee_ty.layout::<M::T>().expect_align("the return value is a local and thus sized");
        let ret_val = self.typed_load(frame.locals[frame.func.ret], callee_ty, align, Atomicity::None)?;

        // Deallocate everything.
        while let Some(local) = frame.locals.keys().next() {
            frame.storage_dead(&mut self.mem, local)?;
        }

        // Inform the memory model that this call has ended.
        self.mem.end_call(frame.extra)?;

        // Perform the stack pop action.
        match frame.stack_pop_action {
            StackPopAction::BottomOfStack => {
                // Only the bottom frame in a stack has no caller.
                // Therefore the thread must terminate now.
                self.terminate_active_thread()?;
            }
            StackPopAction::BackToCaller { ret_val_ptr: caller_ret_ptr, next_block, .. } => {
                // There must be a caller.
                assert!(self.active_thread().stack.len() > 0);
                // Store the return value where the caller wanted it.
                // Crucially, we are doing the store at the same type as the load above.
                self.typed_store(
                    caller_ret_ptr,
                    ret_val,
                    callee_ty,
                    align,
                    Atomicity::None,
                )?;

                // Jump to where the caller wants us to jump.
                if let Some(next_block) = next_block {
                    self.jump_to_block(next_block)?;
                } else {
                    throw_ub!("return from a function where caller did not specify next block");
                }
            }
        }
        ret(())
    }
}
```

Note that the caller has no guarantee at all about the value that it finds in its return place.
It should probably do a `Validate` as the next step to encode that it would be UB for the callee to return an invalid value.

## Starting unwinding

To initiate unwinding, we push the unwind payload to the payload stack and jump to a cleanup block.
This will then eventually invoke `ResumeUnwind` and thus propagate upwards through the stack.

```rust
impl<M: Memory> Machine<M> {
    fn eval_terminator(&mut self, Terminator::StartUnwind { unwind_payload, unwind_block }: Terminator) -> NdResult {
        let (Value::Ptr(unwind_payload), Type::Ptr(PtrType::Raw { meta_kind: PointerMetaKind::None })) =
            self.eval_value(unwind_payload)?
        else {
            panic!("StartUnwind: the unwind payload is not a raw pointer");
        };
        self.mutate_active_thread(|thread| {
            thread.unwind_payloads.push(unwind_payload.thin_pointer)
        });
        self.jump_to_block(unwind_block)?;
        ret(())
    }
}
```

## Stop unwinding

This terminator stops unwinding and jumps to a regular block. `StopUnwind` may only be used in a catch block.

```rust
impl<M: Memory> Machine<M> {
    fn eval_terminator(&mut self, Terminator::StopUnwind(block_name): Terminator) -> NdResult {
        self.mutate_active_thread(|thread| -> Result<()>{
            let Some(_) = thread.unwind_payloads.pop() else {
                throw_ub!("StopUnwind: the payload stack is empty");
            };
            ret(())
        } )?;
        self.jump_to_block(block_name)?;
        ret(())
    }
}
```

## Resuming unwinding in the caller

```rust
impl<M: Memory> Machine<M> {
    fn eval_terminator(&mut self, Terminator::ResumeUnwind: Terminator) -> NdResult {
        let mut frame = self.mutate_cur_stack(
            |stack| stack.pop().unwrap()
        );

        // Deallocate everything.
        while let Some(local) = frame.locals.keys().next() {
            frame.storage_dead(&mut self.mem, local)?;
        }

        // Inform the memory model that this call has ended.
        self.mem.end_call(frame.extra)?;

        // Perform the stack pop action.
        match frame.stack_pop_action {
            StackPopAction::BottomOfStack => {
                // Only the bottom frame in a stack has no caller.
                // It is UB to unwind out of the bottom of the stack.
                throw_ub!("the function at the bottom of the stack must not unwind");
            }
            StackPopAction::BackToCaller { unwind_block, .. } => {
                // Jump to the unwind block specified by the caller. Raise UB if `unwind_block` is `None`.
                if let Some(unwind_block) = unwind_block {
                    self.jump_to_block(unwind_block)?;
                } else {
                    throw_ub!("unwinding from a function where the caller did not specify an unwind_block");
                }
            }
        }
        ret(())
    }
}
```

## Intrinsic calls

```rust
impl<M: Memory> Machine<M> {
    fn eval_terminator(
        &mut self,
        Terminator::Intrinsic { intrinsic, arguments, ret: ret_expr, next_block }: Terminator
    ) -> NdResult {
        // First evaluate return place (left-to-right evaluation).
        let (ret_place, ret_ty) = self.eval_place(ret_expr)?;

        // Evaluate all arguments.
        let arguments = arguments.try_map(|arg| self.eval_value(arg))?;

        // Run the actual intrinsic.
        let value = self.eval_intrinsic(intrinsic, arguments, ret_ty)?;

        // Store return value.
        // `eval_intrinsic` above must guarantee that `value` has the right type.
        self.place_store(ret_place, value, ret_ty)?;

        // Jump to next block.
        if let Some(next_block) = next_block {
            self.jump_to_block(next_block)?;
        } else {
            throw_ub!("return from an intrinsic where caller did not specify next block");
        }

        ret(())
    }
}
```
