# Intrinsics

This file defines the generic machine intrinsics.

```rust
impl<M: Memory> Machine<M> {
    #[specr::argmatch(intrinsic)]
    fn eval_intrinsic(
        &mut self,
        intrinsic: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> { .. }
}
```

These helper functions simplify unit-returning intrinsics.

```rust
fn unit_value<M: Memory>() -> Value<M> {
    Value::Tuple(list![])
}

fn unit_type() -> Type {
    Type::Tuple { sized_fields: list![], sized_head_layout: TupleHeadLayout {
        end: Size::ZERO, align: Align::ONE, packed_align: None,
    }, unsized_field: None }
}
```

## Pointer provenance management

See [this blog post](https://www.ralfj.de/blog/2022/04/11/provenance-exposed.html) for why this is needed.

```rust
impl<M: Memory> Machine<M> {
    fn eval_intrinsic(&mut self,
        IntrinsicOp::PointerExposeProvenance: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if arguments.len() != 1 {
            throw_ub!("invalid number of arguments for `PointerExposeProvenance` intrinsic");
        }
        let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = arguments[0].0 else {
            throw_ub!("invalid argument for `PointerExposeProvenance` intrinsic: not a thin pointer");
        };
        if ret_ty != Type::Int(IntType { signed: Unsigned, size: M::T::PTR_SIZE }) {
            throw_ub!("invalid return type for `PointerExposeProvenance` intrinsic")
        }

        self.intptrcast.expose(ptr);
        ret(Value::Int(ptr.addr))
    }

    fn eval_intrinsic(&mut self,
        IntrinsicOp::PointerWithExposedProvenance: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if arguments.len() != 1 {
            throw_ub!("invalid number of arguments for `PointerWithExposedProvenance` intrinsic");
        }
        let Value::Int(addr) = arguments[0].0 else {
            throw_ub!("invalid argument for `PointerWithExposedProvenance` intrinsic: not an integer");
        };
        let Type::Ptr(ret_ptr_ty) = ret_ty else {
            throw_ub!("invalid return type for `PointerWithExposedProvenance` intrinsic");
        };
        if ret_ptr_ty.meta_kind() != PointerMetaKind::None {
            throw_ub!("unsized pointee requested for `PointerWithExposedProvenance` intrinsic");
        }

        let ptr = self.intptrcast.int2ptr(addr)?;
        ret(Value::Ptr(ptr.widen(None)))
    }
}
```

## Machine primitives

We start with the `Exit` intrinsic.

```rust
impl<M: Memory> Machine<M> {
    fn exit(&self) -> NdResult<!> {
        // Check for memory leaks.
        self.mem.leak_check()?;
        // No leak found -- good, stop the machine.
        throw_machine_stop!();
    }

    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::Exit: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        self.exit()?
    }
}
```

`Abort` stopts the machine immediately.

```rust
impl<M: Memory> Machine<M> {
    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::Abort: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        throw_abort!();
    }
}
```

## UB control

```rust
impl<M: Memory> Machine<M> {
    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::Assume: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if arguments.len() != 1 {
            throw_ub!("invalid number of arguments for `Assume` intrinsic");
        }
        let Value::Bool(b) = arguments[0].0 else {
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
}
```

## Input and output

These are the `PrintStdout` and `PrintStderr` intrinsics.

```rust
impl<M: Memory> Machine<M> {
    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::PrintStdout: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if ret_ty != unit_type() {
            throw_ub!("invalid return type for `PrintStdout` intrinsic")
        }

        self.eval_print(self.stdout, arguments)?;

        ret(unit_value())
    }

    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::PrintStderr: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if ret_ty != unit_type() {
            throw_ub!("invalid return type for `PrintStderr` intrinsic")
        }

        self.eval_print(self.stderr, arguments)?;

        ret(unit_value())
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
}
```

## Heap memory management

These intrinsics can be used for dynamic memory allocation and deallocation.

```rust
impl<M: Memory> Machine<M> {
    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::Allocate: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if arguments.len() != 2 {
            throw_ub!("invalid number of arguments for `Allocate` intrinsic");
        }

        let Value::Int(size) = arguments[0].0 else {
            throw_ub!("invalid first argument to `Allocate` intrinsic: not an integer");
        };
        let Some(size) = Size::from_bytes(size) else {
            throw_ub!("invalid size for `Allocate` intrinsic: negative size");
        };

        let Value::Int(align) = arguments[1].0 else {
            throw_ub!("invalid second argument to `Allocate` intrinsic: not an integer");
        };
        let Some(align) = Align::from_bytes(align) else {
            throw_ub!("invalid alignment for `Allocate` intrinsic: not a power of 2");
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

    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::Deallocate: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if arguments.len() != 3 {
            throw_ub!("invalid number of arguments for `Deallocate` intrinsic");
        }

        let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = arguments[0].0 else {
            throw_ub!("invalid first argument to `Deallocate` intrinsic: not a thin pointer");
        };

        let Value::Int(size) = arguments[1].0 else {
            throw_ub!("invalid second argument to `Deallocate` intrinsic: not an integer");
        };
        let Some(size) = Size::from_bytes(size) else {
            throw_ub!("invalid size for `Deallocate` intrinsic: negative size");
        };

        let Value::Int(align) = arguments[2].0 else {
            throw_ub!("invalid third argument to `Deallocate` intrinsic: not an integer");
        };
        let Some(align) = Align::from_bytes(align) else {
            throw_ub!("invalid alignment for `Deallocate` intrinsic: not a power of 2");
        };

        if ret_ty != unit_type() {
            throw_ub!("invalid return type for `Deallocate` intrinsic")
        }

        self.mem.deallocate(ptr, AllocationKind::Heap, size, align)?;

        ret(unit_value())
    }
}
```

## Threads

These intrinsics let the program spawn and join threads.

```rust
impl<M: Memory> Machine<M> {
    fn spawn(&mut self, func: Function, data_pointer: Value<M>, data_ptr_ty: Type) -> NdResult<ThreadId> {
        // Create the thread.
        let args = list![(data_pointer, data_ptr_ty)];
        let thread_id = self.new_thread(func, args)?;

        // This thread got synchronized because its existence startet with this.
        self.synchronized_threads.insert(thread_id);

        ret(thread_id)
    }

    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::Spawn: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if arguments.len() != 2 {
            throw_ub!("invalid number of arguments for `Spawn` intrinsic");
        }

        let fn_ptr = arguments[0].0;
        let func = self.fn_from_ptr(fn_ptr)?;

        let (data_ptr, data_ptr_ty) = arguments[1];
        if !matches!(data_ptr_ty, Type::Ptr(_)) {
            throw_ub!("invalid second argument to `Spawn` intrinsic: not a pointer");
        }

        if !matches!(ret_ty, Type::Int(_)) {
            throw_ub!("invalid return type for `Spawn` intrinsic")
        }

        let thread_id = self.spawn(func, data_ptr, data_ptr_ty)?;
        ret(Value::Int(thread_id))
    }

    fn join(&mut self, thread_id: ThreadId) -> NdResult {
        let Some(thread) = self.threads.get(thread_id) else {
            throw_ub!("`Join` intrinsic: join non existing thread");
        };

        match thread.state {
            ThreadState::Terminated => {},
            _ => {
                self.threads.mutate_at(self.active_thread, |thread|{
                    thread.state = ThreadState::BlockedOnJoin(thread_id);
                });
            },
        };

        ret(())
    }

    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::Join: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if arguments.len() != 1 {
            throw_ub!("invalid number of arguments for `Join` intrinsic");
        }

        let Value::Int(thread_id) = arguments[0].0 else {
            throw_ub!("invalid first argument to `Join` intrinsic: not an integer");
        };

        if ret_ty != unit_type() {
            throw_ub!("invalid return type for `Join` intrinsic")
        }

        self.join(thread_id)?;
        ret(unit_value())
    }
}
```
## Raw equality
```rust
impl<M: Memory> Machine<M> {
    fn load_raw_data(&mut self, ptr : Pointer<<M as Memory>::Provenance>, ptr_ty : PtrType) -> Result<List<u8>> {
        // We need the pointee layout to determine how many bytes to load.
        let PtrType::Ref { pointee, .. } = ptr_ty else {
            throw_ub!("invalid argument to `RawEq` intrinsic: not a reference");
        };
        let PointeeInfo { layout: LayoutStrategy::Sized(size, align), .. } = pointee else {
            throw_ub!("invalid argument to `RawEq` intrinsic: unsized pointee");
        };
        let bytes = self.mem.load(ptr.thin_pointer, size, align, Atomicity::None)?;

        let Some(data) =  bytes.try_map(|byte| byte.data()) else {
            throw_ub!("invalid argument to `RawEq` intrinsic: byte is uninitialized");
        };

        Ok(data)
    }

    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::RawEq: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if arguments.len() != 2 {
            throw_ub!("invalid number of arguments for `RawEq` intrinsic");
        }
        if ret_ty != Type::Bool {
            throw_ub!("invalid return type for `RawEq` intrinsic")
        }

        let (left, l_ty) = (arguments).index_at(0);
        let (right, r_ty) = (arguments).index_at(1);

        if l_ty != r_ty {
            throw_ub!("invalid arguments to `RawEq` intrinsic: types of arguments are not identical");
        }

        let Value::Ptr(left) = left else {
            throw_ub!("invalid first argument to `RawEq` intrinsic: not a pointer");
        };

        let Value::Ptr(right) = right else {
            throw_ub!("invalid second argument to `RawEq` intrinsic: not a pointer");
        };

        let Type::Ptr(l_ty) = l_ty else {
            throw_ub!("invalid argument type to `RawEq` intrinsic: not a pointer");
        };

        let left_data = self.load_raw_data(left, l_ty)?;
        let right_data = self.load_raw_data(right, l_ty)?;

        ret(Value::Bool(left_data == right_data))
    }
}
```

## Atomic accesses

These intrinsics provide atomic accesses.

```rust
impl<M: Memory> Machine<M> {
    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::AtomicStore: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if arguments.len() != 2 {
            throw_ub!("invalid number of arguments for `AtomicStore` intrinsic");
        }

        let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = arguments[0].0 else {
            throw_ub!("invalid first argument to `AtomicStore` intrinsic: not a thin pointer");
        };

        let (val, ty) = arguments[1];
        let LayoutStrategy::Sized(size, _) = ty.layout::<M::T>() else {
            throw_ub!("invalid second argument to `AtomicStore` intrinsic: unsized type");
        };
        let Some(align) = Align::from_bytes(size.bytes()) else {
            throw_ub!("invalid second argument to `AtomicStore` intrinsic: size not power of two");
        };
        if size > M::T::MAX_ATOMIC_SIZE {
            throw_ub!("invalid second argument to `AtomicStore` intrinsic: size too big");
        }

        if ret_ty != unit_type() {
            throw_ub!("invalid return type for `AtomicStore` intrinsic")
        }

        self.typed_store(ptr, val, ty, align, Atomicity::Atomic)?;
        ret(unit_value())
    }

    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::AtomicLoad: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if arguments.len() != 1 {
            throw_ub!("invalid number of arguments for `AtomicLoad` intrinsic");
        }
    
        let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = arguments[0].0 else {
            throw_ub!("invalid first argument to `AtomicLoad` intrinsic: not a thin pointer");
        };

        let size = ret_ty.layout::<M::T>().expect_size("WF ensures intrinsic return types are sized");
        let Some(align) = Align::from_bytes(size.bytes()) else {
            throw_ub!("invalid return type for `AtomicLoad` intrinsic: size not power of two");
        };
        if size > M::T::MAX_ATOMIC_SIZE {
            throw_ub!("invalid return type for `AtomicLoad` intrinsic: size too big");
        }

        // `ret_ty` is ensured to be sized above.
        let val = self.typed_load(ptr, ret_ty, align, Atomicity::Atomic)?;
        ret(val)
    }

    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::AtomicCompareExchange: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if arguments.len() != 3 {
            throw_ub!("invalid number of arguments for `AtomicCompareExchange` intrinsic");
        }

        let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = arguments[0].0 else {
            throw_ub!("invalid first argument to `AtomicCompareExchange` intrinsic: not a thin pointer");
        };

        let (current, curr_ty) = arguments[1];
        if curr_ty != ret_ty {
            throw_ub!("invalid second argument to `AtomicCompareExchange` intrinsic: not same type as return value");
        }

        let (next, next_ty) = arguments[2];
        if next_ty != ret_ty {
            throw_ub!("invalid third argument to `AtomicCompareExchange` intrinsic: not same type as return value");
        }

        if !matches!(ret_ty, Type::Int(_)) {
            throw_ub!("invalid return type for `Intrinis::AtomicCompareExchange`: only works with integers");
        }

        // All integers are sized with a power of two size.
        let size = ret_ty.layout::<M::T>().expect_size("`ret_ty` is an integer");
        let align = Align::from_bytes(size.bytes()).unwrap();
        if size > M::T::MAX_ATOMIC_SIZE {
            throw_ub!("invalid return type for `AtomicCompareExchange` intrinsic: size too big");
        }

        // The value at the location right now.
        let before = self.typed_load(ptr, ret_ty, align, Atomicity::Atomic)?;

        // This is the central part of the operation. If the expected before value at ptr is the current value,
        // then we exchange it for the next value.
        // FIXME: The memory model might have to know that this is a compare-exchange.
        if current == before {
            self.typed_store(ptr, next, ret_ty, align, Atomicity::Atomic)?;
        } else {
            // We do *not* do a store on a failing AtomicCompareExchange. This means that races between
            // a non-atomic load and a failing AtomicCompareExchange are not considered UB!
        }

        ret(before)
    }

    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::AtomicFetchAndOp(op): IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if arguments.len() != 2 {
            throw_ub!("invalid number of arguments for `AtomicFetchAndOp` intrinsic");
        }

        let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = arguments[0].0 else {
            throw_ub!("invalid first argument to `AtomicFetchAndOp` intrinsic: not a thin pointer");
        };

        let (other, other_ty) = arguments[1];
        if other_ty != ret_ty {
            throw_ub!("invalid second argument to `AtomicFetchAndOp` intrinsic: not same type as return value");
        }

        let Type::Int(int_ty) = ret_ty else {
            throw_ub!("invalid return type for `AtomicFetchAndOp` intrinsic: only works with integers");
        };

        // All integers are sized with a power of two size.
        let size = ret_ty.layout::<M::T>().expect_size("`ret_ty` is an integer");
        let align = Align::from_bytes(size.bytes()).unwrap();
        if size > M::T::MAX_ATOMIC_SIZE {
            throw_ub!("invalid return type for `AtomicFetchAndOp` intrinsic: size too big");
        }

        // The value at the location right now.
        let previous = self.typed_load(ptr, ret_ty, align, Atomicity::Atomic)?;

        // Convert to integers
        let Value::Int(other_int) = other else { unreachable!() };
        let Value::Int(previous_int) = previous else { unreachable!() };

        // Perform operation.
        let next_int = Self::eval_int_bin_op(op, previous_int, other_int, int_ty)?;
        let next = Value::Int(next_int);

        // Store it again.
        self.typed_store(ptr, next, ret_ty, align, Atomicity::Atomic)?;

        ret(previous)
    }
}
```
## GetPayload

```rust
impl<M: Memory> Machine<M> {
    fn eval_intrinsic(
        &mut self,
        IntrinsicOp::GetUnwindPayload: IntrinsicOp,
        arguments: List<(Value<M>, Type)>,
        ret_ty: Type,
    ) -> NdResult<Value<M>> {
        if arguments.len() != 0 {
            throw_ub!("invalid number of arguments for `GetUnwindPayload` intrinsic");
        }

        let Type::Ptr(ret_ptr_ty) = ret_ty else {
            throw_ub!("invalid return type for `GetUnwindPayload` intrinsic");
        };
        if ret_ptr_ty.meta_kind() != PointerMetaKind::None {
            throw_ub!("invalid return type for `GetUnwindPayload` intrinsic");
        }

        let Some(thin_pointer) = self.active_thread().unwind_payloads.last() else {
            throw_ub!("GetUnwindPayload: the payload stack is empty");
        };

        let payload_pointer = Value::Ptr(Pointer { thin_pointer, metadata: None });

        ret(payload_pointer)
    }
}
```
