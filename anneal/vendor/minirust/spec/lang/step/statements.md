
# Statements

Here we define how statements are evaluated.

```rust
impl<M: Memory> Machine<M> {
    #[specr::argmatch(statement)]
    fn eval_statement(&mut self, statement: Statement) -> NdResult { .. }
}
```

## Assignment

Assignment evaluates its two operands, and then stores the value into the destination.

- TODO: This probably needs some aliasing constraints, see [this discussion](https://github.com/rust-lang/rust/issues/68364)
  and [this one](https://github.com/rust-lang/unsafe-code-guidelines/issues/417).
- TODO: Should this implicitly retag, to have full `Validate` semantics?

```rust
impl<M: Memory> Machine<M> {
    fn place_store(&mut self, place: Place<M>, val: Value<M>, ty: Type) -> Result {
        if !place.aligned {
            throw_ub!("storing to a place based on a misaligned pointer");
        }
        // Alignment was already checked.
        self.typed_store(place.ptr.thin_pointer, val, ty, Align::ONE, Atomicity::None)?;
        ret(())
    }

    fn eval_statement(&mut self, Statement::Assign { destination, source }: Statement) -> NdResult {
        let (place, ty) = self.eval_place(destination)?;
        let (val, _) = self.eval_value(source)?;
        self.place_store(place, val, ty)?;

        ret(())
    }
}
```

## Mentioning a place without accessing it

This is what `let _ = place;` compiles to.
The place expression is still evaluated (so e.g. projections in there must be in-bounds), but no load occurs.
This means `let _ = *danling_ptr;` is legal.

```rust
impl<M: Memory> Machine<M> {
    fn eval_statement(&mut self, Statement::PlaceMention(place): Statement) -> NdResult {
        self.eval_place(place)?;
        ret(())
    }
}
```

## Setting a discriminant

```rust
impl<M: Memory> Machine<M> {
    fn eval_statement(&mut self, Statement::SetDiscriminant { destination, value }: Statement) -> NdResult {
        let (place, Type::Enum { variants, .. }) = self.eval_place(destination)? else {
            panic!("setting the discriminant type of a non-enum contradicts well-formedness");
        };
        if !place.aligned {
            throw_ub!("setting the discriminant of a place based on a misaligned pointer");
        }

        let tagger = match variants.get(value) {
            Some(Variant { tagger, .. }) => tagger,
            // guaranteed unreachable by the well-formedness checks
            None => panic!("setting an invalid discriminant ({value})"),
        };

        // Write the tag directly into memory.
        // This should be fine as we don't allow encoded data and the tag to overlap for valid enum variants.
        let accessor = |offset: Offset, bytes| {
            let ptr = self.ptr_offset_inbounds(place.ptr.thin_pointer, offset.bytes())?;
            // We have ensured that the place is aligned, so no alignment requirement here
            self.mem.store(ptr, bytes, Align::ONE, Atomicity::None)
        };
        encode_discriminant::<M>(accessor, tagger)?;
        ret(())
    }
}
```

## Validating a value

This statement asserts that a value satisfies its language invariant, and performs retagging for the aliasing model.
(This matches the `Retag` statement in MIR. They should probaby be renamed.)
To do this, we first lift retagging from pointers to compound values.

```rust
impl<M: Memory> Machine<M> {
    /// Find all pointers in this value, ensure they are valid, and retag them.
    fn retag_val(&mut self, val: Value<M>, ty: Type, fn_entry: bool) -> Result<Value<M>> {
        ret(match (val, ty) {
            // no (identifiable) pointers
            (Value::Int(..) | Value::Bool(..) | Value::Union(..), _) =>
                val,
            // base case
            (Value::Ptr(ptr), Type::Ptr(ptr_type)) => {
                let lookup = self.vtable_lookup();
                let val = self.mutate_cur_frame(|frame, mem| { mem.retag_ptr(&mut frame.extra, ptr, ptr_type, fn_entry, frame.func.implicit_writes, lookup) })?;
                Value::Ptr(val)
            }
            // recurse into tuples/arrays/enums
            (Value::Tuple(vals), Type::Tuple { sized_fields, .. }) =>
                Value::Tuple(vals.zip(sized_fields).try_map(|(val, (_offset, ty))| self.retag_val(val, ty, fn_entry))?),
            (Value::Tuple(vals), Type::Array { elem: ty, .. }) =>
                Value::Tuple(vals.try_map(|val| self.retag_val(val, ty, fn_entry))?),
            (Value::Variant { discriminant, data }, Type::Enum { variants, .. }) =>
                Value::Variant { discriminant, data: self.retag_val(data, variants[discriminant].ty, fn_entry)? },
            _ =>
                panic!("this value does not have that type"),
        })
    }

    fn eval_statement(&mut self, Statement::Validate { place, fn_entry }: Statement) -> NdResult {
        let (place, ty) = self.eval_place(place)?;

        // WF ensures all valid expressions are sized, so we can invoke the load.
        // This also ensures the value in the place satsifies the language invariant.
        let val = self.place_load(place, ty)?;
        let val = self.retag_val(val, ty, fn_entry)?;
        self.place_store(place, val, ty)?;

        ret(())
    }
}
```

## De-initializing a place

This statement replaces the contents of a place with `Uninit`.

```rust
impl<M: Memory> ConcurrentMemory<M> {
    fn deinit(&mut self, ptr: ThinPointer<M::Provenance>, len: Size, align: Align) -> Result {
        self.store(ptr, list![AbstractByte::Uninit; len.bytes()], align, Atomicity::None)?;
        ret(())
    }
}

impl<M: Memory> Machine<M> {
    fn eval_statement(&mut self, Statement::Deinit { place }: Statement) -> NdResult {
        let (p, ty) = self.eval_place(place)?;
        if !p.aligned {
            throw_ub!("de-initializing a place based on a misaligned pointer");
        }
        // Alignment was already checked.
        self.mem.deinit(p.ptr.thin_pointer, ty.layout::<M::T>().expect_size("WF ensures deinits are sized"), Align::ONE)?;

        ret(())
    }
}
```

## StorageDead and StorageLive

These operations (de)allocate the memory backing a local.

```rust
impl<M: Memory> StackFrame<M> {
    fn storage_live(&mut self, mem: &mut ConcurrentMemory<M>, local: LocalName) -> NdResult {
        // First remove the old storage, if any.
        // This means the same address may be re-used for the new stoage.
        self.storage_dead(mem, local)?;
        // Then allocate the new storage.
        let pointee_size = self.func.locals[local].layout::<M::T>().expect_size("WF ensures all locals are sized");
        let pointee_align = self.func.locals[local].layout::<M::T>().expect_align("WF ensures all locals are sized");
        let ptr = mem.allocate(AllocationKind::Stack, pointee_size, pointee_align)?;
        self.locals.insert(local, ptr);
        ret(())
    }

    fn storage_dead(&mut self, mem: &mut ConcurrentMemory<M>, local: LocalName) -> NdResult {
        let pointee_size = self.func.locals[local].layout::<M::T>().expect_size("WF ensures all locals are sized");
        let pointee_align = self.func.locals[local].layout::<M::T>().expect_align("WF ensures all locals are sized");
        if let Some(ptr) = self.locals.remove(local) {
            mem.deallocate(ptr, AllocationKind::Stack, pointee_size, pointee_align)?;
        }
        ret(())
    }
}

impl<M: Memory> Machine<M> {
    fn eval_statement(&mut self, Statement::StorageLive(local): Statement) -> NdResult {
        self.try_mutate_cur_frame(|frame, mem| {
            frame.storage_live(mem, local)
        })
    }

    fn eval_statement(&mut self, Statement::StorageDead(local): Statement) -> NdResult {
        self.try_mutate_cur_frame(|frame, mem| {
            frame.storage_dead(mem, local)
        })
    }
}
```
