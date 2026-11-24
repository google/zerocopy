# Tree Borrows: Permission information for a reborrow

This file defines the settings for a reborrow: it says which permissions the new tag should get where.
The logic for applying those settings is separate (in the `reborrow` funcion).

```rust
struct ReborrowSettings {
    /// The permissions to set "inside" the data the reference points to (indexed
    /// related to the reference).
    inside: List<Permission>,
    /// The permission to set for the "outside" part.
    outside: Permission,
    /// Whether and which protector to set.
    protected: Protected,
}
```

Computing the permissions requires a "mask" indicating where all the `UnsafeCell` are.

```rust
/// Converts a list of cell locations into a "freeze mask",
/// where each `bool` indicates whether the byte is frozen (i.e., *outside* all cells).
fn cells_to_freeze_mask(cells: List<(Offset, Size)>, size: Size) -> List<bool> {
    let padded_front = std::iter::once((Offset::ZERO, Size::ZERO)).chain(cells.iter());
    let padded_back = cells.iter().chain(std::iter::once((size, Size::ZERO)));

    // The following `zip` produces iterators that look like this:
    //
    // current: (0, 0)       first pair     second pair       …        last pair
    // next:    first pair   second pair    …             last pair    (size, size)
    //
    // This is done so that we know when the "next" range of UnsafeCells starts.
    // In the first iteration, we "see" an UnsafeCell between offsets 0 and 0,
    // and we know that the bytes from offset 0 until `(first pair).0` are free
    // of UnsafeCells.  Only in the second iteration do we actually see the
    // first real UnsafeCell.  In general, the loop has n+1 iterations, since we
    // visit the area before the first and after the last UnsafeCell.
    let mut mask = List::new();
    for (current, next) in padded_front.zip(padded_back) {
        // The `current` bytes are inside an UnsafeCell, and hence not frozen.
        mask.append(list![false; current.1.bytes()]);
        // The bytes until `next` are frozen.
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
        vtable_lookup: impl Fn(ThinPointer<TreeBorrowsProvenance>) -> crate::lang::VTable + 'static,
    ) -> List<bool> {
        match (self, layout, ptr_metadata) {
            (UnsafeCellStrategy::Sized { cells }, LayoutStrategy::Sized(size, _align), ..) => {
                cells_to_freeze_mask(cells, size)
            },
            (UnsafeCellStrategy::Slice { element_cells } , LayoutStrategy::Slice(size, _align), Some(PointerMeta::ElementCount(count))) => {
                let element_mask = cells_to_freeze_mask(element_cells, size);
                let mut mask = List::new();
                for _ in Int::ZERO..count {
                    mask.append(element_mask);
                };
                mask
            },
            (UnsafeCellStrategy::TraitObject, LayoutStrategy::TraitObject(_trait_name), Some(PointerMeta::VTablePointer(ptr))) => {
                let vtable = vtable_lookup(ptr);
                cells_to_freeze_mask(vtable.cells, vtable.size)
            },
            (UnsafeCellStrategy::Tuple { head_cells, tail_cells }, LayoutStrategy::Tuple { head, tail }, _) => {
                let mut mask = cells_to_freeze_mask(head_cells, head.end);
                mask.append(tail_cells.freeze_mask(tail, ptr_metadata, vtable_lookup));
                mask
            },
            _ => panic!("Invalid LayoutStrategy and PointerMeta combination"),
        }
    }
}
```

Finally, the core operation is to compute a `ReborrowPermission` given a pointer and its type.

```rust
impl ReborrowSettings {
    /// Compute the permissions to be assigned when retagging the given pointer.
    /// `None` indicates that no retagging should happen.
    fn new(
        ptr: Pointer<TreeBorrowsProvenance>,
        ptr_type: PtrType,
        fn_entry: bool,
        params: TreeBorrowsParams,
        fn_implicit_writes: bool, // wether implicit_writes are enabled for the currently evaluated function, or not
        vtable_lookup: impl Fn(ThinPointer<TreeBorrowsProvenance>) -> crate::lang::VTable + 'static,
    ) -> Option<Self> {
        // Returns None for `Raw`, `FnPtr` and `VTablePtr`, so `ptr_type` can only be `Ref` and `Box` from here.
        let Some(pointee_info) = ptr_type.safe_pointee() else {
            return None;
        };
        if matches!(ptr_type, PtrType::Ref { mutbl: Mutability::Mutable, pointee } | PtrType::Box { pointee } if !pointee.unpin) {
            // Mutable reference / Box to pinning type: retagging is a NOP.
            // FIXME: with `UnsafePinned`, this should do proper per-byte tracking.
            return None;
        }

        // We protect upon function entry.
        let protected = if fn_entry {
            // Boxes are weakly protected, everything else strongly.
            match ptr_type {
                PtrType::Box { .. } => Protected::Weak,
                _ => Protected::Strong,
            }
        } else {
            Protected::No
        };

        // Implicit writes are performed for protected references, only if globally enabled (`params.implicit_writes`),
        // and only if the function has not opted out via the `#[rustc_no_writable]` attribute (`fn_implicit_writes`).
        let implicit_writes_enabled = protected.yes() && params.implicit_writes && fn_implicit_writes;

        // Helper to compute the permission, given whether it is inside the pointee and whether it is frozen.
        let perm = |inside: bool, frozen: bool| {
            // Helper to choose the correct permission, based on protection.
            let mk_perm = |unprot, prot| if protected.yes() { Permission::Prot(prot) } else { Permission::Unprot(unprot) };

            match ptr_type {
                // Shared references
                PtrType::Ref { mutbl: Mutability::Immutable, .. } =>
                    if frozen {
                        mk_perm(PermissionUnprot::Frozen, PermissionProt::Frozen { had_local_read: false })
                    } else {
                        mk_perm(PermissionUnprot::Cell, PermissionProt::Cell)
                    },
                // Mutable references and Boxes (Boxes are treated the same as mutable references)
                PtrType::Ref { mutbl: Mutability::Mutable, .. } | PtrType::Box { .. } =>
                    if implicit_writes_enabled && inside {
                        // The implicit write only happens on the inside.
                        // `implicit_writes_enabled` implies `protected.yes()`, so this case is always protected.
                        assert!(protected.yes());
                        Permission::Prot(PermissionProt::Unique)
                    } else {
                        // Unprotected interior-mutable references and boxes start in `ReservedIm`, but if they are protected we ignore the `Im`
                        mk_perm(
                          if frozen { PermissionUnprot::Reserved } else { PermissionUnprot::ReservedIm },
                          PermissionProt::Reserved { had_local_read: false, had_foreign_read: false }
                        )
                    },
                // Cannot occur: `safe_pointee()` returns `None` for these variants.
                PtrType::Raw { .. } | PtrType::FnPtr | PtrType::VTablePtr(_) => unreachable!("safe_pointee() returns None for Raw, FnPtr, and VTablePtr; should have returned early on function entry"),
            }
        };

        let inside = pointee_info.unsafe_cells.freeze_mask(pointee_info.layout, ptr.metadata, vtable_lookup).map(|freeze|
            perm(/* inside */ true, freeze)
        );
        let outside = perm(/* inside */ false, pointee_info.freeze);

        Some(ReborrowSettings { protected, inside, outside })
    }
}
```
