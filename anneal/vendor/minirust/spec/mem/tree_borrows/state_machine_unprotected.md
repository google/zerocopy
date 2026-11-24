# Unprotected State Machine for Tree Borrows

The states of the unprotected state machine are given by `PermissionUnprot`.

```rust
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
```

The state machine transition table is given by these four functions.
When they return `Err` / signal UB, this means the state machine got stuck.

```rust
impl PermissionUnprot {
    fn local_read(self) -> Result<PermissionUnprot> {
        ret(
            match self {
                PermissionUnprot::Disabled => throw_ub!("Tree Borrows: local read of Disabled reference"),
                // All other states are kept unchanged.
                perm => perm,
            }
        )
    }

    fn local_write(self) -> Result<PermissionUnprot> {
        match self {
            PermissionUnprot::Frozen => throw_ub!("Tree Borrows: local write of Frozen reference"),
            PermissionUnprot::Disabled => throw_ub!("Tree Borrows: local write of Disabled reference"),
            PermissionUnprot::Cell => ret(PermissionUnprot::Cell),
            _ => ret(PermissionUnprot::Unique),
        }
    }

    fn foreign_read(self) -> Result<PermissionUnprot> {
        match self {
            PermissionUnprot::Reserved => ret(PermissionUnprot::Reserved),
            PermissionUnprot::Unique => ret(PermissionUnprot::Frozen),
            // All other states are kept unchanged.
            perm => ret(perm),
        }
    }

    fn foreign_write(self) -> Result<PermissionUnprot> {
        match self {
            PermissionUnprot::Cell => ret(PermissionUnprot::Cell),
            PermissionUnprot::ReservedIm => ret(PermissionUnprot::ReservedIm),
            // All other states become Disabled.
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
        // Note: this is equivalent to `self.foreign_write().is_err()`, just like for protected
        // references, since unprotected references never trigger UB for foreign accesses.
        false
    }

    fn init_access(self) -> Option<AccessKind> {
        // Everything except for `Cell` gets an initial read access.
        // We never perform implicit writes for unprotected references.
        match self {
            PermissionUnprot::Cell => None,
            _ => Some(AccessKind::Read)
        }
    }
}
```
