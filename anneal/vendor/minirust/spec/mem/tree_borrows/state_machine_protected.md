# Protected State Machine for Tree Borrows

The states of the protected state machine are given by `PermissionProt`.
This state machine is more complicated than the one for unprotected permissions, since it can also trigger UB on foreign accesses.

```rust
enum PermissionProt {
    /// Represents a shared reference to interior mutable data.
    Cell,
    /// The various flavours of `Reserved` correspond to a protected/noalias node where no writes happened yet.
    Reserved { 
        had_local_read: bool,
        had_foreign_read: bool
    },
    /// Represents an activated (written to) mutable reference, i.e. it must actually be unique right now.
    Unique,
    /// Represents a shared (immutable) reference.
    Frozen { had_local_read: bool },
    /// Represents a reference that experienced a foreign write. It can not be used locally anymore.
    Disabled,
}
```

The state machine transition table is given by these functions below.
When they return `Err` / signal UB, this means the state machine got stuck.

```rust
impl PermissionProt {
    fn local_read(self) -> Result<PermissionProt> {
        match self {
            PermissionProt::Cell => ret(PermissionProt::Cell),
            PermissionProt::Reserved { had_foreign_read, .. } => ret(PermissionProt::Reserved { had_local_read: true, had_foreign_read }),
            PermissionProt::Unique => ret(PermissionProt::Unique),
            PermissionProt::Frozen { .. } => ret(PermissionProt::Frozen { had_local_read: true }),
            PermissionProt::Disabled => throw_ub!("Tree Borrows: local read of protected Disabled reference"),
        }
    }

    fn local_write(self) -> Result<PermissionProt> {
        match self {
            PermissionProt::Cell => ret(PermissionProt::Cell),
            PermissionProt::Unique => ret(PermissionProt::Unique),
            PermissionProt::Reserved { had_foreign_read: false, .. } => ret(PermissionProt::Unique),
            PermissionProt::Reserved { had_foreign_read: true, .. } =>
                throw_ub!("Tree Borrows: local write to protected Reserved reference that had a foreign read"),
            PermissionProt::Frozen { .. } => throw_ub!("Tree Borrows: local write to protected Frozen reference"),
            // we don't know anymore if we were shared or mutable in this state
            PermissionProt::Disabled => throw_ub!("Tree Borrows: local write to protected Disabled reference"),
        }
    }

    fn foreign_read(self) -> Result<PermissionProt> {
        match self {
            PermissionProt::Cell => ret(PermissionProt::Cell),
            PermissionProt::Unique => throw_ub!("Tree Borrows: foreign read of protected Unique reference"),
            PermissionProt::Reserved { had_local_read, .. } => ret(PermissionProt::Reserved { had_local_read, had_foreign_read: true }),
            // Frozen and Disabled are kept unchanged.
            PermissionProt::Frozen { had_local_read } => ret(PermissionProt::Frozen { had_local_read }),
            PermissionProt::Disabled => ret(PermissionProt::Disabled),
        }
    }

    fn foreign_write(self) -> Result<PermissionProt> {
        match self {
            PermissionProt::Cell => ret(PermissionProt::Cell),
            PermissionProt::Frozen { had_local_read: true } | PermissionProt::Reserved { had_local_read: true, .. } =>
                    throw_ub!("Tree Borrows: foreign write of protected {} reference which had a local read", if matches!(self, PermissionProt::Frozen {..}) { "Frozen" } else { "Reserved" }),
            PermissionProt::Unique =>
                    throw_ub!("Tree Borrows: foreign read of protected Unique reference"),

            // not yet locally accessed states become Disabled
            PermissionProt::Frozen { had_local_read: false } | PermissionProt::Reserved { had_local_read: false, .. } => ret(PermissionProt::Disabled),
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
        // Everything except for `Cell` gets an initial read access.
        // `Unique` gets an initial write.
        match self {
            PermissionProt::Cell => None,
            PermissionProt::Unique => Some(AccessKind::Write),
            _ => Some(AccessKind::Read)
        }
    }

}
```

Protectors are ephemeral, they eventually end.
When they do, they cause a special "protector end access," and the state machine switches back to the unprotected state machine.
The following function defines which accesses are caused (this depends on the permission), and also defines how protected permissions turn into unprotected permissions for the unprotected state machine.

Note that the high-level idea is that if there previously was a local write, we again emit a local write; if there was a local read, we emit a local read.
If no local accesses happened, there also is no protector end access.

```rust
impl PermissionProt {
    /// When a protector is released, we transition to the unprotected state machine.
    /// Additionally, we might emit a _protector end access_, depending on our current state.
    /// The second state indicates that access, or is `None` when no access should happen.
    fn unprotect(self) -> (PermissionUnprot, Option<AccessKind>) {
        match self {
            PermissionProt::Unique => (PermissionUnprot::Unique, Some(AccessKind::Write)),
            PermissionProt::Reserved { had_local_read: true, .. } => (PermissionUnprot::Reserved, Some(AccessKind::Read)),
            PermissionProt::Reserved { had_local_read: false, .. } => (PermissionUnprot::Reserved, None),
            PermissionProt::Frozen { had_local_read: true } => (PermissionUnprot::Frozen, Some(AccessKind::Read)),
            PermissionProt::Frozen { had_local_read: false } => (PermissionUnprot::Frozen, None),
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
            PermissionProt::Reserved { had_local_read, .. } | PermissionProt::Frozen { had_local_read } => *had_local_read,

            PermissionProt::Disabled => false,

            // Cell never prevents deallocation
            PermissionProt::Cell => false,
        }
        // Note: the above is equivalent to `self.foreign_write().is_err()`
    }
}

```
