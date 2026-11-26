# State Machine for Tree Borrows

The core of Tree Borrows is a state machine for each node (reference) and each location.
The states of this state machine are called `Permission` since they regulate what each reference is _permitted_ to do.
Note that this presentation of Tree Borrows splits the protected from the unprotected state machine.
See `state_machine_protected.md` for the protected state machine, and `state_machine_unprotected.md` for the unprotected one.

The `Permission` type just tracks which of the two state machines we are currently using, and delegates everything appropriately.

```rust
enum Permission {
    Unprot(PermissionUnprot),
    Prot(PermissionProt)
}

impl Permission {

    fn transition(
        &mut self,
        access_kind: AccessKind,
        node_relation: NodeRelation,
    ) -> Result {
        match self {
            Permission::Unprot(p) => {
                *p = p.transition(access_kind, node_relation)?
            },
            Permission::Prot(p) => {
                *p = p.transition(access_kind, node_relation)?
            }
        };
        Ok(())
    }

    /// When a protector is released, we transition to the unprotected state machine.
    /// Additionally, we might emit a _protector end access_, depending on our current state.
    /// The second state indicates that access, or is `None` when no access should happen.
    ///
    /// This method may only be called when a protector is present.
    fn unprotect(self) -> (Permission, Option<AccessKind>) {
        match self {
            // This method is only called on protected nodes.
            Permission::Unprot(_) => unreachable!(),
            Permission::Prot(p) => {
                let (new_perm, access) = p.unprotect();
                (Permission::Unprot(new_perm), access)
            }
        }
    }

    /// Strongly protected nodes can block deallocation, based on their permission.
    /// Specifically, they block allocation iff they would cause UB on a foreign write,
    /// that is, if they have been locally accessed ("used"), with an exception for `Cell`.
    /// The check for whether the protector is actually strong happens elsewhere, before
    /// this method is called.
    fn prevents_deallocation(&self) -> bool {
        match self {
            Permission::Unprot(p) => p.prevents_deallocation(),
            Permission::Prot(p) => p.prevents_deallocation()
        }
    }

    /// This function checking this node's internal invariant.
    /// It is only used in debug asserts.
    fn matches_protector(&self, protected: Protected) -> bool {
        if protected.yes() {
            matches!(self, Permission::Prot(_))
        } else {
            matches!(self, Permission::Unprot(_))
        }
    }
}
```

When a new node is created, it may cause an implicit (read or write) access.
This is so the optimizer can insert reads / writes as soon as a reference is created.
The presence and type of the access depends on the permission.
The details are defined by the `init_access` function.

```rust
impl Permission {
    fn init_access(self) -> Option<AccessKind> {
        match self {
            Permission::Unprot(p) => p.init_access(),
            Permission::Prot(p) => p.init_access()
        }
    }
}
```
