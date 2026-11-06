# Tree Borrows Examples

This file contains the Tree Borrows examples.
Examples can be categorized along different axes:
* **Protected vs unprotected**: The difference is whether the reference is protected for a call, or not.
  Protected references have much more optimization potential since they are guaranteed to exist.
* **Shared vs mutable**: Shared references are read-only, whereas mutable references are more unique.
  For shared references, we usually pass these to other functions (since they can not change their value),
  whereas mutable references feature optimizations about writes.
* **Read vs write**: Most optimizations consist of deleting/inserting/re-ordering reads.
  Some also feature writes, but usually then the reference has to be activated first.

The examples are first categorized along the protector axis.
In other words, all optimizations involving protectors are in `protected`, and those without are in `unprotected.
Then, each file has a name like `mutable_reorder_read_up`, which means it's a mutable reference, and a read is being re-ordered.
For writes, we usually postfix `_activated`, because optimizations on writes require an activating write to happen first.
Simiarly, read optimizations with shared references usually involve a `_exposed` since the reference is passed to another function.

Proving a re-ordering always involved first proving that the access can be deleted, and then that it can be inserted somewhere else.
So we do not prove optimizations featuring only deletions or only insertions when we have proven a "reorder" one, since that would be redundant.

There is also the `impossible` folder.
It contains optimizations that do not hold, or only hold when using data races.
