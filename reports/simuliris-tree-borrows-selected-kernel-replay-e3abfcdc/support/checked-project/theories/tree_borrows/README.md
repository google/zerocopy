# Tree Borrows

Forked and adapted from the sibling folder `../stacked_borrows` with the same structure.

## Structure

### TCB

Our trusted computing base is the definition of our borrow calculus language.
It consists of the following files:

* `tree.v` defines our notion of trees, where nodes are indexed by tags.
* `locations.v` defines pointers in our block-based (CompCert) memory model.
* `lang_base.v` defines the syntax of our core calculus, which is mostly unchanged from the one in `../stacked_borrows`
* `expr_semantics.v` defines the semantics of expressions, ignoring the aliasing model. It is also mostly unchanged from SB.
* `bor_semantics.v` defines the semantics of retags and the aliasing. It is where most of Tree Borrows' core definitions live.
* `parallel_subst.v` defines parallel substitution.
* `lang.v` finally instantiates the language interface of Simuliris.

Most of our example files construct an end-to-end proof against the semantics outlined in here, using the machinery provided by Simuliris.
Of course, that end-to-end proof uses Simuliris' definition of refinement, but this definition is already in the literature.


### Development

* `defs.v` contains basic logical definitions, notably that of well-formed states (`state_wf`).
* `tactics.v` and `class_instances.v` are some more Simuliris-related infrastructure.
* `tree_lemmas.v`, `bor_lemmas.v`, `steps_foreach.v`, `steps_inv.v`, and `steps_preserve.v` contain basic lemmas to help with the manipulation of trees.
* `steps_wf.v` proves that all OpSem steps preserve state well-foundedness.
* `tree_access_laws.v` contains more complex lemmas about the entire memory (`trees`) rather than single allocations (`tree`).
* `steps_progress.v` states success conditions for the various borrow steps so that we can prove absence of UB or exploit presence of UB.
* `tkmap_view.v` defines views (partial ownership) of the global maps we use to remember the kind of each tag.
* `trees_equal/` contains a number of files related to a `trees_equal` binary relation between trees.
  Our simulation relation has to allow small differences between the trees in the source and target program; this relation describes the extent to which they are allowed to differ.
* `logical_state.v` defines the invariants and instantiates the simulation relation,
  using among others a notion of when trees are similar in `trees_equal/`.
* `tag_protected_laws.v` contains reasoning principles about protectors.
* `loc_controlled_laws.v` contains reasoning principles for "heaplets" and tags.
* `steps_refl.v` and `steps_opt.v` prove the main execution lemmas.
* `steps_all.v`, `proofmode.v`, and `primitive_laws.v` collect all laws of the program logic.
* `wf.v` defines well-formedness for expressions, in particular that they contain no raw location literals.
* `behavior.v` defines the notion of contextual refinement and expression well-formedness.
* `adequacy.v` contains the resulting adequacy proof.
* `examples/` contains example optimizations, further subdivided into
  - `unprotected/` optimizations, which are program transformations that can be applied even in the absence of protectors,
  - `protected/` optimizations, which require a protector to hold,
  - `impossible/` optimizations used to hold under Stacked Borrows,
    but we know of counter-examples under Tree Borrows.

In addition, `read_read_reorder/` provides proofs of simple reorderings (swapping adjacent operations in a sequential setting) directly against the operational semantics.
You can find more details in the associated [`README.md`](read_read_reorder/README.md).

## Correspondence with Sections 2 and 3

Here, we describe how we formalized the semantics of Tree Borrows described in the paper.
We start with the formalization of trees given in `tree.v`, which defines n-ary trees where each node is indexed by an integer, called a `tag`.

Next, `lang_base.v` defines the type of permission, notably defining `Inductive permission` in line 83, which corresponds to the states of the state machine.
Like in Miri, we actually have two kinds of protectors (line 113), with `ProtStrong` corresponding to regular protectors and `ProtWeak` not being used in the paper.
(It is used to model `Box` aliasing rules, something not touched upon in the paper and also something that might be removed in future versions of Rust.)

Next, `bor_semantics.v` defines the main Tree Borrows semantics.
In line 224-291, we define the notions of "relatedness" in a tree (parent/child/local/foreign etc.).
This culminates in `rel_dec`, which decides the relation between two tags in a tree.

The main state machine is defined in line 340, the function `apply_access_perm_inner`.
This depends on the access kind (read/write), the relatedness (foreign/local) and on whether the current node is protected.
It returns the new permission, or `None` which indicates UB.

This is used in `apply_access_perm`, which also tracks "initialization" which is part of lazy range detection.
It is used to cause UB when a protected, already locally accessed node becomes disabled.
Compare to the description around line 545 in the paper.

The function `item_apply_access` lifts this from one permission to a tree item, which contains the entire range, accounting for every offset in a block in the block-based memory model.
Then, `tree_apply_access` lifts this to an entire tree, and `trees_apply_access` lifts it to the entire memory.

The function `memory_deallocate` ensures that no deallocation happens while a protector exists. This is not described in the paper, but this behavior is inherited from Stacked Borrows.
It is also present in the Miri implementation.

After some basic proofs about the definitions, we contine in line 780 with the definition of retags.
A retag is the core operation creating a new reference, which is parameterized by a "pointer kind" defining if this is to be a shared/mutable reference with(out) interior mutability.
Further it defines whether there are to be protectors.
The function `create_child` is the main function used during a retag.

Finally, the protector end semantics are defined starting at line 841, with the functions `tree_get_all_protected_tags_initialized_locs` and `tree_access_all_protected_initialized`.

To put all the definitions together, the inductive `bor_step` is defined.
It is coupled to the main operational semantics by a series of "events".
For example, a read (called "copy" here) causes a `CopyEvt`, which is picked up by the `CopyIS` rule.
This will ensure the tag exists, and then traverse the tree, advancing the state machine appropiately and triggering UB if necessary.

Also of interests to reviewers are lines 1000-1038. This defines a "unit test" for the `rel_dec` and `create_child` functions.
Since `rel_dec` is not commutative, it can be difficult to remember which node is which and whether an output of e.g. "Child" means that the first node is a child of the second or the other way around.
The "unit test" makes it clear that an output of "Child" indeed means that the first node is a child of the second.

## Correspondence with Section 5

Section 5 has three examples, one for deleting reads, one for deleting writes, and one for reordering reads.

### Paragraph 1: Deleting Reads (Example 16)

This example corresponds to the one in  `examples/unprotected/shared_delete_read_escaped.v`.
The Coq example is very close to the one in the paper.
To model the environment of the closure in the Rust code, we use an explicit argument passed to `f`.

In the justification in the paper (around line 818), we say that a protected Reserved cousing of a tag can be conflicted in one side,
but not in the other. In Coq, this is achieved using the `pseudo_conflicted` case of `perm_eq_up_to_C` in line 88 of `trees_equal_base.v`.

### Paragraph 2: Deleting Writes (Optimizing with Protectors) (Example 17)

This example corresponds to the one in `examples/protected/mutable_reorder_write_up_activated_paper.v`.
This Coq example corresponds very closely to the one in the paper.
Again, closure environments are modeled with extra arguments.

This is also where we need (and the paper finally explains) protector end semantics.
Protector end semantics ensure that two states remain `trees_equal` even when a protector is removed.
The main lemma here is `trees_equal_remove_call` in line 1160 of `trees_equal_endcall_law.v`,
which shows that after the protector end access, `trees_equal` is preserved even without the just ended protector.

### Paragraph 4: Reordering Reads (Example 18)

This is proven in `read_read_reorder`, particularly in `read_reorder.v`.
These proofs do not use the `simuliris` library, but instead they do a much simpler equivalence proof directly against the operational semantics.
This is possible because there is no unknown code involved in this transformation (the reordered instructions are immediately adjacent).
We also cannot use `simuliris` since the transformation does not hold in our concurrent semantics.
We suspect that they also hold in a realistic concurrent setting where data races are Undefined Behavior, but this would be very challenging to prove so we consider it out-of-scope.

Specifically, the simple notion of "equivalence after a few steps" is in `equivalence_def.v`.
The proof that the two reads can be reordered is in `read_reorder.v`.
The file `low_level.v` contains low-level lemmas used in `read_reorder.v`

### Other Examples From The Paper

Example 1 is similar to the one shown in `examples/unprotected/mutable_delete_read.v`.
The one shown in Coq has two places where arbitrary unknown functions are called, and Example 1 is just a special case of that, if one instantiates these unknown functions correctly.

Example 14 is shown in `example/protected/shared_read_insert_coinductive.v`.
The only difference to the one in the paper is that Rust's `0..n` syntax is desugared to an explicit counter.

## Program Logic

As mentioned in the paper, the way we proved these refinements is using a program logic.
This program logic can prove refinements, and uses several separation logic resources to accomplish this.
You can see the separation logic in action in the examples shown above.
Here, we explain the resources that you will encounter when stepping through the proof.

The `t $$ tk` resource associates a "tag" `t` with a "tag kind" `tk`. Remember that each tag corresponds to a specific node in the borrow tree.
The tag kind is a very coarse over-approximation of the shape of the tree from that specific node.

The simplest kind is `tk_local`, which says that the tree here is a singleton, and this tag is the only tag in the tree.
`tk_local` tags are used for new fresh allocations that do not have their address taken, and allows treating them as local variables.

To talk about the value of such a local tag, the "heaplet points-to" `l ↦t∗[tk_local]{t} vs` is used.
This resource comes in two kinds, with `l ↦t∗[tk_local]{t} vs` for the target side and `l ↦s∗[tk_local]{t} vs` for the source side.
In it, `vs` is a list of values, and this heaplet expresses knowledge that the values stored at `l` are `vs`. `vs` is a list so that we can talk about arrays; in many examples it is a singleton list.

This "heaplet" resource works like the separation logic points-to. The version with `tk_local` is exclusive, expressing that this location is "local" to the function.
`tk_local` heaplets are very unrestricted: they can be set to arbitrary values in either source and target, just like local variables.
The rules for heaplets with a different tag kind are more restricted, as we see now.

The next tag kind is `tk_unq`, which corresponds to a mutable reference. It is created when a reference is mutably retagged.
It has two kinds: `tk_unq tk_res` and `tk_unq tk_act`, which correspond to the reservation and activation phase of a mutable reference.
When a `tk_unq tk_res` is written to, it transitions to `tk_unq tk_act` (See rule `sim_write_activate_unprotected` in `step_laws/steps_unique.v`).

The heaplet points-tos for `tk_unq` are still exclusive, since a mutable reference should give us unique access to the memory.
Unfortunately, this is only true with protectors (see below); without protectors, these tags must be written to in lockstep and already deleting reads is restricted.

Finally, there is `tk_pub`, which is the "default" permission that is also not exclusive, but persistent.
Once a tag has been made public, the program logic exposes very weak guarantees on it, but it can be passed around freely.
This corresponds to how it's hard to optimize around unknown pointers.

`tk_pub` tags come in two kinds: Those with, and those without a heaplet.
Those without a heaplet carry almost no information.
Those with a heaplet are more interesting: They correspond to "frozen" tags.
`tk_pub` heaplets are also persistent, so the values stored there can not change their value.
This allows passing a shared reference to another function and later still knowing that the function could not have changed the value.

At this point, we should mention that all heaplets represent "conditional" knowledge: They basically say that the given value is stored in memory, or that alternatively the corresponding tag has since become `Disabled`.
This allows proving rules like lockstep reads (`sim_copy` in `step_laws/steps_unique.v`), based on the argument that either the source has UB when the tag is `Disabled`, or we know that the heaplet is still alive and hence the read is possible.
This means that lockstep rules are typically easy to prove with our setup, but proving anything about single-sided reads is much more difficult, which is why without protectors,  we can only prove read removal optimizations.

### Protectors

Protectors allow us to prove much more optimizations.
The reason here is that protectors give us "independent" and exclusive ownership that a certain tag is has not yet become `Disabled`.
This is expressed using permissions like `c @@ <[t_i:=<[i +ₗ 0%nat:=EnsuringAccess Strongly]> ∅]> ∅`, which say that call `c` protects tag `t_i` at offset `i`.
Once we have such a protector permission, we are able to treat `tk_unq` tags almost like `tk_local` tags: They can be read from and written to individually, can have unrelated values on each side, etc. (See `step_laws/steps_prot.v`.)

The only restrictions here are that the activating write must still happen in lockstep (`sim_write_activate_protected` in `step_laws/steps_unique.v`), and that the values must be related when the protector ends (line 316, for lemma `sim_protected_unprotect` in `step_laws/steps_opt.v`).
This corresponds to what we claimed in the paper (860-870).

