import Toy

/-! Dependency audit: every line printed below must list nothing beyond
`propext`, `Classical.choice`, `Quot.sound`. -/

-- Relocation: flat addresses versus root slots
#print axioms Toy.handle_read_gc_stable
#print axioms Toy.handle_read_gc_stable_star
#print axioms Toy.handle_identity_gc_stable
#print axioms Toy.pinned_raw_gc_stable
#print axioms Toy.pinned_raw_gc_stable_star
#print axioms Toy.unpinned_raw_can_dangle
#print axioms Toy.unpinned_raw_can_alias
#print axioms Toy.unrooted_can_be_collected
#print axioms Toy.raw_stable_iff_pinned

-- Token: branded safepoint tokens
#print axioms Toy.current_view_reads_as_handle
#print axioms Toy.rt_keeps_pinned_view
#print axioms Toy.branded_tokens_sound
#print axioms Toy.branded_tokens_sound_closed
#print axioms Toy.staleProgram_rejected
#print axioms Toy.reloadProgram_accepted
#print axioms Toy.pinnedProgram_accepted
#print axioms Toy.afterUnpinProgram_rejected
#print axioms Toy.unbranded_use_is_stale
#print axioms Toy.pinned_view_valid_not_exclusive

-- Reentrancy: exclusive borrows against callbacks and finalizers
#print axioms Toy.checked_reentrancy_preserves_exclusive
#print axioms Toy.holder_checked
#print axioms Toy.unchecked_reentrancy_breaks_exclusive
#print axioms Toy.unchecked_reentrant_read_observes
#print axioms Toy.sync_unchecked_finalizer_breaks_exclusive
#print axioms Toy.sync_checked_finalizer_preserves_exclusive
#print axioms Toy.deferred_finalizer_preserves_exclusive
#print axioms Toy.deferred_then_poll_breaks_exclusive

-- Finalizer: resurrection and ordering
#print axioms Toy.resurrection_dangles
#print axioms Toy.retrace_sound
#print axioms Toy.objectless_finalizer_sound
#print axioms Toy.interleaved_order_sensitive
#print axioms Toy.two_phase_order_insensitive
