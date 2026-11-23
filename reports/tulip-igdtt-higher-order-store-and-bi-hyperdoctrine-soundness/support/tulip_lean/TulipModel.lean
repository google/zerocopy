-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import TulipModel.World
import TulipModel.Heap
import TulipModel.Monad
import TulipModel.Logic
import TulipModel.WP
import TulipModel.Equations
import TulipModel.Adequacy
import TulipModel.LandinKnot

/-!
# Root Entrypoint & Axiom Audit for the Mechanized Step-Indexed Model of TULIP

Imports all eight modules of `TulipModel` (`World`, `Heap`, `Monad`, `Logic`, `WP`,
`Equations`, `Adequacy`, `LandinKnot`) and verifies the kernel axiom footprint of the
flagship counterexamples, repaired program-logic rules, algebraic state equations,
adequacy theorems, Landin's knot case study, and Lean 4 universe barrier witnesses.
-/

#print axioms Tulip.published_wp_set_frame_ref_unsound
#print axioms Tulip.published_wp_get_frame_ref_unsound
#print axioms Tulip.published_wp_not_heap_monotone
#print axioms Tulip.repaired_wp_set_and_get_frame_ref_sound
#print axioms Tulip.wp_val
#print axioms Tulip.wp_bind
#print axioms Tulip.wp_wand
#print axioms Tulip.wp_frame
#print axioms Tulip.wp_step
#print axioms Tulip.wp_get
#print axioms Tulip.wp_set
#print axioms Tulip.wp_new
#print axioms Tulip.wp_rec
#print axioms Tulip.set_after_new
#print axioms Tulip.set_after_set
#print axioms Tulip.get_after_set
#print axioms Tulip.get_after_get_comm
#print axioms Tulip.set_after_get
#print axioms Tulip.set_after_get_unit
#print axioms Tulip.not_get_after_set_nostep
#print axioms Tulip.not_diagonal_get_idempotent
#print axioms Tulip.not_dead_new_elim
#print axioms Tulip.not_new_comm
#print axioms Tulip.diverge_wp_false
#print axioms Tulip.wp_adequacy_runClosed
#print axioms Tulip.landinFact_wp
#print axioms Tulip.landinFact_adequacy
#print axioms Tulip.landinFact_runClosed
#print axioms Tulip.landinFact_run_4
#print axioms Tulip.prop_collapses_program_values
#print axioms Tulip.cantor_no_predicate_surjection
