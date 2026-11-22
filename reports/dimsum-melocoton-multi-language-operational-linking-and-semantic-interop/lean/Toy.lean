import Toy.EventLinking
import Toy.ReentrantMembrane

-- Axiom audit for all 13 hand-written theorems (expect zero axioms or standard subset only).
#print axioms EventLinking.refines_refl
#print axioms EventLinking.refines_trans
#print axioms EventLinking.link_horizontal_comp
#print axioms EventLinking.polarity_mismatch_breaks_refinement
#print axioms ReentrantMembrane.naive_sequential_preserves_inv
#print axioms ReentrantMembrane.naive_reentrant_linking_breaks_invariant
#print axioms ReentrantMembrane.wbcf_step_preserves_inv
#print axioms ReentrantMembrane.wbcf_reach_preserves_inv
#print axioms ReentrantMembrane.wbcf_awkward_safe
#print axioms ReentrantMembrane.non_wbcf_awkward_fails
#print axioms ReentrantMembrane.framed_membrane_reentrant_sound
#print axioms ReentrantMembrane.peer_only_preserves_private_frame
#print axioms ReentrantMembrane.fixed_coupled_reentrant_safe
