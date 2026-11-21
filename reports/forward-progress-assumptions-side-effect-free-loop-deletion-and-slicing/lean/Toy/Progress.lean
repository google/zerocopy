import Toy.Progress.Syntax
import Toy.Progress.Semantics
import Toy.Progress.RunLemmas
import Toy.Progress.BigStep
import Toy.Progress.Iteration
import Toy.Progress.Examples
import Toy.Progress.Deletion
import Toy.Progress.Slicing
import Toy.Progress.Mixing
import Toy.Progress.Characterizations

/-!
# Forward-progress assumptions, side-effect-free loop deletion, and slicing

A toy While language with an observable `emit` effect, under three behaviour semantics:
divergence-observable (`ObsBeh`), thread-level forward progress (`FPBeh`), and per-loop
progress flags (`MixedBeh`). The results characterize when deleting an emit-free loop and
slicing with respect to all `emit` statements are refinements under each semantics, and
model the hazard of inlining code compiled under one semantics into code compiled under
the other.
-/
