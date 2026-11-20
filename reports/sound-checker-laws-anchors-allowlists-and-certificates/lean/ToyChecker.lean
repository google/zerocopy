import ToyChecker.Basic
import ToyChecker.DownSet
import ToyChecker.Anchors
import ToyChecker.Extensional
import ToyChecker.Certificates
import ToyChecker.Relabel
import ToyChecker.RelativeCompleteness

/-!
# Sound checker laws: anchors, allowlists, certificates

Root module of the package. Namespace `Toy.Checker`.

* `ToyChecker.Basic`: checkers, soundness, relative completeness, pointwise
  order, named checkers, classical oracle, toy instance.
* `ToyChecker.DownSet`: the set of sound checkers (R1a, R1e).
* `ToyChecker.Anchors`: anchored soundness, allowlists, finite suites, and a
  relational law (R2a, R2c, R2f).
* `ToyChecker.Extensional`: the extensionality barrier (R3a).
* `ToyChecker.Certificates`: one-sided and two-sided certification with
  trusted verifiers (R4a–R4f).
* `ToyChecker.Relabel`: relabeling invariance (R5b, R5c).
* `ToyChecker.RelativeCompleteness`: relative completeness versus lockout
  (R6a, R6c, R6e–R6h).
-/
