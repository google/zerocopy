-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import SideCondCert.Farkas
import SideCondCert.BitDomain
import SideCondCert.AEGraph

namespace SideCondCert

/-- Unified middle-end side-condition certificate (`SideCondCert`) for `HybridTrace`,
combining Farkas linear arithmetic multipliers (`FarkasCert2`), bit-mask/interval
transfer witnesses (`BitDomainCert`), and directed poison-monotonic `let`-DAG
e-graph refinement steps (`AEGraphCert`). -/
inductive UnifiedSideCond where
  | farkas    (cert : FarkasCert2)
  | bitDomain (cert : BitDomainCert)
  | aegraph   (src tgt : DAGExpr) (cert : AEGraphCert)
  deriving DecidableEq, Repr

/-- Unified total executable checker `checkSideCond`. -/
def checkSideCond : UnifiedSideCond → Bool
  | .farkas cert          => checkFarkasCert2 cert
  | .bitDomain cert       => checkBitDomainCert cert
  | .aegraph src tgt cert => checkAEGraphCert src tgt cert

/-- Declarative validity predicate `ValidSideCond`. -/
inductive ValidSideCond : UnifiedSideCond → Prop where
  | farkas {cert : FarkasCert2} (h : ValidFarkasCert2 cert) :
      ValidSideCond (.farkas cert)
  | bitDomain {cert : BitDomainCert} (h : ValidBitDomainCert cert) :
      ValidSideCond (.bitDomain cert)
  | aegraph {src tgt : DAGExpr} {cert : AEGraphCert} (h : ValidAEGraphCert src tgt cert) :
      ValidSideCond (.aegraph src tgt cert)

/-- Semantic meaning of a verified `UnifiedSideCond` certificate. -/
def SideCondSemantics : UnifiedSideCond → Prop
  | .farkas cert =>
      ∀ x y : Int, cert.c1.holds x y → cert.c2.holds x y → ¬ cert.negTarget.holds x y
  | .bitDomain cert =>
      ValidBitDomainCert cert
  | .aegraph src tgt _cert =>
      ∀ (env : Nat → PoisonOr Int) (letVal : PoisonOr Int),
        refinesPoison (evalDAGExpr env letVal src) (evalDAGExpr env letVal tgt)

/-- Unified soundness theorem (`checkSideCond_sound`). -/
theorem checkSideCond_sound (sc : UnifiedSideCond)
    (h_check : checkSideCond sc = true) :
    SideCondSemantics sc := by
  cases sc with
  | farkas cert =>
    exact checkFarkasCert2_sound cert h_check
  | bitDomain cert =>
    exact (checkBitDomainCert_iff_valid cert).mp h_check
  | aegraph src tgt cert =>
    exact checkAEGraphCert_sound h_check

/-- Unified completeness theorem (`checkSideCond_complete`). -/
theorem checkSideCond_complete (sc : UnifiedSideCond)
    (h_valid : ValidSideCond sc) :
    checkSideCond sc = true := by
  cases h_valid with
  | farkas h => exact (checkFarkasCert2_iff_valid _).mpr h
  | bitDomain h => exact (checkBitDomainCert_iff_valid _).mpr h
  | aegraph h => exact (checkAEGraphCert_iff_valid _ _ _).mpr h

/-- Bidirectional equivalence (`checkSideCond_iff_valid`). -/
theorem checkSideCond_iff_valid (sc : UnifiedSideCond) :
    checkSideCond sc = true ↔ ValidSideCond sc := by
  constructor
  · intro h
    cases sc with
    | farkas cert => exact .farkas ((checkFarkasCert2_iff_valid cert).mp h)
    | bitDomain cert => exact .bitDomain ((checkBitDomainCert_iff_valid cert).mp h)
    | aegraph src tgt cert => exact .aegraph ((checkAEGraphCert_iff_valid src tgt cert).mp h)
  · exact checkSideCond_complete sc

end SideCondCert
