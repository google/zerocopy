# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""The carry-forward probe suite that the single-guard mutation test runs
against `codex_review` and each of its mutants."""

from __future__ import annotations

from .carry_forward_probes_history import HistoryPrecedenceAndReconcileProbes
from .carry_forward_probes_patch import PatchDriftAndModeProbes
from .support import (
    ANCHOR_HEAD,
    ANCHOR_IK,
    gate2_review,
    OLD_BASE,
    TREE,
    types,
)


class CarryForwardProbeSuite(
    PatchDriftAndModeProbes, HistoryPrecedenceAndReconcileProbes
):
    """The probe suite of `CodexReviewPropertyTests`."""

    def _run_carry_forward_probe_suite(self, mod: types.ModuleType) -> None:
        """Exercise all 49 carry-forward guards in-memory (no disk writes)."""
        clean_anchor = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key=ANCHOR_IK,
            submitted_at="2026-11-23T01:00:00Z",
        )
        verifier = lambda oh, ob, ot, nh, nb, other_heads=(): ANCHOR_IK

        self._probe_patch_drift_and_modes(mod)
        self._probe_history_precedence_and_reconcile(
            mod, clean_anchor, verifier
        )
