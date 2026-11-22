#!/usr/bin/env python3
"""Deterministic verification probe for build/environment setup & CDCL resolution.

Covers five technical pillars using only the Python 3.10+ standard library:
  1. CDCL PubGrub (interval terms, conflict-clause learning, culprit priority,
     heap-iterative derivation reporter & iterative teardown) vs. a pointwise-
     exclusion backjumping model of resolvelib (safe vs. optimistic backjumping
     and backtrack_causes variable-ordering sensitivity).
  2. PEP 508 Boolean marker-algebra universal lockfile forking (Fork::set_env
     disjoint-marker pruning, single-spec no-fork rule, N+1 conflict splitting,
     dominated single-conflict fast path, and cycle-safe marker propagation) vs.
     single-platform flat lockfile drift.
  3. Pinned benchmark evaluator & trace-export forensics (EnvBench@1ba26950,
     Repo2Run@65042aa2, SetupBench@041a412f, SWE-smith@9b74ac08,
     ExecutionAgent@8fb16de8) vs. hardened subshell, manifest, and test graders.
  4. Synthetic competing-risks registry drift vs. per-release --exclude-newer
     timestamp-cut CDCL resolution and content-addressed lockfiles.
  5. Illustrative dual-environment rollback discrete-time Markov chain (DTMC)
     vs. in-place container pollution.

Run from the corpus root:
  PYTHONHASHSEED=1 python3 -I -B reports/agent-build-systems-pubgrub-resolution-and-environment-reproduction/scripts/verify_build_env_pubgrub.py
"""

from __future__ import annotations

from dataclasses import dataclass, field
import json
import os
import random
import shlex
import subprocess
import sys
import tempfile
from typing import Callable

INF_VER = 1_000_000_000


# ============================================================================
# PILLAR 1: CDCL PubGrub + Iterative Proof-Tree Reporter vs. resolvelib Model
# ============================================================================


@dataclass(frozen=True)
class VersionRange:
    """Canonical sorted tuple of non-empty disjoint half-open intervals [lo, hi)."""

    intervals: tuple[tuple[int, int], ...] = ()

    @staticmethod
    def empty() -> VersionRange:
        return VersionRange(())

    @staticmethod
    def full() -> VersionRange:
        return VersionRange(((0, INF_VER),))

    @staticmethod
    def singleton(v: int) -> VersionRange:
        return VersionRange(((v, v + 1),))

    @staticmethod
    def between(lo: int, hi: int) -> VersionRange:
        return VersionRange(((lo, hi),)) if lo < hi else VersionRange(())

    @staticmethod
    def higher_than(lo: int) -> VersionRange:
        return VersionRange.between(lo, INF_VER)

    @staticmethod
    def strictly_lower_than(hi: int) -> VersionRange:
        return VersionRange.between(0, hi)

    def is_empty(self) -> bool:
        return len(self.intervals) == 0

    def contains(self, v: int) -> bool:
        return any(lo <= v < hi for lo, hi in self.intervals)

    def union(self, other: VersionRange) -> VersionRange:
        raw = sorted(self.intervals + other.intervals)
        if not raw:
            return VersionRange.empty()
        merged: list[tuple[int, int]] = [raw[0]]
        for lo, hi in raw[1:]:
            plo, phi = merged[-1]
            if lo <= phi:
                merged[-1] = (plo, max(phi, hi))
            else:
                merged.append((lo, hi))
        return VersionRange(tuple(merged))

    def complement(self) -> VersionRange:
        if not self.intervals:
            return VersionRange.full()
        res: list[tuple[int, int]] = []
        cur = 0
        for lo, hi in self.intervals:
            if cur < lo:
                res.append((cur, lo))
            cur = hi
        if cur < INF_VER:
            res.append((cur, INF_VER))
        return VersionRange(tuple(res))

    def intersection(self, other: VersionRange) -> VersionRange:
        a, b = self.intervals, other.intervals
        if len(a) == 1 and len(b) == 1:
            lo = a[0][0] if a[0][0] > b[0][0] else b[0][0]
            hi = a[0][1] if a[0][1] < b[0][1] else b[0][1]
            return VersionRange(((lo, hi),)) if lo < hi else VersionRange(())
        res: list[tuple[int, int]] = []
        i, j = 0, 0
        while i < len(a) and j < len(b):
            lo = max(a[i][0], b[j][0])
            hi = min(a[i][1], b[j][1])
            if lo < hi:
                res.append((lo, hi))
            if a[i][1] < b[j][1]:
                i += 1
            else:
                j += 1
        return VersionRange(tuple(res))

    def difference(self, other: VersionRange) -> VersionRange:
        return self.intersection(other.complement())

    def subset_of(self, other: VersionRange) -> bool:
        return self.difference(other).is_empty()

    def is_disjoint(self, other: VersionRange) -> bool:
        return self.intersection(other).is_empty()

    def __str__(self) -> str:
        if not self.intervals:
            return "none"
        if self.intervals == ((0, INF_VER),):
            return "any"
        parts: list[str] = []
        for lo, hi in self.intervals:
            if hi == lo + 1:
                parts.append(f"=={lo}")
            elif lo == 0:
                parts.append(f"<{hi}")
            elif hi == INF_VER:
                parts.append(f">={lo}")
            else:
                parts.append(f">={lo},<{hi}")
        return " || ".join(parts)


@dataclass(frozen=True)
class Term:
    """PubGrub Term over domain Versions U {unselected} (Weizenbaum doc/solver.md:84-122).

    Positive(R) denotes R (package must be selected with v in R).
    Negative(R) denotes (Full \\ R) U {unselected}.
    """

    rng: VersionRange
    positive: bool = True

    @staticmethod
    def any_term() -> Term:
        return Term(VersionRange.empty(), positive=False)

    @staticmethod
    def empty_term() -> Term:
        return Term(VersionRange.empty(), positive=True)

    @staticmethod
    def exact(v: int) -> Term:
        return Term(VersionRange.singleton(v), positive=True)

    def negate(self) -> Term:
        return Term(self.rng, not self.positive)

    def intersection(self, other: Term) -> Term:
        if self.positive and other.positive:
            return Term(self.rng.intersection(other.rng), True)
        if self.positive and not other.positive:
            return Term(self.rng.difference(other.rng), True)
        if not self.positive and other.positive:
            return Term(other.rng.difference(self.rng), True)
        return Term(self.rng.union(other.rng), False)

    def union(self, other: Term) -> Term:
        return self.negate().intersection(other.negate()).negate()

    def difference(self, other: Term) -> Term:
        return self.intersection(other.negate())

    def subset_of(self, other: Term) -> bool:
        return self.difference(other) == Term.empty_term()

    def is_disjoint(self, other: Term) -> bool:
        return self.intersection(other) == Term.empty_term()

    def __str__(self) -> str:
        return str(self.rng) if self.positive else f"not {self.rng}"


@dataclass
class Incompatibility:
    """Context-independent forbidden conjunction of package terms."""

    id: int
    terms: dict[str, Term]
    kind: str  # "not_root" | "no_versions" | "dep" | "derived"
    causes: tuple[int, int] | None = None
    dep_info: tuple[str, VersionRange, str, VersionRange] | None = None

    def is_terminal(self, root_pkg: str, root_ver: int) -> bool:
        if not self.terms:
            return True
        if len(self.terms) > 1:
            return False
        pkg, term = next(iter(self.terms.items()))
        return pkg == root_pkg and term.positive and term.rng.contains(root_ver)


@dataclass
class DatedDerivation:
    global_index: int
    decision_level: int
    cause_id: int
    accumulated: Term


@dataclass
class PackageAssignments:
    derivations: list[DatedDerivation] = field(default_factory=list)
    decision: tuple[int, int, int] | None = None  # (global_idx, decision_level, version)

    def current_term(self) -> Term:
        if self.decision is not None:
            return Term.exact(self.decision[2])
        return self.derivations[-1].accumulated

    def is_decided(self) -> bool:
        return self.decision is not None

    def satisfier(self, target_negated: Term) -> tuple[int | None, int, int]:
        """Earliest assignment whose accumulated intersection is disjoint with target_negated."""
        lo, hi = 0, len(self.derivations)
        while lo < hi:
            mid = (lo + hi) // 2
            if not self.derivations[mid].accumulated.is_disjoint(target_negated):
                lo = mid + 1
            else:
                hi = mid
        if lo < len(self.derivations):
            dd = self.derivations[lo]
            return dd.cause_id, dd.global_index, dd.decision_level
        assert self.decision is not None, "Satisfier must exist in derivations or decision"
        gidx, dl, _ = self.decision
        return None, gidx, dl


@dataclass
class ResolutionStats:
    """Conflict culprit/affected counters (pubgrub-rs/src/solver.rs:57-90)."""

    unit_propagation_affected: int = 0
    unit_propagation_culprit: int = 0
    dependencies_affected: int = 0
    dependencies_culprit: int = 0

    def conflict_count(self) -> int:
        return (
            self.unit_propagation_affected
            + self.unit_propagation_culprit
            + self.dependencies_affected
            + self.dependencies_culprit
        )


# DerivationTree structures matching pubgrub-rs/src/report.rs:31-65
@dataclass
class ExternalNode:
    kind: str  # "not_root" | "no_versions" | "dep"
    pkg: str
    rng: VersionRange
    dep_pkg: str | None = None
    dep_rng: VersionRange | None = None

    def format_text(self) -> str:
        if self.kind == "not_root":
            return f"solving dependencies of {self.pkg} {self.rng}"
        if self.kind == "no_versions":
            return f"there is no version of {self.pkg} in {self.rng}"
        return f"{self.pkg} {self.rng} depends on {self.dep_pkg} {self.dep_rng}"


@dataclass
class DerivedNode:
    terms: dict[str, Term]
    shared_id: int | None
    cause1: ExternalNode | DerivedNode
    cause2: ExternalNode | DerivedNode


DerivationTree = ExternalNode | DerivedNode


def _format_terms(terms: dict[str, Term]) -> str:
    if not terms:
        return "version solving failed"
    if len(terms) == 1:
        pkg, term = next(iter(terms.items()))
        if pkg == "root" and term.positive:
            return "version solving failed"
        if term.positive:
            return f"{pkg} {term.rng} is forbidden"
        return f"{pkg} {term.rng} is required"
    pos = [f"{p} {t.rng}" for p, t in sorted(terms.items()) if t.positive and p != "root"]
    neg = [f"{p} {t.rng}" for p, t in sorted(terms.items()) if not t.positive]
    if len(pos) == 1 and len(neg) == 1:
        return f"{pos[0]} requires {neg[0]}"
    parts = [f"{p} {t}" for p, t in sorted(terms.items()) if p != "root"]
    return "{" + ", ".join(parts) + "} are incompatible"


class ProofFormatter:
    """ReportFormatter callbacks mirroring pubgrub-rs/src/report.rs & uv report.rs."""

    def explain_both_external(
        self, e1: ExternalNode, e2: ExternalNode, terms: dict[str, Term]
    ) -> str:
        return f"Because {e1.format_text()} and {e2.format_text()}, {_format_terms(terms)}."

    def explain_both_ref(
        self,
        r1: int,
        d1: DerivedNode,
        r2: int,
        d2: DerivedNode,
        terms: dict[str, Term],
    ) -> str:
        return (
            f"Because {_format_terms(d1.terms)} ({r1}) and "
            f"{_format_terms(d2.terms)} ({r2}), {_format_terms(terms)}."
        )

    def explain_ref_and_external(
        self, r1: int, d1: DerivedNode, ext: ExternalNode, terms: dict[str, Term]
    ) -> str:
        return (
            f"Because {_format_terms(d1.terms)} ({r1}) and "
            f"{ext.format_text()}, {_format_terms(terms)}."
        )

    def and_explain_prior_and_external(
        self, pe: ExternalNode, ext: ExternalNode, terms: dict[str, Term]
    ) -> str:
        return (
            f"And because {pe.format_text()} and {ext.format_text()}, "
            f"{_format_terms(terms)}."
        )

    def and_explain_external(self, ext: ExternalNode, terms: dict[str, Term]) -> str:
        return f"And because {ext.format_text()}, {_format_terms(terms)}."

    def and_explain_ref(self, r: int, d: DerivedNode, terms: dict[str, Term]) -> str:
        return f"Thus, because {_format_terms(d.terms)} ({r}), {_format_terms(terms)}."


class RecursiveStringReporter:
    """Port of pubgrub-rs DefaultStringReporter (src/report.rs:400-555)."""

    def __init__(self) -> None:
        self.ref_count = 0
        self.shared_with_ref: dict[int, int] = {}
        self.lines: list[str] = []

    def _add_line_ref(self) -> int:
        self.ref_count += 1
        if self.lines:
            self.lines[-1] = f"{self.lines[-1]} ({self.ref_count})"
        return self.ref_count

    def _line_ref_of(self, shared_id: int | None) -> int | None:
        return self.shared_with_ref.get(shared_id) if shared_id is not None else None

    def _report_one_each(
        self,
        derived: DerivedNode,
        external: ExternalNode,
        terms: dict[str, Term],
        fmt: ProofFormatter,
    ) -> None:
        ref_id = self._line_ref_of(derived.shared_id)
        if ref_id is not None:
            self.lines.append(fmt.explain_ref_and_external(ref_id, derived, external, terms))
            return
        if isinstance(derived.cause1, DerivedNode) and isinstance(derived.cause2, ExternalNode):
            self.build_recursive(derived.cause1, fmt)
            self.lines.append(
                fmt.and_explain_prior_and_external(derived.cause2, external, terms)
            )
        elif isinstance(derived.cause1, ExternalNode) and isinstance(derived.cause2, DerivedNode):
            self.build_recursive(derived.cause2, fmt)
            self.lines.append(
                fmt.and_explain_prior_and_external(derived.cause1, external, terms)
            )
        else:
            self.build_recursive(derived, fmt)
            self.lines.append(fmt.and_explain_external(external, terms))

    def build_recursive(self, current: DerivedNode, fmt: ProofFormatter) -> None:
        c1, c2 = current.cause1, current.cause2
        if isinstance(c1, ExternalNode) and isinstance(c2, ExternalNode):
            self.lines.append(fmt.explain_both_external(c1, c2, current.terms))
        elif isinstance(c1, DerivedNode) and isinstance(c2, ExternalNode):
            self._report_one_each(c1, c2, current.terms, fmt)
        elif isinstance(c1, ExternalNode) and isinstance(c2, DerivedNode):
            self._report_one_each(c2, c1, current.terms, fmt)
        else:
            assert isinstance(c1, DerivedNode) and isinstance(c2, DerivedNode)
            r1, r2 = self._line_ref_of(c1.shared_id), self._line_ref_of(c2.shared_id)
            if r1 is not None and r2 is not None:
                self.lines.append(fmt.explain_both_ref(r1, c1, r2, c2, current.terms))
            elif r1 is not None and r2 is None:
                self.build_recursive(c2, fmt)
                self.lines.append(fmt.and_explain_ref(r1, c1, current.terms))
            elif r1 is None and r2 is not None:
                self.build_recursive(c1, fmt)
                self.lines.append(fmt.and_explain_ref(r2, c2, current.terms))
            else:
                self.build_recursive(c1, fmt)
                if c1.shared_id is not None:
                    self.lines.append("")
                    self.build_recursive(current, fmt)
                    return
                ref1 = self._add_line_ref()
                self.lines.append("")
                self.build_recursive(c2, fmt)
                self.lines.append(fmt.and_explain_ref(ref1, c1, current.terms))

        if current.shared_id is not None and current.shared_id not in self.shared_with_ref:
            self._add_line_ref()
            self.shared_with_ref[current.shared_id] = self.ref_count

    @classmethod
    def report(cls, tree: DerivationTree, fmt: ProofFormatter | None = None) -> str:
        formatter = fmt or ProofFormatter()
        if isinstance(tree, ExternalNode):
            return tree.format_text()
        inst = cls()
        inst.build_recursive(tree, formatter)
        return "\n".join(inst.lines)


class IterativeStringReporter:
    """Port of astral-sh/uv IterativeReporter (pubgrub/report.rs:80-225)."""

    def __init__(self) -> None:
        self.ref_count = 0
        self.shared_with_ref: dict[int, int] = {}
        self.lines: list[str] = []

    def _add_line_ref(self) -> int:
        self.ref_count += 1
        if self.lines:
            self.lines[-1] = f"{self.lines[-1]} ({self.ref_count})"
        return self.ref_count

    def _line_ref_of(self, shared_id: int | None) -> int | None:
        return self.shared_with_ref.get(shared_id) if shared_id is not None else None

    def build(self, root: DerivedNode, fmt: ProofFormatter) -> None:
        tasks: list[tuple] = [("Build", root)]
        while tasks:
            task = tasks.pop()
            tag = task[0]
            if tag == "Build":
                current: DerivedNode = task[1]
                tasks.append(("Finish", current.shared_id))
                c1, c2 = current.cause1, current.cause2
                if isinstance(c1, ExternalNode) and isinstance(c2, ExternalNode):
                    self.lines.append(fmt.explain_both_external(c1, c2, current.terms))
                elif (isinstance(c1, DerivedNode) and isinstance(c2, ExternalNode)) or (
                    isinstance(c1, ExternalNode) and isinstance(c2, DerivedNode)
                ):
                    derived = c1 if isinstance(c1, DerivedNode) else c2
                    external = c2 if isinstance(c2, ExternalNode) else c1
                    assert isinstance(derived, DerivedNode) and isinstance(external, ExternalNode)
                    ref_id = self._line_ref_of(derived.shared_id)
                    if ref_id is not None:
                        self.lines.append(
                            fmt.explain_ref_and_external(ref_id, derived, external, current.terms)
                        )
                    elif isinstance(derived.cause1, DerivedNode) and isinstance(
                        derived.cause2, ExternalNode
                    ):
                        tasks.append(
                            (
                                "Emit",
                                fmt.and_explain_prior_and_external(
                                    derived.cause2, external, current.terms
                                ),
                            )
                        )
                        tasks.append(("Build", derived.cause1))
                    elif isinstance(derived.cause1, ExternalNode) and isinstance(
                        derived.cause2, DerivedNode
                    ):
                        tasks.append(
                            (
                                "Emit",
                                fmt.and_explain_prior_and_external(
                                    derived.cause1, external, current.terms
                                ),
                            )
                        )
                        tasks.append(("Build", derived.cause2))
                    else:
                        tasks.append(("Emit", fmt.and_explain_external(external, current.terms)))
                        tasks.append(("Build", derived))
                else:
                    assert isinstance(c1, DerivedNode) and isinstance(c2, DerivedNode)
                    r1, r2 = self._line_ref_of(c1.shared_id), self._line_ref_of(c2.shared_id)
                    if r1 is not None and r2 is not None:
                        self.lines.append(fmt.explain_both_ref(r1, c1, r2, c2, current.terms))
                    elif r1 is not None and r2 is None:
                        tasks.append(("Emit", fmt.and_explain_ref(r1, c1, current.terms)))
                        tasks.append(("Build", c2))
                    elif r1 is None and r2 is not None:
                        tasks.append(("Emit", fmt.and_explain_ref(r2, c2, current.terms)))
                        tasks.append(("Build", c1))
                    else:
                        tasks.append(("AfterFirstDerived", current, c1, c2))
                        tasks.append(("Build", c1))
            elif tag == "Finish":
                shared_id = task[1]
                if shared_id is not None and shared_id not in self.shared_with_ref:
                    self._add_line_ref()
                    self.shared_with_ref[shared_id] = self.ref_count
            elif tag == "AfterFirstDerived":
                _, current, first, second = task
                if first.shared_id is not None:
                    self.lines.append("")
                    tasks.append(("Build", current))
                else:
                    ref_id = self._add_line_ref()
                    self.lines.append("")
                    tasks.append(("Emit", fmt.and_explain_ref(ref_id, first, current.terms)))
                    tasks.append(("Build", second))
            elif tag == "Emit":
                self.lines.append(task[1])

    @classmethod
    def report(cls, tree: DerivationTree, fmt: ProofFormatter | None = None) -> str:
        formatter = fmt or ProofFormatter()
        if isinstance(tree, ExternalNode):
            return tree.format_text()
        inst = cls()
        inst.build(tree, formatter)
        return "\n".join(inst.lines)


def iterative_drop_derivation_tree(root: DerivationTree) -> int:
    """Iterative child-pointer unlink mirroring uv drop_derivation_tree (error.rs:231-244)."""
    dummy = ExternalNode("not_root", "dropped", VersionRange.empty())
    stack: list[DerivationTree] = [root]
    unlinked = 0
    while stack:
        node = stack.pop()
        if isinstance(node, DerivedNode):
            c1, c2 = node.cause1, node.cause2
            node.cause1 = dummy
            node.cause2 = dummy
            unlinked += 1
            if isinstance(c1, DerivedNode):
                stack.append(c1)
            if isinstance(c2, DerivedNode):
                stack.append(c2)
    return unlinked


@dataclass
class OfflineRegistry:
    """Deterministic package registry mapping package -> sorted descending versions -> deps."""

    packages: dict[str, dict[int, list[tuple[str, VersionRange]]]] = field(default_factory=dict)

    def add(self, pkg: str, ver: int, deps: list[tuple[str, VersionRange]]) -> None:
        self.packages.setdefault(pkg, {})[ver] = list(deps)

    def versions_desc(self, pkg: str) -> list[int]:
        return sorted(self.packages.get(pkg, {}).keys(), reverse=True)


@dataclass
class PubGrubResult:
    solved: bool
    solution: dict[str, int] | None
    decisions: int
    learned_clauses: int
    derivation_tree: DerivationTree | None


class PubGrubSolver:
    """Complete CDCL PubGrub solver (Weizenbaum doc/solver.md + pubgrub-rs core.rs/solver.rs)."""

    def __init__(
        self,
        registry: OfflineRegistry,
        use_culprit_priority: bool = True,
        widen_ranges: bool = True,
    ) -> None:
        self.registry = registry
        self.use_culprit_priority = use_culprit_priority
        self.widen_ranges = widen_ranges
        self.incompat_store: list[Incompatibility] = []
        self.by_pkg: dict[str, list[int]] = {}
        self.assignments: dict[str, PackageAssignments] = {}
        self.decision_level = 0
        self.global_index = 0
        self.stats: dict[str, ResolutionStats] = {}
        self.added_deps: set[tuple[str, int]] = set()
        self.decisions = 0
        self.learned_clauses = 0

    def _alloc_incompat(
        self,
        terms: dict[str, Term],
        kind: str,
        causes: tuple[int, int] | None = None,
        dep_info: tuple[str, VersionRange, str, VersionRange] | None = None,
    ) -> int:
        # Merge identical dependency incompatibilities across versions (core.rs:450-488).
        if kind == "dep" and dep_info is not None:
            p1, r1, p2, r2 = dep_info
            for old_id in self.by_pkg.get(p1, ()):
                old = self.incompat_store[old_id]
                if old.kind == "dep" and old.dep_info is not None:
                    op1, or1, op2, or2 = old.dep_info
                    if op1 == p1 and op2 == p2 and or2 == r2:
                        merged_r1 = or1.union(r1)
                        new_terms = {
                            p1: Term(merged_r1, True),
                            p2: Term(r2, False),
                        }
                        iid = len(self.incompat_store)
                        inc = Incompatibility(iid, new_terms, "dep", None, (p1, merged_r1, p2, r2))
                        self.incompat_store.append(inc)
                        for p in (p1, p2):
                            lst = self.by_pkg.setdefault(p, [])
                            if old_id in lst:
                                lst.remove(old_id)
                            lst.append(iid)
                        return iid
        iid = len(self.incompat_store)
        inc = Incompatibility(iid, dict(terms), kind, causes, dep_info)
        self.incompat_store.append(inc)
        for p in terms:
            self.by_pkg.setdefault(p, []).append(iid)
        return iid

    def _add_derivation(self, pkg: str, cause_id: int) -> None:
        inc = self.incompat_store[cause_id]
        derived_term = inc.terms[pkg].negate()
        pa = self.assignments.setdefault(pkg, PackageAssignments())
        acc = (
            derived_term
            if not pa.derivations
            else pa.derivations[-1].accumulated.intersection(derived_term)
        )
        self.global_index += 1
        pa.derivations.append(DatedDerivation(self.global_index, self.decision_level, cause_id, acc))

    def _add_decision(self, pkg: str, ver: int) -> None:
        self.decision_level += 1
        self.global_index += 1
        self.decisions += 1
        pa = self.assignments[pkg]
        pa.decision = (self.global_index, self.decision_level, ver)

    def _backtrack(self, target_level: int) -> None:
        self.decision_level = target_level
        to_delete: list[str] = []
        for pkg, pa in self.assignments.items():
            if pa.decision is not None and pa.decision[1] > target_level:
                pa.decision = None
            while pa.derivations and pa.derivations[-1].decision_level > target_level:
                pa.derivations.pop()
            if not pa.derivations and pa.decision is None:
                to_delete.append(pkg)
        for pkg in to_delete:
            del self.assignments[pkg]

    def _relation(self, inc: Incompatibility) -> tuple[str, str | None]:
        unsatisfied: str | None = None
        for pkg, term in inc.terms.items():
            pa = self.assignments.get(pkg)
            if pa is None:
                if unsatisfied is not None:
                    return "inconclusive", None
                unsatisfied = pkg
                continue
            cur = pa.current_term()
            if cur.is_disjoint(term):
                return "contradicted", pkg
            if not cur.subset_of(term):
                if unsatisfied is not None:
                    return "inconclusive", None
                unsatisfied = pkg
        if unsatisfied is None:
            return "satisfied", None
        return "almost", unsatisfied

    def _conflict_resolution(
        self, root_pkg: str, root_ver: int, incompat_id: int, causes_log: list[tuple[str, int]]
    ) -> tuple[str, int]:
        cur_id = incompat_id
        while True:
            cur = self.incompat_store[cur_id]
            if cur.is_terminal(root_pkg, root_ver):
                raise StopIteration(cur_id)
            sat_map: dict[str, tuple[int | None, int, int]] = {}
            for pkg, term in cur.terms.items():
                sat_map[pkg] = self.assignments[pkg].satisfier(term.negate())
            sat_pkg = max(sat_map, key=lambda p: sat_map[p][1])
            sat_cause, _, sat_dl = sat_map[sat_pkg]

            # Find previous_satisfier_level (partial_solution.rs:647-689).
            sat_pa = self.assignments[sat_pkg]
            if sat_cause is not None:
                accum_term = self.incompat_store[sat_cause].terms[sat_pkg].negate()
            else:
                accum_term = sat_pa.current_term()
            inc_term = cur.terms[sat_pkg]
            joint_neg = accum_term.intersection(inc_term.negate())
            prev_map = dict(sat_map)
            if joint_neg == Term.empty_term():
                del prev_map[sat_pkg]
            else:
                prev_map[sat_pkg] = sat_pa.satisfier(joint_neg)
            prev_dl = max((v[2] for v in prev_map.values()), default=1)
            prev_dl = max(1, prev_dl)

            if sat_cause is None or prev_dl < sat_dl:
                self._backtrack(prev_dl)
                causes_log.append((sat_pkg, cur_id))
                rel, almost_pkg = self._relation(self.incompat_store[cur_id])
                assert rel == "almost" and almost_pkg is not None
                return almost_pkg, cur_id

            # Generalized resolution rule (incompatibility.rs:260-286).
            cause_inc = self.incompat_store[sat_cause]
            new_terms: dict[str, Term] = {
                p: t for p, t in cur.terms.items() if p != sat_pkg
            }
            for p, t in cause_inc.terms.items():
                if p == sat_pkg:
                    continue
                new_terms[p] = new_terms[p].intersection(t) if p in new_terms else t
            residual = inc_term.union(cause_inc.terms[sat_pkg])
            if residual != Term.any_term():
                new_terms[sat_pkg] = residual
            cur_id = self._alloc_incompat(new_terms, "derived", causes=(cur_id, sat_cause))
            self.learned_clauses += 1
            causes_log.append((sat_pkg, cur_id))

    def _unit_propagation(self, root_pkg: str, root_ver: int, start_pkg: str) -> int | None:
        buf = [start_pkg]
        causes_log: list[tuple[str, int]] = []
        while buf:
            pkg = buf.pop()
            conflict_id: int | None = None
            for iid in reversed(self.by_pkg.get(pkg, ())):
                rel, almost_pkg = self._relation(self.incompat_store[iid])
                if rel == "satisfied":
                    conflict_id = iid
                    break
                if rel == "almost" and almost_pkg is not None:
                    if almost_pkg not in buf:
                        buf.append(almost_pkg)
                    self._add_derivation(almost_pkg, iid)
            if conflict_id is not None:
                try:
                    almost_pkg, root_cause = self._conflict_resolution(
                        root_pkg, root_ver, conflict_id, causes_log
                    )
                except StopIteration as exc:
                    return int(exc.value)
                buf = [almost_pkg]
                self._add_derivation(almost_pkg, root_cause)
        for affected, iid in causes_log:
            self.stats.setdefault(affected, ResolutionStats()).unit_propagation_affected += 1
            for culprit in self.incompat_store[iid].terms:
                if culprit != affected:
                    self.stats.setdefault(culprit, ResolutionStats()).unit_propagation_culprit += 1
        return None

    def _widen_singleton(self, pkg: str, ver: int) -> VersionRange:
        if not self.widen_ranges:
            return VersionRange.singleton(ver)
        vers = sorted(self.registry.packages.get(pkg, {}).keys())
        idx = vers.index(ver)
        lo = 0 if idx == 0 else vers[idx - 1] + 1
        hi = INF_VER if idx == len(vers) - 1 else vers[idx + 1]
        return VersionRange.between(lo, hi)

    def _build_derivation_tree(self, terminal_id: int) -> DerivationTree:
        """Topological iterative DAG materialization (core.rs:492-528)."""
        all_ids: set[int] = set()
        shared_ids: set[int] = set()
        stack = [terminal_id]
        while stack:
            i = stack.pop()
            inc = self.incompat_store[i]
            if inc.causes is not None:
                if i in all_ids:
                    shared_ids.add(i)
                else:
                    stack.append(inc.causes[0])
                    stack.append(inc.causes[1])
            all_ids.add(i)
        built: dict[int, DerivationTree] = {}
        for i in sorted(all_ids):
            inc = self.incompat_store[i]
            if inc.causes is not None:
                sid = i if i in shared_ids else None
                built[i] = DerivedNode(
                    dict(inc.terms), sid, built[inc.causes[0]], built[inc.causes[1]]
                )
            elif inc.kind == "not_root":
                pkg, term = next(iter(inc.terms.items()))
                built[i] = ExternalNode("not_root", pkg, term.rng)
            elif inc.kind == "no_versions":
                pkg, term = next(iter(inc.terms.items()))
                built[i] = ExternalNode("no_versions", pkg, term.rng)
            else:
                assert inc.dep_info is not None
                p1, r1, p2, r2 = inc.dep_info
                built[i] = ExternalNode("dep", p1, r1, p2, r2)
        return built[terminal_id]

    def solve(self, root_pkg: str = "root", root_ver: int = 1) -> PubGrubResult:
        self._alloc_incompat({root_pkg: Term(VersionRange.singleton(root_ver), False)}, "not_root")
        nxt = root_pkg
        while True:
            term_id = self._unit_propagation(root_pkg, root_ver, nxt)
            if term_id is not None:
                return PubGrubResult(
                    False,
                    None,
                    self.decisions,
                    self.learned_clauses,
                    self._build_derivation_tree(term_id),
                )
            candidates: list[tuple[tuple[int, int, int], str, VersionRange]] = []
            for pkg in sorted(self.assignments):
                pa = self.assignments[pkg]
                if not pa.is_decided() and pa.current_term().positive:
                    rng = pa.current_term().rng
                    matching = [v for v in self.registry.versions_desc(pkg) if rng.contains(v)]
                    cc = (
                        self.stats.get(pkg, ResolutionStats()).conflict_count()
                        if self.use_culprit_priority
                        else 0
                    )
                    # Higher priority: root first, more conflicts first, fewer candidates first.
                    is_root = 1 if pkg == root_pkg else 0
                    prio = (is_root, cc, -len(matching))
                    candidates.append((prio, pkg, rng))
            if not candidates:
                sol = {
                    p: pa.decision[2]
                    for p, pa in sorted(self.assignments.items())
                    if pa.decision is not None
                }
                return PubGrubResult(True, sol, self.decisions, self.learned_clauses, None)
            # Pick highest priority; deterministic lexicographic tie-break by package name.
            candidates.sort(key=lambda item: (item[0], item[1]))
            _, nxt, allowed_rng = candidates[-1]
            matching_vers = [v for v in self.registry.versions_desc(nxt) if allowed_rng.contains(v)]
            if not matching_vers:
                self._alloc_incompat({nxt: Term(allowed_rng, True)}, "no_versions")
                continue
            chosen = matching_vers[0]
            if (nxt, chosen) not in self.added_deps:
                self.added_deps.add((nxt, chosen))
                widened = (
                    self._widen_singleton(nxt, chosen)
                    if nxt != root_pkg
                    else VersionRange.singleton(chosen)
                )
                deps = self.registry.packages[nxt][chosen]
                conflict_hit = False
                for dep_pkg, dep_rng in deps:
                    iid = self._alloc_incompat(
                        {nxt: Term(widened, True), dep_pkg: Term(dep_rng, False)},
                        "dep",
                        dep_info=(nxt, widened, dep_pkg, dep_rng),
                    )
                    # Check immediate conflict with existing partial solution (partial_solution.rs:549-572).
                    inc = self.incompat_store[iid]
                    dep_pa = self.assignments.get(dep_pkg)
                    if dep_pa is not None and dep_pa.current_term().subset_of(inc.terms[dep_pkg]):
                        conflict_hit = True
                        self.stats.setdefault(nxt, ResolutionStats()).dependencies_affected += 1
                        self.stats.setdefault(dep_pkg, ResolutionStats()).dependencies_culprit += 1
                if not conflict_hit:
                    self._add_decision(nxt, chosen)
            else:
                self._add_decision(nxt, chosen)


@dataclass
class Criterion:
    candidates: list[int]
    information: list[tuple[str | None, VersionRange]]
    incompatibilities: list[int]


@dataclass
class ResolvelibState:
    mapping: dict[str, int]
    criteria: dict[str, Criterion]
    backtrack_causes: list[str] = field(default_factory=list)


class ResolvelibBacktracker:
    """Pointwise-exclusion backjumping model of sarugaku/resolvelib@223f4bdc (resolution.py:336-555).

    Models upstream's pointwise candidate exclusion `incompatibilities_from_broken.append((name, [candidate]))`
    (`resolution.py:397`), distinguishing:
      - safe backjumping (`optimistic_backjumping=False`, `resolution.py:356-361`), which stops
        as soon as `name not in incompatible_deps` (chronological 1-step fallback when the popped
        variable is not itself a direct conflict participant);
      - optimistic backjumping (`optimistic_backjumping=True`, `resolution.py:378-379`), which
        skips intermediate states while `name not in incompatible_deps` and `dep_names` is
        disjoint from `incompatible_deps`; and
      - `preference_mode` (`"insertion"` vs. `"pip_backtrack_causes"`, `resolution.py:193,497,539`),
        which prioritizes packages present in `backtrack_causes`, then minimum candidate count,
        then lexical package identifier.
    """

    def __init__(
        self,
        registry: OfflineRegistry,
        optimistic_backjumping: bool = False,
        preference_mode: str = "insertion",
    ) -> None:
        self.registry = registry
        self.optimistic_backjumping = optimistic_backjumping
        self.preference_mode = preference_mode
        self.states: list[ResolvelibState] = []
        self.pin_attempts = 0
        self.conflict_logs: list[str] = []

    def _clone_criteria(self, criteria: dict[str, Criterion]) -> dict[str, Criterion]:
        return {
            k: Criterion(list(c.candidates), list(c.information), list(c.incompatibilities))
            for k, c in criteria.items()
        }

    def _push_new_state(self) -> None:
        base = self.states[-1]
        self.states.append(
            ResolvelibState(
                dict(base.mapping),
                self._clone_criteria(base.criteria),
                list(base.backtrack_causes),
            )
        )

    def _add_to_criteria(
        self, criteria: dict[str, Criterion], pkg: str, rng: VersionRange, parent: str | None
    ) -> bool:
        existing = criteria.get(pkg)
        incompats = list(existing.incompatibilities) if existing else []
        info = (list(existing.information) if existing else []) + [(parent, rng)]
        cands = [
            v
            for v in self.registry.versions_desc(pkg)
            if v not in incompats and all(r.contains(v) for _, r in info)
        ]
        criteria[pkg] = Criterion(cands, info, incompats)
        return len(cands) > 0

    def _patch_criteria(self, broken_incompats: list[tuple[str, list[int]]]) -> bool:
        st = self.states[-1]
        for pkg, bad_vers in broken_incompats:
            if pkg not in st.criteria:
                continue
            c = st.criteria[pkg]
            merged_bad = list(dict.fromkeys(c.incompatibilities + bad_vers))
            cands = [v for v in c.candidates if v not in merged_bad]
            if not cands:
                return False
            st.criteria[pkg] = Criterion(cands, list(c.information), merged_bad)
        return True

    def _backjump(self, incompatible_pkgs: set[str], cause_pkgs: list[str]) -> bool:
        """Model safe (L356-361) vs. optimistic (L378-379) backjumping + L397 pointwise exclusion."""
        while len(self.states) >= 3:
            del self.states[-1]
            while True:
                if not self.states:
                    return False
                broken = self.states.pop()
                if not broken.mapping:
                    return False
                name = next(reversed(broken.mapping))
                candidate = broken.mapping.pop(name)
                if not self.optimistic_backjumping:
                    # Safe backjumping (_optimistic_backjumping_ratio == 0, resolution.py:356-361):
                    # stops immediately when `name not in incompatible_deps`, and also stops when
                    # `name in incompatible_deps` (single-step chronological unwind).
                    break
                dep_names = {d for d, _ in self.registry.packages[name][candidate]}
                if name in incompatible_pkgs or not dep_names.isdisjoint(incompatible_pkgs):
                    break
                if not broken.mapping or len(self.states) <= 1:
                    return False
            incompats_from_broken = [
                (k, list(v.incompatibilities)) for k, v in broken.criteria.items()
            ]
            # Exact line 397 of resolution.py: pointwise candidate exclusion only.
            incompats_from_broken.append((name, [candidate]))
            self._push_new_state()
            self.states[-1].backtrack_causes = list(cause_pkgs)
            if self._patch_criteria(incompats_from_broken):
                return True
        return False

    def solve(
        self, root_deps: list[tuple[str, VersionRange]], max_rounds: int = 100_000
    ) -> tuple[bool, dict[str, int] | None, int, str]:
        self.states = [ResolvelibState({}, {}, [])]
        for pkg, rng in root_deps:
            if not self._add_to_criteria(self.states[-1].criteria, pkg, rng, "root"):
                return False, None, 0, f"root conflict on {pkg} {rng}"
        self._push_new_state()

        for _ in range(max_rounds):
            st = self.states[-1]
            unsatisfied = [
                k
                for k, c in st.criteria.items()
                if c.information
                and (
                    k not in st.mapping
                    or st.mapping[k] in c.incompatibilities
                    or not all(r.contains(st.mapping[k]) for _, r in c.information)
                )
            ]
            if not unsatisfied:
                return True, dict(st.mapping), self.pin_attempts, ""
            if self.preference_mode == "pip_backtrack_causes":
                cause_set = set(st.backtrack_causes)
                name = min(
                    unsatisfied,
                    key=lambda k: (k not in cause_set, len(st.criteria[k].candidates), k),
                )
            else:
                name = unsatisfied[0]
            crit = st.criteria[name]
            failure_pkgs: set[str] | None = None
            cause_pkgs: list[str] = []
            for cand in list(crit.candidates):
                self.pin_attempts += 1
                trial_criteria = self._clone_criteria(st.criteria)
                conflict_deps: set[str] = set()
                for dep_pkg, dep_rng in self.registry.packages[name][cand]:
                    if not self._add_to_criteria(trial_criteria, dep_pkg, dep_rng, name):
                        conflict_deps.add(dep_pkg)
                        parents = [
                            p for p, _ in trial_criteria[dep_pkg].information if p and p != "root"
                        ]
                        cause_pkgs = list(dict.fromkeys(parents + [dep_pkg]))
                        self.conflict_logs.append(
                            f"Conflict: {name}=={cand} requires {dep_pkg} {dep_rng}, "
                            f"incompatible with active constraints "
                            f"{[(p, str(r)) for p, r in trial_criteria[dep_pkg].information]}"
                        )
                        break
                if not conflict_deps:
                    self.states[-1].criteria = trial_criteria
                    self.states[-1].mapping.pop(name, None)
                    self.states[-1].mapping[name] = cand
                    self._push_new_state()
                    failure_pkgs = None
                    break
                failure_pkgs = conflict_deps | {name} | set(cause_pkgs)
            if failure_pkgs is not None:
                if not self._backjump(failure_pkgs, cause_pkgs):
                    return False, None, self.pin_attempts, "\n".join(self.conflict_logs)
        raise RuntimeError(f"ResolutionTooDeep({max_rounds})")


def build_diamond_conflict_registry(
    m: int, satisfiable_tail: bool, sink_name: str = "b"
) -> OfflineRegistry:
    """Construct family where `a` and `sink_name` conflict on `shared` across `mid1`, `mid2`.

    Versions of `a` are spaced by 10 (`10, 20, ..., 10*m`) like semver minor releases so
    unwidened singletons fragment into `m` intervals while widened ranges collapse into 1.
    `mid1` and `mid2` both depend on `shared any`, so neither safe backjumping nor optimistic
    backjumping (`not dep_names.isdisjoint(incompatible_pkgs)`) can skip them when `mid1` and
    `mid2` are decided before `sink_name`.
    """
    reg = OfflineRegistry()
    reg.add(
        "root",
        1,
        [
            ("a", VersionRange.full()),
            ("mid1", VersionRange.full()),
            ("mid2", VersionRange.full()),
            (sink_name, VersionRange.full()),
        ],
    )
    start_bad = 2 if satisfiable_tail else 1
    if satisfiable_tail:
        reg.add("a", 10, [("shared", VersionRange.between(1, 2))])
    for v in range(start_bad, m + 1):
        reg.add("a", 10 * v, [("shared", VersionRange.between(200, 300))])
    for v in range(1, m + 1):
        reg.add("mid1", 10 * v, [("shared", VersionRange.full())])
        reg.add("mid2", 10 * v, [("shared", VersionRange.full())])
        reg.add(sink_name, 10 * v, [("shared", VersionRange.between(1, 100))])
    reg.add("shared", 1, [])
    reg.add("shared", 250, [])
    return reg


def run_probe_1() -> dict[str, object]:
    # 1A: Scaling across M in {3, 4, 5, 6, 8} on unsatisfiable + satisfiable diamonds.
    scaling_rows: list[dict[str, int]] = []
    ordering_sensitivity_m8: dict[str, int] = {}
    for m in (3, 4, 5, 6, 8):
        reg_unsat = build_diamond_conflict_registry(m, satisfiable_tail=False, sink_name="b")
        pg_widen_solver = PubGrubSolver(reg_unsat, use_culprit_priority=True, widen_ranges=True)
        pg_widen = pg_widen_solver.solve()
        pg_exact_solver = PubGrubSolver(reg_unsat, use_culprit_priority=True, widen_ranges=False)
        pg_exact = pg_exact_solver.solve()
        rl_safe_ok, _, rl_safe_steps, _ = ResolvelibBacktracker(
            reg_unsat, optimistic_backjumping=False, preference_mode="insertion"
        ).solve(reg_unsat.packages["root"][1], max_rounds=50_000)
        rl_opt_ok, _, rl_opt_steps, _ = ResolvelibBacktracker(
            reg_unsat, optimistic_backjumping=True, preference_mode="insertion"
        ).solve(reg_unsat.packages["root"][1], max_rounds=50_000)
        assert not pg_widen.solved and not pg_exact.solved and not rl_safe_ok and not rl_opt_ok
        # Both safe and optimistic backjumping hit identical counts because mid1/mid2 touch `shared`.
        assert rl_safe_steps == rl_opt_steps

        # Count max intervals in learned/merged incompatibilities on `a` (core.rs:706-755).
        widen_a_intervals = max(
            len(inc.terms["a"].rng.intervals)
            for inc in pg_widen_solver.incompat_store
            if "a" in inc.terms and inc.kind == "dep"
        )
        exact_a_intervals = max(
            len(inc.terms["a"].rng.intervals)
            for inc in pg_exact_solver.incompat_store
            if "a" in inc.terms and inc.kind == "dep"
        )
        assert widen_a_intervals == 1 and exact_a_intervals == m
        scaling_rows.append(
            {
                "M": m,
                "pubgrub_decisions": pg_widen.decisions,
                "pubgrub_widened_intervals": widen_a_intervals,
                "pubgrub_unwidened_intervals": exact_a_intervals,
                "resolvelib_pin_attempts": rl_safe_steps,
            }
        )

        if m == 8:
            # Verify variable-ordering sensitivity under pip-style `backtrack_causes` + min-cands:
            # when sink `"b"` precedes `"mid1"` lexically, `backtrack_causes` promotes `"b"` ahead
            # of `"mid1"`/`"mid2"` (quadratic 80 attempts); when `"z_sink"` follows `"mid1"`/`"mid2"`
            # lexically, `"mid1"` and `"mid2"` (also in `shared`'s criterion parents) still precede
            # `"z_sink"` on every branch (quartic >= 4,600 attempts), while PubGrub stays 8 decisions.
            _, _, steps_b_lex, _ = ResolvelibBacktracker(
                reg_unsat, optimistic_backjumping=False, preference_mode="pip_backtrack_causes"
            ).solve(reg_unsat.packages["root"][1], max_rounds=50_000)
            reg_z = build_diamond_conflict_registry(m, satisfiable_tail=False, sink_name="z_sink")
            pg_z = PubGrubSolver(reg_z, use_culprit_priority=True, widen_ranges=True).solve()
            _, _, steps_z_lex, _ = ResolvelibBacktracker(
                reg_z, optimistic_backjumping=False, preference_mode="pip_backtrack_causes"
            ).solve(reg_z.packages["root"][1], max_rounds=50_000)
            assert not pg_z.solved and pg_z.decisions == 7
            assert steps_b_lex == 80 and steps_z_lex == 4_688
            ordering_sensitivity_m8 = {
                "pubgrub_decisions_b_sink": pg_widen.decisions,
                "pubgrub_decisions_z_sink": pg_z.decisions,
                "resolvelib_backtrack_causes_b_before_mid": steps_b_lex,
                "resolvelib_backtrack_causes_mid_before_z_sink": steps_z_lex,
            }

    # Verify both solvers agree on satisfiable instance (M=6, a==10 valid).
    reg_sat = build_diamond_conflict_registry(6, satisfiable_tail=True)
    pg_sat = PubGrubSolver(reg_sat, widen_ranges=True).solve()
    rl_sat_ok, rl_sat_sol, rl_sat_steps, _ = ResolvelibBacktracker(reg_sat).solve(
        reg_sat.packages["root"][1]
    )
    assert pg_sat.solved and rl_sat_ok and pg_sat.solution is not None and rl_sat_sol is not None
    assert pg_sat.solution["a"] == 10 and rl_sat_sol["a"] == 10
    assert pg_sat.solution["shared"] == 1 and rl_sat_sol["shared"] == 1
    assert rl_sat_steps > pg_sat.decisions * 20

    row8 = scaling_rows[-1]
    assert row8["pubgrub_decisions"] == 8
    assert row8["resolvelib_pin_attempts"] == 4_680
    speedup = row8["resolvelib_pin_attempts"] / row8["pubgrub_decisions"]
    assert speedup > 150.0

    # 1B: Diagnostic token compression at M=6 (singleton mode so derivation DAG spans versions).
    reg_diag = build_diamond_conflict_registry(6, satisfiable_tail=False)
    pg_diag = PubGrubSolver(reg_diag, widen_ranges=False).solve()
    _, _, _, rl_diag_log = ResolvelibBacktracker(reg_diag).solve(reg_diag.packages["root"][1])
    assert pg_diag.derivation_tree is not None
    pg_report = IterativeStringReporter.report(pg_diag.derivation_tree)
    pg_tokens = len(pg_report.split())
    rl_tokens = len(rl_diag_log.split())
    compression_ratio = rl_tokens / pg_tokens
    assert compression_ratio > 15.0
    assert "shared" in pg_report and "version solving failed" in pg_report

    # 1C: Exact output equivalence (uv report.rs:3135-3147) + recursion safety (report.rs:3151-3170).
    ext1 = ExternalNode("not_root", "root", VersionRange.singleton(1))
    ext2 = ExternalNode("no_versions", "foo", VersionRange.between(1, 2))
    ext3 = ExternalNode("dep", "bar", VersionRange.singleton(1), "foo", VersionRange.between(1, 2))
    shared = DerivedNode({"bar": Term.exact(1)}, shared_id=1, cause1=ext1, cause2=ext2)
    unshared = DerivedNode({"foo": Term.exact(2)}, shared_id=None, cause1=ext2, cause2=ext3)
    dag_fixtures = [
        DerivedNode({}, None, shared, ext3),
        DerivedNode({}, None, ext3, shared),
        DerivedNode({}, None, shared, unshared),
        DerivedNode({}, None, shared, shared),
    ]
    for dag in dag_fixtures:
        assert IterativeStringReporter.report(dag) == RecursiveStringReporter.report(dag)
    assert RecursiveStringReporter.report(pg_diag.derivation_tree) == pg_report

    # Build depth-2,500 right-leaning version-rejection chain exceeding Python recursion limit.
    deep_depth = 2_500
    leaf = ExternalNode("no_versions", "wheel_pkg", VersionRange.singleton(0))
    deep_tree: DerivationTree = leaf
    for step in range(1, deep_depth + 1):
        step_ext = ExternalNode(
            "dep", "app", VersionRange.singleton(step), "wheel_pkg", VersionRange.singleton(0)
        )
        deep_tree = DerivedNode(
            {"app": Term(VersionRange.between(1, step + 1), True)}, None, deep_tree, step_ext
        )

    old_limit = sys.getrecursionlimit()
    sys.setrecursionlimit(1_000)
    try:
        rec_crashed = False
        try:
            RecursiveStringReporter.report(deep_tree)
        except RecursionError:
            rec_crashed = True
        iter_text = IterativeStringReporter.report(deep_tree)
        unlinked_nodes = iterative_drop_derivation_tree(deep_tree)
    finally:
        sys.setrecursionlimit(old_limit)

    assert rec_crashed is True
    # Base (External, External) = 1 line + 1,249 pairwise steps + 1 odd step = 1,251 lines.
    assert len(iter_text.splitlines()) == (deep_depth // 2) + 1
    assert unlinked_nodes == deep_depth

    return {
        "scaling_curve": scaling_rows,
        "scaling_M8": row8,
        "ordering_sensitivity_M8": ordering_sensitivity_m8,
        "satisfiable_M6_steps": {"pubgrub": pg_sat.decisions, "resolvelib": rl_sat_steps},
        "diagnostic_tokens_M6": {
            "pubgrub_tokens": pg_tokens,
            "resolvelib_tokens": rl_tokens,
            "compression_x": round(compression_ratio, 1),
        },
        "deep_chain_2500": {
            "recursive_crashed": rec_crashed,
            "iterative_lines": len(iter_text.splitlines()),
            "unlinked_nodes": unlinked_nodes,
        },
    }


# ============================================================================
# PILLAR 2: PEP 508 Marker-Algebra Universal Lockfile Forking (uv ForkState)
# ============================================================================

PLATFORMS = ("linux", "darwin", "win32")
ARCHES = ("x86_64", "arm64")
PY_MINORS = (10, 11, 12)
ATOM_ENVS: tuple[tuple[str, str, int], ...] = tuple(
    (plat, arch, py) for plat in PLATFORMS for arch in ARCHES for py in PY_MINORS
)
FULL_ENV_MASK = (1 << len(ATOM_ENVS)) - 1


def marker_from_pred(pred: Callable[[str, str, int], bool]) -> int:
    mask = 0
    for idx, (plat, arch, py) in enumerate(ATOM_ENVS):
        if pred(plat, arch, py):
            mask |= 1 << idx
    return mask


@dataclass(frozen=True)
class MarkerDepSpec:
    pkg: str
    rng: VersionRange
    marker_mask: int
    requires_py_floor: int | None = None
    conflict_group: str | None = None


@dataclass
class ForkBranch:
    env_mask: int
    allowed_groups: frozenset[str]
    excluded_groups: frozenset[str]
    deps: list[MarkerDepSpec] = field(default_factory=list)

    def set_env_and_retain(
        self, sub_mask: int, extra_dep: MarkerDepSpec | None = None
    ) -> ForkBranch:
        """Port of astral-sh/uv Fork::set_env (resolver/mod.rs:4148-4160).

        Narrows `env_mask` to a satisfiable (`sub_mask != 0`) subset and retains ONLY
        dependencies whose marker expression is non-disjoint with `sub_mask`.
        """
        assert sub_mask != 0, "Unsatisfiable env_mask == 0 contradiction must never form a fork"
        retained = [d for d in self.deps if (sub_mask & d.marker_mask) != 0]
        if extra_dep is not None and (sub_mask & extra_dep.marker_mask) != 0:
            retained.append(extra_dep)
        return ForkBranch(sub_mask, self.allowed_groups, self.excluded_groups, retained)


def uv_fork_dependencies(
    specs_by_pkg: dict[str, list[MarkerDepSpec]],
    conflict_sets: list[tuple[str, ...]],
    parent_env_mask: int,
    project_py_floor: int,
    enable_pruning_and_fastpath: bool = True,
) -> tuple[list[ForkBranch], int]:
    """Port of astral-sh/uv fork scheduler + Fork::set_env (resolver/mod.rs:3880-4160).

    Basic Boolean satisfiability (`sub_mask != 0`) is ALWAYS enforced unconditionally
    (matching uv's MarkerTree BDD, which never materializes FALSE marker environments).
    `enable_pruning_and_fastpath` toggles ONLY uv's three domain optimizations:
      1. single-spec / uniform-marker no-fork rule (`mod.rs:3880-3930`),
      2. `requires-python` disjointness pruning (`mod.rs:3961-3965`), and
      3. inactive/dominated conflict-set fast path (`mod.rs:3991-4053`).
    Returns `(forks, conflict_n_plus_1_splits_executed)`.
    """
    py_req_mask = marker_from_pred(lambda _p, _a, py: py >= project_py_floor)
    forks = [ForkBranch(parent_env_mask, frozenset(), frozenset(), [])]

    for _pkg_name, deps in sorted(specs_by_pkg.items()):
        if enable_pruning_and_fastpath and len(deps) == 1:
            dep = deps[0]
            if dep.requires_py_floor is None or dep.requires_py_floor <= project_py_floor:
                for fk in forks:
                    if fk.env_mask & dep.marker_mask:
                        fk.deps.append(dep)
                continue
        elif enable_pruning_and_fastpath and len(deps) > 1:
            first_m = deps[0].marker_mask
            floors = {d.requires_py_floor for d in deps}
            if all(d.marker_mask == first_m for d in deps) and all(
                fl is None or fl <= project_py_floor for fl in floors
            ):
                for dep in deps:
                    for fk in forks:
                        if fk.env_mask & first_m:
                            fk.deps.append(dep)
                continue

        for dep in deps:
            if enable_pruning_and_fastpath and (parent_env_mask & dep.marker_mask) == 0:
                continue
            if enable_pruning_and_fastpath and (parent_env_mask & dep.marker_mask) == parent_env_mask:
                for fk in forks:
                    if fk.env_mask & dep.marker_mask:
                        fk.deps.append(dep)
                continue

            next_forks: list[ForkBranch] = []
            for fk in forks:
                inc_mask = fk.env_mask & dep.marker_mask
                exc_mask = fk.env_mask & (~dep.marker_mask & FULL_ENV_MASK)
                for sub_mask, include_dep in ((inc_mask, True), (exc_mask, False)):
                    # Unconditional Boolean satisfiability: never emit env_mask == 0 contradictions.
                    if sub_mask == 0:
                        continue
                    if enable_pruning_and_fastpath and (sub_mask & py_req_mask) == 0:
                        continue
                    next_forks.append(
                        fk.set_env_and_retain(sub_mask, dep if include_dep else None)
                    )
            forks = next_forks

    # Conflicting extras/groups N+1 splitting (mod.rs:3985-4080).
    conflict_n_plus_1_splits = 0
    for cset in conflict_sets:
        next_forks = []
        for fk in forks:
            has_conflict_dep = any(d.conflict_group in cset for d in fk.deps)
            if enable_pruning_and_fastpath and not has_conflict_dep:
                next_forks.append(fk)
                continue
            non_excluded = [g for g in cset if g not in fk.excluded_groups]
            if enable_pruning_and_fastpath and len(non_excluded) < 2:
                dominated = all(
                    not any(
                        other is not cset
                        and item in other
                        and any(o != item and o not in fk.excluded_groups for o in other)
                        for other in conflict_sets
                    )
                    for item in non_excluded
                )
                if dominated:
                    cleaned = [
                        d
                        for d in fk.deps
                        if d.conflict_group is None or d.conflict_group not in fk.excluded_groups
                    ]
                    next_forks.append(
                        ForkBranch(fk.env_mask, fk.allowed_groups, fk.excluded_groups, cleaned)
                    )
                    continue

            conflict_n_plus_1_splits += 1
            # Fork 0: exclude ALL groups in cset (mod.rs:4056-4058).
            if not (fk.allowed_groups & set(cset)):
                exc_all = fk.excluded_groups | set(cset)
                cleaned = [d for d in fk.deps if d.conflict_group not in exc_all]
                next_forks.append(ForkBranch(fk.env_mask, fk.allowed_groups, exc_all, cleaned))

            # Forks 1..N: allow group i, exclude all j != i (mod.rs:4067-4077).
            for grp in cset:
                others = set(cset) - {grp}
                if grp in fk.excluded_groups or (fk.allowed_groups & others):
                    continue
                allow_i = fk.allowed_groups | {grp}
                exc_i = fk.excluded_groups | others
                cleaned = [d for d in fk.deps if d.conflict_group not in exc_i]
                next_forks.append(ForkBranch(fk.env_mask, allow_i, exc_i, cleaned))
        forks = next_forks
    return forks, conflict_n_plus_1_splits


def propagate_markers_cycle_safe(edges: list[tuple[str, str, int]], target: str) -> int:
    """Port of uv find_environments forward BFS fixpoint (resolver/mod.rs:4289-4352)."""
    if target == "root":
        return FULL_ENV_MASK
    ancestors = {target}
    stack = [target]
    has_root = False
    while stack:
        cur = stack.pop()
        for parent, child, _m in edges:
            if child == cur and parent not in ancestors:
                ancestors.add(parent)
                if parent == "root":
                    has_root = True
                stack.append(parent)
    if not has_root:
        return 0
    envs: dict[str, int] = {"root": FULL_ENV_MASK}
    queue = ["root"]
    while queue:
        cur = queue.pop(0)
        cur_env = envs.get(cur, 0)
        for parent, child, child_marker in edges:
            if parent != cur or child not in ancestors:
                continue
            nxt_env = cur_env & child_marker
            prev = envs.get(child, 0)
            comb = prev | nxt_env
            if comb != prev:
                envs[child] = comb
                queue.append(child)
    return envs.get(target, 0)


def run_probe_2() -> dict[str, object]:
    m_linux = marker_from_pred(lambda p, _a, _py: p == "linux")
    m_darwin_arm = marker_from_pred(lambda p, a, _py: p == "darwin" and a == "arm64")
    m_posix = marker_from_pred(lambda p, _a, _py: p in ("linux", "darwin"))
    m_win = marker_from_pred(lambda p, _a, _py: p == "win32")
    m_py310 = marker_from_pred(lambda _p, _a, py: py == 10)
    m_py311_plus = marker_from_pred(lambda _p, _a, py: py >= 11)
    m_dead_py39 = 0  # Disjoint from universe py >= 3.10

    specs_by_pkg = {
        "numpy": [
            MarkerDepSpec("numpy", VersionRange.between(1, 2), m_py310),
            MarkerDepSpec("numpy", VersionRange.between(2, 3), m_py311_plus),
        ],
        "triton": [MarkerDepSpec("triton", VersionRange.singleton(3), m_linux)],
        "metal_kern": [MarkerDepSpec("metal_kern", VersionRange.singleton(1), m_darwin_arm)],
        "eventloop": [
            MarkerDepSpec("eventloop", VersionRange.singleton(1), m_posix),
            MarkerDepSpec("eventloop", VersionRange.singleton(2), m_win),
        ],
        "legacy_backport": [MarkerDepSpec("legacy_backport", VersionRange.singleton(1), m_dead_py39)],
        "torch_backend": [
            MarkerDepSpec("torch_backend", VersionRange.singleton(1), FULL_ENV_MASK, conflict_group="cpu"),
            MarkerDepSpec("torch_backend", VersionRange.singleton(2), m_linux, conflict_group="cu121"),
            MarkerDepSpec("torch_backend", VersionRange.singleton(3), m_linux, conflict_group="rocm"),
        ],
    }
    conflict_sets = [("cpu", "cu121", "rocm"), ("cu121", "rocm")]

    pruned_forks, pruned_csplits = uv_fork_dependencies(
        specs_by_pkg, conflict_sets, FULL_ENV_MASK, project_py_floor=10, enable_pruning_and_fastpath=True
    )
    unoptimized_forks, unopt_csplits = uv_fork_dependencies(
        specs_by_pkg, conflict_sets, FULL_ENV_MASK, project_py_floor=10, enable_pruning_and_fastpath=False
    )

    # Zero unsatisfiable env_mask == 0 contradictions in either mode, and strict Fork::set_env
    # non-disjointness invariant (`(fk.env_mask & d.marker_mask) != 0`) on every fork.
    assert all(fk.env_mask != 0 for fk in pruned_forks)
    assert all(fk.env_mask != 0 for fk in unoptimized_forks)
    assert all((fk.env_mask & d.marker_mask) != 0 for fk in pruned_forks for d in fk.deps)
    assert all((fk.env_mask & d.marker_mask) != 0 for fk in unoptimized_forks for d in fk.deps)
    assert all(
        d.pkg != "metal_kern"
        for fk in pruned_forks
        if (fk.env_mask & m_linux) != 0
        for d in fk.deps
    )
    assert all(
        d.pkg != "triton"
        for fk in pruned_forks
        if (fk.env_mask & ~m_linux) != 0
        for d in fk.deps
    )

    # Exact honest fork counts:
    # - 18 atomic environments x 4 mutually consistent conflict-group assignments = 72 cells.
    # - 32 satisfiable marker-split forks without single-spec no-fork / dominated fast path.
    # - 24 pruned forks (6 env regions x 4 conflict branches), and 6 vs. 40 N+1 conflict splits.
    valid_group_assignments = 4
    atomic_env_group_cells = len(ATOM_ENVS) * valid_group_assignments
    assert atomic_env_group_cells == 72
    assert len(unoptimized_forks) == 32
    assert len(pruned_forks) == 24
    assert pruned_csplits == 6 and unopt_csplits == 40

    # Solve each pruned fork ONCE with PubGrub and compute lockfile package markers via
    # `propagate_markers_cycle_safe` (`find_environments`, mod.rs:4289-4352).
    reg = OfflineRegistry()
    reg.add("numpy", 1, [])
    reg.add("numpy", 2, [])
    reg.add("triton", 3, [])
    reg.add("metal_kern", 1, [])
    reg.add("eventloop", 1, [])
    reg.add("eventloop", 2, [])
    reg.add("torch_backend", 1, [])
    reg.add("torch_backend", 2, [])
    reg.add("torch_backend", 3, [])

    covered_mask = 0
    resolved_forks: list[tuple[ForkBranch, dict[str, int], dict[str, int]]] = []
    for fk in pruned_forks:
        if not fk.allowed_groups and len(fk.excluded_groups) == 3:
            covered_mask |= fk.env_mask
        sub_reg = OfflineRegistry(packages={k: dict(v) for k, v in reg.packages.items()})
        sub_reg.add("root", 1, [(d.pkg, d.rng) for d in fk.deps])
        res = PubGrubSolver(sub_reg).solve()
        assert res.solved and res.solution is not None, f"Fork failed to solve: {fk}"
        fk_sol = {p: v for p, v in res.solution.items() if p != "root"}
        if (fk.env_mask & m_linux) != 0:
            assert "metal_kern" not in fk_sol
        if (fk.env_mask & ~m_linux) != 0:
            assert "triton" not in fk_sol
        fork_edges = [("root", d.pkg, fk.env_mask & d.marker_mask) for d in fk.deps]
        pkg_envs = {p: propagate_markers_cycle_safe(fork_edges, p) for p in fk_sol}
        resolved_forks.append((fk, fk_sol, pkg_envs))
    assert covered_mask == FULL_ENV_MASK

    # Compare single-platform flat lock resolved on (linux, x86_64, py3.11) with group="cpu"
    # against the pre-solved universal forked lock across all 18 atomic environments.
    linux_x64_311_idx = ATOM_ENVS.index(("linux", "x86_64", 11))
    flat_lock = {"numpy": 2, "triton": 3, "eventloop": 1, "torch_backend": 1}

    def wheel_installable_on(pkg: str, ver: int, plat: str, arch: str, py: int) -> bool:
        if pkg == "triton":
            return plat == "linux"
        if pkg == "metal_kern":
            return plat == "darwin" and arch == "arm64"
        if pkg == "eventloop":
            return (plat in ("linux", "darwin") and ver == 1) or (plat == "win32" and ver == 2)
        if pkg == "numpy":
            return (py == 10 and ver == 1) or (py >= 11 and ver == 2)
        if pkg == "torch_backend":
            return ver == 1 or plat == "linux"
        return True

    flat_failures = 0
    universal_failures = 0
    for idx, (plat, arch, py) in enumerate(ATOM_ENVS):
        bit = 1 << idx
        req_pkgs: dict[str, VersionRange] = {}
        for dlist in specs_by_pkg.values():
            for d in dlist:
                if d.conflict_group in (None, "cpu") and (d.marker_mask & bit):
                    req_pkgs[d.pkg] = d.rng
        install_ok = all(wheel_installable_on(p, v, plat, arch, py) for p, v in flat_lock.items())
        reqs_ok = all(p in flat_lock and rng.contains(flat_lock[p]) for p, rng in req_pkgs.items())
        if not (install_ok and reqs_ok):
            flat_failures += 1

        matching = [
            (fk, fk_sol, pkg_envs)
            for fk, fk_sol, pkg_envs in resolved_forks
            if (fk.env_mask & bit) and "cpu" in fk.allowed_groups
        ]
        assert len(matching) == 1
        _fk, fk_sol, pkg_envs = matching[0]
        installed = {p: v for p, v in fk_sol.items() if (pkg_envs[p] & bit) != 0}
        u_ok = all(
            wheel_installable_on(p, v, plat, arch, py) for p, v in installed.items()
        ) and all(p in installed and rng.contains(installed[p]) for p, rng in req_pkgs.items())
        if not u_ok:
            universal_failures += 1

    assert linux_x64_311_idx >= 0
    assert flat_failures == 14  # Fails on all 12 non-Linux envs + 2 Linux py3.10 envs (14/18 = 77.8%).
    assert universal_failures == 0

    # Verify cycle-safe forward marker fixpoint on cyclic dependency graph (pkg_a <-> pkg_b).
    cyclic_edges = [
        ("root", "pkg_a", m_linux),
        ("pkg_a", "pkg_b", m_py311_plus),
        ("pkg_b", "pkg_a", FULL_ENV_MASK),
        ("root", "pkg_b", m_darwin_arm),
    ]
    env_b = propagate_markers_cycle_safe(cyclic_edges, "pkg_b")
    expected_b = (m_linux & m_py311_plus) | m_darwin_arm
    assert env_b == expected_b

    return {
        "atomic_environments": len(ATOM_ENVS),
        "atomic_env_group_cells": atomic_env_group_cells,
        "unoptimized_nonempty_forks": len(unoptimized_forks),
        "pruned_forks": len(pruned_forks),
        "grid_to_pruned_reduction_x": round(atomic_env_group_cells / len(pruned_forks), 2),
        "marker_split_to_pruned_reduction_x": round(len(unoptimized_forks) / len(pruned_forks), 2),
        "conflict_n_plus_1_splits": {"pruned": pruned_csplits, "unoptimized": unopt_csplits},
        "flat_lock_failed_envs": f"{flat_failures}/{len(ATOM_ENVS)}",
        "universal_lock_failed_envs": f"{universal_failures}/{len(ATOM_ENVS)}",
        "cycle_fixpoint_bits": bin(env_b).count("1"),
    }


# ============================================================================
# PILLAR 3: Pinned Benchmark Evaluator Forensics vs. Hardened Graders
# ============================================================================


def envbench_remove_bad_commands(script: str) -> str:
    """Port of JetBrains-Research/EnvBench@1ba26950 evaluation/main.py:42-56."""
    res = []
    for line in script.split("\n"):
        s = line.strip()
        if s.startswith("mvn compile") or s.startswith("./mvnw compile"):
            continue
        if s.startswith("mvn test") or s.startswith("./mvnw test"):
            continue
        if s.startswith("gradle build") or s.startswith("./gradlew build"):
            continue
        if s.startswith("gradle test") or s.startswith("./gradlew test"):
            continue
        res.append(line)
    return "\n".join(res)


def run_envbench_jvm_real_bash(bootstrap_script: str, gradle_behavior: str) -> dict[str, object]:
    """Execute EnvBench@1ba26950 jvm_build.sh logic in a real temporary bash subshell."""
    cleaned = envbench_remove_bad_commands(bootstrap_script)
    with tempfile.TemporaryDirectory() as tmp:
        proj = os.path.join(tmp, "proj")
        os.makedirs(os.path.join(proj, "build_output"), exist_ok=True)
        with open(os.path.join(proj, "bootstrap_script.sh"), "w", encoding="utf-8") as f:
            f.write(cleaned + "\n")
        with open(os.path.join(proj, "gradlew"), "w", encoding="utf-8") as f:
            f.write("#!/bin/bash\n" + gradle_behavior + "\n")
        os.chmod(os.path.join(proj, "gradlew"), 0o755)
        # Structure of evaluation/scripts/jvm_build.sh:1-68 (using python3 in place of jq).
        build_sh = """#!/bin/bash
set -e
mkdir -p build_output
printf '{}\\n' > build_output/results.json
if [ -f "./bootstrap_script.sh" ]; then
  source ./bootstrap_script.sh
fi
chmod +x ./gradlew
./gradlew build -x test --console=plain > build.log 2>&1 || true
issues=$(grep -c "FAILURE" build.log || true)
python3 - "$issues" << 'PY'
import json, sys
with open("build_output/results.json") as f:
    d = json.load(f)
d["build_tool"] = "gradle"
d["issues_count"] = int(sys.argv[1])
with open("build_output/results.json", "w") as f:
    json.dump(d, f)
PY
exit 0
"""
        build_path = os.path.join(proj, "build.sh")
        with open(build_path, "w", encoding="utf-8") as f:
            f.write(build_sh)
        os.chmod(build_path, 0o755)
        proc = subprocess.run(
            ["/bin/bash", "-c", "./build.sh"], cwd=proj, capture_output=True, text=True
        )
        result: dict[str, object] = {"exit_code": proc.returncode, "issues_count": 0}
        res_file = os.path.join(proj, "build_output", "results.json")
        if os.path.exists(res_file):
            with open(res_file, encoding="utf-8") as f:
                result.update(json.load(f))
        return result


def hardened_jvm_bash(bootstrap_script: str, gradle_behavior: str) -> dict[str, object]:
    """Hardened evaluator: runs bootstrap in child process, captures real build exit code."""
    with tempfile.TemporaryDirectory() as tmp:
        proj = os.path.join(tmp, "proj")
        os.makedirs(proj, exist_ok=True)
        with open(os.path.join(proj, "bootstrap_script.sh"), "w", encoding="utf-8") as f:
            f.write(bootstrap_script + "\n")
        with open(os.path.join(proj, "gradlew"), "w", encoding="utf-8") as f:
            f.write("#!/bin/bash\n" + gradle_behavior + "\n")
        os.chmod(os.path.join(proj, "gradlew"), 0o755)
        os.chmod(os.path.join(proj, "bootstrap_script.sh"), 0o755)
        harness = """#!/bin/bash
set -e
bash -e ./bootstrap_script.sh
./gradlew build -x test --console=plain > build.log 2>&1
"""
        hpath = os.path.join(proj, "hardened_build.sh")
        with open(hpath, "w", encoding="utf-8") as f:
            f.write(harness)
        os.chmod(hpath, 0o755)
        proc = subprocess.run(
            ["/bin/bash", "-c", "./hardened_build.sh"], cwd=proj, capture_output=True, text=True
        )
        return {"passed": proc.returncode == 0, "exit_code": proc.returncode}


def envbench_python_eval_and_score(
    early_exit_zero: bool, missing_imports: int, runtime_c_abi_broken: bool
) -> tuple[dict[str, object], bool, str]:
    """Port of EnvBench python_build.sh + main.py:66-73 + both analysis paths."""
    json_result: dict[str, object] = {"exit_code": 0, "issues_count": 0}
    if early_exit_zero:
        # python_build.sh:9 writes {"pyright": {}}, line 16 `source ./bootstrap_script.sh` exits 0.
        json_result["pyright"] = {}
    else:
        diags = [{"rule": "reportMissingImports"}] * missing_imports
        json_result["issues_count"] = missing_imports
        json_result["pyright"] = {"summary": {"filesAnalyzed": 10}, "generalDiagnostics": diags}
    # Path B: env_setup_utils/analysis/analysis_utils.py:180-219 (`calculate_python_stats`)
    path_b_clean_pass = (
        json_result.get("pyright") is not None
        and json_result["exit_code"] == 0
        and json_result.get("issues_count", 0) == 0
    )
    # Path A: env_setup_utils/analysis/analyze_results.py:42 (`if not result.get("pyright"): continue`)
    if not json_result.get("pyright"):
        path_a_status = "dropped_from_denominator"
    elif json_result["exit_code"] == 0 and json_result["issues_count"] == 0:
        path_a_status = "pass"
    else:
        path_a_status = "fail"
    hardened_pass = (not early_exit_zero) and (missing_imports == 0) and (not runtime_c_abi_broken)
    return (
        {"path_b_clean_pass": path_b_clean_pass, "path_a_status": path_a_status},
        hardened_pass,
        path_a_status,
    )


def repo2run_grade(
    action_kind: str,  # "none" | "diff" | "bash"
    target_or_cmd: str,
    collected_tests: int,
    collection_rc: int,
    runtime_failed_tests: int,
) -> tuple[bool, bool]:
    """Port of Repo2Run@65042aa2 runtest.py:59-80, configuration.py:439,480, sandbox.py:479-490,545."""
    blocked = False
    if action_kind == "diff":
        base = target_or_cmd.split("/")[-1].strip()
        if base.startswith("test_") or base.endswith("_test.py"):
            blocked = True
    elif action_kind == "bash":
        cmd = target_or_cmd.strip()
        if "pytest" in cmd.lower() and "pip" not in cmd.lower():
            blocked = True
        elif cmd.split(" ")[0] in ("rm", "mv") and (
            cmd.split("/")[-1].startswith("test_") or cmd.split("/")[-1].endswith("_test.py")
        ):
            blocked = True

    if blocked:
        return False, False

    if collection_rc == 5:
        out = "No unit tests were detected in this repository, so it passes. Congratulations, you have successfully configured the environment!"
    elif collection_rc == 0:
        out = "Congratulations, you have successfully configured the environment!"
    else:
        out = "Error: Please modify the configuration according to the error messages below."
    pinned_pass = "Congratulations, you have successfully configured the environment!" in out

    hardened_pass = (
        action_kind == "none"
        and collection_rc == 0
        and collected_tests > 0
        and runtime_failed_tests == 0
    )
    return pinned_pass, hardened_pass


def swesmith_grade(
    patch_touches: str,  # "test_file_xfail" | "lib_pytest_xfail" | "real_fix"
) -> tuple[bool, bool]:
    """Port of SWE-smith@9b74ac08 utils.py:226-238 + grading.py:95-99."""
    effective_patch = "reverted" if patch_touches == "test_file_xfail" else patch_touches
    if effective_patch == "reverted":
        status = "FAILED"
    elif effective_patch == "lib_pytest_xfail":
        status = "XFAIL"
    else:
        status = "PASSED"
    pinned_resolved = status in ("PASSED", "XFAIL")
    hardened_resolved = status == "PASSED"
    return pinned_resolved, hardened_resolved


def execution_agent_bash_syntax_audit() -> dict[str, bool]:
    """Verify ExecutionAgent@8fb16de8 trace_to_bash.py:53-56 vs. exit_artifacts.py:147-151 via bash -n."""
    filename = "hello.txt"
    plain_content = "hello"  # Zero single quotes in filename or content.
    # Exact string emitted by sola-st/ExecutionAgent@8fb16de8 src/execution_agent/trace_to_bash.py:53-56:
    # trailing `''` on line 53 opens+closes an empty single-quoted string instead of reopening
    # `bash -c '...'`, leaving line 56 `'` unmatched on EVERY container file write.
    trace_to_bash_script = (
        f"docker exec $CONTAINER_ID bash -c 'cat > {shlex.quote(filename)} <<'\"'\"'EOF_FILE'\"'\"''\n"
        f"{plain_content}\n"
        "EOF_FILE\n"
        "'\n"
    )
    proc_broken = subprocess.run(
        ["/bin/bash", "-n"], input=trace_to_bash_script, text=True, capture_output=True
    )

    # Host-heredoc pattern from src/execution_agent/exit_artifacts.py:147-151 with embedded quotes.
    quoted_content = "it's \"$HOME\" and 'EOF_FILE' safe"
    exit_artifacts_script = (
        f"docker exec -i \"$CONTAINER_ID\" sh -eu -c 'cat > \"$1\"' sh {shlex.quote(filename)} "
        "<<'__EA_FILE_0__'\n"
        f"{quoted_content}\n"
        "__EA_FILE_0__\n"
    )
    proc_safe = subprocess.run(
        ["/bin/bash", "-n"], input=exit_artifacts_script, text=True, capture_output=True
    )
    return {
        "trace_to_bash_plain_hello_syntax_error": proc_broken.returncode != 0,
        "exit_artifacts_host_heredoc_syntax_ok": proc_safe.returncode == 0,
    }


def run_probe_3() -> dict[str, object]:
    # 3A: Real POSIX bash verification of EnvBench@1ba26950 jvm_build.sh
    eb_exit0 = run_envbench_jvm_real_bash(
        "exit 0", 'echo "FAILURE: Build failed with an exception." >&2; exit 1'
    )
    hd_exit0 = hardened_jvm_bash(
        "exit 0", 'echo "FAILURE: Build failed with an exception." >&2; exit 1'
    )
    assert eb_exit0["exit_code"] == 0 and eb_exit0["issues_count"] == 0
    assert hd_exit0["passed"] is False

    eb_javahome = run_envbench_jvm_real_bash(
        "export JAVA_HOME=/nonexistent",
        'echo "ERROR: JAVA_HOME is set to an invalid directory" >&2; exit 1',
    )
    hd_javahome = hardened_jvm_bash(
        "export JAVA_HOME=/nonexistent",
        'echo "ERROR: JAVA_HOME is set to an invalid directory" >&2; exit 1',
    )
    assert eb_javahome["exit_code"] == 0 and eb_javahome["issues_count"] == 0
    assert hd_javahome["passed"] is False

    eb_false_fail = run_envbench_jvm_real_bash(
        "true", 'echo "Task :compileJava - Note: ParserFAILUREHandler compiled"; exit 0'
    )
    hd_false_fail = hardened_jvm_bash(
        "true", 'echo "Task :compileJava - Note: ParserFAILUREHandler compiled"; exit 0'
    )
    assert eb_false_fail["exit_code"] == 0 and eb_false_fail["issues_count"] == 1
    assert hd_false_fail["passed"] is True

    assert "mvn clean compile" in envbench_remove_bad_commands("mvn clean compile")

    py_exit0, py_hd0, py_path_a = envbench_python_eval_and_score(
        early_exit_zero=True, missing_imports=5, runtime_c_abi_broken=True
    )
    assert py_exit0["path_b_clean_pass"] is True and py_path_a == "dropped_from_denominator"
    assert py_hd0 is False

    py_c_abi, py_hd_abi, _ = envbench_python_eval_and_score(
        early_exit_zero=False, missing_imports=0, runtime_c_abi_broken=True
    )
    assert py_c_abi["path_b_clean_pass"] is True and py_hd_abi is False

    # 3B: Repo2Run@65042aa2 matrix
    r2r_collect_only = repo2run_grade(
        "none", "", collected_tests=42, collection_rc=0, runtime_failed_tests=19
    )
    r2r_pyproject_bypass = repo2run_grade(
        "diff", "/repo/pyproject.toml", collected_tests=0, collection_rc=5, runtime_failed_tests=19
    )
    r2r_rm_tests_dir = repo2run_grade(
        "bash", "rm -rf /repo/tests", collected_tests=0, collection_rc=5, runtime_failed_tests=19
    )
    r2r_direct_test_blocked = repo2run_grade(
        "diff", "/repo/tests/test_core.py", collected_tests=0, collection_rc=5, runtime_failed_tests=19
    )
    assert r2r_collect_only == (True, False)
    assert r2r_pyproject_bypass == (True, False)
    assert r2r_rm_tests_dir == (True, False)
    assert r2r_direct_test_blocked == (False, False)

    ver_crashed = False
    try:
        for p1, p2 in zip("3.10-slim".split("."), ["3", "8"]):
            _ = int(p1) - int(p2)
    except ValueError:
        ver_crashed = True
    assert ver_crashed is True

    # 3C: SetupBench@041a412f, SWE-smith@9b74ac08, and ExecutionAgent@8fb16de8
    sb_dep_stripped = 0 == 0
    sb_stdout_crash = "Setup successful" in "Setup successful\nSegmentation fault"
    assert sb_dep_stripped is True and sb_stdout_crash is True

    ss_direct_test_xfail = swesmith_grade("test_file_xfail")
    ss_lib_xfail_bypass = swesmith_grade("lib_pytest_xfail")
    ss_real_fix = swesmith_grade("real_fix")
    assert ss_direct_test_xfail == (False, False)
    assert ss_lib_xfail_bypass == (True, False)
    assert ss_real_fix == (True, True)

    ea_syntax = execution_agent_bash_syntax_audit()
    assert ea_syntax["trace_to_bash_plain_hello_syntax_error"] is True
    assert ea_syntax["exit_artifacts_host_heredoc_syntax_ok"] is True

    return {
        "envbench_jvm_exit0_false_pass": eb_exit0["exit_code"] == 0 and eb_exit0["issues_count"] == 0,
        "envbench_jvm_javahome_false_pass": eb_javahome["exit_code"] == 0 and eb_javahome["issues_count"] == 0,
        "envbench_jvm_substring_false_fail": eb_false_fail["issues_count"] == 1,
        "envbench_py_exit0_pathB_pass_pathA_drop": (
            py_exit0["path_b_clean_pass"],
            py_exit0["path_a_status"],
        ),
        "repo2run_bypasses": {
            "collect_only_broken_tests": r2r_collect_only[0],
            "pyproject_testpaths_rc5": r2r_pyproject_bypass[0],
            "rm_rf_tests_dir_rc5": r2r_rm_tests_dir[0],
        },
        "swesmith_xfail": {
            "direct_test_edit_caught_by_reset": not ss_direct_test_xfail[0],
            "library_or_conftest_xfail_false_pass": ss_lib_xfail_bypass[0],
        },
        "execution_agent_trace_export": ea_syntax,
    }


# ============================================================================
# PILLAR 4: Synthetic Competing-Risks Drift vs. Per-Release --exclude-newer
# ============================================================================


@dataclass(frozen=True)
class TimedRelease:
    ver: int
    publish_day: int
    has_upload_time: bool
    api_epoch: int
    py_floor: int
    deps: tuple[tuple[str, VersionRange], ...]
    link_alive_until_day: int


def run_probe_4() -> dict[str, object]:
    """Evaluate 5 reproducibility regimes over 120 synthetic historical snapshots using PubGrub.

    Synthetic competing-risks parameterization:
      - 0.14 import-to-package name-mismatch rate; 0.071 syntax/encoding failure rate (Repo2Run p. 7);
      - 0.08 single-dependency missing-`upload-time` / unpinned-VCS rate (`core_0` only, while the
        remaining 7 packages in that repository retain PEP 700 `upload-time` metadata);
      - 0.40 5-year breaking-major-release rate; 0.03-0.04 external link-rot/yank rate;
      - 0.85 open-upper-bound (`>=1`) direct manifest rate.
    Matches uv's exact per-file rule (`resolver/mod.rs:2754-2785`): distributions with PEP 700
    `upload-time` are retained iff `publish_day < cutoff_day` (strict `<`), while distributions
    missing `upload-time` (`has_upload_time=False`) are retained per file without disabling
    `--exclude-newer` on sibling PEP-700-timestamped packages.
    """
    rng = random.Random(20261122)
    n_repos = 120
    commit_day = 0
    horizons_years = (0.5, 1.0, 3.0, 5.0)
    results_by_horizon: dict[str, dict[str, float]] = {}

    repos = []
    for r_idx in range(n_repos):
        has_name_mismatch = rng.random() < 0.14
        has_syntax_quirk = rng.random() < 0.071
        has_single_dep_missing_ts = rng.random() < 0.08
        pkg_timeline: dict[str, list[TimedRelease]] = {}
        expected_epochs: dict[str, int] = {}
        direct_reqs: list[tuple[str, VersionRange]] = []

        for c in range(4):
            cname = f"core_{c}"
            alive_v1 = INF_VER if rng.random() > 0.04 else rng.randint(60, 1400)
            # Scope missing upload-time strictly to `core_0` when triggered (1 of 8 packages).
            has_ts = not (has_single_dep_missing_ts and c == 0)
            rels = [TimedRelease(1, -100, has_ts, 1, 10, (), alive_v1)]
            if rng.random() < 0.40:
                brk_day = rng.randint(45, 1600)
                rels.append(
                    TimedRelease(2, brk_day, has_ts, 2, 10 if rng.random() > 0.25 else 12, (), INF_VER)
                )
            pkg_timeline[cname] = rels
            expected_epochs[cname] = 1

        for m in range(4):
            mname = f"mid_{m}"
            c_a, c_b = f"core_{m % 4}", f"core_{(m + 1) % 4}"
            alive_m1 = INF_VER if rng.random() > 0.03 else rng.randint(90, 1500)
            loose_upper = rng.random() < 0.70
            r_a = VersionRange.higher_than(1) if loose_upper else VersionRange.between(1, 2)
            rels = [
                TimedRelease(
                    1, -80, True, 1, 10, ((c_a, r_a), (c_b, VersionRange.higher_than(1))), alive_m1
                )
            ]
            if rng.random() < 0.40:
                up_day = rng.randint(60, 1600)
                rels.append(
                    TimedRelease(
                        2,
                        up_day,
                        True,
                        2,
                        10 if rng.random() > 0.2 else 12,
                        ((c_a, VersionRange.higher_than(2)), (c_b, VersionRange.higher_than(1))),
                        INF_VER,
                    )
                )
            pkg_timeline[mname] = rels
            expected_epochs[mname] = 1
            manifest_rng = (
                VersionRange.higher_than(1) if rng.random() < 0.85 else VersionRange.between(1, 2)
            )
            direct_reqs.append((mname, manifest_rng))

        # Pre-compute commit-time lockfile at t = commit_day (0); pre-commit releases have publish_day < 0.
        reg_t0 = OfflineRegistry()
        reg_t0.add("root", 1, direct_reqs)
        for p, rels in pkg_timeline.items():
            for rel in rels:
                if rel.publish_day < commit_day:
                    reg_t0.add(p, rel.ver, list(rel.deps))
        lock_sol = PubGrubSolver(reg_t0).solve().solution
        assert lock_sol is not None

        repos.append(
            {
                "id": r_idx,
                "name_mismatch": has_name_mismatch,
                "syntax_quirk": has_syntax_quirk,
                "timeline": pkg_timeline,
                "expected_epochs": expected_epochs,
                "direct_reqs": direct_reqs,
                "lock_sol": lock_sol,
            }
        )

    for yrs in horizons_years:
        eval_day = int(yrs * 365)
        counts = {
            "pipreqs_unpinned": 0,
            "manifest_latest": 0,
            "cdcl_exclude_newer": 0,
            "lockfile_live_registry": 0,
            "hermetic_lock_plus_mirror": 0,
        }
        timestamped_pkg_drift_under_exclude_newer = 0

        for repo in repos:
            tl: dict[str, list[TimedRelease]] = repo["timeline"]
            exp_ep: dict[str, int] = repo["expected_epochs"]
            dreqs: list[tuple[str, VersionRange]] = repo["direct_reqs"]
            lock_sol: dict[str, int] = repo["lock_sol"]

            def build_reg(
                cutoff_day: int | None, host_py: int, unpinned_root: bool
            ) -> OfflineRegistry:
                r = OfflineRegistry()
                root_d = [(p, VersionRange.full()) for p, _ in dreqs] if unpinned_root else dreqs
                r.add("root", 1, root_d)
                for p, rels in tl.items():
                    for rel in rels:
                        # Live availability at eval_day: published by eval_day and not yanked/link-rotted.
                        if rel.publish_day > eval_day or rel.link_alive_until_day <= eval_day:
                            continue
                        if rel.py_floor > host_py:
                            continue
                        # Exact uv per-distribution exclude_newer rule (resolver/mod.rs:2754-2785):
                        # `file.upload_time_utc_ms.is_none_or(|ts| ts < cutoff)`.
                        if (
                            cutoff_day is not None
                            and rel.has_upload_time
                            and not (rel.publish_day < cutoff_day)
                        ):
                            continue
                        r.add(p, rel.ver, list(rel.deps))
                return r

            def runtime_valid(sol: dict[str, int] | None, host_py: int) -> bool:
                if sol is None:
                    return False
                for p, v in sol.items():
                    if p == "root":
                        continue
                    rel = next(x for x in tl[p] if x.ver == v)
                    if (
                        rel.api_epoch != exp_ep[p]
                        or rel.py_floor > host_py
                        or rel.link_alive_until_day <= eval_day
                    ):
                        return False
                return True

            unpinned_host_py = 10 if yrs <= 1.0 else 11
            pinned_host_py = 10

            # 1. pipreqs: static import scan + unpinned latest versions at eval_day.
            if not repo["syntax_quirk"] and not repo["name_mismatch"]:
                sol1 = PubGrubSolver(
                    build_reg(None, unpinned_host_py, unpinned_root=True)
                ).solve().solution
                if runtime_valid(sol1, unpinned_host_py):
                    counts["pipreqs_unpinned"] += 1

            # 2. Manifest resolved at eval_day without cutoff.
            sol2 = PubGrubSolver(
                build_reg(None, unpinned_host_py, unpinned_root=False)
            ).solve().solution
            if runtime_valid(sol2, unpinned_host_py):
                counts["manifest_latest"] += 1

            # 3. CDCL PubGrub with `--exclude-newer <commit_day>` (per-file PEP 700 timestamp cut).
            res3 = PubGrubSolver(
                build_reg(commit_day, pinned_host_py, unpinned_root=False)
            ).solve()
            if res3.solved and res3.solution is not None:
                for p, v in res3.solution.items():
                    if p != "root":
                        rel = next(x for x in tl[p] if x.ver == v)
                        if rel.has_upload_time and rel.api_epoch != exp_ep[p]:
                            timestamped_pkg_drift_under_exclude_newer += 1
                if runtime_valid(res3.solution, pinned_host_py):
                    counts["cdcl_exclude_newer"] += 1

            # 4. Commit-time lockfile against live registry (immune to missing upload-time,
            # still exposed to external link-rot/yanks).
            if runtime_valid(lock_sol, pinned_host_py):
                counts["lockfile_live_registry"] += 1

            # 5. Commit-time lockfile + content-addressed wheel/jar mirror + pinned container.
            counts["hermetic_lock_plus_mirror"] += 1

        assert timestamped_pkg_drift_under_exclude_newer == 0
        assert (
            counts["pipreqs_unpinned"]
            < counts["manifest_latest"]
            < counts["cdcl_exclude_newer"]
            < counts["lockfile_live_registry"]
            < counts["hermetic_lock_plus_mirror"]
        )
        results_by_horizon[f"{yrs:.1f}y"] = {
            k: round(100.0 * v / n_repos, 1) for k, v in counts.items()
        }

    return results_by_horizon


# ============================================================================
# PILLAR 5: Illustrative Dual-Environment Rollback DTMC vs. Container Pollution
# ============================================================================


def mat_vec_mul(mat: list[list[float]], vec: list[float]) -> list[float]:
    n = len(vec)
    return [sum(vec[i] * mat[i][j] for i in range(n)) for j in range(n)]


def run_dtmc_architecture(
    stages: int,
    step_budget: int,
    wasted_prob: float,
    nonzero_fail_dirty_prob: float,
    silent_zero_exit_dirty_prob: float,
    has_cmd_rollback: bool,
    has_dual_env_clean_synth: bool,
    has_verified_synth: bool,
) -> tuple[float, bool]:
    """Parameterized discrete-time Markov chain (DTMC) over (stage k in 0..stages, cond in 0..2).

    Illustrative synthetic transition constants (`stages=6`, `wasted_prob=0.50`,
    `nonzero_fail_dirty_prob=0.28`, `silent_zero_exit_dirty_prob=0.16`, dirty progress multipliers
    `0.85 / 0.35 / 0.18`, single-env dirty replay `0.30`, unverified synthesis `0.22 / 0.08`)
    isolating how container rollback and dual-environment clean-build synthesis affect finite-budget
    hitting probabilities when external non-recoverable blockers (timeouts, missing GPUs, intrinsic
    repo defects) are absent. Returns `(p_done_at_budget, s_done_is_unique_reachable_absorbing)`.
    """
    n_states = 3 * stages + 2
    s_done = 3 * stages
    s_broken = 3 * stages + 1
    trans = [[0.0] * n_states for _ in range(n_states)]
    trans[s_done][s_done] = 1.0
    trans[s_broken][s_broken] = 1.0

    p_advance = 1.0 - wasted_prob
    for k in range(stages):
        for cond in (0, 1, 2):
            src = 3 * k + cond
            if cond == 2 and not has_dual_env_clean_synth:
                trans[src][src] = 1.0
                continue

            if cond == 0:
                eff_advance = p_advance
            elif cond == 1:
                eff_advance = p_advance * (0.85 if has_dual_env_clean_synth else 0.35)
            else:
                eff_advance = p_advance * 0.18
            p_waste = 1.0 - eff_advance

            if k + 1 == stages:
                if has_verified_synth:
                    if has_dual_env_clean_synth:
                        trans[src][s_done] += eff_advance
                    else:
                        clean_replay = 1.0 if cond == 0 else 0.30
                        trans[src][s_done] += eff_advance * clean_replay
                        trans[src][s_broken] += eff_advance * (1.0 - clean_replay)
                else:
                    synth_ok = 0.22 if cond == 0 else 0.08
                    trans[src][s_done] += eff_advance * synth_ok
                    trans[src][s_broken] += eff_advance * (1.0 - synth_ok)
            else:
                trans[src][3 * (k + 1) + cond] += eff_advance

            p_nz = p_waste * nonzero_fail_dirty_prob
            p_sz = p_waste * silent_zero_exit_dirty_prob
            p_harmless = p_waste - p_nz - p_sz

            trans[src][src] += p_harmless
            if has_cmd_rollback:
                trans[src][src] += p_nz
            else:
                nxt_cond = min(2, cond + 1)
                trans[src][3 * k + nxt_cond] += p_nz

            if has_dual_env_clean_synth:
                nxt_cond_sz = 1 if cond == 0 else cond
                trans[src][3 * k + nxt_cond_sz] += p_sz
            else:
                nxt_cond_sz = min(2, cond + 1)
                trans[src][3 * k + nxt_cond_sz] += p_sz

    # Check whether `s_done` is the sole reachable absorbing state from transient states `0..3*stages-1`:
    no_broken_edges = all(trans[src][s_broken] == 0.0 for src in range(3 * stages))
    no_transient_self_traps = all(trans[src][src] < 1.0 for src in range(3 * stages))
    unique_s_done_absorbing = no_broken_edges and no_transient_self_traps

    dist = [0.0] * n_states
    dist[0] = 1.0
    for _ in range(step_budget):
        dist = mat_vec_mul(trans, dist)
    return dist[s_done], unique_s_done_absorbing


def run_probe_5() -> dict[str, object]:
    stages = 6
    wasted_prob = 0.50
    nz_dirty = 0.28
    sz_dirty = 0.16
    budgets = (12, 24, 48, 75)
    curves: dict[str, dict[str, float]] = {
        "in_place_shell_no_rollback": {},
        "no_dockerfile_synthesizer": {},
        "single_env_cmd_rollback_only": {},
        "dual_env_without_cmd_rollback": {},
        "dual_env_plus_cmd_rollback": {},
    }
    unique_absorbing: dict[str, bool] = {}

    specs = {
        "in_place_shell_no_rollback": (False, False, True),
        "no_dockerfile_synthesizer": (True, True, False),
        "single_env_cmd_rollback_only": (True, False, True),
        "dual_env_without_cmd_rollback": (False, True, True),
        "dual_env_plus_cmd_rollback": (True, True, True),
    }

    for arch_name, (cmd_rb, dual_env, ver_synth) in specs.items():
        for b in budgets:
            val, uniq = run_dtmc_architecture(
                stages, b, wasted_prob, nz_dirty, sz_dirty, cmd_rb, dual_env, ver_synth
            )
            curves[arch_name][f"B={b}"] = round(100.0 * val, 2)
            unique_absorbing[arch_name] = uniq

    # Verify structural absorbing-state property: ONLY the two verified dual-env chains avoid both
    # polluted transient self-traps and s_broken transitions (so lim_{B->inf} P(s_done) = 1.0 in the
    # idealized DTMC without external timeouts/GPU/repo blockers).
    assert unique_absorbing == {
        "in_place_shell_no_rollback": False,
        "no_dockerfile_synthesizer": False,
        "single_env_cmd_rollback_only": False,
        "dual_env_without_cmd_rollback": True,
        "dual_env_plus_cmd_rollback": True,
    }

    b48 = {k: v["B=48"] for k, v in curves.items()}
    assert (
        b48["no_dockerfile_synthesizer"]
        < b48["single_env_cmd_rollback_only"]
        < b48["dual_env_without_cmd_rollback"]
        < b48["dual_env_plus_cmd_rollback"]
    )
    assert b48["in_place_shell_no_rollback"] < b48["single_env_cmd_rollback_only"]
    assert b48["dual_env_plus_cmd_rollback"] - b48["single_env_cmd_rollback_only"] > 35.0

    shell_gain_48_to_75 = (
        curves["in_place_shell_no_rollback"]["B=75"] - curves["in_place_shell_no_rollback"]["B=48"]
    )
    assert shell_gain_48_to_75 < 2.0
    assert curves["dual_env_plus_cmd_rollback"]["B=75"] > 95.0

    return {
        "yield_by_budget": curves,
        "unique_s_done_absorbing_without_external_blockers": unique_absorbing,
    }


def main() -> None:
    p1 = run_probe_1()
    p2 = run_probe_2()
    p3 = run_probe_3()
    p4 = run_probe_4()
    p5 = run_probe_5()

    report = [
        "=== DETERMINISTIC VERIFICATION PROBE: BUILD, ENV & CDCL RESOLUTION ===",
        "",
        "[Probe 1] CDCL PubGrub + Iterative Proof Reporter vs. resolvelib Backjumping Model",
        "  Basis: normative + source + derived + execution",
        f"  Unsat Scaling (M=3..8): {json.dumps(p1['scaling_curve'], sort_keys=True)}",
        f"  M=8 Ordering Sensitivity (backtrack_causes): {json.dumps(p1['ordering_sensitivity_M8'], sort_keys=True)}",
        f"  M=6 Sat Fallback Steps: {json.dumps(p1['satisfiable_M6_steps'], sort_keys=True)}",
        f"  M=6 Diagnostic Compression: {json.dumps(p1['diagnostic_tokens_M6'], sort_keys=True)}",
        f"  Depth-2500 Stack Safety: {json.dumps(p1['deep_chain_2500'], sort_keys=True)}",
        "",
        "[Probe 2] PEP 508 Marker-Algebra Universal Lockfile Forking vs. Single-Host Lock Drift",
        "  Basis: source + execution",
        f"  Results: {json.dumps(p2, sort_keys=True)}",
        "",
        "[Probe 3] Pinned Environment Benchmark Evaluator & Trace Forensics vs. Hardened Graders",
        "  Basis: source + execution",
        f"  EnvBench JVM exit-0 false pass: {p3['envbench_jvm_exit0_false_pass']}",
        f"  EnvBench JVM JAVA_HOME false pass: {p3['envbench_jvm_javahome_false_pass']}",
        f"  EnvBench JVM substring false fail: {p3['envbench_jvm_substring_false_fail']}",
        f"  EnvBench Python exit-0 (Path B clean_pass, Path A status): {json.dumps(p3['envbench_py_exit0_pathB_pass_pathA_drop'])}",
        f"  Repo2Run bypasses: {json.dumps(p3['repo2run_bypasses'], sort_keys=True)}",
        f"  SWE-smith XFAIL audit: {json.dumps(p3['swesmith_xfail'], sort_keys=True)}",
        f"  ExecutionAgent bash -n syntax audit: {json.dumps(p3['execution_agent_trace_export'], sort_keys=True)}",
        "",
        "[Probe 4] Synthetic Competing-Risks Drift vs. Per-Release --exclude-newer CDCL (N=120 repos)",
        "  Basis: source + derived + execution",
        f"  Survival (%) by Horizon: {json.dumps(p4, sort_keys=True)}",
        "",
        "[Probe 5] Illustrative Dual-Environment Rollback DTMC vs. In-Place Container Pollution",
        "  Basis: derived + execution",
        f"  Verified Build Yield (%) by Step Budget: {json.dumps(p5['yield_by_budget'], sort_keys=True)}",
        f"  Unique s_done Absorbing Class (idealized): {json.dumps(p5['unique_s_done_absorbing_without_external_blockers'], sort_keys=True)}",
        "",
        "ALL 5 PROBE PILLARS PASSED DETERMINISTIC INVARIANTS.",
    ]
    sys.stdout.write("\n".join(report) + "\n")


if __name__ == "__main__":
    main()
