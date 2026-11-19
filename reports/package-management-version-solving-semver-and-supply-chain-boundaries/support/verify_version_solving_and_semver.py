#!/usr/bin/env python3
"""Self-contained verification probe for package version solving, MVS, native `links`
conflicts, public-dependency type splits, Specification SemVer subtyping, Rust RFC 2451
coherence breakage, and read-only store epoch `mtime` freshness traps.

Requires Python 3.10+ and uses only the Python standard library.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Iterable


# =============================================================================
# 1. Semantic Versions & Version Constraints
# =============================================================================


@dataclass(frozen=True, order=True)
class Version:
    major: int
    minor: int
    patch: int

    def __str__(self) -> str:
        if self.major < 0:
            return "<absent>"
        return f"{self.major}.{self.minor}.{self.patch}"

    def cargo_compat_bucket(self) -> tuple[str, int]:
        """Cargo SemverCompatibility (leftmost non-zero component)."""
        if self.major > 0:
            return ("major", self.major)
        if self.minor > 0:
            return ("minor", self.minor)
        return ("patch", self.patch)


@dataclass(frozen=True)
class VersionRange:
    """Closed/half-open interval [lo, hi) over Versions (None means unbounded)."""

    lo: Version | None = None
    hi: Version | None = None

    def contains(self, v: Version) -> bool:
        if self.lo is not None and v < self.lo:
            return False
        if self.hi is not None and v >= self.hi:
            return False
        return True

    def intersect(self, other: VersionRange) -> VersionRange | None:
        lo = self.lo if other.lo is None else (other.lo if self.lo is None else max(self.lo, other.lo))
        hi = self.hi if other.hi is None else (other.hi if self.hi is None else min(self.hi, other.hi))
        if lo is not None and hi is not None and lo >= hi:
            return None
        return VersionRange(lo, hi)

    def __str__(self) -> str:
        if self.lo is None and self.hi is None:
            return "*"
        parts = []
        if self.lo is not None:
            parts.append(f">={self.lo}")
        if self.hi is not None:
            parts.append(f"<{self.hi}")
        return " ".join(parts)

    @staticmethod
    def exact(v: Version) -> VersionRange:
        return VersionRange(v, Version(v.major, v.minor, v.patch + 1))

    @staticmethod
    def caret(v: Version) -> VersionRange:
        if v.major > 0:
            return VersionRange(v, Version(v.major + 1, 0, 0))
        if v.minor > 0:
            return VersionRange(v, Version(0, v.minor + 1, 0))
        return VersionRange.exact(v)


@dataclass(frozen=True)
class PackageRelease:
    name: str
    version: Version
    deps: tuple[tuple[str, VersionRange], ...] = ()
    links: str | None = None
    public_deps: tuple[str, ...] = ()


# =============================================================================
# 2. Mini CDCL / PubGrub-style Conflict-Clause Version Solver
# =============================================================================


@dataclass(frozen=True)
class Literal:
    """Positive literal: pkg in allowed_set; Negative literal: pkg not in allowed_set."""

    pkg: str
    versions: frozenset[Version]
    positive: bool = True

    def negate(self) -> Literal:
        return Literal(self.pkg, self.versions, not self.positive)

    def satisfied_by(self, assigned: Version | None) -> bool | None:
        """Return True if satisfied, False if falsified, None if undecided."""
        if assigned is None:
            return None
        in_set = assigned in self.versions
        return in_set if self.positive else (not in_set)

    def __str__(self) -> str:
        vs = ",".join(str(v) for v in sorted(self.versions))
        if self.positive:
            return f"{self.pkg}∈{{{vs}}}"
        return f"{self.pkg}∉{{{vs}}}"


@dataclass(frozen=True)
class Incompatibility:
    """PubGrub-style incompatibility: conjunction of terms that CANNOT all hold.

    Equivalently, as a SAT clause, at least one term must be falsified.
    `causes` records either a human-readable external reason (leaf) or a pair of
    parent incompatibility indices (derived via resolution) to build derivation trees.
    """

    id: int
    terms: tuple[Literal, ...]
    reason: str
    parents: tuple[int, int] | None = None

    def fmt_terms(self) -> str:
        return " ∧ ".join(str(t) for t in self.terms)


@dataclass
class SolveResult:
    satisfiable: bool
    assignment: dict[str, Version] = field(default_factory=dict)
    learned_clauses: int = 0
    decisions: int = 0
    conflicts: int = 0
    derivation_tree: list[str] = field(default_factory=list)


class PubGrubMiniSolver:
    """Finite-domain CDCL version solver with PubGrub-style incompatibility tracking,
    unit propagation, 1-UIP conflict resolution, non-chronological backjumping,
    and derivation-tree explanation for unsatisfiable graphs.

    Models single-version-per-package-key exclusivity AND global native `links`
    mutual exclusion across arbitrary packages/majors.
    """

    def __init__(self, releases: Iterable[PackageRelease], allow_cargo_major_coexistence: bool = False):
        self.allow_cargo_major_coexistence = allow_cargo_major_coexistence
        self.by_key: dict[str, dict[Version, PackageRelease]] = {}
        self.raw_releases: list[PackageRelease] = list(releases)
        for rel in self.raw_releases:
            key = self._pkg_key(rel.name, rel.version)
            self.by_key.setdefault(key, {})[rel.version] = rel

    def _pkg_key(self, name: str, version: Version) -> str:
        if not self.allow_cargo_major_coexistence:
            return name
        kind, num = version.cargo_compat_bucket()
        return f"{name}[{kind}:{num}]"

    def _matching_keys_and_versions(self, dep_name: str, vrange: VersionRange) -> list[tuple[str, frozenset[Version]]]:
        matches: dict[str, set[Version]] = {}
        for key, vmap in self.by_key.items():
            for v, rel in vmap.items():
                if rel.name == dep_name and vrange.contains(v):
                    matches.setdefault(key, set()).add(v)
        return [(k, frozenset(vs)) for k, vs in sorted(matches.items())]

    def solve(self, root_name: str, root_version: Version) -> SolveResult:
        # Domain for each package key includes a sentinel ABSENT = Version(-1, 0, 0)
        ABSENT = Version(-1, 0, 0)
        all_keys = sorted(self.by_key.keys())
        domains: dict[str, frozenset[Version]] = {
            k: frozenset(set(self.by_key[k].keys()) | {ABSENT}) for k in all_keys
        }
        root_key = self._pkg_key(root_name, root_version)
        assert root_key in self.by_key and root_version in self.by_key[root_key], "root missing"

        incompats: list[Incompatibility] = []

        def add_incompat(terms: tuple[Literal, ...], reason: str, parents: tuple[int, int] | None = None) -> int:
            idx = len(incompats)
            incompats.append(Incompatibility(idx, terms, reason, parents))
            return idx

        # 1. Root must be selected at root_version: forbid root != root_version
        add_incompat(
            (Literal(root_key, frozenset({root_version}), positive=False),),
            f"root requires {root_name}=={root_version}",
        )

        # 2. Dependency incompatibilities
        for key, vmap in sorted(self.by_key.items()):
            for v, rel in sorted(vmap.items()):
                for dep_name, vrange in rel.deps:
                    matches = self._matching_keys_and_versions(dep_name, vrange)
                    if not matches:
                        add_incompat(
                            (Literal(key, frozenset({v}), positive=True),),
                            f"{rel.name} {v} depends on {dep_name} {vrange}, which has no available versions",
                        )
                    elif len(matches) == 1:
                        dep_key, allowed = matches[0]
                        add_incompat(
                            (
                                Literal(key, frozenset({v}), positive=True),
                                Literal(dep_key, allowed, positive=False),
                            ),
                            f"{rel.name} {v} depends on {dep_name} {vrange}",
                        )
                    else:
                        # Multiple SemVer-incompatible buckets satisfy the range (disjunction)
                        terms = [Literal(key, frozenset({v}), positive=True)]
                        for dep_key, allowed in matches:
                            terms.append(Literal(dep_key, allowed, positive=False))
                        add_incompat(
                            tuple(terms),
                            f"{rel.name} {v} depends on {dep_name} {vrange} (across major buckets)",
                        )

        # 3. Global native `links` mutual exclusion across ALL releases (even across majors!)
        by_links: dict[str, list[tuple[str, Version, str]]] = {}
        for key, vmap in self.by_key.items():
            for v, rel in vmap.items():
                if rel.links is not None:
                    by_links.setdefault(rel.links, []).append((key, v, rel.name))
        for lib_name, providers in sorted(by_links.items()):
            for i in range(len(providers)):
                for j in range(i + 1, len(providers)):
                    k1, v1, n1 = providers[i]
                    k2, v2, n2 = providers[j]
                    if k1 == k2:
                        continue  # Same package key already mutually exclusive by single-assignment
                    add_incompat(
                        (
                            Literal(k1, frozenset({v1}), positive=True),
                            Literal(k2, frozenset({v2}), positive=True),
                        ),
                        f"native `links = \"{lib_name}\"` conflict between {n1} {v1} and {n2} {v2}",
                    )

        # CDCL search state:
        # We track per-package allowed domain narrowing with decision-level trail.
        # Each trail entry: (level, pkg, excluded_versions, cause_incompat_id_or_None_if_decision)
        trail: list[tuple[int, str, frozenset[Version], int | None]] = []
        decision_level = 0
        decisions = 0
        conflicts = 0
        learned = 0

        def current_allowed(pkg: str) -> frozenset[Version]:
            allowed = set(domains[pkg])
            for _, p, excl, _ in trail:
                if p == pkg:
                    allowed -= excl
            return frozenset(allowed)

        def term_status(lit: Literal) -> str:
            """Return 'satisfied', 'contradicted', or 'inconclusive' relative to current allowed set."""
            avail = current_allowed(lit.pkg)
            if lit.positive:
                if avail and avail.issubset(lit.versions):
                    return "satisfied"
                if avail.isdisjoint(lit.versions):
                    return "contradicted"
                return "inconclusive"
            else:
                if avail.isdisjoint(lit.versions):
                    return "satisfied"
                if avail and avail.issubset(lit.versions):
                    return "contradicted"
                return "inconclusive"

        def earliest_satisfier(lit: Literal) -> tuple[int, int, int | None]:
            """Return (decision_level, trail_pos, cause_incompat_id) where `lit` first became satisfied.
            trail_pos == -1 means tautologically satisfied before any trail entries.
            """
            allowed = set(domains[lit.pkg])

            def is_sat(s: set[Version]) -> bool:
                return (bool(s) and s.issubset(lit.versions)) if lit.positive else s.isdisjoint(lit.versions)

            if is_sat(allowed):
                return (0, -1, None)
            for pos, (lvl, p, excl, cause) in enumerate(trail):
                if p == lit.pkg:
                    allowed -= excl
                    if is_sat(allowed):
                        return (lvl, pos, cause)
            raise RuntimeError(f"literal {lit} is not satisfied by current trail")

        def resolve_conflict(conflict_id: int) -> tuple[int | None, int]:
            """PubGrub / 1-UIP conflict resolution.

            Returns (backjump_level, learned_incompat_id) when satisfiable search can continue,
            or (None, terminal_incompat_id) when UNSAT (derivation tree rooted at ⊥).
            """
            nonlocal learned
            curr_id = conflict_id
            while True:
                inc = incompats[curr_id]
                if not inc.terms:
                    return (None, curr_id)
                # Inspect earliest satisfier (level, trail_pos, cause) for every term
                term_info = []
                for t in inc.terms:
                    lvl, pos, cause = earliest_satisfier(t)
                    term_info.append((lvl, pos, cause, t))
                # Find the term with the latest trail_pos
                term_info.sort(key=lambda x: x[1], reverse=True)
                n_lvl, n_pos, n_cause, n_term = term_info[0]
                prev_lvl = max((x[0] for x in term_info[1:]), default=0)
                if n_lvl > 0 and (prev_lvl < n_lvl or n_cause is None):
                    return (prev_lvl, curr_id)
                if n_cause is None:
                    return (None, curr_id)

                # Resolve curr_id with n_cause on pivot package n_term.pkg:
                # - For non-pivot packages q: sat_set is INTERSECTION (both incompats must trigger).
                # - For pivot package p:      sat_set is UNION (forbid p in A U C when rest holds).
                cause_inc = incompats[n_cause]
                sat_sets: dict[str, set[Version]] = {}
                for t in inc.terms:
                    s = set(t.versions) if t.positive else set(domains[t.pkg]) - set(t.versions)
                    sat_sets[t.pkg] = sat_sets[t.pkg] & s if t.pkg in sat_sets else s
                for t in cause_inc.terms:
                    s = set(t.versions) if t.positive else set(domains[t.pkg]) - set(t.versions)
                    if t.pkg == n_term.pkg:
                        sat_sets[t.pkg] = sat_sets[t.pkg] | s
                    else:
                        sat_sets[t.pkg] = sat_sets[t.pkg] & s if t.pkg in sat_sets else s

                new_terms: list[Literal] = []
                for p, s in sorted(sat_sets.items()):
                    if s == domains[p]:
                        continue  # Pivot eliminated (A U C == full domain)
                    if len(s) <= len(domains[p]) // 2:
                        new_terms.append(Literal(p, frozenset(s), positive=True))
                    else:
                        new_terms.append(Literal(p, frozenset(domains[p] - s), positive=False))
                new_id = add_incompat(
                    tuple(new_terms),
                    f"derived from #{curr_id} and #{n_cause} on {n_term.pkg}",
                    parents=(curr_id, n_cause),
                )
                learned += 1
                curr_id = new_id

        def format_derivation_tree(root_incompat_id: int) -> list[str]:
            lines: list[str] = []
            visited: set[int] = set()

            def walk(iid: int, depth: int) -> None:
                inc = incompats[iid]
                indent = "  " * depth
                tag = f"#{iid}"
                if iid in visited:
                    lines.append(f"{indent}- [{tag}] (shared) {inc.reason}")
                    return
                visited.add(iid)
                if inc.parents is None:
                    lines.append(f"{indent}- [{tag} external] {inc.reason}")
                else:
                    lines.append(f"{indent}- [{tag} derived] forbid ({inc.fmt_terms() or '⊥'}): {inc.reason}")
                    walk(inc.parents[0], depth + 1)
                    walk(inc.parents[1], depth + 1)

            walk(root_incompat_id, 0)
            return lines

        def propagate() -> int | None:
            """Run unit propagation to fixpoint. Return conflicting incompat ID or None."""
            changed = True
            while changed:
                changed = False
                for inc in incompats:
                    statuses = [(term_status(t), t) for t in inc.terms]
                    if any(st == "contradicted" for st, _ in statuses):
                        continue
                    inconclusive = [t for st, t in statuses if st == "inconclusive"]
                    if not inconclusive:
                        return inc.id  # All terms satisfied -> conflict!
                    if len(inconclusive) == 1:
                        # Almost satisfied: forbid the single inconclusive term
                        t = inconclusive[0]
                        avail = current_allowed(t.pkg)
                        to_exclude = (avail & t.versions) if t.positive else (avail - t.versions)
                        if to_exclude:
                            if to_exclude == avail:
                                # Excludes every remaining value -> immediate conflict
                                return inc.id
                            trail.append((decision_level, t.pkg, frozenset(to_exclude), inc.id))
                            changed = True
            return None

        # Main CDCL loop
        while True:
            conflict_id = propagate()
            if conflict_id is not None:
                conflicts += 1
                bj_level, terminal_or_learned_id = resolve_conflict(conflict_id)
                if bj_level is None:
                    return SolveResult(
                        satisfiable=False,
                        learned_clauses=learned,
                        decisions=decisions,
                        conflicts=conflicts,
                        derivation_tree=format_derivation_tree(terminal_or_learned_id),
                    )
                # Non-chronological backjump
                trail = [entry for entry in trail if entry[0] <= bj_level]
                decision_level = bj_level
                # Propagate the newly learned incompatibility immediately
                continue

            # Pick an undecided package with >1 allowed versions (prefer non-ABSENT highest version,
            # preferring packages that are already required != ABSENT first, matching PubGrub heuristics)
            candidates = []
            for k in all_keys:
                avail = current_allowed(k)
                if len(avail) > 1:
                    required = ABSENT not in avail
                    candidates.append((not required, len(avail), k, avail))
            if not candidates:
                assignment = {}
                for k in all_keys:
                    v = next(iter(current_allowed(k)))
                    if v != ABSENT:
                        assignment[k] = v
                return SolveResult(
                    satisfiable=True,
                    assignment=assignment,
                    learned_clauses=learned,
                    decisions=decisions,
                    conflicts=conflicts,
                )
            candidates.sort()
            _, _, pick_pkg, avail = candidates[0]
            non_absent = sorted((v for v in avail if v != ABSENT), reverse=True)
            chosen = non_absent[0] if non_absent else ABSENT
            decision_level += 1
            decisions += 1
            # Decision: narrow pick_pkg to {chosen} by excluding avail - {chosen}
            trail.append((decision_level, pick_pkg, frozenset(avail - {chosen}), None))


# =============================================================================
# 3. Minimal Version Selection (Go MVS / Bazel Bzlmod lattice join)
# =============================================================================


def mvs_build_list(
    root: tuple[str, Version],
    required_fn: Callable[[tuple[str, Version]], list[tuple[str, Version]]],
) -> dict[str, Version]:
    """Russ Cox's Minimal Version Selection (Go `cmd/go/internal/mvs/mvs.go`).

    Requires only minimum versions (no upper bounds, no exclusions) and enforces
    the Import Compatibility Rule (incompatible majors use distinct module paths,
    e.g., `mod` vs `mod/v2`). Always terminates in O(|V| + |E|) without SAT search.
    """
    visited: set[tuple[str, Version]] = set()
    stack: list[tuple[str, Version]] = [root]
    selected: dict[str, Version] = {root[0]: root[1]}

    while stack:
        node = stack.pop()
        if node in visited:
            continue
        visited.add(node)
        mod, ver = node
        if mod not in selected or ver > selected[mod]:
            selected[mod] = ver
        for req in required_fn(node):
            if req not in visited:
                stack.append(req)
    return selected


# =============================================================================
# 4. Public-Dependency Type-Identity Split Checker (RFC 1977 / RFC 3516)
# =============================================================================


def check_public_dependency_pools(
    releases: list[PackageRelease],
    selected: dict[str, Version],
) -> list[str]:
    """Detect RFC 1977/3516 public-dependency type-identity splits.

    When crate A publicly re-exports/exposes types from `dep` (v1) and crate B
    publicly exposes `dep` (v2), any common consumer depending on both A and B
    observes two incompatible nominal identities for `dep::Type`.
    """
    rel_index = {(r.name, r.version): r for r in releases}
    # Map each selected package key -> actual PackageRelease
    active_by_name: dict[str, list[PackageRelease]] = {}
    for k, v in selected.items():
        base_name = k.split("[")[0]
        rel = rel_index[(base_name, v)]
        active_by_name.setdefault(base_name, []).append(rel)

    # For each active package, compute transitive closure of public dependencies
    def public_closure(rel: PackageRelease) -> dict[str, set[Version]]:
        seen: dict[str, set[Version]] = {}
        work = [rel]
        visited_rels: set[tuple[str, Version]] = set()
        while work:
            cur = work.pop()
            if (cur.name, cur.version) in visited_rels:
                continue
            visited_rels.add((cur.name, cur.version))
            for pub_dep_name in cur.public_deps:
                # Find the matching dep range in cur.deps
                for dname, drange in cur.deps:
                    if dname == pub_dep_name:
                        for cand in active_by_name.get(dname, []):
                            if drange.contains(cand.version):
                                seen.setdefault(dname, set()).add(cand.version)
                                work.append(cand)
        return seen

    hazards: list[str] = []
    for base_name, rels in sorted(active_by_name.items()):
        for rel in rels:
            # Check all direct deps of `rel` and union their public pools
            visible_types: dict[str, set[Version]] = {}
            for dname, drange in rel.deps:
                for cand in active_by_name.get(dname, []):
                    if drange.contains(cand.version):
                        visible_types.setdefault(dname, set()).add(cand.version)
                        for tname, tvers in public_closure(cand).items():
                            visible_types.setdefault(tname, set()).update(tvers)
            for tname, tvers in sorted(visible_types.items()):
                if len(tvers) > 1:
                    vers_str = ", ".join(str(x) for x in sorted(tvers))
                    hazards.append(
                        f"consumer `{rel.name} {rel.version}` observes split public type identities "
                        f"for `{tname}`: versions [{vers_str}]"
                    )
    return hazards


# =============================================================================
# 5. Variance-Aware Specification SemVer Subtyping Checker (Liskov & Wing 1994)
# =============================================================================


@dataclass(frozen=True)
class Contract:
    """Behavioral specification over a finite test domain of (input, output) states."""

    name: str
    pre: Callable[[int], bool]
    post: Callable[[int, int], bool]
    invariant: Callable[[int], bool] = lambda _: True


@dataclass(frozen=True)
class SpecSemVerVerdict:
    compatible: bool
    required_bump: str  # "minor/patch" or "major"
    violations: tuple[str, ...]


def check_spec_semver(
    old: Contract,
    new: Contract,
    input_domain: Iterable[int],
    output_domain: Iterable[int],
) -> SpecSemVerVerdict:
    """Verify Liskov-Wing behavioral subtyping for Specification SemVer:
      1. Contravariant Precondition:  ∀ x, Pre_old(x) => Pre_new(x)
      2. Covariant Postcondition:     ∀ x, y, (Pre_old(x) ∧ Post_new(x, y)) => Post_old(x, y)
      3. Preserved Type Invariant:    ∀ s, Inv_new(s) => Inv_old(s)
    """
    inputs = list(input_domain)
    outputs = list(output_domain)
    violations: list[str] = []

    # 1. Precondition contravariance
    for x in inputs:
        if old.pre(x) and not new.pre(x):
            violations.append(
                f"precondition strengthened (contravariance break) at input x={x}: "
                f"Pre_old({x})=True but Pre_new({x})=False"
            )
            break

    # 2. Postcondition covariance (guarded by Pre_old, per Liskov-Wing / Hoare refinement)
    for x in inputs:
        if not old.pre(x):
            continue
        for y in outputs:
            if new.post(x, y) and not old.post(x, y):
                violations.append(
                    f"postcondition weakened (covariance break) at (x={x}, y={y}): "
                    f"Pre_old({x}) ∧ Post_new({x},{y}) holds, but Post_old({x},{y})=False"
                )
                break
        if len(violations) >= 2:
            break

    # 3. Type invariant preservation
    for s in outputs:
        if new.invariant(s) and not old.invariant(s):
            violations.append(
                f"type invariant weakened at state s={s}: Inv_new({s})=True but Inv_old({s})=False"
            )
            break

    if violations:
        return SpecSemVerVerdict(False, "major", tuple(violations))
    return SpecSemVerVerdict(True, "minor/patch", ())


# =============================================================================
# 6. Rust RFC 2451 Trait Coherence & Orphan-Rule SemVer Breakage Checker
# =============================================================================


@dataclass(frozen=True)
class TypeExpr:
    kind: str  # "param", "local", "foreign", "fundamental"
    name: str
    args: tuple[TypeExpr, ...] = ()
    is_new_in_release: bool = False

    def is_local(self) -> bool:
        if self.kind == "local":
            return True
        if self.kind == "fundamental":
            return any(a.is_local() for a in self.args)
        return False

    def is_new_local(self) -> bool:
        if self.kind == "local" and self.is_new_in_release:
            return True
        if self.kind == "fundamental":
            return any(a.is_new_local() for a in self.args)
        return False

    def has_uncovered_param(self) -> bool:
        """RFC 2451: A type param is uncovered unless wrapped in a non-fundamental type constructor."""
        if self.kind == "param":
            return True
        if self.kind == "fundamental":
            return any(a.has_uncovered_param() for a in self.args)
        # Non-fundamental `local` or `foreign` constructor covers its type arguments
        return False


@dataclass(frozen=True)
class TraitImplHeader:
    trait_name: str
    trait_is_local: bool
    trait_args: tuple[TypeExpr, ...]  # T1..Tn
    self_type: TypeExpr               # T0

    def type_sequence(self) -> tuple[TypeExpr, ...]:
        return (self.self_type,) + self.trait_args


def check_rfc2451_orphan_legal(impl: TraitImplHeader) -> tuple[bool, str]:
    """Check RFC 2451 concrete orphan rule for `impl<P..> Trait<T1..Tn> for T0`."""
    if impl.trait_is_local:
        return True, "local trait"
    seq = impl.type_sequence()
    for i, ty in enumerate(seq):
        if ty.is_local():
            for prev in seq[:i]:
                if prev.has_uncovered_param():
                    return False, f"uncovered type param in T{seq.index(prev)} precedes first local type T{i}"
            return True, f"first local type at T{i} with no preceding uncovered type param"
    return False, "foreign trait with no local type in T0..Tn"


def check_rfc2451_upstream_impl_addition_semver(impl: TraitImplHeader) -> tuple[str, str]:
    """Check RFC 2451 'Effects on parent crates' rule for adding an impl to an EXISTING trait.

    Safe (minor) ONLY IF at least one Ti in T0..=Tn is a *newly added* local type
    and no uncovered type parameter appears in T0..Ti (excluding Ti).
    Otherwise MAJOR breaking because a downstream crate may legally hold an overlapping impl.
    """
    seq = impl.type_sequence()
    for i, ty in enumerate(seq):
        if ty.is_new_local():
            for prev in seq[:i]:
                if prev.has_uncovered_param():
                    return (
                        "major",
                        f"coherence-breaking: uncovered param precedes new local type at T{i} "
                        f"(collides with legal downstream impl using a local type at the uncovered position)",
                    )
            return "minor", f"coherence-safe: new local type at T{i} with no preceding uncovered param"
    return (
        "major",
        "coherence-breaking: adds impl for existing trait with no new local type "
        "(can collide with downstream orphan-legal impl)",
    )


# =============================================================================
# 7. Read-Only Store Epoch `mtime` Freshness Trap Simulator
# =============================================================================


def simulate_mtime_freshness(
    input_mtime: int,
    artifact_mtime: int,
    input_hash: str,
    recorded_hash: str,
) -> dict[str, bool]:
    """Contrast strict `mtime` freshness (Lake `MTime.checkUpToDate`: self < mtime)
    against content-hash freshness (Lake `BuildTrace.checkAgainstHash` / Cargo checksum-freshness).
    """
    return {
        "strict_mtime_up_to_date": input_mtime < artifact_mtime,
        "content_hash_up_to_date": input_hash == recorded_hash,
    }


# =============================================================================
# 8. 3-SAT -> Package Version Installability Reduction (Mancinelli 2006 / Cox 2016)
# =============================================================================


def encode_3sat_as_packages(
    num_vars: int,
    clauses: list[tuple[tuple[int, bool], tuple[int, bool], tuple[int, bool]]],
) -> list[PackageRelease]:
    """Encode a 3-SAT formula into a single-version-per-package repository.

    - Variable x_j -> package `X{j}` with versions 0.0.0 (False) and 1.0.0 (True).
    - Clause C_i   -> package `C{i}` with versions 0.0.0, 1.0.0, 2.0.0, where C_i:k
                      depends on the exact version of X_j satisfying literal k.
    - Formula F    -> package `F` version 1.0.0 depending on C_1..C_n (any version).
    """
    rels: list[PackageRelease] = []
    for j in range(1, num_vars + 1):
        rels.append(PackageRelease(f"X{j}", Version(0, 0, 0)))
        rels.append(PackageRelease(f"X{j}", Version(1, 0, 0)))
    f_deps = []
    for idx, clause in enumerate(clauses, start=1):
        cname = f"C{idx}"
        f_deps.append((cname, VersionRange()))
        for lit_idx, (var_j, polarity) in enumerate(clause):
            req_ver = Version(1, 0, 0) if polarity else Version(0, 0, 0)
            rels.append(
                PackageRelease(
                    cname,
                    Version(lit_idx, 0, 0),
                    deps=((f"X{var_j}", VersionRange.exact(req_ver)),),
                )
            )
    rels.append(PackageRelease("F", Version(1, 0, 0), deps=tuple(f_deps)))
    return rels


# =============================================================================
# Main Verification Harness
# =============================================================================


def main() -> int:
    print("=== [1] 3-SAT -> Version Installability Reduction (Cox 2016 / Mancinelli 2006) ===")
    # Russ Cox's exact satisfiable 3-SAT formula:
    # (~x1 v ~x2 v ~x3) ^ (~x2 v ~x3 v ~x4) ^ (~x2 v ~x2 v x3) ^ (x2 v x2 v x2)
    sat_clauses = [
        ((1, False), (2, False), (3, False)),
        ((2, False), (3, False), (4, False)),
        ((2, False), (2, False), (3, True)),
        ((2, True), (2, True), (2, True)),
    ]
    sat_solver = PubGrubMiniSolver(encode_3sat_as_packages(4, sat_clauses))
    sat_res = sat_solver.solve("F", Version(1, 0, 0))
    assert sat_res.satisfiable, "expected SAT 3-SAT instance to resolve"
    x_vals = {f"x{j}": (sat_res.assignment[f"X{j}"].major == 1) for j in range(1, 5)}
    assert x_vals == {"x1": False, "x2": True, "x3": True, "x4": False}, f"unexpected model: {x_vals}"
    print(f"  SAT formula resolved uniquely: {x_vals} (decisions={sat_res.decisions}, conflicts={sat_res.conflicts})")

    # Unsatisfiable extension adding (x1 v ~x2 v x4)
    unsat_clauses = sat_clauses + [((1, True), (2, False), (4, True))]
    unsat_solver = PubGrubMiniSolver(encode_3sat_as_packages(4, unsat_clauses))
    unsat_res = unsat_solver.solve("F", Version(1, 0, 0))
    assert not unsat_res.satisfiable, "expected UNSAT 3-SAT extension to fail"
    print(
        f"  UNSAT extension proved unresolvable (decisions={unsat_res.decisions}, "
        f"conflicts={unsat_res.conflicts}, learned={unsat_res.learned_clauses})"
    )

    print("\n=== [2] PubGrub CDCL Derivation Tree on Unsatisfiable Diamond ===")
    # Classic PubGrub example (dropdown / icons / menu / intl)
    pubgrub_diamond = [
        PackageRelease(
            "root",
            Version(1, 0, 0),
            deps=(
                ("menu", VersionRange(Version(1, 0, 0), None)),
                ("icons", VersionRange(None, Version(2, 0, 0))),
                ("intl", VersionRange(Version(5, 0, 0), None)),
            ),
        ),
        PackageRelease("menu", Version(1, 0, 0), deps=(("dropdown", VersionRange(Version(1, 0, 0), Version(2, 0, 0))),)),
        PackageRelease("menu", Version(1, 1, 0), deps=(("dropdown", VersionRange(Version(2, 0, 0), None)),)),
        PackageRelease("dropdown", Version(1, 0, 0), deps=(("intl", VersionRange(None, Version(4, 0, 0))),)),
        PackageRelease("dropdown", Version(2, 0, 0), deps=(("icons", VersionRange(Version(2, 0, 0), None)),)),
        PackageRelease("icons", Version(1, 0, 0)),
        PackageRelease("icons", Version(2, 0, 0)),
        PackageRelease("intl", Version(3, 0, 0)),
        PackageRelease("intl", Version(5, 0, 0)),
    ]
    pg_res = PubGrubMiniSolver(pubgrub_diamond).solve("root", Version(1, 0, 0))
    assert not pg_res.satisfiable
    assert len(pg_res.derivation_tree) >= 3
    print(f"  UNSAT confirmed (conflicts={pg_res.conflicts}, learned={pg_res.learned_clauses}); derivation tree:")
    for line in pg_res.derivation_tree[:8]:
        print("   ", line)

    print("\n=== [3] Go MVS Lattice Join vs. Import Compatibility Rule ===")
    # Diamond where A requires B@1.2 and C@1.1; B@1.2 requires D@1.3; C@1.1 requires D@1.4;
    # and C@1.1 ALSO imports major v2 `D/v2@2.1` as a distinct module path.
    mvs_graph = {
        ("A", Version(1, 0, 0)): [("B", Version(1, 2, 0)), ("C", Version(1, 1, 0))],
        ("B", Version(1, 2, 0)): [("D", Version(1, 3, 0))],
        ("C", Version(1, 1, 0)): [("D", Version(1, 4, 0)), ("D/v2", Version(2, 1, 0))],
        ("D", Version(1, 3, 0)): [],
        ("D", Version(1, 4, 0)): [],
        ("D/v2", Version(2, 1, 0)): [],
    }
    build_list = mvs_build_list(("A", Version(1, 0, 0)), lambda m: mvs_graph[m])
    assert build_list["D"] == Version(1, 4, 0)
    assert build_list["D/v2"] == Version(2, 1, 0)
    print(f"  MVS build list (deterministic lattice join, 0 conflicts): { {k: str(v) for k, v in sorted(build_list.items())} }")

    print("\n=== [4] Cargo Multi-Major Coexistence, Public-Dep Split & Native `links` Conflict ===")
    # Case 4a: Pure Rust crates allow foo 1.2.0 and foo 2.0.0 simultaneously,
    # BUT expose a public-dependency type-identity split in consumer `app`.
    cargo_split_rels = [
        PackageRelease("app", Version(1, 0, 0), deps=(("lib_a", VersionRange.caret(Version(1, 0, 0))), ("lib_b", VersionRange.caret(Version(1, 0, 0))))),
        PackageRelease("lib_a", Version(1, 0, 0), deps=(("foo", VersionRange.caret(Version(1, 0, 0))),), public_deps=("foo",)),
        PackageRelease("lib_b", Version(1, 0, 0), deps=(("foo", VersionRange.caret(Version(2, 0, 0))),), public_deps=("foo",)),
        PackageRelease("foo", Version(1, 2, 0)),
        PackageRelease("foo", Version(2, 0, 0)),
    ]
    split_res = PubGrubMiniSolver(cargo_split_rels, allow_cargo_major_coexistence=True).solve("app", Version(1, 0, 0))
    assert split_res.satisfiable
    assert "foo[major:1]" in split_res.assignment and "foo[major:2]" in split_res.assignment
    hazards = check_public_dependency_pools(cargo_split_rels, split_res.assignment)
    assert len(hazards) == 1 and "foo" in hazards[0]
    print(f"  Cargo multi-major SAT: { {k: str(v) for k, v in sorted(split_res.assignment.items())} }")
    print(f"  Public-dep type split detected: {hazards[0]}")

    # Case 4b: Same diamond, except `foo` wraps a native C library (`links = "z"`):
    # Global `links` singleton exclusivity makes the graph UNSAT even with major coexistence!
    cargo_links_rels = [
        PackageRelease("app", Version(1, 0, 0), deps=(("lib_a", VersionRange.caret(Version(1, 0, 0))), ("lib_b", VersionRange.caret(Version(1, 0, 0))))),
        PackageRelease("lib_a", Version(1, 0, 0), deps=(("libz_sys", VersionRange.caret(Version(1, 0, 0))),)),
        PackageRelease("lib_b", Version(1, 0, 0), deps=(("libz_sys", VersionRange.caret(Version(2, 0, 0))),)),
        PackageRelease("libz_sys", Version(1, 1, 0), links="z"),
        PackageRelease("libz_sys", Version(2, 0, 0), links="z"),
    ]
    links_res = PubGrubMiniSolver(cargo_links_rels, allow_cargo_major_coexistence=True).solve("app", Version(1, 0, 0))
    assert not links_res.satisfiable
    assert any('links = "z"' in line for line in links_res.derivation_tree)
    print("  Native `links = \"z\"` conflict rejected across majors; root derivation:")
    for line in links_res.derivation_tree[:6]:
        print("   ", line)

    print("\n=== [5] Variance-Aware Specification SemVer Subtyping (Liskov & Wing 1994) ===")
    dom_x = range(-5, 11)
    dom_y = range(-5, 21)
    base = Contract(
        name="v1.0: parse_nonneg(x: i32) -> i32",
        pre=lambda x: x >= 0,
        post=lambda x, y: y >= x,
        invariant=lambda s: s >= 0,
    )
    # 5a: Compatible refinement: weakened pre (x >= -2), strengthened post (y >= x + 1 on x >= 0), stronger invariant (s >= 1)
    compat = Contract(
        name="v1.1: weakened pre + strengthened post",
        pre=lambda x: x >= -2,
        post=lambda x, y: (y >= x + 1) if x >= 0 else (y == -1),
        invariant=lambda s: s >= 1,
    )
    v_compat = check_spec_semver(base, compat, dom_x, dom_y)
    assert v_compat.compatible and v_compat.required_bump == "minor/patch"
    print(f"  [PASS] {compat.name} -> {v_compat.required_bump}")

    # 5b: Precondition strengthening (x > 0 rejects x == 0): MAJOR break with identical Rust signature!
    stronger_pre = Contract(
        name="v1.1-bad-pre: tightened x >= 0 to x > 0",
        pre=lambda x: x > 0,
        post=lambda x, y: y >= x,
        invariant=lambda s: s >= 0,
    )
    v_pre = check_spec_semver(base, stronger_pre, dom_x, dom_y)
    assert not v_pre.compatible and v_pre.required_bump == "major"
    print(f"  [BREAK] {stronger_pre.name} -> {v_pre.required_bump}: {v_pre.violations[0]}")

    # 5c: Postcondition weakening (y >= 0 instead of y >= x): MAJOR break with identical Rust signature!
    weaker_post = Contract(
        name="v1.1-bad-post: weakened y >= x to y >= 0",
        pre=lambda x: x >= 0,
        post=lambda x, y: y >= 0,
        invariant=lambda s: s >= 0,
    )
    v_post = check_spec_semver(base, weaker_post, dom_x, dom_y)
    assert not v_post.compatible and v_post.required_bump == "major"
    print(f"  [BREAK] {weaker_post.name} -> {v_post.required_bump}: {v_post.violations[0]}")

    # 5d: Invariant weakening (s >= -1 instead of s >= 0): MAJOR break!
    weaker_inv = Contract(
        name="v1.1-bad-inv: weakened invariant s >= 0 to s >= -1",
        pre=lambda x: x >= 0,
        post=lambda x, y: y >= x,
        invariant=lambda s: s >= -1,
    )
    v_inv = check_spec_semver(base, weaker_inv, dom_x, dom_y)
    assert not v_inv.compatible and v_inv.required_bump == "major"
    print(f"  [BREAK] {weaker_inv.name} -> {v_inv.required_bump}: {v_inv.violations[0]}")

    print("\n=== [6] Rust RFC 2451 Trait Coherence & Orphan-Rule SemVer Checks ===")
    T = TypeExpr("param", "T")
    OldType = TypeExpr("local", "OldType", is_new_in_release=False)
    NewType = TypeExpr("local", "NewType", is_new_in_release=True)
    ForeignVecT = TypeExpr("foreign", "Vec", args=(T,))
    ForeignVecLocal = TypeExpr("foreign", "Vec", args=(TypeExpr("local", "DownstreamLocal"),))
    BoxT = TypeExpr("fundamental", "Box", args=(T,))

    # Verify downstream `impl From<DownstreamLocal> for Vec<DownstreamLocal>` is orphan-legal:
    ds_legal, ds_why = check_rfc2451_orphan_legal(
        TraitImplHeader("From", False, (TypeExpr("local", "DownstreamLocal"),), ForeignVecLocal)
    )
    assert ds_legal, ds_why
    # Verify downstream `impl<T> ForeignTrait<DownstreamLocal> for Vec<T>` is orphan-legal under RFC 2451 (T covered by Vec!):
    ds_rfc2451_legal, ds_rfc2451_why = check_rfc2451_orphan_legal(
        TraitImplHeader("ForeignTrait", False, (TypeExpr("local", "DownstreamLocal"),), ForeignVecT)
    )
    assert ds_rfc2451_legal, ds_rfc2451_why
    # Verify downstream `impl<T> ForeignTrait<DownstreamLocal> for Box<T>` is orphan-ILLEGAL (Box is fundamental -> T uncovered!):
    ds_box_legal, ds_box_why = check_rfc2451_orphan_legal(
        TraitImplHeader("ForeignTrait", False, (TypeExpr("local", "DownstreamLocal"),), BoxT)
    )
    assert not ds_box_legal, ds_box_why
    print(f"  Orphan check Vec<T> (covered): legal={ds_rfc2451_legal}; Box<T> (fundamental): legal={ds_box_legal}")

    coherence_cases = [
        ("impl<T> OldTrait<T> for OldType", TraitImplHeader("OldTrait", True, (T,), OldType), "major"),
        ("impl<T> OldTrait for T (blanket)", TraitImplHeader("OldTrait", True, (), T), "major"),
        ("impl<T> From<T> for Vec<T>", TraitImplHeader("From", False, (T,), ForeignVecT), "major"),
        ("impl<T> ForeignTrait<NewType> for Vec<T>", TraitImplHeader("ForeignTrait", False, (NewType,), ForeignVecT), "minor"),
        ("impl<T> ForeignTrait<NewType> for Box<T>", TraitImplHeader("ForeignTrait", False, (NewType,), BoxT), "major"),
    ]
    for label, hdr, expected in coherence_cases:
        bump, why = check_rfc2451_upstream_impl_addition_semver(hdr)
        assert bump == expected, f"{label}: expected {expected}, got {bump} ({why})"
        print(f"  [{bump.upper():5s}] {label}: {why}")

    print("\n=== [7] Read-Only Store Epoch `mtime` Freshness Trap (Nix + Lake/Cargo) ===")
    nix_equal = simulate_mtime_freshness(input_mtime=1, artifact_mtime=1, input_hash="abc123", recorded_hash="abc123")
    assert not nix_equal["strict_mtime_up_to_date"] and nix_equal["content_hash_up_to_date"]
    nix_backdated = simulate_mtime_freshness(input_mtime=0, artifact_mtime=1, input_hash="abc123", recorded_hash="abc123")
    assert nix_backdated["strict_mtime_up_to_date"] and nix_backdated["content_hash_up_to_date"]
    print(f"  Nix epoch=1 vs epoch=1: {nix_equal} (strict `<` triggers false rebuild!)")
    print(f"  Backdated input=0 vs artifact=1: {nix_backdated}")

    print("\nALL VERIFICATION CHECKS PASSED.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
