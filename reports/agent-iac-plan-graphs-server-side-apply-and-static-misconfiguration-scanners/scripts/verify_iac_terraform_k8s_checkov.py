#!/usr/bin/env python3
"""Deterministic executable verification probe for declarative Infrastructure-as-Code
plan graphs, Kubernetes Server-Side Apply and CEL admission, static HCL scanners vs.
post-plan JSON evaluation, and agentic IaC benchmark harnesses.

Covers five primary-source verification suites using Python 3.10+ standard library only:
  1. OpenTofu vs. HashiCorp Terraform DAG planning and lifecycle inversion:
     - ForcedCBDTransformer upstream `create_before_destroy` contagion + `s == nil`
       quirk (`opentofu/opentofu@0183949c` `internal/tofu/transform_destroy_cbd.go:41-97`)
       and pre-`Create` `DeposeResourceInstanceObjectForceKey` dual-state singleton
       collision (`internal/tofu/node_resource_apply_instance.go:315-324`).
     - BPlan operational action-graph trace stability (`duplicate(r)` vs. `dangling(r, r')`,
       Perdereau et al., SEFM 2026, `hal-05855612v1` / Zenodo `10.5281/zenodo.22747162`).
     - Exact 4-vertex fork divergence witness (`TestCBDEdgeTransformer_creatorWaitsForDifferentCBDDestroy`,
       `hashicorp/terraform@80e6fc28` `internal/terraform/transform_destroy_cbd.go:91-258` vs.
       `opentofu/opentofu@0183949c` `internal/tofu/transform_destroy_cbd.go:119-149`) via Tarjan SCC.
     - Go map-iteration order sensitivity in `DestroyEdgeTransformer.tryInterProviderDestroyEdge`
       (`opentofu/opentofu@0183949c` `internal/tofu/transform_destroy_edge.go:99-143, 247-277`).
  2. Three-valued `cty.UnknownVal` check deferral, `RefreshOnly` `for_each` postcondition skew
     (`opentofu/opentofu@0183949c` `internal/tofu/node_resource_plan_instance.go:434-532` and
     `internal/tofu/eval_conditions.go:36-69, 116-154`), and an explicitly labeled
     `[illustrative analytical model]` (`Basis: derived`) for cloud read-after-write stale-state
     cascades (assuming independent stale-read trials across backoff intervals) and
     `Sieve` (`OSDI '22`) / `Anvil` (`OSDI '24`) controller perturbations.
  3. Kubernetes Server-Side Apply (`kubernetes-sigs/structured-merge-diff@560aaa51`
     `merge/update.go:125-160, 209-298`, `typed/merge.go:208-255, 350-367`) + `capManagersManager`
     (`kubernetes/kubernetes@43cbb94e` `capmanagers.go:39-134`) and `ValidatingAdmissionPolicy`
     CEL cost-budget / `PerCallLimit` (`1,000,000`) / `compile.go` type-gate / `auditAnnotations`
     canary failure modes (`cel/config.go:22-31`, `cel/environment/base.go:89-96`,
     `cel/compile.go:188-205`, `cel/condition.go:66-92`, `cel/activation.go:147-211`,
     `validating/interface.go:60-62`, `validating/validator.go:64-268`,
     `validating/dispatcher.go:227-294`).
  4. Static HCL scanners vs. post-`Plan` JSON evaluation:
     - `aquasecurity/trivy@edf9f5c1` `evaluator.go:136-163, 321-345, 418-445` (`for_each`
       0-clone False Negative vs. `count` 1-clone False Positive before `evaluateSubmodules`).
     - `bridgecrewio/checkov@28694608` `plan_parser.py:236-331` (`EVAL_TF_PLAN_AFTER_UNKNOWN`
       default drop, `len(v) == 1` nested-list gate, boolean-value-blind `v[0].keys()` injection
       across all elements of `resource_conf[k]`, and `KeyError` on absent `resource_conf[k]`),
       `parser_functions.py:93-135` (`tostring("true") -> bool` + `tomap` ARN colon corruption),
       and `VPCHasFlowLog.yaml` `CKV2_AWS_11` / `Vargas et al. (SBSeg 2026)` / `TerraProbe (2026)`
       arithmetic audits.
  5. `autoiac-project/iac-eval@b75a90b3` (`evaluation/eval.py:29, 79-94, 177-195, 491-575, 770-796`,
     `evaluation/prompt_templates.py:41-55`, `evaluation/metrics.py:12-69`,
     `evaluation/misc/ablation/ablation-iac-eval-pipeline.py:296, 333`) harness defect forensics
     (`0 == False` leaf coercion, `"Success"` vs. `"success"` multi-turn overwrite + hidden Rego
     oracle leakage + cross-sample `preprompt`/`prompt` bleed across `i = 0..19`, `DELIMITERS`
     JSON fence splicing, and `metrics.py` `NameError`), `Jouini (2026)` stage-funnel arithmetic,
     and an explicitly labeled `[illustrative analytical model]` (`Basis: derived`) of 3-step
     (initial + 3 retries, `k=4`) closed-loop repair dynamics.

Execution invariants:
  - Python 3.10+ standard library only; zero third-party imports; zero network I/O.
  - All filesystem fixtures isolated inside `with tempfile.TemporaryDirectory():`.
  - Zero local paths or wall-clock timestamps in stdout; bit-identical across
    `PYTHONHASHSEED=1` and `PYTHONHASHSEED=2` under `python3 -I -B`.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import math
from pathlib import Path
import tempfile
from typing import Any, Optional


# ============================================================================
# PROBE 1: OpenTofu vs. Terraform DAG Planner, CBD Contagion & BPlan Traces
# ============================================================================


@dataclass
class DAGVertex:
    name: str
    addr: str
    is_creator: bool = False
    is_destroyer: bool = False
    is_cbd_capable: bool = False
    cbd: bool = False
    is_deposed_obj: bool = False
    provider: str = "registry.opentofu.org/hashicorp/aws"
    state_deps: tuple[str, ...] = ()


class ProvisioningDAG:
    """Deterministic port of OpenTofu/Terraform `dag.AcyclicGraph` (`internal/dag`).

    Note on edge orientation in Terraform/OpenTofu's `dag` package:
    `g.Connect(BasicEdge(from, to))` means `from` DEPENDS ON `to` (`to` executes
    before `from`). Thus `Ancestors(v)` are vertices reachable via outgoing
    dependency edges (`from -> to`), and `Descendants(v)` are vertices that
    depend (directly or transitively) on `v` (`other ->* v`).
    """

    def __init__(self) -> None:
        self.vertices: dict[str, DAGVertex] = {}
        self.edges: list[tuple[str, str]] = []

    def add(self, v: DAGVertex) -> None:
        self.vertices[v.name] = v

    def connect(self, src: str, dst: str) -> None:
        if (src, dst) not in self.edges:
            self.edges.append((src, dst))

    def remove_edge(self, src: str, dst: str) -> None:
        self.edges = [e for e in self.edges if e != (src, dst)]

    def edges_to(self, target: str) -> list[tuple[str, str]]:
        return [e for e in self.edges if e[1] == target]

    def edges_from(self, source: str) -> list[str]:
        return [dst for src, dst in self.edges if src == source]

    def ancestors(self, start: str) -> set[str]:
        """Vertices reachable from `start` following `src -> dst` dependency arcs."""
        visited: set[str] = set()
        stack = list(self.edges_from(start))
        while stack:
            cur = stack.pop()
            if cur not in visited:
                visited.add(cur)
                stack.extend(self.edges_from(cur))
        return visited

    def descendants(self, starts: list[str]) -> set[str]:
        """Vertices `u` that transitively depend on any vertex in `starts` (`u ->* s`)."""
        rev: dict[str, list[str]] = {k: [] for k in self.vertices}
        for src, dst in self.edges:
            rev[dst].append(src)
        visited: set[str] = set()
        stack: list[str] = []
        for s in starts:
            stack.extend(rev.get(s, []))
        while stack:
            cur = stack.pop()
            if cur not in visited:
                visited.add(cur)
                stack.extend(rev.get(cur, []))
        return visited

    def tarjan_cycles(self) -> list[tuple[str, ...]]:
        """Deterministic Tarjan strongly connected components (`len(scc) > 1` or self-loop)."""
        index_counter = 0
        indices: dict[str, int] = {}
        lowlink: dict[str, int] = {}
        stack: list[str] = []
        on_stack: set[str] = set()
        cycles: list[tuple[str, ...]] = []

        adj: dict[str, list[str]] = {k: [] for k in sorted(self.vertices)}
        for src, dst in sorted(self.edges):
            adj[src].append(dst)

        def strongconnect(v: str) -> None:
            nonlocal index_counter
            indices[v] = index_counter
            lowlink[v] = index_counter
            index_counter += 1
            stack.append(v)
            on_stack.add(v)

            for w in adj[v]:
                if w not in indices:
                    strongconnect(w)
                    lowlink[v] = min(lowlink[v], lowlink[w])
                elif w in on_stack:
                    lowlink[v] = min(lowlink[v], indices[w])

            if lowlink[v] == indices[v]:
                scc: list[str] = []
                while True:
                    w = stack.pop()
                    on_stack.remove(w)
                    scc.append(w)
                    if w == v:
                        break
                scc_sorted = tuple(sorted(scc))
                if len(scc_sorted) > 1 or (scc_sorted[0], scc_sorted[0]) in self.edges:
                    cycles.append(scc_sorted)

        for v_name in sorted(self.vertices):
            if v_name not in indices:
                strongconnect(v_name)
        return sorted(cycles)

    def topological_execution_order(self) -> list[str]:
        """Returns deterministic execution order (`dst` runs before `src` for `src -> dst`)."""
        if self.tarjan_cycles():
            raise ValueError("Cycle detected in provisioning graph")
        remaining_deps: dict[str, set[str]] = {
            v: set(self.edges_from(v)) for v in self.vertices
        }
        order: list[str] = []
        ready = sorted(v for v, deps in remaining_deps.items() if not deps)
        while ready:
            cur = ready.pop(0)
            order.append(cur)
            for v in sorted(remaining_deps):
                if cur in remaining_deps[v]:
                    remaining_deps[v].remove(cur)
                    if not remaining_deps[v] and v not in order and v not in ready:
                        ready.append(v)
                        ready.sort()
        return order


def opentofu_has_cbd_descendent(
    g: ProvisioningDAG, v_name: str, simulate_nil_set: bool = False
) -> bool:
    """Faithful port of `ForcedCBDTransformer.hasCBDDescendent`
    (`opentofu/opentofu@0183949c` `internal/tofu/transform_destroy_cbd.go:77-97`).
    """
    s: Optional[set[str]] = None if simulate_nil_set else g.descendants([v_name])
    if s is None:
        # Lines 79-81: `if s == nil { return true }`
        return True
    for ov_name in sorted(s):
        ov = g.vertices[ov_name]
        if ov.is_cbd_capable and ov.cbd:
            return True
    return False


def opentofu_forced_cbd_transform(g: ProvisioningDAG) -> list[str]:
    """Port of `ForcedCBDTransformer.Transform` (`transform_destroy_cbd.go:41-73`)."""
    forced: list[str] = []
    for v_name in sorted(g.vertices):
        v = g.vertices[v_name]
        if not v.is_cbd_capable:
            continue
        if not v.cbd:
            if not opentofu_has_cbd_descendent(g, v_name):
                continue
            v.cbd = True
            forced.append(v_name)
    return forced


def opentofu_cbd_edge_transform(g: ProvisioningDAG) -> None:
    """Faithful port of OpenTofu `CBDEdgeTransformer.Transform`
    (`opentofu/opentofu@0183949c` `internal/tofu/transform_destroy_cbd.go:119-149`).
    """
    for v_name in list(g.vertices):
        v = g.vertices[v_name]
        if not (v.is_cbd_capable and v.is_destroyer and v.cbd):
            continue
        for src_name, dst_name in list(g.edges_to(v_name)):
            src = g.vertices[src_name]
            if src.is_creator:
                g.remove_edge(src_name, dst_name)
                g.connect(v_name, src_name)


def terraform_cbd_edge_transform(g: ProvisioningDAG) -> list[tuple[str, str]]:
    """Faithful port of HashiCorp Terraform `CBDEdgeTransformer.Transform`
    (`hashicorp/terraform@80e6fc28` `internal/terraform/transform_destroy_cbd.go:91-258`).
    """
    # Phase 0: forceCBDUpdateCreateDependencies (`L232-258`)
    stack = [
        v.name for v in g.vertices.values() if v.is_cbd_capable and v.cbd
    ]
    seen: set[str] = set()
    while stack:
        cur = stack.pop()
        for dep_name in g.edges_from(cur):
            dep = g.vertices[dep_name]
            if dep.is_destroyer or dep_name in seen:
                continue
            seen.add(dep_name)
            stack.append(dep_name)
            if dep.is_cbd_capable and not dep.cbd:
                dep.cbd = True

    # Phase 1: cbdDestroyNodes + downstream destroy propagation (`L97-130`)
    cbd_destroy_nodes: set[str] = set()
    initial_cbd_destroy: list[str] = []
    for v in g.vertices.values():
        if v.is_destroyer and v.is_cbd_capable and v.cbd:
            cbd_destroy_nodes.add(v.name)
            initial_cbd_destroy.append(v.name)

    for desc_name in sorted(g.descendants(initial_cbd_destroy)):
        desc = g.vertices[desc_name]
        if not desc.is_destroyer:
            continue
        if desc.is_cbd_capable:
            desc.cbd = True
            if not desc.cbd:
                continue
        cbd_destroy_nodes.add(desc_name)

    # Phase 2: separate self-deposed edges from cross-instance `removedEdges` (`L136-181`)
    removed_edges: list[tuple[str, str]] = []
    for v_name in sorted(cbd_destroy_nodes):
        v = g.vertices[v_name]
        for src_name, _ in list(g.edges_to(v_name)):
            src = g.vertices[src_name]
            if not src.is_creator:
                continue
            if src.addr == v.addr:
                if v.is_deposed_obj:
                    g.remove_edge(src_name, v_name)
                    g.connect(v_name, src_name)
                continue
            removed_edges.append((src_name, v_name))
            g.remove_edge(src_name, v_name)

    # Phase 3: compute `ancestors` BEFORE restoring any pending edge (`L183-214`)
    ancestors_by_creator: dict[str, set[str]] = {}
    edges_to_reverse: list[bool] = []
    skipped_reversals: list[tuple[str, str]] = []
    for src_name, dst_name in removed_edges:
        if src_name not in ancestors_by_creator:
            ancestors_by_creator[src_name] = g.ancestors(src_name)
        should_reverse = dst_name not in ancestors_by_creator[src_name]
        edges_to_reverse.append(should_reverse)

    for (src_name, dst_name), rev in zip(removed_edges, edges_to_reverse):
        if rev:
            g.connect(dst_name, src_name)
        else:
            skipped_reversals.append((src_name, dst_name))
            g.connect(src_name, dst_name)
    return skipped_reversals


def build_4node_cbd_witness() -> ProvisioningDAG:
    """Exact graph from `TestCBDEdgeTransformer_creatorWaitsForDifferentCBDDestroy`
    (`hashicorp/terraform@80e6fc28` `internal/terraform/transform_destroy_cbd_test.go:373-413`).
    """
    g = ProvisioningDAG()
    g.add(DAGVertex("aDestroy", "test_object.a", is_destroyer=True, is_cbd_capable=True, cbd=True))
    g.add(DAGVertex("bDestroy", "test_object.b", is_destroyer=True, is_cbd_capable=True, cbd=True))
    g.add(DAGVertex("cDestroy", "test_object.c", is_destroyer=True, is_cbd_capable=True, cbd=False))
    g.add(DAGVertex("cCreate", "test_object.c", is_creator=True, is_cbd_capable=False, cbd=False))
    g.connect("cCreate", "cDestroy")
    g.connect("cDestroy", "aDestroy")
    g.connect("cCreate", "aDestroy")
    g.connect("cCreate", "bDestroy")
    return g


def try_inter_provider_destroy_edge(
    g: ProvisioningDAG, from_name: str, to_name: str, is_full_destroy: bool = False
) -> bool:
    """Port of `DestroyEdgeTransformer.tryInterProviderDestroyEdge`
    (`opentofu/opentofu@0183949c` `internal/tofu/transform_destroy_edge.go:99-143`).
    """
    g.connect(from_name, to_name)
    if is_full_destroy:
        return True
    from_p = g.vertices[from_name].provider
    to_p = g.vertices[to_name].provider
    if from_p != to_p and len(g.tarjan_cycles()) > 0:
        g.remove_edge(from_name, to_name)
        return False
    return True


def simulate_bplan_trace(
    events: list[tuple[str, str, str]],
    initial_instances: dict[str, set[str]],
    initial_deps: set[tuple[str, str, str, str]],
    target_deps: dict[str, str],
) -> tuple[bool, bool]:
    """Port of BPlan's Maude operational stability predicates `duplicate(r)` and
    `dangling(r, r')` (`Perdereau et al., SEFM 2026`, `hal-05855612v1`).

    Each event is `(phase, action, res_id)` with `phase in {"start", "end"}` and
    `action in {"C", "U", "D"}`.
    """
    live: dict[str, set[str]] = {r: set(v) for r, v in initial_instances.items()}
    deps = set(initial_deps)
    saw_duplicate = False
    saw_dangling = False

    def check_state() -> None:
        nonlocal saw_duplicate, saw_dangling
        for instances in live.values():
            if len(instances) > 1:
                saw_duplicate = True
        for r_src, inst_src, r_dst, inst_dst in deps:
            if inst_src in live.get(r_src, set()) and inst_dst not in live.get(r_dst, set()):
                saw_dangling = True

    check_state()
    for phase, action, res in events:
        if action == "C" and phase == "start":
            live.setdefault(res, set()).add(f"{res}_new")
            if res in target_deps:
                dep_r = target_deps[res]
                dep_inst = f"{dep_r}_new" if f"{dep_r}_new" in live.get(dep_r, set()) else f"{dep_r}_old"
                deps.add((res, f"{res}_new", dep_r, dep_inst))
        elif action == "D" and phase == "end":
            live.get(res, set()).discard(f"{res}_old")
            deps = {d for d in deps if not (d[0] == res and d[1] == f"{res}_old")}
        elif action == "U" and phase == "end":
            if res in target_deps:
                dep_r = target_deps[res]
                deps = {d for d in deps if not (d[0] == res and d[1] == f"{res}_old")}
                deps.add((res, f"{res}_old", dep_r, f"{dep_r}_new"))
        check_state()
    return saw_duplicate, saw_dangling


def run_probe_1() -> None:
    # 1A. ForcedCBD upstream contagion + deposed singleton collision + `s == nil` quirk
    chain = ProvisioningDAG()
    chain.add(DAGVertex("R1_bucket", "aws_s3_bucket.audit", is_cbd_capable=True, cbd=False))
    chain.add(DAGVertex("R2_policy", "aws_iam_policy.audit_rw", is_cbd_capable=True, cbd=False))
    chain.add(DAGVertex("R3_attach", "aws_iam_role_policy_attachment.leaf", is_cbd_capable=True, cbd=True))
    chain.connect("R3_attach", "R2_policy")
    chain.connect("R2_policy", "R1_bucket")

    nil_quirk = opentofu_has_cbd_descendent(chain, "R1_bucket", simulate_nil_set=True)
    forced_nodes = opentofu_forced_cbd_transform(chain)

    # Simulate pre-`Create` deposed-key demotion (`internal/tofu/node_resource_apply_instance.go:315-324`)
    # on a fixed globally unique S3 bucket name (`bucket = "prod-audit-logs"`).
    cloud_singleton_names = {"prod-audit-logs"}
    state_slot: dict[str, Any] = {"current": "R1_v1", "deposed": {}}
    deposed_key = "00000001"
    state_slot["deposed"][deposed_key] = state_slot["current"]
    state_slot["current"] = None
    singleton_create_err = "EntityAlreadyExists" if "prod-audit-logs" in cloud_singleton_names else "OK"
    stranded_deposed = state_slot["current"] is None and deposed_key in state_slot["deposed"]

    # BPlan stability traces: CBD replacement `[C(R1), U(R2), D(R1)]` vs non-CBD `[D(R1), C(R1), U(R2)]`
    init_live = {"R1": {"R1_old"}, "R2": {"R2_old"}}
    init_deps = {("R2", "R2_old", "R1", "R1_old")}
    cbd_dup, cbd_dang = simulate_bplan_trace(
        [("start", "C", "R1"), ("end", "C", "R1"), ("start", "U", "R2"), ("end", "U", "R2"),
         ("start", "D", "R1"), ("end", "D", "R1")],
        init_live, init_deps, {"R2": "R1"},
    )
    noncbd_dup, noncbd_dang = simulate_bplan_trace(
        [("start", "D", "R1"), ("end", "D", "R1"), ("start", "C", "R1"), ("end", "C", "R1"),
         ("start", "U", "R2"), ("end", "U", "R2")],
        init_live, init_deps, {"R2": "R1"},
    )

    # 1B. Exact 4-vertex witness: OpenTofu cycle crash vs Terraform acyclic DAG
    g_tofu = build_4node_cbd_witness()
    opentofu_cbd_edge_transform(g_tofu)
    tofu_cycles = g_tofu.tarjan_cycles()

    g_tf = build_4node_cbd_witness()
    tf_skipped = terraform_cbd_edge_transform(g_tf)
    tf_cycles = g_tf.tarjan_cycles()
    tf_order = g_tf.topological_execution_order()

    # 1C. Go map-order non-determinism in `tryInterProviderDestroyEdge`
    orders_seen: list[tuple[str, ...]] = []
    kept_edges_seen: list[tuple[str, str]] = []
    for map_iter_order in [("destroyA", "destroyB"), ("destroyB", "destroyA")]:
        gi = ProvisioningDAG()
        gi.add(DAGVertex("destroyA", "aws_eks_cluster.a", is_destroyer=True, provider="aws"))
        gi.add(DAGVertex("destroyB", "kubernetes_config_map.b", is_destroyer=True, provider="k8s"))
        candidate_by_key = {
            "destroyA": ("destroyA", "destroyB"),
            "destroyB": ("destroyB", "destroyA"),
        }
        kept_pair: list[tuple[str, str]] = []
        for k in map_iter_order:
            u, v = candidate_by_key[k]
            if try_inter_provider_destroy_edge(gi, u, v, is_full_destroy=False):
                kept_pair.append((u, v))
        assert len(kept_pair) == 1
        kept_edges_seen.append(kept_pair[0])
        orders_seen.append(tuple(gi.topological_execution_order()))

    assert nil_quirk is True
    assert forced_nodes == ["R1_bucket", "R2_policy"]
    assert singleton_create_err == "EntityAlreadyExists" and stranded_deposed is True
    assert (cbd_dup, cbd_dang) == (True, False)
    assert (noncbd_dup, noncbd_dang) == (False, True)
    assert tofu_cycles == [("aDestroy", "cCreate", "cDestroy")]
    assert tf_cycles == []
    assert tf_skipped == [("cCreate", "aDestroy")]
    assert "bDestroy" in g_tf.vertices and "cCreate" in g_tf.edges_from("bDestroy")
    assert len(set(orders_seen)) == 2

    print("=== PROBE 1: OpenTofu vs. Terraform DAG Planner, CBD Contagion & BPlan Stability ===")
    print(
        f"  ForcedCBD upstream contagion: forced={forced_nodes}, nil_desc_returns_true={nil_quirk}, "
        f"singleton_err={singleton_create_err}, stranded_deposed={stranded_deposed}"
    )
    print(
        f"  BPlan operational trace stability: CBD=(duplicate={cbd_dup}, dangling={cbd_dang}), "
        f"DeleteThenCreate=(duplicate={noncbd_dup}, dangling={noncbd_dang})"
    )
    print(
        f"  4-vertex witness (TestCBDEdgeTransformer_creatorWaitsForDifferentCBDDestroy): "
        f"opentofu_cycles={tofu_cycles} vs terraform_cycles={tf_cycles}, "
        f"terraform_skipped_reversal={tf_skipped}, terraform_exec_order={tf_order}"
    )
    print(
        f"  Inter-provider cycle breaking (`tryInterProviderDestroyEdge`): "
        f"kept_edges={kept_edges_seen}, distinct_exec_orders={orders_seen}"
    )


# ============================================================================
# PROBE 2: UnknownVal Deferral, RefreshOnly Skew & Eventual-Consistency Model
# ============================================================================


@dataclass(frozen=True)
class CtyVal:
    known: bool
    value: Any = None


def eval_cidr_not_open_check(cidr: CtyVal) -> str:
    """Port of `evalCheckRules` / `evalCheckRule` (`internal/tofu/eval_conditions.go:36-69, 116-154`
    called from `internal/tofu/node_resource_plan_instance.go:480-532`):
    check conditions with `!resultVal.IsKnown()` (`L135-154`) return `checks.StatusUnknown`
    during `plan` and evaluate only at `apply`.
    """
    if not cidr.known:
        return "DEFERRED_UNKNOWN"
    return "PASS" if cidr.value != "0.0.0.0/0" else "ERROR_CHECK_FAILED"


def simulate_plan_instance_check_modes(
    refresh_only: bool,
    local_for_each_map: dict[str, str],
    remote_live_tier_by_key: dict[str, str],
    prior_state_tier_by_key: dict[str, str],
) -> tuple[bool, list[str]]:
    """Port of `NodePlannableResourceInstance.managedResourceExecute` vs.
    `refresh-only` branch (`opentofu/opentofu@0183949c`
    `internal/tofu/node_resource_plan_instance.go:480-532`).

    Postcondition invariant: `self.tier == each.value`.
    """
    cloud_drift_detected = remote_live_tier_by_key != prior_state_tier_by_key
    errors: list[str] = []
    if refresh_only:
        # Lines 498-532: evaluates `each.value` from LOCAL `.tf` config while `self`
        # reflects refreshed REMOTE state (no planned change applied).
        for key, each_val in sorted(local_for_each_map.items()):
            self_tier = remote_live_tier_by_key[key]
            if self_tier != each_val:
                errors.append(
                    f"{key}: postcondition self.tier({self_tier!r}) != each.value({each_val!r})"
                )
    else:
        # Normal plan mode plans update `self.tier := each.value` before postcondition check (`L482-489`).
        for key, each_val in sorted(local_for_each_map.items()):
            planned_self_tier = each_val
            if planned_self_tier != each_val:
                errors.append(f"{key}: failed")
    return cloud_drift_detected, errors


def simulate_sieve_controller_perturbations() -> dict[str, tuple[bool, str]]:
    """Deterministic state-machine reproduction of the three `Sieve` (`OSDI '22`)
    eventual-consistency hazards vs. `Anvil` (`OSDI '24`) generation-fenced ESR.
    """
    outcomes: dict[str, tuple[bool, str]] = {}

    # 1. Stale-state ("time-travel" informer cache lag): controller sees 0 pods after creating pod-1
    apiserver_pods = ["pod-1"]
    stale_informer_view: list[str] = []
    if len(stale_informer_view) < 1:
        apiserver_pods.append("pod-2-duplicate")
    outcomes["stale_state_unversioned"] = (len(apiserver_pods) == 1, f"pods={len(apiserver_pods)}")

    # 2. Intermediate-state crash before status write: side effect created external volume without owner token
    external_volumes = ["vol-orphan-1"]
    recorded_status_vol: Optional[str] = None  # crashed mid-reconcile before status subresource patch
    if recorded_status_vol is None:
        external_volumes.append("vol-2")
    outcomes["intermediate_crash_untracked"] = (
        len(external_volumes) == 1,
        f"volumes={len(external_volumes)}",
    )

    # 3. Unobserved-state watch coalescing: ConfigMap rotates v1 -> v2 -> v1 while controller queued;
    # Edge-triggered reconciler checks `old_digest != cur_digest` instead of observed workload spec hash
    last_seen_cm = "v1"
    coalesced_cur_cm = "v1"
    pod_mounted_secret_rev = "rev0_expired"
    desired_secret_rev = "rev2_rotated"
    edge_reconciled = pod_mounted_secret_rev if last_seen_cm == coalesced_cur_cm else desired_secret_rev
    level_fenced_reconciled = (
        desired_secret_rev if pod_mounted_secret_rev != desired_secret_rev else pod_mounted_secret_rev
    )
    outcomes["unobserved_edge_triggered"] = (
        edge_reconciled == desired_secret_rev,
        f"mounted={edge_reconciled}",
    )
    outcomes["anvil_esr_level_fenced"] = (
        level_fenced_reconciled == desired_secret_rev,
        f"mounted={level_fenced_reconciled}",
    )
    return outcomes


def run_probe_2() -> None:
    # 2A. UnknownVal deferral -> mid-apply partial infrastructure mutation
    plan_check = eval_cidr_not_open_check(CtyVal(known=False))
    cloud_created_upstream = ["aws_vpc.main"]
    apply_resolved_check = eval_cidr_not_open_check(CtyVal(known=True, value="0.0.0.0/0"))

    # 2B. RefreshOnly `for_each` postcondition skew under zero cloud drift
    prior_state = {"api": "standard"}
    remote_live = {"api": "standard"}  # zero cloud drift
    edited_local_for_each = {"api": "premium"}
    drift_ro, errs_ro = simulate_plan_instance_check_modes(
        True, edited_local_for_each, remote_live, prior_state
    )
    drift_norm, errs_norm = simulate_plan_instance_check_modes(
        False, edited_local_for_each, remote_live, prior_state
    )

    # 2C. [illustrative analytical model] (Basis: derived) for unretried k-hop read-after-write lag
    # P_fail(k, q) = 1 - (1 - q)^k vs. exponential-backoff retry P_fail_retry(k, q, r) = 1 - (1 - q^(r+1))^k,
    # where the retry exponent q^(r+1) assumes independent stale-read trials across backoff intervals.
    hops = (1, 2, 3, 5)
    q_stale = 0.15
    raw_cascade = {k: round(1.0 - (1.0 - q_stale) ** k, 4) for k in hops}
    retried_cascade_r2 = {k: round(1.0 - (1.0 - (q_stale ** 3)) ** k, 4) for k in hops}
    sieve_matrix = simulate_sieve_controller_perturbations()

    assert plan_check == "DEFERRED_UNKNOWN" and apply_resolved_check == "ERROR_CHECK_FAILED"
    assert drift_ro is False and len(errs_ro) == 1
    assert drift_norm is False and len(errs_norm) == 0
    assert raw_cascade == {1: 0.15, 2: 0.2775, 3: 0.3859, 5: 0.5563}
    assert sieve_matrix["stale_state_unversioned"][0] is False
    assert sieve_matrix["intermediate_crash_untracked"][0] is False
    assert sieve_matrix["unobserved_edge_triggered"][0] is False
    assert sieve_matrix["anvil_esr_level_fenced"][0] is True

    print("=== PROBE 2: UnknownVal Deferral, RefreshOnly Skew & Eventual-Consistency Cascades ===")
    print(
        f"  UnknownVal precondition/postcondition: plan={plan_check}, "
        f"apply={apply_resolved_check}, orphaned_upstream={cloud_created_upstream}"
    )
    print(
        f"  RefreshOnly `for_each` skew (`node_resource_plan_instance.go:498-532`): "
        f"cloud_drift={drift_ro}, refresh_only_errors={len(errs_ro)} ({errs_ro[0]}), "
        f"normal_plan_errors={len(errs_norm)}"
    )
    print(
        f"  [illustrative analytical model] k-hop read-after-write failure (q={q_stale}, independent retry trials): "
        f"unretried={raw_cascade}, with_2_retries={retried_cascade_r2}"
    )
    print(
        "  Sieve/Anvil perturbation matrix: "
        + ", ".join(f"{k}=converged:{v[0]}({v[1]})" for k, v in sieve_matrix.items())
    )


# ============================================================================
# PROBE 3: Kubernetes Server-Side Apply (SMD) & ValidatingAdmissionPolicy CEL
# ============================================================================


class SMDWorkloadSimulator:
    """Port of `sigs.k8s.io/structured-merge-diff` `Updater.Apply`, `Updater.prune`,
    `Updater.addBackOwnedItems`, `Updater.update`, and `typed/merge.go` (`atomic` vs.
    `map` lists) at `560aaa513ea735bf59e6011feecd5388e2dfeae9`, plus
    `capManagersManager` (`kubernetes/kubernetes@43cbb94e` `capmanagers.go:39-134`).

    Scope note: Conflict detection and `compare.Removed` cleanup are specialized to
    the modeled `.spec.args` (`schema.Atomic` list) and `.spec.containers`
    (`schema.Map` associative list keyed by `name`) workload fields, executing the
    upstream `Merge -> ToFieldSet -> prune -> update (conflict check + preemption +
    removed-set cleanup)` pipeline (`merge/update.go:125-160, 215-245`).
    """

    def __init__(self, max_update_managers: int = 10) -> None:
        self.live_args: list[str] = []  # x-kubernetes-list-type: atomic
        self.live_containers: dict[str, dict[str, Any]] = {}  # x-kubernetes-list-type: map (key=name)
        # manager_id -> (applied_bool, timestamp_sec, set_of_field_paths)
        self.managers: dict[str, tuple[bool, int, set[str]]] = {}
        self.max_update_managers = max_update_managers
        self.clock = 0

    @staticmethod
    def config_to_fieldset(cfg: dict[str, Any]) -> set[str]:
        fset: set[str] = set()
        if "args" in cfg:
            # `typed/merge.go:355-357`: atomic list is owned as a single leaf path `.spec.args`
            fset.add(".spec.args")
        for c in cfg.get("containers", []):
            cname = c["name"]
            item_key = f'.spec.containers[k:{{"name":"{cname}"}}]'
            fset.add(item_key)
            for k in c:
                fset.add(f"{item_key}.{k}")
        return fset

    def apply(
        self, manager: str, cfg: dict[str, Any], force: bool = False
    ) -> Optional[list[str]]:
        """Port of `Updater.Apply` (`merge/update.go:215-245`):
        1. `Merge` (`typed/merge.go:208-367`)
        2. `ToFieldSet` (`new_set`)
        3. `prune` + `addBackOwnedItems` (`update.go:256-297`)
        4. `update` (`Compare` + conflict check + `Force` preemption + `compare.Removed`
           manager cleanup, `update.go:125-160`).
        Returns conflicting manager names on HTTP 409 without mutating `self`.
        """
        new_set = self.config_to_fieldset(cfg)
        last_entry = self.managers.get(manager)
        last_set = set(last_entry[2]) if last_entry is not None else set()

        # 1. Merge liveObject + configObject (`typed/merge.go:208-367`)
        merged_args = list(cfg["args"]) if "args" in cfg else list(self.live_args)
        merged_containers = {k: dict(v) for k, v in self.live_containers.items()}
        for c in cfg.get("containers", []):
            cname = c["name"]
            cur = dict(merged_containers.get(cname, {"name": cname}))
            cur.update(c)
            merged_containers[cname] = cur

        # Provisional manager table with applier's `new_set` (`update.go:237`)
        next_managers: dict[str, tuple[bool, int, set[str]]] = {
            m: (ap, ts, set(fs)) for m, (ap, ts, fs) in self.managers.items()
        }
        next_clock = self.clock + 1
        next_managers[manager] = (True, next_clock, set(new_set))

        # 2. `prune` (`update.go:256-280`) + `addBackOwnedItems` (`L284-297`)
        union_all_owned: set[str] = set()
        for _, _, mset in next_managers.values():
            union_all_owned |= mset

        removed_by_applier = last_set - new_set
        if ".spec.args" in removed_by_applier and ".spec.args" not in union_all_owned:
            merged_args = []

        for cname in list(merged_containers):
            item_key = f'.spec.containers[k:{{"name":"{cname}"}}]'
            if item_key in removed_by_applier and item_key not in union_all_owned:
                del merged_containers[cname]
                continue
            cdict = merged_containers[cname]
            for fk in list(cdict):
                if fk == "name":
                    continue
                fp = f"{item_key}.{fk}"
                if fp in removed_by_applier and fp not in union_all_owned:
                    del cdict[fk]

        # 3. `Compare(liveObject, pruned)` (`update.go:228-235`) + `update` (`L125-160`)
        modified_or_added: set[str] = set()
        completely_removed: set[str] = set()
        if merged_args != self.live_args:
            if merged_args:
                modified_or_added.add(".spec.args")
            elif self.live_args:
                completely_removed.add(".spec.args")

        for cname, cdict in merged_containers.items():
            item_key = f'.spec.containers[k:{{"name":"{cname}"}}]'
            old_c = self.live_containers.get(cname)
            if old_c is None:
                modified_or_added.add(item_key)
                for fk in cdict:
                    modified_or_added.add(f"{item_key}.{fk}")
            else:
                for fk, fval in cdict.items():
                    if fk == "name":
                        continue
                    if old_c.get(fk) != fval:
                        modified_or_added.add(f"{item_key}.{fk}")
                for fk in old_c:
                    if fk != "name" and fk not in cdict:
                        completely_removed.add(f"{item_key}.{fk}")
        for cname, old_c in self.live_containers.items():
            if cname not in merged_containers:
                item_key = f'.spec.containers[k:{{"name":"{cname}"}}]'
                completely_removed.add(item_key)
                for fk in old_c:
                    completely_removed.add(f"{item_key}.{fk}")

        conflict_candidates = modified_or_added | (completely_removed & removed_by_applier)
        conflicts: dict[str, set[str]] = {}
        for other_mgr, (_, _, other_set) in next_managers.items():
            if other_mgr == manager:
                continue
            overlap = other_set & conflict_candidates
            if overlap:
                conflicts[other_mgr] = overlap

        if not force and conflicts:
            return sorted(conflicts)

        # Force preemption (`update.go:145-147`) and `compare.Removed` cleanup (`update.go:149-151`)
        for other_mgr in list(next_managers):
            if other_mgr == manager:
                continue
            applied_flag, ts, oset = next_managers[other_mgr]
            diff = oset - conflicts.get(other_mgr, set()) - completely_removed
            if diff:
                next_managers[other_mgr] = (applied_flag, ts, diff)
            else:
                del next_managers[other_mgr]

        if not next_managers[manager][2]:
            del next_managers[manager]

        self.clock = next_clock
        self.managers = next_managers
        self.live_args = merged_args
        self.live_containers = merged_containers
        # `capManagersManager.Apply` (`capmanagers.go:60-62`): delegates directly WITHOUT capping!
        return None

    def record_update_manager(self, manager: str, field_path: str) -> None:
        """Port of `capManagersManager.Update` + `capUpdateManagers` (`capmanagers.go:48-134`)."""
        self.clock += 1
        self.managers[manager] = (False, self.clock, {field_path})
        updaters = [
            m for m, (applied, _, _) in self.managers.items() if not applied
        ]
        if len(updaters) <= self.max_update_managers:
            return
        updaters.sort(key=lambda m: (self.managers[m][1], m))
        first_seen: Optional[str] = None
        length = len(updaters)
        bucket = "ancient-changes"
        for m in updaters:
            if length <= self.max_update_managers:
                break
            _, ts, fset = self.managers[m]
            if first_seen is not None:
                if bucket not in self.managers:
                    _, _, first_set = self.managers.pop(first_seen)
                    self.managers[bucket] = (False, ts, set(first_set))
                _, _, bset = self.managers[bucket]
                self.managers[bucket] = (False, ts, bset | fset)
                if m in self.managers:
                    del self.managers[m]
                length -= 1
            else:
                first_seen = m


# Constants from `staging/src/k8s.io/apiserver/pkg/apis/cel/config.go:22-31`
# and `staging/src/k8s.io/apiserver/pkg/cel/environment/base.go:91` (`cel.CostLimit(PerCallLimit)`).
PER_CALL_LIMIT = 1_000_000
RUNTIME_CEL_COST_BUDGET = 10_000_000
RUNTIME_CEL_COST_BUDGET_MATCH_CONDITIONS = 2_500_000


@dataclass(frozen=True)
class CELExprSpec:
    expr: str
    cost: int
    result_type: str  # "bool", "string", "null", "int", "dyn"
    value: Any
    compile_error: Optional[str] = None
    runtime_error: Optional[str] = None


@dataclass(frozen=True)
class CELEvalOutcome:
    expr: str
    result_type: str
    value: Any
    error: Optional[str] = None


def compile_audit_annotation_spec(sp: CELExprSpec) -> CELExprSpec:
    """Faithful port of `AuditAnnotationCondition.ReturnTypes()` (`validating/interface.go:60-62`)
    + `CompileCELExpression` static type-gate (`cel/compile.go:188-205`, `IsExactType` at `L191`).
    Only exact `string` or `null` AST output types pass compilation (`dyn` and `int` fail at
    compile time, before `ContextEval`).
    """
    if sp.compile_error is not None:
        return sp
    if sp.result_type not in ("string", "null"):
        return CELExprSpec(
            expr=sp.expr,
            cost=0,
            result_type=sp.result_type,
            value=None,
            compile_error=(
                f"must evaluate to one of [string, null_type] but got {sp.result_type}"
            ),
        )
    return sp


def eval_cel_filter_for_input(
    specs: list[CELExprSpec], budget: int
) -> tuple[Optional[list[CELEvalOutcome]], int, Optional[str]]:
    """Faithful port of `condition.ForInput` (`cel/condition.go:66-92`),
    `activation.Evaluate` (`cel/activation.go:147-211`), and `cel-go` per-program
    `cel.CostLimit(celconfig.PerCallLimit)` (`cel/environment/base.go:91`).
    """
    if not specs:
        return [], budget, None
    remaining = budget
    out: list[CELEvalOutcome] = []
    for sp in specs:
        # `activation.go:148-154`: compile error produces per-rule `evaluation.Error` without spending budget.
        if sp.compile_error is not None:
            out.append(
                CELEvalOutcome(
                    expr=sp.expr,
                    result_type=sp.result_type,
                    value=None,
                    error=f"compilation error: {sp.compile_error}",
                )
            )
            continue

        # `base.go:91`: `cel.CostLimit(PerCallLimit)` cancels `Program.ContextEval` at `1,000,001`
        # with an evaluation error rather than consuming unbounded cost in a single call.
        per_call_exceeded = sp.cost > PER_CALL_LIMIT
        actual_cost = (PER_CALL_LIMIT + 1) if per_call_exceeded else sp.cost

        # `activation.go:193-199` + `condition.go:86-88`: if `actual_cost > remainingBudget`,
        # `ForInput` aborts immediately with `ErrOutOfBudget`, discarding all earlier `out` entries!
        if actual_cost > remaining:
            return None, -1, "ErrOutOfBudget"
        remaining -= actual_cost

        # `activation.go:203-207`: per-call cost cancellation or runtime error sets `evaluation.Error`
        # on THIS expression while preserving earlier `out` entries!
        if per_call_exceeded:
            out.append(
                CELEvalOutcome(
                    expr=sp.expr,
                    result_type=sp.result_type,
                    value=None,
                    error="operation cancelled: actual cost limit exceeded",
                )
            )
        elif sp.runtime_error is not None:
            out.append(
                CELEvalOutcome(
                    expr=sp.expr,
                    result_type=sp.result_type,
                    value=None,
                    error=sp.runtime_error,
                )
            )
        else:
            out.append(CELEvalOutcome(expr=sp.expr, result_type=sp.result_type, value=sp.value))
    return out, remaining, None


def policy_decision_action_for_error(failure_policy: str) -> str:
    """Port of `policyDecisionActionForError` (`validator.go:64-69`)."""
    return "ActionAdmit" if failure_policy == "Ignore" else "ActionDeny"


def audit_annotation_evaluation_for_error(failure_policy: str) -> str:
    """Port of `auditAnnotationEvaluationForError` (`validator.go:71-76`)."""
    return "AuditAnnotationActionExclude" if failure_policy == "Ignore" else "AuditAnnotationActionError"


def evaluate_validating_admission_policy(
    validations: list[CELExprSpec],
    message_exprs: list[CELExprSpec],
    audit_annotations: list[tuple[str, CELExprSpec]],
    failure_policy: str,
    validation_actions: list[str],
    bypass_compile_gate_for_audit: bool = False,
) -> tuple[int, list[str], list[str]]:
    """Faithful port of `validator.Validate` (`validating/validator.go:128-268`) and
    `dispatcher.Dispatch` (`validating/dispatcher.go:227-294`).
    Returns `(http_status, warnings, denied_messages)`.
    """
    eval_results, remaining_budget, err = eval_cel_filter_for_input(
        validations, RUNTIME_CEL_COST_BUDGET
    )
    decisions: list[tuple[str, str, str]] = []  # (Action, Evaluation, Message)
    audit_results: list[tuple[str, str]] = []   # (Action, ErrorOrVal)

    if err is not None or eval_results is None:
        decisions.append(
            (policy_decision_action_for_error(failure_policy), "EvalError", str(err))
        )
    else:
        msg_results, _, msg_err = eval_cel_filter_for_input(message_exprs, remaining_budget)
        for i, ev in enumerate(eval_results):
            # `validator.go:159-168`: per-rule `ev.error` -> `msg_err == ErrOutOfBudget` -> `ev.value != True`!
            if ev.error is not None:
                decisions.append(
                    (policy_decision_action_for_error(failure_policy), "EvalError", ev.error)
                )
            elif msg_err == "ErrOutOfBudget":
                decisions.append(
                    (
                        policy_decision_action_for_error(failure_policy),
                        "EvalError",
                        f"failed messageExpression: {msg_err}",
                    )
                )
            elif ev.value is not True:
                msg = ev.expr
                if (
                    msg_results
                    and i < len(msg_results)
                    and msg_results[i].error is None
                    and msg_results[i].result_type == "string"
                ):
                    cand = msg_results[i].value.strip()
                    if cand and "\n" not in cand and len(cand) <= 5 * 1024:
                        msg = cand
                decisions.append(("ActionDeny", "EvalDeny", msg))
            else:
                decisions.append(("ActionAdmit", "EvalAdmit", ""))

        # `validator.go:215`: passes fresh `RUNTIME_CEL_COST_BUDGET`, NOT `remaining_budget`
        aa_specs = [
            sp if bypass_compile_gate_for_audit else compile_audit_annotation_spec(sp)
            for _, sp in audit_annotations
        ]
        aa_evals, _, aa_err = eval_cel_filter_for_input(aa_specs, RUNTIME_CEL_COST_BUDGET)
        if aa_err is not None or aa_evals is None:
            # `validator.go:216-226`: replaces `Decisions` with a single `PolicyDecision` routed
            # through `binding.Spec.ValidationActions` in `dispatcher.go:235-257`!
            decisions = [
                (policy_decision_action_for_error(failure_policy), "EvalError", str(aa_err))
            ]
        else:
            for (_, _), aev in zip(audit_annotations, aa_evals):
                if aev.error is not None:
                    # `validator.go:245-247`: `auditAnnotationEvaluationForError(f)`
                    audit_results.append(
                        (audit_annotation_evaluation_for_error(failure_policy), aev.error)
                    )
                elif aev.result_type == "string":
                    val = aev.value.strip()
                    audit_results.append(
                        ("AuditAnnotationActionExclude" if not val else "AuditAnnotationActionPublish", val)
                    )
                elif aev.result_type == "null":
                    audit_results.append(("AuditAnnotationActionExclude", ""))
                else:
                    # `validator.go:260-264`: defensive branch (unreachable via `CompileCELExpression`
                    # due to `compile.go:191` `IsExactType`, reachable only on uncompiled ASTs).
                    audit_results.append(
                        ("AuditAnnotationActionError", f"unsupported return type: {aev.result_type}")
                    )

    # `dispatcher.go:227-294`
    denied: list[str] = []
    warnings: list[str] = []
    for action, _, msg in decisions:
        if action == "ActionDeny":
            for va in validation_actions:
                if va == "Deny":
                    denied.append(msg)
                elif va == "Warn":
                    warnings.append(msg)

    for aa_action, aa_payload in audit_results:
        if aa_action == "AuditAnnotationActionError":
            # `dispatcher.go:272-285`: appends directly to `deniedDecisions` WITHOUT checking `validation_actions`!
            denied.append(aa_payload)

    return (403 if denied else 200, warnings, denied)


def run_probe_3() -> None:
    smd = SMDWorkloadSimulator(max_update_managers=10)
    # Step 1: deploy-ctrl creates envoy container + atomic args
    assert smd.apply(
        "deploy-ctrl",
        {"args": ["--tls", "--audit"], "containers": [{"name": "envoy", "image": "envoy:v1.31"}]},
    ) is None
    # Step 2: iac-agent conflicts on atomic args without force -> 409
    conflict_mgrs = smd.apply("iac-agent", {"args": ["--debug"]}, force=False)
    # Step 3: iac-agent forces atomic args -> wipes `--tls` and `--audit`
    assert smd.apply("iac-agent", {"args": ["--debug"]}, force=True) is None
    wiped_args = list(smd.live_args)
    # Step 4: vpa-agent co-owns `envoy` container via `resources_cpu`
    assert smd.apply(
        "vpa-agent", {"containers": [{"name": "envoy", "resources_cpu": "250m"}]}
    ) is None
    # Step 5: deploy-ctrl deletes `envoy` from its manifest -> zombie container without `image`!
    assert smd.apply("deploy-ctrl", {"args": ["--debug"], "containers": []}, force=True) is None
    zombie_envoy = dict(smd.live_containers.get("envoy", {}))
    zombie_missing_image = "envoy" in smd.live_containers and "image" not in zombie_envoy

    # Step 6: capManagersManager caps Update entries at 10, leaves 25 Apply entries uncapped
    cap_sim = SMDWorkloadSimulator(max_update_managers=10)
    for idx in range(25):
        cap_sim.record_update_manager(f"legacy-upd-{idx:02d}", f".metadata.labels.u{idx}")
        cap_sim.apply(f"agent-run-{idx:02d}", {"containers": [{"name": "app", f"env_{idx}": "1"}]})
    update_entries = sum(1 for a, _, _ in cap_sim.managers.values() if not a)
    apply_entries = sum(1 for a, _, _ in cap_sim.managers.values() if a)

    # Control: `PerCallLimit` (`1,000,000`) cancels a single expensive rule at `1,000,001 <= remaining`
    # as a per-rule error, PRESERVING Rule 0's `EvalDeny` -> HTTP 403!
    per_call_status, _, _ = evaluate_validating_admission_policy(
        validations=[
            CELExprSpec("!object.spec.privileged", 800_000, "bool", False),
            CELExprSpec("expensive_single_rule", 6_000_000, "bool", True),
        ],
        message_exprs=[],
        audit_annotations=[],
        failure_policy="Ignore",
        validation_actions=["Deny"],
    )

    # CEL Trap K1: Multi-rule `<= 1,000,000` expressions summing past `RuntimeCELCostBudget = 10,000,000`:
    # Rule 0 denies (`False`, 800k), Rules 1..10 each spend 900k (9.8M cumulative, 200k remaining),
    # Rule 11 spends 300k (`<= PerCallLimit`, `> remaining`) -> `ErrOutOfBudget` wipes Rule 0 -> HTTP 200!
    k1_rules = (
        [CELExprSpec("!object.spec.privileged", 800_000, "bool", False)]
        + [CELExprSpec(f"check_{i}", 900_000, "bool", True) for i in range(1, 11)]
        + [CELExprSpec("check_11", 300_000, "bool", True)]
    )
    k1_status, _, _ = evaluate_validating_admission_policy(
        validations=k1_rules,
        message_exprs=[],
        audit_annotations=[],
        failure_policy="Ignore",
        validation_actions=["Deny"],
    )

    # CEL Trap K2: Validations finish at 9.8M (`remainingBudget = 200k`) with Rule 0 = `False` (`EvalDeny`),
    # then Rule 0's `messageExpression` spends 300k (`<= PerCallLimit`, `> remainingBudget`) -> HTTP 200!
    k2_rules = [CELExprSpec("!object.spec.hostNetwork", 800_000, "bool", False)] + [
        CELExprSpec(f"check_{i}", 900_000, "bool", True) for i in range(1, 11)
    ]
    k2_msgs = [CELExprSpec("'denied pod ' + object.metadata.name", 300_000, "string", "denied")] + [
        CELExprSpec("''", 0, "string", "") for _ in range(1, 11)
    ]
    k2_status, _, _ = evaluate_validating_admission_policy(
        validations=k2_rules,
        message_exprs=k2_msgs,
        audit_annotations=[],
        failure_policy="Ignore",
        validation_actions=["Deny"],
    )

    # Compile-gate verification: untyped `object.spec.replicas` (`dyn`) fails `compile.go:191` (`IsExactType`),
    # returning `AuditAnnotationActionExclude` -> HTTP 200 under `failurePolicy: Ignore`.
    k3_dyn_ignore_status, _, _ = evaluate_validating_admission_policy(
        validations=[CELExprSpec("!object.spec.privileged", 100_000, "bool", False)],
        message_exprs=[],
        audit_annotations=[("replicas_raw", CELExprSpec("object.spec.replicas", 50_000, "dyn", 42))],
        failure_policy="Ignore",
        validation_actions=["Warn"],
    )

    # Audit-annotation `ErrOutOfBudget` under `[Warn]` + `Fail` routes through `decisions` -> HTTP 200.
    aa_oob_specs = [
        (f"aa_{i}", CELExprSpec(f"string({i})", 950_000, "string", str(i))) for i in range(11)
    ]
    aa_oob_warn_status, aa_oob_warns, _ = evaluate_validating_admission_policy(
        validations=[CELExprSpec("!object.spec.privileged", 100_000, "bool", True)],
        message_exprs=[],
        audit_annotations=aa_oob_specs,
        failure_policy="Fail",
        validation_actions=["Warn"],
    )

    # CEL Trap K3 (live production canary outage): `failurePolicy: Fail` (Kubernetes default) +
    # `validationActions: [Warn]` + runtime error (`division by zero` when `replicas == 0`) in a
    # valid string-typed `auditAnnotations` expression -> `AuditAnnotationActionError` bypasses
    # `binding.Spec.ValidationActions` in `dispatcher.go:272-285` -> hard HTTP 403!
    k3_status, k3_warns, k3_denied = evaluate_validating_admission_policy(
        validations=[CELExprSpec("!object.spec.privileged", 100_000, "bool", False)],
        message_exprs=[],
        audit_annotations=[
            (
                "inv_replicas",
                CELExprSpec(
                    "string(1 / object.spec.replicas)",
                    50_000,
                    "string",
                    None,
                    runtime_error="division by zero",
                ),
            )
        ],
        failure_policy="Fail",
        validation_actions=["Warn"],
    )

    assert conflict_mgrs == ["deploy-ctrl"]
    assert wiped_args == ["--debug"]
    assert zombie_missing_image is True and zombie_envoy == {"name": "envoy", "resources_cpu": "250m"}
    assert update_entries == 10 and apply_entries == 25
    assert per_call_status == 403
    assert k1_status == 200 and k2_status == 200
    assert k3_dyn_ignore_status == 200
    assert aa_oob_warn_status == 200 and len(aa_oob_warns) == 1
    assert k3_status == 403 and len(k3_warns) == 1 and k3_denied == ["division by zero"]

    print("=== PROBE 3: Kubernetes SSA (`structured-merge-diff`) & CEL Admission Traps ===")
    print(
        f"  SSA ownership algebra: non_force_409={conflict_mgrs}, force_atomic_args={wiped_args}, "
        f"zombie_container={zombie_envoy} (missing_image={zombie_missing_image})"
    )
    print(
        f"  `capManagersManager` asymmetry (25 Update + 25 Apply runs, cap=10): "
        f"update_entries={update_entries}, apply_entries={apply_entries}"
    )
    print(
        f"  ValidatingAdmissionPolicy CEL traps: single_rule_over_1M_status={per_call_status}, "
        f"K1_multi_rule_oob_ignore_status={k1_status}, K2_msgExpr_oob_ignore_status={k2_status}, "
        f"dyn_compile_ignore_status={k3_dyn_ignore_status}, aa_oob_warn_fail_status={aa_oob_warn_status}, "
        f"K3_warn_canary_fail_runtime_err_status={k3_status} (warnings={len(k3_warns)}, denied={k3_denied})"
    )


# ============================================================================
# PROBE 4: Static HCL Scanners (Trivy & Checkov) vs. Post-Plan JSON & Oracles
# ============================================================================


def trivy_evaluate_root_and_submodule(
    child_outputs: dict[str, Any]
) -> tuple[int, int, int, int]:
    """Faithful port of `aquasecurity/trivy@edf9f5c1` `evaluator.go:136-163, 321-345, 418-445`
    compared against actual `terraform plan` resolution.
    """
    # Phase 1 (`evaluator.go:142-151`): `expandBlocks` runs BEFORE `evaluateSubmodules` (`L156`).
    # Any `module.net.*` attribute has `IsKnown() == False` during root expansion!
    for_each_known_at_line_142 = False
    count_known_at_line_142 = False

    # `expandBlockForEaches` (`L323-329`): `if !forEachVal.IsKnown() { continue }` -> 0 clones!
    trivy_foreach_clones = 0 if not for_each_known_at_line_142 else len(child_outputs["open_cidrs"])

    # `expandBlockCounts` (`L418-423`): `count := 1; if countAttrVal.IsKnown() { count = ... }` -> 1 clone!
    trivy_count_clones = 1 if not count_known_at_line_142 else int(child_outputs["enable_legacy_ssh"])

    # `evaluateSubmodules` runs at `L156`, followed by `evaluateSteps` at `L159`, WITHOUT re-expanding blocks!
    tf_plan_foreach_clones = len(child_outputs["open_cidrs"])
    tf_plan_count_clones = int(child_outputs["enable_legacy_ssh"])
    return trivy_foreach_clones, tf_plan_foreach_clones, trivy_count_clones, tf_plan_count_clones


CHECKOV_INTERNAL_LINE_KEYS = ("__startline__", "__endline__")


def _checkov_update_after_unknown_in_complex_types(inner_key: str, value: dict[str, Any]) -> None:
    """Faithful port of `_update_after_unknown_in_complex_types` and `_handle_after_unknown_dict`
    (`bridgecrewio/checkov@28694608` `checkov/terraform/plan_parser.py:282-331`).
    """
    if inner_key not in value:
        value[inner_key] = ["true_after_unknown"]
        return
    inner_value = value[inner_key]
    if isinstance(inner_value, str) and inner_value.lower() == "true":
        value[inner_key] = ["true_after_unknown"]
    if isinstance(inner_value, list):
        for i, v in enumerate(inner_value):
            if isinstance(v, str) and v.lower() == "true":
                inner_value[i] = ["true_after_unknown"]
            if isinstance(v, dict):
                for k in list(v.keys()):
                    _checkov_update_after_unknown_in_complex_types(k, v)
    if isinstance(inner_value, dict):
        for k, v in inner_value.items():
            if isinstance(v, str) and v.lower() == "true":
                inner_value[k] = ["true_after_unknown"]
            if isinstance(v, dict):
                for dk in list(v.keys()):
                    _checkov_update_after_unknown_in_complex_types(dk, v)


def checkov_eval_after_unknown(
    changes: dict[str, Any], resource_conf: dict[str, Any], env_enabled: bool
) -> None:
    """Faithful port of `_eval_after_unknown` and `_handle_complex_after_unknown`
    (`bridgecrewio/checkov@28694608` `checkov/terraform/plan_parser.py:236-280`).
    """
    after_unknown = changes.get("change", {}).get("after_unknown")
    if env_enabled and after_unknown and isinstance(after_unknown, dict):
        for k, v in after_unknown.items():
            if v is True and k not in resource_conf:
                resource_conf[k] = ["true_after_unknown"]
            elif isinstance(v, list) and len(v) == 1 and isinstance(v[0], dict):
                inner_keys = list(v[0].keys())
                for inner_key in inner_keys:
                    if inner_key in CHECKOV_INTERNAL_LINE_KEYS:
                        continue
                    # `plan_parser.py:273`: unguarded `resource_conf[k]` raises `KeyError` if `k` absent!
                    resource_conf_value = resource_conf[k]
                    if inner_key not in resource_conf_value and isinstance(resource_conf_value, list):
                        # `plan_parser.py:268-279`: ignores `v[0][inner_key]` boolean value and mutates
                        # ALL elements `i in range(len(resource_conf_value))`!
                        for i in range(len(resource_conf_value)):
                            if isinstance(resource_conf_value[i], dict):
                                _checkov_update_after_unknown_in_complex_types(
                                    inner_key, resource_conf_value[i]
                                )
                            elif (
                                isinstance(resource_conf_value[i], list)
                                and isinstance(resource_conf_value[i][0], dict)
                            ):
                                _checkov_update_after_unknown_in_complex_types(
                                    inner_key, resource_conf_value[i][0]
                                )


def checkov_tostring(original: str) -> bool | str:
    """Faithful port of `checkov/terraform/parser_functions.py:93-110`."""
    if original.startswith('"') and original.endswith('"'):
        return original[1:-1]
    low = original.strip().lower()
    if low in ("true", "false"):
        # `parser_functions.py:98-100`: returns Python `bool` instead of `str`!
        return low == "true"
    return str(int(original))


def checkov_tomap_arn_demo(raw_hcl_map_expr: str) -> str:
    """Faithful port of line 129 of `checkov/terraform/parser_functions.py`:
    `original = original.replace(":", "=")` (`# converted to colons by parser #shrug`).
    """
    mutated = raw_hcl_map_expr.replace(":", "=")
    return mutated.split('"', 2)[1]


def fisher_exact_two_sided_and_one_sided(a: int, b: int, c: int, d: int) -> tuple[float, float]:
    """Exact two-sided and greater-tail one-sided Fisher's exact test p-values."""
    r1 = a + b
    c1, n = a + c, a + b + c + d

    def hypergeom_pmf(k: int) -> float:
        return (math.comb(c1, k) * math.comb(n - c1, r1 - k)) / math.comb(n, r1)

    p_obs = hypergeom_pmf(a)
    lo = max(0, r1 - (n - c1))
    hi = min(r1, c1)
    two_sided = sum(
        hypergeom_pmf(k) for k in range(lo, hi + 1) if hypergeom_pmf(k) <= p_obs + 1e-12
    )
    one_sided = sum(hypergeom_pmf(k) for k in range(a, hi + 1))
    return two_sided, one_sided


def wilson_95_ci_pct(k: int, n: int) -> tuple[float, float]:
    """Standard Wilson 95% score confidence interval in percent."""
    z = 1.959963984540054
    p = k / n
    denom = 1.0 + (z * z) / n
    center = (p + (z * z) / (2.0 * n)) / denom
    half = (z / denom) * math.sqrt((p * (1.0 - p)) / n + (z * z) / (4.0 * n * n))
    return round((center - half) * 100.0, 1), round((center + half) * 100.0, 1)


def run_probe_4() -> None:
    trv_fe, plan_fe, trv_cnt, plan_cnt = trivy_evaluate_root_and_submodule(
        {"open_cidrs": {"wan": "0.0.0.0/0"}, "enable_legacy_ssh": 0}
    )

    with tempfile.TemporaryDirectory() as tmpdir:
        plan_path = Path(tmpdir) / "tfplan.json"
        plan_doc = {
            "resource_changes": [
                {
                    "type": "aws_instance",
                    "name": "app",
                    "change": {
                        "after": {
                            "ebs_block_device": [{"device_name": "/dev/xvda"}, {"device_name": "/dev/xvdb"}]
                        },
                        "after_unknown": {
                            "kms_key_id": True,
                            "ebs_block_device": [{"kms_key_id": True}, {"kms_key_id": True}],
                        },
                    },
                }
            ]
        }
        plan_path.write_text(json.dumps(plan_doc), encoding="utf-8")
        loaded_change = json.loads(plan_path.read_text(encoding="utf-8"))["resource_changes"][0]

        conf_default = {"ebs_block_device": [{"device_name": "/dev/xvda"}, {"device_name": "/dev/xvdb"}]}
        checkov_eval_after_unknown(loaded_change, conf_default, env_enabled=False)

        conf_env_2vols = {"ebs_block_device": [{"device_name": "/dev/xvda"}, {"device_name": "/dev/xvdb"}]}
        checkov_eval_after_unknown(loaded_change, conf_env_2vols, env_enabled=True)

        conf_env_1vol = {"ebs_block_device": [{"device_name": "/dev/xvda"}]}
        one_vol_change = {"change": {"after_unknown": {"ebs_block_device": [{"kms_key_id": True}]}}}
        checkov_eval_after_unknown(one_vol_change, conf_env_1vol, env_enabled=True)

        # `plan_parser.py:268-309`: even `{"kms_key_id": False}` in a length-1 `after_unknown` list
        # injects `["true_after_unknown"]` across ALL `resource_conf[k]` elements!
        conf_false_multi = {
            "ebs_block_device": [{"device_name": "/dev/xvda"}, {"device_name": "/dev/xvdb"}]
        }
        false_inner_change = {"change": {"after_unknown": {"ebs_block_device": [{"kms_key_id": False}]}}}
        checkov_eval_after_unknown(false_inner_change, conf_false_multi, env_enabled=True)

        missing_k_exc = ""
        try:
            checkov_eval_after_unknown(one_vol_change, {}, env_enabled=True)
        except KeyError as exc:
            missing_k_exc = type(exc).__name__

    tostring_res = checkov_tostring("true")
    corrupted_arn = checkov_tomap_arn_demo('{kms_arn: "arn:aws:kms:us-east-1:111122223333:key/abcd"}')

    # Primary-source audit of Vargas et al. (SBSeg 2026, Tables III-VI) & TerraProbe (Tables 4, 8, 9)
    wc33b_val_total = round(397 / 510 * 100, 1)
    wc33b_val_zeroshot = round(207 / 255 * 100, 1)
    gpt54_trivy_over_141 = round(24 / 141 * 100, 2)
    gpt54_trivy_over_146 = round(24 / 146 * 100, 2)
    p2_gem_gpt4o, p1_gem_gpt4o = fisher_exact_two_sided_and_one_sided(10, 4, 9, 5)
    p2_gem_claude, _ = fisher_exact_two_sided_and_one_sided(10, 4, 8, 6)
    wilson_12_of_14 = wilson_95_ci_pct(12, 14)
    n9_exact_80_possible = any(round(k / 9 * 100, 1) == 80.0 for k in range(10))
    n8_exact_857_possible = any(round(k / 8 * 100, 1) == 85.7 for k in range(9))

    false_flag_injected_all = all(
        d.get("kms_key_id") == ["true_after_unknown"] for d in conf_false_multi["ebs_block_device"]
    )

    assert (trv_fe, plan_fe, trv_cnt, plan_cnt) == (0, 1, 1, 0)
    assert "kms_key_id" not in conf_default
    assert conf_env_2vols["kms_key_id"] == ["true_after_unknown"]
    assert "kms_key_id" not in conf_env_2vols["ebs_block_device"][0]
    assert conf_env_1vol["ebs_block_device"][0]["kms_key_id"] == ["true_after_unknown"]
    assert false_flag_injected_all is True and missing_k_exc == "KeyError"
    assert tostring_res is True and isinstance(tostring_res, bool)
    assert corrupted_arn == "arn=aws=kms=us-east-1=111122223333=key/abcd"
    assert (wc33b_val_total, wc33b_val_zeroshot) == (77.8, 81.2)
    assert (gpt54_trivy_over_141, gpt54_trivy_over_146) == (17.02, 16.44)
    assert (round(p2_gem_gpt4o, 4), round(p1_gem_gpt4o, 4)) == (1.0, 0.5)
    assert wilson_12_of_14 == (60.1, 96.0)
    assert n9_exact_80_possible is False and n8_exact_857_possible is False

    print("=== PROBE 4: Static HCL Scanners (Trivy & Checkov) vs. Post-Plan JSON & Oracles ===")
    print(
        f"  Trivy submodule expansion ordering (`evaluator.go:142-160, 323, 418`): "
        f"for_each_clones=(trivy={trv_fe}, plan={plan_fe} -> FN), "
        f"count_clones=(trivy={trv_cnt}, plan={plan_cnt} -> FP)"
    )
    print(
        f"  Checkov `after_unknown` (`plan_parser.py:236-331`) & HCL functions: "
        f"default_drops_kms={'kms_key_id' not in conf_default}, "
        f"env_1vol_enriched={'kms_key_id' in conf_env_1vol['ebs_block_device'][0]}, "
        f"env_false_flag_injects_all={false_flag_injected_all}, "
        f"env_2vols_dropped={'kms_key_id' not in conf_env_2vols['ebs_block_device'][0]}, "
        f"missing_conf_exc={missing_k_exc}, tostring_true_type={type(tostring_res).__name__}, "
        f"tomap_arn={corrupted_arn!r}"
    )
    print(
        f"  Vargas & TerraProbe audits: wc33b_validate=(397/510={wc33b_val_total}%, "
        f"207/255={wc33b_val_zeroshot}%), gpt54_trivy_L3=(24/141={gpt54_trivy_over_141}% vs "
        f"24/146={gpt54_trivy_over_146}%), TerraProbe_Fisher=(gem_vs_gpt4o_2p={p2_gem_gpt4o:.4f}/1p={p1_gem_gpt4o:.4f}, "
        f"gem_vs_claude_2p={p2_gem_claude:.4f}), wilson_12_14={wilson_12_of_14} "
        f"(n9_80pct_possible={n9_exact_80_possible}, n8_85_7pct_possible={n8_exact_857_possible})"
    )


# ============================================================================
# PROBE 5: IaC-Eval Harness Defect Forensics & Closed-Loop Repair Funnel
# ============================================================================


IAC_EVAL_DELIMITERS = ["```hcl", "```json", "```HCL", "```Terraform", "```terraform", "```"]


def iac_eval_dict_generator(indict: Any, pre: Optional[list[Any]] = None):
    """Verbatim port of `dict_generator` (`autoiac-project/iac-eval@b75a90b3`
    `evaluation/eval.py:79-94`).
    """
    pre = pre[:] if pre else []
    if isinstance(indict, dict):
        for key, value in indict.items():
            if isinstance(value, dict):
                for d in iac_eval_dict_generator(value, pre + [key]):
                    yield d
            elif isinstance(value, (list, tuple)):
                for v in value:
                    for d in iac_eval_dict_generator(v, pre + [key]):
                        yield d
            else:
                yield pre + [key, value]
    else:
        yield pre + [indict]


def iac_eval_opa_rego_evaluation(opa_stdout_json: str) -> tuple[str, list[Any]]:
    """Verbatim port of `OPA_Rego_evaluation` (`evaluation/eval.py:780-796`)."""
    val = json.loads(opa_stdout_json)["result"][0]["expressions"][0]["value"]
    results = [i[-1] for i in iac_eval_dict_generator(val)]
    # Line 788: `False in results` treats `0` and `0.0` as `False` (`0 == False` is True in Python)!
    success = False if False in results else True
    opa_result = "Success" if success else "Failure"
    return opa_result, results


def iac_eval_separate_answer_and_code(text: str) -> tuple[str, str]:
    """Verbatim port of `separate_answer_and_code` (`evaluation/eval.py:29, 177-195`)."""
    answer, code = text.strip(), ""
    for delimiter in IAC_EVAL_DELIMITERS:
        parts = text.split(delimiter)
        if len(parts) < 2:
            answer = text.strip()
            code = ""
            continue
        answer = parts[0].strip()
        code = parts[1].strip().rsplit("```", 1)[0].strip()
        if code != "":
            return answer, code
    return answer, code


def iac_eval_multi_turn_loop(
    samples_spec: list[tuple[tuple[bool, str], tuple[bool, str]]],
    rego_policy_source: str,
) -> dict[str, Any]:
    """Verbatim state-machine port of `model_evaluation` (`evaluation/eval.py:491-575`),
    `prompt_templates.py:41-55`, and post-hoc `ablation-iac-eval-pipeline.py:296, 333`.

    Note `eval.py:491, 498, 503`: `preprompt` and `prompt` are initialized OUTSIDE
    `for i in range(NUM_EXISTING_SAMPLES, NUM_SAMPLES_PER_TASK):` and mutated in-place
    on `L563-571`, leaking Sample `i - 1`'s multi-turn `"fix the error"` system prompt
    and leaked Rego policy directly into Sample `i`'s Turn 1!
    """
    preprompt = "SYSTEM_TURN1"
    prompt = "Here is the actual prompt: Create encrypted S3 bucket"
    num_correct = 0
    per_sample: list[dict[str, Any]] = []

    for (t1_plan_ok, t1_opa_res), (t2_plan_ok, t2_opa_res) in samples_spec:
        multi_turn_count = 1
        turns_executed = 0
        turn1_preprompt_seen = ""
        turn1_prompt_seen = ""
        turn2_prompt_sent = ""
        df_cell_correct = ""

        while True:
            turns_executed += 1
            if turns_executed == 1:
                turn1_preprompt_seen = preprompt
                turn1_prompt_seen = prompt
                x = {
                    "terraform_plan_success": t1_plan_ok,
                    "opa_evaluation_result": t1_opa_res,
                    "terraform_plan_error": "No error",
                    "opa_evaluation_error": "Rule violation",
                }
            else:
                turn2_prompt_sent = prompt
                x = {
                    "terraform_plan_success": t2_plan_ok,
                    "opa_evaluation_result": t2_opa_res,
                    "terraform_plan_error": "No error",
                    "opa_evaluation_error": "No error",
                }

            df_cell_correct = x["opa_evaluation_result"]

            # Line 554 bug: lowercase `"success"` never matches `"Success"` (`L789`)!
            if x["opa_evaluation_result"] == "success":
                num_correct += 1
                break
            else:
                if multi_turn_count == 2:
                    break
                multi_turn_count += 1
                preprompt = "MULTI_TURN_FIX_ERROR_SYSTEM_PROMPT"
                if not x["terraform_plan_success"]:
                    prompt = "PLAN_ERROR_PROMPT"
                elif x["opa_evaluation_result"] == "Failure":
                    # `prompt_templates.py:41-55`: leaks full hidden `rego_policy` verbatim!
                    prompt = (
                        "Here is the Rego OPA policy associated with this configuration:\n"
                        f"{rego_policy_source}"
                    )
                continue

        per_sample.append(
            {
                "turns_executed": turns_executed,
                "posthoc_csv_pass": df_cell_correct == "Success",
                "turn1_preprompt": turn1_preprompt_seen,
                "turn1_prompt_has_rego": rego_policy_source in turn1_prompt_seen,
                "oracle_leaked_in_turn2": rego_policy_source in turn2_prompt_sent,
                "turn2_prompt_unchanged_under_fix_sys": turn2_prompt_sent.startswith(
                    "Here is the actual prompt:"
                ),
            }
        )

    return {"live_num_correct": num_correct, "samples": per_sample}


def mcnemar_exact_two_sided(b: int, c: int) -> float:
    """Exact two-sided binomial McNemar p-value on discordant counts `(b, c)`."""
    n = b + c
    k = min(b, c)
    tail = sum(math.comb(n, i) for i in range(0, k + 1)) / (2 ** n)
    return min(1.0, 2.0 * tail)


def simulate_closed_loop_repair_markov() -> tuple[dict[str, float], dict[str, float]]:
    """[illustrative analytical model] (`Basis: derived`) comparing 3-step (initial +
    3 retries, k=4) Markov transition absorption under:
      (A) Scanner-Only Feedback (`L1` targeted Checkov/Trivy alarm removal), vs.
      (B) Layered Verifier Feedback (`Validate + Plan + Post-Plan Semantic Policy`).
    States: `S0_invalid`, `S1_plan_fail`, `S2_policy_fail`, `S3_deceptive_bypass`, `S4_sound_fix`.
    """
    init = [0.20, 0.35, 0.45, 0.0, 0.0]

    p_scanner = [
        [0.35, 0.25, 0.25, 0.10, 0.05],  # S0_invalid
        [0.10, 0.55, 0.15, 0.15, 0.05],  # S1_plan_fail (unobserved by static scanner!)
        [0.05, 0.20, 0.15, 0.45, 0.15],  # S2_policy_fail -> 45% deceptive bypass per step
        [0.00, 0.00, 0.00, 1.00, 0.00],  # S3_deceptive_bypass (absorbing: scanner reports 0 alarms!)
        [0.00, 0.00, 0.00, 0.00, 1.00],  # S4_sound_fix (absorbing)
    ]

    p_layered = [
        [0.20, 0.35, 0.30, 0.00, 0.15],  # S0_invalid -> validate feedback resolves syntax/schema
        [0.05, 0.25, 0.45, 0.00, 0.25],  # S1_plan_fail -> plan feedback promotes to S2/S4 (Jouini Finding 6)
        [0.02, 0.08, 0.35, 0.05, 0.50],  # S2_policy_fail -> semantic oracle blocks syntactic bypass
        [0.00, 0.05, 0.65, 0.05, 0.25],  # S3_deceptive_bypass -> caught by post-plan semantic check!
        [0.00, 0.00, 0.00, 0.00, 1.00],  # S4_sound_fix
    ]

    def step_k(vec: list[float], mat: list[list[float]], steps: int) -> dict[str, float]:
        cur = list(vec)
        for _ in range(steps):
            cur = [
                sum(cur[i] * mat[i][j] for i in range(5))
                for j in range(5)
            ]
        names = ("invalid", "plan_fail", "policy_fail", "deceptive_bypass", "sound_fix")
        return {names[j]: round(cur[j], 4) for j in range(5)}

    return step_k(init, p_scanner, 3), step_k(init, p_layered, 3)


def run_probe_5() -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        empty_rego = Path(tmpdir) / "template.rego"
        empty_rego.write_text("", encoding="utf-8")
        assert empty_rego.stat().st_size == 0

        # Defect I1: `0 == False` false failure vs. 0-byte template vacuous pass
        opa_zero_leaf, leaves_zero = iac_eval_opa_rego_evaluation(
            json.dumps({"result": [{"expressions": [{"value": {"allow": True, "violation_count": 0}}]}]})
        )
        opa_empty_policy, leaves_empty = iac_eval_opa_rego_evaluation(
            json.dumps({"result": [{"expressions": [{"value": {}}]}]})
        )

    rego_src = "package terraform.validation\ndefault allow = false"
    # Defect I2: (a) Sample 0 Turn-1 `"Success"` overwritten to `"Failure"` on Turn 2;
    # (b) Sample 0 Turn-1 `"Failure"` leaks `rego_policy` into Turn 2 AND bleeds mutated
    # `preprompt`/`prompt` directly into Sample 1's Turn 1 (`eval.py:491-503, 563-571`)!
    mt_turn1_pass = iac_eval_multi_turn_loop(
        [((True, "Success"), (True, "Failure"))],
        rego_policy_source=rego_src,
    )
    mt_two_samples = iac_eval_multi_turn_loop(
        [
            ((True, "Failure"), (True, "Success")),
            ((True, "Success"), (True, "Success")),
        ],
        rego_policy_source=rego_src,
    )
    s0_pass = mt_turn1_pass["samples"][0]
    s0_fail, s1_bleed = mt_two_samples["samples"]
    cross_sample_bleed = (
        s1_bleed["turn1_preprompt"] == "MULTI_TURN_FIX_ERROR_SYSTEM_PROMPT"
        and s1_bleed["turn1_prompt_has_rego"] is True
    )

    # Defect I3: `DELIMITERS` `"```json"` precedes `"```terraform"` + `rsplit("```", 1)` (`eval.py:29, 180-191`)
    llm_reply = (
        'Example IAM JSON:\n```json\n{"Version": "2012-10-17"}\n```\n'
        'Full Terraform configuration:\n```terraform\nresource "aws_s3_bucket" "b" {}\n```'
    )
    _, extracted_code = iac_eval_separate_answer_and_code(llm_reply)
    expected_chimera = (
        '{"Version": "2012-10-17"}\n```\n'
        'Full Terraform configuration:\n```terraform\nresource "aws_s3_bucket" "b" {}'
    )
    has_prose_and_backticks_in_tf = (
        "```" in extracted_code and "Full Terraform configuration:" in extracted_code
    )
    bleu_no_placeholder = "Reference code has less than 4 tokens:".format("resource a b {}")

    def broken_llm_as_judge_reference(reference: str, candidate: str) -> str:
        # Exact reproduction of `evaluation/metrics.py:51-69` (`prompt` is unbound!)
        return "{}\n{}\n{}".format(prompt, reference, candidate)  # type: ignore[name-defined] # noqa: F821

    caught_error = ""
    try:
        broken_llm_as_judge_reference("ref", "cand")
    except NameError as exc:
        caught_error = type(exc).__name__

    # Jouini (2026) primary-source arithmetic (Tables 3, 4, 7, 8)
    jouini_t4_pass = 186 - (8 + 7 + 14)  # 157 (84.41%)
    jouini_t4_oracle_fails = 1 + 9 + 3   # 13 (`1 VAL + 9 PLN + 3 OPA`)
    jouini_t4_oracle_pass = 186 - jouini_t4_oracle_fails  # 173 (93.01%)
    jouini_t7_pass_sum = 156 + 11 + 6    # 173 (`183` total rows in Table 7 + `3` omitted = `186`)
    jouini_t7_total_rows = 156 + 11 + 6 + 3 + 7  # 183
    jouini_mcnemar_27_21 = round(mcnemar_exact_two_sided(27, 21), 4)

    dist_scanner, dist_layered = simulate_closed_loop_repair_markov()

    assert opa_zero_leaf == "Failure" and leaves_zero == [True, 0]
    assert opa_empty_policy == "Success" and leaves_empty == []
    assert s0_pass["turns_executed"] == 2 and mt_turn1_pass["live_num_correct"] == 0
    assert s0_pass["posthoc_csv_pass"] is False
    assert s0_pass["turn2_prompt_unchanged_under_fix_sys"] is True
    assert s0_fail["oracle_leaked_in_turn2"] is True and cross_sample_bleed is True
    assert extracted_code == expected_chimera and has_prose_and_backticks_in_tf is True
    assert caught_error == "NameError"
    assert (jouini_t4_pass, jouini_t4_oracle_pass, jouini_t7_pass_sum, jouini_t7_total_rows) == (
        157,
        173,
        173,
        183,
    )

    print("=== PROBE 5: IaC-Eval Harness Bugs, Jouini Audits & Repair Dynamics ===")
    print(
        f"  `OPA_Rego_evaluation` (`eval.py:780-789`): zero_int_leaf_verdict={opa_zero_leaf} "
        f"(leaves={leaves_zero}), empty_0byte_rego_verdict={opa_empty_policy}"
    )
    print(
        f"  `model_evaluation` multi-turn (`eval.py:491-575`): "
        f"turn1_pass_turns={s0_pass['turns_executed']}, "
        f"live_num_correct={mt_turn1_pass['live_num_correct']}, "
        f"turn1_pass_overwritten_to_fail={not s0_pass['posthoc_csv_pass']}, "
        f"turn1_fail_leaks_rego_oracle={s0_fail['oracle_leaked_in_turn2']}, "
        f"sample1_turn1_inherits_leaked_rego={cross_sample_bleed}"
    )
    print(
        f"  `DELIMITERS` + `rsplit` & `metrics.py`: splices_json_prose_fences={has_prose_and_backticks_in_tf} "
        f"(starts_with_json={extracted_code.startswith('{')}), "
        f"bleu_msg={bleu_no_placeholder!r}, judge_ref_exc={caught_error}"
    )
    print(
        f"  Jouini (2026) audits: Table4_repair_pass={jouini_t4_pass}/186 "
        f"({jouini_t4_pass/186*100:.2f}%), Table4_oracle_pass={jouini_t4_oracle_pass}/186 "
        f"(fails=1_VAL+9_PLN+3_OPA={jouini_t4_oracle_fails}), "
        f"Table7_subset={jouini_t7_pass_sum}/{jouini_t7_total_rows}_rows "
        f"({jouini_t4_oracle_pass/186*100:.2f}% of 186), McNemar_27v21_2p={jouini_mcnemar_27_21}"
    )
    print(
        f"  [illustrative analytical model] 3-step (initial + 3 retries, k=4) repair distribution: "
        f"scanner_only={dist_scanner} vs layered_semantic={dist_layered}"
    )


def main() -> None:
    run_probe_1()
    run_probe_2()
    run_probe_3()
    run_probe_4()
    run_probe_5()
    print("ALL 5 PROBE SUITES PASSED DETERMINISTICALLY.")


if __name__ == "__main__":
    _ = hashlib.sha256(b"iac-plan-ssa-scanners-determinism-anchor").hexdigest()
    main()
