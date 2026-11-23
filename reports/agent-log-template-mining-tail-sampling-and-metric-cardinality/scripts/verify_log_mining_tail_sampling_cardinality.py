#!/usr/bin/env python3
"""Deterministic executable verification probe for log template mining, distributed
trace tail sampling, and high-cardinality metric ingestion.

Covers five primary-source verification suites using Python 3.10+ standard library only:
  1. `logpai/Drain3@0fb6d6e1828838fa05c8f6fa5cda878e02ea79c7` fixed-depth prefix-tree
     online log parsing & four live source defects (`drain3/drain.py`, `drain3/masking.py`,
     `drain3/template_miner.py`, `examples/drain3.ini`):
     - `str.replace` (`drain.py:183-185`) vs. unescaped `re.sub` (`template_miner.py:228-229`)
       desynchronization on `extra_delimiters` (`.` wiping message to spaces, `[` raising
       `re.error`, and `_` breaking `exact_matching=True` on underscore-bearing masks as well
       as fracturing variable-token-count snake_case identifiers at depth-1 `token_count`).
     - Hash-unordered `set(self.masker.mask_names)` capture-group numbering (`p_0, p_1, ...`,
       `template_miner.py:307-327`) changing compiled regex strings across `PYTHONHASHSEED`s
       while Python 3.7+ `Match.groupdict()` (`L243`) preserves left-to-right order on unnested
       masks, plus non-greedy `.+?` multi-word token stealing under `get_parameter_list`
       (`L200, 295-296`).
     - Sequential `LogMasker.mask` rule clobbering (`masking.py:57-60`, `drain3.ini:6-14`).
     - Greedy non-backtracking `Drain.tree_search` false negatives (`drain.py:311-316, 465-470`),
       symmetric `max_children - 1` literal branch caps across numeric-first (`L366`) vs.
       literal-first (`L373-380`) arrival orders, and `max_children = 0` `KeyError('<*>')` (`L382`).
  2. Log parsing accuracy metric gaming (`LogPai` ICSE-SEIP '19, `Khan et al.` ICSE '22,
     `Loghub-2.0` ISSTA '24 `logpai/loghub-2.0@ac4aad2ea86f561e5a0acbc6587fa28b487259f9`)
     and `logpai/LILAC@163d199f95ddf419044c53681f2b474a9c2d45ce` source defects:
     - Exact 14-dataset `Loghub-2.0` scale & `LILAC` CSV reconciliations.
     - Explicitly labeled `[illustrative analytical model]` (`Basis: derived`) over a skewed
       1,000-line corpus (`950` heartbeat lines + `50` rare error lines) proving `GA`/`PA`/`FGA`/`FTA`
       divergences (opaque-template partition `GA=1.0, FGA=1.0, PA=0.0, FTA=0.0`; rare-error cluster
       fragmentation `GA=0.95` vs. `FGA=0.0625`; single-space `=` formatting drift `PA=0.0`).
     - Verbatim ports of `LILAC` `prompt_select.py:36-73` (dead-code `return s` at `L47` +
       in-place `prompts` dict mutation at `L70-71`) and `parsing_cache.py:46-258` (`.split()`
       vs. `message_split()` mismatch in `add_templates`/`modify`, unpruned `delete` dicts,
       unpopped `parameter_list.append("")` caller mutation at `L249`, and `find_template` `L252`
       `("<*>", None, None)` tuple masked to `len >= 2` by `L244-246` across all public-API
       trees yet raising `TypeError` at `match_event` `L227` whenever `len(results) == 1`).
  3. Distributed trace sampling: `open-telemetry/opentelemetry-collector-contrib@8f589e91`
     `processor/tailsamplingprocessor` (`processor.go`, `id_batcher.go`, `sharded_processor.go`,
     `composite.go`, `probabilistic.go`, `pkg/sampling`) & W3C/OTel 56-bit `tracestate`
     probability sampling (`open-telemetry/opentelemetry-specification@c216b822`):
     - Verbatim 1-for-1 port of `idbatcher.Batcher` (`id_batcher.go:75-101, 143-158`:
       `batches: list[Optional[set[int]]]` of length `num_batches` + `current_batch: set[int]`
       + `take_id`) paired with `waitForSpace` -> `dropTrace` (`processor.go:641-647, 1366-1387`),
       demonstrating Subcase A (same-tick re-insertion before Tick 1 deduplicated in
       `current_batch` with zero premature evaluation and zero spurious `DroppedTooEarly`),
       Subcase B (cross-tick re-insertion at `0 < take_id < num_batches` causing early orphan
       evaluation on the evicted root's deadline after `num_batches - take_id` post-close ticks
       plus spurious `ProcessorTailSamplingSamplingTraceDroppedTooEarly` `idNotFoundOnMapCount++`
       on the second batch even though the orphan trace was already sampled), secondary cascade
       evictions of benign traces, and contrast against `Canopy` SOSP '17 §4.2's 5-hour auxiliary
       `TraceID` cache, plus post-decision `ERROR` drops (`L618-623`) and `NopCache` repeated
       `nonSampledHooks` (`L1314-1315`).
     - Exact 56-bit `Rejection Threshold` `T` precision variants (`p = 0.01`: floor
       `0xfd70a3d70a3d70`, collector 14-hex `th:fd70a3d70a3d71`, SDK `precision=4` `th:fd70a`,
       `precision=5` `th:fd70a4`), nested trace completeness (`R >= T`), and `sample_on_first_match`
       + `useTracestate` (`processor.go:182-187, 935-952`) `100x` co-matched adjusted-count inflation.
     - `Composite.Evaluate` (`composite.go:103-133`) first-match SPS starvation, `sharded_processor`
       (`sharded_processor.go:51-58, 107-158, 233-247`) `Composite` max-trace shrinkage vs.
       `ExpectedNewTracesPerSec` zero-truncation vs. `divideRate` `max(1, ...)` inflation, and
       an `[illustrative analytical model]` (`Basis: derived`) of multi-collector split-brain.
  4. `Sifter` (`Las-Casas et al., SoCC '19`, §§5.1-5.5) online path-embedding sampler:
     - Faithful stdlib port of length-`N=5` causal path extraction, 2-layer concatenation
       context-to-center softmax model (`P=10`, `lr=0.01`), sliding loss window (`k=50`), and
       `rho = (w_{k+1} / sum w_j) * (k + 1) * alpha` (`alpha = 0.01`).
     - Evaluates an `[illustrative analytical model]` (`Basis: derived`) trace stream verifying
       that `Sifter`'s pre-sampling backpropagation on *every* incoming trace (`§5.4-5.5`, zero
       importance weights) achieves `>30x` rare-anomaly enrichment, whereas updating weights
       *only* on post-sampled traces corrupts the common-case baseline and collapses enrichment.
  5. High-cardinality metrics: `prometheus/prometheus@06170caaea` (`tsdb/index/postings.go`)
     & OpenTelemetry Metrics SDK (`opentelemetry-specification@c216b822` `sdk.md:908-961` vs.
     `open-telemetry/opentelemetry-go@7b56b60e` `atomic.go:318, 439, 477-483` & `bound_sum.go:43`,
     plus `limit.go:36` / `limit_test.go:14-42` `L38-41`):
     - Faithful `MemPostings` port (`Add`, `addFor` out-of-order tail swap `#15317`, `Delete`
       shared-label slice rewrites, `512`-label `1ms` yield stalls, and `2x` `lvs` capacity
       retention) over an `[illustrative analytical model]` (`Basis: derived`) comparing bounded
       (`60` series) vs. `conversation_id`-polluted (`50,000` ephemeral series) agent telemetry.
     - Exact spec-vs-`opentelemetry-go` boundary check (`1,999` vs. `2,000` non-overflow streams
       at `limit=2000`, and `0` non-overflow streams at `limit=1`) plus `[illustrative analytical
       model]` demonstration of `otel.metric.overflow=true` reporting `0.0%` filtered
       `status="500"` error rate during a `100%` late-window outage, and `cumulativeSum` permanent
       process-lifetime lockout (`sum.go:130, 192-195`) vs. `deltaSum` per-cycle `Clear` recovery
       (`sum.go:58, 103`; `atomic.go:357-378`).

Execution invariants:
  - Python 3.10+ standard library only; zero third-party imports; zero runtime network I/O.
  - All filesystem fixtures isolated inside `with tempfile.TemporaryDirectory():`.
  - Zero local paths or wall-clock timestamps in stdout; bit-identical across
    `PYTHONHASHSEED=1` and `PYTHONHASHSEED=2` under `python3 -I -B`.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field
import hashlib
import json
import math
from pathlib import Path
import random
import re
import string
import struct
import tempfile
from typing import Callable, Optional, Sequence


# ============================================================================
# PROBE 1: logpai/Drain3@0fb6d6e1 Prefix-Tree & Live Defect Reproduction Suite
# ============================================================================


@dataclass
class MaskingInstructionPort:
    """Faithful port of `drain3/masking.py:25-38` (`MaskingInstruction`)."""

    pattern: str
    mask_with: str

    def __post_init__(self) -> None:
        self.regex = re.compile(self.pattern)

    def mask(self, content: str, mask_prefix: str, mask_suffix: str) -> str:
        mask_str = mask_prefix + self.mask_with + mask_suffix
        return self.regex.sub(mask_str, content)


class LogMaskerPort:
    """Faithful port of `drain3/masking.py:44-67` (`LogMasker`)."""

    def __init__(
        self,
        instructions: Sequence[MaskingInstructionPort],
        mask_prefix: str = "<:",
        mask_suffix: str = ":>",
    ) -> None:
        self.mask_prefix = mask_prefix
        self.mask_suffix = mask_suffix
        self.masking_instructions = list(instructions)
        self.mask_name_to_instructions: dict[str, list[MaskingInstructionPort]] = {}
        for mi in self.masking_instructions:
            self.mask_name_to_instructions.setdefault(mi.mask_with, []).append(mi)

    def mask(self, content: str) -> str:
        for mi in self.masking_instructions:
            content = mi.mask(content, self.mask_prefix, self.mask_suffix)
        return content

    @property
    def mask_names(self) -> Sequence[str]:
        return list(self.mask_name_to_instructions.keys())

    def instructions_by_mask_name(self, mask_name: str) -> Sequence[MaskingInstructionPort]:
        return self.mask_name_to_instructions.get(mask_name, [])


@dataclass
class DrainNodePort:
    key_to_child_node: dict[str, DrainNodePort] = field(default_factory=dict)
    cluster_ids: list[int] = field(default_factory=list)


@dataclass
class LogClusterPort:
    log_template_tokens: tuple[str, ...]
    cluster_id: int
    size: int = 1

    def get_template(self) -> str:
        return " ".join(self.log_template_tokens)


class DrainPort:
    """Faithful port of `drain3/drain.py:62-472` (`DrainBase` + `Drain`)."""

    def __init__(
        self,
        depth: int = 4,
        sim_th: float = 0.4,
        max_children: int = 100,
        extra_delimiters: Sequence[str] = (),
        param_str: str = "<*>",
        parametrize_numeric_tokens: bool = True,
    ) -> None:
        if depth < 3:
            raise ValueError("depth argument must be at least 3")
        self.log_cluster_depth = depth
        self.max_node_depth = depth - 2
        self.sim_th = sim_th
        self.max_children = max_children
        self.root_node = DrainNodePort()
        self.id_to_cluster: dict[int, LogClusterPort] = {}
        self.clusters_counter = 0
        self.extra_delimiters = tuple(extra_delimiters)
        self.param_str = param_str
        self.parametrize_numeric_tokens = parametrize_numeric_tokens

    @staticmethod
    def has_numbers(s: str) -> bool:
        return any(ch.isdigit() for ch in s)

    def get_content_as_tokens(self, content: str) -> list[str]:
        # `drain3/drain.py:181-186`: literal `str.replace`, NOT `re.sub`!
        content = content.strip()
        for delimiter in self.extra_delimiters:
            content = content.replace(delimiter, " ")
        return content.split()

    def get_seq_distance(
        self, seq1: Sequence[str], seq2: Sequence[str], include_params: bool
    ) -> tuple[float, int]:
        # `drain3/drain.py:391-413`
        assert len(seq1) == len(seq2)
        if len(seq1) == 0:
            return 1.0, 0
        sim_tokens = 0
        param_count = 0
        for token1, token2 in zip(seq1, seq2):
            if token1 == self.param_str:
                param_count += 1
                continue
            if token1 == token2:
                sim_tokens += 1
        if include_params:
            sim_tokens += param_count
        return float(sim_tokens) / len(seq1), param_count

    def fast_match(
        self,
        cluster_ids: Sequence[int],
        tokens: Sequence[str],
        sim_th: float,
        include_params: bool,
    ) -> Optional[LogClusterPort]:
        max_sim = -1.0
        max_param_count = -1
        max_cluster: Optional[LogClusterPort] = None
        for cid in cluster_ids:
            cluster = self.id_to_cluster.get(cid)
            if cluster is None:
                continue
            cur_sim, param_count = self.get_seq_distance(
                cluster.log_template_tokens, tokens, include_params
            )
            if cur_sim > max_sim or (cur_sim == max_sim and param_count > max_param_count):
                max_sim = cur_sim
                max_param_count = param_count
                max_cluster = cluster
        if max_sim >= sim_th:
            return max_cluster
        return None

    def tree_search(
        self,
        root_node: DrainNodePort,
        tokens: Sequence[str],
        sim_th: float,
        include_params: bool,
    ) -> Optional[LogClusterPort]:
        # `drain3/drain.py:282-322`: greedy single-path prefix walk
        token_count = len(tokens)
        cur_node = root_node.key_to_child_node.get(str(token_count))
        if cur_node is None:
            return None
        if token_count == 0:
            return self.id_to_cluster.get(cur_node.cluster_ids[0])
        cur_node_depth = 1
        for token in tokens:
            if cur_node_depth >= self.max_node_depth or cur_node_depth == token_count:
                break
            key_to_child = cur_node.key_to_child_node
            nxt = key_to_child.get(token)
            if nxt is None:
                nxt = key_to_child.get(self.param_str)
            if nxt is None:
                return None
            cur_node = nxt
            cur_node_depth += 1
        return self.fast_match(cur_node.cluster_ids, tokens, sim_th, include_params)

    def add_seq_to_prefix_tree(self, root_node: DrainNodePort, cluster: LogClusterPort) -> None:
        # `drain3/drain.py:324-388`: `max_children` check (`L366` vs `L373-380`)
        token_count = len(cluster.log_template_tokens)
        token_count_str = str(token_count)
        cur_node = root_node.key_to_child_node.setdefault(token_count_str, DrainNodePort())
        if token_count == 0:
            cur_node.cluster_ids = [cluster.cluster_id]
            return
        current_depth = 1
        for token in cluster.log_template_tokens:
            if current_depth >= self.max_node_depth or current_depth >= token_count:
                cur_node.cluster_ids = [
                    cid for cid in cur_node.cluster_ids if cid in self.id_to_cluster
                ] + [cluster.cluster_id]
                break
            if token not in cur_node.key_to_child_node:
                if self.parametrize_numeric_tokens and self.has_numbers(token):
                    if self.param_str not in cur_node.key_to_child_node:
                        new_node = DrainNodePort()
                        cur_node.key_to_child_node[self.param_str] = new_node
                        cur_node = new_node
                    else:
                        cur_node = cur_node.key_to_child_node[self.param_str]
                else:
                    if self.param_str in cur_node.key_to_child_node:
                        if len(cur_node.key_to_child_node) < self.max_children:
                            new_node = DrainNodePort()
                            cur_node.key_to_child_node[token] = new_node
                            cur_node = new_node
                        else:
                            cur_node = cur_node.key_to_child_node[self.param_str]
                    else:
                        if len(cur_node.key_to_child_node) + 1 < self.max_children:
                            new_node = DrainNodePort()
                            cur_node.key_to_child_node[token] = new_node
                            cur_node = new_node
                        elif len(cur_node.key_to_child_node) + 1 == self.max_children:
                            new_node = DrainNodePort()
                            cur_node.key_to_child_node[self.param_str] = new_node
                            cur_node = new_node
                        else:
                            cur_node = cur_node.key_to_child_node[self.param_str]
            else:
                cur_node = cur_node.key_to_child_node[token]
            current_depth += 1

    def add_log_message(self, content: str) -> LogClusterPort:
        content_tokens = self.get_content_as_tokens(content)
        match_cluster = self.tree_search(self.root_node, content_tokens, self.sim_th, False)
        if match_cluster is None:
            self.clusters_counter += 1
            match_cluster = LogClusterPort(tuple(content_tokens), self.clusters_counter)
            self.id_to_cluster[self.clusters_counter] = match_cluster
            self.add_seq_to_prefix_tree(self.root_node, match_cluster)
        else:
            match_cluster.log_template_tokens = tuple(
                t2 if t1 == t2 else self.param_str
                for t1, t2 in zip(content_tokens, match_cluster.log_template_tokens)
            )
            match_cluster.size += 1
        return match_cluster

    def get_clusters_ids_for_seq_len(self, seq_len: int) -> list[int]:
        cur_node = self.root_node.key_to_child_node.get(str(seq_len))
        if cur_node is None:
            return []
        out: list[int] = []

        def walk(node: DrainNodePort) -> None:
            out.extend(node.cluster_ids)
            for child in node.key_to_child_node.values():
                walk(child)

        walk(cur_node)
        return out

    def match(self, content: str, full_search_strategy: str = "never") -> Optional[LogClusterPort]:
        # `drain3/drain.py:427-472`
        content_tokens = self.get_content_as_tokens(content)
        required_sim_th = 1.0

        def full_search() -> Optional[LogClusterPort]:
            all_ids = self.get_clusters_ids_for_seq_len(len(content_tokens))
            return self.fast_match(all_ids, content_tokens, required_sim_th, include_params=True)

        if full_search_strategy == "always":
            return full_search()
        match_cluster = self.tree_search(
            self.root_node, content_tokens, required_sim_th, include_params=True
        )
        if match_cluster is not None:
            return match_cluster
        if full_search_strategy == "never":
            return None
        return full_search()


class TemplateMinerPort:
    """Faithful port of `drain3/template_miner.py:134-331`."""

    def __init__(self, drain: DrainPort, masker: LogMaskerPort) -> None:
        self.drain = drain
        self.masker = masker

    def add_log_message(self, log_message: str) -> LogClusterPort:
        # `template_miner.py:138-142`: masks BEFORE `drain.add_log_message` replaces delimiters
        masked = self.masker.mask(log_message)
        return self.drain.add_log_message(masked)

    def build_extraction_regex(
        self,
        log_template: str,
        exact_matching: bool,
        mask_name_order: Optional[Sequence[str]] = None,
    ) -> tuple[str, dict[str, str]]:
        # `template_miner.py:252-331` (`_get_template_parameter_extraction_regex`)
        param_group_name_to_mask_name: dict[str, str] = {}
        counter = [0]

        def get_next_param_name() -> str:
            name = f"p_{counter[0]}"
            counter[0] += 1
            return name

        def create_capture_regex(_mask_name: str) -> str:
            allowed_patterns: list[str] = []
            if exact_matching:
                for mi in self.masker.instructions_by_mask_name(_mask_name):
                    mi_groups = list(mi.regex.groupindex.keys())
                    pattern = mi.pattern
                    for group_name in mi_groups:
                        pg = get_next_param_name()
                        pattern = pattern.replace(f"(?P={group_name}", f"(?P={pg}")
                        pattern = pattern.replace(f"(?P<{group_name}>", f"(?P<{pg}>")
                    pattern = re.sub(r"\\(?!0)\d{1,2}", r"(?:.+?)", pattern)
                    allowed_patterns.append(pattern)
            if not exact_matching or _mask_name == "*":
                allowed_patterns.append(r".+?")
            pg_name = get_next_param_name()
            param_group_name_to_mask_name[pg_name] = _mask_name
            return f"(?P<{pg_name}>{'|'.join(allowed_patterns)})"

        # Upstream uses `mask_names = set(self.masker.mask_names); mask_names.add("*")` (`L307-310`).
        # Allow passing explicit `mask_name_order` to test two hash-seed orders deterministically.
        if mask_name_order is None:
            names_iter: Sequence[str] = sorted(set(self.masker.mask_names) | {"*"})
        else:
            names_iter = mask_name_order

        escaped_prefix = re.escape(self.masker.mask_prefix)
        escaped_suffix = re.escape(self.masker.mask_suffix)
        template_regex = re.escape(log_template)
        for mask_name in names_iter:
            search_str = escaped_prefix + re.escape(mask_name) + escaped_suffix
            while True:
                rep_str = create_capture_regex(mask_name)
                new_rx = template_regex.replace(search_str, rep_str, 1)
                if new_rx == template_regex:
                    break
                template_regex = new_rx
        template_regex = re.sub(r"\\ ", r"\\s+", template_regex)
        return f"^{template_regex}$", param_group_name_to_mask_name

    def extract_parameters(
        self,
        log_template: str,
        log_message: str,
        exact_matching: bool = True,
        mask_name_order: Optional[Sequence[str]] = None,
    ) -> Optional[list[tuple[str, str]]]:
        # `template_miner.py:228-249`: BUG — runs `re.sub(delimiter, " ", log_message)`
        # on raw unmasked `log_message` without `re.escape`!
        for delimiter in self.drain.extra_delimiters:
            log_message = re.sub(delimiter, " ", log_message)
        template_regex, pmap = self.build_extraction_regex(
            log_template, exact_matching, mask_name_order=mask_name_order
        )
        m = re.match(template_regex, log_message)
        if not m:
            return None
        return [(val, pmap[g]) for g, val in m.groupdict().items() if g in pmap]


def run_probe_1(tmp_root: Path) -> None:
    # 1. `extra_delimiters` `str.replace` vs. `re.sub` & underscore-mask desynchronization
    dot_miner = TemplateMinerPort(
        DrainPort(depth=4, sim_th=0.4, extra_delimiters=["."]),
        LogMaskerPort([], mask_prefix="<", mask_suffix=">"),
    )
    c1 = dot_miner.add_log_message("service.auth.user.alice.ok")
    c2 = dot_miner.add_log_message("service.auth.user.bob.ok")
    dot_template = c2.get_template()
    assert c1.cluster_id == c2.cluster_id and dot_template == "service auth user <*> ok"
    dot_extract = dot_miner.extract_parameters(dot_template, "service.auth.user.bob.ok")
    assert dot_extract is None  # `re.sub(".", " ", ...)` wipes message to all spaces!

    bracket_miner = TemplateMinerPort(
        DrainPort(depth=4, sim_th=0.4, extra_delimiters=["["]),
        LogMaskerPort([], mask_prefix="<", mask_suffix=">"),
    )
    b_cluster = bracket_miner.add_log_message(" pod[0 ")
    bracket_raises = False
    try:
        bracket_miner.extract_parameters(b_cluster.get_template(), " pod[0 ")
    except re.error:
        bracket_raises = True
    assert bracket_raises

    # Even safe `extra_delimiters = ["_"]` (`examples/drain3.ini:26`) breaks `exact_matching=True`
    # when a mask matches an underscore-bearing token (`USER_42`) AND splits variable snake_case!
    us_miner = TemplateMinerPort(
        DrainPort(depth=4, sim_th=0.4, extra_delimiters=["_"]),
        LogMaskerPort([MaskingInstructionPort(r"USER_\d+", "UID")]),
    )
    uc = us_miner.add_log_message("login USER_42 ok")
    assert uc.get_template() == "login <:UID:> ok"
    us_exact_extract = us_miner.extract_parameters(
        uc.get_template(), "login USER_42 ok", exact_matching=True
    )
    assert us_exact_extract is None  # `re.sub("_", " ", "login USER_42 ok")` -> `"login USER 42 ok"`!

    us_miner.add_log_message("status err_conn_reset retry")
    us_miner.add_log_message("status err_timeout retry")
    snake_distinct_clusters = len(us_miner.drain.id_to_cluster) - 1  # 2 disjoint length subtrees
    assert snake_distinct_clusters == 2

    # 2. `set(mask_names)` order-dependent `p_k` regex compilation vs. preserved unnested
    # `groupdict()` left-to-right order (`template_miner.py:243, 307-327`), & `.+?` stealing
    default_ini_rules = [
        MaskingInstructionPort(
            r"((?<=[^A-Za-z0-9])|^)(([0-9a-f]{2,}:){3,}([0-9a-f]{2,}))((?=[^A-Za-z0-9])|$)",
            "ID",
        ),
        MaskingInstructionPort(
            r"((?<=[^A-Za-z0-9])|^)(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})((?=[^A-Za-z0-9])|$)",
            "IP",
        ),
        MaskingInstructionPort(
            r"((?<=[^A-Za-z0-9])|^)(0x[a-f0-9A-F]+)((?=[^A-Za-z0-9])|$)", "HEX"
        ),
        MaskingInstructionPort(
            r"((?<=[^A-Za-z0-9])|^)([\-\+]?\d+)((?=[^A-Za-z0-9])|$)", "NUM"
        ),
    ]
    ini_path = tmp_root / "drain3_rules.json"
    ini_path.write_text(
        json.dumps([{"mask": r.mask_with, "pat": r.pattern} for r in default_ini_rules]),
        encoding="utf-8",
    )
    loaded_rules = json.loads(ini_path.read_text(encoding="utf-8"))
    assert len(loaded_rules) == 4

    order_miner = TemplateMinerPort(DrainPort(), LogMaskerPort(default_ini_rules))
    rx_a, map_a = order_miner.build_extraction_regex(
        "conn <:IP:> port <:NUM:>", True, mask_name_order=["IP", "NUM", "*"]
    )
    rx_b, map_b = order_miner.build_extraction_regex(
        "conn <:IP:> port <:NUM:>", True, mask_name_order=["NUM", "IP", "*"]
    )
    params_a = order_miner.extract_parameters(
        "conn <:IP:> port <:NUM:>",
        "conn 10.0.0.1 port 8080",
        True,
        mask_name_order=["IP", "NUM", "*"],
    )
    params_b = order_miner.extract_parameters(
        "conn <:IP:> port <:NUM:>",
        "conn 10.0.0.1 port 8080",
        True,
        mask_name_order=["NUM", "IP", "*"],
    )
    unnested_order_preserved = params_a == params_b == [("10.0.0.1", "IP"), ("8080", "NUM")]
    assert rx_a != rx_b and map_a != map_b and unnested_order_preserved

    wildcard_miner = TemplateMinerPort(
        DrainPort(), LogMaskerPort([], mask_prefix="<", mask_suffix=">")
    )
    stolen = wildcard_miner.extract_parameters(
        "exec <*> <*>", "exec rm -rf /var/log", exact_matching=False
    )
    assert stolen == [("rm", "*"), ("-rf /var/log", "*")]

    # 3. `LogMasker` sequential ordering destruction (`NUM` before `IP`, and UUID partial corruption)
    wrong_order_masker = LogMaskerPort([default_ini_rules[3], default_ini_rules[1]])
    ip_clobbered = wrong_order_masker.mask("connect 10.0.0.1")
    default_masker = LogMaskerPort(default_ini_rules)
    sample_rfc4122_uuid = "-".join(("550e8400", "e29b", "41d4", "a716", "446655440000"))
    uuid_corrupted = default_masker.mask(f"req {sample_rfc4122_uuid}")
    assert ip_clobbered == "connect <:NUM:>.<:NUM:>.<:NUM:>.<:NUM:>"
    assert uuid_corrupted == "req 550e8400-e29b-41d4-a716-<:NUM:>"

    # 4. Greedy `tree_search` false negative & `max_children` arrival-order selection
    greedy_drain = DrainPort(depth=4, sim_th=0.5)
    greedy_drain.add_log_message("101 req timeout")
    greedy_drain.add_log_message("202 req timeout")  # template `"<*> req timeout"` under `<*>`
    greedy_drain.add_log_message("login req succeeded")  # creates literal branch `"login"`
    match_never = greedy_drain.match("login req timeout", full_search_strategy="never")
    match_fallback = greedy_drain.match("login req timeout", full_search_strategy="fallback")
    assert match_never is None and match_fallback is not None
    assert match_fallback.get_template() == "<*> req timeout"

    # `max_children = 3` (`drain.py:365-383`): both numeric-first (`L366`) and literal-first
    # (`L373-380`) cap literal branches symmetrically at `max_children - 1 = 2`, while arrival
    # order determines which literal gets forced into `<*>` and `max_children = 0` crashes
    # with `KeyError('<*>')` at `L382`.
    d_num_first = DrainPort(depth=4, sim_th=0.8, max_children=3)
    for msg in ["99 a0 b0", "alpha a1 b1", "beta a2 b2", "gamma a3 b3"]:
        d_num_first.add_log_message(msg)
    keys_num_first = sorted(d_num_first.root_node.key_to_child_node["3"].key_to_child_node.keys())

    d_lit_first = DrainPort(depth=4, sim_th=0.8, max_children=3)
    for msg in ["alpha a1 b1", "beta a2 b2", "gamma a3 b3"]:
        d_lit_first.add_log_message(msg)
    keys_lit_first = sorted(d_lit_first.root_node.key_to_child_node["3"].key_to_child_node.keys())

    max_children_zero_exc = "None"
    try:
        DrainPort(depth=4, sim_th=0.8, max_children=0).add_log_message("alpha a1 b1")
    except KeyError as exc:
        max_children_zero_exc = f"{type(exc).__name__}({exc})"
    assert keys_num_first == ["<*>", "alpha", "beta"] and keys_lit_first == ["<*>", "alpha", "beta"]
    assert max_children_zero_exc == "KeyError('<*>')"

    print("=== PROBE 1: Drain3 Prefix-Tree Mechanics & Live Source Defects ===")
    print(
        f"  extra_delimiters desync: dot_extract={dot_extract}, bracket_re_error={bracket_raises}, "
        f"underscore_masked_exact={us_exact_extract}, snake_case_clusters={snake_distinct_clusters}"
    )
    print(
        f"  set(mask_names) & non-greedy capture: hash_order_changes_regex={rx_a != rx_b}, "
        f"unnested_groupdict_order_preserved={unnested_order_preserved}, "
        f"multiword_steal={[v for v, _ in stolen]}"
    )
    print(
        f"  LogMasker ordering: num_before_ip='{ip_clobbered}', uuid_default='{uuid_corrupted}'"
    )
    print(
        f"  tree_search & max_children: match_never={match_never}, "
        f"match_fallback='{match_fallback.get_template()}', "
        f"max3_keys=(num_first={keys_num_first}, lit_first={keys_lit_first}), "
        f"max0_exc={max_children_zero_exc}"
    )


# ============================================================================
# PROBE 2: Evaluator Gaming (GA/PA/FGA/FTA) & LILAC Cache/Selector Forensics
# ============================================================================


def compute_log_parsing_metrics(
    oracle_templates: Sequence[str], predicted_templates: Sequence[str]
) -> dict[str, float]:
    """Exact formulas from `LogPai` (`evaluator.py`), `Khan ICSE '22` (§3.1.1),
    and `Loghub-2.0` (`LILAC/benchmark/logparser/utils/evaluator.py:61-98`,
    `PA_calculator.py:64-75`)."""
    n_msgs = len(oracle_templates)
    assert n_msgs == len(predicted_templates) and n_msgs > 0

    gt_groups: dict[str, list[int]] = {}
    pred_groups: dict[str, list[int]] = {}
    for idx, (gt, pr) in enumerate(zip(oracle_templates, predicted_templates)):
        gt_groups.setdefault(gt, []).append(idx)
        pred_groups.setdefault(pr, []).append(idx)

    accurate_events = 0
    accurate_grouped_templates = 0
    for gt_tmpl, gt_indices in gt_groups.items():
        pr_set = {predicted_templates[i] for i in gt_indices}
        if len(pr_set) == 1:
            only_pr = next(iter(pr_set))
            if len(pred_groups[only_pr]) == len(gt_indices):
                accurate_events += len(gt_indices)
                accurate_grouped_templates += 1

    ga = accurate_events / n_msgs
    pga = accurate_grouped_templates / len(pred_groups)
    rga = accurate_grouped_templates / len(gt_groups)
    fga = (2.0 * pga * rga / (pga + rga)) if (pga + rga) > 0 else 0.0

    # `PA_calculator.py:71`: exact character-for-character template string equality
    pa = sum(1 for gt, pr in zip(oracle_templates, predicted_templates) if gt == pr) / n_msgs

    # `Khan et al. ICSE '22 §3.1.1`: `corrOT(t) == {t}`
    correct_templates = 0
    for pr_tmpl, pr_indices in pred_groups.items():
        corr_ot = {oracle_templates[i] for i in pr_indices}
        if corr_ot == {pr_tmpl} and len(gt_groups.get(pr_tmpl, ())) == len(pr_indices):
            correct_templates += 1

    pta = correct_templates / len(pred_groups)
    rta = correct_templates / len(gt_groups)
    fta = (2.0 * pta * rta / (pta + rta)) if (pta + rta) > 0 else 0.0
    return {
        "GA": round(ga, 4),
        "PA": round(pa, 4),
        "FGA": round(fga, 4),
        "FTA": round(fta, 4),
    }


def lilac_clean_buggy(s: str) -> str:
    """Verbatim port of `logpai/LILAC@163d199f` `prompt_select.py:36-55` (`return s` at `L47`)."""
    return s


def lilac_clean_intended(s: str) -> str:
    """Intended body of `prompt_select.py:48-55` made unreachable by `L47: return s`."""
    s = re.sub(r":|\(|\)|=|,|\"|\{|\}|@|$|\[|\]|\||;|\.", " ", s)
    s = " ".join([word.lower() if word.isupper() else word for word in s.strip().split()])
    s = re.sub(r"([A-Z][a-z]+)", r" \1", re.sub(r"([A-Z]+)", r" \1", s))
    s = " ".join([word for word in s.split() if not bool(re.search(r"\d", word))])
    trantab = str.maketrans(dict.fromkeys(list(string.punctuation)))
    s = s.translate(trantab)
    s = " ".join([word.lower().strip() for word in s.strip().split()])
    return s


def lilac_jaccard_distance(x: str, y: str) -> float:
    """Normalized set Jaccard distance on `.split()` (`prompt_select.py:28-29`)."""
    sx, sy = set(x.split()), set(y.split())
    if not sx and not sy:
        return 0.0
    return 1.0 - (len(sx & sy) / len(sx | sy))


def lilac_prompt_select(
    prompts: list[dict[str, object]],
    log: str,
    k: int,
    clean_fn: Callable[[str], str],
) -> list[str]:
    """Port of `prompt_select.py:58-79` (note in-place `d['similarity']` mutation at `L70-71`)."""
    log_c = clean_fn(log)
    for d in prompts:
        d["similarity"] = lilac_jaccard_distance(clean_fn(str(d["query"])), log_c)
    ranked = sorted(prompts, key=lambda d: float(d["similarity"]))[:k]
    return [str(x["query"]) for x in ranked]


LILAC_PUNC = "!\"#$%&'()+,-/:;=?@.[\\]^_`{|}~"


def lilac_message_split(message: str) -> list[str]:
    """Verbatim port of `logpai/LILAC@163d199f` `parsing_cache.py:153-198`."""
    excluded_str = ["=", "|", "(", ")"]
    splitters = r"\s\\" + "\\".join(LILAC_PUNC)
    splitter_regex = re.compile(f"([{splitters}])")
    tokens = [t for t in re.split(splitter_regex, message) if t != ""]
    for i in range(len(tokens)):
        if tokens[i].find("<*>") != -1:
            tokens[i] = "<*>"
        else:
            tokens[i] = "".join(
                s for s in tokens[i] if (s not in LILAC_PUNC and s != " ") or s in excluded_str
            )
    tokens = [t.strip() for t in tokens if t != "" and t != " "]
    tokens = [
        t for idx, t in enumerate(tokens) if not (t == "<*>" and idx > 0 and tokens[idx - 1] == "<*>")
    ]
    return tokens


def lcs_similarity(seq_x: Sequence[str], seq_y: Sequence[str]) -> float:
    """Verbatim port of `parsing_cache.py:21-30`."""
    m, n = len(seq_x), len(seq_y)
    c = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if seq_x[i - 1] == seq_y[j - 1]:
                c[i][j] = c[i - 1][j - 1] + 1
            else:
                c[i][j] = max(c[i][j - 1], c[i - 1][j])
    return 2.0 * c[m][n] / (m + n)


class LilacParsingCachePort:
    """Faithful port of `logpai/LILAC@163d199f` `parsing_cache.py:33-259`."""

    def __init__(self) -> None:
        self.template_tree: dict[str, object] = {}
        self.template_list: list[str] = []

    def add_templates(
        self,
        event_template: str,
        insert: bool = True,
        relevant_templates: Sequence[str] = (),
    ) -> int:
        template_tokens = lilac_message_split(event_template)
        if not template_tokens or event_template == "<*>":
            return -1
        if insert or len(relevant_templates) == 0:
            tid = self.insert(event_template, template_tokens, len(self.template_list))
            self.template_list.append(event_template)
            return tid
        max_sim = 0.0
        similar_template: Optional[str] = None
        for rt in relevant_templates:
            # `parsing_cache.py:57-60`: uses `.split()`, NOT `message_split()`!
            s1, s2 = rt.split(), event_template.split()
            if len(s1) != len(s2):
                continue
            sim = lcs_similarity(s1, s2)
            if sim > max_sim:
                max_sim = sim
                similar_template = rt
        if max_sim > 0.8 and similar_template is not None:
            ok, tid = self.modify(similar_template, event_template)
            if not ok:
                tid = self.insert(event_template, template_tokens, len(self.template_list))
                self.template_list.append(event_template)
            return tid
        tid = self.insert(event_template, template_tokens, len(self.template_list))
        self.template_list.append(event_template)
        return tid

    def insert(self, event_template: str, template_tokens: Sequence[str], template_id: int) -> int:
        move: dict[str, object] = self.template_tree.setdefault(template_tokens[0], {})  # type: ignore[assignment]
        for tok in template_tokens[1:]:
            move = move.setdefault(tok, {})  # type: ignore[assignment]
        move["".join(template_tokens)] = (
            sum(1 for s in template_tokens if s != "<*>"),
            template_tokens.count("<*>"),
            event_template,
            template_id,
        )
        return template_id

    def delete(self, event_template: str) -> tuple[bool, int]:
        template_tokens = lilac_message_split(event_template)
        if template_tokens[0] not in self.template_tree:
            return False, -1
        move: dict[str, object] = self.template_tree[template_tokens[0]]  # type: ignore[assignment]
        for tok in template_tokens[1:]:
            if tok not in move or not isinstance(move[tok], dict):
                return False, -1
            move = move[tok]  # type: ignore[assignment]
        leaf = move["".join(template_tokens)]
        old_id = leaf[3]  # type: ignore[index]
        # `parsing_cache.py:137`: deletes leaf tuple only; never prunes empty ancestor dicts!
        del move["".join(template_tokens)]
        return True, int(old_id)

    def modify(self, similar_template: str, event_template: str) -> tuple[bool, int]:
        # `parsing_cache.py:100-119`: merges via `.split()`, then re-inserts via `message_split`!
        s_toks = similar_template.split()
        e_toks = event_template.split()
        merged = " ".join(t1 if t1 == t2 else "<*>" for t1, t2 in zip(s_toks, e_toks))
        ok, old_id = self.delete(similar_template)
        if not ok:
            return False, -1
        self.insert(merged, lilac_message_split(merged), old_id)
        self.template_list[old_id] = merged
        return True, old_id

    def match_event(self, log_content: str) -> object:
        log_tokens = lilac_message_split(log_content)
        results: list[tuple[object, object, object]] = []
        self._find_template(self.template_tree, log_tokens, results, [], 1)
        # `parsing_cache.py:217-227`: skips `None` filtering whenever `len(results) <= 1`!
        if len(results) > 1:
            new_results = [
                r for r in results if r[0] is not None and r[1] is not None and r[2] is not None
            ]
        else:
            new_results = results
        if len(new_results) > 0:
            if len(new_results) > 1:
                new_results.sort(key=lambda x: (-x[1][0], x[1][1]))  # type: ignore[index]
            return new_results[0][1][2], new_results[0][1][3], new_results[0][2]  # type: ignore[index]
        return False

    def _find_template(
        self,
        move_tree: dict[str, object],
        log_tokens: list[str],
        result: list[tuple[object, object, object]],
        parameter_list: list[str],
        depth: int,
    ) -> bool:
        # `parsing_cache.py:241-314`
        flag = 0
        if len(log_tokens) == 0:
            for key, value in move_tree.items():
                if isinstance(value, tuple):
                    result.append((key, value, tuple(parameter_list)))
                    flag = 2
            if "<*>" in move_tree:
                # `parsing_cache.py:249`: appends `""` to caller's `parameter_list` without popping!
                parameter_list.append("")
                sub = move_tree["<*>"]
                if isinstance(sub, tuple):
                    # `parsing_cache.py:251-252`: appends `("<*>", None, None)`!
                    result.append(("<*>", None, None))
                    flag = 2
                elif isinstance(sub, dict):
                    for key, value in sub.items():
                        if isinstance(value, tuple):
                            result.append((key, value, tuple(parameter_list)))
                            flag = 2
        else:
            tok = log_tokens[0]
            if tok in move_tree and isinstance(move_tree[tok], dict):
                if self._find_template(move_tree[tok], log_tokens[1:], result, parameter_list, depth + 1):  # type: ignore[arg-type]
                    flag = 2
            if "<*>" in move_tree and isinstance(move_tree["<*>"], dict):
                sub_wild: dict[str, object] = move_tree["<*>"]  # type: ignore[assignment]
                next_keys = [nk for nk, nv in sub_wild.items() if not isinstance(nv, tuple)]
                idx = 0
                while idx < len(log_tokens):
                    if log_tokens[idx] in next_keys:
                        parameter_list.append("".join(log_tokens[0:idx]))
                        if self._find_template(sub_wild, log_tokens[idx:], result, parameter_list, depth + 1):
                            flag = 2
                        if parameter_list:
                            parameter_list.pop()
                    idx += 1
                if idx == len(log_tokens):
                    parameter_list.append("".join(log_tokens[0:idx]))
                    if self._find_template(sub_wild, log_tokens[idx + 1 :], result, parameter_list, depth + 1):
                        flag = 2
                    if parameter_list:
                        parameter_list.pop()
        return flag == 2


def run_probe_2() -> None:
    # 1. Exact `Loghub-2.0` 14-dataset scale & `LILAC` CSV averages (`README.md` + `result/*.csv`)
    loghub20_datasets = [
        ("Hadoop", 179_993, 236, 114),
        ("HDFS", 11_167_740, 46, 14),
        ("OpenStack", 207_632, 48, 43),
        ("Spark", 16_075_117, 236, 36),
        ("Zookeeper", 74_273, 89, 50),
        ("BGL", 4_631_261, 320, 120),
        ("HPC", 429_987, 74, 46),
        ("Thunderbird", 16_601_745, 1_241, 149),
        ("Linux", 23_921, 338, 118),
        ("Mac", 100_314, 626, 341),
        ("Apache", 51_977, 29, 6),
        ("OpenSSH", 638_946, 38, 27),
        ("HealthApp", 212_394, 156, 75),
        ("Proxifier", 21_320, 11, 8),
    ]
    total_logs = sum(x[1] for x in loghub20_datasets)
    total_t20 = sum(x[2] for x in loghub20_datasets)
    total_t2k = sum(x[3] for x in loghub20_datasets)
    assert len(loghub20_datasets) == 14
    assert total_logs == 50_416_620 and total_t20 == 3_488 and total_t2k == 1_147

    # 2. `[illustrative analytical model]`: 1,000-line skewed log corpus
    # (`950` lines across `2` heartbeat templates + `50` lines across `48` rare error templates)
    oracle: list[str] = ["hb_ok host=<*>"] * 475 + ["hb_sync seq=<*>"] * 475
    for err_id in range(48):
        count = 2 if err_id < 2 else 1
        oracle.extend([f"err_{err_id:02d} code=<*> detail=<*>"] * count)
    assert len(oracle) == 1_000 and len(set(oracle)) == 50

    # Gaming Case A: Exact cluster partition with over-generalized/opaque templates (`IPLoM`/`HDFS`)
    pred_case_a = [f"CLUSTER_HASH_{hashlib.sha1(t.encode()).hexdigest()[:8]}" for t in oracle]
    m_case_a = compute_log_parsing_metrics(oracle, pred_case_a)
    assert m_case_a == {"GA": 1.0, "PA": 0.0, "FGA": 1.0, "FTA": 0.0}

    # Gaming Case B: 2 heartbeats (`950` lines) + 10 rare 5-line error templates (`50` lines)
    # where variable-length stack frames fragment all 50 rare lines into singleton clusters
    # (`|T_pred| = 52` vs `|O| = 12`, mirroring `Drain` on `OpenStack` in `Loghub-2.0`):
    oracle_b: list[str] = ["hb_ok host=<*>"] * 475 + ["hb_sync seq=<*>"] * 475
    pred_b: list[str] = list(oracle_b)
    for r_id in range(10):
        for sub_idx in range(5):
            oracle_b.append(f"err_{r_id:02d} stack=<*>")
            pred_b.append(f"err_{r_id:02d} stack=frame_{r_id}_{sub_idx}")
    assert len(oracle_b) == 1_000 and len(set(oracle_b)) == 12 and len(set(pred_b)) == 52
    m_case_b = compute_log_parsing_metrics(oracle_b, pred_b)
    assert m_case_b["GA"] == 0.95 and m_case_b["FGA"] == 0.0625 and m_case_b["FTA"] == 0.0625

    # Gaming Case C: Single-space formatting difference around `=` (`PA_calculator.py:71`)
    pred_case_c = [t.replace("=", " = ") for t in oracle_b]
    m_case_c = compute_log_parsing_metrics(oracle_b, pred_case_c)
    assert m_case_c == {"GA": 1.0, "PA": 0.0, "FGA": 1.0, "FTA": 0.0}

    # 3. `LILAC` `prompt_select.py:47` dead-code `return s` + in-place dict mutation
    candidates: list[dict[str, object]] = [
        {"query": "abort uid=99 reason=oom", "answer": "abort uid=<*> reason=<*>"},
        {"query": "conn:uid=1,host=node1", "answer": "conn:uid=<*>,host=<*>"},
    ]
    pick_buggy = lilac_prompt_select(candidates, "conn:uid=99,host=node9", 1, lilac_clean_buggy)
    mutated_in_place = "similarity" in candidates[0]
    pick_fixed = lilac_prompt_select(candidates, "conn:uid=99,host=node9", 1, lilac_clean_intended)
    assert pick_buggy == ["abort uid=99 reason=oom"]
    assert pick_fixed == ["conn:uid=1,host=node1"] and mutated_in_place

    # 4. `LILAC` `ParsingCache` `.split()` vs `message_split()` mismatch, orphan dicts,
    # unpopped `L249` `parameter_list.append("")` mutation, & `L252` public-API invariant
    cache = LilacParsingCachePort()
    cache.add_templates("auth user = <*> ok", insert=True)
    # Identical 5-token `message_split` (`['auth', 'user', '=', '<*>', 'ok']`),
    # yet `.split()` has len 5 vs len 3, so `add_templates` skips merging and duplicates!
    cache.add_templates("auth user=<*> ok", insert=False, relevant_templates=["auth user = <*> ok"])
    split_mismatch_dups = len(cache.template_list)
    assert split_mismatch_dups == 2

    cache_del = LilacParsingCachePort()
    cache_del.add_templates("net eth0 down", insert=True)
    ok_del, _ = cache_del.delete("net eth0 down")
    orphan_dict_retained = ok_del and ("net" in cache_del.template_tree)
    assert orphan_dict_retained

    # Public-API reachability invariant (`parsing_cache.py:90, 217-227, 243-258`):
    # Through `add_templates` / `insert` / `modify` / `delete`, `move_tree["<*>"]` is a `tuple`
    # iff `"".join(template_tokens) == "<*>"` (`insert` `L90`, reachable via `add_templates("<*>.")`
    # because `"<*>." != "<*>"` at `L47` while `message_split("<*>.") == ["<*>"]`). Whenever
    # `find_template` reaches `len(log_tokens) == 0` (`L243`) on that `move_tree`, `L244-246`
    # always visits `key == "<*>"` first and appends `("<*>", value, tuple(parameter_list))`
    # before `L249` mutates `parameter_list` in-place via an unpopped `parameter_list.append("")`
    # and `L251-252` appends `("<*>", None, None)`. Consequently `len(results) >= 2` across all
    # public-API trees (`L217-221` strips the `None` tuple), whereas `L227` raises `TypeError`
    # if `template_tree` is mutated externally or `len(results) == 1` contains `("<*>", None, None)`.
    cache_crash = LilacParsingCachePort()
    cache_crash.add_templates("<*>.", insert=True)
    res_list: list[tuple[object, object, object]] = []
    caller_params: list[str] = ["seed_param"]
    cache_crash._find_template(
        cache_crash.template_tree["<*>"], [], res_list, caller_params, 2  # type: ignore[arg-type]
    )
    appended_none_tuple = ("<*>", None, None) in res_list
    unpopped_l249_mutation = caller_params == ["seed_param", ""]
    single_hit_exc = "None"
    try:
        only_res = [r for r in res_list if r[1] is None]
        if len(only_res) == 1:
            _ = only_res[0][1][2]  # type: ignore[index]  # exact `L227: new_results[0][1][2]`
    except TypeError as exc:
        single_hit_exc = type(exc).__name__
    assert (
        appended_none_tuple
        and unpopped_l249_mutation
        and len(res_list) == 2
        and single_hit_exc == "TypeError"
    )

    print("=== PROBE 2: Log Evaluator Metric Gaming & LILAC Cache Forensics ===")
    print(
        f"  Loghub-2.0 verified totals (14 systems): logs={total_logs}, "
        f"templates_2.0={total_t20} (mean={total_t20/14:.3f}) vs templates_2k={total_t2k} (mean={total_t2k/14:.3f})"
    )
    print(
        f"  [illustrative analytical model] 1,000-line metric gaming: "
        f"opaque_partition={m_case_a}, rare_error_split={m_case_b}, space_around_eq={m_case_c}"
    )
    print(
        f"  LILAC prompt_select (`L47 return s`): buggy_top1='{pick_buggy[0]}' vs "
        f"intended_top1='{pick_fixed[0]}', mutates_caller_dicts={mutated_in_place}"
    )
    print(
        f"  LILAC ParsingCache: split_vs_message_split_templates={split_mismatch_dups}, "
        f"delete_retains_orphan_dict={orphan_dict_retained}, "
        f"L249_unpopped_param_mutation={unpopped_l249_mutation}, "
        f"L252_appends_none_tuple={appended_none_tuple} (public_api_len={len(res_list)}, L227_on_len1={single_hit_exc})"
    )


# ============================================================================
# PROBE 3: OTel tailsamplingprocessor, 56-Bit TraceState & Multi-Pod Sharding
# ============================================================================

MAX_ADJUSTED_COUNT = 1 << 56  # `pkg/sampling/threshold.go:14`
NUM_HEX_DIGITS = 14  # `pkg/sampling/threshold.go:18`


def otel_prob_to_threshold(fraction: float, precision: int = NUM_HEX_DIGITS) -> tuple[int, str, float]:
    """Verbatim port of `pkg/sampling/probability.go:33-82` & `threshold.go:99-114`."""
    assert 0.0 < fraction <= 1.0
    if fraction == 1.0:
        return 0, "0", 1.0
    _, exp_f = math.frexp(fraction)
    _, exp_r = math.frexp(1.0 - fraction)
    # Note Go integer division `expF / -4` truncates toward zero!
    adj_f = int(exp_f / -4)
    adj_r = int(exp_r / -4)
    eff_prec = min(NUM_HEX_DIGITS, max(precision + adj_f, precision + adj_r))
    scaled = round(fraction * float(MAX_ADJUSTED_COUNT))
    threshold = MAX_ADJUSTED_COUNT - scaled
    shift = 4 * (NUM_HEX_DIGITS - eff_prec)
    if shift != 0:
        half = 1 << (shift - 1)
        threshold = ((threshold + half) >> shift) << shift
    t_val = f"{threshold:014x}".rstrip("0") or "0"
    adj_count = float(MAX_ADJUSTED_COUNT) / float(MAX_ADJUSTED_COUNT - threshold)
    return threshold, t_val, adj_count


def splitmix64_trace_shard(trace_id_16b: bytes, num_shards: int) -> int:
    """Verbatim port of `sharded_processor.go:233-247` (`traceIDToShard`)."""
    lo, hi = struct.unpack("<QQ", trace_id_16b)
    h = (lo ^ hi) & 0xFFFFFFFFFFFFFFFF
    h ^= h >> 30
    h = (h * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
    h ^= h >> 27
    h = (h * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF
    h ^= h >> 31
    return int(h % num_shards)


@dataclass
class SpanEvent:
    trace_id: int
    span_id: int
    parent_id: Optional[int]
    is_error: bool
    randomness_56b: int


class IdBatcherPort:
    """Verbatim 1-for-1 port of `processor/tailsamplingprocessor/internal/idbatcher/id_batcher.go:75-101, 143-158`."""

    def __init__(self, num_batches: int) -> None:
        if num_batches < 1:
            raise ValueError("num_batches must be >= 1")
        # `id_batcher.go:85-90`: pipe of `numBatches` `Batch` slots (`nil` initially)
        # PLUS a separate `currentBatch` (`map[TraceID]struct{}`) outside the pipe!
        self.batches: list[Optional[set[int]]] = [None] * num_batches
        self.current_batch: set[int] = set()
        self.take_id: int = 0

    def add_to_current_batch(self, tid: int) -> int:
        # `id_batcher.go:95-101`: `b.currentBatch[id] = struct{}{}` (set deduplication!)
        self.current_batch.add(tid)
        return self.take_id + len(self.batches)

    def close_current_and_take_first_batch(self) -> Optional[set[int]]:
        # `id_batcher.go:143-158`
        take_idx = self.take_id % len(self.batches)
        read_batch = self.batches[take_idx]
        self.batches[take_idx] = self.current_batch
        self.current_batch = set()
        self.take_id += 1
        return read_batch


class TailSamplingProcessorPort:
    """Faithful 1-for-1 discrete-event port of `tailsamplingprocessor/processor.go` + `idbatcher.Batcher`."""

    def __init__(
        self,
        num_traces: int,
        decision_wait_ticks: int,
        non_sampled_cache_enabled: bool = True,
        evicted_id_suppression_cache: bool = False,
    ) -> None:
        self.num_traces = num_traces
        # `processor.go:211-212`: `numDecisionBatches := math.Max(1, tsp.cfg.DecisionWait.Seconds())`
        self.batcher = IdBatcherPort(num_batches=max(1, decision_wait_ticks))
        self.non_sampled_cache_enabled = non_sampled_cache_enabled
        self.evicted_id_suppression_cache = evicted_id_suppression_cache
        self.id_to_trace: dict[int, dict[str, object]] = {}
        self.delete_queue: list[int] = []  # FIFO queue (`deleteTraceQueue`)
        self.sampled_cache: set[int] = set()
        self.non_sampled_cache: set[int] = set()
        self.dropped_too_early = 0
        self.spurious_sampled_dropped_too_early = 0
        self.cascade_evictions = 0
        self.non_sampled_hook_calls = 0
        self.exported_traces: dict[int, list[SpanEvent]] = {}

    def ingest_span(self, span: SpanEvent) -> None:
        tid = span.trace_id
        # `processor.go:598-626`: `processCachedTrace`
        if tid in self.sampled_cache:
            self.exported_traces.setdefault(tid, []).append(span)
            return
        if self.non_sampled_cache_enabled and tid in self.non_sampled_cache:
            return

        # `processor.go:573-576, 630-652`: `waitForSpace` -> `dropTrace`
        if tid not in self.id_to_trace and len(self.id_to_trace) >= self.num_traces:
            victim = self.delete_queue.pop(0)
            del self.id_to_trace[victim]
            if span.parent_id is not None:
                self.cascade_evictions += 1
            # Upstream `dropTrace` (`L1366-1387`) neither removes `victim` from
            # `decisionBatcher` nor records `victim` in `nonSampledIDCache` (unlike
            # Canopy SOSP '17 §4.2's 5-hour auxiliary `TraceID` cache)!
            if self.evicted_id_suppression_cache:
                self.non_sampled_cache.add(victim)

        # `processor.go:1200-1318`: `processTrace`
        if tid not in self.id_to_trace:
            batch_id = self.batcher.add_to_current_batch(tid)
            self.id_to_trace[tid] = {
                "spans": [span],
                "final_decision": "unspecified",
                "batch_id": batch_id,
            }
            self.delete_queue.append(tid)
        else:
            entry = self.id_to_trace[tid]
            decision = entry["final_decision"]
            if decision == "unspecified":
                entry["spans"].append(span)  # type: ignore[union-attr]
            elif decision == "sampled":
                self.exported_traces.setdefault(tid, []).append(span)
            elif decision == "not_sampled":
                # `processor.go:1313-1315`: when `nonSampledIDCache` is a `NopCache`,
                # `idToTrace` retains the trace (`L1425-1428`) and re-fires `nonSampledHooks`!
                self.non_sampled_hook_calls += 1

    def on_tick(self) -> None:
        # `processor.go:731, 750-761, 850-868`
        batch = self.batcher.close_current_and_take_first_batch()
        if batch is None:
            return
        for tid in sorted(batch):
            entry = self.id_to_trace.get(tid)
            if entry is None:
                # `processor.go:751-754, 867`: `idNotFoundOnMapCount++` (`DroppedTooEarly`)
                # Fires whenever `idToTrace[id]` is `!ok` — even if `id` is already in `sampledIDCache`!
                self.dropped_too_early += 1
                if tid in self.sampled_cache:
                    self.spurious_sampled_dropped_too_early += 1
                continue
            if entry["final_decision"] != "unspecified":
                continue
            spans: list[SpanEvent] = entry["spans"]  # type: ignore[assignment]
            has_err = any(s.is_error for s in spans)
            if has_err:
                entry["final_decision"] = "sampled"
                self.sampled_cache.add(tid)
                self.exported_traces.setdefault(tid, []).extend(spans)
                del self.id_to_trace[tid]
                if tid in self.delete_queue:
                    self.delete_queue.remove(tid)
            else:
                entry["final_decision"] = "not_sampled"
                self.non_sampled_hook_calls += 1
                if self.non_sampled_cache_enabled:
                    self.non_sampled_cache.add(tid)
                    del self.id_to_trace[tid]
                    if tid in self.delete_queue:
                        self.delete_queue.remove(tid)


def divide_rate_port(v: int, num_shards: int) -> int:
    """Verbatim port of `sharded_processor.go:153-158` (`divideRate`)."""
    if v <= 0:
        return v
    return max(1, v // num_shards)


def composite_evaluate_port(
    span_count: int,
    matches_sub: Sequence[bool],
    allocated_sps: Sequence[int],
    sampled_sps: list[int],
    max_total_sps: int,
) -> bool:
    """Verbatim port of `internal/sampling/composite.go:103-135` (`Composite.Evaluate`)."""
    for i, matched in enumerate(matches_sub):
        if matched:
            if_sampled = sampled_sps[i] + span_count
            if if_sampled <= allocated_sps[i] and if_sampled <= max_total_sps:
                sampled_sps[i] = if_sampled
                return True
            # `composite.go:131`: returns `NotSampled` immediately on first matching
            # sub-policy rate overflow WITHOUT checking later matching sub-policies!
            return False
    return False


def run_probe_3() -> None:
    # 1. `NumTraces` overflow + `idbatcher.Batcher` (`processor.go:211-216, 647, 731, 751-754` &
    #    `id_batcher.go:75-101, 143-158`) with `NumTraces = 100`, `num_batches = 2`:
    #    - Root burst at `take_id = 0`: `50` error roots (`1..50`) + `100` benign roots (`101..200`)
    #      evict `1..50` from `idToTrace` while `currentBatch` holds `{1..50, 101..200}`.
    #    - Subcase A (`tid = 1..10`, same-tick re-insertion at `take_id = 0` before Tick 1):
    #      `AddToCurrentBatch` deduplicates into the SAME `currentBatch` set (`len == 150`),
    #      causing `10` cascade evictions (`101..110`) with ZERO premature evaluations and ZERO
    #      spurious `DroppedTooEarly` increments!
    #    - Subcase B (`tid = 11..35`, cross-tick re-insertion at `take_id = 1` after Tick 1 closes
    #      `currentBatch` into `batches[0]`): `AddToCurrentBatch` inserts `11..35` into the new
    #      `currentBatch` (`batchID = 3`), causing `25` more cascade evictions (`111..135`). At
    #      Tick 3 (`take_id: 2 -> 3`), `batches[0]` fires the evicted roots' original deadline:
    #      `1..10` waited the full `2` post-close ticks, whereas `11..35` are evaluated `1` tick
    #      early (`num_batches - take_id = 1` post-close tick instead of `2`) and deleted from
    #      `idToTrace` via `releaseSampledTrace`; then at Tick 4 (`take_id: 3 -> 4`), `batches[1]`
    #      fires `11..35` again, hitting `!ok` on `idToTrace` (`processor.go:751-753`) and
    #      incrementing `DroppedTooEarly` `25` times on ALREADY-SAMPLED orphan traces!
    #    - Subcase C (`tid = 36..50`, post-deadline re-insertion at `take_id = 3` after Tick 3
    #      recorded `15` `DroppedTooEarly` on their evicted roots): resurrected as rootless
    #      orphans because `dropTrace` bypassed `nonSampledIDCache`, and exported at Tick 6.
    tsp = TailSamplingProcessorPort(num_traces=100, decision_wait_ticks=2)
    for tid in range(1, 51):
        tsp.ingest_span(SpanEvent(tid, 1, None, is_error=False, randomness_56b=tid))
    for tid in range(101, 201):
        tsp.ingest_span(SpanEvent(tid, 1, None, is_error=False, randomness_56b=tid))

    # Subcase A (`1..10`): child arrives BEFORE Tick 1 (`take_id == 0`)
    for tid in range(1, 11):
        tsp.ingest_span(SpanEvent(tid, 2, 1, is_error=True, randomness_56b=tid))
    same_tick_batch_size = len(tsp.batcher.current_batch)  # deduplicated set `{1..50, 101..200}` = 150!
    assert same_tick_batch_size == 150

    tsp.on_tick()  # Tick 1 (`take_id: 0 -> 1`): `batches[0] = {1..50, 101..200}`, `read_batch = None`

    # Subcase B (`11..35`): child arrives BETWEEN Tick 1 and Tick 2 (`take_id == 1`)
    for tid in range(11, 36):
        tsp.ingest_span(SpanEvent(tid, 2, 1, is_error=True, randomness_56b=tid))

    tsp.on_tick()  # Tick 2 (`take_id: 1 -> 2`): `batches[1] = {11..35}`, `read_batch = None`
    assert len(tsp.exported_traces) == 0  # Neither Subcase A nor Subcase B evaluated before Tick 3

    tsp.on_tick()  # Tick 3 (`take_id: 2 -> 3`): pops `batches[0]`!
    same_tick_full_wait_orphans = sum(1 for tid in range(1, 11) if tid in tsp.exported_traces)
    cross_tick_early_orphans = sum(1 for tid in range(11, 36) if tid in tsp.exported_traces)
    dropped_after_tick3 = tsp.dropped_too_early  # `15` (`36..50`) + `35` (`101..135` cascade) = `50`

    # Subcase C (`36..50`): child arrives AFTER Tick 3 (`take_id == 3`)
    for tid in range(36, 51):
        tsp.ingest_span(SpanEvent(tid, 2, 1, is_error=True, randomness_56b=tid))

    tsp.on_tick()  # Tick 4 (`take_id: 3 -> 4`): pops `batches[1] = {11..35}` -> `+25` spurious DroppedTooEarly!
    tsp.on_tick()  # Tick 5 (`take_id: 4 -> 5`): pops `batches[0] = set()`
    tsp.on_tick()  # Tick 6 (`take_id: 5 -> 6`): pops `batches[1] = {36..50}` -> exports `36..50`!

    orphan_error_traces = sum(
        1
        for tid in range(1, 51)
        if tid in tsp.exported_traces
        and all(s.parent_id is not None for s in tsp.exported_traces[tid])
    )
    complete_error_traces = sum(
        1
        for tid in range(1, 51)
        if tid in tsp.exported_traces
        and any(s.parent_id is None for s in tsp.exported_traces[tid])
    )
    assert same_tick_full_wait_orphans == 10 and cross_tick_early_orphans == 25
    assert dropped_after_tick3 == 50 and tsp.cascade_evictions == 35
    assert tsp.spurious_sampled_dropped_too_early == 25 and tsp.dropped_too_early == 75
    assert orphan_error_traces == 50 and complete_error_traces == 0

    # Contrast with `Canopy` (`SOSP '17 §4.2`, p. 42) 5h auxiliary `TraceID` suppression cache
    # (which suppresses re-entry for both completed/forwarded traces AND evicted traces):
    tsp_canopy = TailSamplingProcessorPort(
        num_traces=100, decision_wait_ticks=2, evicted_id_suppression_cache=True
    )
    for tid in range(1, 51):
        tsp_canopy.ingest_span(SpanEvent(tid, 1, None, is_error=False, randomness_56b=tid))
    for tid in range(101, 201):
        tsp_canopy.ingest_span(SpanEvent(tid, 1, None, is_error=False, randomness_56b=tid))
    for tid in range(1, 11):
        tsp_canopy.ingest_span(SpanEvent(tid, 2, 1, is_error=True, randomness_56b=tid))
    tsp_canopy.on_tick()
    for tid in range(11, 36):
        tsp_canopy.ingest_span(SpanEvent(tid, 2, 1, is_error=True, randomness_56b=tid))
    tsp_canopy.on_tick()
    tsp_canopy.on_tick()
    for tid in range(36, 51):
        tsp_canopy.ingest_span(SpanEvent(tid, 2, 1, is_error=True, randomness_56b=tid))
    tsp_canopy.on_tick()
    tsp_canopy.on_tick()
    tsp_canopy.on_tick()
    assert (
        tsp_canopy.dropped_too_early == 50
        and tsp_canopy.cascade_evictions == 0
        and len(tsp_canopy.exported_traces) == 0
    )

    # Late post-decision `ERROR` span drop (`L618-623`) & `NopCache` repeated hooks (`L1314-1315`)
    # Note: with `num_batches = 1`, Tick 1 closes `currentBatch` into `batches[0]` and Tick 2 pops it.
    tsp_late = TailSamplingProcessorPort(
        num_traces=10, decision_wait_ticks=1, non_sampled_cache_enabled=True
    )
    tsp_late.ingest_span(SpanEvent(900, 1, None, is_error=False, randomness_56b=1))
    tsp_late.on_tick()  # Tick 1: closes `{900}` into `batches[0]`
    tsp_late.on_tick()  # Tick 2: pops `{900}` -> decided `not_sampled`
    tsp_late.ingest_span(SpanEvent(900, 2, 1, is_error=True, randomness_56b=1))  # Slow timeout span!
    late_error_dropped = 900 not in tsp_late.exported_traces

    tsp_nop = TailSamplingProcessorPort(
        num_traces=10, decision_wait_ticks=1, non_sampled_cache_enabled=False
    )
    tsp_nop.ingest_span(SpanEvent(901, 1, None, is_error=False, randomness_56b=1))
    tsp_nop.on_tick()  # Tick 1: closes `{901}` into `batches[0]`
    tsp_nop.on_tick()  # Tick 2: pops `{901}` -> 1st `nonSampledHooks` call (`idToTrace` retained!)
    tsp_nop.ingest_span(SpanEvent(901, 2, 1, is_error=False, randomness_56b=1))  # 2nd hook call
    tsp_nop.ingest_span(SpanEvent(901, 3, 1, is_error=False, randomness_56b=1))  # 3rd hook call
    assert late_error_dropped and tsp_nop.non_sampled_hook_calls == 3

    # 2. 56-bit W3C/OTel `Rejection Threshold` `T` precision reconciliation & `sample_on_first_match`
    raw_floor_001 = int((1.0 - 0.01) * float(MAX_ADJUSTED_COUNT))
    th14, tv14, _ = otel_prob_to_threshold(0.01, precision=14)
    th4, tv4, adj4 = otel_prob_to_threshold(0.01, precision=4)
    th5, tv5, adj5 = otel_prob_to_threshold(0.01, precision=5)
    assert f"{raw_floor_001:014x}" == "fd70a3d70a3d70"
    assert tv14 == "fd70a3d70a3d71" and tv4 == "fd70a" and tv5 == "fd70a4"

    # Nested completeness (`p1=0.01 => p2=0.05` via `R >= T`) & `sample_on_first_match` count bias
    th_p05, _, _ = otel_prob_to_threshold(0.05, precision=5)
    rng = random.Random(20261123)
    r_draws = [rng.randrange(0, MAX_ADJUSTED_COUNT) for _ in range(10_000)]
    kept_01 = [r for r in r_draws if r >= th5]
    nested_violations = sum(1 for r in kept_01 if r < th_p05)
    assert nested_violations == 0

    # `processor.go:935-952`: Policy 0 = `1%` probabilistic (`th:fd70a4`, weight `adj5 ~= 100.0`),
    # Policy 1 = `status_code=ERROR` (`th:0`, weight `1.0`). Over 100 error traces where 1 hits
    # the `1%` hash (`R >= th5`), `sample_on_first_match=True` breaks at Policy 0 and exports
    # `adj5` (~100.0) on that error trace instead of `min(T) = 0` (`1.0`), yielding `199.0`!
    first_match_est_errors = round(adj5 + 99 * 1.0, 2)
    min_threshold_est_errors = 100.0
    assert first_match_est_errors == 199.0

    # 3. `Composite` first-match starvation, `sharded_processor` integer division & multi-pod split
    comp_sampled_sps = [10, 0]  # SubPolicy 0 (`allocated=10`) full; SubPolicy 1 (`ERROR`, `allocated=50`) free
    comp_starved = not composite_evaluate_port(
        span_count=4,
        matches_sub=[True, True],
        allocated_sps=[10, 50],
        sampled_sps=comp_sampled_sps,
        max_total_sps=60,
    )
    assert comp_starved

    # `sharded_processor.go:52, 108, 157` with `num_shards = 8`:
    num_shards = 8
    exp_new_traces_per_shard = 4 // num_shards  # `L52`: raw floor -> `0`!
    rate_limit_agg_sps = divide_rate_port(2, num_shards) * num_shards  # `L157`: `max(1, 2//8)*8 = 8` (`4x`)!
    comp_max_per_shard = divide_rate_port(40, num_shards)  # `L108`: `40 // 8 = 5` SPS/shard
    comp_sub_alloc = int(comp_max_per_shard * 0.50)  # `50%` allocation = `2` SPS -> rejects 6-span trace at 0 QPS!
    sharded_comp_rejects_6span = not composite_evaluate_port(
        span_count=6,
        matches_sub=[True],
        allocated_sps=[comp_sub_alloc],
        sampled_sps=[0],
        max_total_sps=comp_max_per_shard,
    )
    assert exp_new_traces_per_shard == 0 and rate_limit_agg_sps == 8 and sharded_comp_rejects_6span

    # `[illustrative analytical model]`: `K = 8` unrouted round-robin collectors, `S = 6` spans/trace
    k_pods, s_spans = 8, 6
    fracture_prob = round(1.0 - (1.0 / k_pods) ** (s_spans - 1), 6)
    headless_leaf_err_prob = round(1.0 - (1.0 / k_pods), 4)
    sample_shard = splitmix64_trace_shard(bytes.fromhex("0102030405060708090a0b0c0d0e0f10"), 8)
    assert fracture_prob == 0.999969 and headless_leaf_err_prob == 0.875 and 0 <= sample_shard < 8

    print("=== PROBE 3: OTel Tail Sampling, 56-Bit TraceState & Sharding Hazards ===")
    print(
        f"  NumTraces=100 + idbatcher(num_batches=2): same_tick_dedup_orphans={same_tick_full_wait_orphans}/10 "
        f"(0 early, 0 spurious_drop), cross_tick_early_orphans={cross_tick_early_orphans}/25 "
        f"(spurious_sampled_drops={tsp.spurious_sampled_dropped_too_early}), "
        f"cascade_evictions={tsp.cascade_evictions}, dropped_too_early={tsp.dropped_too_early} "
        f"(vs canopy_5h_cache={tsp_canopy.dropped_too_early}), orphan_error_traces={orphan_error_traces}/50, "
        f"complete_error_traces={complete_error_traces}/50, late_post_decision_err_dropped={late_error_dropped}, "
        f"nop_cache_hooks={tsp_nop.non_sampled_hook_calls}"
    )
    print(
        f"  56-bit `th` at p=0.01: floor=0x{raw_floor_001:014x}, prec14='th:{tv14}', "
        f"prec4='th:{tv4}' (adj={adj4:.6f}), prec5='th:{tv5}' (adj={adj5:.6f}), "
        f"nested_violations={nested_violations}, first_match_err_est={first_match_est_errors} vs {min_threshold_est_errors}"
    )
    print(
        f"  Composite & sharded_processor (num_shards=8): sub0_starves_sub1_err={comp_starved}, "
        f"exp_traces_floor={exp_new_traces_per_shard}, rate2_agg_sps={rate_limit_agg_sps}, "
        f"sharded_composite_6span_rejected={sharded_comp_rejects_6span}"
    )
    print(
        f"  [illustrative analytical model] Unrouted K=8 collectors (S=6 spans): "
        f"trace_fracture_prob={fracture_prob}, headless_error_fragment_prob={headless_leaf_err_prob}"
    )


# ============================================================================
# PROBE 4: Sifter (SoCC '19) Pre-Sampling Unbiased Training vs. Sampled-Only Drift
# ============================================================================


class SifterSamplerPort:
    """Faithful stdlib port of `Las-Casas et al. (SoCC '19)` §§5.1-5.5 (`N=5, P=10, k=50, lr=0.01`)."""

    def __init__(
        self,
        vocab_size: int,
        path_len: int = 5,
        embed_dim: int = 10,
        window_k: int = 50,
        lr: float = 0.01,
        alpha: float = 0.01,
        seed: int = 42,
    ) -> None:
        self.vocab_size = vocab_size
        self.path_len = path_len
        self.ctx_len = path_len - 1
        self.embed_dim = embed_dim
        self.window_k = window_k
        self.lr = lr
        self.alpha = alpha
        rng = random.Random(seed)
        # Layer 1: `L` of shape `|Sigma| x P`; Layer 2: `U` of shape `((N-1)*P) x |Sigma|`
        self.embed = [
            [(rng.random() - 0.5) * 0.2 for _ in range(embed_dim)] for _ in range(vocab_size)
        ]
        self.proj = [
            [(rng.random() - 0.5) * 0.2 for _ in range(vocab_size)]
            for _ in range(self.ctx_len * embed_dim)
        ]
        self.loss_window: list[float] = []

    def forward_and_loss(
        self, paths: Sequence[tuple[int, ...]]
    ) -> tuple[float, list[tuple[list[int], int, list[float], list[float]]]]:
        mid = self.path_len // 2
        total_loss = 0.0
        cache: list[tuple[list[int], int, list[float], list[float]]] = []
        for path in paths:
            ctx = [path[i] for i in range(self.path_len) if i != mid]
            target = path[mid]
            hidden: list[float] = []
            for tok in ctx:
                hidden.extend(self.embed[tok])
            logits = [0.0] * self.vocab_size
            for h_idx, h_val in enumerate(hidden):
                row = self.proj[h_idx]
                for v in range(self.vocab_size):
                    logits[v] += h_val * row[v]
            m_log = max(logits)
            exps = [math.exp(x - m_log) for x in logits]
            s_exp = sum(exps)
            probs = [e / s_exp for e in exps]
            total_loss += -math.log(max(probs[target], 1e-12))
            cache.append((ctx, target, hidden, probs))
        return total_loss / len(paths), cache

    def backward_sgd(
        self, cache: Sequence[tuple[list[int], int, list[float], list[float]]]
    ) -> None:
        scale = self.lr / len(cache)
        for ctx, target, hidden, probs in cache:
            grad_logits = list(probs)
            grad_logits[target] -= 1.0
            grad_hidden = [0.0] * len(hidden)
            for h_idx, h_val in enumerate(hidden):
                row = self.proj[h_idx]
                gh = 0.0
                for v in range(self.vocab_size):
                    g = grad_logits[v]
                    gh += row[v] * g
                    row[v] -= scale * h_val * g
                grad_hidden[h_idx] = gh
            for c_pos, tok in enumerate(ctx):
                emb_row = self.embed[tok]
                base = c_pos * self.embed_dim
                for p in range(self.embed_dim):
                    emb_row[p] -= scale * grad_hidden[base + p]

    def observe(
        self, paths: Sequence[tuple[int, ...]], rng: random.Random, update_only_if_sampled: bool
    ) -> tuple[float, bool]:
        loss, cache = self.forward_and_loss(paths)
        # `Sifter §5.3`: sliding window of `k` prior losses + current trace loss (`k + 1` total)
        window_plus = self.loss_window + [loss]
        min_l = min(window_plus)
        weights = [x - min_l for x in window_plus]
        sum_w = sum(weights)
        if sum_w == 0.0:
            prob = self.alpha
        else:
            prob = min(1.0, (weights[-1] / sum_w) * len(window_plus) * self.alpha)
        sampled = rng.random() < prob

        # `Sifter §5.4-5.5`: true Sifter updates on EVERY trace seen (`update_only_if_sampled=False`)!
        if not update_only_if_sampled or sampled:
            self.backward_sgd(cache)
        self.loss_window.append(loss)
        if len(self.loss_window) > self.window_k:
            self.loss_window.pop(0)
        return prob, sampled


def run_probe_4() -> None:
    # `[illustrative analytical model]`: 1,200 streaming trace DAGs (`200` warmup + `1,000` eval)
    # at budget `alpha = 0.01` (`99.5%` variable-subpath read DAGs + `0.5%` [`5/1,000`] rare write
    # DAGs, mirroring `Sifter` Fig. 5's `5` writes per `1,000` reads with `lr=0.05` for 1,200-step
    # convergence; `Sifter §6` uses `lr=0.01` over `70,966` HDFS traces).
    rng_stream = random.Random(1337)
    read_pool = [
        (0, 1, 2, 3, 4),
        (1, 2, 3, 4, 5),
        (0, 1, 3, 4, 5),
        (1, 2, 4, 5, 0),
    ]
    stream: list[tuple[bool, list[tuple[int, ...]]]] = []
    for step in range(1_200):
        is_anom = (step >= 200) and (step % 200 == 100)
        if not is_anom:
            k_sub = rng_stream.choice([2, 3, 4])
            paths = rng_stream.sample(read_pool, k_sub)
        else:
            paths = [(0, 6, 7, 8, 9), (6, 7, 10, 11, 9)]
        stream.append((is_anom, paths))

    sifter_true = SifterSamplerPort(vocab_size=12, lr=0.05, alpha=0.01, seed=7)
    sifter_sampled_only = SifterSamplerPort(vocab_size=12, lr=0.05, alpha=0.01, seed=7)
    rng_a = random.Random(99)
    rng_b = random.Random(99)
    read_probs_true: list[float] = []
    anom_probs_true: list[float] = []
    read_probs_so: list[float] = []
    anom_probs_so: list[float] = []
    for step, (is_anom, paths) in enumerate(stream):
        p_t, _ = sifter_true.observe(paths, rng_a, update_only_if_sampled=False)
        p_s, _ = sifter_sampled_only.observe(paths, rng_b, update_only_if_sampled=True)
        if step >= 200:
            (anom_probs_true if is_anom else read_probs_true).append(p_t)
            (anom_probs_so if is_anom else read_probs_so).append(p_s)

    mean_read_p = round(sum(read_probs_true) / len(read_probs_true), 4)
    mean_anom_p = round(sum(anom_probs_true) / len(anom_probs_true), 4)
    enrichment_true = round(mean_anom_p / 0.01, 2)
    mean_read_so = round(sum(read_probs_so) / len(read_probs_so), 4)
    mean_anom_so = round(sum(anom_probs_so) / len(anom_probs_so), 4)
    enrichment_so = round(mean_anom_so / 0.01, 2)
    assert mean_anom_p > 0.40 and mean_read_p < 0.01 and enrichment_true > enrichment_so * 10

    print("=== PROBE 4: Sifter Pre-Sampling Path Model vs. Sampled-Only Feedback Drift ===")
    print(
        f"  [illustrative analytical model] Sifter pre-sampling SGD (alpha=0.01, N=5, P=10, k=50, lr=0.05): "
        f"mean_read_prob={mean_read_p}, mean_anomaly_prob={mean_anom_p} ({enrichment_true}x over uniform head)"
    )
    print(
        f"  [illustrative analytical model] §5.5 post-sampled-only SGD ablation: "
        f"mean_read_prob={mean_read_so}, mean_anomaly_prob={mean_anom_so} ({enrichment_so}x — "
        f"{round(enrichment_true / enrichment_so, 2)}x sensitivity collapse)"
    )


# ============================================================================
# PROBE 5: Prometheus MemPostings Churn & OTel 2,000 Overflow SLO Blindness
# ============================================================================

EXP_SLICE_GROWTH = 2  # `tsdb/index/postings.go:36`
ALL_POSTINGS_KEY = ("", "")  # `tsdb/index/postings.go:38`


class MemPostingsPort:
    """Faithful port of `prometheus/prometheus@06170caaea` `tsdb/index/postings.go`."""

    def __init__(self, ordered: bool = True) -> None:
        self.m: dict[str, dict[str, list[int]]] = {}
        self.lvs: dict[str, list[str]] = {}
        self.lvs_cap: dict[str, int] = {}
        self.ordered = ordered
        self.tail_repair_swaps = 0

    def _append_lvs(self, name: str, val: str) -> None:
        cur = self.lvs.setdefault(name, [])
        cap = self.lvs_cap.get(name, 0)
        if cap < len(cur) + 1:
            cap = len(cur) * EXP_SLICE_GROWTH + 1
            self.lvs_cap[name] = cap
        cur.append(val)

    def add(self, series_ref: int, labels: Sequence[tuple[str, str]]) -> None:
        # `postings.go:409-418`
        for k, v in labels:
            self._add_for(series_ref, k, v)
        self._add_for(series_ref, ALL_POSTINGS_KEY[0], ALL_POSTINGS_KEY[1])

    def _add_for(self, series_ref: int, name: str, value: str) -> None:
        # `postings.go:429-455` (note in-place tail bubble swap `#15317` at `L449-454`)
        nm = self.m.setdefault(name, {})
        if value not in nm:
            self._append_lvs(name, value)
            nm[value] = []
        lst = nm[value]
        lst.append(series_ref)
        if not self.ordered or len(lst) < 2 or lst[-1] >= lst[-2]:
            return
        for i in range(len(lst) - 1, 0, -1):
            if lst[i] >= lst[i - 1]:
                break
            lst[i], lst[i - 1] = lst[i - 1], lst[i]
            self.tail_repair_swaps += 1

    def total_postings_refs(self) -> int:
        return sum(len(lst) for nm in self.m.values() for lst in nm.values())

    def delete_gc(
        self, deleted: set[int], affected: set[tuple[str, str]]
    ) -> dict[str, int]:
        # `postings.go:314-391`
        affected_label_names: set[str] = set()
        copied_refs = 0
        scanned_refs = 0
        sleep_1ms_stalls = 0

        def process(name: str, value: str) -> None:
            nonlocal copied_refs, scanned_refs
            orig = self.m.get(name, {}).get(value, [])
            scanned_refs += len(orig)
            repl = [sid for sid in orig if sid not in deleted]
            copied_refs += len(repl)
            if repl:
                self.m[name][value] = repl
            else:
                self.m[name].pop(value, None)
                affected_label_names.add(name)

        for idx, (k, v) in enumerate(sorted(affected), 1):
            process(k, v)
            if idx % 512 == 0:
                sleep_1ms_stalls += 1
        process(ALL_POSTINGS_KEY[0], ALL_POSTINGS_KEY[1])

        for idx, name in enumerate(sorted(affected_label_names), 1):
            if idx % 512 == 0:
                sleep_1ms_stalls += 1
            if len(self.m.get(name, {})) == 0:
                self.m.pop(name, None)
                self.lvs.pop(name, None)
                self.lvs_cap.pop(name, None)
                continue
            # `postings.go:368`: `make([]string, 0, exponentialSliceGrowthFactor*len(p.m[name]))`
            rem = sorted(self.m[name].keys())
            self.lvs[name] = rem
            self.lvs_cap[name] = EXP_SLICE_GROWTH * len(rem)

        return {
            "scanned_refs": scanned_refs,
            "copied_refs": copied_refs,
            "sleep_1ms_stalls": sleep_1ms_stalls,
        }


class OTelMetricAggregatorPort:
    """Port of OTel Metrics SDK Cardinality Limits:
    - `mode='go_sdk'`: `opentelemetry-go@7b56b60e` active aggregators (`atomic.go:318`
      `lazyLimitedSyncMap`, `atomic.go:439` `limitedSyncMap`, `bound_sum.go:43`
      `boundLimitedSyncMap`, and `atomic.go:477-483` `LoadOrStoreAttrReclaiming`; plus
      standalone `limit.go:36` tested in `limit_test.go:14-42` `L38-41`), checking
      `m.len >= m.aggLimit - 1` to reserve 1 slot for `otel.metric.overflow=true`.
    - `mode='spec_exact'`: `opentelemetry-specification@c216b822` `sdk.md:939-941`
      (no overflow when distinct non-overflow attribute sets `<= limit`).
    - `temporality='cumulative'` (`sum.go:130, 192-195`): never clears `s.values` across
      collection cycles (permanent process-lifetime lockout once saturated), vs.
      `temporality='delta'` (`sum.go:58, 103`, `atomic.go:357-378`): resets per cycle."""

    OVERFLOW_ATTR = (("otel.metric.overflow", "true"),)

    def __init__(self, limit: int, mode: str, temporality: str = "cumulative") -> None:
        assert mode in ("go_sdk", "spec_exact")
        assert temporality in ("cumulative", "delta")
        self.limit = limit
        self.mode = mode
        self.temporality = temporality
        self.streams: Counter[tuple[tuple[str, str], ...]] = Counter()
        self.non_overflow_keys: set[tuple[tuple[str, str], ...]] = set()

    def record(self, attrs: tuple[tuple[str, str], ...], value: int = 1) -> None:
        if attrs in self.non_overflow_keys:
            self.streams[attrs] += value
            return
        max_non_overflow = (self.limit - 1) if self.mode == "go_sdk" else self.limit
        if len(self.non_overflow_keys) >= max_non_overflow:
            self.streams[self.OVERFLOW_ATTR] += value
        else:
            self.non_overflow_keys.add(attrs)
            self.streams[attrs] += value

    def collect_cycle(self) -> Counter[tuple[tuple[str, str], ...]]:
        snapshot = Counter(self.streams)
        if self.temporality == "delta":
            self.streams.clear()
            self.non_overflow_keys.clear()
        return snapshot


def run_probe_5() -> None:
    # 1. `[illustrative analytical model]`: Bounded (`5*3*4 = 60` series) vs. `conversation_id`
    # high-cardinality anti-pattern (`50,000` ephemeral series; `40,000` expire in 2h GC window)
    bounded = MemPostingsPort()
    sid = 1
    for r in range(5):
        for st in ("200", "429", "500"):
            for tool in ("search", "read", "edit", "test"):
                bounded.add(
                    sid,
                    [
                        ("__name__", "agent_rpc_total"),
                        ("service", "orchestrator"),
                        ("route", f"/v1/r{r}"),
                        ("status", st),
                        ("tool", tool),
                    ],
                )
                sid += 1
    bounded_refs = bounded.total_postings_refs()  # `60 * (5 + 1) = 360`

    churn = MemPostingsPort()
    deleted_ids: set[int] = set()
    affected_labels: set[tuple[str, str]] = set()
    for i in range(1, 50_001):
        # Out-of-order pair every 1,000th insert to trigger `addFor` tail swap (`#15317`)
        ref = (i + 1) if (i % 1000 == 1) else ((i - 1) if (i % 1000 == 2) else i)
        lbls = [
            ("__name__", "agent_rpc_total"),
            ("service", "orchestrator"),
            ("route", f"/v1/r{i % 5}"),
            ("status", "200"),
            ("conversation_id", f"conv-{i:06d}"),
        ]
        churn.add(ref, lbls)
        if i <= 40_000:
            deleted_ids.add(ref)
            affected_labels.update(lbls)

    churn_refs_before_gc = churn.total_postings_refs()  # `50,000 * 6 = 300,000`
    tail_swaps = churn.tail_repair_swaps
    gc_stats = churn.delete_gc(deleted_ids, affected_labels)
    conv_lvs_len = len(churn.lvs["conversation_id"])
    conv_lvs_cap = churn.lvs_cap["conversation_id"]
    # 50 out-of-order `SeriesRef` pairs swap across 4 shared postings lists (`__name__`,
    # `service`, `status`, `allPostingsKey`) -> `50 * 4 = 200` in-place tail swaps (`#15317`)!
    assert bounded_refs == 360 and churn_refs_before_gc == 300_000 and tail_swaps == 200
    assert conv_lvs_len == 10_000 and conv_lvs_cap == 20_000  # `2x` capacity (`postings.go:368`)!
    assert gc_stats["sleep_1ms_stalls"] == 78  # `40,008 // 512 = 78` explicit `1ms` sleep pauses!

    # 2. OTel Metrics SDK `limit=2000` spec-vs-`opentelemetry-go` discrepancy & SLO blindness
    go_2000 = OTelMetricAggregatorPort(limit=2000, mode="go_sdk", temporality="cumulative")
    go_delta = OTelMetricAggregatorPort(limit=2000, mode="go_sdk", temporality="delta")
    spec_2000 = OTelMetricAggregatorPort(limit=2000, mode="spec_exact", temporality="cumulative")
    for i in range(2_000):
        attrs = (("route", "/chat"), ("status", "200"), ("conversation_id", f"c-{i}"))
        go_2000.record(attrs)
        go_delta.record(attrs)
        spec_2000.record(attrs)
    go_overflow_at_2000 = OTelMetricAggregatorPort.OVERFLOW_ATTR in go_2000.streams
    spec_overflow_at_2000 = OTelMetricAggregatorPort.OVERFLOW_ATTR in spec_2000.streams

    go_limit1 = OTelMetricAggregatorPort(limit=1, mode="go_sdk")
    go_limit1.record((("status", "200"),))
    go_limit1_immediate_overflow = (
        len(go_limit1.non_overflow_keys) == 0
        and go_limit1.streams[OTelMetricAggregatorPort.OVERFLOW_ATTR] == 1
    )
    assert go_overflow_at_2000 and not spec_overflow_at_2000 and go_limit1_immediate_overflow

    # `[illustrative analytical model]`: Cycle 1 — after `2,000` benign `status="200"` sessions
    # fill the cap, `500` consecutive `status="500"` outage requests arrive on new IDs:
    for j in range(500):
        err_attrs = (("route", "/chat"), ("status", "500"), ("conversation_id", f"outage-{j}"))
        go_2000.record(err_attrs)
        go_delta.record(err_attrs)
        spec_2000.record(err_attrs)

    total_unfiltered = sum(go_2000.streams.values())
    observed_500_go = sum(
        cnt for k, cnt in go_2000.streams.items() if ("status", "500") in k
    )
    observed_500_spec = sum(
        cnt for k, cnt in spec_2000.streams.items() if ("status", "500") in k
    )
    overflow_count_go = go_2000.streams[OTelMetricAggregatorPort.OVERFLOW_ATTR]
    overflow_count_spec = spec_2000.streams[OTelMetricAggregatorPort.OVERFLOW_ATTR]
    assert total_unfiltered == 2_500 and observed_500_go == 0 and observed_500_spec == 0
    assert overflow_count_go == 501 and overflow_count_spec == 500

    # End of Cycle 1 -> Cycle 2 (`100` low-cardinality `status="500"` requests after churn stops):
    go_2000.collect_cycle()
    go_delta.collect_cycle()
    for j in range(100):
        rec_attrs = (("route", "/chat"), ("status", "500"), ("conversation_id", f"c2-err-{j}"))
        go_2000.record(rec_attrs)
        go_delta.record(rec_attrs)
    cycle2_500_cum = sum(cnt for k, cnt in go_2000.streams.items() if ("status", "500") in k)
    cycle2_500_delta = sum(cnt for k, cnt in go_delta.streams.items() if ("status", "500") in k)
    assert cycle2_500_cum == 0 and cycle2_500_delta == 100

    print("=== PROBE 5: Prometheus MemPostings Churn & OTel 2,000 Overflow SLO Blindness ===")
    print(
        f"  [illustrative analytical model] MemPostings (60 bounded vs 50,000 churned series): "
        f"refs={bounded_refs} vs {churn_refs_before_gc} ({churn_refs_before_gc/bounded_refs:.1f}x), "
        f"ooo_tail_swaps={tail_swaps}, gc_scanned_refs={gc_stats['scanned_refs']}, "
        f"gc_1ms_stalls={gc_stats['sleep_1ms_stalls']}, remaining_lvs=(len={conv_lvs_len}, cap={conv_lvs_cap})"
    )
    print(
        f"  OTel CardinalityLimit=2000 spec-vs-Go-SDK: go_sdk_overflows_on_2000th={go_overflow_at_2000} "
        f"(kept=1999), spec_overflows_on_2000th={spec_overflow_at_2000} (kept=2000), "
        f"go_sdk_limit1_zero_kept={go_limit1_immediate_overflow}"
    )
    print(
        f"  [illustrative analytical model] Post-cap 500-request HTTP 500 outage (total={total_unfiltered}, "
        f"true_err_rate=20.0%): observed_status500_go={observed_500_go} (0.0%), "
        f"observed_status500_spec={observed_500_spec} (0.0%), "
        f"overflow_series=(go={overflow_count_go}, spec={overflow_count_spec}), "
        f"cycle2_post_churn_status500=(cumulative={cycle2_500_cum}, delta={cycle2_500_delta})"
    )


def main() -> None:
    with tempfile.TemporaryDirectory() as td:
        tmp_root = Path(td)
        run_probe_1(tmp_root)
        run_probe_2()
        run_probe_3()
        run_probe_4()
        run_probe_5()
        print("ALL 5 TELEMETRY VERIFICATION PROBES PASSED DETERMINISTICALLY.")


if __name__ == "__main__":
    main()
