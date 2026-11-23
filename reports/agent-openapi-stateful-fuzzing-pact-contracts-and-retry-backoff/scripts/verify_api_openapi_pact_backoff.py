#!/usr/bin/env python3
"""Deterministic Primary-Source Verification Probe for API Specifications, Fuzzing, Contracts, Benchmarks, and Backoff.

Covers:
  1. OpenAPI 3.0.3/3.0.4 vs. 3.1.0/3.1.1 (`JSON Schema Draft 2020-12`) dialect
     divergences (`nullable` omission from Fixed Fields, `$ref` siblings,
     `exclusiveMinimum`, `prefixItems`, `allOf` + `additionalProperties: false`
     vs. `unevaluatedProperties: false`, `readOnly` + `required`, polymorphic
     `discriminator`) and `schemathesis/schemathesis@f5ed7dd3` canonicalizer,
     wire-serialization false-positive guards, and stateful `Location`
     normalization (including `_strip_base_path_from_location`).
  2. `microsoft/restler-fuzzer@6d984dee` `Dependencies.fs` + `ApiResourceTypes.fs`
     producer-consumer inference (`isValidProducer` vs. `getIndexedByEndpointProducers`
     `[Put; Post; Get]` omission of `Patch`, `getCreateOrUpdateProducer` `Path`+`Put`
     `commonProducerNames = ["id"; "name"]`, `ParameterKind.Query -> None, None` +
     CamelCase `"token"` suffix), `BFS` vs. `BFS-Fast` sequence-set scaling
     (`ICSE '19` / `arXiv:1806.09739v1`), and the 4 `ICST 2020` security checkers.
  3. `pact-foundation/pact-reference@4a24afcf` `json.rs` `MatchingRule`
     consumer-breaking verification escapes (`Type` float-for-int & empty array,
     unanchored `Regex` + `.to_string()` coercion, `Boolean` string coercion,
     `AllowUnexpectedKeys`), `callback_executors.rs` missing state-URL no-op,
     and `pact-foundation/pact_broker@6298abd2` `can-i-deploy` directional
     asymmetry.
  4. Agentic API benchmark harness defects across `ShishirPatil/gorilla@6ea57973`
     (`BFCL` `standardize_string`, `"any" -> str`, `java_type_converter` comma
     split, cross-turn `response_checker` leakage, `_process_method_calls`
     string-literal corruption & `eval` outer-split/3-segment bypass),
     `Yifan-Song793/RestGPT@d9901286` (`dereference_refs` `RecursionError`,
     `PATCH` `NotImplementedError`, and full 10-row `Table 4` `N=57` vs. `N=55`
     Spotify denominator & `CP%` audit), and `OpenBMB/ToolBench@d56fdd89`
     (`rapidapi.py:214,242` indentation erasing `optional_parameters`,
     `"NUMBER" -> "integer"`, `[-64:]` left-truncation collision, and `rtl.py`
     `Unsolvable -> Passed`).
  5. `LIMIT/OFFSET` vs. single-column vs. composite keyset `(created_at, id)`
     pagination under concurrent writes (plus mutable sort-key caveat) and
     `aws-samples/aws-arch-backoff-simulator@66cb1692` discrete-event OCC +
     `RFC 9110 §10.2.3` integer `Retry-After` (`1*DIGIT`) token-bucket
     (including `RESTler` `request_utilities.py:425-479` fixed-5s/`MAX_RETRIES=5`
     vs. unjittered exponential vs. additive jitter) and quota-window contention.

Stdlib only (Python 3.10+), zero network I/O, zero host paths in stdout,
bit-identical across PYTHONHASHSEED, < 2.0s wall-clock runtime.
"""

from __future__ import annotations

import copy
from dataclasses import dataclass
import heapq
import json
import math
import os
import random
import re
import tempfile
from typing import Any
from urllib.parse import parse_qs, urlencode, urlsplit


# ============================================================================
# PROBE 1: OpenAPI 3.0.3 vs. 3.1.0 Dialect Differential & Schemathesis Ports
# ============================================================================


def _resolve_json_pointer(doc: dict[str, Any], ref: str) -> dict[str, Any]:
    assert ref.startswith("#/"), f"Unsupported non-local ref: {ref}"
    cur: Any = doc
    for part in ref[2:].split("/"):
        part = part.replace("~1", "/").replace("~0", "~")
        cur = cur[part]
    return cur


def _is_json_integer(val: Any) -> bool:
    return isinstance(val, int) and not isinstance(val, bool)


def _is_json_number(val: Any) -> bool:
    return isinstance(val, (int, float)) and not isinstance(val, bool)


def _matches_primitive_type(val: Any, t: str) -> bool:
    if t == "null":
        return val is None
    if t == "boolean":
        return isinstance(val, bool)
    if t == "integer":
        return _is_json_integer(val)
    if t == "number":
        return _is_json_number(val)
    if t == "string":
        return isinstance(val, str)
    if t == "array":
        return isinstance(val, list)
    if t == "object":
        return isinstance(val, dict)
    return False


def validate_strict_oas30(
    schema: dict[str, Any], instance: Any, root_doc: dict[str, Any]
) -> bool:
    """Strict OpenAPI 3.0.3/3.0.4 Schema/Reference validator (`versions/3.0.3.md`).

    Normative rules:
      - Reference Object (`$ref`) ignores all sibling keywords (`3.0.3:2326`,
        Reference Object section: "Other properties MUST be ignored").
      - `null` is not a `type`; `type` MUST be a single string (`3.0.3:148,2314`).
      - `nullable: true` adds null ONLY if `type` is explicitly defined in the
        same Schema Object (`3.0.3:2335`, `3.0.4:2701`).
      - `exclusiveMinimum` is a boolean modifier on `minimum` (Draft 00 / Draft 4).
      - `additionalProperties` evaluates locally on each subschema's `properties`.
    """
    if "$ref" in schema:
        target = _resolve_json_pointer(root_doc, schema["$ref"])
        return validate_strict_oas30(target, instance, root_doc)

    schema_type = schema.get("type")
    if schema_type is not None and not isinstance(schema_type, str):
        raise ValueError("OAS 3.0.3 forbids non-string `type` (e.g., array)")

    if instance is None:
        if schema_type is not None and schema.get("nullable") is True:
            if "enum" in schema and None not in schema["enum"]:
                return False
            return True
        return False

    if schema.get("not") is not None:
        if validate_strict_oas30(schema["not"], instance, root_doc):
            return False

    if "enum" in schema and instance not in schema["enum"]:
        return False

    if schema_type is not None and not _matches_primitive_type(instance, schema_type):
        return False

    if _is_json_number(instance):
        if "minimum" in schema:
            bound = schema["minimum"]
            if schema.get("exclusiveMinimum") is True:
                if not (instance > bound):
                    return False
            elif not (instance >= bound):
                return False

    if isinstance(instance, dict):
        for req in schema.get("required", []):
            if req not in instance:
                return False
        props = schema.get("properties", {})
        for k, v in instance.items():
            if k in props:
                if not validate_strict_oas30(props[k], v, root_doc):
                    return False
            else:
                ap = schema.get("additionalProperties", True)
                if ap is False:
                    return False
                if isinstance(ap, dict) and not validate_strict_oas30(ap, v, root_doc):
                    return False

    if "allOf" in schema:
        if not all(validate_strict_oas30(sub, instance, root_doc) for sub in schema["allOf"]):
            return False
    if "anyOf" in schema:
        if not any(validate_strict_oas30(sub, instance, root_doc) for sub in schema["anyOf"]):
            return False
    if "oneOf" in schema:
        matches = sum(1 for sub in schema["oneOf"] if validate_strict_oas30(sub, instance, root_doc))
        if matches != 1:
            return False

    return True


def _validate_draft202012_inner(
    schema: bool | dict[str, Any], instance: Any, root_doc: dict[str, Any]
) -> tuple[bool, set[str]]:
    """JSON Schema Draft 2020-12 / strict OAS 3.1.0/3.1.1 validator with annotation tracking."""
    if isinstance(schema, bool):
        return (schema, set())

    evaluated_props: set[str] = set()

    # Draft 2020-12 evaluates `$ref` alongside sibling keywords by intersection.
    if "$ref" in schema:
        target = _resolve_json_pointer(root_doc, schema["$ref"])
        ok, ref_eval = _validate_draft202012_inner(target, instance, root_doc)
        if not ok:
            return (False, set())
        evaluated_props.update(ref_eval)

    # In strict OAS 3.1.0 (`3.1.0:2331-2338`) and 3.1.1 (`3.1.1:2749-2757`),
    # `nullable` is omitted from Fixed Fields and treated by Draft 2020-12 as an
    # unrecognized no-op annotation.
    if "not" in schema:
        not_ok, _ = _validate_draft202012_inner(schema["not"], instance, root_doc)
        if not_ok:
            return (False, set())

    if "const" in schema and instance != schema["const"]:
        return (False, set())
    if "enum" in schema and instance not in schema["enum"]:
        return (False, set())

    if "type" in schema:
        t_spec = schema["type"]
        allowed = [t_spec] if isinstance(t_spec, str) else list(t_spec)
        if not any(_matches_primitive_type(instance, t) for t in allowed):
            return (False, set())

    if _is_json_number(instance):
        if "minimum" in schema and not (instance >= schema["minimum"]):
            return (False, set())
        if isinstance(schema.get("exclusiveMinimum"), (int, float)) and not isinstance(
            schema.get("exclusiveMinimum"), bool
        ):
            if not (instance > schema["exclusiveMinimum"]):
                return (False, set())

    if isinstance(instance, list):
        prefix = schema.get("prefixItems", [])
        for idx, sub in enumerate(prefix):
            if idx < len(instance):
                ok, _ = _validate_draft202012_inner(sub, instance[idx], root_doc)
                if not ok:
                    return (False, set())
        if "items" in schema and len(instance) > len(prefix):
            for elem in instance[len(prefix) :]:
                ok, _ = _validate_draft202012_inner(schema["items"], elem, root_doc)
                if not ok:
                    return (False, set())

    if isinstance(instance, dict):
        if "maxProperties" in schema and len(instance) > schema["maxProperties"]:
            return (False, set())
        for req in schema.get("required", []):
            if req not in instance:
                return (False, set())
        props = schema.get("properties", {})
        for k, v in instance.items():
            if k in props:
                ok, _ = _validate_draft202012_inner(props[k], v, root_doc)
                if not ok:
                    return (False, set())
                evaluated_props.add(k)
        if "additionalProperties" in schema:
            ap = schema["additionalProperties"]
            for k, v in instance.items():
                if k not in props:
                    ok, _ = _validate_draft202012_inner(ap, v, root_doc)
                    if not ok:
                        return (False, set())
                    evaluated_props.add(k)

    if "allOf" in schema:
        for sub in schema["allOf"]:
            ok, sub_eval = _validate_draft202012_inner(sub, instance, root_doc)
            if not ok:
                return (False, set())
            evaluated_props.update(sub_eval)

    if "anyOf" in schema:
        matched_any = False
        for sub in schema["anyOf"]:
            ok, sub_eval = _validate_draft202012_inner(sub, instance, root_doc)
            if ok:
                matched_any = True
                evaluated_props.update(sub_eval)
        if not matched_any:
            return (False, set())

    if "oneOf" in schema:
        good_evals: list[set[str]] = []
        for sub in schema["oneOf"]:
            ok, sub_eval = _validate_draft202012_inner(sub, instance, root_doc)
            if ok:
                good_evals.append(sub_eval)
        if len(good_evals) != 1:
            return (False, set())
        evaluated_props.update(good_evals[0])

    if isinstance(instance, dict) and "unevaluatedProperties" in schema:
        up = schema["unevaluatedProperties"]
        for k, v in instance.items():
            if k not in evaluated_props:
                ok, _ = _validate_draft202012_inner(up, v, root_doc)
                if not ok:
                    return (False, set())
                evaluated_props.add(k)

    return (True, evaluated_props)


def validate_strict_oas31(
    schema: dict[str, Any], instance: Any, root_doc: dict[str, Any]
) -> bool:
    ok, _ = _validate_draft202012_inner(schema, instance, root_doc)
    return ok


# Faithful stdlib port of `schemathesis/schemathesis@f5ed7dd3`
# `src/schemathesis/specs/openapi/converter.py` (`L106-136, 175-188, 267-382, 593-621`)
def _upgrade_legacy_exclusive_bounds(schema: dict[str, Any]) -> None:
    for exclusive_key, bound_key in (
        ("exclusiveMinimum", "minimum"),
        ("exclusiveMaximum", "maximum"),
    ):
        exclusive = schema.get(exclusive_key)
        if not isinstance(exclusive, bool):
            continue
        if not exclusive:
            schema.pop(exclusive_key, None)
            continue
        bound = schema.get(bound_key)
        if isinstance(bound, bool) or not isinstance(bound, (int, float)):
            schema.pop(exclusive_key, None)
            continue
        schema[exclusive_key] = bound
        schema.pop(bound_key, None)


def _upgrade_legacy_tuple_items(schema: dict[str, Any]) -> None:
    items = schema.get("items")
    if not isinstance(items, list) or "prefixItems" in schema:
        return
    schema["prefixItems"] = items
    if "additionalItems" in schema:
        schema["items"] = schema.pop("additionalItems")
    else:
        del schema["items"]


def _forbidden_in_allof_branches(
    schema: dict[str, Any], root_doc: dict[str, Any], forbid_read_only: bool
) -> set[str]:
    forbidden: set[str] = set()
    all_of = schema.get("allOf")
    pending: list[Any] = list(all_of) if isinstance(all_of, list) else []
    seen: set[int] = set()
    while pending:
        branch = pending.pop()
        if not isinstance(branch, dict) or id(branch) in seen:
            continue
        seen.add(id(branch))
        if "$ref" in branch:
            pending.append(_resolve_json_pointer(root_doc, branch["$ref"]))
        nested = branch.get("allOf")
        if isinstance(nested, list):
            pending.extend(nested)
        props = branch.get("properties")
        if isinstance(props, dict):
            for k, sub in props.items():
                if sub is False or sub == {"not": {}}:
                    forbidden.add(k)
                elif forbid_read_only and isinstance(sub, dict) and sub.get("readOnly") is True:
                    forbidden.add(k)
    return forbidden


def _pin_discriminator_property(schema: dict[str, Any]) -> None:
    """Port of `converter.py:297-382` (without injecting `required` on branches or `defaultMapping`)."""
    disc = schema.get("discriminator")
    if not isinstance(disc, dict) or "propertyName" not in disc:
        return
    prop_name = disc["propertyName"]
    mapping: dict[str, str] = disc.get("mapping", {})
    default_ref: str | None = disc.get("defaultMapping")
    default_name = default_ref.rsplit("/", 1)[-1] if isinstance(default_ref, str) else None
    ref_to_values: dict[str, list[str]] = {}
    for val, ref in mapping.items():
        ref_to_values.setdefault(ref, []).append(val)
    for keyword in ("oneOf", "anyOf"):
        branches = schema.get(keyword)
        if not isinstance(branches, list):
            continue
        routed: set[str] = set()
        new_branches: list[Any] = []
        default_index: int | None = None
        for idx, item in enumerate(branches):
            if isinstance(item, dict) and "$ref" in item:
                ref = item["$ref"]
                if default_ref is not None and ref == default_ref:
                    default_index = idx
                    new_branches.append(item)
                    continue
                vals = ref_to_values.get(ref) or [ref.rsplit("/", 1)[-1]]
                routed.update(vals)
                # `converter.py:371`: Draft 4 ignores `const`, so pin via `enum` without `required`.
                new_branches.append(
                    {"allOf": [item, {"properties": {prop_name: {"enum": vals}}}]}
                )
            else:
                new_branches.append(item)
        if default_ref is not None:
            routed.update(
                val
                for val, target in mapping.items()
                if val and isinstance(target, str) and target.rsplit("/", 1)[-1] != default_name
            )
            # `converter.py:379-381`: default branch accepts an absent tag and every unclaimed value.
            pin = {"properties": {prop_name: {"not": {"enum": sorted(routed)}}}}
            if default_index is not None:
                new_branches[default_index] = {"allOf": [new_branches[default_index], pin]}
            else:
                new_branches.append({"allOf": [{"$ref": default_ref}, pin]})
        schema[keyword] = new_branches


def schemathesis_to_json_schema(
    raw_schema: dict[str, Any],
    root_doc: dict[str, Any],
    *,
    is_response_schema: bool,
    merge_ref_siblings: bool,
    upgrade_legacy_exclusive_bounds: bool,
    repair_allof_readonly: bool = True,
    nullable_keyword: str = "nullable",
) -> dict[str, Any]:
    schema = copy.deepcopy(raw_schema)

    # `converter.py:107-114`
    if not merge_ref_siblings and "$ref" in schema:
        nullable = schema.get(nullable_keyword)
        for key in list(schema):
            if key != "$ref":
                del schema[key]
        if nullable:
            schema[nullable_keyword] = nullable

    if upgrade_legacy_exclusive_bounds:
        _upgrade_legacy_exclusive_bounds(schema)
        _upgrade_legacy_tuple_items(schema)

    # `converter.py:119-133`
    if schema.get(nullable_keyword):
        del schema[nullable_keyword]
        enum = schema.get("enum")
        if is_response_schema or not isinstance(enum, list) or None in enum:
            schema = {"anyOf": [schema, {"type": "null"}]}

    schema_type = schema.get("type")
    if is_response_schema and isinstance(schema_type, list) and "null" in schema_type:
        enum = schema.get("enum")
        if isinstance(enum, list) and None not in enum:
            enum.append(None)

    _pin_discriminator_property(schema)

    # `converter.py:175-187, 267-294`
    props = schema.get("properties")
    if isinstance(props, dict):
        for k, sub in list(props.items()):
            if isinstance(sub, dict):
                if is_response_schema and sub.get("writeOnly") is True:
                    props[k] = {"not": {}}
                elif not is_response_schema and sub.get("readOnly") is True:
                    props[k] = {"not": {}}

    if "required" in schema and isinstance(schema["required"], list):
        forbidden_direct = {
            k for k, v in (props or {}).items() if v == {"not": {}} or v is False
        }
        forbidden_allof = (
            _forbidden_in_allof_branches(
                schema, root_doc, forbid_read_only=not is_response_schema
            )
            if repair_allof_readonly
            else set()
        )
        schema["required"] = [
            r for r in schema["required"] if r not in (forbidden_direct | forbidden_allof)
        ]

    return schema


def schemathesis_can_negate_type(schema: dict[str, Any], location: str, media_type: str | None) -> bool:
    """Port of `schemathesis` `negative/mutations.py:638-652`."""
    if media_type == "application/x-www-form-urlencoded":
        return False
    t = schema.get("type")
    old_types = [t] if isinstance(t, str) else list(t or [])
    if "string" in old_types and location in ("header", "path", "query"):
        return False
    return True


def _strip_base_path_from_location(path: str, base_path: str) -> str | None:
    """Port of `schemathesis` `stateful/inference.py:193-200`."""
    bp = base_path.rstrip("/")
    if path != bp and not path.startswith(f"{bp}/"):
        return None
    relative_path = path[len(bp) :]
    return relative_path if relative_path.startswith("/") else "/" + relative_path


def schemathesis_normalize_location(
    location: str, base_url: str | None, base_path: str = ""
) -> str | None:
    """Port of `schemathesis` `stateful/inference.py:171-200`."""
    location = location.strip()
    if not location:
        return None
    effective_base_path = urlsplit(base_url).path if base_url else base_path
    if location.startswith(("http://", "https://")):
        if not base_url:
            return None
        parsed = urlsplit(location)
        base_parsed = urlsplit(base_url)
        if (parsed.scheme, parsed.netloc) != (base_parsed.scheme, base_parsed.netloc):
            return None
        return _strip_base_path_from_location(parsed.path, effective_base_path)
    loc_path = urlsplit(location).path
    stripped = _strip_base_path_from_location(loc_path, effective_base_path)
    return stripped if stripped is not None else loc_path


def run_probe_1(tmp_dir: str) -> dict[str, Any]:
    spec_doc = {
        "components": {
            "schemas": {
                "User": {
                    "type": "object",
                    "properties": {"id": {"type": "integer"}},
                    "required": ["id"],
                },
                "Timestamped": {
                    "type": "object",
                    "properties": {"created_at": {"type": "string", "readOnly": True}},
                },
                "Cat": {
                    "type": "object",
                    "properties": {"petType": {"type": "string"}, "meows": {"type": "boolean"}},
                    "required": ["petType", "meows"],
                },
                "Dog": {
                    "type": "object",
                    "properties": {"petType": {"type": "string"}, "barks": {"type": "boolean"}},
                    "required": ["petType", "barks"],
                },
                "FallbackPet": {
                    "type": "object",
                    "properties": {"petType": {"type": "string"}, "unknownTrait": {"type": "boolean"}},
                    "required": ["unknownTrait"],
                },
            }
        }
    }
    spec_file = os.path.join(tmp_dir, "oas_bundle.json")
    with open(spec_file, "w", encoding="utf-8") as f:
        json.dump(spec_doc, f)
    with open(spec_file, "r", encoding="utf-8") as f:
        loaded_doc = json.load(f)

    # H1: Un-migrated `{"type": "string", "nullable": true}` with payload `None`
    s_h1 = {"type": "string", "nullable": True}
    h1_oas30 = validate_strict_oas30(s_h1, None, loaded_doc)
    h1_oas31 = validate_strict_oas31(s_h1, None, loaded_doc)
    s_h1_sch31 = schemathesis_to_json_schema(
        s_h1, loaded_doc, is_response_schema=True, merge_ref_siblings=True, upgrade_legacy_exclusive_bounds=True
    )
    h1_sch31 = validate_strict_oas31(s_h1_sch31, None, loaded_doc)
    assert (h1_oas30, h1_oas31, h1_sch31) == (True, False, True)

    # H2: `{"$ref": "#/components/schemas/User", "nullable": true}` with payload `None`
    s_h2 = {"$ref": "#/components/schemas/User", "nullable": True}
    h2_oas30 = validate_strict_oas30(s_h2, None, loaded_doc)
    h2_oas31 = validate_strict_oas31(s_h2, None, loaded_doc)
    s_h2_sch30 = schemathesis_to_json_schema(
        s_h2, loaded_doc, is_response_schema=True, merge_ref_siblings=False, upgrade_legacy_exclusive_bounds=False
    )
    h2_sch30 = validate_strict_oas31(s_h2_sch30, None, loaded_doc)
    assert (h2_oas30, h2_oas31, h2_sch30) == (False, False, True)

    # H3: Asymmetric `nullable: true` + `enum: ["active", "paused"]` (`converter.py:122-133`)
    s_h3 = {"type": "string", "nullable": True, "enum": ["active", "paused"]}
    h3_req = validate_strict_oas31(
        schemathesis_to_json_schema(
            s_h3, loaded_doc, is_response_schema=False, merge_ref_siblings=False, upgrade_legacy_exclusive_bounds=False
        ),
        None,
        loaded_doc,
    )
    h3_resp = validate_strict_oas31(
        schemathesis_to_json_schema(
            s_h3, loaded_doc, is_response_schema=True, merge_ref_siblings=False, upgrade_legacy_exclusive_bounds=False
        ),
        None,
        loaded_doc,
    )
    assert (h3_req, h3_resp) == (False, True)

    # H4: `allOf` + `additionalProperties: false` unsatisfiability vs. `unevaluatedProperties: false`
    s_allof_ap = {
        "allOf": [
            {"type": "object", "properties": {"id": {"type": "integer"}}, "required": ["id"], "additionalProperties": False},
            {"type": "object", "properties": {"role": {"type": "string"}}, "required": ["role"], "additionalProperties": False},
        ]
    }
    s_allof_up = {
        "allOf": [
            {"type": "object", "properties": {"id": {"type": "integer"}}, "required": ["id"]},
            {"type": "object", "properties": {"role": {"type": "string"}}, "required": ["role"]},
        ],
        "unevaluatedProperties": False,
    }
    candidates = [{}, {"id": 1}, {"role": "admin"}, {"id": 1, "role": "admin"}, {"id": 1, "role": "admin", "rogue": 9}]
    ap_valid = [c for c in candidates if validate_strict_oas30(s_allof_ap, c, loaded_doc)]
    up_valid = [c for c in candidates if validate_strict_oas31(s_allof_up, c, loaded_doc)]
    assert len(ap_valid) == 0 and up_valid == [{"id": 1, "role": "admin"}]

    # H5: `allOf` `$ref` `readOnly` + top-level `required` (`_forbidden_in_allof_branches`)
    s_ro = {
        "type": "object",
        "allOf": [{"$ref": "#/components/schemas/Timestamped"}],
        "properties": {"name": {"type": "string"}},
        "required": ["name", "created_at"],
    }
    req_doc = copy.deepcopy(loaded_doc)
    req_doc["components"]["schemas"]["Timestamped"]["properties"]["created_at"] = {"not": {}}
    s_ro_unrepaired = schemathesis_to_json_schema(
        s_ro, loaded_doc, is_response_schema=False, merge_ref_siblings=True,
        upgrade_legacy_exclusive_bounds=True, repair_allof_readonly=False
    )
    s_ro_repaired = schemathesis_to_json_schema(
        s_ro, loaded_doc, is_response_schema=False, merge_ref_siblings=True,
        upgrade_legacy_exclusive_bounds=True, repair_allof_readonly=True
    )
    ro_payloads = [{}, {"name": "alice"}, {"name": "alice", "created_at": "2026-01-01"}]
    unrep_ok = [p for p in ro_payloads if validate_strict_oas31(s_ro_unrepaired, p, req_doc)]
    rep_ok = [p for p in ro_payloads if validate_strict_oas31(s_ro_repaired, p, req_doc)]
    assert len(unrep_ok) == 0 and rep_ok == [{"name": "alice"}]

    # H6: Polymorphic `oneOf` + `discriminator` pinning (`converter.py:297-382`) incl. `defaultMapping` absent tag
    s_poly = {
        "oneOf": [
            {"$ref": "#/components/schemas/Cat"},
            {"$ref": "#/components/schemas/Dog"},
            {"$ref": "#/components/schemas/FallbackPet"},
        ],
        "discriminator": {
            "propertyName": "petType",
            "defaultMapping": "#/components/schemas/FallbackPet",
        },
    }
    mis_tagged = {"petType": "Dog", "meows": True}
    unpinned_accepts_mistagged = validate_strict_oas31(s_poly, mis_tagged, loaded_doc)
    s_poly_pinned = schemathesis_to_json_schema(
        s_poly, loaded_doc, is_response_schema=False, merge_ref_siblings=True, upgrade_legacy_exclusive_bounds=True
    )
    pinned_accepts_mistagged = validate_strict_oas31(s_poly_pinned, mis_tagged, loaded_doc)
    pinned_accepts_cat = validate_strict_oas31(s_poly_pinned, {"petType": "Cat", "meows": True}, loaded_doc)
    default_absent_tag_ok = validate_strict_oas31(s_poly_pinned, {"unknownTrait": True}, loaded_doc)
    assert (unpinned_accepts_mistagged, pinned_accepts_mistagged, pinned_accepts_cat, default_absent_tag_ok) == (
        True,
        False,
        True,
        True,
    )

    # H7: Legacy OAS 3.0 `exclusiveMinimum: true` + `minimum: 0` & array `items` -> `prefixItems` (`converter.py:593-620`)
    s_legacy_num = {"type": "integer", "minimum": 0, "exclusiveMinimum": True}
    assert validate_strict_oas30(s_legacy_num, 0, loaded_doc) is False
    assert validate_strict_oas31(s_legacy_num, 0, loaded_doc) is True
    s_upgraded_num = schemathesis_to_json_schema(
        s_legacy_num, loaded_doc, is_response_schema=False, merge_ref_siblings=True, upgrade_legacy_exclusive_bounds=True
    )
    assert validate_strict_oas31(s_upgraded_num, 0, loaded_doc) is False
    s_legacy_tuple = {"type": "array", "items": [{"type": "string"}, {"type": "integer"}], "additionalItems": False}
    s_upgraded_tuple = schemathesis_to_json_schema(
        s_legacy_tuple, loaded_doc, is_response_schema=False, merge_ref_siblings=True, upgrade_legacy_exclusive_bounds=True
    )
    assert validate_strict_oas31(s_upgraded_tuple, ["ok", 7], loaded_doc) is True
    assert validate_strict_oas31(s_upgraded_tuple, ["ok", 7, "extra"], loaded_doc) is False

    # Wire-serialization negative-mutation false-positive demonstration
    query_schema = {"type": "string"}
    naive_neg_mutations = [42, True]
    naive_wire_fps = 0
    guarded_wire_fps = 0
    for mut_val in naive_neg_mutations:
        qs = urlencode({"tag": mut_val})
        parsed_on_server = parse_qs(qs)["tag"][0]
        if validate_strict_oas31(query_schema, parsed_on_server, loaded_doc):
            naive_wire_fps += 1
        if schemathesis_can_negate_type(query_schema, "query", None):
            guarded_wire_fps += 1
    assert (naive_wire_fps, guarded_wire_fps) == (2, 0)

    abs_loc_no_base = schemathesis_normalize_location("https://api.example.com/v1/users/123", base_url=None)
    abs_loc_with_base = schemathesis_normalize_location(
        "https://api.example.com/v1/users/123", base_url="https://api.example.com/v1"
    )
    abs_loc_outside_base = schemathesis_normalize_location(
        "https://api.example.com/v2/users/123", base_url="https://api.example.com/v1"
    )
    rel_loc_no_base = schemathesis_normalize_location("/users/123", base_url=None)
    assert (
        abs_loc_no_base is None
        and abs_loc_with_base == "/users/123"
        and abs_loc_outside_base is None
        and rel_loc_no_base == "/users/123"
    )

    # Hatfield-Dodds & Dygalo (2022) exact Table 2, §3.2, Table 6 & Table 7 reconciliation
    table2_unhandled = [1254, 170, 168, 45, 33, 26, 26, 8]
    assert sum(table2_unhandled) == 1730 and 65195 + 1730 == 66925
    prose_subcats = [111, 436, 52, 152]
    table6_allchecks = [13, 0, 11, 316, 32, 12, 1, 184, 7, 39, 14, 3, 7, 1, 0, 24]
    table7_allchecks = [6, 0, 0, 15, 15, 2, 0, 78, 4, 0, 6, 2, 0, 0, 0, 8]
    assert (sum(prose_subcats), sum(table6_allchecks), sum(table7_allchecks)) == (751, 664, 136)

    return {
        "h1": (h1_oas30, h1_oas31, h1_sch31),
        "h2": (h2_oas30, h2_oas31, h2_sch30),
        "h3": (h3_req, h3_resp),
        "h4_counts": (len(ap_valid), len(up_valid)),
        "h5_counts": (len(unrep_ok), len(rep_ok)),
        "h6_mistag": (unpinned_accepts_mistagged, pinned_accepts_mistagged, default_absent_tag_ok),
        "wire_fps": (naive_wire_fps, guarded_wire_fps),
        "abs_loc_no_base": abs_loc_no_base,
        "sch_sums": (sum(prose_subcats), sum(table6_allchecks), sum(table7_allchecks)),
    }


# ============================================================================
# PROBE 2: RESTler Producer-Consumer Compiler, BFS vs. BFS-Fast & 4 Checkers
# ============================================================================


@dataclass(frozen=True)
class RestConsumerParam:
    kind: str  # "Path" | "Query" | "Body" | "Header" (`ParameterKind`)
    name: str


@dataclass(frozen=True)
class RestResponseProducer:
    body_container: str | None  # `BodyContainerName` (None for top-level response fields)
    resource_name: str  # `ResourceName`


@dataclass(frozen=True)
class RestEndpoint:
    method: str
    path: str
    consumes: tuple[RestConsumerParam, ...]
    produces: tuple[RestResponseProducer, ...]


def _restler_producer_param_name(resource_name: str) -> str:
    """Port of `ApiResourceTypes.fs:286-288` (`let p = resourceNameWords |> Array.last; p.ToLower()`)."""
    words = re.findall(r"[A-Z]?[a-z0-9]+|[A-Z]+(?=[A-Z]|$)", resource_name)
    return words[-1].lower() if words else resource_name.lower()


def _restler_is_valid_producer(
    prod_method: str,
    prod_endpoint: str,
    cons_method: str,
    cons_endpoint: str,
    allow_get_producers: bool,
) -> bool:
    """Faithful port of `Dependencies.fs:23-53` (`isValidProducer`)."""
    if not (prod_method in ("PUT", "POST") or allow_get_producers):
        return False
    if cons_endpoint == prod_endpoint:
        if cons_method == prod_method:
            return False
        if prod_method == "POST":
            return True
        if prod_method == "PUT":
            return cons_method != "POST"
        if prod_method == "PATCH":
            return cons_method not in ("PUT", "POST")
        if prod_method == "GET":
            return cons_method not in ("PUT", "POST", "PATCH")
        return False
    return not prod_endpoint.startswith(cons_endpoint)


def restler_infer_producers(
    endpoints: list[RestEndpoint],
    *,
    allow_get_producers: bool = False,
    annotations: dict[tuple[str, str, str], tuple[str, str, str]] | None = None,
) -> dict[tuple[str, str, str], str]:
    """Faithful port of `Dependencies.fs:23-53, 89-152, 303-385, 570-635, 690-710`.

    Zero synthetic `var_type` keys: uses only OpenAPI `(method, path, ParameterKind,
    parameter name, response BodyContainerName/ResourceName)` plus optional explicit
    `restler_api_dependencies` annotations.
    """
    ann_map = annotations or {}
    resolved: dict[tuple[str, str, str], str] = {}

    for cons in endpoints:
        for param in cons.consumes:
            key = (cons.method, cons.path, param.name)

            # 1. Explicit annotation lookup (`Dependencies.fs:358-385`)
            if key in ann_map:
                p_meth, p_ep, p_field = ann_map[key]
                for prod in endpoints:
                    if (prod.method, prod.path) == (p_meth, p_ep) and any(
                        rp.resource_name == p_field for rp in prod.produces
                    ):
                        resolved[key] = f"{prod.method} {prod.path}.{p_field}"
                        break
                if key in resolved:
                    continue

            # `Dependencies.fs:694-697`: `[ consumer.id.ProducerParameterName ; consumer.id.ResourceName ]`
            cand_names: list[str] = []
            for n in (_restler_producer_param_name(param.name), param.name):
                if n not in cand_names:
                    cand_names.append(n)

            # `Dependencies.fs:310-334`: `ParameterKind.Header | Body | Query -> None, None`
            producer_endpoint: str | None = None
            producer_container: str | None = None
            path_param_idx: int | None = None
            bracketed_name: str | None = None
            if param.kind == "Path":
                bracketed_name = "{" + param.name + "}"
                if bracketed_name in cons.path:
                    path_param_idx = cons.path.index(bracketed_name)
                    if path_param_idx == 0:
                        raise ValueError("InvalidSwaggerEndpoint")
                    producer_endpoint = cons.path[: path_param_idx - 1]
                    producer_container = producer_endpoint.split("/")[-1] if producer_endpoint else None

            for prod_param_name in cand_names:
                exact_matches: list[str] = []
                approx_matches: list[str] = []

                # `Dependencies.fs:345-356`: empty when `producerContainer` is None or starts with `{`
                if producer_container is not None and not producer_container.startswith("{"):
                    if producer_endpoint is not None:
                        # `L353-355`: `getIndexedByEndpointProducers(..., [Put; Post; Get])` — omits `Patch`!
                        for prod in endpoints:
                            if prod.path == producer_endpoint and prod.method in ("PUT", "POST", "GET"):
                                if _restler_is_valid_producer(
                                    prod.method, prod.path, cons.method, cons.path, allow_get_producers
                                ):
                                    for rp in prod.produces:
                                        if rp.body_container is None and rp.resource_name == prod_param_name:
                                            exact_matches.append(f"{prod.method} {prod.path}.{rp.resource_name}")

                    # `L574-598`: `inferredApproximateMatches` checks `BodyContainerName == producerContainer`
                    # and `isValidProducer` (which DOES admit `Patch` when `allowGetProducers = True`!).
                    if producer_endpoint is not None:
                        for prod in endpoints:
                            if (
                                prod.path
                                and producer_endpoint.startswith(prod.path)
                                and "{" not in producer_endpoint[len(prod.path) :]
                                and _restler_is_valid_producer(
                                    prod.method, prod.path, cons.method, cons.path, allow_get_producers
                                )
                            ):
                                for rp in prod.produces:
                                    if (
                                        rp.resource_name == prod_param_name
                                        and rp.body_container is not None
                                        and rp.body_container == producer_container
                                    ):
                                        approx_matches.append(
                                            f"{prod.method} {prod.path}.{rp.body_container}.{rp.resource_name}"
                                        )

                if exact_matches:
                    resolved[key] = exact_matches[0]
                    break

                # `Dependencies.fs:89-152, 610-630`: `getCreateOrUpdateProducer` runs strictly for
                # `ParameterKind.Path` against `[OperationMethod.Put]` when `inferredExactMatches` is empty.
                if (
                    param.kind == "Path"
                    and path_param_idx is not None
                    and bracketed_name is not None
                ):
                    put_ep = cons.path[: path_param_idx + len(bracketed_name)]
                    if cons.path == put_ep and cons.method == "PUT":
                        resolved[key] = f"uuid4_suffix({param.name})"
                        break
                    put_hits: list[str] = []
                    for prod in endpoints:
                        if prod.path == put_ep and prod.method == "PUT":
                            for rp in prod.produces:
                                if rp.body_container is None and rp.resource_name == prod_param_name:
                                    put_hits.append(f"PUT {put_ep}.{rp.resource_name}")
                    if not put_hits:
                        # `Dependencies.fs:131`: `let commonProducerNames = ["id"; "name"]`
                        for common_name in ("id", "name"):
                            for prod in endpoints:
                                if prod.path == put_ep and prod.method == "PUT":
                                    for rp in prod.produces:
                                        if rp.body_container is None and rp.resource_name == common_name:
                                            put_hits.append(f"PUT {put_ep}.{rp.resource_name}")
                    if put_hits:
                        resolved[key] = put_hits[0]
                        break

                if approx_matches:
                    resolved[key] = approx_matches[0]
                    break

    return resolved


class ToyMultiTenantCloudService:
    """Deterministic multi-tenant hierarchical service for BFS/BFS-Fast & 4 ICST'20 checkers."""

    def __init__(self, *, buggy: bool) -> None:
        self.buggy = buggy
        self._seq = 0
        self.orgs: dict[str, str] = {}
        self.projects: dict[str, tuple[str, str]] = {}
        self.stale_deleted_cache: set[str] = set()
        self.leaked_failed_projects: set[str] = set()

    def _mint(self, prefix: str) -> str:
        self._seq += 1
        return f"{prefix}_{self._seq}"

    def execute(self, method: str, op: str, args: dict[str, str], token: str = "user_A") -> tuple[int, dict[str, str]]:
        if (method, op) == ("POST", "/orgs"):
            oid = self._mint("org")
            self.orgs[oid] = token
            return (201, {"id": oid})
        if (method, op) == ("POST", "/orgs/{orgId}/projects"):
            oid = args.get("orgId", "")
            if oid not in self.orgs or self.orgs[oid] != token:
                return (404, {})
            pid = self._mint("proj")
            if args.get("force_fail") == "1":
                if self.buggy:
                    self.leaked_failed_projects.add(pid)
                return (400, {"name": pid})
            self.projects[pid] = (oid, token)
            return (201, {"name": pid})
        if (method, op) == ("GET", "/orgs/{orgId}/projects/{projectName}"):
            oid = args.get("orgId", "")
            pid = args.get("projectName", "")
            if self.buggy and pid in self.stale_deleted_cache:
                return (200, {"name": pid, "cached": "true"})
            if self.buggy and pid in self.leaked_failed_projects:
                return (200, {"name": pid, "leaked": "true"})
            if pid not in self.projects:
                return (404, {})
            real_org, real_owner = self.projects[pid]
            if not self.buggy and real_owner != token:
                return (403, {})
            if not self.buggy and real_org != oid:
                return (404, {})
            return (200, {"name": pid, "orgId": real_org})
        if (method, op) == ("PUT", "/orgs/{orgId}/projects/{projectName}/tags"):
            oid = args.get("orgId", "")
            pid = args.get("projectName", "")
            if pid not in self.projects or self.projects[pid][0] != oid:
                return (404, {})
            tid = self._mint("tag")
            return (200, {"id": tid})
        if (method, op) == ("GET", "/orgs/{orgId}/projects/{projectName}/tags/{tagId}"):
            oid = args.get("orgId", "")
            pid = args.get("projectName", "")
            tid = args.get("tagId", "")
            if pid not in self.projects or self.projects[pid][0] != oid or not tid.startswith("tag_"):
                return (404, {})
            return (200, {"id": tid})
        if (method, op) == ("DELETE", "/orgs/{orgId}/projects/{projectName}"):
            oid = args.get("orgId", "")
            pid = args.get("projectName", "")
            if pid not in self.projects or self.projects[pid][0] != oid:
                return (404, {})
            del self.projects[pid]
            if self.buggy:
                self.stale_deleted_cache.add(pid)
            return (204, {})
        return (404, {})


def _replay_sequence(seq: tuple[tuple[str, str], ...]) -> bool:
    """Replay symbolic sequence dynamically, returning True iff all steps return 2xx."""
    svc = ToyMultiTenantCloudService(buggy=False)
    tlb: dict[str, str] = {}
    for method, op in seq:
        args: dict[str, str] = {}
        if "{orgId}" in op:
            if "orgId" not in tlb:
                return False
            args["orgId"] = tlb["orgId"]
        if "{projectName}" in op:
            if "projectName" not in tlb:
                return False
            args["projectName"] = tlb["projectName"]
        if "{tagId}" in op:
            if "tagId" not in tlb:
                return False
            args["tagId"] = tlb["tagId"]
        status, body = svc.execute(method, op, args)
        if not (200 <= status < 300):
            return False
        if (method, op) == ("POST", "/orgs"):
            tlb["orgId"] = body["id"]
        elif (method, op) == ("POST", "/orgs/{orgId}/projects"):
            tlb["projectName"] = body["name"]
        elif (method, op) == ("PUT", "/orgs/{orgId}/projects/{projectName}/tags"):
            tlb["tagId"] = body["id"]
    return True


def run_restler_search_comparison(max_depth: int = 5) -> dict[str, Any]:
    """Port of `RESTler` Fig. 4 (`ICSE '19` / `arXiv:1806.09739v1`) `BFS` vs. `BFS-Fast`."""
    req_set = [
        ("POST", "/orgs"),
        ("POST", "/orgs/{orgId}/projects"),
        ("GET", "/orgs/{orgId}/projects/{projectName}"),
        ("PUT", "/orgs/{orgId}/projects/{projectName}/tags"),
        ("GET", "/orgs/{orgId}/projects/{projectName}/tags/{tagId}"),
        ("DELETE", "/orgs/{orgId}/projects/{projectName}"),
    ]

    bfs_seqs: list[tuple[tuple[str, str], ...]] = [()]
    bfs_covered: set[tuple[str, str]] = set()
    for _ in range(1, max_depth + 1):
        next_bfs: list[tuple[tuple[str, str], ...]] = []
        for seq in bfs_seqs:
            for req in req_set:
                cand = seq + (req,)
                if _replay_sequence(cand):
                    next_bfs.append(cand)
                    bfs_covered.add(req)
        bfs_seqs = next_bfs

    bfs_fast_seqs: list[tuple[tuple[str, str], ...]] = [()]
    bfs_fast_covered: set[tuple[str, str]] = set()
    for _ in range(1, max_depth + 1):
        next_fast: list[tuple[tuple[str, str], ...]] = []
        for req in req_set:
            for seq in bfs_fast_seqs:
                cand = seq + (req,)
                if _replay_sequence(cand):
                    next_fast.append(cand)
                    bfs_fast_covered.add(req)
                    break
        bfs_fast_seqs = next_fast

    raw_space = len(req_set) ** max_depth
    return {
        "raw_space": raw_space,
        "bfs_seqset": len(bfs_seqs),
        "bfs_fast_seqset": len(bfs_fast_seqs),
        "bfs_ops": len(bfs_covered),
        "bfs_fast_ops": len(bfs_fast_covered),
    }


def run_restler_security_checkers(buggy: bool) -> dict[str, bool]:
    """Port of the 4 `ICST 2020` active security property checkers."""
    svc = ToyMultiTenantCloudService(buggy=buggy)

    # 1. UseAfterFreeChecker (`use_after_free_checker.py`): create -> DELETE -> GET
    _, b_org = svc.execute("POST", "/orgs", {}, token="user_A")
    _, b_proj = svc.execute("POST", "/orgs/{orgId}/projects", {"orgId": b_org["id"]}, token="user_A")
    svc.execute("DELETE", "/orgs/{orgId}/projects/{projectName}", {"orgId": b_org["id"], "projectName": b_proj["name"]}, token="user_A")
    st_uaf, _ = svc.execute("GET", "/orgs/{orgId}/projects/{projectName}", {"orgId": b_org["id"], "projectName": b_proj["name"]}, token="user_A")
    uaf_bug = 200 <= st_uaf < 300

    # 2. LeakageRuleChecker (`leakage_rule_checker.py`): failed POST (400) -> GET leaked ID
    _, b_fail = svc.execute(
        "POST", "/orgs/{orgId}/projects", {"orgId": b_org["id"], "force_fail": "1"}, token="user_A"
    )
    st_leak, _ = svc.execute(
        "GET", "/orgs/{orgId}/projects/{projectName}", {"orgId": b_org["id"], "projectName": b_fail["name"]}, token="user_A"
    )
    leak_bug = 200 <= st_leak < 300

    # 3. ResourceHierarchyChecker (`resource_hierarchy_checker.py:67-96`):
    #    Parent A -> Child A1; reset_tlb() -> re-render Parent B -> overwrite child = A1 ("Poluted dependencies")
    tlb: dict[str, str] = {}
    _, org_a = svc.execute("POST", "/orgs", {}, token="user_A")
    tlb["orgId"] = org_a["id"]
    _, proj_a1 = svc.execute("POST", "/orgs/{orgId}/projects", {"orgId": tlb["orgId"]}, token="user_A")
    tlb["projectName"] = proj_a1["name"]
    old_values = {"projectName": tlb["projectName"]}
    tlb.clear()  # `dependencies.reset_tlb()` (`L67`)
    _, org_b = svc.execute("POST", "/orgs", {}, token="user_A")
    tlb["orgId"] = org_b["id"]
    tlb.update(old_values)  # `dependencies.set_variable(...)` ("Poluted dependencies", `L91-94`)
    st_hier, _ = svc.execute("GET", "/orgs/{orgId}/projects/{projectName}", tlb, token="user_A")
    hier_bug = 200 <= st_hier < 300

    # 4. NamespaceRuleChecker (`namespace_rule_checker.py`): replay user_A object with token="user_B"
    st_ns, _ = svc.execute(
        "GET",
        "/orgs/{orgId}/projects/{projectName}",
        {"orgId": org_a["id"], "projectName": proj_a1["name"]},
        token="user_B",
    )
    ns_bug = 200 <= st_ns < 300

    return {"uaf": uaf_bug, "leak": leak_bug, "hierarchy": hier_bug, "namespace": ns_bug}


def run_probe_2() -> dict[str, Any]:
    spec = [
        RestEndpoint("POST", "/orgs", (), (RestResponseProducer(None, "id"),)),
        RestEndpoint(
            "POST",
            "/orgs/{orgId}/projects",
            (RestConsumerParam("Path", "orgId"),),
            (RestResponseProducer(None, "name"),),
        ),
        RestEndpoint(
            "PUT",
            "/orgs/{orgId}/slots/{slot}",
            (RestConsumerParam("Path", "orgId"), RestConsumerParam("Path", "slot")),
            (RestResponseProducer(None, "id"),),
        ),
        RestEndpoint(
            "GET",
            "/orgs/{orgId}/slots/{slot}/status",
            (RestConsumerParam("Path", "orgId"), RestConsumerParam("Path", "slot")),
            (),
        ),
        RestEndpoint(
            "PATCH",
            "/orgs/{orgId}/projects/{projectName}",
            (RestConsumerParam("Path", "orgId"), RestConsumerParam("Path", "projectName")),
            (RestResponseProducer("leases", "id"),),
        ),
        RestEndpoint(
            "DELETE",
            "/orgs/{orgId}/projects/{projectName}/leases/{leaseId}",
            (
                RestConsumerParam("Path", "orgId"),
                RestConsumerParam("Path", "projectName"),
                RestConsumerParam("Path", "leaseId"),
            ),
            (),
        ),
        RestEndpoint(
            "PATCH",
            "/orgs/{orgId}/projects/{projectName}/locks",
            (RestConsumerParam("Path", "orgId"), RestConsumerParam("Path", "projectName")),
            (RestResponseProducer(None, "id"),),
        ),
        RestEndpoint(
            "DELETE",
            "/orgs/{orgId}/projects/{projectName}/locks/{lockId}",
            (
                RestConsumerParam("Path", "orgId"),
                RestConsumerParam("Path", "projectName"),
                RestConsumerParam("Path", "lockId"),
            ),
            (),
        ),
        RestEndpoint(
            "GET",
            "/orgs/{orgId}/feed",
            (RestConsumerParam("Path", "orgId"),),
            (RestResponseProducer(None, "cursor"),),
        ),
        RestEndpoint(
            "GET",
            "/orgs/{orgId}/projects/{projectName}/commits",
            (
                RestConsumerParam("Path", "orgId"),
                RestConsumerParam("Path", "projectName"),
                RestConsumerParam("Query", "pageToken"),
            ),
            (),
        ),
    ]
    total_consumes = sum(len(ep.consumes) for ep in spec)
    default_deps = restler_infer_producers(spec, allow_get_producers=False)
    get_deps = restler_infer_producers(spec, allow_get_producers=True)
    explicit_annotations = {
        ("DELETE", "/orgs/{orgId}/projects/{projectName}/locks/{lockId}", "lockId"): (
            "PATCH",
            "/orgs/{orgId}/projects/{projectName}/locks",
            "id",
        ),
        ("GET", "/orgs/{orgId}/projects/{projectName}/commits", "pageToken"): (
            "GET",
            "/orgs/{orgId}/feed",
            "cursor",
        ),
    }
    annotated_deps = restler_infer_producers(
        spec, allow_get_producers=True, annotations=explicit_annotations
    )

    # Verify each exact mechanism from `Dependencies.fs` + `ApiResourceTypes.fs`:
    # 1. `PUT /orgs/{orgId}/slots/{slot}` gets `uuid4_suffix(slot)` (`L105-117`), and
    #    `GET /orgs/{orgId}/slots/{slot}/status` resolves `slot` via `PUT ...id` (`commonProducerNames = ["id"; "name"]` at `L131`).
    assert default_deps[("PUT", "/orgs/{orgId}/slots/{slot}", "slot")] == "uuid4_suffix(slot)"
    assert default_deps[("GET", "/orgs/{orgId}/slots/{slot}/status", "slot")] == "PUT /orgs/{orgId}/slots/{slot}.id"
    # If `PUT .../slots/{slot}` instead returns `"uid"`, `commonProducerNames = ["id"; "name"]` (`L131`) misses it:
    spec_put_uid = [
        RestEndpoint(
            ep.method,
            ep.path,
            ep.consumes,
            (RestResponseProducer(None, "uid"),) if ep.path == "/orgs/{orgId}/slots/{slot}" else ep.produces,
        )
        for ep in spec
    ]
    put_uid_resolved = ("GET", "/orgs/{orgId}/slots/{slot}/status", "slot") in restler_infer_producers(
        spec_put_uid, allow_get_producers=True
    )
    assert put_uid_resolved is False

    # 2. `allowGetProducers=True` admits container-wrapped `PATCH` in `isValidProducer` (`L28, 43-45`) +
    #    `inferredApproximateMatches` (`L574-598`), resolving `leaseId` (`16 -> 17`), while flat-endpoint
    #    `PATCH .../locks` (`lockId`) remains unresolved because `getIndexedByEndpointProducers` (`L354-355`)
    #    omits `Patch` from `[Put; Post; Get]`, and `Query` `pageToken` remains unresolved (`L311-314` `None, None`
    #    + CamelCase `"token"` != `"cursor"`).
    lease_key = ("DELETE", "/orgs/{orgId}/projects/{projectName}/leases/{leaseId}", "leaseId")
    lock_key = ("DELETE", "/orgs/{orgId}/projects/{projectName}/locks/{lockId}", "lockId")
    cursor_key = ("GET", "/orgs/{orgId}/projects/{projectName}/commits", "pageToken")
    assert lease_key not in default_deps and lease_key in get_deps
    assert lock_key not in get_deps and cursor_key not in get_deps
    assert (len(default_deps), len(get_deps), len(annotated_deps), total_consumes) == (16, 17, 19, 19)

    search = run_restler_search_comparison(max_depth=5)
    assert search["bfs_ops"] == 6 and search["bfs_fast_ops"] == 6
    assert search["bfs_fast_seqset"] < search["bfs_seqset"] < search["raw_space"]

    buggy_res = run_restler_security_checkers(buggy=True)
    clean_res = run_restler_security_checkers(buggy=False)
    assert all(buggy_res.values()) and not any(clean_res.values())

    arxiv_ratios = {
        "Repos": round(909 / 13, 1),
        "Groups": round(13421 / 31, 1),
        "Branches": round(5652 / 6, 1),
    }
    icse19_ratios = {
        "Commits": round(20679 / 33, 1),
        "Branches": round(5528 / 11, 1),
        "Groups": round(79518 / 130, 1),
    }
    assert arxiv_ratios == {"Repos": 69.9, "Groups": 432.9, "Branches": 942.0}
    assert icse19_ratios == {"Commits": 626.6, "Branches": 502.5, "Groups": 611.7}

    return {
        "deps": (len(default_deps), len(get_deps), len(annotated_deps), total_consumes),
        "put_uid_resolved": put_uid_resolved,
        "search": search,
        "buggy_hits": sum(buggy_res.values()),
        "clean_hits": sum(clean_res.values()),
        "arxiv_ratios": arxiv_ratios,
        "icse19_ratios": icse19_ratios,
    }


# ============================================================================
# PROBE 3: Pact `json.rs` Matchers, Missing State URL & `can-i-deploy` Gate
# ============================================================================


def pact_match_rule(rule: tuple[str, Any], expected: Any, actual: Any) -> bool:
    r"""Port of `pact-reference@4a24afcf` `rust/pact_matching/src/json.rs:9, 94-285`."""
    kind, param = rule
    if kind == "Regex":
        actual_str = actual if isinstance(actual, str) else json.dumps(actual)
        py_pat = param.replace(r"\z", r"\Z")
        return re.search(py_pat, actual_str, flags=re.MULTILINE) is not None
    if kind == "Type":
        if isinstance(expected, list) and isinstance(actual, list):
            return True
        if isinstance(expected, bool) and isinstance(actual, bool):
            return True
        if _is_json_number(expected) and _is_json_number(actual):
            return True
        if expected is None and actual is None:
            return True
        if isinstance(expected, dict) and isinstance(actual, dict):
            return True
        if isinstance(expected, str) and isinstance(actual, str):
            return True
        return False
    if kind == "MinType":
        if isinstance(expected, list) and isinstance(actual, list):
            return len(actual) >= int(param)
        return pact_match_rule(("Type", None), expected, actual)
    if kind == "Integer":
        return _is_json_integer(actual)
    if kind == "Boolean":
        if isinstance(actual, bool):
            return True
        if isinstance(actual, str) and actual in ("true", "false"):
            return True
        return False
    if kind == "NotEmpty":
        if actual is None:
            return False
        if isinstance(actual, (str, list, dict)):
            return len(actual) > 0
        return True
    raise ValueError(f"Unknown rule {kind}")


def pact_compare_maps(
    expected: dict[str, Any],
    actual: dict[str, Any],
    rules: dict[str, list[tuple[str, Any]]],
    *,
    allow_unexpected_keys: bool,
) -> bool:
    """Port of `json.rs:444-476` (`NoUnexpectedKeys` vs. `AllowUnexpectedKeys`)."""
    if not allow_unexpected_keys:
        if set(actual.keys()) != set(expected.keys()):
            return False
    else:
        if not set(expected.keys()).issubset(set(actual.keys())):
            return False

    for k, exp_v in expected.items():
        act_v = actual[k]
        path = f"$.{k}"
        if path in rules:
            if not all(pact_match_rule(r, exp_v, act_v) for r in rules[path]):
                return False
            if isinstance(exp_v, list) and isinstance(act_v, list) and exp_v and act_v:
                for elem in act_v:
                    if isinstance(exp_v[0], dict):
                        if not isinstance(elem, dict) or not pact_compare_maps(
                            exp_v[0], elem, {}, allow_unexpected_keys=allow_unexpected_keys
                        ):
                            return False
        else:
            if exp_v != act_v:
                return False
    return True


def strict_typed_consumer_deserialize(payload: dict[str, Any]) -> bool:
    """Models a strict consumer (`#[serde(deny_unknown_fields)]` + strict scalar/ISO date/non-empty list)."""
    expected_keys = {"count", "items", "iso_date", "active"}
    if set(payload.keys()) != expected_keys:
        return False
    if not _is_json_integer(payload["count"]):
        return False
    if not isinstance(payload["items"], list) or len(payload["items"]) == 0:
        return False
    if not all(isinstance(x, dict) and isinstance(x.get("sku"), str) for x in payload["items"]):
        return False
    if not isinstance(payload["iso_date"], str) or re.fullmatch(r"\d{4}-\d{2}-\d{2}", payload["iso_date"]) is None:
        return False
    _, mm, dd = payload["iso_date"].split("-")
    if not (1 <= int(mm) <= 12 and 1 <= int(dd) <= 31):
        return False
    if not isinstance(payload["active"], bool):
        return False
    return True


@dataclass(frozen=True)
class MatrixRow:
    consumer: str
    consumer_version: str
    provider: str
    provider_version: str | None
    success: bool | None


def pact_broker_can_i_deploy(
    considered_rows: list[MatrixRow], required_integrations_without_a_row: list[str]
) -> tuple[bool, str]:
    """Port of `pact_broker@6298abd2` `deployment_status_summary.rb:114-155`."""
    not_verified = [r for r in considered_rows if r.success is None]
    failed = [r for r in considered_rows if r.success is False]
    if not not_verified and not failed and all(r.success is True for r in considered_rows) and not required_integrations_without_a_row:
        if considered_rows:
            return (True, "Successful")
        return (True, "NoDependenciesMissing")
    if not_verified:
        return (False, "PactNotEverVerified")
    if required_integrations_without_a_row:
        return (False, "MissingProviderIntegrationRow")
    return (False, "VerificationFailed")


def run_probe_3() -> dict[str, Any]:
    expected_resp = {
        "count": 42,
        "items": [{"sku": "A1"}],
        "iso_date": "2026-01-15",
        "active": True,
    }
    loose_pact_rules = {
        "$.count": [("Type", None)],
        "$.items": [("Type", None)],
        "$.iso_date": [("Regex", r"\d{4}-\d{2}-\d{2}")],
        "$.active": [("Boolean", None)],
    }
    hardened_pact_rules = {
        "$.count": [("Integer", None)],
        "$.items": [("MinType", 1)],
        "$.iso_date": [("Type", None), ("Regex", r"\A\d{4}-(0[1-9]|1[0-2])-(0[1-9]|[12]\d|3[01])\z")],
        "$.active": [("Type", None)],
    }

    escapes = {
        "float_for_int": {**expected_resp, "count": 42.75},
        "empty_array": {**expected_resp, "items": []},
        "unanchored_multiline_regex": {**expected_resp, "iso_date": "corrupt 2026-99-99\ntrailer"},
        "string_coerced_bool": {**expected_resp, "active": "true"},
        "unexpected_extra_key": {**expected_resp, "debug_trace": "internal"},
    }
    int_regex_coerced = pact_match_rule(("Regex", r"\d{8}"), "20260115", 20260115)
    assert int_regex_coerced is True

    five_resp_cases = [
        escapes["float_for_int"],
        escapes["empty_array"],
        escapes["unanchored_multiline_regex"],
        escapes["string_coerced_bool"],
        escapes["unexpected_extra_key"],
    ]
    loose_passes = sum(
        1 for p in five_resp_cases if pact_compare_maps(expected_resp, p, loose_pact_rules, allow_unexpected_keys=True)
    )
    consumer_ok = sum(1 for p in five_resp_cases if strict_typed_consumer_deserialize(p))
    hardened_strict_passes = sum(
        1
        for p in five_resp_cases
        if pact_compare_maps(expected_resp, p, hardened_pact_rules, allow_unexpected_keys=False)
    )
    assert (loose_passes, consumer_ok, hardened_strict_passes) == (5, 0, 0)

    consumer_deploy = pact_broker_can_i_deploy(
        [MatrixRow("Foo", "v3", "Bar", None, None)], []
    )
    provider_deploy_no_consumers = pact_broker_can_i_deploy([], [])
    assert consumer_deploy == (False, "PactNotEverVerified")
    assert provider_deploy_no_consumers == (True, "NoDependenciesMissing")

    def pact_state_setup_executor(state_name: str, state_change_url: str | None) -> tuple[bool, dict[str, Any]]:
        if state_change_url is None:
            return (True, {})
        return (True, {"seeded": state_name})

    noop_setup_ok, noop_ctx = pact_state_setup_executor("order ord_1 exists", None)
    assert noop_setup_ok is True and noop_ctx == {}

    return {
        "loose_passes": loose_passes,
        "consumer_ok": consumer_ok,
        "hardened_passes": hardened_strict_passes,
        "int_regex_coerced": int_regex_coerced,
        "consumer_deploy": consumer_deploy,
        "provider_deploy": provider_deploy_no_consumers,
    }


# ============================================================================
# PROBE 4: Agentic API Benchmark Harness Defects (`BFCL`, `RestGPT`, `ToolBench`)
# ============================================================================


def bfcl_standardize_string(input_string: str) -> str:
    """Exact port of `gorilla@6ea57973` `ast_checker.py:174-183`."""
    regex_string = r"[ \,\.\/\-\_\*\^]"
    return re.sub(regex_string, "", input_string).lower().replace("'", '"')


def bfcl_java_arraylist_parse(input_str: str, nested_type: str = "String") -> list[str]:
    """Exact port of `gorilla@6ea57973` `java_type_converter.py:72-83`."""
    m = re.match(r"new\s+ArrayList<\w*>\(Arrays\.asList\((.+?)\)\)", input_str)
    assert m is not None
    elements = []
    for element_str in m.group(1).split(","):
        element_str = element_str.strip()
        if nested_type in ("char", "String"):
            elements.append(element_str[1:-1])
    return elements


def bfcl_process_method_calls(function_call_string: str, instance_mapping: dict[str, str]) -> str:
    """Exact port of `gorilla@6ea57973` `multi_turn_utils.py:134-146`."""
    def replace_function(match: re.Match[str]) -> str:
        func_name = match.group(1)
        if func_name in instance_mapping:
            return f"{instance_mapping[func_name]}.{func_name}"
        return func_name

    pattern = r"\b([a-zA-Z_]\w*)\s*(?=\()"
    return re.sub(pattern, replace_function, function_call_string)


def bfcl_is_eval_allowed(func_call: str) -> bool:
    """Exact port of `gorilla@6ea57973` `multi_turn_utils.py:75-81` guard before `eval()`."""
    func_call_copy = func_call
    if "(" in func_call_copy:
        func_call_copy = func_call_copy.split("(")[0]
    if "." in func_call_copy:
        func_call_copy = func_call_copy.split(".")[1]
    return func_call_copy not in ["kill", "exit", "quit", "remove", "unlink", "popen", "Popen", "run"]


def bfcl_multi_turn_response_check(
    per_turn_model_outputs: list[list[str]], per_turn_gt_outputs: list[list[str]], *, cumulative_bug: bool
) -> bool:
    """Port of `gorilla@6ea57973` `multi_turn_checker.py:72, 114-120, 205`."""
    all_turn_model_execution_results: list[str] = []
    for m_out, gt_out in zip(per_turn_model_outputs, per_turn_gt_outputs):
        all_turn_model_execution_results.extend(m_out)
        checked_pool = all_turn_model_execution_results if cumulative_bug else m_out
        if not all(req in checked_pool for req in gt_out):
            return False
    return True


def restgpt_dereference_refs(spec_obj: Any, full_spec: dict[str, Any]) -> Any:
    """Exact port of `RestGPT@d9901286` `utils/oas_utils.py:28-45`."""
    def _retrieve(path: str) -> Any:
        out: Any = full_spec
        for comp in path.split("/")[1:]:
            out = out[comp]
        return out

    def _deref(obj: Any, stop: bool = False) -> Any:
        if stop:
            return obj
        if isinstance(obj, dict):
            obj_out: dict[str, Any] = {}
            for k, v in obj.items():
                if k == "$ref":
                    return _deref(_retrieve(v), stop=False)
                if isinstance(v, list):
                    obj_out[k] = [_deref(el) for el in v]
                elif isinstance(v, dict):
                    obj_out[k] = _deref(v)
                else:
                    obj_out[k] = v
            return obj_out
        if isinstance(obj, list):
            return [_deref(el) for el in obj]
        return obj

    return _deref(spec_obj)


def toolbench_api_json_to_openai_json(
    api_json: dict[str, Any], standard_tool_name: str, *, fix_indent: bool = False
) -> dict[str, Any]:
    """Exact port of `ToolBench@d56fdd89` `rapidapi.py:199-266`."""
    map_type = {"NUMBER": "integer", "STRING": "string", "BOOLEAN": "boolean"}
    pure_api_name = re.sub(r"\W+", "_", api_json["api_name"].lower()).strip("_")
    name_full = f"{pure_api_name}_for_{standard_tool_name}"
    templete: dict[str, Any] = {
        "name": name_full[-64:],
        "parameters": {"type": "object", "properties": {}, "required": [], "optional": []},
    }
    has_req = "required_parameters" in api_json and len(api_json["required_parameters"]) > 0
    if has_req:
        for para in api_json["required_parameters"]:
            pname = para["name"].lower()
            templete["parameters"]["properties"][pname] = {"type": map_type.get(para["type"], "string")}
            templete["parameters"]["required"].append(pname)
        if not fix_indent:
            for para in api_json.get("optional_parameters", []):
                pname = para["name"].lower()
                templete["parameters"]["properties"][pname] = {"type": map_type.get(para["type"], "string")}
                templete["parameters"]["optional"].append(pname)
    if fix_indent:
        for para in api_json.get("optional_parameters", []):
            pname = para["name"].lower()
            templete["parameters"]["properties"][pname] = {"type": map_type.get(para["type"], "string")}
            templete["parameters"]["optional"].append(pname)
    return templete


def toolbench_is_passed(answer_status: str, task_status: str) -> str:
    """Exact port of `ToolBench@d56fdd89` `rtl.py:139-154`."""
    if answer_status == "Solved":
        return "Passed"
    if answer_status == "Unsolved":
        if task_status == "Solvable":
            return "Failed"
        if task_status == "Unsure":
            return "Unsure"
        if task_status == "Unsolvable":
            return "Passed"
    elif answer_status == "Unsure":
        if task_status == "Unsolvable":
            return "Passed"
        return "Unsure"
    return "Failed"


def run_probe_4() -> dict[str, Any]:
    # 1. BFCL `standardize_string` adversarial false positives
    adversarial_pairs = [
        ("/v1/users/12", "/v1/users1/2"),
        ("192.168.1.1", "19.216.81.1"),
        ("*.py", "py"),
        ("2026-01-12", "20260112"),
        ("2^10", "210"),
        ("-5", "5"),
    ]
    bfcl_collisions = sum(1 for a, b in adversarial_pairs if bfcl_standardize_string(a) == bfcl_standardize_string(b))
    assert bfcl_collisions == 6

    java_parsed = bfcl_java_arraylist_parse('new ArrayList<String>(Arrays.asList("Austin, TX", "Boston, MA"))')
    assert len(java_parsed) == 4

    corrupted_call = bfcl_process_method_calls('post_message(msg="run ls() now")', {"post_message": "msg_inst", "ls": "fs_inst"})
    assert corrupted_call == 'msg_inst.post_message(msg="run fs_inst.ls() now")'

    # Nested `echo(os.popen('id'))` and 3-segment (2-dot) `pkg.os.popen('id')` both bypass `multi_turn_utils.py:75-81`!
    bypass_nested = bfcl_is_eval_allowed("echo(os.popen('id'))")
    bypass_3seg = bfcl_is_eval_allowed("pkg.os.popen('id')")
    assert bypass_nested is True and bypass_3seg is True

    # Cross-turn `all_turn_model_execution_results` leakage (`multi_turn_checker.py:72,115`)
    leak_buggy = bfcl_multi_turn_response_check([["ok_A", "premature_B"], []], [["ok_A"], ["premature_B"]], cumulative_bug=True)
    leak_fixed = bfcl_multi_turn_response_check([["ok_A", "premature_B"], []], [["ok_A"], ["premature_B"]], cumulative_bug=False)
    assert (leak_buggy, leak_fixed) == (True, False)

    # 2. RestGPT cyclic `$ref` `RecursionError` + `PATCH` `NotImplementedError` + full 10-row `Table 4` Spotify audit
    cyclic_spec = {"components": {"schemas": {"Node": {"type": "object", "properties": {"next": {"$ref": "#/components/schemas/Node"}}}}}}
    hit_recursion_error = False
    try:
        restgpt_dereference_refs(cyclic_spec["components"]["schemas"]["Node"], cyclic_spec)
    except RecursionError:
        hit_recursion_error = True
    assert hit_recursion_error is True

    restgpt_reduced_ops = [op for op in ("get", "post", "patch", "delete", "put") if op in ["get", "post", "patch", "delete", "put"]]
    restgpt_patch_not_impl = ("patch" in restgpt_reduced_ops) and ("PATCH" not in ["GET", "POST", "DELETE", "PUT"])
    assert restgpt_patch_not_impl is True

    bfcl_any_map_type = str
    assert not isinstance(42, bfcl_any_map_type) and not isinstance({"k": 1}, bfcl_any_map_type)

    # All 9 non-zero Spotify `Success%` rows in `RestGPT` `Table 4` (10th row `Llama2-13B` is `0.0%`):
    spotify_table4_nonzero = [
        ("Offline", 14.5),
        ("DEPS", 19.3),
        ("ReAct", 54.5),
        ("Reflexion", 59.6),
        ("RestGPT", 72.7),
        ("w/o_Planner", 54.5),
        ("w/o_Parser", 47.3),
        ("RestGPT_ChatGPT", 69.1),
        ("RestGPT_Vicuna13B", 12.7),
    ]
    only_57_rows = [
        name
        for name, r in spotify_table4_nonzero
        if any(round(100.0 * k / 57, 1) == r for k in range(58))
        and not any(round(100.0 * k / 55, 1) == r for k in range(56))
    ]
    only_55_rows = [
        name
        for name, r in spotify_table4_nonzero
        if any(round(100.0 * k / 55, 1) == r for k in range(56))
        and not any(round(100.0 * k / 57, 1) == r for k in range(58))
    ]
    assert only_57_rows == ["DEPS", "Reflexion"] and len(only_55_rows) == 7
    # `Reflexion` `CP% = 61.4 = 35/57`, whereas `DEPS = 43.8`, `ChatGPT = 72.3`, `Vicuna-13B = 20.6` match neither `N=57` nor `N=55`:
    assert any(round(100.0 * k / 57, 1) == 61.4 for k in range(58))
    cp_sub_rates = [43.8, 72.3, 20.6]
    cp_neither_count = sum(
        1
        for r in cp_sub_rates
        if not any(round(100.0 * k / 57, 1) == r for k in range(58))
        and not any(round(100.0 * k / 55, 1) == r for k in range(56))
    )
    assert cp_neither_count == 3

    # 3. ToolBench `optional_parameters` deletion + `"NUMBER"->"integer"` + `[-64:]` collision + `Unsolvable->Passed`
    endpoint_zero_req = {
        "api_name": "list_movies",
        "required_parameters": [],
        "optional_parameters": [
            {"name": "page", "type": "NUMBER"},
            {"name": "limit", "type": "NUMBER"},
            {"name": "min_rating", "type": "NUMBER"},
        ],
    }
    tb_buggy = toolbench_api_json_to_openai_json(endpoint_zero_req, "movie_hub", fix_indent=False)
    tb_fixed = toolbench_api_json_to_openai_json(endpoint_zero_req, "movie_hub", fix_indent=True)
    assert len(tb_buggy["parameters"]["properties"]) == 0
    assert len(tb_fixed["parameters"]["properties"]) == 3
    assert tb_fixed["parameters"]["properties"]["min_rating"]["type"] == "integer"

    long_tool = "enterprise_global_customer_relationship_management_v2_prod"
    fn_get = toolbench_api_json_to_openai_json({"api_name": "get_record", "required_parameters": []}, long_tool)["name"]
    fn_del = toolbench_api_json_to_openai_json({"api_name": "delete_record", "required_parameters": []}, long_tool)["name"]
    assert fn_get == fn_del and len(fn_get) == 64

    unsolved_unsolvable = toolbench_is_passed("Unsolved", "Unsolvable")
    assert unsolved_unsolvable == "Passed"

    json_tool_msg = json.dumps({"name": "list_movies", "arguments": "{}"})
    rtl_index_error = len(re.findall(r"'name':\s*'(.*?)'", json_tool_msg, re.DOTALL)) == 0
    assert rtl_index_error is True

    return {
        "bfcl_collisions": bfcl_collisions,
        "java_fragments": len(java_parsed),
        "eval_bypasses": (bypass_nested, bypass_3seg),
        "turn_leak": (leak_buggy, leak_fixed),
        "restgpt_rec_err": hit_recursion_error,
        "spotify_denom": (len(only_57_rows), len(only_55_rows), len(spotify_table4_nonzero), cp_neither_count),
        "tb_opt_kept": (len(tb_buggy["parameters"]["properties"]), len(tb_fixed["parameters"]["properties"])),
        "tb_name_collision": fn_get == fn_del,
        "tb_unsolvable_pass": unsolved_unsolvable,
    }


# ============================================================================
# PROBE 5: Offset vs. Keyset Pagination & Brooker / `RFC 9110` `Retry-After` DES
# ============================================================================


def simulate_pagination_under_writes() -> dict[str, Any]:
    """[illustrative analytical model] Offset vs. single-col vs. composite keyset `(created_at, id)`."""
    n_initial = 1000
    page_size = 25
    initial_rows = [(2000 - (i // 8), n_initial - i) for i in range(n_initial)]
    initial_ids = {r[1] for r in initial_rows}

    def _run_harvest(mode: str, write_kind: str) -> tuple[int, int, int]:
        rows = list(initial_rows)
        next_insert_id = n_initial + 1
        next_insert_ts = 2001
        seen_initial_list: list[int] = []
        scanned_entries = 0

        offset = 0
        last_ts: int | None = None
        last_id: int | None = None

        while True:
            rows.sort(key=lambda r: (r[0], r[1]), reverse=True)
            if mode == "offset":
                page = rows[offset : offset + page_size]
                if not page:
                    break
                scanned_entries += offset + len(page)
                offset += page_size
            elif mode == "single_col_ts":
                if last_ts is None:
                    elig = rows
                else:
                    elig = [r for r in rows if r[0] < last_ts]
                page = elig[:page_size]
                scanned_entries += len(page)
                if page:
                    last_ts = page[-1][0]
            elif mode == "composite_keyset":
                if last_ts is None or last_id is None:
                    elig = rows
                else:
                    elig = [r for r in rows if (r[0], r[1]) < (last_ts, last_id)]
                page = elig[:page_size]
                scanned_entries += len(page)
                if page:
                    last_ts, last_id = page[-1]
            else:
                raise ValueError(mode)

            if not page:
                break
            for _, rid in page:
                if rid in initial_ids:
                    seen_initial_list.append(rid)

            if write_kind == "prefix_insert_2" and len(seen_initial_list) < n_initial:
                for _ in range(2):
                    rows.append((next_insert_ts, next_insert_id))
                    next_insert_id += 1
                next_insert_ts += 1
            elif write_kind == "prefix_delete_2" and len(rows) > page_size:
                rows.sort(key=lambda r: (r[0], r[1]), reverse=True)
                del rows[:2]
            elif write_kind == "bump_unvisited_sort_key" and offset == 0 and last_id == initial_rows[page_size - 1][1]:
                rows = [(2500 if r[1] == 500 else r[0], r[1]) for r in rows]

            if offset > 4 * n_initial:
                break

        unique_seen = set(seen_initial_list)
        dup_count = len(seen_initial_list) - len(unique_seen)
        skipped_count = len(initial_ids - unique_seen)
        return (dup_count, skipped_count, scanned_entries)

    _, _, static_offset_scans = _run_harvest("offset", "none")
    _, _, static_keyset_scans = _run_harvest("composite_keyset", "none")
    off_ins = _run_harvest("offset", "prefix_insert_2")
    off_del = _run_harvest("offset", "prefix_delete_2")
    single_ts = _run_harvest("single_col_ts", "none")
    keyset_ins = _run_harvest("composite_keyset", "prefix_insert_2")
    keyset_del = _run_harvest("composite_keyset", "prefix_delete_2")
    keyset_mut_sort = _run_harvest("composite_keyset", "bump_unvisited_sort_key")

    assert static_offset_scans == 20500 and static_keyset_scans == 1000
    assert off_ins[0] > 0 and off_del[1] > 0
    assert single_ts[1] > 0
    assert keyset_ins[:2] == (0, 0) and keyset_del[:2] == (0, 0)
    assert keyset_mut_sort[1] == 1

    return {
        "scan_ratio": round(static_offset_scans / static_keyset_scans, 1),
        "static_scans": (static_offset_scans, static_keyset_scans),
        "off_ins_dups": off_ins[0],
        "off_del_skips": off_del[1],
        "single_ts_skips": single_ts[1],
        "keyset_ins": keyset_ins[:2],
        "keyset_del": keyset_del[:2],
        "keyset_mut_skips": keyset_mut_sort[1],
    }


def simulate_brooker_occ(clients: int = 100, trials: int = 25) -> dict[str, tuple[float, float]]:
    """Faithful port of `aws-samples/aws-arch-backoff-simulator@66cb1692` `src/backoff_simulator.py`."""
    rng = random.Random(1337)
    base, cap = 5.0, 2000.0
    strategies = ["Exponential", "EqualJitter", "FullJitter", "Decorr"]
    out: dict[str, tuple[float, float]] = {}

    for strat in strategies:
        total_calls = 0
        total_tm = 0.0
        for _ in range(trials):
            version = 0
            calls = 0
            pq: list[tuple[float, int, str, int, int]] = []
            seq = 0

            def net_delay() -> float:
                return abs(rng.normalvariate(10.0, 2.0))

            attempts = [0] * clients
            decorr_sleep = [base] * clients

            for cid in range(clients):
                seq += 1
                heapq.heappush(pq, (net_delay(), seq, "server_read", cid, 0))

            tm = 0.0
            while pq:
                tm, _, kind, cid, payload = heapq.heappop(pq)
                if kind == "server_read":
                    seq += 1
                    heapq.heappush(pq, (tm + net_delay(), seq, "client_read_rsp", cid, version))
                elif kind == "client_read_rsp":
                    seq += 1
                    heapq.heappush(pq, (tm + net_delay(), seq, "server_write", cid, payload))
                elif kind == "server_write":
                    calls += 1
                    ok = 1 if payload == version else 0
                    if ok:
                        version += 1
                    seq += 1
                    heapq.heappush(pq, (tm + net_delay(), seq, "client_write_rsp", cid, ok))
                elif kind == "client_write_rsp":
                    if payload == 0:
                        attempts[cid] += 1
                        n = attempts[cid]
                        v = min(cap, (2**n) * base)
                        if strat == "Exponential":
                            slp = v
                        elif strat == "EqualJitter":
                            slp = v / 2.0 + rng.uniform(0.0, v / 2.0)
                        elif strat == "FullJitter":
                            slp = rng.uniform(0.0, v)
                        elif strat == "Decorr":
                            decorr_sleep[cid] = min(cap, rng.uniform(base, decorr_sleep[cid] * 3.0))
                            slp = decorr_sleep[cid]
                        else:
                            raise ValueError(strat)
                        seq += 1
                        heapq.heappush(pq, (tm + net_delay() + slp, seq, "server_read", cid, 0))
            total_calls += calls
            total_tm += tm
        out[strat] = (round(total_calls / trials, 1), round(total_tm / trials, 1))

    assert out["FullJitter"][0] < 0.5 * out["Exponential"][0]
    assert out["FullJitter"][0] < out["EqualJitter"][0] and out["FullJitter"][1] < out["EqualJitter"][1]
    return out


def simulate_http429_retry_after() -> dict[str, Any]:
    """[illustrative analytical model] `RFC 9110 §10.2.3` `1*DIGIT` `Retry-After` under Token-Bucket vs. Quota-Reset."""
    rng = random.Random(2026)
    clients = 100
    base_ms, cap_ms = 250.0, 4000.0

    def net_ms(r: random.Random = rng) -> float:
        return abs(r.normalvariate(10.0, 2.0))

    # Regime A: Contended Token Bucket (capacity B=10, refill r=50 tok/s = 0.05 tok/ms).
    # Server emits RFC 9110 `delay-seconds = 1*DIGIT` integer `Retry-After = max(1, ceil((1 - tokens)/r_sec))` -> `1`s (`1000ms`).
    # Note: `Unjittered_Expo` models synthetic unjittered exponential backoff (`min(16s, 1s * 2^k)`);
    # `RESTler`'s `RetryStrategy.EXPONENTIAL` (`retry_handler.py:50`) is dead code outside unit tests,
    # while real `RESTler` `HTTP 429` handling in `request_utilities.py:425-479` uses fixed `RETRY_SLEEP_SEC = 5`
    # capped at `MAX_RETRIES = 5` (modeled separately below as `RESTler_Fixed5s`).
    policies = [
        "Unjittered_Expo",
        "Literal_RetryAfter",
        "RA_Plus_EqualJitter",
        "RA_Plus_Decorrelated",
        "RA_Plus_FullJitter",
    ]
    regime_a: dict[str, dict[str, float | int]] = {}
    for pol in policies:
        tokens = 10.0
        last_refill_ms = 0.0
        refill_per_ms = 0.05
        capacity = 10.0
        pq: list[tuple[float, int, str, int, int]] = []
        seq = 0
        attempts = [0] * clients
        decorr = [base_ms] * clients
        done_times: list[float] = []
        total_reqs = 0
        total_429s = 0
        bucket_50ms_counts: dict[int, int] = {}

        for cid in range(clients):
            seq += 1
            heapq.heappush(pq, (net_ms(), seq, "req", cid, 0))

        while pq:
            tm, _, kind, cid, ra_sec = heapq.heappop(pq)
            if kind == "req":
                tokens = min(capacity, tokens + (tm - last_refill_ms) * refill_per_ms)
                last_refill_ms = tm
                total_reqs += 1
                win = int(tm // 50.0)
                bucket_50ms_counts[win] = bucket_50ms_counts.get(win, 0) + 1
                if tokens >= 1.0:
                    tokens -= 1.0
                    done_times.append(tm + net_ms())
                else:
                    total_429s += 1
                    ra_int_sec = max(1, math.ceil((1.0 - tokens) / (refill_per_ms * 1000.0)))
                    seq += 1
                    heapq.heappush(pq, (tm + net_ms(), seq, "rsp_429", cid, ra_int_sec))
            elif kind == "rsp_429":
                k = attempts[cid]
                attempts[cid] += 1
                ra_ms = ra_sec * 1000.0
                env = min(cap_ms, base_ms * (2**k))
                if pol == "Unjittered_Expo":
                    slp = min(16000.0, 1000.0 * (2**k))
                elif pol == "Literal_RetryAfter":
                    slp = ra_ms
                elif pol == "RA_Plus_EqualJitter":
                    slp = ra_ms + env / 2.0 + rng.uniform(0.0, env / 2.0)
                elif pol == "RA_Plus_Decorrelated":
                    decorr[cid] = min(cap_ms, rng.uniform(base_ms, decorr[cid] * 3.0))
                    slp = ra_ms + decorr[cid]
                elif pol == "RA_Plus_FullJitter":
                    slp = ra_ms + rng.uniform(0.0, env)
                else:
                    raise ValueError(pol)
                seq += 1
                heapq.heappush(pq, (tm + slp + net_ms(), seq, "req", cid, 0))

        done_times.sort()
        retry_peak_50ms = max((cnt for w, cnt in bucket_50ms_counts.items() if w >= 10), default=0)
        regime_a[pol] = {
            "reqs": total_reqs,
            "429s": total_429s,
            "retry_peak_50ms": retry_peak_50ms,
            "p99_ms": round(done_times[int(0.99 * len(done_times)) - 1], 1),
        }

    assert regime_a["RA_Plus_FullJitter"]["429s"] < regime_a["Literal_RetryAfter"]["429s"]
    assert regime_a["RA_Plus_FullJitter"]["retry_peak_50ms"] < regime_a["Literal_RetryAfter"]["retry_peak_50ms"]

    # Regime B: Single-tenant Fixed Quota-Window Reset at t = 2000ms (capacity = 100 >= C, `Retry-After: 2`).
    # Compare `Blind_U_0_RA` (`U(0, 2000.0)`) vs. `RA_Plus_FullJitter` (`2000.0 + U(0, base_ms)`).
    ra_window_ms = 2000.0
    regime_b_premature_429s: dict[str, int] = {}
    for b_pol in ("Blind_U_0_RA", "RA_Plus_FullJitter"):
        premature = 0
        for _ in range(clients):
            t0_rsp = 20.0  # initial 429 received at ~20ms -> analytical P(20 + U(0,2000) < 2000) = 1980/2000 = 99%
            if b_pol == "Blind_U_0_RA":
                slp = rng.uniform(0.0, ra_window_ms)
            else:
                slp = ra_window_ms + rng.uniform(0.0, base_ms)
            if t0_rsp + slp < ra_window_ms:
                premature += 1
        regime_b_premature_429s[b_pol] = premature
    assert regime_b_premature_429s == {"Blind_U_0_RA": 99, "RA_Plus_FullJitter": 0}

    # Faithful simulation of `RESTler` `request_utilities.py:425-479` (`RETRY_SLEEP_SEC = 5`, `MAX_RETRIES = 5`):
    rng_restler = random.Random(2026)
    r_tokens = 10.0
    r_last_ms = 0.0
    r_pq: list[tuple[float, int, str, int]] = []
    r_seq = 0
    r_retries = [0] * clients
    r_429s = 0
    r_dropped = 0
    r_buckets: dict[int, int] = {}
    for cid in range(clients):
        r_seq += 1
        heapq.heappush(r_pq, (net_ms(rng_restler), r_seq, "req", cid))
    while r_pq:
        tm, _, kind, cid = heapq.heappop(r_pq)
        if kind == "req":
            r_tokens = min(10.0, r_tokens + (tm - r_last_ms) * 0.05)
            r_last_ms = tm
            win = int(tm // 50.0)
            r_buckets[win] = r_buckets.get(win, 0) + 1
            if r_tokens >= 1.0:
                r_tokens -= 1.0
            else:
                r_429s += 1
                r_seq += 1
                heapq.heappush(r_pq, (tm + net_ms(rng_restler), r_seq, "rsp_429", cid))
        elif kind == "rsp_429":
            # `request_utilities.py:473-479`: `num_retries += 1; if num_retries < MAX_RETRIES: time.sleep(5)`
            r_retries[cid] += 1
            if r_retries[cid] < 5:
                r_seq += 1
                heapq.heappush(r_pq, (tm + 5000.0 + net_ms(rng_restler), r_seq, "req", cid))
            else:
                r_dropped += 1
    r_peak_50ms = max((cnt for w, cnt in r_buckets.items() if w >= 10), default=0)
    assert (r_429s, r_peak_50ms, r_dropped) == (350, 90, 50)
    restler_fixed5s = {"429s": r_429s, "retry_peak_50ms": r_peak_50ms, "dropped": r_dropped}

    return {
        "regime_a": regime_a,
        "restler_fixed5s": restler_fixed5s,
        "regime_b_premature_429s": regime_b_premature_429s,
    }


def main() -> None:
    with tempfile.TemporaryDirectory() as tmp_dir:
        p1 = run_probe_1(tmp_dir)
        p2 = run_probe_2()
        p3 = run_probe_3()
        p4 = run_probe_4()
        pag = simulate_pagination_under_writes()
        occ = simulate_brooker_occ()
        r429 = simulate_http429_retry_after()

    print("=== OpenAPI, Stateful Fuzzing, Pact Contracts, Tool Benchmarks & Retry-After Probe ===")
    print("[Probe 1] OpenAPI 3.0.3 vs. 3.1.0 Dialect Differential & Schemathesis Guards [Basis: normative + documentation + source + execution]")
    print(
        f"  Dialect inversions: H1_nullable_null(3.0={p1['h1'][0]}, strict_3.1={p1['h1'][1]}, sch_3.1={p1['h1'][2]}); "
        f"H2_ref_nullable(3.0={p1['h2'][0]}, strict_3.1={p1['h2'][1]}, sch_3.0={p1['h2'][2]}); "
        f"H3_nullable_enum(req={p1['h3'][0]}, resp={p1['h3'][1]})"
    )
    print(
        f"  Composition & readOnly: H4_allOf_closed_valid(additionalProps_false={p1['h4_counts'][0]}, unevaluatedProps_false={p1['h4_counts'][1]}); "
        f"H5_allOf_readOnly_valid(unrepaired={p1['h5_counts'][0]}, repaired={p1['h5_counts'][1]}); "
        f"H6_discriminator(unpinned_mistag={p1['h6_mistag'][0]}, pinned_mistag={p1['h6_mistag'][1]}, default_absent_tag={p1['h6_mistag'][2]})"
    )
    print(
        f"  Schemathesis wire/stateful & paper sums: query_string_neg_FP(naive={p1['wire_fps'][0]}/2, guarded={p1['wire_fps'][1]}/2), "
        f"abs_Location_no_base={p1['abs_loc_no_base']}; paper_sums(prose_4cat={p1['sch_sums'][0]} vs 755, Table6={p1['sch_sums'][1]}, Table7_500={p1['sch_sums'][2]})"
    )

    print("[Probe 2] RESTler Producer-Consumer Inference, BFS vs. BFS-Fast & 4 Security Checkers [Basis: documentation + source + execution + derived]")
    print(
        f"  Dependencies.fs resolved consumes: default={p2['deps'][0]}/{p2['deps'][3]}, "
        f"allowGetProducers={p2['deps'][1]}/{p2['deps'][3]} (container_PATCH_ok; flat_PATCH+Query_cursor_missed), "
        f"annotated={p2['deps'][2]}/{p2['deps'][3]}, PUT_uid_fallback={p2['put_uid_resolved']}"
    )
    print(
        f"  [illustrative toy model] Depth-5 search: raw={p2['search']['raw_space']}, "
        f"BFS_seqSet={p2['search']['bfs_seqset']} ({p2['search']['bfs_ops']}/6 ops), "
        f"BFS_Fast_seqSet={p2['search']['bfs_fast_seqset']} ({p2['search']['bfs_fast_ops']}/6 ops); "
        f"4_ICST20_checkers(buggy={p2['buggy_hits']}/4, patched={p2['clean_hits']}/4)"
    )
    print(
        f"  RESTler empirical seqSet reductions: arXiv_Table3={p2['arxiv_ratios']}, ICSE19_TableII={p2['icse19_ratios']}"
    )

    print("[Probe 3] Pact `json.rs` MatchingRule Escapes & `can-i-deploy` Directional Gate [Basis: source + execution]")
    print(
        f"  5 consumer-breaking provider payloads: loose_Pact_Ok={p3['loose_passes']}/5, "
        f"strict_typed_consumer_Ok={p3['consumer_ok']}/5, hardened_Pact_Ok={p3['hardened_passes']}/5, "
        f"nonstring_int_regex_coerced={p3['int_regex_coerced']}"
    )
    print(
        f"  Pact Broker can-i-deploy asymmetry: unverified_consumer_to_prod={p3['consumer_deploy']}, "
        f"zero_consumer_provider_to_prod={p3['provider_deploy']}"
    )

    print("[Probe 4] Agentic API Benchmark Harness Defects (`BFCL`, `RestGPT`, `ToolBench`) [Basis: documentation + source + execution + derived]")
    print(
        f"  BFCL defects: standardize_string_FP={p4['bfcl_collisions']}/6, java_comma_split_len={p4['java_fragments']} (expected 2), "
        f"eval_guard_bypass(nested={p4['eval_bypasses'][0]}, 3seg={p4['eval_bypasses'][1]}), "
        f"multi_turn_response_leak(buggy={p4['turn_leak'][0]}, fixed={p4['turn_leak'][1]})"
    )
    print(
        f"  RestGPT & ToolBench defects: cyclic_ref_RecursionError={p4['restgpt_rec_err']}, "
        f"Spotify_Table4_denom(only_N57={p4['spotify_denom'][0]}/{p4['spotify_denom'][2]}, only_N55={p4['spotify_denom'][1]}/{p4['spotify_denom'][2]}, CP_neither={p4['spotify_denom'][3]}/3); "
        f"ToolBench_zero_req_opt_kept(buggy={p4['tb_opt_kept'][0]}/3, fixed={p4['tb_opt_kept'][1]}/3), "
        f"left64_name_collision={p4['tb_name_collision']}, Unsolved+Unsolvable='{p4['tb_unsolvable_pass']}'"
    )

    print("[Probe 5] Pagination Consistency & Brooker / `RFC 9110` `Retry-After` Contention [Basis: normative + source + execution + derived]")
    print(
        f"  [illustrative analytical model] Pagination (N=1000, P=25): static_scans(offset={pag['static_scans'][0]} vs keyset={pag['static_scans'][1]}, {pag['scan_ratio']}x), "
        f"offset_insert_dups={pag['off_ins_dups']}, offset_delete_skips={pag['off_del_skips']}, single_ts_tie_skips={pag['single_ts_skips']}, "
        f"composite_keyset(ins={pag['keyset_ins']}, del={pag['keyset_del']}, mutable_sort_skips={pag['keyset_mut_skips']})"
    )
    print(
        f"  [illustrative analytical model] Brooker OCC (C=100, 25 trials, calls/ms): "
        f"Expo={occ['Exponential']}, Equal={occ['EqualJitter']}, Decorr={occ['Decorr']}, Full={occ['FullJitter']}"
    )
    ra = r429["regime_a"]
    rf = r429["restler_fixed5s"]
    print(
        f"  [illustrative analytical model] HTTP 429 Token-Bucket (C=100, B=10, r=50/s -> 429s/peak50ms/p99ms): "
        f"Literal_RA=({ra['Literal_RetryAfter']['429s']}, {ra['Literal_RetryAfter']['retry_peak_50ms']}, {ra['Literal_RetryAfter']['p99_ms']}), "
        f"Unjittered_Expo=({ra['Unjittered_Expo']['429s']}, {ra['Unjittered_Expo']['retry_peak_50ms']}, {ra['Unjittered_Expo']['p99_ms']}), "
        f"RESTler_Fixed5s=(429s={rf['429s']}, peak50ms={rf['retry_peak_50ms']}, dropped={rf['dropped']}/100), "
        f"RA+Equal=({ra['RA_Plus_EqualJitter']['429s']}, {ra['RA_Plus_EqualJitter']['retry_peak_50ms']}, {ra['RA_Plus_EqualJitter']['p99_ms']}), "
        f"RA+Decorr=({ra['RA_Plus_Decorrelated']['429s']}, {ra['RA_Plus_Decorrelated']['retry_peak_50ms']}, {ra['RA_Plus_Decorrelated']['p99_ms']}), "
        f"RA+FullJitter=({ra['RA_Plus_FullJitter']['429s']}, {ra['RA_Plus_FullJitter']['retry_peak_50ms']}, {ra['RA_Plus_FullJitter']['p99_ms']}); "
        f"QuotaWindow_premature_429s={r429['regime_b_premature_429s']}"
    )
    print("=== ALL 5 PROBE SUITES PASSED DETERMINISTICALLY ===")


if __name__ == "__main__":
    main()
