#!/usr/bin/env python3
"""Validate the common report-agent authority packet as a strict neutral projection."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
PROPOSITIONS = HERE / "propositions.json"
LOCATORS = HERE / "quotation-locators.json"
PACKET = HERE / "agent-visible" / "common.json"
TOP_KEYS = {"schema", "title", "records"}
RECORD_KEYS = {"version", "url", "exact_excerpt"}
URL_VERSION = re.compile(r"^https://doc\.rust-lang\.org/([0-9]+\.[0-9]+\.[0-9]+)/")


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def quotations(entry: dict[str, Any]) -> list[str]:
    if "quotation" in entry:
        if "quotations" in entry:
            raise AssertionError(f"mixed quotation forms in {entry.get('id')}")
        values = [entry["quotation"]]
    else:
        values = entry.get("quotations")
    if not isinstance(values, list) or not values or not all(
        isinstance(value, str) and value for value in values
    ):
        raise AssertionError(f"invalid exact quotation set in {entry.get('id')}")
    return values


def expected_packet(
    propositions: dict[str, Any], locators: dict[str, Any]
) -> dict[str, Any]:
    entries = {entry["id"]: entry for entry in propositions.get("entries", [])}
    if set(locators) != {"schema_version", "status", "records"}:
        raise AssertionError("quotation locator map has unexpected top-level fields")
    if locators["schema_version"] != 1 or locators["status"] != "DRAFT":
        raise AssertionError("quotation locator map is not schema-v1 DRAFT")
    expected_pairs = {
        (entry["id"], excerpt)
        for entry in entries.values()
        if entry.get("kind") == "RUST"
        for excerpt in quotations(entry)
    }
    observed_pairs: set[tuple[str, str]] = set()
    neutral: dict[tuple[str, str, str], dict[str, Any]] = {}
    for locator in locators["records"]:
        if set(locator) != {"authority_id", "exact_excerpt", "urls"}:
            raise AssertionError("quotation locator record has unexpected fields")
        authority_id = locator["authority_id"]
        entry = entries.get(authority_id)
        excerpt = locator["exact_excerpt"]
        pair = (authority_id, excerpt)
        if entry is None or entry.get("kind") != "RUST" or pair not in expected_pairs:
            raise AssertionError(f"invalid quotation locator pair: {pair!r}")
        if pair in observed_pairs:
            raise AssertionError(f"duplicate quotation locator pair: {pair!r}")
        observed_pairs.add(pair)
        urls = locator["urls"]
        if not isinstance(urls, list) or not urls or urls != sorted(set(urls)):
            raise AssertionError(f"invalid quotation locator URLs for {pair!r}")
        if not set(urls).issubset(set(entry["urls"])):
            raise AssertionError(f"quotation locator escapes authority source set: {pair!r}")
        for url in urls:
            match = URL_VERSION.match(url)
            if match is None or match.group(1) not in entry["versions"]:
                raise AssertionError(f"quotation locator URL/version mismatch: {url}")
            key = (match.group(1), url, excerpt)
            neutral[key] = {
                "version": match.group(1),
                "url": url,
                "exact_excerpt": excerpt,
            }
    if observed_pairs != expected_pairs:
        missing = sorted(expected_pairs - observed_pairs)
        extra = sorted(observed_pairs - expected_pairs)
        raise AssertionError(f"quotation locator coverage mismatch: missing={missing}, extra={extra}")
    records = [neutral[key] for key in sorted(neutral)]
    for index, record in enumerate(records):
        record_ordered = {
            "version": record["version"],
            "url": record["url"],
            "exact_excerpt": record["exact_excerpt"],
        }
        records[index] = record_ordered
    return {
        "schema": "rust-documentation-excerpts-v1",
        "title": "Rust documentation excerpts",
        "records": records,
    }


def validate() -> str:
    propositions = read_json(PROPOSITIONS)
    locators = read_json(LOCATORS)
    packet = read_json(PACKET)
    if set(packet) != TOP_KEYS:
        raise AssertionError("agent-visible packet has unexpected top-level fields")
    if packet != expected_packet(propositions, locators):
        raise AssertionError(
            "agent-visible packet is not the exact sorted, deduplicated Rust-only projection"
        )
    for record in packet["records"]:
        if set(record) != RECORD_KEYS:
            raise AssertionError("agent-visible authority record has unexpected fields")
        match = URL_VERSION.match(record["url"])
        if match is None or match.group(1) != record["version"]:
            raise AssertionError(f"URL/version mismatch: {record['url']}")
    raw = PACKET.read_bytes()
    return hashlib.sha256(raw).hexdigest()


if __name__ == "__main__":
    digest = validate()
    print(f"agent-visible authority projection valid: sha256={digest}")
