#!/usr/bin/env python3
"""Validate closed references in the evaluator-only V5 oracle materials."""

from __future__ import annotations

import hashlib
import html.parser
import json
import urllib.request
from pathlib import Path
from urllib.parse import urlsplit, urlunsplit


FREEZE = Path(__file__).resolve().parent
MODES = ("E", "V", "F", "P", "B", "L", "R", "Q")
EXPECTED_COUNTS = {"E": 15, "V": 11, "F": 11, "P": 29, "B": 13, "L": 11, "R": 12, "Q": 13}
EXPECTED_ALLOWLIST_EXTRAS = {
    "B": {
        "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#life-cycle-of-a-build-script",
        "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#outputs-of-the-build-script",
        "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rerun-if-env-changed",
        "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rustc-cfg",
        "https://doc.rust-lang.org/1.85.1/cargo/reference/features.html",
    }
}
EXPECTED_B_CARGO_PAGE_SHA256 = {
    "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#life-cycle-of-a-build-script": "1247cbaf8ce775f17349367d13ac4eecc6d9cfa343310f12d8c1deccd19e07b2",
    "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#outputs-of-the-build-script": "1247cbaf8ce775f17349367d13ac4eecc6d9cfa343310f12d8c1deccd19e07b2",
    "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rerun-if-env-changed": "1247cbaf8ce775f17349367d13ac4eecc6d9cfa343310f12d8c1deccd19e07b2",
    "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rustc-cfg": "1247cbaf8ce775f17349367d13ac4eecc6d9cfa343310f12d8c1deccd19e07b2",
    "https://doc.rust-lang.org/1.85.1/cargo/reference/features.html": "96b2337cd60180df5a8566f343e52938dfcaa369bf12e1e82723a2326f64cb25",
}
EXACT_QUOTATION_EVIDENCE_ALGORITHM = "V5_EXACT_QUOTATION_EVIDENCE_V1"
EXPECTED_EXACT_QUOTATION_EVIDENCE_SHA256 = (
    "a3aff9b35d747b8dc12c90d8484f37d531447122ec186509ca62baa5e360bcaa"
)
QUOTATION_MATCH_ALGORITHM = (
    "Decode HTML character references with the HTML parser. For a URL with a "
    "fragment, require exactly one matching element and scope h1-h6 through the "
    "next heading of equal or higher rank, a rustdoc item to its containing "
    "details element, a regular item to its containing section element, or "
    "otherwise the identified element itself. For a fragmentless citation, "
    "scope only the exact content-addressed page and make no subsection claim. "
    "Within one p, li, td, dd, pre, tr, or h1-h6 semantic element, insert one "
    "ASCII space at block and table-cell DOM boundaries, map curly quotation "
    "marks to ASCII, remove Markdown backticks, collapse whitespace runs to one "
    "ASCII space, trim, and require a nonempty exact character sequence; never "
    "concatenate distinct semantic elements."
)
EXPECTED_VERSIONED_PAGE_BYTE_LINEAGE_ENVELOPE = {
    "status": "PAGE_BYTES_BOUND_TO_FROZEN_V4_MANIFEST",
    "scope": ["B Rust/Cargo 1.85.1", "P Rust 1.84.0, 1.85.0, and 1.86.0"],
    "local_refetch_performed": False,
    "coverage_basis": (
        "The frozen V4 authority manifest binds each cited versioned official "
        "page's bytes; current V5 locators may use corrected fragments on those "
        "same content-addressed pages. This is page-byte and historical lineage "
        "only: it does not claim that V4 reviewed the current V5 quotations, "
        "propositions, locators, or fragment scopes. Those current materials "
        "remain pending until the required V5 source-review receipts exist."
    ),
    "freeze_root": "evals/unsafe-rust/runs/2026-08-01-v4-focused/freeze",
    "authority_manifest_sha256": (
        "48444682cfc13966ce2769add9d4fbde82426a7a6e8777c421be8b26d15ff293"
    ),
    "file_manifest_sha256": (
        "059cde170e6e31d4ef4c4997b4a64413fdd9e47e9f9e5df74c1c9707bf6e3c58"
    ),
    "lock_sha256": (
        "cd7a300f83b045f76530eded20ec2d22bd6abbd484d6459ff50245fb07ef943e"
    ),
    "rubric_sha256": {
        "B": "13790584d0e5ede69cff8c2b1889be80c73df0722c4ea709c0e85ab82900a4bb",
        "P": "1e9e6622a34b3b0376b6912f676695e318edcd971ac1f4960810531ad854911d",
    },
    "lock_declared_file_manifest_sha256": (
        "059cde170e6e31d4ef4c4997b4a64413fdd9e47e9f9e5df74c1c9707bf6e3c58"
    ),
    "review_signoffs": [
        "v4-oracle-final-review: PASS/FREEZE",
        "v4-oracle-review-2: PASS/FREEZE",
    ],
}
ATOM_KEYS = {"id", "direct_criterion", "prerequisites", "authority_dependencies", "applicability"}


def load_json(path: Path) -> object:
    try:
        text = path.read_bytes().decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"{path}: not strict UTF-8") from error

    def reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"{path}: duplicate JSON object key: {key!r}")
            result[key] = value
        return result

    def reject_nonfinite_number(token: str) -> object:
        raise ValueError(f"{path}: non-finite JSON number: {token}")

    return json.loads(
        text,
        object_pairs_hook=reject_duplicate_keys,
        parse_constant=reject_nonfinite_number,
    )


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def exact_quotations(entry: dict[str, object]) -> list[str]:
    if "quotation" in entry:
        values = [entry["quotation"]]
    else:
        values = entry.get("quotations")
    require(
        isinstance(values, list) and values and all(isinstance(value, str) and value for value in values),
        f"{entry.get('id')}: invalid exact quotation set",
    )
    return values


def records_by_id(records: object, label: str) -> dict[str, dict[str, object]]:
    require(isinstance(records, list), f"{label}: entries must be an array")
    result: dict[str, dict[str, object]] = {}
    for record in records:
        require(isinstance(record, dict), f"{label}: entry must be an object")
        record_id = record.get("id")
        require(isinstance(record_id, str) and record_id not in result, f"{label}: duplicate/invalid id {record_id!r}")
        result[record_id] = record
    return result


def canonical_json_bytes(value: object) -> bytes:
    return (
        json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def exact_quotation_evidence_digest(
    freeze_root: Path,
    *,
    expected_status: str,
    local_pages: list[object],
    reused_pages: list[object],
) -> str:
    """Bind every exact excerpt to the reviewed bytes of every cited page.

    This does not read ambient rustup documentation.  Independent source
    reviewers must obtain each page, verify its bytes against ``page_sha256``,
    apply the frozen normalization algorithm, and check the exact excerpt.
    The deterministic digest makes that complete evidence set an exact review
    contract input and detects punctuation drift in any proposition/locator.
    """

    locators = load_json(freeze_root / "authority" / "quotation-locators.json")
    require(isinstance(locators, dict), "quotation locators must be an object")
    require(
        set(locators) == {"schema_version", "status", "records"}
        and locators["schema_version"] == 1
        and locators["status"] == expected_status,
        "quotation locator lifecycle envelope is not exact",
    )
    page_sha256: dict[str, str] = {}
    for raw in local_pages:
        require(isinstance(raw, dict), "local quotation page must be an object")
        digest_value = raw.get("page_sha256")
        urls = raw.get("requested_urls")
        require(
            isinstance(digest_value, str)
            and len(digest_value) == 64
            and isinstance(urls, list),
            "local quotation page binding is invalid",
        )
        for url in urls:
            require(
                isinstance(url, str) and url not in page_sha256,
                f"duplicate/invalid quotation page URL: {url!r}",
            )
            page_sha256[url] = digest_value
    for raw in reused_pages:
        require(isinstance(raw, dict), "reused quotation page must be an object")
        url = raw.get("requested_url")
        digest_value = raw.get("page_sha256")
        require(
            isinstance(url, str)
            and url not in page_sha256
            and isinstance(digest_value, str)
            and len(digest_value) == 64,
            f"duplicate/invalid reused quotation page URL: {url!r}",
        )
        page_sha256[url] = digest_value

    evidence: list[dict[str, object]] = []
    records = locators["records"]
    require(isinstance(records, list), "quotation locator records must be an array")
    for raw in records:
        require(isinstance(raw, dict), "quotation locator record must be an object")
        require(
            set(raw) == {"authority_id", "exact_excerpt", "urls"},
            "quotation locator record fields are not exact",
        )
        urls = raw["urls"]
        require(
            isinstance(raw["authority_id"], str)
            and isinstance(raw["exact_excerpt"], str)
            and isinstance(urls, list)
            and urls,
            "quotation locator record is invalid",
        )
        sources: list[dict[str, str]] = []
        for url in urls:
            require(
                isinstance(url, str) and url in page_sha256,
                f"quotation locator has no frozen page-byte binding: {url!r}",
            )
            sources.append({"url": url, "page_sha256": page_sha256[url]})
        evidence.append(
            {
                "authority_id": raw["authority_id"],
                "exact_excerpt": raw["exact_excerpt"],
                "sources": sources,
            }
        )
    evidence.sort(key=lambda item: (item["authority_id"], item["exact_excerpt"]))
    binding = {
        "schema_version": 1,
        "algorithm": EXACT_QUOTATION_EVIDENCE_ALGORITHM,
        "records": evidence,
    }
    digest_value = hashlib.sha256(
        EXACT_QUOTATION_EVIDENCE_ALGORITHM.encode("ascii")
        + b"\0"
        + canonical_json_bytes(binding)
    ).hexdigest()
    require(
        digest_value == EXPECTED_EXACT_QUOTATION_EVIDENCE_SHA256,
        "exact quotation/page-byte evidence digest drifted",
    )
    return digest_value


class SemanticElementParser(html.parser.HTMLParser):
    ELEMENTS = {
        "p",
        "li",
        "td",
        "dd",
        "pre",
        "tr",
        "h1",
        "h2",
        "h3",
        "h4",
        "h5",
        "h6",
    }
    STRUCTURAL = ELEMENTS | {"section", "details"}
    TEXT_BOUNDARIES = {
        "br",
        "dd",
        "details",
        "div",
        "li",
        "p",
        "pre",
        "section",
        "td",
        "th",
        "tr",
    }

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self._event = 0
        self._active_nodes: list[dict[str, object]] = []
        self._active_semantic: list[dict[str, object]] = []
        self.elements: list[dict[str, object]] = []
        self.nodes_by_id: dict[str, dict[str, object]] = {}
        self.headings: list[dict[str, object]] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        self._event += 1
        if tag in self.TEXT_BOUNDARIES:
            for active in self._active_semantic:
                chunks = active["chunks"]
                assert isinstance(chunks, list)
                chunks.append(" ")
        element_id = next(
            (value for name, value in attrs if name == "id" and value), None
        )
        if element_id is not None and element_id in self.nodes_by_id:
            raise ValueError(f"duplicate rustdoc element id: {element_id}")
        if tag not in self.STRUCTURAL and element_id is None:
            return
        node: dict[str, object] = {
            "tag": tag,
            "start": self._event,
            "end": None,
            "parent": self._active_nodes[-1] if self._active_nodes else None,
            "chunks": [],
        }
        self._active_nodes.append(node)
        if element_id is not None:
            self.nodes_by_id[element_id] = node
        if tag in self.ELEMENTS:
            self._active_semantic.append(node)
        if tag in {"h1", "h2", "h3", "h4", "h5", "h6"}:
            self.headings.append(node)

    def handle_data(self, data: str) -> None:
        for node in self._active_semantic:
            chunks = node["chunks"]
            assert isinstance(chunks, list)
            chunks.append(data)

    def handle_endtag(self, tag: str) -> None:
        self._event += 1
        for index in range(len(self._active_nodes) - 1, -1, -1):
            node = self._active_nodes[index]
            if node["tag"] != tag:
                continue
            node["end"] = self._event
            del self._active_nodes[index]
            if node in self._active_semantic:
                self._active_semantic.remove(node)
                chunks = node["chunks"]
                assert isinstance(chunks, list)
                self.elements.append(
                    {
                        "text": normalized_exact_quotation("".join(chunks)),
                        "start": node["start"],
                        "end": node["end"],
                    }
                )
            break
        if tag in self.TEXT_BOUNDARIES:
            for active in self._active_semantic:
                chunks = active["chunks"]
                assert isinstance(chunks, list)
                chunks.append(" ")

    def section_scope(self, fragment: str) -> tuple[int, int]:
        try:
            node = self.nodes_by_id[fragment]
        except KeyError as error:
            raise ValueError(f"rustdoc URL fragment is absent: {fragment}") from error
        start = node["start"]
        tag = node["tag"]
        assert isinstance(start, int) and isinstance(tag, str)
        if tag in {"h1", "h2", "h3", "h4", "h5", "h6"}:
            level = int(tag[1])
            scope_end = min(
                (
                    int(heading["start"])
                    for heading in self.headings
                    if isinstance(heading["start"], int)
                    and heading["start"] > start
                    and int(str(heading["tag"])[1]) <= level
                ),
                default=self._event + 1,
            )
            return start, scope_end

        lineage: list[dict[str, object]] = []
        current: dict[str, object] | None = node
        while current is not None:
            lineage.append(current)
            parent = current["parent"]
            current = parent if isinstance(parent, dict) else None
        scoped = next(
            (candidate for candidate in lineage if candidate["tag"] == "details"),
            None,
        ) or next(
            (candidate for candidate in lineage if candidate["tag"] == "section"),
            node,
        )
        scope_start = scoped["start"]
        scope_end = scoped["end"]
        if not isinstance(scope_start, int) or not isinstance(scope_end, int):
            raise ValueError(f"rustdoc fragment has no closed section scope: {fragment}")
        return scope_start, scope_end


def normalized_exact_quotation(value: str) -> str:
    value = value.translate(
        str.maketrans({"‘": "'", "’": "'", "“": '"', "”": '"'})
    )
    value = value.replace("`", "")
    return " ".join(value.split())


def _scope_contains_exact_excerpt(
    parser: SemanticElementParser, fragment: str, excerpt: str
) -> bool:
    normalized = normalized_exact_quotation(excerpt)
    require(normalized != "", "exact quotation normalizes to the empty string")
    scope_start, scope_end = parser.section_scope(fragment)
    return any(
        normalized in str(element["text"])
        and isinstance(element["start"], int)
        and scope_start <= element["start"] < scope_end
        for element in parser.elements
    )


def validate_section_scoped_quotation_matcher() -> None:
    """Exercise the load-bearing fragment and semantic-element boundaries."""

    parser = SemanticElementParser()
    parser.feed(
        """
        <h2 id="wrong-section">Wrong section</h2>
        <p>The unrelated premise.</p>
        <h2 id="right-section">Right section</h2>
        <p>The exact premise, including punctuation.</p>
        <h3 id="child-section">Child section</h3>
        <p>The child premise.</p>
        <h2 id="next-section">Next section</h2>
        <p>The later premise.</p>
        <details>
          <div id="method.unwrap_unchecked">Method heading</div>
          <p>The method documentation sibling.</p>
        </details>
        <section id="comparison-operators">
          <p><code>==</code> Equal</p>
        </section>
        <section id="split-elements">
          <p>must not</p><p>concatenate</p>
        </section>
        <p id="closing-boundary">left<div>middle</div>right</p>
        """
    )
    parser.close()
    require(
        _scope_contains_exact_excerpt(
            parser, "right-section", "The exact premise, including punctuation."
        ),
        "correct heading-scoped quotation sentinel failed",
    )
    require(
        not _scope_contains_exact_excerpt(
            parser, "wrong-section", "The exact premise, including punctuation."
        ),
        "quotation matcher escaped a cited heading section",
    )
    require(
        _scope_contains_exact_excerpt(parser, "right-section", "The child premise."),
        "heading scope failed to include a lower-level child section",
    )
    require(
        not _scope_contains_exact_excerpt(parser, "right-section", "The later premise."),
        "heading scope crossed a same-level section boundary",
    )
    require(
        _scope_contains_exact_excerpt(
            parser, "method.unwrap_unchecked", "The method documentation sibling."
        ),
        "rustdoc details scope omitted a method documentation sibling",
    )
    require(
        _scope_contains_exact_excerpt(parser, "comparison-operators", "`==` Equal"),
        "comparison-operator exact quotation sentinel failed",
    )
    require(
        not _scope_contains_exact_excerpt(
            parser, "split-elements", "must not concatenate"
        ),
        "quotation matcher concatenated distinct semantic elements",
    )
    require(
        _scope_contains_exact_excerpt(
            parser, "closing-boundary", "left middle right"
        )
        and not _scope_contains_exact_excerpt(
            parser, "closing-boundary", "middle right".replace(" ", "")
        ),
        "quotation matcher erased a closing block boundary",
    )
    require(
        not _scope_contains_exact_excerpt(
            parser,
            "right-section",
            "The exact premise, includingpunctuation.",
        ),
        "quotation matcher erased a word-boundary space",
    )
    for absent in ("function-body", "integer-types", "layout-and-bit-validity"):
        try:
            parser.section_scope(absent)
        except ValueError:
            pass
        else:
            raise AssertionError("quotation matcher accepted a missing cited fragment")

    duplicate = SemanticElementParser()
    try:
        duplicate.feed('<h2 id="duplicate">one</h2><section id="duplicate">two</section>')
    except ValueError:
        pass
    else:
        raise AssertionError("quotation matcher accepted duplicate element IDs")


def verify_exact_quotations_online(
    freeze_root: Path = FREEZE,
    *,
    expected_status: str = "DRAFT",
    repository_root: Path | None = None,
    supplied_source_root: Path | None = None,
) -> str:
    """Reproduce the exact-quotation check against content-addressed rustdoc.

    Network retrieval is an explicit reviewer operation, never an ambient input
    to ordinary DRAFT or snapshot validation.  Redirects and any page-byte
    drift fail closed before excerpt matching.
    """

    validate(
        freeze_root,
        expected_status=expected_status,
        repository_root=repository_root,
        supplied_source_root=supplied_source_root,
    )
    verification = load_json(freeze_root / "authority" / "verification.json")
    locators = load_json(freeze_root / "authority" / "quotation-locators.json")
    require(isinstance(verification, dict) and isinstance(locators, dict), "invalid authority evidence")
    expected_pages: dict[str, str] = {}
    local_pages = verification["rust_1_83_local_verification"]["pages"]
    reused_pages = verification["versioned_page_byte_lineage"]["bound_pages"]
    for page in local_pages:
        for url in page["requested_urls"]:
            expected_pages[url] = page["page_sha256"]
    for page in reused_pages:
        expected_pages[page["requested_url"]] = page["page_sha256"]

    bodies: dict[str, bytes] = {}
    parsed_pages: dict[str, SemanticElementParser] = {}
    for requested_url, expected_sha256 in sorted(expected_pages.items()):
        parts = urlsplit(requested_url)
        fetch_url = urlunsplit((parts.scheme, parts.netloc, parts.path, parts.query, ""))
        if fetch_url not in bodies:
            request = urllib.request.Request(
                fetch_url,
                headers={"User-Agent": "unsafe-rust-v5-exact-quotation-review"},
            )
            with urllib.request.urlopen(request, timeout=60) as response:
                body = response.read()
                require(response.status == 200, f"rustdoc fetch status drifted: {fetch_url}")
                require(response.geturl() == fetch_url, f"rustdoc fetch redirected: {fetch_url}")
                require(
                    response.headers.get_content_type() == "text/html",
                    f"rustdoc content type drifted: {fetch_url}",
                )
            bodies[fetch_url] = body
            parser = SemanticElementParser()
            parser.feed(body.decode("utf-8", errors="strict"))
            parser.close()
            parsed_pages[fetch_url] = parser
        require(
            hashlib.sha256(bodies[fetch_url]).hexdigest() == expected_sha256,
            f"rustdoc page bytes do not match frozen SHA-256: {fetch_url}",
        )

    for locator in locators["records"]:
        excerpt = normalized_exact_quotation(locator["exact_excerpt"])
        require(excerpt != "", "exact quotation normalizes to the empty string")
        for requested_url in locator["urls"]:
            parts = urlsplit(requested_url)
            fetch_url = urlunsplit((parts.scheme, parts.netloc, parts.path, parts.query, ""))
            parser = parsed_pages[fetch_url]
            require(
                _scope_contains_exact_excerpt(parser, parts.fragment, excerpt)
                if parts.fragment
                else any(excerpt in str(element["text"]) for element in parser.elements),
                f"exact excerpt is absent from one semantic element in its cited section: "
                f"{locator['authority_id']} {requested_url}",
            )
    digest_value = exact_quotation_evidence_digest(
        freeze_root,
        expected_status=expected_status,
        local_pages=local_pages,
        reused_pages=reused_pages,
    )
    print(
        f"verified {len(locators['records'])} exact quotation records against "
        f"{len(bodies)} content-addressed official pages; evidence_sha256={digest_value}"
    )
    return digest_value


def validate(
    freeze_root: Path = FREEZE,
    *,
    expected_status: str = "DRAFT",
    repository_root: Path | None = None,
    supplied_source_root: Path | None = None,
) -> None:
    validate_section_scoped_quotation_matcher()
    require(
        repository_root is None or supplied_source_root is None,
        "choose either a repository root or a bound supplied-source root",
    )
    require(
        expected_status in {"DRAFT", "SOURCE-REVIEW-CANDIDATE", "READY"},
        "oracle expected status is unknown",
    )
    atom_by_id: dict[str, dict[str, object]] = {}
    atom_mode: dict[str, str] = {}

    for mode in MODES:
        path = freeze_root / "atoms" / f"{mode}.json"
        document = load_json(path)
        require(isinstance(document, dict), f"{path}: root must be an object")
        require(set(document) == {"schema_version", "status", "mode", "atoms"}, f"{path}: top-level fields are not exact")
        require(document["schema_version"] == 1 and document["status"] == expected_status, f"{path}: wrong schema/status")
        require(document["mode"] == mode, f"{path}: wrong mode")
        atoms = document["atoms"]
        require(isinstance(atoms, list), f"{path}: atoms must be an array")
        expected_ids = [f"{mode}{number}" for number in range(1, EXPECTED_COUNTS[mode] + 1)]
        require([atom.get("id") for atom in atoms if isinstance(atom, dict)] == expected_ids, f"{path}: atom IDs/count/order mismatch")
        for atom in atoms:
            require(isinstance(atom, dict) and set(atom) == ATOM_KEYS, f"{path}: atom fields are not exact")
            atom_id = atom["id"]
            require(atom_id not in atom_by_id, f"duplicate atom id: {atom_id}")
            require(isinstance(atom["direct_criterion"], str) and atom["direct_criterion"].strip(), f"{atom_id}: blank criterion")
            require(atom["applicability"] == "REQUIRED", f"{atom_id}: applicability must be REQUIRED")
            for field in ("prerequisites", "authority_dependencies"):
                values = atom[field]
                require(isinstance(values, list) and all(isinstance(value, str) for value in values), f"{atom_id}: invalid {field}")
                require(len(values) == len(set(values)), f"{atom_id}: duplicate {field}")
            atom_by_id[atom_id] = atom
            atom_mode[atom_id] = mode

        oracle = (freeze_root / "oracle" / f"{mode}.md").read_text(encoding="utf-8")
        marker = f"**{expected_status} / evaluator-only.**"
        require(marker in oracle, f"oracle/{mode}.md: missing exact {expected_status} / evaluator-only marker")
        for other_status in {"DRAFT", "SOURCE-REVIEW-CANDIDATE", "READY"} - {expected_status}:
            require(
                f"**{other_status} / evaluator-only.**" not in oracle,
                f"oracle/{mode}.md: contradictory lifecycle marker",
            )

    for atom_id, atom in atom_by_id.items():
        for prerequisite in atom["prerequisites"]:
            require(prerequisite in atom_by_id, f"{atom_id}: unknown prerequisite {prerequisite}")
            require(atom_mode[prerequisite] == atom_mode[atom_id], f"{atom_id}: cross-mode prerequisite {prerequisite}")
            require(prerequisite != atom_id, f"{atom_id}: self prerequisite")

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(atom_id: str) -> None:
        require(atom_id not in visiting, f"atom prerequisite cycle at {atom_id}")
        if atom_id in visited:
            return
        visiting.add(atom_id)
        for prerequisite in atom_by_id[atom_id]["prerequisites"]:
            visit(prerequisite)
        visiting.remove(atom_id)
        visited.add(atom_id)

    for atom_id in atom_by_id:
        visit(atom_id)

    authority_path = freeze_root / "authority" / "propositions.json"
    authority = load_json(authority_path)
    require(isinstance(authority, dict), f"{authority_path}: root must be an object")
    require(set(authority) == {"schema_version", "status", "purpose", "verification", "entries"}, f"{authority_path}: top-level fields are not exact")
    require(authority["schema_version"] == 1 and authority["status"] == expected_status, f"{authority_path}: wrong schema/status")
    authority_verification = authority["verification"]
    require(isinstance(authority_verification, dict), "authority proposition verification must be an object")
    expected_authority_verification = {
        "DRAFT": {
            "status": "VERIFIED_PENDING_CROSS_REVIEW",
            "ledger": "verification.json",
            "ready_for_freeze": False,
        },
        "SOURCE-REVIEW-CANDIDATE": {
            "status": "PENDING_INDEPENDENT_SOURCE_REVIEW",
            "ledger": "verification.json",
            "ready_for_freeze": False,
        },
        "READY": {
            "status": "VERIFIED",
            "ledger": "verification.json",
            "ready_for_freeze": True,
        },
    }[expected_status]
    require(authority_verification == expected_authority_verification, "authority proposition review status is not exact")
    entries: dict[str, dict[str, object]] = {}
    for entry in authority["entries"]:
        entry_id = entry.get("id")
        require(isinstance(entry_id, str) and entry_id not in entries, f"duplicate or invalid authority id: {entry_id!r}")
        urls = entry.get("urls", [])
        require(isinstance(urls, list), f"{entry_id}: urls must be an array when present")
        require(len(urls) == len(set(urls)), f"{entry_id}: duplicate urls")
        require(all(isinstance(url, str) and url.startswith("https://") for url in urls), f"{entry_id}: invalid URL")
        require(bool(urls) ^ isinstance(entry.get("source_path"), str), f"{entry_id}: needs exactly one external or supplied source form")
        require(isinstance(entry.get("consumers"), list), f"{entry_id}: consumers must be an array")
        require(len(entry["consumers"]) == len(set(entry["consumers"])), f"{entry_id}: duplicate consumers")
        require(bool(entry.get("quotation")) ^ bool(entry.get("quotations")), f"{entry_id}: needs exactly one quotation form")
        entries[entry_id] = entry

    closure_errors: list[str] = []
    for atom_id, atom in atom_by_id.items():
        for dependency in atom["authority_dependencies"]:
            if dependency not in entries:
                closure_errors.append(f"{atom_id}: unknown authority dependency {dependency}")
            elif atom_id not in entries[dependency]["consumers"]:
                closure_errors.append(f"{dependency}: missing inverse consumer {atom_id}")

    for entry_id, entry in entries.items():
        for consumer in entry["consumers"]:
            if consumer not in atom_by_id:
                closure_errors.append(f"{entry_id}: unknown consumer {consumer}")
            elif entry_id not in atom_by_id[consumer]["authority_dependencies"]:
                closure_errors.append(f"{entry_id}: stale inverse consumer {consumer}")
    require(not closure_errors, "authority/atom closure:\n" + "\n".join(closure_errors))

    extras_by_mode: dict[str, list[str]] = {}
    missing_by_mode: dict[str, list[str]] = {}
    for mode in MODES:
        allowlist_path = freeze_root / "allowlists" / f"{mode}.txt"
        urls = [line for line in allowlist_path.read_text(encoding="utf-8").splitlines() if line]
        require(len(urls) == len(set(urls)), f"{allowlist_path}: duplicate URLs")
        require(all(url.startswith("https://") for url in urls), f"{allowlist_path}: invalid URL")
        required_urls = {
            url
            for atom_id, atom in atom_by_id.items()
            if atom_mode[atom_id] == mode
            for dependency in atom["authority_dependencies"]
            for url in entries[dependency].get("urls", [])
        }
        missing = required_urls - set(urls)
        missing_by_mode[mode] = sorted(missing)
        extras_by_mode[mode] = sorted(set(urls) - required_urls)
        require(
            set(extras_by_mode[mode]) == EXPECTED_ALLOWLIST_EXTRAS.get(mode, set()),
            f"{allowlist_path}: unexpected allowlist extras {extras_by_mode[mode]}",
        )

    require(
        not any(missing_by_mode.values()),
        "allowlist closure:\n"
        + "\n".join(f"{mode}: {urls}" for mode, urls in missing_by_mode.items() if urls),
    )

    verification_path = freeze_root / "authority" / "verification.json"
    verification = load_json(verification_path)
    require(isinstance(verification, dict), f"{verification_path}: root must be an object")
    require(
        set(verification)
        == {
            "schema_version",
            "status",
            "ready_for_freeze",
            "verification_date",
            "manifest_path",
            "current_v5_source_review",
            "rust_1_83_local_verification",
            "versioned_page_byte_lineage",
            "b_cargo_corroborative_material",
            "supplied_tcb_and_dependency_evidence",
            "agent_visible_projection",
            "uncovered_authority_entries",
            "pending",
        },
        f"{verification_path}: top-level fields are not exact",
    )
    require(verification["schema_version"] == 1, "authority verification schema_version must be 1")
    expected_verification_status = {
        "DRAFT": "DRAFT_VERIFIED_PENDING_CROSS_REVIEW",
        "SOURCE-REVIEW-CANDIDATE": "SOURCE-REVIEW-CANDIDATE",
        "READY": "READY_VERIFIED",
    }[expected_status]
    require(verification["status"] == expected_verification_status, "authority verification lifecycle status is wrong")
    require(
        verification["ready_for_freeze"] is (expected_status == "READY"),
        "authority verification readiness flag is wrong",
    )
    if expected_status == "READY":
        require(verification["pending"] == [], "READY authority verification retains pending work")
    elif expected_status == "SOURCE-REVIEW-CANDIDATE":
        require(
            verification["pending"]
            == [
                "two independent V5 oracle source-review receipts",
                "one independent V5 coherence source-review receipt",
                "snapshot derivation of exact report-material bindings",
            ],
            "source-review candidate pending-work inventory is not exact",
        )
    require(verification["manifest_path"] == "propositions.json", "authority verification manifest path mismatch")
    require(verification["uncovered_authority_entries"] == [], "authority verification has uncovered entries")

    rust_entries = {entry_id: entry for entry_id, entry in entries.items() if entry.get("kind") == "RUST"}
    local_expected = {
        entry_id: entry for entry_id, entry in rust_entries.items() if entry.get("versions") == ["1.83.0"]
    }
    reused_expected = {entry_id: entry for entry_id, entry in rust_entries.items() if entry_id not in local_expected}
    supplied_expected = {entry_id: entry for entry_id, entry in entries.items() if entry.get("kind") != "RUST"}

    local = verification["rust_1_83_local_verification"]
    require(isinstance(local, dict) and local.get("status") == "VERIFIED", "Rust 1.83 verification record is invalid")
    require(local.get("uncovered_entries") == [], "Rust 1.83 verification has uncovered entries")
    require(
        local.get("quotation_match_algorithm") == QUOTATION_MATCH_ALGORITHM,
        "Rust 1.83 quotation-match algorithm description drifted from the verifier",
    )
    local_records = records_by_id(local.get("entries"), "Rust 1.83 verification")
    require(set(local_records) == set(local_expected), "Rust 1.83 verification entry coverage mismatch")
    expected_page_urls: dict[str, set[str]] = {}
    for entry_id, entry in local_expected.items():
        record = local_records[entry_id]
        require(record.get("status") == "VERIFIED_LOCAL_OFFICIAL_DOCS", f"{entry_id}: wrong local verification status")
        require(record.get("quotation_count") == len(exact_quotations(entry)), f"{entry_id}: quotation-count mismatch")
        page_paths = sorted(
            {urlsplit(url).path.removeprefix("/1.83.0/") for url in entry["urls"]}
        )
        require(record.get("page_paths") == page_paths, f"{entry_id}: verified page-path mismatch")
        for url in entry["urls"]:
            path = urlsplit(url).path.removeprefix("/1.83.0/")
            expected_page_urls.setdefault(path, set()).add(url)
    local_pages = local.get("pages")
    require(isinstance(local_pages, list), "Rust 1.83 verified pages must be an array")
    pages_by_path: dict[str, dict[str, object]] = {}
    for page in local_pages:
        require(isinstance(page, dict), "Rust 1.83 verified page must be an object")
        path = page.get("path_relative_to_docs_root")
        require(isinstance(path, str) and path not in pages_by_path, f"duplicate/invalid verified page {path!r}")
        pages_by_path[path] = page
    require(set(pages_by_path) == set(expected_page_urls), "Rust 1.83 verified page coverage mismatch")
    for path, urls in expected_page_urls.items():
        require(pages_by_path[path].get("requested_urls") == sorted(urls), f"{path}: requested-URL coverage mismatch")

    current_review = verification["current_v5_source_review"]
    require(
        isinstance(current_review, dict)
        and set(current_review)
        == {
            "status",
            "scope",
            "exact_quotation_evidence_algorithm",
            "exact_quotation_evidence_sha256",
            "required_review_receipts",
        }
        and current_review["scope"]
        == "ALL_CURRENT_V5_EXACT_QUOTATIONS_LOCATORS_PROPOSITIONS_ORACLES_AND_CROSS_FILE_CLOSURE"
        and current_review["exact_quotation_evidence_algorithm"]
        == EXACT_QUOTATION_EVIDENCE_ALGORITHM
        and current_review["exact_quotation_evidence_sha256"]
        == EXPECTED_EXACT_QUOTATION_EVIDENCE_SHA256
        and current_review["required_review_receipts"]
        == [
            "static/integration/reviewed-inputs/source-review-receipts/oracle-review-1.json",
            "static/integration/reviewed-inputs/source-review-receipts/oracle-review-2.json",
            "static/integration/reviewed-inputs/source-review-receipts/coherence-review.json",
        ],
        "current V5 source-review record is not exact",
    )
    expected_current_review_status = (
        "PENDING_INDEPENDENT_SOURCE_REVIEW"
        if expected_status != "READY"
        else "VERIFIED_BY_INDEPENDENT_SOURCE_REVIEW_RECEIPTS"
    )
    require(
        current_review["status"] == expected_current_review_status,
        "current V5 source-review lifecycle status is wrong",
    )

    reused = verification["versioned_page_byte_lineage"]
    require(
        isinstance(reused, dict)
        and set(reused)
        == set(EXPECTED_VERSIONED_PAGE_BYTE_LINEAGE_ENVELOPE)
        | {"entries", "bound_pages", "uncovered_entries", "uncovered_urls"}
        and all(
            reused.get(key) == value
            for key, value in EXPECTED_VERSIONED_PAGE_BYTE_LINEAGE_ENVELOPE.items()
        ),
        "versioned official-page byte lineage is invalid",
    )
    require(reused.get("uncovered_entries") == [] and reused.get("uncovered_urls") == [], "reused V4 authority has uncovered material")
    reused_records = records_by_id(reused.get("entries"), "reused V4 authority")
    require(set(reused_records) == set(reused_expected), "reused V4 authority entry coverage mismatch")
    for entry_id, entry in reused_expected.items():
        record = reused_records[entry_id]
        require(
            record.get("status") == "PAGE_BYTES_BOUND_TO_FROZEN_V4_MANIFEST",
            f"{entry_id}: wrong page-byte lineage status",
        )
        require(record.get("quotation_count") == len(exact_quotations(entry)), f"{entry_id}: quotation-count mismatch")
        require(
            isinstance(record.get("requested_urls"), list)
            and sorted(record["requested_urls"]) == sorted(entry["urls"])
            and len(record["requested_urls"]) == len(set(record["requested_urls"])),
            f"{entry_id}: reused URL mismatch",
        )
    bound_pages = reused.get("bound_pages")
    require(isinstance(bound_pages, list), "reused V4 bound pages must be an array")
    bound_urls = [record.get("requested_url") for record in bound_pages if isinstance(record, dict)]
    expected_reused_urls = {url for entry in reused_expected.values() for url in entry["urls"]}
    require(set(bound_urls) == expected_reused_urls and len(bound_urls) == len(set(bound_urls)), "reused V4 bound-page coverage mismatch")
    exact_quotation_evidence_digest(
        freeze_root,
        expected_status=expected_status,
        local_pages=local_pages,
        reused_pages=bound_pages,
    )

    supplied = verification["supplied_tcb_and_dependency_evidence"]
    require(isinstance(supplied, dict) and supplied.get("status") == "VERIFIED", "supplied evidence record is invalid")
    require(supplied.get("uncovered_entries") == [], "supplied evidence has uncovered entries")
    supplied_records = records_by_id(supplied.get("entries"), "supplied evidence")
    require(set(supplied_records) == set(supplied_expected), "supplied evidence entry coverage mismatch")
    repository = None
    if supplied_source_root is None:
        repository = repository_root
        if repository is None:
            try:
                repository = freeze_root.parents[4]
            except IndexError as error:
                raise ValueError(
                    "cannot infer repository root from a shallow freeze root"
                ) from error
    for entry_id, entry in supplied_expected.items():
        record = supplied_records[entry_id]
        require(record.get("status") == "VERIFIED_EXACT_SUPPLIED_SOURCE", f"{entry_id}: wrong supplied-evidence status")
        require(record.get("quotation_count") == len(exact_quotations(entry)), f"{entry_id}: quotation-count mismatch")
        require(record.get("source_path") == entry["source_path"], f"{entry_id}: supplied source-path mismatch")
        source_path = entry["source_path"].partition("#")[0]
        if supplied_source_root is not None:
            prefix = "evals/unsafe-rust/"
            require(
                source_path.startswith(prefix),
                f"{entry_id}: supplied source path is outside the bound unsafe-rust domain",
            )
            source = supplied_source_root / source_path.removeprefix(prefix)
        else:
            require(repository is not None, "repository root is unavailable")
            source = repository / source_path
        require(source.is_file(), f"{entry_id}: supplied source is absent: {source}")
        require(
            hashlib.sha256(source.read_bytes()).hexdigest() == record.get("source_sha256"),
            f"{entry_id}: supplied source digest mismatch",
        )

    projection = verification["agent_visible_projection"]
    expected_excluded_kinds = sorted(
        {entry.get("kind") for entry in entries.values() if entry.get("kind") != "RUST"}
    )
    require(
        projection
        == {
            "status": "VALIDATED_STRICT_RUST_ONLY_PROJECTION",
            "path": "agent-visible/common.json",
            "schema_path": "../../schemas/agent-authority-packet.schema.json",
            "validator_path": "validate_agent_visible.py",
            "quotation_locator_path": "quotation-locators.json",
            "sha256": projection.get("sha256") if isinstance(projection, dict) else None,
            "common_for_all_modes_and_conditions": True,
            "excluded_kinds": expected_excluded_kinds,
        },
        "agent-visible projection record or excluded-kind inventory is invalid",
    )
    packet = freeze_root / "authority" / projection["path"]
    require(packet.is_file(), "agent-visible projection packet is absent")
    require(hashlib.sha256(packet.read_bytes()).hexdigest() == projection.get("sha256"), "agent-visible projection digest mismatch")

    corroborative = verification.get("b_cargo_corroborative_material")
    require(isinstance(corroborative, dict), "missing B Cargo corroborative-material record")
    require(corroborative.get("status") == "BOUND_TO_FROZEN_V4_REVIEW", "wrong B Cargo provenance status")
    require(corroborative.get("atom_authority_dependency") is False, "B Cargo material must not be an atom authority dependency")
    require(corroborative.get("not_a_substitute_for") == "TCB-B-BUILD-MAP", "B Cargo material must not replace the accepted TCB entry")
    records = corroborative.get("records")
    require(isinstance(records, list) and len(records) == 5, "B Cargo corroborative record count must be five")
    observed_cargo_pages: dict[str, str] = {}
    for record in records:
        require(isinstance(record, dict), "B Cargo corroborative record must be an object")
        require(record.get("fragment_found") is True, "B Cargo corroborative fragment was not verified")
        require(isinstance(record.get("v4_review_excerpt"), str) and record["v4_review_excerpt"].strip(), "B Cargo corroborative record lacks its frozen review excerpt")
        url = record.get("requested_url")
        page_sha256 = record.get("page_sha256")
        require(isinstance(url, str) and isinstance(page_sha256, str), "B Cargo corroborative URL/hash is invalid")
        require(url not in observed_cargo_pages, f"duplicate B Cargo corroborative URL: {url}")
        observed_cargo_pages[url] = page_sha256
    require(observed_cargo_pages == EXPECTED_B_CARGO_PAGE_SHA256, "B Cargo corroborative URL/page-hash binding mismatch")
    require(set(observed_cargo_pages) == set(extras_by_mode["B"]), "B Cargo corroborative records must exactly explain B allowlist extras")

    print(
        "oracle materials ok: "
        f"atoms={len(atom_by_id)} authority_entries={len(entries)} "
        f"allowlist_extras={sum(len(urls) for urls in extras_by_mode.values())}"
    )
    for mode in MODES:
        if extras_by_mode[mode]:
            print(f"allowlist extras {mode}: {extras_by_mode[mode]}")


def main() -> None:
    validate()


if __name__ == "__main__":
    main()
