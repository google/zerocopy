#!/usr/bin/env python3
"""Deterministic verification suite for programmatic codemods, lossless syntax
trees, and two-sided refactoring oracles.

Covers five verification suites using Python 3.10+ standard library only:
  1. CST trivia ownership (OpenRewrite Space / LibCST leading_lines + scope
     qualification) vs. Recast .original shadow-AST reprint cascades vs.
     naive ast.unparse comment erasure.
  2. Comby scannerless parser-combinator priority-delimiter scoping and
     quote/lifetime/raw-string/raw-ident traps (comby-tools/comby@a49be8ef),
     plus Semgrep Textedit.ml / Autofix.ml point-insertion offset corruption,
     multi-pass nesting, newline divergence, and legacy PCRE fix-regex
     re-scanning (semgrep/semgrep@c4dbe9ee).
  3. OpenRewrite RecipeScheduler cycle semantics (openrewrite/rewrite@5c471ca8)
     and RefactoringMiner threshold-free consistent AST replacement unification
     vs. static token-Jaccard similarity thresholds.
  4. Two-sided refactoring oracle forensics: SWE-Refactor Table 2 & Codex
     compound cliff (arXiv:2602.03712v1) plus live AST-test vulnerabilities in
     microsoft/RefactorBench@210b2d15 evaluated inside TemporaryDirectory.
  5. Primary-literature empirical table reconciliations and an explicitly labeled
     [illustrative analytical model] for direct-patch (1 - eps)^N vs. O(1)
     codemod synthesis cost/reliability crossover and over-generalization
     boundaries.

Execution invariants:
  - Python 3.10+ stdlib only; zero third-party packages; zero network I/O.
  - All temporary files isolated in `with tempfile.TemporaryDirectory():`.
  - Zero local paths or wall-clock timestamps in stdout; bit-identical across
    `PYTHONHASHSEED=1` and `PYTHONHASHSEED=2` with `python3 -I -B`.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
import hashlib
import io
import math
import os
import re
import sys
import tempfile
import tokenize
from typing import Callable, Optional


# ============================================================================
# PROBE 1: CST Trivia Ownership vs. Recast Shadow-AST Cascades vs. ast.unparse
# ============================================================================


@dataclass(frozen=True)
class OpenRewriteSpace:
    """Faithful port of `org.openrewrite.java.tree.Space` (`Space.java:34-82`)
    at `openrewrite/rewrite@5c471ca885f60943772d66c18de2f7be94c1a18c`.
    """

    whitespace: Optional[str]
    comments: tuple[str, ...] = ()


class OpenRewriteSpacePool:
    """Port of `Space.flyweights` and `Space.shared` (`Space.java:48-82`)."""

    def __init__(self) -> None:
        self.empty = OpenRewriteSpace(None, ())
        self.single_space = OpenRewriteSpace(" ", ())
        self.flyweights: dict[str, OpenRewriteSpace] = {" ": self.single_space}

    def shared(self, whitespace: str) -> Optional[OpenRewriteSpace]:
        if whitespace == "":
            return self.empty
        if len(whitespace) > 50:
            return None
        existing = self.flyweights.get(whitespace)
        if existing is not None:
            return existing
        created = OpenRewriteSpace(whitespace, ())
        self.flyweights[whitespace] = created
        return created

    def build(self, whitespace: Optional[str], comments: tuple[str, ...]) -> OpenRewriteSpace:
        if not comments:
            interned = self.shared("" if whitespace is None else whitespace)
            if interned is not None:
                return interned
        norm_ws = None if (whitespace is None or whitespace == "") else whitespace
        return OpenRewriteSpace(norm_ws, comments)


@dataclass(frozen=True)
class LeadingEmptyLine:
    """Port of `libcst.EmptyLine` (`libcst/_nodes/whitespace.py:201-239`)
    at `Instagram/LibCST@d9a255843b5cdbecc6834684d233bce1f2987f9d`.
    """

    raw_line: str
    has_comment: bool


@dataclass
class CSTStatementLine:
    """Port of `libcst.SimpleStatementLine` (`libcst/_nodes/statement.py:427-436`)
    owning `leading_lines` (blank lines + standalone `#` comments) and exact
    statement body + trailing inline comment/newline slice.
    """

    leading_lines: list[LeadingEmptyLine]
    code_and_trailing: str
    stmt_ast: Optional[ast.stmt]


def parse_line_cst_module(source: str) -> tuple[list[CSTStatementLine], list[LeadingEmptyLine]]:
    """Splits a Python module into top-level/indented statement chunks with
    `LibCST`-style `leading_lines` ownership so untouched statements round-trip
    byte-for-byte identically.
    """
    raw_lines = source.splitlines(keepends=True)
    tree = ast.parse(source)

    # Collect physical start/end line spans (1-based inclusive) of top-level stmts
    spans: list[tuple[int, int, ast.stmt]] = []
    for node in tree.body:
        start_ln = node.lineno
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and node.decorator_list:
            start_ln = min(start_ln, *(d.lineno for d in node.decorator_list))
        end_ln = node.end_lineno or node.lineno
        spans.append((start_ln, end_ln, node))

    stmts: list[CSTStatementLine] = []
    cursor = 1
    for start_ln, end_ln, node in spans:
        leading: list[LeadingEmptyLine] = []
        while cursor < start_ln:
            ln_txt = raw_lines[cursor - 1]
            stripped = ln_txt.strip()
            leading.append(LeadingEmptyLine(ln_txt, stripped.startswith("#")))
            cursor += 1
        body_txt = "".join(raw_lines[start_ln - 1 : end_ln])
        stmts.append(CSTStatementLine(leading, body_txt, node))
        cursor = end_ln + 1

    footer: list[LeadingEmptyLine] = []
    while cursor <= len(raw_lines):
        ln_txt = raw_lines[cursor - 1]
        footer.append(LeadingEmptyLine(ln_txt, ln_txt.strip().startswith("#")))
        cursor += 1
    return stmts, footer


def render_line_cst_module(stmts: list[CSTStatementLine], footer: list[LeadingEmptyLine]) -> str:
    parts: list[str] = []
    for st in stmts:
        for ll in st.leading_lines:
            parts.append(ll.raw_line)
        parts.append(st.code_and_trailing)
    for ll in footer:
        parts.append(ll.raw_line)
    return "".join(parts)


def count_python_comments(source: str) -> int:
    count = 0
    tok_stream = tokenize.generate_tokens(io.StringIO(source).readline)
    for tok in tok_stream:
        if tok.type == tokenize.COMMENT:
            count += 1
    return count


def scope_qualified_rename_in_chunk(
    chunk: str,
    stmt_node: ast.stmt,
    imported_symbol: str,
    new_symbol: str,
) -> str:
    """Models `LibCST` `ScopeProvider` + `QualifiedNameProvider`
    (`libcst/metadata/name_provider.py:90-197`): renames `NAME` tokens matching
    `imported_symbol` ONLY when lexical scope analysis shows `imported_symbol`
    is not shadowed by a local `def`, assignment, or parameter binding.
    """
    local_bindings: set[str] = set()
    if isinstance(stmt_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        for arg in stmt_node.args.args + stmt_node.args.kwonlyargs:
            local_bindings.add(arg.arg)
        for sub in ast.walk(stmt_node):
            if sub is stmt_node:
                continue
            if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                local_bindings.add(sub.name)
            elif isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Store):
                local_bindings.add(sub.id)
    if imported_symbol in local_bindings:
        return chunk

    # Token-offset surgical replacement preserving all whitespace & comments
    lines = chunk.splitlines(keepends=True)
    line_offsets = [0]
    for ln in lines:
        line_offsets.append(line_offsets[-1] + len(ln))

    edits: list[tuple[int, int]] = []
    for tok in tokenize.generate_tokens(io.StringIO(chunk).readline):
        if tok.type == tokenize.NAME and tok.string == imported_symbol:
            s_row, s_col = tok.start
            e_row, e_col = tok.end
            abs_s = line_offsets[s_row - 1] + s_col
            abs_e = line_offsets[e_row - 1] + e_col
            edits.append((abs_s, abs_e))

    out = chunk
    for abs_s, abs_e in reversed(edits):
        out = out[:abs_s] + new_symbol + out[abs_e:]
    return out


# --- Faithful mini-port of `benjamn/recast@b6377759` `lib/patcher.ts` ---


@dataclass
class RecastNode:
    node_type: str
    fields: dict[str, object]
    orig_text: Optional[str] = None
    original: Optional["RecastNode"] = field(default=None, repr=False)

    def pretty_print(self) -> str:
        """Canonical single-line printer invoked when `findReprints` returns False."""
        if self.node_type == "Identifier":
            return str(self.fields["name"])
        if self.node_type == "BinaryExpression":
            left = self.fields["left"]
            right = self.fields["right"]
            assert isinstance(left, RecastNode) and isinstance(right, RecastNode)
            return f"{left.pretty_print()} {self.fields['operator']} {right.pretty_print()}"
        if self.node_type == "CallExpression":
            callee = self.fields["callee"]
            args = self.fields["arguments"]
            assert isinstance(callee, RecastNode) and isinstance(args, list)
            rendered_args = ", ".join(a.pretty_print() for a in args if isinstance(a, RecastNode))
            return f"{callee.pretty_print()}({rendered_args})"
        if self.node_type == "ReturnStatement":
            arg = self.fields["argument"]
            assert isinstance(arg, RecastNode)
            return f"return {arg.pretty_print()};"
        if self.node_type == "VariableDeclaration":
            ident = self.fields["id"]
            init = self.fields["init"]
            assert isinstance(ident, RecastNode) and isinstance(init, RecastNode)
            return f"const {ident.pretty_print()} = {init.pretty_print()};"
        raise ValueError(f"Unsupported node_type: {self.node_type}")


def recast_tree_copy(node: RecastNode) -> RecastNode:
    """Port of `TreeCopier.copy` (`lib/parser.ts:163-201`): clones tree and sets
    `copy.original = node`.
    """
    copied_fields: dict[str, object] = {}
    for k, v in node.fields.items():
        if isinstance(v, RecastNode):
            copied_fields[k] = recast_tree_copy(v)
        elif isinstance(v, list):
            copied_fields[k] = [recast_tree_copy(x) if isinstance(x, RecastNode) else x for x in v]
        else:
            copied_fields[k] = v
    clone = RecastNode(node.node_type, copied_fields, orig_text=node.orig_text, original=node)
    return clone


def recast_find_any_reprints(
    new_node: object,
    old_node: object,
    reprints: list[tuple[str, str]],
) -> bool:
    """Port of `findAnyReprints` / `findArrayReprints` / `findChildReprints`
    (`lib/patcher.ts:315-539`).
    """
    if new_node is old_node:
        return True
    if isinstance(new_node, list):
        # `patcher.ts:345`: `if (!(isArray.check(oldNode) && oldNode.length === len)) return false;`
        if not (isinstance(old_node, list) and len(old_node) == len(new_node)):
            return False
        for n_elem, o_elem in zip(new_node, old_node):
            if not recast_find_any_reprints(n_elem, o_elem, reprints):
                return False
        return True

    if isinstance(new_node, RecastNode) and isinstance(old_node, RecastNode):
        if new_node.original is None:
            # Fresh builder node (`patcher.ts:176-181, 299-301`)
            if old_node.orig_text is not None:
                reprints.append((old_node.orig_text, new_node.pretty_print()))
                return True
            return False
        if new_node.node_type != old_node.node_type:
            return False
        if new_node.node_type == "Identifier":
            if new_node.fields["name"] != old_node.fields["name"]:
                assert old_node.orig_text is not None
                reprints.append((old_node.orig_text, str(new_node.fields["name"])))
            return True

        orig_reprint_count = len(reprints)
        for k in sorted(set(old_node.fields) | set(new_node.fields)):
            if not recast_find_any_reprints(new_node.fields.get(k), old_node.fields.get(k), reprints):
                # Child could not be surgically patched -> reprint this node if it owns source text
                del reprints[orig_reprint_count:]
                if old_node.orig_text is not None:
                    reprints.append((old_node.orig_text, new_node.pretty_print()))
                    return True
                return False

        # `patcher.ts:531-536`: ReturnStatement ASI blanket bail-out
        if new_node.node_type == "ReturnStatement" and len(reprints) > orig_reprint_count:
            del reprints[orig_reprint_count:]
            return False
        return True

    return new_node == old_node


def recast_print(root: RecastNode) -> str:
    if root.original is None or root.original.orig_text is None:
        return root.pretty_print()
    reprints: list[tuple[str, str]] = []
    ok = recast_find_any_reprints(root, root.original, reprints)
    if not ok:
        return root.pretty_print()
    # Scope note: `recast_find_any_reprints` models `patcher.ts:315-539`'s boolean reprint-cascade
    # decision tree; distinct leaf slices (`accountId`, `tax`) use `str.replace(..., 1)` rather than `loc` offsets.
    text = root.original.orig_text
    for old_slice, new_slice in reprints:
        text = text.replace(old_slice, new_slice, 1)
    return text


def run_probe_1() -> dict[str, object]:
    # --- Part 1A: Python CST trivia + scope qualification vs. ast.unparse ---
    sample_module = (
        "# Module header license comment\n"
        "from auth import check_perm  # imported target\n"
        "\n"
        "# === Critical Auth Section ===\n"
        "LEGACY_AUTH_ENABLED = True\n"
        "def authorize_request(\n"
        "    user_id: str,  # caller id\n"
        "    resource: str,  # target resource\n"
        ") -> bool:\n"
        "    # Verify permission via imported helper\n"
        "    return check_perm(\n"
        "        user_id,\n"
        "        resource,\n"
        "    )\n"
        "\n"
        "def local_override(user_id: str) -> bool:\n"
        "    # Shadowed local helper must NOT be renamed\n"
        "    def check_perm(u: str) -> bool:\n"
        "        return u == 'root'\n"
        "    return check_perm(user_id)\n"
    )
    orig_comments = count_python_comments(sample_module)
    assert orig_comments == 7

    # 1. Naive AST parse + unparse (erases 100% of comments & custom wrapping)
    ast_tree = ast.parse(sample_module)
    ast_tree.body = [
        s for s in ast_tree.body
        if not (isinstance(s, ast.Assign) and isinstance(s.targets[0], ast.Name) and s.targets[0].id == "LEGACY_AUTH_ENABLED")
    ]
    unparsed = ast.unparse(ast_tree) + "\n"
    unparsed_comments = count_python_comments(unparsed)
    assert unparsed_comments == 0

    # 2. LibCST naive RemoveFromParent() without splicing `leading_lines`
    stmts_naive, footer_naive = parse_line_cst_module(sample_module)
    stmts_naive_kept = [
        st for st in stmts_naive
        if not (
            isinstance(st.stmt_ast, ast.Assign)
            and isinstance(st.stmt_ast.targets[0], ast.Name)
            and st.stmt_ast.targets[0].id == "LEGACY_AUTH_ENABLED"
        )
    ]
    naive_cst_out = render_line_cst_module(stmts_naive_kept, footer_naive)
    naive_cst_comments = count_python_comments(naive_cst_out)
    assert naive_cst_comments == 6  # `# === Critical Auth Section ===` silently lost!
    assert "# === Critical Auth Section ===" not in naive_cst_out

    # 3. LibCST leading-line transfer + scope-qualified rename
    stmts_safe, footer_safe = parse_line_cst_module(sample_module)
    spliced_stmts: list[CSTStatementLine] = []
    carry_leading: list[LeadingEmptyLine] = []
    for st in stmts_safe:
        if (
            isinstance(st.stmt_ast, ast.Assign)
            and isinstance(st.stmt_ast.targets[0], ast.Name)
            and st.stmt_ast.targets[0].id == "LEGACY_AUTH_ENABLED"
        ):
            carry_leading.extend(st.leading_lines)
            continue
        merged_leading = carry_leading + st.leading_lines
        carry_leading = []
        assert st.stmt_ast is not None
        updated_chunk = scope_qualified_rename_in_chunk(
            st.code_and_trailing, st.stmt_ast, "check_perm", "verify_perm_v2"
        )
        spliced_stmts.append(CSTStatementLine(merged_leading, updated_chunk, st.stmt_ast))

    safe_cst_out = render_line_cst_module(spliced_stmts, footer_safe)
    safe_cst_comments = count_python_comments(safe_cst_out)
    assert safe_cst_comments == 7
    assert "# === Critical Auth Section ===" in safe_cst_out
    assert "return verify_perm_v2(\n        user_id,\n        resource,\n    )" in safe_cst_out
    assert "def check_perm(u: str) -> bool:" in safe_cst_out
    assert "return check_perm(user_id)" in safe_cst_out

    # 4. OpenRewrite Space flyweight pool (`Space.java:48-82`)
    pool = OpenRewriteSpacePool()
    ws50 = " " * 50
    ws51 = " " * 51
    s50_a = pool.build(ws50, ())
    s50_b = pool.build(ws50, ())
    s51_a = pool.build(ws51, ())
    s51_b = pool.build(ws51, ())
    s_comment_a = pool.build(" ", ("/*c*/",))
    s_comment_b = pool.build(" ", ("/*c*/",))
    assert s50_a is s50_b
    assert s51_a is not s51_b
    assert s_comment_a is not s_comment_b

    # --- Part 1B: Recast `.original` shadow-AST reprint cascades ---
    call_orig_src = (
        "const res = fetchUser(\n"
        "    accountId,\n"
        "    regionCode\n"
        ");"
    )
    call_orig = RecastNode(
        "VariableDeclaration",
        {
            "id": RecastNode("Identifier", {"name": "res"}, orig_text="res"),
            "init": RecastNode(
                "CallExpression",
                {
                    "callee": RecastNode("Identifier", {"name": "fetchUser"}, orig_text="fetchUser"),
                    "arguments": [
                        RecastNode("Identifier", {"name": "accountId"}, orig_text="accountId"),
                        RecastNode("Identifier", {"name": "regionCode"}, orig_text="regionCode"),
                    ],
                },
                orig_text="fetchUser(\n    accountId,\n    regionCode\n)",
            ),
        },
        orig_text=call_orig_src,
    )

    # Case A: Leaf identifier rename preserves 4-line wrapping
    c_rename = recast_tree_copy(call_orig)
    init_node = c_rename.fields["init"]
    assert isinstance(init_node, RecastNode)
    args_list = init_node.fields["arguments"]
    assert isinstance(args_list, list) and isinstance(args_list[0], RecastNode)
    args_list[0].fields["name"] = "tenantId"
    out_a = recast_print(c_rename)
    assert out_a.count("\n") == 3
    assert "    tenantId,\n    regionCode" in out_a

    # Case B: Appending 1 argument triggers `patcher.ts:345` (`oldNode.length !== len`)
    c_append = recast_tree_copy(call_orig)
    init_append = c_append.fields["init"]
    assert isinstance(init_append, RecastNode)
    args_append = init_append.fields["arguments"]
    assert isinstance(args_append, list)
    args_append.append(RecastNode("Identifier", {"name": "timeoutMs"}))
    out_b = recast_print(c_append)
    assert out_b == "const res = fetchUser(accountId, regionCode, timeoutMs);"
    assert out_b.count("\n") == 0  # 100% of multi-line call wrapping collapsed!

    # Case C: Deep leaf edit inside `ReturnStatement` triggers `patcher.ts:531-536`
    ret_orig_src = (
        "return (\n"
        "    price\n"
        "    + tax\n"
        ");"
    )
    ret_orig = RecastNode(
        "ReturnStatement",
        {
            "argument": RecastNode(
                "BinaryExpression",
                {
                    "operator": "+",
                    "left": RecastNode("Identifier", {"name": "price"}, orig_text="price"),
                    "right": RecastNode("Identifier", {"name": "tax"}, orig_text="tax"),
                },
                orig_text="price\n    + tax",
            )
        },
        orig_text=ret_orig_src,
    )
    c_ret = recast_tree_copy(ret_orig)
    bin_arg = c_ret.fields["argument"]
    assert isinstance(bin_arg, RecastNode)
    right_id = bin_arg.fields["right"]
    assert isinstance(right_id, RecastNode)
    right_id.fields["name"] = "vatTax"
    out_c = recast_print(c_ret)
    assert out_c == "return price + vatTax;"
    assert out_c.count("\n") == 0  # 4-line return collapsed to 1 line!

    print("[Probe 1] CST Trivia Ownership vs. Shadow-AST Cascades [Basis: source + execution]")
    print(
        f"  Python comments preserved: orig={orig_comments}, ast.unparse={unparsed_comments}/7 (0.0%), "
        f"naive_CST_remove={naive_cst_comments}/7 (85.7%, banner lost), "
        f"leading_line_splice+scope_rename={safe_cst_comments}/7 (100.0%)"
    )
    print(
        f"  OpenRewrite Space.shared flyweight (limit=50): ws50_interned={s50_a is s50_b}, "
        f"ws51_interned={s51_a is s51_b}, comment_space_interned={s_comment_a is s_comment_b}"
    )
    print(
        f"  Recast patcher.ts line-break survival: leaf_rename={out_a.count(chr(10))}/3 newlines kept, "
        f"arg_append_L345={out_b.count(chr(10))}/3 newlines kept, "
        f"return_inner_rename_L532={out_c.count(chr(10))}/3 newlines kept"
    )
    return {
        "orig_comments": orig_comments,
        "unparsed_comments": unparsed_comments,
        "naive_cst_comments": naive_cst_comments,
        "safe_cst_comments": safe_cst_comments,
    }


# ============================================================================
# PROBE 2: Comby Scannerless Matcher Traps & Semgrep Textedit / Autofix Bugs
# ============================================================================


@dataclass(frozen=True)
class CombySyntaxSpec:
    """Port of `Language.Syntax` in `comby-tools/comby@a49be8ef`
    (`lib/kernel/matchers/languages.ml:4-537`).
    """

    name: str
    escapable_delims: tuple[str, ...]
    escape_char: str = "\\"
    raw_delims: tuple[tuple[str, str], ...] = ()
    line_comments: tuple[str, ...] = ()
    block_comments: tuple[tuple[str, str, bool], ...] = ()  # (open, close, nested)
    balanced_delims: tuple[tuple[str, str], ...] = (("(", ")"), ("[", "]"), ("{", "}"))


COMBY_GENERIC = CombySyntaxSpec(
    name=".generic",
    escapable_delims=('"', "'"),
)

COMBY_RUST = CombySyntaxSpec(
    name=".rs",
    escapable_delims=('"',),  # `languages.ml:499`: `ordinary_string` (drops `'`)
    raw_delims=(("r#", "#"),),  # `languages.ml:500`: `[ {|r#|}, {|#|} ]`
    line_comments=("//",),
    block_comments=(("/*", "*/", True),),
)


def comby_scan_balanced_hole(
    src: str,
    pos: int,
    close_delim: str,
    spec: CombySyntaxSpec,
    priority_delims: Optional[tuple[str, str]] = None,
) -> Optional[int]:
    """Faithful scannerless state-machine port of Comby's `Everything` hole `:[x]`
    (`matcher_engine.ml:379-427, 580-584, 727-741` & `omega_string_literals.ml:6-42`).
    When `priority_delims` is provided (e.g., `("(", ")")` inside `foo(:[x])`),
    `delimiters left right` (`L379-382`) restricts delimiter balancing exclusively to
    `[priority_delims]`; when `priority_delims is None`, all three Dyck pairs in
    `spec.balanced_delims` are balanced.
    """
    n = len(src)
    i = pos
    active_delims = (priority_delims,) if priority_delims is not None else spec.balanced_delims
    open_to_close = dict(active_delims)
    all_closers = {c for _, c in active_delims}

    while i < n:
        if src.startswith(close_delim, i):
            return i

        # 1. `comment_parser` (`matcher_engine.ml:418`)
        matched_comment = False
        for lc in spec.line_comments:
            if src.startswith(lc, i):
                nl = src.find("\n", i + len(lc))
                i = n if nl == -1 else nl + 1
                matched_comment = True
                break
        if matched_comment:
            continue

        for b_open, b_close, is_nested in spec.block_comments:
            if src.startswith(b_open, i):
                i += len(b_open)
                depth = 1
                while i < n and depth > 0:
                    if is_nested and src.startswith(b_open, i):
                        depth += 1
                        i += len(b_open)
                    elif src.startswith(b_close, i):
                        depth -= 1
                        i += len(b_close)
                    else:
                        i += 1
                if depth != 0:
                    return None
                matched_comment = True
                break
        if matched_comment:
            continue

        # 2. `raw_string_literal_parser` (`matcher_engine.ml:419`, `omega_string_literals.ml:38`)
        matched_raw = False
        for r_left, r_right in spec.raw_delims:
            if src.startswith(r_left, i):
                end_idx = src.find(r_right, i + len(r_left))
                if end_idx == -1:
                    return None
                i = end_idx + len(r_right)
                matched_raw = True
                break
        if matched_raw:
            continue

        # 3. `escapable_string_literal_parser` (`matcher_engine.ml:421`, `omega_string_literals.ml:16-25`)
        matched_esc = False
        for q in spec.escapable_delims:
            if src.startswith(q, i):
                i += len(q)
                closed = False
                while i < n:
                    if src[i] == spec.escape_char:
                        if i + 1 >= n:
                            return None
                        i += 2
                    elif src.startswith(q, i):
                        i += len(q)
                        closed = True
                        break
                    else:
                        i += 1
                if not closed:
                    return None
                matched_esc = True
                break
        if matched_esc:
            continue

        # 4. `delims_over_holes` (`between_nested_delims`, `matcher_engine.ml:416,424`)
        matched_nested = False
        for d_open, d_close in open_to_close.items():
            if src.startswith(d_open, i):
                inner_end = comby_scan_balanced_hole(
                    src, i + len(d_open), d_close, spec, priority_delims=priority_delims
                )
                if inner_end is None:
                    return None
                i = inner_end + len(d_close)
                matched_nested = True
                break
        if matched_nested:
            continue

        # Stray closing delimiter in `active_delims` not matching `close_delim` -> fails `reserved_or_space`
        for c_tok in all_closers:
            if src.startswith(c_tok, i):
                return None

        # 5. `whitespace` / `other` (`matcher_engine.ml:423,425`)
        i += 1

    return None


def comby_match_call_hole(src: str, func_prefix: str, spec: CombySyntaxSpec) -> Optional[str]:
    idx = src.find(func_prefix + "(")
    if idx == -1:
        return None
    hole_start = idx + len(func_prefix) + 1
    hole_end = comby_scan_balanced_hole(
        src, hole_start, ")", spec, priority_delims=("(", ")")
    )
    if hole_end is None:
        return None
    return src[hole_start:hole_end]


# --- Faithful port of `semgrep/semgrep@c4dbe9ee` `Textedit.ml` & `Autofix.ml` ---


@dataclass(frozen=True)
class SemgrepEdit:
    path: str
    start: int
    end_: int
    replacement_text: str


@dataclass(frozen=True)
class EditApplicationResult:
    status: str  # "Success" | "Overlap"
    text: str
    conflicting_edits: list[SemgrepEdit]


def semgrep_overlaps_upstream(e1: SemgrepEdit, e2: SemgrepEdit) -> bool:
    """Exact port of `Textedit.overlaps` (`libs/commons/Textedit.ml:57-60`):
    `not (e1.end_ <= e2.start || e2.end_ <= e1.start)`
    """
    return not (e1.end_ <= e2.start or e2.end_ <= e1.start)


def semgrep_overlaps_fixed(e1: SemgrepEdit, e2: SemgrepEdit) -> bool:
    """Fixed interval-conflict predicate rejecting distinct co-located zero-length
    insertions `[p, p)` + `[p, p)`.
    """
    if e1.start == e1.end_ and e2.start == e2.end_ and e1.start == e2.start:
        return True
    return not (e1.end_ <= e2.start or e2.end_ <= e1.start)


def semgrep_remove_overlapping_edits(
    edits: list[SemgrepEdit],
    overlap_fn: Callable[[SemgrepEdit, SemgrepEdit], bool],
) -> tuple[list[SemgrepEdit], list[SemgrepEdit], list[SemgrepEdit]]:
    """Exact port of `Textedit.remove_overlapping_edits` (`Textedit.ml:76-91`)."""
    already_applied: set[SemgrepEdit] = set()
    accepted: list[SemgrepEdit] = []
    redundant: list[SemgrepEdit] = []
    conflicting: list[SemgrepEdit] = []
    for edit in edits:
        if edit in already_applied:
            redundant.append(edit)
        else:
            already_applied.add(edit)
            if any(overlap_fn(edit, acc) for acc in accepted):
                conflicting.append(edit)
            else:
                accepted.append(edit)
    return accepted, redundant, conflicting


def semgrep_remove_newline_for_empty_replacement(text: str, edit: SemgrepEdit) -> SemgrepEdit:
    """Exact port of `Textedit.remove_newline_for_empty_replacement` (`Textedit.ml:95-104`)."""
    text_len = len(text)
    line_start = edit.start == 0 or text[edit.start - 1] == "\n"
    is_empty = len(edit.replacement_text) == 0

    def skip_char(c: str, idx: int) -> int:
        return idx + 1 if (idx + 1 <= text_len and text[idx] == c) else idx

    if line_start and is_empty:
        new_end = skip_char("\n", skip_char("\r", edit.end_))
        return SemgrepEdit(edit.path, edit.start, new_end, edit.replacement_text)
    return edit


def semgrep_apply_edits_to_text(
    text: str,
    edits: list[SemgrepEdit],
    *,
    fixed: bool = False,
) -> EditApplicationResult:
    """Exact port of `Textedit.apply_edits_to_text` (`Textedit.ml:137-168`),
    contrasting upstream `List.sort (fun a b -> Int.compare b.start a.start)`
    against fixed `(b.start, b.end_)` descending tie-breaking.
    """
    overlap_fn = semgrep_overlaps_fixed if fixed else semgrep_overlaps_upstream
    applicable, _redundant, conflicting = semgrep_remove_overlapping_edits(edits, overlap_fn)
    if fixed:
        # Sort descending by `(start, end_)` so `[5, 8)` applies BEFORE `[5, 5)`
        applicable_sorted = sorted(applicable, key=lambda e: (-e.start, -e.end_))
    else:
        # Python `sorted` is stable just like OCaml `List.sort` (`Textedit.ml:151`)
        applicable_sorted = sorted(applicable, key=lambda e: -e.start)

    cur = text
    for ed in applicable_sorted:
        cur = cur[: ed.start] + ed.replacement_text + cur[ed.end_ :]

    if not conflicting:
        return EditApplicationResult("Success", cur, [])
    return EditApplicationResult("Overlap", cur, conflicting)


def semgrep_replace_first_n_upstream(n: int, pattern: str, repl: str, content: str) -> str:
    """Exact port of `Autofix.replace_first_n` (`src/fixing/Autofix.ml:303-315`):
    retained legacy `pcre-ocaml` `replace_first` `[count]` compatibility semantics
    re-scanning `content` from index 0 on every iteration `1..n`.
    """
    cur = content
    for _ in range(n):
        cur = re.sub(pattern, repl, cur, count=1)
    return cur


def run_probe_2() -> dict[str, object]:
    # --- Part 2A: Comby scannerless `.generic` vs `.rs` traps & priority_delims ---
    nested_call = 'foo(bar(1, 2), "unbalanced ) inside string"); foo(3)'
    lazy_match = re.search(r"foo\((.*?)\)", nested_call)
    greedy_match = re.search(r"foo\((.*)\)", nested_call)
    assert lazy_match is not None and greedy_match is not None
    regex_hole = lazy_match.group(1)
    greedy_hole = greedy_match.group(1)
    comby_nested_hole = comby_match_call_hole(nested_call, "foo", COMBY_GENERIC)
    assert regex_hole == "bar(1, 2"  # Lazy regex truncates at inner `bar(1, 2)`!
    assert greedy_hole == 'bar(1, 2), "unbalanced ) inside string"); foo(3'  # Greedy swallows 2nd call!
    assert comby_nested_hole == 'bar(1, 2), "unbalanced ) inside string"'

    # Priority-delimiter scoping (`matcher_engine.ml:379-382, 580-584, 727-741`):
    # Inside `foo(:[x])`, `priority_delims=("(", ")")` restricts delimiters to `()`,
    # matching `foo("}"[0], 1)` and unbalanced-bracket `foo([1, 2)` up to `)`, whereas
    # unenclosed `priority_delims=None` balances all 3 Dyck pairs (`()`, `[]`, `{}`).
    prio_str_idx = comby_match_call_hole('foo("}"[0], 1)', "foo", COMBY_GENERIC)
    prio_unbal_bracket = comby_match_call_hole("foo([1, 2)", "foo", COMBY_GENERIC)
    unenc_unbal_bracket = comby_scan_balanced_hole(
        "foo([1, 2)", 4, ")", COMBY_GENERIC, priority_delims=None
    )
    assert prio_str_idx == '"}"[0], 1'
    assert prio_unbal_bracket == "[1, 2"
    assert unenc_unbal_bracket is None

    # Trap C1: `.generic` fails on single Rust lifetime `'a` (`None`) and
    # silently swallows `)` across return lifetimes `'a .. 'b` (`languages.ml:110` vs `499`)
    rust_lifetime = "fn demo(x: &'a str) {}"
    rust_lifetime_cross = "outer(inner(x: &'a str), y: &'b str)"
    assert comby_match_call_hole(rust_lifetime, "fn demo", COMBY_GENERIC) is None
    assert comby_match_call_hole(rust_lifetime, "fn demo", COMBY_RUST) == "x: &'a str"
    assert (
        comby_match_call_hole(rust_lifetime_cross, "inner", COMBY_GENERIC)
        == "x: &'a str), y: &'b str"
    )
    assert comby_match_call_hole(rust_lifetime_cross, "inner", COMBY_RUST) == "x: &'a str"

    # Trap C2: `.rs` fails on char-literal delimiter `'('` and char-literal quote `'"'`
    rust_char_paren = "foo('(', 42)"
    rust_char_quote = """foo('"', bar(1))"""
    assert comby_match_call_hole(rust_char_paren, "foo", COMBY_RUST) is None
    assert comby_match_call_hole(rust_char_quote, "foo", COMBY_RUST) is None

    # Trap C3: `.rs` `raw_string_literals = [("r#", "#")]` (`languages.ml:500`)
    #   (i) `r##"a"#b"##` or `r#"a#b"#` closes at interior `#`, leaving trailing `"` open!
    #   (ii) Rust 2018 raw identifier `r#type` triggers `raw_string_literal_parser`!
    rust_raw_interior_hash = 'foo(r#"a#b"#, 1)'
    rust_multi_hash_unbalanced = 'foo(r##"a"#)"##, 1)'
    rust_raw_ident = "foo(r#type, 1)"
    assert comby_match_call_hole(rust_raw_interior_hash, "foo", COMBY_RUST) is None
    assert comby_match_call_hole(rust_multi_hash_unbalanced, "foo", COMBY_RUST) == 'r##"a"#'
    assert comby_match_call_hole(rust_raw_ident, "foo", COMBY_RUST) is None

    # --- Part 2B: Semgrep `Textedit.ml` & `Autofix.ml` live bugs ---
    # Bug S1a: Zero-length insertion `[5, 5)` before `[5, 8)` on `"01234foo89"`
    s1_src = "01234foo89"
    s1_edits = [
        SemgrepEdit("demo.py", 5, 5, "HELLO"),
        SemgrepEdit("demo.py", 5, 8, "XYZ"),
    ]
    res_s1_bug = semgrep_apply_edits_to_text(s1_src, s1_edits, fixed=False)
    res_s1_fix = semgrep_apply_edits_to_text(s1_src, s1_edits, fixed=True)
    assert res_s1_bug.status == "Success" and res_s1_bug.conflicting_edits == []
    assert res_s1_bug.text == "01234XYZLOfoo89"  # Corrupted "HELLO" -> "XYZLO" & kept "foo"!
    assert res_s1_fix.status == "Success" and res_s1_fix.text == "01234HELLOXYZ89"

    # Bug S1b: Dual point insertions at `[5, 5)` silently bypass `overlaps` and reverse order
    s1b_edits = [
        SemgrepEdit("demo.py", 5, 5, "A"),
        SemgrepEdit("demo.py", 5, 5, "B"),
    ]
    res_s1b_bug = semgrep_apply_edits_to_text("012345", s1b_edits, fixed=False)
    res_s1b_fix = semgrep_apply_edits_to_text("012345", s1b_edits, fixed=True)
    assert res_s1b_bug.status == "Success" and res_s1b_bug.text == "01234BA5"
    assert res_s1b_fix.status == "Overlap" and res_s1b_fix.text == "01234A5"
    assert len(res_s1b_fix.conflicting_edits) == 1

    # Bug S2: Flat byte-span nesting requires `d` passes on `old(old(...(x)))` vs 1 CST pass
    pass_counts: list[int] = []
    for depth in range(1, 7):
        expr = "old(" * depth + "x" + ")" * depth
        passes = 0
        while "old(" in expr:
            passes += 1
            # Discover top-down matches of `old(...)` and propose `new(<inner>)`
            edits_d: list[SemgrepEdit] = []
            search_pos = 0
            while True:
                idx = expr.find("old(", search_pos)
                if idx == -1:
                    break
                end_paren = comby_scan_balanced_hole(
                    expr, idx + 4, ")", COMBY_GENERIC, priority_delims=("(", ")")
                )
                assert end_paren is not None
                inner = expr[idx + 4 : end_paren]
                edits_d.append(SemgrepEdit("nest.py", idx, end_paren + 1, f"new({inner})"))
                search_pos = idx + 4
            expr = semgrep_apply_edits_to_text(expr, edits_d, fixed=False).text
        assert passes == depth
        pass_counts.append(passes)

    # Bug S3: `Textedit.apply_edits` vs `Autofix.apply_fixes_to_file_exn` newline divergence
    with tempfile.TemporaryDirectory() as tmpdir:
        p_cli = os.path.join(tmpdir, "cli.py")
        p_test = os.path.join(tmpdir, "test.py")
        init_lines = "a = 1\nb = 2\nc = 3\n"
        with open(p_cli, "w", encoding="utf-8") as f:
            f.write(init_lines)
        with open(p_test, "w", encoding="utf-8") as f:
            f.write(init_lines)

        del_edit_cli = semgrep_remove_newline_for_empty_replacement(
            init_lines, SemgrepEdit(p_cli, 6, 11, "")
        )
        cli_out = semgrep_apply_edits_to_text(init_lines, [del_edit_cli]).text
        test_out = semgrep_apply_edits_to_text(init_lines, [SemgrepEdit(p_test, 6, 11, "")]).text
        with open(p_cli, "w", encoding="utf-8") as f:
            f.write(cli_out)
        with open(p_test, "w", encoding="utf-8") as f:
            f.write(test_out)
        assert cli_out == "a = 1\nc = 3\n" and cli_out.count("\n") == 2
        assert test_out == "a = 1\n\nc = 3\n" and test_out.count("\n") == 3

    # Bug S4: `Autofix.replace_first_n` (`Autofix.ml:303-315`) re-wraps match #1
    s4_out = semgrep_replace_first_n_upstream(2, r"\bx\b", "safe(x)", "x + x")
    s4_single_scan = re.sub(r"\bx\b", "safe(x)", "x + x", count=2)
    assert s4_out == "safe(safe(x)) + x"
    assert s4_single_scan == "safe(x) + safe(x)"

    print("[Probe 2] Comby Scannerless Traps & Semgrep Textedit/Autofix Bugs [Basis: source + execution]")
    print(
        "  Comby (.generic vs .rs): "
        f"nested_string_ok={comby_nested_hole is not None} (regex_ok={regex_hole == comby_nested_hole}), "
        f"priority_delims_ok={prio_unbal_bracket == '[1, 2' and unenc_unbal_bracket is None}, "
        f"generic_rust_lifetime={comby_match_call_hole(rust_lifetime, 'fn demo', COMBY_GENERIC)}, "
        f"rs_char_paren={comby_match_call_hole(rust_char_paren, 'foo', COMBY_RUST)}, "
        f"rs_raw_ident_r#type={comby_match_call_hole(rust_raw_ident, 'foo', COMBY_RUST)}"
    )
    print(
        f"  Semgrep Bug S1 (`Textedit.ml:57-60,151`): upstream='{res_s1_bug.text}' "
        f"(status={res_s1_bug.status}, conflicts={len(res_s1_bug.conflicting_edits)}) "
        f"vs fixed='{res_s1_fix.text}'"
    )
    print(
        f"  Semgrep Bug S2/S3/S4: nested_passes(d=1..6)={pass_counts} (CST=1), "
        f"cli_newlines={cli_out.count(chr(10))} vs test_exn_newlines={test_out.count(chr(10))}, "
        f"replace_first_n(2)='{s4_out}'"
    )
    return {
        "s1_bug_text": res_s1_bug.text,
        "s1_fix_text": res_s1_fix.text,
        "nested_passes": pass_counts,
        "s4_out": s4_out,
    }


# ============================================================================
# PROBE 3: OpenRewrite RecipeScheduler Cycles & RefactoringMiner Unification
# ============================================================================


@dataclass(frozen=True)
class SimRecipe:
    name: str
    causes_another_cycle: bool
    transform: Callable[[str], str]


def openrewrite_run_recipe_cycles(
    recipes: list[SimRecipe],
    source: str,
    max_cycles: int = 10,
    min_cycles: int = 1,
    detect_state_cycles: bool = False,
) -> tuple[str, int, bool]:
    """Port of `RecipeScheduler.runRecipeCycles` (`RecipeScheduler.java:85-143`)
    and `RecipeRunCycle.recordChange` (`RecipeRunCycle.java:950-958`) at
    `openrewrite/rewrite@5c471ca885f60943772d66c18de2f7be94c1a18c`.
    Returns `(final_source, cycles_executed, cycle_oscillation_detected)`.
    """
    after = source
    seen_hashes: dict[str, int] = {hashlib.sha256(after.encode("utf-8")).hexdigest(): 0}
    cycles_run = 0

    for i in range(1, max_cycles + 1):
        cycles_run = i
        causes_another = False
        for r in recipes:
            nxt = r.transform(after)
            if nxt != after:
                after = nxt
                if r.causes_another_cycle:
                    causes_another = True

        if detect_state_cycles:
            h = hashlib.sha256(after.encode("utf-8")).hexdigest()
            if h in seen_hashes and causes_another:
                return after, cycles_run, True
            seen_hashes[h] = i

        if i >= min_cycles and not causes_another:
            break

    return after, cycles_run, False


def ast_skeleton_and_consistent_replacements(stmt_a: str, stmt_b: str) -> bool:
    """Models `RefactoringMiner`'s two-pass threshold-free leaf statement matcher
    (`UMLOperationBodyMapper.processLeaves` `L7528` + `ReplacementAlgorithm`
    consistent identifier/expression replacement unification at `L427, L6813`):
    two statements match iff their operator/AST skeletons are isomorphic under
    a bijective identifier replacement map, with zero magic similarity threshold.
    """
    t1 = ast.parse(stmt_a).body[0]
    t2 = ast.parse(stmt_b).body[0]
    fwd: dict[str, str] = {}
    rev: dict[str, str] = {}

    def unify(n1: ast.AST, n2: ast.AST) -> bool:
        if type(n1) is not type(n2):
            return False
        if isinstance(n1, ast.Name) and isinstance(n2, ast.Name):
            prev_f = fwd.get(n1.id)
            prev_r = rev.get(n2.id)
            if prev_f is not None and prev_f != n2.id:
                return False
            if prev_r is not None and prev_r != n1.id:
                return False
            fwd[n1.id] = n2.id
            rev[n2.id] = n1.id
            return True
        if isinstance(n1, ast.Constant) and isinstance(n2, ast.Constant):
            return n1.value == n2.value and type(n1.value) is type(n2.value)
        for field_name in n1._fields:
            if field_name == "ctx":
                continue
            v1 = getattr(n1, field_name)
            v2 = getattr(n2, field_name)
            if isinstance(v1, list) and isinstance(v2, list):
                if len(v1) != len(v2) or not all(unify(x, y) for x, y in zip(v1, v2)):
                    return False
            elif isinstance(v1, ast.AST) and isinstance(v2, ast.AST):
                if not unify(v1, v2):
                    return False
            elif v1 != v2:
                return False
        return True

    return unify(t1, t2)


def token_jaccard_similarity(stmt_a: str, stmt_b: str) -> float:
    toks_a = set(re.findall(r"[A-Za-z_]\w*|\d+|[^\s\w]", stmt_a))
    toks_b = set(re.findall(r"[A-Za-z_]\w*|\d+|[^\s\w]", stmt_b))
    return len(toks_a & toks_b) / len(toks_a | toks_b)


def run_probe_3() -> dict[str, object]:
    # --- Part 3A: OpenRewrite RecipeScheduler starvation & parity oscillation ---
    r_consume = SimRecipe("UpgradeNewApiCall", False, lambda s: s.replace("v2.run(x)", "v2.exec(x)"))
    r_intro = SimRecipe("MigrateV1ToV2", False, lambda s: s.replace("v1.run(x)", "v2.run(x)"))
    starved_out, starved_cycles, _ = openrewrite_run_recipe_cycles([r_consume, r_intro], "v1.run(x)")
    assert starved_out == "v2.run(x)" and starved_cycles == 1  # Starved!

    r_intro_causes = SimRecipe("MigrateV1ToV2", True, lambda s: s.replace("v1.run(x)", "v2.run(x)"))
    fed_out, fed_cycles, _ = openrewrite_run_recipe_cycles([r_consume, r_intro_causes], "v1.run(x)")
    assert fed_out == "v2.exec(x)" and fed_cycles == 2

    # Non-commuting cycle oscillation (`causesAnotherCycle() == True` on exclusive toggle)
    r_toggle = SimRecipe(
        "ToggleIdiom",
        True,
        lambda s: "a != b" if s == "!(a == b)" else ("!(a == b)" if s == "a != b" else s),
    )
    out_odd, cyc_odd, _ = openrewrite_run_recipe_cycles([r_toggle], "!(a == b)", max_cycles=3)
    out_even, cyc_even, _ = openrewrite_run_recipe_cycles([r_toggle], "!(a == b)", max_cycles=4)
    _, cyc_guarded, detected = openrewrite_run_recipe_cycles(
        [r_toggle], "!(a == b)", max_cycles=10, detect_state_cycles=True
    )
    assert out_odd == "a != b" and cyc_odd == 3
    assert out_even == "!(a == b)" and cyc_even == 4
    assert detected is True and cyc_guarded == 2

    # --- Part 3B: [illustrative toy corpus] Threshold-free AST replacement vs. Jaccard ---
    # 8 true refactorings (4 short multi-rename statements + 4 medium renamed statements)
    # 8 non-refactorings (4 operator/literal semantic mutations + 4 long boilerplate cousins)
    toy_pairs: list[tuple[str, str, bool]] = [
        ("a = b + c", "total = price + tax", True),
        ("x = f(y, z)", "res = compute(lhs, rhs)", True),
        ("k = m * n - p", "net = qty * rate - disc", True),
        ("ok = check(u, v)", "valid = verify(uid, tok)", True),
        ("buf.append(item)", "out_list.append(elem)", True),
        ("idx = start + step", "cursor = offset + stride", True),
        ("val = table[key]", "entry = cache[slot]", True),
        ("ret = encode(raw, 8)", "payload = serialize( octets, 8 )", True),
        # False pairs (semantic mutations or shared-boilerplate unrelated statements):
        ("total = price + tax", "total = price - tax", False),
        ("ret = encode(raw, 8)", "ret = encode(raw, 16)", False),
        ("ok = a and b", "ok = a or b", False),
        ("x = f(a, b)", "x = f(a, b, c)", False),
        (
            "logger.info('request_completed', extra_ctx, status_code, latency_ms + overhead_ms)",
            "logger.info('request_completed', extra_ctx, status_code, latency_ms - overhead_ms)",
            False,
        ),
        (
            "metrics.record_histogram('db_query_ms', tenant_id, shard_id, elapsed_ms, 1)",
            "metrics.record_histogram('db_query_ms', tenant_id, shard_id, elapsed_ms, 0)",
            False,
        ),
        (
            "builder.with_header('x-trace', trace_id, span_id, parent_id + 1)",
            "builder.with_header('x-trace', trace_id, span_id, parent_id * 2)",
            False,
        ),
        (
            "audit_log.write_event(actor_id, org_id, resource_id, 'ALLOW')",
            "audit_log.write_event(actor_id, org_id, resource_id, 'DENY')",
            False,
        ),
    ]

    ast_tp = sum(1 for a, b, lbl in toy_pairs if lbl and ast_skeleton_and_consistent_replacements(a, b))
    ast_fp = sum(1 for a, b, lbl in toy_pairs if (not lbl) and ast_skeleton_and_consistent_replacements(a, b))
    assert ast_tp == 8 and ast_fp == 0

    jaccard_results: dict[float, tuple[int, int]] = {}
    for tau in (0.30, 0.50, 0.70, 0.85):
        tp = sum(1 for a, b, lbl in toy_pairs if lbl and token_jaccard_similarity(a, b) >= tau)
        fp = sum(1 for a, b, lbl in toy_pairs if (not lbl) and token_jaccard_similarity(a, b) >= tau)
        jaccard_results[tau] = (tp, fp)
        assert not (tp == 8 and fp == 0)  # No static threshold separates all 16 pairs!

    # Verified live RefactoringMiner Java Benchmark 1 oracle totals (`documentation/accuracy.md:17,38,39`)
    rm_tp, rm_fp, rm_fn = 12725, 13, 211
    rm_prec = rm_tp / (rm_tp + rm_fp)
    rm_rec = rm_tp / (rm_tp + rm_fn)
    em_move_tp, em_move_fp, em_move_fn = 138, 0, 59
    em_move_rec = em_move_tp / (em_move_tp + em_move_fn)
    assert round(rm_prec, 3) == 0.999 and round(rm_rec, 3) == 0.984
    assert round(em_move_rec, 3) == 0.701

    print("[Probe 3] OpenRewrite Cycle Semantics & RefactoringMiner AST Matching [Basis: source + derived]")
    print(
        f"  OpenRewrite RecipeScheduler: default_causesFalse_cycles={starved_cycles} ('{starved_out}'), "
        f"causesTrue_cycles={fed_cycles} ('{fed_out}'), "
        f"oscillation(max=3 -> '{out_odd}', max=4 -> '{out_even}', hash_guard_halt_cycle={cyc_guarded})"
    )
    print(
        f"  [illustrative toy corpus] 16-pair statement matcher: consistent_AST_replacement TP={ast_tp}/8 FP={ast_fp}/8 "
        f"vs Jaccard(tau->TP,FP)={jaccard_results}"
    )
    print(
        f"  RefactoringMiner live oracle (`accuracy.md`, 102 types): TP={rm_tp}, FP={rm_fp}, FN={rm_fn} "
        f"(P={rm_prec:.4f}, R={rm_rec:.4f}); Extract+Move R={em_move_rec:.4f} (FN={1.0 - em_move_rec:.2%})"
    )
    return {
        "jaccard_results": jaccard_results,
        "rm_prec": rm_prec,
        "rm_rec": rm_rec,
        "em_move_rec": em_move_rec,
    }


# ============================================================================
# PROBE 4: SWE-Refactor Two-Sided Oracle & Live RefactorBench AST Flaws
# ============================================================================


def fisher_exact_two_sided(a: int, b: int, c: int, d: int) -> float:
    """Exact two-sided Fisher's exact test p-value via `math.comb`."""
    r1 = a + b
    r2 = c + d
    c1 = a + c
    n = r1 + r2
    denom = math.comb(n, c1)

    def prob(k: int) -> float:
        return (math.comb(r1, k) * math.comb(r2, c1 - k)) / denom

    p_obs = prob(a)
    k_min = max(0, c1 - r2)
    k_max = min(r1, c1)
    return sum(prob(k) for k in range(k_min, k_max + 1) if prob(k) <= p_obs + 1e-15)


def refactorbench_adapt_method_mode_oracle(handler_utils_path: str, base_path: str) -> bool:
    """Exact AST predicate ported verbatim from `microsoft/RefactorBench@210b2d15`
    `tests/django_refactor/adapt_method_mode.py:7-65`.
    """
    with open(handler_utils_path, "r", encoding="utf-8") as f:
        tree_u = ast.parse(f.read())

    fn_ok = False
    for node in ast.walk(tree_u):
        if isinstance(node, ast.FunctionDef) and node.name == "adapt_method_mode":
            args = [arg.arg for arg in node.args.args]
            if "is_async" not in args or "method" not in args:
                return False
            if not {"method_is_async", "debug", "name"}.issubset(args):
                return False
            fn_ok = True
            break
    if not fn_ok:
        return False

    with open(base_path, "r", encoding="utf-8") as f:
        tree_b = ast.parse(f.read())
    import_found = False
    for node in ast.walk(tree_b):
        # `adapt_method_mode.py:39`: ignores `node.level` and rejects full package path!
        if isinstance(node, ast.ImportFrom) and node.module == "handler_utils":
            for alias in node.names:
                if alias.name == "adapt_method_mode":
                    import_found = True
                    break
    if not import_found:
        return False

    required_imports = {"async_to_sync", "iscoroutinefunction", "sync_to_async"}
    imports_found: set[str] = set()
    for node in ast.walk(tree_u):
        if isinstance(node, ast.ImportFrom) and node.module == "asgiref.sync":
            for alias in node.names:
                if alias.name in required_imports:
                    imports_found.add(alias.name)
    return required_imports.issubset(imports_found)


def refactorbench_disconnect_all_param_oracle(signal_path: str) -> bool:
    """Exact AST predicate ported verbatim from `microsoft/RefactorBench@210b2d15`
    `tests/scrapy_refactor/add-log-parameter-disconnect-all.py:19-36`.
    """
    with open(signal_path, "r", encoding="utf-8") as f:
        tree = ast.parse(f.read())

    function_found = False
    log_param_found = False
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name == "disconnect_all":
            function_found = True
            for arg in node.args.args:
                if arg.arg == "log":
                    # `L27`: Unconditionally sets `log_param_found = True` BEFORE checking defaults!
                    log_param_found = True
                    if node.args.defaults:
                        # `L30`: Indexes `defaults[-1]` rather than aligning with `arg`'s position!
                        log_default_value = node.args.defaults[-1]
                        if isinstance(log_default_value, ast.Constant) and isinstance(log_default_value.value, bool):
                            log_param_found = True
                            break
    return function_found and log_param_found


def run_probe_4() -> dict[str, object]:
    # --- Part 4A: SWE-Refactor (`arXiv:2602.03712v1` Table 2, N = 1,099) ---
    n_total = 1099
    swe_refactor_table2 = [
        # (model, compile_and_test |T|, ast_rf |R|, successful |T cap R|)
        ("DeepSeek-V3", 554, 674, 457),
        ("gpt-4o-mini", 537, 636, 438),
        ("gpt-3.5-turbo", 199, 142, 82),
        ("CodeLLaMa-7B", 41, 48, 12),
        ("DeepSeek-Coder-6.7B", 31, 70, 7),
        ("Qwen2.5-Coder-14B", 22, 101, 7),
        ("Qwen2.5-Coder-7B", 20, 142, 6),
        ("DeepSeek-Coder-16B", 23, 101, 3),
        ("CodeLLaMa-13B", 14, 15, 1),
    ]

    oracle_gaps: dict[str, tuple[int, float, int, float]] = {}
    for model, t_cnt, r_cnt, both_cnt in swe_refactor_table2:
        # Exact identity: |T \ R| == |T| - |T cap R|, |R \ T| == |R| - |T cap R|
        # because `Successful Refactoring` IS defined as `Compile&Test AND AST-Based RF`!
        test_only_fp = t_cnt - both_cnt
        ast_only_fp = r_cnt - both_cnt
        assert both_cnt <= min(t_cnt, r_cnt)
        assert t_cnt + r_cnt - both_cnt <= n_total
        oracle_gaps[model] = (
            test_only_fp,
            test_only_fp / t_cnt,
            ast_only_fp,
            ast_only_fp / r_cnt,
        )

    ds_t_fp, ds_t_rate, ds_r_fp, ds_r_rate = oracle_gaps["DeepSeek-V3"]
    g4m_t_fp, g4m_t_rate, g4m_r_fp, g4m_r_rate = oracle_gaps["gpt-4o-mini"]
    assert ds_t_fp == 97 and round(ds_t_rate * 100, 2) == 17.51
    assert ds_r_fp == 217 and round(ds_r_rate * 100, 2) == 32.20
    assert g4m_t_fp == 99 and round(g4m_t_rate * 100, 2) == 18.44
    assert g4m_r_fp == 198 and round(g4m_r_rate * 100, 2) == 31.13

    # GPT-5.1-Codex agentic evaluation (`arXiv:2602.03712v1` §4.4, N = 200):
    # Atomic: 138 / 167 (82.63%), Compound: 13 / 33 (39.39%), Total: 151 / 200 (75.50%)
    a_pass, a_fail = 138, 167 - 138
    c_pass, c_fail = 13, 33 - 13
    p_codex = fisher_exact_two_sided(a_pass, a_fail, c_pass, c_fail)
    odds_ratio = (a_pass * c_fail) / (a_fail * c_pass)
    assert abs(p_codex - 1.073166e-6) < 1e-11

    # --- Part 4B: Live RefactorBench AST-test vulnerabilities in TemporaryDirectory ---
    with tempfile.TemporaryDirectory() as tmpdir:
        # 1. `adapt_method_mode`: adversarial lobotomized + broken Python-2 import vs valid absolute import
        u_bad = os.path.join(tmpdir, "bad_handler_utils.py")
        b_bad = os.path.join(tmpdir, "bad_base.py")
        with open(u_bad, "w", encoding="utf-8") as f:
            f.write(
                "from asgiref.sync import async_to_sync, iscoroutinefunction, sync_to_async\n"
                "def adapt_method_mode(name, debug, method_is_async, method, is_async):\n"
                "    pass  # semantic lobotomy + scrambled required/optional params!\n"
            )
        with open(b_bad, "w", encoding="utf-8") as f:
            f.write("from handler_utils import adapt_method_mode\n")  # level=0 -> ModuleNotFoundError in pkg!

        u_good = os.path.join(tmpdir, "good_handler_utils.py")
        b_good = os.path.join(tmpdir, "good_base.py")
        with open(u_good, "w", encoding="utf-8") as f:
            f.write(
                "from asgiref.sync import async_to_sync, iscoroutinefunction, sync_to_async\n"
                "def adapt_method_mode(is_async, method, method_is_async=None, debug=False, name=None):\n"
                "    return method\n"
            )
        with open(b_good, "w", encoding="utf-8") as f:
            f.write("from django.core.handlers.handler_utils import adapt_method_mode\n")

        rb_adapt_bad = refactorbench_adapt_method_mode_oracle(u_bad, b_bad)
        rb_adapt_good = refactorbench_adapt_method_mode_oracle(u_good, b_good)
        assert rb_adapt_bad is True   # False Positive: broken code PASSES RefactorBench!
        assert rb_adapt_good is False  # False Negative: valid absolute import FAILS RefactorBench!

        # 2. `add-log-parameter-disconnect-all`: missing boolean default vs valid kwonlyargs
        s_bad_no_default = os.path.join(tmpdir, "bad_signal.py")
        s_good_kwonly = os.path.join(tmpdir, "good_signal.py")
        with open(s_bad_no_default, "w", encoding="utf-8") as f:
            f.write("def disconnect_all(signal, sender, log):\n    pass\n")
        with open(s_good_kwonly, "w", encoding="utf-8") as f:
            f.write("def disconnect_all(signal=None, sender=None, *, log: bool = True):\n    return log\n")

        rb_disc_bad = refactorbench_disconnect_all_param_oracle(s_bad_no_default)
        rb_disc_good = refactorbench_disconnect_all_param_oracle(s_good_kwonly)
        assert rb_disc_bad is True   # False Positive via L27 unconditional `log_param_found = True`!
        assert rb_disc_good is False  # False Negative because `node.args.kwonlyargs` is ignored!

        # Verify actual runtime behavior on `s_bad_no_default` vs `s_good_kwonly`
        ns_bad: dict[str, object] = {}
        ns_good: dict[str, object] = {}
        with open(s_bad_no_default, "r", encoding="utf-8") as f:
            exec(compile(f.read(), "bad_signal.py", "exec"), ns_bad)
        with open(s_good_kwonly, "r", encoding="utf-8") as f:
            exec(compile(f.read(), "good_signal.py", "exec"), ns_good)

        runtime_bad_ok = True
        try:
            fn_bad = ns_bad["disconnect_all"]
            assert callable(fn_bad)
            fn_bad("sig", "snd")  # Existing 2-arg callers crash with TypeError!
        except TypeError:
            runtime_bad_ok = False
        fn_good = ns_good["disconnect_all"]
        assert callable(fn_good)
        runtime_good_ok = fn_good("sig", "snd") is True
        assert runtime_bad_ok is False and runtime_good_ok is True

    print("[Probe 4] Two-Sided SWE-Refactor Oracle & Live RefactorBench AST Bugs [Basis: source + execution + derived]")
    print(
        f"  SWE-Refactor Table 2 (N={n_total}) exact set differences (|T\\R|/|T| test-only FP, |R\\T|/|R| AST-only FP): "
        f"DeepSeek-V3=({ds_t_fp}/{554} [{ds_t_rate:.2%}], {ds_r_fp}/{674} [{ds_r_rate:.2%}]), "
        f"gpt-4o-mini=({g4m_t_fp}/{537} [{g4m_t_rate:.2%}], {g4m_r_fp}/{636} [{g4m_r_rate:.2%}])"
    )
    print(
        f"  SWE-Refactor §4.4 GPT-5.1-Codex cliff: atomic=138/167 ({138/167:.2%}) vs compound=13/33 ({13/33:.2%}), "
        f"OR={odds_ratio:.3f}, Fisher two-sided p={p_codex:.4e}"
    )
    print(
        f"  RefactorBench live AST-oracle inversions: "
        f"adapt_method_mode(lobotomized+level0_import -> AST={rb_adapt_bad}, valid_abs_import -> AST={rb_adapt_good}); "
        f"disconnect_all(missing_default -> AST={rb_disc_bad}/runtime={runtime_bad_ok}, "
        f"valid_kwonly -> AST={rb_disc_good}/runtime={runtime_good_ok})"
    )
    return {
        "ds_t_rate": ds_t_rate,
        "ds_r_rate": ds_r_rate,
        "p_codex": p_codex,
    }


# ============================================================================
# PROBE 5: Primary-Literature Reconciliations & Analytical Crossover Model
# ============================================================================


def run_probe_5() -> dict[str, object]:
    # --- Part 5A: Primary-literature exact arithmetic reconciliations ---
    # 1. Soares et al. TSE 2013 (§5.3.1-5.3.2, Tables 5-6)
    soares_compile = {"Eclipse_JDT": 16, "NetBeans": 29, "JRRTv1": 11, "JRRTv2": 1}
    soares_behav = {"Eclipse_JDT": 18, "NetBeans": 22, "JRRTv1": 13, "JRRTv2": 10}
    assert sum(soares_compile.values()) == 57
    assert sum(soares_behav.values()) == 63
    soares_totals = {k: soares_compile[k] + soares_behav[k] for k in soares_compile}
    assert soares_totals == {"Eclipse_JDT": 34, "NetBeans": 51, "JRRTv1": 24, "JRRTv2": 11}
    assert sum(soares_totals.values()) == 120

    # 2. Dilhara et al. FSE 2024 PyCraft Table 1 exact 10-CPAT column sums
    pycraft_rows = [
        # (cpat_id, V, V_c, V_u, V_a, T_1, T_2, reported_rounded_mult)
        (1, 1185, 291, 83, 50, 17, 196, 11),
        (2, 1201, 478, 119, 110, 51, 201, 4),
        (3, 782, 287, 107, 66, 10, 141, 14),
        (4, 285, 101, 20, 10, 2, 12, 6),
        (5, 1265, 416, 150, 75, 9, 125, 14),
        (6, 927, 425, 202, 85, 11, 106, 10),
        (7, 1223, 290, 95, 80, 3, 68, 23),
        (8, 177, 28, 26, 24, 16, 208, 13),
        (9, 64, 11, 11, 9, 5, 36, 7),
        (10, 955, 453, 226, 71, 23, 907, 39),
    ]
    sum_v = sum(r[1] for r in pycraft_rows)
    sum_vc = sum(r[2] for r in pycraft_rows)
    sum_vu = sum(r[3] for r in pycraft_rows)
    sum_va = sum(r[4] for r in pycraft_rows)
    sum_t1 = sum(r[5] for r in pycraft_rows)
    sum_t2 = sum(r[6] for r in pycraft_rows)
    mean_mult = sum(r[7] for r in pycraft_rows) / len(pycraft_rows)
    assert sum_v == 8064  # Note: §4.3.1 prose prints 9,325 while Table 1 sums to 8,064!
    assert (sum_vc, sum_vu, sum_va, sum_t1, sum_t2) == (2780, 1039, 580, 147, 2000)
    assert round(mean_mult, 1) == 14.1 and round(sum_t2 / sum_t1, 2) == 13.61

    # 3. Liu et al. ASE 2025 (§4.2 & §5.2): unsafe patch rate + RefactoringMirror 33/35 vs 32/35
    eps_liu_combined = (13 + 9) / (176 + 137)  # 22 / 313 = 7.0288%
    rm_detected_rate = 33 / 35                 # 94.29% (printed as "94.3%=33/35" in Abstract & §5.2)
    rm_reapplied_rate = 32 / 35                # 91.43% (true end-to-end IntelliJ reapplication in §5.2)
    assert round(eps_liu_combined * 100, 2) == 7.03
    assert round(rm_detected_rate * 100, 1) == 94.3 and round(rm_reapplied_rate * 100, 1) == 91.4

    # 4. Shirafuji et al. APSEC 2023 (Tables II & V): 3-shot fail rate & comment loss
    eps_shirafuji_io = 1.0 - 0.9111  # 8.89% single-shot I/O failure despite 99.93% compilability
    comment_drop_pct = (0.60 - 0.16) / 0.60  # 73.33% mean comment line erasure

    # --- Part 5B: [illustrative analytical model] Direct-Patch vs. Codemod Crossover ---
    # Model assumptions (explicitly analytical, Basis: derived):
    #   - Independent per-site direct-LLM failure rate `eps` over `N` uniform target sites:
    #     P_direct(N) = (1 - eps)^N
    #   - Representative token-cost parameterization:
    #     C_direct(N) = N * c_patch  (c_patch = 1800 tokens/site context + diff)
    #     C_codemod(N) = k_iter * c_synth + N * c_cst  (k_iter = 3, c_synth = 2400 tokens, c_cst = 0 LLM tokens)
    c_patch = 1800
    k_iter = 3
    c_synth = 2400
    n_cost_star = math.ceil((k_iter * c_synth) / c_patch)
    assert n_cost_star == 4

    # Reliability crossover against Refazer empirical synthesis baseline `p_synth = 49 / 59 = 0.8305`
    # on uniform structural edits (where validated deterministic CST codemod has eps_apply = 0):
    p_synth_refazer = 49 / 59  # 83.05% (38 exact + 11 missed-by-developer sites; 10/59 = 16.95% over-generalized)

    def min_n_where_codemod_beats_direct(eps: float, p_codemod: float) -> int:
        for n in range(1, 500):
            if (1.0 - eps) ** n < p_codemod:
                return n
        raise RuntimeError("No crossover")

    n_rel_liu = min_n_where_codemod_beats_direct(eps_liu_combined, p_synth_refazer)
    n_rel_shirafuji = min_n_where_codemod_beats_direct(eps_shirafuji_io, p_synth_refazer)
    n_rel_em_raw = min_n_where_codemod_beats_direct(0.574, p_synth_refazer)
    assert (n_rel_liu, n_rel_shirafuji, n_rel_em_raw) == (3, 2, 1)

    decay_curve_liu = {n: round((1.0 - eps_liu_combined) ** n, 4) for n in (1, 3, 5, 10, 25, 50)}

    print("[Probe 5] Primary-Literature Reconciliations & Direct-vs-Codemod Crossover [Basis: documentation + derived]")
    print(
        f"  Soares TSE'13 per-IDE bug totals (57 compile + 63 behavioral = 120): {soares_totals}"
    )
    print(
        f"  PyCraft FSE'24 Table 1 exact sums: sum(V)={sum_v} (prose=9325), Va={sum_va} (mean=58.0), "
        f"T1={sum_t1} -> T2={sum_t2} ({sum_t2/sum_t1:.2f}x aggregate, {mean_mult:.1f}x mean col multiplier)"
    )
    print(
        f"  Liu ASE'25 RefactoringMirror reconciliation: ReExtractor_detected=33/35 ({rm_detected_rate:.1%}), "
        f"IntelliJ_reapplied=32/35 ({rm_reapplied_rate:.1%}), unsafe_eliminated=22/22 (combined LLM unsafe={eps_liu_combined:.2%})"
    )
    print(
        f"  [illustrative analytical model] Direct-patch (1 - eps)^N at eps=7.03%: {decay_curve_liu}; "
        f"cost break-even N_cost*={n_cost_star} sites (k=3, 2400/1800 tok); "
        f"reliability crossover vs p_synth={p_synth_refazer:.2%}: "
        f"N_rel*(eps=7.03%)={n_rel_liu}, N_rel*(eps=8.89%)={n_rel_shirafuji}, N_rel*(EM_invalid=57.4%)={n_rel_em_raw}; "
        f"Shirafuji comment erasure={comment_drop_pct:.1%}"
    )
    return {
        "n_cost_star": n_cost_star,
        "n_rel_liu": n_rel_liu,
        "decay_curve_liu": decay_curve_liu,
    }


def main() -> int:
    print("=== Programmatic Codemods, CSTs & Refactoring Oracles Verification Suite ===")
    run_probe_1()
    run_probe_2()
    run_probe_3()
    run_probe_4()
    run_probe_5()
    print("=== ALL 5 PROBE SUITES PASSED DETERMINISTICALLY ===")
    return 0


if __name__ == "__main__":
    sys.exit(main())
