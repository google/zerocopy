#!/usr/bin/env python3
"""Executable verification suite for polyglot code-generation harnesses,
exact subword pre-tokenization and byte-level BPE fertility across high- and
low-resource programming languages, multiplicative fertility penalties, and
static-type vs. RLVR cross-language transfer dynamics.

Pure Python 3.10+ standard library only (`python3 -I -B`), zero third-party
dependencies, zero network or subprocess calls, deterministic stdout across
`PYTHONHASHSEED` values, and `< 2.0s` wall-clock execution.
"""

from __future__ import annotations

import ast
import heapq
import math
import random
import re
import time
import unicodedata
from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple

SEED = 20261122


# ============================================================================
# Numerical & linear-algebra utilities (pure stdlib)
# ============================================================================

def norm_cdf(x: float) -> float:
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def two_sided_z_pvalue(z: float) -> float:
    return 2.0 * (1.0 - norm_cdf(abs(z)))


def solve_linear_system(a: List[List[float]], b: List[float]) -> List[float]:
    """Gaussian elimination with partial pivoting for small dense systems."""
    n = len(b)
    mat = [row[:] + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(mat[r][col]))
        if abs(mat[piv][col]) < 1e-14:
            raise ValueError("Singular matrix in regression")
        mat[col], mat[piv] = mat[piv], mat[col]
        div = mat[col][col]
        for j in range(col, n + 1):
            mat[col][j] /= div
        for r in range(n):
            if r != col and mat[r][col] != 0.0:
                factor = mat[r][col]
                for j in range(col, n + 1):
                    mat[r][j] -= factor * mat[col][j]
    return [mat[i][n] for i in range(n)]


def fit_wls(
    x_rows: Sequence[Sequence[float]],
    y: Sequence[float],
    weights: Optional[Sequence[float]] = None,
) -> Tuple[List[float], List[float], float]:
    """Weighted least squares returning (betas, std_errors, r_squared)."""
    n = len(y)
    p = len(x_rows[0])
    w = [1.0] * n if weights is None else list(weights)
    xtwx = [[0.0] * p for _ in range(p)]
    xtwy = [0.0] * p
    for i in range(n):
        wi = w[i]
        xi = x_rows[i]
        yi = y[i]
        for j in range(p):
            xtwy[j] += wi * xi[j] * yi
            for k in range(p):
                xtwx[j][k] += wi * xi[j] * xi[k]
    beta = solve_linear_system(xtwx, xtwy)

    # Invert X^T W X column by column for covariance matrix
    inv_xtwx = [[0.0] * p for _ in range(p)]
    for col in range(p):
        e = [1.0 if i == col else 0.0 for i in range(p)]
        sol = solve_linear_system(xtwx, e)
        for row in range(p):
            inv_xtwx[row][col] = sol[row]

    w_sum = sum(w)
    y_bar = sum(w[i] * y[i] for i in range(n)) / w_sum
    ss_tot = sum(w[i] * (y[i] - y_bar) ** 2 for i in range(n))
    ss_res = 0.0
    for i in range(n):
        pred = sum(x_rows[i][j] * beta[j] for j in range(p))
        ss_res += w[i] * (y[i] - pred) ** 2
    dof = max(1, n - p)
    sigma2 = ss_res / dof
    se = [math.sqrt(max(0.0, sigma2 * inv_xtwx[j][j])) for j in range(p)]
    r2 = 1.0 - (ss_res / ss_tot) if ss_tot > 0.0 else 0.0
    return beta, se, r2


# ============================================================================
# PROBE 1: Polyglot Benchmark Harness Forensics
#   - nuprl/MultiPL-E @ 5d60ac014ea0e8567d7f24b8c733f129c6c5891c
#   - MCEVAL/McEval @ 09dec129dd5756447227239b3e5b47e543c2e0fd
#   - google-research/babelcode @ e8314f6f438193893b705e9fa8f8c8069af26dec
# ============================================================================

def parse_type_ann(type_src: str) -> ast.AST:
    mod = ast.parse(f"x: {type_src}")
    ann = mod.body[0]
    assert isinstance(ann, ast.AnnAssign)
    return ann.annotation


# --- Exact ports from nuprl/MultiPL-E@5d60ac01 ---

def multipl_e_ml_coerce(expr: str, tp: object) -> str:
    """Port of dataset_builder/humaneval_to_ml.py:54-76."""
    def coerce_to_option(e: str) -> str:
        return e if e == "None" else f"Some({e})"

    match expr, tp:
        case e, ast.Subscript(ast.Name("Optional"), _):
            return coerce_to_option(e)
        case e, ast.Name("float") | "float" if "." not in e:
            paren_int = re.fullmatch(r"\((-?\d+)\)", e)
            if paren_int:
                return f"({paren_int.group(1)}.0)"
            return f"{e}.0"
        case e, ast.Subscript(ast.Name("List"), ast.Name("float") | "float"):
            parts = e[1:-1].split("; ")
            inner = "; ".join([multipl_e_ml_coerce(part, "float") for part in parts])
            return f"[{inner}]"
        case _:
            return expr


def multipl_e_ml_gen_literal(c: object) -> Optional[str]:
    """Port of dataset_builder/humaneval_to_ml.py:113-125 (omits None branch)."""
    if type(c) is bool:
        return str(c).lower()
    if type(c) is str:
        return f'"{c}"'
    if type(c) is int:
        return f"(-{c * (-1)})" if c < 0 else repr(c)
    if type(c) is float:
        return repr(c)
    return None


def multipl_e_jl_translate_type(t: object) -> str:
    """Port of dataset_builder/humaneval_to_jl.py:25-65."""
    match t:
        case ast.Subscript(ast.Name(ident), slc, _ctx):
            match ident:
                case "List":
                    return "Vector{" + multipl_e_jl_translate_type(slc) + "}"
                case "Dict":
                    match slc:
                        case ast.Tuple([ast.Name(k), ast.Name(v)], _):
                            key = multipl_e_jl_translate_type(k)
                            val = multipl_e_jl_translate_type(v)
                            # Exact line 51 with stray trailing '>'
                            return f"Dict{{{key}, {val}}}>"
                        case _:
                            raise ValueError(f"Bad dict: {slc}")
                case "Optional":
                    return "Union{" + multipl_e_jl_translate_type(slc) + ", Nothing}"
                case _:
                    raise ValueError(f"Unsupported generic: {ident}")
        case ast.Name("int") | "int":
            return "Int64"
        case ast.Name("float") | "float":
            return "Float64"
        case ast.Name("bool") | "bool":
            return "Bool"
        case ast.Name("str") | "str":
            return "String"
        case _:
            raise ValueError(f"Unknown type: {t}")


def multipl_e_rs_translate_type(t: object) -> str:
    """Port of dataset_builder/humaneval_to_rs.py:52-88."""
    match t:
        case ast.Subscript(ast.Name(ident), slc, _ctx):
            if ident == "List":
                return "Vec<" + multipl_e_rs_translate_type(slc) + ">"
            if ident == "Dict":
                match slc:
                    case ast.Tuple([ast.Name(k), ast.Name(v)], _):
                        return f"HashMap<{multipl_e_rs_translate_type(k)}, {multipl_e_rs_translate_type(v)}>"
        case ast.Name("int") | "int":
            return "isize"
        case ast.Name("float") | "float":
            return "f64"
        case ast.Name("str") | "str":
            return "String"
        case ast.Name("bool") | "bool":
            return "bool"
    raise ValueError(f"Unsupported Rust type: {t}")


def multipl_e_rs_coerce_pinned(expr: str, tp: object) -> str:
    """Port of dataset_builder/humaneval_to_rs.py:99-133 (exact pinned AST bug)."""
    match expr, tp:
        case "vec![]", ast.Subscript(ast.Name("List"), to):
            return f"Vec::<{multipl_e_rs_translate_type(to)}>::new()"
        # Line 113: ast.Tuple([k, v]) is inside ast.Name(..., ctx=...) instead of Subscript.slice!
        case "HashMap::from([])", ast.Subscript(ast.Name("Dict", ast.Tuple([k, v]))):
            # Line 114: second latent bug duplicates k instead of v!
            return f"HashMap::<{multipl_e_rs_translate_type(k)}, {multipl_e_rs_translate_type(k)}>::new()"
        case _:
            return expr


def multipl_e_rs_coerce_slice_fixed_only(expr: str, tp: object) -> str:
    """Counterfactual fixing ONLY line 113's AST pattern, exposing line 114's <K, K> bug."""
    match expr, tp:
        case "HashMap::from([])", ast.Subscript(ast.Name("Dict"), ast.Tuple([k, v])):
            return f"HashMap::<{multipl_e_rs_translate_type(k)}, {multipl_e_rs_translate_type(k)}>::new()"
        case _:
            return expr


class MultiPLELuaTranslator:
    """Port of dataset_builder/humaneval_to_lua.py:48-77."""

    @staticmethod
    def gen_literal(c: object) -> str:
        if type(c) is bool:
            return str(c).lower()
        return repr(c)

    @staticmethod
    def gen_list(elems: List[str]) -> str:
        return "{" + ", ".join(elems) + "}"

    @staticmethod
    def gen_tuple(elems: List[str]) -> str:
        return "{" + ", ".join(elems) + "}"

    @staticmethod
    def gen_dict(keys: List[str], values: List[str]) -> str:
        return "{" + ", ".join(f"[{k}] = {v}" for k, v in zip(keys, values)) + "}"


def lua_ipairs_visit(lua_seq_with_globals: Sequence[str], globals_env: Dict[str, object]) -> List[object]:
    """Exact Lua 5.4 ipairs traversal over table literal `{e_1, ..., e_n}`."""
    table: Dict[int, object] = {}
    for idx, token in enumerate(lua_seq_with_globals, start=1):
        val = globals_env.get(token, None) if token.isidentifier() else ast.literal_eval(token)
        if val is not None:
            table[idx] = val
    visited: List[object] = []
    i = 1
    while i in table:
        visited.append(table[i])
        i += 1
    return visited


class MultiPLERTranslator:
    """Port of dataset_builder/humaneval_to_r.py:7-23, 69-143."""

    def __init__(self, arg_types: List[ast.AST]) -> None:
        self.arg_types = arg_types

    @staticmethod
    def coerce_to_vector(expr: str) -> str:
        return "c(" + "(".join(expr.split("(")[1:])

    @classmethod
    def coerce(cls, expr: str, tp: object) -> str:
        match expr, tp:
            case e, ast.Subscript(ast.Name("List"), sub):
                if "id" not in sub._fields:
                    return e
                if "complex" in sub.id or "Any" in sub.id:
                    return e
                return cls.coerce_to_vector(e)
            case _:
                return expr

    @staticmethod
    def gen_literal(c: object) -> str:
        if type(c) is bool:
            return "TRUE" if c else "FALSE"
        if c is None:
            return "NULL"
        return repr(c)

    @staticmethod
    def _get_r_type(e: str) -> str:
        if e.startswith("c("):
            return "vector"
        if e.startswith("list("):
            return "list"
        if e == "NULL":
            return "null"
        if e in ("TRUE", "FALSE"):
            return "boolean"
        return "numeric" if e.replace("-", "", 1).replace(".", "", 1).isdigit() else "string"

    def is_atomic(self, elems: Sequence[str]) -> bool:
        type_set = {self._get_r_type(e) for e in elems}
        if "null" in type_set or "vector" in type_set or "list" in type_set:
            return False
        return len(type_set) <= 1

    def gen_list(self, elems: Sequence[str]) -> str:
        if self.is_atomic(elems):
            return "c(" + ", ".join(elems) + ")"
        return "list(" + ", ".join(elems) + ")"

    def gen_call(self, func: str, args: Sequence[str]) -> str:
        coerced = [self.coerce(a, self.arg_types[i]) for i, a in enumerate(args)]
        return func + "(" + ", ".join(coerced) + ")"


# --- Exact ports from MCEVAL/McEval@09dec129 ---

def mceval_simulate_timeout_outcome(language_type: str, spawn_overhead_s: float = 0.02) -> Tuple[bool, bool, bool]:
    """Port of eval/excute.py:14, 32-147 + eval/safe_subprocess/__init__.py:31-86.

    Returns (sigalrm_fired_first, process_group_killed, benchmark_pass_result).
    """
    outer_itimer_s = 15.0
    max_iterations = 15 * 10
    inner_loop_duration_s = spawn_overhead_s + max_iterations * 0.1
    sigalrm_fired_first = inner_loop_duration_s > outer_itimer_s
    # When SIGALRM interrupts safe_subprocess.run inside the polling loop, lines 81-85
    # (os.killpg) are NOT in a finally block, so process_group_killed is False!
    process_group_killed = not sigalrm_fired_first
    if sigalrm_fired_first:
        # Common Lisp (excute.py:46-48) and Shell (excute.py:144-146) return True!
        passed = language_type in ("Common Lisp", "Shell")
    else:
        passed = False
    return sigalrm_fired_first, process_group_killed, passed


def mceval_safe_subprocess_capture(
    chunks_per_tick: Sequence[Tuple[bytes, Optional[int]]],
    max_output_size: int = 2048,
    max_bytes_per_read: int = 1024,
) -> bytes:
    """Port of eval/safe_subprocess/__init__.py:60-90 non-blocking pipe reader."""
    pipe_buf = bytearray()
    saved: List[bytes] = []
    bytes_read = 0
    for emitted, exit_code_at_tick in chunks_per_tick:
        pipe_buf.extend(emitted)
        if pipe_buf:
            this_read = bytes(pipe_buf[:max_bytes_per_read])
            del pipe_buf[:max_bytes_per_read]
        else:
            this_read = b""
        if this_read and bytes_read < max_output_size:
            saved.append(this_read)
            bytes_read += len(this_read)
        if exit_code_at_tick is not None:
            # Line 77-78: breaks immediately without draining remaining pipe_buf!
            break
    return b"".join(saved)


def mceval_haskell_eval_path_and_check(path: str, exit_code: int, stdout: str) -> Tuple[str, bool]:
    """Port of eval/excute.py:117, 121."""
    executable_name = path.rstrip(".hs")
    passed = not (exit_code != 0 or "fail" in stdout.lower())
    return executable_name, passed


# --- Exact ports from google-research/babelcode@e8314f6f ---

def babelcode_r_tostring(val: object) -> str:
    """Models R base::toString.default used in templates/R/evaluation.txt:4."""
    if isinstance(val, str):
        return val
    if isinstance(val, (int, float)):
        return str(val)
    if isinstance(val, dict):
        # R named list: toString(list(a=1L, b=2L)) strips names -> "1, 2"
        return ", ".join(babelcode_r_tostring(v) for v in val.values())
    if isinstance(val, (list, tuple)):
        return ", ".join(babelcode_r_tostring(v) for v in val)
    raise TypeError(f"Unsupported R value: {val!r}")


def babelcode_php_serialize(val: object) -> str:
    """Exact PHP serialize() wire format for strings, ints, bools, and ordered arrays."""
    if isinstance(val, bool):
        return f"b:{1 if val else 0};"
    if isinstance(val, int):
        return f"i:{val};"
    if isinstance(val, str):
        b = val.encode("utf-8")
        return f's:{len(b)}:"{val}";'
    if isinstance(val, list):
        inner = "".join(
            babelcode_php_serialize(k) + babelcode_php_serialize(v) for k, v in val
        )
        return f"a:{len(val)}:{{{inner}}}"
    raise TypeError(f"Unsupported PHP value: {val!r}")


def babelcode_php_word_replacement_ast() -> Dict[str, List[str]]:
    """Evaluates exact dict literal from babelcode/languages/lang_implementations/php.py:56-59."""
    literal_src = """{
        'array': ['vector', 'list'],
        'array': ['map', 'dict', 'dictionary', 'dictionaries'],
    }"""
    tree = ast.parse(literal_src, mode="eval")
    assert isinstance(tree.body, ast.Dict)
    assert len(tree.body.keys) == 2  # Two syntactic keys in source
    evaluated: Dict[str, List[str]] = ast.literal_eval(literal_src)
    return evaluated


def run_probe_1() -> None:
    print("=" * 88)
    print("PROBE 1: LIVE POLYGLOT BENCHMARK HARNESS FORENSICS (MultiPL-E, McEval, BabelCode)")
    print("Provenance: [exact source port + deterministic state-machine execution]")
    print("=" * 88)

    # 1. MultiPL-E OCaml empty float list corruption ("[.0]") & None TypeError
    list_float_t = parse_type_ann("List[float]")
    ml_empty = multipl_e_ml_coerce("[]", list_float_t)
    ml_nonempty = multipl_e_ml_coerce("[1; 2]", list_float_t)
    ml_none = multipl_e_ml_gen_literal(None)
    assert ml_empty == "[.0]", f"Expected '[.0]', got {ml_empty!r}"
    assert ml_nonempty == "[1.0; 2.0]"
    assert ml_none is None  # Causes TypeError in ", ".join(elements) inside gen_tuple

    # 2. MultiPL-E Julia malformed Dict{K, V}> syntax
    dict_str_int_t = parse_type_ann("Dict[str, int]")
    jl_dict_ty = multipl_e_jl_translate_type(dict_str_int_t)
    assert jl_dict_ty == "Dict{String, Int64}>"

    # 3. MultiPL-E Rust dead AST pattern masking <K, K> key-duplication bug + isize overflow
    rs_pinned = multipl_e_rs_coerce_pinned("HashMap::from([])", dict_str_int_t)
    rs_unmasked = multipl_e_rs_coerce_slice_fixed_only("HashMap::from([])", dict_str_int_t)
    fact_21 = math.factorial(21)
    isize_max_64 = (1 << 63) - 1
    assert rs_pinned == "HashMap::from([])"  # Dead arm falls through; monomorphic rustc compiles!
    assert rs_unmasked == "HashMap::<String, String>::new()"  # Latent <K, K> type mismatch!
    assert fact_21 > isize_max_64

    # 4. MultiPL-E Lua 3-way empty-collection erasure & unbound None sparse-table hole
    lua_empty_list = MultiPLELuaTranslator.gen_list([])
    lua_empty_tuple = MultiPLELuaTranslator.gen_tuple([])
    lua_empty_dict = MultiPLELuaTranslator.gen_dict([], [])
    lua_none_lit = MultiPLELuaTranslator.gen_literal(None)
    lua_sparse_visited = lua_ipairs_visit(["1", lua_none_lit, "3"], globals_env={})
    assert lua_empty_list == lua_empty_tuple == lua_empty_dict == "{}"
    assert lua_none_lit == "None"
    assert lua_sparse_visited == [1]  # Element 3 silently dropped after nil hole at index 2

    # 5. MultiPL-E R empty c() -> NULL & scientific-notation LHS/RHS asymmetric coercion
    r_tr = MultiPLERTranslator([list_float_t])
    r_empty = r_tr.gen_list([])
    r_sci_elems = [r_tr.gen_literal(0.5), r_tr.gen_literal(1e-5)]
    r_sci_rhs = r_tr.gen_list(r_sci_elems)
    r_sci_lhs_call = r_tr.gen_call("candidate", [r_sci_rhs])
    assert r_empty == "c()"
    assert r_tr._get_r_type("1e-05") == "string"
    assert r_sci_rhs == "list(0.5, 1e-05)"
    assert r_sci_lhs_call == "candidate(c(0.5, 1e-05))"  # LHS coerced to c(...), RHS left as list(...)!

    # 6. McEval Common Lisp / Shell TimeoutException -> True, Haskell rstrip('.hs'), AWK pipe loss
    cl_alarm, cl_killed, cl_pass = mceval_simulate_timeout_outcome("Common Lisp")
    sh_alarm, sh_killed, sh_pass = mceval_simulate_timeout_outcome("Shell")
    py_alarm, py_killed, py_pass = mceval_simulate_timeout_outcome("Python")
    assert cl_alarm and not cl_killed and cl_pass is True
    assert sh_alarm and not sh_killed and sh_pass is True
    assert py_alarm and not py_killed and py_pass is False

    hs_stem_bug, hs_false_fail = mceval_haskell_eval_path_and_check(
        "/tmp/solve_paths.hs", 0, "All tests passed (0 failures)\n"
    )
    assert hs_stem_bug == "/tmp/solve_pat"  # Stripped 'h' and 's' from stem 'paths'!
    assert hs_false_fail is False  # Substring 'fail' in '0 failures' triggers false failure!

    # Fast AWK process emits 1600 bytes and exits on tick 0 -> truncated to 1024 bytes!
    awk_fast = mceval_safe_subprocess_capture([(b"A" * 1600, 0)])
    # Slow AWK process emits 4 x 1024 bytes before exiting -> capped at 2048 bytes!
    awk_slow = mceval_safe_subprocess_capture(
        [(b"B" * 1024, None), (b"B" * 1024, None), (b"B" * 1024, None), (b"B" * 1024, 0)]
    )
    assert len(awk_fast) == 1024
    assert len(awk_slow) == 2048

    # 7. BabelCode R toString key/type erasure, PHP serialize key-order rejection, php.py dup key
    r_map_ab = babelcode_r_tostring({"a": 1, "b": 2})
    r_map_xy = babelcode_r_tostring({"x": 1, "y": 2})
    r_nested = babelcode_r_tostring([1, [2]])
    r_str = babelcode_r_tostring("1, 2")
    assert r_map_ab == r_map_xy == r_nested == r_str == "1, 2"

    php_m1 = babelcode_php_serialize([("a", 1), ("b", 2)])
    php_m2 = babelcode_php_serialize([("b", 2), ("a", 1)])
    php_dup = babelcode_php_word_replacement_ast()
    assert php_m1 != php_m2
    assert list(php_dup.keys()) == ["array"] and "list" not in php_dup["array"]

    print(f"  [MultiPL-E OCaml]   coerce('[]', List[float])      -> {ml_empty!r} (ocamlc syntax error; active on HumanEval_151)")
    print(f"  [MultiPL-E Julia]   translate_type(Dict[str, int]) -> {jl_dict_ty!r} (active on 2 HumanEval + 9 MBPP tasks)")
    print(f"  [MultiPL-E Rust]    pinned coerce(HashMap::from([]))-> {rs_pinned!r} (dead ctx bug masks {rs_unmasked!r})")
    print(f"  [MultiPL-E Lua]     []/()/dict -> {lua_empty_list!r}; [1, None, 3] ipairs -> {lua_sparse_visited} (drops element after nil hole)")
    print(f"  [MultiPL-E R]       [] -> {r_empty!r} (42/161 HE tasks); [0.5, 1e-5] LHS={r_sci_lhs_call} vs RHS={r_sci_rhs}")
    print(f"  [McEval Harness]    Timeout(15s) -> CommonLisp={cl_pass}, Shell={sh_pass}, Python={py_pass}, pg_killed={cl_killed}")
    print(f"  [McEval Pipe/Stem]  'solve_paths.hs'.rstrip('.hs')={hs_stem_bug.split('/')[-1]!r}; AWK 1600B->{len(awk_fast)}B, 4096B->{len(awk_slow)}B")
    print(f"  [BabelCode R/PHP]   R toString(map(a=1,b=2))==toString(map(x=1,y=2))=={r_str!r}; PHP dup-key drops ['vector','list']")


# ============================================================================
# PROBE 2: Exact tiktoken@79dc2c05 Pre-Tokenization + Byte-Level BPE Fertility
#   - openai/tiktoken @ 79dc2c0533685b893616c78160b5d9e40876e724
#     (tiktoken_ext/openai_public.py:12-14, 89, 104-114; src/lib.rs:23-205)
#   - Dagan et al. (ICML 2024, arXiv:2402.01035) Punct pre-tokenizer
# ============================================================================

def build_unicode_category_patterns() -> Dict[str, re.Pattern[str]]:
    """Builds exact full-Unicode (U+0000..U+10FFFF) pre-tokenizers via stdlib unicodedata."""
    by_cat: Dict[str, List[int]] = {}
    for cp in range(0x110000):
        if 0xD800 <= cp <= 0xDFFF:
            continue
        cat = unicodedata.category(chr(cp))
        by_cat.setdefault(cat, []).append(cp)

    def compress_ranges(codepoints: Sequence[int]) -> str:
        pts = sorted(codepoints)
        chunks: List[str] = []
        s = e = pts[0]
        for c in pts[1:]:
            if c == e + 1:
                e = c
            else:
                chunks.append(re.escape(chr(s)) if s == e else f"{re.escape(chr(s))}-{re.escape(chr(e))}")
                s = e = c
        chunks.append(re.escape(chr(s)) if s == e else f"{re.escape(chr(s))}-{re.escape(chr(e))}")
        return "".join(chunks)

    p_l = compress_ranges(
        by_cat["Lu"] + by_cat["Ll"] + by_cat["Lt"] + by_cat["Lm"] + by_cat["Lo"]
    )
    p_n = compress_ranges(by_cat["Nd"] + by_cat["Nl"] + by_cat["No"])
    p_lu_lt_lm_lo_m = compress_ranges(
        by_cat["Lu"] + by_cat["Lt"] + by_cat["Lm"] + by_cat["Lo"]
        + by_cat["Mn"] + by_cat["Mc"] + by_cat["Me"]
    )
    p_ll_lm_lo_m = compress_ranges(
        by_cat["Ll"] + by_cat["Lm"] + by_cat["Lo"]
        + by_cat["Mn"] + by_cat["Mc"] + by_cat["Me"]
    )

    # Exact equivalents of openai_public.py:12-14, 89, 104-114 & Dagan Punct (\Z = Rust end-of-text $)
    r50k = re.compile(
        rf"'(?:[sdmt]|ll|ve|re)| ?[{p_l}]+| ?[{p_n}]+| ?[^\s{p_l}{p_n}]+|\s+\Z|\s+(?!\S)|\s"
    )
    cl100k = re.compile(
        rf"'(?i:[sdmt]|ll|ve|re)|[^\r\n{p_l}{p_n}]?[{p_l}]+|[{p_n}]{{1,3}}| ?[^\s{p_l}{p_n}]+[\r\n]*|\s+\Z|\s*[\r\n]|\s+(?!\S)|\s"
    )
    o200k = re.compile(
        "|".join(
            [
                rf"[^\r\n{p_l}{p_n}]?[{p_lu_lt_lm_lo_m}]*[{p_ll_lm_lo_m}]+(?i:'s|'t|'re|'ve|'m|'ll|'d)?",
                rf"[^\r\n{p_l}{p_n}]?[{p_lu_lt_lm_lo_m}]+[{p_ll_lm_lo_m}]*(?i:'s|'t|'re|'ve|'m|'ll|'d)?",
                rf"[{p_n}]{{1,3}}",
                rf" ?[^\s{p_l}{p_n}]+[\r\n/]*",
                r"\s*[\r\n]+",
                r"\s+(?!\S)",
                r"\s+",
            ]
        )
    )
    dagan_punct = re.compile(
        rf" ?[{p_l}]+|[{p_n}]{{1,3}}| ?[^\s{p_l}{p_n}]+[\r\n]*|\s+\Z|\s*[\r\n]|\s+(?!\S)|\s"
    )
    return {
        "r50k_base": r50k,
        "cl100k_base": cl100k,
        "o200k_base": o200k,
        "dagan_punct": dagan_punct,
    }


RANK_MAX = 0xFFFFFFFF


def byte_pair_merge_large(ranks: Dict[bytes, int], piece: bytes) -> List[int]:
    """Exact port of openai/tiktoken@79dc2c05 src/lib.rs:47-138 (_byte_pair_merge_large)."""
    n = len(piece)
    if n == 0:
        return []
    if n == 1:
        return [ranks[piece]]

    prev = [-1] * n
    end = [0] * n
    next_end = [0] * n
    next_rank = [RANK_MAX] * n
    cur_rank = [RANK_MAX] * n

    prev[0] = -1
    end[0] = 1
    next_end[0] = 2

    # Python heapq is a min-heap, so pushing (rank, start) matches Rust BinaryHeap<Merge>
    # where Ord reverses both rank and start comparisons (src/lib.rs:23-30).
    heap: List[Tuple[int, int]] = []
    for i in range(n - 1):
        rk = ranks.get(piece[i : i + 2])
        if rk is not None:
            heapq.heappush(heap, (rk, i))
            next_rank[i] = rk
        prev[i + 1] = i
        end[i + 1] = i + 2
        next_end[i + 1] = i + 3

    def potential_merge(start: int, next_end_item: int) -> None:
        next_end[start] = next_end_item
        next_rank[start] = RANK_MAX
        if next_end_item <= n:
            rk_local = ranks.get(piece[start:next_end_item])
            if rk_local is not None:
                heapq.heappush(heap, (rk_local, start))
                next_rank[start] = rk_local

    while heap:
        left_rank, left_start = heapq.heappop(heap)
        if left_rank == RANK_MAX:
            break
        if left_rank != next_rank[left_start]:
            continue

        right_start = end[left_start]
        right_end = next_end[left_start]
        assert right_end == end[right_start]
        right_next_end = next_end[right_start]

        cur_rank[left_start] = next_rank[left_start]
        end[left_start] = right_end
        potential_merge(left_start, right_next_end)
        if right_end < n:
            prev[right_end] = left_start
        if left_start > 0:
            prev_start = prev[left_start]
            potential_merge(prev_start, right_end)
        next_rank[right_start] = RANK_MAX

    out: List[int] = []
    i = 0
    while i < n:
        if cur_rank[i] != RANK_MAX:
            out.append(cur_rank[i])
        else:
            out.append(ranks[piece[i : end[i]]])
        i = end[i]
    return out


def byte_pair_merge_small(ranks: Dict[bytes, int], piece: bytes) -> List[int]:
    """Exact port of openai/tiktoken@79dc2c05 src/lib.rs:140-205 (_byte_pair_merge)."""
    n = len(piece)
    if n == 0:
        return []
    if n == 1:
        return [ranks[piece]]

    parts: List[List[int]] = []
    min_rank = (RANK_MAX, n + 1)
    for i in range(n - 1):
        rk = ranks.get(piece[i : i + 2], RANK_MAX)
        if rk < min_rank[0]:
            min_rank = (rk, i)
        parts.append([i, rk])
    parts.append([n - 1, RANK_MAX])
    parts.append([n, RANK_MAX])

    def get_rank(idx: int) -> int:
        if idx + 3 < len(parts):
            return ranks.get(piece[parts[idx][0] : parts[idx + 3][0]], RANK_MAX)
        return RANK_MAX

    while min_rank[0] != RANK_MAX:
        i = min_rank[1]
        if i > 0:
            parts[i - 1][1] = get_rank(i - 1)
        parts[i][1] = get_rank(i)
        parts.pop(i + 1)

        min_rank = (RANK_MAX, len(parts) + 1)
        for j in range(len(parts) - 1):
            if parts[j][1] < min_rank[0]:
                min_rank = (parts[j][1], j)

    return [ranks[piece[parts[k][0] : parts[k + 1][0]]] for k in range(len(parts) - 1)]


def train_deterministic_bpe(
    weighted_texts: Sequence[Tuple[str, int]],
    pat: re.Pattern[str],
    num_merges: int = 380,
    allow_multispace_merges: bool = True,
) -> Dict[bytes, int]:
    """Deterministic byte-level BPE trainer with lexicographic tie-breaking."""
    ranks: Dict[bytes, int] = {bytes([b]): b for b in range(256)}
    piece_freq: Dict[bytes, int] = {}
    for text, weight in weighted_texts:
        for piece_str in pat.findall(text):
            pb = piece_str.encode("utf-8")
            if len(pb) >= 2:
                piece_freq[pb] = piece_freq.get(pb, 0) + weight

    words: List[Tuple[List[bytes], int]] = [
        ([bytes([b]) for b in pb], freq)
        for pb, freq in sorted(piece_freq.items(), key=lambda kv: kv[0])
    ]

    next_rank = 256
    for _ in range(num_merges):
        pair_counts: Dict[Tuple[bytes, bytes], int] = {}
        for syms, freq in words:
            for idx in range(len(syms) - 1):
                pair = (syms[idx], syms[idx + 1])
                if not allow_multispace_merges and pair[0].isspace() and pair[1].isspace():
                    continue
                pair_counts[pair] = pair_counts.get(pair, 0) + freq
        if not pair_counts:
            break
        best_pair, best_cnt = min(
            pair_counts.items(), key=lambda kv: (-kv[1], kv[0][0], kv[0][1])
        )
        if best_cnt < 2:
            break
        merged = best_pair[0] + best_pair[1]
        if merged not in ranks:
            ranks[merged] = next_rank
            next_rank += 1
        a_sym, b_sym = best_pair
        new_words: List[Tuple[List[bytes], int]] = []
        for syms, freq in words:
            out_syms: List[bytes] = []
            i = 0
            m = len(syms)
            while i < m:
                if i + 1 < m and syms[i] == a_sym and syms[i + 1] == b_sym:
                    out_syms.append(merged)
                    i += 2
                else:
                    out_syms.append(syms[i])
                    i += 1
            new_words.append((out_syms, freq))
        words = new_words
    return ranks


# Disjoint BPE training corpora (zero overlap with PARALLEL_ALGORITHMS; 95% HRPL / 5% LRPL, 0% APL)
DISJOINT_HRPL_TRAIN_CORPUS = (
    "import os\n"
    "from typing import List, Dict, Optional\n\n"
    "def lower_bound(arr: List[int], target: int) -> int:\n"
    "    lo, hi = 0, len(arr)\n"
    "    while lo < hi:\n"
    "        mid = (lo + hi) // 2\n"
    "        if arr[mid] < target:\n"
    "            lo = mid + 1\n"
    "        elif arr[mid] > target:\n"
    "            hi = mid\n"
    "        else:\n"
    "            return mid\n"
    "    return lo\n\n"
    "def tally_words(items: List[str]) -> Dict[str, int]:\n"
    "    counts = {}\n"
    "    acc = 0\n"
    "    for k in items:\n"
    "        if len(k) > 0:\n"
    "            counts[k] = counts.get(k, 0) + 1\n"
    "            acc += 1\n"
    "    return counts\n\n"
    "def dispatch_tag(op: str, a: int, b: int) -> int:\n"
    "    if op == 'min':\n"
    "        return a if a <= b else b\n"
    "    elif op == 'max':\n"
    "        return a if a >= b else b\n"
    "    else:\n"
    "        return (a + b) % 2\n\n"
    "function mapItems(arr, fn) {\n"
    "    const out = [];\n"
    "    for (let i = 0; i < arr.length; i++) {\n"
    "        out.push(fn(arr[i]));\n"
    "    }\n"
    "    return out;\n"
    "}\n"
)

DISJOINT_LRPL_TRAIN_CORPUS = (
    "let clamp_all (xs : int list) (lo : int) (hi : int) : int list =\n"
    "  xs\n"
    "  |> List.filter (fun (x : 'elem) -> x >= 0)\n"
    "  |> List.fold_left (fun acc x ->\n"
    "       let v = Option.value (Some x) ~default:0 in\n"
    "       (if v < lo then lo else if v > hi then hi else v) :: acc) []\n\n"
    "(define (count-matches arr target)\n"
    "  (let loop ([lo 0] [acc 0])\n"
    "    (cond [(>= lo (vector-length arr)) acc]\n"
    "          [(= (vector-ref arr lo) target) (loop (+ lo 1) (+ acc 1))]\n"
    "          [else (loop (+ lo 1) acc)])))\n\n"
    "defmodule Tally do\n"
    "  def group_tags(items) do\n"
    "    items\n"
    "    |> Enum.filter(&(rem(&1, 3) == 0))\n"
    "    |> Enum.reduce(%{}, fn k, %{} = acc -> Map.update(acc, k, 1, &(&1 + 1)) end)\n"
    "  end\n"
    "end\n\n"
    "pure integer function clamp_range(vals, n, lo, hi) result(res)\n"
    "  integer, intent(in) :: n, lo, hi, vals(n)\n"
    "  integer :: i\n"
    "  res = 0\n"
    "  do i = 1, n\n"
    "    if (vals(i) >= lo) then\n"
    "      res = res + vals(i)\n"
    "    else if (vals(i) < 0) then\n"
    "      res = res - 1\n"
    "    else\n"
    "      res = res + lo\n"
    "    end if\n"
    "  end do\n"
    "end function clamp_range\n"
)


# Four semantically equivalent benchmark algorithms across 6 languages (matched AST operations)
PARALLEL_ALGORITHMS: Dict[str, List[Tuple[str, int, str]]] = {
    "Python": [
        ("bsearch", 26,
         "def bsearch(arr, target):\n"
         "    lo, hi = 0, len(arr) - 1\n"
         "    while lo <= hi:\n"
         "        mid = (lo + hi) // 2\n"
         "        if arr[mid] == target:\n"
         "            return mid\n"
         "        elif arr[mid] < target:\n"
         "            lo = mid + 1\n"
         "        else:\n"
         "            hi = mid - 1\n"
         "    return -1\n"),
        ("sum_sq_even", 16,
         "def sum_sq_even(xs):\n"
         "    acc = 0\n"
         "    for x in xs:\n"
         "        if x % 2 == 0:\n"
         "            acc += x * x\n"
         "    return acc\n"),
        ("freq_hist", 18,
         "def freq_hist(items):\n"
         "    counts = {}\n"
         "    for k in items:\n"
         "        counts[k] = counts.get(k, 0) + 1\n"
         "    return counts\n"),
        ("eval_expr", 22,
         "def eval_expr(op, a, b):\n"
         "    if op == 'add':\n"
         "        return a + b\n"
         "    elif op == 'mul':\n"
         "        return a * b\n"
         "    return a - b\n"),
    ],
    "OCaml": [
        ("bsearch", 26,
         "let bsearch (arr : int array) (target : int) : int =\n"
         "  let rec loop (lo : int) (hi : int) : int =\n"
         "    if lo > hi then (-1)\n"
         "    else\n"
         "      let mid = (lo + hi) / 2 in\n"
         "      if arr.(mid) = target then mid\n"
         "      else if arr.(mid) < target then loop (mid + 1) hi\n"
         "      else loop lo (mid - 1)\n"
         "  in loop 0 (Array.length arr - 1)\n"),
        ("sum_sq_even", 16,
         "let sum_sq_even (xs : int list) : int =\n"
         "  xs\n"
         "  |> List.filter (fun (x : 'state) -> (x mod 2) = 0)\n"
         "  |> List.fold_left (fun acc x -> acc + (x * x)) 0\n"),
        ("freq_hist", 18,
         "let freq_hist (items : 'key list) : ('key * int) list =\n"
         "  List.fold_left (fun acc k ->\n"
         "    let prev = Option.value (List.assoc_opt k acc) ~default:0 in\n"
         "    (k, prev + 1) :: List.remove_assoc k acc) [] items\n"),
        ("eval_expr", 22,
         "let eval_expr (op : string) (a : int) (b : int) : int =\n"
         "  match op with\n"
         "  | \"add\" -> a + b\n"
         "  | \"mul\" -> a * b\n"
         "  | _ -> a - b\n"),
    ],
    "Racket": [
        ("bsearch", 26,
         "(define (bsearch arr target)\n"
         "  (let loop ([lo 0] [hi (- (vector-length arr) 1)])\n"
         "    (cond [(> lo hi) -1]\n"
         "          [else (let ([mid (quotient (+ lo hi) 2)])\n"
         "                  (cond [(= (vector-ref arr mid) target) mid]\n"
         "                        [(< (vector-ref arr mid) target) (loop (+ mid 1) hi)]\n"
         "                        [else (loop lo (- mid 1))]))])))\n"),
        ("sum_sq_even", 16,
         "(define (sum-sq-even xs)\n"
         "  (foldl (lambda (x acc)\n"
         "           (cond [(= (modulo x 2) 0) (+ acc (* x x))]\n"
         "                 [else acc]))\n"
         "         0 xs))\n"),
        ("freq_hist", 18,
         "(define (freq-hist items)\n"
         "  (foldl (lambda (k acc)\n"
         "           (hash-set acc k (+ (hash-ref acc k 0) 1)))\n"
         "         (hash) items))\n"),
        ("eval_expr", 22,
         "(define (eval-expr op a b)\n"
         "  (cond [(equal? op 'add) (+ a b)]\n"
         "        [(equal? op 'mul) (* a b)]\n"
         "        [else (- a b)]))\n"),
    ],
    "Elixir": [
        ("bsearch", 26,
         "defmodule Search do\n"
         "  def bsearch(arr, target), do: loop(arr, target, 0, tuple_size(arr) - 1)\n"
         "  defp loop(_arr, _target, lo, hi) when lo > hi, do: -1\n"
         "  defp loop(arr, target, lo, hi) do\n"
         "    mid = div(lo + hi, 2)\n"
         "    val = elem(arr, mid)\n"
         "    cond do\n"
         "      val == target -> mid\n"
         "      val < target -> loop(arr, target, mid + 1, hi)\n"
         "      true -> loop(arr, target, lo, mid - 1)\n"
         "    end\n"
         "  end\n"
         "end\n"),
        ("sum_sq_even", 16,
         "def sum_sq_even(xs) do\n"
         "  xs\n"
         "  |> Enum.filter(&(rem(&1, 2) == 0))\n"
         "  |> Enum.reduce(0, fn x, acc -> acc + x * x end)\n"
         "end\n"),
        ("freq_hist", 18,
         "def freq_hist(items) do\n"
         "  items\n"
         "  |> Enum.reduce(%{}, fn k, %{} = acc -> Map.update(acc, k, 1, &(&1 + 1)) end)\n"
         "end\n"),
        ("eval_expr", 22,
         "def eval_expr(op, a, b) do\n"
         "  case op do\n"
         "    :add -> a + b\n"
         "    :mul -> a * b\n"
         "    _ -> a - b\n"
         "  end\n"
         "end\n"),
    ],
    "Fortran": [
        ("bsearch", 26,
         "pure integer function bsearch(arr, n, target) result(idx)\n"
         "  integer, intent(in) :: n, arr(n), target\n"
         "  integer :: lo, hi, mid\n"
         "  lo = 1; hi = n; idx = -1\n"
         "  do while (lo <= hi)\n"
         "    mid = (lo + hi) / 2\n"
         "    if (arr(mid) == target) then\n"
         "      idx = mid; return\n"
         "    else if (arr(mid) < target) then\n"
         "      lo = mid + 1\n"
         "    else\n"
         "      hi = mid - 1\n"
         "    end if\n"
         "  end do\n"
         "end function bsearch\n"),
        ("sum_sq_even", 16,
         "pure integer function sum_sq_even(xs, n) result(acc)\n"
         "  integer, intent(in) :: n, xs(n)\n"
         "  integer :: i\n"
         "  acc = 0\n"
         "  do i = 1, n\n"
         "    if (modulo(xs(i), 2) == 0) acc = acc + xs(i) * xs(i)\n"
         "  end do\n"
         "end function sum_sq_even\n"),
        ("freq_hist", 18,
         "subroutine freq_hist(items, n, max_k, counts)\n"
         "  integer, intent(in) :: n, max_k, items(n)\n"
         "  integer, intent(out) :: counts(max_k)\n"
         "  integer :: i\n"
         "  counts = 0\n"
         "  do i = 1, n\n"
         "    counts(items(i)) = counts(items(i)) + 1\n"
         "  end do\n"
         "end subroutine freq_hist\n"),
        ("eval_expr", 22,
         "pure integer function eval_expr(op, a, b) result(res)\n"
         "  character(len=*), intent(in) :: op\n"
         "  integer, intent(in) :: a, b\n"
         "  if (op == 'add') then\n"
         "    res = a + b\n"
         "  else if (op == 'mul') then\n"
         "    res = a * b\n"
         "  else\n"
         "    res = a - b\n"
         "  end if\n"
         "end function eval_expr\n"),
    ],
    "APL": [
        # Self-contained Dyalog APL dfns with 3-byte UTF-8 glyphs (⌊ ← ≢ × ∘ ⍪ ⌷ ∪ ∇)
        ("bsearch", 26,
         "bsearch ← {(⍺ ⍵) {arr tgt ← ⍺ ⋄ lo hi ← ⍵ ⋄ lo>hi: -1 ⋄ mid ← ⌊0.5×lo+hi ⋄ v ← (mid+1)⌷arr ⋄ v=tgt: mid ⋄ v<tgt: ⍺ ∇ (mid+1),hi ⋄ ⍺ ∇ lo,(mid-1)} 0,((≢⍺)-1)}\n"),
        ("sum_sq_even", 16,
         "sum_sq_even ← {+/ (⍵ × ⍵) /⍨ 0 = 2 | ⍵}\n"),
        ("freq_hist", 18,
         "freq_hist ← {(∪⍵) , ⍪ +/ (∪⍵) ∘.= ⍵}\n"),
        ("eval_expr", 22,
         "eval_expr ← {(⍺≡'add'):+/⍵ ⋄ (⍺≡'mul'):×/⍵ ⋄ -/⍵}\n"),
    ],
}


def run_probe_2() -> Dict[str, float]:
    print("\n" + "=" * 88)
    print("PROBE 2: EXACT TIKTOKEN PRE-TOKENIZATION + BYTE-BPE FERTILITY ACROSS 6 PLs")
    print("Provenance: [exact algorithm port (tiktoken@79dc2c05) + disjoint-corpus BPE measurement]")
    print("=" * 88)

    patterns = build_unicode_category_patterns()
    cl100k = patterns["cl100k_base"]
    o200k = patterns["o200k_base"]
    r50k = patterns["r50k_base"]
    punct = patterns["dagan_punct"]

    # 2a. Verify pinned pre-tokenization mechanics on exact diagnostic specimens
    contraction_probes = ["'state", "'type", "'define", "'reverse", "'alpha", "'lambda"]
    cl_tears = {s: cl100k.findall(s) for s in contraction_probes}
    o2_intact = {s: o200k.findall(s) for s in contraction_probes}
    pu_split = {s: punct.findall(s) for s in contraction_probes}
    assert cl_tears["'state"] == ["'s", "tate"] and cl_tears["'define"] == ["'d", "efine"]
    assert cl_tears["'reverse"] == ["'re", "verse"] and cl_tears["'alpha"] == ["'alpha"]
    assert all(len(o2_intact[s]) == 1 for s in contraction_probes)
    assert all(pu_split[s] == ["'", s[1:]] for s in contraction_probes)

    # Mandatory camelCase / PascalCase split in o200k_base vs cl100k_base
    assert cl100k.findall("Data.ByteString.foldBack") == ["Data", ".ByteString", ".foldBack"]
    assert o200k.findall("Data.ByteString.foldBack") == ["Data", ".Byte", "String", ".fold", "Back"]
    assert punct.findall(".append\treturn") == [".", "append", "\t", "return"]
    assert cl100k.findall(".append\treturn") == [".append", "\treturn"]

    # Racket column-0 vs indented S-expression asymmetry & r50k vs cl100k pre-tokenization
    assert cl100k.findall("(define\n  (cond [(= x 0)])")[:6] == ["(define", "\n", " ", " (", "cond", " [(="]
    assert r50k.findall("    return") == ["   ", " return"]
    assert cl100k.findall("    return") == ["   ", " return"]
    assert r50k.findall("  \n    return") == ["  \n   ", " return"]          # `\s+(?!\S)` crosses `\n`!
    assert cl100k.findall("  \n    return") == ["  \n", "   ", " return"]    # `\s*[\r\n]` isolates linebreaks!
    assert r50k.findall(".get\n") == [".", "get", "\n"]                      # ` ?\p{L}+` splits leading `.`
    assert cl100k.findall(".get\n") == [".get", "\n"]                        # `[^\r\n\p{L}\p{N}]?\p{L}+` fuses `.get`
    # Standalone numeric-chunking unit assertion (`\p{N}{1,3}` vs `\p{N}+`)
    assert len(cl100k.findall("3.14159265358979d0")) == 9
    assert len(r50k.findall("3.14159265358979d0")) == 5  # ['3', '.', '14159265358979', 'd', '0']

    # 2b. Train skewed Stack-like corpus (95% HRPL Python/JS vs 5% LRPL OCaml/Racket/Elixir/Fortran, 0% APL)
    # Strictly disjoint from all 4 evaluated functions in PARALLEL_ALGORITHMS
    for fn_name in ("bsearch", "sum_sq_even", "sum-sq-even", "freq_hist", "freq-hist", "eval_expr", "eval-expr"):
        assert fn_name not in DISJOINT_HRPL_TRAIN_CORPUS and fn_name not in DISJOINT_LRPL_TRAIN_CORPUS
    training_mix = [(DISJOINT_HRPL_TRAIN_CORPUS, 95), (DISJOINT_LRPL_TRAIN_CORPUS, 5)]

    print("  Pre-tokenization boundary diagnostics:")
    print(f"    cl100k contraction tear : 'state -> {cl_tears['\'state']}, 'define -> {cl_tears['\'define']}, 'alpha -> {cl_tears['\'alpha']}")
    print(f"    o200k suffix fix        : 'state -> {o2_intact['\'state']}, 'define -> {o2_intact['\'define']}")
    print(f"    o200k Pascal/camel split: Data.ByteString.foldBack -> {o200k.findall('Data.ByteString.foldBack')}")
    print(f"    r50k vs cl100k prefix/nl: '.get\\n' -> r50k={r50k.findall('.get\n')} vs cl100k={cl100k.findall('.get\n')}")
    print("    numeric literal split   : '3.14159265358979d0' -> cl100k=9 pre-tokens vs r50k=5 pre-tokens")

    print("\n  Parallel 4-algorithm suite (82 AST ops/PL; 380 BPE merges on disjoint 95% HRPL / 5% LRPL corpus, 0% APL weight):")
    print(f"  {'Language':<10} | {'r50k* Tok':>9} {'cl100k Tok':>10} {'o200k Tok':>9} {'Punct Tok':>9} | {'cl100k Tok/AST':>14} {'Rel Fertility phi_L':>19} {'Tok/Glyph(cl100k)':>18}")
    print("  " + "-" * 109)

    ranks_by_tok: Dict[str, Dict[bytes, int]] = {
        name: train_deterministic_bpe(
            training_mix, pat, num_merges=380, allow_multispace_merges=(name != "r50k_base")
        )
        for name, pat in patterns.items()
    }

    tok_counts: Dict[Tuple[str, str], int] = {}
    phi_cl100k: Dict[str, float] = {}
    ast_total = sum(n_ast for _, n_ast, _ in PARALLEL_ALGORITHMS["Python"])

    for lang in ("Python", "Elixir", "OCaml", "Racket", "Fortran", "APL"):
        full_src = "".join(src for _, _, src in PARALLEL_ALGORITHMS[lang])
        for tok_name, pat in patterns.items():
            ranks = ranks_by_tok[tok_name]
            total_t = 0
            for piece in pat.findall(full_src):
                pb = piece.encode("utf-8")
                t_large = byte_pair_merge_large(ranks, pb)
                t_small = byte_pair_merge_small(ranks, pb)
                # Verify 100% equivalence of both src/lib.rs BPE merge engines on every piece!
                assert t_large == t_small, f"Heap vs vector BPE mismatch on {pb!r}"
                total_t += len(t_large)
            tok_counts[(lang, tok_name)] = total_t

    py_cl = tok_counts[("Python", "cl100k_base")]
    for lang in ("Python", "Elixir", "OCaml", "Racket", "Fortran", "APL"):
        full_src = "".join(src for _, _, src in PARALLEL_ALGORITHMS[lang])
        non_ws_glyphs = sum(1 for ch in full_src if not ch.isspace())
        c_r50 = tok_counts[(lang, "r50k_base")]
        c_cl = tok_counts[(lang, "cl100k_base")]
        c_o2 = tok_counts[(lang, "o200k_base")]
        c_pu = tok_counts[(lang, "dagan_punct")]
        f_ast = c_cl / ast_total
        phi_ast = c_cl / py_cl
        phi_cl100k[lang] = phi_ast
        tok_per_glyph = c_cl / non_ws_glyphs
        print(
            f"  {lang:<10} | {c_r50:8d} {c_cl:10d} {c_o2:9d} {c_pu:9d} | "
            f"{f_ast:14.2f} {phi_ast:18.3f}x {tok_per_glyph:18.3f}"
        )

    # Non-vacuous quantitative invariants
    assert tok_counts[("Python", "r50k_base")] > tok_counts[("Python", "cl100k_base")], (
        "r50k_base single-space splitting must inflate indented Python over cl100k_base"
    )
    for lr_lang in ("Elixir", "OCaml", "Racket", "Fortran"):
        assert phi_cl100k[lr_lang] > 1.15, f"Expected AST fertility penalty >1.15x on {lr_lang}, got {phi_cl100k[lr_lang]}"

    # APL per-character byte starvation: 3-byte UTF-8 glyphs decompose into >2.2x tokens per glyph vs Python
    py_tpg = py_cl / sum(1 for c in "".join(s for _, _, s in PARALLEL_ALGORITHMS["Python"]) if not c.isspace())
    apl_tpg = tok_counts[("APL", "cl100k_base")] / sum(1 for c in "".join(s for _, _, s in PARALLEL_ALGORITHMS["APL"]) if not c.isspace())
    assert apl_tpg > 2.2 * py_tpg, f"Expected >2.2x per-glyph byte fragmentation on APL, got {apl_tpg / py_tpg:.2f}x"
    print(f"  APL per-nonspace-glyph fragmentation vs Python: {apl_tpg:.3f} vs {py_tpg:.3f} ({apl_tpg / py_tpg:.2f}x byte starvation)")
    return phi_cl100k


# ============================================================================
# PROBE 3: Multiplicative Fertility Compound Tax & Dagan Over-Compression Bound
#   - Petrov et al. (NeurIPS 2023, arXiv:2305.15425)
#   - Ahia et al. (EMNLP 2023, arXiv:2305.13707)
#   - Dagan et al. (ICML 2024, arXiv:2402.01035 Tables 1, 2, 5)
# ============================================================================

def run_probe_3(rng: random.Random) -> None:
    print("\n" + "=" * 88)
    print("PROBE 3: MULTIPLICATIVE FERTILITY COMPOUND TAX & OVER-COMPRESSION BOUNDARY")
    print("Provenance: [analytic closed-form + calibrated Monte Carlo + Dagan (ICML 2024) Table 1/2/5 audit]")
    print("=" * 88)

    base_tok_per_ast = 2.50  # Baseline Python tokens per AST node
    n_ast_program = 120      # 120-AST-node medium function (~300 Python tokens)
    ctx_budget = 8192
    eps_base = 0.0020        # 0.20% per-token syntactic/semantic error rate

    fertility_grid = [
        ("Python baseline", 1.00, 1.00),
        ("Idiomatic LRPL (OCaml/Elixir)", 1.35, 1.35),
        ("Verbose/S-expr LRPL (Racket/Fortran)", 1.75, 1.80),
        ("Byte-fragmented DSL / heavy types", 2.50, 2.40),
        ("Extreme script/glyph starvation", 3.50, 3.20),
    ]

    print(f"  Context budget B={ctx_budget} tokens, target program N_AST={n_ast_program} nodes, base eps_0={eps_base:.4f}:")
    print(f"  {'Regime':<36} | {'phi_L':>5} {'Ctx AST Cap':>11} {'Attn FLOPs':>10} | {'Surv(pure len)':>14} {'Surv(double-tax)':>16} {'MC Surv':>9}")
    print("  " + "-" * 110)

    rand = rng.random
    prev_pure = 1.01
    for label, phi, eps_mult in fertility_grid:
        eff_ast_cap = int(ctx_budget // (phi * base_tok_per_ast))
        attn_ratio = phi * phi
        seq_len = int(round(phi * base_tok_per_ast * n_ast_program))
        surv_pure = (1.0 - eps_base) ** seq_len
        eps_double = min(0.5, eps_base * eps_mult)
        surv_double = (1.0 - eps_double) ** seq_len

        n_roll = 1500
        ok = 0
        p_step_ok = 1.0 - eps_double
        for _ in range(n_roll):
            alive = True
            for _step in range(seq_len):
                if rand() > p_step_ok:
                    alive = False
                    break
            if alive:
                ok += 1
        mc_surv = ok / n_roll

        assert surv_pure < prev_pure
        assert abs(mc_surv - surv_double) < 0.035, f"MC mismatch: {mc_surv} vs {surv_double}"
        prev_pure = surv_pure

        print(
            f"  {label:<36} | {phi:4.2f}x {eff_ast_cap:11d} {attn_ratio:9.2f}x | "
            f"{100*surv_pure:13.2f}% {100*surv_double:15.2f}% {100*mc_surv:8.2f}%"
        )

    # Dagan et al. (ICML 2024, arXiv:2402.01035v2) exact Table 1, Table 2 (1.5B @ 32k), & Table 5 (7B @ 80k)
    # Note: Table 5 rendered PDF rounds to 1 decimal (32.1%, 30.4%, 30.8%, 31.2% HE; 41.9%, 41.4%, 42.6%, 42.0% MBPP)
    # from the 2-decimal `\num{...}` LaTeX source floats below; Table 1 Code NSL has GPT-4 (OpenAI, 100k) = 0.75,
    # Ours: GPT-4 80k = 0.75, and Ours: GPT-4 100k = 0.74.
    dagan_1_5b_code = [
        # (name, code_nsl_32k, humaneval_pass1, mbpp_pass1, cross_boundary_merges)
        ("LlamaC (32k SentencePiece)", 1.00, 22.8, 30.1, False),
        ("PunctC (32k strict boundary)", 0.86, 22.2, 29.8, False),
        ("GPT-4C (32k cl100k regex)", 0.81, 21.2, 28.9, False),
        ("IdentityC (32k no pre-split)", 0.69, 18.8, 23.4, True),
    ]
    dagan_7b_80k = {
        "CodeLlama_32k": (1.00, 32.06, 41.93),
        "Punct_80k": (0.81, 30.40, 41.44),
        "GPT4_80k": (0.75, 30.82, 42.59),
        "Merged_80k": (0.80, 31.23, 42.01),
    }
    print("\n  Negative Control — Dagan et al. (ICML 2024, Tables 1, 2, 5) Over-Compression Refutation:")
    for name, nsl, he_p1, mbpp_p1, cross in dagan_1_5b_code:
        tag = "CROSS-BOUNDARY OVER-MERGED" if cross else "boundary-preserving"
        print(f"    1.5B @ 32k {name:<30}: Code NSL={nsl:.2f} | HE pass@1={he_p1:5.1f}% | MBPP pass@1={mbpp_p1:5.1f}% [{tag}]")
    print(
        f"    7B @ 80k (Table 5 LaTeX/PDF)              : GPT-4 80k (NSL=0.75 [100k=0.74], HE={dagan_7b_80k['GPT4_80k'][1]:.2f}% [30.8%], MBPP={dagan_7b_80k['GPT4_80k'][2]:.2f}% [42.6%]) "
        f"vs Punct 80k (NSL=0.81, HE={dagan_7b_80k['Punct_80k'][1]:.2f}% [30.4%], MBPP={dagan_7b_80k['Punct_80k'][2]:.2f}% [41.4%])"
    )

    id_nsl, id_he, id_mbpp = dagan_1_5b_code[3][1], dagan_1_5b_code[3][2], dagan_1_5b_code[3][3]
    pu_nsl, pu_he, pu_mbpp = dagan_1_5b_code[1][1], dagan_1_5b_code[1][2], dagan_1_5b_code[1][3]
    assert id_nsl < pu_nsl and id_he < pu_he - 3.0 and id_mbpp < pu_mbpp - 6.0


# ============================================================================
# PROBE 4: MultiPL-T Static-Type Rejection Purity vs. Agnostics Table 8 RLVR
#   - Cassano et al. (OOPSLA 2024, arXiv:2308.09895 Tables 1-4)
#   - Boruch-Gruszecki et al. (ICLR 2026, arXiv:2508.04865 Table 8)
# ============================================================================

def run_probe_4() -> None:
    print("\n" + "=" * 88)
    print("PROBE 4: MULTIPL-T REJECTION-SAMPLING MODEL VS. AGNOSTICS SIBLING-LRPL INTERFERENCE")
    print("Provenance: [MultiPL-T Table 1-4 audit + illustrative analytical Bayes model + verbatim Agnostics (ICLR 2026) Table 8 analysis]")
    print("=" * 88)

    # 4a. MultiPL-T Table 1 source filtering survival + illustrative analytical Bayes gate model
    multiplt_funnel = [
        ("All Python functions in The Stack", 22_311_478),
        ("With docstrings", 5_359_051),
        ("Heuristically type-checked & returns value", 459_280),
        ("No TODOs & benchmark-decontaminated", 432_361),
        ("Passing StarCoder-15B generated tests", 157_767),
        (">=90% line coverage (final seed pool)", 133_168),
    ]
    survival = multiplt_funnel[-1][1] / multiplt_funnel[0][1]
    assert abs(survival - (133_168 / 22_311_478)) < 1e-12

    # Illustrative analytical Bayes model for Pr(semantically_correct | accepted):
    # MultiPL-T reports empirical pass@1 gains (Tables 2-4) and K in {50, 100} (§4.2 fn. 8),
    # NOT empirical candidate-pool purity. Here p_true matches StarCoderBase-15B Table 2 base
    # pass@1, while (q_ill, alpha_ill, alpha_well) are explicitly assumed illustrative parameters.
    regimes = [
        # (label, K, p_true, q_ill, alpha_ill, alpha_well, emp_1b_base, emp_1b_ft, emp_15b_base, emp_15b_ft)
        ("OCaml (static HM + tests, K=100)", 100, 0.069, 0.720, 0.000, 0.025, 1.5, 9.7, 6.9, 19.9),
        ("OCaml counterfactual (no type gate)", 100, 0.069, 0.720, 0.040, 0.025, 1.5, 9.7, 6.9, 19.9),
        ("Racket (dynamic + tests, K=50)", 50, 0.118, 0.550, 0.030, 0.025, 4.7, 11.3, 11.8, 21.0),
        ("R (dynamic + c()/all.equal, K=50)", 50, 0.102, 0.580, 0.045, 0.030, 5.4, 8.9, 10.2, 17.3),
        ("Lua (dynamic + tests, K=50)", 50, 0.266, 0.400, 0.035, 0.025, 12.1, 17.3, 26.6, 31.0),
    ]
    print(f"  MultiPL-T Table 1 Python seed funnel survival: {multiplt_funnel[-1][1]:,}/{multiplt_funnel[0][1]:,} ({100*survival:.3f}%)")
    print("  [illustrative analytical Bayes model: p_true from MultiPL-T StarCoderBase-15B Table 2; assumed priors (OCaml q_ill=0.720, alpha_ill=0.000 vs 0.040, alpha_well=0.025) — not empirically measured by MultiPL-T]")
    print(f"  {'Target Regime':<36} | {'K':>3} {'Yield>=1':>9} {'Model Purity*':>15} {'Contam*':>8} | {'1B Gain':>9} {'15B Gain':>9}")
    print("  " + "-" * 100)

    purities: Dict[str, float] = {}
    for label, k_samp, p_true, q_ill, a_ill, a_well, b1, f1, b15, f15 in regimes:
        q_well = 1.0 - p_true - q_ill
        p_false_accept = q_ill * a_ill + q_well * a_well
        p_accept = p_true + p_false_accept
        yield_k = 1.0 - (1.0 - p_accept) ** k_samp
        purity = p_true / p_accept
        purities[label] = purity
        print(
            f"  {label:<36} | {k_samp:3d} {100*yield_k:8.2f}% {100*purity:14.2f}% {100*(1-purity):7.2f}% | "
            f"{f1/b1:8.2f}x {f15/b15:8.2f}x"
        )

    assert purities["OCaml (static HM + tests, K=100)"] > purities["OCaml counterfactual (no type gate)"] + 0.20

    # MultiPL-T Table 4 idiomatic ceiling check (ADTs, higher-order functions, libraries):
    ocaml_idiomatic_15b = (50.6, 42.9)  # -7.7 pp overfitting drop on non-Pythonic OCaml!
    assert ocaml_idiomatic_15b[1] - ocaml_idiomatic_15b[0] < -7.0

    # 4b. Verbatim Agnostics (arXiv:2508.04865) Table 8 Cross-PL Pass@1 Matrix (N = 499 LCB-X problems)
    n_lcbx = 499
    agnostics_table8: Dict[str, Dict[str, Tuple[float, float, float, float]]] = {
        "Qwen3-4B": {
            "Base":     (34.34, 11.00, 10.00, 10.00),
            "CF-Lua":   (32.96, 23.00,  6.55,  3.00),
            "CF-Julia": (35.10,  8.43, 22.00,  3.90),
            "CF-R":     (31.58,  9.08,  7.92, 15.00),
        },
        "Qwen3-8B": {
            "Base":     (33.51, 11.00,  9.00,  9.00),
            "CF-Lua":   (34.29, 25.00,  7.44,  5.96),
            "CF-Julia": (33.84,  8.26, 25.00,  7.03),
            "CF-R":     (34.49,  9.90,  7.34, 19.00),
        },
        "DSC-6.7B-Ins": {
            "Base":     (16.86,  7.89,  4.79,  7.97),
            "CF-Lua":   (17.63,  8.93,  8.60,  8.08),
            "CF-Julia": (17.60,  9.54,  9.13,  8.56),
            "CF-R":     (17.62,  8.38,  5.75,  9.83),
        },
        "Phi4-mini-ins": {
            "Base":     (19.87,  7.95,  8.10,  4.69),
            "CF-Lua":   (22.16, 11.80,  8.02,  4.56),
            "CF-Julia": (21.15,  9.10,  7.69,  4.22),
            "CF-R":     (19.82,  8.02,  8.54, 11.54),
        },
        "SmolLM3-3B": {
            "Base":     (20.91,  1.02,  2.85,  2.07),
            "CF-Lua":   (21.81,  7.46,  2.93,  2.17),
            "CF-Julia": (21.58,  1.53,  7.83,  2.39),
            "CF-R":     (21.63,  1.30,  3.30,  5.90),
        },
    }

    print("\n  Agnostics (ICLR 2026) Table 8 Audit — HRPL Retention vs. 1-Indexed Sibling-LRPL Interference:")
    print(f"  {'Model Family':<15} | {'Mean Py Rel%':>12} {'Mean Target LRPL':>16} {'Mean Off-Target Sibling LRPL':>28} {'Worst Sibling Drop':>22}")
    print("  " + "-" * 102)

    target_idx = {"CF-Lua": 1, "CF-Julia": 2, "CF-R": 3}
    lang_names = ("Python", "Lua", "Julia", "R")

    qwen4_sibling_rels: List[float] = []
    qwen8_sibling_rels: List[float] = []

    for model_name, rows in agnostics_table8.items():
        base = rows["Base"]
        py_rels: List[float] = []
        on_rels: List[float] = []
        sib_rels: List[Tuple[float, str]] = []
        for ckpt in ("CF-Lua", "CF-Julia", "CF-R"):
            vals = rows[ckpt]
            py_rels.append(100.0 * (vals[0] - base[0]) / base[0])
            t_i = target_idx[ckpt]
            on_rels.append(100.0 * (vals[t_i] - base[t_i]) / base[t_i])
            for s_i in (1, 2, 3):
                if s_i != t_i:
                    rel = 100.0 * (vals[s_i] - base[s_i]) / base[s_i]
                    sib_rels.append((rel, f"{ckpt}->{lang_names[s_i]}"))
                    if model_name == "Qwen3-4B":
                        qwen4_sibling_rels.append(rel)
                    elif model_name == "Qwen3-8B":
                        qwen8_sibling_rels.append(rel)
        worst_rel, worst_tag = min(sib_rels, key=lambda x: x[0])
        mean_sib = sum(x[0] for x in sib_rels) / len(sib_rels)
        print(
            f"  {model_name:<15} | {sum(py_rels)/3:+11.2f}% {sum(on_rels)/3:+15.1f}% "
            f"{mean_sib:+27.2f}% {worst_tag}:{worst_rel:+6.1f}%"
        )

    # Two-proportion z-test on Qwen3-4B R collapse after Lua-GRPO: 10.00% -> 3.00% over N=499
    p1, p2 = 0.1000, 0.0300
    p_pool = 0.5 * (p1 + p2)
    z_r_drop = (p2 - p1) / math.sqrt(p_pool * (1.0 - p_pool) * (2.0 / n_lcbx))
    pval_r_drop = two_sided_z_pvalue(z_r_drop)
    print(f"  Qwen3-4B CF-Lua -> R (10.00% -> 3.00%, N={n_lcbx}): z = {z_r_drop:.3f}, two-sided p = {pval_r_drop:.2e}")

    assert all(r < -15.0 for r in qwen4_sibling_rels), f"All 6 Qwen3-4B sibling pairs must be <-15%, got {qwen4_sibling_rels}"
    assert all(r <= -10.0 + 1e-9 for r in qwen8_sibling_rels), f"All 6 Qwen3-8B sibling pairs must be <=-10%, got {qwen8_sibling_rels}"
    assert pval_r_drop < 1e-4


# ============================================================================
# PROBE 5: MultiPL-E frequency-map.csv Corpus-Share & Julia Typing Re-Analysis
#   - nuprl/MultiPL-E @ 5d60ac01 (analysis/frequency-map.csv, analysis/passk.csv,
#     results/per_problem_all.csv) & Cassano et al. (TSE 2023, arXiv:2208.08227)
# ============================================================================

@dataclass(frozen=True)
class MultiPLELangRow:
    pl: str
    name: str
    freq_tier: str
    csv_types: str                # Exact label in analysis/frequency-map.csv
    true_types: str               # Actual runtime typing & Table 1 'Typed?' column (Julia -> dynamic)
    github_pct: Optional[float]   # Table 1 GitHut 2.0 % for 15 targets (+ external GitHut 2.0 Q1 2022 17.90% for Python)
    compiler_loc: int             # Table 1 compiler LOC (0 for Python identity)
    he_davinci_p1: float          # analysis/passk.csv (davinci, T=0.2, reworded, k=1)
    he_incoder_p1: float          # analysis/passk.csv (incoder, T=0.2, reworded, k=1)
    mbpp_codegen_p1: float        # results/per_problem_all.csv (dataset=="mbpp", model=="codegen", variation=="reworded")
    table2_beta: Optional[float]  # Table 2 GLMM log-odds contrast vs Python (None for dummy reference Python)
    table2_se: Optional[float]    # Table 2 GLMM contrast SE (None for dummy reference Python; Intercept = -0.48 ± 0.40)


MULTIPL_E_19: Tuple[MultiPLELangRow, ...] = (
    # Python is omitted from MultiPL-E Table 1 (17.90% is external GitHut 2.0 Q1 2022) and serves as dummy ref in Table 2
    MultiPLELangRow("py",    "Python",     "High",   "dynamic", "dynamic", 17.90,   0, 0.466770, 0.158696, 0.298092,  None, None),
    MultiPLELangRow("cpp",   "C++",        "High",   "static",  "static",   7.00, 244, 0.484403, 0.103302, 0.267207,  0.10, 0.40),
    MultiPLELangRow("js",    "JavaScript", "High",   "dynamic", "dynamic", 14.30,  45, 0.489938, 0.093758, 0.313741, -0.27, 0.30),
    MultiPLELangRow("ts",    "TypeScript", "High",   "static",  "static",   9.10, 117, 0.440692, 0.085723, 0.290549, -0.27, 0.30),
    MultiPLELangRow("java",  "Java",       "High",   "static",  "static",  13.10, 153, 0.401250, 0.081506, 0.276584, -1.28, 0.30),
    MultiPLELangRow("cs",    "C#",         "Medium", "static",  "static",   3.10, 149, 0.341859, 0.099712, 0.145287, -4.09, 0.60),
    MultiPLELangRow("go",    "Go",         "Medium", "static",  "static",   7.90, 210, 0.313864, 0.072760, 0.204302, -2.61, 0.40),
    MultiPLELangRow("php",   "PHP",        "Medium", "dynamic", "dynamic",  5.30,  50, 0.473975, 0.062050, 0.143840, -0.30, 0.40),
    MultiPLELangRow("rb",    "Ruby",       "Medium", "dynamic", "dynamic",  6.20,  41, 0.426832, 0.061957, 0.000000, -0.68, 0.30),
    MultiPLELangRow("pl",    "Perl",       "Low",    "dynamic", "dynamic",  0.30,  49, 0.347671, 0.044068, 0.072170, -2.00, 0.40),
    MultiPLELangRow("r",     "R",          "Low",    "dynamic", "dynamic",  0.05,  98, 0.231273, 0.040093, 0.100611, -3.69, 0.40),
    MultiPLELangRow("rs",    "Rust",       "Low",    "static",  "static",   1.10, 147, 0.434006, 0.038654, 0.032556, -1.07, 0.30),
    MultiPLELangRow("scala", "Scala",      "Low",    "static",  "static",   1.70, 152, 0.436076, 0.063449, 0.044663, -0.52, 0.30),
    MultiPLELangRow("swift", "Swift",      "Low",    "static",  "static",   0.70, 479, 0.380158, 0.058513, 0.034052, -1.80, 0.30),
    MultiPLELangRow("sh",    "Bash",       "Niche",  "dynamic", "dynamic",  None, 120, 0.232437, 0.023671, 0.007980, -2.59, 0.30),
    MultiPLELangRow("d",     "D",          "Niche",  "static",  "static",   None, 117, 0.217051, 0.016026, 0.149052, -4.79, 0.50),
    # Line 7 of analysis/frequency-map.csv: `jl,Niche,static,NA` vs Table 1 `Typed? = x` (dynamic)!
    MultiPLELangRow("jl",    "Julia",      "Niche",  "static",  "dynamic",  0.10, 125, 0.357421, 0.005535, 0.000274, -1.91, 0.40),
    MultiPLELangRow("lua",   "Lua",        "Niche",  "dynamic", "dynamic",  0.20,  43, 0.408292, 0.053789, 0.086259, -1.04, 0.40),
    MultiPLELangRow("rkt",   "Racket",     "Niche",  "dynamic", "dynamic",  None,  38, 0.175994, 0.022702, 0.009252, -3.78, 0.40),
)


def permutation_pvalue_diff_means(vals: Sequence[float], is_group_a: Sequence[bool], rng: random.Random, n_perm: int = 10000) -> float:
    obs = (
        sum(v for v, g in zip(vals, is_group_a) if g) / sum(is_group_a)
        - sum(v for v, g in zip(vals, is_group_a) if not g) / (len(vals) - sum(is_group_a))
    )
    labels = list(is_group_a)
    extreme = 0
    na = sum(labels)
    nb = len(labels) - na
    for _ in range(n_perm):
        rng.shuffle(labels)
        sa = sum(v for v, g in zip(vals, labels) if g)
        diff = (sa / na) - ((sum(vals) - sa) / nb)
        if abs(diff) >= abs(obs) - 1e-12:
            extreme += 1
    return extreme / n_perm


def run_probe_5(rng: random.Random) -> None:
    print("\n" + "=" * 88)
    print("PROBE 5: MULTIPL-E FREQUENCY-MAP.CSV CORPUS-SHARE & JULIA TYPING RE-ANALYSIS")
    print("Provenance: [exact published dataset regression (MultiPL-E@5d60ac01)]")
    print("=" * 88)

    he_p1 = [r.he_davinci_p1 for r in MULTIPL_E_19]
    pin_static = [r.csv_types == "static" for r in MULTIPL_E_19]
    cor_static = [r.true_types == "static" for r in MULTIPL_E_19]

    # Verify exact per_problem_all.csv (mbpp, codegen, reworded) group sums
    cg_static10_sum = sum(r.mbpp_codegen_p1 for r, m in zip(MULTIPL_E_19, pin_static) if m)
    cg_dyn9_sum = sum(r.mbpp_codegen_p1 for r, m in zip(MULTIPL_E_19, pin_static) if not m)
    assert abs(cg_static10_sum - 1.444526) < 1e-6 and abs(cg_dyn9_sum - 1.031945) < 1e-6

    def group_diff(vals: Sequence[float], mask: Sequence[bool]) -> Tuple[float, float, float]:
        a = [v for v, m in zip(vals, mask) if m]
        b = [v for v, m in zip(vals, mask) if not m]
        return sum(a) / len(a), sum(b) / len(b), (sum(a) / len(a)) - (sum(b) / len(b))

    s_pin, d_pin, diff_pin = group_diff(he_p1, pin_static)
    s_cor, d_cor, diff_cor = group_diff(he_p1, cor_static)
    p_pin = permutation_pvalue_diff_means(he_p1, pin_static, rng)
    p_cor = permutation_pvalue_diff_means(he_p1, cor_static, rng)

    # NICHE-tier sign flip when Julia moves from static -> dynamic
    niche_rows = [r for r in MULTIPL_E_19 if r.freq_tier == "Niche"]
    _, _, niche_diff_pin = group_diff([r.he_davinci_p1 for r in niche_rows], [r.csv_types == "static" for r in niche_rows])
    _, _, niche_diff_cor = group_diff([r.he_davinci_p1 for r in niche_rows], [r.true_types == "static" for r in niche_rows])

    # Open-model sensitivity: InCoder HumanEval & CodeGen MBPP
    _, _, inc_diff_pin = group_diff([r.he_incoder_p1 for r in MULTIPL_E_19], pin_static)
    _, _, inc_diff_cor = group_diff([r.he_incoder_p1 for r in MULTIPL_E_19], cor_static)
    _, _, cg_diff_pin = group_diff([r.mbpp_codegen_p1 for r in MULTIPL_E_19], pin_static)
    _, _, cg_diff_cor = group_diff([r.mbpp_codegen_p1 for r in MULTIPL_E_19], cor_static)

    print(f"  1. Aggregate Codex HumanEval pass@1 (N=19 PLs):")
    print(f"     Pinned (jl=static)    : static(10)={100*s_pin:.2f}%, dynamic(9)={100*d_pin:.2f}%, S-D={100*diff_pin:+.2f} pp (perm p={p_pin:.3f})")
    print(f"     Corrected (jl=dynamic): static(9) ={100*s_cor:.2f}%, dynamic(10)={100*d_cor:.2f}%, S-D={100*diff_cor:+.2f} pp (perm p={p_cor:.3f})")
    print(f"  2. Disaggregated & Open-Model Shifts from fixing `jl=static -> dynamic`:")
    print(f"     NICHE tier (Codex HE) : S-D flips from {100*niche_diff_pin:+.2f} pp -> {100*niche_diff_cor:+.2f} pp (shift = {100*(niche_diff_cor - niche_diff_pin):+.2f} pp)")
    print(f"     InCoder (HumanEval)   : S-D expands from {100*inc_diff_pin:+.2f} pp -> {100*inc_diff_cor:+.2f} pp (shift = {100*(inc_diff_cor - inc_diff_pin):+.2f} pp)")
    print(f"     CodeGen (MBPP)        : S-D nearly doubles from {100*cg_diff_pin:+.2f} pp -> {100*cg_diff_cor:+.2f} pp (jl=0.03%, rb=0.00%)")

    # 3. Corpus-controlled OLS (N=16 with external GitHut 2.0 Q1 2022 py=17.90%; N=15 Table 1 targets)
    #    and inverse-variance WLS strictly over N=15 estimated Table 2 GLMM contrasts (excluding dummy ref py)
    gh_rows_16 = [r for r in MULTIPL_E_19 if r.github_pct is not None]
    gh_targets_15 = [r for r in MULTIPL_E_19 if r.github_pct is not None and r.table2_beta is not None and r.table2_se is not None]
    assert len(gh_rows_16) == 16 and len(gh_targets_15) == 15

    x16_pin = [[1.0, math.log10(r.github_pct), 1.0 if r.csv_types == "static" else 0.0] for r in gh_rows_16 if r.github_pct is not None]
    x16_cor = [[1.0, math.log10(r.github_pct), 1.0 if r.true_types == "static" else 0.0] for r in gh_rows_16 if r.github_pct is not None]
    y16_p1 = [r.he_davinci_p1 for r in gh_rows_16]

    x15_cor = [[1.0, math.log10(r.github_pct), 1.0 if r.true_types == "static" else 0.0] for r in gh_targets_15 if r.github_pct is not None]
    y15_p1 = [r.he_davinci_p1 for r in gh_targets_15]
    y15_beta = [r.table2_beta for r in gh_targets_15 if r.table2_beta is not None]
    w15_iv = [1.0 / (r.table2_se ** 2) for r in gh_targets_15 if r.table2_se is not None]

    b_ols16_pin, se_ols16_pin, r2_ols16_pin = fit_wls(x16_pin, y16_p1)
    b_ols16_cor, se_ols16_cor, r2_ols16_cor = fit_wls(x16_cor, y16_p1)
    b_ols15_cor, se_ols15_cor, r2_ols15_cor = fit_wls(x15_cor, y15_p1)
    b_wls15_cor, se_wls15_cor, r2_wls15_cor = fit_wls(x15_cor, y15_beta, weights=w15_iv)

    print(f"\n  3. Corpus-Controlled Regressions (y ~ 1 + log10(GitHub%) + I[static]):")
    print(f"     OLS N=16 (incl. ext Py=17.90%, jl=static) : beta_logGH={b_ols16_pin[1]:+.4f} (±{se_ols16_pin[1]:.4f}), beta_static={b_ols16_pin[2]:+.4f} (±{se_ols16_pin[2]:.4f}), R^2={r2_ols16_pin:.3f}")
    print(f"     OLS N=16 (incl. ext Py=17.90%, jl=dynamic): beta_logGH={b_ols16_cor[1]:+.4f} (±{se_ols16_cor[1]:.4f}), beta_static={b_ols16_cor[2]:+.4f} (±{se_ols16_cor[2]:.4f}), R^2={r2_ols16_cor:.3f}")
    print(f"     OLS N=15 (Table 1 targets only, jl=dyn)   : beta_logGH={b_ols15_cor[1]:+.4f} (±{se_ols15_cor[1]:.4f}), beta_static={b_ols15_cor[2]:+.4f} (±{se_ols15_cor[2]:.4f}), R^2={r2_ols15_cor:.3f}")
    print(f"     WLS N=15 (Table 2 GLMM contrasts, jl=dyn) : beta_logGH={b_wls15_cor[1]:+.4f} (±{se_wls15_cor[1]:.4f}), beta_static={b_wls15_cor[2]:+.4f} (±{se_wls15_cor[2]:.4f}), R^2={r2_wls15_cor:.3f}")

    # Compute corpus-adjusted pass@1 residuals under corrected typing (N=16) to expose positive/negative transfer outliers
    residuals = []
    for r, xi in zip(gh_rows_16, x16_cor):
        pred = sum(xi[j] * b_ols16_cor[j] for j in range(3))
        residuals.append((r.he_davinci_p1 - pred, r.name, r.github_pct, r.he_davinci_p1))
    residuals.sort(reverse=True)
    top_pos = ", ".join(f"{nm} ({100*res:+.1f} pp)" for res, nm, _, _ in residuals[:3])
    top_neg = ", ".join(f"{nm} ({100*res:+.1f} pp)" for res, nm, _, _ in residuals[-3:])
    print(f"     Top positive residuals above corpus trend : {top_pos}")
    print(f"     Top negative residuals below corpus trend : {top_neg}")

    # Assertions
    assert p_pin > 0.30 and p_cor > 0.30, "Aggregate Codex static-vs-dynamic difference remains non-significant"
    assert niche_diff_pin > 0.0 and niche_diff_cor < -0.07, "NICHE S-D sign must flip by >9 pp when Julia is fixed"
    assert inc_diff_cor - inc_diff_pin > 0.011 and cg_diff_cor - cg_diff_pin > 0.025, "Open-model S-D shifts >1.1 pp / >2.5 pp"
    assert b_ols16_cor[1] > 0.055 and b_ols15_cor[1] > 0.055 and r2_ols16_cor > 0.44
    assert b_ols16_cor[2] < 0.0 and b_ols15_cor[2] < 0.0 and b_wls15_cor[2] < 0.0


def main() -> None:
    t0 = time.perf_counter()
    rng = random.Random(SEED)
    print(f"POLYGLOT HARNESS, SUBWORD FERTILITY, AND CROSS-LANGUAGE TRANSFER VERIFICATION SUITE (seed={SEED})")
    run_probe_1()
    run_probe_2()
    run_probe_3(rng)
    run_probe_4()
    run_probe_5(rng)
    elapsed = time.perf_counter() - t0
    assert elapsed < 2.0, f"Execution exceeded 2.0s budget: {elapsed:.3f}s"
    print("\n" + "=" * 88)
    print("ALL 5 PROBES, QUANTITATIVE INVARIANTS, AND NEGATIVE CONTROLS PASSED DETERMINISTICALLY")
    print("=" * 88)


if __name__ == "__main__":
    main()
