#!/usr/bin/env python3
"""Self-contained executable model for metaprogramming hygiene, reflection, and staging.

Verifies three core mechanisms documented in REPORT.md:
  (a) Flatt's Sets-of-Scopes binder resolution (POPL 2016; racket/racket scope.rkt):
      - accidental-capture prevention (macro-introduced binder vs caller argument),
      - reverse-capture prevention (caller shadowing macro's definition-site reference),
      - intentional anaphoric capture via syntax-context transfer (datum->syntax),
      - incomparable-scope ambiguity detection and unique-superset disambiguation,
      - homonym distinctness across hygiene contexts (motivating Identity<Type = T>).
  (b) Pre-resolution token-stream macros vs. post-resolution semantic reflection:
      - outside-in attribute mutation invalidating an earlier derive unsafe impl,
      - nondeterministic type-macro re-expansion diverging between bound and field,
      - raw-identifier lexical drift (`#[r#repr(r#align(8))]`) bypassing token matchers,
      - post-resolution semantic MetaInfo reflection catching all three hazards.
  (c) Multi-stage scope-extrusion detection:
      - static 2-stage environment-classifier typing (Taha & Nielsen 2003;
        Kameyama, Kiselyov, & Shan 2008/2011) rejecting ref-cell extrusion and
        open-code execution at generator compile time,
      - dynamic stackmark free-variable tracking (BER MetaOCaml typing/trx.ml)
        catching both ref-cell and exception-driven extrusion eagerly at generator
        runtime while accepting valid staged code generation (`spower`).

Requires Python 3.10+ standard library only. Exits 0 iff all assertions pass.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable


# ============================================================================
# Part (a): Flatt's Sets-of-Scopes Binding & Hygiene Model
# ============================================================================


@dataclass(frozen=True, order=True)
class Scope:
    scope_id: int
    kind: str  # e.g., "module", "local", "macro", "use-site"

    def __repr__(self) -> str:
        return f"S{self.scope_id}:{self.kind}"


@dataclass(frozen=True)
class SyntaxId:
    symbol: str
    scopes: frozenset[Scope]

    def add_scope(self, sc: Scope) -> SyntaxId:
        return SyntaxId(self.symbol, self.scopes | {sc})

    def flip_scope(self, sc: Scope) -> SyntaxId:
        if sc in self.scopes:
            return SyntaxId(self.symbol, self.scopes - {sc})
        return SyntaxId(self.symbol, self.scopes | {sc})

    def remove_scope(self, sc: Scope) -> SyntaxId:
        return SyntaxId(self.symbol, self.scopes - {sc})


@dataclass(frozen=True)
class Binding:
    binding_id: str
    origin: str


AMBIGUOUS = "AMBIGUOUS"


class SetsOfScopesEnv:
    """Faithful subset-maximality binder table modeling racket/src/expander/syntax/scope.rkt."""

    def __init__(self) -> None:
        self._next_id = 0
        self._bindings: dict[str, list[tuple[frozenset[Scope], Binding]]] = {}

    def new_scope(self, kind: str) -> Scope:
        self._next_id += 1
        return Scope(self._next_id, kind)

    def add_binding(self, binder: SyntaxId, binding: Binding) -> None:
        entries = self._bindings.setdefault(binder.symbol, [])
        for i, (sc_set, _) in enumerate(entries):
            if sc_set == binder.scopes:
                entries[i] = (binder.scopes, binding)
                return
        entries.append((binder.scopes, binding))

    def resolve(self, ident: SyntaxId) -> Binding | str | None:
        """Return unique binding whose scope set is a maximal subset of ident.scopes.

        Mirrors Racket's `resolve` (scope.rkt:1022-1098): if two matching candidate
        scope sets are incomparable and no matching candidate is a superset of all
        of them, returns AMBIGUOUS.
        """
        candidates = [
            (b_scopes, binding)
            for b_scopes, binding in self._bindings.get(ident.symbol, [])
            if b_scopes <= ident.scopes
        ]
        if not candidates:
            return None

        best_scopes: frozenset[Scope] | None = None
        best_binding: Binding | None = None
        ambiguous_sets: list[frozenset[Scope]] = []

        for b_scopes, binding in candidates:
            if ambiguous_sets:
                if all(amb <= b_scopes for amb in ambiguous_sets):
                    ambiguous_sets.clear()
                    best_scopes = b_scopes
                    best_binding = binding
                else:
                    ambiguous_sets.append(b_scopes)
            elif best_scopes is None:
                best_scopes = b_scopes
                best_binding = binding
            elif b_scopes <= best_scopes:
                continue
            elif best_scopes <= b_scopes:
                best_scopes = b_scopes
                best_binding = binding
            else:
                ambiguous_sets = [best_scopes, b_scopes]
                best_scopes = None
                best_binding = None

        if ambiguous_sets:
            return AMBIGUOUS
        return best_binding


def datum_to_syntax(ctx_stx: SyntaxId, symbol: str) -> SyntaxId:
    """Intentional hygiene-bending: construct an identifier with ctx_stx's scope set."""
    return SyntaxId(symbol, ctx_stx.scopes)


def verify_sets_of_scopes() -> dict[str, Any]:
    env = SetsOfScopesEnv()
    s_mod = env.new_scope("module")

    mod_helper_binder = SyntaxId("helper_fn", frozenset({s_mod}))
    mod_helper_binding = Binding("mod:helper_fn", "module-def")
    env.add_binding(mod_helper_binder, mod_helper_binding)

    # Case 1: Accidental capture prevention — macro `swap(a, b)` introduces `tmp`
    s_caller_let = env.new_scope("local-caller")
    caller_tmp_binder = SyntaxId("tmp", frozenset({s_mod, s_caller_let}))
    caller_tmp_binding = Binding("caller:tmp", "caller-let")
    env.add_binding(caller_tmp_binder, caller_tmp_binding)

    s_intro = env.new_scope("macro-intro")
    arg_tmp_in = caller_tmp_binder.add_scope(s_intro)
    template_tmp_raw = SyntaxId("tmp", frozenset({s_mod}))

    macro_tmp_after_flip = template_tmp_raw.flip_scope(s_intro)  # {s_mod, s_intro}
    arg_tmp_after_flip = arg_tmp_in.flip_scope(s_intro)          # {s_mod, s_caller_let}

    s_macro_let = env.new_scope("local-macro")
    macro_tmp_binder = macro_tmp_after_flip.add_scope(s_macro_let)
    macro_tmp_binding = Binding("macro:tmp", "macro-let")
    env.add_binding(macro_tmp_binder, macro_tmp_binding)

    res_macro_tmp = env.resolve(macro_tmp_after_flip.add_scope(s_macro_let))
    res_caller_arg = env.resolve(arg_tmp_after_flip.add_scope(s_macro_let))
    assert res_macro_tmp == macro_tmp_binding
    assert res_caller_arg == caller_tmp_binding

    # Case 2: Reverse-capture prevention — caller shadows `helper_fn` locally
    s_shadow_let = env.new_scope("local-shadow")
    caller_helper_binder = SyntaxId("helper_fn", frozenset({s_mod, s_shadow_let}))
    caller_helper_binding = Binding("caller:helper_fn", "caller-shadow")
    env.add_binding(caller_helper_binder, caller_helper_binding)

    s_intro2 = env.new_scope("macro-intro")
    macro_helper_ref = SyntaxId("helper_fn", frozenset({s_mod})).flip_scope(s_intro2)
    res_macro_helper = env.resolve(macro_helper_ref)
    res_caller_helper = env.resolve(caller_helper_binder)
    assert res_macro_helper == mod_helper_binding
    assert res_caller_helper == caller_helper_binding

    # Case 3: Intentional anaphoric binding (`aif` binding `it` via datum->syntax)
    s_aif_caller = env.new_scope("caller-ctx")
    caller_cond_stx = SyntaxId("cond", frozenset({s_mod, s_aif_caller}))
    caller_then_it = SyntaxId("it", frozenset({s_mod, s_aif_caller}))

    s_aif_let = env.new_scope("aif-let")
    anaphoric_it_binder = datum_to_syntax(caller_cond_stx, "it").add_scope(s_aif_let)
    anaphoric_it_binding = Binding("aif:it", "anaphoric-let")
    env.add_binding(anaphoric_it_binder, anaphoric_it_binding)

    res_anaphoric_it = env.resolve(caller_then_it.add_scope(s_aif_let))
    assert res_anaphoric_it == anaphoric_it_binding

    # Case 4: Incomparable-scope ambiguity detection & superset disambiguation
    s_a = env.new_scope("branch-a")
    s_b = env.new_scope("branch-b")
    env.add_binding(SyntaxId("amb", frozenset({s_mod, s_a})), Binding("bind:a", "a"))
    env.add_binding(SyntaxId("amb", frozenset({s_mod, s_b})), Binding("bind:b", "b"))
    amb_ref = SyntaxId("amb", frozenset({s_mod, s_a, s_b}))
    res_amb = env.resolve(amb_ref)
    assert res_amb == AMBIGUOUS

    tight_binding = Binding("bind:ab", "ab")
    env.add_binding(SyntaxId("amb", frozenset({s_mod, s_a, s_b})), tight_binding)
    res_disamb = env.resolve(amb_ref)
    assert res_disamb == tight_binding

    # Case 5: Identically spelled tokens with distinct hygiene contexts (`T` alias vs generic `T`)
    s_call_alias = env.new_scope("call-site")
    s_def_generic = env.new_scope("def-site-generic")
    t_alias_id = SyntaxId("T", frozenset({s_mod, s_call_alias}))
    t_param_id = SyntaxId("T", frozenset({s_mod, s_def_generic}))
    env.add_binding(t_alias_id, Binding("type_alias:u8", "call-site-alias"))
    env.add_binding(t_param_id, Binding("generic_param:T", "struct-generic"))
    assert t_alias_id.symbol == t_param_id.symbol == "T"
    assert env.resolve(t_alias_id) != env.resolve(t_param_id)

    return {
        "capture_prevented": (res_macro_tmp.binding_id, res_caller_arg.binding_id),
        "reverse_capture_prevented": (res_macro_helper.binding_id, res_caller_helper.binding_id),
        "anaphoric_capture_resolved": res_anaphoric_it.binding_id,
        "incomparable_ambiguity": (res_amb, res_disamb.binding_id),
        "homonym_distinct": (env.resolve(t_alias_id).binding_id, env.resolve(t_param_id).binding_id),
    }


# ============================================================================
# Part (b): Token-Stream Proc-Macro Soundness Counterexamples vs. Semantic Reflection
# ============================================================================


@dataclass(frozen=True)
class PrimitiveType:
    name: str
    size: int
    align: int
    all_bit_patterns_valid: bool


TYPES: dict[str, PrimitiveType] = {
    "u8": PrimitiveType("u8", 1, 1, True),
    "u16": PrimitiveType("u16", 2, 2, True),
    "u32": PrimitiveType("u32", 4, 4, True),
    "i32": PrimitiveType("i32", 4, 4, True),
    "&'static i32": PrimitiveType("&'static i32", 8, 8, False),
}


@dataclass
class TokenField:
    name: str
    type_token: str


@dataclass
class TokenAttr:
    name: str
    args: tuple[str, ...]


@dataclass
class TokenStruct:
    name: str
    attrs: list[TokenAttr]
    fields: list[TokenField]


@dataclass(frozen=True)
class ResolvedField:
    name: str
    ty: PrimitiveType
    offset: int


@dataclass(frozen=True)
class ResolvedStructMetaInfo:
    """Compiler-resolved semantic reflection record (std::meta::info / @typeInfo model)."""

    name: str
    repr_kind: str
    explicit_align: int
    fields: tuple[ResolvedField, ...]
    size_of: int
    alignment_of: int

    @property
    def padding_bytes(self) -> int:
        return self.size_of - sum(f.ty.size for f in self.fields)


def compute_repr_c_layout(
    name: str,
    resolved_fields: list[tuple[str, PrimitiveType]],
    explicit_align: int = 1,
) -> ResolvedStructMetaInfo:
    offset = 0
    max_align = max(1, explicit_align)
    placed: list[ResolvedField] = []
    for fname, fty in resolved_fields:
        max_align = max(max_align, fty.align)
        rem = offset % fty.align
        if rem != 0:
            offset += fty.align - rem
        placed.append(ResolvedField(fname, fty, offset))
        offset += fty.size
    rem = offset % max_align
    size = offset if rem == 0 else offset + (max_align - rem)
    return ResolvedStructMetaInfo(
        name=name,
        repr_kind="C",
        explicit_align=explicit_align,
        fields=tuple(placed),
        size_of=size,
        alignment_of=max_align,
    )


def run_token_stream_pipeline(
    item: TokenStruct,
    macro_expander: Callable[[str], str],
    normalize_raw_idents: bool = False,
) -> tuple[bool, bool, ResolvedStructMetaInfo]:
    """Simulate outside-in Rust-like token-stream derive + attribute expansion."""
    emitted_into_bytes = False
    emitted_from_bytes = False
    current = TokenStruct(item.name, list(item.attrs), list(item.fields))

    remaining_attrs: list[TokenAttr] = []
    for attr in list(current.attrs):
        if attr.name == "derive":
            explicit_align = 1
            for a in current.attrs:
                a_name = a.name.removeprefix("r#") if normalize_raw_idents else a.name
                if a_name == "repr":
                    for arg in a.args:
                        arg_norm = arg.removeprefix("r#") if normalize_raw_idents else arg
                        if arg_norm.startswith("align(") and arg_norm.endswith(")"):
                            explicit_align = max(explicit_align, int(arg_norm[6:-1]))

            if "IntoBytes" in attr.args:
                seen_fields = [(f.name, TYPES[macro_expander(f.type_token)]) for f in current.fields]
                seen_layout = compute_repr_c_layout(current.name, seen_fields, explicit_align)
                emitted_into_bytes = seen_layout.padding_bytes == 0
            if "FromBytes" in attr.args:
                bound_types = [TYPES[macro_expander(f.type_token)] for f in current.fields]
                emitted_from_bytes = all(t.all_bit_patterns_valid for t in bound_types)
        elif attr.name == "insert_field":
            fname, ftype = attr.args
            current.fields.append(TokenField(fname, ftype))
        else:
            remaining_attrs.append(attr)

    final_align = 1
    for a in remaining_attrs:
        if a.name.removeprefix("r#") == "repr":
            for arg in a.args:
                arg_norm = arg.removeprefix("r#")
                if arg_norm.startswith("align(") and arg_norm.endswith(")"):
                    final_align = max(final_align, int(arg_norm[6:-1]))

    final_fields = [(f.name, TYPES[macro_expander(f.type_token)]) for f in current.fields]
    actual_layout = compute_repr_c_layout(current.name, final_fields, final_align)
    return emitted_into_bytes, emitted_from_bytes, actual_layout


def semantic_reflection_check(meta: ResolvedStructMetaInfo) -> tuple[bool, bool]:
    """Post-resolution reflection check (C++26 P2996 std::meta::info / Zig @typeInfo model)."""
    into_bytes_ok = meta.padding_bytes == 0
    from_bytes_ok = all(f.ty.all_bit_patterns_valid for f in meta.fields)
    return into_bytes_ok, from_bytes_ok


def verify_token_macros_vs_reflection() -> dict[str, Any]:
    id_expand = lambda tok: tok

    # Counterexample 1: Outside-in attribute ordering
    s1 = TokenStruct(
        name="Mutated",
        attrs=[
            TokenAttr("repr", ("C",)),
            TokenAttr("derive", ("IntoBytes",)),
            TokenAttr("insert_field", ("baz", "u32")),
        ],
        fields=[TokenField("bar", "u8")],
    )
    tok_ib1, _, layout1 = run_token_stream_pipeline(s1, id_expand)
    ref_ib1, _ = semantic_reflection_check(layout1)
    assert tok_ib1 is True and layout1.padding_bytes == 3
    assert ref_ib1 is False

    # Counterexample 2: Nondeterministic type-macro re-expansion
    counter = {"n": 0}

    def nondet_make_type(tok: str) -> str:
        if tok != "make_type!()":
            return tok
        n = counter["n"]
        counter["n"] += 1
        return "i32" if n == 0 else "&'static i32"

    s2 = TokenStruct(
        name="Thing",
        attrs=[TokenAttr("repr", ("C",)), TokenAttr("derive", ("FromBytes",))],
        fields=[TokenField("field", "make_type!()")],
    )
    _, tok_fb2, layout2 = run_token_stream_pipeline(s2, nondet_make_type)
    _, ref_fb2 = semantic_reflection_check(layout2)
    assert tok_fb2 is True and layout2.fields[0].ty.name == "&'static i32"
    assert ref_fb2 is False

    # Counterexample 3: Raw-identifier lexical drift (`#[r#repr(r#align(8))]`)
    s3 = TokenStruct(
        name="Response",
        attrs=[
            TokenAttr("repr", ("C",)),
            TokenAttr("r#repr", ("r#align(8)",)),
            TokenAttr("derive", ("IntoBytes",)),
        ],
        fields=[TokenField("status", "u8")],
    )
    tok_ib3_unnorm, _, layout3 = run_token_stream_pipeline(s3, id_expand, normalize_raw_idents=False)
    tok_ib3_norm, _, _ = run_token_stream_pipeline(s3, id_expand, normalize_raw_idents=True)
    ref_ib3, _ = semantic_reflection_check(layout3)
    assert tok_ib3_unnorm is True and layout3.padding_bytes == 7
    assert tok_ib3_norm is False and ref_ib3 is False

    # Positive control: padding-free repr(C) struct of valid primitives
    s4 = TokenStruct(
        name="ValidPair",
        attrs=[TokenAttr("repr", ("C",)), TokenAttr("derive", ("IntoBytes", "FromBytes"))],
        fields=[TokenField("x", "u32"), TokenField("y", "u32")],
    )
    tok_ib4, tok_fb4, layout4 = run_token_stream_pipeline(s4, id_expand, normalize_raw_idents=True)
    ref_ib4, ref_fb4 = semantic_reflection_check(layout4)
    assert (tok_ib4, tok_fb4, ref_ib4, ref_fb4) == (True, True, True, True)
    assert layout4.padding_bytes == 0

    return {
        "attr_order_hazard": {"token_emitted": tok_ib1, "actual_padding": layout1.padding_bytes, "reflection_ok": ref_ib1},
        "reexpansion_hazard": {"token_emitted": tok_fb2, "actual_field_ty": layout2.fields[0].ty.name, "reflection_ok": ref_fb2},
        "raw_ident_hazard": {"naive_emitted": tok_ib3_unnorm, "actual_padding": layout3.padding_bytes, "reflection_ok": ref_ib3},
        "valid_pair": {"size": layout4.size_of, "padding": layout4.padding_bytes, "reflection_ok": (ref_ib4, ref_fb4)},
    }


# ============================================================================
# Part (c): Multi-Stage Scope-Extrusion Detection
#   (c.1) Static Environment Classifiers (Taha & Nielsen 2003; KKS 2008/2011)
#   (c.2) Dynamic Stackmark Heap (BER MetaOCaml typing/trx.ml)
# ============================================================================


class StagingTypeError(Exception):
    pass


class ScopeExtrusionTypeError(StagingTypeError):
    pass


@dataclass(frozen=True)
class Ty:
    pass


@dataclass(frozen=True)
class TInt(Ty):
    pass


@dataclass(frozen=True)
class TUnit(Ty):
    pass


@dataclass(frozen=True)
class TFun(Ty):
    arg: Ty
    ret: Ty


@dataclass(frozen=True)
class TRef(Ty):
    elem: Ty


@dataclass(frozen=True)
class TCode(Ty):
    classifier: str
    inner: Ty


@dataclass(frozen=True)
class Expr:
    pass


@dataclass(frozen=True)
class EInt(Expr):
    val: int


@dataclass(frozen=True)
class EUnit(Expr):
    pass


@dataclass(frozen=True)
class EVar(Expr):
    name: str


@dataclass(frozen=True)
class ELam(Expr):
    param: str
    param_ty: Ty
    body: Expr


@dataclass(frozen=True)
class EApp(Expr):
    fn: Expr
    arg: Expr


@dataclass(frozen=True)
class EAdd(Expr):
    lhs: Expr
    rhs: Expr


@dataclass(frozen=True)
class ELet(Expr):
    name: str
    rhs: Expr
    body: Expr


@dataclass(frozen=True)
class EBracket(Expr):
    body: Expr


@dataclass(frozen=True)
class EEscape(Expr):
    body: Expr


@dataclass(frozen=True)
class ERun(Expr):
    body: Expr


@dataclass(frozen=True)
class ENewRef(Expr):
    init: Expr


@dataclass(frozen=True)
class ESetRef(Expr):
    ref_expr: Expr
    val_expr: Expr


@dataclass(frozen=True)
class EGetRef(Expr):
    ref_expr: Expr


@dataclass(frozen=True)
class ESeq(Expr):
    first: Expr
    second: Expr


class ClassifierTypeChecker:
    """Two-stage type checker with environment classifiers and region ordering."""

    def __init__(self) -> None:
        self._fresh_counter = 0
        self._parent: dict[str, str | None] = {"gamma0": None}

    def fresh_classifier(self, parent: str) -> str:
        self._fresh_counter += 1
        c = f"gamma_{self._fresh_counter}"
        self._parent[c] = parent
        return c

    def is_sub_env(self, ancestor: str, desc: str) -> bool:
        cur: str | None = desc
        while cur is not None:
            if cur == ancestor:
                return True
            cur = self._parent.get(cur)
        return False

    def typecheck(
        self,
        expr: Expr,
        env: dict[str, tuple[int, str, Ty]],
        stage: int = 0,
        cur_classifier: str = "gamma0",
    ) -> Ty:
        if isinstance(expr, EInt):
            return TInt()
        if isinstance(expr, EUnit):
            return TUnit()
        if isinstance(expr, EVar):
            if expr.name not in env:
                raise StagingTypeError(f"Unbound variable {expr.name!r}")
            v_stage, v_cls, v_ty = env[expr.name]
            if v_stage != stage:
                raise StagingTypeError(
                    f"Stage mismatch for {expr.name!r}: bound at stage {v_stage}, used at stage {stage}"
                )
            if stage == 1 and not self.is_sub_env(v_cls, cur_classifier):
                raise ScopeExtrusionTypeError(
                    f"Variable {expr.name!r} from classifier {v_cls} escapes into {cur_classifier}"
                )
            return v_ty
        if isinstance(expr, EAdd):
            t1 = self.typecheck(expr.lhs, env, stage, cur_classifier)
            t2 = self.typecheck(expr.rhs, env, stage, cur_classifier)
            if t1 != TInt() or t2 != TInt():
                raise StagingTypeError(f"EAdd expects Int, got {t1} and {t2}")
            return TInt()
        if isinstance(expr, ELam):
            if stage == 0:
                new_env = dict(env)
                new_env[expr.param] = (0, cur_classifier, expr.param_ty)
                ret_ty = self.typecheck(expr.body, new_env, 0, cur_classifier)
                return TFun(expr.param_ty, ret_ty)
            c_inner = self.fresh_classifier(cur_classifier)
            new_env = dict(env)
            new_env[expr.param] = (1, c_inner, expr.param_ty)
            ret_ty = self.typecheck(expr.body, new_env, 1, c_inner)
            return TFun(expr.param_ty, ret_ty)
        if isinstance(expr, EApp):
            fn_ty = self.typecheck(expr.fn, env, stage, cur_classifier)
            arg_ty = self.typecheck(expr.arg, env, stage, cur_classifier)
            if not isinstance(fn_ty, TFun) or fn_ty.arg != arg_ty:
                raise StagingTypeError(f"App type mismatch: {fn_ty} applied to {arg_ty}")
            return fn_ty.ret
        if isinstance(expr, ELet):
            rhs_ty = self.typecheck(expr.rhs, env, stage, cur_classifier)
            new_env = dict(env)
            new_env[expr.name] = (stage, cur_classifier, rhs_ty)
            return self.typecheck(expr.body, new_env, stage, cur_classifier)
        if isinstance(expr, EBracket):
            if stage != 0:
                raise StagingTypeError("2-stage model forbids nested stage-2 brackets")
            inner_ty = self.typecheck(expr.body, env, 1, cur_classifier)
            return TCode(cur_classifier, inner_ty)
        if isinstance(expr, EEscape):
            if stage != 1:
                raise StagingTypeError("Escape (~) is only valid at stage 1")
            splice_ty = self.typecheck(expr.body, env, 0, cur_classifier)
            if not isinstance(splice_ty, TCode):
                raise StagingTypeError(f"Escape expects TCode, got {splice_ty}")
            if not self.is_sub_env(splice_ty.classifier, cur_classifier):
                raise ScopeExtrusionTypeError(
                    f"Cannot splice code of classifier {splice_ty.classifier} into {cur_classifier}"
                )
            return splice_ty.inner
        if isinstance(expr, ERun):
            if stage != 0:
                raise StagingTypeError("Run is only valid at stage 0")
            c_closed = self.fresh_classifier("gamma0")
            stage0_env = {k: v for k, v in env.items() if v[0] == 0}
            code_ty = self.typecheck(expr.body, stage0_env, 0, c_closed)
            if not isinstance(code_ty, TCode):
                raise StagingTypeError(f"Run expects TCode, got {code_ty}")
            if not self.is_sub_env(code_ty.classifier, c_closed):
                raise ScopeExtrusionTypeError(
                    f"Cannot run open code bound to rigid classifier {code_ty.classifier}"
                )
            return code_ty.inner
        if isinstance(expr, ENewRef):
            if stage != 0:
                raise StagingTypeError("Mutable ref cell modeled at stage 0")
            init_ty = self.typecheck(expr.init, env, 0, cur_classifier)
            return TRef(init_ty)
        if isinstance(expr, ESetRef):
            ref_ty = self.typecheck(expr.ref_expr, env, stage, cur_classifier)
            val_ty = self.typecheck(expr.val_expr, env, stage, cur_classifier)
            if not isinstance(ref_ty, TRef):
                raise StagingTypeError(f"SetRef expects TRef, got {ref_ty}")
            if isinstance(ref_ty.elem, TCode) and isinstance(val_ty, TCode):
                if ref_ty.elem.inner != val_ty.inner:
                    raise StagingTypeError(f"Ref payload mismatch: {ref_ty.elem.inner} vs {val_ty.inner}")
                if not self.is_sub_env(val_ty.classifier, ref_ty.elem.classifier):
                    raise ScopeExtrusionTypeError(
                        f"Ref scope extrusion rejected statically: cannot store code at inner "
                        f"classifier {val_ty.classifier} into ref at outer classifier {ref_ty.elem.classifier}"
                    )
            elif ref_ty.elem != val_ty:
                raise StagingTypeError(f"SetRef type mismatch: {ref_ty.elem} vs {val_ty}")
            return TUnit()
        if isinstance(expr, EGetRef):
            ref_ty = self.typecheck(expr.ref_expr, env, stage, cur_classifier)
            if not isinstance(ref_ty, TRef):
                raise StagingTypeError(f"GetRef expects TRef, got {ref_ty}")
            return ref_ty.elem
        if isinstance(expr, ESeq):
            self.typecheck(expr.first, env, stage, cur_classifier)
            return self.typecheck(expr.second, env, stage, cur_classifier)
        raise StagingTypeError(f"Unknown expr: {expr}")


class DynamicScopeExtrusionError(Exception):
    pass


@dataclass
class StackMark:
    var_name: str
    alive: bool = True


@dataclass
class DynamicCode:
    ast: str
    free_vars: dict[str, StackMark] = field(default_factory=dict)


def dyn_validate(code: DynamicCode) -> None:
    for vname, mark in code.free_vars.items():
        if not mark.alive:
            raise DynamicScopeExtrusionError(
                f"Scope extrusion detected at code construction: variable {vname!r} escaped its binder region"
            )


def dyn_binop(op: str, a: DynamicCode, b: DynamicCode) -> DynamicCode:
    dyn_validate(a)
    dyn_validate(b)
    merged = dict(a.free_vars)
    merged.update(b.free_vars)
    return DynamicCode(f"({a.ast} {op} {b.ast})", merged)


def dyn_build_fun(hint: str, body_fn: Callable[[DynamicCode], DynamicCode]) -> DynamicCode:
    """Models BER MetaOCaml `with_stack_mark` + `build_simple_fun` (typing/trx.ml:996-1015)."""
    mark = StackMark(hint, alive=True)
    var_code = DynamicCode(hint, {hint: mark})
    try:
        body = body_fn(var_code)
    finally:
        mark.alive = False
    remaining = {k: m for k, m in body.free_vars.items() if k != hint}
    res = DynamicCode(f"(fun {hint} -> {body.ast})", remaining)
    dyn_validate(res)
    return res


def dyn_close_code(code: DynamicCode) -> str:
    dyn_validate(code)
    if code.free_vars:
        leaked = ", ".join(sorted(code.free_vars))
        raise DynamicScopeExtrusionError(f"Code is not closed; free variables: {leaked}")
    return code.ast


def verify_staging_and_scope_extrusion() -> dict[str, Any]:
    tc = ClassifierTypeChecker()

    # Valid staged function: run .< fun x:Int -> x + 1 >.  : Int -> Int
    valid_prog = ERun(EBracket(ELam("x", TInt(), EAdd(EVar("x"), EInt(1)))))
    valid_ty = tc.typecheck(valid_prog, {})
    assert valid_ty == TFun(TInt(), TInt())

    # Valid outer-to-inner splice
    valid_splice = ELet(
        "c",
        EBracket(EInt(42)),
        EBracket(ELam("x", TInt(), EAdd(EVar("x"), EEscape(EVar("c"))))),
    )
    valid_splice_ty = tc.typecheck(valid_splice, {})
    assert isinstance(valid_splice_ty, TCode) and valid_splice_ty.inner == TFun(TInt(), TInt())

    # Static rejection of ref-cell scope extrusion
    extrusion_prog = ELet(
        "r",
        ENewRef(EBracket(EInt(0))),
        ELet(
            "_",
            EBracket(
                ELam(
                    "x",
                    TInt(),
                    EEscape(
                        ESeq(
                            ESetRef(EVar("r"), EBracket(EAdd(EVar("x"), EInt(1)))),
                            EBracket(EUnit()),
                        )
                    ),
                )
            ),
            EGetRef(EVar("r")),
        ),
    )
    static_ref_error: str | None = None
    try:
        tc.typecheck(extrusion_prog, {})
    except ScopeExtrusionTypeError as exc:
        static_ref_error = str(exc)
    assert static_ref_error is not None

    # Static rejection of running open code bound to a stage-0 variable `c`
    open_run_prog = EBracket(
        ELam(
            "x",
            TInt(),
            EEscape(
                ELet(
                    "c",
                    EBracket(EVar("x")),
                    ELet("_", ERun(EVar("c")), EBracket(EInt(0))),
                )
            ),
        )
    )
    static_run_error: str | None = None
    try:
        tc.typecheck(open_run_prog, {})
    except ScopeExtrusionTypeError as exc:
        static_run_error = str(exc)
    assert static_run_error is not None

    # Dynamic stackmark heap (BER MetaOCaml model)
    def spower(n: int, x: DynamicCode) -> DynamicCode:
        if n == 0:
            return DynamicCode("1")
        return dyn_binop("*", x, spower(n - 1, x))

    spower3 = dyn_build_fun("x", lambda x: spower(3, x))
    closed_spower3 = dyn_close_code(spower3)
    assert closed_spower3 == "(fun x -> (x * (x * (x * 1))))"

    cell: list[DynamicCode] = [DynamicCode("0")]

    def leaky_ref_body(x: DynamicCode) -> DynamicCode:
        cell[0] = dyn_binop("+", x, DynamicCode("1"))
        return DynamicCode("()")

    _ = dyn_build_fun("x_ref", leaky_ref_body)
    dyn_ref_err: str | None = None
    try:
        dyn_close_code(cell[0])
    except DynamicScopeExtrusionError as exc:
        dyn_ref_err = str(exc)
    assert dyn_ref_err is not None and "x_ref" in dyn_ref_err

    class LeakExc(Exception):
        def __init__(self, leaked: DynamicCode) -> None:
            self.leaked = leaked

    def leaky_exc_body(x: DynamicCode) -> DynamicCode:
        raise LeakExc(x)

    leaked_from_exc: DynamicCode | None = None
    try:
        dyn_build_fun("x_exc", leaky_exc_body)
    except LeakExc as exc:
        leaked_from_exc = exc.leaked

    assert leaked_from_exc is not None
    dyn_exc_err: str | None = None
    try:
        dyn_binop("+", leaked_from_exc, DynamicCode("1"))
    except DynamicScopeExtrusionError as exc:
        dyn_exc_err = str(exc)
    assert dyn_exc_err is not None and "x_exc" in dyn_exc_err

    return {
        "static_valid_run_type": str(valid_ty),
        "static_ref_extrusion_caught": static_ref_error,
        "static_open_run_caught": static_run_error,
        "dynamic_spower3": closed_spower3,
        "dynamic_ref_extrusion_caught": dyn_ref_err,
        "dynamic_exc_extrusion_caught": dyn_exc_err,
    }


def main() -> int:
    res_a = verify_sets_of_scopes()
    res_b = verify_token_macros_vs_reflection()
    res_c = verify_staging_and_scope_extrusion()

    print("[PASS] Part (a) Flatt Sets-of-Scopes:")
    for k, v in res_a.items():
        print(f"  - {k}: {v}")
    print("[PASS] Part (b) Token-Stream Macros vs. Semantic Reflection:")
    for k, v in res_b.items():
        print(f"  - {k}: {v}")
    print("[PASS] Part (c) Multi-Stage Scope-Extrusion Detection:")
    for k, v in res_c.items():
        print(f"  - {k}: {v}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
