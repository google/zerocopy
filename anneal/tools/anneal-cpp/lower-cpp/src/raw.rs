// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Typed view of the `RawCppBundle` v1 JSON emitted by `anneal-clang-dump`.
//!
//! Parsing is strict about the fields lowering relies on and tolerant of
//! additive fields it does not use. Constructs the extractor could not
//! describe are kept as `Unsupported` nodes so lowering fails closed only if
//! they are actually reachable.

use serde_json::{Map, Value};

use crate::error::{schema, Result};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawLangPolicy {
    pub is_cplusplus: bool,
    pub lang_standard: String,
    pub pointer_width_bits: u64,
    pub char_is_signed: bool,
    pub strict_aliasing: bool,
    pub signed_overflow: String,
    pub exceptions_enabled: bool,
    pub fast_math: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RawType {
    Void,
    Bool,
    Int {
        bits: u64,
        signed: bool,
        is_char_like: bool,
    },
    Ptr {
        pointee: Box<RawType>,
        is_const: bool,
        is_restrict: bool,
        may_alias: bool,
    },
    Array {
        elem: Box<RawType>,
        len: u64,
    },
    Record {
        id: String,
    },
    /// C++ `std::nullptr_t` (pointer-sized; its only value is the null
    /// pointer).
    NullPtrT,
    /// C++ `T&` / `T&&` (lowered to a non-null pointer).
    Ref {
        pointee: Box<RawType>,
        is_const: bool,
        is_rvalue: bool,
        may_alias: bool,
    },
    Unsupported {
        desc: String,
    },
}

#[derive(Debug, Clone)]
pub struct RawField {
    pub name: String,
    pub offset_bits: u64,
    pub bit_width: Option<u64>,
    pub ty: RawType,
}

#[derive(Debug, Clone)]
pub struct RawRecord {
    pub id: String,
    pub is_union: bool,
    pub size_bytes: u64,
    pub align_bytes: u64,
    pub fields: Vec<RawField>,
    /// C++ only: direct base subobject record ids.
    pub base_ids: Vec<String>,
    /// C++ only: the record has a vtable (Rung 2).
    pub is_polymorphic: bool,
    /// C++ only: symbol of the non-trivial destructor, if any.
    pub dtor_symbol: Option<String>,
    /// C++ only: the record is trivially copyable (always true in C).
    pub is_trivially_copyable: bool,
    /// C++ only: the record or a subobject has a `mutable` field.
    pub has_mutable: bool,
    /// C++ only: the record or a subobject has a constructor that may observe
    /// `this` (or whose body is unavailable).
    pub has_address_dependent_ctor: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RawPassing {
    DirectInt { bits: u64 },
    ExtendInt { bits: u64 },
    DirectPtr,
    Ignore,
    Other { desc: String },
}

#[derive(Debug, Clone)]
pub struct RawAbiWitness {
    pub cc: String,
    pub return_passing: RawPassing,
    pub param_passing: Vec<RawPassing>,
}

#[derive(Debug, Clone)]
pub struct RawParam {
    pub name: String,
    pub ty: RawType,
    /// The implicit object parameter of a C++ method.
    pub is_this: bool,
    /// Non-null iff a by-value parameter has a non-trivial destructor.
    pub dtor_symbol: Option<String>,
}

/// What a C++ function is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MethodKind {
    Free,
    Method,
    Ctor,
    Dtor,
}

/// One constructor initializer, in execution order.
#[derive(Debug, Clone)]
pub enum RawCtorInit {
    Field { record_id: String, field_idx: u32, init: RawExpr },
    Base { record_id: String, offset_bytes: u64, init: RawExpr },
    Unsupported { desc: String },
}

/// A destructor that runs after a destructor body: a member (`field_idx`)
/// or a base subobject (`offset_bytes`).
#[derive(Debug, Clone)]
pub struct RawSubobjectDtor {
    pub record_id: String,
    pub field_idx: Option<u32>,
    pub offset_bytes: Option<u64>,
    pub dtor_symbol: String,
}

#[derive(Debug, Clone)]
pub struct RawFunction {
    pub symbol: String,
    pub unmangled_name: String,
    pub is_definition: bool,
    pub is_variadic: bool,
    pub return_ty: RawType,
    pub params: Vec<RawParam>,
    pub abi_witness: RawAbiWitness,
    pub body: Option<RawStmt>,
    pub is_extern_c: bool,
    pub method_kind: MethodKind,
    pub is_virtual: bool,
    pub is_trivial: bool,
    pub ctor_inits: Vec<RawCtorInit>,
    /// Member destructors (reverse declaration order), then base
    /// destructors.
    pub subobject_dtors: Vec<RawSubobjectDtor>,
}

#[derive(Debug, Clone)]
pub struct RawBundle {
    pub tu_main_file: String,
    pub target_triple: String,
    pub lang_policy: RawLangPolicy,
    pub records: Vec<RawRecord>,
    pub functions: Vec<RawFunction>,
}

#[derive(Debug, Clone)]
pub enum RawStmt {
    Compound(Vec<RawStmt>),
    Decl {
        var_id: u32,
        name: String,
        ty: RawType,
        init: Option<RawExpr>,
        /// C++: declared with reference type; `init` is the bound glvalue.
        is_ref: bool,
        /// C++: non-trivial destructor run at the end of the scope.
        dtor_symbol: Option<String>,
        /// C++: named return value optimization candidate.
        is_nrvo: bool,
        /// A constant-initialized, const-qualified function-local `static`
        /// (the extractor admits no other static locals).
        is_static_const: bool,
    },
    Expr(RawExpr),
    If {
        cond: RawExpr,
        then_branch: Box<RawStmt>,
        else_branch: Option<Box<RawStmt>>,
    },
    While {
        cond: RawExpr,
        body: Box<RawStmt>,
    },
    DoWhile {
        body: Box<RawStmt>,
        cond: RawExpr,
    },
    For {
        init: Option<Box<RawStmt>>,
        cond: Option<RawExpr>,
        inc: Option<RawExpr>,
        body: Box<RawStmt>,
    },
    Switch {
        cond: RawExpr,
        body: Box<RawStmt>,
    },
    Case {
        value: i128,
        sub: Box<RawStmt>,
    },
    Default {
        sub: Box<RawStmt>,
    },
    Break,
    Continue,
    Goto {
        label: String,
    },
    Label {
        label: String,
        sub: Box<RawStmt>,
    },
    Return(Option<RawExpr>),
    Null,
    Unsupported {
        desc: String,
    },
}

#[derive(Debug, Clone)]
pub struct RawExpr {
    pub ty: RawType,
    pub is_lvalue: bool,
    pub kind: RawExprKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Plus,
    Minus,
    BitNot,
    LogNot,
    AddrOf,
    Deref,
    PreInc,
    PreDec,
    PostInc,
    PostDec,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
    BitAnd,
    BitOr,
    BitXor,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    LogAnd,
    LogOr,
    Comma,
    Assign,
    /// Compound assignment `lhs op= rhs` with the arithmetic operator `op`.
    CompoundAssign(ArithOp),
}

/// The arithmetic operators that have a compound-assignment form.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
    BitAnd,
    BitOr,
    BitXor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CastKind {
    LvalueToRvalue,
    IntegralCast,
    IntToBool,
    BoolToInt,
    BitCast,
    NullToPointer,
    ArrayToPointerDecay,
    PointerCast,
    Noop,
    ToVoid,
    PtrToBool,
    /// C++ derived-to-base conversion with the base subobject offset.
    DerivedToBase {
        offset_bytes: u64,
    },
    /// C++ conversion through a converting constructor (sub is `construct`).
    ConstructorConversion,
    /// C++ conversion through a conversion function (sub is a member call).
    UserDefinedConversion,
}

#[derive(Debug, Clone)]
pub enum RawExprKind {
    IntLit {
        value: i128,
    },
    BoolLit {
        value: bool,
    },
    VarRef {
        var_id: u32,
        is_param: bool,
        param_idx: Option<u32>,
        /// C++: the variable has reference type; the expression designates
        /// the referent.
        is_ref_binding: bool,
    },
    /// An object with static storage duration at file scope or `extern`
    /// (additive extension beyond the v1 node set).
    GlobalRef {
        symbol: String,
    },
    Unary {
        op: UnaryOp,
        sub: Box<RawExpr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<RawExpr>,
        rhs: Box<RawExpr>,
        /// For compound assignment only: the usual-arithmetic-conversion type
        /// the left operand is converted to, and the type the operation is
        /// computed in (C11 6.5.16.2p3).
        compute_tys: Option<(RawType, RawType)>,
    },
    Conditional {
        cond: Box<RawExpr>,
        then_expr: Box<RawExpr>,
        else_expr: Box<RawExpr>,
    },
    Cast {
        kind: CastKind,
        sub: Box<RawExpr>,
    },
    ArraySubscript {
        base: Box<RawExpr>,
        idx: Box<RawExpr>,
    },
    Member {
        base: Box<RawExpr>,
        is_arrow: bool,
        field_name: String,
        record_id: String,
        field_idx: u32,
        is_bitfield: bool,
    },
    Call {
        callee_symbol: Option<String>,
        args: Vec<RawExpr>,
        is_indirect: bool,
        is_builtin: bool,
        /// C++ member call: the object expression (a pointer when
        /// `implicit_object_is_ptr`, else a glvalue).
        implicit_object: Option<Box<RawExpr>>,
        implicit_object_is_ptr: bool,
        is_virtual: bool,
        /// Per declared parameter (excluding `this`): binds a reference.
        param_is_ref: Vec<bool>,
        returns_ref: bool,
        /// Trivial copy/move assignment operator (a byte copy).
        trivial_assign: bool,
    },
    InitList {
        inits: Vec<RawExpr>,
        is_transparent: bool,
        has_union_field: bool,
        /// Initializer of the array elements after `inits`.
        array_filler: Option<Box<RawExpr>>,
    },
    /// C99 compound literal `(T){...}`: an unnamed object initialized by
    /// `init`.
    CompoundLiteral {
        init: Box<RawExpr>,
        is_file_scope: bool,
    },
    /// C++ `this`.
    CxxThis,
    /// C++ `nullptr` (its `ty` is `std::nullptr_t`, emitted as unsupported).
    NullptrLit,
    /// Value-initialization (zero) of `ty`.
    ImplicitValueInit,
    /// Full-expression boundary for C++ temporaries.
    ExprWithCleanups {
        sub: Box<RawExpr>,
    },
    MaterializeTemporary {
        sub: Box<RawExpr>,
        lifetime_extended: bool,
    },
    /// A temporary whose destructor runs at the end of the full-expression.
    BindTemporary {
        sub: Box<RawExpr>,
        dtor_symbol: String,
    },
    Construct {
        ctor_symbol: String,
        record_id: String,
        args: Vec<RawExpr>,
        param_is_ref: Vec<bool>,
        is_trivial: bool,
        is_copy_or_move: bool,
        is_default: bool,
        zero_init: bool,
        is_array_construct: bool,
        is_complete: bool,
    },
    /// `__builtin_bit_cast(ty, sub)`; `sub` is a glvalue of `from_ty`.
    BuiltinBitCast {
        sub: Box<RawExpr>,
        from_ty: RawType,
    },
    SizeofOrAlignof {
        value_bytes: u64,
    },
    Paren {
        sub: Box<RawExpr>,
    },
    Unsupported {
        desc: String,
    },
}

// -------------------------------------------------------------------------
// JSON accessors
// -------------------------------------------------------------------------

fn obj<'a>(v: &'a Value, ctx: &str) -> Result<&'a Map<String, Value>> {
    match v.as_object() {
        Some(o) => Ok(o),
        None => schema(format!("{ctx}: expected object")),
    }
}

fn field<'a>(o: &'a Map<String, Value>, key: &str, ctx: &str) -> Result<&'a Value> {
    match o.get(key) {
        Some(v) => Ok(v),
        None => schema(format!("{ctx}: missing field `{key}`")),
    }
}

fn get_str(o: &Map<String, Value>, key: &str, ctx: &str) -> Result<String> {
    match field(o, key, ctx)?.as_str() {
        Some(s) => Ok(s.to_owned()),
        None => schema(format!("{ctx}: field `{key}` must be a string")),
    }
}

fn get_bool(o: &Map<String, Value>, key: &str, ctx: &str) -> Result<bool> {
    match field(o, key, ctx)?.as_bool() {
        Some(b) => Ok(b),
        None => schema(format!("{ctx}: field `{key}` must be a bool")),
    }
}

fn get_bool_or(o: &Map<String, Value>, key: &str, default: bool, ctx: &str) -> Result<bool> {
    match o.get(key) {
        None => Ok(default),
        Some(v) => match v.as_bool() {
            Some(b) => Ok(b),
            None => schema(format!("{ctx}: field `{key}` must be a bool")),
        },
    }
}

fn get_u64(o: &Map<String, Value>, key: &str, ctx: &str) -> Result<u64> {
    match field(o, key, ctx)?.as_u64() {
        Some(n) => Ok(n),
        None => schema(format!("{ctx}: field `{key}` must be a non-negative integer")),
    }
}

fn get_u32(o: &Map<String, Value>, key: &str, ctx: &str) -> Result<u32> {
    let n = get_u64(o, key, ctx)?;
    match u32::try_from(n) {
        Ok(n) => Ok(n),
        Err(_) => schema(format!("{ctx}: field `{key}` exceeds u32")),
    }
}

fn get_arr<'a>(o: &'a Map<String, Value>, key: &str, ctx: &str) -> Result<&'a Vec<Value>> {
    match field(o, key, ctx)?.as_array() {
        Some(a) => Ok(a),
        None => schema(format!("{ctx}: field `{key}` must be an array")),
    }
}

/// Returns `None` if the field is absent or JSON `null`.
fn get_opt<'a>(o: &'a Map<String, Value>, key: &str) -> Option<&'a Value> {
    match o.get(key) {
        None | Some(Value::Null) => None,
        Some(v) => Some(v),
    }
}

fn parse_i128(s: &str, ctx: &str) -> Result<i128> {
    match s.parse::<i128>() {
        Ok(n) => Ok(n),
        Err(_) => schema(format!("{ctx}: `{s}` is not a decimal integer in i128 range")),
    }
}

// -------------------------------------------------------------------------
// Bundle
// -------------------------------------------------------------------------

pub fn parse_bundle(text: &str) -> Result<RawBundle> {
    let v: Value = match serde_json::from_str(text) {
        Ok(v) => v,
        Err(e) => return Err(crate::error::LowerError::Json { detail: e.to_string() }),
    };
    let o = obj(&v, "bundle")?;
    let version = get_u64(o, "schema_version", "bundle")?;
    if version != 1 {
        return schema(format!("unsupported schema_version {version} (expected 1)"));
    }
    let lp = obj(field(o, "lang_policy", "bundle")?, "lang_policy")?;
    let lang_policy = RawLangPolicy {
        is_cplusplus: get_bool(lp, "is_cplusplus", "lang_policy")?,
        lang_standard: get_str(lp, "lang_standard", "lang_policy")?,
        pointer_width_bits: get_u64(lp, "pointer_width_bits", "lang_policy")?,
        char_is_signed: get_bool(lp, "char_is_signed", "lang_policy")?,
        strict_aliasing: get_bool(lp, "strict_aliasing", "lang_policy")?,
        signed_overflow: get_str(lp, "signed_overflow", "lang_policy")?,
        exceptions_enabled: get_bool(lp, "exceptions_enabled", "lang_policy")?,
        fast_math: get_bool(lp, "fast_math", "lang_policy")?,
    };
    let mut records = Vec::new();
    for r in get_arr(o, "records", "bundle")? {
        records.push(parse_record(r)?);
    }
    let mut functions = Vec::new();
    for f in get_arr(o, "functions", "bundle")? {
        functions.push(parse_function(f)?);
    }
    Ok(RawBundle {
        tu_main_file: get_str(o, "tu_main_file", "bundle")?,
        target_triple: get_str(o, "target_triple", "bundle")?,
        lang_policy,
        records,
        functions,
    })
}

fn parse_record(v: &Value) -> Result<RawRecord> {
    let o = obj(v, "record")?;
    let id = get_str(o, "id", "record")?;
    let ctx = format!("record `{id}`");
    let mut fields = Vec::new();
    for f in get_arr(o, "fields", &ctx)? {
        let fo = obj(f, &ctx)?;
        let bit_width = match get_opt(fo, "bit_width") {
            None => None,
            Some(b) => match b.as_u64() {
                Some(n) => Some(n),
                None => return schema(format!("{ctx}: bit_width must be an integer or null")),
            },
        };
        fields.push(RawField {
            name: get_str(fo, "name", &ctx)?,
            offset_bits: get_u64(fo, "offset_bits", &ctx)?,
            bit_width,
            ty: parse_type(field(fo, "ty", &ctx)?)?,
        });
    }
    let mut base_ids = Vec::new();
    if let Some(bases) = get_opt(o, "bases") {
        let a = match bases.as_array() {
            Some(a) => a,
            None => return schema(format!("{ctx}: bases must be an array")),
        };
        for b in a {
            let bo = obj(b, &ctx)?;
            base_ids.push(get_str(bo, "record_id", &ctx)?);
        }
    }
    Ok(RawRecord {
        is_union: get_bool(o, "is_union", &ctx)?,
        size_bytes: get_u64(o, "size_bytes", &ctx)?,
        align_bytes: get_u64(o, "align_bytes", &ctx)?,
        fields,
        base_ids,
        is_polymorphic: get_bool_or(o, "is_polymorphic", false, &ctx)?,
        is_trivially_copyable: get_bool_or(o, "is_trivially_copyable", true, &ctx)?,
        has_mutable: get_bool_or(o, "has_mutable", false, &ctx)?,
        has_address_dependent_ctor: get_bool_or(o, "has_address_dependent_ctor", false, &ctx)?,
        dtor_symbol: match get_opt(o, "dtor_symbol") {
            Some(d) => match d.as_str() {
                Some(d) => Some(d.to_owned()),
                None => return schema(format!("{ctx}: dtor_symbol must be a string or null")),
            },
            None => None,
        },
        id,
    })
}

fn get_opt_str(o: &Map<String, Value>, key: &str, ctx: &str) -> Result<Option<String>> {
    match get_opt(o, key) {
        None => Ok(None),
        Some(v) => match v.as_str() {
            Some(s) => Ok(Some(s.to_owned())),
            None => schema(format!("{ctx}: field `{key}` must be a string or null")),
        },
    }
}

fn get_bool_list(o: &Map<String, Value>, key: &str, ctx: &str) -> Result<Vec<bool>> {
    match get_opt(o, key) {
        None => Ok(Vec::new()),
        Some(v) => match v.as_array() {
            Some(a) => {
                let mut out = Vec::with_capacity(a.len());
                for b in a {
                    match b.as_bool() {
                        Some(b) => out.push(b),
                        None => return schema(format!("{ctx}: `{key}` must hold booleans")),
                    }
                }
                Ok(out)
            }
            None => schema(format!("{ctx}: field `{key}` must be an array")),
        },
    }
}

pub fn parse_type(v: &Value) -> Result<RawType> {
    let o = obj(v, "type")?;
    let kind = get_str(o, "kind", "type")?;
    Ok(match kind.as_str() {
        "void" => RawType::Void,
        "bool" => RawType::Bool,
        "int" => RawType::Int {
            bits: get_u64(o, "bits", "int type")?,
            signed: get_bool(o, "signed", "int type")?,
            is_char_like: get_bool_or(o, "is_char_like", false, "int type")?,
        },
        "ptr" => RawType::Ptr {
            pointee: Box::new(parse_type(field(o, "pointee", "ptr type")?)?),
            is_const: get_bool(o, "is_const", "ptr type")?,
            is_restrict: get_bool(o, "is_restrict", "ptr type")?,
            may_alias: get_bool(o, "may_alias", "ptr type")?,
        },
        "array" => RawType::Array {
            elem: Box::new(parse_type(field(o, "elem", "array type")?)?),
            len: get_u64(o, "len", "array type")?,
        },
        "record" => RawType::Record { id: get_str(o, "id", "record type")? },
        "nullptr_t" => RawType::NullPtrT,
        "ref" => RawType::Ref {
            pointee: Box::new(parse_type(field(o, "pointee", "ref type")?)?),
            is_const: get_bool(o, "is_const", "ref type")?,
            is_rvalue: get_bool(o, "is_rvalue", "ref type")?,
            may_alias: get_bool_or(o, "may_alias", false, "ref type")?,
        },
        "unsupported" => RawType::Unsupported { desc: get_str(o, "desc", "unsupported type")? },
        other => return schema(format!("unknown type kind `{other}`")),
    })
}

fn parse_passing(v: &Value) -> Result<RawPassing> {
    let o = obj(v, "abi passing")?;
    let kind = get_str(o, "kind", "abi passing")?;
    Ok(match kind.as_str() {
        "direct_int" => RawPassing::DirectInt { bits: get_u64(o, "bits", "direct_int")? },
        "extend_int" => RawPassing::ExtendInt { bits: get_u64(o, "bits", "extend_int")? },
        "direct_ptr" => RawPassing::DirectPtr,
        "ignore" => RawPassing::Ignore,
        other => RawPassing::Other {
            desc: match o.get("desc").and_then(Value::as_str) {
                Some(d) => format!("{other}:{d}"),
                None => other.to_owned(),
            },
        },
    })
}

fn parse_function(v: &Value) -> Result<RawFunction> {
    let o = obj(v, "function")?;
    let symbol = get_str(o, "symbol", "function")?;
    let ctx = format!("function `{symbol}`");
    let mut params = Vec::new();
    for p in get_arr(o, "params", &ctx)? {
        let po = obj(p, &ctx)?;
        params.push(RawParam {
            name: get_str(po, "name", &ctx)?,
            ty: parse_type(field(po, "ty", &ctx)?)?,
            is_this: get_bool_or(po, "is_this", false, &ctx)?,
            dtor_symbol: get_opt_str(po, "dtor_symbol", &ctx)?,
        });
    }
    let abi = obj(field(o, "abi_witness", &ctx)?, &ctx)?;
    let mut param_passing = Vec::new();
    for p in get_arr(abi, "param_passing", &ctx)? {
        param_passing.push(parse_passing(p)?);
    }
    let abi_witness = RawAbiWitness {
        cc: get_str(abi, "cc", &ctx)?,
        return_passing: parse_passing(field(abi, "return_passing", &ctx)?)?,
        param_passing,
    };
    let is_definition = get_bool(o, "is_definition", &ctx)?;
    let body = match get_opt(o, "body_stmt") {
        Some(b) => Some(parse_stmt(b)?),
        None => None,
    };
    if is_definition != body.is_some() {
        return schema(format!("{ctx}: is_definition disagrees with body_stmt presence"));
    }
    let method_kind = match get_opt_str(o, "method_kind", &ctx)?.as_deref() {
        None | Some("free") => MethodKind::Free,
        Some("method") => MethodKind::Method,
        Some("ctor") => MethodKind::Ctor,
        Some("dtor") => MethodKind::Dtor,
        Some(other) => return schema(format!("{ctx}: unknown method_kind `{other}`")),
    };
    let mut ctor_inits = Vec::new();
    if let Some(a) = get_opt(o, "ctor_inits") {
        let a = match a.as_array() {
            Some(a) => a,
            None => return schema(format!("{ctx}: ctor_inits must be an array")),
        };
        for ci in a {
            let co = obj(ci, &ctx)?;
            ctor_inits.push(match get_str(co, "kind", &ctx)?.as_str() {
                "field" => RawCtorInit::Field {
                    record_id: get_str(co, "record_id", &ctx)?,
                    field_idx: get_u32(co, "field_idx", &ctx)?,
                    init: parse_expr(field(co, "init", &ctx)?)?,
                },
                "base" => RawCtorInit::Base {
                    record_id: get_str(co, "record_id", &ctx)?,
                    offset_bytes: get_u64(co, "offset_bytes", &ctx)?,
                    init: parse_expr(field(co, "init", &ctx)?)?,
                },
                _ => RawCtorInit::Unsupported {
                    desc: get_opt_str(co, "desc", &ctx)?.unwrap_or_default(),
                },
            });
        }
    }
    let mut subobject_dtors = Vec::new();
    for (key, is_member) in [("member_dtors", true), ("base_dtors", false)] {
        if let Some(a) = get_opt(o, key) {
            let a = match a.as_array() {
                Some(a) => a,
                None => return schema(format!("{ctx}: {key} must be an array")),
            };
            for d in a {
                let d = obj(d, &ctx)?;
                subobject_dtors.push(RawSubobjectDtor {
                    record_id: get_str(d, "record_id", &ctx)?,
                    field_idx: if is_member { Some(get_u32(d, "field_idx", &ctx)?) } else { None },
                    offset_bytes: if is_member {
                        None
                    } else {
                        get_opt(d, "offset_bytes").and_then(Value::as_u64)
                    },
                    dtor_symbol: get_str(d, "dtor_symbol", &ctx)?,
                });
            }
        }
    }
    Ok(RawFunction {
        is_extern_c: get_bool_or(o, "is_extern_c", false, &ctx)?,
        method_kind,
        is_virtual: get_bool_or(o, "is_virtual", false, &ctx)?,
        is_trivial: get_bool_or(o, "is_trivial", false, &ctx)?,
        ctor_inits,
        subobject_dtors,
        unmangled_name: get_str(o, "unmangled_name", &ctx)?,
        is_definition,
        is_variadic: get_bool_or(o, "is_variadic", false, &ctx)?,
        return_ty: parse_type(field(o, "return_ty", &ctx)?)?,
        params,
        abi_witness,
        body,
        symbol,
    })
}

// -------------------------------------------------------------------------
// Statements
// -------------------------------------------------------------------------

fn boxed_stmt(o: &Map<String, Value>, key: &str, ctx: &str) -> Result<Box<RawStmt>> {
    Ok(Box::new(parse_stmt(field(o, key, ctx)?)?))
}

pub fn parse_stmt(v: &Value) -> Result<RawStmt> {
    let o = obj(v, "stmt")?;
    let kind = get_str(o, "kind", "stmt")?;
    let ctx = kind.as_str();
    Ok(match ctx {
        "compound" => {
            let mut stmts = Vec::new();
            for s in get_arr(o, "stmts", ctx)? {
                stmts.push(parse_stmt(s)?);
            }
            RawStmt::Compound(stmts)
        }
        "decl_stmt" => RawStmt::Decl {
            var_id: get_u32(o, "var_id", ctx)?,
            name: get_str(o, "name", ctx)?,
            ty: parse_type(field(o, "ty", ctx)?)?,
            init: match get_opt(o, "init") {
                Some(e) => Some(parse_expr(e)?),
                None => None,
            },
            is_ref: get_bool_or(o, "is_ref", false, ctx)?,
            dtor_symbol: get_opt_str(o, "dtor_symbol", ctx)?,
            is_nrvo: get_bool_or(o, "is_nrvo", false, ctx)?,
            is_static_const: get_bool_or(o, "is_static_const", false, ctx)?,
        },
        "expr_stmt" => RawStmt::Expr(parse_expr(field(o, "expr", ctx)?)?),
        "if" => RawStmt::If {
            cond: parse_expr(field(o, "cond", ctx)?)?,
            then_branch: boxed_stmt(o, "then_branch", ctx)?,
            else_branch: match get_opt(o, "else_branch") {
                Some(s) => Some(Box::new(parse_stmt(s)?)),
                None => None,
            },
        },
        "while" => RawStmt::While {
            cond: parse_expr(field(o, "cond", ctx)?)?,
            body: boxed_stmt(o, "body", ctx)?,
        },
        "do_while" => RawStmt::DoWhile {
            body: boxed_stmt(o, "body", ctx)?,
            cond: parse_expr(field(o, "cond", ctx)?)?,
        },
        "for" => RawStmt::For {
            init: match get_opt(o, "init") {
                Some(s) => Some(Box::new(parse_stmt(s)?)),
                None => None,
            },
            cond: match get_opt(o, "cond") {
                Some(e) => Some(parse_expr(e)?),
                None => None,
            },
            inc: match get_opt(o, "inc") {
                Some(e) => Some(parse_expr(e)?),
                None => None,
            },
            body: boxed_stmt(o, "body", ctx)?,
        },
        "switch" => RawStmt::Switch {
            cond: parse_expr(field(o, "cond", ctx)?)?,
            body: boxed_stmt(o, "body", ctx)?,
        },
        "case" => RawStmt::Case {
            value: parse_i128(&get_str(o, "value_str", ctx)?, ctx)?,
            sub: boxed_stmt(o, "sub", ctx)?,
        },
        "default" => RawStmt::Default { sub: boxed_stmt(o, "sub", ctx)? },
        "break" => RawStmt::Break,
        "continue" => RawStmt::Continue,
        "goto" => RawStmt::Goto { label: get_str(o, "label", ctx)? },
        "label" => {
            RawStmt::Label { label: get_str(o, "label", ctx)?, sub: boxed_stmt(o, "sub", ctx)? }
        }
        "return" => RawStmt::Return(match get_opt(o, "expr") {
            Some(e) => Some(parse_expr(e)?),
            None => None,
        }),
        "null_stmt" => RawStmt::Null,
        "unsupported_stmt" => RawStmt::Unsupported { desc: get_str(o, "desc", ctx)? },
        other => return schema(format!("unknown stmt kind `{other}`")),
    })
}

// -------------------------------------------------------------------------
// Expressions
// -------------------------------------------------------------------------

fn boxed_expr(o: &Map<String, Value>, key: &str, ctx: &str) -> Result<Box<RawExpr>> {
    Ok(Box::new(parse_expr(field(o, key, ctx)?)?))
}

fn unary_op(s: &str) -> Result<UnaryOp> {
    Ok(match s {
        "plus" => UnaryOp::Plus,
        "minus" => UnaryOp::Minus,
        "bit_not" => UnaryOp::BitNot,
        "log_not" => UnaryOp::LogNot,
        "addr_of" => UnaryOp::AddrOf,
        "deref" => UnaryOp::Deref,
        "pre_inc" => UnaryOp::PreInc,
        "pre_dec" => UnaryOp::PreDec,
        "post_inc" => UnaryOp::PostInc,
        "post_dec" => UnaryOp::PostDec,
        other => return schema(format!("unknown unary op `{other}`")),
    })
}

fn binary_op(s: &str) -> Result<BinaryOp> {
    use ArithOp as A;
    Ok(match s {
        "add" => BinaryOp::Add,
        "sub" => BinaryOp::Sub,
        "mul" => BinaryOp::Mul,
        "div" => BinaryOp::Div,
        "rem" => BinaryOp::Rem,
        "shl" => BinaryOp::Shl,
        "shr" => BinaryOp::Shr,
        "bit_and" => BinaryOp::BitAnd,
        "bit_or" => BinaryOp::BitOr,
        "bit_xor" => BinaryOp::BitXor,
        "eq" => BinaryOp::Eq,
        "ne" => BinaryOp::Ne,
        "lt" => BinaryOp::Lt,
        "le" => BinaryOp::Le,
        "gt" => BinaryOp::Gt,
        "ge" => BinaryOp::Ge,
        "log_and" => BinaryOp::LogAnd,
        "log_or" => BinaryOp::LogOr,
        "comma" => BinaryOp::Comma,
        "assign" => BinaryOp::Assign,
        "add_assign" => BinaryOp::CompoundAssign(A::Add),
        "sub_assign" => BinaryOp::CompoundAssign(A::Sub),
        "mul_assign" => BinaryOp::CompoundAssign(A::Mul),
        "div_assign" => BinaryOp::CompoundAssign(A::Div),
        "rem_assign" => BinaryOp::CompoundAssign(A::Rem),
        "shl_assign" => BinaryOp::CompoundAssign(A::Shl),
        "shr_assign" => BinaryOp::CompoundAssign(A::Shr),
        "and_assign" => BinaryOp::CompoundAssign(A::BitAnd),
        "or_assign" => BinaryOp::CompoundAssign(A::BitOr),
        "xor_assign" => BinaryOp::CompoundAssign(A::BitXor),
        other => return schema(format!("unknown binary op `{other}`")),
    })
}

fn cast_kind(s: &str) -> Option<CastKind> {
    Some(match s {
        "lvalue_to_rvalue" => CastKind::LvalueToRvalue,
        "integral_cast" => CastKind::IntegralCast,
        "int_to_bool" => CastKind::IntToBool,
        "bool_to_int" => CastKind::BoolToInt,
        "bit_cast" => CastKind::BitCast,
        "null_to_pointer" => CastKind::NullToPointer,
        "array_to_pointer_decay" => CastKind::ArrayToPointerDecay,
        "pointer_cast" => CastKind::PointerCast,
        "noop" => CastKind::Noop,
        "to_void" => CastKind::ToVoid,
        "ptr_to_bool" => CastKind::PtrToBool,
        "constructor_conversion" => CastKind::ConstructorConversion,
        "user_defined_conversion" => CastKind::UserDefinedConversion,
        _ => return None,
    })
}

pub fn parse_expr(v: &Value) -> Result<RawExpr> {
    let o = obj(v, "expr")?;
    let kind = get_str(o, "kind", "expr")?;
    let ctx = kind.as_str();
    let ty = parse_type(field(o, "ty", ctx)?)?;
    let is_lvalue = match get_str(o, "value_category", ctx)?.as_str() {
        // C++ xvalues are glvalues: they designate an object.
        "lvalue" | "xvalue" => true,
        "prvalue" => false,
        other => {
            return Ok(RawExpr {
                ty,
                is_lvalue: false,
                kind: RawExprKind::Unsupported { desc: format!("value category `{other}`") },
            })
        }
    };
    let kind = match ctx {
        "int_lit" => {
            let value = parse_i128(&get_str(o, "value_str", ctx)?, ctx)?;
            let bits = get_u64(o, "bits", ctx)?;
            let signed = get_bool(o, "signed", ctx)?;
            match &ty {
                RawType::Int { bits: tb, signed: ts, .. } if *tb == bits && *ts == signed => {}
                _ => return schema("int_lit: bits/signed disagree with `ty`"),
            }
            RawExprKind::IntLit { value }
        }
        "bool_lit" => RawExprKind::BoolLit { value: get_bool(o, "value", ctx)? },
        "var_ref" => RawExprKind::VarRef {
            var_id: get_u32(o, "var_id", ctx)?,
            is_param: get_bool(o, "is_param", ctx)?,
            param_idx: match get_opt(o, "param_idx") {
                Some(p) => match p.as_u64().and_then(|n| u32::try_from(n).ok()) {
                    Some(n) => Some(n),
                    None => return schema("var_ref: param_idx must be a u32 or null"),
                },
                None => None,
            },
            is_ref_binding: get_bool_or(o, "is_ref_binding", false, ctx)?,
        },
        "global_ref" => RawExprKind::GlobalRef { symbol: get_str(o, "symbol", ctx)? },
        "unary_op" => RawExprKind::Unary {
            op: unary_op(&get_str(o, "op", ctx)?)?,
            sub: boxed_expr(o, "sub", ctx)?,
        },
        "binary_op" => {
            let op = binary_op(&get_str(o, "op", ctx)?)?;
            let compute_tys = match op {
                BinaryOp::CompoundAssign(_) => Some((
                    parse_type(field(o, "compute_lhs_ty", ctx)?)?,
                    parse_type(field(o, "compute_result_ty", ctx)?)?,
                )),
                _ => None,
            };
            RawExprKind::Binary {
                op,
                lhs: boxed_expr(o, "lhs", ctx)?,
                rhs: boxed_expr(o, "rhs", ctx)?,
                compute_tys,
            }
        }
        "conditional" => RawExprKind::Conditional {
            cond: boxed_expr(o, "cond", ctx)?,
            then_expr: boxed_expr(o, "then_expr", ctx)?,
            else_expr: boxed_expr(o, "else_expr", ctx)?,
        },
        "cast" => {
            let ck = get_str(o, "cast_kind", ctx)?;
            let kind = if ck == "derived_to_base" {
                match get_opt(o, "base_offset_bytes").and_then(Value::as_u64) {
                    Some(offset_bytes) => Some(CastKind::DerivedToBase { offset_bytes }),
                    None => return schema("derived_to_base cast without base_offset_bytes"),
                }
            } else {
                cast_kind(&ck)
            };
            match kind {
                Some(kind) => RawExprKind::Cast { kind, sub: boxed_expr(o, "sub", ctx)? },
                None => RawExprKind::Unsupported { desc: format!("cast kind `{ck}`") },
            }
        }
        "array_subscript" => RawExprKind::ArraySubscript {
            base: boxed_expr(o, "base", ctx)?,
            idx: boxed_expr(o, "idx", ctx)?,
        },
        "member" => RawExprKind::Member {
            base: boxed_expr(o, "base", ctx)?,
            is_arrow: get_bool(o, "is_arrow", ctx)?,
            field_name: get_str(o, "field_name", ctx)?,
            record_id: get_str(o, "record_id", ctx)?,
            field_idx: get_u32(o, "field_idx", ctx)?,
            is_bitfield: get_bool_or(o, "is_bitfield", false, ctx)?,
        },
        "call" => {
            let mut args = Vec::new();
            for a in get_arr(o, "args", ctx)? {
                args.push(parse_expr(a)?);
            }
            RawExprKind::Call {
                callee_symbol: match get_opt(o, "callee_symbol") {
                    Some(s) => match s.as_str() {
                        Some(s) => Some(s.to_owned()),
                        None => return schema("call: callee_symbol must be a string or null"),
                    },
                    None => None,
                },
                args,
                is_indirect: get_bool(o, "is_indirect", ctx)?,
                is_builtin: get_bool_or(o, "is_builtin", false, ctx)?,
                implicit_object: match get_opt(o, "implicit_object") {
                    Some(e) => Some(Box::new(parse_expr(e)?)),
                    None => None,
                },
                implicit_object_is_ptr: get_bool_or(o, "implicit_object_is_ptr", false, ctx)?,
                is_virtual: get_bool_or(o, "is_virtual", false, ctx)?,
                param_is_ref: get_bool_list(o, "param_is_ref", ctx)?,
                returns_ref: get_bool_or(o, "returns_ref", false, ctx)?,
                trivial_assign: get_bool_or(o, "trivial_assign", false, ctx)?,
            }
        }
        "init_list" => {
            let mut inits = Vec::new();
            for i in get_arr(o, "inits", ctx)? {
                inits.push(parse_expr(i)?);
            }
            RawExprKind::InitList {
                inits,
                is_transparent: get_bool_or(o, "is_transparent", false, ctx)?,
                has_union_field: get_opt(o, "union_field_idx").is_some(),
                array_filler: match get_opt(o, "array_filler") {
                    Some(f) => Some(Box::new(parse_expr(f)?)),
                    None => None,
                },
            }
        }
        "compound_literal" => RawExprKind::CompoundLiteral {
            init: boxed_expr(o, "init", ctx)?,
            is_file_scope: get_bool(o, "is_file_scope", ctx)?,
        },
        "cxx_this" => RawExprKind::CxxThis,
        "nullptr_lit" => RawExprKind::NullptrLit,
        "implicit_value_init" => RawExprKind::ImplicitValueInit,
        "expr_with_cleanups" => RawExprKind::ExprWithCleanups { sub: boxed_expr(o, "sub", ctx)? },
        "materialize_temporary" => RawExprKind::MaterializeTemporary {
            sub: boxed_expr(o, "sub", ctx)?,
            lifetime_extended: get_bool_or(o, "lifetime_extended", false, ctx)?,
        },
        "bind_temporary" => RawExprKind::BindTemporary {
            sub: boxed_expr(o, "sub", ctx)?,
            dtor_symbol: get_str(o, "dtor_symbol", ctx)?,
        },
        "construct" => {
            let mut args = Vec::new();
            for a in get_arr(o, "args", ctx)? {
                args.push(parse_expr(a)?);
            }
            RawExprKind::Construct {
                ctor_symbol: get_str(o, "ctor_symbol", ctx)?,
                record_id: get_str(o, "record_id", ctx)?,
                args,
                param_is_ref: get_bool_list(o, "param_is_ref", ctx)?,
                is_trivial: get_bool(o, "is_trivial", ctx)?,
                is_copy_or_move: get_bool_or(o, "is_copy_or_move", false, ctx)?,
                is_default: get_bool_or(o, "is_default", false, ctx)?,
                zero_init: get_bool_or(o, "zero_init", false, ctx)?,
                is_array_construct: get_bool_or(o, "is_array_construct", false, ctx)?,
                is_complete: get_opt_str(o, "construction_kind", ctx)?.as_deref()
                    == Some("complete"),
            }
        }
        "builtin_bit_cast" => RawExprKind::BuiltinBitCast {
            sub: boxed_expr(o, "sub", ctx)?,
            from_ty: parse_type(field(o, "from_ty", ctx)?)?,
        },
        "sizeof_or_alignof" => {
            RawExprKind::SizeofOrAlignof { value_bytes: get_u64(o, "value_bytes", ctx)? }
        }
        "paren" => RawExprKind::Paren { sub: boxed_expr(o, "sub", ctx)? },
        "unsupported_expr" => RawExprKind::Unsupported { desc: get_str(o, "desc", ctx)? },
        other => return schema(format!("unknown expr kind `{other}`")),
    };
    Ok(RawExpr { ty, is_lvalue, kind })
}
