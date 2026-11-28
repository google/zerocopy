<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# `anneal-clang-dump`: Rung-0 C11 and Rung-1 C++20 extractor

`anneal-clang-dump` runs Clang's preprocessor and Sema over one C or C++
translation unit and writes a deterministic `RawCppBundle` (schema v1) JSON
document for [`anneal-lower-cpp`](../anneal-cpp/lower-cpp/README.md):

```text
anneal-clang-dump [--entry=<fn>]... [--externalize-callee=<fn>]... \
  [--output=<bundle.json>] <file.c> -- <compiler flags>
```

- **Reachability pruning.** Starting from the `--entry` roots (or every
  definition in the main file when none is given), it follows direct calls
  breadth-first. Callees defined in the TU are emitted with bodies; others are
  emitted as declarations (`"body_stmt": null`).
- **Externalized callees.** Each `--externalize-callee` name (unqualified,
  qualified, or mangled) is emitted as a declaration even if the TU defines
  it (`"is_externalized": true`), and its body is never traversed, so neither
  its callees nor the constructs it alone uses reach the bundle. A name that
  matches no function of the TU, or that is also an entry, is an error.
- **Language-policy seal.** `lang_policy` records `LangOptions`,
  `CodeGenOptions`, and `TargetInfo` facts that change the meaning of C code:
  `char` signedness, strict aliasing (`-fno-strict-aliasing`), signed-overflow
  behavior (`-fwrapv`/`-ftrapv`), exceptions, fast-math, and pointer width.
- **Layouts and ABI.** Every transitively referenced record carries its
  `ASTRecordLayout` size, alignment, and field bit offsets (including packed
  and `may_alias` records). Every function carries Clang CodeGen's ABI
  classification of its signature (`abi_witness`).
- **Faithful bodies.** Bodies keep every implicit cast, so integer promotions
  and usual arithmetic conversions are explicit. Compound assignments carry
  Clang's computation types. `sizeof`/`alignof` are folded to byte counts.
  Anything the extractor does not model is emitted as `unsupported_stmt` /
  `unsupported_expr` so the lowerer fails closed.

The extractor refuses to emit a bundle for a translation unit with compile
errors.

## Trust classification

`anneal-clang-dump` lives in untrusted `anneal/tools/` (Zone-2 tooling)
alongside `anneal-lower-cpp`, targeting the companion `Trusted.CppAst`
semantics stack (which does not yet exist on `main`). Because this pipeline
performs compile-time constant/integral-global folding and downstream SSENF
gating and normalization in Zone 2, standalone C/C++ claim admission will
require either Pass-2 TCB promotion or translation validation rather than
trusting Zone-2 output directly.

## Building

The extractor is a single C++20 file that links against an installed Clang
and LLVM development package. With a distribution that ships the shared
`libclang-cpp` and `libLLVM`, for example:

```text
clang++ -std=c++20 $(llvm-config --cxxflags) main.cc -o anneal-clang-dump \
  $(llvm-config --ldflags) -lclang-cpp $(llvm-config --libs)
```

Otherwise, link the static `clangTooling`, `clangFrontend`, `clangCodeGen`,
`clangDriver`, `clangAnalysis`, `clangAST`, and `clangBasic` libraries and
the LLVM `support` and `core` components.

## Schema extensions beyond the v1 contract

The extractor emits these additive fields and node kinds, all consumed by
`anneal-lower-cpp`:

- Expression nodes: `global_ref` (`symbol`, `name`, `has_external_linkage`)
  for objects with static storage duration; `cast_kind: "ptr_to_bool"`;
  `is_implicit` on casts; `compute_lhs_ty` / `compute_result_ty` on compound
  assignments; `is_builtin` on calls; `is_bitfield` on member accesses.
- Statement nodes: `switch` (`cond`, `body`), `case` (`value_str`, `sub`),
  `default` (`sub`). A declaration of several variables is flattened into
  consecutive `decl_stmt` nodes. A function-local `static` that is
  const-qualified (without `mutable` members), not thread-local, and
  constant-initialized is a `decl_stmt` with `is_static_const`, and references
  to it are `var_ref`s; every other static local is unsupported.
- Initializers: `init_list` in its semantic form (one initializer per element
  or named member, omitted members as `implicit_value_init`) with
  `is_transparent`, `union_field_idx`, and `array_filler`; `compound_literal`
  (`init`, `is_file_scope`). In C, `ExprWithCleanups` (which Clang adds around
  some full-expressions with compound literals) has no run-time meaning and is
  dropped.
- Records: `is_packed` and `may_alias`. Volatile-qualified types are emitted
  as `unsupported` so that every volatile access fails closed.
- Functions: `is_variadic`. ABI passing kinds `extend_int` (`bits`,
  `sign_ext`), `ignore`, `indirect` (`byval`), `direct_other`, and `other`, in
  addition to `direct_int` and `direct_ptr`.

## C++ (Rung 1) extensions

For C++ translation units (`lang_policy.is_cplusplus`), the extractor works on
the post-Sema AST and adds the following. None of it is emitted for C, so C
output is unchanged.

- **Roots and specializations.** `--entry` also matches qualified names, and a
  template name selects every specialization that has a body. Methods,
  constructors (complete-object `C1` symbols), and destructors (`D1`) are
  reachable through calls, construction, and destruction. Deduction guides
  are never roots (they are never called and cannot be mangled).
- **Types.** `ref` (`pointee`, `is_const`, `is_rvalue`, `may_alias`) and
  `nullptr_t`. Record ids carry the qualified name and printed template
  arguments, e.g. `struct.Span<const unsigned char>`. Integer literals of
  enumeration type (including scoped enumerations) are described by the
  underlying integer type, as their `ty` is.
- **Records.** `is_cxx_record`, `is_polymorphic`, `is_trivially_copyable`,
  `has_mutable`, `has_address_dependent_ctor`, `bases` (`record_id`,
  `offset_bytes`, `is_virtual`), `has_non_trivial_dtor`, and `dtor_symbol`.
- **Functions.** `qualified_name`, `method_kind`
  (`free`/`method`/`ctor`/`dtor`), `this_record_id`, `is_const_method`,
  `is_virtual`, `is_static_method`, `is_trivial`, `template_args`. Instance
  methods list the implicit object parameter first (`is_this`), and their
  `abi_witness` includes it. Constructors carry `ctor_inits`; destructors
  carry `member_dtors` and `base_dtors`. By-value parameters carry
  `dtor_symbol`.
- **Statements.** `decl_stmt` carries `is_ref`, `is_nrvo`, and `dtor_symbol`
  (the non-trivial destructor run at scope exit). `if constexpr` is resolved to
  its taken branch, and attributes on statements are dropped. `return` carries
  `nrvo_var_id`.
- **Expressions.** `cxx_this`, `nullptr_lit`, `implicit_value_init`,
  `expr_with_cleanups`, `materialize_temporary` (`lifetime_extended`),
  `bind_temporary` (`dtor_symbol`), `construct` (constructor symbol, triviality,
  zero-initialization, construction kind, `param_is_ref`), and
  `builtin_bit_cast` (`from_ty`). Calls gain `implicit_object`,
  `implicit_object_is_ptr`, `is_virtual`, `param_is_ref`, `returns_ref`, and
  `trivial_assign`. `var_ref` gains `is_ref_binding`. Casts gain `cast_syntax`
  and the kinds `derived_to_base` (`base_offset_bytes`),
  `constructor_conversion`, and `user_defined_conversion`. Bit-field members
  carry `bit_offset`, `bit_width`, and `field_is_signed`.
- **Folded away.** Substituted non-type template arguments, default arguments
  and member initializers, rewritten comparison operators, type traits and
  concept checks, and `lvalue_to_rvalue` reads of constexpr-usable integral
  globals.
- **Fail closed.** Lambdas, `new`/`delete`, `throw`/`try`, `dynamic_cast`,
  `typeid`, range-based `for`, and non-trivial destructors that Sema never
  declared (`dtor_symbol: "<undeclared>"`) or that belong to arrays
  (`"<array>"`).
