<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# `anneal-lower-cpp`: `RawCppBundle` to `Trusted.CppAst`

`anneal-lower-cpp` is a pure-Rust lowerer (no C++, LLVM, or FFI dependencies)
from the `RawCppBundle` JSON written by
[`anneal-clang-dump`](../../anneal-clang-dump/README.md) to a `CapturedCpp.lean`
file that defines `CapturedCpp.program : Trusted.CppAst.CppProgram`:

```text
anneal-lower-cpp [--entry SYMBOL] [--namespace NS] [-o CapturedCpp.lean] bundle.json
```

It exits with status 2 and a `LowerError` when it refuses a bundle. It never
emits partial or best-effort output. With `--entry`, only the functions the
entry can call (transitively, including implicit constructor and destructor
calls, read off the lowered bodies) are lowered and emitted, so a construct
used only by an unreachable sibling cannot block the entry. Without `--entry`,
every function in the bundle is lowered and the first is the entry.

## Trust classification

`anneal-clang-dump` and `anneal-lower-cpp` currently live in untrusted
`anneal/tools/` (Zone-2 tooling). Unlike `rustc-capture`, this pipeline
performs semantic gating and normalization before emitting `CapturedCpp.lean`:
SSENF sequencing enforcement, return-slot normalization, read-only
`static const` local hoisting, compile-time constant/integral-global folding
in `anneal-clang-dump`, and scalar global-load stubbing.

The emitted `CapturedCpp.lean` imports `Trusted.CppAst`, which belongs to the
companion C/C++ semantics stack and does not yet exist on `main`, nor does
`TrustedBoundary` yet define an admission rule for `CapturedCpp` modules on
`main`. Admitting standalone C/C++ verification claims over
`CapturedCpp.program` will require either Pass-2 TCB promotion of the
capture/lowering pipeline or translation validation, rather than trusting
Zone-2 output directly.

## Gates

1. **Language policy.** Rung 0 admits C11 and Rung 1 admits C++17/C++20, both
   with exceptions and fast-math disabled, 64-bit pointers, and ISO (`isoUB`)
   or `-fwrapv` (`wrapv`) signed overflow
   (`LowerError::UnsupportedLangPolicy`).
2. **ABI cross-check.** Clang's `abi_witness` must classify every scalar
   parameter and return value as directly passed at the declared width
   (`LowerError::AbiMismatch`). C by-value aggregates are unsupported; C++
   trivially copyable records with trivial destructors may be passed or
   returned by value only when neither the record nor any subobject has a
   non-trivial constructor whose body is unavailable or may observe `this`
   beyond direct member/base initialization (preserving C++17/C++20 guaranteed
   copy elision).
3. **Single-Side-Effect Normal Form (SSENF).** `Trusted.CppAst` is a linear
   IR, so each full-expression must have only one observable evaluation order.
   Operands of every operator other than `&&`, `||`, `,`, and `?:` are
   unsequenced siblings, as are the address and value operands of `=` and
   `op=`, the base and index of `[]`, and call arguments. Two siblings
   conflict when one writes a variable the other reads or writes, or when one
   writes memory or calls a function while the other touches memory or calls.
   C++ temporaries with non-trivial destructors (`BindTemporary`) also count
   as calls and memory reads so unsequenced destructor orders are rejected.
   Variables whose address is taken count as memory. The store of `=`, `op=`,
   `++`, and `--` must not coincide with a write by an operand. Conflicts fail
   with `LowerError::UnsequencedSideEffects`, so `x + (x = 1)`,
   `sink(++x, ++x)`, `a[i] = i++`, `x = x++`, and `g() + h()` are rejected,
   while `x = x + 1`, `s1 += *buf++`, and `p[i] = p[i] + 1` lower. The gate is
   deliberately stricter than C11 (it also rejects some merely unspecified
   orders).

## Lowering

- Local `_0` is the return slot, `_1..=_K` are the parameters, and user locals
  and temporaries follow. Declarations emit `storageLive`, so a local declared
  in a loop is uninitialized again on every iteration.
- Every block scope—including selection (`if`/`else`, `switch`) and iteration
  (`while`, `do`/`while`, `for`) substatements without braces (C11 6.8.4p3,
  6.8.5p5)—ends the lifetimes of its locals in reverse declaration order
  (C11 6.2.4p6) with `storageDead`, on normal exit and when `break`,
  `continue`, `return`, or `goto` leaves it, so a loop body's locals and
  compound literals do not accumulate storage across iterations. Conditionally
  evaluated C compound literals and compound literals in branch conditions are
  rejected. A `goto` into a block past one of its declarations or across a
  declaration in the same block, and a `case` or `default` label after a
  declaration in its `switch`, are rejected, since the jump would skip a
  `storageLive` or repeat one on a live local.
- `if`, `while`, `do`/`while`, `for`, `switch`, `break`, `continue`, `goto`,
  `&&`, `||`, `?:`, and calls become explicit basic blocks; `CppExpr` has no
  hidden control flow. Branch conditions are converted to `CppTy.bool`
  (C11 6.8.4.1p2) with `intToBool` or a comparison against the null pointer;
  a comparison used as a condition is used directly.
- `Trusted.CppAst` comparisons produce `CppTy.bool`. In C, where relational
  and equality operators yield `int` (C11 6.5.8p6, 6.5.9p3), the result is
  widened with `boolToInt`, so `(a < 0) ^ (b < 0)` and `return x == 0;`
  compute `int`s.
- Brace initializers of local records and arrays, and C compound literals
  (`(T){...}`, an unnamed block-scope object), initialize member by member and
  element by element in order; the SSENF gate rejects initializer lists whose
  elements conflict, so the order is unobservable. Omitted members and
  trailing elements are value-initialized, which zeroes their padding too
  (C11 6.7.9p10, p21). When the whole object has no padding bits and no
  explicit initializer can read the target before initialization, it is
  zero-filled first (`CppStmt.zeroInit`) and only explicit initializers are
  stored; self-referential or potentially aliased initializers evaluate in
  order without upfront zeroing so uninitialized-read UB is preserved (failing
  closed on padded or bit-field partial initializers).
- A function-local `static` that is const-qualified, contains no `mutable`
  subobjects, is constant-initialized, is never modified in the body, and
  whose address never escapes is hoisted to a local initialized at the start
  of the body. Since it can never change and no pointer to it exists, a
  per-call copy is indistinguishable from the single static object. Other
  static locals stay unsupported.
- Implicit conversions from the Clang AST are kept as `intCast`, `intToBool`,
  `boolToInt`, and `ptrCast`. `E++` and `++E` promote narrower integer types
  and narrow bit-fields (using the bit-field width, C11 6.3.1.1p2) to `int` or
  `unsigned int` and convert back, as C11 6.5.2.4 requires. Assignments and
  pre-increments/decrements to bit-fields used as values yield the truncated
  bit-field value.
- Values that a later sequenced effect could change (`x++`, `++x` and
  assignments used as values, call results, `&&`/`||`/`?:` results) are
  stored in fresh temporaries.
- Reading a scalar global `g` becomes a call to the bodiless external callee
  `anneal.global_load.g`, and the program is marked `isPartial`.
  `Trusted.CppAst` has no global objects, so this over-approximates the read
  as an arbitrary value of the global's type. The semantics cannot execute the
  call until a contract is linked for the stub. Stores to globals and taking
  their address are unsupported.
- Blocks unreachable from the entry are pruned. Falling off the end of a
  non-`void` function becomes `unreachable`. A discarded `void()` (what a
  disabled assertion macro can expand to) emits nothing.
- A record whose definition cannot be lowered (for example, one with a
  function-pointer field) is left out of `records` when the program only
  names it as a pointee, as in the signature of an externalized callee. Any
  by-value use, field access, or pointer arithmetic on it is still rejected,
  and a polymorphic record is always rejected.

## Output

- The file starts with `module`, `prelude`, and explicit `public import`s of
  `Init.NotationExtra` and `Trusted.CppAst` (defined by the companion C/C++
  semantics stack rather than `main`; `TrustedBoundary` does not yet define a
  `CapturedCpp` rule on `main`).
- Body definitions appear callee-first by strongly connected component
  (`anneal-lower-common::scc`); `program.bodies` keeps capture order, which
  fixes every `defId`.
- A body with more than 64 locals, blocks, or statements in one block has those
  lists hoisted into 16-element leaf definitions joined by a balanced
  `_root_.List.append` tree (`anneal-lower-common::chunk`), so no definition
  approaches Lean's `maxRecDepth`. Smaller bodies are rendered inline.
- With `-o OUT.lean`, a `sha256sum`-compatible `OUT.lean.sha256` is written
  next to the output.

## Rung 1: C++20 without exceptions

The extractor works on the post-Sema AST, so template specializations arrive
as ordinary monomorphic functions and records named by their mangled symbols.

- **Methods, constructors, destructors.** Parameter `_1` of a non-static member
  function is `this`. Constructors run their member and base initializers
  before the body. Destructors run member destructors (in reverse declaration
  order) and then base destructors after the body, on every exit. Calls to all
  of them are ordinary `CppTerminator.call`s. Trivial default constructors do
  nothing (or zero-fill under value-initialization), and trivial copy and move
  constructors and assignment operators copy the object representation.
- **References** are pointers with `CppSignature.paramNonNull` set for
  reference parameters and `this`. Every use of a reference dereferences it,
  and binding one takes the address of the referent.
- **Lifetimes.** As in C, every block scope ends the lifetimes of its locals;
  an object with a non-trivial destructor first gets a destructor call. A
  `goto` while an object with a non-trivial destructor is live is rejected.
- **Return-slot normalization.** `return e;` writes `_0` (constructing a
  class-type result in place) while every local is still alive, then destroys
  the full-expression's temporaries, then ends every open scope innermost
  first, and only then executes `ret`. A destructor that reads or writes a
  local therefore runs after the return value was captured, as C++ requires.
- **Temporaries.** A prvalue that needs an object becomes a fresh local.
  Unless its lifetime is extended to the enclosing scope by a reference
  binding, it is destroyed at the end of its full-expression, in reverse
  order of construction. Conditionally evaluated trivial-destructor
  temporaries emit `storageLive` in the full-expression's dominating entry
  block so `storageLive` and `storageDead` stay paired on every path;
  temporaries with destructors or reference lifetime extension in
  conditionally evaluated operands, and any temporary in a condition, are
  rejected.
- **`std::nullptr_t`** has the size and alignment of `void *` and is lowered
  as `void *`. Converting a `std::nullptr_t` variable to a value or to a
  pointer yields the null pointer without reading the object ([conv.lval]
  p3.1), so its bytes never matter.
- **`__builtin_bit_cast`** (the primitive under `std::bit_cast` and
  `absl::bit_cast`) becomes `CppExpr.bitCast`, and bit-field members become a
  final `CppProjElem.bitfield` projection.
- **Fail closed.** Virtual calls and polymorphic records (Rung 2), arrays of
  class type, base subobjects at a non-zero offset, by-value parameters with
  non-trivial destructors, named-return-value locals with destructors,
  lambdas, `new`/`delete`, and `throw` are all `UnsupportedConstruct`. The
  SSENF gate covers constructor arguments and the implicit object argument,
  so `Foo f(++x, ++x)` is `UnsequencedSideEffects`.

## Tests

`tests/fixtures/src/*.c` and `tests/fixtures/src/*.cc` are compiled by a real
`anneal-clang-dump` into the checked-in `tests/fixtures/*.json` (see
[Regenerating fixtures](#regenerating-fixtures)). The C++ fixtures include no
headers.
`tests/pipeline.rs` checks the mandatory rejections, the accepted shapes, and
that `clean_adler32` lowers byte-for-byte to
`tests/fixtures/clean_adler32.CapturedCpp.golden` (re-bless with
`ANNEAL_BLESS=1 cargo test`). `tests/gaps.rs` covers comparisons used as
`int`, initializer lists and compound literals, static locals, externalized
callees, block-scope lifetimes, `std::nullptr_t`, and `--entry`
reachability.

### Regenerating fixtures

Run the following from `tests/fixtures/` with `ANNEAL_CLANG_DUMP` set to an
`anneal-clang-dump` binary and `CLANG_BUILTIN_HEADERS` set to the builtin
header directory (`stddef.h`, `stdint.h`, ...) of the Clang it links. The
target triple is pinned so fixtures are host-independent.

```bash
set -euo pipefail
: "${ANNEAL_CLANG_DUMP:?}" "${CLANG_BUILTIN_HEADERS:?}"

common=(-target x86_64-unknown-linux-gnu -std=c11 -O2 -fno-exceptions
        -nobuiltininc -isystem "$CLANG_BUILTIN_HEADERS")

for src in src/*.c; do
  name=$(basename "$src" .c)
  if [ "$name" = clean_adler32 ] || [ "$name" = pos_externalize ]; then
    continue
  fi
  extra=()
  if [ "$name" = neg_exceptions ]; then
    extra=(-fexceptions)
  fi
  "$ANNEAL_CLANG_DUMP" --entry="$name" --output="$name.json" "$src" -- \
    "${common[@]}" "${extra[@]}"
done

# The same source with and without the helper externalized.
"$ANNEAL_CLANG_DUMP" --entry=pos_externalize --externalize-callee=get_ctx \
  --output=pos_externalize.json src/pos_externalize.c -- "${common[@]}"
"$ANNEAL_CLANG_DUMP" --entry=pos_externalize --output=neg_externalize_off.json \
  src/pos_externalize.c -- "${common[@]}"

# The clean-room canary is named after its function, not its file.
"$ANNEAL_CLANG_DUMP" --entry=clean_adler32_update --output=clean_adler32.json \
  src/clean_adler32.c -- "${common[@]}"

# Rung-1 C++20 fixtures use no headers at all, so they need no include path.
cxx=(-target x86_64-unknown-linux-gnu -std=c++20 -fno-exceptions -nobuiltininc
     -nostdinc++)
# <source>:<entry>:<fixture name>
for spec in \
  cxx_count_util:HowMany:cxx_howmany \
  cxx_count_util:RoundUp:cxx_roundup \
  cxx_count_util:Bitmask:cxx_bitmask \
  cxx_guard:guard_return:cxx_guard \
  cxx_clobber:clobber_return:cxx_clobber \
  cxx_bitcast:pod_to_u64:cxx_bitcast_pod \
  cxx_bitcast:pack_desc:cxx_bitfield_pack \
  cxx_bitcast:desc_len:cxx_bitfield_unpack \
  cxx_span:span_sum:cxx_span_sum \
  cxx_span:span_data:cxx_span_data \
  cxx_requires:slice_len:cxx_requires \
  cxx_ref:use_ref:cxx_ref \
  cxx_counter:counter_sum:cxx_counter \
  cxx_temp_dtor:temp_dtor:cxx_temp_dtor \
  cxx_loop_raii:loop_raii:cxx_loop_raii \
  cxx_neg_virtual:call_virtual:cxx_neg_virtual \
  cxx_neg_unseq_ctor:unseq_ctor:cxx_neg_unseq_ctor \
  cxx_nullptr:nullptr_use:cxx_nullptr \
  cxx_entry_reach:entry_reach:cxx_entry_reach; do
  IFS=: read -r src entry name <<<"$spec"
  "$ANNEAL_CLANG_DUMP" --entry="$entry" --output="$name.json" "src/$src.cc" -- \
    "${cxx[@]}"
done
# Without `--entry`, every definition in the file is a root.
"$ANNEAL_CLANG_DUMP" --output=cxx_neg_misc.json src/cxx_neg_misc.cc -- \
  "${cxx[@]}"
"$ANNEAL_CLANG_DUMP" --output=cxx_entry_reach_all.json src/cxx_entry_reach.cc -- \
  "${cxx[@]}"
"$ANNEAL_CLANG_DUMP" --entry=cxx_neg_exceptions --output=cxx_neg_exceptions.json \
  src/cxx_neg_exceptions.cc -- "${cxx[@]}" -fexceptions -fcxx-exceptions
```
