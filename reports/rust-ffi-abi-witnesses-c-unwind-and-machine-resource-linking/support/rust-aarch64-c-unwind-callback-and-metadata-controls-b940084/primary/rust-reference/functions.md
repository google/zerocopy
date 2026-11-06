r[items.fn]
# Functions

r[items.fn.syntax]
```grammar,items
Function ->
    FunctionQualifiers `fn` IDENTIFIER GenericParams?
        `(` FunctionParameters? `)`
        FunctionReturnType? WhereClause?
        ( BlockExpression | `;` )

FunctionQualifiers -> `const`? `async`?[^async-edition] ItemSafety?[^extern-qualifiers] (`extern` Abi?)?

ItemSafety -> `safe`[^extern-safe] | `unsafe`

Abi -> STRING_LITERAL | RAW_STRING_LITERAL

FunctionParameters ->
      SelfParam `,`?
    | (SelfParam `,`)? FunctionParam (`,` FunctionParam)* `,`?

SelfParam -> OuterAttribute* ( ShorthandSelf | TypedSelf )

ShorthandSelf -> (`&` | `&` Lifetime)? `mut`? `self`

TypedSelf -> `mut`? `self` `:` Type

FunctionParam -> OuterAttribute* ( FunctionParamPattern | `...` | Type[^fn-param-2015] )

FunctionParamPattern -> PatternNoTopAlt `:` ( Type | `...` )

FunctionReturnType -> `->` Type
```

[^async-edition]: The `async` qualifier is not allowed in the 2015 edition.

[^extern-safe]: The `safe` function qualifier is only allowed semantically within `extern` blocks.

[^extern-qualifiers]: *Relevant to editions earlier than Rust 2024*: Within `extern` blocks, the `safe` or `unsafe` function qualifier is only allowed when the `extern` is qualified as `unsafe`.

[^fn-param-2015]: Function parameters with only a type are only allowed in an associated function of a [trait item] in the 2015 edition.

r[items.fn.intro]
A _function_ consists of a [block] (that's the _body_ of the function), along with a name, a set of parameters, and an output type. Other than a name, all these are optional.

r[items.fn.namespace]
Functions are declared with the keyword `fn` which defines the given name in the [value namespace] of the module or block where it is located.

r[items.fn.signature]
Functions may declare a set of *input* [*variables*][variables] as parameters, through which the caller passes arguments into the function, and the *output* [*type*][type] of the value the function will return to its caller on completion.

r[items.fn.implicit-return]
If the output type is not explicitly stated, it is the [unit type].

r[items.fn.fn-item-type]
When referred to, a _function_ yields a first-class *value* of the corresponding [zero-sized] [*function item type*], which when called evaluates to a direct call to the function.

For example, this is a simple function:

```rust
fn answer_to_life_the_universe_and_everything() -> i32 {
    return 42;
}
```

r[items.fn.safety-qualifiers]
The `safe` function is semantically only allowed when used in an [`extern` block].

r[items.fn.params]
## Function parameters

r[items.fn.params.intro]
Function parameters are irrefutable [patterns], so any pattern that is valid in an else-less `let` binding is also valid as a parameter:

```rust
fn first((value, _): (i32, i32)) -> i32 { value }
```

r[items.fn.params.self-pat]
If the first parameter is a [SelfParam], this indicates that the function is a [method].

r[items.fn.params.self-restriction]
Functions with a self parameter may only appear as an [associated function] in a [trait] or [implementation].

r[items.fn.params.varargs]
A parameter with the `...` token indicates a [C-variadic function] and may only be used as the last parameter. In a function declaration in an [`extern` block], the C-variadic parameter may have a pattern, such as `ap: ...`, and in a [C-variadic function] definition or C-variadic associated function declaration in a trait definition, the pattern is mandatory.

```rust
unsafe extern "C" {
    unsafe fn f1(...);
    unsafe fn f2(ap: ...);
}

unsafe extern "C" fn f3(ap: ...) {}

trait Tr {
    unsafe extern "C" fn f4(ap: ...);
}
```

```rust,compile_fail
unsafe extern "C" fn f(...) {} // ERROR: Missing pattern.
```

```rust,compile_fail
trait Tr {
    unsafe extern "C" fn f(...); // ERROR: Missing pattern.
}
```

r[items.fn.body]
## Function body

r[items.fn.body.intro]
The body block of a function is conceptually wrapped in another block that first binds the argument patterns and then `return`s the value of the function's body. This means that the tail expression of the block, if evaluated, ends up being returned to the caller. As usual, an explicit return expression within the body of the function will short-cut that implicit return, if reached.

For example, the function above behaves as if it was written as:

<!-- ignore: example expansion -->
```rust,ignore
// argument_0 is the actual first argument passed from the caller
let (value, _) = argument_0;
return {
    value
};
```

r[items.fn.body.bodyless]
Functions without a body block are terminated with a semicolon. This form may only appear in a [trait] or [external block].

r[items.fn.generics]
## Generic functions

r[items.fn.generics.intro]
A _generic function_ allows one or more _parameterized types_ to appear in its signature. Each type parameter must be explicitly declared in an angle-bracket-enclosed and comma-separated list, following the function name.

```rust
// foo is generic over A and B

fn foo<A, B>(x: A, y: B) {
# }
```

r[items.fn.generics.param-names]
Inside the function signature and body, the name of the type parameter can be used as a type name.

r[items.fn.generics.param-bounds]
[Trait] bounds can be specified for type parameters to allow methods from that trait to be called on values of that type. This is specified using the `where` syntax:

```rust
# use std::fmt::Debug;
fn foo<T>(x: T) where T: Debug {
# }
```

r[items.fn.generics.mono]
When a generic function is referenced, its type is instantiated based on the context of the reference. For example, calling the `foo` function here:

```rust
use std::fmt::Debug;

fn foo<T>(x: &[T]) where T: Debug {
    // details elided
}

foo(&[1, 2]);
```

will instantiate type parameter `T` with `i32`.

r[items.fn.generics.explicit-arguments]
The type parameters can also be explicitly supplied in a trailing [path] component after the function name. This might be necessary if there is not sufficient context to determine the type parameters. For example, `mem::size_of::<u32>() == 4`.

r[items.fn.extern]
## Extern function qualifier

r[items.fn.extern.intro]
The `extern` function qualifier allows providing function _definitions_ that can be called with a particular ABI:

<!-- ignore: fake ABI -->
```rust,ignore
extern "ABI" fn foo() { /* ... */ }
```

r[items.fn.extern.def]
These are often used in combination with [external block] items which provide function _declarations_ that can be used to call functions without providing their _definition_:

<!-- ignore: fake ABI -->
```rust,ignore
unsafe extern "ABI" {
  unsafe fn foo(); /* no body */
  safe fn bar(); /* no body */
}
unsafe { foo() };
bar();
```

r[items.fn.extern.default-abi]
When `"extern" Abi?*` is omitted from `FunctionQualifiers` in function items, the ABI `"Rust"` is assigned. For example:

```rust
fn foo() {}
```

is equivalent to:

```rust
extern "Rust" fn foo() {}
```

r[items.fn.extern.foreign-call]
Functions can be called by foreign code, and using an ABI that differs from Rust allows, for example, to provide functions that can be called from other programming languages like C:

```rust
// Declares a function with the "C" ABI
extern "C" fn new_i32() -> i32 { 0 }

// Declares a function with the "stdcall" ABI
# #[cfg(any(windows, target_arch = "x86"))]
extern "stdcall" fn new_i32_stdcall() -> i32 { 0 }
```

r[items.fn.extern.default-extern]
Just as with [external block], when the `extern` keyword is used and the `"ABI"` is omitted, the ABI used defaults to `"C"`. That is, this:

```rust
extern fn new_i32() -> i32 { 0 }
let fptr: extern fn() -> i32 = new_i32;
```

is equivalent to:

```rust
extern "C" fn new_i32() -> i32 { 0 }
let fptr: extern "C" fn() -> i32 = new_i32;
```

r[items.fn.extern.unwind]
### Unwinding

r[items.fn.extern.unwind.intro]
Most ABI strings come in two variants, one with an `-unwind` suffix and one without. The `Rust` ABI always permits unwinding, so there is no `Rust-unwind` ABI. The choice of ABI, together with the runtime [panic handler], determines the behavior when unwinding out of a function.

r[items.fn.extern.unwind.behavior]
The table below indicates the behavior of an unwinding operation reaching each type of ABI boundary (function declaration or definition using the corresponding ABI string). Note that the Rust runtime is not affected by, and cannot have an effect on, any unwinding that occurs entirely within another language's runtime, that is, unwinds that are thrown and caught without reaching a Rust ABI boundary.

The `panic`-unwind column refers to [panicking] via the `panic!` macro and similar standard library mechanisms, as well as to any other Rust operations that cause a panic, such as out-of-bounds array indexing or integer overflow.

The "unwinding" ABI category refers to `"Rust"` (the implicit ABI of Rust functions not marked `extern`), `"C-unwind"`, and any other ABI with `-unwind` in its name. The "non-unwinding" ABI category refers to all other ABI strings, including `"C"` and `"stdcall"`.

Native unwinding is defined per-target. On targets that support throwing and catching C++ exceptions, it refers to the mechanism used to implement this feature. Some platforms implement a form of unwinding referred to as ["forced unwinding"][forced-unwinding]; `longjmp` on Windows and `pthread_exit` in `glibc` are implemented this way. Forced unwinding is explicitly excluded from the "Native unwind" column in the table.

| panic runtime  | ABI           | `panic`-unwind                        | Native unwind (unforced) |
| -------------- | ------------  | ------------------------------------- | -----------------------  |
| `panic=unwind` | unwinding     | unwind                                | unwind                   |
| `panic=unwind` | non-unwinding | abort (see notes below)               | [undefined behavior]     |
| `panic=abort`  | unwinding     | `panic` aborts without unwinding      | abort                    |
| `panic=abort`  | non-unwinding | `panic` aborts without unwinding      | [undefined behavior]     |

r[items.fn.extern.abort]
With `panic=unwind`, when a `panic` is turned into an abort by a non-unwinding ABI boundary, either no destructors (`Drop` calls) will run, or all destructors up until the ABI boundary will run. It is unspecified which of those two behaviors will happen.

For other considerations and limitations regarding unwinding across FFI boundaries, see the [relevant section in the Panic documentation][panic-ffi].

r[items.fn.extern.custom]
### Extern "custom"

r[items.fn.extern.custom.intro]
An `extern "custom"` function has an unknown, custom ABI. The only way to call such a function is via [inline assembly].

> [!EXAMPLE]
> ```rust
> # #[cfg(target_arch = "x86_64")] {
> # use core::arch::{asm, naked_asm};
> #
> /// Adds 1 to `rax`.
> ///
> /// This function uses a custom calling convention: the argument is
> /// passed in `rax`, the result is returned in `rax`, the flags may
> /// be clobbered, and all other registers are preserved.
> #[unsafe(naked)]
> unsafe extern "custom" fn increment() {
>     naked_asm!(
>         "add rax, 1",
>         "ret",
>     )
> }
>
> let mut x: u64 = 41;
> // SAFETY: The inline assembly respects the calling convention of
> // `increment`: the argument is passed in `rax`, the result is read
> // from `rax`, and no other registers are affected.
> unsafe {
>     asm!(
>         "call {}",
>         sym increment,
>         inout("rax") x,
>     );
> }
> assert_eq!(x, 42);
> # }
> ```

r[items.fn.extern.custom.signature]
An `extern "custom"` function must:

- Be `unsafe`.
- Not have any parameters.
- Return the [unit type], with the return type either omitted or written explicitly as `()`.

> [!NOTE]
> The rule is syntactic. The return type may not be a type alias, even one defined to be the [unit type].
>
> ```rust,compile_fail
> type Unit = ();
>
> #[unsafe(naked)]
> unsafe extern "custom" fn f() -> Unit { // ERROR: Not explicit `()`.
>     core::arch::naked_asm!("ret")
> }
> ```

r[items.fn.extern.custom.naked]
An `extern "custom"` function definition must be a [naked function].

[forced-unwinding]: https://rust-lang.github.io/rfcs/2945-c-unwind-abi.html#forced-unwinding
[panic handler]: ../panic.md#the-panic_handler-attribute
[panic-ffi]: ../panic.md#unwinding-across-ffi-boundaries
[panicking]: ../panic.md
[undefined behavior]: ../behavior-considered-undefined.md

r[items.fn.const]
## Const functions

See [const functions] for the definition of const functions.

r[items.fn.async]
## Async functions

r[items.fn.async.intro]
Functions may be qualified as async, and this can also be combined with the `unsafe` qualifier:

```rust
async fn regular_example() { }
async unsafe fn unsafe_example() { }
```

r[items.fn.async.future]
Async functions do no work when called: instead, they capture their arguments into a future. When polled, that future will execute the function's body.

r[items.fn.async.desugar-brief]
An async function is roughly equivalent to a function that returns [`impl Future`] and with an [`async move` block][async-blocks] as its body:

```rust
// Source
async fn example(x: &str) -> usize {
    x.len()
}
```

is roughly equivalent to:

```rust
# use std::future::Future;
// Desugared
fn example<'a>(x: &'a str) -> impl Future<Output = usize> + 'a {
    async move { x.len() }
}
```

r[items.fn.async.desugar]
The actual desugaring is more complex:

r[items.fn.async.lifetime-capture]
- The return type in the desugaring is assumed to capture all lifetime parameters from the `async fn` declaration. This can be seen in the desugared example above, which explicitly outlives, and hence captures, `'a`.

r[items.fn.async.param-capture]
- The [`async move` block][async-blocks] in the body captures all function parameters, including those that are unused or bound to a `_` pattern. This ensures that function parameters are dropped in the same order as they would be if the function were not async, except that the drop occurs when the returned future has been fully awaited.

For more information on the effect of async, see [`async` blocks][async-blocks].

[async-blocks]: ../expressions/block-expr.md#async-blocks
[`impl Future`]: ../types/impl-trait.md

r[items.fn.async.edition2018]
> [!EDITION-2018]
> Async functions are only available beginning with Rust 2018.

r[items.fn.async.safety]
### Combining `async` and `unsafe`

r[items.fn.async.safety.intro]
It is legal to declare a function that is both async and unsafe. The resulting function is unsafe to call and (like any async function) returns a future. This future is just an ordinary future and thus an `unsafe` context is not required to "await" it:

```rust
// Returns a future that, when awaited, dereferences `x`.
//
// Soundness condition: `x` must be safe to dereference until
// the resulting future is complete.
async unsafe fn unsafe_example(x: *const i32) -> i32 {
  *x
}

async fn safe_example() {
    // An `unsafe` block is required to invoke the function initially:
    let p = 22;
    let future = unsafe { unsafe_example(&p) };

    // But no `unsafe` block required here. This will
    // read the value of `p`:
    let q = future.await;
}
```

Note that this behavior is a consequence of the desugaring to a function that returns an `impl Future` -- in this case, the function we desugar to is an `unsafe` function, but the return value remains the same.

Unsafe is used on an async function in precisely the same way that it is used on other functions: it indicates that the function imposes some additional obligations on its caller to ensure soundness. As in any other unsafe function, these conditions may extend beyond the initial call itself -- in the snippet above, for example, the `unsafe_example` function took a pointer `x` as argument, and then (when awaited) dereferenced that pointer. This implies that `x` would have to be valid until the future is finished executing, and it is the caller's responsibility to ensure that.

r[items.fn.c-variadic]
## C-variadic functions

r[items.fn.c-variadic.intro]
A *C-variadic* function accepts a variable argument list `pat: ...` as its final parameter.

```rust
unsafe extern "C" fn f(mut ap: ...) -> f64 {
    unsafe { ap.next_arg::<f64>() }
}
```

```rust,compile_fail
unsafe extern "C" fn f(ap: ..., _: ()) {} // ERROR: `...` must be last.
```

This parameter stands in for an arbitrary number of arguments that may be passed by the caller.

r[items.fn.c-variadic.parameter-type]
The type of `pat` in the function body is [`VaList<'_>`].

```rust
# use core::ffi::VaList;
unsafe extern "C" fn f(ap: ...) {
    let _: VaList<'_> = ap;
}
```

r[items.fn.c-variadic.lifetime]
A C-variadic function definition is implicitly generic over the lifetime of its variadic parameter, as if the parameter had type `VaList<'x>` for a fresh, unnameable lifetime `'x`. Because the function must be valid for any such lifetime, the `VaList` cannot be proved to outlive any caller-provided lifetime (and so cannot escape the call) and no caller-provided lifetime can be proved to outlive it.

```rust,compile_fail
# use core::ffi::VaList;
fn b_outlives_a<'a, 'b: 'a>(_: &mut VaList<'a>, _: &mut &'b mut u8) {}
unsafe extern "C" fn f(mut r: &mut u8, mut ap: ...) {
    b_outlives_a(&mut ap, &mut r); // ERROR: May not live long enough.
}
```

```rust,compile_fail
# use core::ffi::VaList;
fn a_outlives_b<'a: 'b, 'b>(_: &mut VaList<'a>, _: &mut &'b mut u8) {}
unsafe extern "C" fn f(mut r: &mut u8, mut ap: ...) {
    a_outlives_b(&mut ap, &mut r); // ERROR: May not live long enough.
}
```

> [!NOTE]
> This is different than if the data were a stack variable: any caller-provided lifetime can be proved to outlive a borrow of a callee stack variable.
>
> ```rust
> struct MockVaList<'data>(&'data u8);
> fn b_outlives_a<'a, 'b: 'a>(_: &mut MockVaList<'a>, _: &mut &'b mut u8) {}
> unsafe extern "C" fn f(mut r: &mut u8) {
>     let data = 0;
>     let mut ap = MockVaList(&data);
>     b_outlives_a(&mut ap, &mut r); // OK.
> }
> ```

r[items.fn.c-variadic.desugar-brief]
A C-variadic function definition is roughly equivalent to a function operating on a [`VaList`].

```rust
unsafe extern "C" fn f(mut ap: ...) -> i32 {
    unsafe { ap.next_arg::<i32>() }
}
```

Roughly desugars to:

<!-- no_run: conceptual desugaring -->
```rust,no_run
# #![ feature(core_intrinsics) ]
# #![allow(internal_features)]
# use core::ffi::VaList;
# use core::mem::MaybeUninit;
use core::intrinsics::{va_arg, va_end};
// `va_start` is magic and has no intrinsic.
fn va_start(ap: *mut VaList<'_>) { /* magic */ }
unsafe extern "C" fn f() -> i32 {
    unsafe {
        let mut ap: MaybeUninit<VaList<'_>> = MaybeUninit::uninit();
        va_start(ap.as_mut_ptr());
        let mut ap = ap.assume_init();
        let x = va_arg::<i32>(&mut ap);
        va_end(&mut ap);
        x
    }
}
```

> [!NOTE]
> In an actual C-variadic function definition, the lifetime in `VaList<'_>` is different from what this code would suggest. See [items.fn.c-variadic.lifetime].

r[items.fn.c-variadic.next-arg-safety]
Calling `VaList::next_arg` to read an argument of type `T` is only safe if all of the following conditions are satisfied:

- There is another C-variadic argument to read.
- The actual type of the argument `U` is compatible with `T` (as defined below).
- If `U` and `T` are both integer types, then the value passed by the caller must be
representable in both types.

Types `T` and `U` are compatible when one of the following is true:

- `T` and `U` are the same type (up to free lifetimes).
- `T` and `U` are integer types of the same size.
- `T` and `U` are both pointers and their target types are compatible.
- `T` is a pointer to `c_void` and `U` is a pointer to `i8` or `u8`, or vice versa.

Examples of compatible types are:

- `u32` and `i32` --- but UB may still occur if the value is not representable in the target type.
- `u64` and `usize` --- on a 64-bit platform.
- `*const &'a u32` and `*mut &'static u32` --- these types are equal up to free lifetimes.

Examples of incompatible types are:

- `usize` and `*const _` --- pointers and integers are not compatible.
- `*const fn(&'static ())` and `*const for<'a> fn(&'a ())` --- these types are not equal up to free lifetimes.

r[items.fn.c-variadic.abi-compatibility]
[`VaList`] is ABI compatible with the C `va_list` type.

```rust
# use core::ffi::{c_char, c_int, VaList};
unsafe extern "C" {
    // The C `vprintf` function is:
    //
    //     int vprintf(const char *format, va_list ap);
    //
    unsafe fn vprintf(fmt: *const c_char, ap: VaList<'_>) -> c_int;
}

unsafe extern "C" fn print(fmt: *const c_char, ap: ...) -> c_int {
    // The `VaList` is passed directly to the C function.
    unsafe { vprintf(fmt, ap) }
}
```

r[items.fn.c-variadic.abi]
Except on [naked functions], only `extern "C"` and `extern "C-unwind"` function definitions can accept a variable argument list.

```rust,compile_fail
unsafe fn f(ap: ...) {} // ERROR: Not supported.
```

```rust,compile_fail
unsafe extern "sysv64" fn f(ap: ...) {} // ERROR: Not supported.
```

A naked function can accept a variable argument list only if its ABI string is accepted under [items.extern.variadic.conventions].

```rust
# #[cfg(target_arch = "x86_64")] {
/// Computes the dot product of the `n`-dimensional vector `v`, passed
/// as `n` C-variadic `f64` arguments, with the vector `(c, ..., c)`.
/// That is, it computes `c * (v1 + ... + vn)`.
///
/// # Safety
///
/// The caller must pass `n` in the range `1..=7`, followed by exactly
/// `n` values of type `f64`.
// SAFETY: The body respects the "sysv64" calling convention, upholds
// the signature, and does not fall through.
#[unsafe(naked)]
unsafe extern "sysv64" fn dot(n: u64, c: f64, v: ...) -> f64 {
    core::arch::naked_asm!(
        // The "sysv64" calling convention passes `n` in `rdi`, `c` in
        // `xmm0`, and the coordinates in `xmm1` through `xmm7`,
        // in order. (The caller also passes the number of vector
        // registers used in `al`.)
        //
        // The sum takes the last `n - 1` additions of the chain
        // below. Each `addsd` encodes in exactly 4 bytes, so we enter
        // the chain `4 * (n - 1)` bytes before the `mulsd`.
        "neg rdi", // I.e., `rdi = -n`.
        "lea rax, [rip + 2f]", // I.e., `rax` = address of label 2.
        "lea rax, [rax + rdi*4 + 4]", // I.e., `rax -= 4 * (n - 1)`.
        "jmp rax",
        "addsd xmm6, xmm7", // Entered when `n` is 7.
        "addsd xmm5, xmm6", // ... when `n` is at least 6.
        "addsd xmm4, xmm5",
        "addsd xmm3, xmm4",
        "addsd xmm2, xmm3",
        "addsd xmm1, xmm2", // ... when `n` is at least 2.
        "2:",
        "mulsd xmm0, xmm1", // The result is returned in `xmm0`.
        "ret",
    )
}

// SAFETY: `dot` is passed `n` variadic `f64` arguments in each call.
let dot2 = unsafe { dot(2, 10.0, 3.0, 4.0) };
assert_eq!(dot2, 70.0);
let dot7 = unsafe { dot(7, 2.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0) };
assert_eq!(dot7, 56.0);
# }
```

r[items.fn.c-variadic.safety]
When a variable argument list is used in the signature:

- Function definitions must be `unsafe`.
- Function declarations within trait definitions must be `unsafe`.
- Function declarations in `extern` blocks may be `safe`.

```rust,compile_fail
extern "C" fn f(ap: ...) {} // ERROR: Must be `unsafe`.
```

```rust,compile_fail
trait Tr {
    extern "C" fn f(ap: ...); // ERROR: Must be `unsafe`.
}
```

```rust
unsafe extern "C" {
    safe fn f(ap: ...); // OK.
}
```

> [!NOTE]
> For `safe` function declarations in an `extern` block, see the warning in [items.extern.variadic].

r[items.fn.c-variadic.async]
A C-variadic function cannot be `async`.

```rust,compile_fail
async unsafe extern "C" fn f(ap: ...) {} // ERROR: Cannot be `async`.
```

r[items.fn.c-variadic.const]
A C-variadic function cannot be `const`.

```rust,compile_fail,E0658
const unsafe extern "C" fn f(ap: ...) {} // ERROR: Cannot be `const`.
```

r[items.fn.c-variadic.stable-targets]
Support for C-variadic function definitions is stable on the following target architectures:

- x86 and x86-64
- ARM
- AArch64 and Arm64EC
- RISC-V 32-bit and 64-bit (except when using the ilp32e ABI)
- LoongArch 32-bit and 64-bit
- s390x
- PowerPC and PowerPC64
- AMDGPU and NVPTX
- Wasm32 and Wasm64
- C-SKY
- Xtensa
- Hexagon
- SPARC64
- MIPS

> [!NOTE]
> Some target architectures (e.g., BPF) do not support C-variadic function definitions. The compiler will emit an error if such a definition is used on an unsupported target.

r[items.fn.attributes]
## Attributes on functions

r[items.fn.attributes.intro]
[Outer attributes][attributes] are allowed on functions. [Inner attributes][attributes] are allowed directly after the `{` inside its body [block].

This example shows an inner attribute on a function. The function is documented with just the word "Example".

```rust
fn documented() {
    #![doc = "Example"]
}
```

> [!NOTE]
> Except for lints, it is idiomatic to only use outer attributes on function items.

r[items.fn.attributes.builtin-attributes]
The attributes that have meaning on a function are:

- [`cfg_attr`]
- [`cfg`]
- [`cold`]
- [`deprecated`]
- [`doc`]
- [`export_name`]
- [`inline`]
- [`link_section`]
- [`must_use`]
- [`no_mangle`]
- [Lint check attributes]
- [Procedural macro attributes]
- [Testing attributes]

r[items.fn.param-attributes]
## Attributes on function parameters

r[items.fn.param-attributes.intro]
[Outer attributes][attributes] are allowed on function parameters and the permitted [built-in attributes] are restricted to `cfg`, `cfg_attr`, `allow`, `warn`, `deny`, and `forbid`.

```rust
fn len(
    #[cfg(windows)] slice: &[u16],
    #[cfg(not(windows))] slice: &[u8],
) -> usize {
    slice.len()
}
```

r[items.fn.param-attributes.parsed-attributes]
Inert helper attributes used by procedural macro attributes applied to items are also allowed but be careful to not include these inert attributes in your final `TokenStream`.

For example, the following code defines an inert `some_inert_attribute` attribute that is not formally defined anywhere and the `some_proc_macro_attribute` procedural macro is responsible for detecting its presence and removing it from the output token stream.

<!-- ignore: requires proc macro -->
```rust,ignore
#[some_proc_macro_attribute]
fn foo_oof(#[some_inert_attribute] arg: u8) {
}
```

[const contexts]: ../const_eval.md#const-context
[const functions]: ../const_eval.md#const-functions
[external block]: external-blocks.md
[path]: ../paths.md
[block]: ../expressions/block-expr.md
[variables]: ../variables.md
[type]: ../types.md#type-expressions
[unit type]: ../types/tuple.md
[*function item type*]: ../types/function-item.md
[Trait]: traits.md
[attributes]: ../attributes.md
[`cfg`]: ../conditional-compilation.md#the-cfg-attribute
[`cfg_attr`]: ../conditional-compilation.md#the-cfg_attr-attribute
[lint check attributes]: ../attributes/diagnostics.md#lint-check-attributes
[procedural macro attributes]: macro.proc.attribute
[testing attributes]: ../attributes/testing.md
[`cold`]: ../attributes/codegen.md#the-cold-attribute
[`inline`]: ../attributes/codegen.md#the-inline-attribute
[naked function]: ../attributes/codegen.md#the-naked-attribute
[`deprecated`]: ../attributes/diagnostics.md#the-deprecated-attribute
[`doc`]: ../../rustdoc/the-doc-attribute.html
[`must_use`]: ../attributes/diagnostics.md#the-must_use-attribute
[patterns]: ../patterns.md
[`export_name`]: ../abi.md#the-export_name-attribute
[`link_section`]: ../abi.md#the-link_section-attribute
[`no_mangle`]: ../abi.md#the-no_mangle-attribute
[built-in attributes]: ../attributes.md#built-in-attributes-index
[trait item]: traits.md
[method]: associated-items.md#methods
[associated function]: associated-items.md#associated-functions-and-methods
[implementation]: implementations.md
[value namespace]: ../names/namespaces.md
[C-variadic function]: items.fn.c-variadic.intro
[`extern` block]: external-blocks.md
[`VaList<'_>`]: lang-types.va-list
[`VaList`]: lang-types.va-list
[zero-sized]: glossary.zst
[inline assembly]: ../inline-assembly.md
[naked functions]: attributes.codegen.naked
