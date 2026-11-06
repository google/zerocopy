r[items.extern]
# External blocks

r[items.extern.syntax]
```grammar,items
ExternBlock ->
    `unsafe`?[^unsafe-2024] `extern` Abi? `{`
        InnerAttribute*
        ExternalItem*
    `}`

ExternalItem ->
    OuterAttribute* (
        MacroInvocationSemi
      | Visibility? StaticItem
      | Visibility? Function
    )
```

[^unsafe-2024]: Starting with the 2024 Edition, the `unsafe` keyword is required semantically.

r[items.extern.intro]
External blocks provide _declarations_ of items that are not _defined_ in the current crate and are the basis of Rust's foreign function interface. These are akin to unchecked imports.

r[items.extern.allowed-kinds]
Two kinds of item _declarations_ are allowed in external blocks: [functions] and [statics].

r[items.extern.safety]
Calling unsafe functions or accessing unsafe statics that are declared in external blocks is only allowed in an [`unsafe` context].

r[items.extern.namespace]
The external block defines its functions and statics in the [value namespace] of the module or block where it is located.

r[items.extern.unsafe-required]
The `unsafe` keyword is semantically required to appear before the `extern` keyword on external blocks.

r[items.extern.edition2024]
> [!EDITION-2024]
> Prior to the 2024 edition, the `unsafe` keyword is optional. The `safe` and `unsafe` item qualifiers are only allowed if the external block itself is marked as `unsafe`.

r[items.extern.fn]
## Functions

r[items.extern.fn.body]
Functions within external blocks are declared in the same way as other Rust functions, with the exception that they must not have a body and are instead terminated by a semicolon.

r[items.extern.fn.param-patterns]
Patterns are not allowed in parameters, only [IDENTIFIER] or `_` may be used.

r[items.extern.fn.qualifiers]
The `safe` and `unsafe` function qualifiers are allowed, but other function qualifiers (e.g. `const`, `async`, `extern`) are not. The `safe` qualifier is rejected in `extern "custom"` blocks.

r[items.extern.fn.foreign-abi]
Functions within external blocks may be called by Rust code, just like functions defined in Rust. The Rust compiler automatically translates between the Rust ABI and the foreign ABI.

r[items.extern.fn.safety]
A function declared in an extern block is implicitly `unsafe` unless the `safe` function qualifier is present.

r[items.extern.fn.fn-ptr]
When coerced to a function pointer, a function declared in an extern block has type `for<'l1, ..., 'lm> extern "abi" fn(A1, ..., An) -> R`, where `'l1`, ... `'lm` are its lifetime parameters, `A1`, ..., `An` are the declared types of its parameters, and `R` is the declared return type.

r[items.extern.static]
## Statics

r[items.extern.static.intro]
Statics within external blocks are declared in the same way as [statics] outside of external blocks, except that they do not have an expression initializing their value.

r[items.extern.static.safety]
Unless a static item declared in an extern block is qualified as `safe`, it is `unsafe` to access that item, whether or not it's mutable, because there is nothing guaranteeing that the bit pattern at the static's memory is valid for the type it is declared with, since some arbitrary (e.g. C) code is in charge of initializing the static.

r[items.extern.static.mut]
Extern statics can be either immutable or mutable just like [statics] outside of external blocks.

r[items.extern.static.read-only]
An immutable static *must* be initialized before any Rust code is executed. It is not enough for the static to be initialized before Rust code reads from it. Once Rust code runs, mutating an immutable static (from inside or outside Rust) is UB, except if the mutation happens to bytes inside of an `UnsafeCell`.

r[items.extern.abi]
## ABI

r[items.extern.abi.intro]
The `extern` keyword can be followed by an optional [ABI] string. The ABI specifies the calling convention of the functions in the block. The calling convention defines a low-level interface for functions, such as how arguments are placed in registers or on the stack, how return values are passed, and who is responsible for cleaning up the stack.

> [!EXAMPLE]
> ```rust
> // Interface to the Windows API.
> unsafe extern "system" { /* ... */ }
> ```

r[items.extern.abi.default]
If the ABI string is not specified, it defaults to `"C"`.

> [!NOTE]
> The `extern` syntax without an explicit ABI is being phased out, so it's better to always write the ABI explicitly.
>
> For more details, see [Rust issue #134986](https://github.com/rust-lang/rust/issues/134986).

r[items.extern.abi.standard]
The following ABI strings are supported on all platforms:

r[items.extern.abi.rust]
* `unsafe extern "Rust"` --- The native calling convention for Rust functions and closures. This is the default when a function is declared without using [`extern fn`]. The Rust ABI offers no stability guarantees.

r[items.extern.abi.c]
* `unsafe extern "C"` --- The "C" ABI matches the default ABI chosen by the dominant C compiler for the target.

r[items.extern.abi.system]
* `unsafe extern "system"` --- This is equivalent to `extern "C"` except on Windows x86_32 where it is equivalent to `"stdcall"` for non-variadic functions, and equivalent to `"C"` for variadic functions.

  > [!NOTE]
  > As the correct underlying ABI on Windows is target-specific, it's best to use `extern "system"` when attempting to link Windows API functions that don't use an explicitly defined ABI.

r[items.extern.abi.unwind]
* `extern "C-unwind"` and `extern "system-unwind"` --- Identical to `"C"` and `"system"`, respectively, but with [different behavior][unwind-behavior] when the callee unwinds (by panicking or throwing a C++ style exception).

r[items.extern.abi.custom]
* `unsafe extern "custom"` --- A custom ABI that is not known to the compiler.

r[items.extern.abi.platform]
There are also some platform-specific ABI strings:

r[items.extern.abi.cdecl]
* `unsafe extern "cdecl"` --- The calling convention typically used with x86_32 C code.
  * Only available on x86_32 targets.
  * Corresponds to MSVC's `__cdecl` and GCC and clang's `__attribute__((cdecl))`.

  > [!NOTE]
  > For details, see:
  >
  > - <https://learn.microsoft.com/en-us/cpp/cpp/cdecl>
  > - <https://en.wikipedia.org/wiki/X86_calling_conventions#cdecl>

r[items.extern.abi.stdcall]
* `unsafe extern "stdcall"` --- The calling convention typically used by the [Win32 API] on x86_32.
  * Only available on x86_32 targets.
  * Corresponds to MSVC's `__stdcall` and GCC and clang's `__attribute__((stdcall))`.

  > [!NOTE]
  > For details, see:
  >
  > - <https://learn.microsoft.com/en-us/cpp/cpp/stdcall>
  > - <https://en.wikipedia.org/wiki/X86_calling_conventions#stdcall>

r[items.extern.abi.win64]
* `unsafe extern "win64"` --- The Windows x64 ABI.
  * Only available on x86_64 targets.
  * "win64" is the same as the "C" ABI on Windows x86_64 targets.
  * Corresponds to GCC and clang's `__attribute__((ms_abi))`.

  > [!NOTE]
  > For details, see:
  >
  > - <https://learn.microsoft.com/en-us/cpp/build/x64-software-conventions>
  > - <https://en.wikipedia.org/wiki/X86_calling_conventions#Microsoft_x64_calling_convention>

r[items.extern.abi.sysv64]
* `unsafe extern "sysv64"` --- The System V ABI.
  * Only available on x86_64 targets.
  * "sysv64" is the same as the "C" ABI on non-Windows x86_64 targets.
  * Corresponds to GCC and clang's `__attribute__((sysv_abi))`.

  > [!NOTE]
  > For details, see:
  >
  > - <https://wiki.osdev.org/System_V_ABI>
  > - <https://en.wikipedia.org/wiki/X86_calling_conventions#System_V_AMD64_ABI>

r[items.extern.abi.aapcs]
* `unsafe extern "aapcs"` --- The soft-float ABI for ARM.
  * Only available on ARM32 targets.
  * "aapcs" is the same as the "C" ABI on soft-float ARM32.
  * Corresponds to clang's `__attribute__((pcs("aapcs")))`.

  > [!NOTE]
  > For details, see:
  >
  > - [Arm Procedure Call Standard](https://developer.arm.com/documentation/107656/0101/Getting-started-with-Armv8-M-based-systems/Procedure-Call-Standard-for-Arm-Architecture--AAPCS-)

r[items.extern.abi.fastcall]
* `unsafe extern "fastcall"` --- A "fast" variant of stdcall that passes some arguments in registers.
  * Only available on x86_32 targets.
  * Corresponds to MSVC's `__fastcall` and GCC and clang's `__attribute__((fastcall))`.

  > [!NOTE]
  > For details, see:
  >
  > - <https://learn.microsoft.com/en-us/cpp/cpp/fastcall>
  > - <https://en.wikipedia.org/wiki/X86_calling_conventions#Microsoft_fastcall>

r[items.extern.abi.thiscall]
* `unsafe extern "thiscall"` --- The calling convention typically used on C++ class member functions on x86_32 MSVC.
  * Only available on x86_32 targets.
  * Corresponds to MSVC's `__thiscall` and GCC and clang's `__attribute__((thiscall))`.

  > [!NOTE]
  > For details, see:
  >
  > - <https://en.wikipedia.org/wiki/X86_calling_conventions#thiscall>
  > - <https://learn.microsoft.com/en-us/cpp/cpp/thiscall>

r[items.extern.abi.efiapi]
* `unsafe extern "efiapi"` --- The ABI used for [UEFI] functions.
  * Only available on x86 and ARM targets (32bit and 64bit).

r[items.extern.abi.platform-unwind-variants]
Like `"C"` and `"system"`, most platform-specific ABI strings also have a [corresponding `-unwind` variant][unwind-behavior]; specifically, these are:

* `"aapcs-unwind"`
* `"cdecl-unwind"`
* `"fastcall-unwind"`
* `"stdcall-unwind"`
* `"sysv64-unwind"`
* `"thiscall-unwind"`
* `"win64-unwind"`

r[items.extern.variadic]
## Variadic functions

r[items.extern.variadic.syntax]
Functions within external blocks may be made variadic by specifying `...` as the last parameter. The variadic parameter may be specified with a pattern.

```rust
unsafe extern "C" {
    unsafe fn foo(...);
    unsafe fn bar(x: i32, ...);
    unsafe fn with_name(format: *const u8, args: ...);
    // SAFETY: This function guarantees it will not access
    // variadic arguments.
    safe fn ignores_variadic_arguments(x: i32, ...);
}
```

> [!WARNING]
> The `safe` qualifier should not be used on a function in an `extern` block unless that function guarantees that it will not access the variadic arguments at all. Passing an unexpected number of arguments or arguments of unexpected type to a variadic function may lead to [undefined behavior][undefined].

r[items.extern.variadic.conventions]
Variadic parameters can only be specified within `extern` blocks with the following ABI strings or their corresponding [`-unwind` variants][items.fn.extern.unwind]:

- `"aapcs"`
- `"C"`
- `"cdecl"`
- `"efiapi"`
- `"system"`
- `"sysv64"`
- `"win64"`

r[items.extern.attributes]
## Attributes on extern blocks

r[items.extern.attributes.intro]
The following [attributes] control the behavior of external blocks.

r[items.extern.attributes.link]
### The `link` attribute

r[items.extern.attributes.link.intro]
The *`link` attribute* specifies the name of a native library that the compiler should link with for the items within an `extern` block.

r[items.extern.attributes.link.syntax]
It uses the [MetaListNameValueStr] syntax to specify its inputs. The `name` key is the name of the native library to link. The `kind` key is an optional value which specifies the kind of library with the following possible values:

r[items.extern.attributes.link.dylib]
- `dylib` --- Indicates a dynamic library. This is the default if `kind` is not specified.

r[items.extern.attributes.link.static]
- `static` --- Indicates a static library.

r[items.extern.attributes.link.framework]
- `framework` --- Indicates a macOS framework. This is only valid for macOS targets.

r[items.extern.attributes.link.raw-dylib]
- `raw-dylib` --- Indicates a dynamic library where the compiler will generate an import library to link against (see [`dylib` versus `raw-dylib`] below for details). This is only valid for Windows targets.

r[items.extern.attributes.link.name-requirement]
The `name` key must be included if `kind` is specified.

r[items.extern.attributes.link.modifiers]
The optional `modifiers` argument is a way to specify linking modifiers for the library to link.

r[items.extern.attributes.link.modifiers-syntax]
Modifiers are specified as a comma-delimited string with each modifier prefixed with either a `+` or `-` to indicate that the modifier is enabled or disabled, respectively.

r[items.extern.attributes.link.modifiers-multiple]
Specifying multiple `modifiers` arguments in a single `link` attribute, or multiple identical modifiers in the same `modifiers` argument is not currently supported. Example: `#[link(name = "mylib", kind = "static", modifiers = "+whole-archive")]`.

r[items.extern.attributes.link.wasm_import_module]
The `wasm_import_module` key may be used to specify the [WebAssembly module] name for the items within an `extern` block when importing symbols from the host environment. The default module name is `env` if `wasm_import_module` is not specified.

<!-- ignore: requires extern linking -->
```rust,ignore
#[link(name = "crypto")]
unsafe extern {
    // …
}

#[link(name = "CoreFoundation", kind = "framework")]
unsafe extern {
    // …
}

#[link(wasm_import_module = "foo")]
unsafe extern {
    // …
}
```

r[items.extern.attributes.link.empty-block]
It is valid to add the `link` attribute on an empty extern block. You can use this to satisfy the linking requirements of extern blocks elsewhere in your code (including upstream crates) instead of adding the attribute to each extern block.

r[items.extern.attributes.link.modifiers-bundle]
#### Linking modifiers: `bundle`

r[items.extern.attributes.link.modifiers-bundle.allowed-kinds]
This modifier is only compatible with the `static` linking kind. Using any other kind will result in a compiler error.

r[items.extern.attributes.link.modifiers-bundle.behavior]
When building a rlib or staticlib `+bundle` means that the native static library will be packed into the rlib or staticlib archive, and then retrieved from there during linking of the final binary.

r[items.extern.attributes.link.modifiers-bundle.behavior-negative]
When building a rlib `-bundle` means that the native static library is registered as a dependency of that rlib "by name", and object files from it are included only during linking of the final binary, the file search by that name is also performed during final linking. When building a staticlib `-bundle` means that the native static library is simply not included into the archive and some higher level build system will need to add it later during linking of the final binary.

r[items.extern.attributes.link.modifiers-bundle.no-effect]
This modifier has no effect when building other targets like executables or dynamic libraries.

r[items.extern.attributes.link.modifiers-bundle.default]
The default for this modifier is `+bundle`.

More implementation details about this modifier can be found in [`bundle` documentation for rustc].

r[items.extern.attributes.link.modifiers-whole-archive]
#### Linking modifiers: `whole-archive`

r[items.extern.attributes.link.modifiers-whole-archive.allowed-kinds]
This modifier is only compatible with the `static` linking kind. Using any other kind will result in a compiler error.

r[items.extern.attributes.link.modifiers-whole-archive.behavior]
`+whole-archive` means that the static library is linked as a whole archive without throwing any object files away.

r[items.extern.attributes.link.modifiers-whole-archive.default]
The default for this modifier is `-whole-archive`.

More implementation details about this modifier can be found in [`whole-archive` documentation for rustc].

r[items.extern.attributes.link.modifiers-verbatim]
#### Linking modifiers: `verbatim`

r[items.extern.attributes.link.modifiers-verbatim.allowed-kinds]
This modifier is compatible with all linking kinds.

r[items.extern.attributes.link.modifiers-verbatim.behavior]
`+verbatim` means that rustc itself won't add any target-specified library prefixes or suffixes (like `lib` or `.a`) to the library name, and will try its best to ask for the same thing from the linker.

r[items.extern.attributes.link.modifiers-verbatim.behavior-negative]
`-verbatim` means that rustc will either add a target-specific prefix and suffix to the library name before passing it to linker, or won't prevent linker from implicitly adding it.

r[items.extern.attributes.link.modifiers-verbatim.default]
The default for this modifier is `-verbatim`.

More implementation details about this modifier can be found in [`verbatim` documentation for rustc].

r[items.extern.attributes.link.kind-raw-dylib]
#### `dylib` versus `raw-dylib`

r[items.extern.attributes.link.kind-raw-dylib.intro]
On Windows, linking against a dynamic library requires that an import library is provided to the linker: this is a special static library that declares all of the symbols exported by the dynamic library in such a way that the linker knows that they have to be dynamically loaded at runtime.

r[items.extern.attributes.link.kind-raw-dylib.import]
Specifying `kind = "dylib"` instructs the Rust compiler to link an import library based on the `name` key. The linker will then use its normal library resolution logic to find that import library. Alternatively, specifying `kind = "raw-dylib"` instructs the compiler to generate an import library during compilation and provide that to the linker instead.

r[items.extern.attributes.link.kind-raw-dylib.platform-specific]
`raw-dylib` is only supported on Windows. Using it when targeting other platforms will result in a compiler error.

r[items.extern.attributes.link.import_name_type]
#### The `import_name_type` key

r[items.extern.attributes.link.import_name_type.intro]
On x86 Windows, names of functions are "decorated" (i.e., have a specific prefix and/or suffix added) to indicate their calling convention. For example, a `stdcall` calling convention function with the name `fn1` that has no arguments would be decorated as `_fn1@0`. However, the [PE Format] does also permit names to have no prefix or be undecorated. Additionally, the MSVC and GNU toolchains use different decorations for the same calling conventions which means, by default, some Win32 functions cannot be called using the `raw-dylib` link kind via the GNU toolchain.

r[items.extern.attributes.link.import_name_type.values]
To allow for these differences, when using the `raw-dylib` link kind you may also specify the `import_name_type` key with one of the following values to change how functions are named in the generated import library:

* `decorated`: The function name will be fully-decorated using the MSVC toolchain format.
* `noprefix`: The function name will be decorated using the MSVC toolchain format, but skipping the leading `?`, `@`, or optionally `_`.
* `undecorated`: The function name will not be decorated.

r[items.extern.attributes.link.import_name_type.default]
If the `import_name_type` key is not specified, then the function name will be fully-decorated using the target toolchain's format.

r[items.extern.attributes.link.import_name_type.variables]
Variables are never decorated and so the `import_name_type` key has no effect on how they are named in the generated import library.

r[items.extern.attributes.link.import_name_type.platform-specific]
The `import_name_type` key is only supported on x86 Windows. Using it when targeting other platforms will result in a compiler error.

<!-- template:attributes -->
r[items.extern.attributes.link_name]
### The `link_name` attribute

r[items.extern.attributes.link_name.intro]
The *`link_name` [attribute][attributes]* may be applied to declarations inside an `extern` block to specify the symbol to import for the given function or static.

> [!EXAMPLE]
> ```rust
> unsafe extern "C" {
>     #[link_name = "actual_symbol_name"]
>     safe fn name_in_rust();
> }
> ```

r[items.extern.attributes.link_name.syntax]
The `link_name` attribute uses the [MetaNameValueStr] syntax.

r[items.extern.attributes.link_name.invalid-names]
The symbol name must not be the empty string or contain any `U+0000` (NUL) bytes.

r[items.extern.attributes.link_name.allowed-positions]
The `link_name` attribute may only be applied to a function or static item in an `extern` block.

> [!NOTE]
> `rustc` ignores use in other positions but lints against it. This may become an error in the future.

r[items.extern.attributes.link_name.duplicates]
Only the first use of `link_name` on an item has effect.

> [!NOTE]
> `rustc` lints against any use following the first with a future-compatibility warning. This may become an error in the future.

r[items.extern.attributes.link_name.link_ordinal]
The `link_name` attribute may not be used with the [`link_ordinal`] attribute.

r[items.extern.attributes.link_ordinal]
### The `link_ordinal` attribute

r[items.extern.attributes.link_ordinal.intro]
The *`link_ordinal` attribute* can be applied on declarations inside an `extern` block to indicate the numeric ordinal to use when generating the import library to link against. An ordinal is a unique number per symbol exported by a dynamic library on Windows and can be used when the library is being loaded to find that symbol rather than having to look it up by name.

> [!WARNING]
> `link_ordinal` should only be used in cases where the ordinal of the symbol is known to be stable: if the ordinal of a symbol is not explicitly set when its containing binary is built then one will be automatically assigned to it, and that assigned ordinal may change between builds of the binary.

```rust
# #[cfg(all(windows, target_arch = "x86"))]
#[link(name = "exporter", kind = "raw-dylib")]
unsafe extern "stdcall" {
    #[link_ordinal(15)]
    safe fn imported_function_stdcall(i: i32);
}
```

r[items.extern.attributes.link_ordinal.allowed-kinds]
This attribute is only used with the `raw-dylib` linking kind. Using any other kind will result in a compiler error.

r[items.extern.attributes.link_ordinal.exclusive]
Using this attribute with the `link_name` attribute will result in a compiler error.

r[items.extern.attributes.fn-parameters]
### Attributes on function parameters

Attributes on extern function parameters follow the same rules and restrictions as [regular function parameters].

[ABI]: glossary.abi
[PE Format]: https://learn.microsoft.com/windows/win32/debug/pe-format#import-name-type
[UEFI]: https://uefi.org/specifications
[WebAssembly module]: https://webassembly.github.io/spec/core/syntax/modules.html
[`bundle` documentation for rustc]: ../../rustc/command-line-arguments.html#linking-modifiers-bundle
[`dylib` versus `raw-dylib`]: #dylib-versus-raw-dylib
[`extern fn`]: items.fn.extern
[`unsafe` context]: ../unsafe-keyword.md
[`verbatim` documentation for rustc]: ../../rustc/command-line-arguments.html#linking-modifiers-verbatim
[`whole-archive` documentation for rustc]: ../../rustc/command-line-arguments.html#linking-modifiers-whole-archive
[attributes]: ../attributes.md
[functions]: functions.md
[regular function parameters]: functions.md#attributes-on-function-parameters
[statics]: static-items.md
[unwind-behavior]: functions.md#unwinding
[value namespace]: ../names/namespaces.md
[win32 api]: https://learn.microsoft.com/en-us/windows/win32/api/
[`link_ordinal`]: items.extern.attributes.link_ordinal
