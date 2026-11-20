# Support material

* `niche_probe.rs` — Rust program printing `size_of` / `align_of` for the payloads and
  option-like enums discussed by the package, transmuting `[0u8; 4]` and nonzero byte
  arrays into `Option<NonZeroU32>`, and reading the observed (not guaranteed) byte
  patterns of `Option<bool>` and `Option<Option<bool>>`.
  A final section prints sizes referenced by the non-claims: `Result<u8, Infallible>`,
  `UnsafeCell<NonZeroU32>` and `Option<UnsafeCell<NonZeroU32>>`, `char` and
  `Option<char>`, and enums with one payload variant (`bool` or `(bool, bool)`) plus 254 or
  255 dataless variants.
* `niche_probe_output.txt` — its output on the toolchain recorded in `rustc_version.txt`
  (`rustc 1.102.0-nightly`, commit `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`,
  host `x86_64-unknown-linux-gnu`), built with `rustc -O niche_probe.rs`.
* `small_universe_check.py` / `small_universe_check_output.txt` — exhaustive enumeration
  of all encoders and decoders over pattern universes of at most 4 patterns (and smaller
  universes for layouts below the payload's size), checking the shapes of the statements
  named in its output. A sanity check, not a proof.

Observations from the last probe section, and what they illustrate (observed on the
recorded toolchain; none of them is a language guarantee):

* `size_of::<Result<u8, Infallible>>() == 1`: an extra variant that is uninhabited needs no
  niche, unlike the inhabited dataless variants of the model's `ExtEnum`.
* `size_of::<Option<UnsafeCell<NonZeroU32>>>() == 8` while `UnsafeCell<NonZeroU32>` has
  size 4: `UnsafeCell` disables niche use although the zero pattern is still invalid.
* An enum with a `bool` payload and 254 dataless variants has size 1, with 255 it has size
  2; with a `(bool, bool)` payload the sizes are 2 and 3. So the compiler used at most 254
  niche values for `(bool, bool)` (one field's out-of-range values), although 65532 of its
  65536 initialized two-byte patterns are invalid.

The execution output is evidence about one compiler build on one target. It is not a
proof and not a language guarantee; the values marked "observed; not guaranteed" are
exactly the ones the package's results say cannot be derived from the documented
guarantees.

## Quoted documentation (pinned)

From `rust-lang/rust` at commit `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`,
`library/core/src/option.rs`, lines 116–158 (module docs, section "Representation"):

> Rust guarantees to optimize the following types `T` such that [`Option<T>`]
> has the same size, alignment, and [function call ABI] as `T`. It is
> therefore sound, when `T` is one of these types, to transmute a value `t` of
> type `T` to type `Option<T>` (producing the value `Some(t)`) and to
> transmute a value `Some(t)` of type `Option<T>` to type `T` (producing the
> value `t`).
>
> In some of these cases, Rust further guarantees the following:
> - `transmute::<_, Option<T>>([0u8; size_of::<T>()])` is sound and produces
>   `Option::<T>::None`
> - `transmute::<_, [u8; size_of::<T>()]>(Option::<T>::None)` is sound and produces
>   `[0u8; size_of::<T>()]`
>
> These cases are identified by the second column: [table: `Box<U>` (only
> `Box<U, Global>`) when `U: Sized`; `&U` when `U: Sized`; `&mut U` when `U: Sized`;
> `fn`, `extern "C" fn` always; `num::NonZero*` always; `ptr::NonNull<U>` when
> `U: Sized`; `#[repr(transparent)]` struct around one of the types in this list when it
> holds for the inner type]
>
> This is called the "null pointer optimization" or NPO.
>
> It is further guaranteed that, for the cases above, one can
> [`mem::transmute`] from all valid values of `T` to `Option<T>` and
> from `Some::<T>(_)` to `T` (but transmuting `None::<T>` to `T`
> is undefined behavior).

The stable documentation page https://doc.rust-lang.org/1.89.0/core/option/index.html
(section "Representation") has the same table and the final paragraph, but its first
paragraph ends after "...function call ABI as `T`." without the sentence stating that the
transmute of `t` produces `Some(t)`.

From the same commit, `library/core/src/num/nonzero.rs`, lines 81–89 (docs of
`NonZero<T>`, section "Layout"):

> `NonZero<T>` is guaranteed to have the same layout and bit validity as `T`
> with the exception that the all-zero bit pattern is invalid.
> `Option<NonZero<T>>` is guaranteed to be ABI-compatible with `T`, including in
> FFI.
>
> Thanks to the [null pointer optimization], `NonZero<T>` and
> `Option<NonZero<T>>` are guaranteed to have the same size and alignment:

From `rust-lang/reference` at commit `a2ae66d7037cbedac68746b9510b24cc34b96d69` (the
revision referenced by the `rust-lang/rust` commit above), `src/types/boolean.md`, rule
`type.bool.repr`:

> The value false has the bit pattern `0x00` and the value true has the bit pattern
> `0x01`. It is [undefined behavior] for an object with the boolean type to have any
> other bit pattern.

and `src/type-layout.md`, rules `layout.repr.rust.layout` / `layout.repr.rust.unspecified`
(default representation): "The only data layout guarantees made by this representation
are those required for soundness." ... "There are no other guarantees of data layout made
by this representation."

From `rust-lang/rust` at commit `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`,
`library/core/src/result.rs`, lines 232–258 (section "Representation"; the two paragraphs
stating the guarantees, lines 234–245):

> In some cases, [`Result<T, E>`] comes with size, alignment, and ABI
> guarantees. Specifically, one of either the `T` or `E` type must be a type
> that qualifies for the `Option` [representation guarantees][opt-rep] (let's
> call that type `I`), and the *other* type is a zero-sized type with
> alignment 1 (a "1-ZST").
>
> If that is the case, then `Result<T, E>` has the same size, alignment, and
> [function call ABI] as `I` (and therefore, as `Option<I>`). If `I` is `T`,
> it is therefore sound to transmute a value `t` of type `I` to type
> `Result<T, E>` (producing the value `Ok(t)`) and to transmute a value
> `Ok(t)` of type `Result<T, E>` to type `I` (producing the value `t`). If `I`
> is `E`, the same applies with `Ok` replaced by `Err`.

The section says nothing about `[0u8; size_of::<T>()]`: `Option`'s zeroed-`None` guarantee is
not stated for `Result`.

From the same commit, `library/core/src/cell.rs`, lines 2221–2233 (docs of
`UnsafeCell<T>`, section "Memory layout"):

> `UnsafeCell<T>` has the same in-memory representation as its inner type `T`. [...]
> This is because `UnsafeCell` disables niche optimizations in
> order to avoid its interior mutability property from spreading from `T` into the `Outer` type,

From `rust-lang/reference` at commit `a2ae66d7037cbedac68746b9510b24cc34b96d69`,
`src/behavior-considered-undefined.md`, rule `undefined.validity.char` (line 127):

> A `char` value must not be a surrogate (i.e., must not be in the range `0xD800..=0xDFFF`)
> and must be equal to or less than `char::MAX`.

From `rust-lang/nomicon` at commit `b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6`,
`src/other-reprs.md`, line 105:

> Adding an explicit `repr(u*)`, `repr(i*)`, or `repr(C)` to an enum with fields suppresses
> the null-pointer optimization
