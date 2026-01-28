# buf-list

[![buf-list on crates.io](https://img.shields.io/crates/v/buf-list)](https://crates.io/crates/buf-list) [![Documentation (latest release)](https://docs.rs/buf-list/badge.svg)](https://docs.rs/buf-list/) [![Documentation (main)](https://img.shields.io/badge/docs-main-brightgreen)](https://sunshowers-code.github.io/buf-list/rustdoc/buf_list/) [![License](https://img.shields.io/badge/license-Apache-green.svg)](LICENSE)

A segmented list of `bytes::Bytes` chunks.

## Overview

This crate provides a `BufList` type that is a list of [`Bytes`](bytes::Bytes) chunks. The
type implements `bytes::Buf`, so it can be used in any APIs that use `Buf`.

The main use case for `BufList` is to buffer data received as a stream of chunks without
having to copy them into a single contiguous chunk of memory. The `BufList` can then be passed
into any APIs that accept `Buf`.

If you've ever wanted a `Vec<Bytes>` or a `VecDeque<Bytes>`, this type is for you.

## Cursors

This crate also provides `Cursor`, which is a cursor type around a
`BufList`. Similar to similar to `std::io::Cursor`, a `Cursor` around
a `BufList` implements

* [`Seek`](std::io::Seek), [`Read`](std::io::Read), and [`BufRead`](std::io::BufRead)
* `bytes::Buf` as well (in other words, both `BufList`s and `Cursor`s over them
  can be passed into any APIs that accept `Buf`).

## Examples

Gather chunks into a `BufList`, then write them all out to standard error in one go:

```rust
use buf_list::BufList;
use tokio::io::AsyncWriteExt;

let mut buf_list = BufList::new();
buf_list.push_chunk(&b"hello "[..]);
buf_list.push_chunk(&b"world"[..]);
buf_list.push_chunk(&b"!"[..]);

let mut stderr = tokio::io::stderr();
stderr.write_all_buf(&mut buf_list).await?;
```

Collect a fallible stream of `Bytes` into a `BufList`:

```rust
use buf_list::BufList;
use bytes::Bytes;
use futures::TryStreamExt;

// A common example is a stream of bytes read over HTTP.
let stream = futures::stream::iter(
    vec![
        Ok(Bytes::from_static(&b"laputa, "[..])),
        Ok(Bytes::from_static(&b"castle "[..])),
        Ok(Bytes::from_static(&b"in the sky"[..]))
    ],
);

let buf_list = stream.try_collect::<BufList>().await?;
assert_eq!(buf_list.num_chunks(), 3);
```

### Converting to `Stream`s

A `BufList` can be converted into a `futures::Stream`, or a `TryStream`, of `Bytes` chunks. Use
this recipe to do so:

(This will be exposed as an API on `BufList` once `Stream` and/or `TryStream` become part of
stable Rust.)

```rust
use buf_list::BufList;
use bytes::Bytes;
use futures::{Stream, TryStream};

fn into_stream(buf_list: BufList) -> impl Stream<Item = Bytes> {
    futures::stream::iter(buf_list)
}

fn into_try_stream<E>(buf_list: BufList) -> impl TryStream<Ok = Bytes, Error = E> {
    futures::stream::iter(buf_list.into_iter().map(Ok))
}
```

## Optional features

* `tokio1`: With this feature enabled, `Cursor` implements the `tokio` crate's
  [`AsyncSeek`](tokio::io::AsyncSeek), [`AsyncRead`](tokio::io::AsyncRead) and
  [`AsyncBufRead`](tokio::io::AsyncBufRead).

* `futures03`: With this feature enabled, `Cursor` implements the `futures` crate's
  [`AsyncSeek`](futures_io_03::AsyncSeek), [`AsyncRead`](futures_io_03::AsyncRead) and
  [`AsyncBufRead`](futures_io_03::AsyncBufRead).

  Note that supporting `futures03` means exporting 0.x types as a public interface. **This
  violates the
  [C-STABLE](https://rust-lang.github.io/api-guidelines/necessities.html#public-dependencies-of-a-stable-crate-are-stable-c-stable)
  guideline.** However, the maintainer of `buf-list` considers that acceptable since `futures03`
  is an optional feature and not critical to `buf-list`. As newer versions of the `futures`
  crate are released, `buf-list` will support their versions of the async traits as well.

## Minimum supported Rust version

The minimum supported Rust version (MSRV) is **1.70**. Optional features may
cause a bump in the MSRV.

`buf-list` has a conservative MSRV policy. MSRV bumps will be sparing, and
if so, they will be accompanied by a minor version bump.

## Contributing

Pull requests are welcome! Please follow the
[code of conduct](https://github.com/sunshowers-code/.github/blob/main/CODE_OF_CONDUCT.md).

## License

buf-list is copyright 2022 The buf-list Contributors. All rights reserved.

Copied and adapted from linkerd2-proxy; [original
code](https://github.com/linkerd/linkerd2-proxy/blob/d36e3a75ef428453945eedaa230a32982c17d30d/linkerd/http-retry/src/replay.rs#L421-L492)
written by Eliza Weisman. linkerd2-proxy is copyright 2018 the linkerd2-proxy authors. All rights
reserved.

Licensed under the Apache License, Version 2.0 (the "License"); you may not use
these files except in compliance with the License. You may obtain a copy of the
License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied. See the License for the
specific language governing permissions and limitations under the License.
