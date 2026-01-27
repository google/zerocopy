// Copyright (c) The buf-list Contributors
// SPDX-License-Identifier: Apache-2.0

use buf_list::BufList;
use bytes::{Buf, Bytes};
use std::{io::IoSlice, ops::Deref};

#[test]
fn test_basic() {
    let mut buf_list = vec![&b"hello"[..], &b"world"[..]]
        .into_iter()
        .collect::<BufList>();
    println!("{:?}", buf_list);
    assert_eq!(buf_list.num_bytes(), 10);
    assert_eq!(buf_list.num_chunks(), 2);

    let chunk = buf_list.push_chunk(&b"foo"[..]);
    assert_eq!(buf_list.num_bytes(), 13);
    assert_eq!(buf_list.num_chunks(), 3);
    assert_eq!(chunk, &b"foo"[..]);

    // Try inserting a zero-length chunk. This should not count as a chunk.
    buf_list.push_chunk(&[] as &[u8]);
    assert_eq!(buf_list.num_bytes(), 13);
    assert_eq!(buf_list.num_chunks(), 3);

    {
        let mut buf_list = buf_list.clone();

        assert_eq!(buf_list.chunk(), &b"hello"[..]);

        // Advance by 2. This won't consume the first chunk.
        buf_list.advance(2);
        assert_eq!(buf_list.num_bytes(), 11);
        assert_eq!(buf_list.num_chunks(), 3);
        assert_eq!(buf_list.chunk(), &b"llo"[..]);

        // Advance by 3. This will consume the "hello" chunk exactly.
        buf_list.advance(3);
        assert_eq!(buf_list.num_bytes(), 8);
        assert_eq!(buf_list.num_chunks(), 2);
        assert_eq!(buf_list.chunk(), &b"world"[..]);

        // Advance by 6. This will consume the "world" chunk + the first byte of "foo".
        buf_list.advance(6);
        assert_eq!(buf_list.num_bytes(), 2);
        assert_eq!(buf_list.num_chunks(), 1);
        assert_eq!(buf_list.chunk(), &b"oo"[..]);

        // Advance by 2. This will consume the "foo" chunk exactly.
        buf_list.advance(2);
        assert_eq!(buf_list.num_bytes(), 0);
        assert_eq!(buf_list.num_chunks(), 0);
        assert_eq!(buf_list.chunk(), &[] as &[u8]);
    }

    {
        // Test chunks_vectored.
        let mut chunks_vectored = vec![IoSlice::new(&[]); 5];
        let ret = buf_list.chunks_vectored(&mut chunks_vectored);
        assert_eq!(ret, 3);
        assert_eq!(chunks_vectored[0].deref(), &b"hello"[..]);
        assert_eq!(chunks_vectored[1].deref(), &b"world"[..]);
        assert_eq!(chunks_vectored[2].deref(), &b"foo"[..]);
        assert_eq!(chunks_vectored[3].deref(), &[] as &[u8]);

        // Test chunks_vectored with a smaller buffer.
        let mut chunks_vectored = vec![IoSlice::new(&[]); 2];
        let ret = buf_list.chunks_vectored(&mut chunks_vectored);
        assert_eq!(ret, 2);
        assert_eq!(chunks_vectored[0].deref(), &b"hello"[..]);
        assert_eq!(chunks_vectored[1].deref(), &b"world"[..]);

        // Test with an empty buffer.
        let mut chunks_vectored = vec![];
        let ret = buf_list.chunks_vectored(&mut chunks_vectored);
        assert_eq!(ret, 0);
    }

    {
        // Test copy_to_bytes.
        let mut buf_list = buf_list.clone();

        // Copy the first two bytes -- this should just be a refcount.
        let bytes = buf_list.copy_to_bytes(2);
        assert_eq!(bytes, &b"he"[..]);
        assert_eq!(buf_list.num_bytes(), 11);
        assert_eq!(buf_list.num_chunks(), 3);

        // Copy the next 3 bytes. This should consume the buffer.
        let bytes = buf_list.copy_to_bytes(3);
        assert_eq!(bytes, &b"llo"[..]);
        assert_eq!(buf_list.num_bytes(), 8);
        assert_eq!(buf_list.num_chunks(), 2);

        // Copy 6 bytes. This should consume the next buffer.
        let bytes = buf_list.copy_to_bytes(6);
        assert_eq!(bytes, &b"worldf"[..]);
        assert_eq!(buf_list.num_bytes(), 2);
        assert_eq!(buf_list.num_chunks(), 1);

        // Copy the last 2 bytes + this next buffer -- ensure that all buffers are consumed.
        buf_list.push_chunk(&b"bar"[..]);
        let bytes = buf_list.copy_to_bytes(5);
        assert_eq!(bytes, &b"oobar"[..]);
        assert_eq!(buf_list.num_bytes(), 0);
        assert_eq!(buf_list.num_chunks(), 0);
    }
}

#[test]
fn test_iter() {
    let buf_list = vec![&b"hello"[..], &b"world"[..], &b"foo"[..], &b"bar"[..]]
        .into_iter()
        .collect::<BufList>();

    // Test iteration over the buf_list.
    let mut iter = (&buf_list).into_iter();
    println!("{:?}", iter);
    assert_eq!(iter.next(), Some(&Bytes::from_static(&b"hello"[..])));
    assert_eq!(iter.size_hint(), (3, Some(3)));
    assert_eq!(iter.len(), 3);

    {
        let mut iter = iter.clone();
        #[allow(clippy::iter_nth_zero)]
        {
            assert_eq!(iter.nth(0), Some(&Bytes::from_static(&b"world"[..])));
        }
        assert_eq!(iter.last(), Some(&Bytes::from_static(&b"bar"[..])));
    }

    {
        let iter = iter.clone();
        let v = iter.fold(vec![], |mut v, item| {
            v.push(item);
            v
        });
        assert_eq!(
            v,
            vec![
                &Bytes::from_static(&b"world"[..]),
                &Bytes::from_static(&b"foo"[..]),
                &Bytes::from_static(&b"bar"[..]),
            ]
        );
    }

    {
        let mut iter = iter.clone();
        assert_eq!(iter.next_back(), Some(&Bytes::from_static(&b"bar"[..])));
        assert_eq!(
            iter.rfold(vec![], |mut v, item| {
                v.push(item);
                v
            }),
            vec![
                &Bytes::from_static(&b"foo"[..]),
                &Bytes::from_static(&b"world"[..]),
            ]
        );
    }
}

#[test]
fn test_into_iter() {
    let buf_list = vec![&b"hello"[..], &b"world"[..], &b"foo"[..], &b"bar"[..]]
        .into_iter()
        .collect::<BufList>();

    let into_iter = buf_list.into_iter();
    println!("{:?}", into_iter);
    #[allow(clippy::redundant_clone)]
    let mut into_iter = into_iter.clone();
    assert_eq!(into_iter.next(), Some(Bytes::from_static(&b"hello"[..])));
    assert_eq!(into_iter.size_hint(), (3, Some(3)));
    assert_eq!(into_iter.len(), 3);
    assert_eq!(into_iter.next_back(), Some(Bytes::from_static(&b"bar"[..])));
}

#[test]
#[should_panic = "`len` (12) greater than remaining (10)"]
fn test_copy_to_bytes_panic() {
    let mut buf_list = vec![&b"hello"[..], &b"world"[..]]
        .into_iter()
        .collect::<BufList>();
    buf_list.copy_to_bytes(12);
}
