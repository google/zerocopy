// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Zero-dependency one-time Wegman-Carter (`Poly1305`, RFC 8439) message
//! authentication and length-delimited authenticated framing.
//!
//! Each [`Poly1305Key`] is affine (non-`Clone`, non-`Copy`, scrubbed on drop
//! via volatile writes) and consumed by value when creating a [`Poly1305`]
//! instance or reading/writing an authenticated frame, statically preventing
//! catastrophic one-time pad / polynomial key reuse.

#![forbid(unsafe_code)]

use std::{
    fmt,
    io::{Read, Write},
};

use crate::{sys_util, toolchain::Failure};

/// Canonical 256-bit (32-byte) one-time `Poly1305` key length.
pub const POLY1305_KEY_LEN: usize = 32;

/// Canonical 128-bit (16-byte) `Poly1305` authentication tag length.
pub const POLY1305_TAG_LEN: usize = 16;

/// Frame magic header for authenticated pipe/stream records (`"AIM1"`).
pub const FRAME_MAGIC: [u8; 4] = *b"AIM1";

/// Maximum payload bytes accepted by default in [`read_authenticated_frame`]
/// (64 MiB).
pub const DEFAULT_MAX_FRAME_BYTES: usize = 64 * 1024 * 1024;

/// Upper bound on payload bytes accepted by [`seal_inline_pipe_frame`]
/// (32 KiB). The write end is additionally marked `O_NONBLOCK`, so frames
/// exceeding the actual kernel pipe capacity fail closed without blocking.
#[cfg(unix)]
pub const MAX_INLINE_PIPE_FRAME_BYTES: usize = 32 * 1024;

const M26_U64: u64 = (1 << 26) - 1;
const M26_U128: u128 = (1 << 26) - 1;

/// Affine one-time 32-byte key (`r || s`) for [`Poly1305`].
///
/// Reusing the same key bytes across two distinct messages breaks Wegman-Carter
/// security completely. Keys therefore do not implement `Clone` or `Copy`,
/// scrub their storage with volatile writes on [`Drop`], and redact their bytes
/// in `Debug` output.
pub struct Poly1305Key([u8; POLY1305_KEY_LEN]);

impl Poly1305Key {
    /// Wrap raw 32-byte one-time key material `(r || s)`.
    ///
    /// Callers must guarantee these 32 bytes are never reused for a second
    /// distinct message under the same `(r, s)` pair.
    pub const fn from_bytes(bytes: [u8; POLY1305_KEY_LEN]) -> Self {
        Self(bytes)
    }

    /// Generate a fresh 32-byte one-time key from the host OS CSPRNG
    /// (`getrandom(2)` on Linux, falling back to `/dev/urandom` on `ENOSYS` or
    /// other Unix platforms).
    pub fn generate() -> Result<Self, Failure> {
        let mut bytes = [0u8; POLY1305_KEY_LEN];
        sys_util::fill_os_random_32(&mut bytes)?;
        Ok(Self(bytes))
    }

    #[cfg(test)]
    pub(crate) fn copy_for_test(&self) -> Self {
        Self(self.0)
    }
}

impl fmt::Debug for Poly1305Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Poly1305Key([REDACTED])")
    }
}

impl Drop for Poly1305Key {
    fn drop(&mut self) {
        sys_util::volatile_zero(&mut self.0);
    }
}

/// 128-bit `Poly1305` authentication tag with constant-time equality checks.
#[derive(Clone, Copy, Debug, Eq)]
pub struct MacTag([u8; POLY1305_TAG_LEN]);

impl MacTag {
    /// Construct a tag from 16 raw bytes.
    pub const fn from_bytes(bytes: [u8; POLY1305_TAG_LEN]) -> Self {
        Self(bytes)
    }

    /// Borrow the 16-byte tag value.
    pub const fn as_bytes(&self) -> &[u8; POLY1305_TAG_LEN] {
        &self.0
    }

    /// Consume this tag and return the raw 16-byte array.
    pub const fn into_bytes(self) -> [u8; POLY1305_TAG_LEN] {
        self.0
    }

    /// Compare two tags in constant time.
    pub fn ct_eq(&self, other: &Self) -> bool {
        constant_time_eq(&self.0, &other.0)
    }
}

impl PartialEq for MacTag {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other)
    }
}

/// Compare two 16-byte authentication tags without secret-dependent branches.
pub fn constant_time_eq(lhs: &[u8; POLY1305_TAG_LEN], rhs: &[u8; POLY1305_TAG_LEN]) -> bool {
    let mut diff = 0u8;
    for (a, b) in lhs.iter().zip(rhs.iter()) {
        diff |= a ^ b;
    }
    std::hint::black_box(diff) == 0
}

/// Streaming RFC 8439 `Poly1305` one-time authenticator over `GF(2^130 - 5)`
/// using 5x26-bit limbs in pure safe Rust.
///
/// Internal key limbs, pad, accumulator, and partial-block buffers are
/// scrubbed via volatile writes on [`Drop`]; register and stack temporaries
/// produced during intermediate arithmetic remain best-effort.
pub struct Poly1305 {
    r: [u64; 5],
    s_mul: [u64; 4],
    h: [u64; 5],
    pad: [u8; 16],
    leftover: [u8; 16],
    leftover_len: usize,
}

impl Poly1305 {
    /// Initialize a streaming authenticator, consuming `key` by value so it
    /// cannot be reused across distinct messages.
    pub fn new(key: Poly1305Key) -> Self {
        let mut r_bytes = [0u8; 16];
        r_bytes.copy_from_slice(&key.0[..16]);
        // RFC 8439 Section 2.5 clamping.
        r_bytes[3] &= 15;
        r_bytes[7] &= 15;
        r_bytes[11] &= 15;
        r_bytes[15] &= 15;
        r_bytes[4] &= 252;
        r_bytes[8] &= 252;
        r_bytes[12] &= 252;

        let r_raw = u128::from_le_bytes(r_bytes);
        sys_util::volatile_zero(&mut r_bytes);
        let r0 = (r_raw & M26_U128) as u64;
        let r1 = ((r_raw >> 26) & M26_U128) as u64;
        let r2 = ((r_raw >> 52) & M26_U128) as u64;
        let r3 = ((r_raw >> 78) & M26_U128) as u64;
        let r4 = (r_raw >> 104) as u64;

        let mut pad = [0u8; 16];
        pad.copy_from_slice(&key.0[16..32]);
        drop(key);

        Self {
            r: [r0, r1, r2, r3, r4],
            s_mul: [r1 * 5, r2 * 5, r3 * 5, r4 * 5],
            h: [0; 5],
            pad,
            leftover: [0; 16],
            leftover_len: 0,
        }
    }

    /// Feed `data` into the authenticator.
    pub fn update(&mut self, mut data: &[u8]) {
        if data.is_empty() {
            return;
        }
        if self.leftover_len > 0 {
            let take = (16 - self.leftover_len).min(data.len());
            self.leftover[self.leftover_len..self.leftover_len + take]
                .copy_from_slice(&data[..take]);
            self.leftover_len += take;
            data = &data[take..];
            if self.leftover_len == 16 {
                let block = self.leftover;
                self.process_block(&block);
                sys_util::volatile_zero(&mut self.leftover);
                self.leftover_len = 0;
            }
        }
        let (chunks, rem) = data.as_chunks::<16>();
        for chunk in chunks {
            self.process_block(chunk);
        }
        if !rem.is_empty() {
            self.leftover[..rem.len()].copy_from_slice(rem);
            self.leftover_len = rem.len();
        }
    }

    /// Finalize the stream, scrub key/accumulator state, and return the 128-bit
    /// [`MacTag`].
    pub fn finalize(mut self) -> MacTag {
        if self.leftover_len > 0 {
            let len = self.leftover_len;
            let block = self.leftover;
            self.process_block(&block[..len]);
        }

        // Complete carry propagation across the 5x26-bit limbs so `h < 2^130`.
        let [mut h0, mut h1, mut h2, mut h3, mut h4] = self.h;
        h2 += h1 >> 26;
        h1 &= M26_U64;
        h3 += h2 >> 26;
        h2 &= M26_U64;
        h4 += h3 >> 26;
        h3 &= M26_U64;
        h0 += (h4 >> 26) * 5;
        h4 &= M26_U64;
        h1 += h0 >> 26;
        h0 &= M26_U64;

        // Constant-time conditional subtraction of `p = 2^130 - 5` by computing
        // `g = h + 5 - 2^130` and selecting `g` iff `h + 5 >= 2^130`.
        let mut g0 = h0.wrapping_add(5);
        let mut c = g0 >> 26;
        g0 &= M26_U64;
        let mut g1 = h1.wrapping_add(c);
        c = g1 >> 26;
        g1 &= M26_U64;
        let mut g2 = h2.wrapping_add(c);
        c = g2 >> 26;
        g2 &= M26_U64;
        let mut g3 = h3.wrapping_add(c);
        c = g3 >> 26;
        g3 &= M26_U64;
        let g4 = h4.wrapping_add(c).wrapping_sub(1 << 26);

        let mask = (g4 >> 63).wrapping_sub(1);
        let keep = !mask;
        h0 = (h0 & keep) | (g0 & mask);
        h1 = (h1 & keep) | (g1 & mask);
        h2 = (h2 & keep) | (g2 & mask);
        h3 = (h3 & keep) | (g3 & mask);
        h4 = (h4 & keep) | (g4 & mask);

        let f = (h0 as u128)
            | ((h1 as u128) << 26)
            | ((h2 as u128) << 52)
            | ((h3 as u128) << 78)
            | ((h4 as u128) << 104);
        let pad_val = u128::from_le_bytes(self.pad);
        let tag = f.wrapping_add(pad_val).to_le_bytes();
        drop(self);
        MacTag(tag)
    }

    /// Finalize the stream and verify against `expected` in constant time.
    pub fn verify(self, expected: &MacTag, context: &str) -> Result<(), Failure> {
        let actual = self.finalize();
        if actual.ct_eq(expected) {
            Ok(())
        } else {
            Err(Failure::operational(context, "Poly1305 authentication tag mismatch"))
        }
    }

    fn process_block(&mut self, block: &[u8]) {
        debug_assert!(!block.is_empty() && block.len() <= 16);
        let mut buf = [0u8; 16];
        buf[..block.len()].copy_from_slice(block);
        let hibit = if block.len() == 16 {
            1u64 << 24
        } else {
            buf[block.len()] = 1;
            0
        };
        let m = u128::from_le_bytes(buf);
        sys_util::volatile_zero(&mut buf);

        let h0 = self.h[0] + (m & M26_U128) as u64;
        let h1 = self.h[1] + ((m >> 26) & M26_U128) as u64;
        let h2 = self.h[2] + ((m >> 52) & M26_U128) as u64;
        let h3 = self.h[3] + ((m >> 78) & M26_U128) as u64;
        let h4 = self.h[4] + (m >> 104) as u64 + hibit;

        let [r0, r1, r2, r3, r4] = self.r;
        let [s1, s2, s3, s4] = self.s_mul;

        let d0 = h0 as u128 * r0 as u128
            + h1 as u128 * s4 as u128
            + h2 as u128 * s3 as u128
            + h3 as u128 * s2 as u128
            + h4 as u128 * s1 as u128;
        let d1 = h0 as u128 * r1 as u128
            + h1 as u128 * r0 as u128
            + h2 as u128 * s4 as u128
            + h3 as u128 * s3 as u128
            + h4 as u128 * s2 as u128;
        let d2 = h0 as u128 * r2 as u128
            + h1 as u128 * r1 as u128
            + h2 as u128 * r0 as u128
            + h3 as u128 * s4 as u128
            + h4 as u128 * s3 as u128;
        let d3 = h0 as u128 * r3 as u128
            + h1 as u128 * r2 as u128
            + h2 as u128 * r1 as u128
            + h3 as u128 * r0 as u128
            + h4 as u128 * s4 as u128;
        let d4 = h0 as u128 * r4 as u128
            + h1 as u128 * r3 as u128
            + h2 as u128 * r2 as u128
            + h3 as u128 * r1 as u128
            + h4 as u128 * r0 as u128;

        let mut c = d0 >> 26;
        let out0 = (d0 as u64) & M26_U64;
        let d1 = d1 + c;
        c = d1 >> 26;
        let out1 = (d1 as u64) & M26_U64;
        let d2 = d2 + c;
        c = d2 >> 26;
        let out2 = (d2 as u64) & M26_U64;
        let d3 = d3 + c;
        c = d3 >> 26;
        let out3 = (d3 as u64) & M26_U64;
        let d4 = d4 + c;
        c = d4 >> 26;
        let out4 = (d4 as u64) & M26_U64;

        let out0 = out0 + (c as u64) * 5;
        let c = out0 >> 26;
        self.h[0] = out0 & M26_U64;
        self.h[1] = out1 + c;
        self.h[2] = out2;
        self.h[3] = out3;
        self.h[4] = out4;
    }
}

impl Drop for Poly1305 {
    fn drop(&mut self) {
        sys_util::volatile_zero_u64(&mut self.r);
        sys_util::volatile_zero_u64(&mut self.s_mul);
        sys_util::volatile_zero_u64(&mut self.h);
        self.leftover_len = 0;
        sys_util::volatile_zero(&mut self.pad);
        sys_util::volatile_zero(&mut self.leftover);
    }
}

/// Compute a one-time `Poly1305` [`MacTag`] over `message`, consuming `key`.
pub fn authenticate(key: Poly1305Key, message: &[u8]) -> MacTag {
    let mut mac = Poly1305::new(key);
    mac.update(message);
    mac.finalize()
}

/// Verify a one-time `Poly1305` [`MacTag`] over `message` in constant time,
/// consuming `key`.
pub fn verify(
    key: Poly1305Key,
    message: &[u8],
    expected: &MacTag,
    context: &str,
) -> Result<(), Failure> {
    let mut mac = Poly1305::new(key);
    mac.update(message);
    mac.verify(expected, context)
}

fn update_domain_header(
    mac: &mut Poly1305,
    domain: &[u8],
    payload_len: u64,
) -> Result<(), Failure> {
    let domain_len: u32 = domain
        .len()
        .try_into()
        .map_err(|_| Failure::operational("it-mac", "domain tag exceeds 32-bit length bound"))?;
    mac.update(&domain_len.to_le_bytes());
    mac.update(domain);
    mac.update(&payload_len.to_le_bytes());
    Ok(())
}

/// Write a length-delimited frame `[AIM1][len_u64][payload][tag]`
/// authenticated under `(domain, len_u64, payload)` and consuming `key`.
pub fn write_authenticated_frame<W: Write>(
    writer: &mut W,
    key: Poly1305Key,
    domain: &[u8],
    payload: &[u8],
) -> Result<MacTag, Failure> {
    let payload_len: u64 = payload
        .len()
        .try_into()
        .map_err(|_| Failure::operational("it-mac", "frame payload length does not fit in u64"))?;
    let mut mac = Poly1305::new(key);
    update_domain_header(&mut mac, domain, payload_len)?;
    mac.update(payload);
    let tag = mac.finalize();

    writer
        .write_all(&FRAME_MAGIC)
        .map_err(|e| sys_util::failure_from_io("it-mac", "write authenticated frame header", &e))?;
    writer
        .write_all(&payload_len.to_le_bytes())
        .map_err(|e| sys_util::failure_from_io("it-mac", "write authenticated frame length", &e))?;
    writer.write_all(payload).map_err(|e| {
        sys_util::failure_from_io("it-mac", "write authenticated frame payload", &e)
    })?;
    writer
        .write_all(tag.as_bytes())
        .map_err(|e| sys_util::failure_from_io("it-mac", "write authenticated frame tag", &e))?;
    Ok(tag)
}

/// Read and verify a single authenticated frame from `reader` bounded by
/// `max_bytes`, consuming `key`. Rejects header/length mismatches, truncation,
/// tag forgery, or trailing unauthenticated bytes after the frame.
pub fn read_authenticated_frame<R: Read>(
    reader: &mut R,
    key: Poly1305Key,
    domain: &[u8],
    max_bytes: usize,
) -> Result<Vec<u8>, Failure> {
    let mut header = [0u8; 12];
    reader
        .read_exact(&mut header)
        .map_err(|e| sys_util::failure_from_io("it-mac", "read authenticated frame header", &e))?;
    if header[..4] != FRAME_MAGIC {
        return Err(Failure::operational("it-mac", "unexpected authenticated frame magic"));
    }
    let payload_len = u64::from_le_bytes(header[4..12].try_into().unwrap());
    let max_u64 = max_bytes as u64;
    if payload_len > max_u64 {
        return Err(Failure::operational(
            "it-mac",
            format!("authenticated frame payload {payload_len} bytes exceeds {max_bytes}-byte cap"),
        ));
    }
    let payload_usize = payload_len as usize;
    let mut payload = vec![0u8; payload_usize];
    if let Err(err) = reader.read_exact(&mut payload) {
        sys_util::volatile_zero(&mut payload);
        return Err(sys_util::failure_from_io("it-mac", "read authenticated frame payload", &err));
    }
    let mut tag_bytes = [0u8; POLY1305_TAG_LEN];
    if let Err(err) = reader.read_exact(&mut tag_bytes) {
        sys_util::volatile_zero(&mut payload);
        return Err(sys_util::failure_from_io("it-mac", "read authenticated frame tag", &err));
    }
    let mut trailing = [0u8; 1];
    loop {
        match reader.read(&mut trailing) {
            Ok(0) => break,
            Ok(_) => {
                sys_util::volatile_zero(&mut payload);
                return Err(Failure::operational(
                    "it-mac",
                    "unexpected trailing bytes after authenticated frame",
                ));
            }
            Err(err) if err.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(err) => {
                sys_util::volatile_zero(&mut payload);
                return Err(sys_util::failure_from_io("it-mac", "verify frame EOF", &err));
            }
        }
    }

    let mut mac = Poly1305::new(key);
    if let Err(err) = update_domain_header(&mut mac, domain, payload_len) {
        sys_util::volatile_zero(&mut payload);
        return Err(err);
    }
    mac.update(&payload);
    if let Err(err) = mac.verify(&MacTag(tag_bytes), "it-mac") {
        sys_util::volatile_zero(&mut payload);
        return Err(err);
    }
    Ok(payload)
}

/// Allocate an `O_CLOEXEC` authenticated pipe pair `(read_fd, write_fd)` and
/// generate its matching one-time [`Poly1305Key`].
#[cfg(unix)]
pub fn authenticated_pipe_pair()
-> Result<(std::os::unix::io::OwnedFd, std::os::unix::io::OwnedFd, Poly1305Key), Failure> {
    let key = Poly1305Key::generate()?;
    let (read_fd, write_fd) = sys_util::create_cloexec_pipe()?;
    Ok((read_fd, write_fd, key))
}

/// Write one bounded authenticated frame (`<= MAX_INLINE_PIPE_FRAME_BYTES`)
/// into a fresh `O_CLOEXEC` pipe using non-blocking writes on the write end,
/// close the write end, and return the read end alongside its fresh one-time
/// [`Poly1305Key`].
///
/// If the kernel pipe buffer cannot hold the framed payload without blocking
/// (for example under reduced per-user pipe limits), this fails closed with an
/// operational error rather than blocking indefinitely.
#[cfg(unix)]
pub fn seal_inline_pipe_frame(
    domain: &[u8],
    payload: &[u8],
) -> Result<(std::os::unix::io::OwnedFd, Poly1305Key), Failure> {
    use std::os::unix::io::AsFd as _;

    if payload.len() > MAX_INLINE_PIPE_FRAME_BYTES {
        return Err(Failure::operational(
            "it-mac",
            format!(
                "inline pipe payload {} bytes exceeds {MAX_INLINE_PIPE_FRAME_BYTES}-byte limit",
                payload.len()
            ),
        ));
    }
    let key_bytes = Poly1305Key::generate()?;
    let mut raw_copy = [0u8; POLY1305_KEY_LEN];
    raw_copy.copy_from_slice(&key_bytes.0);
    drop(key_bytes);

    let write_key = Poly1305Key::from_bytes(raw_copy);
    let read_key = Poly1305Key::from_bytes(raw_copy);
    sys_util::volatile_zero(&mut raw_copy);

    let (read_fd, write_fd) = sys_util::create_cloexec_pipe()?;
    sys_util::set_fd_nonblocking(write_fd.as_fd())?;
    let mut writer = std::fs::File::from(write_fd);
    let _tag = write_authenticated_frame(&mut writer, write_key, domain, payload)?;
    drop(writer);
    Ok((read_fd, read_key))
}

/// Read and authenticate an inline or streamed frame from `read_fd`, consuming
/// both the descriptor and its one-time [`Poly1305Key`].
#[cfg(unix)]
pub fn open_pipe_frame(
    read_fd: std::os::unix::io::OwnedFd,
    key: Poly1305Key,
    domain: &[u8],
    max_bytes: usize,
) -> Result<Vec<u8>, Failure> {
    let mut reader = std::fs::File::from(read_fd);
    read_authenticated_frame(&mut reader, key, domain, max_bytes)
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use super::*;

    fn hex_to_bytes(s: &str) -> Vec<u8> {
        assert_eq!(s.len() % 2, 0);
        (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
    }

    #[test]
    fn rfc8439_section_2_5_2_test_vector() {
        let key: [u8; 32] =
            hex_to_bytes("85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b")
                .try_into()
                .unwrap();
        let msg = b"Cryptographic Forum Research Group";
        let expected: [u8; 16] =
            hex_to_bytes("a8061dc1305136c6c22b8baf0c0127a9").try_into().unwrap();

        let tag = authenticate(Poly1305Key::from_bytes(key), msg);
        assert_eq!(tag.as_bytes(), &expected);
        assert!(verify(Poly1305Key::from_bytes(key), msg, &tag, "test").is_ok());

        // Unaligned chunk splits must yield the exact same tag as one-shot.
        for chunk_len in [1usize, 3, 7, 15, 16, 17, 34] {
            let mut mac = Poly1305::new(Poly1305Key::from_bytes(key));
            for chunk in msg.chunks(chunk_len) {
                mac.update(chunk);
            }
            assert_eq!(mac.finalize().as_bytes(), &expected, "chunk_len={chunk_len}");
        }
    }

    #[test]
    fn rfc8439_appendix_a3_vectors_empty_exact_and_mod_p_reduction() {
        // Test Vector #2 (all-zero key => zero tag for any message).
        let key_zero = [0u8; 32];
        assert_eq!(authenticate(Poly1305Key::from_bytes(key_zero), b"abc").as_bytes(), &[0u8; 16]);

        // Empty message yields the one-time pad `s` directly.
        let mut key_empty = [0u8; 32];
        for (idx, b) in key_empty[16..].iter_mut().enumerate() {
            *b = (idx as u8) + 1;
        }
        assert_eq!(
            authenticate(Poly1305Key::from_bytes(key_empty), b"").as_bytes(),
            &key_empty[16..]
        );

        // RFC 8439 Section A.3 Vector #4 (`r = 0`, verifying `tag == s` on
        // exact 375-byte message).
        let key4: [u8; 32] =
            hex_to_bytes("0000000000000000000000000000000036e5f6b5c5e06070f0efca96227a863e")
                .try_into()
                .unwrap();
        let msg_ietf = concat!(
            "Any submission to the IETF intended by the Contributor for ",
            "publication as all or part of an IETF Internet-Draft or RFC and ",
            "any statement made within the context of an IETF activity is ",
            "considered an \"IETF Contribution\". Such statements include ",
            "oral statements in IETF sessions, as well as written and ",
            "electronic communications made at any time or place, which are ",
            "addressed to"
        );
        assert_eq!(msg_ietf.len(), 375);
        assert_eq!(
            authenticate(Poly1305Key::from_bytes(key4), msg_ietf.as_bytes()).as_bytes(),
            &hex_to_bytes("36e5f6b5c5e06070f0efca96227a863e")[..]
        );

        // RFC 8439 Section A.3 Vector #5 (nonzero `r`, `s = 0`, 375-byte
        // multi-block message exercising carries and final reduction).
        let key5: [u8; 32] =
            hex_to_bytes("36e5f6b5c5e06070f0efca96227a863e00000000000000000000000000000000")
                .try_into()
                .unwrap();
        assert_eq!(
            authenticate(Poly1305Key::from_bytes(key5), msg_ietf.as_bytes()).as_bytes(),
            &hex_to_bytes("f3477e7cd95417af89a6b8794c310cf0")[..]
        );

        // 48-byte `0xff` test exercising mod `2^130 - 5` carry wrapping.
        let msg_ff = hex_to_bytes(&"ff".repeat(48));
        assert_eq!(
            authenticate(Poly1305Key::from_bytes(key5), &msg_ff).as_bytes(),
            &hex_to_bytes("b1e26d5d7ca1e69b21c6827a2696f1d1")[..]
        );

        // Exact `h = p` (`2^130 - 5`) and `h = p - 1` boundary reduction checks
        // with clamped `r = 1`, `s = 0`.
        let mut key_r1 = [0u8; 32];
        key_r1[0] = 1;
        let mut msg_p = [0xffu8; 32];
        msg_p[0] = 0xfe;
        msg_p[16] = 0xfd;
        assert_eq!(authenticate(Poly1305Key::from_bytes(key_r1), &msg_p).as_bytes(), &[0u8; 16]);

        let mut msg_pm1 = [0xffu8; 32];
        msg_pm1[0] = 0xfe;
        msg_pm1[16] = 0xfc;
        assert_eq!(
            authenticate(Poly1305Key::from_bytes(key_r1), &msg_pm1).as_bytes(),
            &hex_to_bytes("faffffffffffffffffffffffffffffff")[..]
        );
    }

    #[test]
    fn verify_and_framed_io_reject_tamper_forgery_domain_and_trailing_bytes() {
        let key = Poly1305Key::generate().unwrap();
        let payload = b"{\"status\":\"verified\",\"modules\":3}";
        let mut wire = Vec::new();
        let _tag =
            write_authenticated_frame(&mut wire, key.copy_for_test(), b"anneal-ipc-v1", payload)
                .unwrap();

        let opened = read_authenticated_frame(
            &mut Cursor::new(&wire),
            key.copy_for_test(),
            b"anneal-ipc-v1",
            DEFAULT_MAX_FRAME_BYTES,
        )
        .unwrap();
        assert_eq!(opened, payload);

        // Wrong domain fails closed.
        assert!(
            read_authenticated_frame(
                &mut Cursor::new(&wire),
                key.copy_for_test(),
                b"anneal-ipc-v2",
                DEFAULT_MAX_FRAME_BYTES,
            )
            .is_err()
        );

        // Payload bit flip fails closed.
        let mut flipped = wire.clone();
        flipped[15] ^= 0x01;
        assert!(
            read_authenticated_frame(
                &mut Cursor::new(&flipped),
                key.copy_for_test(),
                b"anneal-ipc-v1",
                DEFAULT_MAX_FRAME_BYTES,
            )
            .is_err()
        );

        // Tag bit flip fails closed.
        let mut forged_tag = wire.clone();
        let last = forged_tag.len() - 1;
        forged_tag[last] ^= 0x80;
        assert!(
            read_authenticated_frame(
                &mut Cursor::new(&forged_tag),
                key.copy_for_test(),
                b"anneal-ipc-v1",
                DEFAULT_MAX_FRAME_BYTES,
            )
            .is_err()
        );

        // Trailing bytes after valid tag fail closed.
        let mut with_tail = wire.clone();
        with_tail.push(0);
        assert!(
            read_authenticated_frame(
                &mut Cursor::new(&with_tail),
                key.copy_for_test(),
                b"anneal-ipc-v1",
                DEFAULT_MAX_FRAME_BYTES,
            )
            .is_err()
        );

        // Truncated frame and cap violation fail closed.
        let truncated = &wire[..wire.len() - 1];
        assert!(
            read_authenticated_frame(
                &mut Cursor::new(truncated),
                key.copy_for_test(),
                b"anneal-ipc-v1",
                DEFAULT_MAX_FRAME_BYTES,
            )
            .is_err()
        );
        assert!(
            read_authenticated_frame(&mut Cursor::new(&wire), key, b"anneal-ipc-v1", 8).is_err()
        );
    }

    #[test]
    fn key_generation_is_unique_and_debug_is_redacted() {
        let k1 = Poly1305Key::generate().unwrap();
        let k2 = Poly1305Key::generate().unwrap();
        assert_ne!(k1.0, [0u8; POLY1305_KEY_LEN]);
        assert_ne!(k1.0, k2.0);
        assert_eq!(format!("{k1:?}"), "Poly1305Key([REDACTED])");
    }

    #[cfg(unix)]
    #[test]
    fn authenticated_pipe_round_trip_and_tamper_detection() {
        let domain = b"anneal-execseal-pipe-v1";
        let payload = b"seal-payload-contents";
        let (read_fd, read_key) = seal_inline_pipe_frame(domain, payload).unwrap();
        let recovered =
            open_pipe_frame(read_fd, read_key, domain, DEFAULT_MAX_FRAME_BYTES).unwrap();
        assert_eq!(recovered, payload);

        // Tampering with a single byte on the pipe fails closed.
        let (r_fd, w_fd, key) = authenticated_pipe_pair().unwrap();
        let mut raw_wire = Vec::new();
        let _ =
            write_authenticated_frame(&mut raw_wire, key.copy_for_test(), domain, payload).unwrap();
        raw_wire[12] ^= 0x04;
        {
            let mut writer = std::fs::File::from(w_fd);
            writer.write_all(&raw_wire).unwrap();
        }
        assert!(open_pipe_frame(r_fd, key, domain, DEFAULT_MAX_FRAME_BYTES).is_err());

        let too_big = vec![0u8; MAX_INLINE_PIPE_FRAME_BYTES + 1];
        assert!(seal_inline_pipe_frame(domain, &too_big).is_err());

        // Non-blocking write end fails closed once the kernel pipe buffer fills
        // instead of hanging indefinitely with no reader.
        use std::os::unix::io::AsFd as _;
        let (_r_full, w_full, key_full) = authenticated_pipe_pair().unwrap();
        sys_util::set_fd_nonblocking(w_full.as_fd()).unwrap();
        let mut w_file = std::fs::File::from(w_full);
        let huge = vec![0x5Au8; 2 * 1024 * 1024];
        assert!(write_authenticated_frame(&mut w_file, key_full, domain, &huge).is_err());
    }
}
