// Copyright 2026 The Fuchsia Authors
// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT

//! Binder's 64-bit wire ABI accessed through initialized-byte projections.
//! This models BINDER_IPC_32BIT disabled, independently of host pointer width.

use zerocopy::{
    invariant::{Aligned, Initialized, Shared},
    FromBytes, Immutable, IntoBytes, KnownLayout, Project, Ptr, ReadOnly,
};

const HANDLE: u32 = 0x73682a85;
const BUFFER: u32 = 0x70742a85;

#[derive(Clone, Copy, Project, KnownLayout, Immutable)]
#[repr(C)]
struct ObjectHeader {
    type_: u32,
}

#[derive(Clone, Copy, Project, KnownLayout, Immutable)]
#[repr(C)]
union Payload {
    binder: u64,
    handle: u32,
}

#[derive(Clone, Copy, Project, KnownLayout, Immutable)]
#[repr(C)]
struct FlatObject {
    hdr: ObjectHeader,
    flags: u32,
    payload: Payload,
    cookie: u64,
}

#[derive(Clone, Copy, Project, KnownLayout, Immutable)]
#[repr(C)]
struct BufferObject {
    hdr: ObjectHeader,
    flags: u32,
    buffer: u64,
    length: u64,
    parent: u64,
    parent_offset: u64,
}

#[derive(Clone, Copy, Project, KnownLayout, Immutable)]
#[repr(C)]
union RawObject {
    hdr: ObjectHeader,
    flat: FlatObject,
    buffer: BufferObject,
}

const STORAGE_BYTES: usize = core::mem::size_of::<RawObject>();

#[derive(FromBytes, IntoBytes, KnownLayout, Immutable)]
#[repr(C, align(8))]
struct Storage([u8; STORAGE_BYTES]);

macro_rules! project {
    ($ptr:expr, struct, $field:ident) => {
        $ptr.project::<zerocopy::project_clients::ProjectDerive, _, { zerocopy::STRUCT_VARIANT_ID }, { zerocopy::ident_id!($field) }>().unwrap()
    };
    ($ptr:expr, union, $field:ident) => {
        $ptr.project::<zerocopy::project_clients::ProjectDerive, _, { zerocopy::REPR_C_UNION_VARIANT_ID }, { zerocopy::ident_id!($field) }>().unwrap()
    };
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    Alignment,
    Type,
    WrongVariant,
}

/// Owns a snapshot. All bytes remain initialized, including unused union bytes.
/// Private storage and scalar-only writers prevent padded aggregate assignment.
pub struct Packet {
    storage: Storage,
    len: usize,
}

impl Packet {
    pub fn parse_prefix(bytes: &[u8]) -> Result<(Self, &[u8]), Error> {
        let tag = u32::read_from_prefix(bytes).map_err(|_| Error::Truncated)?.0;
        let len = match tag {
            HANDLE => core::mem::size_of::<FlatObject>(),
            BUFFER => core::mem::size_of::<BufferObject>(),
            _ => return Err(Error::Type),
        };
        let (object, rest) = bytes.split_at_checked(len).ok_or(Error::Truncated)?;
        let mut storage = Storage([0; STORAGE_BYTES]);
        storage.0[..len].copy_from_slice(object);
        Ok((Self { storage, len }, rest))
    }

    fn view(&self) -> Ptr<'_, ReadOnly<RawObject>, (Shared, Aligned, Initialized)> {
        Ptr::from_ref(&self.storage.0[..])
            .try_cast_into_no_leftover::<ReadOnly<RawObject>, zerocopy::BecauseImmutable>(None)
            .unwrap()
    }

    pub fn bytes(&self) -> &[u8] {
        &self.storage.0[..self.len]
    }

    pub fn tag(&self) -> u32 {
        let header = project!(self.view(), union, hdr);
        ReadOnly::into_inner(
            project!(header, struct, type_)
                .recall_validity::<zerocopy::invariant::Safe, zerocopy::BecauseImmutable>()
                .read::<zerocopy::BecauseImmutable>(),
        )
    }

    pub fn handle(&self) -> Result<u32, Error> {
        if self.tag() != HANDLE {
            return Err(Error::WrongVariant);
        }
        let flat = project!(self.view(), union, flat);
        let payload = project!(flat, struct, payload);
        Ok(ReadOnly::into_inner(
            project!(payload, union, handle)
                .recall_validity::<zerocopy::invariant::Safe, zerocopy::BecauseImmutable>()
                .read::<zerocopy::BecauseImmutable>(),
        ))
    }

    pub fn set_handle(&mut self, value: u32) -> Result<(), Error> {
        if self.tag() != HANDLE {
            return Err(Error::WrongVariant);
        }
        let object = Ptr::from_mut(&mut self.storage.0[..])
            .try_cast_into_no_leftover::<RawObject, zerocopy::pointer::BecauseExclusive>(None)
            .unwrap();
        let flat = project!(object, union, flat);
        let payload = project!(flat, struct, payload);
        let field = project!(payload, union, handle)
            .recall_validity::<zerocopy::invariant::Safe, (_, (_, zerocopy::pointer::BecauseExclusive))>();
        *field.as_mut() = value;
        Ok(())
    }

    pub fn buffer_address(&self) -> Result<u64, Error> {
        if self.tag() != BUFFER {
            return Err(Error::WrongVariant);
        }
        let buffer = project!(self.view(), union, buffer);
        Ok(ReadOnly::into_inner(
            project!(buffer, struct, buffer)
                .recall_validity::<zerocopy::invariant::Safe, zerocopy::BecauseImmutable>()
                .read::<zerocopy::BecauseImmutable>(),
        ))
    }
}

// binder_pri_ptr_cookie has implicit padding between priority and ptr in the
// 64-bit ABI. We never instantiate or mutably reference this aggregate.
#[derive(Clone, Copy, Project, KnownLayout, Immutable)]
#[repr(C)]
struct PriPtrCookie {
    priority: i32,
    ptr: u64,
    cookie: u64,
}

/// Scalar writes preserve the aggregate's padding bytes. In contrast, a
/// mutable typed reference to a padded aggregate is rejected:
///
/// ```compile_fail
/// use zerocopy::{FromBytes, Immutable, KnownLayout};
/// #[derive(FromBytes, Immutable, KnownLayout)]
/// #[repr(C)]
/// struct Padded { byte: u8, word: u32 }
/// fn aggregate(bytes: &mut [u8]) -> &mut Padded {
///     Padded::mut_from_bytes(bytes).unwrap()
/// }
/// ```
pub fn rewrite_priority(bytes: &mut [u8], priority: i32) -> Result<(), Error> {
    let ptr = Ptr::from_mut(bytes)
        .try_cast_into_no_leftover::<PriPtrCookie, zerocopy::pointer::BecauseExclusive>(None)
        .map_err(|error| match error {
            zerocopy::CastError::Alignment(_) => Error::Alignment,
            _ => Error::Truncated,
        })?;
    *project!(ptr, struct, priority)
        .recall_validity::<zerocopy::invariant::Safe, (_, (_, zerocopy::pointer::BecauseExclusive))>()
        .as_mut() = priority;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn handle_update_preserves_unused_union_bytes_and_cookie() {
        let mut bytes = [0xa5; 28];
        bytes[..4].copy_from_slice(&HANDLE.to_ne_bytes());
        let (mut packet, rest) = Packet::parse_prefix(&bytes).unwrap();
        assert_eq!(rest, &bytes[24..]);
        packet.set_handle(42).unwrap();
        assert_eq!(packet.handle(), Ok(42));
        let mut expected = bytes[..24].to_vec();
        expected[8..12].copy_from_slice(&42_u32.to_ne_bytes());
        assert_eq!(packet.bytes(), expected);
        assert_eq!(packet.buffer_address(), Err(Error::WrongVariant));
    }

    #[test]
    fn rejects_invalid_tag_and_short_variant() {
        assert!(matches!(Packet::parse_prefix(&[0; 48]), Err(Error::Type)));
        for (tag, len) in [(HANDLE, 24), (BUFFER, 40)] {
            let mut bytes = [0; 48];
            bytes[..4].copy_from_slice(&tag.to_ne_bytes());
            for end in 0..len {
                assert!(matches!(Packet::parse_prefix(&bytes[..end]), Err(Error::Truncated)));
            }
        }
        let mut bytes = [0; 48];
        bytes[..4].copy_from_slice(&BUFFER.to_ne_bytes());
        bytes[8..16].copy_from_slice(&0x123456789_u64.to_ne_bytes());
        let (mut packet, _) = Packet::parse_prefix(&bytes).unwrap();
        assert_eq!(packet.buffer_address(), Ok(0x123456789));
        assert_eq!(packet.set_handle(1), Err(Error::WrongVariant));
    }

    #[test]
    fn scalar_projection_preserves_implicit_padding() {
        let mut storage = Storage([0x5a; STORAGE_BYTES]);
        rewrite_priority(&mut storage.0[..24], -7).unwrap();
        assert_eq!(&storage.0[..4], &(-7_i32).to_ne_bytes());
        assert!(storage.0[4..24].iter().all(|byte| *byte == 0x5a));
        assert_eq!(core::mem::offset_of!(PriPtrCookie, ptr), 8);
    }
}
