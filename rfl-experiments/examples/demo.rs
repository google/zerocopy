// Copyright 2026 The Fuchsia Authors
// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT

use std::{cell::Cell, rc::Rc};

use rfl_zerocopy_experiments::{
    address_projection::AddressProject,
    binder::Packet,
    conversions::{LegacyAsBytes, LegacyFromBytes},
    device_ids::{Context, DeviceId, IdTable},
    field_descriptor,
    firmware::Header,
    typed_init::{initialize, Failure},
};

#[repr(C)]
struct Registers {
    control: u32,
    status: u32,
}
field_descriptor!(Status, Registers, status, u32);

static CONTEXT: Context = Context { name: "GPU demo" };
const IDS: IdTable<1> = IdTable::new([(DeviceId::new(0x1234, 42), &CONTEXT)]);

fn main() {
    let mmio = core::ptr::without_provenance_mut::<Registers>(0x1000);
    assert_eq!(Status::project(mmio).addr(), 0x1004);
    println!("1. Raw projection: MMIO 0x1000 -> status 0x1004, without memory access");

    let mut bytes = [0xa5; 24];
    bytes[..4].copy_from_slice(&0x73682a85_u32.to_ne_bytes());
    let (mut packet, _) = Packet::parse_prefix(&bytes).unwrap();
    packet.set_handle(42).unwrap();
    assert_eq!(packet.handle(), Ok(42));
    assert_eq!(&packet.bytes()[12..], &bytes[12..]);
    println!("2. Binder: rewrote handle to 42; unused union bytes and cookie preserved");

    let value = 0x12345678_u32;
    let copy = <u32 as LegacyFromBytes>::from_bytes_copy(LegacyAsBytes::as_bytes(&value)).unwrap();
    assert_eq!(copy, value);
    println!("3. Conversion facade: byte round trip uses zerocopy, no legacy unsafe impl");

    let resource = Rc::new(Cell::new(0));
    let address = Rc::new(Cell::new(0));
    assert!(initialize(Failure::Error, resource.clone(), address.clone()).is_err());
    assert_eq!((resource.get(), address.get()), (1, 0));
    let record = initialize(Failure::None, resource.clone(), address.clone()).unwrap();
    assert!(record.as_ref().address_is_stable());
    drop(record);
    assert_eq!((resource.get(), address.get()), (2, 1));
    println!("4. Pin-init: rollback drops completed field; success preserves self-address");

    let table = IDS;
    assert!(core::ptr::eq(table.context(0).unwrap(), &CONTEXT));
    assert!(table.sentinel_is_zero());
    println!(
        "5. Const device IDs: recovered '{}' with original reference provenance",
        table.context(0).unwrap().name
    );

    let mut image = [0; 24];
    image[..4].copy_from_slice(&0xc3f13a6e_u32.to_le_bytes());
    image[4] = 7;
    image[16..20].copy_from_slice(&24_u32.to_le_bytes());
    let (header, remainder) = Header::parse(&image).unwrap();
    assert_eq!(header.version(), (0, 7));
    assert_eq!(remainder.len(), 4);
    println!("6. Firmware: borrowed little-endian header v0.7, with four bytes remaining");
}
